/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.WeakDeriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Removable point singularities of weak derivatives

A function that is classically differentiable on `Ω ∖ {a}` need not have that derivative as its
weak derivative on all of `Ω`: the Heaviside function on `ℝ` has classical derivative `0` away
from the origin, but its weak derivative is a Dirac mass. What rules such a jump out is a
quantitative smallness of the function near the singular point, and the sharp condition is that

`∫_{B(a,δ)} ‖f‖ = o(δ)   as δ → 0`.

`hasWeakFDerivOn_of_hasFDerivAt_compl_singleton` is the statement: under that condition, the
classical derivative on `Ω ∖ {a}` is the weak derivative on `Ω`, the singular point included.

The proof integrates by parts against a test function multiplied by a cutoff `1 - punctureBump a δ`
that vanishes on `B(a, δ)`, where the classical derivative is available, and lets `δ → 0`. The
error term produced by differentiating the cutoff carries the factor `δ⁻¹`, because the cutoff
climbs from `0` to `1` across an annulus of width `δ`, and it is exactly the displayed condition
that makes it vanish in the limit. No mollification and no convolution theory is involved.

## Main definitions

* `punctureBump a δ`, a smooth bump equal to `1` on the closed ball `B̄(a, δ)`, supported in
  `B(a, 2δ)`, with values in `[0, 1]` and with derivative of size `O(1/δ)`.

## Main statements

* `hasWeakFDerivOn_of_hasFDerivAt_compl_singleton`: the removable-singularity lemma above.
* `hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton`: the same conclusion read along a
  single direction, which is the form in which a Sobolev space indexed by multi-indices asks for a
  first-order derivative.
* `hasWeakFDerivOn_of_hasFDerivAt` and `hasWeakIteratedLineDerivOn_of_hasFDerivAt`: the degenerate
  case with no singular point at all, that is, the first-order form of "a classical derivative is
  a weak derivative" stated with the derivative named rather than written `fderiv`.
* `tendsto_inv_mul_setIntegral_norm_ball_zero`: a sufficient condition for the displayed
  smallness, namely `‖f x‖ ≤ C ‖x‖ ^ s` near the origin for some `s > 1 - d` with `d` the
  dimension. This covers every radial singularity milder than `‖x‖^{1-d}`, in particular every
  logarithmic one. Its ingredients `setIntegral_norm_rpow_ball_zero` and
  `integrableOn_norm_rpow_ball_zero` are the scaling law and the integrability of a power on a
  ball, and are useful on their own.

## Implementation notes

The exceptional set is a single point. A closed set of vanishing `(d-1)`-dimensional capacity
would do as well, but the cutoff would then have to be built by a smooth Urysohn lemma and the
bound `‖∇χ‖ = O(1/δ)` would have to be assumed rather than computed, so nothing is gained for
the applications, which are radial functions on a ball singular at the centre.

The smallness condition is imposed on `f` alone. The corresponding error term for the derivative
is handled instead by the hypothesis that the derivative is locally integrable on all of `Ω`,
origin included — which is also part of the conclusion, since a weak derivative is by definition
locally integrable there.

Nothing is asked about the continuity of the derivative: the integration by parts used is
`integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`, which needs only pointwise
differentiability on the support of the test function, so `HasFDerivAt` off the singular point is
the whole hypothesis.
-/

open Filter MeasureTheory Metric Set TopologicalSpace

open scoped ContDiff Distributions ENNReal NNReal Topology

/-! ### A smooth bump concentrated near a point -/

section Bump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

variable (E) in
/-- The bump function of `E` that is `1` on the closed unit ball and vanishes outside the ball of
radius `2`. Rescaling it is how `punctureBump` is built. -/
noncomputable def unitPunctureBump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `punctureBump a δ` is a smooth function of `E` that equals `1` on the closed ball `B̄(a, δ)`,
vanishes outside the ball `B(a, 2δ)`, takes values in `[0, 1]` and has derivative of size
`O(1/δ)`. Multiplying a test function by `1 - punctureBump a δ` produces a test function that
vanishes near `a`, which is how one integrates by parts away from a point singularity. -/
noncomputable def punctureBump (a : E) (δ : ℝ) : E → ℝ :=
  fun x ↦ unitPunctureBump E (δ⁻¹ • (x - a))

variable {a x : E} {δ : ℝ}

omit [HasContDiffBump E] in
/-- The rescaling map `x ↦ δ⁻¹ • (x - a)` used to build `punctureBump`. -/
private theorem hasFDerivAt_punctureBump_arg (a : E) (δ : ℝ) (x : E) :
    HasFDerivAt (fun y ↦ δ⁻¹ • (y - a)) (δ⁻¹ • (ContinuousLinearMap.id ℝ E)) x :=
  ((hasFDerivAt_id x).sub_const a).const_smul δ⁻¹

/-- `punctureBump` is smooth. -/
theorem contDiff_punctureBump (a : E) (δ : ℝ) : ContDiff ℝ ∞ (punctureBump a δ) :=
  (unitPunctureBump E).contDiff.comp
    ((contDiff_id.sub contDiff_const).const_smul δ⁻¹)

/-- `punctureBump` is nonnegative. -/
theorem punctureBump_nonneg : 0 ≤ punctureBump a δ x := ContDiffBump.nonneg _

/-- `punctureBump` is at most `1`. -/
theorem punctureBump_le_one : punctureBump a δ x ≤ 1 := ContDiffBump.le_one _

/-- `punctureBump a δ` is `1` on the closed ball of radius `δ` about `a`. -/
theorem punctureBump_eq_one (hδ : 0 < δ) (hx : dist x a ≤ δ) : punctureBump a δ x = 1 := by
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  simp only [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hδ, unitPunctureBump]
  rw [inv_mul_le_iff₀ hδ, mul_one, ← dist_eq_norm]
  exact hx

/-- `punctureBump a δ` vanishes outside the ball of radius `2δ` about `a`. -/
theorem punctureBump_eq_zero (hδ : 0 < δ) (hx : 2 * δ ≤ dist x a) : punctureBump a δ x = 0 := by
  refine ContDiffBump.zero_of_le_dist _ ?_
  simp only [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ,
    unitPunctureBump]
  rw [le_inv_mul_iff₀ hδ, ← dist_eq_norm]
  linarith

/-- The support of `punctureBump a δ` is contained in the ball of radius `2δ` about `a`. -/
theorem support_punctureBump_subset (hδ : 0 < δ) :
    Function.support (punctureBump a δ) ⊆ ball a (2 * δ) := fun x hx ↦ by
  by_contra hmem
  rw [mem_ball, not_lt] at hmem
  exact hx (punctureBump_eq_zero hδ hmem)

/-- The derivative of `punctureBump a δ` vanishes outside the ball of radius `2δ` about `a`: there
the bump is at a global minimum. -/
theorem fderiv_punctureBump_eq_zero (hδ : 0 < δ) (hx : 2 * δ ≤ dist x a) :
    fderiv ℝ (punctureBump a δ) x = 0 := by
  refine IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ ?_)
  rw [punctureBump_eq_zero hδ hx]
  exact punctureBump_nonneg

/-- The derivative of `punctureBump a δ` is `O(1/δ)`, with a constant depending only on `E`: the
bump climbs from `0` to `1` across an annulus of width `δ`. -/
theorem exists_norm_fderiv_punctureBump_le [FiniteDimensional ℝ E] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : E) (δ : ℝ), 0 < δ → ∀ x, ‖fderiv ℝ (punctureBump a δ) x‖ ≤ K / δ := by
  have hb : ContDiff ℝ ∞ (unitPunctureBump E : E → ℝ) := ContDiffBump.contDiff _
  obtain ⟨K, hK⟩ := ((unitPunctureBump E).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv (by simp))
  refine ⟨K, le_trans (norm_nonneg _) (hK 0), fun a δ hδ x ↦ ?_⟩
  have hcomp : HasFDerivAt (punctureBump a δ)
      ((fderiv ℝ (unitPunctureBump E) (δ⁻¹ • (x - a))).comp (δ⁻¹ • ContinuousLinearMap.id ℝ E)) x :=
    (hb.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
      x (hasFDerivAt_punctureBump_arg a δ x)
  rw [hcomp.fderiv]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h2 : ‖(δ⁻¹ • ContinuousLinearMap.id ℝ E : E →L[ℝ] E)‖ ≤ δ⁻¹ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
  rw [div_eq_mul_inv]
  exact mul_le_mul (hK _) h2 (norm_nonneg _) (le_trans (norm_nonneg _) (hK 0))

end Bump

/-! ### Integration by parts against a test function -/

section IntegrationByParts

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {w : E → E →L[ℝ] F}

/-- **Integration by parts against a test function whose support avoids the singularities.** If
`f` is locally integrable on `Ω`, if `w` is locally integrable on `Ω`, and if `w x` is the
classical derivative of `f` at every point of the support of the test function `ψ`, then the
integration by parts formula holds for `ψ`. Nothing is asked of `f` off that support, which is
what makes this usable with a cutoff. -/
theorem integral_fderiv_smul_eq_neg_integral_smul_apply
    (hf : LocallyIntegrableOn f Ω μ) (hw : LocallyIntegrableOn w Ω μ) (ψ : 𝓓(Ω, ℝ))
    (hfd : ∀ x ∈ tsupport (ψ : E → ℝ), HasFDerivAt f (w x) x) (v : E) :
    ∫ x, fderiv ℝ (ψ : E → ℝ) x v • f x ∂μ = -∫ x, (ψ : E → ℝ) x • w x v ∂μ := by
  have hψf : Integrable (fun x ↦ (ψ : E → ℝ) x • f x) μ :=
    hf.integrable_smul_left_of_tsupport_subset ψ.contDiff.continuous ψ.hasCompactSupport
      ψ.tsupport_subset
  have hψ'f : Integrable (fun x ↦ fderiv ℝ (ψ : E → ℝ) x v • f x) μ :=
    hf.integrable_smul_left_of_tsupport_subset (ψ.fderivApply v).contDiff.continuous
      (ψ.fderivApply v).hasCompactSupport (ψ.fderivApply v).tsupport_subset
  have hψw : Integrable (fun x ↦ (ψ : E → ℝ) x • w x v) μ := by
    have h := (hw.integrable_smul_left_of_tsupport_subset ψ.contDiff.continuous
      ψ.hasCompactSupport ψ.tsupport_subset).apply_continuousLinearMap v
    simpa using h
  have heq : ∀ x, (ψ : E → ℝ) x • fderiv ℝ f x v = (ψ : E → ℝ) x • w x v := fun x ↦ by
    by_cases hx : x ∈ tsupport (ψ : E → ℝ)
    · rw [(hfd x hx).fderiv]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, zero_smul]
  have hψf' : Integrable (fun x ↦ (ψ : E → ℝ) x • fderiv ℝ f x v) μ :=
    hψw.congr (Eventually.of_forall fun x ↦ (heq x).symm)
  have key := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ)
    (f := (ψ : E → ℝ)) (g := f) (v := v) hψ'f hψf' hψf
    (fun x _ ↦ ψ.contDiff.differentiable (by simp) x) (fun x hx ↦ (hfd x hx).differentiableAt)
  rw [← integral_congr_ae (Eventually.of_forall heq), key, neg_neg]

end IntegrationByParts

/-! ### Removable point singularities -/

section RemovableSingularity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {w : E → E →L[ℝ] F} {a : E}

/-- **A classical derivative is a weak derivative**, first-order form with the derivative named
rather than written `fderiv`: if `f` is differentiable at every point of the open set `Ω` with
derivative `w`, and both are locally integrable there, then `w` is the weak derivative of `f`
on `Ω`. -/
theorem hasWeakFDerivOn_of_hasFDerivAt (hf : LocallyIntegrableOn f Ω μ)
    (hw : LocallyIntegrableOn w Ω μ) (hfd : ∀ x ∈ (Ω : Set E), HasFDerivAt f (w x) x) :
    HasWeakFDerivOn f w Ω μ := by
  refine hasWeakFDerivOn_iff.2 ⟨hf, hw, fun φ v ↦ ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show fderiv ℝ (φ : E → ℝ) x v = 0 from (φ.fderivApply v).eq_zero_of_notMem hx,
          zero_smul],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]]
  exact integral_fderiv_smul_eq_neg_integral_smul_apply hf hw φ
    (fun x hx ↦ hfd x (φ.tsupport_subset hx)) v

/-- **A classical derivative is a weak derivative**, read along a single direction: the form in
which a Sobolev space indexed by multi-indices asks for a first-order derivative, the tuple having
length one and single entry the direction `u`. -/
theorem hasWeakIteratedLineDerivOn_of_hasFDerivAt {n : ℕ} {y : Fin n → E} {u : E} (hn : n = 1)
    (hy : ∀ i, y i = u) (hf : LocallyIntegrableOn f Ω μ) (hw : LocallyIntegrableOn w Ω μ)
    (hfd : ∀ x ∈ (Ω : Set E), HasFDerivAt f (w x) x) :
    HasWeakIteratedLineDerivOn y f (fun x ↦ w x u) Ω μ := by
  subst hn
  have h := (hasWeakFDerivOn_of_hasFDerivAt hf hw hfd).lineDeriv y
  simpa [hy 0] using h

variable [Nontrivial E]

omit [BorelSpace E] [Nontrivial E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
private theorem norm_integral_le_mul_setIntegral_norm {g h : E → F} {s : Set E} {C : ℝ}
    (hg : Integrable g μ) (hh : IntegrableOn h s μ) (hs : MeasurableSet s)
    (hb : ∀ x, ‖g x‖ ≤ C * s.indicator (fun y ↦ ‖h y‖) x) :
    ‖∫ x, g x ∂μ‖ ≤ C * ∫ x in s, ‖h x‖ ∂μ := by
  refine le_trans (norm_integral_le_integral_norm g) (le_trans (integral_mono hg.norm ?_ hb) ?_)
  · exact ((integrable_indicator_iff hs).2 hh.norm).const_mul C
  · exact le_of_eq (by rw [integral_const_mul, integral_indicator hs])

/-- Almost every point differs from a given one: a point is null for an additive Haar measure on
a nontrivial space. -/
private theorem ae_ne_of_isAddHaarMeasure (a : E) : ∀ᵐ x ∂μ, x ≠ a := by
  have ha : μ ({a} : Set E) = 0 := by simp
  simp [ae_iff, ha]

/-- **The removable-singularity lemma for weak derivatives.** Let `f` be locally integrable on the
open set `Ω`, let `w` be locally integrable on `Ω`, and suppose that `w x` is the classical
derivative of `f` at every point of `Ω` other than `a`. If moreover

`∫_{B(a,δ)} ‖f‖ = o(δ)   as δ → 0⁺,`

then `w` is the weak derivative of `f` on all of `Ω`, the point `a` included.

Some such smallness is genuinely needed: on `ℝ` the Heaviside function is locally integrable, has
classical derivative `0` away from the origin, and has weak derivative a Dirac mass rather than
`0`. The proof integrates by parts against `φ · (1 - punctureBump a δ)`, a test function that
vanishes near `a`, and lets `δ → 0`; the term in which the cutoff is differentiated is `O(δ⁻¹)`
times the displayed integral, which is exactly why the displayed condition is the right one. -/
theorem hasWeakFDerivOn_of_hasFDerivAt_compl_singleton (hf : LocallyIntegrableOn f Ω μ)
    (hw : LocallyIntegrableOn w Ω μ)
    (hfd : ∀ x ∈ (Ω : Set E), x ≠ a → HasFDerivAt f (w x) x)
    (hlim : Tendsto (fun δ : ℝ ↦ δ⁻¹ * ∫ x in ball a δ, ‖f x‖ ∂μ) (𝓝[>] 0) (𝓝 0)) :
    HasWeakFDerivOn f w Ω μ := by
  refine hasWeakFDerivOn_iff.2 ⟨hf, hw, fun φ v ↦ ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show fderiv ℝ (φ : E → ℝ) x v = 0 from (φ.fderivApply v).eq_zero_of_notMem hx,
          zero_smul],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]]
  by_cases ha : a ∈ (Ω : Set E)
  swap
  · exact integral_fderiv_smul_eq_neg_integral_smul_apply hf hw φ
      (fun x hx ↦ hfd x (φ.tsupport_subset hx)
        fun hxa ↦ ha (hxa ▸ φ.tsupport_subset hx)) v
  -- The singular point lies in `Ω`. Cut it out with a cutoff of width `δ` and let `δ → 0`.
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall a r ⊆ (Ω : Set E) := by
    obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.1 Ω.isOpen a ha
    exact ⟨R / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hRsub⟩
  obtain ⟨K, hK0, hK⟩ := exists_norm_fderiv_punctureBump_le (E := E)
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM a)
  have hβ : ∀ δ : ℝ, ContDiff ℝ ∞ (punctureBump a δ) := fun δ ↦ contDiff_punctureBump a δ
  have hβ' : ∀ δ : ℝ, ContDiff ℝ ∞ fun x ↦ fderiv ℝ (punctureBump a δ) x v := fun δ ↦
    (((hβ δ).fderiv_right le_rfl).clm_apply contDiff_const)
  have hint : ∀ θ : 𝓓(Ω, ℝ), Integrable (fun x ↦ (θ : E → ℝ) x • f x) μ := fun θ ↦
    hf.integrable_smul_left_of_tsupport_subset θ.contDiff.continuous θ.hasCompactSupport
      θ.tsupport_subset
  have hintw : ∀ θ : 𝓓(Ω, ℝ), Integrable (fun x ↦ (θ : E → ℝ) x • w x v) μ := fun θ ↦ by
    have h := (hw.integrable_smul_left_of_tsupport_subset θ.contDiff.continuous
      θ.hasCompactSupport θ.tsupport_subset).apply_continuousLinearMap v
    simpa using h
  set I := ∫ x, fderiv ℝ (φ : E → ℝ) x v • f x ∂μ with hIdef
  set J := ∫ x, (φ : E → ℝ) x • w x v ∂μ with hJdef
  set A : ℝ → F := fun δ ↦
    ∫ x, (fderiv ℝ (φ : E → ℝ) x v * punctureBump a δ x) • f x ∂μ with hAdef
  set B : ℝ → F := fun δ ↦
    ∫ x, ((φ : E → ℝ) x * fderiv ℝ (punctureBump a δ) x v) • f x ∂μ with hBdef
  set C : ℝ → F := fun δ ↦
    ∫ x, ((φ : E → ℝ) x * punctureBump a δ x) • w x v ∂μ with hCdef
  -- The integration by parts identity at width `δ`.
  have hid : ∀ δ : ℝ, 0 < δ → I + J = A δ + B δ + C δ := by
    intro δ hδ
    set ψ : 𝓓(Ω, ℝ) := φ.mulContDiff (contDiff_const.sub (hβ δ)) with hψdef
    have hcoe : (ψ : E → ℝ) = fun x ↦ (φ : E → ℝ) x * (1 - punctureBump a δ x) := rfl
    have hzero : ∀ x ∈ ball a δ, (ψ : E → ℝ) x = 0 := fun x hx ↦ by
      rw [hcoe]
      simp [punctureBump_eq_one hδ (le_of_lt (mem_ball.1 hx))]
    have hsupp : tsupport (ψ : E → ℝ) ⊆ (ball a δ)ᶜ :=
      closure_minimal (fun x hx hmem ↦ hx (hzero x hmem)) isOpen_ball.isClosed_compl
    have key := integral_fderiv_smul_eq_neg_integral_smul_apply hf hw ψ
      (fun x hx ↦ hfd x (ψ.tsupport_subset hx)
        fun hxa ↦ hsupp hx (hxa ▸ mem_ball_self hδ)) v
    have hderiv : ∀ x, fderiv ℝ (ψ : E → ℝ) x v
        = fderiv ℝ (φ : E → ℝ) x v - fderiv ℝ (φ : E → ℝ) x v * punctureBump a δ x
          - (φ : E → ℝ) x * fderiv ℝ (punctureBump a δ) x v := by
      intro x
      have h1 : HasFDerivAt (φ : E → ℝ) (fderiv ℝ (φ : E → ℝ) x) x :=
        (φ.contDiff.differentiable (by simp) x).hasFDerivAt
      have h2 : HasFDerivAt (punctureBump a δ) (fderiv ℝ (punctureBump a δ) x) x :=
        ((hβ δ).differentiable (by simp) x).hasFDerivAt
      have h3 := h1.fun_mul (h2.const_sub (1 : ℝ))
      rw [hcoe, h3.fderiv]
      simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
      ring
    have e1 : ∫ x, fderiv ℝ (ψ : E → ℝ) x v • f x ∂μ = I - A δ - B δ := by
      have hfun : (fun x ↦ fderiv ℝ (ψ : E → ℝ) x v • f x)
          = fun x ↦ (fderiv ℝ (φ : E → ℝ) x v • f x
            - (fderiv ℝ (φ : E → ℝ) x v * punctureBump a δ x) • f x)
            - ((φ : E → ℝ) x * fderiv ℝ (punctureBump a δ) x v) • f x := by
        funext x; rw [hderiv x, sub_smul, sub_smul]
      have i1 : Integrable (fun x ↦ fderiv ℝ (φ : E → ℝ) x v • f x) μ :=
        hint (φ.fderivApply v)
      have i2 : Integrable
          (fun x ↦ (fderiv ℝ (φ : E → ℝ) x v * punctureBump a δ x) • f x) μ :=
        hint ((φ.fderivApply v).mulContDiff (hβ δ))
      have i3 : Integrable
          (fun x ↦ ((φ : E → ℝ) x * fderiv ℝ (punctureBump a δ) x v) • f x) μ :=
        hint (φ.mulContDiff (hβ' δ))
      have i12 : Integrable (fun x ↦ fderiv ℝ (φ : E → ℝ) x v • f x
          - (fderiv ℝ (φ : E → ℝ) x v * punctureBump a δ x) • f x) μ := i1.sub i2
      rw [hfun, integral_sub i12 i3, integral_sub i1 i2]
    have e2 : ∫ x, (ψ : E → ℝ) x • w x v ∂μ = J - C δ := by
      have hfun : (fun x ↦ (ψ : E → ℝ) x • w x v)
          = fun x ↦ (φ : E → ℝ) x • w x v - ((φ : E → ℝ) x * punctureBump a δ x) • w x v := by
        funext x; rw [hcoe]; simp [mul_sub, sub_smul]
      have i1 : Integrable (fun x ↦ (φ : E → ℝ) x • w x v) μ := hintw φ
      have i2 : Integrable (fun x ↦ ((φ : E → ℝ) x * punctureBump a δ x) • w x v) μ :=
        hintw (φ.mulContDiff (hβ δ))
      rw [hfun, integral_sub i1 i2]
    rw [e1, e2] at key
    have h0 : (I - A δ - B δ) - -(J - C δ) = 0 := sub_eq_zero_of_eq key
    have h1 : I + J - (A δ + B δ + C δ) = 0 := by rw [← h0]; abel
    exact sub_eq_zero.1 h1
  -- Almost every point differs from the singular one.
  have hae : ∀ᵐ x ∂μ, x ≠ a := ae_ne_of_isAddHaarMeasure a
  have hvanish : ∀ x : E, x ≠ a →
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ ∧ punctureBump a δ x = 0 := by
    intro x hx
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < dist x a / 2 by
        simpa using dist_pos.2 hx))] with δ h1 h2
    simp only [mem_Iio] at h2
    exact ⟨h1, punctureBump_eq_zero h1 (by linarith)⟩
  -- The two error terms in which the cutoff is not differentiated vanish by dominated convergence.
  have hAlim : Tendsto A (𝓝[>] 0) (𝓝 0) := by
    rw [hAdef, show (0 : F) = ∫ (_ : E), (0 : F) ∂μ by simp]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ ‖fderiv ℝ (φ : E → ℝ) x v • f x‖)
      (Eventually.of_forall fun δ ↦
        (hint ((φ.fderivApply v).mulContDiff (hβ δ))).aestronglyMeasurable)
      (Eventually.of_forall fun δ ↦ Eventually.of_forall fun x ↦ ?_)
      (hint (φ.fderivApply v)).norm ?_
    · calc ‖(fderiv ℝ (φ : E → ℝ) x v * punctureBump a δ x) • f x‖
          = |fderiv ℝ (φ : E → ℝ) x v| * (|punctureBump a δ x| * ‖f x‖) := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc]
        _ ≤ |fderiv ℝ (φ : E → ℝ) x v| * (1 * ‖f x‖) := by
            gcongr
            exact abs_le.2 ⟨by linarith [punctureBump_nonneg (a := a) (δ := δ) (x := x)],
              punctureBump_le_one⟩
        _ = ‖fderiv ℝ (φ : E → ℝ) x v • f x‖ := by rw [norm_smul, Real.norm_eq_abs, one_mul]
    · filter_upwards [hae] with x hx
      refine Tendsto.congr' (EventuallyEq.symm ?_) tendsto_const_nhds
      filter_upwards [hvanish x hx] with δ hδ
      rw [hδ.2, mul_zero, zero_smul]
  have hClim : Tendsto C (𝓝[>] 0) (𝓝 0) := by
    rw [hCdef, show (0 : F) = ∫ (_ : E), (0 : F) ∂μ by simp]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ ‖(φ : E → ℝ) x • w x v‖)
      (Eventually.of_forall fun δ ↦ (hintw (φ.mulContDiff (hβ δ))).aestronglyMeasurable)
      (Eventually.of_forall fun δ ↦ Eventually.of_forall fun x ↦ ?_) (hintw φ).norm ?_
    · calc ‖((φ : E → ℝ) x * punctureBump a δ x) • w x v‖
          = |(φ : E → ℝ) x| * (|punctureBump a δ x| * ‖w x v‖) := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc]
        _ ≤ |(φ : E → ℝ) x| * (1 * ‖w x v‖) := by
            gcongr
            exact abs_le.2 ⟨by linarith [punctureBump_nonneg (a := a) (δ := δ) (x := x)],
              punctureBump_le_one⟩
        _ = ‖(φ : E → ℝ) x • w x v‖ := by rw [norm_smul, Real.norm_eq_abs, one_mul]
    · filter_upwards [hae] with x hx
      refine Tendsto.congr' (EventuallyEq.symm ?_) tendsto_const_nhds
      filter_upwards [hvanish x hx] with δ hδ
      rw [hδ.2, mul_zero, zero_smul]
  -- The term in which the cutoff is differentiated is `O(δ⁻¹ ∫_{B(a,3δ)} ‖f‖)`.
  have h3 : Tendsto (fun δ : ℝ ↦ 3 * δ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun δ : ℝ ↦ 3 * δ) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const_mul (3 : ℝ)).tendsto (0 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact mul_pos three_pos (mem_Ioi.1 hδ)
  have hR : Tendsto (fun δ : ℝ ↦ δ⁻¹ * ∫ x in ball a (3 * δ), ‖f x‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have h := (hlim.comp h3).const_mul (3 : ℝ)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hne : δ ≠ 0 := ne_of_gt hδ
    simp only [Function.comp_apply]
    rw [mul_inv, ← mul_assoc, ← mul_assoc]
    norm_num
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 3 * δ ≤ r := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < r / 3 by positivity))]
      with δ hδ
    simp only [mem_Iio] at hδ
    linarith
  have hBlim : Tendsto B (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hR.const_mul (M * (K * ‖v‖)))
    filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδr
    replace hδ : (0 : ℝ) < δ := hδ
    have hfball : IntegrableOn f (ball a (3 * δ)) μ :=
      (hf.integrableOn_compact_subset
        ((closedBall_subset_closedBall hδr).trans hrsub) (isCompact_closedBall a (3 * δ))).mono_set
        ball_subset_closedBall
    have hb : ∀ x, ‖((φ : E → ℝ) x * fderiv ℝ (punctureBump a δ) x v) • f x‖
        ≤ M * (K * ‖v‖) * δ⁻¹ * (ball a (3 * δ)).indicator (fun y ↦ ‖f y‖) x := by
      intro x
      by_cases hx : x ∈ ball a (3 * δ)
      · rw [indicator_of_mem hx]
        have hφ : |(φ : E → ℝ) x| ≤ M := by simpa [Real.norm_eq_abs] using hM x
        have hd : |fderiv ℝ (punctureBump a δ) x v| ≤ K * ‖v‖ * δ⁻¹ := by
          have h1 : ‖fderiv ℝ (punctureBump a δ) x v‖
              ≤ ‖fderiv ℝ (punctureBump a δ) x‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ _
          have h2 : ‖fderiv ℝ (punctureBump a δ) x‖ ≤ K / δ := hK a δ hδ x
          rw [Real.norm_eq_abs] at h1
          calc |fderiv ℝ (punctureBump a δ) x v| ≤ ‖fderiv ℝ (punctureBump a δ) x‖ * ‖v‖ := h1
            _ ≤ (K / δ) * ‖v‖ := by gcongr
            _ = K * ‖v‖ * δ⁻¹ := by ring
        calc ‖((φ : E → ℝ) x * fderiv ℝ (punctureBump a δ) x v) • f x‖
            = |(φ : E → ℝ) x| * |fderiv ℝ (punctureBump a δ) x v| * ‖f x‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_mul]
          _ ≤ M * (K * ‖v‖ * δ⁻¹) * ‖f x‖ := by gcongr
          _ = M * (K * ‖v‖) * δ⁻¹ * ‖f x‖ := by ring
      · rw [indicator_of_notMem hx, mul_zero]
        rw [mem_ball, not_lt] at hx
        rw [fderiv_punctureBump_eq_zero hδ (by linarith)]
        simp
    have hbnd := norm_integral_le_mul_setIntegral_norm (μ := μ)
      (hint (φ.mulContDiff (hβ' δ))) hfball measurableSet_ball hb
    calc ‖B δ‖ ≤ M * (K * ‖v‖) * δ⁻¹ * ∫ x in ball a (3 * δ), ‖f x‖ ∂μ := hbnd
      _ = M * (K * ‖v‖) * (δ⁻¹ * ∫ x in ball a (3 * δ), ‖f x‖ ∂μ) := by ring
  -- Conclude: the constant `I + J` is the limit of a family tending to zero.
  have hsum : Tendsto (fun δ : ℝ ↦ A δ + B δ + C δ) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hAlim.add hBlim).add hClim
  have hconst : Tendsto (fun _ : ℝ ↦ I + J) (𝓝[>] 0) (𝓝 0) :=
    hsum.congr' (by filter_upwards [self_mem_nhdsWithin] with δ hδ using (hid δ hδ).symm)
  have hIJ : I + J = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  exact eq_neg_of_add_eq_zero_left hIJ

/-- **The removable-singularity lemma along a single direction.** The same hypotheses as
`hasWeakFDerivOn_of_hasFDerivAt_compl_singleton` give the weak derivative in the form indexed by a
tuple of directions, which is how a Sobolev space indexed by multi-indices asks for a first-order
derivative: the tuple has length one and its single entry is the direction `u`. -/
theorem hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton {n : ℕ} {y : Fin n → E} {u : E}
    (hn : n = 1) (hy : ∀ i, y i = u) (hf : LocallyIntegrableOn f Ω μ)
    (hw : LocallyIntegrableOn w Ω μ)
    (hfd : ∀ x ∈ (Ω : Set E), x ≠ a → HasFDerivAt f (w x) x)
    (hlim : Tendsto (fun δ : ℝ ↦ δ⁻¹ * ∫ x in ball a δ, ‖f x‖ ∂μ) (𝓝[>] 0) (𝓝 0)) :
    HasWeakIteratedLineDerivOn y f (fun x ↦ w x u) Ω μ := by
  subst hn
  have h := (hasWeakFDerivOn_of_hasFDerivAt_compl_singleton hf hw hfd hlim).lineDeriv y
  simpa [hy 0] using h


end RemovableSingularity

/-! ### A sufficient condition for the smallness hypothesis -/

section Smallness

open Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The integral of `‖x‖ ^ s` over a ball about the origin scales like `δ ^ (d + s)`, with `d` the
dimension: the integrand is homogeneous of degree `s` and the measure of degree `d`. -/
theorem setIntegral_norm_rpow_ball_zero {s δ : ℝ} (hδ : 0 < δ) :
    ∫ x in ball (0 : E) δ, ‖x‖ ^ s ∂μ
      = δ ^ finrank ℝ E * (δ ^ s * ∫ x in ball (0 : E) 1, ‖x‖ ^ s ∂μ) := by
  have hne : (δ : ℝ) ^ finrank ℝ E ≠ 0 := by positivity
  have h := Measure.setIntegral_comp_smul_of_pos μ (fun y : E ↦ ‖y‖ ^ s) (ball (0 : E) 1) hδ
  rw [smul_unitBall_of_pos hδ] at h
  have hlhs : ∫ x in ball (0 : E) 1, ‖δ • x‖ ^ s ∂μ
      = δ ^ s * ∫ x in ball (0 : E) 1, ‖x‖ ^ s ∂μ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun x _ ↦ ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, Real.mul_rpow hδ.le (norm_nonneg x)]
  rw [hlhs, smul_eq_mul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- A power `‖x‖ ^ s` with `s > -d` is integrable on every ball about the origin. -/
theorem integrableOn_norm_rpow_ball_zero (hd : 1 ≤ finrank ℝ E) {s : ℝ}
    (hs : -(finrank ℝ E : ℝ) < s) (t : ℝ) :
    IntegrableOn (fun x : E ↦ ‖x‖ ^ s) (ball (0 : E) t) μ := by
  refine integrableOn_ball_of_norm_le_rpow hd (C := 1) (α := -s) (by linarith)
    (Eventually.of_forall fun x ↦ ?_) (measurable_norm.pow measurable_const).aestronglyMeasurable
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) s), one_mul, neg_neg]

/-- **A sufficient condition for the smallness hypothesis of
`hasWeakFDerivOn_of_hasFDerivAt_compl_singleton`.** If `‖f x‖ ≤ C ‖x‖ ^ s` near the origin for
some `s > 1 - d`, `d` being the dimension of the ambient space, then
`∫_{B(0,δ)} ‖f‖ = o(δ)` as `δ → 0⁺`.

Every radial singularity milder than `‖x‖^{1-d}` qualifies, and in particular every logarithmic
one, since `|log ‖x‖|^m ≤ C ‖x‖^{-ε}` near the origin for every `ε > 0`. The statement is at the
origin because that is where a radial singularity sits; the general case follows by translating,
the measure being invariant. -/
theorem tendsto_inv_mul_setIntegral_norm_ball_zero (hd : 1 ≤ finrank ℝ E) {f : E → F} {C s R : ℝ}
    (hR : 0 < R) (hs : 1 - (finrank ℝ E : ℝ) < s) (hmeas : AEStronglyMeasurable f μ)
    (hle : ∀ x ∈ ball (0 : E) R, ‖f x‖ ≤ C * ‖x‖ ^ s) :
    Tendsto (fun δ : ℝ ↦ δ⁻¹ * ∫ x in ball (0 : E) δ, ‖f x‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hd' : (1 : ℝ) ≤ (finrank ℝ E : ℝ) := mod_cast hd
  have hsd : -(finrank ℝ E : ℝ) < s := by linarith
  have hq : 0 < (finrank ℝ E : ℝ) + s - 1 := by linarith
  set C' : ℝ := max C 0 with hC'def
  have hC' : 0 ≤ C' := le_max_right _ _
  have hle' : ∀ x ∈ ball (0 : E) R, ‖f x‖ ≤ C' * ‖x‖ ^ s := fun x hx ↦
    le_trans (hle x hx)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg x) s))
  set G : ℝ := ∫ x in ball (0 : E) 1, ‖x‖ ^ s ∂μ with hGdef
  have hcmp : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      δ⁻¹ * ∫ x in ball (0 : E) δ, ‖f x‖ ∂μ ≤ C' * G * δ ^ ((finrank ℝ E : ℝ) + s - 1) := by
    intro δ hδ hδR
    have hsub : ball (0 : E) δ ⊆ ball (0 : E) R := ball_subset_ball hδR
    have hpow : IntegrableOn (fun x : E ↦ C' * ‖x‖ ^ s) (ball (0 : E) δ) μ :=
      (integrableOn_norm_rpow_ball_zero hd hsd δ).const_mul C'
    have hfint : IntegrableOn f (ball (0 : E) δ) μ := by
      refine Integrable.mono' hpow hmeas.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx using hle' x (hsub hx)
    have hint : ∫ x in ball (0 : E) δ, ‖f x‖ ∂μ ≤ C' * (δ ^ finrank ℝ E * (δ ^ s * G)) := by
      rw [hGdef, ← setIntegral_norm_rpow_ball_zero hδ, ← integral_const_mul]
      refine integral_mono_ae hfint.norm hpow ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx using hle' x (hsub hx)
    have hpow2 : δ ^ finrank ℝ E * δ ^ s * δ⁻¹ = δ ^ ((finrank ℝ E : ℝ) + s - 1) := by
      rw [← Real.rpow_natCast δ (finrank ℝ E), ← Real.rpow_neg_one δ, ← Real.rpow_add hδ,
        ← Real.rpow_add hδ]
      ring_nf
    calc δ⁻¹ * ∫ x in ball (0 : E) δ, ‖f x‖ ∂μ
        ≤ δ⁻¹ * (C' * (δ ^ finrank ℝ E * (δ ^ s * G))) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = C' * G * δ ^ ((finrank ℝ E : ℝ) + s - 1) := by rw [← hpow2]; ring
  refine squeeze_zero' (g := fun δ : ℝ ↦ C' * G * δ ^ ((finrank ℝ E : ℝ) + s - 1)) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    replace hδ : (0 : ℝ) < δ := hδ
    exact mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_ball fun x _ ↦ norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hR)] with δ hδ hδR
    exact hcmp δ hδ (le_of_lt hδR)
  · have hc := (Real.continuousAt_rpow_const (0 : ℝ) ((finrank ℝ E : ℝ) + s - 1)
      (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hq)] at hc
    simpa using (hc.mono_left nhdsWithin_le_nhds).const_mul (C' * G)

end Smallness
