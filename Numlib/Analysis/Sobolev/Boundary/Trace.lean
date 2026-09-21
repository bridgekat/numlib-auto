import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Sobolev.Boundary.Data
import Numlib.Analysis.Sobolev.Boundary.Density

/-!
# The trace theorem from a transversal field

The trace theorem from a transversal field — Nečas's proof, decision B7 of
`notes/boundary/planning-brief.md` — over the abstract `BoundaryData Ω` of `Boundary/Data.lean`
and the density predicates of `Boundary/Density.lean`; the two concrete instances are the bounded
`C¹` domains (`Boundary/ContDiffDomain.lean`) and the triangles (`Boundary/PolygonTrace.lean`).

A **transversal field** is a `C¹` compactly supported `w : ℝ^N → ℝ^N` with `⟪w, ν⟫ ≥ 1` `σ`-a.e.
(`BoundaryData.HasTransversalField`). For `u ∈ C¹_c(ℝ^N)` and `1 ≤ p < ∞` the divergence
theorem applied to `φ_ε(u) w`, `φ_ε(t) = (t² + ε²)^{p/2} − ε^p` (`Real.rpowReg`), gives
**Nečas's inequality**
`∫_{∂Ω} |u|^p dσ ≤ C (∫_Ω |u|^p + ∫_Ω |u|^{p−1} |∇u|)` with `C` depending on `w` and `p` only
(`BoundaryData.integral_abs_rpow_le_of_contDiff`; the regularization `φ_ε` is what makes `p = 1`
work, `|t|^p` not being `C¹` there), hence `‖u|_{∂Ω}‖_{L^p(σ)} ≤ C' ‖u‖_{W^{1,p}(Ω)}`
(`BoundaryData.eLpNorm_le_of_contDiff`). Restriction to `∂Ω` is therefore a bounded linear map on
the subspace `SobolevEuclidean.smoothRestrictions` of smooth-representable elements
(`BoundaryData.traceSmoothL`), dense under `HasSmoothDensity` ([brezis2011functional]
Corollary 9.8 on `C¹` domains, the segment property elsewhere), and `BoundaryData.traceL` is its
continuous extension (`ContinuousLinearMap.extend`; the density hypothesis enters the lemmas, not
the definition, as for Mathlib's `extend`). Then: `Tu = ũ|_{∂Ω}` for `ũ` continuous up to the
boundary (`traceL_ae_eq_of_continuousOn`, under `HasUniformSmoothDensity`), uniqueness
(`traceL_unique`, `TraceFamily.traceL_eq_of_hasSmoothDensity`), Green's formula
`∫_Ω ∂ᵢu v + ∫_Ω u ∂ᵢv = ∫ Tu Tv νᵢ dσ` at conjugate exponents by density from
`BoundaryData.integral_fderiv_mul_add_eq` (`green_of_hasSmoothDensity`,
`green_contDiff_of_hasSmoothDensity`), the assembly `BoundaryData.traceFamily : B.TraceFamily`,
the sharper inequality for all `u ∈ W^{1,p}` (`integral_abs_traceL_rpow_le`) and with it the
**compactness** of the trace from Rellich–Kondrachov for `1 < p` (`isCompactOperator_traceL`,
Atkinson–Han Theorem 7.3.10 (c); at `p = 1` the trace `W^{1,1} → L¹(∂Ω)` is onto, hence not
compact, so the book's `1 ≤ p` is an erratum).

The kernel characterization `ker T = W_0^{1,p}(Ω)` (the hard half) is chart-local and lives in
`Boundary/Kernel.lean`; the fractional range `W^{1−1/p,p}(∂Ω)` is out of scope.

Sources: Nečas, *Direct Methods in the Theory of Elliptic Equations*, Ch. 2 §4; Evans, *PDE*,
§5.5 Theorem 1; Grisvard, *Elliptic Problems in Nonsmooth Domains*, Theorems 1.5.1.3 and
1.5.3.1; Atkinson–Han §7.3 and §7.6; [brezis2011functional] Comments on chapter 9.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace Topology

noncomputable section

/-! ### The regularization `φ_ε t = (t² + ε²)^{p/2} − ε^p` of `|t|^p` -/

namespace Real

/-- **The regularization `(t² + ε²)^{p/2} − ε^p` of `|t|^p`**, smooth in `t` for `ε > 0`, with
`φ_ε 0 = 0`, `0 ≤ φ_ε t ≤ (|t| + ε)^p`, `|φ_ε' t| ≤ p (|t| + ε)^{p−1}` and `φ_ε t → |t|^p` as
`ε → 0`. It is what makes Nečas's proof of the trace inequality work at `p = 1`, where `|t|^p` is
not `C¹`. -/
def rpowReg (p ε t : ℝ) : ℝ := (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p

variable {p ε : ℝ}

/-- `t² + ε² > 0` for `ε > 0`. -/
theorem sq_add_sq_pos (hε : 0 < ε) (t : ℝ) : 0 < t ^ 2 + ε ^ 2 := by positivity

/-- `φ_ε 0 = 0`. -/
theorem rpowReg_zero (hε : 0 < ε) : rpowReg p ε 0 = 0 := by
  have h : (0 : ℝ) ^ 2 + ε ^ 2 = ε ^ 2 := by ring
  unfold rpowReg
  rw [sub_eq_zero, h, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
  congr 1
  push_cast
  ring

/-- `φ_ε ≥ 0`. -/
theorem rpowReg_nonneg (hε : 0 < ε) (hp : 0 ≤ p) (t : ℝ) : 0 ≤ rpowReg p ε t := by
  unfold rpowReg
  rw [sub_nonneg]
  calc ε ^ p = (ε ^ 2) ^ (p / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
        congr 1
        push_cast
        ring
    _ ≤ (t ^ 2 + ε ^ 2) ^ (p / 2) :=
        Real.rpow_le_rpow (by positivity) (le_add_of_nonneg_left (by positivity))
          (by positivity)

/-- `φ_ε t ≤ (|t| + ε)^p`. -/
theorem rpowReg_le (hε : 0 < ε) (hp : 0 ≤ p) (t : ℝ) : rpowReg p ε t ≤ (|t| + ε) ^ p := by
  unfold rpowReg
  calc (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p ≤ (t ^ 2 + ε ^ 2) ^ (p / 2) :=
        sub_le_self _ (Real.rpow_nonneg hε.le _)
    _ ≤ ((|t| + ε) ^ 2) ^ (p / 2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        nlinarith [abs_nonneg t, sq_abs t]
    _ = (|t| + ε) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring

/-- The derivative of `φ_ε`: `φ_ε' t = p t (t² + ε²)^{p/2 − 1}`. -/
theorem hasDerivAt_rpowReg (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (rpowReg p ε) (p * t * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ t ^ 2 + ε ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_pow 2 t).add_const (ε ^ 2))
  have h2 := h1.rpow_const (p := p / 2) (Or.inl (sq_add_sq_pos hε t).ne')
  have h3 : HasDerivAt (fun t : ℝ ↦ (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p)
      (2 * t * (p / 2) * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)) t := h2.sub_const (ε ^ p)
  exact h3.congr_deriv (by ring)

/-- `φ_ε` is `C¹` (indeed smooth). -/
theorem contDiff_rpowReg (hε : 0 < ε) {n : WithTop ℕ∞} : ContDiff ℝ n (rpowReg p ε) := by
  unfold rpowReg
  refine ContDiff.sub ?_ contDiff_const
  exact ((contDiff_id.pow 2).add contDiff_const).rpow_const_of_ne fun t ↦ (sq_add_sq_pos hε t).ne'

/-- `|φ_ε' t| ≤ p (|t| + ε)^{p−1}` for `p ≥ 1`. -/
theorem abs_deriv_rpowReg_le (hε : 0 < ε) (hp : 1 ≤ p) (t : ℝ) :
    |p * t * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)| ≤ p * (|t| + ε) ^ (p - 1) := by
  have hpos := sq_add_sq_pos hε t
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg (Real.rpow_nonneg hpos.le _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hp0
  have h1 : |t| ≤ (t ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))
  calc |t| * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)
      ≤ (t ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hpos.le _)
    _ = (t ^ 2 + ε ^ 2) ^ ((p - 1) / 2) := by
        rw [← Real.rpow_add hpos]
        ring_nf
    _ ≤ ((|t| + ε) ^ 2) ^ ((p - 1) / 2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
        nlinarith [abs_nonneg t, sq_abs t]
    _ = (|t| + ε) ^ (p - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring

/-- `φ_ε t → |t|^p` as `ε → 0⁺`. -/
theorem tendsto_rpowReg (hp : 0 < p) (t : ℝ) :
    Tendsto (fun ε ↦ rpowReg p ε t) (𝓝[>] 0) (𝓝 (|t| ^ p)) := by
  have h1 : Tendsto (fun ε : ℝ ↦ (t ^ 2 + ε ^ 2) ^ (p / 2)) (𝓝[>] 0) (𝓝 ((t ^ 2) ^ (p / 2))) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x ^ (p / 2)) (t ^ 2) :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))
    have h : Tendsto (fun ε : ℝ ↦ t ^ 2 + ε ^ 2) (𝓝[>] 0) (𝓝 (t ^ 2)) := by
      have hc' : Continuous (fun ε : ℝ ↦ t ^ 2 + ε ^ 2) := by fun_prop
      have := (hc'.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    exact hc.tendsto.comp h
  have h2 : Tendsto (fun ε : ℝ ↦ ε ^ p) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.zero_rpow hp.ne'] using this
  have h3 : (t ^ 2 : ℝ) ^ (p / 2) = |t| ^ p := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
    congr 1
    push_cast
    ring
  have := h1.sub h2
  rw [sub_zero, h3] at this
  exact this

end Real

/-! ### Small general lemmas -/

section General

variable {N : ℕ}

/-- The operator norm of the derivative of `u : ℝ^N → ℝ` is the Euclidean norm of the tuple of
partial derivatives `(∂ᵢu x)ᵢ`. -/
theorem EuclideanSpace.norm_fderiv_eq (u : EuclideanSpace ℝ (Fin N) → ℝ)
    (x : EuclideanSpace ℝ (Fin N)) :
    ‖fderiv ℝ u x‖
      = ‖(WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :
          PiLp 2 fun _ : Fin N ↦ ℝ)‖ := by
  have h : gradient u x
      = (WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :
          PiLp 2 fun _ : Fin N ↦ ℝ) := by
    ext i
    rw [gradient, PiLp.toLp_apply]
    have h2 : ∀ w : EuclideanSpace ℝ (Fin N), w i = ⟪w, EuclideanSpace.single i 1⟫_ℝ := fun w ↦ by
      rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    rw [h2, InnerProductSpace.toDual_symm_apply]
  rw [← h, gradient, LinearIsometryEquiv.norm_map]

/-- `|div w x| ≤ N ‖Dw(x)‖`. -/
theorem EuclideanSpace.abs_div_le (w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) : |EuclideanSpace.div w x| ≤ N * ‖fderiv ℝ w x‖ := by
  unfold EuclideanSpace.div
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ i : Fin N, |fderiv ℝ w x (EuclideanSpace.single i 1) i| ≤ ‖fderiv ℝ w x‖ := fun i ↦ by
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le _ i).trans ?_
    refine ((fderiv ℝ w x).le_opNorm _).trans ?_
    simp
  refine (Finset.sum_le_sum fun i _ ↦ h i).trans ?_
  simp

/-- `a^{p−1} b ≤ a^p + b^p` for `a, b ≥ 0` and `p ≥ 1` (the crude Young inequality). -/
theorem Real.rpow_sub_one_mul_le_add {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    a ^ (p - 1) * b ≤ a ^ p + b ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  rcases le_total a b with hab | hab
  · calc a ^ (p - 1) * b ≤ b ^ (p - 1) * b :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha hab (by linarith)) hb
      _ = b ^ p := by
          rw [← Real.rpow_add_one' hb (by linarith), sub_add_cancel]
      _ ≤ a ^ p + b ^ p := le_add_of_nonneg_left (Real.rpow_nonneg ha _)
  · calc a ^ (p - 1) * b ≤ a ^ (p - 1) * a :=
          mul_le_mul_of_nonneg_left hab (Real.rpow_nonneg ha _)
      _ = a ^ p := by
          rw [← Real.rpow_add_one' ha (by linarith), sub_add_cancel]
      _ ≤ a ^ p + b ^ p := le_add_of_nonneg_right (Real.rpow_nonneg hb _)

end General

section Sobolev

variable {N : ℕ} {p : ℝ≥0∞} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- The partial derivatives of an element `U` of `W^{1,p}(Ω)` whose function is a `C¹` function
`u` are the classical ones, almost everywhere on `Ω` (at every `p`; the `H¹` case is
`Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn`). -/
theorem SobolevEuclidean.weakDeriv_single_ae_eq_fderiv (U : SobolevEuclidean N 1 p Ω)
    {u : EuclideanSpace ℝ (Fin N) → ℝ} (hu : ContDiff ℝ 1 u)
    (hU : fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) (i : Fin N) :
    (weakDeriv U (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :=
  SobolevEuclidean.weakDeriv_single_ae_eq U hU (hu.contDiffOn.hasWeakIteratedLineDerivOn_single Ω i)

/-- The pointwise gradient of an element of `W^{1,p}(Ω)` with a `C¹` function `u` has the norm
of `Du`, almost everywhere on `Ω`. -/
theorem SobolevEuclidean.norm_fderiv_ae_eq_norm_gradFn (U : SobolevEuclidean N 1 p Ω)
    {u : EuclideanSpace ℝ (Fin N) → ℝ} (hu : ContDiff ℝ 1 u)
    (hU : fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) :
    (fun x ↦ ‖fderiv ℝ u x‖) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ ‖gradFn U x‖ := by
  have h := ae_all_iff.2 fun i : Fin N ↦ SobolevEuclidean.weakDeriv_single_ae_eq_fderiv U hu hU i
  filter_upwards [h] with x hx
  rw [EuclideanSpace.norm_fderiv_eq]
  congr 1
  ext i
  rw [PiLp.toLp_apply, gradFn_apply, hx i]

/-- **The chosen smooth representative** of an element of `smoothRestrictions`: a `C^∞`
compactly supported function on `ℝ^N` equal to `fn u` almost everywhere on `Ω`. -/
def SobolevEuclidean.smoothRep (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    EuclideanSpace ℝ (Fin N) → ℝ :=
  Classical.choose (SobolevEuclidean.exists_contDiff_of_mem_smoothRestrictions u.2)

/-- The smooth representative is smooth. -/
theorem SobolevEuclidean.contDiff_smoothRep (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    ContDiff ℝ ∞ (SobolevEuclidean.smoothRep u) :=
  (Classical.choose_spec (SobolevEuclidean.exists_contDiff_of_mem_smoothRestrictions u.2)).1

/-- The smooth representative is continuous. -/
theorem SobolevEuclidean.continuous_smoothRep (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    Continuous (SobolevEuclidean.smoothRep u) :=
  (SobolevEuclidean.contDiff_smoothRep u).continuous

/-- The smooth representative has compact support. -/
theorem SobolevEuclidean.hasCompactSupport_smoothRep
    (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    HasCompactSupport (SobolevEuclidean.smoothRep u) :=
  (Classical.choose_spec (SobolevEuclidean.exists_contDiff_of_mem_smoothRestrictions u.2)).2.1

/-- The smooth representative represents `u` on `Ω`. -/
theorem SobolevEuclidean.fn_ae_eq_smoothRep (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    fn (u : SobolevEuclidean N 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] SobolevEuclidean.smoothRep u :=
  (Classical.choose_spec (SobolevEuclidean.exists_contDiff_of_mem_smoothRestrictions u.2)).2.2

end Sobolev

namespace BoundaryData

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω)

/-- The ambient space `ℝ^N`, locally. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-! ### Transversal fields -/

/-- **A transversal field** for the boundary data `B`: a `C¹` compactly supported vector field
`w : ℝ^N → ℝ^N` pointing strictly outward along `∂Ω`, `⟪w, ν⟫ ≥ 1` `σ`-a.e. (Nečas; the
normalization `≥ 1` rather than `> 0` costs nothing on a compact boundary and saves a compactness
argument). Instances: `IsContDiffDomain.hasTransversalField` (`ContDiffDomain.lean`) and the
triangles (`PolygonTrace.lean`, `w = c (x − x₀)` for an interior point `x₀`). A pinched polygon
(two triangles meeting at a vertex) has none, which is why this is a hypothesis of the trace
construction and not a field of `BoundaryData`. -/
def HasTransversalField : Prop :=
  ∃ w : 𝔼 → 𝔼, ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ ∀ᵐ x ∂B.σ, 1 ≤ ⟪w x, B.ν x⟫_ℝ

/-! ### Integrability on `σ` and on `Ω` -/

include B in
/-- The Lebesgue measure of the bounded `Ω` is finite. -/
theorem isFiniteMeasure_volume_restrict : IsFiniteMeasure (volume.restrict (Ω : Set 𝔼)) :=
  MeasureTheory.isFiniteMeasure_restrict.2 B.isBounded.measure_lt_top.ne

/-- A function continuous on `closure Ω` is in every `L^p(σ)`. -/
theorem memLp_of_continuousOn {G : Type*} [NormedAddCommGroup G] {f : 𝔼 → G}
    (hf : ContinuousOn f (closure (Ω : Set 𝔼))) (p : ℝ≥0∞) : MemLp f p B.σ := by
  have hae : ∀ᵐ x ∂B.σ, x ∈ closure (Ω : Set 𝔼) :=
    B.ae_mem_frontier.mono fun x hx ↦ frontier_subset_closure hx
  have hm : AEStronglyMeasurable f B.σ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hf.aestronglyMeasurable isClosed_closure.measurableSet
  obtain ⟨C, hC⟩ := B.isBounded.isCompact_closure.exists_bound_of_continuousOn hf
  exact MemLp.of_bound hm C (hae.mono fun x hx ↦ hC x hx)

/-- A continuous function is in every `L^p(σ)`. -/
theorem memLp_of_continuous {G : Type*} [NormedAddCommGroup G] {f : 𝔼 → G} (hf : Continuous f)
    (p : ℝ≥0∞) : MemLp f p B.σ :=
  B.memLp_of_continuousOn hf.continuousOn p

/-- A continuous function is `σ`-integrable. -/
theorem integrable_of_continuous {G : Type*} [NormedAddCommGroup G] {f : 𝔼 → G}
    (hf : Continuous f) : Integrable f B.σ :=
  memLp_one_iff_integrable.1 (B.memLp_of_continuous hf 1)

include B in
/-- A continuous function is integrable on the bounded `Ω`. -/
theorem integrableOn_of_continuous {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : 𝔼 → G} (hf : Continuous f) : IntegrableOn f (Ω : Set 𝔼) :=
  B.integrableOn_of_continuousOn hf.continuousOn

/-! ### Nečas's inequality -/

/-- **The divergence-theorem step of Nečas's inequality at a fixed `ε`**: for a transversal
field `w` with `‖w‖ ≤ M₀`, `‖Dw‖ ≤ M₁`, and `u ∈ C¹(ℝ^N)`,
`∫ φ_ε(u) dσ ≤ max (N M₁) (p M₀) (∫_Ω (|u| + ε)^p + ∫_Ω (|u| + ε)^{p−1} ‖∇u‖)`.
The divergence theorem for `F_ε = φ_ε(u) w`: the boundary term dominates `∫ φ_ε(u) dσ` because
`φ_ε ≥ 0` and `⟪w, ν⟫ ≥ 1`, and `div F_ε = φ_ε'(u) ⟪∇u, w⟫ + φ_ε(u) div w` is bounded by the
derivative estimates of `Real.rpowReg`. -/
theorem integral_rpowReg_le {w : 𝔼 → 𝔼} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w)
    (hwν : ∀ᵐ x ∂B.σ, 1 ≤ ⟪w x, B.ν x⟫_ℝ) {M₀ M₁ : ℝ} (hM₀ : ∀ x, ‖w x‖ ≤ M₀)
    (hM₁ : ∀ x, ‖fderiv ℝ w x‖ ≤ M₁) {p : ℝ} (hp : 1 ≤ p) {ε : ℝ} (hε : 0 < ε)
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫ x, Real.rpowReg p ε (u x) ∂B.σ
      ≤ max (N * M₁) (p * M₀) * ((∫ x in (Ω : Set 𝔼), (|u x| + ε) ^ p)
        + ∫ x in (Ω : Set 𝔼), (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hφ : ContDiff ℝ 1 (Real.rpowReg p ε) := Real.contDiff_rpowReg hε
  have hφu : ContDiff ℝ 1 (fun x ↦ Real.rpowReg p ε (u x)) := hφ.comp hu
  have hF : ContDiff ℝ 1 (fun x ↦ Real.rpowReg p ε (u x) • w x) := hφu.smul hw
  have hFc : HasCompactSupport (fun x ↦ Real.rpowReg p ε (u x) • w x) :=
    HasCompactSupport.smul_left (f := fun x ↦ Real.rpowReg p ε (u x)) hwc
  have hdiv := B.integral_div_eq_of_contDiff hF
  -- the boundary term dominates `∫ φ_ε(u) dσ`
  have h1 : ∫ x, Real.rpowReg p ε (u x) ∂B.σ
      ≤ ∫ x, ⟪Real.rpowReg p ε (u x) • w x, B.ν x⟫_ℝ ∂B.σ := by
    refine integral_mono_ae (B.integrable_of_continuous hφu.continuous) ?_
      (hwν.mono fun x hx ↦ ?_)
    · obtain ⟨K, hK⟩ := hF.continuous.bounded_above_of_compact_support hFc
      refine Integrable.of_bound (hF.continuous.aestronglyMeasurable.inner
        B.aestronglyMeasurable_ν) K (B.ae_norm_ν.mono fun x hx ↦ ?_)
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by rw [hx, mul_one]; exact hK x)
    · dsimp only
      rw [real_inner_smul_left]
      exact le_mul_of_one_le_right (Real.rpowReg_nonneg hε hp0 _) hx
  -- the interior term, pointwise
  have hcont₁ : Continuous fun x ↦ (|u x| + ε) ^ p :=
    (hu.continuous.abs.add continuous_const).rpow_const fun x ↦ Or.inr hp0
  have hcont₂ : Continuous fun x ↦ (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖ :=
    ((hu.continuous.abs.add continuous_const).rpow_const fun x ↦ Or.inr (by linarith)).mul
      (hu.continuous_fderiv one_ne_zero).norm
  have hdivc : Continuous (EuclideanSpace.div fun x ↦ Real.rpowReg p ε (u x) • w x) := by
    unfold EuclideanSpace.div
    exact continuous_finsetSum _ fun i _ ↦ (PiLp.continuous_apply 2 _ i).comp
      ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have h2 : ∫ x in (Ω : Set 𝔼), EuclideanSpace.div (fun x ↦ Real.rpowReg p ε (u x) • w x) x
      ≤ ∫ x in (Ω : Set 𝔼), max (N * M₁) (p * M₀)
        * ((|u x| + ε) ^ p + (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by
    refine integral_mono (B.integrableOn_of_continuous hdivc)
      ((B.integrableOn_of_continuous (hcont₁.add hcont₂)).const_mul _) fun x ↦ ?_
    -- the product rule and the chain rule
    have hux : DifferentiableAt ℝ u x := (hu.differentiable one_ne_zero).differentiableAt
    have hwx : DifferentiableAt ℝ w x := (hw.differentiable one_ne_zero).differentiableAt
    have hφx : DifferentiableAt ℝ (fun x ↦ Real.rpowReg p ε (u x)) x :=
      (hφu.differentiable one_ne_zero).differentiableAt
    rw [EuclideanSpace.div_smul_fun hφx hwx]
    have hgrad : ⟪gradient (fun x ↦ Real.rpowReg p ε (u x)) x, w x⟫_ℝ
        = p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (w x) := by
      have hd : HasFDerivAt (fun x ↦ Real.rpowReg p ε (u x))
          ((p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1)) • fderiv ℝ u x) x :=
        (Real.hasDerivAt_rpowReg hε (u x)).comp_hasFDerivAt x hux.hasFDerivAt
      rw [gradient, InnerProductSpace.toDual_symm_apply, hd.fderiv]
      simp only [smul_apply, smul_eq_mul]
    rw [hgrad]
    have hA : |p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (w x)|
        ≤ p * M₀ * ((|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by
      rw [abs_mul]
      calc |p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1)| * |fderiv ℝ u x (w x)|
          ≤ p * (|u x| + ε) ^ (p - 1) * (‖fderiv ℝ u x‖ * M₀) := by
            refine mul_le_mul (Real.abs_deriv_rpowReg_le hε hp _) ?_ (abs_nonneg _)
              (by positivity)
            rw [← Real.norm_eq_abs]
            exact ((fderiv ℝ u x).le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (hM₀ x) (norm_nonneg _))
        _ = p * M₀ * ((|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by ring
    have hB : |Real.rpowReg p ε (u x) * EuclideanSpace.div w x|
        ≤ N * M₁ * (|u x| + ε) ^ p := by
      rw [abs_mul, abs_of_nonneg (Real.rpowReg_nonneg hε hp0 _)]
      calc Real.rpowReg p ε (u x) * |EuclideanSpace.div w x|
          ≤ (|u x| + ε) ^ p * (N * ‖fderiv ℝ w x‖) :=
            mul_le_mul (Real.rpowReg_le hε hp0 _) (EuclideanSpace.abs_div_le w x)
              (abs_nonneg _) (by positivity)
        _ ≤ (|u x| + ε) ^ p * (N * M₁) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM₁ x) (by positivity))
              (by positivity)
        _ = N * M₁ * (|u x| + ε) ^ p := by ring
    have hmax₁ : p * M₀ ≤ max (N * M₁) (p * M₀) := le_max_right _ _
    have hmax₂ : N * M₁ ≤ max (N * M₁) (p * M₀) := le_max_left _ _
    have hnn₁ : 0 ≤ (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖ := by positivity
    have hnn₂ : 0 ≤ (|u x| + ε) ^ p := by positivity
    calc p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (w x)
          + Real.rpowReg p ε (u x) * EuclideanSpace.div w x
        ≤ |p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (w x)|
          + |Real.rpowReg p ε (u x) * EuclideanSpace.div w x| :=
          add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ p * M₀ * ((|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) + N * M₁ * (|u x| + ε) ^ p :=
          add_le_add hA hB
      _ ≤ max (N * M₁) (p * M₀) * ((|u x| + ε) ^ p
          + (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by
          nlinarith [mul_le_mul_of_nonneg_right hmax₁ hnn₁, mul_le_mul_of_nonneg_right hmax₂ hnn₂]
  rw [integral_const_mul, integral_add (B.integrableOn_of_continuous hcont₁)
    (B.integrableOn_of_continuous hcont₂)] at h2
  rw [hdiv] at h2
  exact h1.trans h2

/-- **Nečas's inequality for `C¹` functions** ([Nečas, *Direct Methods*, Ch. 2 §4]; Evans §5.5
Theorem 1, step 1, in the transversal-field form): for a transversal field `w` (`C¹`, compactly
supported, `⟪w, ν⟫ ≥ 1` `σ`-a.e.) with `‖w‖ ≤ M₀` and `‖Dw‖ ≤ M₁` everywhere, `p ≥ 1`, and every
`u ∈ C¹(ℝ^N)`,
`∫ |u|^p dσ ≤ max (N M₁) (p M₀) (∫_Ω |u|^p + ∫_Ω |u|^{p−1} ‖∇u‖)`.
The fixed-`ε` inequality `integral_rpowReg_le` for the regularization
`φ_ε(t) = (t² + ε²)^{p/2} − ε^p` of `|t|^p`, and `ε = 1/(n+1) → 0` by dominated convergence on
both sides (`u` and `∇u` are bounded on the compact `closure Ω`, `σ` and `Ω` have finite
measure). No compact support of `u` is needed: only its values on `closure Ω` enter. -/
theorem integral_abs_rpow_le_of_contDiff {w : 𝔼 → 𝔼} (hw : ContDiff ℝ 1 w)
    (hwc : HasCompactSupport w) (hwν : ∀ᵐ x ∂B.σ, 1 ≤ ⟪w x, B.ν x⟫_ℝ) {M₀ M₁ : ℝ}
    (hM₀ : ∀ x, ‖w x‖ ≤ M₀) (hM₁ : ∀ x, ‖fderiv ℝ w x‖ ≤ M₁) {p : ℝ} (hp : 1 ≤ p)
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫ x, |u x| ^ p ∂B.σ
      ≤ max (N * M₁) (p * M₀) * ((∫ x in (Ω : Set 𝔼), |u x| ^ p)
        + ∫ x in (Ω : Set 𝔼), |u x| ^ (p - 1) * ‖fderiv ℝ u x‖) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have := B.isFiniteMeasure_volume_restrict
  -- the bounds on `u` and `∇u` on the compact `closure Ω`
  obtain ⟨K, hK⟩ := B.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hu.continuous.continuousOn
  obtain ⟨K', hK'⟩ := B.isBounded.isCompact_closure.exists_bound_of_continuousOn
    (hu.continuous_fderiv one_ne_zero).continuousOn
  have hK₁ : ∀ x ∈ closure (Ω : Set 𝔼), |u x| ≤ max K 0 := fun x hx ↦
    (Real.norm_eq_abs (u x) ▸ hK x hx).trans (le_max_left _ _)
  have hK₂ : ∀ x ∈ closure (Ω : Set 𝔼), ‖fderiv ℝ u x‖ ≤ max K' 0 := fun x hx ↦
    (hK' x hx).trans (le_max_left _ _)
  have hK₁0 : 0 ≤ max K 0 := le_max_right _ _
  have hK₂0 : 0 ≤ max K' 0 := le_max_right _ _
  -- the sequence `ε n = 1/(n+1)`
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hεle : ∀ n, ε n ≤ 1 := fun n ↦
    div_le_one_of_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by positivity)
  have hε0 : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall hεpos⟩
  have hε0' : Tendsto ε atTop (𝓝 0) := hε0.mono_right nhdsWithin_le_nhds
  -- the boundary integrals converge
  have hL : Tendsto (fun n ↦ ∫ x, Real.rpowReg p (ε n) (u x) ∂B.σ) atTop
      (𝓝 (∫ x, |u x| ^ p ∂B.σ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (max K 0 + 1) ^ p)
      (fun n ↦ ((Real.contDiff_rpowReg (n := 1) (hεpos n)).continuous.comp
        hu.continuous).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ?_)
      (.of_forall fun x ↦ (Real.tendsto_rpowReg hp0 (u x)).comp hε0)
    filter_upwards [B.ae_mem_frontier] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpowReg_nonneg (hεpos n) hp0.le _)]
    exact (Real.rpowReg_le (hεpos n) hp0.le _).trans (Real.rpow_le_rpow (by positivity)
      (add_le_add (hK₁ x (frontier_subset_closure hx)) (hεle n)) hp0.le)
  -- the interior integrals converge
  have hR₁ : Tendsto (fun n ↦ ∫ x in (Ω : Set 𝔼), (|u x| + ε n) ^ p) atTop
      (𝓝 (∫ x in (Ω : Set 𝔼), |u x| ^ p)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (max K 0 + 1) ^ p)
      (fun n ↦ ((hu.continuous.abs.add continuous_const).rpow_const
        fun x ↦ Or.inr hp0.le).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ?_) (.of_forall fun x ↦ ?_)
    · filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow (by positivity)
        (add_le_add (hK₁ x (subset_closure hx)) (hεle n)) hp0.le
    · have h := (tendsto_const_nhds (x := |u x|)).add hε0'
      rw [add_zero] at h
      exact ((Real.continuous_rpow_const hp0.le).tendsto (|u x|)).comp h
  have hR₂ : Tendsto (fun n ↦ ∫ x in (Ω : Set 𝔼), (|u x| + ε n) ^ (p - 1) * ‖fderiv ℝ u x‖)
      atTop (𝓝 (∫ x in (Ω : Set 𝔼), |u x| ^ (p - 1) * ‖fderiv ℝ u x‖)) := by
    have hp1 : 0 ≤ p - 1 := by linarith
    refine tendsto_integral_of_dominated_convergence
      (fun _ ↦ (max K 0 + 1) ^ (p - 1) * max K' 0)
      (fun n ↦ (((hu.continuous.abs.add continuous_const).rpow_const fun x ↦ Or.inr hp1).mul
        (hu.continuous_fderiv one_ne_zero).norm).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ?_) (.of_forall fun x ↦ ?_)
    · filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul (Real.rpow_le_rpow (by positivity)
        (add_le_add (hK₁ x (subset_closure hx)) (hεle n)) hp1) (hK₂ x (subset_closure hx))
        (norm_nonneg _) (by positivity)
    · have h := (tendsto_const_nhds (x := |u x|)).add hε0'
      rw [add_zero] at h
      exact (((Real.continuous_rpow_const hp1).tendsto (|u x|)).comp h).mul
        (tendsto_const_nhds (x := ‖fderiv ℝ u x‖))
  exact le_of_tendsto_of_tendsto' hL ((hR₁.add hR₂).const_mul _) fun n ↦
    B.integral_rpowReg_le hw hwc hwν hM₀ hM₁ hp (hεpos n) hu

/-! ### The trace inequality in the Sobolev norm -/

open SobolevMultiIndex

/-- `1 ≤ p.toReal` for `1 ≤ p < ∞`. -/
theorem _root_.ENNReal.one_le_toReal_of_ne_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    1 ≤ p.toReal := by
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono hp Fact.out

/-- `∫_Ω |u|^p = ‖fnL U‖^p` for a representative `u` of `U ∈ W^{1,p}(Ω)`. -/
theorem _root_.SobolevEuclidean.integral_abs_rpow_eq_norm_fnL {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (U : SobolevEuclidean N 1 p Ω) {u : 𝔼 → ℝ}
    (hU : fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u) :
    ∫ x in (Ω : Set 𝔼), |u x| ^ p.toReal
      = ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume U‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  rw [Lp.norm_rpow_eq_integral hp0 hp, fnL_apply]
  refine integral_congr_ae (hU.mono fun x hx ↦ ?_)
  simp only [hx, Real.norm_eq_abs]

/-- `∫_Ω ‖Du‖^p ≤ N^p ‖U‖^p` for a `C¹` representative `u` of `U ∈ W^{1,p}(Ω)`. -/
theorem _root_.SobolevEuclidean.integral_norm_fderiv_rpow_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (U : SobolevEuclidean N 1 p Ω) {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u)
    (hU : fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u) :
    ∫ x in (Ω : Set 𝔼), ‖fderiv ℝ u x‖ ^ p.toReal ≤ (N : ℝ) ^ p.toReal * ‖U‖ ^ p.toReal := by
  have h := integral_norm_gradFn_rpow_le hp U
  rw [Fintype.card_fin] at h
  calc ∫ x in (Ω : Set 𝔼), ‖fderiv ℝ u x‖ ^ p.toReal
      = ∫ x in (Ω : Set 𝔼), ‖gradFn U x‖ ^ p.toReal :=
        integral_congr_ae ((SobolevEuclidean.norm_fderiv_ae_eq_norm_gradFn U hu hU).mono
          fun x hx ↦ by simp only at hx ⊢; rw [hx])
    _ ≤ (N : ℝ) ^ p.toReal * gradNorm U ^ p.toReal := h
    _ ≤ (N : ℝ) ^ p.toReal * ‖U‖ ^ p.toReal :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (gradNorm_nonneg U) (gradNorm_le_norm U)
          ENNReal.toReal_nonneg) (by positivity)

/-- **The trace inequality on the smooth functions, in the Sobolev norm** (Atkinson–Han Theorem
7.3.10 (b) on the smooth subspace): for a transversal field and `1 ≤ p < ∞` there is `C` such
that `‖u‖_{L^p(σ)} ≤ C ‖U‖_{W^{1,p}(Ω)}` for every `U ∈ W^{1,p}(Ω)` with a `C¹` representative
`u`. Nečas's inequality `integral_abs_rpow_le_of_contDiff` at `p.toReal`, with
`∫_Ω |u|^p = ‖U‖_p^p ≤ ‖U‖^p`, the crude Young inequality
`∫_Ω |u|^{p−1} ‖∇u‖ ≤ ∫_Ω |u|^p + ∫_Ω ‖∇u‖^p` and `∫_Ω ‖∇u‖^p ≤ N^p ‖U‖^p`, then `p`-th roots. -/
theorem eLpNorm_le_of_contDiff (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : SobolevEuclidean N 1 p Ω) (u : 𝔼 → ℝ), ContDiff ℝ 1 u →
      fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u → eLpNorm u p B.σ ≤ ENNReal.ofReal (C * ‖U‖) := by
  obtain ⟨w, hw, hwc, hwν⟩ := hw
  obtain ⟨M₀, hM₀⟩ := hw.continuous.bounded_above_of_compact_support hwc
  obtain ⟨M₁, hM₁⟩ :=
    (hw.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hwc.fderiv (𝕜 := ℝ))
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_ne_top hp
  have hP0 : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hC₀ : 0 ≤ max (N * M₁) (p.toReal * M₀) := le_max_of_le_right (by positivity)
  refine ⟨(max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal)) ^ (1 / p.toReal),
    by positivity, fun U u hu hU ↦ ?_⟩
  have hnec := B.integral_abs_rpow_le_of_contDiff hw hwc hwν hM₀ hM₁ hP1 hu
  have h1 : ∫ x in (Ω : Set 𝔼), |u x| ^ p.toReal ≤ ‖U‖ ^ p.toReal := by
    rw [SobolevEuclidean.integral_abs_rpow_eq_norm_fnL hp U hU]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_fnL_apply_le U) hP0.le
  have h3 := SobolevEuclidean.integral_norm_fderiv_rpow_le hp U hu hU
  have hcont₁ : Continuous fun x ↦ |u x| ^ p.toReal :=
    hu.continuous.abs.rpow_const fun x ↦ Or.inr hP0.le
  have hcont₃ : Continuous fun x ↦ ‖fderiv ℝ u x‖ ^ p.toReal :=
    (hu.continuous_fderiv one_ne_zero).norm.rpow_const fun x ↦ Or.inr hP0.le
  have h2 : ∫ x in (Ω : Set 𝔼), |u x| ^ (p.toReal - 1) * ‖fderiv ℝ u x‖
      ≤ (∫ x in (Ω : Set 𝔼), |u x| ^ p.toReal)
        + ∫ x in (Ω : Set 𝔼), ‖fderiv ℝ u x‖ ^ p.toReal := by
    rw [← integral_add (B.integrableOn_of_continuous hcont₁) (B.integrableOn_of_continuous hcont₃)]
    refine integral_mono (B.integrableOn_of_continuous
      ((hu.continuous.abs.rpow_const fun x ↦ Or.inr (by linarith)).mul
        (hu.continuous_fderiv one_ne_zero).norm))
      (B.integrableOn_of_continuous (hcont₁.add hcont₃)) fun x ↦ ?_
    exact Real.rpow_sub_one_mul_le_add (abs_nonneg _) (norm_nonneg _) hP1
  have htot : ∫ x, |u x| ^ p.toReal ∂B.σ
      ≤ max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal) * ‖U‖ ^ p.toReal := by
    have hN : 0 ≤ (N : ℝ) ^ p.toReal := by positivity
    have hU0 : 0 ≤ ‖U‖ ^ p.toReal := by positivity
    calc ∫ x, |u x| ^ p.toReal ∂B.σ
        ≤ max (N * M₁) (p.toReal * M₀) * ((∫ x in (Ω : Set 𝔼), |u x| ^ p.toReal)
          + ∫ x in (Ω : Set 𝔼), |u x| ^ (p.toReal - 1) * ‖fderiv ℝ u x‖) := hnec
      _ ≤ max (N * M₁) (p.toReal * M₀)
          * (‖U‖ ^ p.toReal + (‖U‖ ^ p.toReal + (N : ℝ) ^ p.toReal * ‖U‖ ^ p.toReal)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 (h2.trans (add_le_add h1 h3))) hC₀
      _ = max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal) * ‖U‖ ^ p.toReal := by ring
  rw [(B.memLp_of_continuous hu.continuous p).eLpNorm_eq_integral_rpow_norm hp0 hp]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [Real.norm_eq_abs]
  calc (∫ x, |u x| ^ p.toReal ∂B.σ) ^ p.toReal⁻¹
      ≤ (max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal) * ‖U‖ ^ p.toReal)
          ^ p.toReal⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x ↦ by positivity) htot (by positivity)
    _ = (max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal)) ^ (1 / p.toReal) * ‖U‖ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (norm_nonneg _),
          mul_inv_cancel₀ hP0.ne', Real.rpow_one, one_div]

/-! ### The trace operator -/

/-- Two representatives of `u ∈ W^{1,p}(Ω)` continuous up to the boundary agree `σ`-a.e.:
they agree on `closure Ω ⊇ ∂Ω` (`SobolevEuclidean.eqOn_closure_of_ae_eq_of_continuousOn`) and
`σ` is carried by `∂Ω`. -/
theorem ae_eq_of_ae_eq_of_continuousOn {p : ℝ≥0∞} (u : SobolevEuclidean N 1 p Ω)
    {v₁ v₂ : 𝔼 → ℝ} (h₁ : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v₁)
    (h₂ : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v₂) (hc₁ : ContinuousOn v₁ (closure (Ω : Set 𝔼)))
    (hc₂ : ContinuousOn v₂ (closure (Ω : Set 𝔼))) : v₁ =ᵐ[B.σ] v₂ :=
  B.ae_mem_frontier.mono fun _ hx ↦
    SobolevEuclidean.eqOn_closure_of_ae_eq_of_continuousOn u h₁ h₂ hc₁ hc₂
      (frontier_subset_closure hx)

section SmoothTrace

variable (p : ℝ≥0∞)

/-- **Restriction to `∂Ω` on the smooth-representable subspace**, as a linear map
`smoothRestrictions →ₗ L^p(σ)`: `u ↦ (smoothRep u)|_{∂Ω}`. Well defined and linear because two
continuous representatives agree `σ`-a.e. (`ae_eq_of_ae_eq_of_continuousOn`). -/
def traceSmooth : SobolevEuclidean.smoothRestrictions N p Ω →ₗ[ℝ] Lp ℝ p B.σ where
  toFun u := (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr
      (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep (u + v)) p)
      ((B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p).add
        (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep v) p))
      (B.ae_eq_of_ae_eq_of_continuousOn (u + v : SobolevEuclidean N 1 p Ω)
      (SobolevEuclidean.fn_ae_eq_smoothRep (u + v)) ?_
      (SobolevEuclidean.continuous_smoothRep _).continuousOn
      ((SobolevEuclidean.continuous_smoothRep u).add
        (SobolevEuclidean.continuous_smoothRep v)).continuousOn)
    exact (fn_add _ _).trans ((SobolevEuclidean.fn_ae_eq_smoothRep u).add
      (SobolevEuclidean.fn_ae_eq_smoothRep v))
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr
      (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep (c • u)) p)
      ((B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p).const_smul c)
      (B.ae_eq_of_ae_eq_of_continuousOn (c • u : SobolevEuclidean N 1 p Ω)
      (SobolevEuclidean.fn_ae_eq_smoothRep (c • u)) ?_
      (SobolevEuclidean.continuous_smoothRep _).continuousOn
      ((SobolevEuclidean.continuous_smoothRep u).const_smul c).continuousOn)
    exact (fn_smul _ _).trans ((SobolevEuclidean.fn_ae_eq_smoothRep u).const_smul c)

/-- `traceSmooth u` is the class of the smooth representative of `u`. -/
theorem coeFn_traceSmooth (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    (B.traceSmooth p u : 𝔼 → ℝ) =ᵐ[B.σ] SobolevEuclidean.smoothRep u :=
  MemLp.coeFn_toLp (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p)

end SmoothTrace

section TraceL

/-- **The constant of the trace inequality** `‖u|_{∂Ω}‖_{L^p(σ)} ≤ C ‖U‖_{W^{1,p}(Ω)}` of
`eLpNorm_le_of_contDiff`. -/
def traceConst (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) : ℝ :=
  Classical.choose (B.eLpNorm_le_of_contDiff hw p hp)

/-- The trace constant is nonnegative. -/
theorem traceConst_nonneg (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    0 ≤ B.traceConst hw p hp :=
  (Classical.choose_spec (B.eLpNorm_le_of_contDiff hw p hp)).1

/-- The trace inequality with the constant `traceConst`. -/
theorem eLpNorm_le_traceConst_mul (hw : B.HasTransversalField) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (U : SobolevEuclidean N 1 p Ω) {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u)
    (hU : fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u) :
    eLpNorm u p B.σ ≤ ENNReal.ofReal (B.traceConst hw p hp * ‖U‖) :=
  (Classical.choose_spec (B.eLpNorm_le_of_contDiff hw p hp)).2 U u hu hU

/-- **Restriction to `∂Ω` on the smooth-representable subspace, as a bounded operator**
`smoothRestrictions →L L^p(σ)`, with norm at most `traceConst`. -/
def traceSmoothL (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SobolevEuclidean.smoothRestrictions N p Ω →L[ℝ] Lp ℝ p B.σ :=
  (B.traceSmooth p).mkContinuous (B.traceConst hw p hp) fun u ↦ by
    change ‖(B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p).toLp _‖ ≤ _
    rw [Lp.norm_toLp]
    have h := B.eLpNorm_le_traceConst_mul hw hp u (SobolevEuclidean.contDiff_smoothRep u |>.of_le
      (by simp)) (SobolevEuclidean.fn_ae_eq_smoothRep u)
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (B.traceConst_nonneg hw p hp) (norm_nonneg _))]
    rfl

/-- `traceSmoothL u` is the class of the smooth representative of `u`. -/
theorem coeFn_traceSmoothL (hw : B.HasTransversalField) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    (B.traceSmoothL hw p hp u : 𝔼 → ℝ) =ᵐ[B.σ] SobolevEuclidean.smoothRep u :=
  B.coeFn_traceSmooth p u

/-- The norm of the trace on the smooth subspace is at most `traceConst`. -/
theorem norm_traceSmoothL_le (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) : ‖B.traceSmoothL hw p hp‖ ≤ B.traceConst hw p hp :=
  LinearMap.mkContinuous_norm_le _ (B.traceConst_nonneg hw p hp) _

/-- **The trace operator of a domain with a transversal field**, `T : W^{1,p}(Ω) →L L^p(σ)`,
`1 ≤ p < ∞`: the continuous extension (`ContinuousLinearMap.extend`) of the restriction to `∂Ω`
from the subspace `smoothRestrictions` of smooth-representable elements. It is the trace wherever
that subspace is dense — `SobolevEuclidean.HasSmoothDensity N p Ω`, the hypothesis of every
lemma below — and, as for Mathlib's `extend`, the density hypothesis enters the lemmas rather than
the definition (`traceL_ae_eq_of_contDiff`, `traceL_ae_eq_of_continuousOn`, `traceL_unique`,
`norm_traceL_le`). -/
def traceL (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SobolevEuclidean N 1 p Ω →L[ℝ] Lp ℝ p B.σ :=
  (B.traceSmoothL hw p hp).extend (SobolevEuclidean.smoothRestrictions N p Ω).subtypeL

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On the smooth-representable subspace the trace is the restriction of the smooth
representative. -/
theorem traceL_apply_of_mem (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) {u : SobolevEuclidean N 1 p Ω}
    (hu : u ∈ SobolevEuclidean.smoothRestrictions N p Ω) :
    B.traceL hw p hp u = B.traceSmoothL hw p hp ⟨u, hu⟩ :=
  ContinuousLinearMap.extend_eq (B.traceSmoothL hw p hp) hd.dense_smoothRestrictions.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing ⟨u, hu⟩

/-- **The trace of a smooth-representable element is its restriction**: for
`u ∈ W^{1,p}(Ω)` and `v ∈ C_c^∞(ℝ^N)` with `fn u = v` a.e. on `Ω`, `T u = v` `σ`-a.e. -/
theorem traceL_ae_eq_of_contDiff (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) (u : SobolevEuclidean N 1 p Ω)
    {v : 𝔼 → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (huv : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v) :
    (B.traceL hw p hp u : 𝔼 → ℝ) =ᵐ[B.σ] v := by
  have hu : u ∈ SobolevEuclidean.smoothRestrictions N p Ω := ⟨v, hv, hvc, huv⟩
  rw [B.traceL_apply_of_mem hw hp hd hu]
  refine (B.coeFn_traceSmoothL hw hp ⟨u, hu⟩).trans ?_
  exact B.ae_eq_of_ae_eq_of_continuousOn u (SobolevEuclidean.fn_ae_eq_smoothRep ⟨u, hu⟩) huv
    (SobolevEuclidean.continuous_smoothRep _).continuousOn hv.continuous.continuousOn

/-- **The trace is bounded by `traceConst`**: `‖T‖ ≤ C` (Atkinson–Han Theorem 7.3.10 (b)). -/
theorem norm_traceL_le (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) :
    ‖B.traceL hw p hp‖ ≤ B.traceConst hw p hp := by
  refine (ContinuousLinearMap.opNorm_extend_le (N := 1) _ hd.dense_smoothRestrictions.denseRange_val
    fun _ ↦ ?_).trans ?_
  · simp
  · rw [NNReal.coe_one, one_mul]
    exact B.norm_traceSmoothL_le hw p hp

/-- **The trace inequality** `‖T u‖_{L^p(σ)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for every `u ∈ W^{1,p}(Ω)`
(Atkinson–Han Theorem 7.3.10 (b)). -/
theorem norm_traceL_apply_le (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) (u : SobolevEuclidean N 1 p Ω) :
    ‖B.traceL hw p hp u‖ ≤ B.traceConst hw p hp * ‖u‖ :=
  ((B.traceL hw p hp).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (B.norm_traceL_le hw hp hd) (norm_nonneg _))

/-- **Uniqueness of an operator restricting smooth representatives**: two bounded operators
`W^{1,p}(Ω) →L L^p(σ)` which both send every smooth-representable element to the restriction of
its representative agree, when the smooth-representable elements are dense. -/
theorem ext_of_forall_ae_eq (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    {T T' : SobolevEuclidean N 1 p Ω →L[ℝ] Lp ℝ p B.σ}
    (hT : ∀ (u : SobolevEuclidean N 1 p Ω) (v : 𝔼 → ℝ), ContDiff ℝ ∞ v → HasCompactSupport v →
      fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v → (T u : 𝔼 → ℝ) =ᵐ[B.σ] v)
    (hT' : ∀ (u : SobolevEuclidean N 1 p Ω) (v : 𝔼 → ℝ), ContDiff ℝ ∞ v → HasCompactSupport v →
      fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v → (T' u : 𝔼 → ℝ) =ᵐ[B.σ] v) :
    T = T' := by
  have h : ⇑T = ⇑T' := Continuous.ext_on hd.dense_smoothRestrictions T.continuous T'.continuous
    fun u ⟨v, hv, hvc, huv⟩ ↦ Lp.ext ((hT u v hv hvc huv).trans (hT' u v hv hvc huv).symm)
  exact ContinuousLinearMap.ext fun u ↦ congrFun h u

/-- **Uniqueness of the trace**: a bounded operator `T' : W^{1,p}(Ω) →L L^p(σ)` restricting
every smooth compactly supported representative is `traceL`. -/
theorem traceL_unique (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    {T' : SobolevEuclidean N 1 p Ω →L[ℝ] Lp ℝ p B.σ}
    (hT' : ∀ (u : SobolevEuclidean N 1 p Ω) (v : 𝔼 → ℝ), ContDiff ℝ ∞ v → HasCompactSupport v →
      fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v → (T' u : 𝔼 → ℝ) =ᵐ[B.σ] v) :
    T' = B.traceL hw p hp :=
  B.ext_of_forall_ae_eq hd hT' fun u _ hv hvc huv ↦ B.traceL_ae_eq_of_contDiff hw hp hd u hv hvc huv

/-- **Two trace families over the same boundary data agree** at every exponent with smooth
density: their `traceL_ae_eq` fields both restrict smooth representatives. In particular the
two routes to the trace of a convex polygon agree. -/
theorem TraceFamily.traceL_eq_of_hasSmoothDensity (𝒯 𝒯' : B.TraceFamily) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) : 𝒯.traceL p hp = 𝒯'.traceL p hp :=
  B.ext_of_forall_ae_eq hd
    (fun u v hv _ huv ↦ 𝒯.traceL_ae_eq p hp u v huv hv.continuous.continuousOn)
    (fun u v hv _ huv ↦ 𝒯'.traceL_ae_eq p hp u v huv hv.continuous.continuousOn)

/-- **The trace of a function continuous up to the boundary is its restriction** (Evans §5.5
Theorem 1 (ii), Atkinson–Han Theorem 7.3.10 (a)): under `HasUniformSmoothDensity`, for
`u ∈ W^{1,p}(Ω)` with a representative `ũ` continuous on `closure Ω`, `T u = ũ` `σ`-a.e. The
approximants `vₙ` of the uniform density predicate satisfy `T wₙ = vₙ` on `∂Ω`
(`traceL_ae_eq_of_contDiff`), `T wₙ → T u` in `L^p(σ)` by continuity, and `vₙ → ũ` uniformly on
`closure Ω ⊇ ∂Ω`, hence in `L^p(σ)` (`σ` finite); limits in `L^p(σ)` are unique. -/
theorem traceL_ae_eq_of_continuousOn (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    (hdu : SobolevEuclidean.HasUniformSmoothDensity N p Ω) (u : SobolevEuclidean N 1 p Ω)
    {ũ : 𝔼 → ℝ} (hu : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) : (B.traceL hw p hp u : 𝔼 → ℝ) =ᵐ[B.σ] ũ := by
  obtain ⟨v, hv, hvc, ⟨w, hw', hwu⟩, hunif⟩ := hdu u ũ hu hc
  have hũ : MemLp ũ p B.σ := B.memLp_of_continuousOn hc p
  have h1 : Tendsto (fun n ↦ B.traceL hw p hp (w n)) atTop (𝓝 (B.traceL hw p hp u)) :=
    ((B.traceL hw p hp).continuous.tendsto u).comp hwu
  have h2 : Tendsto (fun n ↦ B.traceL hw p hp (w n)) atTop (𝓝 (hũ.toLp ũ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hMtop : B.σ univ ^ p.toReal⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
    set M := (B.σ univ ^ p.toReal⁻¹).toReal with hM
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
    have hδ : 0 < ε / (M + 1) := by positivity
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif _ hδ)
    refine ⟨n₀, fun n hn ↦ ?_⟩
    rw [Lp.dist_def]
    have hae : (⇑(B.traceL hw p hp (w n)) - ⇑(hũ.toLp ũ)) =ᵐ[B.σ] v n - ũ := by
      filter_upwards [B.traceL_ae_eq_of_contDiff hw hp hd (w n) (hv n) (hvc n) (hw' n),
        hũ.coeFn_toLp] with x hx hx'
      rw [Pi.sub_apply, Pi.sub_apply, hx, hx']
    calc (eLpNorm (⇑(B.traceL hw p hp (w n)) - ⇑(hũ.toLp ũ)) p B.σ).toReal
        = (eLpNorm (v n - ũ) p B.σ).toReal := by rw [eLpNorm_congr_ae hae]
      _ ≤ (B.σ univ ^ p.toReal⁻¹ * ENNReal.ofReal (ε / (M + 1))).toReal := by
          refine ENNReal.toReal_mono (ENNReal.mul_ne_top hMtop ENNReal.ofReal_ne_top) ?_
          refine eLpNorm_le_of_ae_bound
            ((hv n).continuous.aestronglyMeasurable.sub hũ.aestronglyMeasurable) ?_
          filter_upwards [B.ae_mem_frontier] with x hx
          rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm, ← Real.dist_eq]
          exact (hn₀ n hn x (frontier_subset_closure hx)).le
      _ = M * (ε / (M + 1)) := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le]
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  rw [tendsto_nhds_unique h1 h2]
  exact hũ.coeFn_toLp

end TraceL

/-! ### Green's formula by density -/

section Green

/-- **The pairing `(f, g) ↦ ∫ f g` of `L^p × L^q` at conjugate exponents is jointly continuous**
(Hölder's inequality, through Mathlib's `ContinuousLinearMap.lpPairing` in the form
`MeasureTheory.Lp.toDualCLM`). -/
theorem _root_.MeasureTheory.continuous_integral_mul_prod {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] :
    Continuous fun x : Lp ℝ p μ × Lp ℝ q μ ↦ ∫ y, x.1 y * x.2 y ∂μ :=
  (Lp.toDualCLM ℝ q p μ).continuous₂.congr fun x ↦ Lp.toDualCLM_apply x.1 x.2

/-- **Multiplication by the coordinate `νᵢ` of the normal**, as a bounded operator on `L^p(σ)`
of norm at most one (`|νᵢ| ≤ 1` `σ`-a.e.). -/
def mulNormalL (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin N) : Lp ℝ p B.σ →L[ℝ] Lp ℝ p B.σ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (B.memLp_ν_apply_mul (Lp.memLp f) i).toLp _
      map_add' := fun f g ↦ by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr (B.memLp_ν_apply_mul (Lp.memLp (f + g)) i)
          ((B.memLp_ν_apply_mul (Lp.memLp f) i).add (B.memLp_ν_apply_mul (Lp.memLp g) i)) ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [hx, Pi.add_apply, mul_add]
      map_smul' := fun c f ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr (B.memLp_ν_apply_mul (Lp.memLp (c • f)) i)
          ((B.memLp_ν_apply_mul (Lp.memLp f) i).const_smul c) ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul]
        ring }
    1 fun f ↦ by
      change ‖(B.memLp_ν_apply_mul (Lp.memLp f) i).toLp _‖ ≤ _
      rw [Lp.norm_toLp, one_mul, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_ae
        ((B.aestronglyMeasurable_ν_apply i).mul (Lp.aestronglyMeasurable f)) ?_)
      filter_upwards [B.ae_abs_ν_apply_le i] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hx

/-- `mulNormalL f` is the class of `νᵢ f`. -/
theorem coeFn_mulNormalL (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin N) (f : Lp ℝ p B.σ) :
    (B.mulNormalL p i f : 𝔼 → ℝ) =ᵐ[B.σ] fun x ↦ B.ν x i * f x :=
  MemLp.coeFn_toLp (B.memLp_ν_apply_mul (Lp.memLp f) i)

/-- **Green's formula for smooth-representable elements**: the classical Green formula
`BoundaryData.integral_fderiv_mul_add_eq` read through the smooth representatives, at any two
exponents. -/
theorem green_of_mem_smoothRestrictions (hw : B.HasTransversalField) {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) (hd' : SobolevEuclidean.HasSmoothDensity N q Ω)
    {u : SobolevEuclidean N 1 p Ω} (hu : u ∈ SobolevEuclidean.smoothRestrictions N p Ω)
    {v : SobolevEuclidean N 1 q Ω} (hv : v ∈ SobolevEuclidean.smoothRestrictions N q Ω)
    (i : Fin N) :
    (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * fn v x)
      + ∫ x in (Ω : Set 𝔼), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * (B.traceL hw q hq v : 𝔼 → ℝ) x * B.ν x i ∂B.σ := by
  obtain ⟨ũ, hũ, hũc, huũ⟩ := hu
  obtain ⟨v', hv', hv'c, hvv'⟩ := hv
  have hũ1 : ContDiff ℝ 1 ũ := hũ.of_le (by simp)
  have hv'1 : ContDiff ℝ 1 v' := hv'.of_le (by simp)
  have h := B.integral_fderiv_mul_add_eq hũ1.continuous.continuousOn
    (hũ1.contDiffOn.contDiffOnClosure Ω.isOpen) hv'1.continuous.continuousOn
    (hv'1.contDiffOn.contDiffOnClosure Ω.isOpen) i
  have e1 : ∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * fn v x
      = ∫ x in (Ω : Set 𝔼), fderiv ℝ ũ x (EuclideanSpace.single i 1) * v' x := by
    refine integral_congr_ae ?_
    filter_upwards [SobolevEuclidean.weakDeriv_single_ae_eq_fderiv u hũ1 huũ i, hvv'] with x h1 h2
    rw [h1, h2]
  have e2 : ∫ x in (Ω : Set 𝔼), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x in (Ω : Set 𝔼), ũ x * fderiv ℝ v' x (EuclideanSpace.single i 1) := by
    refine integral_congr_ae ?_
    filter_upwards [SobolevEuclidean.weakDeriv_single_ae_eq_fderiv v hv'1 hvv' i, huũ] with x h1 h2
    rw [h1, h2]
  have e3 : ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * (B.traceL hw q hq v : 𝔼 → ℝ) x * B.ν x i ∂B.σ
      = ∫ x, ũ x * v' x * B.ν x i ∂B.σ := by
    refine integral_congr_ae ?_
    filter_upwards [B.traceL_ae_eq_of_contDiff hw hp hd u hũ hũc huũ,
      B.traceL_ae_eq_of_contDiff hw hq hd' v hv' hv'c hvv'] with x h1 h2
    rw [h1, h2]
  rw [e1, e2, e3]
  exact h

/-- **Green's formula by density** (Atkinson–Han Proposition 7.6.1, (7.6.3); Grisvard Theorem
1.5.3.1): for conjugate exponents `1 < p, q < ∞` with smooth density, `u ∈ W^{1,p}(Ω)`,
`v ∈ W^{1,q}(Ω)` and `i`,
`∫_Ω ∂ᵢu v + ∫_Ω u ∂ᵢv = ∫ (Tu)(Tv) νᵢ dσ`.
Both sides are continuous in `(u, v)` (the `L^p × L^q` pairing `continuous_integral_mul_prod`
composed with `weakDerivL`, `fnL`, `traceL` and `mulNormalL`), and they agree on the dense set
of smooth-representable pairs (`green_of_mem_smoothRestrictions`). -/
theorem green_of_hasSmoothDensity (hw : B.HasTransversalField) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] [p.HolderConjugate q] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) (hd' : SobolevEuclidean.HasSmoothDensity N q Ω)
    (u : SobolevEuclidean N 1 p Ω) (v : SobolevEuclidean N 1 q Ω) (i : Fin N) :
    (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * fn v x)
      + ∫ x in (Ω : Set 𝔼), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * (B.traceL hw q hq v : 𝔼 → ℝ) x * B.ν x i ∂B.σ := by
  refine (hd.dense_smoothRestrictions.prod hd'.dense_smoothRestrictions).induction
    (P := fun x : SobolevEuclidean N 1 p Ω × SobolevEuclidean N 1 q Ω ↦
      (∫ y in (Ω : Set 𝔼), (weakDeriv x.1 (MultiIndexLE.single i) : 𝔼 → ℝ) y * fn x.2 y)
        + ∫ y in (Ω : Set 𝔼), fn x.1 y * (weakDeriv x.2 (MultiIndexLE.single i) : 𝔼 → ℝ) y
        = ∫ y, (B.traceL hw p hp x.1 : 𝔼 → ℝ) y * (B.traceL hw q hq x.2 : 𝔼 → ℝ) y * B.ν y i
          ∂B.σ)
    (fun x hx ↦ B.green_of_mem_smoothRestrictions hw hp hq hd hd' hx.1 hx.2 i) ?_ (u, v)
  refine isClosed_eq ?_ ?_
  · have c1 : Continuous fun x : SobolevEuclidean N 1 p Ω × SobolevEuclidean N 1 q Ω ↦
        ∫ y in (Ω : Set 𝔼), (weakDeriv x.1 (MultiIndexLE.single i) : 𝔼 → ℝ) y * fn x.2 y :=
      (MeasureTheory.continuous_integral_mul_prod p q).comp
        (((weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
          (MultiIndexLE.single i)).continuous.comp continuous_fst).prodMk
          ((fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 q Ω volume).continuous.comp
            continuous_snd))
    have c2 : Continuous fun x : SobolevEuclidean N 1 p Ω × SobolevEuclidean N 1 q Ω ↦
        ∫ y in (Ω : Set 𝔼), fn x.1 y * (weakDeriv x.2 (MultiIndexLE.single i) : 𝔼 → ℝ) y :=
      (MeasureTheory.continuous_integral_mul_prod p q).comp
        (((fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).continuous.comp
          continuous_fst).prodMk
          ((weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 q Ω volume
            (MultiIndexLE.single i)).continuous.comp continuous_snd))
    exact c1.add c2
  · have c3 : Continuous fun x : SobolevEuclidean N 1 p Ω × SobolevEuclidean N 1 q Ω ↦
        ∫ y, (B.traceL hw p hp x.1 : 𝔼 → ℝ) y * (B.mulNormalL q i (B.traceL hw q hq x.2) : 𝔼 → ℝ) y
          ∂B.σ :=
      (MeasureTheory.continuous_integral_mul_prod p q).comp
        (((B.traceL hw p hp).continuous.comp continuous_fst).prodMk
          ((B.mulNormalL q i).continuous.comp ((B.traceL hw q hq).continuous.comp continuous_snd)))
    refine c3.congr fun x ↦ integral_congr_ae ?_
    filter_upwards [B.coeFn_mulNormalL q i (B.traceL hw q hq x.2)] with y hy
    rw [hy]
    ring

/-- **Green's formula against a fixed compactly supported `C¹` test function, at every
`1 ≤ p < ∞`**: for `u ∈ W^{1,p}(Ω)`, `φ ∈ C¹_c(ℝ^N)` and `i`,
`∫_Ω ∂ᵢu φ + ∫_Ω u ∂ᵢφ = ∫ (Tu) φ νᵢ dσ`.
The density argument of `green_of_hasSmoothDensity` with only `u` approximated: the fixed bounded
`φ`, `∂ᵢφ`, `φ νᵢ` lie in `L^{p'}` of the finite measures (`p'` the conjugate exponent, `∞` at
`p = 1`), so every term is continuous in `u`. -/
theorem green_contDiff_of_hasSmoothDensity (hw : B.HasTransversalField) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    (u : SobolevEuclidean N 1 p Ω) {φ : 𝔼 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (i : Fin N) :
    (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x)
      + ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * φ x * B.ν x i ∂B.σ := by
  have : p.HolderConjugate (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent Fact.out
  have : Fact (1 ≤ ENNReal.conjExponent p) := ENNReal.fact_one_le_conjExponent
  have := B.isFiniteMeasure_volume_restrict
  -- the fixed factors as `L^{p'}` elements
  obtain ⟨K, hK⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨K', hK'⟩ :=
    (hφ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
  have hφq : MemLp φ (ENNReal.conjExponent p) (volume.restrict (Ω : Set 𝔼)) :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable K (.of_forall hK)
  have hdφq : MemLp (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) (ENNReal.conjExponent p)
      (volume.restrict (Ω : Set 𝔼)) :=
    MemLp.of_bound ((hφ.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).aestronglyMeasurable K' (.of_forall fun x ↦
        ((fderiv ℝ φ x).le_opNorm _).trans (by simpa using hK' x))
  have hφν : MemLp (fun x ↦ φ x * B.ν x i) (ENNReal.conjExponent p) B.σ := by
    exact MemLp.ae_eq (Eventually.of_forall fun x ↦ mul_comm (B.ν x i) (φ x))
      (B.memLp_ν_apply_mul (B.memLp_of_continuous hφ.continuous (ENNReal.conjExponent p)) i)
  -- the identity on the smooth-representable elements
  have key : ∀ u ∈ SobolevEuclidean.smoothRestrictions N p Ω,
      (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x)
        + ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
        = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * φ x * B.ν x i ∂B.σ := by
    rintro u ⟨ũ, hũ, hũc, huũ⟩
    have hũ1 : ContDiff ℝ 1 ũ := hũ.of_le (by simp)
    have h := B.integral_fderiv_mul_add_eq hũ1.continuous.continuousOn
      (hũ1.contDiffOn.contDiffOnClosure Ω.isOpen) hφ.continuous.continuousOn
      (hφ.contDiffOn.contDiffOnClosure Ω.isOpen) i
    have e1 : ∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x
        = ∫ x in (Ω : Set 𝔼), fderiv ℝ ũ x (EuclideanSpace.single i 1) * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [SobolevEuclidean.weakDeriv_single_ae_eq_fderiv u hũ1 huũ i] with x h1
      rw [h1]
    have e2 : ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
        = ∫ x in (Ω : Set 𝔼), ũ x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      refine integral_congr_ae ?_
      filter_upwards [huũ] with x h1
      rw [h1]
    have e3 : ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * φ x * B.ν x i ∂B.σ
        = ∫ x, ũ x * φ x * B.ν x i ∂B.σ := by
      refine integral_congr_ae ?_
      filter_upwards [B.traceL_ae_eq_of_contDiff hw hp hd u hũ hũc huũ] with x h1
      rw [h1]
    rw [e1, e2, e3]
    exact h
  refine hd.dense_smoothRestrictions.induction (P := fun u : SobolevEuclidean N 1 p Ω ↦
    (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x)
      + ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * φ x * B.ν x i ∂B.σ) key ?_ u
  refine isClosed_eq ?_ ?_
  · have c1 : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
        ∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * (hφq.toLp φ) x :=
      (MeasureTheory.continuous_integral_mul_prod p (ENNReal.conjExponent p)).comp
        ((weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
          (MultiIndexLE.single i)).continuous.prodMk continuous_const)
    have c2 : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
        ∫ x in (Ω : Set 𝔼), fn u x * (hdφq.toLp _) x :=
      (MeasureTheory.continuous_integral_mul_prod p (ENNReal.conjExponent p)).comp
        ((fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).continuous.prodMk
          continuous_const)
    refine (c1.add c2).congr fun u ↦ ?_
    rw [Pi.add_apply]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [hφq.coeFn_toLp] with x hx
      rw [hx]
    · refine integral_congr_ae ?_
      filter_upwards [hdφq.coeFn_toLp] with x hx
      rw [hx]
  · have c3 : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
        ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * (hφν.toLp _) x ∂B.σ :=
      (MeasureTheory.continuous_integral_mul_prod p (ENNReal.conjExponent p)).comp
        ((B.traceL hw p hp).continuous.prodMk continuous_const)
    refine c3.congr fun u ↦ integral_congr_ae ?_
    filter_upwards [hφν.coeFn_toLp] with x hx
    rw [hx, mul_assoc]

end Green

/-! ### The trace family -/

/-- **The trace family of a domain with a transversal field and smooth density at every
exponent**: `traceL p hp := B.traceL hw p hp`, the restriction property from
`traceL_ae_eq_of_continuousOn`, Green's formula from `green_of_hasSmoothDensity` and
`green_contDiff_of_hasSmoothDensity`. The instances `IsContDiffDomain.traceFamily` and
`EuclideanSpace.triangleTraceFamily` are this constructor with the density theorems of
`Boundary/Density.lean`. -/
def traceFamily (hw : B.HasTransversalField)
    (hd : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → SobolevEuclidean.HasSmoothDensity N p Ω)
    (hdu : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → SobolevEuclidean.HasUniformSmoothDensity N p Ω) :
    B.TraceFamily where
  traceL p _ hp := B.traceL hw p hp
  traceL_ae_eq p _ hp u _ hu hc := B.traceL_ae_eq_of_continuousOn hw hp (hd p hp) (hdu p hp) u hu hc
  green p q _ _ _ hp hq u v i :=
    B.green_of_hasSmoothDensity hw p q hp hq (hd p hp) (hd q hq) u v i
  green_contDiff p _ hp u _ hφ hφc i :=
    B.green_contDiff_of_hasSmoothDensity hw p hp (hd p hp) u hφ hφc i

/-- The trace of the trace family is `traceL`. -/
@[simp]
theorem traceFamily_traceL (hw : B.HasTransversalField)
    (hd : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → SobolevEuclidean.HasSmoothDensity N p Ω)
    (hdu : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → SobolevEuclidean.HasUniformSmoothDensity N p Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (B.traceFamily hw hd hdu).traceL p hp = B.traceL hw p hp :=
  rfl

/-! ### Nečas's inequality for every `W^{1,p}` function, and compactness of the trace -/

section Compact

/-- **Hölder's inequality in the form `∫ ‖f‖^{p−1} ‖g‖ ≤ ‖f‖_p^{p−1} ‖g‖_p`** for `1 ≤ p < ∞`
(an equality of integrals at `p = 1`). -/
theorem _root_.MeasureTheory.integral_norm_rpow_sub_one_mul_norm_le {X G G' : Type*}
    [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup G] [NormedAddCommGroup G']
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : X → G} {g : X → G'} (hf : MemLp f p μ)
    (hg : MemLp g p μ) :
    ∫ x, ‖f x‖ ^ (p.toReal - 1) * ‖g x‖ ∂μ
      ≤ (eLpNorm f p μ).toReal ^ (p.toReal - 1) * (eLpNorm g p μ).toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hP0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hfP := hf.eLpNorm_eq_integral_rpow_norm hp0 hp
  have hgP := hg.eLpNorm_eq_integral_rpow_norm hp0 hp
  rw [hfP, hgP, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rcases (Fact.out : (1 : ℝ≥0∞) ≤ p).eq_or_lt with h1 | h1
  · -- `p = 1`: both sides are `∫ ‖g‖`
    subst h1
    simp only [ENNReal.toReal_one, sub_self, Real.rpow_zero, one_mul, inv_one, Real.rpow_one]
    exact le_rfl
  · -- `1 < p`: Hölder with the exponents `p/(p−1)` and `p`
    have hP1 : 1 < p.toReal := by
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 h1
    have hP1' : 0 < p.toReal - 1 := by linarith
    have hconj : (Real.conjExponent p.toReal).HolderConjugate p.toReal :=
      (Real.HolderConjugate.conjExponent hP1).symm
    have hq : Real.conjExponent p.toReal = p.toReal / (p.toReal - 1) := rfl
    have hfq : MemLp (fun x ↦ ‖f x‖ ^ (p.toReal - 1))
        (ENNReal.ofReal (Real.conjExponent p.toReal)) μ := by
      have h := hf.norm_rpow_div (ENNReal.ofReal (p.toReal - 1))
      rw [ENNReal.toReal_ofReal hP1'.le] at h
      convert h using 1
      rw [hq, ENNReal.ofReal_div_of_pos hP1', ENNReal.ofReal_toReal hp]
    have hgq : MemLp (fun x ↦ ‖g x‖) (ENNReal.ofReal p.toReal) μ := by
      rw [ENNReal.ofReal_toReal hp]
      exact hg.norm
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
      (.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) (.of_forall fun x ↦ norm_nonneg _)
      hfq hgq
    refine hH.trans (le_of_eq ?_)
    have e1 : ∀ x, (‖f x‖ ^ (p.toReal - 1)) ^ Real.conjExponent p.toReal = ‖f x‖ ^ p.toReal := by
      intro x
      rw [← Real.rpow_mul (norm_nonneg _), hq, mul_div_cancel₀ _ hP1'.ne']
    simp_rw [e1]
    rw [← Real.rpow_mul (integral_nonneg fun x ↦ by positivity), one_div, one_div, hq, inv_div,
      inv_mul_eq_div]

/-- The gradient norm is continuous on `W^{1,p}(Ω)`. -/
theorem _root_.SobolevEuclidean.continuous_gradNorm {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Continuous fun u : SobolevEuclidean N 1 p Ω ↦ gradNorm u := by
  refine continuous_norm.comp ((PiLp.continuous_toLp p _).comp (continuous_pi fun i ↦ ?_))
  exact (weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
    (MultiIndexLE.single i)).continuous

/-- `‖∇u‖_{L^p(Ω)} ≤ N ‖∇u‖` for the Euclidean pointwise gradient (`gradFn`) and the `ℓ^p`
gradient norm (`gradNorm`). -/
theorem _root_.SobolevEuclidean.toReal_eLpNorm_gradFn_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : SobolevEuclidean N 1 p Ω) :
    (eLpNorm (gradFn u) p (volume.restrict (Ω : Set 𝔼))).toReal ≤ N * gradNorm u := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hP0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h := integral_norm_gradFn_rpow_le hp u
  rw [Fintype.card_fin] at h
  rw [(memLp_gradFn u).eLpNorm_eq_integral_rpow_norm hp0 hp,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x ↦ by positivity) _)]
  calc (∫ x in (Ω : Set 𝔼), ‖gradFn u x‖ ^ p.toReal) ^ p.toReal⁻¹
      ≤ ((N : ℝ) ^ p.toReal * gradNorm u ^ p.toReal) ^ p.toReal⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x ↦ by positivity) h (by positivity)
    _ = N * gradNorm u := by
        rw [← Real.mul_rpow (by positivity) (gradNorm_nonneg u), ← Real.rpow_mul
          (mul_nonneg N.cast_nonneg (gradNorm_nonneg u)), mul_inv_cancel₀ hP0.ne', Real.rpow_one]

/-- **Nečas's inequality for every `W^{1,p}` function** (Atkinson–Han Theorem 7.3.10 (c), the
estimate behind compactness): there is `C` such that for every `u ∈ W^{1,p}(Ω)`,
`∫ |Tu|^p dσ ≤ C (‖u‖_p^p + ‖u‖_p^{p−1} ‖∇u‖_p)`
with `‖u‖_p = ‖fnL u‖` and `‖∇u‖_p = gradNorm u`. For smooth-representable `u` it is
`integral_abs_rpow_le_of_contDiff` after Hölder on the mixed term
(`integral_norm_rpow_sub_one_mul_norm_le`); both sides are continuous in `u` and the
smooth-representable elements are dense. -/
theorem integral_abs_traceL_rpow_le (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hd : SobolevEuclidean.HasSmoothDensity N p Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω,
      ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
        ≤ C * (‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ p.toReal
          + ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ (p.toReal - 1)
            * gradNorm u) := by
  have hw₀ := hw
  obtain ⟨w, hw', hwc, hwν⟩ := hw₀
  obtain ⟨M₀, hM₀⟩ := hw'.continuous.bounded_above_of_compact_support hwc
  obtain ⟨M₁, hM₁⟩ :=
    (hw'.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hwc.fderiv (𝕜 := ℝ))
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_ne_top hp
  have hP0 : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hC₀ : 0 ≤ max (N * M₁) (p.toReal * M₀) := le_max_of_le_right (by positivity)
  refine ⟨max (N * M₁) (p.toReal * M₀) * (1 + N), by positivity, fun u ↦ ?_⟩
  -- the inequality on the smooth-representable elements
  have key : ∀ u ∈ SobolevEuclidean.smoothRestrictions N p Ω,
      ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
        ≤ max (N * M₁) (p.toReal * M₀) * (1 + N)
          * (‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ p.toReal
            + ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ (p.toReal - 1)
              * gradNorm u) := by
    rintro u ⟨v, hv, hvc, huv⟩
    have hv1 : ContDiff ℝ 1 v := hv.of_le (by simp)
    have hnec := B.integral_abs_rpow_le_of_contDiff hw' hwc hwν hM₀ hM₁ hP1 hv1
    have e0 : ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
        = ∫ x, |v x| ^ p.toReal ∂B.σ := by
      refine integral_congr_ae ?_
      filter_upwards [B.traceL_ae_eq_of_contDiff hw hp hd u hv hvc huv] with x hx
      rw [hx]
    have e1 := SobolevEuclidean.integral_abs_rpow_eq_norm_fnL hp u huv
    -- the mixed term by Hölder
    have e2 : ∫ x in (Ω : Set 𝔼), |v x| ^ (p.toReal - 1) * ‖fderiv ℝ v x‖
        = ∫ x in (Ω : Set 𝔼), ‖fn u x‖ ^ (p.toReal - 1) * ‖gradFn u x‖ := by
      refine integral_congr_ae ?_
      filter_upwards [huv, SobolevEuclidean.norm_fderiv_ae_eq_norm_gradFn u hv1 huv] with x h1 h2
      rw [h1, h2, Real.norm_eq_abs]
    have h2 := MeasureTheory.integral_norm_rpow_sub_one_mul_norm_le hp (memLp u) (memLp_gradFn u)
    have h3 := SobolevEuclidean.toReal_eLpNorm_gradFn_le hp u
    have hfn : (eLpNorm (fn u) p (volume.restrict (Ω : Set 𝔼))).toReal
        = ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ := by
      rw [Lp.norm_def, fnL_apply]
    rw [hfn] at h2
    set a := ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have hg0 : 0 ≤ gradNorm u := gradNorm_nonneg u
    calc ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
        = ∫ x, |v x| ^ p.toReal ∂B.σ := e0
      _ ≤ max (N * M₁) (p.toReal * M₀) * ((∫ x in (Ω : Set 𝔼), |v x| ^ p.toReal)
          + ∫ x in (Ω : Set 𝔼), |v x| ^ (p.toReal - 1) * ‖fderiv ℝ v x‖) := hnec
      _ ≤ max (N * M₁) (p.toReal * M₀)
          * (a ^ p.toReal + a ^ (p.toReal - 1) * (N * gradNorm u)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add (le_of_eq e1) ?_) hC₀
          rw [e2]
          exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ ≤ max (N * M₁) (p.toReal * M₀) * (1 + N)
          * (a ^ p.toReal + a ^ (p.toReal - 1) * gradNorm u) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hC₀
          have h4 : 0 ≤ a ^ p.toReal := by positivity
          have h5 : 0 ≤ a ^ (p.toReal - 1) * gradNorm u := by positivity
          nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  refine hd.dense_smoothRestrictions.induction (P := fun u : SobolevEuclidean N 1 p Ω ↦
    ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
      ≤ max (N * M₁) (p.toReal * M₀) * (1 + N)
        * (‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ p.toReal
          + ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ (p.toReal - 1)
            * gradNorm u)) key ?_ u
  -- closedness: both sides are continuous in `u`
  have hL : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
      ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ := by
    have h : Continuous fun u : SobolevEuclidean N 1 p Ω ↦ ‖B.traceL hw p hp u‖ ^ p.toReal :=
      (continuous_norm.comp (B.traceL hw p hp).continuous).rpow_const fun _ ↦ Or.inr hP0.le
    refine h.congr fun u ↦ ?_
    rw [Lp.norm_rpow_eq_integral hp0 hp]
    simp_rw [Real.norm_eq_abs]
  have hfnc : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
      ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ :=
    continuous_norm.comp (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).continuous
  refine isClosed_le hL (continuous_const.mul ((hfnc.rpow_const fun _ ↦ Or.inr hP0.le).add
    ((hfnc.rpow_const fun _ ↦ Or.inr (by linarith)).mul SobolevEuclidean.continuous_gradNorm)))

/-- **Compactness of the trace** (Atkinson–Han Theorem 7.3.10 (c)): for `1 < p < ∞`, if the
embedding `W^{1,p}(Ω) → L^p(Ω)` is compact (Rellich–Kondrachov,
`SobolevEuclidean.isCompactEmbedding_fnL` on bounded `C¹` chart domains), the trace
`T : W^{1,p}(Ω) →L L^p(σ)` is a compact operator. Given a sequence in the unit ball, extract a
subsequence whose `L^p(Ω)` parts converge; Nečas's inequality `integral_abs_traceL_rpow_le`
applied to the differences bounds `‖T(uₙ − uₘ)‖` by `(C (t^p + 2 t^{p−1}))^{1/p}` with
`t = ‖uₙ − uₘ‖_p → 0`, so the traces are Cauchy in the complete `L^p(σ)`.

The hypothesis `1 < p` is necessary: at `p = 1` the modulus `C (t + 2)` does not vanish at
`t = 0`, and indeed the trace `W^{1,1}(Ω) → L¹(∂Ω)` is onto (Gagliardo), hence not compact — the
book's `1 ≤ p` in (c) is an erratum. -/
theorem isCompactOperator_traceL (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    (hR : IsCompactEmbedding
      (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).toLinearMap) :
    IsCompactOperator (B.traceL hw p hp) := by
  obtain ⟨C, hC0, hC⟩ := B.integral_abs_traceL_rpow_le hw p hp hd
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hP1 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  have hP0 : 0 < p.toReal := zero_lt_one.trans hP1
  have hP1' : 0 < p.toReal - 1 := by linarith
  -- the modulus of continuity (`obtain` rather than `set`: `set` abstracts in typed hypotheses)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      ∀ t, g t = (C * (t ^ p.toReal + 2 * t ^ (p.toReal - 1))) ^ (1 / p.toReal) :=
    ⟨_, fun _ ↦ rfl⟩
  have hgc : Continuous g := by
    refine Continuous.congr ?_ fun t ↦ (hg t).symm
    exact (continuous_const.mul ((continuous_id.rpow_const fun _ ↦ Or.inr hP0.le).add
      (continuous_const.mul (continuous_id.rpow_const fun _ ↦ Or.inr hP1'.le)))).rpow_const
      fun _ ↦ Or.inr (by positivity)
  have hg0 : g 0 = 0 := by
    rw [hg, Real.zero_rpow hP0.ne', Real.zero_rpow hP1'.ne', mul_zero, add_zero, mul_zero,
      one_div, Real.zero_rpow (inv_ne_zero hP0.ne')]
  have hgt : Tendsto g (𝓝 0) (𝓝 (g 0)) := hgc.tendsto 0
  rw [hg0] at hgt
  -- the key estimate on the unit ball
  have key : ∀ a b : SobolevEuclidean N 1 p Ω, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      dist (B.traceL hw p hp a) (B.traceL hw p hp b)
        ≤ g (dist (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume a)
          (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume b)) := by
    intro a b ha hb
    rw [dist_eq_norm, dist_eq_norm, ← (B.traceL hw p hp).map_sub,
      ← (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).map_sub]
    have hab := hC (a - b)
    have ht0 : 0 ≤ ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (a - b)‖ :=
      norm_nonneg _
    have hgrad : gradNorm (a - b) ≤ 2 :=
      (gradNorm_le_norm _).trans ((norm_sub_le _ _).trans (by linarith))
    have hTP : ‖B.traceL hw p hp (a - b)‖ ^ p.toReal
        = ∫ x, |(B.traceL hw p hp (a - b) : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ := by
      rw [Lp.norm_rpow_eq_integral hp0 hp]
      simp_rw [Real.norm_eq_abs]
    calc ‖B.traceL hw p hp (a - b)‖ = (‖B.traceL hw p hp (a - b)‖ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hP0.ne', Real.rpow_one]
      _ ≤ (C * (‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (a - b)‖ ^ p.toReal
          + 2 * ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (a - b)‖
            ^ (p.toReal - 1))) ^ (1 / p.toReal) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [hTP]
          refine hab.trans (mul_le_mul_of_nonneg_left ?_ hC0)
          have := mul_le_mul_of_nonneg_left hgrad (Real.rpow_nonneg ht0 (p.toReal - 1))
          linarith
      _ = g ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (a - b)‖ := (hg _).symm
  -- sequential compactness of the closure of the image of the unit ball
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (B.traceL hw p hp).toLinearMap one_pos).2 ?_
  refine IsSeqCompact.isCompact fun {y} hy ↦ ?_
  have hy' : ∀ n : ℕ, ∃ v : SobolevEuclidean N 1 p Ω, ‖v‖ ≤ 1 ∧
      dist (y n) (B.traceL hw p hp v) < 1 / (n + 1) := by
    intro n
    obtain ⟨z, ⟨v, hv, rfl⟩, hz⟩ := Metric.mem_closure_iff.1 (hy n) (1 / (n + 1)) (by positivity)
    exact ⟨v, mem_closedBall_zero_iff.1 hv, hz⟩
  choose v hv hvy using hy'
  obtain ⟨φ, w, hφ, hw'⟩ := hR.exists_subseq_tendsto v ⟨1, hv⟩
  have hcauchy : CauchySeq fun n ↦ B.traceL hw p hp (v (φ n)) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hb : Tendsto (fun mn : ℕ × ℕ ↦
        dist (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (v (φ mn.1)))
          (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (v (φ mn.2))))
        atTop (𝓝 0) :=
      cauchySeq_iff_tendsto_dist_atTop_0.1 hw'.cauchySeq
    have hgb : Tendsto (fun mn : ℕ × ℕ ↦
        g (dist (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (v (φ mn.1)))
          (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (v (φ mn.2)))))
        atTop (𝓝 0) := hgt.comp hb
    exact squeeze_zero (fun _ ↦ dist_nonneg)
      (fun mn ↦ key (v (φ mn.1)) (v (φ mn.2)) (hv _) (hv _)) hgb
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨z, isClosed_closure.mem_of_tendsto hz (.of_forall fun n ↦
    subset_closure (mem_image_of_mem _ (mem_closedBall_zero_iff.2 (hv _)))), φ, hφ,
    hz.congr_dist ?_⟩
  refine squeeze_zero (g := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) (fun n ↦ dist_nonneg) (fun n ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [dist_comm]
  refine (hvy (φ n)).le.trans (one_div_le_one_div_of_le (by positivity) ?_)
  have : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.le_apply
  linarith


end Compact

end BoundaryData
