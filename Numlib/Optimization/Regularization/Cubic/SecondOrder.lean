import Numlib.Optimization.Regularization.Cubic.Gradient
import Numlib.Optimization.TrustRegion.SecondOrder.Finite
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# Genuine cubic-model second derivatives and curvature step bounds

The derivative of the cubic gradient is computed at every step, including zero.
The penalty Hessian has norm at most `σ * ‖s‖`; its coefficient is `σ/2`, correcting
the missing factor one half in the source's unnumbered formula after (3.3.2).
-/

open scoped Topology
namespace CubicRegularization
open TaylorModel Asymptotics
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine derivative of the cubic gradient penalty, with its zero-step extension. -/
noncomputable def penaltySecondDerivative (σ : ℝ) (s : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  (σ / 2) • (‖s‖ • J + (fderiv ℝ (norm : E → ℝ) s).smulRight (innerSL ℝ s))

/-- The cubic penalty Hessian is zero at a zero step. -/
@[simp] theorem penaltySecondDerivative_zero (σ : ℝ) :
    penaltySecondDerivative σ (0 : E) = 0 := by
  ext v w
  simp [penaltySecondDerivative]

/-- Away from zero the actual norm derivative is the normalized inner product. -/
theorem norm_derivative_apply {s : E} (hs : s ≠ 0) (v : E) :
    fderiv ℝ (norm : E → ℝ) s v = inner ℝ s v / ‖s‖ := by
  have hn : HasFDerivAt (norm : E → ℝ) (fderiv ℝ norm s) s :=
    ((contDiffAt_norm ℝ (n := 1) (x := s) hs).differentiableAt one_ne_zero).hasFDerivAt
  have he := (hn.pow 2).unique (hasStrictFDerivAt_norm_sq s).hasFDerivAt
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) he
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply] at hh
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, nsmul_eq_mul] at hh
  apply (eq_div_iff (norm_ne_zero_iff.mpr hs)).mpr
  linarith

/-- The explicit corrected cubic penalty Hessian formula, also valid at zero
with real division by zero interpreted as zero. -/
theorem penaltySecondDerivative_apply (σ : ℝ) (s v w : E) :
    penaltySecondDerivative σ s v w = σ / 2 *
      (‖s‖ * inner ℝ v w + inner ℝ s v * inner ℝ s w / ‖s‖) := by
  by_cases hs : s = 0
  · subst s
    simp
  · change σ / 2 * (‖s‖ * inner ℝ v w +
      fderiv ℝ (norm : E → ℝ) s v * inner ℝ s w) = _
    rw [norm_derivative_apply hs]
    ring

/-- The map `s ↦ ‖s‖ inner(s,·)` has derivative zero at zero. -/
theorem hasFDerivAt_norm_smul_inner_zero :
    HasFDerivAt (fun s : E => ‖s‖ • innerSL ℝ s)
      (0 : E →L[ℝ] E →L[ℝ] ℝ) 0 := by
  apply HasFDerivAt.of_isLittleO
  have hh : (fun s : E => ‖s‖ • innerSL ℝ s) =O[nhds 0] (fun s : E => ‖s‖ ^ 2) := by
    apply IsBigO.of_bound' (Filter.Eventually.of_forall (fun s => ?_))
    simp [norm_smul, innerSL_apply_norm, sq]
  simpa using hh.trans_isLittleO (isLittleO_norm_pow_id (E' := E) (by norm_num : 1 < 2))

/-- Differentiating the actual cubic gradient penalty is valid also at zero. -/
theorem hasFDerivAt_penaltyGradient (σ : ℝ) (s : E) :
    HasFDerivAt (fun t : E => (σ / 2 * ‖t‖) • innerSL ℝ t)
      (penaltySecondDerivative σ s) s := by
  by_cases hs : s = 0
  · subst s
    have hh := hasFDerivAt_norm_smul_inner_zero (E := E) |>.const_smul (σ / 2)
    simpa [Pi.smul_def, smul_smul, penaltySecondDerivative_zero] using hh
  · have hn : HasFDerivAt (norm : E → ℝ) (fderiv ℝ norm s) s :=
      ((contDiffAt_norm ℝ (n := 1) (x := s) hs).differentiableAt one_ne_zero).hasFDerivAt
    let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
    have hh := (hn.smul J.hasFDerivAt).const_smul (σ / 2)
    convert hh using 1
    · funext t
      change (σ / 2 * ‖t‖) • innerSL ℝ t = (σ / 2) • (‖t‖ • J t)
      rw [smul_smul]
    · rfl

/-- The second derivative of the actual cubic model has the corrected penalty coefficient. -/
theorem hasFDerivAt_fderiv_model {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (σ : ℝ) (s : E) :
    HasFDerivAt (fderiv ℝ (model f x σ))
      (fderiv ℝ (fderiv ℝ f) x + penaltySecondDerivative σ s) s := by
  have hq : HasFDerivAt (quadraticDerivative f x)
      (fderiv ℝ (fderiv ℝ f) x) s := by
    change HasFDerivAt (fun y => fderiv ℝ f x + fderiv ℝ (fderiv ℝ f) x y) _ s
    simpa only [zero_add, Pi.add_def] using
      (hasFDerivAt_const (fderiv ℝ f x) s).add (fderiv ℝ (fderiv ℝ f) x).hasFDerivAt
  have hh := hq.add (hasFDerivAt_penaltyGradient σ s)
  convert hh using 1
  funext t
  exact fderiv_model hf σ t

/-- The actual curried second derivative of the cubic model. -/
theorem fderiv_fderiv_model {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (σ : ℝ) (s : E) :
    fderiv ℝ (fderiv ℝ (model f x σ)) s =
      fderiv ℝ (fderiv ℝ f) x + penaltySecondDerivative σ s :=
  (hasFDerivAt_fderiv_model hf σ s).fderiv

/-- The exact cubic penalty Hessian bound has coefficient one. -/
theorem norm_penaltySecondDerivative_le {σ : ℝ} (hσ : 0 ≤ σ) (s : E) :
    ‖penaltySecondDerivative σ s‖ ≤ σ * ‖s‖ := by
  have hn : ‖fderiv ℝ (norm : E → ℝ) s‖ ≤ 1 :=
    by simpa only [NNReal.coe_one] using
      (norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := E)) (x₀ := s))
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  change ‖(σ / 2) • (‖s‖ • J +
    (fderiv ℝ (norm : E → ℝ) s).smulRight (innerSL ℝ s))‖ ≤ _
  have houter := ContinuousLinearMap.opNorm_smul_le (σ / 2)
    (‖s‖ • J + (fderiv ℝ (norm : E → ℝ) s).smulRight (innerSL ℝ s))
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ σ / 2)] at houter
  have hh := norm_add_le (‖s‖ • J)
    ((fderiv ℝ (norm : E → ℝ) s).smulRight (innerSL ℝ s))
  have hi : ‖J‖ ≤ 1 := norm_innerSL_le ℝ
  have hinner := ContinuousLinearMap.opNorm_smul_le ‖s‖ J
  rw [Real.norm_of_nonneg (norm_nonneg s)] at hinner
  have hinner' : ‖‖s‖ • J‖ ≤ ‖s‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg s)]
  have hrank : ‖(fderiv ℝ (norm : E → ℝ) s).smulRight (innerSL ℝ s)‖ ≤ ‖s‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg s)
  have hsum : ‖‖s‖ • J +
      (fderiv ℝ (norm : E → ℝ) s).smulRight (innerSL ℝ s)‖ ≤ 2 * ‖s‖ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ σ / 2)]

/-- The actual model's second-order stationarity condition, expressed on every unit direction. -/
def SecondOrderStationary (f : E → ℝ) (x s : E) (σ θ : ℝ) : Prop :=
  ∀ v : E, ‖v‖ = 1 → -θ * ‖s‖ ≤ iteratedFDeriv ℝ 2 (model f x σ) s (fun _ => v)

/-- Genuine model second-order stationarity controls the trial Hessian quadratic form. -/
theorem trial_curvature_lower {f : E → ℝ} {L θ σ : ℝ}
    (hf : ContDiff ℝ 2 f) (hσ : 0 ≤ σ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (x s v : E) (hv : ‖v‖ = 1) (hstat : SecondOrderStationary f x s σ θ) :
    -(L + θ + σ) * ‖s‖ ≤ iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) := by
  have hp := hstat v hv
  have hd : iteratedFDeriv ℝ 2 (model f x σ) s (fun _ => v) =
      iteratedFDeriv ℝ 2 f x (fun _ => v) + penaltySecondDerivative σ s v v := by
    simp only [iteratedFDeriv_two_apply, fderiv_fderiv_model hf.contDiffAt,
      add_apply]
  rw [hd] at hp
  have he := (iteratedFDeriv ℝ 2 f (x + s) - iteratedFDeriv ℝ 2 f x).le_opNorm (fun _ => v)
  simp only [sub_apply, Fin.prod_const, hv, one_pow, mul_one,
    Real.norm_eq_abs] at he
  have hl := hlip (x + s) x
  rw [add_sub_cancel_left] at hl
  have habs : |iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) -
      iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ L * ‖s‖ := he.trans hl
  have hpen := (penaltySecondDerivative σ s v).le_opNorm v
  have hpen' := (penaltySecondDerivative σ s).le_opNorm v
  rw [hv, mul_one, Real.norm_eq_abs] at hpen
  rw [hv, mul_one] at hpen'
  have hupper := (le_abs_self _).trans
    (hpen.trans (hpen'.trans (norm_penaltySecondDerivative_le hσ s)))
  linarith [(abs_le.mp habs).1]

variable [CompleteSpace E]

/-- The unit-direction condition is exactly the least-eigenvalue model test
whenever the actual model Hessian least eigenpair is supplied. -/
theorem secondOrderStationary_iff_leastEigenvalue {f : E → ℝ} {x s u : E} {σ θ μ : ℝ}
    (hp : SecondOrderTrustRegion.IsLeastEigenpair (model f x σ) s μ u) :
    SecondOrderStationary f x s σ θ ↔ -θ * ‖s‖ ≤ μ := by
  constructor
  · intro h
    have hh := h u hp.unit
    rw [TaylorModel.tensor_curvature_of_eigenvector (model f x σ) s u hp.unit
      hp.eigenvector] at hh
    exact hh
  · intro h v hv
    exact h.trans (hp.least v hv)

/-- The genuine parameter trace gives the source's uniform negative-eigenvalue step bound. -/
theorem ModelTrace.step_length_lower_secondOrder {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ μ : ℝ} {N : ℕ}
    (h : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hθ : 0 < θ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hstat : SecondOrderStationary f (x i) (s i) (σ i) θ)
    (u : E) (hu : ‖u‖ = 1) (he : TaylorModel.hessianOperator f (x i + s i) u = μ • u)
    (hμ : μ < 0) :
    |μ| / (L + θ + max (σ 0) (γ₃ * L / (1 - η₂))) ≤ ‖s i‖ := by
  have hσ := h.updates.pos (show i ≤ N by omega)
  have hmax := h.parameter_le hf hL hlip (i := i) (by omega)
  have hmaxpos : 0 < max (σ 0) (γ₃ * L / (1 - η₂)) :=
    h.updates.pos (Nat.zero_le N) |>.trans_le (le_max_left _ _)
  have hden : 0 < L + θ + max (σ 0) (γ₃ * L / (1 - η₂)) := by positivity
  have hh := trial_curvature_lower hf hσ.le hlip (x i) (s i) u hu hstat
  rw [TaylorModel.tensor_curvature_of_eigenvector f (x i + s i) u hu he] at hh
  rw [abs_of_neg hμ]
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_right hmax (norm_nonneg (s i))]
end CubicRegularization
