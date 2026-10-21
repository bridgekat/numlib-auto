import Numlib.Optimization.ResidualPowerObjective
import Numlib.Optimization.MeasureDomination
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

/-!
# Full-rank residual objectives

A uniform lower bound on the adjoint residual derivative gives gradient domination of
an actual residual norm power. Only pointwise differentiability is required. All formulas
include zero residuals; no normalization or division by a residual norm is used there.
-/

noncomputable section
namespace Optimization

open scoped InnerProduct RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Uniform full row rank in Hilbert spaces: the residual is differentiable on the domain,
and every adjoint derivative is bounded below by the same positive constant. -/
structure HasUniformlyFullRankDerivative (D : Set E) (r : E → F) (σ : ℝ) : Prop where
  lower_pos : 0 < σ
  differentiableAt : ∀ x ∈ D, DifferentiableAt ℝ r x
  adjoint_lower : ∀ x ∈ D, ∀ y : F, σ * ‖y‖ ≤ ‖(fderiv ℝ r x).adjoint y‖

/-- The gradient of the actual residual objective, including at zero residuals. -/
theorem hasGradientAt_residualPowerObjective {r : E → F} {x : E} {ell : ℝ}
    (hr : DifferentiableAt ℝ r x) (hell : 1 < ell) :
    HasGradientAt (residualPowerObjective r ell)
      (‖r x‖ ^ (ell - 2) • (fderiv ℝ r x).adjoint (r x)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := ((hasFDerivAt_norm_rpow (r x) hell).comp x hr.hasFDerivAt).const_smul ell⁻¹
  change HasFDerivAt (fun y => ‖r y‖ ^ ell / ell) _ x
  convert h using 1
  · funext y
    simp [div_eq_mul_inv, mul_comm]
  ext y
  simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]
  field_simp [ne_of_gt (lt_trans zero_lt_one hell)]

/-- The explicit gradient formula for a differentiable residual map. -/
theorem gradient_residualPowerObjective {r : E → F} {x : E} {ell : ℝ}
    (hr : DifferentiableAt ℝ r x) (hell : 1 < ell) :
    gradient (residualPowerObjective r ell) x =
      ‖r x‖ ^ (ell - 2) • (fderiv ℝ r x).adjoint (r x) :=
  (hasGradientAt_residualPowerObjective hr hell).gradient

/-- Full row rank bounds the actual gradient from below by a residual norm power. -/
theorem HasUniformlyFullRankDerivative.gradient_lower {D : Set E} {r : E → F} {σ ell : ℝ}
    (h : HasUniformlyFullRankDerivative D r σ) (hell : 1 < ell) {x : E} (hx : x ∈ D) :
    σ * ‖r x‖ ^ (ell - 1) ≤ ‖gradient (residualPowerObjective r ell) x‖ := by
  rw [gradient_residualPowerObjective (h.differentiableAt x hx) hell,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  by_cases hz : r x = 0
  · simp [hz, Real.zero_rpow (by linarith : ell - 1 ≠ 0)]
  · have hn : 0 < ‖r x‖ := norm_pos_iff.mpr hz
    calc
      σ * ‖r x‖ ^ (ell - 1) = ‖r x‖ ^ (ell - 2) * (σ * ‖r x‖) := by
        have he : ell - 1 = (ell - 2) + 1 := by ring
        rw [he, Real.rpow_add hn, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h.adjoint_lower x hx (r x))
        (Real.rpow_nonneg hn.le _)

/-- The full-rank derivative property restricts to a smaller domain. -/
theorem HasUniformlyFullRankDerivative.mono {D D' : Set E} {r : E → F} {σ : ℝ}
    (h : HasUniformlyFullRankDerivative D r σ) (hD : D' ⊆ D) :
    HasUniformlyFullRankDerivative D' r σ :=
  ⟨h.lower_pos, fun x hx => h.differentiableAt x (hD hx),
    fun x hx => h.adjoint_lower x (hD hx)⟩

/-- For a full-rank residual map, stationarity of a norm power is equivalent to a zero
residual, including for real powers strictly between one and two. -/
theorem HasUniformlyFullRankDerivative.gradient_eq_zero_iff
    {D : Set E} {r : E → F} {σ ell : ℝ}
    (h : HasUniformlyFullRankDerivative D r σ) (hell : 1 < ell) {x : E} (hx : x ∈ D) :
    gradient (residualPowerObjective r ell) x = 0 ↔ r x = 0 := by
  constructor
  · intro hg
    by_contra hr
    have hp := mul_pos h.lower_pos
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hr) (ell - 1))
    have hl := h.gradient_lower hell hx
    rw [hg, norm_zero] at hl
    linarith
  · intro hr
    rw [gradient_residualPowerObjective (h.differentiableAt x hx) hell, hr, map_zero,
      smul_zero]

/-- The exact domination constant for a residual norm power and adjoint lower bound. -/
def residualDominationConstant (ell σ : ℝ) : ℝ :=
  1 / (ell * σ ^ (ell / (ell - 1)))

/-- Positivity of the residual domination constant under its natural assumptions. -/
theorem residualDominationConstant_pos {ell σ : ℝ} (hell : 0 < ell) (hσ : 0 < σ) :
    0 < residualDominationConstant ell σ :=
  one_div_pos.mpr (mul_pos hell (Real.rpow_pos_of_pos hσ _))

/-- Least squares has the familiar reciprocal squared full-rank constant. -/
@[simp] theorem residualDominationConstant_two (σ : ℝ) :
    residualDominationConstant 2 σ = 1 / (2 * σ ^ 2) := by
  norm_num [residualDominationConstant, Real.rpow_two]

/-- Uniform full row rank yields gradient domination at exponent `ell / (ell - 1)`.
The constant is independent of the point and of any requested tolerance. -/
theorem HasUniformlyFullRankDerivative.isMeasureDominated
    {D : Set E} {r : E → F} {σ ell : ℝ}
    (h : HasUniformlyFullRankDerivative D r σ) (hell : 1 < ell) :
    MeasureDomination.IsMeasureDominated D (residualPowerObjective r ell)
      (fun x => ‖gradient (residualPowerObjective r ell) x‖) 0
      (residualDominationConstant ell σ) (ell / (ell - 1)) := by
  have he : 0 < ell := lt_trans zero_lt_one hell
  have hm : 0 < ell / (ell - 1) := div_pos he (sub_pos.mpr hell)
  refine ⟨residualDominationConstant_pos he h.lower_pos, hm,
    fun _ _ => norm_nonneg _, fun x _ => by
      simpa using residualPowerObjective_nonneg r he.le x, ?_⟩
  intro x hx
  have hp := Real.rpow_le_rpow (mul_nonneg h.lower_pos.le
    (Real.rpow_nonneg (norm_nonneg (r x)) _)) (h.gradient_lower hell hx) hm.le
  rw [Real.mul_rpow h.lower_pos.le (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _)] at hp
  have hmul : (ell - 1) * (ell / (ell - 1)) = ell := by
    field_simp [ne_of_gt (sub_pos.mpr hell)]
  rw [hmul] at hp
  dsimp [residualPowerObjective, residualDominationConstant]
  rw [sub_zero]
  apply (div_le_iff₀ he).mpr
  have hs : 0 < σ ^ (ell / (ell - 1)) := Real.rpow_pos_of_pos h.lower_pos _
  calc
    ‖r x‖ ^ ell ≤ ‖gradient (residualPowerObjective r ell) x‖ ^ (ell / (ell - 1)) /
      σ ^ (ell / (ell - 1)) := (le_div_iff₀ hs).mpr (by simpa [mul_comm] using hp)
    _ = _ := by field_simp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [InnerProductSpace ℝ F] [CompleteSpace F] in
/-- The residual tolerance and its objective-gap tolerance are equivalent, including zero. -/
theorem residualPowerObjective_le_iff {r : E → F} {ell ε : ℝ} (hell : 0 < ell)
    (hε : 0 ≤ ε) (x : E) :
    residualPowerObjective r ell x ≤ ε ^ ell / ell ↔ ‖r x‖ ≤ ε := by
  rw [residualPowerObjective, div_le_div_iff_of_pos_right hell]
  exact Real.rpow_le_rpow_iff (norm_nonneg _) hε hell

end Optimization
