import Numlib.Optimization.LeastSquares.Powers
import Numlib.Analysis.SpecialFunctions.Pow.Normalized

/-!
# Normalized residual-power criticality measures

The measures use actual residual-power objective derivatives and the residual
weight `‖r(x)‖^(ℓ-1)`. A least-Hessian value receives an actual eigenpair
certificate when used in optimization results. Weighted decrease bounds extend
to zero normalizations with real division.
-/

namespace LeastSquares
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- The residual factor normalizing each low-order objective derivative in Section 5.1. -/
noncomputable def derivativeWeight (r : E → F) (ℓ : ℝ) (x : E) : ℝ := ‖r x‖ ^ (ℓ - 1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The exact scalar normalization of every derivative measure. -/
theorem derivativeWeight_eq (r : E → F) (ℓ : ℝ) (x : E) :
    derivativeWeight r ℓ x = ‖r x‖ ^ (ℓ - 1) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The residual derivative weight is nonnegative, including residual zeros. -/
theorem derivativeWeight_nonneg (r : E → F) (ℓ : ℝ) (x : E) :
    0 ≤ derivativeWeight r ℓ x := Real.rpow_nonneg (norm_nonneg _) _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Nonzero residuals have a strictly positive derivative normalization. -/
theorem derivativeWeight_pos (r : E → F) (ℓ : ℝ) {x : E} (hx : r x ≠ 0) :
    0 < derivativeWeight r ℓ x := Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _

/-- The source normalized first derivative of the actual residual-power objective. -/
noncomputable def firstMeasure (r : E → F) (ℓ : ℝ) (x : E) : ℝ :=
  ‖fderiv ℝ (powerObjective r ℓ) x‖ / derivativeWeight r ℓ x

/-- The source normalized least Hessian value, supplied with an actual eigenpair
certificate when used. -/
noncomputable def secondMeasure (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ) : ℝ :=
  μ / derivativeWeight r ℓ x

/-- The source normalized absolute directional Hessian of the actual objective. -/
noncomputable def directionalSecondMeasure (r : E → F) (ℓ : ℝ) (x v : E) : ℝ :=
  |iteratedFDeriv ℝ 2 (powerObjective r ℓ) x (fun _ => v)| / derivativeWeight r ℓ x

/-- The source normalized absolute third derivative of the actual objective. -/
noncomputable def thirdMeasure (r : E → F) (ℓ : ℝ) (x v : E) : ℝ :=
  |iteratedFDeriv ℝ 3 (powerObjective r ℓ) x (fun _ => v)| / derivativeWeight r ℓ x

/-- The first normalized measure is the true objective derivative norm divided by its weight. -/
theorem firstMeasure_eq (r : E → F) (ℓ : ℝ) (x : E) :
    firstMeasure r ℓ x = ‖fderiv ℝ (powerObjective r ℓ) x‖ /
      derivativeWeight r ℓ x := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The normalized least Hessian measure is its supplied genuine eigenvalue divided by the
weight. -/
theorem secondMeasure_eq (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ) :
    secondMeasure r ℓ x μ = μ / derivativeWeight r ℓ x := rfl

/-- The directional Hessian measure uses the actual absolute tensor value. -/
theorem directionalSecondMeasure_eq (r : E → F) (ℓ : ℝ) (x v : E) :
    directionalSecondMeasure r ℓ x v =
      |iteratedFDeriv ℝ 2 (powerObjective r ℓ) x (fun _ => v)| / derivativeWeight r ℓ x := rfl

/-- The third normalized measure uses the actual absolute tensor value. -/
theorem thirdMeasure_eq (r : E → F) (ℓ : ℝ) (x v : E) :
    thirdMeasure r ℓ x v =
      |iteratedFDeriv ℝ 3 (powerObjective r ℓ) x (fun _ => v)| / derivativeWeight r ℓ x := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Normalizing a least Hessian value commutes with its nonnegative negative part. -/
theorem max_neg_secondMeasure (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ) :
    max 0 (-secondMeasure r ℓ x μ) = max 0 (-μ) / derivativeWeight r ℓ x := by
  simpa only [secondMeasure, neg_div, zero_div] using
    max_div_div_right (derivativeWeight_nonneg r ℓ x) 0 (-μ)

/-- The directional third measure is exactly the absolute normalized tensor value in (5.1.6). -/
theorem thirdMeasure_eq_abs_div (r : E → F) (ℓ : ℝ) (x v : E) :
    thirdMeasure r ℓ x v =
      |iteratedFDeriv ℝ 3 (powerObjective r ℓ) x (fun _ => v) / derivativeWeight r ℓ x| := by
  rw [abs_div, abs_of_nonneg (derivativeWeight_nonneg r ℓ x)]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The change in residual power is exactly the exponent times the objective change. -/
theorem residual_power_drop_eq (r : E → F) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x y : E) :
    ‖r x‖ ^ ℓ - ‖r y‖ ^ ℓ =
      ℓ * (powerObjective r ℓ x - powerObjective r ℓ y) := by
  unfold powerObjective
  field_simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- An actual objective decrease yields the normalized residual-power decrease without
excluding a zero endpoint residual. -/
theorem residual_decrease_of_power {r : E → F} {ℓ κ u a : ℝ} (hℓ : 0 < ℓ)
    (hκ : 0 ≤ κ) (hu : 0 ≤ u) (ha : 0 < a) {x y : E}
    (hdrop : κ * u ^ a ≤ powerObjective r ℓ x - powerObjective r ℓ y) :
    κ * ℓ * (u / derivativeWeight r ℓ y) ^ a * ‖r y‖ ^ ((ℓ - 1) * a) ≤
      ‖r x‖ ^ ℓ - ‖r y‖ ^ ℓ := by
  have hn := Real.normalized_rpow_mul_le hu (derivativeWeight_nonneg r ℓ y) ha
  have hnorm : derivativeWeight r ℓ y ^ a = ‖r y‖ ^ ((ℓ - 1) * a) := by
    exact (Real.rpow_mul (norm_nonneg _) _ _).symm
  rw [hnorm] at hn
  have hb := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hn hκ).trans hdrop) hℓ.le
  rw [residual_power_drop_eq r hℓ.ne' x y]
  convert hb using 1
  ring

end LeastSquares
