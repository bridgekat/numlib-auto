import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
# Radial power multiplier targets

Scalar power identities recover a radius and its square from a nonnegative radial multiplier.
No vector-space, dimension or Hessian assumptions are required.
-/

namespace Optimization.QuadraticSubproblem

/-- Inversion of a nonzero radial power retains the multiplier to the first power. -/
theorem radialShift_iff_radius {t lambda σ a : ℝ} (ht : 0 ≤ t) (hlambda : 0 ≤ lambda)
    (hσ : 0 < σ) (ha : a ≠ 0) :
    lambda = σ * t ^ a ↔ t = (lambda / σ) ^ (1 / a) := by
  constructor
  · rintro rfl
    rw [mul_div_cancel_left₀ _ hσ.ne', one_div, Real.rpow_rpow_inv ht ha]
  · intro h
    rw [h, one_div, Real.rpow_inv_rpow (div_nonneg hlambda hσ.le) ha]
    exact (mul_div_cancel₀ lambda hσ.ne').symm

/-- The squared radial target is `(lambda / sigma) ^ (2 / a)`. -/
theorem radialShift_iff_sq_radius {t lambda σ a : ℝ} (ht : 0 ≤ t) (hlambda : 0 ≤ lambda)
    (hσ : 0 < σ) (ha : a ≠ 0) :
    lambda = σ * t ^ a ↔ t ^ 2 = (lambda / σ) ^ (2 / a) := by
  rw [radialShift_iff_radius ht hlambda hσ ha]
  have hb : 0 ≤ lambda / σ := div_nonneg hlambda hσ.le
  have he : ((lambda / σ) ^ (1 / a)) ^ 2 =
      (lambda / σ) ^ (2 / a) := by
    rw [← Real.rpow_mul_natCast hb]
    congr 1
    ring
  rw [← he]
  exact (sq_eq_sq₀ ht (Real.rpow_nonneg hb _)).symm

/-- The inverse-power radial target agrees with the negative-exponent convention. -/
theorem inverse_radial_target_eq (σ a r : ℝ) :
    (1 / σ) ^ (a / (r - 2)) = σ ^ (-a / (r - 2)) := by
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  congr 1
  ring

end Optimization.QuadraticSubproblem
