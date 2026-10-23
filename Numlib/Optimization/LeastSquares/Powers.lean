import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Smoothness of Euclidean residual-power objectives

The objective `‖r(x)‖^ℓ / ℓ` factors through the smooth squared residual norm.
For even nonnegative integer exponents the outer function is a polynomial;
for real exponents at least twice the finite smoothness order it is a smooth
scalar real power. Local and global results include residual zeros, without
assuming differentiability of the norm at zero.
-/

namespace LeastSquares
variable {E F : Type*} [NormedAddCommGroup F]

/-- The Euclidean residual-power objective `‖r(x)‖^ℓ / ℓ`. -/
noncomputable def powerObjective (r : E → F) (ℓ : ℝ) (x : E) : ℝ := ‖r x‖ ^ ℓ / ℓ

/-- The residual-power objective evaluated at a point. -/
@[simp] theorem powerObjective_apply (r : E → F) (ℓ : ℝ) (x : E) :
    powerObjective r ℓ x = ‖r x‖ ^ ℓ / ℓ := rfl

/-- Exponent one gives the residual norm. -/
@[simp] theorem powerObjective_one (r : E → F) (x : E) :
    powerObjective r 1 x = ‖r x‖ := by simp [powerObjective]

/-- Exponent two gives the least-squares objective. -/
@[simp] theorem powerObjective_two (r : E → F) (x : E) :
    powerObjective r 2 x = ‖r x‖ ^ 2 / 2 := by simp [powerObjective]

/-- Rewriting through the smooth squared norm isolates the scalar power. -/
theorem powerObjective_eq_sq_norm_rpow (r : E → F) (ℓ : ℝ) (x : E) :
    powerObjective r ℓ x = (‖r x‖ ^ 2) ^ (ℓ / 2) / ℓ := by
  rw [powerObjective,←Real.rpow_two,←Real.rpow_mul (norm_nonneg _)]
  congr 2
  ring

/-- At an even nonnegative integer exponent the objective is a polynomial in the squared norm. -/
theorem powerObjective_even (r : E → F) (q : ℕ) (x : E) :
    powerObjective r (2 * (q : ℝ)) x = (‖r x‖ ^ 2) ^ q / (2 * (q : ℝ)) := by
  rw [powerObjective,Real.rpow_mul (norm_nonneg _),Real.rpow_two,Real.rpow_natCast]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ F]

/-- Even powers of residuals preserve all local smoothness, including at residual zeros. -/
theorem contDiffOn_powerObjective_even {r : E → F} {S : Set E} {p : WithTop ℕ∞}
    (hr : ContDiffOn ℝ p r S) (q : ℕ) :
    ContDiffOn ℝ p (powerObjective r (2 * (q : ℝ))) S := by
  have heq : powerObjective r (2 * (q : ℝ)) =
      fun x => (‖r x‖ ^ 2) ^ q / (2 * (q : ℝ)) := funext (powerObjective_even r q)
  rw [heq]
  exact ((hr.norm_sq ℝ).pow q).div_const _

/-- A real exponent at least twice the differentiability order preserves local smoothness. -/
theorem contDiffOn_powerObjective_of_two_mul_le {r : E → F} {S : Set E} {p : ℕ} {ℓ : ℝ}
    (hr : ContDiffOn ℝ p r S) (hℓ : 2 * (p : ℝ) ≤ ℓ) :
    ContDiffOn ℝ p (powerObjective r ℓ) S := by
  have heq : powerObjective r ℓ = fun x => (‖r x‖ ^ 2) ^ (ℓ / 2) / ℓ :=
    funext (powerObjective_eq_sq_norm_rpow r ℓ)
  rw [heq]
  exact ((hr.norm_sq ℝ).rpow_const_of_le (by linarith : (p : ℝ) ≤ ℓ / 2)).div_const _

/-- Even powers of residuals preserve global smoothness. -/
theorem contDiff_powerObjective_even {r : E → F} {p : WithTop ℕ∞}
    (hr : ContDiff ℝ p r) (q : ℕ) : ContDiff ℝ p (powerObjective r (2 * (q : ℝ))) := by
  rw [←contDiffOn_univ] at *
  exact contDiffOn_powerObjective_even hr q

/-- The real-power smoothness condition for globally smooth residuals. -/
theorem contDiff_powerObjective_of_two_mul_le {r : E → F} {p : ℕ} {ℓ : ℝ}
    (hr : ContDiff ℝ p r) (hℓ : 2 * (p : ℝ) ≤ ℓ) :
    ContDiff ℝ p (powerObjective r ℓ) := by
  rw [←contDiffOn_univ] at *
  exact contDiffOn_powerObjective_of_two_mul_le hr hℓ
end LeastSquares
