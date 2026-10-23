import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A nonintegral exact iteration count

A claimed equality between a natural iteration count and an inverse-accuracy
rate needs an integer-compatibility restriction or a rounding convention.
-/

namespace ExactSteepestDescent

/-- No natural iteration index equals the printed inverse-square count for
accuracy two thirds. -/
theorem no_exact_inverse_square_iterations :
    (0 < (2 / 3 : ℝ) ∧ (2 / 3 : ℝ) ≤ 1) ∧
      ¬∃ N : ℕ, (N : ℝ) = (2 / 3 : ℝ) ^ (-(2 : ℝ)) := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨N, hN⟩
  norm_num [Real.rpow_neg, Real.rpow_two] at hN
  have hlo : 2 < N := by exact_mod_cast (show (2 : ℝ) < N by linarith)
  have hhi : N < 3 := by exact_mod_cast (show (N : ℝ) < 3 by linarith)
  omega

end ExactSteepestDescent
