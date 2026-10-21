/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A lower bound for `log ((1 + w) / (1 - w))`

Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one` is the power series
`log (1 + w) - log (1 - w) = ∑ 2 w^{2k+1} / (2k+1)` for `|w| < 1`. For `0 ≤ w < 1` its terms are
nonnegative, so it dominates its first two: `Real.two_mul_add_le_log_sub_log`,
`2 w + (2/3) w³ ≤ log (1 + w) - log (1 - w)`.
-/

namespace Real

/-- The power series of `log ((1 + w) / (1 - w))` has nonnegative terms for `0 ≤ w < 1`, so it
dominates the sum of its first two: `2 w + (2/3) w³ ≤ log (1 + w) - log (1 - w)`. -/
theorem two_mul_add_le_log_sub_log {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    2 * w + 2 / 3 * w ^ 3 ≤ Real.log (1 + w) - Real.log (1 - w) := by
  have habs : |w| < 1 := by rwa [abs_of_nonneg hw0]
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * w ^ (2 * k + 1) := by
    intro k
    positivity
  have h := sum_le_hasSum (Finset.range 2) (fun i _ => hnn i) hsum
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

end Real
