/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A lower bound for $\log((1 + w)/(1 - w))$

For $|w| < 1$, Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one` gives the power series
$$\log(1 + w) - \log(1 - w) = \sum_{k \ge 0} \frac{2 w^{2k+1}}{2k + 1}.$$
For $0 \le w < 1$ all terms are nonnegative, so the sum is at least the sum of its first two terms.
This file proves the resulting bound $2w + \frac{2}{3} w^3 \le \log(1 + w) - \log(1 - w)$.

## Main results

* `Real.two_mul_add_le_log_sub_log`: $2w + \frac{2}{3} w^3 \le \log(1 + w) - \log(1 - w)$ for
  $0 \le w < 1$.
-/

namespace Real

/-- Let $0 \le w < 1$. Then
$$2w + \frac{2}{3} w^3 \le \log(1 + w) - \log(1 - w).$$

The power series $\log(1 + w) - \log(1 - w) = \sum_{k \ge 0} 2 w^{2k+1}/(2k + 1)$ has
nonnegative terms for these $w$, and the bound is the sum of its first two terms. -/
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
