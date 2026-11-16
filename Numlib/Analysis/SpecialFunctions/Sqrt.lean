/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Real.Sqrt` (plain `√` arithmetic; `SpecialFunctions.Sqrt` is
about smoothness).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Real.Sqrt

/-!
# Elementary bounds for square roots

This file proves two elementary inequalities for real square roots. The first is
$\sqrt{p} + \sqrt{q} \le \sqrt{2}\,\sqrt{p + q}$ for $p, q \ge 0$, which is the case of two terms of
$\bigl(\sum_{i=1}^n \sqrt{a_i}\bigr)^2 \le n \sum_{i=1}^n a_i$. The second is $A \le R \le A + F$
when $R^2 = A^2 + F^2$ with $R, A, F \ge 0$.

## Main results

* `Real.sqrt_add_sqrt_le_sqrt_two_mul`: $\sqrt{p} + \sqrt{q} \le \sqrt{2}\,\sqrt{p + q}$ for
  $p, q \ge 0$.
* `Real.le_and_le_add_of_sq_eq_add_sq`: if $R, A, F \ge 0$ and $R^2 = A^2 + F^2$, then
  $A \le R \le A + F$.
-/

namespace Real

/-- Let $p, q \ge 0$. Then
$$\sqrt{p} + \sqrt{q} \le \sqrt{2}\,\sqrt{p + q}.$$
-/
theorem sqrt_add_sqrt_le_sqrt_two_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    √p + √q ≤ √2 * √(p + q) := by
  have hsq : (√p + √q) ^ 2 ≤ (√2 * √(p + q)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (add_nonneg hp hq), add_sq,
      Real.sq_sqrt hp, Real.sq_sqrt hq]
    nlinarith [sq_nonneg (√p - √q), Real.sq_sqrt hp, Real.sq_sqrt hq]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- Let $R, A, F \ge 0$ be real numbers with $R^2 = A^2 + F^2$. Then $A \le R$ and $R \le A + F$. -/
theorem le_and_le_add_of_sq_eq_add_sq {R A F : ℝ} (hR : 0 ≤ R) (hsq : R ^ 2 = A ^ 2 + F ^ 2)
    (hA : 0 ≤ A) (hF : 0 ≤ F) : A ≤ R ∧ R ≤ A + F := by
  constructor <;> nlinarith [sq_nonneg (R - A), sq_nonneg (R - A - F), mul_nonneg hA hF]

end Real
