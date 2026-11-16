/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Pow.Real`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Comparing real and natural powers

Let $a, t \ge 0$ and let $m > 0$ and $n$ be natural numbers. This file proves that $a \le t^m$
implies $a^{n/m} \le t^n$, where $a^{n/m}$ is a real power. In the complexity analyses of
regularization methods, this step turns a lower bound $\|s\|^m \ge a$ on a step length into a lower
bound on a decrease $\|s\|^n$.

## Main results

* `Real.rpow_div_le_pow_of_le_pow`: if $a, t \ge 0$, $m > 0$ and $a \le t^m$, then
  $a^{n/m} \le t^n$.
-/

namespace Real

/-- Let $a, t \ge 0$ be real numbers, and let $m, n$ be natural numbers with $m > 0$. If
$a \le t^m$, then
$$a^{n/m} \le t^n.$$

The left side is the real power `Real.rpow` with exponent $n/m$, and the right side is a natural
power. -/
theorem rpow_div_le_pow_of_le_pow {a t : ℝ} {m n : ℕ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hm : 0 < m)
    (h : a ≤ t ^ m) : a ^ ((n : ℝ) / m) ≤ t ^ n := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  calc a ^ ((n : ℝ) / m) ≤ (t ^ m) ^ ((n : ℝ) / m) := by gcongr
    _ = t ^ n := by
        rw [← Real.rpow_natCast t m, ← Real.rpow_mul ht, mul_div_cancel₀ _ hm', Real.rpow_natCast]

end Real
