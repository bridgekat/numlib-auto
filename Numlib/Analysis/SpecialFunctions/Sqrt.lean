/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Real.Sqrt` (plain `√` arithmetic; `SpecialFunctions.Sqrt` is
about smoothness).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Real.Sqrt

/-!
# The sum of two square roots

`Real.sqrt_add_sqrt_le_sqrt_two_mul`: `√p + √q ≤ √2 √(p + q)` for `p, q ≥ 0`, the case of two terms
of `(∑ √aᵢ)² ≤ n ∑ aᵢ`.
-/

namespace Real

/-- `√p + √q ≤ √2 √(p + q)` for `p, q ≥ 0`. -/
theorem sqrt_add_sqrt_le_sqrt_two_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    √p + √q ≤ √2 * √(p + q) := by
  have hsq : (√p + √q) ^ 2 ≤ (√2 * √(p + q)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (add_nonneg hp hq), add_sq,
      Real.sq_sqrt hp, Real.sq_sqrt hq]
    nlinarith [sq_nonneg (√p - √q), Real.sq_sqrt hp, Real.sq_sqrt hq]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

end Real
