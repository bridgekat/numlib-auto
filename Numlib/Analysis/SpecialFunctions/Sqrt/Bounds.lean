/-
Upstreaming candidate: elementary square-root bounds, naturally belonging beside
Mathlib.Analysis.Real.Sqrt. No optimization-specific assumptions are used.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
/-!
# Lower bounds for square-root increments

A nonnegative scaling of the increment `sqrt (b^2+a)-b` is bounded below by its value at
scaling one multiplied by `min 1 c`. The result allows zero parameters as well.
-/

namespace Real

/-- A lower bound for a square-root increment under a nonnegative scaling. -/
theorem min_mul_sqrt_sub_le_sqrt_add_mul_sub {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    -b + sqrt (b ^ 2 + a * c) ≥ (-b + sqrt (b ^ 2 + a)) * min 1 c := by
  have hbase : b ≤ sqrt (b ^ 2 + a) := by
    rw [Real.le_sqrt hb (by positivity)]
    linarith
  by_cases hc1 : c ≤ 1
  · rw [min_eq_right hc1]
    have hsq : (b + c * (sqrt (b ^ 2 + a) - b)) ^ 2 ≤ b ^ 2 + a * c := by
      have hprod := mul_nonneg (mul_nonneg hc (sub_nonneg.mpr hc1))
        (sq_nonneg (sqrt (b ^ 2 + a) - b))
      nlinarith [Real.sq_sqrt (show 0 ≤ b ^ 2 + a by positivity)]
    have hle := (Real.le_sqrt
      (show 0 ≤ b + c * (sqrt (b ^ 2 + a) - b) by positivity)
      (show 0 ≤ b ^ 2 + a * c by positivity)).2 hsq
    nlinarith
  · rw [min_eq_left (le_of_not_ge hc1), mul_one]
    have hrad : b ^ 2 + a ≤ b ^ 2 + a * c := by nlinarith
    linarith [Real.sqrt_le_sqrt hrad]

/-- On a disk of radius `r ≤ R`, the function `-x + sqrt (R²-y²)` is bounded below by
`R-r`. Both radii may be zero, and the boundary case `r = R` is included. -/
theorem sub_le_neg_add_sqrt_of_sq_add_sq_le {r R x y : ℝ} (hr : 0 ≤ r)
    (hR : r ≤ R) (hxy : x ^ 2 + y ^ 2 ≤ r ^ 2) :
    R - r ≤ -x + sqrt (R ^ 2 - y ^ 2) := by
  have hx : x ≤ r := by nlinarith [sq_nonneg y]
  have hrad : 0 ≤ R ^ 2 - y ^ 2 := by
    nlinarith [sq_nonneg x, mul_nonneg (sub_nonneg.mpr hR) (add_nonneg hr (hr.trans hR))]
  by_cases hleft : R - r + x ≤ 0
  · linarith [sqrt_nonneg (R ^ 2 - y ^ 2)]
  · have hsq : (R - r + x) ^ 2 ≤ R ^ 2 - y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hx)]
    have h := (le_sqrt (le_of_lt (lt_of_not_ge hleft)) hrad).2 hsq
    linarith

end Real
