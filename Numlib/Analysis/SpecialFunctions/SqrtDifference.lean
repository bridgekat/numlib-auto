import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A lower scaling bound for square-root differences

Subtracting a fixed nonnegative base from the square root of its square plus a nonnegative
increment gives a concave quantity: scaling the increment scales the difference from below
by the smaller of one and the scale.
-/

namespace Real

/-- Scaling a nonnegative increment in a square-root difference gives a lower bound by
its unit-scale value times the smaller of one and the scale. -/
theorem sqrt_sq_add_mul_sub_ge_mul_min {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (sqrt (b ^ 2 + a) - b) * min 1 c ≤ sqrt (b ^ 2 + a * c) - b := by
  by_cases h1 : 1 ≤ c
  · rw [min_eq_left h1, mul_one]
    exact sub_le_sub_right (sqrt_le_sqrt (by nlinarith)) b
  · have hc1 : c ≤ 1 := le_of_not_ge h1
    rw [min_eq_right hc1]
    have hA : (sqrt (b ^ 2 + a)) ^ 2 = b ^ 2 + a := sq_sqrt (by positivity)
    have hC : (sqrt (b ^ 2 + a * c)) ^ 2 = b ^ 2 + a * c := sq_sqrt (by positivity)
    have hAb : b ≤ sqrt (b ^ 2 + a) := by
      calc
        b = sqrt (b ^ 2) := (sqrt_sq hb).symm
        _ ≤ _ := sqrt_le_sqrt (le_add_of_nonneg_right ha)
    have hz : 0 ≤ b + c * (sqrt (b ^ 2 + a) - b) := by positivity
    have hh := mul_nonneg (mul_nonneg hc (sub_nonneg.mpr hc1))
      (sq_nonneg (sqrt (b ^ 2 + a) - b))
    have hAc := congrArg (fun z : ℝ => c * z) hA
    nlinarith [sqrt_nonneg (b ^ 2 + a * c)]

/-- On a disk of radius `ω`, the shifted semicircle of radius `ε ≥ ω` is bounded
below by the difference of radii. The endpoint cases `ω = 0` and `ω = ε` are included. -/
theorem sub_add_sqrt_sq_sub_sq_ge_sub {ε ω f c : ℝ} (hω : 0 ≤ ω) (hεω : ω ≤ ε)
    (hdisk : f ^ 2 + c ^ 2 ≤ ω ^ 2) : ε - ω ≤ -f + sqrt (ε ^ 2 - c ^ 2) := by
  have hfw : f ≤ ω := by nlinarith [sq_nonneg c]
  have hprod := mul_nonneg (sub_nonneg.mpr hεω) (sub_nonneg.mpr hfw)
  have hs : (ε - ω + f) ^ 2 ≤ ε ^ 2 - c ^ 2 := by nlinarith
  linarith [le_sqrt_of_sq_le hs]

end Real
