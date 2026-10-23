/-
Upstreaming candidate: positivity of normalized power gaps and their logarithmic threshold.
Natural home: Mathlib.Analysis.SpecialFunctions.Pow.Real.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Normalized power gaps

The difference `(a - 1)/a - (b - 1)/b` is positive precisely when `b < a`, for positive
`a` and `b`. When `a` is a power of a base greater than one, this has an exact logarithmic
threshold. The results keep both denominator positivity assumptions explicit.
-/

namespace Real

/-- Positivity of the difference of two normalized gaps is exactly the order of their
positive denominators. -/
theorem sub_one_div_sub_one_div_pos_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < (a - 1) / a - (b - 1) / b ↔ b < a := by
  rw [sub_pos, div_lt_div_iff₀ hb ha]
  constructor <;> intro h <;> nlinarith

/-- A normalized power gap is positive exactly above the logarithmic exponent threshold. -/
theorem normalized_pow_gap_pos_iff {b x : ℝ} (hb : 1 < b) (hx : 0 < x) (i : ℕ) :
    0 < (b ^ i - 1) / b ^ i - (x - 1) / x ↔ log x / log b < (i : ℝ) := by
  rw [sub_one_div_sub_one_div_pos_iff (pow_pos (by linarith : 0 < b) i) hx,
    lt_pow_iff_log_lt hx (by linarith : 0 < b), div_lt_iff₀ (log_pos hb)]
end Real
