import Mathlib.Analysis.Real.Sqrt

/-!
# A lower bound for `-b + √(b² + a c)`

For `a, c ≥ 0` (and any `b`), `(-b + √(b² + a)) min(1, c) ≤ -b + √(b² + a c)`
(`neg_add_sqrt_sq_add_mul_ge`; [cartis2022evaluation] Lemma B.3.1, after Royer–Wright). It turns a
quadratic inequality `σ t² + b' t ≥ a' c` on a step length `t` into an explicit lower bound on `t`.
The quantity `-b + √(b² + a)` is also `a / (b + √(b² + a))` (`neg_add_sqrt_sq_add_eq_div`).
-/

/-- Rationalization: `-b + √(b² + a) = a / (b + √(b² + a))` for `a, b ≥ 0`. -/
theorem neg_add_sqrt_sq_add_eq_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    -b + √(b ^ 2 + a) = a / (b + √(b ^ 2 + a)) := by
  have hs : √(b ^ 2 + a) ^ 2 = b ^ 2 + a := Real.sq_sqrt (by positivity)
  rcases eq_or_lt_of_le (add_nonneg hb (Real.sqrt_nonneg (b ^ 2 + a))) with h | h
  · have hb0 : b = 0 := by linarith [Real.sqrt_nonneg (b ^ 2 + a)]
    have hr0 : √(b ^ 2 + a) = 0 := by linarith
    have ha0 : a = 0 := by nlinarith
    simp [hb0, ha0]
  · rw [eq_div_iff h.ne']
    nlinarith

/-- **Lemma B.3.1 of [cartis2022evaluation].** For `a, c ≥ 0` and any `b`,
`(-b + √(b² + a)) min(1, c) ≤ -b + √(b² + a c)`. (The book assumes `a, b > 0`; the sign of `b`
plays no role.) -/
theorem neg_add_sqrt_sq_add_mul_ge {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (-b + √(b ^ 2 + a)) * min 1 c ≤ -b + √(b ^ 2 + a * c) := by
  set r := -b + √(b ^ 2 + a) with hr
  have hs : √(b ^ 2 + a) ^ 2 = b ^ 2 + a := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := by
    have : b ≤ √(b ^ 2 + a) := Real.le_sqrt_of_sq_le (by linarith)
    linarith
  have har : a = r ^ 2 + 2 * b * r := by rw [hr]; nlinarith
  rcases le_total c 1 with hc1 | hc1
  · rw [min_eq_right hc1]
    have key : (b + r * c) ^ 2 ≤ b ^ 2 + a * c := by
      rw [har]; nlinarith [mul_nonneg (mul_nonneg hr0 hr0) (mul_nonneg hc (sub_nonneg.2 hc1))]
    have := Real.le_sqrt_of_sq_le key
    linarith
  · rw [min_eq_left hc1, mul_one]
    have : √(b ^ 2 + a) ≤ √(b ^ 2 + a * c) :=
      Real.sqrt_le_sqrt (by nlinarith)
    linarith
