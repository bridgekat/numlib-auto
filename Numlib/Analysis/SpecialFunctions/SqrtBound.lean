import Mathlib.Analysis.Real.Sqrt

/-!
# A lower bound for `-b + √(b² + a c)`

For `a, c ≥ 0` (and any `b`), `(-b + √(b² + a)) min(1, c) ≤ -b + √(b² + a c)`
(`neg_add_sqrt_sq_add_mul_ge`; [cartis2022evaluation] Lemma B.3.1, after Royer–Wright). It turns a
quadratic inequality `σ t² + b' t ≥ a' c` on a step length `t` into an explicit lower bound on `t`.
The quantity `-b + √(b² + a)` is also `a / (b + √(b² + a))` (`neg_add_sqrt_sq_add_eq_div`).
A cruder explicit form: `0 ≤ G ≤ a t² + ε t` gives `t ≥ min(ε, G/ε)/√(1 + 4a)`
(`le_of_le_quadratic`).
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
`(-b + √(b² + a)) min(1, c) ≤ -b + √(b² + a c)`. (The sign of `b` plays no role.) -/
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

/-- **Step length from a quadratic inequality** (the real inequality behind Lemma 3.4.3 of
[cartis2022evaluation]): if `0 ≤ G ≤ a t² + ε t` with `a ≥ 0`, `ε > 0`, `t ≥ 0`,
then `t ≥ min(ε, G/ε)/√(1 + 4a)`. -/
theorem le_of_le_quadratic {a ε t G : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (ht : 0 ≤ t) (hG : 0 ≤ G)
    (h : G ≤ a * t ^ 2 + ε * t) : 1 / √(1 + 4 * a) * min ε (G / ε) ≤ t := by
  set u := √(1 + 4 * a) with hu
  have hu2 : u ^ 2 = 1 + 4 * a := Real.sq_sqrt (by linarith)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : 1 ≤ u := by nlinarith
  have hu3 : u ≤ 1 + 3 * a := by nlinarith
  set M := min ε (G / ε)
  have hM1 : M ≤ ε := min_le_left _ _
  have hM2 : ε * M ≤ G := by
    have := min_le_right ε (G / ε)
    rw [le_div_iff₀ hε] at this
    linarith
  have hM0 : 0 ≤ M := le_min hε.le (div_nonneg hG hε.le)
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by linarith)]
  by_contra hlt
  push Not at hlt
  have h1 : u ^ 2 * G ≤ a * (u * t) ^ 2 + ε * u * (u * t) := by
    have := mul_le_mul_of_nonneg_left h (sq_nonneg u)
    nlinarith
  have hut : 0 ≤ u * t := mul_nonneg hu0 ht
  have h2 : a * (u * t) ^ 2 ≤ a * M ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hut (by linarith) 2) ha
  have h3 : ε * u * (u * t) < ε * u * M := mul_lt_mul_of_pos_left (by linarith) (by positivity)
  have h4 : M ^ 2 ≤ ε * M := by nlinarith
  have h5 : a * M ^ 2 + ε * u * M ≤ (a + u) * G := by nlinarith
  have h6 : (a + u) * G ≤ u ^ 2 * G := mul_le_mul_of_nonneg_right (by nlinarith) hG
  linarith
