/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.MeanInequalitiesPow` for the power-sum inequality and
`Mathlib.Analysis.SpecialFunctions.Pow.Real` for the elementary bound.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Two elementary inequalities for real powers

* `Real.sum_rpow_le_card_rpow_mul_sum`: `(∑ᵢ aᵢ)^r ≤ n^r ∑ᵢ aᵢ^r` for nonnegative `aᵢ`, `n` the
  number of terms and `r ≥ 1` — the convexity of `t ↦ t^r` with uniform weights
  (`Real.rpow_arith_mean_le_arith_mean_rpow`), the crude form of the comparison between the
  `ℓ^1` and the `ℓ^r` norms that the `p`-Laplacian energy and the `W^{1,p}` gradient norms use.
* `Real.one_add_rpow_le`: `(1 + t)^r ≤ 2^r (1 + t^r)` for `t ≥ 0`, `r ≥ 0`.
* `Real.summable_mul_of_summable_sq`: the product of two square-summable real families is
  summable, by `|a b| ≤ (a² + b²) / 2`.
* `Real.rpow_le_tangent`: for `0 ≤ α ≤ 1` the concave power `u ↦ u ^ α` lies below its tangent
  line at `s > 0`, `u ^ α ≤ α s ^ (α - 1) u + (1 - α) s ^ α` (weighted AM–GM).
-/

namespace Real

/-- `(∑ᵢ aᵢ)^p ≤ n^p ∑ᵢ aᵢ^p` for nonnegative `aᵢ`, `n = card s` and `p ≥ 1` (the convexity of
`t ↦ t^p`, `Real.rpow_arith_mean_le_arith_mean_rpow`, with the uniform weights). -/
theorem sum_rpow_le_card_rpow_mul_sum {ι : Type*} (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i ∈ s, a i) ^ r ≤ (s.card : ℝ) ^ r * ∑ i ∈ s, a i ^ r := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    simp [Real.zero_rpow (zero_lt_one.trans_le hr).ne']
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow (s := s) (fun _ ↦ (s.card : ℝ)⁻¹) a
    (fun _ _ ↦ by positivity) (by simp [Finset.sum_const, hn.ne']) ha hr
  have hsum : ∑ i ∈ s, (s.card : ℝ)⁻¹ * a i = (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i := by
    rw [Finset.mul_sum]
  have hsum' : ∑ i ∈ s, (s.card : ℝ)⁻¹ * a i ^ r = (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i ^ r := by
    rw [Finset.mul_sum]
  rw [hsum, hsum', Real.mul_rpow (by positivity) (Finset.sum_nonneg ha),
    Real.inv_rpow hn.le] at hmean
  have hle : (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i ^ r ≤ ∑ i ∈ s, a i ^ r := by
    have h1 : (s.card : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hs.card_pos)
    have h2 : 0 ≤ ∑ i ∈ s, a i ^ r := Finset.sum_nonneg fun i hi ↦ Real.rpow_nonneg (ha i hi) r
    nlinarith
  calc (∑ i ∈ s, a i) ^ r
      = (s.card : ℝ) ^ r * (((s.card : ℝ) ^ r)⁻¹ * (∑ i ∈ s, a i) ^ r) := by
        field_simp
    _ ≤ (s.card : ℝ) ^ r * ∑ i ∈ s, a i ^ r := by
        gcongr
        exact hmean.trans hle

/-- The elementary bound `(1 + t)^p ≤ 2^p (1 + t^p)` for `t ≥ 0`, `p ≥ 0`. -/
theorem one_add_rpow_le {t p : ℝ} (ht : 0 ≤ t) (hp : 0 ≤ p) :
    (1 + t) ^ p ≤ 2 ^ p * (1 + t ^ p) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    have := le_max_left 1 t
    have := le_max_right 1 t
    linarith
  calc (1 + t) ^ p ≤ (2 * max 1 t) ^ p := Real.rpow_le_rpow (by positivity) h1 hp
    _ = 2 ^ p * (max 1 t) ^ p := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 ^ p * (1 + t ^ p) := by
      gcongr
      rcases le_total 1 t with h | h
      · rw [max_eq_right h]
        linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1) p]
      · rw [max_eq_left h, Real.one_rpow]
        linarith [Real.rpow_nonneg ht p]

/-- The product of two square-summable real families is summable: `|f k g k| ≤ (f k² + g k²) / 2`
(the case `p = q = 2` of `Real.summable_mul_of_Lp_Lq_of_nonneg`, without the signs). -/
theorem summable_mul_of_summable_sq {ι : Type*} {f g : ι → ℝ} (hf : Summable fun k => f k ^ 2)
    (hg : Summable fun k => g k ^ 2) : Summable fun k => f k * g k := by
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((hf.add hg).div_const 2))
  rw [abs_mul]
  nlinarith [sq_nonneg (|f k| - |g k|), abs_nonneg (f k), abs_nonneg (g k), sq_abs (f k),
    sq_abs (g k)]

/-- The tangent line to the concave power `u ↦ u ^ α` at `u = s`: `u^α ≤ α s^{α-1} u +
(1 - α) s^α`. It is the weighted arithmetic–geometric mean inequality, and it is what replaces
Jensen's inequality in Hölder-type estimates. -/
theorem rpow_le_tangent {u s α : ℝ} (hu : 0 ≤ u) (hs : 0 < s) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : u ^ α ≤ α * s ^ (α - 1) * u + (1 - α) * s ^ α := by
  have h := Real.geom_mean_le_arith_mean2_weighted hα0 (by linarith : (0 : ℝ) ≤ 1 - α)
    (div_nonneg hu hs.le) zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one, Real.div_rpow hu hs.le] at h
  have hsα : (0 : ℝ) < s ^ α := Real.rpow_pos_of_pos hs α
  have hmul := mul_le_mul_of_nonneg_right h hsα.le
  rw [div_mul_cancel₀ _ hsα.ne'] at hmul
  refine hmul.trans_eq ?_
  rw [Real.rpow_sub hs, Real.rpow_one]
  field_simp

end Real

/-- `a^{p−1} b ≤ a^p + b^p` for `a, b ≥ 0` and `p ≥ 1` (the crude Young inequality). -/
theorem Real.rpow_sub_one_mul_le_add {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    a ^ (p - 1) * b ≤ a ^ p + b ^ p := by
  rcases le_total a b with hab | hab
  · calc a ^ (p - 1) * b ≤ b ^ (p - 1) * b :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha hab (by linarith)) hb
      _ = b ^ p := by
          rw [← Real.rpow_add_one' hb (by linarith), sub_add_cancel]
      _ ≤ a ^ p + b ^ p := le_add_of_nonneg_left (Real.rpow_nonneg ha _)
  · calc a ^ (p - 1) * b ≤ a ^ (p - 1) * a :=
          mul_le_mul_of_nonneg_left hab (Real.rpow_nonneg ha _)
      _ = a ^ p := by
          rw [← Real.rpow_add_one' ha (by linarith), sub_add_cancel]
      _ ≤ a ^ p + b ^ p := le_add_of_nonneg_right (Real.rpow_nonneg hb _)
