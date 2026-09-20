/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.MeanInequalitiesPow` for the power-sum inequality and
`Mathlib.Analysis.SpecialFunctions.Pow.Real` for the elementary bound.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Two elementary inequalities for real powers

* `Real.sum_rpow_le_card_rpow_mul_sum`: `(∑ᵢ aᵢ)^r ≤ n^r ∑ᵢ aᵢ^r` for nonnegative `aᵢ`, `n` the
  number of terms and `r ≥ 1` — the convexity of `t ↦ t^r` with uniform weights
  (`Real.rpow_arith_mean_le_arith_mean_rpow`), the crude form of the comparison between the
  `ℓ^1` and the `ℓ^r` norms that the `p`-Laplacian energy and the `W^{1,p}` gradient norms use.
* `Real.one_add_rpow_le`: `(1 + t)^r ≤ 2^r (1 + t^r)` for `t ≥ 0`, `r ≥ 0`.
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
  have hpos : 0 < (s.card : ℝ) ^ r := by positivity
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

end Real
