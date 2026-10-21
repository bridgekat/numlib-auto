import Numlib.Analysis.SpecialFunctions.FactorialSeries

/-!
# Finite series bounds

Lemma A.10.1 and its immediate consequences, with natural interval endpoints and all empty-range
and zero-argument cases included. General finite exponential-series estimates are in the backbone.
-/

namespace CartisGouldToint.AppendixA.Section10

open scoped Nat

/-- Lemma A.10.1: the two finite factorial-series estimates. -/
theorem lemma_A_10_1 {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (j p : ℕ) (_hjp : j ≤ p) :
    (∑ ℓ ∈ Finset.Icc j p, δ ^ (ℓ - j) / ((ℓ - j).factorial : ℝ)) ≤ 1 + 2 * δ ∧
      (∑ ℓ ∈ Finset.Icc (j + 1) (p + 1), δ ^ ℓ / (ℓ.factorial : ℝ)) ≤
        2 * δ ^ (j + 1) / (j.factorial : ℝ) := by
  constructor
  · have hIcc : Finset.Icc j p = Finset.Ico j (p + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_sub_cancel_left] using
      Real.sum_pow_div_factorial_le_one_add_two_mul hδ (p + 1 - j)
  · have hIcc : Finset.Icc (j + 1) (p + 1) =
        (Finset.range (p + 2)).filter (j + 1 ≤ ·) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
      omega
    rw [hIcc]
    exact Real.sum_tail_pow_div_factorial_le hδ j (p + 2)

/-- Equations (A.34)–(A.36): positive-degree sums on either side of one and unit-argument
reciprocal factorial bounds. -/
theorem factorial_series_auxiliary_bounds (j p : ℕ) (_hjp : j ≤ p) :
    (∀ δ ∈ Set.Icc (0 : ℝ) 1,
      (∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / (ℓ.factorial : ℝ)) ≤ 2 * δ) ∧
    (∀ δ : ℝ, 1 ≤ δ →
      (∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / (ℓ.factorial : ℝ)) ≤ 2 * δ ^ j) ∧
    (∑ ℓ ∈ Finset.Icc 1 j, (1 / (ℓ.factorial : ℝ))) ≤ 2 ∧
    (∑ ℓ ∈ Finset.Icc j p, (1 / ((ℓ - j).factorial : ℝ))) < 3 ∧
    (∑ ℓ ∈ Finset.Icc (j + 1) (p + 1), (1 / (ℓ.factorial : ℝ))) ≤
      2 / (j.factorial : ℝ) := by
  have hIcc : Finset.Icc 1 j = (Finset.range (j + 1)).filter (1 ≤ ·) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  have hsmall : ∀ δ ∈ Set.Icc (0 : ℝ) 1,
      (∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / (ℓ.factorial : ℝ)) ≤ 2 * δ := by
    intro δ hδ
    rw [hIcc]
    exact Real.sum_pos_pow_div_factorial_le hδ (j + 1)
  refine ⟨hsmall, ?_, ?_, ?_, ?_⟩
  · intro δ hδ
    rw [hIcc]
    exact Real.sum_pos_pow_div_factorial_le_two_mul_pow hδ j
  · simpa only [one_pow, mul_one] using hsmall 1 (by constructor <;> norm_num)
  · have hshift : Finset.Icc j p = Finset.Ico j (p + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hshift, Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_sub_cancel_left] using Real.sum_inv_factorial_lt_three (p + 1 - j)
  · simpa only [one_pow, mul_one] using (lemma_A_10_1 (δ := 1)
      (by constructor <;> norm_num) j p _hjp).2

end CartisGouldToint.AppendixA.Section10
