import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-!
# Finite factorial series estimates

Explicit bounds for finite exponential-series sections, including shifted tails. The proofs
reuse Mathlib's factorial tail bound and require no differentiability assumptions. These are
the elementary series estimates used in high-order Taylor-model complexity arguments.
-/

namespace Real

/-- The positive-degree part of a finite exponential series on the unit interval is at most
twice its argument. -/
theorem sum_pos_pow_div_factorial_le {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ∑ i ∈ (Finset.range N).filter (1 ≤ ·), δ ^ i / (i.factorial : ℝ) ≤ 2 * δ := by
  have htail := Complex.sum_div_factorial_le (α := ℝ) 1 N (by omega)
  have hsum : (∑ i ∈ (Finset.range N).filter (1 ≤ ·), δ ^ i / (i.factorial : ℝ)) ≤
      δ * ∑ i ∈ (Finset.range N).filter (1 ≤ ·), 1 / (i.factorial : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hpos : i ≠ 0 := by have := (Finset.mem_filter.mp hi).2; omega
    simpa only [mul_one_div] using
      div_le_div_of_nonneg_right (pow_le_of_le_one hδ.1 hδ.2 hpos)
        (Nat.cast_nonneg i.factorial)
  norm_num at htail
  simp only [one_div] at hsum
  have hmul := mul_le_mul_of_nonneg_left htail hδ.1
  nlinarith

/-- A finite exponential series on the unit interval is bounded by `1 + 2δ`. -/
theorem sum_pow_div_factorial_le_one_add_two_mul {δ : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, δ ^ i / (i.factorial : ℝ) ≤ 1 + 2 * δ := by
  cases N with
  | zero => simp; linarith [hδ.1]
  | succ N =>
    have h0 : 0 ∈ Finset.range (N + 1) := by simp
    have herase : ((Finset.range (N + 1)).erase 0) =
        (Finset.range (N + 1)).filter (1 ≤ ·) := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_filter]
      omega
    have heq := Finset.sum_erase_add (Finset.range (N + 1))
      (fun i => δ ^ i / (i.factorial : ℝ)) h0
    rw [herase] at heq
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at heq
    linarith [sum_pos_pow_div_factorial_le hδ (N + 1)]

/-- The tail beginning at degree `j + 1` is at most `2δ^(j+1)/j!` on the unit interval. -/
theorem sum_tail_pow_div_factorial_le {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (j N : ℕ) :
    ∑ i ∈ (Finset.range N).filter (j + 1 ≤ ·), δ ^ i / (i.factorial : ℝ) ≤
      2 * δ ^ (j + 1) / (j.factorial : ℝ) := by
  have htail := Complex.sum_div_factorial_le (α := ℝ) (j + 1) N (by omega)
  have hsum : (∑ i ∈ (Finset.range N).filter (j + 1 ≤ ·), δ ^ i / (i.factorial : ℝ)) ≤
      δ ^ (j + 1) * ∑ i ∈ (Finset.range N).filter (j + 1 ≤ ·),
        1 / (i.factorial : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_one_div] using div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one hδ.1 hδ.2 (Finset.mem_filter.mp hi).2)
      (Nat.cast_nonneg i.factorial)
  have hfactor : ((j + 1 + 1 : ℕ) : ℝ) /
        (((j + 1).factorial : ℝ) * (j + 1 : ℕ)) ≤ 2 / (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hf : (0 : ℝ) < j.factorial := by positivity
    have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    apply (div_le_div_iff₀ (mul_pos (mul_pos hj hf) hj) hf).mpr
    push_cast
    nlinarith [sq_nonneg (j : ℝ)]
  have htotal := hsum.trans (mul_le_mul_of_nonneg_left (htail.trans hfactor)
    (pow_nonneg hδ.1 (j + 1)))
  calc
    _ ≤ δ ^ (j + 1) * (2 / (j.factorial : ℝ)) := htotal
    _ = _ := by ring

/-- Above one, the positive-degree part of a finite exponential section is at most twice
the largest power appearing in that section. -/
theorem sum_pos_pow_div_factorial_le_two_mul_pow {δ : ℝ} (hδ : 1 ≤ δ) (j : ℕ) :
    ∑ i ∈ (Finset.range (j + 1)).filter (1 ≤ ·), δ ^ i / (i.factorial : ℝ) ≤ 2 * δ ^ j := by
  have htail := Complex.sum_div_factorial_le (α := ℝ) 1 (j + 1) (by omega)
  have hsum : (∑ i ∈ (Finset.range (j + 1)).filter (1 ≤ ·), δ ^ i / (i.factorial : ℝ)) ≤
      δ ^ j * ∑ i ∈ (Finset.range (j + 1)).filter (1 ≤ ·), 1 / (i.factorial : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ j := by have := (Finset.mem_filter.mp hi).1; simp at this; omega
    simpa only [mul_one_div] using div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hδ hi') (Nat.cast_nonneg i.factorial)
  norm_num at htail
  simp only [one_div] at hsum
  have := mul_le_mul_of_nonneg_left htail (pow_nonneg (zero_le_one.trans hδ) j)
  nlinarith

/-- At one, every finite exponential-series section is strictly below three. -/
theorem sum_inv_factorial_lt_three (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 / (i.factorial : ℝ)) < 3 := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) N
  simpa only [one_pow] using h.trans_lt exp_one_lt_three

end Real
