import Numlib.Analysis.SpecialFunctions.Exp.FiniteSum
import Mathlib.Tactic

/-!
# Mixed-power finite Taylor sums

The factorial-normalized mixed sum is bounded by its highest-radius term when
the step is shorter than the radius, and by its first-radius term in the
opposite case. These estimates apply to Taylor-criticality step bounds.
-/

namespace Real

/-- A finite sum of positive-order reciprocal factorials is at most two. -/
theorem sum_range_inv_succ_factorial_le_two (j : ℕ) :
    (∑ i ∈ Finset.range j, (1 : ℝ) / (i + 1).factorial) ≤ 2 := by
  have he : (∑ i ∈ Finset.range j, (1 : ℝ) / (i + 1).factorial) =
      ∑ i ∈ Finset.Icc 1 j, (1 : ℝ) / i.factorial := by
    have hi : Finset.Icc 1 j = Finset.Ico 1 (j + 1) := by ext i; simp
    rw [hi, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, add_comm 1]
  rw [he]
  simpa using sum_Icc_inv_factorial_le 1 j (by norm_num)

/-- The mixed Taylor-power sum for a step shorter than the radius is bounded
by twice its highest-radius term. -/
theorem sum_range_mixed_pow_le_two_top {p j : ℕ} (hjp : j ≤ p)
    {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hsδ : s ≤ δ) :
    (∑ i ∈ Finset.range j, δ ^ (i + 1) * s ^ (p - (i + 1) + 1) /
      (i + 1).factorial) ≤ 2 * δ ^ j * s ^ (p - j + 1) := by
  have ht : ∀ i ∈ Finset.range j,
      δ ^ (i + 1) * s ^ (p - (i + 1) + 1) ≤ δ ^ j * s ^ (p - j + 1) := by
    intro i hi
    have hij : i + 1 ≤ j := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have he : p - (i + 1) + 1 = (j - (i + 1)) + (p - j + 1) := by omega
    calc
      _ = (δ ^ (i + 1) * s ^ (j - (i + 1))) * s ^ (p - j + 1) := by
          rw [he, pow_add s]; ring
      _ ≤ (δ ^ (i + 1) * δ ^ (j - (i + 1))) * s ^ (p - j + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hs hsδ _) (pow_nonneg hδ _)) (pow_nonneg hs _)
      _ = _ := by rw [←pow_add, Nat.add_sub_of_le hij]
  calc
    _ ≤ ∑ i ∈ Finset.range j,
        (δ ^ j * s ^ (p - j + 1)) * (1 / ((i + 1).factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_one_div] using div_le_div_of_nonneg_right (ht i hi)
        (Nat.cast_nonneg (i + 1).factorial)
    _ = (δ ^ j * s ^ (p - j + 1)) *
        ∑ i ∈ Finset.range j, (1 / ((i + 1).factorial : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (δ ^ j * s ^ (p - j + 1)) * 2 := mul_le_mul_of_nonneg_left
        (sum_range_inv_succ_factorial_le_two j) (by positivity)
    _ = _ := by ring

/-- The mixed Taylor-power sum for a radius shorter than the step is bounded
by twice its first-radius term. -/
theorem sum_range_mixed_pow_le_two_first {p j : ℕ} (hjp : j ≤ p)
    {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hδs : δ ≤ s) :
    (∑ i ∈ Finset.range j, δ ^ (i + 1) * s ^ (p - (i + 1) + 1) /
      (i + 1).factorial) ≤ 2 * δ * s ^ p := by
  have ht : ∀ i ∈ Finset.range j,
      δ ^ (i + 1) * s ^ (p - (i + 1) + 1) ≤ δ * s ^ p := by
    intro i hi
    have hij : i + 1 ≤ p := (Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans hjp
    have he : i + (p - (i + 1) + 1) = p := by omega
    calc
      _ = δ * δ ^ i * s ^ (p - (i + 1) + 1) := by rw [pow_succ]; ring
      _ ≤ δ * s ^ i * s ^ (p - (i + 1) + 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ hδs _) hδ)
            (pow_nonneg hs _)
      _ = _ := by rw [mul_assoc, ←pow_add, he]
  calc
    _ ≤ ∑ i ∈ Finset.range j, (δ * s ^ p) * (1 / ((i + 1).factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_one_div] using div_le_div_of_nonneg_right (ht i hi)
        (Nat.cast_nonneg (i + 1).factorial)
    _ = (δ * s ^ p) * ∑ i ∈ Finset.range j, (1 / ((i + 1).factorial : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (δ * s ^ p) * 2 := mul_le_mul_of_nonneg_left
        (sum_range_inv_succ_factorial_le_two j) (by positivity)
    _ = _ := by ring

end Real
