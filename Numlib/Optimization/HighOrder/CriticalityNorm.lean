import Numlib.Optimization.HighOrder.Criticality
import Numlib.Analysis.Calculus.TaylorModel.Scalar

/-!
# Scalar Taylor criticality from actual derivative bounds

Finite sums bound the genuine closed-ball supremum using the actual scalar jets.
-/

namespace TaylorModel
/-- A common bound on the actual positive scalar jets bounds the unit-ball Taylor supremum. -/
theorem criticality_unit_le_of_scalar_jets (f : ℝ → ℝ) (j : ℕ) (x : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (hj : ∀ a, 1 ≤ a → a ≤ j → |iteratedDeriv a f x| ≤ H) :
    criticality f j x 1 ≤ j * H := by
  obtain ⟨u, hu, heq⟩ := exists_decrement_eq_criticality f j x (by norm_num : (0 : ℝ) ≤ 1)
  rw [← heq, decrement_eq, eval_eq_sum_iteratedDeriv, Finset.sum_range_succ']
  simp only [pow_zero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul,
    div_one]
  have he : f x - ((∑ a ∈ Finset.range j,
      u ^ (a + 1) * iteratedDeriv (a + 1) f x / ((a + 1).factorial : ℝ)) + f x) =
      -(∑ a ∈ Finset.range j,
      u ^ (a + 1) * iteratedDeriv (a + 1) f x / ((a + 1).factorial : ℝ)) := by ring
  rw [he]
  apply (le_abs_self _).trans
  rw [abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _a ∈ Finset.range j, H := by
         apply Finset.sum_le_sum
         intro a ha
         rw [abs_div, abs_mul, abs_pow]
         rw [show |((a + 1).factorial : ℝ)| = (a + 1).factorial from
           abs_of_nonneg (Nat.cast_nonneg _)]
         have hu1 : |u| ^ (a + 1) ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
         have hh := hj (a + 1) (by omega) (Finset.mem_range.mp ha)
         have hf : (1 : ℝ) ≤ (a + 1).factorial := by exact_mod_cast Nat.factorial_pos _
         exact (div_le_div_of_nonneg_right
           ((mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)).trans (by simpa using hh))
           (Nat.cast_nonneg _)).trans (div_le_self hH hf)
       _ = _ := by simp
end TaylorModel
