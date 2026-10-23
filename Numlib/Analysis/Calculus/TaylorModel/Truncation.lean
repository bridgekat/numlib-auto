import Numlib.Analysis.Calculus.TaylorModel.Perturbation

/-!
# Truncation of finite derivative jets

Higher homogeneous terms bound the difference between two truncations of the
same actual or approximate derivative jet. The unit-ball bound retains the
factorial of the last retained order.
-/

open scoped BigOperators
namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Truncating a finite jet removes exactly its higher homogeneous terms. -/
theorem ofJet_sub_ofJet_eq_sum (A : FormalMultilinearSeries ℝ E F)
    {j p : ℕ} (hjp : j ≤ p) (s : E) :
    ofJet A p s - ofJet A j s =
      ∑ i ∈ Finset.Icc (j + 1) p, ((i.factorial : ℝ)⁻¹) • A i (fun _ => s) := by
  rw [ofJet_eq_sum, ofJet_eq_sum]
  have he : Finset.Icc (j + 1) p = Finset.Ico (j + 1) (p + 1) := by ext i; simp
  rw [he, Finset.sum_Ico_eq_sub _ (by omega)]

/-- Bounded derivative tensors control the true truncation error on the unit ball. -/
theorem norm_ofJet_sub_ofJet_le (A : FormalMultilinearSeries ℝ E F)
    {j p : ℕ} (hj : 0 < j) (hjp : j ≤ p) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ a, j < a → a ≤ p → ‖A a‖ ≤ B) (s : E) (hs : ‖s‖ ≤ 1) :
    ‖ofJet A p s - ofJet A j s‖ ≤ B * ‖s‖ ^ (j + 1) / j.factorial := by
  rw [ofJet_sub_ofJet_eq_sum A hjp s]
  calc _ ≤ ∑ i ∈ Finset.Icc (j + 1) p,
        ‖((i.factorial : ℝ)⁻¹) • A i (fun _ => s)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Icc (j + 1) p, B * (‖s‖ ^ i / i.factorial) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ((i.factorial : ℝ)⁻¹))]
      have hnorm := (A i).le_opNorm (fun _ => s)
      simp only [Fin.prod_const] at hnorm
      have hb := mul_le_mul_of_nonneg_right (hA i (by have := (Finset.mem_Icc.mp hi).1; omega)
        (Finset.mem_Icc.mp hi).2) (pow_nonneg (norm_nonneg s) i)
      convert mul_le_mul_of_nonneg_left (hnorm.trans hb)
        (by positivity : 0 ≤ ((i.factorial : ℝ)⁻¹)) using 1; ring
    _ = B * ∑ i ∈ Finset.Icc (j + 1) p, ‖s‖ ^ i / i.factorial :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ B * (‖s‖ ^ (j + 1) / j.factorial) :=
      mul_le_mul_of_nonneg_left
        (Real.sum_Icc_pow_div_factorial_le_tail_of_pos (norm_nonneg s) hs hj p) hB
    _ = _ := by ring
end TaylorModel
