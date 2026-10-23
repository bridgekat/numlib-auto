import Numlib.Analysis.Calculus.TaylorModel.Perturbation
import Numlib.Analysis.Calculus.TaylorModel.JetBounds

/-!
# Actual derivatives of perturbed finite tensor polynomials

Differentiating the actual polynomial difference gives the exact weighted
coefficient-error tail. Relative tensor errors with the trial-length powers
therefore yield a single common power at every positive derivative order.
-/

namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual iterated derivatives preserve the difference of finite tensor polynomials. -/
theorem iteratedFDeriv_ofJet_sub (A B : FormalMultilinearSeries ℝ E F) (p n : ℕ) (s : E) :
    iteratedFDeriv ℝ n (ofJet (A - B) p) s =
      iteratedFDeriv ℝ n (ofJet A p) s - iteratedFDeriv ℝ n (ofJet B p) s := by
  have he : ofJet (A - B) p = fun z => ofJet A p z - ofJet B p z :=
    funext (ofJet_sub A B p)
  rw [he]
  exact iteratedFDeriv_sub_apply (contDiff_ofJet A p n).contDiffAt
    (contDiff_ofJet B p n).contDiffAt

/-- The exact weighted coefficient-error tail bounds actual polynomial derivative errors. -/
theorem norm_iteratedFDeriv_ofJet_sub_le_Icc (A B : FormalMultilinearSeries ℝ E F)
    (p n : ℕ) (s : E) :
    ‖iteratedFDeriv ℝ n (ofJet A p) s - iteratedFDeriv ℝ n (ofJet B p) s‖ ≤
      ∑ i ∈ Finset.Icc n p, ‖A i - B i‖ * ‖s‖ ^ (i - n) / (i - n).factorial := by
  rw [← iteratedFDeriv_ofJet_sub]
  exact norm_iteratedFDeriv_ofJet_le_Icc (A - B) p n s

/-- Actual relative tensor errors give the exact trial-length power in every
positive polynomial derivative; no derivative identity is assumed. -/
theorem norm_iteratedFDeriv_ofJet_sub_le_power (A B : FormalMultilinearSeries ℝ E F)
    {p n : ℕ} (hn : 1 ≤ n) (hnp : n ≤ p) {K : ℝ} (hK : 0 ≤ K) (s : E)
    (herr : ∀ i, 1 ≤ i → i ≤ p → ‖A i - B i‖ ≤ K * ‖s‖ ^ (p - i + 1)) :
    ‖iteratedFDeriv ℝ n (ofJet A p) s - iteratedFDeriv ℝ n (ofJet B p) s‖ ≤
      3 * K * ‖s‖ ^ (p - n + 1) := by
  classical
  let C := K * ‖s‖ ^ (p - n + 1)
  have hC : 0 ≤ C := mul_nonneg hK (pow_nonneg (norm_nonneg _) _)
  calc _ ≤ ∑ i ∈ Finset.Icc n p, ‖A i - B i‖ * ‖s‖ ^ (i - n) /
        (i - n).factorial := norm_iteratedFDeriv_ofJet_sub_le_Icc A B p n s
    _ ≤ ∑ i ∈ Finset.Icc n p, C * (1 / ((i - n).factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hni, hip⟩ := Finset.mem_Icc.mp hi
      have hpowers : p - i + 1 + (i - n) = p - n + 1 := by omega
      have hm := mul_le_mul_of_nonneg_right (herr i (hn.trans hni) hip)
        (pow_nonneg (norm_nonneg s) (i - n))
      rw [mul_assoc, ← pow_add, hpowers] at hm
      simpa only [C, mul_one_div] using
        div_le_div_of_nonneg_right hm (Nat.cast_nonneg (i - n).factorial)
    _ = C * ∑ i ∈ Finset.Icc n p, (1 / ((i - n).factorial : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * 3 := by
      have ht := Real.sum_Icc_shift_pow_div_factorial_le (x := 1) (by norm_num) le_rfl hnp
      simp only [one_pow] at ht
      exact mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by dsimp [C]; ring

end TaylorModel
