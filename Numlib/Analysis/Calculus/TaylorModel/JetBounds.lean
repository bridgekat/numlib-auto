import Numlib.Analysis.Calculus.TaylorModel.Smooth
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Numlib.Analysis.SpecialFunctions.Exp.FiniteSum
import Mathlib.Tactic
/-!
# Actual derivative bounds for arbitrary finite tensor jets

The diagonal chain rule and Mathlib's continuous multilinear derivative bound
supply the exact falling-factorial coefficient. Summing these bounds gives the
usual shifted-factorial tail estimate for the genuine derivatives of a tensor
jet polynomial, without symmetry or compatibility assumptions on its tensors.
Uniform coefficient bounds then give a factor-three bound on the unit ball.
-/

namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The true derivative of a diagonal multilinear map obeys the exact
falling-factorial operator bound, including derivative orders above its degree. -/
theorem norm_iteratedFDeriv_diagonal_le {i n : ℕ} (A : E [×i]→L[ℝ] F) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y : E => A (fun _ => y)) x‖ ≤
      Nat.descFactorial i n * ‖A‖ * ‖x‖ ^ (i - n) := by
  let D : E →L[ℝ] (Fin i → E) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ E
  have hDx (x : E) : ‖D x‖ ≤ ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro a
    exact le_rfl
  have hD : ‖D‖ ≤ 1 := D.opNorm_le_bound zero_le_one (fun x => by simpa using hDx x)
  have he := ContinuousLinearMap.iteratedFDeriv_comp_right D A.contDiff x (n := n) le_rfl
  change ‖iteratedFDeriv ℝ n (A ∘ D) x‖ ≤ _
  rw [he]
  calc _ ≤ ‖iteratedFDeriv ℝ n A (D x)‖ * ∏ _ : Fin n, ‖D‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n A (D x)‖ := by
      apply mul_le_of_le_one_right (norm_nonneg _)
      simpa using pow_le_one₀ (n := n) (norm_nonneg D) hD
    _ ≤ Nat.descFactorial i n * ‖A‖ * ‖D x‖ ^ (i - n) := by
      simpa only [Fintype.card_fin] using A.norm_iteratedFDeriv_le n (D x)
    _ ≤ _ := by gcongr; exact hDx x


/-- A finite sum of exact diagonal derivative bounds controls the actual
derivative of an arbitrary finite tensor jet. -/
theorem norm_iteratedFDeriv_ofJet_le_sum (A : FormalMultilinearSeries ℝ E F)
    (p n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (ofJet A p) x‖ ≤
      ∑ i ∈ Finset.range (p + 1),
        (Nat.descFactorial i n : ℝ) / i.factorial * ‖A i‖ * ‖x‖ ^ (i - n) := by
  have he : ofJet A p = fun y => ∑ i ∈ Finset.range (p + 1),
      ((i.factorial : ℝ)⁻¹) • A i (fun _ => y) := funext (ofJet_eq_sum A p)
  have hd (i : ℕ) : ContDiff ℝ n (fun y : E => A i (fun _ => y)) :=
    (A i).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)
  rw [he, iteratedFDeriv_fun_sum_apply
    (fun i _ => (hd i).contDiffAt.const_smul ((i.factorial : ℝ)⁻¹))]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [iteratedFDeriv_const_smul_apply' (hd i).contDiffAt, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (i.factorial : ℝ)⁻¹)]
  have hb := mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_diagonal_le (n := n) (A i) x)
    (show 0 ≤ (i.factorial : ℝ)⁻¹ by positivity)
  convert hb using 1; ring

/-- The actual jet derivative has the usual factorial-normalized tail bound,
independently of whether the supplied tensors come from any underlying map. -/
theorem norm_iteratedFDeriv_ofJet_le_Icc (A : FormalMultilinearSeries ℝ E F)
    (p n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (ofJet A p) x‖ ≤
      ∑ i ∈ Finset.Icc n p, ‖A i‖ * ‖x‖ ^ (i - n) / (i - n).factorial := by
  classical
  apply (norm_iteratedFDeriv_ofJet_le_sum A p n x).trans
  rw [← Finset.sum_filter_ne_zero]
  calc
    _ ≤ ∑ i ∈ (Finset.range (p + 1)).filter (fun i => n ≤ i),
        (Nat.descFactorial i n : ℝ) / i.factorial * ‖A i‖ * ‖x‖ ^ (i - n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        obtain ⟨hi, hnz⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨hi, ?_⟩
        by_contra hn
        have hz := Nat.descFactorial_eq_zero_iff_lt.mpr (lt_of_not_ge hn)
        simp only [hz, Nat.cast_zero, zero_div, zero_mul, ne_eq, not_true_eq_false] at hnz
      · intro i hi hn
        positivity
    _ = _ := by
      have hset : (Finset.range (p + 1)).filter (fun i => n ≤ i) = Finset.Icc n p := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        omega
      rw [hset]
      apply Finset.sum_congr rfl
      intro i hi
      have hin := (Finset.mem_Icc.mp hi).1
      have hf := congrArg (fun k : ℕ => (k : ℝ)) (Nat.factorial_mul_descFactorial hin)
      simp only [Nat.cast_mul] at hf
      have hfac : (i.factorial : ℝ) ≠ 0 := by positivity
      have hfac' : ((i - n).factorial : ℝ) ≠ 0 := by positivity
      field_simp
      linear_combination (‖A i‖ * ‖x‖ ^ (i - n)) * hf


/-- Uniform supplied tensor norms bound every requested actual derivative by
three times that coefficient bound on the unit ball. -/
theorem norm_iteratedFDeriv_ofJet_le_three_mul (A : FormalMultilinearSeries ℝ E F)
    {p n : ℕ} (hnp : n ≤ p) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i, n ≤ i → i ≤ p → ‖A i‖ ≤ B) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ n (ofJet A p) x‖ ≤ 3 * B := by
  calc _ ≤ ∑ i ∈ Finset.Icc n p, ‖A i‖ * ‖x‖ ^ (i - n) / (i - n).factorial :=
        norm_iteratedFDeriv_ofJet_le_Icc A p n x
    _ ≤ ∑ i ∈ Finset.Icc n p, B * (‖x‖ ^ (i - n) / (i - n).factorial) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hA i (Finset.mem_Icc.mp hi).1
          (Finset.mem_Icc.mp hi).2) (pow_nonneg (norm_nonneg x) _)) (Nat.cast_nonneg _)
    _ = B * ∑ i ∈ Finset.Icc n p, ‖x‖ ^ (i - n) / (i - n).factorial := by
      rw [Finset.mul_sum]
    _ ≤ B * (1 + 2 * ‖x‖) :=
      mul_le_mul_of_nonneg_left
        (Real.sum_Icc_shift_pow_div_factorial_le (norm_nonneg x) hx hnp) hB
    _ ≤ 3 * B := by nlinarith

end TaylorModel
