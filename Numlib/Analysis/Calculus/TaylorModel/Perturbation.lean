import Numlib.Analysis.Calculus.TaylorModel
import Numlib.Analysis.SpecialFunctions.Exp.FiniteSum
import Mathlib.Tactic

/-!
# Perturbations of finite Taylor jets

The constant coefficient cancels from model decrements. Higher derivative
tensor errors therefore control both computed decrements and, when the exact
constant is retained, computed model values. The estimates use genuine
continuous multilinear operator norms and the exact factorial normalization.
-/

open scoped BigOperators
namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Decrement of a model built from an arbitrary derivative jet. -/
noncomputable def jetDecrement (A : FormalMultilinearSeries ℝ E F) (p : ℕ) (s : E) : F :=
  ofJet A p 0 - ofJet A p s

/-- Finite model evaluation is linear in its derivative jet. -/
theorem ofJet_sub (A B : FormalMultilinearSeries ℝ E F) (p : ℕ) (s : E) :
    ofJet (A - B) p s = ofJet A p s - ofJet B p s := by
  simp only [ofJet_eq_sum, FormalMultilinearSeries.sub_apply, sub_apply,
    smul_sub, Finset.sum_sub_distrib]

/-- The jet decrement is linear in the supplied tensor data. -/
theorem jetDecrement_sub (A B : FormalMultilinearSeries ℝ E F) (p : ℕ) (s : E) :
    jetDecrement (A - B) p s = jetDecrement A p s - jetDecrement B p s := by
  simp only [jetDecrement, ofJet_sub]
  abel

/-- The constant jet cancels, leaving precisely the strictly positive orders. -/
theorem jetDecrement_eq_sum (A : FormalMultilinearSeries ℝ E F) (p : ℕ) (s : E) :
    jetDecrement A p s =
      -(∑ i ∈ Finset.range p, (((i + 1).factorial : ℝ)⁻¹) • A (i + 1) (fun _ => s)) := by
  have hzero : (fun _ : Fin 0 => (0 : E)) = (fun _ => s) := by
    funext i
    exact Fin.elim0 i
  rw [jetDecrement, ofJet_zero, ofJet_eq_sum, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, hzero]
  abel

/-- The actual jet decrement is bounded by the tensor norms of its coefficients. -/
theorem norm_jetDecrement_le (A : FormalMultilinearSeries ℝ E F) (p : ℕ) (s : E) :
    ‖jetDecrement A p s‖ ≤
      ∑ i ∈ Finset.range p, ‖A (i + 1)‖ * ‖s‖ ^ (i + 1) / (i + 1).factorial := by
  rw [jetDecrement_eq_sum, norm_neg]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (((i + 1).factorial : ℝ)⁻¹))]
  have hi := (A (i + 1)).le_opNorm (fun _ => s)
  simp only [Fin.prod_const] at hi
  convert mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ (((i + 1).factorial : ℝ)⁻¹)) using 1
  ring

/-- The exact weighted perturbation bound for two computed Taylor decrements. -/
theorem norm_jetDecrement_sub_le (A B : FormalMultilinearSeries ℝ E F) (p : ℕ) (s : E) :
    ‖jetDecrement A p s - jetDecrement B p s‖ ≤
      ∑ i ∈ Finset.range p,
        ‖A (i + 1) - B (i + 1)‖ * ‖s‖ ^ (i + 1) / (i + 1).factorial := by
  rw [← jetDecrement_sub]
  exact norm_jetDecrement_le (A - B) p s

/-- Requested tensor accuracies scaled by the actual trial length give the
uniform power remainder used by implicit dynamic accuracy methods. -/
theorem norm_jetDecrement_sub_le_power (A B : FormalMultilinearSeries ℝ E F)
    {j q : ℕ} (hjq : j ≤ q) {K : ℝ} (hK : 0 ≤ K) (s : E)
    (herr : ∀ i, 1 ≤ i → i ≤ j →
      ‖A i - B i‖ ≤ K * ‖s‖ ^ (q - i + 1)) :
    ‖jetDecrement A j s - jetDecrement B j s‖ ≤ 2 * K * ‖s‖ ^ (q + 1) := by
  have ht (i : ℕ) (hi : i ∈ Finset.range j) :
      ‖A (i + 1) - B (i + 1)‖ * ‖s‖ ^ (i + 1) / (i + 1).factorial ≤
        (K * ‖s‖ ^ (q + 1)) * (1 / ((i + 1).factorial : ℝ)) := by
    have hij : i + 1 ≤ j := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hip : i + 1 ≤ q := hij.trans hjq
    have he : q - (i + 1) + 1 + (i + 1) = q + 1 := by omega
    have hm := mul_le_mul_of_nonneg_right (herr (i + 1) (by omega) hij)
      (pow_nonneg (norm_nonneg s) (i + 1))
    rw [mul_assoc, ← pow_add, he] at hm
    convert div_le_div_of_nonneg_right hm (Nat.cast_nonneg (i + 1).factorial) using 1
    ring
  have hfact : ∑ i ∈ Finset.range j, (1 / ((i + 1).factorial : ℝ)) ≤ 2 := by
    have he : (∑ i ∈ Finset.range j, (1 / ((i + 1).factorial : ℝ))) =
        ∑ i ∈ Finset.Icc 1 j, (1 / (i.factorial : ℝ)) := by
      have hi : Finset.Icc 1 j = Finset.Ico 1 (j + 1) := by ext i; simp
      rw [hi, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, add_comm 1]
    rw [he]
    simpa using Real.sum_Icc_inv_factorial_le 1 j (by norm_num)
  calc _ ≤ ∑ i ∈ Finset.range j,
        ‖A (i + 1) - B (i + 1)‖ * ‖s‖ ^ (i + 1) / (i + 1).factorial :=
      norm_jetDecrement_sub_le A B j s
    _ ≤ ∑ i ∈ Finset.range j,
        (K * ‖s‖ ^ (q + 1)) * (1 / ((i + 1).factorial : ℝ)) := Finset.sum_le_sum ht
    _ = (K * ‖s‖ ^ (q + 1)) * ∑ i ∈ Finset.range j,
        (1 / ((i + 1).factorial : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (K * ‖s‖ ^ (q + 1)) * 2 :=
      mul_le_mul_of_nonneg_left hfact (by positivity)
    _ = _ := by ring

/-- Exact constant coefficients make model-value and decrement errors identical. -/
theorem norm_ofJet_sub_eq_norm_jetDecrement_sub (A B : FormalMultilinearSeries ℝ E F)
    (hzero : A 0 (fun _ => 0) = B 0 (fun _ => 0)) (p : ℕ) (s : E) :
    ‖ofJet A p s - ofJet B p s‖ = ‖jetDecrement A p s - jetDecrement B p s‖ := by
  have he : jetDecrement A p s - jetDecrement B p s = -(ofJet A p s - ofJet B p s) := by
    simp only [jetDecrement, ofJet_zero, hzero]
    abel
  rw [he, norm_neg]

end TaylorModel
