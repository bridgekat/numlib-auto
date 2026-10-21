import Numlib.Optimization.HigherOrderDerivativeFamily
import Numlib.Optimization.HigherOrderRegularizationSmoothness
import Numlib.Optimization.TaylorModelDerivatives
import Numlib.Analysis.SpecialFunctions.FactorialSeries
import Mathlib.Tactic

/-!
# Bounds on derivatives of objectives and their Taylor polynomials

A Lipschitz bound on a positive-order derivative bounds the next actual derivative.
Consequently the all-orders Lipschitz family bounds all Taylor coefficients of order
at least two, and gives a uniform bound for all higher derivatives of its Taylor model.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderDerivativeFamily

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {p : ℕ} {L : ℕ → ℝ}

/-- Every derivative above the gradient is bounded by the preceding Lipschitz constant. -/
theorem norm_iteratedFDeriv_le (hf : HigherOrderDerivativeFamily f p L)
    {j : ℕ} (hj : 2 ≤ j) (hjp : j ≤ p) (x : E) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ L (j - 1) := by
  have hpos : 1 ≤ j - 1 := by omega
  have hle : j - 1 ≤ p := by omega
  have h := norm_fderiv_le_of_lip' ℝ
    (f := iteratedFDeriv ℝ (j - 1) f) (x₀ := x) (hf.nonneg (j - 1) hpos hle)
    (Filter.Eventually.of_forall (fun y => (hf.at_order hpos hle).operator_bound hpos y x))
  rw [show j = (j - 1) + 1 by omega, iteratedFDeriv_succ_eq_comp_left]
  simpa only [Function.comp_apply, LinearIsometryEquiv.norm_map, Nat.add_sub_cancel] using h

/-- The common family constant bounds every actual derivative above the gradient. -/
theorem norm_iteratedFDeriv_le_maxConstant (hf : HigherOrderDerivativeFamily f p L)
    {j : ℕ} (hj : 2 ≤ j) (hjp : j ≤ p) (x : E) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ maxConstant p L :=
  (hf.norm_iteratedFDeriv_le hj hjp x).trans (le_maxConstant L (by omega) (by omega))

/-- On the unit ball, every Taylor-model derivative above the gradient is bounded by
three times the common Lipschitz constant of the objective derivatives. -/
theorem norm_iteratedFDeriv_taylorModel_le (hf : HigherOrderDerivativeFamily f p L)
    {j : ℕ} (hj : 2 ≤ j) (hjp : j ≤ p) (x s : E) (hs : ‖s‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (RegularizedTaylorModel.taylorModel f p x) s‖ ≤
      3 * maxConstant p L := by
  classical
  have hA := hf.maxConstant_nonneg
  have hsm : ContDiffAt ℝ j (RegularizedTaylorModel.taylorModel f p x) s :=
    (RegularizedTaylorModel.contDiff_taylorModel f p x j).contDiffAt
  rw [← hsm.diagonalNorm_iteratedFDeriv_eq_norm (by omega : 0 < j)]
  apply ContinuousMultilinearMap.diagonalNorm_le _ (by positivity)
  intro v hv
  change ‖iteratedFDeriv ℝ j (RegularizedTaylorModel.taylorModel f p x) s (fun _ => v)‖ ≤ _
  rw [RegularizedTaylorModel.iteratedFDeriv_taylorModel_contraction hf.smooth.contDiffAt]
  have hterm : ∀ k ∈ Finset.range (p + 1),
      ‖(if _h : j ≤ k then ((k - j)! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x
        (fun l => if h : (l : ℕ) < j then v else s) else 0)‖ ≤
      if j ≤ k then maxConstant p L / ((k - j)! : ℝ) else 0 := by
    intro k hk
    by_cases hjk : j ≤ k
    · simp only [dite_eq_left hjk, ite_eq_left hjk, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_nonneg (show (0 : ℝ) ≤ ((k - j)! : ℝ) by positivity)]
      have hb : ‖iteratedFDeriv ℝ k f x
          (fun l : Fin k => if (l : ℕ) < j then v else s)‖ ≤ maxConstant p L := by
        have ht := (iteratedFDeriv ℝ k f x).le_opNorm_mul_prod_of_le
          (b := fun _ => (1 : ℝ)) (m := fun l => if (l : ℕ) < j then v else s) (by
            intro l
            split_ifs <;> simp_all)
        simp only [Finset.prod_const_one, mul_one] at ht
        exact ht.trans (hf.norm_iteratedFDeriv_le_maxConstant (by omega) (by
          have := Finset.mem_range.mp hk; omega) x)
      simpa only [div_eq_inv_mul, Real.norm_eq_abs, dite_eq_ite] using
        mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ ((k - j)! : ℝ)⁻¹)
    · simp [hjk]
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have heq : (∑ k ∈ Finset.range (p + 1),
      if j ≤ k then maxConstant p L / ((k - j)! : ℝ) else 0) =
      maxConstant p L * ∑ k ∈ Finset.range (p + 1 - j), 1 / (k ! : ℝ) := by
    rw [Finset.mul_sum]
    have hr : p + 1 = j + (p + 1 - j) := by omega
    rw [hr, Finset.sum_range_add]
    have hz : (∑ k ∈ Finset.range j,
        if j ≤ k then maxConstant p L / ((k - j)! : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [show ¬j ≤ k by have := Finset.mem_range.mp hk; omega]
    rw [hz, zero_add, Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro k _
    simp [div_eq_mul_inv]
  rw [heq] at hsum
  have hb := mul_le_mul_of_nonneg_left
    (Real.sum_inv_factorial_lt_three (p + 1 - j)).le hA
  exact hsum.trans (by nlinarith only [hb])

end Optimization.HigherOrderDerivativeFamily
