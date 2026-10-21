import Numlib.Analysis.Calculus.NormPowerBounds
import Numlib.Optimization.HigherOrderDerivativeFamilyBounds

/-!
# Sharp smoothness bounds for regularized Taylor models

The actual factorial-normalized norm regularizer preserves the exact top-jet Lipschitz
constant and contributes at most its parameter to every model derivative on the unit ball.
-/

open scoped Nat
noncomputable section
namespace Optimization

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {p j : ℕ} {x : E}

/-- The highest Taylor-model derivative is the objective derivative at the expansion point. -/
theorem RegularizedTaylorModel.iteratedFDeriv_taylorModel_top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} {p : ℕ} {x : F}
    (hf : ContDiffAt ℝ p f x) (s : F) :
    iteratedFDeriv ℝ p (taylorModel f p x) s = iteratedFDeriv ℝ p f x := by
  classical
  ext v
  rw [iteratedFDeriv_taylorModel_contraction hf]
  rw [Finset.sum_eq_single p]
  · simp only [le_refl, dite_eq_left, Nat.sub_self, Nat.factorial_zero, Nat.cast_one,
      inv_one, one_smul]
    congr 1
    funext l
    simp only [l.isLt, dite_eq_left]
  · intro k hk hkp
    have hn : ¬p ≤ k := by have := Finset.mem_range.mp hk; omega
    rw [dite_eq_right hn]
  · intro hp
    exact (hp (Finset.mem_range.mpr (Nat.lt_succ_self p))).elim

/-- Actual derivatives of the regularized model split into Taylor and radial derivatives. -/
theorem HigherOrderRegularization.iteratedFDeriv_model_of_le (hj : j ≤ p) (f : E → ℝ)
    (x s : E) (σ : ℝ) :
    iteratedFDeriv ℝ j (model f p x σ) s =
      iteratedFDeriv ℝ j (RegularizedTaylorModel.taylorModel f p x) s +
      (σ / ((p + 1)! : ℝ)) • iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s := by
  have hn : ContDiff ℝ j (fun z : E => ‖z‖ ^ (p + 1)) := by
    simpa only [Real.rpow_natCast] using contDiff_norm_rpow_of_lt (E := E)
      (n := j) (r := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast (by omega : j < p + 1))
  change iteratedFDeriv ℝ j (RegularizedTaylorModel.taylorModel f p x +
    (fun z : E => (σ / ((p + 1)! : ℝ)) • ‖z‖ ^ (p + 1))) s = _
  rw [iteratedFDeriv_add_apply
    (RegularizedTaylorModel.contDiff_taylorModel f p x j).contDiffAt
    (hn.const_smul _).contDiffAt, iteratedFDeriv_const_smul_apply' hn.contDiffAt]

/-- The actual regularized Taylor model has exactly the parameter as a top-jet
Lipschitz bound. -/
theorem HigherOrderRegularization.diagonalLipschitz_model (hf : ContDiffAt ℝ p f x)
    {σ : ℝ} (hσ : 0 ≤ σ) : DiagonalLipschitz (model f p x σ) p σ := by
  apply DiagonalLipschitz.of_operator
  · have hn : ContDiff ℝ p (fun z : E => ‖z‖ ^ (p + 1)) := by
      simpa only [Real.rpow_natCast] using contDiff_norm_rpow_of_lt (E := E)
        (n := p) (r := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast Nat.lt_succ_self p)
    exact (RegularizedTaylorModel.contDiff_taylorModel f p x p).add (contDiff_const.mul hn)
  · exact hσ
  · intro s t
    rw [iteratedFDeriv_model_of_le le_rfl, iteratedFDeriv_model_of_le le_rfl,
      RegularizedTaylorModel.iteratedFDeriv_taylorModel_top hf,
      RegularizedTaylorModel.iteratedFDeriv_taylorModel_top hf,
      add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hσ (by positivity))]
    calc
      _ ≤ (σ / ((p + 1)! : ℝ)) * (((p + 1)! : ℝ) * ‖s - t‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_iteratedFDeriv_norm_pow_le p s t)
          (div_nonneg hσ (by positivity))
      _ = _ := by field_simp

/-- On the unit ball the model derivatives above the gradient are bounded by the
objective family's common coefficient bound plus the regularization parameter. -/
theorem HigherOrderDerivativeFamily.norm_iteratedFDeriv_model_le
    {L : ℕ → ℝ} (hf : HigherOrderDerivativeFamily f p L) (hj : 2 ≤ j) (hjp : j ≤ p)
    (x s : E) {σ : ℝ} (hσ : 0 ≤ σ) (hs : ‖s‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (HigherOrderRegularization.model f p x σ) s‖ ≤
      3 * maxConstant p L + σ := by
  have hfac : Nat.descFactorial (p + 1) j ≤ (p + 1)! := by
    calc
      _ = 1 * Nat.descFactorial (p + 1) j := by omega
      _ ≤ (p + 1 - j)! * Nat.descFactorial (p + 1) j :=
        Nat.mul_le_mul_right _ (Nat.factorial_pos _)
      _ = _ := Nat.factorial_mul_descFactorial (by omega)
  have hr : ‖iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s‖ ≤ ((p + 1)! : ℝ) := by
    apply (norm_iteratedFDeriv_norm_pow_le_of_le hjp s).trans
    calc
      _ ≤ (Nat.descFactorial (p + 1) j : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg s) hs) (by positivity)
      _ ≤ _ := by simpa only [mul_one] using (show
        (Nat.descFactorial (p + 1) j : ℝ) ≤ ((p + 1)! : ℝ) by exact_mod_cast hfac)
  rw [HigherOrderRegularization.iteratedFDeriv_model_of_le hjp]
  apply (norm_add_le _ _).trans
  apply add_le_add (hf.norm_iteratedFDeriv_taylorModel_le hj hjp x s hs)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hσ (by positivity))]
  calc
    _ ≤ (σ / ((p + 1)! : ℝ)) * ((p + 1)! : ℝ) :=
      mul_le_mul_of_nonneg_left hr (div_nonneg hσ (by positivity))
    _ = σ := by field_simp

end Optimization
