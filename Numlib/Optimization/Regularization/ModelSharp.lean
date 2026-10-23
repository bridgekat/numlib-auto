import Numlib.Optimization.Regularization.ModelBounds
import Numlib.Analysis.InnerProductSpace.NormPow.Gaussian

/-!
# Sharp derivative bounds for actual regularized tensor models

Combining the polynomial derivative tail with the single penalty term gives
one exponential tail. This proves the coefficient `3 * max D σ` directly;
replacing the looser coefficient `3 * D + σ` by that coefficient would not be
valid. All derivatives here are actual iterated Fréchet derivatives.
-/

namespace ModelDecrease
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual penalty derivative has the sharp factorial-normalized bound
at every point, including zero, for every order below its degree. -/
theorem norm_iteratedFDeriv_penalty_le {p n : ℕ} (hn : n ≤ p)
    {σ : ℝ} (hσ : 0 ≤ σ) (x : E) :
    ‖(σ / ((p + 1).factorial : ℝ)) •
        iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ (p + 1)) x‖ ≤
      σ * ‖x‖ ^ (p + 1 - n) / (p + 1 - n).factorial := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hσ (Nat.cast_nonneg _))]
  have hb := NormPower.norm_iteratedFDeriv_norm_pow_integer_le_factorial_finiteDimensional
    (show n ≤ p + 1 by omega) x (Or.inl (by omega))
  calc _ ≤ (σ / ((p + 1).factorial : ℝ)) *
        (((p + 1).factorial : ℝ) / (p + 1 - n).factorial * ‖x‖ ^ (p + 1 - n)) :=
          mul_le_mul_of_nonneg_left hb (div_nonneg hσ (Nat.cast_nonneg _))
    _ = _ := by field_simp

/-- The polynomial and penalty derivatives fit one common factorial tail,
with coefficient equal to the maximum of the tensor and penalty bounds. -/
theorem norm_iteratedFDeriv_penalized_ofJet_le_tail
    (A : FormalMultilinearSeries ℝ E ℝ) {p n : ℕ} (hn : n ≤ p)
    {σ D : ℝ} (hσ : 0 ≤ σ)
    (hA : ∀ i, n ≤ i → i ≤ p → ‖A i‖ ≤ D) (x : E) :
    ‖iteratedFDeriv ℝ n (penalized (TaylorModel.ofJet A p) p σ) x‖ ≤
      max D σ * ∑ i ∈ Finset.Icc n (p + 1),
        ‖x‖ ^ (i - n) / (i - n).factorial := by
  classical
  let H := max D σ
  have hHσ : σ ≤ H := le_max_right _ _
  rw [iteratedFDeriv_penalized_ofJet_eq A p n hn σ x]
  apply (norm_add_le _ _).trans
  have hpoly : ‖iteratedFDeriv ℝ n (TaylorModel.ofJet A p) x‖ ≤
      H * ∑ i ∈ Finset.Icc n p, ‖x‖ ^ (i - n) / (i - n).factorial := by
    apply (TaylorModel.norm_iteratedFDeriv_ofJet_le_Icc A p n x).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((hA i hi'.1 hi'.2).trans (le_max_left _ _)) (by positivity)) (Nat.cast_nonneg _)
  have hpen := (norm_iteratedFDeriv_penalty_le hn hσ x).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hHσ (by positivity))
      (Nat.cast_nonneg _))
  calc _ ≤ H * (∑ i ∈ Finset.Icc n p, ‖x‖ ^ (i - n) / (i - n).factorial) +
        H * ‖x‖ ^ (p + 1 - n) / (p + 1 - n).factorial := add_le_add hpoly hpen
    _ = _ := by
      rw [Finset.sum_Icc_succ_top (by omega : n ≤ p + 1)]
      ring

/-- The actual model derivative bound on the unit ball is three times the
maximum coefficient. This is stronger than separately adding two coarse bounds. -/
theorem norm_iteratedFDeriv_penalized_ofJet_le_three_max
    (A : FormalMultilinearSeries ℝ E ℝ) {p n : ℕ} (hn : n ≤ p)
    {σ D : ℝ} (hσ : 0 ≤ σ)
    (hA : ∀ i, n ≤ i → i ≤ p → ‖A i‖ ≤ D) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ n (penalized (TaylorModel.ofJet A p) p σ) x‖ ≤
      3 * max D σ := by
  have hH : 0 ≤ max D σ := hσ.trans (le_max_right _ _)
  apply (norm_iteratedFDeriv_penalized_ofJet_le_tail A hn hσ hA x).trans
  have ht := Real.sum_Icc_shift_pow_div_factorial_le (norm_nonneg x) hx
    (show n ≤ p + 1 by omega)
  exact (mul_le_mul_of_nonneg_left ht hH).trans (by nlinarith)

/-- The highest actual model derivative is globally Lipschitz with the
penalty parameter itself, for arbitrary supplied polynomial tensors. -/
theorem norm_sub_iteratedFDeriv_penalized_ofJet_le
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (x y : E) :
    ‖iteratedFDeriv ℝ p (penalized (TaylorModel.ofJet A p) p σ) x -
      iteratedFDeriv ℝ p (penalized (TaylorModel.ofJet A p) p σ) y‖ ≤ σ * ‖x - y‖ := by
  rw [iteratedFDeriv_penalized_ofJet_eq A p p le_rfl σ x,
    iteratedFDeriv_penalized_ofJet_eq A p p le_rfl σ y,
    TaylorModel.iteratedFDeriv_ofJet_top_eq A p x y,
    add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hσ (Nat.cast_nonneg _))]
  calc _ ≤ (σ / ((p + 1).factorial : ℝ)) *
        (((p + 1).factorial : ℝ) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left
            (NormPower.norm_sub_iteratedFDeriv_norm_pow_integer_le_finiteDimensional p x y)
            (div_nonneg hσ (Nat.cast_nonneg _))
    _ = _ := by field_simp

/-- The separately estimated polynomial and penalty terms give the source
bound `3*D+sigma` on the unit ball, with the exact highest-derivative penalty. -/
theorem norm_iteratedFDeriv_penalized_ofJet_le_three_mul_add
    (A : FormalMultilinearSeries ℝ E ℝ) {p n : ℕ} (hn : n ≤ p)
    {σ D : ℝ} (hσ : 0 ≤ σ) (hD : 0 ≤ D)
    (hA : ∀ i, n ≤ i → i ≤ p → ‖A i‖ ≤ D) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ n (penalized (TaylorModel.ofJet A p) p σ) x‖ ≤ 3 * D + σ := by
  have hpoly := TaylorModel.norm_iteratedFDeriv_ofJet_le_three_mul A hn hD hA hx
  have hpen := norm_iteratedFDeriv_penalty_le hn hσ x
  have hfac : (1 : ℝ) ≤ (p + 1 - n).factorial := by exact_mod_cast Nat.factorial_pos _
  have hpow : ‖x‖ ^ (p + 1 - n) ≤ 1 := pow_le_one₀ (norm_nonneg _) hx
  have hpen' := (hpen.trans (div_le_self (by positivity) hfac)).trans
    (mul_le_of_le_one_right hσ hpow)
  rw [iteratedFDeriv_penalized_ofJet_eq A p n hn σ x]
  exact (norm_add_le _ _).trans (add_le_add hpoly hpen')

end ModelDecrease
