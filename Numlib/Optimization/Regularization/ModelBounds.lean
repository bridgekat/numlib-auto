import Numlib.Optimization.Regularization.ModelLipschitz
import Numlib.Analysis.Calculus.TaylorModel.JetBounds
import Numlib.Analysis.InnerProductSpace.NormPow.UniformBounds

/-!
# Uniform actual derivative bounds for regularized tensor models

Compactness and homogeneity give finite bounds on the derivatives of an integer
norm power. Together with the exact polynomial derivative bounds these yield a
common positive constant for model derivatives of order at least two on the
unit ball and the
highest derivative's global Lipschitz bound. The constant is chosen before the
supplied jet, regularization parameter, points or requested accuracies.
-/

namespace ModelDecrease
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual derivative of a regularized finite jet is the sum of its actual
polynomial derivative and its actual norm-power penalty derivative. -/
theorem iteratedFDeriv_penalized_ofJet_eq (A : FormalMultilinearSeries ℝ E ℝ)
    (p n : ℕ) (hn : n ≤ p) (σ : ℝ) (x : E) :
    iteratedFDeriv ℝ n (penalized (TaylorModel.ofJet A p) p σ) x =
      iteratedFDeriv ℝ n (TaylorModel.ofJet A p) x +
        (σ / ((p + 1).factorial : ℝ)) •
          iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ (p + 1)) x := by
  have hpoly := TaylorModel.contDiff_ofJet A p n
  have hpow : ContDiff ℝ n (fun z : E => ‖z‖ ^ (p + 1)) := by
    have hp : (n : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hn
    simpa only [Real.rpow_natCast] using contDiff_normRpow_of_nat_lt (E := E) hp
  have hadd := iteratedFDeriv_add_apply (x := x) hpoly.contDiffAt
    (hpow.contDiffAt.const_smul (σ / ((p + 1).factorial : ℝ)))
  rw [iteratedFDeriv_const_smul_apply' hpow.contDiffAt] at hadd
  convert! hadd using 1

/-- Bounded supplied tensors of order at least two and a bounded nonnegative penalty
parameter yield one uniform positive bound on every model derivative of order at least two
on the unit ball and on the highest derivative's global Lipschitz constant. -/
theorem exists_uniform_penalized_derivative_bound (p : ℕ) {S D : ℝ}
    (hS : 0 ≤ S) (hD : 0 ≤ D) :
    ∃ B > 0, ∀ σ : ℝ, 0 ≤ σ → σ ≤ S →
      ∀ A : FormalMultilinearSeries ℝ E ℝ,
        (∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D) →
        (∀ n, 2 ≤ n → n ≤ p → ∀ x : E, ‖x‖ ≤ 1 →
          ‖iteratedFDeriv ℝ n (penalized (TaylorModel.ofJet A p) p σ) x‖ ≤ B) ∧
        (∀ x y : E,
          ‖iteratedFDeriv ℝ p (penalized (TaylorModel.ofJet A p) p σ) x -
            iteratedFDeriv ℝ p (penalized (TaylorModel.ofJet A p) p σ) y‖ ≤
              B * ‖x - y‖) := by
  obtain ⟨P, hP, hPb⟩ := exists_uniform_normPow_derivative_bound (E := E) p
  obtain ⟨L, hL, hLb⟩ := exists_lipschitz_iteratedFDeriv_normPow (E := E) p
  let c := S / ((p + 1).factorial : ℝ)
  let B := 1 + 3 * D + c * max P L
  have hc : 0 ≤ c := div_nonneg hS (Nat.cast_nonneg _)
  have hPL : 0 ≤ max P L := hP.trans (le_max_left _ _)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro σ hσ hσS A hA
  have hcσ : 0 ≤ σ / ((p + 1).factorial : ℝ) := div_nonneg hσ (Nat.cast_nonneg _)
  have hcσc : σ / ((p + 1).factorial : ℝ) ≤ c :=
    div_le_div_of_nonneg_right hσS (Nat.cast_nonneg _)
  constructor
  · intro n hn hnp x hx
    rw [iteratedFDeriv_penalized_ofJet_eq A p n hnp σ x]
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcσ]
    have hpoly := TaylorModel.norm_iteratedFDeriv_ofJet_le_three_mul A hnp hD
      (fun i hni hip => hA i (by omega) hip) hx
    have hpen := mul_le_mul hcσc ((hPb n hnp x hx).trans (le_max_left P L))
      (norm_nonneg _) hc
    dsimp only [B]
    linarith
  · intro x y
    rw [iteratedFDeriv_penalized_ofJet_eq A p p le_rfl σ x,
      iteratedFDeriv_penalized_ofJet_eq A p p le_rfl σ y,
      TaylorModel.iteratedFDeriv_ofJet_top_eq A p x y]
    have he : (iteratedFDeriv ℝ p (TaylorModel.ofJet A p) y +
        (σ / ((p + 1).factorial : ℝ)) •
          iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) x) -
        (iteratedFDeriv ℝ p (TaylorModel.ofJet A p) y +
          (σ / ((p + 1).factorial : ℝ)) •
            iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) y) =
        (σ / ((p + 1).factorial : ℝ)) •
          (iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) x -
            iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) y) := by
      rw [smul_sub]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcσ]
    calc _ ≤ (σ / ((p + 1).factorial : ℝ)) * (L * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (hLb x y) hcσ
      _ ≤ (c * max P L) * ‖x - y‖ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hcσc (le_max_right P L) hL hc) (norm_nonneg _)
      _ ≤ B * ‖x - y‖ := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _)

end ModelDecrease
