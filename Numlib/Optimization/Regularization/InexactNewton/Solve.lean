import Numlib.Optimization.Regularization.InexactNewton.Run
import Numlib.Optimization.Regularization.ModelMinimum
import Numlib.Optimization.Quadratic.Optimality.Regularization
import Numlib.Optimization.TrustRegion.SecondOrder.Eigenpair

/-!
# Genuine global cubic solves furnish inexact Newton steps

A positive cubic norm penalty supplies an actual global minimizer. Its actual
stationarity and shifted positive semidefiniteness give every inexact quadratic
model condition, with multiplier equal to the upper parameter times step norm.
-/

namespace InexactRegularizedNewton
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Exact stationarity and nonnegative actual model curvature imply all
primitive inexact step tests for nonnegative control constants. -/
theorem Step.of_stationary_psd {f : E → ℝ} {x s : E} {ℓ σL σU κ₁ κ₂ κ₃ : ℝ}
    (hℓ : 0 ≤ ℓ) (hlo : σL * ‖s‖ ≤ ℓ) (hup : ℓ ≤ σU * ‖s‖)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hκ₃ : 0 ≤ κ₃)
    (hstat : fderiv ℝ (model f x ℓ) s = 0)
    (hpsd : ∀ v : E, 0 ≤ iteratedFDeriv ℝ 2 (model f x ℓ) s (fun _ => v)) :
    Step f x s ℓ σL σU κ₁ κ₂ κ₃ := by
  refine ⟨hℓ, hlo, hup, ?_, ?_⟩
  · rw [hstat, zero_apply]
    exact le_min (by positivity) (add_nonneg (div_nonneg (hpsd s) (by norm_num))
      (by positivity))
  · rw [hstat, norm_zero]
    positivity

/-- The positive cubic regularization of the genuine Taylor model has a global
minimizer with exact shifted stationarity and nonnegative actual model Hessian. -/
theorem exists_exact_step [ProperSpace E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s : E, fderiv ℝ (model f x (σ * ‖s‖)) s = 0 ∧
      ∀ v : E, 0 ≤ iteratedFDeriv ℝ 2 (model f x (σ * ‖s‖)) s (fun _ => v) := by
  let H := SecondOrderTrustRegion.hessian f x
  let g := gradient f x
  have hH : H.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (SecondOrderTrustRegion.hessian_isSelfAdjoint hf)
  obtain ⟨s, hs⟩ := ModelDecrease.exists_minimizer_ofJet
    (ftaylorSeries ℝ f x) 2 (mul_pos (by norm_num : (0 : ℝ) < 2) hσ)
  have hidentity (t : E) :
      ModelDecrease.penalized (ofJet (ftaylorSeries ℝ f x) 2) 2 (2 * σ) t =
        f x + QuadraticOptimality.regularized H g σ 3 t := by
    change eval f 2 x t + (2 * σ) / ((2 + 1).factorial : ℝ) * ‖t‖ ^ (2 + 1) = _
    rw [←SecondOrderTrustRegion.model_eq_taylor]
    simp only [QuadraticTrustRegion.model, QuadraticOptimality.regularized,
      QuadraticOptimality.model_eq, Nat.factorial, Nat.cast_mul,
      Nat.cast_one, Real.rpow_ofNat, Nat.reduceAdd]
    rw [real_inner_comm t (H t)]
    dsimp only [H, g]
    ring
  have hmin : ∀ t, QuadraticOptimality.regularized H g σ 3 s ≤
      QuadraticOptimality.regularized H g σ 3 t := by
    intro t
    have ht := hs t
    rw [hidentity s, hidentity t] at ht
    linarith
  obtain ⟨hstat, hpsd⟩ := QuadraticOptimality.necessary_regularized hH g s
    (by norm_num : (2 : ℝ) < 3) σ hmin
  norm_num only [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one] at hstat hpsd
  refine ⟨s, ?_, ?_⟩
  · ext v
    rw [RegularizedTrustRegion.fderiv_model hf]
    simp only [add_apply, smul_apply,
      smul_eq_mul, innerSL_apply_apply, zero_apply,
      quadraticDerivative]
    have he := congrArg (fun z : E => inner ℝ z v) hstat
    simp only [inner_add_left, real_inner_smul_left, neg_mul, inner_gradient_left,
      H, SecondOrderTrustRegion.hessian_apply, inner_hessianOperator,
      iteratedFDeriv_two_apply, g, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    linarith
  · intro v
    have hp := hpsd v
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at hp
    rw [RegularizedTrustRegion.iteratedFDeriv_two_model_diag hf]
    have hv : (![v, v] : Fin 2 → E) = fun _ => v := by funext i; fin_cases i <;> rfl
    simpa only [H, SecondOrderTrustRegion.hessian_apply, inner_hessianOperator, hv] using hp

/-- Every ordered regularization interval with positive upper endpoint admits
an actual primitive step and all projected model-curvature tests. The step is
obtained from a genuine global cubic model minimizer. -/
theorem exists_step [ProperSpace E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) {σL σU κ₁ κ₂ κ₃ κ₄ : ℝ}
    (hσ : 0 < σU) (horder : σL ≤ σU)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hκ₃ : 0 ≤ κ₃) (hκ₄ : 0 ≤ κ₄) :
    ∃ (s : E) (ℓ : ℝ), ℓ = σU * ‖s‖ ∧ Step f x s ℓ σL σU κ₁ κ₂ κ₃ ∧
      ∀ v : E, -κ₄ * ‖s‖ ≤ iteratedFDeriv ℝ 2 (model f x ℓ) s (fun _ => v) := by
  obtain ⟨s, hstat, hpsd⟩ := exists_exact_step hf hσ
  refine ⟨s, σU * ‖s‖, rfl, Step.of_stationary_psd (by positivity)
    (mul_le_mul_of_nonneg_right horder (norm_nonneg _)) le_rfl
      hκ₁ hκ₂ hκ₃ hstat hpsd, fun v => ?_⟩
  exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ₄) (norm_nonneg _)).trans (hpsd v)

end InexactRegularizedNewton
