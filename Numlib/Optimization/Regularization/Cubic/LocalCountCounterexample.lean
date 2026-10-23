import Numlib.Optimization.Regularization.Cubic.FirstOrder
import Numlib.Optimization.Regularization.HighOrder.ObstructionCounterexample
import Numlib.Optimization.SecondOrder.HessianRegion
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A local cubic-regularization count cannot start at zero

The actual quadratic objective has a legal one-trial cubic execution satisfying
the tightened derivative test. Its initial point lies in the printed local
region, with all five threshold terms finite. At accuracy equal to half the
initial gradient threshold, the printed double logarithm is zero although the
initial test fails and the first accepted trial is necessary.
-/

namespace CubicRegularization.LocalCountCounterexample
open HighOrderRegularization.ObstructionCounterexample

/-- The actual second scalar derivative of the fixed quadratic is one. -/
theorem second_derivative (x : ℝ) : iteratedDeriv 2 objective x = 1 := by
  have he : deriv objective = fun x => x := funext deriv_objective
  rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, he]
  simp

/-- The quadratic has the exact Euclidean Hessian bilinear form. -/
theorem second_formula (x : ℝ) (v : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 objective x v = v 0 * v 1 := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, second_derivative]
  simp [Fin.prod_univ_two]

/-- The unit scalar vector is a genuine least Hessian eigenvector at every point. -/
theorem least_eigenpair (x : ℝ) :
    SecondOrderTrustRegion.IsLeastEigenpair objective x 1 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · have hh := TaylorModel.inner_hessianOperator objective x 1 1
    rw [second_formula] at hh
    simpa using hh
  · intro v hv
    rw [second_formula]
    have hh : v ^ 2 = 1 := by
      have hs := congrArg (fun a : ℝ => a ^ 2) hv
      simpa [Real.norm_eq_abs] using hs
    nlinarith

/-- The fixed objective is smooth, bounded below, minimized at zero, and has
actual Hessian Lipschitz bound one. -/
theorem regularity : ContDiff ℝ 2 objective ∧ IsLocalMin objective 0 ∧
    (∀ x, 0 ≤ objective x) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 objective x - iteratedFDeriv ℝ 2 objective y‖ ≤
      1 * ‖x - y‖) := by
  refine ⟨by unfold objective; fun_prop, ?_, objective_regularity.2.2, ?_⟩
  · filter_upwards [] with x
    simpa [objective] using objective_regularity.2.2 x
  · intro x y
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub, second_derivative,
      second_derivative, sub_self, norm_zero]
    positivity

/-- The exact quadratic Taylor model is the objective at the trial point. -/
theorem taylor_exact (x s : ℝ) : TaylorModel.eval objective 2 x s = objective (x + s) := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    deriv_objective, second_derivative, objective]
  ring

/-- The actual cubic model derivative at the chosen rational step is zero. -/
theorem model_derivative_zero :
    fderiv ℝ (model objective (513 / 32768) (1 / 4)) (-(1 : ℝ) / 64) = 0 := by
  rw [fderiv_model (by unfold objective; fun_prop)]
  apply ContinuousLinearMap.ext
  intro d
  simp only [TaylorModel.quadraticDerivative, add_apply, smul_apply, zero_apply,
    innerSL_apply_apply]
  have hf : fderiv ℝ objective (513 / 32768) d = (513 / 32768 : ℝ) * d := by
    rw [fderiv_eq_deriv_mul, deriv_objective]
  rw [hf]
  rw [show fderiv ℝ (fderiv ℝ objective) (513 / 32768) (-(1 : ℝ) / 64) d =
      (-(1 : ℝ) / 64) * d by
    have hh := second_formula (513 / 32768) ![-(1 : ℝ) / 64, d]
    rw [iteratedFDeriv_two_apply] at hh
    exact hh]
  norm_num [real_inner_comm]
  ring

/-- The exact one-trial arrays have an initial point and a much smaller endpoint. -/
noncomputable def point (k : ℕ) : ℝ := if k = 0 then 513 / 32768 else 1 / 32768

/-- All actual model, ratio, acceptance and update rules hold through one trial. -/
theorem modelTrace : ModelTrace objective point (fun _ => -(1 : ℝ) / 64)
    (fun _ => 1 / 4) (fun _ => 1) (1 / 4) (3 / 4) (1 / 2) 2 3 (1 / 4) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro i hi
    norm_num
  · intro i hi
    have he : i = 0 := by omega
    subst i
    unfold model ModelDecrease.penalized
    rw [taylor_exact, taylor_exact]
    norm_num [point, objective]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [taylor_exact, taylor_exact]
    norm_num [point, objective]

/-- A complete first-order AR2 prefix, with the second-order test disabled,
actually needs its first accepted trial for the selected accuracy. -/
theorem run : FirstOrderRun objective point (fun _ => -(1 : ℝ) / 64)
    (fun _ => 1 / 4) (fun _ => 1) (1 / 4) (3 / 4) (1 / 2) 2 3 (1 / 4)
      (1 / 2) ((513 / 32768 : ℝ) / 2) ⊤ 1 := by
  refine ⟨rfl, modelTrace, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [← norm_deriv_eq_norm_fderiv, deriv_objective]
    norm_num [point]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    change ‖fderiv ℝ (model objective (513 / 32768) (1 / 4)) (-(1 : ℝ) / 64)‖ ≤ _
    rw [model_derivative_zero, norm_zero]
    positivity
  · intro i hi
    have he : i = 0 := by omega
    subst i
    norm_num [point]

/-- The stricter source model-termination test holds with its actual derivative. -/
theorem stricter_test :
    ‖fderiv ℝ (model objective (point 0) (1 / 4)) (-(1 : ℝ) / 64)‖ ≤
      (1 / 2 : ℝ) * min ‖fderiv ℝ objective (point 0)‖
        ((1 / 2 : ℝ) * ‖(-(1 : ℝ) / 64)‖ ^ 2) := by
  change ‖fderiv ℝ (model objective (513 / 32768) (1 / 4)) (-(1 : ℝ) / 64)‖ ≤ _
  rw [model_derivative_zero, norm_zero]
  positivity

/-- The complete printed five-term local threshold. -/
noncomputable def printedZeta (ell L theta sigmaMin sigmaMax eta2 : ℝ) : ℝ :=
  let A := (ell + sigmaMin / 2) / (1 + theta)
  min (2 / (L + theta + sigmaMax) * A ^ 2)
    (min (ell / (4 * L) * A)
      (min (ell ^ 2 / (16 * L))
        (min (3 * (1 - eta2) * ell / (4 * L) * A)
          (ell / (4 * max (theta - sigmaMin) 0) * A))))

/-- All five terms are finite and their printed minimum equals one sixteenth. -/
theorem printed_constants :
    max (1 / 4 : ℝ) (3 * 1 / (1 - 3 / 4)) = 12 ∧
      printedZeta 1 1 (1 / 2) (1 / 4) 12 (3 / 4) = 1 / 16 := by
  norm_num [printedZeta]

/-- The initial gradient is below half of the exact printed local threshold
and the initial point is inside its positive-curvature neighborhood. -/
theorem initial_region :
    ‖point 0‖ ≤ (1 : ℝ) / 4 ∧
      ‖fderiv ℝ objective (point 0)‖ = (513 / 32768 : ℝ) ∧
      (513 / 32768 : ℝ) ≤ printedZeta 1 1 (1 / 2) (1 / 4) 12 (3 / 4) / 2 := by
  rw [printed_constants.2, ← norm_deriv_eq_norm_fderiv, deriv_objective]
  norm_num [point]

/-- The actual first accepted endpoint passes the requested derivative test. -/
theorem terminal_certificate :
    ‖fderiv ℝ objective (point 1)‖ ≤ ((513 / 32768 : ℝ) / 2) := by
  rw [← norm_deriv_eq_norm_fderiv, deriv_objective]
  norm_num [point]

/-- For the legal accuracy equal to half the initial local threshold, the
literal double logarithm is zero, although the initial gradient test fails. -/
theorem count_fails :
    Real.logb 2 (Real.logb 2 ((513 / 32768 : ℝ) / ((513 / 32768 : ℝ) / 2))) = 0 ∧
      ¬∃ k : ℕ, (k : ℝ) ≤
        Real.logb 2 (Real.logb 2 ((513 / 32768 : ℝ) / ((513 / 32768 : ℝ) / 2))) ∧
          ‖fderiv ℝ objective (point k)‖ ≤ ((513 / 32768 : ℝ) / 2) := by
  have he : Real.logb 2 (Real.logb 2
      ((513 / 32768 : ℝ) / ((513 / 32768 : ℝ) / 2))) = 0 := by
    norm_num [Real.logb_self_eq_one]
  refine ⟨he, ?_⟩
  rintro ⟨k, hk, hc⟩
  rw [he] at hk
  have hk0 : k = 0 := by exact_mod_cast (le_antisymm hk (Nat.cast_nonneg k))
  subst k
  rw [← norm_deriv_eq_norm_fderiv, deriv_objective] at hc
  norm_num [point] at hc

end CubicRegularization.LocalCountCounterexample
