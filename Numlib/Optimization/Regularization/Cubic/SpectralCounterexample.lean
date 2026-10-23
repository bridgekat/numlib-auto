import Numlib.Optimization.Regularization.Cubic.QuadraticTrial

/-!
# The printed local quadratic-convergence coefficient can be too small

A positive scalar quadratic has a legal accepted cubic-regularization trial
whose actual model derivative is zero. Every one of the five printed threshold
terms is finite and positive, and both iterates lie in the local region. The
true endpoint gradient nevertheless exceeds the printed quadratic bound.
-/

noncomputable section
namespace CubicRegularization.SpectralCounterexample
open Set

/-- A fixed strongly convex scalar quadratic with least Hessian eigenvalue one tenth. -/
def objective (x : ℝ) : ℝ := x ^ 2 / 20

/-- The actual scalar objective derivative. -/
theorem hasDerivAt_objective (x : ℝ) : HasDerivAt objective (x / 10) x := by
  unfold objective
  convert (hasDerivAt_pow 2 x).div_const 20 using 1
  ring

/-- The genuine scalar derivative equals one tenth times the point. -/
theorem deriv_objective (x : ℝ) : deriv objective x = x / 10 :=
  (hasDerivAt_objective x).deriv

/-- The actual second derivative is the positive constant one tenth. -/
theorem second_derivative (x : ℝ) : iteratedDeriv 2 objective x = 1 / 10 := by
  have he : deriv objective = fun x => x / 10 := funext deriv_objective
  rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, he]
  norm_num

/-- The actual Hessian tensor is the constant positive bilinear form. -/
theorem second_formula (x : ℝ) (w : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 objective x w = (1 / 10 : ℝ) * w 0 * w 1 := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, second_derivative]
  simp only [Fin.prod_univ_two]
  ring

/-- The scalar unit vector is a true least Hessian eigenvector at every point. -/
theorem least_eigenpair (x : ℝ) :
    SecondOrderTrustRegion.IsLeastEigenpair objective x (1 / 10) 1 := by
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

/-- The actual objective is smooth, nonnegative, minimized at zero and has
Hessian Lipschitz constant one thousandth. -/
theorem regularity : ContDiff ℝ 2 objective ∧ IsLocalMin objective 0 ∧
    (∀ x, 0 ≤ objective x) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 objective x - iteratedFDeriv ℝ 2 objective y‖ ≤
      (1 / 1000 : ℝ) * ‖x - y‖) := by
  refine ⟨by unfold objective; fun_prop, ?_, ?_, ?_⟩
  · filter_upwards [] with x
    norm_num [objective]
    positivity
  · intro x
    unfold objective
    positivity
  · intro x y
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub, second_derivative,
      second_derivative, sub_self, norm_zero]
    positivity

/-- The true quadratic Taylor model is exact globally. -/
theorem taylor_exact (x s : ℝ) : TaylorModel.eval objective 2 x s = objective (x + s) := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    deriv_objective, second_derivative, objective]
  ring

/-- The fixed positive step length. -/
def u : ℝ := 1 / 100000000

/-- The initialized point and accepted endpoint. -/
def point (k : ℕ) : ℝ := if k = 0 then u + 500 * u ^ 2 else 500 * u ^ 2

/-- The actual cubic model gradient vanishes at the selected step. -/
theorem model_derivative_zero :
    fderiv ℝ (model objective (point 0) 100) (-u) = 0 := by
  rw [fderiv_model (by unfold objective; fun_prop)]
  apply ContinuousLinearMap.ext
  intro d
  simp only [TaylorModel.quadraticDerivative, add_apply, smul_apply, zero_apply,
    innerSL_apply_apply]
  have hf : fderiv ℝ objective (point 0) d = (point 0 / 10) * d := by
    rw [fderiv_eq_deriv_mul, deriv_objective]
  rw [hf]
  rw [show fderiv ℝ (fderiv ℝ objective) (point 0) (-u) d =
      (1 / 10 : ℝ) * (-u) * d by
    have hh := second_formula (point 0) ![-u, d]
    rw [iteratedFDeriv_two_apply] at hh
    exact hh]
  norm_num [u, point, real_inner_comm]
  ring

/-- All actual model-improvement, ratio and parameter-update rules hold. -/
theorem modelTrace : ModelTrace objective point (fun _ => -u)
    (fun _ => 100) (fun _ => 1) (1 / 4) (3 / 4) (1 / 2) 2 3 (1 / 4) 1 := by
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
    norm_num [point, objective, u]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [taylor_exact, taylor_exact]
    norm_num [point, objective, u]

/-- A genuine one-trial first-order AR2 execution, with the higher test disabled. -/
theorem actual_run : FirstOrderRun objective point (fun _ => -u) (fun _ => 100)
    (fun _ => 1) (1 / 4) (3 / 4) (1 / 2) 2 3 (1 / 4) (1 / 2)
      (1 / 100000000000) ⊤ 1 := by
  refine ⟨rfl, modelTrace, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [← norm_deriv_eq_norm_fderiv, deriv_objective]
    norm_num [point, u]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [model_derivative_zero, norm_zero]
    positivity
  · intro i hi
    have he : i = 0 := by omega
    subst i
    norm_num [point]

/-- The stronger printed model-termination test holds with zero actual gradient. -/
theorem stricter_test : ‖fderiv ℝ (model objective (point 0) 100) (-u)‖ ≤
    (1 / 2 : ℝ) * min ‖fderiv ℝ objective (point 0)‖ ((1 / 2 : ℝ) * ‖-u‖ ^ 2) := by
  rw [model_derivative_zero, norm_zero]
  positivity

/-- The source parameter cap is exactly the actual initial parameter. -/
theorem parameter_cap : max (100 : ℝ) (3 * (1 / 1000) / (1 - 3 / 4)) = 100 := by
  norm_num

/-- All five printed local-threshold terms are finite, positive rational
numbers, and their genuine minimum is the first term. -/
theorem printed_constants :
    2 / ((1 / 1000 : ℝ) + 1 / 2 + 100) *
      (((1 / 10 : ℝ) + (1 / 4) / 2) / (1 + 1 / 2)) ^ 2 = 45 / 100501 ∧
    (1 / 10 : ℝ) / (4 * (1 / 1000)) *
      (((1 / 10 : ℝ) + (1 / 4) / 2) / (1 + 1 / 2)) = 15 / 4 ∧
    (1 / 10 : ℝ) ^ 2 / (16 * (1 / 1000)) = 5 / 8 ∧
    3 * (1 - 3 / 4) * (1 / 10 : ℝ) / (4 * (1 / 1000)) *
      (((1 / 10 : ℝ) + (1 / 4) / 2) / (1 + 1 / 2)) = 45 / 16 ∧
    (1 / 10 : ℝ) / (4 * max (1 / 2 - 1 / 4) 0) *
      (((1 / 10 : ℝ) + (1 / 4) / 2) / (1 + 1 / 2)) = 3 / 200 ∧
    LocalCountCounterexample.printedZeta (1 / 10) (1 / 1000) (1 / 2)
      (1 / 4) 100 (3 / 4) = 45 / 100501 := by
  norm_num [LocalCountCounterexample.printedZeta]

/-- Both genuine points lie in the prescribed positive-curvature neighborhood;
the initial actual gradient is below its full printed threshold. -/
theorem local_region : ‖point 0‖ ≤ (1 / 10 : ℝ) / (4 * (1 / 1000)) ∧
    ‖point 1‖ ≤ (1 / 10 : ℝ) / (4 * (1 / 1000)) ∧
    ‖fderiv ℝ objective (point 0)‖ ≤
      LocalCountCounterexample.printedZeta (1 / 10) (1 / 1000) (1 / 2)
        (1 / 4) 100 (3 / 4) := by
  rw [← norm_deriv_eq_norm_fderiv, deriv_objective]
  norm_num [point, u, LocalCountCounterexample.printedZeta]

/-- The actual accepted endpoint violates the printed quadratic gradient bound. -/
theorem printed_bound_fails : ‖fderiv ℝ objective (point 0)‖ ^ 2 /
    LocalCountCounterexample.printedZeta (1 / 10) (1 / 1000) (1 / 2)
      (1 / 4) 100 (3 / 4) < ‖fderiv ℝ objective (point 1)‖ := by
  rw [← norm_deriv_eq_norm_fderiv, ← norm_deriv_eq_norm_fderiv,
    deriv_objective, deriv_objective]
  norm_num [point, u, LocalCountCounterexample.printedZeta]

end CubicRegularization.SpectralCounterexample
