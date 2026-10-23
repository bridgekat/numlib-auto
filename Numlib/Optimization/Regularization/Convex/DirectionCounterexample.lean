import Numlib.Optimization.Constrained.RestrictedCriticality
import Numlib.Optimization.Regularization.Convex.DerivativeError
import Numlib.Optimization.Regularization.Cubic.LocalCountCounterexample

/-!
# The literal constrained directional bound needs the unit-ball restriction

The source restricted direction set C¹ need not be bounded. A genuine scalar
first-order constrained execution reaches the quadratic minimizer with a small
nonzero model derivative. Arbitrarily long restricted directions therefore
violate a derivative-error bound stated without their norm factor.
-/

namespace ConvexRegularization.DirectionCounterexample
open Set TaylorModel HighOrderRegularization.ObstructionCounterexample

/-- Fixed legal first-order constrained parameters. -/
noncomputable def settings : Settings 1 where
  order_pos := by decide
  tau := 1/2
  theta := 3/4
  eta1 := 1/4
  eta2 := 3/4
  gamma1 := 1/2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 5/4
  sigmaInitial := 5/4
  tau_pos := by norm_num
  tau_lt_one := by norm_num
  theta_lower := by norm_num
  theta_lt_one := by norm_num
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num
  sigmaMin_le_initial := le_rfl

/-- Actual initialized and accepted-point arrays. -/
noncomputable def data : Data ℝ where
  point := fun k => if k = 0 then 1 else 0
  step := fun _ => -1
  parameter := fun _ => 5/4
  ratio := fun _ => 1/2

/-- The actual first-order Taylor polynomial of the quadratic. -/
theorem taylor_formula (x s : ℝ) : eval objective 1 x s = objective x + x*s := by
  rw [eval_eq_sum_iteratedDeriv]
  simp [Finset.sum_range_succ,deriv_objective,mul_comm]

/-- The actual regularized model has the genuine scalar quadratic penalty. -/
theorem model_formula (x s : ℝ) :
    HighOrderRegularization.model objective 1 x (5/4) s =
      objective x + x*s + (5/8)*s^2 := by
  unfold HighOrderRegularization.model ModelDecrease.penalized
  rw [taylor_formula]
  norm_num [Real.norm_eq_abs,sq_abs]

/-- The genuine model derivative, obtained by differentiating its actual formula. -/
theorem model_deriv (x s : ℝ) :
    deriv (HighOrderRegularization.model objective 1 x (5/4)) s = x+(5/4)*s := by
  have he : HighOrderRegularization.model objective 1 x (5/4) =
      fun s => objective x+x*s+(5/8)*s^2 := funext (model_formula x)
  rw [he]
  have hd := ((hasDerivAt_const s (objective x)).add ((hasDerivAt_id s).const_mul x)).add
    (((hasDerivAt_id s).pow 2).const_mul (5/8 : ℝ))
  change HasDerivAt (fun t : ℝ => objective x+x*t+(5/8)*t^2) _ s at hd
  convert hd.deriv using 1
  simp only [id_eq]
  ring

/-- A full genuine first-order ARp-CC execution accepts the trial to the minimizer. -/
theorem run : Run objective univ settings (1/2) data 1 := by
  refine {
    accuracy_pos := by norm_num
    initial_parameter := rfl
    initial_mem := mem_univ _
    modelTrace := ?_
    feasible_trial := fun _ _ => mem_univ _
    model_test := ?_
    continues := ?_ }
  · refine {
      order_pos := by decide
      updates := ?_
      improvement := ?_
      ratio := ?_
      point_update := ?_ }
    · refine ⟨by norm_num [settings],by norm_num [data,settings],
        by norm_num [settings],by norm_num [settings],by norm_num [settings],
        by norm_num [settings],by norm_num [settings],by norm_num [settings],
        by norm_num [settings],fun i hi => ?_⟩
      norm_num [data,settings]
    · intro i hi
      have he : i = 0 := by omega
      subst i
      norm_num [data,model_formula,objective]
    · intro i hi
      have he : i = 0 := by omega
      subst i
      unfold HighOrderRegularization.ratio decrement
      norm_num [data,taylor_formula,objective]
    · intro i hi
      have he : i = 0 := by omega
      subst i
      norm_num [data,settings]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    have hset : feasibleDisplacements (univ : Set ℝ) (1 : ℝ) = univ := by ext d;simp
    simp only [data,ite_true,hset]
    rw [constrainedCriticality_univ,TaylorModel.criticality_one _ _ zero_lt_one,gradient_eq_deriv]
    norm_num [model_deriv,settings]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    simp only [data,ite_true]
    rw [constrainedCriticality_univ,TaylorModel.criticality_one _ _ zero_lt_one,gradient_eq_deriv]
    norm_num [deriv_objective]

/-- The exact source parameter cap at the declared derivative Lipschitz constant. -/
theorem parameter_cap : parameterCap settings 1 = 12 := by
  norm_num [parameterCap,settings]

/-- The actual quadratic satisfies the full source smoothness and derivative-Lipschitz condition. -/
theorem regularity : ContDiff ℝ 1 objective ∧
    ∀ x y : ℝ, ‖iteratedFDeriv ℝ 1 objective x -
      iteratedFDeriv ℝ 1 objective y‖ ≤ ‖x-y‖ := by
  refine ⟨by unfold objective;fun_prop,?_⟩
  intro x y
  rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
  simp [iteratedDeriv_one,deriv_objective]

/-- The long direction belongs to the actual source C¹ set, which does not itself
include the unit ball. Its genuine endpoint first derivative is zero. -/
theorem restricted_direction : (100 : ℝ) ∈ firstRestrictedDirections objective
    (feasibleDisplacements univ (data.point 1)) (data.point 1) (settings.tau*(1/2)) := by
  constructor
  · trivial
  · norm_num [data,fderiv_eq_deriv_mul,deriv_objective,settings]

/-- The actual model directional derivative grows with the long feasible direction. -/
theorem directional_value :
    |fderiv ℝ (HighOrderRegularization.model objective 1 (data.point 0)
      (data.parameter 0)) (data.step 0) (100 : ℝ)| = 25 := by
  norm_num [data,fderiv_eq_deriv_mul,model_deriv]

/-- The literal direction-independent right side is only thirteen and one quarter. -/
theorem printed_error_value :
    ((1 : ℝ)+parameterCap settings 1) / (1 : ℕ).factorial * ‖data.step 0‖ ^ 1 +
      settings.tau*(1/2) = 53/4 := by
  rw [parameter_cap]
  norm_num [data,settings]

/-- A genuine source-restricted direction violates the literal bound(6.2.18). -/
theorem directional_bound_fails :
    ¬|fderiv ℝ (HighOrderRegularization.model objective 1 (data.point 0)
      (data.parameter 0)) (data.step 0) (100 : ℝ)| ≤
        ((1 : ℝ)+parameterCap settings 1) / (1 : ℕ).factorial * ‖data.step 0‖ ^ 1 +
          settings.tau*(1/2) := by
  rw [directional_value,printed_error_value]
  norm_num

end ConvexRegularization.DirectionCounterexample
