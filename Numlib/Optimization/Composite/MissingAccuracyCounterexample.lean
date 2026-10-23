import Numlib.Optimization.Composite.TruncatedAbs
import Numlib.Optimization.Composite.RunStepPowers

/-!
# The literal general composite step floor needs an accuracy factor

A genuine one-step execution on the fixed quadratic objective with zero
residual and a nonconvex subadditive outer function remains nonterminal at
both points. Its exact global model minimum is accepted at ratio three quarters.
All unit radii satisfy the source radius floor, but the actual tiny step is
below the printed accuracy-independent bound.
-/

namespace Composite.MissingAccuracyCounterexample
open HighOrderRegularization.ObstructionCounterexample
/-- The fixed small initial gradient scale. -/
noncomputable def a : ℝ := 1 / 1000000
/-- The actual initial point and accepted nonterminal endpoint. -/
noncomputable def point (k : ℕ) : ℝ := if k = 0 then -a else -a/2
/-- The actual global minimizer of each first-order regularized model. -/
noncomputable def step (k : ℕ) : ℝ := -point k / 2
/-- The legal accuracy below both actual objective criticalities. -/
noncomputable def epsilon : ℝ := a/4
/-- Fixed legal source parameters with regularization floor two. -/
noncomputable def settings : Settings 1 1 := {
  ZeroReturnCounterexample.settings with
  sigmaMin := 2
  sigmaInitial := 2
  sigmaMin_pos := by norm_num
  sigmaMin_le_initial := le_rfl }
/-- Actual point, model, ratio, radius and direction arrays. -/
noncomputable def data : ExecutionData ℝ 1 where
  point := point
  step := step
  parameter := fun _ => 2
  ratio := fun _ => 3/4
  radius := fun _ _ => 1
  solvedRadius := fun _ _ => 1
  direction := fun _ _ => 1
  selected := fun _ => some 0
  fraction := fun _ => 1
  modelDirection := fun _ _ => 0

/-- The actual first-order Taylor polynomial of the fixed quadratic. -/
theorem taylor_formula (x s : ℝ) : TaylorModel.eval objective 1 x s = objective x + x*s := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  simp [Finset.sum_range_succ, deriv_objective, mul_comm]
/-- The actual regularized first-order model is a scalar quadratic. -/
theorem model_formula (x s : ℝ) : HighOrderRegularization.model objective 1 x 2 s =
    objective x + x*s + s^2 := by
  unfold HighOrderRegularization.model ModelDecrease.penalized
  rw [taylor_formula]
  norm_num [Real.norm_eq_abs, sq_abs]
/-- Completing the square proves true global model minimality. -/
theorem model_min (x t : ℝ) : HighOrderRegularization.model objective 1 x 2 (-x/2) ≤
    HighOrderRegularization.model objective 1 x 2 t := by
  rw [model_formula,model_formula]
  nlinarith [sq_nonneg (t+x/2)]
/-- The genuine derivative of the actual regularized model. -/
theorem model_deriv (x s : ℝ) :
    deriv (HighOrderRegularization.model objective 1 x 2) s = x+2*s := by
  have he : HighOrderRegularization.model objective 1 x 2 = fun s => objective x+x*s+s^2 :=
    funext (model_formula x)
  rw [he]
  have hh : HasDerivAt (fun s : ℝ => objective x+x*s+s^2) (x+2*s) s := by
    convert ((hasDerivAt_const s (objective x)).add ((hasDerivAt_id s).const_mul x)).add
      ((hasDerivAt_id s).pow 2) using 1 <;> (first | (funext t; rfl) | (simp only [id_eq]; ring))
  exact hh.deriv

/-- The actual model has zero unit first-order criticality at its minimizer. -/
theorem smooth_criticality (x : ℝ) :
    TaylorModel.criticality (HighOrderRegularization.model objective 1 x 2) 1 (-x/2) 1 = 0 := by
  rw [TaylorModel.criticality_one _ _ zero_lt_one, gradient_eq_deriv, model_deriv]
  simp
  ring_nf

/-- The true global minimum and genuine model tests give a permitted detailed return. -/
theorem output (x : ℝ) : StepOutput objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1
    settings.theta settings.zeta (fun _ : Fin 1 => epsilon) x (-x/2) 2 1
      (fun _ => 1) (fun _ => 0) := by
  have hh := TruncatedAbs.zero
  have hm (t : ℝ) : regularizedModel objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h
      1 x 2 (-x/2) ≤ regularizedModel objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1 x 2 t := by
    simpa only [regularizedModel_zero_residual objective hh] using model_min x t
  refine ⟨zero_lt_one,le_rfl,?_,fun _ => ⟨zero_lt_one,le_rfl⟩,?_⟩
  · intro t
    simpa only [one_mul] using sub_le_sub_left (hm t)
      (regularizedModel objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1 x 2 0)
  · intro hs i
    have hi : InexactTrustRegion.modelOrder i = 1 := by
      have := i.isLt
      unfold InexactTrustRegion.modelOrder
      omega
    have hc : residualModel (fun _ : ℝ => (0 : ℝ)) 1 x = fun _ => 0 := by
      funext t
      exact eval_zero_residual 1 x t
    rw [hi,hc,criticality_zero_residual _ hh,decrement_zero_residual _ hh]
    change ‖(0 : ℝ)‖ ≤ 1 ∧ settings.zeta *
      TaylorModel.criticality (HighOrderRegularization.model objective 1 x 2) 1 (-x/2) 1 ≤
      TaylorModel.decrement (HighOrderRegularization.model objective 1 x 2) 1 (-x/2) 0 ∧ _
    rw [smooth_criticality]
    simp only [TaylorModel.decrement, TaylorModel.eval_zero, sub_self, mul_zero, norm_zero]
    refine ⟨zero_le_one,le_rfl,?_⟩
    dsimp [settings,ZeroReturnCounterexample.settings,epsilon,a]
    positivity
end Composite.MissingAccuracyCounterexample

namespace Composite.MissingAccuracyCounterexample
open HighOrderRegularization.ObstructionCounterexample

/-- The accepted constant parameter satisfies every allowed update interval. -/
theorem parameter_updates : EvaluationComplexity.RegularizationParameterUpdates
    data.parameter data.ratio settings.eta1 settings.eta2 settings.gamma1 settings.gamma2
      settings.gamma3 settings.sigmaMin 1 := by
  refine ⟨by norm_num [data,settings,ZeroReturnCounterexample.settings],
    by norm_num [data,settings,ZeroReturnCounterexample.settings],
    by norm_num [data,settings,ZeroReturnCounterexample.settings],
    by norm_num [data,settings,ZeroReturnCounterexample.settings],
    by norm_num [data,settings,ZeroReturnCounterexample.settings],
    by norm_num [data,settings,ZeroReturnCounterexample.settings],
    by norm_num [data,settings,ZeroReturnCounterexample.settings],
    by norm_num [data,settings,ZeroReturnCounterexample.settings],
    by norm_num [data,settings,ZeroReturnCounterexample.settings],?_⟩
  intro i hi
  norm_num [data,settings,ZeroReturnCounterexample.settings]

/-- Strict model improvement and the true objective ratio define the accepted trial. -/
theorem model_trace : ModelTrace objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1
    data.point data.step data.parameter data.ratio settings.eta1 settings.eta2
      settings.gamma1 settings.gamma2 settings.gamma3 settings.sigmaMin 1 := by
  refine ⟨parameter_updates,?_,?_⟩
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp only [data,regularizedModel_zero_residual objective TruncatedAbs.zero,model_formula]
    norm_num [point,step,a,objective]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp only [data,taylorModel_zero_residual objective TruncatedAbs.zero,taylor_formula]
    norm_num [point,step,a,objective,TruncatedAbs.zero]

/-- The actual generalized unit criticality equals the magnitude of the negative iterate. -/
theorem criticality_formula (k : ℕ) :
    criticality objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1 (point k) 1 = -point k := by
  rw [criticality_zero_residual objective TruncatedAbs.zero,
    TaylorModel.criticality_one _ _ zero_lt_one,gradient_eq_deriv,deriv_objective]
  have hx : point k < 0 := by unfold point;split_ifs <;> norm_num [a]
  simp [Real.norm_eq_abs,abs_of_neg hx]

/-- Every specified point selects the failing first-order computed test. -/
theorem check (k : ℕ) : OptimalityCheck objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h
    settings.zeta (fun _ : Fin 1 => epsilon) (data.radius k) (data.point k)
      (data.direction k) (data.selected k) := by
  refine ⟨fun _ => by norm_num [data],?_,?_,?_⟩
  · intro i
    have hi : InexactTrustRegion.modelOrder i = 1 := by
      have := i.isLt
      unfold InexactTrustRegion.modelOrder
      omega
    rw [hi]
    change settings.zeta *
      criticality objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1 (point k) 1 ≤
      decrement objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1 (point k) 1
    rw [criticality_formula,decrement_zero_residual objective TruncatedAbs.zero,
      TaylorModel.decrement,taylor_formula,taylor_formula]
    norm_num [settings,ZeroReturnCounterexample.settings]
  · intro hn
    simp [data] at hn
  · intro i hi
    have hj : InexactTrustRegion.modelOrder i = 1 := by
      have := i.isLt
      unfold InexactTrustRegion.modelOrder
      omega
    rw [hj]
    simp only [data,decrement_zero_residual objective TruncatedAbs.zero,TaylorModel.decrement,
      taylor_formula]
    unfold point
    split_ifs <;> norm_num [settings,ZeroReturnCounterexample.settings,epsilon,a]

/-- A complete detailed ARqpC prefix realizes the actual accepted trial. -/
theorem run : Run objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h settings
    (fun _ : Fin 1 => epsilon) data 1 where
  accuracy_pos := fun _ => by norm_num [epsilon,a]
  accuracy_le_one := fun _ => by norm_num [epsilon,a]
  initial_parameter := rfl
  initial_radii := fun _ => by norm_num [data]
  modelTrace := model_trace
  check := fun k _ => check k
  step_two := fun k _ _ => output (point k)
  continues := fun _ _ => by simp [data]
  point_update := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [data,point,step,settings,ZeroReturnCounterexample.settings]
    ring
  radius_update := by
    intro k hk
    change (fun _ : Fin 1 => (1 : ℝ)) = if _ then (fun _ => 1) else (fun _ => 1)
    split_ifs <;> rfl

/-- All source scalar and residual smoothness and Lipschitz bounds hold globally. -/
theorem source_regularity : ContDiff ℝ 1 objective ∧
    ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 objective x - iteratedFDeriv ℝ 1 objective y‖ ≤ 1*‖x-y‖) ∧
    (∀ x y : ℝ, ‖iteratedFDeriv ℝ 1 (fun _ : ℝ => (0 : ℝ)) x -
      iteratedFDeriv ℝ 1 (fun _ : ℝ => (0 : ℝ)) y‖ ≤ 1*‖x-y‖) ∧
    (∀ x : ℝ, 0 ≤ objective x + TruncatedAbs.h 0) := by
  refine ⟨by unfold objective;fun_prop,contDiff_const,?_,?_,?_⟩
  · intro x y
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
    simp [iteratedDeriv_one,deriv_objective]
  · intro x y
    simp [iteratedFDeriv_fun_zero]
  · intro x
    rw [TruncatedAbs.zero,add_zero]
    exact objective_regularity.2.2 x

/-- Both produced points fail true approximate optimality at unit radii. -/
theorem true_failure (k : ℕ) :
    ¬OptimalityAt objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h
      (fun _ : Fin 1 => epsilon) (point k) (fun _ => 1) := by
  intro hc
  have hh := hc.2 0
  norm_num [InexactTrustRegion.modelOrder,criticality_formula] at hh
  unfold point at hh
  split_ifs at hh <;> norm_num [epsilon,a] at hh

/-- The exact source regularization cap for the declared unit derivative bounds. -/
noncomputable def printedCap : ℝ := max settings.sigmaInitial
  (settings.gamma3 * (1+1) / (1-settings.eta2))
/-- The exact source radius coefficient at the printed regularization cap. -/
noncomputable def printedRadiusCoefficient : ℝ := settings.zeta * settings.theta /
  (8*(3*(1+1)+printedCap))
/-- The literal general-branch step floor, which omits any requested accuracy. -/
noncomputable def printedStepFloor : ℝ :=
  ((1-settings.theta)*printedRadiusCoefficient^1 /
    (3*((1 : ℕ).factorial : ℝ)*((1+1)+printedCap))) ^ ((1 : ℝ)/(1-1+1))

/-- The three printed coefficients have their exact positive rational values. -/
theorem printed_constants : printedCap = 24 ∧ printedRadiusCoefficient = 1/480 ∧
    printedStepFloor = 1/74880 := by
  norm_num [printedCap,printedRadiusCoefficient,printedStepFloor,settings,
    ZeroReturnCounterexample.settings]
/-- The actual step violates the literal accuracy-independent step floor. -/
theorem step_floor_violated : ‖data.step 0‖ < printedStepFloor := by
  rw [printed_constants.2.2]
  norm_num [data,step,point,a]
/-- Every actual solved radius satisfies the prescribed source floor. -/
theorem radius_floor (k : ℕ) (i : Fin 1) :
    printedRadiusCoefficient * epsilon ≤ data.solvedRadius k i := by
  rw [printed_constants.2.1]
  norm_num [epsilon,a,data]
/-- The actual trial ratio accepts the step. -/
theorem successful : settings.eta1 ≤ data.ratio 0 := by
  norm_num [data,settings,ZeroReturnCounterexample.settings]
end Composite.MissingAccuracyCounterexample

namespace Composite.MissingAccuracyCounterexample
open HighOrderRegularization.ObstructionCounterexample
/-- No point of the finite execution triggers either the true or zero-return stop. -/
theorem not_target (k : ℕ) : ¬TargetAt objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h
    settings (fun _ : Fin 1 => epsilon) data k := by
  rintro (h | ⟨hs,he⟩)
  · exact true_failure k h
  · change regularizedModel objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1
      (point k) 2 0 = regularizedModel objective (fun _ : ℝ => (0 : ℝ)) TruncatedAbs.h 1
      (point k) 2 (step k) at he
    simp only [regularizedModel_zero_residual objective TruncatedAbs.zero,model_formula] at he
    by_cases hk : k = 0
    · norm_num [point,step,hk,a,objective] at he
    · norm_num [point,step,hk,a,objective] at he
end Composite.MissingAccuracyCounterexample

namespace Composite.MissingAccuracyCounterexample
/-- Even the alternative OCR parsing of 3j! as (3j)! gives a violated floor. -/
theorem factorial_step_floor_violated : ‖data.step 0‖ <
    ((1-settings.theta)*printedRadiusCoefficient^1 /
      (((3*1 : ℕ).factorial : ℝ)*((1+1)+printedCap))) ^ ((1 : ℝ)/(1-1+1)) := by
  rw [printed_constants.1,printed_constants.2.1]
  norm_num [data,step,point,a,settings,ZeroReturnCounterexample.settings]
end Composite.MissingAccuracyCounterexample
