import Numlib.Optimization.Composite.Run
import Numlib.Optimization.Composite.ZeroReturnCounterexample

/-!
# An accepted composite step can increase its smooth scalar part

For the affine scalar part `x/2`, residual `x-1` and outer absolute value, the
actual regularized model is globally minimized by step one. The genuine ratio
is one and accepts the step, but the scalar part increases by one half. The
objective decrease in the composite analysis must concern the full objective.
-/

noncomputable section
namespace Composite.FunctionDecreaseCounterexample

/-- The smooth scalar part of the affine composite problem. -/
def f (x : ℝ) : ℝ := x / 2
/-- The affine residual whose absolute value supplies the objective decrease. -/
def c (x : ℝ) : ℝ := x - 1

/-- Actual scalar and residual derivatives on any direction. -/
theorem derivatives (x d : ℝ) : fderiv ℝ f x d = d / 2 ∧ fderiv ℝ c x d = d := by
  have hf : HasDerivAt f (1 / 2) x := (hasDerivAt_id x).div_const 2
  have hc : HasDerivAt c 1 x := (hasDerivAt_id x).sub_const 1
  rw [hf.hasFDerivAt.fderiv, hc.hasFDerivAt.fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- The actual generalized linear Taylor model is exact for the affine data. -/
theorem taylor_formula (x s : ℝ) : taylorModel f c abs 1 x s =
    (x + s) / 2 + |x + s - 1| := by
  rw [taylorModel_one, (derivatives x s).1, (derivatives x s).2]
  dsimp [f, c]
  rw [show x - 1 + s = x + s - 1 by ring]
  ring

/-- The actual regularized model for parameter one half. -/
theorem model_formula (s : ℝ) : regularizedModel f c abs 1 0 (1 / 2) s =
    s / 2 + |s - 1| + s ^ 2 / 4 := by
  unfold regularizedModel ModelDecrease.penalized
  rw [taylor_formula]
  norm_num [Real.norm_eq_abs, sq_abs]
  ring

/-- Step one is a genuine global minimizer of the actual regularized model. -/
theorem model_min (s : ℝ) : regularizedModel f c abs 1 0 (1 / 2) 1 ≤
    regularizedModel f c abs 1 0 (1 / 2) s := by
  rw [model_formula, model_formula]
  have ha := neg_le_abs (s - 1)
  norm_num
  nlinarith [sq_nonneg (s - 1)]

/-- Every global source regularity assumption holds and the full composite
objective is globally bounded below, despite the scalar part's increase. -/
theorem source_regularity : ContDiff ℝ 1 f ∧ ContDiff ℝ 1 c ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 c x - iteratedFDeriv ℝ 1 c y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x, 0 ≤ f x + |c x|) := by
  have hfd : ∀ x y, iteratedFDeriv ℝ 1 f x = iteratedFDeriv ℝ 1 f y := by
    intro x y
    ext
    simp only [iteratedFDeriv_one_apply, (derivatives x _).1, (derivatives y _).1]
  have hcd : ∀ x y, iteratedFDeriv ℝ 1 c x = iteratedFDeriv ℝ 1 c y := by
    intro x y
    ext
    simp only [iteratedFDeriv_one_apply, (derivatives x _).2, (derivatives y _).2]
  refine ⟨by unfold f; fun_prop, by unfold c; fun_prop, ?_, ?_, ?_⟩
  · intro x y
    rw [hfd x y, sub_self, norm_zero]
    positivity
  · intro x y
    rw [hcd x y, sub_self, norm_zero]
    positivity
  · intro x
    have h1 := le_abs_self (x - 1)
    have h2 := neg_le_abs (x - 1)
    dsimp [f, c]
    linarith

/-- A genuine global model minimizer satisfies the detailed positive-gap rule. -/
theorem global_step : ModelDecrease.ApproximateGlobalStep
    (regularizedModel f c abs 1 0 (1 / 2)) 1 1 := by
  intro t
  have hm := model_min t
  simpa only [one_mul] using sub_le_sub_left hm (regularizedModel f c abs 1 0 (1 / 2) 0)

/-- The full objective decreases while its smooth scalar part increases. -/
theorem opposite_decreases :
    f 0 + |c 0| - (f 1 + |c 1|) = 1 / 2 ∧ f 0 - f 1 = -(1 / 2) := by
  norm_num [f, c]


/-- The initial computed direction attains a genuine unit criticality of one half. -/
theorem initial_criticality : criticality f c abs 1 0 1 = 1 / 2 := by
  obtain ⟨d, hd, he⟩ := exists_decrement_eq_criticality f c continuous_abs 1 0
    (δ := (1 : ℝ)) (by norm_num)
  have hlo := decrement_le_criticality f c continuous_abs 1 0
    (δ := (1 : ℝ)) (s := (1 : ℝ)) (by norm_num)
  have hd1 : d ≤ 1 := (le_abs_self d).trans (by simpa only [Real.norm_eq_abs] using hd)
  rw [taylor_formula, taylor_formula] at he hlo
  rw [abs_of_nonpos (by linarith : (0 : ℝ) + d - 1 ≤ 0)] at he
  norm_num at he hlo
  linarith

/-- The accepted point's actual generalized unit criticality is zero. -/
theorem final_criticality : criticality f c abs 1 1 1 = 0 := by
  apply criticality_eq_zero_of_model_min f c abs 1 1 (by norm_num)
  intro d hd
  change taylorModel f c abs 1 1 0 ≤ taylorModel f c abs 1 1 d
  rw [taylor_formula, taylor_formula]
  have h1 := le_abs_self d
  have h2 := neg_le_abs d
  norm_num
  linarith

/-- Fixed legal settings for the genuine accepted affine-composite execution. -/
def settings : Settings 1 1 := {
  ZeroReturnCounterexample.settings with
  sigmaMin := 1 / 2
  sigmaInitial := 1 / 2
  sigmaMin_pos := by norm_num
  sigmaMin_le_initial := by norm_num }

/-- Actual data for the one accepted trial and its terminal objective check. -/
def data : ExecutionData ℝ 1 where
  point := fun k => if k = 0 then 0 else 1
  step := fun _ => 1
  parameter := fun _ => 1 / 2
  ratio := fun _ => 1
  radius := fun _ _ => 1
  solvedRadius := fun _ _ => 1
  direction := fun k _ => if k = 0 then 1 else 0
  selected := fun k => if k = 0 then some 0 else none
  fraction := fun _ => 1
  modelDirection := fun _ _ => 0

/-- Exact constant parameters obey every prescribed successful update interval. -/
theorem parameter_updates : EvaluationComplexity.RegularizationParameterUpdates
    data.parameter data.ratio settings.eta1 settings.eta2 settings.gamma1 settings.gamma2
      settings.gamma3 settings.sigmaMin 1 := by
  refine ⟨by norm_num [data, settings, ZeroReturnCounterexample.settings],
    by norm_num [data, settings, ZeroReturnCounterexample.settings],
    by norm_num [data, settings, ZeroReturnCounterexample.settings],
    by norm_num [data, settings, ZeroReturnCounterexample.settings],
    by norm_num [data, settings, ZeroReturnCounterexample.settings],
    by norm_num [data, settings, ZeroReturnCounterexample.settings],
    by norm_num [data, settings, ZeroReturnCounterexample.settings],
    by norm_num [data, settings, ZeroReturnCounterexample.settings],
    by norm_num [data, settings, ZeroReturnCounterexample.settings], ?_⟩
  intro i hi
  norm_num [data, settings, ZeroReturnCounterexample.settings]

/-- The actual prediction, objective ratio and legal updates make the trial accepted. -/
theorem model_trace : ModelTrace f c abs 1 data.point data.step data.parameter data.ratio
    settings.eta1 settings.eta2 settings.gamma1 settings.gamma2 settings.gamma3
      settings.sigmaMin 1 := by
  refine ⟨parameter_updates, ?_, ?_⟩
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    change regularizedModel f c abs 1 0 (1 / 2) 1 <
      regularizedModel f c abs 1 0 (1 / 2) 0
    rw [model_formula, model_formula]
    norm_num
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    change (1 : ℝ) = (f 0 + |c 0| - (f (0 + 1) + |c (0 + 1)|)) /
      (taylorModel f c abs 1 0 0 - taylorModel f c abs 1 0 1)
    rw [taylor_formula, taylor_formula]
    norm_num [f, c]

/-- The actual computed initial and terminal tests use the true criticality. -/
theorem objective_checks (k : ℕ) (hk : k ≤ 1) :
    OptimalityCheck f c abs settings.zeta (fun _ : Fin 1 => 1 / 4)
      (data.radius k) (data.point k) (data.direction k) (data.selected k) := by
  have hj (a : Fin 1) : InexactTrustRegion.modelOrder a = 1 := by
    unfold InexactTrustRegion.modelOrder
    omega
  interval_cases k
  · constructor
    · intro a
      norm_num [data]
    · intro a
      simp only [hj, data, ite_true, initial_criticality, settings,
        ZeroReturnCounterexample.settings]
      rw [decrement_eq, taylor_formula]
      norm_num [f, c]
    · intro hn
      norm_num [data] at hn
    · intro a ha
      simp only [hj, data, ite_true, settings, ZeroReturnCounterexample.settings]
      rw [decrement_eq, taylor_formula]
      norm_num [f, c]
  · constructor
    · intro a
      norm_num [data]
    · intro a
      simp only [hj, data, show ¬(1 : ℕ) = 0 by omega, ite_false, final_criticality,
        settings, ZeroReturnCounterexample.settings, decrement_zero]
      norm_num
    · intro hn a
      simp only [hj, data, show ¬(1 : ℕ) = 0 by omega, ite_false,
        settings, ZeroReturnCounterexample.settings, decrement_zero]
      norm_num
    · intro a ha
      norm_num [data] at ha

/-- A genuine detailed-solver execution includes the accepted trial, actual
updates, unit radii, initial failure and terminal successful check. -/
theorem actual_run : Run f c abs settings (fun _ : Fin 1 => 1 / 4) data 1 := by
  refine ⟨by intro a; norm_num, by intro a; norm_num, rfl,
    by intro a; norm_num [data], model_trace, objective_checks, ?_, ?_, ?_, ?_⟩
  · intro k hk hsel
    have hk0 : k = 0 := by
      interval_cases k
      · rfl
      · norm_num [data] at hsel
    subst k
    refine ⟨by norm_num [data], by norm_num [data], global_step,
      by intro a; norm_num [data], ?_⟩
    intro hs
    norm_num [data] at hs
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [data]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [data, settings, ZeroReturnCounterexample.settings]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [data, settings, ZeroReturnCounterexample.settings]

/-- The printed parameter cap and first-order decrease coefficient are positive
exact constants, with the scalar/residual derivative bounds both set to one. -/
theorem printed_constants :
    max settings.sigmaInitial
      (settings.gamma3 * (1 + 1 * 1) / (1 - settings.eta2)) = 24 ∧
    settings.sigmaMin / (2 : ℕ).factorial *
      ((1 - settings.theta) / (3 * (1 : ℕ).factorial * (1 + (24 : ℝ)))) ^ 2 =
        1 / 90000 := by
  norm_num [settings, ZeroReturnCounterexample.settings]

/-- The literal smooth-scalar decrease claim fails despite the actual accepted
run and its genuine global model solve. The full composite objective decreases. -/
theorem violates_scalar_decrease :
    ¬settings.eta1 * (1 / 90000 : ℝ) * (1 / 4 : ℝ) ^ 2 ≤
      f (data.point 0) - f (data.point 1) := by
  norm_num [f, data, settings, ZeroReturnCounterexample.settings]


/-- All source regularity and outer assumptions, an actual detailed accepted
run and the exact printed positive coefficient accompany the violated scalar
claim. The accepted trial is the last trial before its successful endpoint check.
-/
theorem verified_counterexample : ContDiff ℝ 1 f ∧ ContDiff ℝ 1 c ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 c x - iteratedFDeriv ℝ 1 c y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x, 0 ≤ f x + |c x|) ∧
    LipschitzWith 1 (abs : ℝ → ℝ) ∧ ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 ∧
    Run f c abs settings (fun _ : Fin 1 => 1 / 4) data 1 ∧
    settings.eta1 ≤ data.ratio 0 ∧
    max settings.sigmaInitial
      (settings.gamma3 * (1 + 1 * 1) / (1 - settings.eta2)) = 24 ∧
    settings.sigmaMin / (2 : ℕ).factorial *
      ((1 - settings.theta) / (3 * (1 : ℕ).factorial * (1 + (24 : ℝ)))) ^ 2 =
        1 / 90000 ∧
    f 0 + |c 0| - (f 1 + |c 1|) = 1 / 2 ∧ f 0 - f 1 = -(1 / 2) ∧
    ¬settings.eta1 * (1 / 90000 : ℝ) * (1 / 4 : ℝ) ^ 2 ≤
      f (data.point 0) - f (data.point 1) := by
  rcases source_regularity with ⟨hf, hc, hLf, hLc, hlow⟩
  exact ⟨hf, hc, hLf, hLc, hlow, ZeroReturnCounterexample.outer_properties.1,
    ZeroReturnCounterexample.outer_properties.2.1,
    ZeroReturnCounterexample.outer_properties.2.2.1,
    ZeroReturnCounterexample.outer_properties.2.2.2.1, actual_run,
    by norm_num [data, settings, ZeroReturnCounterexample.settings],
    printed_constants.1, printed_constants.2, opposite_decreases.1,
    opposite_decreases.2, violates_scalar_decrease⟩

end Composite.FunctionDecreaseCounterexample
