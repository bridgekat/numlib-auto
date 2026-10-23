import Numlib.Optimization.Regularization.Inexact.GuardedCounterexample.Execution
import Numlib.Optimization.Regularization.Inexact.RunObstruction
/-!
# Literal printed constants fail along an actual finite execution

The regularization cap printed in (13.1.77) is thirty for these legal settings,
while the actual guarded execution reaches two to the power forty. At its final
accepted trial, both the step and computed decrement equal two to the power
minus forty. True criticality still fails. These explicit inequalities refute
the dependent fixed-coefficient bounds, without refuting existential complexity
statements whose constants may depend on the initial derivative-error allowance.
-/

namespace InexactRegularization.GuardedCounterexample
open InexactTrustRegion
/-- The literal coefficient (13.1.77), specialized to order one and unit Lipschitz constants. -/
noncomputable def printedParameterCap : ℝ := max settings.sigmaInitial
  (settings.gamma3 * (2 * 1 + 4 * ((1 + 1).factorial : ℝ) *
    settings.stepCoefficient * settings.errorBound) / (1 - settings.eta2))
/-- The literal weighted-obstruction coefficient from (13.1.79). -/
noncomputable def printedCoefficient : ℝ :=
  1 + printedParameterCap + 3 * settings.errorBound * settings.stepCoefficient
/-- The literal model-decrease coefficient from (13.1.82), with p=q=1. -/
noncomputable def printedModelConstant : ℝ := settings.sigmaMin / ((1 + 1).factorial : ℝ) *
  ((1 - settings.theta) / (2 * ((1 : ℕ).factorial : ℝ) * printedCoefficient)) ^ 2
/-- The literal source parameter cap equals thirty for the fixed legal settings. -/
theorem printedParameterCap_eq : printedParameterCap = 30 := by
  norm_num [printedParameterCap, settings]
/-- The literal source obstruction coefficient equals 499 divided by sixteen. -/
theorem printedCoefficient_eq : printedCoefficient = 499 / 16 := by
  norm_num [printedCoefficient, printedParameterCap_eq, settings]
/-- The final actual trial parameter exceeds the literal printed parameter cap. -/
theorem actual_parameter_exceeds_printed : printedParameterCap < data.parameter 124 := by
  norm_num [printedParameterCap_eq, data, parameter]
/-- Every produced point fails actual approximate optimality at its inherited unit radius. -/
theorem true_failure (k : ℕ) :
    ¬OptimalityAt Real.sin (fun _ : Fin 1 => 1 / 2) (data.point k) (data.startRadius k) := by
  intro h
  have hh := h.2 0
  have hn := not_critical k zero_lt_one
  norm_num [OptimalityAt, data, modelOrder] at hh
  norm_num at hn
  linarith
/-- The actual accepted short step violates the printed first-order obstruction. -/
theorem inequality_violated :
    printedCoefficient * ‖data.step 124‖ < (1 - settings.theta) * (1 / 2 : ℝ) := by
  norm_num [printedCoefficient_eq, data, trialStep, slope, parameter, point, settings]
/-- The actual accepted short step is smaller than the printed step-length floor. -/
theorem step_floor_violated :
    ‖data.step 124‖ < (1 - settings.theta) / (2 * printedCoefficient) * (1 / 2 : ℝ) := by
  norm_num [printedCoefficient_eq, data, trialStep, slope, parameter, point, settings]
/-- The computed Taylor decrement is smaller than the printed model-decrease floor. -/
theorem model_floor_violated :
    TaylorModel.jetDecrement (data.jet 124) 1 (data.step 124) <
      printedModelConstant * (1 / 2 : ℝ) ^ 2 := by
  norm_num [printedModelConstant, printedCoefficient_eq, settings,
    data, decrement, trialStep, slope, parameter, point]
/-- The true accepted objective decrease is smaller than the printed successful-decrease floor. -/
theorem objective_floor_violated : Real.sin (data.point 124) - Real.sin (data.point 125) <
    settings.eta1 / 2 * printedModelConstant * (1 / 2 : ℝ) ^ 2 := by
  have hh := Real.sin_le (show (0 : ℝ) ≤ 1 / 2 ^ 40 by positivity)
  norm_num [data, point, printedModelConstant, printedCoefficient_eq, settings] at *
  linarith
/-- The final finite trial is an actual successful short iteration. -/
theorem successful_short_trial : 124 ∈ data.trials ∧ settings.eta1 ≤ data.ratio 124 ∧
    ‖data.step 124‖ < 1 := by
  refine ⟨by change 124 < 40 ∨ 124 = 124; omega, ?_, trialStep_small (by omega)⟩
  exact (show settings.eta1 ≤ 3 / 4 by norm_num [settings]).trans ratio_success
/-- Every allowed order violates the literal weighted inequality (13.1.79). -/
theorem weighted_inequality_violated (a : Fin 1) :
    printedCoefficient * ∑ i ∈ Finset.range (modelOrder a),
      data.startRadius 125 a ^ (i + 1) * ‖data.step 124‖ ^ (1 - (i + 1) + 1) /
        (i + 1).factorial <
      (1 - settings.theta) * (1 / 2 : ℝ) * data.startRadius 125 a ^ modelOrder a /
        (modelOrder a).factorial := by
  have ha : modelOrder a = 1 := by have := a.isLt; unfold modelOrder; omega
  simpa only [ha, data, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow,
    pow_one, Nat.factorial_one, Nat.cast_one, div_one, zero_tsub, Nat.sub_self, Nat.zero_add,
    one_mul, mul_one] using
    inequality_violated
/-- The sine objective has the full global zeroth/first derivative Lipschitz regularity
and a global lower bound required by the source. -/
theorem source_regularity : ContDiff ℝ 1 Real.sin ∧
    (∀ i, i ≤ 1 → ∀ x y, ‖iteratedFDeriv ℝ i Real.sin x -
      iteratedFDeriv ℝ i Real.sin y‖ ≤ ‖x - y‖) ∧ ∀ x, -1 ≤ Real.sin x :=
  ⟨sine_smooth 1, sine_lipschitz, sine_lower⟩
/-- The actual model-solve radii are one, as required in the low-order source branches. -/
theorem unit_solved_radii (k : ℕ) (a : Fin 1) : data.solvedRadius k a = 1 := rfl
end InexactRegularization.GuardedCounterexample
