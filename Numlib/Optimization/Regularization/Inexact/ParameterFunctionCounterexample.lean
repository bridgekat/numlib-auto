import Numlib.Optimization.Regularization.Inexact.ParameterFunctionValues
import Numlib.Optimization.Regularization.Inexact.ParameterCounterexample

/-!
# EDA guarded-accuracy counterexample

Exact zero objective evaluations satisfy both relative error requests. A large
step skips the short-step tensor request, so the initial cap still invalidates
the printed parameter bound even under the EDA coefficient restrictions.
-/

namespace InexactRegularization.FunctionCounterexample
open Set TaylorModel Counterexample

/-- The EDA coefficient satisfies both source upper restrictions. -/
noncomputable def settings : OracleSettings 1 :=
  { Counterexample.settings with
    stepCoefficient := 1 / 16
    stepCoefficient_pos := by norm_num }

/-- The same actual large trial obeys the primitive shared EDA oracle rules. -/
theorem oracleTrace : OracleTrace (fun _ : ℝ => 0) 1 settings (fun _ => data) univ
    (fun _ => 0) (fun _ => 1) (fun _ => 125 / 4) (fun _ _ => 1000)
    parameter (fun _ => 0) (1 / 4) (1 / 2) (1 / 2) 2 3 1 1 := by
  have h := Counterexample.trace.toOracleTrace
  exact {
    order_pos := h.order_pos
    updates := h.updates
    initial_accuracy := h.initial_accuracy
    accuracy_trial := h.accuracy_trial
    accuracy_improvement := h.accuracy_improvement
    oracle := h.oracle
    short_request := by intro i hi hT hs; norm_num at hs
    reference_improvement := h.reference_improvement
    comparison := h.comparison
    point_update := h.point_update
    point_inactive := h.point_inactive }

/-- Both actual objective evaluations are exact, with positive requested error one. -/
theorem trace : FunctionTrace (fun _ : ℝ => 0) 1 settings (fun _ => data) univ
    (fun _ => 0) (fun _ => 1) (fun _ => 125 / 4) (fun _ _ => 1000)
    parameter (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1)
    (1 / 4) (1 / 2) (1 / 2) 2 3 1 1 := by
  refine ⟨oracleTrace, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hT
    simp [data, ftaylorSeries]
  · intro i hi hT
    norm_num
  · intro i hi hT
    norm_num
  · intro i hi hT
    norm_num
  · intro i hi hT
    rw [jetDecrement, ofJet_data, ofJet_data]
    norm_num [settings]
  · intro i hi hT
    simp

/-- The EDA coefficient obeys the acceptance and objective-error restrictions. -/
theorem coefficient_restrictions :
    settings.stepCoefficient ≤ ((1 : ℝ) / 4) / 4 ∧
    settings.stepCoefficient ≤ (1 - (1 : ℝ) / 2) / 4 ∧ settings.errorBound = 1 := by
  norm_num [settings, Counterexample.settings]

/-- The printed EDA upper bound is 32, but the actual updated parameter is 64. -/
theorem printed_bound_violated :
    max (parameter 0)
      (3 * (2 * (1 : ℝ) + 4 * ((1 + 1 : ℕ).factorial : ℝ) *
        settings.stepCoefficient) / (1 - 1 / 2)) < parameter 1 := by
  norm_num [parameter, settings, Counterexample.settings]

end InexactRegularization.FunctionCounterexample
