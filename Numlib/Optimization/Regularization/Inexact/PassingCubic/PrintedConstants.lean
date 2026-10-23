import Numlib.Optimization.Regularization.Inexact.PassingCubic.Run
import Numlib.Optimization.Regularization.Inexact.RunVerified

/-!
# Literal error thresholds fail along complete cubic executions

A large rejected inaccurate trial legally increases the parameter beyond the
printed cap. Later passing computed checks omit a small true derivative. The
actual error requests satisfy the printed sufficient threshold, while true
criticality and the explicit stopping test fail.
-/

namespace InexactRegularization.PassingCubic
open InexactTrustRegion

/-- The literal source parameter coefficient (13.1.77), with the actual third-order
Lipschitz constant three. -/
noncomputable def printedParameterCap : ℝ := max settings.sigmaInitial
  (settings.gamma3 * (2 * 3 + 4 * ((3 + 1).factorial : ℝ) *
    settings.stepCoefficient * settings.errorBound) / (1 - settings.eta2))

/-- The literal source tensor bound (13.1.63), using the actual initial derivative-error
allowance. -/
noncomputable def printedTensorCap : ℝ := 3 + settings.errorBound * settings.initialCap

/-- The literal source radius coefficient (13.1.72), evaluated at the printed parameter
cap. -/
noncomputable def printedRadiusCoefficient : ℝ := stepRadiusCoefficient settings.zeta
  settings.theta printedTensorCap printedParameterCap

/-- The exact printed sufficient error threshold (13.1.78) at the common requested
accuracy one half. -/
noncomputable def printedAccuracyThreshold : ℝ := verificationThreshold 3 settings.zeta
  printedRadiusCoefficient settings.errorBound (minimumAccuracy settings.order_pos (fun _ => 1 / 2))

/-- The exact printed parameter cap is forty-eight times the initial parameter. -/
theorem printedParameterCap_eq : printedParameterCap = 48 * height := by
  norm_num [printedParameterCap, settings, height]

/-- The source tensor bound is three plus twice the initial parameter. -/
theorem printedTensorCap_eq : printedTensorCap = 3 + 2 * height := by
  norm_num [printedTensorCap, settings]

/-- The exact source radius coefficient at the printed cap has its displayed dyadic
denominator. -/
theorem printedRadiusCoefficient_eq : printedRadiusCoefficient = 1 / (2560 * height) := by
  norm_num [printedRadiusCoefficient, stepRadiusCoefficient, printedTensorCap_eq,
    printedParameterCap_eq, settings, height]

/-- The minimum of the three actual requested optimality accuracies is one half. -/
theorem minimum_accuracy_eq : minimumAccuracy settings.order_pos (fun _ => 1 / 2) = 1 / 2 := by
  apply le_antisymm
  · exact minimumAccuracy_le _ _ 0
  · apply Finset.le_inf'
    intro a ha
    exact le_rfl

/-- The small missing true derivative satisfies the exact printed sufficient error
threshold. -/
theorem small_printed_accuracy : perturbation ≤ printedAccuracyThreshold := by
  norm_num [printedAccuracyThreshold, verificationThreshold, minimum_accuracy_eq,
    printedRadiusCoefficient_eq, settings, height, perturbation]

/-- The true objective satisfies the full global zeroth-through-third Lipschitz smoothness
hypotheses with common constant three. -/
theorem source_regularity : ContDiff ℝ 3 (objective perturbation curvature) ∧
    (∀ j, j ≤ 3 → ∀ x y, ‖iteratedFDeriv ℝ j (objective perturbation curvature) x -
      iteratedFDeriv ℝ j (objective perturbation curvature) y‖ ≤ 3 * ‖x - y‖) := by
  refine ⟨smooth_objective _ _ _, ?_⟩
  exact fun j hj x y => objective_lipschitz (by unfold perturbation; positivity)
    numeric_bounds.2.2.2.2.1 numeric_bounds.2.1.le numeric_bounds.2.2.1 j hj x y

/-- The actual passing computed check at iteration 382 fails true approximate optimality
at its returned radii. -/
theorem bad_not_optimality : ¬OptimalityAt (objective perturbation curvature)
    (fun _ => 1 / 2) (data.point 382) (data.checkedRadius 382) := by
  intro h
  have hh := h.2 2
  have ho : modelOrder (2 : Fin 3) = 3 := rfl
  rw [ho] at hh
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at hh
  exact (not_le_of_gt bad_true_failure) hh

/-- All actual derivative error requests at iteration 382 satisfy the printed sufficient
bound (13.1.78). -/
theorem bad_small_accuracy (i : ℕ) : data.accuracy 382 i ≤ printedAccuracyThreshold := by
  rw [bad_accuracy]
  exact small_printed_accuracy

/-- The actual parameter at the failing check exceeds the printed uniform cap used in the
sufficient error bound. -/
theorem actual_parameter_exceeds_printed : printedParameterCap < data.parameter 382 := by
  norm_num [printedParameterCap_eq, data, parameter, height]

/-- Complete actual IDA and EDA executions satisfy the literal printed sufficient error
bound at a passing computed check, yet true criticality fails and explicit
verification forces an accuracy-only iteration. This refutes Lemma13.1.15 and
clause(ii) of Lemma13.3.6 with their printed parameter constants. -/
theorem verified_counterexample :
    ContDiff ℝ 3 (objective perturbation curvature) ∧
    (∀ j, j ≤ 3 → ∀ x y, ‖iteratedFDeriv ℝ j (objective perturbation curvature) x -
      iteratedFDeriv ℝ j (objective perturbation curvature) y‖ ≤ 3 * ‖x - y‖) ∧
    InexactRegularization.Run (objective perturbation curvature) settings.toSettings
      (fun _ => 1 / 2) data.toExecutionData 383 ∧
    Explicit.Run (objective perturbation curvature) settings (fun _ => 1 / 2) data 383 ∧
    data.selected 382 = none ∧
    (∀ i, data.accuracy 382 i ≤ verificationThreshold 3 settings.zeta
      (stepRadiusCoefficient settings.zeta settings.theta
        (3 + settings.errorBound * settings.initialCap)
        (max settings.sigmaInitial
          (settings.gamma3 * (2 * 3 + 4 * ((3 + 1).factorial : ℝ) *
            settings.stepCoefficient * settings.errorBound) / (1 - settings.eta2))))
      settings.errorBound (minimumAccuracy settings.order_pos (fun _ => 1 / 2))) ∧
    ¬OptimalityAt (objective perturbation curvature) (fun _ => 1 / 2)
      (data.point 382) (data.checkedRadius 382) ∧
    ¬Explicit.StopsAt settings (fun _ => 1 / 2) data 382 ∧
    382 ∉ data.trials ∧ data.parameter 383 = data.parameter 382 ∧
    (∀ i, data.accuracy 383 i = (1 / 2) * data.accuracy 382 i) := by
  exact ⟨source_regularity.1, source_regularity.2, ida_run, run, bad_selected,
    bad_small_accuracy, bad_not_optimality, never_stops (by omega), bad_accuracy_only⟩

end InexactRegularization.PassingCubic
