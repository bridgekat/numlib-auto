import Numlib.Optimization.Constrained.TargetCounterexample.InnerExecution

/-!
# A complete two-phase execution with a genuine regularization inner method

Phase one immediately satisfies primal feasibility. The actual AR22 inner
run reaches the old target-merit root in one accepted trial. The target reset
then passes every recomputed merit check, causing the printed outer method to
return a point that satisfies neither stated Lagrangian output alternative.
-/

namespace Constrained.TargetCounterexample.InnerRegularization

/-- Neither the infeasible return alternative nor even the first two printed
Lagrangian bounds can hold at the actual two-phase return, for any multiplier. -/
theorem no_output_alternative : ¬(‖constraint (0 : E)‖ > (1 / 2 : ℝ) * (1 / 10) ∨
    ∃ y : ℝ, TaylorModel.constrainedCriticality
      (vectorLagrangian objective constraint y) 1 Set.univ 0 1 ≤
        (1 / 10 : ℝ) * multiplierNorm y ∧
      TaylorModel.restrictedCriticality (vectorLagrangian objective constraint y)
        2 tangent 0 1 ≤ (1 / 2 : ℝ) * ((1 / 10 : ℝ) * multiplierNorm y +
          TaylorModel.constrainedCriticality (vectorLagrangian objective constraint y)
            1 Set.univ 0 1 * ‖gradient objective 0‖)) := by
  rintro (hbad | hmult)
  · norm_num [constraint] at hbad
  · exact no_multiplier_satisfies_printed_bounds hmult

/-- A full concrete regularization-based two-phase execution has all global
source regularity, actual phase-one and phase-two inner runs, exact target
updates and genuine merit stopping checks, but no allowed output certificate.
The inner return is derived from a real one-trial AR22 execution. -/
theorem verified_regularized_counterexample :
    ContDiff ℝ 2 objective ∧ ContDiff ℝ 2 constraint ∧
    (∀ x : E, -(1 / 10 : ℝ) ≤ objective x) ∧
    (∀ x : E, objective x ≤ (1 / 10 : ℝ)) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x y : E,
      ‖iteratedFDeriv ℝ j objective x - iteratedFDeriv ℝ j objective y‖ ≤ ‖x - y‖) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x y : E,
      ‖iteratedFDeriv ℝ j constraint x -
        iteratedFDeriv ℝ j constraint y‖ ≤ ‖x - y‖) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x : E, ‖iteratedFDeriv ℝ j objective x‖ ≤ 1) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x : E, ‖iteratedFDeriv ℝ j constraint x‖ ≤ 1) ∧
    LeastNorm.Run (q := 2) constraint Set.univ (fun _ _ _ _ _ _ => False)
      (1 / 2 * (1 / 10)) (1 / 4) (fun _ => 1 / 10) (fun _ => initial)
        (fun _ _ => 1) (fun _ => 0) (fun _ => 0) 0 ∧
    ‖constraint initial‖ < (1 / 2 : ℝ) * (1 / 10) ∧
    HighOrderRegularization.Run oldMerit settings (fun _ : Fin 2 => tolerance) data 1 ∧
    LeastNorm.InnerSound (residual 0) Set.univ regularizedCall ∧
    regularizedCall initial
      (fun _ : Fin 2 => (1 / 4 : ℝ) * ‖residual 0 initial‖ * (1 / 10))
      0 (fun _ => 1) 2 2 ∧
    objective initial - Real.sqrt ((1 / 10 : ℝ) ^ 2 - ‖constraint initial‖ ^ 2) = 0 ∧
    ‖residual 0 (0 : E)‖ < (1 / 2 : ℝ) * (1 / 10) ∧
    objective 0 - Real.sqrt ((1 / 10 : ℝ) ^ 2 - ‖constraint (0 : E)‖ ^ 2) = -1 / 10 ∧
    ‖residual (-1 / 10) (0 : E)‖ = (1 / 10 : ℝ) ∧
    (∀ a : Fin 2, TaylorModel.constrainedCriticality (LeastNorm.merit (residual (-1 / 10)))
      (InexactTrustRegion.modelOrder a) Set.univ 0 1 ≤
        (1 / 10 : ℝ) * ‖residual (-1 / 10) (0 : E)‖ /
          (InexactTrustRegion.modelOrder a).factorial) ∧
    ¬(‖constraint (0 : E)‖ > (1 / 2 : ℝ) * (1 / 10) ∨
      ∃ y : ℝ, TaylorModel.constrainedCriticality
        (vectorLagrangian objective constraint y) 1 Set.univ 0 1 ≤
          (1 / 10 : ℝ) * multiplierNorm y ∧
        TaylorModel.restrictedCriticality (vectorLagrangian objective constraint y)
          2 tangent 0 1 ≤ (1 / 2 : ℝ) * ((1 / 10 : ℝ) * multiplierNorm y +
            TaylorModel.constrainedCriticality (vectorLagrangian objective constraint y)
              1 Set.univ 0 1 * ‖gradient objective 0‖)) := by
  obtain ⟨hf, hc, hlo, hup, hfl, hcl, hfb, hcb⟩ := source_regularity
  simp only [one_mul] at hfl hcl
  exact ⟨hf, hc, hlo, hup, hfl, hcl, hfb, hcb, phase_one_run, phase_one_primal,
    actual_run, regularizedCall_sound, actual_inner_call, actual_targets.1,
    actual_targets.2.1, actual_targets.2.2.1, actual_targets.2.2.2,
    reset_stopping_checks, no_output_alternative⟩

end Constrained.TargetCounterexample.InnerRegularization
