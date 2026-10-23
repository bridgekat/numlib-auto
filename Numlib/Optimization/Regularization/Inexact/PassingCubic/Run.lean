import Numlib.Optimization.Regularization.Inexact.PassingCubic.Execution

/-!
# Complete inaccurate cubic executions

Every parameter, accuracy, point, radius and derivative-reuse update is checked. Both
literal IDA and EDA executions include the final exact derivative refresh.
-/

namespace InexactRegularization.PassingCubic
open InexactTrustRegion EvaluationComplexity

/-- The single rejection and all subsequent accuracy-only iterations satisfy the primitive
parameter-update intervals. -/
theorem updates : TrialRegularizationUpdates data.trials data.parameter data.ratio
    settings.eta1 settings.eta2 settings.gamma1 settings.gamma2 settings.gamma3
      settings.sigmaMin 383 := by
  refine ⟨settings.sigmaMin_pos, by simp [data, parameter, settings], settings.eta1_pos,
    settings.eta1_le_eta2, settings.eta2_lt_one, settings.gamma1_pos,
    settings.gamma1_lt_one, settings.one_lt_gamma2, settings.gamma2_lt_gamma3, ?_, ?_⟩
  · intro k hk ht
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    have hn1 : ¬settings.eta1 ≤ data.ratio 0 := not_le_of_gt ratio_rejected
    have hn2 : ¬settings.eta2 ≤ data.ratio 0 := by
      exact not_le_of_gt (ratio_rejected.trans_le settings.eta1_le_eta2)
    rw [ite_eq_right hn2, ite_eq_right hn1]
    change parameter 1 ∈ Set.Icc (2 * parameter 0) (height * parameter 0)
    norm_num only [parameter, Nat.reduceEqDiff, reduceIte, Set.mem_Icc]
    constructor
    · nlinarith [numeric_bounds.1]
    · exact le_of_eq (pow_two height)
  · intro k hk ht
    have h0 : k ≠ 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    change parameter (k + 1) = parameter k
    simp only [parameter, h0, show ¬k + 1 = 0 by omega, reduceIte]

/-- The initial trial reuses unchanged error requests. -/
theorem accuracy_trial {k : ℕ} (ht : k ∈ data.trials) :
    accuracy (k + 1) = accuracy k := by
  have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
  subst k
  norm_num [accuracy]

/-- Every nontrial iteration halves all derivative error requests. -/
theorem accuracy_improvement {k : ℕ} (ht : k ∉ data.trials) :
    accuracy (k + 1) = (1 / 2) * accuracy k := by
  have h0 : k ≠ 0 := by simpa only [data, Set.mem_singleton_iff] using ht
  have he : k + 1 - 1 = k - 1 + 1 := by omega
  unfold accuracy
  rw [he, pow_succ]
  ring

/-- All 383 iterations form a genuine explicit-accuracy high-order regularization
execution. -/
theorem run : Explicit.Run (objective perturbation curvature) settings
    (fun _ => 1 / 2) data 383 where
  accuracy_pos := fun _ => by norm_num
  accuracy_le_one := fun _ => by norm_num
  initial_parameter := by simp [data, parameter, settings]
  initial_radii := fun _ => by norm_num [data]
  updates := updates
  initial_accuracy := fun _ _ _ => by
    change accuracy 0 ∈ Set.Icc 0 (2 * height)
    simp only [accuracy, Nat.zero_sub, pow_zero, div_one, Set.mem_Icc, le_refl, and_true]
    unfold height
    positivity
  accuracy_trial := fun _ _ ht _ _ _ => accuracy_trial ht
  accuracy_improvement := fun _ _ ht _ _ _ => accuracy_improvement ht
  oracle_all := fun _ _ _ hi hip => oracle hi hip
  constant_value := fun k _ _ => exact_value k
  error_initial := by
    intro k hk ht
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    change |objective perturbation curvature 0 - objective perturbation curvature 0| ≤ _
    rw [sub_self, abs_zero]
    exact (div_pos first_prediction_pos (by norm_num : (0 : ℝ) < 32)).le
  error_trial := by
    intro k hk ht
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    change |objective perturbation curvature (trialStep 0) -
      objective perturbation curvature (0 + trialStep 0)| ≤ _
    rw [zero_add, sub_self, abs_zero]
    exact (div_pos first_prediction_pos (by norm_num : (0 : ℝ) < 32)).le
  request_positive := by
    intro k hk ht
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    exact div_pos first_prediction_pos (by norm_num)
  relative_request := by
    intro k hk ht
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    change TaylorModel.jetDecrement (data.jet 0) 3 (data.step 0) / 32 ≤
      1 / 16 * TaylorModel.jetDecrement (data.jet 0) 3 (data.step 0)
    linarith [first_prediction_pos]
  no_exit := fun _ hk => never_stops hk
  step_one := fun k _ => computation_one k
  step_two := fun _ hk hs => computation_two hk hs
  trial_rule := fun _ hk => trial_rule hk
  ratio := fun _ _ _ => rfl
  point_trial := by
    intro k hk ht
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    rw [ite_eq_right (not_le_of_gt ratio_rejected)]
    rfl
  point_inactive := fun _ _ _ => rfl
  radius_trial := by
    intro k hk ht
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    have hn : ¬(settings.eta1 ≤ data.ratio 0 ∧ ‖data.step 0‖ < 1) :=
      fun h => (not_le_of_gt ratio_rejected) h.1
    rw [ite_eq_right hn]
    change (fun _ : Fin 3 => (1 : ℝ)) = firstCheck.reduced
    exact firstCheck_spec.2.2.1.symm
  radius_inactive := fun _ _ _ => rfl
  derivative_reuse := by
    intro k hk ht hr i hi hip
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    rfl

/-- The same exact objective evaluations and rejected whole-jet reuse form a genuine
implicit-accuracy execution. -/
theorem ida_run : InexactRegularization.Run (objective perturbation curvature)
    settings.toSettings (fun _ => 1 / 2) data.toExecutionData 383 where
  accuracy_pos := run.accuracy_pos
  accuracy_le_one := run.accuracy_le_one
  initial_parameter := run.initial_parameter
  initial_radii := run.initial_radii
  updates := run.updates
  initial_accuracy := run.initial_accuracy
  accuracy_trial := run.accuracy_trial
  accuracy_improvement := run.accuracy_improvement
  oracle_all := run.oracle_all
  exact_value := fun k _ => exact_value k
  step_one := run.step_one
  step_two := run.step_two
  trial_rule := run.trial_rule
  ratio := by
    intro k hk ht
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    unfold InexactRegularization.ratio
    simp only [data, zero_add]
  point_trial := run.point_trial
  point_inactive := run.point_inactive
  radius_trial := run.radius_trial
  radius_inactive := run.radius_inactive
  jet_reuse := by
    intro k hk ht hr
    have heq : k = 0 := by simpa only [data, Set.mem_singleton_iff] using ht
    subst k
    rfl

/-- The actual computed optimality check passes at iteration 382. -/
theorem bad_selected : data.selected 382 = none := by
  simpa only [data, check, Nat.reduceEqDiff, Nat.reduceLeDiff, reduceIte] using
    passingCheck_spec.2.1

/-- Every positive-order request at iteration 382 equals the small omitted true gradient. -/
theorem bad_accuracy (i : ℕ) : data.accuracy 382 i = perturbation := accuracy_at_bad

/-- True third-order criticality fails at the actual positive radius returned by the
passing computed check. -/
theorem bad_true_failure :
    (1 / 2 : ℝ) * data.checkedRadius 382 2 ^ 3 / 6 <
      TaylorModel.criticality (objective perturbation curvature) 3 (data.point 382)
        (data.checkedRadius 382 2) := by
  have hr : data.checkedRadius 382 2 = passingCheck.reduced 2 := by
    simp only [data, check, Nat.reduceEqDiff, Nat.reduceLeDiff, reduceIte]
  rw [hr]
  exact true_failure passingCheck_spec.2.2.1 numeric_bounds.2.1.le
    passingCheck_spec.2.2.2 numeric_bounds.2.2.2.1

/-- Iteration 382 is an actual accuracy-only iteration with unchanged parameter and halved
requests. -/
theorem bad_accuracy_only : 382 ∉ data.trials ∧
    data.parameter 383 = data.parameter 382 ∧
    (∀ i, data.accuracy 383 i = (1 / 2) * data.accuracy 382 i) := by
  refine ⟨by norm_num [data], by norm_num [data, parameter], fun i => ?_⟩
  exact accuracy_improvement (by norm_num [data] : 382 ∉ data.trials)

end InexactRegularization.PassingCubic
