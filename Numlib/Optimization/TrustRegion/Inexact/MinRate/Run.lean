import Numlib.Optimization.TrustRegion.Inexact.MinRate.Criticality
import Numlib.Optimization.TrustRegion.Inexact.Complexity

/-!
# Actual exact-oracle trust-region executions for unequal tolerances

One fixed objective admits accepted unit-step executions of arbitrary finite length. The
first-order tolerance is one and the second decreases with the horizon; all actual
ordered checks and primitive updates are proved.
-/

namespace OracleSimulation.MinRateCounterexample
open Real InexactTrustRegion EvaluationComplexity

/-- Fixed legal trust-region settings with exact derivative oracles, unit radius cap and
unit retained radii. -/
noncomputable def settings : InexactTrustRegion.Settings 2 where
  order_pos := by omega
  zeta := 1
  zeta_pos := zero_lt_one
  zeta_le_one := le_rfl
  theta := 1
  theta_pos := zero_lt_one
  theta_le_one := le_rfl
  eta1 := 1 / 4
  eta2 := 3 / 4
  gamma1 := 1 / 2
  gamma2 := 3 / 4
  gamma3 := 2
  radiusMax := 1
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_le_gamma2 := by norm_num
  gamma2_lt_one := by norm_num
  one_le_gamma3 := by norm_num
  requestFactor := 1 / 16
  requestFactor_pos := by norm_num
  oracleBound := 0
  oracleBound_nonneg := le_rfl
  initialCap := 1 / 32
  initialCap_pos := by norm_num
  reduction := 1 / 2
  reduction_pos := by norm_num
  reduction_lt_one := by norm_num

/-- The first requested accuracy is one half and the second is the actual derivative magnitude
at the chosen horizon. -/
noncomputable def requested (N : ℕ) (a : Fin 2) : ℝ := if a = 0 then 1 / 2 else magnitude N
/-- Every supplied derivative tensor is the true Frechet derivative at its actual trial
point. -/
noncomputable def exactJet (k : ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  ftaylorSeries ℝ objective (node k)
/-- The actual trial indices in a finite prefix. -/
def trials (N : ℕ) : Set ℕ := {i | i < N}

/-- Both requested accuracies are strictly positive at every horizon. -/
theorem requested_pos (N : ℕ) (a : Fin 2) : 0 < requested N a := by
  unfold requested
  split_ifs
  · norm_num
  · exact magnitude_pos _

/-- Both requested accuracies are at most one at every horizon. -/
theorem requested_le_one (N : ℕ) (a : Fin 2) : requested N a ≤ 1 := by
  unfold requested
  split_ifs
  · norm_num
  · exact (magnitude_lt_half _).le.trans (by norm_num)

/-- Both actual requested accuracies are strictly below one, including at the initial
point. -/
theorem requested_lt_one (N : ℕ) (a : Fin 2) : requested N a < 1 := by
  unfold requested
  split_ifs
  · norm_num
  · exact (magnitude_lt_quarter N).trans (by norm_num)

/-- Every horizon gives a genuine TRqIDA execution using the same fixed objective, exact
derivative oracles and accepted unit steps. -/
theorem run (N : ℕ) : InexactTrustRegion.Run objective settings (requested N)
    exactJet (trials N) (fun _ => 1) node (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => ratio) (fun _ _ => 1 / 32) N := by
  refine {
    order_pos := by omega
    zeta_pos := zero_lt_one
    zeta_le_one := le_rfl
    cap_pos := zero_lt_one
    cap_le_one := le_rfl
    accuracy_pos := requested_pos N
    accuracy_le_one := requested_le_one N
    radius_pos := fun _ _ => zero_lt_one
    direction_feasible := fun _ _ => by norm_num [optimalityRadius, settings]
    failed_test := ?_
    step_feasible := fun _ _ => by norm_num
    model_comparison := fun _ _ => le_rfl
    updates := ?_
    initial_cap := le_rfl
    cap_accuracy := ?_
    request_factor_nonneg := by norm_num [settings]
    oracle_constant_nonneg := le_rfl
    oracle := fun _ _ _ _ _ _ => by simp [exactJet, ftaylorSeries, settings]
    requests := fun _ _ _ _ _ _ => by norm_num [settings]
    exact_constant := fun _ _ _ => rfl
    ratio := ?_
    point_trial := ?_
    point_inactive := fun _ hk ht => (ht hk).elim
    initial_accuracy := fun _ _ _ => by norm_num [settings]
    accuracy_trial := fun _ _ _ _ _ _ => rfl
    accuracy_improvement := fun _ hk ht => (ht hk).elim
    oracle_all := fun _ _ _ _ _ => by simp [exactJet, ftaylorSeries, settings]
    unchanged_jet := ?_
    accuracy_branch := fun _ hk ht => (ht hk).elim }
  · intro k hk
    change k < N at hk
    change 1 / 2 * requested N 1 * optimalityRadius 1 1 ^ modelOrder (1 : Fin 2) /
      (modelOrder (1 : Fin 2)).factorial < TaylorModel.decrement objective 2 (node k) 1
    rw [decrement_two]
    have hm := magnitude_antitone hk.le
    have hp := magnitude_pos k
    norm_num [requested, optimalityRadius, modelOrder]
    linarith
  · refine ⟨zero_lt_one, le_rfl, settings.eta1_pos, settings.eta1_le_eta2,
      settings.eta2_lt_one, settings.gamma1_pos, settings.gamma1_le_gamma2,
      settings.gamma2_lt_one, settings.one_le_gamma3, ?_, fun _ _ _ => rfl⟩
    intro k hk ht
    have hr : settings.eta2 ≤ ratio := le_trans (by norm_num [settings]) ratio_gt_one.le
    rw [ite_eq_left hr]
    norm_num [settings]
  · exact (minimumAccuracy_le _ _ 0).trans (requested_le_one N 0)
  · intro k hk ht
    exact (actual_ratio k).symm
  · intro k hk ht
    have hr : settings.eta1 ≤ ratio := le_trans (by norm_num [settings]) ratio_gt_one.le
    rw [ite_eq_left hr]
    exact node_succ k
  · intro k hk ht hr
    exact (hr ((show settings.eta1 ≤ 1 by norm_num [settings]).trans ratio_gt_one.le)).elim

/-- The actual first-order check passes and the second-order unit direction attains the
genuine computed criticality. -/
theorem ordered_checks (N : ℕ) (k : ℕ) :
    (TaylorModel.decrement objective 1 (node k) 1 =
      TaylorModel.criticality objective 1 (node k) 1) ∧
    TaylorModel.decrement objective 1 (node k) 1 ≤ 1 / 2 * requested N 0 ∧
    (TaylorModel.decrement objective 2 (node k) 1 =
      TaylorModel.criticality objective 2 (node k) 1) := by
  rw [criticality_one, criticality_two, decrement_one, decrement_two]
  norm_num [requested]
  exact ⟨(magnitude_lt_quarter k).le, by ring⟩

/-- Every point through the horizon fails true second-order criticality at every positive
radius. -/
theorem true_second_failure {N k : ℕ} (hk : k ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    requested N 1 * δ ^ 2 / 2 < TaylorModel.criticality objective 2 (node k) δ := by
  have hh := TaylorModel.decrement_le_criticality objective 2 (x := node k)
    (s := δ) (δ := δ) (by simpa only [Real.norm_eq_abs, abs_of_pos hδ] using le_refl δ)
  rw [decrement_two] at hh
  have hm := magnitude_antitone hk
  have hpos := mul_pos (magnitude_pos k) hδ
  change magnitude N * δ ^ 2 / 2 < _
  have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg δ)
  nlinarith

/-- The actual objective schedule contains initialization and one call for every accepted
trial. -/
theorem function_evaluations (N : ℕ) : functionEvaluations (trials N) N = N + 1 := by
  classical
  have hs : successfulIterations (trials N) N = Finset.range N := by
    unfold successfulIterations
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact Finset.mem_range.mp hi
  simp only [functionEvaluations, hs, Finset.card_range]

/-- The actual schedule for each derivative order contains initialization and one refresh
after every accepted trial. -/
theorem derivative_evaluations (N : ℕ) :
    derivativeEvaluations (trials N) (fun _ => ratio) settings.eta1 N = N + 1 := by
  classical
  have hs : successfulIterations (successfulSet (trials N) (fun _ => ratio) settings.eta1) N =
      Finset.range N := by
    ext k
    have hr : settings.eta1 ≤ ratio :=
      (show settings.eta1 ≤ 1 by norm_num [settings]).trans ratio_gt_one.le
    simp only [successfulIterations, Finset.mem_filter, Finset.mem_range,
      successfulSet, trials, Set.mem_ofPred_eq, hr, and_true, and_self]
  have ha : successfulIterations (trials N)ᶜ N = ∅ := by
    ext k
    simp only [successfulIterations, Finset.mem_filter, Finset.mem_range, trials,
      Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.notMem_empty, iff_false, not_and]
    exact fun hk => not_not.mpr hk
  simp only [derivativeEvaluations, hs, ha, Finset.card_range, Finset.card_empty, add_zero]

/-- Every preterminal and endpoint ordered check strictly fails at the second
order, after the first-order check passed. -/
theorem selected_second {N k : ℕ} (hk : k ≤ N) :
    (1 / 2 : ℝ) * requested N 1 / 2 < TaylorModel.decrement objective 2 (node k) 1 := by
  rw [decrement_two]
  have hm := magnitude_antitone hk
  have hp := magnitude_pos k
  norm_num [requested]
  linarith

end OracleSimulation.MinRateCounterexample
