import Numlib.Optimization.Constrained.TargetCounterexample.InnerRegularization

/-!
# An actual one-trial AR22 execution inside the two-phase obstruction

Exact ordered Taylor computations select the second-order trial. A true global
model minimizer attains zero old residual and is accepted at its genuine ratio.
The inherited unit radii pass the actual endpoint checks, giving a complete
primitive inner regularization run.
-/

noncomputable section
namespace Constrained.TargetCounterexample.InnerRegularization
open HighOrderRegularization InexactTrustRegion

/-- The actual first-order old-merit decrement vanishes initially. -/
theorem initial_decrement_one (v : E) : TaylorModel.decrement oldMerit 1 initial v = 0 := by
  rw [TaylorModel.decrement_one, inner_gradient_left, old_fderiv_initial]
  simp

/-- The true initial second-order Taylor decrement. -/
theorem initial_decrement_two (v : E) : TaylorModel.decrement oldMerit 2 initial v =
    (v 0) ^ 2 / 200 - (v 1) ^ 2 / 2 := by
  rw [TaylorModel.decrement_eq, old_taylor]
  have hv : oldMerit initial = 1 / 200 := by
    norm_num [oldMerit, merit_residual, targetMerit, objective, constraint, initial, vec]
  rw [hv]
  ring

/-- The first ordered criticality test sees an exactly zero gradient. -/
theorem initial_criticality_one : TaylorModel.criticality oldMerit 1 initial 1 = 0 := by
  obtain ⟨v, _, he⟩ := TaylorModel.exists_decrement_eq_criticality oldMerit 1 initial
    (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [initial_decrement_one] using he.symm

/-- The initial negative curvature gives actual quadratic criticality one two-hundredth. -/
theorem initial_criticality_two :
    TaylorModel.criticality oldMerit 2 initial 1 = (1 / 200 : ℝ) := by
  have hn : ‖vec (-1) 0‖ ≤ (1 : ℝ) := by
    rw [EuclideanSpace.norm_eq]
    norm_num [vec, Fin.sum_univ_two]
  apply le_antisymm
  · obtain ⟨v, hv, he⟩ := TaylorModel.exists_decrement_eq_criticality oldMerit 2 initial
      (by norm_num : (0 : ℝ) ≤ 1)
    rw [← he, initial_decrement_two]
    have hc := (coordinate_bound v 0).trans hv
    have hs : (v 0) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (v 0)) hc 2
    nlinarith [sq_nonneg (v 1)]
  · have hh := TaylorModel.decrement_le_criticality oldMerit 2 initial hn
    simpa [initial_decrement_two, vec] using hh

/-- The actual Taylor prediction for the selected step. -/
theorem trial_decrement : TaylorModel.decrement oldMerit 2 initial trial = length ^ 2 / 200 := by
  rw [initial_decrement_two]
  simp [trial, vec]

/-- The exact objective ratio of the one genuine merit trial. -/
theorem actual_ratio : HighOrderRegularization.ratio oldMerit 2 initial trial = 1 / length ^ 2 := by
  rw [HighOrderRegularization.ratio_eq, initial_add_trial, trial_decrement]
  have hi : oldMerit initial = 1 / 200 := by
    norm_num [oldMerit, merit_residual, targetMerit, objective, constraint, initial, vec]
  have hz : oldMerit (0 : E) = 0 := by
    norm_num [oldMerit, merit_residual, targetMerit, objective, constraint]
  rw [hi, hz]
  ring

/-- The actual trial is accepted but not very successful. -/
theorem ratio_bounds : (1 / 4 : ℝ) ≤ 1 / length ^ 2 ∧ 1 / length ^ 2 < 3 / 4 := by
  have hp : 0 < length := lt_trans zero_lt_one length_bounds.1
  have hs : 0 < length ^ 2 := sq_pos_of_pos hp
  have hlarge : 3 / 2 < length := by unfold length; linarith [Real.pi_gt_three]
  constructor
  · apply (le_div_iff₀ hs).mpr
    nlinarith [length_bounds.2]
  · apply (div_lt_iff₀ hs).mpr
    nlinarith

/-- The fixed inner accuracy is precisely the requested outer scale. -/
def tolerance : ℝ := 1 / 400

/-- Legal fixed AR22 settings, including the actual positive retained parameter. -/
def settings : Settings 2 2 where
  order_pos := by decide
  order_le := le_rfl
  zeta := 1
  zeta_pos := by norm_num
  zeta_le_one := le_rfl
  theta := 1 / 2
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  eta1 := 1 / 4
  eta2 := 3 / 4
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := sigma
  sigmaInitial := sigma
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := sigma_pos
  sigmaMin_le_initial := le_rfl

/-- Exact computed Taylor directions, first zero and then the negative coordinate unit. -/
def initialDirection (a : Fin 2) : E := if a = 0 then 0 else vec (-1) 0

/-- The actual initial ordered checks pass order one and fail order two. -/
theorem initial_check : OptimalityCheck oldMerit 1 (fun _ : Fin 2 => tolerance)
    (fun _ => 1) initial initialDirection (some 1) := by
  have hn : ‖vec (-1) 0‖ ≤ (1 : ℝ) := by
    rw [EuclideanSpace.norm_eq]
    norm_num [vec, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a _
    fin_cases a
    · simp [initialDirection]
    · simpa [initialDirection] using hn
  · intro a _
    fin_cases a
    · simp [modelOrder, initialDirection, initial_criticality_one]
    · norm_num [modelOrder, initialDirection, initial_criticality_two,
        initial_decrement_two, vec]
  · intro hn
    contradiction
  · intro a ha
    have he : a = 1 := Option.some.inj ha.symm
    subst a
    norm_num [modelOrder, initialDirection, tolerance, initial_decrement_two, vec]
  · intro a ha b hb
    have he : a = 1 := Option.some.inj ha.symm
    subst a
    have hb0 : b = 0 := by omega
    subst b
    norm_num [modelOrder, initialDirection, tolerance, initial_decrement_one]

/-- Every endpoint Taylor criticality is zero at the genuine old-merit root. -/
theorem endpoint_criticality (a : Fin 2) :
    TaylorModel.criticality oldMerit (modelOrder a) 0 1 = 0 := by
  have hh := old_criticality_zero a
  rw [TaylorModel.constrainedCriticality_univ] at hh
  exact hh

/-- Actual endpoint computations pass both strict ordered objective checks. -/
theorem endpoint_check : OptimalityCheck oldMerit 1 (fun _ : Fin 2 => tolerance)
    (fun _ => 1) 0 (fun _ => 0) none := by
  refine ⟨fun _ _ => by norm_num, ?_, ?_, ?_, ?_⟩
  · intro a _
    rw [endpoint_criticality, TaylorModel.decrement_zero]
    norm_num
  · intro _ a
    rw [TaylorModel.decrement_zero]
    unfold tolerance
    positivity
  · intro a ha
    contradiction
  · intro a ha
    contradiction

/-- The actual globally minimizing model step supplies every primitive model
computation field, including the legal large-step exit with unit radii. -/
theorem actual_stepComputation : ModelSolve.StepComputation
    (model oldMerit 2 initial sigma) modelOrder (1 / 2) 1
      (fun _ : Fin 2 => tolerance) trial (fun _ => 1) := by
  refine ⟨⟨1, zero_lt_one, le_rfl, ?_⟩, Or.inl ⟨?_, fun _ => rfl⟩⟩
  · intro v
    simpa only [one_mul] using sub_le_sub_left (model_isMin v)
      (model oldMerit 2 initial sigma 0)
  · rw [trial_norm]
    exact length_bounds.1

/-- Actual initialized arrays for the one-trial regularization execution. -/
def data : ExecutionData E 2 where
  point k := if k = 0 then initial else 0
  step _ := trial
  parameter _ := sigma
  ratio _ := 1 / length ^ 2
  radius _ _ := 1
  solvedRadius _ _ := 1
  direction k := if k = 0 then initialDirection else fun _ => 0
  selected k := if k = 0 then some 1 else none

/-- The genuine model trace obeys its actual ratio, accepted point update and
legal constant-parameter update interval. -/
theorem actual_modelTrace : HighOrderRegularization.ModelTrace oldMerit 2
    data.point data.step data.parameter data.ratio (1 / 4) (3 / 4) (1 / 2) 2 3 sigma 1 := by
  obtain ⟨hlo, hup⟩ := ratio_bounds
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · refine ⟨sigma_pos, le_rfl, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro k hk
    change if (3 / 4 : ℝ) ≤ 1 / length ^ 2 then
        sigma ∈ Set.Icc (max sigma (1 / 2 * sigma)) sigma
      else if (1 / 4 : ℝ) ≤ 1 / length ^ 2 then
        sigma ∈ Set.Icc sigma (2 * sigma)
      else sigma ∈ Set.Icc (2 * sigma) (3 * sigma)
    rw [ite_eq_right (not_le.mpr hup), ite_eq_left hlo]
    exact ⟨le_rfl, by linarith [sigma_pos]⟩
  · intro k hk
    have he : k = 0 := by omega
    subst k
    exact model_improves
  · intro k hk
    have he : k = 0 := by omega
    subst k
    exact actual_ratio.symm
  · intro k hk
    have he : k = 0 := by omega
    subst k
    change (0 : E) = if (1 / 4 : ℝ) ≤ 1 / length ^ 2 then initial + trial else initial
    rw [ite_eq_left hlo, initial_add_trial]

/-- A complete primitive AR22 run performs one actual accepted trial and has
an endpoint whose two ordered Taylor checks both pass. -/
theorem actual_run : HighOrderRegularization.Run oldMerit settings
    (fun _ : Fin 2 => tolerance) data 1 := by
  refine {
    accuracy_pos := fun _ => by norm_num [tolerance]
    accuracy_le_one := fun _ => by norm_num [tolerance]
    initial_parameter := rfl
    initial_radii := fun _ => ⟨zero_lt_one, le_rfl⟩
    modelTrace := actual_modelTrace
    check := ?_
    step_two := ?_
    continues := ?_
    radius_update := ?_ }
  · intro k hk
    by_cases he : k = 0
    · subst k
      exact initial_check
    · have he1 : k = 1 := by omega
      subst k
      exact endpoint_check
  · intro k hk hselected
    by_cases he : k = 0
    · subst k
      exact actual_stepComputation
    · have he1 : k = 1 := by omega
      subst k
      exact (hselected rfl).elim
  · intro k hk
    have he : k = 0 := by omega
    subst k
    simp [data]
  · intro k hk
    funext a
    simp [data]

/-- A genuine inner-call relation records actual AR22 executions, endpoint
ordered-check termination, and the initialized function and derivative counts. -/
def regularizedCall (xs : E) (ε : Fin 2 → ℝ) (x : E) (δ : Fin 2 → ℝ)
    (nf nd : ℕ) : Prop :=
  ∃ (D : ExecutionData E 2) (N : ℕ), HighOrderRegularization.Run oldMerit settings ε D N ∧
    D.point 0 = xs ∧ D.point N = x ∧ D.radius N = δ ∧ D.selected N = none ∧
      nf = N + 1 ∧ nd =
        (EvaluationComplexity.successfulIterations {i | settings.eta1 ≤ D.ratio i} N).card + 1

/-- Soundness follows from the real endpoint ordered checks and actual
inherited radii of the inner regularization execution. -/
theorem regularizedCall_sound : LeastNorm.InnerSound (residual 0) Set.univ regularizedCall := by
  intro xs ε x δ nf nd hcall
  obtain ⟨D, N, hrun, _, hx, hδ, hnone, _, _⟩ := hcall
  have ho := (hrun.check N le_rfl).optimality_of_none settings.zeta_pos
    (fun a => hrun.radius_mem le_rfl a) hnone
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · intro a
    simpa only [hδ] using ho.1 a
  · intro a
    rw [TaylorModel.constrainedCriticality_univ]
    change TaylorModel.criticality oldMerit (modelOrder a) x (δ a) ≤ _
    rw [← hx, ← hδ]
    exact ho.2 a

/-- The actual single trial has one successful iteration and two initialized
evaluations of the function and of each derivative. -/
theorem actual_inner_call :
    regularizedCall initial
      (fun _ : Fin 2 => (1 / 4 : ℝ) * ‖residual 0 initial‖ * (1 / 10))
      0 (fun _ => 1) 2 2 := by
  have he : (fun _ : Fin 2 => (1 / 4 : ℝ) * ‖residual 0 initial‖ * (1 / 10)) =
      (fun _ => tolerance) := by
    funext a
    norm_num [tolerance, initial, residual, objective, constraint, vec,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
  rw [he]
  refine ⟨data, 1, actual_run, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hs : (EvaluationComplexity.successfulIterations
      {i | settings.eta1 ≤ data.ratio i} 1) = {0} := by
    ext i
    simp only [EvaluationComplexity.mem_successfulIterations, Set.mem_ofPred_eq,
      Finset.mem_singleton]
    constructor
    · intro h
      omega
    · intro h
      subst i
      exact ⟨by decide, ratio_bounds.1⟩
  rw [hs]
  norm_num

/-- The genuine inner endpoint is truly critical for the old target at both
requested orders, before the outer algorithm's target reset. -/
theorem actual_endpoint_optimality : OptimalityAt oldMerit
    (fun _ : Fin 2 => tolerance) (0 : E) (fun _ => 1) :=
  (actual_run.check 1 le_rfl).optimality_of_none settings.zeta_pos
    (fun a => actual_run.radius_mem le_rfl a) rfl

/-- At the genuine global model minimum both actual low-order Taylor
criticalities vanish, even though the legal large-step return needs no such test. -/
theorem actual_model_criticality (a : Fin 2) :
    TaylorModel.criticality (model oldMerit 2 initial sigma) (modelOrder a) trial 1 = 0 := by
  have hlocal : IsLocalMin (model oldMerit 2 initial sigma) trial :=
    Filter.Eventually.of_forall model_isMin
  fin_cases a
  · exact TaylorModel.criticality_one_eq_zero_of_isLocalMin hlocal zero_le_one
  · have hf : ContDiff ℝ 2 (model oldMerit 2 initial sigma) :=
      ModelDecrease.contDiff_penalized_ofJet (ftaylorSeries ℝ oldMerit initial) 2 2 le_rfl sigma
    exact TaylorModel.criticality_two_eq_zero_of_isLocalMin hf hlocal zero_le_one

end Constrained.TargetCounterexample.InnerRegularization
