import Numlib.Optimization.Constrained.TwoPhase.BoundaryCalculus

/-!
# A literal one-call two-phase execution at the equality boundary

Phase one is initially feasible. One genuine p=2 ARp-CC trial with fixed cubic
parameter eight reaches residual `θ ε₀` exactly. The printed strict reset guard
falls through to termination even though the actual normalized merit test fails.
-/

namespace Constrained.TwoPhase.Boundary
open Set Metric TaylorModel ConvexRegularization HighOrderRegularization

/-- Fixed legal p=2 inner settings, including the source theta/tau restriction. -/
noncomputable def settings : ConvexRegularization.Settings 2 where
  order_pos := by decide
  tau := 1 / 2
  theta := 3 / 4
  eta1 := 1 / 4
  eta2 := 3 / 4
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 8
  sigmaInitial := 8
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

/-- The actual single inner trial is accepted, with constant regularization eight. -/
noncomputable def innerData : ConvexRegularization.Data E where
  point := fun k => if k = 0 then 0 else endpoint
  step := fun _ => endpoint
  parameter := fun _ => 8
  ratio := fun _ => 1

/-- The actual endpoint lies strictly inside the source's bounded convex region. -/
theorem endpoint_mem : endpoint ∈ region := by
  change dist endpoint 0 ≤ 2
  rw [dist_zero_right, endpoint_norm]
  norm_num

/-- The primitive inner run uses actual objective ratios and actual constrained
model criticality; its initial derivative test fails strictly. -/
theorem inner_run : ConvexRegularization.Run oldMerit region settings (1 / 40) innerData 1 := by
  refine {
    accuracy_pos := by norm_num
    initial_parameter := rfl
    initial_mem := by simp [innerData, region]
    modelTrace := ?_
    feasible_trial := ?_
    model_test := ?_
    continues := ?_ }
  · refine {
      order_pos := by decide
      updates := ?_
      improvement := ?_
      ratio := ?_
      point_update := ?_ }
    · refine {
        min_pos := by norm_num [settings]
        min_le_initial := le_rfl
        eta1_pos := by norm_num [settings]
        eta1_le_eta2 := by norm_num [settings]
        eta2_lt_one := by norm_num [settings]
        gamma1_pos := by norm_num [settings]
        gamma1_lt_one := by norm_num [settings]
        one_lt_gamma2 := by norm_num [settings]
        gamma2_lt_gamma3 := by norm_num [settings]
        update := fun _ _ => by norm_num [innerData, settings] }
    · intro i hi
      have he : i = 0 := by omega
      subst i
      simpa only [innerData, ite_true] using model_improves
    · intro i hi
      have he : i = 0 := by omega
      subst i
      simpa only [innerData, ite_true] using actual_ratio.symm
    · intro i hi
      have he : i = 0 := by omega
      subst i
      norm_num [innerData, settings]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    simpa [innerData] using endpoint_mem
  · intro i hi
    have he : i = 0 := by omega
    subst i
    have hset : feasibleDisplacements region (0 : E) = region := by
      ext z
      simp
    have hz := constrainedCriticality_one_eq_zero_of_fderiv isClosed_closedBall
      endpoint_mem zero_le_one model_fderiv_zero
    simp only [innerData, ite_true, hset]
    change constrainedCriticality (model oldMerit 2 0 8) 1 region endpoint 1 ≤ _
    change constrainedCriticality (model oldMerit 2 0 8) 1 region endpoint 1 = 0 at hz
    rw [hz]
    norm_num [settings]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    have hh := old_criticalities.1
    change firstCriticality oldMerit region 0 = _ at hh
    change (1 / 40 : ℝ) < firstCriticality oldMerit region 0
    rw [hh]
    norm_num

/-- Exact actual residual norms at the start and the accepted endpoint. -/
theorem actual_residuals : ‖residual objective constraint (-1 / 2) (0 : E)‖ = 1 / 2 ∧
    ‖residual objective constraint (-1 / 2) endpoint‖ = 1 / 4 := by
  constructor <;> rw [residual_norm] <;>
    norm_num [objective, constraint, endpoint, vec]

/-- The actual Phase2 arrays retain the old target because the strict reset
guard fails at equality and the objective has not overshot that target. -/
noncomputable def outerData : Constrained.TwoPhase.Data E where
  point := fun k => if k = 0 then 0 else endpoint
  target := fun _ => -1 / 2
  inner := fun _ => innerData
  length := fun _ => 1

/-- Every literal two-phase rule is satisfied by the genuine one-trial inner run. -/
theorem literal_run : PhaseTwoRun false objective constraint region settings
    (1 / 2) (1 / 10) (1 / 2) outerData 1 := by
  refine {
    primal_pos := by norm_num
    primal_le_one := by norm_num
    dual_pos := by norm_num
    dual_le_one := by norm_num
    theta_pos := by norm_num
    theta_lt_one := by norm_num
    initial_mem := by simp [outerData, region]
    initial_constraint := by norm_num [outerData, constraint]
    initial_target := by norm_num [outerData, resetTarget, objective, constraint]
    inner_run := ?_
    inner_start := ?_
    inner_end := ?_
    inner_return := ?_
    inner_first := ?_
    target_update := ?_
    continues := fun k hk => by omega }
  · intro k hk
    have he : k = 0 := by omega
    subst k
    convert inner_run using 1 <;> norm_num [outerData, oldMerit]
  · intro k hk
    have he : k = 0 := by omega
    subst k
    rfl
  · intro k hk
    have he : k = 0 := by omega
    subst k
    simp [outerData, innerData]
  · intro k hk
    have he : k = 0 := by omega
    subst k
    apply Or.inl
    change ‖residual objective constraint (-1 / 2) endpoint‖ ≤ _
    rw [actual_residuals.2]
    norm_num
  · intro k hk i hi
    have he : k = 0 := by omega
    have hi0 : i = 0 := by simpa only [outerData] using Nat.lt_one_iff.mp hi
    subst k i
    change ¬InnerReturn objective constraint region (1 / 2) (1 / 10) (1 / 2)
      (-1 / 2) 0
    rw [InnerReturn, actual_residuals.1]
    change ¬((1 / 2 : ℝ) ≤ 1 / 2 * (1 / 2) ∨ objective 0 < -1 / 2 ∨
      firstCriticality oldMerit region 0 ≤ 1 / 10 * (1 / 2))
    rw [old_criticalities.1]
    norm_num [objective]
  · intro k hk
    have he : k = 0 := by omega
    subst k
    change (-1 / 2 : ℝ) = nextTarget false objective constraint (1 / 2) (1 / 2)
      (-1 / 2) endpoint
    have hn : ¬ResetGuard false objective constraint (1 / 2) (1 / 2)
        (-1 / 2) endpoint := by
      change ¬‖residual objective constraint (-1 / 2) endpoint‖ < _
      rw [actual_residuals.2]
      norm_num
    simp only [nextTarget, ite_eq_right hn]
    norm_num [objective, endpoint, vec]

/-- Literal Step2(c) terminates at the accepted endpoint. -/
theorem literal_stop : StopAfter false objective constraint region
    (1 / 2) (1 / 10) (1 / 2) (-1 / 2) endpoint := by
  left
  constructor
  · change ¬‖residual objective constraint (-1 / 2) endpoint‖ < _
    rw [actual_residuals.2]
    norm_num
  · norm_num [objective, endpoint, vec]

/-- The actual normalized merit derivative test is still false at termination. -/
theorem merit_test_fails : ¬MeritTarget objective constraint region
    (1 / 10) (-1 / 2) endpoint := by
  have hh := old_criticalities.2
  change firstCriticality (targetMerit objective constraint (-1 / 2)) region endpoint = _ at hh
  change ¬firstCriticality (targetMerit objective constraint (-1 / 2)) region endpoint ≤
    (1 / 10 : ℝ) * ‖residual objective constraint (-1 / 2) endpoint‖
  rw [actual_residuals.2, hh]
  norm_num

end Constrained.TwoPhase.Boundary
