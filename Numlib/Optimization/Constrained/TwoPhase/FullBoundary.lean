import Numlib.Optimization.Constrained.TwoPhase.FullRun
import Numlib.Optimization.Constrained.TwoPhase.BoundaryRegularity

/-!
# A complete two-phase execution with an uncertified literal return

The equality-boundary example includes its genuine zero-trial feasibility
execution. It then performs one actual accepted target-model trial and stops
through the literal fallback branch. Thus the full-method first-order
certificate can fail under all source problem assumptions, regardless of any
evaluation budget.
-/

namespace Constrained.TwoPhase.Boundary
open Set ConvexRegularization

/-- The initially feasible example has a genuine zero-trial ARpLE-CC execution. -/
theorem phaseOne_run : ConvexLeastSquares.Run constraint 2 region settings
    (1 / 4) (1 / 10) innerData 0 := by
  refine {
    residual_order := by norm_num
    accuracy_global_pos := by norm_num
    accuracy_first_pos := by norm_num
    initial_parameter := rfl
    initial_mem := by simp [innerData, region]
    trace := ?_
    feasible_trial := by intro i hi; omega
    model_test := by intro i hi; omega
    continues := by intro i hi; omega }
  exact {
    order_pos := by decide
    updates := (inner_run.modelTrace.restrict (by omega : 0 ≤ 1)).updates
    improvement := by intro i hi; omega
    ratio := by intro i hi; omega
    point_update := by intro i hi; omega }

/-- The complete-method arrays include the genuine feasibility call and target call. -/
noncomputable def fullData : FullData E where
  phaseOne := innerData
  phaseOneLength := 0
  phaseTwo := outerData
  phaseTwoLength := 1

/-- Every primitive rule of the complete literal method holds. -/
theorem full_run : FullRun false objective constraint region settings settings 2
    (1 / 2) (1 / 10) (1 / 2) fullData := by
  refine {
    primal_pos := by norm_num
    primal_le_one := by norm_num
    dual_pos := by norm_num
    dual_le_one := by norm_num
    theta_pos := by norm_num
    theta_lt_one := by norm_num
    phaseOne_run := ?_
    phaseOne_return := ?_
    phaseTwo_start := rfl
    phaseTwo_run := fun _ => literal_run
    phaseOne_exit := ?_ }
  · convert phaseOne_run using 1 <;> norm_num [fullData]
  · apply Or.inl
    norm_num [fullData, innerData, constraint]
  · intro hn
    norm_num [fullData, innerData, constraint] at hn

/-- The actual final complete-method return satisfies the literal stopping guard. -/
theorem full_stop : FullStop false objective constraint region
    (1 / 2) (1 / 10) (1 / 2) fullData :=
  Or.inr ⟨by norm_num [fullData], literal_stop⟩

/-- The full actual method terminates at a feasible point where every multiplier
fails the required normalized Lagrangian criticality inequality. -/
theorem full_certificate_fails :
    ‖constraint (fullData.phaseTwo.point fullData.phaseTwoLength)‖ = 0 ∧
      ¬∃ y : ℝ, firstCriticality (Constrained.vectorLagrangian objective constraint y)
        region (fullData.phaseTwo.point fullData.phaseTwoLength) ≤
          (1 / 10 : ℝ) * Constrained.multiplierNorm y := by
  change ‖constraint endpoint‖ = 0 ∧ _
  exact ⟨by norm_num [constraint, endpoint, vec], no_multiplier⟩

end Constrained.TwoPhase.Boundary

namespace Constrained.TwoPhase.Boundary
open Constrained
/-- Neither infeasible stopping alternative nor any scaled Lagrangian
alternative in the final source complexity theorem holds at the actual return. -/
theorem all_certificates_fail :
    ¬((firstCriticality feasibilityMerit region endpoint ≤
          (1 / 10 : ℝ) * ‖constraint endpoint‖ ∧
        (1 / 2 : ℝ) * (1 / 2) < ‖constraint endpoint‖) ∨
      (firstCriticality feasibilityMerit region endpoint ≤
          (1 / 10 : ℝ) * ‖constraint endpoint‖ ∧
        (1 / 2 : ℝ) * (1 / 2) < ‖constraint endpoint‖) ∨
      ∃ y : ℝ, firstCriticality (vectorLagrangian objective constraint y) region endpoint ≤
        (1 / 10 : ℝ) * multiplierNorm y ∧ ‖constraint endpoint‖ ≤ (1 / 2 : ℝ)) := by
  have hc : ‖constraint endpoint‖ = 0 := by norm_num [constraint, endpoint, vec]
  rintro (h | h | ⟨y, hy, _⟩)
  · rw [hc] at h
    norm_num at h
  · rw [hc] at h
    norm_num at h
  · exact no_multiplier ⟨y, hy⟩
end Constrained.TwoPhase.Boundary
