import Numlib.Optimization.Constrained.TwoPhase.CompletedBudget
import Numlib.Optimization.Constrained.TwoPhase.CompletedExecution
import Numlib.Optimization.Constrained.TwoPhase.CompletedFullRun

/-!
# Actual full completed-inner two-phase evaluation budgets

The feasibility call spends its actual initialized constrained-solver budget.
The bounded target interval pays for all completed Phase2 calls. Summing both
phases counts every initialization, including a first or terminal return.
-/

namespace Constrained.TwoPhase
open Set InexactTrustRegion
open HighOrderRegularization (parameterCap)

/-- Explicit initialized feasibility-call budget using its true starting residual. -/
noncomputable def completedPhaseOneBudget {p q : ℕ}
    (P : ConstrainedRegularization.Settings p q)
    (L β θ ε₀ r₀ : ℝ) (ε : Fin q → ℝ) : ℝ :=
  HighOrderRegularization.trialCountFactor P *
    (r₀ ^ 2 / (2 * ConstrainedRegularization.commonDecreaseCoefficient P L
      (parameterCap P L) * ConstrainedRegularization.accuracyFactor P
        (completedInnerAccuracy β θ ε₀ ε)) + 1) +
          |HighOrderRegularization.trialCountOffset P L| + 1

/-- Actual initialized function evaluations over the two complete phases. -/
def completedFullFunctionEvaluations {E : Type*} {q : ℕ}
    (D : CompletedFullData E q) : ℕ :=
  (D.phaseOneLength + 1) + completedFunctionEvaluations D.phaseTwo D.phaseTwoLength

/-- Actual initialized per-order derivative evaluations over the two phases. -/
noncomputable def completedFullDerivativeEvaluations {E : Type*} {p q : ℕ}
    (P₁ P₂ : ConstrainedRegularization.Settings p q) (D : CompletedFullData E q) : ℕ :=
  ((EvaluationComplexity.successfulIterations {i | P₁.eta1 ≤ D.phaseOne.ratio i}
    D.phaseOneLength).card + 1) + completedDerivativeEvaluations P₂ D.phaseTwo D.phaseTwoLength

/-- Every actual initialized derivative schedule is bounded by its true
initialized function schedule in both phases. -/
theorem completedFullDerivativeEvaluations_le_functions {E : Type*} {p q : ℕ}
    (P₁ P₂ : ConstrainedRegularization.Settings p q) (D : CompletedFullData E q) :
    completedFullDerivativeEvaluations P₁ P₂ D ≤ completedFullFunctionEvaluations D := by
  unfold completedFullDerivativeEvaluations completedFullFunctionEvaluations
  apply Nat.add_le_add
  · apply Nat.add_le_add_right
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  · exact completedDerivativeEvaluations_le_functions P₂ D.phaseTwo D.phaseTwoLength

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace CompletedFullRun
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {X : Set E}
  {P₁ P₂ : ConstrainedRegularization.Settings p q} {β θ ε₀ L : ℝ}
  {ε : Fin q → ℝ} {D : CompletedFullData E q}

omit [InnerProductSpace ℝ F] in
/-- Every actual completed feasibility call spends its derived initialized
least-squares budget, with no assumed cap or count. -/
theorem phaseOne_iterations_le (h : CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D)
    (hX : IsClosed X) (hν : ContDiff ℝ p (LeastNorm.merit c)) {L₁ : ℝ} (hL₁ : 1 ≤ L₁)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i (LeastNorm.merit c) y -
        iteratedFDeriv ℝ i (LeastNorm.merit c) z‖ ≤ L₁ * ‖y - z‖) :
    ((D.phaseOneLength + 1 : ℕ) : ℝ) ≤ completedPhaseOneBudget P₁ L₁ β θ ε₀
      ‖c (D.phaseOne.point 0)‖ ε := by
  have hr := h.phaseOne_run
  have ht := hr.iterations_le hX hν hL₁ hlip
    (fun z _ => by unfold LeastNorm.merit; positivity) h.phaseOne_first
  have hc := ConstrainedRegularization.commonDecreaseCoefficient_pos P₁ hL₁
    (HighOrderRegularization.parameterCap_pos P₁ L₁).le
  have ha := ConstrainedRegularization.accuracyFactor_pos P₁ hr.accuracy_pos
  unfold completedPhaseOneBudget
  simp only [LeastNorm.merit, sub_zero, div_div, mul_assoc] at ht ⊢
  push_cast
  have hoff := le_abs_self (HighOrderRegularization.trialCountOffset P₁ L₁)
  linarith only [ht, hoff]

/-- Explicit initialized cost of both actual phases. The positive part of the
target interval also covers an infeasible Phase1 exit with no Phase2 calls. -/
theorem total_evaluations_le (h : CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D)
    {L₁ B flow fup : ℝ} (hL₁ : 1 ≤ L₁)
    (hν : ContDiff ℝ p (LeastNorm.merit c))
    (hlipν : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i (LeastNorm.merit c) y -
        iteratedFDeriv ℝ i (LeastNorm.merit c) z‖ ≤ L₁ * ‖y - z‖)
    (A : CompletedRegularity f c X p q L B flow fup) :
    (completedFullFunctionEvaluations D : ℝ) ≤
      completedPhaseOneBudget P₁ L₁ β θ ε₀ ‖c (D.phaseOne.point 0)‖ ε +
        (max 0 (fup - flow + 1) / completedDropFloor P₂ L β θ B ε₀ ε + 1) *
          completedInnerBudget P₂ L β θ ε₀ ε ∧
    (completedFullDerivativeEvaluations P₁ P₂ D : ℝ) ≤
      completedPhaseOneBudget P₁ L₁ β θ ε₀ ‖c (D.phaseOne.point 0)‖ ε +
        (max 0 (fup - flow + 1) / completedDropFloor P₂ L β θ B ε₀ ε + 1) *
          completedInnerBudget P₂ L β θ ε₀ ε := by
  have h₁ := h.phaseOne_iterations_le A.closed hν hL₁ hlipν
  simp only [Nat.cast_add, Nat.cast_one] at h₁
  have hd := completedDropFloor_pos P₂ A.one_le_constant h.margin_pos h.margin_lt_one
    h.theta_pos h.theta_lt_one A.derivative_bound_pos h.primal_pos h.dual_pos
  have hi := completedInnerBudget_pos P₂ A.one_le_constant h.margin_pos h.theta_pos
    h.primal_pos h.dual_pos
  have h₂ : (completedFunctionEvaluations D.phaseTwo D.phaseTwoLength : ℝ) ≤
      (max 0 (fup - flow + 1) / completedDropFloor P₂ L β θ B ε₀ ε + 1) *
        completedInnerBudget P₂ L β θ ε₀ ε := by
    by_cases he : ‖c (D.phaseOne.point D.phaseOneLength)‖ ≤ θ * ε₀
    · have hb := ((h.phaseTwo_run he).total_inner_evaluations_le A).1
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ hi.le
      have hh := div_le_div_of_nonneg_right (le_max_right 0 (fup - flow + 1)) hd.le
      linarith only [hh]
    · rw [h.phaseOne_exit (lt_of_not_ge he), completedFunctionEvaluations]
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
      positivity
  have hb : (completedFullFunctionEvaluations D : ℝ) ≤
      completedPhaseOneBudget P₁ L₁ β θ ε₀ ‖c (D.phaseOne.point 0)‖ ε +
        (max 0 (fup - flow + 1) / completedDropFloor P₂ L β θ B ε₀ ε + 1) *
          completedInnerBudget P₂ L β θ ε₀ ε := by
    unfold completedFullFunctionEvaluations
    push_cast
    exact add_le_add h₁ h₂
  refine ⟨hb, ?_⟩
  have he : (completedFullDerivativeEvaluations P₁ P₂ D : ℝ) ≤
      completedFullFunctionEvaluations D := by
    exact_mod_cast completedFullDerivativeEvaluations_le_functions P₁ P₂ D
  exact he.trans hb

end CompletedFullRun

/-- Actual constructed feasibility and target calls reach a full repaired
stopping return within explicit initialized function and derivative budgets.
No execution availability, stopping index or cost estimate is an assumption. -/
theorem exists_completed_full_complexity {p q : ℕ} (f : E → ℝ) (c : E → F) (X : Set E)
    (P₁ P₂ : ConstrainedRegularization.Settings p q) {L L₁ B flow fup : ℝ}
    (A : CompletedRegularity f c X p q L B flow fup) (hL₁ : 1 ≤ L₁)
    (hlipν : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i (LeastNorm.merit c) y -
        iteratedFDeriv ℝ i (LeastNorm.merit c) z‖ ≤ L₁ * ‖y - z‖)
    (x₀ : E) (hx₀ : x₀ ∈ X) {β θ ε₀ : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (ε : Fin q → ℝ)
    (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1) :
    ∃ D : CompletedFullData E q, D.phaseOne.point 0 = x₀ ∧
      CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D ∧
      CompletedFullStop f c X P₂ β θ ε₀ L ε D ∧
      (completedFullFunctionEvaluations D : ℝ) ≤
        completedPhaseOneBudget P₁ L₁ β θ ε₀ ‖c x₀‖ ε +
          (max 0 (fup - flow + 1) / completedDropFloor P₂ L β θ B ε₀ ε + 1) *
            completedInnerBudget P₂ L β θ ε₀ ε ∧
      (completedFullDerivativeEvaluations P₁ P₂ D : ℝ) ≤
        completedPhaseOneBudget P₁ L₁ β θ ε₀ ‖c x₀‖ ε +
          (max 0 (fup - flow + 1) / completedDropFloor P₂ L β θ B ε₀ ε + 1) *
            completedInnerBudget P₂ L β θ ε₀ ε := by
  classical
  have hν : ContDiff ℝ p (LeastNorm.merit c) :=
    (A.smooth_constraint.norm_sq (𝕜 := ℝ)).div_const 2
  have hα : ∀ a, 0 < completedInnerAccuracy β θ ε₀ ε a ∧
      completedInnerAccuracy β θ ε₀ ε a ≤ 1 := by
    intro a
    dsimp only [completedInnerAccuracy]
    refine ⟨by have := (hε a).1; positivity, ?_⟩
    have hbt : β * θ ≤ 1 := (mul_le_of_le_one_left hθ.le hβ1.le).trans hθ1.le
    have hbte : β * θ * ε₀ ≤ 1 := (mul_le_of_le_one_left hε₀.le hbt).trans hε₀1
    exact (mul_le_of_le_one_left (hε a).1.le hbte).trans (hε a).2
  obtain ⟨_, _, _, _, _, _, hcall⟩ := ConstrainedRegularization.exists_certified_execution
    (LeastNorm.merit c) X A.closed A.convex P₁ x₀ hx₀ hν hL₁ hlipν
      (fun z _ => by unfold LeastNorm.merit; positivity)
  obtain ⟨D₁, K₁, _, hx₁, _, hδ₁, hr₁, ht₁, hfirst₁, _, _, _, _⟩ :=
    hcall (completedInnerAccuracy β θ ε₀ ε) hα
  have hxend := hr₁.point_mem le_rfl
  have hfinish (D : CompletedFullData E q) (hinit : D.phaseOne.point 0 = x₀)
      (hr : CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D)
      (hs : CompletedFullStop f c X P₂ β θ ε₀ L ε D) :
      ∃ D : CompletedFullData E q, D.phaseOne.point 0 = x₀ ∧
        CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D ∧
        CompletedFullStop f c X P₂ β θ ε₀ L ε D ∧
        (completedFullFunctionEvaluations D : ℝ) ≤
          completedPhaseOneBudget P₁ L₁ β θ ε₀ ‖c x₀‖ ε +
            (max 0 (fup - flow + 1) / completedDropFloor P₂ L β θ B ε₀ ε + 1) *
              completedInnerBudget P₂ L β θ ε₀ ε ∧
        (completedFullDerivativeEvaluations P₁ P₂ D : ℝ) ≤
          completedPhaseOneBudget P₁ L₁ β θ ε₀ ‖c x₀‖ ε +
            (max 0 (fup - flow + 1) / completedDropFloor P₂ L β θ B ε₀ ε + 1) *
              completedInnerBudget P₂ L β θ ε₀ ε := by
    have hb := hr.total_evaluations_le hL₁ hν hlipν A
    rw [hinit] at hb
    exact ⟨D, hinit, hr, hs, hb.1, hb.2⟩
  by_cases he : ‖c (D₁.point K₁)‖ ≤ θ * ε₀
  · obtain ⟨D₂, hx₂, hprefix⟩ := exists_completed_execution f c X A.closed A.convex P₂
      hβ hβ1 hθ hθ1 hε₀ hε₀1 A.one_le_constant A.objective_band A.merit_regularity
        ε hε (D₁.point K₁) hxend he
    obtain ⟨k, hs, _, hr₂, _⟩ := exists_completed_stop A hprefix
    let D : CompletedFullData E q := ⟨D₁, K₁, D₂, k + 1⟩
    have hr : CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D := {
      margin_pos := hβ
      margin_lt_one := hβ1
      theta_pos := hθ
      theta_lt_one := hθ1
      primal_pos := hε₀
      primal_le_one := hε₀1
      dual_pos := fun a => (hε a).1
      dual_le_one := fun a => (hε a).2
      phaseOne_run := hr₁
      phaseOne_target := ht₁
      phaseOne_first := hfirst₁
      phaseOne_radius := hδ₁
      phaseTwo_start := hx₂
      phaseTwo_run := fun _ => hr₂
      phaseOne_exit := fun hi => False.elim ((not_lt_of_ge he) hi) }
    have hstop : CompletedFullStop f c X P₂ β θ ε₀ L ε D := by
      apply Or.inr
      exact ⟨by dsimp [D]; omega, by simpa only [D, Nat.add_sub_cancel] using hs⟩
    exact hfinish D hx₁ hr hstop
  · let D₂ : CompletedData E q := {
      point := fun _ => D₁.point K₁
      target := fun _ => resetTarget f c ε₀ (D₁.point K₁)
      inner := fun _ => D₁
      length := fun _ => 0 }
    let D : CompletedFullData E q := ⟨D₁, K₁, D₂, 0⟩
    have hr : CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D := {
      margin_pos := hβ
      margin_lt_one := hβ1
      theta_pos := hθ
      theta_lt_one := hθ1
      primal_pos := hε₀
      primal_le_one := hε₀1
      dual_pos := fun a => (hε a).1
      dual_le_one := fun a => (hε a).2
      phaseOne_run := hr₁
      phaseOne_target := ht₁
      phaseOne_first := hfirst₁
      phaseOne_radius := hδ₁
      phaseTwo_start := rfl
      phaseTwo_run := fun hi => False.elim (he hi)
      phaseOne_exit := fun _ => rfl }
    exact hfinish D hx₁ hr (Or.inl (lt_of_not_ge he))

end Constrained.TwoPhase
