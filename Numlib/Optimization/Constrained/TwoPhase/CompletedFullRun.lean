import Numlib.Optimization.Constrained.TwoPhase.CompletedReturn
import Numlib.Optimization.LeastNorm.Run


/-!
# Complete two-phase executions with completed inner calls

Actual feasibility and target calls use the constructed all-order constrained
solver. Entry and return guards are recorded separately from derived certificates
and evaluation counts. The inner absolute tolerances are fixed before the calls.
-/

namespace Constrained.TwoPhase
open Set InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual complete Phase1 constrained execution arrays and subsequent completed-inner Phase2
arrays. -/
structure CompletedFullData (E : Type*) (q : ℕ) where
  phaseOne : ConstrainedRegularization.ExecutionData E q
  phaseOneLength : ℕ
  phaseTwo : CompletedData E q
  phaseTwoLength : ℕ

variable {F : Type*} [NormedAddCommGroup F]
/-- A complete two-phase repair: actual true-target Phase1 run at absolute inner accuracies,
unit initial radii, actual entry guard, actual completed Phase2 runs and no Phase2 calls on
an infeasible Phase1 exit. No output certificate or count is a field. -/
structure CompletedFullRun {p q : ℕ} (f : E → ℝ) (c : E → F) (X : Set E)
    (P₁ P₂ : ConstrainedRegularization.Settings p q) (β θ ε₀ L : ℝ)
    (ε : Fin q → ℝ) (D : CompletedFullData E q) : Prop where
  margin_pos : 0 < β
  margin_lt_one : β < 1
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  primal_pos : 0 < ε₀
  primal_le_one : ε₀ ≤ 1
  dual_pos : ∀ a, 0 < ε a
  dual_le_one : ∀ a, ε a ≤ 1
  phaseOne_run : ConstrainedRegularization.Run (LeastNorm.merit c) X P₁
    (completedInnerAccuracy β θ ε₀ ε) D.phaseOne D.phaseOneLength
  phaseOne_target : ConstrainedRegularization.TargetAt (LeastNorm.merit c) X P₁
    (completedInnerAccuracy β θ ε₀ ε) D.phaseOne D.phaseOneLength
  phaseOne_first : ∀ i < D.phaseOneLength, ¬ConstrainedRegularization.TargetAt
    (LeastNorm.merit c) X P₁ (completedInnerAccuracy β θ ε₀ ε) D.phaseOne i
  phaseOne_radius : ∀ a, D.phaseOne.radius 0 a = 1
  phaseTwo_start : D.phaseTwo.point 0 = D.phaseOne.point D.phaseOneLength
  phaseTwo_run : ‖c (D.phaseOne.point D.phaseOneLength)‖ ≤ θ * ε₀ →
    CompletedRun f c X P₂ β θ ε₀ L ε D.phaseTwo D.phaseTwoLength
  phaseOne_exit : θ * ε₀ < ‖c (D.phaseOne.point D.phaseOneLength)‖ → D.phaseTwoLength = 0

/-- Actual full-method stop: infeasible Phase1 return or the final completed Phase2 stopping
guard. -/
def CompletedFullStop {p q : ℕ} (f : E → ℝ) (c : E → F) (X : Set E)
    (P : ConstrainedRegularization.Settings p q) (β θ ε₀ L : ℝ) (ε : Fin q → ℝ)
    (D : CompletedFullData E q) : Prop :=
  θ * ε₀ < ‖c (D.phaseOne.point D.phaseOneLength)‖ ∨
    0 < D.phaseTwoLength ∧
      CompletedStopAfter f c X P β θ ε₀ L ε D.phaseTwo (D.phaseTwoLength - 1)

namespace CompletedFullRun
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {X : Set E}
  {P₁ P₂ : ConstrainedRegularization.Settings p q} {β θ ε₀ L : ℝ}
  {ε : Fin q → ℝ} {D : CompletedFullData E q}

/-- A genuine Phase1 true-target return yields legal radii and actual constraint-violation
Taylor certificates; an infeasible exit makes the absolute inner accuracies imply normalized
source certificates. -/
theorem phaseOne_certificate (h : CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D)
    (hX : IsClosed X) (hc : ContDiff ℝ p (LeastNorm.merit c))
    (hi : θ * ε₀ < ‖c (D.phaseOne.point D.phaseOneLength)‖) :
    ∃ δ : Fin q → ℝ, D.phaseOne.point D.phaseOneLength ∈ X ∧
      (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧ ∀ a,
        TaylorModel.constrainedCriticality (LeastNorm.merit c) (modelOrder a) X
          (D.phaseOne.point D.phaseOneLength) (δ a) ≤
          ε a * ‖c (D.phaseOne.point D.phaseOneLength)‖ *
            δ a ^ modelOrder a / (modelOrder a).factorial := by
  obtain ⟨δ, hopt⟩ := h.phaseOne_run.target_optimality hX hc.contDiffAt h.phaseOne_target
  refine ⟨δ, hopt.1, hopt.2.1, fun a => (hopt.2.2 a).trans ?_⟩
  have hb : β * (θ * ε₀) ≤ ‖c (D.phaseOne.point D.phaseOneLength)‖ :=
    (mul_le_of_le_one_left (mul_pos h.theta_pos h.primal_pos).le
      h.margin_lt_one.le).trans hi.le
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ ε a * δ a ^ modelOrder a / (modelOrder a).factorial by
      have := h.dual_pos a; have := (hopt.2.1 a).1; positivity)
  simpa only [completedInnerAccuracy] using (show β * θ * ε₀ * ε a *
    δ a ^ modelOrder a / (modelOrder a).factorial ≤ _ by convert hh using 1 <;> ring)
end CompletedFullRun
end Constrained.TwoPhase
