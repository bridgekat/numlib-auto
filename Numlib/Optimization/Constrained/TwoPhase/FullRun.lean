import Numlib.Optimization.Constrained.TwoPhase.Run
import Numlib.Optimization.Regularization.Convex.LeastSquares.Run

/-!
# A complete primitive two-phase execution prefix

A true ARpLE-CC feasibility call precedes the actual target-method calls.
The recorded Phase1 return uses its literal test; Phase2 is entered precisely
when the returned constraint residual passes the feasibility guard. The final
outer return need not be a stopping return in an execution prefix.
-/

namespace Constrained.TwoPhase
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- Primitive arrays for the feasibility call and subsequent target calls. -/
structure FullData (E : Type*) where
  phaseOne : ConvexRegularization.Data E
  phaseOneLength : ℕ
  phaseTwo : Data E
  phaseTwoLength : ℕ

/-- A genuine complete-method prefix uses the actual Phase1 residual-power
model and every actual Phase2 model. Only operational return and entry guards
are fields; no final approximate optimality or evaluation bound is assumed. -/
structure FullRun {p : ℕ} (closedReset : Bool) (f : E → ℝ) (c : E → F) (C : Set E)
    (P₁ P₂ : ConvexRegularization.Settings p) (ℓ ε₀ ε₁ θ : ℝ) 
    (D : FullData E) : Prop where
  primal_pos : 0 < ε₀
  primal_le_one : ε₀ ≤ 1
  dual_pos : 0 < ε₁
  dual_le_one : ε₁ ≤ 1
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  phaseOne_run : ConvexLeastSquares.Run c ℓ C P₁ (θ * ε₀) ε₁ D.phaseOne D.phaseOneLength
  phaseOne_return : ConvexLeastSquares.Stop c ℓ C (θ * ε₀) ε₁
    (D.phaseOne.point D.phaseOneLength)
  phaseTwo_start : D.phaseTwo.point 0 = D.phaseOne.point D.phaseOneLength
  phaseTwo_run : ‖c (D.phaseOne.point D.phaseOneLength)‖ ≤ θ * ε₀ →
    PhaseTwoRun closedReset f c C P₂ ε₀ ε₁ θ D.phaseTwo D.phaseTwoLength
  phaseOne_exit : θ * ε₀ < ‖c (D.phaseOne.point D.phaseOneLength)‖ → D.phaseTwoLength = 0

/-- A complete-method prefix terminates by the literal Phase1 exit or an
actual stopping return of its last Phase2 call. -/
def FullStop (closedReset : Bool) (f : E → ℝ) (c : E → F) (C : Set E)
    (ε₀ ε₁ θ : ℝ) (D : FullData E) : Prop :=
  θ * ε₀ < ‖c (D.phaseOne.point D.phaseOneLength)‖ ∨
    0 < D.phaseTwoLength ∧ StopAfter closedReset f c C ε₀ ε₁ θ
      (D.phaseTwo.target (D.phaseTwoLength - 1)) (D.phaseTwo.point D.phaseTwoLength)

/-- If the feasibility call fails the entry guard, no target call is executed. -/
theorem FullRun.no_phaseTwo_of_infeasible {p : ℕ} {closedReset : Bool}
    {f : E → ℝ} {c : E → F} {C : Set E} {P₁ P₂ : ConvexRegularization.Settings p}
    {ℓ ε₀ ε₁ θ : ℝ} {D : FullData E}
    (h : FullRun closedReset f c C P₁ P₂ ℓ ε₀ ε₁ θ D)
    (hn : ¬‖c (D.phaseOne.point D.phaseOneLength)‖ ≤ θ * ε₀) : D.phaseTwoLength = 0 :=
  h.phaseOne_exit (not_le.mp hn)

end Constrained.TwoPhase
