import Numlib.Optimization.QuadraticSubproblem

/-!
# Associated trust-region multipliers

The associated multiplier carries precisely primal feasibility, nonnegativity,
shifted stationarity, positive semidefiniteness, and common-radius complementarity.
These are equivalent to feasible global quadratic minimization on a positive-radius ball.
-/

noncomputable section
open Set Metric
namespace Optimization.QuadraticSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The necessary and sufficient shifted optimality conditions for a quadratic trust region. -/
structure TrustRegionShiftConditions (g : E) (H : E →L[ℝ] E) (delta lambda : ℝ)
    (s : E) : Prop where
  /-- The step is feasible. -/
  feasible : ‖s‖ ≤ delta
  /-- The multiplier is nonnegative. -/
  nonneg : 0 ≤ lambda
  /-- The actual shifted model gradient vanishes. -/
  stationary : g + H s + lambda • s = 0
  /-- The actual Hessian shift is positive semidefinite. -/
  positive : (H + lambda • ContinuousLinearMap.id ℝ E).IsPositive
  /-- Complementarity with the common radius. -/
  complementary : lambda * (‖s‖ ^ 2 - delta ^ 2) = 0

/-- Conjunctive characterization of associated trust-region shift conditions. -/
theorem TrustRegionShiftConditions.iff {g : E} {H : E →L[ℝ] E} {delta lambda : ℝ} {s : E} :
    TrustRegionShiftConditions g H delta lambda s ↔
      ‖s‖ ≤ delta ∧ 0 ≤ lambda ∧ g + H s + lambda • s = 0 ∧
        (H + lambda • ContinuousLinearMap.id ℝ E).IsPositive ∧
          lambda * (‖s‖ ^ 2 - delta ^ 2) = 0 := by
  constructor
  · intro h
    exact ⟨h.feasible, h.nonneg, h.stationary, h.positive, h.complementary⟩
  · rintro ⟨hf, hn, hs, hp, hc⟩
    exact ⟨hf, hn, hs, hp, hc⟩

/-- Feasible global minimization on a positive-radius ball is equivalent to the existence
of an associated multiplier satisfying the bundled shift conditions. -/
theorem isMinOn_ball_iff_exists_shiftConditions {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {delta : ℝ} (hdelta : 0 < delta) {s : E} :
    (‖s‖ ≤ delta ∧ IsMinOn (quadratic g H) (closedBall 0 delta) s) ↔
      ∃ lambda, TrustRegionShiftConditions g H delta lambda s := by
  simpa only [TrustRegionShiftConditions.iff, exists_and_left] using
    isMinOn_ball_iff_shift hH hdelta (s := s)

end Optimization.QuadraticSubproblem
