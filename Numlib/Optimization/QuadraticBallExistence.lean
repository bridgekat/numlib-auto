import Numlib.Optimization.QuadraticSubproblem

/-!
# Finite-dimensional quadratic ball attainment

A continuous quadratic attains its minimum on every nonempty closed finite-dimensional ball.
-/

namespace Optimization.QuadraticSubproblem

/-- A quadratic objective attains its minimum on every nonempty finite-dimensional closed ball. -/
theorem exists_isMinOn_ball_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (g : E) (H : E →L[ℝ] E)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ s : E, ‖s‖ ≤ Δ ∧ IsMinOn (quadratic g H) {x | ‖x‖ ≤ Δ} s := by
  have hc : Continuous (quadratic g H) := by unfold quadratic; fun_prop
  have hb : {x : E | ‖x‖ ≤ Δ} = Metric.closedBall (0 : E) Δ := by
    ext x
    simp
  rw [hb]
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (isCompact_closedBall (0 : E) Δ).exists_isMinOn
    ⟨0, by simp [hΔ]⟩ hc.continuousOn

end Optimization.QuadraticSubproblem
