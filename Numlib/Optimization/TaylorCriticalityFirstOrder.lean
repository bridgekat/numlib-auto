import Numlib.Optimization.TaylorOptimality

/-!
# Exact first-order Taylor criticality

The first Taylor decrement on a norm ball has a gap equal to its radius times the operator
norm of the derivative. No compactness or properness hypothesis is needed.
-/

namespace Optimization.TaylorCriticality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first-order Taylor gap on a nonnegative-radius ball is exactly the radius times
the operator norm of the derivative. -/
theorem gapOn_taylorDecrement_one (f : E → ℝ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    gapOn (taylorDecrement f 1 x) (Metric.closedBall 0 δ) = δ * ‖fderiv ℝ f x‖ := by
  have he : taylorDecrement f 1 x = fun d => -fderiv ℝ f x d := by
    funext d
    exact taylorDecrement_one f x d
  rw [he, gapOn_norm_linear _ hδ]

end Optimization.TaylorCriticality
