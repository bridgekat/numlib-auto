import Numlib.Optimization.Regularization.Inexact.Parameter

/-!
# Reference model decreases bound computed Taylor decreases

A nonnegative regularization penalty and the actual model comparison transfer
the decrease at a reference point to the computed Taylor decrement of the trial.
-/

namespace InexactRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual model comparison transfers the reference gap to the computed Taylor decrement. -/
theorem reference_gap_le_computed_decrement {A : FormalMultilinearSeries ℝ E ℝ}
    {p : ℕ} {σ : ℝ} {reference s : E} (hσ : 0 ≤ σ)
    (hc : model A p σ s ≤ model A p σ reference) :
    model A p σ 0 - model A p σ reference ≤ TaylorModel.jetDecrement A p s := by
  change model A p σ 0 - model A p σ reference ≤
    TaylorModel.ofJet A p 0 - TaylorModel.ofJet A p s
  unfold model ModelDecrease.penalized at hc ⊢
  simp only [norm_zero, zero_pow (Nat.succ_ne_zero p), mul_zero, add_zero]
  have hp : 0 ≤ σ / (p + 1).factorial * ‖s‖ ^ (p + 1) := by positivity
  linarith
end InexactRegularization
