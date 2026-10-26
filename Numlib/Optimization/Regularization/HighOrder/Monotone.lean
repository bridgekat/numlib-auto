import Numlib.Optimization.Regularization.HighOrder.Parameter

/-!
# Objective monotonicity of actual regularization traces

The true ratio and strict model improvement give decrease on acceptance;
rejection preserves the point. Every finite actual prefix is nonincreasing.
-/

namespace HighOrderRegularization.ModelTrace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {p : ℕ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ} {N : ℕ}

/-- Every actual accepted or rejected update is objective nonincreasing. -/
theorem objective_succ_le
    (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N) {k : ℕ} (hk : k < N) :
    f (x (k + 1)) ≤ f (x k) := by
  by_cases hs : η₁ ≤ ρ k
  · have hh := h.successful_decrease hk hs
    have hz : 0 ≤ η₁ * σmin / (p + 1).factorial * ‖s k‖ ^ (p + 1) := by
      have hη := h.updates.eta1_pos
      have hσ := h.updates.min_pos
      positivity
    linarith
  · rw [h.point_update k hk, ite_eq_right hs]

/-- The genuine objective cannot increase between any two ordered prefix indices. -/
theorem objective_le (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : f (x j) ≤ f (x i) := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih => exact (h.objective_succ_le (by omega)).trans (ih (by omega))

end HighOrderRegularization.ModelTrace
