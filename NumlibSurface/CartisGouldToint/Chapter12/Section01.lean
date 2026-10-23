import Numlib.Optimization.HighOrder.Criticality

/-!
# Cartis–Gould–Toint, Section 12.1: high-order criticality

The criticality measure (12.1.10) is the largest decrease of the genuine Taylor polynomial
on a closed ball. The supremum is attained for nonnegative radii in finite dimension,
as proved in the backbone. This formulation also permits radius zero.
-/

namespace CartisGouldToint

/-- The Taylor criticality measure `φ_{f,j}^δ(x)` of equation (12.1.10), the maximum of
`f(x)-T_{f,j}(x,s)` over `‖s‖ ≤ δ`. The polynomial uses the actual derivative tensors of `f`. -/
noncomputable def highOrderCriticality {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (j : ℕ) (x : E) (δ : ℝ) : ℝ :=
  TaylorModel.criticality f j x δ

/-- Zero Taylor criticality is equivalent to every feasible model decrement being nonpositive. -/
theorem highOrderCriticality_eq_zero_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (f : E → ℝ) (j : ℕ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    highOrderCriticality f j x δ = 0 ↔
      ∀ s : E, ‖s‖ ≤ δ → TaylorModel.decrement f j x s ≤ 0 :=
  TaylorModel.criticality_eq_zero_iff f j x hδ

end CartisGouldToint
