import Numlib.Optimization.HighOrder.Criticality

/-!
# Equality of Taylor criticality from equality of actual decrements

A pointwise equality of actual Taylor decrements identifies their supremum on
the same displacement ball, independently of radius sign or attainment.
-/

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equal actual Taylor decrements have equal criticality on every common ball. -/
theorem criticality_eq_of_decrement_eq {f g : E → ℝ} {p q : ℕ} {x y : E}
    (h : ∀ d : E, decrement f p x d = decrement g q y d) (δ : ℝ) :
    criticality f p x δ = criticality g q y δ := by
  unfold criticality
  rw [funext h]

end TaylorModel
