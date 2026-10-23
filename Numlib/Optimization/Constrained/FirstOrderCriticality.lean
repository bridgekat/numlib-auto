import Numlib.Optimization.HighOrder.ConstrainedCriticality
import Numlib.Optimization.HighOrder.CriticalityApproximate

/-!
# First-order criticality on actual feasible displacement balls

At an interior ball the constrained and unrestricted Taylor criticalities
coincide. A zero genuine derivative gives zero constrained first-order
criticality at every feasible point, without a constraint qualification.
-/

namespace TaylorModel
open Set Metric
variable {E : Type*} [NormedAddCommGroup E]

/-- If every displacement in the testing ball is feasible, restricting that
ball to actual feasible displacements leaves it unchanged. -/
theorem feasibleDisplacements_inter_eq_closedBall {X : Set E} {x : E} {δ : ℝ}
    (hball : ∀ d, ‖d‖ ≤ δ → x + d ∈ X) :
    feasibleDisplacements X x ∩ closedBall 0 δ = closedBall 0 δ := by
  ext d
  constructor
  · exact fun h => h.2
  · intro hd
    exact ⟨hball d (by simpa using hd), hd⟩

section Normed
variable [NormedSpace ℝ E]

/-- Feasible containment of the testing ball gives unrestricted criticality. -/
theorem constrainedCriticality_eq_of_ball {X : Set E} {x : E} {δ : ℝ}
    (hball : ∀ d, ‖d‖ ≤ δ → x + d ∈ X) (f : E → ℝ) (p : ℕ) :
    constrainedCriticality f p X x δ = criticality f p x δ := by
  rw [constrainedCriticality, feasibleDisplacements_inter_eq_closedBall hball, criticality]

/-- Identical genuine derivatives give identical constrained first-order
criticality, independently of objective values or regularity elsewhere. -/
theorem constrainedCriticality_one_congr_fderiv {f g : E → ℝ} {x : E}
    (h : fderiv ℝ f x = fderiv ℝ g x) (C : Set E) (δ : ℝ) :
    constrainedCriticality f 1 C x δ = constrainedCriticality g 1 C x δ := by
  have hd : decrement f 1 x = decrement g 1 x := by
    funext d
    simp [decrement_eq, eval_eq_sum, Finset.sum_range_succ,
      iteratedFDeriv_one_apply, smul_eq_mul, h]
  rw [constrainedCriticality, constrainedCriticality, hd]

end Normed

variable [InnerProductSpace ℝ E] [ProperSpace E]

/-- A genuinely zero objective derivative gives zero constrained first-order
criticality on any closed feasible set. -/
theorem constrainedCriticality_one_eq_zero_of_fderiv {f : E → ℝ} {X : Set E}
    (hX : IsClosed X) {x : E} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : fderiv ℝ f x = 0) : constrainedCriticality f 1 X x δ = 0 := by
  apply (constrainedCriticality_eq_zero_iff f 1 hX hx hδ).mpr
  intro d _ _
  rw [decrement_one, inner_gradient_left, hf]
  simp

/-- At a feasible testing ball, the actual first-order constrained criticality
is exactly its radius times the genuine gradient norm. -/
theorem constrainedCriticality_one_eq_norm_of_ball
    {X : Set E} {x : E} {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ d, ‖d‖ ≤ δ → x + d ∈ X) (f : E → ℝ) :
    constrainedCriticality f 1 X x δ = δ * ‖gradient f x‖ := by
  rw [constrainedCriticality_eq_of_ball hball, criticality_one f x hδ]

end TaylorModel
