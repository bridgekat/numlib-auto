import Numlib.Optimization.Descent
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# A lower objective point from a nonzero gradient

A differentiable objective cannot have a global minimum at a point with nonzero
gradient. The resulting strict objective gap can be fixed before algorithmic
accuracies or a choice of global lower bound.
-/

namespace Descent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A nonzero gradient at a differentiable point gives a point with strictly
smaller objective value. -/
theorem exists_lt_of_gradient_ne_zero {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : gradient f x ≠ 0) : ∃ y, f y < f x := by
  by_contra hn
  push Not at hn
  have hm : IsLocalMin f x := Filter.Eventually.of_forall hn
  have hd := hm.hasFDerivAt_eq_zero hf.hasFDerivAt
  apply hg
  simp only [gradient, hd, map_zero]

end Descent
