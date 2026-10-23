import Numlib.Analysis.Calculus.LipschitzDerivative
import Numlib.Optimization.LineSearch

/-!
# Armijo steps for a Lipschitz gradient

A Lipschitz bound on the gradient gives an explicit interval of step lengths
satisfying sufficient decrease. The derivative is specified through the Riesz
map, so no independent vector field can stand in for the gradient.
-/

namespace LineSearch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A step along the negative gradient satisfies Armijo whenever
`L * t ≤ 2 * (1 - α)`. This includes the zero step and a vanishing gradient. -/
theorem armijo_neg_gradient_of_lipschitz {f : E → ℝ} {g : E → E} {L α t : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hL : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (ht : 0 ≤ t) (hstep : L * t ≤ 2 * (1 - α)) (x : E) :
    Armijo f (fun y => innerSL ℝ (g y)) α x (-g x) t := by
  have hderiv : ∀ y z, ‖innerSL ℝ (g y) - innerSL ℝ (g z)‖ ≤ L * ‖y - z‖ := by
    intro y z
    rw [← map_sub, innerSL_apply_norm]
    exact hL y z
  have hr := norm_sub_sub_fderiv_le_half_of_lipschitz_bound hf hderiv x (t • -g x)
  have heval : innerSL ℝ (g x) (t • -g x) = -t * ‖g x‖ ^ 2 := by
    rw [map_smul, map_neg, innerSL_apply_apply, real_inner_self_eq_norm_sq]
    simp [smul_eq_mul]
  rw [heval, norm_smul, Real.norm_of_nonneg ht, norm_neg, Real.norm_eq_abs] at hr
  have hupper := (abs_le.mp hr).2
  have hmul := mul_le_mul_of_nonneg_right hstep (mul_nonneg ht (sq_nonneg ‖g x‖))
  change f (x + t • -g x) ≤ f x + α * t * innerSL ℝ (g x) (-g x)
  rw [map_neg, innerSL_apply_apply, real_inner_self_eq_norm_sq]
  nlinarith

end LineSearch
