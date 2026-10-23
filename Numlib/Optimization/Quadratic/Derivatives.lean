import Numlib.Optimization.Quadratic.Optimality.TrustRegion
import Numlib.Analysis.Calculus.TaylorModel.SecondOrder

/-!
# Actual derivatives and Taylor models of bounded symmetric quadratics

The Hessian is derived from the genuine quadratic objective. Its constant
second derivative and exact degree-two Taylor polynomial apply at every center.
-/

namespace QuadraticOptimality
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (g x : E)
include hH

/-- The actual quadratic derivative is the inner-product functional of g+Hx. -/
theorem fderiv_model_eq : fderiv ℝ (model H g) x = innerSL ℝ (g + H x) :=
  (hasFDerivAt_model hH g x).fderiv

/-- The derivative of the actual quadratic derivative is its constant Hessian form. -/
theorem fderiv_fderiv_model_apply (v w : E) :
    fderiv ℝ (fderiv ℝ (model H g)) x v w = inner ℝ (H v) w := by
  have he : fderiv ℝ (model H g) = fun z => innerSL ℝ (g + H z) :=
    funext (fderiv_model_eq hH g)
  have hd := (innerSL ℝ).hasFDerivAt.comp x ((H.hasFDerivAt).const_add g)
  change HasFDerivAt (fun z => innerSL ℝ (g + H z)) _ x at hd
  rw [he, hd.fderiv]
  rfl

/-- The genuine second derivative tensor is the same at every quadratic center. -/
theorem iteratedFDeriv_two_model (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (model H g) x v = inner ℝ (H (v 0)) (v 1) := by
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_model_apply hH]

/-- The actual quadratic Taylor polynomial agrees exactly with the objective increment. -/
theorem taylor_two_model (s : E) : eval (model H g) 2 x s = model H g (x + s) := by
  rw [eval_two_eq, fderiv_model_eq hH, fderiv_fderiv_model_apply hH]
  have hh := model_add hH g x s
  simp only [innerSL_apply_apply]
  linarith

end QuadraticOptimality

namespace QuadraticOptimality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- The actual gradient of a symmetric quadratic is its genuine affine gradient. -/
theorem gradient_model {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (g x : E) :
    gradient (model H g) x = g + H x :=
  (show HasGradientAt (model H g) (g + H x) x from
    hasGradientAt_iff_hasFDerivAt.mpr (hasFDerivAt_model hH g x)).gradient
end QuadraticOptimality
