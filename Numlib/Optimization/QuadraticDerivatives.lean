import Numlib.Optimization.QuadraticSubproblem
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness and Hessians of quadratic models

The exact quadratic model is smooth without a symmetry assumption. Symmetry identifies
its actual bilinear Hessian with the supplied bounded operator.
-/

open scoped InnerProductSpace
namespace Optimization.QuadraticSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every bounded quadratic model is smooth of every finite or infinite order. -/
theorem contDiff_quadratic (g : E) (H : E →L[ℝ] E) (p : WithTop ℕ∞) :
    ContDiff ℝ p (quadratic g H) :=
  (contDiff_const.inner ℝ contDiff_id).add
    ((contDiff_id.inner ℝ H.contDiff).const_smul (1 / 2 : ℝ))

/-- The actual second derivative of the quadratic part is its symmetric bilinear form. -/
theorem fderiv_fderiv_quadratic_apply (g : E) {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    (s u v : E) : fderiv ℝ (fderiv ℝ (quadratic g H)) s u v = inner ℝ (H u) v := by
  have he : fderiv ℝ (quadratic g H) = fun z => innerSL ℝ g + innerSL ℝ (H z) := by
    funext z
    rw [(hasFDerivAt_quadratic g hH z).fderiv, map_add]
  rw [he]
  have h := (hasFDerivAt_const (innerSL ℝ g) s).add
    ((((innerSL ℝ).restrictScalars ℝ).comp H).hasFDerivAt)
  have h' : HasFDerivAt (fun z => innerSL ℝ g + innerSL ℝ (H z))
      (((innerSL ℝ).restrictScalars ℝ).comp H) s := by
    convert h using 1 <;> first | rfl | simp only [zero_add]
  rw [h'.fderiv]
  exact innerSL_apply_apply ℝ (H u) v

end Optimization.QuadraticSubproblem
