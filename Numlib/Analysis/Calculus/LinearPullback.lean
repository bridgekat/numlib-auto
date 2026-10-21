import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Second derivatives through linear restrictions

The bilinear second derivative of a function composed with a continuous linear map is its
second derivative evaluated on the images of the two directions.
-/

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pull back the actual bilinear second derivative through a linear restriction. -/
theorem secondFDeriv_comp_right_apply (K : E →L[ℝ] F) {f : F → G}
    (hf : ContDiff ℝ 2 f) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (K y))) x u v =
      fderiv ℝ (fderiv ℝ f) (K x) (K u) (K v) := by
  have h := congrArg (fun A : E [×2]→L[ℝ] G => A ![u, v])
    (K.iteratedFDeriv_comp_right hf x (by norm_num))
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Function.comp_def, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end ContinuousLinearMap
