import Numlib.Analysis.Calculus.ContDiff.Lipschitz
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Lipschitz first derivatives from bounded second derivatives

The actual second derivative tensor bounds the Lipschitz constant of the first
Fréchet derivative. For real Hilbert spaces the Riesz isometry transfers exactly
the same constant to the gradient.
-/

open Set

/-- A bounded actual second derivative makes the first Fréchet derivative globally
Lipschitz, with the same constant and without completeness assumptions. -/
theorem norm_fderiv_sub_le_of_iteratedFDeriv_two_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 2 f) {B : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ B) (x y : E) :
    ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ B*‖x-y‖ := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hdf.differentiable (by norm_num) z) _ convex_univ (mem_univ y) (mem_univ x)
  intro z _
  rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
  exact hb z

/-- A bounded actual second derivative makes the actual Hilbert-space gradient
Lipschitz with exactly the same constant. -/
theorem norm_gradient_sub_le_of_iteratedFDeriv_two_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {B : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ B) (x y : E) :
    ‖gradient f x-gradient f y‖ ≤ B*‖x-y‖ := by
  rw [← (InnerProductSpace.toDual ℝ E).norm_map (gradient f x-gradient f y),
    map_sub,toDual_gradient,toDual_gradient]
  exact norm_fderiv_sub_le_of_iteratedFDeriv_two_le hf hb x y
