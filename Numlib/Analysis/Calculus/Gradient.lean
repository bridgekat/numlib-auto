/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.Gradient.Basic`, beside `gradient` and `HasGradientAt`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.InnerProductSpace.Dual

/-!
# The gradient: the Riesz map, and coordinates on `ℝ^N`

Small facts about Mathlib's `gradient f x = (toDual ℝ F).symm (fderiv ℝ f x)` that the boundary
modules of `Numlib/Analysis/Sobolev/Boundary/` use:

* `gradient_eq_toDualReal_symm`: the gradient through the real-linear Riesz map
  `InnerProductSpace.toDualReal` (so the calculus lemmas for `≃ₗᵢ[ℝ]` apply);
* on `ℝ^N`: `EuclideanSpace.gradient_apply` (the coordinates of the gradient are the partial
  derivatives), `EuclideanSpace.inner_gradient_eq_fderiv`, `EuclideanSpace.norm_gradient_eq`,
  `EuclideanSpace.norm_fderiv_eq` (the operator norm of `Du(x)` is the Euclidean norm of the
  tuple of partial derivatives) and `EuclideanSpace.continuous_gradient` for a `C¹` function.
-/

open scoped InnerProductSpace

section ToDualReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gradient through `toDualReal`. -/
theorem gradient_eq_toDualReal_symm (f : E → ℝ) :
    gradient f = fun x ↦ (InnerProductSpace.toDualReal E).symm (fderiv ℝ f x) := rfl

end ToDualReal

namespace EuclideanSpace

variable {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient (hg : ContDiff ℝ 1 g) : Continuous (gradient g) := by
  change Continuous fun x' ↦ (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm
    (fderiv ℝ g x')
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp
    (hg.continuous_fderiv one_ne_zero)

/-- The norm of the gradient is the operator norm of the derivative. -/
theorem norm_gradient_eq (x' : EuclideanSpace ℝ (Fin d)) : ‖gradient g x'‖ = ‖fderiv ℝ g x'‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- The pairing of the gradient with a vector is the derivative in that direction. -/
theorem inner_gradient_eq_fderiv (x' v : EuclideanSpace ℝ (Fin d)) :
    ⟪gradient g x', v⟫_ℝ = fderiv ℝ g x' v :=
  InnerProductSpace.toDual_symm_apply

/-- The coordinates of the gradient are the partial derivatives. -/
theorem gradient_apply (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin d) : gradient g x i = fderiv ℝ g x (EuclideanSpace.single i 1) := by
  have h : gradient g x i = ⟪gradient g x, EuclideanSpace.single i 1⟫_ℝ := by
    rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  rw [h, gradient, InnerProductSpace.toDual_symm_apply]

/-- The operator norm of the derivative of `u : ℝ^N → ℝ` is the Euclidean norm of the tuple of
partial derivatives `(∂ᵢu x)ᵢ`. -/
theorem norm_fderiv_eq (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ u x‖
      = ‖(WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :
          PiLp 2 fun _ : Fin d ↦ ℝ)‖ := by
  have h : gradient u x
      = (WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :
          PiLp 2 fun _ : Fin d ↦ ℝ) := by
    ext i
    rw [gradient, PiLp.toLp_apply]
    have h2 : ∀ w : EuclideanSpace ℝ (Fin d), w i = ⟪w, EuclideanSpace.single i 1⟫_ℝ := fun w ↦ by
      rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    rw [h2, InnerProductSpace.toDual_symm_apply]
  rw [← h, gradient, LinearIsometryEquiv.norm_map]

end EuclideanSpace
