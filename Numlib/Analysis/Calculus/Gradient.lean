/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.Gradient.Basic`, beside `gradient` and `HasGradientAt`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
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
  derivatives), `EuclideanSpace.inner_gradient_eq_fderiv`, `EuclideanSpace.inner_gradient_eq_sum`,
  `EuclideanSpace.norm_gradient_eq`, `EuclideanSpace.norm_fderiv_eq` (the operator norm of `Du(x)`
  is the Euclidean norm of the tuple of partial derivatives) and
  `EuclideanSpace.continuous_gradient` for a `C¹` function, and the coordinate bounds
  `EuclideanSpace.abs_apply_sub_le` (`|x i - y i| ≤ ‖x - y‖`) and
  `EuclideanSpace.norm_toLp_two_le` (`‖(a, b)‖ ≤ |a| + |b|`);
* second derivatives from the gradient: `norm_iteratedFDeriv_two_le_of_gradient` (a `C`-Lipschitz
  gradient bounds the second derivative by `C`) and `contDiff_two_of_gradient`.
-/

open scoped InnerProductSpace

section ToDualReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gradient through `toDualReal`. -/
theorem gradient_eq_toDualReal_symm (f : E → ℝ) :
    gradient f = fun x ↦ (InnerProductSpace.toDualReal E).symm (fderiv ℝ f x) := rfl

/-- **The Fréchet derivative is the inner product with the gradient**, as a continuous linear
map: `fderiv ℝ f x = innerSL ℝ (∇f(x))`, so that `fderiv ℝ f x d = ⟪∇f(x), d⟫`. No
differentiability is needed, both sides being junk-valued together. This is the form in which
derivative data `f' x = innerSL ℝ (g x)` (as in `Numlib/Optimization/Descent`) meets Mathlib's
gradient; upstreaming candidate beside Mathlib's `toDual_gradient`. -/
theorem fderiv_eq_innerSL_gradient (f : E → ℝ) (x : E) :
    fderiv ℝ f x = innerSL ℝ (gradient f x) := by
  ext d
  rw [innerSL_apply_apply, inner_gradient_left]

end ToDualReal

namespace EuclideanSpace

/-- **The inner product of `ℝⁿ` in coordinates**, `⟪v, w⟫ = ∑ j, v_j w_j`: the real case of
`EuclideanSpace.inner_eq_star_dotProduct`, written as a sum. Upstreaming candidate (natural home
`Mathlib/Analysis/InnerProductSpace/PiL2`). -/
theorem real_inner_eq_sum {ι : Type*} [Fintype ι] (v w : EuclideanSpace ℝ ι) :
    ⟪v, w⟫_ℝ = ∑ j, v j * w j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- **A real functional on `ℝⁿ` through the coordinate projections**:
`⟪v, ·⟫ = ∑ j, v j • proj j`, which is how a gradient is read off the coordinate derivatives.
Upstreaming candidate (natural home `Mathlib/Analysis/InnerProductSpace/PiL2`, beside
`EuclideanSpace.proj`). -/
theorem innerSL_eq_sum_smul_proj {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    innerSL ℝ v = ∑ j, v j • EuclideanSpace.proj (𝕜 := ℝ) j := by
  ext w
  rw [innerSL_apply_apply, real_inner_eq_sum]
  simp

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

/-- **The inner product of two gradients in coordinates**, `⟪∇u, ∇v⟫ = ∑ᵢ ∂ᵢu ∂ᵢv`. -/
theorem inner_gradient_eq_sum (u v : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ⟪gradient u x, gradient v x⟫_ℝ
      = ∑ i, fderiv ℝ u x (EuclideanSpace.single i 1)
        * fderiv ℝ v x (EuclideanSpace.single i 1) := by
  simp only [real_inner_eq_sum, gradient_apply]

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

/-- A coordinate difference is at most the Euclidean distance. -/
theorem abs_apply_sub_le {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) (i : ι) :
    |x i - y i| ≤ ‖x - y‖ := by
  have := PiLp.norm_apply_le (x - y) i
  rwa [PiLp.sub_apply, Real.norm_eq_abs] at this

/-- The Euclidean norm of `(a, b)` is at most `|a| + |b|`. -/
theorem norm_toLp_two_le (a b : ℝ) : ‖!₂[a, b]‖ ≤ |a| + |b| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]

end EuclideanSpace

/-! ### Second derivatives from the gradient -/

section SecondDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : E → ℝ} {G : E → E}

/-- A function with a `C`-Lipschitz gradient has second derivative bounded by `C`. -/
theorem norm_iteratedFDeriv_two_le_of_gradient {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ z, HasGradientAt F (G z) z) (hL : ∀ z z', ‖G z - G z'‖ ≤ C * ‖z - z'‖) (z : E) :
    ‖iteratedFDeriv ℝ 2 F z‖ ≤ C := by
  have hfd : fderiv ℝ F = fun z => InnerProductSpace.toDual ℝ E (G z) :=
    funext fun z => ((hasGradientAt_iff_hasFDerivAt).1 (hG z)).fderiv
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  refine norm_fderiv_le_of_lip' ℝ hC (Filter.Eventually.of_forall fun x => ?_)
  rw [hfd, ← map_sub, LinearIsometryEquiv.norm_map]
  exact hL x z

/-- A function whose gradient is `C¹` is `C²`. -/
theorem contDiff_two_of_gradient (hG : ∀ z, HasGradientAt F (G z) z) (hGc : ContDiff ℝ 1 G) :
    ContDiff ℝ 2 F := by
  have hfd : fderiv ℝ F = fun z => InnerProductSpace.toDual ℝ E (G z) :=
    funext fun z => ((hasGradientAt_iff_hasFDerivAt).1 (hG z)).fderiv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun z => (hG z).differentiableAt, by simp, ?_⟩
  rw [hfd]
  exact ((InnerProductSpace.toDual ℝ E).contDiff (n := 1)).comp hGc

end SecondDerivative
