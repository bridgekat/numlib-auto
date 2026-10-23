import Numlib.Optimization.TrustRegion.Regularized.Step

/-!
# Actual Hessians of quadratically regularized Taylor models

Finite second-order smoothness at the expansion point identifies the actual
model Hessian at every trial step, including zero. The added norm-square term
contributes exactly the regularization weight times the inner product.
-/

namespace RegularizedTrustRegion
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual model derivative has a constant genuine Fréchet derivative. -/
theorem hasFDerivAt_fderiv_model {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (ℓ : ℝ) (s : E) :
    let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
    HasFDerivAt (fderiv ℝ (model f x ℓ))
      (fderiv ℝ (fderiv ℝ f) x + ℓ • J) s := by
  let B := fderiv ℝ (fderiv ℝ f) x
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hd : HasFDerivAt (fun y => quadraticDerivative f x y + ℓ • innerSL ℝ y)
      (B + ℓ • J) s := by
    convert ((hasFDerivAt_const (fderiv ℝ f x) s).add B.hasFDerivAt).add
      (J.hasFDerivAt.const_smul ℓ) using 1
    · ext y w
      rfl
    · simp only [zero_add]
  have heq : (fun y => quadraticDerivative f x y + ℓ • innerSL ℝ y) =
      fderiv ℝ (model f x ℓ) := by
    funext y
    exact (fderiv_model hf ℓ y).symm
  rw [heq] at hd
  exact hd

/-- The actual second derivative tensor of the model equals the true Hessian
bilinear form plus the regularization inner product. -/
theorem iteratedFDeriv_two_model_apply {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (ℓ : ℝ) (s v w : E) :
    iteratedFDeriv ℝ 2 (model f x ℓ) s ![v, w] =
      fderiv ℝ (fderiv ℝ f) x v w + ℓ * inner ℝ v w := by
  rw [iteratedFDeriv_two_apply, (hasFDerivAt_fderiv_model hf ℓ s).fderiv]
  rfl

/-- The actual model quadratic form has the exact spectral shift, at every
trial point and in every diagonal direction. -/
theorem iteratedFDeriv_two_model_diag {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (ℓ : ℝ) (s v : E) :
    iteratedFDeriv ℝ 2 (model f x ℓ) s (fun _ => v) =
      iteratedFDeriv ℝ 2 f x (fun _ => v) + ℓ * ‖v‖ ^ 2 := by
  have he : (![v, v] : Fin 2 → E) = (fun _ => v) := by
    ext i; fin_cases i <;> rfl
  rw [← he, iteratedFDeriv_two_model_apply hf, real_inner_self_eq_norm_sq,
    iteratedFDeriv_two_apply]
  rfl

end RegularizedTrustRegion
