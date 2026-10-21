import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Calculus in one-dimensional Euclidean space

The unique coordinate identifies Euclidean one-space isometrically with the real line.
Scalar derivatives transport to genuine Fréchet derivatives and gradients under this map.
-/
noncomputable section
namespace EuclideanOne

/-- The unique coordinate of Euclidean one-space, with its isometric structure. -/
def coord : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]

/-- A scalar objective viewed on the one-dimensional Euclidean space. -/
def lift (f : ℝ → ℝ) : EuclideanSpace ℝ (Fin 1) → ℝ := f ∘ coord

/-- Evaluating the lifted objective is scalar evaluation at the unique coordinate. -/
@[simp] theorem lift_apply (f : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    lift f x = f (coord x) := rfl

/-- Composition with the coordinate map preserves every order of continuous smoothness. -/
theorem contDiff {f : ℝ → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (lift f) := hf.comp coord.toContinuousLinearEquiv.contDiff

/-- A scalar derivative gives the Euclidean Fréchet derivative by composition. -/
theorem hasFDerivAt {f : ℝ → ℝ} {d : ℝ} {x : EuclideanSpace ℝ (Fin 1)}
    (hf : HasDerivAt f d (coord x)) :
    HasFDerivAt (lift f) (d • coord.toContinuousLinearEquiv.toContinuousLinearMap) x := by
  have hh := hf.hasFDerivAt.comp x coord.toContinuousLinearEquiv.hasFDerivAt
  convert hh using 1 <;> ext v <;> simp [mul_comm]

/-- A scalar derivative represents the gradient through the inverse isometry. -/
theorem hasGradientAt {f : ℝ → ℝ} {d : ℝ} {x : EuclideanSpace ℝ (Fin 1)}
    (hf : HasDerivAt f d (coord x)) : HasGradientAt (lift f) (coord.symm d) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hasFDerivAt hf using 1
  ext v
  have hinner := coord.inner_map_map (coord.symm d) v
  simpa [real_inner_comm, mul_comm] using hinner.symm

/-- The Euclidean gradient is the transported scalar derivative. -/
theorem gradient_eq {f : ℝ → ℝ} {d : ℝ} {x : EuclideanSpace ℝ (Fin 1)}
    (hf : HasDerivAt f d (coord x)) : gradient (lift f) x = coord.symm d :=
  (hasGradientAt hf).gradient

/-- A globally differentiable scalar objective has the expected gradient everywhere. -/
theorem gradient_eq_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (x : EuclideanSpace ℝ (Fin 1)) : gradient (lift f) x = coord.symm (deriv f (coord x)) :=
  gradient_eq (hf (coord x)).hasDerivAt

/-- A global scalar derivative Lipschitz estimate transfers without changing its constant. -/
theorem gradient_lipschitz {f : ℝ → ℝ} (hf : Differentiable ℝ f) {L : NNReal}
    (hL : LipschitzWith L (deriv f)) : LipschitzWith L (gradient (lift f)) := by
  have h := coord.symm.lipschitzWith.comp (hL.comp coord.lipschitzWith)
  simpa only [Function.comp_def, ← gradient_eq_deriv hf, one_mul, mul_one] using h

/-- The first Fréchet derivative is the scalar derivative times the coordinate functional. -/
theorem fderiv_eq {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (x : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ (lift f) x = deriv f (coord x) • coord.toContinuousLinearEquiv.toContinuousLinearMap :=
  (hasFDerivAt (hf (coord x)).hasDerivAt).fderiv

/-- The second Fréchet derivative, applied to two directions, is the transported scalar
second derivative. The hypothesis asserts actual differentiability of the first derivative. -/
theorem fderiv_fderiv_apply {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {x : EuclideanSpace ℝ (Fin 1)} {d₂ : ℝ}
    (hd : HasDerivAt (deriv f) d₂ (coord x)) (u v : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ (fderiv ℝ (lift f)) x u v = d₂ * coord u * coord v := by
  have heq : fderiv ℝ (lift f) = fun y =>
      deriv f (coord y) • coord.toContinuousLinearEquiv.toContinuousLinearMap :=
    funext (fderiv_eq hf)
  rw [heq]
  have hh := (hasFDerivAt hd).smul_const coord.toContinuousLinearEquiv.toContinuousLinearMap
  change HasFDerivAt (fun y => deriv f (coord y) • _) _ x at hh
  rw [hh.fderiv]
  simp [mul_assoc]

open InnerProductSpace

/-- The Hessian operator of a scalar lift is its scalar second derivative times the identity. -/
theorem continuousLinearMapOfBilin_fderiv_fderiv {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (y : EuclideanSpace ℝ (Fin 1)) :
    continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ (lift φ)) y) =
      deriv (deriv φ) (coord y) • ContinuousLinearMap.id ℝ _ := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv φ) := by
    simpa only [iteratedDeriv_one] using hφ.differentiable_iteratedDeriv 1 (by norm_num)
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [continuousLinearMapOfBilin_apply,
    fderiv_fderiv_apply hd (hd' (coord y)).hasDerivAt]
  have hh := coord.inner_map_map u v
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left]
  rw [← hh]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end EuclideanOne
