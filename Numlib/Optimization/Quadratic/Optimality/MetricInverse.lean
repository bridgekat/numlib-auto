import Numlib.Optimization.Quadratic.Optimality.RegularizationMetric
import Numlib.Analysis.InnerProductSpace.Symmetric.Similarity
import Mathlib.Tactic

/-!
# Actual inverse-metric gradient and Hessian transport

Riesz metric coordinates equal the actual inverse-metric gradient and
Hessian. A spectral similarity argument bounds the metric Hessian norm by
the ordinary inverse-metric operator norm without assuming norm invariance.
-/

namespace QuadraticOptimality.Metric
open QuadraticRegularization.Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (M : E →L[ℝ] E) (hM : M.toLinearMap.IsSymmetricCoercive)

include hM in
/-- A finite-dimensional positive-definite metric has an actual bounded inverse. -/
theorem invertible : M.IsInvertible := by
  let e := LinearEquiv.ofBijective M.toLinearMap
    ⟨hM.isCoercive.injective, (LinearMap.injective_iff_surjective).mp hM.isCoercive.injective⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

/-- The transported Hessian equals the actual inverse-metric Hessian in original coordinates. -/
theorem hessian_intertwines (H : E →L[ℝ] E) (v : WithEnergy M.toLinearMap hM) :
    toOriginal M hM (hessian M hM H v) = M.inverse (H (toOriginal M hM v)) := by
  have he : M (toOriginal M hM (hessian M hM H v)) = H (toOriginal M hM v) := by
    apply ext_inner_right ℝ
    intro w
    change inner ℝ (hessian M hM H v) (WithEnergy.equiv M.toLinearMap hM w) = _
    rw [inner_hessian]
    rfl
  rw [←he, (invertible M hM).inverse_apply_self]

/-- The metric Hessian operator norm is at most the ordinary inverse-metric Hessian norm. -/
theorem norm_hessian_le {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) :
    ‖hessian M hM H‖ ≤ ‖M.inverse.comp H‖ := by
  apply ContinuousLinearMap.norm_le_norm_of_similar (hessian_symmetric M hM hH)
    (M.inverse.comp H) (WithEnergy.equiv M.toLinearMap hM).symm
  exact hessian_intertwines M hM H

/-- The metric gradient equals the actual inverse-metric gradient in original coordinates. -/
theorem gradient_intertwines (g : E) :
    toOriginal M hM (gradient M hM g) = M.inverse g := by
  have he : M (toOriginal M hM (gradient M hM g)) = g := by
    apply ext_inner_right ℝ
    intro w
    change inner ℝ (gradient M hM g) (WithEnergy.equiv M.toLinearMap hM w) = _
    rw [inner_gradient]
    rfl
  calc _ = M.inverse (M (toOriginal M hM (gradient M hM g))) :=
      ((invertible M hM).inverse_apply_self _).symm
    _ = M.inverse g := congrArg M.inverse he

/-- A nonzero original gradient has a nonzero actual metric Riesz representative. -/
theorem gradient_ne_zero {g : E} (hg : g ≠ 0) : gradient M hM g ≠ 0 := by
  intro hz
  have hh := gradient_intertwines M hM g
  rw [hz, map_zero] at hh
  have he := congrArg (fun z => M z) hh
  rw [map_zero, (invertible M hM).self_apply_inverse] at he
  exact hg he.symm

/-- The metric Riesz gradient norm equals the actual inverse-metric energy norm. -/
theorem norm_gradient (g : E) :
    ‖gradient M hM g‖ = energyNorm M.inverse.toLinearMap g := by
  have hn := WithEnergy.norm_equiv M.toLinearMap hM (M.inverse g)
  have he : gradient M hM g = WithEnergy.equiv M.toLinearMap hM (M.inverse g) :=
    (WithEnergy.equiv M.toLinearMap hM).symm.injective (gradient_intertwines M hM g)
  rw [he, hn]
  unfold energyNorm
  change Real.sqrt (inner ℝ (M (M.inverse g)) (M.inverse g)) =
    Real.sqrt (inner ℝ (M.inverse g) g)
  rw [(invertible M hM).self_apply_inverse, real_inner_comm]

/-- The actual metric shifted residual represents the original shifted-pencil gradient. -/
theorem gradient_residual (H : E →L[ℝ] E) (g : E) (τ : ℝ)
    (v : WithEnergy M.toLinearMap hM) :
    hessian M hM H v + τ • v + gradient M hM g =
      gradient M hM (H (toOriginal M hM v) + τ • M (toOriginal M hM v) + g) := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_add_left, inner_add_left, real_inner_smul_left, inner_hessian,
    inner_gradient, inner_gradient, inner_add_left, inner_add_left, real_inner_smul_left]
  rfl

/-- The metric shifted-residual norm equals the original inverse-metric gradient norm. -/
theorem norm_residual (H : E →L[ℝ] E) (g : E) (τ : ℝ)
    (v : WithEnergy M.toLinearMap hM) :
    ‖hessian M hM H v + τ • v + gradient M hM g‖ =
      energyNorm M.inverse.toLinearMap (H (toOriginal M hM v) +
        τ • M (toOriginal M hM v) + g) := by
  rw [gradient_residual, norm_gradient]
end QuadraticOptimality.Metric
