import Numlib.LinearSolve.Projection.Optimality
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# One-dimensional projection processes

The projection step with `K = span {v}`, `L = span {w}` (Saad (5.12)–(5.13)), and its three
classical instances: steepest descent (`v = w = r`), minimal residual iteration (`v = r`,
`w = A r`), and residual-norm steepest descent (`v = A† r`, `w = A v`). Convergence: Kantorovich's
inequality (Saad Lemma 5.8), the steepest-descent rate (Thm 5.9) and the minimal-residual rate
(Thm 5.10, valid for bounded coercive operators on any inner product space).
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Projection

/-- One projection step onto `span {v}` orthogonally to `span {w}`:
`x ↦ x + (⟪r, w⟫ / ⟪A v, w⟫) v` with `r = b - A x` (Saad (5.12)). -/
noncomputable def step1 (A : E →ₗ[𝕜] E) (b : E) (v w : E) (x : E) : E :=
  x + (inner 𝕜 w (b - A x) / inner 𝕜 w (A v)) • v

variable {A : E →ₗ[𝕜] E} {b : E}

theorem step1_isPetrovGalerkin (v w x : E) (h : inner 𝕜 w (A v) ≠ 0) :
    IsPetrovGalerkin A b x (𝕜 ∙ v) (𝕜 ∙ w) (step1 A b v w x) := by
  sorry

/-- Steepest descent step (Saad Alg 5.2): `v = w = r`. -/
noncomputable def steepestDescentStep (A : E →ₗ[𝕜] E) (b : E) (x : E) : E :=
  step1 A b (b - A x) (b - A x) x

/-- Minimal residual iteration step (Saad Alg 5.3): `v = r`, `w = A r`. -/
noncomputable def minResStep (A : E →ₗ[𝕜] E) (b : E) (x : E) : E :=
  step1 A b (b - A x) (A (b - A x)) x

/-- Residual-norm steepest descent step (Saad Alg 5.4): `v = A† r`, `w = A v`. -/
noncomputable def residualNormSDStep [CompleteSpace E] (A : E →L[𝕜] E) (b : E) (x : E) : E :=
  step1 (A : E →ₗ[𝕜] E) b ((ContinuousLinearMap.adjoint A) (b - A x))
    (A ((ContinuousLinearMap.adjoint A) (b - A x))) x

theorem steepestDescentStep_isGalerkin (x : E) (hA : A.IsCoercive) :
    IsGalerkin A b x (𝕜 ∙ (b - A x)) (steepestDescentStep A b x) := by
  sorry

theorem minResStep_isMinRes (x : E) (hA : A.IsCoercive) :
    IsMinRes A b x (𝕜 ∙ (b - A x)) (minResStep A b x) := by
  sorry

/-- Kantorovich's inequality (Saad Lemma 5.8): for symmetric coercive `A` with spectrum in
`[λmin, λmax]`, `re⟪A x, x⟫ · re⟪A⁻¹ x, x⟫ ≤ (λmax + λmin)² / (4 λmax λmin) ‖x‖⁴`. -/
theorem kantorovich_inequality {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) (x : E) {y : E} (hy : A y = x) :
    RCLike.re (inner 𝕜 (A x) x) * RCLike.re (inner 𝕜 y x) ≤
      (lmax + lmin) ^ 2 / (4 * lmax * lmin) * ‖x‖ ^ 4 := by
  sorry

/-- Saad Thm 5.9: steepest descent contracts the energy norm of the error by
`(λmax - λmin)/(λmax + λmin)`. -/
theorem energyNorm_steepestDescentStep_le {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) {xstar : E} (hstar : A xstar = b) (x : E) :
    energyNorm A (xstar - steepestDescentStep A b x) ≤
      (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x) := by
  sorry

/-- Saad Thm 5.10: for a bounded operator with `c ‖x‖² ≤ re⟪A x, x⟫`, the minimal residual
iteration contracts the residual by `√(1 - c² / ‖A‖²)`. -/
theorem norm_residual_minResStep_le {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) (b x : E) :
    ‖b - A (minResStep (A : E →ₗ[𝕜] E) b x)‖ ≤
      Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x‖ := by
  sorry

end Projection
