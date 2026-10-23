import Numlib.Krylov.Lanczos.Residual
import Numlib.Analysis.Matrix.SpectralExtrema
import Numlib.LinearAlgebra.Matrix.Tridiagonal.Kernel
import Numlib.Optimization.Quadratic.Optimality.Matrix
import Mathlib.Tactic

open scoped BigOperators Matrix ComplexOrder

/-!
# Regularized quadratic minimization in actual Lanczos spaces

Actual projected global minimality and unreduced tridiagonal structure imply
a positive - definite shifted system. The true regularized model derivative
then satisfies the sharp radius and spectral - condition decay estimate.
-/

namespace QuadraticKrylov
open Krylov Lanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- Every actual projected regularized minimizer solves its positive - definite shifted system. -/
theorem projected_optimality (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    {m : ℕ} (hm : m + 1 ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) {σ r : ℝ} (hr : 2 < r)
    (hmin : ∀ z, QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) σ r y ≤
      QuadraticOptimality.regularized (Matrix.toEuclideanLin (Lanczos.tridiag A g (m +
        1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) σ r z) :
    let τ := σ * ‖y‖ ^ (r - 2)
    Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) ∧
      (Lanczos.tridiag A g (m + 1) + τ • 1).PosDef := by
  dsimp only
  generalize hb : (‖g‖ • (PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ) : EuclideanSpace ℝ
    (Fin (m + 1)))) = b at hmin ⊢
  obtain ⟨hsolve, hPSD⟩ := Matrix.regularized_minimizer_solve (r := r) (σ := σ)
    (T := Lanczos.tridiag A g (m + 1))
    (Lanczos.tridiag_isSymm A g (m + 1))
    b y hr hmin
  refine ⟨hsolve, ?_⟩
  apply Matrix.posDef_of_tridiagonal_solve (shifted_tridiag A g (m + 1) _)
    (shifted_tridiag_offdiag_ne A g hm _) hPSD
    (neg_ne_zero.mpr (norm_ne_zero_iff.mpr hg)) y
  rw [←hb] at hsolve
  simpa only [neg_smul] using hsolve


omit [FiniteDimensional ℝ E] in
/-- The true derivative norm of a regularized quadratic is the norm of its explicit gradient. -/
theorem norm_fderiv_regularized (A : E →L[ℝ] E) (g : E)
    (hA : A.toLinearMap.IsSymmetric) {r : ℝ} (hr : 2 < r) (σ : ℝ) (s : E) :
    ‖fderiv ℝ (QuadraticOptimality.regularized A g σ r) s‖ =
      ‖A s + (σ * ‖s‖ ^ (r - 2)) • s + g‖ := by
  have he : fderiv ℝ (QuadraticOptimality.regularized A g σ r) s =
      innerSL ℝ (A s + (σ * ‖s‖ ^ (r - 2)) • s + g) := by
    rw [(QuadraticOptimality.hasFDerivAt_regularized hA g hr σ s).fderiv]
    ext v
    simp only [add_apply, innerSL_apply_apply, smul_apply, NormPower.first, smul_eq_mul,
      inner_add_left, real_inner_smul_left]
    field_simp
    ring
  rw [he, innerSL_apply_norm]

/-- Actual Lanczos regularization subproblem minimizers satisfy the sharp model - gradient
decay bound. -/
theorem regularized_gradient_bound (A : E →L[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.toLinearMap.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A.toLinearMap g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hmin : ∀ z, QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (Lanczos.tridiag A.toLinearMap g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) σ r y ≤
      QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (Lanczos.tridiag A.toLinearMap g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) σ r z) :
    let τ := σ * ‖y‖ ^ (r - 2)
    let hT := shifted_tridiag_isHermitian A.toLinearMap g (m + 1) τ
    let κ := hT.greatestEigenvalue / hT.leastEigenvalue
    ‖fderiv ℝ (QuadraticOptimality.regularized A g σ r) (basisEmbedding A.toLinearMap g hm
      y)‖ ≤
      2 * ‖A‖ * κ * (τ / σ) ^ (1 / (r - 2)) *
        ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m := by
  dsimp only
  obtain ⟨hsolve, hPD⟩ := projected_optimality (m := m) A.toLinearMap (g := g) hg hm y hr hmin
  have hres := norm_residual_le A hg hA hm y (σ * ‖y‖ ^ (r - 2)) hsolve hPD.isUnit
    (hPD.isHermitian.leastEigenvalue_pos hPD) hPD.isHermitian.leastEigenvalue_le_greatest
    hPD.isHermitian.isSymmetricBoundedBy_extrema
  rw [norm_fderiv_regularized A g hA hr σ, (basisEmbedding A.toLinearMap g hm).norm_map]
  have hrad : (σ * ‖y‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) = ‖y‖ := by
    rw [mul_div_cancel_left₀ _ hσ.ne', ←Real.rpow_mul (norm_nonneg _),
      mul_one_div_cancel (by linarith : r - 2 ≠ 0), Real.rpow_one]
  rw [hrad]
  simpa only [(basisEmbedding A.toLinearMap g hm).norm_map] using hres


end QuadraticKrylov
