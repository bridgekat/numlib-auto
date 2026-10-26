import Numlib.Analysis.InnerProductSpace.MinCurvature
import Numlib.Optimization.Subproblem.Secular

/-!
# `λ_min` of a bilinear form and the leftmost eigenvalue

If `A[v, w] = ⟪v, H w⟫` with `H : E →L[ℝ] E` symmetric on a finite-dimensional real inner
product space, the least curvature `minCurvature A` (from
`Numlib.Analysis.InnerProductSpace.MinCurvature`) is the leftmost eigenvalue
`Subproblem.leftmost hH` used by the trust-region subproblem theory
([cartis2022evaluation], Section A.5). Both are `0` on the zero space.
-/

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Bridge to the leftmost eigenvalue** ([cartis2022evaluation], Section A.5): if
`A[v, w] = ⟪v, H w⟫` with `H` symmetric, then `λ_min[A] = Subproblem.leftmost hH`. -/
theorem minCurvature_eq_leftmost {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}
    {H : E →L[ℝ] E} (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hAH : ∀ v w, A ![v, w] = ⟪v, H w⟫) :
    minCurvature A = Subproblem.leftmost hH :=
  minCurvature_eq_iInf_eigenvalues hH rfl hAH
