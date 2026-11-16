/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.MinCurvature
import Numlib.Optimization.Subproblem.Secular

/-!
# The least curvature of a symmetric form and the leftmost eigenvalue

Let $E$ be a finite-dimensional real inner product space and let $H : E \to E$ be a symmetric
continuous linear operator. If a continuous bilinear form $A$ on $E$ satisfies
$A[v, w] = \langle v, H w \rangle$, then its least curvature
$\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d, d]$ (the definition `minCurvature` of
`Numlib.Analysis.InnerProductSpace.MinCurvature`) equals the leftmost eigenvalue $\lambda_1$ of $H$
(the definition `Subproblem.leftmost`), which the trust-region subproblem theory uses. This is the
setting of Section A.5 of [cartis2022evaluation]. On the zero space both numbers are $0$.

## Main results

* `minCurvature_eq_leftmost`: if $A[v, w] = \langle v, H w \rangle$ with $H$ symmetric, then
  $\lambda_{\min}[A] = \lambda_1(H)$.
-/

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Let $E$ be a finite-dimensional real inner product space, let $A$ be a continuous bilinear form
on $E$, and let $H : E \to E$ be a symmetric continuous linear operator with
$A[v, w] = \langle v, H w \rangle$ for all $v, w \in E$. Then the least curvature of $A$ equals
the leftmost eigenvalue of $H$:
$$\lambda_{\min}[A] = \lambda_1(H).$$

This links the least curvature of Section A.5 of [cartis2022evaluation] to the spectral theory
of the trust-region subproblem. The form $A$ is a `ContinuousMultilinearMap` on `Fin 2`, applied
to `![v, w]`. The least curvature is `minCurvature A` and the leftmost eigenvalue is
`Subproblem.leftmost hH`. Both are $0$ when $E$ is the zero space, so the identity also holds
there. -/
theorem minCurvature_eq_leftmost {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}
    {H : E →L[ℝ] E} (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hAH : ∀ v w, A ![v, w] = ⟪v, H w⟫) :
    minCurvature A = Subproblem.leftmost hH :=
  minCurvature_eq_iInf_eigenvalues hH rfl hAH
