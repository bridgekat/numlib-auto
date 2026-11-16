/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Quarteroni, Sacco and Saleri, Section 5.12: Applications

This module formalizes Section 5.12 of [quarteroni2000numerical], which treats two engineering
eigenvalue problems. The buckling of a beam (Section 5.12.1) reduces, after a centred finite
difference discretization, to the smallest eigenvalue of the symmetric positive definite tridiagonal
matrix $A = \operatorname{tridiag}_n(-1, 2, -1)$. Its eigenvalues (5.69) are
$\lambda_j = 2(1 - \cos(j\theta))$ with $\theta = \pi/(n + 1)$, the discrete sine spectrum of
`Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`; this is the one numbered result of the section.
The free vibration of a bridge (Section 5.12.2) is a generalized eigenvalue problem (5.70) with a
diagonal positive mass matrix $M$, which the change of variable $z = M^{1/2} x$ reduces to a
standard one.

## Main results

* Equation (5.69), `QuarteroniSaccoSaleri.Chapter05.equation_5_69`: the eigenvalues of
  $\operatorname{tridiag}_n(-1, 2, -1)$ are exactly the numbers $2(1 - \cos(j\theta))$,
  $\theta = \pi/(n + 1)$, $j = 1, \dots, n$.

## Conventions

* The matrix $\operatorname{tridiag}_n(-1, 2, -1)$ is `Matrix.symmTridiagonalToeplitz n (-1) 2`,
  read as the operator `Matrix.toEuclideanLin` on $\mathbb{R}^n$. Its eigenvalues are stated with
  `Module.End.HasEigenvalue`.
* The index $j = 1, \dots, n$ of the book is `j : Fin n` shifted by one, so $j\theta$ is
  `(j + 1) * θ` in Lean.

## Not formalized

* **Section 5.12.2, the free vibration of a bridge.** It states no numbered result.
* **The numerical experiments of Section 5.12.**
-/

open scoped Real

namespace QuarteroniSaccoSaleri.Chapter05

/-- **Equation (5.69)** of [quarteroni2000numerical]. Let $n \in \mathbb{N}$ and
$\theta = \pi/(n + 1)$. A real number $\mu$ is an eigenvalue of the matrix $A =
\operatorname{tridiag}_n(-1, 2, -1) \in \mathbb{R}^{n \times n}$ of the buckling problem
(Section 5.12.1) if and only if $$\mu = \lambda_j = 2\,(1 - \cos(j\theta)) \quad \text{for some
} j = 1, \dots, n.$$

The source refers to Exercise 3 of Chapter 4 for the proof. The Lean index is `j : Fin n`, so
the book's $j$ is `j + 1`. The statement is the discrete sine spectrum of the backbone,
`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff`, which also says that these are all the
eigenvalues. The source then gives the critical load $P_{cr}^h = \lambda_{\min} E J / h^2$ with
$\lambda_{\min} = 2(1 - \cos\theta)$. -/
theorem equation_5_69 (n : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (Matrix.symmTridiagonalToeplitz n (-1) 2)) μ ↔
      ∃ j : Fin n, μ = 2 * (1 - Real.cos ((((j : ℕ) : ℝ) + 1) * (π / ((n : ℝ) + 1)))) := by
  rw [Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff]
  refine exists_congr fun j => ?_
  rw [mul_div_assoc]
  constructor <;> intro h <;> linarith

end QuarteroniSaccoSaleri.Chapter05
