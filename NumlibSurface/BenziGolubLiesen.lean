/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenziGolubLiesen.Section01
import NumlibSurface.BenziGolubLiesen.Section03.Solvability
import NumlibSurface.BenziGolubLiesen.Section03.Spectrum
import NumlibSurface.BenziGolubLiesen.Section09
import NumlibSurface.BenziGolubLiesen.Section10.Constraint
import NumlibSurface.BenziGolubLiesen.Section10.Pencil

/-!
# Benzi, Golub and Liesen, *Numerical solution of saddle point problems*

This library formalizes the numbered results of the Acta Numerica survey [benzi2005numerical]. The
survey studies linear systems whose coefficient matrix has the saddle-point form
$$\mathcal{A} = \begin{bmatrix} A & B_1^T \\ B_2 & -C \end{bmatrix},$$
with $A \in \mathbb{R}^{n \times n}$, $B_1, B_2 \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times m}$, and the methods that solve them. Section 1 gives the coefficient
matrix, Section 3 studies its nonsingularity and its spectrum, Section 9 studies the projection
framework and the optimality of Krylov subspace methods, and Section 10 studies the spectrum after
constraint preconditioning. The proofs specialize backbone results in
`Numlib.LinearAlgebra.Matrix.SaddlePoint` and its submodules, `Numlib.Krylov.Iterate`,
`Numlib.Projection.Basic`, `Numlib.Preconditioner.Constraint` and
`Numlib.Preconditioner.ConstraintPencil`.

## Coverage

The library formalizes the explicitly numbered theorems and the lemma of the survey: Theorems
3.1–3.8, 9.1–9.3 and 10.1, and Lemma 10.2. It also formalizes the definitions and the equations that
their statements use: the matrices (1.1), (3.10) and (3.13), the Krylov space and the projection
conditions (9.1)–(9.4), and the generalized eigenvalue problem (10.21). The examples after Theorem
3.4 and the paragraph after Theorem 3.8 are formalized, together with counterexamples that support
the corrections below. Standalone equations, applications and descriptions of solvers are included
only where they support a numbered result.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1 Introduction | `Section01` | the matrix $\mathcal{A}$ of (1.1) |
| §3.2 Solvability conditions | `Section03.Solvability` | Theorems 3.1–3.4 and examples |
| §3.4 Spectral properties | `Section03.Spectrum` | (3.10), (3.13), Theorems 3.5–3.8 |
| §9 Krylov subspace methods | `Section09` | (9.1)–(9.4), Theorems 9.1–9.3 |
| §10.2 Constraint and indefinite preconditioning | `Section10.Constraint` | Theorem 10.1 |
| §10.2 Constraint and indefinite preconditioning | `Section10.Pencil` | (10.21), Lemma 10.2 |

## Conventions

* All declarations are in the namespace `BenziGolubLiesen`. Theorem 3.1 is
  `BenziGolubLiesen.theorem_3_1`, part (iii) of Lemma 10.2 is `BenziGolubLiesen.lemma_10_2_iii`, and
  case (C) of Theorem 9.3 is `BenziGolubLiesen.theorem_9_3_c`. A counterexample to a printed
  statement has a name that ends in `_example`.
* Matrices are indexed by finite types: $A \in \mathbb{R}^{n \times n}$ is `A : Matrix n n ℝ`, and a
  block matrix of order $n + m$ is indexed by `n ⊕ m`. In Section 10.2 (`Section10.Constraint`) the
  dimensions are natural numbers and the index types are `Fin n` and `Fin m`.
* "$B$ has full rank" for $B \in \mathbb{R}^{m \times n}$ means $\operatorname{rank} B = m$, which
  is `B.rank = Fintype.card m`.
* A square matrix is nonsingular if it is a unit, `IsUnit`. For a real matrix, `Matrix.PosDef` and
  `Matrix.PosSemidef` include symmetry.
* Eigenvalues and eigenvectors are complex. A real matrix $M$ acts on complex vectors through
  `Matrix.complexify`, its spectrum is `spectrum ℂ M.complexify`, and "real" means membership in the
  image of `Complex.ofReal`.
* In Section 9, vectors are elements of `EuclideanSpace ℝ ι`, and a matrix acts on them through
  `Matrix.toEuclideanLin`.

## Deviations from the source

**Section 3**

* **Paragraph after Theorem 3.8** (correction). The source calls the nonreal eigenvalues of the
  sign-flipped form (3.13) purely imaginary. They have real part $\eta / 2$, as the formulas of
  Theorem 3.8 give. See `BenziGolubLiesen.signFlipped_roots_re_of_lt`.

**Section 10**

* **Theorem 10.1** (correction). The source gives the eigenvalue $1$ of
  $\mathcal{P}^{-1}\mathcal{A}$ the multiplicity $2m$. The characteristic polynomial is
  $(\lambda - 1)^{2m}$ times the characteristic polynomial of the reduced matrix, and the reduced
  pencil can supply further roots at $1$. The eigenvector lifted from a reduced eigenvector $z$ has
  primal component $Zz$. See `BenziGolubLiesen.theorem_10_1` and
  `BenziGolubLiesen.theorem_10_1_multiplicity_example`.
* **Lemma 10.2(ii)** (correction). The source requires $y \neq 0$ for the eigenvalue $0$. The
  condition is $Ex = 0$ alone, with $y$ arbitrary as long as $(x, y) \neq 0$. See
  `BenziGolubLiesen.lemma_10_2_ii` and `BenziGolubLiesen.lemma_10_2_zero_multiplier_example`.
* **Lemma 10.2(iii)** (correction). The source prints the upper bound $\lambda_{\max}(E)$. The upper
  bound is $\max\{0, \lambda_{\max}(E)\}$: for $B = C = 1$ and $E = -1$ the eigenvalue $-1/2$
  exceeds $\lambda_{\max}(E) = -1$. See `BenziGolubLiesen.lemma_10_2_iii` and
  `BenziGolubLiesen.lemma_10_2_upper_endpoint_example`.

## Not formalized

All numbered theorems and the numbered lemma of the survey are formalized, and no module records an
omitted item.
-/
