/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenziGolubLiesen.Section01
import NumlibSurface.BenziGolubLiesen.Section02
import NumlibSurface.BenziGolubLiesen.Section03.Conditioning
import NumlibSurface.BenziGolubLiesen.Section03.Factorization
import NumlibSurface.BenziGolubLiesen.Section03.Inverse
import NumlibSurface.BenziGolubLiesen.Section03.Solvability
import NumlibSurface.BenziGolubLiesen.Section03.Spectrum
import NumlibSurface.BenziGolubLiesen.Section05
import NumlibSurface.BenziGolubLiesen.Section06
import NumlibSurface.BenziGolubLiesen.Section07
import NumlibSurface.BenziGolubLiesen.Section08
import NumlibSurface.BenziGolubLiesen.Section09
import NumlibSurface.BenziGolubLiesen.Section09.Convergence
import NumlibSurface.BenziGolubLiesen.Section09.Implementation
import NumlibSurface.BenziGolubLiesen.Section10.Block
import NumlibSurface.BenziGolubLiesen.Section10.Constraint
import NumlibSurface.BenziGolubLiesen.Section10.ConstraintFormulas
import NumlibSurface.BenziGolubLiesen.Section10.Factorization
import NumlibSurface.BenziGolubLiesen.Section10.HSS
import NumlibSurface.BenziGolubLiesen.Section10.Pencil
import NumlibSurface.BenziGolubLiesen.Section11

/-!
# Benzi, Golub and Liesen, *Numerical solution of saddle point problems*

The Acta Numerica survey [benzi2005numerical] studies linear systems whose coefficient matrix has
the saddle-point form
$$\mathcal{A} = \begin{bmatrix} A & B_1^T \\ B_2 & -C \end{bmatrix},$$
with $A \in \mathbb{R}^{n \times n}$, $B_1, B_2 \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times m}$. The library formalizes their application models, algebraic
properties, solvers and preconditioners. Reusable results live in `Numlib.LinearAlgebra.Matrix`,
`Numlib.Optimization`, `Numlib.Stationary`, `Numlib.Krylov`, `Numlib.Preconditioner`,
`Numlib.Multigrid` and `Numlib.DomainDecomposition`.

## Coverage

The library formalizes all 13 numbered results (Theorems 3.1–3.8, 9.1–9.3 and 10.1, and Lemma
10.2) together with substantive unnumbered definitions and propositions. The coverage includes
quadratic Lagrangians, least squares and barrier systems, block factorization and elimination,
null-space and stationary iterations, Krylov convergence, and block, constraint, HSS and multilevel
preconditioning. Algorithms are modeled in exact arithmetic. Individual modules record
qualifications and mathematical items not formalized.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1 Introduction | `Section01` | classification, quadratic KKT equations and saddle value |
| §2 Applications | `Section02` | weak Stokes equations, least squares, barrier Newton systems |
| §3.1 Block factorizations | `Section03.Factorization` | Schur complement, (3.1)–(3.4) |
| §3.2 Solvability conditions | `Section03.Solvability` | Theorems 3.1–3.4 and examples |
| §3.3 Inverses | `Section03.Inverse` | projection, weighted residual, quasidefiniteness, (3.8) |
| §3.4 Spectral properties | `Section03.Spectrum` | signature transform and Theorems 3.5–3.8 |
| §3.5 Conditioning | `Section03.Conditioning` | zero right-hand side block and augmentation |
| §5 Schur complement reduction | `Section05` | reduced solves and augmentation |
| §6 Null space methods | `Section06` | null bases, reduced Hessians and recovery |
| §7 Coupled direct solvers | `Section07` | pivoted, block and quasidefinite $LDL^T$ |
| §8 Stationary iterations | `Section08` | Uzawa, Arrow–Hurwicz, penalty and multipliers |
| §9 Krylov subspace methods | `Section09` | (9.1)–(9.4), Theorems 9.1–9.3 |
| §9.2 Convergence | `Section09.Convergence` | termination, polynomial and Chebyshev bounds |
| §9.3 Implementation | `Section09.Implementation` | symmetry-preserving split preconditioning |
| §10.1 Block preconditioning | `Section10.Block` | exact block spectra, sweeps and approximations |
| §10.2 Constraint and indefinite preconditioning | `Section10.Constraint` | Theorem 10.1 |
| §10.2 Constraint formulas | `Section10.ConstraintFormulas` | feasibility and regularization |
| §10.2 Constraint and indefinite preconditioning | `Section10.Pencil` | (10.21), Lemma 10.2 |
| §10.3 Hermitian/skew-Hermitian splitting | `Section10.HSS` | split iterations and spectral disk |
| §10.4 Approximate factorizations | `Section10.Factorization` | exact block and signed factors |
| §11 Multilevel methods | `Section11` | transfer, coarse correction, smoothers and Schwarz |

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

**Section 2**

* **(2.21)** (typo). The variable minimized over is $y$, not $x$.
* **After (2.37)** (correction). Strict convexity of the objective does not imply positive
  definiteness of its Hessian at the current iterate. See `Section02.InteriorPoint`.

**Section 3**

* **(3.5)** (correction). With the survey's negative Schur complement $S$, the multiplier is
  $-S^{-1}BA^{-1}f$, as follows from (3.4). See `saddlePointSolution_zero_constraint`.
* **After (3.8)** (correction). The projector $I-ZZ^T$ assumes orthonormal columns of $Z$.
  For a general null basis it is $I-Z(Z^TZ)^{-1}Z^T$. The inverse does not require orthonormality.
* **Paragraph after Theorem 3.8** (correction). The source calls the nonreal eigenvalues of the
  sign-flipped form (3.13) purely imaginary. They have real part $\eta / 2$, as the formulas of
  Theorem 3.8 give. See `BenziGolubLiesen.signFlipped_roots_re_of_lt`.

**Sections 6–8**

* The kernel-intersection test in §6 requires a positive semidefinite symmetric part, and the
  existence assertion for (7.2) uses positive semidefiniteness of $C$. The real-spectrum and
  positive-definiteness claims for Uzawa use symmetry and full row rank as specified in §8.1's
  formal statements. See `Section06`, `Section07` and `Section08`.

**Section 10**

* **(10.8)** (correction). The sign change of the lower block row also changes its right-hand
  side. See `Section10.Block`.
* **End of §10.2** (correction). The lower bound $\beta$ for regularized constraint
  preconditioning can be attained (take $A=B=C=[1]$). See `Section10.ConstraintFormulas`.
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

* **§2.** Strong boundary-value PDEs, discretization and inf-sup estimates, and barrier path
  convergence require concrete function spaces, meshes, or an algorithm additional to the
  weak or algebraic models in the survey.
* **§3.** The nonreal eigenvalue count for the signature form, mesh-uniform conditioning, and the
  uniform bounds for weighted pseudoinverses as the diagonal weights vary are not proved here.
* **§§5–8.** The graph cycle and spanning-tree claims, sparse symbolic elimination and finite
  precision stability, and mesh-dependent rates for inexact and variable stationary variants
  are not included. The equation-level descriptions do not imply those results.
* **§9.** Sharp worst-case minimax bounds, quantitative estimates of the asymptotic limit
  in (9.13), and some cited normal/nonnormal comparisons are not proved.
* **§10.** Remaining gaps include exact ideal block spectral multiplicities, quantitative mesh
  estimates, the general constraint-preconditioned grade bound, sharp regularization endpoints,
  and quantitative HSS shift selection. The §10 modules give the specific hypotheses and gaps.
* **§11.** Nonlinear FAS, adaptive damping, balancing Neumann–Neumann, and PDE-specific Schwarz
  and multigrid convergence and complexity estimates are not formalized.
* **§§4, 12 and 13.** Solver taxonomy, historical software listings and concluding discussion
  introduce no new standalone mathematical statements. Historical notes, experiments and
  implementation performance comparisons are not formalized.
-/
