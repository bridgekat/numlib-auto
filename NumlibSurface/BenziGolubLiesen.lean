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

**Section 1**

* **Section 1.1, quadratic Lagrangian saddle** (generalization). The source identifies
  block-system solutions as saddle points. The equivalence also gives the reverse implication.
  See `BenziGolubLiesen.isSaddlePoint_quadraticLagrangian_iff`.

**Section 2**

* **Equation (2.13)** (generalization). The Stokes energy takes an abstract bilinear
  form and load. The printed functional is the case of the Dirichlet form and body load.
  See `BenziGolubLiesen.stokesEnergy`.
* **Stokes variational interpretation** (reading). The weak equations use an algebraic
  pressure functional on the divergence space. See
  `BenziGolubLiesen.stokes_minimizer_iff_weak_equations`.
* **(2.21)** (typo). The variable minimized over is $y$, not $x$.
* **(2.21)–(2.24)** (generalization). The equivalences omit the printed dimension
  inequalities. See `BenziGolubLiesen.equalityLeastSquares_iff_augmented` and
  `BenziGolubLiesen.weightedLeastSquares_iff_augmented`.
* **Paragraph after (2.24)** (reading). For singular covariance, the minimization is over
  noise vectors satisfying the factored observation equation. See
  `BenziGolubLiesen.generalizedLeastSquares_iff_augmented`.
* **After (2.37)** (correction). Strict convexity of the objective does not imply positive
  definiteness of its Hessian at the current iterate. See `Section02.InteriorPoint`.

**Section 3**

* **Section 3.1, Schur complement** (reading). The total matrix inverse gives $S=-C$
  when $A$ is singular. The factorization identities require nonsingularity. See
  `BenziGolubLiesen.saddleSchurComplement`.
* **(3.5)** (correction). With the survey's negative Schur complement $S$, the multiplier is
  $-S^{-1}BA^{-1}f$, as follows from (3.4). See
  `BenziGolubLiesen.saddlePointSolution_zero_constraint`.
* **(3.5)** (generalization). The solution formula requires invertible $A$ and $BA^{-1}B^T$;
  the source assumes symmetric positive definite $A$. See
  `BenziGolubLiesen.saddlePointSolution_zero_constraint`.
* **Section 3.3, oblique projector** (generalization). The range and kernel
  calculation needs nonsingularity of $BA^{-1}B^T$, with no positive definiteness
  hypothesis on $A$. See `BenziGolubLiesen.saddleObliqueProjector_spec`.
* **Equation (3.8)** (generalization). The inverse formula requires invertibility of
  $Z^TAZ$ directly. The source obtains it from a positive semidefinite symmetric part and
  a kernel-intersection condition. See `BenziGolubLiesen.saddlePointMatrix_inv_eq_of_nullBasis`.
* **After (3.8)** (correction). The projector $I-ZZ^T$ assumes orthonormal columns of $Z$.
  For a general null basis it is $I-Z(Z^TZ)^{-1}Z^T$. The inverse does not require orthonormality.
* **Paragraph after Theorem 3.8** (correction). The source calls the nonreal eigenvalues of the
  sign-flipped form (3.13) purely imaginary. They have real part $\eta / 2$, as the formulas of
  Theorem 3.8 give. See `BenziGolubLiesen.signFlipped_roots_re_of_lt`.
* **Equation (3.13)** (generalization). The matrix is defined with a real multiplier
  on the lower coupling block, including the printed signs $+1$ and $-1$. See
  `BenziGolubLiesen.scaledSaddlePointMatrix`.
* **Section 3.5, zero constraint right-hand side** (reading). The block-column identity
  holds for the total matrix inverse. It describes a solution via the inverse when the
  saddle matrix is nonsingular. See `BenziGolubLiesen.saddlePointMatrix_inv_mulVec_zero_right`.
* **Equation (3.14)** (generalization). Adding $B^TW$ times the constraint equation
  preserves the solution set for arbitrary $W$. See
  `BenziGolubLiesen.augmentedSaddlePointSystem_iff`.
* **After (3.14)** (correction). Positivity of $A$ on $\ker B$ alone need not make
  $A+\gamma B^TB$ positive definite for every $\gamma>0$. The result uses positive
  semidefiniteness of $A$ and the trivial kernel intersection. See
  `BenziGolubLiesen.posDef_augmentedTopBlock`.

**Sections 5–8**

* **Equations (5.1)–(5.2)** (generalization). The reduced equations are equivalent to the
  original equations even when the full saddle matrix is singular, provided $A$ is
  invertible. See `BenziGolubLiesen.saddlePointMatrix_mulVec_iff_schurReduction`.
* **Equations (6.1)–(6.2)** (generalization). The equivalence of the equations
  does not require the kernel condition used for uniqueness. See
  `BenziGolubLiesen.nullSpace_reduced_system_iff`.
* **Equation (6.4)** (generalization). The two shift identities use any real $\rho$
  and any matrix $A$ with the stated compression hypotheses. See
  `BenziGolubLiesen.reducedHessian_add_smul_one` and
  `BenziGolubLiesen.reducedHessian_add_smul_one_eq_spectral`.
* The kernel-intersection test in §6 requires a positive semidefinite symmetric part, and the
  existence assertion for (7.2) uses positive semidefiniteness of $C$. The real-spectrum and
  positive-definiteness claims for Uzawa use symmetry and full row rank as specified in §8.1's
  formal statements. See `Section06`, `Section07` and `Section08`.
* **Equations (8.1)–(8.2)** (generalization). The update allows any real relaxation
  parameter, and the splitting permits any nonzero one. The update uses the total inverse.
  See `BenziGolubLiesen.uzawaStep` and `BenziGolubLiesen.uzawaSplitting`.
* **Section 8.1, primal minimization** (correction). Invertibility of $A$ alone gives
  a stationary point. The strict minimum result requires positive definiteness. See
  `BenziGolubLiesen.uzawa_primal_lt`.
* **Equation (8.11)** (generalization). The equivalence with the two penalty equations
  holds for any nonzero $\gamma$. See `BenziGolubLiesen.penalty_regularized_iff`.

**Section 9**

* **Section 9.2** (generalization). Conditional terminal exactness uses weaker matrix
  assumptions. The residual polynomial bounds admit complex data or enclosing endpoints,
  and the minimax sequence and its root limit are defined for any real set.
* **Section 9.2, prescribed GMRES curve** (reading). The positive normalized prefix and
  nonzero spectrum specify a nonsingular pretermination problem. Normal matrices are allowed.
* **Section 9.3** (generalization). The symmetry result permits a singular factor under
  total inversion. See `BenziGolubLiesen.isHermitian_symmetricPreconditionedMatrix`.

**Section 10**

* **Section 10.1.1** (correction). The exact block diagonal spectrum is contained in the three
  listed values. When $A=B_1=B_2=[1]$, the eigenvalue $1$ is absent. See
  `BenziGolubLiesen.blockDiagonalPreconditioned_eigenvalues`.
* **Section 10.1.2** (generalization). The triangular result gives the annihilator $(X-1)^2$
  even when the lower-left block vanishes. The minimal polynomial can then have degree one.
  See `BenziGolubLiesen.blockTriangularPreconditioned_charpoly`.
* **Block and constraint formulas** (generalization). Several identities use explicit
  invertibility hypotheses, arbitrary Schur or scaling blocks, or total inverses. See
  `Section10.Block`, `Section10.ConstraintFormulas` and `Section10.HSS`.
* **(10.8)** (correction). The sign change of the lower block row also changes its right-hand
  side. See `Section10.Block`.
* **Section 10.2, square constraint block** (generalization). The square-zero identity
  includes $G=A$, where the preconditioned matrix is the identity. See
  `BenziGolubLiesen.constraintPreconditioned_square_case`.
* **End of Section 10.2** (correction). The printed strict lower endpoint $\beta$ can be
  attained. The spectrum result gives the weaker universal interval $(0,1]$. See
  `BenziGolubLiesen.regularizedConstraintPreconditioned_spectrum`.
* **Theorem 10.1** (correction). The source gives the eigenvalue $1$ of
  $\mathcal{P}^{-1}\mathcal{A}$ the multiplicity $2m$. The characteristic polynomial is
  $(\lambda - 1)^{2m}$ times the characteristic polynomial of the reduced matrix, and the reduced
  pencil can supply further roots at $1$. The eigenvector lifted from a reduced eigenvector $z$ has
  primal component $Zz$. See `BenziGolubLiesen.theorem_10_1` and
  `BenziGolubLiesen.theorem_10_1_multiplicity_example`.
* **Lemma 10.2(i)–(ii)** (generalization). The Rayleigh formula and zero-eigenvalue
  characterization hold for nonsymmetric $E$ as well. See `BenziGolubLiesen.lemma_10_2_i`
  and `BenziGolubLiesen.lemma_10_2_ii`.
* **Lemma 10.2(ii)** (correction). The source requires $y \neq 0$ for the eigenvalue $0$. The
  condition is $Ex = 0$ alone, with $y$ arbitrary as long as $(x, y) \neq 0$. See
  `BenziGolubLiesen.lemma_10_2_ii` and `BenziGolubLiesen.lemma_10_2_zero_multiplier_example`.
* **Lemma 10.2(iii)** (correction). The source prints the upper bound $\lambda_{\max}(E)$. The upper
  bound is $\max\{0, \lambda_{\max}(E)\}$: for $B = C = 1$ and $E = -1$ the eigenvalue $-1/2$
  exceeds $\lambda_{\max}(E) = -1$. See `BenziGolubLiesen.lemma_10_2_iii` and
  `BenziGolubLiesen.lemma_10_2_upper_endpoint_example`.

* **Section 10.3, HSS spectral disk** (correction). A trivial common kernel with $B$
  does not suffice for the strict disk when $H$ is singular. The theorem requires
  $H$ positive definite and also applies over $\mathbb C$. See
  `BenziGolubLiesen.hss_saddle_spectrum_disk`.
* **Equation (10.34)** (correction). The transpose-congruence formula requires symmetric
  $G_{11}$ and $G_{21}=G_{12}^T$. The algebraic identity here still permits nonsymmetric
  $G_{22}$. See `BenziGolubLiesen.schilders_factorization`.
* **Equation (10.35)** (generalization). The congruence needs symmetry of $G_{11}$ and
  transposed off-diagonal blocks, but $G_{22}$ may be nonsymmetric. See
  `BenziGolubLiesen.saunders_factorization`.

**Section 11**

* **Two-grid procedure** (reading). The six steps form a linear residual-correction
  cycle here, with fixed damping and linear responses. See `BenziGolubLiesen.twoGridCycle`.
* **Limit of (11.1)** (reading). The limit solves the system even when the matrix is
  singular. Its inverse expression assumes nonsingularity. See
  `BenziGolubLiesen.distributiveRelaxation_limit_solves`.
* **Pressure-scaled distribution** (reading). The printed block $-BA^{-1}B^TQ$ is for
  $C=0$. Retaining $C$ gives $(-BA^{-1}B^T-C)Q$. See
  `BenziGolubLiesen.distributiveTransform_mul`.
* **Smoothers and patch corrections** (reading). Matrix definitions use total inverses.
  Vanka uses fixed weighted patch responses and a supplied sweep order. See `Section11`.
* **Hybrid additive-local/coarse correction** (reading). The coarse update acts on the
  residual left by the additive local update. See `BenziGolubLiesen.twoLevelHybridSchwarz`.

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
