/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.SaadSparse.Chapter01.Basics
import NumlibSurface.SaadSparse.Chapter01.Section07
import NumlibSurface.SaadSparse.Chapter01.Section08
import NumlibSurface.SaadSparse.Chapter01.Section09
import NumlibSurface.SaadSparse.Chapter01.Section10
import NumlibSurface.SaadSparse.Chapter01.Section11
import NumlibSurface.SaadSparse.Chapter01.Section12
import NumlibSurface.SaadSparse.Chapter01.Section13
import NumlibSurface.SaadSparse.Chapter02.Section02
import NumlibSurface.SaadSparse.Chapter02.Section03
import NumlibSurface.SaadSparse.Chapter02.Section04
import NumlibSurface.SaadSparse.Chapter02.Section05
import NumlibSurface.SaadSparse.Chapter03.Section02
import NumlibSurface.SaadSparse.Chapter03.Section03
import NumlibSurface.SaadSparse.Chapter03.Section04
import NumlibSurface.SaadSparse.Chapter04.Section01
import NumlibSurface.SaadSparse.Chapter04.Section02
import NumlibSurface.SaadSparse.Chapter04.Section03
import NumlibSurface.SaadSparse.Chapter05.Section01
import NumlibSurface.SaadSparse.Chapter05.Section03
import NumlibSurface.SaadSparse.Chapter05.Section04
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter06.Section02
import NumlibSurface.SaadSparse.Chapter06.Section03
import NumlibSurface.SaadSparse.Chapter06.Section04
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter06.Section06
import NumlibSurface.SaadSparse.Chapter06.Section07
import NumlibSurface.SaadSparse.Chapter06.Section08
import NumlibSurface.SaadSparse.Chapter06.Section09
import NumlibSurface.SaadSparse.Chapter06.Section10
import NumlibSurface.SaadSparse.Chapter06.Section11
import NumlibSurface.SaadSparse.Chapter06.Section12
import NumlibSurface.SaadSparse.Chapter07.Section01
import NumlibSurface.SaadSparse.Chapter07.Section02
import NumlibSurface.SaadSparse.Chapter07.Section03
import NumlibSurface.SaadSparse.Chapter07.Section04
import NumlibSurface.SaadSparse.Chapter08.Section01
import NumlibSurface.SaadSparse.Chapter08.Section02
import NumlibSurface.SaadSparse.Chapter08.Section03
import NumlibSurface.SaadSparse.Chapter08.Section04
import NumlibSurface.SaadSparse.Chapter09.Section01
import NumlibSurface.SaadSparse.Chapter09.Section02
import NumlibSurface.SaadSparse.Chapter09.Section03
import NumlibSurface.SaadSparse.Chapter09.Section04
import NumlibSurface.SaadSparse.Chapter09.Section05
import NumlibSurface.SaadSparse.Chapter09.Section06
import NumlibSurface.SaadSparse.Chapter10.Section02
import NumlibSurface.SaadSparse.Chapter10.Section03
import NumlibSurface.SaadSparse.Chapter10.Section04
import NumlibSurface.SaadSparse.Chapter10.Section05
import NumlibSurface.SaadSparse.Chapter10.Section08
import NumlibSurface.SaadSparse.Chapter11
import NumlibSurface.SaadSparse.Chapter12.Section02
import NumlibSurface.SaadSparse.Chapter12.Section03
import NumlibSurface.SaadSparse.Chapter12.Section04
import NumlibSurface.SaadSparse.Chapter12.Section07
import NumlibSurface.SaadSparse.Chapter13.Section02
import NumlibSurface.SaadSparse.Chapter13.Section03
import NumlibSurface.SaadSparse.Chapter13.Section04
import NumlibSurface.SaadSparse.Chapter13.Section05
import NumlibSurface.SaadSparse.Chapter13.Section06
import NumlibSurface.SaadSparse.Chapter14.Section02
import NumlibSurface.SaadSparse.Chapter14.Section03
import NumlibSurface.SaadSparse.Chapter14.Section04
import NumlibSurface.SaadSparse.Chapter14.Section05
import NumlibSurface.SaadSparse.Chapter14.Section06
import NumlibSurface.SaadSparse.Common

/-!
# Saad, *Iterative Methods for Sparse Linear Systems*

This library formalizes the book [saad2003iterative] of Yousef Saad, second edition, on the
iterative solution of large sparse linear systems $Ax = b$. The book starts from the linear algebra
of matrices and projectors, the discretization of partial differential equations and the storage of
sparse matrices. It then treats the classical relaxation methods, projection methods, the Krylov
subspace methods (Arnoldi, FOM, GMRES, Lanczos, the conjugate gradient method, BCG, QMR and the
transpose-free variants), the methods for the normal equations, preconditioned iterations and
preconditioning techniques, multigrid and domain decomposition. The library has one module for each
section of the book that it covers, and it reaches every chapter that states a numbered result. Each
module states the results of the book in the terms of the book: the positive definiteness of a
matrix that need not be symmetric, the splitting $A = D - E - F$, and the algorithms written out as
Lean functions. The proofs specialize the backbone, mainly `Numlib.LinearAlgebra`, `Numlib.Eigen`,
`Numlib.Stationary`, `Numlib.Projection`, `Numlib.Krylov`, `Numlib.Preconditioner`,
`Numlib.Multigrid` and `Numlib.DomainDecomposition`; almost nothing is proved in the library that is
not proved in the backbone.

## Coverage

The library has 68 modules: 66 modules for units of the book and the two modules `Common` and
`Chapter06.Common` of shared vocabulary. The formalized items are the theorems, propositions,
lemmas, corollaries and numbered definitions of the book, its algorithms, its numbered equations,
its examples, and the problems that the text cites. A worked example over a small matrix or graph is
stated as a theorem, for example the storage layouts of §3.4 and §11.5, the assembly of Example 2.1
and the interpolation weights of Example 13.9. A definition that the book names is restated even
where Mathlib has the content, as `SaadSparse.Chapter01.definition_1_1` for the spectrum and
`SaadSparse.Chapter01.definition_1_23` for the entrywise order.

Some modules cover more than one section. `Chapter01.Basics` covers §1.1–1.6, because almost all of
their content is Mathlib restated in the notation of the book. `Chapter05.Section01` covers §5.1 and
§5.2, which share the numbering (5.1)–(5.11). There is no module for §6.1: it is the introduction of
Chapter 6, and its one substantive paragraph is stated with §6.2. Chapter 11 states no theorem; its
module states its one example with mathematical content, the jagged diagonal format of §11.5.4.

Two numbered theorems of the book are not formalized: Theorem 10.16 and Theorem 14.16. The book
quotes both from other sources without proof. Out of scope are implementation advice, the exercises
that the text does not cite, measured tables and figures (Examples 8.1, 10.1, 12.2, 13.4 and 13.5),
and the examples whose data are only in a figure that the text does not reproduce (Examples 3.4–3.6,
on the mesh of Figure 2.10, and Example 11.2). The section `Not formalized` lists every omitted
item.

## Contents

| Source | Module | Subject |
|---|---|---|
| Conventions | `Common` | vectors, matrices, $\lambda_{\min}$ and $\lambda_{\max}$ |
| §1.1–1.6 Matrices, eigenvalues, norms | `Chapter01.Basics` | Def. 1.1, Props. 1.2–1.4, norms |
| §1.7 Orthogonal vectors and subspaces | `Chapter01.Section07` | Gram–Schmidt, QR, Householder |
| §1.8 Canonical forms of matrices | `Chapter01.Section08` | Jordan, Schur, Theorems 1.6–1.12 |
| §1.9 Normal and Hermitian matrices | `Chapter01.Section09` | field of values, Theorems 1.14–1.22 |
| §1.10 Nonnegative matrices, M-matrices | `Chapter01.Section10` | Theorems 1.25–1.33 |
| §1.11 Positive-definite matrices | `Chapter01.Section11` | Theorems 1.34 and 1.35 (Bendixson) |
| §1.12 Projection operators | `Chapter01.Section12` | Lemma 1.36 to Corollary 1.39 |
| §1.13 Basic concepts in linear systems | `Chapter01.Section13` | (1.74)–(1.76), Example 1.5 |
| §2.2 Finite difference methods | `Chapter02.Section02` | truncation errors, model matrices |
| §2.3 The finite element method | `Chapter02.Section03` | Galerkin system, assembly, Example 2.1 |
| §2.4 Mesh generation and refinement | `Chapter02.Section04` | midpoint refinement keeps angles |
| §2.5 The finite volume method | `Chapter02.Section05` | sign structure of the scheme |
| §3.2 Graph representations | `Chapter03.Section02` | adjacency graph, patterns of products |
| §3.3 Permutations and reorderings | `Chapter03.Section03` | reorderings, irreducibility |
| §3.4 Storage schemes | `Chapter03.Section04` | coordinate, CSR, MSR, diagonal, Ellpack |
| §4.1 Jacobi, Gauss–Seidel and SOR | `Chapter04.Section01` | splittings, block relaxation |
| §4.2 Convergence | `Chapter04.Section02` | Theorem 4.1, diagonal dominance, SOR |
| §4.3 Alternating direction methods | `Chapter04.Section03` | Peaceman–Rachford ADI |
| §5.1–5.2 Projection methods | `Chapter05.Section01` | Propositions 5.1–5.6, Theorem 5.7 |
| §5.3 One-dimensional projection processes | `Chapter05.Section03` | Lemma 5.8, Thms. 5.9, 5.10 |
| §5.4 Additive and multiplicative processes | `Chapter05.Section04` | Algorithms 5.5 and 5.6 |
| Chapter 6, the data of a linear system | `Chapter06.Common` | $r_0$, $\beta$, $v_1$, $e_1$ |
| §6.1–6.2 Krylov subspaces | `Chapter06.Section02` | grade, Propositions 6.1–6.3 |
| §6.3 Arnoldi's method | `Chapter06.Section03` | Algorithms 6.1–6.3, Props. 6.4–6.6 |
| §6.4 The full orthogonalization method | `Chapter06.Section04` | FOM, IOM, DIOM, Props. 6.7, 6.8 |
| §6.5 GMRES | `Chapter06.Section05` | GMRES, DQGMRES, Props. 6.9–6.17 |
| §6.6 The symmetric Lanczos algorithm | `Chapter06.Section06` | Theorem 6.19 |
| §6.7 The conjugate gradient method | `Chapter06.Section07` | Lanczos, D-Lanczos, CG, Prop. 6.20 |
| §6.8 The conjugate residual method | `Chapter06.Section08` | Algorithm 6.20 |
| §6.9 GCR, ORTHOMIN and ORTHODIR | `Chapter06.Section09` | Lemma 6.21 |
| §6.10 Optimality, Faber–Manteuffel | `Chapter06.Section10` | Prop. 6.22, Lemma 6.23, Thm. 6.24 |
| §6.11 Convergence analysis | `Chapter06.Section11` | Theorem 6.25 to Corollary 6.33 |
| §6.12 Block Krylov methods | `Chapter06.Section12` | Ruhe's variant, block FOM, block GMRES |
| §7.1 Lanczos biorthogonalization | `Chapter07.Section01` | Algorithm 7.1, Proposition 7.1 |
| §7.2 The two-sided Lanczos algorithm | `Chapter07.Section02` | Algorithm 7.2, Petrov–Galerkin |
| §7.3 BCG and QMR | `Chapter07.Section03` | Prop. 7.3, Theorem 7.4, smoothing |
| §7.4 Transpose-free variants | `Chapter07.Section04` | CGS, BICGSTAB, TFQMR, (7.83) |
| §8.1 The normal equations | `Chapter08.Section01` | least squares, conditioning |
| §8.2 Row projection methods | `Chapter08.Section02` | Cimmino, Kaczmarz, NE-SOR |
| §8.3 Conjugate gradient, normal equations | `Chapter08.Section03` | CGNR, CGNE |
| §8.4 Saddle-point problems | `Chapter08.Section04` | Uzawa's method, Example 8.2 |
| §9.1 Left, right and split preconditioning | `Chapter09.Section01` | (9.1)–(9.3) |
| §9.2 The preconditioned CG method | `Chapter09.Section02` | Algorithm 9.1 and its variants |
| §9.3 Preconditioned GMRES | `Chapter09.Section03` | Algorithms 9.4 and 9.5 |
| §9.4 Flexible variants | `Chapter09.Section04` | FGMRES, DQGMRES, Props. 9.2, 9.3 |
| §9.5 Preconditioned CG, normal equations | `Chapter09.Section05` | Algorithms 9.7 and 9.8 |
| §9.6 The Concus–Golub–Widlund algorithm | `Chapter09.Section06` | the recurrence (9.29) |
| §10.2 Jacobi, SOR, SSOR preconditioners | `Chapter10.Section02` | splittings as preconditioners |
| §10.3 Incomplete LU factorizations | `Chapter10.Section03` | ILU(0), ILU($p$), Thms. 10.1–10.7 |
| §10.4 Threshold strategies and ILUT | `Chapter10.Section04` | $\hat M$ matrices, Theorem 10.8 |
| §10.5 Approximate inverse preconditioners | `Chapter10.Section05` | Prop. 10.9 to Lemma 10.15 |
| §10.8 Preconditioners, normal equations | `Chapter10.Section08` | Prop. 10.17, Theorem 10.18 |
| Chapter 11 Parallel implementations | `Chapter11` | Example 11.1, jagged diagonal format |
| §12.2 Overlapping block-Jacobi | `Chapter12.Section02` | the weighted additive step |
| §12.3 Polynomial preconditioners | `Chapter12.Section03` | Neumann, Chebyshev, least squares |
| §12.4 Multicolouring | `Chapter12.Section04` | the red–black reduced system |
| §12.7.2 Winget regularization | `Chapter12.Section07` | positive definiteness (12.25) |
| §13.2 Model problems, smoother spectra | `Chapter13.Section02` | Jacobi, Gauss–Seidel |
| §13.3 Inter-grid operations | `Chapter13.Section03` | prolongation, restriction |
| §13.4 The standard multigrid cycles | `Chapter13.Section04` | Lemma 13.1, cycles, Theorem 13.2 |
| §13.5 Analysis of the two-grid cycle | `Chapter13.Section05` | Theorem 13.3, Examples 13.7, 13.8 |
| §13.6 Algebraic multigrid | `Chapter13.Section06` | the quadratic form (13.68)–(13.69) |
| §14.2 Block Gaussian elimination | `Chapter14.Section02` | Schur complement, Prop. 14.1 |
| §14.3 Schwarz alternating procedures | `Chapter14.Section03` | Schwarz methods, Thms. 14.2–14.9 |
| §14.4 Schur complement approaches | `Chapter14.Section04` | induced preconditioners, Prop. 14.10 |
| §14.5 Full matrix methods | `Chapter14.Section05` | Propositions 14.11 and 14.12 |
| §14.6 Graph partitioning | `Chapter14.Section06` | spectral bisection, Defs. 14.13–14.15 |

## Conventions

* A declaration is named for the item that it states: `SaadSparse.Chapter06.theorem_6_29` is Theorem
  6.29, `SaadSparse.Chapter06.proposition_6_13` is Proposition 6.13,
  `SaadSparse.Chapter06.equation_6_43` is equation (6.43), `SaadSparse.Chapter04.definition_4_5` is
  Definition 4.5, and `SaadSparse.Chapter06.problem_6_25` is Problem P-6.25. A theorem about an
  algorithm starts with its number, as `SaadSparse.Chapter06.algorithm_6_2_eq_alg_6_1`. Where one
  item needs several declarations, for its separate clauses or the two directions of an equivalence,
  a suffix tells them apart, as in `SaadSparse.Chapter06.problem_6_25_le`.
* An object that the book names but does not number has a descriptive name, such as
  `SaadSparse.Chapter06.arnoldiCGS`, `SaadSparse.Chapter06.gmresFixed` and
  `SaadSparse.Chapter06.smoothEta`. Each such definition has a lemma that identifies it with its
  backbone counterpart, and the proofs of the module go through these lemmas.
* The declarations of Chapter $N$ are in the namespace `SaadSparse.ChapterNN`, with the chapter
  number written with two digits. In §1.11–1.13, the definitions and some results about a matrix are
  in the namespace `Matrix`, so that dot notation reads as in the book. The shared vocabulary of the
  library is in `SaadSparse` (module `Common`). The quantities $r_0 = b - Ax_0$,
  $\beta = \|r_0\|_2$, $v_1 = r_0/\beta$ and $e_1$ that every Krylov method of Chapter 6 uses are in
  module `Chapter06.Common`.
* A vector of $\mathbb{R}^n$ or $\mathbb{C}^n$ is an element of `EuclideanSpace 𝕜 (Fin n)`, and a
  matrix is a `Matrix (Fin n) (Fin n) 𝕜`. The product $Ax$ is `Matrix.toEuclideanLin A x`, written
  `A ⬝ x` with the scoped notation of `SaadSparse`; Chapter 6 writes the operator as
  `SaadSparse.Chapter06.op A`. Componentwise statements use the function type `Fin n → 𝕜` with
  `A *ᵥ x` and `x ⬝ᵥ y`, and `WithLp.toLp 2` and `WithLp.ofLp` translate between the two types.
* The inner product of the book, $(x, y) = \sum_i x_i \bar y_i$, is `inner 𝕜 y x`: Mathlib's inner
  product is conjugate-linear in the first argument, and the book's in the second. Over $\mathbb{R}$
  the two agree. Every complex statement is written so that only the real part, the norm, or the
  vanishing of an inner product matters.
* Definitions and algorithms are polymorphic in the field `𝕜` with `[RCLike 𝕜]`, so that the complex
  GMRES of §6.5.9 is the same code as the real GMRES of §6.5.3. Each numbered result is stated at
  the generality of the book: over $\mathbb{R}$ where the book says real, and over $\mathbb{C}$ for
  §6.5.9, Theorem 1.35, Theorem 6.11, Lemma 6.23, Theorem 6.24 and Proposition 6.32.
* A real matrix $A$ is **positive definite** in the book when $(Au, u) > 0$ for all $u \neq 0$, with
  no symmetry assumed. This is `Matrix.IsPositiveReal`, and the symmetric case is `Matrix.IsSPD`.
* The splitting $A = D - E - F$ into the diagonal $D$, the negated strict lower part $E$ and the
  negated strict upper part $F$ is `SaadSparse.Chapter04.D`, `SaadSparse.Chapter04.E` and
  `SaadSparse.Chapter04.F`.
* For a Hermitian matrix $H$, $\lambda_{\min}(H)$ and $\lambda_{\max}(H)$ are `SaadSparse.lambdaMin`
  and `SaadSparse.lambdaMax`, the extreme values of `Matrix.IsHermitian.eigenvalues`. The backbone
  takes spectral hypotheses as bounds on the quadratic form (`LinearMap.IsSymmetricBoundedBy`), not
  as lists of eigenvalues, and `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin` connects the
  two forms. So no proof in the library diagonalizes $A$.
* A real matrix acts on complex vectors through `Matrix.complexify`, and the spectral radius
  $\rho(A)$ of a real matrix is `Matrix.complexSpectralRadius A`.
* The book numbers the Arnoldi, Lanczos and incomplete orthogonalization vectors from $1$. The
  library indexes them by `ℕ` from $0$: `SaadSparse.Chapter06.arnoldiCGS A v₁ j` is $v_{j+1}$, and
  `SaadSparse.Chapter06.arnoldiCoeff A v₁ i j` is $h_{i+1,j+1}$. The Givens quantities $c_i$, $s_i$
  and $\gamma_i$ have the same shift. The iterates of CG, CR and GCR are numbered from $0$ in the
  book already and keep their indices. Matrices built from these data keep the dimensions of the
  book: $V_m$ is `Matrix (Fin n) (Fin m) 𝕜`, $H_m$ is `Matrix (Fin m) (Fin m) 𝕜` and $\bar H_m$ is
  `Matrix (Fin (m + 1)) (Fin m) 𝕜`.
* Division by $0$ gives $0$ in Lean. This reproduces the instruction "if $h_{j+1,j} = 0$ then Stop"
  of the book: every later vector is $0$, and the recurrences and expansion identities hold past the
  breakdown with no hypothesis. The instruction "set $m := j$" is `SaadSparse.Chapter06.mEff`, the
  number $\min(m, \mu)$ with $\mu$ the grade of $v_1$.

## Deviations from the source

**Chapter 1.**

* **Scope.** The common Hermitian estimate gives the inequalities from the extremal Rayleigh
  quotient formulas. See `SaadSparse.isSymmetricBoundedBy_toEuclideanLin`.
* **Propositions 1.2 and 1.4, Equations (1.2) and (1.5)** (generalization). The book uses complex
  scalars. The declarations also cover real scalars. See `SaadSparse.Chapter01.proposition_1_2`,
  `SaadSparse.Chapter01.proposition_1_4`, `SaadSparse.Chapter01.equation_1_2` and
  `SaadSparse.Chapter01.equation_1_5`.
* **§1.2, trace as a sum of eigenvalues** (generalization). The theorem also identifies the
  determinant as the product of the same eigenvalues. See
  `SaadSparse.Chapter01.trace_eq_sum_eigenvalues`.
* **Proposition 1.3** (generalization). The book gives one implication for the eigenvalues. The
  theorem identifies the two spectra by conjugation. See `SaadSparse.Chapter01.proposition_1_3`.
* **Equations (1.12)–(1.16), the norm formulas** (reading). The book states the formulas for
  rectangular matrices. The surface declarations use square matrices. See
  `SaadSparse.Chapter01.equation_1_14`, `SaadSparse.Chapter01.equation_1_15` and
  `SaadSparse.Chapter01.equation_1_16`.
* **Equation (1.18)** (typo). The book prints $\mathbb{C}^n = \operatorname{Ran}(A) \oplus
  \operatorname{Null}(A^T)$ in a complex setting, where $A^H$ is meant. See
  `SaadSparse.Chapter01.equation_1_18`.
* **Equation (1.18)** (reading). The book uses rectangular matrices. The declaration uses square
  matrices. See `SaadSparse.Chapter01.equation_1_18`.
* **Algorithms 1.1 and 1.2** (reading). The recurrences continue through zero pivots, putting a
  zero vector at each zero pivot. See `SaadSparse.Chapter01.gramSchmidt_expansion`,
  `SaadSparse.Chapter01.modifiedGramSchmidt` and `SaadSparse.Chapter01.algorithm_1_2_eq`.
* **Equation (1.19)** (generalization). The statement adds uniqueness with a positive real
  diagonal in $R$. See `SaadSparse.Chapter01.equation_1_19`.
* **Derivation of (1.22)** (typo). The book prints $\|x\|_1^2$ where $\|x\|_2^2$ is meant. See
  `SaadSparse.Chapter01.equation_1_22`.
* **Equation (1.22)** (generalization and reading). The complex reflector can target any
  coordinate, with phase $1$ at a zero pivot. See `SaadSparse.Chapter01.equation_1_22`.
* **Equation (1.25)** (typo). The book prints the entry $\beta + x_{ii}$ of the Householder
  direction, where $\beta + x_{kk}$, the pivot of step $k$, is meant. See
  `SaadSparse.Chapter01.householder_mulVec_apply_of_eq_zero`, and
  `SaadSparse.Chapter06.householderDir` for the Householder Arnoldi process of §6.3.
* **Equations (1.27)–(1.28) and Algorithm 1.3** (reading). The declaration states the final
  unitary factorization. See `SaadSparse.Chapter01.equation_1_28`.
* **§1.7, the leading identity columns** (generalization). A request for more than $n$ columns
  appends zero columns. See `SaadSparse.Chapter01.stdCols`.
* **Theorem 1.6 and the corollary to Proposition 1.7** (generalization). Both results also cover
  real scalars. See `SaadSparse.Chapter01.theorem_1_6` and
  `SaadSparse.Chapter01.diagonalizable_of_injective_eigenvalues`.
* **Theorem 1.8, the sentence after the block display** (correction). The index bounds the sizes
  of individual Jordan blocks. See `SaadSparse.Chapter01.theorem_1_8_index`.
* **§1.8.3, partial Schur decomposition** (reading). The declaration states invariance of the
  column span, selecting all columns if $k>n$. See `SaadSparse.Chapter01.theorem_1_9_partial`.
* **§1.8.3, real Schur form** (reading). The declaration asserts the block shape only. See
  `SaadSparse.Chapter01.realSchur`.
* **Theorem 1.10** (reading). The declaration treats real matrices using their complex spectral
  radius. See `SaadSparse.Chapter01.theorem_1_10`.
* **Theorem 1.11** (reading). The summability equivalence uses positive dimension. The separate
  nonsingularity theorem treats real matrices. See `SaadSparse.Chapter01.theorem_1_11` and
  `SaadSparse.Chapter01.theorem_1_11_isUnit`.
* **Theorem 1.12** (reading and generalization). The statement concerns real matrices and allows
  every norm on that space. See `SaadSparse.Chapter01.theorem_1_12_norm` and its Euclidean case
  `SaadSparse.Chapter01.theorem_1_12`.
* **Lemma 1.13** (reading). The declaration uses the upper triangular case. See
  `SaadSparse.Chapter01.lemma_1_13`.
* **Equation (1.33)** (reading). The Rayleigh quotient extends by zero at the zero vector. See
  `SaadSparse.Chapter01.rayleigh`.
* **§1.9.1, the numerical radius** (correction). The disk in the geometric description must be
  centered at zero. See `SaadSparse.Chapter01.numericalRadius`.
* **Equation (1.36)** (reading). The declaration takes the exponent to be a positive integer.
  See `SaadSparse.Chapter01.equation_1_36`.
* **Equations (1.37) and (1.39)** (reading). The variational identities use infima and suprema.
  See `SaadSparse.Chapter01.theorem_1_21`.
* **Theorems 1.19–1.22 and Equations (1.38) and (1.40)** (generalization). The Hermitian
  statements also cover real symmetric matrices. See `SaadSparse.Chapter01.theorem_1_19`,
  `SaadSparse.Chapter01.theorem_1_20`, `SaadSparse.Chapter01.theorem_1_21`,
  `SaadSparse.Chapter01.theorem_1_22`, `SaadSparse.Chapter01.equation_1_38`, and
  `SaadSparse.Chapter01.equation_1_40`.
* **Problem P-1.28** (reading). The declaration gives the norm conclusion of the exercise. See
  `SaadSparse.Chapter01.problem_1_28`.
* **Theorem 1.25** (reading). The existence and simplicity clauses require a positive matrix
  dimension. See `SaadSparse.Chapter01.theorem_1_25` and
  `SaadSparse.Chapter01.theorem_1_25_algSimple`.
* **Proposition 1.26** (generalization). Only the multiplying matrix $C$ needs to be entrywise
  nonnegative. See `SaadSparse.Chapter01.proposition_1_26`.
* **Theorem 1.34, the bound from its proof** (generalization). The lower bound by
  $\lambda_{\min}((A+A^T)/2)$ holds for every real square matrix of positive order. See
  `SaadSparse.Chapter01.theorem_1_34'` and `SaadSparse.Chapter01.isCoerciveWith_lambdaMin`.
* **Equation (1.57)** (generalization). The formula defines a sesquilinear form for every $B$.
  See `Matrix.energyInner` and `Matrix.IsSelfAdjointWrt`.
* **Equation (1.57), inner-product properties** (reading). The individual properties are stated
  for real matrices. See `Matrix.energyInner_comm`, `Matrix.energyInner_add_left`,
  `Matrix.energyInner_smul_left`, and `Matrix.energyInner_self_pos`.
* **Problem P-1.18** (reading and generalization). The self-adjointness results use real
  matrices. For $CB$, symmetry of $B$ suffices. See `Matrix.isSelfAdjointWrt_inv_mul` and
  `Matrix.isSelfAdjointWrt_mul`.
* **Equation (1.66)** (reading). The matrix formula returns zero for a singular cross-Gram
  matrix. See `Matrix.obliqueProj`.
* **§1.12.2, nonsingularity of the cross-Gram matrix** (generalization). The criterion is an
  equivalence. See `SaadSparse.Chapter01.isUnit_conjTranspose_mul_iff`.
* **Equations (1.69)–(1.70)** (generalization). The identities apply to arbitrary square matrices.
  See `SaadSparse.Chapter01.ker_conjTranspose_eq_orthogonal_range` and
  `SaadSparse.Chapter01.ker_eq_orthogonal_range_conjTranspose`.
* **§1.12.4, $\|P\|_2 = 1$ for an orthogonal projector** (reading). The claim needs $P \neq 0$,
  because the zero matrix is the orthogonal projector onto $\{0\}$. The library states
  $\|Px\|_2 \le \|x\|_2$ for every orthogonal projector. See `SaadSparse.Chapter01.norm_apply_le`.
* **§1.12.4, projector eigenvalues and fixed vectors** (generalization). Idempotence suffices
  for both properties. See `SaadSparse.Chapter01.spectrum_subset_pair` and
  `SaadSparse.Chapter01.mem_range_iff_eigen_one`.
* **Corollary 1.39** (reading). The book's $\min_{y \in M}$ is read with $y$ ranging over $M$, so
  $y \in M$ is a hypothesis and the statement is about the least element of the set of distances.
  See `SaadSparse.Chapter01.corollary_1_39`.
* **§1.13.1, Case 2** (generalization). The affine description of the solution set also holds
  for nonsingular matrices. See `Matrix.setOf_mulVec_eq`.
* **Equations (1.74)–(1.75)** (generalization). The direction parameter may be complex. See
  `Matrix.equation_1_75`.
* **Equation (1.76)** (reading). The declaration gives a finite perturbation estimate with an
  explicit stability denominator and nonzero reference norms. See
  `Matrix.relative_error_le_of_perturbed`.
* **Example 1.5** (generalization). The book takes $i$ to be the first index and $j$ the last. The
  statement holds for any $i \neq j$. See `Matrix.example_1_5`.
* **§1.13.2, relative residual bound** (reading). The reference right-hand side is explicitly
  nonzero. See `Matrix.relative_error_le_condNumberLp`.

**Chapter 2.**

* **Equations (2.9)–(2.13)** (reading). The difference estimates use global regularity.
  The first derivative formulas give exact Lagrange remainders. See
  `SaadSparse.Chapter02.equation_2_10`, `SaadSparse.Chapter02.equation_2_12` and
  `SaadSparse.Chapter02.equation_2_13`.
* **Equation (2.16) and Problems P-2.6–P-2.7** (reading). The staggered difference identity is
  unscaled, and the accuracy result gives an exact remainder for globally $C^4$ functions.
  See `SaadSparse.Chapter02.equation_2_16_symm` and `SaadSparse.Chapter02.equation_2_16`.
* **Equation (2.17), Figure 2.4 and Problem P-2.4** (reading). The error formulas evaluate
  the relevant derivatives at intermediate points, under separate regularity hypotheses.
  See `SaadSparse.Chapter02.equation_2_17`, `SaadSparse.Chapter02.ninePointC_error` and
  `SaadSparse.Chapter02.ninePointD_error`.
* **§2.2.2, stencil definitions** (reading). The uniform-grid quotients extend to all real
  step sizes and have value $0$ at step size zero. See `SaadSparse.Chapter02.diffX`,
  `SaadSparse.Chapter02.diffY`, `SaadSparse.Chapter02.diagonalStencil`,
  `SaadSparse.Chapter02.ninePointC` and `SaadSparse.Chapter02.ninePointD`.
* **§2.2.3, grid and stencil** (reading and generalization). The scalar equation has $h^2 f_i$
  on the right, and the matrix display carries $1/h^2$. The surface matrix uses the latter
  convention for any size and step, with zero padding outside the interior.
  See `SaadSparse.Chapter02.dirichletExt`, `SaadSparse.Chapter02.dirichletExt_of_gt`,
  `SaadSparse.Chapter02.laplacian1D`, `SaadSparse.Chapter02.laplacian1D_apply` and
  `SaadSparse.Chapter02.laplacian1D_mulVec_apply`.
* **Equations (13.7)–(13.8), eigenpairs of the 1-D model matrix** (reading). The eigenvalues
  here carry the $1/h^2$ scaling of §2.2.3.
  See `SaadSparse.Chapter02.laplacian1D_mulVec_sineVec`.
* **Equation (2.20)** (reading). The exponential formula is totalized at $R=0$. The
  uniqueness theorem uses nonzero denominators and derivative hypotheses on $[0,1]$.
  See `SaadSparse.Chapter02.convDiffExact` and `SaadSparse.Chapter02.equation_2_20`.
* **Equation (2.21)** (reading). The closed forms are totalized at zero denominators.
  The uniqueness statement on the grid excludes the degenerate roots at $c=0,1$.
  See `SaadSparse.Chapter02.convDiffRatio`, `SaadSparse.Chapter02.convDiffDiscrete` and
  `SaadSparse.Chapter02.equation_2_21`.
* **§2.2.4, positivity, monotonicity and oscillation** (generalization). The continuous and
  discrete formulas have these properties beyond the source's grid interval under the stated
  parameter conditions. See `SaadSparse.Chapter02.convDiffExact_pos`,
  `SaadSparse.Chapter02.convDiffExact_strictMono`, `SaadSparse.Chapter02.equation_2_21_oscillates`
  and `SaadSparse.Chapter02.equation_2_21_strictMono`.
* **§2.2.4, centered and backward upwind matrices** (generalization). The six-point
  displays extend to arbitrary matrix sizes and independent parameters. The sign and
  dominance results use explicit size and parameter ranges.
  See `SaadSparse.Chapter02.convDiffCentered`, `SaadSparse.Chapter02.convDiffCentered_apply`,
  `SaadSparse.Chapter02.convDiffUpwind`, `SaadSparse.Chapter02.convDiffUpwind_apply`,
  `SaadSparse.Chapter02.convDiffCentered_not_isMMatrix`,
  `SaadSparse.Chapter02.convDiffCentered_not_diagDominant` and
  `SaadSparse.Chapter02.convDiffUpwind_diagDominant`.
* **Equation (2.23)** (reading). The two upwind expressions are equal for all steps,
  including zero by totalized division. See `SaadSparse.Chapter02.equation_2_23`.
* **§2.2.5, the interior index ranges** (typo). The source omits the last interior index in
  each direction. The formal grid has $n_1$ by $n_2$ interior points.
  See `SaadSparse.Chapter02.laplacian2D` and `SaadSparse.Chapter02.laplacian2D_apply`.
* **§2.2.5 and Equations (2.26), (13.12), (13.14)** (reading and generalization). The
  scaled matrix formulas use independent step sizes for the two grid directions.
  The block form fixes the first coordinate, giving vertical blocks.
  See `SaadSparse.Chapter02.laplacian2D`, `SaadSparse.Chapter02.laplacian2D_apply`,
  `SaadSparse.Chapter02.laplacian2D_eq_kroneckerSum`, `SaadSparse.Chapter02.laplacian2D_smul`,
  `SaadSparse.Chapter02.laplacian2D_block_apply` and
  `SaadSparse.Chapter02.laplacian2D_mulVec_kroneckerVec`.
* **Equation (2.29)** (typo). The book prints the two indices transposed, which gives systems of the
  wrong size. The library states $p$ systems of size $m$, as line 2 of Algorithm 2.1 says. See
  `SaadSparse.Chapter02.equation_2_29`.
* **Equations (2.33) and (2.36)** (generalization). The cyclic reduction recurrence,
  its polynomial form, and the factorization apply to arbitrary square real matrices.
  See `SaadSparse.Chapter02.cyclicReduction`, `SaadSparse.Chapter02.equation_2_33` and
  `SaadSparse.Chapter02.equation_2_36`.
* **Equation (2.36)** (typo). The product for the block solve uses $B$ in place of the
  printed $A$. See `SaadSparse.Chapter02.equation_2_36`.
* **§2.3, energy form, symmetry and bilinearity** (generalization and reading). The integral is over
  a measured real Hilbert space. The linearity theorem uses classical gradients and assumes
  differentiability and integrability explicitly. See `SaadSparse.Chapter02.energyForm`,
  `SaadSparse.Chapter02.energyForm_symm` and
  `SaadSparse.Chapter02.energyForm_bilinear`.
* **Equation (2.44) and the element stiffness matrix** (generalization). The trial function
  enters the first slot of a possibly nonsymmetric form. The load can be any bounded linear
  functional. See `SaadSparse.Chapter02.stiffnessMatrix`,
  `SaadSparse.Chapter02.stiffnessMatrix_apply`, `SaadSparse.Chapter02.loadVector`,
  `SaadSparse.Chapter02.equation_2_44`,
  `SaadSparse.Chapter02.stiffnessMatrix_mulVec_apply` and
  `SaadSparse.Chapter02.elementMatrix`.
* **§2.3, stiffness matrix identities** (generalization). The symmetry claim allows any
  symmetric form and any family. The quadratic-form identity extends to two coefficient
  vectors. See `SaadSparse.Chapter02.stiffness_isSymm` and
  `SaadSparse.Chapter02.dotProduct_stiffnessMatrix_mulVec`.
* **§2.3, positive definiteness and Neumann singularity** (reading). The algebraic results
  take coercivity and annihilation of the basis sum, respectively, as hypotheses.
  See `SaadSparse.Chapter02.stiffness_posDef` and `SaadSparse.Chapter02.neumann_not_isUnit`.
* **Equations (2.45)–(2.46)** (generalization). Arbitrary element forms satisfy the assembly
  and product formulas under the source's splitting and support properties.
  See `SaadSparse.Chapter02.gramMatrix_eq_sum`, `SaadSparse.Chapter02.equation_2_45` and
  `SaadSparse.Chapter02.equation_2_46`.
* **Example 2.1** (reading). The filled positions in Figure 2.8 indicate where entries can
  be nonzero. See `SaadSparse.Chapter02.example_2_1`.
* **§2.4, preservation of angles** (generalization). The angle identities include degenerate
  vertex triples. See `SaadSparse.Chapter02.medialTriangle_angle_eq` and
  `SaadSparse.Chapter02.cornerTriangle_angle_eq`.
* **Equation (2.53)** (reading). The declaration gives the flux obtained by multiplying the
  edge state by its normal flux coefficient. See `SaadSparse.Chapter02.equation_2_53`.
* **Problem P-2.12** (generalization). The edge-vector sum vanishes for any finite cyclic list
  of vertices. See `SaadSparse.Chapter02.sum_edgeVec_eq_zero`.
* **Equations (2.54)–(2.55)** (generalization). The operator adds the contributions of all edges
  with the same neighbour. See `SaadSparse.Chapter02.equation_2_55_apply_ne`.
* **§2.5, weak diagonal dominance** (generalization). The theorem uses abstract edge vectors
  summing to zero and a neighbour map with no self-neighbours. See
  `SaadSparse.Chapter02.equation_2_55_isDiagDominant`.

**Chapter 3.**

* **§3.2.1, the adjacency graph** (reading). The directed relation includes loops, and the
  simple graph used for symmetry records off-diagonal edges.
  See `SaadSparse.Chapter03.adjDigraph_eq`.
* **§3.2.1 and Problem P-3.4, powers** (correction). A nonzero entry gives a path of the
  prescribed length. Cancellation can make the reverse implication false.
  See `SaadSparse.Chapter03.pattern_pow`.
* **Problem P-3.2, sums** (reading). Pattern containment always holds, and the equality is
  stated for entrywise nonnegative matrices. See `SaadSparse.Chapter03.pattern_add` and
  `SaadSparse.Chapter03.pattern_add_of_nonneg`.
* **Problem P-3.5, products** (correction). The diagonal hypothesis alone permits cancellation.
  The theorem imposes nonnegative entries and positive diagonals.
  See `SaadSparse.Chapter03.problem_3_5`.
* **Proposition 3.2** (reading). The permutation identities use an arbitrary permutation
  matrix directly. The ordered products of interchange matrices are factored out.
  See `SaadSparse.Chapter03.proposition_3_2`.
* **§3.3.2, graph relabelling** (generalization). The graph isomorphism is also stated
  for the loopless symmetrized graph, with invariance of colourability and connectivity.
  See `SaadSparse.Chapter03.adjGraph_submatrix`.
* **Example 3.3, the arrow matrix** (reading). Figure 3.4 prints a pattern and no values, so the
  pattern is the hypothesis and every clause holds for every matrix with it. The fill claims are
  stated for one elimination step and for an exhibited $LU$ factorization with support
  containment, allowing cancellation in an originally nonzero position. See
  `SaadSparse.Chapter03.example_3_3`.
* **§3.3.3, level-set orderings** (generalization). The source leaves the connectedness of the graph
  implicit. The statements hold without it. See `SaadSparse.Chapter03.levelSet_blockTridiagonal`.
* **§3.3.3, the size of an independent set** (generalization). The source states the bound for the
  set that Algorithm 3.4 produces. It holds for every maximal independent set. See
  `SaadSparse.Chapter03.indepSet_card_ge`.
* **Equation (3.3)** (generalization). The block zero entries follow from any independent
  set and any reindexing of it. See `SaadSparse.Chapter03.equation_3_3`.
* **§3.3.3, colour classes and degree bound** (reading). The blocks use the symmetrized
  graph. The colour bound uses off-diagonal row counts under a symmetric pattern.
  See `SaadSparse.Chapter03.multicoloring_blocks`,
  `SaadSparse.Chapter03.exists_multicoloring` and `SaadSparse.Chapter03.greedy_coloring_bounds`.
* **Algorithm 3.6 and Problem P-3.11** (reading). The traversal of the greedy colouring is the order
  of the index set, so it is the identity ordering of a matrix that is already reordered. See
  `SaadSparse.Chapter03.greedy_coloring_bounds`.
* **§3.3.4, irreducibility** (reading). The "connected" adjacency graph of the source is read as
  strongly connected, with directed paths of positive length, and the equivalence with the block
  form needs $n \ge 2$. See `SaadSparse.Chapter03.isPatternIrreducible_iff`.
* **§3.3.4, the Frobenius normal form** (reading). The source says that each block "corresponds to a
  connected component". The blocks are the strongly connected components, listed in an order in
  which every arrow points forward. See `SaadSparse.Chapter03.frobenius_normal_form`.
* **§3.4, compressed sparse rows** (typo). Row pointers replace the coordinate row-index
  array $\mathrm{JR}$. The prose prints $\mathrm{JC}$ for that array.
  See `SaadSparse.Chapter03.csrIA` and `SaadSparse.Chapter03.example_3_7_csr`.
* **Example 3.8** (reading). The diagonal layout assigns a common value to all three
  unused positions, and the decoder ignores them. See `SaadSparse.Chapter03.diag_3_8`
  and `SaadSparse.Chapter03.example_3_8`.

**Chapter 4.**

* **Correction.** Equation (4.3) prints the residual of the completed iterate. The coordinate
  equation of `SaadSparse.Chapter04.jacobiStep_spec` uses the new value in coordinate $i$ and
  the old values elsewhere, as in (4.4).
* **Reading.** The source assumes nonzero diagonal entries. Scalar division totalizes
  `SaadSparse.Chapter04.jacobiStep` at zeros. Matrix inversion totalizes
  `SaadSparse.Chapter04.gsStep`, `SaadSparse.Chapter04.backwardGsStep`,
  `SaadSparse.Chapter04.symmetricGsStep`, `SaadSparse.Chapter04.sorStep`,
  `SaadSparse.Chapter04.backwardSORStep`, `SaadSparse.Chapter04.ssorStep`,
  `SaadSparse.Chapter04.sorStep_one`, `SaadSparse.Chapter04.G_ssor`,
  `SaadSparse.Chapter04.f_ssor` and `SaadSparse.Chapter04.ssorStep_eq_affine`.
* **Reading.** The forward and backward SOR equation specifications
  `SaadSparse.Chapter04.sorStep_spec` and `SaadSparse.Chapter04.backwardSORStep_spec`
  exclude $\omega=0$ even though (4.12) and its backward analogue give the identity sweep there.
  The preconditioners `SaadSparse.Chapter04.M_sor` and `SaadSparse.Chapter04.M_ssor` totalize
  reciprocals at the undefined parameters in (4.26)–(4.27), and SSOR totalizes the inverse of $D$.
* **Reading.** The block sweeps `SaadSparse.Chapter04.blockJacobiStep` and
  `SaadSparse.Chapter04.blockGaussSeidelStep` use disjoint blocks and totalized inverses.
  Jacobi assembles corrections from every block as in (4.17). Line 4 of Algorithm 4.1 literally
  assigns the full iterate anew at each block. The restricted block scope also applies to
  `SaadSparse.Chapter04.equation_4_17`, `SaadSparse.Chapter04.blockJacobiStep_eq`,
  `SaadSparse.Chapter04.blockGaussSeidelStep_eq`,
  `SaadSparse.Chapter04.blockJacobiStep_eq_additiveStep` and
  `SaadSparse.Chapter04.blockGaussSeidelStep_eq_multiplicativeStep`.

* **Reading.** The $p$-norm versions of Corollary 4.2 use the induced vector $p$-norms. See
  `SaadSparse.Chapter04.corollary_4_2_lp`,
  `SaadSparse.Chapter04.complexSpectralRadius_lt_one_of_lpOpNorm_lt_one`.
* **Generalization.** The algebra-norm spectral bound allows non-induced norms on real matrices. See
  `SaadSparse.Chapter04.complexSpectralRadius_le_algebraNorm`.
* **Reading.** The complex eigenvalue bound before Theorem 4.6 is specialized to induced vector
  $p$-norms. See `SaadSparse.Chapter04.norm_le_lpOpNorm_of_mem_spectrum`.
* **Reading.** The convergence-factor theorem expresses attainment by a nonzero initial error using
  a limit superior. See `SaadSparse.Chapter04.exists_specific_eq`.
* **Generalization.** The Richardson step and its affine representation allow signed parameters. See
  `SaadSparse.Chapter04.richardsonStep`, `SaadSparse.Chapter04.richardsonStep_eq_affine`.
* **Generalization.** The splitting and convergence criterion for Richardson use all nonzero signed
  parameters. See `SaadSparse.Chapter04.richardsonStep_eq`,
  `SaadSparse.Chapter04.richardson_tendsto_iff`.
* **Reading.** The Richardson spectral-radius formula assumes symmetry and a signed nonzero
  parameter. See `SaadSparse.Chapter04.example_4_1_spectralRadius`.
* **Reading.** The Richardson convergence interval uses a symmetric matrix and the strict bound from
  the final display. See `SaadSparse.Chapter04.example_4_1_tendsto_iff`.
* **Correction.** The indefinite Richardson result excludes the identity step at zero and assumes
  symmetry. See `SaadSparse.Chapter04.example_4_1_diverges`.
* **Reading.** The Richardson optimum uses symmetry and minimizes on the positive parameter range.
  See `SaadSparse.Chapter04.example_4_1_opt`.
* **Reading.** The row readings of Corollary 4.8 follow the Gershgorin argument. See
  `SaadSparse.Chapter04.corollary_4_8_strict`, `SaadSparse.Chapter04.corollary_4_8_irred`.
* **Reading.** The row readings of Theorem 4.9 follow the proof. See
  `SaadSparse.Chapter04.theorem_4_9_jacobi`, `SaadSparse.Chapter04.theorem_4_9_gs`,
  `SaadSparse.Chapter04.theorem_4_9_jacobi_irred`, `SaadSparse.Chapter04.theorem_4_9_gs_irred`.
* **Reading.** The strict column readings of Theorem 4.9 use the printed definition and make
  diagonal nonsingularity explicit. See `SaadSparse.Chapter04.theorem_4_9_jacobi_col`,
  `SaadSparse.Chapter04.theorem_4_9_gs_col`.
* **Reading.** The spectral reading of Theorem 4.10 encodes convergence for every right-hand side
  and starting vector. See `SaadSparse.Chapter04.theorem_4_10`.
* **Reading.** The converse of Theorem 4.16 also excludes a zero SOR eigenvalue. See
  `SaadSparse.Chapter04.theorem_4_16_mpr`.
* **Reading.** The optimal SOR parameter makes the real Jacobi spectrum, radius bound and nonempty
  size explicit. See `SaadSparse.Chapter04.equation_4_47`.
* **Corollary 4.2** (generalization). The norm can be any submultiplicative norm on the real
  matrix space, including norms outside the induced class of §1.5. See
  `SaadSparse.Chapter04.corollary_4_2`.
* **Definition 4.5** (reading). The book prints all three conditions with column sums, while the
  proofs of Theorems 4.6 and 4.9 use row sums. Both forms are stated, following the backbone's
  `Matrix.IsStrictDiagDominant` (rows) and `Matrix.IsStrictColDiagDominant` (columns). See
  `SaadSparse.Chapter04.definition_4_5_iff`.
* **Theorem 4.10** (reading). The convergence criterion quantifies over the right-hand side as
  well as the starting vector. See `SaadSparse.Chapter04.theorem_4_10_tendsto`.
* **Theorem 4.16** (reading). The book uses the name $M_{SOR}$ for the SOR iteration matrix, while
  (4.26) uses it for the preconditioner. The library gives the two different names. See
  `SaadSparse.Chapter04.theorem_4_16_mp`.
* **Algorithm 4.3 and Equations (4.50)–(4.51)** (reading). The sweep takes the current
  parameter as input, and its inverse formulas are totalized at singular shifts.
  The solve identities require the corresponding shift to be nonsingular.
  See `SaadSparse.Chapter04.adiHalfStep`, `SaadSparse.Chapter04.adiStep`,
  `SaadSparse.Chapter04.adiHalfStep_spec`, `SaadSparse.Chapter04.adiStep_spec`,
  `SaadSparse.Chapter04.G_adi`, `SaadSparse.Chapter04.f_adi` and
  `SaadSparse.Chapter04.equation_4_50`.
* **Equation (4.52) and Problem P-4.5** (generalization). For the splitting, nonzero
  parameters of either sign are allowed when both shifts are nonsingular. The simplification
  of the affine term uses only the horizontal shift's nonsingularity.
  See `SaadSparse.Chapter04.adiSplitting`, `SaadSparse.Chapter04.adiSplitting_m`,
  `SaadSparse.Chapter04.equation_4_52`, `SaadSparse.Chapter04.adiSplitting_iterationOperator`,
  `SaadSparse.Chapter04.f_adi_eq` and `SaadSparse.Chapter04.f_adi_eq_m_inv_mulVec`.
* **Equation (4.49), model split and convergence** (reading). The concrete split uses
  the constant-coefficient negative Laplacean of §2.2.5. The abstract ADI convergence
  theorem applies to any two symmetric positive definite matrices.
  See `SaadSparse.Chapter04.modelH`, `SaadSparse.Chapter04.modelV`,
  `SaadSparse.Chapter04.laplacian2D_eq_modelH_add_modelV` and
  `SaadSparse.Chapter04.adi_model_problem`.

**Chapter 5.**

* **Generalization.** Projection families permit arbitrary column matrices and repeated subspaces.
  See `SaadSparse.Chapter05.ProjFamily`, `SaadSparse.Chapter05.ProjFamily.subspace`.
* **Reading.** The corrector and residual-projector formulas use totalized inverses. See
  `SaadSparse.Chapter05.corrector`, `SaadSparse.Chapter05.P_i`,
  `SaadSparse.Chapter05.P_i_eq_obliqueProj`.
* **Generalization.** The additive update and residual identity use arbitrary families and totalized
  inverses. See `SaadSparse.Chapter05.additiveStep`, `SaadSparse.Chapter05.residual_additiveStep`.
* **Reading.** The multiplicative procedure is one ordered sweep with totalized reduced solves. See
  `SaadSparse.Chapter05.multiplicativeSweep`.
* **Generalization.** The block correction and projection formulas agree for arbitrary column
  matrices. See `SaadSparse.Chapter05.blockCorrection_eq_projStep`.
* **Generalization.** The abstract process identities require nonsingular compressions and allow
  arbitrary bases. See `SaadSparse.Chapter05.additiveStep_eq`,
  `SaadSparse.Chapter05.multiplicativeSweep_eq`.
* **Generalization.** The residual-projector characterization needs invertible compression without
  orthogonal columns. See `SaadSparse.Chapter05.P_i_isProjOnto`.
* **Reading.** The least-squares projector explicitly assumes an invertible Gram matrix. See
  `SaadSparse.Chapter05.leastSquares_P_i_eq_starProjection`.
* **Reading.** One-step exactness is represented by the sum-of-projectors identity. See
  `SaadSparse.Chapter05.sum_P_i_eq_one`.
* **Reading.** The scalar quotient of the one-dimensional projection step is totalized. See
  `SaadSparse.Chapter05.step1`, `SaadSparse.Chapter05.step1_eq`.
* **Generalization.** The steepest-descent step is defined even outside the SPD case. See
  `SaadSparse.Chapter05.sdStep`.
* **Generalization.** The minimal-residual step and its line optimality allow all real matrices. See
  `SaadSparse.Chapter05.mrStep`, `SaadSparse.Chapter05.mrStep_min`.
* **Generalization.** The residual-norm step and its equivalence with the normal-equation step allow
  singular matrices. See `SaadSparse.Chapter05.rnsdStep`,
  `SaadSparse.Chapter05.rnsdStep_eq_sdStep_normal`.
* **Generalization.** The Galerkin property of the steepest-descent step needs positive realness.
  See `SaadSparse.Chapter05.sdStep_isProjectionApprox`.
* **Generalization.** The cross-multiplied Kantorovich inequality also holds at the zero vector. See
  `SaadSparse.Chapter05.lemma_5_8`.
* **Reading.** The convergence results concern indefinitely iterated exact steps, with geometric
  bounds after $k$ steps. See `SaadSparse.Chapter05.theorem_5_9`,
  `SaadSparse.Chapter05.theorem_5_9_tendsto`, `SaadSparse.Chapter05.theorem_5_10`,
  `SaadSparse.Chapter05.theorem_5_10_tendsto`, `SaadSparse.Chapter05.rnsd_norm_residual_le`,
  `SaadSparse.Chapter05.rnsd_tendsto`.
* **Generalization.** The minimal-residual identities use totalized quotients and angles and allow
  arbitrary matrices. See `SaadSparse.Chapter05.equation_5_18`,
  `SaadSparse.Chapter05.norm_residual_mrStep_eq_sin`.
* **Reading.** The squared steepest-descent error identity also includes the exact-solution case.
  See `SaadSparse.Chapter05.energyNorm_sdStep_sq_eq`.
* **Reading.** The angle-based factor uses a supremum without a separate attainment claim. See
  `SaadSparse.Chapter05.sinAngleSup`, `SaadSparse.Chapter05.sin_angle_le_sinAngleSup`,
  `SaadSparse.Chapter05.norm_residual_mrStep_le_sinAngleSup`,
  `SaadSparse.Chapter05.sinAngleSup_lt_one`, `SaadSparse.Chapter05.norm_mrStep_le_sup_sin`.
* **Reading.** The coordinate projection formula is a single Gauss–Seidel correction and is
  totalized at zero diagonal. See `SaadSparse.Chapter05.example_5_1`.
* **Reading.** The three algorithms have exact state-update specifications for a given number of
  iterations. See `SaadSparse.Chapter05.sdAlgStep`, `SaadSparse.Chapter05.mrAlgStep`,
  `SaadSparse.Chapter05.rnsdAlgStep`, `SaadSparse.Chapter05.rnsdAlgStep_alpha`,
  `SaadSparse.Chapter05.sdAlg_spec`, `SaadSparse.Chapter05.mrAlg_spec`,
  `SaadSparse.Chapter05.rnsdAlg_spec`.
* **Generalization.** The Petrov–Galerkin predicate allows trial and test subspaces of unequal
  dimension. See `SaadSparse.Chapter05.IsProjectionApprox`,
  `SaadSparse.Chapter05.isProjectionApprox_iff`.
* **Reading.** The projection prototype is a single update with a totalized inverse. See
  `SaadSparse.Chapter05.projStep`.
* **Reading.** Proposition 5.1 is stated as basis-free existence and uniqueness. See
  `SaadSparse.Chapter05.proposition_5_1_i`, `SaadSparse.Chapter05.proposition_5_1_ii`.
* **Generalization.** The error functional is defined for all matrices, with the norm interpretation
  in the SPD case. See `SaadSparse.Chapter05.E_A`.
* **Reading.** Proposition 5.5 is represented by its algebraic characterization and a separate norm
  bound. See `SaadSparse.Chapter05.proposition_5_5_char`.
* **Reading.** The reduced operator and projector reformulations make the oblique projector’s
  hypotheses explicit. See `SaadSparse.Chapter05.A_m`,
  `SaadSparse.Chapter05.isProjectionApprox_zero_iff_Q`,
  `SaadSparse.Chapter05.isProjectionApprox_zero_iff_A_m`.
* **Reading.** The general statement of Theorem 5.7 gives the residual identity from its proof. See
  `SaadSparse.Chapter05.theorem_5_7`.
* **Reading.** The matrix forms expose the automatic trivial-intersection hypothesis when $L=K$. See
  `SaadSparse.Chapter05.theorem_5_7_matrix_eq`, `SaadSparse.Chapter05.theorem_5_7_matrix`.
* **§5.1.2** (reading). The book states that $W^TAV$ is nonsingular if and only if no vector of $AK$
  is orthogonal to $L$, which fails for $A = 0$. The library states that $u \in K$ and $u \neq 0$
  imply $Au \notin L^\perp$. See `SaadSparse.Chapter05.isUnit_transpose_mul_mul_iff`.
* **Proposition 5.6** (reading). The statement presupposes that $Q_K^L$ exists, that is
  $K \cap L^\perp = \{0\}$. The library adds this hypothesis. See
  `SaadSparse.Chapter05.proposition_5_6`.

**Chapter 6.**

* **Reading.** Ruhe's definition uses raw block powers and can continue through dependent columns.
  See `SaadSparse.Chapter06.ruhe`.
* **Generalization.** The Ruhe band relation includes zero columns produced by raw-sequence
  dependence. See `SaadSparse.Chapter06.ruheCoeff`, `SaadSparse.Chapter06.HbarBlock`,
  `SaadSparse.Chapter06.HBlock`, `SaadSparse.Chapter06.equation_6_130`.
* **Scope.** The block Arnoldi comparison assumes an infinite orthonormal sequence and is vacuous in
  finite dimension. See `SaadSparse.Chapter06.IsBlockArnoldi`,
  `SaadSparse.Chapter06.equation_6_129`, `SaadSparse.Chapter06.ruhe_eq_blockArnoldiMGS`.
* **Generalization.** Ruhe's block Krylov span identity persists through dependent columns. See
  `SaadSparse.Chapter06.span_ruhe_eq_blockKrylov`.
* **Scope.** The initial residual coefficient theorem uses span membership and a single right-hand
  side. See `SaadSparse.Chapter06.exists_initial_residual_coeffs`.
* **Reading.** The residual and FOM formulas use one right-hand side and general initial block
  coefficients. See `SaadSparse.Chapter06.equation_6_136`, `SaadSparse.Chapter06.blockFOM_iff`.
* **Scope.** The block GMRES definitions and coordinate theorem state minimality without a
  uniqueness claim. See `SaadSparse.Chapter06.IsBlockGMRES`, `SaadSparse.Chapter06.blockGMRES_iff`.
* **Scope.** The real hyperbolic and reciprocal closed forms are stated on the positive branch. See
  `SaadSparse.Chapter06.equation_6_110`, `SaadSparse.Chapter06.equation_6_111`.
* **Reading.** The normalized real Chebyshev polynomial is defined before imposing its minimax
  conditions. See `SaadSparse.Chapter06.Chat`.
* **Generalization.** The real Chebyshev minimax statement allows all degrees up to $k$ on a
  nondegenerate interval. See `SaadSparse.Chapter06.theorem_6_25`.
* **Reading.** The ellipse and filled region use a radius parameter and allow arbitrary
  orientations. See `SaadSparse.Chapter06.ellipse`, `SaadSparse.Chapter06.filledEllipse`.
* **Reading.** The normalized complex Chebyshev polynomial has a totalized definition. See
  `SaadSparse.Chapter06.ChatComplex`.
* **Scope.** The circle minimax theorem states attainment without naming the optimizing polynomial.
  See `SaadSparse.Chapter06.lemma_6_26`.
* **Reading.** The ellipse bounds use an infimum and a supplied exterior Joukowski parameter. See
  `SaadSparse.Chapter06.theorem_6_27`.
* **Scope.** The ellipse maximum is stated as a quotient of Chebyshev values. See
  `SaadSparse.Chapter06.ellipse_max_Chat`.
* **Reading.** The spectral quotients and quadratic-form expression have totalized definitions. See
  `SaadSparse.Chapter06.η`, `SaadSparse.Chapter06.κ`, `SaadSparse.Chapter06.anorm`.
* **Generalization.** The CG characterization allows a minimizing polynomial of degree less than
  $m-1$. See `SaadSparse.Chapter06.lemma_6_28`.
* **Reading.** The theorem named for (6.124) gives the preceding unnumbered Chebyshev bound. See
  `SaadSparse.Chapter06.equation_6_124`.
* **Reading.** The theorem named for (6.125) gives the preceding radical identity. See
  `SaadSparse.Chapter06.equation_6_125`.
* **Reading.** The theorem named for (6.126) gives the source equality (6.124). See
  `SaadSparse.Chapter06.equation_6_126`.
* **Reading.** The theorem for (6.127) combines the intervening equalities. See
  `SaadSparse.Chapter06.equation_6_127`.
* **Generalization.** The CG condition-number bound also includes coincident extreme eigenvalues.
  See `SaadSparse.Chapter06.equation_6_128`.
* **Reading.** The GMRES convergence theorem identifies the limit as the supplied solution. See
  `SaadSparse.Chapter06.theorem_6_30`.
* **Reading.** The fixed-length GMRES convergence bounds explicitly require its nonsingular
  triangular solve. See `SaadSparse.Chapter06.lemma_6_31`, `SaadSparse.Chapter06.proposition_6_32`,
  `SaadSparse.Chapter06.corollary_6_33`.
* **Reading.** The GMRES spectral polynomial value is defined by an infimum. See
  `SaadSparse.Chapter06.epsMin`.
* **Generalization.** The band property following (6.108) is stated with the adjoint. See
  `SaadSparse.Chapter06.arnoldiCoeff_eq_zero_of_adjoint_mem`.
* **Generalization.** The IOP and Arnoldi arrays agree under a band condition for the given starting
  vector. See `SaadSparse.Chapter06.iop_eq_arnoldiMGS_of_band`,
  `SaadSparse.Chapter06.iopCoeff_eq_arnoldiCoeff_of_band`, `SaadSparse.Chapter06.VI_eq_V`,
  `SaadSparse.Chapter06.HI_eq_H`.
* **Reading.** The DIOM–FOM comparison makes the projected elimination conditions explicit. See
  `SaadSparse.Chapter06.iomFixed_eq_fomFixed_of_band`,
  `SaadSparse.Chapter06.diom_eq_fomFixed_of_band`, `SaadSparse.Chapter06.proposition_6_22`.
* **Reading.** The least-degree function uses a totalized infimum on nonnormal matrices. See
  `SaadSparse.Chapter06.ν`.
* **Reading.** The CG(s) definition fixes the Euclidean inner product and includes the last basis
  column. See `SaadSparse.Chapter06.IsCGs`.
* **Correction.** The proof of Lemma 6.23 bounds the adjoint polynomial degree directly. See
  `SaadSparse.Chapter06.lemma_6_23`.
* **Scope.** The formalized part of Theorem 6.24 is the Euclidean sufficiency direction. See
  `SaadSparse.Chapter06.isCGs_of_natDegree_minpoly_le`,
  `SaadSparse.Chapter06.isCGs_of_isStarNormal`,
  `SaadSparse.Chapter06.isCGs_of_natDegree_minpoly_le_or_isStarNormal`.
* **Generalization.** The degree-one classification includes its converse for normal matrices. See
  `SaadSparse.Chapter06.nu_le_one_iff`.
* **Generalization.** The minimal-residual proof uses the final span and explicit nonzero images.
  See `SaadSparse.Chapter06.isMinResidualIterate_of_orthogonalDirections`.
* **Generalization.** The closed form is valid without a spanning hypothesis or nonzero
  denominators. See `SaadSparse.Chapter06.equation_6_104`.
* **Reading.** The exact GCR recurrence totalizes division and does not model cached operation
  counts. See `SaadSparse.Chapter06.gcrBody`, `SaadSparse.Chapter06.gcrAux`,
  `SaadSparse.Chapter06.gcrX`, `SaadSparse.Chapter06.gcrR`, `SaadSparse.Chapter06.gcrP`,
  `SaadSparse.Chapter06.gcrAlpha`, `SaadSparse.Chapter06.gcrBeta`,
  `SaadSparse.Chapter06.gcrAlpha_eq`, `SaadSparse.Chapter06.gcrX_succ`,
  `SaadSparse.Chapter06.gcrR_succ`, `SaadSparse.Chapter06.gcrP_succ`.
* **Generalization.** The GCR step formulas extend to complex vectors and totalized division. See
  `SaadSparse.Chapter06.gcrStepAlpha`, `SaadSparse.Chapter06.gcrStepR`,
  `SaadSparse.Chapter06.gcrStepBeta`.
* **Reading.** ORTHODIR combines the source direction recurrence with the GCR state updates. See
  `SaadSparse.Chapter06.orthodirBody`, `SaadSparse.Chapter06.orthodirAux`,
  `SaadSparse.Chapter06.orthodirX`, `SaadSparse.Chapter06.orthodirR`,
  `SaadSparse.Chapter06.orthodirP`, `SaadSparse.Chapter06.orthodirAlpha`,
  `SaadSparse.Chapter06.orthodirBeta`, `SaadSparse.Chapter06.orthodirAlpha_eq`,
  `SaadSparse.Chapter06.orthodirX_succ`, `SaadSparse.Chapter06.orthodirR_succ`,
  `SaadSparse.Chapter06.orthodirP_succ`.
* **Reading.** ORTHOMIN clips the window to the available directions and allows an empty window. See
  `SaadSparse.Chapter06.orthominBody`, `SaadSparse.Chapter06.orthominAux`,
  `SaadSparse.Chapter06.orthominX`, `SaadSparse.Chapter06.orthominR`,
  `SaadSparse.Chapter06.orthominP`.
* **Reading.** Restarted GCR uses fixed cycle lengths and recomputes the initial residual at each
  restart. See `SaadSparse.Chapter06.gcrCycle`, `SaadSparse.Chapter06.gcrRestarted`,
  `SaadSparse.Chapter06.gcrRestarted_succ`.
* **Reading.** The GCR and ORTHODIR basis properties make the no-breakdown and grade conditions
  explicit. See `SaadSparse.Chapter06.inner_apply_gcrP_eq_zero`,
  `SaadSparse.Chapter06.inner_apply_orthodirP_eq_zero`, `SaadSparse.Chapter06.span_gcrP_eq`,
  `SaadSparse.Chapter06.span_orthodirP_eq`.
* **Reading.** The GCR and ORTHODIR minimal-residual specifications apply to prefixes without
  breakdown. See `SaadSparse.Chapter06.gcrX_isMinResidualIterate`,
  `SaadSparse.Chapter06.orthodirX_isMinResidualIterate`.
* **Scope.** The GMRES equivalence is stated for nonsingular systems before breakdown. See
  `SaadSparse.Chapter06.gcrX_eq_gmresFixed`, `SaadSparse.Chapter06.orthodirX_eq_gmresFixed`,
  `SaadSparse.Chapter06.algorithm_6_21_eq_gmres`, `SaadSparse.Chapter06.orthodir_eq_gmres`.
* **Reading.** The CR step and its components are defined on arbitrary matrices and totalize the
  quotients. See `SaadSparse.Chapter06.crStepAlpha`, `SaadSparse.Chapter06.crStepR`,
  `SaadSparse.Chapter06.crStepBeta`, `SaadSparse.Chapter06.crStep`, `SaadSparse.Chapter06.cr`,
  `SaadSparse.Chapter06.crStepAlpha_def`, `SaadSparse.Chapter06.crStepR_def`,
  `SaadSparse.Chapter06.crStepBeta_def`, `SaadSparse.Chapter06.crX`, `SaadSparse.Chapter06.crR`,
  `SaadSparse.Chapter06.crP`, `SaadSparse.Chapter06.crAp`, `SaadSparse.Chapter06.crAlpha`,
  `SaadSparse.Chapter06.crBeta`, `SaadSparse.Chapter06.cr_succ`, `SaadSparse.Chapter06.crAlpha_eq`,
  `SaadSparse.Chapter06.crX_succ`, `SaadSparse.Chapter06.crR_succ`,
  `SaadSparse.Chapter06.crBeta_eq`, `SaadSparse.Chapter06.crP_succ`,
  `SaadSparse.Chapter06.crAp_succ`.
* **Scope.** Unconditional orthogonality of the totalized CR sequence is stated for positive
  definite input. See `SaadSparse.Chapter06.inner_crAp_eq_zero`,
  `SaadSparse.Chapter06.inner_apply_crR_eq_zero`,
  `SaadSparse.Chapter06.algorithm_6_20_orthogonality`.
* **Scope.** The CR minimal-residual property is unconditional under positive definiteness. See
  `SaadSparse.Chapter06.crX_isMinResidualIterate`,
  `SaadSparse.Chapter06.algorithm_6_20_isMinResidualIterate`.
* **Reading.** The conditional CR minimization theorem makes the nonzero denominators explicit. See
  `SaadSparse.Chapter06.crX_isMinResidualIterate_of_no_breakdown`,
  `SaadSparse.Chapter06.algorithm_6_20_isMinResidualIterate_of_no_breakdown`.
* **Scope.** The exact CR–GMRES equality compares fixed-length iterates up to the grade. See
  `SaadSparse.Chapter06.crX_eq_gmresFixed`, `SaadSparse.Chapter06.algorithm_6_20_eq_alg_6_9`.
* **Reading.** The fixed-size Lanczos formulas use the totalized projected inverse. See
  `SaadSparse.Chapter06.lanczosMethodY`, `SaadSparse.Chapter06.lanczosMethodY_def`,
  `SaadSparse.Chapter06.lanczosMethodAt`, `SaadSparse.Chapter06.lanczosMethodAt_def`.
* **Reading.** The Lanczos solve represents its stopping test by the grade and includes a zero
  initial residual. See `SaadSparse.Chapter06.lanczosMethod`,
  `SaadSparse.Chapter06.lanczosMethod_eq_lanczosMethodAt`.
* **Reading.** The Galerkin and residual identities specify the conditions on the projected solve.
  See `SaadSparse.Chapter06.equation_6_87`,
  `SaadSparse.Chapter06.lanczosMethodAt_isGalerkinIterate`.
* **Scope.** The two Lanczos residual formulas and the orthogonality assertion have separate
  hypotheses. See `SaadSparse.Chapter06.proposition_6_20_1`,
  `SaadSparse.Chapter06.inner_residual_lanczosMethodAt_eq_zero`,
  `SaadSparse.Chapter06.residual_dLanczosX`.
* **Reading.** D-Lanczos uses totalized pivots and has no convergence test in its recurrence. See
  `SaadSparse.Chapter06.dlEta`, `SaadSparse.Chapter06.dlLambda`, `SaadSparse.Chapter06.dlZeta`,
  `SaadSparse.Chapter06.dlP`, `SaadSparse.Chapter06.dLanczosX`,
  `SaadSparse.Chapter06.dlLambda_succ`, `SaadSparse.Chapter06.dlEta_succ`,
  `SaadSparse.Chapter06.dlZeta_succ`, `SaadSparse.Chapter06.dlP_zero`,
  `SaadSparse.Chapter06.dlP_succ`, `SaadSparse.Chapter06.dLanczosX_succ`.
* **Scope.** The main CG and Lanczos comparisons explicitly assume SPD and the requisite projection
  conditions. See `SaadSparse.Chapter06.dLanczosX_eq_lanczosMethodAt`,
  `SaadSparse.Chapter06.cgX_eq_dLanczosX`, `SaadSparse.Chapter06.cgX_eq_lanczosMethodAt`.
* **Reading.** The Lanczos and FOM comparison uses the same grade-truncated length. See
  `SaadSparse.Chapter06.lanczosMethod_eq_fom`.
* **Reading.** D-Lanczos conjugacy explicitly assumes that the pivots used by the two directions are
  nonzero. See `SaadSparse.Chapter06.proposition_6_20_2`.
* **Reading.** The CG–Lanczos residual comparison gives a nonzero scale prior to convergence. See
  `SaadSparse.Chapter06.equation_6_99`, `SaadSparse.Chapter06.lanczosV_eq_smul_cgR`.
* **Generalization.** The A-conjugacy quotient for CG beta extends to a converged iterate. See
  `SaadSparse.Chapter06.cgBeta_eq'`.
* **Scope.** The two cases of (6.102) are proved in separate declarations. See
  `SaadSparse.Chapter06.equation_6_102`.
* **Scope.** The (6.103) declaration gives the off-diagonal entries of the displayed matrix. See
  `SaadSparse.Chapter06.equation_6_103`.
* **Generalization.** The exact IOM(2), DIOM(2) and Arnoldi comparisons extend to Hermitian
  matrices. See `SaadSparse.Chapter06.arnoldiCoeff_eq_zero_of_isSymmetric`,
  `SaadSparse.Chapter06.iop_two_eq_arnoldiCGS`, `SaadSparse.Chapter06.iop_two_eq`,
  `SaadSparse.Chapter06.iopVecW_two_eq_arnoldiW`,
  `SaadSparse.Chapter06.iopCoeff_two_eq_arnoldiCoeff`, `SaadSparse.Chapter06.VI_two_eq_V`,
  `SaadSparse.Chapter06.HI_two_eq_H`, `SaadSparse.Chapter06.iomFixed_two_eq_fomFixed`,
  `SaadSparse.Chapter06.diom_two_eq_fomFixed`.
* **Reading.** The direct Lanczos and DIOM(2) comparison states the pivot and grade hypotheses. See
  `SaadSparse.Chapter06.dLanczos_eq_diom2`.
* **Generalization.** The CG recurrence and its components are totalized, with stationary converged
  iterates on SPD input. See `SaadSparse.Chapter06.cgStepAlpha`, `SaadSparse.Chapter06.cgStepR`,
  `SaadSparse.Chapter06.cgStepBeta`, `SaadSparse.Chapter06.cgStep`, `SaadSparse.Chapter06.cg`,
  `SaadSparse.Chapter06.cgStepAlpha_def`, `SaadSparse.Chapter06.cgStepR_def`,
  `SaadSparse.Chapter06.cgStepBeta_def`, `SaadSparse.Chapter06.cgX`, `SaadSparse.Chapter06.cgR`,
  `SaadSparse.Chapter06.cgP`, `SaadSparse.Chapter06.cgAlpha`, `SaadSparse.Chapter06.cgBeta`,
  `SaadSparse.Chapter06.cg_succ`, `SaadSparse.Chapter06.cgAlpha_eq`,
  `SaadSparse.Chapter06.cgX_succ`, `SaadSparse.Chapter06.cgR_succ`,
  `SaadSparse.Chapter06.cgBeta_eq`, `SaadSparse.Chapter06.cgP_succ`.
* **Generalization.** The division-free form of (6.94) also holds at a zero step length. See
  `SaadSparse.Chapter06.cgAlpha_smul_apply_cgP`.
* **Generalization.** The CG residual identity and conjugacy extend to the Hermitian setting. See
  `SaadSparse.Chapter06.cgR_eq_residual`, `SaadSparse.Chapter06.inner_cgR_eq_zero`,
  `SaadSparse.Chapter06.inner_apply_cgP_eq_zero`.
* **Generalization.** The alternative CG step-length and direction identities extend to Hermitian
  systems. See `SaadSparse.Chapter06.inner_cgP_apply_cgP_eq`, `SaadSparse.Chapter06.cgAlpha_eq'`,
  `SaadSparse.Chapter06.apply_cgP_eq`.
* **Reading.** The exact scalar formulas can be read off the ordinary CG sequence. See
  `SaadSparse.Chapter06.cgGamma`, `SaadSparse.Chapter06.cgGamma_def`, `SaadSparse.Chapter06.cgRho`,
  `SaadSparse.Chapter06.cgRho_succ`.
* **Generalization.** The three-term residual recurrence extends to Hermitian positive definite
  systems. See `SaadSparse.Chapter06.equation_6_96`.
* **Correction.** The three-term CG iterate update corrects the sign of the residual term. See
  `SaadSparse.Chapter06.equation_6_98`, `SaadSparse.Chapter06.cg3Step`,
  `SaadSparse.Chapter06.cg3Step_def`.
* **Reading.** The three-term state realizes the first-step coefficient by totalized division. See
  `SaadSparse.Chapter06.CG3State`, `SaadSparse.Chapter06.cg3Init`,
  `SaadSparse.Chapter06.cg3StepRho`.
* **Reading.** The three-term implementation formalizes all steps with totalized quotients and the
  corrected sign. See `SaadSparse.Chapter06.cg3StepGamma`, `SaadSparse.Chapter06.cg3StepGamma_def`,
  `SaadSparse.Chapter06.cg3StepRho_def`, `SaadSparse.Chapter06.cg3`,
  `SaadSparse.Chapter06.cg3_succ`.
* **Reading.** The three-term equivalence uses the corrected update and nonzero preceding residuals.
  See `SaadSparse.Chapter06.cg3_eq`.
* **Generalization.** The three-term scalar is uniquely characterized by the recurrence for
  Hermitian systems. See `SaadSparse.Chapter06.equation_6_97_of_eq_6_96`.
* **Reading.** The Lanczos state, vector and off-diagonal coefficient continue with zeros after
  breakdown. See `SaadSparse.Chapter06.lanczosStep`, `SaadSparse.Chapter06.lanczosStep_eq`,
  `SaadSparse.Chapter06.lanczosState`, `SaadSparse.Chapter06.lanczosState_succ`,
  `SaadSparse.Chapter06.lanczosV`, `SaadSparse.Chapter06.lanczosBeta`.
* **Generalization.** The Lanczos residual and coefficient formulas extend to the complex inner
  product. See `SaadSparse.Chapter06.lanczosStepAlpha`, `SaadSparse.Chapter06.lanczosStepAlpha_eq`,
  `SaadSparse.Chapter06.lanczosStepW`, `SaadSparse.Chapter06.lanczosStepW_eq`.
* **Reading.** The Lanczos diagonal accessor extracts a real coefficient. See
  `SaadSparse.Chapter06.lanczosAlpha`.
* **Generalization.** The Lanczos and Arnoldi comparisons extend to Hermitian matrices and the
  totalized sequences. See `SaadSparse.Chapter06.lanczosV_eq`,
  `SaadSparse.Chapter06.lanczosV_eq_arnoldiMGS`,
  `SaadSparse.Chapter06.lanczosAlpha_eq_arnoldiCoeff`,
  `SaadSparse.Chapter06.lanczosBeta_succ_eq_arnoldiCoeff`.
* **Reading.** The zero-norm test characterizes breakdown and subsequent indices. See
  `SaadSparse.Chapter06.lanczosBeta_succ_eq_zero_iff`.
* **Reading.** The tridiagonal and equivalence theorems quantify over the totalized coefficients.
  See `SaadSparse.Chapter06.theorem_6_19`, `SaadSparse.Chapter06.algorithm_6_15_eq_alg_6_2`.
* **Generalization.** The tridiagonal and Hessenberg arrays agree after mapping real coefficients
  into the field. See `SaadSparse.Chapter06.map_T_eq_H`, `SaadSparse.Chapter06.map_Tbar_eq_Hbar`.
* **Generalization.** The polynomial pairing is defined on all polynomials over the real or complex
  field. See `SaadSparse.Chapter06.polyInner`.
* **Generalization.** Polynomial evaluation is surjective even when the degree bound exceeds the
  grade. See `SaadSparse.Chapter06.polyToKrylov`, `SaadSparse.Chapter06.polyToKrylov_surjective`.
* **Reading.** A Lanczos polynomial is chosen at every index and has the prescribed degree below the
  grade. See `SaadSparse.Chapter06.lanczosPoly`, `SaadSparse.Chapter06.aeval_lanczosPoly`.
* **Scope.** The polynomial pairing theorem states nondegeneracy directly. See
  `SaadSparse.Chapter06.equation_6_85_nondegenerate`.
* **Reading.** The Lanczos polynomial orthogonality includes the totalized post-breakdown vectors.
  See `SaadSparse.Chapter06.equation_6_85_orthogonal_polynomials`.
* **Reading.** Characteristic-polynomial minimization is among monic polynomials of the same degree.
  See `SaadSparse.Chapter06.equation_6_85_charpoly_isMinOn`.
* **Reading.** The characteristic-polynomial vectors equal the Lanczos vectors multiplied by the
  subdiagonal product. See `SaadSparse.Chapter06.equation_6_85_lanczos_charpoly`.
* **Reading.** The residual-smoothing update leaves the state fixed when its direction vanishes. See
  `SaadSparse.Chapter06.smoothEta`, `SaadSparse.Chapter06.smoothEta_eq`, `SaadSparse.Chapter06.mrs`,
  `SaadSparse.Chapter06.mrsX`, `SaadSparse.Chapter06.mrsR`, `SaadSparse.Chapter06.mrsEta`,
  `SaadSparse.Chapter06.mrsX_succ`, `SaadSparse.Chapter06.mrsR_succ`.
* **Reading.** The quasi-minimal smoothing recurrence totalizes reciprocal norms. See
  `SaadSparse.Chapter06.qmrsTau`, `SaadSparse.Chapter06.qmrsEta`, `SaadSparse.Chapter06.qmrs`,
  `SaadSparse.Chapter06.qmrs_succ`.
* **Reading.** The one-step reciprocal identity states the nonzero residual assumptions explicitly.
  See `SaadSparse.Chapter06.equation_6_76`, `SaadSparse.Chapter06.equation_6_77`,
  `SaadSparse.Chapter06.lemma_6_18`.
* **Correction.** The accumulated reciprocal formula uses the summation index in each denominator.
  See `SaadSparse.Chapter06.inv_qmrsTau_sq`, `SaadSparse.Chapter06.qmrsTau_sq`,
  `SaadSparse.Chapter06.inv_sq_norm_mrsR`.
* **Correction.** The weighted MRS and QMRS residual formulas include the initial residual. See
  `SaadSparse.Chapter06.qmrs_eq_6_79`, `SaadSparse.Chapter06.residual_mrs_eq`.
* **Reading.** The weighted update and agreement of the two smoothing procedures state their nonzero
  conditions. See `SaadSparse.Chapter06.qmrs_eq_6_78`, `SaadSparse.Chapter06.equation_6_78`,
  `SaadSparse.Chapter06.norm_mrsR_eq_qmrsTau`, `SaadSparse.Chapter06.mrs_eq_qmrs`.
* **Reading.** The smoothing comparison is with fixed IOM and QGMRES and uses the cosine ratio from
  (6.57). See `SaadSparse.Chapter06.qmrs_iomOfBasis_eq_qgmres`.
* **Reading.** The GMRES equality uses uniqueness and explicit hypotheses for the FOM prefix. See
  `SaadSparse.Chapter06.mrs_isMinResidualIterate`, `SaadSparse.Chapter06.mrs_fom_eq_gmres`.
* **Reading.** The smoothing exercise gives orthogonality for Krylov Galerkin iterates. See
  `SaadSparse.Chapter06.problem_6_26`.
* **Reading.** The residual norms use the fixed-size, totalized iterates. See
  `SaadSparse.Chapter06.ρG`, `SaadSparse.Chapter06.ρF`.
* **Generalization.** The data before the last rotation support complex scalars and totalized
  inversion. See `SaadSparse.Chapter06.Rtilde`, `SaadSparse.Chapter06.gtilde`,
  `SaadSparse.Chapter06.ξ`, `SaadSparse.Chapter06.ytilde`, `SaadSparse.Chapter06.Rtilde_apply`,
  `SaadSparse.Chapter06.gtilde_last`, `SaadSparse.Chapter06.gtilde_castSucc`.
* **Reading.** The best FOM residual includes the initial residual at index zero. See
  `SaadSparse.Chapter06.ρFmin`, `SaadSparse.Chapter06.ρFmin_le`, `SaadSparse.Chapter06.le_ρFmin`.
* **Reading.** The product formula is certified strictly before the grade without assuming
  nonsingularity of the system. See `SaadSparse.Chapter06.ρG_succ`,
  `SaadSparse.Chapter06.equation_6_62`.
* **Reading.** The residual ratio has a complex-modulus version. See
  `SaadSparse.Chapter06.ρF_eq_div_norm_c`, `SaadSparse.Chapter06.equation_6_63`.
* **Reading.** The consecutive-residual identities make the nonzero denominator hypotheses explicit.
  See `SaadSparse.Chapter06.equation_6_65`, `SaadSparse.Chapter06.proposition_6_13`.
* **Reading.** The accumulated reciprocal identities require defined FOM iterates throughout the
  prefix. See `SaadSparse.Chapter06.equation_6_66`, `SaadSparse.Chapter06.corollary_6_14`.
* **Reading.** The FOM–GMRES combination formulas require a nonsingular system and nonzero later
  residual. See `SaadSparse.Chapter06.equation_6_74`, `SaadSparse.Chapter06.equation_6_75`,
  `SaadSparse.Chapter06.problem_6_14`.
* **Reading.** The triangular-coordinate relation makes the reached step and nonsingularity
  explicit. See `SaadSparse.Chapter06.lemma_6_16`.
* **Reading.** QGMRES uses a fixed reduced solve under an abstract Hessenberg relation. See
  `SaadSparse.Chapter06.qgmresY`, `SaadSparse.Chapter06.qgmres`,
  `SaadSparse.Chapter06.qgmresY_isMinOn`, `SaadSparse.Chapter06.qgmres_isQuasiMinResidualIterate`.
* **Generalization.** The QGMRES residual-direction recurrence uses the adjoint in the complex case.
  See `SaadSparse.Chapter06.Z`, `SaadSparse.Chapter06.z`, `SaadSparse.Chapter06.z_eq`,
  `SaadSparse.Chapter06.z_eq_sum`, `SaadSparse.Chapter06.equation_6_53`.
* **Generalization.** The QGMRES and IOM residual identities extend to an abstract real or complex
  Hessenberg relation. See `SaadSparse.Chapter06.equation_6_50`,
  `SaadSparse.Chapter06.equation_6_55`, `SaadSparse.Chapter06.equation_6_56`,
  `SaadSparse.Chapter06.equation_6_58`.
* **Generalization.** The residual-direction norm estimate retains the norm of an arbitrary next
  vector. See `SaadSparse.Chapter06.equation_6_54`.
* **Generalization.** The IOM comparison formulas use an arbitrary basis and make nonsingularity
  explicit for the residual. See `SaadSparse.Chapter06.iomOfBasisY`,
  `SaadSparse.Chapter06.iomOfBasis`, `SaadSparse.Chapter06.residual_iomOfBasis`.
* **Reading.** The quasi-residual and IOM norm comparison explicitly assumes a unit next vector. See
  `SaadSparse.Chapter06.equation_6_57`.
* **Reading.** The quasi-residual estimate uses an explicit base bound and nonzero radii. See
  `SaadSparse.Chapter06.problem_6_25`, `SaadSparse.Chapter06.problem_6_25_le`,
  `SaadSparse.Chapter06.equation_6_51`.
* **Reading.** The QGMRES residual bound uses explicit upper and lower basis constants. See
  `SaadSparse.Chapter06.theorem_6_11`.
* **Reading.** The fixed-length DQGMRES recurrence uses rotated coefficients and totalized division.
  See `SaadSparse.Chapter06.dqgmresP`, `SaadSparse.Chapter06.dqgmresP_eq`,
  `SaadSparse.Chapter06.dqgmres`, `SaadSparse.Chapter06.dqgmres_eq_sum`.
* **Reading.** The certified DQGMRES–QGMRES equivalence requires a full window. See
  `SaadSparse.Chapter06.sum_R_smul_dqgmresP`, `SaadSparse.Chapter06.dqgmres_eq_qgmres`.
* **Reading.** The Givens data extend the rotation formulas to zero radii by totalized division. See
  `SaadSparse.Chapter06.c`, `SaadSparse.Chapter06.s`, `SaadSparse.Chapter06.Ω`,
  `SaadSparse.Chapter06.Qrot`.
* **Reading.** Givens unitarity and norm preservation explicitly require nonzero active radii. See
  `SaadSparse.Chapter06.norm_c_sq_add_norm_s_sq`, `SaadSparse.Chapter06.Ω_mem_unitaryGroup`,
  `SaadSparse.Chapter06.Qrot_mem_unitaryGroup`, `SaadSparse.Chapter06.norm_toLp_Qrot_mulVec`,
  `SaadSparse.Chapter06.equation_6_35`, `SaadSparse.Chapter06.equation_6_38`,
  `SaadSparse.Chapter06.equation_6_80_unitary`.
* **Generalization.** The triangular pattern of the rotated matrix also holds at a degenerate
  rotation. See `SaadSparse.Chapter06.Rbar_eq_zero_of_lt`, `SaadSparse.Chapter06.Rbar_last_row`,
  `SaadSparse.Chapter06.R_isUpperTriangular`, `SaadSparse.Chapter06.R_diag`,
  `SaadSparse.Chapter06.equation_6_39`.
* **Reading.** The rotated least-squares norm identities explicitly require nonzero radii. See
  `SaadSparse.Chapter06.norm_firstVec_sub_mulVec_eq_norm_gbar_sub`,
  `SaadSparse.Chapter06.norm_sq_firstVec_sub_mulVec`, `SaadSparse.Chapter06.equation_6_43`,
  `SaadSparse.Chapter06.sq_J_eq`.
* **Reading.** The triangular least-squares minimizer is certified when its triangular factor is
  nonsingular. See `SaadSparse.Chapter06.isMinOn_lsq`, `SaadSparse.Chapter06.proposition_6_9_2`,
  `SaadSparse.Chapter06.gmresFixed_isGMRESIterate`,
  `SaadSparse.Chapter06.gmresFixed_isMinResidualIterate`, `SaadSparse.Chapter06.lsq_eq_norm_gamma`.
* **Reading.** The complex rotation matrix is defined entrywise, including out-of-range row indices.
  See `SaadSparse.Chapter06.equation_6_80`.
* **Reading.** The evolving last component is real. Earlier entries of the rotated right-hand side
  can be complex. See `SaadSparse.Chapter06.exists_real_gamma_arnoldiCoeff`,
  `SaadSparse.Chapter06.equation_6_81`.
* **Reading.** The objective named $J$ is defined in the projected coordinates. See
  `SaadSparse.Chapter06.J`, `SaadSparse.Chapter06.J_eq`, `SaadSparse.Chapter06.J_eq_lsq`.
* **Generalization.** The Arnoldi residual vector identity includes the padded sequence. See
  `SaadSparse.Chapter06.equation_6_27`, `SaadSparse.Chapter06.residual_eq_6_27`.
* **Reading.** The residual norm equality includes the first breakdown step. See
  `SaadSparse.Chapter06.equation_6_28`, `SaadSparse.Chapter06.residual_eq_6_28`.
* **Reading.** The GMRES specification separates existence and uniqueness of least-squares
  minimizers. See `SaadSparse.Chapter06.IsGMRESIterate`, `SaadSparse.Chapter06.isGMRESIterate_iff`,
  `SaadSparse.Chapter06.gmres_isMinResidualIterate_iff`,
  `SaadSparse.Chapter06.exists_isGMRESIterate`.
* **Reading.** The uniqueness theorem makes matrix nonsingularity and the grade bound explicit. See
  `SaadSparse.Chapter06.existsUnique_isGMRESIterate`, `SaadSparse.Chapter06.gmres_unique`.
* **Reading.** The concrete GMRES algorithm uses a triangular inverse whose singular value is
  totalized. See `SaadSparse.Chapter06.gmresY`, `SaadSparse.Chapter06.gmresFixed`,
  `SaadSparse.Chapter06.gmres`.
* **Reading.** Restarted GMRES takes the cycle count as an input. See
  `SaadSparse.Chapter06.gmresCycle`, `SaadSparse.Chapter06.gmresRestarted`.
* **Reading.** The GMRES residual formulas state the nonsingularity and valid-prefix hypotheses
  explicitly. See `SaadSparse.Chapter06.equation_6_41`, `SaadSparse.Chapter06.equation_6_42`.
* **Generalization.** The reached-step characterization of GMRES breakdown also covers complex
  scalars. See `SaadSparse.Chapter06.proposition_6_10`.
* **Reading.** Householder GMRES uses the signed first reflected entry as its right-hand side. See
  `SaadSparse.Chapter06.βHH`, `SaadSparse.Chapter06.βHH_eq`, `SaadSparse.Chapter06.abs_βHH`,
  `SaadSparse.Chapter06.βHH_smul_hhV_zero`.
* **Reading.** Householder GMRES uses a totalized triangular inverse for the least-squares solve.
  See `SaadSparse.Chapter06.gmresHHY`, `SaadSparse.Chapter06.gmresHH`.
* **Reading.** The Householder GMRES correctness results require the extended basis to fit and the
  reduced factor to be nonsingular. See `SaadSparse.Chapter06.gmresHH_isMinResidualIterate`,
  `SaadSparse.Chapter06.gmresHH_eq`, `SaadSparse.Chapter06.algorithm_6_10`.
* **Reading.** The fixed-size FOM formula returns the starting value if the projected matrix is
  singular. See `SaadSparse.Chapter06.fomY`, `SaadSparse.Chapter06.fomFixed`,
  `SaadSparse.Chapter06.fomFixed_zero`, `SaadSparse.Chapter06.fomFixed_eq_add_sum`.
* **Reading.** FOM uses the exact Gram–Schmidt recurrence, the effective step count and totalized
  inverses. See `SaadSparse.Chapter06.fom`.
* **Generalization.** The FOM Galerkin equations also have complex-scalar formulations. See
  `SaadSparse.Chapter06.H_mulVec_fomY`, `SaadSparse.Chapter06.fomFixed_isGalerkinIterate`,
  `SaadSparse.Chapter06.fom_isGalerkinIterate`,
  `SaadSparse.Chapter06.eq_fomFixed_of_isGalerkinIterate`.
* **Generalization.** The projected initial residual formula includes zero initial residual and a
  complex version. See `SaadSparse.Chapter06.conjTranspose_V_mulVec_r₀`,
  `SaadSparse.Chapter06.Vt_r₀`.
* **Generalization.** FOM's residual formulas generalize to complex scalars. See
  `SaadSparse.Chapter06.residual_fomFixed`, `SaadSparse.Chapter06.norm_residual_fomFixed`.
* **Reading.** The incomplete orthogonalization recurrence is exact, complex-capable and totalized
  at breakdown. See `SaadSparse.Chapter06.iopW`, `SaadSparse.Chapter06.iopCoeffOf`,
  `SaadSparse.Chapter06.iopW_succ`, `SaadSparse.Chapter06.iop`, `SaadSparse.Chapter06.iopVecW`,
  `SaadSparse.Chapter06.iopCoeff`, `SaadSparse.Chapter06.iop_succ`,
  `SaadSparse.Chapter06.iop_succ_eq_zero_iff`, `SaadSparse.Chapter06.norm_iop`.
* **Generalization.** The incomplete Hessenberg relation holds even for the padded recurrence. See
  `SaadSparse.Chapter06.iop_hessenbergRelation`, `SaadSparse.Chapter06.mul_VI_eq`,
  `SaadSparse.Chapter06.iop_eq_6_7`, `SaadSparse.Chapter06.VI`, `SaadSparse.Chapter06.HbarI`,
  `SaadSparse.Chapter06.HI`.
* **Reading.** At the first zero subdiagonal, IOM drops the current step, unlike the rule stated for
  FOM. See `SaadSparse.Chapter06.iomSteps`, `SaadSparse.Chapter06.iomSteps_le`,
  `SaadSparse.Chapter06.iomSteps_eq`, `SaadSparse.Chapter06.iom`,
  `SaadSparse.Chapter06.iom_eq_iomFixed`.
* **Reading.** The fixed-size IOM formulas return zero coefficients for singular projected matrices.
  See `SaadSparse.Chapter06.iomY`, `SaadSparse.Chapter06.iomFixed`,
  `SaadSparse.Chapter06.iomFixed_eq_add_sum`.
* **Generalization.** The fixed-prefix IOM residual formulas have real and complex versions. See
  `SaadSparse.Chapter06.residual_iomFixed`, `SaadSparse.Chapter06.norm_residual_iomFixed`.
* **Reading.** The fixed-size IOM projection interpretation makes the span and unit-vector
  hypotheses explicit. See `SaadSparse.Chapter06.iomFixed_isPetrovGalerkin`.
* **Reading.** The Hessenberg factor recurrences use totalized division and support complex
  coefficients. See `SaadSparse.Chapter06.dioU`, `SaadSparse.Chapter06.dioL`,
  `SaadSparse.Chapter06.dioU_succ`, `SaadSparse.Chapter06.hessL`, `SaadSparse.Chapter06.hessU`,
  `SaadSparse.Chapter06.hessLU`.
* **Reading.** The Hessenberg LU results state the nonzero-pivot conditions explicitly. See
  `SaadSparse.Chapter06.hessL_mul_hessU`, `SaadSparse.Chapter06.isUnit_hessU`,
  `SaadSparse.Chapter06.isUnit_hessenbergSqOf`, `SaadSparse.Chapter06.hessLU_spec`.
* **Generalization.** The DIOM bidiagonal solve allows an arbitrary starting scalar. See
  `SaadSparse.Chapter06.diomZeta`, `SaadSparse.Chapter06.diomZeta_succ`,
  `SaadSparse.Chapter06.hessL_mulVec_diomZeta`.
* **Reading.** The DIOM recurrence continues through the source's zero-pivot stop using a zero
  direction. See `SaadSparse.Chapter06.diomP`, `SaadSparse.Chapter06.diomP_eq`,
  `SaadSparse.Chapter06.diom`, `SaadSparse.Chapter06.diom_succ`,
  `SaadSparse.Chapter06.diom_eq_add_sum`, `SaadSparse.Chapter06.smul_apply_diomP`.
* **Reading.** The auxiliary DIOM solve totalizes the inverse, with correctness under nonzero
  pivots. See `SaadSparse.Chapter06.diomY`, `SaadSparse.Chapter06.hessU_mulVec_diomY`,
  `SaadSparse.Chapter06.HI_mulVec_diomY`, `SaadSparse.Chapter06.diomY_eq_iomY`.
* **Reading.** The DIOM–IOM equivalence is with the fixed-size IOM formula. See
  `SaadSparse.Chapter06.diom_eq_iomFixed`, `SaadSparse.Chapter06.algorithm_6_8_eq_alg_6_7`.
* **Reading.** The DIOM residual statements expose the nonzero pivots and use coefficient moduli.
  See `SaadSparse.Chapter06.diomY_last`, `SaadSparse.Chapter06.norm_residual_diom`,
  `SaadSparse.Chapter06.residual_diom_eq_smul`, `SaadSparse.Chapter06.diom_residual`.
* **Reading.** The local DIOM residual orthogonality includes the initial residual. See
  `SaadSparse.Chapter06.inner_residual_diom_eq_zero`, `SaadSparse.Chapter06.equation_6_22`.
* **Reading.** Local A-orthogonality and semi-conjugacy require a nonzero update scalar. See
  `SaadSparse.Chapter06.inner_iop_apply_diomP_eq_zero`,
  `SaadSparse.Chapter06.inner_diomP_apply_diomP_eq_zero`, `SaadSparse.Chapter06.equation_6_23`,
  `SaadSparse.Chapter06.equation_6_24`.
* **Generalization.** A finite window covering the prefix suffices for agreement with full MGS. See
  `SaadSparse.Chapter06.iop_eq_arnoldiMGS_of_le`, `SaadSparse.Chapter06.algorithm_6_6_eq_alg_6_2`.
* **Reading.** Restarted FOM takes a supplied number of exact cycles. See
  `SaadSparse.Chapter06.fomCycle`, `SaadSparse.Chapter06.fomRestarted`,
  `SaadSparse.Chapter06.fomRestarted_succ`,
  `SaadSparse.Chapter06.fomRestarted_succ_isGalerkinIterate`.
* **Reading.** The Gram–Schmidt Arnoldi definitions pad exact breakdown with zeros and allow complex
  scalars. See `SaadSparse.Chapter06.arnoldiCGS`, `SaadSparse.Chapter06.arnoldiCGS_succ`,
  `SaadSparse.Chapter06.arnoldiMGS`, `SaadSparse.Chapter06.arnoldiMGS_succ`.
* **Reading.** The Arnoldi coefficient and residual formulas use the complex inner product when
  needed. See `SaadSparse.Chapter06.arnoldiCoeff`, `SaadSparse.Chapter06.arnoldiW`,
  `SaadSparse.Chapter06.arnoldiMGSW`, `SaadSparse.Chapter06.arnoldiMGSCoeff`,
  `SaadSparse.Chapter06.mgsW`, `SaadSparse.Chapter06.mgsW_succ`.
* **Reading.** The zero tests on the padded sequence identify indices at or past breakdown. See
  `SaadSparse.Chapter06.arnoldiCGS_eq_zero_iff`,
  `SaadSparse.Chapter06.arnoldiCoeff_succ_self_eq_zero_iff`.
* **Generalization.** The orthogonality and span formulas include complex scalars and describe the
  stabilized span. See `SaadSparse.Chapter06.inner_arnoldiCGS_eq_zero`,
  `SaadSparse.Chapter06.norm_arnoldiCGS`, `SaadSparse.Chapter06.orthonormal_arnoldiCGS`,
  `SaadSparse.Chapter06.span_arnoldiCGS`.
* **Generalization.** The Arnoldi recurrence and matrix relations hold for the totalized real or
  complex sequence. See `SaadSparse.Chapter06.arnoldiCoeff_succ_self`,
  `SaadSparse.Chapter06.arnoldiW_eq_smul`, `SaadSparse.Chapter06.arnoldiCoeff_eq_zero_of_lt`,
  `SaadSparse.Chapter06.hessenbergRelation`, `SaadSparse.Chapter06.apply_arnoldiCGS`,
  `SaadSparse.Chapter06.mul_V_eq`, `SaadSparse.Chapter06.mul_V_eq_add_vecMulVec`.
* **Generalization.** The stopping, grade and invariance conditions are available for both scalar
  fields. See `SaadSparse.Chapter06.NoBreakdownBefore`,
  `SaadSparse.Chapter06.noBreakdownBefore_iff`, `SaadSparse.Chapter06.breakdown_iff_grade_eq`,
  `SaadSparse.Chapter06.krylov_mem_invtSubmodule_of_breakdown`.
* **Reading.** The matrices $V_m$, $H_m$ and the extended Hessenberg matrix also allow padded
  prefixes. See `SaadSparse.Chapter06.V`, `SaadSparse.Chapter06.Hbar`, `SaadSparse.Chapter06.H`.
* **Generalization.** The compression identity holds entrywise even for nonunit starts and after
  breakdown. See `SaadSparse.Chapter06.conjTranspose_V_mul_mul_V`,
  `SaadSparse.Chapter06.equation_6_8`.
* **Generalization.** The real Arnoldi identities include the padded sequence after breakdown. See
  `SaadSparse.Chapter06.equation_6_9`, `SaadSparse.Chapter06.equation_6_7`,
  `SaadSparse.Chapter06.equation_6_6`.
* **Reading.** The exact equivalence of CGS and MGS includes the padded tails. See
  `SaadSparse.Chapter06.arnoldiMGS_eq_arnoldiCGS`,
  `SaadSparse.Chapter06.arnoldiMGSCoeff_eq_arnoldiCoeff`,
  `SaadSparse.Chapter06.algorithm_6_2_eq_alg_6_1`.
* **Reading.** The Householder sign is chosen positive at a zero leading coordinate. See
  `SaadSparse.Chapter06.householderBeta`.
* **Correction.** The Householder direction uses the corrected pivot-coordinate entry. See
  `SaadSparse.Chapter06.householderDir_coord`, `SaadSparse.Chapter06.householderDir_eq`.
* **Reading.** Householder normalization and the reflector identities cover zero tails. See
  `SaadSparse.Chapter06.householderVec`, `SaadSparse.Chapter06.norm_householderVec`,
  `SaadSparse.Chapter06.householder_householder`, `SaadSparse.Chapter06.norm_householder_apply`,
  `SaadSparse.Chapter06.householder_householderVec_apply`,
  `SaadSparse.Chapter06.householder_householderVec_coord`.
* **Generalization.** The elementary Householder map is defined even when its input direction is
  zero. See `SaadSparse.Chapter06.householder`.
* **Reading.** The Householder process uses identity reflectors on zero tails and can complete the
  basis. See `SaadSparse.Chapter06.hhZ`, `SaadSparse.Chapter06.hhW`, `SaadSparse.Chapter06.Qhh`,
  `SaadSparse.Chapter06.QhhT`, `SaadSparse.Chapter06.hhV`, `SaadSparse.Chapter06.hhH`,
  `SaadSparse.Chapter06.hhZ_succ`, `SaadSparse.Chapter06.norm_hhW`.
* **Correction.** The Householder factorization uses $Q_{m+1}$ for all $m+1$ columns. See
  `SaadSparse.Chapter06.equation_6_12_zero`, `SaadSparse.Chapter06.equation_6_12`.
* **Correction.** The Householder matrix relation uses consistent coordinate spaces in the reading
  of P-6.1(d). See `SaadSparse.Chapter06.hh_hessenbergRelation`,
  `SaadSparse.Chapter06.hh_arnoldi_relation`.
* **Reading.** The Householder and Gram–Schmidt basis comparison is restricted to the prefix within
  the grade. See `SaadSparse.Chapter06.span_hhV_eq`,
  `SaadSparse.Chapter06.hh_eq_arnoldi_up_to_sign`.
* **Reading.** Lucky-breakdown exactness explicitly needs the test space to separate trial vectors.
  See `SaadSparse.Chapter06.lucky_breakdown`.
* **Generalization.** The starting residual and its norm allow complex scalars. See
  `SaadSparse.Chapter06.r₀`, `SaadSparse.Chapter06.β`, `SaadSparse.Chapter06.r₀_def`,
  `SaadSparse.Chapter06.β_def`, `SaadSparse.Chapter06.β_eq_norm_r₀`.
* **Reading.** The normalized starting vector is zero at a zero residual. See
  `SaadSparse.Chapter06.v₁`, `SaadSparse.Chapter06.v₁_def`.
* **Generalization.** The projected first-coordinate vector includes dimension zero. See
  `SaadSparse.Chapter06.e₁`.
* **Reading.** The effective number of Arnoldi steps is the grade capped by the requested count. See
  `SaadSparse.Chapter06.mEff`, `SaadSparse.Chapter06.mEff_le`.
* **Generalization.** Grade and Krylov spans also agree for the totalized zero starting vector. See
  `SaadSparse.Chapter06.grade_v₁`, `SaadSparse.Chapter06.krylov_v₁`.
* **Generalization.** The matrix operator in §6.2 is available over real and complex scalars. See
  `SaadSparse.Chapter06.op`.
* **Generalization.** The span in (6.2) includes complex scalars and zero steps. See
  `SaadSparse.Chapter06.krylov`, `SaadSparse.Chapter06.krylov_mono`.
* **Generalization.** The minimal-polynomial and grade statements are available over real and
  complex scalars. See `SaadSparse.Chapter06.grade`, `SaadSparse.Chapter06.minpolyVec`,
  `SaadSparse.Chapter06.monic_natDegree_eq_grade`, `SaadSparse.Chapter06.grade_le_natDegree`,
  `SaadSparse.Chapter06.minpolyVec_monic`, `SaadSparse.Chapter06.natDegree_minpolyVec`,
  `SaadSparse.Chapter06.op_aeval_minpolyVec`, `SaadSparse.Chapter06.grade_le_card`.
* **Generalization.** The polynomial characterization uses strict degree bounds and includes zero
  steps. See `SaadSparse.Chapter06.krylov_eq_map_degreeLT`,
  `SaadSparse.Chapter06.mem_krylov_iff_exists_aeval`, `SaadSparse.Chapter06.aeval_mem_krylov`.
* **Generalization.** The invariance, stabilization and dimension results have real and complex
  formulations. See `SaadSparse.Chapter06.krylov_grade_mem_invtSubmodule`,
  `SaadSparse.Chapter06.krylov_eq_of_grade_le`, `SaadSparse.Chapter06.proposition_6_1`,
  `SaadSparse.Chapter06.finrank_krylov`, `SaadSparse.Chapter06.finrank_krylov_eq_iff`.
* **Generalization.** The section is defined for arbitrary maps onto the subspace, with idempotence
  used in the identities. See `SaadSparse.Chapter06.section'`.
* **Generalization.** The two polynomial compression identities generalize to complex scalars. See
  `SaadSparse.Chapter06.coe_aeval_section'`,
  `SaadSparse.Chapter06.apply_aeval_eq_coe_aeval_section'`.
* **Proposition 6.8** (reading). The library adds two hypotheses that the book leaves implicit:
  $\|v_{m+1}\| = 1$, and $v_1, \dots, v_m$ span $\mathcal{K}_m$. See
  `SaadSparse.Chapter06.proposition_6_8`.
* **Proposition 6.9** (reading). The statement assumes a nonsingular $A$ and replaces the
  printed $m \le n$ with $m \le \operatorname{grade}(v_1)$. It proves the nonsingularity
  consequence of part (1). See `SaadSparse.Chapter06.proposition_6_9`.
* **Proposition 6.10** (reading). The implicit hypothesis that the first $j$ steps are taken is
  explicit: $r_0 \neq 0$ and no breakdown before step $j$. See
  `SaadSparse.Chapter06.proposition_6_10_book`.
* **Proposition 6.17** (reading). The stagnation equivalence assumes a reached prefix, a
  nonzero GMRES residual and nonsingularity of $A$ for both directions. See
  `SaadSparse.Chapter06.proposition_6_17`.
* **Proposition 6.15** (correction). The book prints the upper bound $\sqrt{m}\,\rho^G_m$ in (6.68).
  The bound is $\sqrt{m+1}\,\rho^G_m$ because the minimum includes the initial residual.
  Lean assumes every FOM reduced system is nonsingular, while the source permits skipping
  undefined iterates. See `SaadSparse.Chapter06.proposition_6_15`.
* **Equation (6.79)** (correction). The book prints both sums from $j = 1$. They run from $j = 0$.
  See `SaadSparse.Chapter06.equation_6_79`.
* **Lemma 6.21** (reading). The book asks that $\{p_0, \dots, p_{j-1}\}$ be a basis of
  $\mathcal{K}_j(A, r_0)$ for each $j \le m$. The library asks that $p_0, \dots, p_{m-1}$ span
  $\mathcal{K}_m(A, r_0)$ and that $A p_i \ne 0$. See `SaadSparse.Chapter06.lemma_6_21`.
* **Lemma 6.23** (generalization). The book assumes that $A$ is nonsingular. The proof does not use
  this, and the hypothesis is omitted. See `SaadSparse.Chapter06.lemma_6_23`.
* **Lemma 6.23** (reading). The book leaves $s \ge 1$ implicit. The statement assumes $0 < s$. See
  `SaadSparse.Chapter06.lemma_6_23`.
* **Equation (6.112)** (reading). The book writes the growth estimate as an approximation
  $C_k(t) \gtrsim \frac12 (t + \sqrt{t^2 - 1})^k$. The library states the inequality
  $\frac12 (t + \sqrt{t^2 - 1})^k \le C_k(t)$ for $t \ge 1$. See
  `SaadSparse.Chapter06.equation_6_112`.
* **Theorem 6.25** (reading). The book's "non-empty interval $[\alpha, \beta]$" is read as
  nondegenerate, $\alpha < \beta$, since (6.113) divides by $\beta - \alpha$. See
  `SaadSparse.Chapter06.theorem_6_25`.
* **Theorem 6.29** (reading). The book's $\eta$ is infinite when $\lambda_{\min} = \lambda_{\max}$,
  so the bound (6.123) tacitly assumes $\lambda_{\min} < \lambda_{\max}$. The library makes this
  hypothesis explicit. See `SaadSparse.Chapter06.theorem_6_29`.

**Chapter 7.**

* **Representation.** TFQMR stores the quantities that carry over between half-steps. See
  `SaadSparse.Chapter07.TFQMRState`.
* **Generalization.** TFQMR accepts arbitrary shadows and complex input and initializes an extra
  alpha field. See `SaadSparse.Chapter07.tfqmr`, `SaadSparse.Chapter07.tfqmr_zero`.
* **Totalization.** TFQMR extends the real updates to complex scalars and totalizes their quotients.
  See `SaadSparse.Chapter07.tfqmrStepAlpha`, `SaadSparse.Chapter07.tfqmrStepBeta`,
  `SaadSparse.Chapter07.tfqmr_alpha_even`, `SaadSparse.Chapter07.tfqmr_succ_theta`,
  `SaadSparse.Chapter07.tfqmr_succ_d`, `SaadSparse.Chapter07.tfqmr_succ_rho_odd`,
  `SaadSparse.Chapter07.tfqmr_succ_u_odd`, `SaadSparse.Chapter07.tfqmr_succ_v_odd`.
* **Scope.** TFQMR defines all half-steps independently of a stopping rule. See
  `SaadSparse.Chapter07.tfqmrStep`, `SaadSparse.Chapter07.tfqmr_succ`.
* **Correction.** The TFQMR coefficient array uses the terminal row indices implied by the product
  in (7.81). See `SaadSparse.Chapter07.tfqmrCoeff`, `SaadSparse.Chapter07.tfqmrH`.
* **Correction.** The TFQMR entry lemmas use the corrected zero-based scaling factors in (7.81). See
  `SaadSparse.Chapter07.tfqmrCoeff_self`, `SaadSparse.Chapter07.tfqmrCoeff_succ_self`,
  `SaadSparse.Chapter07.tfqmrH_self`, `SaadSparse.Chapter07.tfqmrH_succ_self`.
* **Scope.** The continuation condition for (7.69) is phrased through the image direction. See
  `SaadSparse.Chapter07.TFQMRNoSeriousBreakdown`.
* **Generalization.** The TFQMR Hessenberg identity permits zero step lengths and zero scales under
  explicit conditions. See `SaadSparse.Chapter07.equation_7_70`.
* **Generalization.** The reduced TFQMR least-squares formulation permits any nonzero finite
  scaling. See `SaadSparse.Chapter07.equation_7_76`.
* **Scope.** The TFQMR equivalences use a nonzero prefix that includes index $m$. See
  `SaadSparse.Chapter07.TFQMRNoBreakdown`.
* **Totalization.** Norm-based scaling is defined for zero residuals, whose normalized columns are
  then zero. See `SaadSparse.Chapter07.tfqmrDelta`.
* **Convention.** The TFQMR residual recurrence identifies tau with the magnitude of the rotated
  residual. See `SaadSparse.Chapter07.norm_gamma_eq_tfqmrTau`.
* **Scope.** The proofs of equivalence with DQGMRES and the projected minimizer assume the nonzero
  prefix. See `SaadSparse.Chapter07.tfqmr_eq_dqgmres`, `SaadSparse.Chapter07.tfqmr_eq_qgmres`,
  `SaadSparse.Chapter07.tfqmr_isQuasiMinResidualIterate`.
* **Scope.** The residual bound (7.83) has explicit finite and global no-breakdown hypotheses. See
  `SaadSparse.Chapter07.equation_7_83`.
* **Generalization.** The BCG residual and direction polynomial recurrences extend to totalized
  complex coefficients. See `SaadSparse.Chapter07.bcgResidualPoly`,
  `SaadSparse.Chapter07.bcgDirectionPoly`, `SaadSparse.Chapter07.bcgResidualPoly_succ`,
  `SaadSparse.Chapter07.bcgDirectionPoly_succ`.
* **Reading.** The BCG polynomial degree bounds allow vanishing leading coefficients. See
  `SaadSparse.Chapter07.bcgResidualPoly_natDegree_le`,
  `SaadSparse.Chapter07.bcgDirectionPoly_natDegree_le`.
* **Generalization.** The BCG leading-term identities are valid even when those coefficients vanish.
  See `SaadSparse.Chapter07.bcgDirectionPoly_coeff_self`,
  `SaadSparse.Chapter07.bcgResidualPoly_coeff_succ`.
* **Generalization.** The dual BCG polynomial formulas use conjugate coefficients with the adjoint.
  See `SaadSparse.Chapter07.bcg_succ`, `SaadSparse.Chapter07.bcg_residual_eq_aeval`,
  `SaadSparse.Chapter07.inner_aeval_conjTranspose_aeval`.
* **Reading.** The CGS recurrence is defined for complex input and all indices with totalized
  quotients. See `SaadSparse.Chapter07.cgsStep`, `SaadSparse.Chapter07.cgs`,
  `SaadSparse.Chapter07.cgs_succ`, `SaadSparse.Chapter07.cgsAlpha`, `SaadSparse.Chapter07.cgsBeta`,
  `SaadSparse.Chapter07.cgsQ`, `SaadSparse.Chapter07.cgs_succ_x`, `SaadSparse.Chapter07.cgs_succ_r`,
  `SaadSparse.Chapter07.cgs_succ_u`, `SaadSparse.Chapter07.cgs_succ_p`.
* **Generalization.** The squared polynomial identity holds for the totalized CGS and BCG
  recurrences. See `SaadSparse.Chapter07.cgs_residual_eq`.
* **Reading.** The BICGSTAB recurrence totalizes the quotients and uses the complex minimum-residual
  coefficient. See `SaadSparse.Chapter07.bicgstabStep`, `SaadSparse.Chapter07.bicgstab`,
  `SaadSparse.Chapter07.bicgstab_succ`, `SaadSparse.Chapter07.bicgstabAlpha`,
  `SaadSparse.Chapter07.bicgstabS`, `SaadSparse.Chapter07.bicgstabOmega`,
  `SaadSparse.Chapter07.bicgstabBeta`.
* **Generalization.** The BICGSTAB update identities include the complex totalized recurrence. See
  `SaadSparse.Chapter07.bicgstab_succ_x`, `SaadSparse.Chapter07.bicgstab_succ_r`,
  `SaadSparse.Chapter07.bicgstab_succ_p`.
* **Reading.** The BICGSTAB comparison makes the leading-coefficient nonvanishing conditions
  explicit. See `SaadSparse.Chapter07.bicgstab_residual_eq`, `SaadSparse.Chapter07.equation_7_53`.
* **Generalization.** The BICGSTAB minimum-residual half-step includes the case of zero matrix
  image. See `SaadSparse.Chapter07.equation_7_55`.
* **Generalization.** The BCG recurrence totalizes the quotients and uses conjugated dual updates.
  See `SaadSparse.Chapter07.bcgStep`, `SaadSparse.Chapter07.bcg`,
  `SaadSparse.Chapter07.bcg_alpha_eq`, `SaadSparse.Chapter07.bcg_beta_eq`,
  `SaadSparse.Chapter07.bcgAlpha`, `SaadSparse.Chapter07.bcgBeta`,
  `SaadSparse.Chapter07.bcgAlpha_eq`, `SaadSparse.Chapter07.bcgBeta_eq`.
* **Reading.** The BCG orthogonality and projection require nonzero divisors on the active prefix.
  See `SaadSparse.Chapter07.BCGNoBreakdown`, `SaadSparse.Chapter07.proposition_7_2`,
  `SaadSparse.Chapter07.bcg_isPetrovGalerkin`.
* **Scope.** The BCG–Lanczos equality compares primal iterates under both no-breakdown conditions.
  See `SaadSparse.Chapter07.bcg_eq_lanczosSolve`.
* **Generalization.** The BCG three-term identities include complex scalars and specify the residual
  division condition. See `SaadSparse.Chapter07.problem_7_7`,
  `SaadSparse.Chapter07.problem_7_7_direction`, `SaadSparse.Chapter07.problem_7_7_start`.
* **Reading.** The exact QMR definition uses a supplied dual starting vector and a projected
  triangular solve. See `SaadSparse.Chapter07.qmrV`, `SaadSparse.Chapter07.qmrCoeff`,
  `SaadSparse.Chapter07.qmr`.
* **Reading.** The QMR minimization specification explicitly assumes an invertible projected factor.
  See `SaadSparse.Chapter07.qmr_isQuasiMinResidualIterate`.
* **Correction.** The residual expansion uses the normalization from the displayed derivation. See
  `SaadSparse.Chapter07.equation_7_16`, `SaadSparse.Chapter07.smul_qmrV_zero`.
* **Reading.** The sine product gives the rotated coordinate before assuming projected solvability.
  See `SaadSparse.Chapter07.equation_7_18`.
* **Reading.** The scalar residual identity uses the Algorithm 7.2 residual. See
  `SaadSparse.Chapter07.equation_7_19`.
* **Scope.** Several QMR norm and smoothing results require an all-index unit-norm hypothesis. See
  `SaadSparse.Chapter07.equation_7_20`, `SaadSparse.Chapter07.equation_7_23`,
  `SaadSparse.Chapter07.equation_7_24`, `SaadSparse.Chapter07.proposition_7_5`,
  `SaadSparse.Chapter07.qmrsTau_eq`, `SaadSparse.Chapter07.qmrsEta_eq`,
  `SaadSparse.Chapter07.qmrSmoothing_eq_qmr`.
* **Generalization.** The QMR residual bound accepts any operator bound, with a specialization to
  vector norms at most one. See `SaadSparse.Chapter07.proposition_7_3`,
  `SaadSparse.Chapter07.proposition_7_3_sqrt`.
* **Reading.** The QMR–GMRES comparison uses supplied basis bounds and explicit projected solve
  hypotheses. See `SaadSparse.Chapter07.theorem_7_4`.
* **Generalization.** QMR residual recovery and its update use complex rotation conventions. See
  `SaadSparse.Chapter07.equation_7_26`, `SaadSparse.Chapter07.equation_7_28`.
* **Generalization.** The exact smoothing identities compare QMR with the tridiagonal-solve
  iterates. See `SaadSparse.Chapter07.equation_7_29`, `SaadSparse.Chapter07.equation_7_30`.
* **Reading.** Residual smoothing returns a pair and uses the algebraically reduced weight. See
  `SaadSparse.Chapter07.qmrSmoothing`, `SaadSparse.Chapter07.qmrsTau_succ`,
  `SaadSparse.Chapter07.qmrsEta_def`.
* **Generalization.** The scaled starting-vector identity includes the zero residual. See
  `SaadSparse.Chapter07.smul_v₁_eq_r₀`.
* **Reading.** The two-sided Lanczos solve is total and returns the initial guess for a singular
  projected matrix. See `SaadSparse.Chapter07.lanczosSolveY`, `SaadSparse.Chapter07.lanczosSolve`,
  `SaadSparse.Chapter07.lanczosSolve_eq_add_sum`.
* **Generalization.** The two-sided Lanczos projection extends to complex systems under the explicit
  solve hypotheses. See `SaadSparse.Chapter07.lanczosSolve_isPetrovGalerkin`.
* **Reading.** The residual identities require the projected solve and the global primal recurrence.
  See `SaadSparse.Chapter07.residual_lanczosSolve`, `SaadSparse.Chapter07.equation_7_9`.
* **Reading.** Exactness at primal lucky breakdown requires a nonsingular projected system. See
  `SaadSparse.Chapter07.lanczosSolve_eq_of_bilanczosVhat_eq_zero`.
* **Generalization.** The two-sided Lanczos matrices use the totalized vector and coefficient
  sequences. See `SaadSparse.Chapter07.bilanczosCoeff`, `SaadSparse.Chapter07.T`,
  `SaadSparse.Chapter07.Tbar`, `SaadSparse.Chapter07.V`, `SaadSparse.Chapter07.W`,
  `SaadSparse.Chapter07.T_apply`, `SaadSparse.Chapter07.Tbar_apply`, `SaadSparse.Chapter07.V_apply`,
  `SaadSparse.Chapter07.W_apply`.
* **Generalization.** Biorthogonality and the span identities extend to complex matrices with the
  adjoint. See `SaadSparse.Chapter07.proposition_7_1`, `SaadSparse.Chapter07.proposition_7_1'`,
  `SaadSparse.Chapter07.proposition_7_1_span`, `SaadSparse.Chapter07.span_bilanczosV_succ`.
* **Scope.** The full-rank declaration certifies an $m$-column prefix after $m$ successful steps.
  See `SaadSparse.Chapter07.problem_7_2`.
* **Reading.** The combined matrix expansion uses a single successful-step hypothesis and two
  adjacent sizes. See `SaadSparse.Chapter07.apply_bilanczosV_sum`,
  `SaadSparse.Chapter07.apply_bilanczosW_sum`, `SaadSparse.Chapter07.equation_7_3`.
* **Reading.** The global primal Hessenberg relation imposes a primal termination hypothesis. See
  `SaadSparse.Chapter07.bilanczos_hessenbergRelation`.
* **Generalization.** The projected matrix result includes both complex adjoint compressions. See
  `SaadSparse.Chapter07.equation_7_5`.
* **Scope.** The exercise declarations give the primal projector and the Lanczos-pair intersection.
  See `SaadSparse.Chapter07.problem_7_6`, `SaadSparse.Chapter07.problem_7_6_inf_eq_bot`.
* **Scope.** The lucky-breakdown results concern termination and invariance on the primal side. See
  `SaadSparse.Chapter07.noSeriousBreakdown_of_bilanczosVhat_eq_zero`,
  `SaadSparse.Chapter07.krylov_mem_invtSubmodule_of_bilanczosVhat_eq_zero`.
* **Generalization.** The Lanczos moment form remains bilinear over the complex field. See
  `SaadSparse.Chapter07.polyForm`, `SaadSparse.Chapter07.momentMatrix`,
  `SaadSparse.Chapter07.polyForm_eq_moment`, `SaadSparse.Chapter07.momentMatrix_apply_eq_of_add_eq`.
* **Reading.** The formal polynomial sequence is total, with degree and orthogonality proved on
  nonbroken prefixes. See `SaadSparse.Chapter07.bilanczosPoly`,
  `SaadSparse.Chapter07.bilanczosVhat_eq_aeval`, `SaadSparse.Chapter07.bilanczosPoly_natDegree`,
  `SaadSparse.Chapter07.polyForm_bilanczosPoly_eq_zero`.
* **Correction.** The dual polynomial evaluation uses the dual initial vector. See
  `SaadSparse.Chapter07.bilanczosWhat_eq_smul`.
* **Correction.** The polynomial criterion detects the zero pairing in both breakdown cases. See
  `SaadSparse.Chapter07.breakdown_iff_polyForm_eq_zero`.
* **Reading.** The unit-norm variant is expressed by rescaled vectors and the entries of its
  projected pencil. See `SaadSparse.Chapter07.bilanczosVUnit`,
  `SaadSparse.Chapter07.bilanczosWUnit`, `SaadSparse.Chapter07.problem_7_3`.
* **Reading.** The dual starting vector is computed by rescaling an arbitrary candidate. See
  `SaadSparse.Chapter07.w₁`, `SaadSparse.Chapter07.inner_w₁_v₁`.
* **Generalization.** The two-sided Lanczos recurrence extends to complex scalars and totalizes
  breakdown. See `SaadSparse.Chapter07.bilanczosStep`, `SaadSparse.Chapter07.bilanczos`,
  `SaadSparse.Chapter07.bilanczosV`, `SaadSparse.Chapter07.bilanczosW`,
  `SaadSparse.Chapter07.bilanczosVPrev`, `SaadSparse.Chapter07.bilanczosWPrev`,
  `SaadSparse.Chapter07.bilanczosBeta`, `SaadSparse.Chapter07.bilanczosDelta`,
  `SaadSparse.Chapter07.bilanczosAlpha`, `SaadSparse.Chapter07.bilanczosVhat`,
  `SaadSparse.Chapter07.bilanczosWhat`, `SaadSparse.Chapter07.bilanczosVPrev_succ`,
  `SaadSparse.Chapter07.bilanczosWPrev_succ`, `SaadSparse.Chapter07.bilanczosDelta_succ`,
  `SaadSparse.Chapter07.bilanczosBeta_succ`, `SaadSparse.Chapter07.bilanczosW_succ`,
  `SaadSparse.Chapter07.bilanczosV_succ`.
* **Generalization.** The normalization coefficients have the same modulus at every index. See
  `SaadSparse.Chapter07.norm_bilanczosBeta_succ`.
* **Generalization.** The normalization product identity also holds at zero in the totalized
  recurrence. See `SaadSparse.Chapter07.equation_7_1`.
* **Generalization.** The admissible normalization rule conjugates the denominator for the complex
  dual vector. See `SaadSparse.Chapter07.inner_smul_smul_eq_one`.
* **Reading.** The alternative normalization preserves the pairing by applying unit norm only on the
  primal side. See `SaadSparse.Chapter07.equation_7_1_norm`.
* **Reading.** The no-breakdown predicate counts completed normalizations after initialization. See
  `SaadSparse.Chapter07.NoBreakdown`.
* **Reading.** The no-serious-breakdown predicate is specific to the primal expansion. See
  `SaadSparse.Chapter07.NoSeriousBreakdown`.
* **Problem P-7.5** (correction). The book says that $t^k p_j$ is orthogonal to
  $p_1, \dots, p_{j-k}$. The range is one polynomial too long, and the library stops at $p_{j-k-1}$.
  The worked example of §7.1.2 has the same error. See `SaadSparse.Chapter07.problem_7_5`.

**Chapter 8.**

* **Generalization.** The saddle block matrix allows any lower-right block and uses the adjoint. See
  `SaadSparse.Chapter08.saddleMatrix`, `SaadSparse.Chapter08.saddleMatrix_mulVec_iff`,
  `SaadSparse.Chapter08.saddleMatrix_apply_blockVec`.
* **Generalization.** The constrained-quadratic results extend to Hermitian matrices and prove
  sufficiency under positive definiteness. See `SaadSparse.Chapter08.saddleObjective`,
  `SaadSparse.Chapter08.isGalerkin_iff_saddleObjective_min`, `SaadSparse.Chapter08.equation_8_30`,
  `SaadSparse.Chapter08.equation_8_30_unique`.
* **Totalization.** Schur expressions and the Uzawa–Richardson identity are total in the leading
  block. See `SaadSparse.Chapter08.schur`, `SaadSparse.Chapter08.schurRhs`,
  `SaadSparse.Chapter08.schur_apply`, `SaadSparse.Chapter08.equation_8_32`,
  `SaadSparse.Chapter08.uzawa_snd_eq_richardson`.
* **Generalization.** Schur elimination and its definiteness and weighted least-squares facts extend
  to complex scalars. See `SaadSparse.Chapter08.schur_eq`, `SaadSparse.Chapter08.schur_posDef`,
  `SaadSparse.Chapter08.equation_8_32_isMinResidual`.
* **Scope.** Uzawa's recurrence is defined at all iteration counts with a totalized inverse. See
  `SaadSparse.Chapter08.uzawaStep`, `SaadSparse.Chapter08.uzawa`, `SaadSparse.Chapter08.uzawa_succ`.
* **Reading.** Uzawa's splitting uses the lower row scaled by the negative relaxation parameter. See
  `SaadSparse.Chapter08.uzawa_eq_splitting`.
* **Generalization.** The Arrow–Hurwicz updates use the adjoint and are defined at every iteration.
  See `SaadSparse.Chapter08.arrowHurwiczStep`, `SaadSparse.Chapter08.arrowHurwicz`,
  `SaadSparse.Chapter08.arrowHurwicz_succ`, `SaadSparse.Chapter08.arrowHurwicz_eq_block`.
* **Generalization.** The regularized Schur formulas use adjoints and a totalized inverse. See
  `SaadSparse.Chapter08.regularizedSchur`, `SaadSparse.Chapter08.regularizedSchur_eq`,
  `SaadSparse.Chapter08.regularizedSchur_apply`, `SaadSparse.Chapter08.re_inner_regularizedSchur`.
* **Correction.** Example 8.2 uses strict thresholds for strict definiteness and assumes full column
  rank. See `SaadSparse.Chapter08.example_8_2`.
* **Scope.** The Uzawa convergence criterion is formalized on the Schur iteration with nonzero
  relaxation. See `SaadSparse.Chapter08.corollary_8_1`.
* **Generalization.** The Lagrangian saddle property extends to complex scalars under positive
  definiteness. See `SaadSparse.Chapter08.lagrangian`, `SaadSparse.Chapter08.lagrangian_isSaddle`.
* **Generalization.** The constraint projector and its range and null space extend to complex
  scalars. See `SaadSparse.Chapter08.constraintProjector`,
  `SaadSparse.Chapter08.problem_8_6_projector`,
  `SaadSparse.Chapter08.constraintProjector_apply_eq_self_iff`,
  `SaadSparse.Chapter08.constraintProjector_apply_eq_zero_iff`.
* **Scope.** The projected equation is equivalent to the block equations on the constraint subspace.
  See `SaadSparse.Chapter08.equation_8_35`.
* **Scope.** The projected CG exercise is covered by the zero-start Krylov containment. See
  `SaadSparse.Chapter08.problem_8_6_cg_subspace`.
* **Scope.** Exercise P-8.5(b) formalizes reconstruction from the Schur solution. See
  `SaadSparse.Chapter08.problem_8_5b`.
* **Generalization.** The saddle indefiniteness witnesses and initial residual use the complex
  Hermitian formulation. See `SaadSparse.Chapter08.problem_8_12_pos`,
  `SaadSparse.Chapter08.problem_8_12_neg`, `SaadSparse.Chapter08.problem_8_12_indefinite`,
  `SaadSparse.Chapter08.inner_saddleMatrix_blockVec_zero`,
  `SaadSparse.Chapter08.problem_8_12_residual`.
* **Totalization.** The stalled steepest-descent step uses totalized division at the undefined
  quotient. See `SaadSparse.Chapter08.problem_8_12_steepestDescent_stalls`,
  `SaadSparse.Chapter08.problem_8_12_minRes_stalls`.
* **Generalization.** The reduced steepest-descent identity uses the positive Schur sign and total
  division. See `SaadSparse.Chapter08.problem_8_12_reduced`.
* **Generalization.** The two normal operators are Hermitian coercive for the corresponding
  injective maps. See `SaadSparse.Chapter08.isSymmetricCoercive_normal`,
  `SaadSparse.Chapter08.isSymmetricCoercive_normal'`.
* **Totalization.** The CGNR and CGNE step coefficients are totalized squared-norm quotients. See
  `SaadSparse.Chapter08.cgnrStepAlpha`, `SaadSparse.Chapter08.cgnrStepBeta`,
  `SaadSparse.Chapter08.cgneStepAlpha`, `SaadSparse.Chapter08.cgneStepBeta`.
* **Generalization.** The CGNR and CGNE states are defined at every index, use the adjoint, and omit
  an explicit convergence test. See `SaadSparse.Chapter08.cgnrStepR`,
  `SaadSparse.Chapter08.cgnrStep`, `SaadSparse.Chapter08.cgnr`, `SaadSparse.Chapter08.cgnr_succ`,
  `SaadSparse.Chapter08.cgnr_zero_p`, `SaadSparse.Chapter08.cgneStepR`,
  `SaadSparse.Chapter08.cgneStep`, `SaadSparse.Chapter08.cgne`, `SaadSparse.Chapter08.cgne_succ`,
  `SaadSparse.Chapter08.cgne_zero_p`.
* **Generalization.** The normal-equation CG identities include singular inputs and use a compatible
  start for CGNE. See `SaadSparse.Chapter08.cgnr_eq`, `SaadSparse.Chapter08.cgne_eq`.
* **Generalization.** The two normal-equation optimality properties and shared Krylov space extend
  to complex scalars. See `SaadSparse.Chapter08.cgnr_isMinResidual`,
  `SaadSparse.Chapter08.cgne_isMinError`, `SaadSparse.Chapter08.subspace_adjoint_eq`.
* **Derivation.** An explicit CGNR residual bound is derived from the normal-equation identity and
  the earlier CG bound. See `SaadSparse.Chapter08.cgnr_norm_residual_le`.
* **Representation.** The SOR sweeps retain only the iterate and use zero corrections for zero
  denominators. See `SaadSparse.Chapter08.neSORStep`, `SaadSparse.Chapter08.neSORSweep`,
  `SaadSparse.Chapter08.nrSORStep`, `SaadSparse.Chapter08.nrSORSweep`.
* **Scope.** Cimmino-NR defines a single update with totalized coordinate corrections. See
  `SaadSparse.Chapter08.cimmino`.
* **Correction.** The normalized Cimmino-NR update uses column norms in the reading of P-8.2. See
  `SaadSparse.Chapter08.cimmino_eq_richardson`.
* **Generalization.** The convergence interval is an equivalence for nonzero Richardson parameters
  under explicit positive spectral endpoints. See `SaadSparse.Chapter08.equation_8_22`.
* **Totalization.** The preconditioned Cimmino identities use an entrywise reciprocal that permits
  zero row or column norms. See `SaadSparse.Chapter08.colNormDiagInv`,
  `SaadSparse.Chapter08.cimmino_eq_richardson_diag`, `SaadSparse.Chapter08.cimminoNE`,
  `SaadSparse.Chapter08.cimminoNE_eq_jacobi`.
* **Generalization.** The block update allows arbitrary basis matrices and uses zero corrections at
  singular block Gram matrices. See `SaadSparse.Chapter08.blockCimmino`,
  `SaadSparse.Chapter08.blockCimmino_eq_additiveStep`,
  `SaadSparse.Chapter08.blockCimmino_isMinResidual`.
* **Scope.** The SOR convergence theorem concerns NR-SOR on the first normal equations. See
  `SaadSparse.Chapter08.sorSweep_tendsto`.
* **Generalization.** The first normal equations use the adjoint, with full column rank required
  only for positive definiteness. See `SaadSparse.Chapter08.equation_8_1`,
  `SaadSparse.Chapter08.isSymmetricCoercive_conjTranspose_mul_self`.
* **Generalization.** Exercise P-8.10 holds for all aspect ratios and identifies the whole minimizer
  set. See `SaadSparse.Chapter08.problem_8_10_residual`, `SaadSparse.Chapter08.problem_8_10`.
* **Generalization.** The second normal equations require solvability of the stated equation in
  place of full row rank. See `SaadSparse.Chapter08.equation_8_3`.
* **Scope.** The augmented-system theorem gives the residual and least-squares equivalence, with the
  multiplier interpretation in prose. See `SaadSparse.Chapter08.equation_8_5`.
* **Generalization.** The squared condition-number identity uses the adjoint and holds for singular
  square matrices with the totalized inverse. See `SaadSparse.Chapter08.equation_8_8`.
* **Equation (8.8)** (generalization). The book states the identity for a nonsingular $A$. It holds
  for every square $A$, because Lean's inverse of a singular matrix is $0$ and both sides vanish.
  See `SaadSparse.Chapter08.equation_8_8`.
* **Problem P-8.2** (typo). The problem writes the normalization $\|A^T e_i\|_2 = 1$ of the rows.
  The hypothesis that makes Cimmino's step Richardson's is the normalization $\|A e_i\|_2 = 1$ of
  the columns, as in Algorithm 8.3. See `SaadSparse.Chapter08.cimmino_eq_richardson`.

**Chapter 9.**

* **Generalization.** The weighted self-adjointness arguments extend to Hermitian data and separate
  the symmetry hypotheses. See `SaadSparse.Chapter09.isPreconditioner`,
  `SaadSparse.Chapter09.isSymmetric_energy`, `SaadSparse.Chapter09.energyInner_leftPreconditioned`,
  `SaadSparse.Chapter09.energyInner_inv`, `SaadSparse.Chapter09.isSymmetric_energyA`,
  `SaadSparse.Chapter09.isSymmetric_energyInv`.
* **Generalization.** The PCG recurrence uses totalized operations and a fixed step count with the
  preconditioned residual derived from the state. See `SaadSparse.Chapter09.pcgStepAlpha`,
  `SaadSparse.Chapter09.pcgStepR`, `SaadSparse.Chapter09.pcgStepBeta`,
  `SaadSparse.Chapter09.pcgStep`, `SaadSparse.Chapter09.pcg`,
  `SaadSparse.Chapter09.pcgStepAlpha_def`, `SaadSparse.Chapter09.pcgStepR_def`,
  `SaadSparse.Chapter09.pcgStepBeta_def`, `SaadSparse.Chapter09.pcgAlpha`,
  `SaadSparse.Chapter09.pcgBeta`, `SaadSparse.Chapter09.pcgAlpha_eq`,
  `SaadSparse.Chapter09.pcgBeta_eq`.
* **Generalization.** The PCG Galerkin characterization uses explicit coercivity relative to the
  preconditioner. See `SaadSparse.Chapter09.pcg_isGalerkinIterate`.
* **Scope.** The PCG error bound uses relative quadratic-form constants and the
  weighted-inner-product proof. See `SaadSparse.Chapter09.problem_9_6`.
* **Generalization.** The split PCG recurrence uses the complex adjoint and totalized operations.
  See `SaadSparse.Chapter09.splitPcgStepAlpha`, `SaadSparse.Chapter09.splitPcgStepR`,
  `SaadSparse.Chapter09.splitPcgStepBeta`, `SaadSparse.Chapter09.splitPcgStep`,
  `SaadSparse.Chapter09.splitPcg`, `SaadSparse.Chapter09.splitPcg_succ`.
* **Generalization.** Split preconditioning compares full states, with invertibility required for
  the ordinary CG coordinate change. See `SaadSparse.Chapter09.splitPcg_eq_pcg`,
  `SaadSparse.Chapter09.splitPcg_eq_cg`.
* **Generalization.** The right-preconditioned recurrence extends to complex data, with symmetry
  sufficient for the state comparison. See `SaadSparse.Chapter09.rightPcgStepAlpha`,
  `SaadSparse.Chapter09.rightPcgStepR`, `SaadSparse.Chapter09.rightPcgStepBeta`,
  `SaadSparse.Chapter09.rightPcgStep`, `SaadSparse.Chapter09.rightPcg`,
  `SaadSparse.Chapter09.rightPcg_succ`, `SaadSparse.Chapter09.rightPcg_eq_pcg`.
* **Representation.** The solution to P-9.2 records the two auxiliary images and states algebraic
  updates. See `SaadSparse.Chapter09.pcgEnergyAStepAlpha`, `SaadSparse.Chapter09.pcgEnergyAStepZ`,
  `SaadSparse.Chapter09.pcgEnergyAStepW`, `SaadSparse.Chapter09.pcgEnergyAStepBeta`,
  `SaadSparse.Chapter09.pcgEnergyAStep`, `SaadSparse.Chapter09.pcgEnergyA`,
  `SaadSparse.Chapter09.pcgEnergyA_succ`.
* **Derivation.** The energy-A recurrence has a transformed-state equivalence and a Galerkin
  characterization. See `SaadSparse.Chapter09.pcgEnergyA_eq`,
  `SaadSparse.Chapter09.pcgEnergyA_isGalerkinIterate`.
* **Generalization.** The preconditioned CR recurrence gives total updates and their energy-space
  interpretation. See `SaadSparse.Chapter09.pcrStepAlpha`, `SaadSparse.Chapter09.pcrStepZ`,
  `SaadSparse.Chapter09.pcrStepBeta`, `SaadSparse.Chapter09.pcrStep`, `SaadSparse.Chapter09.pcr`,
  `SaadSparse.Chapter09.pcr_succ`, `SaadSparse.Chapter09.pcr_eq`,
  `SaadSparse.Chapter09.pcr_residual_eq`.
* **Generalization.** The inverse-sum formula allows a general matrix in place of the diagonal. See
  `SaadSparse.Chapter09.equation_9_8`.
* **Scope.** The Eisenstat product uses the unscaled formula preceding Algorithm 9.3. See
  `SaadSparse.Chapter09.eisenstat`, `SaadSparse.Chapter09.eisenstat_def`,
  `SaadSparse.Chapter09.eisenstat_eq`.
* **Scope.** The split Eisenstat exercise gives the matrix identity and the SSOR simplification. See
  `SaadSparse.Chapter09.problem_9_8c`, `SaadSparse.Chapter09.problem_9_8c_ssor`.
* **Scope.** Example 9.1 formalizes the arithmetic of the stated counts. See
  `SaadSparse.Chapter09.example_9_1`.
* **Generalization.** The energy identities make the preconditioner hypothesis explicit and identify
  the adjoint. See `SaadSparse.Chapter09.isSkewAdjoint_energy`,
  `SaadSparse.Chapter09.energyEnd_eq_one_sub`, `SaadSparse.Chapter09.adjoint_energyEnd`,
  `SaadSparse.Chapter09.isShiftedSkewAdjoint_energyEnd`.
* **Reading.** The tridiagonal identities use the preconditioned operator and the complex
  skew-Hermitian form of the display. See `SaadSparse.Chapter09.equation_9_29`.
* **Generalization.** The CGW coefficient and state recurrences are total and retain the negative
  beta. See `SaadSparse.Chapter09.cgwStep`, `SaadSparse.Chapter09.cgw`,
  `SaadSparse.Chapter09.cgw_succ`, `SaadSparse.Chapter09.cgwAlpha`, `SaadSparse.Chapter09.cgwBeta`,
  `SaadSparse.Chapter09.cgw_alpha`.
* **Scope.** The CGW equivalence and Galerkin result are proved for real input with a valid energy
  preconditioner. See `SaadSparse.Chapter09.cgw_eq_CGW_iterate`,
  `SaadSparse.Chapter09.cgw_isGalerkinIterate`.
* **Generalization.** The two normal operators are Hermitian over the complex field. See
  `SaadSparse.Chapter09.isSymmetric_conjTranspose_mul`,
  `SaadSparse.Chapter09.isSymmetric_mul_conjTranspose`.
* **Generalization.** The normal-equation search spaces and optimality properties are transported by
  the complex adjoint. See `SaadSparse.Chapter09.map_krylov_conjTranspose`,
  `SaadSparse.Chapter09.isGalerkin_adjoint_comp_iff_isMinResidual`,
  `SaadSparse.Chapter09.isMinError_of_isGalerkin_comp_adjoint`.
* **Generalization.** The left-preconditioned normal-equation updates are total recurrences with
  complex adjoints and a fixed count. See `SaadSparse.Chapter09.pcgnrStepAlpha`,
  `SaadSparse.Chapter09.pcgnrStepR`, `SaadSparse.Chapter09.pcgnrStepBeta`,
  `SaadSparse.Chapter09.pcgnrStep`, `SaadSparse.Chapter09.pcgnr`,
  `SaadSparse.Chapter09.pcgneStepAlpha`, `SaadSparse.Chapter09.pcgneStepR`,
  `SaadSparse.Chapter09.pcgneStepBeta`, `SaadSparse.Chapter09.pcgneStep`,
  `SaadSparse.Chapter09.pcgne`.
* **Generalization.** The reductions to PCG need symmetry of the inverse, and the NE comparison
  needs a compatible start. See `SaadSparse.Chapter09.pcgnr_eq`, `SaadSparse.Chapter09.pcgnrX_eq`,
  `SaadSparse.Chapter09.pcgne_eq`, `SaadSparse.Chapter09.pcgneX_eq`.
* **Derivation.** The preconditioned optimality statements use explicit relative coercivity. See
  `SaadSparse.Chapter09.pcgnr_isMinResidual`, `SaadSparse.Chapter09.pcgne_isMinError`.
* **Generalization.** The four exercise variants include state equivalences and extend to complex
  scalars with total inverses. See `SaadSparse.Chapter09.rightPcgnr_eq`,
  `SaadSparse.Chapter09.splitPcgnr_eq`, `SaadSparse.Chapter09.rightPcgne_eq`,
  `SaadSparse.Chapter09.splitPcgne_eq`.
* **Generalization.** The centered operator formulas use adjoints and make the symmetry hypothesis
  explicit. See `SaadSparse.Chapter09.isSymmetric_centredNR`,
  `SaadSparse.Chapter09.isSymmetric_centredNE`, `SaadSparse.Chapter09.op_centredNR_apply`,
  `SaadSparse.Chapter09.op_centredNE_apply`.
* **Representation.** The exercise variants are given as CG on centered operators with separate
  coordinate recovery formulas. See `SaadSparse.Chapter09.centredPcgnr`,
  `SaadSparse.Chapter09.centredPcgne`, `SaadSparse.Chapter09.centredPcgneX`,
  `SaadSparse.Chapter09.centredPcgnr_residual_eq`, `SaadSparse.Chapter09.centredPcgne_eq`.
* **Derivation.** The centered NR operator has a coercivity theorem and a Galerkin characterization
  under explicit hypotheses. See `SaadSparse.Chapter09.isSymmetricCoercive_centredNR`,
  `SaadSparse.Chapter09.centredPcgnr_isGalerkinIterate`.
* **Reading.** The flexible Arnoldi loop uses classical Gram–Schmidt and totalized normalization.
  See `SaadSparse.Chapter09.fgmresV`, `SaadSparse.Chapter09.fgmresW`,
  `SaadSparse.Chapter09.fgmresCoeff`, `SaadSparse.Chapter09.fgmresCoeff_of_le`.
* **Scope.** Flexible directions are supplied through a family of matrix preconditioners. See
  `SaadSparse.Chapter09.fgmresZ`.
* **Generalization.** The flexible basis recurrence is defined for any initial vector and uses
  totalized normalization. See `SaadSparse.Chapter09.fgmresV_zero`,
  `SaadSparse.Chapter09.fgmresV_succ`.
* **Generalization.** The flexible Arnoldi relation holds for the padded recurrence, including
  breakdown. See `SaadSparse.Chapter09.equation_9_22`.
* **Scope.** The flexible GMRES update uses a totalized Givens solve for one cycle. See
  `SaadSparse.Chapter09.fgmresY`, `SaadSparse.Chapter09.fgmres`.
* **Generalization.** The flexible residual factorization includes zero initial residual. See
  `SaadSparse.Chapter09.residual_eq_smul_fgmresV`.
* **Scope.** Proposition 9.2 uses the nonzero prefix and an invertible triangular factor. See
  `SaadSparse.Chapter09.proposition_9_2`.
* **Scope.** The formalized Proposition 9.3 excludes the final breakdown that the printed
  equivalence allows. See `SaadSparse.Chapter09.proposition_9_3`.
* **Scope.** The exact-inner-solve theorem includes invertibility of the chosen triangular factor.
  See `SaadSparse.Chapter09.fgmres_eq_of_apply_fgmresZ_eq`.
* **Scope.** Constant-preconditioner agreement is stated for a nonzero initial residual and
  invertible preconditioner. See `SaadSparse.Chapter09.fgmres_eq_gmresRight`.
* **Scope.** Flexible DQGMRES formalizes the update for supplied basis data and recovers standard
  DQGMRES at identity preconditioning. See `SaadSparse.Chapter09.fdqgmres`,
  `SaadSparse.Chapter09.fdqgmres_eq_dqgmres`.
* **Scope.** The GMRES definitions implement one fixed-length cycle, with total inversion and
  complex scalars. See `SaadSparse.Chapter09.gmresLeft`, `SaadSparse.Chapter09.gmresRight`,
  `SaadSparse.Chapter09.gmresRight_eq`.
* **Scope.** The two GMRES optimality theorems require an invertible preconditioned operator and a
  prefix up to the grade. See `SaadSparse.Chapter09.gmresLeft_isMinResidual`,
  `SaadSparse.Chapter09.gmresRight_isMinResidual`.
* **Generalization.** The polynomial intertwining equation adds the Krylov space identity and does
  not require invertibility. See `SaadSparse.Chapter09.equation_9_18`.
* **Scope.** Proposition 9.1's polynomial representation is separated from optimality and uses the
  factors as printed in the proposition. See `SaadSparse.Chapter09.proposition_9_1`.
* **Scope.** The energy-GMRES declarations give the optimality specification for P-9.13. See
  `SaadSparse.Chapter09.IsGMRESEnergyIterate`, `SaadSparse.Chapter09.isGMRESEnergyIterate_iff`.
* **Generalization.** The energy-product identities are stated for arbitrary vectors and with
  complex conjugation conventions. See `SaadSparse.Chapter09.equation_9_12`.
* **Totalization.** The preconditioned matrices use total inverses; system equivalence uses
  invertible factors. See `SaadSparse.Chapter09.leftPreconditioned`,
  `SaadSparse.Chapter09.rightPreconditioned`, `SaadSparse.Chapter09.splitPreconditioned`.
* **Scope.** A single theorem compares all three systems under a common invertible factorization.
  See `SaadSparse.Chapter09.solution_iff`.
* **Generalization.** The preconditioning spectral comparison includes explicit similarities and
  characteristic polynomials. See `SaadSparse.Chapter09.problem_9_1`,
  `SaadSparse.Chapter09.problem_9_1_charpoly`, `SaadSparse.Chapter09.problem_9_1_spectrum`.

**Chapter 10.**

* **Totalization.** Natural-index row selection returns zero outside the matrix. See
  `SaadSparse.Chapter10.rowVec`.
* **Scope.** The incomplete Gram–Schmidt recurrence drops entries only from $L$, uses complex inner
  products and totalizes normalization. See `SaadSparse.Chapter10.imgsHat`,
  `SaadSparse.Chapter10.imgsQ`, `SaadSparse.Chapter10.imgsL`, `SaadSparse.Chapter10.imgsLMat`,
  `SaadSparse.Chapter10.imgsQMat`, `SaadSparse.Chapter10.imgsL_of_gt`,
  `SaadSparse.Chapter10.imgsL_of_not_drop`, `SaadSparse.Chapter10.imgsHat_eq`,
  `SaadSparse.Chapter10.imgsL_diag_smul_imgsQ`.
* **Correction.** The row identity sums through its row index, with no residual from dropping $Q$
  entries. See `SaadSparse.Chapter10.rowVec_eq_sum`.
* **Correction.** The incomplete LQ factor has positive diagonal entries, as established in the
  printed proof. See `SaadSparse.Chapter10.proposition_10_17`.
* **Correction.** The incomplete Cholesky comparison requires a symmetric drop pattern with a
  retained diagonal. See `SaadSparse.Chapter10.IsICPattern`.
* **Reading.** The incomplete Cholesky condition is proved for the classical recurrence with the
  corrected symmetric pattern. See `SaadSparse.Chapter10.theorem_10_18`.
* **Representation.** The gradient matrix of Proposition 10.9 represents the Fréchet derivative
  through the Frobenius inner product. See `SaadSparse.Chapter10.proposition_10_9`.
* **Scope.** Nonsingularity is shown in Frobenius norm without assuming $A$ nonsingular, and scales
  may be arbitrary invertible matrices. See `SaadSparse.Chapter10.proposition_10_10`,
  `SaadSparse.Chapter10.equation_10_54`.
* **Generalization.** The equimodular support criterion permits any common bound on the column
  residual norms. See `SaadSparse.Chapter10.corollary_10_12`.
* **Scope.** The declaration named for Proposition 10.13 gives the preceding one-step identity,
  using total division. See `SaadSparse.Chapter10.proposition_10_13`.
* **Scope.** The global MR estimate uses an explicit minimizing-step hypothesis. See
  `SaadSparse.Chapter10.proposition_10_14`.
* **Generalization.** The positive pivot result is stated as positivity of the diagonal for an
  arbitrary invertible congruence. See `SaadSparse.Chapter10.lemma_10_15`.
* **Generalization.** The elimination factorization uses arbitrary pivot positions and totalized
  division. See `SaadSparse.Chapter10.equation_10_10`.
* **Generalization.** Ky Fan's theorem and its Schur-complement consequence are stated at any pivot.
  See `SaadSparse.Chapter10.theorem_10_1`, `SaadSparse.Chapter10.theorem_10_1_schur`.
* **Scope.** The factorization existence theorem makes the nonzero pivots explicit and leaves the
  producing algorithm outside its conclusion. See `SaadSparse.Chapter10.theorem_10_2`,
  `SaadSparse.Chapter10.theorem_10_2_ilu0`.
* **Correction.** The level of fill uses the shortest fill-path length, with symmetric sparsity
  pattern. See `SaadSparse.Chapter10.theorem_10_7`.
* **Reading.** The fill-path equivalence is for structural fill in a symmetric sparsity pattern. See
  `SaadSparse.Chapter10.theorem_10_6`.
* **Generalization.** The static-pattern loop comparison omits the common initial zeroing and
  permits totalized pivots. See `SaadSparse.Chapter10.iluRowOp`, `SaadSparse.Chapter10.rowOps`,
  `SaadSparse.Chapter10.ikjSweep`, `SaadSparse.Chapter10.kijSweep`,
  `SaadSparse.Chapter10.ikjSweep_succ_apply`, `SaadSparse.Chapter10.kijSweep_succ_apply`,
  `SaadSparse.Chapter10.ikjSweep_row`, `SaadSparse.Chapter10.kijSweep_row`,
  `SaadSparse.Chapter10.proposition_10_3`.
* **Reading.** The ILUT row invariants use an abstract recurrence with explicit pivot, sign and drop
  hypotheses. See `SaadSparse.Chapter10.theorem_10_8`.
* **Totalization.** The SGS matrix and lower factor are totalized; their intended factor properties
  use a nonsingular diagonal. See `SaadSparse.Chapter10.M_sgs`, `SaadSparse.Chapter10.L_sgs`.
* **Theorem 10.1** (generalization). The book states the first elimination step. The library states
  every pivot step. See `SaadSparse.Chapter10.theorem_10_1`.
* **Theorem 10.2** (reading). "Algorithm 10.1 does not break down" is read as the existence of the
  factors together with $u_{ii} \neq 0$ for all $i$. See `SaadSparse.Chapter10.theorem_10_2`.
* **Proposition 10.3** (generalization). Line 1 of both algorithms, which sets $a_{ij} = 0$ for
  $(i, j) \in P$, is omitted, so the statement holds for every starting matrix. See
  `SaadSparse.Chapter10.proposition_10_3`.
* **Lemma 10.15** (reading). The pivot $\delta_{k+1}$ of (10.70) is read as the diagonal entry of
  $L A L^T$, and the positivity is proved for every nonsingular $L$. See
  `SaadSparse.Chapter10.lemma_10_15`.


**Chapter 12.**

* **§12.2, overlapping blocks** (generalization). The coordinate sets are arbitrary finite
  subsets. The source constructs overlapping intervals. `SaadSparse.Chapter12.blockJacobiStep`
  uses scalar weights over the real or complex field. Its Galerkin and residual theorems take
  $A$ positive definite to ensure well-posed local solves.
* **(12.1)** (source location). `SaadSparse.Chapter12.equation_12_1` states the unnumbered
  weighted residual identity at the end of §12.2. The printed number labels the local unweighted
  correction, whose zero-extended version is `SaadSparse.Chapter12.pairStep_eq`.

* **(12.3)** (scope). `SaadSparse.Chapter12.equation_12_3` states the finite geometric
  identity in the display after the approximate-inverse formula. It requires $\omega\ne0$ and
  uses the total inverse of $D$. `SaadSparse.Chapter12.neumann_isSymmetric_withEnergy` uses any
  real polynomial and any positive definite $D$.
* **(12.4) and (12.5)** (scope). `SaadSparse.Chapter12.equation_12_4` gives a lower bound for
  the interval objective of (12.5) on a positive nondegenerate interval. Printed (12.4) uses the
  discrete spectrum. `SaadSparse.Chapter12.equation_12_5` bounds the operator error by the
  interval objective.
* **(12.6), (12.7), (12.9) and Algorithm 12.1** (source location and reading).
  `SaadSparse.Chapter12.equation_12_6` gives the recurrence printed as (12.7), and
  `SaadSparse.Chapter12.equation_12_7` gives the unnumbered $\sigma_k$ recurrence.
  `SaadSparse.Chapter12.equation_12_9` gives the direction recurrence in Algorithm 12.1. The
  printed (12.9) is the preceding scalar difference quotient.
  `SaadSparse.Chapter12.chebyshevIterate` takes a fixed step count and starts with the
  algorithm's $\rho_0=1/\sigma_1$.
* **§12.3.2** (extensions). `SaadSparse.Chapter12.norm_chebyshev_residual_le` makes the
  residual rate explicit using the Chebyshev interval bound, and
  `SaadSparse.Chapter12.norm_residual_minRes_le_chebyshev` compares it to Krylov minimal
  residuals.
* **(12.10)–(12.14)** (generalizations). `SaadSparse.Chapter12.bilinFormOfWeight` admits
  arbitrary integrable weights. The kernel optimality and orthogonality theorems use an abstract
  bilinear form with explicit hypotheses. `SaadSparse.Chapter12.equation_12_13` gives the
  polynomial identity $R_k=1-Xs_{k-1}$ and implements the quotient with `Polynomial.divX`, so
  evaluation at zero is defined.
* **(12.16)** (scope). `SaadSparse.Chapter12.equation_12_16` is the finite coefficient formula
  for all real parameters. The assertion that it minimizes the weighted norm for the Jacobi
  weight remains outside the statement.

* **§12.4.1 and (12.18)** (generalization).
  `SaadSparse.Chapter12.isDiag_submatrix_of_coloring` proves the diagonal property over any
  entry type with zero. `SaadSparse.Chapter12.equation_12_18` allows any commutative ring and
  invertible $D_1$, removes the diagonal block hypotheses, and gives an equivalence with the
  reduced and back-substitution equations.

* **(12.24) and (12.25)** (scope and generalization).
  `SaadSparse.Chapter12.diag_diagonalScaled` uses the positive diagonal of $A$ and proves unit
  diagonal for that choice of $D$. `SaadSparse.Chapter12.equation_12_25` takes already scaled
  positive semidefinite summands and a positive definite unit-diagonal sum, which gives the
  Winget conclusion without finite-element connectivity data.

**Chapter 13.**

* **§13.2, grid values after (13.14)** (reading).
  `SaadSparse.Chapter13.kroneckerVec_sineVec_eq_sin_grid` uses normalized coordinates. On the
  earlier rectangle with side lengths $l_1,l_2$, the physical coordinates must be divided by the
  respective side lengths.
* **(13.15)–(13.16)** (convention and generalization).
  `SaadSparse.Chapter13.richardson_reduction` uses the iterate minus the solution and allows any
  $\gamma$, with total division. The source uses the solution minus the iterate and chooses a
  positive spectral upper bound.
* **(13.19)–(13.22)** (scope). The weighted Jacobi eigenpair statements use a splitting with
  nonzero weight. `SaadSparse.Chapter13.equation_13_22` gives an absolute-value bound for
  $0<\omega\le1$ where the printed display states signed endpoint bounds.
* **Text before (13.23)** (correction). The sine-square estimate uses $\theta_k/2$, as in
  `SaadSparse.Chapter13.sin_sq_theta_div_two_ge_half` and the factor in (13.21). The printed
  prose omits the half angle.
* **Smoothing factors in §13.2.2** (scope). The theorem at weight $2/3$ in one dimension and the
  theorem at weight $4/5$ in two dimensions give the stated bounds at those weights. The
  optimality comparisons across weights are omitted.
* **(13.25)** (scope). `SaadSparse.Chapter13.weightedJacobi2D_eigenvalue_mem_Ioc` assumes an
  oscillatory mode in at least one coordinate and proves the simple interval bounds. The source
  also gives a sharper finite-grid lower bound.
* **§13.2.3, Gauss–Seidel spectrum** (correction and scope).
  `SaadSparse.Chapter13.gaussSeidel_eigenvalues` asserts membership of the cosine-square values.
  The list misses zero for even positive $n$, which
  `SaadSparse.Chapter13.gaussSeidel1D_mulVec_single` supplies. In the corrected eigenvector
  formula the vectors from paired modes $k$ and $n+1-k$ differ only by a sign, so the family
  cannot furnish the basis suggested by the text.
* **Equation (13.23)** (generalization). The book prints the upper bound $1 - \omega/2$ for the
  oscillatory weighted Jacobi eigenvalues in one dimension; the sharp bound $1 - \omega$ is proved.
  See `SaadSparse.Chapter13.weightedJacobi_eigenvalue_mem_Ioc`.
* **Smoothing factor at $\omega = 1/2$, Section 13.2.2** (generalization). The book gives $3/4$ in
  one dimension; the sharp value $1/2$ is proved. See
  `SaadSparse.Chapter13.smoothingFactor_one_half`.
* **The sentence after (13.25)** (typo). The book says that $\omega = 3/5$ gives the smoothing
  factor $4/5$; the two numbers are transposed, and $\omega = 4/5$ gives $3/5$. See
  `SaadSparse.Chapter13.smoothingFactor2D_four_fifths`.
* **Equation (13.29)** (correction). The book prints $|\cos\theta_k|^j$; the eigenvector has the
  signed power $(\cos\theta_k)^j$. See `SaadSparse.Chapter13.gaussSeidelVec`.

* **(13.30) and (13.32)** (domain). The operators act on interior grid values, with zero
  boundary values for interpolation. The preceding nodal description also includes boundary
  values. The original matrix in (13.30) ends in a row with coefficient $1/2$, matching
  `SaadSparse.Chapter13.prolongation1D`.
* **Example 13.1** (generalization). `SaadSparse.Chapter13.equation_13_31` acts on tensor
  products of arbitrary coordinate vectors. The example uses basis-vector pairs.
* **(13.35)–(13.37)** (generalization). `SaadSparse.Chapter13.coarseProjection_eq_of_scaled` and
  `SaadSparse.Chapter13.coarseProjection_apply_eq_of_smul` use any nonzero scalar over the real
  or complex field. The source's weights are positive real scalars.

* **§13.4.1, after (13.42)** (convention). `SaadSparse.Chapter13.smootherStep_iterate_sub`
  defines the error using the iterate minus the exact solution, reversing the sign convention in
  (13.16). The residual convention is unchanged.
* **(13.43) and Lemma 13.1** (scope and hypotheses). `SaadSparse.Chapter13.equation_13_43`
  defines the full error composition in the preceding display. Printed (13.43) defines the
  coarse correction alone. The inverse in the definitions is total. The projector and
  orthogonality statements assume positive definiteness, injective prolongation and positive-
  scaled transpose restriction.
* **Algorithms 13.3–13.5** (representation). `SaadSparse.Chapter13.Hierarchy` uses natural-
  number levels with an exact inverse-based solve at level zero on the nonsingular domain. The
  $\gamma$-cycle repeats its coarse solver uniformly, which has the same effect as a single
  direct solve at the bottom for $\gamma\ge1$. It also admits $\gamma=0$, when the coarse solver
  is skipped.
* **Theorem 13.2** (reading). `SaadSparse.Chapter13.theorem_13_2` uses Euclidean norms, assumes
  a bound on actual cycle error in place of the linear operator norm, and states the solved
  nonsingular base level explicitly. The argument needs $\xi\ge0$ and $c_2\xi^\mu<1$.
* **Example 13.6, truncation error** (scope). `SaadSparse.Chapter13.example_13_6_truncation`
  proves the componentwise inequality with $K$ bounding the absolute value of the fourth
  derivative. The source gives a Taylor identity with a point between neighboring grid nodes.
* **Example 13.2** (correction). The book's computation ends at
  $A_H e_j^H = -e_{j-1}^H + 2e_j^H - e_{j+1}^H$, which drops a factor $\frac14$; the Galerkin coarse
  matrix is $\frac14 \operatorname{tridiag}(-1, 2, -1)$. See `SaadSparse.Chapter13.example_13_2`.
* **Example 13.3** (correction). The book gives the Gauss–Seidel smoother as $B = (D - E)^{-1}F$;
  the approximate inverse is $B = (D - E)^{-1}$, and $(D - E)^{-1}F$ is the error propagation
  operator. See `SaadSparse.Chapter13.example_13_3_gaussSeidel`.
* **Lemma 13.1** (correction). The third clause names the restriction where the proof of the book
  gives the prolongation: the range of $T_h^H$ is $A_h$-orthogonal to the range of $I_H^h$. See
  `SaadSparse.Chapter13.lemma_13_1_energyInner_eq_zero`.
* **Equation (13.44)** (correction). The book prints the constant $7/3$ for the two-dimensional
  V-cycle; the geometric series $\sum_k 4^{-k}$ of the recurrence is $4/3$. See
  `SaadSparse.Chapter13.equation_13_44`.
* **Example 13.6** (correction). The closing display has $1 - (\pi h/2)^2/6$ in the denominator
  where the derivation gives its square. See `SaadSparse.Chapter13.example_13_6_le`.

* **Example 13.7** (scope). `SaadSparse.Chapter13.example_13_7` proves the exact pointwise
  formula for every fine mode. `SaadSparse.Chapter13.example_13_7_smul` identifies the same-
  index coarse mode only within the coarse index range.
  `SaadSparse.Chapter13.example_13_7_le_half` gives a uniform bound over the oscillatory half.
* **(13.62) and (13.63)** (reading). The predicates express one level at a time, so level-
  independent constants are supplied by their applications.
  `SaadSparse.Chapter13.equation_13_63` uses a coarse witness for the minimum bound and uses the
  same variable under the prolongation.
* **Theorem 13.3** (hypotheses and generalization). `SaadSparse.Chapter13.theorem_13_3_le`
  requires strictly fewer coarse unknowns to ensure a nonzero oscillatory subspace. The norm
  bound is stated pointwise with $\alpha\ge0$. `SaadSparse.Chapter13.theorem_13_3_cycle` extends
  the bound to arbitrary pre-smoothing and at least one post-smoothing step.
* **Example 13.8** (generalization). `SaadSparse.Chapter13.example_13_8_of_le` uses any relative
  quadratic-form upper bound. `SaadSparse.Chapter13.example_13_8` gives the inequality for all
  real $\omega$, with `SaadSparse.Chapter13.example_13_8_pos` separately establishing $\alpha>0$
  in the source's range.
* **Equation (13.61)** (correction). The book's last equality reads
  $\mathcal{T}_h = \operatorname{Null}(I_h^H)$, without the factor $A_h$; this is false, and
  $\mathcal{T}_h = \operatorname{Null}(I_h^H A_h)$. See `SaadSparse.Chapter13.equation_13_61` and
  `SaadSparse.Chapter13.oscillatorySubspace_ne_ker_of_restriction`.

* **(13.68)** (source location). `SaadSparse.Chapter13.equation_13_68` and
  `SaadSparse.Chapter13.equation_13_68_of_rowSum_zero` state the exact expansions in the
  unnumbered displays after (13.69). Printed (13.68) is the heuristic that the $A$ quadratic
  form is much smaller than the $D$ quadratic form on smooth errors.
* **(13.69)** (reading). `SaadSparse.Chapter13.equation_13_69` gives the exact row identity
  equivalent to zero residual in that row. The source presents an approximate relation for
  smooth errors.

**Chapter 14.**

* **(14.4), (14.5) and Algorithm 14.1** (representation and totalization).
  `SaadSparse.Chapter14.blockGaussianElimination` expresses the source's block solves through
  exact inverse actions. The definitions use total inverses, and the correctness theorem
  requires nonsingular $A$ and $B$.
* **(14.16)** (generalization). `SaadSparse.Chapter14.equation_14_16` needs a block diagonal
  interior and a common interface index set on which the local $C_i$ sum. It does not require
  the blocks to arise from finite-element assembly.
* **(14.20) and §14.2.5** (scope and normalization). `SaadSparse.Chapter14.modelSchurEigen`
  represents the scalar recurrence at an eigenvalue of $B$, starting at source index $1$.
  `SaadSparse.Chapter14.modelSeq` omits the common factor $1/\sqrt{\mu^2-4}$, which cancels in
  the ratio. The matrix recurrence and identification of its final term with the Schur
  complement remain outside the statement.

* **(14.8)–(14.14)** (representation). `SaadSparse.Chapter14.VertexPartitioning` groups all
  interiors before interfaces and uses a label to recover each subdomain's blocks. Sums over
  off-diagonal subdomains include zero couplings in place of the source's explicit neighbor
  sets. Local Schur formulas use total inverses.
* **Algorithm 14.3 and Theorem 14.2** (representation and hypotheses).
  `SaadSparse.Chapter14.VertexPartitioning.schwarzSweep` is an exact global block-lower inverse
  update. `SaadSparse.Chapter14.theorem_14_2` makes the local inverses of $B_i$ and $S_i$ well
  posed explicitly and allows real or complex matrices with arbitrary coupling patterns of the
  given block shape.
* **Proposition 14.3 and Lemma 14.4** (scope). `SaadSparse.Chapter14.proposition_14_3` states
  the fixed-point update under positive definiteness and includes the additive identities from
  §14.3.3. `SaadSparse.Chapter14.lemma_14_4` writes the recurrences from prefix $0$ and includes
  the sum from (14.35).
* **Theorems 14.5 and 14.7** (generalization). The eigenvalue bounds are stated for every
  eigenvalue through its real part over the real or complex field, with companion inequalities
  for the energy quadratic form. The orthogonal projector theory uses the Hermitian energy inner
  product.
* **Assumption 2 and Lemma 14.8** (generalization).
  `SaadSparse.Chapter14.IsStrengthenedCauchySchwarz` takes vectors already in each projector's
  range and uses the real parts of their Hermitian inner products.
  `SaadSparse.Chapter14.lemma_14_8` requires Assumption 2 alone.
* **Theorem 14.9** (reading). `SaadSparse.Chapter14.theorem_14_9` gives the operator bound
  pointwise in the energy norm over the real or complex field, with $K_0>0$ and $K_1\ge0$
  explicit.
* **Theorem 14.6** (correction). The book asks only that subdomains of the same colour have no
  common nodes. This is not enough; the theorem assumes that subdomains of the same colour have no
  coupling in $A$. See `SaadSparse.Chapter14.theorem_14_6`.

* **(14.46)** (totalization). `SaadSparse.Chapter14.inducedPreconditioner` uses total inverses
  for the full preconditioner and the inverse principal block. Proposition 14.10 makes the
  diagonal-block invertibility conditions explicit.
* **§14.4.2, probing** (scope). `SaadSparse.Chapter14.probeVec` defines the three residue-class
  probes with 0-based indexing and returns zero for other residue numbers.
  `SaadSparse.Chapter14.probing_eq` gives uniqueness for an exactly tridiagonal matrix.
* **Proposition 14.10** (generalization). The book assumes an ILU factorization;
  `SaadSparse.Chapter14.proposition_14_10` assumes only block triangular factors. See
  `SaadSparse.Chapter14.proposition_14_10_of_isILU` for the form of the book.

* **(14.55) and Proposition 14.12** (domain). `SaadSparse.Chapter14.blockPreconditioner` defines
  the product using the total inverse of $B$. The correspondence theorems assume invertible
  $B,L_S,U_S$. They need no separate approximate factorization remainder because $L_SU_S-S$ is
  determined by those factors.
* **Propositions 14.11 and 14.12** (generalization). `SaadSparse.Chapter14.proposition_14_11`
  and `SaadSparse.Chapter14.proposition_14_12` also give the converse for a candidate in the
  consistent form. The source states the direction from full-system iterates to reduced-system
  iterates.
* **Propositions 14.11 and 14.12** (reading). The book speaks of "the same Krylov subspace method",
  which is not a formal object. The propositions are stated for the minimal-residual and the
  Galerkin specifications, in the variables $u = U_A x$ and $w = U_S y$. See
  `SaadSparse.Chapter14.proposition_14_11` and `SaadSparse.Chapter14.proposition_14_12`.

* **§14.6.3, Laplacian sign** (correction). `SaadSparse.Chapter14.inner_lapOperator_self_nonneg`
  proves positive semidefiniteness for the displayed sign convention. The source says negative
  semidefinite, although its smallest-eigenvalue statement and Exercise 14.11 use the positive
  sign.
* **§14.6.3, Fiedler vector** (scope). `SaadSparse.Chapter14.fiedlerVector` characterizes the
  second smallest eigenvalue as the least Rayleigh quotient orthogonal to constants for a
  connected graph on at least two vertices. The statement makes no claim about the balance or
  output of the sign partition.
* **Definitions 14.13–14.15** (domain). `SaadSparse.Chapter14.IsMap` and
  `SaadSparse.Chapter14.IsProperMap` permit arbitrary families of subsets of a finite vertex
  set. `SaadSparse.Chapter14.definition_14_14` uses open balls for strict interior, and the
  equivalence with topological interiors of closed balls is stated for nonzero radii.
  `SaadSparse.Chapter14.definition_14_15` constructs a loopless graph for all $\alpha$ and ball
  families. The source assumes $\alpha\ge1$ and $k$-ply data and leaves distinctness implicit in
  the edge display.

## Not formalized

**Chapter 1.**

* **The difference between Algorithms 1.1 and 1.2 in floating-point arithmetic.** It belongs to a
  floating-point layer.
* **Algorithm 1.3, the step-by-step program.** The declaration states the final factorization.
* **§1.8.3, the spectra of the $2 \times 2$ real Schur blocks.** The theorem records only the
  block sizes and the vanishing entries below the blocks.
* **Theorem 1.11, the value of the sum.** The surface states summability and nonsingularity
  separately. The real-matrix identity is available as
  `Matrix.hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one`.
* **Equation (1.35), the lower bound.** The surface proves the upper bound in
  `SaadSparse.Chapter01.numericalRadius_le_l2_opNorm`.
* **Definition 1.23, strict positivity and negativity.** The declaration gives the weak order
  and the corresponding weak sign conditions.
* **Problem P-1.28, the entrywise comparison of the Gram matrices.** The surface states the
  norm comparison.
* **Equation (1.47).** The Neumann series identity is available as
  `Matrix.hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one`.
* **Problem P-1.18, ordinary Hermitian symmetry.** The declarations give the conclusions for
  the $B$-form only.
* **Problem P-1.33.** The answer is a counterexample, not a theorem:
  $\begin{bmatrix} 1 & -2 \\ -2 & 1 \end{bmatrix}$ satisfies the clauses (1)–(3) of Definition 1.30,
  and its inverse is entrywise negative.

**Chapter 2.**

* **§2.2.2, the sixth-order accuracy of the nine-point stencil (d) on harmonic functions.** It needs
  the equality of mixed partial derivatives for a curried function, which Mathlib does not have.
* **§2.2.3, the asymptotic value $4/(\pi^2 h^2)$ of the condition number of the one-dimensional
  model matrix.**
* **§2.2.6, the fast Fourier transform and the operation count of Algorithm 2.1.** These are
  implementation, not statements.
* **§2.2.7, the stability of block cyclic reduction compared with Buneman's variant.** The book
  asserts it with no analysis.
* **§2.3, the divergence theorem (2.37), the integration by parts (2.38)–(2.40) and the Neumann
  equation (2.47).** They need a surface measure on the boundary and an outward normal, which
  Mathlib does not have.
* **§2.3, the weak formulation (2.41).** The backbone has $H^1_0(\Omega)$ as `SobolevZero`, but no
  trace operator.
* **§2.3, the discrete space $V_h$ of (2.42) and the positive definiteness of $a$ on it.** They need
  a triangulation of a planar domain and the piecewise affine functions on it.
* **§2.4, triangulations, their mesh size and their refinements.** They need the same geometry as
  $V_h$.
* **§2.4, the angle bounds for a usable refinement.** The book never writes such a bound down.
* **§2.5, the derivation of the scheme, (2.48)–(2.51).** The cell integration is the divergence
  theorem on a cell, and the book states no error bound for the approximations.

**Chapter 3.**

* **§3.2.2, the graphs of matrices that arise from partial differential equations.** The section
  states no result there.
* **Examples 3.4, 3.5 and 3.6.** Each is a run on the mesh of Figure 2.10, which the text does not
  reproduce.
* **The reverse Cuthill–McKee ordering.** The book gives it as an observation with no statement.
* **Problem P-3.12.** It needs the notion of a structural inverse, which the chapter does not
  define.
* **The compressed sparse column format of §3.4.** The section names it but does not write it out.
* **§3.5, the code fragments for the matrix-by-vector product.** They state nothing.
* **§3.6, sparse direct solution methods.** The book states no complexity or fill-in result.
* **§3.7, test problems.** The section is descriptive.

**Chapter 4.**

* **Algorithm 4.1 with overlapping blocks.** The book proves no theorem about the overlapping case.
* **Theorem 4.9 for irreducible column diagonal dominance.** The irreducible case is stated with
  the row sums used in the proof of the book.
* **The convergence factor of §4.2.1 for a general $d_0$.** The book derives it heuristically from
  the Jordan form.
* **§4.3, the optimal parameter $r$, the cyclic parameter sequences, and the comparison of ADI with
  SSOR.** The book states no formula, bound or theorem for them.
* **§4.3, the operation count $O(n^2 \log n)$.**
* **§4.3, the parabolic formulation (4.53)–(4.56).** It is a semi-discretization of a partial
  differential equation, not the image of Algorithm 4.3 under $r = 2/\Delta t$.
* **§4.3, the decoupling of each half-step into tridiagonal systems.** It is about a data layout,
  not about the iteration.

**Chapter 6.**

* **Theorem 6.24, necessity.** It is the Faber–Manteuffel theorem proper. The book states it without
  proof, and the known proofs are research papers.
* **The Givens elimination of block GMRES.** The book states no result about it.

**Chapter 7.**

* **The LU factorization $M_k = L_k U_k$ of the moment matrix (§7.1.2).** Neither Mathlib nor the
  library has a general existence theorem for the LU factorization.
* **The look-ahead Lanczos algorithms (§7.1.2).** They are implementation, with no claim attached.
* **Problem P-7.5, second and third parts.** The second part adds nothing to the first, and the
  third asks for an algorithm.

**Chapter 8.**

* **The eigenvalues $\pm\sigma_i(A)$ of the augmented matrix of §8.1, and Problem P-8.4.** They need
  a singular value decomposition, which Mathlib does not have.
* **Problem P-8.2(c), the convergence interval of the unnormalized iteration.** It needs the
  symmetric square root of $D$.
* **Example 8.1.** Table 8.1 reports measured counts of a floating-point run.
* **Problem P-8.6(c).** It needs a theorem on the conjugate gradient method for a consistent
  symmetric positive semidefinite system, which the backbone does not have.
* **Problem P-8.6(d).** It needs a QR factorization of a rectangular matrix.
* **Problem P-8.9 (inexact Uzawa).** It needs a theorem on perturbed fixed-point iterations.

**Chapter 9.**

* **Problems P-9.7, P-9.8(a) and (b), and P-9.9.**
* **The inner-outer variants of Golub and Overton (§9.6).** The book states no result about them.

**Chapter 10.**

* **Example 10.1.** Table 10.1 reports measured counts of a floating-point run.
* **Algorithms 10.4 and 10.5.** They are listings.
* **Algorithm 10.6 and §10.4.3–10.4.6 (ILUT implementation, ILUTP, ILUS, Crout ILU).** They are
  implementations and dropping heuristics.
* **§10.5.1–10.5.5 and §10.5.7–10.5.8 (dropping strategies, factored approximate inverses).** They
  carry no statement of their own.
* **Theorem 10.16 (§10.7.1).** The diagonal blocks of the block ILU preconditioner (10.77) of a
  block tridiagonal M-matrix are symmetric M-matrices, and the preconditioner is positive definite.
  The book says only that the theorem "can be shown". Its statement needs the block tridiagonal
  splitting, the recurrence (10.79)–(10.80) and the closed form (10.81) of the tridiagonal part of
  the inverse of a tridiagonal matrix, which the library does not have. Because $\Omega^{(3)}$ in
  (10.81) is a truncation of the inverse, the blocks $\Delta_{i+1}$ of the recurrence are not Schur
  complements. It is the only item of §10.7, which has no module.
* **§10.8.2 (shifted IC(0)).** It is an algorithm with an empirical discussion and no theorem.
* **Algorithm 10.18 (incomplete modified Gram–Schmidt).**

**Chapter 11.**

* **Example 11.2.** Neither its mesh nor the permuted matrix of Figure 11.12 is in the text.
* **§11.6.3 (level scheduling).** The book defines the depth of a vertex and the levels, but states
  no property of them.
* **Algorithms 11.1–11.8.**

**Chapter 12.**

* **§12.2, weighting by a nonnegative diagonal matrix $D_i$.** The identity that the book states is
  the scalar one.
* **§12.3.4 (the nonsymmetric case).** Its results are Lemma 6.26 and Theorem 6.27, and the case of
  a polygon is a numerical procedure.
* **Example 12.2.** It is a table of measured iteration counts and timings.
* **The identification of (12.16) with the least-squares residual polynomial, and the case
  $\alpha = 0$ of its decay.** They need Jacobi polynomials, which Mathlib does not have.
* **§12.4, the colouring itself, and Algorithm 12.3.** The colouring is a graph problem with no
  claim attached, and the algorithm is a listing.
* **(12.26)–(12.29), the element-by-element preconditioners.** The book claims no property of them.
* **§12.7.1.** It points back to §10.5.
* **§12.7.3, Algorithm 12.8.** It is a block Gauss–Seidel iteration for the normal equations, which
  Chapter 8 covers in general.

**Chapter 13.**

* **Algorithm 13.1 (nested iteration).** The book uses it only to introduce the notation.
* **The identity $M_h = M_H^h + S^{\nu_2} I_H^h M_H A_H^{-1} I_h^H A_h$ of §13.4.3.** It needs the
  error operator of the whole recursive cycle, and the book uses it nowhere.
* **Examples 13.4 and 13.5.** They record measured floating-point runs, and the comparisons that the
  book draws from them are not proved.
* **The smoothness criterion (13.70).** The book does not call its averaging argument rigorous.
* **§13.6.2–13.6.4 and the interpolation weights (13.72)–(13.74).** They are constructions, not
  theorems.

**Chapter 14.**

* **The matrix form of §14.2.5.** It needs the block $LU$ factorization of a block tridiagonal
  matrix and a matrix square root.
* **§14.4.2, probing.** It is a heuristic, and the book gives no bound on $S - T$.
* **§14.4.3.** It is advice with no stated result.
* **Theorem 14.16 (geometric separator theorem of Miller, Teng, Thurston and Vavasis).** The book
  quotes it without proof. Its proof needs stereographic projection, centerpoints and a random great
  circle, which Mathlib does not have. Definitions 14.14 and 14.15, over which it is stated, are
  formalized.
* **Coordinate and inertial bisection, §14.6.4 and Algorithms 14.7–14.10.** They are heuristics with
  no claim attached.
-/
