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

* **Equation (1.18)** (typo). The book prints $\mathbb{C}^n = \operatorname{Ran}(A) \oplus
  \operatorname{Null}(A^T)$ in a complex setting, where $A^H$ is meant. See
  `SaadSparse.Chapter01.equation_1_18`.
* **Derivation of (1.22)** (typo). The book prints $\|x\|_1^2$ where $\|x\|_2^2$ is meant. See
  `SaadSparse.Chapter01.equation_1_22`.
* **Equation (1.25)** (typo). The book prints the entry $\beta + x_{ii}$ of the Householder
  direction, where $\beta + x_{kk}$, the pivot of step $k$, is meant. See
  `SaadSparse.Chapter01.householder_mulVec_apply_of_eq_zero`, and
  `SaadSparse.Chapter06.householderDir` for the Householder Arnoldi process of §6.3.
* **§1.12.4, $\|P\|_2 = 1$ for an orthogonal projector** (reading). The claim needs $P \neq 0$,
  because the zero matrix is the orthogonal projector onto $\{0\}$. The library states
  $\|Px\|_2 \le \|x\|_2$ for every orthogonal projector. See `SaadSparse.Chapter01.norm_apply_le`.
* **Corollary 1.39** (reading). The book's $\min_{y \in M}$ is read with $y$ ranging over $M$, so
  $y \in M$ is a hypothesis and the statement is about the least element of the set of distances.
  See `SaadSparse.Chapter01.corollary_1_39`.
* **Example 1.5** (generalization). The book takes $i$ to be the first index and $j$ the last. The
  statement holds for any $i \neq j$. See `Matrix.example_1_5`.

**Chapter 2.**

* **§2.2.3, the scaling $1/h^2$** (reading). The book writes the scaling on the right-hand side of
  the scalar equation and on the matrix in the display. The library puts it on the matrix only. See
  `SaadSparse.Chapter02.laplacian1D`.
* **§2.2.5, the interior index range** (typo). The book prints $0 < i < n_1$, which is off by one.
  See `SaadSparse.Chapter02.laplacian2D`.
* **Equation (2.29)** (typo). The book prints the two indices transposed, which gives systems of the
  wrong size. The library states $p$ systems of size $m$, as line 2 of Algorithm 2.1 says. See
  `SaadSparse.Chapter02.equation_2_29`.
* **Equations (2.45)–(2.46)** (reading). The book leaves implicit that $a_e(\phi_i, \phi_j) = 0$
  unless both $i$ and $j$ are vertices of the element $e$. The library makes this a hypothesis. See
  `SaadSparse.Chapter02.equation_2_45`.

**Chapter 3.**

* **§3.2.1 and Problems P-3.2, P-3.4 and P-3.5, the patterns of sums, powers and products**
  (reading). The book assumes that no numerical cancellation occurs. The library proves the
  containments with no hypothesis, and the equalities for entrywise nonnegative matrices. See
  `SaadSparse.Chapter03.pattern_add_of_nonneg` and `SaadSparse.Chapter03.problem_3_5`.
* **Example 3.3, the arrow matrix** (reading). Figure 3.4 prints a pattern and no values, so the
  pattern is the hypothesis. The fill claims are stated for one elimination step and for an
  exhibited $LU$ factorization. See `SaadSparse.Chapter03.example_3_3`.
* **§3.3.3, level-set orderings** (generalization). The book leaves the connectedness of the graph
  implicit. The statements hold without it. See `SaadSparse.Chapter03.levelSet_blockTridiagonal`.
* **§3.3.3, the size of an independent set** (generalization). The book states the bound for the set
  that Algorithm 3.4 produces. It holds for every maximal independent set. See
  `SaadSparse.Chapter03.indepSet_card_ge`.
* **Algorithm 3.6 and Problem P-3.11** (reading). The traversal of the greedy colouring is the order
  of the index set. See `SaadSparse.Chapter03.greedy_coloring_bounds`.
* **§3.3.4, irreducibility** (reading). The "connected" adjacency graph of the book is read as
  strongly connected, with directed paths of positive length, and the equivalence with the block
  form needs $n \ge 2$. See `SaadSparse.Chapter03.isPatternIrreducible_iff`.
* **§3.3.4, the Frobenius normal form** (reading). The book says that each block corresponds to a
  connected component. The blocks are the strongly connected components, in an order in which every
  arrow points forward. See `SaadSparse.Chapter03.frobenius_normal_form`.

**Chapter 4.**

* **Definition 4.5** (reading). The book prints all three conditions with column sums, while the
  proofs of Theorems 4.6 and 4.9 use row sums. Both forms are stated, following the backbone's
  `Matrix.IsStrictDiagDominant` (rows) and `Matrix.IsStrictColDiagDominant` (columns). See
  `SaadSparse.Chapter04.definition_4_5_iff`.
* **Theorem 4.16** (reading). The book uses the name $M_{SOR}$ for the SOR iteration matrix, while
  (4.26) uses it for the preconditioner. The library gives the two different names. See
  `SaadSparse.Chapter04.theorem_4_16_mp`.

**Chapter 5.**

* **§5.1.2** (reading). The book states that $W^TAV$ is nonsingular if and only if no vector of $AK$
  is orthogonal to $L$, which fails for $A = 0$. The library states that $u \in K$ and $u \neq 0$
  imply $Au \notin L^\perp$. See `SaadSparse.Chapter05.isUnit_transpose_mul_mul_iff`.
* **Proposition 5.6** (reading). The statement presupposes that $Q_K^L$ exists, that is
  $K \cap L^\perp = \{0\}$. The library adds this hypothesis. See
  `SaadSparse.Chapter05.proposition_5_6`.

**Chapter 6.**

* **Proposition 6.8** (reading). The library adds two hypotheses that the book leaves implicit:
  $\|v_{m+1}\| = 1$, and $v_1, \dots, v_m$ span $\mathcal{K}_m$. See
  `SaadSparse.Chapter06.proposition_6_8`.
* **Proposition 6.9** (reading). The statement assumes that $m$ Arnoldi steps are completed,
  $m \le \operatorname{grade}(v_1)$, in addition to the printed $m \le n$, because the proof uses
  it. See `SaadSparse.Chapter06.proposition_6_9`.
* **Proposition 6.10** (reading). The implicit hypothesis that the first $j$ steps are taken is
  explicit: $r_0 \neq 0$ and no breakdown before step $j$. See
  `SaadSparse.Chapter06.proposition_6_10_book`.
* **Propositions 6.12, 6.13 and 6.17, Lemma 6.16** (reading). The statements make explicit the
  nonsingularity of $H_m$ and the condition $\rho^G_m \neq 0$ that the proofs need. See
  `SaadSparse.Chapter06.proposition_6_12`, `SaadSparse.Chapter06.proposition_6_13`,
  `SaadSparse.Chapter06.proposition_6_17` and `SaadSparse.Chapter06.lemma_6_16`.
* **Proposition 6.15** (correction). The book prints the upper bound $\sqrt{m}\,\rho^G_m$ in (6.68).
  The bound is $\sqrt{m+1}\,\rho^G_m$. See `SaadSparse.Chapter06.proposition_6_15`.
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

* **Problem P-7.5** (correction). The book says that $t^k p_j$ is orthogonal to
  $p_1, \dots, p_{j-k}$. The range is one polynomial too long, and the library stops at $p_{j-k-1}$.
  The worked example of §7.1.2 has the same error. See `SaadSparse.Chapter07.problem_7_5`.

**Chapter 8.**

* **Equation (8.8)** (generalization). The book states the identity for a nonsingular $A$. It holds
  for every square $A$, because Lean's inverse of a singular matrix is $0$ and both sides vanish.
  See `SaadSparse.Chapter08.equation_8_8`.
* **Problem P-8.2** (typo). The problem writes the normalization $\|A^T e_i\|_2 = 1$ of the rows.
  The hypothesis that makes Cimmino's step Richardson's is the normalization $\|A e_i\|_2 = 1$ of
  the columns, as in Algorithm 8.3. See `SaadSparse.Chapter08.cimmino_eq_richardson`.

**Chapter 10.**

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
* **Theorem 10.18** (correction). The printed condition constrains only the pairs $(i, j)$ with
  $i < j$, while Algorithm 10.17 drops entries $l_{ij}$ with $j < i$, so the theorem is false as
  printed: for $n = 3$ and $P_L = \{(3, 2)\}$ the condition holds and $LL^T$ misses $b_{32}$. The
  hypothesis adds the symmetry of $P_L$. See `SaadSparse.Chapter10.IsICPattern`.
* **Theorem 10.18** (reading). The book attaches the theorem to Algorithm 10.18, the incomplete
  modified Gram–Schmidt process. It is stated for Algorithm 10.17, which computes the same $L$ under
  the hypothesis of the theorem. See `SaadSparse.Chapter10.theorem_10_18`.

**Chapter 13.**

* **Equation (13.23)** (generalization). The book prints the upper bound $1 - \omega/2$ for the
  oscillatory eigenvalues of weighted Jacobi in one dimension. The library proves the sharp bound
  $1 - \omega$. See `SaadSparse.Chapter13.weightedJacobi_eigenvalue_mem_Ioc`.
* **§13.2.2, the smoothing factor at $\omega = 1/2$** (generalization). The book gives $3/4$ in one
  dimension. The library proves the sharp value $1/2$. See
  `SaadSparse.Chapter13.smoothingFactor_one_half`.
* **The sentence after (13.25)** (typo). The book says that $\omega = 3/5$ gives the smoothing
  factor $4/5$. The two numbers are transposed: $\omega = 4/5$ gives $3/5$. See
  `SaadSparse.Chapter13.smoothingFactor2D_four_fifths`.
* **Equation (13.29)** (correction). The book prints $|\cos\theta_k|^j$. The eigenvector has the
  signed power $(\cos\theta_k)^j$. See `SaadSparse.Chapter13.gaussSeidelVec`.
* **Example 13.2** (correction). The book's computation ends at
  $A_H e_j^H = -e_{j-1}^H + 2e_j^H - e_{j+1}^H$, which drops a factor $\frac14$. The Galerkin coarse
  matrix is $\frac14 \operatorname{tridiag}(-1, 2, -1)$. See `SaadSparse.Chapter13.example_13_2`.
* **Example 13.3** (correction). The book gives the Gauss–Seidel smoother as $B = (D - E)^{-1}F$.
  The approximate inverse is $B = (D - E)^{-1}$, and $(D - E)^{-1}F$ is the error propagation
  operator. See `SaadSparse.Chapter13.example_13_3_gaussSeidel`.
* **Lemma 13.1** (correction). The third clause names the restriction where the proof of the book
  gives the prolongation: the range of $T_h^H$ is $A_h$-orthogonal to the range of $I_H^h$. See
  `SaadSparse.Chapter13.lemma_13_1_energyInner_eq_zero`.
* **Equation (13.44)** (correction). The book prints the constant $7/3$ for the two-dimensional
  V-cycle. The geometric series $\sum_k 4^{-k}$ of the recurrence is $4/3$. See
  `SaadSparse.Chapter13.equation_13_44`.
* **Example 13.6** (correction). The closing display has $1 - (\pi h/2)^2/6$ in the denominator,
  where the derivation gives its square. See `SaadSparse.Chapter13.example_13_6_le`.
* **Equation (13.61)** (correction). The last equality of the book reads
  $\mathcal{T}_h = \operatorname{Null}(I_h^H)$, which is false. The library states
  $\mathcal{T}_h = \operatorname{Null}(I_h^H A_h)$. See `SaadSparse.Chapter13.equation_13_61` and
  `SaadSparse.Chapter13.oscillatorySubspace_ne_ker_of_restriction`.

**Chapter 14.**

* **Theorem 14.6** (correction). The book asks only that subdomains of the same colour have no
  common nodes. This is not enough. The theorem assumes that subdomains of the same colour have no
  coupling in $A$. See `SaadSparse.Chapter14.theorem_14_6`.
* **Proposition 14.10** (generalization). The book assumes an ILU factorization. The library assumes
  only block triangular factors. See `SaadSparse.Chapter14.proposition_14_10`, and
  `SaadSparse.Chapter14.proposition_14_10_of_isILU` for the form of the book.
* **Propositions 14.11 and 14.12** (reading). The book speaks of "the same Krylov subspace method",
  which is not a formal object. The propositions are stated for the minimal residual and the
  Galerkin specifications, in the variables $u = U_A x$ and $w = U_S y$. See
  `SaadSparse.Chapter14.proposition_14_11` and `SaadSparse.Chapter14.proposition_14_12`.

## Not formalized

**Chapter 1.**

* **The difference between Algorithms 1.1 and 1.2 in floating-point arithmetic.** It belongs to a
  floating-point layer.
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
