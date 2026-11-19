/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter01
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter01.Section03
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter01.Section05
import NumlibSurface.GolubVanLoan.Chapter01.Section06
import NumlibSurface.GolubVanLoan.Chapter02
import NumlibSurface.GolubVanLoan.Chapter02.Section01
import NumlibSurface.GolubVanLoan.Chapter02.Section02
import NumlibSurface.GolubVanLoan.Chapter02.Section03
import NumlibSurface.GolubVanLoan.Chapter02.Section04
import NumlibSurface.GolubVanLoan.Chapter02.Section05
import NumlibSurface.GolubVanLoan.Chapter02.Section06
import NumlibSurface.GolubVanLoan.Chapter02.Section07
import NumlibSurface.GolubVanLoan.Chapter03
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter03.Section02
import NumlibSurface.GolubVanLoan.Chapter03.Section03
import NumlibSurface.GolubVanLoan.Chapter03.Section04
import NumlibSurface.GolubVanLoan.Chapter03.Section05
import NumlibSurface.GolubVanLoan.Chapter03.Section06
import NumlibSurface.GolubVanLoan.Chapter04
import NumlibSurface.GolubVanLoan.Chapter04.Section01
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter04.Section03
import NumlibSurface.GolubVanLoan.Chapter04.Section04
import NumlibSurface.GolubVanLoan.Chapter04.Section05
import NumlibSurface.GolubVanLoan.Chapter04.Section06
import NumlibSurface.GolubVanLoan.Chapter04.Section07
import NumlibSurface.GolubVanLoan.Chapter04.Section08
import NumlibSurface.GolubVanLoan.Chapter05
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section03
import NumlibSurface.GolubVanLoan.Chapter05.Section04
import NumlibSurface.GolubVanLoan.Chapter05.Section05
import NumlibSurface.GolubVanLoan.Chapter05.Section06
import NumlibSurface.GolubVanLoan.Chapter06
import NumlibSurface.GolubVanLoan.Chapter06.Section01
import NumlibSurface.GolubVanLoan.Chapter06.Section02
import NumlibSurface.GolubVanLoan.Chapter06.Section03
import NumlibSurface.GolubVanLoan.Chapter06.Section04
import NumlibSurface.GolubVanLoan.Chapter06.Section05
import NumlibSurface.GolubVanLoan.Chapter07
import NumlibSurface.GolubVanLoan.Chapter07.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section02
import NumlibSurface.GolubVanLoan.Chapter07.Section03
import NumlibSurface.GolubVanLoan.Chapter07.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section05
import NumlibSurface.GolubVanLoan.Chapter07.Section06
import NumlibSurface.GolubVanLoan.Chapter07.Section07
import NumlibSurface.GolubVanLoan.Chapter07.Section08
import NumlibSurface.GolubVanLoan.Chapter07.Section09
import NumlibSurface.GolubVanLoan.Chapter08
import NumlibSurface.GolubVanLoan.Chapter08.Section01
import NumlibSurface.GolubVanLoan.Chapter08.Section02
import NumlibSurface.GolubVanLoan.Chapter08.Section03
import NumlibSurface.GolubVanLoan.Chapter08.Section04
import NumlibSurface.GolubVanLoan.Chapter08.Section05
import NumlibSurface.GolubVanLoan.Chapter08.Section06
import NumlibSurface.GolubVanLoan.Chapter08.Section07
import NumlibSurface.GolubVanLoan.Chapter09
import NumlibSurface.GolubVanLoan.Chapter09.Section01
import NumlibSurface.GolubVanLoan.Chapter09.Section02
import NumlibSurface.GolubVanLoan.Chapter09.Section03
import NumlibSurface.GolubVanLoan.Chapter09.Section04
import NumlibSurface.GolubVanLoan.Chapter10
import NumlibSurface.GolubVanLoan.Chapter10.Section01
import NumlibSurface.GolubVanLoan.Chapter10.Section02
import NumlibSurface.GolubVanLoan.Chapter10.Section03
import NumlibSurface.GolubVanLoan.Chapter10.Section04
import NumlibSurface.GolubVanLoan.Chapter10.Section05
import NumlibSurface.GolubVanLoan.Chapter10.Section06
import NumlibSurface.GolubVanLoan.Chapter11
import NumlibSurface.GolubVanLoan.Chapter11.Section01
import NumlibSurface.GolubVanLoan.Chapter11.Section02
import NumlibSurface.GolubVanLoan.Chapter11.Section03
import NumlibSurface.GolubVanLoan.Chapter11.Section04
import NumlibSurface.GolubVanLoan.Chapter11.Section05
import NumlibSurface.GolubVanLoan.Chapter11.Section06
import NumlibSurface.GolubVanLoan.Chapter12
import NumlibSurface.GolubVanLoan.Chapter12.Section01
import NumlibSurface.GolubVanLoan.Chapter12.Section02
import NumlibSurface.GolubVanLoan.Chapter12.Section03
import NumlibSurface.GolubVanLoan.Chapter12.Section04
import NumlibSurface.GolubVanLoan.Chapter12.Section05

/-!
# Golub and Van Loan, *Matrix Computations*

This library formalizes the book of Gene H. Golub and Charles F. Van Loan, *Matrix Computations*,
4th edition, Johns Hopkins University Press, 2013 [golub2013matrix]. The book treats the algorithms
of numerical linear algebra and their analysis: matrix multiplication, norms and the singular value
decomposition, linear systems and their factorizations, least-squares problems, symmetric and
unsymmetric eigenvalue problems, functions of matrices, iterative methods for large sparse problems,
and structured matrices and tensors. The library covers all twelve chapters, with one module for
each section. Each module states the results of the source in the terms of the source: real matrices
$A \in \mathbb{R}^{m \times n}$ are `Matrix (Fin m) (Fin n) ℝ`, and every algorithm is a program
that follows the source step by step. The proofs specialize the backbone, in particular the modules
under `Numlib.LinearAlgebra.Matrix`, `Numlib.Analysis.Matrix`, `Numlib.Conditioning`,
`Numlib.FloatingPoint`, `Numlib.Eigen`, `Numlib.Krylov` and `Numlib.Stationary`.

## Coverage

Every theorem, lemma and corollary of the source is formalized. Every numbered algorithm is
formalized, including the variants for other loop orders, blocked variants and recursive variants.
An algorithm is a definition `algorithm_N_M_K`, written once as a monadic program in which every
arithmetic result passes through a rounding hook `rnd : ℝ → M ℝ`, together with a theorem
`algorithm_N_M_K_spec` that states its correctness in exact arithmetic (`M := Id`, `rnd := pure`)
against a specification of the backbone. Where the source analyses the rounding errors of an
algorithm, a theorem about its runs in the relational model of floating-point arithmetic
(`M := SetM`, `rnd := fp.round`) states the bound of the source; these theorems use the relational
predicates of the backbone, and the program semantics is `Numlib.FloatingPoint.Program`. A numbered
display $(N.M.K)$ is formalized when it states a precise proposition. Problems are out of scope; a
Problem that the text cites in a proof becomes a supporting lemma. Also out of scope are the
operation counts, §1.5 and §1.6 (except Cannon's identity (1.6.16)), the parallel and architecture
material of §3.6, the discussion of storage formats and of the BLAS, the numerical examples, and the
Notes and References. The section modules list the omitted items one by one.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1.1 | `Chapter01.Section01` | Basic algorithms and notation: Algorithms 1.1.1–1.1.8 |
| §1.2 | `Chapter01.Section02` | Structure and efficiency: Algorithms 1.2.1–1.2.3 |
| §1.3 | `Chapter01.Section03` | Block matrices and algorithms: Theorem 1.3.1; Algorithm 1.3.1 |
| §1.4 | `Chapter01.Section04` | Fast matrix-vector products |
| §1.5 | `Chapter01.Section05` | Vectorization and locality |
| §1.6 | `Chapter01.Section06` | Parallel matrix multiplication: equation (1.6.16) |
| §2.1 | `Chapter02.Section01` | Basic ideas from linear algebra: Theorem 2.1.1 |
| §2.2 | `Chapter02.Section02` | Vector norms: equations (2.2.1)–(2.2.7) |
| §2.3 | `Chapter02.Section03` | Matrix norms: Theorems 2.3.1, 2.3.4; Lemma 2.3.3; Corollary 2.3.2 |
| §2.4 | `Chapter02.Section04` | The singular value decomposition |
| §2.5 | `Chapter02.Section05` | Subspace metrics: Theorems 2.5.1–2.5.3; equation (2.5.1) |
| §2.6 | `Chapter02.Section06` | The sensitivity of square systems |
| §2.7 | `Chapter02.Section07` | Finite precision matrix computations: Lemma 2.7.1 |
| §3.1 | `Chapter03.Section01` | Triangular systems: Algorithms 3.1.1–3.1.4 |
| §3.2 | `Chapter03.Section02` | The LU factorization: Theorem 3.2.1; Algorithms 3.2.1–3.2.4 |
| §3.3 | `Chapter03.Section03` | Roundoff error in Gaussian elimination: Theorems 3.3.1, 3.3.2 |
| §3.4 | `Chapter03.Section04` | Pivoting: Algorithms 3.4.1–3.4.3; equations (3.4.1)–(3.4.13) |
| §3.5 | `Chapter03.Section05` | Improving and estimating accuracy: Algorithm 3.5.1 |
| §3.6 | `Chapter03.Section06` | Parallel LU: equations (3.6.2)–(3.6.5) |
| §4.1 | `Chapter04.Section01` | Diagonal dominance and symmetry |
| §4.2 | `Chapter04.Section02` | Positive definite systems |
| §4.3 | `Chapter04.Section03` | Banded systems: Theorems 4.3.1–4.3.3; Algorithms 4.3.1–4.3.6 |
| §4.4 | `Chapter04.Section04` | Symmetric indefinite systems |
| §4.5 | `Chapter04.Section05` | Block tridiagonal systems |
| §4.6 | `Chapter04.Section06` | Vandermonde systems: Algorithms 4.6.1, 4.6.2 |
| §4.7 | `Chapter04.Section07` | Classical methods for Toeplitz systems: Algorithms 4.7.1–4.7.3 |
| §4.8 | `Chapter04.Section08` | Circulant and discrete Poisson systems |
| §5.1 | `Chapter05.Section01` | Householder and Givens transformations |
| §5.2 | `Chapter05.Section02` | The QR factorization |
| §5.3 | `Chapter05.Section03` | The full-rank least-squares problem |
| §5.4 | `Chapter05.Section04` | Other orthogonal factorizations |
| §5.5 | `Chapter05.Section05` | The rank-deficient least-squares problem |
| §5.6 | `Chapter05.Section06` | Square and underdetermined systems |
| §6.1 | `Chapter06.Section01` | Weighting and regularization: Theorem 6.1.1 |
| §6.2 | `Chapter06.Section02` | Constrained least squares: Algorithms 6.2.1, 6.2.2 |
| §6.3 | `Chapter06.Section03` | Total least squares: Theorem 6.3.1; Algorithm 6.3.1 |
| §6.4 | `Chapter06.Section04` | Subspace computations with the SVD |
| §6.5 | `Chapter06.Section05` | Updating matrix factorizations: Theorem 6.5.1 |
| §7.1 | `Chapter07.Section01` | Properties and decompositions |
| §7.2 | `Chapter07.Section02` | Perturbation Theory |
| §7.3 | `Chapter07.Section03` | Power Iterations: Theorem 7.3.1; Lemma 7.3.2 |
| §7.4 | `Chapter07.Section04` | The Hessenberg and Real Schur Forms |
| §7.5 | `Chapter07.Section05` | The practical QR algorithm |
| §7.6 | `Chapter07.Section06` | Invariant subspace computations: Algorithms 7.6.1–7.6.3 |
| §7.7 | `Chapter07.Section07` | The generalized eigenvalue problem |
| §7.8 | `Chapter07.Section08` | Hamiltonian and product eigenvalue problems |
| §7.9 | `Chapter07.Section09` | Pseudospectra |
| §8.1 | `Chapter08.Section01` | Properties and decompositions of symmetric matrices |
| §8.2 | `Chapter08.Section02` | Power iterations: Theorems 8.2.1, 8.2.2 |
| §8.3 | `Chapter08.Section03` | The symmetric QR algorithm |
| §8.4 | `Chapter08.Section04` | More methods for tridiagonal problems |
| §8.5 | `Chapter08.Section05` | Jacobi methods: Algorithms 8.5.1–8.5.3; equations (8.5.1)–(8.5.3) |
| §8.6 | `Chapter08.Section06` | Computing the SVD |
| §8.7 | `Chapter08.Section07` | Generalized eigenvalue problems with symmetry |
| §9.1 | `Chapter09.Section01` | Eigenvalue methods |
| §9.2 | `Chapter09.Section02` | Approximation methods |
| §9.3 | `Chapter09.Section03` | The matrix exponential: Algorithm 9.3.1 |
| §9.4 | `Chapter09.Section04` | The sign, square root, and log of a matrix: Theorem 9.4.1 |
| §10.1 | `Chapter10.Section01` | The symmetric Lanczos process |
| §10.2 | `Chapter10.Section02` | Lanczos, quadrature, and approximation |
| §10.3 | `Chapter10.Section03` | Practical Lanczos procedures: Theorem 10.3.2; Lemma 10.3.1 |
| §10.4 | `Chapter10.Section04` | Large sparse SVD frameworks: Algorithms 10.4.1, 10.4.2 |
| §10.5 | `Chapter10.Section05` | Krylov methods for unsymmetric problems |
| §10.6 | `Chapter10.Section06` | Jacobi–Davidson and related methods |
| §11.1 | `Chapter11.Section01` | Direct methods |
| §11.2 | `Chapter11.Section02` | The classical iterations: Theorems 11.2.1–11.2.4 |
| §11.3 | `Chapter11.Section03` | The conjugate gradient method |
| §11.4 | `Chapter11.Section04` | Other Krylov methods: Algorithm 11.4.2 |
| §11.5 | `Chapter11.Section05` | Preconditioning |
| §11.6 | `Chapter11.Section06` | The multigrid framework: Theorem 11.6.2; Lemma 11.6.1 |
| §12.1 | `Chapter12.Section01` | Linear systems with displacement structure |
| §12.2 | `Chapter12.Section02` | Structured-rank problems: Algorithms 12.2.1, 12.2.2 |
| §12.3 | `Chapter12.Section03` | Kronecker product computations |
| §12.4 | `Chapter12.Section04` | Tensor unfoldings and contractions: Theorem 12.4.1 |
| §12.5 | `Chapter12.Section05` | Tensor decompositions and iterations: Theorem 12.5.1 |

## Conventions

* The declarations of Chapter $N$ are in the namespace `GolubVanLoan.ChapterNN`, for example
  `GolubVanLoan.Chapter03`. Theorem, Lemma, Corollary and Algorithm $N.M.K$ are `theorem_N_M_K`,
  `lemma_N_M_K`, `corollary_N_M_K` and `algorithm_N_M_K`, with the suffixes of algorithm convention
  12 below; for example, Theorem 3.3.2 is `GolubVanLoan.Chapter03.theorem_3_3_2`. A numbered display
  $(N.M.K)$ that is a proposition is the theorem `equation_N_M_K`.
* A definition is named by its content, never `equation_N_M_K`. This holds for pure notation, such
  as `GolubVanLoan.Chapter01.fourierMatrix`, and for a definition in prose, such as the growth
  factor `GolubVanLoan.Chapter03.growthFactorStages`. The doc comment of the definition gives the
  display number.
* A numbered display that has the form of an algorithm, a loop that the source writes as a display
  and not as a numbered Algorithm, is a program named by its content, such as
  `GolubVanLoan.Chapter11.gaussSeidelSweep` or `GolubVanLoan.Chapter10.blockLanczos`. Its
  exact-semantics theorem is `equation_N_M_K`.
* Later chapters use the restatements of earlier chapters, not the backbone or Mathlib originals
  behind them. The backbone of Chapter 7 is also used by the surface library of Quarteroni, Sacco
  and Saleri, Chapter 5; the two surface libraries share the backbone and do not import each other.
* The source is real, $A \in \mathbb{R}^{m \times n}$ is `A : Matrix (Fin m) (Fin n) ℝ`, and its
  colon notation is 1-based. The library is 0-based on `Fin n`: the index $i$ of the source is
  `i - 1`, and each module states the translation where it matters. Complex statements are over `ℂ`:
  the FFT of §1.4 and the sine and cosine transforms through it, §2.1.7 and the complex SVD of
  §2.4.4, the decompositions of Chapter 7, §7.9, and parts of Chapter 9.
* The $k$-th largest singular value $\sigma_k$ of the source is `A.sortedSingularValues (k - 1)`;
  this is Mathlib's `LinearMap.singularValues` of `Matrix.toEuclideanLin A`. The largest and the
  smallest singular value $\sigma_{\max}(A)$ and $\sigma_{\min}(A)$ are
  `GolubVanLoan.Chapter02.sigmaMax` and `GolubVanLoan.Chapter02.sigmaMin` (§2.4), defined for every
  shape. The working form in the backbone is the column-indexed family `Matrix.colSingularValues`:
  for $n \le m$, $\sigma_{\max}(A)$ is the supremum and $\sigma_{\min}(A)$ is the infimum of
  `A.colSingularValues i` over the columns $i$
  (`GolubVanLoan.Chapter02.sigmaMax_eq_iSup_colSingularValues`,
  `GolubVanLoan.Chapter02.sigmaMin_eq_iInf_colSingularValues`).
* Shared helper programs of Chapter 1 (algorithm convention 13): the rounded entrywise vector
  operations `GolubVanLoan.Chapter01.vecAdd`, `GolubVanLoan.Chapter01.vecSub` and
  `GolubVanLoan.Chapter01.vecPointwiseMul` (§1.4, for any hook `rnd : K → M K`) and the matrix
  operations `GolubVanLoan.Chapter01.matrixAdd` and `GolubVanLoan.Chapter01.matrixSub` (§1.3), each
  with its theorem `_spec`. Every later chapter calls them and defines no variant.
* Shared helper programs of Chapter 5, §5.1: the Householder and Givens family, each with its
  theorem `_spec` and, where the source analyses it, its theorems `_rounds` and `_rounding`. Every
  later chapter calls them.
* `GolubVanLoan.Chapter05.houseOn rnd o x` is Algorithm 5.1.1 on the entries of $x \in \mathbb{R}^m$
  listed by `o : List (Fin m)`. Its pivot is the head of `o`, the $x(1)$ of the source, and the sum
  over the tail of `o` is computed by Algorithm 1.1.1. It returns $(v, \beta)$, with $v$ zero
  outside `o` and $1$ at the pivot. Algorithm 5.1.1 itself is
  `GolubVanLoan.Chapter05.algorithm_5_1_1 rnd x = houseOn rnd (List.finRange (k+1)) x`.
* `GolubVanLoan.Chapter05.householderApplyLeft rnd v β rows cols A` overwrites
  $A(\mathrm{rows}, \mathrm{cols})$ with $(I - \beta v v^T) A(\mathrm{rows}, \mathrm{cols})$,
  computed as $A - (\beta v)(v^T A)$, and `GolubVanLoan.Chapter05.householderApplyRight rnd v β rows
  cols A` overwrites it with $A(\mathrm{rows}, \mathrm{cols}) (I - \beta v v^T)$, computed as
  $A - (Av)(\beta v)^T$. Both act in place on the full matrix.
* `GolubVanLoan.Chapter05.givensRotation i k c s` is the matrix $G(i, k, \theta)$ of (5.1.7), which
  is `Matrix.planeRotation i k c (-s)`. `GolubVanLoan.Chapter05.algorithm_5_1_3` is the function
  `givens` of the source, which computes $(c, s)$. `GolubVanLoan.Chapter05.givensApplyLeft rnd i k c
  s cols A` overwrites $A([i, k], \mathrm{cols})$ with $G(i, k, \theta)^T A([i, k], \mathrm{cols})$,
  and `GolubVanLoan.Chapter05.givensApplyRight rnd i k c s rows A` overwrites
  $A(\mathrm{rows}, [i, k])$ with $A(\mathrm{rows}, [i, k]) G(i, k, \theta)$.
* Householder data are lists `List ((Fin m → ℝ) × ℝ)`;
  `GolubVanLoan.Chapter05.householderProduct data` is the product $Q_1 \cdots Q_r$, and
  `GolubVanLoan.Chapter05.forwardAccumulation rnd data` and
  `GolubVanLoan.Chapter05.backwardAccumulation rnd data` (§5.1.6) are programs that compute it in
  exact arithmetic.
* In §9.4 the Newton iterations (9.4.1), (9.4.7) and (9.4.11) are not programs. They are the exact
  recursions `Matrix.newtonSignIterate`, `Matrix.newtonSqrtIterate` and `Matrix.newtonPolarIterate`
  of the backbone, with no rounding hook and no fuel, because the source uses them as mathematical
  sequences whose limits and rates it analyses, not as algorithms with a stopping rule. Their
  content is stated by `GolubVanLoan.Chapter09.newtonSign_isUnit` and
  `GolubVanLoan.Chapter09.newtonSign_tendsto` ((9.4.1)–(9.4.4)),
  `GolubVanLoan.Chapter09.newtonSqrt_tendsto` ((9.4.7)), and
  `GolubVanLoan.Chapter09.equation_9_4_12` and `GolubVanLoan.Chapter09.newtonPolar_tendsto`
  ((9.4.11)–(9.4.12)). No declaration is named `equation_9_4_1`, `equation_9_4_7` or
  `equation_9_4_11`.

**Algorithm conventions.** The following numbered conventions govern every program of the library.
The same list, with the same numbers, heads the module doc comment of
`Numlib.FloatingPoint.Program`.

1. **What is rounded.** Exact, that is, not passed through `rnd`: unary negation, $|\cdot|$,
   $\operatorname{sign}$ and copysign, copying, and comparisons. A comparison stores nothing and
   acts on the values that the program holds. Rounded, with exactly one `rnd` after each: the result
   of every $+$, $-$, $\times$, $/$ and $\sqrt{\cdot}$, where $\sqrt{\cdot}$ is `Real.sqrt` followed
   by one `rnd`. This includes arithmetic whose only use is a test, such as
   $\mathrm{fl}(\mathrm{tol} \cdot \mathrm{fl}(|h_{ii}| + |h_{i-1,i-1}|))$, $\delta \leftarrow
   \mathrm{fl}(\mathrm{tol} \cdot \|A\|_F)$, or the $\mathrm{fl}(1 - \mathrm{fl}(\alpha^2))$ of a
   positivity check. IEEE negation, absolute value and copysign are exact, and the relational model
   does not know that $x$ rounds to $x$, so rounding them would only add spurious error. The value
   of an elementary function ($\exp$, $\cos$, $\sin$, for example the root $\exp(-2\pi i/n)$ of the
   FFT) is one rounded result. Multiplication by $\pm 1$ and $\pm i$ is exact: it is a sign change
   or a swap of the real and the imaginary part.
2. A division by a unit diagonal inside a factorization is not performed.
3. Loops are `List.foldlM` over `List.finRange n` or over an explicit list of indices, never
   `for … in [a:b]`. A `while` loop is `List.foldlM` over `List.range fuel` with a field
   `done : Bool` in the state: once `done` holds, a step is the identity. The specification states
   what holds after `min fuel stop` passes, where `stop` is the exit index of the source. The fuel
   parameter is named `fuel : ℕ` and is the last explicit argument. Structural or well-founded
   recursion is used only for algorithms that are recursive in the source: Strassen's method, the
   FFT, the Haar transform, recursive block LU, Cholesky and QR, and `LUdisp`.
4. A program that branches on a real test is a `noncomputable def`, through `Real.decidableEq` and
   `Real.decidableLT`.
5. A step that the source delegates to an algorithm of a later chapter, such as "compute the SVD" or
   "find $\lambda_+$", is a monadic function parameter, and the specification assumes the
   specification of that parameter. A step that the source delegates to an earlier chapter calls the
   program of that chapter.
6. `FloatingPoint.RoundingModel.IsIdempotent` is assumed only when the stated constant needs it. A
   program whose accumulation starts from $0$ and whose bound is the $\gamma_n$ of the source,
   through a relation that starts from the unrounded first term (`FloatingPoint.RoundsDot`,
   `FloatingPoint.RoundsSum`), needs it; this is the mismatch of $0 + p$ described in
   `Numlib.FloatingPoint.Program`. A relation that itself absorbs the rounding of $0 + p$, such as
   `FloatingPoint.RoundsForwardSubstDot`, needs nothing.
7. The monad variable is `M`, as in `{M : Type → Type} [Monad M]`, never `m`, which is the row count
   of the source.
8. Breakdown is not checked in the program: $x / 0 = 0$, and the specification carries the
   hypotheses, such as nonzero pivots or nonsingular leading submatrices. Overwrites are updates of
   the state (`Function.update`, `Matrix.updateRow`). A state with several outputs is a structure or
   a tuple.
9. The hypotheses of a rounding theorem are about the inputs and about the values that the program
   returns, never about intermediate values that a run overwrites, such as a computed pivot $t_j$
   that is then replaced by $\sqrt{t_j}$, or a packed factor that the program does not return. A
   composite computation, such as a factorization followed by a solve, is stated nested, one program
   for each quantifier: `∀ F ∈ (alg₁ fp.round A).run, hyp F → ∀ x ∈ (alg₂ fp.round F b).run, concl`.
   This is the form of `GolubVanLoan.Chapter03.theorem_3_3_2`.
10. **Submatrices are lists of indices.** A block $A(j{:}m, k{:}n)$ of the source is the full matrix
    together with the filtered lists of its rows and columns, `rows : List (Fin m)` and
    `cols : List (Fin n)`, never a copy typed by a loop-dependent `Fin (m - j)`. A subvector
    $x(j{:}m)$ is the full vector with its list of active indices. Helpers act in place on the full
    matrix over such lists (`GolubVanLoan.Chapter05.houseOn`,
    `GolubVanLoan.Chapter05.householderApplyLeft`, `GolubVanLoan.Chapter05.givensApplyLeft` and
    their right-hand versions), and an algorithm of the source on vectors is its helper at the full
    list: `algorithm_5_1_1 rnd x = houseOn rnd (List.finRange (k+1)) x` holds by `rfl`. The
    relations of the backbone read such a block through the subtype `{i // i ∈ rows}` or through a
    pivot `i : ι` of the full index type. The recursive algorithms of convention 3 (Strassen's
    method, the FFT, the Haar transform) do pass typed halves `Fin (2^t)`, because they recurse on
    the size, not over a shrinking active block.
11. **Exact specifications come from bridges.** When a bridge "every run satisfies the backbone
    relation $R$" exists, the exact specification `_spec` is its instance at
    `FloatingPoint.RoundingModel.exact`, through `FloatingPoint.RoundingModel.round_exact` and the
    exact characterization of $R$ (for example `FloatingPoint.roundsLU_exact_iff` or
    `FloatingPoint.mem_run_dotAccum_exact_iff`), not a second proof at `Id`.
12. **Suffixes.** `algorithm_N_M_K` is the program and `_spec` its exact semantics. `_rounds` states
    that every run satisfies a relation `FloatingPoint.RoundsX …` of the backbone; this is the
    bridge. `_mem_run` characterizes the set of runs by an equivalence when no relation of the
    backbone exists. `_rounding` is the error bound of the source for every run. A theorem that
    proves the bound through a bridge depends on the `_rounds` theorem.
13. **One family of helpers, one type of reflector data.** Updates that several algorithms share are
    defined once, in Chapter 5 for this library, in symmetric pairs `…Left` and `…Right` on lists of
    indices. Householder data are `List ((Fin m → ℝ) × ℝ)`: pairs $(v, \beta)$ in the order of
    application, with $v$ of full length and zero outside its active rows, carrying the $\beta$ that
    the program returned. A reflector is never rebuilt as $\beta = 2/(v^Tv)$ from a stored $v$: when
    `house` returns $\beta = 0$, the rebuilt $I - 2e_1e_1^T$ is not the identity that it applied.
14. **Symmetric pairs are separate declarations** (`…Left` and `…Right`, `…_col` and `…_row`,
    forward and backward accumulation), each with its own `_spec`. A consumer depends on the half
    that it uses.

## Deviations from the source

The entries are grouped by chapter. Each entry names the item, the kind of deviation, what the
source prints and what the library states instead, and the declaration with the full account.

**Chapter 1: Matrix multiplication**

* **Algorithm 1.1.6** (reading). The program retains the rounding order of Algorithm 1.1.5 by
  accumulating the dot product onto $C(i,j)$. See `GolubVanLoan.Chapter01.algorithm_1_1_6`.
* **Table 1.2.1** (reading). The book includes rectangular matrices. The theorem uses square
  matrices. See `GolubVanLoan.Chapter01.table_1_2_1`.
* **Algorithm 1.2.1** (generalization). The source takes $C$ upper triangular; the specification
  holds for every $C$. See `GolubVanLoan.Chapter01.algorithm_1_2_1_spec`.
* **Equations (1.2.1) and (1.2.2)** (reading). The storage accessors are total and the algorithms
  use only their printed domains. See `GolubVanLoan.Chapter01.bandEntry` and
  `GolubVanLoan.Chapter01.packedIndex`.
* **§1.2.11, the downshift** (typo). The source's formula $\mathcal{D}_n = I_n(v,:)$ with
  $v = [(2{:}n)\ 1]$ gives the upshift $\mathcal{D}_n^T$; the definition follows the displayed
  $\mathcal{D}_4$ and the name. See `GolubVanLoan.Chapter01.downshift`.
* **Equation (1.3.6)** (typo). The source gives $X \in \mathbb{R}^{n_1 \times m_2}$; the size is
  $X \in \mathbb{R}^{n_2 \times n_1}$, the only size for which $CXB^T$ is defined. See
  `GolubVanLoan.Chapter01.equation_1_3_6`.
* **§1.3.10, blocks of a symplectic matrix** (generalization). The source derives the block
  conditions from $S^T J S = J$; the statement is an equivalence. See
  `GolubVanLoan.Chapter01.symplectic_blocks`.
* **Algorithm 1.3.1** (generalization). The source assumes $n_{\min} = 2^d$ with $d \le q$; the
  specification holds for every $d$. See `GolubVanLoan.Chapter01.algorithm_1_3_1_spec`.
* **Equations (1.4.3), (1.4.4), and (1.4.8)** (reading). At $m=0$, the sine transform is empty
  and the cosine transform is the identity on one entry. See `GolubVanLoan.Chapter01.dstTransform`,
  `GolubVanLoan.Chapter01.dctTransform` and `GolubVanLoan.Chapter01.equation_1_4_8`.
* **Algorithm 1.4.1, twiddle factors** (reading). The program computes successive powers by
  repeated rounded multiplication. See `GolubVanLoan.Chapter01.fftTwiddles`.
* **Algorithms 1.4.2 and 1.4.3** (reading). The programs choose the radix-2 FFT, so $m$ is a power
  of two. The rounded outputs are complex. See `GolubVanLoan.Chapter01.algorithm_1_4_2` and
  `GolubVanLoan.Chapter01.algorithm_1_4_3`.
* **Algorithm 1.4.4** (typo). The source writes $y(1{:}2{:}m)$ and $y(2{:}2{:}m)$ for $y(1{:}2{:}n)$
  and $y(2{:}2{:}n)$. See `GolubVanLoan.Chapter01.algorithm_1_4_4`.
* **§1.6.8 and Equation (1.6.16)** (generalization). The four-block displays extend to arbitrary
  positive order as in Problem P1.6.6. See `GolubVanLoan.Chapter01.cannonA`,
  `GolubVanLoan.Chapter01.cannonB`, `GolubVanLoan.Chapter01.equation_1_6_16` and
  `GolubVanLoan.Chapter01.cannon_succ`.

**Chapter 2: Matrix analysis**

* **Equations (2.1.1) and (2.1.2)** (generalization). The identities also hold for singular
  matrices with Mathlib's inverse convention. See `GolubVanLoan.Chapter02.equation_2_1_1` and
  `GolubVanLoan.Chapter02.equation_2_1_2`.
* **Note after Theorem 2.1.1** (generalization). The orthogonal complement identity allows
  arbitrary complementary column selections. See
  `GolubVanLoan.Chapter02.orthogonal_range_submatrix_eq`.
* **§2.1.7, similarity** (generalization). Equality of the characteristic polynomials records
  the eigenvalues with multiplicity. See `GolubVanLoan.Chapter02.isSimilar_spectrum_eq`.
* **§2.2.1, vector norm** (generalization). The axioms apply to every real vector space.
  See `GolubVanLoan.Chapter02.IsVectorNorm`.
* **Equation (2.2.1) and following special cases** (reading). The infinity norm of the empty
  vector is zero. See `GolubVanLoan.Chapter02.equation_2_2_1`.
* **§2.2.4, convergence** (generalization). The equivalence holds on every finite-dimensional
  real normed space. See `GolubVanLoan.Chapter02.tendsto_iff_of_isVectorNorm`.
* **Equation (2.3.2), attainment** (reading). The unit-vector conclusion requires positive
  input dimension. See `GolubVanLoan.Chapter02.equation_2_3_2`.
* **Equations (2.3.5)–(2.3.6)** (generalization and reading). The target may carry a seminorm.
  Attainment requires positive input dimension. See `GolubVanLoan.Chapter02.equation_2_3_5`
  and `GolubVanLoan.Chapter02.equation_2_3_6`.
* **Equations (2.3.8)–(2.3.12)** (reading). Empty maxima and division by zero evaluate to zero.
  See `GolubVanLoan.Chapter02.equation_2_3_8`, `GolubVanLoan.Chapter02.equation_2_3_9`,
  `GolubVanLoan.Chapter02.equation_2_3_10`, `GolubVanLoan.Chapter02.equation_2_3_11`, and
  `GolubVanLoan.Chapter02.equation_2_3_12`.
* **Theorem 2.3.1 and its spectral formula** (reading). The column count is positive. See
  `GolubVanLoan.Chapter02.theorem_2_3_1` and `GolubVanLoan.Chapter02.l2_opNorm_eq_sqrt_lambdaMax`.
* **Proof of Theorem 2.3.4** (correction). The proof factors out $A$ on the left to retain the
  stated bound in terms of $\|A^{-1}E\|_p$. See `GolubVanLoan.Chapter02.theorem_2_3_4`.
* **§2.4.1 and Corollaries 2.4.3–2.4.4** (reading). The extremal singular values are zero
  when the singular-value list is empty. See `GolubVanLoan.Chapter02.sigmaMax`,
  `GolubVanLoan.Chapter02.sigmaMin`, `GolubVanLoan.Chapter02.corollary_2_4_3`, and
  `GolubVanLoan.Chapter02.corollary_2_4_4`.
* **Proof of Corollary 2.4.4** (correction). The lower bound on $\|Ax\|_2$ used in the proof
  can fail for wide matrices. See `GolubVanLoan.Chapter02.corollary_2_4_4`.
* **Corollary 2.4.5** (reading). The source does not define $\sigma_{\min}$ of an $m \times 0$
  matrix; the corollary assumes $n \ge 1$. See `GolubVanLoan.Chapter02.corollary_2_4_5`.
* **Remark after Theorem 2.4.8** (reading). The statement that $\sigma_{\min}(A)$ is the distance to
  the rank-deficient matrices assumes $m, n \ge 1$. See
  `GolubVanLoan.Chapter02.sigmaMin_eq_dist_rankDeficient`.
* **Frobenius-norm remark after Theorem 2.4.8** (generalization). The theorem also gives the
  exact error of the truncation. See `GolubVanLoan.Chapter02.svdTruncation_isLeast_frobenius`.
* **Section 2.5.1, projection onto a line** (reading). The quotient requires $v \ne 0$.
  See `GolubVanLoan.Chapter02.isOrthogonalProjection_vecMulVec`.
* **Equation (2.5.1) and the bounds in §2.5.3** (generalization). The distance, its matrix
  formula and the bounds $0 \le \operatorname{dist} \le 1$ apply to unequal dimensions too.
  See `GolubVanLoan.Chapter02.subspaceDist`,
  `GolubVanLoan.Chapter02.subspaceDist_eq_lpOpNorm_sub` and
  `GolubVanLoan.Chapter02.subspaceDist_mem_Icc`.
* **Section 2.5.3, $\operatorname{dist}(S_1, S_2) = 0 \Rightarrow S_1 = S_2$** (generalization). The
  source states an implication. The theorem is an equivalence and needs no hypothesis on the
  dimensions. See `GolubVanLoan.Chapter02.subspaceDist_eq_zero`.
* **Section 2.5.3, $\operatorname{dist}(S_1, S_2) = 1 \Rightarrow S_1 \cap S_2^\perp \neq \{0\}$**
  (generalization). The source states an implication. The theorem is an equivalence. See
  `GolubVanLoan.Chapter02.subspaceDist_eq_one`.
* **Theorem 2.5.2** (typo). The right-hand side stacks the rectangular diagonal matrices
  $C_0$ and $S_0$, labeled $C$ and $S$ in the source display.
  See `GolubVanLoan.Chapter02.theorem_2_5_2`.
* **Theorem 2.5.3** (generalization). The decomposition also holds when $m_1 < m_2$.
  See `GolubVanLoan.Chapter02.theorem_2_5_3`.
* **Equation (2.6.1)** (generalization). An orthogonal diagonalization of the two-sided form
  suffices, with signed and unordered diagonal entries. See `GolubVanLoan.Chapter02.equation_2_6_1`.
* **Equations (2.6.2) and (2.6.4)** (reading). For induced $p$-norms, the bounds use an explicit
  smallness condition, nonzero denominators and a finite factor in place of the asymptotic
  remainder. See `GolubVanLoan.Chapter02.equation_2_6_2` and
  `GolubVanLoan.Chapter02.equation_2_6_4`.
* **Equations (2.6.3) and (2.6.7), Lemma 2.6.1 and Theorem 2.6.2** (reading). The surface
  statements specialize the norm to an induced $p$-norm. See `GolubVanLoan.Chapter02.kappa`,
  `GolubVanLoan.Chapter02.equation_2_6_7`, `GolubVanLoan.Chapter02.lemma_2_6_1` and
  `GolubVanLoan.Chapter02.theorem_2_6_2`.
* **Equations (2.6.5)–(2.6.7)** (reading). The ratio and inverse characterizations are stated
  for nonsingular $A$. The minimum and normalized limit also require $n > 0$, and the limit is
  from positive radii. See `GolubVanLoan.Chapter02.equation_2_6_5`,
  `GolubVanLoan.Chapter02.equation_2_6_6` and `GolubVanLoan.Chapter02.equation_2_6_7`.
* **Equation (2.6.8) and the Skeel condition number in §2.6.5** (reading). The real-valued
  condition numbers use the totalized matrix inverse, giving $0$ for singular matrices.
  Equation (2.6.8) also includes $n=0$ with $1/0=0$.
  See `GolubVanLoan.Chapter02.equation_2_6_8` and
  `GolubVanLoan.Chapter02.skeelCond_eq_and_le_condNumberLp`.
* **Lemma 2.6.1** (reading). The source carries the nonsingularity of $A$ through the convention
  $\kappa(A) = \infty$. The lemma has the explicit hypothesis that $A$ is nonsingular. See
  `GolubVanLoan.Chapter02.lemma_2_6_1`.
* **Equation (2.6.11)** (generalization). The identity requires only the two system equations
  and nonsingularity of $A$. See `GolubVanLoan.Chapter02.equation_2_6_11`.
* **Theorem 2.6.3** (typo). The source prints the hypothesis as $\delta \kappa_\infty(A) = r < 1$,
  with $\delta$ for $\epsilon$. See `GolubVanLoan.Chapter02.theorem_2_6_3`.
* **Equation (2.6.13)** (reading). A zero denominator contributes $0$ when the row residual is
  zero and precludes every finite feasible perturbation size otherwise.
  See `GolubVanLoan.Chapter02.equation_2_6_13`.
* **Equation (2.6.13)** (generalization). The theorem characterizes feasibility for every
  perturbation size $\omega \ge 0$, in addition to identifying the minimum.
  See `GolubVanLoan.Chapter02.equation_2_6_13`.
* **Section 2.7.2, rounding to nearest** (generalization). The error bound includes both tie
  choices and every real value at least as close as any normalized double.
  See `GolubVanLoan.Chapter02.ieeeDouble_round_nearest`.
* **Equations (2.7.4) and (2.7.6)** (reading). The concrete rounding and arithmetic use
  unbounded exponents. Equation (2.7.6) takes its operands from the normalized set with zero.
  See `GolubVanLoan.Chapter02.equation_2_7_4_system` and `GolubVanLoan.Chapter02.equation_2_7_6`.
* **Equation (2.7.5)** (reading). The gap above $1$ requires an exponent range containing the
  binade of $1$ and at least two digits. See `GolubVanLoan.Chapter02.equation_2_7_5`.
* **Equation (2.7.6)** (generalization). The arithmetic bound applies to every real binary
  operation. See `GolubVanLoan.Chapter02.equation_2_7_6`.
* **Equation (2.7.12)** (reading and generalization). The dot product bound has explicit
  coefficient $\gamma_n$ when $nu<1$. A second bound allows inexact addition of the first
  product to zero and uses $\gamma_{n+1}$. See `GolubVanLoan.Chapter02.equation_2_7_12`.
* **Equations (2.7.17) and (2.7.18)** (reading). The remainder is an explicit quadratic term
  in the unit roundoff. See `GolubVanLoan.Chapter02.equation_2_7_17` and
  `GolubVanLoan.Chapter02.equation_2_7_18`.
* **Equations (2.7.19) and (2.7.20), and the nonnegative product bound in §2.7.10** (reading).
  The coefficient is $\gamma_r$ when $ru<1$, where $r$ is the inner dimension. The norm and
  nonnegative product bounds use dot product multiplication.
  See `GolubVanLoan.Chapter02.equation_2_7_19`, `GolubVanLoan.Chapter02.equation_2_7_19_saxpy`,
  `GolubVanLoan.Chapter02.equation_2_7_19_outer`, `GolubVanLoan.Chapter02.equation_2_7_20` and
  `GolubVanLoan.Chapter02.abs_sub_le_gamma_mul_abs_of_nonneg`.
* **Section 2.7.9, triangular product** (reading). The backward error bounds use $\gamma_2$
  when $2u<1$. See `GolubVanLoan.Chapter02.triangular_mul_two_backward`.
* **Equation (2.7.21)** (reading). The result states the storage bounds. The perturbed
  solution equation appears as a hypothesis in the next theorem.
  See `GolubVanLoan.Chapter02.equation_2_7_21` and `GolubVanLoan.Chapter02.equation_2_7_22`.
* **Equation (2.7.22)** (generalization). The estimate holds for all perturbations satisfying
  the norm bounds. See `GolubVanLoan.Chapter02.equation_2_7_22`.

**Chapter 3: General linear systems**

* **Algorithms 3.1.1–3.1.4** (reading). The programs specify the rounding order and
  use totalized division on arbitrary inputs. The exact solve specifications require
  nonsingular triangular input. See `GolubVanLoan.Chapter03.algorithm_3_1_1`,
  `GolubVanLoan.Chapter03.algorithm_3_1_2`, `GolubVanLoan.Chapter03.algorithm_3_1_3` and
  `GolubVanLoan.Chapter03.algorithm_3_1_4`.
* **Equations (3.1.1)–(3.1.2) and §3.1.3** (reading). The explicit coefficient
  $\gamma_n$ is used under $u<1$ and $nu<1$. See `GolubVanLoan.Chapter03.equation_3_1_1`,
  `GolubVanLoan.Chapter03.equation_3_1_2`, `GolubVanLoan.Chapter03.algorithm_3_1_3_rounding` and
  `GolubVanLoan.Chapter03.algorithm_3_1_4_rounding`.
* **Equation (3.1.4) and Problem P3.1.3** (reading). The block program uses labelled rows,
  a column-oriented solve on each block and rounded running differences for the block
  update. Its specification uses contiguous blocks and nonzero diagonal entries.
  See `GolubVanLoan.Chapter03.forwardSubstColOn`, `GolubVanLoan.Chapter03.blockForwardElim`
  and `GolubVanLoan.Chapter03.equation_3_1_4`.
* **§3.1.6, wide lower triangular systems** (typo and reading). The leading part of
  the solution is the vector slice $x(1{:}m)$. The solve assumes a nonzero diagonal
  in the leading block and includes the square case.
  See `GolubVanLoan.Chapter03.nonsquareLower_wide`.
* **§3.1.7, unit triangular solve** (reading). The column program omits division by
  the unit diagonal. See `GolubVanLoan.Chapter03.unitForwardSubstColOn`.
* **§3.1.7, inverse triangularity** (reading). The statement uses the totalized inverse
  and includes singular matrices. See `GolubVanLoan.Chapter03.triangular_inv`.
* **Equation (3.2.1)** (generalization). The two solve equations imply $Ax=b$ for
  any factors with $A=LU$. See `GolubVanLoan.Chapter03.equation_3_2_1`.
* **§3.2.1 and (3.2.2)** (reading). The Gauss vector is zero at a zero pivot by totalized
  division. The rank-one matrix formula accepts any $\tau$, with the structured case
  specified by a separate predicate. See `GolubVanLoan.Chapter03.gaussVector` and
  `GolubVanLoan.Chapter03.gaussTransformation`.
* **§3.2.2, outer product update** (generalization). The multiplication identity holds
  for arbitrary $\tau$. The rounded program specifies the order of operations.
  See `GolubVanLoan.Chapter03.gaussTransformation_mul` and
  `GolubVanLoan.Chapter03.gaussUpdate`.
* **§3.2.3, roundoff** (reading). The Gauss vector and update use totalized quotients.
  The update bound uses an explicit $\gamma_3$ coefficient when $3u<1$.
  See `GolubVanLoan.Chapter03.gaussVector_rounding` and
  `GolubVanLoan.Chapter03.gaussUpdate_rounding`.
* **Equations (3.2.3), (3.2.5) and (3.2.7)** (reading). A zero pivot leaves the stage
  unchanged and contributes zero multipliers. The additional terminal step has no
  update. See `GolubVanLoan.Chapter03.gaussStage`, `GolubVanLoan.Chapter03.equation_3_2_3`,
  `GolubVanLoan.Chapter03.pivot`, `GolubVanLoan.Chapter03.equation_3_2_5` and
  `GolubVanLoan.Chapter03.equation_3_2_7`.
* **Theorem 3.2.1, determinant** (generalization). The product of diagonal entries
  gives the determinant for any LU factorization, including singular matrices.
  See `GolubVanLoan.Chapter03.theorem_3_2_1_det`.
* **§3.2.5, the inverse of a Gauss transformation** (generalization). The source states
  $M_k^{-1} = I_n + \tau e_k^T$ for a Gauss transformation. The theorem needs only $\tau_k = 0$. See
  `GolubVanLoan.Chapter03.gaussTransformation_inv`.
* **Algorithms 3.2.1 and 3.2.2** (reading). The rounded programs give explicit scalar
  evaluation orders and totalized quotients. The gaxpy specification identifies the
  exact output with the totalized Doolittle formulas before assuming nonzero pivots.
  See `GolubVanLoan.Chapter03.outerProductStep`, `GolubVanLoan.Chapter03.algorithm_3_2_1`,
  `GolubVanLoan.Chapter03.gaxpyColumn`, `GolubVanLoan.Chapter03.algorithm_3_2_2` and
  `GolubVanLoan.Chapter03.algorithm_3_2_2_spec`.
* **Equation (3.2.8)** (reading). The rectangular program specifies scalar rounding
  and includes square matrices. The exact specification requires nonsingular
  leading blocks through the column count. See `GolubVanLoan.Chapter03.tallOuterProductLU`
  and `GolubVanLoan.Chapter03.equation_3_2_8`.
* **Equation (3.2.9) and the assembled block LU** (generalization). The product
  identities use only the indicated block factors and solves. Nonsingularity is
  used for the inverse form of the Schur complement. See
  `GolubVanLoan.Chapter03.equation_3_2_9` and `GolubVanLoan.Chapter03.blockLU_of_schur`.
* **Algorithm 3.2.3** (correction). The source assumes that $A$ has an LU factorization. This does
  not exclude a zero pivot, for example $A = \begin{bmatrix} 0 & 1 \\ 0 & 1 \end{bmatrix}$, and the
  algorithm then fails. The specification assumes that $A(1{:}k, 1{:}k)$ is nonsingular for
  $k = 1, \dots, n-1$. See `GolubVanLoan.Chapter03.algorithm_3_2_3_spec`.
* **Algorithm 3.2.4** (correction). The same hypothesis replaces "$A$ has an LU factorization". See
  `GolubVanLoan.Chapter03.algorithm_3_2_4_spec`.
* **Algorithms 3.2.3 and 3.2.4, evaluation order** (reading). Both programs
  use unit triangular solves without diagonal divisions, and rounded running differences
  for the block products. The nonrecursive program uses equal block sizes.
  See `GolubVanLoan.Chapter03.algorithm_3_2_3` and `GolubVanLoan.Chapter03.algorithm_3_2_4`.
* **Theorems 3.3.1 and 3.3.2** (generalization). The source assumes that the entries of $A$ are
  floating point numbers. The theorems hold for every real matrix $A$. See
  `GolubVanLoan.Chapter03.theorem_3_3_1` and `GolubVanLoan.Chapter03.theorem_3_3_2`.
* **Theorem 3.3.1** (generalization). The source assumes that no zero pivots occur. Only the pivots
  that are used as divisors, $\hat u_{jj}$ for $j < n$, must be nonzero. See
  `GolubVanLoan.Chapter03.theorem_3_3_1`.
* **Theorems 3.3.1 and 3.3.2** (reading). The error estimates use explicit $\gamma_n$ and
  $\gamma_{3n}$ bounds with smallness hypotheses. The solves require every diagonal pivot
  of $\hat U$ to be nonzero. See `GolubVanLoan.Chapter03.theorem_3_3_1`,
  `GolubVanLoan.Chapter03.theorem_3_3_1_gaxpy`, `GolubVanLoan.Chapter03.theorem_3_3_2` and
  `GolubVanLoan.Chapter03.theorem_3_3_2_column`.
* **Reading.** The pivot encoding in §3.4.1 accepts full-length vectors with identity swaps in
  unused positions. The algorithms take first maximizing rows for partial pivoting, and include the
  final identity step in the outer-product loops. See `GolubVanLoan.Chapter03.pivPerm`,
  `GolubVanLoan.Chapter03.applyPiv`, `GolubVanLoan.Chapter03.applyPivRev`,
  `GolubVanLoan.Chapter03.partialPivotStage`, `GolubVanLoan.Chapter03.equation_3_4_2`,
  `GolubVanLoan.Chapter03.algorithm_3_4_1` and `GolubVanLoan.Chapter03.algorithm_3_4_3`.
* **Reading.** The gaxpy variant returns separate factors and uses rounded running differences for
  the substitution and trailing update. See `GolubVanLoan.Chapter03.algorithm_3_4_2`.
* **Reading.** The triangular solves are totalized at zero pivots. The column permutation for
  complete pivoting follows Step 3, applying $Q^T$ where the following sentence prints $Q$. The
  matrix-power solve also accepts exponent zero. See `GolubVanLoan.Chapter03.solvePLU`,
  `GolubVanLoan.Chapter03.solveGEPP`, `GolubVanLoan.Chapter03.solvePLUQ`,
  `GolubVanLoan.Chapter03.solveGECP`, `GolubVanLoan.Chapter03.solveMultipleRHS`,
  `GolubVanLoan.Chapter03.solvePowerSystem` and `GolubVanLoan.Chapter03.equation_3_4_13`.
* **Reading.** The rounding bridges use nonzero returned pivots before the last and the multiplier
  bound $1+u$. The backward-error theorems use explicit $\gamma_{3n}$ bounds with $3nu<1$ and
  nonzero pivots. See `GolubVanLoan.Chapter03.algorithm_3_4_1_rounds`,
  `GolubVanLoan.Chapter03.algorithm_3_4_2_rounds`, `GolubVanLoan.Chapter03.equation_3_4_6`,
  `GolubVanLoan.Chapter03.equation_3_4_6_gaxpy`, `GolubVanLoan.Chapter03.equation_3_4_7` and
  `GolubVanLoan.Chapter03.equation_3_4_7_gaxpy`.
* **Reading.** Equation (3.4.8) uses computed stages. The norm-scaled Lean growth factor uses exact
  stages, and both backward-error versions of (3.4.9) assume a bound on the computed upper factor.
  See `GolubVanLoan.Chapter03.growthFactorStages`, `GolubVanLoan.Chapter03.growthFactorStages_eq`,
  `GolubVanLoan.Chapter03.growthFactor_le_two_pow`, `GolubVanLoan.Chapter03.equation_3_4_9` and
  `GolubVanLoan.Chapter03.equation_3_4_9_gaxpy`.
* **Correction.** The exact growth-example equality $2^{n-1}$ uses the maximum input entry modulus
  in the denominator. With the norm denominator of (3.4.8), it is $2^{n-1}/n$. See
  `GolubVanLoan.Chapter03.growthExample_noInterchange`.
* **Reading.** The complete-pivoting factorization may still swap entries in a zero trailing block.
  Its rank theorem describes the block structure of the factors of the full run. See
  `GolubVanLoan.Chapter03.completePivoting_rank_factorization`.
* **Correction.** The rook loop recomputes $\tau=|a_{\mu\lambda}|$ after a candidate change, which
  the printed loop omits. It uses a sufficient explicit fuel bound. See
  `GolubVanLoan.Chapter03.rookPivotSearch`, `GolubVanLoan.Chapter03.rookPivotSearch_spec`,
  `GolubVanLoan.Chapter03.rookPivot` and `GolubVanLoan.Chapter03.isRookPivot_rookPivot`.
* **Generalization.** The underdetermined factorization also permits square matrices and asserts
  existence. The solve uses invertible $U_1$ and does not require its triangularity. See
  `GolubVanLoan.Chapter03.equation_3_4_11` and `GolubVanLoan.Chapter03.underdetermined_solve`.
* **(3.4.10)** (correction). The source prints the bound with $k$ in place of $k + 1$, which is
  false for $k = 1$ when $A^{(k)}$ is the matrix after $k$ steps. See
  `GolubVanLoan.Chapter03.equation_3_4_10`.
* **Heuristic I** (reading). The source states $\|b - A\hat x\|_\infty \approx u \|A\|_\infty \|\hat
  x\|_\infty$. The theorem states a rigorous bound under the hypotheses of (3.4.9). See
  `GolubVanLoan.Chapter03.heuristic_I`.
* **(3.5.2)** (reading). The source states $\|\hat x - x\|_\infty / \|x\|_\infty \approx u
  \kappa_\infty(A)$. The theorem states the bound $2\varepsilon\kappa_\infty(A) / (1 -
  \varepsilon\kappa_\infty(A))$ for a backward error of size $\varepsilon$. See
  `GolubVanLoan.Chapter03.equation_3_5_2`.
* **(3.5.3)** (generalization). The source takes $D_1$ and $D_2$ diagonal. The theorem holds for any
  nonsingular $D_1$, $D_2$. See `GolubVanLoan.Chapter03.equation_3_5_3`.
* **(3.5.3)** (reading). The exact scaled error identity uses totalized division.
  See `GolubVanLoan.Chapter03.equation_3_5_3`.
* **§3.5.2, equilibration** (reading). The interval test takes a real parameter in place
  of the machine radix. See `GolubVanLoan.Chapter03.IsEquilibrated`.
* **(3.5.4)–(3.5.5)** (reading). The residual is computed by rounded row dot products.
  The mixed-precision loop takes two rounding operations and a pass count. Its
  correctness statement treats the case where both operations are exact.
  See `GolubVanLoan.Chapter03.iterativeImprovementStep`,
  `GolubVanLoan.Chapter03.mixedPrecisionImprovement` and
  `GolubVanLoan.Chapter03.equation_3_5_5`.
* **§3.5.4, inverse-norm estimate** (generalization). The norm and condition bounds
  allow $d=0$ by using the product form and totalized division.
  See `GolubVanLoan.Chapter03.condEstimate_lowerBound`.
* **(3.5.6) and §3.5.4, norm computation** (reading). The right-hand-side choice is a
  function of the step and running vector. The rounded matrix norm uses a fixed
  summation order. See `GolubVanLoan.Chapter03.backSubstChosenRHS` and
  `GolubVanLoan.Chapter03.linftyNormRounded`.
* **Algorithm 3.5.1, rounding** (reading). Look-ahead scores accumulate from the
  absolute candidate solution entry. The program accepts an explicit rounding operation.
  See `GolubVanLoan.Chapter03.algorithm_3_5_1`.
* **§3.5.4, LU condition estimation** (reading). The lower triangular estimator is
  invoked on reversed indices and passes its normalized vector to the next solve.
  The common scale cancels in the exact norm ratio.
  See `GolubVanLoan.Chapter03.luCondEstimate` and `GolubVanLoan.Chapter03.luCondEstimate_le`.
* **Algorithm 3.5.1** (reading). The source says $\|Ty\|_\infty \approx 1/\|T^{-1}\|_\infty$ and
  $\kappa \approx \kappa_\infty(T)$. The theorem states the inequalities that hold in exact
  arithmetic. See `GolubVanLoan.Chapter03.algorithm_3_5_1_spec`.
* **Equation (3.6.2)** (reading). The rectangular step states existence with the multiplier
  bound from partial pivoting. See `GolubVanLoan.Chapter03.equation_3_6_2`.
* **Equations (3.6.3)–(3.6.5), and assembly** (generalization). The block identities allow
  arbitrary combined trailing size. The Schur complement identity uses only the stated
  product equations. See `GolubVanLoan.Chapter03.equation_3_6_5` and
  `GolubVanLoan.Chapter03.blockLUPivoting`.
* **§3.6.1, block column induction** (generalization). The source assumes $n = rN$; the last block
  column may be narrower. See `GolubVanLoan.Chapter03.exists_blockLUPivoting`.

**Chapter 4: Special linear systems**

* **Generalization.** The diagonalization solve identity extends to the totalized inverse of
  singular matrices. See `GolubVanLoan.Chapter04.equation_4_8_2`.
* **Generalization.** The Fourier and circulant identities include the empty matrix case. See
  `GolubVanLoan.Chapter04.map_star_fourierMatrix`, `GolubVanLoan.Chapter04.dft_conjTranspose`,
  `GolubVanLoan.Chapter04.dft_conjTranspose_mul_self`, `GolubVanLoan.Chapter04.theorem_4_8_2`.
* **Reading.** The circulant program uses one forward FFT interface and totalized division. See
  `GolubVanLoan.Chapter04.algorithm_4_8_1`.
* **Scope.** The circulant solver specification captures correctness for any exact transform. See
  `GolubVanLoan.Chapter04.algorithm_4_8_1_spec`.
* **Reading.** The scalar divided-difference identity uses arbitrary nonzero grid step. See
  `GolubVanLoan.Chapter04.equation_4_8_6`.
* **Reading.** The Poisson program takes transform callbacks and totalizes zero eigenvalue sums. See
  `GolubVanLoan.Chapter04.algorithm_4_8_2`.
* **Generalization.** The exact Poisson solve does not impose a complexity bound on its transforms.
  See `GolubVanLoan.Chapter04.algorithm_4_8_2_spec`.
* **Reading.** The Dirichlet Poisson bandwidth bounds count distances from the main diagonal. See
  `GolubVanLoan.Chapter04.poisson2D_posDef_bandwidth`.
* **Scope.** The periodic real transform theorem proves column eigen-equations. See
  `GolubVanLoan.Chapter04.equation_4_8_25`.
* **Generalization.** The persymmetry results include the totalized inverse of a singular matrix.
  See `GolubVanLoan.Chapter04.isPersymmetric_inv`,
  `GolubVanLoan.Chapter04.isPersymmetric_inv_of_isToeplitz`.
* **Generalization.** The Durbin and Levinson bordering identities require only a nonzero
  denominator. See `GolubVanLoan.Chapter04.durbin_step`, `GolubVanLoan.Chapter04.equation_4_7_3`.
* **Reading.** The beta recurrence explicitly assumes the previous denominator is nonzero. See
  `GolubVanLoan.Chapter04.durbin_beta_succ`.
* **Reading.** The rounded Durbin and Levinson programs totalize division at zero pivots. See
  `GolubVanLoan.Chapter04.durbinStep`, `GolubVanLoan.Chapter04.algorithm_4_7_1`,
  `GolubVanLoan.Chapter04.algorithm_4_7_2`.
* **Reading.** The Trench program returns zeros for the uncomputed entries. See
  `GolubVanLoan.Chapter04.algorithm_4_7_3`.
* **Generalization.** The secular identity and Newton convergence also apply to indefinite Toeplitz
  matrices. See `GolubVanLoan.Chapter04.secular_lambdaMin`,
  `GolubVanLoan.Chapter04.equation_4_7_10`.
* **Generalization.** The derivative formulas and shifted Newton step require only symmetry of the
  trailing block. See `GolubVanLoan.Chapter04.secular_deriv`,
  `GolubVanLoan.Chapter04.newton_step_eq`.
* **Generalization.** The definiteness criteria include converses and the bisection index is
  antitone. See `GolubVanLoan.Chapter04.durbin_beta_pos_iff`,
  `GolubVanLoan.Chapter04.bisectionIndex_spec`.
* **Reading.** The normalized Toeplitz data are total at shift one. See
  `GolubVanLoan.Chapter04.shiftedToeplitzSeq`.
* **Reading.** The exact bisection index uses the matrix size when every denominator is positive.
  See `GolubVanLoan.Chapter04.bisectionIndex`, `GolubVanLoan.Chapter04.durbinIndex_spec`.
* **Reading.** The bisection index tests the denominator after the full Durbin step. See
  `GolubVanLoan.Chapter04.durbinIndex`.
* **Scope.** The Toeplitz bisection returns a bracket and an explicit stopping flag. See
  `GolubVanLoan.Chapter04.durbinBisection`.
* **Generalization.** The unsymmetric Toeplitz bordering implication uses cross-multiplied scalar
  equations. See `GolubVanLoan.Chapter04.equation_4_7_13`.
* **Generalization.** The nonsingularity criterion includes the converse. See
  `GolubVanLoan.Chapter04.vandermonde_isUnit_iff`.
* **Correction.** The Newton interpolant can have degree less than $n$. See
  `GolubVanLoan.Chapter04.equation_4_6_2`.
* **Reading.** The Björck–Pereyra programs totalize division and use a rounding hook. See
  `GolubVanLoan.Chapter04.algorithm_4_6_1`, `GolubVanLoan.Chapter04.algorithm_4_6_2`.
* **Reading.** The factorization and exact recurrence require only the pivots used in forming
  multipliers. See `GolubVanLoan.Chapter04.equation_4_5_3`, `GolubVanLoan.Chapter04.equation_4_5_4`.
* **Reading.** The block solve programs specify pivoting, rounding and singular-input behavior. See
  `GolubVanLoan.Chapter04.blockTridiagonalLU`, `GolubVanLoan.Chapter04.blockTridiagonalSolve`.
* **Generalization.** A single cyclic reduction step works with any odd block count. See
  `GolubVanLoan.Chapter04.cyclicReduction_step`.
* **Generalization.** The local back-substitution equations hold without commutativity. See
  `GolubVanLoan.Chapter04.cyclicReduction_back`.
* **Generalization.** The SPIKE scaling is stated for general invertible diagonal blocks. See
  `GolubVanLoan.Chapter04.equation_4_5_14`, `GolubVanLoan.Chapter04.diagonal_inv_mul_tridiagonalOf`.
* **Correction.** The first component of the Aasen recurrence uses the boundary rule in (4.4.14).
  See `GolubVanLoan.Chapter04.aasenH`, `GolubVanLoan.Chapter04.hval`.
* **Reading.** The rounded Aasen column updates use running subtractions. See
  `GolubVanLoan.Chapter04.aasenColumn`.
* **Reading.** The Aasen recurrence totalizes division at a zero subdiagonal pivot. See
  `GolubVanLoan.Chapter04.aasenNoPivot`, `GolubVanLoan.Chapter04.ColDone`.
* **Reading.** The no-pivot factorization assumes nonzero entries only where the program divides.
  See `GolubVanLoan.Chapter04.equation_4_4_14`.
* **Generalization.** The one-by-one growth bound needs only a positive entry bound and an
  admissible pivot. See `GolubVanLoan.Chapter04.equation_4_4_16`.
* **Generalization.** The two-by-two growth bound allows threshold equality at the selected diagonal
  entries. See `GolubVanLoan.Chapter04.equation_4_4_17`.
* **Scope.** The parameter theorem characterizes equality of the two factors. See
  `GolubVanLoan.Chapter04.bunchParlett_alpha`.
* **Scope.** The theorem for (4.4.5) gives the matrix identity and its Hessenberg support. See
  `GolubVanLoan.Chapter04.equation_4_4_5`.
* **Correction.** The combined band theorem requires nonsingular proper leading blocks for the lower
  factor. See `GolubVanLoan.Chapter04.theorem_4_3_1`.
* **Reading.** Band Gaussian elimination uses a final empty step and totalized division. See
  `GolubVanLoan.Chapter04.algorithm_4_3_1`, `GolubVanLoan.Chapter04.bandGEStepId`.
* **Reading.** The band forward-substitution program is defined before imposing its structural
  hypotheses. See `GolubVanLoan.Chapter04.algorithm_4_3_2`.
* **Reading.** Band back substitution totalizes division at zero diagonal entries. See
  `GolubVanLoan.Chapter04.algorithm_4_3_3`.
* **Reading.** Band Cholesky totalizes the column update and its square-root division. See
  `GolubVanLoan.Chapter04.algorithm_4_3_5`, `GolubVanLoan.Chapter04.bandCholStepId`.
* **Generalization.** The tridiagonal factorization requires just the nonzero pivots used as
  divisors. See `GolubVanLoan.Chapter04.tridiagonal_ldlt`.
* **Correction.** The exact forward substitution in the tridiagonal solver uses the previous
  right-hand-side entry. See `GolubVanLoan.Chapter04.algorithm_4_3_6_id`.
* **Reading.** The Hessenberg LU program includes a final unused pivot flag. See
  `GolubVanLoan.Chapter04.hessenbergLUStep`, `GolubVanLoan.Chapter04.algorithm_4_3_4`.
* **Reading.** The exact Hessenberg specification compares only flags at actual pivot steps. See
  `GolubVanLoan.Chapter04.algorithm_4_3_4_spec`.
* **Reading.** Gaxpy Cholesky uses rounded running differences and a totalized recurrence. See
  `GolubVanLoan.Chapter04.algorithm_4_2_1`, `GolubVanLoan.Chapter04.algorithm_4_2_1_rounds`,
  `GolubVanLoan.Chapter04.algorithm_4_2_1_lower_eq_cholesky`.
* **Reading.** The Cholesky solve uses column-oriented substitutions and totalized division. See
  `GolubVanLoan.Chapter04.solveCholesky`.
* **Reading.** The Cholesky backward-error theorem gives a finite bound for a completed run with
  nonzero pivots. See `GolubVanLoan.Chapter04.cholesky_backward_error`.
* **Reading.** The symmetric diagonal pivot chooses the first maximizer. See
  `GolubVanLoan.Chapter04.diagPivot`, `GolubVanLoan.Chapter04.diagPivot_spec`.
* **Reading.** The pivoted LDLᵀ programs totalize the displayed update at zero pivots. See
  `GolubVanLoan.Chapter04.ldltPivotStep`, `GolubVanLoan.Chapter04.algorithm_4_2_2`,
  `GolubVanLoan.Chapter04.pivotElim`, `GolubVanLoan.Chapter04.ldltPivotStep_id`.
* **Reading.** Equation (4.2.11) states nonnegativity and a count rather than a formula for the
  positions in sorted order. See `GolubVanLoan.Chapter04.equation_4_2_11`.
* **Generalization.** The bundled semidefinite bounds include diagonal indices in (4.2.13). See
  `GolubVanLoan.Chapter04.theorem_4_2_8`.
* **Generalization.** The rank-revealing invariant covers all stages, including those beyond the
  rank. See `GolubVanLoan.Chapter04.equation_4_2_16`.
* **Reading.** The algorithmic reading of (4.2.17) specifies the pivot pattern used to truncate the
  factors. See `GolubVanLoan.Chapter04.equation_4_2_17_algorithm`.
* **Reading.** The block algorithms use the totalized gaxpy Cholesky implementation for diagonal
  blocks. See `GolubVanLoan.Chapter04.choleskyLower`, `GolubVanLoan.Chapter04.choleskyLower_id`.
* **Reading.** The block triangular solves use rowwise substitution with totalized division. See
  `GolubVanLoan.Chapter04.solveRowsLower`, `GolubVanLoan.Chapter04.solveRowsLower_id`.
* **Reading.** The block product differences use running subtractions in a chosen order. See
  `GolubVanLoan.Chapter04.mulTransposeDiff`, `GolubVanLoan.Chapter04.mulTransposeDiff_id`.
* **Reading.** The recursive and nonrecursive block programs are totalized and use a fixed order of
  operations. See `GolubVanLoan.Chapter04.algorithm_4_2_3`,
  `GolubVanLoan.Chapter04.algorithm_4_2_4`, `GolubVanLoan.Chapter04.blockCholeskyStep`.
* **Reading.** Theorem 4.1.1 uses weak column dominance, with a weak inequality in the proof. See
  `GolubVanLoan.Chapter04.theorem_4_1_1`.
* **Generalization.** The inverse-norm bound uses any positive lower bound on the column margins.
  See `GolubVanLoan.Chapter04.theorem_4_1_2`.
* **Reading.** The LDLᵀ program uses running differences and describes rounded operations even at
  zero pivots. See `GolubVanLoan.Chapter04.algorithm_4_1_1`,
  `GolubVanLoan.Chapter04.algorithm_4_1_1_rounds`.
* **Reading.** The LDLᵀ solve fixes the substitution order and totalizes division at zero diagonal
  entries. See `GolubVanLoan.Chapter04.solveLDLT`.
* **Reading.** Equation (4.1.4) uses an explicit finite-roundoff bound and nonzero computed pivots.
  See `GolubVanLoan.Chapter04.equation_4_1_4`.
* **Algorithm 4.1.1** (reading). The source assumes that $A$ has an LU factorization. The
  specification assumes the hypothesis of Theorem 4.1.3, nonsingular leading principal submatrices
  of orders $1, \dots, n-1$. See `GolubVanLoan.Chapter04.algorithm_4_1_1_spec`.
* **References to "Algorithm 4.1.2"** (typo). The source refers twice to an "Algorithm 4.1.2"; it
  means Algorithm 4.1.1. See `GolubVanLoan.Chapter04.algorithm_4_1_1`.
* **(4.2.7)** (generalization). The source prints a first-order bound with the extra term
  $2n \|A\|_F$. The library proves the rigorous bound $\|E\|_F \le \gamma_{3n} c n (\|T\|_2 + \|S
  T^{-1} S\|_2)$. See `GolubVanLoan.Chapter04.equation_4_2_7`.
* **Theorem 4.2.8, (4.2.13)** (generalization). The source states
  $|a_{ij}| \le \sqrt{a_{ii} a_{jj}}$ for $i \neq j$. The library states it for all $i, j$. See
  `GolubVanLoan.Chapter04.theorem_4_2_8_b`.
* **Algorithm 4.2.2** (correction). The source gives $d_n > 0$ for a semidefinite input. For a
  singular $A$ the computed $d_n$ is $0$; the library states $d_i \ge 0$, and $d_i > 0$ when $A$ is
  positive definite. See `GolubVanLoan.Chapter04.algorithm_4_2_2_spec`.
* **Algorithm 4.2.2** (reading). The source writes $P = P_1 \cdots P_n$. The library takes the
  product of the interchanges in the order in which they are applied. See
  `GolubVanLoan.Chapter04.algorithm_4_2_2_spec`.
* **Theorem 4.3.1** (correction). The statement about $L$ is false without the nonsingularity of the
  leading principal submatrices: $\begin{bmatrix} 0 & 1 \\ 0 & 2 \end{bmatrix} = \begin{bmatrix} 1 &
  0 \\ \beta & 1 \end{bmatrix} \begin{bmatrix} 0 & 1 \\ 0 & 2 - \beta \end{bmatrix}$ for every
  $\beta$. The library adds this hypothesis for $L$. See `GolubVanLoan.Chapter04.theorem_4_3_1_b`.
* **Algorithm 4.3.1** (reading). "Assuming it exists" is read as the nonsingularity of the leading
  principal submatrices $A(1{:}k, 1{:}k)$, $k = 1{:}n-1$. See
  `GolubVanLoan.Chapter04.algorithm_4_3_1_spec`.
* **Theorem 4.3.2** (generalization). The source assumes that $A$ is nonsingular. The library does
  not need this hypothesis. See `GolubVanLoan.Chapter04.theorem_4_3_2`.
* **Algorithm 4.3.6** (typo). The second loop prints $b(k) = b(k) - \beta(k-1) \cdot \beta(k-1)$.
  The forward solve $Ly = b$ is $b(k) = b(k) - \beta(k-1) \cdot b(k-1)$, which the program does. See
  `GolubVanLoan.Chapter04.algorithm_4_3_6`.
* **(4.4.2)** (correction). The source says that $P$ is chosen so that $|\ell_{ij}| \le 1$. This is
  false for the Bunch–Parlett strategy of the section. The library proves
  $|\ell_{ij}| \le \max(1/\alpha, 1/(1 - \alpha))$. See
  `GolubVanLoan.Chapter04.equation_4_4_2_multipliers`.
* **(4.4.10)** (typo). The loop starts at $k = 1$, which needs an undefined $\beta_0$. The program
  follows (4.4.14), whose loop starts at $k = 2$. See `GolubVanLoan.Chapter04.aasenNoPivot`.
* **(4.4.15)** (generalization). The pivot block $E$ need not be symmetric for the displayed
  factorization. See `GolubVanLoan.Chapter04.equation_4_4_15`.
* **(4.4.20)** (generalization). The source assumes that $C$ is diagonal. The library assumes only
  that $C$ is symmetric positive definite. See `GolubVanLoan.Chapter04.equation_4_4_20`.
* **(4.5.8)** (reading). The source prints $\|U_i\|_1 \le \|A_n\|_1$, whose right-hand side has no
  referent in the section. It is read as the $1$-norm of the whole matrix $A$. See
  `GolubVanLoan.Chapter04.equation_4_5_8`.
* **The bracket of §4.7.7** (reading). The source writes $\lambda_{\min}(T) < \lambda_{\min}(B)$,
  which is the hypothesis (4.7.8). The theorem proves $\lambda_{\min}(T) \le \lambda_{\min}(B)$
  without it. See `GolubVanLoan.Chapter04.lambdaMin_bracket`.
* **The invariant after (4.7.11)** (correction). The source prints $m(L) \le n - 1 \le m(R)$. Since
  $m$ is antitone, the update rule maintains $m(R) \le n - 1 \le m(L)$ instead. See
  `GolubVanLoan.Chapter04.equation_4_7_11`.
* **Equation (4.8.4)** (typo). The source prints $(V^{-1} \mathcal{D}_n V^{-1})^k$;
  $(V^{-1} \mathcal{D}_n V)^k$ is meant. See `GolubVanLoan.Chapter04.equation_4_8_4`.
* **Lemma 4.8.1** (reading). The formula $\lambda_{j+1} = \bar\omega_n^j$ is read for every
  $n \ge 1$; for $n = 1$ the downshift is $I_1$. See `GolubVanLoan.Chapter04.lemma_4_8_1`.
* **§4.8.6, the Dirichlet–Neumann paragraph** (typo). The source cites a nonexistent "(1.4.13)" for
  $\mathrm{DST2}$; (1.4.12) is meant. See `GolubVanLoan.Chapter04.dn_eigen`.
* **§4.8.6, the Neumann–Neumann paragraph** (typo). The source twice writes $\mathcal{T}^{(DN)}$ and
  $V^{(DN)}$ for $\mathcal{T}^{(NN)}$ and $V^{(NN)}$. See `GolubVanLoan.Chapter04.nn_eigen`.
* **§4.8.6, the periodic matrix** (reading). The statement that $\mathcal{T}^{(P)}_n$ is circulant,
  with first column $(2, -1, 0, \dots, 0, -1)^T$, is read for $n \ge 3$. See
  `GolubVanLoan.Chapter04.periodic_eigen`.

**Chapter 5: Orthogonalization and least squares**

* **(5.1.1), (5.1.2) and §5.1.13** (domain). `GolubVanLoan.Chapter05.householderMatrix`
  assigns the identity to the zero vector, extending the source's nonzero domain.
  `GolubVanLoan.Chapter05.equation_5_1_2` and `GolubVanLoan.Chapter05.complexHouseholder` impose
  the nonzero normal explicitly for the selected sign. The complex theorem fixes the phase at
  $1$ when the first component is zero.
* **(5.1.8)** (reading). `GolubVanLoan.Chapter05.equation_5_1_8` requires a nonzero input pair
  to ensure a nonzero denominator and gives the first component as well as the zero second
  component.
* **§5.1.4, §5.1.9 and §6.5.4** (generalization).
  `GolubVanLoan.Chapter05.householderApplyLeft`, `GolubVanLoan.Chapter05.householderApplyRight`,
  `GolubVanLoan.Chapter05.givensApplyLeft`, `GolubVanLoan.Chapter05.givensApplyRight` and
  `GolubVanLoan.Chapter05.hyperbolicApplyLeft` work on selected index lists, including
  noncontiguous ones. The exact specifications use duplicate-free lists.
* **§5.1.5 and §5.1.10** (precision). The rounding theorems state explicit constants in the
  relative rounding model. The update bounds use row or column norms and the Frobenius norm of
  the selected block where the source gives a spectral-norm backward error.
  `GolubVanLoan.Chapter05.one_sub_smul_vecMulVec_computed_sub_le` also analyzes the applied
  reflector with the actual computed coefficient, including an identity step.
* **(5.1.3), (5.1.6) and Algorithm 5.1.2** (generalizations).
  `GolubVanLoan.Chapter05.householderProduct` and the accumulation programs accept arbitrary
  lists of rank-one update data. `GolubVanLoan.Chapter05.equation_5_1_6` and
  `GolubVanLoan.Chapter05.algorithm_5_1_2_spec` establish WY even for nonorthogonal factors and
  empty data.
* **§5.1.12** (precision). `GolubVanLoan.Chapter05.orthogonalToWorkingPrecision` takes an
  explicit tolerance in the spectral norm. The corollary bounds the orthogonality defect by
  $2\varepsilon+\varepsilon^2$. Equation (5.1.11) assumes a local Frobenius error bound at the
  computed iterates and gives explicit global Frobenius and spectral bounds.
* **(5.1.12)** (scope). `GolubVanLoan.Chapter05.equation_5_1_12` proves that the second
  component is zero using the three real rotations.
  `GolubVanLoan.Chapter05.complexGivens_mem_unitaryGroup` gives the separate unitary-matrix
  result.
* **Algorithm 5.1.1** (correction). The source sets $\beta = -2$ in the branch $\sigma = 0$,
  $x(1) < 0$, which makes $P$ not orthogonal. The program sets $\beta = 2$. See
  `GolubVanLoan.Chapter05.algorithm_5_1_1`.
* **Equations (5.1.4) and (5.1.5)** (correction). The source recovers
  $\beta_j = 2/(1 + \|A(j+1{:}m, j)\|_2^2)$ from the stored vector, which is wrong when Algorithm
  5.1.1 returned $\beta_j = 0$. The displays are stated for the recomputed $\beta_j$, and the first
  columns of $Q$ with the returned $\beta_j$ are a separate program. See
  `GolubVanLoan.Chapter05.equation_5_1_4`, `GolubVanLoan.Chapter05.equation_5_1_5` and
  `GolubVanLoan.Chapter05.storedQFirstColumns`.
* **Lemma 5.1.1** (generalization). The source assumes that $Q$ is orthogonal. The identity holds
  without this assumption. See `GolubVanLoan.Chapter05.lemma_5_1_1`.
* **Equation (5.1.11)** (reading). The source refers to the rotations or reflections that would
  be produced without roundoff. The theorem uses the exact transformations determined by the
  computed data at each step and assumes a local error bound for them. See
  `GolubVanLoan.Chapter05.equation_5_1_11`.

* **(5.2.3) and (5.2.4)** (generalizations). `GolubVanLoan.Chapter05.equation_5_2_3` needs no
  rank hypothesis. `GolubVanLoan.Chapter05.kappa2` uses the pseudoinverse for every matrix, and
  `GolubVanLoan.Chapter05.kappa2_eq_div_of_rows` gives the full-row-rank counterpart of (5.2.4).
* **Algorithm 5.2.1** (representation). `GolubVanLoan.Chapter05.algorithm_5_2_1` retains the
  coefficients returned by `house` along with the packed array. Its exact correctness theorem
  assumes $m \ge n$.
* **§5.2.2, backward error** (precision). `GolubVanLoan.Chapter05.algorithm_5_2_1_rounding`
  and `GolubVanLoan.Chapter05.algorithm_5_2_1_rounding_data` replace the approximate spectral
  norm bound by explicit columnwise bounds, with idempotence and smallness assumptions in the
  rounding model.
* **§5.2.3 and Algorithm 5.2.2** (corrections). The preceding trailing-block example omits the
  outer transpose, and the algorithm's block identity omits the transpose of $Y_k$.
  `GolubVanLoan.Chapter05.wyApplyLeft` applies $(I-W_k Y_k^T)^T$, and
  `GolubVanLoan.Chapter05.blockQRPanel` multiplies $Q$ on the right by $I-W_k Y_k^T$.
  `GolubVanLoan.Chapter05.algorithm_5_2_2` returns a packed array, and its exact specification
  uses its upper part.
* **§5.2.5, row-ordered Givens QR** (correction). The printed inner loop runs to $i-1$, which
  can exceed the number of columns. `GolubVanLoan.Chapter05.givensQRByRow` restricts the upper
  endpoint to $\min(i-1,n)$.
* **Algorithm 5.2.5** (reading). `GolubVanLoan.Chapter05.algorithm_5_2_5` represents positive
  orders as $k+1$ and returns the rotation parameters. Its specification also proves the
  Hessenberg structure of $Q$ described in §7.4.2.
* **Algorithms 5.2.4 and 5.2.5** (extensions).
  `GolubVanLoan.Chapter05.algorithm_5_2_4_rounding` and
  `GolubVanLoan.Chapter05.algorithm_5_2_5_rounding` give explicit columnwise bounds for the
  completed Givens reductions.
* **§5.2.7 and Algorithm 5.2.6** (totalization). The Gram–Schmidt programs and their exact
  equalities to the backbone factors extend to all matrices using total division. The thin QR
  specifications retain full column rank. Modified Gram–Schmidt writes $Q$ to a separate array.
  `GolubVanLoan.Chapter05.mgs_remainder_eq` applies to any thin QR and assumes a positive pivot
  only for the normalization and coefficient identities.
* **§5.2.10** (scope). `GolubVanLoan.Chapter05.complexHouseholderQR` proves existence of a
  complex QR factorization. The statement omits the complex Householder pseudocode and the
  sequence of reflectors.
* **§6.5.1, Givens sweeps** (generalization). `GolubVanLoan.Chapter05.givensHessenbergSweep`
  and `GolubVanLoan.Chapter05.givensVectorSweep` take explicit interval limits and rectangular
  arrays, applying each rotation to the whole array. Their specifications state the active
  interval and the shape or support hypotheses used in the updating algorithms.
* **§5.2.2, the formula $\beta_j = 2/(1 + \|A(j{+}1{:}m, j)\|_2^2)$** (correction). The formula
  gives $2$ where `house` returned $\beta_j = 0$; it is stated only for the nonzero $\beta_j$. See
  `GolubVanLoan.Chapter05.equation_5_1_4_beta`.
* **(5.2.2)** (generalization). The source states it under the full column rank hypothesis of
  Theorem 5.2.2; it holds for every QR factorization with $m \ge n$. See
  `GolubVanLoan.Chapter05.equation_5_2_2`.
* **Algorithm 5.2.2** (reading). The source does not restrict $m$ and $n$; the specification assumes
  $m \ge n$, which its panel factorization by Algorithm 5.2.1 needs. See
  `GolubVanLoan.Chapter05.algorithm_5_2_2_spec`.
* **Algorithm 5.2.3** (generalization). The source assumes that the block size $n_b$ is a positive
  integer; the exact specification holds for every $n_b \ge 0$. See
  `GolubVanLoan.Chapter05.algorithm_5_2_3_spec`.
* **Algorithm 5.2.4** (generalization). The source assumes $m \ge n$; the exact specification and
  the backward error bound hold for all $m$ and $n$. See
  `GolubVanLoan.Chapter05.algorithm_5_2_4_spec` and
  `GolubVanLoan.Chapter05.algorithm_5_2_4_rounding`.

* **Equation (5.3.5)** (generalization). The QR residual split is independent of rank. The
  inverse formula for the minimizer uses full column rank. See
  `GolubVanLoan.Chapter05.equation_5_3_5`.
* **§5.3.5, augmented modified Gram–Schmidt** (reading). The exact theorem requires independent
  columns of $[A\mid b]$ to justify the final normalization. See
  `GolubVanLoan.Chapter05.mgs_augmented`.
* **Equation (5.3.9)** (reading). The projector norm identities assume $0<n<m$. A full-rank
  square matrix has zero residual projector. See `GolubVanLoan.Chapter05.equation_5_3_9`.
* **§5.3.8, iterative improvement** (reading). The program takes an iteration count and two
  rounding functions. The exact theorem gives a solution after any positive number of
  iterations. See `GolubVanLoan.Chapter05.lsIterativeImprovement` and
  `GolubVanLoan.Chapter05.lsIterativeImprovement_spec`.
* **Equation (5.3.25)** (reading). The normalized inner product requires nonzero vectors. See
  `GolubVanLoan.Chapter05.equation_5_3_25`.
* **Equation (5.3.3)** (typo). The source prints the upper summation limit as $2$; it is $m$. See
  `GolubVanLoan.Chapter05.equation_5_3_3`.
* **Equation (5.3.4)** (reading). The source estimates the relative error as
  $\approx u\kappa_2(A)^2$. The theorem states the rigorous bound
  $\eta\kappa_2(A)^2/(1 - \eta\kappa_2(A)^2)$. See `GolubVanLoan.Chapter05.equation_5_3_4`.
* **Algorithm 5.3.2** (correction). The source recomputes $\beta_j = 2/v^Tv$, which is wrong when
  `house` returned $\beta_j = 0$; the correctness statement needs every returned $\beta_j \neq 0$.
  See `GolubVanLoan.Chapter05.algorithm_5_3_2_spec`,
  `GolubVanLoan.Chapter05.algorithm_5_3_2_counterexample` and
  `GolubVanLoan.Chapter05.householderLS`.
* **Equations (5.3.6)–(5.3.8)** (reading). The source states first-order bounds with the constants
  of Lawson and Hanson. The theorems state rigorous bounds with explicit $\gamma$ constants, for
  runs with nonzero computed $\beta_j$ and nonsingular $\hat R_1$. See
  `GolubVanLoan.Chapter05.equation_5_3_6`.
* **Theorem 5.3.1** (reading). The terms $O(\varepsilon^2)$ are read as $K\varepsilon^2$ for
  $\varepsilon \le \varepsilon_0$. See `GolubVanLoan.Chapter05.theorem_5_3_1`.
* **Theorem 5.3.1, (5.3.11)** (generalization). A rigorous form with $\sigma_n(A) - \|\delta A\|_2$
  in place of $\sigma_n(A)$ holds without the hypothesis $r_{LS} \neq 0$. See
  `GolubVanLoan.Chapter05.theorem_5_3_1_a`.
* **Theorem 5.3.1, (5.3.12)** (reading). A rigorous form holds with
  $\|A\|_2/(\sigma_n(A) - \|\delta A\|_2)$ in place of $\kappa_2(A)$ in the last term. See
  `GolubVanLoan.Chapter05.theorem_5_3_1_b`.
* **Equations (5.3.27)–(5.3.28)** (correction). The source omits the hypothesis that the lines are
  not parallel, $r \neq 0$; for $r = 0$ the formulas divide by zero. See
  `GolubVanLoan.Chapter05.equation_5_3_27`.
* **Equation (5.3.29)** (correction). Three distinct points do not determine a plane; the points
  must not be collinear, $v \neq 0$. See `GolubVanLoan.Chapter05.equation_5_3_29`.

* **§5.4.3, pivoted QR roundoff and stopping criterion** (reading). The theorem gives an
  explicit columnwise backward error under idempotent rounding. The singular-value bound is
  conditional on the trailing-block test. See `GolubVanLoan.Chapter05.algorithm_5_4_1_rounding`
  and `GolubVanLoan.Chapter05.algorithm_5_4_1_sigma_succ_le`.
* **Theorem 5.4.1** (reading). The statement requires $m\ge n$ explicitly, as needed by the last
  diagonal entry. The chosen permutation works for any QR factorization. See
  `GolubVanLoan.Chapter05.theorem_5_4_1`.
* **§5.4.5, zero-chasing update** (reading). The implementation allows either sign of the last
  unit vector, which preserves the last-column norm identity. See
  `GolubVanLoan.Chapter05.givensRevealUpdate_spec`.
* **Equation (5.4.13) and Algorithm 5.4.2** (reading). Existence also covers wide matrices. The
  tall Householder program returns both arrays of reflector coefficients with the packed matrix.
  See `GolubVanLoan.Chapter05.equation_5_4_13` and `GolubVanLoan.Chapter05.algorithm_5_4_2`.
* **Algorithm 5.4.1** (typo). The source prints $A(:r{:}m, r{:}n)$; it is $A(r{:}m, r{:}n)$. See
  `GolubVanLoan.Chapter05.algorithm_5_4_1`.
* **The Kahan matrix, §5.4.3** (generalization). The source takes $c > 0$; the result needs only
  $s > 0$ and $c^2 + s^2 = 1$. See `GolubVanLoan.Chapter05.kahanMatrix_unaltered`.
* **Equation (5.4.10)** (generalization). The source assumes $\sigma_k(A) > \sigma_{k+1}(A)$; the
  bound holds for every SVD without it. See `GolubVanLoan.Chapter05.equation_5_4_10`.
* **Equation (5.4.11)** (typo). The source prints $\|L_{12}\|_2$, a zero block; it is
  $\|L_{21}\|_2$. See `GolubVanLoan.Chapter05.equation_5_4_11`.
* **Equation (5.4.11)** (generalization). As for (5.4.10), the separation
  $\sigma_k(A) > \sigma_{k+1}(A)$ is not needed. See `GolubVanLoan.Chapter05.equation_5_4_11`.

* **§5.5.2, Moore–Penrose projections** (reading). The declaration states the projection onto
  the range of $A$. The source also identifies the projection onto the range of $A^T$. See
  `GolubVanLoan.Chapter05.moorePenrose`.
* **§5.5.4, truncation bound** (generalization). Only the retained terms require positive
  singular values. Zero singular values in the omitted tail contribute zero through the
  pseudoinverse convention. See `GolubVanLoan.Chapter05.norm_truncatedSVDSolution_sub_le`.
* **§5.5.5, basic solution** (correction). A zero $R_{12}$ is sufficient for the basic solution
  to have minimum norm. The source phrases this as necessary, although equality can also occur
  for nonzero $R_{12}$. See `GolubVanLoan.Chapter05.basicSolution_eq_pinv_of_eq_zero`.
* **Algorithm 5.5.1** (reading). The program receives $V$ and the rank estimate from the caller,
  and uses a padded pivoted QR. See `GolubVanLoan.Chapter05.algorithm_5_5_1`.
* **Equation (5.5.3)** (typo). The source prints $X \in \mathbb{R}^{m \times n}$; the unknown is
  $X \in \mathbb{R}^{n \times m}$. See `GolubVanLoan.Chapter05.equation_5_5_3`.
* **Example of §5.5.3** (typo). The source prints $(A + \delta A)^+$ with a spurious entry $1$ in
  position $(2, 1)$. See `GolubVanLoan.Chapter05.pinv_discontinuity`.
* **Equation (5.5.4)** (typo). The source prints $z \in \mathbb{R}^{n-2}$ for
  $z \in \mathbb{R}^{n-r}$. See `GolubVanLoan.Chapter05.equation_5_5_4`.
* **Theorem 5.5.3** (typo). The source calls $\tilde V_{11}$ the leading "$r$-by-$r$" principal
  submatrix of $P^T V$; it is $\tilde r$-by-$\tilde r$. See `GolubVanLoan.Chapter05.theorem_5_5_3`.
* **Theorem 5.5.3** (reading). The source leaves the hypothesis
  $\tilde r \le \operatorname{rank}(A)$ implicit; the statement assumes it. See
  `GolubVanLoan.Chapter05.theorem_5_5_3`.

* **§5.6.2, SVD minimum-norm solution** (generalization). The expansion applies to consistent
  systems of any shape. See `GolubVanLoan.Chapter05.minNorm_svd_underdetermined`.
* **Algorithm 5.6.1** (reading). Zero padding lets the program reuse square pivoted QR. The
  source factors the input directly. See `GolubVanLoan.Chapter05.algorithm_5_6_1`.
* **Theorem 5.6.1, rank preservation** (reading). The exact bound requires $\|\delta
  A\|_2<\sigma_m(A)$. The first-order theorem chooses a sufficient relative-error threshold for
  $A$. The printed comparison of dimensionless $\epsilon$ with $\sigma_m(A)$ does not by itself
  imply this rank-preservation condition. See `GolubVanLoan.Chapter05.theorem_5_6_1` and
  `GolubVanLoan.Chapter05.theorem_5_6_1_firstOrder`.
* **Theorem 5.6.1** (reading). The source states a first-order bound with an implicit
  $O(\epsilon^2)$ term. The library reads the remainder as $K \epsilon^2$ for all perturbations with
  $\epsilon \le \epsilon_0$, and also proves a rigorous bound in which $\sigma_m(A)$ is replaced by
  $\sigma_m(A) - \|\delta A\|_2$. See `GolubVanLoan.Chapter05.theorem_5_6_1_firstOrder` and
  `GolubVanLoan.Chapter05.theorem_5_6_1`.

**Chapter 6: Modified least squares problems and methods**

* **Equation (6.1.1)** (generalization). The weighted objective and its minimizers allow zero
  weights. See `GolubVanLoan.Chapter06.IsWeightedLeastSquaresSolution` and
  `GolubVanLoan.Chapter06.equation_6_1_1`.
* **After (6.1.4)** (typo). The positive definite weighted Gram matrix uses the squared weight
  matrix $D(\delta)^2$, as in the derivative formula. See
  `GolubVanLoan.Chapter06.equation_6_1_4`.
* **§6.1.4, ridge limits and monotonicity** (reading). The positive-parameter limit selects the
  minimum-norm solution. The norm is nonincreasing, with strict decrease when $A^Tb$ is nonzero.
  See `GolubVanLoan.Chapter06.tendsto_ridge_leastSquares` and
  `GolubVanLoan.Chapter06.norm_ridge_antitoneOn`.
* **§6.1.4, cross-validation** (reading). The sum accepts signed weights. Equation (6.1.18) uses
  the full ridge residual for both the numerator and derivative, with (6.1.17) giving the
  quotient as the leave-one-out residual. See `GolubVanLoan.Chapter06.crossValidationError` and
  `GolubVanLoan.Chapter06.equation_6_1_18`.
* **Theorem 6.1.1 and §6.1.6** (reading). The full GSVD theorem includes the normalization from
  the CS construction. The generalized eigenvalue relation is homogeneous, with a finite ratio
  when $\beta_i$ is nonzero. See `GolubVanLoan.Chapter06.theorem_6_1_1_b` and
  `GolubVanLoan.Chapter06.gsvd_generalizedEigen`.
* **Remark after (6.1.4)** (correction). The source derives the monotonicity of $|r_k(\delta)|$ from
  $\frac{d}{d\delta} [r_k(\delta)^2] < 0$, which fails when $a_k = 0$ or $r_k(\delta) = 0$. The
  library states the non-strict monotonicity. See
  `GolubVanLoan.Chapter06.abs_weightedResidual_antitoneOn`.
* **Paige's method, (6.1.9)–(6.1.10)** (generalization). The source assumes that $A$ has full column
  rank and $B$ is nonsingular; the statement needs only that $S$ is nonsingular. See
  `GolubVanLoan.Chapter06.equation_6_1_9`.
* **§6.1.3, column weighting** (generalization). $x_G = G^{-1} y$ minimizes $\|Ax - b\|_2$ for every
  least-squares solution $y$, not only for the minimum-norm one. See
  `GolubVanLoan.Chapter06.isLeastSquaresSolution_columnWeighting`.
* **§6.1.3, the least $G$-norm** (generalization). The source states the property for
  $\operatorname{rank}(A) < n$; it holds for every rank. See
  `GolubVanLoan.Chapter06.norm_columnWeighting_le`.
* **Equation (6.1.19)** (typo). The numerator has $\tilde b_k$ where $b_k$ is meant. See
  `GolubVanLoan.Chapter06.equation_6_1_19`.
* **Theorem 6.1.1** (typo). The row labels $p$, $r - p$, $m_2 - r$ of the blocks of $D_B$ are
  $r - p$, $m_2 - r + p$, and $n_{1-r}$ is $n_1 - r$. See `GolubVanLoan.Chapter06.theorem_6_1_1`.
* **§6.1.6, the GSVD of $(A, I)$** (correction). The source sets $X = U_2$ to obtain the SVD of $A$;
  in fact $X = U_2 D_B$ and $U_1^T A U_2 = \operatorname{diag}(\alpha_i / \beta_i)$. See
  `GolubVanLoan.Chapter06.gsvd_one`.

* **§6.2.3, QR derivation** (generalization). Full row rank of $B$ suffices for the QR
  construction given a reduced least-squares solution. Full column rank of $A$ suffices for
  uniqueness. See `GolubVanLoan.Chapter06.isLSESolution_qr`.
* **Equation (6.2.13)** (generalization). The stacked objective identity includes zero penalty
  weight. For positive weight, the theorem also gives positive definiteness under the trivial
  common-kernel condition. See `GolubVanLoan.Chapter06.equation_6_2_13`.
* **Equation (6.2.1), solution predicate** (generalization). The closed-ball problem includes
  radius zero. The source starts with a positive radius. See
  `GolubVanLoan.Chapter06.IsSphereLSQISolution`.
* **Algorithm 6.2.1** (reading). The program delegates the SVD and root steps. The supplied root
  routine receives the exact secular function. See `GolubVanLoan.Chapter06.algorithm_6_2_1`.
* **Equation (6.2.12)** (reading). The formula requires full row rank of $B$ to ensure nonzero
  constraint denominators. See `GolubVanLoan.Chapter06.equation_6_2_12`.
* **Equation (6.2.14) and penalty convergence** (generalization). Full row rank of $B$ and a
  trivial common kernel suffice in place of full rank of both matrices. See
  `GolubVanLoan.Chapter06.equation_6_2_14` and
  `GolubVanLoan.Chapter06.tendsto_penaltyLSE_solution`.
* **§6.2.1, the secular equation** (reading). The source's $f(0) > 0$ is read as
  $f(0^+) = \|x_{LS}\|_2^2 - \alpha^2 > 0$, because $x(\lambda)$ is $x_{LS}$ only in the limit. See
  `GolubVanLoan.Chapter06.secular_existsUnique`.
* **Algorithm 6.2.1** (generalization). The source assumes $m \ge n$; the correctness statement
  holds for all $m$ and $n$. See `GolubVanLoan.Chapter06.algorithm_6_2_1_spec`.
* **Equation (6.2.6)** (typo). The source cites "(6.2.23)" for (6.1.23). See
  `GolubVanLoan.Chapter06.equation_6_2_6`.
* **Equation (6.2.7)** (generalization). The diagonal residual formula is stated for both tall and
  wide rectangular matrices. For $m_1 \ge n_1$ it splits into the two sums printed in the source.
  See `GolubVanLoan.Chapter06.equation_6_2_7`.
* **Equation (6.2.8)** (correction). The source prints it in the block order of the third edition,
  and its second sum, over $\tilde d_i$ for $i = m_2 + 1, \dots, n_1$, is meaningless. See
  `GolubVanLoan.Chapter06.equation_6_2_8`.
* **§6.2.3, non-uniqueness of the LSE solution** (generalization). The source gives a sufficient
  condition for non-uniqueness. The theorem gives existence whenever $d \in \operatorname{ran}(B)$
  and shows that every common null vector translates a solution to another solution. See
  `GolubVanLoan.Chapter06.isLSESolution_not_unique`.
* **Algorithm 6.2.2** (generalization). The source assumes $m_2 < n_1$; the correctness statement
  allows $m_2 \le n_1$. See `GolubVanLoan.Chapter06.algorithm_6_2_2_spec`.
* **Equation (6.2.12)** (correction). The source prints it in the block order of the third edition.
  See `GolubVanLoan.Chapter06.equation_6_2_12`.
* **Equation (6.2.14)** (correction). The source prints it in the block order of the third edition,
  with $\lambda^2$ for $\lambda$, $u_i^T b$ and $v_i^T d$ for $\tilde b_i$ and $\tilde d_i$, and the
  range $1{:}p$. See `GolubVanLoan.Chapter06.equation_6_2_14`.

* **Equation (6.3.6)** (reading). The orthogonal-regression theorem uses the explicit singular-
  vector minimizer under the strict singular-value gap and permits zero row weights for the
  objective comparison. See `GolubVanLoan.Chapter06.equation_6_3_6`.
* **Algorithm 6.3.1** (reading). The trailing equal values can cover the entire spectrum. The
  zero-pivot branch returns `none`, and the exact specification proves that no TLS solution
  exists in that case. See `GolubVanLoan.Chapter06.algorithm_6_3_1` and
  `GolubVanLoan.Chapter06.algorithm_6_3_1_spec`.
* **Theorem 6.3.1, nonsingularity of $V_{22}$** (generalization). The source assumes that $D$ and
  $T$ are nonsingular and $m \ge n + k$. The nonsingularity of $V_{22}$ holds without these
  hypotheses. See `GolubVanLoan.Chapter06.theorem_6_3_1_isUnit`.
* **§6.3.2, the single right-hand side** (generalization). The source takes $\tilde Q$ to be a
  Householder matrix. The statement holds for every orthogonal $\tilde Q$ with the same zero
  pattern. See `GolubVanLoan.Chapter06.tls_single`.
* **§6.3.2, the single right-hand side** (reading). The source says that the last column has the
  largest $(n{+}1)$st component of all vectors in the span. The statement compares absolute values
  over the unit vectors of the span. See `GolubVanLoan.Chapter06.tls_single`.

* **§6.4.1, polar factor** (generalization). The orthogonal polar factor of $B^T A$ is a
  Procrustes minimizer for arbitrary $A$ and $B$. The source discusses the special case $B=I$.
  See `GolubVanLoan.Chapter06.procrustes_solution_of_isPolarDecomposition`.
* **Algorithm 6.4.2** (reading). Exact comparisons of computed singular values give the rank.
  The trivial intersection returns a zero-column matrix. See
  `GolubVanLoan.Chapter06.algorithm_6_4_2`.
* **Equation (6.4.3) and §6.4.3** (generalization). The recursive characterization includes the
  empty family. The cosine and singular-value equality is zero-extended beyond the available
  pairs and permits either dimension order. See `GolubVanLoan.Chapter06.equation_6_4_3` and
  `GolubVanLoan.Chapter06.singularValues_transpose_mul_eq_cosPrincipalAngle`.
* **Theorem 6.4.2** (reading). The initial run of unit cosines can be empty or include all
  indices. See `GolubVanLoan.Chapter06.theorem_6_4_2`.
* **Algorithm 6.4.3** (typo). The heading says that the algorithm computes the cosines of the
  principal angles $\theta_1 \ge \dots \ge \theta_q$. The order is reversed: the cosines decrease
  and the angles increase. See `GolubVanLoan.Chapter06.algorithm_6_4_3`.
* **§6.4.3** (typo). The source says that the subspaces lie in $\mathbb{R}^m$ but takes
  $A \in \mathbb{R}^{n \times p}$. The library takes $A \in \mathbb{R}^{m \times p}$. See
  `GolubVanLoan.Chapter06.algorithm_6_4_3`.
* **§6.4.3** (typo). The source writes "$v = Q_B z_1 = g_1$" where it means $g_1 = Q_B z_1$. See
  `GolubVanLoan.Chapter06.isPrincipalVectors_of_isSVD`.
* **Equation (6.4.6)** (generalization). The source states the identity for unit vectors $u$ and
  $v$. It holds for all $u$ and $v$. See `GolubVanLoan.Chapter06.equation_6_4_6`.
* **Theorem 6.4.2** (generalization). The source states the theorem for the principal vectors
  computed by Algorithm 6.4.3. It holds for any principal vectors of
  $(\operatorname{ran}(A), \operatorname{ran}(B))$. See `GolubVanLoan.Chapter06.theorem_6_4_2`.

* **Equations (6.5.6) and (6.5.10)** (generalization). The two Gram identities hold for any
  square $G$ with $GG^T=A$, without the source's positive-definite Cholesky setting. See
  `GolubVanLoan.Chapter06.equation_6_5_6` and `GolubVanLoan.Chapter06.equation_6_5_10`.
* **Equations (6.5.2)–(6.5.3)** (generalization). Arbitrary embedded adjacent blocks preserve
  the Hessenberg structure. The rank-one update identity assumes only that the sweep maps $w$ to
  $\rho e_1$. See `GolubVanLoan.Chapter06.equation_6_5_2` and
  `GolubVanLoan.Chapter06.equation_6_5_3`.
* **§6.5.2** (generalization). The column updates accept wide upper trapezoidal factors.
  Insertion can occur at the first column. See `GolubVanLoan.Chapter06.qrDeleteColumn` and
  `GolubVanLoan.Chapter06.qrInsertColumn`.
* **§6.5.3, row deletion** (reading). The arbitrary-row result gives existence of a QR
  factorization. The implemented update treats the source's detailed first-row procedure. See
  `GolubVanLoan.Chapter06.qrDeleteRow_exists` and `GolubVanLoan.Chapter06.qrDeleteFirstRow`.
* **§6.5.4, downdate sweep** (typo). The matrix whose bottom row is zeroed is the stack
  $[G^T;z^T]$. The prose immediately before Theorem 6.5.1 transposes the concatenation
  $[G^T\mid z]$, which gives $[G;z^T]$. See
  `GolubVanLoan.Chapter06.choleskyDowndate`.
* **§6.5.1** (typo). "Following Algorithm 5.2.4" means Algorithm 5.2.5, the QR factorization of an
  upper Hessenberg matrix. See `GolubVanLoan.Chapter06.qrUpdateRankOne`.
* **Equation (6.5.7)** (typo). The source prints $\tilde A = RR^T$. The correct identity is
  $\tilde A = R^T R$. See `GolubVanLoan.Chapter06.equation_6_5_7`.
* **Equation (6.5.7)** (correction). The source says that $\tilde G = R^T$ is the updated Cholesky
  factor. When the rotations are Givens rotations, the diagonal of $R$ can have negative entries, so
  $R^T$ is the Cholesky factor only after the signs of its diagonal are normalized. See
  `GolubVanLoan.Chapter06.equation_6_5_7` and `GolubVanLoan.Chapter06.choleskyUpdate_spec`.
* **Equation (6.5.12)** (correction). The source says that $\tilde G = R^T$ is the Cholesky factor
  of $A - zz^T$. The statement normalizes the signs of the diagonal of $R$, as for (6.5.7). See
  `GolubVanLoan.Chapter06.equation_6_5_12`.
* **§6.5.4, nonexistence of a hyperbolic rotation** (generalization). The source treats
  $|x_2| > |x_1|$. The statement also covers $|x_2| = |x_1| \neq 0$. See
  `GolubVanLoan.Chapter06.hyperbolic_not_exists`.
* **Proof of Theorem 6.5.1** (typo). The Schur complement in the proof uses the pivot
  $\alpha - \mu^2$, printed as $\alpha$ in the prose. See `GolubVanLoan.Chapter06.theorem_6_5_1`.
* **Equation (6.5.16)** (generalization). The source obtains $\Pi$ and $R$ from QR with column
  pivoting. The statement holds for every orthogonal $\Pi$ and every $R$ with $U^T A \Pi = [R; 0]$.
  See `GolubVanLoan.Chapter06.equation_6_5_16`.
* **§6.5.5** (typo). In $\|AV_2\|_2 = \|U_2 L_{22}\|_2$, the source takes $U_2 = U(:, r{+}1{:}m)$,
  which does not match the $n - r$ rows of $L_{22}$. The columns $r{+}1{:}n$ of $U$ are meant; in
  both readings the norm is $\|L_{22}\|_2$. See `GolubVanLoan.Chapter06.ulv_nullspace_norm`.

**Chapter 7: Unsymmetric eigenvalue problems**

* **Equations (7.1.1)–(7.1.3)** (reading). The radius and abscissa use suprema and take value
  zero in dimension zero, where the maxima in the source are undefined. See
  `GolubVanLoan.Chapter07.spectralRadius`, `GolubVanLoan.Chapter07.spectralAbscissa` and
  `GolubVanLoan.Chapter07.numericalRadius`.
* **Lemma 7.1.1** (reading). The characteristic polynomial identity gives multiplicities and
  establishes spectral equality without the source's counting argument for sets. See
  `GolubVanLoan.Chapter07.lemma_7_1_1`.
* **Corollary 7.1.7** (reading). The block-size data permit empty blocks. Removing these gives
  the decomposition into eigenvalue blocks. See `GolubVanLoan.Chapter07.corollary_7_1_7`.
* **Equation (7.1.3)** (typo). The source prints the maximum as $\max_{\lambda \in \lambda(A)}$. The
  maximum is over the unit vectors $x$. See `GolubVanLoan.Chapter07.numericalRadius`.
* **Lemma 7.1.5, block diagonalization** (generalization). The source assumes that $\phi$ is
  nonsingular. The statement needs only a solution $Z$ of $\phi(Z) = -T_{12}$. See
  `GolubVanLoan.Chapter07.lemma_7_1_5_blockDiagonal`.
* **Theorem 7.1.6** (generalization). The theorem uses a block upper triangular form whose
  diagonal blocks can be arbitrary square matrices. The source assumes a Schur decomposition.
  See `GolubVanLoan.Chapter07.theorem_7_1_6`.
* **Equation (7.1.13)** (reading). The source says that the diagonalizing matrix has "a 2-norm
  condition of order $1/\varepsilon$". The statement gives the lower bound $1/(2\varepsilon)$ for
  every diagonalizing matrix and the upper bound $1/\varepsilon + 2\varepsilon$ for one of them. See
  `GolubVanLoan.Chapter07.equation_7_1_13`.

* **§7.2.2** (typo). The source interchanges $x$ and $y$ when assigning them to columns of the
  right and left Jordan bases. See `GolubVanLoan.Chapter07.inner_ne_zero_of_simple`.
* **Equation (7.2.2), derivative argument** (reading). The assertion states differentiability at
  the origin and bounds the derivative for an arbitrary perturbation direction, scaled by its
  norm. See `GolubVanLoan.Chapter07.equation_7_2_2`.
* **Theorem 7.2.4 and Corollary 7.2.5** (generalization). The separation and invariant-subspace
  bounds apply to upper block triangular matrices with arbitrary diagonal blocks. See
  `GolubVanLoan.Chapter07.theorem_7_2_4` and `GolubVanLoan.Chapter07.corollary_7_2_5`.
* **Theorem 7.2.3** (generalization). The source takes a Schur decomposition, with $N$ strictly
  upper triangular, and the least $p$ with $|N|^p = 0$. The theorem holds for every $p \ge 1$ with
  $|N|^p = 0$ and every such $N$. See `GolubVanLoan.Chapter07.theorem_7_2_3`.
* **§7.2.3** (reading). The source says that the rate of change of the eigenvalues at the origin is
  infinite. The statement reads this as: no branch of eigenvalues is differentiable at
  $\varepsilon = 0$. See `GolubVanLoan.Chapter07.repeated_eigenvalue_example`.

* **§7.3.2, dominant invariant subspace** (generalization). The diagonal blocks may be arbitrary
  matrices with strictly separated spectral moduli. Disjoint spectra alone suffice to identify
  the leading span with a sum of generalized eigenspaces. See
  `GolubVanLoan.Chapter07.dominantInvariantSubspace_unique` and
  `GolubVanLoan.Chapter07.span_leading_schurVectors_eq`.
* **Equations (7.3.1)–(7.3.2)** (generalization). The similarity identity allows arbitrary
  second factors $R_k$. See `GolubVanLoan.Chapter07.equation_7_3_2`.
* **Equations (7.3.3), (7.3.5) and §7.3.1** (generalization). The power method also accepts real
  matrices and defines a zero iterate when normalization encounters zero. The rate assumes an
  eigenvector expansion of the initial vector and allows any bound on the nondominant moduli.
  The backward error gives a minimum over perturbations. See
  `GolubVanLoan.Chapter07.powerMethod`, `GolubVanLoan.Chapter07.equation_7_3_5`,
  `GolubVanLoan.Chapter07.powerMethod_dist` and
  `GolubVanLoan.Chapter07.powerMethod_backwardError`.
* **Equation (7.3.6) and §7.3.2** (reading). The iterate predicate records the QR sequence,
  including the empty-width case. The range theorem assumes full column rank of $A^kQ_0$ and
  gives first-column agreement with power iteration up to a unit-modulus phase. See
  `GolubVanLoan.Chapter07.orthogonalIteration` and
  `GolubVanLoan.Chapter07.orthogonalIteration_range`.
* **Equations (7.3.23)–(7.3.25)** (generalization). The factor bound accepts any square factor
  with $GG^H=I+XX^H$. The invariant-subspace theorem also gives the complementary right
  identity. See `GolubVanLoan.Chapter07.equation_7_3_24` and
  `GolubVanLoan.Chapter07.equation_7_3_25`.
* **Equation (7.3.26)** (typo). The displayed definition of $Z$ has $r$ columns. The source
  labels it as $n$ by $n-r$. See `GolubVanLoan.Chapter07.equation_7_3_26`.
* **Theorem 7.3.1** (correction). The printed bound is false. The theorem assumes
  $\operatorname{dist}(D_r(A^H), \operatorname{ran}(Q_0)) < 1$ in place of (7.3.9) and has this
  distance in the denominator. See `GolubVanLoan.Chapter07.theorem_7_3_1` and
  `GolubVanLoan.Chapter07.theorem_7_3_1_counterexample`.
* **Theorem 7.3.1** (generalization). Any bounds $a \le |\lambda_r|$, $b \ge |\lambda_{r+1}|$ with
  $b < a$, and $\nu \ge \|N\|_F$ can replace the source's $|\lambda_r|$, $|\lambda_{r+1}|$ and
  $\|N\|_F$. See `GolubVanLoan.Chapter07.theorem_7_3_1`.
* **Equation (7.3.26)** (correction). The source ends the chain of inequalities with $d_0 =
  \operatorname{dist}(D_r(A), \operatorname{ran}(Q_0))$ through the false claim
  $\operatorname{ran}(Q_\beta) = D_r(A^H)^\perp$. The statement ends it with
  $\operatorname{dist}(D_r(A^H), \operatorname{ran}(Q_0))$. See
  `GolubVanLoan.Chapter07.equation_7_3_26`.
* **Lemma 7.3.2** (typo). The last display of the source writes $|\mu|$ for $|\lambda_{\min}|$. See
  `GolubVanLoan.Chapter07.lemma_7_3_2`.
* **Equations (7.3.12)–(7.3.14)** (reading). The source starts treppeniteration from
  $G_0 \in \mathbb{C}^{n \times r}$ of rank $r$. The statement takes $r = n$ and $G_0 = L_0$ unit
  lower triangular. See `GolubVanLoan.Chapter07.equation_7_3_14`.

* **Algorithm 7.4.2** (reading). The program returns the compact storage array and a separate
  list of reflector vectors and coefficients. The upper Hessenberg part of the array is $H$. See
  `GolubVanLoan.Chapter07.algorithm_7_4_2`.
* **§7.4.3, rounding analysis** (reading). The source states a bound with an unspecified
  constant times $n^2u$. The theorem gives an explicit nested $\gamma$ bound with idempotent
  rounding and quantitative smallness assumptions. See
  `GolubVanLoan.Chapter07.algorithm_7_4_2_rounding`.
* **Theorem 7.4.2** (generalization). The first part allows any prefix with nonzero subdiagonal
  entries. The essential-uniqueness statement requires only one unreduced output. See
  `GolubVanLoan.Chapter07.theorem_7_4_2` and `GolubVanLoan.Chapter07.theorem_7_4_2_essential`.
* **Theorem 7.4.4** (typo). The proof's rank calculation concerns $H - \lambda I$, printed as $A
  - \lambda I$. See `GolubVanLoan.Chapter07.theorem_7_4_4`.
* **Equation (7.4.4)** (generalization). The identity $AK=KC$ needs only a solution of $Kc=-A^n
  x$. Nonsingularity is required for the similarity conclusion. See
  `GolubVanLoan.Chapter07.equation_7_4_4`.

* **§7.5.4, real double shift** (reading). The canonical QR factors give a real result for a
  nonsingular conjugate pair of shifts. Arbitrary factors give diagonal unitary similarity. The
  source also allows two distinct real shifts. See `GolubVanLoan.Chapter07.double_shift_real`.
* **Algorithm 7.5.1** (generalization). The program takes a consecutive window and returns its
  Householder data. Windows with fewer than three indices are left unchanged. See
  `GolubVanLoan.Chapter07.algorithm_7_5_1`.
* **§7.5.5, essential uniqueness** (reading). The comparison with the explicit step assumes a
  nonsingular shift polynomial and takes its canonical QR factors. The source assumes that both
  output Hessenberg matrices are unreduced and that the orthogonal factors share their first
  column. See `GolubVanLoan.Chapter07.algorithm_7_5_1_essential`.
* **Algorithm 7.5.2** (reading). The program always returns $Q$ and exposes a pass budget and
  completion flag. The source also describes an eigenvalues-only mode that skips transformations
  outside the active diagonal block. See `GolubVanLoan.Chapter07.algorithm_7_5_2`.
* **(7.5.3) and (7.5.6)–(7.5.7)** (generalization). The source takes the factorizations to be QR
  factorizations. The identities hold for any second factor $R$, $R_1$, $R_2$. See
  `GolubVanLoan.Chapter07.equation_7_5_3` and `GolubVanLoan.Chapter07.equation_7_5_7`.
* **§7.5.2, the rate of the fixed-shift iteration** (reading). The source states the rate
  $|(\lambda_{p+1} - \mu)/(\lambda_p - \mu)|^k$ by reference to the theory of §7.3. The theorem
  assumes a diagonalizable $A$ with real eigenvalues, distinct nonzero $|\lambda_i - \mu|$ and a
  general-position condition, and it gives the bound $C (r / |\lambda_p - \mu|)^k$ for every
  $r > |\lambda_{p+1} - \mu|$. See `GolubVanLoan.Chapter07.shiftedQr_rate`.
* **§7.5.3, the quadratic convergence** (reading). The source says that if $h_{n,n-1}$ converges to
  zero, it is likely to do so at a quadratic rate. The theorem is a local bound near an
  algebraically simple real eigenvalue. See `GolubVanLoan.Chapter07.single_shift_quadratic`.
* **§7.5.5, the essential uniqueness of the Francis step** (typo). The source cites "Theorem 7.4.3"
  for the implicit Q theorem, which is Theorem 7.4.2. See
  `GolubVanLoan.Chapter07.algorithm_7_5_1_essential`.
* **Algorithm 7.5.2, the last step** (reading). The source gives no algorithm to upper triangularize
  the $2 \times 2$ diagonal blocks with real eigenvalues. The library uses one Givens rotation built
  from an eigenvector of the block. See `GolubVanLoan.Chapter07.triangularize2x2`.
* **Algorithm 7.5.2** (reading). The source says that the algorithm computes the real Schur form
  $Q^T A Q = T$. The deflations set nonzero entries to zero, so in exact arithmetic the theorem
  states $T = Q^T (A + E) Q$ with a bound on $\|E\|_F$, and $E = 0$ if $\mathrm{tol} = 0$. See
  `GolubVanLoan.Chapter07.algorithm_7_5_2_spec`.

* **§7.6.2, two-by-two swap** (generalization). The matrix identity includes equal diagonal
  entries and gives exactly $t_{12}$ for the off-diagonal entry in the stated rotation
  convention. See `GolubVanLoan.Chapter07.swap_two_by_two`.
* **Algorithm 7.6.1** (reading). The implementation takes a pass budget, and the correctness
  theorem assumes at least $n$ passes are available. See
  `GolubVanLoan.Chapter07.algorithm_7_6_1`.
* **Equation (7.6.5)** (generalization). The recurrences allow arbitrary $F$ and upper
  Hessenberg $G$ with the necessary local subdiagonal zeros. See
  `GolubVanLoan.Chapter07.equation_7_6_5`.
* **Equation (7.6.6)** (generalization). The separation bounds apply to complex blocks, with
  positivity explicitly required for the solution norm bound. See
  `GolubVanLoan.Chapter07.equation_7_6_6`.
* **§7.6.5** (generalization). The Jordan block count applies to any one eigenvalue of a complex
  matrix even when other eigenvalues are present. See
  `GolubVanLoan.Chapter07.jordan_block_count`.
* **Equation (7.6.1)** (reading). The source describes the convergence of inverse iteration
  informally; the statement fixes a precise form, in which $A$ need not be diagonalizable. See
  `GolubVanLoan.Chapter07.equation_7_6_1`.
* **Equation (7.6.1)** (generalization). Inverse iteration is defined over any `RCLike` field, not
  only over $\mathbb{R}$. See `GolubVanLoan.Chapter07.inverseIteration`.
* **Equation (7.6.2)** (reading). The source leaves the factor $\sqrt{n}$ in the bound on the
  perturbation implicit; the statement makes it explicit. See
  `GolubVanLoan.Chapter07.equation_7_6_2`.
* **§7.6.2, unique invariant subspace** (generalization). The source has a real orthogonal $Q$; the
  statement has a complex unitary $Q$, of which the real case is an instance. See
  `GolubVanLoan.Chapter07.invariantSubspace_leading_unique`.
* **Algorithm 7.6.1** (reading). The test $\{t_{11}, \dots, t_{pp}\} = \Delta$ is read with
  multiplicities: the diagonal entries in $\Delta$ come first. See
  `GolubVanLoan.Chapter07.algorithm_7_6_1_spec`.
* **Algorithm 7.6.3** (reading). The source applies Algorithm 7.6.2, which it states for triangular
  matrices only, to the blocks of a quasi-triangular $T$; the specification assumes $T$ upper
  triangular. See `GolubVanLoan.Chapter07.algorithm_7_6_3_spec`.
* **§7.6.3, condition of $Y_{ij}$** (correction). The source prints
  $\kappa_F(Y_{ij}) = n_i^2 + n_j^2 + \|Z\|_F^2$; the value is $n_i + n_j + \|Z\|_F^2$, because
  $\|I_k\|_F^2 = k$. See `GolubVanLoan.Chapter07.kappaF_blockUnit`.
* **§7.6.4** (generalization). The identities hold without the hypothesis $\lambda \notin
  \lambda(T_{11}) \cup \lambda(T_{33})$, which the source needs only to solve for $w$ and $z$. See
  `GolubVanLoan.Chapter07.schur_eigenvectors`.

* **§7.7.1, the pencil eigenvalue count** (reading).
  `GolubVanLoan.Chapter07.pencilSpectrum_card` states degree of the determinant polynomial,
  which counts eigenvalues with multiplicity when the determinant polynomial is nonzero.
* **§7.7.5, the zero chase** (typo). The penultimate source diagram prints $BZ_{34}^T$ alongside
  $AZ_{34}$. `GolubVanLoan.Chapter07.qzZeroChase` applies the same right factor to both arrays.
* **Algorithm 7.7.2** (reading). `GolubVanLoan.Chapter07.algorithm_7_7_2` acts on a window and
  returns reflector lists. Its exact full-window theorem uses an order of at least three and
  compares with the Francis polynomial-factorization condition. The product on the left of the
  source's similarity relation is the updated $\bar A\bar B^{-1}$.
* **Algorithm 7.7.3** (reading). `GolubVanLoan.Chapter07.algorithm_7_7_3` always accumulates
  both orthogonal factors and returns a stop flag after bounded work. Its exact specification
  bounds threshold deflations of $A$ in Frobenius norm and gives quasi-triangular $T$ upon
  stopping.
* **Equations (7.7.5)–(7.7.6)** (reading). `GolubVanLoan.Chapter07.equation_7_7_5` corrects
  missing factors of $x$ in the elimination and proves the converse kernel relation.
  `GolubVanLoan.Chapter07.equation_7_7_6` establishes the factorization for all coefficients,
  including cases where the leading coefficient vanishes.
* **§7.7.8, generalized inverse iteration** (typo). The source prints the eigenvalue estimate as
  $\lambda^{(k)} = q^{(k)H} A q^{(k)} / q^{(k)H} A q^{(k)}$; the denominator is
  $q^{(k)H} B q^{(k)}$. See `GolubVanLoan.Chapter07.generalizedInverseIteration_eq`.

* **Figure 7.8.1, orthogonal-symplectic row** (reading).
  `GolubVanLoan.Chapter07.figure_7_8_1_orthogonalSymplectic` takes orthogonality explicitly when
  characterizing symplecticity by $JQ=QJ$.
* **§7.8.1, structured vector reduction** (generalization).
  `GolubVanLoan.Chapter07.symplectic_householder_givens` allows any repeated orthogonal block
  and any target coordinate in the first block.
* **Equations (7.8.1)–(7.8.2)** (reading). `GolubVanLoan.Chapter07.equation_7_8_1` includes the
  stable ordering of $T$ specified in the Riccati discussion.
  `GolubVanLoan.Chapter07.equation_7_8_2` derives symmetry from the cross Gram identity and uses
  the block transformation without assuming symmetry of $F$ and $G$.
* **§7.8.2, perfect shuffle display** (typo). The source repeats the same permutation matrix on
  both sides. `GolubVanLoan.Chapter07.blockCyclic_shuffle_isUpperHessenberg` uses simultaneous
  row and column reindexing, equivalent to a permutation similarity.

* **Equation (7.9.5), closed level set** (reading). `GolubVanLoan.Chapter07.pseudospectrum`
  takes the nonstrict inequality. With a positive tolerance the two conventions can differ at
  boundary points, even for the scalar zero matrix.
* **Equation (7.9.7)** (reading). `GolubVanLoan.Chapter07.equation_7_9_7` makes the source’s
  implicit existential perturbation quantifier explicit.
* **Theorem 7.9.2, proof** (typo). The rightmost factor of the resolvent similarity is $X$, not
  the printed $X^{-1}$. See `GolubVanLoan.Chapter07.theorem_7_9_2`.
* **Theorem 7.9.8 and §7.9.5** (reading). `GolubVanLoan.Chapter07.theorem_7_9_8` uses the least
  singular value everywhere and the reciprocal resolvent only off the spectrum.
  `GolubVanLoan.Chapter07.sigmaMin_schur` does not require a triangular transformed matrix for
  the stated identities.
* **Equations (7.9.8)–(7.9.9)** (reading). `GolubVanLoan.Chapter07.pseudospectralAbscissa` and
  `GolubVanLoan.Chapter07.pseudospectralRadius` use real suprema. Attainment is proved for
  nonempty matrices and nonnegative tolerance.
* **Equations (7.9.10)–(7.9.11)** (reading). The ray eigenvalue and singular value
  correspondence is bidirectional for positive tolerance. The transient growth estimate uses
  arbitrary real uniform upper bounds in place of a supremum.
* **(7.9.5)** (typo). The source writes $\lambda$ for $z$ inside the set-builder. See
  `GolubVanLoan.Chapter07.pseudospectrum`.
* **(7.9.6)** (reading). The resolvent form is stated for $\varepsilon > 0$ with
  $\lambda(A) \subseteq \Lambda_\varepsilon(A)$ explicit, since
  $\|(zI - A)^{-1}\|_2 \ge 1/\varepsilon$ has no meaning at an eigenvalue. See
  `GolubVanLoan.Chapter07.equation_7_9_6`.
* **(7.9.1)** (reading). The source says that $A^k$ decays "like $\rho(A)^k$"; the theorem states
  Gelfand's formula and a bound $C(\rho(A) + \varepsilon)^k$. See
  `GolubVanLoan.Chapter07.equation_7_9_1`.
* **(7.9.3)** (generalization). The source derives the formula from (7.9.2) under
  $\lambda_1 \neq \lambda_2$; it holds without this hypothesis. See
  `GolubVanLoan.Chapter07.equation_7_9_3`.
* **§7.9.1, the power bound of the $2 \times 2$ example** (correction). The source states the bound
  for any $\varepsilon > 0$; at $k = 0$ it reads $1 \le M/\varepsilon$, so $\varepsilon \le M$ is
  needed. See `GolubVanLoan.Chapter07.two_by_two_power_bound`.

**Chapter 8: Symmetric eigenvalue problems**

* **§8.1.1, the Rayleigh quotient and Theorem 8.1.2** (reading).
  `GolubVanLoan.Chapter08.rayleighQuotient` has a total value at the zero vector, and
  `GolubVanLoan.Chapter08.theorem_8_1_2_minmax` gives the dual of the source’s max–min
  statement.
* **Equation (8.1.2) and Problem P8.1.9** (correction). `GolubVanLoan.Chapter08.sepSymm_eq_sep`
  compares spectral separation to the Sylvester-operator minimum on the Frobenius unit sphere.
  The printed unconstrained minimum includes $X=0$.
* **Theorems 8.1.13–8.1.14** (reading). `GolubVanLoan.Chapter08.theorem_8_1_13_weak` bounds one
  projected eigenvalue with factor one. `GolubVanLoan.Chapter08.theorem_8_1_14` gives the
  Frobenius residual minimum for arbitrary real $A$.
* **Equations (8.1.5)–(8.1.7)** (correction). The intermediate norms use $Q-X_1$ and
  $X_1^TX_1-I_r$. `GolubVanLoan.Chapter08.equation_8_1_7` uses the full singular-value deviation
  from one, correcting the printed equality with the smallest singular value alone.
* **Theorem 8.1.3** (generalization). The source assumes that $A$ is symmetric. The inclusion holds
  for the real eigenvalues of every real $A$. See `GolubVanLoan.Chapter08.theorem_8_1_3`.
* **Theorem 8.1.7** (generalization). The source assumes that $A$ is symmetric. Only the leading
  principal submatrices $A(1{:}r, 1{:}r)$ and $A(1{:}r{+}1, 1{:}r{+}1)$ need to be symmetric. See
  `GolubVanLoan.Chapter08.theorem_8_1_7`.
* **Theorem 8.1.8** (generalization). The source normalizes $\|c\|_2 = 1$. The interlacing holds for
  every $c$. See `GolubVanLoan.Chapter08.theorem_8_1_8`.
* **Theorem 8.1.10 and Corollary 8.1.11** (generalization). The theorems do not need $E$ to be
  symmetric, and they hold for every symmetric square root of $I + P^T P$. See
  `GolubVanLoan.Chapter08.theorem_8_1_10`.
* **Theorem 8.1.12** (generalization). The source assumes that $A + E$ is symmetric. Only $A$ needs
  to be symmetric. See `GolubVanLoan.Chapter08.theorem_8_1_12`.
* **Theorem 8.1.13** (reading). The source says that there exist
  $\mu_1, \dots, \mu_r \in \lambda(A)$. The theorem gives $\mu_k = \lambda_{\sigma(k)}(A)$ for an
  injective $\sigma$, as the proof of the source produces them. See
  `GolubVanLoan.Chapter08.theorem_8_1_13`.
* **Theorem 8.1.15** (generalization). The source takes $Q_1$ with orthonormal columns. The identity
  and the bound hold for every $Q_1$. See `GolubVanLoan.Chapter08.theorem_8_1_15`.
* **Equation (8.1.5)** (generalization). The source takes $Q$ with orthonormal columns. The bound
  holds for every $Q$. See `GolubVanLoan.Chapter08.equation_8_1_5`.
* **Theorem 8.1.16** (reading). As in Theorem 8.1.13, the eigenvalues $\mu_k$ are
  $\lambda_{\sigma(k)}(A)$ for an injective $\sigma$. See `GolubVanLoan.Chapter08.theorem_8_1_16`.
* **§8.2.1, residual error estimate** (reading).
  `GolubVanLoan.Chapter08.powerMethod_residual_bound` proves the factor-one estimate as well as
  the printed $\sqrt2$ estimate.
* **§8.2.2–§8.2.3** (reading). `GolubVanLoan.Chapter08.inverseIteration_expansion` requires a
  shift outside the spectrum. `GolubVanLoan.Chapter08.rayleighQuotientIteration` is total at a
  singular shifted solve. The residual minimizer theorem applies to nonsymmetric real $A$ as
  well.
* **Theorem 8.2.2, final line of the proof** (typo). The theorem's bound and Lean both contain
  $1/\sqrt{1-d_0^2}$. The source proof's final line omits the square root.
* **§8.2.5, subspace and diagonal convergence** (reading).
  `GolubVanLoan.Chapter08.orthogonalIteration_gap_le_of_forall` gives the explicit finite-step
  gap estimate. `GolubVanLoan.Chapter08.qrIterate_tendsto_diagonal` uses canonical QR from the
  identity basis, assumes nonzero eigenvalues, and specifies each diagonal limit.
* **Equations (8.2.1)–(8.2.2)** (generalization). The source takes $U_0$ orthogonal. The similarity
  $T_k = (U_0 \cdots U_k)^T A (U_0 \cdots U_k)$ and the symmetry of $T_k$ hold for every $U_0$, and
  the $R_k$ need not be upper triangular. See `GolubVanLoan.Chapter08.equation_8_2_2`.
* **Proof of Theorem 8.2.1** (typo). The final bound uses the maximum of $|\lambda_1-\lambda_i|$,
  as in (8.2.5). The proof prints $\lambda_n$ inside that maximum. See
  `GolubVanLoan.Chapter08.theorem_8_2_1_b`.
* **Equation (8.2.7)** (correction). The source omits the hypothesis $c_k s_k \neq 0$; without it
  $\mu_k$ is an eigenvalue and the step is not defined. See `GolubVanLoan.Chapter08.equation_8_2_7`.
* **Equation (8.2.7)** (typo). The source loses the minus sign: the next iterate is
  $(c_k^3, -s_k^3)/\sqrt{c_k^6 + s_k^6}$. See `GolubVanLoan.Chapter08.equation_8_2_7`.
* **Equation (8.2.13)** (typo). The source defines both $V_k$ and $W_k$ with $Q_0$;
  $V_k = Q_\alpha^T Q_k$ and $W_k = Q_\beta^T Q_k$ are meant. See
  `GolubVanLoan.Chapter08.equation_8_2_13`.
* **§8.3.1, the rank-two update** (generalization).
  `GolubVanLoan.Chapter08.householder_conj_eq_sub_rankTwo` proves the algebraic formula before
  requiring a Householder coefficient.
* **Algorithm 8.3.2, implicit versus explicit step** (reading).
  `GolubVanLoan.Chapter08.algorithm_8_3_2_spec` proves the explicit-step comparison up to
  diagonal signs under shifted nonsingularity.
* **Equation (8.3.6)** (generalization). `GolubVanLoan.Chapter08.IsRitzAcceleration` accepts any
  real $A$ for which the iterate data include an orthogonal diagonalization of each projected
  matrix.
* **Equation (8.3.1) and Algorithm 8.3.1** (reading). The tridiagonal reduction fixes the first
  coordinate vector. `GolubVanLoan.Chapter08.algorithm_8_3_1` keeps the reflectors separately
  and mirrors the lower-triangular trailing update. Its rounding theorem gives a dimension-
  dependent explicit coefficient under stated rounding-model hypotheses.
* **Theorem 8.3.1 and the spectral split** (generalization).
  `GolubVanLoan.Chapter08.theorem_8_3_1` uses a tridiagonal reduction without requiring
  symmetry. `GolubVanLoan.Chapter08.tridiagonal_spectrum_split` uses vanishing couplings on both
  sides and retains multiplicities.
* **Equation (8.3.2)** (reading). `GolubVanLoan.Chapter08.explicitShiftedQR` uses the canonical
  QR decomposition, a rule depending on the current iterate, and a supplied initial matrix. The
  associated theorem states orthogonal similarity and symmetry for any symmetric start.
* **Algorithms 8.3.2–8.3.3** (reading). The implicit step accepts a working window and
  accumulates rotations. The outer algorithm uses a finite pass budget and always accumulates
  the orthogonal factor. Its error and eigenvalue results are exact-arithmetic estimates for
  threshold deflations, conditional on the stop flag where diagonalization is needed.
* **§8.3.6, the Rayleigh quotient connection** (reading).
  `GolubVanLoan.Chapter08.rayleigh_qr_connection` makes the shifted solve’s nonsingularity
  explicit and gives the next iterate up to the sign of $r_{nn}$.
* **§8.3.7, Ritz acceleration** (reading). `GolubVanLoan.Chapter08.ritzAcceleration_residual`
  formalizes the residual minimum over coefficient matrices in the selected subspace, with
  invariance under its Ritz rotation.
* **§8.3.3, preservation of form** (correction). The source states it for every QR factorization
  $T = QR$. For singular $T$ the orthogonal factor is not unique ($T = 0 = Q \cdot 0$ for every
  orthogonal $Q$), and the claim fails. The statements assume that $T$ (or $T - sI$) is nonsingular
  or that $(Q, R)$ is the Givens QR factorization. See
  `GolubVanLoan.Chapter08.qr_tridiagonal_preservation` and
  `GolubVanLoan.Chapter08.shifted_qr_tridiagonal`.
* **Equation (8.3.3)** (reading). The source does not fix $\operatorname{sign}(0)$. Lean uses
  $\operatorname{sign}(0) = 1$ to select one of the two equally close eigenvalues when $d=0$.
  See `GolubVanLoan.Chapter08.wilkinsonShift`.
* **Theorem 8.3.2** (generalization). The source assumes that $A$ is symmetric and that $T$ and
  $S$ are tridiagonal. The Lean theorem only needs the latter assumption. See
  `GolubVanLoan.Chapter08.theorem_8_3_2`.
* **Lemma 8.4.2 and Theorem 8.4.3(a), (c)** (generalization).
  `GolubVanLoan.Chapter08.lemma_8_4_2` and `GolubVanLoan.Chapter08.theorem_8_4_3` need distinct
  diagonal entries, without sorting them. The secular roots are taken away from the poles of the
  source formula.
* **§8.4.3, final line of Theorem 8.4.3's proof** (typo). The rank-one update is $D+\rho zz^T$,
  where the source writes $D+\rho vv^T$.
* **Equations (8.4.10)–(8.4.11)** (reading). `GolubVanLoan.Chapter08.equation_8_4_10` states the
  general resolvent and determinant identities for points outside the spectrum of $T$. The
  source uses the special case where the trailing principal block has the point as an
  eigenvalue.
* **§8.4.6, inverse eigenvalue construction** (reading).
  `GolubVanLoan.Chapter08.inverseTridiagonal_exists` states existence with the two
  characteristic polynomials and their multiplicities. The source gives construction steps.
* **§8.4.1, bisection loop** (reading). In exact arithmetic the first bisection loop need not
  terminate when the bracketed zero is $0$. The declaration states one step of the loop. See
  `GolubVanLoan.Chapter08.bisection_bracket`.
* **Theorem 8.4.1** (correction). The source says that $a(\lambda)$ is the number of eigenvalues
  less than $\lambda$. With the sign convention of the source, $a(\lambda)$ is the number of
  eigenvalues $\le \lambda$; the two numbers differ exactly when $\lambda$ is an eigenvalue. See
  `GolubVanLoan.Chapter08.theorem_8_4_1_b`.
* **(8.4.3)** (correction). The source tests $a(x) \ge n - k$. The correct test is
  $a(x) \ge n - k + 1$. See `GolubVanLoan.Chapter08.equation_8_4_3`.
* **Theorem 8.4.4** (correction). The source claims $\mu_r \ge \mu_{r+1}$ across the deflation
  boundary. This is false for $d = (2, 1)$ and $z = (0, 1)$. The declaration orders the two parts
  separately. See `GolubVanLoan.Chapter08.theorem_8_4_4`.
* **(8.4.6)** (generalization). The source takes $\theta \in \{-1, 1\}$. The identity holds for
  every real $\theta$. See `GolubVanLoan.Chapter08.equation_8_4_6`.
* **(8.4.6)–(8.4.7)** (typo). The source prints $a_m$ for $\alpha_m$ and a stray $\lambda'_{n-1}$.
  See `GolubVanLoan.Chapter08.equation_8_4_6` and `GolubVanLoan.Chapter08.equation_8_4_12`.
* **(8.4.12)** (typo). The product in the denominator runs over $j \ne k$, $j = 1, \dots, n$. See
  `GolubVanLoan.Chapter08.equation_8_4_12`.
* **Equation (8.5.1)** (generalization). `GolubVanLoan.Chapter08.equation_8_5_1` is a block
  identity for every $c,s$ and any distinct $p,q$, before imposing orthogonality or an ordering.
* **Equation (8.5.3) and the chosen root** (reading). `GolubVanLoan.Chapter08.equation_8_5_3`
  follows the printed formula, which selects a root of smaller absolute value.
* **Algorithms 8.5.2–8.5.3** (reading). `GolubVanLoan.Chapter08.algorithm_8_5_2` and
  `GolubVanLoan.Chapter08.algorithm_8_5_3` take fuel and return a stop flag. The classical pivot
  selects the first maximizer in the upper triangle. Their exact specifications make the
  stopping guarantee conditional on the flag, and
  `GolubVanLoan.Chapter08.algorithm_8_5_2_terminates` supplies a sufficient classical budget for
  the output to meet tolerance.
* **§8.6.4, one-sided Jacobi cross-reference** (typo). The printed P8.6.8 is P8.6.6. See
  `GolubVanLoan.Chapter08.oneSidedJacobi_orthogonal`.
* **Theorem 8.6.1 and Corollaries 8.6.2–8.6.3** (reading).
  `GolubVanLoan.Chapter08.theorem_8_6_1` expresses the extremal quotients through homogeneous
  bounds. The corollaries use zero padding to cover arbitrary indices and rectangular
  dimensions.
* **Algorithm 8.6.1** (reading). `GolubVanLoan.Chapter08.algorithm_8_6_1_spec` states agreement
  with the exact shifted QR step up to diagonal signs for the full window when the shifted Gram
  matrix is invertible.
* **Algorithm 8.6.2** (reading). `GolubVanLoan.Chapter08.algorithm_8_6_2` bounds the number of
  passes and returns a stop flag. The final zero diagonal of a window uses the column chase from
  the preceding discussion. `GolubVanLoan.Chapter08.algorithm_8_6_2_spec` and
  `GolubVanLoan.Chapter08.algorithm_8_6_2_forward` bound exact-arithmetic threshold deflations
  in Frobenius norm, with diagonal output conditional on stopping.
* **§8.6.4, one-sided Jacobi** (reading). `GolubVanLoan.Chapter08.oneSidedJacobi_orthogonal`
  scales nonzero columns to unit norm and leaves zero columns without an orthonormal completion.
* **Theorem 8.6.5** (typo). The source swaps $P$ and $Q$: its $Q$ is $(n - r) \times r$. See
  `GolubVanLoan.Chapter08.theorem_8_6_5`.
* **Theorem 8.6.5** (correction). As printed, the theorem is false for $m > n$. For $m > n$ the
  declaration adds Wedin's condition $\delta \le \sigma_{\min}(A_{11})$. See
  `GolubVanLoan.Chapter08.theorem_8_6_5` and `GolubVanLoan.Chapter08.theorem_8_6_5_counterexample`.
* **Algorithm 8.6.1** (typo). The source says $B \in \mathbb{R}^{m \times n}$ for a square $B$. See
  `GolubVanLoan.Chapter08.algorithm_8_6_1`.
* **§8.7.2, Cholesky spectrum** (reading). `GolubVanLoan.Chapter08.pencil_eq_cholesky_spectrum`
  combines the source’s Cholesky spectral identity with identification of the output of an exact
  Schur routine.
* **Equation (8.7.5)** (reading). `GolubVanLoan.Chapter08.generalizedRayleighQuotientIteration`
  uses totalized inversion and returns zero at a singular shifted solve or zero normalization
  direction.
* **§8.7.4, GSVD pencil consequences** (reading).
  `GolubVanLoan.Chapter08.gsvd_columns_and_pencil` assumes the corresponding $\beta_k\neq 0$ for
  each finite generalized eigenvalue and assumes all denominators are nonzero to identify the
  full finite spectrum.
* **Algorithm 8.7.2 and the following RQ discussion** (typo).
  `GolubVanLoan.Chapter08.algorithm_8_7_2_spec` uses $D_B\in\mathbb{R}^{m_2\times n}$,
  correcting the printed $m_1$. `GolubVanLoan.Chapter08.gsvd_subspace_via_rq` uses $X=R^{-1}V$,
  as follows from $RX=V$.
* **§8.7.9, quadratic eigenvalue problems** (generalization).
  `GolubVanLoan.Chapter08.equation_8_7_13`, `GolubVanLoan.Chapter08.equation_8_7_15`, and
  `GolubVanLoan.Chapter08.qep_re_nonpos` allow complex coefficient matrices. The discriminant
  identity avoids division by $x^H Mx$, and `GolubVanLoan.Chapter08.palindromic_reciprocal`
  restricts the reciprocal to nonzero finite values.
* **Equation (8.7.4)** (correction). The source's display of the Crawford number has no square root.
  The definition takes the square root, which the ratio $\epsilon / c(A, B)$ of Theorem 8.7.3 needs.
  See `GolubVanLoan.Chapter08.crawfordNumber`.
* **Theorem 8.7.3** (correction). The printed bound $|\arctan \lambda_i - \arctan \mu_i| \le
  \arctan(\epsilon / c(A, B))$ is false. The library proves $\sin |\arctan \lambda_i - \arctan
  \mu_i| \le \epsilon / c(A, B)$ and assumes that $B + E_B$ is positive definite. See
  `GolubVanLoan.Chapter08.theorem_8_7_3` and `GolubVanLoan.Chapter08.theorem_8_7_3_counterexample`.
* **Algorithm 8.7.1** (typo). The source cites Algorithm 4.2.2 for the Cholesky factorization. The
  intended algorithm is Algorithm 4.2.1. See `GolubVanLoan.Chapter08.algorithm_8_7_1`.
* **Algorithm 8.7.2** (typo). The source writes the hypothesis as $\operatorname{null}(A) \cap
  \operatorname{null}(B) = \emptyset$. The intended hypothesis is $\operatorname{null}(A) \cap
  \operatorname{null}(B) = \{0\}$. See `GolubVanLoan.Chapter08.algorithm_8_7_2_spec`.
* **§8.7.7** (typo). The source prints $U_1^T F = (U_2^T G) \Sigma$. The correct identity is
  $U_1^T F = \Sigma (U_2^T G)$. See `GolubVanLoan.Chapter08.kogbetliantz_twoByTwo`.
* **§8.7.9, gyroscopic systems** (correction). The source says that the eigenvalues are purely
  imaginary. This holds only when $K$ is positive semidefinite, which the library assumes. See
  `GolubVanLoan.Chapter08.gyroscopic_eigenvalues_imaginary` and
  `GolubVanLoan.Chapter08.gyroscopic_counterexample`.

**Chapter 9: Functions of matrices**

* **Equations (9.1.3), (9.1.4), and (9.1.6)** (reading).
  `GolubVanLoan.Chapter09.equation_9_1_3`, `GolubVanLoan.Chapter09.equation_9_1_4`, and
  `GolubVanLoan.Chapter09.equation_9_1_6` apply to total primary functional calculus and total
  iterated derivatives. The source assumes the required derivative evaluations exist.
* **Equation (9.1.8)** (generalization). Along with correcting the similarity orientation,
  `GolubVanLoan.Chapter09.equation_9_1_8` drops the Taylor-series restriction of the surrounding
  text.
* **Theorem 9.1.4** (reading). `GolubVanLoan.Chapter09.theorem_9_1_4` uses total primary
  functional calculus and confluent divided differences, so it has no separate hypothesis that
  $f(T)$ is defined.
* **§9.1.5 and Equation (9.1.12)** (generalization). `GolubVanLoan.Chapter09.blockParlett_diag`
  and `GolubVanLoan.Chapter09.equation_9_1_12` use an arbitrary block-upper-triangular matrix.
  `GolubVanLoan.Chapter09.equation_9_1_12_unique` needs separation only for the particular two
  diagonal blocks.
* **§9.1.6** (reading). `GolubVanLoan.Chapter09.condRel` uses an extended nonnegative right
  limsup on normed additive groups. `GolubVanLoan.Chapter09.condRel_eq_of_hasFDerivAt` states
  the normalized derivative formula under explicit differentiability and nonzero conditions.
* **§9.1.2, the logarithm series** (typo). The source prints $\log(I - A) = \sum_{k \ge 1} A^k / k$,
  which is the series of $-\log(I - A)$. See `GolubVanLoan.Chapter09.taylor_log_one_sub`.
* **Equation (9.1.7)** (generalization). The source restricts the identity to functions given by a
  Taylor series. It holds for every $f$. See `GolubVanLoan.Chapter09.equation_9_1_7`.
* **Equation (9.1.8)** (typo). The source prints $f(X^{-1} A X) = X f(A) X^{-1}$, with $X$ and
  $X^{-1}$ exchanged on the right. See `GolubVanLoan.Chapter09.equation_9_1_8`.
* **Theorem 9.2.3** (reading). `GolubVanLoan.Chapter09.theorem_9_2_3` accepts any uniform bound
  on the derivative norm. Its proof uses the integral remainder in place of the pointwise real
  Taylor remainder printed for complex entries.
* **Algorithm 9.2.1** (reading). `GolubVanLoan.Chapter09.algorithm_9_2_1` is total at degree
  zero, where the printed start has an invalid coefficient index. The correctness theorem
  assumes positive degree.
* **Equation (9.2.5)** (reading). `GolubVanLoan.Chapter09.equation_9_2_5` proves the grouping
  identity for semiring algebras and allows all natural block sizes, including the degenerate
  size zero.
* **Equation (9.2.8)** (reading). `GolubVanLoan.Chapter09.equation_9_2_8` identifies the primary
  matrix function with the contour integral for circles. The source states the formula for a
  general enclosing contour.
* **Theorem 9.2.1** (typo). The source takes the maximum over $1 \le i \le p$. The intended range is
  $1 \le i \le q$, the blocks of the Jordan form. See `GolubVanLoan.Chapter09.theorem_9_2_1`.
* **Equation (9.2.1) and Theorem 9.2.2** (reading). The source takes $\Omega$ closed and convex.
  The statements take $\Omega$ compact to guarantee that $\delta_r$ is finite
  and convex. See `GolubVanLoan.Chapter09.equation_9_2_1` and
  `GolubVanLoan.Chapter09.theorem_9_2_2`.
* **Equation (9.2.7)** (correction). The source bounds the error by
  $\max_{a \le t \le b} \|f^{(4)}(At)\|_2$, without the factor $A^4$, which is false. The statement
  has $\max_{a \le t \le b} \|A^4 f^{(4)}(At)\|_2$. See `GolubVanLoan.Chapter09.equation_9_2_7`.
* **§9.3.1, even and odd evaluation** (generalization). `GolubVanLoan.Chapter09.pade_even_odd`
  proves the split for every diagonal Padé order. The source gives the example $q=8$.
* **§9.3.1, the Padé fraction and Equation (9.3.1)** (reading).
  `GolubVanLoan.Chapter09.pade_def` uses a total inverse when the denominator is singular, and
  `GolubVanLoan.Chapter09.equation_9_3_1` makes the invertibility needed for the remainder
  formula explicit.
* **§9.3.2–§9.3.3, time domain** (reading). `GolubVanLoan.Chapter09.exp_perturbation_integral`,
  `GolubVanLoan.Chapter09.exp_perturbation_schur`, and `GolubVanLoan.Chapter09.equation_9_3_4`
  make the nonnegative time restriction on the norm results explicit.
* **Equation (9.3.6)** (reading). `GolubVanLoan.Chapter09.equation_9_3_6` gives a lower bound on
  every real uniform upper bound, expressing the source’s supremum bound without requiring a
  finite supremum.
* **§9.3.4, normal squaring** (reading). `GolubVanLoan.Chapter09.normal_squaring` includes the
  zeroth power and uses totalized Padé evaluation.
* **Algorithm 9.3.1** (correction). The printed exponent $j = \max\{0, 1 + \lfloor \log_2
  \|A\|_\infty \rfloor\}$ only guarantees $\|A/2^j\|_\infty < 1$, not the bound
  $\|A/2^j\|_\infty \le 1/2$ that the Moler–Van Loan bound needs. The library proves the claim of
  the printed algorithm under this extra hypothesis, and proves it for every $A$ with the exponent
  $\max\{0, 2 + \lfloor \log_2 \|A\|_\infty \rfloor\}$. See
  `GolubVanLoan.Chapter09.algorithm_9_3_1_spec_backward` and
  `GolubVanLoan.Chapter09.algorithm_9_3_1_corrected_spec_backward`.
* **Equation (9.3.2)** (typo). The source prints $e^{\alpha(A) t M_S(t)}$ for
  $e^{\alpha(A) t} M_S(t)$. See `GolubVanLoan.Chapter09.equation_9_3_2`.
* **§9.3.2, the equality case of $\nu(A, t) \ge t \|A\|_2$** (correction). The source states
  equality for all $t \ge 0$ if and only if $A$ is normal. The "only if" direction is false. The
  library proves the "if" direction. See `GolubVanLoan.Chapter09.expCondNumber_eq_of_isStarNormal`
  and `GolubVanLoan.Chapter09.expCondNumber_eq_iff_counterexample`.
* **Equation (9.3.6)** (typo). The source cites "(7.8.8)" for the pseudospectral abscissa, which is
  (7.9.8). See `GolubVanLoan.Chapter09.equation_9_3_6`.
* **§9.4.1, the sign and projector** (reading). `GolubVanLoan.Chapter09.matrixSign_eq_conj` and
  `GolubVanLoan.Chapter09.sign_projector` use any similarity separating the two open half-
  planes; the latter also states idempotence.
* **§9.4.4, logarithm series and inverse scaling** (reading).
  `GolubVanLoan.Chapter09.log_maclaurin`, `GolubVanLoan.Chapter09.log_gregory`, and
  `GolubVanLoan.Chapter09.log_inverse_scaling` state complex-matrix versions. The inverse-
  scaling identity holds after any prescribed number of square roots.
* **Equation (9.4.4)** (reading). `GolubVanLoan.Chapter09.equation_9_4_4` proves that each
  eigenvalue of $G_0$ comes from an eigenvalue of $A$. The source states the opposite inclusion.
* **Equation (9.4.5)** (typo). `GolubVanLoan.Chapter09.equation_9_4_5` supplies the missing
  closing parenthesis in the intermediate Newton–Schulz expression.
* **Equation (9.4.7)** (reading). `GolubVanLoan.Chapter09.newtonSqrt_tendsto` states the square-
  root limit and transformation to the sign iterates, with an explicit quadratic step estimate
  for those sign iterates.
* **§9.4.4, the Padé approximant** (reading). `GolubVanLoan.Chapter09.log_pade_33` proves the
  local scalar error estimate, while the source evaluates the fraction at $A-I$.
* **§9.4.1** (typo). The source derives the Jordan-form expression of $\operatorname{sign}(A)$ "from
  Theorem 9.1.1", which does not exist; the expression follows from the definition (9.1.3)–(9.1.4).
  The source also writes $S^2 = S$ for $S^2 = I$. See `GolubVanLoan.Chapter09.matrixSign_eq_conj`.
* **§9.4.2, the principal square root** (reading). The source leaves implicit that $A$ has no
  eigenvalue on $(-\infty, 0]$. The statement assumes it. See
  `GolubVanLoan.Chapter09.principalSqrt_existsUnique`.
* **§9.4.3, $\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix}\right) =
  \begin{bmatrix} 0 & U \\ U^T & 0 \end{bmatrix}$** (correction). The identity needs $A$ to be
  nonsingular, which the source omits. See `GolubVanLoan.Chapter09.sign_block_polar`.
* **§9.4.3, the Li–Sun bound** (correction). The bound is false for nonsingular $A$ and $\tilde A$
  alone. The statement assumes $\det A \cdot \det \tilde A > 0$. See
  `GolubVanLoan.Chapter09.li_sun`.
* **§9.4.3, the citation of Li and Sun** (typo). The source dates the paper "(2003)". It appeared in
  SIAM J. Matrix Anal. Appl. 23 (2002). See `GolubVanLoan.Chapter09.li_sun`.

**Chapter 10: Large sparse eigenvalue problems**

* **Algorithm 10.1.1 and Theorem 10.1.1** (reading). A fuel-limited prefix can retain the
  residual term. The stopped exact theorem assumes enough fuel and uses the last coordinate
  vector of $\mathbb R^k$ in (10.1.4). See `GolubVanLoan.Chapter10.algorithm_10_1_1_spec`,
  `GolubVanLoan.Chapter10.theorem_10_1_1`, and `GolubVanLoan.Chapter10.equation_10_1_4`.
* **Theorem 10.1.4** (reading). The bound explicitly requires the interior index, strict
  spectral gaps, separation from earlier Ritz values, and nonzero starting overlap. See
  `GolubVanLoan.Chapter10.theorem_10_1_4`.
* **Theorem 10.1.2** (reading). The hypothesis $q_1^T z_1 \neq 0$, implicit in the source, is
  explicit. The source's $\rho_1$ is undefined when $\lambda_2 = \lambda_n$; the statement takes
  $\rho_1 = 0$ and needs no gap hypothesis. See `GolubVanLoan.Chapter10.theorem_10_1_2`.
* **Corollary 10.1.3** (typo). The source writes $\cos\phi_n = q_1^T z_n$ without the absolute
  value. See `GolubVanLoan.Chapter10.corollary_10_1_3`.
* **Golub's rank-one modification, §10.1.4** (generalization). The source takes
  $\tau \in \{-1, 1\}$; the statement holds for every real $\tau$. See
  `GolubVanLoan.Chapter10.golub_rankOne_modification`.
* **Equations (10.2.7)–(10.2.10), quadrature existence** (reading). The weight hypothesis
  requires finite moments of every order and infinite support. The Gauss existence theorem gives
  distinct real nodes but does not state their location in a prescribed interval. See
  `GolubVanLoan.Chapter10.equation_10_2_7`.
* **Gauss–Radau and Gauss–Lobatto remainders, §10.2.2** (specialization). The mean-value point
  is asserted in $[a,b]$. The printed statement places it in $(a,b)$. See
  `GolubVanLoan.Chapter10.gaussRadau_remainder` and
  `GolubVanLoan.Chapter10.gaussLobatto_remainder`.
* **Fact 1, §10.2.3** (correction). The constant polynomial is normalized by the reciprocal
  square root of the total mass. The printed $p_0=1$ requires a unit-mass weight. See
  `GolubVanLoan.Chapter10.orthonormalPolynomials_threeTerm`.
* **§10.2.5, Radau exactness by Lanczos** (generalization). The special node for polynomial
  exactness need not be a spectral endpoint. The shifted tridiagonal matrix must be invertible
  and the Krylov prefix must have full dimension. See
  `GolubVanLoan.Chapter10.gaussRadau_via_lanczos`.
* **Remainder of the Gauss rule, §10.2.2** (typo). The source prints $(2n)!$; the rule has $k$ nodes
  and the factor is $(2k)!$. See `GolubVanLoan.Chapter10.gauss_remainder`.
* **Remainder of the Gauss–Lobatto rule, §10.2.2** (typo). The source's list prints this remainder
  as $R_{GG}$. See `GolubVanLoan.Chapter10.gaussLobatto_remainder`.
* **(10.2.13)** (correction). The source prints the recurrence with $\beta_{k-1}^2$, which is the
  recurrence of the monic polynomials $\det(\lambda I - T_k)$; the Lanczos polynomials have
  $\beta_j$. See `GolubVanLoan.Chapter10.equation_10_2_13`.
* **(10.2.13)** (typo). The source writes $q_k = p_k(A) q_1$ for a polynomial of degree $k$; the
  index is off by one. See `GolubVanLoan.Chapter10.equation_10_2_13`.
* **(10.2.12)** (generalization). The source's weights $s_{1j}^2$ assume $\|u\| = 1$; the statement
  holds for every $u$, with the weights $\|u\|^2 s_{1j}^2$. See
  `GolubVanLoan.Chapter10.equation_10_2_12`.
* **Gauss rule by Lanczos, §10.2.4** (generalization). The source locates $\eta$ in
  $[\lambda_n, \lambda_1]$; the statement allows any interval that contains the spectrum. See
  `GolubVanLoan.Chapter10.lanczos_gaussRule`.
* **Gauss–Radau modification, §10.2.5** (typo). The source prints $\beta_{k+1}^2$ for $\beta_k^2$ in
  $\tilde\alpha_{k+1}$, and its display of $\tilde T_{k+1}$ omits $\beta_k$ above the diagonal. See
  `GolubVanLoan.Chapter10.gaussRadau_tridiag`.
* **Equation (10.3.4)** (reading). The reflector program gives an exact orthogonal completion,
  and the comparison with Lanczos vectors is restricted to indices below the grade. See
  `GolubVanLoan.Chapter10.equation_10_3_4`.
* **§10.3.4, good Ritz pairs** (reading). The predicate expresses the residual test alone. The
  source applies the test to already computed Ritz pairs. See
  `GolubVanLoan.Chapter10.IsGoodRitzPair`.
* **Equations (10.3.7)–(10.3.9)** (generalization). The prefix identities do not need $n=rp$.
  Global orthogonality and compression of a prefix use the full-rank residual condition in the
  text. See `GolubVanLoan.Chapter10.equation_10_3_8` and
  `GolubVanLoan.Chapter10.equation_10_3_9`.
* **Theorem 10.3.2** (typo). The bound uses $\tan(\phi_p)$ for the angle defined by the smallest
  singular value. The source prints $\tan(\theta_p)$. See
  `GolubVanLoan.Chapter10.theorem_10_3_2`.
* **Theorem 10.3.2** (reading). The source's $\rho_i$ is undefined when $\lambda_{p+1} = \lambda_n$;
  the statement takes $\rho_i = 0$ and needs no gap hypothesis. See
  `GolubVanLoan.Chapter10.theorem_10_3_2`.
* **Algorithms 10.4.1–10.4.2, zero normalization coefficients** (reading). The exact results
  identify the totalized vectors and coefficients. A zero normalization coefficient can give a
  zero vector. For Algorithm 10.4.2 this can occur even when the leading square block is
  nonsingular. See `GolubVanLoan.Chapter10.bidiagLoop_spec` and
  `GolubVanLoan.Chapter10.algorithm_10_4_2_spec`.
* **§10.4.5, CUR product** (correction). Equation (10.4.24) also needs the transpose on $D_R
  Z_1(\mathrm{row},:)$. See `GolubVanLoan.Chapter10.equation_10_4_24`.
* **Equation (10.4.6)** (typo). The source prints $A U(:, 1:k) = V(:, 1:k) B(1:k, 1:k)$, with $U$
  and $V$ exchanged. See `GolubVanLoan.Chapter10.equation_10_4_6`.
* **Equation (10.4.6)** (generalization). The source attributes the identity to $\beta_k = 0$. It
  holds for every $k \le n$. See `GolubVanLoan.Chapter10.equation_10_4_6`.
* **Equation (10.4.7)** (typo). The source prints $A^T V(:, 1:k) = U(:, 1:k) B(1:k, 1:k)^T$, with
  $U$ and $V$ exchanged. See `GolubVanLoan.Chapter10.equation_10_4_7`.
* **Algorithm 10.4.1** (generalization). The source assumes that $A$ has full column rank. The exact
  semantics holds for every $A$; full column rank only makes every $\alpha_j$ positive. See
  `GolubVanLoan.Chapter10.algorithm_10_4_1_spec`.
* **§10.4.2, Ritz pairs of $A^T A$** (correction). The source prints
  $A^T A y_i = \gamma_i^2 z_i + [F_k]_{ki} p_k$. The identity is $A^T A y_i = \gamma_i^2 y_i +
  \gamma_i [F_k]_{ki} p_k$. See `GolubVanLoan.Chapter10.isRitzPair_gram`.
* **§10.4.2, Ritz pairs of $A^T A$** (reading). The source names the Ritz pair $\{\gamma_i, y_i\}$.
  The Ritz value of $A^T A$ is $\gamma_i^2$. See `GolubVanLoan.Chapter10.isRitzPair_gram`.
* **Algorithm 10.4.2** (typo). The source states $u_c \in \mathbb{R}^n$. The starting vector is
  $u_c \in \mathbb{R}^m$. See `GolubVanLoan.Chapter10.algorithm_10_4_2`.
* **Algorithm 10.4.2** (generalization). The source assumes that $A(1:n, 1:n)$ is nonsingular. The
  exact semantics holds for every $A$. See `GolubVanLoan.Chapter10.algorithm_10_4_2_spec`.
* **Equation (10.4.24)** (typo). The source prints $(C\Phi)(\Psi R)$. The product is
  $(C\Phi)(\Psi^T R)$, as in (10.4.23). See `GolubVanLoan.Chapter10.equation_10_4_24`.
* **Algorithm 10.5.1** (reading). The printed zero-residual factorization concerns a completed
  exact run. A fuel-limited prefix instead has the last residual term of (10.5.2). See
  `GolubVanLoan.Chapter10.algorithm_10_5_1_spec` and
  `GolubVanLoan.Chapter10.algorithm_10_5_1_matrices`.
* **Equations (10.5.3) and (10.5.10)** (reading). The filter polynomial is the monic product,
  and the first-column identities account for the source's normalization scalar separately. See
  `GolubVanLoan.Chapter10.filterPolynomial` and
  `GolubVanLoan.Chapter10.explicitRestartCycle_spec`.
* **§10.5.3, continued Arnoldi steps** (reading). The specification of the full-size restart
  requires reaching the requested order, since the continuation may stop earlier when its
  residual vanishes. See `GolubVanLoan.Chapter10.implicitRestartCycle_spec`.
* **Equation (10.5.11)** (generalization). The unsymmetric Lanczos program normalizes starting
  vectors with nonzero mutual dot product, handles initially degenerate pairs by stopping, and
  limits its loop by fuel. See `GolubVanLoan.Chapter10.unsymmetricLanczos`.
* **Equation (10.5.4)** (typo). The source prints the loop as `for i = 0:p`. It runs for
  $i = 1, \dots, p$. See `GolubVanLoan.Chapter10.shiftedQrSteps`.
* **Theorem 10.5.1** (generalization). The source defines $V_i$ and $R_i$ by QR factorizations. The
  identity holds for any matrices that satisfy the two lines of (10.5.4). See
  `GolubVanLoan.Chapter10.theorem_10_5_1`.
* **§10.5.3, the filter in the first column** (generalization). The source writes
  $V(:, 1) = p(H_c) e_1 / R(1, 1)$, which assumes $R(1, 1) \neq 0$. The statement
  $R(1, 1) V(:, 1) = p(H_c) e_1$ holds without this assumption. See
  `GolubVanLoan.Chapter10.filter_firstColumn`.
* **§10.5.3, the restarted starting vector** (generalization). The source writes
  $q_+ = c (A - \mu_1 I) \cdots (A - \mu_p I) q_1$ with $c = 1/R(1, 1)$. The statement
  $R(1, 1) q_+ = p(A) q_1$ holds also when $R(1, 1) = 0$. See
  `GolubVanLoan.Chapter10.restart_firstColumn_eq`.
* **§10.5.3, the truncated Arnoldi decomposition** (correction). The source gives the new residual
  as $v_{mj} r_c$. The residual is $h^+_{j+1,j} q^+_{j+1} + v_{mj} r_c$. See
  `GolubVanLoan.Chapter10.implicitRestart_isArnoldiDecomposition` and
  `GolubVanLoan.Chapter10.implicitlyRestartedArnoldi`.
* **§10.5.4, the Krylov–Schur restart** (typo). The source asks for a Schur decomposition of $A$
  where it means one of $H_m$, and its display has $r_c c_m^T U$ for $r_m e_m^T U$. See
  `GolubVanLoan.Chapter10.krylovSchur_isArnoldiDecomposition`.
* **§10.5.4, the Krylov–Schur restart** (generalization). The source uses a Schur decomposition of
  $H_m$. Only the block upper triangular form of $U^T H_m U$ is needed. See
  `GolubVanLoan.Chapter10.krylovSchur_isArnoldiDecomposition`.
* **Equations (10.6.4)–(10.6.5)** (correction). The linear constraint fixes $w^Tx=1$. Taking
  $w=x_c$ does not force the next vector to have unit norm. See
  `GolubVanLoan.Chapter10.equation_10_6_4`.
* **Equations (10.6.6)–(10.6.10)** (reading). The formulas assume the shifted matrix and scalar
  denominator used in them are invertible. See `GolubVanLoan.Chapter10.equation_10_6_7` and
  `GolubVanLoan.Chapter10.equation_10_6_10`.
* **Davidson and Jacobi–Davidson correctness** (limitation). Five specifications ask for unit
  Ritz vectors in every projected dimension, including dimension zero, where none exist. The
  iteration requests Ritz pairs only in positive dimension. See
  `GolubVanLoan.Chapter10.subspaceExpansion_spec`, `GolubVanLoan.Chapter10.equation_10_6_16`,
  `GolubVanLoan.Chapter10.subspaceExpansion_ritzValue_mono`,
  `GolubVanLoan.Chapter10.davidson_ritzValue_mono`, and
  `GolubVanLoan.Chapter10.jacobiDavidson_spec`.
* **Equation (10.6.13)** (typo). The source prints $\alpha + + c^T z_c$ in the right-hand side; the
  intended term is $\alpha + c^T z_c$. See `GolubVanLoan.Chapter10.equation_10_6_13`.
* **Trace-min principle, §10.6.5** (correction). The source says that every minimizer
  $V_{\mathrm{opt}}$ has $V_{\mathrm{opt}}^T A V_{\mathrm{opt}}$ diagonal; this holds only for some
  minimizer. See `GolubVanLoan.Chapter10.isLeast_trace_transpose_mul_mul`.

**Chapter 11: Large sparse linear system problems**

* **§11.1.1, compressed columns** (reading). Stored positions may include zeros, and row indices
  inside each column must increase strictly. See `GolubVanLoan.Chapter11.CompressedColumn`.
* **Equation (11.1.6)** (reading). When the minimum's set is empty, the index is the diagonal
  position and $i-f_i(A)=0$. See `GolubVanLoan.Chapter11.profileIndex`.
* **§11.1.8, Sparse QR Challenge** (typo). For $A(:,p)=AP^T$, use $P=I_n(p,:)$, the transpose of
  the printed $I_n(:,p)$. See `GolubVanLoan.Chapter11.seminormal_cholesky` and
  `GolubVanLoan.Chapter11.seminormal_normalEquations`.
* **Equation (11.1.8)** (correction). The source runs the loop for $k = 1{:}n-2$, which leaves the
  last two columns unfactored; the program runs it for $k = 1{:}n$. See
  `GolubVanLoan.Chapter11.choleskyWithPivoting`.
* **Formula after Fact 2, §11.1.6** (generalization). The source discusses lower-triangular
  entries. The formula holds for every pair of indices. See
  `GolubVanLoan.Chapter11.cholesky_apply_eq`.
* **Facts 1–2, §11.1.6** (reading). The source says that $g_{ij}$ is nonzero at the predicted
  positions "assuming no numerical cancellation", which has no exact reading; the theorem states the
  exact converse, that $g_{ij}$ vanishes off the symbolic fill. See
  `GolubVanLoan.Chapter11.cholesky_eq_zero_of_not_isCholeskyFill`.
* **Structural symmetry, §11.1.9** (correction). The source says that one elimination step keeps
  structural symmetry; this is false for the computed $A^{(1)}$, and the theorem states it for the
  predicted pattern. See `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm` and
  `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm_counterexample`.
* **§11.2.2, block Jacobi and Gauss–Seidel** (generalization). Ordered block labels permit
  arbitrary numbers and sizes of blocks and noncontiguous original indices. See
  `GolubVanLoan.Chapter11.blockJacobi_eq` and `GolubVanLoan.Chapter11.blockGaussSeidel_eq`.
* **Equation (11.2.27)** (generalization). The normalized SSOR product and eigenvalue quotient
  hold for symmetric matrices with positive diagonals and any nonzero weight. See
  `GolubVanLoan.Chapter11.equation_11_2_27`.
* **§11.2.8, Chebyshev interval** (reading). The bound requires $\alpha<\beta$ because the
  rescaling divides by $\beta-\alpha$. The program uses finite fuel and the bound is at its
  attained iterate. See `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le` and
  `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le'`.
* **Equation (11.2.8)** (correction). The source prints the corner entry of the $k$-th power as
  $\alpha \lambda^{k-1}$, which is false for $k \ge 2$. The corner entry is
  $k \alpha \lambda^{k-1}$. See `GolubVanLoan.Chapter11.equation_11_2_8`.
* **Equation (11.2.9)** (correction). The proof of Theorem 11.2.1 in the source takes
  $\mu = 2\|E\|_2/(1 - \rho)$, but the bound (7.3.15) needs $\|E\|_F$. The bound is stated with
  $\|E\|_F$. See `GolubVanLoan.Chapter11.equation_11_2_9`.
* **Equation (11.2.9)** (typo). The proof in the source writes $E = A - D$. The strictly upper
  triangular part is $E = T - D$. See `GolubVanLoan.Chapter11.equation_11_2_9`.
* **Theorem 11.2.2** (typo). The proof in the source says "no eigenvalue of $A$"; it means the
  Jacobi iteration matrix $G_J$. See `GolubVanLoan.Chapter11.jacobi_linfty_opNorm_lt_one`.
* **Equation (11.2.17)** (typo). The source prints "$\rho(G) = =$". See
  `GolubVanLoan.Chapter11.equation_11_2_17`.
* **Equations (11.2.18)–(11.2.19)** (correction). The source prints
  $N_\omega = (\omega^{-1} - 1) D_A + U_A$, which is inconsistent with $A = M_\omega - N_\omega$.
  The sign of $U_A$ is changed. See `GolubVanLoan.Chapter11.equation_11_2_18` and
  `GolubVanLoan.Chapter11.equation_11_2_19`.
* **Equation (11.2.20)** (reading). The display of SOR at the component level carries no tag in the
  source. It is taken to be (11.2.20). See `GolubVanLoan.Chapter11.sorSweep`.
* **Equation (11.2.21)** (correction). The source prints $+L_A$ on the right side, which is
  inconsistent with the backward SOR splitting. The sign of $L_A$ is changed. See
  `GolubVanLoan.Chapter11.equation_11_2_21`.
* **Equation (11.2.25)** (generalization). The identity is stated for every $A$ with nonzero
  diagonal entries, not only for symmetric $A$. See `GolubVanLoan.Chapter11.equation_11_2_25`.
* **Theorem 11.2.4** (generalization). The theorem also states that the eigenvalues of $G$ lie in
  $[0, 1)$, which the proof in the source shows. See `GolubVanLoan.Chapter11.theorem_11_2_4`.
* **Section 11.2.8** (typo). The Chebyshev bound in the source writes $\lambda_i \in \lambda(A)$; it
  means the eigenvalues of $G$. See `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le`.
* **Equation (11.3.24)** (typo). The numerator is $p_{k-1}^TAg_{k-1}$, with a transpose missing
  in print. See `GolubVanLoan.Chapter11.equation_11_3_24`.
* **Algorithms 11.3.2–11.3.3 and (11.3.26)** (reading). The programs have bounded fuel. The
  returned iterate may already solve the system before a subsequent pass records the failed loop
  test. See `GolubVanLoan.Chapter11.algorithm_11_3_2_spec`,
  `GolubVanLoan.Chapter11.algorithm_11_3_3_spec`, and `GolubVanLoan.Chapter11.equation_11_3_26`.
* **Equation (11.3.28), CGNR and CGNE** (generalization). The rectangular CGNR criterion assumes
  full column rank. The rectangular CGNE criterion assumes full row rank and a consistent right-
  hand side, with $x_0=A^Ty_0$. See `GolubVanLoan.Chapter11.cgnr_isMinResidual_of_injective` and
  `GolubVanLoan.Chapter11.cgne_isMinError_of_injective_transpose`.
* **Algorithm 11.3.1** (reading). Exact termination at a sufficient finite fuel budget requires
  positive tolerance. See `GolubVanLoan.Chapter11.algorithm_11_3_1_spec`.
* **Equations (11.3.10)–(11.3.11) and the Krylov argument** (correction). The subspace contains
  the affine displacement $x_k-x_0$ and the gradient $g_k=g_0+A(x_k-x_0)$. Nested spaces may
  repeat. See `GolubVanLoan.Chapter11.equation_11_3_11` and
  `GolubVanLoan.Chapter11.gradient_mem_krylov`.
* **Corollary 11.3.2** (generalization). The source assumes that $D$ is symmetric and that $r < n$;
  neither is needed. See `GolubVanLoan.Chapter11.corollary_11_3_2`.
* **Equation (11.3.14)** (correction). The source prints $x_k = Q_ky_k$, which holds only for
  $x_0 = 0$; the method computes $x_k = x_0 + Q_ky_k$. See `GolubVanLoan.Chapter11.preliminaryCG`.
* **Equation (11.3.19)** (generalization). The source extends the solution vector for a positive
  definite Lanczos tridiagonal matrix. The theorem gives the extension for arbitrary recurrence
  coefficients and states each row identity under a local nonzero-pivot hypothesis. See
  `GolubVanLoan.Chapter11.equation_11_3_19`.
* **Theorem 11.3.4** (generalization). The orthogonality $g_i^Tg_j = 0$ holds for $0 \le i < j$, not
  only for $1 \le i < j$. See `GolubVanLoan.Chapter11.theorem_11_3_4`.
* **Theorem 11.3.5** (typo). The source prints the range $1 \le i < j \le k$, which excludes the
  case $i = j$ of its own statement; the range is $1 \le i, j \le k$. See
  `GolubVanLoan.Chapter11.theorem_11_3_5`.
* **§11.4.1, MINRES initialization and Givens update** (correction). The initial scale uses
  $\|r_0\|_2$. The final rotation is determined from the new column after its earlier rotations
  and the new subdiagonal entry. See `GolubVanLoan.Chapter11.minres_reduction` and
  `GolubVanLoan.Chapter11.minres_givens_update`.
* **§11.4.2, LSMR monotonicity** (specialization). The formal ordinary residual norm bound
  requires full column rank. The normal residual norm bound has no rank assumption. See
  `GolubVanLoan.Chapter11.lsmr_norm_residual_antitone`.
* **§11.4.5, BiCG LU expression** (typo). The final LU expression restores the base iterate
  $x_0$. See `GolubVanLoan.Chapter11.bicg_residual_orthogonal`.
* **Display for $\phi(\alpha x)$ in §11.4.1** (typo). The source prints $\phi(\alpha x) =
  \alpha^2\lambda_{\min} - \alpha x^Tb$; the value is $\frac12\alpha^2\lambda_{\min}\|x\|_2^2 -
  \alpha x^Tb$. See `GolubVanLoan.Chapter11.energyFunctional_unbounded_of_indefinite`.
* **Equation (11.4.1)** (generalization). The source states the Givens solve for symmetric $A$; it
  holds for every $A$. See `GolubVanLoan.Chapter11.equation_11_4_1`.
* **Equation (11.4.3)** (typo). The source prints the first row as $\alpha_1\ \beta_2$; it is
  $\alpha_1\ \beta_1$. See `GolubVanLoan.Chapter11.equation_11_4_2`.
* **Equation (11.4.5)** (typo). The derivation prints $r_k = r_0 - AQ_{k-1}y_k$; it is
  $r_0 - AQ_ky_k$. See `GolubVanLoan.Chapter11.equation_11_4_5`.
* **Equation (11.4.5)** (generalization). The source takes the minimum-norm solution $y_k$; the
  orthogonality holds for every solution. See `GolubVanLoan.Chapter11.equation_11_4_5`.
* **The LSQR subspace in §11.4.2** (generalization). The source starts from $u_1 = r_0/\beta_0$; any
  nonzero multiple of $r_0$ gives the same subspace. See `GolubVanLoan.Chapter11.lsqr_span_eq`.
* **Givens display for LSQR in §11.4.2** (typo). The source prints $\beta_1e_1$; it is $\beta_0e_1$.
  See `GolubVanLoan.Chapter11.equation_11_4_7`.
* **First line of §11.4.3** (reading). The source writes $\mathcal{K}(A, b, k)$; it is read as
  $\mathcal{K}(A, r_0, k)$. See `GolubVanLoan.Chapter11.gmres_reduction`.
* **Three-line display of §11.4.4** (typo). The source prints the middle term
  $\|b - A(x_0 + \phi(A))r_0\|_2$; it is $\|b - A(x_0 + \phi(A)r_0)\|_2$. See
  `GolubVanLoan.Chapter11.minResidual_eq_iInf_poly`.
* **BiCG and CG in §11.4.5** (generalization). The source assumes $A$ symmetric positive definite;
  symmetry is enough. See `GolubVanLoan.Chapter11.bicg_eq_cg`.
* **Equation (11.4.14)** (correction). The source prints $\phi_k(0) = 1$, which is false:
  $\phi_1(0) = 1 + \tau_0$. The statement asserts only $\psi_k(0) = 1$. See
  `GolubVanLoan.Chapter11.equation_11_4_14`.
* **Figure 11.4.1, CGS and BiCGstab** (typo). The figure prints the initial condition
  $\tilde r_0^T\tilde r_0 \neq 0$; it is $\tilde r_0^Tr_0 \neq 0$. See `GolubVanLoan.Chapter11.cgs`
  and `GolubVanLoan.Chapter11.bicgstab`.
* **§11.5.1, transformed system** (generalization). Only the left factor must be nonsingular for
  the stated equivalence, which uses the total inverse of the right factor. See
  `GolubVanLoan.Chapter11.preconditioned_system_iff`.
* **§11.5.3, SSOR** (generalization). The unscaled SSOR product is positive definite for
  symmetric $A$ with positive diagonal and any real $\omega$. See
  `GolubVanLoan.Chapter11.ssorPreconditioner_posDef`.
* **§11.5.8, incomplete Cholesky** (reading). `GolubVanLoan.Chapter11.incChol` uses the real-
  valued mask as a keep-or-drop test. `GolubVanLoan.Chapter11.incChol_isIncompleteCholesky`
  requires dropped input positions to be zero for the agreement asserted in (11.5.7).
* **§11.5.9, block Cholesky recurrence** (generalization). The block product uses invertible
  diagonal factors satisfying the Schur update and does not require them to be triangular. In
  (11.5.10), the bandwidth of a Cholesky factor is conditional on its existence. See
  `GolubVanLoan.Chapter11.blockTridiagonal_cholesky` and
  `GolubVanLoan.Chapter11.equation_11_5_10`.
* **§11.5.11, Schwarz update** (generalization). The affine update allows arbitrary
  nondegenerate trial and test spaces and additive weights. The residual multiplier is not
  asserted to be invertible. See `GolubVanLoan.Chapter11.schwarz_update_affine`.
* **Equation (11.5.1)** (typo). The printed recurrence mixes the gradient and residual sign
  conventions and writes $\tilde p_+ = \tilde r_c + \tau \tilde p_c$ for
  $\tilde r_+ + \tau \tilde p_c$; the consistent recurrence is stated. See
  `GolubVanLoan.Chapter11.equation_11_5_1`.
* **Algorithm 11.5.1** (typo). The source prints $x_k = x_{k-1} - \mu p_k$; the program uses
  $x_k = x_{k-1} + \mu p_k$. See `GolubVanLoan.Chapter11.algorithm_11_5_1`.
* **Equation (11.5.2)** (reading). The printed relation $p_j^T (C^{-1} A C^{-1}) p_i = 0$ holds for
  the transformed directions $\tilde p = Cp$; for the directions of Algorithm 11.5.1 it is stated as
  $p_j^T A p_i = 0$. See `GolubVanLoan.Chapter11.equation_11_5_2`.
* **Algorithm 11.5.2**, closing remark (reading). The sign of $\rho_k$ depends on the rotations, so
  the residual norm is stated as $|\rho_k|$. See `GolubVanLoan.Chapter11.algorithm_11_5_2_spec`.
* **§11.5.5**, the pattern condition (reading). The condition $\mathrm{sp}(T) = Z$ is read as "$T$
  vanishes where $Z$ does". See `GolubVanLoan.Chapter11.spai_column_decouple`.
* **§11.5.5**, the reduced problem (typo). The source writes $T(\mathit{rows}, k) = \tau$ for
  $T(\mathit{cols}, k) = \tau$. See `GolubVanLoan.Chapter11.spai_reduced_ls`.
* **§11.5.6**, the truncated Neumann loop (correction). The source says that $m$ steps apply
  $(\sum_{k=0}^{m} G^k) M_1^{-1}$; they apply $(\sum_{k=0}^{m-1} G^k) M_1^{-1}$, so $m + 1$ steps
  are needed. See `GolubVanLoan.Chapter11.neumannLoop_spec`.
* **§11.5.7**, the Concus–Golub–O'Leary loop (reading). The display is untagged in the source and is
  taken to be (11.5.5). See `GolubVanLoan.Chapter11.concusGolubOLearyPCG`.
* **§11.5.8**, the Lin–Moré nonzero count (correction). The printed bound $pn + N_1 + \dots + N_n$
  fails; the bound is $pn + N_1 + \dots + N_n + n$. See
  `GolubVanLoan.Chapter11.linMoreIC_nnz_le_add`.
* **Equation (11.5.10)** (generalization). The source takes $\Lambda_k$ symmetric tridiagonal; the
  statement needs only $\Lambda_k$ tridiagonal. See `GolubVanLoan.Chapter11.equation_11_5_10`.
* **Equation (11.5.11)**, the block LU factorization (correction). The off-diagonal interface blocks
  of $U$ are $-FA_1^{-1}C$ and $-GA_1^{-1}B$, not $0$ as printed. See
  `GolubVanLoan.Chapter11.equation_11_5_11_blockLU` and
  `GolubVanLoan.Chapter11.equation_11_5_11_counterexample`.
* **Equations (11.6.11)–(11.6.12)** (generalization). The two algebraic identities hold for all
  nonzero $\omega$. The restriction $0 < \omega \leq 1$ is used for the contraction bound. See
  `GolubVanLoan.Chapter11.equation_11_6_11` and `GolubVanLoan.Chapter11.equation_11_6_12`.
* **Theorem 11.6.2, proof** (typo). The coarse diagonal eigenvalue matrix is $(4/h^2) S^h C^h$.
  The printed value $(1/(2h^2))(I_m - \sqrt{C^h})$ does not equal it. See
  `GolubVanLoan.Chapter11.theorem_11_6_2`.
* **Grid sizes** (generalization). The source takes $n = 2^k - 1$. Everything it proves uses only
  $n = 2m + 1$, and the results hold for every $m$. See `GolubVanLoan.Chapter11.modelA`.
* **Equation (11.6.16)** (typo). The source updates $u_c$ instead of $u_{p_1}$ in the coarse-grid
  correction. See `GolubVanLoan.Chapter11.coarseGridCorrection`.
* **§11.6.2**, the optimal $\omega$ (reading). The source says that the minimization of the
  high-frequency damping factor "is essentially solved by $\omega_{\mathrm{opt}} = 2/3$"; the
  statement gives the exact minimizer and its limit $2/3$. See
  `GolubVanLoan.Chapter11.weightedJacobi_optimalOmega`.

**Chapter 12: Special topics**

* **Theorem 12.1.1, rank bound** (generalization). The rank inequality holds without spectral
  separation. See `GolubVanLoan.Chapter12.theorem_12_1_1_b`.
* **Algorithm 12.1.2** (correction). Pivoting selects a first-column entry of maximal modulus.
  The signed maximum printed in the source can be zero for nonsingular $A$. See
  `GolubVanLoan.Chapter12.algorithm_12_1_2`.
* **Equation (12.1.3)** (generalization). The source defines the displacement rank only for a
  nonsingular Sylvester operator. The generators exist without this assumption. See
  `GolubVanLoan.Chapter12.equation_12_1_3`.
* **Definition of a Cauchy-like matrix, §12.1.2** (reading). The condition $\omega_k \neq \nu_j$
  from the context is part of the definition, and the informal requirement $r \ll n$ is not. See
  `GolubVanLoan.Chapter12.IsCauchyLike`.
* **Algorithm 12.1.1** (reading). The hypothesis "$A$ has an LU factorization" is read as the
  nonsingularity of the leading principal submatrices of orders $1, \dots, n - 1$. See
  `GolubVanLoan.Chapter12.algorithm_12_1_1_spec`.
* **Definitions of §12.1.7** (reading). The informal requirement $r \ll n$ is not part of the
  definitions. See `GolubVanLoan.Chapter12.IsToeplitzLike`.
* **§12.1.7, after (12.1.9)** (typo). The source prints
  $\lambda(Z_{-1}) \cup \lambda(Z_1) = \emptyset$ for
  $\lambda(Z_{-1}) \cap \lambda(Z_1) = \emptyset$. See
  `GolubVanLoan.Chapter12.disjoint_spectra_displacement_operators`.
* **§12.1.8** (typo). The first display prints $X_G^{-1} G X_F$ for $X_G^{-1} G X_G$. See
  `GolubVanLoan.Chapter12.cauchyLike_of_diagonalizable`.
* **Equation (12.2.3)** (correction). The inverse blocks have rank at most one, allowing
  vanishing blocks. See `GolubVanLoan.Chapter12.equation_12_2_3`.
* **Equations (12.2.15)–(12.2.16)** (correction). The second term in (12.2.15) uses the strict
  upper triangle, as in Algorithm 12.2.2, so the diagonal is included only once. See
  `GolubVanLoan.Chapter12.equation_12_2_16`.
* **§12.2.10, quasiseparability and Facts 1–2** (generalization). The rank bound holds for all
  orthogonal upper Hessenberg matrices. The reflector product similarity and the even-order
  spectral relation allow arbitrary angles. See
  `GolubVanLoan.Chapter12.orthogonalHessenberg_isQuasiseparable`,
  `GolubVanLoan.Chapter12.orthogonalHessenberg_fact_1`, and
  `GolubVanLoan.Chapter12.orthogonalHessenberg_fact_2`.
* **§12.2.3, $B(r)$ has no generator representation** (generalization). The source takes $r$ with
  nonzero entries; $r_1 \neq 0$ and $r_2 \neq 0$ suffice. See
  `GolubVanLoan.Chapter12.unitBidiagonal_not_generatorRepresentable`.
* **Equation (12.2.8)** (correction). Not every quasiseparable matrix is
  $\mathbf{S}(u, v, t, d, p, q, r)$: for $n \ge 3$ and $r_1 r_2 \neq 0$, $B(r)$ is not. The
  statement uses the representation of Eidelman and Gohberg. See
  `GolubVanLoan.Chapter12.equation_12_2_8`.
* **§12.2.5** (correction). The lower LU factor of a semiseparable matrix need not be semiseparable
  when $A$ is singular. The statement assumes that the leading principal submatrices are
  nonsingular. See `GolubVanLoan.Chapter12.semiseparable_lu_factors`.
* **Algorithm 12.2.1** (correction). The hypothesis "$A$ has an LU factorization" does not ensure
  the divisions by $u_k$. The statement assumes $u_k \neq 0$ for $k = 1, \dots, n - 1$. See
  `GolubVanLoan.Chapter12.algorithm_12_2_1_spec`.
* **Algorithm 12.2.1** (typo). The text's "$M = B(\tau)$" should read $M = B(\tau)^T$. See
  `GolubVanLoan.Chapter12.algorithm_12_2_1_spec`.
* **Equation (12.2.11)** (correction). The Givens-vector representation needs $(A_L)_{n1} \neq 0$.
  See `GolubVanLoan.Chapter12.equation_12_2_11`.
* **Algorithm 12.2.2** (typo). The update of $g_k$ prints $u_k$ for $\tilde u_k$. See
  `GolubVanLoan.Chapter12.algorithm_12_2_2Step`.
* **Algorithm 12.2.2** (generalization). The correctness does not need the hypothesis
  $u .* v = p .* q$. See `GolubVanLoan.Chapter12.algorithm_12_2_2_spec`.
* **Equation (12.2.18)** (correction). The source assumes a nonzero subdiagonal. The statement
  assumes a positive subdiagonal, even order and $\det H = 1$. See
  `GolubVanLoan.Chapter12.equation_12_2_18`.
* **Equations (12.3.3)–(12.3.4)** (reading). The Kronecker congruences require only the two
  factor identities. The SVD statement uses real matrices and column-indexed singular values.
  See `GolubVanLoan.Chapter12.equation_12_3_3` and `GolubVanLoan.Chapter12.equation_12_3_4`.
* **Theorem 12.3.1 and (12.3.19)** (generalization). The exact expansion accepts arbitrary outer
  products. The truncation may include zero singular values. See
  `GolubVanLoan.Chapter12.theorem_12_3_1` and `GolubVanLoan.Chapter12.equation_12_3_19`.
* **Equation (12.3.9)** (typo). The source states $X \in \mathbb{R}^{n_1 \times m_2}$ for
  $X \in \mathbb{R}^{n_2 \times n_1}$. See `GolubVanLoan.Chapter12.equation_12_3_9`.
* **§12.3.5, the two-pass transposition** (correction). The source prints
  $\Gamma_1 = \mathcal{P}_{r,q} \otimes I_q$, which generally has the opposite shuffle
  orientation, and announces a factorization of $\mathcal{P}_{rq,q}$ before it writes
  $\mathcal{P}_{q,rq}$. See
  `GolubVanLoan.Chapter12.perfectShuffle_two_pass`.
* **Equation (12.3.21)** (typo). The source writes $\phi_{skew}(X)$ for $\phi_{skew}(X, Y)$ and
  drops a parenthesis. See `GolubVanLoan.Chapter12.equation_12_3_21`.
* **Lemma 12.3.2** (correction). The minimum over $\operatorname{rank}(Z) = 1$ is not attained for
  $T = 0$; the statement uses $\operatorname{rank}(Z) \le 1$. See
  `GolubVanLoan.Chapter12.lemma_12_3_2`.
* **§12.3.8, the nearest $X \otimes X$** (correction). The eigenvalue must be the algebraically
  largest one, not one of largest modulus, and it enters through its positive part. See
  `GolubVanLoan.Chapter12.nearest_kronecker_self`.
* **Lemma 12.3.3** (correction). For $S = 0$ the minimizer has rank $0$; the statement minimizes
  over rank at most two. See `GolubVanLoan.Chapter12.lemma_12_3_3`.
* **Lemma 12.3.3** (generalization). Of the hypothesis $S [u \,|\, v] = [u \,|\, v] \begin{bmatrix}
  0 & \mu \\ -\mu & 0 \end{bmatrix}$ only $Sv = \mu u$ is needed. See
  `GolubVanLoan.Chapter12.lemma_12_3_3`.
* **Sections 12.4.2 and 12.4.9** (generalization). Equal slice modes give a fiber, inverted
  colon bounds give an empty mode, and the contraction identity takes arbitrary typed outer mode
  families. See `GolubVanLoan.Chapter12.slice`, `GolubVanLoan.Chapter12.subtensor` and
  `GolubVanLoan.Chapter12.equation_12_4_13`.
* **Equations (12.4.18)–(12.4.19)** (reading). The successive-product expressions use square
  factors. The coordinate and Kronecker formulas allow rectangular factors. See
  `GolubVanLoan.Chapter12.equation_12_4_19`.
* **Equation (12.4.17)** (correction). The source prints $\mathcal{S} \times_k (FG)$. The correct
  right side is $\mathcal{S} \times_k (GF)$. See `GolubVanLoan.Chapter12.equation_12_4_17`.
* **Equation (12.5.4)** (typo). The third row-inner-product line is missing its equality sign.
  The full Gram identity states the inner products in all modes of tensors of arbitrary positive
  order. See `GolubVanLoan.Chapter12.gram_modeUnfold_of_isSVD`.
* **Equations (12.5.16)–(12.5.20)** (generalization). The CP unfolding identity uses arbitrary
  order, and the row normal equations are combined into a matrix equivalence. See
  `GolubVanLoan.Chapter12.equation_12_5_16` and `GolubVanLoan.Chapter12.equation_12_5_20`.
* **Equation (12.5.22)** (correction). The absolute value of a stationary quotient is a singular
  value. A sign change in one vector changes the quotient sign. See
  `GolubVanLoan.Chapter12.equation_12_5_22`.
* **Equations (12.5.25)–(12.5.29)** (reading). The contraction extends to arbitrary boundary
  ranks. The TT-SVD result gives existence with the sequential unfolding ranks. See
  `GolubVanLoan.Chapter12.equation_12_5_25` and `GolubVanLoan.Chapter12.equation_12_5_29`.
* **Equation (12.5.1)** (typo). The source writes $v_i T$ for $v_i^T$. See
  `GolubVanLoan.Chapter12.equation_12_5_1`.
* **Equation (12.5.3)** (typo). The source writes the maximum of $\|Q^T A\|_F$ as
  $\sigma_1^2 + \cdots + \sigma_r^2$; this is the maximum of $\|Q^T A\|_F^2$. See
  `GolubVanLoan.Chapter12.equation_12_5_3`.
* **Equation (12.5.5)** (correction). The source prints $\mathcal{A} \times_k U_k$, which does not
  produce the stated unfoldings; the statement uses $\mathcal{A} \times_k U_k^T$. See
  `GolubVanLoan.Chapter12.hosvd_modeProduct_slices`.
* **The displayed unfoldings before Theorem 12.5.1** (typo). Displays such as
  $\mathcal{B}^{(1)}_{(1)} = \Sigma_1 V_1^T (U_3 \otimes U_2)^T$ are misprints and are not
  reproduced. See `GolubVanLoan.Chapter12.hosvd_modeProduct_slices`.
* **The slice norms before Theorem 12.5.1** (generalization). The source states them for an order-3
  tensor; the statement holds in every mode of a tensor of any order. See
  `GolubVanLoan.Chapter12.hosvd_modeProduct_slices`.
* **Equation (12.5.11)** (correction). The source prints $\min_{1 \le k \le d}$ in place of
  $\sum_{k=1}^{d}$, and the printed bound is false. See `GolubVanLoan.Chapter12.equation_12_5_11`.
* **The Tucker problem of §12.5.3** (generalization). The source writes it for order 3; the
  statements hold for every order. See `GolubVanLoan.Chapter12.tucker_best_core` and
  `GolubVanLoan.Chapter12.tucker_objective_unfoldings`.
* **The gradient display before (12.5.24)** (typo). The gradient of $\phi_{\mathcal{C}}$ omits the
  factor $d$, which does not change where it vanishes. See
  `GolubVanLoan.Chapter12.equation_12_5_24`.

## Not formalized

The entries are grouped by chapter, after the classes of content that are out of scope in every
chapter.

**All chapters**

* **The Problems.** A Problem that the text cites in a proof is formalized as a supporting lemma.
* **Operation counts**, flop counts, and the analyses of memory traffic and communication.
* **The discussion of storage formats and of the BLAS levels.**
* **The numerical examples**, the figures, and the MATLAB illustrations.
* **The Notes and References** of every section.

**Chapter 1: Matrix multiplication**

* **The notation of §1.1.1–1.1.4 and §1.1.7–1.1.8.** The displays (1.1.1)–(1.1.3) are partition
  notation.
* **The unnumbered `jki` and `kij` loops (§1.1).** Algorithms 1.1.7 and 1.1.8 are their colon forms.
* **Table 1.1.1.**
* **The flop counts, the big-Oh notation and the BLAS levels of §1.1.15–1.1.17, with Table 1.1.2.**
  Operation counts are out of scope for the library.
* **The complex notation of §1.1.19.** Mathlib supplies the conjugate transpose `ᴴ`.
* **The numerical examples (§1.1).** Numerical examples are out of scope for the library.
* **The flop sums of §1.2.4.** Operation counts are out of scope for the library.
* **Diagonal scaling, §1.2.6.** Mathlib supplies it as `Matrix.diagonal_mul` and
  `Matrix.mul_diagonal`.
* **The prose definitions of symmetric, skew-symmetric, Hermitian and skew-Hermitian matrices
  (§1.2).** Mathlib supplies them, for example as `Matrix.IsSymm` and `Matrix.IsHermitian`.
* **The example (1.2.3).**
* **The index vectors of §1.2.9.** They are maps on `Fin n`.
* **The operation count $2n(p + q + 1)$ after Algorithm 1.2.2.** Operation counts are out of scope
  for the library.
* **Table 1.2.1 for rectangular matrices.** The table is stated for square matrices only, where the
  triangular, bidiagonal and Hessenberg predicates are defined.
* **The storage schemes (1.2.1) and (1.2.2) as such (§1.2).** They enter only as hypotheses of the
  specifications of Algorithms 1.2.2 and 1.2.3.
* **The terminology for block-sparse matrices of §1.3.1.**
* **The submatrix notation of §1.3.3.**
* **The unnumbered blocked gaxpys of §1.3.4 and block products of §1.3.5.**
* **The band structure that $B \otimes C$ inherits from $B$ and $C$ (§1.3).**
* **The reshaping of multiple Kronecker products in §1.3.8, with its count $6n^4$.** Operation
  counts are out of scope for the library.
* **The real form of complex matrix multiplication in §1.3.9.**
* **The operation counts of Strassen's method and the exponent $2.807$ (§1.3).** Operation counts
  are out of scope for the library.
* **The MATLAB `reshape` example (§1.3).** The backbone has `Matrix.reshape`.
* **The flop counts $8n \log_2 n$, $5n \log_2 n$ and $2n$ (§1.4).** Operation counts are out of
  scope for the library.
* **The display of $F_8(:, \mathrm{cols})$ as a worked example (§1.4).** Its content is the radix-2
  splitting.
* **The definitions DST-II to DCT-IV of (1.4.12), and the remark that DST-II is a subvector of a DST
  of an interleaved vector.** The backbone's `Matrix.dst2` and `Matrix.dct2` serve Chapter 4.
* **The examples $F_4$, $W_2$, $W_4$ and $W_8$ (§1.4).**
* **The notation-only displays (1.4.6), (1.4.9) and (1.4.11) (§1.4).** They are definitions, and
  they are given as definitions where an object is needed.
* **All of §1.5.** The section is a qualitative performance model: pipelined vector processing and
  the cycle counts of the strip-mined loop (1.5.1), the load and store counts of the gaxpy and the
  outer product (§1.5.2), stride (§1.5.3), and cache blocking (§1.5.4) with the capacity constraint
  (1.5.5) and the heuristic optimum (1.5.6). None of these is a proposition about the computed
  quantities. See `NumlibSurface.GolubVanLoan.Chapter01.Section05`.
* **§1.6, except Cannon's identity (1.6.16) and its shift relations.** The items below are cost
  models or statements about processors, not about the computed matrices.
* **The model computation and its blockings (1.6.1)–(1.6.2), as a parallel program.**
* **The load-balancing ratios (1.6.3)–(1.6.4).**
* **The time model (1.6.5)–(1.6.6) and the communication ratios (1.6.7)–(1.6.15).**
* **Barrier synchronization and the shared-memory and distributed-memory paradigms of
  §1.6.5–1.6.7.**
* **The update sequence (1.6.17)–(1.6.20) and the toroidal message passing, as communication
  patterns.**

**Chapter 2: Matrix analysis**

* **Independence, span, basis and dimension, §2.1.1.** These are the vocabulary of Mathlib.
* **The notation of §2.1.8.** The subsection fixes a notation only.
* **Absolute and relative error, §2.2.3.** The subsection names quantities and states a heuristic,
  "about $p$ correct significant digits", with $\approx$.
* **Equation (2.3.4)**, the definition of a consistent family of norms. The source uses it only in
  prose.
* **The hyperellipsoid picture after Corollary 2.4.2.** It is prose.
* **The pointer to §8.6 for the computation of the SVD (§2.4).** It is prose.
* **The prose on the connection of the SVD with $A^TA$, and the remark that all real SVD properties
  have complex analogs (§2.4).** The complex analogs are covered by the backbone over `RCLike`
  fields and are not restated.
* **The two example CS patterns after Theorem 2.5.3.** They are examples.
* **Equation (2.5.2).** It only names $Q = W^T Z$ inside a proof.
* **The $2 \times 2$ example after Theorem 2.6.2**, which shows that the bound can be attained or
  not. It is a numerical example.
* **The hyperellipsoid geometry of §2.6.2.** It is prose.
* **The remark that the Skeel number can be considerably less than $\kappa_\infty(A)$ (§2.6).** It
  names no specific matrix.
* **The IEEE bit layout (2.7.1).** It is notation.
* **The sample roundings of §2.7.1.**
* **The values $\pm\infty$ and NaN, the exceptions, and the directed rounding modes of §2.7.2.** The
  tie rule of rounding to nearest is covered by allowing any nearest element.
* **Maxims 2 and 3 of §2.7.4.**
* **The styles of error analysis (2.7.13)–(2.7.14).**
* **The quotation of Wilkinson (§2.7).**
* **The claims about the Strassen method in §2.7.10.** They have no stated constant.
* **The operation-count remarks of Chapter 2**, such as "$O(n^2)$ computations" and "the 2-norm
  computation is iterative".
* **The remark that (2.7.21)–(2.7.22) are best possible (§2.7)** and the correct rounding of
  $\sqrt{\cdot}$ and of conversions (§2.7.2). They are prose.
* **The Problems of Chapter 2**, except those that the text cites in a proof: P2.3.2 is
  `Matrix.lpOpNorm_submatrix_le`, P2.3.3 is `Matrix.l2_opNorm_rectDiagonal`, P2.4.7 is
  `Matrix.frobenius_norm_le_sqrt_rank_mul_l2_opNorm`, and P2.7.2 is
  `FloatingPoint.System.abs_sub_le_of_forall_abs_sub_le`.

**Chapter 3: General linear systems**

* **The flop counts and the level-3 fraction of §3.1.5.** Operation counts are out of scope for the
  library.
* **The least-squares remark of §3.1.6.**
* **The numerical example of §3.1.3.** Numerical examples are out of scope for the library.
* **The Problems of §3.1.** Problems are out of scope for the library.
* **Operation counts and level-3 fractions (§3.2).** Operation counts are out of scope for the
  library.
* **The Problems of §3.2.** Problems are out of scope for the library.
* **The five loop orders of §3.2.9 that the source does not write out.**
* **Displays (3.3.3)–(3.3.13).** They are steps of the proof in the source; the backbone proves the
  entrywise bound of [higham2002accuracy] Theorem 9.3 directly.
* **The remark on rectangular matrices after Theorem 3.3.1.**
* **The average-case growth $n^{2/3}$ and the statement "$\rho = 10$" (§3.4).** They are heuristics
  with no rigorous reading.
* **The reliability of rook pivoting (§3.4).** The claim that rook pivoting has the same level of
  reliability as complete pivoting is a heuristic.
* **The backward stability of complete pivoting (§3.4.6, §3.4.10).** Algorithm 3.4.3 has an exact
  specification only.
* **Example 3 of the "LU mentality" and the vocabulary of §3.4.10.**
* **The algorithm of P3.4.5 behind (3.4.11).** The factorization (3.4.11) is proved from the
  specification.
* **Operation counts (§3.4).**
* **(3.5.1) as an approximation, the "correct digits" statements, and Heuristics II and III.** They
  have no rigorous reading beyond the theorems of this module.
* **The Forsythe–Moler estimate (§3.5).**
* **Skeel's criterion (§3.5).**
* **Simple row scaling (§3.5).**
* **How close the estimate of Algorithm 3.5.1 is to $\kappa_\infty(T)$.**
* **The parallel material of §3.6.** The block-cyclic distribution, the processor grids, (3.6.6) and
  the figures state no proposition.
* **Tournament pivoting (§3.6.3).** It states no proposition.
* **The algorithm of P3.6.1.** The source leaves it as an exercise.

**Chapter 4: Special linear systems**

* **Operation counts (§4.1).**
* **§4.2.4, matrix square roots.** They are the subject of Chapter 9.
* **§4.2.10, packed formats.**
* **Flop counts (§4.2).**
* **The numerical example with the matrix $\begin{bmatrix} \epsilon & m \\ -m & \epsilon
  \end{bmatrix}$ (§4.2).**
* **Wilkinson's completion criterion $q_n u \kappa_2(A) \le 1$ (§4.2.6).** The source quotes it
  without derivation.
* **The numerical-rank threshold of §4.2.8.** The source quotes it without derivation.
* **§4.3.7, vectorization.**
* **§4.3.9, banded inverses.**
* **Band storage (§4.3).**
* **Flop counts (§4.3).**
* **The band $LDL^T$ factorization (§4.3).** The source leaves it to the reader.
* **The derivation steps (4.4.3)–(4.4.4) and (4.4.6)–(4.4.13).** Their content is
  `GolubVanLoan.Chapter04.equation_4_4_14`.
* **The Bunch–Kaufman strategy (§4.4).**
* **The stability claims of §4.4.4.**
* **The flop count of block cyclic reduction (§4.5).**
* **Buneman's stabilization of block cyclic reduction (§4.5).**
* **The rest of the SPIKE framework of §4.5.4**, including the displays (4.5.11)–(4.5.12) and the
  refined blockings.
* **Displays (4.6.3)–(4.6.4)** as separate results. They are the two stages of Algorithm 4.6.1,
  which `GolubVanLoan.Chapter04.vandermonde_inv_factorization` and
  `GolubVanLoan.Chapter04.algorithm_4_6_1_spec` cover.
* **The accuracy remark of Björck and Pereyra (§4.6).**
* **Confluent Vandermonde systems (§4.6).**
* **The error approximations of §4.7.6**, stated with $\approx$.
* **The count of $O(\log n)$ Newton steps in §4.7.7.**
* **The lookahead strategy of §4.7.8.**
* **The Problems of §4.8.** Problems are out of scope for the library.
* **Vavasis's method.** The source quotes it without derivation.

**Chapter 5: Orthogonalization and least squares**

* **The 2-by-2 preview of §5.1.1.** It is prose.
* **The flop counts of §5.1.** Operation counts are out of scope for the library.
* **The level-2 and level-3 discussion of §5.1.7.**
* **A rounding bound for Algorithm 5.1.2.** The source states none.
* **The Problems of §5.1.** Problems are out of scope for the library.
* **Stewart's perturbation bound $O(\varepsilon \kappa_2(A))$ for the QR factors (§5.2.1).** The
  source quotes it without a statement.
* **The roundoff properties of Algorithm 5.2.2.** The source says only that they are essentially the
  same as those of Algorithm 5.2.1.
* **The roundoff properties of Gram–Schmidt (§5.2.9).** The source quotes them without derivation.
* **The orthogonality $\hat Q_1^T \hat Q_1 = I + E_H$, $\|E_H\|_2 \approx u$, of the Householder $Q$
  accumulated in floating point (§5.2.9).** No rounding theorem for
  `GolubVanLoan.Chapter05.forwardAccumulation` or `GolubVanLoan.Chapter05.backwardAccumulation` is
  stated.
* **Flop counts, level-3 fractions and parallel Givens orderings (§5.2).**
* **The $p$-norm example of the introduction (§5.3).**
* **The numerical examples of §5.3.1 and §5.3.2**, in which $\mathrm{fl}(A^TA)$ is singular.
* **Equations (5.3.18)–(5.3.19).** They are heuristic readings.
* **The comparison of methods in §5.3.7.** It is prose.
* **Björck's claim on the gain of correct digits in iterative improvement (§5.3.8).**
* **Equation (5.3.17).** It is the first-order expansion inside the proof of Theorem 5.3.1.
* **The Problems (§5.3).**
* **Equations (5.4.2)–(5.4.3).** They are approximations.
* **Equation (5.4.4).** It is the backward stability of the Golub–Kahan–Reinsch SVD, an algorithm of
  Chapter 8; it appears only as a hypothesis.
* **The claim $\sigma_{300}(\mathrm{Kah}_{300}(0.99)) = O(10^{-19})$ (§5.4).** It is numerical.
* **The remark that in practice small trailing submatrices almost always emerge (§5.4).** It is
  empirical.
* **Flop counts (§5.4).**
* **The pivot rule (5.4.8) as a separate statement.** It is the choice of the pivot $k$ in
  `GolubVanLoan.Chapter05.algorithm_5_4_1`.
* **The second bound of §5.5.4.** Its middle term cannot be right as printed, and the source gives
  no derivation.
* **The display of the $\delta$-rank in §5.5.4.** It is misprinted; the definition is (5.4.5).
* **The flop table of §5.5.6.** Operation counts are out of scope for the library.
* **The example of an unstable subset (§5.5).** It is a numerical example.
* **The remark that column pivoting tends to produce a well-conditioned $R_{11}$ (§5.5).** It is a
  heuristic.
* **The flop table (Figure 5.6.1).** Operation counts are out of scope for the library.
* **The three arguments in favour of orthogonal methods (§5.6).** They are prose.

**Chapter 6: Modified least squares problems and methods**

* **Equation (6.1.6).** It is a statistical model.
* **Equation (6.1.13).** It recalls the SVD.
* **Equations (6.1.24)–(6.1.25).** They are steps of the proof of Theorem 6.1.1.
* **Paige's claim on the stability of his method (§6.1).**
* **The remark of van der Sluis that $\kappa_2(AG^{-1})$ is approximately minimized (§6.1).**
* **The choice of $\lambda$ that minimizes $C(\lambda)$ (§6.1).**
* **The flop counts (§6.1).** Operation counts are out of scope for the library.
* **Equation (6.2.2).** It recalls the SVD.
* **Equations (6.2.5) and (6.2.9).** They define the problems, which are the backbone predicates
  `Matrix.IsLSQISolution` and `Matrix.IsLSESolution`.
* **The Lagrange-multiplier arguments of §6.2.1, §6.2.2 and §6.2.4.**
* **The remark that there may not be a solution if $\operatorname{rank}(B) < m_2$ (§6.2).**
* **The numerical precautions of Powell and Reid (§6.2).**
* **The flop counts (§6.2).** Operation counts are out of scope for the library.
* **The variants of §6.3.4.**
* **The flop count of Algorithm 6.3.1.**
* **The display $[I_{n-1}\ 0; 0\ \tilde Q]\, U^T (D[A \mid b]T)\, V [I_{n-p}\ 0; 0\ \tilde Q] =
  \Sigma$ of §6.3.2.** Its block sizes do not match.
* **The line "$|t_{n+1}| \|Db\|_2 \ge \sigma_n(DAT_1)$" printed after §6.3.4.** It is a displaced
  fragment of Problem P6.3.1(b).
* **The threshold $1 - \delta$ for a unit singular value (§6.4).** It is a heuristic.
* **Displays (6.4.4)–(6.4.5) (§6.4).** They only name data.
* **The ULV updating procedure of §6.5.5 beyond (6.5.16):** condition estimation, the "small"
  entries, "$\approx \sigma_{\min}$", and zero chasing.
* **The rank-revealing smallness of $L_{21}$ and $L_{22}$ in (6.5.16).** It is a heuristic property
  of QR with column pivoting.
* **The numerical caveats on hyperbolic rotations with $|x_1| \approx |x_2|$ (§6.5).**
* **The flop counts (§6.5)** ($26n^2$, $O(n^2)$, $O(mn)$).
* **Displays (6.5.4), (6.5.5), (6.5.8) and (6.5.9).** They only name data.
* **The numerical caveats on disparate weights, on an ill-conditioned $B$, and on a large $\lambda$
  in the weighting method.**

**Chapter 7: Unsymmetric eigenvalue problems**

* **The roundoff claims (7.1.14)–(7.1.15)**, $fl(X^{-1} A X) = X^{-1} A X + E$ with
  $\|E\|_2 \approx u\, \kappa_2(X) \|A\|_2$. They name no algorithm for forming $X^{-1} A X$, and
  they are approximate.
* **The remark that $\max |\lambda_i| / |\lambda_j| \ll \kappa_2(A)$ may occur (§7.1).** It is an
  illustration. Its rigorous half, $|\lambda_i| / |\lambda_j| \le \kappa_2(A)$, is in
  `GolubVanLoan.Chapter07.sigmaMin_le_norm_eigenvalue`.
* **Wilkinson's bound on the distance to a matrix with a multiple eigenvalue (§7.2)**, $\|E\|_2 /
  \|A\|_2 \le s(\lambda) / \sqrt{1 - s(\lambda)^2}$. The source quotes it from Wilkinson (1972)
  without a proof or a construction of $E$.
* **The heuristic that perturbations of size $O(\varepsilon)$ can move a defective eigenvalue by
  $O(\varepsilon^{1/p})$ (§7.2).** Its rigorous content is the term $\theta^{1/p}$ of Theorem 7.2.3.
* **The discussion of "wobbly" eigenvectors (§7.2).**
* **Stewart's accelerated orthogonal iteration (§7.3).** The source gives only approximate rates and
  no algorithm.
* **The estimates $|\lambda^{(k)} - \lambda_1| \approx \|r^{(k)}\|_2 / s(\lambda_1)$ and
  $s(\lambda_1) \approx |w^{(k)H} q^{(k)}|$ (§7.3).** They are heuristics.
* **The remark that "under reasonable assumptions" the matrices $T_k$ of the LR iteration converge
  to upper triangular form (§7.3).**
* **Equations (7.3.17), (7.3.21) and (7.3.22).** They are identities inside the proof of Theorem
  7.3.1, whose content is the theorem.
* **The flop count (§7.3).**
* **§7.4.4, the level-3 block Hessenberg reduction and the WY form.** It is a discussion at the
  level of BLAS operations.
* **The flop counts (§7.4).**
* **The remark that the computation of eigenvalues through the companion matrix "can be highly
  unstable" (§7.4).** The source makes no precise statement.
* **The deflation criterion (7.5.2) as a heuristic, and the discussion of decoupling.** The
  criterion itself is the deflation step of Algorithm 7.5.2.
* **Stewart's worked example (§7.5)** $\tilde h_{n,n-1} = -\epsilon^2 b/(a^2 + \epsilon^2)$ of
  §7.5.3. Its rigorous content is `GolubVanLoan.Chapter07.single_shift_quadratic`.
* **The roundoff claims of §7.5.6.** The source states them with $\approx$ and gives no derivation.
* **Balancing (§7.5.7).**
* **Flop counts (§7.5).**
* **The quasi-triangular case of Algorithm 7.6.3.** It needs the $2p \times 2p$ systems (7.6.5),
  which the source does not write as an algorithm.
* **The SVD heuristic for why one step of inverse iteration suffices (§7.6).**
* **The stability claims of §7.6.2.**
* **The relative error of the Sylvester solve after (7.6.6).** The source states it with $\approx$
  and gives no derivation.
* **The algorithm of Bavely and Stewart (§7.6).**
* **The $7 \times 7$ example of a Jordan structure in §7.6.5.**
* **The flop counts (§7.6).** Operation counts are out of scope for the library.
* **The backward stability of block diagonalization (§7.6.3).** The source states it with $\approx$
  and gives no derivation.
* **The Kronecker canonical form (§7.7).** The source mentions it but does not state it.
* **The 7-digit example (§7.7).**
* **Stewart's chordal-metric bound and Wilkinson's remark on $t_{kk} = s_{kk} = 0$ (§7.7).** The
  bound is first order and quoted without proof.
* **The backward stability of QZ (§7.7).** The source states it with $\approx$ and gives no
  derivation.
* **Flop counts (§7.7).**
* **Display (7.8.7).** It says that the iterates stay in Hessenberg–triangular–triangular form; the
  source makes no convergence statement.
* **The remark that a structure-preserving QR iteration has yet to be devised, and the quality of
  the eigenvalues computed from $M^2$ (§7.8).** The source makes no precise claims.
* **Rectangular and inverted factors in the product problem (§7.8).** The source only mentions them.
* **Display (7.9.4).** It repeats (7.9.1) and illustrates transient growth.
* **The Eigtool plots and the Kahan, Demmel and `Gallery(5)` matrices (§7.9).**
* **The strategies of §7.9.5 for computing pseudospectra, and the Burke–Lewis–Overton and
  Mengi–Overton algorithms.**
* **The estimate $\sigma_{\min}(zI - T) \approx 1/\|y\|_2$ (§7.9).** It is a heuristic; the rigorous
  upper bound is `GolubVanLoan.Chapter07.sigmaMin_schur`.
* **The convergence of the QR, QZ and product iterations.** The source does not prove it.

**Chapter 8: Symmetric eigenvalue problems**

* **The remark that one step of inverse iteration is usually sufficient (§8.2).** It is a heuristic.
* **Cubic convergence of the shifted QR iteration (§8.3.4).** The source quotes Wilkinson's result
  without proof.
* **The convergence rate of Ritz acceleration (§8.3.7).** The source quotes Stewart's result without
  proof.
* **The backward error of the eigenvalues computed by Algorithm 8.3.3.** The source gives
  $\|E\|_2 \approx u \|A\|_2$ without a derivation; it rests on rounding models of Givens-based
  iterations.
* **Storage and operation counts (§8.3).**
* **§8.4.5**, the parallel divide-and-conquer tree and Figure 8.4.1.
* **§8.4.6**, the Lagrange-multiplier motivation of the inverse eigenvalue problem.
* **Operation counts (§8.4).**
* **The relative accuracy of bisection (§8.4).** The source gives it without derivation.
* **Quadratic convergence of the classical and cyclic methods (§8.5)** (Henrici, Schönhage, van
  Kempen, Wilkinson). The source quotes it without proof.
* **The sweep count of Brent and Luk (§8.5)**, $\log n$ sweeps for the parallel ordering.
* **§8.5.5**, the error analysis, including (8.5.4).
* **Operation counts (§8.5).**
* **The parallel-computing remarks of §8.5.6–8.5.7**, beyond the precise statement about the
  parallel ordering.
* **The backward error of Algorithm 8.6.2 (§8.6)**, $\|E\|_2 \approx u \|A\|_2$. The source gives it
  without derivation.
* **The sketch of §8.6.3 that forms $A^TA$ and then uses QR.**
* **The overdamping theorem of §8.7.9, which the source quotes from Duffin and Veselić.**
* **The characterization of the generalized singular values as stationary values (§8.7).**
* **The product SVD and the restricted SVD of §8.7.8.**
* **The accuracy discussion of §8.7.6.**
* **The backward error of Algorithm 8.7.1 (§8.7)**, $\|E_i\|_2 \approx u \|A\|_2 \|B^{-1}\|_2$. The
  source gives it without derivation.
* **The remedy $V D^{-1/2}$ and the remark on the conditioning of convex combinations in §8.7.2.**
  They are heuristics.

**Chapter 9: Functions of matrices**

* **The numerical example of §9.1.3, with eigenvalues $1 \pm 10^{-5}$.**
* **The $3 \times 3$ illustration of Theorem 9.1.4.**
* **The flop counts (§9.1).**
* **The forward-stability heuristic $\|\hat F - f(A)\| / \|f(A)\| \approx u
  \operatorname{cond}_{\mathrm{rel}}(f, A)$ of §9.1.6.**
* **The clustering step of the block Schur–Parlett method (§9.1).** The source gives an outline
  without a precise claim.
* **Display (9.2.3), the notation for the Taylor remainder $E(s)$.**
* **Display (9.2.4), the entrywise mean-value form of the remainder, a step of the source's proof of
  Theorem 9.2.3.**
* **The numerical examples, among them the matrix $\begin{bmatrix} -49 & 24 \\ -64 & 31
  \end{bmatrix}$ with $q = 9$ after Theorem 9.2.2.**
* **The multiplication counts (§9.2).**
* **The scaling loop for $\sin$ and $\cos$; its exact content is the double-angle formulas,
  `GolubVanLoan.Chapter09.double_angle` (§9.2).**
* **The choice $s = \lfloor \sqrt{q} \rfloor$ as the one that minimizes the work (§9.2).** Operation
  counts are out of scope for the library.
* **The general closed contour of (9.2.8) (§9.2).** The statement is for circles.
* **The accuracy comparisons of §9.1.3 and §9.2.3.**
* **The flop counts (§9.3).**
* **Figure 9.3.1 and the estimate $\alpha_{.01}(A)/.01 \approx 216$.**
* **The heuristic claim of §9.3.2 about a matrix $E$ for which an approximate equality holds.**
* **The heuristic claims of §9.3.4: the rounding estimate $\gamma$ and what "numerical experiments
  suggest".**
* **The four square roots of $\begin{bmatrix} 4 & 10 \\ 0 & 9 \end{bmatrix}$, a numerical example
  (§9.4).**
* **The scaled Newton iteration (9.4.6) and its choices of $\mu_k$.**
* **QR with column pivoting on $(I + \operatorname{sign}(A))/2$; only the statement about the range
  of this projection is formalized (§9.4).**
* **The `while` loop of inverse scaling and squaring; only its identity $\log(A) = 2^k \log(A_k)$ is
  formalized (§9.4).**
* **The Problems (§9.4).**
* **The Newton–Schulz motivation (§9.4).** It is prose.

**Chapter 10: Large sparse eigenvalue problems**

* **(10.1.2)–(10.1.3).** The motivation of the Lanczos process through $M_k$ and $m_k$.
* **(10.1.5).** The display of the tridiagonal $T_k$, which is the backbone's `Lanczos.tridiag`.
* **Figure 10.1.1 and the comparison after (10.1.11).** They are numerical.
* **Operation counts (§10.1).**
* **The Riemann–Stieltjes sums of §10.2.1.**
* **The Golub–Welsch weight formula of Fact 3 for a general weight (§10.2).** The source uses Fact 3
  only through §10.2.4, where it is formalized for the spectral weight.
* **The strict location $a < \eta < b$ in the remainders of the Gauss–Radau and Gauss–Lobatto rules
  (§10.2).** The statements give $\eta \in [a, b]$, which is what the mean value argument of the
  backbone gives.
* **Numerical remarks (§10.2).**
* **Display (10.2.1).** It is notation, not a proposition.
* **(10.3.2)–(10.3.3), (10.3.5)–(10.3.6) and the estimates with $\approx$ between them.** The
  floating-point analysis of §10.3.2 and §10.3.4 is quoted from Paige without derivation.
* **The application of Theorem 8.1.16 at the end of §10.3.2.** It is invalid as printed: $\hat T_k$
  is not $\hat Q_k^T A \hat Q_k$.
* **The ghost-eigenvalue discussion of §10.3.5 and the restarted block Lanczos of §10.3.7.** They
  are prose.
* **The claim that (10.3.4) gives vectors that are orthogonal to working precision, and the choice
  of $X_{k+1}$ when some $R_k$ is rank deficient (Golub–Underwood).** They are prose.
* **The randomized sampling of §10.4.5** and its probabilistic error bound.
* **The $4 \times 3$ permutation example of §10.4.3.**
* **Operation counts (§10.4).**
* **The expansion of the filtered vector in eigenvectors of $A$, (10.5.3).**
* **The exact-shift heuristic (§10.5)** for the filter values.
* **The look-ahead idea of §10.5.6.**
* **Operation counts (§10.5).**
* **Convergence of the methods (§10.6).** The source makes no convergence claim.
* **The trace-min iteration of §10.6.5.** The source sketches it without a claim.
* **Restarting the Davidson and Jacobi–Davidson loops (§10.6).** The source only mentions it.
* **The trade-offs in the choice of the block size.** They are heuristics.
* **The Problems of Chapter 10**, except P10.5.2, which is a backbone helper.

**Chapter 11: Large sparse linear system problems**

* **The heuristics and challenges of choosing $P$ (§11.1).** Choosing $P$ to minimize
  $\mathrm{nnz}(G)$ is not a statement.
* **Markowitz pivoting and the threshold $\tau$ (§11.1).**
* **The elimination tree (§11.1).** The source defines it in prose and states no theorem about it.
* **The row orderings for sparse QR (§11.1)**, including the row orderings that limit fill-in during
  (11.1.9).
* **The complexity claims of §11.1.2 and §11.1.7.**
* **Björck's accuracy claim for the seminormal equations with one refinement step (§11.1).**
* **The numerical examples (§11.1):** (11.1.5), its profile $37 \to 25$, and the elimination tree
  example of Davis. Numerical examples are out of scope for the library.
* **The Problems of §11.1.** Problems are out of scope for the library.
* **The reverse Cuthill–McKee ordering (§11.1).** The source quotes its properties without proof.
* **Display (11.2.1).** It is the case $n = 3$ of (11.2.2).
* **The discussion of vectorization and parallelism (§11.2).**
* **The remark that the Jacobi radius (11.2.15) approaches $1$.** The text does not state the limit
  precisely.
* **Young's theory of the optimal $\omega$ (§11.2).**
* **The Problems (§11.2).**
* **The remark that the more dominant the diagonal, the faster the convergence (§11.2).** It is a
  heuristic.
* **The operation counts and storage of §11.3.5 and §11.3.8** (the "13n flops" and the four arrays).
  Operation counts are out of scope for the library.
* **The uniqueness claim of §11.3.3** that the only way to satisfy the requirement of (11.3.11) is
  $S_k = \mathcal{K}(A, g_0, k)$. It has no precise statement.
* **The Problems of §11.3.** Problems are out of scope for the library.
* **The Notes and References of §11.3.** They are out of scope for the library.
* **The operation counts of §11.4**, such as "$O(1)$ flops" and "$O(n)$ work", and Problem P11.4.1.
  Operation counts are out of scope for the library.
* **The short recurrences of MINRES, SYMMLQ and LSQR (§11.4)** that avoid storing all Lanczos
  vectors, which the source describes in prose.
* **The monotonicity of $\|r_k\|_2$ for LSMR without full column rank (§11.4).** The general case
  needs the energy argument on $\operatorname{ran} A^T$, where $A^TA$ is positive definite.
* **The look-ahead remark (§11.4).**
* **The remark that CGS typically outperforms BiCG (§11.4).** It is an observation, not a statement.
* **The advice on when to use which method (§11.4).**
* **The Notes and References of §11.4.**
* **§11.5.4** (Toeplitz and circulant preconditioners). T. Chan's and Strang's choices are
  definitions with no claim.
* **§11.5.8**, the drop-tolerance and $\mathrm{ILU}(\ell)$ variants.
* **§11.5.10**, the HSS saddle-point preconditioner. The source cites its effectiveness and proves
  nothing.
* **§11.5.1**, the cost inequality and Criteria 1–2.
* **§11.5.9**, the heuristic choices of $\Lambda_k$.
* **The Problems (§11.5).**
* **The L-shaped domain of §11.5.11, and the claims that a matrix discretizes a differential
  equation.**
* **Equation (11.6.1)**, the differential equation and the discretization claim.
* **Equation (11.6.13)**, the example matrices for $n = 7$.
* **Equation (11.6.21)**, the instance for $n = 7$, which the source prints with a row missing.
* **The V-cycle `mgV`, full multigrid and §11.6.5.** The text states no property of them beyond flop
  counts and the heuristic that the rate of convergence is independent of $n$.
* **The Problems (§11.6).**
* **Storage formats as such.**

**Chapter 12: Special topics**

* **The non-recursive sketch of Algorithm 12.1.1.**
* **The stability of Algorithm 12.1.2.** The source cites it from Gu (1998) and analyses no rounding
  errors in the chapter.
* **The $n = 4$ example of the Cauchy generator update in §12.1.3.** Numerical examples are out of
  scope for the library.
* **The "Steps 1–4" framework of §12.1.8**, beyond its correctness statement.
* **The flop counts (§12.1).** Operation counts are out of scope for the library.
* **The Problems of §12.1.** Problems are out of scope for the library. Part (a) of Problem P12.1.1
  is proved as a supporting lemma.
* **The operation and storage counts (§12.2).** Operation counts are out of scope for the library.
* **The $\{p, q\}$-semiseparable definition of §12.2.8.** It is misprinted.
* **The extended, sequentially semiseparable and hierarchical classes of §12.2.8.** The display
  (12.2.17) shows only a shape.
* **§12.2.9.** It describes eigenvalue methods in prose with citations.
* **The pivoting variant of Algorithm 12.2.1.** The source describes it in words only.
* **Fact 3 of §12.2.10.** It names neither the perfect shuffles nor the positions of the bidiagonal
  blocks, and the source proves nothing.
* **The Problems of §12.2.** Problems are out of scope for the library.
* **§12.3.7, constrained nearest Kronecker products.** The positive definiteness and the
  nonnegativity of $B_{opt}$ and $C_{opt}$ are cited without proof, and the reduction for Toeplitz
  constraints is a method sketch.
* **The memory-hierarchy discussion of multipass transposition in §12.3.5**, beyond the two-pass
  identity.
* **The dynamic-programming remark of §12.3.10**, beyond the reshaping identity.
* **The remark of §12.3.1 that rectangular $R$ factors need row permutations to become triangular.**
  It is prose.
* **The small numerical examples (§12.3).** Numerical examples are out of scope for the library.
* **The operation counts (§12.3).** Operation counts are out of scope for the library.
* **The Problems of §12.3.** Problems are out of scope for the library.
* **The loops (12.4.1) and (12.4.12).**
* **The numerical examples (§12.4)**: the $2 \times 2 \times 3 \times 4$ unfolding of §12.4.1, the
  vec and transposition examples of §12.4.3–12.4.4, and (12.4.7). Numerical examples are out of
  scope for the library.
* **The vec formula for $\mathcal{A}^{\langle [3\,2\,1] \rangle}$ (§12.4)** in the transposition
  example. The source misprints it; the correct formula is $(\mathcal{P}_{n_2, n_1} \otimes I_{n_3})
  \mathcal{P}_{n_3, n_1 n_2}$.
* **The space–time contraction example of §12.4.12.**
* **The flop counts (§12.4).** Operation counts are out of scope for the library.
* **The "Repeat" iterations (§12.5)** of Tucker and CP alternating least squares and of the
  higher-order power methods, as programs. What each update solves is formalized.
* **The TT-SVD procedure (12.5.29) as a program.** Its ranks depend on the data, so the shapes of
  its carriages depend on the run.
* **The claim that the truncated HOSVD does not solve the Tucker problem (§12.5).** The source gives
  no example.
* **Complications 1–6 of §12.5.5** on tensor rank: NP-hardness, maximal and typical ranks, real
  versus complex rank, and degeneracy.
* **The counts for tensor trains (§12.5).**
* **The MATLAB fragments.**
-/
