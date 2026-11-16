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

* **Algorithm 1.2.1** (generalization). The source takes $C$ upper triangular; the specification
  holds for every $C$. See `GolubVanLoan.Chapter01.algorithm_1_2_1_spec`.
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
* **§1.4.3, the Haar matrix** (typo). The printed recursion for $W_{2m}$ lost its brackets, and the
  printed $W_4$ and the sixth row of $W_8$ are garbled; the definition follows $W_2$ and the intact
  rows of $W_8$. See `GolubVanLoan.Chapter01.haarMatrix`.
* **Algorithm 1.4.4** (typo). The source writes $y(1{:}2{:}m)$ and $y(2{:}2{:}m)$ for $y(1{:}2{:}n)$
  and $y(2{:}2{:}n)$. See `GolubVanLoan.Chapter01.algorithm_1_4_4`.

**Chapter 2: Matrix analysis**

* **Corollary 2.4.5** (reading). The source does not define $\sigma_{\min}$ of an $m \times 0$
  matrix; the corollary assumes $n \ge 1$. See `GolubVanLoan.Chapter02.corollary_2_4_5`.
* **Remark after Theorem 2.4.8** (reading). The statement that $\sigma_{\min}(A)$ is the distance to
  the rank-deficient matrices assumes $m, n \ge 1$. See
  `GolubVanLoan.Chapter02.sigmaMin_eq_dist_rankDeficient`.
* **Section 2.5.3, $\operatorname{dist}(S_1, S_2) = 0 \Rightarrow S_1 = S_2$** (generalization). The
  source states an implication. The theorem is an equivalence and needs no hypothesis on the
  dimensions. See `GolubVanLoan.Chapter02.subspaceDist_eq_zero`.
* **Section 2.5.3, $\operatorname{dist}(S_1, S_2) = 1 \Rightarrow S_1 \cap S_2^\perp \neq \{0\}$**
  (generalization). The source states an implication. The theorem is an equivalence. See
  `GolubVanLoan.Chapter02.subspaceDist_eq_one`.
* **Theorem 2.5.3** (generalization). The source assumes $m_1 \ge m_2$ and that $Q$ is orthogonal.
  The theorem does not assume $m_1 \ge m_2$, and it assumes only $Q^T Q = I$ for the square matrix
  $Q$. See `GolubVanLoan.Chapter02.theorem_2_5_3`.
* **Theorem 2.5.3** (typo). The row labels of the block display are misprinted ($n_1 - n_1$). The
  block sizes that add up are the rows $p, n_1 - p, m_1 - n_1 \mid n_1 - p, q$ and the columns
  $p, n_1 - p \mid n_1 - p, q, m_1 - n_1$. See `GolubVanLoan.Chapter02.theorem_2_5_3`.
* **Lemma 2.6.1** (reading). The source carries the nonsingularity of $A$ through the convention
  $\kappa(A) = \infty$. The lemma has the explicit hypothesis that $A$ is nonsingular. See
  `GolubVanLoan.Chapter02.lemma_2_6_1`.
* **Theorem 2.6.3** (typo). The source prints the hypothesis as $\delta \kappa_\infty(A) = r < 1$,
  with $\delta$ for $\epsilon$. See `GolubVanLoan.Chapter02.theorem_2_6_3`.

**Chapter 3: General linear systems**

* **§3.2.5, the inverse of a Gauss transformation** (generalization). The source states
  $M_k^{-1} = I_n + \tau e_k^T$ for a Gauss transformation. The theorem needs only $\tau_k = 0$. See
  `GolubVanLoan.Chapter03.gaussTransformation_inv`.
* **Algorithm 3.2.3** (correction). The source assumes that $A$ has an LU factorization. This does
  not exclude a zero pivot, for example $A = \begin{bmatrix} 0 & 1 \\ 0 & 1 \end{bmatrix}$, and the
  algorithm then fails. The specification assumes that $A(1{:}k, 1{:}k)$ is nonsingular for
  $k = 1, \dots, n-1$. See `GolubVanLoan.Chapter03.algorithm_3_2_3_spec`.
* **Algorithm 3.2.4** (correction). The same hypothesis replaces "$A$ has an LU factorization". See
  `GolubVanLoan.Chapter03.algorithm_3_2_4_spec`.
* **Theorems 3.3.1 and 3.3.2** (generalization). The source assumes that the entries of $A$ are
  floating point numbers. The theorems hold for every real matrix $A$. See
  `GolubVanLoan.Chapter03.theorem_3_3_1` and `GolubVanLoan.Chapter03.theorem_3_3_2`.
* **Theorem 3.3.1** (generalization). The source assumes that no zero pivots occur. Only the pivots
  that are used as divisors, $\hat u_{jj}$ for $j < n$, must be nonzero. See
  `GolubVanLoan.Chapter03.theorem_3_3_1`.
* **(3.4.8)** (correction). The source defines the growth factor on the computed stages
  $\hat A^{(k)}$. The definition uses the exact stages, since only these admit bounds. See
  `GolubVanLoan.Chapter03.growthFactorStages`.
* **(3.4.9)** (reading). The source's $\rho$ bounds the computed $\hat U$ through
  $|\hat u_{ij}| \le \rho \|A\|_\infty$. The theorem takes this bound as a hypothesis, with any
  $\rho \ge 0$. See `GolubVanLoan.Chapter03.equation_3_4_9`.
* **(3.4.10)** (correction). The source prints the bound with $k$ in place of $k + 1$, which is
  false for $k = 1$ when $A^{(k)}$ is the matrix after $k$ steps. See
  `GolubVanLoan.Chapter03.equation_3_4_10`.
* **Heuristic I (§3.5)** (reading). The source states $\|b - A\hat x\|_\infty \approx u \|A\|_\infty
  \|\hat x\|_\infty$. The theorem states a rigorous bound under the hypotheses of (3.4.9). See
  `GolubVanLoan.Chapter03.heuristic_I`.
* **(3.5.2)** (reading). The source states $\|\hat x - x\|_\infty / \|x\|_\infty \approx u
  \kappa_\infty(A)$. The theorem states the bound $2\varepsilon\kappa_\infty(A) / (1 -
  \varepsilon\kappa_\infty(A))$ for a backward error of size $\varepsilon$. See
  `GolubVanLoan.Chapter03.equation_3_5_2`.
* **(3.5.3)** (generalization). The source takes $D_1$ and $D_2$ diagonal. The theorem holds for any
  nonsingular $D_1$, $D_2$. See `GolubVanLoan.Chapter03.equation_3_5_3`.
* **Algorithm 3.5.1** (reading). The source says $\|Ty\|_\infty \approx 1/\|T^{-1}\|_\infty$ and
  $\kappa \approx \kappa_\infty(T)$. The theorem states the inequalities that hold in exact
  arithmetic. See `GolubVanLoan.Chapter03.algorithm_3_5_1_spec`.
* **§3.6.1, block column induction** (generalization). The source assumes $n = rN$; the last block
  column may be narrower. See `GolubVanLoan.Chapter03.exists_blockLUPivoting`.

**Chapter 4: Special linear systems**

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
* **(4.4.9)** (typo). The vector $[0; \ell_{52}; \ell_{53}; \ell_{53}; \ell_{54}]$ should read
  $[0; \ell_{52}; \ell_{53}; \ell_{54}; 1]$. See `GolubVanLoan.Chapter04.equation_4_4_14`.
* **(4.4.10)** (typo). The loop starts at $k = 1$, which needs an undefined $\beta_0$. The program
  follows (4.4.14), whose loop starts at $k = 2$. See `GolubVanLoan.Chapter04.aasenNoPivot`.
* **(4.4.15)** (generalization). The pivot block $E$ need not be symmetric for the displayed
  factorization. See `GolubVanLoan.Chapter04.equation_4_4_15`.
* **(4.4.20)** (generalization). The source assumes that $C$ is diagonal. The library assumes only
  that $C$ is symmetric positive definite. See `GolubVanLoan.Chapter04.equation_4_4_20`.
* **(4.5.8)** (reading). The source prints $\|U_i\|_1 \le \|A_n\|_1$, whose right-hand side has no
  referent in the section. It is read as the $1$-norm of the whole matrix $A$. See
  `GolubVanLoan.Chapter04.equation_4_5_8`.
* **The display for $N = 7$ in §4.5.3** (typo). The source prints $b_4 = Fx_5 + Dx_4 + Fx_5$ for
  $b_4 = Fx_3 + Dx_4 + Fx_5$. See `GolubVanLoan.Chapter04.cyclicReduction_step`.
* **(4.7.6), lower bound** (generalization). The source prints the two lower bounds with an extra
  factor $1/(n - 1)$. The bounds hold without it. See `GolubVanLoan.Chapter04.equation_4_7_6_lower`.
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
* **Equation (5.1.11)** (reading). The orthogonal matrices $Q_k$ and $Z_k$ are the exact
  transformations determined by the computed data at each step. See
  `GolubVanLoan.Chapter05.equation_5_1_11`.
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
* **Algorithm 5.4.2** (typo). The source prints the second call of `house` as "ho se". See
  `GolubVanLoan.Chapter05.algorithm_5_4_2`.
* **§5.5.1** (typo). The source writes $z \in \operatorname{hull}(A)$ where
  $z \in \operatorname{null}(A)$ is meant. See `GolubVanLoan.Chapter05.minNorm_existsUnique`.
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
* **Theorem 5.6.1** (reading). The source states a first-order bound with an implicit
  $O(\epsilon^2)$ term. The library reads the remainder as $K \epsilon^2$ for all perturbations with
  $\epsilon \le \epsilon_0$, and also proves a rigorous bound in which $\sigma_m(A)$ is replaced by
  $\sigma_m(A) - \|\delta A\|_2$. See `GolubVanLoan.Chapter05.theorem_5_6_1_firstOrder` and
  `GolubVanLoan.Chapter05.theorem_5_6_1`.

**Chapter 6: Modified least squares problems and methods**

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
* **§6.2.1, the secular equation** (reading). The source's $f(0) > 0$ is read as
  $f(0^+) = \|x_{LS}\|_2^2 - \alpha^2 > 0$, because $x(\lambda)$ is $x_{LS}$ only in the limit. See
  `GolubVanLoan.Chapter06.secular_existsUnique`.
* **Algorithm 6.2.1** (generalization). The source assumes $m \ge n$; the correctness statement
  holds for all $m$ and $n$. See `GolubVanLoan.Chapter06.algorithm_6_2_1_spec`.
* **Equation (6.2.6)** (typo). The source cites "(6.2.23)" for (6.1.23). See
  `GolubVanLoan.Chapter06.equation_6_2_6`.
* **Equation (6.2.7)** (reading). The source prints it in the block order of the GSVD of the third
  edition, which is inconsistent with Theorem 6.1.1. The library uses the block order of Theorem
  6.1.1. See `GolubVanLoan.Chapter06.equation_6_2_7`.
* **Equation (6.2.8)** (correction). The source prints it in the block order of the third edition,
  and its second sum, over $\tilde d_i$ for $i = m_2 + 1, \dots, n_1$, is meaningless. See
  `GolubVanLoan.Chapter06.equation_6_2_8`.
* **§6.2.3, non-uniqueness of the LSE solution** (reading). The printed sentence is garbled. The
  library states that an LSE solution exists for $d \in \operatorname{ran}(B)$ and stays a solution
  after adding a vector of $\operatorname{null}(A) \cap \operatorname{null}(B)$. See
  `GolubVanLoan.Chapter06.isLSESolution_not_unique`.
* **Algorithm 6.2.2** (generalization). The source assumes $m_2 < n_1$; the correctness statement
  allows $m_2 \le n_1$. See `GolubVanLoan.Chapter06.algorithm_6_2_2_spec`.
* **Equation (6.2.12)** (correction). The source prints it in the block order of the third edition.
  See `GolubVanLoan.Chapter06.equation_6_2_12`.
* **Equation (6.2.14)** (correction). The source prints it in the block order of the third edition,
  with $\lambda^2$ for $\lambda$, $u_i^T b$ and $v_i^T d$ for $\tilde b_i$ and $\tilde d_i$, and the
  range $1{:}p$. See `GolubVanLoan.Chapter06.equation_6_2_14`.
* **Theorem 6.3.1, nonsingularity of $V_{22}$** (generalization). The source assumes that $D$ and
  $T$ are nonsingular and $m \ge n + k$. The nonsingularity of $V_{22}$ holds without these
  hypotheses. See `GolubVanLoan.Chapter06.theorem_6_3_1_isUnit`.
* **§6.3.2, the single right-hand side** (generalization). The source takes $\tilde Q$ to be a
  Householder matrix. The statement holds for every orthogonal $\tilde Q$ with the same zero
  pattern. See `GolubVanLoan.Chapter06.tls_single`.
* **§6.3.2, the single right-hand side** (reading). The source says that the last column has the
  largest $(n{+}1)$st component of all vectors in the span. The statement compares absolute values
  over the unit vectors of the span. See `GolubVanLoan.Chapter06.tls_single`.
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
* **Theorem 6.5.1** (typo). The statement is garbled in print ("If / and / A = …"). See
  `GolubVanLoan.Chapter06.theorem_6_5_1`.
* **Equation (6.5.16)** (generalization). The source obtains $\Pi$ and $R$ from QR with column
  pivoting. The statement holds for every orthogonal $\Pi$ and every $R$ with $U^T A \Pi = [R; 0]$.
  See `GolubVanLoan.Chapter06.equation_6_5_16`.
* **§6.5.5** (typo). In $\|AV_2\|_2 = \|U_2 L_{22}\|_2$, the source takes $U_2 = U(:, r{+}1{:}m)$,
  which does not match the $n - r$ rows of $L_{22}$. The columns $r{+}1{:}n$ of $U$ are meant; in
  both readings the norm is $\|L_{22}\|_2$. See `GolubVanLoan.Chapter06.ulv_nullspace_norm`.

**Chapter 7: Unsymmetric eigenvalue problems**

* **Equation (7.1.3)** (typo). The source prints the maximum as $\max_{\lambda \in \lambda(A)}$. The
  maximum is over the unit vectors $x$. See `GolubVanLoan.Chapter07.numericalRadius`.
* **Lemma 7.1.5, block diagonalization** (generalization). The source assumes that $\phi$ is
  nonsingular. The statement needs only a solution $Z$ of $\phi(Z) = -T_{12}$. See
  `GolubVanLoan.Chapter07.lemma_7_1_5_blockDiagonal`.
* **Theorem 7.1.6** (typo). The source prints the hypothesis as $\lambda(T_{ij}) \cap
  \lambda(T_{jj}) = \emptyset$. It means $\lambda(T_{ii}) \cap \lambda(T_{jj}) = \emptyset$. See
  `GolubVanLoan.Chapter07.theorem_7_1_6`.
* **Equation (7.1.13)** (reading). The source says that the diagonalizing matrix has "a 2-norm
  condition of order $1/\varepsilon$". The statement gives the lower bound $1/(2\varepsilon)$ for
  every diagonalizing matrix and the upper bound $1/\varepsilon + 2\varepsilon$ for one of them. See
  `GolubVanLoan.Chapter07.equation_7_1_13`.
* **Theorem 7.2.3** (generalization). The source takes a Schur decomposition, with $N$ strictly
  upper triangular, and the least $p$ with $|N|^p = 0$. The theorem holds for every $p \ge 1$ with
  $|N|^p = 0$ and every such $N$. See `GolubVanLoan.Chapter07.theorem_7_2_3`.
* **§7.2.3** (reading). The source says that the rate of change of the eigenvalues at the origin is
  infinite. The statement reads this as: no branch of eigenvalues is differentiable at
  $\varepsilon = 0$. See `GolubVanLoan.Chapter07.repeated_eigenvalue_example`.
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
* **(7.5.3) and (7.5.6)–(7.5.7)** (generalization). The source takes the factorizations to be QR
  factorizations. The identities hold for any second factor $R$, $R_1$, $R_2$. See
  `GolubVanLoan.Chapter07.equation_7_5_3` and `GolubVanLoan.Chapter07.equation_7_5_7`.
* **§7.5.2, the rate of the fixed-shift iteration** (reading). The source states the rate
  $|(\lambda_{p+1} - \mu)/(\lambda_p - \mu)|^k$ by reference to the theory of §7.3. The theorem
  assumes a diagonalizable $A$ with real eigenvalues, distinct nonzero $|\lambda_i - \mu|$ and a
  general-position condition, and it gives the bound $C (r / |\lambda_p - \mu|)^k$ for every
  $r > |\lambda_{p+1} - \mu|$. See `GolubVanLoan.Chapter07.shiftedQr_rate`.
* **Theorem 7.5.1** (generalization). The source concludes $\tilde h_{n,n-1} = 0$ and
  $\tilde h_{nn} = \mu$. The theorem shows that the whole last row of $\tilde H$ is $\mu e_n^T$. See
  `GolubVanLoan.Chapter07.theorem_7_5_1`.
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
* **§7.7.8, generalized inverse iteration** (typo). The source prints the eigenvalue estimate as
  $\lambda^{(k)} = q^{(k)H} A q^{(k)} / q^{(k)H} A q^{(k)}$; the denominator is
  $q^{(k)H} B q^{(k)}$. See `GolubVanLoan.Chapter07.generalizedInverseIteration_eq`.
* **Equation (7.8.1)** (typo). The source labels the blocks $F$ and $G$ of the Hamiltonian matrix in
  (7.8.1) differently from Figure 7.8.1. See `GolubVanLoan.Chapter07.equation_7_8_1` and
  `GolubVanLoan.Chapter07.equation_7_8_2`.
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
* **§7.9.1, the citation in the power bound of the $2 \times 2$ example** (typo). The source cites
  "Lemma 7.3.1" for Lemma 7.3.2. See `GolubVanLoan.Chapter07.two_by_two_power_bound`.
* **Proofs of Theorems 7.9.1 and 7.9.2** (typo). The proofs in the source contain misprints. The
  statements are not affected. See `GolubVanLoan.Chapter07.theorem_7_9_1` and
  `GolubVanLoan.Chapter07.theorem_7_9_2`.

**Chapter 8: Symmetric eigenvalue problems**

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
* **Equations (8.2.1)–(8.2.2)** (generalization). The source takes $U_0$ orthogonal. The similarity
  $T_k = (U_0 \cdots U_k)^T A (U_0 \cdots U_k)$ and the symmetry of $T_k$ hold for every $U_0$, and
  the $R_k$ need not be upper triangular. See `GolubVanLoan.Chapter08.equation_8_2_2`.
* **Equation (8.2.7)** (correction). The source omits the hypothesis $c_k s_k \neq 0$; without it
  $\mu_k$ is an eigenvalue and the step is not defined. See `GolubVanLoan.Chapter08.equation_8_2_7`.
* **Equation (8.2.7)** (typo). The source loses the minus sign: the next iterate is
  $(c_k^3, -s_k^3)/\sqrt{c_k^6 + s_k^6}$. See `GolubVanLoan.Chapter08.equation_8_2_7`.
* **Equation (8.2.13)** (typo). The source defines both $V_k$ and $W_k$ with $Q_0$;
  $V_k = Q_\alpha^T Q_k$ and $W_k = Q_\beta^T Q_k$ are meant. See
  `GolubVanLoan.Chapter08.equation_8_2_13`.
* **§8.3.3, preservation of form** (correction). The source states it for every QR factorization
  $T = QR$. For singular $T$ the orthogonal factor is not unique ($T = 0 = Q \cdot 0$ for every
  orthogonal $Q$), and the claim fails. The statements assume that $T$ (or $T - sI$) is nonsingular
  or that $(Q, R)$ is the Givens QR factorization. See
  `GolubVanLoan.Chapter08.qr_tridiagonal_preservation` and
  `GolubVanLoan.Chapter08.shifted_qr_tridiagonal`.
* **Equation (8.3.3)** (reading). The source does not fix $\operatorname{sign}(0)$. The Wilkinson
  shift needs $\operatorname{sign}(0) = 1$. See `GolubVanLoan.Chapter08.wilkinsonShift`.
* **Theorem 8.3.2** (generalization). The source takes $A$ symmetric, which makes $T$ and $S$
  tridiagonal. The theorem uses only that $T$ and $S$ are tridiagonal. See
  `GolubVanLoan.Chapter08.theorem_8_3_2`.
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
* **Theorem 8.6.5** (typo). The source swaps $P$ and $Q$: its $Q$ is $(n - r) \times r$. See
  `GolubVanLoan.Chapter08.theorem_8_6_5`.
* **Theorem 8.6.5** (correction). As printed, the theorem is false for $m > n$. For $m > n$ the
  declaration adds Wedin's condition $\delta \le \sigma_{\min}(A_{11})$. See
  `GolubVanLoan.Chapter08.theorem_8_6_5` and `GolubVanLoan.Chapter08.theorem_8_6_5_counterexample`.
* **Algorithm 8.6.1** (typo). The source says $B \in \mathbb{R}^{m \times n}$ for a square $B$. See
  `GolubVanLoan.Chapter08.algorithm_8_6_1`.
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

* **§9.1.2, the logarithm series** (typo). The source prints $\log(I - A) = \sum_{k \ge 1} A^k / k$,
  which is the series of $-\log(I - A)$. See `GolubVanLoan.Chapter09.taylor_log_one_sub`.
* **Equation (9.1.7)** (generalization). The source restricts the identity to functions given by a
  Taylor series. It holds for every $f$. See `GolubVanLoan.Chapter09.equation_9_1_7`.
* **Equation (9.1.8)** (typo). The source prints $f(X^{-1} A X) = X f(A) X^{-1}$, with $X$ and
  $X^{-1}$ exchanged on the right. See `GolubVanLoan.Chapter09.equation_9_1_8`.
* **Theorem 9.2.1** (typo). The source takes the maximum over $1 \le i \le p$. The intended range is
  $1 \le i \le q$, the blocks of the Jordan form. See `GolubVanLoan.Chapter09.theorem_9_2_1`.
* **Equation (9.2.1) and Theorem 9.2.2** (reading). The source takes $\Omega$ closed and convex, but
  the supremum $\delta_r$ is finite only for bounded $\Omega$. The statements take $\Omega$ compact
  and convex. See `GolubVanLoan.Chapter09.equation_9_2_1` and
  `GolubVanLoan.Chapter09.theorem_9_2_2`.
* **Equation (9.2.7)** (correction). The source bounds the error by
  $\max_{a \le t \le b} \|f^{(4)}(At)\|_2$, without the factor $A^4$, which is false. The statement
  has $\max_{a \le t \le b} \|A^4 f^{(4)}(At)\|_2$. See `GolubVanLoan.Chapter09.equation_9_2_7`.
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
* **§9.4.1** (typo). The source derives the Jordan-form expression of $\operatorname{sign}(A)$ "from
  Theorem 9.1.1", which does not exist; the expression follows from the definition (9.1.3)–(9.1.4).
  The source also writes $S^2 = S$ for $S^2 = I$. See `GolubVanLoan.Chapter09.matrixSign_eq_conj`.
* **§9.4.2, the principal square root** (reading). The source leaves implicit that $A$ has no
  eigenvalue on $(-\infty, 0]$. The statement assumes it. See
  `GolubVanLoan.Chapter09.principalSqrt_existsUnique`.
* **Equation (9.4.11)** (reading). The body of the iteration is lost in the source. It is read off
  (9.4.12) as $X_{k+1} = (X_k + X_k^{-T})/2$. See `GolubVanLoan.Chapter09.equation_9_4_12`.
* **§9.4.3, $\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix}\right) =
  \begin{bmatrix} 0 & U \\ U^T & 0 \end{bmatrix}$** (correction). The identity needs $A$ to be
  nonsingular, which the source omits. See `GolubVanLoan.Chapter09.sign_block_polar`.
* **§9.4.3, the Li–Sun bound** (correction). The bound is false for nonsingular $A$ and $\tilde A$
  alone. The statement assumes $\det A \cdot \det \tilde A > 0$. See
  `GolubVanLoan.Chapter09.li_sun`.
* **§9.4.3, the citation of Li and Sun** (typo). The source dates the paper "(2003)". It appeared in
  SIAM J. Matrix Anal. Appl. 23 (2002). See `GolubVanLoan.Chapter09.li_sun`.

**Chapter 10: Large sparse eigenvalue problems**

* **Theorem 10.1.2** (reading). The hypothesis $q_1^T z_1 \neq 0$, implicit in the source, is
  explicit. The source's $\rho_1$ is undefined when $\lambda_2 = \lambda_n$; the statement takes
  $\rho_1 = 0$ and needs no gap hypothesis. See `GolubVanLoan.Chapter10.theorem_10_1_2`.
* **Corollary 10.1.3** (typo). The source writes $\cos\phi_n = q_1^T z_n$ without the absolute
  value. See `GolubVanLoan.Chapter10.corollary_10_1_3`.
* **Golub's rank-one modification, §10.1.4** (generalization). The source takes
  $\tau \in \{-1, 1\}$; the statement holds for every real $\tau$. See
  `GolubVanLoan.Chapter10.golub_rankOne_modification`.
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
* **Theorem 10.3.2** (reading). The source's $\rho_i$ is undefined when $\lambda_{p+1} = \lambda_n$;
  the statement takes $\rho_i = 0$ and needs no gap hypothesis. See
  `GolubVanLoan.Chapter10.theorem_10_3_2`.
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
* **Equation (10.6.13)** (typo). The source prints $\alpha + + c^T z_c$ in the right-hand side; the
  intended term is $\alpha + c^T z_c$. See `GolubVanLoan.Chapter10.equation_10_6_13`.
* **Trace-min principle, §10.6.5** (correction). The source says that every minimizer
  $V_{\mathrm{opt}}$ has $V_{\mathrm{opt}}^T A V_{\mathrm{opt}}$ diagonal; this holds only for some
  minimizer. See `GolubVanLoan.Chapter10.isLeast_trace_transpose_mul_mul`.

**Chapter 11: Large sparse linear system problems**

* **Equation (11.1.8)** (correction). The source runs the loop for $k = 1{:}n-2$, which leaves the
  last two columns unfactored; the program runs it for $k = 1{:}n$. See
  `GolubVanLoan.Chapter11.choleskyWithPivoting`.
* **Formula after Fact 2, §11.1.6** (generalization). The source states the formula for $j < i$; it
  holds for all $i$ and $j$. See `GolubVanLoan.Chapter11.cholesky_apply_eq`.
* **Facts 1–2, §11.1.6** (reading). The source says that $g_{ij}$ is nonzero at the predicted
  positions "assuming no numerical cancellation", which has no exact reading; the theorem states the
  exact converse, that $g_{ij}$ vanishes off the symbolic fill. See
  `GolubVanLoan.Chapter11.cholesky_eq_zero_of_not_isCholeskyFill`.
* **Structural symmetry, §11.1.9** (correction). The source says that one elimination step keeps
  structural symmetry; this is false for the computed $A^{(1)}$, and the theorem states it for the
  predicted pattern. See `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm` and
  `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm_counterexample`.
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
* **Corollary 11.3.2** (generalization). The source assumes that $D$ is symmetric and that $r < n$;
  neither is needed. See `GolubVanLoan.Chapter11.corollary_11_3_2`.
* **Equation (11.3.14)** (correction). The source prints $x_k = Q_ky_k$, which holds only for
  $x_0 = 0$; the method computes $x_k = x_0 + Q_ky_k$. See `GolubVanLoan.Chapter11.preliminaryCG`.
* **Equation (11.3.19)** (typo). The source prints the garbled
  $v_k = [\nu_1; \dots; \nu_{k-1}/\nu_k]$ for $v_k = [v_{k-1}; \nu_k]$. See
  `GolubVanLoan.Chapter11.equation_11_3_19`.
* **Theorem 11.3.4** (generalization). The orthogonality $g_i^Tg_j = 0$ holds for $0 \le i < j$, not
  only for $1 \le i < j$. See `GolubVanLoan.Chapter11.theorem_11_3_4`.
* **Theorem 11.3.5** (typo). The source prints the range $1 \le i < j \le k$, which excludes the
  case $i = j$ of its own statement; the range is $1 \le i, j \le k$. See
  `GolubVanLoan.Chapter11.theorem_11_3_5`.
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
* **Grid sizes (§11.6)** (generalization). The source takes $n = 2^k - 1$. Everything it proves uses
  only $n = 2m + 1$, and the results hold for every $m$. See `GolubVanLoan.Chapter11.modelA`.
* **Equation (11.6.16)** (typo). The source updates $u_c$ instead of $u_{p_1}$ in the coarse-grid
  correction. See `GolubVanLoan.Chapter11.coarseGridCorrection`.
* **§11.6.2**, the optimal $\omega$ (reading). The source says that the minimization of the
  high-frequency damping factor "is essentially solved by $\omega_{\mathrm{opt}} = 2/3$"; the
  statement gives the exact minimizer and its limit $2/3$. See
  `GolubVanLoan.Chapter11.weightedJacobi_optimalOmega`.

**Chapter 12: Special topics**

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
* **Equation (12.3.9)** (typo). The source states $X \in \mathbb{R}^{n_1 \times m_2}$ for
  $X \in \mathbb{R}^{n_2 \times n_1}$. See `GolubVanLoan.Chapter12.equation_12_3_9`.
* **§12.3.5, the two-pass transposition** (correction). The source prints
  $\Gamma_1 = \mathcal{P}_{r,q} \otimes I_q$, which is correct only for $r = q$, and announces a
  factorization of $\mathcal{P}_{rq,q}$ before it writes $\mathcal{P}_{q,rq}$. See
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
* **Equation (12.4.17)** (correction). The source prints $\mathcal{S} \times_k (FG)$. The correct
  right side is $\mathcal{S} \times_k (GF)$. See `GolubVanLoan.Chapter12.equation_12_4_17`.
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
