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

The surface library for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition,
Johns Hopkins University Press, 2013 [golub2013matrix]: one chapter module per chapter and one
module per section, `NumlibSurface/GolubVanLoan/ChapterNN/SectionMM.lean`, in the namespace
`GolubVanLoan.ChapterNN`. Each module states the book's results in the book's own terms — real
matrices `Matrix (Fin m) (Fin n) ℝ`, every algorithm written as the book writes it — and proves them
by specializing the general backbone under `Numlib/`. This module imports the chapter modules and
adds nothing of its own.

Plan and per-result book alignment: the module plans under
`plans/NumlibSurface/GolubVanLoan/`, one per section.

## Scope

* Every Theorem, Lemma and Corollary is formalized.
* **Every numbered Algorithm is formalized**, loop-order, blocked and recursive variants included:
  a definition `algorithm_N_M_K`, written once as a monadic program in which every arithmetic
  result passes through a rounding hook `rnd : ℝ → M ℝ`, and a theorem `algorithm_N_M_K_spec`
  stating its exact-arithmetic correctness (`M := Id`, `rnd := pure`) against a backbone
  specification. Where the book analyses the algorithm's rounding errors, that is a theorem about
  its runs in the relational model (`M := SetM`, `rnd := fp.round`), proved through the backbone's
  relational predicates. The infrastructure is `Numlib/FloatingPoint/Program`.
* Numbered displays `(N.M.K)` are formalized when they assert a precise proposition.
* Problems are not formalized; a Problem the text cites for a proof step becomes a helper.
* Operation counts, §1.5–1.6 (except Cannon's identity (1.6.16)), §3.6's parallel and architecture
  material, the storage and BLAS discussion, numerical examples and the Notes and References are
  not formalized; each chapter module says so once.

## Naming

* Theorems, Lemmas, Corollaries and Algorithms are `theorem_N_M_K`, `lemma_N_M_K`,
  `corollary_N_M_K`, `algorithm_N_M_K` (with the suffixes of convention 12 below); a propositional
  numbered display is `equation_N_M_K`, always a theorem.
* A definition is named by its content, never `equation_N_M_K` — pure notation
  (`fourierMatrix`, `modelEigenvalues`) as much as a prose definition (`growthFactor`) — and its
  docstring keeps the display number.
* An algorithm-shaped numbered display (a loop the book writes as a display rather than as a
  numbered Algorithm) is a content-named program (`gaussSeidelSweep`, `blockLanczos`), and its
  exact-semantics theorem is `equation_N_M_K`.
* Later chapters use earlier chapters' restatements rather than reaching past them to the backbone
  or Mathlib.

The book is real, `Matrix (Fin m) (Fin n) ℝ`, 1-based in its colon notation; the surface is 0-based
on `Fin n`, and each chapter states the translation. Complex statements (Chapter 7's
decompositions, §7.9, parts of Chapter 9) are over `ℂ`.

**Singular values.** The book's sorted `σ_k` is `A.sortedSingularValues (k - 1)` (Mathlib's
`LinearMap.singularValues` of `toEuclideanLin A`); `σ_min(A)` and `σ_max(A)` of an `m × n` matrix
with `n ≤ m` may be read as `⨅ i, A.colSingularValues i` / `⨆ i, A.colSingularValues i` over the
backbone's column-indexed `Matrix.colSingularValues`.

**Shared helper programs** (convention 13; all in `GolubVanLoan.Chapter05`, §5.1, each with its own
`_spec` and, where the book analyses it, `_rounds`/`_rounding`; every later chapter calls them and
defines no variant):

* `houseOn rnd (o : List (Fin m)) (x : Fin m → ℝ) : M ((Fin m → ℝ) × ℝ)` — Algorithm 5.1.1 on the
  entries of `x` listed by `o` (pivot `o.head`, the book's `x(1)`; the tail sum by Algorithm 1.1.1
  over `o.tail`), returning `(v, β)` with `v` zero off `o` and `1` at the pivot;
  `algorithm_5_1_1 rnd x := houseOn rnd (List.finRange (k+1)) x`.
* `householderApplyLeft rnd v β rows cols A` (`A(rows, cols) ← (I − βvvᵀ) A(rows, cols)`, the book's
  `A − (βv)(vᵀA)`) and `householderApplyRight rnd v β rows cols A`
  (`A(rows, cols) ← A(rows, cols)(I − βvvᵀ)`, `A − (Av)(βv)ᵀ`), in place on the full matrix.
* `givensRotation i k c s := Matrix.planeRotation i k c (-s)` (the book's matrix `G(i, k, θ)`,
  (5.1.7));
  `algorithm_5_1_3` is the book's `givens`, computing `(c, s)`; `givensApplyLeft rnd i k c s cols A`
  (`A([i,k], cols) ← G(i,k,θ)ᵀ A([i,k], cols)`) and `givensApplyRight rnd i k c s rows A`
  (`A(rows, [i,k]) ← A(rows, [i,k]) G(i,k,θ)`).
* Householder data `List ((Fin m → ℝ) × ℝ)` (convention 13), `householderProduct data = Q₁ ⋯ Q_r`,
  and `forwardAccumulation rnd data` / `backwardAccumulation rnd data` (§5.1.6), each
  `= householderProduct data` at `Id`.

## Algorithm conventions

The same list, with the same numbers, heads the module documentation of
`Numlib/FloatingPoint/Program`.

1. **What is rounded.** *Exact* (not passed through `rnd`): unary negation, `|·|`, `sign` and
   copysign, copying, comparisons (a comparison stores nothing and acts on the values the program
   holds). *Rounded* (exactly one `rnd` after each): the result of every `+`, `−`, `×`, `/` and
   `√` (`√` is `Real.sqrt` followed by one `rnd`), **including arithmetic whose only use is a
   test** — `fl(tol · fl(|h_ii| + |h_{i-1,i-1}|))`, `δ ← fl(tol · ‖A‖_F)`, the `fl(1 − fl(α²))` of a
   positivity check. IEEE negation, `abs` and copysign are exact, and the relational model does not
   know `Rounds x x`, so rounding them would only add spurious error.
2. A division by a unit diagonal inside a factorization is not performed.
3. Loops are `List.foldlM` over `List.finRange n` or an explicit index list, never `for … in
   [a:b]`. A `while` loop is `List.foldlM` over `List.range fuel` with a `done : Bool` field in the
   state: once `done`, a step is the identity; the spec theorem states what holds after
   `min fuel stop` passes (`stop` the book's exit index). The fuel parameter is named `fuel : ℕ` and
   is the **last** explicit argument. Structural or well-founded recursion is reserved for
   genuinely recursive algorithms (Strassen, the FFT, recursive block LU/Cholesky/QR, `LUdisp`).
4. A program that branches on a real test is a `noncomputable def` (through `Real.decidableEq`,
   `Real.decidableLT`).
5. A step the book delegates to an algorithm of a *later* chapter ("compute the SVD", "find
   `λ₊`") is a monadic function parameter, and the spec theorem assumes its specification; a step
   delegated to an *earlier* chapter calls that chapter's program.
6. `fp.IsIdempotent` is assumed **only when the stated constant needs it**: a program whose
   accumulation starts from `0` and whose bound is the book's `γ_n` through a relation that starts
   from the unrounded first term (`RoundsDot`, `RoundsSum`) needs it (the `0 + p` paragraph below);
   a relation that itself absorbs the `0 + p` rounding (`RoundsForwardSubstDot`) needs nothing.
7. The monad variable is `M` (`{M : Type → Type} [Monad M]`), never `m`, which is the book's row
   count.
8. Breakdown is not checked in the program (`x / 0 = 0`); the spec theorem carries the
   hypotheses (nonzero pivots, nonsingular leading submatrices, …). Overwrites are state updates
   (`Function.update`, `Matrix.updateRow`); a multi-output state is a structure or a tuple.
9. **Hypotheses of a rounding theorem are about the inputs and the values the program returns**,
   never about intermediate values a run overwrites (a computed pivot `t_j` that is then replaced
   by `√t_j`, a packed factor the program does not return). A composite (factor, then solve) is
   stated nested, one program per quantifier:
   `∀ F ∈ (alg₁ fp.round A).run, hyp F → ∀ x ∈ (alg₂ fp.round F b).run, concl` (the shape of
   `GolubVanLoan.Chapter03.theorem_3_3_2`).
10. **Submatrices are index lists.** A block `A(j:m, k:n)` of the book is the full matrix together
    with the filtered index lists of its rows and columns (`rows : List (Fin m)`,
    `cols : List (Fin n)`), never a copy typed by a loop-dependent `Fin (m - j)`; a subvector
    `x(j:m)` is the full vector with its list of active indices. Helpers operate in place on the
    full matrix over such lists (`GolubVanLoan.Chapter05.houseOn rnd o x`,
    `householderApplyLeft/Right`, `givensApplyLeft/Right`), and a vector-level book algorithm is
    its helper at the full list (`algorithm_5_1_1 rnd x = houseOn rnd (List.finRange (k+1)) x` by
    `rfl`). The backbone relations read such a block through the subtype `{i // i ∈ rows}` or a
    pivot `i : ι` of the full index type.
11. **Exact specs are read off bridges.** When a bridge "every run satisfies the backbone relation
    `R`" exists, the exact spec `_spec` is its instance at `RoundingModel.exact` (`round_exact`
    and `R`'s exact characterization, e.g. `roundsLU_exact_iff`, `mem_run_dotAccum_exact_iff`),
    not a second proof at `Id`.
12. **Node suffixes.** `algorithm_N_M_K` is the program; `_spec` its exact semantics; `_rounds`
    says every run satisfies a backbone relation (`∀ out ∈ run, FloatingPoint.RoundsX …`, the
    bridge); `_mem_run` characterizes the run set (an `↔`) when no backbone relation exists;
    `_rounding` is the book's error bound for every run. A node proving the bound through a
    bridge depends on the `_rounds` node.
13. **One helper family, one reflector-data type.** Updates shared by several algorithms are
    defined once (for Golub–Van Loan: chapter 5), in symmetric pairs `…Left`/`…Right` on index
    lists; Householder data are `List ((Fin m → ℝ) × ℝ)` — pairs `(v, β)` in order of
    application, `v` full length and zero off its active rows — carrying the `β` the program
    returned. A reflector is **never** rebuilt as `β = 2/(vᵀv)` from a stored `v` (when `house`
    returns `β = 0`, the rebuilt `I − 2e₁e₁ᵀ` is not the identity it applied).
14. **Symmetric pairs are separate nodes** (`…Left` and `…Right`, `…_col` and `…_row`, forward and
    backward accumulation), each with its own `_spec`; consumers depend on the half they use.

## The outline

| § | module | subject |
|---|---|---|
| **1** | `Chapter01` | *Matrix multiplication* |
| 1.1 | `Chapter01.Section01` | Basic algorithms and notation |
| 1.2 | `Chapter01.Section02` | Structure and efficiency |
| 1.3 | `Chapter01.Section03` | Block matrices and algorithms |
| 1.4 | `Chapter01.Section04` | Fast matrix-vector products |
| 1.5 | `Chapter01.Section05` | Vectorization and locality |
| 1.6 | `Chapter01.Section06` | Parallel matrix multiplication (Cannon's identity) |
| **2** | `Chapter02` | *Matrix Analysis* |
| 2.1 | `Chapter02.Section01` | Basic ideas from linear algebra |
| 2.2 | `Chapter02.Section02` | Vector norms |
| 2.3 | `Chapter02.Section03` | Matrix norms |
| 2.4 | `Chapter02.Section04` | The singular value decomposition |
| 2.5 | `Chapter02.Section05` | Subspace metrics |
| 2.6 | `Chapter02.Section06` | The sensitivity of square systems |
| 2.7 | `Chapter02.Section07` | Finite precision matrix computations |
| **3** | `Chapter03` | *General Linear Systems* |
| 3.1 | `Chapter03.Section01` | Triangular systems |
| 3.2 | `Chapter03.Section02` | The LU factorization |
| 3.3 | `Chapter03.Section03` | Roundoff error in Gaussian elimination |
| 3.4 | `Chapter03.Section04` | Pivoting |
| 3.5 | `Chapter03.Section05` | Improving and estimating accuracy |
| 3.6 | `Chapter03.Section06` | Parallel LU |
| **4** | `Chapter04` | *Special linear systems* |
| 4.1 | `Chapter04.Section01` | Diagonal dominance and symmetry |
| 4.2 | `Chapter04.Section02` | Positive definite systems |
| 4.3 | `Chapter04.Section03` | Banded systems |
| 4.4 | `Chapter04.Section04` | Symmetric indefinite systems |
| 4.5 | `Chapter04.Section05` | Block tridiagonal systems |
| 4.6 | `Chapter04.Section06` | Vandermonde systems |
| 4.7 | `Chapter04.Section07` | Classical methods for Toeplitz systems |
| 4.8 | `Chapter04.Section08` | Circulant and discrete Poisson systems |
| **5** | `Chapter05` | *Orthogonalization and Least Squares* |
| 5.1 | `Chapter05.Section01` | Householder and Givens transformations |
| 5.2 | `Chapter05.Section02` | The QR factorization |
| 5.3 | `Chapter05.Section03` | The full-rank least-squares problem |
| 5.4 | `Chapter05.Section04` | Other orthogonal factorizations |
| 5.5 | `Chapter05.Section05` | The rank-deficient least-squares problem |
| 5.6 | `Chapter05.Section06` | Square and underdetermined systems |
| **6** | `Chapter06` | *Modified least squares problems and methods* |
| 6.1 | `Chapter06.Section01` | Weighting and regularization |
| 6.2 | `Chapter06.Section02` | Constrained least squares |
| 6.3 | `Chapter06.Section03` | Total least squares |
| 6.4 | `Chapter06.Section04` | Subspace computations with the SVD |
| 6.5 | `Chapter06.Section05` | Updating matrix factorizations |
| **7** | `Chapter07` | *Unsymmetric eigenvalue problems* |
| 7.1 | `Chapter07.Section01` | Properties and decompositions |
| 7.2 | `Chapter07.Section02` | Perturbation theory |
| 7.3 | `Chapter07.Section03` | Power iterations |
| 7.4 | `Chapter07.Section04` | The Hessenberg and real Schur forms |
| 7.5 | `Chapter07.Section05` | The practical QR algorithm |
| 7.6 | `Chapter07.Section06` | Invariant subspace computations |
| 7.7 | `Chapter07.Section07` | The generalized eigenvalue problem |
| 7.8 | `Chapter07.Section08` | Hamiltonian and product eigenvalue problems |
| 7.9 | `Chapter07.Section09` | Pseudospectra |
| **8** | `Chapter08` | *Symmetric Eigenvalue Problems* |
| 8.1 | `Chapter08.Section01` | Properties and decompositions of symmetric matrices |
| 8.2 | `Chapter08.Section02` | Power iterations |
| 8.3 | `Chapter08.Section03` | The symmetric QR algorithm |
| 8.4 | `Chapter08.Section04` | More methods for tridiagonal problems |
| 8.5 | `Chapter08.Section05` | Jacobi methods |
| 8.6 | `Chapter08.Section06` | Computing the SVD |
| 8.7 | `Chapter08.Section07` | Generalized eigenvalue problems with symmetry |
| **9** | `Chapter09` | *Functions of matrices* |
| 9.1 | `Chapter09.Section01` | Eigenvalue methods |
| 9.2 | `Chapter09.Section02` | Approximation methods |
| 9.3 | `Chapter09.Section03` | The matrix exponential |
| 9.4 | `Chapter09.Section04` | The sign, square root, and log of a matrix |
| **10** | `Chapter10` | *Large sparse eigenvalue problems* |
| 10.1 | `Chapter10.Section01` | The symmetric Lanczos process |
| 10.2 | `Chapter10.Section02` | Lanczos, quadrature, and approximation |
| 10.3 | `Chapter10.Section03` | Practical Lanczos procedures |
| 10.4 | `Chapter10.Section04` | Large sparse SVD frameworks |
| 10.5 | `Chapter10.Section05` | Krylov methods for unsymmetric problems |
| 10.6 | `Chapter10.Section06` | Jacobi–Davidson and related methods |
| **11** | `Chapter11` | *Large Sparse Linear System Problems* |
| 11.1 | `Chapter11.Section01` | Direct methods |
| 11.2 | `Chapter11.Section02` | The classical iterations |
| 11.3 | `Chapter11.Section03` | The conjugate gradient method |
| 11.4 | `Chapter11.Section04` | Other Krylov methods |
| 11.5 | `Chapter11.Section05` | Preconditioning |
| 11.6 | `Chapter11.Section06` | The multigrid framework |
| **12** | `Chapter12` | *Special topics* |
| 12.1 | `Chapter12.Section01` | Linear systems with displacement structure |
| 12.2 | `Chapter12.Section02` | Structured-rank problems |
| 12.3 | `Chapter12.Section03` | Kronecker product computations |
| 12.4 | `Chapter12.Section04` | Tensor unfoldings and contractions |
| 12.5 | `Chapter12.Section05` | Tensor decompositions and iterations |
-/
