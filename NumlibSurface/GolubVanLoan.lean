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

Plan and per-result book alignment: the groups under `plans/NumlibSurface/GolubVanLoan/`, one file
per section.

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
with `n ≤ m` may be read as `⨅ i, A.singularValues i` / `⨆ i, A.singularValues i` over the
backbone's column-indexed `Matrix.singularValues`.

**Shared helper programs** (convention 13; all in `GolubVanLoan.Chapter05`, §5.1, each with its own
specification): `houseOn` (Algorithm 5.1.1 on the entries of a vector listed by an index list),
`householderApplyLeft`/`householderApplyRight`, `givensRotation` (the book's `G(i, k, θ)`),
`algorithm_5_1_3` (the book's `givens`), `givensApplyLeft`/`givensApplyRight`, the Householder data
`List ((Fin m → ℝ) × ℝ)` with `householderProduct`, and `forwardAccumulation` /
`backwardAccumulation` (§5.1.6). Every later chapter calls them and defines no variant.

## Algorithm conventions

The same list, with the same numbers, heads the module documentation of
`Numlib/FloatingPoint/Program`.

1. **What is rounded.** *Exact* (not passed through `rnd`): unary negation, `|·|`, `sign` and
   copysign, copying, comparisons. *Rounded* (exactly one `rnd` after each): the result of every
   `+`, `−`, `×`, `/` and `√` (`√` is `Real.sqrt` followed by one `rnd`), including arithmetic
   whose only use is a test.
2. A division by a unit diagonal inside a factorization is not performed.
3. Loops are `List.foldlM` over `List.finRange n` or an explicit index list. A `while` loop is
   `List.foldlM` over `List.range fuel` with a `done : Bool` field in the state; the fuel parameter
   `fuel : ℕ` is the last explicit argument. Structural or well-founded recursion is reserved for
   genuinely recursive algorithms (Strassen, the FFT, recursive block factorizations).
4. A program that branches on a real test is a `noncomputable def`.
5. A step the book delegates to an algorithm of a *later* chapter is a monadic function parameter,
   and the specification assumes its specification; a step delegated to an *earlier* chapter calls
   that chapter's program.
6. `fp.IsIdempotent` is assumed only when the stated constant needs it (an accumulation from `0`
   bounded by the book's `γ_n` through a relation that starts from the unrounded first term).
7. The monad variable is `M`, never `m`, which is the book's row count.
8. Breakdown is not checked in the program (`x / 0 = 0`); the specification carries the
   hypotheses. Overwrites are state updates (`Function.update`, `Matrix.updateRow`).
9. Hypotheses of a rounding theorem are about the inputs and the values the program returns. A
   composite (factor, then solve) is stated nested, one program per quantifier.
10. **Submatrices are index lists**: a block `A(j:m, k:n)` is the full matrix with the filtered
    index lists of its rows and columns; helpers operate in place on the full matrix.
11. **Exact specifications are read off bridges**: when a bridge "every run satisfies the backbone
    relation `R`" exists, the exact specification is its instance at `RoundingModel.exact`.
12. **Suffixes**: `algorithm_N_M_K` is the program; `_spec` its exact semantics; `_rounds` says
    every run satisfies a backbone relation (the bridge); `_mem_run` characterizes the run set when
    no backbone relation exists; `_rounding` is the book's error bound for every run.
13. **One helper family, one reflector-data type** (chapter 5, above); a reflector is never
    rebuilt as `β = 2/(vᵀv)` from a stored `v`.
14. **Symmetric pairs are separate declarations** (`…Left` and `…Right`, forward and backward
    accumulation), each with its own specification.

## The outline

| § | module | subject |
|---|---|---|
| **1** | `Chapter01` | *Matrix Multiplication* |
| 1.1 | `Chapter01.Section01` | Basic algorithms and notation |
| 1.2 | `Chapter01.Section02` | Structure and efficiency |
| 1.3 | `Chapter01.Section03` | Block matrices and algorithms |
| 1.4 | `Chapter01.Section04` | Fast matrix-vector products |
| 1.5 | `Chapter01.Section05` | Vectorization and locality (no formal content) |
| 1.6 | `Chapter01.Section06` | Parallel matrix multiplication (Cannon's identity) |
-/
