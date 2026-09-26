import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section03
import NumlibSurface.GolubVanLoan.Chapter05.Section04
import NumlibSurface.GolubVanLoan.Chapter05.Section05
import NumlibSurface.GolubVanLoan.Chapter05.Section06

/-!
# Golub–Van Loan, Chapter 5: Orthogonalization and Least Squares

Surface of [golub2013matrix] Chapter 5: §5.1 Householder and Givens transformations, §5.2 the QR
factorization, §5.3 the full-rank least-squares problem, §5.4 other orthogonal factorizations,
§5.5 the rank-deficient least-squares problem, §5.6 square and underdetermined systems. One
module per section, `NumlibSurface/GolubVanLoan/Chapter05/SectionMM.lean`, namespace
`GolubVanLoan.Chapter05`. Real throughout (`Matrix (Fin m) (Fin n) ℝ`), with the complex reflector,
rotation and QR of §5.1.13 and §5.2.10 over `ℂ`.

## Conventions of the chapter's surface files

* Indices are 0-based on `Fin n`: the book's `x(1)` is `x 0`, `e₁` is `Pi.single 0 1`. A block
  `A(j:m, k:n)` is the full matrix with the index lists of its rows and columns (`indexFrom m j`),
  never a `Fin (m - j)`-typed copy (convention 10 of `NumlibSurface/GolubVanLoan`): a Householder
  step on `A(j:m, j)` is `houseOn rnd (indexFrom m j) (A.col j)` followed by
  `householderApplyLeft … (indexFrom m j) (indexFrom n j) A`, in place.
* Vectors of algorithms are `Fin m → ℝ`; least-squares statements are on
  `EuclideanSpace ℝ (Fin m)` (the backbone's `Matrix.IsLeastSquaresSolution`,
  `Matrix.IsMinNormLeastSquaresSolution`, `Matrix.toEuclideanLin`), converted with `WithLp.toLp 2`.
* `P = I - β v vᵀ` is `1 - β • vecMulVec v v`; the book's Householder matrix `I - 2vvᵀ/vᵀv` is
  `householderMatrix v`, the backbone's `Matrix.reflector v`.
* The book's Givens rotation `G(i, k, θ)` (`c` at `(i,i)`, `(k,k)`, `s` at `(i,k)`, `-s` at `(k,i)`)
  is `givensRotation i k c s = Matrix.planeRotation i k c (-s)`; the rounding relations of
  `Numlib/FloatingPoint/Givens` are stated in the book's sign convention, signs inside the rounded
  expressions, so that runs reach them literally.
* Orthogonal is `Matrix.orthogonalGroup (Fin m) ℝ`; the full QR factorization is `Matrix.IsQR`, the
  thin one `Matrix.IsThinQR`, bidiagonalization `Matrix.IsBidiagonalization`. Overwritten arrays
  are read back through `upperPart` and the factored form
  `factoredQ β A' = householderProduct (storedReflectors A' β)`, with the `β` the program returned
  (convention 13).
* Norms: the 2-norm of a matrix through the scoped `Matrix.Norms.L2Operator` or `Matrix.lpOpNorm 2`,
  the Frobenius norm through `Matrix.Norms.Frobenius`, each in its own section. `σ_min` of a
  full-column-rank matrix is `⨅ i, A.singularValues i`; the book's sorted `σ_k` is
  `A.sortedSingularValues (k - 1)`; an SVD is `Matrix.IsSVD A U σ V`.
* Algorithms follow the numbered conventions of `NumlibSurface/GolubVanLoan`. This chapter owns the
  **shared helper family** of convention 13 (§5.1: `houseOn`, `householderApplyLeft`/`Right`,
  `givensRotation`, `givensApplyLeft`/`Right`, `householderProduct`,
  `forwardAccumulation`/`backwardAccumulation`, reflector data `List ((Fin m → ℝ) × ℝ)`), which
  every later chapter calls. Node suffixes per convention 12: `_spec` (exact, read off the bridge at
  `RoundingModel.exact` where one exists, convention 11), `_rounds` (every run satisfies the
  backbone relation: `RoundsHouseholderVectorParlett`, `RoundsHouseholderApplyScaled`,
  `RoundsGivensPair`, `RoundsGivensRowUpdate`/`ColUpdate`), `_rounding` (the book's bound).
  Wherever a program accumulates a dot product from `c = 0` (Algorithm 1.1.1,
  `FloatingPoint.dotAccum`), the bridge carries `fp.IsIdempotent` (convention 6).

## Design

The chapter's backbone is `Numlib/LinearAlgebra/Matrix/{QR, PlaneRotation, LeastSquares, SVD, WY,
Bidiagonal}` and `Numlib/FloatingPoint/{Householder, Givens}`; rank-revealing and complete
orthogonal decompositions (`RankRevealing`, `CompleteOrthogonal`) and the conditioning of least
squares (`Conditioning/LeastSquares`) are the remaining backbone of §5.3–§5.6.

## Not formalized, by class

Operation counts, flop tables (Figures 5.5.1, 5.6.1), level-2/level-3 fractions, storage and the
BLAS discussion; the numerical examples (§5.3.1 sensitivity, `fl(AᵀA)` singular, `Kah₃₀₀(.99)`'s
`σ₃₀₀`, the unstable subset in §5.5.7); heuristic statements with no rigorous content beyond the
theorems they paraphrase ((5.3.18), (5.3.19), (5.4.2), (5.4.3), "column pivoting tends to produce a
well-conditioned `R₁₁`", "small trailing `R`-submatrices almost always emerge", Björck's digit gain
of §5.3.8); rounding claims quoted without derivation whose rigorous proofs are research-length
(MGS's `‖Q̂ᵀQ̂ - I‖ ≈ u κ₂(A)` and `‖A - Q̂R̂‖ ≈ u‖A‖`, §5.2.9; Stewart's `O(ε κ₂)` perturbation of
the QR factors, §5.2.1; the backward stability (5.4.4) of the Golub–Kahan–Reinsch SVD, a Chapter 8
algorithm, used only as a hypothesis; "the roundoff properties of Algorithm 5.2.2 are essentially
the same"); the garbled second bound of §5.5.4; the prose of §5.1.1 and §5.6.1; Problems and Notes
and References. The rounding claims the book quotes for Householder and Givens transformations
(§5.1.5, §5.1.10, §5.1.12, (5.1.11)) are formalized rigorously, with the constants of the
relational `γ` calculus in place of the book's `O(u)`.
-/
