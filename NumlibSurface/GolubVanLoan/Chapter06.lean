import NumlibSurface.GolubVanLoan.Chapter06.Section01
import NumlibSurface.GolubVanLoan.Chapter06.Section02
import NumlibSurface.GolubVanLoan.Chapter06.Section03
import NumlibSurface.GolubVanLoan.Chapter06.Section04
import NumlibSurface.GolubVanLoan.Chapter06.Section05

/-!
# Golub–Van Loan, Chapter 6: modified least squares problems and methods

Surface of [golub2013matrix] Chapter 6: weighting and regularization with the generalized SVD
(§6.1), constrained least squares (§6.2), total least squares (§6.3), subspace computations with the
SVD (§6.4), updating matrix factorizations (§6.5). One module per section,
`NumlibSurface/GolubVanLoan/Chapter06/SectionMM.lean`, namespace `GolubVanLoan.Chapter06`. This
module imports the sections.

## Conventions of the chapter's surface files

* **Shapes and scalars.** Real throughout, as the book: `Matrix (Fin m) (Fin n) ℝ`; the book's
  `m₁, n₁, m₂` are kept as `m₁ n₁ m₂` where they appear. Vectors in least-squares statements are
  `EuclideanSpace ℝ (Fin n)` and matrices act through `Matrix.toEuclideanLin`, the convention of the
  backbone's `LeastSquares`; programs take `Fin n → ℝ` and their specifications apply
  `WithLp.toLp 2`. "Orthogonal" is `Matrix.orthogonalGroup` (`= unitaryGroup` over `ℝ`). The book's
  parameter `λ` is written `μ` (`λ` is reserved in Lean).
* **Indices.** The book is 1-based with colon notation; the surface is 0-based on `Fin n`: the
  book's `σ_i`, `θ_i`, `α_i`, `β_i`, `x_i` are `σ (i − 1)`, …, `X.col (i − 1)`; `A(:, 1:r)` is a
  `Matrix.submatrix` along `Fin.castLE` (`Matrix.firstColumns`), `A(:, r+1:n)` along
  `fun j => ⟨r + j, _⟩`; block partitions are `Matrix.fromRows`/`fromCols`/`fromBlocks` over sum
  types, reindexed by `finSumFinEquiv` where the book speaks of one matrix.
* **The SVD** enters every statement as a *factorization* `Matrix.IsSVD A U σ V`
  (`Uᵀ A V = rectDiagonal σ`, `σ` antitone and nonnegative), never as "the" SVD, so that the output
  of any SVD routine can be used; the book's `u_i`, `v_i` are the columns of `U`, `V`.
* **The GSVD** is `Matrix.IsGSVD A B U₁ U₂ X α β` in Theorem 6.1.1's block order:
  `D_A = rectDiagonal α`, `D_B = shiftedRectDiagonal p β`, `p = max(r − m₂, 0)`. Displays of §6.2
  printed in the third edition's order are restated in this one, corrected.
* **Norms.** 2-norms of vectors are `EuclideanSpace` norms; the matrix 2-norm is the scoped
  `Matrix.Norms.L2Operator` norm, the Frobenius norm the scoped `Matrix.Norms.Frobenius` one.

## Algorithms

Every numbered algorithm — 6.2.1, 6.2.2, 6.3.1, 6.4.1, 6.4.2, 6.4.3 — is a program
`algorithm_6_M_K {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) …` in the book's operation order, every
arithmetic result through `rnd`, with a theorem `algorithm_6_M_K_spec` about
`Id.run (algorithm_6_M_K pure …)`, following the fourteen conventions of
`NumlibSurface/GolubVanLoan`.
The steps "Compute the SVD", "Find `z` so that … is minimized" and "Find `λ₊ > 0` such that …" are
monadic parameters (`svd`, `ls`, `root`), and the specifications assume their specifications: the
book's SVD algorithm is Chapter 8's, and the least-squares method and the root finder are
unspecified. "Compute the QR factorization" is Chapter 5's Householder QR with the explicit factor
from the forward accumulation of the reflector data it returned. Rotations and reflections are
applied by Chapter 5's shared helpers; concrete steps call Chapters 1, 3 and 5's programs. §6.5 has
no numbered algorithm: its prose procedures are programs named by content (`qrUpdateRankOne`,
`qrDeleteColumn`, `qrInsertColumn`, `qrInsertRow`, `qrDeleteFirstRow`, `choleskyUpdate`,
`choleskyDowndate`), each with a `_spec`. The chapter has no rounding-error analysis, so no `SetM`
theorem is stated.

## Backbone correspondence

| book | backbone |
|---|---|
| (6.1.1)–(6.1.10), §6.1.3 | `LinearAlgebra/Matrix/LeastSquares/Weighted` |
| (6.1.11)–(6.1.21), (6.1.26), (6.2.3)–(6.2.4) | `LeastSquares/Regularized` |
| Theorem 6.1.1 | `LinearAlgebra/Matrix/GSVD` |
| §6.2 | `LeastSquares/Constrained` |
| §6.3 | `LeastSquares/Total` |
| §6.4.1 | `LinearAlgebra/Matrix/Procrustes`, `Polar` |
| Theorem 6.4.1 | Mathlib's `Submodule.map_comap_eq` |
| (6.4.3), Theorem 6.4.2, `dist = sin θ_p` | `Analysis/InnerProductSpace/PrincipalAngles` |
| §6.5 | `Direct/Updating`, `LinearAlgebra/Matrix/PlaneRotation` |

## Not formalized

Operation counts; the Notes and References; numerical caveats (disparate weights, ill-conditioned
`B`, large `λ` in the weighting method, hyperbolic rotations with `|x₁| ≈ |x₂|`); heuristic claims
without a rigorous reading (van der Sluis's "approximately minimized", the choice of `λ` by
minimizing `C(λ)`, the threshold `1 − δ` for a unit singular value, the rank-revealing smallness in
(6.5.16) and the ULV updating procedure of §6.5.5); statements quoted without proof or without a
precise reading (Paige's stability, the Lagrange arguments of §6.2, the TLS variants
(6.3.7)–(6.3.9),
"there may not be a solution if `rank(B) < m₂`"); displays that only name data ((6.1.6), (6.1.13),
(6.1.24)–(6.1.25), (6.2.2), (6.2.5), (6.2.9), (6.4.4)–(6.4.5), (6.5.4), (6.5.5), (6.5.8), (6.5.9));
the displaced fragment of P6.3.1(b) printed after §6.3.4. Each section module lists its own.
-/
