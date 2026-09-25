import NumlibSurface.GolubVanLoan.Chapter04.Section01
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter04.Section03
import NumlibSurface.GolubVanLoan.Chapter04.Section04
import NumlibSurface.GolubVanLoan.Chapter04.Section05
import NumlibSurface.GolubVanLoan.Chapter04.Section06
import NumlibSurface.GolubVanLoan.Chapter04.Section07
import NumlibSurface.GolubVanLoan.Chapter04.Section08

/-!
# Golub–Van Loan, Chapter 4: special linear systems

Surface of [golub2013matrix] Chapter 4: diagonal dominance and symmetry (§4.1), positive definite
systems (§4.2), banded systems (§4.3), symmetric indefinite systems (§4.4), block tridiagonal
systems (§4.5), Vandermonde systems (§4.6), Toeplitz systems (§4.7), circulant and discrete Poisson
systems (§4.8). One module per section, `NumlibSurface/GolubVanLoan/Chapter04/SectionMM.lean`,
namespace `GolubVanLoan.Chapter04`. This module imports the sections.

## Conventions of the chapter's surface files

* **Scalars and shapes.** Real square systems, `A : Matrix (Fin n) (Fin n) ℝ`, vectors `Fin n → ℝ`;
  §4.8.1–4.8.2 (the DFT and circulants) and Algorithm 4.8.1 are over `ℂ`. Indices are 0-based:
  the book's `A(i, j)` is `A ⟨i − 1, _⟩ ⟨j − 1, _⟩`, its `A(i:j, k:l)` a `submatrix` or a
  `toBlock`, the leading principal submatrix `A(1:k,1:k)` is
  `Matrix.leadingPrincipalSubmatrix`/`strictLeadingPrincipalSubmatrix`. §4.6 is already 0-based in
  the book (`x(0:n)`), and the surface keeps its indices.
* **Bands.** "Upper bandwidth `q`" is `Matrix.HasUpperBandwidth A q`, "lower bandwidth `p`" is
  `Matrix.HasLowerBandwidth A p`.
* **Norms.** `‖·‖₁` of a matrix is `Matrix.lpOpNorm 1`, `‖·‖₂` is `Matrix.lpOpNorm 2` (the scoped
  `Matrix.Norms.L2Operator` norm), `‖·‖_F` the scoped `Matrix.Norms.Frobenius` norm.
* **Factorization specifications.** `Matrix.IsLU`, `Matrix.IsLDM` (the book's `L D Lᵀ` is
  `IsLDM A L D L`), `Matrix.IsCholesky A H` with the *upper* factor `H = Gᵀ` (the book's lower `G`
  is `Matrix.cholesky A`), `Matrix.IsAasen`, `Matrix.IsBlockLDL`; a permutation `P` acts as
  `A.submatrix σ σ = P A Pᵀ`.
* **Positive definite** for an unsymmetric real matrix (§4.2) is the surface predicate
  `IsPositiveDefinite A` (`xᵀAx > 0` for `x ≠ 0`), bridged to `(Matrix.hermitianPart A).PosDef`;
  "symmetric positive definite" is Mathlib's `Matrix.PosDef`.
* **Structured matrices.** Toeplitz `Matrix.toeplitz r` and `Matrix.IsToeplitz`; symmetric Toeplitz
  with unit diagonal `T_k = Matrix.symmToeplitz k r`, `r 0 = 1`; the exchange matrix
  `ℰ_n = Matrix.exchange n`; the downshift `𝒟_n = Matrix.downshift n`; the book's
  `V(x₀, …, x_n)` is `(Matrix.vandermonde x)ᵀ`; the DFT matrix `F_n` is chapter 1's `fourierMatrix`
  (`= (Matrix.dft n)ᴴ`); block tridiagonal matrices are `Matrix.blockTridiagonal`; the
  second-difference matrices are `Matrix.symmTridiagonalToeplitz n (-1) 2` and
  `Matrix.secondDifferenceDN/NN/Periodic n`; the DST/DCT matrices `Matrix.dst1`, `Matrix.dst2`,
  `Matrix.dct1`, `Matrix.dct2`; the equilibrium matrix `[C B; Bᵀ 0]` is `Matrix.saddleMatrix C B 0`.
* **Algorithms** follow the numbered algorithm conventions of `NumlibSurface.GolubVanLoan`. The
  matrix–vector products inside a column update are running differences from the entry of `A`
  (`runningDiff`, §4.1), the operation order of the backbone relations `FloatingPoint.RoundsLDL` and
  `FloatingPoint.RoundsCholeskyDiv`. The exact meaning is `Id.run (algorithm_4_M_K pure …)`;
  `algorithm_4_M_K_spec` states it meets the backbone specification; where the book analyses
  rounding errors ((4.1.4) and §4.2.6) the bridge `algorithm_4_M_K_rounds` says every run in the
  relational model satisfies the backbone relation. The packed unit lower factor of a packed output
  `F` is written `1 + F.strictLower` (chapter 3's `packedL F`), a packed lower triangle
  `F − F.strictUpper`.

## Not formalized

Operation counts; the storage schemes of §4.2.10 and §4.3; §4.3.7; numerical examples and `2 × 2`
illustrations; quoted results without derivation (Wilkinson's completion criterion, the numerical
rank threshold, the stability of Bunch's method and of pivoted Aasen, the Bunch–Kaufman strategy,
Vavasis's method, Buneman's cyclic reduction, Cybenko's `≈` estimates, the `O(log n)` Newton count,
lookahead, banded inverses, SPIKE beyond (4.5.14), band `L D Lᵀ`, confluent Vandermonde systems);
displays that write out an algorithm step; displays that are definitions; Problems (except as
helpers).
-/
