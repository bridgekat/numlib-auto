/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section03
import NumlibSurface.GolubVanLoan.Chapter05.Section04
import NumlibSurface.GolubVanLoan.Chapter05.Section05
import NumlibSurface.GolubVanLoan.Chapter05.Section06

/-!
# Golub and Van Loan, Chapter 5: Orthogonalization and least squares

This module collects the formalization of Chapter 5 of [golub2013matrix]: Householder reflections
and Givens rotations (§5.1), the QR factorization by Householder, Givens and Gram–Schmidt methods
(§5.2), the full-rank least-squares problem (§5.3), bidiagonalization and rank-revealing and
complete orthogonal factorizations (§5.4), the rank-deficient least-squares problem (§5.5), and
square and underdetermined systems (§5.6). The chapter is real, except for the complex reflections,
rotations and QR factorization of §5.1.13 and §5.2.10. The chapter defines the Householder and
Givens programs that all later chapters call. The rounding claims of the source for Householder and
Givens transformations, and its rounding claims for runs of the algorithms of §5.3–5.4, are
formalized with the constants of the relational rounding model in place of $O(u)$. The proofs use
`Numlib.LinearAlgebra.Matrix.QR`, `Numlib.LinearAlgebra.Matrix.PlaneRotation`,
`Numlib.LinearAlgebra.Matrix.LeastSquares`, `Numlib.LinearAlgebra.Matrix.SVD`,
`Numlib.LinearAlgebra.Matrix.WY`, `Numlib.LinearAlgebra.Matrix.Bidiagonal`,
`Numlib.LinearAlgebra.Matrix.RankRevealing`, `Numlib.LinearAlgebra.Matrix.CompleteOrthogonal`,
`Numlib.Conditioning.LeastSquares`, `Numlib.FloatingPoint.Householder` and
`Numlib.FloatingPoint.Givens`. The module imports the section modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §5.1 | `Chapter05.Section01` | Householder and Givens transformations |
| §5.2 | `Chapter05.Section02` | The QR factorization |
| §5.3 | `Chapter05.Section03` | The full-rank least-squares problem |
| §5.4 | `Chapter05.Section04` | Other orthogonal factorizations |
| §5.5 | `Chapter05.Section05` | The rank-deficient least-squares problem |
| §5.6 | `Chapter05.Section06` | Square and underdetermined systems |
-/
