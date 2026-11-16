/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter12.Section01
import NumlibSurface.GolubVanLoan.Chapter12.Section02
import NumlibSurface.GolubVanLoan.Chapter12.Section03
import NumlibSurface.GolubVanLoan.Chapter12.Section04
import NumlibSurface.GolubVanLoan.Chapter12.Section05

/-!
# Golub and Van Loan, Chapter 12: Special topics

This module collects the formalization of Chapter 12 of [golub2013matrix]: linear systems with
displacement structure (§12.1), semiseparable and quasiseparable matrices (§12.2), Kronecker product
computations and the nearest Kronecker product (§12.3), tensor unfoldings and contractions (§12.4),
and tensor decompositions such as the higher-order SVD, the Tucker and CP decompositions and tensor
trains (§12.5). The proofs use `Numlib.LinearAlgebra.Matrix.Displacement`,
`Numlib.LinearAlgebra.Matrix.Semiseparable`, `Numlib.LinearAlgebra.Matrix.KroneckerApprox`,
`Numlib.LinearAlgebra.Matrix.Kronecker` and the modules under `Numlib.LinearAlgebra.Tensor`. The
module imports the section modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §12.1 | `Chapter12.Section01` | Linear systems with displacement structure |
| §12.2 | `Chapter12.Section02` | Structured-rank problems: Algorithms 12.2.1, 12.2.2 |
| §12.3 | `Chapter12.Section03` | Kronecker product computations |
| §12.4 | `Chapter12.Section04` | Tensor unfoldings and contractions: Theorem 12.4.1 |
| §12.5 | `Chapter12.Section05` | Tensor decompositions and iterations: Theorem 12.5.1 |
-/
