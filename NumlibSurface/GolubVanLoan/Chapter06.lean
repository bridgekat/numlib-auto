/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter06.Section01
import NumlibSurface.GolubVanLoan.Chapter06.Section02
import NumlibSurface.GolubVanLoan.Chapter06.Section03
import NumlibSurface.GolubVanLoan.Chapter06.Section04
import NumlibSurface.GolubVanLoan.Chapter06.Section05

/-!
# Golub and Van Loan, Chapter 6: Modified least squares problems and methods

This module collects the formalization of Chapter 6 of [golub2013matrix]: weighted and regularized
least squares and the generalized SVD (§6.1), least squares with quadratic and equality constraints
(§6.2), total least squares (§6.3), subspace computations with the SVD, such as the orthogonal
Procrustes problem and principal angles (§6.4), and the updating of QR and Cholesky factorizations
(§6.5). The chapter is real. Its algorithms are exact programs; the chapter has no rounding-error
analysis. The proofs use `Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted`,
`Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized`, `Numlib.LinearAlgebra.Matrix.GSVD`,
`Numlib.LinearAlgebra.Matrix.LeastSquares.Constrained`,
`Numlib.LinearAlgebra.Matrix.LeastSquares.Total`, `Numlib.LinearAlgebra.Matrix.Procrustes`,
`Numlib.Analysis.InnerProductSpace.PrincipalAngles` and `Numlib.Direct.Updating`. The module imports
the section modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §6.1 | `Chapter06.Section01` | Weighting and regularization: Theorem 6.1.1 |
| §6.2 | `Chapter06.Section02` | Constrained least squares: Algorithms 6.2.1, 6.2.2 |
| §6.3 | `Chapter06.Section03` | Total least squares: Theorem 6.3.1; Algorithm 6.3.1 |
| §6.4 | `Chapter06.Section04` | Subspace computations with the SVD |
| §6.5 | `Chapter06.Section05` | Updating matrix factorizations: Theorem 6.5.1 |
-/
