/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter09.Section01
import NumlibSurface.GolubVanLoan.Chapter09.Section02
import NumlibSurface.GolubVanLoan.Chapter09.Section03
import NumlibSurface.GolubVanLoan.Chapter09.Section04

/-!
# Golub and Van Loan, Chapter 9: Functions of matrices

This module collects the formalization of Chapter 9 of [golub2013matrix], functions of matrices: the
definition of $f(A)$ through the Jordan form and the Schur–Parlett algorithm (§9.1), approximation
by Taylor series, Padé approximants and contour integrals (§9.2), the matrix exponential (§9.3), and
the matrix sign function, the principal square root, the principal logarithm and the polar
decomposition (§9.4). The function $f(A)$ is the primary functional calculus of the backbone, under
which the Jordan-form definition of the source is a theorem. The proofs use the modules under
`Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus` and `Numlib.Analysis.Matrix.Function`,
and `Numlib.Analysis.Calculus.HermiteInterpolation`. The module imports the section modules and
declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §9.1 | `Chapter09.Section01` | Eigenvalue methods |
| §9.2 | `Chapter09.Section02` | Approximation methods |
| §9.3 | `Chapter09.Section03` | The matrix exponential: Algorithm 9.3.1 |
| §9.4 | `Chapter09.Section04` | The sign, square root, and log of a matrix: Theorem 9.4.1 |
-/
