/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter04.Section01
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter04.Section03
import NumlibSurface.GolubVanLoan.Chapter04.Section04
import NumlibSurface.GolubVanLoan.Chapter04.Section05
import NumlibSurface.GolubVanLoan.Chapter04.Section06
import NumlibSurface.GolubVanLoan.Chapter04.Section07
import NumlibSurface.GolubVanLoan.Chapter04.Section08

/-!
# Golub and Van Loan, Chapter 4: Special linear systems

This module collects the formalization of Chapter 4 of [golub2013matrix], linear systems with
special structure: diagonally dominant and symmetric systems (§4.1), positive definite systems and
the Cholesky factorization (§4.2), banded systems (§4.3), symmetric indefinite systems with the
methods of Parlett–Reid, Aasen and Bunch–Parlett (§4.4), block tridiagonal systems and cyclic
reduction (§4.5), Vandermonde systems (§4.6), Toeplitz systems and the Durbin, Levinson and Trench
algorithms (§4.7), and circulant and discrete Poisson systems (§4.8). The systems are real, except
that the discrete Fourier transform and circulant matrices of §4.8 are complex. Where the source
analyses rounding errors, a bridge states that every run satisfies a relational predicate of the
backbone. The proofs use `Numlib.LinearAlgebra.Matrix.Cholesky`, `Numlib.LinearAlgebra.Matrix.Band`
and `Numlib.LinearAlgebra.Matrix.Toeplitz`, among others. The module imports the section modules and
declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §4.1 | `Chapter04.Section01` | Diagonal dominance and symmetry |
| §4.2 | `Chapter04.Section02` | Positive definite systems |
| §4.3 | `Chapter04.Section03` | Banded systems: Theorems 4.3.1–4.3.3; Algorithms 4.3.1–4.3.6 |
| §4.4 | `Chapter04.Section04` | Symmetric indefinite systems |
| §4.5 | `Chapter04.Section05` | Block tridiagonal systems |
| §4.6 | `Chapter04.Section06` | Vandermonde systems: Algorithms 4.6.1, 4.6.2 |
| §4.7 | `Chapter04.Section07` | Classical methods for Toeplitz systems: Algorithms 4.7.1–4.7.3 |
| §4.8 | `Chapter04.Section08` | Circulant and discrete Poisson systems |
-/
