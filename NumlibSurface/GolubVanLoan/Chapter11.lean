/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter11.Section01
import NumlibSurface.GolubVanLoan.Chapter11.Section02
import NumlibSurface.GolubVanLoan.Chapter11.Section03
import NumlibSurface.GolubVanLoan.Chapter11.Section04
import NumlibSurface.GolubVanLoan.Chapter11.Section05
import NumlibSurface.GolubVanLoan.Chapter11.Section06

/-!
# Golub and Van Loan, Chapter 11: Large sparse linear system problems

This module collects the formalization of Chapter 11 of [golub2013matrix], large sparse linear
systems: sparse direct methods with orderings and fill (§11.1), the classical iterations of Jacobi,
Gauss–Seidel, SOR and ADI (§11.2), the conjugate gradient method (§11.3), other Krylov methods such
as MINRES, GMRES, BiCG and QMR (§11.4), preconditioning (§11.5), and the multigrid framework
(§11.6). The matrices are real. The algorithms are exact programs whose specifications identify them
with the recurrences of the backbone; the chapter has no rounding-error analysis. The proofs use the
modules under `Numlib.LinearAlgebra.Sparse`, `Numlib.Stationary`, `Numlib.Krylov`,
`Numlib.Preconditioner` and `Numlib.Multigrid`. The module imports the section modules and declares
nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §11.1 | `Chapter11.Section01` | Direct methods |
| §11.2 | `Chapter11.Section02` | The classical iterations: Theorems 11.2.1–11.2.4 |
| §11.3 | `Chapter11.Section03` | The conjugate gradient method |
| §11.4 | `Chapter11.Section04` | Other Krylov methods: Algorithm 11.4.2 |
| §11.5 | `Chapter11.Section05` | Preconditioning |
| §11.6 | `Chapter11.Section06` | The multigrid framework: Theorem 11.6.2; Lemma 11.6.1 |
-/
