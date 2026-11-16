/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter03.Section02
import NumlibSurface.GolubVanLoan.Chapter03.Section03
import NumlibSurface.GolubVanLoan.Chapter03.Section04
import NumlibSurface.GolubVanLoan.Chapter03.Section05
import NumlibSurface.GolubVanLoan.Chapter03.Section06

/-!
# Golub and Van Loan, Chapter 3: General linear systems

This module collects the formalization of Chapter 3 of [golub2013matrix]: triangular systems (§3.1),
the LU factorization and its algorithms (§3.2), the rounding errors of Gaussian elimination (§3.3),
partial, complete and rook pivoting (§3.4), iterative improvement and condition estimation (§3.5),
and the precise statements of the parallel LU material (§3.6). The systems are real and square,
$A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$, and rectangular in §3.1.6, §3.2.10 and
§3.6. The algorithms that the source analyses carry a bridge to the relational rounding predicates
of the backbone and the backward error bounds of the source. The proofs use
`Numlib.FloatingPoint.Substitution`, `Numlib.FloatingPoint.LU` and `Numlib.LinearAlgebra.Matrix.LU`.
The module imports the section modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §3.1 | `Chapter03.Section01` | Triangular systems: Algorithms 3.1.1–3.1.4 |
| §3.2 | `Chapter03.Section02` | The LU factorization: Theorem 3.2.1; Algorithms 3.2.1–3.2.4 |
| §3.3 | `Chapter03.Section03` | Roundoff error in Gaussian elimination: Theorems 3.3.1, 3.3.2 |
| §3.4 | `Chapter03.Section04` | Pivoting: Algorithms 3.4.1–3.4.3; equations (3.4.1)–(3.4.13) |
| §3.5 | `Chapter03.Section05` | Improving and estimating accuracy: Algorithm 3.5.1 |
| §3.6 | `Chapter03.Section06` | Parallel LU: equations (3.6.2)–(3.6.5) |
-/
