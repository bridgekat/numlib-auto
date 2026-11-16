/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter10.Section01
import NumlibSurface.GolubVanLoan.Chapter10.Section02
import NumlibSurface.GolubVanLoan.Chapter10.Section03
import NumlibSurface.GolubVanLoan.Chapter10.Section04
import NumlibSurface.GolubVanLoan.Chapter10.Section05
import NumlibSurface.GolubVanLoan.Chapter10.Section06

/-!
# Golub and Van Loan, Chapter 10: Large sparse eigenvalue problems

This module collects the formalization of Chapter 10 of [golub2013matrix], large sparse eigenvalue
problems: the symmetric Lanczos process and the convergence of its Ritz values (§10.1), Lanczos and
Gauss quadrature for $u^T f(A) u$ (§10.2), practical Lanczos procedures with reorthogonalization and
block Lanczos (§10.3), Golub–Kahan bidiagonalization and a CUR sketch (§10.4), the Arnoldi process,
implicit and Krylov–Schur restarting and unsymmetric Lanczos (§10.5), and the Davidson and
Jacobi–Davidson methods (§10.6). The matrices are real. The proofs use `Numlib.Krylov.Lanczos`,
`Numlib.Krylov.Arnoldi`, `Numlib.Krylov.Bidiagonalization`, `Numlib.Krylov.Quadrature`,
`Numlib.Eigen.RayleighRitz`, `Numlib.Eigen.ImplicitRestart` and `Numlib.Eigen.JacobiDavidson`, among
others. The module imports the section modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §10.1 | `Chapter10.Section01` | The symmetric Lanczos process |
| §10.2 | `Chapter10.Section02` | Lanczos, quadrature, and approximation |
| §10.3 | `Chapter10.Section03` | Practical Lanczos procedures: Theorem 10.3.2; Lemma 10.3.1 |
| §10.4 | `Chapter10.Section04` | Large sparse SVD frameworks: Algorithms 10.4.1, 10.4.2 |
| §10.5 | `Chapter10.Section05` | Krylov methods for unsymmetric problems |
| §10.6 | `Chapter10.Section06` | Jacobi–Davidson and related methods |
-/
