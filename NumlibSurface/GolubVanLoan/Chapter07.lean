/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter07.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section02
import NumlibSurface.GolubVanLoan.Chapter07.Section03
import NumlibSurface.GolubVanLoan.Chapter07.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section05
import NumlibSurface.GolubVanLoan.Chapter07.Section06
import NumlibSurface.GolubVanLoan.Chapter07.Section07
import NumlibSurface.GolubVanLoan.Chapter07.Section08
import NumlibSurface.GolubVanLoan.Chapter07.Section09

/-!
# Golub and Van Loan, Chapter 7: Unsymmetric eigenvalue problems

This module collects the formalization of Chapter 7 of [golub2013matrix], the unsymmetric eigenvalue
problem: the Schur, Jordan and block diagonal decompositions (§7.1), perturbation theory (§7.2), the
power method and orthogonal iteration (§7.3), the Hessenberg and real Schur forms (§7.4), the
practical QR algorithm (§7.5), invariant subspace computations (§7.6), the generalized eigenvalue
problem and the QZ algorithm (§7.7), Hamiltonian and product eigenvalue problems (§7.8), and
pseudospectra (§7.9). The theory of §7.1–7.3 and §7.9 is over $\mathbb{C}$; the algorithms of
§7.4–7.8 are over $\mathbb{R}$. The proofs use `Numlib.LinearAlgebra.Matrix.Schur`,
`Numlib.LinearAlgebra.Matrix.Jordan`, `Numlib.LinearAlgebra.Matrix.RealSchur`,
`Numlib.Eigen.Perturbation`, `Numlib.Eigen.PowerMethod`, `Numlib.Eigen.QRAlgorithm`,
`Numlib.Eigen.Pencil` and `Numlib.Eigen.Pseudospectrum`, among others. The module imports the
section modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §7.1 | `Chapter07.Section01` | Properties and decompositions |
| §7.2 | `Chapter07.Section02` | Perturbation Theory |
| §7.3 | `Chapter07.Section03` | Power Iterations: Theorem 7.3.1; Lemma 7.3.2 |
| §7.4 | `Chapter07.Section04` | The Hessenberg and Real Schur Forms |
| §7.5 | `Chapter07.Section05` | The practical QR algorithm |
| §7.6 | `Chapter07.Section06` | Invariant subspace computations: Algorithms 7.6.1–7.6.3 |
| §7.7 | `Chapter07.Section07` | The generalized eigenvalue problem |
| §7.8 | `Chapter07.Section08` | Hamiltonian and product eigenvalue problems |
| §7.9 | `Chapter07.Section09` | Pseudospectra |
-/
