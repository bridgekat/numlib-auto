/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter08.Section01
import NumlibSurface.GolubVanLoan.Chapter08.Section02
import NumlibSurface.GolubVanLoan.Chapter08.Section03
import NumlibSurface.GolubVanLoan.Chapter08.Section04
import NumlibSurface.GolubVanLoan.Chapter08.Section05
import NumlibSurface.GolubVanLoan.Chapter08.Section06
import NumlibSurface.GolubVanLoan.Chapter08.Section07

/-!
# Golub and Van Loan, Chapter 8: Symmetric eigenvalue problems

This module collects the formalization of Chapter 8 of [golub2013matrix], the symmetric eigenvalue
problem: the perturbation theory of symmetric matrices (§8.1), the power, inverse, Rayleigh quotient
and orthogonal iterations (§8.2), the symmetric QR algorithm (§8.3), bisection, Sturm sequences and
divide and conquer for tridiagonal matrices (§8.4), Jacobi methods (§8.5), the computation of the
SVD (§8.6), and symmetric-definite pencils, the generalized SVD and the quadratic eigenvalue problem
(§8.7). The matrices are real, except in §8.7.9. The proofs use `Numlib.Eigen.MinMax`,
`Numlib.Eigen.Perturbation`, `Numlib.Eigen.RayleighRitz`, `Numlib.Eigen.Sturm`,
`Numlib.Eigen.DivideConquer`, `Numlib.Eigen.Jacobi`, `Numlib.Eigen.SymmetricPencil` and
`Numlib.Analysis.InnerProductSpace.SingularValues`, among others. The module imports the section
modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §8.1 | `Chapter08.Section01` | Properties and decompositions of symmetric matrices |
| §8.2 | `Chapter08.Section02` | Power iterations: Theorems 8.2.1, 8.2.2 |
| §8.3 | `Chapter08.Section03` | The symmetric QR algorithm |
| §8.4 | `Chapter08.Section04` | More methods for tridiagonal problems |
| §8.5 | `Chapter08.Section05` | Jacobi methods: Algorithms 8.5.1–8.5.3; equations (8.5.1)–(8.5.3) |
| §8.6 | `Chapter08.Section06` | Computing the SVD |
| §8.7 | `Chapter08.Section07` | Generalized eigenvalue problems with symmetry |
-/
