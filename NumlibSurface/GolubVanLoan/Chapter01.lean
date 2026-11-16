/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter01.Section03
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter01.Section05
import NumlibSurface.GolubVanLoan.Chapter01.Section06

/-!
# Golub and Van Loan, Chapter 1: Matrix multiplication

This module collects the formalization of Chapter 1 of [golub2013matrix]: the dot product, the
saxpy, the gaxpy and the loop orderings of the matrix product (§1.1), structured matrices such as
band, triangular and symmetric matrices and permutations (§1.2), block matrices, Kronecker products,
Strassen's method and Hamiltonian and symplectic matrices (§1.3), the fast Fourier transform, the
sine and cosine transforms and the Haar wavelet transform (§1.4), and Cannon's identity for parallel
multiplication (§1.6). Each numbered algorithm is a program with a rounding hook, and its exact run
is the product or the transform of Mathlib or the backbone. The chapter also defines the rounded
entrywise vector and matrix operations that the later chapters call. The proofs use
`Numlib.FloatingPoint.Program`, `Numlib.LinearAlgebra.Matrix.Band`,
`Numlib.LinearAlgebra.Matrix.Block`, `Numlib.LinearAlgebra.Matrix.Permutation`,
`Numlib.LinearAlgebra.Matrix.Kronecker`, `Numlib.LinearAlgebra.Matrix.Hamiltonian`,
`Numlib.Analysis.Fourier.DFT` and `Numlib.Analysis.Fourier.SineCosineTransform`. The module imports
the section modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1.1 | `Chapter01.Section01` | Basic algorithms and notation: Algorithms 1.1.1–1.1.8 |
| §1.2 | `Chapter01.Section02` | Structure and efficiency: Algorithms 1.2.1–1.2.3 |
| §1.3 | `Chapter01.Section03` | Block matrices and algorithms: Theorem 1.3.1; Algorithm 1.3.1 |
| §1.4 | `Chapter01.Section04` | Fast matrix-vector products |
| §1.5 | `Chapter01.Section05` | Vectorization and locality |
| §1.6 | `Chapter01.Section06` | Parallel matrix multiplication: equation (1.6.16) |
-/
