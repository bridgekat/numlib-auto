/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter02.Section01
import NumlibSurface.GolubVanLoan.Chapter02.Section02
import NumlibSurface.GolubVanLoan.Chapter02.Section03
import NumlibSurface.GolubVanLoan.Chapter02.Section04
import NumlibSurface.GolubVanLoan.Chapter02.Section05
import NumlibSurface.GolubVanLoan.Chapter02.Section06
import NumlibSurface.GolubVanLoan.Chapter02.Section07

/-!
# Golub and Van Loan, Chapter 2: Matrix analysis

This module collects the formalization of Chapter 2 of [golub2013matrix], the matrix analysis that
the later chapters use: the review of linear algebra (§2.1), vector and matrix norms (§2.2–2.3), the
singular value decomposition (§2.4), the distance between subspaces and the CS decomposition (§2.5),
the sensitivity of square linear systems (§2.6), and the model of floating-point arithmetic with the
rounding errors of dot products and matrix products (§2.7). The chapter has no numbered algorithm;
its rounding results are stated about the runs of the algorithms of Chapter 1. Most of the proofs
are in the backbone: `Numlib.Analysis.Matrix.OperatorNorm`, `Numlib.Analysis.Normed.Lp.PiLp`,
`Numlib.Conditioning.LinearSystem`, `Numlib.LinearAlgebra.Matrix.SVD`,
`Numlib.LinearAlgebra.Matrix.CSDecomposition`, `Numlib.Analysis.InnerProductSpace.Projection.Gap`,
`Numlib.FloatingPoint.Model`, `Numlib.FloatingPoint.InnerProduct` and `Numlib.FloatingPoint.System`.
The module imports the section modules and declares nothing.

## Contents

| Source | Module | Subject |
|---|---|---|
| §2.1 | `Chapter02.Section01` | Basic ideas from linear algebra: Theorem 2.1.1 |
| §2.2 | `Chapter02.Section02` | Vector norms: equations (2.2.1)–(2.2.7) |
| §2.3 | `Chapter02.Section03` | Matrix norms: Theorems 2.3.1, 2.3.4; Lemma 2.3.3; Corollary 2.3.2 |
| §2.4 | `Chapter02.Section04` | The singular value decomposition |
| §2.5 | `Chapter02.Section05` | Subspace metrics: Theorems 2.5.1–2.5.3; equation (2.5.1) |
| §2.6 | `Chapter02.Section06` | The sensitivity of square systems |
| §2.7 | `Chapter02.Section07` | Finite precision matrix computations: Lemma 2.7.1 |
-/
