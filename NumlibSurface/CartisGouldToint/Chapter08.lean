/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter08.Section01
import NumlibSurface.CartisGouldToint.Chapter08.Section02
import NumlibSurface.CartisGouldToint.Chapter08.Section03

/-!
# Cartis, Gould and Toint, Chapter 8: Subproblem Fundamentals

This module collects the formalization of Chapter 8 of [cartis2022evaluation]: the trust-region
subproblem (8.1.2) and the regularization subproblem (8.1.3) for a quadratic model in a scaled norm
$\|\cdot\|_M$, the secular function and its transformed versions, global optimality, and the hard
case. Chapters 8–11 share these conventions: vectors are in `EuclideanSpace ℝ (Fin n)`, $H$ is
symmetric, $M$ is symmetric positive definite, and the eigenvalues of the pencil $(H, M)$ are
`Matrix.pencilEigenvalues`. Every statement is transported through the space
`Subproblem.ScaledSpace` with the $M$-inner product to the operator backbone in
`Numlib.Optimization.Subproblem`. Lemmas B.8.1–B.8.2 of Appendix B are in
`NumlibSurface.CartisGouldToint.AppendixB.Chapter08`. The module imports the section modules and
adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §8.1 The context of the step computation | `Chapter08.Section01` | the two subproblems |
| §8.2 A digression on all things secular | `Chapter08.Section02` | items 8.2.1–8.2.8 |
| §8.3 Subproblem solution | `Chapter08.Section03` | Algorithms and Corollaries 8.3.1–8.3.2 |
-/
