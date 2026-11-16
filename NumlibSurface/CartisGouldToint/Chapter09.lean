/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter09.Section01
import NumlibSurface.CartisGouldToint.Chapter09.Section02
import NumlibSurface.CartisGouldToint.Chapter09.Section03
import NumlibSurface.CartisGouldToint.Chapter09.Section04

/-!
# Cartis, Gould and Toint, Chapter 9: Step Computation with Factorizations

This module collects the formalization of Chapter 9 of [cartis2022evaluation]: the solution of the
subproblems of Chapter 8 with factorizations of $H + \lambda M$. The conventions are those of
Chapter 8, whose definitions are reused. The proofs are in the backbone modules
`Numlib.Optimization.Subproblem.Bracketing`, `Numlib.Optimization.Subproblem.InverseIteration`,
`Numlib.Optimization.Subproblem.Stopping` and `Numlib.Optimization.Subproblem.TrustRegion`. The
module imports the section modules and adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §9.1 Matrix factorization | `Chapter09.Section01` | Algorithm 9.1.1, Corollary 9.1.1 |
| §9.2 Finding a point in $\mathcal{L}$ | `Chapter09.Section02` | Algorithm 9.2.1 |
| §9.3 The regularization subproblem | `Chapter09.Section03` | (9.3.3)–(9.3.7); items 9.3.1–9.3.2 |
| §9.4 The trust-region subproblem | `Chapter09.Section04` | bounds and tests (9.4.1)–(9.4.7) |
-/
