/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter06.Section01
import NumlibSurface.CartisGouldToint.Chapter06.Section02
import NumlibSurface.CartisGouldToint.Chapter06.Section03

/-!
# Cartis, Gould and Toint, Chapter 6: Convexly Constrained Problems

This module collects the formalization of Chapter 6 of [cartis2022evaluation]: the minimization of
$f(x)$ over a closed, convex and nonempty set $\mathcal{C}$. The criticality measures
$\omega_{f,\mathcal{C},1}$, $\omega_{f,\mathcal{C},2}$ and $\omega_{f,\mathcal{C},3}$ are instances
of the backbone `Optimization.formCriticality` over `Optimization.feasibleSteps` or
`Optimization.restrictedSteps`, and the runs of ARp-CC, ARp1-CC and ARpLE-CC are instances of
`Optimization.IsARRun`. The order of the sought minimizer is an explicit $q \in \{1, 2, 3\}$ with
$q \le p$, in place of the infinite tolerances of the book. The module imports the section modules
and adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §6.1 Problems with convex constraints | `Chapter06.Section01` | C.CNe; measures (6.1.5)–(6.1.10) |
| §6.2 The ARp-CC algorithm | `Chapter06.Section02` | ARp-CC, ARp1-CC; items 6.2.1–6.2.5 |
| §6.3 Convex constraints, least Euclidean norm | `Chapter06.Section03` | ARpLE-CC; Theorem 6.3.1 |
-/
