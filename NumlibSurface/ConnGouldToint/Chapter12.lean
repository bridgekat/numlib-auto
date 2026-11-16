/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter12.Section01
import NumlibSurface.ConnGouldToint.Chapter12.Section02
import NumlibSurface.ConnGouldToint.Chapter12.Section03
import NumlibSurface.ConnGouldToint.Chapter12.Section03Counterexample
import NumlibSurface.ConnGouldToint.Chapter12.Section03IterateCounterexample
import NumlibSurface.ConnGouldToint.Chapter12.Section04

/-!
# Conn, Gould and Toint, Chapter 12: Projection Methods for Convex Constraints

Chapter 12 of [conn2000trust] treats trust-region methods for minimizing $f$ over a closed convex
set. Section 12.1 studies the projected-gradient path $p(t) = P_C(x - t \nabla f(x))$ and the
criticality measure, Section 12.2 the generalized Cauchy point and first-order convergence, Section
12.3 the identification of the active constraints at limit points, and Section 12.4 the second-order
analysis on an identified face.

## Contents

| Source | Module | Subject |
|---|---|---|
| §12.1 The projected-gradient path | `Chapter12.Section01` | Theorems 12.1.1–12.1.6 |
| §12.2 Cauchy decrease | `Chapter12.Section02` | Algorithm 12.2.2, Theorems 12.2.1–12.2.2 |
| §12.3 Active constraints | `Chapter12.Section03` | Lemma 12.3.1 to Corollary 12.3.9 |
| §12.3 Cauchy active sets | `Chapter12.Section03Counterexample` | Theorem 12.3.8 |
| §12.3 Remote active set | `Chapter12.Section03ConstraintExample` | constraints of an example |
| §12.3 Iterates | `Chapter12.Section03IterateCounterexample` | Lemma 12.3.7, Theorem 12.3.8 |
| §12.4 Models on an identified face | `Chapter12.Section04` | Lemma 12.4.1 to Theorem 12.4.6 |
-/
