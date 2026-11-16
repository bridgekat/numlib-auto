/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter09.InterpolationCounterexample
import NumlibSurface.ConnGouldToint.Chapter09.Section01
import NumlibSurface.ConnGouldToint.Chapter09.Section02
import NumlibSurface.ConnGouldToint.Chapter09.Section03
import NumlibSurface.ConnGouldToint.Chapter09.Section04
import NumlibSurface.ConnGouldToint.Chapter09.Section05

/-!
# Conn, Gould and Toint, Chapter 9: Conditional Models

Chapter 9 of [conn2000trust] treats trust-region methods whose models need only be valid on a ball,
$|f(z) - m(z)| \le \kappa \delta^2$ for $z \in B(x, \delta)$, rather than agree with the objective
to first order. Sections 9.1–9.3 define such conditional models and prove convergence to first- and
second-order critical points. Section 9.4 builds them without derivatives by Newton interpolation,
and Section 9.5 treats models with memory.

## Contents

| Source | Module | Subject |
|---|---|---|
| §9.1 Conditional models | `Chapter09.Section01` | Theorem 9.1.1, Lemma 9.1.2(i), (iii) |
| §9.2 First-order convergence | `Chapter09.Section02` | Lemma 9.1.2(ii), Theorem 9.2.1 to 9.2.6 |
| §9.3 Second-order convergence | `Chapter09.Section03` | Algorithm 9.3.1, Theorems 9.3.1, 9.3.3 |
| §9.4 Newton interpolation | `Chapter09.Section04` | Algorithms 9.4.1–9.4.2, Theorems 9.4.1–9.4.4 |
| §9.4 Incomplete quadratic blocks | `Chapter09.InterpolationCounterexample` | Theorem 9.4.4 |
| §9.5 Conditional models with memory | `Chapter09.Section05` | Theorems 9.5.1–9.5.2 |
-/
