/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter14.Section01
import NumlibSurface.ConnGouldToint.Chapter14.Section02
import NumlibSurface.ConnGouldToint.Chapter14.Section03
import NumlibSurface.ConnGouldToint.Chapter14.Section04
import NumlibSurface.ConnGouldToint.Chapter14.Section05
import NumlibSurface.ConnGouldToint.Chapter14.Section06

/-!
# Conn, Gould and Toint, Chapter 14: Penalty-Function Methods

Chapter 14 of [conn2000trust] treats penalty methods for minimizing $f(x)$ subject to $c(x) = 0$.
The modules cover the setting (Section 14.1), the quadratic penalty and augmented Lagrangian
functions and their multiplier estimates (Section 14.2), the convergence of quadratic penalty
methods (Section 14.3) and augmented Lagrangian methods (Section 14.4), and nonsmooth and smooth
exact penalty functions (Sections 14.5–14.6).

## Contents

| Source | Module | Subject |
|---|---|---|
| §14.1 Penalty methods: motivation and notation | `Chapter14.Section01` | AW.1, (14.1.4) |
| §14.2 Quadratic penalty, augmented Lagrangian | `Chapter14.Section02` | Lemmas 14.2.1–14.2.2 |
| §14.3 Quadratic penalty methods | `Chapter14.Section03` | Theorem 14.3.1, Lemma 14.3.2 |
| §14.4 Augmented Lagrangian methods | `Chapter14.Section04` | Lemma 14.4.1 to Theorem 14.4.7 |
| §14.5 Nonsmooth exact penalties | `Chapter14.Section05` | Theorems 14.5.1–14.5.2 |
| §14.6 Smooth exact penalties | `Chapter14.Section06` | Theorem 14.6.1 |
-/
