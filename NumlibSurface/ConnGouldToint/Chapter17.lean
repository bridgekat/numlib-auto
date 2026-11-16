/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter17.Section01
import NumlibSurface.ConnGouldToint.Chapter17.Section02
import NumlibSurface.ConnGouldToint.Chapter17.Section03
import NumlibSurface.ConnGouldToint.Chapter17.Section04

/-!
# Conn, Gould and Toint, Chapter 17: Practicalities

Chapter 17 of [conn2000trust] treats the practical choices of a trust-region method: the parameters
of the radius update (Section 17.1), the initial radius (Section 17.2), the generalized Cauchy point
on a box (Section 17.3), and the computation of the model decrease and the stopping residuals
(Section 17.4).

## Contents

| Source | Module | Subject |
|---|---|---|
| §17.1 Practical trust-region parameters | `Chapter17.Section01` | (17.1.1)–(17.1.4) |
| §17.2 The initial radius | `Chapter17.Section02` | Algorithm 17.2.1, (17.2.1)–(17.2.14) |
| §17.3 The generalized Cauchy point on a box | `Chapter17.Section03` | Algorithm 17.3.1 |
| §17.4 Model decrease and stopping residuals | `Chapter17.Section04` | (17.4.1)–(17.4.9) |
-/
