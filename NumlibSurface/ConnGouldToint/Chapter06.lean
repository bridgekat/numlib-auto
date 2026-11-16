/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter06.Section01
import NumlibSurface.ConnGouldToint.Chapter06.Section03
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import NumlibSurface.ConnGouldToint.Chapter06.Section05
import NumlibSurface.ConnGouldToint.Chapter06.Section06
import NumlibSurface.ConnGouldToint.Chapter06.Section07

/-!
# Conn, Gould and Toint, Chapter 6: Global Convergence of the Basic Algorithm

Chapter 6 of [conn2000trust] defines the basic trust-region algorithm, Algorithm 6.1.1, and proves
its global convergence. The model decrease at the Cauchy point (Section 6.3) gives convergence of
the gradients to zero (Section 6.4). Locally convex models make the whole sequence converge to a
critical point with a nonsingular Hessian (Section 6.5), negative curvature steps give convergence
to second-order critical points (Section 6.6), and Section 6.7 treats the scaling of the variables.

## Contents

| Source | Module | Subject |
|---|---|---|
| §6.1 The basic algorithm | `Chapter06.Section01` | Algorithm 6.1.1, (6.1.2)–(6.1.7) |
| §6.3 The Cauchy point of a quadratic model | `Chapter06.Section03` | Theorems 6.3.1, 6.3.3–6.3.5 |
| §6.4 Convergence to first-order critical points | `Chapter06.Section04` | Theorems 6.4.1–6.4.6 |
| §6.5 Asymptotically convex models | `Chapter06.Section05` | Lemma 6.5.1 to Theorem 6.5.5 |
| §6.6 Exploiting negative curvature | `Chapter06.Section06` | Theorem 6.6.1 to Theorem 6.6.8 |
| §6.7 Variable scaling | `Chapter06.Section07` | Theorem 6.7.1 |
-/
