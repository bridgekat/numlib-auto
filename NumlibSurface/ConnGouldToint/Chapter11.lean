/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter11.Section01
import NumlibSurface.ConnGouldToint.Chapter11.Section02
import NumlibSurface.ConnGouldToint.Chapter11.Section03
import NumlibSurface.ConnGouldToint.Chapter11.Section04
import NumlibSurface.ConnGouldToint.Chapter11.Section05

/-!
# Conn, Gould and Toint, Chapter 11: Nonsmooth Problems

Chapter 11 of [conn2000trust] extends trust-region methods to locally Lipschitz objectives, with the
Clarke directional derivative in place of the gradient. Sections 11.1–11.3 prove convergence of the
basic, nonmonotone and corrected nonsmooth methods to Clarke stationary points. Section 11.4
computes the generalized gradients of residual penalties, and Section 11.5 proves the accuracy of
Taylor models of composite objectives $f(x) + h(c(x))$.

## Contents

| Source | Module | Subject |
|---|---|---|
| §11.1 Nonsmooth steepest descent | `Chapter11.Section01` | Lemma 11.1.1 to Corollary 11.1.4 |
| §11.2 Normalized model error | `Chapter11.Section02` | Lemmas 11.2.1–11.2.4, Theorem 11.2.5 |
| §11.3 Corrected steps | `Chapter11.Section03` | Algorithm 11.3.1, Theorems 11.3.1–11.3.2 |
| §11.4 Residual penalties | `Chapter11.Section04` | Theorem 11.4.1 to Theorem 11.4.3 |
| §11.5 Taylor models of composites | `Chapter11.Section05` | Theorem 11.5.1 |
-/
