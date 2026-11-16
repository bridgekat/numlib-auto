/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter08.Section01
import NumlibSurface.ConnGouldToint.Chapter08.Section03
import NumlibSurface.ConnGouldToint.Chapter08.Section04
import NumlibSurface.ConnGouldToint.Chapter08.Section05

/-!
# Conn, Gould and Toint, Chapter 8: Further Convergence Theory Issues

Chapter 8 of [conn2000trust] extends the convergence theory of Chapter 6. Section 8.1 allows
trust-region norms that vary with the iteration, Section 8.3 replaces the least eigenvalue by the
Rayleigh infimum in Hilbert spaces, Section 8.4 allows approximate model gradients and growing model
Hessians, and Section 8.5 treats composite objectives $f(x) = f_0(x, u(x))$.

## Contents

| Source | Module | Subject |
|---|---|---|
| §8.1 Iteration-dependent norms | `Chapter08.Section01` | Lemma 8.1.1 to Theorem 8.1.12 |
| §8.3 Rayleigh infima in Hilbert spaces | `Chapter08.Section03` | (8.3.3) |
| §8.4 Approximate derivatives | `Chapter08.Section04` | Lemma 8.4.1, Theorems 8.4.2–8.4.8 |
| §8.5 Composite objective functions | `Chapter08.Section05` | Theorems 8.5.1–8.5.2 |
-/
