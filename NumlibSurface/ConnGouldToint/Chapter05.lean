/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter05.Section01
import NumlibSurface.ConnGouldToint.Chapter05.Section02
import NumlibSurface.ConnGouldToint.Chapter05.Section03
import NumlibSurface.ConnGouldToint.Chapter05.Section04

/-!
# Conn, Gould and Toint, Chapter 5: Krylov Subspace Methods

Chapter 5 of [conn2000trust] treats the Krylov subspace methods that solve the linear systems and
subproblems of trust-region methods. Section 5.1 proves the properties and error bounds of the
conjugate gradient method and its preconditioned form, Section 5.2 builds the Lanczos basis and its
tridiagonal matrix, Section 5.3 applies conjugate gradients to linear least-squares problems, and
Section 5.4 treats quadratic problems with linear equality constraints by reduced and projected
conjugate gradients.

## Contents

| Source | Module | Subject |
|---|---|---|
| §5.1 Conjugate gradients | `Chapter05.Section01` | Lemma 5.1.1 to Corollary 5.1.9 |
| §5.2 The Lanczos basis | `Chapter05.Section02` | Lemma 5.2.1, Algorithms 5.2.1–5.2.4 |
| §5.3 Linear least-squares problems | `Chapter05.Section03` | Algorithm 5.3.1, Theorem 5.3.1 |
| §5.4 Problems with linear constraints | `Chapter05.Section04` | Algorithms 5.4.1–5.4.2 |
-/
