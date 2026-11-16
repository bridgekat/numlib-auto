/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter13.Section01
import NumlibSurface.ConnGouldToint.Chapter13.Section02
import NumlibSurface.ConnGouldToint.Chapter13.Section03
import NumlibSurface.ConnGouldToint.Chapter13.Section04
import NumlibSurface.ConnGouldToint.Chapter13.Section06
import NumlibSurface.ConnGouldToint.Chapter13.Section07
import NumlibSurface.ConnGouldToint.Chapter13.Section09
import NumlibSurface.ConnGouldToint.Chapter13.Section10
import NumlibSurface.ConnGouldToint.Chapter13.Section11
import NumlibSurface.ConnGouldToint.Chapter13.Section12

/-!
# Conn, Gould and Toint, Chapter 13: Barrier Methods for Inequality Constraints

Chapter 13 of [conn2000trust] treats barrier methods, which minimize $f(x) - \mu \sum_i \log c_i(x)$
for a decreasing sequence of barrier parameters $\mu$. The modules cover the outer iteration and the
primal inner algorithms (Sections 13.1–13.4), primal-dual methods (Section 13.6), scaling (Section
13.7), general inequality constraints (Section 13.9), affine equality constraints (Section 13.10),
and affine-scaling and Coleman–Li methods for bound constraints (Sections 13.11–13.12).

## Contents

| Source | Module | Subject |
|---|---|---|
| §13.1 The logarithmic barrier | `Chapter13.Section01` | Algorithm 13.1.1, (13.1.1)–(13.1.2) |
| §13.2 First inner algorithm | `Chapter13.Section02` | Algorithm 13.2.1, Theorems 13.2.1–13.2.3 |
| §13.3 Cauchy and eigenpoints | `Chapter13.Section03` | Algorithm 13.3.1, Theorems 13.3.1, 13.3.3 |
| §13.4 Barrier model | `Chapter13.Section04` | Algorithm 13.4.1, Lemma 13.4.1 to Corollary 13.4.4 |
| §13.6 Primal-dual methods | `Chapter13.Section06` | Lemma 13.6.1 to Theorem 13.6.4 |
| §13.7 Scaling of barrier methods | `Chapter13.Section07` | Theorems 13.7.1–13.7.3 |
| §13.9 General inequalities | `Chapter13.Section09` | Algorithms 13.9.1–13.9.2, Theorem 13.9.1 |
| §13.10 Affine slices of the orthant | `Chapter13.Section10` | Algorithm 13.10.1, Theorem 13.10.2 |
| §13.11 Affine scaling | `Chapter13.Section11` | Algorithm 13.11.1, Theorem 13.11.1 |
| §13.12 Coleman–Li scaling | `Chapter13.Section12` | Theorems 13.12.1–13.12.6, two algorithms |
-/
