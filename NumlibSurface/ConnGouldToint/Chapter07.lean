/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter07.Section02
import NumlibSurface.ConnGouldToint.Chapter07.Section03
import NumlibSurface.ConnGouldToint.Chapter07.Section03Algorithms
import NumlibSurface.ConnGouldToint.Chapter07.Section03Cholesky
import NumlibSurface.ConnGouldToint.Chapter07.Section03Direction
import NumlibSurface.ConnGouldToint.Chapter07.Section03HardLimit
import NumlibSurface.ConnGouldToint.Chapter07.Section03Matrix
import NumlibSurface.ConnGouldToint.Chapter07.Section04
import NumlibSurface.ConnGouldToint.Chapter07.Section05
import NumlibSurface.ConnGouldToint.Chapter07.Section05Algorithm
import NumlibSurface.ConnGouldToint.Chapter07.Section07

/-!
# Conn, Gould and Toint, Chapter 7: The Trust-Region Subproblem

Chapter 7 of [conn2000trust] treats the trust-region subproblem of minimizing a quadratic model
$q(s) = \langle g, s \rangle + \frac12 \langle s, H s \rangle$ subject to $\|s\| \le \Delta$.
Section 7.2 characterizes its global minimizers. Section 7.3 solves it by the Moré–Sorensen method
for the secular equation, with safeguards, Cholesky factorizations and the LINPACK direction in the
hard case. Section 7.4 treats scaled Euclidean norms, Section 7.5 the truncated conjugate gradient
and Lanczos methods, and Section 7.7 a diagonal trust-region Newton iteration.

## Contents

| Source | Module | Subject |
|---|---|---|
| §7.2 The Euclidean model minimizer | `Chapter07.Section02` | Theorem 7.2.1, Corollary 7.2.2 |
| §7.3 The Moré–Sorensen method | `Chapter07.Section03` | Lemma 7.3.1 to Lemma 7.3.6 |
| §7.3 Separate safeguards | `Chapter07.Section03Algorithms` | Algorithms 7.3.2, 7.3.3, 7.3.6 |
| §7.3.7 The LINPACK direction | `Chapter07.Section03Direction` | §7.3.7, (7.3.16)–(7.3.17) |
| §7.3 LINPACK matrix certificates | `Chapter07.Section03Matrix` | Theorem 7.3.4, hard case |
| §7.3.7 Cholesky pivot detection | `Chapter07.Section03Cholesky` | Algorithm 7.3.4, (7.3.17) |
| §7.3 One-sided stabilization | `Chapter07.Section03HardLimit` | Theorem 7.3.4, hard case |
| §7.4 The scaled Euclidean trust-region problem | `Chapter07.Section04` | Theorem 7.4.1 |
| §7.5 Truncated CG and Lanczos | `Chapter07.Section05` | Theorem 7.5.1 to Theorem 7.5.17 |
| Algorithm 7.5.2 Generalized Lanczos | `Chapter07.Section05Algorithm` | Algorithm 7.5.2 |
| §7.7 The diagonal trust-region Newton iteration | `Chapter07.Section07` | Algorithm 7.7.1 |
-/
