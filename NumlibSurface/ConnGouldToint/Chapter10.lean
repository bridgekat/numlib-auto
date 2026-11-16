/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter10.Section01
import NumlibSurface.ConnGouldToint.Chapter10.Section02
import NumlibSurface.ConnGouldToint.Chapter10.Section03
import NumlibSurface.ConnGouldToint.Chapter10.Backtracking
import NumlibSurface.ConnGouldToint.Chapter10.Section04
import NumlibSurface.ConnGouldToint.Chapter10.Section05
import NumlibSurface.ConnGouldToint.Chapter10.Section06

/-!
# Conn, Gould and Toint, Chapter 10: Algorithmic Extensions

Chapter 10 of [conn2000trust] treats variants of the basic algorithm: nonmonotone acceptance
(Section 10.1), structured trust regions for partially separable objectives (Section 10.2),
backtracking line searches (Section 10.3), steps with an objective-improving correction (Section
10.4), alternative rules for the radius (Section 10.5), and inexact objective values (Section 10.6).

## Contents

| Source | Module | Subject |
|---|---|---|
| §10.1 Nonmonotone method | `Chapter10.Section01` | Lemma 10.1.1 to Theorem 10.1.4 |
| §10.2 Structured trust regions | `Chapter10.Section02` | Lemma 10.2.1 to Theorem 10.2.6 |
| §10.3 Backtracking directions | `Chapter10.Section03` | Algorithm 10.3.1, Theorems 10.3.1–10.3.4 |
| §10.3 The backtracking trust-region algorithm | `Chapter10.Backtracking` | Algorithm 10.3.2 |
| §10.4 Corrected steps | `Chapter10.Section04` | Algorithm 10.4.1, Theorems 10.4.1–10.4.3 |
| §10.5 Radius management | `Chapter10.Section05` | Algorithm 10.5.1, (10.5.1)–(10.5.8) |
| §10.6 Dynamic accuracy | `Chapter10.Section06` | Algorithm 10.6.1, Lemma 10.6.1 |
-/
