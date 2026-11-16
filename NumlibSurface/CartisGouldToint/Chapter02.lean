/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter02.Section01
import NumlibSurface.CartisGouldToint.Chapter02.Section02
import NumlibSurface.CartisGouldToint.Chapter02.Section03
import NumlibSurface.CartisGouldToint.Chapter02.Section04

/-!
# Cartis, Gould and Toint, Chapter 2: Methods Using First Derivatives

This module collects the formalization of Chapter 2 of [cartis2022evaluation]: first-order methods
for the unconstrained minimization of a function that satisfies the assumptions f.Bb, f.C1 and f.gL.
Each method needs $O(\epsilon^{-2})$ evaluations to find a point with
$\|\nabla f(x)\| \le \epsilon$, and an example shows that this order is attained. The algorithms are
the run predicates `CartisGouldToint.Chapter02.algorithm_2_2_1` (steepest descent with backtracking,
SDBA), `CartisGouldToint.Chapter02.IsSDEXRun` (steepest descent with exact linesearch, SDEX),
`CartisGouldToint.Chapter02.algorithm_2_3_1` (the trust-region method TR1) and
`CartisGouldToint.Chapter02.algorithm_2_4_1` (the adaptive-regularization method AR1), each with an
existence theorem. TR1 and AR1 are instances of the backbone runs `Optimization.IsTRRun` and
`Optimization.IsARRun`. The zig-zag example behind Theorem 2.2.5 is formed by Lemmas B.2.1–B.2.6 of
Appendix B, in `NumlibSurface.CartisGouldToint.AppendixB.Chapter02`. Section 2.5 has no numbered
results. The module imports the section modules and adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §2.1 A requirement | `Chapter02.Section01` | the assumptions f.Bb, f.C1, f.gL |
| §2.2 Linesearch algorithms | `Chapter02.Section02` | SDBA, SDEX; items 2.2.1–2.2.5 |
| §2.3 The trust-region method | `Chapter02.Section03` | TR1; items 2.3.1–2.3.8 |
| §2.4 The adaptive-regularization method | `Chapter02.Section04` | AR1; items 2.4.1–2.4.5 |
-/
