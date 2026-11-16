/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter13.Section01
import NumlibSurface.CartisGouldToint.Chapter13.Section02
import NumlibSurface.CartisGouldToint.Chapter13.Section03

/-!
# Cartis, Gould and Toint, Chapter 13: Inexact Function Values and Derivatives

This module collects the formalization of Chapter 13 of [cartis2022evaluation]: the high-order
methods of Chapter 12 with inexact derivatives, and in §13.3 also inexact function values, whose
accuracy the algorithm controls. The trust-region method TRqIDA and the regularization method
ARqpIDA use exact function values and derivative estimates within $\kappa_{\nabla,i} h_{k,i}$ of the
true derivatives, for constants $\kappa_{\nabla,i}$ that the algorithm does not know (implicit
dynamic accuracy). Their variants TRqEDA and ARqpEDA with explicit dynamic accuracy also use inexact
function values and certify termination. Both families keep the orders of complexity of TRq and
ARqp. The analyses are those of the backbone module
`Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy`, for the runs `Optimization.IsTRqIDARun`,
`Optimization.IsARqpIDARun`, `Optimization.IsTRqEDARun` and `Optimization.IsARqpEDARun` on a
feasible set $X$, under the anchored assumption `LipschitzDerivsAnchored f C A 0 p L` with an anchor
set $A$ that contains the sublevel set $\{y \in X \mid f(y) \le f(x_0)\}$. The results of the book
are their instances with $X = C = A = \mathbb{R}^n$; the rows of §14.2 on a feasible set are in
`NumlibSurface.CartisGouldToint.Chapter14.Section02`. Appendix B contains only proofs for this
chapter, so there is no `AppendixB.Chapter13`. The module imports the section modules and adds
nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §13.1 Implicit dynamic accuracy | `Chapter13.Section01` | TRqIDA, ARqpIDA; items 13.1.1–13.1.19 |
| §13.2 Low-degree oracles | `Chapter13.Section02` | (13.2.1)–(13.2.4), Theorem 13.2.1 |
| §13.3 Explicit dynamic accuracy | `Chapter13.Section03` | TRqEDA, ARqpEDA; items 13.3.1–13.3.8 |
-/
