/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter12.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section02
import NumlibSurface.CartisGouldToint.Chapter12.Section03

/-!
# Cartis, Gould and Toint, Chapter 12: Finding High-Order Approximate Minimizers

This module collects the formalization of Chapter 12 of [cartis2022evaluation], the first chapter of
Part II. It covers necessary optimality conditions of arbitrary order and their limits; the
Taylor-decrement measure $\phi^\delta_{f,j}(x) = f(x) - \min_{\|d\| \le \delta} T_{f,j}(x, d)$,
which is `Optimization.taylorMeasure`; the $(\epsilon, \delta)$-approximate minimizers of order $q$
(12.1.25), which are `Optimization.IsEpsDeltaApprox`; the trust-region method TRq and the
regularization method ARqp with their complexity and its sharpness; and inexact global minimization
of the model. TRq and ARqp are the backbone run predicates `Optimization.IsTRqRun` and
`Optimization.IsARqpRun` with the exact data `ftaylorSeries ℝ f (x k)`, and the tolerances and radii
are vectors `ε δ : ℕ → ℝ` indexed by the order. The complexity analyses are those of the backbone
modules `Numlib.Optimization.ModelBased.HighOrder.TRqComplexity`,
`Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity` and
`Numlib.Optimization.ModelBased.HighOrder.ARqpDetailedStep`. They are stated on a feasible set under
anchored Lipschitz bounds on the derivatives (`LipschitzDerivsAnchored`), and the theorems of the
book are their unconstrained instances. `NumlibSurface.CartisGouldToint.Chapter12.Section02` also
defines the runs on a feasible set that Chapter 14 uses,
`CartisGouldToint.Chapter12.algorithm_12_2_1_feasible` and
`CartisGouldToint.Chapter12.algorithm_12_2_2_feasible`. Lemma B.12.1 of Appendix B is in
`NumlibSurface.CartisGouldToint.AppendixB.Chapter12`. The module imports the section modules and
adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §12.1 Optimality conditions revisited | `Chapter12.Section01` | items 12.1.1–12.1.8 |
| §12.2 Minimizers of arbitrary order | `Chapter12.Section02` | TRq, ARqp; items 12.2.1–12.2.17 |
| §12.3 Inexact global minimization in ARqp | `Chapter12.Section03` | relaxed Step 2 of ARqp |
-/
