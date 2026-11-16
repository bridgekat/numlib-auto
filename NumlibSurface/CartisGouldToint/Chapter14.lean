/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter14.Section01
import NumlibSurface.CartisGouldToint.Chapter14.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section03

/-!
# Cartis, Gould and Toint, Chapter 14: Composite and Constrained Problems

This module collects the formalization of Chapter 14 of [cartis2022evaluation], the last chapter of
Part II: high-order approximate minimizers and their evaluation complexity for three classes of
problems. The first class is composite problems $\min f(x) + h(c(x))$ with a nonsmooth $h$, solved
by the regularization method ARqpC. The second is problems with simple (inexpensive) constraints
$x \in X$, solved by the "-SC" variants of the methods of Chapters 12–13 and §14.1. The third is
problems with nonconvex equality constraints $c(x) = 0$, $x \in X$, with necessary conditions along
curves, the least-norm method LENq-SC and the two-phase method TPqp-GC. The composite Taylor model
$T_{f,j}(x, s) + h(T_{c,j}(x, s))$ and its measure $\phi^\delta_{w,j}$ (14.1.6) are the backbone
`Optimization.compositeTaylorDecrement` and `Optimization.compositeTaylorMeasure`. ARqpC is the
backbone run `Optimization.IsARqpCRun`, analysed in `Numlib.Optimization.ModelBased.HighOrder.ARqpC`
and `Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity`: it is the ARqp run
`Optimization.IsARqpRun` with composite model data and the detailed Step 2, on a closed feasible set
$X$; with $X = \mathbb{R}^n$ it is ARqpC, with a general $X$ it is ARqpC-SC, and with $c = 0$,
$h = 0$ it is ARqp-SC, the INNER solver of §14.3
(`Numlib.Optimization.ModelBased.HighOrder.ARqpCCall`). The constrained measure (14.2.2) is
`Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ {d | x + d ∈ X}`. In §14.3 the Lagrangian
$f - \langle y, c \rangle$ is `Constrained.innerLagrangian f c y`; Phase 1 of TPqp-GC is LENq-SC on
$c$; Phase 2 and its INNER contracts are the backbone `Constrained.IsHighOrderTargetRun` and
`Constrained.HighOrderTargetSeq.IsMeritContract`; and the INNER calls of both algorithms are
described by contracts on cost and decrease (`CartisGouldToint.Chapter14.innerEvalBound`,
`CartisGouldToint.Chapter14.IsInnerPhaseRunStrong`). Appendix B contains only proofs for this
chapter, so there is no `AppendixB.Chapter14`. The module imports the section modules and adds
nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §14.1 Composite optimization problems | `Chapter14.Section01` | ARqpC; items 14.1.1–14.1.11 |
| §14.2 Simple constraints | `Chapter14.Section02` | -SC methods; items 14.2.1–14.2.5 |
| §14.3 Nonconvex constraints | `Chapter14.Section03` | LENq-SC, TPqp-GC; items 14.3.1–14.3.9 |
-/
