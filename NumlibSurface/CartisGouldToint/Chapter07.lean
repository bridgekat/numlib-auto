/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter07.Section01
import NumlibSurface.CartisGouldToint.Chapter07.Section02

/-!
# Cartis, Gould and Toint, Chapter 7: Problems with Nonconvex Constraints

This module collects the formalization of Chapter 7 of [cartis2022evaluation]: the minimization of
$f(x)$ over $x \in \mathcal{C}$ subject to $c(x) = 0$ (7.1.1), its Lagrangian $\mathcal{L}(x, y) =
f(x) - \langle y, c(x) \rangle$, scaled approximate first-order criticality (7.1.4), and the
two-phase target-following method TPp-GC (Algorithm 7.2.1). The target residual and the merit
function are the backbone `Constrained.targetResidual` and `Constrained.targetMerit`. Phase 1 is an
ARpLE-CC run (§6.3) on $c$. Phase 2 is the run predicate `CartisGouldToint.Chapter07.IsTPpGCPhase2`,
an instance of the backbone target-following outer loop `Constrained.IsTargetFollowingRun`; Lemma
7.2.6 and Theorem 7.2.7 follow from its complexity theorem, which TPqp-GC of Chapter 14 shares.
Lemma B.7.1 of Appendix B is in `NumlibSurface.CartisGouldToint.AppendixB.Chapter07`. The module
imports the section modules and adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §7.1 The general constrained problem | `Chapter07.Section01` | (7.1.1), (7.1.4); Theorem 7.1.1 |
| §7.2 First-order approximate minimizers | `Chapter07.Section02` | TPp-GC; items 7.2.1–7.2.7 |
-/
