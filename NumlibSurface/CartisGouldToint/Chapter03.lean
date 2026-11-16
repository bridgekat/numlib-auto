/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter03.Section01
import NumlibSurface.CartisGouldToint.Chapter03.Section02
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import NumlibSurface.CartisGouldToint.Chapter03.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section05

/-!
# Cartis, Gould and Toint, Chapter 3: Methods Using Second Derivatives

This module collects the formalization of Chapter 3 of [cartis2022evaluation]: the slow convergence
of Newton's method, the second-order trust-region and adaptive-regularization methods TR2 and AR2,
the methods TRε and iRN with $O(\epsilon^{-3/2})$ evaluations, and the lower bound
$\lceil \epsilon^{-3/2} \rceil$ for the class $\mathcal{M}$ of second-order methods. The tolerance
$\epsilon_2$ is an element of `Option ℝ`, where `none` stands for $\epsilon_2 = +\infty$. The
termination test `CartisGouldToint.Chapter03.stopTest` of TR2 and AR2 covers the separate "strict
local minimizer" branch of the book, because the points of that branch pass the test. Lemma B.3.1 of
Appendix B is in `NumlibSurface.CartisGouldToint.AppendixB.Chapter03`; the proofs in the appendix of
Theorems 3.4.11–3.4.12 and of §3.5 belong to the results of this chapter. The module imports the
section modules and adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §3.1 Slow convergence of Newton's method | `Chapter03.Section01` | f.C2, f.HL; Theorem 3.1.1 |
| §3.2 Trust region with second derivatives | `Chapter03.Section02` | TR2; items 3.2.1–3.2.7 |
| §3.3 Regularization with second derivatives | `Chapter03.Section03` | AR2; items 3.3.1–3.3.10 |
| §3.4 More $O(\epsilon^{-3/2})$ algorithms | `Chapter03.Section04` | TRε, iRN; items 3.4.1–3.4.12 |
| §3.5 Optimal complexity | `Chapter03.Section05` | the class $\mathcal{M}$; items 3.5.1–3.5.5 |
-/
