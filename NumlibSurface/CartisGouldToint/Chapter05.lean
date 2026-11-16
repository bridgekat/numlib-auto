/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter05.Section01
import NumlibSurface.CartisGouldToint.Chapter05.Section02
import NumlibSurface.CartisGouldToint.Chapter05.Section03
import NumlibSurface.CartisGouldToint.Chapter05.Section04
import NumlibSurface.CartisGouldToint.Chapter05.Section05

/-!
# Cartis, Gould and Toint, Chapter 5: Structured Problems

This module collects the formalization of Chapter 5 of [cartis2022evaluation]: problems whose
structure improves on the complexity bounds of Chapters 2–4. Section 5.1 treats least-squares and
least-Euclidean-norm problems through $\Phi_\ell = \|r\|^\ell / \ell$ and the method ARpLE, which is
the backbone run `Optimization.IsARpRun` applied to $\Phi_\ell$. Section 5.3 treats
measure-dominated problems with the classes $\mathrm{AR}_{\psi,\nu}$ and $\mathrm{TR}_{\psi,\nu}$,
which are `Optimization.IsARLikeRun` and `Optimization.IsTRLikeRun`; their analysis is the scalar
recurrences of `Numlib.Optimization.Complexity.GapRecurrence`. Section 5.4 analyses AR2 near a
strict local minimizer, and §5.5 the universal regularization method ARp-H, an instance of
`Optimization.IsARRun`. Rates and statements of the form "at most $N$ iterations" are stated as
upper bounds along the iterations. Lemma B.5.1 of Appendix B is in
`NumlibSurface.CartisGouldToint.AppendixB.Chapter05`. The module imports the section modules and
adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §5.1 Least squares and least Euclidean norms | `Chapter05.Section01` | ARpLE; items 5.1.1–5.1.7 |
| §5.2 Partially separable problems | `Chapter05.Section02` | (5.2.1)–(5.2.2) |
| §5.3 Measure-dominated problems | `Chapter05.Section03` | items 5.3.1–5.3.12 |
| §5.4 Phase complexity under strict local convexity | `Chapter05.Section04` | items 5.4.1–5.4.4 |
| §5.5 Universal regularization methods | `Chapter05.Section05` | ARp-H, f.DpH; items 5.5.1–5.5.7 |
-/
