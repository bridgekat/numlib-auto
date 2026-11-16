/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import NumlibSurface.CartisGouldToint.Chapter04.Section02

/-!
# Cartis, Gould and Toint, Chapter 4: Methods Using Third Derivatives and Beyond

This module collects the formalization of Chapter 4 of [cartis2022evaluation]. Section 4.1 studies
the adaptive-regularization method ARp with Taylor models of order $p$ and proves that it finds an
approximate minimizer of order $q \in \{1, 2, 3\}$ with $O(\epsilon^{-(p+1)/(p-q+1)})$ evaluations.
Section 4.2 proves the lower bound of Carmon, Duchi, Hinder and Sidford for methods of order $p$ on
functions of unbounded dimension, which shows that ARp is optimal. ARp is the backbone run predicate
`Optimization.IsARpRun`. The lower bound uses the backbone modules
`Numlib.Optimization.Complexity.ZeroChain`, `Numlib.Optimization.Complexity.ResistingOracle` and
`Numlib.Optimization.Complexity.CarmonChain`. Lemma B.4.1 of Appendix B is in
`NumlibSurface.CartisGouldToint.AppendixB.Chapter04`. The module imports the section modules and
adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §4.1 The ARp algorithm | `Chapter04.Section01` | ARp, f.DpL; items 4.1.1–4.1.6 |
| §4.2 A lower complexity bound | `Chapter04.Section02` | zero chains; items 4.2.1–4.2.6 |
-/
