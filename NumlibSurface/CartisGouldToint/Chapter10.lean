/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter10.Section01
import NumlibSurface.CartisGouldToint.Chapter10.Section02
import NumlibSurface.CartisGouldToint.Chapter10.Section03

/-!
# Cartis, Gould and Toint, Chapter 10: Step Computation without Factorizations

This module collects the formalization of Chapter 10 of [cartis2022evaluation]: the subproblems of
Chapter 8 restricted to the Krylov subspaces $\mathcal{K}_k = \mathcal{K}(M^{-1}H, M^{-1}g, k)$,
their computation by the preconditioned Lanczos method, and the convergence of the subspace
solutions. The conventions are those of Chapter 8, and $\|M^{-1}H\|$ is the operator norm induced by
$\|\cdot\|_M$. Krylov subspaces are the backbone `Krylov.subspace`, and the proofs are in the
backbone modules `Numlib.Optimization.Subproblem.Krylov`,
`Numlib.Optimization.Subproblem.KrylovConvergence`, `Numlib.LinearAlgebra.Matrix.TridiagonalLDL` and
`Numlib.LinearAlgebra.Matrix.InverseDecay`. Lemma B.10.1 of Appendix B is in
`NumlibSurface.CartisGouldToint.AppendixB.Chapter10`. The module imports the section modules and
adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §10.1 Krylov-subspace methods | `Chapter10.Section01` | Lanczos (Algorithm 10.1.1) |
| §10.2 Regularization methods | `Chapter10.Section02` | items 10.2.1–10.2.3 |
| §10.3 The trust-region case | `Chapter10.Section03` | items 10.3.1–10.3.3 |
-/
