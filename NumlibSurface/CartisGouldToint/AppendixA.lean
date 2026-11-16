/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.AppendixA.Section08
import NumlibSurface.CartisGouldToint.AppendixA.Section09
import NumlibSurface.CartisGouldToint.AppendixA.Section10

/-!
# Cartis, Gould and Toint, Appendix A: Background and General Technical Results

This module collects the formalization of Appendix A of [cartis2022evaluation]. Only §§A.8–A.10
contain numbered results: Taylor's theorem, Hermite interpolation and bounds on partial sums of the
exponential series. Mathlib and the backbone supply the notation of §§A.1–A.7: the tensor norm (A.7)
is the operator norm of continuous multilinear maps, $\nabla^j f(x)$ is `iteratedFDeriv ℝ j f x`,
and $\lambda_{\min}$ is `minCurvature`. The module imports the section modules and adds nothing of
its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §A.8 Taylor's theorem | `AppendixA.Section08` | items A.8.1–A.8.5, (A.16) |
| §A.9 Polynomial Hermite interpolation | `AppendixA.Section09` | Theorems A.9.1–A.9.2 |
| §A.10 Simple series bounds | `AppendixA.Section10` | Lemma A.10.1, (A.34)–(A.36) |
-/
