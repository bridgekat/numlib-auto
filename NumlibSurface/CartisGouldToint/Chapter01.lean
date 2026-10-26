import NumlibSurface.CartisGouldToint.Chapter01.Section01

/-!
# Cartis–Gould–Toint, Chapter 1: Introduction

Surface of [cartis2022evaluation] Chapter 1. Only §1.1, "Nonlinear optimization and optimality
conditions", has numbered results; §§1.2–1.4 (the history and scope of evaluation complexity)
contain none. This module imports the section module and adds nothing of its own.

* §1.1, `Chapter01.Section01`: Lagrangian, active sets, LICQ, KKT pairs; Theorems 1.1.1–1.1.4; the
  measures `ω₁`, `ω₂`

Each clause of Theorems 1.1.1–1.1.4 is a declaration of its own (`theorem_1_1_2_i` …
`theorem_1_1_2_iv`, and so on). The least Hessian eigenvalue `λ_min[∇²f(x)]` is `hessianMinEig`,
used by every later chapter.

## Deviations from the book

* The converse of Theorem 1.1.2 is false as printed: the strict-curvature condition on the radial
  directions `𝒞(x*)` does not make `x*` a local minimizer of `f` on a closed convex set
  (`theorem_1_1_2_iv_counterexample`, on `C = {v ≥ u²}`). `theorem_1_1_2_iv` asks for the condition
  on the tangent cone instead.
* The sufficient conditions (1.1.15) and (1.1.18) quantify over `d ≠ 0` (with `d = 0` the strict
  inequality is unsatisfiable).
* "A constraint qualification" is taken to be LICQ (`licq`); the second-order necessary conditions
  are proved for every multiplier satisfying the first-order conditions.

See `Chapter01.Section01` for the remaining minor readings.

## Not formalized

The tensor-product notation (1.1.2); the equivalent "minimum over the unit ball" forms
(1.1.10)–(1.1.12), (1.1.19); the projection form of (1.1.6); the reduced-Hessian reformulation of
(1.1.14)–(1.1.15); the hardness remarks.
-/
