/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter16.Section01
import NumlibSurface.ConnGouldToint.Chapter16.Section02
import NumlibSurface.ConnGouldToint.Chapter16.Section03

/-!
# Conn, Gould and Toint, Chapter 16: Nonlinear Equations and Nonlinear Fitting

Chapter 16 of [conn2000trust] applies trust-region methods to nonlinear equations and fitting
problems: nonlinear least squares $\min \frac12 \|c(x)\|^2$ (Section 16.1), composite nonsmooth
problems $\min h(c(x))$ where $h$ is a maximum of finitely many affine functions (Section 16.2), and
complementarity problems through the Fischer–Burmeister function (Section 16.3).

## Contents

| Source | Module | Subject |
|---|---|---|
| §16.1 Nonlinear equations and least squares | `Chapter16.Section01` | Theorems 16.1.1–16.1.4 |
| §16.2 Composite problems | `Chapter16.Section02` | Algorithm 16.2.1, Theorems 16.2.1–16.2.2 |
| §16.3 Complementarity problems | `Chapter16.Section03` | Theorem 16.3.1 |
-/
