/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter01.Section01

/-!
# Cartis, Gould and Toint, Chapter 1: Introduction

This module collects the formalization of Chapter 1 of [cartis2022evaluation]. Only §1.1, "Nonlinear
optimization and optimality conditions", has numbered results: the Lagrangian, active sets, the
linear independence constraint qualification (LICQ) and KKT pairs, the first-, second- and
third-order optimality conditions of Theorems 1.1.1–1.1.4, and the criticality measures $\omega_1$
and $\omega_2$. Each clause of Theorems 1.1.1–1.1.4 is a declaration of its own. The least
eigenvalue $\lambda_{\min}[\nabla^2 f(x)]$ of the Hessian is
`CartisGouldToint.Chapter01.hessianMinEig`, which every later chapter uses. Sections 1.2–1.4, on the
history and the scope of evaluation complexity, contain no numbered results. The module imports the
section module and adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1.1 Optimality conditions | `Chapter01.Section01` | LICQ, KKT pairs; Theorems 1.1.1–1.1.4 |
-/
