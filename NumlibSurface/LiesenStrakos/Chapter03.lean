/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.LiesenStrakos.Chapter03.Section01
import NumlibSurface.LiesenStrakos.Chapter03.Section02
import NumlibSurface.LiesenStrakos.Chapter03.Section03
import NumlibSurface.LiesenStrakos.Chapter03.Section04
import NumlibSurface.LiesenStrakos.Chapter03.Section05
import NumlibSurface.LiesenStrakos.Chapter03.Section06
import NumlibSurface.LiesenStrakos.Chapter03.Section07
import NumlibSurface.LiesenStrakos.Chapter03.Section08
import NumlibSurface.LiesenStrakos.Chapter03.Section09

/-!
# Liesen and Strakoš, Chapter 3. Matching moments and model reduction view

Chapter 3 of [liesen2013krylov] interprets Krylov methods as moment matching. The Stieltjes
formulation matches the moments of a measure by a finite Gauss–Christoffel rule. The Vorobyev
formulation matches the scalar and vector moments of an operator by compressing it onto a Krylov
subspace. Jacobi matrices link the two formulations, and the inverse moment of the reduced
measure gives the Gauss quadrature interpretation of the conjugate gradient error.

## Contents

| Source | Module | Subject |
|---|---|---|
| §3.1 | `Chapter03.Section01` | Stieltjes moment problem and degree of exactness |
| §3.2 | `Chapter03.Section02` | Gauss–Christoffel quadrature and its uniqueness |
| §3.3 | `Chapter03.Section03` | Strict interlacing, continued fractions and resolvent convergence |
| §3.4 | `Chapter03.Section04` | Jacobi matrices and eigenvalue persistence |
| §3.5 | `Chapter03.Section05` | Spectral measures and the CG energy error |
| §3.6 | `Chapter03.Section06` | Hankel moment matrices and the Cholesky factor |
| §3.7 | `Chapter03.Section07` | Vorobyev compression and moment matching |
| §3.8 | `Chapter03.Section08` | Projection decomposition for the CG residual |
| §3.9 | `Chapter03.Section09` | Transfer functions and partial realization |
-/
