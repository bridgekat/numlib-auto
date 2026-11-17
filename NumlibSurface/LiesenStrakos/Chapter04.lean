import NumlibSurface.LiesenStrakos.Chapter04.Section01
import NumlibSurface.LiesenStrakos.Chapter04.Section02
import NumlibSurface.LiesenStrakos.Chapter04.Section03
import NumlibSurface.LiesenStrakos.Chapter04.Section04
import NumlibSurface.LiesenStrakos.Chapter04.Section05
import NumlibSurface.LiesenStrakos.Chapter04.Section06
import NumlibSurface.LiesenStrakos.Chapter04.Section06.Real
import NumlibSurface.LiesenStrakos.Chapter04.Section07
import NumlibSurface.LiesenStrakos.Chapter04.Section08
import NumlibSurface.LiesenStrakos.Chapter04.Section09

/-!
# Liesen and Strakoš, Chapter 4: Short recurrences for generating orthogonal Krylov subspace bases

Chapter 4 of [liesen2013krylov] relates Arnoldi recurrence lengths to the minimal polynomials,
cyclic subspaces, and adjoints of their operators.

## Contents

| Source | Module | Subject |
|---|---|---|
| §4.1 | `Chapter04.Section01` | Error minimization and conjugate gradient-like descent. |
| §4.2 | `Chapter04.Section02` | Vector and subspace minimal polynomials, grades, and Jordan form. |
| §4.3 | `Chapter04.Section03` | Exact Hessenberg bandwidth and optimal recurrence length. |
| §4.4 | `Chapter04.Section04` | Sufficient conditions for optimal short recurrences. |
| §4.5 | `Chapter04.Section05` | Polynomial adjoints and continuity of Arnoldi vectors. |
| §4.6 | `Chapter04.Section06` | Weighted adjoints, eigenbases, and polynomial interpolation. |
| §4.6 | `Chapter04.Section06.Real` | Weighted normality and spectral interpolation for real matrices. |
| §4.7 | `Chapter04.Section07` | Bounds on short recurrences from conjugation interpolation. |
| §4.8 | `Chapter04.Section08` | Isometric Arnoldi, McMillan degree, and generalized Lanczos. |
| §4.9 | `Chapter04.Section09` | Resolvent contour integrals and Riesz projections. |
-/
