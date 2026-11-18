import NumlibSurface.BenziGolubLiesen.Section02.Flow
import NumlibSurface.BenziGolubLiesen.Section02.LeastSquares
import NumlibSurface.BenziGolubLiesen.Section02.InteriorPoint

set_option linter.style.longLine false in
/-!
# Benzi, Golub and Liesen, Section 2: Applications leading to saddle point problems

[benzi2005numerical] derives saddle-point systems from incompressible flow, least
squares, and interior-point optimization. The Stokes Dirichlet energy gives a weak
stationarity equation with pressure as a multiplier. Least-squares minimizers
satisfy augmented systems with a residual variable. In the logarithmic barrier
method, eliminating the slack step gives a smaller saddle-point Newton system.

## Contents

| Source | Module | Subject |
|---|---|---|
| §2.1 Incompressible flow problems | `Section02.Flow` | Stokes energy and rotation form |
| §2.2 Constrained and weighted least squares | `Section02.LeastSquares` | Augmented residual systems |
| §2.3 Saddle point systems from interior point methods | `Section02.InteriorPoint` | Barrier and Newton equations |
-/
