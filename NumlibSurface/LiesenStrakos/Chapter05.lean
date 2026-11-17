/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.LiesenStrakos.Chapter05.Section01
import NumlibSurface.LiesenStrakos.Chapter05.Section04
import NumlibSurface.LiesenStrakos.Chapter05.Section05
import NumlibSurface.LiesenStrakos.Chapter05.Section06
import NumlibSurface.LiesenStrakos.Chapter05.Section06.ActiveSpectrum
import NumlibSurface.LiesenStrakos.Chapter05.Section07
import NumlibSurface.LiesenStrakos.Chapter05.Section07.BlockBound
import NumlibSurface.LiesenStrakos.Chapter05.Section07.CurveClassification
import NumlibSurface.LiesenStrakos.Chapter05.Section07.PrescribedCurve
import NumlibSurface.LiesenStrakos.Chapter05.Section07.Sharpness
import NumlibSurface.LiesenStrakos.Chapter05.Section08
import NumlibSurface.LiesenStrakos.Chapter05.Section09
import NumlibSurface.LiesenStrakos.Chapter05.Section10

/-!
# Liesen and Strakoš, Chapter 5: Cost of computations using Krylov subspace methods

Chapter 5 of [liesen2013krylov] relates accuracy and computational effort to the behaviour of
stationary and Krylov iterations. The formalized results address Chebyshev semi-iteration,
the exact errors of conjugate gradients, GMRES residuals, and backward error.

## Contents

| Source | Module | Subject |
|---|---|---|
| §5.1 | `Chapter05.Section01` | Galerkin error and backward errors |
| §5.4 | `Chapter05.Section04` | Strong optimality with respect to a tolerance |
| §5.5 | `Chapter05.Section05` | Stationary iteration, Richardson, and Chebyshev semi-iteration |
| §5.6 | `Chapter05.Section06` | Energy and Euclidean error identities for CG |
| §5.7 | `Chapter05.Section07` | Ritz and harmonic Ritz pairs, polynomial residual bounds |
| §5.8 | `Chapter05.Section08` | Normwise backward error and the relative forward error bound |
| §5.9 | `Chapter05.Section09` | Spectral deflation and the exact CG iteration limit |
| §5.10 | `Chapter05.Section10` | Arnoldi and orthogonality defects |

## Not formalized

* The numerical experiments and the perturbation estimates for finite-precision CG and GMRES
  are outside the current coverage.
-/
