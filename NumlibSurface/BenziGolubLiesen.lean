/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenziGolubLiesen.Section01
import NumlibSurface.BenziGolubLiesen.Section03.Solvability
import NumlibSurface.BenziGolubLiesen.Section03.Spectrum
import NumlibSurface.BenziGolubLiesen.Section09
import NumlibSurface.BenziGolubLiesen.Section10.Constraint
import NumlibSurface.BenziGolubLiesen.Section10.Pencil

/-!
# Benzi, Golub and Liesen, *Numerical solution of saddle point problems*

This surface library follows the numbered results of [benzi2005numerical], an Acta Numerica
survey of saddle-point systems and their solvers. Section 1 supplies the coefficient matrix,
Section 3 studies nonsingularity and spectra, Section 9 studies Krylov projection and optimality,
and Section 10 studies constraint preconditioners.

The surface covers the survey's explicitly numbered theorems and lemma, along with the
definitions used in their statements. Standalone equations, applications, and solver
descriptions are included where they support a numbered result.

## Corrections to the published statements

* **After Theorem 3.8.** In the nonreal branch, both roots of each quadratic have real
  part `η / 2`, as the numbered theorem's formulas imply. The prose calls them purely imaginary.
* **Theorem 10.1.** The characteristic polynomial contains a factor `(X - 1)^(2m)` in
  addition to the characteristic polynomial of the reduced pencil. The reduced pencil
  can supply additional roots at 1. The lift of a reduced eigenvector `z` has primal
  component `Z z` in the original coordinates.
* **Lemma 10.2(ii).** At zero, the primal component lies in the kernel of `E` and the
  multiplier is arbitrary. The eigenvector pair must be nonzero.
* **Lemma 10.2(iii).** The upper endpoint is `max 0 (λmax E)`. The scalar case
  `B = C = 1`, `E = -1` has eigenvalue `-1/2`, above the printed upper endpoint `-1`.
-/
