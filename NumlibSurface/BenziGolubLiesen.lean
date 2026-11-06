/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenziGolubLiesen.Section01
import NumlibSurface.BenziGolubLiesen.Section03.Solvability
import NumlibSurface.BenziGolubLiesen.Section09

/-!
# Benzi, Golub and Liesen, *Numerical solution of saddle point problems*

This surface library follows the numbered results of [benzi2005numerical], an Acta Numerica
survey of saddle-point systems and their solvers. Section 1 supplies the coefficient matrix,
Section 3 studies nonsingularity and spectra, Section 9 studies Krylov projection and optimality,
and Section 10 studies constraint preconditioners.

The coverage targets the survey's explicitly numbered theorems and lemma, along with the
definitions used in their statements. Standalone equation numbers, applications, and solver
descriptions outside those results are outside this scope.
-/
