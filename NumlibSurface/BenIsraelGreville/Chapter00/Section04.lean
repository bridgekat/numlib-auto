/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Hermite normal form and rank factorization

Section 0.4 of [benIsrael2003generalized] uses a complex matrix
to illustrate elimination and rank factorization.
-/

namespace BenIsraelGreville.Chapter00

/-- **Equation (80)** of [benIsrael2003generalized], Chapter 0. The example matrix
for Gaussian elimination, also used in Chapter 2 for a prescribed inverse. -/
def hermiteExampleMatrix : Matrix (Fin 3) (Fin 6) ℂ :=
  !![0, 2 * Complex.I, Complex.I, 0, 4 + 2 * Complex.I, 1;
    0, 0, 0, -3, -6, -3 - 3 * Complex.I;
    0, 2, 1, 1, 4 - 4 * Complex.I, 1]

end BenIsraelGreville.Chapter00
