/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Algebra.Group.Drazin
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# Spectral inverse equations

Section 4.1 of [benIsrael2003generalized] adds power equations for square matrices to
the four Penrose equations. The exponents used for these equations in the book are positive.
-/

namespace BenIsraelGreville.Chapter04

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equation $(1^k)$** of [benIsrael2003generalized], Chapter 4. The first power
equation is $A^k X A = A^k$. -/
def SatisfiesFirstPowerEquation (k : ℕ) (A X : Matrix n n ℂ) : Prop :=
  A ^ k * X * A = A ^ k

/-- **Equation $(5^k)$** of [benIsrael2003generalized], Chapter 4. The fifth power
equation is $A^k X = X A^k$. -/
abbrev SatisfiesFifthPowerEquation (k : ℕ) (A X : Matrix n n ℂ) : Prop :=
  Commute (A ^ k) X

/-- **Equation $(6^k)$** of [benIsrael2003generalized], Chapter 4. The sixth power
equation is $A X^k = X^k A$. -/
abbrev SatisfiesSixthPowerEquation (k : ℕ) (A X : Matrix n n ℂ) : Prop :=
  Commute A (X ^ k)

end BenIsraelGreville.Chapter04
