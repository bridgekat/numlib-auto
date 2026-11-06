/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Block
import Mathlib.Basic.Real.Basic

/-!
# Benzi, Golub and Liesen, Section 1

The coefficient matrix of the generalized saddle-point system.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*}

/-- The coefficient matrix in equation (1.1) of [benzi2005numerical]. -/
abbrev saddlePointMatrix (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ) (C : Matrix m m ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks A B₁ᵀ B₂ (-C)

end BenziGolubLiesen
