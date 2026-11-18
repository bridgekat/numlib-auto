/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Matrices and linear transformations

Section 0.2 of [benIsrael2003generalized] introduces the coordinate conventions
for rectangular matrices and their selected rows and columns.
-/

namespace BenIsraelGreville.Chapter00

/-- **Section 0.2.1** of [benIsrael2003generalized]. An element of $Q_{k,n}$
is an increasing sequence of $k$ indices among $n$. -/
abbrev IndexSequence (k n : ℕ) := Fin k ↪o Fin n

/-- **Section 0.2.1** of [benIsrael2003generalized]. Select the rows and columns
of a matrix in increasing order. -/
abbrev submatrix {K : Type*} {m n r c : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (rows : IndexSequence r m) (cols : IndexSequence c n) : Matrix (Fin r) (Fin c) K :=
  A.submatrix rows cols

/-- A rectangular diagonal matrix vanishes away from its main diagonal. -/
def IsRectDiagonal {K : Type*} [Zero K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) : Prop :=
  ∀ i j, i.val ≠ j.val → A i j = 0

/-- A rectangular upper triangular matrix vanishes below the main diagonal. -/
def IsRectUpperTriangular {K : Type*} [Zero K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) : Prop :=
  ∀ i j, j.val < i.val → A i j = 0

/-- A rectangular lower triangular matrix vanishes above the main diagonal. -/
def IsRectLowerTriangular {K : Type*} [Zero K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) : Prop :=
  ∀ i j, i.val < j.val → A i j = 0

end BenIsraelGreville.Chapter00
