/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Symmetric`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Congruences of symmetric matrices

Let $A$ be a symmetric $n \times n$ matrix over a commutative semiring, and let $X$ be a rectangular
matrix. This file proves that the congruences $X^T A X$ and $X A X^T$ are again symmetric.

## Main results

* `Matrix.IsSymm.transpose_mul_mul`: if $A$ is symmetric, then $X^T A X$ is symmetric.
* `Matrix.IsSymm.mul_mul_transpose`: if $A$ is symmetric, then $X A X^T$ is symmetric.

## Implementation notes

* The two results are the transpose analogues of Mathlib's
  `Matrix.isHermitian_conjTranspose_mul_mul` and `Matrix.isHermitian_mul_mul_conjTranspose`. The
  Mathlib module `Mathlib.LinearAlgebra.Matrix.Symmetric` does not contain them.
-/

namespace Matrix

variable {m n α : Type*} [Fintype n] [CommSemiring α] {A : Matrix n n α}

/-- Let $A$ be a symmetric $n \times n$ matrix over a commutative semiring, and let $X$ be an
$n \times m$ matrix. Then the **congruence** $X^T A X$ is symmetric:
$$(X^T A X)^T = X^T A^T X = X^T A X.$$
-/
theorem IsSymm.transpose_mul_mul (hA : A.IsSymm) (X : Matrix n m α) : (Xᵀ * A * X).IsSymm := by
  rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]

/-- Let $A$ be a symmetric $n \times n$ matrix over a commutative semiring, and let $X$ be an
$m \times n$ matrix. Then $X A X^T$ is symmetric:
$$(X A X^T)^T = X A^T X^T = X A X^T.$$

This is the row form of `Matrix.IsSymm.transpose_mul_mul`. -/
theorem IsSymm.mul_mul_transpose (hA : A.IsSymm) (X : Matrix m n α) : (X * A * Xᵀ).IsSymm := by
  simpa only [transpose_transpose] using hA.transpose_mul_mul Xᵀ

end Matrix
