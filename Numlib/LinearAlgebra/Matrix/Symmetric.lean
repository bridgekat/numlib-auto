/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Symmetric`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Congruences of symmetric matrices

A congruence `Xᵀ A X` of a symmetric matrix is symmetric (`Matrix.IsSymm.transpose_mul_mul`), and
so is its row twin `X A Xᵀ` (`Matrix.IsSymm.mul_mul_transpose`), for rectangular `X` over a
commutative semiring: the transpose analogues of Mathlib's
`Matrix.isHermitian_conjTranspose_mul_mul` and `Matrix.isHermitian_mul_mul_conjTranspose`, which
Mathlib's `Symmetric` file lacks.
-/

namespace Matrix

variable {m n α : Type*} [Fintype n] [CommSemiring α] {A : Matrix n n α}

/-- **A congruence of a symmetric matrix is symmetric**: `(Xᵀ A X)ᵀ = Xᵀ Aᵀ X = Xᵀ A X`. -/
theorem IsSymm.transpose_mul_mul (hA : A.IsSymm) (X : Matrix n m α) : (Xᵀ * A * X).IsSymm := by
  rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]

/-- **A congruence of a symmetric matrix is symmetric**, the row twin of
`Matrix.IsSymm.transpose_mul_mul`: `(X A Xᵀ)ᵀ = X Aᵀ Xᵀ = X A Xᵀ`. -/
theorem IsSymm.mul_mul_transpose (hA : A.IsSymm) (X : Matrix m n α) : (X * A * Xᵀ).IsSymm := by
  simpa only [transpose_transpose] using hA.transpose_mul_mul Xᵀ

end Matrix
