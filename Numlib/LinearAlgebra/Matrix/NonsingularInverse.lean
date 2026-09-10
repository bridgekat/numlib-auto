/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The inverse of a nonsingular matrix, acting on vectors

Mathlib's `Matrix.mul_nonsing_inv` and `Matrix.nonsing_inv_mul` cancel a matrix against its inverse
inside a *product of matrices*. This module carries the same cancellation one step further, to the
action `Matrix.mulVec` on vectors: `A *ᵥ (A⁻¹ *ᵥ u) = u` and `A⁻¹ *ᵥ (A *ᵥ u) = u` for an
invertible `A`, and the form in which they are usually wanted, namely that `A⁻¹ *ᵥ u` is *the*
solution of `A *ᵥ v = u`.

Every direct solver and every preconditioned iteration writes a step as `A⁻¹ *ᵥ u` and then needs
to know that applying `A` undoes it; without these lemmas the same
`Matrix.mulVec_mulVec`/`Matrix.mul_nonsing_inv`/`Matrix.one_mulVec` rewrite is repeated at each such
step. Invertibility is stated as `IsUnit A` rather than as `IsUnit A.det`, the two being
interchangeable by `Matrix.isUnit_iff_isUnit_det`.
-/

namespace Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Applying `A` undoes applying `A⁻¹`: `A (A⁻¹ u) = u` for an invertible `A`. -/
theorem mulVec_nonsing_inv_mulVec {A : Matrix n n R} (hA : IsUnit A) (u : n → R) :
    A *ᵥ (A⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]

/-- Applying `A⁻¹` undoes applying `A`: `A⁻¹ (A u) = u` for an invertible `A`. -/
theorem nonsing_inv_mulVec_mulVec {A : Matrix n n R} (hA : IsUnit A) (u : n → R) :
    A⁻¹ *ᵥ (A *ᵥ u) = u := by
  rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]

/-- For an invertible `A`, the vector `A⁻¹ u` is *the* solution of `A v = u`: a `v` that solves the
system is already `A⁻¹ u`. -/
theorem nonsing_inv_mulVec_eq {A : Matrix n n R} (hA : IsUnit A) {u v : n → R} (h : A *ᵥ v = u) :
    A⁻¹ *ᵥ u = v := by
  rw [← h, nonsing_inv_mulVec_mulVec hA]

end Matrix
