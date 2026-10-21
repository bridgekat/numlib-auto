/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.DotProduct`, beside
`Matrix.conjTranspose_mul_self_eq_zero`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# A column with vanishing Gram diagonal entry

`Matrix.apply_eq_zero_of_conjTranspose_mul_self_apply_self_eq_zero`: over a star-ordered ring
without zero divisors, if the diagonal entry `(Aᴴ A)_jj = ∑ₖ |a_kj|²` vanishes then column `j` of
`A` is zero. It is the entrywise form of Mathlib's `Matrix.conjTranspose_mul_self_eq_zero`.
-/

namespace Matrix

variable {m n R : Type*} [Fintype m] [PartialOrder R] [NonUnitalRing R] [StarRing R]
  [StarOrderedRing R] [NoZeroDivisors R]

/-- A column of a matrix whose Gram diagonal entry vanishes is zero. -/
theorem apply_eq_zero_of_conjTranspose_mul_self_apply_self_eq_zero {A : Matrix m n R} {j : n}
    (h : (Aᴴ * A) j j = 0) (k : m) : A k j = 0 := by
  have h0 : star (fun k => A k j) ⬝ᵥ (fun k => A k j) = 0 := by
    rw [← h, mul_apply]
    rfl
  exact congrFun (dotProduct_star_self_eq_zero.1 h0) k

end Matrix
