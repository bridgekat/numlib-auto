/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Block`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Block multiplication and block triangular products

Three facts about how products of matrices see a partition of their indices into blocks, the
general rules behind the triangular, banded and trapezoidal shapes of
`Numlib/LinearAlgebra/Matrix/Triangular` and `Numlib/LinearAlgebra/Matrix/Band`.

## Main results

* `Matrix.mul_submatrix_sigmaMk_eq_sum`: **block multiplication** with blocks of arbitrary sizes.
  For `A : Matrix (Σ a, m a) (Σ c, p c) R` and `B : Matrix (Σ c, p c) (Σ b, n b) R`, the `(a, b)`
  block of `A * B` is `∑ c, A_{ac} B_{cb}` ([golub2013matrix] Theorem 1.3.1). Mathlib has the
  `2 × 2` case `Matrix.fromBlocks_multiply`, the block diagonal case `Matrix.blockDiagonal'_mul`
  and the case of uniform square blocks `Matrix.compRingEquiv`, but not the general statement.
* `Matrix.BlockTriangular.mul_apply_self_of_injective`: the diagonal of a product of two block
  triangular matrices with singleton blocks is the product of the diagonals; its instances are the
  triangular statements `Matrix.IsUpperTriangular.mul_apply_self` and
  `Matrix.IsLowerTriangular.mul_apply_self`.
* `Matrix.mul_apply_eq_zero_of_lt`: **the rectangular product rule**, the form of
  `Matrix.BlockTriangular.mul` with a block map on each of the three index types, behind the
  trapezoidal shapes of rectangular factorizations.

## References

* [golub2013matrix] §1.3.
-/

namespace Matrix

/-! ### Block multiplication over a `Sigma` index -/

section Sigma

variable {ι α β R : Type*} [Fintype ι] {m : α → Type*} {p : ι → Type*} {n : β → Type*}
  [∀ c, Fintype (p c)] [NonUnitalNonAssocSemiring R]

/-- **Block multiplication** ([golub2013matrix] Theorem 1.3.1): the `(a, b)` block of `A * B` is
`∑ c, A_{ac} B_{cb}`, for blocks of arbitrary sizes indexed by `Sigma` types. -/
theorem mul_submatrix_sigmaMk_eq_sum (A : Matrix (Σ a, m a) (Σ c, p c) R)
    (B : Matrix (Σ c, p c) (Σ b, n b) R) (a : α) (b : β) :
    (A * B).submatrix (Sigma.mk a) (Sigma.mk b) =
      ∑ c, A.submatrix (Sigma.mk a) (Sigma.mk c) * B.submatrix (Sigma.mk c) (Sigma.mk b) := by
  ext i j
  simp [mul_apply, Fintype.sum_sigma, sum_apply]

end Sigma

/-! ### Diagonals of block triangular products -/

section Diag

variable {n R α : Type*} [LinearOrder α] {b : n → α} [Fintype n] [NonUnitalNonAssocSemiring R]

/-- The diagonal of a product of two block triangular matrices with singleton blocks is the
product of the diagonals: in `∑ k, M i k * N k i` every term with `k ≠ i` has `b k ≠ b i`, and one
of the two factors then vanishes. -/
theorem BlockTriangular.mul_apply_self_of_injective {M N : Matrix n n R}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (hb : Function.Injective b) (i : n) :
    (M * N) i i = M i i * N i i := by
  rw [mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne (hb.ne hk) with h | h
  · rw [hM h, zero_mul]
  · rw [hN h, mul_zero]

end Diag

/-! ### The rectangular product rule -/

section Rectangular

/-- **The rectangular product rule** behind the trapezoidal shapes, the rectangular form of
`Matrix.BlockTriangular.mul` with a block map on each of the three index types: if `A i k = 0`
whenever `c k < b i` and `B k j = 0` whenever `d j < c k`, then `(A * B) i j = 0` whenever
`d j < b i`, because every term `A i k * B k j` of the product has `c k < b i` or
`d j < b i ≤ c k`. -/
theorem mul_apply_eq_zero_of_lt {α l m n R : Type*} [LinearOrder α] [Fintype m]
    [NonUnitalNonAssocSemiring R] {b : l → α} {c : m → α} {d : n → α} {A : Matrix l m R}
    {B : Matrix m n R} (hA : ∀ i k, c k < b i → A i k = 0) (hB : ∀ k j, d j < c k → B k j = 0)
    {i : l} {j : n} (hij : d j < b i) : (A * B) i j = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (c k) (b i) with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k j (hij.trans_le h), mul_zero]

end Rectangular

end Matrix
