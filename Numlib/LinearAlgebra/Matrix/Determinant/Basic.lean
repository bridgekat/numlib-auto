/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, beside `Matrix.det_succ_row`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The continuant step of a bordered determinant

`Matrix.det_succ_succ_of_last_row_col`: when the last row and the last column of `M` vanish outside
their last two entries — a tridiagonal matrix, or any matrix bordered in that shape — `det M` is
`m_{NN} det M' - m_{N,N-1} m_{N-1,N} det M''` in terms of the two leading principal minors. It is
the three-term recurrence of the characteristic polynomials of Jacobi matrices.
-/

namespace Matrix

/-- **The continuant step**: the determinant of a matrix whose last row and last column vanish
outside their last two entries is `m_{NN} det M' - m_{N,N-1} m_{N-1,N} det M''`, `M'` and `M''`
the leading principal submatrices of orders `n + 1` and `n`. Laplace expansion along the last
row, then along the last column of the off-diagonal minor. -/
theorem det_succ_succ_of_last_row_col {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (hrow : ∀ i : Fin n, M (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc i)) = 0)
    (hcol : ∀ i : Fin n, M (Fin.castSucc (Fin.castSucc i)) (Fin.last (n + 1)) = 0) :
    M.det = M (Fin.last (n + 1)) (Fin.last (n + 1)) *
        (M.submatrix Fin.castSucc Fin.castSucc).det -
      M (Fin.last (n + 1)) (Fin.castSucc (Fin.last n)) *
        M (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)) *
        (M.submatrix (Fin.castSucc ∘ Fin.castSucc) (Fin.castSucc ∘ Fin.castSucc)).det := by
  rw [Matrix.det_succ_row M (Fin.last (n + 1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hrow, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last]
  have hsign1 : ((-1 : R) ^ ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]; simp
  have hsign2 : ((-1 : R) ^ ((Fin.last (n + 1) : ℕ) + (Fin.castSucc (Fin.last n) : ℕ))) = -1 := by
    rw [Fin.val_last, Fin.val_castSucc, Fin.val_last, show n + 1 + n = 2 * n + 1 by ring,
      pow_succ, pow_mul]
    simp
  rw [hsign1, hsign2, one_mul]
  -- expand the off-diagonal minor along its last column
  rw [Matrix.det_succ_column (M.submatrix Fin.castSucc (Fin.castSucc (Fin.last n)).succAbove)
    (Fin.last n), Fin.sum_univ_castSucc]
  simp only [Matrix.submatrix_apply, Fin.succAbove_castSucc_self, Fin.succ_last, hcol, mul_zero,
    zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last, Matrix.submatrix_submatrix]
  have hsign3 : ((-1 : R) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]; simp
  rw [hsign3, one_mul]
  have hsub : ((Fin.castSucc (Fin.last n)).succAbove ∘ Fin.castSucc : Fin n → Fin (n + 2)) =
      Fin.castSucc ∘ Fin.castSucc := by
    funext i
    simp only [Function.comp_apply]
    exact Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last i)
  rw [hsub]
  ring

end Matrix
