/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, beside `Matrix.det_succ_row`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The continuant step of a bordered determinant

Let $M$ be a square matrix of order $N$ over a commutative ring, and assume that the last row and
the last column of $M$ are zero outside their last two entries. This holds for a tridiagonal matrix,
and for any matrix bordered in that shape. Then
$$\det M = m_{NN} \det M' - m_{N,N-1} \, m_{N-1,N} \det M'',$$
where $M'$ and $M''$ are the leading principal submatrices of orders $N - 1$ and $N - 2$. This is
the three-term recurrence of the characteristic polynomials of Jacobi matrices.

## Main results

* `Matrix.det_succ_succ_of_last_row_col`: the continuant step $\det M = m_{NN} \det M' - m_{N,N-1}
  m_{N-1,N} \det M''$.
-/

namespace Matrix

/-- **The continuant step**. Let $R$ be a commutative ring, let $N = n + 2$, and let
$M \in R^{N \times N}$. Assume that the last row and the last column of $M$ are zero outside
their last two entries: $m_{Ni} = 0$ and $m_{iN} = 0$ for $i \le n$. Then
$$\det M = m_{NN} \det M' - m_{N,N-1} \, m_{N-1,N} \det M'',$$
where $M'$ and $M''$ are the leading principal submatrices of orders $n + 1$ and $n$.

The indices in the statement start at $1$; in Lean they are `Fin (n + 2)`, starting at $0$, and
$N$ is `Fin.last (n + 1)`. The proof is a Laplace expansion along the last row, followed by an
expansion of the off-diagonal minor along its last column. -/
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
