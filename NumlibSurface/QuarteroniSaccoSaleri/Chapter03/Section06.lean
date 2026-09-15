import Numlib.LinearAlgebra.Matrix.FaddeevLeVerrier
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section05

/-!
# Quarteroni–Sacco–Saleri §3.6: computing the inverse of a matrix

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.6, over the backbone `Numlib/Direct/Substitution` (forward and
backward substitution `Matrix.forwardSubst`, `Matrix.backSubst`, the LU solve `Matrix.luSolve`
and its correctness with a row permutation) and
`Numlib/LinearAlgebra/Matrix/FaddeevLeVerrier` (the recurrence `Matrix.faddeevB`,
`Matrix.faddeevAlpha` and the formula `Matrix.faddeevLeverrier_inv` for the inverse).

## Conventions

Those of §3.3 and §3.5: an LU factorization is `Matrix.IsLU A L U` (`L` unit lower triangular,
`U` upper triangular, `L U = A`), a permutation matrix is `σ.permMatrix ℝ`, and the `i`-th vector
of the canonical basis `e_i` is `Pi.single i 1`, so that the `i`-th column of `X = A⁻¹` is
`A⁻¹.col i = A⁻¹ *ᵥ e_i` (`Matrix.mulVec_single_one`). The book's `k = 1, …, n` recurrence is
`0`-based: `B₀ = 1` and the step from `k` to `k + 1` is
`α_{k+1} = tr(A B_k) / (k + 1)`, `B_{k+1} = -A B_k + α_{k+1} I`, so that the book's `B_k`, `α_k`
are `Matrix.faddeevB A k`, `Matrix.faddeevAlpha A k` and its terminal index `n` is
`Fintype.card (Fin n) = n`.

## Contents

* `inv_col_eq_luSolve` — the `2n` triangular systems `L y_i = P e_i`, `U x_i = y_i` and their
  solution, the `i`-th column of `A⁻¹`.
* `inv_col_partialPivoting` — the same with the factors produced by GEM with partial pivoting,
  the `P A = L U` of (3.52).
* `faddeevLeverrier` — the Faddeev–LeVerrier recurrence, `B_n = 0` and `A⁻¹ = B_{n-1} / α_n`.

The operation counts (`(n - 1) n³` flops for the Faddeev–LeVerrier route) and the remark that
inverting a matrix can be less stable than GEM are prose.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### The inverse through the LU factorization -/

/-- **§3.6, the `2n` triangular systems.** Let `A ∈ ℝ^{n×n}` be nonsingular and let `P A = L U`
with `P` a permutation matrix and `U` with no zero pivot. Denoting by `X = A⁻¹` the inverse, the
column vectors of `X` are the solutions of `A x_i = e_i`, and they are obtained by solving the
`2n` triangular systems

`L y_i = P e_i`, `U x_i = y_i`, `i = 1, …, n`,

a succession of systems with the same coefficient matrices and different right-hand sides
(backbone `Matrix.forwardSubst`, `Matrix.backSubst`, `Matrix.mulVec_luSolve_permMatrix`). -/
theorem inv_col_eq_luSolve {A L U : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    {σ : Equiv.Perm (Fin n)} (h : IsLU (σ.permMatrix ℝ * A) L U) (hd : ∀ i, U i i ≠ 0)
    (i : Fin n) :
    A *ᵥ A⁻¹.col i = Pi.single i 1 ∧
      L *ᵥ forwardSubst L (σ.permMatrix ℝ *ᵥ Pi.single i 1) = σ.permMatrix ℝ *ᵥ Pi.single i 1 ∧
      U *ᵥ luSolve L U (σ.permMatrix ℝ *ᵥ Pi.single i 1) =
        forwardSubst L (σ.permMatrix ℝ *ᵥ Pi.single i 1) ∧
      luSolve L U (σ.permMatrix ℝ *ᵥ Pi.single i 1) = A⁻¹.col i := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  have hcol : A *ᵥ A⁻¹.col i = Pi.single i 1 := by
    rw [← mulVec_single_one, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  refine ⟨hcol, mulVec_forwardSubst _ h.isUnitLowerTriangular.isLowerTriangular
      (fun j => by rw [h.isUnitLowerTriangular.diag_eq_one]; exact one_ne_zero),
    mulVec_backSubst _ h.isUpperTriangular hd, ?_⟩
  refine mulVec_injective_iff_isUnit.2 hA ?_
  rw [mulVec_luSolve_permMatrix _ h hd, hcol]

/-- **§3.6 with partial pivoting.** The factorization used in practice is the one (3.52) produces:
`P A = L U` with `P` the permutation matrix of GEM with partial pivoting, `L` the matrix of the
multipliers and `U` the last stage of the elimination. The columns of `A⁻¹` are then the
`luSolve L U (P e_i)`. -/
theorem inv_col_partialPivoting {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (i : Fin n) :
    luSolve (gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A))
      (gemPivotStage A partialPivotRow n).1
      ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ *ᵥ Pi.single i 1) = A⁻¹.col i := by
  have hLU := (equation_3_52 A hA).1
  refine (inv_col_eq_luSolve hA hLU (fun j => ?_) i).2.2.2
  have hdet : ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero
      (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 (isUnit_permMatrix _)))
      (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det A).1 hA))
  rw [hLU.det_eq_prod_diag, Finset.prod_ne_zero_iff] at hdet
  exact hdet j (mem_univ j)

/-! ### The Faddeev–LeVerrier formula -/

/-- **§3.6, the Faddeev or Leverrier formula.** Letting `B₀ = I`, the recurrence

`α_k = tr(A B_{k-1}) / k`, `B_k = -A B_{k-1} + α_k I`, `k = 1, 2, …, n`,

satisfies `B_n = 0`, and if `α_n ≠ 0` — that is, if `A` is nonsingular, `α_n` being `det A` —
then `A⁻¹ = B_{n-1} / α_n` (backbone `Matrix.faddeevB`, `Matrix.faddeevAlpha`,
`Matrix.faddeevB_card_eq_zero`, `Matrix.faddeevLeverrier_inv`; `B_n = 0` is the Cayley–Hamilton
theorem and the `α_k` are, up to sign, the coefficients of the characteristic polynomial). -/
theorem faddeevLeverrier (A : Matrix (Fin n) (Fin n) ℝ) :
    faddeevB A 0 = 1 ∧
      (∀ k : ℕ, faddeevAlpha A (k + 1) = trace (A * faddeevB A k) / (k + 1)) ∧
      (∀ k : ℕ, faddeevB A (k + 1) = -(A * faddeevB A k) + faddeevAlpha A (k + 1) • 1) ∧
      faddeevAlpha A n = A.det ∧
      faddeevB A n = 0 ∧
      (faddeevAlpha A n ≠ 0 → A⁻¹ = (faddeevAlpha A n)⁻¹ • faddeevB A (n - 1)) := by
  have hdet := faddeevAlpha_card_eq_det A
  have hzero := faddeevB_card_eq_zero A
  have hinv := fun h => faddeevLeverrier_inv A h
  simp only [Fintype.card_fin] at hdet hzero hinv
  exact ⟨faddeevB_zero A, faddeevAlpha_succ A, fun k => by rw [faddeevB_succ]; abel, hdet, hzero,
    hinv⟩

end QuarteroniSaccoSaleri.Chapter03
