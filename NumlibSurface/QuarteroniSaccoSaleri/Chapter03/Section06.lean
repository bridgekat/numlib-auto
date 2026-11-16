/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.FaddeevLeVerrier
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section05

/-!
# Quarteroni, Sacco and Saleri, Section 3.6: Computing the inverse of a matrix

This module formalizes Section 3.6 of [quarteroni2000numerical]. The inverse $X = A^{-1}$ of a
nonsingular matrix $A \in \mathbb{R}^{n \times n}$ has as columns the solutions $x_i$ of
$Ax_i = e_i$. With a factorization $PA = LU$, they are found by solving the $2n$ triangular systems
$Ly_i = Pe_i$ and $Ux_i = y_i$, $i = 1, \ldots, n$. The module also states the Faddeev–LeVerrier
formula, which computes $A^{-1}$ from the recurrence $B_k = -AB_{k-1} + \alpha_k I$,
$\alpha_k = \operatorname{tr}(AB_{k-1})/k$.

The proofs specialize the backbone modules `Numlib.Direct.Substitution` (forward and backward
substitution `Matrix.forwardSubst` and `Matrix.backSubst`, the solve `Matrix.luSolve` and its
correctness with a row permutation) and `Numlib.LinearAlgebra.Matrix.FaddeevLeVerrier` (the
recurrence `Matrix.faddeevB`, `Matrix.faddeevAlpha` and the formula `Matrix.faddeevLeverrier_inv`
for the inverse).

## Main results

* Section 3.6, `QuarteroniSaccoSaleri.Chapter03.inv_col_eq_luSolve`: the columns of $A^{-1}$ are the
  solutions of the triangular systems $Ly_i = Pe_i$, $Ux_i = y_i$.
* Section 3.6, `QuarteroniSaccoSaleri.Chapter03.inv_col_partialPivoting`: the same with the factors
  of GEM with partial pivoting.
* Section 3.6, `QuarteroniSaccoSaleri.Chapter03.faddeevLeverrier`: the Faddeev–LeVerrier recurrence
  gives $B_n = 0$ and $A^{-1} = B_{n-1}/\alpha_n$.

## Conventions

* As in Sections 3.3 and 3.5, an LU factorization is `Matrix.IsLU A L U`, and a permutation matrix
  is `σ.permMatrix ℝ`.
* The $i$-th vector $e_i$ of the canonical basis is `Pi.single i 1`. The $i$-th column of $A^{-1}$
  is `A⁻¹.col i`, which equals `A⁻¹ *ᵥ Pi.single i 1` (`Matrix.mulVec_single_one`).
* The recurrence is $0$-based: $B_0 = I$, and the step from $k$ to $k + 1$ is
  $\alpha_{k+1} = \operatorname{tr}(AB_k)/(k + 1)$, $B_{k+1} = -AB_k + \alpha_{k+1} I$. The book's
  $B_k$ and $\alpha_k$ are `Matrix.faddeevB A k` and `Matrix.faddeevAlpha A k`, and its last index
  $n$ is `Fintype.card (Fin n) = n`.

## Not formalized

* **The operation counts**, among them the $(n - 1)n^3$ flops of the Faddeev–LeVerrier formula.
* **The remark** that computing the inverse can be less stable than GEM.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### The inverse through the LU factorization -/

/-- **Section 3.6** of [quarteroni2000numerical], the $2n$ triangular systems. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $P$ be a permutation matrix, and let
$PA = LU$ be an LU factorization in which $U$ has nonzero diagonal entries. Let $x_i$ be the
$i$-th column of $X = A^{-1}$. Then $Ax_i = e_i$, and $x_i$ is obtained by solving the two
triangular systems
$$Ly_i = Pe_i, \qquad Ux_i = y_i,$$
the first by forward substitution and the second by backward substitution. The $2n$ systems, for
$i = 1, \ldots, n$, have the same coefficient matrices and different right-hand sides.

The vector $y_i$ is `forwardSubst L (σ.permMatrix ℝ *ᵥ Pi.single i 1)`, and the computed $x_i$
is `luSolve L U (σ.permMatrix ℝ *ᵥ Pi.single i 1)` (see `Matrix.forwardSubst` and
`Matrix.luSolve`). The proof uses `Matrix.mulVec_luSolve_permMatrix`. -/
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

/-- **Section 3.6** of [quarteroni2000numerical], with partial pivoting. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, and let $PA = LU$ be the factorization (3.52)
that GEM with partial pivoting produces: $P$ is the accumulated permutation matrix, $L$ is the
matrix of the multipliers and $U$ is the last stage of the elimination. Then for every $i$,
solving $Ly_i = Pe_i$ and $Ux_i = y_i$ gives the $i$-th column $x_i$ of $A^{-1}$. -/
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

/-- **Section 3.6** of [quarteroni2000numerical], the Faddeev or Leverrier formula. Let
$A \in \mathbb{R}^{n \times n}$, let $B_0 = I$, and let
$$\alpha_k = \frac{\operatorname{tr}(AB_{k-1})}{k}, \qquad B_k = -AB_{k-1} + \alpha_k I, \qquad
  k = 1, 2, \ldots.$$
Then $\alpha_n = \det A$ and $B_n = 0$. If $\alpha_n \neq 0$, that is, if $A$ is nonsingular,
then
$$A^{-1} = \frac{1}{\alpha_n} B_{n-1}.$$

The identity $B_n = 0$ is the Cayley–Hamilton theorem, and the $\alpha_k$ are, up to sign, the
coefficients of the characteristic polynomial. The proof uses `Matrix.faddeevB_card_eq_zero` and
`Matrix.faddeevLeverrier_inv`. -/
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
