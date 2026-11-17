/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Triangular factors for prescribed GMRES curves

For a companion matrix $C$ with last-column coefficients, the constrained
triangular factor $T$ can be replaced by $Y=TC^{-1}$ with a fixed first column
and an unconstrained upper triangular block.
-/

open Matrix
open scoped Matrix

namespace Krylov

variable {𝕜 : Type*} [Field 𝕜] {n : ℕ}

/-- The block factor $[h,\binom{R}{0}]$. Its first column is $h$ and its
other columns form $R$ with a zero row appended. -/
def gmresCompanionBlock (h : Fin (n + 1) → 𝕜) (R : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  Matrix.of fun i => Fin.cons (h i) (fun j => Fin.lastCases 0 (fun k => R k j) i)

/-- The first column of the GMRES companion block is the prescribed vector. -/
@[simp] theorem gmresCompanionBlock_zero (h : Fin (n + 1) → 𝕜)
    (R : Matrix (Fin n) (Fin n) 𝕜) (i : Fin (n + 1)) :
    gmresCompanionBlock h R i 0 = h i := rfl

/-- The upper entries of the remaining columns are the entries of the triangular factor. -/
@[simp] theorem gmresCompanionBlock_castSucc_succ (h : Fin (n + 1) → 𝕜)
    (R : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n) :
    gmresCompanionBlock h R i.castSucc j.succ = R i j := by
  simp [gmresCompanionBlock]

/-- The last row vanishes in every column after the first. -/
@[simp] theorem gmresCompanionBlock_last_succ (h : Fin (n + 1) → 𝕜)
    (R : Matrix (Fin n) (Fin n) 𝕜) (j : Fin n) :
    gmresCompanionBlock h R (Fin.last n) j.succ = 0 := by
  simp [gmresCompanionBlock]

variable {C : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}

private theorem mul_castSucc_of_shift
    (hC : ∀ (i : Fin (n + 1)) (j : Fin n), C i j.castSucc = if i = j.succ then 1 else 0)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i : Fin (n + 1)) (j : Fin n) :
    (Y * C) i j.castSucc = Y i j.succ := by
  rw [Matrix.mul_apply]
  simp only [hC, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private theorem zero_last_ne_zero_of_shift (hCu : IsUnit C)
    (hC : ∀ (i : Fin (n + 1)) (j : Fin n), C i j.castSucc = if i = j.succ then 1 else 0) :
    C 0 (Fin.last n) ≠ 0 := by
  intro hz
  apply ((Matrix.isUnit_iff_isUnit_det C).mp hCu).ne_zero
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  induction j using Fin.lastCases with
  | last => exact hz
  | cast j => simp [hC, Ne.symm (Fin.succ_ne_zero j)]

private theorem block_mul_companion_isUpperTriangular
    (hC : ∀ (i : Fin (n + 1)) (j : Fin n), C i j.castSucc = if i = j.succ then 1 else 0)
    (h : Fin (n + 1) → 𝕜) {R : Matrix (Fin n) (Fin n) 𝕜}
    (hR : R.IsUpperTriangular) :
    (gmresCompanionBlock h R * C).IsUpperTriangular := by
  intro i j hji
  induction j using Fin.lastCases with
  | last => exact (not_lt_of_ge (Fin.le_last i) hji).elim
  | cast j =>
    rw [mul_castSucc_of_shift hC]
    induction i using Fin.lastCases with
    | last => simp
    | cast i =>
      rw [gmresCompanionBlock_castSucc_succ]
      exact hR hji

private theorem block_mul_companion_isUnit (hCu : IsUnit C)
    (hC : ∀ (i : Fin (n + 1)) (j : Fin n), C i j.castSucc = if i = j.succ then 1 else 0)
    {h : Fin (n + 1) → 𝕜} (hh : h (Fin.last n) ≠ 0) {R : Matrix (Fin n) (Fin n) 𝕜}
    (hRt : R.IsUpperTriangular) (hRu : IsUnit R) :
    IsUnit (gmresCompanionBlock h R * C) := by
  let T := gmresCompanionBlock h R * C
  have hTt : T.IsUpperTriangular := block_mul_companion_isUpperTriangular hC h hRt
  have hRd := hRt.det_ne_zero_iff.mp ((Matrix.isUnit_iff_isUnit_det R).mp hRu).ne_zero
  apply (Matrix.isUnit_iff_isUnit_det T).2
  apply isUnit_iff_ne_zero.2
  apply hTt.det_ne_zero_iff.2
  intro i
  change T i i ≠ 0
  induction i using Fin.lastCases with
  | last =>
    dsimp only [T]
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simpa using mul_ne_zero hh (zero_last_ne_zero_of_shift hCu hC)
  | cast i =>
    dsimp only [T]
    rw [mul_castSucc_of_shift hC, gmresCompanionBlock_castSucc_succ]
    exact hRd i

private theorem companion_conjugate_mul_right (hCu : IsUnit C)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) :
    (Y * C) * C * (Y * C)⁻¹ = Y * C * Y⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_assoc (Y * C), ← Matrix.mul_assoc C,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det C).mp hCu), Matrix.one_mul]

/-- Let $C$ be a nonsingular companion matrix with last-column coefficients
and $Cs=e_0$. If the last component of $h$ is nonzero, the similarities
$TCT^{-1}$ with nonsingular upper triangular $T$ constrained by $Ts=h$
are exactly $YCY^{-1}$ with $Y=[h,\binom{R}{0}]$ and nonsingular upper
triangular $R$. The factors are related by $Y=TC^{-1}$. -/
theorem gmres_companion_factor_iff (hCu : IsUnit C)
    (hC : ∀ (i : Fin (n + 1)) (j : Fin n), C i j.castSucc = if i = j.succ then 1 else 0)
    {s h : Fin (n + 1) → 𝕜} (hs : C *ᵥ s = Pi.single 0 1)
    (hh : h (Fin.last n) ≠ 0) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) :
    (∃ T : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜,
      T.IsUpperTriangular ∧ IsUnit T ∧ T *ᵥ s = h ∧ A = T * C * T⁻¹) ↔
    (∃ R : Matrix (Fin n) (Fin n) 𝕜,
      R.IsUpperTriangular ∧ IsUnit R ∧
        A = gmresCompanionBlock h R * C * (gmresCompanionBlock h R)⁻¹) := by
  have hCd := (Matrix.isUnit_iff_isUnit_det C).mp hCu
  constructor
  · rintro ⟨T, hTt, hTu, hTs, hA⟩
    let R := T.submatrix Fin.castSucc Fin.castSucc
    have hRt : R.IsUpperTriangular := fun _ _ hij => hTt hij
    have hTd := hTt.det_ne_zero_iff.mp ((Matrix.isUnit_iff_isUnit_det T).mp hTu).ne_zero
    have hRu : IsUnit R :=
      (Matrix.isUnit_iff_isUnit_det R).2
        (isUnit_iff_ne_zero.2 (hRt.det_ne_zero_iff.2 fun i => hTd i.castSucc))
    let Y := T * C⁻¹
    have hYC : Y * C = T := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCd, Matrix.mul_one]
    have hY : Y = gmresCompanionBlock h R := by
      ext i j
      induction j using Fin.cases with
      | zero =>
        rw [gmresCompanionBlock_zero]
        have hv : Y *ᵥ Pi.single 0 1 = h := by
          rw [← hs, mulVec_mulVec, hYC, hTs]
        simpa only [mulVec_single_one, col_apply] using congrFun hv i
      | succ j =>
        rw [← mul_castSucc_of_shift hC Y i j, hYC]
        induction i using Fin.lastCases with
        | last =>
          rw [gmresCompanionBlock_last_succ]
          exact hTt (Fin.castSucc_lt_last j)
        | cast i => exact (gmresCompanionBlock_castSucc_succ h R i j).symm
    exact ⟨R, hRt, hRu, by rw [hA, ← hYC, companion_conjugate_mul_right hCu, hY]⟩
  · rintro ⟨R, hRt, hRu, hA⟩
    let Y := gmresCompanionBlock h R
    refine ⟨Y * C, block_mul_companion_isUpperTriangular hC h hRt,
      block_mul_companion_isUnit hCu hC hh hRt hRu, ?_, ?_⟩
    · rw [← mulVec_mulVec, hs, mulVec_single_one]
      funext i
      exact gmresCompanionBlock_zero h R i
    · rw [companion_conjugate_mul_right hCu]
      exact hA

end Krylov
