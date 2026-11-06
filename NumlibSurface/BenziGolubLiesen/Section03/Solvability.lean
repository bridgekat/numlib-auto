/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Numlib.LinearAlgebra.Matrix.SaddlePoint
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 3.2

Nonsingularity criteria for symmetric and nonsymmetric saddle-point systems.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {A : Matrix n n ℝ} {B B₁ B₂ : Matrix m n ℝ} {C : Matrix m m ℝ}

omit [DecidableEq n] [DecidableEq m] in
private theorem fullRowRank_injective (hB : B.rank = Fintype.card m) :
    Function.Injective Bᵀ.mulVec :=
  Matrix.mulVec_injective_iff_rank_eq_card.mpr (by rwa [Matrix.rank_transpose])

/-- **Theorem 3.1** of [benzi2005numerical]. With positive definite `A` and positive semidefinite
`C`, a trivial intersection of the kernels of `C` and `Bᵀ` implies nonsingularity.
In particular full row rank of `B` suffices. -/
theorem theorem_3_1 (hA : A.PosDef) (hC : C.PosSemidef) :
    (LinearMap.ker C.mulVecLin ⊓ LinearMap.ker Bᵀ.mulVecLin = ⊥ →
      IsUnit (saddlePointMatrix A B B C)) ∧
    (B.rank = Fintype.card m → IsUnit (saddlePointMatrix A B B C)) := by
  have hkerA : LinearMap.ker A.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr hA.mulVec_injective
  have h (hker : LinearMap.ker C.mulVecLin ⊓ LinearMap.ker Bᵀ.mulVecLin = ⊥) :
      IsUnit (saddlePointMatrix A B B C) :=
    (isUnit_fromBlocks_transpose_neg_iff B hA.posSemidef hC).mpr ⟨by simp [hkerA], hker⟩
  refine ⟨h, fun hB ↦ h ?_⟩
  have hkerB : LinearMap.ker Bᵀ.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fullRowRank_injective hB)
  simp only [hkerB, inf_bot_eq]

/-- **Theorem 3.2** of [benzi2005numerical]. For positive semidefinite `A` and full-row-rank
`B`, the symmetric saddle-point matrix with zero trailing block is nonsingular exactly when
the kernels of `A` and `B` intersect trivially. -/
theorem theorem_3_2 (hA : A.PosSemidef) (hB : B.rank = Fintype.card m) :
    IsUnit (saddlePointMatrix A B B 0) ↔
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ := by
  have hkerB : LinearMap.ker Bᵀ.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fullRowRank_injective hB)
  simpa only [hkerB, inf_bot_eq, and_true] using
    isUnit_fromBlocks_transpose_neg_iff B hA (PosSemidef.zero (n := m))

/-- **Theorem 3.3** of [benzi2005numerical]. Nonsingularity with a zero trailing block implies
full row rank of `B₁` and full column rank of the vertical stack of `A` and `B₂`. -/
theorem theorem_3_3 (h : IsUnit (saddlePointMatrix A B₁ B₂ 0)) :
    B₁.rank = Fintype.card m ∧ (fromRows A B₂).rank = Fintype.card n :=
  ranks_of_isUnit_fromBlocks_transpose_zero (by simpa [saddlePointMatrix] using h)

/-- **Theorem 3.4** of [benzi2005numerical]. For a positive semidefinite symmetric part `H`,
a positive semidefinite `C` and full-row-rank `B`, a trivial intersection of the kernels of
`H` and `B` suffices for nonsingularity. Nonsingularity in turn forces the intersection of the
kernels of `A` and `B` to be trivial. -/
theorem theorem_3_4 (hA : (hermitianPart A).PosSemidef) (hC : C.PosSemidef)
    (hB : B.rank = Fintype.card m) :
    ((LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) →
      IsUnit (saddlePointMatrix A B B C)) ∧
    (IsUnit (saddlePointMatrix A B B C) →
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :=
  ⟨isUnit_fromBlocks_transpose_neg_of_hermitianPart hA hC (fullRowRank_injective hB),
    ker_inter_eq_bot_of_isUnit_fromBlocks⟩

private theorem singleRow_fullRank {k : ℕ} (j : Fin k) :
    (Matrix.single (0 : Fin 1) j (1 : ℝ)).rank = 1 := by
  suffices (Matrix.single (0 : Fin 1) j (1 : ℝ)).rank = Fintype.card (Fin 1) by
    simpa only [Fintype.card_fin] using this
  rw [← rank_transpose, ← mulVec_injective_iff_rank_eq_card, transpose_single]
  intro x y h
  have h0 := congrFun h j
  simp only [single_mulVec, Function.update_self, one_mul] at h0
  funext i
  fin_cases i
  exact h0

private theorem converse_i_counterexample :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (B : Matrix (Fin 1) (Fin 3) ℝ),
      (hermitianPart A).PosSemidef ∧ B.rank = 1 ∧ IsUnit (saddlePointMatrix A B B 0) ∧
        LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin ≠ ⊥ := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![1, -1, 0; 1, 0, 0; 0, 0, 0]
  let B : Matrix (Fin 1) (Fin 3) ℝ := Matrix.single 0 2 1
  have hH : hermitianPart A = Matrix.diagonal ![1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, hermitianPart_eq_smul_add_transpose, Matrix.diagonal_apply]
  refine ⟨A, B, ?_, singleRow_fullRank 2, ?_, ?_⟩
  · rw [hH, posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  · rw [isUnit_iff_mulVec_sumElim]
    intro x y h
    change fromBlocks A Bᵀ B (-(0 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ Sum.elim x y = 0 at h
    rw [fromBlocks_mulVec_sumElim_eq_zero_iff] at h
    have hx0 : x 0 = 0 := by
      simpa [A, B, transpose_single, single_mulVec, dotProduct, Fin.sum_univ_succ] using
        congrFun h.1 1
    have hy0 : y 0 = 0 := by
      simpa [A, B, transpose_single, single_mulVec, dotProduct, Fin.sum_univ_succ] using
        congrFun h.1 2
    have hx1 : x 1 = 0 := by
      simpa [A, B, transpose_single, single_mulVec, dotProduct, Fin.sum_univ_succ, hx0] using
        congrFun h.1 0
    have hx2 : x 2 = 0 := by
      simpa [B, single_mulVec] using congrFun h.2 0
    constructor
    · funext i
      fin_cases i
      · exact hx0
      · exact hx1
      · exact hx2
    · funext i
      fin_cases i
      exact hy0
  · intro h
    let x : Fin 3 → ℝ := ![0, 1, 0]
    have hx : x ∈ LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
      rw [hH]
      simp only [Submodule.mem_inf, LinearMap.mem_ker, mulVecLin_apply]
      constructor <;> ext i <;> fin_cases i <;>
        norm_num [B, x, mulVec, dotProduct, Fin.sum_univ_succ, Matrix.single, diagonal_apply]
    have hzero := (Submodule.eq_bot_iff _).mp h x hx
    have h1 := congrFun hzero 1
    norm_num [x] at h1

private theorem converse_ii_counterexample :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ),
      (hermitianPart A).PosSemidef ∧ B.rank = 1 ∧
        LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ ∧
        ¬IsUnit (saddlePointMatrix A B B 0) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1]
  let B : Matrix (Fin 1) (Fin 2) ℝ := Matrix.single 0 1 1
  have hH : hermitianPart A = Matrix.diagonal ![0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, hermitianPart_eq_smul_add_transpose, Matrix.diagonal_apply]
  refine ⟨A, B, ?_, singleRow_fullRank 1, ?_, ?_⟩
  · rw [hH, posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  · have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (by
      norm_num [A, Matrix.det_fin_two])
    simp [(LinearMap.ker_eq_bot.mpr (mulVec_injective_iff_isUnit.mpr hA) :
      LinearMap.ker A.mulVecLin = ⊥)]
  · intro h
    let x : Fin 2 → ℝ := ![1, 0]
    let y : Fin 1 → ℝ := ![-1]
    have hxy : saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = 0 := by
      change fromBlocks A Bᵀ B (-(0 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ Sum.elim x y = 0
      rw [fromBlocks_mulVec_sumElim_eq_zero_iff]
      constructor
      · ext i
        fin_cases i <;>
          norm_num [A, B, x, y, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.single]
      · simp [B, x, single_mulVec]
    have h0 := congrFun ((isUnit_iff_mulVec_sumElim.mp h) x y hxy).1 0
    norm_num [x] at h0

/-- The examples following **Theorem 3.4** of [benzi2005numerical]. Even with a zero trailing block,
the hypotheses of the two implications do not force their converses. -/
theorem theorem_3_4_converses :
    (∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (B : Matrix (Fin 1) (Fin 3) ℝ),
      (hermitianPart A).PosSemidef ∧ B.rank = 1 ∧ IsUnit (saddlePointMatrix A B B 0) ∧
        LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin ≠ ⊥) ∧
    (∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ),
      (hermitianPart A).PosSemidef ∧ B.rank = 1 ∧
        LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ ∧
        ¬IsUnit (saddlePointMatrix A B B 0)) :=
  ⟨converse_i_counterexample, converse_ii_counterexample⟩

end BenziGolubLiesen
