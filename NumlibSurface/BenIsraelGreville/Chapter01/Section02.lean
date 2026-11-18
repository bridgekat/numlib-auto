/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section01
import Mathlib.Data.Matrix.Block
import NumlibSurface.BenIsraelGreville.Chapter00.Section04

/-!
# Inner inverses from Hermite form

Section 1.2 of [benIsrael2003generalized] constructs inner inverses by applying invertible
row and column operations to a block matrix with an identity in its leading block.
-/

namespace BenIsraelGreville.Chapter01

open Matrix

variable {r m n : Type*} [Fintype r] [Fintype m] [Fintype n]

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 1. When $EAP$ is in the block
form $[I,K;0,0]$ with $E$ and $P$ nonsingular, $P[I,0;0,L]E$ is an inner inverse
of $A$ for any block $L$. The dimensions of the other blocks may be zero. -/
theorem theorem_1 [DecidableEq r] [DecidableEq m] [DecidableEq n]
    {A : Matrix (r ⊕ m) (r ⊕ n) ℂ}
    {E : Matrix (r ⊕ m) (r ⊕ m) ℂ} {P : Matrix (r ⊕ n) (r ⊕ n) ℂ}
    (hE : IsUnit E) (hP : IsUnit P) (K : Matrix r n ℂ)
    (h : E * A * P = fromBlocks 1 K 0 0) (L : Matrix n m ℂ) :
    P * fromBlocks 1 0 0 L * E ∈ definition_1 A {.inner} := by
  let R : Matrix (r ⊕ m) (r ⊕ n) ℂ := fromBlocks 1 K 0 0
  let S : Matrix (r ⊕ n) (r ⊕ m) ℂ := fromBlocks 1 0 0 L
  change E * A * P = R at h
  have hR : R * S * R = R := by
    dsimp only [R, S]
    simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
  have hE' := E.nonsing_inv_mul ((isUnit_iff_isUnit_det _).mp hE)
  have hP' := P.mul_nonsing_inv ((isUnit_iff_isUnit_det _).mp hP)
  have hcancel : ∀ B : Matrix (r ⊕ m) (r ⊕ n) ℂ, E⁻¹ * (E * B * P) * P⁻¹ = B := by
    intro B
    calc
      E⁻¹ * (E * B * P) * P⁻¹ = (E⁻¹ * E) * B * (P * P⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hE', hP', Matrix.one_mul, Matrix.mul_one]
  rw [mem_one_iff, isInnerInverse_iff]
  change A * (P * S * E) * A = A
  calc
    A * (P * S * E) * A = E⁻¹ * (E * (A * (P * S * E) * A) * P) * P⁻¹ :=
      (hcancel _).symm
    _ = E⁻¹ * ((E * A * P) * S * (E * A * P)) * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = E⁻¹ * (E * A * P) * P⁻¹ := by rw [h, hR]
    _ = A := hcancel _

/-- **Equation (6)** of [benIsrael2003generalized], Chapter 1. The Hermite
formula yields an inner inverse of rank equal to the size of the leading
identity plus the rank of the freely chosen lower block. -/
theorem rank_hermiteInverse [DecidableEq r] [DecidableEq m] [DecidableEq n]
    {E : Matrix (r ⊕ m) (r ⊕ m) ℂ} {P : Matrix (r ⊕ n) (r ⊕ n) ℂ}
    (hE : IsUnit E) (hP : IsUnit P) (L : Matrix n m ℂ) :
    (P * fromBlocks (1 : Matrix r r ℂ) 0 0 L * E).rank = Fintype.card r + L.rank := by
  rw [rank_mul_eq_left_of_isUnit_det E _ ((isUnit_iff_isUnit_det E).mp hE),
    rank_mul_eq_right_of_isUnit_det P _ ((isUnit_iff_isUnit_det P).mp hP),
    rank_fromBlocks_diagonal, rank_one]

private theorem exists_matrix_rank {s : ℕ} (hm : s ≤ Fintype.card m) (hn : s ≤ Fintype.card n) :
    ∃ L : Matrix n m ℂ, L.rank = s := by
  classical
  let σ (i : ℕ) : ℂ := if i < s then 1 else 0
  let L : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card m)) ℂ := rectDiagonal σ
  refine ⟨L.reindex (Fintype.equivFin n).symm (Fintype.equivFin m).symm, ?_⟩
  rw [rank_reindex, rank_rectDiagonal]
  refine (Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_)).trans
    (Fintype.card_fin_lt_of_le hm)
  by_cases hj : (j : ℕ) < s
  · simp [σ, hj, hj.trans_le hn]
  · simp [σ, hj]

/-- **Section 1.2** of [benIsrael2003generalized], after Equation (6).
Every rank from the rank of the input matrix to the smaller of its dimensions
is attained by an inner inverse. -/
theorem exists_innerInverse_rank {a b s : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (hr : A.rank ≤ s) (hs : s ≤ min a b) :
    ∃ X, X ∈ definition_1 A {.inner} ∧ X.rank = s := by
  classical
  obtain ⟨E, hE, h⟩ := Chapter00.exists_isUnit_mul_isReducedRowEchelon A
  obtain ⟨p, e, f, B, hB⟩ := Chapter00.exists_reindex_eq_hermiteBlock (E * A) h
  let I := {i : Fin a // (E * A) i ≠ 0}
  let I₀ := {i : Fin a // (E * A) i = 0}
  let J₀ := {j : Fin b // j ∉ Set.range p}
  change I ⊕ I₀ ≃ Fin a at e
  change I ⊕ J₀ ≃ Fin b at f
  let E' := E.reindex e.symm e.symm
  let A' := A.submatrix e f
  have hE' : IsUnit E' := hE.map (reindexRingEquiv ℂ e.symm).toMonoidHom
  have hEA' : E' * A' = fromBlocks 1 B 0 0 := by
    simpa only [E', A', reindex_apply, Equiv.symm_symm, submatrix_mul_equiv] using hB
  have hRank : A.rank = Fintype.card I := by
    calc
      A.rank = (E * A).rank :=
        (rank_mul_eq_right_of_isUnit_det E A ((isUnit_iff_isUnit_det E).mp hE)).symm
      _ = ((E * A).submatrix e f).rank := (rank_submatrix _ e f).symm
      _ = Fintype.card I :=
        (congrArg Matrix.rank hB).trans (Chapter00.rank_hermiteBlock B)
  have hRows := Fintype.card_congr e
  have hCols := Fintype.card_congr f
  simp only [Fintype.card_sum, Fintype.card_fin] at hRows hCols
  obtain ⟨L, hL⟩ := exists_matrix_rank (m := I₀) (n := J₀) (s := s - A.rank)
    (by omega) (by omega)
  let P : Matrix (I ⊕ J₀) (I ⊕ J₀) ℂ := 1
  let X' := P * fromBlocks (1 : Matrix I I ℂ) 0 0 L * E'
  have hx : A' * X' * A' = A' := by
    exact isInnerInverse_iff.mp (mem_one_iff.mp (theorem_1 hE' (show IsUnit P from isUnit_one)
      B (by simpa only [P, Matrix.mul_one] using hEA') L))
  refine ⟨X'.submatrix f.symm e.symm, mem_one_iff.mpr (isInnerInverse_iff.mpr ?_), ?_⟩
  · have hA : A'.submatrix e.symm f.symm = A := by
      simp only [A', submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
    calc
      A * X'.submatrix f.symm e.symm * A =
          A'.submatrix e.symm f.symm * X'.submatrix f.symm e.symm *
            A'.submatrix e.symm f.symm := by rw [hA]
      _ = (A' * X' * A').submatrix e.symm f.symm := by rw [submatrix_mul_equiv,
        submatrix_mul_equiv]
      _ = A := by rw [hx, hA]
  · rw [rank_submatrix]
    change (P * fromBlocks (1 : Matrix I I ℂ) 0 0 L * E').rank = s
    rw [rank_hermiteInverse hE' (show IsUnit P from isUnit_one), hL,
      ← hRank, Nat.add_sub_of_le hr]

/-- **Section 1.2** of [benIsrael2003generalized]. Every complex matrix has an inner inverse. -/
theorem exists_innerInverse (A : Matrix m n ℂ) : (definition_1 A {.inner}).Nonempty := by
  classical
  exact ⟨A.pinv, mem_one_iff.mpr A.mul_pinv_mul_self⟩

end BenIsraelGreville.Chapter01
