/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section03
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# Outer inverses of prescribed rank

Section 1.7 of [benIsrael2003generalized] uses a full-rank factorization of a reflexive
inverse and restricts its intermediate coordinates to construct outer inverses.
-/

namespace BenIsraelGreville.Chapter01

open Matrix

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-- **Section 1.7** of [benIsrael2003generalized]. An outer inverse has rank at most
the rank of the original matrix. -/
theorem outerInverse_rank_le {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (hX : X ∈ definition_1 A {.outer}) : X.rank ≤ A.rank :=
  (mem_two_iff.mp hX).rank_le

/-- **Section 1.7** of [benIsrael2003generalized]. The zero matrix is an outer inverse of rank
zero for every matrix. -/
theorem outerInverse_rank_zero (A : Matrix m n ℂ) :
    (0 : Matrix n m ℂ) ∈ definition_1 A {.outer} ∧ (0 : Matrix n m ℂ).rank = 0 := by
  simp only [mem_two_iff, isOuterInverse_iff, Matrix.zero_mul, rank_zero, and_self]

/-- **Equation (21)** of [benIsrael2003generalized], Chapter 1. For a full-rank
factorization $X=YZ$, the outer inverse condition for $X$ is equivalent to $ZAY=I$. -/
theorem rankFactorization_outerInverse [DecidableEq k] (A : Matrix m n ℂ)
    (Y : Matrix n k ℂ) (Z : Matrix k m ℂ) (hY : Y.rank = Fintype.card k)
    (hZ : Z.rank = Fintype.card k) :
    Y * Z ∈ definition_1 A {.outer} ↔ Z * A * Y = 1 := by
  rw [mem_two_iff, isOuterInverse_iff]
  constructor
  · intro h
    classical
    have hL := (lemma_2_a (mem_one_iff.mpr Y.mul_pinv_mul_self)).mpr hY
    have hR := (lemma_2_b (mem_one_iff.mpr Z.mul_pinv_mul_self)).mpr hZ
    calc
      Z * A * Y = (Y.pinv * Y) * (Z * A * Y) * (Z * Z.pinv) := by
        rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
      _ = Y.pinv * ((Y * Z) * A * (Y * Z)) * Z.pinv := by simp only [Matrix.mul_assoc]
      _ = (Y.pinv * Y) * (Z * Z.pinv) := by rw [h]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hL, hR, Matrix.one_mul]
  · intro h
    calc
      (Y * Z) * A * (Y * Z) = Y * (Z * A * Y) * Z := by simp only [Matrix.mul_assoc]
      _ = Y * Z := by rw [h, Matrix.mul_one]

/-- **Section 1.7** of [benIsrael2003generalized]. For every $s\le\operatorname{rank} A$
there is an outer inverse of $A$ of rank $s$, obtained by truncating the intermediate
coordinates of a full-rank factorization of a reflexive inverse. -/
theorem exists_outerInverse_rank (A : Matrix m n ℂ) (s : ℕ) (hs : s ≤ A.rank) :
    ∃ X ∈ definition_1 A {.outer}, X.rank = s := by
  classical
  have hi : A.IsInnerInverse A.pinv := A.mul_pinv_mul_self
  have ho : A.IsOuterInverse A.pinv := A.pinv_mul_self_mul_pinv
  have hr : A.pinv.rank = A.rank := hi.isOuterInverse_iff_rank_eq.mp ho
  obtain ⟨Y, Z, hYZ⟩ :=
    (rank_le_iff_exists_mul A.pinv A.rank).mp hr.le
  have hprod : (Y * Z).rank = A.rank := hYZ ▸ hr
  have hY : Y.rank = Fintype.card (Fin A.rank) := by
    refine le_antisymm Y.rank_le_card_width ?_
    exact ((Fintype.card_fin _).trans hprod.symm).le.trans (rank_mul_le_left Y Z)
  have hZ : Z.rank = Fintype.card (Fin A.rank) := by
    refine le_antisymm Z.rank_le_card_height ?_
    exact ((Fintype.card_fin _).trans hprod.symm).le.trans (rank_mul_le_right Y Z)
  have hId : Z * A * Y = 1 :=
    (rankFactorization_outerInverse A Y Z hY hZ).mp (hYZ ▸ mem_two_iff.mpr ho)
  let e : Fin s ↪ Fin A.rank := ⟨Fin.castLE hs, Fin.castLE_injective hs⟩
  let Y' := Y.submatrix id e
  let Z' := Z.submatrix e id
  have hSub : Z' * A * Y' = 1 := calc
    Z' * A * Y' = (Z * A * Y).submatrix e e := by
      dsimp only [Y', Z']
      rw [submatrix_mul (Z * A) Y e id e Function.bijective_id,
        submatrix_mul Z A e id id Function.bijective_id, submatrix_id_id]
    _ = 1 := by rw [hId, submatrix_one_embedding e]
  have hY' : Y'.rank = Fintype.card (Fin s) := by
    refine le_antisymm Y'.rank_le_card_width ?_
    rw [← rank_one (R := ℂ), ← hSub]
    exact rank_mul_le_right _ _
  have hZ' : Z'.rank = Fintype.card (Fin s) := by
    refine le_antisymm Z'.rank_le_card_height ?_
    rw [← rank_one (R := ℂ), ← hSub]
    exact (rank_mul_le_left ..).trans (rank_mul_le_left ..)
  refine ⟨Y' * Z', (rankFactorization_outerInverse A Y' Z' hY' hZ').mpr hSub, ?_⟩
  have he := exercise_7 Y' (1 : Matrix (Fin s) (Fin s) ℂ) Z' hY' hZ'
  simpa only [Matrix.mul_one, rank_one, Fintype.card_fin] using he

end BenIsraelGreville.Chapter01
