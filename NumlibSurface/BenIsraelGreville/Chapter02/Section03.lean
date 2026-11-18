/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section04
import NumlibSurface.BenIsraelGreville.Chapter01.Section07

/-!
# Outer inverses of fixed rank

Section 2.3 of [benIsrael2003generalized] characterizes outer inverses by factorizations
through their ranks. With a Hermitian product, one factor can be chosen as a Moore–Penrose
inverse.
-/

namespace BenIsraelGreville.Chapter02

open Matrix
open BenIsraelGreville.Chapter01 (definition_1 mem_one_iff mem_two_iff mem_one_two_iff)
open scoped ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Section 2.3** of [benIsrael2003generalized]. The subscript $s$ on a class of inverses
restricts the class to matrices of rank $s$. -/
def inversesOfRank (A : Matrix m n ℂ) (c : Set PenroseCondition) (s : ℕ) :
    Set (Matrix n m ℂ) :=
  {X | X ∈ definition_1 A c ∧ X.rank = s}

private theorem factorization_of_outerInverse (A : Matrix m n ℂ) {X : Matrix n m ℂ} {s : ℕ} :
    X ∈ inversesOfRank A {.outer} s ↔
      ∃ (Y : Matrix n (Fin s) ℂ) (Z : Matrix (Fin s) m ℂ), X = Y * Z ∧ Z * A * Y = 1 := by
  classical
  change (X ∈ definition_1 A {.outer} ∧ X.rank = s) ↔ _
  constructor
  · rintro ⟨hx, hr⟩
    obtain ⟨Y, Z, hYZ⟩ := (rank_le_iff_exists_mul X s).mp hr.le
    have hcard : Fintype.card (Fin s) = (Y * Z).rank := by
      rw [Fintype.card_fin, ← hYZ, hr]
    have hY := le_antisymm Y.rank_le_card_width (hcard.le.trans (rank_mul_le_left Y Z))
    have hZ := le_antisymm Z.rank_le_card_height (hcard.le.trans (rank_mul_le_right Y Z))
    exact ⟨Y, Z, hYZ, (Chapter01.rankFactorization_outerInverse A Y Z hY hZ).mp (hYZ ▸ hx)⟩
  · rintro ⟨Y, Z, rfl, hId⟩
    have hcard : Fintype.card (Fin s) = (Z * A * Y).rank := by rw [hId, rank_one]
    have hY := le_antisymm Y.rank_le_card_width (hcard.le.trans (rank_mul_le_right _ _))
    have hZ := le_antisymm Z.rank_le_card_height
      (hcard.le.trans ((rank_mul_le_left ..).trans (rank_mul_le_left ..)))
    refine ⟨(Chapter01.rankFactorization_outerInverse A Y Z hY hZ).mpr hId, ?_⟩
    simpa only [Matrix.mul_one, rank_one, Fintype.card_fin] using
      Chapter01.exercise_7 Y (1 : Matrix (Fin s) (Fin s) ℂ) Z hY hZ

/-- **Theorem 5** of [benIsrael2003generalized], Chapter 2. For $0<s\le\operatorname{rank} A$,
the rank-$s$ outer inverses are exactly the products $YZ$ with $ZAY=I_s$. -/
theorem theorem_5 (A : Matrix m n ℂ) (X : Matrix n m ℂ) (s : ℕ)
    (_hs : 0 < s) (_hr : s ≤ A.rank) :
    X ∈ inversesOfRank A {.outer} s ↔
      ∃ (Y : Matrix n (Fin s) ℂ) (Z : Matrix (Fin s) m ℂ), X = Y * Z ∧ Z * A * Y = 1 :=
  factorization_of_outerInverse A

/-- **Corollary 5** of [benIsrael2003generalized], Chapter 2. Reflexive inverses are products
$YZ$ through $r=\operatorname{rank} A$ coordinates with $ZAY=I_r$. -/
theorem corollary_5 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    X ∈ definition_1 A {.inner, .outer} ↔
      ∃ (Y : Matrix n (Fin A.rank) ℂ) (Z : Matrix (Fin A.rank) m ℂ),
        X = Y * Z ∧ Z * A * Y = 1 := by
  rw [← factorization_of_outerInverse A, mem_one_two_iff]
  change A.IsInnerInverse X ∧ A.IsOuterInverse X ↔
    X ∈ definition_1 A {.outer} ∧ X.rank = A.rank
  rw [mem_two_iff]
  constructor
  · rintro ⟨hi, ho⟩
    exact ⟨ho, hi.isOuterInverse_iff_rank_eq.mp ho⟩
  · rintro ⟨ho, hr⟩
    have h := (isOuterInverse_iff_isInnerInverse.mp ho).isOuterInverse_iff_rank_eq.mpr hr.symm
    exact ⟨isOuterInverse_iff_isInnerInverse.mp h, ho⟩

private theorem mem_inversesOfRank_outer_three {A : Matrix m n ℂ} {X : Matrix n m ℂ} {s : ℕ} :
    X ∈ inversesOfRank A {.outer, .hermitianMul} s ↔
      (A.IsOuterInverse X ∧ (A * X).IsHermitian) ∧ X.rank = s := by
  change (X ∈ definition_1 A {.outer, .hermitianMul} ∧ _) ↔ _
  simp only [mem_penroseInverses_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  rfl

private theorem mem_inversesOfRank_outer_four {A : Matrix m n ℂ} {X : Matrix n m ℂ} {s : ℕ} :
    X ∈ inversesOfRank A {.outer, .hermitianMulRev} s ↔
      (A.IsOuterInverse X ∧ (X * A).IsHermitian) ∧ X.rank = s := by
  change (X ∈ definition_1 A {.outer, .hermitianMulRev} ∧ _) ↔ _
  simp only [mem_penroseInverses_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  rfl

/-- **Theorem 6** of [benIsrael2003generalized], Chapter 2. For $0<s\le\operatorname{rank} A$,
the rank-$s$ matrices in $A\{2,3\}$ are exactly $Y(AY)^\dagger$ with $AY$ of full
column rank $s$. -/
theorem theorem_6 (A : Matrix m n ℂ) (X : Matrix n m ℂ) (s : ℕ)
    (_hs : 0 < s) (_hr : s ≤ A.rank) :
    X ∈ inversesOfRank A {.outer, .hermitianMul} s ↔
      ∃ Y : Matrix n (Fin s) ℂ, (A * Y).rank = s ∧ X = Y * (A * Y).pinv := by
  rw [mem_inversesOfRank_outer_three]
  constructor
  · rintro ⟨⟨ho, hh⟩, hr⟩
    have hX : X ∈ inversesOfRank A {.outer} s := ⟨mem_two_iff.mpr ho, hr⟩
    obtain ⟨Y, Z, rfl, hId⟩ := (factorization_of_outerInverse A).mp hX
    have h : Z * (A * Y) = 1 := by rwa [← Matrix.mul_assoc]
    have hAY : (A * Y).rank = s := by
      have hcard := congrArg rank h
      rw [rank_one, Fintype.card_fin] at hcard
      refine le_antisymm ?_ (hcard.ge.trans (rank_mul_le_right _ _))
      exact (rank_le_card_width (A * Y)).trans_eq (Fintype.card_fin s)
    refine ⟨Y, hAY, ?_⟩
    have hZ : Z = (A * Y).pinv := by
      refine (A * Y).pinv_unique ?_ ?_ ?_ ?_
      · rw [Matrix.mul_assoc, h, Matrix.mul_one]
      · rw [h, Matrix.one_mul]
      · rwa [Matrix.mul_assoc]
      · rw [h]
        exact isHermitian_one
    rw [← hZ]
  · rintro ⟨Y, hAY, rfl⟩
    let H := A * Y
    have hProd : A * (Y * H.pinv) = H * H.pinv := (Matrix.mul_assoc ..).symm
    have ho : A.IsOuterInverse (Y * H.pinv) := by
      rw [isOuterInverse_iff]
      calc
        (Y * H.pinv) * A * (Y * H.pinv) = Y * (H.pinv * H * H.pinv) := by
          dsimp only [H]
          simp only [Matrix.mul_assoc]
        _ = Y * H.pinv := by rw [H.pinv_mul_self_mul_pinv]
    have hh : (A * (Y * H.pinv)).IsHermitian := by rw [hProd]; exact H.isHermitian_mul_pinv
    refine ⟨⟨ho, hh⟩, le_antisymm ?_ ?_⟩
    · exact (rank_mul_le_left ..).trans (Y.rank_le_card_width.trans_eq (Fintype.card_fin s))
    · calc
        s = H.rank := hAY.symm
        _ = (H * H.pinv).rank := (isInnerInverse_iff.mpr H.mul_pinv_mul_self).rank_mul.symm
        _ = (A * (Y * H.pinv)).rank := congrArg rank hProd.symm
        _ ≤ (Y * H.pinv).rank := rank_mul_le_right _ _

private theorem adjoint_mem_outer_three {A : Matrix m n ℂ} {X : Matrix n m ℂ} {s : ℕ} :
    Xᴴ ∈ inversesOfRank Aᴴ {.outer, .hermitianMul} s ↔
      X ∈ inversesOfRank A {.outer, .hermitianMulRev} s := by
  rw [mem_inversesOfRank_outer_three, mem_inversesOfRank_outer_four, rank_conjTranspose]
  refine and_congr_left fun _ => ?_
  constructor
  · rintro ⟨ho, hh⟩
    refine ⟨?_, ?_⟩
    · simpa only [isOuterInverse_iff, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.mul_assoc] using congrArg Matrix.conjTranspose (isOuterInverse_iff.mp ho)
    · simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using hh.conjTranspose
  · rintro ⟨ho, hh⟩
    refine ⟨?_, ?_⟩
    · simpa only [isOuterInverse_iff, conjTranspose_mul, Matrix.mul_assoc] using
        congrArg Matrix.conjTranspose (isOuterInverse_iff.mp ho)
    · simpa only [conjTranspose_mul] using hh.conjTranspose

/-- **Theorem 7** of [benIsrael2003generalized], Chapter 2. For $0<s\le\operatorname{rank} A$,
the rank-$s$ matrices in $A\{2,4\}$ are exactly $(YA)^\dagger Y$ with $YA$ of full row
rank $s$. -/
theorem theorem_7 [DecidableEq n] (A : Matrix m n ℂ) (X : Matrix n m ℂ) (s : ℕ)
    (hs : 0 < s) (hr : s ≤ A.rank) :
    X ∈ inversesOfRank A {.outer, .hermitianMulRev} s ↔
      ∃ Y : Matrix (Fin s) m ℂ, (Y * A).rank = s ∧ X = (Y * A).pinv * Y := by
  classical
  rw [← adjoint_mem_outer_three, theorem_6 Aᴴ Xᴴ s hs (hr.trans_eq A.rank_conjTranspose.symm)]
  constructor
  · rintro ⟨Y, hy, hX⟩
    have hAdj : (Aᴴ * Y)ᴴ = Yᴴ * A := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
    refine ⟨Yᴴ, ?_, ?_⟩
    · rw [← hAdj, rank_conjTranspose, hy]
    · have h := congrArg Matrix.conjTranspose hX
      simpa only [conjTranspose_mul, conjTranspose_conjTranspose, ← pinv_conjTranspose, hAdj]
        using h
  · rintro ⟨Y, hy, hX⟩
    have hAdj : (Y * A)ᴴ = Aᴴ * Yᴴ := conjTranspose_mul Y A
    refine ⟨Yᴴ, ?_, ?_⟩
    · rw [← hAdj, rank_conjTranspose, hy]
    · have h := congrArg Matrix.conjTranspose hX
      simpa only [conjTranspose_mul, ← pinv_conjTranspose, hAdj] using h

end BenIsraelGreville.Chapter02
