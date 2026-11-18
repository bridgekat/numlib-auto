/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Introduction
import NumlibSurface.BenIsraelGreville.Chapter01.Section01

/-!
# Properties of inner inverses

Section 1.3 of [benIsrael2003generalized] relates the inner inverse equation to rank,
idempotency, scalar multiplication and changes of coordinates.

## Deviations from the source

* **Exercise 9** (typo). The kernel equality concerns $XA$ and $A$.
-/

namespace BenIsraelGreville.Chapter01

open Matrix

variable {m n k l : Type*} [Fintype m] [Fintype n]
  {A : Matrix m n ℂ} {X : Matrix n m ℂ}

/-- **Equation (8)** of [benIsrael2003generalized], Chapter 1. The scalar pseudoinverse
is the reciprocal of a nonzero scalar and is zero at zero. -/
noncomputable def scalarPseudoinverse (a : ℂ) : ℂ := a⁻¹

/-- **Lemma 1(a)** of [benIsrael2003generalized], Chapter 1. The conjugate transpose of an
inner inverse is an inner inverse of the conjugate transpose. -/
theorem lemma_1_a (h : X ∈ definition_1 A {.inner}) :
    Xᴴ ∈ definition_1 Aᴴ {.inner} := by
  apply mem_one_iff.mpr
  rw [isInnerInverse_iff]
  simpa only [conjTranspose_mul, Matrix.mul_assoc] using
    congrArg Matrix.conjTranspose (isInnerInverse_iff.mp (mem_one_iff.mp h))

/-- **Lemma 1(b)** of [benIsrael2003generalized], Chapter 1. The ordinary inverse of a
nonsingular matrix is its unique inner inverse. -/
theorem lemma_1_b [DecidableEq n] {B Y : Matrix n n ℂ} (hB : IsUnit B) :
    Y ∈ definition_1 B {.inner} ↔ Y = B⁻¹ := by
  rw [mem_one_iff]
  refine ⟨Introduction.generalizedInverse_eq_inv hB, ?_⟩
  rintro rfl
  rw [isInnerInverse_iff, B.mul_nonsing_inv ((isUnit_iff_isUnit_det _).mp hB), Matrix.one_mul]

/-- **Lemma 1(c)** of [benIsrael2003generalized], Chapter 1. Scaling a matrix by a scalar
scales an inner inverse by the pseudoinverse of that scalar. -/
theorem lemma_1_c (h : X ∈ definition_1 A {.inner}) (a : ℂ) :
    scalarPseudoinverse a • X ∈ definition_1 (a • A) {.inner} := by
  rw [mem_one_iff, isInnerInverse_iff, scalarPseudoinverse]
  by_cases ha : a = 0
  · simp only [ha, zero_smul, Matrix.zero_mul]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, mul_one,
      isInnerInverse_iff.mp (mem_one_iff.mp h)]

/-- **Lemma 1(d)** of [benIsrael2003generalized], Chapter 1. An inner inverse has rank at
least as large as that of the original matrix. -/
theorem lemma_1_d (h : X ∈ definition_1 A {.inner}) : A.rank ≤ X.rank :=
  (mem_one_iff.mp h).rank_le

/-- **Lemma 1(e)** of [benIsrael2003generalized], Chapter 1. If $X$ is an inner inverse of $A$
and $S,T$ are nonsingular, then $T^{-1}XS^{-1}$ is an inner inverse of $SAT$. -/
theorem lemma_1_e [DecidableEq m] [DecidableEq n] (h : X ∈ definition_1 A {.inner})
    {S : Matrix m m ℂ} {T : Matrix n n ℂ} (hS : IsUnit S) (hT : IsUnit T) :
    T⁻¹ * X * S⁻¹ ∈ definition_1 (S * A * T) {.inner} := by
  rw [mem_one_iff, isInnerInverse_iff]
  have hT' := T.mul_nonsing_inv ((isUnit_iff_isUnit_det T).mp hT)
  have hS' := S.nonsing_inv_mul ((isUnit_iff_isUnit_det S).mp hS)
  calc
    (S * A * T) * (T⁻¹ * X * S⁻¹) * (S * A * T) =
        S * (A * (T * T⁻¹) * X * (S⁻¹ * S) * A) * T := by simp only [Matrix.mul_assoc]
    _ = S * A * T := by
      rw [hT', hS', Matrix.mul_one, Matrix.mul_one, isInnerInverse_iff.mp (mem_one_iff.mp h)]

/-- **Lemma 1(f)** of [benIsrael2003generalized], Chapter 1. For an inner inverse $X$ of
$A$, the products $AX$ and $XA$ are idempotent and have the same rank as $A$. -/
theorem lemma_1_f (h : X ∈ definition_1 A {.inner}) :
    IsIdempotentElem (A * X) ∧ IsIdempotentElem (X * A) ∧
      (A * X).rank = A.rank ∧ (X * A).rank = A.rank := by
  have hX := mem_one_iff.mp h
  exact ⟨hX.isIdempotentElem_mul, hX.isIdempotentElem_mul_rev, hX.rank_mul, hX.rank_mul_rev⟩

/-- **Lemma 2(a)** of [benIsrael2003generalized], Chapter 1. For an inner inverse $X$,
the identity $XA=I$ holds if and only if $A$ has full column rank. -/
theorem lemma_2_a [DecidableEq n] (h : X ∈ definition_1 A {.inner}) :
    X * A = 1 ↔ A.rank = Fintype.card n := by
  obtain ⟨_, hId, _, hRank⟩ := lemma_1_f h
  rw [← hRank, ← vecMul_surjective_iff_rank_eq_card, vecMul_surjective_iff_isUnit]
  exact ⟨fun heq => heq ▸ isUnit_one, fun hu => (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp hId⟩

/-- **Lemma 2(b)** of [benIsrael2003generalized], Chapter 1. For an inner inverse $X$,
the identity $AX=I$ holds if and only if $A$ has full row rank. -/
theorem lemma_2_b [DecidableEq m] (h : X ∈ definition_1 A {.inner}) :
    A * X = 1 ↔ A.rank = Fintype.card m := by
  obtain ⟨hId, _, hRank, _⟩ := lemma_1_f h
  rw [← hRank, ← mulVec_surjective_iff_rank_eq_card, mulVec_surjective_iff_isUnit]
  exact ⟨fun heq => heq ▸ isUnit_one, fun hu => (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp hId⟩

omit [Fintype m] in
/-- **Exercise 7** of [benIsrael2003generalized], Chapter 1. Multiplication by a full-column-rank
factor on the left and a full-row-rank factor on the right preserves rank. -/
theorem exercise_7 [Finite m] [Fintype k] [Fintype l] (F : Matrix m k ℂ) (H : Matrix k l ℂ)
    (G : Matrix l n ℂ) (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card l) :
    (F * H * G).rank = H.rank := by
  classical
  let _ := Fintype.ofFinite m
  have hL := (lemma_2_a (mem_one_iff.mpr F.mul_pinv_mul_self)).mpr hF
  have hR := (lemma_2_b (mem_one_iff.mpr G.mul_pinv_mul_self)).mpr hG
  have hBack : F.pinv * (F * H * G) * G.pinv = H := calc
    F.pinv * (F * H * G) * G.pinv = (F.pinv * F) * H * (G * G.pinv) := by
      simp only [Matrix.mul_assoc]
    _ = H := by rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
  refine le_antisymm ((rank_mul_le_left ..).trans (rank_mul_le_right ..)) ?_
  calc
    H.rank = (F.pinv * (F * H * G) * G.pinv).rank := congrArg rank hBack.symm
    _ ≤ (F * H * G).rank := (rank_mul_le_left ..).trans (rank_mul_le_right ..)

/-- **Exercise 9** of [benIsrael2003generalized], Chapter 1. For an inner inverse $X$,
$AX$ has the range of $A$, $XA$ has the kernel of $A$, and $(XA)^H$ has the range of $A^H$.

**Typo.** The exercise statement prints $N(AX)$. Its proof and Chapter 2, Equation (28),
both give $N(XA)=N(A)$, which is the equality of subspaces of the domain of $A$. -/
theorem exercise_9 (h : X ∈ definition_1 A {.inner}) :
    LinearMap.range (A * X).mulVecLin = LinearMap.range A.mulVecLin ∧
      LinearMap.ker (X * A).mulVecLin = LinearMap.ker A.mulVecLin ∧
      LinearMap.range (X * A)ᴴ.mulVecLin = LinearMap.range Aᴴ.mulVecLin := by
  have hi := mem_one_iff.mp h
  refine ⟨hi.range_mul, hi.ker_mul_rev, ?_⟩
  rw [conjTranspose_mul]
  exact (mem_one_iff.mp (lemma_1_a h)).range_mul

omit [Fintype m] in
/-- **Exercise 10** of [benIsrael2003generalized], Chapter 1. The range of $AB$ equals
the range of $A$ exactly when their ranks agree. The kernel of $AB$ equals the kernel
of $B$ exactly when their ranks agree. -/
theorem exercise_10 [Fintype k] (A : Matrix m n ℂ) (B : Matrix n k ℂ) :
    (LinearMap.range (A * B).mulVecLin = LinearMap.range A.mulVecLin ↔
      (A * B).rank = A.rank) ∧
    (LinearMap.ker (A * B).mulVecLin = LinearMap.ker B.mulVecLin ↔
      (A * B).rank = B.rank) := by
  have hR : LinearMap.range (A * B).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rw [mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hK : LinearMap.ker B.mulVecLin ≤ LinearMap.ker (A * B).mulVecLin := by
    rw [mulVecLin_mul]
    exact LinearMap.ker_le_ker_comp B.mulVecLin A.mulVecLin
  have h₁ := LinearMap.finrank_range_add_finrank_ker (A * B).mulVecLin
  have h₂ := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  change (A * B).rank + Module.finrank ℂ (LinearMap.ker (A * B).mulVecLin) = _ at h₁
  change B.rank + Module.finrank ℂ (LinearMap.ker B.mulVecLin) = _ at h₂
  constructor
  · exact ⟨fun hr => congrArg (fun L : Submodule ℂ (m → ℂ) => Module.finrank ℂ L) hr,
      Submodule.eq_of_le_of_finrank_eq hR⟩
  · constructor
    · intro hk
      rw [hk] at h₁
      omega
    · intro h
      exact (Submodule.eq_of_le_of_finrank_eq hK (by omega)).symm

end BenIsraelGreville.Chapter01
