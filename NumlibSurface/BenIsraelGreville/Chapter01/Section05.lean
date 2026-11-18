/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section03
import NumlibSurface.BenIsraelGreville.Chapter01.Section04

/-!
# Inverses with Hermitian products

Section 1.5 of [benIsrael2003generalized] constructs reflexive inverses with a Hermitian
product from inner inverses of the Gram matrices. Combining the two one-sided Hermitian
conditions gives the Moore–Penrose inverse.

## Deviations from the source

* **Corollary 2** (typo). The kernel of $AA^H$ equals the kernel of $A^H$.
-/

namespace BenIsraelGreville.Chapter01

open Matrix
open scoped ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Lemma 4** of [benIsrael2003generalized], Chapter 1. Both Gram matrices have the same
rank as $A$. -/
theorem lemma_4 (A : Matrix m n ℂ) :
    (A * Aᴴ).rank = A.rank ∧ A.rank = (Aᴴ * A).rank :=
  ⟨A.rank_self_mul_conjTranspose, A.rank_conjTranspose_mul_self.symm⟩

/-- **Corollary 2** of [benIsrael2003generalized], Chapter 1. The range of $AA^H$ is the
range of $A$, and the kernel of $AA^H$ is the kernel of $A^H$.

**Typo.** The printed kernel on the right is $N(A)$. The two kernels in the formal equality
are subspaces of the same coordinate space, including for rectangular matrices. -/
theorem corollary_2 (A : Matrix m n ℂ) :
    LinearMap.range (A * Aᴴ).mulVecLin = LinearMap.range A.mulVecLin ∧
      LinearMap.ker (A * Aᴴ).mulVecLin = LinearMap.ker Aᴴ.mulVecLin := by
  constructor
  · refine Submodule.eq_of_le_of_finrank_eq ?_ (lemma_4 A).1
    rw [mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · simpa only [conjTranspose_conjTranspose] using ker_mulVecLin_conjTranspose_mul_self Aᴴ

private theorem urquhart_left (A : Matrix m n ℂ) {U : Matrix n n ℂ}
    (hGram : (Aᴴ * A) * U * (Aᴴ * A) = Aᴴ * A) :
    A.IsInnerInverse (U * Aᴴ) ∧ A.IsOuterInverse (U * Aᴴ) ∧ (A * (U * Aᴴ)).IsHermitian := by
  classical
  have hAdj : (Aᴴ * A) * A.pinv = Aᴴ := by
    rw [Matrix.mul_assoc, conjTranspose_mul_mul_pinv]
  have hA : A.pinvᴴ * (Aᴴ * A) = A := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hAdj
  have hprod : A * (U * Aᴴ) = A * A.pinv := calc
    A * (U * Aᴴ) = (A.pinvᴴ * (Aᴴ * A)) * (U * ((Aᴴ * A) * A.pinv)) := by
      rw [hA, hAdj]
    _ = A.pinvᴴ * ((Aᴴ * A) * U * (Aᴴ * A)) * A.pinv := by
      simp only [Matrix.mul_assoc]
    _ = A * A.pinv := by rw [hGram, hA]
  have hi : A.IsInnerInverse (U * Aᴴ) := by
    rw [isInnerInverse_iff, hprod, mul_pinv_mul_self]
  have hrank : (U * Aᴴ).rank = A.rank :=
    le_antisymm ((rank_mul_le_right ..).trans_eq A.rank_conjTranspose) hi.rank_le
  have ho := hi.isOuterInverse_iff_rank_eq.mpr hrank
  have hh : (A * (U * Aᴴ)).IsHermitian := by
    rw [hprod]
    exact A.isHermitian_mul_pinv
  exact ⟨hi, ho, hh⟩

/-- **Theorem 3(a)** of [benIsrael2003generalized], Chapter 1. An inner inverse $U$ of $A^H A$
gives a $\{1,2,3\}$-inverse $U A^H$ of $A$. -/
theorem theorem_3_a (A : Matrix m n ℂ) {U : Matrix n n ℂ}
    (hU : U ∈ definition_1 (Aᴴ * A) {.inner}) :
    U * Aᴴ ∈ definition_1 A {.inner, .outer, .hermitianMul} := by
  rw [mem_penroseInverses_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact urquhart_left A (isInnerInverse_iff.mp (mem_one_iff.mp hU))

/-- **Theorem 3(b)** of [benIsrael2003generalized], Chapter 1. An inner inverse $V$ of $AA^H$
gives a $\{1,2,4\}$-inverse $A^H V$ of $A$. -/
theorem theorem_3_b (A : Matrix m n ℂ) {V : Matrix m m ℂ}
    (hV : V ∈ definition_1 (A * Aᴴ) {.inner}) :
    Aᴴ * V ∈ definition_1 A {.inner, .outer, .hermitianMulRev} := by
  have hGram : (Aᴴᴴ * Aᴴ) * Vᴴ * (Aᴴᴴ * Aᴴ) = Aᴴᴴ * Aᴴ := by
    simpa only [conjTranspose_mul, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose (isInnerInverse_iff.mp (mem_one_iff.mp hV))
  have ⟨hi, ho, hh⟩ := urquhart_left Aᴴ hGram
  rw [mem_penroseInverses_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_⟩
  · change A * (Aᴴ * V) * A = A
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose (isInnerInverse_iff.mp hi)
  · change (Aᴴ * V) * A * (Aᴴ * V) = Aᴴ * V
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose (isOuterInverse_iff.mp ho)
  · change ((Aᴴ * V) * A).IsHermitian
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using hh.conjTranspose

/-- **Theorem 4** of [benIsrael2003generalized], Chapter 1. If $Y$ is a $\{1,3\}$-inverse
and $Z$ a $\{1,4\}$-inverse of $A$, then $ZAY=A^\dagger$. -/
theorem theorem_4 [DecidableEq n] {A : Matrix m n ℂ} {Y Z : Matrix n m ℂ}
    (hY : Y ∈ definition_1 A {.inner, .hermitianMul})
    (hZ : Z ∈ definition_1 A {.inner, .hermitianMulRev}) :
    Z * A * Y = A.pinv := by
  obtain ⟨hiY, hhY⟩ := mem_one_three_iff.mp hY
  obtain ⟨hiZ, hhZ⟩ := mem_one_four_iff.mp hZ
  exact (Matrix.pinv_eq_of_innerInverse_mul hiZ hiY hhZ hhY).symm

/-- **Section 1.5** of [benIsrael2003generalized]. There is an inverse satisfying any selected
set of Penrose equations. -/
theorem penroseInverses_nonempty (A : Matrix m n ℂ) (s : Set PenroseCondition) :
    (definition_1 A s).Nonempty := by
  classical
  exact ⟨A.pinv, mem_penroseInverses_iff.mpr fun c _ => A.penroseCondition_pinv c⟩

end BenIsraelGreville.Chapter01
