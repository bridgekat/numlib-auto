/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section03

/-!
# Inner inverses with one Hermitian product

Section 2.2 of [benIsrael2003generalized] characterizes the $\{1,3\}$ and $\{1,4\}$ inverse
classes by their products with $A$ and gives affine parametrizations of both classes.
-/

namespace BenIsraelGreville.Chapter02

open Matrix
open BenIsraelGreville.Chapter01 (definition_1 mem_one_three_iff mem_one_four_iff)

variable {m n : Type*} [Fintype m] [Fintype n]
  {A : Matrix m n ℂ} {X Z : Matrix n m ℂ}

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 2. For a fixed $\{1,3\}$-inverse $Z$,
$X$ lies in that class if and only if $AX=AZ$. -/
theorem theorem_3 (hZ : Z ∈ definition_1 A {.inner, .hermitianMul}) :
    X ∈ definition_1 A {.inner, .hermitianMul} ↔ A * X = A * Z := by
  obtain ⟨hZi, hZh⟩ := mem_one_three_iff.mp hZ
  have hZeq := isInnerInverse_iff.mp hZi
  rw [mem_one_three_iff, isInnerInverse_iff]
  constructor
  · rintro ⟨hXi, hXh⟩
    have h : (A * X) * (A * Z) = A * Z := by
      rw [← Matrix.mul_assoc, hXi]
    have h' : (A * Z) * (A * X) = A * Z := by
      simpa only [conjTranspose_mul, hXh.eq, hZh.eq] using congrArg Matrix.conjTranspose h
    rwa [← Matrix.mul_assoc, hZeq] at h'
  · intro h
    rw [h]
    exact ⟨hZeq, hZh⟩

/-- **Corollary 3** of [benIsrael2003generalized], Chapter 2. For a fixed $\{1,3\}$-inverse $Z$,
the other members are exactly $Z+(I-ZA)Y$ for arbitrary $Y$. -/
theorem corollary_3 [DecidableEq n] (hZ : Z ∈ definition_1 A {.inner, .hermitianMul}) :
    X ∈ definition_1 A {.inner, .hermitianMul} ↔
      ∃ Y : Matrix n m ℂ, X = Z + (1 - Z * A) * Y := by
  rw [theorem_3 hZ]
  constructor
  · intro h
    refine ⟨X - Z, ?_⟩
    have hzero : A * (X - Z) = 0 := by rw [Matrix.mul_sub, h, sub_self]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hzero, Matrix.mul_zero,
      sub_zero, add_sub_cancel]
  · rintro ⟨Y, rfl⟩
    have hA := isInnerInverse_iff.mp (mem_one_three_iff.mp hZ).1
    have hzero : A * (1 - Z * A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hA, sub_self]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hzero, Matrix.zero_mul, add_zero]

private theorem adjoint_mem_one_three_iff {W : Matrix n m ℂ} :
    Wᴴ ∈ definition_1 Aᴴ {.inner, .hermitianMul} ↔
      W ∈ definition_1 A {.inner, .hermitianMulRev} := by
  rw [mem_one_three_iff, mem_one_four_iff]
  constructor
  · rintro ⟨hi, hh⟩
    refine ⟨?_, ?_⟩
    · simpa only [isInnerInverse_iff, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.mul_assoc] using congrArg Matrix.conjTranspose (isInnerInverse_iff.mp hi)
    · simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using hh.conjTranspose
  · rintro ⟨hi, hh⟩
    refine ⟨?_, ?_⟩
    · simpa only [isInnerInverse_iff, conjTranspose_mul, Matrix.mul_assoc] using
        congrArg Matrix.conjTranspose (isInnerInverse_iff.mp hi)
    · simpa only [conjTranspose_mul] using hh.conjTranspose

/-- **Theorem 4** of [benIsrael2003generalized], Chapter 2. For a fixed $\{1,4\}$-inverse $Z$,
$X$ lies in that class if and only if $XA=ZA$. -/
theorem theorem_4 (hZ : Z ∈ definition_1 A {.inner, .hermitianMulRev}) :
    X ∈ definition_1 A {.inner, .hermitianMulRev} ↔ X * A = Z * A := by
  rw [← adjoint_mem_one_three_iff, theorem_3 (adjoint_mem_one_three_iff.mpr hZ)]
  rw [← conjTranspose_mul, ← conjTranspose_mul, conjTranspose_inj]

/-- **Corollary 4** of [benIsrael2003generalized], Chapter 2. For a fixed $\{1,4\}$-inverse $Z$,
the other members are exactly $Z+Y(I-AZ)$ for arbitrary $Y$. -/
theorem corollary_4 [DecidableEq m] (hZ : Z ∈ definition_1 A {.inner, .hermitianMulRev}) :
    X ∈ definition_1 A {.inner, .hermitianMulRev} ↔
      ∃ Y : Matrix n m ℂ, X = Z + Y * (1 - A * Z) := by
  rw [theorem_4 hZ]
  constructor
  · intro h
    refine ⟨X - Z, ?_⟩
    have hzero : (X - Z) * A = 0 := by rw [Matrix.sub_mul, h, sub_self]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hzero, Matrix.zero_mul,
      sub_zero, add_sub_cancel]
  · rintro ⟨Y, rfl⟩
    have hA := isInnerInverse_iff.mp (mem_one_four_iff.mp hZ).1
    have hzero : (1 - A * Z) * A = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hA, sub_self]
    rw [Matrix.add_mul, Matrix.mul_assoc, hzero, Matrix.mul_zero, add_zero]

end BenIsraelGreville.Chapter02
