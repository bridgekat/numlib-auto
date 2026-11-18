/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section01
import NumlibSurface.BenIsraelGreville.Introduction

/-!
# Solutions of linear systems

Section 2.1 of [benIsrael2003generalized] gives the consistency test and the affine
solution family for the two-sided matrix equation $AXB=D$. Its special cases describe
inner inverses and the solutions of consistent vector equations.
-/

namespace BenIsraelGreville.Chapter02

open Matrix
open BenIsraelGreville.Chapter01 (definition_1 mem_one_iff)

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 2. For any inner inverses $U$ of $A$
and $V$ of $B$, the system $AXB=D$ is consistent exactly when $AUDVB=D$. In that case its
solutions are exactly $UDV+Y-UAYBV$, for arbitrary $Y$. -/
theorem theorem_1
    {A : Matrix m n ℂ} {B : Matrix p q ℂ} {U : Matrix n m ℂ} {V : Matrix q p ℂ}
    (hU : U ∈ definition_1 A {.inner}) (hV : V ∈ definition_1 B {.inner})
    (D : Matrix m q ℂ) :
    ((∃ X, A * X * B = D) ↔ A * U * D * V * B = D) ∧
      (A * U * D * V * B = D → ∀ X, A * X * B = D ↔
        ∃ Y, X = U * D * V + Y - U * A * Y * B * V) := by
  have hA := isInnerInverse_iff.mp (mem_one_iff.mp hU)
  have hB := isInnerInverse_iff.mp (mem_one_iff.mp hV)
  have hPart : A * (U * D * V) * B = A * U * D * V * B := by
    simp only [Matrix.mul_assoc]
  have hProj (Y : Matrix n p ℂ) : A * U * (A * Y * B) * V * B = A * Y * B := calc
    A * U * (A * Y * B) * V * B = (A * U * A) * Y * (B * V * B) := by
      simp only [Matrix.mul_assoc]
    _ = A * Y * B := by rw [hA, hB]
  constructor
  · constructor
    · rintro ⟨X, rfl⟩
      exact hProj X
    · intro hD
      exact ⟨U * D * V, hPart.trans hD⟩
  · intro hD X
    constructor
    · intro hX
      refine ⟨X, ?_⟩
      have hEq : U * D * V = U * A * X * B * V := by
        rw [← hX]
        simp only [Matrix.mul_assoc]
      rw [← hEq, add_comm, add_sub_cancel_right]
    · rintro ⟨Y, rfl⟩
      have hY : A * (U * A * Y * B * V) * B = A * Y * B := calc
        A * (U * A * Y * B * V) * B = A * U * (A * Y * B) * V * B := by
          simp only [Matrix.mul_assoc]
        _ = _ := hProj Y
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
        hY, hPart, hD, add_sub_cancel_right]

/-- **Corollary 1** of [benIsrael2003generalized], Chapter 2. Given an inner inverse $U$ of $A$,
all inner inverses of $A$ have the form $U+Z-UAZAU$. -/
theorem corollary_1 {A : Matrix m n ℂ} {U X : Matrix n m ℂ}
    (hU : U ∈ definition_1 A {.inner}) :
    X ∈ definition_1 A {.inner} ↔ ∃ Z, X = U + Z - U * A * Z * A * U := by
  have hA := isInnerInverse_iff.mp (mem_one_iff.mp hU)
  have hD : A * U * A * U * A = A := by rw [hA, hA]
  have hparam (Z : Matrix n m ℂ) :
      U * A * U + (U + Z) - U * A * (U + Z) * A * U =
        U + Z - U * A * Z * A * U := by
    have hAA : U * A * U * A * U = U * A * U := calc
      U * A * U * A * U = U * (A * U * A) * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, hAA]
    abel
  rw [mem_one_iff, isInnerInverse_iff, (theorem_1 hU hU A).2 hD]
  constructor
  · rintro ⟨Y, hX⟩
    refine ⟨Y - U, ?_⟩
    rw [← hparam, add_comm U, sub_add_cancel, ← hX]
  · rintro ⟨Z, hX⟩
    exact ⟨U + Z, hX.trans (hparam Z).symm⟩

/-- **Corollary 2** of [benIsrael2003generalized], Chapter 2. Given an inner inverse $U$,
$Ax=b$ is consistent exactly when $AUb=b$, and its solutions in that case have the form
$Ub+(I-UA)y$. -/
theorem corollary_2 [DecidableEq n] {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    (hU : U ∈ definition_1 A {.inner}) (b : m → ℂ) :
    ((∃ x, A *ᵥ x = b) ↔ (A * U) *ᵥ b = b) ∧
      ((A * U) *ᵥ b = b → ∀ x, A *ᵥ x = b ↔
        ∃ y, x = U *ᵥ b + (1 - U * A) *ᵥ y) :=
  ⟨Introduction.solvable_iff_mul_mulVec_eq (mem_one_iff.mp hU) b,
    fun hb => Introduction.solution_iff_exists_eq_generalSolution (mem_one_iff.mp hU) hb⟩

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 2. The matrix $X$ is an inner inverse of
$A$ exactly when $Xb$ solves $Ax=b$ for every consistent right-hand side $b$. -/
theorem theorem_2 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    X ∈ definition_1 A {.inner} ↔
      ∀ b, (∃ x, A *ᵥ x = b) → A *ᵥ (X *ᵥ b) = b := by
  rw [mem_one_iff]
  exact Introduction.generalizedInverse_iff_solves_consistent A X

end BenIsraelGreville.Chapter02
