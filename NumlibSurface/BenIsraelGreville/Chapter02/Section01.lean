/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section01
import NumlibSurface.BenIsraelGreville.Introduction
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Solutions of linear systems

Section 2.1 of [benIsrael2003generalized] gives the consistency test and the affine
solution family for the two-sided matrix equation $AXB=D$. Its special cases describe
inner inverses and the solutions of consistent vector equations.
-/

namespace BenIsraelGreville.Chapter02

open Matrix
open scoped Kronecker
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

/-- The row-by-row vectorization of **Exercise 2** of
[benIsrael2003generalized]. -/
abbrev vectorization (X : Matrix m n ℂ) : m × n → ℂ := Xᵀ.vec

omit [Fintype m] [Fintype q] in
/-- The Kronecker matrix for the vectorized two-sided equation
in **Equations (10)–(11)**. -/
theorem vectorization_mul_mul (A : Matrix m n ℂ) (X : Matrix n p ℂ)
    (B : Matrix p q ℂ) :
    vectorization (A * X * B) = (A ⊗ₖ Bᵀ) *ᵥ vectorization X := by
  unfold vectorization
  rw [kronecker_mulVec_vec, transpose_mul, transpose_mul, Matrix.mul_assoc]

omit [Fintype m] [Fintype n] in
/-- Row vectorization preserves and reflects equality of matrices. -/
theorem vectorization_injective : Function.Injective (vectorization (m := m) (n := n)) :=
  fun _ _ h => transpose_injective (vec_inj.mp h)

/-- **Equation (12)**. Two inner inverses give an inner inverse of the
Kronecker product. -/
theorem kronecker_innerInverse {A : Matrix m n ℂ} {B : Matrix p q ℂ}
    {U : Matrix n m ℂ} {V : Matrix q p ℂ} (hU : A.IsInnerInverse U)
    (hV : B.IsInnerInverse V) :
    (A ⊗ₖ B).IsInnerInverse (U ⊗ₖ V) := by
  rw [isInnerInverse_iff, ← mul_kronecker_mul, ← mul_kronecker_mul,
    isInnerInverse_iff.mp hU, isInnerInverse_iff.mp hV]

/-- **Equation (13)**. Ordinary transposition preserves the
inner-inverse relation. -/
theorem transpose_innerInverse {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    (hU : A.IsInnerInverse U) : Aᵀ.IsInnerInverse Uᵀ := by
  rw [isInnerInverse_iff, ← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc,
    isInnerInverse_iff.mp hU]

/-- **Exercise 3** of [benIsrael2003generalized]. The Moore–Penrose
inverse preserves Kronecker products. -/
theorem pinv_kronecker [DecidableEq n] [DecidableEq q]
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    (A ⊗ₖ B).pinv = A.pinv ⊗ₖ B.pinv := by
  classical
  symm
  apply (A ⊗ₖ B).pinv_unique
  · rw [← mul_kronecker_mul, ← mul_kronecker_mul, A.mul_pinv_mul_self, B.mul_pinv_mul_self]
  · rw [← mul_kronecker_mul, ← mul_kronecker_mul,
      A.pinv_mul_self_mul_pinv, B.pinv_mul_self_mul_pinv]
  · rw [← mul_kronecker_mul, IsHermitian, conjTranspose_kronecker,
      A.isHermitian_mul_pinv.eq, B.isHermitian_mul_pinv.eq]
  · rw [← mul_kronecker_mul, IsHermitian, conjTranspose_kronecker,
      A.isHermitian_pinv_mul.eq, B.isHermitian_pinv_mul.eq]

/-- **Exercise 4**, Equation (14) of [benIsrael2003generalized]. The
two matrix equations have a common solution exactly when each is
consistent and their right-hand sides satisfy the compatibility equation. -/
theorem commonSolution (A : Matrix m n ℂ) (B : Matrix m p ℂ) (D : Matrix p q ℂ)
    (E : Matrix n q ℂ) (U : Matrix n m ℂ) (V : Matrix q p ℂ)
    (hU : A.IsInnerInverse U) (hV : D.IsInnerInverse V) :
    (∃ X : Matrix n p ℂ, A * X = B ∧ X * D = E) ↔
      (∃ X : Matrix n p ℂ, A * X = B) ∧ (∃ X : Matrix n p ℂ, X * D = E) ∧ A * E = B * D := by
  have hA := isInnerInverse_iff.mp hU
  have hD := isInnerInverse_iff.mp hV
  constructor
  · rintro ⟨X, rfl, rfl⟩
    exact ⟨⟨X, rfl⟩, ⟨X, rfl⟩, (Matrix.mul_assoc A X D).symm⟩
  · rintro ⟨⟨X₁, h₁⟩, ⟨X₂, h₂⟩, h⟩
    have hB : A * (U * B) = B := by rw [← h₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA]
    have hE : E * V * D = E := by rw [← h₂, Matrix.mul_assoc X₂, Matrix.mul_assoc X₂, hD]
    refine ⟨U * B + E * V - U * A * E * V, ?_, ?_⟩
    · rw [Matrix.mul_sub, Matrix.mul_add, hB,
        show A * (U * A * E * V) = (A * U * A) * (E * V) by simp only [Matrix.mul_assoc],
        hA, add_sub_cancel_right]
    · rw [Matrix.sub_mul, Matrix.add_mul, hE,
        show U * A * E * V * D = U * A * (E * V * D) by simp only [Matrix.mul_assoc],
        hE, Matrix.mul_assoc U A E, h, ← Matrix.mul_assoc]
      abel

/-- **Exercise 5**, Equation (15) of [benIsrael2003generalized]. All
common solutions are the stated affine family around any one solution. -/
theorem commonSolution_iff [DecidableEq n] [DecidableEq p]
    {A : Matrix m n ℂ} {B : Matrix m p ℂ} {D : Matrix p q ℂ} {E : Matrix n q ℂ}
    {U : Matrix n m ℂ} {V : Matrix q p ℂ} (hU : A.IsInnerInverse U) (hV : D.IsInnerInverse V)
    {X₀ : Matrix n p ℂ} (hB : A * X₀ = B) (hE : X₀ * D = E) (X : Matrix n p ℂ) :
    A * X = B ∧ X * D = E ↔
      ∃ Y : Matrix n p ℂ, X = X₀ + (1 - U * A) * Y * (1 - D * V) := by
  constructor
  · rintro ⟨hX, hY⟩
    let Z := X - X₀
    have hAZ : A * Z = 0 := by rw [Matrix.mul_sub, hX, hB, sub_self]
    have hZD : Z * D = 0 := by rw [Matrix.sub_mul, hY, hE, sub_self]
    refine ⟨Z, ?_⟩
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc U A Z, hAZ, Matrix.mul_zero, sub_zero,
      Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc Z D V, hZD, Matrix.zero_mul, sub_zero]
    dsimp only [Z]
    abel
  · rintro ⟨Y, rfl⟩
    have hL : A * (1 - U * A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, isInnerInverse_iff.mp hU, sub_self]
    have hR : (1 - D * V) * D = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, isInnerInverse_iff.mp hV, sub_self]
    constructor
    · rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL,
        Matrix.zero_mul, Matrix.zero_mul, add_zero, hB]
    · rw [Matrix.add_mul, Matrix.mul_assoc _ (1 - D * V), hR, Matrix.mul_zero, add_zero, hE]

end BenIsraelGreville.Chapter02
