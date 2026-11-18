/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse
import Numlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Introduction

The ordinary inverse of a nonsingular matrix is unique. The equation $AXA=A$ extends the
solution formula for a nonsingular system to all consistent systems, including rectangular
ones. These are the results in the Introduction of [benIsrael2003generalized].

## Main definitions

* `BenIsraelGreville.Introduction.IsGeneralizedInverse` is the relation $AXA=A$.

## Main results

* `BenIsraelGreville.Introduction.existsUnique_inverse` gives the unique ordinary inverse.
* `BenIsraelGreville.Introduction.solution_iff_exists_eq_generalSolution` parametrizes the
  solutions of a consistent system using an inner inverse.
-/

namespace BenIsraelGreville.Introduction

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

section OrdinaryInverse

variable [DecidableEq n] {A B X : Matrix n n ℂ}

/-- A nonsingular complex matrix has a unique two-sided inverse.
[benIsrael2003generalized], Introduction, Equation (1). -/
theorem existsUnique_inverse (hA : IsUnit A) : ∃! X, A * X = 1 ∧ X * A = 1 :=
  ⟨A⁻¹, ⟨A.mul_nonsing_inv ((isUnit_iff_isUnit_det A).mp hA),
    A.nonsing_inv_mul ((isUnit_iff_isUnit_det A).mp hA)⟩,
    fun _ hX => (inv_eq_right_inv hX.1).symm⟩

/-- Inverting a nonsingular matrix twice recovers the original matrix.
[benIsrael2003generalized], Introduction, §1. -/
theorem inv_inv (hA : IsUnit A) : A⁻¹⁻¹ = A :=
  A.nonsing_inv_nonsing_inv ((isUnit_iff_isUnit_det A).mp hA)

/-- Inversion commutes with transposition.
[benIsrael2003generalized], Introduction, §1. -/
theorem inv_transpose (A : Matrix n n ℂ) : Aᵀ⁻¹ = A⁻¹ᵀ :=
  (A.transpose_nonsing_inv).symm

/-- Inversion commutes with conjugate transposition.
[benIsrael2003generalized], Introduction, §1. -/
theorem inv_conjTranspose (A : Matrix n n ℂ) : Aᴴ⁻¹ = A⁻¹ᴴ :=
  (A.conjTranspose_nonsing_inv).symm

/-- The inverse of a product of nonsingular matrices is the product of their inverses in
reverse order. [benIsrael2003generalized], Introduction, §1. -/
theorem inv_mul (hA : IsUnit A) (hB : IsUnit B) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  apply inv_eq_right_inv
  rw [Matrix.mul_assoc A, ← Matrix.mul_assoc B, B.mul_nonsing_inv
    ((isUnit_iff_isUnit_det B).mp hB), Matrix.one_mul,
    A.mul_nonsing_inv ((isUnit_iff_isUnit_det A).mp hA)]

/-- An eigenvector of a nonsingular matrix is an eigenvector of the inverse at the reciprocal
eigenvalue. [benIsrael2003generalized], Introduction, §1 and Exercise 1. -/
theorem eigenvector_inv (hA : IsUnit A) {x : n → ℂ} (hx : x ≠ 0) {μ : ℂ}
    (h : A *ᵥ x = μ • x) : μ ≠ 0 ∧ A⁻¹ *ᵥ x = μ⁻¹ • x := by
  have hμ : μ ≠ 0 := by
    intro hμ
    apply hx
    have h' : A *ᵥ x = A *ᵥ (0 : n → ℂ) := by
      rw [h, hμ, zero_smul, mulVec_zero]
    exact (mulVec_injective_iff_isUnit.mpr hA) h'
  refine ⟨hμ, (nonsing_inv_mulVec_eq hA ?_)⟩
  rw [mulVec_smul, h, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- Nonsingularity is equivalent to linear independence of the rows, and equivalently of the
columns. [benIsrael2003generalized], Introduction, §2. -/
theorem isUnit_iff_linearIndependent_rows_cols (A : Matrix n n ℂ) :
    (IsUnit A ↔ LinearIndependent ℂ A.row) ∧ (IsUnit A ↔ LinearIndependent ℂ A.col) :=
  ⟨linearIndependent_row_iff_isUnit.symm, linearIndependent_col_iff_isUnit.symm⟩

end OrdinaryInverse

/-- An inner inverse $X$ of $A$ satisfies $AXA=A$.
[benIsrael2003generalized], Introduction, Equation (2). -/
abbrev IsGeneralizedInverse (A : Matrix m n ℂ) (X : Matrix n m ℂ) : Prop :=
  A.IsInnerInverse X

/-- For a nonsingular matrix $A$, a matrix satisfying $AXA=A$ is the ordinary inverse.
[benIsrael2003generalized], Introduction, §2. -/
theorem generalizedInverse_eq_inv [DecidableEq n] {A X : Matrix n n ℂ}
    (hA : IsUnit A) (hX : IsGeneralizedInverse A X) : X = A⁻¹ := by
  have h := (Matrix.isInnerInverse_iff).mp hX
  have hAX : A * X = 1 := by
    have h' := congrArg (· * A⁻¹) h
    rwa [Matrix.mul_assoc (A * X), A.mul_nonsing_inv ((isUnit_iff_isUnit_det A).mp hA),
      Matrix.mul_one] at h'
  exact (inv_eq_right_inv hAX).symm

/-- For nonsingular $A$, the unique solution of $Ax=b$ is $A^{-1}b$.
[benIsrael2003generalized], Introduction, §3. -/
theorem solution_iff_eq_inv_mulVec [DecidableEq n] {A : Matrix n n ℂ} (hA : IsUnit A)
    {x b : n → ℂ} : A *ᵥ x = b ↔ x = A⁻¹ *ᵥ b :=
  ⟨fun h => (nonsing_inv_mulVec_eq hA h).symm,
    fun h => by rw [h, mulVec_nonsing_inv_mulVec hA]⟩

omit [Fintype m] in
/-- A system $Ax=b$ has a solution exactly when $b$ belongs to the span of the columns of $A$.
[benIsrael2003generalized], Introduction, §3. -/
theorem solvable_iff_mem_columnSpan (A : Matrix m n ℂ) (b : m → ℂ) :
    (∃ x, A *ᵥ x = b) ↔ b ∈ Submodule.span ℂ (Set.range A.col) := by
  rw [← Matrix.range_mulVecLin]
  rfl

/-- Under $AXA=A$, consistency of $Ax=b$ is equivalent to $AXb=b$.
[benIsrael2003generalized], Introduction, §3 and Exercise 3. -/
theorem solvable_iff_mul_mulVec_eq {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (hX : IsGeneralizedInverse A X) (b : m → ℂ) :
    (∃ x, A *ᵥ x = b) ↔ (A * X) *ᵥ b = b := by
  have h := (Matrix.isInnerInverse_iff).mp hX
  constructor
  · rintro ⟨x, rfl⟩
    rw [mulVec_mulVec, h]
  · intro hb
    exact ⟨X *ᵥ b, (mulVec_mulVec ..).trans hb⟩

/-- If $AXA=A$ and $AXb=b$, then $x$ solves $Ax=b$ exactly when it has the form
$Xb+(I-XA)y$ for a vector $y$.
[benIsrael2003generalized], Introduction, Equation (4) and Exercise 4. -/
theorem solution_iff_exists_eq_generalSolution [DecidableEq n] {A : Matrix m n ℂ}
    {X : Matrix n m ℂ} (hX : IsGeneralizedInverse A X) {b : m → ℂ}
    (hb : (A * X) *ᵥ b = b) (x : n → ℂ) :
    A *ᵥ x = b ↔ ∃ y, x = X *ᵥ b + (1 - X * A) *ᵥ y := by
  have h := (Matrix.isInnerInverse_iff).mp hX
  constructor
  · intro hx
    refine ⟨x, ?_⟩
    rw [← hx, mulVec_mulVec, sub_mulVec, one_mulVec, add_sub_cancel]
  · rintro ⟨y, rfl⟩
    have hzero : A * (1 - X * A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, sub_self]
    rw [mulVec_add, mulVec_mulVec, hb, mulVec_mulVec, hzero, zero_mulVec, add_zero]

/-- The identity $AXA=A$ is equivalent to $Xb$ solving $Ax=b$ for every consistent right
hand side. [benIsrael2003generalized], Introduction, §4 and Exercise 7. -/
theorem generalizedInverse_iff_solves_consistent (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    IsGeneralizedInverse A X ↔
      ∀ b, (∃ x, A *ᵥ x = b) → A *ᵥ (X *ᵥ b) = b := by
  constructor
  · intro hX b hb
    rw [mulVec_mulVec]
    exact (solvable_iff_mul_mulVec_eq hX b).mp hb
  · intro hX
    apply (Matrix.isInnerInverse_iff).mpr
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    simpa only [mulVec_mulVec, Matrix.mul_assoc] using hX (A *ᵥ x) ⟨x, rfl⟩

end BenIsraelGreville.Introduction
