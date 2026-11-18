/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# The Penrose equations

Section 1.1 of [benIsrael2003generalized] defines a class of generalized inverses for each set
of Penrose equations. The class for all four equations contains only the Moore–Penrose inverse.
-/

namespace BenIsraelGreville.Chapter01

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Definition 1** of [benIsrael2003generalized], Chapter 1. For a set $s$ of Penrose
equations, $A\{s\}$ consists of the matrices satisfying each equation in $s$ for $A$. -/
abbrev definition_1 (A : Matrix m n ℂ) (s : Set PenroseCondition) : Set (Matrix n m ℂ) :=
  A.penroseInverses s

/-- A matrix belongs to $A\{1\}$ exactly when it is an inner inverse of $A$. -/
theorem mem_one_iff {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    X ∈ definition_1 A {.inner} ↔ A.IsInnerInverse X := by
  change (∀ c ∈ ({.inner} : Set PenroseCondition), c.Holds A X) ↔ PenroseCondition.inner.Holds A X
  simp only [Set.mem_singleton_iff, forall_eq]

/-- A matrix belongs to $A\{2\}$ exactly when it is an outer inverse of $A$. -/
theorem mem_two_iff {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    X ∈ definition_1 A {.outer} ↔ A.IsOuterInverse X := by
  change (∀ c ∈ ({.outer} : Set PenroseCondition), c.Holds A X) ↔ (PenroseCondition.outer).Holds A X
  simp only [Set.mem_singleton_iff, forall_eq]

/-- A matrix belongs to $A\{1,2\}$ exactly when it is both an inner and an outer inverse of $A$. -/
theorem mem_one_two_iff {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    X ∈ definition_1 A {.inner, .outer} ↔ A.IsInnerInverse X ∧ A.IsOuterInverse X := by
  change (∀ c ∈ ({.inner, .outer} : Set PenroseCondition), c.Holds A X) ↔
    (PenroseCondition.inner).Holds A X ∧ (PenroseCondition.outer).Holds A X
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

/-- A matrix belongs to $A\{1,3\}$ exactly when it is an inner inverse and $AX$ is Hermitian. -/
theorem mem_one_three_iff {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    X ∈ definition_1 A {.inner, .hermitianMul} ↔ A.IsInnerInverse X ∧ (A * X).IsHermitian := by
  change (∀ c ∈ ({.inner, .hermitianMul} : Set PenroseCondition), c.Holds A X) ↔
    (PenroseCondition.inner).Holds A X ∧ (PenroseCondition.hermitianMul).Holds A X
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

/-- A matrix belongs to $A\{1,4\}$ exactly when it is an inner inverse and $XA$ is Hermitian. -/
theorem mem_one_four_iff {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    X ∈ definition_1 A {.inner, .hermitianMulRev} ↔ A.IsInnerInverse X ∧ (X * A).IsHermitian := by
  change (∀ c ∈ ({.inner, .hermitianMulRev} : Set PenroseCondition), c.Holds A X) ↔
    (PenroseCondition.inner).Holds A X ∧ (PenroseCondition.hermitianMulRev).Holds A X
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

/-- **Equations (1)–(4)** of [benIsrael2003generalized], Chapter 1. Every complex matrix
has exactly one generalized inverse satisfying all four Penrose equations. -/
theorem existsUnique_penrose (A : Matrix m n ℂ) :
    ∃! X, X ∈ definition_1 A Set.univ := by
  classical
  change ∃! X, X ∈ A.penroseInverses Set.univ
  rw [A.penroseInverses_univ]
  exact ⟨A.pinv, Set.mem_singleton _, fun _ h => h⟩

/-- **Section 1.1** of [benIsrael2003generalized]. The Moore–Penrose inverse of a nonsingular
square matrix is its ordinary inverse. -/
theorem pinv_eq_inv [DecidableEq n] {A : Matrix n n ℂ} (hA : IsUnit A) :
    A.pinv = A⁻¹ :=
  Matrix.pinv_eq_inv hA

end BenIsraelGreville.Chapter01
