/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.SVD
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generalized inverses of rectangular matrices

An inner inverse satisfies $AXA=A$ and an outer inverse satisfies $XAX=X$. The Penrose
conditions include these two equations and require the two products $AX$ and $XA$ to be
Hermitian. Over real or complex scalars, their common solution is the Moore–Penrose inverse.
-/

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

section Semiring

variable {R : Type*} [Semiring R] {A : Matrix m n R} {X Y Z : Matrix n m R}

/-- A matrix $X$ is an **inner inverse** of $A$ if $AXA=A$. -/
def IsInnerInverse (A : Matrix m n R) (X : Matrix n m R) : Prop :=
  A * X * A = A

/-- A matrix $X$ is an **outer inverse** of $A$ if $XAX=X$. -/
def IsOuterInverse (A : Matrix m n R) (X : Matrix n m R) : Prop :=
  X * A * X = X

/-- The inner inverse relation is the first Penrose equation. -/
theorem isInnerInverse_iff : A.IsInnerInverse X ↔ A * X * A = A :=
  Iff.rfl

/-- The outer inverse relation is the second Penrose equation. -/
theorem isOuterInverse_iff : A.IsOuterInverse X ↔ X * A * X = X :=
  Iff.rfl

/-- Being an outer inverse of $A$ is equivalent to having $A$ as an inner inverse. -/
theorem isOuterInverse_iff_isInnerInverse : A.IsOuterInverse X ↔ X.IsInnerInverse A :=
  Iff.rfl

/-- If $X$ is an inner inverse of $A$, then $AX$ is idempotent. -/
theorem IsInnerInverse.isIdempotentElem_mul (h : A.IsInnerInverse X) :
    IsIdempotentElem (A * X) := by
  change (A * X) * (A * X) = A * X
  rw [← Matrix.mul_assoc, isInnerInverse_iff.mp h]

/-- If $X$ is an inner inverse of $A$, then $XA$ is idempotent. -/
theorem IsInnerInverse.isIdempotentElem_mul_rev (h : A.IsInnerInverse X) :
    IsIdempotentElem (X * A) := by
  change (X * A) * (X * A) = X * A
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, isInnerInverse_iff.mp h]

/-- Multiplying $YAZ$ on the left by $A$ gives $AZ$ when $Y$ is an inner inverse. -/
theorem IsInnerInverse.mul_mul_inner (hY : A.IsInnerInverse Y) :
    A * (Y * A * Z) = A * Z := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, isInnerInverse_iff.mp hY]

/-- Multiplying $YAZ$ on the right by $A$ gives $YA$ when $Z$ is an inner inverse. -/
theorem IsInnerInverse.inner_mul_mul (hZ : A.IsInnerInverse Z) :
    (Y * A * Z) * A = Y * A := by
  calc
    (Y * A * Z) * A = Y * (A * Z * A) := by simp only [Matrix.mul_assoc]
    _ = Y * A := by rw [isInnerInverse_iff.mp hZ]

/-- The product $YAZ$ of two inner inverses with $A$ is an inner inverse of $A$. -/
theorem IsInnerInverse.isInnerInverse_mul (hY : A.IsInnerInverse Y)
    (hZ : A.IsInnerInverse Z) : A.IsInnerInverse (Y * A * Z) := by
  rw [isInnerInverse_iff, hY.mul_mul_inner]
  exact hZ

/-- The product $YAZ$ of two inner inverses with $A$ is also an outer inverse of $A$. -/
theorem IsInnerInverse.isOuterInverse_mul (hY : A.IsInnerInverse Y)
    (hZ : A.IsInnerInverse Z) : A.IsOuterInverse (Y * A * Z) := by
  rw [isOuterInverse_iff, hZ.inner_mul_mul]
  calc
    Y * A * (Y * A * Z) = Y * (A * (Y * A * Z)) := Matrix.mul_assoc _ _ _
    _ = Y * (A * Z) := by rw [hY.mul_mul_inner]
    _ = Y * A * Z := (Matrix.mul_assoc _ _ _).symm

end Semiring

section Field

variable {K : Type*} [Field K] {A : Matrix m n K} {X : Matrix n m K}

/-- An inner inverse has rank at least that of the original matrix. -/
theorem IsInnerInverse.rank_le (h : A.IsInnerInverse X) : A.rank ≤ X.rank := by
  calc
    A.rank = (A * X * A).rank := congrArg rank (isInnerInverse_iff.mp h).symm
    _ ≤ (A * X).rank := rank_mul_le_left _ _
    _ ≤ X.rank := rank_mul_le_right _ _

/-- An outer inverse has rank at most that of the original matrix. -/
theorem IsOuterInverse.rank_le (h : A.IsOuterInverse X) : X.rank ≤ A.rank :=
  (isOuterInverse_iff_isInnerInverse.mp h).rank_le

/-- If $X$ is an inner inverse of $A$, then $AX$ has rank equal to that of $A$. -/
theorem IsInnerInverse.rank_mul (h : A.IsInnerInverse X) : (A * X).rank = A.rank := by
  refine le_antisymm (rank_mul_le_left ..) ?_
  simpa only [isInnerInverse_iff.mp h] using rank_mul_le_left (A * X) A

/-- If $X$ is an inner inverse of $A$, then $XA$ has rank equal to that of $A$. -/
theorem IsInnerInverse.rank_mul_rev (h : A.IsInnerInverse X) : (X * A).rank = A.rank := by
  refine le_antisymm (rank_mul_le_right ..) ?_
  simpa only [← Matrix.mul_assoc, isInnerInverse_iff.mp h] using rank_mul_le_right A (X * A)

/-- An inner inverse is an outer inverse if and only if it has the same rank as the matrix. -/
theorem IsInnerInverse.isOuterInverse_iff_rank_eq (h : A.IsInnerInverse X) :
    A.IsOuterInverse X ↔ X.rank = A.rank := by
  refine ⟨fun h' => le_antisymm h'.rank_le h.rank_le, fun hRank => ?_⟩
  have hle : LinearMap.range (X * A).mulVecLin ≤ LinearMap.range X.mulVecLin := by
    rw [mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hrange := Submodule.eq_of_le_of_finrank_eq hle (h.rank_mul_rev.trans hRank.symm)
  rw [isOuterInverse_iff, ext_iff_mulVec]
  intro v
  change (X * A * X).mulVecLin v = X.mulVecLin v
  have hv : X.mulVecLin v ∈ LinearMap.range (X * A).mulVecLin := by
    rw [hrange]
    exact LinearMap.mem_range_self _ _
  obtain ⟨u, hu⟩ := hv
  rw [mulVecLin_mul, LinearMap.comp_apply, ← hu, ← LinearMap.comp_apply, ← mulVecLin_mul,
    h.isIdempotentElem_mul_rev.eq]

end Field

/-- The four equations that characterize the Moore–Penrose inverse. -/
inductive PenroseCondition
  /-- The first Penrose equation, $AXA=A$. -/
  | inner
  /-- The second Penrose equation, $XAX=X$. -/
  | outer
  /-- The third Penrose equation, $(AX)^H=AX$. -/
  | hermitianMul
  /-- The fourth Penrose equation, $(XA)^H=XA$. -/
  | hermitianMulRev
  deriving DecidableEq

section Star

variable {R : Type*} [Semiring R] [Star R]

/-- The proposition that $X$ satisfies a specified Penrose equation for $A$. -/
def PenroseCondition.Holds (A : Matrix m n R) (X : Matrix n m R) :
    PenroseCondition → Prop
  | .inner => A.IsInnerInverse X
  | .outer => A.IsOuterInverse X
  | .hermitianMul => (A * X).IsHermitian
  | .hermitianMulRev => (X * A).IsHermitian

/-- The matrices that satisfy every Penrose equation in a given set. -/
def penroseInverses (A : Matrix m n R) (s : Set PenroseCondition) : Set (Matrix n m R) :=
  {X | ∀ c ∈ s, c.Holds A X}

/-- Membership in the class associated with $s$ means satisfying every condition in $s$. -/
theorem mem_penroseInverses_iff {A : Matrix m n R} {X : Matrix n m R}
    {s : Set PenroseCondition} : X ∈ A.penroseInverses s ↔ ∀ c ∈ s, c.Holds A X :=
  Iff.rfl

end Star

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n] {A : Matrix m n 𝕜}
  {Y Z : Matrix n m 𝕜}

/-- The Moore–Penrose inverse satisfies every Penrose equation. -/
theorem penroseCondition_pinv (A : Matrix m n 𝕜) (c : PenroseCondition) :
    c.Holds A A.pinv := by
  cases c
  · exact A.mul_pinv_mul_self
  · exact A.pinv_mul_self_mul_pinv
  · exact A.isHermitian_mul_pinv
  · exact A.isHermitian_pinv_mul

/-- The matrices satisfying all four Penrose equations form the singleton containing $A^\dagger$. -/
theorem penroseInverses_univ (A : Matrix m n 𝕜) :
    A.penroseInverses Set.univ = {A.pinv} := by
  ext X
  rw [Set.mem_singleton_iff, mem_penroseInverses_iff]
  refine ⟨fun h => A.pinv_unique (h .inner trivial) (h .outer trivial)
    (h .hermitianMul trivial) (h .hermitianMulRev trivial), ?_⟩
  rintro rfl c _
  exact A.penroseCondition_pinv c

/-- If $Y$ and $Z$ are inner inverses and $AZ$ and $YA$ are Hermitian, then
$YAZ$ is the Moore–Penrose inverse of $A$. -/
theorem pinv_eq_of_innerInverse_mul (hY : A.IsInnerInverse Y) (hZ : A.IsInnerInverse Z)
    (hYA : (Y * A).IsHermitian) (hAZ : (A * Z).IsHermitian) : A.pinv = Y * A * Z := by
  refine (A.pinv_unique (hY.isInnerInverse_mul hZ) (hY.isOuterInverse_mul hZ) ?_ ?_).symm
  · rwa [hY.mul_mul_inner]
  · rwa [hZ.inner_mul_mul]

end RCLike

end Matrix
