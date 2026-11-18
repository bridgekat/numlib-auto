/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section01

/-!
# Reflexive inverses

Section 1.4 of [benIsrael2003generalized] constructs a reflexive inverse and characterizes
reflexive inverses among inner inverses by equality of ranks.
-/

namespace BenIsraelGreville.Chapter01

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]
  {A : Matrix m n ℂ} {X Y Z : Matrix n m ℂ}

/-- **Lemma 3** of [benIsrael2003generalized], Chapter 1. If $Y$ and $Z$ are inner inverses
of $A$, then $YAZ$ is a $\{1,2\}$-inverse of $A$. -/
theorem lemma_3 (hY : Y ∈ definition_1 A {.inner}) (hZ : Z ∈ definition_1 A {.inner}) :
    Y * A * Z ∈ definition_1 A {.inner, .outer} := by
  rw [mem_one_iff] at hY hZ
  exact mem_one_two_iff.mpr ⟨hY.isInnerInverse_mul hZ, hY.isOuterInverse_mul hZ⟩

/-- **Section 1.4** of [benIsrael2003generalized]. The $\{1,2\}$-inverse relation is symmetric. -/
theorem mutual_reflexiveInverse :
    X ∈ definition_1 A {.inner, .outer} ↔ A ∈ definition_1 X {.inner, .outer} := by
  rw [mem_one_two_iff, mem_one_two_iff, and_comm]
  rfl

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 1. An inner inverse is reflexive if
and only if its rank equals that of the original matrix. -/
theorem theorem_2 (hX : X ∈ definition_1 A {.inner}) :
    X ∈ definition_1 A {.inner, .outer} ↔ X.rank = A.rank := by
  rw [mem_one_iff] at hX
  rw [mem_one_two_iff, and_iff_right hX]
  exact hX.isOuterInverse_iff_rank_eq

/-- **Corollary 1** of [benIsrael2003generalized], Chapter 1. Any two of the inner inverse
equation, the outer inverse equation and equality of ranks imply the third. -/
theorem corollary_1 :
    (X ∈ definition_1 A {.inner} → X ∈ definition_1 A {.outer} → X.rank = A.rank) ∧
    (X ∈ definition_1 A {.inner} → X.rank = A.rank → X ∈ definition_1 A {.outer}) ∧
    (X ∈ definition_1 A {.outer} → X.rank = A.rank → X ∈ definition_1 A {.inner}) := by
  refine ⟨fun h₁ h₂ => (theorem_2 h₁).mp (mem_one_two_iff.mpr
    ⟨mem_one_iff.mp h₁, mem_two_iff.mp h₂⟩), ?_, ?_⟩
  · intro h₁ hrank
    exact mem_two_iff.mpr (mem_one_two_iff.mp ((theorem_2 h₁).mpr hrank)).2
  · intro h₂ hrank
    have hInner : X.IsInnerInverse A := isOuterInverse_iff_isInnerInverse.mp (mem_two_iff.mp h₂)
    exact mem_one_iff.mpr (isOuterInverse_iff_isInnerInverse.mp
      (hInner.isOuterInverse_iff_rank_eq.mpr hrank.symm))

end BenIsraelGreville.Chapter01
