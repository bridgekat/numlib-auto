/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter02.Section07

/-!
# Restricted generalized inverses

Section 2.9 of [benIsrael2003generalized] solves $Ax=b$ with $x$ restricted to a subspace
$S$. Composing $A$ with the orthogonal projector onto $S$ gives the unconstrained
system used to construct restricted inverses.
-/

namespace BenIsraelGreville.Chapter02

open Matrix
open BenIsraelGreville.Chapter01 (definition_1 mem_one_iff)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Equation (117)** of [benIsrael2003generalized], Chapter 2. The restriction to $S$
applies the original map to vectors from $S$. -/
def restrictToSubspace {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℂ V] [Module ℂ W] (A : V →ₗ[ℂ] W) (S : Submodule ℂ V) : S →ₗ[ℂ] W :=
  A.comp S.subtype

/-- **Equation (118)** of [benIsrael2003generalized], Chapter 2. The extension of a map
from $S$ agrees with it on $S$ and sends its orthogonal complement to zero. -/
noncomputable def extendFromSubspace {V W : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ V) [S.HasOrthogonalProjection] (A : S →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  A.comp S.orthogonalProjectionOnto.toLinearMap

omit [Fintype m] in
/-- **Equation (119)** of [benIsrael2003generalized], Chapter 2. The extension of the
restriction of $A$ to $S$ is represented by $AP_S$. -/
theorem extend_restrict (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n)) :
    extendFromSubspace S (restrictToSubspace (toEuclideanLin A) S) =
      toEuclideanLin (A * orthogonalProjector S) := by
  rw [toEuclideanLin_mul, toEuclideanLin_orthogonalProjector]
  rfl

omit [Fintype m] in
/-- **Lemma 4** of [benIsrael2003generalized], Chapter 2. The solutions of $Ax=b$
in $S$ are precisely the projections of the solutions of $AP_S z=b$ onto $S$. -/
theorem lemma_4 (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    x ∈ S ∧ toEuclideanLin A x = b ↔
      ∃ z : EuclideanSpace ℂ n, toEuclideanLin (A * orthogonalProjector S) z = b ∧
        x = toEuclideanLin (orthogonalProjector S) z := by
  constructor
  · rintro ⟨hx, h⟩
    have hP : toEuclideanLin (orthogonalProjector S) x = x := by
      rw [toEuclideanLin_orthogonalProjector]
      exact S.starProjection_eq_self_iff.mpr hx
    refine ⟨x, ?_, hP.symm⟩
    rw [toEuclideanLin_mul_apply, hP, h]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [toEuclideanLin_orthogonalProjector]
      exact S.starProjection_apply_mem _
    · rwa [← toEuclideanLin_mul_apply]

/-- **Definition 2** of [benIsrael2003generalized], Chapter 2. An $S$-restricted inverse
satisfying the selected equations has the form $P_S Y$ where $Y$ satisfies those equations
for $AP_S$. -/
def definition_2 (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (c : Set PenroseCondition) (X : Matrix n m ℂ) : Prop :=
  ∃ Y ∈ definition_1 (A * orthogonalProjector S) c, X = orthogonalProjector S * Y

/-- **Corollary 11** of [benIsrael2003generalized], Chapter 2. For a restricted inner inverse
$X$, the constrained system is consistent precisely when $AXb=b$. Its solutions are
$Xb+(I-XA)y$ for arbitrary $y\in S$. -/
theorem corollary_11 [DecidableEq m] (A : Matrix m n ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ n)) (b : EuclideanSpace ℂ m)
    {X : Matrix n m ℂ} (hX : definition_2 A S {.inner} X) :
    ((∃ x ∈ S, toEuclideanLin A x = b) ↔ toEuclideanLin (A * X) b = b) ∧
      (toEuclideanLin (A * X) b = b → ∀ x : EuclideanSpace ℂ n,
        (x ∈ S ∧ toEuclideanLin A x = b) ↔
          ∃ y ∈ S, x = toEuclideanLin X b + toEuclideanLin (1 - X * A) y) := by
  obtain ⟨Y, hy, rfl⟩ := hX
  let P := orthogonalProjector S
  let X := P * Y
  have hi : A * X * (A * P) = A * P := calc
    A * X * (A * P) = (A * P) * Y * (A * P) := by dsimp only [X]; simp only [Matrix.mul_assoc]
    _ = _ := isInnerInverse_iff.mp (mem_one_iff.mp hy)
  have hMap (v : EuclideanSpace ℂ m) : toEuclideanLin X v ∈ S := by
    change toEuclideanLin (P * Y) v ∈ S
    rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
    exact S.starProjection_apply_mem _
  have hProj (v : EuclideanSpace ℂ n) (hv : v ∈ S) :
      toEuclideanLin A (toEuclideanLin X (toEuclideanLin A v)) = toEuclideanLin A v := by
    have hP : toEuclideanLin P v = v := by
      rw [toEuclideanLin_orthogonalProjector]
      exact S.starProjection_eq_self_iff.mpr hv
    have hi' := congrArg (fun M => toEuclideanLin M v) hi
    simpa only [toEuclideanLin_mul_apply, hP] using hi'
  change ((∃ x ∈ S, toEuclideanLin A x = b) ↔ toEuclideanLin (A * X) b = b) ∧ _
  constructor
  · constructor
    · rintro ⟨v, hv, rfl⟩
      rw [toEuclideanLin_mul_apply, hProj v hv]
    · intro h
      exact ⟨toEuclideanLin X b, hMap b, (toEuclideanLin_mul_apply A X b).symm ▸ h⟩
  · intro hb x
    change (x ∈ S ∧ toEuclideanLin A x = b) ↔
      ∃ y ∈ S, x = toEuclideanLin X b + toEuclideanLin (1 - X * A) y
    constructor
    · rintro ⟨hx, he⟩
      refine ⟨x, hx, ?_⟩
      rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply X A x, he,
        add_sub_cancel]
    · rintro ⟨y, hy, rfl⟩
      have hdiff : toEuclideanLin (1 - X * A) y = y - toEuclideanLin X (toEuclideanLin A y) := by
        rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply]
      constructor
      · exact S.add_mem (hMap b) (hdiff.symm ▸ S.sub_mem hy (hMap _))
      · rw [hdiff, map_add, map_sub, hProj y hy, sub_self, add_zero, ← toEuclideanLin_mul_apply]
        exact hb

end BenIsraelGreville.Chapter02
