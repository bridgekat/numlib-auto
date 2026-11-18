/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section01
import Mathlib.Data.Matrix.Block

/-!
# Inner inverses from Hermite form

Section 1.2 of [benIsrael2003generalized] constructs inner inverses by applying invertible
row and column operations to a block matrix with an identity in its leading block.
-/

namespace BenIsraelGreville.Chapter01

open Matrix

variable {r m n : Type*} [Fintype r] [Fintype m] [Fintype n]

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 1. When $EAP$ is in the block
form $[I,K;0,0]$ with $E$ and $P$ nonsingular, $P[I,0;0,L]E$ is an inner inverse
of $A$ for any block $L$. The dimensions of the other blocks may be zero. -/
theorem theorem_1 [DecidableEq r] [DecidableEq m] [DecidableEq n]
    {A : Matrix (r ⊕ m) (r ⊕ n) ℂ}
    {E : Matrix (r ⊕ m) (r ⊕ m) ℂ} {P : Matrix (r ⊕ n) (r ⊕ n) ℂ}
    (hE : IsUnit E) (hP : IsUnit P) (K : Matrix r n ℂ)
    (h : E * A * P = fromBlocks 1 K 0 0) (L : Matrix n m ℂ) :
    P * fromBlocks 1 0 0 L * E ∈ definition_1 A {.inner} := by
  let R : Matrix (r ⊕ m) (r ⊕ n) ℂ := fromBlocks 1 K 0 0
  let S : Matrix (r ⊕ n) (r ⊕ m) ℂ := fromBlocks 1 0 0 L
  change E * A * P = R at h
  have hR : R * S * R = R := by
    dsimp only [R, S]
    simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
  have hE' := E.nonsing_inv_mul ((isUnit_iff_isUnit_det _).mp hE)
  have hP' := P.mul_nonsing_inv ((isUnit_iff_isUnit_det _).mp hP)
  have hcancel : ∀ B : Matrix (r ⊕ m) (r ⊕ n) ℂ, E⁻¹ * (E * B * P) * P⁻¹ = B := by
    intro B
    calc
      E⁻¹ * (E * B * P) * P⁻¹ = (E⁻¹ * E) * B * (P * P⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hE', hP', Matrix.one_mul, Matrix.mul_one]
  rw [mem_one_iff, isInnerInverse_iff]
  change A * (P * S * E) * A = A
  calc
    A * (P * S * E) * A = E⁻¹ * (E * (A * (P * S * E) * A) * P) * P⁻¹ :=
      (hcancel _).symm
    _ = E⁻¹ * ((E * A * P) * S * (E * A * P)) * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = E⁻¹ * (E * A * P) * P⁻¹ := by rw [h, hR]
    _ = A := hcancel _

/-- **Section 1.2** of [benIsrael2003generalized]. Every complex matrix has an inner inverse. -/
theorem exists_innerInverse (A : Matrix m n ℂ) : (definition_1 A {.inner}).Nonempty := by
  classical
  exact ⟨A.pinv, mem_one_iff.mpr A.mul_pinv_mul_self⟩

end BenIsraelGreville.Chapter01
