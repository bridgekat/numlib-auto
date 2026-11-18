/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section05

/-!
# The Moore–Penrose inverse of a rank factorization

Section 1.6 of [benIsrael2003generalized] gives MacDuffee's formula for the Moore–Penrose
inverse using full-rank factors and the ordinary inverse of a square middle matrix.
-/

namespace BenIsraelGreville.Chapter01

open Matrix
open scoped ComplexOrder

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq n] [DecidableEq k]

/-- **Exercise 17** of [benIsrael2003generalized], Chapter 1. If $A=FG$ is a rank factorization
with $F$ of full column rank and $G$ of full row rank, then $A^\dagger=G^\dagger F^\dagger$. -/
theorem pinv_rankFactorization (F : Matrix m k ℂ) (G : Matrix k n ℂ)
    (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) :
    (F * G).pinv = G.pinv * F.pinv := by
  have hL := (lemma_2_a (mem_one_iff.mpr F.mul_pinv_mul_self)).mpr hF
  have hR := (lemma_2_b (mem_one_iff.mpr G.mul_pinv_mul_self)).mpr hG
  have h₁ : (F * G) * (G.pinv * F.pinv) = F * F.pinv := calc
    (F * G) * (G.pinv * F.pinv) = F * (G * G.pinv) * F.pinv := by simp only [Matrix.mul_assoc]
    _ = F * F.pinv := by rw [hR, Matrix.mul_one]
  have h₂ : (G.pinv * F.pinv) * (F * G) = G.pinv * G := calc
    (G.pinv * F.pinv) * (F * G) = G.pinv * (F.pinv * F) * G := by simp only [Matrix.mul_assoc]
    _ = G.pinv * G := by rw [hL, Matrix.mul_one]
  symm
  refine (F * G).pinv_unique ?_ ?_ ?_ ?_
  · rw [h₁, ← Matrix.mul_assoc, F.mul_pinv_mul_self]
  · rw [h₂, ← Matrix.mul_assoc, G.pinv_mul_self_mul_pinv]
  · rw [h₁]
    exact F.isHermitian_mul_pinv
  · rw [h₂]
    exact G.isHermitian_pinv_mul

/-- **Theorem 5** of [benIsrael2003generalized], Chapter 1. For a full-rank factorization
$A=FG$ of positive rank, $F^H A G^H$ is nonsingular and
$A^\dagger=G^H(F^H A G^H)^{-1}F^H$. -/
theorem theorem_5 {A : Matrix m n ℂ} {F : Matrix m k ℂ} {G : Matrix k n ℂ}
    (hA : A = F * G) (_hrank : 0 < A.rank)
    (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) :
    IsUnit (Fᴴ * A * Gᴴ) ∧ A.pinv = Gᴴ * (Fᴴ * A * Gᴴ)⁻¹ * Fᴴ := by
  have hFu : IsUnit (Fᴴ * F) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (F.rank_conjTranspose_mul_self.trans hF))
  have hGu : IsUnit (G * Gᴴ) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (G.rank_self_mul_conjTranspose.trans hG))
  have hMid : Fᴴ * A * Gᴴ = (Fᴴ * F) * (G * Gᴴ) := by
    rw [hA]
    simp only [Matrix.mul_assoc]
  have hFpinv := Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hFu
  have hGpinv : G.pinv = Gᴴ * (G * Gᴴ)⁻¹ := by
    have hu : IsUnit (Gᴴᴴ * Gᴴ) := by rwa [conjTranspose_conjTranspose]
    have hh := congrArg Matrix.conjTranspose
      (Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hu)
    simpa only [Matrix.pinv_conjTranspose, conjTranspose_conjTranspose, conjTranspose_mul,
      (isHermitian_mul_conjTranspose_self G).inv.eq] using hh
  refine ⟨hMid ▸ hFu.mul hGu, ?_⟩
  calc
    A.pinv = G.pinv * F.pinv := hA ▸ pinv_rankFactorization F G hF hG
    _ = Gᴴ * ((G * Gᴴ)⁻¹ * (Fᴴ * F)⁻¹) * Fᴴ := by
      rw [hGpinv, hFpinv]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hMid, Introduction.inv_mul hFu hGu]

/-- **Exercise 18(a)** of [benIsrael2003generalized], Chapter 1. Applying the Moore–Penrose
inverse twice recovers the original matrix. -/
theorem pinv_pinv [DecidableEq m] (A : Matrix m n ℂ) : A.pinv.pinv = A := by
  symm
  exact A.pinv.pinv_unique A.pinv_mul_self_mul_pinv A.mul_pinv_mul_self
    A.isHermitian_pinv_mul A.isHermitian_mul_pinv

/-- **Exercise 18(b)** of [benIsrael2003generalized], Chapter 1. The Moore–Penrose inverse
commutes with conjugate transposition. -/
theorem pinv_conjTranspose [DecidableEq m] (A : Matrix m n ℂ) :
    Aᴴ.pinv = A.pinvᴴ :=
  Matrix.pinv_conjTranspose A

end BenIsraelGreville.Chapter01
