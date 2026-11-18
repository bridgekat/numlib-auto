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

/-- **Exercise 18(c)** of [benIsrael2003generalized]. The Moore–Penrose
inverse commutes with ordinary transposition. -/
theorem pinv_transpose [DecidableEq m] (A : Matrix m n ℂ) : Aᵀ.pinv = A.pinvᵀ := by
  symm
  apply Aᵀ.pinv_unique
  · rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, A.mul_pinv_mul_self]
  · rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]
  · rw [← transpose_mul, IsHermitian,
      conjTranspose_transpose_eq_transpose_conjTranspose, A.isHermitian_pinv_mul.eq]
  · rw [← transpose_mul, IsHermitian,
      conjTranspose_transpose_eq_transpose_conjTranspose, A.isHermitian_mul_pinv.eq]

private theorem pinv_eq_columnGram {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) :
    A.pinv = (Aᴴ * A).pinv * Aᴴ := by
  classical
  let G := Aᴴ * A
  have hG : G.IsHermitian := isHermitian_conjTranspose_mul_self A
  have hGp : G.pinvᴴ = G.pinv := by rw [← Matrix.pinv_conjTranspose, hG.eq]
  have hc : G.pinv * G = G * G.pinv := calc
    _ = (G.pinv * G)ᴴ := G.isHermitian_pinv_mul.eq.symm
    _ = _ := by rw [conjTranspose_mul, hG.eq, hGp]
  have h : G * A.pinv = Aᴴ := by
    change (Aᴴ * A) * A.pinv = Aᴴ
    rw [Matrix.mul_assoc, conjTranspose_mul_mul_pinv]
  have hL : G.pinv * G * Aᴴ = Aᴴ := by
    rw [← h, ← Matrix.mul_assoc, hc, mul_pinv_mul_self, h]
  have hX : A.pinv = Aᴴ * (A.pinvᴴ * A.pinv) := calc
    _ = (A.pinv * A) * A.pinv := A.pinv_mul_self_mul_pinv.symm
    _ = (A.pinv * A)ᴴ * A.pinv := by rw [A.isHermitian_pinv_mul.eq]
    _ = _ := by rw [conjTranspose_mul, Matrix.mul_assoc]
  calc
    A.pinv = G.pinv * G * A.pinv := by
      conv_rhs => rw [hX, ← Matrix.mul_assoc, hL]
      exact hX
    _ = _ := by rw [Matrix.mul_assoc, h]

/-- **Exercise 18(d)** of [benIsrael2003generalized]. The two Gram
matrices give equivalent formulas for the Moore–Penrose inverse. -/
theorem pinv_gram {𝕜 : Type*} [RCLike 𝕜] [DecidableEq m] (A : Matrix m n 𝕜) :
    A.pinv = (Aᴴ * A).pinv * Aᴴ ∧ A.pinv = Aᴴ * (A * Aᴴ).pinv := by
  refine ⟨pinv_eq_columnGram A, ?_⟩
  have h := congrArg Matrix.conjTranspose (pinv_eq_columnGram Aᴴ)
  rw [conjTranspose_mul, ← Matrix.pinv_conjTranspose, conjTranspose_conjTranspose,
    ← Matrix.pinv_conjTranspose, (isHermitian_mul_conjTranspose_self A).eq] at h
  exact h

/-- **Exercise 22** of [benIsrael2003generalized]. Diagonal entries
are reciprocated with zero left fixed. -/
theorem pinv_diagonal (d : n → ℂ) :
    (diagonal d).pinv = diagonal (fun i => (d i)⁻¹) := by
  symm
  apply (diagonal d).pinv_unique
  · simp only [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext i
    by_cases h : d i = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]
  · simp only [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext i
    by_cases h : d i = 0
    · simp [h]
    · simp [inv_mul_cancel₀ h]
  · simp only [diagonal_mul_diagonal, IsHermitian, diagonal_conjTranspose]
    apply congrArg diagonal
    funext i
    by_cases h : d i = 0 <;> simp [h, mul_inv_cancel₀]
  · simp only [diagonal_mul_diagonal, IsHermitian, diagonal_conjTranspose]
    apply congrArg diagonal
    funext i
    by_cases h : d i = 0 <;> simp [h, inv_mul_cancel₀]

/-- **Exercise 25** of [benIsrael2003generalized]. Unitary changes of
coordinates transport the Moore–Penrose inverse by their adjoints. -/
theorem pinv_unitary_mul [DecidableEq m] (A : Matrix m n ℂ)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ) (hU : U ∈ unitaryGroup m ℂ)
    (hV : V ∈ unitaryGroup n ℂ) :
    (U * A * V).pinv = Vᴴ * A.pinv * Uᴴ := by
  have h₁ : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have h₂ : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hV
  have hp : (U * A * V) * (Vᴴ * A.pinv * Uᴴ) = U * (A * A.pinv) * Uᴴ := calc
    _ = U * (A * (V * Vᴴ) * A.pinv) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h₂, Matrix.mul_one]
  have hq : (Vᴴ * A.pinv * Uᴴ) * (U * A * V) = Vᴴ * (A.pinv * A) * V := calc
    _ = Vᴴ * (A.pinv * (Uᴴ * U) * A) * V := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h₁, Matrix.mul_one]
  symm
  apply (U * A * V).pinv_unique
  · rw [hp]
    calc
      _ = U * ((A * A.pinv) * (Uᴴ * U) * A) * V := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h₁, Matrix.mul_one, A.mul_pinv_mul_self]
  · rw [hq]
    calc
      _ = Vᴴ * ((A.pinv * A) * (V * Vᴴ) * A.pinv) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h₂, Matrix.mul_one, A.pinv_mul_self_mul_pinv]
  · rw [hp]
    simpa only [conjTranspose_conjTranspose] using
      isHermitian_conjTranspose_mul_mul Uᴴ A.isHermitian_mul_pinv
  · rw [hq]
    exact isHermitian_conjTranspose_mul_mul V A.isHermitian_pinv_mul

end BenIsraelGreville.Chapter01
