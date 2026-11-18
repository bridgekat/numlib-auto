/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter06.Section01
import NumlibSurface.BenIsraelGreville.Chapter00.Section06

/-!
# The singular value decomposition

Section 6.2 of [benIsrael2003generalized] pairs the positive Gram eigenvectors
on both sides of a matrix. The singular value decomposition gives formulas
for the Moore–Penrose inverse and its low-rank companions.
-/

namespace BenIsraelGreville.Chapter06

open Matrix
open scoped ComplexOrder InnerProductSpace

private theorem normalize_gram_eigenvectors {E F ι : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (T : E →ₗ[ℂ] F) (σ : ι → ℝ) (hσ : ∀ i, 0 < σ i)
    (u : ι → E) (hu : Orthonormal ℂ u)
    (he : ∀ i, T.adjoint (T (u i)) = (σ i : ℂ) ^ 2 • u i) :
    let v := fun i => (σ i : ℂ)⁻¹ • T (u i)
    Orthonormal ℂ v ∧ ∀ i,
      T (T.adjoint (v i)) = (σ i : ℂ) ^ 2 • v i ∧
      u i = (σ i : ℂ)⁻¹ • T.adjoint (v i) := by
  let v := fun i => (σ i : ℂ)⁻¹ • T (u i)
  have hσ₀ (i : ι) : (σ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hσ i).ne'
  have hv : Orthonormal ℂ v := by
    classical
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    have hInner : inner ℂ (T (u i)) (T (u j)) =
        (σ j : ℂ) ^ 2 * inner ℂ (u i) (u j) := by
      rw [← LinearMap.adjoint_inner_right, he j, inner_smul_right]
    simp only [v, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal, hInner, hu]
    split_ifs with hij
    · subst j
      field_simp [hσ₀]
    · simp
  have hPair (i : ι) : T.adjoint (v i) = (σ i : ℂ) • u i := by
    dsimp only [v]
    rw [map_smul, he i, smul_smul]
    congr 1
    field_simp [hσ₀]
  refine ⟨hv, fun i => ⟨?_, ?_⟩⟩
  · rw [hPair, map_smul]
    dsimp only [v]
    rw [smul_smul]
    congr 1
    field_simp [hσ₀]
  · rw [hPair, smul_smul, inv_mul_cancel₀ (hσ₀ i), one_smul]

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 6, Equations
(19)–(22). Normalized adjoint images of positive left Gram eigenvectors
form the corresponding orthonormal right Gram eigenvectors. -/
theorem theorem_6_1 {m n ι : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ)
    (σ : ι → ℝ) (hσ : ∀ i, 0 < σ i)
    (u : ι → EuclideanSpace ℂ m) (hu : Orthonormal ℂ u)
    (he : ∀ i, toEuclideanLin (A * Aᴴ) (u i) = (σ i : ℂ) ^ 2 • u i) :
    let v := fun i => (σ i : ℂ)⁻¹ • toEuclideanLin Aᴴ (u i)
    Orthonormal ℂ v ∧ ∀ i,
      toEuclideanLin (Aᴴ * A) (v i) = (σ i : ℂ) ^ 2 • v i ∧
      u i = (σ i : ℂ)⁻¹ • toEuclideanLin A (v i) := by
  simp only [toEuclideanLin_mul_apply] at he ⊢
  simpa only [← toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_conjTranspose] using
    normalize_gram_eigenvectors (toEuclideanLin Aᴴ) σ hσ u hu
      (by simpa only [← toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_conjTranspose]
        using he)

/-- **Theorem 1, dual statement** of [benIsrael2003generalized], Chapter 6.
Normalized forward images of the right Gram eigenvectors give the left family. -/
theorem theorem_6_1_dual {m n ι : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ)
    (σ : ι → ℝ) (hσ : ∀ i, 0 < σ i)
    (v : ι → EuclideanSpace ℂ n) (hv : Orthonormal ℂ v)
    (he : ∀ i, toEuclideanLin (Aᴴ * A) (v i) = (σ i : ℂ) ^ 2 • v i) :
    let u := fun i => (σ i : ℂ)⁻¹ • toEuclideanLin A (v i)
    Orthonormal ℂ u ∧ ∀ i,
      toEuclideanLin (A * Aᴴ) (u i) = (σ i : ℂ) ^ 2 • u i ∧
      v i = (σ i : ℂ)⁻¹ • toEuclideanLin Aᴴ (u i) := by
  simpa only [conjTranspose_conjTranspose] using
    theorem_6_1 Aᴴ σ hσ v hv (by simpa only [conjTranspose_conjTranspose] using he)

section Decomposition

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
  {U : Matrix (Fin m) (Fin m) ℂ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℂ}

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 6. Every complex
matrix has a unitary singular value decomposition with its ordered singular
values and zero padding on the rectangular diagonal. -/
theorem theorem_6_2 (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ U V, IsSingularValueDecomposition A U A.sortedSingularValues V := by
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  exact ⟨U, V,
    ⟨⟨hU, hV, h⟩, A.sortedSingularValues_antitone, A.sortedSingularValues_nonneg⟩,
    fun i => (A.sortedSingularValues_eq_zero_iff_rank_le i).mpr⟩

/-- **Corollary 1** of [benIsrael2003generalized], Chapter 6, Equations
(27)–(28). Reciprocating the positive singular values and interchanging the
unitary factors gives the Moore–Penrose inverse. -/
theorem corollary_6_1 (h : IsSingularValueDecomposition A U σ V) :
    A.pinv = V * (rectDiagonal (fun i => (σ i : ℂ)⁻¹) : Matrix (Fin n) (Fin m) ℂ) * Uᴴ :=
  h.1.pinv_eq

private theorem svdTruncation_eq_leading_blocks (U : Matrix (Fin m) (Fin m) ℂ)
    (σ : ℕ → ℝ) (V : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (hm : k ≤ m) (hn : k ≤ n) :
    svdTruncation U σ V k =
      U.submatrix id (Fin.castLE hm) * diagonal (fun i : Fin k => (σ i : ℂ)) *
        (V.submatrix id (Fin.castLE hn))ᴴ := by
  let Uk := U.submatrix id (Fin.castLE hm)
  let Vk := V.submatrix id (Fin.castLE hn)
  let D := diagonal (fun i : Fin k => (σ i : ℂ))
  rw [Matrix.svdTruncation_eq_sum U σ V hm hn]
  change _ = Uk * D * Vkᴴ
  ext i j
  rw [Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (Uk * D) i l = Uk i l * (σ l : ℂ) from mul_diagonal _ _ _ _]
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, col_apply, smul_eq_mul,
    conjTranspose_apply, Uk, Vk, submatrix_apply, id_eq]
  change (σ l : ℂ) * (U i (Fin.castLE hm l) * star (V j (Fin.castLE hn l))) =
    U i (Fin.castLE hm l) * (σ l : ℂ) * star (V j (Fin.castLE hn l))
  rw [mul_assoc]
  exact mul_left_comm _ _ _

/-- **Equations (29)–(30)** of [benIsrael2003generalized], Chapter 6. A
truncation is the product of the leading singular-vector matrices with the
truncated diagonal. It also expands as a sum of rank-one matrices. -/
theorem svd_truncation_expansion (h : IsSingularValueDecomposition A U σ V)
    {k : ℕ} (hk : k ≤ A.rank) :
    let hm := hk.trans A.rank_le_height
    let hn := hk.trans A.rank_le_width
    let Uk := U.submatrix id (Fin.castLE hm)
    let Vk := V.submatrix id (Fin.castLE hn)
    svdTruncation U σ V k = Uk * diagonal (fun i : Fin k => (σ i : ℂ)) * Vkᴴ ∧
      svdTruncation U σ V k = ∑ i : Fin k,
        (σ i : ℂ) • vecMulVec (U.col (Fin.castLE hm i)) (star (V.col (Fin.castLE hn i))) ∧
      (svdTruncation U σ V k).rank = k := by
  let hm := hk.trans A.rank_le_height
  let hn := hk.trans A.rank_le_width
  exact ⟨svdTruncation_eq_leading_blocks U σ V hm hn,
    Matrix.svdTruncation_eq_sum U σ V hm hn, rank_svdTruncation h.1 hk⟩

/-- **Equation (30a)** of [benIsrael2003generalized], Chapter 6. Truncating
at the rank preserves the whole matrix. -/
theorem svd_truncation_rank (h : IsSingularValueDecomposition A U σ V) :
    svdTruncation U σ V A.rank = A := by
  have he : (fun i => if i < A.rank then (σ i : ℂ) else 0) = fun i => (σ i : ℂ) := by
    funext i
    split_ifs with hi
    · rfl
    · rw [h.2 i (Nat.le_of_not_gt hi), Complex.ofReal_zero]
  change U * (rectDiagonal (fun i => if i < A.rank then (σ i : ℂ) else 0) :
    Matrix (Fin m) (Fin n) ℂ) * star V = A
  rw [he]
  exact h.1.eq_mul_mul_star.symm

/-- **Equation (30b)** of [benIsrael2003generalized], Chapter 6. Restricting
to the positive diagonal entries gives the square inverse of the leading
diagonal and a finite expansion of the Moore–Penrose inverse. -/
theorem svd_pinv_expansion (h : IsSingularValueDecomposition A U σ V) :
    let r := A.rank
    let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
    let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
    let D := diagonal (fun i : Fin r => (σ i : ℂ))
    A.pinv = Vr * D⁻¹ * Urᴴ ∧
      A.pinv = ∑ i : Fin r, (σ i : ℂ)⁻¹ •
        vecMulVec (V.col (Fin.castLE A.rank_le_width i))
          (star (U.col (Fin.castLE A.rank_le_height i))) := by
  let τ := fun i : ℕ => (σ i)⁻¹
  let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
  let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
  let D := diagonal (fun i : Fin A.rank => (σ i : ℂ))
  let D' := diagonal (fun i : Fin A.rank => (τ i : ℂ))
  have hσ₀ (i : Fin A.rank) : (σ i : ℂ) ≠ 0 := by
    intro he
    have hz := Complex.ofReal_eq_zero.mp he
    rw [h.eq_sortedSingularValues] at hz
    exact (not_lt_of_ge ((A.sortedSingularValues_eq_zero_iff_rank_le i).mp hz)) i.isLt
  have hd : D * D' = 1 := by
    change diagonal (fun i : Fin A.rank => (σ i : ℂ)) *
      diagonal (fun i : Fin A.rank => (τ i : ℂ)) = _
    rw [diagonal_mul_diagonal]
    have hc : (fun i : Fin A.rank => (σ i : ℂ) * (τ i : ℂ)) = 1 := by
      funext i
      change (σ i : ℂ) * ((σ i)⁻¹ : ℝ) = 1
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (hσ₀ i)]
    rw [hc]
    exact diagonal_one
  have hRect : (rectDiagonal (fun i => (σ i : ℂ)⁻¹) : Matrix (Fin n) (Fin m) ℂ) =
      rectDiagonal (fun i => if i < A.rank then (τ i : ℂ) else 0) := by
    apply congrArg rectDiagonal
    funext i
    split_ifs with hi
    · exact (Complex.ofReal_inv (σ i)).symm
    · rw [h.2 i (Nat.le_of_not_gt hi), Complex.ofReal_zero, _root_.inv_zero]
  have hp : A.pinv = svdTruncation V τ U A.rank := by
    rw [corollary_6_1 h, hRect]
    rfl
  constructor
  · change A.pinv = Vr * D⁻¹ * Urᴴ
    rw [hp, inv_eq_right_inv hd]
    exact svdTruncation_eq_leading_blocks V τ U A.rank_le_width A.rank_le_height
  · rw [hp, Matrix.svdTruncation_eq_sum V τ U A.rank_le_width A.rank_le_height]
    simp only [τ, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inv]

/-- **Exercise 18** of [benIsrael2003generalized], Chapter 6, Equations
(34)–(35). A complex diagonal with the same moduli as the singular values
can be used with unitary factors. -/
def IsUDVDecomposition (A : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (d : ℕ → ℂ) (V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  U ∈ unitaryGroup (Fin m) ℂ ∧ V ∈ unitaryGroup (Fin n) ℂ ∧
    A = U * (rectDiagonal d : Matrix (Fin m) (Fin n) ℂ) * Vᴴ ∧
    ∀ i, ‖d i‖ = A.sortedSingularValues i

/-- **Exercise 18** of [benIsrael2003generalized], Chapter 6, Equations
(36)–(37). Introducing unit-modulus phases into the SVD diagonal is
equivalent to multiplying the corresponding right singular vectors by those phases. -/
theorem exercise_18 (h : IsSingularValueDecomposition A U σ V) (p : Fin n → ℂ)
    (hp : ∀ i, ‖p i‖ = 1) :
    let d (i : ℕ) := if hi : i < n then (σ i : ℂ) * p ⟨i, hi⟩ else 0
    IsUDVDecomposition A U d (V * diagonal p) := by
  let d (i : ℕ) := if hi : i < n then (σ i : ℂ) * p ⟨i, hi⟩ else 0
  let T := diagonal p
  let D₀ : Matrix (Fin m) (Fin n) ℂ := rectDiagonal (fun i => (σ i : ℂ))
  have hT : T * Tᴴ = 1 := by
    change diagonal p * (diagonal p)ᴴ = 1
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    have he : (fun i => p i * (star p) i) = fun _ => (1 : ℂ) := by
      funext i
      change p i * (starRingEnd ℂ) (p i) = 1
      rw [Complex.mul_conj', hp i]
      norm_num
    rw [he, diagonal_one]
  have hD : D₀ * T = rectDiagonal d := by
    ext i j
    change (D₀ * diagonal p) i j = _
    rw [mul_diagonal]
    simp only [D₀, rectDiagonal_apply, d]
    by_cases hEq : i.val = j.val
    · have hi : i.val < n := hEq ▸ j.isLt
      rw [ite_eq_left hEq, ite_eq_left hEq, dite_eq_left hi, show (⟨i.val, hi⟩ : Fin n) = j
        from Fin.ext hEq]
    · rw [ite_eq_right hEq, ite_eq_right hEq, zero_mul]
  refine ⟨h.1.mem_unitaryGroup_left,
    mul_mem h.1.mem_unitaryGroup_right (Matrix.mem_unitaryGroup_iff.mpr hT), ?_, ?_⟩
  · change A = U * rectDiagonal d * (V * T)ᴴ
    rw [← hD, conjTranspose_mul]
    calc
      A = U * D₀ * Vᴴ := h.1.eq_mul_mul_star
      _ = U * D₀ * (T * Tᴴ) * Vᴴ := by rw [hT, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro i
    rw [← h.eq_sortedSingularValues]
    dsimp only [d]
    split_ifs with hi
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.1.nonneg i), hp, mul_one]
    · rw [norm_zero, h.2 i (A.rank_le_width.trans (Nat.le_of_not_gt hi))]

end Decomposition

/-- **Exercise 21** of [benIsrael2003generalized], Chapter 6, Equation (41),
for real matrices. The volume is the product of the positive singular values. -/
theorem exercise_21_real {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank ≠ 0) :
    Chapter00.matrixVolume A = ∏ i : Fin A.rank, A.sortedSingularValues i := by
  classical
  let : Unique (Chapter00.IndexSequence A.rank A.rank) :=
    ⟨⟨(OrderIso.refl (Fin A.rank)).toOrderEmbedding⟩, Chapter00.indexSequence_self_unique⟩
  rw [← Chapter00.kVolume_eq_matrixVolume A rfl hA,
    Chapter00.kVolume_eq_sqrt_sum_singularValues _ A (Nat.pos_of_ne_zero hA) le_rfl]
  simp only [Fintype.sum_unique]
  change Real.sqrt (∏ i : Fin A.rank, A.sortedSingularValues i ^ 2) = _
  rw [Finset.prod_pow]
  exact Real.sqrt_sq (show 0 ≤ ∏ i : Fin A.rank, A.sortedSingularValues i from
    Finset.prod_nonneg fun i _ => A.sortedSingularValues_nonneg i)

end BenIsraelGreville.Chapter06
