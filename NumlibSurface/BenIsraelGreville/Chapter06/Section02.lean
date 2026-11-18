/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter06.Section01
import NumlibSurface.BenIsraelGreville.Chapter00.Section06
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# The singular value decomposition

Section 6.2 of [benIsrael2003generalized] pairs the positive Gram eigenvectors
on both sides of a matrix. The singular value decomposition gives formulas
for the Moore–Penrose inverse and its low-rank companions.

## Deviations from the source

* **Exercise 18** (correction). Equation (20*) divides by the conjugate of
  the complex diagonal entry.
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

/-- **Exercise 13**, Equations (31)–(32), of [benIsrael2003generalized].
The reciprocal and damped coefficients give the least-norm and
Tikhonov solutions in paired singular-vector coordinates. Terms
with zero singular value contribute zero. -/
theorem exercise_13 {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℂ}
    (h : IsSingularValueDecomposition A U σ V) (b : EuclideanSpace ℂ (Fin m))
    {α : ℝ} (hα : 0 < α) :
    let β (i : Fin (min m n)) :=
      inner ℂ (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace ℂ (Fin m)) b
    let v (i : Fin (min m n)) : EuclideanSpace ℂ (Fin n) :=
      WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i))
    toEuclideanLin A.pinv b = ∑ i : Fin (min m n), ((σ i : ℂ)⁻¹) • β i • v i ∧
      toEuclideanLin (A.tikhonov α) b =
        ∑ i : Fin (min m n), ((σ i / (σ i ^ 2 + α) : ℝ) : ℂ) • β i • v i :=
  ⟨toEuclideanLin_pinv_eq_sum_of_isSVD h.1 b,
    toEuclideanLin_tikhonov_eq_sum_of_isSVD h.1 hα b⟩

/-- **Exercise 13**, reciprocal expansion. The exact remainder has cubic
order as the singular-value perturbation tends to zero. -/
theorem exercise_13_reciprocal_taylor (σ ε : ℝ) (hσ : σ ≠ 0) (h : σ + ε ≠ 0) :
    1 / (σ + ε) =
      1 / σ - ε / σ ^ 2 + ε ^ 2 / σ ^ 3 - ε ^ 3 / (σ ^ 3 * (σ + ε)) := by
  field_simp
  ring

/-- **Exercise 13**, damped expansion. The remainder is written as an
explicit cubic multiple with a denominator that stays positive. -/
theorem exercise_13_damped_taylor (σ ε α : ℝ) (hα : 0 < α) :
    let d := σ ^ 2 + α
    (σ + ε) / ((σ + ε) ^ 2 + α) =
      σ / d - (σ ^ 2 - α) / d ^ 2 * ε + σ * (σ ^ 2 - 3 * α) / d ^ 3 * ε ^ 2 -
        ε ^ 3 * (σ ^ 4 - 6 * α * σ ^ 2 + α ^ 2 + ε * σ * (σ ^ 2 - 3 * α)) /
          (d ^ 3 * ((σ + ε) ^ 2 + α)) := by
  intro d
  have hd : d ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hα).ne'
  have he : (σ + ε) ^ 2 + α ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hα).ne'
  field_simp
  dsimp [d]
  ring

/-- At the matched damping value the linear perturbation term vanishes,
and the quadratic coefficient is the one displayed in Exercise 13. -/
theorem exercise_13_damped_taylor_matched (σ ε : ℝ) (hσ : σ ≠ 0) :
    (σ + ε) / ((σ + ε) ^ 2 + σ ^ 2) =
      1 / (2 * σ) - ε ^ 2 / (4 * σ ^ 3) +
        ε ^ 3 * (2 * σ + ε) / (4 * σ ^ 3 * ((σ + ε) ^ 2 + σ ^ 2)) := by
  have he : (σ + ε) ^ 2 + σ ^ 2 ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hσ)).ne'
  field_simp
  ring

private theorem hermitian_diagonal_has_real_entries {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) {A : Matrix n n ℂ} (hA : A.IsHermitian) {d : n → ℂ}
    (hd : Uᴴ * A * U = diagonal d) : ∀ i, ((d i).re : ℂ) = d i := by
  have hH : (Uᴴ * A * U).IsHermitian := by
    change (Uᴴ * A * U)ᴴ = Uᴴ * A * U
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  rw [hd] at hH
  intro i
  have he := congrFun (congrFun hH.eq i) i
  simp only [conjTranspose_apply, diagonal_apply_eq] at he
  have hi := congrArg Complex.im he
  change -(d i).im = (d i).im at hi
  apply Complex.ext
  · simp
  · change 0 = (d i).im
    linarith

/-- In Exercise 16, the two Hermitian product conditions are equivalent to commutation. -/
theorem exercise_16_products_iff_commute {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A * B).IsHermitian ∧ (B * A).IsHermitian) ↔ Commute A B := by
  constructor
  · rintro ⟨h, _⟩
    have he := h.eq
    rw [conjTranspose_mul, hA.eq, hB.eq] at he
    exact he.symm
  · intro h
    refine ⟨?_, ?_⟩
    · change (A * B)ᴴ = A * B
      rw [conjTranspose_mul, hA.eq, hB.eq, h.eq]
    · change (B * A)ᴴ = B * A
      rw [conjTranspose_mul, hA.eq, hB.eq, h.eq]

/-- **Exercise 16** of [benIsrael2003generalized], Chapter 6.
Two Hermitian matrices share a unitary real diagonalization exactly
when they commute, equivalently when both products are Hermitian. -/
theorem exercise_16 {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∃ U ∈ unitaryGroup n ℂ, ∃ d e : n → ℝ,
      Uᴴ * A * U = diagonal (fun i => (d i : ℂ)) ∧
        Uᴴ * B * U = diagonal (fun i => (e i : ℂ))) ↔
      (A * B).IsHermitian ∧ (B * A).IsHermitian := by
  rw [exercise_16_products_iff_commute hA hB]
  constructor
  · rintro ⟨U, hU, d, e, hd, he⟩
    have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have hprod (M N : Matrix n n ℂ) : Uᴴ * (M * N) * U = (Uᴴ * M * U) * (Uᴴ * N * U) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᴴ, hUU, Matrix.one_mul]
    have hc : Uᴴ * (A * B) * U = Uᴴ * (B * A) * U := by
      rw [hprod, hprod, hd, he, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have hback := congrArg (fun M : Matrix n n ℂ => U * M * Uᴴ) hc
    have hcancel (M : Matrix n n ℂ) : U * (Uᴴ * M * U) * Uᴴ = M := calc
      _ = (U * Uᴴ) * M * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
    change U * (Uᴴ * (A * B) * U) * Uᴴ = U * (Uᴴ * (B * A) * U) * Uᴴ at hback
    rw [hcancel, hcancel] at hback
    exact hback
  · intro h
    obtain ⟨U, hU, d, e, hd, he⟩ := hA.exists_unitary_conj_diagonal_of_commute hB h
    change Uᴴ * A * U = diagonal d at hd
    change Uᴴ * B * U = diagonal e at he
    refine ⟨U, hU, fun i => (d i).re, fun i => (e i).re, ?_, ?_⟩
    · rw [show (fun i => ((d i).re : ℂ)) = d from funext (hermitian_diagonal_has_real_entries U hA hd)]
      exact hd
    · rw [show (fun i => ((e i).re : ℂ)) = e from funext (hermitian_diagonal_has_real_entries U hB he)]
      exact he

/-- **Exercise 18**, Equations (20*) and (22*) of [benIsrael2003generalized].
The right and left column vectors are paired by the complex diagonal
entry and its conjugate, respectively. -/
theorem phaseSingularVectorPair {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {d : ℕ → ℂ}
    (h : IsUDVDecomposition A U d V) (i : ℕ) (hm : i < m) (hn : i < n) :
    A *ᵥ V.col ⟨i, hn⟩ = d i • U.col ⟨i, hm⟩ ∧
      Aᴴ *ᵥ U.col ⟨i, hm⟩ = star (d i) • V.col ⟨i, hn⟩ := by
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal d
  have hV : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp h.2.1
  have hU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp h.1
  have hA : A = U * D * Vᴴ := h.2.2.1
  have hAV : A * V = U * D := by
    rw [hA, Matrix.mul_assoc, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hAU : Aᴴ * U = V * Dᴴ := by
    rw [hA, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]
  constructor
  · change (A * V).col ⟨i, hn⟩ = _
    rw [hAV]
    funext j
    rw [col_apply, mul_rectDiagonal_apply]
    simp [hm, col_apply, mul_comm]
  · change (Aᴴ * U).col ⟨i, hm⟩ = _
    rw [hAU]
    funext j
    rw [col_apply, rectDiagonal_conjTranspose, mul_rectDiagonal_apply]
    simp [hn, col_apply, mul_comm]

private theorem unitary_sandwich_injective {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {U : Matrix m m ℂ} {V : Matrix n n ℂ}
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    Function.Injective (fun M : Matrix m n ℂ => U * M * Vᴴ) := by
  have hcancel (M : Matrix m n ℂ) : Uᴴ * (U * M * Vᴴ) * V = M := calc
    _ = (Uᴴ * U) * M * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
  intro M N h
  simpa only [hcancel] using congrArg (fun B : Matrix m n ℂ => Uᴴ * B * V) h

private theorem isHermitian_unitary_sandwich_iff {m : Type*} [Fintype m] [DecidableEq m]
    {U : Matrix m m ℂ} (hU : Uᴴ * U = 1) (T : Matrix m m ℂ) :
    (U * T * Uᴴ).IsHermitian ↔ T.IsHermitian := by
  unfold IsHermitian
  have h : (U * T * Uᴴ)ᴴ = U * Tᴴ * Uᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [h]
  exact (unitary_sandwich_injective hU hU).eq_iff

section InverseBlocks

variable {r m n : Type*} [Fintype r] [Fintype m] [Fintype n] [DecidableEq r]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
private theorem block_diagonal_inner_iff (S : Matrix r r ℂ) (hS : IsUnit S)
    (H : Matrix (r ⊕ n) (r ⊕ m) ℂ) :
    let D := fromBlocks S (0 : Matrix r n ℂ) (0 : Matrix m r ℂ) (0 : Matrix m n ℂ)
    D.IsInnerInverse H ↔ H.toBlocks₁₁ = S⁻¹ := by
  intro D
  have hd := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hL := Matrix.nonsing_inv_mul S hd
  have hR := Matrix.mul_nonsing_inv S hd
  have he : D * H * D = fromBlocks (S * H.toBlocks₁₁ * S)
      (0 : Matrix r n ℂ) (0 : Matrix m r ℂ) (0 : Matrix m n ℂ) := by
    conv_lhs => rw [← fromBlocks_toBlocks H]
    simp [D, fromBlocks_multiply]
  rw [isInnerInverse_iff, he]
  change fromBlocks (S * H.toBlocks₁₁ * S) 0 0 0 = fromBlocks S 0 0 0 ↔ _
  simp only [fromBlocks_inj, and_true]
  constructor
  · intro h
    have h' := congrArg (fun T : Matrix r r ℂ => S⁻¹ * T * S⁻¹) h
    have ht : S⁻¹ * (S * H.toBlocks₁₁ * S) * S⁻¹ = H.toBlocks₁₁ := by
      calc
        _ = (S⁻¹ * S) * H.toBlocks₁₁ * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
    change S⁻¹ * (S * H.toBlocks₁₁ * S) * S⁻¹ = S⁻¹ * S * S⁻¹ at h'
    rw [ht, hL, Matrix.one_mul] at h'
    exact h'
  · intro h
    rw [h, hR, Matrix.one_mul]

omit [DecidableEq m] [DecidableEq n] in
private theorem block_diagonal_extra_penrose (S : Matrix r r ℂ) (hS : IsUnit S)
    (X : Matrix r m ℂ) (Y : Matrix n r ℂ) (Z : Matrix n m ℂ) :
    let D := fromBlocks S (0 : Matrix r n ℂ) (0 : Matrix m r ℂ) (0 : Matrix m n ℂ)
    let H := fromBlocks S⁻¹ X Y Z
    (D.IsOuterInverse H ↔ Z = Y * S * X) ∧
      ((D * H).IsHermitian ↔ X = 0) ∧
      ((H * D).IsHermitian ↔ Y = 0) := by
  intro D H
  have hd := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hL := Matrix.nonsing_inv_mul S hd
  have hR := Matrix.mul_nonsing_inv S hd
  have hDH : D * H = fromBlocks (1 : Matrix r r ℂ) (S * X) (0 : Matrix m r ℂ) 0 := by
    simp [D, H, fromBlocks_multiply, hR]
  have hHD : H * D = fromBlocks (1 : Matrix r r ℂ) (0 : Matrix r n ℂ) (Y * S) 0 := by
    simp [D, H, fromBlocks_multiply, hL]
  refine ⟨?_, ?_, ?_⟩
  · rw [isOuterInverse_iff, hHD]
    have hY : Y * S * S⁻¹ = Y := by rw [Matrix.mul_assoc, hR, Matrix.mul_one]
    simp [H, fromBlocks_multiply, fromBlocks_inj, hY, eq_comm]
  · rw [hDH, isHermitian_fromBlocks_iff]
    constructor
    · intro h
      have he : S * X = 0 := h.2.2.1.symm.trans (conjTranspose_zero : (0 : Matrix m r ℂ)ᴴ = 0)
      have hg := congrArg (fun M : Matrix r m ℂ => S⁻¹ * M) he
      change S⁻¹ * (S * X) = S⁻¹ * 0 at hg
      rw [← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_zero] at hg
      exact hg
    · intro hx
      simp [hx, Matrix.isHermitian_one, Matrix.isHermitian_zero]
  · rw [hHD, isHermitian_fromBlocks_iff]
    constructor
    · intro h
      have he : Y * S = 0 := h.2.1.symm.trans (conjTranspose_zero : (0 : Matrix r n ℂ)ᴴ = 0)
      have hg := congrArg (fun M : Matrix n r ℂ => M * S⁻¹) he
      change (Y * S) * S⁻¹ = 0 * S⁻¹ at hg
      rw [Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] at hg
      exact hg
    · intro hy
      simp [hy, Matrix.isHermitian_one, Matrix.isHermitian_zero]

/-- **Exercise 14**, Equation (33), of [benIsrael2003generalized].
In the two unitary coordinates, the inner equation fixes the leading
block. The remaining equations determine the stated product or zero
blocks, and the Moore–Penrose inverse makes every free block zero. -/
theorem exercise_14 (S : Matrix r r ℂ) (hS : IsUnit S)
    (U : Matrix (r ⊕ m) (r ⊕ m) ℂ) (V : Matrix (r ⊕ n) (r ⊕ n) ℂ)
    (hU : U ∈ unitaryGroup (r ⊕ m) ℂ) (hV : V ∈ unitaryGroup (r ⊕ n) ℂ)
    (W : Matrix (r ⊕ n) (r ⊕ m) ℂ) :
    let D := fromBlocks S (0 : Matrix r n ℂ) (0 : Matrix m r ℂ) (0 : Matrix m n ℂ)
    let A := U * D * Vᴴ
    let H := Vᴴ * W * U
    (A.IsInnerInverse W ↔ H.toBlocks₁₁ = S⁻¹) ∧
    (A.IsInnerInverse W →
      (A.IsOuterInverse W ↔ H.toBlocks₂₂ = H.toBlocks₂₁ * S * H.toBlocks₁₂) ∧
      ((A * W).IsHermitian ↔ H.toBlocks₁₂ = 0) ∧
      ((W * A).IsHermitian ↔ H.toBlocks₂₁ = 0)) ∧
    A.pinv = V * fromBlocks S⁻¹ (0 : Matrix r m ℂ) (0 : Matrix n r ℂ) 0 * Uᴴ := by
  intro D A H
  have hU₁ : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU₂ : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hV₁ : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hV₂ : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  have ht (B : Matrix (r ⊕ n) (r ⊕ m) ℂ) :
      A * (V * B * Uᴴ) = U * (D * B) * Uᴴ ∧
      (V * B * Uᴴ) * A = V * (B * D) * Vᴴ := by
    constructor
    · change (U * D * Vᴴ) * (V * B * Uᴴ) = _
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, hV₁, Matrix.one_mul]
    · change (V * B * Uᴴ) * (U * D * Vᴴ) = _
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU₁, Matrix.one_mul]
  have hW : W = V * H * Uᴴ := calc
    _ = (V * Vᴴ) * W * (U * Uᴴ) := by rw [hV₂, hU₂, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by dsimp only [H]; simp only [Matrix.mul_assoc]
  have transform (B : Matrix (r ⊕ n) (r ⊕ m) ℂ) :
      (A.IsInnerInverse (V * B * Uᴴ) ↔ D.IsInnerInverse B) ∧
      (A.IsOuterInverse (V * B * Uᴴ) ↔ D.IsOuterInverse B) ∧
      ((A * (V * B * Uᴴ)).IsHermitian ↔ (D * B).IsHermitian) ∧
      (((V * B * Uᴴ) * A).IsHermitian ↔ (B * D).IsHermitian) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [isInnerInverse_iff, isInnerInverse_iff, (ht B).1]
      have he : (U * (D * B) * Uᴴ) * A = U * (D * B * D) * Vᴴ := by
        change (U * (D * B) * Uᴴ) * (U * D * Vᴴ) = _
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U, hU₁, Matrix.one_mul]
      rw [he]
      change U * (D * B * D) * Vᴴ = U * D * Vᴴ ↔ _
      exact (unitary_sandwich_injective hU₁ hV₁).eq_iff
    · rw [isOuterInverse_iff, isOuterInverse_iff, (ht B).2]
      have he : (V * (B * D) * Vᴴ) * (V * B * Uᴴ) = V * (B * D * B) * Uᴴ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Vᴴ V, hV₁, Matrix.one_mul]
      rw [he]
      exact (unitary_sandwich_injective hV₁ hU₁).eq_iff
    · rw [(ht B).1, isHermitian_unitary_sandwich_iff hU₁]
    · rw [(ht B).2, isHermitian_unitary_sandwich_iff hV₁]
  have hT :
      (A.IsInnerInverse W ↔ D.IsInnerInverse H) ∧ (A.IsOuterInverse W ↔ D.IsOuterInverse H) ∧
        ((A * W).IsHermitian ↔ (D * H).IsHermitian) ∧ ((W * A).IsHermitian ↔ (H * D).IsHermitian) := by
    have h := transform H
    rwa [← hW] at h
  have hI := (hT.1).trans (block_diagonal_inner_iff S hS H)
  refine ⟨hI, ?_, ?_⟩
  · intro hW
    rw [hT.2.1, hT.2.2.1, hT.2.2.2]
    have he : H = fromBlocks S⁻¹ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂ := by
      rw [← fromBlocks_toBlocks H]
      simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
        toBlocks_fromBlocks₂₂, hI.mp hW]
    have hh := block_diagonal_extra_penrose S hS H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂
    rw [← he] at hh
    exact hh
  · let B := fromBlocks S⁻¹ (0 : Matrix r m ℂ) (0 : Matrix n r ℂ) (0 : Matrix n m ℂ)
    have hi : D.IsInnerInverse B := (block_diagonal_inner_iff S hS B).mpr (by simp [B])
    have he := block_diagonal_extra_penrose S hS (0 : Matrix r m ℂ) (0 : Matrix n r ℂ) (0 : Matrix n m ℂ)
    have hB := transform B
    symm
    apply A.pinv_unique
    · exact (hB.1).mpr hi
    · exact (hB.2.1).mpr (he.1.mpr (by simp))
    · exact (hB.2.2.1).mpr (he.2.1.mpr rfl)
    · exact (hB.2.2.2).mpr (he.2.2.mpr rfl)

end InverseBlocks

end BenIsraelGreville.Chapter06
