/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter06.Section01
import NumlibSurface.BenIsraelGreville.Chapter00.Section06
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse
import Numlib.LinearAlgebra.Matrix.Aeval

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

section SimultaneousRectangularDiagonalization

open Polynomial

private theorem aeval_mul_of_mul_eq_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {X : Matrix m m ℂ} {Y : Matrix n n ℂ}
    {C : Matrix m n ℂ} (h : X * C = C * Y) (f : ℂ[X]) :
    aeval X f * C = C * aeval Y f := by
  have hpow (k : ℕ) : X ^ k * C = C * Y ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc X, h, Matrix.mul_assoc]
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hf, hg]
  | monomial k a =>
    simp only [aeval_monomial, ← Algebra.smul_def, Matrix.smul_mul, Matrix.mul_smul, hpow]

private theorem unitary_coordinate_mul {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] {U : Matrix m m ℂ} {V : Matrix n n ℂ} {W : Matrix p p ℂ}
    (hV : V * Vᴴ = 1) (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    (Uᴴ * A * V) * (Vᴴ * B * W) = Uᴴ * (A * B) * W := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V, hV, Matrix.one_mul]

private theorem unitary_coordinate_adjoint {m n : Type*} [Fintype m] [Fintype n]
    (U : Matrix m m ℂ) (V : Matrix n n ℂ) (A : Matrix m n ℂ) :
    (Uᴴ * A * V)ᴴ = Vᴴ * Aᴴ * U := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

private theorem unitary_coordinate_normal {m : Type*} [Fintype m] [DecidableEq m]
    {U X : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ) (hX : IsStarNormal X) :
    IsStarNormal (Uᴴ * X * U) := by
  have he := hX.map (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) (star ⟨U, hU⟩))
  simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star, star_eq_conjTranspose] using he

private def splitFin {r m : ℕ} (h : r ≤ m) : (Fin r ⊕ Fin (m - r)) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

private theorem splitFin_inl {r m : ℕ} (h : r ≤ m) (i : Fin r) :
    (splitFin h (Sum.inl i) : ℕ) = i := by simp [splitFin]

private theorem splitFin_inr {r m : ℕ} (h : r ≤ m) (i : Fin (m - r)) :
    (splitFin h (Sum.inr i) : ℕ) = r + i := by simp [splitFin]

private theorem submatrix_rectDiagonal_split {m n r : ℕ} (hm : r ≤ m) (hn : r ≤ n)
    (d : ℕ → ℂ) :
    (rectDiagonal d : Matrix (Fin m) (Fin n) ℂ).submatrix (splitFin hm) (splitFin hn) =
      fromBlocks (diagonal (fun i : Fin r => d i)) 0 0
        (rectDiagonal (fun i => d (r + i)) : Matrix (Fin (m - r)) (Fin (n - r)) ℂ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [submatrix_apply, rectDiagonal_apply, splitFin_inl, fromBlocks_apply₁₁,
      diagonal_apply, Fin.ext_iff]
  · have hn' : (i : ℕ) ≠ r + (j : ℕ) := by omega
    simp only [submatrix_apply, rectDiagonal_apply, splitFin_inl, splitFin_inr,
      fromBlocks_apply₁₂, hn', ite_false]
    rfl
  · have hn' : r + (i : ℕ) ≠ (j : ℕ) := by omega
    simp only [submatrix_apply, rectDiagonal_apply, splitFin_inl, splitFin_inr,
      fromBlocks_apply₂₁, hn', ite_false]
    rfl
  · simp only [submatrix_apply, rectDiagonal_apply, splitFin_inr, fromBlocks_apply₂₂,
      Nat.add_left_cancel_iff]

private theorem submatrix_equiv_normal {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k] (e : k ≃ m) {X : Matrix m m ℂ} (hX : IsStarNormal X) :
    IsStarNormal (X.submatrix e e) := by
  refine ⟨?_⟩
  have he : Xᴴ * X = X * Xᴴ := hX.star_comm_self.eq
  change (X.submatrix e e)ᴴ * X.submatrix e e = X.submatrix e e * (X.submatrix e e)ᴴ
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, he]

private theorem block_unitary {r s m : Type*} [Fintype r] [Fintype s] [Fintype m]
    [DecidableEq r] [DecidableEq s] [DecidableEq m] (e : r ⊕ s ≃ m)
    {Q : Matrix r r ℂ} {P : Matrix s s ℂ} (hQ : Q ∈ unitaryGroup r ℂ)
    (hP : P ∈ unitaryGroup s ℂ) :
    (fromBlocks Q 0 0 P).submatrix e.symm e.symm ∈ unitaryGroup m ℂ := by
  apply mem_unitaryGroup_iff'.mpr
  rw [star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv, fromBlocks_conjTranspose]
  have hQ₁ : Qᴴ * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  have hP₁ : Pᴴ * P = 1 := mem_unitaryGroup_iff'.mp hP
  simp only [conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, hQ₁, hP₁, fromBlocks_one, submatrix_one_equiv]

private theorem conjugate_back_from_blocks {m n r : ℕ} (hm : r ≤ m) (hn : r ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) (L : Matrix (Fin r ⊕ Fin (m - r)) (Fin r ⊕ Fin (m - r)) ℂ)
    (R : Matrix (Fin r ⊕ Fin (n - r)) (Fin r ⊕ Fin (n - r)) ℂ) (d : ℕ → ℂ)
    (h : Lᴴ * A.submatrix (splitFin hm) (splitFin hn) * R =
      (rectDiagonal d : Matrix (Fin m) (Fin n) ℂ).submatrix (splitFin hm) (splitFin hn)) :
    (L.submatrix (splitFin hm).symm (splitFin hm).symm)ᴴ * A *
      R.submatrix (splitFin hn).symm (splitFin hn).symm = rectDiagonal d := by
  have he := congrArg (fun X : Matrix (Fin r ⊕ Fin (m - r)) (Fin r ⊕ Fin (n - r)) ℂ =>
    X.submatrix (splitFin hm).symm (splitFin hn).symm) h
  rw [← submatrix_mul_equiv _ _ _ (splitFin hn).symm,
    ← submatrix_mul_equiv _ _ _ (splitFin hm).symm, ← conjTranspose_submatrix,
    submatrix_submatrix, submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm,
    submatrix_id_id, submatrix_id_id] at he
  exact he


private theorem real_diagonal_isHermitian {r : Type*} [DecidableEq r] (s : r → ℝ) :
    (diagonal (fun i => (s i : ℂ))).IsHermitian := by
  change (diagonal (fun i => (s i : ℂ)))ᴴ = _
  rw [diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

private theorem support_blocks_of_gram_intertwining {r m n : ℕ} (s : Fin r → ℝ)
    (hs : ∀ i, 0 < s i) (C : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin n) ℂ)
    (h : let D : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin n) ℂ :=
       fromBlocks (diagonal (fun i => (s i : ℂ))) 0 0 0
      D * Dᴴ * C = C * (Dᴴ * D)) :
    C = fromBlocks C.toBlocks₁₁ 0 0 C.toBlocks₂₂ ∧
      Commute (diagonal (fun i => (s i : ℂ))) C.toBlocks₁₁ := by
  let S := diagonal (fun i => (s i : ℂ))
  let E := diagonal (fun i => (s i : ℂ) ^ 2)
  let D : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin n) ℂ := fromBlocks S 0 0 0
  change D * Dᴴ * C = C * (Dᴴ * D) at h
  have hD : Dᴴ = (fromBlocks S 0 0 0 : Matrix (Fin r ⊕ Fin n) (Fin r ⊕ Fin m) ℂ) := by
    have hS : Sᴴ = S := (real_diagonal_isHermitian s).eq
    simp only [D, fromBlocks_conjTranspose, conjTranspose_zero, hS]
  have hE : S * S = E := by
    simp only [S, E, diagonal_mul_diagonal, pow_two]
  rw [hD] at h
  simp only [D, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, hE] at h
  rw [← fromBlocks_toBlocks C] at h
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero] at h
  have hc11 : E * C.toBlocks₁₁ = C.toBlocks₁₁ * E := by
    simpa only [toBlocks_fromBlocks₁₁] using congrArg Matrix.toBlocks₁₁ h
  have hc12 : E * C.toBlocks₁₂ = 0 := by
    simpa only [toBlocks_fromBlocks₁₂] using congrArg Matrix.toBlocks₁₂ h
  have hc21 : C.toBlocks₂₁ * E = 0 := by
    simpa only [toBlocks_fromBlocks₂₁] using (congrArg Matrix.toBlocks₂₁ h).symm
  have hs0 (i : Fin r) : (s i : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hs i).ne')
  have h12 : C.toBlocks₁₂ = 0 := by
    ext i j
    have he := congrFun (congrFun hc12 i) j
    rw [show (E * C.toBlocks₁₂) i j = _ from diagonal_mul _ _ _ _] at he
    exact (mul_eq_zero.mp he).resolve_left (hs0 i)
  have h21 : C.toBlocks₂₁ = 0 := by
    ext i j
    have he := congrFun (congrFun hc21 i) j
    rw [show (C.toBlocks₂₁ * E) i j = _ from mul_diagonal _ _ _ _] at he
    exact (mul_eq_zero.mp he).resolve_right (hs0 j)
  refine ⟨by conv_lhs => rw [← fromBlocks_toBlocks C, h12, h21], ?_⟩
  change S * C.toBlocks₁₁ = C.toBlocks₁₁ * S
  ext i j
  rw [show (S * C.toBlocks₁₁) i j = _ from diagonal_mul _ _ _ _,
    show (C.toBlocks₁₁ * S) i j = _ from mul_diagonal _ _ _ _]
  by_cases h0 : C.toBlocks₁₁ i j = 0
  · rw [h0, mul_zero, zero_mul]
  have he := congrFun (congrFun hc11 i) j
  rw [show (E * C.toBlocks₁₁) i j = _ from diagonal_mul _ _ _ _,
    show (C.toBlocks₁₁ * E) i j = _ from mul_diagonal _ _ _ _, mul_comm (C.toBlocks₁₁ i j)] at he
  have he' : s i ^ 2 = s j ^ 2 := by exact_mod_cast mul_right_cancel₀ h0 he
  have hs' := (pow_left_inj₀ (hs i).le (hs j).le two_ne_zero).mp he'
  change (s i : ℂ) * C.toBlocks₁₁ i j = C.toBlocks₁₁ i j * (s j : ℂ)
  rw [hs', mul_comm]

private theorem normal_first_block {r m : Type*} [Fintype r] [Fintype m]
    [DecidableEq r] [DecidableEq m] {X : Matrix r r ℂ} :
    IsStarNormal (fromBlocks X 0 0 (0 : Matrix m m ℂ)) → IsStarNormal X := by
  intro h
  have he : (fromBlocks X 0 0 (0 : Matrix m m ℂ))ᴴ * fromBlocks X 0 0 (0 : Matrix m m ℂ) =
      fromBlocks X 0 0 (0 : Matrix m m ℂ) * (fromBlocks X 0 0 (0 : Matrix m m ℂ))ᴴ :=
    h.star_comm_self.eq
  simp only [fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero] at he
  refine ⟨?_⟩
  change Xᴴ * X = X * Xᴴ
  simpa only [toBlocks_fromBlocks₁₁] using congrArg Matrix.toBlocks₁₁ he

private theorem hermitian_first_block {r m : Type*} {X : Matrix r r ℂ} :
    (fromBlocks X 0 0 (0 : Matrix m m ℂ)).IsHermitian → X.IsHermitian := by
  intro h
  change Xᴴ = X
  simpa only [fromBlocks_conjTranspose, toBlocks_fromBlocks₁₁] using
    congrArg Matrix.toBlocks₁₁ h.eq

private theorem simultaneous_on_positive_support {r : ℕ} (s : Fin r → ℝ) (hs : ∀ i, 0 < s i)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (hComm : Commute (diagonal (fun i => (s i : ℂ))) X)
    (hNormal : IsStarNormal (X * diagonal (fun i => (s i : ℂ)))) :
    ∃ Q ∈ unitaryGroup (Fin r) ℂ, ∃ (a : Fin r → ℝ) (b : Fin r → ℂ),
      (∀ i, 0 < a i) ∧
      Qᴴ * diagonal (fun i => (s i : ℂ)) * Q = diagonal (fun i => (a i : ℂ)) ∧
      Qᴴ * X * Q = diagonal b ∧
      ((X * diagonal (fun i => (s i : ℂ))).IsHermitian → ∀ i, ((b i).re : ℂ) = b i) := by
  let S := diagonal (fun i => (s i : ℂ))
  let Y := X * S
  have hS := real_diagonal_isHermitian s
  have hSn : IsStarNormal S := ⟨by change Sᴴ * S = S * Sᴴ; rw [hS.eq]⟩
  have hSY : Commute S Y := hComm.mul_right (Commute.refl S)
  obtain ⟨Q, hQ, a, b, ha, hb⟩ :=
    Matrix.IsStarNormal.exists_unitary_conj_diagonal_of_commute hSn hNormal hSY
  change Qᴴ * S * Q = diagonal a at ha
  change Qᴴ * Y * Q = diagonal b at hb
  have haPos : ∀ i, 0 < a i := by
    have hPos : S.PosDef := posDef_diagonal_iff.mpr fun i => Complex.pos_iff.mpr ⟨hs i, rfl⟩
    have hQinj : Function.Injective Q.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_of_mem_unitaryGroup hQ)
    have h := hPos.conjTranspose_mul_mul_same hQinj
    rwa [ha, posDef_diagonal_iff] at h
  have haReal (i : Fin r) : ((a i).re : ℂ) = a i := by
    apply Complex.ext
    · simp
    · exact (Complex.pos_iff.mp (haPos i)).2
  have hX : (Qᴴ * X * Q) * diagonal a = diagonal b := by
    rw [← ha, unitary_coordinate_mul (mem_unitaryGroup_iff.mp hQ), hb]
  refine ⟨Q, hQ, (fun i => (a i).re), (fun i => b i / a i),
    fun i => (Complex.pos_iff.mp (haPos i)).1, ?_, ?_, ?_⟩
  · simpa only [haReal] using ha
  · ext i j
    have he := congrFun (congrFun hX i) j
    rw [mul_diagonal] at he
    by_cases hij : i = j
    · subst j
      rw [diagonal_apply_eq] at he ⊢
      exact (eq_div_iff (haPos i).ne').mpr he
    · rw [diagonal_apply_ne _ hij] at he ⊢
      exact (mul_eq_zero.mp he).resolve_right (haPos j).ne'
  · intro h i
    have he := hermitian_diagonal_has_real_entries Q h hb i
    change ((b i / a i).re : ℂ) = b i / a i
    rw [← he, ← haReal i, ← Complex.ofReal_div]
    simp


private theorem simultaneous_rectangular_diagonal_of_normal_cross {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℂ) (hNormal : IsStarNormal (B * Aᴴ))
    (hGram : (A * Aᴴ) * B = B * (Aᴴ * A)) :
    ∃ U ∈ unitaryGroup (Fin m) ℂ, ∃ V ∈ unitaryGroup (Fin n) ℂ,
      ∃ (a : ℕ → ℝ) (b : ℕ → ℂ), (∀ i, 0 ≤ a i) ∧
        Uᴴ * A * V = rectDiagonal (fun i => (a i : ℂ)) ∧
        Uᴴ * B * V = rectDiagonal b ∧
        ((B * Aᴴ).IsHermitian → ∀ i, ((b i).re : ℂ) = b i) := by
  obtain ⟨U, hU, V, hV, hA⟩ := A.exists_svd
  let σ := A.sortedSingularValues
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal fun i => (σ i : ℂ)
  let C := Uᴴ * B * V
  change Uᴴ * A * V = D at hA
  have hUU : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  have hVV : V * Vᴴ = 1 := mem_unitaryGroup_iff.mp hV
  have hCD : C * Dᴴ = Uᴴ * (B * Aᴴ) * U := by
    rw [← hA, unitary_coordinate_adjoint]
    exact unitary_coordinate_mul hVV B Aᴴ
  have hDD₁ : D * Dᴴ = Uᴴ * (A * Aᴴ) * U := by
    rw [← hA, unitary_coordinate_adjoint]
    exact unitary_coordinate_mul hVV A Aᴴ
  have hDD₂ : Dᴴ * D = Vᴴ * (Aᴴ * A) * V := by
    rw [← hA, unitary_coordinate_adjoint]
    exact unitary_coordinate_mul hUU Aᴴ A
  have hC : D * Dᴴ * C = C * (Dᴴ * D) := calc
    _ = Uᴴ * ((A * Aᴴ) * B) * V := by
      rw [hDD₁]
      exact unitary_coordinate_mul hUU (A * Aᴴ) B
    _ = Uᴴ * (B * (Aᴴ * A)) * V := by rw [hGram]
    _ = _ := by
      rw [hDD₂]
      exact (unitary_coordinate_mul hVV B (Aᴴ * A)).symm
  let r := A.rank
  have hm : r ≤ m := A.rank_le_height
  have hn : r ≤ n := A.rank_le_width
  let eₘ := splitFin hm
  let eₙ := splitFin hn
  let s (i : Fin r) := σ i
  let S := diagonal (fun i => (s i : ℂ))
  let X := C.submatrix eₘ eₙ
  let D' : Matrix (Fin r ⊕ Fin (m - r)) (Fin r ⊕ Fin (n - r)) ℂ := fromBlocks S 0 0 0
  have hσ (i : Fin r) : 0 < s i :=
    lt_of_le_of_ne (A.sortedSingularValues_nonneg i)
      (Ne.symm ((A.sortedSingularValues_eq_zero_iff_rank_le i).not.mpr (not_le.mpr i.isLt)))
  have hD' : D.submatrix eₘ eₙ = D' := by
    change (rectDiagonal (fun i => (σ i : ℂ)) : Matrix (Fin m) (Fin n) ℂ).submatrix eₘ eₙ = D'
    rw [submatrix_rectDiagonal_split hm hn]
    have h0 (i : ℕ) : σ (r + i) = 0 :=
      (A.sortedSingularValues_eq_zero_iff_rank_le _).mpr (Nat.le_add_right _ _)
    simp only [D', S, s, h0, Complex.ofReal_zero]
    congr 1
    ext i j
    simp [rectDiagonal_apply]
  have hGram' : D' * D'ᴴ * X = X * (D'ᴴ * D') := by
    have h := congrArg (fun Y : Matrix (Fin m) (Fin n) ℂ => Y.submatrix eₘ eₙ) hC
    simpa only [← submatrix_mul_equiv _ _ _ eₘ, ← submatrix_mul_equiv _ _ _ eₙ,
      ← conjTranspose_submatrix, hD', X] using h
  obtain ⟨hX, hXcomm⟩ := support_blocks_of_gram_intertwining s hσ X hGram'
  let X₁ := X.toBlocks₁₁
  let X₂ := X.toBlocks₂₂
  have hDX : X * D'ᴴ = fromBlocks (X₁ * S) 0 0 (0 : Matrix (Fin (m - r)) (Fin (m - r)) ℂ) := by
    conv_lhs => rw [hX]
    have hS : Sᴴ = S := (real_diagonal_isHermitian s).eq
    simp only [D', fromBlocks_conjTranspose, conjTranspose_zero, hS,
      fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, X₁]
  have hCross : X * D'ᴴ = (Uᴴ * (B * Aᴴ) * U).submatrix eₘ eₘ := by
    have h := congrArg (fun Y : Matrix (Fin m) (Fin m) ℂ => Y.submatrix eₘ eₘ) hCD
    simpa only [← submatrix_mul_equiv _ _ _ eₙ, ← conjTranspose_submatrix, hD', X] using h
  have hNormal₁ : IsStarNormal (X₁ * S) := by
    apply normal_first_block (m := Fin (m - r))
    rw [← hDX, hCross]
    exact submatrix_equiv_normal eₘ (unitary_coordinate_normal hU hNormal)
  obtain ⟨Q, hQ, a, b, haPos, ha, hb, hbReal⟩ :=
    simultaneous_on_positive_support s hσ X₁ hXcomm hNormal₁
  obtain ⟨P, hP, R, hR, h₂⟩ := X₂.exists_svd
  let τ := X₂.sortedSingularValues
  change Pᴴ * X₂ * R = rectDiagonal (fun i => (τ i : ℂ)) at h₂
  let L := fromBlocks Q 0 0 P
  let M := fromBlocks Q 0 0 R
  let L₀ := L.submatrix eₘ.symm eₘ.symm
  let M₀ := M.submatrix eₙ.symm eₙ.symm
  let a₀ (i : ℕ) : ℝ := if h : i < r then a ⟨i, h⟩ else 0
  let b₀ (i : ℕ) : ℂ := if h : i < r then b ⟨i, h⟩ else (τ (i - r) : ℂ)
  have hDA : Lᴴ * D.submatrix eₘ eₙ * M =
      (rectDiagonal (fun i => (a₀ i : ℂ)) : Matrix (Fin m) (Fin n) ℂ).submatrix eₘ eₙ := by
    rw [hD', submatrix_rectDiagonal_split hm hn]
    simp only [L, M, D', fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero]
    have h00 (i : ℕ) : a₀ (r + i) = 0 := dite_eq_right (by omega)
    simp only [h00, Complex.ofReal_zero]
    have ha₀ (i : Fin r) : a₀ i = a i := dite_eq_left i.isLt
    simp only [ha₀]
    congr 1
    ext i j
    simp [rectDiagonal_apply]
  have hDB : Lᴴ * C.submatrix eₘ eₙ * M =
      (rectDiagonal b₀ : Matrix (Fin m) (Fin n) ℂ).submatrix eₘ eₙ := by
    rw [submatrix_rectDiagonal_split hm hn]
    change Lᴴ * X * M = _
    rw [hX]
    simp only [L, M, fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, ← show X₁ = X.toBlocks₁₁ from rfl,
      ← show X₂ = X.toBlocks₂₂ from rfl, hb, h₂]
    have hb₀ (i : Fin r) : b₀ i = b i := dite_eq_left i.isLt
    have h₂₀ (i : ℕ) : b₀ (r + i) = (τ i : ℂ) := by
      dsimp only [b₀]
      rw [dite_eq_right (by omega), Nat.add_sub_cancel_left]
    simp only [hb₀, h₂₀]
  have hLa := conjugate_back_from_blocks hm hn D L M (fun i => (a₀ i : ℂ)) hDA
  have hMb := conjugate_back_from_blocks hm hn C L M b₀ hDB
  refine ⟨U * L₀, mul_mem hU (block_unitary eₘ hQ hP),
    V * M₀, mul_mem hV (block_unitary eₙ hQ hR), a₀, b₀, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only [a₀]
    split_ifs with hi
    · exact (haPos ⟨i, hi⟩).le
    · exact le_rfl
  · calc
      _ = L₀ᴴ * (Uᴴ * A * V) * M₀ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := hA ▸ hLa
  · calc
      _ = L₀ᴴ * C * M₀ := by simp only [C, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := hMb
  · intro h i
    have h₁ : (X₁ * S).IsHermitian := by
      apply hermitian_first_block (m := Fin (m - r))
      rw [← hDX, hCross]
      exact (isHermitian_conjTranspose_mul_mul U h).submatrix eₘ
    dsimp only [b₀]
    split_ifs with hi
    · exact hbReal h₁ ⟨i, hi⟩
    · rw [Complex.ofReal_re]


private theorem rectangular_cross_coordinates {m n : ℕ} {A B : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitaryGroup (Fin m) ℂ) (hV : V ∈ unitaryGroup (Fin n) ℂ)
    {a b : ℕ → ℂ} (hA : Uᴴ * A * V = rectDiagonal a) (hB : Uᴴ * B * V = rectDiagonal b) :
    Uᴴ * (A * Bᴴ) * U =
        diagonal (fun i : Fin m => if (i : ℕ) < n then a i * star (b i) else 0) ∧
      Vᴴ * (Bᴴ * A) * V =
        diagonal (fun i : Fin n => if (i : ℕ) < m then star (b i) * a i else 0) := by
  constructor
  · rw [← unitary_coordinate_mul (mem_unitaryGroup_iff.mp hV) A Bᴴ,
      ← unitary_coordinate_adjoint U V B, hA, hB, rectDiagonal_conjTranspose,
      rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    rfl
  · rw [← unitary_coordinate_mul (mem_unitaryGroup_iff.mp hU) Bᴴ A,
      ← unitary_coordinate_adjoint U V B, hA, hB, rectDiagonal_conjTranspose,
      rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    rfl

private theorem hermitian_of_unitary_coordinate_hermitian {m : Type*} [Fintype m] [DecidableEq m]
    {U H : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ) (hH : (Uᴴ * H * U).IsHermitian) :
    H.IsHermitian := by
  have h := isHermitian_conjTranspose_mul_mul Uᴴ hH
  rw [conjTranspose_conjTranspose] at h
  have hUU : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  have he : U * (Uᴴ * H * U) * Uᴴ = H := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hUU, Matrix.one_mul, Matrix.mul_one]
  rwa [he] at h

/-- **Exercise 15** of [benIsrael2003generalized], Chapter 6. The two Hermitian
cross-product conditions also allow the first simultaneous diagonal to be
chosen nonnegative. -/
theorem exercise_15_nonnegative {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ)
    (h₁ : (A * Bᴴ).IsHermitian) (h₂ : (Bᴴ * A).IsHermitian) :
    ∃ U ∈ unitaryGroup (Fin m) ℂ, ∃ V ∈ unitaryGroup (Fin n) ℂ,
      ∃ a b : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧
        Uᴴ * A * V = rectDiagonal (fun i => (a i : ℂ)) ∧
        Uᴴ * B * V = rectDiagonal (fun i => (b i : ℂ)) := by
  have h₁' : B * Aᴴ = A * Bᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using h₁.eq
  have h₂' : Aᴴ * B = Bᴴ * A := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using h₂.eq
  have hX : (B * Aᴴ).IsHermitian := h₁' ▸ h₁
  have hNormal : IsStarNormal (B * Aᴴ) := ⟨by
    change (B * Aᴴ)ᴴ * (B * Aᴴ) = (B * Aᴴ) * (B * Aᴴ)ᴴ
    rw [hX.eq]⟩
  have hGram : (A * Aᴴ) * B = B * (Aᴴ * A) := by
    rw [Matrix.mul_assoc, h₂', ← Matrix.mul_assoc, ← h₁', Matrix.mul_assoc]
  obtain ⟨U, hU, V, hV, a, b, ha, hA, hB, hb⟩ :=
    simultaneous_rectangular_diagonal_of_normal_cross A B hNormal hGram
  exact ⟨U, hU, V, hV, a, fun i => (b i).re, ha, hA, by simpa only [hb hX]⟩

/-- **Exercise 15** of [benIsrael2003generalized], Chapter 6. A rectangular
pair has a simultaneous real diagonalization by two unitary factors if
and only if both cross products are Hermitian. -/
theorem exercise_15 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (∃ U ∈ unitaryGroup (Fin m) ℂ, ∃ V ∈ unitaryGroup (Fin n) ℂ,
      ∃ a b : ℕ → ℝ,
        Uᴴ * A * V = rectDiagonal (fun i => (a i : ℂ)) ∧
        Uᴴ * B * V = rectDiagonal (fun i => (b i : ℂ))) ↔
      (A * Bᴴ).IsHermitian ∧ (Bᴴ * A).IsHermitian := by
  constructor
  · rintro ⟨U, hU, V, hV, a, b, hA, hB⟩
    obtain ⟨h₁, h₂⟩ := rectangular_cross_coordinates hU hV hA hB
    refine ⟨hermitian_of_unitary_coordinate_hermitian hU ?_,
      hermitian_of_unitary_coordinate_hermitian hV ?_⟩
    · rw [h₁]
      simpa only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_zero,
        ← apply_ite (fun z : ℝ => (z : ℂ))] using
        real_diagonal_isHermitian (fun i : Fin m => if (i : ℕ) < n then a i * b i else 0)
    · rw [h₂]
      simpa only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_zero,
        ← apply_ite (fun z : ℝ => (z : ℂ))] using
        real_diagonal_isHermitian (fun i : Fin n => if (i : ℕ) < m then b i * a i else 0)
  · rintro ⟨h₁, h₂⟩
    obtain ⟨U, hU, V, hV, a, b, -, hA, hB⟩ := exercise_15_nonnegative A B h₁ h₂
    exact ⟨U, hU, V, hV, a, b, hA, hB⟩

private theorem fromBlocks_normal_adjoint {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {X : Matrix m m ℂ} {Y : Matrix n n ℂ}
    (hX : IsStarNormal X) (hY : IsStarNormal Y) :
    IsStarNormal (fromBlocks Xᴴ 0 0 Yᴴ) := by
  have hXe : Xᴴ * X = X * Xᴴ := hX.star_comm_self.eq
  have hYe : Yᴴ * Y = Y * Yᴴ := hY.star_comm_self.eq
  refine ⟨?_⟩
  change (fromBlocks Xᴴ 0 0 Yᴴ)ᴴ * fromBlocks Xᴴ 0 0 Yᴴ =
    fromBlocks Xᴴ 0 0 Yᴴ * (fromBlocks Xᴴ 0 0 Yᴴ)ᴴ
  simp only [fromBlocks_conjTranspose, conjTranspose_conjTranspose, conjTranspose_zero,
    fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, hXe, hYe]

/-- **Exercise 17** of [benIsrael2003generalized], Chapter 6. The same
polynomial in the two adjoint cross products characterizes simultaneous
complex diagonalization by two unitary factors. -/
theorem exercise_17 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (∃ U ∈ unitaryGroup (Fin m) ℂ, ∃ V ∈ unitaryGroup (Fin n) ℂ,
      ∃ a b : ℕ → ℂ, Uᴴ * A * V = rectDiagonal a ∧ Uᴴ * B * V = rectDiagonal b) ↔
      ∃ f : ℂ[X], A * Bᴴ = aeval (B * Aᴴ) f ∧ Bᴴ * A = aeval (Aᴴ * B) f := by
  constructor
  · rintro ⟨U, hU, V, hV, a, b, hA, hB⟩
    obtain ⟨h₁, h₂⟩ := rectangular_cross_coordinates hU hV hA hB
    have hX : IsStarNormal (A * Bᴴ) :=
      Matrix.IsStarNormal.spectral_theorem.mpr ⟨U, hU, _, h₁⟩
    have hY : IsStarNormal (Bᴴ * A) :=
      Matrix.IsStarNormal.spectral_theorem.mpr ⟨V, hV, _, h₂⟩
    obtain ⟨f, hf⟩ := Matrix.IsStarNormal.exists_aeval_eq_conjTranspose
      (fromBlocks_normal_adjoint hX hY)
    simp only [aeval_fromBlocks_zero, fromBlocks_conjTranspose, conjTranspose_conjTranspose,
      conjTranspose_zero, conjTranspose_mul] at hf
    refine ⟨f, ?_, ?_⟩
    · simpa only [toBlocks_fromBlocks₁₁] using (congrArg Matrix.toBlocks₁₁ hf).symm
    · simpa only [toBlocks_fromBlocks₂₂] using (congrArg Matrix.toBlocks₂₂ hf).symm
  · rintro ⟨f, hf₁, hf₂⟩
    have hXF : (B * Aᴴ)ᴴ = aeval (B * Aᴴ) f := by
      simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using hf₁
    have hNormal : IsStarNormal (B * Aᴴ) := ⟨by
      change (B * Aᴴ)ᴴ * (B * Aᴴ) = (B * Aᴴ) * (B * Aᴴ)ᴴ
      rw [hXF]
      exact ((Commute.refl (B * Aᴴ)).aeval_left f).eq⟩
    have h := aeval_mul_of_mul_eq_mul (Matrix.mul_assoc Aᴴ B Aᴴ) f
    rw [← hf₁, ← hf₂] at h
    have hGram : (A * Aᴴ) * B = B * (Aᴴ * A) := by
      simpa only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using
        congrArg conjTranspose h
    obtain ⟨U, hU, V, hV, a, b, -, hA, hB, -⟩ :=
      simultaneous_rectangular_diagonal_of_normal_cross A B hNormal hGram
    exact ⟨U, hU, V, hV, (fun i => (a i : ℂ)), b, hA, hB⟩

end SimultaneousRectangularDiagonalization

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

/-- **Exercise 19**, Equations (38)–(40), of [benIsrael2003generalized].
For a normal matrix the complex singular diagonal consists of the sorted
eigenvalues, and a single column basis gives both singular-vector families. -/
theorem exercise_19 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    ∃ U d, IsUDVDecomposition A U d U ∧ ∀ i : Fin n,
      A *ᵥ U.col i = d i • U.col i ∧ Aᴴ *ᵥ U.col i = star (d i) • U.col i := by
  obtain ⟨U, hU, d, hd, hs⟩ := exercise_6 hA
  have h : IsUDVDecomposition A U d U :=
    ⟨hU, hU, by simpa only [rectDiagonal_eq_diagonal] using hd, hs⟩
  exact ⟨U, d, h, fun i => phaseSingularVectorPair h i i.isLt i.isLt⟩

/-- **Exercise 20** of [benIsrael2003generalized], Chapter 6.
The common-basis complex singular decomposition of a normal matrix is
a unitary similarity to its eigenvalue diagonal. -/
theorem exercise_20 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    ∃ U d, IsUDVDecomposition A U d U ∧
      Uᴴ * A * U = diagonal (fun i : Fin n => d i) := by
  obtain ⟨U, d, h, _⟩ := exercise_19 hA
  refine ⟨U, d, h, ?_⟩
  have hU := conjTranspose_mul_self_of_mem_unitaryGroup h.1
  rw [h.2.2.1]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
    Matrix.mul_one, rectDiagonal_eq_diagonal]

/-- **Exercise 24**, Equation (44), of [benIsrael2003generalized].
Every singular value of an inner inverse is at least the corresponding
singular value of the Moore–Penrose inverse, with both sequences padded by zero. -/
theorem exercise_24 {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜}
    {G : Matrix (Fin n) (Fin m) 𝕜} (hG : A.IsInnerInverse G) (i : ℕ) :
    A.pinv.sortedSingularValues i ≤ G.sortedSingularValues i := by
  let r := A.rank
  by_cases hi : i < r
  · obtain ⟨U, hU, V, hV, hS⟩ := A.exists_svd
    let σ := A.sortedSingularValues
    let f : ℕ → 𝕜 := fun j => (σ j : 𝕜)
    let D : Matrix (Fin m) (Fin n) 𝕜 := rectDiagonal f
    let C := Vᴴ * G * U
    let S : Matrix (Fin r) (Fin r) 𝕜 := rectDiagonal f
    have hf (j : Fin r) : f j ≠ 0 := by
      intro hz
      have hzr : σ j = 0 := RCLike.ofReal_eq_zero.mp hz
      exact (not_le_of_gt j.isLt) ((A.sortedSingularValues_eq_zero_iff_rank_le j).mp hzr)
    have hC : D * C * D = D := by
      have h := congrArg (fun B : Matrix (Fin m) (Fin n) 𝕜 => Uᴴ * B * V) (isInnerInverse_iff.mp hG)
      change Uᴴ * A * V = D at hS
      change Uᴴ * (A * G * A) * V = Uᴴ * A * V at h
      rw [← hS]
      have hVV := mul_conjTranspose_self_of_mem_unitaryGroup hV
      have hUU := mul_conjTranspose_self_of_mem_unitaryGroup hU
      simp only [C, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc V Vᴴ, hVV, Matrix.one_mul,
        ← Matrix.mul_assoc U Uᴴ, hUU, Matrix.one_mul]
      simpa only [Matrix.mul_assoc] using h
    have hEntry (j k : Fin r) :
        C (Fin.castLE A.rank_le_width j) (Fin.castLE A.rank_le_height k) =
          (rectDiagonal (fun j => (f j)⁻¹) : Matrix (Fin r) (Fin r) 𝕜) j k := by
      have hjm := j.isLt.trans_le A.rank_le_height
      have hkn := k.isLt.trans_le A.rank_le_width
      have h := congrArg (fun B : Matrix (Fin m) (Fin n) 𝕜 =>
        B ⟨j, hjm⟩ ⟨k, hkn⟩) hC
      change ((D * C) * D) (⟨j, hjm⟩ : Fin m) ⟨k, hkn⟩ = _ at h
      dsimp only [D] at h
      rw [mul_rectDiagonal_apply, dite_eq_left (k.isLt.trans_le A.rank_le_height)] at h
      have hrow := rectDiagonal_mul_apply (m := m) (n := n) f C (⟨j, hjm⟩ : Fin m)
        (Fin.castLE A.rank_le_height k) (j.isLt.trans_le A.rank_le_width)
      change (D * C) (⟨j, hjm⟩ : Fin m) (Fin.castLE A.rank_le_height k) * f k = _ at h
      have h' := congrArg (fun a => a * f k) hrow
      have h := h'.symm.trans h
      change f j * C (Fin.castLE A.rank_le_width j) (Fin.castLE A.rank_le_height k) * f k =
        (rectDiagonal f : Matrix (Fin m) (Fin n) 𝕜) ⟨j, hjm⟩ ⟨k, hkn⟩ at h
      rw [rectDiagonal_apply] at h ⊢
      by_cases hjk : j.val = k.val
      · have hjk' : j = k := Fin.ext hjk
        subst k
        simp only [ite_true] at h ⊢
        have hc : C (Fin.castLE A.rank_le_width j) (Fin.castLE A.rank_le_height j) * f j = 1 := by
          apply mul_left_cancel₀ (hf j)
          simpa only [← mul_assoc, mul_one] using h
        exact eq_inv_of_mul_eq_one_left hc
      · simp only [ite_eq_right hjk] at h ⊢
        rcases mul_eq_zero.mp h with h' | hk
        · exact (mul_eq_zero.mp h').resolve_left (hf j)
        · exact False.elim (hf k hk)
    have hSigma : S.IsSVD 1 σ 1 :=
      ⟨⟨one_mem _, one_mem _, by simp [S, f]⟩,
        A.sortedSingularValues_antitone, A.sortedSingularValues_nonneg⟩
    have hSigma_rank : S.rank = r := by
      apply le_antisymm S.rank_le_width
      by_contra! h
      exact hf ⟨S.rank, h⟩ (RCLike.ofReal_eq_zero.mpr (by
        rw [hSigma.singularValues_eq h h]
        exact (S.sortedSingularValues_eq_zero_iff_rank_le _).mpr le_rfl))
    have hSigma_inv : S.pinv =
        (rectDiagonal (fun j => (f j)⁻¹) : Matrix (Fin r) (Fin r) 𝕜) := by
      simpa [f] using hSigma.pinv_eq
    have hsub : C.submatrix (Fin.castLE A.rank_le_width) (Fin.castLE A.rank_le_height) =
        S.pinv := by
      rw [hSigma_inv]
      exact Matrix.ext hEntry
    have hcompare := sortedSingularValues_submatrix_le C
      (Fin.castLE_injective A.rank_le_width) (Fin.castLE_injective A.rank_le_height) i
    rw [hsub, exercise_7, hSigma_rank, ite_eq_left hi,
      ← hSigma.singularValues_eq (show r - 1 - i < r by omega)
        (show r - 1 - i < r by omega)] at hcompare
    have hCσ : C.sortedSingularValues = G.sortedSingularValues :=
      sortedSingularValues_unitary_mul_mul (A := G) (Unitary.star_mem hV) hU
    rw [hCσ] at hcompare
    rw [exercise_7, ite_eq_left hi]
    exact hcompare
  · rw [exercise_7, ite_eq_right hi]
    exact G.sortedSingularValues_nonneg i

section ComplexVolume

open scoped Matrix.Norms.Frobenius

/-- The complex matrix volume is the square root of the sum of squared
moduli of its maximal minors, with volume zero for matrices of rank zero. -/
noncomputable def complexMatrixVolume {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  if A.rank = 0 then 0 else ‖Chapter00.compound A.rank A‖

private theorem compound_conjTranspose {m n : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Chapter00.compound k Aᴴ = (Chapter00.compound k A)ᴴ := by
  ext i j
  exact det_conjTranspose (A.submatrix j i)

/-- **Exercise 21**, Equation (41), of [benIsrael2003generalized], Chapter 6.
The volume from the squared moduli of the complex maximal minors is the
product of the positive singular values. -/
theorem exercise_21_complex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (hA : A.rank ≠ 0) :
    complexMatrixVolume A = ∏ i : Fin A.rank, A.sortedSingularValues i := by
  classical
  let r := A.rank
  let σ := A.sortedSingularValues
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal (fun j => (σ j : ℂ))
  let s₀ : Chapter00.IndexSequence r n := Fin.castLEOrderEmb A.rank_le_width
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  have hAeq : A = U * D * Vᴴ := eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  have hD : Dᴴ * D = diagonal (fun j : Fin n => ((σ j ^ 2 : ℝ) : ℂ)) := by
    dsimp only [D]
    rw [conjTranspose_rectDiagonal_mul_self]
    apply congrArg diagonal
    funext j
    by_cases hj : j.val < m
    · simp [hj, sq]
    · simp [hj, σ, (A.sortedSingularValues_eq_zero_iff_rank_le j).mpr
        (A.rank_le_height.trans (Nat.le_of_not_gt hj))]
  have hGram : Aᴴ * A = V * (Dᴴ * D) * Vᴴ := by
    rw [hAeq, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U,
      conjTranspose_mul_self_of_mem_unitaryGroup hU, Matrix.one_mul]
  have htrace : trace (Chapter00.compound r (Aᴴ * A)) =
      trace (Chapter00.compound r (Dᴴ * D)) := by
    rw [hGram, Chapter00.compound_mul, Chapter00.compound_mul, trace_mul_comm,
      ← Matrix.mul_assoc, ← Chapter00.compound_mul, conjTranspose_mul_self_of_mem_unitaryGroup hV,
      Chapter00.compound_one, Matrix.one_mul]
  have hprod : trace (Chapter00.compound r (Dᴴ * D)) = ((∏ i : Fin r, σ i ^ 2 : ℝ) : ℂ) := by
    rw [hD, Chapter00.compound_diagonal, trace_diagonal]
    rw [Finset.sum_eq_single s₀]
    · push_cast
      rfl
    · intro s _ hs
      have hb : ∃ j, r ≤ (s j).val := by
        by_contra! hall
        let t : Chapter00.IndexSequence r r :=
          OrderEmbedding.ofStrictMono (fun j => ⟨(s j).val, hall j⟩) (fun _ _ hlt => s.strictMono hlt)
        apply hs
        ext j
        have hj := DFunLike.congr_fun (Chapter00.indexSequence_self_unique t) j
        exact congrArg (fun i : Fin r => i.val) hj
      obtain ⟨j, hj⟩ := hb
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      change ((σ (s j) ^ 2 : ℝ) : ℂ) = 0
      simp [σ, (A.sortedSingularValues_eq_zero_iff_rank_le _).mpr hj]
    · simp
  have hsq : (‖Chapter00.compound r A‖ ^ 2 : ℝ) = ∏ i : Fin r, σ i ^ 2 := by
    apply Complex.ofReal_injective
    rw [← hprod, ← htrace, Chapter00.compound_mul, compound_conjTranspose]
    exact frobenius_norm_sq_eq_trace _
  rw [complexMatrixVolume, ite_eq_right hA]
  have hnonneg : 0 ≤ ∏ i : Fin r, σ i :=
    Finset.prod_nonneg fun i _ => A.sortedSingularValues_nonneg i
  exact (pow_left_inj₀ (norm_nonneg _) hnonneg two_ne_zero).mp (hsq.trans (Finset.prod_pow ..))

/-- **Exercise 21**, geometric interpretation of [benIsrael2003generalized].
The columns of $V$ are the orthonormal edges of a unit cube in the row space.
The image edges $AV$ have complex volume equal to the volume of $A$. -/
theorem exercise_21_complex_geometric {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (V : Matrix (Fin n) (Fin r) ℂ) (hV : Vᴴ * V = 1)
    (hR : (toEuclideanLin V).range = (toEuclideanLin Aᴴ).range) :
    complexMatrixVolume (A * V) = complexMatrixVolume A := by
  classical
  have hv : V.pinv = Vᴴ := by
    symm
    apply V.pinv_unique
    · rw [Matrix.mul_assoc, hV, Matrix.mul_one]
    · rw [hV, Matrix.one_mul]
    · exact isHermitian_mul_conjTranspose_self V
    · rw [hV]
      exact isHermitian_one
  have hP : V * Vᴴ * Aᴴ = Aᴴ := by
    rw [← hv]
    exact (V.range_toEuclideanLin_le_iff_mul_pinv_mul_eq Aᴴ).mp hR.ge
  have hA : (A * V) * Vᴴ = A := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using
      congrArg conjTranspose hP
  have hRank : (A * V).rank = A.rank := by
    refine le_antisymm (rank_mul_le_left _ _) ?_
    calc
      _ = ((A * V) * Vᴴ).rank := congrArg Matrix.rank hA.symm
      _ ≤ _ := rank_mul_le_left _ _
  by_cases h0 : A.rank = 0
  · simp [complexMatrixVolume, hRank, h0]
  let k := A.rank
  let F := Chapter00.compound k V
  let C := Chapter00.compound k (A * V)
  have hF : Fᴴ * F = 1 := by
    change (Chapter00.compound k V)ᴴ * Chapter00.compound k V = 1
    rw [← compound_conjTranspose, ← Chapter00.compound_mul, hV, Chapter00.compound_one]
  have hC : C * Fᴴ = Chapter00.compound k A := by
    change Chapter00.compound k (A * V) * (Chapter00.compound k V)ᴴ = _
    rw [← compound_conjTranspose, ← Chapter00.compound_mul, hA]
  have hnorm : ‖Chapter00.compound k A‖ = ‖C‖ := calc
    _ = ‖(C * Fᴴ)ᴴ‖ := by rw [← hC, frobenius_norm_conjTranspose]
    _ = ‖F * Cᴴ‖ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
    _ = _ := by rw [frobenius_norm_mul_of_conjTranspose_mul_self_eq_one hF,
      frobenius_norm_conjTranspose]
  unfold complexMatrixVolume
  rw [hRank, ite_eq_right h0, ite_eq_right h0]
  exact hnorm.symm

end ComplexVolume

section CompoundVolume

open scoped Matrix.Norms.Frobenius

private theorem rank_pinv_eq_rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A.pinv.rank = A.rank := by
  apply le_antisymm
  · calc
      A.pinv.rank = (A.pinv * A * A.pinv).rank := congrArg Matrix.rank A.pinv_mul_self_mul_pinv.symm
      _ ≤ (A.pinv * A).rank := rank_mul_le_left _ _
      _ ≤ A.rank := rank_mul_le_right _ _
  · calc
      A.rank = (A * A.pinv * A).rank := congrArg Matrix.rank A.mul_pinv_mul_self.symm
      _ ≤ (A * A.pinv).rank := rank_mul_le_left _ _
      _ ≤ A.pinv.rank := rank_mul_le_right _ _

private theorem rank_le_of_innerInverse {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin m) ℝ} (hG : A.IsInnerInverse G) : A.rank ≤ G.rank := by
  calc
    A.rank = (A * G * A).rank := congrArg Matrix.rank (isInnerInverse_iff.mp hG).symm
    _ ≤ (A * G).rank := rank_mul_le_left _ _
    _ ≤ G.rank := rank_mul_le_right _ _

/-- **Exercise 24**, Equation (45), of [benIsrael2003generalized]. The
Moore–Penrose inverse minimizes each positive $k$-volume among the real
inner inverses for $k$ no larger than the rank of the original matrix. -/
theorem exercise_24_kVolume {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin m) ℝ} (hG : A.IsInnerInverse G) (hk : 0 < k) (hr : k ≤ A.rank) :
    Chapter00.kVolume k A.pinv ≤ Chapter00.kVolume k G := by
  have hr₁ : k ≤ A.pinv.rank := (rank_pinv_eq_rank A).symm ▸ hr
  have hr₂ : A.pinv.rank ≤ G.rank := (rank_pinv_eq_rank A).symm ▸ rank_le_of_innerInverse hG
  rw [Chapter00.kVolume_eq_sqrt_sum_singularValues_padded k A.pinv hk hr₁ hr₂,
    Chapter00.kVolume_eq_sqrt_sum_singularValues k G hk (hr₁.trans hr₂)]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro s _
  apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
  intro j _
  exact (sq_le_sq₀ (A.pinv.sortedSingularValues_nonneg _) (G.sortedSingularValues_nonneg _)).mpr
    (exercise_24 hG (s j).val)

private theorem exists_indexSequence_containing {k r : ℕ} (hk : 0 < k) (hr : k ≤ r)
    (i : Fin r) : ∃ (s : Chapter00.IndexSequence k r) (j : Fin k), s j = i := by
  classical
  have hcard : k - 1 ≤ ((Finset.univ : Finset (Fin r)).erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨T, hT, hsize⟩ := Finset.exists_subset_card_eq hcard
  have hiT : i ∉ T := fun h => Finset.notMem_erase i _ (hT h)
  let S := insert i T
  have hS : S.card = k := by
    rw [show S = insert i T from rfl, Finset.card_insert_of_notMem hiT, hsize]
    omega
  have hi : i ∈ Set.range (S.orderEmbOfFin hS) := by
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_insert_self _ _
  obtain ⟨j, hj⟩ := hi
  exact ⟨S.orderEmbOfFin hS, j, hj⟩

private theorem singularValues_eq_of_kVolume_eq {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin m) ℝ} (hG : A.IsInnerInverse G) (hk : 0 < k) (hr : k ≤ A.rank)
    (hVol : Chapter00.kVolume k G = Chapter00.kVolume k A.pinv) :
    ∀ i, G.sortedSingularValues i = A.pinv.sortedSingularValues i := by
  classical
  have hr₁ : k ≤ A.pinv.rank := (rank_pinv_eq_rank A).symm ▸ hr
  have hr₂ : A.pinv.rank ≤ G.rank := (rank_pinv_eq_rank A).symm ▸ rank_le_of_innerInverse hG
  let left (s : Chapter00.IndexSequence k G.rank) :=
    ∏ j : Fin k, A.pinv.sortedSingularValues (s j).val ^ 2
  let right (s : Chapter00.IndexSequence k G.rank) :=
    ∏ j : Fin k, G.sortedSingularValues (s j).val ^ 2
  have hterm (s : Chapter00.IndexSequence k G.rank) (j : Fin k) :
      A.pinv.sortedSingularValues (s j).val ^ 2 ≤ G.sortedSingularValues (s j).val ^ 2 :=
    (sq_le_sq₀ (A.pinv.sortedSingularValues_nonneg _) (G.sortedSingularValues_nonneg _)).mpr
      (exercise_24 hG (s j).val)
  have hle (s : Chapter00.IndexSequence k G.rank) : left s ≤ right s :=
    Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun j _ => hterm s j)
  have hsum : (∑ s, left s) = ∑ s, right s := by
    rw [Chapter00.kVolume_eq_sqrt_sum_singularValues_padded k A.pinv hk hr₁ hr₂,
      Chapter00.kVolume_eq_sqrt_sum_singularValues k G hk (hr₁.trans hr₂)] at hVol
    have he := congrArg (fun x : ℝ => x ^ 2) hVol.symm
    change Real.sqrt (∑ s, left s) ^ 2 = Real.sqrt (∑ s, right s) ^ 2 at he
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => sq_nonneg _)] at he
  intro i
  apply le_antisymm _ (exercise_24 hG i)
  by_cases hi : i < G.rank
  · by_contra! hlt
    obtain ⟨s, j, hj⟩ := exists_indexSequence_containing hk (hr₁.trans hr₂) ⟨i, hi⟩
    have hj' : (s j).val = i := congrArg Fin.val hj
    have hprod : left s < right s := by
      by_cases hpos : ∀ t : Fin k, 0 < A.pinv.sortedSingularValues (s t).val ^ 2
      · refine Finset.prod_lt_prod₀ (fun t _ => hpos t) (fun t _ => hterm s t)
          ⟨j, Finset.mem_univ _, ?_⟩
        rw [hj']
        exact (sq_lt_sq₀ (A.pinv.sortedSingularValues_nonneg _) (G.sortedSingularValues_nonneg _)).mpr hlt
      · push Not at hpos
        obtain ⟨t, ht⟩ := hpos
        have hz : left s = 0 := Finset.prod_eq_zero (Finset.mem_univ t)
          (le_antisymm ht (sq_nonneg _))
        rw [hz]
        exact Finset.prod_pos fun t _ => sq_pos_of_ne_zero fun he =>
          (not_le_of_gt (s t).isLt) ((G.sortedSingularValues_eq_zero_iff_rank_le _).mp he)
    have hltSum := Finset.sum_lt_sum (fun t _ => hle t) ⟨s, Finset.mem_univ _, hprod⟩
    rw [hsum] at hltSum
    exact (lt_irrefl _ hltSum)
  · rw [(G.sortedSingularValues_eq_zero_iff_rank_le i).mpr (not_lt.mp hi)]
    exact A.pinv.sortedSingularValues_nonneg _

private theorem innerInverse_eq_pinv_of_frobenius_sq_eq {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin m) ℝ} (hG : A.IsInnerInverse G) (hEq : ‖G‖ ^ 2 = ‖A.pinv‖ ^ 2) :
    G = A.pinv := by
  let X := A.pinv
  let D := G - X
  let P := X * A
  let Q := A * X
  have hP : Pᴴ = P := A.isHermitian_pinv_mul.eq
  have hQ : Qᴴ = Q := A.isHermitian_mul_pinv.eq
  have hX : P * X * Q = X := by simp only [P, Q, X, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]
  have hG₀ : P * G * Q = X := calc
    _ = X * (A * G * A) * X := by simp only [P, Q, Matrix.mul_assoc]
    _ = _ := by rw [isInnerInverse_iff.mp hG, A.pinv_mul_self_mul_pinv]
  have hD : P * D * Q = 0 := by rw [show D = G - X from rfl, Matrix.mul_sub, Matrix.sub_mul,
    hX, hG₀, sub_self]
  have ht : trace (Xᴴ * D) = 0 := calc
    _ = trace ((P * X * Q)ᴴ * D) := congrArg (fun Y => trace (Yᴴ * D)) hX.symm
    _ = trace (Q * (Xᴴ * P * D)) := by
      simp only [conjTranspose_mul, hP, hQ, Matrix.mul_assoc]
    _ = trace (Xᴴ * (P * D * Q)) := by
      rw [trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hD, Matrix.mul_zero, trace_zero]
  have hs := frobenius_norm_add_sq_of_trace_eq_zero ht
  have hAdd : X + D = G := by
    change X + (G - X) = G
    abel
  rw [hAdd, hEq] at hs
  have hz : ‖D‖ ^ 2 = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hz))

/-- **Exercise 25** of [benIsrael2003generalized]. Equality in the
minimum positive $k$-volume inequality characterizes the Moore–Penrose inverse. -/
theorem exercise_25 {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin m) ℝ} (hG : A.IsInnerInverse G) (hk : 0 < k) (hr : k ≤ A.rank) :
    Chapter00.kVolume k G = Chapter00.kVolume k A.pinv ↔ G = A.pinv := by
  constructor
  · intro h
    have hσ := singularValues_eq_of_kVolume_eq hG hk hr h
    apply innerInverse_eq_pinv_of_frobenius_sq_eq hG
    simp only [frobenius_norm_sq_eq_sum_sq_sortedSingularValues, hσ]
  · rintro rfl
    rfl

/-- **Exercise 22** of [benIsrael2003generalized]. The rank of the $k$th
compound is the binomial coefficient of the original rank, and its singular
values, counted with their zero terms, are the products indexed by $k$ columns. -/
theorem exercise_22 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    let C := Chapter00.compound k A
    C.rank = A.rank.choose k ∧
      ∃ e : Chapter00.IndexSequence k n ≃ Chapter00.IndexSequence k n,
        ∀ s, C.colSingularValues (e s) = ∏ j : Fin k, A.sortedSingularValues (s j).val := by
  intro C
  classical
  refine ⟨Chapter00.compound_rank k A, ?_⟩
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  let σ := A.sortedSingularValues
  let D : Matrix (Fin m) (Fin n) ℝ := rectDiagonal σ
  let W := Chapter00.compound k V
  have hV₁ : Vᵀ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hW : W ∈ unitaryGroup (Chapter00.IndexSequence k n) ℝ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change Wᵀ * W = 1
    rw [show W = Chapter00.compound k V from rfl, ← Chapter00.compound_transpose,
      ← Chapter00.compound_mul, hV₁, Chapter00.compound_one]
  have hA : A = U * D * Vᵀ := eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  have hU₁ : Uᵀ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hD : Dᵀ * D = diagonal (fun i : Fin n => σ i ^ 2) := by
    rw [← conjTranspose_eq_transpose_of_trivial, conjTranspose_rectDiagonal_mul_self]
    apply congrArg diagonal
    funext j
    by_cases hj : j.val < m
    · simp [hj, pow_two]
    · simp [hj, σ, (A.sortedSingularValues_eq_zero_iff_rank_le j).mpr
        (A.rank_le_height.trans (Nat.le_of_not_gt hj))]
  have hG : Aᵀ * A = V * (Dᵀ * D) * Vᵀ := by
    rw [hA, transpose_mul, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hU₁, Matrix.one_mul]
  apply exists_equiv_colSingularValues_eq_of_conjTranspose_mul_self_eq hW
    (fun s => Finset.prod_nonneg fun _ _ => A.sortedSingularValues_nonneg (s _).val)
  rw [conjTranspose_eq_transpose_of_trivial, show C = Chapter00.compound k A from rfl,
    ← Chapter00.compound_transpose, ← Chapter00.compound_mul, hG, hD,
    Chapter00.compound_mul, Chapter00.compound_mul, Chapter00.compound_transpose,
    Chapter00.compound_diagonal]
  congr 2
  funext s
  simp only [RCLike.ofReal_real_eq_id, id_eq, Finset.prod_pow, σ]

private theorem wedgeCoordinates_smul_each {r n : ℕ} (a : Fin r → ℝ) (v : Fin r → Fin n → ℝ) :
    Chapter00.wedgeCoordinates r (fun j => a j • v j) =
      (∏ j, a j) • Chapter00.wedgeCoordinates r v := by
  simp only [Chapter00.wedgeCoordinates, AlternatingMap.map_smul_univ, map_smul, Finsupp.coe_smul]

private theorem pinv_mulVec_of_positive_singular_pair {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {u : Fin m → ℝ} {v : Fin n → ℝ} {s : ℝ}
    (hs : s ≠ 0) (h : A *ᵥ v = s • u) (h' : Aᵀ *ᵥ u = s • v) :
    A.pinv *ᵥ u = s⁻¹ • v := by
  have hV : (A.pinv * A) *ᵥ v = v := by
    apply (smul_right_injective (Fin n → ℝ) hs)
    have he := congrArg ((A.pinv * A) *ᵥ ·) h'.symm
    rw [mulVec_smul, mulVec_mulVec, ← conjTranspose_eq_transpose_of_trivial,
      A.pinv_mul_self_mul_conjTranspose, conjTranspose_eq_transpose_of_trivial, h'] at he
    exact he
  have hU : u = s⁻¹ • (A *ᵥ v) := by rw [h, inv_smul_smul₀ hs]
  calc
    _ = A.pinv *ᵥ (s⁻¹ • (A *ᵥ v)) := congrArg (A.pinv *ᵥ ·) hU
    _ = _ := by rw [mulVec_smul, mulVec_mulVec, hV]

/-- **Exercise 23**, Equations (42), of [benIsrael2003generalized]. The
top compound and the top compound of the pseudoinverse multiply the paired
singular basis wedges by the volume and its reciprocal. -/
theorem exercise_23 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank ≠ 0)
    (u : Fin A.rank → Fin m → ℝ) (v : Fin A.rank → Fin n → ℝ)
    (hAu : ∀ j, A *ᵥ v j = A.sortedSingularValues j • u j)
    (hAv : ∀ j, Aᵀ *ᵥ u j = A.sortedSingularValues j • v j) :
    Chapter00.compound A.rank A *ᵥ Chapter00.wedgeCoordinates A.rank v =
      Chapter00.matrixVolume A • Chapter00.wedgeCoordinates A.rank u ∧
    Chapter00.compound A.rank A.pinv *ᵥ Chapter00.wedgeCoordinates A.rank u =
      (Chapter00.matrixVolume A)⁻¹ • Chapter00.wedgeCoordinates A.rank v := by
  have hσ (j : Fin A.rank) : A.sortedSingularValues j ≠ 0 := fun h =>
    (not_le_of_gt j.isLt) ((A.sortedSingularValues_eq_zero_iff_rank_le _).mp h)
  constructor
  · rw [Chapter00.compound_mulVec_wedgeCoordinates, exercise_21_real A hA]
    simp_rw [hAu]
    exact wedgeCoordinates_smul_each (fun j => A.sortedSingularValues j) u
  · rw [Chapter00.compound_mulVec_wedgeCoordinates, exercise_21_real A hA, ← Finset.prod_inv_distrib]
    simp_rw [fun j => pinv_mulVec_of_positive_singular_pair A (hσ j) (hAu j) (hAv j)]
    exact wedgeCoordinates_smul_each (fun j => (A.sortedSingularValues j)⁻¹) v

/-- The compound preserves all four Penrose equations, so the Moore–Penrose
inverse commutes with taking compounds. This includes the top compound in
**Exercise 23**. -/
theorem compound_pinv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    Chapter00.compound k A.pinv = (Chapter00.compound k A).pinv := by
  classical
  apply (Chapter00.compound k A).pinv_unique
  · rw [← Chapter00.compound_mul, ← Chapter00.compound_mul, A.mul_pinv_mul_self]
  · rw [← Chapter00.compound_mul, ← Chapter00.compound_mul, A.pinv_mul_self_mul_pinv]
  · change (Chapter00.compound k A * Chapter00.compound k A.pinv)ᴴ = _
    rw [← Chapter00.compound_mul, conjTranspose_eq_transpose_of_trivial,
      ← Chapter00.compound_transpose, ← conjTranspose_eq_transpose_of_trivial,
      A.isHermitian_mul_pinv.eq]
  · change (Chapter00.compound k A.pinv * Chapter00.compound k A)ᴴ = _
    rw [← Chapter00.compound_mul, conjTranspose_eq_transpose_of_trivial,
      ← Chapter00.compound_transpose, ← conjTranspose_eq_transpose_of_trivial,
      A.isHermitian_pinv_mul.eq]

/-- The top compound has rank one and its sole nonzero singular value is
the volume of the original matrix, completing **Exercise 22**. -/
theorem exercise_22_top {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank ≠ 0) :
    let C := Chapter00.compound A.rank A
    C.rank = 1 ∧ ∃ j, C.colSingularValues j = Chapter00.matrixVolume A ∧
      Chapter00.matrixVolume A ≠ 0 ∧ ∀ i ≠ j, C.colSingularValues i = 0 := by
  intro C
  obtain ⟨hR, e, he⟩ := exercise_22 A A.rank
  let s₀ : Chapter00.IndexSequence A.rank n := Fin.castLEOrderEmb A.rank_le_width
  have hp (j : Fin A.rank) : A.sortedSingularValues j ≠ 0 := fun h =>
    (not_le_of_gt j.isLt) ((A.sortedSingularValues_eq_zero_iff_rank_le _).mp h)
  refine ⟨hR.trans (Nat.choose_self _), e s₀, ?_, ?_, ?_⟩
  · rw [he, exercise_21_real A hA]
    rfl
  · rw [exercise_21_real A hA]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hp i
  · intro i hi
    rw [← e.apply_symm_apply i, he]
    have hn : e.symm i ≠ s₀ := fun h => hi ((e.apply_symm_apply i).symm.trans (congrArg e h))
    have hb : ∃ j, A.rank ≤ (e.symm i j).val := by
      by_contra! hj
      let s : Chapter00.IndexSequence A.rank A.rank :=
        OrderEmbedding.ofStrictMono (fun j => ⟨(e.symm i j).val, hj j⟩)
          (fun _ _ h => (e.symm i).strictMono h)
      apply hn
      ext j
      exact congrArg (fun a : Fin A.rank => a.val)
        (DFunLike.congr_fun (Chapter00.indexSequence_self_unique s) j)
    obtain ⟨j, hj⟩ := hb
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      ((A.sortedSingularValues_eq_zero_iff_rank_le _).mpr hj)

/-- The volume of the pseudoinverse of a positive-rank real matrix is the
reciprocal of its volume, as in **Exercise 23**. -/
theorem matrixVolume_pinv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank ≠ 0) :
    Chapter00.matrixVolume A.pinv = (Chapter00.matrixVolume A)⁻¹ := by
  have hR := rank_pinv_eq_rank A
  rw [exercise_21_real A.pinv (hR.symm ▸ hA), exercise_21_real A hA, ← Finset.prod_inv_distrib, hR]
  calc
    _ = ∏ i : Fin A.rank, (A.sortedSingularValues (Fin.rev i))⁻¹ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [exercise_7 A, ite_eq_left i.isLt]
      congr 2
      rw [Fin.val_rev]
      omega
    _ = _ := (Equiv.prod_comp Fin.revPerm (fun i : Fin A.rank => (A.sortedSingularValues i)⁻¹))

end CompoundVolume

end BenIsraelGreville.Chapter06
