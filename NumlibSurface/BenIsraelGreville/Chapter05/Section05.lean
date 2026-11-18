/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.SaddlePoint.NullSpaceReduction
import NumlibSurface.BenIsraelGreville.Chapter01.Section03
import NumlibSurface.BenIsraelGreville.Chapter02.Section07
import NumlibSurface.BenIsraelGreville.Chapter03.Section02
import NumlibSurface.BenIsraelGreville.Chapter00.Section05

/-!
# Generalized inverses from bordered matrices

Section 5.5 of [benIsrael2003generalized] adds bases for the two null
spaces to a rectangular matrix. The bordered system is nonsingular and
contains the Moore–Penrose inverse as a block of its ordinary inverse.

## Deviations from the source

* **Theorem 7(b)** (typo). The columns of $V$ form the basis of the kernel of $A$.
* **Corollary 5** (typo). The right-hand side is indexed by the rows of $A$.
-/

namespace BenIsraelGreville.Chapter05

open Matrix Chapter02
open scoped ComplexOrder

variable {m n u v : Type*} [Fintype m] [Fintype n] [Fintype u] [Fintype v]
  [DecidableEq m] [DecidableEq n] [DecidableEq u] [DecidableEq v]

private theorem pinv_mul_eq_zero_of_conjTranspose_mul_eq_zero
    {a b c : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (A : Matrix a b ℂ) (F : Matrix a c ℂ)
    (h : Aᴴ * F = 0) : A.pinv * F = 0 := by
  classical
  calc
    A.pinv * F = A.pinv * (A * A.pinv) * F := by
      rw [← Matrix.mul_assoc A.pinv A, A.pinv_mul_self_mul_pinv]
    _ = A.pinv * (A * A.pinv)ᴴ * F := by rw [A.isHermitian_mul_pinv.eq]
    _ = A.pinv * (A.pinvᴴ * (Aᴴ * F)) := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.mul_zero]

private theorem range_toEuclideanLin_eq_ker_of_isNullBasis
    {a b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    {A : Matrix a b ℂ} {U : Matrix b c ℂ} (hU : IsNullBasis A U) :
    (toEuclideanLin U).range = (toEuclideanLin A).ker := by
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    rw [← toEuclideanLin_mul_apply, hU.mul_eq_zero, map_zero, LinearMap.zero_apply]
  · intro hx
    have h : WithLp.ofLp x ∈ A.mulVecLin.ker := by
      rw [LinearMap.mem_ker, mulVecLin_apply, ← ofLp_toEuclideanLin, hx, WithLp.ofLp_zero]
    rw [← hU.range_eq_ker] at h
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp h
    exact ⟨WithLp.toLp 2 y, WithLp.ofLp_injective 2 hy⟩

private theorem mul_pinv_eq_projector_ker_of_isNullBasis
    {a b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    {A : Matrix a b ℂ} {U : Matrix b c ℂ} (hU : IsNullBasis A U) :
    U * U.pinv = orthogonalProjector (toEuclideanLin A).ker := by
  apply toEuclideanLin.injective
  rw [U.mul_pinv_eq_starProjection, toEuclideanLin_orthogonalProjector]
  exact congrArg (fun L : Submodule ℂ (EuclideanSpace ℂ b) =>
    L.starProjection.toLinearMap) (range_toEuclideanLin_eq_ker_of_isNullBasis hU)

private theorem bordered_projector_add (A : Matrix m n ℂ) (U : Matrix m u ℂ)
    (hU : IsNullBasis Aᴴ U) : A * A.pinv + U * U.pinv = 1 := by
  have hA : A * A.pinv = orthogonalProjector (toEuclideanLin A).range := by
    apply toEuclideanLin.injective
    rw [A.mul_pinv_eq_starProjection, toEuclideanLin_orthogonalProjector]
  have hKer : (toEuclideanLin Aᴴ).ker = (toEuclideanLin A).rangeᗮ := by
    rw [toEuclideanLin_conjTranspose_eq_adjoint, ← LinearMap.orthogonal_range]
  rw [hA, mul_pinv_eq_projector_ker_of_isNullBasis hU, hKer, Chapter02.exercise_56]
  abel

/-- **Theorem 7** of [benIsrael2003generalized], Chapter 5, Equations
(108)–(109). Bases of the kernel and adjoint kernel give a two-sided inverse
for the bordered matrix. The two index types may be presented separately. -/
theorem theorem_5_7 (A : Matrix m n ℂ) (U : Matrix m u ℂ) (V : Matrix n v ℂ)
    (hU : IsNullBasis Aᴴ U) (hV : IsNullBasis A V) :
    let B := fromBlocks A U Vᴴ (0 : Matrix v u ℂ)
    let X := fromBlocks A.pinv Vᴴ.pinv U.pinv (0 : Matrix u v ℂ)
    B * X = 1 ∧ X * B = 1 := by
  have hUU : U.pinv * U = 1 := by
    apply (Chapter01.lemma_2_a (Chapter01.mem_one_iff.mpr U.mul_pinv_mul_self)).mpr
    exact mulVec_injective_iff_rank_eq_card.mp hU.injective
  have hVV : Vᴴ * Vᴴ.pinv = 1 := by
    apply (Chapter01.lemma_2_b (Chapter01.mem_one_iff.mpr Vᴴ.mul_pinv_mul_self)).mpr
    rw [rank_conjTranspose]
    exact mulVec_injective_iff_rank_eq_card.mp hV.injective
  have hUV : A.pinv * U = 0 :=
    pinv_mul_eq_zero_of_conjTranspose_mul_eq_zero A U hU.mul_eq_zero
  have hUA : U.pinv * A = 0 := by
    apply pinv_mul_eq_zero_of_conjTranspose_mul_eq_zero U A
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg Matrix.conjTranspose hU.mul_eq_zero
  have hVA : Vᴴ * A.pinv = 0 := by
    have h : Aᴴ.pinv * V = 0 :=
      pinv_mul_eq_zero_of_conjTranspose_mul_eq_zero Aᴴ V (by simpa using hV.mul_eq_zero)
    simpa only [conjTranspose_mul, ← pinv_conjTranspose, conjTranspose_conjTranspose,
      conjTranspose_zero] using congrArg Matrix.conjTranspose h
  have hAV : A * Vᴴ.pinv = 0 := by
    have hv : V * V.pinv * Vᴴ.pinv = Vᴴ.pinv := by
      rw [pinv_conjTranspose, ← V.isHermitian_mul_pinv.eq, ← conjTranspose_mul,
        ← Matrix.mul_assoc, V.pinv_mul_self_mul_pinv]
    calc
      A * Vᴴ.pinv = A * (V * V.pinv * Vᴴ.pinv) := by rw [hv]
      _ = 0 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV.mul_eq_zero,
          Matrix.zero_mul, Matrix.zero_mul]
  have hVproj : Vᴴ.pinv * Vᴴ = V * V.pinv := by
    rw [pinv_conjTranspose, ← conjTranspose_mul, V.isHermitian_mul_pinv.eq]
  have hAproj : A.pinv * A + Vᴴ.pinv * Vᴴ = 1 := by
    rw [hVproj]
    have h : IsNullBasis Aᴴᴴ V := by simpa using hV
    simpa only [pinv_conjTranspose, ← conjTranspose_mul, A.isHermitian_pinv_mul.eq] using
      bordered_projector_add Aᴴ V h
  dsimp only
  constructor
  · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      bordered_projector_add A U hU, hAV, hVA, hVV, fromBlocks_one]
  · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      hAproj, hUV, hUA, hUU, fromBlocks_one]

omit [DecidableEq m] [DecidableEq n] [DecidableEq u] [DecidableEq v] in
/-- The bordered matrix has the same number of rows and columns. -/
theorem card_bordered (A : Matrix m n ℂ) (U : Matrix m u ℂ) (V : Matrix n v ℂ)
    (hU : IsNullBasis Aᴴ U) (hV : IsNullBasis A V) :
    Fintype.card (m ⊕ v) = Fintype.card (n ⊕ u) := by
  classical
  let B := fromBlocks A U Vᴴ (0 : Matrix v u ℂ)
  let X := fromBlocks A.pinv Vᴴ.pinv U.pinv (0 : Matrix u v ℂ)
  obtain ⟨hL, hR⟩ := theorem_5_7 A U V hU hV
  change B * X = 1 at hL
  change X * B = 1 at hR
  apply le_antisymm
  · have h := (rank_mul_le_left B X).trans B.rank_le_card_width
    rw [hL, rank_one] at h
    exact h
  · have h := (rank_mul_le_left X B).trans X.rank_le_card_width
    rw [hR, rank_one] at h
    exact h

/-- **Theorem 7** of [benIsrael2003generalized], Chapter 5. After identifying
the row and column index types, the bordered matrix is nonsingular with
ordinary inverse given by Equation (109). -/
theorem bordered_isUnit_inv (A : Matrix m n ℂ) (U : Matrix m u ℂ) (V : Matrix n v ℂ)
    (hU : IsNullBasis Aᴴ U) (hV : IsNullBasis A V) (e : n ⊕ u ≃ m ⊕ v) :
    let B := (fromBlocks A U Vᴴ (0 : Matrix v u ℂ)).submatrix id e.symm
    let X := (fromBlocks A.pinv Vᴴ.pinv U.pinv (0 : Matrix u v ℂ)).submatrix e.symm id
    IsUnit B ∧ B⁻¹ = X := by
  dsimp only
  have hp :
      (fromBlocks A U Vᴴ (0 : Matrix v u ℂ)).submatrix id e.symm *
        (fromBlocks A.pinv Vᴴ.pinv U.pinv (0 : Matrix u v ℂ)).submatrix e.symm id = 1 := by
    rw [submatrix_mul_equiv, (theorem_5_7 A U V hU hV).1, submatrix_id_id]
  exact ⟨isUnit_iff_exists_inv.mpr ⟨_, hp⟩, inv_eq_right_inv hp⟩

omit [DecidableEq v] in
/-- **Corollary 5** of [benIsrael2003generalized], Chapter 5, Equation (115).
The solution of the bordered system gives the minimum-norm least-squares
solution in its first block and the residual in the image of its second block. -/
theorem corollary_5_5 (A : Matrix m n ℂ) (U : Matrix m u ℂ) (V : Matrix n v ℂ)
    (hU : IsNullBasis Aᴴ U) (hV : IsNullBasis A V) (b : m → ℂ) :
    let B := fromBlocks A U Vᴴ (0 : Matrix v u ℂ)
    let d := Sum.elim b (0 : v → ℂ)
    (∀ (x : n → ℂ) (y : u → ℂ), B *ᵥ Sum.elim x y = d ↔
      x = A.pinv *ᵥ b ∧ y = U.pinv *ᵥ b) ∧
      U *ᵥ (U.pinv *ᵥ b) = orthogonalProjector ((toEuclideanLin Aᴴ).ker) *ᵥ b ∧
      A.IsMinNormLeastSquaresSolution (WithLp.toLp 2 b) (WithLp.toLp 2 (A.pinv *ᵥ b)) := by
  classical
  let B := fromBlocks A U Vᴴ (0 : Matrix v u ℂ)
  let X := fromBlocks A.pinv Vᴴ.pinv U.pinv (0 : Matrix u v ℂ)
  let d := Sum.elim b (0 : v → ℂ)
  obtain ⟨hBX, hXB⟩ := theorem_5_7 A U V hU hV
  change B * X = 1 at hBX
  change X * B = 1 at hXB
  have hX : X *ᵥ d = Sum.elim (A.pinv *ᵥ b) (U.pinv *ᵥ b) := by
    simp [X, d, fromBlocks_mulVec]
  refine ⟨fun x y => ?_, ?_, A.isMinNormLeastSquaresSolution_pinv (WithLp.toLp 2 b)⟩
  · change B *ᵥ Sum.elim x y = d ↔ x = A.pinv *ᵥ b ∧ y = U.pinv *ᵥ b
    constructor
    · intro h
      have hw : Sum.elim x y = X *ᵥ d := by
        rw [← h, mulVec_mulVec, hXB, one_mulVec]
      rwa [hX, Sum.elim_eq_iff] at hw
    · rintro ⟨rfl, rfl⟩
      rw [← hX, mulVec_mulVec, hBX, one_mulVec]
  · rw [mulVec_mulVec, mul_pinv_eq_projector_ker_of_isNullBasis hU]

omit [DecidableEq u] in
/-- **Corollary 6** of [benIsrael2003generalized], Chapter 5, Equation (116).
Cramer's rule gives the coordinates of the least-squares solution from
determinants of the bordered matrix. -/
theorem corollary_5_6 (A : Matrix m n ℂ) (U : Matrix m u ℂ) (V : Matrix n v ℂ)
    (hU : IsNullBasis Aᴴ U) (hV : IsNullBasis A V) (b : m → ℂ)
    (e : n ⊕ u ≃ m ⊕ v) (j : n) :
    let B := (fromBlocks A U Vᴴ (0 : Matrix v u ℂ)).submatrix id e.symm
    (A.pinv *ᵥ b) j = (B.updateCol (e (Sum.inl j)) (Sum.elim b 0)).det / B.det := by
  classical
  let C := fromBlocks A U Vᴴ (0 : Matrix v u ℂ)
  let B := C.submatrix id e.symm
  let w := Sum.elim (A.pinv *ᵥ b) (U.pinv *ᵥ b)
  have hw : C *ᵥ w = Sum.elim b 0 :=
    ((corollary_5_5 A U V hU hV b).1 _ _).mpr ⟨rfl, rfl⟩
  have hB : IsUnit B := (bordered_isUnit_inv A U V hU hV e).1
  have hy : B *ᵥ (w ∘ e.symm) = Sum.elim b 0 := by
    change C.submatrix id e.symm *ᵥ (w ∘ e.symm) = _
    have he : (w ∘ e.symm) ∘ e.symm.symm = w := by
      funext i
      exact congrArg w (Equiv.symm_apply_apply e i)
    rw [submatrix_mulVec_equiv, he, Function.comp_id, hw]
  simpa only [w, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using
    Chapter00.cramer_rule hB hy (e (Sum.inl j))

private theorem isNullBasis_of_orthonormal_columns
    {a b c : Type*} [Fintype b] [Fintype c] [DecidableEq c]
    (A : Matrix a b ℂ) (U : Matrix b c ℂ) (h0 : A * U = 0) (hU : Uᴴ * U = 1)
    (hc : Fintype.card c = Module.finrank ℂ A.mulVecLin.ker) :
    IsNullBasis A U := by
  have hInj : Function.Injective U.mulVec := by
    intro x y h
    have h' := congrArg (Uᴴ.mulVec) h
    simpa only [mulVec_mulVec, hU, one_mulVec] using h'
  refine ⟨hInj, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, h0, zero_mulVec]
  · have hLi : Function.Injective U.mulVecLin := hInj
    rw [LinearMap.finrank_range_of_inj hLi, Module.finrank_fintype_fun_eq_card, hc]

private theorem pinv_eq_conjTranspose_of_orthonormal_columns
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (U : Matrix a b ℂ) (hU : Uᴴ * U = 1) : U.pinv = Uᴴ := by
  refine (U.pinv_unique ?_ ?_ ?_ ?_).symm
  · rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  · rw [hU, Matrix.one_mul]
  · exact isHermitian_mul_conjTranspose_self U
  · rw [hU]
    exact isHermitian_one

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 5, Equations
(117)–(118). Orthonormal null-space bases simplify the two off-diagonal
blocks in the inverse. -/
theorem exercise_25 (A : Matrix m n ℂ) (U : Matrix m u ℂ) (V : Matrix n v ℂ)
    (hu : Fintype.card u = Fintype.card m - A.rank)
    (hv : Fintype.card v = Fintype.card n - A.rank)
    (hAU : Aᴴ * U = 0) (hAV : A * V = 0) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    let B := fromBlocks A U Vᴴ (0 : Matrix v u ℂ)
    let X := fromBlocks A.pinv V Uᴴ (0 : Matrix u v ℂ)
    B * X = 1 ∧ X * B = 1 := by
  have hrU := LinearMap.finrank_range_add_finrank_ker Aᴴ.mulVecLin
  have hrV := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [← Matrix.rank, rank_conjTranspose, Module.finrank_fintype_fun_eq_card] at hrU
  rw [← Matrix.rank, Module.finrank_fintype_fun_eq_card] at hrV
  have hUb := isNullBasis_of_orthonormal_columns Aᴴ U hAU hU (by omega)
  have hVb := isNullBasis_of_orthonormal_columns A V hAV hV (by omega)
  have hUp := pinv_eq_conjTranspose_of_orthonormal_columns U hU
  have hVp : Vᴴ.pinv = V := by
    rw [pinv_conjTranspose, pinv_eq_conjTranspose_of_orthonormal_columns V hV,
      conjTranspose_conjTranspose]
  simpa only [hUp, hVp] using theorem_5_7 A U V hUb hVb

private theorem det_sq_orthonormal_completion {a b c : Type*}
    [Fintype a] [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    (C : Matrix a b ℝ) (U : Matrix a c ℝ) (e : b ⊕ c ≃ a)
    (hCU : Cᵀ * U = 0) (hU : Uᵀ * U = 1) :
    ((fromCols C U).submatrix e id).det ^ 2 = (Cᵀ * C).det := by
  let B := (fromCols C U).submatrix e id
  have hUC : Uᵀ * C = 0 := by
    simpa only [transpose_mul, transpose_transpose, transpose_zero] using
      congrArg Matrix.transpose hCU
  have hB : Bᵀ * B = fromBlocks (Cᵀ * C) 0 0 (1 : Matrix c c ℝ) := by
    dsimp only [B]
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_id_id, transpose_fromCols,
      fromRows_mul_fromCols, hCU, hUC, hU]
  calc
    B.det ^ 2 = (Bᵀ * B).det := by rw [det_mul, det_transpose, pow_two]
    _ = (Cᵀ * C).det := by rw [hB, det_fromBlocks_zero₂₁, det_one, mul_one]

/-- **Exercise 28(a)** of [benIsrael2003generalized], Chapter 5, Equation
(125). Completing a full-column-rank real matrix by orthonormal columns in
its orthogonal complement gives a squared determinant equal to its squared volume. -/
theorem exercise_28_a {a r : ℕ} (C : Matrix (Fin a) (Fin r) ℝ) (U : Matrix (Fin a) u ℝ)
    (e : Fin r ⊕ u ≃ Fin a) (hr : C.rank = r) (h0 : r ≠ 0)
    (hCU : Cᵀ * U = 0) (hU : Uᵀ * U = 1) :
    ((fromCols C U).submatrix e id).det ^ 2 = Chapter00.matrixVolume C ^ 2 := by
  classical
  rw [det_sq_orthonormal_completion C U e hCU hU,
    Chapter00.matrixVolume_sq_eq_det_transpose_mul C hr h0]

/-- **Exercise 28(b)** of [benIsrael2003generalized], Chapter 5, Equation
(126). The row completion of a full-row-rank matrix by orthonormal rows
has squared determinant equal to its squared volume. -/
theorem exercise_28_b {a r : ℕ} (R : Matrix (Fin r) (Fin a) ℝ) (V : Matrix (Fin a) v ℝ)
    (e : Fin r ⊕ v ≃ Fin a) (hr : R.rank = r) (h0 : r ≠ 0)
    (hRV : R * V = 0) (hV : Vᵀ * V = 1) :
    ((fromRows R Vᵀ).submatrix id e).det ^ 2 = Chapter00.matrixVolume R ^ 2 := by
  classical
  calc
    ((fromRows R Vᵀ).submatrix id e).det ^ 2 =
        ((fromCols Rᵀ V).submatrix e id).det ^ 2 := by
      rw [← det_transpose ((fromRows R Vᵀ).submatrix id e), transpose_submatrix,
        transpose_fromRows, transpose_transpose]
    _ = (R * Rᵀ).det := by
      rw [det_sq_orthonormal_completion Rᵀ V e (by simpa using hRV) hV,
        transpose_transpose]
    _ = Chapter00.matrixVolume R ^ 2 :=
      (Chapter00.matrixVolume_sq_eq_det_mul_transpose R hr h0).symm

end BenIsraelGreville.Chapter05
