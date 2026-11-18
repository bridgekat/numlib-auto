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
* **Exercise 26** (correction). The vector acted on by $A^†$ belongs
  to the codomain of $A$, as in the proof.
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

omit [Fintype m] [Fintype n] [Fintype u] [Fintype v] [DecidableEq m] [DecidableEq n]
  [DecidableEq u] [DecidableEq v] in
private theorem norm_complex_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} (hx : x ≠ 0) : ‖((‖x‖ : ℂ)⁻¹) • x‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

omit [Fintype u] [Fintype v] [DecidableEq u] [DecidableEq v] in
/-- **Exercise 26**, Equations (119)–(121), of [benIsrael2003generalized],
Chapter 5. The minimum expansion on the row-space unit sphere and the
maximum expansion of the Moore–Penrose inverse are attained, with product one. -/
theorem exercise_26 (A : Matrix m n ℂ) (hA : 0 < A.rank) :
    let U := ((toEuclideanLin Aᴴ).range : Set (EuclideanSpace ℂ n)) ∩ Metric.sphere 0 1
    let V := Metric.sphere (0 : EuclideanSpace ℂ m) 1
    ∃ x ∈ U, ∃ y ∈ V,
      IsMinOn (fun x => ‖toEuclideanLin A x‖) U x ∧
      IsMaxOn (fun y => ‖toEuclideanLin A.pinv y‖) V y ∧
      ‖toEuclideanLin A x‖ * ‖toEuclideanLin A.pinv y‖ = 1 := by
  intro U V
  let R := (toEuclideanLin Aᴴ).range
  let F := toEuclideanLin A
  let G := toEuclideanLin A.pinv
  have hR : R ≠ ⊥ := by
    intro he
    have hz : Aᴴ = 0 := toEuclideanLin.injective <| by
      rw [map_zero]
      exact LinearMap.range_eq_bot.mp he
    have hh : Aᴴ.rank = 0 := rank_eq_zero_iff.mpr hz
    rw [rank_conjTranspose] at hh
    exact hA.ne' hh
  obtain ⟨w, hwR, hw⟩ := R.ne_bot_iff.mp hR
  have hUne : U.Nonempty := by
    refine ⟨((‖w‖ : ℂ)⁻¹) • w, R.smul_mem _ hwR, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_complex_normalize hw]
  have hU : IsCompact U := (isCompact_sphere 0 1).inter_left R.closed_of_finiteDimensional
  have hF : Continuous F := F.continuous_of_finiteDimensional
  have hG : Continuous G := G.continuous_of_finiteDimensional
  obtain ⟨x, hx, hxmin⟩ := hU.exists_isMinOn hUne hF.norm.continuousOn
  have hxR : x ∈ R := hx.1
  have hx1 : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx.2
  have hGF {z : EuclideanSpace ℂ n} (hz : z ∈ R) : G (F z) = z := by
    rw [← toEuclideanLin_mul_apply, A.pinv_mul_eq_starProjection]
    exact R.starProjection_eq_self_iff.mpr hz
  have hFx : F x ≠ 0 := by
    intro h
    have he := hGF hxR
    rw [h, map_zero] at he
    rw [← he] at hx1
    simp at hx1
  have hVne : V.Nonempty := by
    refine ⟨((‖F x‖ : ℂ)⁻¹) • F x, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_complex_normalize hFx]
  obtain ⟨y, hy, hymax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ m) 1).exists_isMaxOn
    hVne hG.norm.continuousOn
  have hy1 : ‖y‖ = 1 := by simpa [Metric.mem_sphere] using hy
  have hAmin (z : EuclideanSpace ℂ n) (hzR : z ∈ R) : ‖F x‖ * ‖z‖ ≤ ‖F z‖ := by
    by_cases hz : z = 0
    · simp [hz, F]
    have hmem : ((‖z‖ : ℂ)⁻¹) • z ∈ U := by
      refine ⟨R.smul_mem _ hzR, ?_⟩
      rw [Metric.mem_sphere, dist_zero_right, norm_complex_normalize hz]
    have hle := hxmin hmem
    change ‖F x‖ ≤ ‖F (((‖z‖ : ℂ)⁻¹) • z)‖ at hle
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), mul_comm, ← div_eq_mul_inv] at hle
    exact (le_div_iff₀ (norm_pos_iff.mpr hz)).mp hle
  have hAmax (w : EuclideanSpace ℂ m) : ‖G w‖ ≤ ‖G y‖ * ‖w‖ := by
    by_cases hw : w = 0
    · simp [hw, G]
    have hmem : ((‖w‖ : ℂ)⁻¹) • w ∈ V := by
      rw [Metric.mem_sphere, dist_zero_right, norm_complex_normalize hw]
    have hle := hymax hmem
    change ‖G (((‖w‖ : ℂ)⁻¹) • w)‖ ≤ ‖G y‖ at hle
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), mul_comm, ← div_eq_mul_inv] at hle
    exact (div_le_iff₀ (norm_pos_iff.mpr hw)).mp hle
  have hGy : G y ∈ R := by
    apply R.starProjection_eq_self_iff.mp
    change ((toEuclideanLin Aᴴ).range.starProjection.toLinearMap) (G y) = G y
    rw [← A.pinv_mul_eq_starProjection]
    change toEuclideanLin (A.pinv * A) (toEuclideanLin A.pinv y) = _
    rw [← toEuclideanLin_mul_apply, A.pinv_mul_self_mul_pinv]
  have hFG : ‖F (G y)‖ ≤ 1 := by
    change ‖toEuclideanLin A (toEuclideanLin A.pinv y)‖ ≤ 1
    rw [← toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection, ← hy1]
    exact Submodule.norm_starProjection_apply_le _ _
  have hlo := hAmax (F x)
  rw [hGF hxR, hx1, mul_comm] at hlo
  exact ⟨x, hx, y, hy, hxmin, hymax, le_antisymm ((hAmin _ hGy).trans hFG) hlo⟩

/-- **Exercise 27**, Equations (122)–(124), of [benIsrael2003generalized],
Chapter 5. The lower-right block of the inverse vanishes exactly at the
stated leading-block rank. In that case the other blocks are reflexive
inverses with the indicated ranges and kernels. -/
theorem exercise_27 (B : Matrix m n ℂ) (C : Matrix m u ℂ) (D : Matrix v n ℂ)
    (Y : Matrix (n ⊕ u) (m ⊕ v) ℂ)
    (hMY : fromBlocks B C D (0 : Matrix v u ℂ) * Y = 1)
    (hYM : Y * fromBlocks B C D (0 : Matrix v u ℂ) = 1) :
    let E := Y.toBlocks₁₁
    let F := Y.toBlocks₁₂
    let G := Y.toBlocks₂₁
    let H := Y.toBlocks₂₂
    (H = 0 ↔ B.rank = Fintype.card n - Fintype.card v) ∧
      (H = 0 →
        (B.IsInnerInverse E ∧ B.IsOuterInverse E ∧
          E.mulVecLin.range = D.mulVecLin.ker ∧ E.mulVecLin.ker = C.mulVecLin.range) ∧
        (D.IsInnerInverse F ∧ D.IsOuterInverse F ∧
          F.mulVecLin.range = B.mulVecLin.ker ∧ F.mulVecLin.ker = ⊥) ∧
        (C.IsInnerInverse G ∧ C.IsOuterInverse G ∧
          G.mulVecLin.range = ⊤ ∧ G.mulVecLin.ker = B.mulVecLin.range)) := by
  intro E F G H
  have hY : fromBlocks E F G H = Y := fromBlocks_toBlocks Y
  rw [← hY] at hMY hYM
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    ← fromBlocks_one, fromBlocks_inj] at hMY hYM
  obtain ⟨hBE, hBF, hDE, hDF⟩ := hMY
  obtain ⟨hEB, hEC, hGB, hGC⟩ := hYM
  have hsplit (x : n → ℂ) : E *ᵥ (B *ᵥ x) + F *ᵥ (D *ᵥ x) = x := by
    rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.add_mulVec, hEB, one_mulVec]
  have hsplit' (y : m → ℂ) : B *ᵥ (E *ᵥ y) + C *ᵥ (G *ᵥ y) = y := by
    rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.add_mulVec, hBE, one_mulVec]
  have hDsurj : Function.Surjective D.mulVec := fun y =>
    ⟨F *ᵥ y, by rw [mulVec_mulVec, hDF, one_mulVec]⟩
  have hDsize : Fintype.card v ≤ Fintype.card n := by
    have he := LinearMap.finrank_le_finrank_of_surjective (f := D.mulVecLin) hDsurj
    simpa only [Module.finrank_fintype_fun_eq_card] using he
  let T : B.mulVecLin.ker →ₗ[ℂ] (v → ℂ) := D.mulVecLin.comp B.mulVecLin.ker.subtype
  have hTi : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hBx : B *ᵥ (x : n → ℂ) = 0 := x.prop
    have hDx : D *ᵥ (x : n → ℂ) = 0 := hx
    have he := hsplit (x : n → ℂ)
    rw [hBx, hDx, mulVec_zero, mulVec_zero, zero_add] at he
    exact Subtype.ext he.symm
  have hRankNull := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  change B.rank + Module.finrank ℂ B.mulVecLin.ker = Module.finrank ℂ (n → ℂ) at hRankNull
  rw [Module.finrank_fintype_fun_eq_card] at hRankNull
  constructor
  · constructor
    · intro hH
      have hBF' : B * F = 0 := by simpa only [hH, Matrix.mul_zero, add_zero] using hBF
      have hTs : Function.Surjective T := by
        intro y
        refine ⟨⟨F *ᵥ y, ?_⟩, ?_⟩
        · rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_mulVec, hBF', zero_mulVec]
        · change D *ᵥ (F *ᵥ y) = y
          rw [mulVec_mulVec, hDF, one_mulVec]
      have hdim := LinearMap.finrank_range_of_inj hTi
      rw [LinearMap.range_eq_top.mpr hTs, finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
      omega
    · intro hr
      have hdim : Module.finrank ℂ B.mulVecLin.ker = Module.finrank ℂ (v → ℂ) := by
        rw [Module.finrank_fintype_fun_eq_card]
        omega
      have hTs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hTi
      apply Matrix.mulVec_injective
      funext y
      obtain ⟨x, hx⟩ := hTs y
      have hBx : B *ᵥ (x : n → ℂ) = 0 := x.prop
      change D *ᵥ (x : n → ℂ) = y at hx
      have hHD : H * D = -(G * B) :=
        eq_neg_of_add_eq_zero_left (by rwa [add_comm])
      rw [← hx, mulVec_mulVec, hHD, Matrix.neg_mulVec, ← mulVec_mulVec,
        hBx, mulVec_zero, neg_zero, zero_mulVec]
  · intro hH
    have hBF' : B * F = 0 := by simpa only [hH, Matrix.mul_zero, add_zero] using hBF
    have hGB' : G * B = 0 := by simpa only [hH, Matrix.zero_mul, add_zero] using hGB
    have hbi : B.IsInnerInverse E := by
      rw [isInnerInverse_iff]
      calc
        B * E * B = (B * E + C * G) * B := by
          rw [Matrix.add_mul, Matrix.mul_assoc C G, hGB', Matrix.mul_zero, add_zero]
        _ = B := by rw [hBE, Matrix.one_mul]
    have hbo : B.IsOuterInverse E := by
      rw [isOuterInverse_iff]
      calc
        E * B * E = (E * B + F * D) * E := by
          rw [Matrix.add_mul, Matrix.mul_assoc F D, hDE, Matrix.mul_zero, add_zero]
        _ = E := by rw [hEB, Matrix.one_mul]
    refine ⟨⟨hbi, hbo, ?_, ?_⟩,
      ⟨by rw [isInnerInverse_iff, hDF, Matrix.one_mul],
        by rw [isOuterInverse_iff, Matrix.mul_assoc, hDF, Matrix.mul_one], ?_, ?_⟩,
      ⟨by rw [isInnerInverse_iff, Matrix.mul_assoc, hGC, Matrix.mul_one],
        by rw [isOuterInverse_iff, hGC, Matrix.one_mul], ?_, ?_⟩⟩
    · ext x
      simp only [LinearMap.mem_range, LinearMap.mem_ker, mulVecLin_apply]
      constructor
      · rintro ⟨z, rfl⟩
        rw [mulVec_mulVec, hDE, zero_mulVec]
      · intro hx
        refine ⟨B *ᵥ x, ?_⟩
        simpa only [hx, mulVec_zero, add_zero] using hsplit x
    · ext y
      simp only [LinearMap.mem_range, LinearMap.mem_ker, mulVecLin_apply]
      constructor
      · intro hy
        refine ⟨G *ᵥ y, ?_⟩
        simpa only [hy, mulVec_zero, zero_add] using hsplit' y
      · rintro ⟨z, rfl⟩
        rw [mulVec_mulVec, hEC, zero_mulVec]
    · ext x
      simp only [LinearMap.mem_range, LinearMap.mem_ker, mulVecLin_apply]
      constructor
      · rintro ⟨y, rfl⟩
        rw [mulVec_mulVec, hBF', zero_mulVec]
      · intro hx
        refine ⟨D *ᵥ x, ?_⟩
        simpa only [hx, mulVec_zero, zero_add] using hsplit x
    · rw [Submodule.eq_bot_iff]
      intro y hy
      have h : F *ᵥ y = 0 := hy
      have he := congrArg (fun w => D *ᵥ w) h
      rwa [mulVec_mulVec, hDF, one_mulVec, mulVec_zero] at he
    · apply LinearMap.range_eq_top.mpr
      intro z
      exact ⟨C *ᵥ z, by rw [mulVecLin_apply, mulVec_mulVec, hGC, one_mulVec]⟩
    · ext y
      simp only [LinearMap.mem_range, LinearMap.mem_ker, mulVecLin_apply]
      constructor
      · intro hy
        refine ⟨E *ᵥ y, ?_⟩
        simpa only [hy, mulVec_zero, add_zero] using hsplit' y
      · rintro ⟨x, rfl⟩
        rw [mulVec_mulVec, hGB', zero_mulVec]

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

section BorderedVolumes

variable {a b r : ℕ}

omit [Fintype m] [Fintype n] [Fintype v] [DecidableEq m] [DecidableEq n] [DecidableEq v] in
private theorem gram_add_orthonormal_nullColumns
    (A : Matrix (Fin a) (Fin b) ℝ) (hr : A.rank = r) (hpos : 0 < r)
    (U : Matrix (Fin a) u ℝ) (hu : Fintype.card u = a - r)
    (hAU : Aᵀ * U = 0) (hU : Uᵀ * U = 1) :
    IsUnit (A * Aᵀ + U * Uᵀ) ∧
      (A * Aᵀ + U * Uᵀ).det = Chapter00.matrixVolume A ^ 2 := by
  obtain ⟨F, G, hFG⟩ := (rank_le_iff_exists_mul A r).mp hr.le
  have hF : F.rank = r := le_antisymm (by simpa using F.rank_le_card_width) (by
    simpa only [← hFG, hr] using rank_mul_le_left F G)
  have hG : G.rank = r := le_antisymm (by simpa using G.rank_le_card_height) (by
    simpa only [← hFG, hr] using rank_mul_le_right F G)
  have hUFG : Uᵀ * F * G = 0 := by
    rw [Matrix.mul_assoc, ← hFG]
    simpa only [transpose_mul, transpose_transpose, transpose_zero] using
      congrArg Matrix.transpose hAU
  have hGsurj : Function.Surjective G.mulVec :=
    mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hG)
  have hUF : Uᵀ * F = 0 := by
    apply Matrix.mulVec_injective
    funext x
    obtain ⟨y, rfl⟩ := hGsurj x
    rw [mulVec_mulVec, hUFG, zero_mulVec, zero_mulVec]
  have hFU : Fᵀ * U = 0 := by
    simpa only [transpose_mul, transpose_transpose, transpose_zero] using
      congrArg Matrix.transpose hUF
  have hra : r ≤ a := hr ▸ by simpa using A.rank_le_card_height
  let e : Fin r ⊕ u ≃ Fin a := Fintype.equivOfCardEq (by simp [hu]; omega)
  let J := (fromCols F U).submatrix e id
  let D := fromBlocks (G * Gᵀ) 0 0 (1 : Matrix u u ℝ)
  have hProd : fromCols F U * D * (fromCols F U)ᵀ = A * Aᵀ + U * Uᵀ := by
    rw [transpose_fromCols, fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, fromCols_mul_fromRows,
      ← transpose_mul, Matrix.mul_assoc, hFG]
  have hProd' : J * D * Jᵀ = (A * Aᵀ + U * Uᵀ).submatrix e e := by
    have he₁ : J * D = (fromCols F U * D).submatrix e id := by
      exact submatrix_mul_equiv (fromCols F U) D e (Equiv.refl _) id
    have he₂ : Jᵀ = (fromCols F U)ᵀ.submatrix id e := (transpose_submatrix ..).symm
    rw [he₁, he₂, show
      (fromCols F U * D).submatrix e id * (fromCols F U)ᵀ.submatrix id e =
        (fromCols F U * D * (fromCols F U)ᵀ).submatrix e e from
      submatrix_mul_equiv _ _ e (Equiv.refl _) e, hProd]
  have hJ : J.det ^ 2 = (Fᵀ * F).det :=
    det_sq_orthonormal_completion F U e hFU hU
  have hDet : (A * Aᵀ + U * Uᵀ).det = (Fᵀ * F).det * (G * Gᵀ).det := calc
    _ = ((A * Aᵀ + U * Uᵀ).submatrix e e).det := (det_submatrix_equiv_self e _).symm
    _ = J.det ^ 2 * (G * Gᵀ).det := by
      rw [← hProd', det_mul, det_mul, det_transpose, show D.det = (G * Gᵀ).det by
        simp [D], pow_two]
      ring
    _ = _ := by rw [hJ]
  have hFunit : IsUnit (Fᵀ * F) := isUnit_of_rank_eq_card (by
    simpa [conjTranspose_eq_transpose_of_trivial, hF] using F.rank_conjTranspose_mul_self)
  have hGunit : IsUnit (G * Gᵀ) := isUnit_of_rank_eq_card (by
    rw [← conjTranspose_eq_transpose_of_trivial, G.rank_self_mul_conjTranspose, hG,
      Fintype.card_fin])
  constructor
  · exact (isUnit_iff_isUnit_det _).mpr (hDet ▸
      ((isUnit_iff_isUnit_det _).mp hFunit).mul ((isUnit_iff_isUnit_det _).mp hGunit))
  · have hRank : Chapter00.IsRankFactorization A F G :=
      ⟨hFG, hr.trans (Fintype.card_fin _).symm, hF.trans (Fintype.card_fin _).symm,
        hG.trans (Fintype.card_fin _).symm⟩
    rw [hDet, ← Chapter00.matrixVolume_sq_eq_det_transpose_mul F hF hpos.ne',
      ← Chapter00.matrixVolume_sq_eq_det_mul_transpose G hG hpos.ne',
      Chapter00.matrixVolume_mul_of_rankFactorization hRank, mul_pow]

private theorem realMatrixVolume_transpose (A : Matrix (Fin a) (Fin b) ℝ)
    (hr : A.rank = r) (hpos : 0 < r) :
    Chapter00.matrixVolume Aᵀ = Chapter00.matrixVolume A := by
  have hrt : Aᵀ.rank = r := A.rank_transpose.trans hr
  rw [Chapter00.matrixVolume_eq_sqrt_sum_minors A hr hpos.ne',
    Chapter00.matrixVolume_eq_sqrt_sum_minors Aᵀ hrt hpos.ne', Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  rw [← transpose_submatrix, det_transpose]

omit [Fintype m] [Fintype n] [Fintype u] [Fintype v] [DecidableEq m] [DecidableEq n]
  [DecidableEq u] [DecidableEq v] in
/-- **Exercise 29(a)** of [benIsrael2003generalized], Chapter 5.
Adjoining an orthonormal left null-space basis gives full row rank and
preserves the volume. -/
theorem exercise_29_a (A : Matrix (Fin a) (Fin b) ℝ) (hr : A.rank = r) (hpos : 0 < r)
    (U : Matrix (Fin a) (Fin (a - r)) ℝ) (hAU : Aᵀ * U = 0) (hU : Uᵀ * U = 1) :
    let C := (fromCols A U).submatrix id (finSumFinEquiv.symm : Fin (b + (a - r)) ≃ _)
    C.rank = a ∧ Chapter00.matrixVolume C = Chapter00.matrixVolume A := by
  intro C
  obtain ⟨hunit, hdet⟩ :=
    gram_add_orthonormal_nullColumns A hr hpos U (Fintype.card_fin _) hAU hU
  have hGram : C * Cᵀ = A * Aᵀ + U * Uᵀ := by
    dsimp only [C]
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_id_id, transpose_fromCols,
      fromCols_mul_fromRows]
  have hRank : C.rank = a := by
    rw [← C.rank_self_mul_conjTranspose, conjTranspose_eq_transpose_of_trivial, hGram,
      rank_of_isUnit _ hunit, Fintype.card_fin]
  have ha : a ≠ 0 := (hpos.trans_le (hr ▸ by simpa using A.rank_le_card_height)).ne'
  have hsq : Chapter00.matrixVolume C ^ 2 = Chapter00.matrixVolume A ^ 2 := by
    rw [Chapter00.matrixVolume_sq_eq_det_mul_transpose C hRank ha, hGram, hdet]
  have hVC : 0 ≤ Chapter00.matrixVolume C := by
    rw [Chapter00.matrixVolume_eq_sqrt_sum_minors C hRank ha]
    positivity
  have hVA : 0 ≤ Chapter00.matrixVolume A := by
    rw [Chapter00.matrixVolume_eq_sqrt_sum_minors A hr hpos.ne']
    positivity
  exact ⟨hRank, (sq_eq_sq₀ hVC hVA).mp hsq⟩

omit [Fintype m] [Fintype n] [Fintype u] [Fintype v] [DecidableEq m] [DecidableEq n]
  [DecidableEq u] [DecidableEq v] in
/-- **Exercise 29(b)** of [benIsrael2003generalized], Chapter 5.
Appending the transposes of orthonormal right null-space basis vectors
gives full column rank and preserves the volume. -/
theorem exercise_29_b (A : Matrix (Fin a) (Fin b) ℝ) (hr : A.rank = r) (hpos : 0 < r)
    (V : Matrix (Fin b) (Fin (b - r)) ℝ) (hAV : A * V = 0) (hV : Vᵀ * V = 1) :
    let C := (fromRows A Vᵀ).submatrix (finSumFinEquiv.symm : Fin (a + (b - r)) ≃ _) id
    C.rank = b ∧ Chapter00.matrixVolume C = Chapter00.matrixVolume A := by
  intro C
  have hrt : Aᵀ.rank = r := A.rank_transpose.trans hr
  have hV' : Aᵀᵀ * V = 0 := by rwa [transpose_transpose]
  obtain ⟨hRank, hVolume⟩ := exercise_29_a Aᵀ hrt hpos V hV' hV
  change ((fromCols Aᵀ V).submatrix id finSumFinEquiv.symm).rank = b at hRank
  have hC : Cᵀ = (fromCols Aᵀ V).submatrix id finSumFinEquiv.symm := by
    dsimp only [C]
    rw [transpose_submatrix, transpose_fromRows, transpose_transpose]
  have hCR : C.rank = b := by rwa [← C.rank_transpose, hC]
  rw [← hC] at hVolume
  have hb : 0 < b := hpos.trans_le (hr ▸ by simpa using A.rank_le_card_width)
  exact ⟨hCR, (realMatrixVolume_transpose C hCR hb).symm.trans
    (hVolume.trans (realMatrixVolume_transpose A hr hpos))⟩

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- **Exercise 30(a)**, Equations (127)–(130) of [benIsrael2003generalized],
Chapter 5. All three determinant formulas give the squared volume.
The equivalence identifies the equally sized row and column index sets
of the bordered matrix. -/
theorem exercise_30_a (A : Matrix (Fin a) (Fin b) ℝ) (hr : A.rank = r) (hpos : 0 < r)
    (U : Matrix (Fin a) u ℝ) (V : Matrix (Fin b) v ℝ)
    (hu : Fintype.card u = a - r) (hv : Fintype.card v = b - r)
    (hAU : Aᵀ * U = 0) (hAV : A * V = 0) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (e : (Fin a ⊕ v) ≃ (Fin b ⊕ u)) :
    let B := (fromBlocks A U Vᵀ (0 : Matrix v u ℝ)).submatrix id e
    Chapter00.matrixVolume A ^ 2 = B.det ^ 2 ∧
      Chapter00.matrixVolume A ^ 2 = (A * Aᵀ + U * Uᵀ).det ∧
      Chapter00.matrixVolume A ^ 2 = (Aᵀ * A + V * Vᵀ).det := by
  intro B
  have hUdet := (gram_add_orthonormal_nullColumns A hr hpos U hu hAU hU).2
  have hVdet := (gram_add_orthonormal_nullColumns Aᵀ (A.rank_transpose.trans hr) hpos V hv
    (by simpa only [transpose_transpose] using hAV) hV).2
  rw [transpose_transpose, realMatrixVolume_transpose A hr hpos] at hVdet
  have hVA : Vᵀ * Aᵀ = 0 := by
    simpa only [transpose_mul, transpose_zero] using congrArg Matrix.transpose hAV
  have hGram : B * Bᵀ = fromBlocks (A * Aᵀ + U * Uᵀ) 0 0 (1 : Matrix v v ℝ) := by
    dsimp only [B]
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_id_id, fromBlocks_transpose]
    simp [fromBlocks_multiply, hAV, hVA, hV]
  refine ⟨?_, hUdet.symm, hVdet.symm⟩
  have hb : (B * Bᵀ).det = B.det ^ 2 := by rw [det_mul, det_transpose, pow_two]
  rw [← hb, hGram, det_fromBlocks_zero₂₁, det_one, mul_one, hUdet]

omit [Fintype m] [Fintype n] [Fintype v] [DecidableEq m] [DecidableEq n] [DecidableEq v] in
/-- **Exercise 30(b)**, Equation (131) of [benIsrael2003generalized],
Chapter 5. The null-space correction of a square matrix gives a
determinant whose square equals the squared volume. -/
theorem exercise_30_b (A : Matrix (Fin a) (Fin a) ℝ) (hr : A.rank = r) (hpos : 0 < r)
    (U V : Matrix (Fin a) u ℝ) (hu : Fintype.card u = a - r)
    (hAU : Aᵀ * U = 0) (hAV : A * V = 0) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    Chapter00.matrixVolume A ^ 2 = (A + U * Vᵀ).det ^ 2 := by
  have hVA : Vᵀ * Aᵀ = 0 := by
    simpa only [transpose_mul, transpose_zero] using congrArg Matrix.transpose hAV
  have hVV : U * Vᵀ * (V * Uᵀ) = U * Uᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V Uᵀ, hV, Matrix.one_mul]
  have hB : (A + U * Vᵀ) * (A + U * Vᵀ)ᵀ = A * Aᵀ + U * Uᵀ := by
    rw [transpose_add, transpose_mul, transpose_transpose, Matrix.mul_add, Matrix.add_mul,
      Matrix.add_mul, ← Matrix.mul_assoc A V Uᵀ, Matrix.mul_assoc U Vᵀ Aᵀ,
      hAV, hVA, hVV]
    simp
  have hb : ((A + U * Vᵀ) * (A + U * Vᵀ)ᵀ).det = (A + U * Vᵀ).det ^ 2 := by
    rw [det_mul, det_transpose, pow_two]
  rw [← hb, hB, (gram_add_orthonormal_nullColumns A hr hpos U hu hAU hU).2]

end BorderedVolumes

end BenIsraelGreville.Chapter05
