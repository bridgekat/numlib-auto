/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter06.Section02
import NumlibSurface.BenIsraelGreville.Chapter02.Section07
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import Numlib.LinearAlgebra.Matrix.OrthogonalTrace
import Numlib.LinearAlgebra.Matrix.Polar
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# Partial isometries and polar decomposition

Section 6.4 of [benIsrael2003generalized] characterizes partial isometries
and uses them to give canonical polar factors for rectangular matrices.

## Deviations from the source

* **Corollary 2** (scope). The normal factors are specified for a fixed
  $UDV^H$ factorization. The range constraints permit changes of phase.
* **Exercise 38** (correction). Mazur–Ulam requires a surjective isometry
  between general real normed spaces. The map $x \mapsto (x,|x|)$ into
  the product with supremum norm illustrates the need for this hypothesis.
-/

namespace BenIsraelGreville.Chapter06

open Matrix Chapter02
open scoped InnerProductSpace ComplexOrder

section PartialIsometries

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Equation (72)** of [benIsrael2003generalized], Chapter 6.
A partial isometry preserves the Euclidean norm on its initial space,
the orthogonal complement of its kernel. -/
def IsPartialIsometry (U : Matrix m n ℂ) : Prop :=
  ∀ x ∈ (toEuclideanLin U).kerᗮ, ‖toEuclideanLin U x‖ = ‖x‖

omit [DecidableEq m] in
/-- **Equation (72)**, distance form, of [benIsrael2003generalized],
Chapter 6. The restriction to the initial space is an isometry. -/
theorem isPartialIsometry_iff_dist (U : Matrix m n ℂ) :
    IsPartialIsometry U ↔
      ∀ x ∈ (toEuclideanLin U).kerᗮ, ∀ y ∈ (toEuclideanLin U).kerᗮ,
        dist (toEuclideanLin U x) (toEuclideanLin U y) = dist x y := by
  constructor
  · intro h x hx y hy
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact h _ (Submodule.sub_mem _ hx hy)
  · intro h x hx
    simpa only [map_zero, dist_zero_right] using h x hx 0 (Submodule.zero_mem _)

/-- **Equation (73)** of [benIsrael2003generalized], Chapter 6.
The adjoint Gram product of a partial isometry is the orthogonal projector
onto the range of its adjoint, and this condition is sufficient. -/
theorem isPartialIsometry_iff_initial_gram (U : Matrix m n ℂ) :
    IsPartialIsometry U ↔
      Uᴴ * U = orthogonalProjector (LinearMap.range (toEuclideanLin Uᴴ)) := by
  let T := toEuclideanLin U
  let K := T.kerᗮ
  let P : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := K.starProjection
  have hK : K = (toEuclideanLin Uᴴ).range := by
    rw [toEuclideanLin_conjTranspose_eq_adjoint]
    exact T.orthogonal_ker
  rw [← hK, ← toEuclideanLin.injective.eq_iff, toEuclideanLin_mul,
    toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin_orthogonalProjector]
  change IsPartialIsometry U ↔ T.adjoint ∘ₗ T = P
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply (inner_map_self_eq_zero _).mp
    intro x
    have hk : x - P x ∈ T.ker := by
      simpa only [P, K, ContinuousLinearMap.coe_coe, Submodule.orthogonal_orthogonal] using
        K.sub_starProjection_mem_orthogonal x
    have hTx := LinearMap.mem_ker.mp hk
    rw [map_sub, sub_eq_zero] at hTx
    have hPx : P x ∈ K := K.starProjection_apply_mem x
    have hNorm : ‖T (P x)‖ = ‖P x‖ := h _ hPx
    have ho : inner ℂ x (P x) = inner ℂ (P x) (P x) := by
      have he := K.starProjection_inner_eq_zero x (P x) hPx
      rwa [inner_sub_left, sub_eq_zero] at he
    have hi : inner ℂ (P x) x = inner ℂ (P x) (P x) := by
      simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) ho
    rw [LinearMap.sub_apply, inner_sub_left, LinearMap.comp_apply,
      LinearMap.adjoint_inner_left, hTx, hi, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hNorm, sub_self]
  · intro h x hx
    have hPx : P x = x := K.starProjection_eq_self_iff.mpr hx
    have he := LinearMap.congr_fun h x
    change T.adjoint (T x) = P x at he
    rw [hPx] at he
    have hi := LinearMap.adjoint_inner_left T x (T x)
    rw [he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
    have hs : ‖x‖ ^ 2 = ‖T x‖ ^ 2 := by exact_mod_cast hi
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs.symm

omit [DecidableEq m] in
private theorem adjoint_eq_pinv_of_mul_adjoint_mul (U : Matrix m n ℂ)
    (h : U * Uᴴ * U = U) : Uᴴ = U.pinv := by
  have h' := congrArg Matrix.conjTranspose h
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc] at h'
  exact U.pinv_unique h h' (isHermitian_mul_conjTranspose_self U)
    (isHermitian_conjTranspose_mul_self U)

omit [DecidableEq m] in
/-- **Theorem 5(a,c,d)** of [benIsrael2003generalized], Chapter 6.
A partial isometry satisfies the adjoint reflexivity identity and its
adjoint is its Moore–Penrose inverse. -/
theorem isPartialIsometry_iff_adjoint_eq_pinv (U : Matrix m n ℂ) :
    IsPartialIsometry U ↔ Uᴴ = U.pinv := by
  classical
  have hP : U.pinv * U = orthogonalProjector (LinearMap.range (toEuclideanLin Uᴴ)) := by
    apply toEuclideanLin.injective
    rw [U.pinv_mul_eq_starProjection, toEuclideanLin_orthogonalProjector]
  rw [isPartialIsometry_iff_initial_gram, ← hP]
  refine ⟨fun h => adjoint_eq_pinv_of_mul_adjoint_mul U ?_, fun h => by rw [h]⟩
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, mul_pinv_mul_self]

omit [DecidableEq m] in
private theorem isPartialIsometry_iff_reflexive (U : Matrix m n ℂ) :
    IsPartialIsometry U ↔ U * Uᴴ * U = U :=
  (isPartialIsometry_iff_adjoint_eq_pinv U).trans
    ⟨fun h => h ▸ U.mul_pinv_mul_self, adjoint_eq_pinv_of_mul_adjoint_mul U⟩

omit [DecidableEq m] in
private theorem isPartialIsometry_iff_gram_idempotent (U : Matrix m n ℂ) :
    IsPartialIsometry U ↔ (Uᴴ * U).IsHermitian ∧ IsIdempotentElem (Uᴴ * U) := by
  classical
  refine ⟨fun h => ⟨isHermitian_conjTranspose_mul_self U, ?_⟩, fun ⟨_, h⟩ => ?_⟩
  · rw [(isPartialIsometry_iff_initial_gram U).mp h]
    exact isIdempotentElem_orthogonalProjector _
  · rw [isPartialIsometry_iff_reflexive]
    have h0 : Uᴴ * U * (Uᴴ * U - 1) = 0 := by
      rw [mul_sub, mul_one, h.eq, sub_self]
    have he := mul_eq_zero_of_conjTranspose_mul_self_mul_eq_zero U h0
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, ← Matrix.mul_assoc] at he

/-- **Theorem 5** of [benIsrael2003generalized], Chapter 6. The seven
other characterizations of a partial isometry are equivalent to norm
preservation on the initial space. -/
theorem theorem_6_5 (U : Matrix m n ℂ) :
    (IsPartialIsometry U ↔ IsPartialIsometry Uᴴ) ∧
    (IsPartialIsometry U ↔ (Uᴴ * U).IsHermitian ∧ IsIdempotentElem (Uᴴ * U)) ∧
    (IsPartialIsometry U ↔ (U * Uᴴ).IsHermitian ∧ IsIdempotentElem (U * Uᴴ)) ∧
    (IsPartialIsometry U ↔ U * Uᴴ * U = U) ∧
    (IsPartialIsometry U ↔ Uᴴ * U * Uᴴ = Uᴴ) ∧
    (IsPartialIsometry U ↔ Uᴴ = U.pinv) ∧
    (IsPartialIsometry U ↔ IsPartialIsometry U.pinv) := by
  have hp := isPartialIsometry_iff_adjoint_eq_pinv U
  have hAdj : IsPartialIsometry U ↔ IsPartialIsometry Uᴴ := by
    rw [hp, isPartialIsometry_iff_adjoint_eq_pinv, pinv_conjTranspose]
    constructor <;> intro h <;>
      simpa only [conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose h
  have hDual :
      IsPartialIsometry Uᴴ ↔ (U * Uᴴ).IsHermitian ∧ IsIdempotentElem (U * Uᴴ) := by
    simpa only [conjTranspose_conjTranspose] using isPartialIsometry_iff_gram_idempotent Uᴴ
  refine ⟨hAdj, isPartialIsometry_iff_gram_idempotent U, hAdj.trans hDual,
    isPartialIsometry_iff_reflexive U, ?_, hp, ?_⟩
  · apply hAdj.trans
    simpa only [conjTranspose_conjTranspose] using isPartialIsometry_iff_reflexive Uᴴ
  · rw [hp, isPartialIsometry_iff_adjoint_eq_pinv, Chapter01.pinv_pinv]
    constructor <;> intro h <;>
      simpa only [conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose h.symm

end PartialIsometries

section CanonicalPolar

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Theorem 7**, Equations (79)–(80), of [benIsrael2003generalized],
Chapter 6. The left and right positive polar factors have the ranges of
the partial isometry and its adjoint, respectively. -/
structure IsCanonicalPolarDecomposition (A E : Matrix m n ℂ)
    (G : Matrix m m ℂ) (H : Matrix n n ℂ) : Prop where
  partialIsometry : IsPartialIsometry E
  left_posSemidef : G.PosSemidef
  right_posSemidef : H.PosSemidef
  left_eq : A = G * E
  right_eq : A = E * H
  left_range : (toEuclideanLin E).range = (toEuclideanLin G).range
  right_range : (toEuclideanLin Eᴴ).range = (toEuclideanLin H).range

private theorem final_gram_of_partialIsometry {E : Matrix m n ℂ} (hE : IsPartialIsometry E) :
    E * Eᴴ = orthogonalProjector (toEuclideanLin E).range := by
  rw [(isPartialIsometry_iff_adjoint_eq_pinv E).mp hE]
  exact toEuclideanLin.injective (E.mul_pinv_eq_starProjection.trans
    (toEuclideanLin_orthogonalProjector _).symm)

private theorem supported_left_polar {A E : Matrix m n ℂ} {G : Matrix m m ℂ}
    (hE : IsPartialIsometry E) (hG : G.IsHermitian) (hA : A = G * E)
    (hr : (toEuclideanLin E).range = (toEuclideanLin G).range) :
    A * Aᴴ = G * G ∧ E = G.pinv * A := by
  have hEE := final_gram_of_partialIsometry hE
  have hP : (E * Eᴴ) * G = G := by
    apply toEuclideanLin.injective
    rw [hEE, hr]
    ext1 x
    rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector,
      ContinuousLinearMap.coe_coe]
    exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ _)
  have hGG : G.pinv * G = E * Eᴴ := by
    apply toEuclideanLin.injective
    rw [G.pinv_mul_eq_starProjection, hG.eq, hEE, hr, toEuclideanLin_orthogonalProjector]
  refine ⟨?_, ?_⟩
  · rw [hA, conjTranspose_mul, hG.eq]
    calc
      (G * E) * (Eᴴ * G) = G * ((E * Eᴴ) * G) := by simp only [Matrix.mul_assoc]
      _ = G * G := by rw [hP]
  · rw [hA, ← Matrix.mul_assoc, hGG, (isPartialIsometry_iff_reflexive E).mp hE]

/-- **Theorem 7**, Equations (81), (84), of [benIsrael2003generalized],
Chapter 6. The supported factors square to the Gram matrices, and the
partial isometry is recovered from the left positive factor. -/
theorem IsCanonicalPolarDecomposition.gram_and_recover
    {A E : Matrix m n ℂ} {G : Matrix m m ℂ} {H : Matrix n n ℂ}
    (h : IsCanonicalPolarDecomposition A E G H) :
    G * G = A * Aᴴ ∧ H * H = Aᴴ * A ∧ E = G.pinv * A := by
  have hl := supported_left_polar h.partialIsometry h.left_posSemidef.isHermitian
    h.left_eq h.left_range
  have hAr : Aᴴ = H * Eᴴ := by
    rw [h.right_eq, conjTranspose_mul, h.right_posSemidef.isHermitian.eq]
  have hr := supported_left_polar ((theorem_6_5 E).1.mp h.partialIsometry)
    h.right_posSemidef.isHermitian hAr h.right_range
  rw [conjTranspose_conjTranspose] at hr
  exact ⟨hl.1.symm, hr.1.symm, hl.2⟩

open scoped MatrixOrder in
/-- **Theorem 7** of [benIsrael2003generalized], Chapter 6. The support
conditions determine all three polar factors uniquely. -/
theorem IsCanonicalPolarDecomposition.unique
    {A E E' : Matrix m n ℂ} {G G' : Matrix m m ℂ} {H H' : Matrix n n ℂ}
    (h : IsCanonicalPolarDecomposition A E G H)
    (h' : IsCanonicalPolarDecomposition A E' G' H') : E = E' ∧ G = G' ∧ H = H' := by
  obtain ⟨hG, hH, hE⟩ := h.gram_and_recover
  obtain ⟨hG', hH', hE'⟩ := h'.gram_and_recover
  have hGG : G = G' := by
    calc
      G = CFC.sqrt (A * Aᴴ) := by rw [← hG, CFC.sqrt_mul_self _ h.left_posSemidef.nonneg]
      _ = G' := by rw [← hG', CFC.sqrt_mul_self _ h'.left_posSemidef.nonneg]
  have hHH : H = H' := by
    calc
      H = CFC.sqrt (Aᴴ * A) := by rw [← hH, CFC.sqrt_mul_self _ h.right_posSemidef.nonneg]
      _ = H' := by rw [← hH', CFC.sqrt_mul_self _ h'.right_posSemidef.nonneg]
  exact ⟨hE.trans (by rw [hGG, ← hE']), hGG, hHH⟩

omit [DecidableEq n] in
open scoped MatrixOrder in
/-- **Exercise 37** of [benIsrael2003generalized], Chapter 6, Equation (89).
A positive semidefinite matrix has a unique positive semidefinite square
root and both matrices have the same rank. -/
theorem exercise_6_37 (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    ∃! B, B.PosSemidef ∧ B * B = A ∧ B.rank = A.rank := by
  classical
  let B := CFC.sqrt A
  have hB : B.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSq : B * B = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hr : B.rank = A.rank := by
    have he := rank_conjTranspose_mul_self B
    rw [hB.isHermitian.eq, hSq] at he
    exact he.symm
  refine ⟨B, ⟨hB, hSq, hr⟩, ?_⟩
  rintro B' ⟨hB', hSq', -⟩
  change B' = CFC.sqrt A
  rw [← hSq', CFC.sqrt_mul_self _ hB'.nonneg]

end CanonicalPolar

section SingularFactors

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
  {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {σ : ℕ → ℝ}

private theorem isUnit_det_singularDiagonal (h : IsSingularValueDecomposition A U σ V) :
    IsUnit (diagonal (fun i : Fin A.rank => (σ i : ℂ))).det := by
  rw [det_diagonal, isUnit_iff_ne_zero]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Complex.ofReal_ne_zero.mpr ?_)
  rw [h.eq_sortedSingularValues, Ne, A.sortedSingularValues_eq_zero_iff_rank_le i]
  exact not_le.mpr i.isLt

/-- **Theorem 6** of [benIsrael2003generalized], Chapter 6, Equations
(75)–(78). The leading singular-vector matrices and their cross product
are partial isometries. Their range projections are the Gram products
of these factors. -/
theorem theorem_6_6 (h : IsSingularValueDecomposition A U σ V) :
    let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
    let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
    let E := Ur * Vrᴴ
    let P := orthogonalProjector (toEuclideanLin A).range
    let Q := orthogonalProjector (toEuclideanLin Aᴴ).range
    IsPartialIsometry Ur ∧ IsPartialIsometry Vr ∧ IsPartialIsometry E ∧
      Urᴴ * Ur = 1 ∧ Vrᴴ * Vr = 1 ∧
      Ur * Urᴴ = P ∧ Vr * Vrᴴ = Q ∧ E * Eᴴ = P ∧ Eᴴ * E = Q := by
  let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
  let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
  let D := diagonal (fun i : Fin A.rank => (σ i : ℂ))
  let E := Ur * Vrᴴ
  have hUr : Urᴴ * Ur = 1 :=
    conjTranspose_submatrix_castLE_mul_self _ h.1.mem_unitaryGroup_left
  have hVr : Vrᴴ * Vr = 1 :=
    conjTranspose_submatrix_castLE_mul_self _ h.1.mem_unitaryGroup_right
  have hE : Eᴴ = Vr * Urᴴ := by simp only [E, conjTranspose_mul, conjTranspose_conjTranspose]
  have hA : A = Ur * D * Vrᴴ :=
    (svd_truncation_rank h).symm.trans (svd_truncation_expansion h le_rfl).1
  have hInv : A.pinv = Vr * D⁻¹ * Urᴴ := (svd_pinv_expansion h).1
  have hAP : A * A.pinv = Ur * Urᴴ := by
    calc
      A * A.pinv = (Ur * D * Vrᴴ) * (Vr * D⁻¹ * Urᴴ) :=
        congrArg₂ (fun X Y => X * Y) hA hInv
      _ = Ur * (D * (Vrᴴ * Vr) * D⁻¹) * Urᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hVr, Matrix.mul_one, mul_nonsing_inv D (isUnit_det_singularDiagonal h),
          Matrix.mul_one]
  have hAQ : A.pinv * A = Vr * Vrᴴ := by
    calc
      A.pinv * A = (Vr * D⁻¹ * Urᴴ) * (Ur * D * Vrᴴ) :=
        congrArg₂ (fun X Y => X * Y) hInv hA
      _ = Vr * (D⁻¹ * (Urᴴ * Ur) * D) * Vrᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hUr, Matrix.mul_one, nonsing_inv_mul D (isUnit_det_singularDiagonal h),
          Matrix.mul_one]
  have hP : Ur * Urᴴ = orthogonalProjector (toEuclideanLin A).range := by
    rw [← hAP]
    exact toEuclideanLin.injective (A.mul_pinv_eq_starProjection.trans
      (toEuclideanLin_orthogonalProjector _).symm)
  have hQ : Vr * Vrᴴ = orthogonalProjector (toEuclideanLin Aᴴ).range := by
    rw [← hAQ]
    exact toEuclideanLin.injective (A.pinv_mul_eq_starProjection.trans
      (toEuclideanLin_orthogonalProjector _).symm)
  have hEE : E * Eᴴ = Ur * Urᴴ := by
    rw [hE]
    change Ur * Vrᴴ * (Vr * Urᴴ) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vrᴴ Vr, hVr, Matrix.one_mul]
  have hE'E : Eᴴ * E = Vr * Vrᴴ := by
    rw [hE]
    change Vr * Urᴴ * (Ur * Vrᴴ) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Urᴴ Ur, hUr, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, hUr, hVr, hP, hQ, hEE.trans hP, hE'E.trans hQ⟩
  · exact (isPartialIsometry_iff_reflexive Ur).mpr (by rw [Matrix.mul_assoc, hUr, Matrix.mul_one])
  · exact (isPartialIsometry_iff_reflexive Vr).mpr (by rw [Matrix.mul_assoc, hVr, Matrix.mul_one])
  · exact (isPartialIsometry_iff_reflexive E).mpr (by
      rw [Matrix.mul_assoc, hE'E]
      change Ur * Vrᴴ * (Vr * Vrᴴ) = Ur * Vrᴴ
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vrᴴ Vr, hVr, Matrix.one_mul])

private theorem range_toEuclideanLin_mul_of_right_inverse {p q r : ℕ}
    (W : Matrix (Fin p) (Fin r) ℂ) {B : Matrix (Fin r) (Fin q) ℂ}
    {C : Matrix (Fin q) (Fin r) ℂ} (h : B * C = 1) :
    (toEuclideanLin (W * B)).range = (toEuclideanLin W).range := by
  refine le_antisymm ?_ ?_
  · rw [toEuclideanLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · have hW : W = (W * B) * C := by rw [Matrix.mul_assoc, h, Matrix.mul_one]
    conv_lhs => rw [hW, toEuclideanLin_mul]
    exact LinearMap.range_comp_le_range _ _

/-- **Theorem 7** of [benIsrael2003generalized], Chapter 6, Equations
(77), (79)–(83). The leading singular-vector factors give a supported
polar decomposition, including for the zero matrix. -/
theorem theorem_6_7 (h : IsSingularValueDecomposition A U σ V) :
    let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
    let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
    let D := diagonal (fun i : Fin A.rank => (σ i : ℂ))
    IsCanonicalPolarDecomposition A (Ur * Vrᴴ) (Ur * D * Urᴴ) (Vr * D * Vrᴴ) := by
  let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
  let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
  let D := diagonal (fun i : Fin A.rank => (σ i : ℂ))
  obtain ⟨-, -, hE, hU, hV, -⟩ := theorem_6_6 h
  have hD : D.PosSemidef :=
    posSemidef_diagonal_iff.mpr (fun i => RCLike.ofReal_nonneg.mpr (h.1.nonneg i))
  have hInv : D * D⁻¹ = 1 := mul_nonsing_inv D (isUnit_det_singularDiagonal h)
  have hA : A = Ur * D * Vrᴴ :=
    (svd_truncation_rank h).symm.trans (svd_truncation_expansion h le_rfl).1
  refine ⟨hE, hD.mul_mul_conjTranspose_same Ur, hD.mul_mul_conjTranspose_same Vr,
    ?_, ?_, ?_, ?_⟩
  · change A = (Ur * D * Urᴴ) * (Ur * Vrᴴ)
    calc
      A = Ur * D * Vrᴴ := hA
      _ = Ur * D * (Urᴴ * Ur) * Vrᴴ := by rw [hU, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · change A = (Ur * Vrᴴ) * (Vr * D * Vrᴴ)
    calc
      A = Ur * D * Vrᴴ := hA
      _ = Ur * (Vrᴴ * Vr) * D * Vrᴴ := by rw [hV, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · change (toEuclideanLin (Ur * Vrᴴ)).range = (toEuclideanLin (Ur * D * Urᴴ)).range
    rw [range_toEuclideanLin_mul_of_right_inverse Ur hV,
      range_toEuclideanLin_mul_of_right_inverse (Ur * D) hU,
      range_toEuclideanLin_mul_of_right_inverse Ur hInv]
  · change (toEuclideanLin (Ur * Vrᴴ)ᴴ).range = (toEuclideanLin (Vr * D * Vrᴴ)).range
    rw [conjTranspose_mul, conjTranspose_conjTranspose,
      range_toEuclideanLin_mul_of_right_inverse Vr hU,
      range_toEuclideanLin_mul_of_right_inverse (Vr * D) hV,
      range_toEuclideanLin_mul_of_right_inverse Vr hInv]

/-- **Theorem 7**, existence and uniqueness, of [benIsrael2003generalized],
Chapter 6. Every rectangular complex matrix has exactly one supported
left-right polar decomposition. -/
theorem existsUnique_canonicalPolarDecomposition (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃! t : Matrix (Fin m) (Fin n) ℂ × Matrix (Fin m) (Fin m) ℂ × Matrix (Fin n) (Fin n) ℂ,
      IsCanonicalPolarDecomposition A t.1 t.2.1 t.2.2 := by
  obtain ⟨U, V, h⟩ := theorem_6_2 A
  let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
  let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
  let D := diagonal (fun i : Fin A.rank => (A.sortedSingularValues i : ℂ))
  refine ⟨(Ur * Vrᴴ, Ur * D * Urᴴ, Vr * D * Vrᴴ), theorem_6_7 h, ?_⟩
  intro t ht
  obtain ⟨hE, hG, hH⟩ := ht.unique (theorem_6_7 h)
  exact Prod.ext hE (Prod.ext hG hH)

private theorem udv_eq_leading_factors {d : ℕ → ℂ} (h : IsUDVDecomposition A U d V) :
    A = U.submatrix id (Fin.castLE A.rank_le_height) * diagonal (fun i : Fin A.rank => d i) *
      (V.submatrix id (Fin.castLE A.rank_le_width))ᴴ := by
  let hm := A.rank_le_height
  let hn := A.rank_le_width
  let Ur := U.submatrix id (Fin.castLE hm)
  let Vr := V.submatrix id (Fin.castLE hn)
  let D := diagonal (fun i : Fin A.rank => d i)
  let Δ : Matrix (Fin m) (Fin n) ℂ := rectDiagonal d
  have hA : A = U * Δ * Vᴴ := h.2.2.1
  calc
    A = U * Δ * Vᴴ := hA
    _ = Ur * D * Vrᴴ := by
      ext i j
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have he (l : Fin n) :
          (U * Δ) i l * Vᴴ l j =
            if (l : ℕ) < A.rank then (U * Δ) i l * Vᴴ l j else 0 := by
        split_ifs with hl
        · rfl
        · have hd : d l = 0 := norm_eq_zero.mp
            ((h.2.2.2 l).trans ((A.sortedSingularValues_eq_zero_iff_rank_le l).mpr
              (Nat.le_of_not_gt hl)))
          rw [show (U * Δ) i l =
            if h : (l : ℕ) < m then U i ⟨l, h⟩ * d l else 0
            from mul_rectDiagonal_apply _ _ _ _]
          simp [hd]
      rw [Finset.sum_congr rfl fun l _ => he l, ← Fin.sum_castLE_eq_sum_ite hn]
      apply Finset.sum_congr rfl
      intro l _
      have hl := l.isLt.trans_le hm
      rw [show (U * Δ) i (Fin.castLE hn l) =
        if h : (l : ℕ) < m then U i ⟨l, h⟩ * d l else 0 from mul_rectDiagonal_apply _ _ _ _,
        dite_eq_left hl, show (Ur * D) i l = Ur i l * d l from mul_diagonal _ _ _ _]
      rfl

private theorem thin_conjugate_mul {p r : ℕ} {W : Matrix (Fin p) (Fin r) ℂ}
    (hW : Wᴴ * W = 1) (D F : Matrix (Fin r) (Fin r) ℂ) :
    (W * D * Wᴴ) * (W * F * Wᴴ) = W * (D * F) * Wᴴ := by
  calc
    _ = W * (D * (Wᴴ * W) * F) * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hW, Matrix.mul_one]

/-- **Corollary 2** of [benIsrael2003generalized], Chapter 6, Equations
(77), (79)–(80), (86)–(87). For a prescribed $UDV^H$ decomposition, the
phase-bearing diagonal gives normal polar factors with the two Gram
identities and the corresponding initial and final ranges. -/
theorem corollary_6_2 {d : ℕ → ℂ} (h : IsUDVDecomposition A U d V) :
    let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
    let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
    let D := diagonal (fun i : Fin A.rank => d i)
    let E := Ur * Vrᴴ
    let G := Ur * D * Urᴴ
    let H := Vr * D * Vrᴴ
    IsPartialIsometry E ∧ IsStarNormal G ∧ IsStarNormal H ∧
      A = G * E ∧ A = E * H ∧
      (toEuclideanLin E).range = (toEuclideanLin G).range ∧
      (toEuclideanLin Eᴴ).range = (toEuclideanLin H).range ∧
      G * Gᴴ = A * Aᴴ ∧ Hᴴ * H = Aᴴ * A := by
  let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
  let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
  let D := diagonal (fun i : Fin A.rank => d i)
  let E := Ur * Vrᴴ
  let G := Ur * D * Urᴴ
  let H := Vr * D * Vrᴴ
  have hU : Urᴴ * Ur = 1 := conjTranspose_submatrix_castLE_mul_self _ h.1
  have hV : Vrᴴ * Vr = 1 := conjTranspose_submatrix_castLE_mul_self _ h.2.1
  have hA : A = Ur * D * Vrᴴ := udv_eq_leading_factors h
  have hAa : Aᴴ = Vr * Dᴴ * Urᴴ := by
    have he := congrArg Matrix.conjTranspose hA
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using he
  have hEa : Eᴴ = Vr * Urᴴ := by simp only [E, conjTranspose_mul, conjTranspose_conjTranspose]
  have hGa : Gᴴ = Ur * Dᴴ * Urᴴ := by
    simp only [G, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hHa : Hᴴ = Vr * Dᴴ * Vrᴴ := by
    simp only [H, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hUnit : IsUnit D.det := by
    change IsUnit (diagonal (fun i : Fin A.rank => d i)).det
    rw [det_diagonal, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ hi => ?_)
    have hz := h.2.2.2 i
    rw [hi, norm_zero] at hz
    exact not_le.mpr i.isLt ((A.sortedSingularValues_eq_zero_iff_rank_le i).mp hz.symm)
  have hInv : D * D⁻¹ = 1 := mul_nonsing_inv D hUnit
  have hD : Dᴴ * D = D * Dᴴ := by
    simp only [D, diagonal_conjTranspose, diagonal_mul_diagonal, mul_comm]
  refine ⟨(isPartialIsometry_iff_reflexive E).mpr ?_, ⟨?_⟩, ⟨?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEa]
    change (Ur * Vrᴴ) * (Vr * Urᴴ) * (Ur * Vrᴴ) = Ur * Vrᴴ
    calc
      _ = Ur * (Vrᴴ * Vr) * (Urᴴ * Ur) * Vrᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, hU, Matrix.mul_one, Matrix.mul_one]
  · change Gᴴ * G = G * Gᴴ
    rw [hGa]
    change (Ur * Dᴴ * Urᴴ) * (Ur * D * Urᴴ) = (Ur * D * Urᴴ) * (Ur * Dᴴ * Urᴴ)
    rw [thin_conjugate_mul hU, thin_conjugate_mul hU, hD]
  · change Hᴴ * H = H * Hᴴ
    rw [hHa]
    change (Vr * Dᴴ * Vrᴴ) * (Vr * D * Vrᴴ) = (Vr * D * Vrᴴ) * (Vr * Dᴴ * Vrᴴ)
    rw [thin_conjugate_mul hV, thin_conjugate_mul hV, hD]
  · change A = (Ur * D * Urᴴ) * (Ur * Vrᴴ)
    calc
      A = Ur * D * Vrᴴ := hA
      _ = Ur * D * (Urᴴ * Ur) * Vrᴴ := by rw [hU, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · change A = (Ur * Vrᴴ) * (Vr * D * Vrᴴ)
    calc
      A = Ur * D * Vrᴴ := hA
      _ = Ur * (Vrᴴ * Vr) * D * Vrᴴ := by rw [hV, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · change (toEuclideanLin (Ur * Vrᴴ)).range = (toEuclideanLin (Ur * D * Urᴴ)).range
    rw [range_toEuclideanLin_mul_of_right_inverse Ur hV,
      range_toEuclideanLin_mul_of_right_inverse (Ur * D) hU,
      range_toEuclideanLin_mul_of_right_inverse Ur hInv]
  · change (toEuclideanLin Eᴴ).range = (toEuclideanLin (Vr * D * Vrᴴ)).range
    rw [hEa, range_toEuclideanLin_mul_of_right_inverse Vr hU,
      range_toEuclideanLin_mul_of_right_inverse (Vr * D) hV,
      range_toEuclideanLin_mul_of_right_inverse Vr hInv]
  · change G * Gᴴ = A * Aᴴ
    calc
      G * Gᴴ = Ur * (D * Dᴴ) * Urᴴ := hGa ▸ thin_conjugate_mul hU D Dᴴ
      _ = (Ur * D * Vrᴴ) * (Vr * Dᴴ * Urᴴ) := by
        calc
          _ = Ur * (D * (Vrᴴ * Vr) * Dᴴ) * Urᴴ := by rw [hV, Matrix.mul_one]
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = A * Aᴴ := congrArg₂ (fun X Y => X * Y) hA.symm hAa.symm
  · change Hᴴ * H = Aᴴ * A
    calc
      Hᴴ * H = Vr * (Dᴴ * D) * Vrᴴ := by
        rw [hHa]
        exact thin_conjugate_mul hV _ _
      _ = (Vr * Dᴴ * Urᴴ) * (Ur * D * Vrᴴ) := by
        calc
          _ = Vr * (Dᴴ * (Urᴴ * Ur) * D) * Vrᴴ := by rw [hU, Matrix.mul_one]
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = Aᴴ * A := congrArg₂ (fun X Y => X * Y) hAa.symm hA.symm

end SingularFactors

section Exercises

/-- **Exercise 38** of [benIsrael2003generalized], Chapter 6, with the
surjectivity hypothesis of the Mazur–Ulam theorem. A surjective isometry
on real normed spaces that fixes zero is linear. -/
theorem exercise_6_38 {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace ℝ X] [NormedSpace ℝ Y] (f : X ≃ᵢ Y) (hf : f 0 = 0) :
    ∃ L : X ≃ₗᵢ[ℝ] Y, ∀ x, L x = f x :=
  ⟨f.toRealLinearIsometryEquivOfMapZero hf, fun _ => rfl⟩

/-- The map $x \mapsto (x,|x|)$ into the supremum-norm product is an
isometry fixing zero and has no linear realization. -/
theorem exercise_6_38_counterexample :
    ∃ f : ℝ → ℝ × ℝ, Isometry f ∧ f 0 = 0 ∧
      ¬ ∃ L : ℝ →ₗ[ℝ] ℝ × ℝ, ∀ x, L x = f x := by
  let f (x : ℝ) := (x, |x|)
  refine ⟨f, Isometry.of_dist_eq ?_, by simp [f], ?_⟩
  · intro x y
    change dist (x, |x|) (y, |y|) = dist x y
    rw [Prod.dist_eq, max_eq_left]
    simpa only [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  · rintro ⟨L, hL⟩
    have he := congrArg Prod.snd (map_neg L (1 : ℝ))
    rw [hL, hL] at he
    norm_num [f] at he

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- **Exercise 39**, forward direction, of [benIsrael2003generalized],
Chapter 6. Any selection of distinct columns of a unitary matrix gives
a partial isometry. -/
theorem exercise_6_39_columns {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ) (e : k ↪ m) :
    IsPartialIsometry (U.submatrix id e) := by
  have h : (U.submatrix id e)ᴴ * U.submatrix id e = 1 := by
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
      conjTranspose_mul_self_of_mem_unitaryGroup hU]
    exact submatrix_one _ e.injective
  exact (isPartialIsometry_iff_reflexive _).mpr (by rw [Matrix.mul_assoc, h, Matrix.mul_one])

/-- **Exercise 40** of [benIsrael2003generalized], Chapter 6. Partial
isometries are preserved by left and right unitary changes of basis. -/
theorem exercise_6_40 {U : Matrix m m ℂ} {V : Matrix n n ℂ} {B : Matrix m n ℂ}
    (hU : U ∈ unitaryGroup m ℂ) (hV : V ∈ unitaryGroup n ℂ) (hB : IsPartialIsometry B) :
    IsPartialIsometry (U * B * Vᴴ) := by
  have hUr := conjTranspose_mul_self_of_mem_unitaryGroup hU
  have hVr := conjTranspose_mul_self_of_mem_unitaryGroup hV
  have hb := (isPartialIsometry_iff_reflexive B).mp hB
  apply (isPartialIsometry_iff_reflexive _).mpr
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  calc
    _ = U * B * (Vᴴ * V) * Bᴴ * (Uᴴ * U) * B * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by simp only [hVr, hUr, Matrix.mul_one, Matrix.mul_assoc, hb]

/-- **Exercise 43**, definition (90), of [benIsrael2003generalized],
Chapter 6. A contraction never increases the Euclidean norm. -/
def IsContraction (A : Matrix m n ℂ) : Prop :=
  ∀ x, ‖toEuclideanLin A x‖ ≤ ‖x‖

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
private theorem isContraction_iff_l2_opNorm_le_one (A : Matrix m n ℂ) :
    IsContraction A ↔ ‖A‖ ≤ 1 := by
  rw [l2_opNorm_def, ContinuousLinearMap.opNorm_le_iff zero_le_one]
  simp only [one_mul]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 43(a,b)** of [benIsrael2003generalized], Chapter 6. The
contraction condition is equivalent to the spectral norm bound of one,
and it is preserved by adjoints. -/
theorem exercise_6_43_adjoint (A : Matrix m n ℂ) :
    (IsContraction A ↔ ‖A‖ ≤ 1) ∧ (IsContraction A ↔ IsContraction Aᴴ) := by
  refine ⟨isContraction_iff_l2_opNorm_le_one A, ?_⟩
  rw [isContraction_iff_l2_opNorm_le_one A, isContraction_iff_l2_opNorm_le_one Aᴴ,
    l2_opNorm_conjTranspose]

private theorem norm_apply_eq_norm_initialProjection {U : Matrix m n ℂ}
    (hU : IsPartialIsometry U) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin U x‖ = ‖(toEuclideanLin Uᴴ).range.starProjection x‖ := by
  let T := toEuclideanLin U
  let L := (toEuclideanLin Uᴴ).range
  let y := L.starProjection x
  have hL : L = T.kerᗮ := by
    rw [T.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint]
  have hz : x - y ∈ T.ker := by
    have ho : Lᗮ = T.ker := by rw [hL, Submodule.orthogonal_orthogonal]
    rw [← ho]
    exact L.sub_starProjection_mem_orthogonal x
  have he := LinearMap.mem_ker.mp hz
  rw [map_sub, sub_eq_zero] at he
  change ‖T x‖ = ‖y‖
  rw [he]
  exact hU _ (hL ▸ L.starProjection_apply_mem x)

/-- **Exercise 45** of [benIsrael2003generalized], Chapter 6. The modulus
of an eigenvalue of a partial isometry is the ratio of the projected
eigenvector norm to its original norm, and is at most one. -/
theorem exercise_6_45 {U : Matrix n n ℂ} (hU : IsPartialIsometry U)
    {x : EuclideanSpace ℂ n} (hx : x ≠ 0) {μ : ℂ} (he : toEuclideanLin U x = μ • x) :
    ‖μ‖ = ‖(toEuclideanLin Uᴴ).range.starProjection x‖ / ‖x‖ ∧ ‖μ‖ ≤ 1 := by
  have h := norm_apply_eq_norm_initialProjection hU x
  rw [he, norm_smul] at h
  have hp := norm_pos_iff.mpr hx
  have hμ := (eq_div_iff hp.ne').mpr h
  exact ⟨hμ, hμ.le.trans ((div_le_one hp).mpr (Submodule.norm_starProjection_apply_le _ _))⟩

/-- **Exercise 47** of [benIsrael2003generalized], Chapter 6. A square
partial isometry is normal exactly when its initial and final spaces
coincide. -/
theorem exercise_6_47 {U : Matrix n n ℂ} (hU : IsPartialIsometry U) :
    IsStarNormal U ↔ (toEuclideanLin U).range = (toEuclideanLin Uᴴ).range := by
  have hI := (isPartialIsometry_iff_initial_gram U).mp hU
  have hF := final_gram_of_partialIsometry hU
  constructor
  · intro h
    have he : Uᴴ * U = U * Uᴴ := h.star_comm_self
    rw [hI, hF] at he
    have hi := congrArg (fun M : Matrix n n ℂ => (toEuclideanLin M).range) he
    simpa only [toEuclideanLin_orthogonalProjector, Submodule.range_starProjection] using hi.symm
  · intro h
    refine ⟨?_⟩
    change Uᴴ * U = U * Uᴴ
    rw [hI, hF, h]

/-- **Exercise 48** of [benIsrael2003generalized], Chapter 6. A normal
partial isometry has eigenvalue moduli zero or one. -/
theorem exercise_6_48 {U : Matrix n n ℂ} (hU : IsPartialIsometry U) (hN : IsStarNormal U)
    {x : EuclideanSpace ℂ n} (hx : x ≠ 0) {μ : ℂ} (he : toEuclideanLin U x = μ • x) :
    ‖μ‖ = 0 ∨ ‖μ‖ = 1 := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · exact Or.inl norm_zero
  right
  have hxR : x ∈ (toEuclideanLin U).range := by
    refine ⟨μ⁻¹ • x, ?_⟩
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hxI : x ∈ (toEuclideanLin U).kerᗮ := by
    rw [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← (exercise_6_47 hU).mp hN]
    exact hxR
  have hn := hU x hxI
  rw [he, norm_smul] at hn
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hx) (hn.trans (one_mul _).symm)

open scoped MatrixOrder in
/-- **Exercise 53** of [benIsrael2003generalized], Chapter 6, Equation (91).
The original matrix is a partial isometry precisely when its supported
left polar factor is an orthogonal projector. -/
theorem exercise_6_53 {A E : Matrix m n ℂ} {G : Matrix m m ℂ} {H : Matrix n n ℂ}
    (h : IsCanonicalPolarDecomposition A E G H) :
    IsPartialIsometry A ↔ G.IsHermitian ∧ IsIdempotentElem G := by
  have hG := h.gram_and_recover.1
  have hA := (theorem_6_5 A).2.2.1
  constructor
  · intro hA'
    have hI := (hA.mp hA').2
    have hPSD := posSemidef_self_mul_conjTranspose A
    have he : G = A * Aᴴ := by
      calc
        G = CFC.sqrt (G * G) := (CFC.sqrt_mul_self _ h.left_posSemidef.nonneg).symm
        _ = CFC.sqrt ((A * Aᴴ) * (A * Aᴴ)) := by rw [hG, hI.eq]
        _ = A * Aᴴ := CFC.sqrt_mul_self _ hPSD.nonneg
    rw [he]
    exact ⟨isHermitian_mul_conjTranspose_self A, hI⟩
  · rintro ⟨-, hI⟩
    apply hA.mpr
    rw [← hG, hI.eq]
    exact ⟨h.left_posSemidef.isHermitian, hI⟩

/-- **Exercise 59** of [benIsrael2003generalized], Chapter 6.
Multiplication by a unitary matrix cannot increase the real trace
of a positive semidefinite matrix. -/
theorem exercise_6_59 {H W : Matrix n n ℂ} (hH : H.PosSemidef)
    (hW : W ∈ unitaryGroup n ℂ) : (trace (H * W)).re ≤ (trace H).re := by
  rw [trace_mul_comm]
  exact re_trace_mul_le_trace_of_posSemidef hW hH

/-- The upper bound in **Exercise 61** of [benIsrael2003generalized],
Chapter 6. Unitary factors leave the singular values in von Neumann's
trace bound unchanged. -/
theorem exercise_6_61_upper {A : Matrix m n ℂ} {B : Matrix n m ℂ}
    {X : Matrix n n ℂ} {W : Matrix m m ℂ} (hX : X ∈ unitaryGroup n ℂ)
    (hW : W ∈ unitaryGroup m ℂ) :
    (trace (A * X * B * W)).re ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      A.sortedSingularValues i * B.sortedSingularValues i := by
  have hAX := exercise_2 A (one_mem (unitaryGroup m ℂ)) hX
  have hBW := exercise_2 B (one_mem (unitaryGroup n ℂ)) hW
  rw [Matrix.one_mul] at hAX hBW
  rw [Matrix.mul_assoc (A * X) B W]
  have h := re_trace_mul_le_sum_sortedSingularValues_mul (A * X) (B * W)
  rwa [hAX, hBW] at h

end Exercises

end BenIsraelGreville.Chapter06
