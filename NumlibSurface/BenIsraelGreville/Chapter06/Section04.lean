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
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Partial isometries and polar decomposition

Section 6.4 of [benIsrael2003generalized] characterizes partial isometries
and uses them to give canonical polar factors for rectangular matrices.

## Deviations from the source

* **Corollary 2** (scope). The normal factors are specified for a fixed
  $UDV^H$ factorization. The range constraints permit changes of phase.
* **Equation (88)** (phase). The complex argument accounts for the
  quadrant of the scalar.
* **Exercise 38** (correction). Mazur–Ulam requires a surjective isometry
  between general real normed spaces. The map $x \mapsto (x,|x|)$ into
  the product with supremum norm illustrates the need for this hypothesis.
* **Exercise 60** (dimensions). A trial partial isometry has the dimensions
  of the adjoint of the given matrix so that the product is square.
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

/-- **Equations (82)–(83)** of [benIsrael2003generalized], Chapter 6.
Any number of singular directions between the rank and the smaller
matrix dimension gives polar factors. The rank of the isometry factor
is the number of directions used. -/
theorem polar_factors_of_larger_truncation (h : IsSingularValueDecomposition A U σ V)
    {k : ℕ} (hr : A.rank ≤ k) (hm : k ≤ m) (hn : k ≤ n) :
    let Uk := U.submatrix id (Fin.castLE hm)
    let Vk := V.submatrix id (Fin.castLE hn)
    let Dk := diagonal (fun i : Fin k => (σ i : ℂ))
    let E := Uk * Vkᴴ
    let G := Uk * Dk * Ukᴴ
    let H := Vk * Dk * Vkᴴ
    IsPartialIsometry E ∧ E.rank = k ∧ G.PosSemidef ∧ H.PosSemidef ∧
      A = G * E ∧ A = E * H := by
  let Uk := U.submatrix id (Fin.castLE hm)
  let Vk := V.submatrix id (Fin.castLE hn)
  let Dk := diagonal (fun i : Fin k => (σ i : ℂ))
  let E := Uk * Vkᴴ
  have hU : Ukᴴ * Uk = 1 := conjTranspose_submatrix_castLE_mul_self _
    h.1.mem_unitaryGroup_left
  have hV : Vkᴴ * Vk = 1 := conjTranspose_submatrix_castLE_mul_self _
    h.1.mem_unitaryGroup_right
  have hE : Eᴴ = Vk * Ukᴴ := by simp only [E, conjTranspose_mul, conjTranspose_conjTranspose]
  have hP : E * Eᴴ * E = E := by
    rw [hE]
    change (Uk * Vkᴴ) * (Vk * Ukᴴ) * (Uk * Vkᴴ) = Uk * Vkᴴ
    calc
      _ = Uk * (Vkᴴ * Vk) * (Ukᴴ * Uk) * Vkᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hU, hV, Matrix.mul_one]
  have hrE : E.rank = k := by
    have hIE : Ukᴴ * E * Vk = 1 := by
      change Ukᴴ * (Uk * Vkᴴ) * Vk = 1
      rw [← Matrix.mul_assoc Ukᴴ Uk Vkᴴ, hU, Matrix.one_mul, hV]
    refine le_antisymm ((rank_mul_le_left _ _).trans (by simpa using rank_le_card_width Uk)) ?_
    calc
      k = (Ukᴴ * E * Vk).rank := by simp [hIE]
      _ ≤ (Ukᴴ * E).rank := rank_mul_le_left _ _
      _ ≤ E.rank := rank_mul_le_right _ _
  have hD : Dk.PosSemidef :=
    posSemidef_diagonal_iff.mpr (fun i => RCLike.ofReal_nonneg.mpr (h.1.nonneg i))
  have hA : A = Uk * Dk * Vkᴴ := by
    have htr : svdTruncation U σ V k = A := by
      have hpad : (fun i => if i < k then (σ i : ℂ) else 0) = fun i => (σ i : ℂ) := by
        funext i
        split_ifs with hi
        · rfl
        · rw [h.2 i (hr.trans (not_lt.mp hi)), Complex.ofReal_zero]
      change U * (rectDiagonal (fun i => if i < k then (σ i : ℂ) else 0) :
        Matrix (Fin m) (Fin n) ℂ) * star V = A
      rw [hpad]
      exact h.1.eq_mul_mul_star.symm
    rw [← htr, Matrix.svdTruncation_eq_sum U σ V hm hn]
    ext i j
    rw [Matrix.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (Uk * Dk) i l = Uk i l * (σ l : ℂ) from mul_diagonal _ _ _ _]
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, col_apply, smul_eq_mul,
      conjTranspose_apply, Uk, Vk, submatrix_apply, id_eq]
    change (σ l : ℂ) * (U i (Fin.castLE hm l) * star (V j (Fin.castLE hn l))) =
      U i (Fin.castLE hm l) * (σ l : ℂ) * star (V j (Fin.castLE hn l))
    rw [mul_assoc]
    exact mul_left_comm _ _ _
  refine ⟨(isPartialIsometry_iff_reflexive E).mpr hP, hrE,
    hD.mul_mul_conjTranspose_same Uk, hD.mul_mul_conjTranspose_same Vk, ?_, ?_⟩
  · change A = (Uk * Dk * Ukᴴ) * (Uk * Vkᴴ)
    calc
      A = Uk * Dk * Vkᴴ := hA
      _ = Uk * Dk * (Ukᴴ * Uk) * Vkᴴ := by rw [hU, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · change A = (Uk * Vkᴴ) * (Vk * Dk * Vkᴴ)
    calc
      A = Uk * Dk * Vkᴴ := hA
      _ = Uk * (Vkᴴ * Vk) * Dk * Vkᴴ := by rw [hV, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

/-- **Equations (82)–(83)** of [benIsrael2003generalized], Chapter 6.
When the rank is below both matrix dimensions, two distinct partial
isometries occur as polar factors. -/
theorem polar_isometry_nonunique_of_rank_lt (h : IsSingularValueDecomposition A U σ V)
    (hr : A.rank < min m n) :
    ∃ E₁ E₂ : Matrix (Fin m) (Fin n) ℂ,
      ∃ G₁ G₂ : Matrix (Fin m) (Fin m) ℂ,
        E₁ ≠ E₂ ∧ IsPartialIsometry E₁ ∧ IsPartialIsometry E₂ ∧
          G₁.PosSemidef ∧ G₂.PosSemidef ∧ A = G₁ * E₁ ∧ A = G₂ * E₂ := by
  obtain ⟨hE₁, hr₁, hG₁, -, hA₁, -⟩ :=
    polar_factors_of_larger_truncation h le_rfl A.rank_le_height A.rank_le_width
  obtain ⟨hE₂, hr₂, hG₂, -, hA₂, -⟩ :=
    polar_factors_of_larger_truncation h (Nat.le_succ A.rank)
      (hr.trans_le (min_le_left m n)) (hr.trans_le (min_le_right m n))
  refine ⟨_, _, _, _, ?_, hE₁, hE₂, hG₁, hG₂, hA₁, hA₂⟩
  intro he
  exact Nat.ne_of_lt (Nat.lt_succ_self A.rank)
    (hr₁.symm.trans ((congrArg Matrix.rank he).trans hr₂))

/-- **Equation (85)** of [benIsrael2003generalized], Chapter 6.
The Moore–Penrose inverse of the left positive polar factor reciprocates
its nonzero singular values within the leading left singular space. -/
theorem polar_left_factor_pinv (h : IsSingularValueDecomposition A U σ V) :
    let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
    let D := diagonal (fun i : Fin A.rank => (σ i : ℂ))
    (Ur * D * Urᴴ).pinv = Ur * D⁻¹ * Urᴴ := by
  let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
  let D := diagonal (fun i : Fin A.rank => (σ i : ℂ))
  have hU : Urᴴ * Ur = 1 := conjTranspose_submatrix_castLE_mul_self _
    h.1.mem_unitaryGroup_left
  have hD := mul_nonsing_inv D (isUnit_det_singularDiagonal h)
  have hDi := nonsing_inv_mul D (isUnit_det_singularDiagonal h)
  let G := Ur * D * Urᴴ
  let B := Ur * D⁻¹ * Urᴴ
  have hGB : G * B = Ur * Urᴴ := by
    change (Ur * D * Urᴴ) * (Ur * D⁻¹ * Urᴴ) = Ur * Urᴴ
    calc
      _ = Ur * (D * (Urᴴ * Ur) * D⁻¹) * Urᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hU, Matrix.mul_one, hD]
  have hBG : B * G = Ur * Urᴴ := by
    change (Ur * D⁻¹ * Urᴴ) * (Ur * D * Urᴴ) = Ur * Urᴴ
    calc
      _ = Ur * (D⁻¹ * (Urᴴ * Ur) * D) * Urᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hU, Matrix.mul_one, hDi]
  change G.pinv = B
  symm
  refine G.pinv_unique ?_ ?_ ?_ ?_
  · rw [hGB]
    change (Ur * Urᴴ) * (Ur * D * Urᴴ) = Ur * D * Urᴴ
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Urᴴ Ur, hU, Matrix.one_mul]
  · rw [hBG]
    change (Ur * Urᴴ) * (Ur * D⁻¹ * Urᴴ) = Ur * D⁻¹ * Urᴴ
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Urᴴ Ur, hU, Matrix.one_mul]
  · rw [hGB]
    exact isHermitian_mul_conjTranspose_self _
  · rw [hBG]
    exact isHermitian_mul_conjTranspose_self _

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

private theorem projector_sub_final_gram_posSemidef_iff (A : Matrix m n ℂ)
    (L : Submodule ℂ (EuclideanSpace ℂ m)) :
    (orthogonalProjector L - A * Aᴴ).PosSemidef ↔
      ∀ x, ‖toEuclideanLin Aᴴ x‖ ≤ ‖L.starProjection x‖ := by
  rw [← isPositive_toEuclideanLin_iff]
  have hsym : (toEuclideanLin (orthogonalProjector L - A * Aᴴ)).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr
      ((isHermitian_orthogonalProjector L).sub (isHermitian_mul_conjTranspose_self A))
  rw [LinearMap.IsPositive, and_iff_right hsym]
  apply forall_congr'
  intro x
  have hProjection : inner ℂ (L.starProjection x) x =
      inner ℂ (L.starProjection x) (L.starProjection x) := by
    have h := L.inner_starProjection_left_eq_right (L.starProjection x) x
    rwa [L.starProjection_eq_self_iff.mpr (L.starProjection_apply_mem x)] at h
  have hGram := toEuclideanLin_conjTranspose_inner_left Aᴴ x (toEuclideanLin Aᴴ x)
  rw [conjTranspose_conjTranspose] at hGram
  rw [map_sub, LinearMap.sub_apply, inner_sub_left, toEuclideanLin_orthogonalProjector,
    ContinuousLinearMap.coe_coe, hProjection, toEuclideanLin_mul_apply, hGram,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, map_sub, RCLike.re_ofReal_pow,
    RCLike.re_ofReal_pow, sub_nonneg]
  exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)

/-- **Exercise 43(c)** of [benIsrael2003generalized], Chapter 6. A
contraction's final Gram matrix is dominated by each orthogonal
projection whose range contains the matrix range. -/
theorem exercise_6_43_projector (A : Matrix m n ℂ) :
    IsContraction A ↔ ∀ L : Submodule ℂ (EuclideanSpace ℂ m),
      (toEuclideanLin A).range ≤ L → (orthogonalProjector L - A * Aᴴ).PosSemidef := by
  rw [(exercise_6_43_adjoint A).2]
  constructor
  · intro hA L hL
    apply (projector_sub_final_gram_posSemidef_iff A L).mpr
    intro x
    have hk : x - L.starProjection x ∈ (toEuclideanLin Aᴴ).ker := by
      rw [toEuclideanLin_conjTranspose_eq_adjoint, ← LinearMap.orthogonal_range]
      exact (Submodule.orthogonal_le_orthogonal_iff.mpr hL)
        (L.sub_starProjection_mem_orthogonal x)
    have hx := LinearMap.mem_ker.mp hk
    rw [map_sub, sub_eq_zero] at hx
    rw [hx]
    exact hA _
  · intro hA x
    have h := (projector_sub_final_gram_posSemidef_iff A ⊤).mp (hA ⊤ le_top) x
    simpa only [Submodule.starProjection_top, ContinuousLinearMap.id_apply] using h

open scoped MatrixOrder in
/-- **Exercise 44** of [benIsrael2003generalized], Chapter 6. Appending
the positive square root of the Gram defect makes the final Gram
matrix an orthogonal projection. -/
theorem exercise_6_44 (A : Matrix m n ℂ) (hA : IsContraction A)
    (L : Submodule ℂ (EuclideanSpace ℂ m)) (hL : (toEuclideanLin A).range ≤ L) :
    let B := CFC.sqrt (orthogonalProjector L - A * Aᴴ)
    let M := fromBlocks A B (0 : Matrix n n ℂ) (0 : Matrix n m ℂ)
    IsPartialIsometry M := by
  let P := orthogonalProjector L
  let B := CFC.sqrt (P - A * Aᴴ)
  let M := fromBlocks A B (0 : Matrix n n ℂ) (0 : Matrix n m ℂ)
  have hdef := (exercise_6_43_projector A).mp hA L hL
  have hB : B.IsHermitian := (CFC.sqrt_nonneg (P - A * Aᴴ)).posSemidef.isHermitian
  have hsq : B * B = P - A * Aᴴ := CFC.sqrt_mul_sqrt_self _ hdef.nonneg
  have hMM : M * Mᴴ = fromBlocks P (0 : Matrix m n ℂ) (0 : Matrix n m ℂ) 0 := by
    simp only [M, fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, hB.eq, hsq]
    rw [add_sub_cancel]
  apply (theorem_6_5 M).2.2.1.mpr
  refine ⟨isHermitian_mul_conjTranspose_self M, ?_⟩
  rw [hMM, IsIdempotentElem, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, (isIdempotentElem_orthogonalProjector L).eq, P]

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

/-- **Equation (88)** of [benIsrael2003generalized], Chapter 6.
The complex argument gives the phase in the scalar polar decomposition,
with unit modulus for every argument. -/
theorem polar_complex_scalar (z : ℂ) :
    z = (‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I) ∧
      ‖Complex.exp ((z.arg : ℂ) * Complex.I)‖ = 1 :=
  ⟨(Complex.norm_mul_exp_arg_mul_I z).symm, Complex.norm_exp_ofReal_mul_I _⟩

/-- **Corollary 2** of [benIsrael2003generalized], Chapter 6. The range
conditions allow distinct choices of normal factors, even in dimension one. -/
theorem normal_polar_factors_range_nonunique :
    ∃ A E₁ E₂ G₁ G₂ : Matrix (Fin 1) (Fin 1) ℂ,
      E₁ ≠ E₂ ∧ G₁ ≠ G₂ ∧ IsPartialIsometry E₁ ∧ IsPartialIsometry E₂ ∧
        IsStarNormal G₁ ∧ IsStarNormal G₂ ∧
        (toEuclideanLin E₁).range = (toEuclideanLin G₁).range ∧
        (toEuclideanLin E₂).range = (toEuclideanLin G₂).range ∧
        (toEuclideanLin E₁ᴴ).range = (toEuclideanLin G₁).range ∧
        (toEuclideanLin E₂ᴴ).range = (toEuclideanLin G₂).range ∧
        A = G₁ * E₁ ∧ A = E₁ * G₁ ∧ A = G₂ * E₂ ∧ A = E₂ * G₂ := by
  let I : Matrix (Fin 1) (Fin 1) ℂ := 1
  have hne : I ≠ -I := by
    intro h
    have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
    norm_num [I] at he
  refine ⟨I, I, -I, I, -I, hne, hne, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_⟩ <;> try simp [I]
  · exact (isPartialIsometry_iff_reflexive _).mpr (by simp)
  · exact (isPartialIsometry_iff_reflexive _).mpr (by simp)
  · exact ⟨by simp⟩
  · exact ⟨by simp⟩


/-- **Exercise 39**, converse direction, of [benIsrael2003generalized],
Chapter 6. A partial isometry of full column rank extends to a unitary
matrix by adjoining orthonormal columns. The two injections select the
consecutive blocks of the completed square matrix. -/
theorem exercise_6_39_completion {m k : ℕ} (W : Matrix (Fin m) (Fin k) ℂ)
    (hW : IsPartialIsometry W) (hr : W.rank = k) :
    ∃ (hk : k ≤ m) (U : Matrix (Fin m) (Fin m) ℂ)
        (V : Matrix (Fin m) (Fin (m - k)) ℂ),
      U ∈ unitaryGroup (Fin m) ℂ ∧ U.submatrix id (Fin.castLE hk) = W ∧
        U.submatrix id (fun j : Fin (m - k) => (⟨k + j, by omega⟩ : Fin m)) = V ∧
        IsPartialIsometry V := by
  have hk : k ≤ m := hr ▸ (by simpa using rank_le_card_height W)
  have hinj := (mulVec_injective_iff_rank_eq_card (M := W)).mpr (by simpa using hr)
  have hker : (toEuclideanLin W).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact (WithLp.ofLp_injective 2) (hinj (congrArg (fun z : EuclideanSpace ℂ (Fin m) => z.ofLp) hxy))
  have hWg : Wᴴ * W = 1 := by
    have hrange : (toEuclideanLin Wᴴ).range = ⊤ := by
      rw [toEuclideanLin_conjTranspose_eq_adjoint, ← LinearMap.orthogonal_ker,
        hker, Submodule.bot_orthogonal_eq_top]
    rw [(isPartialIsometry_iff_initial_gram W).mp hW, hrange]
    apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector, Submodule.starProjection_top, toEuclideanLin_one]
    rfl
  let e : Fin k ↪ Fin m := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  obtain ⟨U, hU, hUe⟩ := exists_mem_unitaryGroup_submatrix_eq W hWg e
  let f : Fin (m - k) ↪ Fin m :=
    ⟨fun j => ⟨k + j, by omega⟩, fun i j hij => by
      have he := Fin.val_eq_of_eq hij
      change k + (i : ℕ) = k + (j : ℕ) at he
      exact Fin.ext (Nat.add_left_cancel he)⟩
  exact ⟨hk, U, U.submatrix id f, hU, hUe, rfl, exercise_6_39_columns hU f⟩

private theorem partialIsometry_rectDiagonal_iff {m n : ℕ} (d : ℕ → ℂ) :
    IsPartialIsometry (rectDiagonal d : Matrix (Fin m) (Fin n) ℂ) ↔
      ∀ i, i < m → i < n → d i = 0 ∨ ‖d i‖ = 1 := by
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal d
  have hp : D.pinv = (rectDiagonal (fun i => (d i)⁻¹) : Matrix (Fin n) (Fin m) ℂ) := by
    simpa using pinv_eq_of_svd (A := D) (U := 1) (V := 1) (σ := d)
      (one_mem (unitaryGroup (Fin m) ℂ)) (one_mem (unitaryGroup (Fin n) ℂ))
      (by simp [D])
  rw [show rectDiagonal d = D from rfl, isPartialIsometry_iff_adjoint_eq_pinv, hp,
    show Dᴴ = rectDiagonal (star ∘ d) from rectDiagonal_conjTranspose d]
  have hscalar (z : ℂ) : star z = z⁻¹ ↔ z = 0 ∨ ‖z‖ = 1 := by
    by_cases hz : z = 0
    · simp [hz]
    rw [or_iff_right hz, ← mul_eq_one_iff_eq_inv₀ hz, mul_comm]
    change z * (starRingEnd ℂ) z = 1 ↔ ‖z‖ = 1
    rw [Complex.mul_conj']
    constructor
    · intro hs
      have hs' : ‖z‖ ^ 2 = 1 := by exact_mod_cast hs
      nlinarith [norm_nonneg z]
    · intro hs
      simp [hs]
  constructor
  · intro h i hm hn
    have he := congrArg (fun M : Matrix (Fin n) (Fin m) ℂ => M ⟨i, hn⟩ ⟨i, hm⟩) h
    apply (hscalar (d i)).mp
    simpa [rectDiagonal_apply, Function.comp_apply] using he
  · intro h
    apply rectDiagonal_congr
    intro i hn hm
    exact (hscalar (d i)).mpr (h i hm hn)

/-- **Exercise 41** of [benIsrael2003generalized], Chapter 6.
Every positive singular value of a partial isometry is one, and this
condition is sufficient. -/
theorem exercise_6_41 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    IsPartialIsometry A ↔ ∀ i < A.rank, A.sortedSingularValues i = 1 := by
  obtain ⟨U, V, h⟩ := theorem_6_2 A
  let σ := A.sortedSingularValues
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal (fun i => (σ i : ℂ))
  have hA : A = U * D * Vᴴ := h.1.eq_mul_mul_star
  have hD : D = Uᴴ * A * V := by
    symm
    calc
      Uᴴ * A * V = Uᴴ * (U * D * Vᴴ) * V := by rw [hA]
      _ = (Uᴴ * U) * D * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = D := by rw [conjTranspose_mul_self_of_mem_unitaryGroup h.1.mem_unitaryGroup_left,
        conjTranspose_mul_self_of_mem_unitaryGroup h.1.mem_unitaryGroup_right,
        Matrix.one_mul, Matrix.mul_one]
  have hPI : IsPartialIsometry A ↔ IsPartialIsometry D := by
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · rw [hD, ← conjTranspose_conjTranspose V]
      exact exercise_6_40 (conjTranspose_mem_unitaryGroup h.1.mem_unitaryGroup_left)
        (conjTranspose_mem_unitaryGroup h.1.mem_unitaryGroup_right) h'
    · rw [hA]
      exact exercise_6_40 h.1.mem_unitaryGroup_left h.1.mem_unitaryGroup_right h'
  rw [hPI, show D = rectDiagonal (fun i => (σ i : ℂ)) from rfl,
    partialIsometry_rectDiagonal_iff]
  constructor
  · intro h' i hi
    rcases h' i (hi.trans_le A.rank_le_height) (hi.trans_le A.rank_le_width) with hz | ho
    · exact False.elim (not_le_of_gt hi ((A.sortedSingularValues_eq_zero_iff_rank_le i).mp
        (Complex.ofReal_eq_zero.mp hz)))
    · rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (A.sortedSingularValues_nonneg i)] at ho
  · intro h' i _ _
    by_cases hi : i < A.rank
    · right
      simp [σ, h' i hi]
    · left
      exact Complex.ofReal_eq_zero.mpr ((A.sortedSingularValues_eq_zero_iff_rank_le i).mpr (not_lt.mp hi))

/-- **Exercise 41** of [benIsrael2003generalized], Chapter 6.
The nonzero diagonal entries in any complex unitary diagonal
factorization of a partial isometry have unit modulus. -/
theorem exercise_6_41_udv {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {d : ℕ → ℂ}
    (h : IsUDVDecomposition A U d V) (hA : IsPartialIsometry A) :
    ∀ i, d i ≠ 0 → ‖d i‖ = 1 := by
  intro i hi
  rw [h.2.2.2 i]
  refine (exercise_6_41 A).mp hA i (lt_of_not_ge fun hr => hi (norm_eq_zero.mp ?_))
  rw [h.2.2.2 i, (A.sortedSingularValues_eq_zero_iff_rank_le i).mpr hr]

/-- **Exercise 42** of [benIsrael2003generalized], Chapter 6.
A partial isometry takes an orthonormal basis of its initial space to
an orthonormal basis of its range, and this property characterizes it. -/
theorem exercise_6_42 (E : Matrix m n ℂ) :
    let K := (toEuclideanLin Eᴴ).range
    let L := (toEuclideanLin E).range
    IsPartialIsometry E ↔
      ∃ (v : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K)
        (u : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ L),
        ∀ i, toEuclideanLin E (v i : EuclideanSpace ℂ n) = (u i : EuclideanSpace ℂ m) := by
  let T := toEuclideanLin E
  let K := (toEuclideanLin Eᴴ).range
  let L := T.range
  let T₀ : K →ₗ[ℂ] L := T.rangeRestrict.comp K.subtype
  have hK : K = T.kerᗮ := by
    rw [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint]
  have hT₀ (x : K) : (T₀ x : EuclideanSpace ℂ m) = T x := rfl
  change IsPartialIsometry E ↔
    ∃ (v : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K)
      (u : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ L),
      ∀ i, T (v i : EuclideanSpace ℂ n) = (u i : EuclideanSpace ℂ m)
  constructor
  · intro h
    have hnorm (x : K) : ‖T₀ x‖ = ‖x‖ := h _ (hK ▸ x.property)
    let V : K →ₗᵢ[ℂ] L := ⟨T₀, hnorm⟩
    have hs : Function.Surjective V := by
      intro y
      obtain ⟨x, hx⟩ := y.property
      refine ⟨⟨K.starProjection x, K.starProjection_apply_mem x⟩, Subtype.ext ?_⟩
      change T (K.starProjection x) = y.val
      have hz : x - K.starProjection x ∈ T.ker := by
        have horth : Kᗮ = T.ker := by rw [hK, Submodule.orthogonal_orthogonal]
        rw [← horth]
        exact K.sub_starProjection_mem_orthogonal x
      have he := LinearMap.mem_ker.mp hz
      rw [map_sub, sub_eq_zero] at he
      exact he.symm.trans hx
    let v := stdOrthonormalBasis ℂ K
    let e := LinearIsometryEquiv.ofSurjective V hs
    exact ⟨v, v.map e, fun i => by simp [e, V, hT₀]⟩
  · rintro ⟨v, u, huv⟩ x hx
    let e := v.equiv u (Equiv.refl _)
    have he : T₀ = e.toLinearEquiv.toLinearMap := by
      apply v.toBasis.ext
      intro i
      apply Subtype.ext
      change T (v i) = ((e (v i) : L) : EuclideanSpace ℂ m)
      simpa only [e, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply] using huv i
    have hxK : x ∈ K := hK.symm ▸ hx
    have h := e.norm_map ⟨x, hxK⟩
    have happ := LinearMap.congr_fun he ⟨x, hxK⟩
    change T₀ ⟨x, hxK⟩ = e ⟨x, hxK⟩ at happ
    rw [← happ] at h
    exact h

/-- **Exercise 46** of [benIsrael2003generalized], Chapter 6.
The displayed three-dimensional partial isometry has the stated
eigenvectors at zero, one, and the interior eigenvalue √3/2.
The interior eigenvector splits into its initial and kernel components. -/
theorem exercise_6_46 :
    let c := Real.sqrt 3 / 2
    let M : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, (c : ℂ), 0; 0, 1 / 2, 0]
    let e₁ : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![1, 0, 0]
    let e₃ : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, 0, 1]
    let xI : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, (c : ℂ), 0]
    let xN : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, 0, 1 / 2]
    let x : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, (c : ℂ), 1 / 2]
    IsPartialIsometry M ∧ 0 < c ∧ c < 1 ∧ e₁ ≠ 0 ∧ e₃ ≠ 0 ∧ x ≠ 0 ∧
      toEuclideanLin M e₃ = 0 ∧ toEuclideanLin M e₁ = e₁ ∧
      toEuclideanLin M x = (c : ℂ) • x ∧
      e₁ ∈ (toEuclideanLin Mᴴ).range ∧
      x = xI + xN ∧ xI ∈ (toEuclideanLin Mᴴ).range ∧ xN ∈ (toEuclideanLin M).ker := by
  let c := Real.sqrt 3 / 2
  let M : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, (c : ℂ), 0; 0, 1 / 2, 0]
  let e₁ : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![1, 0, 0]
  let e₂ : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, 1, 0]
  let e₃ : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, 0, 1]
  let xI : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, (c : ℂ), 0]
  let xN : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, 0, 1 / 2]
  let x : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, (c : ℂ), 1 / 2]
  let P : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
  have hc : c ^ 2 = 3 / 4 := by
    rw [show c = Real.sqrt 3 / 2 from rfl, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hcPos : 0 < c := by dsimp [c]; positivity
  have hcLt : c < 1 := by nlinarith
  have hcMul : c * c = (3 : ℝ) / 4 := (pow_two c).symm.trans hc
  have hz : (c : ℂ) * (c : ℂ) = 3 / 4 := by
    rw [← Complex.ofReal_mul, hcMul]
    norm_num
  have hP : Mᴴ * M = P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [M, P, Matrix.mul_apply, Fin.sum_univ_succ, hz, map_ofNat]
  have hM : IsPartialIsometry M := by
    apply (isPartialIsometry_iff_reflexive M).mpr
    rw [Matrix.mul_assoc, hP]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [M, P, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨hM, hcPos, hcLt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun u : EuclideanSpace ℂ (Fin 3) => u 0) h
    norm_num [e₁] at h0
  · intro h
    have h0 := congrArg (fun u : EuclideanSpace ℂ (Fin 3) => u 2) h
    norm_num [e₃] at h0
  · intro h
    have h0 := congrArg (fun u : EuclideanSpace ℂ (Fin 3) => u 2) h
    norm_num [x] at h0
  · ext i
    fin_cases i <;> norm_num [M, e₃, toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;> norm_num [M, e₁, toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;> norm_num [M, x, toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      mul_comm]
  · refine ⟨e₁, ?_⟩
    ext i
    fin_cases i <;> norm_num [M, e₁, toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;> norm_num [x, xI, xN]
  · refine ⟨e₂, ?_⟩
    ext i
    fin_cases i <;>
      norm_num [M, e₂, xI, toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, map_ofNat]
  · apply LinearMap.mem_ker.mpr
    ext i
    fin_cases i <;> norm_num [M, xN, toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **Exercise 49** of [benIsrael2003generalized], Chapter 6.
The two-dimensional nilpotent shift is a nonnormal partial isometry
whose eigenvalues are all zero. -/
theorem exercise_6_49 :
    let U : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
    IsPartialIsometry U ∧ ¬ IsStarNormal U ∧
      ∀ (μ : ℂ) (x : EuclideanSpace ℂ (Fin 2)), x ≠ 0 →
        toEuclideanLin U x = μ • x → μ = 0 := by
  let U : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  have hU : U * Uᴴ = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [U, Matrix.mul_apply, Fin.sum_univ_two]
  have hU' : Uᴴ * U = !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [U, Matrix.mul_apply, Fin.sum_univ_two]
  have hSq : U * U = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [U, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨(isPartialIsometry_iff_reflexive U).mpr ?_, ?_, ?_⟩
  · rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [U, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have he : Uᴴ * U = U * Uᴴ := h.star_comm_self
    rw [hU, hU'] at he
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) he
    norm_num at h00
  · intro μ x hx he
    have hzero : toEuclideanLin U (toEuclideanLin U x) = 0 := by
      rw [← toEuclideanLin_mul_apply, hSq, map_zero, LinearMap.zero_apply]
    rw [he, map_smul, he, smul_smul, smul_eq_zero] at hzero
    exact (mul_eq_zero.mp (hzero.resolve_right hx)).elim id id

private theorem range_toEuclideanLin_eq_range_conjTranspose_of_normal {A : Matrix n n ℂ}
    (hA : IsStarNormal A) : (toEuclideanLin A).range = (toEuclideanLin Aᴴ).range := by
  let F := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  let T := F A
  have hn : IsStarNormal T := by
    refine ⟨?_⟩
    change star (F A) * F A = F A * star (F A)
    rw [← map_star, ← map_mul, ← map_mul, hA.star_comm_self]
  have hk := ContinuousLinearMap.IsStarNormal.orthogonal_range hn
  change (toEuclideanLin A).rangeᗮ = (toEuclideanLin A).ker at hk
  have hker : (toEuclideanLin A).kerᗮ = (toEuclideanLin Aᴴ).range := by
    rw [LinearMap.orthogonal_ker, toEuclideanLin_conjTranspose_eq_adjoint]
  rw [← hker, ← hk, Submodule.orthogonal_orthogonal]

open scoped MatrixOrder in
/-- **Exercise 52** of [benIsrael2003generalized], Chapter 6.
A square matrix is normal exactly when its range-supported positive
left polar factor commutes with its partial isometry. In that case
the partial isometry is normal as well. -/
theorem exercise_6_52 {A E G : Matrix n n ℂ} (hE : IsPartialIsometry E)
    (hG : G.PosSemidef) (hA : A = G * E)
    (hr : (toEuclideanLin E).range = (toEuclideanLin G).range) :
    IsStarNormal A ↔ G * E = E * G ∧ IsStarNormal E := by
  obtain ⟨hSq, hRec⟩ := supported_left_polar hE hG.isHermitian hA hr
  have hHerm := hG.isHermitian.eq
  have hP := final_gram_of_partialIsometry hE
  have hPG : (E * Eᴴ) * G = G := by
    apply toEuclideanLin.injective
    rw [hP, hr, toEuclideanLin_mul, toEuclideanLin_orthogonalProjector]
    ext1 x
    change (toEuclideanLin G).range.starProjection (toEuclideanLin G x) = toEuclideanLin G x
    exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ _)
  have hGP : G * (E * Eᴴ) = G := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hHerm] using
      congrArg Matrix.conjTranspose hPG
  have hAE : (toEuclideanLin A).range = (toEuclideanLin E).range := by
    rw [hr]
    refine le_antisymm ?_ ?_
    · rw [hA, toEuclideanLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · have hGE : G = A * Eᴴ := by rw [hA, Matrix.mul_assoc, hGP]
      conv_lhs => rw [hGE, toEuclideanLin_mul]
      exact LinearMap.range_comp_le_range _ _
  have hAE' : (toEuclideanLin Aᴴ).range = (toEuclideanLin Eᴴ).range := by
    refine le_antisymm ?_ ?_
    · rw [hA, conjTranspose_mul, toEuclideanLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · rw [hRec, conjTranspose_mul, toEuclideanLin_mul]
      exact LinearMap.range_comp_le_range _ _
  constructor
  · intro hn
    have hC : Commute (A * Aᴴ) A := by
      change (A * Aᴴ) * A = A * (A * Aᴴ)
      rw [Matrix.mul_assoc, show Aᴴ * A = A * Aᴴ from hn.star_comm_self]
    have hGA : Commute G A := by
      have hg : G = CFC.sqrt (A * Aᴴ) := by rw [hSq, CFC.sqrt_mul_self _ hG.nonneg]
      rw [hg]
      exact hC.cfcₙ_nnreal NNReal.sqrt
    have hInv : Commute G G.pinv := by
      change G * G.pinv = G.pinv * G
      apply toEuclideanLin.injective
      rw [G.mul_pinv_eq_starProjection, G.pinv_mul_eq_starProjection, hHerm]
    refine ⟨?_, (exercise_6_47 hE).mpr ?_⟩
    · rw [hRec]
      exact (hInv.mul_right hGA).eq
    · rw [← hAE, ← hAE']
      exact range_toEuclideanLin_eq_range_conjTranspose_of_normal hn
  · rintro ⟨hc, hn⟩
    have hh : G * (G * E) = E * (G * G) := calc
      _ = G * (E * G) := by rw [hc]
      _ = _ := by rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    refine ⟨?_⟩
    change Aᴴ * A = A * Aᴴ
    rw [hSq]
    calc
      Aᴴ * A = (Eᴴ * G) * (G * E) := by rw [hA, conjTranspose_mul, hHerm]
      _ = Eᴴ * (G * (G * E)) := Matrix.mul_assoc _ _ _
      _ = (Eᴴ * E) * (G * G) := by rw [hh, Matrix.mul_assoc]
      _ = (E * Eᴴ) * (G * G) := by rw [show Eᴴ * E = E * Eᴴ from hn.star_comm_self]
      _ = G * G := by rw [← Matrix.mul_assoc, hPG]

/-- **Exercise 52** of [benIsrael2003generalized], Chapter 6.
Commutation of the supported polar factors alone is sufficient for
normality. -/
theorem exercise_6_52_commute {A E G : Matrix n n ℂ} (hE : IsPartialIsometry E)
    (hG : G.PosSemidef) (hA : A = G * E)
    (hr : (toEuclideanLin E).range = (toEuclideanLin G).range) :
    IsStarNormal A ↔ G * E = E * G := by
  have h := exercise_6_52 hE hG hA hr
  refine ⟨fun hn => (h.mp hn).1, fun hc => h.mpr ⟨hc, (exercise_6_47 hE).mpr ?_⟩⟩
  have hG' : G * Eᴴ = Eᴴ * G := by
    have he := congrArg Matrix.conjTranspose hc
    simpa only [conjTranspose_mul, hG.isHermitian.eq, conjTranspose_conjTranspose] using he.symm
  have hle : (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin E).range := by
    rw [hr]
    have hrel : Eᴴ = Eᴴ * G * G.pinv := by
      have hh : G * G.pinv = E * Eᴴ := by
        apply toEuclideanLin.injective
        rw [G.mul_pinv_eq_starProjection, final_gram_of_partialIsometry hE, hr,
          toEuclideanLin_orthogonalProjector]
      rw [Matrix.mul_assoc, hh, ← Matrix.mul_assoc, (theorem_6_5 E).2.2.2.2.1.mp hE]
    have hrel' : Eᴴ = G * (Eᴴ * G.pinv) := by
      calc
        Eᴴ = Eᴴ * G * G.pinv := hrel
        _ = G * (Eᴴ * G.pinv) := by rw [← hG', Matrix.mul_assoc]
    conv_lhs => rw [hrel', toEuclideanLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hd (D : Matrix n n ℂ) :
      D.rank = Module.finrank ℂ (toEuclideanLin D).range := by
    rw [toEuclideanLin_eq_toLin_orthonormal]
    exact rank_eq_finrank_range_toLin _ _ _
  symm
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [← hd, ← hd, rank_conjTranspose])

/-- The scalar case of **Exercise 55** of [benIsrael2003generalized],
Chapter 6. Distance from a complex number to a point on the unit
circle is smallest at its phase and largest at the opposite phase. -/
theorem exercise_6_55_scalar (z : ℂ) (α : ℝ) :
    let u := Complex.exp ((z.arg : ℂ) * Complex.I)
    let v := Complex.exp ((α : ℂ) * Complex.I)
    ‖z - u‖ ≤ ‖z - v‖ ∧ ‖z - v‖ ≤ ‖z + u‖ := by
  let u := Complex.exp ((z.arg : ℂ) * Complex.I)
  let v := Complex.exp ((α : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hv : ‖v‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hz : z = (‖z‖ : ℂ) * u := (polar_complex_scalar z).1
  have hsub : ‖z - u‖ = |‖z‖ - 1| := calc
    _ = ‖((‖z‖ : ℂ) - 1) * u‖ := congrArg norm (by rw [sub_mul, one_mul]; exact congrArg (· - u) hz)
    _ = _ := by rw [norm_mul, hu, mul_one, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  have hadd : ‖z + u‖ = ‖z‖ + 1 := calc
    _ = ‖((‖z‖ : ℂ) + 1) * u‖ := congrArg norm (by rw [add_mul, one_mul]; exact congrArg (· + u) hz)
    _ = _ := by rw [norm_mul, hu, mul_one, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine ⟨?_, ?_⟩
  · rw [hsub, ← hv]
    exact abs_norm_sub_norm_le z v
  · rw [hadd, ← hv, sub_eq_add_neg]
    simpa only [norm_neg] using norm_add_le z (-v)

/-- **Exercise 60** of [benIsrael2003generalized], Chapter 6, Equations
(100)–(101). The largest real trace is the sum of singular values. A
maximal-rank partial isometry attains it with a positive product. -/
theorem exercise_6_60 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    let k := min m n
    let s := ∑ i ∈ Finset.range k, A.sortedSingularValues i
    IsGreatest {t : ℝ | ∃ W : Matrix (Fin n) (Fin m) ℂ,
      IsPartialIsometry W ∧ W.rank = k ∧ (trace (A * W)).re = t} s ∧
      ∃ W : Matrix (Fin n) (Fin m) ℂ, IsPartialIsometry W ∧ W.rank = k ∧
        (A * W).PosSemidef ∧ trace (A * W) = (s : ℂ) := by
  let k := min m n
  let s := ∑ i ∈ Finset.range k, A.sortedSingularValues i
  obtain ⟨U, V, h⟩ := theorem_6_2 A
  let Uk := U.submatrix id (Fin.castLE (min_le_left m n))
  let Vk := V.submatrix id (Fin.castLE (min_le_right m n))
  let D := diagonal (fun i : Fin k => (A.sortedSingularValues i : ℂ))
  let E := Uk * Vkᴴ
  let G := Uk * D * Ukᴴ
  obtain ⟨hE, hr, hG, -, hA, -⟩ :=
    polar_factors_of_larger_truncation h (le_min A.rank_le_height A.rank_le_width)
      (min_le_left m n) (min_le_right m n)
  have hU : Ukᴴ * Uk = 1 :=
    conjTranspose_submatrix_castLE_mul_self _ h.1.mem_unitaryGroup_left
  have hV : Vkᴴ * Vk = 1 :=
    conjTranspose_submatrix_castLE_mul_self _ h.1.mem_unitaryGroup_right
  have hW : IsPartialIsometry Eᴴ := (theorem_6_5 E).1.mp hE
  have hrW : Eᴴ.rank = k := (rank_conjTranspose E).trans hr
  have hAW : A * Eᴴ = G := by
    rw [hA]
    change (Uk * D * Ukᴴ) * (Uk * Vkᴴ) * (Uk * Vkᴴ)ᴴ = Uk * D * Ukᴴ
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc
      _ = Uk * D * (Ukᴴ * Uk) * (Vkᴴ * Vk) * Ukᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, hV, Matrix.mul_one, Matrix.mul_one]
  have ht : trace (A * Eᴴ) = (s : ℂ) := by
    rw [hAW]
    change trace (Uk * D * Ukᴴ) = (s : ℂ)
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    simp only [D, s, trace_diagonal, Complex.ofReal_sum]
    exact Fin.sum_univ_eq_sum_range (fun i : ℕ => (A.sortedSingularValues i : ℂ)) k
  refine ⟨⟨⟨Eᴴ, hW, hrW, by rw [ht, Complex.ofReal_re]⟩, ?_⟩,
    ⟨Eᴴ, hW, hrW, hAW ▸ hG, ht⟩⟩
  rintro t ⟨W, hW', hr', rfl⟩
  have hb := re_trace_mul_le_sum_sortedSingularValues_mul A W
  rw [Fintype.card_fin, Fintype.card_fin] at hb
  refine hb.trans_eq (Finset.sum_congr rfl (fun i hi => ?_))
  rw [(exercise_6_41 W).mp hW' i (hr'.symm ▸ Finset.mem_range.mp hi), mul_one]

private theorem trace_mul_rectDiagonal_eq {m n : ℕ} (σ τ : ℕ → ℝ) :
    trace ((rectDiagonal (fun i => (σ i : ℂ)) : Matrix (Fin m) (Fin n) ℂ) *
      (rectDiagonal (fun i => (τ i : ℂ)) : Matrix (Fin n) (Fin m) ℂ)) =
        (∑ i ∈ Finset.range (min m n), σ i * τ i : ℝ) := by
  rw [rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal, trace_diagonal]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < n then (σ i : ℂ) * (τ i : ℂ) else 0)]
  have hsum : (Finset.range m).filter (fun i => i < n) = Finset.range (min m n) := by
    ext i
    simp [lt_min_iff]
  rw [← Finset.sum_filter, hsum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => (Complex.ofReal_mul (σ i) (τ i)).symm)

/-- **Exercise 61** of [benIsrael2003generalized], Chapter 6. The maximum
real trace over two unitary factors equals the sum of the products of
matching singular values. The maximizing trace itself is real. -/
theorem exercise_6_61 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ) :
    let s := ∑ i ∈ Finset.range (min m n), A.sortedSingularValues i * B.sortedSingularValues i
    IsGreatest {t : ℝ | ∃ (X : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin m) (Fin m) ℂ),
      X ∈ unitaryGroup (Fin n) ℂ ∧ W ∈ unitaryGroup (Fin m) ℂ ∧
        (trace (A * X * B * W)).re = t} s ∧
      ∃ (X : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin m) (Fin m) ℂ),
        X ∈ unitaryGroup (Fin n) ℂ ∧ W ∈ unitaryGroup (Fin m) ℂ ∧
          trace (A * X * B * W) = (s : ℂ) := by
  let s := ∑ i ∈ Finset.range (min m n), A.sortedSingularValues i * B.sortedSingularValues i
  obtain ⟨U, V, hA⟩ := theorem_6_2 A
  obtain ⟨P, Q, hB⟩ := theorem_6_2 B
  let X := V * Pᴴ
  let W := Q * Uᴴ
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal (fun i => (A.sortedSingularValues i : ℂ))
  let F : Matrix (Fin n) (Fin m) ℂ := rectDiagonal (fun i => (B.sortedSingularValues i : ℂ))
  have hX : X ∈ unitaryGroup (Fin n) ℂ :=
    mul_mem hA.1.mem_unitaryGroup_right (conjTranspose_mem_unitaryGroup hB.1.mem_unitaryGroup_left)
  have hW : W ∈ unitaryGroup (Fin m) ℂ :=
    mul_mem hB.1.mem_unitaryGroup_right (conjTranspose_mem_unitaryGroup hA.1.mem_unitaryGroup_left)
  have hAX : A * X = U * D * Pᴴ := by
    change A * (V * Pᴴ) = U * D * Pᴴ
    rw [show A = U * D * Vᴴ from hA.1.eq_mul_mul_star]
    calc
      _ = U * D * (Vᴴ * V) * Pᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [conjTranspose_mul_self_of_mem_unitaryGroup hA.1.mem_unitaryGroup_right,
        Matrix.mul_one]
  have hBW : B * W = P * F * Uᴴ := by
    change B * (Q * Uᴴ) = P * F * Uᴴ
    rw [show B = P * F * Qᴴ from hB.1.eq_mul_mul_star]
    calc
      _ = P * F * (Qᴴ * Q) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [conjTranspose_mul_self_of_mem_unitaryGroup hB.1.mem_unitaryGroup_right,
        Matrix.mul_one]
  have hprod : A * X * B * W = U * (D * F) * Uᴴ := by
    rw [Matrix.mul_assoc (A * X) B W, hAX, hBW]
    calc
      _ = U * D * (Pᴴ * P) * F * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [conjTranspose_mul_self_of_mem_unitaryGroup hB.1.mem_unitaryGroup_left,
        Matrix.mul_one, Matrix.mul_assoc U D F]
  have ht : trace (A * X * B * W) = (s : ℂ) := by
    rw [hprod, trace_mul_comm, ← Matrix.mul_assoc,
      conjTranspose_mul_self_of_mem_unitaryGroup hA.1.mem_unitaryGroup_left, Matrix.one_mul]
    exact trace_mul_rectDiagonal_eq _ _
  refine ⟨⟨⟨X, W, hX, hW, by rw [ht, Complex.ofReal_re]⟩, ?_⟩, ⟨X, W, hX, hW, ht⟩⟩
  rintro t ⟨X', W', hX', hW', rfl⟩
  simpa only [Fintype.card_fin] using exercise_6_61_upper (A := A) (B := B) hX' hW'

end Exercises

end BenIsraelGreville.Chapter06
