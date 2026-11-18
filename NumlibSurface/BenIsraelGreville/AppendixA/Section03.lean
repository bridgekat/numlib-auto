/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.AppendixA.Section02
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The general reciprocal in General Analysis

Appendix A, §3 of [benIsrael2003generalized] constructs the general
reciprocal through orthogonal projections and a maximal nonsingular minor.
The uniqueness assertion in (29.2)(1) uses the range condition in (29.2)(3).
The domain and codomain in (29.1)(12), and the two subvector indices in
(29.45)(2), are written in their dimensionally consistent order. The
row Gram inverse in the second expression of (29.1)(11) acts on the
selected-row index space.
-/

noncomputable section

namespace BenIsraelGreville.AppendixA

open Matrix
open scoped ComplexOrder

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- Moore's generalized identity matrix of a subspace, represented in the
ambient Euclidean coordinates. -/
def generalizedIdentityMatrix (M : Submodule ℂ (EuclideanSpace ℂ n)) : Matrix n n ℂ :=
  (toEuclideanLin : Matrix n n ℂ ≃ₗ[ℂ] _).symm M.starProjection.toLinearMap

@[simp]
theorem generalizedIdentityMatrix_toEuclideanLin (M : Submodule ℂ (EuclideanSpace ℂ n)) :
    toEuclideanLin (generalizedIdentityMatrix M) = M.starProjection.toLinearMap :=
  LinearEquiv.apply_symm_apply _ _

/-- The left reciprocal product is Moore's generalized identity on the
column space of the matrix. -/
theorem mul_pinv_eq_generalizedIdentity (A : Matrix m n ℂ) :
    A * A.pinv = generalizedIdentityMatrix (columnSpace A) :=
  toEuclideanLin.injective <| by
    rw [generalizedIdentityMatrix_toEuclideanLin, A.mul_pinv_eq_starProjection]

/-- The right reciprocal product is Moore's generalized identity on the
column space of the adjoint. -/
theorem pinv_mul_eq_generalizedIdentity (A : Matrix m n ℂ) :
    A.pinv * A = generalizedIdentityMatrix (columnSpace Aᴴ) :=
  toEuclideanLin.injective <| by
    rw [generalizedIdentityMatrix_toEuclideanLin, A.pinv_mul_eq_starProjection]

/-- **Theorem (29.2)(2)–(5)** of [benIsrael2003generalized], Appendix A.
The generalized identity is Hermitian, positive semidefinite, and idempotent,
with the stated range, orthogonal residual, and kernel. -/
theorem theorem_29_2 (M : Submodule ℂ (EuclideanSpace ℂ n)) :
    let P := generalizedIdentityMatrix M
    P.IsHermitian ∧ P.PosSemidef ∧ P * P = P ∧ columnSpace P = M ∧
      (∀ x, toEuclideanLin P x ∈ M ∧ x - toEuclideanLin P x ∈ Mᗮ) ∧
      ∀ x, x ∈ Mᗮ ↔ toEuclideanLin P x = 0 := by
  let P := generalizedIdentityMatrix M
  have hHerm : P.IsHermitian := by
    apply (toEuclideanLin : Matrix n n ℂ ≃ₗ[ℂ] _).injective
    rw [toEuclideanLin_conjTranspose_eq_adjoint, generalizedIdentityMatrix_toEuclideanLin]
    exact congrArg ContinuousLinearMap.toLinearMap (isSelfAdjoint_starProjection M).star_eq
  have hIdem : P * P = P := by
    apply (toEuclideanLin : Matrix n n ℂ ≃ₗ[ℂ] _).injective
    ext1 x
    rw [toEuclideanLin_mul_apply, generalizedIdentityMatrix_toEuclideanLin]
    exact M.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem x)
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self P
  rw [hHerm.eq, hIdem] at hPSD
  refine ⟨hHerm, hPSD, hIdem, ?_, ?_, ?_⟩
  · rw [columnSpace, generalizedIdentityMatrix_toEuclideanLin]
    exact M.range_starProjection
  · intro x
    rw [generalizedIdentityMatrix_toEuclideanLin]
    exact ⟨M.starProjection_apply_mem x, M.sub_starProjection_mem_orthogonal x⟩
  · intro x
    rw [generalizedIdentityMatrix_toEuclideanLin]
    exact M.starProjection_apply_eq_zero_iff.symm

/-- **Theorem (29.2)(6)** of [benIsrael2003generalized], Appendix A.
Either adjoint-range support or annihilation of the orthogonal complement,
together with fixing the subspace, characterizes the generalized identity. -/
theorem theorem_29_2_characterization (M : Submodule ℂ (EuclideanSpace ℂ n))
    (B : Matrix n n ℂ) :
    (B = generalizedIdentityMatrix M ↔
      (∀ x ∈ M, toEuclideanLin B x = x) ∧ columnSpace Bᴴ ≤ M) ∧
    (B = generalizedIdentityMatrix M ↔
      (∀ x ∈ M, toEuclideanLin B x = x) ∧
        ∀ x ∈ Mᗮ, toEuclideanLin B x = 0) := by
  have hzero (x : EuclideanSpace ℂ n) : x ∈ (columnSpace Bᴴ)ᗮ ↔ toEuclideanLin B x = 0 := by
    rw [columnSpace, LinearMap.orthogonal_range, ← toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_conjTranspose, LinearMap.mem_ker]
  have hsupport : columnSpace Bᴴ ≤ M ↔ ∀ x ∈ Mᗮ, toEuclideanLin B x = 0 := by
    constructor
    · intro h x hx
      exact (hzero x).mp (Submodule.orthogonal_le h hx)
    · intro h
      have horth : Mᗮ ≤ (columnSpace Bᴴ)ᗮ := fun x hx => (hzero x).mpr (h x hx)
      simpa only [Submodule.orthogonal_orthogonal] using Submodule.orthogonal_le horth
  have heq : B = generalizedIdentityMatrix M ↔
      (∀ x ∈ M, toEuclideanLin B x = x) ∧ ∀ x ∈ Mᗮ, toEuclideanLin B x = 0 := by
    constructor
    · rintro rfl
      rw [generalizedIdentityMatrix_toEuclideanLin]
      exact ⟨fun _ hx => M.starProjection_eq_self_iff.mpr hx,
        fun _ hx => M.starProjection_apply_eq_zero_iff.mpr hx⟩
    · rintro ⟨hfix, hkill⟩
      apply (toEuclideanLin : Matrix n n ℂ ≃ₗ[ℂ] _).injective
      ext1 x
      rw [generalizedIdentityMatrix_toEuclideanLin]
      have hx := hkill (x - M.starProjection x) (M.sub_starProjection_mem_orthogonal x)
      rw [map_sub, hfix _ (M.starProjection_apply_mem x), sub_eq_zero] at hx
      exact hx
  exact ⟨heq.trans (and_congr_right fun _ => hsupport.symm), heq⟩

/-- **Theorem (29.2)(1)** of [benIsrael2003generalized], Appendix A.
The unique generalized identity with image in the given subspace fixes its
vectors and their conjugate rows. The image condition is needed for uniqueness. -/
theorem theorem_29_2_existsUnique (M : Submodule ℂ (EuclideanSpace ℂ n)) :
    ∃! B : Matrix n n ℂ, columnSpace B ≤ M ∧
      (∀ x ∈ M, toEuclideanLin B x = x) ∧ (∀ x ∈ M, toEuclideanLin Bᴴ x = x) := by
  let P := generalizedIdentityMatrix M
  have hP := theorem_29_2 M
  have hfix := ((theorem_29_2_characterization M P).2.mp rfl).1
  refine ⟨P, ⟨hP.2.2.2.1.le, hfix, fun x hx => ?_⟩, ?_⟩
  · rw [hP.1.eq]
    exact hfix x hx
  · rintro B ⟨hR, hB, hB'⟩
    have h := (theorem_29_2_characterization M Bᴴ).1.mpr
      ⟨hB', by simpa only [conjTranspose_conjTranspose] using hR⟩
    simpa only [conjTranspose_conjTranspose, hP.1.eq] using congrArg Matrix.conjTranspose h

/-- **Theorem (29.5)(a)–(c)** of [benIsrael2003generalized], Appendix A.
The two historical characterizations of the reciprocal agree. -/
theorem theorem_29_5 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    (X = A.pinv ↔ columnSpace X ≤ columnSpace Aᴴ ∧
      A * X = generalizedIdentityMatrix (columnSpace A)) ∧
    (X = A.pinv ↔ IsMooreReciprocal A X) := by
  refine ⟨⟨?_, ?_⟩, isMooreReciprocal_iff.symm⟩
  · rintro rfl
    exact ⟨(columnSpace_pinv A).le, mul_pinv_eq_generalizedIdentity A⟩
  · rintro ⟨hX, hAX⟩
    calc
      X = A.pinv * (A * X) := by rw [← Matrix.mul_assoc, pinv_mul_mul_eq_of_columnSpace_le hX]
      _ = A.pinv := by
        rw [hAX, ← mul_pinv_eq_generalizedIdentity, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]

/-- **Theorem (29.3)** of [benIsrael2003generalized], Appendix A.
The reciprocal on the column spaces extends by zero on their input
orthogonal complement, giving a unique matrix with the two projector identities
and the prescribed output space. -/
theorem theorem_29_3 (A : Matrix m n ℂ) :
    ∃! X : Matrix n m ℂ, columnSpace X ≤ columnSpace Aᴴ ∧
      A * X = generalizedIdentityMatrix (columnSpace A) ∧
      X * A = generalizedIdentityMatrix (columnSpace Aᴴ) := by
  refine ⟨A.pinv, ⟨(columnSpace_pinv A).le, mul_pinv_eq_generalizedIdentity A,
    pinv_mul_eq_generalizedIdentity A⟩, ?_⟩
  rintro X ⟨hX, hAX, _⟩
  exact (theorem_29_5 A X).1.mpr ⟨hX, hAX⟩

/-- **Theorem (29.4)(1)–(4)** of [benIsrael2003generalized], Appendix A.
The general reciprocal has the stated reflexive, rank, range, adjoint, and
involution properties. -/
theorem theorem_29_4 (A : Matrix m n ℂ) :
    A.pinv * A * A.pinv = A.pinv ∧ A * A.pinv * A = A ∧ A.rank = A.pinv.rank ∧
      columnSpace A = columnSpace A.pinvᴴ ∧ columnSpace Aᴴ = columnSpace A.pinv ∧
      A.pinvᴴ = Aᴴ.pinv ∧ A = A.pinv.pinv := by
  have hRank := (Matrix.IsInnerInverse.isOuterInverse_iff_rank_eq A.mul_pinv_mul_self).mp
    A.pinv_mul_self_mul_pinv
  exact ⟨A.pinv_mul_self_mul_pinv, A.mul_pinv_mul_self, hRank.symm,
    (columnSpace_pinv_conjTranspose A).symm, (columnSpace_pinv A).symm,
    A.pinv_conjTranspose.symm, (isMooreReciprocal_iff.mp
      (IsMooreReciprocal.mutual (isMooreReciprocal_iff.mpr rfl : IsMooreReciprocal A A.pinv)).1)⟩

omit [DecidableEq m] in
/-- **Corollary (29.55)** of [benIsrael2003generalized], Appendix A.
Taking the general reciprocal commutes with a two-block diagonal sum. -/
theorem corollary_29_55 {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (B : Matrix m n ℂ) (C : Matrix p q ℂ) :
    (fromBlocks B 0 0 C).pinv = fromBlocks B.pinv 0 0 C.pinv := by
  classical
  symm
  apply (fromBlocks B 0 0 C).pinv_unique
  · simp [fromBlocks_multiply, B.mul_pinv_mul_self, C.mul_pinv_mul_self]
  · simp [fromBlocks_multiply, B.pinv_mul_self_mul_pinv, C.pinv_mul_self_mul_pinv]
  · simp [fromBlocks_multiply, IsHermitian, fromBlocks_conjTranspose,
      B.isHermitian_mul_pinv.eq, C.isHermitian_mul_pinv.eq]
  · simp [fromBlocks_multiply, IsHermitian, fromBlocks_conjTranspose,
      B.isHermitian_pinv_mul.eq, C.isHermitian_pinv_mul.eq]

/-- **Theorem (29.6)(1)–(2)** of [benIsrael2003generalized], Appendix A.
The general reciprocal preserves Hermitian and positive semidefinite matrices. -/
theorem theorem_29_6 (A : Matrix n n ℂ) :
    (A.IsHermitian → A.pinv.IsHermitian) ∧ (A.PosSemidef → A.pinv.PosSemidef) := by
  have hHerm (h : A.IsHermitian) : A.pinv.IsHermitian := by
    rw [IsHermitian, ← A.pinv_conjTranspose, h.eq]
  refine ⟨hHerm, fun hA => ?_⟩
  have h := hA.conjTranspose_mul_mul_same A.pinv
  rwa [(hHerm hA.isHermitian).eq, A.pinv_mul_self_mul_pinv] at h

/-- The null space is the orthogonal complement of the adjoint column space. -/
theorem orthogonal_columnSpace_conjTranspose (A : Matrix m n ℂ) :
    (columnSpace Aᴴ)ᗮ = (toEuclideanLin A).ker := by
  rw [columnSpace, LinearMap.orthogonal_range, ← toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_conjTranspose]

/-- **Theorem (29.8)(a)–(d)** of [benIsrael2003generalized], Appendix A.
For a positive semidefinite matrix, its quadratic form vanishes exactly
when the form of its reciprocal vanishes, or when the vector is orthogonal
to either column space. -/
theorem theorem_29_8 (A : Matrix n n ℂ) (hA : A.PosSemidef) (x : EuclideanSpace ℂ n) :
    (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x) = 0 ↔ x ∈ (columnSpace A)ᗮ) ∧
    (x ∈ (columnSpace A)ᗮ ↔ x ∈ (columnSpace A.pinv)ᗮ) ∧
    (x ∈ (columnSpace A.pinv)ᗮ ↔ star (WithLp.ofLp x) ⬝ᵥ (A.pinv *ᵥ WithLp.ofLp x) = 0) := by
  have hzero {B : Matrix n n ℂ} (hB : B.PosSemidef) :
      star (WithLp.ofLp x) ⬝ᵥ (B *ᵥ WithLp.ofLp x) = 0 ↔ x ∈ (columnSpace B)ᗮ := by
    rw [hB.dotProduct_mulVec_zero_iff,
      ← show Bᴴ = B from hB.isHermitian.eq, orthogonal_columnSpace_conjTranspose, LinearMap.mem_ker]
    simp only [hB.isHermitian.eq, toEuclideanLin_apply, WithLp.toLp_eq_zero]
  exact ⟨hzero hA, by rw [columnSpace_pinv, hA.isHermitian.eq],
    (hzero ((theorem_29_6 A).2 hA)).symm⟩

/-- **Theorem (29.9)** of [benIsrael2003generalized], Appendix A.
For consistent forcing, the reciprocal supplies a particular solution and
every other solution differs from it by a vector orthogonal to the adjoint
column space. -/
theorem theorem_29_9 (A : Matrix m n ℂ) {b : EuclideanSpace ℂ m} (hb : b ∈ columnSpace A)
    (x : EuclideanSpace ℂ n) :
    toEuclideanLin A x = b ↔ ∃ y ∈ (columnSpace Aᴴ)ᗮ, x = toEuclideanLin A.pinv b + y := by
  have hp : toEuclideanLin A (toEuclideanLin A.pinv b) = b := by
    rw [← toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection]
    exact (columnSpace A).starProjection_eq_self_iff.mpr hb
  simp only [orthogonal_columnSpace_conjTranspose, LinearMap.mem_ker]
  constructor
  · intro hx
    exact ⟨x - toEuclideanLin A.pinv b, by rw [map_sub, hx, hp, sub_self], by abel⟩
  · rintro ⟨y, hy, rfl⟩
    rw [map_add, hp, hy, add_zero]

section Submatrix

/-- The rows of the identity selected by the given indices. -/
def rowSelectionMatrix (I : k → m) : Matrix k m ℂ :=
  (1 : Matrix m m ℂ).submatrix I id

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
@[simp]
theorem rowSelectionMatrix_mul (I : k → m) (A : Matrix m n ℂ) :
    rowSelectionMatrix I * A = A.submatrix I id := by
  simpa only [rowSelectionMatrix, Function.id_comp, Equiv.refl_symm, Equiv.coe_refl] using
    Matrix.one_submatrix_mul I (Equiv.refl m) A

omit [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k] in
@[simp]
theorem mul_rowSelectionMatrix_conjTranspose (A : Matrix m n ℂ) (J : k → n) :
    A * (rowSelectionMatrix J)ᴴ = A.submatrix id J := by
  have h : (rowSelectionMatrix J)ᴴ = (1 : Matrix n n ℂ).submatrix id J := by
    ext i j
    simp only [rowSelectionMatrix, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
      id_eq, Matrix.one_apply]
    by_cases hij : i = J j <;> simp [hij, eq_comm]
  rw [h]
  simpa only [rowSelectionMatrix, Function.id_comp, Equiv.refl_symm, Equiv.coe_refl] using
    Matrix.mul_submatrix_one (Equiv.refl n) J A

/-- The nonsingular minor is maximal precisely when its order equals the
rank of the original matrix. The empty minor is permitted for rank zero. -/
structure IsMaximalNonsingularMinor (A : Matrix m n ℂ) (I : k ↪ m) (J : k ↪ n) : Prop where
  card_eq_rank : Fintype.card k = A.rank
  isUnit : IsUnit (A.submatrix I J)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Every matrix has a nonsingular minor of order equal to its rank. -/
theorem exists_maximalNonsingularMinor [Finite m] (A : Matrix m n ℂ) :
    ∃ (I : Fin A.rank ↪ m) (J : Fin A.rank ↪ n), IsMaximalNonsingularMinor A I J := by
  let _ : Fintype m := Fintype.ofFinite m
  obtain ⟨i, j, h⟩ := A.exists_det_submatrix_ne_zero
  exact ⟨⟨i, A.injective_of_det_submatrix_ne_zero_left h⟩,
    ⟨j, A.injective_of_det_submatrix_ne_zero_right h⟩, Fintype.card_fin _,
    (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)⟩

omit [Fintype k] [DecidableEq k] in
/-- Selecting the rows of the pivot columns or the columns of the pivot rows
gives the same square minor. -/
private theorem pivot_eq_selections (A : Matrix m n ℂ) (I : k ↪ m) (J : k ↪ n) :
    rowSelectionMatrix I * A.submatrix id J = A.submatrix I J ∧
      A.submatrix I id * (rowSelectionMatrix J)ᴴ = A.submatrix I J := by
  simp only [rowSelectionMatrix_mul, mul_rowSelectionMatrix_conjTranspose, submatrix_submatrix,
    Function.id_comp, Function.comp_id, and_self]

/-- The selected rows and columns through a maximal nonsingular minor have
full rank and span the two column spaces used by the reciprocal. -/
theorem IsMaximalNonsingularMinor.rank_and_columnSpace {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    let F := A.submatrix id J
    let G := A.submatrix I id
    F.rank = Fintype.card k ∧ G.rank = Fintype.card k ∧
      columnSpace F = columnSpace A ∧ columnSpace Gᴴ = columnSpace Aᴴ := by
  let F := A.submatrix id J
  let G := A.submatrix I id
  obtain ⟨hSF, hGS⟩ := pivot_eq_selections A I J
  have hH := rank_of_isUnit _ h.isUnit
  have hF : F.rank = Fintype.card k := by
    refine le_antisymm (rank_le_card_width F) ?_
    rw [← hH, ← hSF]
    exact rank_mul_le_right _ _
  have hG : G.rank = Fintype.card k := by
    refine le_antisymm (rank_le_card_height G) ?_
    rw [← hH, ← hGS]
    exact rank_mul_le_left _ _
  refine ⟨hF, hG, ?_, ?_⟩
  · apply Submodule.eq_of_le_of_finrank_eq
    · rw [← mul_rowSelectionMatrix_conjTranspose]
      exact columnSpace_mul_le _ _
    · rw [finrank_range_toEuclideanLin, finrank_range_toEuclideanLin]
      exact hF.trans h.card_eq_rank
  · apply Submodule.eq_of_le_of_finrank_eq
    · rw [← rowSelectionMatrix_mul, conjTranspose_mul]
      exact columnSpace_mul_le _ _
    · rw [finrank_range_toEuclideanLin, finrank_range_toEuclideanLin,
        rank_conjTranspose, rank_conjTranspose]
      exact hG.trans h.card_eq_rank

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- A maximal nonsingular minor (H) gives the exact factorization
(A=FH^{-1}G), where (F) and (G) are its full columns and rows. -/
theorem IsMaximalNonsingularMinor.factorization [Finite m] {A : Matrix m n ℂ}
    {I : k ↪ m} {J : k ↪ n} (h : IsMaximalNonsingularMinor A I J) :
    A = A.submatrix id J * (A.submatrix I J)⁻¹ * A.submatrix I id := by
  classical
  let _ : Fintype m := Fintype.ofFinite m
  let F := A.submatrix id J
  let H := A.submatrix I J
  let S := rowSelectionMatrix I
  have hSF : S * F = H := (pivot_eq_selections A I J).1
  have hfix : F * H⁻¹ * S * F = F := by
    rw [Matrix.mul_assoc, hSF, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp h.isUnit), Matrix.mul_one]
  rw [← rowSelectionMatrix_mul, ← Matrix.mul_assoc]
  apply (toEuclideanLin : Matrix m n ℂ ≃ₗ[ℂ] _).injective
  ext1 x
  obtain ⟨z, hz⟩ : toEuclideanLin A x ∈ columnSpace F := by
    rw [h.rank_and_columnSpace.2.2.1]
    exact ⟨x, rfl⟩
  rw [toEuclideanLin_mul_apply, ← hz, ← toEuclideanLin_mul_apply, hfix]

omit [DecidableEq m] [DecidableEq n] in
/-- **Lemma (29.1)(1)–(4)** of [benIsrael2003generalized], Appendix A.
The column and row Gram matrices of a maximal pivot, and their inverses,
are Hermitian positive definite. -/
theorem lemma_29_1_gram_posDef {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    let F := A.submatrix id J
    let G := A.submatrix I id
    (Fᴴ * F).PosDef ∧ ((Fᴴ * F)⁻¹).PosDef ∧ (G * Gᴴ).PosDef ∧ ((G * Gᴴ)⁻¹).PosDef := by
  classical
  let F := A.submatrix id J
  let G := A.submatrix I id
  obtain ⟨hF, hG, _, _⟩ := h.rank_and_columnSpace
  have hFu : IsUnit (Fᴴ * F) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (F.rank_conjTranspose_mul_self.trans hF))
  have hGu : IsUnit (G * Gᴴ) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (G.rank_self_mul_conjTranspose.trans hG))
  have hFp := (posSemidef_conjTranspose_mul_self F).posDef_iff_isUnit.mpr hFu
  have hGp := (posSemidef_self_mul_conjTranspose G).posDef_iff_isUnit.mpr hGu
  exact ⟨hFp, hFp.inv, hGp, hGp.inv⟩

omit [DecidableEq m] in
private theorem pivot_reciprocals {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    let F := A.submatrix id J
    let G := A.submatrix I id
    F.pinv = (Fᴴ * F)⁻¹ * Fᴴ ∧ G.pinv = Gᴴ * (G * Gᴴ)⁻¹ := by
  classical
  let F := A.submatrix id J
  let G := A.submatrix I id
  obtain ⟨hF, _, hG, _⟩ := lemma_29_1_gram_posDef h
  refine ⟨pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hF.isUnit, ?_⟩
  have hu : IsUnit (Gᴴᴴ * Gᴴ) := by simpa only [conjTranspose_conjTranspose] using hG.isUnit
  have hh := congrArg Matrix.conjTranspose
    (pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hu)
  simpa only [pinv_conjTranspose, conjTranspose_conjTranspose, conjTranspose_mul,
    (isHermitian_mul_conjTranspose_self G).inv.eq] using hh

/-- **Lemma (29.1)(5)–(10)** of [benIsrael2003generalized], Appendix A.
The two Gram formulas give the generalized identities on the column and
adjoint column spaces, fixing vectors and their conjugate rows. -/
theorem lemma_29_1_projectors {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    let F := A.submatrix id J
    let G := A.submatrix I id
    let P := F * (Fᴴ * F)⁻¹ * Fᴴ
    let Q := Gᴴ * (G * Gᴴ)⁻¹ * G
    P = generalizedIdentityMatrix (columnSpace A) ∧
      Q = generalizedIdentityMatrix (columnSpace Aᴴ) ∧
      (∀ x ∈ columnSpace A, toEuclideanLin P x = x ∧ toEuclideanLin Pᴴ x = x) ∧
      ∀ x ∈ columnSpace Aᴴ, toEuclideanLin Q x = x ∧ toEuclideanLin Qᴴ x = x := by
  let F := A.submatrix id J
  let G := A.submatrix I id
  obtain ⟨hFp, hGp⟩ := pivot_reciprocals h
  obtain ⟨_, _, hF, hG⟩ := h.rank_and_columnSpace
  have hP : F * (Fᴴ * F)⁻¹ * Fᴴ = generalizedIdentityMatrix (columnSpace A) := by
    rw [Matrix.mul_assoc, ← hFp, mul_pinv_eq_generalizedIdentity, hF]
  have hQ : Gᴴ * (G * Gᴴ)⁻¹ * G = generalizedIdentityMatrix (columnSpace Aᴴ) := by
    rw [← hGp, pinv_mul_eq_generalizedIdentity, hG]
  have hfix (M : Submodule ℂ (EuclideanSpace ℂ n)) (x : EuclideanSpace ℂ n) (hx : x ∈ M) :
      toEuclideanLin (generalizedIdentityMatrix M) x = x ∧
        toEuclideanLin (generalizedIdentityMatrix M)ᴴ x = x := by
    rw [(theorem_29_2 M).1.eq, generalizedIdentityMatrix_toEuclideanLin]
    exact ⟨M.starProjection_eq_self_iff.mpr hx, M.starProjection_eq_self_iff.mpr hx⟩
  refine ⟨hP, hQ, ?_, ?_⟩
  · intro x hx
    rw [hP]
    rw [(theorem_29_2 (columnSpace A)).1.eq, generalizedIdentityMatrix_toEuclideanLin]
    exact ⟨(columnSpace A).starProjection_eq_self_iff.mpr hx,
      (columnSpace A).starProjection_eq_self_iff.mpr hx⟩
  · intro x hx
    rw [hQ]
    exact hfix (columnSpace Aᴴ) x hx

/-- The pivot formulas for the two generalized identities, expressed as
products of the selected matrix and its own reciprocal. -/
private theorem pivot_projection_products {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    let F := A.submatrix id J
    let G := A.submatrix I id
    F * F.pinv = generalizedIdentityMatrix (columnSpace A) ∧
      G.pinv * G = generalizedIdentityMatrix (columnSpace Aᴴ) := by
  obtain ⟨_, _, hF, hG⟩ := h.rank_and_columnSpace
  dsimp only
  rw [mul_pinv_eq_generalizedIdentity, pinv_mul_eq_generalizedIdentity, hF, hG]
  exact ⟨rfl, rfl⟩

private theorem pivot_projector_selections {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    (generalizedIdentityMatrix (columnSpace A)).submatrix I id =
      A.submatrix I J * (A.submatrix id J).pinv ∧
    (generalizedIdentityMatrix (columnSpace Aᴴ)).submatrix id J =
      (A.submatrix I id).pinv * A.submatrix I J := by
  obtain ⟨hP, hQ⟩ := pivot_projection_products h
  obtain ⟨hSF, hGS⟩ := pivot_eq_selections A I J
  constructor
  · rw [← hP, ← rowSelectionMatrix_mul, ← Matrix.mul_assoc, hSF]
  · rw [← hQ, ← mul_rowSelectionMatrix_conjTranspose, Matrix.mul_assoc, hGS]

omit [DecidableEq m] in
private theorem pivot_pinv_eq {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    A.pinv = (A.submatrix I id).pinv * A.submatrix I J * (A.submatrix id J).pinv := by
  classical
  let F := A.submatrix id J
  let G := A.submatrix I id
  let H := A.submatrix I J
  let X := G.pinv * H * F.pinv
  have hG := h.rank_and_columnSpace.2.2.2
  have hGright : G * G.pinv = 1 := by
    have hGp := (pivot_reciprocals h).2
    have hGu := (lemma_29_1_gram_posDef h).2.2.1.isUnit
    rw [hGp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hGu)]
  have hAX : A * X = generalizedIdentityMatrix (columnSpace A) := calc
    A * X = F * H⁻¹ * (G * G.pinv) * H * F.pinv := by
      nth_rw 1 [h.factorization]
      simp only [X, F, G, H, Matrix.mul_assoc]
    _ = F * F.pinv := by rw [hGright, Matrix.mul_one, Matrix.mul_assoc _ H⁻¹ H,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp h.isUnit), Matrix.mul_one]
    _ = _ := (pivot_projection_products h).1
  symm
  apply (theorem_29_5 A X).1.mpr
  refine ⟨?_, hAX⟩
  rw [show X = G.pinv * (H * F.pinv) by simp only [X, Matrix.mul_assoc]]
  exact (columnSpace_mul_le G.pinv _).trans ((columnSpace_pinv G).trans hG).le

/-- **Lemma (29.1)(11)–(14)** of [benIsrael2003generalized], Appendix A.
The maximal pivot gives three expressions for the reciprocal. The reciprocal
maps the column space of the matrix onto that of the adjoint. Its left and
right products give the corresponding generalized identities. -/
theorem lemma_29_1_reciprocal {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    let F := A.submatrix id J
    let G := A.submatrix I id
    let H := A.submatrix I J
    let P := generalizedIdentityMatrix (columnSpace A)
    let Q := generalizedIdentityMatrix (columnSpace Aᴴ)
    A.pinv = Gᴴ * (G * Gᴴ)⁻¹ * H * (Fᴴ * F)⁻¹ * Fᴴ ∧
      A.pinv = Gᴴ * (G * Gᴴ)⁻¹ * P.submatrix I id ∧
      A.pinv = Q.submatrix id J * (Fᴴ * F)⁻¹ * Fᴴ ∧
      Set.MapsTo (toEuclideanLin A.pinv) (columnSpace A : Set _) (columnSpace Aᴴ : Set _) ∧
      Set.SurjOn (toEuclideanLin A.pinv) (columnSpace A : Set _) (columnSpace Aᴴ : Set _) ∧
      A * A.pinv = P ∧ A.pinv * A = Q := by
  let F := A.submatrix id J
  let G := A.submatrix I id
  let H := A.submatrix I J
  obtain ⟨hFp, hGp⟩ := pivot_reciprocals h
  obtain ⟨hPi, hQj⟩ := pivot_projector_selections h
  refine ⟨?_, ?_, ?_, ?_, ?_, mul_pinv_eq_generalizedIdentity A, pinv_mul_eq_generalizedIdentity A⟩
  · rw [pivot_pinv_eq h, hFp, hGp]
    simp only [Matrix.mul_assoc]
  · rw [pivot_pinv_eq h, hPi, ← hGp, Matrix.mul_assoc]
  · rw [pivot_pinv_eq h, hQj, hFp]
    simp only [Matrix.mul_assoc]
  · intro x _
    rw [← columnSpace_pinv A]
    exact ⟨x, rfl⟩
  · intro x hx
    let y := mooreReciprocal_range_equiv A ⟨x, hx⟩
    exact ⟨y.val, y.2,
      congrArg Subtype.val ((mooreReciprocal_range_equiv A).symm_apply_apply ⟨x, hx⟩)⟩

/-- The selected columns of the adjoint-space projector and the selected
rows of the column-space projector furnish the pivot formula. -/
theorem corollary_29_45 {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) :
    A.pinv = (generalizedIdentityMatrix (columnSpace Aᴴ)).submatrix id J *
      (A.submatrix I J)⁻¹ * (generalizedIdentityMatrix (columnSpace A)).submatrix I id := by
  let F := A.submatrix id J
  let G := A.submatrix I id
  let H := A.submatrix I J
  obtain ⟨hPi, hQj⟩ := pivot_projector_selections h
  rw [pivot_pinv_eq h, hPi, hQj, Matrix.mul_assoc (G.pinv * H) H⁻¹,
    ← Matrix.mul_assoc H⁻¹ H F.pinv,
    Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp h.isUnit), Matrix.one_mul]

/-- **Corollary (29.45)(2)** of [benIsrael2003generalized], Appendix A.
For vectors in the adjoint and ordinary column spaces, the reciprocal form
is computed from the column-selected first vector and the row-selected second vector. -/
theorem corollary_29_45_form {A : Matrix m n ℂ} {I : k ↪ m} {J : k ↪ n}
    (h : IsMaximalNonsingularMinor A I J) {x : EuclideanSpace ℂ n} {y : EuclideanSpace ℂ m}
    (hx : x ∈ columnSpace Aᴴ) (hy : y ∈ columnSpace A) :
    inner ℂ x (toEuclideanLin A.pinv y) =
      inner ℂ (toEuclideanLin (rowSelectionMatrix J) x)
        (toEuclideanLin (A.submatrix I J)⁻¹ (toEuclideanLin (rowSelectionMatrix I) y)) := by
  let P := generalizedIdentityMatrix (columnSpace A)
  let Q := generalizedIdentityMatrix (columnSpace Aᴴ)
  rw [corollary_29_45 h, ← rowSelectionMatrix_mul, ← mul_rowSelectionMatrix_conjTranspose]
  simp only [toEuclideanLin_mul_apply]
  have hP : toEuclideanLin P y = y := by
    rw [generalizedIdentityMatrix_toEuclideanLin]
    exact (columnSpace A).starProjection_eq_self_iff.mpr hy
  have hQ : toEuclideanLin Q x = x := by
    rw [generalizedIdentityMatrix_toEuclideanLin]
    exact (columnSpace Aᴴ).starProjection_eq_self_iff.mpr hx
  rw [show toEuclideanLin (generalizedIdentityMatrix (columnSpace A)) y = y from hP,
    ← show Qᴴ = generalizedIdentityMatrix (columnSpace Aᴴ) from (theorem_29_2 _).1.eq,
    toEuclideanLin_conjTranspose_inner_right, hQ, toEuclideanLin_conjTranspose_inner_right]

/-- Selecting rows of a positive semidefinite matrix gives columns in the
range of the corresponding principal submatrix. -/
private theorem columnSpace_rows_le_principal {A : Matrix n n ℂ} (hA : A.PosSemidef) (I : k → n) :
    columnSpace (A.submatrix I id) ≤ columnSpace (A.submatrix I I) := by
  let S := rowSelectionMatrix I
  let H := A.submatrix I I
  let G := A.submatrix I id
  have hG : S * A = G := rowSelectionMatrix_mul I A
  have hH : G * Sᴴ = H := by
    rw [mul_rowSelectionMatrix_conjTranspose, submatrix_submatrix,
      Function.id_comp, Function.comp_id]
  have hHerm := (hA.submatrix I).isHermitian
  suffices horth : (columnSpace H)ᗮ ≤ (columnSpace G)ᗮ by
    simpa only [Submodule.orthogonal_orthogonal] using Submodule.orthogonal_le horth
  rw [← show Hᴴ = H from hHerm.eq, orthogonal_columnSpace_conjTranspose,
    ← conjTranspose_conjTranspose G, orthogonal_columnSpace_conjTranspose]
  intro x hx
  have hz : H *ᵥ WithLp.ofLp x = 0 := by
    simpa only [LinearMap.mem_ker, toEuclideanLin_apply, WithLp.toLp_eq_zero] using hx
  have hquad : star (Sᴴ *ᵥ WithLp.ofLp x) ⬝ᵥ (A *ᵥ (Sᴴ *ᵥ WithLp.ofLp x)) = 0 := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec,
      mulVec_mulVec (Sᴴ *ᵥ WithLp.ofLp x) S A, hG, mulVec_mulVec, hH, hz, dotProduct_zero]
  have hnull := hA.dotProduct_mulVec_zero_iff.mp hquad
  rw [LinearMap.mem_ker, toEuclideanLin_apply, WithLp.toLp_eq_zero, ← hG,
    conjTranspose_mul, hA.isHermitian.eq, ← mulVec_mulVec]
  exact hnull

omit [Fintype n] [DecidableEq n] in
/-- Every principal submatrix satisfies the first reciprocal equation with
its own reciprocal. -/
theorem principalSubmatrix_mul_pinv_mul (A : Matrix n n ℂ) (I : k → n) :
    A.submatrix I I * (A.submatrix I I).pinv * A.submatrix I I = A.submatrix I I :=
  (A.submatrix I I).mul_pinv_mul_self

omit [Fintype n] [DecidableEq n] in
/-- **Theorem (29.7)(1)–(2)** of [benIsrael2003generalized], Appendix A.
The two reciprocal projections of a positive principal block fix the
corresponding rows and columns of the full matrix. -/
theorem theorem_29_7 [Finite n] (A : Matrix n n ℂ) (hA : A.PosSemidef) (I : k ↪ n) :
    let H := A.submatrix I I
    H * H.pinv * A.submatrix I id = A.submatrix I id ∧
      A.submatrix id I * H.pinv * H = A.submatrix id I := by
  classical
  let _ : Fintype n := Fintype.ofFinite n
  let H := A.submatrix I I
  have hH := hA.submatrix I
  have h := mul_pinv_mul_eq_of_columnSpace_le (columnSpace_rows_le_principal hA I)
  refine ⟨h, ?_⟩
  simpa only [conjTranspose_mul, ← pinv_conjTranspose, hH.isHermitian.eq,
    conjTranspose_submatrix, hA.isHermitian.eq, Matrix.mul_assoc] using
    congrArg Matrix.conjTranspose h

end Submatrix

end BenIsraelGreville.AppendixA
