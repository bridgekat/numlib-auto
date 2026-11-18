/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import NumlibSurface.BenIsraelGreville.Chapter00.Section05

/-!
# Exterior powers and compound matrices

Section 0.6 of [benIsrael2003generalized] describes compound matrices as
the maps induced on exterior powers. The increasing index sequences in
Section 0.2 index the standard exterior bases.

## Deviations from the source

* **Exercise 68** (typo). The factors in the volume computation are the
  one-dimensional volumes of the second compounds of $C$ and $R$.
-/

namespace BenIsraelGreville.Chapter00

open Matrix Module

variable {K : Type*} [Field K] {m n p : ℕ}

/-- **Section 0.6** of [benIsrael2003generalized]. The $k$th exterior space
of the coordinate space on $n$ indices. -/
abbrev exteriorPower (K : Type*) [Field K] (k n : ℕ) :=
  ⋀[K]^k (Fin n → K)

/-- The basis vectors are the wedges of standard unit vectors in the
increasing index sequence. -/
noncomputable def exteriorCoordinateBasis (K : Type*) [Field K] (k n : ℕ) :
    Basis (IndexSequence k n) K (exteriorPower K k n) :=
  ((Pi.basisFun K (Fin n)).exteriorPower k).reindex Set.powersetCard.ofFinEmbEquiv.symm

/-- **Equation (108)** of [benIsrael2003generalized], Chapter 0. The entries of
the $k$th compound matrix are the $k$-row, $k$-column minors. -/
def compound (k : ℕ) (A : Matrix (Fin m) (Fin n) K) :
    Matrix (IndexSequence k m) (IndexSequence k n) K :=
  fun i j => (A.submatrix i j).det

/-- The minor matrix is the coordinate representation of the exterior map. -/
theorem compound_eq_toMatrix (k : ℕ) (A : Matrix (Fin m) (Fin n) K) :
    compound k A = LinearMap.toMatrix (exteriorCoordinateBasis K k n)
      (exteriorCoordinateBasis K k m) (_root_.exteriorPower.map k A.mulVecLin) := by
  ext i j
  rw [LinearMap.toMatrix_apply, exteriorCoordinateBasis, exteriorCoordinateBasis,
    Basis.reindex_apply, Basis.repr_reindex_apply, Equiv.symm_symm,
    _root_.exteriorPower.basis_apply, _root_.exteriorPower.map_apply_ιMulti_family,
    _root_.exteriorPower.ιMulti_family, _root_.exteriorPower.basis_repr_apply,
    _root_.exteriorPower.ιMultiDual_apply_ιMulti, Equiv.symm_apply_apply]
  rw [compound, ← det_transpose (A.submatrix i j)]
  congr 1
  ext a b
  simp [Function.comp_apply, Basis.coord_apply]

/-- **Equation (108)** of [benIsrael2003generalized], Chapter 0. The compound
acts on a wedge of vectors by applying the matrix to each vector. -/
theorem compound_map_wedge (k : ℕ) (A : Matrix (Fin m) (Fin n) K)
    (x : Fin k → Fin n → K) :
    (compound k A).toLin (exteriorCoordinateBasis K k n) (exteriorCoordinateBasis K k m)
      (_root_.exteriorPower.ιMulti K k x) =
      _root_.exteriorPower.ιMulti K k (fun i => A *ᵥ x i) := by
  rw [compound_eq_toMatrix, Matrix.toLin_toMatrix, _root_.exteriorPower.map_apply_ιMulti]
  rfl

/-- A compound preserves matrix multiplication. -/
theorem compound_mul (k : ℕ) (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin p) K) :
    compound k (A * B) = compound k A * compound k B := by
  classical
  simp only [compound_eq_toMatrix, Matrix.mulVecLin_mul, _root_.exteriorPower.map_comp]
  exact LinearMap.toMatrix_comp (exteriorCoordinateBasis K k p)
    (exteriorCoordinateBasis K k n) (exteriorCoordinateBasis K k m) _ _

/-- Increasing selections of $k$ indices from $n$ have cardinality
$inom{n}{k}$. -/
theorem card_indexSequence (k n : ℕ) : Fintype.card (IndexSequence k n) = n.choose k := by
  rw [Fintype.card_congr (Set.powersetCard.ofFinEmbEquiv (I := Fin n) (n := k)),
    Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]

/-- **Section 0.6** of [benIsrael2003generalized]. The rank of the $k$th
compound is the number of $k$-element subsets of a set of size $operatorname{rank} A$. -/
theorem compound_rank (k : ℕ) (A : Matrix (Fin m) (Fin n) K) :
    (compound k A).rank = A.rank.choose k := by
  rw [rank_eq_finrank_range_toLin _ (exteriorCoordinateBasis K k m)
    (exteriorCoordinateBasis K k n), compound_eq_toMatrix, Matrix.toLin_toMatrix]
  let f := A.mulVecLin
  have he : _root_.exteriorPower.map k f =
      (_root_.exteriorPower.map k f.range.subtype).comp
        (_root_.exteriorPower.map k f.rangeRestrict) := by
    rw [← _root_.exteriorPower.map_comp]
    congr 1
  have hs := _root_.exteriorPower.map_surjective (n := k) f.surjective_rangeRestrict
  have hi := _root_.exteriorPower.map_injective_field (n := k) f.range.subtype_injective
  rw [he, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs),
    LinearMap.finrank_range_of_inj hi, _root_.exteriorPower.finrank_eq]
  rfl

/-- The exterior product written in the ordered exterior coordinate basis. -/
noncomputable def wedgeCoordinates (k : ℕ) (x : Fin k → Fin n → K) :
    IndexSequence k n → K :=
  (exteriorCoordinateBasis K k n).repr (_root_.exteriorPower.ιMulti K k x)

/-- A wedge coordinate is the determinant formed by restricting the input
vectors to the corresponding coordinate selection. -/
theorem wedgeCoordinates_apply (k : ℕ) (x : Fin k → Fin n → K) (i : IndexSequence k n) :
    wedgeCoordinates k x i = (Matrix.of fun a b => x b (i a)).det := by
  rw [wedgeCoordinates, exteriorCoordinateBasis, Basis.repr_reindex_apply, Equiv.symm_symm,
    _root_.exteriorPower.basis_repr_apply, _root_.exteriorPower.ιMultiDual_apply_ιMulti,
    Equiv.symm_apply_apply, ← det_transpose]
  congr 1

/-- The coordinate form of the exterior map on a wedge of vectors. -/
theorem compound_mulVec_wedgeCoordinates (k : ℕ) (A : Matrix (Fin m) (Fin n) K)
    (x : Fin k → Fin n → K) :
    compound k A *ᵥ wedgeCoordinates k x = wedgeCoordinates k (fun i => A *ᵥ x i) := by
  rw [compound_eq_toMatrix]
  simpa only [wedgeCoordinates, _root_.exteriorPower.map_apply_ιMulti, Function.comp_def,
    Matrix.mulVecLin_apply] using
    LinearMap.toMatrix_mulVec_repr (exteriorCoordinateBasis K k n)
      (exteriorCoordinateBasis K k m) (_root_.exteriorPower.map k A.mulVecLin)
      (_root_.exteriorPower.ιMulti K k x)

/-- The compound commutes with transposition. -/
theorem compound_transpose (k : ℕ) (A : Matrix (Fin m) (Fin n) K) :
    compound k Aᵀ = (compound k A)ᵀ := by
  ext i j
  change (Aᵀ.submatrix i j).det = (A.submatrix j i).det
  rw [← transpose_submatrix, det_transpose]

/-- The compound of the identity is the identity in the exterior basis. -/
theorem compound_one (k n : ℕ) :
    compound k (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  classical
  rw [compound_eq_toMatrix, Matrix.mulVecLin_one, _root_.exteriorPower.map_id,
    LinearMap.toMatrix_id]

/-- **Equation (109)** of [benIsrael2003generalized], Chapter 0. The top
exterior line is the image of the top exterior power of the subspace. -/
noncomputable def topExteriorLine (W : Submodule K (Fin n → K)) :
    Submodule K (exteriorPower K (finrank K W) n) :=
  LinearMap.range (_root_.exteriorPower.map (finrank K W) W.subtype)

/-- The top exterior line has dimension one. -/
theorem finrank_topExteriorLine (W : Submodule K (Fin n → K)) :
    finrank K (topExteriorLine W) = 1 := by
  rw [topExteriorLine, LinearMap.finrank_range_of_inj
    (_root_.exteriorPower.map_injective_field W.subtype_injective),
    _root_.exteriorPower.finrank_eq, Nat.choose_self]

/-- **Equation (109)** of [benIsrael2003generalized], Chapter 0. The wedge
of any ordered basis of the subspace generates its top exterior line. -/
theorem topExteriorLine_eq_span (W : Submodule K (Fin n → K))
    (b : Basis (Fin (finrank K W)) K W) :
    topExteriorLine W =
      K ∙ _root_.exteriorPower.ιMulti K (finrank K W) (fun j => (b j : Fin n → K)) := by
  let r := finrank K W
  let x := _root_.exteriorPower.ιMulti K r (fun j => (b j : Fin n → K))
  let s : Set.powersetCard (Fin r) r :=
    Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin r)).toOrderEmbedding)
  have hx : _root_.exteriorPower.map r W.subtype (b.exteriorPower r s) = x := by
    rw [_root_.exteriorPower.basis_apply, _root_.exteriorPower.map_apply_ιMulti_family]
    simp [x, s, _root_.exteriorPower.ιMulti_family, Function.comp_def]
    rfl
  have hx0 : x ≠ 0 := by
    simpa only [hx, map_zero] using
      (_root_.exteriorPower.map_injective_field (n := r) W.subtype_injective).ne
        ((b.exteriorPower r).ne_zero s)
  have hxMem : x ∈ topExteriorLine W := ⟨b.exteriorPower r s, hx⟩
  exact (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hxMem)
    (by rw [finrank_topExteriorLine, finrank_span_singleton hx0])).symm

/-- The Plücker coordinates associated with a chosen ordered basis of a
subspace are the coordinates of its top exterior product. -/
noncomputable def pluckerCoordinates (W : Submodule K (Fin n → K))
    (b : Basis (Fin (finrank K W)) K W) : IndexSequence (finrank K W) n → K :=
  wedgeCoordinates (finrank K W) (fun j => (b j : Fin n → K))

/-- Changing the basis multiplies every Plücker coordinate by the same
nonzero scalar. -/
theorem pluckerCoordinates_eq_smul (W : Submodule K (Fin n → K))
    (b c : Basis (Fin (finrank K W)) K W) :
    ∃ a : Kˣ, pluckerCoordinates W c = (a : K) • pluckerCoordinates W b := by
  obtain ⟨a, ha⟩ := Submodule.span_singleton_eq_span_singleton.mp
    ((topExteriorLine_eq_span W b).symm.trans (topExteriorLine_eq_span W c))
  refine ⟨a, ?_⟩
  rw [pluckerCoordinates, pluckerCoordinates, wedgeCoordinates, wedgeCoordinates, ← ha]
  ext j
  simp [Units.smul_def]

/-- **Equation (114a)** of [benIsrael2003generalized], Chapter 0.
The $k$-volume is the Frobenius norm of the compound for $1le kleoperatorname{rank} A$.
It vanishes by convention outside those degrees. -/
noncomputable def kVolume (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  if k = 0 ∨ A.rank < k then 0 else
    Real.sqrt (∑ i : IndexSequence k m, ∑ j : IndexSequence k n, (compound k A i j) ^ 2)

open scoped Matrix.Norms.Frobenius in
/-- The $k$-volume is the Frobenius norm of the compound in the positive
degrees up to the rank. -/
theorem kVolume_eq_frobenius_norm (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (hk : 0 < k) (hr : k ≤ A.rank) : kVolume k A = ‖compound k A‖ := by
  unfold kVolume
  rw [ite_eq_right (not_or.mpr ⟨hk.ne', not_lt_of_ge hr⟩)]
  apply (Real.sqrt_eq_iff_eq_sq
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (norm_nonneg _)).mpr
  rw [frobenius_norm_sq_eq_sum_sq]
  simp

/-- At the positive rank of the matrix the compound volume is the volume
defined by the maximal nonsingular minors. -/
theorem kVolume_eq_matrixVolume {r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hr : A.rank = r) (h0 : r ≠ 0) : kVolume r A = matrixVolume A := by
  rw [matrixVolume_eq_sqrt_sum_minors A hr h0, kVolume, ite_eq_right]
  · rfl
  · simp [hr, h0]

private theorem wedgeCoordinates_col {r : ℕ} (C : Matrix (Fin m) (Fin r) K)
    (i : IndexSequence r m) :
    wedgeCoordinates r C.col i = (C.submatrix i id).det := by
  rw [wedgeCoordinates_apply]
  rfl

private theorem wedgeCoordinates_row {r : ℕ} (R : Matrix (Fin r) (Fin n) K)
    (j : IndexSequence r n) :
    wedgeCoordinates r R.row j = (R.submatrix id j).det := by
  rw [wedgeCoordinates_apply, ← det_transpose (R.submatrix id j)]
  rfl

/-- **Equation (110a)** of [benIsrael2003generalized], Chapter 0. The top
compound of a full-row-rank matrix sends the wedge of its rows to its
squared volume in the unique top coordinate. -/
theorem lemma_2_a {r : ℕ} (R : Matrix (Fin r) (Fin n) ℝ) (hr : R.rank = r) (h0 : r ≠ 0) :
    compound r R *ᵥ wedgeCoordinates r R.row = fun _ => matrixVolume R ^ 2 := by
  funext i
  rw [matrixVolume_sq_eq_det_mul_transpose R hr h0, det_mul_eq_sum_minors,
    indexSequence_self_unique i]
  apply Finset.sum_congr rfl
  intro j _
  rw [wedgeCoordinates_row, ← transpose_submatrix, det_transpose]
  rfl

/-- **Equation (110b)** of [benIsrael2003generalized], Chapter 0. The top
compound of the transpose of a full-column-rank matrix sends the wedge
of its columns to its squared volume. -/
theorem lemma_2_b {r : ℕ} (C : Matrix (Fin m) (Fin r) ℝ) (hr : C.rank = r) (h0 : r ≠ 0) :
    compound r Cᵀ *ᵥ wedgeCoordinates r C.col = fun _ => matrixVolume C ^ 2 := by
  funext j
  rw [matrixVolume_sq_eq_det_transpose_mul C hr h0, det_mul_eq_sum_minors,
    indexSequence_self_unique j]
  apply Finset.sum_congr rfl
  intro i _
  rw [wedgeCoordinates_col]
  rfl

/-- **Equation (110c)** of [benIsrael2003generalized], Chapter 0. The top
compound in a full-rank factorization is the outer product of the wedge
coordinates of the columns and of the rows of its two factors. -/
theorem lemma_2_c {r : ℕ} {A : Matrix (Fin m) (Fin n) K}
    {C : Matrix (Fin m) (Fin r) K} {R : Matrix (Fin r) (Fin n) K}
    (h : IsRankFactorization A C R) :
    compound r A = vecMulVec (wedgeCoordinates r C.col) (wedgeCoordinates r R.row) := by
  ext i j
  rw [vecMulVec_apply, wedgeCoordinates_col, wedgeCoordinates_row]
  change (A.submatrix i j).det = (C.submatrix i id).det * (R.submatrix id j).det
  rw [submatrix_mul_submatrix_eq h.eq_mul, det_mul]

/-- **Equation (111)** of [benIsrael2003generalized], Chapter 0. The inner
product of the column wedge with the wedge of the images of the row vectors
is the squared volume. The ordered exterior basis is orthonormal. -/
theorem lemma_2_inner {r : ℕ} (h0 : r ≠ 0) {A : Matrix (Fin m) (Fin n) ℝ}
    {C : Matrix (Fin m) (Fin r) ℝ} {R : Matrix (Fin r) (Fin n) ℝ}
    (h : IsRankFactorization A C R) :
    wedgeCoordinates r C.col ⬝ᵥ wedgeCoordinates r (fun j => A *ᵥ R.row j) =
      matrixVolume A ^ 2 := by
  classical
  let : Unique (IndexSequence r r) :=
    ⟨⟨(OrderIso.refl (Fin r)).toOrderEmbedding⟩, indexSequence_self_unique⟩
  have hC := h.rank_left.trans (Fintype.card_fin r)
  have hR := h.rank_right.trans (Fintype.card_fin r)
  have hMul : compound r A = compound r C * compound r R :=
    (congrArg (compound r) h.eq_mul).trans (compound_mul r C R)
  rw [← compound_mulVec_wedgeCoordinates, hMul, ← mulVec_mulVec, lemma_2_a R hR h0]
  rw [← dotProduct_transpose_mulVec, ← compound_transpose, lemma_2_b C hC h0]
  rw [dotProduct, Fintype.sum_unique, matrixVolume_mul_of_rankFactorization h, mul_pow, mul_comm]

open scoped Matrix.Norms.Frobenius in
/-- **Equation (112)** of [benIsrael2003generalized], Chapter 0. The squared
volume is the squared Frobenius norm of the top compound and factors into
the squared Frobenius norms of the top compounds of the rank factors. -/
theorem lemma_2_volume {r : ℕ} (h0 : r ≠ 0) {A : Matrix (Fin m) (Fin n) ℝ}
    {C : Matrix (Fin m) (Fin r) ℝ} {R : Matrix (Fin r) (Fin n) ℝ}
    (h : IsRankFactorization A C R) :
    matrixVolume A ^ 2 = ‖compound r A‖ ^ 2 ∧
      ‖compound r A‖ ^ 2 = ‖compound r C‖ ^ 2 * ‖compound r R‖ ^ 2 := by
  have hVol {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) (hr : B.rank = r) :
      ‖compound r B‖ = matrixVolume B := by
    rw [← kVolume_eq_frobenius_norm r B (Nat.pos_of_ne_zero h0) hr.ge,
      kVolume_eq_matrixVolume B hr h0]
  have hA := h.rank_eq.trans (Fintype.card_fin r)
  have hC := h.rank_left.trans (Fintype.card_fin r)
  have hR := h.rank_right.trans (Fintype.card_fin r)
  rw [hVol A hA]
  refine ⟨rfl, ?_⟩
  rw [hVol C hC, hVol R hR, matrixVolume_mul_of_rankFactorization h, mul_pow]

/-- **Equation (115)** of [benIsrael2003generalized], Chapter 0.
A square left factor scales the full-row-dimensional volume by the
absolute value of its determinant. -/
theorem kVolume_mul_left (S : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (hr : A.rank = m) : kVolume m (S * A) = |S.det| * matrixVolume A := by
  classical
  by_cases hm : m = 0
  · simp [kVolume, matrixVolume, hr, hm]
  by_cases hu : IsUnit S
  · have hSA : (S * A).rank = m :=
      (rank_mul_eq_right_of_isUnit_det S A ((isUnit_iff_isUnit_det S).mp hu)).trans hr
    rw [kVolume_eq_matrixVolume (S * A) hSA hm,
      matrixVolume_eq_sqrt_sum_minors (S * A) hSA hm, matrixVolume_eq_sqrt_sum_minors A hr hm]
    let : Unique (IndexSequence m m) :=
      ⟨⟨(OrderIso.refl (Fin m)).toOrderEmbedding⟩, indexSequence_self_unique⟩
    simp only [Fintype.sum_unique]
    change Real.sqrt (∑ j : IndexSequence m n, ((S * A).submatrix id j).det ^ 2) =
      |S.det| * Real.sqrt (∑ j : IndexSequence m n, (A.submatrix id j).det ^ 2)
    simp_rw [submatrix_mul_submatrix_eq (A := S * A) (F := S) (G := A) rfl,
      submatrix_id_id, det_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  · have hz : S.det = 0 := by
      simpa only [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] using hu
    have hs : S.rank < m := by
      refine lt_of_le_of_ne S.rank_le_width (fun he => hu ?_)
      exact mulVec_surjective_iff_isUnit.mp
        (mulVec_surjective_iff_rank_eq_card.mpr (he.trans (Fintype.card_fin m).symm))
    simp [kVolume, (rank_mul_le_left S A).trans_lt hs, hz]

private theorem trace_compound_diagonal (k : ℕ) (f : Fin n → K) :
    trace (compound k (diagonal f)) = ∑ s : IndexSequence k n, ∏ j : Fin k, f (s j) := by
  apply Finset.sum_congr rfl
  intro s _
  change ((diagonal f).submatrix s s).det = ∏ j, f (s j)
  rw [submatrix_diagonal _ _ s.injective, det_diagonal]
  rfl

private noncomputable def indexSequence_restrict {k r n : ℕ} (h : r ≤ n) :
    IndexSequence k r ≃ {s : IndexSequence k n // ∀ j, (s j).val < r} :=
  Equiv.ofBijective (fun s => ⟨s.trans (Fin.castLEOrderEmb h), fun j => (s j).isLt⟩) (by
    constructor
    · intro s t he
      ext j
      exact congrArg (fun a : {s : IndexSequence k n // ∀ j, (s j).val < r} =>
        (a.1 j).val) he
    · intro s
      let f (i : Fin k) : Fin r := ⟨(s.1 i).val, s.2 i⟩
      let t := OrderEmbedding.ofStrictMono f (fun _ _ hij => s.1.strictMono hij)
      refine ⟨t, Subtype.ext ?_⟩
      ext j
      rfl)

private theorem sum_indexSequence_of_zero_tail (k r : ℕ) (hr : r ≤ n) (f : ℕ → ℝ)
    (hz : ∀ j, r ≤ j → f j = 0) :
    (∑ s : IndexSequence k n, ∏ j : Fin k, f (s j).val) =
      ∑ s : IndexSequence k r, ∏ j : Fin k, f (s j).val := by
  classical
  let term (s : IndexSequence k n) := ∏ j : Fin k, f (s j).val
  let good (s : IndexSequence k n) := ∀ j, (s j).val < r
  have hbad : (∑ s : {s // ¬good s}, term s.1) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    obtain ⟨j, hj⟩ := not_forall.mp s.2
    exact Finset.prod_eq_zero (Finset.mem_univ j) (hz (s.1 j).val (not_lt.mp hj))
  change (∑ s, term s) = _
  rw [← Fintype.sum_subtype_add_sum_subtype good term, hbad, add_zero]
  exact (Equiv.sum_comp (indexSequence_restrict hr) (fun s => term s.1)).symm

open scoped Matrix.Norms.Frobenius in
/-- **Equation (114b)** of [benIsrael2003generalized], Chapter 0. The square
of the $k$-volume is the $k$th elementary symmetric function of the squares
of the positive singular values. -/
theorem kVolume_eq_sqrt_sum_singularValues (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (hk : 0 < k) (hr : k ≤ A.rank) :
    kVolume k A = Real.sqrt (∑ s : IndexSequence k A.rank,
      ∏ j : Fin k, A.sortedSingularValues (s j).val ^ 2) := by
  classical
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  let D : Matrix (Fin m) (Fin n) ℝ := Matrix.rectDiagonal A.sortedSingularValues
  have hUV : A = U * D * Vᵀ :=
    Matrix.eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  have hUt : Uᵀ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hVt : Vᵀ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hD : Dᵀ * D = diagonal (fun i : Fin n => A.sortedSingularValues i ^ 2) := by
    dsimp only [D]
    rw [← conjTranspose_eq_transpose_of_trivial, conjTranspose_rectDiagonal_mul_self]
    congr 1
    funext i
    by_cases hi : i.val < m
    · simp [hi, pow_two]
    · simp [hi, (A.sortedSingularValues_eq_zero_iff_rank_le i).mpr
        (A.rank_le_height.trans (not_lt.mp hi))]
  have hGram : Aᵀ * A = V * (Dᵀ * D) * Vᵀ := by
    rw [hUV, transpose_mul, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hUt, Matrix.one_mul]
  have htr : trace (compound k (Aᵀ * A)) = trace (compound k (Dᵀ * D)) := by
    rw [hGram, compound_mul, compound_mul, trace_mul_comm, ← Matrix.mul_assoc,
      ← compound_mul, hVt, compound_one, Matrix.one_mul]
  have hSq : ‖compound k A‖ ^ 2 = trace (compound k (Aᵀ * A)) := by
    simpa only [conjTranspose_eq_transpose_of_trivial, ← compound_transpose, ← compound_mul,
      RCLike.ofReal_real_eq_id, id_eq]
      using frobenius_norm_sq_eq_trace (compound k A)
  have hs : ‖compound k A‖ ^ 2 = ∑ s : IndexSequence k A.rank,
      ∏ j : Fin k, A.sortedSingularValues (s j).val ^ 2 := by
    rw [hSq, htr, hD, trace_compound_diagonal]
    exact sum_indexSequence_of_zero_tail k A.rank A.rank_le_width
      (fun j => A.sortedSingularValues j ^ 2)
      (fun j hj => by simp [(A.sortedSingularValues_eq_zero_iff_rank_le j).mpr hj])
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    kVolume_eq_frobenius_norm k A hk hr]

/-- The three pairs selected from three indices, in the order $(0,1)$,
$(0,2)$, and $(1,2)$. -/
noncomputable def pairSelectionsThree : Fin 3 ≃ IndexSequence 2 3 :=
  Equiv.ofBijective (fun i : Fin 3 => Fin.succAboveOrderEmb i.rev) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, by simp [card_indexSequence]⟩
    intro i j he
    have h := congrArg (fun f : IndexSequence 2 3 => Set.range f) he
    rw [Fin.range_succAboveOrderEmb, Fin.range_succAboveOrderEmb] at h
    exact Fin.rev_injective (Set.singleton_injective (compl_injective h)))

private theorem pairSelectionsThree_apply (i : Fin 3) (j : Fin 2) :
    pairSelectionsThree i j = (!![0, 1; 0, 2; 1, 2] : Matrix (Fin 3) (Fin 2) (Fin 3)) i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- **Exercise 68** of [benIsrael2003generalized], Chapter 0. The second
compound has the displayed entries in the order of the selected pairs. -/
theorem exercise_68_compound :
    (compound 2 (!![1, 2, 3; 4, 5, 6; 7, 8, 9] : Matrix (Fin 3) (Fin 3) ℝ)).submatrix
      pairSelectionsThree pairSelectionsThree = !![-3, -6, -3; -6, -12, -6; -3, -6, -3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [compound, submatrix_apply, Matrix.det_fin_two, pairSelectionsThree_apply]

/-- **Exercise 68** of [benIsrael2003generalized], Chapter 0. The second
compounds of the rank factors form the displayed column and row vectors. -/
theorem exercise_68_compound_factors :
    let C : Matrix (Fin 3) (Fin 2) ℝ := !![1, 2; 4, 5; 7, 8]
    let R : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, -1; 0, 1, 2]
    let e := (OrderIso.refl (Fin 2)).toOrderEmbedding
    ∀ i : Fin 3, compound 2 C (pairSelectionsThree i) e = ![-3, -6, -3] i ∧
      compound 2 R e (pairSelectionsThree i) = ![1, 2, 1] i := by
  intro C R e i
  fin_cases i <;>
    norm_num [compound, submatrix_apply, Matrix.det_fin_two, pairSelectionsThree_apply, C, R, e]

open scoped Matrix.Norms.Frobenius in
/-- **Exercise 68** of [benIsrael2003generalized], Chapter 0. The displayed
matrix factors as in Equation (113), has rank two and squared volume $324$. -/
theorem exercise_68_volume :
    let A : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2, 3; 4, 5, 6; 7, 8, 9]
    let C : Matrix (Fin 3) (Fin 2) ℝ := !![1, 2; 4, 5; 7, 8]
    let R : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, -1; 0, 1, 2]
    A = C * R ∧ A.rank = 2 ∧ matrixVolume A ^ 2 = 324 := by
  intro A C R
  have hA : A = C * R := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, C, R, Matrix.mul_apply, Fin.sum_univ_two]
  have hMinor : (A.submatrix (pairSelectionsThree 0) (pairSelectionsThree 0)).det = -3 := by
    norm_num [A, submatrix_apply, Matrix.det_fin_two, pairSelectionsThree_apply]
  have hu : IsUnit (A.submatrix (pairSelectionsThree 0) (pairSelectionsThree 0)) := by
    rw [isUnit_iff_isUnit_det, hMinor, isUnit_iff_ne_zero]
    norm_num
  have hr : A.rank = 2 := by
    apply le_antisymm
    · rw [hA]
      exact (rank_mul_le_left C R).trans (C.rank_le_width)
    · apply le_trans _ (rank_submatrix_le A (pairSelectionsThree 0) (pairSelectionsThree 0))
      simpa using (rank_of_isUnit _ hu).ge
  refine ⟨hA, hr, ?_⟩
  rw [← kVolume_eq_matrixVolume A hr (by decide),
    kVolume_eq_frobenius_norm _ _ (by decide) hr.ge,
    ← frobenius_norm_submatrix_equiv (compound 2 A) pairSelectionsThree pairSelectionsThree]
  change ‖(compound 2 (!![1, 2, 3; 4, 5, 6; 7, 8, 9] :
    Matrix (Fin 3) (Fin 3) ℝ)).submatrix pairSelectionsThree pairSelectionsThree‖ ^ 2 = 324
  rw [exercise_68_compound, frobenius_norm_sq_eq_sum_sq]
  norm_num [Fin.sum_univ_succ]

end BenIsraelGreville.Chapter00
