/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter03.Section05

/-!
# Minors of the Moore–Penrose inverse

Chapter 3, §6 of [benIsrael2003generalized] uses the squared determinant
weights of the basic inverses to average minors of every order.
-/

noncomputable section

namespace BenIsraelGreville.Chapter03

open Matrix

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [LinearOrder m] [LinearOrder n] [Preorder k] [DecidableEq k] {r : ℕ}

/-- **Theorem 9**, Equation (112) of [benIsrael2003generalized], Chapter 3.
Each minor of the reciprocal is the weighted sum of the corresponding
minors of the zero-extended basic inverses. -/
theorem theorem_9 (A : Matrix m n ℝ) (hr : A.rank = r) (α : k ↪o m) (β : k ↪o n) :
    (A.pinv.submatrix β α).det = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
      maximalMinorWeight A I J * ((basicInverse A I J).submatrix β α).det := by
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using pinv_submatrix_det_eq_sum_basic A hr α β

private theorem minorWeightSum_pos (A : Matrix m n ℝ) (hr : A.rank = r) :
    0 < minorWeightSum A r := by
  have hw : 0 ≤ minorWeightSum A r :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply lt_of_le_of_ne hw
  intro hz
  have h := (maximalMinorWeight_convex A hr).2
  simp [maximalMinorWeight, ← hz] at h

private theorem real_corresponding_maximal_minors (A : Matrix m n ℝ) (hr : A.rank = r)
    (I : Fin r ↪o m) (J : Fin r ↪o n) :
    (A.pinv.submatrix J I).det = (A.submatrix I J).det / minorWeightSum A r := by
  simpa only [RCLike.ofReal_real_eq_id, id_eq, star_trivial] using
    correspondingMaximalMinors A hr I J

/-- The determinant weights are unchanged by taking the reciprocal and
interchanging the selected rows and columns. -/
theorem maximalMinorWeight_pinv (A : Matrix m n ℝ) (hr : A.rank = r)
    (I : Fin r ↪o m) (J : Fin r ↪o n) :
    maximalMinorWeight A.pinv J I = maximalMinorWeight A I J := by
  let w := minorWeightSum A r
  have hw : w ≠ 0 := (minorWeightSum_pos A hr).ne'
  have hsum : minorWeightSum A.pinv r = w⁻¹ := by
    unfold minorWeightSum
    rw [Finset.sum_comm]
    simp_rw [real_corresponding_maximal_minors A hr, Real.norm_eq_abs, sq_abs, div_pow,
      ← Finset.sum_div]
    change (∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n, (A.submatrix I J).det ^ 2) / w ^ 2 = w⁻¹
    have hw' : (∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n, (A.submatrix I J).det ^ 2) = w := by
      simp only [w, minorWeightSum, Real.norm_eq_abs, sq_abs]
    rw [hw']
    field_simp
  simp only [maximalMinorWeight, real_corresponding_maximal_minors A hr, Real.norm_eq_abs, sq_abs,
    hsum]
  change ((A.submatrix I J).det / w) ^ 2 / w⁻¹ = (A.submatrix I J).det ^ 2 / w
  field_simp

private theorem reciprocal_involutive (A : Matrix m n ℝ) : A.pinv.pinv = A := by
  symm
  exact A.pinv.pinv_unique A.pinv_mul_self_mul_pinv A.mul_pinv_mul_self
    A.isHermitian_pinv_mul A.isHermitian_mul_pinv

omit [LinearOrder m] in
private theorem reciprocal_rank (A : Matrix m n ℝ) : A.pinv.rank = A.rank :=
  (Matrix.IsInnerInverse.isOuterInverse_iff_rank_eq A.mul_pinv_mul_self).mp A.pinv_mul_self_mul_pinv

/-- **Theorem 10**, Equations (114)–(115) of [benIsrael2003generalized], Chapter 3.
The original matrix and each of its minors have the same convex
decomposition into the padded inverses of the reciprocal's maximal minors. -/
theorem theorem_10 (A : Matrix m n ℝ) (hr : A.rank = r) (_hpos : 0 < r) :
    ∃ B : (Fin r ↪o m) → (Fin r ↪o n) → Matrix m n ℝ,
      (∀ (I : Fin r ↪o m) (J : Fin r ↪o n), IsUnit (A.submatrix I J) →
        ∃ H : Matrix (Fin r) (Fin r) ℝ, IsUnit H ∧
          B I J = minorColumnSelector I * H * minorRowSelector J) ∧
      A = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n, maximalMinorWeight A I J • B I J ∧
      ∀ (p : ℕ) (α : Fin p ↪o m) (β : Fin p ↪o n),
        (A.submatrix α β).det = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
          maximalMinorWeight A I J * ((B I J).submatrix α β).det := by
  refine ⟨fun I J => basicInverse A.pinv J I, ?_, ?_, ?_⟩
  · intro I J hij
    have hdet := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hij)
    have hunit : IsUnit (A.pinv.submatrix J I) := (isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (by
        rw [real_corresponding_maximal_minors A hr]
        exact div_ne_zero hdet (minorWeightSum_pos A hr).ne'))
    exact ⟨(A.pinv.submatrix J I)⁻¹, isUnit_nonsing_inv_iff.mpr hunit, rfl⟩
  · have h := pinv_eq_sum_basicInverses A.pinv ((reciprocal_rank A).trans hr)
    rw [reciprocal_involutive, Finset.sum_comm] at h
    simpa only [RCLike.ofReal_real_eq_id, id_eq, maximalMinorWeight_pinv A hr] using h
  · intro p α β
    have h := theorem_9 A.pinv ((reciprocal_rank A).trans hr) β α
    rw [reciprocal_involutive, Finset.sum_comm] at h
    simpa only [maximalMinorWeight_pinv A hr] using h

section ComplementaryDeterminants

variable {p : Type*} [Fintype p] [DecidableEq p]

/-- Equation (109) of [benIsrael2003generalized], Chapter 3.
Column β(j) is replaced by the standard vector with its unit coordinate
at α(j), and all other columns are copied from the original matrix. -/
def replaceSelectedColumns (H : Matrix p p ℝ) (α β : k ↪ p) : Matrix p p ℝ := by
  classical
  exact fun i j => if h : j ∈ Set.range β then (Pi.single (α h.choose) (1 : ℝ) : p → ℝ) i else H i j

omit [Preorder k] [DecidableEq k] [Fintype p] in
private theorem col_replaceSelectedColumns (H : Matrix p p ℝ) (α β : k ↪ p) (j : k) :
    (replaceSelectedColumns H α β).col (β j) = Pi.single (α j) 1 := by
  classical
  have h : β j ∈ Set.range β := ⟨j, rfl⟩
  have hj : h.choose = j := β.injective h.choose_spec
  funext i
  simp only [replaceSelectedColumns, col_apply, dite_eq_left h, hj]

omit [Preorder k] [DecidableEq k] [Fintype p] in
private theorem col_replaceSelectedColumns_of_not_mem (H : Matrix p p ℝ) (α β : k ↪ p)
    {j : p} (h : j ∉ Set.range β) :
    (replaceSelectedColumns H α β).col j = H.col j := by
  classical
  funext i
  simp only [replaceSelectedColumns, col_apply, dite_eq_right h]

omit [Preorder k] in
private theorem det_eq_det_submatrix_of_identity_columns (K : Matrix p p ℝ) (β : k ↪ p)
    (h : ∀ j ∉ Set.range β, K.col j = (1 : Matrix p p ℝ).col j) :
    K.det = (K.submatrix β β).det := by
  classical
  let e : k ⊕ {j : p // j ∉ Set.range β} ≃ p :=
    (Equiv.sumCongr (Equiv.ofInjective β β.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range β))
  have hleft (j : k) : e (Sum.inl j) = β j := rfl
  have hright (j : {j : p // j ∉ Set.range β}) : e (Sum.inr j) = j.val := rfl
  let B : Matrix {j : p // j ∉ Set.range β} k ℝ := fun i j => K i.val (β j)
  have he : K.submatrix e e = fromBlocks (K.submatrix β β) 0 B 1 := by
    ext (i | i) (j | j)
    · simp only [submatrix_apply, hleft, fromBlocks_apply₁₁]
    · rw [submatrix_apply, hleft, hright, fromBlocks_apply₁₂]
      have he := congrFun (h j.val j.prop) (β i)
      change K (β i) j.val = _ at he
      rw [he]
      simp [show β i ≠ j.val from fun hh => j.prop ⟨i, hh⟩]
    · rfl
    · rw [submatrix_apply, hright, hright, fromBlocks_apply₂₂]
      have he := congrFun (h j.val j.prop) i.val
      change K i.val j.val = _ at he
      rw [he]
      simp [Matrix.one_apply, Subtype.ext_iff]
  rw [← det_submatrix_equiv_self e K, he, det_fromBlocks_zero₁₂, det_one, mul_one]

omit [Preorder k] in
/-- Equation (110a) of [benIsrael2003generalized], Chapter 3.
The determinant of the matrix with the selected columns replaced is the
determinant of the corresponding inverse minor times the original determinant. -/
theorem det_replaceSelectedColumns (H : Matrix p p ℝ) (hH : IsUnit H) (α β : k ↪ p) :
    (replaceSelectedColumns H α β).det = H.det * (H⁻¹.submatrix β α).det := by
  let K := H⁻¹ * replaceSelectedColumns H α β
  have hu : IsUnit H.det := (isUnit_iff_isUnit_det _).mp hH
  have hK : H * K = replaceSelectedColumns H α β := by
    rw [show K = H⁻¹ * replaceSelectedColumns H α β from rfl,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have hother (j : p) (hj : j ∉ Set.range β) : K.col j = (1 : Matrix p p ℝ).col j := by
    rw [show K = H⁻¹ * replaceSelectedColumns H α β from rfl, col_mul_eq_mulVec_col,
      col_replaceSelectedColumns_of_not_mem _ _ _ hj, ← col_mul_eq_mulVec_col,
      Matrix.nonsing_inv_mul _ hu]
  have hKsub : K.submatrix β β = H⁻¹.submatrix β α := by
    ext i j
    simp only [submatrix_apply]
    have he : K.col (β j) = H⁻¹.col (α j) := by
      rw [show K = H⁻¹ * replaceSelectedColumns H α β from rfl, col_mul_eq_mulVec_col,
        col_replaceSelectedColumns, mulVec_single_one]
    exact congrFun he (β i)
  rw [← hK, det_mul, det_eq_det_submatrix_of_identity_columns K β hother, hKsub]

omit [Preorder k] in
/-- The Gram-normalized Jacobi identity of **Equation (110b)**. -/
theorem det_replaceSelectedColumns_gram (H : Matrix p p ℝ) (hH : IsUnit H) (α β : k ↪ p) :
    (H⁻¹.submatrix β α).det = (Hᵀ * replaceSelectedColumns H α β).det / (Hᵀ * H).det := by
  have hu : H.det ≠ 0 := ((isUnit_iff_isUnit_det _).mp hH).ne_zero
  rw [Matrix.det_mul, Matrix.det_mul, det_transpose, det_replaceSelectedColumns H hH α β]
  apply (eq_div_iff (mul_ne_zero hu hu)).mpr
  ring

/-- The index of a selected coordinate within a larger ordered selection. -/
private def embeddingWithinSelection {r : ℕ} (α : k ↪o m) (I : Fin r ↪o m)
    (h : Set.range α ⊆ Set.range I) : k ↪ Fin r where
  toFun x := (h ⟨x, rfl⟩).choose
  inj' x y hxy :=
    α.injective (((h ⟨x, rfl⟩).choose_spec.symm.trans (congrArg I hxy)).trans
      (h ⟨y, rfl⟩).choose_spec)

omit [Fintype m] [Fintype k] [DecidableEq k] in
private theorem embeddingWithinSelection_apply {r : ℕ} (α : k ↪o m) (I : Fin r ↪o m)
    (h : Set.range α ⊆ Set.range I) (x : k) :
    I (embeddingWithinSelection α I h x) = α x := (h ⟨x, rfl⟩).choose_spec

/-- The signed complementary minor occurring at the two selected subsets.
It is computed by replacing columns as in Equation (109), and is zero when
the smaller row or column selection is absent from the larger one. -/
def pivotComplementaryDet (A : Matrix m n ℝ) (I : Fin r ↪o m) (J : Fin r ↪o n)
    (α : k ↪o m) (β : k ↪o n) : ℝ := by
  classical
  exact if h : Set.range α ⊆ Set.range I ∧ Set.range β ⊆ Set.range J then
    (replaceSelectedColumns (A.submatrix I J) (embeddingWithinSelection α I h.1)
      (embeddingWithinSelection β J h.2)).det
  else 0

omit [Fintype m] [Fintype n] in
/-- A minor of a basic inverse is zero if one of its indices is absent
from the selected rows or columns of the pivot. -/
theorem basicInverse_submatrix_det_eq_zero_of_not_subset (A : Matrix m n ℝ)
    (I : Fin r ↪o m) (J : Fin r ↪o n) (α : k ↪o m) (β : k ↪o n)
    (h : ¬ (Set.range α ⊆ Set.range I ∧ Set.range β ⊆ Set.range J)) :
    ((basicInverse A I J).submatrix β α).det = 0 := by
  classical
  by_cases hα : Set.range α ⊆ Set.range I
  · have hβ : ¬ Set.range β ⊆ Set.range J := fun hf => h ⟨hα, hf⟩
    obtain ⟨j, ⟨x, rfl⟩, hj⟩ := Set.not_subset.mp hβ
    exact det_eq_zero_of_row_eq_zero x fun y => basicInverse_apply_eq_zero A I J _ _ (Or.inr hj)
  · obtain ⟨i, ⟨x, rfl⟩, hi⟩ := Set.not_subset.mp hα
    exact det_eq_zero_of_column_eq_zero x fun y => basicInverse_apply_eq_zero A I J _ _ (Or.inl hi)

omit [Fintype m] [Fintype n] in
private theorem det_sq_mul_basic_inverse (A : Matrix m n ℝ) (I : Fin r ↪o m) (J : Fin r ↪o n)
    (α : k ↪o m) (β : k ↪o n) :
    (A.submatrix I J).det ^ 2 * ((basicInverse A I J).submatrix β α).det =
      (A.submatrix I J).det * pivotComplementaryDet A I J α β := by
  classical
  let M := A.submatrix I J
  by_cases hd : M.det = 0
  · simp only [show (A.submatrix I J).det = 0 from hd, zero_pow (by decide : 2 ≠ 0), zero_mul]
  by_cases h : Set.range α ⊆ Set.range I ∧ Set.range β ⊆ Set.range J
  · let a := embeddingWithinSelection α I h.1
    let b := embeddingWithinSelection β J h.2
    have hM : IsUnit M := (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    have he : (basicInverse A I J).submatrix β α = M⁻¹.submatrix b a := by
      ext i j
      have hi : J (b i) = β i := embeddingWithinSelection_apply _ _ _ _
      have hj : I (a j) = α j := embeddingWithinSelection_apply _ _ _ _
      calc
        _ = basicInverse A I J (J (b i)) (I (a j)) :=
          congrArg₂ (basicInverse A I J) hi.symm hj.symm
        _ = _ := basicInverse_apply_selected A I.toEmbedding J.toEmbedding (a j) (b i)
    rw [he, pivotComplementaryDet, dite_eq_left h, det_replaceSelectedColumns _ hM]
    change M.det ^ 2 * (M⁻¹.submatrix b a).det =
      M.det * (M.det * (M⁻¹.submatrix b a).det)
    ring
  · rw [basicInverse_submatrix_det_eq_zero_of_not_subset A I J α β h, pivotComplementaryDet,
      dite_eq_right h, mul_zero, mul_zero]

/-- **Theorem 8**, Equation (111) of [benIsrael2003generalized], Chapter 3.
The reciprocal minor is the sum of determinants times the signed
complementary determinants in the column-replacement form of (109).
The minor vanishes when no nonsingular maximal minor contains both selections. -/
theorem theorem_8 (A : Matrix m n ℝ) (hr : A.rank = r) (α : k ↪o m) (β : k ↪o n) :
    (A.pinv.submatrix β α).det =
      (∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
        (A.submatrix I J).det * pivotComplementaryDet A I J α β) / minorWeightSum A r ∧
    ((∀ (I : Fin r ↪o m) (J : Fin r ↪o n), IsUnit (A.submatrix I J) →
      ¬ (Set.range α ⊆ Set.range I ∧ Set.range β ⊆ Set.range J)) →
      (A.pinv.submatrix β α).det = 0) := by
  classical
  have h := theorem_9 A hr α β
  refine ⟨?_, ?_⟩
  · apply (eq_div_iff (minorWeightSum_pos A hr).ne').mpr
    rw [h, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J _
    rw [maximalMinorWeight, Real.norm_eq_abs, sq_abs, mul_right_comm, div_mul_cancel₀ _
      (minorWeightSum_pos A hr).ne', det_sq_mul_basic_inverse]
  · intro hnone
    rw [h]
    apply Finset.sum_eq_zero
    intro I _
    apply Finset.sum_eq_zero
    intro J _
    by_cases hJ : IsUnit (A.submatrix I J)
    · rw [basicInverse_submatrix_det_eq_zero_of_not_subset A I J α β (hnone I J hJ), mul_zero]
    · have hz : (A.submatrix I J).det = 0 := by
        simpa only [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] using hJ
      simp [maximalMinorWeight, hz]

end ComplementaryDeterminants

section MarginalAverages

/-- **Exercise 47** of [benIsrael2003generalized], Chapter 3.
Each reciprocal minor is also the average of the minors of the padded
reciprocals of maximal column submatrices, or of maximal row submatrices. -/
theorem exercise_3_47 (A : Matrix m n ℝ) (hr : A.rank = r) (α : k ↪o m) (β : k ↪o n) :
    ((A.pinv.submatrix β α).det = ∑ J : Fin r ↪o n,
      columnSliceWeight A J * ((columnSliceInverse A J).submatrix β α).det) ∧
    ((A.pinv.submatrix β α).det = ∑ I : Fin r ↪o m,
      rowSliceWeight A I * ((rowSliceInverse A I).submatrix β α).det) := by
  have hcomp (X : Matrix n m ℝ) :
      minorRowSelector β * X * minorColumnSelector α = X.submatrix β α := by
    rw [minorRowSelector_mul, mul_minorColumnSelector, submatrix_submatrix, Function.id_comp,
      Function.comp_id]
  constructor
  · have h := pinv_compression_det_eq_sum_columnSlices A hr
      (minorColumnSelector α) (minorRowSelector β)
    rw [hcomp A.pinv] at h
    simp_rw [hcomp] at h
    exact h
  · have h := pinv_compression_det_eq_sum_rowSlices A hr
      (minorColumnSelector α) (minorRowSelector β)
    rw [hcomp A.pinv] at h
    simp_rw [hcomp] at h
    exact h

omit [Fintype n] [LinearOrder m] in
private theorem columnSliceInverse_entry_zero (A : Matrix m n ℝ)
    (J : Fin r ↪o n) {j : n} (hj : j ∉ Set.range J) (i : m) :
    columnSliceInverse A J j i = 0 := by
  have h (p : Fin r) : (minorColumnSelector (𝕜 := ℝ) J) j p = 0 := by
    have hp : j ≠ J p := fun he => hj ⟨p, he.symm⟩
    simp [minorColumnSelector, hp]
  simp [columnSliceInverse, Matrix.mul_apply, h]

omit [Fintype n] in
private theorem columnSliceDet_zero_of_not_subset (A : Matrix m n ℝ)
    (J : Fin r ↪o n) (α : k ↪o m) (β : k ↪o n) (h : ¬ Set.range β ⊆ Set.range J) :
    ((columnSliceInverse A J).submatrix β α).det = 0 := by
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := Set.not_subset.mp h
  exact det_eq_zero_of_row_eq_zero j fun i => columnSliceInverse_entry_zero A J hj (α i)

omit [Fintype m] in
private theorem rowSliceDet_zero_of_not_subset (A : Matrix m n ℝ)
    (I : Fin r ↪o m) (α : k ↪o m) (β : k ↪o n) (h : ¬ Set.range α ⊆ Set.range I) :
    ((rowSliceInverse A I).submatrix β α).det = 0 := by
  rw [rowSliceInverse, ← transpose_submatrix, det_transpose]
  exact columnSliceDet_zero_of_not_subset Aᵀ I β α h

open scoped Classical in
/-- Only selections containing the specified minor indices contribute
to the column and row averages in **Exercise 47**. -/
theorem exercise_3_47_restricted (A : Matrix m n ℝ) (hr : A.rank = r)
    (α : k ↪o m) (β : k ↪o n) :
    ((A.pinv.submatrix β α).det =
      ∑ J ∈ Finset.univ.filter (fun J : Fin r ↪o n => Set.range β ⊆ Set.range J),
        columnSliceWeight A J * ((columnSliceInverse A J).submatrix β α).det) ∧
    ((A.pinv.submatrix β α).det =
      ∑ I ∈ Finset.univ.filter (fun I : Fin r ↪o m => Set.range α ⊆ Set.range I),
        rowSliceWeight A I * ((rowSliceInverse A I).submatrix β α).det) := by
  classical
  obtain ⟨hcol, hrow⟩ := exercise_3_47 A hr α β
  constructor
  · rw [hcol, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro J _
    by_cases hJ : Set.range β ⊆ Set.range J
    · simp only [ite_eq_left hJ]
    · simp only [ite_eq_right hJ, columnSliceDet_zero_of_not_subset A J α β hJ, mul_zero]
  · rw [hrow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I _
    by_cases hI : Set.range α ⊆ Set.range I
    · simp only [ite_eq_left hI]
    · simp only [ite_eq_right hI, rowSliceDet_zero_of_not_subset A I α β hI, mul_zero]

/-- The reciprocal minor vanishes when either of its index sets is in no
full-rank row or column selection. -/
theorem exercise_3_47_zero (A : Matrix m n ℝ) (hr : A.rank = r)
    (α : k ↪o m) (β : k ↪o n)
    (h : (∀ I : Fin r ↪o m, (A.submatrix I id).rank = r →
        ¬ Set.range α ⊆ Set.range I) ∨
      (∀ J : Fin r ↪o n, (A.submatrix id J).rank = r →
        ¬ Set.range β ⊆ Set.range J)) :
    (A.pinv.submatrix β α).det = 0 := by
  apply (theorem_8 A hr α β).2
  intro I J hU hsubset
  have hPivot : (A.submatrix I J).rank = r := (rank_of_isUnit _ hU).trans (Fintype.card_fin r)
  rcases h with hi | hj
  · have hle := rank_submatrix_le (A.submatrix I id) id J
    change (A.submatrix I J).rank ≤ (A.submatrix I id).rank at hle
    rw [hPivot] at hle
    exact hi I (le_antisymm (by simpa using rank_le_card_height (A.submatrix I id)) hle) hsubset.1
  · have hle := rank_submatrix_le (A.submatrix id J) I id
    change (A.submatrix I J).rank ≤ (A.submatrix id J).rank at hle
    rw [hPivot] at hle
    exact hj J (le_antisymm (by simpa using rank_le_card_width (A.submatrix id J)) hle) hsubset.2

end MarginalAverages

end BenIsraelGreville.Chapter03
