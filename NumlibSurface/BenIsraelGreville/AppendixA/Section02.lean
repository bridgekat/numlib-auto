/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import NumlibSurface.BenIsraelGreville.Chapter03.Section05
import Mathlib.Order.Hom.PowersetCard
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# Moore's 1920 general reciprocal

Appendix A, §2 of [benIsrael2003generalized] characterizes the reciprocal
by its row and column spaces and the inner-inverse equation.
-/

noncomputable section

namespace BenIsraelGreville.AppendixA

open Matrix

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- The column space, in Euclidean coordinates. -/
abbrev columnSpace (A : Matrix m n ℂ) := LinearMap.range (Matrix.toEuclideanLin A)

/-- **Conditions (1)–(3)** of [benIsrael2003generalized], Appendix A, §2.
The columns and conjugate rows of the reciprocal belong to the prescribed
spaces, and it is an inner inverse. -/
def IsMooreReciprocal (A : Matrix m n ℂ) (X : Matrix n m ℂ) : Prop :=
  columnSpace X ≤ columnSpace Aᴴ ∧ columnSpace Xᴴ ≤ columnSpace A ∧ A.IsInnerInverse X

omit [Fintype m] [DecidableEq m] in
/-- The column space of a product lies in that of the left factor. -/
theorem columnSpace_mul_le (A : Matrix m n ℂ) (B : Matrix n k ℂ) :
    columnSpace (A * B) ≤ columnSpace A := by
  rintro _ ⟨x, rfl⟩
  exact ⟨toEuclideanLin B x, toEuclideanLin_mul_apply _ _ _ |>.symm⟩

/-- The Moore–Penrose inverse has the column space of the adjoint. -/
theorem columnSpace_pinv (A : Matrix m n ℂ) :
    columnSpace A.pinv = columnSpace Aᴴ := by
  have hP : columnSpace (A.pinv * A) = columnSpace Aᴴ := by
    rw [columnSpace, A.pinv_mul_eq_starProjection]
    exact (columnSpace Aᴴ).range_starProjection
  apply le_antisymm
  · have h := columnSpace_mul_le (A.pinv * A) A.pinv
    rwa [A.pinv_mul_self_mul_pinv, hP] at h
  · rw [← A.pinv_mul_self_mul_conjTranspose]
    exact (columnSpace_mul_le (A.pinv * A) Aᴴ).trans (columnSpace_mul_le A.pinv A)

omit [DecidableEq m] in
/-- The adjoint of the reciprocal has the column space of the original matrix. -/
theorem columnSpace_pinv_conjTranspose (A : Matrix m n ℂ) :
    columnSpace A.pinvᴴ = columnSpace A := by
  classical
  rw [← A.pinv_conjTranspose, columnSpace_pinv, conjTranspose_conjTranspose]

/-- A projection onto the column space of the adjoint fixes any matrix with
columns in that space. -/
theorem pinv_mul_mul_eq_of_columnSpace_le {A : Matrix m n ℂ} {X : Matrix n k ℂ}
    (hX : columnSpace X ≤ columnSpace Aᴴ) : A.pinv * A * X = X := by
  apply (toEuclideanLin : Matrix n k ℂ ≃ₗ[ℂ] _).injective
  ext1 y
  rw [toEuclideanLin_mul_apply, A.pinv_mul_eq_starProjection]
  exact (columnSpace Aᴴ).starProjection_eq_self_iff.mpr (hX ⟨y, rfl⟩)

omit [DecidableEq m] in
/-- A projection onto the column space of a matrix fixes any matrix with
columns in that space. -/
theorem mul_pinv_mul_eq_of_columnSpace_le {A : Matrix m n ℂ} {X : Matrix m k ℂ}
    (hX : columnSpace X ≤ columnSpace A) : A * A.pinv * X = X := by
  classical
  apply (toEuclideanLin : Matrix m k ℂ ≃ₗ[ℂ] _).injective
  ext1 y
  rw [toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection]
  exact (columnSpace A).starProjection_eq_self_iff.mpr (hX ⟨y, rfl⟩)

/-- **Conditions (1)–(3)** determine the Moore–Penrose inverse. -/
theorem isMooreReciprocal_iff {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    IsMooreReciprocal A X ↔ X = A.pinv := by
  constructor
  · rintro ⟨hX, hX', hAXA⟩
    have hL := pinv_mul_mul_eq_of_columnSpace_le hX
    have hR : X * (A * A.pinv) = X := by
      apply conjTranspose_injective
      rw [conjTranspose_mul, A.isHermitian_mul_pinv.eq]
      exact mul_pinv_mul_eq_of_columnSpace_le hX'
    calc
      X = A.pinv * (A * X * A) * A.pinv := by
        rw [show A.pinv * (A * X * A) * A.pinv = (A.pinv * A * X) * (A * A.pinv) by
          simp only [Matrix.mul_assoc], hL, hR]
      _ = A.pinv := by rw [hAXA, A.pinv_mul_self_mul_pinv]
  · rintro rfl
    exact ⟨(columnSpace_pinv A).le, (columnSpace_pinv_conjTranspose A).le, A.mul_pinv_mul_self⟩

/-- Each complex matrix has a unique reciprocal in Moore's 1920 definition. -/
theorem existsUnique_mooreReciprocal (A : Matrix m n ℂ) :
    ∃! X, IsMooreReciprocal A X :=
  ⟨A.pinv, isMooreReciprocal_iff.mpr rfl, fun _ h => isMooreReciprocal_iff.mp h⟩

/-- **Conditions (4)–(6)** of [benIsrael2003generalized], Appendix A, §2.
The reciprocal relation is mutual. Both column-space inclusions are equalities. -/
theorem IsMooreReciprocal.mutual {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (h : IsMooreReciprocal A X) :
    IsMooreReciprocal X A ∧ columnSpace X = columnSpace Aᴴ ∧ columnSpace Xᴴ = columnSpace A := by
  rw [isMooreReciprocal_iff] at h
  subst X
  exact ⟨⟨(columnSpace_pinv_conjTranspose A).ge, (columnSpace_pinv A).ge, A.pinv_mul_self_mul_pinv⟩,
    columnSpace_pinv A, columnSpace_pinv_conjTranspose A⟩

variable (A : Matrix m n ℂ)

/-- The forward and inverse column actions give Moore's one-to-one linear
correspondence between the column spaces of the adjoint and of the matrix. -/
def mooreReciprocal_range_equiv : columnSpace Aᴴ ≃ₗ[ℂ] columnSpace A where
  toFun x := ⟨toEuclideanLin A x, ⟨x, rfl⟩⟩
  invFun y := ⟨toEuclideanLin A.pinv y, (columnSpace_pinv A).le ⟨y, rfl⟩⟩
  left_inv x := Subtype.ext <| by
    change toEuclideanLin A.pinv (toEuclideanLin A x.val) = x.val
    rw [← toEuclideanLin_mul_apply, A.pinv_mul_eq_starProjection]
    exact (columnSpace Aᴴ).starProjection_eq_self_iff.mpr x.2
  right_inv y := Subtype.ext <| by
    change toEuclideanLin A (toEuclideanLin A.pinv y.val) = y.val
    rw [← toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection]
    exact (columnSpace A).starProjection_eq_self_iff.mpr y.2
  map_add' x y := Subtype.ext (map_add (toEuclideanLin A) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (toEuclideanLin A) c x.val)

/-- The reciprocal commutes with transposition, so the same correspondence
can be written using row vectors without changing scalars. -/
theorem pinv_transpose : Aᵀ.pinv = A.pinvᵀ :=
  Chapter01.pinv_transpose A

/-- In row coordinates Moore's correspondence is right multiplication by
the matrix, with right multiplication by the reciprocal as its inverse. -/
def mooreReciprocal_right_range_equiv : columnSpace Aᵀᴴ ≃ₗ[ℂ] columnSpace Aᵀ :=
  mooreReciprocal_range_equiv Aᵀ

/-- The forward row action in the right correspondence. -/
theorem mooreReciprocal_right_range_equiv_apply (x : columnSpace Aᵀᴴ) :
    (mooreReciprocal_right_range_equiv A x).val = toEuclideanLin Aᵀ x.val := rfl

/-- The inverse row action in the right correspondence. -/
theorem mooreReciprocal_right_range_equiv_symm_apply (y : columnSpace Aᵀ) :
    ((mooreReciprocal_right_range_equiv A).symm y).val = toEuclideanLin A.pinvᵀ y.val := by
  change toEuclideanLin Aᵀ.pinv y.val = _
  rw [pinv_transpose]

omit [DecidableEq m] in
/-- The rank-zero reciprocal in the 1920 lecture. -/
theorem mooreReciprocal_rank_zero (h : A.rank = 0) : A.pinv = 0 := by
  rw [rank_eq_zero_iff.mp h]
  exact (pinv_unique (0 : Matrix m n ℂ) (by simp) (by simp)
    (by simp [IsHermitian]) (by simp [IsHermitian])).symm

/-- The sum of squared moduli of the entries, the denominator in the
rank-one case of the 1920 formula. -/
def reciprocalRankOneDenominator : ℂ :=
  ∑ i, ∑ j, star (A i j) * A i j

omit [DecidableEq m] [DecidableEq n] in
private theorem reciprocalRankOneDenominator_star :
    star (reciprocalRankOneDenominator A) = reciprocalRankOneDenominator A := by
  simp [reciprocalRankOneDenominator, star_sum, star_mul]

omit [DecidableEq m] [DecidableEq n] in
private theorem reciprocalRankOneDenominator_ne_zero (hA : A ≠ 0) :
    reciprocalRankOneDenominator A ≠ 0 := by
  have hcast : reciprocalRankOneDenominator A = ((∑ i, ∑ j, Complex.normSq (A i j) : ℝ) : ℂ) := by
    simp [reciprocalRankOneDenominator, Complex.normSq_eq_conj_mul_self]
  intro h
  rw [hcast, Complex.ofReal_eq_zero] at h
  apply hA
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    Finset.sum_nonneg fun l _ => Complex.normSq_nonneg (A k l))).mp h i (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun l _ => Complex.normSq_nonneg (A i l))).mp hi j
      (Finset.mem_univ j))

omit [DecidableEq m] [DecidableEq n] in
private theorem mul_adjoint_mul_of_rank_one (hr : A.rank = 1) :
    A * Aᴴ * A = reciprocalRankOneDenominator A • A := by
  have hcross (i k : m) (j l : n) : A i l * A k j = A k l * A i j := by
    have hd : (A.submatrix ![i, k] ![j, l]).det = 0 := by
      by_contra hn
      have := A.card_le_rank_of_det_submatrix_ne_zero hn
      omega
    rw [Matrix.det_fin_two] at hd
    change A i j * A k l - A i l * A k j = 0 at hd
    rw [mul_comm (A k l) (A i j)]
    exact (sub_eq_zero.mp hd).symm
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    smul_eq_mul, reciprocalRankOneDenominator, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  calc
    A i k * star (A l k) * A l j = star (A l k) * (A i k * A l j) := by ring
    _ = star (A l k) * A l k * A i j := by rw [hcross]; ring

omit [DecidableEq m] in
/-- In rank one the reciprocal is the conjugate transpose divided by the
sum of squared moduli of all entries, as in Moore's 1920 lecture. -/
theorem mooreReciprocal_rank_one (hr : A.rank = 1) (i : m) (j : n) :
    A.pinv j i = star (A i j) / reciprocalRankOneDenominator A := by
  let d := reciprocalRankOneDenominator A
  have hd : d ≠ 0 := reciprocalRankOneDenominator_ne_zero A (by
    intro hz
    rw [hz, Matrix.rank_zero] at hr
    omega)
  have he : A * Aᴴ * A = d • A := mul_adjoint_mul_of_rank_one A hr
  have hstar : star d = d := reciprocalRankOneDenominator_star A
  have her : Aᴴ * A * Aᴴ = d • Aᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul,
      hstar, Matrix.mul_assoc] using congrArg Matrix.conjTranspose he
  have hA : (d⁻¹ • Aᴴ : Matrix n m ℂ) = A.pinv := by
    apply A.pinv_unique
    · rw [Matrix.mul_smul, Matrix.smul_mul, he, smul_smul, inv_mul_cancel₀ hd, one_smul]
    · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, her]
      simp only [smul_smul, inv_mul_cancel₀ hd, mul_one]
    · rw [Matrix.mul_smul, IsHermitian, conjTranspose_smul, star_inv₀, hstar,
        (Matrix.isHermitian_mul_conjTranspose_self A).eq]
    · rw [Matrix.smul_mul, IsHermitian, conjTranspose_smul, star_inv₀, hstar,
        (Matrix.isHermitian_conjTranspose_mul_self A).eq]
  rw [← hA]
  exact mul_comm _ _

/-- For nonsingular square matrices the maximal-minor sum has one nonzero
candidate in the numerator and one term in the denominator. Moving row
(i) and column (j) to the front gives the ordered minor in the numerator. -/
theorem mooreReciprocal_minorSums_square {d : ℕ} (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hB : IsUnit B) (i j : Fin (d + 1)) :
    B.pinv j i = (B.submatrix i.succAbove j.succAbove).det *
      star (B.submatrix (Fin.cons i i.succAbove) (Fin.cons j j.succAbove)).det /
        (star B.det * B.det) := by
  have hrow : Fin.cons i i.succAbove = (i.cycleRange.symm : Fin (d + 1) → Fin (d + 1)) := by
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero, Fin.cycleRange_symm_zero]
    · simp only [Fin.cons_succ, Fin.cycleRange_symm_succ]
  have hcol : Fin.cons j j.succAbove = (j.cycleRange.symm : Fin (d + 1) → Fin (d + 1)) := by
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero, Fin.cycleRange_symm_zero]
    · simp only [Fin.cons_succ, Fin.cycleRange_symm_succ]
  have hdet : (B.submatrix (Fin.cons i i.succAbove) (Fin.cons j j.succAbove)).det =
      (-1 : ℂ) ^ (i.val + j.val) * B.det := by
    rw [hrow, hcol, ← show (B.submatrix i.cycleRange.symm id).submatrix id j.cycleRange.symm =
      B.submatrix i.cycleRange.symm j.cycleRange.symm by simp only [submatrix_submatrix,
        Function.id_comp, Function.comp_id], det_permute', det_permute]
    simp [Fin.sign_cycleRange, pow_add, mul_left_comm, mul_assoc]
  have hne : B.det ≠ 0 := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hB)
  have hne' : star B.det ≠ 0 := fun h => hne (star_eq_zero.mp h)
  rw [pinv_eq_inv hB, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_fin_succ_eq_det_submatrix, hdet, star_mul, star_pow, star_neg, star_one]
  field_simp

end BenIsraelGreville.AppendixA

namespace BenIsraelGreville.AppendixA

section OrderedComplement

open Matrix Chapter03

variable {d : ℕ} {s : Type*} [Fintype s] [LinearOrder s]

private def eraseSelectedIndex (i : s) (I : {I : Fin (d + 1) ↪o s // i ∈ Set.range I}) :
    Fin d ↪o s :=
  (Fin.succAboveOrderEmb I.prop.choose).trans I.val

omit [Fintype s] in
private theorem range_eraseSelectedIndex (i : s)
    (I : {I : Fin (d + 1) ↪o s // i ∈ Set.range I}) :
    Set.range (eraseSelectedIndex i I) = Set.range I.val \ {i} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨⟨I.prop.choose.succAbove a, rfl⟩, ?_⟩
    intro h
    have he : I.val (I.prop.choose.succAbove a) = i := h
    exact I.prop.choose.succAbove_ne a (I.val.injective (he.trans I.prop.choose_spec.symm))
  · rintro ⟨⟨a, rfl⟩, h⟩
    have hne : a ≠ I.prop.choose := by
      intro he
      exact h ((congrArg I.val he).trans I.prop.choose_spec)
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hne
    exact ⟨b, congrArg I.val hb⟩

omit [Fintype s] in
private theorem orderEmbedding_eq_of_range_eq {q : ℕ} {I J : Fin q ↪o s}
    (h : Set.range I = Set.range J) : I = J := by
  apply Set.powersetCard.ofFinEmbEquiv.injective
  ext x
  change x ∈ Set.powersetCard.ofFinEmbEquiv I ↔ x ∈ Set.powersetCard.ofFinEmbEquiv J
  simp only [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range, h]

private def eraseSelectedIndexEquiv (i : s) :
    {I : Fin (d + 1) ↪o s // i ∈ Set.range I} ≃ {I : Fin d ↪o s // i ∉ Set.range I} :=
  Equiv.ofBijective
    (fun I => ⟨eraseSelectedIndex i I, by rw [range_eraseSelectedIndex]; simp⟩) (by
      constructor
      · intro I J h
        apply Subtype.ext
        apply orderEmbedding_eq_of_range_eq
        have he := congrArg (fun K : {K : Fin d ↪o s // i ∉ Set.range K} => Set.range K.val) h
        change Set.range (eraseSelectedIndex i I) = Set.range (eraseSelectedIndex i J) at he
        rw [range_eraseSelectedIndex, range_eraseSelectedIndex] at he
        ext x
        by_cases hi : x = i
        · subst x
          exact iff_of_true I.prop J.prop
        · have hp : x ∉ ({i} : Set s) := hi
          have hx := Set.ext_iff.mp he x
          simpa only [Set.mem_sdiff, hp, not_false_eq_true, and_true] using hx
      · intro I
        let S := Finset.univ.image I.val
        have hnot : i ∉ S := by
          intro hi
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
          exact I.prop ⟨j, hj⟩
        have hcard : (insert i S).card = d + 1 := by
          rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ I.val.injective,
            Finset.card_univ, Fintype.card_fin]
        let J := (insert i S).orderEmbOfFin hcard
        have hJ : Set.range J = ↑(insert i S) := Finset.range_orderEmbOfFin _ _
        have hmem : i ∈ Set.range J := by
          rw [hJ]
          exact Finset.mem_insert_self _ _
        refine ⟨⟨J, hmem⟩, Subtype.ext (orderEmbedding_eq_of_range_eq ?_)⟩
        rw [range_eraseSelectedIndex, hJ]
        ext x
        simp only [Finset.coe_insert, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        have hx : x ∈ (S : Set s) ↔ x ∈ Set.range I.val := by
          simp [S, Set.mem_range]
        rw [hx]
        constructor
        · exact fun h => h.1.resolve_left h.2
        · intro h
          exact ⟨Or.inr h, fun he => I.prop (he ▸ h)⟩)

omit [Fintype s] in
private theorem cons_eraseSelectedIndex (i : s)
    (I : {I : Fin (d + 1) ↪o s // i ∈ Set.range I}) :
    Fin.cons i (eraseSelectedIndex i I) = I.val ∘ I.prop.choose.cycleRange.symm := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Fin.cons_zero, Function.comp_apply, Fin.cycleRange_symm_zero]
    exact I.prop.choose_spec.symm
  · simp only [Fin.cons_succ, Function.comp_apply, Fin.cycleRange_symm_succ]
    rfl

private theorem sum_over_subtype_of_zero {ι : Type*} [Fintype ι] {R : Type*} [AddCommMonoid R]
    (P : ι → Prop) [DecidablePred P] (f : ι → R) (h : ∀ i, ¬ P i → f i = 0) :
    ∑ i, f i = ∑ i : {i // P i}, f i := by
  rw [← Fintype.sum_subtype_add_sum_subtype P f,
    (Finset.sum_eq_zero fun i _ => h i.val i.prop : (∑ i : {i // ¬ P i}, f i) = 0), add_zero]

private theorem doubleSum_over_subtypes_of_zero
    {ι κ R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (P : ι → Prop) [DecidablePred P] (Q : κ → Prop) [DecidablePred Q]
    (f : ι → κ → R) (h : ∀ i j, ¬ P i ∨ ¬ Q j → f i j = 0) :
    (∑ i, ∑ j, f i j) = ∑ i : {i // P i}, ∑ j : {j // Q j}, f i j := by
  rw [sum_over_subtype_of_zero P (fun i => ∑ j, f i j)
    (fun i hi => Finset.sum_eq_zero fun j _ => h i j (Or.inl hi))]
  exact Finset.sum_congr rfl fun i _ =>
    sum_over_subtype_of_zero Q (f i) (fun j hj => h i j (Or.inr hj))

variable {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]

omit [Fintype m] [Fintype n] in
private theorem prepended_minor_eq_signed_det
    (A : Matrix m n ℂ) (i : m) (j : n)
    (I : {I : Fin (d + 1) ↪o m // i ∈ Set.range I})
    (J : {J : Fin (d + 1) ↪o n // j ∈ Set.range J}) :
    (A.submatrix (Fin.cons i (eraseSelectedIndex i I)) (Fin.cons j (eraseSelectedIndex j J))).det =
      (-1 : ℂ) ^ (I.prop.choose.val + J.prop.choose.val) * (A.submatrix I.val J.val).det := by
  let M := A.submatrix I.val J.val
  let p := I.prop.choose
  let q := J.prop.choose
  rw [cons_eraseSelectedIndex, cons_eraseSelectedIndex]
  change (M.submatrix p.cycleRange.symm q.cycleRange.symm).det = _
  rw [← show (M.submatrix p.cycleRange.symm id).submatrix id q.cycleRange.symm =
      M.submatrix p.cycleRange.symm q.cycleRange.symm by simp only [submatrix_submatrix,
        Function.id_comp, Function.comp_id], det_permute', det_permute]
  simp [p, q, M, Fin.sign_cycleRange, pow_add, mul_left_comm, mul_assoc]

omit [Fintype m] [Fintype n] in
private theorem padded_inv_weight_eq_complement_term
    (A : Matrix m n ℂ) (i : m) (j : n)
    (I : {I : Fin (d + 1) ↪o m // i ∈ Set.range I})
    (J : {J : Fin (d + 1) ↪o n // j ∈ Set.range J}) :
    ((‖(A.submatrix I.val J.val).det‖ ^ 2 : ℝ) : ℂ) * basicInverse A I.val J.val j i =
      (A.submatrix (eraseSelectedIndex i I) (eraseSelectedIndex j J)).det *
        star (A.submatrix (Fin.cons i (eraseSelectedIndex i I))
          (Fin.cons j (eraseSelectedIndex j J))).det := by
  let M := A.submatrix I.val J.val
  let p := I.prop.choose
  let q := J.prop.choose
  have hb : basicInverse A I.val J.val j i = M⁻¹ q p := calc
    basicInverse A I.val J.val j i = basicInverse A I.val J.val (J.val q) (I.val p) :=
      congrArg₂ (basicInverse A I.val J.val) J.prop.choose_spec.symm I.prop.choose_spec.symm
    _ = _ := basicInverse_apply_selected A I.val.toEmbedding J.val.toEmbedding p q
  have hcomp : A.submatrix (eraseSelectedIndex i I) (eraseSelectedIndex j J) =
      M.submatrix p.succAbove q.succAbove := rfl
  have hcast (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hb, hcomp, prepended_minor_eq_signed_det, hcast]
  change star M.det * M.det * M⁻¹ q p = _ * star ((-1 : ℂ) ^ (p.val + q.val) * M.det)
  simp only [star_mul, star_pow, star_neg, star_one]
  by_cases hM : M.det = 0
  · simp [hM]
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  field_simp

/-- The general maximal-minor formula of [benIsrael2003generalized],
Appendix A, §2. The rows and columns in the smaller minor are increasing.
The indicated row and column are prepended in the conjugated determinant. -/
theorem mooreReciprocal_eq_minorSums (A : Matrix m n ℂ) (hr : A.rank = d + 1)
    (i : m) (j : n) :
    A.pinv j i =
      (∑ I : Fin d ↪o m, ∑ J : Fin d ↪o n, (A.submatrix I J).det *
        star (A.submatrix (Fin.cons i I) (Fin.cons j J)).det) /
        (minorWeightSum A (d + 1) : ℂ) := by
  classical
  let w := minorWeightSum A (d + 1)
  have hw : w ≠ 0 := by
    intro hz
    have h := (maximalMinorWeight_convex A hr).2
    simp [maximalMinorWeight, show minorWeightSum A (d + 1) = 0 from hz] at h
  have hw' : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  let f (I : Fin (d + 1) ↪o m) (J : Fin (d + 1) ↪o n) :=
    ((‖(A.submatrix I J).det‖ ^ 2 : ℝ) : ℂ) * basicInverse A I J j i
  let g (I : Fin d ↪o m) (J : Fin d ↪o n) :=
    (A.submatrix I J).det * star (A.submatrix (Fin.cons i I) (Fin.cons j J)).det
  apply (eq_div_iff hw').mpr
  have h := congrArg (fun X : Matrix n m ℂ => X j i) (pinv_eq_sum_basicInverses A hr)
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  calc
    A.pinv j i * (w : ℂ) = ∑ I, ∑ J, f I J := by
      rw [h, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro J _
      let t := ((‖(A.submatrix I J).det‖ ^ 2 : ℝ) : ℂ)
      have hc : (RCLike.ofReal (maximalMinorWeight A I J) : ℂ) = t / (w : ℂ) := by
        rw [RCLike.ofReal_eq_complex_ofReal]
        exact Complex.ofReal_div _ _
      calc
        _ = (t / (w : ℂ)) * basicInverse A I J j i * (w : ℂ) :=
          congrArg (fun a : ℂ => a * basicInverse A I J j i * (w : ℂ)) hc
        _ = f I J := by
          change (t / (w : ℂ)) * basicInverse A I J j i * (w : ℂ) =
            t * basicInverse A I J j i
          field_simp
    _ = ∑ I : {I : Fin (d + 1) ↪o m // i ∈ Set.range I},
          ∑ J : {J : Fin (d + 1) ↪o n // j ∈ Set.range J}, f I J := by
      apply doubleSum_over_subtypes_of_zero
      intro I J hmiss
      simp only [f, basicInverse_apply_eq_zero A I J i j hmiss, mul_zero]
    _ = ∑ I : {I : Fin d ↪o m // i ∉ Set.range I},
          ∑ J : {J : Fin d ↪o n // j ∉ Set.range J}, g I J := by
      rw [← (eraseSelectedIndexEquiv i).sum_comp]
      apply Finset.sum_congr rfl
      intro I _
      rw [← (eraseSelectedIndexEquiv j).sum_comp]
      exact Finset.sum_congr rfl fun J _ => padded_inv_weight_eq_complement_term A i j I J
    _ = ∑ I, ∑ J, g I J := by
      symm
      apply doubleSum_over_subtypes_of_zero
      intro I J hmiss
      have hz : (A.submatrix (Fin.cons i I) (Fin.cons j J)).det = 0 := by
        rcases hmiss with hI | hJ
        · obtain ⟨a, ha⟩ := not_not.mp hI
          apply Matrix.det_zero_of_row_eq (Fin.succ_ne_zero a)
          funext q
          simp [ha]
        · obtain ⟨b, hb⟩ := not_not.mp hJ
          apply Matrix.det_zero_of_column_eq (Fin.succ_ne_zero b)
          intro p
          simp [hb]
      simp [g, hz]

end OrderedComplement

end BenIsraelGreville.AppendixA
