/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
theorem pinv_transpose : Aᵀ.pinv = A.pinvᵀ := by
  symm
  apply Aᵀ.pinv_unique
  · rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, A.mul_pinv_mul_self]
  · rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]
  · rw [← transpose_mul, IsHermitian,
      conjTranspose_transpose_eq_transpose_conjTranspose, A.isHermitian_pinv_mul.eq]
  · rw [← transpose_mul, IsHermitian,
      conjTranspose_transpose_eq_transpose_conjTranspose, A.isHermitian_mul_pinv.eq]

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
