/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section02
import NumlibSurface.BenIsraelGreville.Chapter00.Section03
import NumlibSurface.BenIsraelGreville.Chapter00.Section04
import Numlib.LinearAlgebra.Matrix.CauchyBinet
import Numlib.LinearAlgebra.Matrix.QR
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinants and volume

Section 0.5 of [benIsrael2003generalized] characterizes the determinant by the
scaling law and multiplicativity, applies Cauchy–Binet to Gram matrices, and
defines the volume of a real matrix using its maximal nonsingular minors.

## Deviations from the source

* **Definition 2** (reading). The characterization assumes positive matrix size.
  In size zero the scaling law is vacuous.
* **Equation (87)** (typo). The selected columns belong to the left factor and
  the selected rows belong to the right factor.
* **Exercise 58(a)–(b)** (reading). The two indices of the elementary row
  operations are distinct.
-/

namespace BenIsraelGreville.Chapter00

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equation (86)** of [benIsrael2003generalized], Chapter 0. The determinant
is the signed sum of products over the permutations of the rows. -/
theorem det_eq_sum_perm (A : Matrix n n ℂ) :
    A.det = ∑ π : Equiv.Perm n, (Equiv.Perm.sign π : ℂ) * ∏ i, A (π i) i :=
  det_apply' A

/-- **Definition 2** of [benIsrael2003generalized], Chapter 0. A determinant is
multiplicative and takes the value $a$ on the elementary scaling by $a$. -/
structure IsDeterminant (f : Matrix n n ℂ → ℂ) : Prop where
  scale : ∀ i (a : ℂ), f (scaleRowMatrix i a) = a
  mul : ∀ A B, f (A * B) = f A * f B

private theorem det_scaleRowMatrix (i : n) (a : ℂ) : (scaleRowMatrix i a).det = a := by
  rw [scaleRowMatrix, Matrix.rowScale, det_diagonal, Fintype.prod_eq_single i]
  · simp
  · intro j hj
    simp [hj]

private theorem rowScale_mul_addRowMatrix (i j : n) (hij : i ≠ j) (b : ℂ) :
    scaleRowMatrix i (2 : ℂ) * addRowMatrix i j b =
      addRowMatrix i j (2 * b) * scaleRowMatrix i 2 := by
  ext u v
  simp only [scaleRowMatrix, Matrix.rowScale, addRowMatrix, Matrix.transvection,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.single, Matrix.of_apply]
  by_cases h : i = u ∧ j = v
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, hij.symm]
  · simp only [ite_eq_right h, add_zero]
    by_cases he : u = v
    · subst v
      simp
    · simp [he]

private theorem IsDeterminant.val_transvection {f : Matrix n n ℂ → ℂ}
    (hf : IsDeterminant f) (i j : n) (hij : i ≠ j) (b : ℂ) :
    f (addRowMatrix i j b) = 1 := by
  let T := addRowMatrix i j b
  have hOne : f 1 = 1 := by simpa only [scaleRowMatrix, Matrix.rowScale_one] using hf.scale i 1
  have hT : f T ≠ 0 := by
    intro h
    have he := hf.mul T (addRowMatrix i j (-b))
    rw [show T * addRowMatrix i j (-b) = 1 from by
      change Matrix.transvection i j b * Matrix.transvection i j (-b) = 1
      rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
        Matrix.transvection_zero], hOne, h, zero_mul] at he
    exact one_ne_zero he
  have hscale := congrArg f (rowScale_mul_addRowMatrix i j hij b)
  rw [hf.mul, hf.mul, hf.scale] at hscale
  have hsame : f T = f (addRowMatrix i j (2 * b)) := by
    apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
    rw [mul_comm (2 : ℂ) (f (addRowMatrix i j (2 * b)))]
    exact hscale
  have hSquare := hf.mul T T
  have hTprod : T * T = addRowMatrix i j (2 * b) := by
    change Matrix.transvection i j b * Matrix.transvection i j b =
      Matrix.transvection i j (2 * b)
    rw [Matrix.transvection_mul_transvection_same i j hij, two_mul]
  rw [hTprod, ← hsame] at hSquare
  apply mul_left_cancel₀ hT
  rw [mul_one, ← hSquare]

/-- The scaling law and multiplicativity characterize the determinant for a
positive matrix size. -/
theorem isDeterminant_iff_eq_det [Nonempty n] (f : Matrix n n ℂ → ℂ) :
    IsDeterminant f ↔ f = Matrix.det := by
  constructor
  · intro hf
    have hOne : f 1 = 1 := by
      obtain ⟨i⟩ := ‹Nonempty n›
      simpa only [scaleRowMatrix, Matrix.rowScale_one] using hf.scale i 1
    funext A
    apply diagonal_transvection_induction (fun B => f B = B.det) A
    · intro D _
      have h (s : Finset n) :
          f (diagonal (fun j => if j ∈ s then D j else 1)) =
            (diagonal (fun j => if j ∈ s then D j else 1)).det := by
        induction s using Finset.induction_on with
        | empty => simp [hOne]
        | insert i s hi ih =>
            rw [diagonal_insert_eq_scale_mul D s i hi, hf.mul, det_mul, hf.scale,
              det_scaleRowMatrix, ih]
      simpa using h Finset.univ
    · intro t
      change f (addRowMatrix t.i t.j t.c) = (addRowMatrix t.i t.j t.c).det
      rw [hf.val_transvection t.i t.j t.hij, Matrix.det_transvection_of_ne t.i t.j t.hij]
    · intro B C hB hC
      rw [hf.mul, det_mul, hB, hC]
  · rintro rfl
    exact ⟨det_scaleRowMatrix, Matrix.det_mul⟩

/-- **Exercise 58(a)–(b)** of [benIsrael2003generalized], Chapter 0. A row
addition has determinant one and a swap of distinct rows has determinant
minus one. -/
theorem det_elementaryRow (i j : n) (hij : i ≠ j) (b : ℂ) :
    (addRowMatrix i j b).det = 1 ∧ (swapRowMatrix (K := ℂ) i j).det = -1 := by
  have hadd (u v : n) (huv : u ≠ v) (a : ℂ) : (addRowMatrix u v a).det = 1 :=
    det_transvection_of_ne u v huv a
  refine ⟨hadd i j hij b, ?_⟩
  rw [exercise_49_b i j hij]
  simp only [det_mul, det_scaleRowMatrix, hadd i j hij, hadd j i hij.symm, mul_one]

/-- **Equation (90)** of [benIsrael2003generalized], Chapter 0. The determinant
of a product of elementary matrices is the product of their determinants. -/
theorem det_listProd (E : List (Matrix n n ℂ)) :
    E.prod.det = (E.map Matrix.det).prod := by
  induction E with
  | nil => simp
  | cons A E ih => simp [det_mul, ih]

/-- **Exercise 58(d)** of [benIsrael2003generalized], Chapter 0. The two
matrices in Exercise 54(b) have determinants $3$ and $0$. -/
theorem exercise_58_d :
    (!![1, 2, 3; 4, 5, 6; 7, 8, 8] : Matrix (Fin 3) (Fin 3) ℂ).det = 3 ∧
      (!![1, 2, 3; 4, 5, 6; 7, 8, 9] : Matrix (Fin 3) (Fin 3) ℂ).det = 0 := by
  norm_num [Matrix.det_fin_three]

/-- **Equation (92)** of [benIsrael2003generalized], Chapter 0. The coordinates
of the solution of a nonsingular system are ratios of determinants. -/
theorem cramer_rule {A : Matrix n n ℂ} (hA : IsUnit A) {b x : n → ℂ}
    (hx : A *ᵥ x = b) (j : n) : x j = (A.updateCol j b).det / A.det := by
  have hd := (isUnit_iff_isUnit_det A).mp hA
  have hx' : A⁻¹ *ᵥ b = x := by
    rw [← hx, mulVec_mulVec, nonsing_inv_mul _ hd, one_mulVec]
  have h := congrFun (A.det_smul_inv_mulVec_eq_cramer b hd) j
  rw [hx', cramer_apply] at h
  change A.det * x j = (A.updateCol j b).det at h
  exact (eq_div_iff hd.ne_zero).mpr (by simpa only [mul_comm] using h)

section Schur

variable {K : Type*} [Field K] {i j k : Type*}
  [Fintype i] [Fintype j] [Fintype k] [DecidableEq i] [DecidableEq j] [DecidableEq k]

/-- **Equation (96)** of [benIsrael2003generalized], Chapter 0. The Schur
complement of the leading block in a partitioned matrix. -/
noncomputable def schurComplement (A : Matrix i i K) (B : Matrix i k K)
    (C : Matrix j i K) (D : Matrix j k K) : Matrix j k K :=
  D - C * A⁻¹ * B

/-- **Equation (97)** of [benIsrael2003generalized], Chapter 0. The determinant
of a block matrix factors through the Schur complement. -/
theorem det_fromBlocks_eq_det_mul_schurComplement (A : Matrix i i K) (B : Matrix i j K)
    (C : Matrix j i K) (D : Matrix j j K) (hA : IsUnit A) :
    (fromBlocks A B C D).det = A.det * (schurComplement A B C D).det := by
  let := hA.invertible
  simpa [schurComplement, invOf_eq_nonsing_inv] using det_fromBlocks₁₁ A B C D

/-- **Equation (100)** of [benIsrael2003generalized], Chapter 0. The inverse
of a block matrix with two invertible diagonal blocks is expressed using the
two Schur complements. -/
theorem inv_fromBlocks_eq_schurComplements (A : Matrix i i K) (B : Matrix i j K)
    (C : Matrix j i K) (D : Matrix j j K)
    (hA : IsUnit A) (hD : IsUnit D) (hM : IsUnit (fromBlocks A B C D)) :
    (fromBlocks A B C D)⁻¹ = fromBlocks
      (schurComplement D C B A)⁻¹
      (-(A⁻¹ * B * (schurComplement A B C D)⁻¹))
      (-(D⁻¹ * C * (schurComplement D C B A)⁻¹))
      (schurComplement A B C D)⁻¹ := by
  let := hA.invertible
  let := hD.invertible
  let := hM.invertible
  let := invertibleOfFromBlocks₁₁Invertible A B C D
  let := invertibleOfFromBlocks₂₂Invertible A B C D
  have hLeft := invOf_fromBlocks₁₁_eq A B C D
  have hRight := invOf_fromBlocks₂₂_eq A B C D
  simp only [invOf_eq_nonsing_inv] at hLeft hRight
  have hb := fromBlocks_inj.mp (hLeft.symm.trans hRight)
  rw [schurComplement, schurComplement, hLeft, hb.1, hb.2.2.1]

omit [Fintype k] [DecidableEq k] in
/-- **Equation (99)** of [benIsrael2003generalized], Chapter 0. Eliminating
the first two blocks at once gives the same Schur complement as eliminating
them in succession. -/
theorem schurComplement_quotient
    (E : Matrix i i K) (F : Matrix i j K) (G : Matrix j i K) (H : Matrix j j K)
    (P : Matrix i k K) (Q : Matrix j k K) (R : Matrix k i K) (S : Matrix k j K)
    (T : Matrix k k K) (hE : IsUnit E) (hM : IsUnit (fromBlocks E F G H)) :
    let D := schurComplement E (fromCols F P) (fromRows G R) (fromBlocks H Q S T)
    schurComplement (fromBlocks E F G H) (fromRows P Q) (fromCols R S) T =
      schurComplement D.toBlocks₁₁ D.toBlocks₁₂ D.toBlocks₂₁ D.toBlocks₂₂ := by
  intro D
  let H' := schurComplement E F G H
  let Q' := schurComplement E P G Q
  let S' := schurComplement E F R S
  let T' := schurComplement E P R T
  have hD : D = fromBlocks H' Q' S' T' := by
    dsimp only [D, H', Q', S', T', schurComplement]
    rw [fromRows_mul, fromRows_mul_fromCols]
    ext (a | a) (b | b) <;> rfl
  have hdE := (isUnit_iff_isUnit_det E).mp hE
  have hdM := (isUnit_iff_isUnit_det _).mp hM
  have hH : IsUnit H'.det := by
    rw [det_fromBlocks_eq_det_mul_schurComplement E F G H hE] at hdM
    exact isUnit_of_mul_isUnit_right hdM
  let Y := H'⁻¹ * Q'
  let X := E⁻¹ * (P - F * Y)
  have hY : H' * Y = Q' := mul_nonsing_inv_cancel_left _ _ hH
  have hSol : fromBlocks E F G H * fromRows X Y = fromRows P Q := by
    rw [fromBlocks_mul_fromRows]
    congr 1
    · dsimp only [X]
      rw [mul_nonsing_inv_cancel_left _ _ hdE, sub_add_cancel]
    · calc
        G * X + H * Y = G * E⁻¹ * P + H' * Y := by
          simp only [X, H', schurComplement, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
          abel
        _ = Q := by
          rw [hY]
          dsimp only [Q', schurComplement]
          abel
  have hInv : (fromBlocks E F G H)⁻¹ * fromRows P Q = fromRows X Y := by
    rw [← hSol, nonsing_inv_mul_cancel_left _ _ hdM]
  rw [hD, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, schurComplement, Matrix.mul_assoc, hInv, fromCols_mul_fromRows]
  simp only [X, Y, T', S', schurComplement, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

end Schur

private noncomputable def orderSelectionPermEquiv (p q : ℕ) :
    (IndexSequence p q × Equiv.Perm (Fin p)) ≃ {f : Fin p → Fin q // Function.Injective f} :=
  Equiv.ofBijective
    (fun rs => ⟨rs.1 ∘ rs.2, rs.1.injective.comp rs.2.injective⟩) (by
      constructor
      · rintro ⟨r, σ⟩ ⟨s, τ⟩ h
        let R := Finset.univ.image r
        have hCard : R.card = p := by
          change (Finset.univ.image r).card = p
          rw [Finset.card_image_of_injective _ r.injective, Finset.card_univ, Fintype.card_fin]
        have hv (j : Fin p) : r (σ j) = s (τ j) :=
          congrArg (fun f : {f : Fin p → Fin q // Function.Injective f} => f.1 j) h
        have hr (i : Fin p) : r i ∈ R := Finset.mem_image_of_mem r (Finset.mem_univ i)
        have hs (i : Fin p) : s i ∈ R := by
          obtain ⟨j, rfl⟩ := τ.surjective i
          exact hv j ▸ hr (σ j)
        have hrs : r = s := (Finset.orderEmbOfFin_unique' hCard hr).trans
          (Finset.orderEmbOfFin_unique' hCard hs).symm
        subst s
        exact Prod.ext rfl (Equiv.ext fun i => r.injective (hv i))
      · intro f
        let R := Finset.univ.image f.1
        have hCard : R.card = p := by
          change (Finset.univ.image f.1).card = p
          rw [Finset.card_image_of_injective _ f.2, Finset.card_univ, Fintype.card_fin]
        let e := R.orderIsoOfFin hCard
        let g : Fin p ≃ R := Equiv.ofBijective
          (fun j => ⟨f.1 j, Finset.mem_image_of_mem f.1 (Finset.mem_univ j)⟩) (by
            constructor
            · intro i j he
              exact f.2 (congrArg Subtype.val he)
            · intro i
              obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.2
              exact ⟨j, Subtype.ext hj⟩)
        refine ⟨(R.orderEmbOfFin hCard, g.trans e.toEquiv.symm), Subtype.ext ?_⟩
        funext i
        change (e (e.symm (g i)) : Fin q) = f.1 i
        rw [e.apply_symm_apply]
        rfl)

/-- **Equation (87)** of [benIsrael2003generalized], Chapter 0. The determinant
of a rectangular product is the sum of products of the corresponding maximal
minors, with each selected set counted in increasing order. -/
theorem det_mul_eq_sum_minors {K : Type*} [Field K] [CharZero K] {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) K) (B : Matrix (Fin q) (Fin p) K) :
    (A * B).det = ∑ r : IndexSequence p q,
      (A.submatrix id r).det * (B.submatrix r id).det := by
  classical
  let term (r : Fin p → Fin q) := (A.submatrix id r).det * (B.submatrix r id).det
  have hZero (r : Fin p → Fin q) (hr : ¬Function.Injective r) : term r = 0 := by
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hr
    have h := det_zero_of_column_eq (M := A.submatrix id r) hne
      (fun l => congrArg (A l) hij)
    exact (congrArg (· * (B.submatrix r id).det) h).trans (zero_mul _)
  have hPerm (r : IndexSequence p q) (σ : Equiv.Perm (Fin p)) : term (r ∘ σ) = term r := by
    change (((A.submatrix id r).submatrix id σ).det) *
      (((B.submatrix r id).submatrix σ id).det) = term r
    rw [det_permute', det_permute]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [term, h]
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p))
  calc
    (p.factorial : K) * (A * B).det = ∑ r : Fin p → Fin q, term r := by
      simpa only [Fintype.card_fin] using Matrix.factorial_mul_det_mul A B
    _ = ∑ r : {r : Fin p → Fin q // Function.Injective r}, term r.1 := by
      have hBad : (∑ r : {r : Fin p → Fin q // ¬Function.Injective r}, term r.1) = 0 :=
        Finset.sum_eq_zero fun r _ => hZero r.1 r.2
      rw [← Fintype.sum_subtype_add_sum_subtype (fun r => Function.Injective r) term,
        hBad, add_zero]
    _ = ∑ rs : IndexSequence p q × Equiv.Perm (Fin p), term (rs.1 ∘ rs.2) :=
      (Equiv.sum_comp (orderSelectionPermEquiv p q) (fun r => term r.1)).symm
    _ = (p.factorial : K) * ∑ r : IndexSequence p q, term r := by
      rw [Fintype.sum_prod_type]
      simp_rw [hPerm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum]

/-- **Equation (88)** of [benIsrael2003generalized], Chapter 0. The Gram matrix
uses the source convention that the inner product is linear in its first slot. -/
noncomputable def gramMatrix {ι d : Type*} [Fintype d] (x : ι → EuclideanSpace ℂ d) :
    Matrix ι ι ℂ :=
  fun i j => inner ℂ (x j) (x i)

/-- The Gramian of a finite family is the determinant of its Gram matrix. -/
noncomputable def gramian {ι d : Type*} [Fintype d] [Fintype ι] [DecidableEq ι]
    (x : ι → EuclideanSpace ℂ d) : ℂ :=
  (gramMatrix x).det

private theorem gramian_eq_det_gram {ι d : Type*} [Fintype d] [Fintype ι] [DecidableEq ι]
    (x : ι → EuclideanSpace ℂ d) : gramian x = (Matrix.gram ℂ x).det :=
  det_transpose (Matrix.gram ℂ x)

/-- **Exercise 62** of [benIsrael2003generalized], Chapter 0. A finite family
is linearly independent precisely when its Gram matrix is nonsingular. -/
theorem isUnit_gramMatrix_iff {ι d : Type*} [Fintype d] [Fintype ι] [DecidableEq ι]
    (x : ι → EuclideanSpace ℂ d) : IsUnit (gramMatrix x) ↔ LinearIndependent ℂ x := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  change gramian x ≠ 0 ↔ LinearIndependent ℂ x
  rw [gramian_eq_det_gram, det_gram_ne_zero_iff_linearIndependent]

/-- **Exercise 63** of [benIsrael2003generalized], Chapter 0. Permuting the
vectors leaves the Gramian unchanged. -/
theorem gramian_perm {ι d : Type*} [Fintype d] [Fintype ι] [DecidableEq ι]
    (x : ι → EuclideanSpace ℂ d) (p : Equiv.Perm ι) : gramian (x ∘ p) = gramian x :=
  det_submatrix_equiv_self p (gramMatrix x)

open scoped ComplexOrder in
/-- **Exercise 63** of [benIsrael2003generalized], Chapter 0. A Gramian is
real and nonnegative, and vanishes precisely for linearly dependent families. -/
theorem gramian_nonneg_eq_zero_iff {ι d : Type*} [Fintype d] [Fintype ι] [DecidableEq ι]
    (x : ι → EuclideanSpace ℂ d) :
    0 ≤ gramian x ∧ (gramian x = 0 ↔ ¬LinearIndependent ℂ x) := by
  rw [gramian_eq_det_gram]
  refine ⟨(posSemidef_gram ℂ x).det_nonneg, ?_⟩
  rw [← det_gram_ne_zero_iff_linearIndependent, not_ne_iff]

/-- The Gramian of the columns of $X$ is the determinant of $X^HX$ and equals
the sum of squared moduli of the maximal minors of $X$. -/
theorem gramian_eq_sum_sq_minors {p q : ℕ} (X : Matrix (Fin q) (Fin p) ℂ) :
    let x : Fin p → EuclideanSpace ℂ (Fin q) := fun i => WithLp.toLp 2 (X.col i)
    gramian x = (Xᴴ * X).det ∧
      gramian x = ∑ r : IndexSequence p q, ((‖(X.submatrix r id).det‖ ^ 2 : ℝ) : ℂ) := by
  intro x
  have he : gramMatrix x = (Xᴴ * X)ᵀ := by
    ext i j
    simp [gramMatrix, x, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Matrix.mul_apply, Matrix.col, Matrix.conjTranspose_apply, mul_comm]
  have hd : gramian x = (Xᴴ * X).det := by
    rw [gramian, he, det_transpose]
  refine ⟨hd, ?_⟩
  rw [hd, det_mul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro r _
  rw [← conjTranspose_submatrix, det_conjTranspose, ← starRingEnd_apply,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- A minor submatrix of a factored matrix is the product of the selected
rows of the first factor and the selected columns of the second factor. -/
theorem submatrix_mul_submatrix_eq {K : Type*} [Field K] {m d k : ℕ}
    {A : Matrix (Fin m) (Fin d) K} {F : Matrix (Fin m) (Fin k) K}
    {G : Matrix (Fin k) (Fin d) K} (h : A = F * G) {a b : Type*}
    (r : a → Fin m) (c : b → Fin d) :
    A.submatrix r c = F.submatrix r id * G.submatrix id c :=
  (congrArg (fun M => M.submatrix r c) h).trans
    (submatrix_mul F G r id c Function.bijective_id)

section MinorIndices

variable {K : Type*} [Field K] {m d : ℕ}

/-- **Section 0.5.3** of [benIsrael2003generalized]. The index set $I(A)$ selects
the maximal submatrices having full row rank. -/
def fullRankRowIndices (A : Matrix (Fin m) (Fin d) K) : Set (IndexSequence A.rank m) :=
  {r | (A.submatrix r id).rank = A.rank}

/-- **Section 0.5.3** of [benIsrael2003generalized]. The index set $J(A)$ selects
the maximal submatrices having full column rank. -/
def fullRankColumnIndices (A : Matrix (Fin m) (Fin d) K) : Set (IndexSequence A.rank d) :=
  {c | (A.submatrix id c).rank = A.rank}

/-- **Section 0.5.3** of [benIsrael2003generalized]. The set $N(A)$ consists of
the row and column selections that give invertible maximal minors. -/
def nonsingularMinorIndices (A : Matrix (Fin m) (Fin d) K) :
    Set (IndexSequence A.rank m × IndexSequence A.rank d) :=
  {s | IsUnit (A.submatrix s.1 s.2)}

/-- **Exercise 64** of [benIsrael2003generalized], Chapter 0. The indexing set
of invertible maximal minors is the product of the two full-rank selection sets. -/
theorem nonsingularMinorIndices_eq (A : Matrix (Fin m) (Fin d) K) :
    nonsingularMinorIndices A = fullRankRowIndices A ×ˢ fullRankColumnIndices A := by
  ext ⟨r, c⟩
  change IsUnit (A.submatrix r c) ↔
    (A.submatrix r id).rank = A.rank ∧ (A.submatrix id c).rank = A.rank
  constructor
  · intro h
    have hr := rank_of_isUnit _ h
    rw [Fintype.card_fin] at hr
    have hr₁ := rank_submatrix_le (A.submatrix r id) (id : Fin A.rank → Fin A.rank) c
    have hr₂ := rank_submatrix_le (A.submatrix id c) r (id : Fin A.rank → Fin A.rank)
    change (A.submatrix r c).rank ≤ (A.submatrix r id).rank at hr₁
    change (A.submatrix r c).rank ≤ (A.submatrix id c).rank at hr₂
    exact ⟨le_antisymm (rank_submatrix_le A r id) (hr.ge.trans hr₁),
      le_antisymm (rank_submatrix_le A id c) (hr.ge.trans hr₂)⟩
  · rintro ⟨hr, hc⟩
    obtain ⟨F, G, hf⟩ := lemma_1 A
    have hRow := submatrix_mul_submatrix_eq hf.eq_mul r (id : Fin d → Fin d)
    have hCol := submatrix_mul_submatrix_eq hf.eq_mul (id : Fin m → Fin m) c
    have hr' : (F.submatrix r id).rank = Fintype.card (Fin A.rank) := by
      refine le_antisymm (rank_le_card_width _) ?_
      calc
        Fintype.card (Fin A.rank) = (A.submatrix r id).rank := by rw [hr, Fintype.card_fin]
        _ ≤ (F.submatrix r id).rank := hRow ▸ rank_mul_le_left _ _
    have hc' : (G.submatrix id c).rank = Fintype.card (Fin A.rank) := by
      refine le_antisymm (rank_le_card_height _) ?_
      calc
        Fintype.card (Fin A.rank) = (A.submatrix id c).rank := by rw [hc, Fintype.card_fin]
        _ ≤ (G.submatrix id c).rank := hCol ▸ rank_mul_le_right _ _
    rw [submatrix_mul_submatrix_eq hf.eq_mul]
    exact (mulVec_surjective_iff_isUnit.mp (mulVec_surjective_iff_rank_eq_card.mpr hr')).mul
      (mulVec_surjective_iff_isUnit.mp (mulVec_surjective_iff_rank_eq_card.mpr hc'))

private theorem rank_mul_eq_left_of_fullRowRank {a b c : Type*}
    [Fintype b] [Fintype c] (F : Matrix a b K) (G : Matrix b c K)
    (hG : G.rank = Fintype.card b) : (F * G).rank = F.rank := by
  have hs : Function.Surjective G.mulVecLin := mulVec_surjective_iff_rank_eq_card.mpr hG
  rw [Matrix.rank, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr hs)]
  rfl

/-- **Exercise 64(a)–(b)** of [benIsrael2003generalized]. A rank
factorization preserves full-rank row selections in its first factor
and full-rank column selections in its second factor. -/
theorem rankFactorization_fullRankIndices {r : ℕ}
    {A : Matrix (Fin m) (Fin d) K} {F : Matrix (Fin m) (Fin r) K}
    {G : Matrix (Fin r) (Fin d) K} (h : IsRankFactorization A F G) :
    (∀ I : IndexSequence A.rank m, I ∈ fullRankRowIndices A ↔
      (F.submatrix I id).rank = r) ∧
      (∀ J : IndexSequence A.rank d, J ∈ fullRankColumnIndices A ↔
        (G.submatrix id J).rank = r) := by
  have hr : A.rank = r := h.rank_eq.trans (Fintype.card_fin r)
  constructor
  · intro I
    change (A.submatrix I id).rank = A.rank ↔ _
    rw [submatrix_mul_submatrix_eq h.eq_mul, submatrix_id_id,
      rank_mul_eq_left_of_fullRowRank _ _ h.rank_right]
    exact ⟨fun he => he.trans hr, fun he => he.trans hr.symm⟩
  · intro J
    change (A.submatrix id J).rank = A.rank ↔ _
    have hF : Fᵀ.rank = Fintype.card (Fin r) := F.rank_transpose.trans h.rank_left
    have he := rank_mul_eq_left_of_fullRowRank (G.submatrix id J)ᵀ Fᵀ hF
    rw [← transpose_mul, rank_transpose, rank_transpose] at he
    rw [submatrix_mul_submatrix_eq h.eq_mul, submatrix_id_id, he]
    exact ⟨fun he => he.trans hr, fun he => he.trans hr.symm⟩

end MinorIndices

/-- **Equation (89)** of [benIsrael2003generalized], Chapter 0. The volume of a
positive-rank real matrix is the square root of the sum of squared maximal
nonsingular minors. Its value at rank zero is zero. -/
noncomputable def matrixVolume {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) : ℝ := by
  classical
  exact if A.rank = 0 then 0 else
    Real.sqrt (∑ s : nonsingularMinorIndices A, (A.submatrix s.1.1 s.1.2).det ^ 2)

/-- The volume may be computed over all choices of maximal minors, since
singular minors contribute zero. -/
theorem matrixVolume_eq_sqrt_sum_minors {m d r : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (hr : A.rank = r) (h0 : r ≠ 0) :
    matrixVolume A = Real.sqrt (∑ i : IndexSequence r m, ∑ j : IndexSequence r d,
      (A.submatrix i j).det ^ 2) := by
  subst r
  classical
  let term (s : IndexSequence A.rank m × IndexSequence A.rank d) :=
    (A.submatrix s.1 s.2).det ^ 2
  have hzero (s : {s // s ∉ nonsingularMinorIndices A}) : term s.1 = 0 := by
    have hu : ¬IsUnit (A.submatrix s.1.1 s.1.2) := s.2
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hu
    simp [term, hu]
  have hbad : (∑ s : {s // s ∉ nonsingularMinorIndices A}, term s.1) = 0 :=
    Finset.sum_eq_zero fun s _ => hzero s
  simp only [matrixVolume, ite_eq_right h0]
  apply congrArg Real.sqrt
  change (∑ s : nonsingularMinorIndices A, term s.1) =
    ∑ i : IndexSequence A.rank m, ∑ j : IndexSequence A.rank d, term (i, j)
  rw [← Fintype.sum_prod_type term, ← Fintype.sum_subtype_add_sum_subtype
    (fun s => s ∈ nonsingularMinorIndices A) term, hbad, add_zero]

/-- The only increasing selection of every index is the identity. -/
theorem indexSequence_self_unique {r : ℕ} (s : IndexSequence r r) :
    s = (OrderIso.refl (Fin r)).toOrderEmbedding := by
  let h : (Finset.univ : Finset (Fin r)).card = r := by simp
  exact (Finset.orderEmbOfFin_unique' h (fun i => Finset.mem_univ (s i))).trans
    (Finset.orderEmbOfFin_unique' h (fun i => Finset.mem_univ i)).symm

/-- **Equation (104)** of [benIsrael2003generalized], Chapter 0. The square
of the volume of a positive full-column-rank matrix is its column Gramian. -/
theorem matrixVolume_sq_eq_det_transpose_mul {m r : ℕ} (F : Matrix (Fin m) (Fin r) ℝ)
    (hr : F.rank = r) (h0 : r ≠ 0) : matrixVolume F ^ 2 = (Fᵀ * F).det := by
  classical
  let : Unique (IndexSequence r r) :=
    ⟨⟨(OrderIso.refl (Fin r)).toOrderEmbedding⟩, indexSequence_self_unique⟩
  rw [matrixVolume_eq_sqrt_sum_minors F hr h0]
  simp only [Fintype.sum_unique]
  change √(∑ i : IndexSequence r m, (F.submatrix i id).det ^ 2) ^ 2 = (Fᵀ * F).det
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), det_mul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro i _
  rw [← transpose_submatrix, det_transpose, pow_two]

/-- **Equation (105)** of [benIsrael2003generalized], Chapter 0. The square
of the volume of a positive full-row-rank matrix is its row Gramian. -/
theorem matrixVolume_sq_eq_det_mul_transpose {r d : ℕ} (G : Matrix (Fin r) (Fin d) ℝ)
    (hr : G.rank = r) (h0 : r ≠ 0) : matrixVolume G ^ 2 = (G * Gᵀ).det := by
  classical
  let : Unique (IndexSequence r r) :=
    ⟨⟨(OrderIso.refl (Fin r)).toOrderEmbedding⟩, indexSequence_self_unique⟩
  rw [matrixVolume_eq_sqrt_sum_minors G hr h0]
  simp only [Fintype.sum_unique]
  change √(∑ j : IndexSequence r d, (G.submatrix id j).det ^ 2) ^ 2 = (G * Gᵀ).det
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), det_mul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro j _
  rw [← transpose_submatrix, det_transpose, pow_two]

/-- **Exercise 66(c)** of [benIsrael2003generalized], Chapter 0. The volume of
a real matrix is the product of the volumes of its full-rank factors. -/
theorem matrixVolume_mul_of_rankFactorization {m d r : ℕ}
    {A : Matrix (Fin m) (Fin d) ℝ} {F : Matrix (Fin m) (Fin r) ℝ}
    {G : Matrix (Fin r) (Fin d) ℝ} (h : IsRankFactorization A F G) :
    matrixVolume A = matrixVolume F * matrixVolume G := by
  classical
  have hA : A.rank = r := h.rank_eq.trans (Fintype.card_fin r)
  have hF : F.rank = r := h.rank_left.trans (Fintype.card_fin r)
  have hG : G.rank = r := h.rank_right.trans (Fintype.card_fin r)
  by_cases h0 : r = 0
  · simp [matrixVolume, hA, hF, hG, h0]
  let : Unique (IndexSequence r r) :=
    ⟨⟨(OrderIso.refl (Fin r)).toOrderEmbedding⟩, indexSequence_self_unique⟩
  rw [matrixVolume_eq_sqrt_sum_minors A hA h0, matrixVolume_eq_sqrt_sum_minors F hF h0,
    matrixVolume_eq_sqrt_sum_minors G hG h0]
  simp only [Fintype.sum_unique]
  change Real.sqrt (∑ i : IndexSequence r m, ∑ j : IndexSequence r d,
    (A.submatrix i j).det ^ 2) = Real.sqrt (∑ i : IndexSequence r m,
    (F.submatrix i id).det ^ 2) * Real.sqrt (∑ j : IndexSequence r d,
    (G.submatrix id j).det ^ 2)
  simp_rw [submatrix_mul_submatrix_eq h.eq_mul, det_mul, mul_pow, ← Finset.mul_sum]
  rw [← Finset.sum_mul, Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

open scoped Classical in
/-- **Equations (106a)–(106b)** of [benIsrael2003generalized]. The
square of the volume is the sum of the squared volumes of the
full-rank row selections, and also of the full-rank column selections. -/
theorem matrixVolume_sq_eq_sum_row_column_volumes {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (h0 : A.rank ≠ 0) :
    matrixVolume A ^ 2 =
      (∑ I : IndexSequence A.rank m, if I ∈ fullRankRowIndices A then
        matrixVolume (A.submatrix I id) ^ 2 else 0) ∧
    matrixVolume A ^ 2 =
      (∑ J : IndexSequence A.rank d, if J ∈ fullRankColumnIndices A then
        matrixVolume (A.submatrix id J) ^ 2 else 0) := by
  classical
  let r := A.rank
  let : Unique (IndexSequence r r) :=
    ⟨⟨(OrderIso.refl (Fin r)).toOrderEmbedding⟩, indexSequence_self_unique⟩
  have hvol := matrixVolume_eq_sqrt_sum_minors A (r := r) rfl h0
  rw [hvol, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  constructor
  · apply Finset.sum_congr rfl
    intro I _
    by_cases hI : I ∈ fullRankRowIndices A
    · have hr : (A.submatrix I id).rank = r := hI
      rw [ite_eq_left hI, matrixVolume_eq_sqrt_sum_minors _ hr h0]
      simp only [Fintype.sum_unique]
      change _ = (Real.sqrt (∑ J : IndexSequence r d,
        (((A.submatrix I id).submatrix id J).det) ^ 2)) ^ 2
      simp only [submatrix_submatrix, Function.comp_id, Function.id_comp]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    · rw [ite_eq_right hI]
      apply Finset.sum_eq_zero
      intro J _
      have hminor : (A.submatrix I J).rank < r := by
        have hle := rank_submatrix_le (A.submatrix I id) (id : Fin r → Fin r) J
        change (A.submatrix I J).rank ≤ (A.submatrix I id).rank at hle
        exact hle.trans_lt (lt_of_le_of_ne (rank_submatrix_le A I id) hI)
      have hz : (A.submatrix I J).det = 0 := by
        by_contra hne
        have he := rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
        rw [Fintype.card_fin] at he
        exact hminor.ne he
      simp [hz]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J _
    by_cases hJ : J ∈ fullRankColumnIndices A
    · have hr : (A.submatrix id J).rank = r := hJ
      rw [ite_eq_left hJ, matrixVolume_eq_sqrt_sum_minors _ hr h0]
      simp only [Fintype.sum_unique]
      change _ = (Real.sqrt (∑ I : IndexSequence r m,
        (((A.submatrix id J).submatrix I id).det) ^ 2)) ^ 2
      simp only [submatrix_submatrix, Function.comp_id, Function.id_comp]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    · rw [ite_eq_right hJ]
      apply Finset.sum_eq_zero
      intro I _
      have hminor : (A.submatrix I J).rank < r := by
        have hle := rank_submatrix_le (A.submatrix id J) I (id : Fin r → Fin r)
        change (A.submatrix I J).rank ≤ (A.submatrix id J).rank at hle
        exact hle.trans_lt (lt_of_le_of_ne (rank_submatrix_le A id J) hJ)
      have hz : (A.submatrix I J).det = 0 := by
        by_contra hne
        have he := rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
        rw [Fintype.card_fin] at he
        exact hminor.ne he
      simp [hz]

/-- **Exercise 60**, Equation (94) of [benIsrael2003generalized].
Hadamard's determinant inequality is an equality exactly when some
column is zero or the columns are pairwise orthogonal. -/
theorem det_norm_le_prod_col_norm [LinearOrder n] (A : Matrix n n ℂ) :
    let c : n → ℝ := fun j => Real.sqrt (∑ i, ‖A i j‖ ^ 2)
    ‖A.det‖ ≤ ∏ j, c j ∧
      (‖A.det‖ = ∏ j, c j ↔ (∃ j, ∀ i, A i j = 0) ∨
        ∀ i j, i ≠ j → (Aᴴ * A) i j = 0) := by
  intro c
  refine ⟨norm_det_le_prod_sqrt_sum_norm_sq A, ?_⟩
  constructor
  · intro h
    by_cases hzero : ∃ j, ∀ i, A i j = 0
    · exact Or.inl hzero
    right
    have hc (j : n) : 0 < c j := by
      obtain ⟨i, hi⟩ : ∃ i, A i j ≠ 0 := by
        by_contra! hn
        exact hzero ⟨j, hn⟩
      apply Real.sqrt_pos.mpr
      exact (sq_pos_of_pos (norm_pos_iff.mpr hi)).trans_le
        (Finset.single_le_sum (fun i _ => sq_nonneg ‖A i j‖) (Finset.mem_univ i))
    obtain ⟨U, hU, hT⟩ := exists_unitary_mul_isUpperTriangular A
    let T := U * A
    have hcol (j : n) : ∑ i, ‖T i j‖ ^ 2 = ∑ i, ‖A i j‖ ^ 2 :=
      sum_norm_sq_mulVec_of_mem_unitaryGroup hU (A.col j)
    have hdet : ‖A.det‖ = ∏ j, ‖T j j‖ := by
      calc
        _ = ‖T.det‖ := by
          dsimp only [T]
          rw [det_mul, norm_mul, norm_det_of_mem_unitaryGroup hU, one_mul]
        _ = _ := by rw [det_of_isUpperTriangular hT, norm_prod]
    have hprod : (∏ j, ‖T j j‖) = ∏ j, c j := hdet.symm.trans h
    have hdiag (j : n) : 0 < ‖T j j‖ := by
      by_contra! hn
      have hz := Finset.prod_eq_zero (f := fun i : n => ‖T i i‖) (Finset.mem_univ j)
        (le_antisymm hn (norm_nonneg _))
      rw [hprod] at hz
      exact (Finset.prod_pos (fun i _ => hc i)).ne' hz
    have hle (j : n) : ‖T j j‖ ≤ c j := by
      change ‖T j j‖ ≤ Real.sqrt _
      rw [← hcol j, ← Real.sqrt_sq (norm_nonneg (T j j))]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun i _ => sq_nonneg ‖T i j‖)
        (Finset.mem_univ j))
    have hd (j : n) : ‖T j j‖ = c j := by
      refine le_antisymm (hle j) ?_
      by_contra! hj
      have hstrict := Finset.prod_lt_prod₀ (fun i _ => hdiag i) (fun i _ => hle i)
        ⟨j, Finset.mem_univ j, hj⟩
      rw [hprod] at hstrict
      exact (lt_irrefl _ hstrict)
    have hTzero (i j : n) (hij : i ≠ j) : T i j = 0 := by
      have he : ∑ a, ‖T a j‖ ^ 2 = ‖T j j‖ ^ 2 := by
        rw [hd j, hcol j]
        exact (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
      have hrest : ∑ a ∈ Finset.univ.erase j, ‖T a j‖ ^ 2 = 0 := by
        have hh := Finset.sum_erase_add (s := Finset.univ) (fun a => ‖T a j‖ ^ 2)
          (Finset.mem_univ j)
        rw [he] at hh
        linarith
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖T a j‖)).mp hrest i
        (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
      exact norm_eq_zero.mp (mul_self_eq_zero.mp (by simpa only [pow_two] using hz))
    have hTdiag : T = diagonal fun j => T j j := by
      ext i j
      by_cases hij : i = j
      · subst j
        rw [diagonal_apply_eq]
      · rw [diagonal_apply_ne _ hij, hTzero i j hij]
    have hGram : Tᴴ * T = Aᴴ * A := by
      dsimp only [T]
      rw [conjTranspose_mul, Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc Uᴴ,
        show Uᴴ * U = 1 from Unitary.star_mul_self_of_mem hU, Matrix.one_mul]
    intro i j hij
    rw [← hGram, hTdiag, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_apply_ne _ hij]
  · rintro (⟨j, hj⟩ | hOrth)
    · have hdet := det_eq_zero_of_column_eq_zero j hj
      have hzero : c j = 0 := by simp [c, hj]
      rw [hdet, norm_zero, Finset.prod_eq_zero (Finset.mem_univ j) hzero]
    · have hGram : Aᴴ * A = diagonal fun j => (Aᴴ * A) j j := by
        ext i j
        by_cases hij : i = j
        · subst j
          rw [diagonal_apply_eq]
        · rw [diagonal_apply_ne _ hij, hOrth i j hij]
      have hentry (j : n) : (Aᴴ * A) j j = ((∑ i, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
        simp only [Matrix.mul_apply, conjTranspose_apply, Complex.ofReal_sum,
          RCLike.star_def, RCLike.conj_mul, Complex.ofReal_pow]
        rfl
      have hdet : ‖(Aᴴ * A).det‖ = ‖A.det‖ ^ 2 := by
        rw [det_mul, det_conjTranspose, norm_mul, norm_star, pow_two]
      have ht : 0 ≤ ∏ j, c j := Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
      apply (sq_eq_sq₀ (norm_nonneg _) ht).mp
      rw [← hdet, hGram, det_diagonal, norm_prod, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro j _
      rw [hentry, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm

end BenIsraelGreville.Chapter00
