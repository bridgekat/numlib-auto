import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Matrix.SaddlePoint.Spectrum
import Numlib.LinearAlgebra.Matrix.LU

/-!
# Direct factorizations of symmetric saddle-point matrices

For $\mathcal A=\begin{bmatrix} A&B^T\\B&-C \end{bmatrix}$, an $LDL^T$ factorization of
$A$ and one of the negative Schur complement can be assembled into a factorization of
$\mathcal A$. When $A$ and $C$ are both positive definite, every principal submatrix
of $\mathcal A$ is nonsingular, allowing diagonal pivots in any coordinate order.

## Main results

* `Matrix.fromBlocks_transpose_neg_eq_block_ldl`: the assembled block $LDL^T$ identity.
* `Matrix.posDef_add_mul_inv_mul_transpose`: the negative Schur complement is positive definite
  when $A$ is positive definite, $C$ is positive semidefinite, and $B$ has full row rank.
* `Matrix.isUnit_submatrix_fromBlocks_transpose_neg_of_posDef`: every principal submatrix
  of a symmetric quasidefinite matrix is nonsingular.
* `Matrix.exists_isLDM_submatrix_fromBlocks_transpose_neg_of_posDef`: such submatrices have
  an $LDL^T$ factorization using a diagonal $D$ in every ordering.

## Proof outline

Negating the constraint rows changes the symmetric part to $\operatorname{diag}(A,C)$.
The same sign change on any principal submatrix still gives a positive definite symmetric part.
Thus all the strict leading principal submatrices in a chosen ordering are invertible, which
is sufficient for the unpivoted factorization.
-/

open scoped Matrix

namespace Matrix

variable {K n m p : Type*} [Fintype n] [Fintype m]

/-- Over a commutative ring, let $A=L_A D_A L_A^T$ with $L_A,D_A$ invertible and $D_A$
symmetric, and let $C+BA^{-1}B^T=L_S D_S L_S^T$. Define
$L_B=B(L_A^T)^{-1}D_A^{-1}$. Then $BA^{-1}B^T=L_BD_A L_B^T$ and
$$\begin{bmatrix}A&B^T\\B&-C\end{bmatrix}
= \begin{bmatrix}L_A&0\\L_B&L_S\end{bmatrix}
  \begin{bmatrix}D_A&0\\0&-D_S\end{bmatrix}
  \begin{bmatrix}L_A^T&L_B^T\\0&L_S^T\end{bmatrix}.$$
All index types are finite. Triangularity and definiteness are not needed for the identity. -/
theorem fromBlocks_transpose_neg_eq_block_ldl [CommRing K] [DecidableEq n]
    {A LA DA : Matrix n n K} {C LS DS : Matrix m m K} (B : Matrix m n K)
    (hLA : IsUnit LA) (hDA : IsUnit DA) (hD : DA.IsSymm)
    (hA : A = LA * DA * LAᵀ) (hS : C + B * A⁻¹ * Bᵀ = LS * DS * LSᵀ) :
    let LB := B * LAᵀ⁻¹ * DA⁻¹
    B * A⁻¹ * Bᵀ = LB * DA * LBᵀ ∧
      fromBlocks A Bᵀ B (-C) =
        fromBlocks LA 0 LB LS * fromBlocks DA 0 0 (-DS) * fromBlocks LAᵀ LBᵀ 0 LSᵀ := by
  intro LB
  have hLA' := (isUnit_iff_isUnit_det LA).1 hLA
  have hDAT := (isUnit_iff_isUnit_det DA).1 hDA
  have hLAT := isUnit_det_transpose LA hLA'
  have hB : LB * DA * LAᵀ = B := by
    dsimp only [LB]
    rw [nonsing_inv_mul_cancel_right DA _ hDAT, nonsing_inv_mul_cancel_right LAᵀ _ hLAT]
  have hBT : LA * DA * LBᵀ = Bᵀ := by
    simpa only [transpose_mul, transpose_transpose, hD.eq, Matrix.mul_assoc] using
      congrArg transpose hB
  have hGram : B * A⁻¹ * Bᵀ = LB * DA * LBᵀ := by
    calc
      B * A⁻¹ * Bᵀ = B * LAᵀ⁻¹ * LBᵀ := by
        rw [hA, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← hBT]
        simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left LA _ hLA',
          nonsing_inv_mul_cancel_left DA _ hDAT]
      _ = LB * DA * LBᵀ := by
        dsimp only [LB]
        rw [nonsing_inv_mul_cancel_right DA _ hDAT]
  have hbottom : LB * DA * LBᵀ + LS * (-DS) * LSᵀ = -C := by
    rw [← hGram, Matrix.mul_neg, Matrix.neg_mul, ← hS]
    abel
  refine ⟨hGram, ?_⟩
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    ← hA, hBT, hB, hbottom]

/-- If $A$ is real symmetric positive definite, $C$ is real symmetric positive semidefinite,
and $B$ has full row rank, then $BA^{-1}B^T+C$ is symmetric positive definite. -/
theorem posDef_add_mul_inv_mul_transpose [DecidableEq n]
    {A : Matrix n n ℝ} {C : Matrix m m ℝ} {B : Matrix m n ℝ}
    (hA : A.PosDef) (hC : C.PosSemidef) (hB : Function.Injective Bᵀ.mulVec) :
    (B * A⁻¹ * Bᵀ + C).PosDef := by
  have h := hA.conjTranspose_mul_inv_mul (B := Bᵀ) hB
  simpa using h.add_posSemidef hC

omit [Fintype n] [Fintype m] in
private theorem posDef_fromBlocks_diagonal_real [Finite n] [Finite m]
    {A : Matrix n n ℝ} {C : Matrix m m ℝ}
    (hA : A.PosDef) (hC : C.PosDef) : (fromBlocks A 0 0 C).PosDef := by
  let := Fintype.ofFinite n
  let := Fintype.ofFinite m
  refine PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hC.1) fun x hx => ?_
  have hnonnegA : 0 ≤ (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have hnonnegC : 0 ≤ (x ∘ Sum.inr) ⬝ᵥ (C *ᵥ (x ∘ Sum.inr)) := by
    simpa using hC.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  simp only [star_trivial, fromBlocks_mulVec, dotProduct_block, Sum.elim_comp_inl,
    Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  by_cases hleft : x ∘ Sum.inl = 0
  · have hright : x ∘ Sum.inr ≠ 0 := by
      intro hright
      apply hx
      funext index
      cases index with
      | inl row => exact congrFun hleft row
      | inr row => exact congrFun hright row
    have hpos : 0 < (x ∘ Sum.inr) ⬝ᵥ (C *ᵥ (x ∘ Sum.inr)) := by
      simpa using hC.dotProduct_mulVec_pos hright
    exact add_pos_of_nonneg_of_pos hnonnegA hpos
  · have hpos : 0 < (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) := by
      simpa using hA.dotProduct_mulVec_pos hleft
    exact add_pos_of_pos_of_nonneg hpos hnonnegC

omit [Fintype n] [Fintype m] in
/-- For finite real matrices $A,B,C$ with $A$ and $C$ symmetric positive definite, every principal
submatrix of $\begin{bmatrix}A&B^T\\B&-C\end{bmatrix}$ is nonsingular. The selected
coordinates, in any order, are given by an injection $e:p\to n\sqcup m$ with finite domain. -/
theorem isUnit_submatrix_fromBlocks_transpose_neg_of_posDef [Finite n] [Finite m]
    [Fintype p] [DecidableEq p]
    {A : Matrix n n ℝ} {C : Matrix m m ℝ} (B : Matrix m n ℝ) (hA : A.PosDef) (hC : C.PosDef)
    (e : p → n ⊕ m) (he : Function.Injective e) :
    IsUnit ((fromBlocks A Bᵀ B (-C)).submatrix e e) := by
  classical
  let := Fintype.ofFinite n
  let := Fintype.ofFinite m
  let s : n ⊕ m → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hflip :
      diagonal s * fromBlocks A Bᵀ B (-C) = fromBlocks A Bᵀ (-B) C := by
    have hs : diagonal s = fromBlocks (1 : Matrix n n ℝ) 0 0 (- (1 : Matrix m m ℝ)) := by
      ext (row | row) (col | col) <;> simp [s, Matrix.one_apply, diagonal]
      split_ifs <;> norm_num
    rw [hs]
    simp [fromBlocks_multiply]
  have hsub :
      diagonal (s ∘ e) * (fromBlocks A Bᵀ B (-C)).submatrix e e =
        (fromBlocks A Bᵀ (-B) C).submatrix e e := by
    rw [← hflip]
    ext row col
    simp [diagonal_mul]
  have hpart : (hermitianPart (fromBlocks A Bᵀ (-B) C)).PosDef := by
    have h := hermitianPart_fromBlocks_neg_conjTranspose A Bᵀ hC.isHermitian
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose,
      hA.isHermitian.hermitianPart_eq] at h
    rw [h]
    exact posDef_fromBlocks_diagonal_real hA hC
  have hunit : IsUnit ((fromBlocks A Bᵀ (-B) C).submatrix e e) :=
    isUnit_of_posDef_hermitianPart (by rw [hermitianPart_submatrix]; exact hpart.submatrix he)
  exact isUnit_of_mul_isUnit_right (hsub ▸ hunit)

omit [Fintype n] [Fintype m] in
/-- Let $A$ and $C$ be finite real symmetric positive definite matrices and $B$ any real matrix of
compatible size. Every principal submatrix of the saddle-point matrix, ordered by a finite
linearly ordered index type and an injective index map $e$, has a factorization $LDL^T$,
where $L$ is unit lower triangular and $D$ is diagonal. -/
theorem exists_isLDM_submatrix_fromBlocks_transpose_neg_of_posDef [Finite n] [Finite m]
    [Fintype p] [LinearOrder p]
    {A : Matrix n n ℝ} {C : Matrix m m ℝ} (B : Matrix m n ℝ) (hA : A.PosDef) (hC : C.PosDef)
    (e : p → n ⊕ m) (he : Function.Injective e) :
    ∃ L D, IsLDM ((fromBlocks A Bᵀ B (-C)).submatrix e e) L D L := by
  let M := (fromBlocks A Bᵀ B (-C)).submatrix e e
  have hM : M.HasUnitStrictLeadingPrincipalSubmatrices := fun i =>
    isUnit_submatrix_fromBlocks_transpose_neg_of_posDef B hA hC
      (e ∘ Subtype.val) (he.comp Subtype.val_injective)
  have hMsymm : M.IsSymm := (hA.isSymm.fromBlocks rfl hC.isSymm.neg).submatrix e
  obtain ⟨⟨L, D, N⟩, h, -⟩ := existsUnique_isLDM hM
  have hNL : N = L := h.eq_of_isSymm hMsymm hM
  change IsLDM M L D N at h
  exact ⟨L, D, by simpa only [hNL] using h⟩

end Matrix
