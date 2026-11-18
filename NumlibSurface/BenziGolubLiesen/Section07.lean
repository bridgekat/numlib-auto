import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Numlib.LinearAlgebra.Matrix.SaddlePoint.DirectFactorization
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.SymmetricIndefinite
import NumlibSurface.BenziGolubLiesen.Section05

/-!
# Benzi, Golub and Liesen, Section 7: Coupled direct solvers

Section 7 of [benzi2005numerical] considers symmetric saddle-point matrices
$\mathcal A=\begin{bmatrix}A&B^T\\B&-C\end{bmatrix}$. The general $LDL^T$ factorization uses
symmetric permutations and pivot blocks of order one or two. Positive definiteness of $A$
and of the negative Schur complement gives a factorization with scalar pivots in the original
block ordering. If both $A$ and $C$ are positive definite, scalar pivots work in every ordering.
The proofs use `Numlib.LinearAlgebra.Matrix.SymmetricIndefinite` and
`Numlib.LinearAlgebra.Matrix.SaddlePoint.DirectFactorization`.

## Main definitions

* Section 7, `BenziGolubLiesen.zeroDiagonalPivotExample`: the order-three example with no
  nonzero diagonal pivot.

## Main results

* Equation (7.1), `BenziGolubLiesen.exists_pivoted_blockLDL`: a symmetric permutation makes
  a block $LDL^T$ factorization with pivot orders one and two possible.
* Section 7, `BenziGolubLiesen.zeroDiagonalPivotExample_no_scalar_ldl`: the example admits no
  factorization with a diagonal $D$, even after simultaneous row and column permutation.
* Equation (7.2), `BenziGolubLiesen.saddlePointMatrix_eq_block_ldl` and
  `BenziGolubLiesen.exists_saddlePointMatrix_block_ldl`: assemble the factorization from
  positive diagonal pivots of $A$ and of the negative Schur complement.
* Section 7, `BenziGolubLiesen.exists_quasidefinite_ldl`: in the quasidefinite case, scalar
  diagonal pivots are sufficient in every ordering.

## Deviations from the source

* **Equation (7.2), existence** (reading). The discussion of the negative Schur block uses
  the positive semidefiniteness of $C$ (condition C4 of Section 1.1), not just its symmetry.

## Not formalized

* Tůma's elimination-tree conditions for static fill-reducing orderings require a graph model
  of symbolic elimination.
* Pivot-selection costs, backward errors, and software performance require arithmetic or
  implementation models in addition to the exact factorization.
-/

noncomputable section

open Matrix

namespace BenziGolubLiesen

variable {n m : Type*} [Fintype n] [Fintype m]
variable {A : Matrix n n ℝ} {B : Matrix m n ℝ} {C : Matrix m m ℝ}

omit [Fintype n] [Fintype m] in
/-- **Equation (7.1)** of [benzi2005numerical]. Let $A,C$ be real symmetric matrices and $B$
any compatible real matrix. In any initial numbering of the combined coordinates by
$\{0,\ldots,N-1\}$, there is a permutation $Q$ such that
$Q\mathcal A Q^T=LDL^T$, with $L$ unit lower triangular and $D$ symmetric block diagonal with
blocks of size one or two. Here the initial numbering is the equivalence $e$ and the pivot
permutation acts by simultaneous reindexing. -/
theorem exists_pivoted_blockLDL {N : ℕ} (hA : A.IsSymm) (hC : C.IsSymm) (e : Fin N ≃ n ⊕ m) :
    ∃ (σ : Equiv.Perm (Fin N)) (L D : Matrix (Fin N) (Fin N) ℝ),
      IsBlockLDL ((saddlePointMatrix A B B C).submatrix (e ∘ σ) (e ∘ σ)) L D := by
  have hM : (saddlePointMatrix A B B C).IsSymm := hA.fromBlocks rfl hC.neg
  obtain ⟨σ, L, D, h⟩ := exists_perm_isBlockLDL (hM.submatrix e)
  exact ⟨σ, L, D, by simpa only [submatrix_submatrix] using h⟩

/-- **Section 7** of [benzi2005numerical], pivot example. This real matrix has order three,
zero diagonal and all off-diagonal entries equal to one. -/
def zeroDiagonalPivotExample : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

/-- **Section 7** of [benzi2005numerical], pivot example. No symmetric permutation of the
printed order-three example admits an $LDL^T$ factorization with $L$ unit lower triangular
and $D$ diagonal. Its zero first diagonal entry forces the entire first row of $LDL^T$
to vanish, in conflict with its nonzero off-diagonal entries. -/
theorem zeroDiagonalPivotExample_no_scalar_ldl (σ : Equiv.Perm (Fin 3)) :
    ¬ ∃ L D, IsLDM (zeroDiagonalPivotExample.submatrix σ σ) L D L := by
  rintro ⟨L, D, h⟩
  have hone := h.isUnitLowerTriangular_left.diag_eq_one 0
  have h01 : L 0 1 = 0 := h.isUnitLowerTriangular_left.isLowerTriangular (by decide)
  have h02 : L 0 2 = 0 := h.isUnitLowerTriangular_left.isLowerTriangular (by decide)
  have hrow (j : Fin 3) : (L * D * Lᵀ) 0 j = D 0 0 * L j 0 := by
    conv_lhs => rw [← h.isDiag.diagonal_diag]
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp [mul_diagonal, hone, h01, h02]
  have hz : D 0 0 = 0 := by
    have hd := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h.mul_eq
    change (L * D * Lᵀ) 0 0 = _ at hd
    simpa [hrow, hone, zeroDiagonalPivotExample] using hd
  have hc := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h.mul_eq
  change (L * D * Lᵀ) 0 1 = _ at hc
  have hne := σ.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  simp [hrow, hz, zeroDiagonalPivotExample, hne] at hc

/-- **Section 7** of [benzi2005numerical]. For $A=B=[1]$ and $C=[0]$, the natural block
order admits (7.2), but the swapped order has first diagonal entry $0$ and off-diagonal
entry $1$. Thus it admits no scalar $LDL^T$ factorization with unit lower triangular $L$. -/
theorem swappedSaddlePoint_no_scalar_ldl_example :
    ¬ ∃ L D, IsLDM (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) L D L := by
  rintro ⟨L, D, h⟩
  have hone := h.isUnitLowerTriangular_left.diag_eq_one 0
  have h01 : L 0 1 = 0 := h.isUnitLowerTriangular_left.isLowerTriangular (by decide)
  have hrow (j : Fin 2) : (L * D * Lᵀ) 0 j = D 0 0 * L j 0 := by
    conv_lhs => rw [← h.isDiag.diagonal_diag]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hone, h01]
  have hz : D 0 0 = 0 := by
    have hd := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h.mul_eq
    change (L * D * Lᵀ) 0 0 = _ at hd
    simpa [hrow, hone] using hd
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h.mul_eq
  change (L * D * Lᵀ) 0 1 = _ at hc
  simp [hrow, hz] at hc

section Block

variable [DecidableEq n]

/-- **Equation (7.2)** of [benzi2005numerical], block formula. Let $A=L_AD_A L_A^T$
and $-S=L_SD_S L_S^T$, with $L_A,D_A$ nonsingular and $D_A$ symmetric. Put
$L_B=B(L_A^T)^{-1}D_A^{-1}$. Then $BA^{-1}B^T=L_BD_A L_B^T$ and
$$\mathcal A=\begin{bmatrix}L_A&0\\L_B&L_S\end{bmatrix}
  \begin{bmatrix}D_A&0\\0&-D_S\end{bmatrix}
  \begin{bmatrix}L_A^T&L_B^T\\0&L_S^T\end{bmatrix}.$$
This algebraic identity only uses the displayed factorizations, not triangularity. -/
theorem saddlePointMatrix_eq_block_ldl {LA DA : Matrix n n ℝ} {LS DS : Matrix m m ℝ}
    (hLA : IsUnit LA) (hDA : IsUnit DA) (hD : DA.IsSymm)
    (hA : A = LA * DA * LAᵀ) (hS : negativeSchurComplement A B B C = LS * DS * LSᵀ) :
    let LB := B * LAᵀ⁻¹ * DA⁻¹
    B * A⁻¹ * Bᵀ = LB * DA * LBᵀ ∧
      saddlePointMatrix A B B C =
        fromBlocks LA 0 LB LS * fromBlocks DA 0 0 (-DS) * fromBlocks LAᵀ LBᵀ 0 LSᵀ := by
  apply fromBlocks_transpose_neg_eq_block_ldl B hLA hDA hD hA
  simpa [add_comm] using hS

end Block

private theorem exists_isLDM_of_posDef {p : Type*} [Fintype p] [LinearOrder p] {M : Matrix p p ℝ}
    (hM : M.PosDef) : ∃ L D, IsLDM M L D L := by
  have hp : M.HasUnitStrictLeadingPrincipalSubmatrices := hM.isUnit_strictLeadingPrincipalSubmatrix
  obtain ⟨⟨L, D, T⟩, h, -⟩ := existsUnique_isLDM hp
  have heq : T = L := h.eq_of_isSymm hM.isSymm hp
  change IsLDM M L D T at h
  exact ⟨L, D, by simpa only [heq] using h⟩

/-- **Equation (7.2)** of [benzi2005numerical], existence. For real matrices $A,B,C$,
suppose $A$ is symmetric positive definite, $C$ is symmetric positive semidefinite, and $B$
has full row rank. For either choice of coordinate ordering within the primal and constraint
blocks, $A$ and $-S$ have unit lower $LDL^T$ factorizations with positive diagonal factors.
Together they give the displayed block factorization of $\mathcal A$ in the original block order.

**Reading.** The immediate discussion assumes symmetry of $C$, but positivity of the negative
Schur complement also uses condition C4 of Section 1.1. Symmetry alone does not suffice:
$A=B=1$ and $C=-1$ give a zero Schur complement. -/
theorem exists_saddlePointMatrix_block_ldl [LinearOrder n] [LinearOrder m]
    (hA : A.PosDef) (hC : C.PosSemidef) (hB : B.rank = Fintype.card m) :
    ∃ (LA DA : Matrix n n ℝ) (LS DS : Matrix m m ℝ),
      IsLDM A LA DA LA ∧ IsLDM (negativeSchurComplement A B B C) LS DS LS ∧
        (∀ i, 0 < DA i i) ∧ (∀ i, 0 < DS i i) ∧
        let LB := B * LAᵀ⁻¹ * DA⁻¹
        saddlePointMatrix A B B C =
          fromBlocks LA 0 LB LS * fromBlocks DA 0 0 (-DS) * fromBlocks LAᵀ LBᵀ 0 LSᵀ := by
  have hBt : Function.Injective Bᵀ.mulVec := mulVec_injective_iff_rank_eq_card.2
    (by simpa only [rank_transpose] using hB)
  have hS : (negativeSchurComplement A B B C).PosDef := by
    simpa using posDef_add_mul_inv_mul_transpose hA hC hBt
  obtain ⟨LA, DA, hLA⟩ := exists_isLDM_of_posDef hA
  obtain ⟨LS, DS, hLS⟩ := exists_isLDM_of_posDef hS
  have hDA : IsUnit DA := isUnit_of_mul_isUnit_right
    (isUnit_of_mul_isUnit_left (hLA.mul_eq.symm ▸ hA.isUnit))
  exact ⟨LA, DA, LS, DS, hLA, hLS, hLA.diag_pos_of_posDef hA, hLS.diag_pos_of_posDef hS,
    (saddlePointMatrix_eq_block_ldl hLA.isUnitLowerTriangular_left.isUnit hDA hLA.isDiag.isSymm
      hLA.mul_eq.symm hLS.mul_eq.symm).2⟩

omit [Fintype n] [Fintype m] in
/-- **Section 7** of [benzi2005numerical], quasidefinite case. If $A$ and $C$ are both real
symmetric positive definite, then for any symmetric permutation of the primal and constraint
coordinates, the reordered $\mathcal A$ has an $LDL^T$ factorization with unit lower triangular
$L$ and diagonal $D$. There is no rank assumption on $B$. -/
theorem exists_quasidefinite_ldl {p : Type*} [Fintype p] [LinearOrder p]
    (hA : A.PosDef) (hC : C.PosDef) (e : p ≃ n ⊕ m) :
    ∃ L D, IsLDM ((saddlePointMatrix A B B C).submatrix e e) L D L := by
  let := Finite.of_injective (e.symm ∘ Sum.inl) (e.symm.injective.comp Sum.inl_injective)
  let := Finite.of_injective (e.symm ∘ Sum.inr) (e.symm.injective.comp Sum.inr_injective)
  exact exists_isLDM_submatrix_fromBlocks_transpose_neg_of_posDef B hA hC e e.injective

end BenziGolubLiesen
