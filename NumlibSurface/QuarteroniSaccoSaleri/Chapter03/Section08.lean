/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.BlockTridiagonal
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.SchurComplement
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section07

/-!
# Quarteroni, Sacco and Saleri, Section 3.8: Block systems

This module formalizes Section 3.8 of [quarteroni2000numerical]. A matrix partitioned into blocks
has a block LU factorization $A = LU$, with $L$ block lower triangular with identity diagonal blocks
and $U$ block upper triangular. For a $2 \times 2$ partition with a nonsingular leading block
$A_{11}$, the factorization comes from the Schur complement
$\Delta_2 = A_{22} - A_{21} A_{11}^{-1} A_{12}$ (Section 3.8.1). The block LU factorization exists
and is unique if and only if the leading block submatrices are nonsingular (Theorem 3.7). The module
also states the Sherman–Morrison–Woodbury formula (3.57) for the inverse of $C + UBV$, and the block
Thomas recurrences for a block tridiagonal matrix (Section 3.8.3).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.SchurComplement` (the Schur
complement `Matrix.schurComplement` and the block $LDU$ factorization
`Matrix.fromBlocks_eq_mul_fromBlocks_of_mul_eq`), `Numlib.LinearAlgebra.Matrix.LU` (the block LU
specification `Matrix.IsBlockLU` along a labelling and its existence and uniqueness theorem
`Matrix.existsUnique_isBlockLU_iff`) and `Numlib.LinearAlgebra.Matrix.NonsingularInverse` (the
Sherman–Morrison–Woodbury formula).

## Main results

* Section 3.8.1, `QuarteroniSaccoSaleri.Chapter03.blockLDU`: the block $LDU$ factorization of a
  $2 \times 2$ block matrix with a factored leading block.
* Theorem 3.7, `QuarteroniSaccoSaleri.Chapter03.theorem_3_7`: the block LU factorization exists and
  is unique if and only if the leading block submatrices are nonsingular.
* (3.57), `QuarteroniSaccoSaleri.Chapter03.equation_3_57`: the Sherman–Morrison–Woodbury formula
  $(C + UBV)^{-1} = C^{-1} - C^{-1} U (I + BVC^{-1}U)^{-1} BVC^{-1}$.
* (3.58), `QuarteroniSaccoSaleri.Chapter03.blockTridiagonal_lu`: the block Thomas recurrences
  $U_1 = A_{11}$, $L_{i-1} U_{i-1} = A_{i,i-1}$, $U_i = A_{ii} - L_{i-1} A_{i-1,i}$.

## Conventions

* A $2 \times 2$ partition of a matrix is `Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂`, indexed by
  `Fin r ⊕ Fin s`, as in Section 3.9. The Schur complement
  $\Delta_2 = A_{22} - A_{21} A_{11}^{-1} A_{12}$ of the leading block is `Matrix.schurComplement`.
* A partition into $m \times m$ blocks is a labelling `b : Fin N → Fin m`. The block $(k, l)$ of a
  matrix `X` is `X.toBlock (b · = k) (b · = l)`. The book's contiguous blocks of sizes
  $n_1, \ldots, n_m$ are a monotone labelling, but no result below needs monotonicity.
* `Matrix.IsBlockLU b A L U` is the book's block LU factorization: $L$ is block lower triangular
  with identity diagonal blocks ("$L$ having unit diagonal entries"), $U$ is block upper triangular,
  and $LU = A$.
* The $m - 1$ "dominant principal block minors" of the book are the leading block submatrices
  `A.toBlock (b · < k) (b · < k)` for the labels $k$ attained by $b$. For the smallest label this
  submatrix is empty, and for the largest label it is $A$ without its last block row and column.

## Deviations from the source

* **Theorem 3.7** (reading). The labelling can omit indices for empty blocks. The leading
  submatrices are tested only at attained labels.
* **Section 3.8.3, the block Thomas factorization** (generalization). The source assumes the shape
  of the factors and reads off the recurrence by equating blocks. The recurrences follow
  from block LU and the leading-minor assumptions, using a proof that derives the shape. See
  `QuarteroniSaccoSaleri.Chapter03.blockTridiagonal_lu`.

## Not formalized

* **The storage counts.**
* **The block Cholesky–Thomas reduction** of a symmetric positive definite block tridiagonal system.
* **The flop count** $(7/6)(n - 1)p^3$.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

/-! ### Section 3.8.1: block LU factorization -/

section BlockLDU

variable {r s : ℕ}

/-- **Section 3.8.1** of [quarteroni2000numerical], the block $LDU$ factorization. Let
$$A = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix}$$
with $A_{11} \in \mathbb{R}^{r \times r}$, $A_{12} \in \mathbb{R}^{r \times s}$,
$A_{21} \in \mathbb{R}^{s \times r}$ and $A_{22} \in \mathbb{R}^{s \times s}$, and let
$A_{11} = L_{11} D_1 R_{11}$ with $L_{11}$, $D_1$, $R_{11}$ nonsingular. Let
$L_{21} = A_{21} R_{11}^{-1} D_1^{-1}$, $R_{12} = D_1^{-1} L_{11}^{-1} A_{12}$ and
$\Delta_2 = A_{22} - L_{21} D_1 R_{12}$. Then $\Delta_2$ is the Schur complement
$A_{22} - A_{21} A_{11}^{-1} A_{12}$ of $A_{11}$, and
$$A = \begin{bmatrix} L_{11} & 0 \\ L_{21} & I \end{bmatrix} \begin{bmatrix} D_1 & 0 \\ 0 &
  \Delta_2 \end{bmatrix} \begin{bmatrix} R_{11} & R_{12} \\ 0 & I \end{bmatrix}.$$

Repeating the reduction on $\Delta_2$ gives the block version of the LU factorization. When
$A_{11}$ is a scalar, it is one step of Gaussian elimination. The proof uses
`Matrix.fromBlocks_eq_mul_fromBlocks_of_mul_eq` and
`Matrix.schurComplement_fromBlocks_of_mul_eq`. -/
theorem blockLDU {A₁₁ L₁₁ D₁ R₁₁ : Matrix (Fin r) (Fin r) ℝ} {A₁₂ R₁₂ : Matrix (Fin r) (Fin s) ℝ}
    {A₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ} {A₂₂ Δ₂ : Matrix (Fin s) (Fin s) ℝ}
    (hL : IsUnit L₁₁) (hD : IsUnit D₁) (hR : IsUnit R₁₁) (hA : A₁₁ = L₁₁ * D₁ * R₁₁)
    (hL₂₁ : L₂₁ = A₂₁ * R₁₁⁻¹ * D₁⁻¹) (hR₁₂ : R₁₂ = D₁⁻¹ * L₁₁⁻¹ * A₁₂)
    (hΔ : Δ₂ = A₂₂ - L₂₁ * D₁ * R₁₂) :
    Δ₂ = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).schurComplement ∧
      fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ =
        fromBlocks L₁₁ 0 L₂₁ 1 * fromBlocks D₁ 0 0 Δ₂ * fromBlocks R₁₁ R₁₂ 0 1 := by
  subst hL₂₁ hR₁₂
  have hΔ' : Δ₂ = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).schurComplement := by
    rw [hΔ, schurComplement_fromBlocks_of_mul_eq hD hA]
  exact ⟨hΔ', by rw [hΔ']; exact fromBlocks_eq_mul_fromBlocks_of_mul_eq hL hD hR hA⟩

end BlockLDU

/-! ### Theorem 3.7 -/

/-- **Theorem 3.7** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{N \times N}$ be partitioned
into $m \times m$ blocks $A_{ij}$ by a labelling $b$ of the indices. Then $A$ admits a unique
block LU factorization, with $L$ having identity diagonal blocks, if and only if the $m - 1$
dominant principal block minors of $A$ are nonzero, that is, if and only if the leading block
submatrix $A(b < k)$ is nonsingular for every label $k$ that $b$ attains.

The theorem extends Theorem 3.4, which is the case $m = N$ and $b = \mathrm{id}$
(`Matrix.isBlockLU_id_iff`). The factorization is `Matrix.IsBlockLU b A L U`, and $A(b < k)$ is
`A.toBlock (b · < k) (b · < k)`. The proof specializes `Matrix.existsUnique_isBlockLU_iff`.

**Reading.** The label function need not use every block label. Leading blocks are tested
only for attained labels, so empty blocks do not add constraints. -/
theorem theorem_3_7 {N m : ℕ} (b : Fin N → Fin m) (A : Matrix (Fin N) (Fin N) ℝ) :
    (∃! LU : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ, IsBlockLU b A LU.1 LU.2) ↔
      ∀ k ∈ Set.range b, IsUnit (A.toBlock (b · < k) (b · < k)) :=
  existsUnique_isBlockLU_iff b A

/-! ### Section 3.8.2: the inverse of a block-partitioned matrix -/

/-- **Equation (3.57)** of [quarteroni2000numerical] (the Sherman–Morrison or Woodbury formula). Let
$C \in \mathbb{R}^{n \times n}$ be nonsingular, let $U \in \mathbb{R}^{n \times m}$,
$B \in \mathbb{R}^{m \times m}$ and $V \in \mathbb{R}^{m \times n}$, and assume that
$I + BVC^{-1}U$ is nonsingular. Then
$$(C + UBV)^{-1} = C^{-1} - C^{-1} U (I + BVC^{-1}U)^{-1} BVC^{-1}.$$

The matrix $B$ may be singular, unlike in Mathlib's `Matrix.add_mul_mul_inv_eq_sub`. The formula
is effective when $C$, for instance the block diagonal of $A = C + UBV$, is easy to invert, and
$U$, $B$, $V$ carry connections of modest relevance between the diagonal blocks. The proof uses
`Matrix.add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add`. -/
theorem equation_3_57 {n m : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} (hC : IsUnit C)
    (U : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin m) (Fin n) ℝ)
    (hW : IsUnit (1 + B * V * C⁻¹ * U)) :
    (C + U * B * V)⁻¹ = C⁻¹ - C⁻¹ * U * (1 + B * V * C⁻¹ * U)⁻¹ * B * V * C⁻¹ :=
  add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add hC U B V hW

/-! ### Section 3.8.3: block tridiagonal systems -/

section BlockTridiagonal

variable {N m : ℕ} {b : Fin N → Fin m} {A L U : Matrix (Fin N) (Fin N) ℝ}

/-- **Equation (3.58)** of [quarteroni2000numerical], Section 3.8.3, the block Thomas factorization.
Let $A \in \mathbb{R}^{N \times N}$ be partitioned into blocks $A_{ij}$ by a labelling $b$, and
let $A$ be block tridiagonal: $A_{ij} = 0$ for $|i - j| > 1$. Assume that the leading block
submatrices $A(b \le k)$ are nonsingular for every label $k$, and let $A = LU$ be a block LU
factorization. Then:

* the first diagonal block of $U$ is $U_1 = A_{11}$;
* the superdiagonal blocks of $U$ are those of $A$: $U_{i-1,i} = A_{i-1,i}$;
* the subdiagonal block $L_{i,i-1}$ of $L$ solves $L_{i,i-1} U_{i-1} = A_{i,i-1}$;
* the diagonal blocks of $U$ are $U_i = A_{ii} - L_{i,i-1} A_{i-1,i}$.

The blocks are thus obtained sequentially for $i = 2, \ldots, m$.

**Generalization.** The source assumes that $L$ is block unit lower bidiagonal and $U$ is block
upper bidiagonal, and reads off the recurrence by equating blocks. Here the shape is proved:
`Matrix.IsBlockLU.blockBidiagonal_of_blockTridiagonal` is the block form of Property 3.4, with
the lower clause under the hypothesis of Theorem 3.7, as in Section 3.7. The recurrences hold
under the stated leading-block nonsingularity assumption.

The book writes $L_{i-1}$ for the block $L_{i,i-1}$. The first block is the block of the
smallest label, the one with $k \le b(i)$ for all indices $i$. The proof uses
`Matrix.IsBlockLU.toBlock_recurrence_of_blockTridiagonal`. -/
theorem blockTridiagonal_lu (h : IsBlockLU b A L U)
    (htriL : ∀ i j, (b j : ℕ) + 1 < b i → A i j = 0)
    (htriU : ∀ i j, (b i : ℕ) + 1 < b j → A i j = 0)
    (hlead : ∀ k : Fin m, IsUnit (A.toBlock (b · ≤ k) (b · ≤ k))) :
    (∀ k : Fin m, (∀ i, k ≤ b i) →
        U.toBlock (b · = k) (b · = k) = A.toBlock (b · = k) (b · = k)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        U.toBlock (b · = k) (b · = l) = A.toBlock (b · = k) (b · = l)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        L.toBlock (b · = l) (b · = k) * U.toBlock (b · = k) (b · = k) =
          A.toBlock (b · = l) (b · = k)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        U.toBlock (b · = l) (b · = l) = A.toBlock (b · = l) (b · = l) -
          L.toBlock (b · = l) (b · = k) * A.toBlock (b · = k) (b · = l)) :=
  h.toBlock_recurrence_of_blockTridiagonal htriL htriU hlead

end BlockTridiagonal

end QuarteroniSaccoSaleri.Chapter03
