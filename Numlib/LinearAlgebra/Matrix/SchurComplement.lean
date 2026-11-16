/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.SchurComplement`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.Analysis.Matrix.SpectralNorm

/-!
# The Schur complement of a block matrix

Let $R$ be a commutative ring and let
$$A = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix}$$
be a square block matrix over $R$, with $A_{11}$ of order $m$ and $A_{22}$ of order $n$. The **Schur
complement** of $A_{11}$ in $A$ is $S = A_{22} - A_{21} A_{11}^{-1} A_{12}$. In the notation $A =
\begin{bmatrix} B & E \\ F & C \end{bmatrix}$ of [saad2003iterative] (14.5) it is
$S = C - F B^{-1} E$. When $A_{11}$ is nonsingular, $A$ has block LU and block LDU factorizations
with $S$ in the $(2,2)$ position, $A$ is nonsingular if and only if $S$ is, and the $(2,2)$ block of
$A^{-1}$ is $S^{-1}$. The last fact lets a preconditioner for the interface system be built out of a
solver for $A$. For a Hermitian positive definite $A$, the Schur complement is positive definite, it
satisfies $S \le A_{22}$ in the Loewner order, and it is better conditioned than $A$ in the spectral
norm. When the interior block $A_{11}$ is block diagonal, the Schur complement is the sum of the
local Schur complements of the subdomains. Every preconditioner assembled from local Schur
complements rests on this.

The module also treats the Schur complement of a single pivot, which is one step of Gaussian
elimination and the form that incomplete factorizations use ([saad2003iterative] Theorem 10.1), and
the saddle-point matrix $\begin{bmatrix} A & B \\ B^H & D \end{bmatrix}$ of [golub2013matrix] §4.4.5
and [saad2003iterative] (8.30).

## Main definitions

* `Matrix.schurComplement`: the Schur complement $A_{22} - A_{21} A_{11}^{-1} A_{12}$ of the $(1,1)$
  block.
* `Matrix.schurComplementSingle`: for a pivot index $p$, the matrix with entries
  $a_{ij} - a_{ip} a_{pp}^{-1} a_{pj}$ for $i, j \neq p$.
* `Matrix.saddleMatrix`: the saddle-point matrix $\begin{bmatrix} A & B \\ B^H & D \end{bmatrix}$.

## Main results

* `Matrix.fromBlocks_eq_mul_fromBlocks_schurComplement`, `Matrix.fromBlocks_eq_mul_schurComplement`:
  the block LU and block LDU factorizations for a nonsingular $(1,1)$ block.
* `Matrix.isUnit_schurComplement_iff`: if $A_{11}$ is nonsingular, then $A$ is nonsingular if and
  only if $S$ is.
* `Matrix.inv_fromBlocks_eq`, `Matrix.toBlocks₂₂_inv_eq_inv_schurComplement`: the block inverse, and
  $(A^{-1})_{22} = S^{-1}$.
* `Matrix.PosDef.schurComplement`: the Schur complement of a positive definite matrix is positive
  definite.
* `Matrix.PosDef.schurComplement_loewner_le`: for a positive definite $A$, the matrix $A_{22} - S$
  is positive semidefinite.
* `Matrix.l2_opNorm_le_of_posSemidef_of_posSemidef_sub`: if $0 \le X \le Y$ in the Loewner order,
  then $\|X\|_2 \le \|Y\|_2$.
* `Matrix.PosDef.condNumber_schurComplement_le`: for a positive definite $A$,
  $\|S\|_2 \|S^{-1}\|_2 \le \|A\|_2 \|A^{-1}\|_2$ ([quarteroni2000numerical] Remark 3.6).
* `Matrix.fromBlocks_eq_mul_fromBlocks_of_mul_eq`: the block LDU factorization of
  [quarteroni2000numerical] §3.8.1, built from a factorization $A_{11} = L_{11} D_1 R_{11}$ of the
  leading block.
* `Matrix.isUnit_blockDiagonal'`, `Matrix.inv_blockDiagonal'`, `Matrix.mul_blockDiagonal'_mul`: a
  block diagonal matrix with invertible blocks is invertible, its inverse is block diagonal, and a
  product $F \operatorname{diag}(M_i) E$ is a sum over the blocks.
* `Matrix.schurComplement_fromBlocks_blockDiagonal'`: if the interior block is block diagonal and
  the interface block is a sum of local contributions, then $S = \sum_i S_i$ ([saad2003iterative]
  (14.16)).
* `Matrix.schurComplementSingle_mulVec_of_apply_eq_zero`: if $(Ax)_p = 0$, then the single-pivot
  Schur complement applied to the restriction of $x$ reproduces $Ax$ off the pivot row.
* `Matrix.isUnit_schurComplementSingle`, `Matrix.inv_schurComplementSingle`: the single-pivot Schur
  complement of a nonsingular matrix is nonsingular, and its inverse is the submatrix of $A^{-1}$ on
  the indices other than the pivot.
* `Matrix.saddleMatrix_mulVec_elim`: the block equations of a saddle-point system.
* `Matrix.PosDef.conjTranspose_mul_inv_mul`: $B^H A^{-1} B$ is positive definite for a positive
  definite $A$ and a $B$ of full column rank.
* `Matrix.isUnit_saddleMatrix_zero`, `Matrix.saddleMatrix_zero_eq_mul`,
  `Matrix.saddleMatrix_zero_mulVec_snd_eq`: the nonsingularity (4.4.18), the triangular
  factorization and the reduced equation (4.4.20) of the equilibrium matrix
  $\begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix}$ of [golub2013matrix].

## Implementation notes

* The hypotheses are `IsUnit`, not `Invertible`, because a nonsingularity hypothesis takes that form
  downstream. Each proof turns them into `Invertible` instances, and `Matrix.invOf_eq_nonsing_inv`
  identifies `⅟` with `⁻¹`.
* Indexing is by a sum type `m ⊕ n` throughout, so that `Matrix.toBlocks₁₁`, …, `Matrix.toBlocks₂₂`
  apply and no reindexing equivalence appears in the statements.
* The inverse is `Matrix.inv`, which is $0$ for a singular matrix. So when $A_{11}$ is singular,
  `Matrix.schurComplement` is $A_{22}$.
* Mathlib's `Mathlib.LinearAlgebra.Matrix.SchurComplement` has the block LDU identity, the
  determinant formulas and the positive semidefinite criterion `Matrix.PosDef.fromBlocks₁₁`, but it
  does not name the Schur complement and proves nothing about its inverse.
* `Matrix.schurComplementSingle` is not connected to `Matrix.schurComplement` here. The connecting
  identity is `A.schurComplementSingle p = (A.submatrix e e).schurComplement` for the reindexing
  `e = Equiv.sumCompl (· = p)` of `{i // i = p} ⊕ {i // i ≠ p}` as `n`.
-/

open Function
open scoped ComplexOrder

namespace Matrix

variable {m n R : Type*}

section Def

variable [Fintype m] [DecidableEq m] [CommRing R]

/-- Let $R$ be a commutative ring and let $A$ be a square matrix over $R$ indexed by $m \oplus n$,
with blocks $A_{11}, A_{12}, A_{21}, A_{22}$. The **Schur complement** of the block $A_{11}$ is
$$S = A_{22} - A_{21} A_{11}^{-1} A_{12} \in R^{n \times n}.$$
In the notation of [saad2003iterative] (14.5), this is $S = C - F B^{-1} E$.

When $A_{11}$ is singular, the definition gives $S = A_{22}$, because the inverse `Matrix.inv`
of a singular matrix is $0$. The definition is `noncomputable` because `Matrix.inv` is. -/
noncomputable def schurComplement (A : Matrix (m ⊕ n) (m ⊕ n) R) : Matrix n n R :=
  A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₁⁻¹ * A.toBlocks₁₂

/-- The Schur complement of $A$ is $A_{22} - A_{21} A_{11}^{-1} A_{12}$, by definition. -/
theorem schurComplement_eq (A : Matrix (m ⊕ n) (m ⊕ n) R) :
    A.schurComplement = A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₁⁻¹ * A.toBlocks₁₂ := rfl

/-- Let $B \in R^{m \times m}$, $E \in R^{m \times n}$, $F \in R^{n \times m}$ and
$C \in R^{n \times n}$. The Schur complement of $B$ in the block matrix
$\begin{bmatrix} B & E \\ F & C \end{bmatrix}$ is
$$C - F B^{-1} E.$$

This is the `simp` normal form of the Schur complement of a block matrix. -/
@[simp]
theorem schurComplement_fromBlocks (B : Matrix m m R) (E : Matrix m n R) (F : Matrix n m R)
    (C : Matrix n n R) : (fromBlocks B E F C).schurComplement = C - F * B⁻¹ * E := rfl

end Def

section Factorization

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
variable {B : Matrix m m R} {E : Matrix m n R} {F : Matrix n m R} {C : Matrix n n R}

/-- The **block LU factorization**. Let $B \in R^{m \times m}$ be invertible, let
$E \in R^{m \times n}$, $F \in R^{n \times m}$ and $C \in R^{n \times n}$, and let
$S = C - F B^{-1} E$ be the Schur complement of $B$. Then
$$\begin{bmatrix} B & E \\ F & C \end{bmatrix}
  = \begin{bmatrix} I & 0 \\ F B^{-1} & I \end{bmatrix}
  \begin{bmatrix} B & E \\ 0 & S \end{bmatrix}.$$
This is (14.6) of [saad2003iterative]. -/
theorem fromBlocks_eq_mul_fromBlocks_schurComplement (hB : IsUnit B) :
    fromBlocks B E F C
      = fromBlocks 1 0 (F * B⁻¹) 1 * fromBlocks B E 0 (fromBlocks B E F C).schurComplement := by
  have hinv : B⁻¹ * B = 1 := nonsing_inv_mul B ((isUnit_iff_isUnit_det B).1 hB)
  simp only [schurComplement_fromBlocks, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_assoc, hinv, add_sub_cancel]

/-- The **block LDU factorization**. Let $B \in R^{m \times m}$ be invertible, let
$E \in R^{m \times n}$, $F \in R^{n \times m}$ and $C \in R^{n \times n}$, and let
$S = C - F B^{-1} E$ be the Schur complement of $B$. Then
$$\begin{bmatrix} B & E \\ F & C \end{bmatrix}
  = \begin{bmatrix} I & 0 \\ F B^{-1} & I \end{bmatrix}
  \begin{bmatrix} I & 0 \\ 0 & S \end{bmatrix} \begin{bmatrix} B & E \\ 0 & I \end{bmatrix}.$$
This is (14.52) of [saad2003iterative].

The first factor is unit block lower triangular. The last factor is block upper triangular with
the diagonal blocks $B$ and $I$, so it is unit block triangular only when $B = I$. -/
theorem fromBlocks_eq_mul_schurComplement (hB : IsUnit B) :
    fromBlocks B E F C
      = fromBlocks 1 0 (F * B⁻¹) 1 * fromBlocks 1 0 0 (fromBlocks B E F C).schurComplement
        * fromBlocks B E 0 1 := by
  have hDU : fromBlocks (1 : Matrix m m R) 0 0 (fromBlocks B E F C).schurComplement
      * fromBlocks B E 0 1 = fromBlocks B E 0 (fromBlocks B E F C).schurComplement := by
    simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.mul_assoc, hDU]
  exact fromBlocks_eq_mul_fromBlocks_schurComplement hB

end Factorization

section IsUnit

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]

/-- Let $A$ be a square matrix over $R$ indexed by $m \oplus n$ whose block $A_{11}$ is invertible.
Then the Schur complement $S$ of $A_{11}$ is invertible if and only if $A$ is invertible. This
is part (1) of Proposition 14.1 of [saad2003iterative]. -/
theorem isUnit_schurComplement_iff {A : Matrix (m ⊕ n) (m ⊕ n) R} (hB : IsUnit A.toBlocks₁₁) :
    IsUnit A.schurComplement ↔ IsUnit A := by
  let _ := hB.invertible
  have h1 : A.toBlocks₁₁⁻¹ = ⅟A.toBlocks₁₁ := (invOf_eq_nonsing_inv _).symm
  rw [schurComplement_eq, h1, ← isUnit_fromBlocks_iff_of_invertible₁₁, fromBlocks_toBlocks]

/-- Let $A$ be an invertible square matrix over $R$ indexed by $m \oplus n$ whose block $A_{11}$ is
invertible. Then the Schur complement of $A_{11}$ is invertible. This is part (1) of Proposition
14.1 of [saad2003iterative].

This is one direction of `Matrix.isUnit_schurComplement_iff`. -/
theorem isUnit_schurComplement {A : Matrix (m ⊕ n) (m ⊕ n) R} (hB : IsUnit A.toBlocks₁₁)
    (hA : IsUnit A) : IsUnit A.schurComplement :=
  (isUnit_schurComplement_iff hB).2 hA

/-- Let $A$ be a square matrix over $R$ indexed by $m \oplus n$ whose block $A_{11}$ is invertible.
If the Schur complement of $A_{11}$ is invertible, then $A$ is invertible.

This is the converse of `Matrix.isUnit_schurComplement`, and the other direction of
`Matrix.isUnit_schurComplement_iff`. -/
theorem isUnit_of_isUnit_schurComplement {A : Matrix (m ⊕ n) (m ⊕ n) R}
    (hB : IsUnit A.toBlocks₁₁) (hS : IsUnit A.schurComplement) : IsUnit A :=
  (isUnit_schurComplement_iff hB).1 hS

end IsUnit

section Inverse

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
variable {B : Matrix m m R} {E : Matrix m n R} {F : Matrix n m R} {C : Matrix n n R}

/-- The **block inverse**. Let $B \in R^{m \times m}$ be invertible, let $E \in R^{m \times n}$,
$F \in R^{n \times m}$ and $C \in R^{n \times n}$, let the block matrix
$\begin{bmatrix} B & E \\ F & C \end{bmatrix}$ be invertible, and let $S = C - F B^{-1} E$. Then
$$\begin{bmatrix} B & E \\ F & C \end{bmatrix}^{-1}
  = \begin{bmatrix} B^{-1} + B^{-1} E S^{-1} F B^{-1} & -B^{-1} E S^{-1} \\
  -S^{-1} F B^{-1} & S^{-1} \end{bmatrix}.$$
This is (14.7) of [saad2003iterative]. -/
theorem inv_fromBlocks_eq (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    (fromBlocks B E F C)⁻¹
      = fromBlocks (B⁻¹ + B⁻¹ * E * (C - F * B⁻¹ * E)⁻¹ * F * B⁻¹)
          (-(B⁻¹ * E * (C - F * B⁻¹ * E)⁻¹))
          (-((C - F * B⁻¹ * E)⁻¹ * F * B⁻¹)) (C - F * B⁻¹ * E)⁻¹ := by
  let iB := hB.invertible
  let iA := hA.invertible
  have hBinv : ⅟B = B⁻¹ := invOf_eq_nonsing_inv B
  have hSB : C - F * ⅟B * E = C - F * B⁻¹ * E := by rw [hBinv]
  have hS : IsUnit (C - F * B⁻¹ * E) := by
    have := isUnit_schurComplement (A := fromBlocks B E F C) (by simpa using hB) hA
    simpa using this
  let iS : Invertible (C - F * ⅟B * E) := by rw [hSB]; exact hS.invertible
  have hSinv : ⅟(C - F * ⅟B * E) = (C - F * B⁻¹ * E)⁻¹ := by
    rw [invOf_eq_nonsing_inv, hSB]
  rw [← invOf_eq_nonsing_inv (fromBlocks B E F C), invOf_fromBlocks₁₁_eq B E F C, hSinv, hBinv]

/-- Let $A$ be an invertible square matrix over $R$ indexed by $m \oplus n$ whose block $A_{11}$ is
invertible, and let $S$ be the Schur complement of $A_{11}$. Then the $(2,2)$ block of the
inverse is the inverse of the Schur complement:
$$(A^{-1})_{22} = S^{-1}.$$
This is part (3) of Proposition 14.1 of [saad2003iterative].

This identity lets a preconditioner for the interface system $Sy = g$ be built out of a solver
for $A$. -/
theorem toBlocks₂₂_inv_eq_inv_schurComplement {A : Matrix (m ⊕ n) (m ⊕ n) R}
    (hB : IsUnit A.toBlocks₁₁) (hA : IsUnit A) :
    (A⁻¹).toBlocks₂₂ = A.schurComplement⁻¹ := by
  conv_lhs => rw [← fromBlocks_toBlocks A]
  rw [inv_fromBlocks_eq hB (by rwa [fromBlocks_toBlocks]), toBlocks_fromBlocks₂₂]
  rfl

end Inverse

section Additive

variable {o : Type*} [Fintype o] [DecidableEq o] {m' : o → Type*}
variable [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommRing R]

/-- Let $o$ be a finite index set, and for each $i \in o$ let $M_i$ be a square matrix over $R$
indexed by a finite type $m'_i$. If every $M_i$ is invertible, then the block diagonal matrix
$\operatorname{diag}(M_i)_{i \in o}$ is invertible.

The block diagonal matrix is `Matrix.blockDiagonal'`, indexed by the sigma type
$\Sigma_i \, m'_i$. Only this direction of the equivalence is stated. -/
theorem isUnit_blockDiagonal' (M : ∀ i, Matrix (m' i) (m' i) R) (hM : ∀ i, IsUnit (M i)) :
    IsUnit (blockDiagonal' M) := by
  refine IsUnit.of_mul_eq_one (blockDiagonal' fun i => (M i)⁻¹) ?_
  rw [← blockDiagonal'_mul]
  have h : (fun i => M i * (M i)⁻¹) = (1 : ∀ i, Matrix (m' i) (m' i) R) := funext fun i => by
    rw [Pi.one_apply]
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (hM i))
  rw [h, blockDiagonal'_one]

/-- Let $o$ be a finite index set, and for each $i \in o$ let $M_i$ be an invertible square matrix
over $R$ indexed by a finite type $m'_i$. Then the inverse of the block diagonal matrix of the
$M_i$ is the block diagonal matrix of the inverses:
$$\operatorname{diag}(M_i)_{i \in o}^{-1} = \operatorname{diag}(M_i^{-1})_{i \in o}.$$
-/
theorem inv_blockDiagonal' (M : ∀ i, Matrix (m' i) (m' i) R) (hM : ∀ i, IsUnit (M i)) :
    (blockDiagonal' M)⁻¹ = blockDiagonal' fun i => (M i)⁻¹ := by
  refine inv_eq_right_inv ?_
  have h : (fun i => M i * (M i)⁻¹) = (1 : ∀ i, Matrix (m' i) (m' i) R) := funext fun i => by
    rw [Pi.one_apply]
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (hM i))
  rw [← blockDiagonal'_mul, h, blockDiagonal'_one]

omit [∀ i, DecidableEq (m' i)] in
/-- Let $o$ be a finite index set, and for each $i \in o$ let $M_i$ be a square matrix over $R$
indexed by a finite type $m'_i$. Let $F$ be a matrix whose columns are indexed by
$\Sigma_i \, m'_i$, and $E$ a matrix whose rows are indexed by $\Sigma_i \, m'_i$. Then
$$F \operatorname{diag}(M_i)_{i \in o} \, E = \sum_{i \in o} F_i M_i E_i,$$
where $F_i$ is the block of the columns of $F$ in $m'_i$ and $E_i$ is the block of the rows of
$E$ in $m'_i$. -/
theorem mul_blockDiagonal'_mul {n : Type*} (F : Matrix n (Σ i, m' i) R)
    (M : ∀ i, Matrix (m' i) (m' i) R) (E : Matrix (Σ i, m' i) n R) :
    F * blockDiagonal' M * E
      = ∑ i, F.submatrix id (Sigma.mk i) * M i * E.submatrix (Sigma.mk i) id := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, submatrix_apply, id_eq, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  refine congrArg₂ _ ?_ rfl
  refine (Fintype.sum_eq_single i fun j hj => Finset.sum_eq_zero fun k _ => ?_).trans
    (Finset.sum_congr rfl fun k _ => ?_)
  · rw [blockDiagonal'_apply_ne _ _ _ hj, mul_zero]
  · rw [blockDiagonal'_apply_eq]

/-- The **Schur complement is additive over the subdomains**. Let $o$ be a finite index set, and for
each $i \in o$ let $B_i$ be an invertible square matrix over $R$ indexed by a finite type $m'_i$
and let $C_i \in R^{n \times n}$. Let $E$ have rows indexed by $\Sigma_i \, m'_i$ and columns
indexed by $n$, let $F$ have rows indexed by $n$ and columns indexed by $\Sigma_i \, m'_i$, and
let $E_i$ and $F_i$ be their blocks of rows and of columns in $m'_i$. Then the Schur complement
of the interior block $\operatorname{diag}(B_i)_{i \in o}$ in
$$\begin{bmatrix} \operatorname{diag}(B_i)_{i \in o} & E \\ F & \sum_i C_i \end{bmatrix}$$
is the sum of the local Schur complements:
$$S = \sum_{i \in o} \bigl(C_i - F_i B_i^{-1} E_i\bigr).$$
This is (14.16) of [saad2003iterative].

The derivation in the source is for finite elements, but the identity is block algebra and holds
for any such decomposition. -/
theorem schurComplement_fromBlocks_blockDiagonal' {n : Type*} (B : ∀ i, Matrix (m' i) (m' i) R)
    (E : Matrix (Σ i, m' i) n R) (F : Matrix n (Σ i, m' i) R) (C : o → Matrix n n R)
    (hB : ∀ i, IsUnit (B i)) :
    (fromBlocks (blockDiagonal' B) E F (∑ i, C i)).schurComplement
      = ∑ i, (fromBlocks (B i) (E.submatrix (Sigma.mk i) id) (F.submatrix id (Sigma.mk i))
          (C i)).schurComplement := by
  simp only [schurComplement_fromBlocks]
  rw [inv_blockDiagonal' B hB, mul_blockDiagonal'_mul, Finset.sum_sub_distrib]

end Additive

section PosDef

variable {K : Type*} [Field K] [PartialOrder K] [StarRing K]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- Let $K$ be a field with a partial order and a star operation, and let $A$ be a Hermitian
positive definite matrix over $K$ indexed by $m \oplus n$. Then the Schur complement of $A_{11}$
is Hermitian positive definite. This is part (2) of Proposition 14.1 of [saad2003iterative].

Mathlib's `Matrix.PosDef.fromBlocks₁₁` gives only the positive semidefinite equivalence. The
strict form here comes from `Matrix.toBlocks₂₂_inv_eq_inv_schurComplement`: $A^{-1}$ is positive
definite, so its principal submatrix $S^{-1}$ is positive definite, and so is its inverse $S$. -/
theorem PosDef.schurComplement {A : Matrix (m ⊕ n) (m ⊕ n) K} (hA : A.PosDef) :
    A.schurComplement.PosDef := by
  have h11 : A.toBlocks₁₁.PosDef := Matrix.PosDef.submatrix hA Sum.inl_injective
  have hAinv : (A⁻¹).PosDef := Matrix.PosDef.inv hA
  have h22 : ((A⁻¹).toBlocks₂₂).PosDef := Matrix.PosDef.submatrix hAinv Sum.inr_injective
  rw [toBlocks₂₂_inv_eq_inv_schurComplement (Matrix.PosDef.isUnit h11)
    (Matrix.PosDef.isUnit hA)] at h22
  exact Matrix.posDef_inv_iff.1 h22

end PosDef

section Single

variable {K : Type*} [Field K]

/-- Let $K$ be a field, $A \in K^{n \times n}$, and $p$ an index, the pivot. The **single-pivot
Schur complement** of $A$ at $p$ is the matrix indexed by the indices $i, j \neq p$ with the
entries
$$a_{ij} - a_{ip} \, a_{pp}^{-1} \, a_{pj}.$$
It is the result of one step of Gaussian elimination with the pivot $a_{pp}$.

It is the trailing block of the matrix $A_1$ of [saad2003iterative] Theorem 10.1. The matrix
$A_1$ of the source is square on all $n$ indices, keeps the pivot row and has a zero pivot
column. It is the matrix whose incomplete factorizations Chapter 10 of the source studies. If
$a_{pp} = 0$, then $a_{pp}^{-1}$ is $0$ in Lean and the entries are $a_{ij}$. -/
noncomputable def schurComplementSingle (A : Matrix n n K) (p : n) :
    Matrix {i : n // i ≠ p} {i : n // i ≠ p} K :=
  Matrix.of fun i j => A i.1 j.1 - A i.1 p * (A p p)⁻¹ * A p j.1

/-- The entry $(i, j)$ of the single-pivot Schur complement of $A$ at $p$ is
$a_{ij} - a_{ip} a_{pp}^{-1} a_{pj}$. -/
@[simp]
theorem schurComplementSingle_apply (A : Matrix n n K) (p : n) (i j : {i : n // i ≠ p}) :
    A.schurComplementSingle p i j = A i.1 j.1 - A i.1 p * (A p p)⁻¹ * A p j.1 := rfl

/-- Let $K$ be a field, $A \in K^{n \times n}$, and $p$ a pivot index. The transpose of the
single-pivot Schur complement of $A$ at $p$ is the single-pivot Schur complement of $A^T$ at
$p$. -/
theorem schurComplementSingle_transpose (A : Matrix n n K) (p : n) :
    (A.schurComplementSingle p)ᵀ = Aᵀ.schurComplementSingle p := by
  ext i j
  simp only [transpose_apply, schurComplementSingle_apply]
  ring

variable [Fintype n] [DecidableEq n]

/-- For every row $t$, $\sum_{j \neq p} a_{tj} x_j = (Ax)_t - a_{tp} x_p$. -/
private theorem sum_ne_eq_mulVec_sub (A : Matrix n n K) (X : n → K) (p t : n) :
    ∑ j : {x : n // x ≠ p}, A t j.1 * X j.1 = (A *ᵥ X) t - A t p * X p := by
  rw [← Finset.sum_subtype (p := fun x => x ≠ p) (Finset.univ.erase p) (fun x => by simp)
      fun j => A t j * X j, Matrix.mulVec_apply_eq_sum,
    ← Finset.add_sum_erase _ (fun j => A t j * X j) (Finset.mem_univ p)]
  ring

/-- Let $K$ be a field, let $A \in K^{n \times n}$ with $n$ finite, let $p$ be an index with
$a_{pp} \neq 0$, and let $x \in K^n$ satisfy $(Ax)_p = 0$. Let $S$ be the single-pivot Schur
complement of $A$ at $p$, and let $x'$ be the restriction of $x$ to the indices other than $p$.
Then
$$(S x')_i = (Ax)_i \quad \text{for every } i \neq p.$$

This is the content of one step of Gaussian elimination: $x$ is recovered from $x'$ by
back-substitution in the pivot row, $a_{pp} x_p = -\sum_{j \neq p} a_{pj} x_j$. -/
theorem schurComplementSingle_mulVec_of_apply_eq_zero (A : Matrix n n K) {p : n}
    (hpp : A p p ≠ 0) {X : n → K} (hX : (A *ᵥ X) p = 0) (i : {x : n // x ≠ p}) :
    (A.schurComplementSingle p *ᵥ fun t : {x : n // x ≠ p} => X t.1) i = (A *ᵥ X) i.1 := by
  have hp := sum_ne_eq_mulVec_sub A X p p
  rw [hX, zero_sub] at hp
  have hXp : (A p p)⁻¹ * ∑ j : {x : n // x ≠ p}, A p j.1 * X j.1 = -X p := by
    rw [hp]; field_simp
  have expand : ∑ j : {x : n // x ≠ p}, A.schurComplementSingle p i j * X j.1
      = (∑ j : {x : n // x ≠ p}, A i.1 j.1 * X j.1)
        - ∑ j : {x : n // x ≠ p}, A i.1 p * (A p p)⁻¹ * (A p j.1 * X j.1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Matrix.schurComplementSingle_apply]; ring
  have pull : ∑ j : {x : n // x ≠ p}, A i.1 p * (A p p)⁻¹ * (A p j.1 * X j.1)
      = A i.1 p * (A p p)⁻¹ * ∑ j : {x : n // x ≠ p}, A p j.1 * X j.1 := by
    rw [Finset.mul_sum]
  have lhs : (A.schurComplementSingle p *ᵥ fun t : {x : n // x ≠ p} => X t.1) i
      = ∑ j : {x : n // x ≠ p}, A.schurComplementSingle p i j * X j.1 :=
    Matrix.mulVec_apply_eq_sum _ _ _
  rw [lhs, expand, pull, mul_assoc, hXp, sum_ne_eq_mulVec_sub A X p i.1]
  ring

/-- Let $A \in K^{n \times n}$ be invertible with $a_{pp} \neq 0$, and let $S$ be the single-pivot
Schur complement of $A$ at $p$. Then $S \, (A^{-1})' = I$, where $(A^{-1})'$ is the submatrix of
$A^{-1}$ on the indices other than $p$. -/
theorem schurComplementSingle_mul_submatrix_inv {A : Matrix n n K} {p : n} (hA : IsUnit A)
    (hpp : A p p ≠ 0) :
    A.schurComplementSingle p * A⁻¹.submatrix Subtype.val Subtype.val = 1 := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hA
  ext i j
  have hcol : ∀ s : n, (A *ᵥ fun t => A⁻¹ t j.1) s = (1 : Matrix n n K) s j.1 := fun s => by
    rw [Matrix.mulVec_apply_eq_sum, ← Matrix.mul_apply, mul_nonsing_inv A hdet]
  have hzero : (A *ᵥ fun t => A⁻¹ t j.1) p = 0 := by
    rw [hcol p, Matrix.one_apply_ne (Ne.symm j.2)]
  have h := schurComplementSingle_mulVec_of_apply_eq_zero A hpp hzero i
  rw [hcol i.1] at h
  have hone : (1 : Matrix n n K) i.1 j.1
      = (1 : Matrix {x : n // x ≠ p} {x : n // x ≠ p} K) i j := by
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne (Subtype.coe_injective.ne hij), Matrix.one_apply_ne hij]
  exact h.trans hone

/-- Let $A \in K^{n \times n}$ be invertible with $a_{pp} \neq 0$. Then the single-pivot Schur
complement of $A$ at $p$ is invertible. -/
theorem isUnit_schurComplementSingle {A : Matrix n n K} {p : n} (hA : IsUnit A) (hpp : A p p ≠ 0) :
    IsUnit (A.schurComplementSingle p) :=
  have h := schurComplementSingle_mul_submatrix_inv hA hpp
  ⟨⟨_, _, h, _root_.mul_eq_one_comm.1 h⟩, rfl⟩

/-- Let $A \in K^{n \times n}$ be invertible with $a_{pp} \neq 0$, and let $S$ be the single-pivot
Schur complement of $A$ at $p$. Then $S^{-1}$ is the submatrix of $A^{-1}$ on the indices other
than $p$.

This is the single-pivot form of `Matrix.toBlocks₂₂_inv_eq_inv_schurComplement`. -/
theorem inv_schurComplementSingle {A : Matrix n n K} {p : n} (hA : IsUnit A) (hpp : A p p ≠ 0) :
    (A.schurComplementSingle p)⁻¹ = A⁻¹.submatrix Subtype.val Subtype.val :=
  Matrix.inv_eq_right_inv (schurComplementSingle_mul_submatrix_inv hA hpp)

end Single

section BlockLDU

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
variable {A₁₁ L₁₁ D₁ R₁₁ : Matrix m m R} {A₁₂ : Matrix m n R} {A₂₁ : Matrix n m R}
  {A₂₂ : Matrix n n R}

omit [Fintype n] [DecidableEq n] in
/-- Let $A_{11}, L_{11}, D_1, R_{11} \in R^{m \times m}$, $A_{12} \in R^{m \times n}$,
$A_{21} \in R^{n \times m}$ and $A_{22} \in R^{n \times n}$, with $D_1$ invertible and
$A_{11} = L_{11} D_1 R_{11}$. Then the Schur complement of $A_{11}$ in $\begin{bmatrix} A_{11} &
A_{12} \\ A_{21} & A_{22} \end{bmatrix}$ is
$$\Delta_2 = A_{22} - L_{21} D_1 R_{12}, \qquad
  L_{21} = A_{21} R_{11}^{-1} D_1^{-1}, \qquad R_{12} = D_1^{-1} L_{11}^{-1} A_{12}.$$
This is the Schur complement of [quarteroni2000numerical] §3.8.1.

Only $D_1$ needs to be nonsingular for this identity. If $L_{11}$ or $R_{11}$ is singular, then
so is $A_{11}$, and both sides are $A_{22}$, because `Matrix.inv` gives $0$ for a singular
matrix. -/
theorem schurComplement_fromBlocks_of_mul_eq (hD : IsUnit D₁) (h : A₁₁ = L₁₁ * D₁ * R₁₁) :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).schurComplement
      = A₂₂ - (A₂₁ * R₁₁⁻¹ * D₁⁻¹) * D₁ * (D₁⁻¹ * L₁₁⁻¹ * A₁₂) := by
  rw [schurComplement_fromBlocks, h, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc D₁⁻¹ D₁, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hD),
    Matrix.one_mul]

/-- The **block LDU factorization**. Let $A_{11} = L_{11} D_1 R_{11}$ with
$L_{11}, D_1, R_{11} \in R^{m \times m}$ invertible, let $A_{12} \in R^{m \times n}$,
$A_{21} \in R^{n \times m}$ and $A_{22} \in R^{n \times n}$, and let $\Delta_2$ be the Schur
complement of $A_{11}$. Then
$$\begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix}
  = \begin{bmatrix} L_{11} & 0 \\ L_{21} & I \end{bmatrix}
  \begin{bmatrix} D_1 & 0 \\ 0 & \Delta_2 \end{bmatrix}
  \begin{bmatrix} R_{11} & R_{12} \\ 0 & I \end{bmatrix}$$
with $L_{21} = A_{21} R_{11}^{-1} D_1^{-1}$ and $R_{12} = D_1^{-1} L_{11}^{-1} A_{12}$. This is
the factorization of [quarteroni2000numerical] §3.8.1.

`Matrix.schurComplement_fromBlocks_of_mul_eq` writes $\Delta_2$ as $A_{22} - L_{21} D_1 R_{12}$. -/
theorem fromBlocks_eq_mul_fromBlocks_of_mul_eq (hL : IsUnit L₁₁) (hD : IsUnit D₁) (hR : IsUnit R₁₁)
    (h : A₁₁ = L₁₁ * D₁ * R₁₁) :
    fromBlocks A₁₁ A₁₂ A₂₁ A₂₂
      = fromBlocks L₁₁ 0 (A₂₁ * R₁₁⁻¹ * D₁⁻¹) 1
        * fromBlocks D₁ 0 0 (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).schurComplement
        * fromBlocks R₁₁ (D₁⁻¹ * L₁₁⁻¹ * A₁₂) 0 1 := by
  have hLL : L₁₁ * L₁₁⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hL)
  have hDD : D₁ * D₁⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hD)
  have hRR : R₁₁⁻¹ * R₁₁ = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hR)
  have hDD' : D₁⁻¹ * D₁ = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hD)
  rw [schurComplement_fromBlocks_of_mul_eq hD h, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul]
  congr 1
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D₁ D₁⁻¹, hDD, Matrix.one_mul, ← Matrix.mul_assoc L₁₁ L₁₁⁻¹, hLL,
      Matrix.one_mul]
  · rw [Matrix.mul_assoc (A₂₁ * R₁₁⁻¹) D₁⁻¹ D₁, hDD', Matrix.mul_one, Matrix.mul_assoc, hRR,
      Matrix.mul_one]
  · rw [add_sub_cancel]

end BlockLDU

section Loewner

/-- Let $A$ be a Hermitian matrix indexed by $m \oplus n$ over a type with a star operation. Then
the off-diagonal blocks are conjugate transposes of each other: $A_{12} = A_{21}^H$. -/
theorem IsHermitian.toBlocks₁₂_eq_conjTranspose {α : Type*} [Star α]
    {A : Matrix (m ⊕ n) (m ⊕ n) α} (hA : A.IsHermitian) : A.toBlocks₁₂ = A.toBlocks₂₁ᴴ := by
  ext i j
  rw [toBlocks₁₂, conjTranspose_apply, toBlocks₂₁, of_apply, of_apply, ← hA.apply]

variable {K : Type*} [Field K] [PartialOrder K] [StarRing K] [Fintype m] [DecidableEq m]
  [Finite n]

/-- **The Schur complement lies below the $(2,2)$ block in the Loewner order.** Let $K$ be a field
with a partial order and a star operation, let $m$ and $n$ be finite, and let $A$ be a Hermitian
positive definite matrix over $K$ indexed by $m \oplus n$, with Schur complement $S$ of
$A_{11}$. Then $A_{22} - S$ is positive semidefinite, that is, $S \le A_{22}$ in the Loewner
order.

The difference is $A_{22} - S = A_{21} A_{11}^{-1} A_{12} = A_{21} A_{11}^{-1} A_{21}^H$. The
Loewner order $X \le Y \iff Y - X$ positive semidefinite is in `Mathlib.Analysis.Matrix.Order`
(scoped `MatrixOrder`, over `RCLike`, where `Matrix.le_iff` is `Iff.rfl`). The statement here is
over any field with a partial order and a star operation, without that order, as the positive
semidefiniteness of the difference. -/
theorem PosDef.schurComplement_loewner_le {A : Matrix (m ⊕ n) (m ⊕ n) K} (hA : A.PosDef) :
    (A.toBlocks₂₂ - A.schurComplement).PosSemidef := by
  have h11 : A.toBlocks₁₁.PosDef := Matrix.PosDef.submatrix hA Sum.inl_injective
  rw [schurComplement_eq, sub_sub_cancel, hA.1.toBlocks₁₂_eq_conjTranspose]
  exact (Matrix.PosDef.inv h11).posSemidef.mul_mul_conjTranspose_same _

end Loewner

section L2Order

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The spectral norm is monotone on positive semidefinite matrices.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, and let $X, Y \in \mathbb{K}^{n \times n}$. If $X$ and $Y - X$ are
positive semidefinite, that is, $0 \le X \le Y$ in the Loewner order, then
$$\|X\|_2 \le \|Y\|_2,$$
where $\|\cdot\|_2$ is the operator norm induced by the Euclidean norm.

Here $\mathbb{K}$ is an `RCLike` field, and the norm is the scoped instance
`Matrix.Norms.L2Operator`. The norm of a Hermitian matrix is the supremum of its Rayleigh
quotient, and the Rayleigh quotients of $X$ lie between $0$ and those of $Y$. -/
theorem l2_opNorm_le_of_posSemidef_of_posSemidef_sub {X Y : Matrix n n 𝕜} (hX : X.PosSemidef)
    (hXY : (Y - X).PosSemidef) : ‖X‖ ≤ ‖Y‖ := by
  rw [l2_opNorm_def, l2_opNorm_def]
  obtain ⟨TX, hTX⟩ : ∃ TX : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n,
    TX = (toEuclideanLin.trans LinearMap.toContinuousLinearMap) X := ⟨_, rfl⟩
  obtain ⟨TY, hTY⟩ : ∃ TY : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n,
    TY = (toEuclideanLin.trans LinearMap.toContinuousLinearMap) Y := ⟨_, rfl⟩
  rw [← hTX, ← hTY]
  have hsym : (TX : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n).IsSymmetric := by
    rw [hTX, LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap]
    exact isSymmetric_toEuclideanLin_iff.mpr hX.1
  -- the Rayleigh quotients of `X` are nonnegative and below those of `Y`
  have hre : ∀ x : EuclideanSpace 𝕜 n, 0 ≤ RCLike.re (inner 𝕜 (TX x) x) ∧
      RCLike.re (inner 𝕜 (TX x) x) ≤ RCLike.re (inner 𝕜 (TY x) x) := by
    intro x
    have hinner : ∀ (M : Matrix n n 𝕜), RCLike.re (inner 𝕜
        ((toEuclideanLin.trans LinearMap.toContinuousLinearMap) M x) x)
          = RCLike.re (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)) := by
      intro M
      rw [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap',
        EuclideanSpace.inner_eq_star_dotProduct, ofLp_toLpLin, toLin'_apply, dotProduct_star,
        dotProduct_comm, RCLike.star_def, RCLike.conj_re]
    rw [hTX, hTY, hinner, hinner]
    refine ⟨hX.re_dotProduct_nonneg _, ?_⟩
    have h := hXY.re_dotProduct_nonneg (WithLp.ofLp x)
    rw [sub_mulVec, dotProduct_sub, map_sub] at h
    linarith
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient TX hsym]
  refine ciSup_le fun x => ?_
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    abs_of_nonneg (div_nonneg (hre x).1 (sq_nonneg _))]
  refine le_trans ?_ (le_trans (le_abs_self _) (TY.rayleighQuotient_le_norm x))
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  exact div_le_div_of_nonneg_right (hre x).2 (sq_nonneg _)

end L2Order

section CondNumber

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- **The Schur complement of a positive definite matrix is better conditioned than the matrix.**
Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $A$ be a Hermitian positive definite
matrix over $\mathbb{K}$ indexed by $m \oplus n$, and let $S$ be the Schur complement of
$A_{11}$. Then in the spectral norm
$$\|S\|_2 \, \|S^{-1}\|_2 \le \|A\|_2 \, \|A^{-1}\|_2.$$
This is Remark 3.6 of [quarteroni2000numerical], and Lemma 3.12 of Axelsson, *Iterative Solution
Methods*.

The norm is the scoped instance `Matrix.Norms.L2Operator`. The bound $0 \le S \le A_{22}$ in the
Loewner order gives $\|S\| \le \|A_{22}\| \le \|A\|$, since a principal submatrix has the
smaller norm (`Matrix.l2_opNorm_submatrix_le`), and $S^{-1} = (A^{-1})_{22}$ gives
$\|S^{-1}\| \le \|A^{-1}\|$ in the same way. -/
theorem PosDef.condNumber_schurComplement_le {A : Matrix (m ⊕ n) (m ⊕ n) 𝕜} (hA : A.PosDef) :
    ‖A.schurComplement‖ * ‖A.schurComplement⁻¹‖ ≤ ‖A‖ * ‖A⁻¹‖ := by
  have h11 : A.toBlocks₁₁.PosDef := hA.submatrix Sum.inl_injective
  have hS : ‖A.schurComplement‖ ≤ ‖A‖ :=
    (l2_opNorm_le_of_posSemidef_of_posSemidef_sub hA.schurComplement.posSemidef
      hA.schurComplement_loewner_le).trans
      (l2_opNorm_submatrix_le A Sum.inr_injective Sum.inr_injective)
  have hSinv : ‖A.schurComplement⁻¹‖ ≤ ‖A⁻¹‖ := by
    rw [← toBlocks₂₂_inv_eq_inv_schurComplement h11.isUnit hA.isUnit]
    exact l2_opNorm_submatrix_le A⁻¹ Sum.inr_injective Sum.inr_injective
  exact mul_le_mul hS hSinv (norm_nonneg _) (norm_nonneg _)

end CondNumber


/-! ### Saddle-point matrices -/

section Saddle

/-- Let $R$ have a star operation, and let $A \in R^{m \times m}$, $B \in R^{m \times n}$ and
$D \in R^{n \times n}$. The **saddle-point matrix** (equilibrium matrix, KKT matrix) is
$$\begin{bmatrix} A & B \\ B^H & D \end{bmatrix},$$
indexed by $m \oplus n$.

With $D = 0$ it is the equilibrium matrix $\begin{bmatrix} C & B \\ B^T & 0 \end{bmatrix}$ of
[golub2013matrix] §4.4.5, with $A$ in place of $C$. In [saad2003iterative] (8.30), $D = 0$ gives
the saddle-point matrix itself and $D = \rho C$ its regularization. -/
def saddleMatrix [Star R] (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    Matrix (m ⊕ n) (m ⊕ n) R :=
  fromBlocks A B Bᴴ D

/-- Let $R$ have an involutive star operation. The conjugate transpose of a saddle-point matrix is
the saddle-point matrix of the conjugate transposed diagonal blocks:
$$\begin{bmatrix} A & B \\ B^H & D \end{bmatrix}^H
  = \begin{bmatrix} A^H & B \\ B^H & D^H \end{bmatrix}.$$
-/
theorem saddleMatrix_conjTranspose [InvolutiveStar R] (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) : (saddleMatrix A B D)ᴴ = saddleMatrix Aᴴ B Dᴴ := by
  rw [saddleMatrix, saddleMatrix, fromBlocks_conjTranspose, conjTranspose_conjTranspose]

/-- Let $R$ have an involutive star operation. If $A \in R^{m \times m}$ and $D \in R^{n \times n}$
are Hermitian, then the saddle-point matrix $\begin{bmatrix} A & B \\ B^H & D \end{bmatrix}$ is
Hermitian for every $B \in R^{m \times n}$. -/
theorem IsHermitian.saddleMatrix [InvolutiveStar R] {A : Matrix m m R} {D : Matrix n n R}
    (hA : A.IsHermitian) (B : Matrix m n R) (hD : D.IsHermitian) :
    (saddleMatrix A B D).IsHermitian :=
  hA.fromBlocks rfl hD

/-- **The block equations of a saddle-point system.** Let $R$ be a semiring (not necessarily unital
or associative) with a star operation, let $m$ and $n$ be finite, and let
$A \in R^{m \times m}$, $B \in R^{m \times n}$, $D \in R^{n \times n}$, $x, b \in R^m$ and
$y, c \in R^n$. Then
$$\begin{bmatrix} A & B \\ B^H & D \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix}
  = \begin{bmatrix} b \\ c \end{bmatrix}$$
if and only if $Ax + By = b$ and $B^H x + D y = c$.

The stacked vectors are `Sum.elim x y` and `Sum.elim b c`. -/
theorem saddleMatrix_mulVec_elim [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring R] [Star R]
    (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) (x b : m → R) (y c : n → R) :
    saddleMatrix A B D *ᵥ Sum.elim x y = Sum.elim b c ↔
      A *ᵥ x + B *ᵥ y = b ∧ Bᴴ *ᵥ x + D *ᵥ y = c := by
  rw [saddleMatrix, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_eq_iff]

/-- **The triangular factorization of an equilibrium matrix.** Let $R$ be a ring with a star
operation, and let $A, G \in R^{m \times m}$, $B, K \in R^{m \times n}$ and
$H \in R^{n \times n}$ satisfy $A = G G^H$, $G K = B$ and $H H^H = K^H K$. Then
$$\begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix}
  = \begin{bmatrix} G & 0 \\ K^H & H \end{bmatrix}
  \begin{bmatrix} G^H & K \\ 0 & -H^H \end{bmatrix}.$$
This is the factorization of [golub2013matrix] §4.4.5.

In the source, $A = G G^H$ is a Cholesky factorization, and $H H^H = K^H K = B^H A^{-1} B$ is a
Cholesky factorization of the Schur complement. The identity needs no definiteness. -/
theorem saddleMatrix_zero_eq_mul [Fintype m] [Fintype n] [Ring R] [StarRing R]
    {A G : Matrix m m R} {B K : Matrix m n R} {H : Matrix n n R} (hA : A = G * Gᴴ)
    (hK : G * K = B) (hH : H * Hᴴ = Kᴴ * K) :
    saddleMatrix A B 0 = fromBlocks G 0 Kᴴ H * fromBlocks Gᴴ K 0 (-Hᴴ) := by
  rw [fromBlocks_multiply, saddleMatrix, ← hK, conjTranspose_mul, hA]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, Matrix.mul_neg, neg_zero, hH,
    add_neg_cancel]

variable {K : Type*} [Field K] [PartialOrder K] [StarRing K]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- **The Schur complement of a saddle-point matrix is definite.** Let $K$ be a field with a partial
order and a star operation, let $A \in K^{m \times m}$ be Hermitian positive definite, and let
$B \in K^{m \times n}$ have full column rank. Then $B^H A^{-1} B$ is Hermitian positive
definite. This is Corollary 8.1 of [saad2003iterative].

Full column rank is the injectivity of $x \mapsto Bx$, `Function.Injective B.mulVec`. The Schur
complement of $A$ in $\begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix}$ is $-B^H A^{-1} B$
(`Matrix.schurComplement_fromBlocks`). -/
theorem PosDef.conjTranspose_mul_inv_mul {A : Matrix m m K} {B : Matrix m n K} (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) : (Bᴴ * A⁻¹ * B).PosDef :=
  hA.inv.conjTranspose_mul_mul_same hB

/-- **The equilibrium matrix is nonsingular.** Let $K$ be a field with a partial order and a star
operation, let $A \in K^{m \times m}$ be Hermitian positive definite, and let
$B \in K^{m \times n}$ have full column rank. Then the matrix
$\begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix}$ is nonsingular. This is (4.4.18) of
[golub2013matrix].

Its Schur complement $-B^H A^{-1} B$ is negative definite, hence nonsingular. Full column rank
is `Function.Injective B.mulVec`. -/
theorem isUnit_saddleMatrix_zero {A : Matrix m m K} {B : Matrix m n K} (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) : IsUnit (saddleMatrix A B 0) := by
  refine isUnit_of_isUnit_schurComplement (by simpa [saddleMatrix] using hA.isUnit) ?_
  rw [saddleMatrix, schurComplement_fromBlocks, zero_sub, Matrix.mul_assoc Bᴴ, ← Matrix.mul_assoc]
  exact (hA.conjTranspose_mul_inv_mul hB).isUnit.neg

/-- **The reduced equation of an equilibrium system.** Let $K$ be a field with a partial order and a
star operation, let $A \in K^{m \times m}$ be Hermitian positive definite, and let
$B \in K^{m \times n}$ have full column rank. If $x, f \in K^m$ and $y \in K^n$ satisfy
$$\begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix}
  = \begin{bmatrix} f \\ 0 \end{bmatrix},$$
then
$$y = (B^H A^{-1} B)^{-1} B^H A^{-1} f.$$
This is (4.4.20) of [golub2013matrix].

The proof eliminates $x = A^{-1} (f - By)$. Full column rank is `Function.Injective B.mulVec`. -/
theorem saddleMatrix_zero_mulVec_snd_eq {A : Matrix m m K} {B : Matrix m n K} (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) {x f : m → K} {y : n → K}
    (h : saddleMatrix A B 0 *ᵥ Sum.elim x y = Sum.elim f 0) :
    y = (Bᴴ * A⁻¹ * B)⁻¹ *ᵥ ((Bᴴ * A⁻¹) *ᵥ f) := by
  obtain ⟨h₁, h₂⟩ := (saddleMatrix_mulVec_elim A B 0 x f y 0).1 h
  rw [zero_mulVec, add_zero] at h₂
  have hx : x = A⁻¹ *ᵥ (f - B *ᵥ y) := by
    rw [← h₁, add_sub_cancel_right, mulVec_mulVec,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hA.isUnit), one_mulVec]
  rw [hx, mulVec_mulVec, mulVec_sub, mulVec_mulVec, sub_eq_zero] at h₂
  rw [h₂, mulVec_mulVec, nonsing_inv_mul _
    ((isUnit_iff_isUnit_det _).1 (hA.conjTranspose_mul_inv_mul hB).isUnit), one_mulVec]

end Saddle

end Matrix
