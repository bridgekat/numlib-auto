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

/-!
# The Schur complement of a block matrix

For `A : Matrix (m ⊕ n) (m ⊕ n) R`, the *Schur complement* of the `(1,1)` block is

`A.schurComplement = A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₁⁻¹ * A.toBlocks₁₂`,

written `S = C - F B⁻¹ E` in the notation of [saad2003iterative] (14.5). Mathlib's
`Mathlib.LinearAlgebra.Matrix.SchurComplement` carries the block LDU identity, the determinant
formulas and the positive *semi*definite criterion, but names no Schur complement and proves nothing
about its inverse. This file adds the name and the facts a domain-decomposition method needs:

* the block LU and LDU factorizations `Matrix.fromBlocks_eq_mul_schurComplement` and
  `Matrix.fromBlocks_eq_mul_fromBlocks_schurComplement`;
* `Matrix.isUnit_schurComplement_iff`: with an invertible `(1,1)` block, the whole matrix is
  nonsingular exactly when its Schur complement is;
* `Matrix.inv_fromBlocks_eq`, the block inverse, and `Matrix.toBlocks₂₂_inv_eq_inv_schurComplement`:
  the `(2,2)` block of `A⁻¹` is `S⁻¹`, which is what lets a preconditioner for the interface system
  be built out of a solver for `A`;
* `Matrix.PosDef.schurComplement`: the Schur complement of a positive definite matrix is positive
  definite. Mathlib has only the positive semidefinite equivalence `Matrix.PosDef.fromBlocks₁₁`;
* `Matrix.PosDef.schurComplement_loewner_le`: it lies below the `(2,2)` block in the Loewner
  order, `A₂₂ - S` being positive semidefinite;
* `Matrix.PosDef.condNumber_schurComplement_le`: in the spectral norm it is better conditioned
  than the matrix, `‖S‖ ‖S⁻¹‖ ≤ ‖A‖ ‖A⁻¹‖` ([quarteroni2000numerical] Remark 3.6), by way of two
  general facts about the `ℓ²` operator norm: it is monotone on positive semidefinite matrices
  (`Matrix.l2_opNorm_le_of_posSemidef_of_posSemidef_sub`) and decreases on passing to a
  submatrix (`Matrix.l2_opNorm_submatrix_le`);
* `Matrix.fromBlocks_eq_mul_fromBlocks_of_mul_eq`: the block LDU factorization of
  [quarteroni2000numerical] §3.8.1, built from a factorization `A₁₁ = L₁₁ D₁ R₁₁` of the leading
  block;
* `Matrix.schurComplement_fromBlocks_blockDiagonal'`: the Schur complement is *additive over the
  subdomains*, `S = ∑ S_i`, when the interior block is block diagonal and the interface block is a
  sum of local contributions. This is what every preconditioner assembled from local Schur
  complements rests on, and `Matrix.inv_blockDiagonal'` and `Matrix.mul_blockDiagonal'_mul` are the
  two block-diagonal identities it is built from; `Matrix.isUnit_blockDiagonal'` is the
  nonsingularity criterion that goes with them, a block diagonal matrix being nonsingular exactly
  when each of its blocks is.

`Matrix.schurComplementSingle` is the `1 × 1`-pivot case, one step of Gaussian elimination, which is
the form incomplete factorizations use ([saad2003iterative] Theorem 10.1).

## Implementation notes

The hypotheses are `IsUnit`, not `Invertible`, because that is the form a nonsingularity hypothesis
takes downstream; each proof turns them into `Invertible` instances internally and
`Matrix.invOf_eq_nonsing_inv` reconciles `⅟` with `⁻¹`.

Indexing is by a sum type `m ⊕ n` throughout, so that `Matrix.toBlocks₁₁ … Matrix.toBlocks₂₂` apply
and no reindexing equivalence appears in the statements.

## TODO

Connect `Matrix.schurComplementSingle` to `Matrix.schurComplement`, by the identity
`A.schurComplementSingle p = (A.submatrix e e).schurComplement` for `e = Equiv.sumCompl (· = p) : {i
// i = p} ⊕ {i // i ≠ p} ≃ n`. It needs the inverse of the `1 × 1` block, which is
`Matrix.adjugate_subsingleton` (the adjugate of a subsingleton-indexed matrix is `1`) together with
`Matrix.det_unique`, and then the collapse of a sum over a `Unique` index type.
-/

open Function
open scoped ComplexOrder

namespace Matrix

variable {m n R : Type*}

section Def

variable [Fintype m] [DecidableEq m] [CommRing R]

/-- The **Schur complement** of the `(1,1)` block of a `2 × 2` block matrix, `S = C - F B⁻¹ E` in
the notation of [saad2003iterative], (14.5).

It is `noncomputable` because `Matrix.inv` is, and it is junk when the `(1,1)` block is singular,
`Matrix.inv` being junk there. -/
noncomputable def schurComplement (A : Matrix (m ⊕ n) (m ⊕ n) R) : Matrix n n R :=
  A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₁⁻¹ * A.toBlocks₁₂

/-- The Schur complement, unfolded. -/
theorem schurComplement_eq (A : Matrix (m ⊕ n) (m ⊕ n) R) :
    A.schurComplement = A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₁⁻¹ * A.toBlocks₁₂ := rfl

/-- The Schur complement in terms of the four blocks: the simp-normal form. -/
@[simp]
theorem schurComplement_fromBlocks (B : Matrix m m R) (E : Matrix m n R) (F : Matrix n m R)
    (C : Matrix n n R) : (fromBlocks B E F C).schurComplement = C - F * B⁻¹ * E := rfl

end Def

section Factorization

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
variable {B : Matrix m m R} {E : Matrix m n R} {F : Matrix n m R} {C : Matrix n n R}

/-- **The block LU factorization** of a block matrix with a nonsingular `(1,1)` block
([saad2003iterative], (14.6)): the second factor is block upper triangular with the Schur complement
in its `(2,2)` corner. -/
theorem fromBlocks_eq_mul_fromBlocks_schurComplement (hB : IsUnit B) :
    fromBlocks B E F C
      = fromBlocks 1 0 (F * B⁻¹) 1 * fromBlocks B E 0 (fromBlocks B E F C).schurComplement := by
  have hinv : B⁻¹ * B = 1 := nonsing_inv_mul B ((isUnit_iff_isUnit_det B).1 hB)
  simp only [schurComplement_fromBlocks, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_assoc, hinv, add_sub_cancel]

/-- **The block LDU factorization** of a block matrix with a nonsingular `(1,1)` block
([saad2003iterative], (14.52)): the middle factor is `1 ⊕ S`, and the two outer factors are
unipotent block triangular. -/
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

/-- **[saad2003iterative] Proposition 14.1 (1)**: with a nonsingular `(1,1)` block, a block matrix
is nonsingular exactly when its Schur complement is. -/
theorem isUnit_schurComplement_iff {A : Matrix (m ⊕ n) (m ⊕ n) R} (hB : IsUnit A.toBlocks₁₁) :
    IsUnit A.schurComplement ↔ IsUnit A := by
  let _ := hB.invertible
  have h1 : A.toBlocks₁₁⁻¹ = ⅟A.toBlocks₁₁ := (invOf_eq_nonsing_inv _).symm
  rw [schurComplement_eq, h1, ← isUnit_fromBlocks_iff_of_invertible₁₁, fromBlocks_toBlocks]

/-- The Schur complement of a nonsingular block matrix with a nonsingular `(1,1)` block is
nonsingular ([saad2003iterative], Proposition 14.1 (1)). -/
theorem isUnit_schurComplement {A : Matrix (m ⊕ n) (m ⊕ n) R} (hB : IsUnit A.toBlocks₁₁)
    (hA : IsUnit A) : IsUnit A.schurComplement :=
  (isUnit_schurComplement_iff hB).2 hA

/-- The converse of `Matrix.isUnit_schurComplement`. -/
theorem isUnit_of_isUnit_schurComplement {A : Matrix (m ⊕ n) (m ⊕ n) R}
    (hB : IsUnit A.toBlocks₁₁) (hS : IsUnit A.schurComplement) : IsUnit A :=
  (isUnit_schurComplement_iff hB).1 hS

end IsUnit

section Inverse

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
variable {B : Matrix m m R} {E : Matrix m n R} {F : Matrix n m R} {C : Matrix n n R}

/-- **The block inverse** of a nonsingular block matrix with a nonsingular `(1,1)` block
([saad2003iterative], (14.7)), with `S = C - F B⁻¹ E` the Schur complement in the `(2,2)` corner. -/
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

/-- **[saad2003iterative] Proposition 14.1 (3)**: the `(2,2)` block of the inverse of a block matrix
is the inverse of its Schur complement. This is the identity that lets a preconditioner for the
interface system `S y = g` be built out of a solver for the whole matrix. -/
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

/-- A block diagonal matrix is nonsingular as soon as every one of its blocks is. -/
theorem isUnit_blockDiagonal' (M : ∀ i, Matrix (m' i) (m' i) R) (hM : ∀ i, IsUnit (M i)) :
    IsUnit (blockDiagonal' M) := by
  refine IsUnit.of_mul_eq_one (blockDiagonal' fun i => (M i)⁻¹) ?_
  rw [← blockDiagonal'_mul]
  have h : (fun i => M i * (M i)⁻¹) = (1 : ∀ i, Matrix (m' i) (m' i) R) := funext fun i => by
    rw [Pi.one_apply]
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (hM i))
  rw [h, blockDiagonal'_one]

/-- The inverse of a block diagonal matrix is the block diagonal matrix of the inverses. -/
theorem inv_blockDiagonal' (M : ∀ i, Matrix (m' i) (m' i) R) (hM : ∀ i, IsUnit (M i)) :
    (blockDiagonal' M)⁻¹ = blockDiagonal' fun i => (M i)⁻¹ := by
  refine inv_eq_right_inv ?_
  have h : (fun i => M i * (M i)⁻¹) = (1 : ∀ i, Matrix (m' i) (m' i) R) := funext fun i => by
    rw [Pi.one_apply]
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (hM i))
  rw [← blockDiagonal'_mul, h, blockDiagonal'_one]

omit [∀ i, DecidableEq (m' i)] in
/-- A product `F D E` whose middle factor is block diagonal is the sum, over the blocks, of the
products of the corresponding blocks of `F`, `D` and `E`. -/
theorem mul_blockDiagonal'_mul {n : Type*} (F : Matrix n (Σ i, m' i) R)
    (M : ∀ i, Matrix (m' i) (m' i) R) (E : Matrix (Σ i, m' i) n R) :
    F * blockDiagonal' M * E
      = ∑ i, F.submatrix id (Sigma.mk i) * M i * E.submatrix (Sigma.mk i) id := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [mul_apply, submatrix_apply, id_eq, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  refine congrArg₂ _ ?_ rfl
  refine (Fintype.sum_eq_single i fun j hj => Finset.sum_eq_zero fun k _ => ?_).trans
    (Finset.sum_congr rfl fun k _ => ?_)
  · rw [blockDiagonal'_apply_ne _ _ _ hj, mul_zero]
  · rw [blockDiagonal'_apply_eq]

/-- **The Schur complement is additive over the subdomains**: if the interior block is block
diagonal, `B = diag(B_1, …, B_s)`, and the interface block is a sum `C = ∑ C_i` of local
contributions, then the Schur complement is the sum of the local Schur complements,
`S = ∑ (C_i - F_i B_i⁻¹ E_i)`.  This is [saad2003iterative], (14.16); the derivation there is
finite-element, but the identity is block algebra and holds for any such decomposition. -/
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
/-- **[saad2003iterative] Proposition 14.1 (2)**: the Schur complement of a Hermitian positive
definite matrix is Hermitian positive definite.

Mathlib's `Matrix.PosDef.fromBlocks₁₁` gives only the positive *semi*definite equivalence; the
strict form comes from `Matrix.toBlocks₂₂_inv_eq_inv_schurComplement`, since `A⁻¹` is positive
definite, a principal submatrix of a positive definite matrix is positive definite, and the inverse
of a positive definite matrix is positive definite. -/
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

/-- **One step of Gaussian elimination**, the `1 × 1`-pivot Schur complement: for a pivot index `p`,
the matrix `A i j - A i p (A p p)⁻¹ A p j` on the indices other than `p`. It is the trailing block
of the matrix `A₁` of [saad2003iterative], Theorem 10.1 — his `A₁` is square on all `n` indices,
keeping the pivot row and a zeroed pivot column — and it is the matrix whose incomplete
factorizations the theory of Chapter 10 studies. -/
noncomputable def schurComplementSingle (A : Matrix n n K) (p : n) :
    Matrix {i : n // i ≠ p} {i : n // i ≠ p} K :=
  Matrix.of fun i j => A i.1 j.1 - A i.1 p * (A p p)⁻¹ * A p j.1

@[simp]
theorem schurComplementSingle_apply (A : Matrix n n K) (p : n) (i j : {i : n // i ≠ p}) :
    A.schurComplementSingle p i j = A i.1 j.1 - A i.1 p * (A p p)⁻¹ * A p j.1 := rfl

end Single

section BlockLDU

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
variable {A₁₁ L₁₁ D₁ R₁₁ : Matrix m m R} {A₁₂ : Matrix m n R} {A₂₁ : Matrix n m R}
  {A₂₂ : Matrix n n R}

omit [Fintype n] [DecidableEq n] in
/-- The Schur complement written with the factors of `A₁₁ = L₁₁ D₁ R₁₁`: `Δ₂ = A₂₂ - L₂₁ D₁ R₁₂`
with `L₂₁ = A₂₁ R₁₁⁻¹ D₁⁻¹` and `R₁₂ = D₁⁻¹ L₁₁⁻¹ A₁₂` ([quarteroni2000numerical] §3.8.1); only
`D₁` needs to be nonsingular for this identity. -/
theorem schurComplement_fromBlocks_of_mul_eq (hD : IsUnit D₁) (h : A₁₁ = L₁₁ * D₁ * R₁₁) :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).schurComplement
      = A₂₂ - (A₂₁ * R₁₁⁻¹ * D₁⁻¹) * D₁ * (D₁⁻¹ * L₁₁⁻¹ * A₁₂) := by
  rw [schurComplement_fromBlocks, h, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc D₁⁻¹ D₁, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hD),
    Matrix.one_mul]

/-- **The block LDU factorization** ([quarteroni2000numerical] §3.8.1): if the leading block
factors as `A₁₁ = L₁₁ D₁ R₁₁` with nonsingular factors, then
`[A₁₁ A₁₂; A₂₁ A₂₂] = [L₁₁ 0; L₂₁ I] [D₁ 0; 0 Δ₂] [R₁₁ R₁₂; 0 I]` with `L₂₁ = A₂₁ R₁₁⁻¹ D₁⁻¹`,
`R₁₂ = D₁⁻¹ L₁₁⁻¹ A₁₂` and `Δ₂` the Schur complement of `A₁₁`
(`Matrix.schurComplement_fromBlocks_of_mul_eq` writes it as `A₂₂ - L₂₁ D₁ R₁₂`). -/
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

/-- The off-diagonal blocks of a Hermitian matrix are conjugate transposes of each other. -/
theorem IsHermitian.toBlocks₁₂_eq_conjTranspose {α : Type*} [Star α]
    {A : Matrix (m ⊕ n) (m ⊕ n) α} (hA : A.IsHermitian) : A.toBlocks₁₂ = A.toBlocks₂₁ᴴ := by
  ext i j
  rw [toBlocks₁₂, conjTranspose_apply, toBlocks₂₁, of_apply, of_apply, ← hA.apply]

variable {K : Type*} [Field K] [PartialOrder K] [StarRing K] [Fintype m] [DecidableEq m]
  [Finite n]

/-- **The Schur complement lies below the `(2,2)` block in the Loewner order**: for `A` positive
definite, `A₂₂ - S = A₂₁ A₁₁⁻¹ A₁₂ = A₂₁ A₁₁⁻¹ A₂₁ᴴ` is positive semidefinite, which is exactly
`S ≤ A₂₂` for the order `X ≤ Y ↔ (Y - X).PosSemidef` of `Mathlib.Analysis.Matrix.Order` (scoped
`MatrixOrder`, over `RCLike`; `Matrix.le_iff` is `Iff.rfl`). Stated over any ordered star field,
without that order, as the positive semidefiniteness of the difference. -/
theorem PosDef.schurComplement_loewner_le {A : Matrix (m ⊕ n) (m ⊕ n) K} (hA : A.PosDef) :
    (A.toBlocks₂₂ - A.schurComplement).PosSemidef := by
  have h11 : A.toBlocks₁₁.PosDef := Matrix.PosDef.submatrix hA Sum.inl_injective
  rw [schurComplement_eq, sub_sub_cancel, hA.1.toBlocks₁₂_eq_conjTranspose]
  exact (Matrix.PosDef.inv h11).posSemidef.mul_mul_conjTranspose_same _

end Loewner

section L2Order

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `ℓ²` norm of a subfamily of the coordinates of a vector is at most the norm of the
vector. -/
theorem _root_.EuclideanSpace.norm_toLp_comp_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : ι → κ} (hf : Injective f) (y : κ → 𝕜) :
    ‖(WithLp.toLp 2 (y ∘ f) : EuclideanSpace 𝕜 ι)‖ ≤ ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 κ)‖ := by
  classical
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  change ∑ i, ‖y (f i)‖ ^ 2 ≤ ∑ k, ‖y k‖ ^ 2
  rw [← Finset.sum_image (f := fun k => ‖y k‖ ^ 2) hf.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => by positivity

/-- Extending a vector by zero along an injection preserves the `ℓ²` norm. -/
theorem _root_.EuclideanSpace.norm_toLp_extend {ι κ : Type*} [Fintype ι] [Fintype κ]
    {g : ι → κ} (hg : Injective g) (x : ι → 𝕜) :
    ‖(WithLp.toLp 2 (extend g x 0) : EuclideanSpace 𝕜 κ)‖
      = ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 ι)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine (Fintype.sum_of_injective g hg (fun i => ‖x i‖ ^ 2) (fun k => ‖extend g x 0 k‖ ^ 2)
    (fun k hk => ?_) fun i => ?_).symm
  · rw [extend_apply' _ _ _ (by simpa using hk)]
    simp
  · rw [hg.extend_apply]

/-- `Matrix.l2_opNorm_mulVec` in the `WithLp.toLp` form. -/
theorem l2_opNorm_toLp_mulVec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (v : n → 𝕜) :
    ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace 𝕜 m)‖
      ≤ ‖A‖ * ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ :=
  l2_opNorm_mulVec A (WithLp.toLp 2 v)

/-- **A submatrix has a smaller `ℓ²` operator norm**, for injective row and column selections:
`‖A.submatrix f g‖₂ ≤ ‖A‖₂`. Apply `A` to the vector extended by zero and drop coordinates. -/
theorem l2_opNorm_submatrix_le {m n m' n' : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Fintype m'] [Fintype n'] [DecidableEq n'] (A : Matrix m n 𝕜) {f : m' → m} (hf : Injective f)
    {g : n' → n} (hg : Injective g) : ‖A.submatrix f g‖ ≤ ‖A‖ := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have hx : (A.submatrix f g) *ᵥ WithLp.ofLp x = (A *ᵥ extend g (WithLp.ofLp x) 0) ∘ f := by
    funext i
    simp only [mulVec, dotProduct, submatrix_apply]
    exact Fintype.sum_of_injective g hg _ _ (fun k hk => by
      rw [extend_apply' _ _ _ (by simpa using hk), Pi.zero_apply, mul_zero]) fun j => by
      rw [hg.extend_apply]
  have key : ‖(WithLp.toLp 2 ((A.submatrix f g) *ᵥ WithLp.ofLp x) : EuclideanSpace 𝕜 m')‖
      ≤ ‖A‖ * ‖x‖ := by
    rw [hx]
    calc ‖(WithLp.toLp 2 ((A *ᵥ extend g (WithLp.ofLp x) 0) ∘ f) : EuclideanSpace 𝕜 m')‖
        ≤ ‖(WithLp.toLp 2 (A *ᵥ extend g (WithLp.ofLp x) 0) : EuclideanSpace 𝕜 m)‖ :=
          EuclideanSpace.norm_toLp_comp_le hf _
      _ ≤ ‖A‖ * ‖(WithLp.toLp 2 (extend g (WithLp.ofLp x) 0) : EuclideanSpace 𝕜 n)‖ :=
          l2_opNorm_toLp_mulVec A _
      _ = ‖A‖ * ‖x‖ := by rw [EuclideanSpace.norm_toLp_extend hg]
  exact key

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The `ℓ²` operator norm is monotone on positive semidefinite matrices**: if `0 ≤ X ≤ Y` in the
Loewner order — `X` and `Y - X` positive semidefinite — then `‖X‖₂ ≤ ‖Y‖₂`. The norm of a
Hermitian matrix is the supremum of its Rayleigh quotient, and the Rayleigh quotients of `X` lie
between `0` and those of `Y`. -/
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

/-- **The Schur complement of a positive definite matrix is better conditioned than the matrix**
([quarteroni2000numerical] Remark 3.6; Axelsson, *Iterative Solution Methods*, Lemma 3.12): in the
spectral norm, `‖S‖₂ ‖S⁻¹‖₂ ≤ ‖A‖₂ ‖A⁻¹‖₂` for `S = A.schurComplement`. Indeed `0 ≤ S ≤ A₂₂` in the
Loewner order gives `‖S‖ ≤ ‖A₂₂‖ ≤ ‖A‖`, a principal submatrix having the smaller norm, and
`S⁻¹ = (A⁻¹)₂₂` gives `‖S⁻¹‖ ≤ ‖A⁻¹‖` for the same reason. -/
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

end Matrix
