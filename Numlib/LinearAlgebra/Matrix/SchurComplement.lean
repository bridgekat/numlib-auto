/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.SchurComplement`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
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
* `Matrix.schurComplement_fromBlocks_blockDiagonal'`: the Schur complement is *additive over the
  subdomains*, `S = ∑ S_i`, when the interior block is block diagonal and the interface block is a
  sum of local contributions. This is what every preconditioner assembled from local Schur
  complements rests on, and `Matrix.inv_blockDiagonal'` and `Matrix.mul_blockDiagonal'_mul` are the
  two block-diagonal identities it is built from.

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

end Matrix
