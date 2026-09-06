import Mathlib.LinearAlgebra.Matrix.Block
import Numlib.LinearSolve.Stationary.Splitting

/-!
# Block splittings and block relaxation

The block form of the classical iterations ([Saad][saad2003iterative] §4.1.1, (4.15)–(4.17),
Algorithms 4.1–4.2 in the non-overlapping case). The block structure is a *labelling*
`π : n → ι` of the index set by a linearly ordered type of block labels, and the block-diagonal,
strict block-lower and strict block-upper parts of `A` are the entries with `π i = π j`,
`π j < π i` and `π i < π j` respectively (`Matrix.blockDiagPart`, `Matrix.blockStrictLower`,
`Matrix.blockStrictUpper`). They add up to `A`
(`Matrix.blockDiagPart_add_blockStrictLower_add_blockStrictUpper`), which is Saad's
`A = D - E - F` of (4.15) with `E = -blockStrictLower π A` and `F = -blockStrictUpper π A`.

The point splittings of `Numlib/LinearSolve/Stationary/Splitting.lean` are the case `π = id`
(`Matrix.blockDiagPart_id`, `Matrix.blockStrictLower_id`, `Matrix.blockStrictUpper_id`), and the
block Jacobi, Gauss–Seidel and SOR splittings (Saad (4.16), Algorithms 4.1–4.2) are built here
exactly as the point ones are, under the invertibility of the block diagonal.

## Implementation notes

Invertibility of the block-lower factor `D - ω E` rests on `Matrix.BlockTriangular.det`, which
factors the determinant of a block triangular matrix as the product of the determinants of its
diagonal blocks over `Finset.univ.image π`: adding the strict block-lower part changes no diagonal
block, hence changes no determinant. So no finiteness of the label type `ι` is needed, only a
`LinearOrder` on it.

Overlapping blocks — Saad's general Algorithm 4.1, in which the index sets need not partition
`n` — are not formalized; the book proves no theorem about them.
-/

namespace Matrix

open Stationary

variable {n ι R : Type*}

/-! ### The three block parts of a matrix -/

section Parts

variable [Zero R]

/-- The **block diagonal part** of `A` for the block labelling `π`: the entries whose row and
column carry the same label, Saad's `D` of (4.15). -/
def blockDiagPart [DecidableEq ι] (π : n → ι) (A : Matrix n n R) : Matrix n n R :=
  Matrix.of fun i j => if π i = π j then A i j else 0

/-- Entries of the block diagonal part: those whose row and column carry the same label. -/
@[simp]
theorem blockDiagPart_apply [DecidableEq ι] (π : n → ι) (A : Matrix n n R) (i j : n) :
    blockDiagPart π A i j = if π i = π j then A i j else 0 := rfl

/-- The **strict block-lower part** of `A` for the block labelling `π`, Saad's `-E` of (4.15). -/
def blockStrictLower [LinearOrder ι] (π : n → ι) (A : Matrix n n R) : Matrix n n R :=
  Matrix.of fun i j => if π j < π i then A i j else 0

/-- Entries of the strict block-lower part: those whose column label is below the row label. -/
@[simp]
theorem blockStrictLower_apply [LinearOrder ι] (π : n → ι) (A : Matrix n n R) (i j : n) :
    blockStrictLower π A i j = if π j < π i then A i j else 0 := rfl

/-- The **strict block-upper part** of `A` for the block labelling `π`, Saad's `-F` of (4.15). -/
def blockStrictUpper [LinearOrder ι] (π : n → ι) (A : Matrix n n R) : Matrix n n R :=
  Matrix.of fun i j => if π i < π j then A i j else 0

/-- Entries of the strict block-upper part: those whose row label is below the column label. -/
@[simp]
theorem blockStrictUpper_apply [LinearOrder ι] (π : n → ι) (A : Matrix n n R) (i j : n) :
    blockStrictUpper π A i j = if π i < π j then A i j else 0 := rfl

end Parts

section Decomposition

variable [LinearOrder ι] [AddCommMonoid R] (π : n → ι) (A : Matrix n n R)

/-- **Saad (4.15)**: a matrix is the sum of its block-diagonal, strict block-lower and strict
block-upper parts, which in Saad's letters is `A = D - E - F`. -/
theorem blockDiagPart_add_blockStrictLower_add_blockStrictUpper :
    blockDiagPart π A + blockStrictLower π A + blockStrictUpper π A = A := by
  ext i j
  simp only [Matrix.add_apply, blockDiagPart_apply, blockStrictLower_apply,
    blockStrictUpper_apply]
  rcases lt_trichotomy (π i) (π j) with h | h | h
  · simp [h, h.ne, asymm h]
  · simp [h]
  · simp [h, h.ne', asymm h]

/-- With the identity labelling the block diagonal part is the diagonal part. -/
@[simp]
theorem blockDiagPart_id [DecidableEq n] (A : Matrix n n R) :
    blockDiagPart id A = diagPart A := by
  ext i j
  rw [blockDiagPart_apply, diagPart, Matrix.diagonal_apply]
  split <;> simp_all [Matrix.diag]

/-- With the identity labelling the strict block-lower part is the strictly lower part. -/
@[simp]
theorem blockStrictLower_id [LinearOrder n] (A : Matrix n n R) :
    blockStrictLower id A = strictLower A := rfl

/-- With the identity labelling the strict block-upper part is the strictly upper part. -/
@[simp]
theorem blockStrictUpper_id [LinearOrder n] (A : Matrix n n R) :
    blockStrictUpper id A = strictUpper A := rfl

end Decomposition

/-! ### The block splittings -/

section Splittings

variable {𝕜 : Type*} [Field 𝕜] [Fintype n] [DecidableEq n] [LinearOrder ι] {π : n → ι}
variable {A : Matrix n n 𝕜}

omit [Fintype n] [DecidableEq n] in
/-- A scaled block diagonal plus the strict block-lower part is block triangular for the reversed
labelling. -/
private theorem blockTriangular_smul_add_blockStrictLower (c : 𝕜) (A : Matrix n n 𝕜) :
    BlockTriangular (c • blockDiagPart π A + blockStrictLower π A) (OrderDual.toDual ∘ π) := by
  intro i j hij
  have h : π i < π j := hij
  simp [h.ne, asymm h]

/-- Adding the strict block-lower part changes no diagonal block, hence no determinant. -/
private theorem det_smul_add_blockStrictLower (c : 𝕜) (A : Matrix n n 𝕜) :
    (c • blockDiagPart π A + blockStrictLower π A).det = (c • blockDiagPart π A).det := by
  have hD : BlockTriangular (c • blockDiagPart π A) (OrderDual.toDual ∘ π) := by
    intro i j hij
    have h : π i < π j := hij
    simp [h.ne]
  rw [(blockTriangular_smul_add_blockStrictLower (π := π) c A).det, hD.det]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  ext i j
  have hij : π i.1 = π j.1 := i.2.trans j.2.symm
  change (c • blockDiagPart π A + blockStrictLower π A) i.1 j.1
    = (c • blockDiagPart π A) i.1 j.1
  simp [hij]

/-- **The block-lower factor of a block relaxation is invertible** as soon as the block diagonal
is: it is block triangular with the same diagonal blocks. This is what makes the block
Gauss–Seidel and block SOR splittings well defined. -/
theorem isUnit_smul_blockDiagPart_add_blockStrictLower {c : 𝕜} (hc : c ≠ 0)
    (h : IsUnit (blockDiagPart π A)) :
    IsUnit (c • blockDiagPart π A + blockStrictLower π A) := by
  rw [isUnit_iff_isUnit_det] at h ⊢
  rw [det_smul_add_blockStrictLower, det_smul, isUnit_iff_ne_zero] at *
  exact mul_ne_zero (pow_ne_zero _ hc) h

/-- `D - E`, the block-lower part of `A` in Saad's letters, is invertible as soon as the block
diagonal of `A` is. -/
theorem isUnit_blockDiagPart_add_blockStrictLower (h : IsUnit (blockDiagPart π A)) :
    IsUnit (blockDiagPart π A + blockStrictLower π A) := by
  simpa using isUnit_smul_blockDiagPart_add_blockStrictLower (c := (1 : 𝕜)) one_ne_zero h

/-- **Block Jacobi** (Saad, *Iterative Methods for Sparse Linear Systems*, (4.16)): `M = D`,
the block diagonal part. With `π = id` it is `Matrix.jacobiSplitting`. -/
noncomputable def blockJacobiSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) : Splitting A :=
  ⟨blockDiagPart π A, h⟩

/-- The complementary part of the block Jacobi splitting is `-(E + F)`. -/
theorem blockJacobiSplitting_n (π : n → ι) (A : Matrix n n 𝕜) (h : IsUnit (blockDiagPart π A)) :
    (blockJacobiSplitting π A h).n = -(blockStrictLower π A + blockStrictUpper π A) := by
  change blockDiagPart π A - A = -(blockStrictLower π A + blockStrictUpper π A)
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← add_assoc,
    blockDiagPart_add_blockStrictLower_add_blockStrictUpper, sub_self]

/-- **Block Gauss–Seidel** (Saad, *Iterative Methods for Sparse Linear Systems*, Algorithm 4.1):
`M = D - E`, the block-lower part. With `π = id` it is `Matrix.gaussSeidelSplitting`. -/
noncomputable def blockGaussSeidelSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) : Splitting A :=
  ⟨blockDiagPart π A + blockStrictLower π A, isUnit_blockDiagPart_add_blockStrictLower h⟩

/-- The complementary part of the block Gauss–Seidel splitting is `-F`: the forward sweep absorbs
the whole block-lower triangle. -/
theorem blockGaussSeidelSplitting_n (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) :
    (blockGaussSeidelSplitting π A h).n = -blockStrictUpper π A := by
  change blockDiagPart π A + blockStrictLower π A - A = -blockStrictUpper π A
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub,
    blockDiagPart_add_blockStrictLower_add_blockStrictUpper, sub_self]

/-- **Block SOR** (Saad, *Iterative Methods for Sparse Linear Systems*, Algorithm 4.2) with
parameter `ω`: `M = ω⁻¹ (D - ω E)`. With `π = id` it is `Matrix.sorSplitting`. -/
noncomputable def blockSorSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) {ω : 𝕜} (hω : ω ≠ 0) : Splitting A :=
  ⟨ω⁻¹ • blockDiagPart π A + blockStrictLower π A,
    isUnit_smul_blockDiagPart_add_blockStrictLower (inv_ne_zero hω) h⟩

/-- Block Gauss–Seidel is block SOR with `ω = 1`. -/
theorem blockSorSplitting_one (π : n → ι) (A : Matrix n n 𝕜) (h : IsUnit (blockDiagPart π A)) :
    blockSorSplitting π A h (one_ne_zero (α := 𝕜)) = blockGaussSeidelSplitting π A h := by
  ext : 1
  change (1 : 𝕜)⁻¹ • blockDiagPart π A + blockStrictLower π A
    = blockDiagPart π A + blockStrictLower π A
  rw [inv_one, one_smul]

end Splittings

end Matrix
