/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Block` for the determinant and
`Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` for the characteristic matrix and polynomial, which
are where the block triangular determinant `Matrix.BlockTriangular.det_fintype` and the block
triangular characteristic polynomial `Matrix.BlockTriangular.charpoly` already live.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The determinant and the characteristic polynomial of a block diagonal matrix

A matrix `Matrix.blockDiagonal' M`, assembled from a finite family of square blocks
`M i : Matrix (m i) (m i) R` of possibly different sizes, has determinant `∏ i, (M i).det` and
characteristic polynomial `∏ i, (M i).charpoly`.

Mathlib has the determinant of a block *diagonal* matrix only for blocks that all have the same
size (`Matrix.det_blockDiagonal`), and the determinant of a block *triangular* matrix as a product
over the blocks that the ordering cuts out (`Matrix.BlockTriangular.det_fintype`). The results here
are the missing block diagonal case with varying block sizes; they are read off the block
triangular ones, since a block diagonal matrix is block triangular for `Sigma.fst` under any linear
order on the index, and the block that `Matrix.toSquareBlock` cuts out over `k` is `M k` reindexed
along `Equiv.sigmaSubtype`.

The characteristic polynomial then costs nothing beyond the determinant: the characteristic matrix
of a block diagonal matrix is the block diagonal matrix of the characteristic matrices
(`Matrix.charmatrix_blockDiagonal'`), so the identity over `R` gives the identity over `R[X]`.

## Main statements

* `Matrix.det_blockDiagonal'`: `(blockDiagonal' M).det = ∏ i, (M i).det`.
* `Matrix.charpoly_blockDiagonal'`: `(blockDiagonal' M).charpoly = ∏ i, (M i).charpoly`.
* `Matrix.blockDiagonal'_mulVec`: a block diagonal matrix acts on a vector blockwise.
-/

open Polynomial

namespace Matrix

variable {ι : Type*} {m : ι → Type*} {R : Type*}

section Zero

variable [Zero R] [DecidableEq ι]

/-- The diagonal block that `Matrix.toSquareBlock` cuts out of a block diagonal matrix over `k` is
the block `M k`, reindexed along the identification of the fibre of `Sigma.fst` over `k` with
`m k`. -/
theorem reindex_toSquareBlock_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) R) (k : ι) :
    reindex (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k)
        ((blockDiagonal' M).toSquareBlock Sigma.fst k) = M k := by
  ext a b
  exact blockDiagonal'_apply_eq M k a b

end Zero

section CommRing

variable [CommRing R] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- **The determinant of a block diagonal matrix** is the product of the determinants of its
blocks, which may have different sizes. -/
theorem det_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(blockTriangular_blockDiagonal' M).det_fintype]
  exact Finset.prod_congr rfl fun k _ => by
    rw [← reindex_toSquareBlock_blockDiagonal' M k, det_reindex_self]

/-- The characteristic matrix of a block diagonal matrix is the block diagonal matrix of the
characteristic matrices of its blocks. -/
theorem charmatrix_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) R) :
    charmatrix (blockDiagonal' M) = blockDiagonal' fun i => charmatrix (M i) := by
  have hfun : (fun i => charmatrix (M i))
      = (fun i => (Matrix.scalar (m i) (X : R[X])))
        - fun i => (C : R →+* R[X]).mapMatrix (M i) := rfl
  rw [charmatrix, hfun, blockDiagonal'_sub]
  congr 1
  · exact (blockDiagonal'_diagonal fun _ _ => (X : R[X])).symm
  · exact blockDiagonal'_map M (C : R →+* R[X]) (map_zero C)

/-- **The characteristic polynomial of a block diagonal matrix** is the product of the
characteristic polynomials of its blocks, which may have different sizes. -/
theorem charpoly_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' M).charpoly = ∏ i, (M i).charpoly := by
  rw [charpoly, charmatrix_blockDiagonal', det_blockDiagonal']
  rfl

end CommRing

section Shift

variable [CommRing R] [DecidableEq ι] [∀ i, DecidableEq (m i)]

/-- Shifting a block diagonal matrix by a scalar shifts each of its blocks. -/
theorem blockDiagonal'_sub_smul_one (M : ∀ i, Matrix (m i) (m i) R) (c : R) :
    blockDiagonal' M - c • 1 = blockDiagonal' fun i => M i - c • 1 := by
  have hfun : (fun i => M i - c • (1 : Matrix (m i) (m i) R))
      = M - c • fun i => (1 : Matrix (m i) (m i) R) := rfl
  rw [hfun, blockDiagonal'_sub, blockDiagonal'_smul,
    show (blockDiagonal' fun i : ι => (1 : Matrix (m i) (m i) R)) = 1 from blockDiagonal'_one]

end Shift

section Semiring

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (m i)] [NonUnitalNonAssocSemiring R]

/-- A block diagonal matrix acts on a vector blockwise. -/
theorem blockDiagonal'_mulVec (M : ∀ i, Matrix (m i) (m i) R) (v : (i : ι) × m i → R)
    (i : ι) (a : m i) :
    (blockDiagonal' M *ᵥ v) ⟨i, a⟩ = (M i *ᵥ fun b => v ⟨i, b⟩) a := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun b _ => by rw [blockDiagonal'_apply_eq]
  · exact fun j _ hj => Finset.sum_eq_zero fun b _ => by
      rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hj), zero_mul]
  · exact fun h => absurd (Finset.mem_univ i) h

end Semiring

end Matrix
