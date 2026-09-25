import Mathlib.Logic.Equiv.Fin.Rotate
import NumlibSurface.GolubVanLoan.Chapter01.Section02

/-!
# Golub–Van Loan §1.6: parallel matrix multiplication (Cannon's identity)

Surface file for §1.6 of Golub and Van Loan, *Matrix Computations* (4th edition), formalized only
in its one precise statement: Cannon's identity (1.6.16) with the shift relations
`A^{(k+1)} = A^{(k)} Pᵀ`, `B^{(k+1)} = P B^{(k)}` of §1.6.8.

## Design

The block matrices of §1.6.8 are `N × N` arrays of `n₁ × n₁` blocks,
`Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)`, multiplied as matrices over the
(noncommutative) ring of blocks. Block indices are taken modulo `N` with `Fin N`'s own wrap-around
arithmetic. The book's `A^{(1)}, …, A^{(4)}` for `N = 4` are, 0-based, the general
`A^{(k)}_{ij} = A_{i, i + j − k}`, `B^{(k)}_{ij} = B_{i + j − k, j}` (`cannonA`, `cannonB`), which
is how the book's P1.6.6 asks for general `N`. The block downshift `P` of the shift relations is the
downshift `𝒟_N` of §1.2.11 (`GolubVanLoan.Chapter01.downshift`, the permutation matrix of
`(finRotate N)⁻¹`) acting on block rows; multiplying by it, or by its transpose on the right, is a
reindexing (`Matrix.submatrix`).

## Not formalized here

The model computation and its blockings (1.6.1)–(1.6.2) as a *parallel* program; the load-balancing
ratios (1.6.3)–(1.6.4); the time model (1.6.5)–(1.6.6) and the communication ratios
(1.6.7)–(1.6.15); barrier synchronization and the shared- and distributed-memory paradigms
(§1.6.5–1.6.7); the update sequence (1.6.17)–(1.6.20) and the toroidal message passing as
communication patterns. All are cost models or statements about processors, not about the computed
matrices.
-/

namespace GolubVanLoan.Chapter01

variable {N n₁ : ℕ}

/-- **§1.6.8**: the skewed block matrices of Cannon's algorithm,
`A^{(k)}_{ij} = A_{i, i + j − k}` (block indices modulo `N`, 0-based); for `N = 4` and
`k = 0, 1, 2, 3` they are the book's displayed `A^{(1)}, …, A^{(4)}`. Its twin is `cannonB`. -/
def cannonA (A : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)) (k : Fin N) :
    Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ) :=
  Matrix.of fun i j => A i (i + j - k)

/-- **§1.6.8**: the skewed block matrices `B^{(k)}_{ij} = B_{i + j − k, j}` of Cannon's algorithm,
the twin of `cannonA`. -/
def cannonB (B : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)) (k : Fin N) :
    Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ) :=
  Matrix.of fun i j => B (i + j - k) j

variable [NeZero N]

/-- **(1.6.16)** (Cannon's identity): for the block product `C = AB`,
`C_ij = ∑_{k} A^{(k)}_ij B^{(k)}_ij` — each block of `C` is a sum of products of the blocks that the
skewed matrices hold in the same position. -/
theorem equation_1_6_16 (A B : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)) (i j : Fin N) :
    (A * B) i j = ∑ k, cannonA A k i j * cannonB B k i j := by
  rw [Matrix.mul_apply]
  exact (Fintype.sum_equiv (Equiv.subLeft (i + j)) _ _ fun _ => rfl).symm

/-- `(finRotate N)⁻¹ j = j − 1`. -/
private theorem finRotate_symm_apply (j : Fin N) : (finRotate N).symm j = j - 1 := by
  rw [Equiv.symm_apply_eq, finRotate_apply, sub_add_cancel]

/-- **§1.6.8**: "observe that `A^{(k+1)} = A^{(k)} Pᵀ` and `B^{(k+1)} = P B^{(k)}`" for the block
downshift `P` (`downshift`): the `A`-blocks move one column right and the `B`-blocks one row down,
with wrap-around. Multiplication by the block permutation is the reindexing by
`(finRotate N)⁻¹`, the permutation of `𝒟_N`. -/
theorem cannon_succ (A B : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)) (k : Fin N) :
    cannonA A (k + 1) = (cannonA A k).submatrix id (finRotate N).symm ∧
      cannonB B (k + 1) = (cannonB B k).submatrix (finRotate N).symm id := by
  refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩ <;>
    simp only [cannonA, cannonB, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
      finRotate_symm_apply]
  · congr 1
    abel
  · congr 1
    abel

end GolubVanLoan.Chapter01
