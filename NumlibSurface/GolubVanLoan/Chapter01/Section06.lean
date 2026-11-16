/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Logic.Equiv.Fin.Rotate
import NumlibSurface.GolubVanLoan.Chapter01.Section02

/-!
# Golub and Van Loan, Section 1.6: Parallel matrix multiplication

This module formalizes the one precise mathematical statement of §1.6 of [golub2013matrix]: Cannon's
identity (1.6.16), together with the shift relations $A^{(k+1)} = A^{(k)} P^T$ and
$B^{(k+1)} = P B^{(k)}$ of §1.6.8. Let $A$ and $B$ be $N \times N$ block matrices. For
$k = 0, \dots, N - 1$, the skewed block matrices $A^{(k)}$ and $B^{(k)}$ have the blocks
$A^{(k)}_{ij} = A_{i, i+j-k}$ and $B^{(k)}_{ij} = B_{i+j-k, j}$, with block indices modulo $N$.
Cannon's identity says that each block of $C = AB$ is $C_{ij} = \sum_k A^{(k)}_{ij} B^{(k)}_{ij}$, a
sum of products of blocks that the skewed matrices hold in the same position. The shift relations
say that $A^{(k+1)}$ and $B^{(k+1)}$ come from $A^{(k)}$ and $B^{(k)}$ by the block downshift
permutation $P$ of §1.2.11.

## Main definitions

* §1.6.8, `GolubVanLoan.Chapter01.cannonA`: the skewed block matrices $A^{(k)}$ of Cannon's
  algorithm.
* §1.6.8, `GolubVanLoan.Chapter01.cannonB`: the skewed block matrices $B^{(k)}$ of Cannon's
  algorithm.

## Main results

* Equation (1.6.16), `GolubVanLoan.Chapter01.equation_1_6_16`: Cannon's identity
  $C_{ij} = \sum_k A^{(k)}_{ij} B^{(k)}_{ij}$.
* §1.6.8, `GolubVanLoan.Chapter01.cannon_succ`: the shift relations $A^{(k+1)} = A^{(k)} P^T$ and
  $B^{(k+1)} = P B^{(k)}$.

## Conventions

* Block indices are 0-based and are taken modulo $N$ with the wraparound arithmetic of `Fin N`. The
  source's displayed $A^{(1)}, \dots, A^{(4)}$ for $N = 4$ are `GolubVanLoan.Chapter01.cannonA A k`
  for $k = 0, 1, 2, 3$.

## Implementation notes

* The block matrices of §1.6.8 are $N \times N$ arrays of $n_1 \times n_1$ blocks, `Matrix (Fin N)
  (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)`, multiplied as matrices over the noncommutative ring of
  blocks.
* The source displays $A^{(k)}$ and $B^{(k)}$ for $N = 4$ only. The general definitions for every
  $N$ are those that Problem P1.6.6 of the source asks for.
* The block downshift $P$ of the shift relations is the downshift $\mathcal{D}_N$ of §1.2.11 over
  the ring of blocks, the backbone's `Matrix.downshift N`, which is the permutation matrix of
  $\rho^{-1}$ for the cyclic rotation $\rho$ = `finRotate N`. A product with it on the left, or with
  its transpose on the right, is a reindexing (`Matrix.submatrix`).

## Not formalized

All the items below are cost models or statements about processors, not about the computed matrices.

* **The model computation and its blockings (1.6.1)–(1.6.2), as a parallel program.**
* **The load-balancing ratios (1.6.3)–(1.6.4).**
* **The time model (1.6.5)–(1.6.6) and the communication ratios (1.6.7)–(1.6.15).**
* **Barrier synchronization and the shared-memory and distributed-memory paradigms of
  §1.6.5–1.6.7.**
* **The update sequence (1.6.17)–(1.6.20) and the toroidal message passing, as communication
  patterns.**
-/

namespace GolubVanLoan.Chapter01

variable {N n₁ : ℕ}

/-- **§1.6.8** of [golub2013matrix], the skewed block matrices $A^{(k)}$ of Cannon's algorithm. Let
$A$ be an $N \times N$ matrix of $n_1 \times n_1$ blocks and $k \in \{0, \dots, N - 1\}$. Then
$A^{(k)}$ is the block matrix with the blocks
$$A^{(k)}_{ij} = A_{i, i+j-k},$$
with block indices 0-based and modulo $N$.

For $N = 4$ and $k = 0, 1, 2, 3$ these are the source's displayed $A^{(1)}, \dots, A^{(4)}$. The
twin definition is `GolubVanLoan.Chapter01.cannonB`. -/
def cannonA (A : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)) (k : Fin N) :
    Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ) :=
  Matrix.of fun i j => A i (i + j - k)

/-- **§1.6.8** of [golub2013matrix], the skewed block matrices $B^{(k)}$ of Cannon's algorithm. Let
$B$ be an $N \times N$ matrix of $n_1 \times n_1$ blocks and $k \in \{0, \dots, N - 1\}$. Then
$B^{(k)}$ is the block matrix with the blocks
$$B^{(k)}_{ij} = B_{i+j-k, j},$$
with block indices 0-based and modulo $N$.

This is the twin of `GolubVanLoan.Chapter01.cannonA`. -/
def cannonB (B : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)) (k : Fin N) :
    Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ) :=
  Matrix.of fun i j => B (i + j - k) j

variable [NeZero N]

/-- **Equation (1.6.16)** of [golub2013matrix] (Cannon's identity). Let $N \ge 1$, let $A$ and $B$
be $N \times N$ matrices of $n_1 \times n_1$ blocks, and let $C = AB$ be their block product.
Then for all block indices $i$ and $j$,
$$C_{ij} = \sum_{k=0}^{N-1} A^{(k)}_{ij} B^{(k)}_{ij}.$$
So each block of $C$ is a sum of products of the blocks that the skewed matrices hold in the
same position. -/
theorem equation_1_6_16 (A B : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)) (i j : Fin N) :
    (A * B) i j = ∑ k, cannonA A k i j * cannonB B k i j := by
  rw [Matrix.mul_apply]
  exact (Fintype.sum_equiv (Equiv.subLeft (i + j)) _ _ fun _ => rfl).symm

/-- The inverse cyclic rotation maps $j$ to $j - 1$ modulo $N$. -/
private theorem finRotate_symm_apply (j : Fin N) : (finRotate N).symm j = j - 1 := by
  rw [Equiv.symm_apply_eq, finRotate_apply, sub_add_cancel]

/-- The shift relations as reindexings: from $A^{(k)}$ to $A^{(k+1)}$ the blocks move one column to
the right, and from $B^{(k)}$ to $B^{(k+1)}$ they move one row down, with wraparound. -/
private theorem cannon_succ_submatrix (A B : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ))
    (k : Fin N) :
    cannonA A (k + 1) = (cannonA A k).submatrix id (finRotate N).symm ∧
      cannonB B (k + 1) = (cannonB B k).submatrix (finRotate N).symm id := by
  refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩ <;>
    simp only [cannonA, cannonB, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
      finRotate_symm_apply]
  · congr 1
    abel
  · congr 1
    abel

/-- **§1.6.8** of [golub2013matrix], the shift relations. "Define the block downshift permutation
$P$ … and observe that $A^{(k+1)} = A^{(k)} P^T$ and $B^{(k+1)} = P B^{(k)}$". That is, let
$N \ge 1$, let $A$ and $B$ be $N \times N$ matrices of $n_1 \times n_1$ blocks, and let
$k \in \{0, \dots, N - 1\}$, with $k + 1$ taken modulo $N$. Then
$$A^{(k+1)} = A^{(k)} P^T, \qquad B^{(k+1)} = P B^{(k)}.$$

The matrix $P$ is the downshift $\mathcal{D}_N$ of §1.2.11 over the ring of $n_1 \times n_1$
blocks, `Matrix.downshift N`: it has identity blocks at the cyclic positions $(j + 1, j)$ and
zero blocks elsewhere. -/
theorem cannon_succ (A B : Matrix (Fin N) (Fin N) (Matrix (Fin n₁) (Fin n₁) ℝ)) (k : Fin N) :
    cannonA A (k + 1) = cannonA A k * (Matrix.downshift N).transpose ∧
      cannonB B (k + 1) = Matrix.downshift N * cannonB B k := by
  obtain ⟨hA, hB⟩ := cannon_succ_submatrix A B k
  rw [hA, hB, Matrix.downshift, Matrix.transpose_permMatrix, Equiv.Perm.permMatrix,
    Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  exact ⟨rfl, rfl⟩

end GolubVanLoan.Chapter01
