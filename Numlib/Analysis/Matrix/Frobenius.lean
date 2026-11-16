/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix.Normed`, beside `Matrix.frobenius_norm_def`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Positivity.Finset

/-!
# The Frobenius norm, entry by entry

The Frobenius norm of a matrix $A = (a_{ij}) \in \mathbb{K}^{m \times n}$, over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, is $\|A\|_F = \bigl(\sum_{i,j} |a_{ij}|^2\bigr)^{1/2}$.
This file proves its elementary identities: $\|A\|_F^2 = \sum_{i,j} |a_{ij}|^2$,
$\|A\|_F^2 = \operatorname{tr}(A^H A)$, the bound $|a_{ij}| \le \|A\|_F$, and the expressions of
$\|A\|_F^2$ as the sum of the squared Euclidean norms of the columns and of the rows. A matrix that
is zero outside a block has the Frobenius norm of the block.

## Main results

* `Matrix.frobenius_norm_sq_eq_sum_sq`: $\|A\|_F^2 = \sum_{i,j} |a_{ij}|^2$.
* `Matrix.frobenius_norm_sq_eq_trace`: $\|A\|_F^2 = \operatorname{tr}(A^H A)$.
* `Matrix.norm_entry_le_frobenius_norm`: $|a_{ij}| \le \|A\|_F$.
* `Matrix.frobenius_norm_sq_eq_sum_norm_sq_col` and `Matrix.frobenius_norm_sq_eq_sum_norm_sq_row`:
  $\|A\|_F^2$ is the sum of the squared Euclidean norms of the columns, and of the rows.
* `Matrix.frobenius_norm_eq_submatrix_val`: a matrix that is zero outside a block has the Frobenius
  norm of the block.

## Implementation notes

* The norm is Mathlib's Frobenius norm on `Matrix m n 𝕜`, from the scoped instances
  `Matrix.Norms.Frobenius`, with rows and columns indexed by finite types.
-/

open Finset

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

open scoped Matrix.Norms.Frobenius

/-- For every matrix $A = (a_{ij}) \in \mathbb{K}^{m \times n}$,
$$\|A\|_F^2 = \sum_{i,j} |a_{ij}|^2.$$
-/
theorem frobenius_norm_sq_eq_sum_sq (A : Matrix m n 𝕜) : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- For every matrix $A \in \mathbb{K}^{m \times n}$,
$$\|A\|_F^2 = \operatorname{tr}(A^H A).$$
This is (1.18) in Example 1.7 of [quarteroni2000numerical]; the display there omits the square
root.

The real number $\|A\|_F^2$ is embedded in $\mathbb{K}$. -/
theorem frobenius_norm_sq_eq_trace (A : Matrix m n 𝕜) :
    ((‖A‖ ^ 2 : ℝ) : 𝕜) = trace (Aᴴ * A) := by
  rw [frobenius_norm_sq_eq_sum_sq, trace, Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]

/-- Every entry of a matrix $A = (a_{ij})$ is bounded by its Frobenius norm: $|a_{ij}| \le \|A\|_F$.

This is the Frobenius form of `Matrix.norm_entry_le_l2_opNorm`. -/
theorem norm_entry_le_frobenius_norm (A : Matrix m n 𝕜) (i : m) (j : n) : ‖A i j‖ ≤ ‖A‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq]
  calc ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

/-- For every matrix $A \in \mathbb{K}^{m \times n}$, $\|A\|_F^2$ is the sum of the squared
Euclidean norms of the columns:
$$\|A\|_F^2 = \sum_j \|A e_j\|_2^2.$$
-/
theorem frobenius_norm_sq_eq_sum_norm_sq_col (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ j, ‖(WithLp.toLp 2 fun i => A i j : EuclideanSpace 𝕜 m)‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by simp [EuclideanSpace.norm_sq_eq]

/-- For every matrix $A \in \mathbb{K}^{m \times n}$, $\|A\|_F^2$ is the sum of the squared
Euclidean norms of the rows:
$$\|A\|_F^2 = \sum_i \|a_{i,:}\|_2^2,$$
where $a_{i,:} \in \mathbb{K}^n$ is the $i$-th row of $A$. -/
theorem frobenius_norm_sq_eq_sum_norm_sq_row (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq]
  exact Finset.sum_congr rfl fun i _ => by rw [EuclideanSpace.norm_sq_eq]

/-- Let $P$ be a set of row indices and $Q$ a set of column indices, and let $A$ be a matrix with
$a_{ij} = 0$ unless $i \in P$ and $j \in Q$. Then $\|A\|_F$ is the Frobenius norm of the block
$(a_{ij})_{i \in P, j \in Q}$.

The sets are given by predicates `p` and `q`, and the block is
`A.submatrix Subtype.val Subtype.val`. -/
theorem frobenius_norm_eq_submatrix_val {p : m → Prop} {q : n → Prop} [DecidablePred p]
    [DecidablePred q] {A : Matrix m n 𝕜} (h : ∀ i j, ¬ (p i ∧ q j) → A i j = 0) :
    ‖A‖ = ‖A.submatrix (Subtype.val : {i // p i} → m) (Subtype.val : {j // q j} → n)‖ := by
  have hsq : ‖A‖ ^ 2 =
      ‖A.submatrix (Subtype.val : {i // p i} → m) (Subtype.val : {j // q j} → n)‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq,
      ← Fintype.sum_subtype_add_sum_subtype p]
    have h2 : ∑ r : {i // ¬ p i}, ∑ j, ‖A r j‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun j _ => by
        rw [h r j fun h => r.2 h.1]
        simp
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Fintype.sum_subtype_add_sum_subtype q]
    have h3 : ∑ s : {j // ¬ q j}, ‖A a s‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun s _ => by
        rw [h a s fun h => s.2 h.2]
        simp
    rw [h3, add_zero]
    rfl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

end Matrix
