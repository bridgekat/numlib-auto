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

The elementary identities of the Frobenius norm (Mathlib's scoped `Matrix.Norms.Frobenius`):
`‖A‖_F² = ∑ᵢⱼ |aᵢⱼ|²` (`Matrix.frobenius_norm_sq_eq_sum_sq`), `‖A‖_F² = tr(Aᴴ A)`
(`Matrix.frobenius_norm_sq_eq_trace`), `|aᵢⱼ| ≤ ‖A‖_F` (`Matrix.norm_entry_le_frobenius_norm`), and
the sums of the squared Euclidean norms of the columns and of the rows
(`Matrix.frobenius_norm_sq_eq_sum_norm_sq_col`, `Matrix.frobenius_norm_sq_eq_sum_norm_sq_row`).
-/

open Finset

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

open scoped Matrix.Norms.Frobenius

/-- The Frobenius norm squared is the sum of the squared entries. -/
theorem frobenius_norm_sq_eq_sum_sq (A : Matrix m n 𝕜) : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- **(1.18)**: `‖A‖_F² = tr(Aᴴ A)`, [quarteroni2000numerical] Example 1.7 (the display there
omits the square root). -/
theorem frobenius_norm_sq_eq_trace (A : Matrix m n 𝕜) :
    ((‖A‖ ^ 2 : ℝ) : 𝕜) = trace (Aᴴ * A) := by
  rw [frobenius_norm_sq_eq_sum_sq, trace, Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]

/-- An entry is bounded by the Frobenius norm, `|a_ij| ≤ ‖A‖_F`: the Frobenius form of
`Matrix.norm_entry_le_l2_opNorm`. -/
theorem norm_entry_le_frobenius_norm (A : Matrix m n 𝕜) (i : m) (j : n) : ‖A i j‖ ≤ ‖A‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq]
  calc ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

/-- The Frobenius norm squared is the sum of the squared Euclidean norms of the columns. -/
theorem frobenius_norm_sq_eq_sum_norm_sq_col (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ j, ‖(WithLp.toLp 2 fun i => A i j : EuclideanSpace 𝕜 m)‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by simp [EuclideanSpace.norm_sq_eq]

/-- The Frobenius norm squared is the sum of the squared Euclidean norms of the rows. -/
theorem frobenius_norm_sq_eq_sum_norm_sq_row (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq]
  exact Finset.sum_congr rfl fun i _ => by rw [EuclideanSpace.norm_sq_eq]

@[deprecated (since := "2026-09-30")]
alias frobenius_norm_sq_eq_sum_norm_toLp_row_sq := frobenius_norm_sq_eq_sum_norm_sq_row

end Matrix
