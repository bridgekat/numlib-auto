/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Rank`, where `Matrix.rank` and its behaviour under
multiplication by an invertible matrix and under reindexing already live.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.BlockDiagonal

/-!
# The nullity of a matrix

The *nullity* of a square matrix `A` over a field is the dimension of its null space
`LinearMap.ker A.mulVecLin`, the `Null A` of numerical linear algebra. Mathlib has `Matrix.rank`,
the dimension of the range, but not the rank–nullity relation between the two, nor the invariance
of the null space dimension under the operations that leave the rank alone.

## Main statements

* `Matrix.rank_add_finrank_ker_mulVecLin`: rank–nullity, `A.rank + nullity A = card`.
* `Matrix.finrank_ker_mulVecLin_reindex` and `Matrix.finrank_ker_mulVecLin_conj`: the nullity is
  unchanged by reindexing and by conjugation with an invertible matrix, both because the rank is.
* `Matrix.ker_mulVecLin_pow_le_succ`: the null spaces of the powers of a square matrix increase.
* `Matrix.finrank_ker_mulVecLin_blockDiagonal'`: the nullity of a block diagonal matrix is the sum
  of the nullities of its blocks, since its null space is the product of theirs
  (`Matrix.kerMulVecLinBlockDiagonal'Equiv`).
-/

open Module

namespace Matrix

variable {ι : Type*} {m : ι → Type*} {K : Type*} [Field K]

section Square

variable {n n' : Type*} [Fintype n] [Fintype n']

/-- **Rank–nullity for a square matrix**: the rank of `A` and the dimension of its null space add
up to the number of columns. -/
theorem rank_add_finrank_ker_mulVecLin (A : Matrix n n K) :
    A.rank + finrank K (LinearMap.ker A.mulVecLin) = Fintype.card n := by
  rw [rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_pi]

/-- Reindexing a square matrix does not change the dimension of its null space. -/
theorem finrank_ker_mulVecLin_reindex (σ : n ≃ n') (A : Matrix n n K) :
    finrank K (LinearMap.ker (reindex σ σ A).mulVecLin)
      = finrank K (LinearMap.ker A.mulVecLin) := by
  have h₁ := rank_add_finrank_ker_mulVecLin (reindex σ σ A)
  have h₂ := rank_add_finrank_ker_mulVecLin A
  rw [rank_reindex] at h₁
  rw [Fintype.card_congr σ] at h₂
  omega

variable [DecidableEq n]

/-- Conjugating a square matrix by an invertible matrix does not change its rank. -/
theorem rank_conj {A P : Matrix n n K} (hP : IsUnit P) : (P * A * P⁻¹).rank = A.rank := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  rw [rank_mul_eq_left_of_isUnit_det _ _ (isUnit_nonsing_inv_det P hd),
    rank_mul_eq_right_of_isUnit_det _ _ hd]

/-- Conjugating a square matrix by an invertible matrix does not change the dimension of its null
space. -/
theorem finrank_ker_mulVecLin_conj {A P : Matrix n n K} (hP : IsUnit P) :
    finrank K (LinearMap.ker (P * A * P⁻¹).mulVecLin)
      = finrank K (LinearMap.ker A.mulVecLin) := by
  have h₁ := rank_add_finrank_ker_mulVecLin (P * A * P⁻¹)
  have h₂ := rank_add_finrank_ker_mulVecLin A
  rw [rank_conj hP] at h₁
  omega

/-- The null spaces of the powers of a square matrix increase with the exponent. -/
theorem ker_mulVecLin_pow_le_succ (A : Matrix n n K) (k : ℕ) :
    LinearMap.ker ((A ^ k).mulVecLin) ≤ LinearMap.ker ((A ^ (k + 1)).mulVecLin) := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  rw [pow_succ', ← mulVec_mulVec, hv, mulVec_zero]

end Square

section BlockDiagonal

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (m i)]

/-- The null space of a block diagonal matrix is the product of the null spaces of its blocks: a
vector is annihilated by `blockDiagonal' M` exactly when each of its blocks is annihilated by the
corresponding `M i`. -/
noncomputable def kerMulVecLinBlockDiagonal'Equiv (M : ∀ i, Matrix (m i) (m i) K) :
    LinearMap.ker (blockDiagonal' M).mulVecLin ≃ₗ[K] ∀ i, LinearMap.ker (M i).mulVecLin where
  toFun v i := ⟨fun a => v.1 ⟨i, a⟩, by
    refine LinearMap.mem_ker.2 (funext fun a => ?_)
    have h := congrFun (LinearMap.mem_ker.1 v.2) (⟨i, a⟩ : (i : ι) × m i)
    rwa [mulVecLin_apply, blockDiagonal'_mulVec] at h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨fun x => (w x.1).1 x.2, by
    refine LinearMap.mem_ker.2 (funext fun x => ?_)
    obtain ⟨i, a⟩ := x
    rw [mulVecLin_apply, blockDiagonal'_mulVec]
    exact congrFun (LinearMap.mem_ker.1 (w i).2) a⟩
  left_inv v := by ext x; obtain ⟨i, a⟩ := x; rfl
  right_inv w := by ext i a; rfl

/-- **The nullity of a block diagonal matrix** is the sum of the nullities of its blocks. -/
theorem finrank_ker_mulVecLin_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) K) :
    finrank K (LinearMap.ker (blockDiagonal' M).mulVecLin)
      = ∑ i, finrank K (LinearMap.ker (M i).mulVecLin) := by
  rw [(kerMulVecLinBlockDiagonal'Equiv M).finrank_eq, Module.finrank_pi_fintype]

end BlockDiagonal

end Matrix
