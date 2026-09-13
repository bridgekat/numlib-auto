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
# The nullity of a matrix, and the rank as the largest nonvanishing minor

The *nullity* of a square matrix `A` over a field is the dimension of its null space
`LinearMap.ker A.mulVecLin`, the `Null A` of numerical linear algebra. Mathlib has `Matrix.rank`,
the dimension of the range, but not the rank–nullity relation between the two, nor the invariance
of the null space dimension under the operations that leave the rank alone. Nor does it have the
classical characterization of the rank as the largest order of a nonvanishing minor
([quarteroni2000numerical] Definition 1.12), which is the last section.

## Main statements

* `Matrix.rank_add_finrank_ker_mulVecLin`: rank–nullity, `A.rank + nullity A = card`.
* `Matrix.finrank_ker_mulVecLin_reindex` and `Matrix.finrank_ker_mulVecLin_conj`: the nullity is
  unchanged by reindexing and by conjugation with an invertible matrix, both because the rank is.
* `Matrix.ker_mulVecLin_pow_le_succ`: the null spaces of the powers of a square matrix increase.
* `Matrix.finrank_ker_mulVecLin_blockDiagonal'`: the nullity of a block diagonal matrix is the sum
  of the nullities of its blocks, since its null space is the product of theirs
  (`Matrix.kerMulVecLinBlockDiagonal'Equiv`).
* `Matrix.rank_eq_sup_card_det_submatrix_ne_zero`: the rank of a rectangular matrix is the
  largest `k` for which some `k × k` submatrix has nonzero determinant; the two inequalities are
  `Matrix.card_le_rank_of_det_submatrix_ne_zero` and `Matrix.exists_det_submatrix_ne_zero`.
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

section Minor

variable {m n : Type*} [Fintype n] (A : Matrix m n K)

/-- A nonvanishing minor of order `k` forces rank at least `k`: the `k × k` submatrix is a unit,
so its rank is `k`, and the rank of a submatrix is at most the rank. -/
theorem card_le_rank_of_det_submatrix_ne_zero {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : k ≤ A.rank := by
  have hu : IsUnit (A.submatrix r c) := (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have := rank_submatrix_le A r c
  rwa [rank_of_isUnit _ hu, Fintype.card_fin] at this

omit [Fintype n] in
/-- The row selection of a nonvanishing minor is injective: two equal rows give a zero
determinant. -/
theorem injective_of_det_submatrix_ne_zero_left {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : Function.Injective r := fun a b hab => by
  by_contra hne
  exact h (det_zero_of_row_eq hne (funext fun j => by simp [hab]))

omit [Fintype n] in
/-- The column selection of a nonvanishing minor is injective. -/
theorem injective_of_det_submatrix_ne_zero_right {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : Function.Injective c := fun a b hab => by
  by_contra hne
  exact h (det_zero_of_column_eq hne fun i => by simp [hab])

/-- A matrix of rank `k` has `k` linearly independent columns. -/
theorem exists_linearIndependent_col {k : ℕ} (h : A.rank = k) :
    ∃ c : Fin k → n, LinearIndependent K (A.col ∘ c) := by
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have htf : t.Finite := (Set.finite_range A.col).subset ht
  have : Fintype t := htf.fintype
  have hcard : Fintype.card t = k := by
    rw [← h, rank_eq_finrank_span_cols, ← hsp, finrank_span_set_eq_card hli, Set.toFinset_card]
  let e : Fin k ≃ t := (Fintype.equivFinOfCardEq hcard).symm
  choose c hc using fun x : t => ht x.2
  refine ⟨c ∘ e, ?_⟩
  have : A.col ∘ (c ∘ e) = ((↑) : t → m → K) ∘ e := funext fun i => hc (e i)
  rw [this]
  exact hli.comp e e.injective

/-- A matrix of rank `k` has a nonsingular `k × k` submatrix: choose `k` linearly independent
columns, then `k` linearly independent rows of the resulting `m × k` matrix (which has rank `k`
as well); a square matrix with linearly independent rows is a unit. -/
theorem exists_det_submatrix_ne_zero [Finite m] :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n), (A.submatrix r c).det ≠ 0 := by
  have := Fintype.ofFinite m
  obtain ⟨c, hc⟩ := exists_linearIndependent_col A rfl
  have hB : (A.submatrix id c)ᵀ.rank = A.rank := by
    rw [rank_transpose, rank_eq_finrank_span_cols]
    have : (A.submatrix id c).col = A.col ∘ c := rfl
    rw [this, finrank_span_eq_card hc, Fintype.card_fin]
  obtain ⟨r, hr⟩ := exists_linearIndependent_col _ hB
  refine ⟨r, c, ?_⟩
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, ← linearIndependent_rows_iff_isUnit]
  exact hr

/-- [quarteroni2000numerical] Definition 1.12 as a theorem: the rank is the largest order of a
nonvanishing minor. The set of orders is bounded by the rank
(`Matrix.card_le_rank_of_det_submatrix_ne_zero`) and attains it
(`Matrix.exists_det_submatrix_ne_zero`). -/
theorem rank_eq_sup_card_det_submatrix_ne_zero [Finite m] :
    A.rank = sSup {k | ∃ (r : Fin k ↪ m) (c : Fin k ↪ n), (A.submatrix r c).det ≠ 0} := by
  have hub : ∀ k ∈ {k | ∃ (r : Fin k ↪ m) (c : Fin k ↪ n), (A.submatrix r c).det ≠ 0},
      k ≤ A.rank := fun k ⟨_, _, h⟩ => card_le_rank_of_det_submatrix_ne_zero A h
  have hmem : A.rank ∈ {k | ∃ (r : Fin k ↪ m) (c : Fin k ↪ n), (A.submatrix r c).det ≠ 0} := by
    obtain ⟨r, c, h⟩ := exists_det_submatrix_ne_zero A
    exact ⟨⟨r, injective_of_det_submatrix_ne_zero_left A h⟩,
      ⟨c, injective_of_det_submatrix_ne_zero_right A h⟩, h⟩
  exact le_antisymm (le_csSup ⟨A.rank, hub⟩ hmem) (csSup_le ⟨_, hmem⟩ hub)

end Minor

end Matrix
