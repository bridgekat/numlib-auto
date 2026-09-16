/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LU`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.LU

/-!
# One step of Gaussian elimination

One step of Gaussian elimination at a pivot `p`, applied to a square matrix `M` indexed by a
finite linear order `n`: the rows strictly below `p` have `M i p / M p p` times the row `p`
subtracted from them, and every other row is left alone. It is the elementary operation from which
the `LU` factorization (`Numlib/LinearAlgebra/Matrix/LU`) and the incomplete factorizations of
`Numlib/Preconditioner/ILU` are built.

## Main definitions

* `Matrix.elimMultipliers M p`: the matrix `N` of multipliers, `M i p / M p p` in the column `p`
  below the pivot and zero elsewhere; `Matrix.elimMul M p`: the unipotent factor `G = 1 + N` of
  the step; `Matrix.elimStep M p`: the eliminated matrix `M - N M = (1 - N) M`;
  `Matrix.gaussTransform M p = 1 - N`, the Gaussian transformation matrix `M_p` of
  [quarteroni2000numerical] §3.3.1.
* `Matrix.gemStage A k`, the stages `A^{(k+1)}` of the Gaussian elimination method on `Fin N`
  ([quarteroni2000numerical] (3.29)), and `Matrix.gemLower A`, the matrix of multipliers ((3.37)).
* `Matrix.luPacked A`, the Doolittle recurrence ((3.43)) as one total function on any finite
  linear order, by well-founded recursion on the number of indices below `min i j`, with
  `Matrix.luLower A` and `Matrix.luUpper A` the two factors read off the packed form; and the Crout
  factors `Matrix.croutLower`, `Matrix.croutUpper`, which are Doolittle applied to the transpose.

## Main results

* `Matrix.elimStep_apply_pivot`: the step annihilates the pivot column below the pivot, and
  `Matrix.elimStep_apply_of_not_lt` says it changes nothing above it.
* `Matrix.elimMultipliers_mul_self`: `N * N = 0`, so that `G⁻¹ = 1 - N`
  (`Matrix.inv_elimMul`, `Matrix.gaussTransform_mul_elimMul`), [quarteroni2000numerical] (3.36).
* `Matrix.elimMul_mul_elimStep`: the factorization `M = G * elimStep M p` of one step;
  `Matrix.gemStage_succ_eq_gaussTransform_mul`: `A^{(k+1)} = M_k A^{(k)}` ((3.35)).
* `Matrix.isLU_gemLower_gemStage`: Gaussian elimination as a factorization method, `A = L U` with
  `U = A^{(N)}` the last stage, when the pivots `a_kk^{(k)}`, `k < N - 1`, are nonzero; and
  `Matrix.gemStage_pivots_ne_zero_iff`: those pivots are nonzero exactly when the strict leading
  principal submatrices of `A` are nonsingular (the book's sentence after (3.33)).
* `Matrix.elimStep_submatrix_orderEmbedding` and `Matrix.gemStage_submatrix_blockEmb`: elimination
  commutes with the restriction to a block of indices carried by an order embedding, so that the
  elimination of the trailing block of `A^{(k)}` on the `j` consecutive indices `k, …, k + j - 1`
  (`Matrix.blockEmb`) is the restriction of the global elimination;
  `Matrix.elimStep_submatrix_id_of_apply_self`: one step commutes with a permutation of the columns
  fixing the pivot.
* `Matrix.isLU_luLower_luUpper`: the Doolittle recurrence computes the LU factorization whenever
  the strict leading principal submatrices are nonsingular; `Matrix.luLower_eq_gemLower`: every
  loop order computes the same factors; `Matrix.croutLower_mul_croutUpper`: the Crout
  factorization.

## Implementation notes

The index type is kept fixed: elimination is written as multiplication by the unipotent `G` on
the whole of `n`, rather than as a Schur complement on the smaller index type `{i // i ≠ p}`. The
accumulated `L` factor of a factorization is then a product of the matrices `elimMul`, and no
reindexing appears anywhere in the statements; the same step read on the smaller index type is
`Matrix.schurComplementSingle` of `Numlib/LinearAlgebra/Matrix/SchurComplement`. Only the strict
order `p < i` of the index type is used, to say which rows lie below the pivot.

The last pivot `a_{N-1,N-1}^{(N-1)}` is never used as a divisor, so the factorization theorems ask
only for the pivots `k` with `k + 1 < N` to be nonzero; this is what makes them equivalent to the
nonsingularity of the *strict* leading principal submatrices, and lets a singular matrix with
nonsingular strict leading blocks (Example 3.3's `B`) be factored. The restriction is not a
convenience: quantifying `Matrix.gemStage_pivots_ne_zero_iff` over *all* the pivots would make it
false. For `B = !![1, 2; 1, 2]` of [quarteroni2000numerical] Example 3.3 the strict leading
principal submatrices are the empty one and `!![1]`, both units, while the last pivot is
`b₂₂ - (b₂₁/b₁₁) b₁₂ = 2 - 2 = 0`; the `1 × 1` zero matrix is the same failure with an empty strict
block. The last pivot is `det A / det A(< N - 1)`, so it vanishes for every singular `A` whose
strict leading blocks are nonsingular. The book restricts its own condition the same way, to
`k = 1, …, n - 1`, in the sentence after (3.33) and in Theorem 3.4.

Everything is over a field, and nothing here is numerical: pivoting and the growth factor belong
to `Numlib/LinearAlgebra/Matrix/LU/Pivoting`.

## References

* [saad2003iterative] §10.3.
* [quarteroni2000numerical] §3.3.
-/

open Finset

namespace Matrix

section Step

variable {n K : Type*} [LinearOrder n] [DecidableEq n] [Field K]

/-- **The multipliers of one step of Gaussian elimination** at the pivot `p`: the entries `M i p / M
p p` in column `p` and in the rows below `p`, and zero elsewhere. It is nilpotent of square zero,
because its only nonzero column is indexed by `p` and its row `p` vanishes. -/
noncomputable def elimMultipliers (M : Matrix n n K) (p : n) : Matrix n n K :=
  Matrix.of fun i j => if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0

/-- **The unipotent factor** of one step of Gaussian elimination at the pivot `p`. -/
noncomputable def elimMul (M : Matrix n n K) (p : n) : Matrix n n K :=
  1 + elimMultipliers M p

/-- Entries of the multiplier matrix: `M i p / M p p` in column `p` below the pivot, zero elsewhere.
-/
@[simp]
theorem elimMultipliers_apply (M : Matrix n n K) (p i j : n) :
    elimMultipliers M p i j = if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0 := rfl

variable [Fintype n]

/-- **One step of Gaussian elimination** at the pivot `p`, on the whole index type: the rows
strictly below `p` have `M i p / M p p` times row `p` subtracted from them, and every other row is
left alone. Keeping the index type fixed is what lets the accumulated `L` factor of a
factorization be a product of `Matrix.elimMul`s, with no reindexing anywhere; the same step read on
the index type without `p` is `Matrix.schurComplementSingle`. -/
noncomputable def elimStep (M : Matrix n n K) (p : n) : Matrix n n K :=
  M - elimMultipliers M p * M

/-- The multipliers of one row: the product `N M` has the correction of one elimination step as its
entries. -/
theorem elimMultipliers_mul_apply (M : Matrix n n K) (p i j : n) :
    (elimMultipliers M p * M) i j = if p < i then M i p * (M p p)⁻¹ * M p j else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : p < i
  · rw [ite_eq_left hi, Finset.sum_eq_single p (fun c _ hc => by simp [hc]) (by simp)]
    simp [hi]
  · simp [hi]

/-- Entries of the eliminated matrix: the rows below the pivot lose `M i p / M p p` times row `p`,
and every other row is unchanged. -/
theorem elimStep_apply (M : Matrix n n K) (p i j : n) :
    elimStep M p i j = M i j - if p < i then M i p * (M p p)⁻¹ * M p j else 0 := by
  rw [elimStep, Matrix.sub_apply, elimMultipliers_mul_apply]

/-- Above the pivot and in the pivot row itself, one elimination step changes nothing. -/
theorem elimStep_apply_of_not_lt (M : Matrix n n K) {p i : n} (hi : ¬ p < i) (j : n) :
    elimStep M p i j = M i j := by
  rw [elimStep_apply, ite_eq_right hi, sub_zero]

/-- Below the pivot, one elimination step is the usual formula. -/
theorem elimStep_apply_of_lt (M : Matrix n n K) {p i : n} (hi : p < i) (j : n) :
    elimStep M p i j = M i j - M i p * (M p p)⁻¹ * M p j := by
  rw [elimStep_apply, ite_eq_left hi]

/-- One elimination step annihilates the pivot column below the pivot. -/
theorem elimStep_apply_pivot (M : Matrix n n K) {p i : n} (hi : p < i) (hp : M p p ≠ 0) :
    elimStep M p i p = 0 := by
  rw [elimStep_apply_of_lt M hi, mul_assoc, inv_mul_cancel₀ hp, mul_one, sub_self]

/-- One elimination step leaves a column that is already zero in the pivot row alone. -/
theorem elimStep_apply_of_pivot_row_eq_zero (M : Matrix n n K) (p i : n) {j : n}
    (hj : M p j = 0) : elimStep M p i j = M i j := by
  rw [elimStep_apply, hj, mul_zero, ite_self, sub_zero]

/-- The multiplier matrix squares to zero. -/
theorem elimMultipliers_mul_self (M : Matrix n n K) (p : n) :
    elimMultipliers M p * elimMultipliers M p = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases eq_or_ne c p with rfl | hc
  · simp
  · simp [hc]

/-- The unipotent factor is inverted by `1 - N`. -/
theorem elimMul_mul_one_sub (M : Matrix n n K) (p : n) :
    elimMul M p * (1 - elimMultipliers M p) = 1 := by
  rw [elimMul, add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    elimMultipliers_mul_self, sub_zero]
  abel

/-- `1 - N` inverts the unipotent factor on the left as well. -/
theorem one_sub_mul_elimMul (M : Matrix n n K) (p : n) :
    (1 - elimMultipliers M p) * elimMul M p = 1 := by
  rw [elimMul, Matrix.mul_add, Matrix.mul_one, sub_mul, Matrix.one_mul,
    elimMultipliers_mul_self, sub_zero]
  abel

/-- The unipotent factor of an elimination step is a unit. -/
theorem isUnit_elimMul (M : Matrix n n K) (p : n) : IsUnit (elimMul M p) :=
  ⟨⟨_, _, elimMul_mul_one_sub M p, one_sub_mul_elimMul M p⟩, rfl⟩

/-- The inverse of the unipotent factor is `1 - N`, obtained by negating the multipliers. -/
theorem inv_elimMul (M : Matrix n n K) (p : n) :
    (elimMul M p)⁻¹ = 1 - elimMultipliers M p :=
  Matrix.inv_eq_right_inv (elimMul_mul_one_sub M p)

/-- **The factorization of one elimination step**: `M = G M₁` with `G` the unipotent factor and `M₁`
the eliminated matrix. -/
theorem elimMul_mul_elimStep (M : Matrix n n K) (p : n) : elimMul M p * elimStep M p = M := by
  rw [elimStep, elimMul, Matrix.mul_sub, add_mul, Matrix.one_mul, add_mul, Matrix.one_mul,
    ← Matrix.mul_assoc, elimMultipliers_mul_self, Matrix.zero_mul, add_zero]
  abel

end Step

/-! ### The Gaussian transformation matrices -/

variable {n K : Type*} [LinearOrder n] [Field K]

/-- The `p`-th Gaussian transformation matrix `M_p = 1 - m_p e_pᵀ` of
[quarteroni2000numerical] §3.3.1: the identity with the negated multipliers in column `p` below
the pivot. It is the inverse of the unipotent factor `Matrix.elimMul`, and it performs one
elimination step by left multiplication (`Matrix.gaussTransform_mul`). -/
noncomputable def gaussTransform (M : Matrix n n K) (p : n) : Matrix n n K :=
  1 - elimMultipliers M p

variable [Fintype n]

/-- `M_p⁻¹ = 2 I - M_p = 1 + m_p e_pᵀ`, [quarteroni2000numerical] (3.36): the Gaussian
transformation and the unipotent factor are mutually inverse. -/
theorem gaussTransform_mul_elimMul (M : Matrix n n K) (p : n) :
    gaussTransform M p * elimMul M p = 1 :=
  one_sub_mul_elimMul M p

/-- The unipotent factor times the Gaussian transformation is the identity. -/
theorem elimMul_mul_gaussTransform (M : Matrix n n K) (p : n) :
    elimMul M p * gaussTransform M p = 1 :=
  elimMul_mul_one_sub M p

/-- The inverse of the unipotent factor is the Gaussian transformation. -/
theorem inv_elimMul_eq_gaussTransform (M : Matrix n n K) (p : n) :
    (elimMul M p)⁻¹ = gaussTransform M p :=
  inv_elimMul M p

/-- One elimination step is left multiplication by the Gaussian transformation
([quarteroni2000numerical] (3.35)). -/
theorem gaussTransform_mul (M : Matrix n n K) (p : n) : gaussTransform M p * M = elimStep M p := by
  rw [gaussTransform, elimStep, sub_mul, Matrix.one_mul]

/-! ### The stages of Gaussian elimination on `Fin N` -/

section Stages

variable {N : ℕ}

/-- The stages `A^{(k+1)}` of the Gaussian elimination method, [quarteroni2000numerical] (3.29):
`gemStage A 0 = A` and `gemStage A (k + 1)` eliminates the column `k` below the pivot `(k, k)` of
`gemStage A k`. Beyond `N` nothing happens, and `gemStage A N` is the upper factor `U`. -/
noncomputable def gemStage (A : Matrix (Fin N) (Fin N) K) : ℕ → Matrix (Fin N) (Fin N) K
  | 0 => A
  | k + 1 => if h : k < N then elimStep (gemStage A k) ⟨k, h⟩ else gemStage A k

variable (A : Matrix (Fin N) (Fin N) K)

/-- Stage `0` is the matrix itself. -/
@[simp]
theorem gemStage_zero : gemStage A 0 = A := rfl

/-- Stage `k + 1` eliminates column `k` of stage `k`. -/
theorem gemStage_succ_of_lt {k : ℕ} (h : k < N) :
    gemStage A (k + 1) = elimStep (gemStage A k) ⟨k, h⟩ := by
  simp only [gemStage, h, dite_true]

/-- Beyond `N`, the stages do not change. -/
theorem gemStage_succ_of_le {k : ℕ} (h : N ≤ k) : gemStage A (k + 1) = gemStage A k := by
  simp only [gemStage, not_lt.2 h, dite_false]

/-- [quarteroni2000numerical] (3.35): `A^{(k+1)} = M_k A^{(k)}`. -/
theorem gemStage_succ_eq_gaussTransform_mul {k : ℕ} (h : k < N) :
    gemStage A (k + 1) = gaussTransform (gemStage A k) ⟨k, h⟩ * gemStage A k := by
  rw [gemStage_succ_of_lt A h, gaussTransform_mul]

/-- Stage `k + 1` changes only the rows strictly below `k`. -/
theorem gemStage_succ_apply_of_le {k : ℕ} {i : Fin N} (hi : (i : ℕ) ≤ k) (j : Fin N) :
    gemStage A (k + 1) i j = gemStage A k i j := by
  by_cases h : k < N
  · rw [gemStage_succ_of_lt A h, elimStep_apply_of_not_lt _ (by simpa [Fin.lt_def] using hi)]
  · rw [gemStage_succ_of_le A (not_lt.1 h)]

/-- Row `i` is final after stage `i`: the later stages do not change it. -/
theorem gemStage_apply_of_le {k k' : ℕ} {i : Fin N} (hi : (i : ℕ) ≤ k) (hk : k ≤ k') (j : Fin N) :
    gemStage A k' i j = gemStage A k i j := by
  induction k', hk using Nat.le_induction with
  | base => rfl
  | succ k' hk ih => rw [gemStage_succ_apply_of_le A (hi.trans hk), ih]

/-- The shape of `A^{(k)}` in [quarteroni2000numerical] (3.29): if the pivots of the stages before
`k` are nonzero, then stage `k` vanishes below the diagonal in the first `k` columns. -/
theorem gemStage_apply_eq_zero_of_lt {k : ℕ}
    (hpiv : ∀ (m : ℕ) (hm : m < N), m < k → m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0)
    {i j : Fin N} (hjk : (j : ℕ) < k) (hji : j < i) : gemStage A k i j = 0 := by
  induction k generalizing i j with
  | zero => exact absurd hjk (Nat.not_lt_zero _)
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hjk | hjk
    · have ih' : ∀ {i j : Fin N}, (j : ℕ) < k → j < i → gemStage A k i j = 0 :=
        ih fun m hm hmk => hpiv m hm (hmk.trans (Nat.lt_succ_self k))
      by_cases hkN : k < N
      · rw [gemStage_succ_of_lt A hkN,
          elimStep_apply_of_pivot_row_eq_zero _ _ _ (ih' hjk (Fin.mk_lt_of_lt_val hjk))]
        exact ih' hjk hji
      · rw [gemStage_succ_of_le A (not_lt.1 hkN)]
        exact ih' hjk hji
    · subst hjk
      rw [gemStage_succ_of_lt A j.2]
      exact elimStep_apply_pivot _ hji (hpiv j j.2 (Nat.lt_succ_self _)
        (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Fin.lt_def.1 hji)) i.2))

/-- The multiplier matrix of Gaussian elimination, [quarteroni2000numerical] (3.37): unit lower
triangular, with the multiplier `m_ij = a_ij^{(j)} / a_jj^{(j)}` produced at stage `j` in position
`(i, j)` below the diagonal. -/
noncomputable def gemLower : Matrix (Fin N) (Fin N) K :=
  of fun i j => if j < i then gemStage A j i j / gemStage A j j j else if i = j then 1 else 0

/-- The multiplier matrix is unit lower triangular. -/
theorem isUnitLowerTriangular_gemLower : (gemLower A).IsUnitLowerTriangular := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [gemLower, hij'.not_gt, hij'.ne]
  · simp [gemLower]

/-- The partial multiplier matrix after `k` stages: the multipliers of the columns `j < k`. -/
noncomputable def gemLowerStage (k : ℕ) : Matrix (Fin N) (Fin N) K :=
  of fun i j =>
    if j < i ∧ (j : ℕ) < k then gemStage A j i j / gemStage A j j j else if i = j then 1 else 0

/-- Before the first stage, the partial multiplier matrix is the identity. -/
theorem gemLowerStage_zero : gemLowerStage A 0 = 1 := by
  ext i j
  simp [gemLowerStage, one_apply]

/-- After all `N` stages, the partial multiplier matrix is the multiplier matrix. -/
theorem gemLowerStage_of_le {k : ℕ} (hk : N ≤ k) : gemLowerStage A k = gemLower A := by
  ext i j
  simp [gemLowerStage, gemLower, j.2.trans_le hk]

/-- One more stage multiplies the partial multiplier matrix by the unipotent factor of the stage:
the new column of multipliers is appended. -/
theorem gemLowerStage_succ {k : ℕ} (h : k < N) :
    gemLowerStage A (k + 1) = gemLowerStage A k * elimMul (gemStage A k) ⟨k, h⟩ := by
  ext i j
  rw [elimMul, Matrix.mul_add, Matrix.mul_one, add_apply, mul_apply]
  rw [Finset.sum_eq_single i (fun r _ hri => ?_) (fun h => absurd (mem_univ i) h)]
  · simp only [gemLowerStage, of_apply, elimMultipliers_apply, lt_irrefl, false_and, ite_false,
      ite_true, one_mul]
    by_cases hj : j = ⟨k, h⟩
    · subst hj
      have : ¬ ((⟨k, h⟩ : Fin N) < i ∧ k < k) := fun h => lt_irrefl _ h.2
      simp only [this, ite_false, and_true]
      split_ifs with h1 h2 h3 <;> simp_all [div_eq_mul_inv]
    · have : ¬ (j : ℕ) = k := fun h' => hj (Fin.ext h')
      simp only [hj, and_false, ite_false, add_zero]
      congr 1
      apply propext
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  · simp only [elimMultipliers_apply]
    split_ifs with hr
    · obtain ⟨hkr, rfl⟩ := hr
      have : ¬ (r < i ∧ (r : ℕ) < k) := fun h' => absurd h'.2 (not_lt.2 (Fin.lt_def.1 hkr).le)
      simp [gemLowerStage, this, Ne.symm hri]
    · rw [mul_zero]

/-- After `k` stages, `A = L_k A^{(k)}` with `L_k` the partial multiplier matrix. -/
theorem gemLowerStage_mul_gemStage (k : ℕ) : gemLowerStage A k * gemStage A k = A := by
  induction k with
  | zero => rw [gemLowerStage_zero, gemStage_zero, Matrix.one_mul]
  | succ k ih =>
    by_cases h : k < N
    · rw [gemLowerStage_succ A h, gemStage_succ_of_lt A h, Matrix.mul_assoc, elimMul_mul_elimStep,
        ih]
    · have hN : N ≤ k := not_lt.1 h
      rw [gemStage_succ_of_le A hN, gemLowerStage_of_le A (hN.trans (Nat.le_succ k)),
        ← gemLowerStage_of_le A hN, ih]

/-- The partial multiplier matrices are unit lower triangular. -/
theorem isUnitLowerTriangular_gemLowerStage (k : ℕ) :
    (gemLowerStage A k).IsUnitLowerTriangular := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [gemLowerStage, hij'.not_gt, hij'.ne]
  · simp [gemLowerStage]

/-- **Gaussian elimination as a factorization method**, [quarteroni2000numerical] §3.3.1 and
(3.37): if the pivots `a_kk^{(k)}`, `k = 0, …, N - 2`, are nonzero, then `A = L U` with `L` the
multiplier matrix and `U = A^{(N)}` the last stage. The last pivot is never used, so it is not
required to be nonzero. -/
theorem isLU_gemLower_gemStage
    (hpiv : ∀ (m : ℕ) (hm : m < N), m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0) :
    IsLU A (gemLower A) (gemStage A N) where
  isUnitLowerTriangular := isUnitLowerTriangular_gemLower A
  isUpperTriangular := fun i j hij =>
    gemStage_apply_eq_zero_of_lt A (fun m hm _ hmN => hpiv m hm hmN) j.2 hij
  mul_eq := by rw [← gemLowerStage_of_le A le_rfl, gemLowerStage_mul_gemStage]

/-- After `k` stages with nonzero pivots, the leading block of order `k + 1` of
`A = L_k A^{(k)}` is an LU factorization of the leading block of `A`: the block of `A^{(k)}` is
already upper triangular. -/
theorem isLU_leadingPrincipalSubmatrix_gemStage {k : ℕ} (hk : k < N)
    (hpiv : ∀ (m : ℕ) (hm : m < N), m < k → m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0) :
    IsLU (A.leadingPrincipalSubmatrix ⟨k, hk⟩)
      ((gemLowerStage A k).leadingPrincipalSubmatrix ⟨k, hk⟩)
      ((gemStage A k).leadingPrincipalSubmatrix ⟨k, hk⟩) where
  isUnitLowerTriangular :=
    ⟨(isUnitLowerTriangular_gemLowerStage A k).isLowerTriangular.submatrix,
     fun i => (isUnitLowerTriangular_gemLowerStage A k).diag_eq_one i.1⟩
  isUpperTriangular := fun i j hij =>
    gemStage_apply_eq_zero_of_lt A hpiv (Fin.lt_def.1 ((Subtype.coe_lt_coe.2 hij).trans_le i.2))
      (Subtype.coe_lt_coe.2 hij)
  mul_eq := by
    conv_rhs => rw [← gemLowerStage_mul_gemStage A k]
    unfold leadingPrincipalSubmatrix
    rw [toBlock_mul_eq_add' _ (· ≤ ⟨k, hk⟩),
      (isUnitLowerTriangular_gemLowerStage A k).isLowerTriangular.toBlock_not_eq_zero
        (fun _ _ hi hji => hji.trans hi), Matrix.zero_mul, add_zero]

/-- **The pivots are nonzero iff the strict leading principal submatrices are nonsingular**
([quarteroni2000numerical], the sentence after (3.33)): `a_kk^{(k)} ≠ 0` for `k = 0, …, N - 2`
exactly when every `A(< k)` is a unit. Forwards, `det A(< k) = ∏_{m < k} a_mm^{(m)}`; backwards,
by strong induction, `A = L_k A^{(k)}` restricts to the leading block of order `k + 1`, whose
determinant `∏_{m ≤ k} a_mm^{(m)}` is nonzero. The last pivot `a_{N-1,N-1}^{(N-1)}` is excluded on
both sides, and must be: it is `det A / det A(< N - 1)`, which vanishes for a singular `A`, as for
`B = !![1, 2; 1, 2]` of [quarteroni2000numerical] Example 3.3, whose strict leading principal
submatrices are units and whose last pivot is `0`. -/
theorem gemStage_pivots_ne_zero_iff :
    (∀ (m : ℕ) (hm : m < N), m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0) ↔
      ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) := by
  constructor
  · intro hpiv k
    have h := isLU_gemLower_gemStage A hpiv
    rw [isUnit_iff_isUnit_det, h.det_strictLeadingPrincipalSubmatrix, isUnit_iff_ne_zero,
      Finset.prod_ne_zero_iff]
    intro i hi
    have hik : i < k := (mem_filter.1 hi).2
    rw [gemStage_apply_of_le A le_rfl i.2.le]
    exact hpiv i i.2 (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Fin.lt_def.1 hik)) k.2)
  · intro hA m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm hmN
    have hLU := isLU_leadingPrincipalSubmatrix_gemStage A hm
      fun m' hm' hm'm hm'N => ih m' hm'm hm' hm'N
    have hunit : IsUnit (A.leadingPrincipalSubmatrix ⟨m, hm⟩) := by
      have := hA ⟨m + 1, hmN⟩
      unfold strictLeadingPrincipalSubmatrix at this
      unfold leadingPrincipalSubmatrix
      exact (isUnit_toBlock_congr A fun i => by simp [Fin.lt_def, Fin.le_def]).1 this
    have hdet : (∏ i, (gemStage A m).leadingPrincipalSubmatrix ⟨m, hm⟩ i i) ≠ 0 := by
      rw [← hLU.det_eq_prod_diag]
      exact isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 hunit)
    rw [Finset.prod_ne_zero_iff] at hdet
    exact hdet ⟨⟨m, hm⟩, le_rfl⟩ (mem_univ _)

end Stages

/-! ### Restriction to a block of indices

Elimination is local: the formula for the entry `(i, j)` of one step uses only the entries
`(i, j)`, `(i, p)`, `(p, p)` and `(p, j)`, so it commutes with the restriction to any subset of
the indices carried by an order embedding, and with any permutation of the columns fixing the
pivot. For the consecutive block `k, …, k + j - 1` of `Matrix.blockEmb` this says that the
elimination of a trailing block of `A^{(k)}` is the restriction of the global elimination. -/

/-- One step of elimination commutes with a permutation of the columns that fixes the pivot. -/
theorem elimStep_submatrix_id_of_apply_self {m : Type*} [LinearOrder m] [Fintype m]
    (M : Matrix m m K) {p : m} {ρ : Equiv.Perm m} (hρ : ρ p = p) :
    elimStep (M.submatrix id ρ) p = (elimStep M p).submatrix id ρ := by
  ext i j
  simp only [elimStep_apply, submatrix_apply, id, hρ]

/-- The order embedding `Fin j ↪o Fin N`, `i ↦ k + i`, of a block of `j` consecutive indices
starting at `k`. -/
def blockEmb (k j N : ℕ) (h : k + j ≤ N) : Fin j ↪o Fin N :=
  OrderEmbedding.ofStrictMono (fun i => ⟨k + i, by have := i.isLt; omega⟩)
    (fun a b hab => by simp only [Fin.lt_def] at hab ⊢; omega)

/-- The value of `Matrix.blockEmb`. -/
@[simp]
theorem blockEmb_apply {k j N : ℕ} (h : k + j ≤ N) (i : Fin j) (hki : k + (i : ℕ) < N) :
    blockEmb k j N h i = ⟨k + (i : ℕ), hki⟩ := rfl

/-- One step of elimination commutes with the restriction to a subset of the indices carried by
an order embedding: the formula for the entry `(i, j)` uses only the entries `(i, j)`, `(i, p)`,
`(p, p)` and `(p, j)`, all inside the block. -/
theorem elimStep_submatrix_orderEmbedding {m n K : Type*} [LinearOrder m] [Fintype m]
    [LinearOrder n] [Fintype n] [Field K] (M : Matrix n n K) (e : m ↪o n) (p : m) :
    elimStep (M.submatrix e e) p = (elimStep M (e p)).submatrix e e := by
  ext i j
  simp only [elimStep_apply, submatrix_apply, e.lt_iff_lt]

/-- **Gaussian elimination on a trailing block is the restriction of the global elimination**:
the `t`-th stage of the elimination of the block of `A^{(k)}` on the indices `k, …, k + j - 1` is
the block of `A^{(k + t)}` on the same indices, for `t ≤ j`. -/
theorem gemStage_submatrix_blockEmb {K : Type*} [Field K] {N : ℕ} (A : Matrix (Fin N) (Fin N) K)
    {k j : ℕ} (h : k + j ≤ N) :
    ∀ t ≤ j, gemStage ((gemStage A k).submatrix (blockEmb k j N h) (blockEmb k j N h)) t =
      (gemStage A (k + t)).submatrix (blockEmb k j N h) (blockEmb k j N h) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have htj : t < j := by omega
    have hkt : k + t < N := by omega
    rw [gemStage_succ_of_lt _ htj, ih (by omega), elimStep_submatrix_orderEmbedding]
    have he : blockEmb k j N h ⟨t, htj⟩ = (⟨k + t, hkt⟩ : Fin N) := rfl
    rw [he, ← gemStage_succ_of_lt A hkt, Nat.add_assoc]

/-! ### The Doolittle recurrence -/

/-- A smaller strict initial segment has fewer elements. -/
theorem card_filter_lt_lt_of_lt {a b : n} (h : a < b) : #{k | k < a} < #{k | k < b} := by
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun k hk => ?_) |>.2 ⟨a, ?_, ?_⟩)
  · simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · simp [h]
  · simp

/-- The Doolittle recurrence, [quarteroni2000numerical] (3.43), as one total function on a finite
linear order, in packed form: `luPacked A i j = A i j - ∑_{r < i} luPacked A i r * luPacked A r j`
for `i ≤ j` (the entry `u_ij` of the upper factor) and
`luPacked A i j = (A i j - ∑_{r < j} luPacked A i r * luPacked A r j) / luPacked A j j` for `j < i`
(the entry `l_ij` of the unit lower factor). The recursion is well founded on the number of
indices below `min i j`, the `l` entries after the `u` entries at the same level; a zero pivot
gives junk (`x / 0 = 0`) rather than a hypothesis, and `Matrix.isLU_luLower_luUpper` says when
the result is right. -/
noncomputable def luPacked (A : Matrix n n K) : n → n → K
  | i, j =>
    if j < i then
      (A i j - ∑ r ∈ (univ.filter (· < j)).attach, luPacked A i r * luPacked A r j) /
        luPacked A j j
    else A i j - ∑ r ∈ (univ.filter (· < i)).attach, luPacked A i r * luPacked A r j
termination_by i j => (#{k | k < min i j}, if j < i then 1 else 0)
decreasing_by
  · have hr : (r : n) < j := (mem_filter.1 r.2).2
    rw [min_eq_right (hr.trans ‹j < i›).le, min_eq_right ‹j < i›.le]
    exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr)
  · have hr : (r : n) < j := (mem_filter.1 r.2).2
    rw [min_eq_left hr.le, min_eq_right ‹j < i›.le]
    exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr)
  · rw [min_self, min_eq_right ‹j < i›.le]
    exact Prod.Lex.right _ (by simp [‹j < i›])
  · have hr : (r : n) < i := (mem_filter.1 r.2).2
    rw [min_eq_right hr.le, min_eq_left (not_lt.1 ‹¬ j < i›)]
    exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr)
  · have hr : (r : n) < i := (mem_filter.1 r.2).2
    rw [min_eq_left (hr.le.trans (not_lt.1 ‹¬ j < i›)), min_eq_left (not_lt.1 ‹¬ j < i›)]
    exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr)

section Doolittle

variable (A : Matrix n n K)

/-- The Doolittle recurrence for the entries of the upper factor. -/
theorem luPacked_of_le {i j : n} (hij : i ≤ j) :
    luPacked A i j = A i j - ∑ r ∈ univ.filter (· < i), luPacked A i r * luPacked A r j := by
  rw [luPacked, ite_eq_right (not_lt.2 hij),
    Finset.sum_attach (univ.filter (· < i)) fun r => luPacked A i r * luPacked A r j]

/-- The Doolittle recurrence for the entries of the lower factor. -/
theorem luPacked_of_lt {i j : n} (hij : j < i) :
    luPacked A i j =
      (A i j - ∑ r ∈ univ.filter (· < j), luPacked A i r * luPacked A r j) / luPacked A j j := by
  rw [luPacked, ite_eq_left hij,
    Finset.sum_attach (univ.filter (· < j)) fun r => luPacked A i r * luPacked A r j]

/-- The unit lower factor read off the packed Doolittle recurrence. -/
noncomputable def luLower : Matrix n n K :=
  of fun i j => if j < i then luPacked A i j else if i = j then 1 else 0

/-- The upper factor read off the packed Doolittle recurrence. -/
noncomputable def luUpper : Matrix n n K :=
  of fun i j => if i ≤ j then luPacked A i j else 0

/-- **Correctness of the Doolittle recurrence** ([quarteroni2000numerical] (3.43)): when the strict
leading principal submatrices are nonsingular, the packed recurrence computes the (unique) LU
factorization. The recurrence equations are exactly the entrywise identities
`Matrix.IsLU.upper_apply_eq` and `Matrix.IsLU.lower_apply_mul_diag_eq` satisfied by any LU
factorization, so the packed entries agree with the factors of
`Matrix.exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix` by strong induction along
the order of `min i j`. -/
theorem luPacked_eq {L U : Matrix n n K} (h : IsLU A L U)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) (m : n) :
    ∀ i j, min i j = m → (i ≤ j → luPacked A i j = U i j) ∧ (j < i → luPacked A i j = L i j) := by
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  have hU : ∀ i j, min i j = m → i ≤ j → luPacked A i j = U i j := by
    intro i j hm hij
    rw [luPacked_of_le A hij, h.upper_apply_eq hij]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := (mem_filter.1 hr).2
    have hrm : r < m := by rw [← hm, min_eq_left hij]; exact hr'
    rw [(ih r hrm i r (min_eq_right hr'.le)).2 hr',
      (ih r hrm r j (min_eq_left (hr'.le.trans hij))).1 (hr'.le.trans hij)]
  refine fun i j hm => ⟨hU i j hm, fun hij => ?_⟩
  have hjm : j = m := (min_eq_right hij.le).symm.trans hm
  rw [luPacked_of_lt A hij, hU j j (by rw [min_self]; exact hjm) le_rfl,
    div_eq_iff (h.diag_upper_ne_zero_of_lt (hA i) hij), h.lower_apply_mul_diag_eq hij]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := (mem_filter.1 hr).2
  have hrm : r < m := hjm ▸ hr'
  rw [(ih r hrm i r (min_eq_right (hr'.trans hij).le)).2 (hr'.trans hij),
    (ih r hrm r j (min_eq_left hr'.le)).1 hr'.le]

/-- **Correctness of the Doolittle factorization**: with nonsingular strict leading principal
submatrices, `A = luLower A * luUpper A` is the LU factorization of `A`. -/
theorem isLU_luLower_luUpper (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    IsLU A (luLower A) (luUpper A) := by
  obtain ⟨L, U, h⟩ := exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix hA
  have hL : luLower A = L := by
    ext i j
    simp only [luLower, of_apply]
    split_ifs with hij hij'
    · exact (luPacked_eq A h hA _ i j rfl).2 hij
    · subst hij'
      exact (h.isUnitLowerTriangular.diag_eq_one i).symm
    · exact (h.isUnitLowerTriangular.isLowerTriangular (OrderDual.toDual_lt_toDual.2
        (lt_of_le_of_ne (not_lt.1 hij) hij'))).symm
  have hU : luUpper A = U := by
    ext i j
    simp only [luUpper, of_apply]
    split_ifs with hij
    · exact (luPacked_eq A h hA _ i j rfl).1 hij
    · exact (h.isUpperTriangular (not_le.1 hij)).symm
  rw [hL, hU]
  exact h

end Doolittle

/-- **Every loop order computes the same factors** ([quarteroni2000numerical] §3.3.4, "the
Doolittle factorization is nothing but the `ijk` version of GEM"): on `Fin N` with nonzero
pivots, the Doolittle factors are the Gaussian elimination factors, by uniqueness of the LU
factorization. -/
theorem luLower_eq_gemLower {N : ℕ} (A : Matrix (Fin N) (Fin N) K)
    (hpiv : ∀ (m : ℕ) (hm : m < N), m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0) :
    luLower A = gemLower A ∧ luUpper A = gemStage A N :=
  (isLU_luLower_luUpper A ((gemStage_pivots_ne_zero_iff A).1 hpiv)).unique
    (isLU_gemLower_gemStage A hpiv) ((gemStage_pivots_ne_zero_iff A).1 hpiv)

/-! ### The Crout factorization -/

section Crout

variable (A : Matrix n n K)

/-- The lower factor of the Crout factorization ([quarteroni2000numerical] §3.3.4, `u_kk = 1`):
Doolittle applied to the transpose, transposed back. -/
noncomputable def croutLower : Matrix n n K := (luUpper Aᵀ)ᵀ

/-- The unit upper factor of the Crout factorization: Doolittle applied to the transpose,
transposed back. -/
noncomputable def croutUpper : Matrix n n K := (luLower Aᵀ)ᵀ

/-- **The Crout factorization**: with nonsingular strict leading principal submatrices,
`A = croutLower A * croutUpper A` with `croutLower A` lower triangular and `croutUpper A` unit
upper triangular. -/
theorem croutLower_mul_croutUpper (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    croutLower A * croutUpper A = A ∧ (croutLower A).IsLowerTriangular ∧
      (croutUpper A)ᵀ.IsUnitLowerTriangular := by
  have hAT : ∀ k, IsUnit (Aᵀ.strictLeadingPrincipalSubmatrix k) := fun k => by
    rw [strictLeadingPrincipalSubmatrix_transpose, isUnit_transpose]
    exact hA k
  have h := isLU_luLower_luUpper Aᵀ hAT
  refine ⟨?_, h.isUpperTriangular.transpose, ?_⟩
  · rw [croutLower, croutUpper, ← transpose_mul, h.mul_eq, transpose_transpose]
  · rw [croutUpper, transpose_transpose]
    exact h.isUnitLowerTriangular

end Crout

end Matrix
