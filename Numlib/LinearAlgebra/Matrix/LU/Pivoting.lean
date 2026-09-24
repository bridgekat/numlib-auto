/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LU`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Numlib.LinearAlgebra.Matrix.LU.Elimination
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Pivoting and the growth factor of Gaussian elimination

Pivoting, at two levels. The *specification* level says what pivoting achieves: every square
matrix over a normed field has a row permutation `σ` with `P A = L U`, `P` the permutation matrix
of `σ`, and all multipliers of modulus at most one — partial pivoting,
[quarteroni2000numerical] (3.52) — and a row and a column permutation with `P A Q = L U` whose
upper factor is dominated by its diagonal — complete pivoting, [quarteroni2000numerical] §3.5.
Neither needs nonsingularity: a zero pivot column is skipped with a zero column of multipliers.
The *algorithm* level is the stage recurrence of Gaussian elimination
(`Numlib/LinearAlgebra/Matrix/LU/Elimination`) with a pivot-row choice inserted before each step:
`Matrix.gemPivotStage A piv k` runs `k` stages with an arbitrary strategy `piv`, returning the
current matrix and the accumulated row permutation, and `Matrix.partialPivotRow` (the first row of
maximal modulus in the current column) is the strategy of Gaussian elimination with partial
pivoting. `Matrix.gemFullPivotStage A piv k` is its two-sided counterpart, interchanging rows *and*
columns for a strategy choosing a pair of indices, with `Matrix.completePivotEntry` the strategy of
complete pivoting.

The growth factor `ρ_N = max_{i,j,k} |a^{(k)}_{ij}| / max_{i,j} |a_{ij}|`
([quarteroni2000numerical] (3.66)) is defined on the *exact* stages and over `ℝ`; the book
defines it on the computed stages, and [higham2002accuracy] (after Theorem 9.5) explains why the
exact one is the one that can be bounded. Of the bounds of [quarteroni2000numerical] §3.10, this
module proves `2^{N-1}` under bounded multipliers (hence for partial pivoting), `1` for symmetric
positive definite matrices, `2` for column diagonally dominant matrices, `2` for tridiagonal,
`N` for upper Hessenberg, `2^{p+q}` for banded matrices of lower bandwidth `p` and upper
bandwidth `q` under partial pivoting, and Wilkinson's
`N^{1/2} (2 · 3^{1/2} ⋯ N^{1/(N-1)})^{1/2}` for complete pivoting.

**Bohte's band bound is not here.** [quarteroni2000numerical] §3.10 (1) and
[higham2002accuracy] Theorem 9.11 state that a matrix whose upper and lower bandwidths are both
`p` has `ρ_n ≤ 2^{2p-1} - (p-1) 2^{p-2}` under partial pivoting. What this module proves instead
is `Matrix.growthFactor_le_two_pow_of_hasBandwidth`, `ρ_N ≤ 2^{p+q}` for lower bandwidth `p` and
upper bandwidth `q`; that carries the content of the book's item — the growth factor of a banded
matrix is bounded independently of the order — and `Matrix.growthFactor_le_two_of_isTridiagonal`
gives the book's tridiagonal consequence `2` sharply. Bohte's constant is about a factor two
better at `p = q`, and no proof of it is available: the book states it without one, and
[higham2002accuracy] refers to Z. Bohte, *Bounds for rounding errors in the Gaussian elimination
for band systems*, J. Inst. Maths. Applics. 16 (1975), 133–142, which is not among the project's
references; Problem 9.15 there records the sharp bound for `p ≠ q` as an open research problem.
Reaching the printed constant would need Bohte's finer analysis of how the entries of one band row
grow along a sweep — a second-order recursion in the pair (column offset, number of updates) in
place of the "each update at most doubles the column" counting used here — and the constant itself
could not be checked against its source. Nothing in the corpus consumes it, so it is not tracked.

## Main definitions

* `Matrix.IsPartialPivot`, `Matrix.partialPivotRow M k`: choosing a row `r ≥ k` maximizing
  `‖M r k‖`, the strategy of partial pivoting, with `Matrix.partialPivotRow` the first such row.
* `Matrix.IsCompletePivot`, `Matrix.completePivotEntry M k`: choosing an entry of maximal modulus
  in the trailing block from `k` on, the strategy of complete pivoting.
* `Matrix.gemPivotStage A piv k`: `k` stages of Gaussian elimination with the pivoting strategy
  `piv`, as a pair (current matrix, accumulated row permutation).
* `Matrix.gemFullPivotStage A piv k`: the same for a strategy choosing an entry, as a triple
  (current matrix, accumulated row permutation, accumulated column permutation).
* `Matrix.supAbs A`: the largest absolute value of an entry of a real matrix, and
  `Matrix.growthFactor A`: the growth factor of Gaussian elimination without pivoting on `A`.
* `Matrix.HasDominantPivots A`: every stage of the elimination has its pivot dominating the
  trailing block, with `Matrix.absGemPivot A k` the modulus of the `k`-th pivot.
* `Matrix.wilkinsonGrowthBound N`: `N^{1/2} (2 · 3^{1/2} ⋯ N^{1/(N-1)})^{1/2}`.

## Main results

* `Matrix.exists_permMatrix_mul_isLU`: `P A = L U` with `‖L i j‖ ≤ 1`, for every square matrix.
* `Matrix.exists_permMatrix_mul_mul_permMatrix_isLU`: `P A Q = L U` with `‖L i j‖ ≤ 1` and
  `‖U i j‖ ≤ ‖U i i‖`.
* `Matrix.gemStage_permMatrix_mul_eq_submatrix_gemPivotStage`: the stages of Gaussian elimination
  on `P A` are the pivoted stages with their rows permuted by the *later* interchanges; hence
  `Matrix.gemPivotStage_permMatrix_mul_isLU`, the factorization `P A = L U` computed by the
  recurrence, and `Matrix.gemPivotStage_partialPivotRow_norm_gemLower_le_one`, the bound on the
  multipliers of partial pivoting.
* `Matrix.growthFactor_le_two_pow`, `Matrix.growthFactor_eq_one_of_posDef`,
  `Matrix.growthFactor_le_two_of_isColDiagDominant`, `Matrix.growthFactor_le_two_of_isTridiagonal`,
  `Matrix.growthFactor_le_card_of_isUpperHessenberg`,
  `Matrix.growthFactor_le_two_pow_of_hasBandwidth`.
* `Matrix.gemStage_submatrix_eq_submatrix_gemFullPivotStage`: the two-sided analogue for complete
  pivoting, whence `Matrix.hasDominantPivots_submatrix_gemFullPivotStage`, the stage dominance
  that complete pivoting buys.
* `Matrix.growthFactor_le_of_completePivoting` and its algorithmic form
  `Matrix.growthFactor_le_wilkinson_of_isCompletePivot`: **Wilkinson's bound**, by Hadamard's
  determinant inequality (`Matrix.norm_det_le_of_forall_norm_le`) on the leading blocks of the
  reduced matrices and a telescoping induction over the pivots.

## Implementation notes

A row permutation is applied as `A.submatrix σ id`, whose entries are `A (σ i) j` by definition;
the permutation-matrix form `σ.permMatrix K * A` of the statements is the same matrix by
`PEquiv.toMatrix_toPEquiv_mul`. The existence proofs are the strong induction on the number of
indices of `Numlib/LinearAlgebra/Matrix/LU` (`Matrix.isLU_luLowerOfSchur_luUpperOfSchur`), with
the pivot moved to the first index by a transposition and the permutation of the trailing block
extended by `Equiv.Perm.ofSubtype`. The recurrence is on `Fin N`, as `Matrix.gemStage` is; the
accumulated permutation is `σ_{k+1} = σ_k * swap k r_k`, so that its permutation matrix is
`P_k ⋯ P_1` and the interchanges *after* stage `k`, `σ_k⁻¹ σ_N`, fix the indices below `k`. The
complete-pivoting recurrence carries a second permutation with the same bookkeeping, and the only
new geometric fact is that an elimination step commutes with a permutation of the *columns* that
fixes the pivot (`Matrix.elimStep_submatrix_id_of_apply_self`).

## References

* [quarteroni2000numerical] §3.5, §3.10.
* [higham2002accuracy] §9.3–9.5, (9.14) (Wilkinson's complete-pivoting bound) and
  Theorem 9.11 (Bohte).
-/

open Finset

universe u

namespace Matrix

/-! ### Row and column permutations of a one-step Schur complement -/

section Perm

variable {n : Type*} {K : Type*} [Field K]

/-- The one-step Schur complement at `p` commutes with a permutation of the rows and of the
columns that fixes `p`, the permutation restricting to the indices other than `p`. -/
theorem schurComplementSingle_submatrix_ofSubtype [DecidableEq n] (A : Matrix n n K) (p : n)
    (σ ρ : Equiv.Perm {i : n // i ≠ p}) :
    (A.submatrix (Equiv.Perm.ofSubtype σ) (Equiv.Perm.ofSubtype ρ)).schurComplementSingle p =
      (A.schurComplementSingle p).submatrix σ ρ := by
  ext i j
  simp only [schurComplementSingle_apply, submatrix_apply, Equiv.Perm.ofSubtype_apply_coe,
    Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun i => i ≠ p) _ (not_not.2 rfl)]

/-- A permutation extended from the indices other than `p` fixes `p`. -/
theorem ofSubtype_ne_apply_self [DecidableEq n] (p : n) (σ : Equiv.Perm {i : n // i ≠ p}) :
    Equiv.Perm.ofSubtype σ p = p :=
  Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun i => i ≠ p) _ (not_not.2 rfl)

variable [LinearOrder n] [Fintype n]

/-- `Matrix.isLU_luLowerOfSchur_luUpperOfSchur` with a zero pivot allowed when its whole column
vanishes: the multipliers `a_ip / a_pp` are then `0` (junk division), and the bordered
factorization is still one. This is what lets pivoting skip a zero column. -/
theorem isLU_luLowerOfSchur_luUpperOfSchur' {A : Matrix n n K} {p : n} (hp : ∀ i, p ≤ i)
    (hpp : A p p = 0 → ∀ i, A i p = 0) {L' U' : Matrix {i // i ≠ p} {i // i ≠ p} K}
    (h : IsLU (A.schurComplementSingle p) L' U') :
    IsLU A (luLowerOfSchur A p L') (luUpperOfSchur A p U') := by
  rcases eq_or_ne (A p p) 0 with h0 | h0
  swap
  · exact isLU_luLowerOfSchur_luUpperOfSchur hp h0 h
  have hcol := hpp h0
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp only [luLowerOfSchur, of_apply]
    split_ifs with hi hj hj
    · exact absurd (hj ▸ hij') (hi ▸ lt_irrefl _)
    · rfl
    · exact absurd (hj ▸ hij') (not_lt.2 (hp i))
    · exact h.isUnitLowerTriangular.isLowerTriangular
        (OrderDual.toDual_lt_toDual.2 (Subtype.mk_lt_mk.2 hij'))
  · simp only [luLowerOfSchur, of_apply]
    split_ifs with hi
    · rfl
    · exact h.isUnitLowerTriangular.diag_eq_one _
  · simp only [luUpperOfSchur, of_apply]
    split_ifs with hi hj
    · exact absurd (hi ▸ hij) (not_lt.2 (hp j))
    · rfl
    · exact h.isUpperTriangular (Subtype.mk_lt_mk.2 hij)
  · have hLpp : luLowerOfSchur A p L' p p = 1 := by simp [luLowerOfSchur]
    have hLpx : ∀ x : {x // x ≠ p}, luLowerOfSchur A p L' p x = 0 := fun x => by
      simp [luLowerOfSchur, x.2]
    have hLxp : ∀ i, i ≠ p → luLowerOfSchur A p L' i p = A i p / A p p := fun i hi => by
      simp [luLowerOfSchur, hi]
    have hLxx : ∀ i (hi : i ≠ p) (x : {x // x ≠ p}), luLowerOfSchur A p L' i x = L' ⟨i, hi⟩ x :=
      fun i hi x => by simp [luLowerOfSchur, hi, x.2]
    have hUpj : ∀ j, luUpperOfSchur A p U' p j = A p j := fun j => by simp [luUpperOfSchur]
    have hUxp : ∀ x : {x // x ≠ p}, luUpperOfSchur A p U' x p = 0 := fun x => by
      simp [luUpperOfSchur, x.2]
    have hUxj : ∀ (x : {x // x ≠ p}) j (hj : j ≠ p), luUpperOfSchur A p U' x j = U' x ⟨j, hj⟩ :=
      fun x j hj => by simp [luUpperOfSchur, x.2, hj]
    ext i j
    rw [mul_apply, sum_eq_add_sum_subtype_ne p]
    rcases eq_or_ne i p with hi | hi
    · subst hi
      simp [hLpp, hLpx, hUpj]
    rcases eq_or_ne j p with hj | hj
    · subst hj
      simp [hLxp i hi, hUpj, hUxp, hcol]
    have hS := congrFun (congrFun h.mul_eq ⟨i, hi⟩) ⟨j, hj⟩
    rw [mul_apply, schurComplementSingle_apply] at hS
    simp only [hLxp i hi, hUpj, hLxx i hi, hUxj _ j hj]
    rw [hS, div_eq_mul_inv]
    ring

end Perm

/-! ### Existence of `P A = L U` and `P A Q = L U` -/

section Existence

variable {n : Type u} [LinearOrder n] {𝕜 : Type*} [NormedField 𝕜]

/-- The bordered lower factor is bounded by `1` when the pivot dominates its column and the
lower factor of the trailing block is bounded by `1`. -/
theorem norm_luLowerOfSchur_apply_le_one {A : Matrix n n 𝕜} {p : n}
    (hpiv : ∀ i, ‖A i p‖ ≤ ‖A p p‖) {L' : Matrix {i // i ≠ p} {i // i ≠ p} 𝕜}
    (hL' : ∀ i j, ‖L' i j‖ ≤ 1) (i j : n) : ‖luLowerOfSchur A p L' i j‖ ≤ 1 := by
  simp only [luLowerOfSchur, of_apply]
  split_ifs with hi hj hj
  · simp
  · simp
  · rcases eq_or_ne (A p p) 0 with h0 | h0
    · simp [h0]
    · rw [norm_div, div_le_one (norm_pos_iff.2 h0)]
      exact hpiv i
  · exact hL' _ _

/-- The bordered upper factor is dominated by its diagonal when the pivot dominates its row and
the upper factor of the trailing block is dominated by its diagonal. -/
theorem norm_luUpperOfSchur_apply_le {A : Matrix n n 𝕜} {p : n}
    (hpiv : ∀ j, ‖A p j‖ ≤ ‖A p p‖) {U' : Matrix {i // i ≠ p} {i // i ≠ p} 𝕜}
    (hU' : ∀ i j, ‖U' i j‖ ≤ ‖U' i i‖) (i j : n) :
    ‖luUpperOfSchur A p U' i j‖ ≤ ‖luUpperOfSchur A p U' i i‖ := by
  simp only [luUpperOfSchur, of_apply]
  rcases eq_or_ne i p with rfl | hi
  · simpa using hpiv j
  · simp only [hi, dite_false]
    rcases eq_or_ne j p with rfl | hj
    · simp
    · simpa [hj] using hU' ⟨i, hi⟩ ⟨j, hj⟩

variable [Fintype n]

omit [LinearOrder n] [Fintype n] in
/-- **Partial pivoting**, by strong induction on the number of indices: a row of maximal
modulus in the first column is moved to the first index by a transposition, one step of
elimination is taken, and the permutation of the trailing block is extended by
`Equiv.Perm.ofSubtype`. -/
theorem exists_submatrix_isLU_of_card (N : ℕ) :
    ∀ {n : Type u} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜), Fintype.card n = N →
      ∃ (σ : Equiv.Perm n) (L U : Matrix n n 𝕜), IsLU (A.submatrix σ id) L U ∧
        ∀ i j, ‖L i j‖ ≤ 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n _ _ A hN
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, 1, ⟨isUnitLowerTriangular_one, blockTriangular_one,
      Matrix.ext fun i => isEmptyElim i⟩, fun i => isEmptyElim i⟩
  set p := univ.min' (univ_nonempty : (univ : Finset n).Nonempty)
  have hp : ∀ i, p ≤ i := fun i => min'_le _ _ (mem_univ i)
  obtain ⟨r, -, hr⟩ := Finset.exists_max_image univ (fun r => ‖A r p‖) univ_nonempty
  set A' := A.submatrix (Equiv.swap p r) id with hA'
  have hpiv : ∀ i, ‖A' i p‖ ≤ ‖A' p p‖ := fun i => by
    simp only [hA', submatrix_apply, id, Equiv.swap_apply_left]
    exact hr _ (mem_univ _)
  have hcard : Fintype.card {i // i ≠ p} < N :=
    hN ▸ Fintype.card_subtype_lt (x := p) (not_not.2 rfl)
  obtain ⟨σ', L', U', h', hL'⟩ := ih _ hcard (A'.schurComplementSingle p) rfl
  set A'' := A'.submatrix (Equiv.Perm.ofSubtype σ') id with hA''
  have hA''p : ∀ i, ‖A'' i p‖ ≤ ‖A'' p p‖ := fun i => by
    simp only [hA'', submatrix_apply, id, ofSubtype_ne_apply_self]
    exact hpiv _
  have hS : A''.schurComplementSingle p = (A'.schurComplementSingle p).submatrix σ' id := by
    simpa using schurComplementSingle_submatrix_ofSubtype A' p σ' 1
  refine ⟨Equiv.swap p r * Equiv.Perm.ofSubtype σ', luLowerOfSchur A'' p L',
    luUpperOfSchur A'' p U', ?_, norm_luLowerOfSchur_apply_le_one hA''p hL'⟩
  have : A.submatrix (Equiv.swap p r * Equiv.Perm.ofSubtype σ') id = A'' := by
    rw [hA'', hA', submatrix_submatrix]
    rfl
  rw [this]
  refine isLU_luLowerOfSchur_luUpperOfSchur' hp (fun h0 i => ?_) (by rwa [hS])
  have := hA''p i
  rw [h0, norm_zero] at this
  exact norm_le_zero_iff.1 this

omit [LinearOrder n] [Fintype n] in
/-- **Complete pivoting**, by the same induction with the pivot chosen in the whole matrix. -/
theorem exists_submatrix_submatrix_isLU_of_card (N : ℕ) :
    ∀ {n : Type u} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜), Fintype.card n = N →
      ∃ (σ ρ : Equiv.Perm n) (L U : Matrix n n 𝕜), IsLU (A.submatrix σ ρ) L U ∧
        (∀ i j, ‖L i j‖ ≤ 1) ∧ ∀ i j, ‖U i j‖ ≤ ‖U i i‖ := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n _ _ A hN
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, 1, 1, ⟨isUnitLowerTriangular_one, blockTriangular_one,
      Matrix.ext fun i => isEmptyElim i⟩, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  set p := univ.min' (univ_nonempty : (univ : Finset n).Nonempty)
  have hp : ∀ i, p ≤ i := fun i => min'_le _ _ (mem_univ i)
  obtain ⟨⟨q, r⟩, -, hqr⟩ :=
    Finset.exists_max_image univ (fun qr : n × n => ‖A qr.1 qr.2‖) univ_nonempty
  set A' := A.submatrix (Equiv.swap p q) (Equiv.swap p r) with hA'
  have hpiv : ∀ i j, ‖A' i j‖ ≤ ‖A' p p‖ := fun i j => by
    simp only [hA', submatrix_apply, Equiv.swap_apply_left]
    exact hqr (Equiv.swap p q i, Equiv.swap p r j) (mem_univ _)
  have hcard : Fintype.card {i // i ≠ p} < N :=
    hN ▸ Fintype.card_subtype_lt (x := p) (not_not.2 rfl)
  obtain ⟨σ', ρ', L', U', h', hL', hU'⟩ := ih _ hcard (A'.schurComplementSingle p) rfl
  set A'' := A'.submatrix (Equiv.Perm.ofSubtype σ') (Equiv.Perm.ofSubtype ρ') with hA''
  have hA''pp : ∀ i j, ‖A'' i j‖ ≤ ‖A'' p p‖ := fun i j => by
    simp only [hA'', submatrix_apply, ofSubtype_ne_apply_self]
    exact hpiv _ _
  have hS : A''.schurComplementSingle p = (A'.schurComplementSingle p).submatrix σ' ρ' :=
    schurComplementSingle_submatrix_ofSubtype A' p σ' ρ'
  refine ⟨Equiv.swap p q * Equiv.Perm.ofSubtype σ', Equiv.swap p r * Equiv.Perm.ofSubtype ρ',
    luLowerOfSchur A'' p L', luUpperOfSchur A'' p U', ?_,
    norm_luLowerOfSchur_apply_le_one (fun i => hA''pp i p) hL',
    norm_luUpperOfSchur_apply_le (fun j => hA''pp p j) hU'⟩
  have : A.submatrix (Equiv.swap p q * Equiv.Perm.ofSubtype σ')
      (Equiv.swap p r * Equiv.Perm.ofSubtype ρ') = A'' := by
    rw [hA'', hA', submatrix_submatrix]
    rfl
  rw [this]
  refine isLU_luLowerOfSchur_luUpperOfSchur' hp (fun h0 i => ?_) (by rwa [hS])
  have := hA''pp i p
  rw [h0, norm_zero] at this
  exact norm_le_zero_iff.1 this

/-- **Gaussian elimination with partial pivoting exists** ([quarteroni2000numerical] (3.52),
[higham2002accuracy] §9.3): every square matrix over a normed field has a row permutation `σ`
with `P A = L U`, `P = σ.permMatrix 𝕜`, and every multiplier of modulus at most `1`. No
nonsingularity is needed — the book proves (3.52) for nonsingular `A`, but a zero pivot column
is simply skipped, with a zero column of multipliers. -/
theorem exists_permMatrix_mul_isLU (A : Matrix n n 𝕜) :
    ∃ (σ : Equiv.Perm n) (L U : Matrix n n 𝕜),
      IsLU (σ.permMatrix 𝕜 * A) L U ∧ ∀ i j, ‖L i j‖ ≤ 1 := by
  obtain ⟨σ, L, U, h, hL⟩ := exists_submatrix_isLU_of_card _ A rfl
  exact ⟨σ, L, U, by rwa [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul], hL⟩

/-- **Gaussian elimination with complete pivoting exists** ([quarteroni2000numerical] §3.5):
every square matrix has a row permutation `σ` and a column permutation `τ` with
`P A Q = L U`, every multiplier of modulus at most `1`, and every row of `U` dominated by its
diagonal entry — the pivot is the largest entry of the trailing block, which is what complete
pivoting buys over partial pivoting. -/
theorem exists_permMatrix_mul_mul_permMatrix_isLU (A : Matrix n n 𝕜) :
    ∃ (σ τ : Equiv.Perm n) (L U : Matrix n n 𝕜),
      IsLU (σ.permMatrix 𝕜 * A * τ.permMatrix 𝕜) L U ∧ (∀ i j, ‖L i j‖ ≤ 1) ∧
        ∀ i j, ‖U i j‖ ≤ ‖U i i‖ := by
  obtain ⟨σ, ρ, L, U, h, hL, hU⟩ := exists_submatrix_submatrix_isLU_of_card _ A rfl
  refine ⟨σ, ρ⁻¹, L, U, ?_, hL, hU⟩
  rwa [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix, Function.id_comp, Function.comp_id,
    Equiv.Perm.inv_def, Equiv.symm_symm]

end Existence

/-! ### The partial-pivoting strategy -/

section PartialPivot

variable {n : Type*} [LinearOrder n] {𝕜 : Type*} [NormedField 𝕜]

/-- **A partial-pivoting strategy** ([quarteroni2000numerical] §3.5, [golub2013matrix] §3.4.3):
`piv M k` returns a row `r` at or after `k` at which `‖M r k‖` is maximal among the rows from `k`
on. `Matrix.partialPivotRow` is one (`Matrix.isPartialPivot_partialPivotRow`); the interchanges
such a strategy produces are run by `Matrix.gemPivotStage`. The column counterpart of
`Matrix.IsCompletePivot`. -/
def IsPartialPivot (piv : Matrix n n 𝕜 → n → n) : Prop :=
  ∀ (M : Matrix n n 𝕜) (k : n), k ≤ piv M k ∧ ∀ r, k ≤ r → ‖M r k‖ ≤ ‖M (piv M k) k‖

variable [Fintype n]

/-- Some row `r ≥ k` maximizes `‖M r k‖` among the rows `≥ k`. -/
theorem exists_partialPivotRow (M : Matrix n n 𝕜) (k : n) :
    (univ.filter fun r => k ≤ r ∧ ∀ r', k ≤ r' → ‖M r' k‖ ≤ ‖M r k‖).Nonempty := by
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image (univ.filter (k ≤ ·)) (fun r => ‖M r k‖)
    ⟨k, by simp⟩
  refine ⟨r, mem_filter.2 ⟨mem_univ _, (mem_filter.1 hr).2, fun r' hr' => ?_⟩⟩
  exact hmax r' (mem_filter.2 ⟨mem_univ _, hr'⟩)

/-- **The partial-pivoting strategy** ([quarteroni2000numerical] §3.5): `partialPivotRow M k`
is the first row `r ≥ k` at which `‖M r k‖` is maximal among the rows `≥ k`. Taking the *first*
such row makes the choice deterministic and, when the whole column vanishes below `k`, makes it
`k` itself, so that no interchange is performed on a zero pivot column. -/
noncomputable def partialPivotRow (M : Matrix n n 𝕜) (k : n) : n :=
  (univ.filter fun r => k ≤ r ∧ ∀ r', k ≤ r' → ‖M r' k‖ ≤ ‖M r k‖).min'
    (exists_partialPivotRow M k)

variable (M : Matrix n n 𝕜) (k : n)

/-- The membership of the pivot row in the set of maximizing rows. -/
theorem partialPivotRow_mem :
    partialPivotRow M k ∈
      univ.filter fun r => k ≤ r ∧ ∀ r', k ≤ r' → ‖M r' k‖ ≤ ‖M r k‖ :=
  Finset.min'_mem _ _

/-- The pivot row lies at or below the current index. -/
theorem le_partialPivotRow : k ≤ partialPivotRow M k :=
  (mem_filter.1 (partialPivotRow_mem M k)).2.1

/-- The pivot dominates its column below the current index. -/
theorem norm_apply_le_partialPivotRow {r : n} (hr : k ≤ r) :
    ‖M r k‖ ≤ ‖M (partialPivotRow M k) k‖ :=
  (mem_filter.1 (partialPivotRow_mem M k)).2.2 r hr

/-- The pivot row is the *first* maximizing row. -/
theorem partialPivotRow_le {r : n} (hr : k ≤ r) (hmax : ∀ r', k ≤ r' → ‖M r' k‖ ≤ ‖M r k‖) :
    partialPivotRow M k ≤ r :=
  Finset.min'_le _ _ (mem_filter.2 ⟨mem_univ _, hr, hmax⟩)

/-- If the pivot vanishes, the whole column vanishes below the current index. -/
theorem apply_eq_zero_of_partialPivotRow_eq_zero (h : M (partialPivotRow M k) k = 0) {r : n}
    (hr : k ≤ r) : M r k = 0 := by
  have := norm_apply_le_partialPivotRow M k hr
  rw [h, norm_zero] at this
  exact norm_le_zero_iff.1 this

/-- On a zero pivot column no interchange is performed: the pivot row is `k` itself. -/
theorem partialPivotRow_eq_self_of_forall_eq_zero (h : ∀ r, k ≤ r → M r k = 0) :
    partialPivotRow M k = k :=
  le_antisymm (partialPivotRow_le M k le_rfl fun r' hr' => by rw [h r' hr', h k le_rfl])
    (le_partialPivotRow M k)

/-- `Matrix.partialPivotRow` is a partial-pivoting strategy. -/
theorem isPartialPivot_partialPivotRow :
    IsPartialPivot (partialPivotRow : Matrix n n 𝕜 → n → n) :=
  fun M k => ⟨le_partialPivotRow M k, fun _ hr => norm_apply_le_partialPivotRow M k hr⟩

end PartialPivot

/-! ### The complete-pivoting strategy -/

section CompletePivot

variable {n : Type*} [LinearOrder n] {𝕜 : Type*} [NormedField 𝕜]

/-- **A complete-pivoting strategy** ([quarteroni2000numerical] §3.5, [higham2002accuracy] §9.3):
`piv M k` returns a pair `(r, c)` of indices at or after `k` at which `‖M r c‖` is maximal over
the whole trailing block, the rows and columns from `k` on. The interchanges such a strategy
produces are run by `Matrix.gemFullPivotStage`. -/
def IsCompletePivot (piv : Matrix n n 𝕜 → n → n × n) : Prop :=
  ∀ (M : Matrix n n 𝕜) (k : n), k ≤ (piv M k).1 ∧ k ≤ (piv M k).2 ∧
    ∀ i j, k ≤ i → k ≤ j → ‖M i j‖ ≤ ‖M (piv M k).1 (piv M k).2‖

variable [Finite n]

/-- Some entry of the trailing block from `k` on has maximal modulus in that block. -/
theorem exists_completePivotEntry (M : Matrix n n 𝕜) (k : n) :
    ∃ rc : n × n, k ≤ rc.1 ∧ k ≤ rc.2 ∧
      ∀ i j, k ≤ i → k ≤ j → ‖M i j‖ ≤ ‖M rc.1 rc.2‖ := by
  have : Fintype n := Fintype.ofFinite n
  obtain ⟨rc, hrc, hmax⟩ := Finset.exists_max_image
    (univ.filter fun rc : n × n => k ≤ rc.1 ∧ k ≤ rc.2) (fun rc => ‖M rc.1 rc.2‖)
    ⟨(k, k), by simp⟩
  obtain ⟨-, h1, h2⟩ := mem_filter.1 hrc
  exact ⟨rc, h1, h2, fun i j hi hj => hmax (i, j) (mem_filter.2 ⟨mem_univ _, hi, hj⟩)⟩

/-- **Complete pivoting** ([quarteroni2000numerical] §3.5): an entry of maximal modulus in the
trailing block from `k` on. Unlike `Matrix.partialPivotRow` no canonical choice among the
maximizing entries is made, because every complete-pivoting strategy obeys the same growth bound
(`Matrix.growthFactor_le_wilkinson_of_isCompletePivot`). -/
noncomputable def completePivotEntry (M : Matrix n n 𝕜) (k : n) : n × n :=
  (exists_completePivotEntry M k).choose

/-- `Matrix.completePivotEntry` is a complete-pivoting strategy. -/
theorem isCompletePivot_completePivotEntry :
    IsCompletePivot (completePivotEntry : Matrix n n 𝕜 → n → n × n) :=
  fun M k => (exists_completePivotEntry M k).choose_spec

end CompletePivot

/-! ### Gaussian elimination with a pivoting strategy, on `Fin N` -/

section Stages

variable {K : Type*} [Field K] {N : ℕ}

/-- **Gaussian elimination with a pivoting strategy** `piv`, [quarteroni2000numerical] §3.5:
`gemPivotStage A piv k` is the pair of the matrix `A^{(k+1)}` after `k` stages and the row
permutation `σ_k` accumulated so far. Stage `k < N` chooses the row `r = piv A^{(k)} k`, swaps
rows `k` and `r`, and eliminates column `k` below the pivot; the permutation becomes
`σ_k * swap k r`, so that `σ_k.permMatrix K = P_{k-1} ⋯ P_0` (`Matrix.permMatrix_mul` reverses
the order). Beyond `N` nothing happens. `gemPivotStage A partialPivotRow` is Gaussian elimination
with partial pivoting, and `gemPivotStage A (fun _ k => k)` performs no interchange. -/
noncomputable def gemPivotStage (A : Matrix (Fin N) (Fin N) K)
    (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N) :
    ℕ → Matrix (Fin N) (Fin N) K × Equiv.Perm (Fin N)
  | 0 => (A, 1)
  | k + 1 =>
    if h : k < N then
      (elimStep ((gemPivotStage A piv k).1.submatrix
          (Equiv.swap ⟨k, h⟩ (piv (gemPivotStage A piv k).1 ⟨k, h⟩)) id) ⟨k, h⟩,
        (gemPivotStage A piv k).2 * Equiv.swap ⟨k, h⟩ (piv (gemPivotStage A piv k).1 ⟨k, h⟩))
    else gemPivotStage A piv k

variable (A : Matrix (Fin N) (Fin N) K) (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N)

/-- The interchange of stage `k`: the transposition of `k` and the chosen pivot row. -/
noncomputable def gemPivotSwap (k : ℕ) (h : k < N) : Equiv.Perm (Fin N) :=
  Equiv.swap ⟨k, h⟩ (piv (gemPivotStage A piv k).1 ⟨k, h⟩)

/-- Before the first stage: the matrix itself and the identity permutation. -/
@[simp]
theorem gemPivotStage_zero : gemPivotStage A piv 0 = (A, 1) := rfl

/-- Stage `k + 1`: swap, eliminate, and record the interchange. -/
theorem gemPivotStage_succ_of_lt {k : ℕ} (h : k < N) :
    gemPivotStage A piv (k + 1) =
      (elimStep ((gemPivotStage A piv k).1.submatrix (gemPivotSwap A piv k h) id) ⟨k, h⟩,
        (gemPivotStage A piv k).2 * gemPivotSwap A piv k h) := by
  simp only [gemPivotStage, h, dite_true, gemPivotSwap]

/-- Beyond `N`, the stages do not change. -/
theorem gemPivotStage_succ_of_le {k : ℕ} (h : N ≤ k) :
    gemPivotStage A piv (k + 1) = gemPivotStage A piv k := by
  simp only [gemPivotStage, not_lt.2 h, dite_false]

/-- Beyond `N`, the stages do not change. -/
theorem gemPivotStage_of_le {k : ℕ} (h : N ≤ k) :
    gemPivotStage A piv k = gemPivotStage A piv N := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [gemPivotStage_succ_of_le A piv hk, ih]

/-- [quarteroni2000numerical] (3.51), one stage: `A^{(k+2)} = M_k P_k A^{(k+1)}` with `P_k` the
permutation matrix of the interchange and `M_k` the Gaussian transformation of the swapped
matrix. -/
theorem gemPivotStage_succ_fst_eq_gaussTransform_mul {k : ℕ} (h : k < N) :
    (gemPivotStage A piv (k + 1)).1 =
      gaussTransform ((gemPivotSwap A piv k h).permMatrix K * (gemPivotStage A piv k).1) ⟨k, h⟩ *
        ((gemPivotSwap A piv k h).permMatrix K * (gemPivotStage A piv k).1) := by
  rw [gemPivotStage_succ_of_lt A piv h, gaussTransform_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]

/-- The pivot row chosen at stage `k` lies at or below `k` when the strategy does; the
interchange then fixes every index below `k`. -/
theorem gemPivotSwap_apply_of_lt (hpiv : ∀ M k, k ≤ piv M k) {k : ℕ} (h : k < N) {i : Fin N}
    (hi : (i : ℕ) < k) : gemPivotSwap A piv k h i = i := by
  refine Equiv.swap_apply_of_ne_of_ne (fun hik => ?_) fun hir => ?_
  · rw [hik] at hi
    exact lt_irrefl _ hi
  · have := hpiv (gemPivotStage A piv k).1 ⟨k, h⟩
    rw [← hir, Fin.le_def] at this
    exact absurd (this.trans_lt hi) (lt_irrefl _)

/-- The interchanges after stage `m`, `σ_m⁻¹ σ_{m'}` for `m ≤ m'`, fix every index below `m`. -/
theorem gemPivotStage_snd_inv_mul_apply (hpiv : ∀ M k, k ≤ piv M k) {m m' : ℕ} (hmm' : m ≤ m')
    {i : Fin N} (hi : (i : ℕ) < m) :
    ((gemPivotStage A piv m).2⁻¹ * (gemPivotStage A piv m').2) i = i := by
  induction m', hmm' using Nat.le_induction with
  | base => simp
  | succ m' hm ih =>
    by_cases h : m' < N
    · rw [gemPivotStage_succ_of_lt A piv h]
      dsimp only
      rw [← mul_assoc, Equiv.Perm.mul_apply, gemPivotSwap_apply_of_lt A piv hpiv h (hi.trans_le hm),
        ih]
    · rw [gemPivotStage_succ_of_le A piv (not_lt.1 h), ih]

/-- One step of elimination commutes with a permutation of the rows that fixes the pivot and
every index below it. -/
theorem elimStep_submatrix_of_forall_le {n : Type*} [LinearOrder n] [Fintype n]
    (M : Matrix n n K) {p : n} {ρ : Equiv.Perm n} (hρ : ∀ i, i ≤ p → ρ i = i) :
    elimStep (M.submatrix ρ id) p = (elimStep M p).submatrix ρ id := by
  have hp : ρ p = p := hρ p le_rfl
  have hlt : ∀ i, p < ρ i ↔ p < i := fun i => by
    rcases le_or_gt i p with hi | hi
    · rw [hρ i hi]
    · refine ⟨fun _ => hi, fun _ => lt_of_not_ge fun h => ?_⟩
      have := hρ _ h
      rw [ρ.injective.eq_iff] at this
      rw [this] at h
      exact absurd hi (not_lt.2 h)
  ext i j
  simp only [elimStep_apply, submatrix_apply, id, hp, hlt]

/-- **The stages of Gaussian elimination on `P A` are the pivoted stages, with the rows
permuted by the later interchanges**: with `σ = σ_N` the final permutation of
`gemPivotStage A piv`, `gemStage (P A) k = (A^{(k+1)}).submatrix (σ_k⁻¹ σ) id`, i.e. row `i`
of the plain stage is row `σ_k⁻¹ σ i` of the pivoted stage. This is the content of the book's
`L = P M⁻¹` bookkeeping in [quarteroni2000numerical] §3.5. -/
theorem gemStage_submatrix_eq_submatrix_gemPivotStage (hpiv : ∀ M k, k ≤ piv M k) (k : ℕ) :
    gemStage (A.submatrix (gemPivotStage A piv N).2 id) k =
      (gemPivotStage A piv k).1.submatrix
        ((gemPivotStage A piv k).2⁻¹ * (gemPivotStage A piv N).2) id := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases h : k < N
    · rw [gemStage_succ_of_lt _ h, ih, gemPivotStage_succ_of_lt A piv h]
      dsimp only
      have hρ : (gemPivotStage A piv k).2⁻¹ * (gemPivotStage A piv N).2 =
          gemPivotSwap A piv k h *
            (((gemPivotStage A piv k).2 * gemPivotSwap A piv k h)⁻¹ *
              (gemPivotStage A piv N).2) := by
        rw [_root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [hρ, Equiv.Perm.coe_mul, ← Function.id_comp id, ← submatrix_submatrix,
        Function.id_comp]
      refine elimStep_submatrix_of_forall_le _ fun i hi => ?_
      have hk : (gemPivotStage A piv (k + 1)).2 =
          (gemPivotStage A piv k).2 * gemPivotSwap A piv k h := by
        rw [gemPivotStage_succ_of_lt A piv h]
      rw [← hk]
      exact gemPivotStage_snd_inv_mul_apply A piv hpiv h (Nat.lt_succ_of_le (Fin.le_def.1 hi))
    · rw [gemStage_succ_of_le _ (not_lt.1 h), ih, gemPivotStage_succ_of_le A piv (not_lt.1 h)]

/-- The permutation-matrix form of `Matrix.gemStage_submatrix_eq_submatrix_gemPivotStage`. -/
theorem gemStage_permMatrix_mul_eq_submatrix_gemPivotStage (hpiv : ∀ M k, k ≤ piv M k)
    (k : ℕ) :
    gemStage ((gemPivotStage A piv N).2.permMatrix K * A) k =
      (gemPivotStage A piv k).1.submatrix
        ((gemPivotStage A piv k).2⁻¹ * (gemPivotStage A piv N).2) id := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  exact gemStage_submatrix_eq_submatrix_gemPivotStage A piv hpiv k

/-- The last stage of Gaussian elimination on `P A` is the last pivoted stage. -/
theorem gemStage_permMatrix_mul_card (hpiv : ∀ M k, k ≤ piv M k) :
    gemStage ((gemPivotStage A piv N).2.permMatrix K * A) N = (gemPivotStage A piv N).1 := by
  rw [gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A piv hpiv, inv_mul_cancel]
  rfl

/-- The pivot of stage `k` of Gaussian elimination on `P A` is the entry chosen by the
strategy: `(P A)^{(k)}_{kk} = A^{(k)}_{r_k k}` with `r_k = piv A^{(k)} k`. -/
theorem gemStage_permMatrix_mul_apply_self (hpiv : ∀ M k, k ≤ piv M k) {k : ℕ} (h : k < N) :
    gemStage ((gemPivotStage A piv N).2.permMatrix K * A) k ⟨k, h⟩ ⟨k, h⟩ =
      (gemPivotStage A piv k).1 (piv (gemPivotStage A piv k).1 ⟨k, h⟩) ⟨k, h⟩ := by
  rw [gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A piv hpiv, submatrix_apply, id]
  have hρ : (gemPivotStage A piv k).2⁻¹ * (gemPivotStage A piv N).2 =
      gemPivotSwap A piv k h * ((gemPivotStage A piv (k + 1)).2⁻¹ * (gemPivotStage A piv N).2) := by
    rw [gemPivotStage_succ_of_lt A piv h]
    dsimp only
    rw [_root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hρ, Equiv.Perm.mul_apply, gemPivotStage_snd_inv_mul_apply A piv hpiv h (Nat.lt_succ_self k),
    gemPivotSwap, Equiv.swap_apply_left]

/-- The later interchanges map the indices `≥ k` to indices `≥ k`. -/
theorem le_gemPivotStage_snd_inv_mul_apply (hpiv : ∀ M k, k ≤ piv M k) {m m' : ℕ} (hmm' : m ≤ m')
    {i : Fin N} (hi : m ≤ (i : ℕ)) :
    m ≤ (((gemPivotStage A piv m).2⁻¹ * (gemPivotStage A piv m').2) i : ℕ) := by
  by_contra hcon
  have h := gemPivotStage_snd_inv_mul_apply A piv hpiv hmm' (not_le.1 hcon)
  rw [Equiv.apply_eq_iff_eq] at h
  rw [h] at hcon
  exact hcon hi

/-- **[quarteroni2000numerical] (3.52) for the recurrence**: if the strategy chooses rows at or
below the current index and no chosen pivot vanishes (the last one excepted, which is never used),
then `P A = L U` with `P` the permutation matrix of the accumulated interchanges, `U` the last
pivoted stage, and `L` the multiplier matrix of Gaussian elimination *without* pivoting applied
to `P A` — the book's "the entries of `L` coincide with the multipliers computed by LU
factorization, without pivoting, when applied to the matrix `P A`". -/
theorem gemPivotStage_permMatrix_mul_isLU (hpiv : ∀ M k, k ≤ piv M k)
    (hnz : ∀ k (hk : k < N), k + 1 < N →
      (gemPivotStage A piv k).1 (piv (gemPivotStage A piv k).1 ⟨k, hk⟩) ⟨k, hk⟩ ≠ 0) :
    IsLU ((gemPivotStage A piv N).2.permMatrix K * A)
      (gemLower ((gemPivotStage A piv N).2.permMatrix K * A)) (gemPivotStage A piv N).1 := by
  rw [← gemStage_permMatrix_mul_card A piv hpiv]
  refine isLU_gemLower_gemStage _ fun m hm hmN => ?_
  rw [gemStage_permMatrix_mul_apply_self A piv hpiv hm]
  exact hnz m hm hmN

/-- **The multipliers of partial pivoting are bounded by one**: every entry of the unit lower
factor `L` of `P A = L U` produced by `gemPivotStage A partialPivotRow` has norm at most `1`,
because `l_ij` is `a^{(j)}_{r j} / a^{(j)}_{r_j j}` for some row `r ≥ j`, and the pivot row `r_j`
maximizes the modulus in the column. -/
theorem gemPivotStage_partialPivotRow_norm_gemLower_le_one {𝕜 : Type*} [NormedField 𝕜]
    (A : Matrix (Fin N) (Fin N) 𝕜) (i j : Fin N) :
    ‖gemLower ((gemPivotStage A partialPivotRow N).2.permMatrix 𝕜 * A) i j‖ ≤ 1 := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) 𝕜) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  simp only [gemLower, of_apply]
  split_ifs with hij hij'
  · set M := (gemPivotStage A partialPivotRow j).1
    set ρ := (gemPivotStage A partialPivotRow j).2⁻¹ * (gemPivotStage A partialPivotRow N).2
    have hden : gemStage ((gemPivotStage A partialPivotRow N).2.permMatrix 𝕜 * A) j j j =
        M (partialPivotRow M j) j :=
      gemStage_permMatrix_mul_apply_self A partialPivotRow hpiv j.2
    have hnum : gemStage ((gemPivotStage A partialPivotRow N).2.permMatrix 𝕜 * A) j i j =
        M (ρ i) j := by
      rw [gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A partialPivotRow hpiv j,
        submatrix_apply]
      rfl
    rw [norm_div, hnum, hden]
    rcases eq_or_ne (M (partialPivotRow M j) j) 0 with h0 | h0
    · rw [h0, norm_zero, div_zero]
      exact zero_le_one
    · rw [div_le_one (norm_pos_iff.2 h0)]
      exact norm_apply_le_partialPivotRow M j (Fin.le_def.2
        (le_gemPivotStage_snd_inv_mul_apply A partialPivotRow hpiv j.2.le (Fin.le_def.1 hij.le)))
  · simp
  · simp

end Stages

/-! ### Gaussian elimination with complete pivoting, on `Fin N` -/

section FullPivotStages

variable {K : Type*} [Field K] {N : ℕ}

/-- **Gaussian elimination with complete pivoting** ([quarteroni2000numerical] §3.5): with a
strategy `piv` choosing a *pair* of indices, `gemFullPivotStage A piv k` is the triple of the
matrix `A^{(k+1)}` after `k` stages, the accumulated row permutation `σ_k` and the accumulated
column permutation `ρ_k`. Stage `k < N` chooses `(r, c) = piv A^{(k)} k`, swaps rows `k` and `r`
and columns `k` and `c`, and eliminates column `k` below the pivot; the permutations become
`σ_k * swap k r` and `ρ_k * swap k c`. Beyond `N` nothing happens. This is the two-sided analogue
of `Matrix.gemPivotStage`, which permutes rows only. -/
noncomputable def gemFullPivotStage (A : Matrix (Fin N) (Fin N) K)
    (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N × Fin N) :
    ℕ → Matrix (Fin N) (Fin N) K × Equiv.Perm (Fin N) × Equiv.Perm (Fin N)
  | 0 => (A, 1, 1)
  | k + 1 =>
    if h : k < N then
      (elimStep ((gemFullPivotStage A piv k).1.submatrix
          (Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1)
          (Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2)) ⟨k, h⟩,
        (gemFullPivotStage A piv k).2.1 *
          Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1,
        (gemFullPivotStage A piv k).2.2 *
          Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2)
    else gemFullPivotStage A piv k

variable (A : Matrix (Fin N) (Fin N) K) (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N × Fin N)

/-- The row interchange of stage `k` of complete pivoting. -/
noncomputable def gemFullPivotRowSwap (k : ℕ) (h : k < N) : Equiv.Perm (Fin N) :=
  Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1

/-- The column interchange of stage `k` of complete pivoting. -/
noncomputable def gemFullPivotColSwap (k : ℕ) (h : k < N) : Equiv.Perm (Fin N) :=
  Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2

/-- Before the first stage: the matrix itself and two identity permutations. -/
@[simp]
theorem gemFullPivotStage_zero : gemFullPivotStage A piv 0 = (A, 1, 1) := rfl

/-- Stage `k + 1`: interchange, eliminate, and record both interchanges. -/
theorem gemFullPivotStage_succ_of_lt {k : ℕ} (h : k < N) :
    gemFullPivotStage A piv (k + 1) =
      (elimStep ((gemFullPivotStage A piv k).1.submatrix (gemFullPivotRowSwap A piv k h)
          (gemFullPivotColSwap A piv k h)) ⟨k, h⟩,
        (gemFullPivotStage A piv k).2.1 * gemFullPivotRowSwap A piv k h,
        (gemFullPivotStage A piv k).2.2 * gemFullPivotColSwap A piv k h) := by
  simp only [gemFullPivotStage, h, dite_true, gemFullPivotRowSwap, gemFullPivotColSwap]

/-- Beyond `N`, the stages do not change. -/
theorem gemFullPivotStage_succ_of_le {k : ℕ} (h : N ≤ k) :
    gemFullPivotStage A piv (k + 1) = gemFullPivotStage A piv k := by
  simp only [gemFullPivotStage, not_lt.2 h, dite_false]

omit [Field K] in
/-- A sequence of permutations built up by right multiplication by permutations that fix the
indices below the step: the composite of the interchanges after step `m` fixes every index below
`m`. Both the row and the column permutations of `Matrix.gemFullPivotStage` are of this shape. -/
theorem perm_inv_mul_apply_of_step {σ : ℕ → Equiv.Perm (Fin N)}
    (hstep : ∀ k, ∃ τ : Equiv.Perm (Fin N),
      σ (k + 1) = σ k * τ ∧ ∀ i : Fin N, (i : ℕ) < k → τ i = i)
    {m m' : ℕ} (hmm' : m ≤ m') {i : Fin N} (hi : (i : ℕ) < m) :
    ((σ m)⁻¹ * σ m') i = i := by
  induction m', hmm' using Nat.le_induction with
  | base => simp
  | succ m' hm ih =>
    obtain ⟨τ, hτ, hfix⟩ := hstep m'
    rw [hτ, ← mul_assoc, Equiv.Perm.mul_apply, hfix i (hi.trans_le hm), ih]

omit [Field K] in
/-- A permutation fixing every index below `m` maps the indices from `m` on to indices from `m`
on. -/
theorem le_apply_of_forall_lt_apply_eq {ρ : Equiv.Perm (Fin N)} {m : ℕ}
    (h : ∀ i : Fin N, (i : ℕ) < m → ρ i = i) {i : Fin N} (hi : m ≤ (i : ℕ)) : m ≤ (ρ i : ℕ) := by
  by_contra hcon
  have h1 := h _ (not_le.1 hcon)
  rw [ρ.injective.eq_iff] at h1
  rw [h1] at hcon
  exact hcon hi

/-- Taking a submatrix along a product of permutations is taking two submatrices. -/
theorem submatrix_perm_mul {m α : Type*} (M : Matrix m m α) (s t s' t' : Equiv.Perm m) :
    M.submatrix (s * t) (s' * t') = (M.submatrix s s').submatrix t t' := rfl

/-- One step of elimination commutes with a permutation of the rows fixing the pivot and every
index below it together with a permutation of the columns fixing the pivot. -/
theorem elimStep_submatrix_submatrix_of_forall_le {m : Type*} [LinearOrder m] [Fintype m]
    (M : Matrix m m K) {p : m} {σ ρ : Equiv.Perm m} (hσ : ∀ i, i ≤ p → σ i = i) (hρ : ρ p = p) :
    elimStep (M.submatrix σ ρ) p = (elimStep M p).submatrix σ ρ := by
  have h1 : M.submatrix (σ : m → m) (ρ : m → m) = (M.submatrix id ρ).submatrix σ id := by
    rw [submatrix_submatrix]
    rfl
  rw [h1, elimStep_submatrix_of_forall_le _ hσ, elimStep_submatrix_id_of_apply_self _ hρ,
    submatrix_submatrix]
  rfl

/-- The row interchange of stage `k` fixes every index below `k`. -/
theorem gemFullPivotRowSwap_apply_of_lt (hrow : ∀ M k, k ≤ (piv M k).1) {k : ℕ} (h : k < N)
    {i : Fin N} (hi : (i : ℕ) < k) : gemFullPivotRowSwap A piv k h i = i := by
  refine Equiv.swap_apply_of_ne_of_ne (fun hik => ?_) fun hir => ?_
  · rw [hik] at hi
    exact lt_irrefl _ hi
  · have := hrow (gemFullPivotStage A piv k).1 ⟨k, h⟩
    rw [← hir, Fin.le_def] at this
    exact absurd (this.trans_lt hi) (lt_irrefl _)

/-- The column interchange of stage `k` fixes every index below `k`. -/
theorem gemFullPivotColSwap_apply_of_lt (hcol : ∀ M k, k ≤ (piv M k).2) {k : ℕ} (h : k < N)
    {i : Fin N} (hi : (i : ℕ) < k) : gemFullPivotColSwap A piv k h i = i := by
  refine Equiv.swap_apply_of_ne_of_ne (fun hik => ?_) fun hir => ?_
  · rw [hik] at hi
    exact lt_irrefl _ hi
  · have := hcol (gemFullPivotStage A piv k).1 ⟨k, h⟩
    rw [← hir, Fin.le_def] at this
    exact absurd (this.trans_lt hi) (lt_irrefl _)

/-- The row interchanges after stage `m` fix every index below `m`. -/
theorem gemFullPivotStage_rowPerm_inv_mul_apply (hrow : ∀ M k, k ≤ (piv M k).1) {m m' : ℕ}
    (hmm' : m ≤ m') {i : Fin N} (hi : (i : ℕ) < m) :
    ((gemFullPivotStage A piv m).2.1⁻¹ * (gemFullPivotStage A piv m').2.1) i = i := by
  refine perm_inv_mul_apply_of_step (σ := fun k => (gemFullPivotStage A piv k).2.1)
    (fun k => ?_) hmm' hi
  by_cases h : k < N
  · exact ⟨gemFullPivotRowSwap A piv k h, by rw [gemFullPivotStage_succ_of_lt A piv h],
      fun _ hj => gemFullPivotRowSwap_apply_of_lt A piv hrow h hj⟩
  · exact ⟨1, by rw [gemFullPivotStage_succ_of_le A piv (not_lt.1 h), mul_one], fun _ _ => rfl⟩

/-- The column interchanges after stage `m` fix every index below `m`. -/
theorem gemFullPivotStage_colPerm_inv_mul_apply (hcol : ∀ M k, k ≤ (piv M k).2) {m m' : ℕ}
    (hmm' : m ≤ m') {i : Fin N} (hi : (i : ℕ) < m) :
    ((gemFullPivotStage A piv m).2.2⁻¹ * (gemFullPivotStage A piv m').2.2) i = i := by
  refine perm_inv_mul_apply_of_step (σ := fun k => (gemFullPivotStage A piv k).2.2)
    (fun k => ?_) hmm' hi
  by_cases h : k < N
  · exact ⟨gemFullPivotColSwap A piv k h, by rw [gemFullPivotStage_succ_of_lt A piv h],
      fun _ hj => gemFullPivotColSwap_apply_of_lt A piv hcol h hj⟩
  · exact ⟨1, by rw [gemFullPivotStage_succ_of_le A piv (not_lt.1 h), mul_one], fun _ _ => rfl⟩

/-- **The stages of Gaussian elimination on `P A Q` are the completely pivoted stages, with their
rows and columns permuted by the later interchanges**: with `σ` and `ρ` the final permutations of
`gemFullPivotStage A piv`,
`gemStage (A.submatrix σ ρ) k = (A^{(k+1)}).submatrix (σ_k⁻¹ σ) (ρ_k⁻¹ ρ)`. It is the two-sided
form of `Matrix.gemStage_submatrix_eq_submatrix_gemPivotStage`. -/
theorem gemStage_submatrix_eq_submatrix_gemFullPivotStage (hrow : ∀ M k, k ≤ (piv M k).1)
    (hcol : ∀ M k, k ≤ (piv M k).2) (k : ℕ) :
    gemStage (A.submatrix (gemFullPivotStage A piv N).2.1 (gemFullPivotStage A piv N).2.2) k =
      (gemFullPivotStage A piv k).1.submatrix
        ((gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1)
        ((gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases h : k < N
    · rw [gemStage_succ_of_lt _ h, ih, gemFullPivotStage_succ_of_lt A piv h]
      dsimp only
      have hk1 : (gemFullPivotStage A piv (k + 1)).2.1 =
          (gemFullPivotStage A piv k).2.1 * gemFullPivotRowSwap A piv k h := by
        rw [gemFullPivotStage_succ_of_lt A piv h]
      have hk2 : (gemFullPivotStage A piv (k + 1)).2.2 =
          (gemFullPivotStage A piv k).2.2 * gemFullPivotColSwap A piv k h := by
        rw [gemFullPivotStage_succ_of_lt A piv h]
      have hs : (gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1 =
          gemFullPivotRowSwap A piv k h *
            ((gemFullPivotStage A piv (k + 1)).2.1⁻¹ * (gemFullPivotStage A piv N).2.1) := by
        rw [hk1, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      have hr : (gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2 =
          gemFullPivotColSwap A piv k h *
            ((gemFullPivotStage A piv (k + 1)).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) := by
        rw [hk2, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [← hk1, ← hk2, hs, hr, submatrix_perm_mul]
      refine elimStep_submatrix_submatrix_of_forall_le _ (fun i hi => ?_) ?_
      · exact gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow h
          (Nat.lt_succ_of_le (Fin.le_def.1 hi))
      · exact gemFullPivotStage_colPerm_inv_mul_apply A piv hcol h (Nat.lt_succ_self k)
    · rw [gemStage_succ_of_le _ (not_lt.1 h), ih, gemFullPivotStage_succ_of_le A piv (not_lt.1 h)]

/-- The pivot of stage `k` of Gaussian elimination on `P A Q` is the entry chosen by the
strategy: `(P A Q)^{(k)}_{kk} = A^{(k)}_{r c}` with `(r, c) = piv A^{(k)} k`. -/
theorem gemStage_submatrix_apply_self (hrow : ∀ M k, k ≤ (piv M k).1)
    (hcol : ∀ M k, k ≤ (piv M k).2) {k : ℕ} (h : k < N) :
    gemStage (A.submatrix (gemFullPivotStage A piv N).2.1 (gemFullPivotStage A piv N).2.2) k
        ⟨k, h⟩ ⟨k, h⟩ =
      (gemFullPivotStage A piv k).1 (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1
        (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2 := by
  rw [gemStage_submatrix_eq_submatrix_gemFullPivotStage A piv hrow hcol, submatrix_apply]
  have hk1 : (gemFullPivotStage A piv (k + 1)).2.1 =
      (gemFullPivotStage A piv k).2.1 * gemFullPivotRowSwap A piv k h := by
    rw [gemFullPivotStage_succ_of_lt A piv h]
  have hk2 : (gemFullPivotStage A piv (k + 1)).2.2 =
      (gemFullPivotStage A piv k).2.2 * gemFullPivotColSwap A piv k h := by
    rw [gemFullPivotStage_succ_of_lt A piv h]
  have hs : (gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1 =
      gemFullPivotRowSwap A piv k h *
        ((gemFullPivotStage A piv (k + 1)).2.1⁻¹ * (gemFullPivotStage A piv N).2.1) := by
    rw [hk1, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hr : (gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2 =
      gemFullPivotColSwap A piv k h *
        ((gemFullPivotStage A piv (k + 1)).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) := by
    rw [hk2, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hs, Equiv.Perm.mul_apply,
    gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow h (Nat.lt_succ_self k), hr,
    Equiv.Perm.mul_apply,
    gemFullPivotStage_colPerm_inv_mul_apply A piv hcol h (Nat.lt_succ_self k),
    gemFullPivotRowSwap, gemFullPivotColSwap, Equiv.swap_apply_left, Equiv.swap_apply_left]

/-- The later row interchanges map the indices from `m` on to indices from `m` on. -/
theorem le_gemFullPivotStage_rowPerm_inv_mul_apply (hrow : ∀ M k, k ≤ (piv M k).1) {m m' : ℕ}
    (hmm' : m ≤ m') {i : Fin N} (hi : m ≤ (i : ℕ)) :
    m ≤ ((((gemFullPivotStage A piv m).2.1⁻¹ * (gemFullPivotStage A piv m').2.1) i : Fin N) : ℕ) :=
  le_apply_of_forall_lt_apply_eq
    (fun _ hj => gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow hmm' hj) hi

/-- The later column interchanges map the indices from `m` on to indices from `m` on. -/
theorem le_gemFullPivotStage_colPerm_inv_mul_apply (hcol : ∀ M k, k ≤ (piv M k).2) {m m' : ℕ}
    (hmm' : m ≤ m') {i : Fin N} (hi : m ≤ (i : ℕ)) :
    m ≤ ((((gemFullPivotStage A piv m).2.2⁻¹ * (gemFullPivotStage A piv m').2.2) i : Fin N) : ℕ) :=
  le_apply_of_forall_lt_apply_eq
    (fun _ hj => gemFullPivotStage_colPerm_inv_mul_apply A piv hcol hmm' hj) hi

/-- The permutation-matrix form of a two-sided submatrix: `A.submatrix σ ρ` is `P A Q` with
`P = σ.permMatrix K` and `Q = (ρ⁻¹).permMatrix K`. -/
theorem permMatrix_mul_mul_permMatrix (σ ρ : Equiv.Perm (Fin N)) :
    σ.permMatrix K * A * (ρ⁻¹).permMatrix K = A.submatrix σ ρ := by
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix, Function.id_comp, Function.comp_id,
    Equiv.Perm.inv_def, Equiv.symm_symm]

end FullPivotStages

/-! ### Nonsingular matrices have nonzero pivots under partial pivoting -/

section Nonsingular

/-- A square matrix whose columns before `k` vanish below the diagonal and whose column `k`
vanishes from row `k` downwards is singular: it is block upper triangular along `{≤ k}`, and its
leading block is upper triangular with the zero diagonal entry `M k k`. -/
theorem det_eq_zero_of_apply_eq_zero_of_lt {n : Type*} [LinearOrder n] [Fintype n] {R : Type*}
    [CommRing R] (M : Matrix n n R) (k : n) (h1 : ∀ i j, j < k → j < i → M i j = 0)
    (h2 : ∀ i, k ≤ i → M i k = 0) : M.det = 0 := by
  rw [twoBlockTriangular_det M (· ≤ k) fun i hi j hj => ?_]
  · refine mul_eq_zero_of_left ?_ _
    rw [det_of_isUpperTriangular (M := toSquareBlockProp M (· ≤ k)) fun i j hij =>
      h1 i.1 j.1 ((Subtype.coe_lt_coe.2 hij).trans_le i.2) hij]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨k, le_rfl⟩ : {a // a ≤ k})) (h2 k le_rfl)
  · rcases hj.lt_or_eq with hjk | rfl
    · exact h1 i j hjk (hjk.trans (not_le.1 hi))
    · exact h2 i (not_le.1 hi).le

variable {N : ℕ} {𝕜 : Type*} [NormedField 𝕜]

/-- **A nonsingular matrix has nonzero pivots under partial pivoting**: if `A` is a unit, the
pivot chosen at every stage of `gemPivotStage A partialPivotRow` is nonzero. Otherwise the
pivot column of some stage vanishes from the diagonal downwards, so the corresponding stage of
Gaussian elimination on `P A` is singular (`Matrix.det_eq_zero_of_apply_eq_zero_of_lt`), while
every stage has the determinant of `P A = ± det A`. -/
theorem gemPivotStage_partialPivotRow_pivot_ne_zero_of_isUnit (A : Matrix (Fin N) (Fin N) 𝕜)
    (hA : IsUnit A) (k : ℕ) (hk : k < N) :
    (gemPivotStage A partialPivotRow k).1
      (partialPivotRow (gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩) ⟨k, hk⟩ ≠ 0 := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) 𝕜) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  set B := (gemPivotStage A partialPivotRow N).2.permMatrix 𝕜 * A with hB
  have hdetB : B.det ≠ 0 := by
    rw [hB, det_mul, det_permutation]
    refine mul_ne_zero ?_ (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det A).1 hA))
    rcases Int.units_eq_one_or (Equiv.Perm.sign (gemPivotStage A partialPivotRow N).2)
      with h | h <;> simp [h]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro h0
  have hprev : ∀ m (hm : m < N), m < k → m + 1 < N → gemStage B m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0 :=
    fun m hm hmk _ => by
      rw [hB, gemStage_permMatrix_mul_apply_self A partialPivotRow hpiv hm]
      exact ih m hmk hm
  have hz : ∀ i : Fin N, k ≤ (i : ℕ) → gemStage B k i ⟨k, hk⟩ = 0 := fun i hi => by
    rw [hB, gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A partialPivotRow hpiv k,
      submatrix_apply]
    exact apply_eq_zero_of_partialPivotRow_eq_zero _ _ h0 (Fin.le_def.2
      (le_gemPivotStage_snd_inv_mul_apply A partialPivotRow hpiv hk.le hi))
  have hdet : (gemStage B k).det = 0 :=
    det_eq_zero_of_apply_eq_zero_of_lt _ ⟨k, hk⟩
      (fun i j hj hji => gemStage_apply_eq_zero_of_lt B hprev (Fin.lt_def.1 hj) hji)
      fun i hi => hz i (Fin.le_def.1 hi)
  have := gemLowerStage_mul_gemStage B k
  rw [← this, det_mul, (isUnitLowerTriangular_gemLowerStage B k).det_eq_one, one_mul, hdet]
    at hdetB
  exact hdetB rfl

/-- **The factors of `P A = L U` are those of Gaussian elimination without pivoting applied to
`P A`** ([quarteroni2000numerical] §3.5, the sentence before Program 9): if `P A = L U` and the
strict leading principal submatrices of `P A` are nonsingular, then `L` is the multiplier matrix
and `U` the last stage of `Matrix.gemStage` on `P A`, by uniqueness of the factorization. -/
theorem IsLU.eq_of_permMatrix_mul {K : Type*} [Field K] {σ : Equiv.Perm (Fin N)}
    {A L U : Matrix (Fin N) (Fin N) K} (h : IsLU (σ.permMatrix K * A) L U)
    (hA : ∀ k, IsUnit ((σ.permMatrix K * A).strictLeadingPrincipalSubmatrix k)) :
    L = gemLower (σ.permMatrix K * A) ∧ U = gemStage (σ.permMatrix K * A) N :=
  h.unique (isLU_gemLower_gemStage _ ((gemStage_pivots_ne_zero_iff _).2 hA)) hA

end Nonsingular

/-! ### The growth factor -/

section SupAbs

variable {m n : Type*} [Finite m] [Finite n]

/-- The largest absolute value of an entry of a real matrix, `max_{i,j} |a_ij|`, as a supremum
(`0` for an empty matrix). -/
noncomputable def supAbs (A : Matrix m n ℝ) : ℝ := ⨆ p : m × n, |A p.1 p.2|

/-- Every entry is bounded by `supAbs`. -/
theorem abs_apply_le_supAbs (A : Matrix m n ℝ) (i : m) (j : n) : |A i j| ≤ A.supAbs :=
  le_ciSup (f := fun p : m × n => |A p.1 p.2|) (Set.finite_range _).bddAbove (i, j)

/-- `supAbs` is nonnegative. -/
theorem supAbs_nonneg (A : Matrix m n ℝ) : 0 ≤ A.supAbs := by
  rcases isEmpty_or_nonempty (m × n) with h | ⟨⟨i, j⟩⟩
  · simp [supAbs]
  · exact (abs_nonneg _).trans (abs_apply_le_supAbs A i j)

omit [Finite m] [Finite n] in
/-- `supAbs` is the least bound on the entries, among nonnegative bounds. -/
theorem supAbs_le {A : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, |A i j| ≤ c) :
    A.supAbs ≤ c := by
  rcases isEmpty_or_nonempty (m × n) with hmn | hmn
  · simp [supAbs, hc]
  · exact ciSup_le fun p => h p.1 p.2

/-- `supAbs` is attained on a nonempty matrix. -/
theorem exists_abs_apply_eq_supAbs [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) :
    ∃ i j, |A i j| = A.supAbs := by
  obtain ⟨⟨i, j⟩, hij⟩ := Finite.exists_max fun p : m × n => |A p.1 p.2|
  exact ⟨i, j, le_antisymm (abs_apply_le_supAbs A i j) (ciSup_le fun p => hij p)⟩

/-- `supAbs A = 0` exactly when `A = 0`. -/
theorem supAbs_eq_zero_iff {A : Matrix m n ℝ} : A.supAbs = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have := abs_apply_le_supAbs A i j
    rw [h] at this
    exact abs_nonpos_iff.1 this
  · rintro rfl
    exact le_antisymm (supAbs_le le_rfl fun i j => by simp) (supAbs_nonneg _)

omit [Finite m] [Finite n] in
/-- On an empty index type `supAbs` vanishes. -/
theorem supAbs_of_isEmpty [IsEmpty m] (A : Matrix m n ℝ) : A.supAbs = 0 := by
  simp [supAbs]

end SupAbs

section GrowthFactor

variable {N : ℕ}

/-- **The growth factor** of Gaussian elimination without pivoting on `A`,
[quarteroni2000numerical] (3.66) and [higham2002accuracy] §9.3:
`max_{i,j,k} |a^{(k)}_{ij}| / max_{i,j} |a_{ij}|` over the *exact* stages
`A^{(1)} = A, …, A^{(N)}` (`Matrix.gemStage A k`, `k < N`), with the junk value `0` for `A = 0`.
The book defines it on the computed stages; the exact one is the one that admits bounds
([higham2002accuracy], after Theorem 9.5). For Gaussian elimination with partial pivoting the
growth factor is `growthFactor (P A)`, since the stages of the pivoted elimination are those of
the plain elimination on `P A` up to the order of the rows
(`Matrix.gemStage_permMatrix_mul_eq_submatrix_gemPivotStage`). -/
noncomputable def growthFactor (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (⨆ p : Fin N × Fin N × Fin N, |gemStage A p.1 p.2.1 p.2.2|) / A.supAbs

variable (A : Matrix (Fin N) (Fin N) ℝ)

/-- The stages of the zero matrix are zero. -/
theorem gemStage_zero_matrix {K : Type*} [Field K] (k : ℕ) :
    gemStage (0 : Matrix (Fin N) (Fin N) K) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < N
    · rw [gemStage_succ_of_lt _ h, ih]
      ext i j
      simp [elimStep_apply]
    · rw [gemStage_succ_of_le _ (not_lt.1 h), ih]

/-- The growth factor is nonnegative. -/
theorem growthFactor_nonneg : 0 ≤ growthFactor A := by
  unfold growthFactor
  refine div_nonneg ?_ (supAbs_nonneg A)
  rcases isEmpty_or_nonempty (Fin N × Fin N × Fin N) with h | ⟨⟨k, i, j⟩⟩
  · simp
  · exact (abs_nonneg _).trans (le_ciSup (f := fun p : Fin N × Fin N × Fin N =>
      |gemStage A p.1 p.2.1 p.2.2|) (Set.finite_range _).bddAbove (k, i, j))

/-- Every entry of every stage (the last, `U`, included) is at most the growth factor times the
largest entry of `A`, the inequality `|u_ij| ≤ ρ_n max |a_ij|` of [quarteroni2000numerical]
§3.10. -/
theorem abs_gemStage_le_growthFactor_mul_supAbs (k : ℕ) (i j : Fin N) :
    |gemStage A k i j| ≤ growthFactor A * A.supAbs := by
  rcases eq_or_ne A.supAbs 0 with h0 | h0
  · rw [supAbs_eq_zero_iff.1 h0, gemStage_zero_matrix]
    simp only [zero_apply, abs_zero]
    exact mul_nonneg (growthFactor_nonneg _) (supAbs_nonneg _)
  have hbdd : BddAbove (Set.range fun p : Fin N × Fin N × Fin N =>
      |gemStage A p.1 p.2.1 p.2.2|) := (Set.finite_range _).bddAbove
  rw [growthFactor, div_mul_cancel₀ _ h0]
  rcases lt_or_ge k N with hk | hk
  · exact le_ciSup hbdd (⟨k, hk⟩, i, j)
  · rw [gemStage_apply_of_le A (le_refl (i : ℕ)) (i.2.le.trans hk)]
    exact le_ciSup hbdd (i, i, j)

/-- A uniform bound `|a^{(k)}_{ij}| ≤ c max |a_{ij}|` on the stages bounds the growth factor by
`c`. -/
theorem growthFactor_le_of_forall_abs_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (k : ℕ) (i j : Fin N), k < N → |gemStage A k i j| ≤ c * A.supAbs) :
    growthFactor A ≤ c := by
  rcases eq_or_ne A.supAbs 0 with h0 | h0
  · rw [growthFactor, h0, div_zero]
    exact hc
  have hpos : 0 < A.supAbs := lt_of_le_of_ne (supAbs_nonneg A) (Ne.symm h0)
  have hN : Nonempty (Fin N) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h0 (supAbs_of_isEmpty A)
  rw [growthFactor, div_le_iff₀ hpos]
  exact ciSup_le fun p => h p.1 p.2.1 p.2.2 p.1.2

/-- The growth factor of a nonzero matrix is at least `1`: the first stage is `A` itself. -/
theorem one_le_growthFactor (hA : A ≠ 0) : 1 ≤ growthFactor A := by
  have h0 : A.supAbs ≠ 0 := fun h => hA (supAbs_eq_zero_iff.1 h)
  have hpos : 0 < A.supAbs := lt_of_le_of_ne (supAbs_nonneg A) (Ne.symm h0)
  have hN : Nonempty (Fin N) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h0 (supAbs_of_isEmpty A)
  obtain ⟨i, j, hij⟩ := exists_abs_apply_eq_supAbs A
  rw [growthFactor, le_div_iff₀ hpos, one_mul, ← hij]
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN.elim fun i => i.elim0)
  exact le_ciSup (f := fun p : Fin N × Fin N × Fin N => |gemStage A p.1 p.2.1 p.2.2|)
    (Set.finite_range _).bddAbove (⟨0, hN0⟩, i, j)

/-- Each stage of Gaussian elimination with multipliers of modulus at most `1` at most doubles
the largest entry: `|a^{(k+1)}_{ij}| ≤ |a^{(k)}_{ij}| + |m_{ik}| |a^{(k)}_{kj}|`. -/
theorem abs_gemStage_le_two_pow_mul_supAbs
    (hmul : ∀ (k : ℕ) (hk : k < N) (i : Fin N), ⟨k, hk⟩ < i →
      |gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩| ≤ 1) (k : ℕ) (i j : Fin N) :
    |gemStage A k i j| ≤ 2 ^ k * A.supAbs := by
  induction k generalizing i j with
  | zero => simpa using abs_apply_le_supAbs A i j
  | succ k ih =>
    have hS : 0 ≤ A.supAbs := supAbs_nonneg A
    have h2 : (2 : ℝ) ^ k * A.supAbs ≤ 2 ^ (k + 1) * A.supAbs := by
      rw [pow_succ]
      nlinarith [pow_pos (two_pos (α := ℝ)) k]
    by_cases hk : k < N
    · rw [gemStage_succ_of_lt A hk, elimStep_apply]
      split_ifs with hki
      · have hm := hmul k hk i hki
        rw [← div_eq_mul_inv]
        calc |gemStage A k i j - gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩ *
              gemStage A k ⟨k, hk⟩ j|
            ≤ |gemStage A k i j| + |gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩| *
              |gemStage A k ⟨k, hk⟩ j| := by
              rw [← abs_mul]
              exact abs_sub _ _
          _ ≤ 2 ^ k * A.supAbs + 1 * (2 ^ k * A.supAbs) := by
              gcongr
              · exact ih i j
              · exact ih _ j
          _ = 2 ^ (k + 1) * A.supAbs := by ring
      · rw [sub_zero]
        exact (ih i j).trans h2
    · rw [gemStage_succ_of_le A (not_lt.1 hk)]
      exact (ih i j).trans h2

/-- **[quarteroni2000numerical] §3.10, "the growth factor can be bounded by `2^{n-1}`"**: if
every multiplier of Gaussian elimination has modulus at most one, the growth factor is at most
`2^{N-1}`, each stage at most doubling the largest entry. With
`Matrix.gemPivotStage_partialPivotRow_norm_gemLower_le_one` this is the bound for partial
pivoting (`Matrix.growthFactor_le_two_pow_of_partialPivotRow`). -/
theorem growthFactor_le_two_pow
    (hmul : ∀ (k : ℕ) (hk : k < N) (i : Fin N), ⟨k, hk⟩ < i →
      |gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩| ≤ 1) :
    growthFactor A ≤ 2 ^ (N - 1) := by
  refine growthFactor_le_of_forall_abs_le A (by positivity) fun k i j hk => ?_
  refine (abs_gemStage_le_two_pow_mul_supAbs A hmul k i j).trans ?_
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) (supAbs_nonneg A)

/-- **The growth factor of partial pivoting is at most `2^{N-1}`** ([quarteroni2000numerical]
§3.10, [higham2002accuracy] §9.3): the multipliers of `P A = L U` are bounded by one. -/
theorem growthFactor_le_two_pow_of_partialPivotRow :
    growthFactor ((gemPivotStage A partialPivotRow N).2.permMatrix ℝ * A) ≤ 2 ^ (N - 1) := by
  refine growthFactor_le_two_pow _ fun k hk i hki => ?_
  have := gemPivotStage_partialPivotRow_norm_gemLower_le_one A i ⟨k, hk⟩
  rwa [Real.norm_eq_abs, gemLower, of_apply, ite_eq_left hki] at this

end GrowthFactor

/-! ### Symmetric positive definite matrices: no growth -/

section PosDef

variable {N : ℕ}

/-- `IsPosDefFrom M k`: the trailing block `M(≥ k, ≥ k)` of a real matrix is symmetric positive
definite, stated on the vectors supported on the indices `≥ k` so that no reindexing is needed.
It is the invariant carried by the stages of Gaussian elimination on a positive definite matrix
([higham2002accuracy] §10.1.1). -/
def IsPosDefFrom (M : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : Prop :=
  (∀ i j : Fin N, k ≤ (i : ℕ) → k ≤ (j : ℕ) → M i j = M j i) ∧
    ∀ y : Fin N → ℝ, (∀ i : Fin N, (i : ℕ) < k → y i = 0) → y ≠ 0 → 0 < y ⬝ᵥ M *ᵥ y

/-- A positive definite matrix is positive definite from the first index. -/
theorem PosDef.isPosDefFrom_zero {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    IsPosDefFrom A 0 :=
  ⟨fun i j _ _ => by simpa using (hA.isHermitian.apply i j).symm,
    fun y _ hy => by simpa using hA.dotProduct_mulVec_pos hy⟩

/-- Positive definiteness from `k` implies positive definiteness from every later index. -/
theorem IsPosDefFrom.mono {M : Matrix (Fin N) (Fin N) ℝ} {k k' : ℕ} (h : IsPosDefFrom M k)
    (hkk' : k ≤ k') : IsPosDefFrom M k' :=
  ⟨fun i j hi hj => h.1 i j (hkk'.trans hi) (hkk'.trans hj),
    fun y hy hy0 => h.2 y (fun i hi => hy i (hi.trans_le hkk')) hy0⟩

/-- The quadratic form at `y = e_i a + e_j b`. -/
theorem dotProduct_mulVec_single_add_single (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N)
    (a b : ℝ) :
    (Pi.single i a + Pi.single j b) ⬝ᵥ M *ᵥ (Pi.single i a + Pi.single j b) =
      a * M i i * a + a * M i j * b + (b * M j i * a + b * M j j * b) := by
  simp only [mulVec_add, mulVec_single, add_dotProduct, dotProduct_add, single_dotProduct,
    Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

/-- The diagonal of the trailing block is positive. -/
theorem IsPosDefFrom.diag_pos {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ} (h : IsPosDefFrom M k)
    {i : Fin N} (hi : k ≤ (i : ℕ)) : 0 < M i i := by
  have := h.2 (Pi.single i 1) (fun l hl => Pi.single_eq_of_ne (fun hli => by
    rw [hli] at hl; exact absurd hi (not_le.2 hl)) 1) (by simp)
  simpa using this

/-- The entries of a positive definite block are bounded by its diagonal:
`|m_ij| ≤ max m_ii m_jj`, since `m_ii ± 2 m_ij + m_jj > 0`. -/
theorem IsPosDefFrom.abs_apply_le_max {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ}
    (h : IsPosDefFrom M k) {i j : Fin N} (hi : k ≤ (i : ℕ)) (hj : k ≤ (j : ℕ)) :
    |M i j| ≤ max (M i i) (M j j) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [abs_of_pos (h.diag_pos hi)]
    exact le_max_left _ _
  have hsymm := h.1 i j hi hj
  have hsupp : ∀ b : ℝ, ∀ l : Fin N, (l : ℕ) < k →
      (Pi.single i 1 + Pi.single j b : Fin N → ℝ) l = 0 := by
    intro b l hl
    have hli : l ≠ i := fun e => by rw [e] at hl; exact absurd hi (not_le.2 hl)
    have hlj : l ≠ j := fun e => by rw [e] at hl; exact absurd hj (not_le.2 hl)
    simp [Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj]
  have hne : ∀ b : ℝ, Pi.single i 1 + Pi.single j b ≠ (0 : Fin N → ℝ) := fun b h0 => by
    have := congrFun h0 i
    rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.zero_apply] at this
    linarith
  have h1 := h.2 _ (hsupp 1) (hne 1)
  have h2 := h.2 _ (hsupp (-1)) (hne (-1))
  rw [dotProduct_mulVec_single_add_single] at h1 h2
  rw [abs_le]
  constructor
  · nlinarith [le_max_left (M i i) (M j j), le_max_right (M i i) (M j j)]
  · nlinarith [le_max_left (M i i) (M j j), le_max_right (M i i) (M j j)]

/-- The quadratic form of one elimination step on a vector supported strictly below the pivot
is the quadratic form of the matrix on the vector completed by `-s / m_kk` at the pivot, where
`s = (M y)_k`: the Schur-complement identity `yᵀ S y = zᵀ M z`. -/
theorem dotProduct_elimStep_mulVec {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ} (h : IsPosDefFrom M k)
    (hk : k < N) {y : Fin N → ℝ} (hy : ∀ i : Fin N, (i : ℕ) < k + 1 → y i = 0) :
    y ⬝ᵥ elimStep M ⟨k, hk⟩ *ᵥ y =
      (y + Pi.single ⟨k, hk⟩ (-((M *ᵥ y) ⟨k, hk⟩ / M ⟨k, hk⟩ ⟨k, hk⟩))) ⬝ᵥ
        M *ᵥ (y + Pi.single ⟨k, hk⟩ (-((M *ᵥ y) ⟨k, hk⟩ / M ⟨k, hk⟩ ⟨k, hk⟩))) := by
  set p : Fin N := ⟨k, hk⟩ with hp
  have hpp : M p p ≠ 0 := (h.diag_pos le_rfl).ne'
  set s := (M *ᵥ y) p with hs
  set c := -(s / M p p) with hc
  -- the column sum against `y` is `s`, by symmetry of the trailing block
  have hcol : ∑ i, y i * M i p = s := by
    rw [hs, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne (y i) 0 with h0 | h0
    · rw [h0, zero_mul, mul_zero]
    · have hi : k ≤ (i : ℕ) := le_of_not_gt fun hlt => h0 (hy i (hlt.trans (Nat.lt_succ_self k)))
      rw [h.1 i p hi le_rfl, mul_comm]
  -- the left-hand side
  have hL : y ⬝ᵥ elimStep M p *ᵥ y = y ⬝ᵥ M *ᵥ y - s * (M p p)⁻¹ * s := by
    rw [elimStep, sub_mulVec, dotProduct_sub, ← mulVec_mulVec]
    congr 1
    have hterm : ∀ i, y i * (elimMultipliers M p *ᵥ (M *ᵥ y)) i =
        y i * M i p * (M p p)⁻¹ * s := by
      intro i
      rw [mulVec, dotProduct, Finset.sum_eq_single p (fun j _ hj => by simp [hj]) (by simp)]
      simp only [elimMultipliers_apply, and_true, ← hs]
      split_ifs with hpi
      · ring
      · rw [hy i (Nat.lt_succ_of_le (Fin.le_def.1 (not_lt.1 hpi)))]
        ring
    rw [dotProduct]
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hcol]
  -- the right-hand side
  have hR : (y + Pi.single p c) ⬝ᵥ M *ᵥ (y + Pi.single p c) =
      y ⬝ᵥ M *ᵥ y + c * s + c * s + c * (M p p * c) := by
    simp only [mulVec_add, mulVec_single, add_dotProduct, dotProduct_add, single_dotProduct]
    have h1 : y ⬝ᵥ (MulOpposite.op c • M.col p) = c * s := by
      rw [← hcol, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
    rw [h1]
    simp only [Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, ← hs]
    ring
  rw [hL, hR, hc]
  field_simp
  ring

/-- One elimination step at the pivot `k` of a matrix positive definite from `k` is positive
definite from `k + 1`: the trailing block of the step is a Schur complement. -/
theorem IsPosDefFrom.elimStep {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ} (h : IsPosDefFrom M k)
    (hk : k < N) : IsPosDefFrom (elimStep M ⟨k, hk⟩) (k + 1) := by
  set p : Fin N := ⟨k, hk⟩ with hp
  refine ⟨fun i j hi hj => ?_, fun y hy hy0 => ?_⟩
  · have hi' : p < i := Fin.lt_def.2 (Nat.lt_of_succ_le hi)
    have hj' : p < j := Fin.lt_def.2 (Nat.lt_of_succ_le hj)
    rw [elimStep_apply_of_lt _ hi', elimStep_apply_of_lt _ hj',
      h.1 i j (Nat.le_of_succ_le hi) (Nat.le_of_succ_le hj), h.1 i p (Nat.le_of_succ_le hi) le_rfl,
      h.1 j p (Nat.le_of_succ_le hj) le_rfl]
    ring
  · rw [dotProduct_elimStep_mulVec h hk hy]
    refine h.2 _ (fun i hi => ?_) fun h0 => hy0 ?_
    · have hip : i ≠ p := fun e => by rw [e] at hi; exact lt_irrefl _ hi
      rw [Pi.add_apply, hy i (hi.trans (Nat.lt_succ_self k)), Pi.single_eq_of_ne hip, add_zero]
    · ext i
      have := congrFun h0 i
      rcases eq_or_ne i p with hip | hip
      · rw [hip]
        exact hy p (Nat.lt_succ_self k)
      · rwa [Pi.add_apply, Pi.single_eq_of_ne hip, add_zero] at this

/-- The diagonal entries do not increase along an elimination step at a positive pivot:
`m_ii - m_ik² / m_kk ≤ m_ii`. -/
theorem IsPosDefFrom.elimStep_apply_self_le {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ}
    (h : IsPosDefFrom M k) (hk : k < N) {i : Fin N} (hi : k + 1 ≤ (i : ℕ)) :
    Matrix.elimStep M ⟨k, hk⟩ i i ≤ M i i := by
  set p : Fin N := ⟨k, hk⟩ with hp
  rw [elimStep_apply_of_lt _ (Fin.lt_def.2 (Nat.lt_of_succ_le hi)),
    h.1 p i le_rfl (Nat.le_of_succ_le hi), mul_right_comm]
  have : 0 ≤ M i p * M i p * (M p p)⁻¹ :=
    mul_nonneg (mul_self_nonneg _) (inv_nonneg.2 (h.diag_pos le_rfl).le)
  linarith

variable {A : Matrix (Fin N) (Fin N) ℝ}

/-- Every stage of Gaussian elimination on a positive definite matrix is positive definite from
its pivot index on ([higham2002accuracy] §10.1.1: the trailing blocks are Schur complements). -/
theorem PosDef.isPosDefFrom_gemStage (hA : A.PosDef) (k : ℕ) :
    IsPosDefFrom (gemStage A k) k := by
  induction k with
  | zero => exact hA.isPosDefFrom_zero
  | succ k ih =>
    by_cases hk : k < N
    · rw [gemStage_succ_of_lt A hk]
      exact ih.elimStep hk
    · rw [gemStage_succ_of_le A (not_lt.1 hk)]
      exact ih.mono (Nat.le_succ k)

/-- The pivots of Gaussian elimination on a positive definite matrix are positive. -/
theorem PosDef.gemStage_pivot_pos (hA : A.PosDef) {k : ℕ} (hk : k < N) :
    0 < gemStage A k ⟨k, hk⟩ ⟨k, hk⟩ :=
  (hA.isPosDefFrom_gemStage k).diag_pos le_rfl

/-- The diagonal entries of the stages of Gaussian elimination on a positive definite matrix
never exceed those of the matrix. -/
theorem PosDef.gemStage_apply_self_le (hA : A.PosDef) (k : ℕ) {i : Fin N} (hi : k ≤ (i : ℕ)) :
    gemStage A k i i ≤ A i i := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hk : k < N
    · rw [gemStage_succ_of_lt A hk]
      exact ((hA.isPosDefFrom_gemStage k).elimStep_apply_self_le hk hi).trans
        (ih (Nat.le_of_succ_le hi))
    · rw [gemStage_succ_of_le A (not_lt.1 hk)]
      exact ih (Nat.le_of_succ_le hi)

/-- On a positive definite matrix no entry of any stage exceeds the largest entry of the matrix,
in the rows at or below the pivot. -/
theorem PosDef.abs_gemStage_le_supAbs_of_le (hA : A.PosDef) {k : ℕ} {i : Fin N}
    (hki : k ≤ (i : ℕ)) (j : Fin N) : |gemStage A k i j| ≤ A.supAbs := by
  rcases le_or_gt k j with hkj | hjk
  · calc |gemStage A k i j|
        ≤ max (gemStage A k i i) (gemStage A k j j) :=
          (hA.isPosDefFrom_gemStage k).abs_apply_le_max hki hkj
      _ ≤ max (A i i) (A j j) :=
          max_le_max (hA.gemStage_apply_self_le k hki) (hA.gemStage_apply_self_le k hkj)
      _ ≤ A.supAbs :=
          max_le ((le_abs_self _).trans (abs_apply_le_supAbs A i i))
            ((le_abs_self _).trans (abs_apply_le_supAbs A j j))
  · rw [gemStage_apply_eq_zero_of_lt A (fun m hm _ _ => (hA.gemStage_pivot_pos hm).ne') hjk
      (Fin.lt_def.2 (hjk.trans_le hki)), abs_zero]
    exact supAbs_nonneg A

/-- On a positive definite matrix no entry of any stage exceeds the largest entry of the
matrix. -/
theorem PosDef.abs_gemStage_le_supAbs (hA : A.PosDef) (k : ℕ) (i j : Fin N) :
    |gemStage A k i j| ≤ A.supAbs := by
  rcases le_or_gt k i with hki | hik
  · exact hA.abs_gemStage_le_supAbs_of_le hki j
  · rw [gemStage_apply_of_le A (le_refl (i : ℕ)) hik.le]
    exact hA.abs_gemStage_le_supAbs_of_le le_rfl j

/-- **No growth on positive definite matrices**: the growth factor of Gaussian elimination
without pivoting on a symmetric positive definite matrix is at most `1`. -/
theorem growthFactor_le_one_of_posDef (hA : A.PosDef) : growthFactor A ≤ 1 :=
  growthFactor_le_of_forall_abs_le A zero_le_one fun k i j _ => by
    simpa using hA.abs_gemStage_le_supAbs k i j

/-- **[quarteroni2000numerical] §3.10 (3)**, [higham2002accuracy] §10.1.1: for a symmetric
positive definite matrix of positive order, the growth factor of Gaussian elimination without
pivoting is exactly `1`. Every stage's trailing block is again positive definite, so its entries
are bounded by its diagonal, and the diagonal entries decrease from stage to stage. The order
must be positive: the growth factor of the empty matrix is the junk value `0`. -/
theorem growthFactor_eq_one_of_posDef (hA : A.PosDef) (hN : 0 < N) : growthFactor A = 1 := by
  refine le_antisymm (growthFactor_le_one_of_posDef hA) (one_le_growthFactor A fun h0 => ?_)
  have := hA.diag_pos (i := ⟨0, hN⟩)
  rw [h0] at this
  simp at this

end PosDef

/-! ### Column diagonally dominant matrices: growth at most two -/

section ColDiagDominant

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

/-- The pivots of Gaussian elimination on a nonsingular column diagonally dominant matrix are
nonzero: the factorization exists (`Matrix.exists_isLU_of_isColDiagDominant`) and
`det A = ∏ u_ii`. -/
theorem gemStage_pivot_ne_zero_of_isColDiagDominant (hu : IsUnit A) (hA : A.IsColDiagDominant)
    {k : ℕ} (hk : k < N) : gemStage A k ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0 := by
  obtain ⟨L, U, hLU, -⟩ := exists_isLU_of_isColDiagDominant hu hA
  have hdet : A.det ≠ 0 := isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det A).1 hu)
  have hA' : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) := by
    intro k
    rw [isUnit_iff_isUnit_det, hLU.det_strictLeadingPrincipalSubmatrix, isUnit_iff_ne_zero]
    have hU := hdet
    rw [hLU.det_eq_prod_diag] at hU
    exact Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.1 hU i (mem_univ _)
  have hpiv := (gemStage_pivots_ne_zero_iff A).2 hA'
  have hdet' := hdet
  rw [(isLU_gemLower_gemStage A hpiv).det_eq_prod_diag] at hdet'
  have := Finset.prod_ne_zero_iff.1 hdet' ⟨k, hk⟩ (mem_univ _)
  rwa [gemStage_apply_of_le A (le_refl k) hk.le] at this

/-- The rows `≥ k` are the row `k` and the rows `≥ k + 1`. -/
theorem filter_le_eq_insert_filter_succ_le {k : ℕ} (hk : k < N) :
    (univ.filter fun i : Fin N => k ≤ (i : ℕ)) =
      insert ⟨k, hk⟩ (univ.filter fun i : Fin N => k + 1 ≤ (i : ℕ)) := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

/-- The rows `≥ k` other than `k` are the rows `≥ k + 1`. -/
theorem filter_le_erase_eq_filter_succ_le {k : ℕ} (hk : k < N) :
    (univ.filter fun i : Fin N => k ≤ (i : ℕ)).erase ⟨k, hk⟩ =
      univ.filter fun i : Fin N => k + 1 ≤ (i : ℕ) := by
  ext i
  simp only [mem_erase, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]
  omega

/-- **The invariant of Gaussian elimination on a column diagonally dominant matrix**
([higham2002accuracy] Theorem 9.9, after Wilkinson): at every stage the trailing block is
column diagonally dominant, and the column sums of the trailing block do not exceed those of
`A`. The dominance of the trailing block is the Schur-complement lemma
`Matrix.IsColDiagDominant.sum_norm_sub_le`, applied to the stage with its finished rows replaced
by zeros. -/
theorem gemStage_isColDiagDominant_invariant (hu : IsUnit A) (hA : A.IsColDiagDominant) (k : ℕ) :
    (∀ j : Fin N, k ≤ (j : ℕ) →
      ∑ i ∈ (univ.filter fun i : Fin N => k ≤ (i : ℕ)).erase j, |gemStage A k i j| ≤
        |gemStage A k j j|) ∧
    ∀ j : Fin N, ∑ i ∈ univ.filter (fun i : Fin N => k ≤ (i : ℕ)), |gemStage A k i j| ≤
      ∑ i, |A i j| := by
  induction k with
  | zero =>
    refine ⟨fun j _ => ?_, fun j => le_of_eq ?_⟩
    · have := hA j
      simpa [Real.norm_eq_abs] using this
    · simp
  | succ k ih =>
    by_cases hk : k < N
    swap
    · have hempty : (univ.filter fun i : Fin N => k + 1 ≤ (i : ℕ)) = ∅ := by
        ext i
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_le]
        exact i.2.trans_le (Nat.le_succ_of_le (not_lt.1 hk))
      refine ⟨fun j hj => absurd (hj.trans_lt j.2) (by omega), fun j => ?_⟩
      rw [hempty, Finset.sum_empty]
      exact Finset.sum_nonneg fun i _ => abs_nonneg _
    obtain ⟨ha, hb⟩ := ih
    set p : Fin N := ⟨k, hk⟩ with hp
    set M := gemStage A k with hM
    have hpp : M p p ≠ 0 := gemStage_pivot_ne_zero_of_isColDiagDominant hu hA hk
    have hstep : gemStage A (k + 1) = elimStep M p := gemStage_succ_of_lt A hk
    have hcolp : ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i p| ≤ |M p p| := by
      rw [← filter_le_erase_eq_filter_succ_le hk]
      exact ha p le_rfl
    have hlt : ∀ i : Fin N, k + 1 ≤ (i : ℕ) → p < i := fun i hi => Fin.lt_def.2 hi
    refine ⟨fun j hj => ?_, fun j => ?_⟩
    · -- column dominance of the trailing block, through the padded matrix `T`
      set T : Matrix (Fin N) (Fin N) ℝ := of fun i j => if k ≤ (i : ℕ) then M i j else 0 with hT
      have hTz : ∀ i j : Fin N, (i : ℕ) < k → T i j = 0 := fun i j hi => by
        simp [hT, not_le.2 hi]
      have hTe : ∀ i j : Fin N, k ≤ (i : ℕ) → T i j = M i j := fun i j hi => by
        simp [hT, hi]
      have hTdom : T.IsColDiagDominant := by
        intro j
        simp only [Real.norm_eq_abs]
        rcases le_or_gt k j with hkj | hjk
        · rw [hTe j j hkj, ← Finset.sum_filter_of_ne (p := fun i : Fin N => k ≤ (i : ℕ))
            (fun i _ hi => by
              by_contra hik
              exact hi (by rw [hTz i j (not_le.1 hik), abs_zero])),
            Finset.filter_erase]
          refine (Finset.sum_le_sum fun i hi => ?_).trans (ha j hkj)
          rw [hTe i j (mem_filter.1 (mem_erase.1 hi).2).2]
        · rw [hTz j j hjk, abs_zero]
          refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
          by_cases hik : k ≤ (i : ℕ)
          · have h0 : M i j = 0 := gemStage_apply_eq_zero_of_lt A
              (fun m hm _ _ => gemStage_pivot_ne_zero_of_isColDiagDominant hu hA hm) hjk
              (Fin.lt_def.2 (hjk.trans_le hik))
            rw [hTe i j hik, h0, abs_zero]
          · rw [hTz i j (not_le.1 hik), abs_zero]
      have key := hTdom.sum_norm_sub_le (p := p) (j := j) (by rwa [hTe p p le_rfl])
        (hlt j hj).ne'
      simp only [Real.norm_eq_abs, hTe j j (Nat.le_of_succ_le hj), hTe j p (Nat.le_of_succ_le hj),
        hTe p p le_rfl, hTe p j le_rfl] at key
      rw [hstep, elimStep_apply_of_lt _ (hlt j hj)]
      refine le_trans (le_of_eq ?_) key
      rw [← Finset.sum_filter_of_ne (s := (univ.erase p).erase j)
        (p := fun i : Fin N => k ≤ (i : ℕ)) fun i _ hi => ?_]
      · have hset : ((univ.erase p).erase j).filter (fun i : Fin N => k ≤ (i : ℕ)) =
            (univ.filter fun i : Fin N => k + 1 ≤ (i : ℕ)).erase j := by
          ext i
          simp only [mem_filter, mem_erase, mem_univ, true_and, and_true]
          constructor
          · rintro ⟨⟨hij, hip⟩, hki⟩
            exact ⟨hij, Nat.lt_of_le_of_ne hki fun e => hip (Fin.ext e.symm)⟩
          · rintro ⟨hij, hki⟩
            exact ⟨⟨hij, fun e => by
              rw [e] at hki; exact absurd hki (by rw [hp]; exact Nat.not_succ_le_self k)⟩,
              Nat.le_of_succ_le hki⟩
        rw [hset]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := (mem_filter.1 (mem_erase.1 hi).2).2
        rw [elimStep_apply_of_lt _ (hlt i hi'), hTe i j (Nat.le_of_succ_le hi'),
          hTe i p (Nat.le_of_succ_le hi')]
      · by_contra hik
        rw [hTz i j (not_le.1 hik), hTz i p (not_le.1 hik)] at hi
        simp at hi
    · -- the column sums of the trailing block do not increase
      have hb' := hb j
      rw [filter_le_eq_insert_filter_succ_le hk, Finset.sum_insert (by simp)] at hb'
      rw [hstep]
      refine le_trans ?_ hb'
      calc ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |elimStep M p i j|
          ≤ ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)),
              (|M i j| + |M i p| * |M p p|⁻¹ * |M p j|) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [elimStep_apply_of_lt _ (hlt i (mem_filter.1 hi).2)]
            refine (abs_sub _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_inv]
        _ = ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i j| +
              (∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i p|) * |M p p|⁻¹ *
                |M p j| := by
            rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
        _ ≤ ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i j| +
              |M p p| * |M p p|⁻¹ * |M p j| := by gcongr
        _ = |M p j| + ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i j| := by
            rw [mul_inv_cancel₀ (abs_ne_zero.2 hpp), one_mul, add_comm]

/-- On a nonsingular column diagonally dominant matrix, no entry of any stage of Gaussian
elimination exceeds twice the largest entry of the matrix: a column sum of the trailing block is
at most the column sum of `A`, which is at most `2 |a_jj|` by dominance. -/
theorem abs_gemStage_le_two_mul_supAbs_of_isColDiagDominant (hu : IsUnit A)
    (hA : A.IsColDiagDominant) (k : ℕ) (i j : Fin N) :
    |gemStage A k i j| ≤ 2 * A.supAbs := by
  have hcol : ∀ k, ∀ i : Fin N, k ≤ (i : ℕ) → |gemStage A k i j| ≤ 2 * A.supAbs := by
    intro k i hki
    have h1 : |gemStage A k i j| ≤ ∑ i' ∈ univ.filter (fun i : Fin N => k ≤ (i : ℕ)),
        |gemStage A k i' j| :=
      Finset.single_le_sum (f := fun i' => |gemStage A k i' j|) (fun _ _ => abs_nonneg _)
        (mem_filter.2 ⟨mem_univ _, hki⟩)
    have h2 := (gemStage_isColDiagDominant_invariant hu hA k).2 j
    have h3 : ∑ i', |A i' j| ≤ 2 * A.supAbs := by
      rw [← Finset.add_sum_erase _ _ (mem_univ j), two_mul]
      have := hA j
      simp only [Real.norm_eq_abs] at this
      exact add_le_add (abs_apply_le_supAbs A j j) (this.trans (abs_apply_le_supAbs A j j))
    exact h1.trans (h2.trans h3)
  rcases le_or_gt k i with hki | hik
  · exact hcol k i hki
  · rw [gemStage_apply_of_le A (le_refl (i : ℕ)) hik.le]
    exact hcol i i le_rfl

/-- **[quarteroni2000numerical] §3.10 (4)**, [higham2002accuracy] Theorem 9.9 (Wilkinson): the
growth factor of Gaussian elimination without pivoting on a nonsingular matrix diagonally
dominant by columns is at most `2`. Weak dominance suffices (the book says "strictly"), and
partial pivoting would perform no interchange, the multipliers being bounded by `1`
(`Matrix.exists_isLU_of_isColDiagDominant`). -/
theorem growthFactor_le_two_of_isColDiagDominant (hu : IsUnit A) (hA : A.IsColDiagDominant) :
    growthFactor A ≤ 2 :=
  growthFactor_le_of_forall_abs_le A zero_le_two fun k i j _ =>
    abs_gemStage_le_two_mul_supAbs_of_isColDiagDominant hu hA k i j

end ColDiagDominant

/-! ### Partial pivoting on Hessenberg and tridiagonal matrices -/

section Hessenberg

variable {N : ℕ}

/-- The largest entry is invariant under a permutation of the rows. -/
theorem supAbs_submatrix_equiv {m : Type*} [Finite m] (A : Matrix m m ℝ) (σ : Equiv.Perm m) :
    (A.submatrix σ id).supAbs = A.supAbs := by
  refine le_antisymm (supAbs_le (supAbs_nonneg A) fun i j => abs_apply_le_supAbs A (σ i) j)
    (supAbs_le (supAbs_nonneg _) fun i j => ?_)
  have := abs_apply_le_supAbs (A.submatrix σ id) (σ.symm i) j
  simpa using this

/-- `|a / b| ≤ 1` when `|a| ≤ |b|`, the case `b = 0` included (junk division). -/
theorem abs_div_le_one_of_abs_le {a b : ℝ} (h : |a| ≤ |b|) : |a / b| ≤ 1 := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · rw [abs_div, div_le_one (abs_pos.2 hb)]
    exact h

/-- When the rows more than `b` below `p` vanish in column `p`, partial pivoting chooses a row at
most `b` below `p`: a pivot further down would be zero, so the whole column below `p` would vanish
and the first maximal row would be `p` itself. -/
theorem partialPivotRow_le_add {𝕜 : Type*} [NormedField 𝕜] (M : Matrix (Fin N) (Fin N) 𝕜)
    (p : Fin N) (b : ℕ) (h : ∀ i : Fin N, (p : ℕ) + b < i → M i p = 0) :
    ((partialPivotRow M p : Fin N) : ℕ) ≤ (p : ℕ) + b := by
  by_contra hlt
  push Not at hlt
  have h0 : M (partialPivotRow M p) p = 0 := h _ hlt
  have hself := partialPivotRow_eq_self_of_forall_eq_zero M p fun r hr =>
    apply_eq_zero_of_partialPivotRow_eq_zero M p h0 hr
  rw [hself] at hlt
  omega

/-- When the rows more than one below `p` vanish in column `p`, partial pivoting chooses the
row `p` or the row `p + 1`, the case `b = 1` of `Matrix.partialPivotRow_le_add`. -/
theorem partialPivotRow_le_succ {𝕜 : Type*} [NormedField 𝕜] (M : Matrix (Fin N) (Fin N) 𝕜)
    (p : Fin N) (h : ∀ i : Fin N, (p : ℕ) + 1 < i → M i p = 0) :
    ((partialPivotRow M p : Fin N) : ℕ) ≤ (p : ℕ) + 1 :=
  partialPivotRow_le_add M p 1 h

variable {A : Matrix (Fin N) (Fin N) ℝ}

/-- **The shape invariant of partial pivoting on an upper Hessenberg matrix**
([higham2002accuracy], proof of Theorem 9.10): at the start of stage `k`, the rows below `k`
are the original rows of `A`, and the entries of the rows `i ≤ k` are bounded by `(i + 1)` times
the largest entry of `A`. Each stage swaps at most the rows `k` and `k + 1` and adds a multiple
of modulus at most one of the pivot row to the row `k + 1`. -/
theorem gemPivotStage_partialPivotRow_isUpperHessenberg_invariant (hA : A.IsUpperHessenberg)
    (k : ℕ) :
    (∀ i j : Fin N, k < (i : ℕ) → (gemPivotStage A partialPivotRow k).1 i j = A i j) ∧
      ∀ i j : Fin N, (i : ℕ) ≤ k →
        |(gemPivotStage A partialPivotRow k).1 i j| ≤ ((i : ℕ) + 1) * A.supAbs := by
  have hμ := supAbs_nonneg A
  induction k with
  | zero =>
    refine ⟨fun i j _ => rfl, fun i j hi => ?_⟩
    have : (i : ℕ) = 0 := by omega
    rw [gemPivotStage_zero]
    simp only [this, Nat.cast_zero, zero_add, one_mul]
    exact abs_apply_le_supAbs A i j
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact ⟨fun i j hi => h1 i j (by omega), fun i j _ => h2 i j (by omega)⟩
    set p : Fin N := ⟨k, hk⟩ with hp
    have hpk : (p : ℕ) = k := rfl
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M p with hrdef
    have hM1 : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap p r) id) p := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    set M' := M.submatrix (Equiv.swap p r) id with hM'
    -- the rows more than one below `p` vanish in column `p`, so `r ∈ {k, k + 1}`
    have hcol : ∀ i : Fin N, (p : ℕ) + 1 < i → M i p = 0 := fun i hi => by
      rw [h1 i p (by omega)]
      exact hA i p ⟨⟨k + 1, by omega⟩, Fin.lt_def.2 (by rw [hpk]; simp),
        Fin.lt_def.2 (by simp only; omega)⟩
    have hr : (r : ℕ) ≤ k + 1 := partialPivotRow_le_succ M p hcol
    have hkr : k ≤ (r : ℕ) := le_partialPivotRow M p
    -- the rows of the swapped matrix
    have hM'_of : ∀ i : Fin N, i ≠ p → i ≠ r → ∀ j, M' i j = M i j := fun i hip hir j => by
      simp [hM', Equiv.swap_apply_of_ne_of_ne hip hir]
    have hM'p : ∀ j, M' p j = M r j := fun j => by simp [hM']
    have hrow_p : ∀ j, |M r j| ≤ ((k : ℕ) + 1) * A.supAbs := fun j => by
      rcases hkr.eq_or_lt with hrk | hrk
      · have : r = p := Fin.ext hrk.symm
        rw [this]
        exact h2 p j le_rfl
      · rw [h1 r j hrk]
        calc |A r j| ≤ A.supAbs := abs_apply_le_supAbs A r j
          _ ≤ ((k : ℕ) + 1) * A.supAbs := le_mul_of_one_le_left hμ (by linarith)
    refine ⟨fun i j hi => ?_, fun i j hi => ?_⟩
    · -- rows below `k + 1` are untouched
      have hip : i ≠ p := fun e => by rw [e] at hi; omega
      have hir : i ≠ r := fun e => by rw [e] at hi; omega
      rw [hM1, elimStep_apply_of_lt _ (Fin.lt_def.2 (by omega)),
        hM'_of i hip hir, hM'_of i hip hir, h1 i p (by omega), h1 i j (by omega),
        hA i p ⟨⟨k + 1, by omega⟩, Fin.lt_def.2 (by rw [hpk]; simp),
          Fin.lt_def.2 (by simp only; omega)⟩]
      ring
    · rcases Nat.lt_or_ge (i : ℕ) (k + 1) with hik | hik
      · -- rows at or above the pivot: unchanged by the elimination
        have hnlt : ¬ p < i := by simp only [Fin.lt_def]; omega
        rw [hM1, elimStep_apply_of_not_lt _ hnlt]
        rcases Nat.lt_or_ge (i : ℕ) k with hik' | hik'
        · have hip : i ≠ p := fun e => by rw [e] at hik'; omega
          have hir : i ≠ r := fun e => by rw [e] at hik'; omega
          rw [hM'_of i hip hir]
          exact h2 i j hik'.le
        · have hip : i = p := Fin.ext (by omega)
          rw [hip, hM'p, hpk]
          exact hrow_p j
      · -- the new working row `k + 1`
        have hiq : (i : ℕ) = k + 1 := by omega
        have hpi : p < i := Fin.lt_def.2 (by omega)
        rw [hM1, elimStep_apply_of_lt _ hpi, ← div_eq_mul_inv]
        -- the multiplier has modulus at most one
        have hτi : (p : ℕ) ≤ (Equiv.swap p r i : ℕ) := by
          rcases eq_or_ne r p with hrp | hrp
          · rw [hrp, Equiv.swap_self]
            simp only [Equiv.refl_apply]
            omega
          · have hir : i = r := Fin.ext (by omega)
            rw [hir, Equiv.swap_apply_right]
        have hmul : |M' i p / M' p p| ≤ 1 := by
          refine abs_div_le_one_of_abs_le ?_
          rw [hM'p]
          simp only [hM', submatrix_apply, id]
          have := norm_apply_le_partialPivotRow M p (Fin.le_def.2 hτi)
          simpa [Real.norm_eq_abs] using this
        -- the two rows involved are the working row and the original row `k + 1`
        have hsum : |M' i j| + |M' p j| ≤ ((k : ℕ) + 1) * A.supAbs + A.supAbs := by
          have hpk' : ((p : ℕ) : ℝ) = k := by rw [hpk]
          rcases eq_or_ne r p with hrp | hrp
          · have hip : i ≠ p := fun e => by rw [e] at hiq; omega
            have hir : i ≠ r := fun e => by rw [hrp] at e; exact hip e
            rw [hM'_of i hip hir, hM'p, h1 i j (by omega), hrp]
            have := h2 p j le_rfl
            rw [hpk'] at this
            linarith [abs_apply_le_supAbs A i j]
          · have hir : i = r := Fin.ext (by omega)
            rw [hM'p, hir]
            simp only [hM', submatrix_apply, Equiv.swap_apply_right, id]
            rw [h1 r j (by omega)]
            have := h2 p j le_rfl
            rw [hpk'] at this
            linarith [abs_apply_le_supAbs A r j]
        calc |M' i j - M' i p / M' p p * M' p j|
            ≤ |M' i j| + |M' i p / M' p p| * |M' p j| := by
              rw [← abs_mul]
              exact abs_sub _ _
          _ ≤ |M' i j| + 1 * |M' p j| :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right hmul (abs_nonneg _))
          _ ≤ ((k : ℕ) + 1) * A.supAbs + A.supAbs := by rw [one_mul]; exact hsum
          _ = ((i : ℕ) + 1) * A.supAbs := by rw [hiq]; push_cast; ring

/-- **[quarteroni2000numerical] §3.10 (2)**, [higham2002accuracy] Theorem 9.10 (Wilkinson):
the growth factor of Gaussian elimination with partial pivoting on an upper Hessenberg matrix of
order `N` is at most `N`. Every entry of every stage is bounded by `N` times the largest entry
of `A`, by the shape invariant `Matrix.gemPivotStage_partialPivotRow_isUpperHessenberg_invariant`;
the stages of the pivoted elimination are those of the plain elimination on `P A` up to the
order of the rows. -/
theorem growthFactor_le_card_of_isUpperHessenberg (hA : A.IsUpperHessenberg) :
    growthFactor ((gemPivotStage A partialPivotRow N).2.permMatrix ℝ * A) ≤ N := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) ℝ) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  have hμ := supAbs_nonneg A
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  refine growthFactor_le_of_forall_abs_le _ (Nat.cast_nonneg N) fun k i j hk => ?_
  rw [supAbs_submatrix_equiv, gemStage_submatrix_eq_submatrix_gemPivotStage A partialPivotRow
    hpiv k, submatrix_apply, id_eq]
  obtain ⟨h1, h2⟩ := gemPivotStage_partialPivotRow_isUpperHessenberg_invariant hA k
  set i' := ((gemPivotStage A partialPivotRow k).2⁻¹ * (gemPivotStage A partialPivotRow N).2) i
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact i.elim0)
  rcases le_or_gt (i' : ℕ) k with hi | hi
  · refine (h2 i' j hi).trans (mul_le_mul_of_nonneg_right ?_ hμ)
    exact_mod_cast i'.2
  · rw [h1 i' j hi]
    exact (abs_apply_le_supAbs A i' j).trans (le_mul_of_one_le_left hμ hN)

end Hessenberg

section Tridiagonal

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

/-- After a stage of partial pivoting the pivot column vanishes below the pivot, whether or
not the pivot itself is zero: a zero pivot means a zero column. -/
theorem gemPivotStage_partialPivotRow_succ_apply_pivot {k : ℕ} (hk : k < N) {i : Fin N}
    (hi : (⟨k, hk⟩ : Fin N) < i) :
    (gemPivotStage A partialPivotRow (k + 1)).1 i ⟨k, hk⟩ = 0 := by
  set p : Fin N := ⟨k, hk⟩ with hp
  set M := (gemPivotStage A partialPivotRow k).1 with hM
  set r := partialPivotRow M p with hrdef
  rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
  change elimStep (M.submatrix (Equiv.swap p r) id) p i p = 0
  rcases eq_or_ne (M.submatrix (Equiv.swap p r) id p p) 0 with h0 | h0
  · have hcol : ∀ i : Fin N, p ≤ i → M i p = 0 := fun i hi => by
      refine apply_eq_zero_of_partialPivotRow_eq_zero M p ?_ hi
      simpa using h0
    rw [elimStep_apply_of_lt _ hi, h0, submatrix_apply, id_eq, hcol _ ?_]
    · ring
    · rcases eq_or_ne r p with hrp | hrp
      · rw [hrp, Equiv.swap_self, Equiv.refl_apply]
        exact hi.le
      · rcases eq_or_ne i r with hir | hir
        · rw [hir, Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne hi.ne' hir]
          exact hi.le
  · exact elimStep_apply_pivot _ hi h0

/-- **The shape invariant of partial pivoting on a tridiagonal matrix** ([higham2002accuracy]
§9.5, "the easily verified result that for a tridiagonal matrix `ρ_n^p ≤ 2`"): at the start of
stage `k`, the working row `k` is supported on the columns `k`, `k + 1`, with `|a^{(k)}_{kk}| ≤ 2μ`
and every other entry at most `μ`, the largest entry of `A`; the finished rows are bounded by
`2μ`; and the rows below `k` are the original rows
(`Matrix.gemPivotStage_partialPivotRow_isUpperHessenberg_invariant`). -/
theorem gemPivotStage_partialPivotRow_isTridiagonal_invariant (hA : A.IsTridiagonal) (k : ℕ) :
    (∀ hk : k < N,
      |(gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ ⟨k, hk⟩| ≤ 2 * A.supAbs ∧
      (∀ j, j ≠ ⟨k, hk⟩ → |(gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ j| ≤ A.supAbs) ∧
      ∀ j : Fin N, (j : ℕ) ≠ k → (j : ℕ) ≠ k + 1 →
        (gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ j = 0) ∧
    ∀ i j : Fin N, (i : ℕ) < k → |(gemPivotStage A partialPivotRow k).1 i j| ≤ 2 * A.supAbs := by
  have hμ := supAbs_nonneg A
  induction k with
  | zero =>
    refine ⟨fun hk => ⟨?_, fun j _ => ?_, fun j hj0 hj1 => ?_⟩, fun i j hi => absurd hi (by omega)⟩
    · rw [gemPivotStage_zero]
      exact (abs_apply_le_supAbs A _ _).trans (le_mul_of_one_le_left hμ one_le_two)
    · rw [gemPivotStage_zero]
      exact abs_apply_le_supAbs A _ _
    · rw [gemPivotStage_zero]
      exact hA _ j (Or.inr ⟨⟨1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩)
  | succ k ih =>
    obtain ⟨hT2, hT3⟩ := ih
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact ⟨fun hk' => absurd hk' (by omega), fun i j _ => hT3 i j (by omega)⟩
    obtain ⟨h2a, h2b, h2c⟩ := hT2 hk
    have h1 := (gemPivotStage_partialPivotRow_isUpperHessenberg_invariant hA.isUpperHessenberg k).1
    set p : Fin N := ⟨k, hk⟩ with hp
    have hpk : (p : ℕ) = k := rfl
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M p with hrdef
    have hM1 : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap p r) id) p := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    set M' := M.submatrix (Equiv.swap p r) id with hM'
    have hcol : ∀ i : Fin N, (p : ℕ) + 1 < i → M i p = 0 := fun i hi => by
      rw [h1 i p (by omega)]
      exact hA.isUpperHessenberg i p ⟨⟨k + 1, by omega⟩, Fin.lt_def.2 (by rw [hpk]; simp),
        Fin.lt_def.2 (by simp only; omega)⟩
    have hr : (r : ℕ) ≤ k + 1 := partialPivotRow_le_succ M p hcol
    have hkr : k ≤ (r : ℕ) := le_partialPivotRow M p
    have hM'_of : ∀ i : Fin N, i ≠ p → i ≠ r → ∀ j, M' i j = M i j := fun i hip hir j => by
      simp [hM', Equiv.swap_apply_of_ne_of_ne hip hir]
    have hM'p : ∀ j, M' p j = M r j := fun j => by simp [hM']
    -- the working row is bounded by `2μ`
    have hrow_p : ∀ j, |M p j| ≤ 2 * A.supAbs := fun j => by
      rcases eq_or_ne j p with rfl | hj
      · exact h2a
      · exact (h2b j hj).trans (le_mul_of_one_le_left hμ one_le_two)
    have hrow_r : ∀ j, |M r j| ≤ 2 * A.supAbs := fun j => by
      rcases hkr.eq_or_lt with hrk | hrk
      · have : r = p := Fin.ext hrk.symm
        rw [this]
        exact hrow_p j
      · rw [h1 r j hrk]
        exact (abs_apply_le_supAbs A r j).trans (le_mul_of_one_le_left hμ one_le_two)
    refine ⟨fun hk1 => ?_, fun i j hi => ?_⟩
    swap
    · -- the finished rows
      have hnlt : ¬ p < i := by simp only [Fin.lt_def]; omega
      rw [hM1, elimStep_apply_of_not_lt _ hnlt]
      rcases Nat.lt_or_ge (i : ℕ) k with hik' | hik'
      · have hip : i ≠ p := fun e => by rw [e] at hik'; omega
        have hir : i ≠ r := fun e => by rw [e] at hik'; omega
        rw [hM'_of i hip hir]
        exact hT3 i j hik'
      · have hip : i = p := Fin.ext (by omega)
        rw [hip, hM'p]
        exact hrow_r j
    -- the new working row `q = k + 1`
    set q : Fin N := ⟨k + 1, hk1⟩ with hq
    have hqk : (q : ℕ) = k + 1 := rfl
    have hpq : p < q := Fin.lt_def.2 (by omega)
    have hqp : q ≠ p := fun e => by rw [Fin.ext_iff] at e; omega
    -- the pair of rows involved, in either order
    have hpair : ∀ j, |M' q j| + |M' p j| = |M p j| + |A q j| := fun j => by
      rcases eq_or_ne r p with hrp | hrp
      · have hqr : q ≠ r := by rw [hrp]; exact hqp
        rw [hM'_of q hqp hqr, hM'p, hrp, h1 q j (by omega), add_comm]
      · have hqr : q = r := Fin.ext (by omega)
        rw [hM'p, ← hqr]
        simp only [hM', submatrix_apply, hqr, Equiv.swap_apply_right, id_eq]
        rw [← hqr, h1 q j (by omega)]
    have hmul : |M' q p / M' p p| ≤ 1 := by
      refine abs_div_le_one_of_abs_le ?_
      rw [hM'p]
      simp only [hM', submatrix_apply, id_eq]
      have hτq : p ≤ Equiv.swap p r q := by
        rcases eq_or_ne r p with hrp | hrp
        · rw [hrp, Equiv.swap_self, Equiv.refl_apply]
          exact hpq.le
        · have hqr : q = r := Fin.ext (by omega)
          rw [hqr, Equiv.swap_apply_right]
      have := norm_apply_le_partialPivotRow M p hτq
      simpa [Real.norm_eq_abs] using this
    have hentry : ∀ j, |(gemPivotStage A partialPivotRow (k + 1)).1 q j| ≤ |M p j| + |A q j| := by
      intro j
      rw [hM1, elimStep_apply_of_lt _ hpq, ← div_eq_mul_inv]
      calc |M' q j - M' q p / M' p p * M' p j|
          ≤ |M' q j| + |M' q p / M' p p| * |M' p j| := by
            rw [← abs_mul]
            exact abs_sub _ _
        _ ≤ |M' q j| + 1 * |M' p j| :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hmul (abs_nonneg _))
        _ = |M p j| + |A q j| := by rw [one_mul, hpair]
    have hpiv0 : (gemPivotStage A partialPivotRow (k + 1)).1 q p = 0 :=
      gemPivotStage_partialPivotRow_succ_apply_pivot hk hpq
    refine ⟨?_, fun j hjq => ?_, fun j hj1 hj2 => ?_⟩
    · -- the diagonal entry
      refine (hentry q).trans ?_
      have := h2b q hqp
      linarith [abs_apply_le_supAbs A q q]
    · -- the other entries of the working row
      rcases eq_or_ne j p with rfl | hjp
      · rw [hpiv0, abs_zero]
        exact hμ
      · have hw : M p j = 0 := h2c j (fun e => hjp (Fin.ext e)) fun e => hjq (Fin.ext e)
        refine (hentry j).trans ?_
        rw [hw, abs_zero, zero_add]
        exact abs_apply_le_supAbs A q j
    · -- the support of the working row
      rcases eq_or_ne j p with rfl | hjp
      · exact hpiv0
      · have hw : M p j = 0 := h2c j (fun e => hjp (Fin.ext e)) hj1
        have hAqj : A q j = 0 := by
          refine hA q j ?_
          rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
          · exact Or.inl ⟨p, Fin.lt_def.2 (by omega), hpq⟩
          · exact Or.inr ⟨⟨k + 2, by omega⟩, Fin.lt_def.2 (by simp only; omega),
              Fin.lt_def.2 (by simp only; omega)⟩
        have := hentry j
        rw [hw, hAqj, abs_zero, add_zero] at this
        exact abs_nonpos_iff.1 this

/-- **[quarteroni2000numerical] §3.10 (1), the tridiagonal case**, [higham2002accuracy] §9.5 (the
case `p = 1` of Bohte's Theorem 9.11): the growth factor of Gaussian elimination with partial
pivoting on a tridiagonal matrix is at most `2`. Every entry of every stage is at most twice the
largest entry of `A`, by the shape invariant
`Matrix.gemPivotStage_partialPivotRow_isTridiagonal_invariant`. -/
theorem growthFactor_le_two_of_isTridiagonal (hA : A.IsTridiagonal) :
    growthFactor ((gemPivotStage A partialPivotRow N).2.permMatrix ℝ * A) ≤ 2 := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) ℝ) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  have hμ := supAbs_nonneg A
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  refine growthFactor_le_of_forall_abs_le _ zero_le_two fun k i j hk => ?_
  rw [supAbs_submatrix_equiv, gemStage_submatrix_eq_submatrix_gemPivotStage A partialPivotRow
    hpiv k, submatrix_apply, id_eq]
  obtain ⟨hT2, hT3⟩ := gemPivotStage_partialPivotRow_isTridiagonal_invariant hA k
  obtain ⟨h2a, h2b, -⟩ := hT2 hk
  have h1 := (gemPivotStage_partialPivotRow_isUpperHessenberg_invariant hA.isUpperHessenberg k).1
  set i' := ((gemPivotStage A partialPivotRow k).2⁻¹ * (gemPivotStage A partialPivotRow N).2) i
  rcases lt_trichotomy (i' : ℕ) k with hi | hi | hi
  · exact hT3 i' j hi
  · have : i' = ⟨k, hk⟩ := Fin.ext hi
    rw [this]
    rcases eq_or_ne j ⟨k, hk⟩ with rfl | hj
    · exact h2a
    · exact (h2b j hj).trans (le_mul_of_one_le_left hμ one_le_two)
  · rw [h1 i' j hi]
    exact (abs_apply_le_supAbs A i' j).trans (le_mul_of_one_le_left hμ one_le_two)

end Tridiagonal

section Band

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {p q : ℕ}

/-- Once a column has been eliminated it stays zero below its diagonal entry, whether or not the
pivot was zero: under partial pivoting a zero pivot means a zero column, so no hypothesis on the
pivots is needed, unlike in `Matrix.gemStage_apply_eq_zero_of_lt`. -/
theorem gemPivotStage_partialPivotRow_apply_eq_zero_of_lt (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    ∀ i j : Fin N, (j : ℕ) < k → j < i → (gemPivotStage A partialPivotRow k).1 i j = 0 := by
  induction k with
  | zero => exact fun i j hj _ => absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro i j hj hji
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact ih i j (by omega) hji
    set P : Fin N := ⟨k, hk⟩ with hP
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M P with hr
    have hMk : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap P r) id) P := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
    · -- an earlier column: the pivot row is already zero there, so nothing changes
      have hPr : (P : ℕ) ≤ (r : ℕ) := le_partialPivotRow M P
      have hswap : ∀ i : Fin N, j < i → j < Equiv.swap P r i := by
        intro i hi
        rcases eq_or_ne i P with rfl | hiP
        · rw [Equiv.swap_apply_left]
          exact Fin.lt_def.2 (by omega)
        rcases eq_or_ne i r with rfl | hir
        · rw [Equiv.swap_apply_right]
          exact Fin.lt_def.2 (by omega)
        · rwa [Equiv.swap_apply_of_ne_of_ne hiP hir]
      have hrow : (M.submatrix (Equiv.swap P r) id) P j = 0 := by
        simp only [submatrix_apply, id_eq]
        exact ih _ j hjk (hswap P (Fin.lt_def.2 (by omega)))
      rw [hMk, elimStep_apply_of_pivot_row_eq_zero _ _ _ hrow, submatrix_apply, id_eq]
      exact ih _ j hjk (hswap i hji)
    · -- the column just eliminated
      have hjP : j = P := Fin.ext hjk
      subst hjP
      exact gemPivotStage_partialPivotRow_succ_apply_pivot hk hji

/-- **The shape invariant of partial pivoting on a banded matrix** ([higham2002accuracy] §9.5,
[quarteroni2000numerical] §3.10 (1)): if `A` has lower bandwidth `p` and upper bandwidth `q` then,
at the start of stage `k`, the rows `k + p` and below are still the original rows of `A` (they have
not met a pivot yet), and every row above them vanishes past the column `k + p + q`: the
interchanges widen the upper band from `q` to `p + q` and no further, because a pivot row is at
most `p` below the pivot index. -/
theorem gemPivotStage_partialPivotRow_hasBandwidth_invariant (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) (k : ℕ) :
    (∀ i j : Fin N, k + p ≤ (i : ℕ) → (gemPivotStage A partialPivotRow k).1 i j = A i j) ∧
      (∀ i j : Fin N, (i : ℕ) < k + p → k + p + q < (j : ℕ) →
        (gemPivotStage A partialPivotRow k).1 i j = 0) := by
  rw [hasLowerBandwidth_iff_fin] at hp
  rw [hasUpperBandwidth_iff_fin] at hq
  induction k with
  | zero =>
    refine ⟨fun i j _ => rfl, fun i j hi hj => ?_⟩
    rw [gemPivotStage_zero]
    exact hq i j (by omega)
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact ⟨fun i j hi => h1 i j (by omega), fun i j hi hj => h2 i j (by omega) (by omega)⟩
    set P : Fin N := ⟨k, hk⟩ with hP
    have hPk : (P : ℕ) = k := rfl
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M P with hr
    have hMk : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap P r) id) P := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    set M' := M.submatrix (Equiv.swap P r) id with hM'
    -- the pivot row lies at most `p` below the pivot index
    have hcol : ∀ i : Fin N, (P : ℕ) + p < i → M i P = 0 := fun i hi => by
      rw [h1 i P (by omega)]
      exact hp i P (by omega)
    have hrp : (r : ℕ) ≤ k + p := partialPivotRow_le_add M P p hcol
    have hkr : k ≤ (r : ℕ) := le_partialPivotRow M P
    have hM'_of : ∀ i : Fin N, i ≠ P → i ≠ r → ∀ j, M' i j = M i j := fun i hiP hir j => by
      simp [hM', Equiv.swap_apply_of_ne_of_ne hiP hir]
    have hM'P : ∀ j, M' P j = M r j := fun j => by simp [hM']
    -- the pivot row vanishes past the column `k + p + q`
    have hpivrow : ∀ j : Fin N, k + p + q < (j : ℕ) → M' P j = 0 := by
      intro j hj
      rw [hM'P]
      rcases Nat.lt_or_ge (r : ℕ) (k + p) with hrk | hrk
      · exact h2 r j hrk hj
      · rw [h1 r j (by omega)]
        exact hq r j (by omega)
    refine ⟨fun i j hi => ?_, fun i j hi hj => ?_⟩
    · -- the rows `k + 1 + p` and below are untouched
      have hiP : i ≠ P := fun e => by rw [e] at hi; omega
      have hir : i ≠ r := fun e => by rw [e] at hi; omega
      rw [hMk, elimStep_apply_of_lt _ (Fin.lt_def.2 (by omega)), hM'_of i hiP hir,
        hM'_of i hiP hir, h1 i P (by omega), hp i P (by omega)]
      simp [h1 i j (by omega)]
    · -- the support of the rows above them
      have hrow : ∀ i : Fin N, (i : ℕ) < k + 1 + p → M' i j = 0 := by
        intro i hi
        rcases eq_or_ne i P with rfl | hiP
        · exact hpivrow j (by omega)
        rcases eq_or_ne i r with rfl | hir
        · simp only [hM', submatrix_apply, Equiv.swap_apply_right, id_eq]
          rcases Nat.lt_or_ge (k : ℕ) (k + p) with hkp | hkp
          · exact h2 P j hkp (by omega)
          · rw [h1 P j (by omega)]
            exact hq P j (by omega)
        · rw [hM'_of i hiP hir]
          rcases Nat.lt_or_ge (i : ℕ) (k + p) with hik | hik
          · exact h2 i j hik (by omega)
          · rw [h1 i j (by omega)]
            exact hq i j (by omega)
      rw [hMk, elimStep_apply, hrow P (by omega), mul_zero, ite_self, sub_zero]
      exact hrow i hi

/-- **The band bound on the stages of Gaussian elimination with partial pivoting**: with `A` of
lower bandwidth `p` and upper bandwidth `q`, an entry of column `j` at stage `k` is at most `2^m`
times the largest entry of `A`, where `m = min k j - (j - (p + q))` counts the stages before `k`
that touch column `j`. A stage touches a column only while the pivot row — supported in the columns
`k` to `k + p + q` by `Matrix.gemPivotStage_partialPivotRow_hasBandwidth_invariant` — reaches it,
and each such stage at most doubles the column, since the multipliers are bounded by one. -/
theorem abs_gemPivotStage_le_of_hasBandwidth (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) (k : ℕ) (i j : Fin N) :
    |(gemPivotStage A partialPivotRow k).1 i j| ≤
      2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs := by
  have hμ := supAbs_nonneg A
  induction k generalizing i with
  | zero => simpa using abs_apply_le_supAbs A i j
  | succ k ih =>
    have hmono : (2 : ℝ) ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) ≤
        2 ^ (min (k + 1) (j : ℕ) - ((j : ℕ) - (p + q))) :=
      pow_le_pow_right₀ one_le_two (by omega)
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact (ih i).trans (mul_le_mul_of_nonneg_right hmono hμ)
    set P : Fin N := ⟨k, hk⟩ with hP
    have hPk : (P : ℕ) = k := rfl
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M P with hr
    have hMk : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap P r) id) P := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    set M' := M.submatrix (Equiv.swap P r) id with hM'
    have hih' : ∀ i : Fin N, |M' i j| ≤ 2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs :=
      fun i => ih _
    have hPr : P ≤ r := le_partialPivotRow M P
    have hkr : k ≤ (r : ℕ) := hPr
    have hband := gemPivotStage_partialPivotRow_hasBandwidth_invariant hp hq k
    have hb1 : ∀ i j : Fin N, k + p ≤ (i : ℕ) → M i j = A i j := hband.1
    have hb2 : ∀ i j : Fin N, (i : ℕ) < k + p → k + p + q < (j : ℕ) → M i j = 0 := hband.2
    have hcol : ∀ i : Fin N, (P : ℕ) + p < i → M i P = 0 := fun i hi => by
      rw [hb1 i P (by omega)]
      exact hasLowerBandwidth_iff_fin.1 hp i P (by omega)
    have hrp : (r : ℕ) ≤ k + p := partialPivotRow_le_add M P p hcol
    rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
    · -- an earlier column: the pivot row vanishes there
      have hjr : j < r := lt_of_lt_of_le (show j < P from Fin.lt_def.2 (by omega)) hPr
      have hrow : M' P j = 0 := by
        simp only [hM', submatrix_apply, Equiv.swap_apply_left, id_eq]
        exact gemPivotStage_partialPivotRow_apply_eq_zero_of_lt A k r j hjk hjr
      rw [hMk, elimStep_apply_of_pivot_row_eq_zero _ _ _ hrow]
      exact (hih' i).trans (mul_le_mul_of_nonneg_right hmono hμ)
    rcases Nat.lt_or_ge (k : ℕ) (j : ℕ) with hjk' | hjk'
    swap
    · -- the column just eliminated
      have hjP : j = P := Fin.ext (by omega)
      by_cases hi : P < i
      · rw [hjP, gemPivotStage_partialPivotRow_succ_apply_pivot hk hi, abs_zero]
        exact mul_nonneg (by positivity) hμ
      · rw [hMk, elimStep_apply_of_not_lt _ hi]
        exact (hih' i).trans (mul_le_mul_of_nonneg_right hmono hμ)
    rcases Nat.lt_or_ge (k + p + q) (j : ℕ) with hjq | hjq
    · -- past the band of the pivot row
      have hrow : M' P j = 0 := by
        simp only [hM', submatrix_apply, Equiv.swap_apply_left, id_eq]
        rcases Nat.lt_or_ge (r : ℕ) (k + p) with hrk | hrk
        · exact hb2 r j hrk hjq
        · rw [hb1 r j (by omega)]
          exact hasUpperBandwidth_iff_fin.1 hq r j (by omega)
      rw [hMk, elimStep_apply_of_pivot_row_eq_zero _ _ _ hrow]
      exact (hih' i).trans (mul_le_mul_of_nonneg_right hmono hμ)
    · -- inside the band: one more doubling, which the counter allows
      have hpow : (2 : ℝ) ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * 2 ≤
          2 ^ (min (k + 1) (j : ℕ) - ((j : ℕ) - (p + q))) := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ one_le_two (by omega)
      by_cases hi : P < i
      · rw [hMk, elimStep_apply_of_lt _ hi, ← div_eq_mul_inv]
        have hmul : |M' i P / M' P P| ≤ 1 := by
          refine abs_div_le_one_of_abs_le ?_
          simp only [hM', submatrix_apply, Equiv.swap_apply_left, id_eq]
          have hτ : P ≤ Equiv.swap P r i := by
            rcases eq_or_ne i P with rfl | hiP
            · rwa [Equiv.swap_apply_left]
            rcases eq_or_ne i r with rfl | hir
            · rw [Equiv.swap_apply_right]
            · rw [Equiv.swap_apply_of_ne_of_ne hiP hir]
              exact hi.le
          simpa [Real.norm_eq_abs] using norm_apply_le_partialPivotRow M P hτ
        calc |M' i j - M' i P / M' P P * M' P j|
            ≤ |M' i j| + |M' i P / M' P P| * |M' P j| := by
              rw [← abs_mul]; exact abs_sub _ _
          _ ≤ |M' i j| + 1 * |M' P j| :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right hmul (abs_nonneg _))
          _ ≤ 2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs +
                2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs := by
              rw [one_mul]; exact add_le_add (hih' i) (hih' P)
          _ = 2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * 2 * A.supAbs := by ring
          _ ≤ 2 ^ (min (k + 1) (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs :=
              mul_le_mul_of_nonneg_right hpow hμ
      · rw [hMk, elimStep_apply_of_not_lt _ hi]
        exact (hih' i).trans (mul_le_mul_of_nonneg_right hmono hμ)

/-- **A band bound for the growth factor of Gaussian elimination with partial pivoting**: for `A`
of lower bandwidth `p` and upper bandwidth `q` the growth factor is at most `2^{p+q}`, a bound
independent of the order of the matrix. [quarteroni2000numerical] §3.10 (1) and
[higham2002accuracy] Theorem 9.11 quote Bohte's sharper `2^{2p-1} - (p-1) 2^{p-2}` for `p = q`,
which this does not reach (it gives `2^{2p}`); the tridiagonal case `p = q = 1` is sharpened to `2`
by `Matrix.growthFactor_le_two_of_isTridiagonal`. -/
theorem growthFactor_le_two_pow_of_hasBandwidth (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) :
    growthFactor ((gemPivotStage A partialPivotRow N).2.permMatrix ℝ * A) ≤ 2 ^ (p + q) := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) ℝ) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  have hμ := supAbs_nonneg A
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  refine growthFactor_le_of_forall_abs_le _ (by positivity) fun k i j hk => ?_
  rw [supAbs_submatrix_equiv, gemStage_submatrix_eq_submatrix_gemPivotStage A partialPivotRow
    hpiv k, submatrix_apply, id_eq]
  refine (abs_gemPivotStage_le_of_hasBandwidth hp hq k _ j).trans
    (mul_le_mul_of_nonneg_right ?_ hμ)
  exact pow_le_pow_right₀ one_le_two (by omega)

end Band

/-! ### Complete pivoting: Wilkinson's growth bound -/

section Wilkinson

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

/-- `A.HasDominantPivots`: at every stage of Gaussian elimination *without* pivoting on `A` the
pivot dominates the whole trailing block, `|a^{(k)}_{ij}| ≤ |a^{(k)}_{kk}|` for `i, j ≥ k`. This
is what complete pivoting arranges (`Matrix.hasDominantPivots_submatrix_gemFullPivotStage`), and
it is the hypothesis under which Wilkinson's bound of [quarteroni2000numerical] §3.10 holds. It is
strictly stronger than the `‖U i j‖ ≤ ‖U i i‖` recorded by
`Matrix.exists_permMatrix_mul_mul_permMatrix_isLU`, which speaks about the final factor only. -/
def HasDominantPivots (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ (k : ℕ) (hk : k < N) (i j : Fin N), k ≤ (i : ℕ) → k ≤ (j : ℕ) →
    |gemStage A k i j| ≤ |gemStage A k ⟨k, hk⟩ ⟨k, hk⟩|

/-- The modulus `|a^{(k)}_{kk}|` of the `k`-th pivot of Gaussian elimination without pivoting, as
a total function of `k : ℕ` with the junk value `0` beyond the order of the matrix. -/
noncomputable def absGemPivot (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : ℝ :=
  if h : k < N then |gemStage A k ⟨k, h⟩ ⟨k, h⟩| else 0

/-- Below the order of the matrix, `Matrix.absGemPivot` is the modulus of the pivot. -/
theorem absGemPivot_of_lt (A : Matrix (Fin N) (Fin N) ℝ) {k : ℕ} (h : k < N) :
    absGemPivot A k = |gemStage A k ⟨k, h⟩ ⟨k, h⟩| := by simp [absGemPivot, h]

/-- `Matrix.absGemPivot` is nonnegative. -/
theorem absGemPivot_nonneg (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : 0 ≤ absGemPivot A k := by
  rw [absGemPivot]
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

/-- Dominance, in terms of `Matrix.absGemPivot`. -/
theorem HasDominantPivots.abs_gemStage_le (hA : A.HasDominantPivots) {k : ℕ} (hk : k < N)
    {i j : Fin N} (hi : k ≤ (i : ℕ)) (hj : k ≤ (j : ℕ)) :
    |gemStage A k i j| ≤ absGemPivot A k := by
  rw [absGemPivot_of_lt A hk]
  exact hA k hk i j hi hj

/-- **The shape of `A^{(k)}` under dominance**: stage `k` vanishes below the diagonal in the first
`k` columns. This is `Matrix.gemStage_apply_eq_zero_of_lt` with the nonvanishing of the pivots
replaced by dominance, which also covers a vanishing pivot: there the whole trailing block is
zero, so the elimination step is the identity. -/
theorem HasDominantPivots.gemStage_apply_eq_zero (hA : A.HasDominantPivots) (k : ℕ) {i j : Fin N}
    (hjk : (j : ℕ) < k) (hji : j < i) : gemStage A k i j = 0 := by
  induction k generalizing i j with
  | zero => exact absurd hjk (Nat.not_lt_zero _)
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hjk' | hjk'
    · by_cases hkN : k < N
      · rw [gemStage_succ_of_lt A hkN,
          elimStep_apply_of_pivot_row_eq_zero _ _ _ (ih hjk' (Fin.mk_lt_of_lt_val hjk'))]
        exact ih hjk' hji
      · rw [gemStage_succ_of_le A (not_lt.1 hkN)]
        exact ih hjk' hji
    · have hkN : k < N := hjk' ▸ j.isLt
      have hj : j = (⟨k, hkN⟩ : Fin N) := Fin.ext hjk'
      subst hj
      rw [gemStage_succ_of_lt A hkN, elimStep_apply_of_lt _ hji]
      rcases eq_or_ne (gemStage A k ⟨k, hkN⟩ ⟨k, hkN⟩) 0 with h0 | h0
      · have := hA k hkN i ⟨k, hkN⟩ (le_of_lt (Fin.lt_def.1 hji)) le_rfl
        rw [h0, abs_zero, abs_nonpos_iff] at this
        rw [this, h0]
        ring
      · rw [mul_assoc, inv_mul_cancel₀ h0, mul_one, sub_self]

/-- **A vanishing pivot freezes the elimination**: under dominance a zero pivot at stage `m` means
that the whole trailing block of `A^{(m)}` vanishes, and then every later stage equals `A^{(m)}`. -/
theorem HasDominantPivots.gemStage_eq_of_pivot_eq_zero (hA : A.HasDominantPivots) {m : ℕ}
    (hm : m < N) (h0 : gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ = 0) {k : ℕ} (hk : m ≤ k) :
    gemStage A k = gemStage A m := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    by_cases hkN : k < N
    · rw [gemStage_succ_of_lt A hkN, ih]
      have hrow : ∀ j : Fin N, gemStage A m ⟨k, hkN⟩ j = 0 := by
        intro j
        rcases lt_or_ge (j : ℕ) m with hj | hj
        · exact hA.gemStage_apply_eq_zero m hj (Fin.lt_def.2 (lt_of_lt_of_le hj hk))
        · have := hA m hm ⟨k, hkN⟩ j hk hj
          rw [h0, abs_zero, abs_nonpos_iff] at this
          exact this
      ext i j
      exact elimStep_apply_of_pivot_row_eq_zero _ _ _ (hrow j)
    · rw [gemStage_succ_of_le A (not_lt.1 hkN), ih]

/-- Under dominance the vanishing of a pivot propagates to every later pivot. -/
theorem HasDominantPivots.absGemPivot_eq_zero_of_le (hA : A.HasDominantPivots) {m k : ℕ}
    (hm : m < N) (hk : k < N) (hmk : m ≤ k) (h0 : absGemPivot A m = 0) : absGemPivot A k = 0 := by
  rw [absGemPivot_of_lt A hm, abs_eq_zero] at h0
  rw [absGemPivot_of_lt A hk, hA.gemStage_eq_of_pivot_eq_zero hm h0 hmk, abs_eq_zero]
  have := hA m hm ⟨k, hk⟩ ⟨k, hk⟩ hmk hmk
  rw [h0, abs_zero, abs_nonpos_iff] at this
  exact this

/-- **Hadamard's inequality on the reduced matrices**, the first half of Wilkinson's argument for
[higham2002accuracy] (9.14): under dominance, if the pivots `a^{(k+t)}_{k+t,k+t}` of a run of `j`
consecutive stages are nonzero, then their moduli multiply to at most `(√j |a^{(k)}_{kk}|)^j`.
Indeed the block of `A^{(k)}` on the indices `k, …, k + j - 1` has those pivots as the diagonal of
its own elimination, so its determinant is their product, while its entries are bounded by
`|a^{(k)}_{kk}|` and `Matrix.norm_det_le_of_forall_norm_le` applies. -/
theorem prod_absGemPivot_le (hA : A.HasDominantPivots) {k j : ℕ} (h : k + j ≤ N) (hj : 0 < j)
    (hne : ∀ t, t < j → absGemPivot A (k + t) ≠ 0) :
    ∏ t ∈ Finset.range j, absGemPivot A (k + t) ≤ (Real.sqrt j * absGemPivot A k) ^ j := by
  have hkN : k < N := by omega
  set e := blockEmb k j N h with he
  set B := (gemStage A k).submatrix e e with hB
  have hpivB : ∀ (m : ℕ) (hm : m < j), m + 1 < j → gemStage B m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0 := by
    intro m hm _
    have hkm : k + m < N := by omega
    rw [hB, gemStage_submatrix_blockEmb A h m hm.le, submatrix_apply]
    have := hne m hm
    rw [absGemPivot_of_lt A hkm, ne_eq, abs_eq_zero] at this
    exact this
  have hupper : (gemStage B j).IsUpperTriangular := fun i j' hij =>
    gemStage_apply_eq_zero_of_lt B (fun m hm _ hmj => hpivB m hm hmj) j'.isLt hij
  have hdetB : B.det = ∏ i : Fin j, gemStage A (k + (i : ℕ)) (e i) (e i) := by
    have h1 : gemLowerStage B j * gemStage B j = B := gemLowerStage_mul_gemStage B j
    rw [← h1, det_mul, (isUnitLowerTriangular_gemLowerStage B j).det_eq_one, one_mul,
      det_of_isUpperTriangular hupper]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [gemStage_submatrix_blockEmb A h j le_rfl, submatrix_apply]
    exact gemStage_apply_of_le A (le_refl (k + (i : ℕ))) (by omega) _
  have hentry : ∀ i i' : Fin j, ‖B i i'‖ ≤ absGemPivot A k := by
    intro i i'
    rw [hB, submatrix_apply, Real.norm_eq_abs]
    exact hA.abs_gemStage_le hkN (Nat.le_add_right k _) (Nat.le_add_right k _)
  have hHad := norm_det_le_of_forall_norm_le (absGemPivot_nonneg A k) hentry
  rw [Fintype.card_fin] at hHad
  rw [Real.norm_eq_abs, hdetB, abs_prod] at hHad
  refine le_trans (le_of_eq ?_) hHad
  rw [← Fin.prod_univ_eq_prod_range (fun t => absGemPivot A (k + t)) j]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hki : k + (i : ℕ) < N := by omega
  rw [absGemPivot_of_lt A hki]
  rfl

/-- **Wilkinson's growth bound** ([quarteroni2000numerical] §3.10, [higham2002accuracy] (9.14)):
`n^{1/2} (2 · 3^{1/2} · 4^{1/3} ⋯ n^{1/(n-1)})^{1/2}`, the bound on the growth factor
of Gaussian elimination with complete pivoting on a matrix of order `n`. The inner product is
written over `t = 0, …, n - 2` with the factor `(t + 2)^{1/(t+1)}`. -/
noncomputable def wilkinsonGrowthBound (n : ℕ) : ℝ :=
  Real.sqrt n * Real.sqrt (∏ t ∈ Finset.range (n - 1), ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹)

/-- Every factor of Wilkinson's product is at least one. -/
theorem one_le_wilkinsonFactor (t : ℕ) : (1 : ℝ) ≤ ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  calc (1 : ℝ) = (1 : ℝ) ^ ((t : ℝ) + 1)⁻¹ := (Real.one_rpow _).symm
    _ ≤ ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ :=
        Real.rpow_le_rpow zero_le_one (by linarith) (by positivity)

/-- Wilkinson's product is at least one. -/
theorem one_le_wilkinsonProd (n : ℕ) :
    (1 : ℝ) ≤ ∏ t ∈ Finset.range n, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ := by
  have h1 : (∏ _t ∈ Finset.range n, (1 : ℝ)) ≤
      ∏ t ∈ Finset.range n, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ :=
    Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun t _ => one_le_wilkinsonFactor t
  simpa using h1

/-- Wilkinson's product is positive. -/
theorem wilkinsonProd_pos (n : ℕ) :
    (0 : ℝ) < ∏ t ∈ Finset.range n, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ :=
  lt_of_lt_of_le zero_lt_one (one_le_wilkinsonProd n)

/-- Wilkinson's product is monotone in the number of factors. -/
theorem wilkinsonProd_mono {a b : ℕ} (h : a ≤ b) :
    (∏ t ∈ Finset.range a, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹) ≤
      ∏ t ∈ Finset.range b, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih =>
    rw [Finset.prod_range_succ]
    exact ih.trans (by nlinarith [wilkinsonProd_pos b, one_le_wilkinsonFactor b])

/-- Wilkinson's bound is nonnegative. -/
theorem wilkinsonGrowthBound_nonneg (n : ℕ) : 0 ≤ wilkinsonGrowthBound n := by
  unfold wilkinsonGrowthBound
  positivity

/-- Wilkinson's bound is positive on a nonempty matrix. -/
theorem wilkinsonGrowthBound_pos {n : ℕ} (hn : 0 < n) : 0 < wilkinsonGrowthBound n :=
  mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)) (Real.sqrt_pos.2 (wilkinsonProd_pos _))

/-- Wilkinson's bound is monotone in the order. -/
theorem wilkinsonGrowthBound_mono {m n : ℕ} (h : m ≤ n) :
    wilkinsonGrowthBound m ≤ wilkinsonGrowthBound n := by
  have hmn : ((m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast h
  refine (_root_.mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmn)
    (Real.sqrt_nonneg _)).trans ?_
  exact _root_.mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (wilkinsonProd_mono (by omega))) (Real.sqrt_nonneg _)

/-- The logarithm of Wilkinson's bound, the form in which the telescoping induction uses it. -/
theorem log_wilkinsonGrowthBound {n : ℕ} (hn : 0 < n) :
    Real.log (wilkinsonGrowthBound n) = Real.log n / 2 +
      ∑ t ∈ Finset.range (n - 1), Real.log ((t : ℝ) + 2) / (2 * ((t : ℝ) + 1)) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [wilkinsonGrowthBound, Real.log_mul (Real.sqrt_pos.2 hn').ne'
      (Real.sqrt_pos.2 (wilkinsonProd_pos _)).ne',
    Real.log_sqrt hn'.le, Real.log_sqrt (wilkinsonProd_pos _).le,
    Real.log_prod (fun t _ => by positivity), Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht1 : ((t : ℝ) + 1) ≠ 0 := by positivity
  rw [Real.log_rpow (by positivity)]
  field_simp

/-- **Wilkinson's telescoping estimate, in logarithmic form**: under dominance, if the first
`r + 1` pivots are nonzero then
`log μ_r ≤ log μ_0 + (1/2) log(r+1) + ∑_{t<r} log(t+2) / (2(t+1))`, where `μ_k` is the modulus of
the `k`-th pivot. Neither [quarteroni2000numerical] nor [higham2002accuracy] proves (9.14) — both
refer to Wilkinson's 1961 paper — so the argument is reconstructed here: writing
`L_s` for the sum of the logarithms of the last `s + 1` pivots, `Matrix.prod_absGemPivot_le` on the
run of `s + 2` pivots ending at `r` gives `L_{s+1} ≥ ((s+2)/(s+1)) (L_s - (1/2) log(s+2))`, whence
`L_s ≥ (s+1) log μ_r - (s+1) ∑_{t<s} log(t+2)/(2(t+1))`; feeding `s = r` into
`Matrix.prod_absGemPivot_le` on the whole run gives the statement. -/
theorem log_absGemPivot_le (hA : A.HasDominantPivots) {r : ℕ} (hr : r < N)
    (hne : ∀ m, m ≤ r → absGemPivot A m ≠ 0) :
    Real.log (absGemPivot A r) ≤ Real.log (absGemPivot A 0) + Real.log ((r : ℝ) + 1) / 2 +
      ∑ t ∈ Finset.range r, Real.log ((t : ℝ) + 2) / (2 * ((t : ℝ) + 1)) := by
  have hpos : ∀ m, m ≤ r → 0 < absGemPivot A m := fun m hm =>
    lt_of_le_of_ne (absGemPivot_nonneg A m) (Ne.symm (hne m hm))
  have hP : ∀ k j : ℕ, k + j ≤ r + 1 → 0 < j →
      ∑ i ∈ Finset.range j, Real.log (absGemPivot A (k + i)) ≤
        (j : ℝ) / 2 * Real.log j + j * Real.log (absGemPivot A k) := by
    intro k j hkj hj
    have hkN : k + j ≤ N := by omega
    have hnz : ∀ t, t < j → absGemPivot A (k + t) ≠ 0 := fun t ht => hne _ (by omega)
    have hprodpos : (0 : ℝ) < ∏ t ∈ Finset.range j, absGemPivot A (k + t) :=
      Finset.prod_pos fun t ht => hpos _ (by simp only [Finset.mem_range] at ht; omega)
    have hsq : (0 : ℝ) < Real.sqrt j := Real.sqrt_pos.2 (by exact_mod_cast hj)
    have hlog := Real.log_le_log hprodpos (prod_absGemPivot_le hA hkN hj hnz)
    rw [Real.log_prod (fun t ht => (hpos _ (by simp only [Finset.mem_range] at ht; omega)).ne'),
      Real.log_pow, Real.log_mul hsq.ne' (hne k (by omega)),
      Real.log_sqrt (by positivity)] at hlog
    linarith
  have hclaim : ∀ s k : ℕ, k + s = r →
      ((s : ℝ) + 1) * Real.log (absGemPivot A r) -
          ((s : ℝ) + 1) * ∑ t ∈ Finset.range s, Real.log ((t : ℝ) + 2) / (2 * ((t : ℝ) + 1)) ≤
        ∑ i ∈ Finset.range (s + 1), Real.log (absGemPivot A (k + i)) := by
    intro s
    induction s with
    | zero =>
      intro k hk
      have hkr : k = r := by omega
      subst hkr
      simp
    | succ s ih =>
      intro k hk
      have hS1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
      have hS2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
      have IH := ih (k + 1) (by omega)
      have hPk := hP k (s + 1 + 1) (by omega) (by omega)
      have hcast : ((s + 1 + 1 : ℕ) : ℝ) = (s : ℝ) + 2 := by push_cast; ring
      rw [hcast] at hPk
      have hsplit : (∑ i ∈ Finset.range (s + 1 + 1), Real.log (absGemPivot A (k + i))) =
          (∑ i ∈ Finset.range (s + 1), Real.log (absGemPivot A (k + 1 + i))) +
            Real.log (absGemPivot A k) := by
        rw [Finset.sum_range_succ' (fun i => Real.log (absGemPivot A (k + i))) (s + 1)]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by omega]
      rw [Finset.sum_range_succ]
      push_cast
      set G := ∑ i ∈ Finset.range (s + 1 + 1), Real.log (absGemPivot A (k + i)) with hGd
      set G' := ∑ i ∈ Finset.range (s + 1), Real.log (absGemPivot A (k + 1 + i)) with hG'd
      set m := Real.log (absGemPivot A k) with hmd
      set L := Real.log (absGemPivot A r) with hLd
      set Ts := ∑ t ∈ Finset.range s, Real.log ((t : ℝ) + 2) / (2 * ((t : ℝ) + 1)) with hTd
      set c := Real.log ((s : ℝ) + 2) with hcd
      have hGm : ((s : ℝ) + 2) * m = ((s : ℝ) + 2) * (G - G') := by rw [hsplit]; ring
      have step1 : ((s : ℝ) + 2) * G' - ((s : ℝ) + 2) / 2 * c ≤ ((s : ℝ) + 1) * G := by
        linarith [hPk, hGm]
      have step2 := _root_.mul_le_mul_of_nonneg_left IH hS2.le
      have hcdiv : ((s : ℝ) + 1) * (((s : ℝ) + 1 + 1) * (c / (2 * ((s : ℝ) + 1)))) =
          ((s : ℝ) + 2) * c / 2 := by
        field_simp
        ring
      refine le_of_mul_le_mul_left ?_ hS1
      nlinarith [step1, step2, hcdiv]
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  have hfin := hclaim r 0 (by omega)
  have hP0 := hP 0 (r + 1) (by omega) (by omega)
  rw [hcast] at hP0
  simp only [Nat.zero_add] at hfin hP0
  refine le_of_mul_le_mul_left ?_ hr1
  nlinarith [hfin, hP0]

/-- **Wilkinson's estimate on one pivot**: under dominance the `r`-th pivot is at most
`wilkinsonGrowthBound (r + 1)` times the first. -/
theorem absGemPivot_le_wilkinson (hA : A.HasDominantPivots) {r : ℕ} (hr : r < N) :
    absGemPivot A r ≤ wilkinsonGrowthBound (r + 1) * absGemPivot A 0 := by
  rcases eq_or_ne (absGemPivot A r) 0 with h0 | h0
  · rw [h0]
    exact mul_nonneg (wilkinsonGrowthBound_nonneg _) (absGemPivot_nonneg A 0)
  have hne : ∀ m, m ≤ r → absGemPivot A m ≠ 0 := fun m hm hzero =>
    h0 (hA.absGemPivot_eq_zero_of_le (by omega) hr hm hzero)
  have hposr : 0 < absGemPivot A r := lt_of_le_of_ne (absGemPivot_nonneg A r) (Ne.symm h0)
  have hpos0 : 0 < absGemPivot A 0 :=
    lt_of_le_of_ne (absGemPivot_nonneg A 0) (Ne.symm (hne 0 (Nat.zero_le r)))
  have hB : 0 < wilkinsonGrowthBound (r + 1) := wilkinsonGrowthBound_pos (by omega)
  have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  rw [← Real.log_le_log_iff hposr (by positivity), Real.log_mul hB.ne' hpos0.ne',
    log_wilkinsonGrowthBound (n := r + 1) (by omega), hcast, Nat.add_sub_cancel]
  have := log_absGemPivot_le hA hr hne
  linarith

/-- **Wilkinson's bound on the growth factor of complete pivoting**
([quarteroni2000numerical] §3.10, [higham2002accuracy] (9.14)): if the pivot dominates the
trailing block at every stage — which is what complete pivoting arranges — then
`ρ_N ≤ N^{1/2} (2 · 3^{1/2} ⋯ N^{1/(N-1)})^{1/2}`. The largest entry of `A` is the first pivot, by
dominance at stage `0`; every entry of every stage is either zero, by the shape of the reduced
matrices, or bounded by the pivot of an earlier stage; and
`Matrix.absGemPivot_le_wilkinson` bounds each pivot in terms of the first. -/
theorem growthFactor_le_of_completePivoting {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.HasDominantPivots) : growthFactor A ≤ wilkinsonGrowthBound N := by
  refine growthFactor_le_of_forall_abs_le A (wilkinsonGrowthBound_nonneg N) fun k i j hk => ?_
  have hN : 0 < N := by omega
  have hsup : A.supAbs = absGemPivot A 0 := by
    refine le_antisymm (supAbs_le (absGemPivot_nonneg A 0) fun i' j' =>
      hA.abs_gemStage_le hN (Nat.zero_le _) (Nat.zero_le _)) ?_
    rw [absGemPivot_of_lt A hN]
    exact abs_apply_le_supAbs A _ _
  have main : ∀ m : ℕ, m < N → ∀ i' j' : Fin N, m ≤ (i' : ℕ) → m ≤ (j' : ℕ) →
      |gemStage A m i' j'| ≤ wilkinsonGrowthBound N * A.supAbs := by
    intro m hm i' j' hi' hj'
    rw [hsup]
    calc |gemStage A m i' j'| ≤ absGemPivot A m := hA.abs_gemStage_le hm hi' hj'
      _ ≤ wilkinsonGrowthBound (m + 1) * absGemPivot A 0 := absGemPivot_le_wilkinson hA hm
      _ ≤ wilkinsonGrowthBound N * absGemPivot A 0 :=
          _root_.mul_le_mul_of_nonneg_right (wilkinsonGrowthBound_mono (by omega))
            (absGemPivot_nonneg A 0)
  have hzero : (0 : ℝ) ≤ wilkinsonGrowthBound N * A.supAbs :=
    mul_nonneg (wilkinsonGrowthBound_nonneg N) (supAbs_nonneg A)
  rcases le_or_gt k (i : ℕ) with hi | hi
  · rcases le_or_gt k (j : ℕ) with hj | hj
    · exact main k hk i j hi hj
    · rw [hA.gemStage_apply_eq_zero k hj (Fin.lt_def.2 (lt_of_lt_of_le hj hi)), abs_zero]
      exact hzero
  · rw [gemStage_apply_of_le A (le_refl (i : ℕ)) hi.le j]
    rcases le_or_gt (i : ℕ) (j : ℕ) with hij | hij
    · exact main (i : ℕ) i.isLt i j le_rfl hij
    · rw [hA.gemStage_apply_eq_zero (i : ℕ) hij (Fin.lt_def.2 hij), abs_zero]
      exact hzero

/-- **Complete pivoting makes the pivots dominant**: the stages of Gaussian elimination on
`P A Q`, for the permutations accumulated by `Matrix.gemFullPivotStage` with a complete-pivoting
strategy, have their pivot dominating the trailing block. -/
theorem hasDominantPivots_submatrix_gemFullPivotStage (A : Matrix (Fin N) (Fin N) ℝ)
    {piv : Matrix (Fin N) (Fin N) ℝ → Fin N → Fin N × Fin N} (hpiv : IsCompletePivot piv) :
    (A.submatrix (gemFullPivotStage A piv N).2.1
      (gemFullPivotStage A piv N).2.2).HasDominantPivots := by
  have hrow : ∀ M k, k ≤ (piv M k).1 := fun M k => (hpiv M k).1
  have hcol : ∀ M k, k ≤ (piv M k).2 := fun M k => (hpiv M k).2.1
  intro k hk i j hi hj
  rw [gemStage_submatrix_apply_self A piv hrow hcol hk,
    gemStage_submatrix_eq_submatrix_gemFullPivotStage A piv hrow hcol, submatrix_apply]
  have hbound := (hpiv (gemFullPivotStage A piv k).1 ⟨k, hk⟩).2.2
    (((gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1) i)
    (((gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) j)
    (Fin.le_def.2 (le_gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow hk.le hi))
    (Fin.le_def.2 (le_gemFullPivotStage_colPerm_inv_mul_apply A piv hcol hk.le hj))
  simpa only [Real.norm_eq_abs] using hbound

/-- **The growth factor of Gaussian elimination with complete pivoting obeys Wilkinson's bound**
([quarteroni2000numerical] §3.10, [higham2002accuracy] (9.14)): for every complete-pivoting
strategy `piv`, the growth factor of the elimination of `P A Q` — whose stages are those of the
pivoted elimination up to the order of the rows and of the columns
(`Matrix.gemStage_submatrix_eq_submatrix_gemFullPivotStage`) — is at most
`N^{1/2} (2 · 3^{1/2} ⋯ N^{1/(N-1)})^{1/2}`, which grows more slowly than the `2^{N-1}` of partial
pivoting. -/
theorem growthFactor_le_wilkinson_of_isCompletePivot (A : Matrix (Fin N) (Fin N) ℝ)
    {piv : Matrix (Fin N) (Fin N) ℝ → Fin N → Fin N × Fin N} (hpiv : IsCompletePivot piv) :
    growthFactor (A.submatrix (gemFullPivotStage A piv N).2.1
      (gemFullPivotStage A piv N).2.2) ≤ wilkinsonGrowthBound N :=
  growthFactor_le_of_completePivoting (hasDominantPivots_submatrix_gemFullPivotStage A hpiv)

end Wilkinson

end Matrix
