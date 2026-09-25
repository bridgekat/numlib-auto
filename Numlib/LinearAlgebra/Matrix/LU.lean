/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LU`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The LU factorization

The LU factorization as a *specification*: the predicate `Matrix.IsLU A L U` (`L` unit lower
triangular, `U` upper triangular, `L * U = A`) and everything that is true of the factorization
independently of how it is computed. The algorithms — the elimination stages of Gaussian
elimination, the Doolittle recurrence, pivoting and the growth factor — belong to
`Numlib/LinearAlgebra/Matrix/LU/Elimination` and `…/LU/Pivoting`; the substitution solves to
`Numlib/Direct/Substitution`; the rounding-error analysis to `Numlib/FloatingPoint/LU`;
Cholesky to `Numlib/LinearAlgebra/Matrix/Cholesky`.

## Main definitions

* `Matrix.leadingPrincipalSubmatrix A k = A.toBlock (· ≤ k) (· ≤ k)`,
  `Matrix.strictLeadingPrincipalSubmatrix A k = A.toBlock (· < k) (· < k)` and
  `Matrix.leadingPrincipalMinor`: the leading principal submatrices, indexed by the subtypes
  `{i // i ≤ k}` and `{i // i < k}` of a finite linear order, with no arithmetic on indices.
* `Matrix.IsLU A L U`; `Matrix.IsLDM A L D M`, the `L D Mᵀ` factorization (and `L D Lᵀ` when
  `M = L`).
* `Matrix.IsBlockUnitLowerTriangular b L`, `Matrix.IsBlockLU b A L U`: block unit lower
  triangularity and block LU along a labelling `b : n → α` of the indices by a linear order, built
  on Mathlib's `Matrix.BlockTriangular`; `b = id` is `Matrix.IsLU` (`Matrix.isBlockLU_id_iff`).
* `Matrix.IsRectLU A L U`: the rectangular (trapezoidal) LU factorization of an `M × N` matrix
  on `Fin` indices ([golub2013matrix] §3.2.10), which is `Matrix.IsLU` on a square matrix
  (`Matrix.isRectLU_iff_isLU`).
* `Matrix.envelope A`, the lower envelope of a matrix; `Matrix.tridiagonalOfNat a b c N`, the
  tridiagonal matrix with diagonals `a`, `b`, `c`; `Matrix.thomasAlpha`, `Matrix.thomasBeta`,
  `Matrix.thomasGamma`, the recurrences of the Thomas algorithm, and its factors
  `Matrix.thomasLower`, `Matrix.thomasUpper`, which are the bidiagonal matrices
  `Matrix.lowerBidiagonalOf`, `Matrix.upperBidiagonalOf` of the multipliers and the pivots.

## Main results

* `Matrix.existsUnique_isBlockLU_iff`: a matrix has a unique block LU factorization along `b` iff
  its leading principal block submatrices `A(b < a)`, `a` a label, are nonsingular
  ([quarteroni2000numerical] Theorem 3.7). Existence (`Matrix.exists_isBlockLU_of_forall_isUnit`)
  is by strong induction on the number of indices, bordering the last block onto the factorization
  of the leading block (`Matrix.isBlockLU_fromBlocks`, the induction step of the book's proof of
  Theorem 3.4); uniqueness (`Matrix.IsBlockLU.unique`) is the same induction with the bordering
  equations `Matrix.IsBlockLU.toBlock_not_left`, `…_not_right`, `…_not_not`; necessity
  (`Matrix.IsBlockLU.exists_ne_of_not_isUnit`) perturbs a factorization along the left kernel of
  a singular leading block, as in Example 3.3.
* `Matrix.existsUnique_isLU_iff`,
  `Matrix.exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix`, `Matrix.IsLU.unique`:
  [quarteroni2000numerical] Theorem 3.4, [higham2002accuracy] Theorem 9.1, as the case `b = id`.
* `Matrix.IsLU.det_leadingPrincipalSubmatrix`, `Matrix.IsLU.det_eq_prod_diag`,
  `Matrix.IsLU.diag_upper_eq_div_leadingPrincipalMinor`: the leading principal minors are the
  products of the pivots, and the pivots are ratios of consecutive minors ((3.39)).
* `Matrix.exists_isRectLU_of_forall_isUnit`: a rectangular matrix whose leading blocks of order
  at most `min M N` are nonsingular has a rectangular LU factorization, by bordering with zeros to
  a square matrix and the block LU factorization along the labelling `i ↦ min i (min M N)`.
* `Matrix.existsUnique_isLDM` (Theorem 3.5, [golub2013matrix] Theorem 4.1.3, with the *strict*
  leading principal minors, the last pivot free to vanish), `Matrix.IsLDM.eq_of_isSymm`
  (`L D Lᵀ`), `Matrix.IsLDM.diag_pos_of_posDef`.
* `Matrix.exists_isLU_of_isDiagDominant`, `Matrix.exists_isLU_of_isColDiagDominant`: Property 3.2,
  [higham2002accuracy] Theorem 9.9, for *nonsingular* weakly dominant matrices (the book omits
  the nonsingularity, which `!![0, 0; 1, 1]` shows is needed), by induction through the Schur
  complement at the first index (`Matrix.isLU_luLowerOfSchur_luUpperOfSchur`).
* `Matrix.IsLU.hasUpperBandwidth`, `Matrix.IsLU.hasLowerBandwidth`: Property 3.4, band
  preservation; `Matrix.IsLU.envelope_eq`: (3.60), the envelope is preserved.
* `Matrix.isLU_tridiagonal_thomas`: the Thomas identities (3.53) as an LU factorization of a
  tridiagonal matrix by bidiagonal factors; `Matrix.isBlockLU_fromBlocks_schurComplement`: the
  two-block case is the Schur complement factorization of §3.8.1.

## Implementation notes

The index type is any `[Fintype n] [LinearOrder n]`, never `Fin N`: the order is all a
triangular factorization uses, and `Matrix.toBlock` gives the leading blocks without reindexing.
Lower triangular is Mathlib's `Matrix.IsLowerTriangular = BlockTriangular toDual`, upper triangular
is `Matrix.IsUpperTriangular = BlockTriangular id`, so that block LU along a labelling `b` is the
same structure with `id` replaced by `b`, and the scalar theory is derived from the block theory.
The block theory itself needs only `[DecidableEq n]` on the indices. Where a leading block is
reindexed (`Equiv.sumCompl` in the bordering step, `Equiv.subtypeSubtypeEquivSubtype` when the
strict-block hypothesis passes to a leading block), nonsingularity is transported through
`Matrix.det_submatrix_equiv_self`.

## References

* [quarteroni2000numerical] §3.3–3.4, §3.7–3.8.
* [higham2002accuracy] §9.1, §9.5–9.6, Theorem 13.8.
-/

open Finset

universe u

namespace Matrix

variable {n : Type u} {R : Type*}

/-! ### Leading principal submatrices -/

section LeadingPrincipal

variable [LinearOrder n]

/-- The leading principal submatrix `A(≤ k, ≤ k)`, indexed by `{i // i ≤ k}`. On `Fin N` with
`k = ⟨i, _⟩` this is the submatrix `A_{i+1}` of order `i + 1` of [quarteroni2000numerical] §3.3. -/
def leadingPrincipalSubmatrix (A : Matrix n n R) (k : n) :
    Matrix {i // i ≤ k} {i // i ≤ k} R :=
  A.toBlock (· ≤ k) (· ≤ k)

/-- The strict leading principal submatrix `A(< k, < k)`, indexed by `{i // i < k}`. As `k` ranges
over `n` these are exactly the leading principal submatrices of orders `0, …, N - 1`, which is the
hypothesis of the existence theorem for the LU factorization ([quarteroni2000numerical] Theorem
3.4, "`A_i` nonsingular for `i = 1, …, n - 1`"; the order `0` is the empty matrix, a unit). -/
def strictLeadingPrincipalSubmatrix (A : Matrix n n R) (k : n) :
    Matrix {i // i < k} {i // i < k} R :=
  A.toBlock (· < k) (· < k)

/-- The strict leading principal submatrices of the transpose are the transposes. -/
theorem strictLeadingPrincipalSubmatrix_transpose (A : Matrix n n R) (k : n) :
    Aᵀ.strictLeadingPrincipalSubmatrix k = (A.strictLeadingPrincipalSubmatrix k)ᵀ := rfl

/-- The leading principal minor `d_k = det A(≤ k, ≤ k)`. -/
noncomputable def leadingPrincipalMinor [Fintype n] [CommRing R] (A : Matrix n n R) (k : n) :
    R :=
  (A.leadingPrincipalSubmatrix k).det

/-- The entries of a leading principal submatrix. -/
@[simp]
theorem leadingPrincipalSubmatrix_apply (A : Matrix n n R) (k : n) (i j : {i // i ≤ k}) :
    A.leadingPrincipalSubmatrix k i j = A i j := rfl

/-- The entries of a strict leading principal submatrix. -/
@[simp]
theorem strictLeadingPrincipalSubmatrix_apply (A : Matrix n n R) (k : n) (i j : {i // i < k}) :
    A.strictLeadingPrincipalSubmatrix k i j = A i j := rfl

omit [LinearOrder n] in
/-- Reindexing a block along an equivalence of index subtypes: `A.toBlock q q` is the
`submatrix` of `A.toBlock p p` along `Equiv.subtypeEquivRight`. -/
theorem toBlock_eq_submatrix_subtypeEquivRight (A : Matrix n n R) {p q : n → Prop}
    (h : ∀ i, q i ↔ p i) :
    A.toBlock q q = (A.toBlock p p).submatrix (Equiv.subtypeEquivRight h)
      (Equiv.subtypeEquivRight h) := by
  ext i j; rfl

variable [Fintype n]

omit [LinearOrder n] in
/-- Nonsingularity of a block is invariant under equivalent index predicates. -/
theorem isUnit_toBlock_congr [DecidableEq n] [CommRing R] (A : Matrix n n R) {p q : n → Prop}
    [DecidablePred p] [DecidablePred q] (h : ∀ i, q i ↔ p i) :
    IsUnit (A.toBlock q q) ↔ IsUnit (A.toBlock p p) := by
  rw [toBlock_eq_submatrix_subtypeEquivRight A h, isUnit_iff_isUnit_det,
    det_submatrix_equiv_self, ← isUnit_iff_isUnit_det]

/-- If every leading principal submatrix is nonsingular, so is every strict one: `A(< k)` is
either empty or `A(≤ k')` for the predecessor `k'` of `k`. -/
theorem isUnit_strictLeadingPrincipalSubmatrix_of_forall_isUnit [CommRing R] {A : Matrix n n R}
    (h : ∀ k, IsUnit (A.leadingPrincipalSubmatrix k)) (k : n) :
    IsUnit (A.strictLeadingPrincipalSubmatrix k) := by
  by_cases hne : (univ.filter (· < k)).Nonempty
  · set k' := (univ.filter (· < k)).max' hne with hk'
    have hk'k : k' < k := (mem_filter.1 (max'_mem _ hne)).2
    have hiff : ∀ i, i < k ↔ i ≤ k' := fun i =>
      ⟨fun hi => le_max' (univ.filter (· < k)) i (mem_filter.2 ⟨mem_univ _, hi⟩),
        fun hi => hi.trans_lt hk'k⟩
    exact (isUnit_toBlock_congr A hiff).2 (h k')
  · have : IsEmpty {i // i < k} := ⟨fun i => hne ⟨i.1, mem_filter.2 ⟨mem_univ _, i.2⟩⟩⟩
    rw [isUnit_iff_isUnit_det, det_isEmpty]
    exact isUnit_one

end LeadingPrincipal

/-! ### The LU specification -/

section IsLU

variable [LinearOrder n] [Fintype n]

/-- `IsLU A L U`: `L` is unit lower triangular, `U` is upper triangular and `L * U = A`. This is
the specification every LU algorithm satisfies; theorems about "the LU factorization" are
theorems about any pair satisfying it ([quarteroni2000numerical] §3.3.1). -/
structure IsLU [Semiring R] (A L U : Matrix n n R) : Prop where
  /-- The lower factor is unit lower triangular. -/
  isUnitLowerTriangular : L.IsUnitLowerTriangular
  /-- The upper factor is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- The factors multiply to `A`. -/
  mul_eq : L * U = A

variable [Semiring R] {A L U : Matrix n n R}

/-- [quarteroni2000numerical] (3.42): the entry `a_ij` of `A = L U` is `∑_{r ≤ min i j} l_ir u_rj`,
because `L` vanishes to the right of the diagonal and `U` below it. -/
theorem IsLU.apply_eq_sum (h : IsLU A L U) (i j : n) :
    A i j = ∑ r ∈ univ.filter (· ≤ min i j), L i r * U r j := by
  rw [← h.mul_eq, mul_apply]
  refine (Finset.sum_filter_of_ne fun r _ hr => ?_).symm
  rw [le_min_iff]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hir | hjr
  · exact hr (by rw [h.isUnitLowerTriangular.isLowerTriangular
      (OrderDual.toDual_lt_toDual.2 hir), zero_mul])
  · exact hr (by rw [h.isUpperTriangular hjr, mul_zero])

/-- Splitting a product over `{r ≤ i}` into the product over `{r < i}` and the factor at `i`. -/
@[to_additive /-- Splitting a sum over `{r ≤ i}` into the sum over `{r < i}` and the term at
`i`. -/]
theorem prod_filter_le_eq_mul {M : Type*} [CommMonoid M] (f : n → M) (i : n) :
    ∏ r ∈ univ.filter (· ≤ i), f r = (∏ r ∈ univ.filter (· < i), f r) * f i := by
  rw [← Finset.prod_erase_mul (univ.filter (· ≤ i)) f (mem_filter.2 ⟨mem_univ i, le_rfl⟩)]
  congr 2
  ext r
  simp [lt_iff_le_and_ne, and_comm]

/-- The upper factor, entry by entry: for `i ≤ j`, `u_ij = a_ij - ∑_{r < i} l_ir u_rj`
([quarteroni2000numerical] (3.43), first line). -/
theorem IsLU.upper_apply_eq {R : Type*} [Ring R] {A L U : Matrix n n R} (h : IsLU A L U)
    {i j : n} (hij : i ≤ j) :
    U i j = A i j - ∑ r ∈ univ.filter (· < i), L i r * U r j := by
  rw [h.apply_eq_sum, min_eq_left hij, sum_filter_le_eq_add, h.isUnitLowerTriangular.diag_eq_one,
    one_mul, add_sub_cancel_left]

/-- The lower factor, entry by entry: for `j < i`, `l_ij u_jj = a_ij - ∑_{r < j} l_ir u_rj`
([quarteroni2000numerical] (3.43), second line). -/
theorem IsLU.lower_apply_mul_diag_eq {R : Type*} [Ring R] {A L U : Matrix n n R} (h : IsLU A L U)
    {i j : n} (hij : j < i) :
    L i j * U j j = A i j - ∑ r ∈ univ.filter (· < j), L i r * U r j := by
  rw [h.apply_eq_sum, min_eq_right hij.le, sum_filter_le_eq_add, add_sub_cancel_left]

end IsLU

/-! ### Block LU along a labelling -/

section Block

variable [DecidableEq n] {α : Type*} [LinearOrder α] (b : n → α)

/-- Block unit lower triangular along the labelling `b`: block lower triangular in Mathlib's sense
(`Matrix.BlockTriangular (OrderDual.toDual ∘ b)`, entries with `b i < b j` vanish) with identity
diagonal blocks. For `b = id` this is `Matrix.IsUnitLowerTriangular`
(`Matrix.isBlockUnitLowerTriangular_id_iff`). -/
structure IsBlockUnitLowerTriangular [Zero R] [One R] (L : Matrix n n R) : Prop where
  /-- The matrix is block lower triangular. -/
  blockTriangular : L.BlockTriangular (OrderDual.toDual ∘ b)
  /-- Within a diagonal block the matrix is the identity. -/
  apply_eq_one_of_eq : ∀ i j, b i = b j → L i j = (1 : Matrix n n R) i j

/-- `IsBlockLU b A L U`: the block LU factorization of [quarteroni2000numerical] Theorem 3.7
along the block labelling `b : n → α`, with `L` block unit lower triangular and `U` block upper
triangular; `b = id` is `Matrix.IsLU` (`Matrix.isBlockLU_id_iff`). The book's `m × m` blocks of
sizes `n₁, …, n_m` are a monotone `b : Fin N → Fin m`; a general labelling costs nothing and
covers the substructuring orderings of [quarteroni2000numerical] §3.9.2. -/
structure IsBlockLU [Fintype n] [Semiring R] (A L U : Matrix n n R) : Prop where
  /-- The lower factor is block unit lower triangular. -/
  isBlockUnitLowerTriangular : IsBlockUnitLowerTriangular b L
  /-- The upper factor is block upper triangular. -/
  blockTriangular : U.BlockTriangular b
  /-- The factors multiply to `A`. -/
  mul_eq : L * U = A

variable {b}

/-- Relabelling along a strictly monotone map does not change block unit lower triangularity. -/
theorem isBlockUnitLowerTriangular_comp_iff [Zero R] [One R] {β : Type*} [LinearOrder β]
    {f : β → α} (hf : StrictMono f) {b : n → β} {L : Matrix n n R} :
    IsBlockUnitLowerTriangular (f ∘ b) L ↔ IsBlockUnitLowerTriangular b L := by
  constructor
  · rintro ⟨hL, hd⟩
    exact ⟨fun i j hij => hL (OrderDual.toDual_lt_toDual.2
        (hf (OrderDual.toDual_lt_toDual.1 hij))),
      fun i j hij => hd i j (congrArg f hij)⟩
  · rintro ⟨hL, hd⟩
    exact ⟨fun i j hij => hL (OrderDual.toDual_lt_toDual.2
        (hf.lt_iff_lt.1 (OrderDual.toDual_lt_toDual.1 hij))),
      fun i j hij => hd i j (hf.injective hij)⟩

/-- Relabelling along a strictly monotone map does not change block LU. -/
theorem isBlockLU_comp_iff [Fintype n] [Semiring R] {β : Type*} [LinearOrder β]
    {f : β → α} (hf : StrictMono f) {b : n → β} {A L U : Matrix n n R} :
    IsBlockLU (f ∘ b) A L U ↔ IsBlockLU b A L U := by
  constructor
  · rintro ⟨hL, hU, h⟩
    exact ⟨(isBlockUnitLowerTriangular_comp_iff hf).1 hL,
      fun i j hij => hU (hf (hij : b j < b i)), h⟩
  · rintro ⟨hL, hU, h⟩
    exact ⟨(isBlockUnitLowerTriangular_comp_iff hf).2 hL,
      fun i j hij => hU (hf.lt_iff_lt.1 hij), h⟩

variable [Fintype n]

omit [DecidableEq n] in
/-- Within a diagonal block, the product of two block lower triangular matrices is the product
of the diagonal blocks: in `∑ r, M i r * N r j` with `b i = b j`, a nonzero term needs
`b i ≤ b r ≤ b j`. -/
theorem BlockTriangular.mul_apply_of_eq [NonUnitalNonAssocSemiring R] {M N : Matrix n n R}
    (hM : M.BlockTriangular (OrderDual.toDual ∘ b)) (hN : N.BlockTriangular (OrderDual.toDual ∘ b))
    {i j : n} (hij : b i = b j) :
    (M * N) i j = ∑ r ∈ univ.filter (fun r => b r = b i), M i r * N r j := by
  rw [mul_apply]
  refine (Finset.sum_filter_of_ne fun r _ hr => ?_).symm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hr (by rw [hN (show (OrderDual.toDual ∘ b) j < (OrderDual.toDual ∘ b) r from
      OrderDual.toDual_lt_toDual.2 (hij ▸ hlt)), mul_zero])
  · exact hr (by rw [hM (show (OrderDual.toDual ∘ b) r < (OrderDual.toDual ∘ b) i from
      OrderDual.toDual_lt_toDual.2 hlt), zero_mul])

/-- The product of two block unit lower triangular matrices is block unit lower triangular. -/
theorem IsBlockUnitLowerTriangular.mul [NonAssocSemiring R] {L₁ L₂ : Matrix n n R}
    (h₁ : IsBlockUnitLowerTriangular b L₁) (h₂ : IsBlockUnitLowerTriangular b L₂) :
    IsBlockUnitLowerTriangular b (L₁ * L₂) where
  blockTriangular := h₁.blockTriangular.mul h₂.blockTriangular
  apply_eq_one_of_eq i j hij := by
    rw [h₁.blockTriangular.mul_apply_of_eq h₂.blockTriangular hij,
      Finset.sum_eq_single_of_mem (s := univ.filter fun r => b r = b i) i
        (mem_filter.2 ⟨mem_univ i, rfl⟩) fun r hr hri => by
        rw [h₁.apply_eq_one_of_eq i r (mem_filter.1 hr).2.symm, one_apply_ne (Ne.symm hri),
          zero_mul],
      h₁.apply_eq_one_of_eq i i rfl, one_apply_eq, one_mul, h₂.apply_eq_one_of_eq i j hij]

omit [Fintype n] in
/-- The identity is block unit lower triangular. -/
theorem isBlockUnitLowerTriangular_one [Zero R] [One R] :
    IsBlockUnitLowerTriangular b (1 : Matrix n n R) :=
  ⟨blockTriangular_one, fun _ _ _ => rfl⟩

/-- A block unit lower triangular matrix has determinant `1`: its determinant is the product of
the determinants of its diagonal blocks, which are identity matrices. -/
theorem IsBlockUnitLowerTriangular.det_eq_one [CommRing R] {L : Matrix n n R}
    (hL : IsBlockUnitLowerTriangular b L) : L.det = 1 := by
  rw [hL.blockTriangular.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : L.toSquareBlock (OrderDual.toDual ∘ b) a = 1 := by
    ext i j
    rw [toSquareBlock_def, of_apply, hL.apply_eq_one_of_eq i j
      (OrderDual.toDual.injective (i.2.trans j.2.symm))]
    exact congrFun (congrFun (toBlock_one_self (fun i => (OrderDual.toDual ∘ b) i = a)) i) j
  rw [this, det_one]

/-- A block unit lower triangular matrix is a unit. -/
theorem IsBlockUnitLowerTriangular.isUnit [CommRing R] {L : Matrix n n R}
    (hL : IsBlockUnitLowerTriangular b L) : IsUnit L :=
  (isUnit_iff_isUnit_det L).2 (by rw [hL.det_eq_one]; exact isUnit_one)

/-! #### Restriction to a leading block of labels -/

omit [DecidableEq n] in
/-- The product of two matrices, restricted to a pair of blocks, is the sum over the two
complementary middle blocks (`Matrix.toBlock_mul_eq_add` without commutativity). -/
theorem toBlock_mul_eq_add' [NonUnitalNonAssocSemiring R] (p : n → Prop) (q : n → Prop)
    [DecidablePred q] (r : n → Prop) (A B : Matrix n n R) :
    (A * B).toBlock p r =
      A.toBlock p q * B.toBlock q r +
        (A.toBlock p fun i => ¬q i) * B.toBlock (fun i => ¬q i) r := by
  ext i k
  simp only [toBlock_apply, mul_apply, add_apply]
  exact (Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm

variable {p : n → Prop} [DecidablePred p]

omit [DecidableEq n] [Fintype n] [DecidablePred p] in
/-- A block lower triangular matrix vanishes on the block `(p, ¬p)` when `p` is closed under
decreasing the label. -/
theorem BlockTriangular.toBlock_not_eq_zero [Zero R] {L : Matrix n n R}
    (hL : L.BlockTriangular (OrderDual.toDual ∘ b)) (hp : ∀ i j, p i → b j ≤ b i → p j) :
    L.toBlock p (fun i => ¬p i) = 0 := by
  ext i j
  rw [toBlock_apply, zero_apply]
  refine hL (OrderDual.toDual_lt_toDual.2 (lt_of_not_ge fun h => ?_))
  exact j.2 (hp i.1 j.1 i.2 h)

omit [DecidableEq n] [Fintype n] [DecidablePred p] in
/-- A block upper triangular matrix vanishes on the block `(¬p, p)` when `p` is closed under
decreasing the label. -/
theorem BlockTriangular.not_toBlock_eq_zero [Zero R] {U : Matrix n n R} (hU : U.BlockTriangular b)
    (hp : ∀ i j, p i → b j ≤ b i → p j) : U.toBlock (fun i => ¬p i) p = 0 := by
  ext i j
  rw [toBlock_apply, zero_apply]
  refine hU (lt_of_not_ge fun h => ?_)
  exact i.2 (hp j.1 i.1 j.2 h)

omit [Fintype n] [DecidablePred p] in
/-- The identity restricted to a diagonal block is the identity. -/
theorem IsBlockUnitLowerTriangular.toBlock_eq_one [Zero R] [One R] {L : Matrix n n R}
    (hL : IsBlockUnitLowerTriangular b L) (hq : ∀ i j, ¬p i → ¬p j → b i = b j) :
    L.toBlock (fun i => ¬p i) (fun i => ¬p i) = 1 := by
  ext i j
  rw [toBlock_apply, hL.apply_eq_one_of_eq i.1 j.1 (hq _ _ i.2 j.2)]
  exact congrFun (congrFun (toBlock_one_self (fun i => ¬p i)) i) j

variable [Semiring R] {A L U : Matrix n n R}

/-- A block LU factorization restricts to every leading block of labels: for `p` closed under
decreasing the label, `A.toBlock p p = L.toBlock p p * U.toBlock p p` and the restricted factors
keep their shapes. This is [quarteroni2000numerical] (3.38) read downwards. -/
theorem IsBlockLU.toBlock (h : IsBlockLU b A L U) (hp : ∀ i j, p i → b j ≤ b i → p j) :
    IsBlockLU (b ∘ Subtype.val) (A.toBlock p p) (L.toBlock p p) (U.toBlock p p) where
  isBlockUnitLowerTriangular :=
    ⟨h.isBlockUnitLowerTriangular.blockTriangular.submatrix,
     fun i j hij => by
      rw [toBlock_apply, h.isBlockUnitLowerTriangular.apply_eq_one_of_eq i.1 j.1 hij]
      exact congrFun (congrFun (toBlock_one_self p) i) j⟩
  blockTriangular := h.blockTriangular.submatrix
  mul_eq := by
    rw [← h.mul_eq, toBlock_mul_eq_add' p p p,
      h.isBlockUnitLowerTriangular.blockTriangular.toBlock_not_eq_zero hp, Matrix.zero_mul,
      add_zero]

/-- The block `(¬p, p)` of `A = L U`, for `p` closed under decreasing the label: the bordering
equation `A₂₁ = L₂₁ U₁₁`. -/
theorem IsBlockLU.toBlock_not_left (h : IsBlockLU b A L U)
    (hp : ∀ i j, p i → b j ≤ b i → p j) :
    A.toBlock (fun i => ¬p i) p = L.toBlock (fun i => ¬p i) p * U.toBlock p p := by
  rw [← h.mul_eq, toBlock_mul_eq_add' _ p, h.blockTriangular.not_toBlock_eq_zero hp,
    Matrix.mul_zero, add_zero]

/-- The block `(p, ¬p)` of `A = L U`, for `p` closed under decreasing the label: the bordering
equation `A₁₂ = L₁₁ U₁₂`. -/
theorem IsBlockLU.toBlock_not_right (h : IsBlockLU b A L U)
    (hp : ∀ i j, p i → b j ≤ b i → p j) :
    A.toBlock p (fun i => ¬p i) = L.toBlock p p * U.toBlock p (fun i => ¬p i) := by
  rw [← h.mul_eq, toBlock_mul_eq_add' _ p,
    h.isBlockUnitLowerTriangular.blockTriangular.toBlock_not_eq_zero hp, Matrix.zero_mul,
    add_zero]

/-- The block `(¬p, ¬p)` of `A = L U` when `¬p` is a single block: the bordering equation
`A₂₂ = L₂₁ U₁₂ + U₂₂`. -/
theorem IsBlockLU.toBlock_not_not (h : IsBlockLU b A L U)
    (hq : ∀ i j, ¬p i → ¬p j → b i = b j) :
    A.toBlock (fun i => ¬p i) (fun i => ¬p i) =
      L.toBlock (fun i => ¬p i) p * U.toBlock p (fun i => ¬p i) +
        U.toBlock (fun i => ¬p i) (fun i => ¬p i) := by
  rw [← h.mul_eq, toBlock_mul_eq_add' _ p, h.isBlockUnitLowerTriangular.toBlock_eq_one hq,
    Matrix.one_mul]

end Block

section BlockId

variable [LinearOrder n] [DecidableEq n]

/-- Along `b = id`, block unit lower triangular is unit lower triangular. -/
theorem isBlockUnitLowerTriangular_id_iff [Zero R] [One R] {L : Matrix n n R} :
    IsBlockUnitLowerTriangular id L ↔ L.IsUnitLowerTriangular := by
  constructor
  · rintro ⟨hL, hd⟩
    exact ⟨hL, fun i => by simpa using hd i i rfl⟩
  · rintro ⟨hL, hd⟩
    refine ⟨hL, fun i j hij => ?_⟩
    obtain rfl : i = j := hij
    simp [hd]

/-- Along `b = id`, block LU is LU. -/
theorem isBlockLU_id_iff [Fintype n] [Semiring R] {A L U : Matrix n n R} :
    IsBlockLU id A L U ↔ IsLU A L U :=
  ⟨fun h => ⟨isBlockUnitLowerTriangular_id_iff.1 h.isBlockUnitLowerTriangular,
    h.blockTriangular, h.mul_eq⟩,
   fun h => ⟨isBlockUnitLowerTriangular_id_iff.2 h.isUnitLowerTriangular,
    h.isUpperTriangular, h.mul_eq⟩⟩

end BlockId

/-! ### Determinants and pivots -/

section Det

variable [LinearOrder n] [Fintype n] [CommRing R] {A L U : Matrix n n R}

/-- An LU factorization restricts to every leading principal block
([quarteroni2000numerical] (3.38)). -/
theorem IsLU.toBlock_le (h : IsLU A L U) (k : n) :
    IsLU (A.leadingPrincipalSubmatrix k) (L.leadingPrincipalSubmatrix k)
      (U.leadingPrincipalSubmatrix k) :=
  isBlockLU_id_iff.1 ((isBlockLU_comp_iff (b := id) (Subtype.strictMono_coe (· ≤ k))).1
    ((isBlockLU_id_iff.2 h).toBlock (p := (· ≤ k)) fun _ _ hi hji => hji.trans hi))

/-- An LU factorization restricts to every strict leading principal block. -/
theorem IsLU.toBlock_lt (h : IsLU A L U) (k : n) :
    IsLU (A.strictLeadingPrincipalSubmatrix k) (L.strictLeadingPrincipalSubmatrix k)
      (U.strictLeadingPrincipalSubmatrix k) :=
  isBlockLU_id_iff.1 ((isBlockLU_comp_iff (b := id) (Subtype.strictMono_coe (· < k))).1
    ((isBlockLU_id_iff.2 h).toBlock (p := (· < k)) fun _ _ hi hji => hji.trans_lt hi))

/-- The determinant of `A = L U` is the product of the diagonal of `U`
([quarteroni2000numerical], after Example 3.3). -/
theorem IsLU.det_eq_prod_diag (h : IsLU A L U) : A.det = ∏ i, U i i := by
  rw [← h.mul_eq, det_mul, h.isUnitLowerTriangular.det_eq_one, one_mul,
    det_of_isUpperTriangular h.isUpperTriangular]

/-- [quarteroni2000numerical] (3.39): the leading principal minors of `A = L U` are the products
of the leading pivots, `det A(≤ k) = ∏_{i ≤ k} u_ii`. -/
theorem IsLU.det_leadingPrincipalSubmatrix (h : IsLU A L U) (k : n) :
    (A.leadingPrincipalSubmatrix k).det = ∏ i ∈ univ.filter (· ≤ k), U i i := by
  -- the two `DecidableEq {i // i ≤ k}` instances in play are propositionally equal
  have h1 : (A.leadingPrincipalSubmatrix k).det = ∏ i : {i // i ≤ k}, U i i := by
    convert (h.toBlock_le k).det_eq_prod_diag using 2
    rfl
  rw [h1, Finset.prod_subtype (p := (· ≤ k)) (univ.filter (· ≤ k)) (by simp) fun i => U i i]

/-- The strict leading principal minors of `A = L U` are the products of the strict leading
pivots, `det A(< k) = ∏_{i < k} u_ii`. -/
theorem IsLU.det_strictLeadingPrincipalSubmatrix (h : IsLU A L U) (k : n) :
    (A.strictLeadingPrincipalSubmatrix k).det = ∏ i ∈ univ.filter (· < k), U i i := by
  have h1 : (A.strictLeadingPrincipalSubmatrix k).det = ∏ i : {i // i < k}, U i i := by
    convert (h.toBlock_lt k).det_eq_prod_diag using 2
    rfl
  rw [h1, Finset.prod_subtype (p := (· < k)) (univ.filter (· < k)) (by simp) fun i => U i i]

variable {K : Type*} [Field K] {A L U : Matrix n n K}

/-- If the strict leading principal submatrix `A(< k)` of `A = L U` is nonsingular, the pivots
before `k` are nonzero. -/
theorem IsLU.diag_upper_ne_zero_of_lt (h : IsLU A L U) {k : n}
    (hk : IsUnit (A.strictLeadingPrincipalSubmatrix k)) {j : n} (hj : j < k) : U j j ≠ 0 := by
  have hdet := (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 hk))
  rw [h.det_strictLeadingPrincipalSubmatrix, Finset.prod_ne_zero_iff] at hdet
  exact hdet j (mem_filter.2 ⟨mem_univ _, hj⟩)

/-- The pivots are ratios of consecutive leading principal minors,
`u_kk = det A(≤ k) / det A(< k)` ([quarteroni2000numerical] §3.3.1, after (3.39)). -/
theorem IsLU.diag_upper_eq_div_leadingPrincipalMinor (h : IsLU A L U) {k : n}
    (hk : (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    U k k = (A.leadingPrincipalSubmatrix k).det / (A.strictLeadingPrincipalSubmatrix k).det := by
  rw [eq_div_iff hk, h.det_leadingPrincipalSubmatrix, h.det_strictLeadingPrincipalSubmatrix,
    prod_filter_le_eq_mul, mul_comm]

end Det

/-! ### Existence and uniqueness of the block LU factorization -/

/-! ### Leading principal submatrices on `Fin N` -/

section Fin

/-- On `Fin N`, the leading principal submatrix `A(≤ k)` is, up to the reindexing of `{i // i ≤ k}`
by `Fin (k + 1)`, the submatrix along `Fin.castLE`, so the two have the same determinant. -/
theorem det_leadingPrincipalSubmatrix_fin {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (k : Fin N) :
    (A.leadingPrincipalSubmatrix k).det =
      (A.submatrix (Fin.castLE (Nat.succ_le_of_lt k.2))
        (Fin.castLE (Nat.succ_le_of_lt k.2))).det := by
  let e : Fin (k + 1) ≃ {i : Fin N // i ≤ k} :=
    { toFun := fun a => ⟨Fin.castLE (Nat.succ_le_of_lt k.2) a, Fin.le_def.2 (Nat.lt_succ_iff.1 a.2)⟩
      invFun := fun i => ⟨i.1, Nat.lt_succ_of_le (Fin.le_def.1 i.2)⟩
      left_inv := fun a => rfl
      right_inv := fun i => rfl }
  rw [← det_submatrix_equiv_self e]
  rfl

end Fin

/-! ### Block tridiagonal matrices -/

section BlockTridiagonal

/-- **The block bandwidth of the block LU factors** ([quarteroni2000numerical] §3.8.3). For a
block tridiagonal `A` on `Fin N` with blocks labelled by a map `b : Fin N → Fin m` — the blocks
`A_{ij}` with `|i - j| ≥ 2` vanish — whose leading principal block submatrices are nonsingular,
the block LU factors are block bidiagonal: `L` has only its diagonal and first subdiagonal
blocks, `U` only its diagonal and first superdiagonal blocks. This is the block form of
`Matrix.IsLU.hasLowerBandwidth`; as there, the clause for `U` needs no hypothesis on the leading
blocks, while the clause for `L` does (`Matrix.IsBlockLU.toBlock`,
`Matrix.IsBlockLU.toBlock_not_left`, `Matrix.IsBlockLU.toBlock_not_right`). -/
theorem IsBlockLU.blockBidiagonal_of_blockTridiagonal {N m : ℕ} {b : Fin N → Fin m} {K : Type*}
    [Field K] {A L U : Matrix (Fin N) (Fin N) K} (h : IsBlockLU b A L U)
    (htriL : ∀ i j, (b j : ℕ) + 1 < b i → A i j = 0)
    (htriU : ∀ i j, (b i : ℕ) + 1 < b j → A i j = 0)
    (hlead : ∀ k : Fin m, IsUnit (A.toBlock (b · ≤ k) (b · ≤ k))) :
    (∀ i j, (b j : ℕ) + 1 < b i → L i j = 0) ∧ ∀ i j, (b i : ℕ) + 1 < b j → U i j = 0 := by
  constructor
  · intro i j hij
    have hp : ∀ x y : Fin N, b x ≤ b j → b y ≤ b x → b y ≤ b j := fun _ _ hx hyx => hyx.trans hx
    have hLp : IsUnit (L.toBlock (b · ≤ b j) (b · ≤ b j)) :=
      (h.toBlock hp).isBlockUnitLowerTriangular.isUnit
    have hUp : IsUnit (U.toBlock (b · ≤ b j) (b · ≤ b j)) := by
      have hmul := (h.toBlock hp).mul_eq
      rw [isUnit_iff_isUnit_det] at hLp ⊢
      have hAp := hlead (b j)
      rw [isUnit_iff_isUnit_det, ← hmul, det_mul] at hAp
      exact isUnit_of_mul_isUnit_right hAp
    have hLeq : L.toBlock (fun x => ¬ b x ≤ b j) (b · ≤ b j) =
        A.toBlock (fun x => ¬ b x ≤ b j) (b · ≤ b j) *
          (U.toBlock (b · ≤ b j) (b · ≤ b j))⁻¹ := by
      rw [h.toBlock_not_left hp, Matrix.mul_assoc,
        mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hUp), Matrix.mul_one]
    have hi : ¬ b i ≤ b j := not_le.2 (Fin.lt_def.2 (by omega))
    have hentry := congrFun (congrFun hLeq ⟨i, hi⟩) ⟨j, le_rfl⟩
    rw [toBlock_apply, mul_apply] at hentry
    rw [hentry]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [toBlock_apply, htriL i x.1 (by have := Fin.le_def.1 x.2; omega), zero_mul]
  · intro i j hij
    have hp : ∀ x y : Fin N, b x ≤ b i → b y ≤ b x → b y ≤ b i := fun _ _ hx hyx => hyx.trans hx
    have hLp : IsUnit (L.toBlock (b · ≤ b i) (b · ≤ b i)) :=
      (h.toBlock hp).isBlockUnitLowerTriangular.isUnit
    have hUeq : U.toBlock (b · ≤ b i) (fun x => ¬ b x ≤ b i) =
        (L.toBlock (b · ≤ b i) (b · ≤ b i))⁻¹ *
          A.toBlock (b · ≤ b i) (fun x => ¬ b x ≤ b i) := by
      rw [h.toBlock_not_right hp, ← Matrix.mul_assoc,
        nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hLp), Matrix.one_mul]
    have hj : ¬ b j ≤ b i := not_le.2 (Fin.lt_def.2 (by omega))
    have hentry := congrFun (congrFun hUeq ⟨i, le_rfl⟩) ⟨j, hj⟩
    rw [toBlock_apply, mul_apply] at hentry
    rw [hentry]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [toBlock_apply, htriU x.1 j (by have := Fin.le_def.1 x.2; omega), mul_zero]

end BlockTridiagonal

section BlockExistence

variable {α : Type*} [LinearOrder α]

/-- Reindexed along `Equiv.sumCompl p`, a square matrix is the `fromBlocks` of its four blocks. -/
theorem submatrix_sumCompl_eq_fromBlocks (A : Matrix n n R) (p : n → Prop) [DecidablePred p] :
    A.submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) =
      fromBlocks (A.toBlock p p) (A.toBlock p fun i => ¬p i)
        (A.toBlock (fun i => ¬p i) p) (A.toBlock (fun i => ¬p i) fun i => ¬p i) := by
  ext (i | i) (j | j) <;> rfl

/-- Two matrices agree when their four blocks along a predicate agree. -/
theorem ext_of_toBlock {M N : Matrix n n R} (p : n → Prop)
    (h₁₁ : M.toBlock p p = N.toBlock p p)
    (h₁₂ : M.toBlock p (fun i => ¬p i) = N.toBlock p (fun i => ¬p i))
    (h₂₁ : M.toBlock (fun i => ¬p i) p = N.toBlock (fun i => ¬p i) p)
    (h₂₂ : M.toBlock (fun i => ¬p i) (fun i => ¬p i) = N.toBlock (fun i => ¬p i) (fun i => ¬p i)) :
    M = N := by
  classical
  ext i j
  by_cases hi : p i <;> by_cases hj : p j
  · exact congrFun (congrFun h₁₁ ⟨i, hi⟩) ⟨j, hj⟩
  · exact congrFun (congrFun h₁₂ ⟨i, hi⟩) ⟨j, hj⟩
  · exact congrFun (congrFun h₂₁ ⟨i, hi⟩) ⟨j, hj⟩
  · exact congrFun (congrFun h₂₂ ⟨i, hi⟩) ⟨j, hj⟩

variable {m : Type*} [DecidableEq m] [DecidableEq n]

/-- Reindexing along an equivalence relabels a block unit lower triangular matrix. -/
theorem isBlockUnitLowerTriangular_reindex_iff [Zero R] [One R] {e : m ≃ n} {L : Matrix m m R}
    {b : n → α} :
    IsBlockUnitLowerTriangular b (reindex e e L) ↔ IsBlockUnitLowerTriangular (b ∘ e) L := by
  constructor
  · rintro ⟨hL, hd⟩
    refine ⟨blockTriangular_reindex_iff.1 hL, fun x y hxy => ?_⟩
    have h := hd (e x) (e y) hxy
    rwa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      ← submatrix_one_equiv e.symm, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply] at h
  · rintro ⟨hL, hd⟩
    refine ⟨blockTriangular_reindex_iff.2 hL, fun i j hij => ?_⟩
    rw [reindex_apply, submatrix_apply, ← submatrix_one_equiv e.symm, submatrix_apply]
    exact hd (e.symm i) (e.symm j) (by simpa using hij)

variable [Fintype m] [Fintype n]

/-- Reindexing along an equivalence relabels a block LU factorization. -/
theorem isBlockLU_reindex_iff [Semiring R] {e : m ≃ n} {A L U : Matrix m m R} {b : n → α} :
    IsBlockLU b (reindex e e A) (reindex e e L) (reindex e e U) ↔ IsBlockLU (b ∘ e) A L U := by
  constructor
  · rintro ⟨hL, hU, h⟩
    refine ⟨isBlockUnitLowerTriangular_reindex_iff.1 hL, blockTriangular_reindex_iff.1 hU, ?_⟩
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv] at h
    exact (reindex e e).injective (by simpa [reindex_apply] using h)
  · rintro ⟨hL, hU, h⟩
    refine ⟨isBlockUnitLowerTriangular_reindex_iff.2 hL, blockTriangular_reindex_iff.2 hU, ?_⟩
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, h]

variable {K : Type*} [Field K]

/-- **The bordering step.** If the leading block `A₁₁` has a block LU factorization `L' U'` with
both factors nonsingular, and the trailing labels form a single block above all the leading
ones, then the whole matrix has the block LU factorization
`[[L', 0], [A₂₁ U'⁻¹, 1]] · [[U', L'⁻¹ A₁₂], [0, A₂₂ - A₂₁ U'⁻¹ L'⁻¹ A₁₂]]`
([quarteroni2000numerical] §3.8.1, and the induction step of Theorem 3.4). -/
theorem isBlockLU_fromBlocks {c : m ⊕ n → α} (hc : ∀ x y, c (Sum.inl x) < c (Sum.inr y))
    (hc' : ∀ y y', c (Sum.inr y) = c (Sum.inr y'))
    {A₁₁ L' U' : Matrix m m K} {A₁₂ : Matrix m n K} {A₂₁ : Matrix n m K} {A₂₂ : Matrix n n K}
    (h : IsBlockLU (c ∘ Sum.inl) A₁₁ L' U') (hL' : IsUnit L') (hU' : IsUnit U') :
    IsBlockLU c (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (fromBlocks L' 0 (A₂₁ * U'⁻¹) 1)
      (fromBlocks U' (L'⁻¹ * A₁₂) 0 (A₂₂ - A₂₁ * U'⁻¹ * (L'⁻¹ * A₁₂))) where
  isBlockUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · have hij' : c i < c j := OrderDual.toDual_lt_toDual.1 hij
      rcases i with i | i <;> rcases j with j | j
      · exact h.isBlockUnitLowerTriangular.blockTriangular (OrderDual.toDual_lt_toDual.2 hij')
      · rfl
      · exact absurd ((hc j i).trans hij') (lt_irrefl _)
      · exact absurd (hc' i j ▸ hij') (lt_irrefl _)
    · rcases i with i | i <;> rcases j with j | j
      · rw [fromBlocks_apply₁₁, h.isBlockUnitLowerTriangular.apply_eq_one_of_eq i j hij]
        simp [one_apply]
      · exact absurd (hij ▸ hc i j) (lt_irrefl _)
      · exact absurd (hij ▸ hc j i) (lt_irrefl _)
      · simp [one_apply]
  blockTriangular := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact h.blockTriangular hij
    · exact absurd ((hc i j).trans hij) (lt_irrefl _)
    · rfl
    · exact absurd (hc' j i ▸ hij) (lt_irrefl _)
  mul_eq := by
    have hLd : IsUnit L'.det := (isUnit_iff_isUnit_det _).1 hL'
    have hUd : IsUnit U'.det := (isUnit_iff_isUnit_det _).1 hU'
    rw [fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, add_zero]
    rw [h.mul_eq, mul_nonsing_inv_cancel_left _ _ hLd, nonsing_inv_mul_cancel_right _ _ hUd,
      add_sub_cancel]

/-- The strict leading block hypothesis of the block LU theorem passes to the leading block
`{i | b i < k}`, relabelled by `b`. -/
theorem forall_isUnit_toBlock_comp_val {b : n → α} {A : Matrix n n K}
    (hA : ∀ a ∈ Set.range b, IsUnit (A.toBlock (b · < a) (b · < a))) (k : α) :
    ∀ a ∈ Set.range (b ∘ (Subtype.val : {i // b i < k} → n)),
      IsUnit ((A.toBlock (b · < k) (b · < k)).toBlock ((b ∘ Subtype.val) · < a)
        ((b ∘ Subtype.val) · < a)) := by
  rintro a ⟨i, rfl⟩
  let e : {x : {i // b i < k} // (b ∘ Subtype.val) x < (b ∘ Subtype.val) i} ≃
      {x // b x < (b ∘ Subtype.val) i} :=
    Equiv.subtypeSubtypeEquivSubtype (p := fun i => b i < k)
      (q := fun x => b x < (b ∘ Subtype.val) i) fun hx => hx.trans i.2
  have : (A.toBlock (b · < k) (b · < k)).toBlock ((b ∘ Subtype.val) · < (b ∘ Subtype.val) i)
      ((b ∘ Subtype.val) · < (b ∘ Subtype.val) i) =
      (A.toBlock (b · < (b ∘ Subtype.val) i) (b · < (b ∘ Subtype.val) i)).submatrix e e := by
    ext x y; rfl
  rw [this, isUnit_iff_isUnit_det, det_submatrix_equiv_self, ← isUnit_iff_isUnit_det]
  exact hA _ ⟨i.1, rfl⟩

omit [Fintype n] [DecidableEq n] in
/-- Existence of the block LU factorization, by strong induction on the number of indices: the
last block of labels is bordered onto the factorization of the leading block
(`Matrix.isBlockLU_fromBlocks`). -/
theorem exists_isBlockLU_of_card (N : ℕ) :
    ∀ {n : Type u} [Fintype n] [DecidableEq n] (b : n → α) (A : Matrix n n K),
      Fintype.card n = N → (∀ a ∈ Set.range b, IsUnit (A.toBlock (b · < a) (b · < a))) →
        ∃ L U, IsBlockLU b A L U := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n _ _ b A hN hA
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, isBlockUnitLowerTriangular_one, blockTriangular_one,
      Matrix.ext fun i => isEmptyElim i⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image univ b univ_nonempty
  have hle : ∀ i, b i ≤ b i₀ := fun i => hi₀ i (mem_univ i)
  have hbk : ∀ i, ¬ b i < b i₀ → b i = b i₀ := fun i h => le_antisymm (hle i) (not_lt.1 h)
  have hcard : Fintype.card {i // b i < b i₀} < N :=
    hN ▸ Fintype.card_subtype_lt (x := i₀) (lt_irrefl _)
  obtain ⟨L', U', hLU'⟩ := ih _ hcard (b ∘ Subtype.val) (A.toBlock (b · < b i₀) (b · < b i₀)) rfl
    (forall_isUnit_toBlock_comp_val hA (b i₀))
  have hA' : IsUnit (A.toBlock (b · < b i₀) (b · < b i₀)) := hA _ ⟨i₀, rfl⟩
  rw [← hLU'.mul_eq, isUnit_iff_isUnit_det, det_mul, IsUnit.mul_iff, ← isUnit_iff_isUnit_det,
    ← isUnit_iff_isUnit_det] at hA'
  obtain ⟨hL', hU'⟩ := hA'
  set e := Equiv.sumCompl (fun i => b i < b i₀)
  have hAe : A = reindex e e (A.submatrix e e) := by
    rw [reindex_apply, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  rw [submatrix_sumCompl_eq_fromBlocks] at hAe
  rw [hAe]
  refine ⟨reindex e e (fromBlocks L' 0 (A.toBlock (fun i => ¬ b i < b i₀) (b · < b i₀) * U'⁻¹) 1),
    reindex e e (fromBlocks U' (L'⁻¹ * A.toBlock (b · < b i₀) (fun i => ¬ b i < b i₀)) 0
      (A.toBlock (fun i => ¬ b i < b i₀) (fun i => ¬ b i < b i₀) -
        A.toBlock (fun i => ¬ b i < b i₀) (b · < b i₀) * U'⁻¹ *
          (L'⁻¹ * A.toBlock (b · < b i₀) (fun i => ¬ b i < b i₀)))), ?_⟩
  rw [isBlockLU_reindex_iff]
  refine isBlockLU_fromBlocks (c := b ∘ e) (fun x y => ?_) (fun y y' => ?_) hLU' hL' hU'
  · exact x.2.trans_eq (hbk y.1 y.2).symm
  · exact (hbk y.1 y.2).trans (hbk y'.1 y'.2).symm

/-- **Existence of the block LU factorization** ([quarteroni2000numerical] Theorem 3.7, the
existence half): if every strict leading block `A(b < a)`, `a` a label, is nonsingular, then `A`
has a block LU factorization along `b`. -/
theorem exists_isBlockLU_of_forall_isUnit {b : n → α} {A : Matrix n n K}
    (hA : ∀ a ∈ Set.range b, IsUnit (A.toBlock (b · < a) (b · < a))) :
    ∃ L U, IsBlockLU b A L U :=
  exists_isBlockLU_of_card _ b A rfl hA

omit [DecidableEq m] [Fintype m] in
/-- **Uniqueness of the block LU factorization** ([quarteroni2000numerical] Theorem 3.7, the
uniqueness half), by the same induction as the existence: on the leading block the two
factorizations agree by induction, and the bordering equations
(`Matrix.IsBlockLU.toBlock_not_left`, `…_right`, `…_not_not`) determine the last block. -/
theorem isBlockLU_unique_of_card (N : ℕ) :
    ∀ {n : Type u} [Fintype n] [DecidableEq n] (b : n → α) (A L₁ U₁ L₂ U₂ : Matrix n n K),
      Fintype.card n = N → (∀ a ∈ Set.range b, IsUnit (A.toBlock (b · < a) (b · < a))) →
        IsBlockLU b A L₁ U₁ → IsBlockLU b A L₂ U₂ → L₁ = L₂ ∧ U₁ = U₂ := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n _ _ b A L₁ U₁ L₂ U₂ hN hA h₁ h₂
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨Matrix.ext fun i => isEmptyElim i, Matrix.ext fun i => isEmptyElim i⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image univ b univ_nonempty
  have hle : ∀ i, b i ≤ b i₀ := fun i => hi₀ i (mem_univ i)
  have hbk : ∀ i, ¬ b i < b i₀ → b i = b i₀ := fun i h => le_antisymm (hle i) (not_lt.1 h)
  set p : n → Prop := fun i => b i < b i₀ with hp
  have hpd : ∀ i j, p i → b j ≤ b i → p j := fun i j hi hji => hji.trans_lt hi
  have hq : ∀ i j, ¬p i → ¬p j → b i = b j := fun i j hi hj => (hbk i hi).trans (hbk j hj).symm
  have hcard : Fintype.card {i // p i} < N :=
    hN ▸ Fintype.card_subtype_lt (x := i₀) (lt_irrefl _)
  -- the leading block
  obtain ⟨hL, hU⟩ := ih _ hcard (b ∘ Subtype.val) (A.toBlock p p) (L₁.toBlock p p) (U₁.toBlock p p)
    (L₂.toBlock p p) (U₂.toBlock p p) rfl (forall_isUnit_toBlock_comp_val hA (b i₀))
    (h₁.toBlock hpd) (h₂.toBlock hpd)
  have hA' : IsUnit (A.toBlock p p) := hA _ ⟨i₀, rfl⟩
  rw [← (h₁.toBlock hpd).mul_eq, isUnit_iff_isUnit_det, det_mul, IsUnit.mul_iff] at hA'
  obtain ⟨hL', hU'⟩ := hA'
  -- the bordering blocks
  have hL₂₁ : L₁.toBlock (fun i => ¬p i) p = L₂.toBlock (fun i => ¬p i) p := by
    have := (h₁.toBlock_not_left hpd).symm.trans (h₂.toBlock_not_left hpd)
    rw [← hU] at this
    calc L₁.toBlock (fun i => ¬p i) p
        = L₁.toBlock (fun i => ¬p i) p * U₁.toBlock p p * (U₁.toBlock p p)⁻¹ :=
          (mul_nonsing_inv_cancel_right _ _ hU').symm
      _ = L₂.toBlock (fun i => ¬p i) p * U₁.toBlock p p * (U₁.toBlock p p)⁻¹ := by rw [this]
      _ = L₂.toBlock (fun i => ¬p i) p := mul_nonsing_inv_cancel_right _ _ hU'
  have hU₁₂ : U₁.toBlock p (fun i => ¬p i) = U₂.toBlock p (fun i => ¬p i) := by
    have := (h₁.toBlock_not_right hpd).symm.trans (h₂.toBlock_not_right hpd)
    rw [hL] at this
    calc U₁.toBlock p (fun i => ¬p i)
        = (L₂.toBlock p p)⁻¹ * (L₂.toBlock p p * U₁.toBlock p (fun i => ¬p i)) :=
          (nonsing_inv_mul_cancel_left _ _ (hL ▸ hL')).symm
      _ = (L₂.toBlock p p)⁻¹ * (L₂.toBlock p p * U₂.toBlock p (fun i => ¬p i)) := by rw [this]
      _ = U₂.toBlock p (fun i => ¬p i) := nonsing_inv_mul_cancel_left _ _ (hL ▸ hL')
  have hU₂₂ : U₁.toBlock (fun i => ¬p i) (fun i => ¬p i) =
      U₂.toBlock (fun i => ¬p i) (fun i => ¬p i) := by
    have := (h₁.toBlock_not_not hq).symm.trans (h₂.toBlock_not_not hq)
    rwa [hL₂₁, hU₁₂, add_right_inj] at this
  refine ⟨ext_of_toBlock p hL ?_ hL₂₁ ?_, ext_of_toBlock p hU hU₁₂ ?_ hU₂₂⟩
  · rw [h₁.isBlockUnitLowerTriangular.blockTriangular.toBlock_not_eq_zero hpd,
      h₂.isBlockUnitLowerTriangular.blockTriangular.toBlock_not_eq_zero hpd]
  · rw [h₁.isBlockUnitLowerTriangular.toBlock_eq_one hq,
      h₂.isBlockUnitLowerTriangular.toBlock_eq_one hq]
  · rw [h₁.blockTriangular.not_toBlock_eq_zero hpd, h₂.blockTriangular.not_toBlock_eq_zero hpd]

/-- **Uniqueness of the block LU factorization** ([quarteroni2000numerical] Theorem 3.7): two
block LU factorizations of a matrix whose strict leading blocks are nonsingular coincide. -/
theorem IsBlockLU.unique {b : n → α} {A L₁ U₁ L₂ U₂ : Matrix n n K}
    (hA : ∀ a ∈ Set.range b, IsUnit (A.toBlock (b · < a) (b · < a)))
    (h₁ : IsBlockLU b A L₁ U₁) (h₂ : IsBlockLU b A L₂ U₂) : L₁ = L₂ ∧ U₁ = U₂ :=
  isBlockLU_unique_of_card _ b A L₁ U₁ L₂ U₂ rfl hA h₁ h₂

/-- If some strict leading block `A(b < a)` of `A = L U` is singular, the factorization is not
unique: with `y ≠ 0` in the left kernel of `U(b < a)` and `E` the matrix with the single nonzero
row `y` (padded) at an index of label `a`, `(L (1 + E), (1 - E) U)` is a second factorization
([quarteroni2000numerical] Theorem 3.4, the necessity half, and Example 3.3). -/
theorem IsBlockLU.exists_ne_of_not_isUnit {b : n → α} {A L U : Matrix n n K}
    (h : IsBlockLU b A L U) {a : α} (ha : a ∈ Set.range b)
    (hA : ¬ IsUnit (A.toBlock (b · < a) (b · < a))) :
    ∃ L' U', IsBlockLU b A L' U' ∧ L' ≠ L := by
  obtain ⟨i₀, rfl⟩ := ha
  set p : n → Prop := fun i => b i < b i₀ with hp
  have hpd : ∀ i j, p i → b j ≤ b i → p j := fun i j hi hji => hji.trans_lt hi
  have h' := h.toBlock hpd
  -- the upper leading block is singular
  have hU' : ¬ IsUnit (U.toBlock p p) := fun hU' =>
    hA (by rw [← h'.mul_eq]; exact h'.isBlockUnitLowerTriangular.isUnit.mul hU')
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not, ← exists_vecMul_eq_zero_iff] at hU'
  obtain ⟨y, hy, hyU⟩ := hU'
  -- the perturbation
  set E : Matrix n n K := of fun i j => if i = i₀ then (if hj : p j then y ⟨j, hj⟩ else 0) else 0
    with hE
  have hEE : E * E = 0 := by
    ext i j
    rw [mul_apply, zero_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = i₀
    · subst hr
      have : ¬ p r := lt_irrefl _
      simp [hE, this]
    · simp [hE, hr]
  have hEU : ∀ j, p j → (E * U) i₀ j = 0 := fun j hj => by
    have := congrFun hyU ⟨j, hj⟩
    rw [vecMul, dotProduct, Pi.zero_apply] at this
    rw [mul_apply, ← Fintype.sum_subtype_add_sum_subtype p,
      Finset.sum_eq_zero (s := (univ : Finset {x // ¬p x})) (fun r _ => by simp [hE, r.2]),
      add_zero, ← this]
    exact Finset.sum_congr rfl fun r _ => by simp [hE, r.2]
  have hEU' : ∀ i j, i ≠ i₀ → (E * U) i j = 0 := fun i j hi => by
    rw [mul_apply]
    exact Finset.sum_eq_zero fun r _ => by simp [hE, hi]
  refine ⟨L * (1 + E), (1 - E) * U, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine h.isBlockUnitLowerTriangular.mul ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · have hij' : b i < b j := OrderDual.toDual_lt_toDual.1 hij
      rw [add_apply, one_apply_ne (ne_of_apply_ne b hij'.ne), zero_add, hE, of_apply]
      split_ifs with hi hj
      · rw [hi] at hij'
        exact absurd ((hj : b j < b i₀).trans hij') (lt_irrefl _)
      · rfl
      · rfl
    · rw [add_apply, hE, of_apply]
      split_ifs with hi hj
      · rw [hi] at hij
        have hj' : b j < b i₀ := hj
        rw [hij] at hj'
        exact absurd hj' (lt_irrefl _)
      · rw [add_zero]
      · rw [add_zero]
  · intro i j hij
    rw [sub_mul, Matrix.one_mul, sub_apply, h.blockTriangular hij, zero_sub, neg_eq_zero]
    by_cases hi : i = i₀
    · subst hi
      exact hEU j hij
    · exact hEU' i j hi
  · have : (1 + E) * (1 - E) = 1 := by
      rw [add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hEE, sub_zero, sub_add_cancel]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + E), this, Matrix.one_mul, h.mul_eq]
  · intro hLE
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    have := congrFun (congrFun hLE i₀) j.1
    rw [Matrix.mul_add, Matrix.mul_one, add_apply, add_eq_left, mul_apply,
      Finset.sum_eq_single i₀ (fun r _ hr => by simp [hE, hr]) (fun h => absurd (mem_univ _) h),
      h.isBlockUnitLowerTriangular.apply_eq_one_of_eq i₀ i₀ rfl, one_apply_eq, one_mul] at this
    exact hj (by simpa [hE, j.2] using this)

/-- **[quarteroni2000numerical] Theorem 3.7** (and Theorem 3.4 as the case `b = id`): a matrix has
a unique block LU factorization along the labelling `b` if and only if the leading principal
block submatrices `A(b < a)`, one for each label `a` attained by `b`, are nonsingular. The book
says "the `m - 1` dominant principal block minors": the block for the smallest label is empty
and the block for the largest is `A` without its last block row and column, so the range
condition is exactly the book's `m - 1` blocks. -/
theorem existsUnique_isBlockLU_iff (b : n → α) (A : Matrix n n K) :
    (∃! LU : Matrix n n K × Matrix n n K, IsBlockLU b A LU.1 LU.2) ↔
      ∀ a ∈ Set.range b, IsUnit (A.toBlock (b · < a) (b · < a)) := by
  constructor
  · rintro ⟨⟨L, U⟩, h, huniq⟩ a ha
    by_contra hA
    obtain ⟨L', U', h', hne⟩ := h.exists_ne_of_not_isUnit ha hA
    exact hne (congrArg Prod.fst (huniq (L', U') h'))
  · intro hA
    obtain ⟨L, U, h⟩ := exists_isBlockLU_of_forall_isUnit hA
    refine ⟨(L, U), h, fun LU' h' => ?_⟩
    obtain ⟨hL, hU⟩ := IsBlockLU.unique hA h' h
    exact Prod.ext hL hU

end BlockExistence

/-! ### The LU factorization: existence and uniqueness -/

section Theorem34

variable [LinearOrder n] [Fintype n] {K : Type*} [Field K]

/-- The strict leading block hypothesis along `b = id` is the nonsingularity of the strict
leading principal submatrices. -/
theorem forall_isUnit_toBlock_id_iff {A : Matrix n n K} :
    (∀ a ∈ Set.range (id : n → n), IsUnit (A.toBlock (id · < a) (id · < a))) ↔
      ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) := by
  simp only [Set.range_id, Set.mem_univ, true_implies, id]
  exact Iff.rfl

/-- **Existence of the LU factorization** ([quarteroni2000numerical] Theorem 3.4, the existence
half; [higham2002accuracy] Theorem 9.1): if the strict leading principal submatrices are
nonsingular, `A` has a unit lower LU factorization. -/
theorem exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix {A : Matrix n n K}
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) : ∃ L U, IsLU A L U := by
  obtain ⟨L, U, h⟩ :=
    exists_isBlockLU_of_forall_isUnit (b := id) (forall_isUnit_toBlock_id_iff.2 hA)
  exact ⟨L, U, isBlockLU_id_iff.1 h⟩

/-- **Uniqueness of the LU factorization** ([quarteroni2000numerical] Theorem 3.4, the uniqueness
half): two unit lower LU factorizations of a matrix with nonsingular strict leading principal
submatrices coincide. -/
theorem IsLU.unique {A L₁ U₁ L₂ U₂ : Matrix n n K} (h₁ : IsLU A L₁ U₁) (h₂ : IsLU A L₂ U₂)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) : L₁ = L₂ ∧ U₁ = U₂ :=
  IsBlockLU.unique (b := id) (forall_isUnit_toBlock_id_iff.2 hA) (isBlockLU_id_iff.2 h₁)
    (isBlockLU_id_iff.2 h₂)

/-- **[quarteroni2000numerical] Theorem 3.4** ([higham2002accuracy] Theorem 9.1): the unit lower
LU factorization of `A` exists and is unique if and only if the strict leading principal
submatrices of `A` (the book's `A_i`, `i = 1, …, n - 1`) are nonsingular. -/
theorem existsUnique_isLU_iff (A : Matrix n n K) :
    (∃! LU : Matrix n n K × Matrix n n K, IsLU A LU.1 LU.2) ↔
      ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) := by
  rw [← forall_isUnit_toBlock_id_iff, ← existsUnique_isBlockLU_iff]
  exact existsUnique_congr fun LU => isBlockLU_id_iff.symm

end Theorem34

/-! ### The rectangular LU factorization -/

section RectLU

variable {M N P : ℕ}

/-- The two halves of `Fin (s + m)` under `finSumFinEquiv`: an index below `s` comes from the left
summand, an index from `s` on from the right one, shifted by `s`. -/
theorem _root_.finSumFinEquiv_symm_cases {s m : ℕ} (i : Fin (s + m)) :
    (∃ hi : (i : ℕ) < s, finSumFinEquiv.symm i = Sum.inl ⟨i, hi⟩) ∨
      ∃ hi : s ≤ (i : ℕ), finSumFinEquiv.symm i = Sum.inr ⟨i - s, by omega⟩ := by
  by_cases hi : (i : ℕ) < s
  · refine Or.inl ⟨hi, finSumFinEquiv.symm_apply_eq.2 ?_⟩
    rw [finSumFinEquiv_apply_left]
    exact Fin.ext rfl
  · refine Or.inr ⟨not_lt.1 hi, finSumFinEquiv.symm_apply_eq.2 ?_⟩
    rw [finSumFinEquiv_apply_right]
    exact Fin.ext (by simp; omega)

/-- **The rectangular LU factorization** ([golub2013matrix] §3.2.10): `A = L U` with
`A : Matrix (Fin M) (Fin N) R`, `L : Matrix (Fin M) (Fin P) R` unit lower trapezoidal and
`U : Matrix (Fin P) (Fin N) R` upper trapezoidal. The index comparisons are on the `ℕ` values,
since the index types differ (the rectangular band vocabulary of
`Numlib/LinearAlgebra/Matrix/Band`); on a square `Fin N` it is `Matrix.IsLU`
(`Matrix.isRectLU_iff_isLU`). -/
structure IsRectLU [Semiring R] (A : Matrix (Fin M) (Fin N) R) (L : Matrix (Fin M) (Fin P) R)
    (U : Matrix (Fin P) (Fin N) R) : Prop where
  /-- The lower factor is lower trapezoidal: `L i j = 0` for `i < j`. -/
  lower : L.HasUpperBandwidthRect 0
  /-- The lower factor has ones on its diagonal. -/
  lower_apply_self : ∀ (i : Fin M) (j : Fin P), (i : ℕ) = j → L i j = 1
  /-- The upper factor is upper trapezoidal: `U i j = 0` for `j < i`. -/
  upper : U.HasLowerBandwidthRect 0
  /-- The factors multiply to `A`. -/
  mul_eq : L * U = A

/-- On a square `Fin N` the rectangular LU factorization is the LU factorization. -/
theorem isRectLU_iff_isLU [Semiring R] {A L U : Matrix (Fin N) (Fin N) R} :
    IsRectLU A L U ↔ IsLU A L U := by
  constructor
  · intro h
    refine ⟨⟨fun i j hij => h.lower i j ?_, fun i => h.lower_apply_self i i rfl⟩,
      fun i j hij => h.upper i j ?_, h.mul_eq⟩
    · rw [add_zero]; exact OrderDual.toDual_lt_toDual.1 hij
    · rw [add_zero]; exact hij
  · intro h
    refine ⟨fun i j hij => h.isUnitLowerTriangular.isLowerTriangular ?_,
      fun i j hij => ?_, fun i j hij => h.isUpperTriangular ?_, h.mul_eq⟩
    · rw [add_zero] at hij; exact OrderDual.toDual_lt_toDual.2 hij
    · rw [Fin.ext hij, h.isUnitLowerTriangular.diag_eq_one]
    · rw [add_zero] at hij; exact hij

/-- The bordered square matrix of the rectangular existence proof: `A` in the leading `M × N`
corner of a `max M N` square, zero elsewhere. -/
private def rectBorder [Zero R] (A : Matrix (Fin M) (Fin N) R) :
    Matrix (Fin (max M N)) (Fin (max M N)) R :=
  fun i j => if h : (i : ℕ) < M ∧ (j : ℕ) < N then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

variable {K : Type*} [Field K]

/-- **Existence of the rectangular LU factorization** ([golub2013matrix] §3.2.10, "guaranteed to
exist if `A(1:k, 1:k)` is nonsingular for `k = 1:min{m, n}`"): if every leading block of `A` of
order at most `min M N` is nonsingular, `A` has a rectangular LU factorization with
`P = min M N`. Proof: the matrix bordered by zeros to a `max M N` square has a block LU
factorization along the labelling `i ↦ min i (min M N)` (singletons, then one trailing block),
whose strict leading blocks are the leading blocks of `A`; the leading `M × P` part of the lower
factor and `P × N` part of the upper factor are the rectangular factors. -/
theorem exists_isRectLU_of_forall_isUnit {A : Matrix (Fin M) (Fin N) K}
    (hA : ∀ k (hk : k + 1 ≤ min M N),
      (A.submatrix (Fin.castLE (hk.trans (min_le_left _ _)))
        (Fin.castLE (hk.trans (min_le_right _ _)))).det ≠ 0) :
    ∃ L U, IsRectLU (P := min M N) A L U := by
  set p := min M N with hp
  let b : Fin (max M N) → ℕ := fun i => min (i : ℕ) p
  have hblock : ∀ a ∈ Set.range b,
      IsUnit ((rectBorder A).toBlock (b · < a) (b · < a)) := by
    rintro _ ⟨i₀, rfl⟩
    set k := b i₀
    have hk : k ≤ p := min_le_right _ _
    clear_value k
    have hlt : ∀ i : Fin (max M N), b i < k ↔ (i : ℕ) < k := fun i => by
      simp only [b]; omega
    let e : Fin k ≃ {i : Fin (max M N) // b i < k} :=
      { toFun := fun a => ⟨⟨a, by omega⟩, (hlt _).2 a.2⟩
        invFun := fun i => ⟨i.1, (hlt _).1 i.2⟩
        left_inv := fun a => rfl
        right_inv := fun i => rfl }
    rw [isUnit_iff_isUnit_det, ← det_submatrix_equiv_self e, isUnit_iff_ne_zero]
    cases k with
    | zero => rw [det_isEmpty]; exact one_ne_zero
    | succ k' =>
    convert hA k' hk using 2
    ext x y
    simp only [submatrix_apply, toBlock_apply, rectBorder, e, Equiv.coe_fn_mk]
    rw [dite_eq_left_of_eq_true (eq_true ⟨by omega, by omega⟩)]
    rfl
  obtain ⟨L, U, h⟩ := exists_isBlockLU_of_forall_isUnit hblock
  refine ⟨of fun i j => L ⟨i, by omega⟩ ⟨j, by omega⟩, of fun i j => U ⟨i, by omega⟩ ⟨j, by omega⟩,
    ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hij => ?_, ?_⟩⟩
  · exact h.isBlockUnitLowerTriangular.blockTriangular (by
      simp only [Function.comp_apply, OrderDual.toDual_lt_toDual, b]; omega)
  · change L ⟨i, _⟩ ⟨j, _⟩ = 1
    rw [show (⟨j, _⟩ : Fin (max M N)) = ⟨i, by omega⟩ from Fin.ext hij.symm]
    exact (h.isBlockUnitLowerTriangular.apply_eq_one_of_eq _ _ rfl).trans (one_apply_eq _)
  · exact h.blockTriangular (by simp only [b]; omega)
  · ext i j
    have := congrFun (congrFun h.mul_eq ⟨i, by omega⟩) ⟨j, by omega⟩
    rw [rectBorder, dite_eq_left_of_eq_true (eq_true ⟨i.2, j.2⟩), mul_apply] at this
    simp only [mul_apply, of_apply]
    rw [← this]
    refine Fintype.sum_of_injective (fun r : Fin p => (⟨r, by omega⟩ : Fin (max M N)))
      (fun r s hrs => Fin.ext (Fin.mk.inj_iff.1 hrs)) _ _ (fun r hr => ?_) (fun r => rfl)
    have hrp : p ≤ (r : ℕ) := by
      by_contra hcon
      exact hr ⟨⟨r, by omega⟩, rfl⟩
    by_cases hi : (i : ℕ) < p
    · rw [h.isBlockUnitLowerTriangular.blockTriangular (by
        simp only [Function.comp_apply, OrderDual.toDual_lt_toDual, b]; omega), zero_mul]
    · rw [h.blockTriangular (by simp only [b]; omega), mul_zero]

end RectLU

/-! ### The `L D Mᵀ` and `L D Lᵀ` factorizations -/

section LDM

variable [LinearOrder n] [Fintype n]

/-- `IsLDM A L D M`: `L` and `M` unit lower triangular, `D` diagonal and `L * D * Mᵀ = A`, the
`L D Mᵀ` factorization of [quarteroni2000numerical] §3.4.1; `M = L` is the `L D Lᵀ`
factorization of §3.4.2. -/
structure IsLDM [Semiring R] (A L D M : Matrix n n R) : Prop where
  /-- The left factor is unit lower triangular. -/
  isUnitLowerTriangular_left : L.IsUnitLowerTriangular
  /-- The middle factor is diagonal. -/
  isDiag : D.IsDiag
  /-- The right factor (before transposition) is unit lower triangular. -/
  isUnitLowerTriangular_right : M.IsUnitLowerTriangular
  /-- The factors multiply to `A`. -/
  mul_eq : L * D * Mᵀ = A

omit [Fintype n] in
/-- The transpose of a lower triangular matrix is upper triangular. -/
theorem IsLowerTriangular.transpose_isUpperTriangular [Zero R] {M : Matrix n n R}
    (hM : M.IsLowerTriangular) : Mᵀ.IsUpperTriangular := fun _ _ hij =>
  hM (OrderDual.toDual_lt_toDual.2 hij)

omit [Fintype n] in
/-- A diagonal matrix is upper triangular. -/
theorem IsDiag.isUpperTriangular [Zero R] {D : Matrix n n R} (hD : D.IsDiag) :
    D.IsUpperTriangular := fun _ _ hij => hD (ne_of_gt hij)

/-- An `L D Mᵀ` factorization is the LU factorization with `U = D Mᵀ`. -/
theorem IsLDM.isLU [Semiring R] {A L D M : Matrix n n R} (h : IsLDM A L D M) :
    IsLU A L (D * Mᵀ) :=
  ⟨h.isUnitLowerTriangular_left,
    h.isDiag.isUpperTriangular.mul
      h.isUnitLowerTriangular_right.isLowerTriangular.transpose_isUpperTriangular,
    by rw [← Matrix.mul_assoc, h.mul_eq]⟩

variable {K : Type*} [Field K]

/-- **[quarteroni2000numerical] Theorem 3.5**, at the generality of [golub2013matrix]
Theorem 4.1.3: if every *strict* leading principal submatrix of `A` is nonsingular, then `A` has a
unique `L D Mᵀ` factorization (`A` itself may be singular, and then the last pivot vanishes). From
the LU factorization `A = L U` take `D = diag U` and `Mᵀ = D⁻¹ U` off the diagonal: every pivot but
the last is nonzero (`Matrix.IsLU.diag_upper_ne_zero_of_lt`), and a vanishing last pivot comes
with a zero last row. Uniqueness follows from the uniqueness of the LU factorization, since
`L (D Mᵀ)` is one. The book says "all the principal minors"; its proof uses the leading ones. -/
theorem existsUnique_isLDM {A : Matrix n n K}
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    ∃! LDM : Matrix n n K × Matrix n n K × Matrix n n K, IsLDM A LDM.1 LDM.2.1 LDM.2.2 := by
  obtain ⟨L, U, hLU⟩ := exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix hA
  have hrow : ∀ i j, U i i = 0 → U i j = 0 := fun i j hi => by
    rcases lt_trichotomy j i with hji | rfl | hij
    · exact hLU.isUpperTriangular hji
    · exact hi
    · exact absurd hi (hLU.diag_upper_ne_zero_of_lt (hA j) hij)
  set Mt : Matrix n n K := of fun i j => if i = j then 1 else (U i i)⁻¹ * U i j with hMt
  have hM : Mtᵀ.IsUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i => by simp [hMt]⟩
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [transpose_apply, hMt, of_apply, ite_eq_right hij'.ne', hLU.isUpperTriangular hij',
      mul_zero]
  have hDM : diagonal (fun i => U i i) * Mt = U := by
    ext i j
    rw [diagonal_mul, hMt, of_apply]
    split_ifs with hij
    · rw [hij, mul_one]
    · rcases eq_or_ne (U i i) 0 with hi | hi
      · rw [hi, zero_mul, hrow i j hi]
      · rw [← mul_assoc, mul_inv_cancel₀ hi, one_mul]
  refine ⟨(L, diagonal fun i => U i i, Mtᵀ),
    ⟨hLU.isUnitLowerTriangular, isDiag_diagonal _, hM, ?_⟩, ?_⟩
  · rw [transpose_transpose, Matrix.mul_assoc, hDM, hLU.mul_eq]
  · rintro ⟨L', D', M'⟩ h'
    dsimp only at h'
    obtain ⟨hL, hU'⟩ := h'.isLU.unique hLU hA
    have hD'M' : ∀ i j, (D' * M'ᵀ) i j = D' i i * M' j i := fun i j => by
      conv_lhs => rw [← h'.isDiag.diagonal_diag]
      rw [diagonal_mul, transpose_apply]
      rfl
    have hD : ∀ i, D' i i = U i i := fun i => by
      have := congrFun (congrFun hU' i) i
      rwa [hD'M' i i, h'.isUnitLowerTriangular_right.diag_eq_one, mul_one] at this
    refine Prod.ext hL (Prod.ext ?_ ?_)
    · ext i j
      rcases eq_or_ne i j with rfl | hij
      · simp [hD]
      · simp [h'.isDiag hij, diagonal_apply_ne _ hij]
    · ext i j
      change M' i j = Mtᵀ i j
      rw [transpose_apply, hMt, of_apply]
      rcases lt_trichotomy j i with hji | rfl | hij
      · have := congrFun (congrFun hU' j) i
        rw [hD'M' j i, hD j] at this
        rw [ite_eq_right hji.ne, ← this, ← mul_assoc,
          inv_mul_cancel₀ (hLU.diag_upper_ne_zero_of_lt (hA i) hji), one_mul]
      · rw [ite_eq_left rfl, h'.isUnitLowerTriangular_right.diag_eq_one]
      · rw [ite_eq_right hij.ne', hLU.isUpperTriangular hij, mul_zero,
          h'.isUnitLowerTriangular_right.isLowerTriangular (OrderDual.toDual_lt_toDual.2 hij)]

/-- The `L D Lᵀ` factorization ([quarteroni2000numerical] §3.4.2): for a symmetric matrix with
nonsingular strict leading principal submatrices, the two unit triangular factors of the `L D Mᵀ`
factorization coincide, since transposing `A = L D Mᵀ` gives the second factorization
`A = M D Lᵀ`. -/
theorem IsLDM.eq_of_isSymm {A L D M : Matrix n n K} (h : IsLDM A L D M) (hs : A.IsSymm)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) : M = L := by
  have h' : IsLDM A M D L := ⟨h.isUnitLowerTriangular_right, h.isDiag,
    h.isUnitLowerTriangular_left, by
      rw [← hs.eq, ← h.mul_eq, transpose_mul, transpose_mul, transpose_transpose,
        h.isDiag.isSymm.eq, Matrix.mul_assoc]⟩
  obtain ⟨⟨L₀, D₀, M₀⟩, -, huniq⟩ := existsUnique_isLDM hA
  have h₁ := huniq (L, D, M) h
  have h₂ := huniq (M, D, L) h'
  exact (congrArg Prod.fst h₂).trans (congrArg Prod.fst h₁).symm

/-- In the `L D Lᵀ` factorization of a positive definite matrix the diagonal entries of `D` are
positive ([quarteroni2000numerical] §3.4.2): `D = L⁻¹ A L⁻ᵀ` is congruent to `A`, hence positive
definite, and the diagonal of a positive definite matrix is positive. Stated for a field with a
trivial star, where `ᵀ` is `ᴴ`. -/
theorem IsLDM.diag_pos_of_posDef {K : Type*} [Field K] [PartialOrder K] [StarRing K]
    [TrivialStar K] {A L D : Matrix n n K} (h : IsLDM A L D L) (hA : A.PosDef) (i : n) :
    0 < D i i := by
  have hLd : IsUnit L.det := (isUnit_iff_isUnit_det L).1 h.isUnitLowerTriangular_left.isUnit
  have hD : D = L⁻¹ * A * (L⁻¹)ᵀ := by
    rw [← h.mul_eq, transpose_nonsing_inv, Matrix.mul_assoc L, nonsing_inv_mul_cancel_left _ _ hLd,
      mul_nonsing_inv_cancel_right _ _ (by rwa [det_transpose])]
  have hB : IsUnit (L⁻¹)ᵀ := (isUnit_transpose _).2 (isUnit_nonsing_inv_iff.2
    ((isUnit_iff_isUnit_det L).2 hLd))
  have hpos := hA.conjTranspose_mul_mul_same (B := (L⁻¹)ᵀ) (mulVec_injective_iff_isUnit.2 hB)
  rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, ← hD] at hpos
  exact hpos.diag_pos

end LDM

/-! ### Existence under diagonal dominance -/

section DiagDominant

variable [LinearOrder n] [Fintype n] {K : Type*} [Field K]

/-- Splitting a sum over `n` into the term at `p` and the sum over the other indices. -/
theorem sum_eq_add_sum_subtype_ne {M : Type*} [AddCommMonoid M] (p : n) (f : n → M) :
    ∑ j, f j = f p + ∑ j : {j // j ≠ p}, f j := by
  rw [Fintype.sum_eq_add_sum_compl p, Finset.sum_subtype (p := (· ≠ p)) {p}ᶜ (fun x => by simp) f]

/-- The unit lower factor of `A` bordered from the lower factor `L'` of the Schur complement of
`A` at the pivot `p`: the identity row at `p`, the multipliers `a_ip / a_pp` in column `p`, and
`L'` elsewhere. -/
noncomputable def luLowerOfSchur (A : Matrix n n K) (p : n)
    (L' : Matrix {i // i ≠ p} {i // i ≠ p} K) : Matrix n n K :=
  of fun i j =>
    if hi : i = p then (if j = p then 1 else 0)
    else if hj : j = p then A i p / A p p else L' ⟨i, hi⟩ ⟨j, hj⟩

/-- The upper factor of `A` bordered from the upper factor `U'` of the Schur complement of `A` at
the pivot `p`: the pivot row of `A` at `p`, zeros below it in column `p`, and `U'` elsewhere. -/
noncomputable def luUpperOfSchur (A : Matrix n n K) (p : n)
    (U' : Matrix {i // i ≠ p} {i // i ≠ p} K) : Matrix n n K :=
  of fun i j => if hi : i = p then A p j else if hj : j = p then 0 else U' ⟨i, hi⟩ ⟨j, hj⟩

/-- **One step of Gaussian elimination as a factorization step**: if `p` is the first index,
`a_pp ≠ 0` and the Schur complement of `A` at `p` has the LU factorization `L' U'`, then `A` has
the LU factorization `Matrix.luLowerOfSchur A p L' * Matrix.luUpperOfSchur A p U'`
([quarteroni2000numerical] §3.8.1, "if `A₁₁` were a scalar"). -/
theorem isLU_luLowerOfSchur_luUpperOfSchur {A : Matrix n n K} {p : n} (hp : ∀ i, p ≤ i)
    (hpp : A p p ≠ 0) {L' U' : Matrix {i // i ≠ p} {i // i ≠ p} K}
    (h : IsLU (A.schurComplementSingle p) L' U') :
    IsLU A (luLowerOfSchur A p L') (luUpperOfSchur A p U') where
  isUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
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
  isUpperTriangular := by
    intro i j hij
    simp only [luUpperOfSchur, of_apply]
    split_ifs with hi hj
    · exact absurd (hi ▸ hij) (not_lt.2 (hp j))
    · rfl
    · exact h.isUpperTriangular (Subtype.mk_lt_mk.2 hij)
  mul_eq := by
    have hLpp : luLowerOfSchur A p L' p p = 1 := by simp [luLowerOfSchur]
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
      simp [hLxp i hi, hUpj, hUxp, div_mul_cancel₀ _ hpp]
    have hS := congrFun (congrFun h.mul_eq ⟨i, hi⟩) ⟨j, hj⟩
    rw [mul_apply, schurComplementSingle_apply] at hS
    simp only [hLxp i hi, hUpj, hLxx i hi, hUxj _ j hj]
    rw [hS, div_eq_mul_inv]
    ring

/-- The existence half of [quarteroni2000numerical] Property 3.2 for rows, by induction on the
number of indices: the Schur complement at the first index of a nonsingular weakly row dominant
matrix is again nonsingular and weakly row dominant, so it factors, and the factorization extends
by `Matrix.isLU_luLowerOfSchur_luUpperOfSchur`. -/
theorem exists_isLU_of_isDiagDominant_of_card {𝕜 : Type*} [RCLike 𝕜] (N : ℕ) :
    ∀ {n : Type u} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜), Fintype.card n = N →
      IsUnit A → A.IsDiagDominant → ∃ L U, IsLU A L U := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n _ _ A hN hu hA
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, isUnitLowerTriangular_one, blockTriangular_one, Matrix.ext fun i => isEmptyElim i⟩
  set p := univ.min' (univ_nonempty : (univ : Finset n).Nonempty)
  have hp : ∀ i, p ≤ i := fun i => min'_le _ _ (mem_univ i)
  have hpp : A p p ≠ 0 := hA.diag_ne_zero_of_isUnit hu p
  have hcard : Fintype.card {i // i ≠ p} < N :=
    hN ▸ Fintype.card_subtype_lt (x := p) (not_not.2 rfl)
  -- `convert` reconciles the two `DecidableEq {i // i ≠ p}` instances behind `IsUnit`
  obtain ⟨L', U', h⟩ := ih _ hcard (A.schurComplementSingle p) rfl
    (by convert isUnit_schurComplementSingle hu hpp)
    (by convert hA.schurComplementSingle hpp)
  exact ⟨_, _, isLU_luLowerOfSchur_luUpperOfSchur hp hpp h⟩

/-- **[quarteroni2000numerical] Property 3.2** (rows), [higham2002accuracy] Theorem 9.9: a
nonsingular matrix that is weakly diagonally dominant by rows has an LU factorization.
Nonsingularity is not in the book's statement and is needed: `!![0, 0; 1, 1]` is weakly row
dominant and has no unit lower LU factorization (`u₁₁ = 0` forces `l₂₁ · 0 = 1`). -/
theorem exists_isLU_of_isDiagDominant {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜} (hu : IsUnit A)
    (hA : A.IsDiagDominant) : ∃ L U, IsLU A L U :=
  exists_isLU_of_isDiagDominant_of_card _ A rfl hu hA

/-- The existence half of [quarteroni2000numerical] Property 3.2 for columns, with the bound
`|l_ij| ≤ 1` carried through the induction: the multipliers `a_ip / a_pp` are bounded by `1` by
column dominance of the pivot column. -/
theorem exists_isLU_of_isColDiagDominant_of_card {𝕜 : Type*} [RCLike 𝕜] (N : ℕ) :
    ∀ {n : Type u} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜), Fintype.card n = N →
      IsUnit A → A.IsColDiagDominant → ∃ L U, IsLU A L U ∧ ∀ i j, ‖L i j‖ ≤ 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n _ _ A hN hu hA
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, ⟨isUnitLowerTriangular_one, blockTriangular_one,
      Matrix.ext fun i => isEmptyElim i⟩, fun i => isEmptyElim i⟩
  set p := univ.min' (univ_nonempty : (univ : Finset n).Nonempty)
  have hp : ∀ i, p ≤ i := fun i => min'_le _ _ (mem_univ i)
  have hpp : A p p ≠ 0 := hA.diag_ne_zero_of_isUnit hu p
  have hcard : Fintype.card {i // i ≠ p} < N :=
    hN ▸ Fintype.card_subtype_lt (x := p) (not_not.2 rfl)
  obtain ⟨L', U', h, hL'⟩ := ih _ hcard (A.schurComplementSingle p) rfl
    (by convert isUnit_schurComplementSingle hu hpp)
    (by convert hA.schurComplementSingle hpp)
  refine ⟨_, _, isLU_luLowerOfSchur_luUpperOfSchur hp hpp h, fun i j => ?_⟩
  simp only [luLowerOfSchur, of_apply]
  split_ifs with hi hj hj
  · simp
  · simp
  · rw [norm_div, div_le_one (norm_pos_iff.2 hpp)]
    refine le_trans ?_ (hA p)
    exact Finset.single_le_sum (f := fun r => ‖A r p‖) (fun r _ => norm_nonneg _)
      (mem_erase.2 ⟨hi, mem_univ i⟩)
  · exact hL' _ _

/-- **[quarteroni2000numerical] Property 3.2** (columns), [higham2002accuracy] Theorem 9.9: a
nonsingular matrix that is weakly diagonally dominant by columns has an LU factorization whose
lower factor has all entries of modulus at most `1`. -/
theorem exists_isLU_of_isColDiagDominant {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}
    (hu : IsUnit A) (hA : A.IsColDiagDominant) : ∃ L U, IsLU A L U ∧ ∀ i j, ‖L i j‖ ≤ 1 :=
  exists_isLU_of_isColDiagDominant_of_card _ A rfl hu hA

end DiagDominant

/-! ### Bands and the envelope -/

section Band

variable [LinearOrder n] [Fintype n]

/-- **[quarteroni2000numerical] Property 3.4**, the upper half: if `A = L U` has upper bandwidth
`q`, so does `U`. No hypothesis beyond the factorization is needed: `u_ij = a_ij - ∑_{r<i} l_ir
u_rj` vanishes by induction on `i` whenever `a_ij` does. -/
theorem IsLU.hasUpperBandwidth [Ring R] {A L U : Matrix n n R} (h : IsLU A L U) {q : ℕ}
    (hA : A.HasUpperBandwidth q) : U.HasUpperBandwidth q := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
  intro j hij
  have hlt : i < j := (card_filter_le_lt_pos_iff j i).1 ((Nat.zero_le q).trans_lt hij)
  rw [h.upper_apply_eq hlt.le, hA i j hij, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hr' := (mem_filter.1 hr).2
  rw [ih r hr' j (hij.trans_le (card_filter_le_lt_mono hr'.le le_rfl)), mul_zero]

variable {K : Type*} [Field K]

/-- **[quarteroni2000numerical] Property 3.4**, the lower half: if `A = L U` has lower bandwidth
`p` and the strict leading principal submatrices of `A` are nonsingular, then `L` has lower
bandwidth `p`. Without the nonsingularity the claim fails: Example 3.3's `D = !![0, 1; 0, 2]` is
upper triangular and factors as `L_β U_β` with `L_β = !![1, 0; β, 1]` for every `β`. -/
theorem IsLU.hasLowerBandwidth {A L U : Matrix n n K} (h : IsLU A L U)
    (hA' : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) {p : ℕ}
    (hA : A.HasLowerBandwidth p) : L.HasLowerBandwidth p := by
  intro i j
  induction j using WellFoundedLT.induction generalizing i with
  | ind j ih =>
  intro hij
  have hlt : j < i := (card_filter_le_lt_pos_iff i j).1 ((Nat.zero_le p).trans_lt hij)
  have hU := h.diag_upper_ne_zero_of_lt (hA' i) hlt
  have key := h.lower_apply_mul_diag_eq hlt
  rw [hA i j hij, zero_sub, Finset.sum_eq_zero fun r hr => ?_, neg_zero] at key
  · exact (mul_eq_zero.1 key).resolve_right hU
  · have hr' := (mem_filter.1 hr).2
    rw [ih r hr' i (hij.trans_le (card_filter_le_lt_mono hr'.le le_rfl)), zero_mul]

/-- The (lower) envelope of a matrix, [quarteroni2000numerical] (3.59): the strictly lower
positions `(i, j)` from the first nonzero of row `i` to the diagonal. On `Fin N` this is
`{(i, j) | 0 < i - j ≤ m_i(A)}` with `m_i(A) = i - min {j < i | a_ij ≠ 0}`, and it is empty for a
row whose strict lower part vanishes. -/
def envelope [Zero R] (A : Matrix n n R) : Set (n × n) :=
  {ij | ij.2 < ij.1 ∧ ∃ j₀ ≤ ij.2, A ij.1 j₀ ≠ 0}

/-- Below the diagonal, `L` vanishes wherever the row of `A` vanishes up to that column: by
induction on the column, `l_ij u_jj = a_ij - ∑_{r<j} l_ir u_rj = 0`, and `u_jj ≠ 0`. -/
theorem IsLU.lower_apply_eq_zero_of_forall_le {A L U : Matrix n n K} (h : IsLU A L U)
    (hA' : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) {i j : n} (hij : j < i)
    (hz : ∀ r ≤ j, A i r = 0) : L i j = 0 := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
  have hU := h.diag_upper_ne_zero_of_lt (hA' i) hij
  have key := h.lower_apply_mul_diag_eq hij
  rw [hz j le_rfl, zero_sub, Finset.sum_eq_zero fun r hr => ?_, neg_zero] at key
  · exact (mul_eq_zero.1 key).resolve_right hU
  · have hr' := (mem_filter.1 hr).2
    rw [ih r hr' (hr'.trans hij) fun r' hr'' => hz r' (hr''.trans hr'.le), zero_mul]

/-- **[quarteroni2000numerical] (3.60)**, no fill-in outside the envelope and none missing on its
boundary: if `A = L U` with nonsingular strict leading principal submatrices, then `L` and `A`
have the same envelope. Below the first nonzero `a_{i j₀}` of a row every `l_ir` vanishes
(`Matrix.IsLU.lower_apply_eq_zero_of_forall_le`), and at `j₀` itself `l_{i j₀} u_{j₀ j₀} =
a_{i j₀} ≠ 0`. For a symmetric positive definite `A` with Cholesky factor `H`, `Hᵀ = L D^{1/2}`
has the pattern of `L`, which is the book's `E(A) = E(H + Hᵀ)`. -/
theorem IsLU.envelope_eq {A L U : Matrix n n K} (h : IsLU A L U)
    (hA' : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) : L.envelope = A.envelope := by
  ext ⟨i, j⟩
  simp only [envelope, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hij, j₀, hj₀, hL⟩
    refine ⟨hij, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hL (h.lower_apply_eq_zero_of_forall_le hA' (hj₀.trans_lt hij)
      fun r hr => hcon r (hr.trans hj₀))
  · rintro ⟨hij, j₀, hj₀, hA⟩
    refine ⟨hij, ?_⟩
    classical
    set s := univ.filter fun r => r ≤ j ∧ A i r ≠ 0 with hs_def
    have hs : s.Nonempty := ⟨j₀, mem_filter.2 ⟨mem_univ _, hj₀, hA⟩⟩
    obtain ⟨hj₁j, hAj₁⟩ := (mem_filter.1 (min'_mem s hs)).2
    refine ⟨s.min' hs, hj₁j, fun hL => ?_⟩
    have hlt : s.min' hs < i := hj₁j.trans_lt hij
    have key := h.lower_apply_mul_diag_eq hlt
    rw [hL, zero_mul, Finset.sum_eq_zero fun r hr => ?_, sub_zero] at key
    · exact hAj₁ key.symm
    · have hr' := (mem_filter.1 hr).2
      rw [h.lower_apply_eq_zero_of_forall_le hA' (hr'.trans hlt) fun r' hr'' => ?_, zero_mul]
      by_contra hne
      exact absurd (min'_le s r' (mem_filter.2 ⟨mem_univ _, (hr''.trans hr'.le).trans hj₁j, hne⟩))
        (not_le.2 (hr''.trans_lt hr'))

end Band

/-! ### The two-block case: the Schur complement -/

section TwoBlocks

variable {m o : Type*} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
variable {K : Type*} [Field K]

/-- The two-block case of the block LU factorization is the Schur complement factorization
`Matrix.fromBlocks_eq_mul_fromBlocks_schurComplement`: for `A = [[B, E], [F, C]]` with `B`
nonsingular, `A = [[1, 0], [F B⁻¹, 1]] · [[B, E], [0, S]]` with `S = C - F B⁻¹ E`, along the
labelling `0` on the first block and `1` on the second. [quarteroni2000numerical] §3.8.1's
display with `A₁₁ = L₁₁ D₁ R₁₁` is this identity with `B` refactored. -/
theorem isBlockLU_fromBlocks_schurComplement {B : Matrix m m K} {E : Matrix m o K}
    {F : Matrix o m K} {C : Matrix o o K} (hB : IsUnit B) :
    IsBlockLU (Sum.elim (fun _ => (0 : ℕ)) fun _ => 1) (fromBlocks B E F C)
      (fromBlocks 1 0 (F * B⁻¹) 1) (fromBlocks B E 0 (fromBlocks B E F C).schurComplement) where
  isBlockUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · have hij' := OrderDual.toDual_lt_toDual.1 hij
      rcases i with i | i <;> rcases j with j | j <;> first | rfl | (exfalso; simp at hij')
    · rcases i with i | i <;> rcases j with j | j <;> simp [one_apply] at hij ⊢
  blockTriangular := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j <;> first | rfl | (exfalso; simp at hij)
  mul_eq := (fromBlocks_eq_mul_fromBlocks_schurComplement hB).symm

end TwoBlocks

/-! ### Tridiagonal matrices: the Thomas algorithm -/

section Thomas

variable {K : Type*} [Field K]

/-- The tridiagonal matrix of [quarteroni2000numerical] §3.7.1 from three sequences: `a i` on the
diagonal, `b i` on the subdiagonal (at `(i, i - 1)`) and `c i` on the superdiagonal (at
`(i, i + 1)`), on `Fin N`; `b 0` and `c (N - 1)` are unused. It is `Matrix.tridiagonalOf` of the
shifted sequences (`Matrix.tridiagonalOfNat_eq_tridiagonalOf`). -/
def tridiagonalOfNat [Zero R] (a b c : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  of fun i j =>
    if (i : ℕ) = j then a i else if (j : ℕ) + 1 = i then b i else if (i : ℕ) + 1 = j then c i
    else 0

/-- `Matrix.tridiagonalOfNat` is `Matrix.tridiagonalOf` of the shifted sequences. -/
theorem tridiagonalOfNat_eq_tridiagonalOf [Zero R] (a b c : ℕ → R) (N : ℕ) :
    tridiagonalOfNat a b c (N + 1) =
      tridiagonalOf (fun i : Fin N => b (i + 1)) (fun i => a i) fun i : Fin N => c i := by
  ext i j
  simp only [tridiagonalOfNat, tridiagonalOf, of_apply]
  split_ifs <;> first | rfl | omega | congr 1

/-- The pivots `α_i` of the Thomas algorithm, [quarteroni2000numerical] (3.53):
`α_0 = a_0`, `α_{i+1} = a_{i+1} - β_{i+1} c_i` with `β_{i+1} = b_{i+1} / α_i`. -/
noncomputable def thomasAlpha (a b c : ℕ → K) : ℕ → K
  | 0 => a 0
  | i + 1 => a (i + 1) - b (i + 1) / thomasAlpha a b c i * c i

/-- The multipliers `β_i` of the Thomas algorithm, [quarteroni2000numerical] (3.53):
`β_{i+1} = b_{i+1} / α_i`, and `β_0 = 0` by convention. -/
noncomputable def thomasBeta (a b c : ℕ → K) : ℕ → K
  | 0 => 0
  | i + 1 => b (i + 1) / thomasAlpha a b c i

variable (a b c : ℕ → K)

/-- The first Thomas pivot is `a₀`. -/
@[simp]
theorem thomasAlpha_zero : thomasAlpha a b c 0 = a 0 := rfl

/-- The Thomas recurrence for the pivots, `α_{i+1} = a_{i+1} - β_{i+1} c_i`. -/
theorem thomasAlpha_succ (i : ℕ) :
    thomasAlpha a b c (i + 1) = a (i + 1) - thomasBeta a b c (i + 1) * c i := rfl

/-- The multiplier `β₀` is `0` by convention. -/
@[simp]
theorem thomasBeta_zero : thomasBeta a b c 0 = 0 := rfl

/-- The Thomas recurrence for the multipliers, `β_{i+1} = b_{i+1} / α_i`. -/
theorem thomasBeta_succ (i : ℕ) : thomasBeta a b c (i + 1) = b (i + 1) / thomasAlpha a b c i := rfl

/-- The unit lower bidiagonal factor of the Thomas algorithm, with the multipliers `β_i` on the
subdiagonal. -/
noncomputable def thomasLower (N : ℕ) : Matrix (Fin N) (Fin N) K :=
  of fun i j => if i = j then 1 else if (j : ℕ) + 1 = i then thomasBeta a b c i else 0

/-- The upper bidiagonal factor of the Thomas algorithm, with the pivots `α_i` on the diagonal
and the superdiagonal `c` of the matrix. -/
noncomputable def thomasUpper (N : ℕ) : Matrix (Fin N) (Fin N) K :=
  of fun i j => if i = j then thomasAlpha a b c i else if (i : ℕ) + 1 = j then c i else 0

/-- The unit lower bidiagonal matrix with subdiagonal `β` (`β i` at `(i, i - 1)`), the shape of
the lower Thomas factor: `Matrix.thomasLower a b c N` is `lowerBidiagonalOf (thomasBeta a b c) N`
(`Matrix.thomasLower_eq`), and the computed factor of the floating-point Thomas algorithm is
`lowerBidiagonalOf β̂ N`. -/
def lowerBidiagonalOf [Zero R] [One R] (β : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  of fun i j => if i = j then 1 else if (j : ℕ) + 1 = i then β i else 0

/-- The upper bidiagonal matrix with diagonal `α` and superdiagonal `c`, the shape of the upper
Thomas factor: `Matrix.thomasUpper a b c N` is `upperBidiagonalOf (thomasAlpha a b c) c N`
(`Matrix.thomasUpper_eq`). -/
def upperBidiagonalOf [Zero R] (α c : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  of fun i j => if i = j then α i else if (i : ℕ) + 1 = j then c i else 0

/-- The exact Thomas lower factor is the bidiagonal matrix of the exact multipliers. -/
theorem thomasLower_eq (N : ℕ) :
    thomasLower a b c N = lowerBidiagonalOf (thomasBeta a b c) N := rfl

/-- The exact Thomas upper factor is the bidiagonal matrix of the exact pivots. -/
theorem thomasUpper_eq (N : ℕ) :
    thomasUpper a b c N = upperBidiagonalOf (thomasAlpha a b c) c N := rfl

/-- Left multiplication by the lower bidiagonal matrix adds `β_i` times the previous row. -/
theorem lowerBidiagonalOf_mul_apply [NonAssocSemiring R] {N : ℕ} (β : ℕ → R)
    (M : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    (lowerBidiagonalOf β N * M) i j =
      M i j + if h : 0 < (i : ℕ) then β i * M ⟨i - 1, by omega⟩ j else 0 := by
  rw [mul_apply]
  have hterm : ∀ r : Fin N, lowerBidiagonalOf β N i r * M r j =
      (if r = i then M i j else 0) + if _h : (r : ℕ) + 1 = i then β i * M r j else 0 := by
    intro r
    simp only [lowerBidiagonalOf, of_apply]
    by_cases hri : r = i
    · subst hri
      simp
    · simp only [Ne.symm hri, hri, ite_false, zero_add]
      split_ifs <;> simp
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sum_dite_val_add_one_eq]

/-- An entry of the upper bidiagonal matrix off its two diagonals vanishes. -/
theorem upperBidiagonalOf_apply_eq_zero [Zero R] {N : ℕ} {α c : ℕ → R} {i j : Fin N}
    (h1 : (i : ℕ) ≠ j) (h2 : (i : ℕ) + 1 ≠ j) : upperBidiagonalOf α c N i j = 0 := by
  simp [upperBidiagonalOf, Fin.ext_iff, h1, h2]

/-- The lower Thomas factor is lower bidiagonal. -/
theorem isLowerBidiagonal_thomasLower (N : ℕ) : (thomasLower a b c N).IsLowerBidiagonal := by
  intro i j h
  simp only [thomasLower, of_apply, Fin.ext_iff]
  rcases h with h | ⟨k, hk⟩ <;> simp only [Fin.lt_def] at * <;> split_ifs <;> first | rfl | omega

/-- The upper Thomas factor is upper bidiagonal. -/
theorem isUpperBidiagonal_thomasUpper (N : ℕ) : (thomasUpper a b c N).IsUpperBidiagonal := by
  intro i j h
  simp only [thomasUpper, of_apply, Fin.ext_iff]
  rcases h with h | ⟨k, hk⟩ <;> simp only [Fin.lt_def] at * <;> split_ifs <;> first | rfl | omega

/-- Each term of `(thomasLower * thomasUpper) i j`, split into the two possible contributions. -/
theorem thomasLower_apply_mul_eq {N : ℕ} (i j r : Fin N) :
    thomasLower a b c N i r * thomasUpper a b c N r j =
      (if r = i then thomasUpper a b c N i j else 0) +
        (if _h : (r : ℕ) + 1 = i then thomasBeta a b c i * thomasUpper a b c N r j else 0) := by
  simp only [thomasLower, of_apply]
  by_cases hri : r = i
  · subst hri
    simp
  · simp only [Ne.symm hri, hri, ite_false, zero_add]
    split_ifs <;> simp

/-- **The Thomas algorithm** ([quarteroni2000numerical] §3.7.1, (3.53)): when no pivot `α_i`,
`i < N - 1`, vanishes, the tridiagonal matrix with diagonals `a`, `b`, `c` factors as the unit
lower bidiagonal matrix of the multipliers `β_i` times the upper bidiagonal matrix of the pivots
`α_i` and the superdiagonal `c`. The pivot condition is equivalent to the nonsingularity of the
strict leading principal submatrices, by `Matrix.IsLU.det_strictLeadingPrincipalSubmatrix`. -/
theorem isLU_tridiagonal_thomas {N : ℕ} (hα : ∀ i, i + 1 < N → thomasAlpha a b c i ≠ 0) :
    IsLU (tridiagonalOfNat a b c N) (thomasLower a b c N) (thomasUpper a b c N) where
  isUnitLowerTriangular :=
    ⟨(isLowerBidiagonal_thomasLower a b c N).isLowerTriangular, fun i => by simp [thomasLower]⟩
  isUpperTriangular := (isUpperBidiagonal_thomasUpper a b c N).isUpperTriangular
  mul_eq := by
    ext i j
    simp only [mul_apply, thomasLower_apply_mul_eq, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sum_dite_val_add_one_eq]
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
    · simp only [show ¬ (0 < (i : ℕ)) by omega, dite_false, add_zero]
      simp only [thomasUpper, tridiagonalOfNat, of_apply, Fin.ext_iff, hi]
      split_ifs <;> first | omega | rfl | contradiction
    · simp only [hi, dite_true]
      obtain ⟨m, hm⟩ : ∃ m : Fin N, (m : ℕ) + 1 = i := ⟨⟨i - 1, by omega⟩, by simp; omega⟩
      have hmi : (⟨(i : ℕ) - 1, by omega⟩ : Fin N) = m := Fin.ext (by simp; omega)
      rw [hmi]
      simp only [thomasUpper, tridiagonalOfNat, of_apply, Fin.ext_iff, ← hm]
      have hmN : (m : ℕ) + 1 < N := hm ▸ i.2
      split_ifs
      all_goals try omega
      all_goals try rw [thomasAlpha_succ, sub_add_cancel]
      all_goals try rw [zero_add, thomasBeta_succ, div_mul_cancel₀ _ (hα m hmN)]
      all_goals simp

/-- The reciprocal pivots `γ_i = (a_i - b_i γ_{i-1} c_{i-1})⁻¹` of the division-free Thomas
algorithm, [quarteroni2000numerical] §3.7.2, with `γ_0 = a_0⁻¹`; they are the reciprocals of the
pivots `α_i` (`Matrix.thomasGamma_eq_inv_thomasAlpha`). -/
noncomputable def thomasGamma (a b c : ℕ → K) : ℕ → K
  | 0 => (a 0)⁻¹
  | i + 1 => (a (i + 1) - b (i + 1) * thomasGamma a b c i * c i)⁻¹

/-- The reciprocal pivots are the reciprocals of the pivots. -/
theorem thomasGamma_eq_inv_thomasAlpha (i : ℕ) : thomasGamma a b c i = (thomasAlpha a b c i)⁻¹ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [thomasGamma, ih, thomasAlpha_succ, thomasBeta_succ, div_eq_mul_inv]

end Thomas

end Matrix
