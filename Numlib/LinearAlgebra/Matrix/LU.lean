/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

This file treats the LU factorization as a specification. Let $n$ be a finite linearly ordered index
set. An **LU factorization** of a square matrix $A$ indexed by $n$ is a pair $(L, U)$ with $L$ unit
lower triangular, $U$ upper triangular and $LU = A$. The file proves what holds for every such pair,
independently of how it is computed. The presentation follows [quarteroni2000numerical], §3.3–3.4
and §3.7–3.8, and [higham2002accuracy], §9.1, §9.5–9.6 and Theorem 13.8. The algorithms are
elsewhere: Gaussian elimination, the Doolittle recurrence, pivoting and the growth factor in
`Numlib.LinearAlgebra.Matrix.LU.Elimination` and `Numlib.LinearAlgebra.Matrix.LU.Pivoting`, the
substitution solves in `Numlib.Direct.Substitution`, the rounding-error analysis in
`Numlib.FloatingPoint.LU`, and the Cholesky factorization in `Numlib.LinearAlgebra.Matrix.Cholesky`.

For $k \in n$, $A_{\le k}$ and $A_{< k}$ denote the leading principal submatrices with the indices
$i \le k$ and $i < k$. For sets $P$ and $Q$ of indices, $A_{PQ}$ is the submatrix with rows in $P$
and columns in $Q$, and $P^c$ is the complement of $P$. The central result is that $A$ has a unique
LU factorization if and only if every $A_{< k}$ is nonsingular. It is proved for block LU
factorizations along a labelling $b$ of the indices, and the scalar case is $b = \mathrm{id}$.
Further results relate the pivots $u_{kk}$ to the leading principal minors, give existence under
diagonal dominance, show that the factors keep the band and the envelope of $A$, and treat the
$LDM^T$, $LDL^T$ and rectangular factorizations and the Thomas algorithm for tridiagonal matrices.

## Main definitions

* `Matrix.leadingPrincipalSubmatrix`, `Matrix.strictLeadingPrincipalSubmatrix`,
  `Matrix.leadingPrincipalMinor`: the submatrices $A_{\le k}$ and $A_{< k}$, and the minor
  $\det A_{\le k}$.
* `Matrix.HasUnitStrictLeadingPrincipalSubmatrices`: every $A_{< k}$ is nonsingular, the hypothesis
  of the existence and uniqueness theorem.
* `Matrix.IsLU`: $L$ is unit lower triangular, $U$ is upper triangular and $LU = A$.
* `Matrix.IsLDM`: the factorization $A = L D M^T$ with $L$ and $M$ unit lower triangular and $D$
  diagonal; $M = L$ gives $A = L D L^T$.
* `Matrix.IsBlockUnitLowerTriangular`, `Matrix.IsBlockLU`: block unit lower triangular matrices and
  the block LU factorization along a labelling $b$ of the indices by a linear order.
* `Matrix.IsRectLU`: the rectangular LU factorization of an $M \times N$ matrix ([golub2013matrix]
  §3.2.10).
* `Matrix.envelope`: the lower envelope of a matrix.
* `Matrix.tridiagonalOfNat`: the tridiagonal matrix with the diagonals $a$, $b$ and $c$.
* `Matrix.thomasAlpha`, `Matrix.thomasBeta`, `Matrix.thomasGamma`: the pivots, the multipliers and
  the reciprocal pivots of the Thomas algorithm.
* `Matrix.thomasLower`, `Matrix.thomasUpper`, `Matrix.lowerBidiagonalOf`,
  `Matrix.upperBidiagonalOf`: the bidiagonal factors of the Thomas algorithm.

## Main results

* `Matrix.existsUnique_isBlockLU_iff`: a matrix has a unique block LU factorization along $b$ if and
  only if its leading block submatrices $A_{\{b < a\}}$, for the labels $a$ of $b$, are nonsingular
  ([quarteroni2000numerical] Theorem 3.7).
* `Matrix.existsUnique_isLU_iff`,
  `Matrix.exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix`, `Matrix.IsLU.unique`: the
  case $b = \mathrm{id}$, [quarteroni2000numerical] Theorem 3.4 and [higham2002accuracy] Theorem
  9.1.
* `Matrix.IsLU.det_leadingPrincipalSubmatrix`, `Matrix.IsLU.det_eq_prod_diag`,
  `Matrix.IsLU.diag_upper_eq_div_leadingPrincipalMinor`: the leading principal minors are the
  products of the pivots, and the pivots are ratios of consecutive minors ([quarteroni2000numerical]
  (3.39)).
* `Matrix.exists_isRectLU_of_forall_det_ne_zero`: a rectangular matrix whose leading blocks of order
  at most $\min(M, N)$ are nonsingular has a rectangular LU factorization.
* `Matrix.existsUnique_isLDM`, `Matrix.IsLDM.eq_of_isSymm`, `Matrix.IsLDM.diag_pos_of_posDef`:
  existence and uniqueness of the $LDM^T$ factorization ([quarteroni2000numerical] Theorem 3.5,
  [golub2013matrix] Theorem 4.1.3), the $LDL^T$ factorization of a symmetric matrix, and positivity
  of $D$ for a positive definite matrix.
* `Matrix.exists_isLU_of_isDiagDominant`, `Matrix.exists_isLU_of_isColDiagDominant`: a nonsingular
  matrix that is weakly diagonally dominant by rows or by columns has an LU factorization
  ([quarteroni2000numerical] Property 3.2, [higham2002accuracy] Theorem 9.9).
* `Matrix.IsLU.hasUpperBandwidth`, `Matrix.IsLU.hasLowerBandwidth`, `Matrix.IsLU.envelope_eq`: the
  factors keep the bandwidths of $A$ ([quarteroni2000numerical] Property 3.4), and $L$ has the
  envelope of $A$ ([quarteroni2000numerical] (3.60)).
* `Matrix.isLU_tridiagonal_thomas`: the Thomas recurrences (3.53) of [quarteroni2000numerical] give
  an LU factorization of a tridiagonal matrix with bidiagonal factors.
* `Matrix.isBlockLU_fromBlocks_schurComplement`: the block LU factorization with two blocks is the
  Schur complement factorization of [quarteroni2000numerical] §3.8.1.

## Proof outline

Existence of the block LU factorization is proved by strong induction on the number of indices. The
last block of labels is bordered onto the factorization of the leading block
(`Matrix.isBlockLU_fromBlocks`), which is the induction step of the proof of Theorem 3.4 of
[quarteroni2000numerical]. Uniqueness is the same induction with the bordering equations
$A_{P^c P} = L_{P^c P} U_{PP}$, $A_{P P^c} = L_{PP} U_{P P^c}$ and $A_{P^c P^c} = L_{P^c P} U_{P
P^c} + U_{P^c P^c}$. For necessity, a singular leading block gives a vector in the left kernel of
the corresponding block of $U$, and a perturbation along this vector gives a second factorization,
as in Example 3.3 of [quarteroni2000numerical]. Existence under diagonal dominance is proved by
induction through the Schur complement at the first index
(`Matrix.isLU_luLowerOfSchur_luUpperOfSchur`).

## Implementation notes

* The index type is any `[Fintype n] [LinearOrder n]`, not `Fin N`. A triangular factorization uses
  only the order, and `Matrix.toBlock` gives the leading blocks without reindexing.
* Lower triangular is Mathlib's `Matrix.IsLowerTriangular`, which is `Matrix.BlockTriangular` for
  `OrderDual.toDual`, and upper triangular is `Matrix.IsUpperTriangular`, which is
  `Matrix.BlockTriangular` for `id`. A block LU factorization along a labelling $b$ is the same
  structure with `id` replaced by $b$, and the scalar theory is derived from the block theory. The
  block theory needs only `[DecidableEq n]` on the indices.
* Where a leading block is reindexed (`Equiv.sumCompl` in the bordering step, and
  `Equiv.subtypeSubtypeEquivSubtype` when the hypothesis on the strict leading blocks passes to a
  leading block), nonsingularity is transported through `Matrix.det_submatrix_equiv_self`.
-/

open Finset

universe u

namespace Matrix

variable {n : Type u} {R : Type*}

/-! ### Leading principal submatrices -/

section LeadingPrincipal

variable [LinearOrder n]

/-- The **leading principal submatrix** $A_{\le k}$ of a square matrix $A$ indexed by a linear order
$n$: the submatrix of the entries $a_{ij}$ with $i \le k$ and $j \le k$.

It is indexed by the subtype `{i // i ≤ k}`. On `Fin N` with $k = i$, it is the submatrix
$A_{i+1}$ of order $i + 1$ of [quarteroni2000numerical] §3.3. -/
def leadingPrincipalSubmatrix (A : Matrix n n R) (k : n) :
    Matrix {i // i ≤ k} {i // i ≤ k} R :=
  A.toBlock (· ≤ k) (· ≤ k)

/-- The **strict leading principal submatrix** $A_{< k}$ of a square matrix $A$ indexed by a linear
order $n$: the submatrix of the entries $a_{ij}$ with $i < k$ and $j < k$.

It is indexed by the subtype `{i // i < k}`. As $k$ ranges over $n$, these are exactly the
leading principal submatrices of the orders $0, \dots, N - 1$, where $N$ is the number of
indices. Their nonsingularity is the hypothesis of the existence theorem for the LU
factorization, Theorem 3.4 of [quarteroni2000numerical]: "$A_i$ nonsingular for
$i = 1, \dots, n - 1$". The submatrix of order $0$ is the empty matrix, which is a unit. -/
def strictLeadingPrincipalSubmatrix (A : Matrix n n R) (k : n) :
    Matrix {i // i < k} {i // i < k} R :=
  A.toBlock (· < k) (· < k)

/-- The strict leading principal submatrices of the transpose are the transposes:
$(A^T)_{< k} = (A_{< k})^T$. -/
theorem strictLeadingPrincipalSubmatrix_transpose (A : Matrix n n R) (k : n) :
    Aᵀ.strictLeadingPrincipalSubmatrix k = (A.strictLeadingPrincipalSubmatrix k)ᵀ := rfl

/-- The **leading principal minor** $d_k = \det A_{\le k}$ of a square matrix $A$ over a commutative
ring. -/
noncomputable def leadingPrincipalMinor [Fintype n] [CommRing R] (A : Matrix n n R) (k : n) :
    R :=
  (A.leadingPrincipalSubmatrix k).det

/-- The entries of $A_{\le k}$ are the entries of $A$. -/
@[simp]
theorem leadingPrincipalSubmatrix_apply (A : Matrix n n R) (k : n) (i j : {i // i ≤ k}) :
    A.leadingPrincipalSubmatrix k i j = A i j := rfl

/-- The entries of $A_{< k}$ are the entries of $A$. -/
@[simp]
theorem strictLeadingPrincipalSubmatrix_apply (A : Matrix n n R) (k : n) (i j : {i // i < k}) :
    A.strictLeadingPrincipalSubmatrix k i j = A i j := rfl

omit [LinearOrder n] in
/-- Let $P$ and $Q$ be predicates on the indices with $Q(i) \iff P(i)$ for all $i$. Then the
submatrix of $A$ on $Q$ is the submatrix of $A$ on $P$, reindexed along
`Equiv.subtypeEquivRight`. -/
theorem toBlock_eq_submatrix_subtypeEquivRight (A : Matrix n n R) {p q : n → Prop}
    (h : ∀ i, q i ↔ p i) :
    A.toBlock q q = (A.toBlock p p).submatrix (Equiv.subtypeEquivRight h)
      (Equiv.subtypeEquivRight h) := by
  ext i j; rfl

variable [Fintype n]

omit [LinearOrder n] in
/-- Let $P$ and $Q$ be predicates on the indices with $Q(i) \iff P(i)$ for all $i$. Then the
submatrix of $A$ on $Q$ is nonsingular if and only if the submatrix of $A$ on $P$ is
nonsingular. -/
theorem isUnit_toBlock_congr [DecidableEq n] [CommRing R] (A : Matrix n n R) {p q : n → Prop}
    [DecidablePred p] [DecidablePred q] (h : ∀ i, q i ↔ p i) :
    IsUnit (A.toBlock q q) ↔ IsUnit (A.toBlock p p) := by
  rw [toBlock_eq_submatrix_subtypeEquivRight A h, isUnit_iff_isUnit_det,
    det_submatrix_equiv_self, ← isUnit_iff_isUnit_det]

/-- Let $A$ be a square matrix over a commutative ring, indexed by a finite linear order. If every
leading principal submatrix $A_{\le k}$ is nonsingular, then every strict leading principal
submatrix $A_{< k}$ is nonsingular.

The submatrix $A_{< k}$ is either empty or equal to $A_{\le k'}$ for the predecessor $k'$ of
$k$. -/
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

/-- A square matrix $A$ indexed by a finite linear order **has nonsingular strict leading principal
submatrices** if $A_{< k}$ is a unit for every index $k$.

As $k$ ranges over the indices, the submatrices $A_{< k}$ are the leading principal submatrices
of the orders $0, \dots, N - 1$. So this is the hypothesis of the existence and uniqueness
theorem for the LU factorization, Theorem 3.4 of [quarteroni2000numerical] ("$A_i$ nonsingular
for $i = 1, \dots, n - 1$"), which is `Matrix.existsUnique_isLU_iff`. -/
def HasUnitStrictLeadingPrincipalSubmatrices [Semiring R] (A : Matrix n n R) : Prop :=
  ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)

/-- $A$ has nonsingular strict leading principal submatrices if and only if $A_{< k}$ is a unit for
every $k$. -/
theorem hasUnitStrictLeadingPrincipalSubmatrices_iff [Semiring R] {A : Matrix n n R} :
    A.HasUnitStrictLeadingPrincipalSubmatrices ↔
      ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) :=
  Iff.rfl

/-- If $A$ has nonsingular strict leading principal submatrices, then $A_{< k}$ is a unit for every
$k$. -/
theorem HasUnitStrictLeadingPrincipalSubmatrices.isUnit [Semiring R] {A : Matrix n n R}
    (h : A.HasUnitStrictLeadingPrincipalSubmatrices) (k : n) :
    IsUnit (A.strictLeadingPrincipalSubmatrix k) :=
  h k

/-- If every leading principal submatrix $A_{\le k}$ is nonsingular, then $A$ has nonsingular strict
leading principal submatrices. -/
theorem HasUnitStrictLeadingPrincipalSubmatrices.of_forall_isUnit [CommRing R]
    {A : Matrix n n R} (h : ∀ k, IsUnit (A.leadingPrincipalSubmatrix k)) :
    A.HasUnitStrictLeadingPrincipalSubmatrices :=
  isUnit_strictLeadingPrincipalSubmatrix_of_forall_isUnit h

/-- If $A$ has nonsingular strict leading principal submatrices, then so has $A^T$. -/
theorem HasUnitStrictLeadingPrincipalSubmatrices.transpose [CommRing R] {A : Matrix n n R}
    (h : A.HasUnitStrictLeadingPrincipalSubmatrices) :
    Aᵀ.HasUnitStrictLeadingPrincipalSubmatrices := fun k => by
  rw [strictLeadingPrincipalSubmatrix_transpose, isUnit_transpose]
  exact h k

end LeadingPrincipal

/-- On `Fin N`, the determinant of $A_{< k}$ equals the determinant of the submatrix of the first
$k$ rows and columns of $A$, taken along `Fin.castLE`. -/
theorem det_strictLeadingPrincipalSubmatrix_castLE [CommRing R] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (k : Fin N) :
    (A.strictLeadingPrincipalSubmatrix k).det =
      (A.submatrix (Fin.castLE k.isLt.le) (Fin.castLE k.isLt.le)).det := by
  let e : Fin k ≃ {i : Fin N // i < k} :=
    { toFun := fun a => ⟨Fin.castLE k.isLt.le a, Fin.lt_def.2 a.2⟩
      invFun := fun i => ⟨i.1, Fin.lt_def.1 i.2⟩
      left_inv := fun a => rfl
      right_inv := fun i => rfl }
  rw [← det_submatrix_equiv_self e]
  rfl

/-! ### The LU specification -/

section IsLU

variable [LinearOrder n] [Fintype n]

/-- An **LU factorization** of a square matrix $A$ indexed by a finite linear order is a pair
$(L, U)$ such that $L$ is unit lower triangular, $U$ is upper triangular, and
$$LU = A.$$

Every LU algorithm satisfies this specification, and theorems about "the LU factorization" are
theorems about every pair that satisfies it ([quarteroni2000numerical] §3.3.1). -/
structure IsLU [Semiring R] (A L U : Matrix n n R) : Prop where
  /-- The lower factor $L$ is unit lower triangular. -/
  isUnitLowerTriangular : L.IsUnitLowerTriangular
  /-- The upper factor $U$ is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- The factors multiply to $A$: $LU = A$. -/
  mul_eq : L * U = A

variable [Semiring R] {A L U : Matrix n n R}

/-- Let $A = LU$ be an LU factorization. Then for all indices $i$ and $j$,
$$a_{ij} = \sum_{r \le \min(i, j)} l_{ir} u_{rj}.$$

This is (3.42) of [quarteroni2000numerical]. The other terms vanish because $L$ is zero to the
right of the diagonal and $U$ is zero below it. -/
theorem IsLU.apply_eq_sum (h : IsLU A L U) (i j : n) :
    A i j = ∑ r ∈ univ.filter (· ≤ min i j), L i r * U r j := by
  rw [← h.mul_eq, Matrix.mul_apply]
  refine (Finset.sum_filter_of_ne fun r _ hr => ?_).symm
  rw [le_min_iff]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hir | hjr
  · exact hr (by rw [h.isUnitLowerTriangular.isLowerTriangular
      (OrderDual.toDual_lt_toDual.2 hir), zero_mul])
  · exact hr (by rw [h.isUpperTriangular hjr, mul_zero])

/-- For a function $f$ on the indices with values in a commutative monoid, $\prod_{r \le i} f(r) =
\left(\prod_{r < i} f(r)\right) f(i)$. -/
@[to_additive /-- Splitting a sum over `{r ≤ i}` into the sum over `{r < i}` and the term at
`i`. -/]
theorem prod_filter_le_eq_mul {M : Type*} [CommMonoid M] (f : n → M) (i : n) :
    ∏ r ∈ univ.filter (· ≤ i), f r = (∏ r ∈ univ.filter (· < i), f r) * f i := by
  rw [← Finset.prod_erase_mul (univ.filter (· ≤ i)) f (mem_filter.2 ⟨mem_univ i, le_rfl⟩)]
  congr 2
  ext r
  simp [lt_iff_le_and_ne, and_comm]

/-- The upper factor, entry by entry. Let $A = LU$ be an LU factorization over a ring. Then for
$i \le j$,
$$u_{ij} = a_{ij} - \sum_{r < i} l_{ir} u_{rj}.$$

This is the first line of (3.43) of [quarteroni2000numerical]. -/
theorem IsLU.upper_apply_eq {R : Type*} [Ring R] {A L U : Matrix n n R} (h : IsLU A L U)
    {i j : n} (hij : i ≤ j) :
    U i j = A i j - ∑ r ∈ univ.filter (· < i), L i r * U r j := by
  rw [h.apply_eq_sum, min_eq_left hij, sum_filter_le_eq_add, h.isUnitLowerTriangular.diag_eq_one,
    one_mul, add_sub_cancel_left]

/-- The lower factor, entry by entry. Let $A = LU$ be an LU factorization over a ring. Then for
$j < i$,
$$l_{ij} u_{jj} = a_{ij} - \sum_{r < j} l_{ir} u_{rj}.$$

This is the second line of (3.43) of [quarteroni2000numerical]. -/
theorem IsLU.lower_apply_mul_diag_eq {R : Type*} [Ring R] {A L U : Matrix n n R} (h : IsLU A L U)
    {i j : n} (hij : j < i) :
    L i j * U j j = A i j - ∑ r ∈ univ.filter (· < j), L i r * U r j := by
  rw [h.apply_eq_sum, min_eq_right hij.le, sum_filter_le_eq_add, add_sub_cancel_left]

end IsLU

/-! ### Block LU along a labelling -/

section Block

variable [DecidableEq n] {α : Type*} [LinearOrder α] (b : n → α)

/-- Let $b$ be a labelling of the indices by a linear order. A square matrix $L$ is **block unit
lower triangular** along $b$ if $l_{ij} = 0$ whenever $b_i < b_j$, and $l_{ij} = \delta_{ij}$
whenever $b_i = b_j$.

The first condition is Mathlib's `Matrix.BlockTriangular (OrderDual.toDual ∘ b)`. For
$b = \mathrm{id}$ the notion is `Matrix.IsUnitLowerTriangular`, by
`Matrix.isBlockUnitLowerTriangular_id_iff`. -/
structure IsBlockUnitLowerTriangular [Zero R] [One R] (L : Matrix n n R) : Prop where
  /-- The matrix is block lower triangular along $b$: $l_{ij} = 0$ whenever $b_i < b_j$. -/
  blockTriangular : L.BlockTriangular (OrderDual.toDual ∘ b)
  /-- Within a diagonal block the matrix is the identity: $l_{ij} = \delta_{ij}$ whenever
  $b_i = b_j$. -/
  apply_eq_one_of_eq : ∀ i j, b i = b j → L i j = (1 : Matrix n n R) i j

/-- A **block LU factorization** of a square matrix $A$ along a labelling $b$ of the indices by a
linear order is a pair $(L, U)$ such that $L$ is block unit lower triangular along $b$, $U$ is
block upper triangular along $b$ ($u_{ij} = 0$ whenever $b_j < b_i$), and $LU = A$.

This is the factorization of Theorem 3.7 of [quarteroni2000numerical]. For $b = \mathrm{id}$ it
is `Matrix.IsLU`, by `Matrix.isBlockLU_id_iff`. The $m \times m$ blocks of the sizes
$n_1, \dots, n_m$ in the source are a monotone labelling $b : \{0, \dots, N - 1\} \to \{0,
\dots, m - 1\}$. A general labelling costs nothing and also covers the substructuring orderings
of [quarteroni2000numerical] §3.9.2. -/
structure IsBlockLU [Fintype n] [Semiring R] (A L U : Matrix n n R) : Prop where
  /-- The lower factor is block unit lower triangular along $b$. -/
  isBlockUnitLowerTriangular : IsBlockUnitLowerTriangular b L
  /-- The upper factor is block upper triangular along $b$: $u_{ij} = 0$ whenever $b_j < b_i$. -/
  blockTriangular : U.BlockTriangular b
  /-- The factors multiply to $A$: $LU = A$. -/
  mul_eq : L * U = A

variable {b}

/-- Let $f$ be a strictly monotone map between linear orders. A matrix is block unit lower
triangular along $f \circ b$ if and only if it is block unit lower triangular along $b$. -/
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

/-- Let $f$ be a strictly monotone map between linear orders. Then $(L, U)$ is a block LU
factorization of $A$ along $f \circ b$ if and only if it is a block LU factorization of $A$
along $b$. -/
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
/-- Let $M$ and $N$ be block lower triangular along $b$, and let $b_i = b_j$. Then
$$(MN)_{ij} = \sum_{r : b_r = b_i} m_{ir} n_{rj},$$
because a nonzero term needs $b_i \le b_r \le b_j$. -/
theorem BlockTriangular.mul_apply_of_eq [NonUnitalNonAssocSemiring R] {M N : Matrix n n R}
    (hM : M.BlockTriangular (OrderDual.toDual ∘ b)) (hN : N.BlockTriangular (OrderDual.toDual ∘ b))
    {i j : n} (hij : b i = b j) :
    (M * N) i j = ∑ r ∈ univ.filter (fun r => b r = b i), M i r * N r j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_filter_of_ne fun r _ hr => ?_).symm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hr (by rw [hN (show (OrderDual.toDual ∘ b) j < (OrderDual.toDual ∘ b) r from
      OrderDual.toDual_lt_toDual.2 (hij ▸ hlt)), mul_zero])
  · exact hr (by rw [hM (show (OrderDual.toDual ∘ b) r < (OrderDual.toDual ∘ b) i from
      OrderDual.toDual_lt_toDual.2 hlt), zero_mul])

/-- The product of two matrices that are block unit lower triangular along $b$ is block unit lower
triangular along $b$. -/
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
/-- The identity matrix is block unit lower triangular along every labelling. -/
theorem isBlockUnitLowerTriangular_one [Zero R] [One R] :
    IsBlockUnitLowerTriangular b (1 : Matrix n n R) :=
  ⟨blockTriangular_one, fun _ _ _ => rfl⟩

/-- A block unit lower triangular matrix $L$ over a commutative ring has $\det L = 1$.

The determinant is the product of the determinants of the diagonal blocks, which are identity
matrices. -/
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

/-- A block unit lower triangular matrix over a commutative ring is a unit. -/
theorem IsBlockUnitLowerTriangular.isUnit [CommRing R] {L : Matrix n n R}
    (hL : IsBlockUnitLowerTriangular b L) : IsUnit L :=
  (isUnit_iff_isUnit_det L).2 (by rw [hL.det_eq_one]; exact isUnit_one)

/-! ### Restriction to a leading block of labels -/

omit [DecidableEq n] in
/-- For sets $P$, $Q$ and $S$ of indices and square matrices $A$ and $B$, the block of the product
on $P \times S$ is
$$(AB)_{PS} = A_{PQ} B_{QS} + A_{P Q^c} B_{Q^c S}.$$

This is `Matrix.toBlock_mul_eq_add` without commutativity. -/
theorem toBlock_mul_eq_add' [NonUnitalNonAssocSemiring R] (p : n → Prop) (q : n → Prop)
    [DecidablePred q] (r : n → Prop) (A B : Matrix n n R) :
    (A * B).toBlock p r =
      A.toBlock p q * B.toBlock q r +
        (A.toBlock p fun i => ¬q i) * B.toBlock (fun i => ¬q i) r := by
  ext i k
  simp only [toBlock_apply, Matrix.mul_apply, Matrix.add_apply]
  exact (Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm

variable {p : n → Prop} [DecidablePred p]

omit [DecidableEq n] [Fintype n] [DecidablePred p] in
/-- Let $L$ be block lower triangular along $b$, and let $P$ be a set of indices that is closed
under decreasing the label: $i \in P$ and $b_j \le b_i$ imply $j \in P$. Then $L_{P P^c} = 0$. -/
theorem BlockTriangular.toBlock_not_eq_zero [Zero R] {L : Matrix n n R}
    (hL : L.BlockTriangular (OrderDual.toDual ∘ b)) (hp : ∀ i j, p i → b j ≤ b i → p j) :
    L.toBlock p (fun i => ¬p i) = 0 := by
  ext i j
  rw [toBlock_apply, Matrix.zero_apply]
  refine hL (OrderDual.toDual_lt_toDual.2 (lt_of_not_ge fun h => ?_))
  exact j.2 (hp i.1 j.1 i.2 h)

omit [DecidableEq n] [Fintype n] [DecidablePred p] in
/-- Let $U$ be block upper triangular along $b$, and let $P$ be a set of indices that is closed
under decreasing the label: $i \in P$ and $b_j \le b_i$ imply $j \in P$. Then $U_{P^c P} = 0$. -/
theorem BlockTriangular.not_toBlock_eq_zero [Zero R] {U : Matrix n n R} (hU : U.BlockTriangular b)
    (hp : ∀ i j, p i → b j ≤ b i → p j) : U.toBlock (fun i => ¬p i) p = 0 := by
  ext i j
  rw [toBlock_apply, Matrix.zero_apply]
  refine hU (lt_of_not_ge fun h => ?_)
  exact i.2 (hp j.1 i.1 j.2 h)

omit [Fintype n] [DecidablePred p] in
/-- Let $L$ be block unit lower triangular along $b$, and let $P$ be a set of indices whose
complement lies in a single block: $b_i = b_j$ for all $i, j \notin P$. Then $L_{P^c P^c} = I$. -/
theorem IsBlockUnitLowerTriangular.toBlock_eq_one [Zero R] [One R] {L : Matrix n n R}
    (hL : IsBlockUnitLowerTriangular b L) (hq : ∀ i j, ¬p i → ¬p j → b i = b j) :
    L.toBlock (fun i => ¬p i) (fun i => ¬p i) = 1 := by
  ext i j
  rw [toBlock_apply, hL.apply_eq_one_of_eq i.1 j.1 (hq _ _ i.2 j.2)]
  exact congrFun (congrFun (toBlock_one_self (fun i => ¬p i)) i) j

variable [Semiring R] {A L U : Matrix n n R}

/-- A block LU factorization restricts to every leading block of labels. Let $(L, U)$ be a block LU
factorization of $A$ along $b$, and let $P$ be a set of indices that is closed under decreasing
the label: $i \in P$ and $b_j \le b_i$ imply $j \in P$. Then $(L_{PP}, U_{PP})$ is a block LU
factorization of $A_{PP}$ along the restriction of $b$ to $P$.

In particular $A_{PP} = L_{PP} U_{PP}$. This is (3.38) of [quarteroni2000numerical], read
downwards. -/
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

/-- A bordering equation of the block LU factorization. Let $(L, U)$ be a block LU factorization of
$A$ along $b$, and let $P$ be a set of indices that is closed under decreasing the label. Then
$$A_{P^c P} = L_{P^c P} U_{PP}.$$
-/
theorem IsBlockLU.toBlock_not_left (h : IsBlockLU b A L U)
    (hp : ∀ i j, p i → b j ≤ b i → p j) :
    A.toBlock (fun i => ¬p i) p = L.toBlock (fun i => ¬p i) p * U.toBlock p p := by
  rw [← h.mul_eq, toBlock_mul_eq_add' _ p, h.blockTriangular.not_toBlock_eq_zero hp,
    Matrix.mul_zero, add_zero]

/-- A bordering equation of the block LU factorization. Let $(L, U)$ be a block LU factorization of
$A$ along $b$, and let $P$ be a set of indices that is closed under decreasing the label. Then
$$A_{P P^c} = L_{PP} U_{P P^c}.$$
-/
theorem IsBlockLU.toBlock_not_right (h : IsBlockLU b A L U)
    (hp : ∀ i j, p i → b j ≤ b i → p j) :
    A.toBlock p (fun i => ¬p i) = L.toBlock p p * U.toBlock p (fun i => ¬p i) := by
  rw [← h.mul_eq, toBlock_mul_eq_add' _ p,
    h.isBlockUnitLowerTriangular.blockTriangular.toBlock_not_eq_zero hp, Matrix.zero_mul,
    add_zero]

/-- A bordering equation of the block LU factorization. Let $(L, U)$ be a block LU factorization of
$A$ along $b$, and let $P$ be a set of indices whose complement lies in a single block:
$b_i = b_j$ for all $i, j \notin P$. Then
$$A_{P^c P^c} = L_{P^c P} U_{P P^c} + U_{P^c P^c}.$$
-/
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

/-- Along the labelling $b = \mathrm{id}$, a matrix is block unit lower triangular if and only if it
is unit lower triangular. -/
theorem isBlockUnitLowerTriangular_id_iff [Zero R] [One R] {L : Matrix n n R} :
    IsBlockUnitLowerTriangular id L ↔ L.IsUnitLowerTriangular := by
  constructor
  · rintro ⟨hL, hd⟩
    exact ⟨hL, fun i => by simpa using hd i i rfl⟩
  · rintro ⟨hL, hd⟩
    refine ⟨hL, fun i j hij => ?_⟩
    obtain rfl : i = j := hij
    simp [hd]

/-- Along the labelling $b = \mathrm{id}$, $(L, U)$ is a block LU factorization of $A$ if and only
if it is an LU factorization of $A$. -/
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

/-- An LU factorization restricts to every leading principal submatrix. If $A = LU$ is an LU
factorization, then $A_{\le k} = L_{\le k} U_{\le k}$ is an LU factorization for every $k$.

This is (3.38) of [quarteroni2000numerical]. -/
theorem IsLU.toBlock_le (h : IsLU A L U) (k : n) :
    IsLU (A.leadingPrincipalSubmatrix k) (L.leadingPrincipalSubmatrix k)
      (U.leadingPrincipalSubmatrix k) :=
  isBlockLU_id_iff.1 ((isBlockLU_comp_iff (b := id) (Subtype.strictMono_coe (· ≤ k))).1
    ((isBlockLU_id_iff.2 h).toBlock (p := (· ≤ k)) fun _ _ hi hji => hji.trans hi))

/-- An LU factorization restricts to every strict leading principal submatrix. If $A = LU$ is an LU
factorization, then $A_{< k} = L_{< k} U_{< k}$ is an LU factorization for every $k$. -/
theorem IsLU.toBlock_lt (h : IsLU A L U) (k : n) :
    IsLU (A.strictLeadingPrincipalSubmatrix k) (L.strictLeadingPrincipalSubmatrix k)
      (U.strictLeadingPrincipalSubmatrix k) :=
  isBlockLU_id_iff.1 ((isBlockLU_comp_iff (b := id) (Subtype.strictMono_coe (· < k))).1
    ((isBlockLU_id_iff.2 h).toBlock (p := (· < k)) fun _ _ hi hji => hji.trans_lt hi))

/-- Let $A = LU$ be an LU factorization over a commutative ring. Then
$$\det A = \prod_i u_{ii}.$$

This is stated after Example 3.3 of [quarteroni2000numerical]. -/
theorem IsLU.det_eq_prod_diag (h : IsLU A L U) : A.det = ∏ i, U i i := by
  rw [← h.mul_eq, det_mul, h.isUnitLowerTriangular.det_eq_one, one_mul,
    det_of_isUpperTriangular h.isUpperTriangular]

/-- **Equation (3.39)** of [quarteroni2000numerical]. Let $A = LU$ be an LU factorization over a
commutative ring. Then the leading principal minors are the products of the leading pivots: for
every $k$,
$$\det A_{\le k} = \prod_{i \le k} u_{ii}.$$
-/
theorem IsLU.det_leadingPrincipalSubmatrix (h : IsLU A L U) (k : n) :
    (A.leadingPrincipalSubmatrix k).det = ∏ i ∈ univ.filter (· ≤ k), U i i := by
  -- the two `DecidableEq {i // i ≤ k}` instances in play are propositionally equal
  have h1 : (A.leadingPrincipalSubmatrix k).det = ∏ i : {i // i ≤ k}, U i i := by
    convert (h.toBlock_le k).det_eq_prod_diag using 2
    rfl
  rw [h1, Finset.prod_subtype (p := (· ≤ k)) (univ.filter (· ≤ k)) (by simp) fun i => U i i]

/-- Let $A = LU$ be an LU factorization over a commutative ring. Then the strict leading principal
minors are the products of the pivots before $k$: for every $k$,
$$\det A_{< k} = \prod_{i < k} u_{ii}.$$
-/
theorem IsLU.det_strictLeadingPrincipalSubmatrix (h : IsLU A L U) (k : n) :
    (A.strictLeadingPrincipalSubmatrix k).det = ∏ i ∈ univ.filter (· < k), U i i := by
  have h1 : (A.strictLeadingPrincipalSubmatrix k).det = ∏ i : {i // i < k}, U i i := by
    convert (h.toBlock_lt k).det_eq_prod_diag using 2
    rfl
  rw [h1, Finset.prod_subtype (p := (· < k)) (univ.filter (· < k)) (by simp) fun i => U i i]

variable {K : Type*} [Field K] {A L U : Matrix n n K}

/-- Let $A = LU$ be an LU factorization over a field. If $A_{< k}$ is nonsingular, then
$u_{jj} \neq 0$ for every $j < k$. -/
theorem IsLU.diag_upper_ne_zero_of_lt (h : IsLU A L U) {k : n}
    (hk : IsUnit (A.strictLeadingPrincipalSubmatrix k)) {j : n} (hj : j < k) : U j j ≠ 0 := by
  have hdet := (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 hk))
  rw [h.det_strictLeadingPrincipalSubmatrix, Finset.prod_ne_zero_iff] at hdet
  exact hdet j (mem_filter.2 ⟨mem_univ _, hj⟩)

/-- The pivots are ratios of consecutive leading principal minors. Let $A = LU$ be an LU
factorization over a field, and suppose that $\det A_{< k} \neq 0$. Then
$$u_{kk} = \frac{\det A_{\le k}}{\det A_{< k}}.$$

This is stated after (3.39) in §3.3.1 of [quarteroni2000numerical]. -/
theorem IsLU.diag_upper_eq_div_leadingPrincipalMinor (h : IsLU A L U) {k : n}
    (hk : (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    U k k = (A.leadingPrincipalSubmatrix k).det / (A.strictLeadingPrincipalSubmatrix k).det := by
  rw [eq_div_iff hk, h.det_leadingPrincipalSubmatrix, h.det_strictLeadingPrincipalSubmatrix,
    prod_filter_le_eq_mul, mul_comm]

end Det

/-! ### Leading principal submatrices on `Fin N` -/

section Fin

/-- On `Fin N`, the determinant of the leading principal submatrix $A_{\le k}$ equals the
determinant of the submatrix of the first $k + 1$ rows and columns of $A$, taken along
`Fin.castLE`.

The two matrices agree up to the reindexing of `{i // i ≤ k}` by `Fin (k + 1)`. -/
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

/-- **The block LU factors of a block tridiagonal matrix are block bidiagonal.** Let $A$ be a square
matrix of order $N$ over a field, and let $b : \{0, \dots, N - 1\} \to \{0, \dots, m - 1\}$ be a
labelling of the indices. Suppose that $A$ is block tridiagonal along $b$, that is, $a_{ij} = 0$
whenever $b_j + 1 < b_i$ or $b_i + 1 < b_j$. Suppose also that the leading block
$A_{\{b \le k\}}$ of the indices $i$ with $b_i \le k$ is nonsingular for every $k < m$. If
$(L, U)$ is a block LU factorization of $A$ along $b$, then $l_{ij} = 0$ whenever
$b_j + 1 < b_i$, and $u_{ij} = 0$ whenever $b_i + 1 < b_j$.

This follows §3.8.3 of [quarteroni2000numerical]. Thus $L$ has only its diagonal and first
subdiagonal blocks, and $U$ only its diagonal and first superdiagonal blocks. It is the block
form of `Matrix.IsLU.hasLowerBandwidth`. As there, the clause for $U$ needs no hypothesis on the
leading blocks, and the clause for $L$ needs it. The proof uses `Matrix.IsBlockLU.toBlock`,
`Matrix.IsBlockLU.toBlock_not_left` and `Matrix.IsBlockLU.toBlock_not_right`. -/
theorem IsBlockLU.blockBidiagonal_of_blockTridiagonal {N m : ℕ} {b : Fin N → Fin m} {K : Type*}
    [Field K] {A L U : Matrix (Fin N) (Fin N) K} (h : IsBlockLU b A L U)
    (htriL : ∀ i j, (b j : ℕ) + 1 < b i → A i j = 0)
    (htriU : ∀ i j, (b i : ℕ) + 1 < b j → A i j = 0)
    (hlead : ∀ k : Fin m, IsUnit (A.toBlock (b · ≤ k) (b · ≤ k))) :
    (∀ i j, (b j : ℕ) + 1 < b i → L i j = 0) ∧ ∀ i j, (b i : ℕ) + 1 < b j → U i j = 0 := by
  constructor
  · intro i j hij
    have hp : ∀ x y : Fin N, b x ≤ b j → b y ≤ b x → b y ≤ b j := fun _ _ hx hyx => hyx.trans hx
    have hUp : IsUnit (U.toBlock (b · ≤ b j) (b · ≤ b j)) := by
      have hmul := (h.toBlock hp).mul_eq
      rw [isUnit_iff_isUnit_det]
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
    rw [toBlock_apply, Matrix.mul_apply] at hentry
    rw [hentry]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [toBlock_apply, htriL i x.1 (by omega), zero_mul]
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
    rw [toBlock_apply, Matrix.mul_apply] at hentry
    rw [hentry]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [toBlock_apply, htriU x.1 j (by omega), mul_zero]

end BlockTridiagonal

/-! ### Existence and uniqueness of the block LU factorization -/

section BlockExistence

variable {α : Type*} [LinearOrder α]

/-- For a set $P$ of indices, the square matrix $A$ reindexed along `Equiv.sumCompl P` is the block
matrix
$$\begin{bmatrix} A_{PP} & A_{P P^c} \\ A_{P^c P} & A_{P^c P^c} \end{bmatrix}.$$
-/
theorem submatrix_sumCompl_eq_fromBlocks (A : Matrix n n R) (p : n → Prop) [DecidablePred p] :
    A.submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) =
      fromBlocks (A.toBlock p p) (A.toBlock p fun i => ¬p i)
        (A.toBlock (fun i => ¬p i) p) (A.toBlock (fun i => ¬p i) fun i => ¬p i) := by
  ext (i | i) (j | j) <;> rfl

/-- Two square matrices are equal if their four blocks along a set $P$ of indices are equal. -/
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

/-- Let $e$ be an equivalence of index types. The matrix $L$ reindexed along $e$ is block unit lower
triangular along $b$ if and only if $L$ is block unit lower triangular along $b \circ e$. -/
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

/-- Let $e$ be an equivalence of index types. The matrices $A$, $L$, $U$ reindexed along $e$ form a
block LU factorization along $b$ if and only if $A$, $L$, $U$ form a block LU factorization
along $b \circ e$. -/
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

/-- **The bordering step.** Let $c$ be a labelling of the indices of $m \sqcup n$ such that every
label of $m$ is smaller than every label of $n$, and all indices of $n$ have the same label. Let
$A_{11}$, $A_{12}$, $A_{21}$ and $A_{22}$ be the blocks of a matrix over a field, and suppose
that $A_{11} = L' U'$ is a block LU factorization along the restriction of $c$ to $m$ with $L'$
and $U'$ nonsingular. Then
$$\begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix} = \begin{bmatrix} L' & 0 \\
  A_{21} U'^{-1} & I \end{bmatrix} \begin{bmatrix} U' & L'^{-1} A_{12} \\ 0 & A_{22} - A_{21}
  U'^{-1} L'^{-1} A_{12} \end{bmatrix}$$
is a block LU factorization along $c$.

This is §3.8.1 of [quarteroni2000numerical], and the induction step of the proof of Theorem 3.4
there. -/
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
        simp [Matrix.one_apply]
      · exact absurd (hij ▸ hc i j) (lt_irrefl _)
      · exact absurd (hij ▸ hc j i) (lt_irrefl _)
      · simp [Matrix.one_apply]
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

/-- Suppose that the strict leading blocks $A_{\{b < a\}}$ are nonsingular for all labels $a$ of
$b$. Then, for every $k$, the leading block $A_{\{b < k\}}$, labelled by the restriction of $b$,
satisfies the same hypothesis. -/
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
/-- Existence of the block LU factorization for matrices with $N$ indices. Let $n$ have $N$
elements, let $b$ label the indices by a linear order, and let $A$ be a square matrix over a
field indexed by $n$. If the strict leading block $A_{\{b < a\}}$ is nonsingular for every label
$a$ of $b$, then $A$ has a block LU factorization along $b$.

The proof is by strong induction on $N$. The last block of labels is bordered onto the
factorization of the leading block by `Matrix.isBlockLU_fromBlocks`. -/
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

/-- **Theorem 3.7** of [quarteroni2000numerical], existence. Let $A$ be a square matrix over a
field, indexed by a finite set with a labelling $b$ by a linear order. If the strict leading
block $A_{\{b < a\}}$, made of the indices $i$ with $b_i < a$, is nonsingular for every label
$a$ of $b$, then $A$ has a block LU factorization along $b$. -/
theorem exists_isBlockLU_of_forall_isUnit {b : n → α} {A : Matrix n n K}
    (hA : ∀ a ∈ Set.range b, IsUnit (A.toBlock (b · < a) (b · < a))) :
    ∃ L U, IsBlockLU b A L U :=
  exists_isBlockLU_of_card _ b A rfl hA

omit [DecidableEq m] [Fintype m] in
/-- Uniqueness of the block LU factorization for matrices with $N$ indices. Let $n$ have $N$
elements, let $b$ label the indices by a linear order, and let $A$ be a square matrix over a
field indexed by $n$ whose strict leading blocks $A_{\{b < a\}}$ are nonsingular for all labels
$a$ of $b$. If $(L_1, U_1)$ and $(L_2, U_2)$ are block LU factorizations of $A$ along $b$, then
$L_1 = L_2$ and $U_1 = U_2$.

The proof is the induction of the existence proof. On the leading block the two factorizations
agree by induction, and the bordering equations `Matrix.IsBlockLU.toBlock_not_left`,
`Matrix.IsBlockLU.toBlock_not_right` and `Matrix.IsBlockLU.toBlock_not_not` determine the last
block. -/
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

/-- **Theorem 3.7** of [quarteroni2000numerical], uniqueness. Let $A$ be a square matrix over a
field, indexed by a finite set with a labelling $b$ by a linear order, and suppose that the
strict leading block $A_{\{b < a\}}$ is nonsingular for every label $a$ of $b$. If $(L_1, U_1)$
and $(L_2, U_2)$ are block LU factorizations of $A$ along $b$, then $L_1 = L_2$ and $U_1 = U_2$. -/
theorem IsBlockLU.unique {b : n → α} {A L₁ U₁ L₂ U₂ : Matrix n n K}
    (hA : ∀ a ∈ Set.range b, IsUnit (A.toBlock (b · < a) (b · < a)))
    (h₁ : IsBlockLU b A L₁ U₁) (h₂ : IsBlockLU b A L₂ U₂) : L₁ = L₂ ∧ U₁ = U₂ :=
  isBlockLU_unique_of_card _ b A L₁ U₁ L₂ U₂ rfl hA h₁ h₂

/-- Without nonsingular leading blocks, the block LU factorization is not unique. Let $(L, U)$ be a
block LU factorization of $A$ along $b$ over a field, and let $a$ be a label of $b$ such that
the strict leading block $A_{\{b < a\}}$ is singular. Then there is a second block LU
factorization $(L', U')$ of $A$ along $b$ with $L' \neq L$.

This is the necessity half of Theorem 3.4 of [quarteroni2000numerical], and Example 3.3 there.
Take $y \neq 0$ in the left kernel of the block $U_{\{b < a\}}$, and let $E$ be the matrix whose
only nonzero row is $y$, padded with zeros, at an index with the label $a$. Then
$(L(I + E), (I - E)U)$ is a second factorization. -/
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
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = i₀
    · subst hr
      have : ¬ p r := lt_irrefl _
      simp [hE, this]
    · simp [hE, hr]
  have hEU : ∀ j, p j → (E * U) i₀ j = 0 := fun j hj => by
    have := congrFun hyU ⟨j, hj⟩
    rw [vecMul, dotProduct, Pi.zero_apply] at this
    rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype p,
      Finset.sum_eq_zero (s := (univ : Finset {x // ¬p x})) (fun r _ => by simp [hE, r.2]),
      add_zero, ← this]
    exact Finset.sum_congr rfl fun r _ => by simp [hE, r.2]
  have hEU' : ∀ i j, i ≠ i₀ → (E * U) i j = 0 := fun i j hi => by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun r _ => by simp [hE, hi]
  refine ⟨L * (1 + E), (1 - E) * U, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine h.isBlockUnitLowerTriangular.mul ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · have hij' : b i < b j := OrderDual.toDual_lt_toDual.1 hij
      rw [Matrix.add_apply, one_apply_ne (ne_of_apply_ne b hij'.ne), zero_add, hE, of_apply]
      split_ifs with hi hj
      · rw [hi] at hij'
        exact absurd ((hj : b j < b i₀).trans hij') (lt_irrefl _)
      · rfl
      · rfl
    · rw [Matrix.add_apply, hE, of_apply]
      split_ifs with hi hj
      · rw [hi] at hij
        have hj' : b j < b i₀ := hj
        rw [hij] at hj'
        exact absurd hj' (lt_irrefl _)
      · rw [add_zero]
      · rw [add_zero]
  · intro i j hij
    rw [sub_mul, Matrix.one_mul, Matrix.sub_apply, h.blockTriangular hij, zero_sub, neg_eq_zero]
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
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, add_eq_left, Matrix.mul_apply,
      Finset.sum_eq_single i₀ (fun r _ hr => by simp [hE, hr]) (fun h => absurd (mem_univ _) h),
      h.isBlockUnitLowerTriangular.apply_eq_one_of_eq i₀ i₀ rfl, one_apply_eq, one_mul] at this
    exact hj (by simpa [hE, j.2] using this)

/-- **Theorem 3.7** of [quarteroni2000numerical]. Let $A$ be a square matrix over a field, indexed
by a finite set with a labelling $b$ by a linear order. Then $A$ has a unique block LU
factorization along $b$ if and only if the strict leading block $A_{\{b < a\}}$, made of the
indices $i$ with $b_i < a$, is nonsingular for every label $a$ attained by $b$.

Theorem 3.4 of [quarteroni2000numerical] is the case $b = \mathrm{id}$. The source states the
condition for "the $m - 1$ dominant principal block minors". The block for the smallest label is
empty, and the block for the largest label is $A$ without its last block row and column, so the
condition on the labels in the range of $b$ is exactly the condition on the $m - 1$ blocks of
the source. -/
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

/-- Along the labelling $b = \mathrm{id}$, the strict leading blocks of $A$ are nonsingular if and
only if $A$ has nonsingular strict leading principal submatrices. -/
theorem forall_isUnit_toBlock_id_iff {A : Matrix n n K} :
    (∀ a ∈ Set.range (id : n → n), IsUnit (A.toBlock (id · < a) (id · < a))) ↔
      A.HasUnitStrictLeadingPrincipalSubmatrices := by
  simp only [Set.range_id, Set.mem_univ, true_implies, id]
  exact Iff.rfl

/-- **Theorem 3.4** of [quarteroni2000numerical], existence. Let $A$ be a square matrix over a
field, indexed by a finite linear order. If every strict leading principal submatrix $A_{< k}$
is nonsingular, then $A$ has an LU factorization $A = LU$ with $L$ unit lower triangular and $U$
upper triangular.

This is also Theorem 9.1 of [higham2002accuracy]. -/
theorem exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix {A : Matrix n n K}
    (hA : A.HasUnitStrictLeadingPrincipalSubmatrices) : ∃ L U, IsLU A L U := by
  obtain ⟨L, U, h⟩ :=
    exists_isBlockLU_of_forall_isUnit (b := id) (forall_isUnit_toBlock_id_iff.2 hA)
  exact ⟨L, U, isBlockLU_id_iff.1 h⟩

/-- **Theorem 3.4** of [quarteroni2000numerical], uniqueness. Let $A$ be a square matrix over a
field, indexed by a finite linear order, such that every strict leading principal submatrix
$A_{< k}$ is nonsingular. If $A = L_1 U_1$ and $A = L_2 U_2$ are LU factorizations, then
$L_1 = L_2$ and $U_1 = U_2$. -/
theorem IsLU.unique {A L₁ U₁ L₂ U₂ : Matrix n n K} (h₁ : IsLU A L₁ U₁) (h₂ : IsLU A L₂ U₂)
    (hA : A.HasUnitStrictLeadingPrincipalSubmatrices) : L₁ = L₂ ∧ U₁ = U₂ :=
  IsBlockLU.unique (b := id) (forall_isUnit_toBlock_id_iff.2 hA) (isBlockLU_id_iff.2 h₁)
    (isBlockLU_id_iff.2 h₂)

/-- **Theorem 3.4** of [quarteroni2000numerical]. Let $A$ be a square matrix over a field, indexed
by a finite linear order. Then $A$ has a unique LU factorization $A = LU$, with $L$ unit lower
triangular and $U$ upper triangular, if and only if every strict leading principal submatrix
$A_{< k}$ is nonsingular.

This is also Theorem 9.1 of [higham2002accuracy]. The submatrices $A_{< k}$ are the matrices
$A_i$, $i = 1, \dots, n - 1$, of the source, together with the empty matrix. -/
theorem existsUnique_isLU_iff (A : Matrix n n K) :
    (∃! LU : Matrix n n K × Matrix n n K, IsLU A LU.1 LU.2) ↔
      A.HasUnitStrictLeadingPrincipalSubmatrices := by
  rw [← forall_isUnit_toBlock_id_iff, ← existsUnique_isBlockLU_iff]
  exact existsUnique_congr fun LU => isBlockLU_id_iff.symm

end Theorem34

/-! ### The rectangular LU factorization -/

section RectLU

variable {M N P : ℕ}

/-- A **rectangular LU factorization** of $A \in R^{M \times N}$ is a pair $(L, U)$ with
$L \in R^{M \times P}$ and $U \in R^{P \times N}$ such that $L$ is unit lower trapezoidal
($l_{ij} = 0$ for $i < j$ and $l_{ii} = 1$), $U$ is upper trapezoidal ($u_{ij} = 0$ for
$j < i$), and $LU = A$.

This is the factorization of [golub2013matrix] §3.2.10. The index comparisons are on the
natural-number values, because the index types differ. They use the rectangular band predicates
of `Numlib.LinearAlgebra.Matrix.Band`. On a square `Fin N` it is `Matrix.IsLU`, by
`Matrix.isRectLU_iff_isLU`. -/
structure IsRectLU [Semiring R] (A : Matrix (Fin M) (Fin N) R) (L : Matrix (Fin M) (Fin P) R)
    (U : Matrix (Fin P) (Fin N) R) : Prop where
  /-- The lower factor is lower trapezoidal: $l_{ij} = 0$ for $i < j$. -/
  hasUpperBandwidthRect : L.HasUpperBandwidthRect 0
  /-- The lower factor has ones on its diagonal: $l_{ij} = 1$ for $i = j$. -/
  apply_eq_one : ∀ (i : Fin M) (j : Fin P), (i : ℕ) = j → L i j = 1
  /-- The upper factor is upper trapezoidal: $u_{ij} = 0$ for $j < i$. -/
  hasLowerBandwidthRect : U.HasLowerBandwidthRect 0
  /-- The factors multiply to $A$: $LU = A$. -/
  mul_eq : L * U = A

/-- For square matrices of order $N$ and $P = N$, $(L, U)$ is a rectangular LU factorization of $A$
if and only if it is an LU factorization of $A$. -/
theorem isRectLU_iff_isLU [Semiring R] {A L U : Matrix (Fin N) (Fin N) R} :
    IsRectLU A L U ↔ IsLU A L U := by
  constructor
  · intro h
    refine ⟨⟨fun i j hij => h.hasUpperBandwidthRect i j ?_, fun i => h.apply_eq_one i i rfl⟩,
      fun i j hij => h.hasLowerBandwidthRect i j ?_, h.mul_eq⟩
    · rw [add_zero]; exact OrderDual.toDual_lt_toDual.1 hij
    · rw [add_zero]; exact hij
  · intro h
    refine ⟨fun i j hij => h.isUnitLowerTriangular.isLowerTriangular ?_,
      fun i j hij => ?_, fun i j hij => h.isUpperTriangular ?_, h.mul_eq⟩
    · rw [add_zero] at hij; exact OrderDual.toDual_lt_toDual.2 hij
    · rw [Fin.ext hij, h.isUnitLowerTriangular.diag_eq_one]
    · rw [add_zero] at hij; exact hij

/-- **Cutting a square factorization to a rectangular one.** Let $L U = S$ for square matrices of
order $K$, and let $M, N, P \le K$. Suppose that the leading $M \times N$ block of $S$ is $A$,
that the leading $M \times P$ block of $L$ is unit lower trapezoidal, that the leading
$P \times N$ block of $U$ is upper trapezoidal, and that $l_{ir} u_{rj} = 0$ for all $i < M$,
$j < N$ and $r \ge P$. Then the leading $M \times P$ block of $L$ and the leading $P \times N$
block of $U$ form a rectangular LU factorization of $A$.

This is the last step of the existence proofs that border $A$ to a square matrix. -/
theorem isRectLU_submatrix_of_mul_eq [Semiring R] {K : ℕ} {A : Matrix (Fin M) (Fin N) R}
    {S L U : Matrix (Fin K) (Fin K) R} (hLU : L * U = S) (hM : M ≤ K) (hN : N ≤ K) (hP : P ≤ K)
    (hA : ∀ i j, S (Fin.castLE hM i) (Fin.castLE hN j) = A i j)
    (hL : ∀ (i : Fin M) (j : Fin P), (i : ℕ) < j → L (Fin.castLE hM i) (Fin.castLE hP j) = 0)
    (hLd : ∀ (i : Fin M) (j : Fin P), (i : ℕ) = j → L (Fin.castLE hM i) (Fin.castLE hP j) = 1)
    (hU : ∀ (i : Fin P) (j : Fin N), (j : ℕ) < i → U (Fin.castLE hP i) (Fin.castLE hN j) = 0)
    (hout : ∀ (i : Fin M) (j : Fin N) (r : Fin K), P ≤ (r : ℕ) →
      L (Fin.castLE hM i) r * U r (Fin.castLE hN j) = 0) :
    IsRectLU A (L.submatrix (Fin.castLE hM) (Fin.castLE hP))
      (U.submatrix (Fin.castLE hP) (Fin.castLE hN)) where
  hasUpperBandwidthRect i j hij := hL i j (by simpa using hij)
  apply_eq_one := hLd
  hasLowerBandwidthRect i j hij := hU i j (by simpa using hij)
  mul_eq := by
    ext i j
    rw [← hA, ← hLU, Matrix.mul_apply, Matrix.mul_apply]
    refine Fintype.sum_of_injective (Fin.castLE hP) (Fin.castLE_injective hP) _ _
      (fun r hr => hout i j r ?_) fun r => rfl
    by_contra hcon
    exact hr ⟨⟨r, by omega⟩, rfl⟩

/-- The square matrix of order $\max(M, N)$ that has $A$ in its leading $M \times N$ block and zeros
elsewhere. -/
private def rectBorder [Zero R] (A : Matrix (Fin M) (Fin N) R) :
    Matrix (Fin (max M N)) (Fin (max M N)) R :=
  fun i j => if h : (i : ℕ) < M ∧ (j : ℕ) < N then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

variable {K : Type*} [Field K]

/-- **Existence of the rectangular LU factorization.** Let $A \in K^{M \times N}$ over a field $K$.
If the leading $(k+1) \times (k+1)$ block of $A$ is nonsingular for every $k$ with
$k + 1 \le \min(M, N)$, then $A$ has a rectangular LU factorization with $P = \min(M, N)$.

This is the existence statement of [golub2013matrix] §3.2.10: the factorization is "guaranteed
to exist if $A(1{:}k, 1{:}k)$ is nonsingular for $k = 1{:}\min\{m, n\}$". The proof borders $A$
with zeros to a square matrix of order $\max(M, N)$. This matrix has a block LU factorization
along the labelling $i \mapsto \min(i, \min(M, N))$, which has singletons followed by one
trailing block, and whose strict leading blocks are the leading blocks of $A$. The leading
$M \times P$ block of the lower factor and the leading $P \times N$ block of the upper factor
are the rectangular factors. -/
theorem exists_isRectLU_of_forall_det_ne_zero {A : Matrix (Fin M) (Fin N) K}
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
  refine ⟨_, _, isRectLU_submatrix_of_mul_eq h.mul_eq (le_max_left M N) (le_max_right M N)
    ((min_le_left M N).trans (le_max_left M N)) (fun i j => ?_) (fun i j hij => ?_)
    (fun i j hij => ?_) (fun i j hij => ?_) (fun i j r hr => ?_)⟩
  · rw [rectBorder, dite_eq_left_of_eq_true (eq_true ⟨i.2, j.2⟩)]
    rfl
  · exact h.isBlockUnitLowerTriangular.blockTriangular (by
      simp only [Function.comp_apply, OrderDual.toDual_lt_toDual, b, Fin.val_castLE]; omega)
  · change L ⟨i, _⟩ ⟨j, _⟩ = 1
    rw [show (⟨j, _⟩ : Fin (max M N)) = ⟨i, by omega⟩ from Fin.ext hij.symm]
    exact (h.isBlockUnitLowerTriangular.apply_eq_one_of_eq _ _ rfl).trans (one_apply_eq _)
  · exact h.blockTriangular (by simp only [b, Fin.val_castLE]; omega)
  · by_cases hi : (i : ℕ) < p
    · rw [h.isBlockUnitLowerTriangular.blockTriangular (by
        simp only [Function.comp_apply, OrderDual.toDual_lt_toDual, b, Fin.val_castLE]; omega),
        zero_mul]
    · rw [h.blockTriangular (by simp only [b, Fin.val_castLE]; omega), mul_zero]

end RectLU

/-! ### The $LDM^T$ and $LDL^T$ factorizations -/

section LDM

variable [LinearOrder n] [Fintype n]

/-- An **$LDM^T$ factorization** of a square matrix $A$ indexed by a finite linear order is a triple
$(L, D, M)$ such that $L$ and $M$ are unit lower triangular, $D$ is diagonal, and
$$L D M^T = A.$$

This is the factorization of [quarteroni2000numerical] §3.4.1. The case $M = L$ is the $LDL^T$
factorization of §3.4.2. -/
structure IsLDM [Semiring R] (A L D M : Matrix n n R) : Prop where
  /-- The left factor $L$ is unit lower triangular. -/
  isUnitLowerTriangular_left : L.IsUnitLowerTriangular
  /-- The middle factor $D$ is diagonal. -/
  isDiag : D.IsDiag
  /-- The right factor $M$, before transposition, is unit lower triangular. -/
  isUnitLowerTriangular_right : M.IsUnitLowerTriangular
  /-- The factors multiply to $A$: $L D M^T = A$. -/
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

/-- An $LDM^T$ factorization $A = L D M^T$ gives the LU factorization $A = L (D M^T)$. -/
theorem IsLDM.isLU [Semiring R] {A L D M : Matrix n n R} (h : IsLDM A L D M) :
    IsLU A L (D * Mᵀ) :=
  ⟨h.isUnitLowerTriangular_left,
    h.isDiag.isUpperTriangular.mul
      h.isUnitLowerTriangular_right.isLowerTriangular.transpose_isUpperTriangular,
    by rw [← Matrix.mul_assoc, h.mul_eq]⟩

variable {K : Type*} [Field K]

/-- **Theorem 3.5** of [quarteroni2000numerical], in the generality of [golub2013matrix] Theorem
4.1.3. Let $A$ be a square matrix over a field, indexed by a finite linear order. If every
strict leading principal submatrix $A_{< k}$ is nonsingular, then $A$ has a unique $LDM^T$
factorization.

The matrix $A$ itself may be singular, and then the last pivot vanishes. The source says "all
the principal minors", but its proof uses only the leading ones. The proof takes the LU
factorization $A = LU$, $D = \operatorname{diag}(u_{ii})$ and $M^T = D^{-1} U$ off the diagonal.
Every pivot except the last is nonzero by `Matrix.IsLU.diag_upper_ne_zero_of_lt`, and a
vanishing last pivot comes with a zero last row of $U$. Uniqueness follows from the uniqueness
of the LU factorization, since $L (D M^T)$ is an LU factorization. -/
theorem existsUnique_isLDM {A : Matrix n n K}
    (hA : A.HasUnitStrictLeadingPrincipalSubmatrices) :
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

/-- **The $LDL^T$ factorization.** Let $A$ be a symmetric square matrix over a field, indexed by a
finite linear order, such that every strict leading principal submatrix $A_{< k}$ is
nonsingular. If $A = L D M^T$ is an $LDM^T$ factorization, then $M = L$.

This is §3.4.2 of [quarteroni2000numerical]. Transposition of $A = L D M^T$ gives a second
$LDM^T$ factorization $A = M D L^T$, and the factorization is unique. -/
theorem IsLDM.eq_of_isSymm {A L D M : Matrix n n K} (h : IsLDM A L D M) (hs : A.IsSymm)
    (hA : A.HasUnitStrictLeadingPrincipalSubmatrices) : M = L := by
  have h' : IsLDM A M D L := ⟨h.isUnitLowerTriangular_right, h.isDiag,
    h.isUnitLowerTriangular_left, by
      rw [← hs.eq, ← h.mul_eq, transpose_mul, transpose_mul, transpose_transpose,
        h.isDiag.isSymm.eq, Matrix.mul_assoc]⟩
  obtain ⟨⟨L₀, D₀, M₀⟩, -, huniq⟩ := existsUnique_isLDM hA
  have h₁ := huniq (L, D, M) h
  have h₂ := huniq (M, D, L) h'
  exact (congrArg Prod.fst h₂).trans (congrArg Prod.fst h₁).symm

/-- Let $K$ be a partially ordered field with the trivial star operation, and let $A$ be a square
matrix over $K$ indexed by a finite linear order. If $A = L D L^T$ is an $LDL^T$ factorization
and $A$ is positive definite, then $d_{ii} > 0$ for every $i$.

This follows §3.4.2 of [quarteroni2000numerical]. The matrix $D = L^{-1} A L^{-T}$ is congruent
to $A$, hence positive definite, and the diagonal of a positive definite matrix is positive.
With the trivial star, the transpose $L^T$ is the conjugate transpose $L^H$. -/
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

/-- For an index $p$ and a function $f$ on the indices with values in a commutative monoid,
$\sum_j f(j) = f(p) + \sum_{j \neq p} f(j)$. -/
theorem sum_eq_add_sum_subtype_ne {M : Type*} [AddCommMonoid M] (p : n) (f : n → M) :
    ∑ j, f j = f p + ∑ j : {j // j ≠ p}, f j :=
  Fintype.sum_eq_add_sum_subtype_ne f p

/-- The unit lower factor of $A$ bordered from the lower factor $L'$ of the Schur complement of $A$
at the pivot $p$. Its row $p$ is the unit row $e_p^T$, its entry in column $p$ and row
$i \neq p$ is the multiplier $a_{ip} / a_{pp}$, and its other entries are those of $L'$.

When $a_{pp} = 0$, the multipliers are $0$, by the Lean convention $x / 0 = 0$. -/
noncomputable def luLowerOfSchur (A : Matrix n n K) (p : n)
    (L' : Matrix {i // i ≠ p} {i // i ≠ p} K) : Matrix n n K :=
  of fun i j =>
    if hi : i = p then (if j = p then 1 else 0)
    else if hj : j = p then A i p / A p p else L' ⟨i, hi⟩ ⟨j, hj⟩

/-- The upper factor of $A$ bordered from the upper factor $U'$ of the Schur complement of $A$ at
the pivot $p$. Its row $p$ is row $p$ of $A$, its other entries in column $p$ are zero, and its
other entries are those of $U'$. -/
noncomputable def luUpperOfSchur (A : Matrix n n K) (p : n)
    (U' : Matrix {i // i ≠ p} {i // i ≠ p} K) : Matrix n n K :=
  of fun i j => if hi : i = p then A p j else if hj : j = p then 0 else U' ⟨i, hi⟩ ⟨j, hj⟩

/-- **One step of Gaussian elimination as a factorization step, with a zero pivot column allowed.**
Let $A$ be a square matrix over a field, indexed by a finite linear order with first index $p$.
Suppose that $a_{pp} \neq 0$ or the whole column $p$ of $A$ is zero. Let $S$ be the Schur
complement of $A$ at $p$, with the entries $a_{ij} - a_{ip} a_{pp}^{-1} a_{pj}$ for
$i, j \neq p$, and let $S = L' U'$ be an LU factorization. Then $A = L U$ is an LU
factorization, with $L$ = `Matrix.luLowerOfSchur A p L'` and $U$ =
`Matrix.luUpperOfSchur A p U'`.

For a zero column the multipliers $a_{ip} / a_{pp}$ are $0$, by the Lean convention $x / 0 = 0$,
and this lets pivoting skip a zero column. The case $a_{pp} \neq 0$ is
`Matrix.isLU_luLowerOfSchur_luUpperOfSchur`. The Schur complement is
`Matrix.schurComplementSingle`. -/
theorem isLU_luLowerOfSchur_luUpperOfSchur' {A : Matrix n n K} {p : n} (hp : ∀ i, p ≤ i)
    (hpp : A p p = 0 → ∀ i, A i p = 0) {L' U' : Matrix {i // i ≠ p} {i // i ≠ p} K}
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
    rw [Matrix.mul_apply, sum_eq_add_sum_subtype_ne p]
    rcases eq_or_ne i p with hi | hi
    · subst hi
      simp [hLpp, hLpx, hUpj]
    rcases eq_or_ne j p with hj | hj
    · rcases eq_or_ne (A p p) 0 with h0 | h0
      · subst hj
        simp [hLxp i hi, hUpj, hUxp, hpp h0]
      · subst hj
        simp [hLxp i hi, hUpj, hUxp, div_mul_cancel₀ _ h0]
    have hS := congrFun (congrFun h.mul_eq ⟨i, hi⟩) ⟨j, hj⟩
    rw [Matrix.mul_apply, schurComplementSingle_apply] at hS
    simp only [hLxp i hi, hUpj, hLxx i hi, hUxj _ j hj]
    rw [hS, div_eq_mul_inv]
    ring

/-- **One step of Gaussian elimination as a factorization step.** Let $A$ be a square matrix over a
field, indexed by a finite linear order with first index $p$, and suppose that $a_{pp} \neq 0$.
Let $S$ be the Schur complement of $A$ at $p$, with the entries
$a_{ij} - a_{ip} a_{pp}^{-1} a_{pj}$ for $i, j \neq p$, and let $S = L' U'$ be an LU
factorization. Then $A = L U$ is an LU factorization, with $L$ = `Matrix.luLowerOfSchur A p L'`
and $U$ = `Matrix.luUpperOfSchur A p U'`.

This is the case "if $A_{11}$ were a scalar" of [quarteroni2000numerical] §3.8.1. -/
theorem isLU_luLowerOfSchur_luUpperOfSchur {A : Matrix n n K} {p : n} (hp : ∀ i, p ≤ i)
    (hpp : A p p ≠ 0) {L' U' : Matrix {i // i ≠ p} {i // i ≠ p} K}
    (h : IsLU (A.schurComplementSingle p) L' U') :
    IsLU A (luLowerOfSchur A p L') (luUpperOfSchur A p U') :=
  isLU_luLowerOfSchur_luUpperOfSchur' hp (fun h0 => absurd h0 hpp) h

/-- Existence of the LU factorization under row diagonal dominance, for matrices with $N$ indices.
Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be a square matrix over
$\mathbb{K}$ indexed by a linear order with $N$ elements. If $A$ is nonsingular and weakly
diagonally dominant by rows, then $A$ has an LU factorization.

The proof is by induction on $N$. The Schur complement of $A$ at the first index is again
nonsingular and weakly diagonally dominant by rows, so it has an LU factorization, and
`Matrix.isLU_luLowerOfSchur_luUpperOfSchur` extends it to $A$. -/
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

/-- **Property 3.2** of [quarteroni2000numerical], for rows. Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $A$ be a square matrix over $\mathbb{K}$ indexed by a finite linear order.
If $A$ is nonsingular and weakly diagonally dominant by rows, that is,
$\sum_{j \neq i} |a_{ij}| \le |a_{ii}|$ for every $i$, then $A$ has an LU factorization.

This is also Theorem 9.9 of [higham2002accuracy]. The statement of the source does not assume
that $A$ is nonsingular, and the assumption is needed: the matrix
$\begin{bmatrix} 0 & 0 \\ 1 & 1 \end{bmatrix}$ is weakly diagonally dominant by rows and has no
LU factorization with unit lower triangular $L$, because $u_{11} = 0$ forces
$l_{21} \cdot 0 = 1$. -/
theorem exists_isLU_of_isDiagDominant {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜} (hu : IsUnit A)
    (hA : A.IsDiagDominant) : ∃ L U, IsLU A L U :=
  exists_isLU_of_isDiagDominant_of_card _ A rfl hu hA

/-- Existence of the LU factorization under column diagonal dominance, for matrices with $N$
indices. Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be a square matrix over
$\mathbb{K}$ indexed by a linear order with $N$ elements. If $A$ is nonsingular and weakly
diagonally dominant by columns, then $A$ has an LU factorization $A = LU$ with $|l_{ij}| \le 1$
for all $i$ and $j$.

The proof is by induction on $N$, and carries the bound on $L$ through the induction. The
multipliers $a_{ip} / a_{pp}$ have modulus at most $1$ because the pivot column is diagonally
dominant. -/
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

/-- **Property 3.2** of [quarteroni2000numerical], for columns. Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $A$ be a square matrix over $\mathbb{K}$ indexed by a finite linear order.
If $A$ is nonsingular and weakly diagonally dominant by columns, that is,
$\sum_{i \neq j} |a_{ij}| \le |a_{jj}|$ for every $j$, then $A$ has an LU factorization $A = LU$
with $|l_{ij}| \le 1$ for all $i$ and $j$.

This is also Theorem 9.9 of [higham2002accuracy]. -/
theorem exists_isLU_of_isColDiagDominant {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}
    (hu : IsUnit A) (hA : A.IsColDiagDominant) : ∃ L U, IsLU A L U ∧ ∀ i j, ‖L i j‖ ≤ 1 :=
  exists_isLU_of_isColDiagDominant_of_card _ A rfl hu hA

end DiagDominant

/-! ### Bands and the envelope -/

section Band

variable [LinearOrder n] [Fintype n]

/-- **Property 3.4** of [quarteroni2000numerical], upper bandwidth. Let $A = LU$ be an LU
factorization over a ring. If $A$ has upper bandwidth $q$, then $U$ has upper bandwidth $q$. On
`Fin N` this means: if $a_{ij} = 0$ for $j > i + q$, then $u_{ij} = 0$ for $j > i + q$.

No hypothesis beyond the factorization is needed. The entry
$u_{ij} = a_{ij} - \sum_{r < i} l_{ir} u_{rj}$ vanishes by induction on $i$ whenever $a_{ij}$
vanishes. The bandwidth is `Matrix.HasUpperBandwidth`. -/
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

/-- **Property 3.4** of [quarteroni2000numerical], lower bandwidth. Let $A = LU$ be an LU
factorization over a field, and suppose that every strict leading principal submatrix $A_{< k}$
is nonsingular. If $A$ has lower bandwidth $p$, then $L$ has lower bandwidth $p$. On `Fin N`
this means: if $a_{ij} = 0$ for $i > j + p$, then $l_{ij} = 0$ for $i > j + p$.

The claim fails without the nonsingularity. The matrix $D = \begin{bmatrix} 0 & 1 \\ 0 & 2
\end{bmatrix}$ of Example 3.3 of [quarteroni2000numerical] is upper triangular, and it factors
as $D = L_\beta U_\beta$ with $L_\beta = \begin{bmatrix} 1 & 0 \\ \beta & 1 \end{bmatrix}$ for
every $\beta$. The bandwidth is `Matrix.HasLowerBandwidth`. -/
theorem IsLU.hasLowerBandwidth {A L U : Matrix n n K} (h : IsLU A L U)
    (hA' : A.HasUnitStrictLeadingPrincipalSubmatrices) {p : ℕ}
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

/-- The **lower envelope** of a square matrix $A$ indexed by a linear order is the set of the
positions $(i, j)$ with $j < i$ such that $a_{i j_0} \neq 0$ for some $j_0 \le j$. These are the
strictly lower positions of row $i$ from its first nonzero entry to the diagonal.

This is (3.59) of [quarteroni2000numerical]. On `Fin N` it is the set
$\{(i, j) : 0 < i - j \le m_i(A)\}$ with $m_i(A) = i - \min\{j < i : a_{ij} \neq 0\}$. A row
whose strictly lower part vanishes contributes no position. -/
def envelope [Zero R] (A : Matrix n n R) : Set (n × n) :=
  {ij | ij.2 < ij.1 ∧ ∃ j₀ ≤ ij.2, A ij.1 j₀ ≠ 0}

/-- Let $A = LU$ be an LU factorization over a field such that every strict leading principal
submatrix $A_{< k}$ is nonsingular. Let $j < i$, and suppose that $a_{ir} = 0$ for every
$r \le j$. Then $l_{ij} = 0$.

The proof is by induction on the column: $l_{ij} u_{jj} = a_{ij} - \sum_{r < j} l_{ir} u_{rj} =
0$, and $u_{jj} \neq 0$. -/
theorem IsLU.lower_apply_eq_zero_of_forall_le {A L U : Matrix n n K} (h : IsLU A L U)
    (hA' : A.HasUnitStrictLeadingPrincipalSubmatrices) {i j : n} (hij : j < i)
    (hz : ∀ r ≤ j, A i r = 0) : L i j = 0 := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
  have hU := h.diag_upper_ne_zero_of_lt (hA' i) hij
  have key := h.lower_apply_mul_diag_eq hij
  rw [hz j le_rfl, zero_sub, Finset.sum_eq_zero fun r hr => ?_, neg_zero] at key
  · exact (mul_eq_zero.1 key).resolve_right hU
  · have hr' := (mem_filter.1 hr).2
    rw [ih r hr' (hr'.trans hij) fun r' hr'' => hz r' (hr''.trans hr'.le), zero_mul]

/-- **Equation (3.60)** of [quarteroni2000numerical]. Let $A = LU$ be an LU factorization over a
field such that every strict leading principal submatrix $A_{< k}$ is nonsingular. Then $L$ and
$A$ have the same lower envelope.

So the factorization creates no fill-in outside the envelope, and no position on the boundary of
the envelope is lost. Before the first nonzero entry $a_{i j_0}$ of a row, every $l_{ir}$
vanishes by `Matrix.IsLU.lower_apply_eq_zero_of_forall_le`, and at $j_0$ itself
$l_{i j_0} u_{j_0 j_0} = a_{i j_0} \neq 0$. For a symmetric positive definite $A$ with Cholesky
factor $H$, the matrix $H^T = L D^{1/2}$ has the pattern of $L$, and this gives the statement
$E(A) = E(H + H^T)$ of the source. -/
theorem IsLU.envelope_eq {A L U : Matrix n n K} (h : IsLU A L U)
    (hA' : A.HasUnitStrictLeadingPrincipalSubmatrices) : L.envelope = A.envelope := by
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

/-- The block LU factorization with two blocks is the Schur complement factorization. Let $A =
\begin{bmatrix} B & E \\ F & C \end{bmatrix}$ over a field, with $B$ nonsingular, and let
$S = C - F B^{-1} E$. Then
$$A = \begin{bmatrix} I & 0 \\ F B^{-1} & I \end{bmatrix} \begin{bmatrix} B & E \\ 0 & S
  \end{bmatrix}$$
is a block LU factorization along the labelling with the label $0$ on the first block and $1$ on
the second.

The identity is `Matrix.fromBlocks_eq_mul_fromBlocks_schurComplement`. The display of
[quarteroni2000numerical] §3.8.1 with $A_{11} = L_{11} D_1 R_{11}$ is this identity with $B$
factored again. -/
theorem isBlockLU_fromBlocks_schurComplement {B : Matrix m m K} {E : Matrix m o K}
    {F : Matrix o m K} {C : Matrix o o K} (hB : IsUnit B) :
    IsBlockLU (Sum.elim (fun _ => (0 : ℕ)) fun _ => 1) (fromBlocks B E F C)
      (fromBlocks 1 0 (F * B⁻¹) 1) (fromBlocks B E 0 (fromBlocks B E F C).schurComplement) where
  isBlockUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · have hij' := OrderDual.toDual_lt_toDual.1 hij
      rcases i with i | i <;> rcases j with j | j <;> first | rfl | (exfalso; simp at hij')
    · rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply] at hij ⊢
  blockTriangular := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j <;> first | rfl | (exfalso; simp at hij)
  mul_eq := (fromBlocks_eq_mul_fromBlocks_schurComplement hB).symm

end TwoBlocks

/-! ### Tridiagonal matrices: the Thomas algorithm -/

section Thomas

variable {K : Type*} [Field K]

/-- The **tridiagonal matrix** of order $N$ with the diagonals $a$, $b$ and $c$, given by sequences
indexed by $\mathbb{N}$: it has $a_i$ at $(i, i)$, $b_i$ at $(i, i - 1)$ on the subdiagonal,
$c_i$ at $(i, i + 1)$ on the superdiagonal, and zeros elsewhere. The values $b_0$ and $c_{N-1}$
are not used.

This is the matrix of [quarteroni2000numerical] §3.7.1, indexed from $0$. It is
`Matrix.tridiagonalOf` of the shifted sequences, by `Matrix.tridiagonalOfNat_eq_tridiagonalOf`. -/
def tridiagonalOfNat [Zero R] (a b c : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  of fun i j =>
    if (i : ℕ) = j then a i else if (j : ℕ) + 1 = i then b i else if (i : ℕ) + 1 = j then c i
    else 0

/-- The tridiagonal matrix of order $N + 1$ with the diagonals $a$, $b$ and $c$ is
`Matrix.tridiagonalOf` with the subdiagonal $(b_1, \dots, b_N)$, the diagonal
$(a_0, \dots, a_N)$ and the superdiagonal $(c_0, \dots, c_{N-1})$. -/
theorem tridiagonalOfNat_eq_tridiagonalOf [Zero R] (a b c : ℕ → R) (N : ℕ) :
    tridiagonalOfNat a b c (N + 1) =
      tridiagonalOf (fun i : Fin N => b (i + 1)) (fun i => a i) fun i : Fin N => c i := by
  ext i j
  simp only [tridiagonalOfNat, tridiagonalOf, of_apply]
  split_ifs <;> first | rfl | omega | congr 1

/-- Let $T$ be the tridiagonal matrix with the diagonals $a$, $b$ and $c$. Then $t_{ij} x_j$ is
$a_i x_i$ if $j = i$, $b_i x_{i-1}$ if $j = i - 1$, $c_i x_{i+1}$ if $j = i + 1$, and $0$
otherwise, written as a sum of the three cases. -/
theorem tridiagonalOfNat_apply_mul_eq [NonUnitalNonAssocSemiring R] (a b c : ℕ → R) {N : ℕ}
    (x : Fin N → R) (i j : Fin N) :
    tridiagonalOfNat a b c N i j * x j =
      (if j = i then a i * x i else 0) +
        (if h : (j : ℕ) + 1 = i then b i * x ⟨i - 1, by omega⟩ else 0) +
        (if h : (j : ℕ) = i + 1 then c i * x ⟨i + 1, by omega⟩ else 0) := by
  by_cases hij : j = i
  · subst hij
    simp [tridiagonalOfNat]
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h.symm)
    simp only [tridiagonalOfNat, of_apply, hij', ite_false, hij]
    split_ifs <;> (try simp only [zero_add, add_zero]) <;>
      first | omega | (congr 2; exact Fin.ext (by simp; omega)) | simp

/-- Let $T$ be the tridiagonal matrix with the diagonals $a$, $b$ and $c$. Then $x_i t_{ij}$ is
$x_j a_j$ if $i = j$, $x_{j+1} b_{j+1}$ if $i = j + 1$, $x_{j-1} c_{j-1}$ if $i = j - 1$, and
$0$ otherwise, written as a sum of the three cases. -/
theorem mul_tridiagonalOfNat_apply_eq [NonUnitalNonAssocSemiring R] (a b c : ℕ → R) {N : ℕ}
    (x : Fin N → R) (i j : Fin N) :
    x i * tridiagonalOfNat a b c N i j =
      (if i = j then x j * a j else 0) +
        (if h : (i : ℕ) = j + 1 then x ⟨j + 1, by omega⟩ * b (j + 1) else 0) +
        (if h : (i : ℕ) + 1 = j then x ⟨j - 1, by omega⟩ * c (j - 1) else 0) := by
  by_cases hij : i = j
  · subst hij
    simp [tridiagonalOfNat]
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp only [tridiagonalOfNat, of_apply, hij', ite_false, hij]
    split_ifs <;> (try simp only [zero_add, add_zero]) <;>
      first | omega | (congr 2 <;> first | omega | exact Fin.ext (by simp; omega)) | simp

/-- **The three-term formula.** Let $T$ be the tridiagonal matrix of order $N$ with the diagonals
$a$, $b$ and $c$. Then for every $i < N$,
$$(T x)_i = b_i x_{i-1} + a_i x_i + c_i x_{i+1},$$
where the term $b_i x_{i-1}$ is absent for $i = 0$ and the term $c_i x_{i+1}$ is absent for
$i = N - 1$. -/
theorem tridiagonalOfNat_mulVec [NonUnitalNonAssocSemiring R] (a b c : ℕ → R) {N : ℕ}
    (x : Fin N → R) (i : Fin N) :
    (tridiagonalOfNat a b c N *ᵥ x) i =
      (if h : 0 < (i : ℕ) then b i * x ⟨i - 1, by omega⟩ else 0) + a i * x i +
        (if h : (i : ℕ) + 1 < N then c i * x ⟨i + 1, h⟩ else 0) := by
  simp only [mulVec, dotProduct, tridiagonalOfNat_apply_mul_eq, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_dite_val_add_one_eq,
    sum_dite_val_eq_add_one]
  abel

/-- **The three-term formula for the action on the left.** Let $T$ be the tridiagonal matrix of
order $N$ with the diagonals $a$, $b$ and $c$. Then for every $j < N$,
$$(x^T T)_j = x_{j-1} c_{j-1} + x_j a_j + x_{j+1} b_{j+1},$$
where the first term is absent for $j = 0$ and the last term is absent for $j = N - 1$. -/
theorem tridiagonalOfNat_vecMul [NonUnitalNonAssocSemiring R] (a b c : ℕ → R) {N : ℕ}
    (x : Fin N → R) (j : Fin N) :
    (x ᵥ* tridiagonalOfNat a b c N) j =
      (if h : 0 < (j : ℕ) then x ⟨j - 1, by omega⟩ * c (j - 1) else 0) + x j * a j +
        (if h : (j : ℕ) + 1 < N then x ⟨j + 1, h⟩ * b (j + 1) else 0) := by
  simp only [vecMul, dotProduct, mul_tridiagonalOfNat_apply_eq, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_dite_val_add_one_eq,
    sum_dite_val_eq_add_one]
  abel

/-- The **pivots** $\alpha_i$ of the Thomas algorithm for the tridiagonal matrix with the diagonals
$a$, $b$ and $c$:
$$\alpha_0 = a_0, \qquad \alpha_{i+1} = a_{i+1} - \beta_{i+1} c_i, \qquad \beta_{i+1} =
  \frac{b_{i+1}}{\alpha_i}.$$

These are the recurrences (3.53) of [quarteroni2000numerical], indexed from $0$. If
$\alpha_i = 0$, then $\beta_{i+1} = 0$ and $\alpha_{i+1} = a_{i+1}$, by the Lean convention
$x / 0 = 0$. -/
noncomputable def thomasAlpha (a b c : ℕ → K) : ℕ → K
  | 0 => a 0
  | i + 1 => a (i + 1) - b (i + 1) / thomasAlpha a b c i * c i

/-- The **multipliers** $\beta_i$ of the Thomas algorithm: $\beta_0 = 0$ and
$\beta_{i+1} = b_{i+1} / \alpha_i$, where $\alpha_i$ are the pivots of `Matrix.thomasAlpha`.

These are the recurrences (3.53) of [quarteroni2000numerical]. The value $\beta_0 = 0$ is a
convention. If $\alpha_i = 0$, then $\beta_{i+1} = 0$, by the Lean convention $x / 0 = 0$. -/
noncomputable def thomasBeta (a b c : ℕ → K) : ℕ → K
  | 0 => 0
  | i + 1 => b (i + 1) / thomasAlpha a b c i

variable (a b c : ℕ → K)

/-- The first pivot of the Thomas algorithm is $\alpha_0 = a_0$. -/
@[simp]
theorem thomasAlpha_zero : thomasAlpha a b c 0 = a 0 := rfl

/-- The recurrence for the pivots of the Thomas algorithm:
$\alpha_{i+1} = a_{i+1} - \beta_{i+1} c_i$. -/
theorem thomasAlpha_succ (i : ℕ) :
    thomasAlpha a b c (i + 1) = a (i + 1) - thomasBeta a b c (i + 1) * c i := rfl

/-- The first multiplier of the Thomas algorithm is $\beta_0 = 0$, by convention. -/
@[simp]
theorem thomasBeta_zero : thomasBeta a b c 0 = 0 := rfl

/-- The recurrence for the multipliers of the Thomas algorithm: $\beta_{i+1} = b_{i+1} / \alpha_i$.
-/
theorem thomasBeta_succ (i : ℕ) : thomasBeta a b c (i + 1) = b (i + 1) / thomasAlpha a b c i := rfl

/-- The **lower factor** of the Thomas algorithm: the unit lower bidiagonal matrix of order $N$ with
the multipliers $\beta_i$ at the positions $(i, i - 1)$ of the subdiagonal. -/
noncomputable def thomasLower (N : ℕ) : Matrix (Fin N) (Fin N) K :=
  of fun i j => if i = j then 1 else if (j : ℕ) + 1 = i then thomasBeta a b c i else 0

/-- The **upper factor** of the Thomas algorithm: the upper bidiagonal matrix of order $N$ with the
pivots $\alpha_i$ on the diagonal and the entries $c_i$ of the tridiagonal matrix at the
positions $(i, i + 1)$ of the superdiagonal. -/
noncomputable def thomasUpper (N : ℕ) : Matrix (Fin N) (Fin N) K :=
  of fun i j => if i = j then thomasAlpha a b c i else if (i : ℕ) + 1 = j then c i else 0

/-- The **unit lower bidiagonal matrix** of order $N$ with the subdiagonal $\beta$: it has ones on
the diagonal, $\beta_i$ at $(i, i - 1)$, and zeros elsewhere.

This is the shape of the lower factor of the Thomas algorithm. The exact factor
`Matrix.thomasLower a b c N` is `Matrix.lowerBidiagonalOf (Matrix.thomasBeta a b c) N`, by
`Matrix.thomasLower_eq`. The factor computed by the Thomas algorithm in floating point is the
same matrix for the computed multipliers $\hat\beta$. -/
def lowerBidiagonalOf [Zero R] [One R] (β : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  of fun i j => if i = j then 1 else if (j : ℕ) + 1 = i then β i else 0

/-- The **upper bidiagonal matrix** of order $N$ with the diagonal $\alpha$ and the superdiagonal
$c$: it has $\alpha_i$ at $(i, i)$, $c_i$ at $(i, i + 1)$, and zeros elsewhere.

This is the shape of the upper factor of the Thomas algorithm. The exact factor
`Matrix.thomasUpper a b c N` is `Matrix.upperBidiagonalOf (Matrix.thomasAlpha a b c) c N`, by
`Matrix.thomasUpper_eq`. -/
def upperBidiagonalOf [Zero R] (α c : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  of fun i j => if i = j then α i else if (i : ℕ) + 1 = j then c i else 0

/-- The lower factor of the Thomas algorithm is the unit lower bidiagonal matrix of the multipliers
$\beta_i$. -/
theorem thomasLower_eq (N : ℕ) :
    thomasLower a b c N = lowerBidiagonalOf (thomasBeta a b c) N := rfl

/-- The upper factor of the Thomas algorithm is the upper bidiagonal matrix with the pivots
$\alpha_i$ on the diagonal and $c$ on the superdiagonal. -/
theorem thomasUpper_eq (N : ℕ) :
    thomasUpper a b c N = upperBidiagonalOf (thomasAlpha a b c) c N := rfl

/-- Left multiplication by the unit lower bidiagonal matrix $L_\beta$ adds $\beta_i$ times the
previous row: for a square matrix $M$ of order $N$,
$$(L_\beta M)_{ij} = m_{ij} + \beta_i m_{i-1,j} \quad \text{for } i > 0, \qquad (L_\beta
  M)_{0j} = m_{0j}.$$
-/
theorem lowerBidiagonalOf_mul_apply [NonAssocSemiring R] {N : ℕ} (β : ℕ → R)
    (M : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    (lowerBidiagonalOf β N * M) i j =
      M i j + if h : 0 < (i : ℕ) then β i * M ⟨i - 1, by omega⟩ j else 0 := by
  rw [Matrix.mul_apply]
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

/-- An entry $(i, j)$ of the upper bidiagonal matrix with $j \neq i$ and $j \neq i + 1$ is zero. -/
theorem upperBidiagonalOf_apply_eq_zero [Zero R] {N : ℕ} {α c : ℕ → R} {i j : Fin N}
    (h1 : (i : ℕ) ≠ j) (h2 : (i : ℕ) + 1 ≠ j) : upperBidiagonalOf α c N i j = 0 := by
  simp [upperBidiagonalOf, Fin.ext_iff, h1, h2]

/-- The lower factor of the Thomas algorithm is lower bidiagonal. -/
theorem isLowerBidiagonal_thomasLower (N : ℕ) : (thomasLower a b c N).IsLowerBidiagonal := by
  intro i j h
  simp only [thomasLower, of_apply, Fin.ext_iff]
  rcases h with h | ⟨k, hk⟩ <;> simp only [Fin.lt_def] at * <;> split_ifs <;> first | rfl | omega

/-- The upper factor of the Thomas algorithm is upper bidiagonal. -/
theorem isUpperBidiagonal_thomasUpper (N : ℕ) : (thomasUpper a b c N).IsUpperBidiagonal := by
  intro i j h
  simp only [thomasUpper, of_apply, Fin.ext_iff]
  rcases h with h | ⟨k, hk⟩ <;> simp only [Fin.lt_def] at * <;> split_ifs <;> first | rfl | omega

/-- Let $L$ and $U$ be the lower and the upper factors of the Thomas algorithm. Then $l_{ir} u_{rj}$
is $u_{ij}$ if $r = i$, $\beta_i u_{rj}$ if $r = i - 1$, and $0$ otherwise, written as a sum of
the two cases. -/
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

/-- **The Thomas algorithm.** Let $T$ be the tridiagonal matrix of order $N$ over a field with the
diagonals $a$, $b$ and $c$, and suppose that the pivot $\alpha_i$ is nonzero for every $i$ with
$i + 1 < N$. Then $T = LU$ is an LU factorization, where $L$ is the unit lower bidiagonal matrix
of the multipliers $\beta_i$, and $U$ is the upper bidiagonal matrix with the pivots $\alpha_i$
on the diagonal and $c$ on the superdiagonal.

This is §3.7.1 and (3.53) of [quarteroni2000numerical]. The condition on the pivots is
equivalent to the nonsingularity of the strict leading principal submatrices of $T$, by
`Matrix.IsLU.det_strictLeadingPrincipalSubmatrix`. The last pivot $\alpha_{N-1}$ may vanish. -/
theorem isLU_tridiagonal_thomas {N : ℕ} (hα : ∀ i, i + 1 < N → thomasAlpha a b c i ≠ 0) :
    IsLU (tridiagonalOfNat a b c N) (thomasLower a b c N) (thomasUpper a b c N) where
  isUnitLowerTriangular :=
    ⟨(isLowerBidiagonal_thomasLower a b c N).isLowerTriangular, fun i => by simp [thomasLower]⟩
  isUpperTriangular := (isUpperBidiagonal_thomasUpper a b c N).isUpperTriangular
  mul_eq := by
    ext i j
    simp only [Matrix.mul_apply, thomasLower_apply_mul_eq, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_dite_val_add_one_eq]
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

/-- The **reciprocal pivots** $\gamma_i$ of the division-free Thomas algorithm:
$$\gamma_0 = a_0^{-1}, \qquad \gamma_{i+1} = (a_{i+1} - b_{i+1} \gamma_i c_i)^{-1}.$$

This is the algorithm of [quarteroni2000numerical] §3.7.2, indexed from $0$. The inverse follows
the Lean convention $0^{-1} = 0$. The $\gamma_i$ are the reciprocals of the pivots $\alpha_i$,
by `Matrix.thomasGamma_eq_inv_thomasAlpha`. -/
noncomputable def thomasGamma (a b c : ℕ → K) : ℕ → K
  | 0 => (a 0)⁻¹
  | i + 1 => (a (i + 1) - b (i + 1) * thomasGamma a b c i * c i)⁻¹

/-- The reciprocal pivots are the reciprocals of the pivots: $\gamma_i = \alpha_i^{-1}$ for every
$i$.

No pivot needs to be nonzero, because both sides follow the Lean convention $0^{-1} = 0$. -/
theorem thomasGamma_eq_inv_thomasAlpha (i : ℕ) : thomasGamma a b c i = (thomasAlpha a b c i)⁻¹ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [thomasGamma, ih, thomasAlpha_succ, thomasBeta_succ, div_eq_mul_inv]

end Thomas

end Matrix
