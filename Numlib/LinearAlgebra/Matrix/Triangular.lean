/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Block`, beside `Matrix.IsUpperTriangular`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Defs
import Numlib.LinearAlgebra.Matrix.Block

/-!
# Triangular matrices and the triangular parts of a matrix

This file extends Mathlib's vocabulary of triangular matrices, `Matrix.IsUpperTriangular` and
`Matrix.IsLowerTriangular`, for square matrices indexed by any linearly ordered type. A square
matrix $A$ splits into its diagonal part $D$, its strictly lower part and its strictly upper part.
In the sign convention of the classical stationary iterations (Jacobi, Gauss–Seidel, SOR), this
splitting is $A = D - E - F$, where $-E$ is the strictly lower part and $-F$ is the strictly upper
part. The same splitting exists for a block labelling $\pi$ of the indices, as in (4.15) of
[saad2003iterative].

A triangular matrix over a field is nonsingular if and only if its diagonal has no zero entry, and
its inverse is triangular of the same kind. The diagonal of a product of triangular matrices is the
product of the diagonals. Hence unit triangular matrices, which have ones on the diagonal and are
the shapes of the factors of an LU factorization, are closed under products and inverses and have
determinant $1$. The spectrum of a triangular matrix is the set of its diagonal entries. The
presentation follows [quarteroni2000numerical] §1.6.2 and §3.2, and [golub2013matrix] §3.1.7.

## Main definitions

* `Matrix.strictLower`, `Matrix.strictUpper`, `Matrix.diagPart`: the strictly lower part, the
  strictly upper part and the diagonal part of a square matrix.
* `Matrix.blockDiagPart`, `Matrix.blockStrictLower`, `Matrix.blockStrictUpper`: the same three parts
  for a block labelling $\pi$ of the indices, that is, the entries with $\pi(i) = \pi(j)$,
  $\pi(j) < \pi(i)$ and $\pi(i) < \pi(j)$. For $\pi = \mathrm{id}$ they are the three parts above.
* `Matrix.IsUnitLowerTriangular`, `Matrix.IsUnitUpperTriangular`: lower or upper triangular with
  ones on the diagonal.

## Main results

* `Matrix.diagPart_add_strictLower_add_strictUpper`,
  `Matrix.diagPart_sub_neg_strictLower_sub_neg_strictUpper`: a matrix is the sum of its three parts,
  and $A = D - E - F$.
* `Matrix.blockDiagPart_add_blockStrictLower_add_blockStrictUpper`: the block form of the splitting,
  (4.15) of [saad2003iterative].
* `Matrix.isUnit_diagPart_iff`, `Matrix.inv_diagPart`: over a field, the diagonal part is invertible
  if and only if the diagonal has no zero entry, and its inverse is then the diagonal matrix of the
  inverses.
* `Matrix.IsUpperTriangular.isUnit_iff`, `Matrix.IsLowerTriangular.isUnit_iff`: over a field, a
  triangular matrix is nonsingular if and only if its diagonal has no zero entry.
* `Matrix.IsUpperTriangular.inv`, `Matrix.IsLowerTriangular.inv`: the inverse of a triangular matrix
  is triangular of the same kind.
* `Matrix.IsUpperTriangular.mul_apply_self`, `Matrix.IsLowerTriangular.mul_apply_self`: the diagonal
  of a product of two triangular matrices of the same kind is the product of the diagonals.
* `Matrix.IsUnitLowerTriangular.mul`, `Matrix.IsUnitLowerTriangular.inv`,
  `Matrix.IsUnitLowerTriangular.det_eq_one`: unit lower triangular matrices are closed under
  products and inverses and have determinant $1$. The upper versions also hold.
* `Matrix.IsUpperTriangular.isLowerTriangular_orderDual`,
  `Matrix.IsLowerTriangular.isUpperTriangular_orderDual`: a triangular matrix is triangular of the
  other kind for the reversed order of the indices.
* `Matrix.charpoly_of_isLowerTriangular`, `Matrix.IsUpperTriangular.spectrum_eq`,
  `Matrix.IsLowerTriangular.spectrum_eq`: the characteristic polynomial of a triangular matrix is
  $\prod_i (X - a_{ii})$, and over a field its spectrum is the set of its diagonal entries.
* `Matrix.IsUpperTriangular.mul_apply`, `Matrix.mul_transpose_apply_of_lower`,
  `Matrix.transpose_mul_apply_of_upper`, `Matrix.mul_mul_transpose_apply_of_isDiag`: the entries of
  the products $M N$, $G H^T$, $G^T H$ and $L D L^T$ of triangular matrices as sums over a
  restricted range of indices.
* `Matrix.IsUpperTriangular.apply_mul_sub_eq_of_commute`: the Parlett identity for commuting upper
  triangular matrices.
* `Matrix.BlockTriangular.toBlock_mul`, `Matrix.BlockTriangular.toBlock_pow`,
  `Matrix.BlockTriangular.toBlock_mul_eq_sum_Icc`: the diagonal blocks of products and powers of
  block triangular matrices, and the blocks of a product.
* `Matrix.IsUpperTriangular.eq_diagonal_of_mem_unitaryGroup`,
  `Matrix.IsLowerTriangular.eq_diagonal_of_mem_unitaryGroup`: a unitary triangular matrix is
  diagonal.

## Implementation notes

* Mathlib's `Matrix.BlockTriangular M b` unfolds to `b j < b i → M i j = 0`. So
  `BlockTriangular · id` is upper triangularity, and lower triangularity is
  `BlockTriangular · OrderDual.toDual`. For this reason `Matrix.strictLower_blockTriangular` and
  `Matrix.strictUpper_blockTriangular` use different order maps.
* The reading of a triangular matrix on the dual order `nᵒᵈ` makes backward substitution an instance
  of forward substitution in `Numlib.Direct.Substitution`.
* The inverse is Mathlib's `Matrix.inv`, which is $0$ for a singular matrix. So the results on the
  inverse of a triangular matrix need no hypothesis.
-/

namespace Matrix

variable {n R : Type*} [LinearOrder n]

/-! ### The triangular parts -/

section Parts

variable [Zero R]

/-- The **strictly lower triangular part** of a square matrix $A$: the matrix with the entries
$a_{ij}$ for $j < i$ and $0$ elsewhere. -/
def strictLower (A : Matrix n n R) : Matrix n n R := Matrix.of fun i j => if j < i then A i j else 0

/-- The **strictly upper triangular part** of a square matrix $A$: the matrix with the entries
$a_{ij}$ for $i < j$ and $0$ elsewhere. -/
def strictUpper (A : Matrix n n R) : Matrix n n R := Matrix.of fun i j => if i < j then A i j else 0

/-- The **diagonal part** of a square matrix $A$: the diagonal matrix $\operatorname{diag}(a_{ii})$.
-/
def diagPart [DecidableEq n] (A : Matrix n n R) : Matrix n n R := Matrix.diagonal A.diag

/-- The entry $(i, j)$ of the strictly lower part of $A$ is $a_{ij}$ if $j < i$, and $0$ otherwise.
-/
@[simp]
theorem strictLower_apply (A : Matrix n n R) (i j : n) :
    strictLower A i j = if j < i then A i j else 0 := rfl

/-- The entry $(i, j)$ of the strictly upper part of $A$ is $a_{ij}$ if $i < j$, and $0$ otherwise.
-/
@[simp]
theorem strictUpper_apply (A : Matrix n n R) (i j : n) :
    strictUpper A i j = if i < j then A i j else 0 := rfl

omit [LinearOrder n] in
/-- The entry $(i, j)$ of the diagonal part of $A$ is $a_{ii}$ if $i = j$, and $0$ otherwise. -/
@[simp]
theorem diagPart_apply [DecidableEq n] (A : Matrix n n R) (i j : n) :
    diagPart A i j = if i = j then A i i else 0 := diagonal_apply _ _ _

/-- The strictly lower part of a square matrix is lower triangular, that is, block triangular for
`OrderDual.toDual`.

The implementation notes of the module explain why the order map is not `id`. -/
theorem strictLower_blockTriangular (A : Matrix n n R) :
    (strictLower A).BlockTriangular OrderDual.toDual := fun _ _ h => by
  simp [asymm (OrderDual.toDual_lt_toDual.mp h)]

/-- The strictly upper part of a square matrix is upper triangular, that is, block triangular for
`id`. -/
theorem strictUpper_blockTriangular (A : Matrix n n R) :
    (strictUpper A).BlockTriangular id := fun i j h => by
  simp only [strictUpper_apply, ite_eq_right_iff]
  exact fun h' => absurd h' (asymm h)

/-- The transpose of the strictly lower part of $A$ is the strictly upper part of $A^T$. -/
theorem strictLower_transpose (A : Matrix n n R) : (strictLower A)ᵀ = strictUpper Aᵀ := by
  ext i j
  simp

/-- The transpose of the strictly upper part of $A$ is the strictly lower part of $A^T$. -/
theorem strictUpper_transpose (A : Matrix n n R) : (strictUpper A)ᵀ = strictLower Aᵀ := by
  ext i j
  simp

omit [LinearOrder n] in
/-- The transpose of the diagonal part of $A$ is the diagonal part of $A^T$. -/
theorem diagPart_transpose [DecidableEq n] (A : Matrix n n R) : (diagPart A)ᵀ = diagPart Aᵀ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

end Parts

/-- Every square matrix $A$ is the sum of its diagonal part $D$, its strictly lower part $L$ and its
strictly upper part $U$:
$$A = D + L + U.$$
The three parts partition the entries of $A$. -/
theorem diagPart_add_strictLower_add_strictUpper [DecidableEq n] [AddCommMonoid R]
    (A : Matrix n n R) : diagPart A + strictLower A + strictUpper A = A := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, asymm h]
  · simp
  · simp [h, h.ne', asymm h]

/-- The splitting $A = D - E - F$ of the classical stationary iterations, where $D$ is the diagonal
part of $A$, $E$ is the negative of the strictly lower part and $F$ is the negative of the
strictly upper part. -/
theorem diagPart_sub_neg_strictLower_sub_neg_strictUpper [DecidableEq n] [AddCommGroup R]
    (A : Matrix n n R) : diagPart A - (-strictLower A) - (-strictUpper A) = A := by
  rw [sub_neg_eq_add, sub_neg_eq_add, diagPart_add_strictLower_add_strictUpper]

/-! ### The block parts for a block labelling -/

section BlockParts

variable {m ι : Type*}

section Zero

variable [Zero R]

/-- The **block diagonal part** of a square matrix $A$ for a block labelling $\pi$ of the indices:
the matrix with the entries $a_{ij}$ for $\pi(i) = \pi(j)$ and $0$ elsewhere. This is the matrix
$D$ of (4.15) of [saad2003iterative]. -/
def blockDiagPart [DecidableEq ι] (π : m → ι) (A : Matrix m m R) : Matrix m m R :=
  Matrix.of fun i j => if π i = π j then A i j else 0

/-- The entry $(i, j)$ of the block diagonal part of $A$ is $a_{ij}$ if $\pi(i) = \pi(j)$, and $0$
otherwise. -/
@[simp]
theorem blockDiagPart_apply [DecidableEq ι] (π : m → ι) (A : Matrix m m R) (i j : m) :
    blockDiagPart π A i j = if π i = π j then A i j else 0 := rfl

/-- The **strictly block lower part** of a square matrix $A$ for a block labelling $\pi$ of the
indices: the matrix with the entries $a_{ij}$ for $\pi(j) < \pi(i)$ and $0$ elsewhere. This is
the matrix $-E$ of (4.15) of [saad2003iterative]. -/
def blockStrictLower [LinearOrder ι] (π : m → ι) (A : Matrix m m R) : Matrix m m R :=
  Matrix.of fun i j => if π j < π i then A i j else 0

/-- The entry $(i, j)$ of the strictly block lower part of $A$ is $a_{ij}$ if $\pi(j) < \pi(i)$, and
$0$ otherwise. -/
@[simp]
theorem blockStrictLower_apply [LinearOrder ι] (π : m → ι) (A : Matrix m m R) (i j : m) :
    blockStrictLower π A i j = if π j < π i then A i j else 0 := rfl

/-- The **strictly block upper part** of a square matrix $A$ for a block labelling $\pi$ of the
indices: the matrix with the entries $a_{ij}$ for $\pi(i) < \pi(j)$ and $0$ elsewhere. This is
the matrix $-F$ of (4.15) of [saad2003iterative]. -/
def blockStrictUpper [LinearOrder ι] (π : m → ι) (A : Matrix m m R) : Matrix m m R :=
  Matrix.of fun i j => if π i < π j then A i j else 0

/-- The entry $(i, j)$ of the strictly block upper part of $A$ is $a_{ij}$ if $\pi(i) < \pi(j)$, and
$0$ otherwise. -/
@[simp]
theorem blockStrictUpper_apply [LinearOrder ι] (π : m → ι) (A : Matrix m m R) (i j : m) :
    blockStrictUpper π A i j = if π i < π j then A i j else 0 := rfl

/-- For the identity labelling, the strictly block lower part is the strictly lower part. -/
@[simp]
theorem blockStrictLower_id (A : Matrix n n R) : blockStrictLower id A = strictLower A := rfl

/-- For the identity labelling, the strictly block upper part is the strictly upper part. -/
@[simp]
theorem blockStrictUpper_id (A : Matrix n n R) : blockStrictUpper id A = strictUpper A := rfl

omit [LinearOrder n] in
/-- For the identity labelling, the block diagonal part is the diagonal part. -/
@[simp]
theorem blockDiagPart_id [DecidableEq n] (A : Matrix n n R) : blockDiagPart id A = diagPart A := by
  ext i j
  rw [blockDiagPart_apply, diagPart, Matrix.diagonal_apply]
  split <;> simp_all [Matrix.diag]

end Zero

/-- **Block splitting.** For a block labelling $\pi$ of the indices, a square matrix $A$ is the sum
of its block diagonal part, its strictly block lower part and its strictly block upper part. In
the notation of (4.15) of [saad2003iterative] this is $A = D - E - F$. -/
theorem blockDiagPart_add_blockStrictLower_add_blockStrictUpper [LinearOrder ι] [AddCommMonoid R]
    (π : m → ι) (A : Matrix m m R) :
    blockDiagPart π A + blockStrictLower π A + blockStrictUpper π A = A := by
  ext i j
  simp only [Matrix.add_apply, blockDiagPart_apply, blockStrictLower_apply,
    blockStrictUpper_apply]
  rcases lt_trichotomy (π i) (π j) with h | h | h
  · simp [h, h.ne, asymm h]
  · simp [h]
  · simp [h, h.ne', asymm h]

end BlockParts

section DiagPart

variable {𝕜 : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

omit [LinearOrder n] in
/-- Over a field, the diagonal part of a square matrix $A$ is invertible if and only if
$a_{ii} \neq 0$ for every $i$. Every classical splitting assumes this condition. -/
theorem isUnit_diagPart_iff (A : Matrix n n 𝕜) : IsUnit (diagPart A) ↔ ∀ i, A i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, diagPart, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp [Matrix.diag]

omit [LinearOrder n] in
/-- Over a field, if the diagonal part of $A$ is invertible, then its inverse is
$\operatorname{diag}(a_{ii}^{-1})$.

Entrywise computations with a splitting use this form. The lemma `Matrix.inv_diagonal` inverts
the diagonal in the product ring, and so gives $0$ when one diagonal entry is zero. -/
theorem inv_diagPart {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    (diagPart A)⁻¹ = diagonal fun i => (A i i)⁻¹ := by
  have hd := (isUnit_diagPart_iff A).mp h
  refine inv_eq_left_inv ?_
  rw [diagPart, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg _ (funext fun i => inv_mul_cancel₀ (hd i))

end DiagPart

section MulVec

/-! ### Rows of the triangular parts -/

open Finset

variable [Fintype n] [NonUnitalNonAssocSemiring R]

omit [LinearOrder n] in
/-- The entry $i$ of $D v$, for the diagonal part $D$ of $A$, is $a_{ii} v_i$. -/
theorem diagPart_mulVec_apply [DecidableEq n] (A : Matrix n n R) (v : n → R) (i : n) :
    (diagPart A *ᵥ v) i = A i i * v i := by
  rw [diagPart, mulVec_diagonal]
  rfl

/-- The entry $i$ of $L v$, for the strictly lower part $L$ of $A$, is $\sum_{j < i} a_{ij} v_j$. -/
theorem strictLower_mulVec_apply (A : Matrix n n R) (v : n → R) (i : n) :
    (strictLower A *ᵥ v) i = ∑ j ∈ univ.filter (· < i), A i j * v j := by
  simp [mulVec, dotProduct, sum_filter, ite_mul]

/-- The entry $i$ of $U v$, for the strictly upper part $U$ of $A$, is $\sum_{j > i} a_{ij} v_j$. -/
theorem strictUpper_mulVec_apply (A : Matrix n n R) (v : n → R) (i : n) :
    (strictUpper A *ᵥ v) i = ∑ j ∈ univ.filter (i < ·), A i j * v j := by
  simp [mulVec, dotProduct, sum_filter, ite_mul]

omit [LinearOrder n] in
/-- The entry $i$ of $A v$ is the diagonal term plus the sum of the other terms: $(A v)_i = a_{ii}
v_i + \sum_{j \neq i} a_{ij} v_j$. -/
theorem mulVec_apply_eq_add_sum_erase [DecidableEq n] (A : Matrix n n R) (v : n → R) (i : n) :
    (A *ᵥ v) i = A i i * v i + ∑ j ∈ univ.erase i, A i j * v j := by
  rw [mulVec, dotProduct, ← add_sum_erase _ _ (mem_univ i)]

end MulVec

/-! ### The order-dual reading -/

section OrderDual

variable [Zero R] {U L : Matrix n n R}

/-- An upper triangular matrix for the order of $n$ is lower triangular for the dual order `nᵒᵈ`. -/
theorem IsUpperTriangular.isLowerTriangular_orderDual (hU : U.IsUpperTriangular) :
    IsLowerTriangular (m := nᵒᵈ) U := fun i j h => hU (i := i) (j := j) h

/-- A lower triangular matrix for the order of $n$ is upper triangular for the dual order `nᵒᵈ`. -/
theorem IsLowerTriangular.isUpperTriangular_orderDual (hL : L.IsLowerTriangular) :
    IsUpperTriangular (m := nᵒᵈ) L := fun i j h => hL (i := i) (j := j) h

end OrderDual

/-! ### Diagonals of triangular products -/

section Diag

variable [Fintype n] [NonUnitalNonAssocSemiring R]

/-- If $M$ and $N$ are upper triangular, then the diagonal of $M N$ is the product of the diagonals:
$(M N)_{ii} = m_{ii} n_{ii}$. -/
theorem IsUpperTriangular.mul_apply_self {M N : Matrix n n R} (hM : M.IsUpperTriangular)
    (hN : N.IsUpperTriangular) (i : n) : (M * N) i i = M i i * N i i :=
  hM.mul_apply_self_of_injective hN Function.injective_id i

/-- If $M$ and $N$ are lower triangular, then the diagonal of $M N$ is the product of the diagonals:
$(M N)_{ii} = m_{ii} n_{ii}$. -/
theorem IsLowerTriangular.mul_apply_self {M N : Matrix n n R} (hM : M.IsLowerTriangular)
    (hN : N.IsLowerTriangular) (i : n) : (M * N) i i = M i i * N i i :=
  hM.mul_apply_self_of_injective hN OrderDual.toDual.injective i

/-- If $M$ and $N$ are upper triangular and the index order is locally finite, then
$$(M N)_{ij} = \sum_{i \le k \le j} m_{ik} n_{kj}.$$
In particular $(M N)_{ij} = 0$ for $j < i$. -/
theorem IsUpperTriangular.mul_apply {M N : Matrix n n R} (hM : M.IsUpperTriangular)
    (hN : N.IsUpperTriangular) [LocallyFiniteOrder n] (i j : n) :
    (M * N) i j = ∑ k ∈ Finset.Icc i j, M i k * N k j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  rcases hk with hk | hk
  · rw [hM hk, zero_mul]
  · rw [hN hk, mul_zero]

/-- If $M$ and $N$ are lower triangular and the index order is locally finite, then
$$(M N)_{ij} = \sum_{j \le k \le i} m_{ik} n_{kj}.$$
In particular $(M N)_{ij} = 0$ for $i < j$. -/
theorem IsLowerTriangular.mul_apply {M N : Matrix n n R} (hM : M.IsLowerTriangular)
    (hN : N.IsLowerTriangular) [LocallyFiniteOrder n] (i j : n) :
    (M * N) i j = ∑ k ∈ Finset.Icc j i, M i k * N k j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  rcases hk with hk | hk
  · rw [hN (i := k) (j := j) hk, mul_zero]
  · rw [hM (i := i) (j := k) hk, zero_mul]

/-- If $G$ and $H$ are lower triangular, then
$$(G H^T)_{ij} = \sum_{k \le \min\{i, j\}} g_{ik} h_{jk}.$$
-/
theorem mul_transpose_apply_of_lower {G H : Matrix n n R} (hG : G.IsLowerTriangular)
    (hH : H.IsLowerTriangular) (i j : n) :
    (G * Hᵀ) i j = ∑ k ∈ Finset.univ.filter (· ≤ min i j), G i k * H j k := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
  rw [le_min_iff]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hik | hjk
  · exact hk (by rw [hG (i := i) (j := k) hik, zero_mul])
  · exact hk (by rw [Matrix.transpose_apply, hH (i := j) (j := k) hjk, mul_zero])

/-- If $G$ and $H$ are upper triangular, then
$$(G^T H)_{ij} = \sum_{k \le \min\{i, j\}} g_{ki} h_{kj}.$$
This is the counterpart of `Matrix.mul_transpose_apply_of_lower`. -/
theorem transpose_mul_apply_of_upper {G H : Matrix n n R} (hG : G.IsUpperTriangular)
    (hH : H.IsUpperTriangular) (i j : n) :
    (Gᵀ * H) i j = ∑ k ∈ Finset.univ.filter (· ≤ min i j), G k i * H k j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
  rw [le_min_iff]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hik | hjk
  · exact hk (by rw [Matrix.transpose_apply, hG hik, zero_mul])
  · exact hk (by rw [hH hjk, mul_zero])

/-- If $L$ is lower triangular and $D$ is diagonal, then
$$(L D L^T)_{ij} = \sum_{k \le \min\{i, j\}} \ell_{ik} d_{kk} \ell_{jk}.$$
-/
theorem mul_mul_transpose_apply_of_isDiag {L D : Matrix n n R} (hL : L.IsLowerTriangular)
    (hD : D.IsDiag) (i j : n) :
    (L * D * Lᵀ) i j = ∑ k ∈ Finset.univ.filter (· ≤ min i j), L i k * D k k * L j k := by
  have hLD : ∀ i k, (L * D) i k = L i k * D k k := fun i k => by
    conv_lhs => rw [← hD.diagonal_diag]
    rw [Matrix.mul_diagonal, Matrix.diag_apply]
  rw [mul_transpose_apply_of_lower (G := L * D) (H := L)
    (fun i j hij => by rw [hLD, hL hij, zero_mul]) hL]
  simp only [hLD]

end Diag

open Finset in
/-- **The Parlett identity for commuting upper triangular matrices.** Let $F$ and $T$ be upper
triangular matrices over a commutative ring with $T F = F T$, and let $i < j$. Then
$$f_{ij} (t_{jj} - t_{ii}) = t_{ij} (f_{jj} - f_{ii}) + \sum_{i < k < j} (t_{ik} f_{kj} - f_{ik}
  t_{kj}).$$
This is the entry $(i, j)$ of $T F = F T$, with the terms $k = i$ and $k = j$ split off.

For $F = f(T)$ this gives the Parlett recurrence `Matrix.pfc_apply_eq_parlett` of the module
`Numlib.Analysis.Matrix.Function.Triangular`. -/
theorem IsUpperTriangular.apply_mul_sub_eq_of_commute [Fintype n] [CommRing R]
    [LocallyFiniteOrder n] {F T : Matrix n n R} (hF : F.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (hc : Commute T F) {i j : n} (hij : i < j) :
    F i j * (T j j - T i i) =
      T i j * (F j j - F i i) + ∑ k ∈ Ioo i j, (T i k * F k j - F i k * T k j) := by
  have h := congrFun (congrFun hc.eq i) j
  rw [hT.mul_apply hF i j, hF.mul_apply hT i j, Icc_eq_cons_Ioc hij.le,
    sum_cons, sum_cons, Ioc_eq_cons_Ioo hij, sum_cons, sum_cons] at h
  rw [sum_sub_distrib, ← sub_eq_zero, ← neg_eq_zero, ← sub_eq_zero.mpr h]
  ring

/-- If $M$ is upper triangular, then the diagonal of the power $M^k$ is $(M^k)_{ii} = (m_{ii})^k$.
-/
theorem IsUpperTriangular.pow_apply_self [Fintype n] [Semiring R] {M : Matrix n n R}
    (hM : M.IsUpperTriangular) (m : ℕ) (i : n) : (M ^ m) i i = M i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, IsUpperTriangular.mul_apply_self (hM.pow m) hM, ih, pow_succ]

/-- If $M$ is lower triangular, then the diagonal of the power $M^k$ is $(M^k)_{ii} = (m_{ii})^k$.
-/
theorem IsLowerTriangular.pow_apply_self [Fintype n] [Semiring R] {M : Matrix n n R}
    (hM : M.IsLowerTriangular) (m : ℕ) (i : n) : (M ^ m) i i = M i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, IsLowerTriangular.mul_apply_self (hM.pow m) hM, ih, pow_succ]

omit [LinearOrder n] in
/-- Over a commutative semiring, if $D$ is diagonal, then $L D L^T$ is symmetric for every square
matrix $L$. -/
theorem isSymm_mul_mul_transpose_of_isDiag [Fintype n] [CommSemiring R] (L : Matrix n n R)
    {D : Matrix n n R} (hD : D.IsDiag) : (L * D * Lᵀ).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hD.isSymm.eq, Matrix.mul_assoc]

/-- A matrix on `Fin N` is upper triangular if and only if $a_{ij} = 0$ whenever $j < i$ as natural
numbers. -/
theorem isUpperTriangular_iff_fin [Zero R] {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsUpperTriangular ↔ ∀ i j : Fin N, (j : ℕ) < i → A i j = 0 :=
  ⟨fun h _ _ hij => h (Fin.lt_def.2 hij), fun h _ _ hij => h _ _ (Fin.lt_def.1 hij)⟩

/-- A matrix on `Fin N` is lower triangular if and only if $a_{ij} = 0$ whenever $i < j$ as natural
numbers. -/
theorem isLowerTriangular_iff_fin [Zero R] {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsLowerTriangular ↔ ∀ i j : Fin N, (i : ℕ) < j → A i j = 0 :=
  ⟨fun h _ _ hij => h (Fin.lt_def.2 hij), fun h _ _ hij => h _ _ (Fin.lt_def.1 hij)⟩

/-- If $M = Z T$ with $T$ upper triangular, then the first column of $M$ is $t_{00}$ times the first
column of $Z$: $M e_0 = t_{00} Z e_0$. -/
theorem col_zero_eq_smul_of_eq_mul [CommRing R] {N : ℕ} {M Z T : Matrix (Fin (N + 1))
    (Fin (N + 1)) R} (hM : M = Z * T) (hT : T.IsUpperTriangular) : M.col 0 = T 0 0 • Z.col 0 := by
  ext i
  rw [hM, col_apply, Matrix.mul_apply, Finset.sum_eq_single 0, Pi.smul_apply, col_apply,
    smul_eq_mul, mul_comm]
  · intro l _ hl
    rw [hT (Fin.pos_iff_ne_zero.2 hl), mul_zero]
  · simp

/-! ### Diagonal blocks of block triangular products -/

section BlockTriangular

variable {m α : Type*} [Fintype m] [LinearOrder α] {b : m → α} [CommRing R]

/-- If $M$ and $N$ are block triangular for the same labelling $b$, then each diagonal block of
$M N$ is the product of the diagonal blocks: $(M N)_{kk} = M_{kk} N_{kk}$, where $M_{kk}$ is the
block of the indices with label $k$. -/
theorem BlockTriangular.toBlock_mul {M N : Matrix m m R} (hM : M.BlockTriangular b)
    (hN : N.BlockTriangular b) (k : α) :
    (M * N).toBlock (b · = k) (b · = k) =
      M.toBlock (b · = k) (b · = k) * N.toBlock (b · = k) (b · = k) := by
  classical
  rw [toBlock_mul_eq_add _ (b · = k), add_eq_left]
  ext i j
  simp only [Matrix.mul_apply, toBlock_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hl : b l ≠ k := l.2
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hM (by rw [i.2]; exact h), zero_mul]
  · rw [hN (by rw [j.2]; exact h), mul_zero]

/-- If $M$ is block triangular for the labelling $b$, then each diagonal block of $M^p$ is the
$p$-th power of the diagonal block: $(M^p)_{kk} = (M_{kk})^p$. -/
theorem BlockTriangular.toBlock_pow [DecidableEq m] {M : Matrix m m R} (hM : M.BlockTriangular b)
    (k : α) (p : ℕ) :
    (M ^ p).toBlock (b · = k) (b · = k) = M.toBlock (b · = k) (b · = k) ^ p := by
  induction p with
  | zero => ext i j; simp [Matrix.one_apply, Subtype.ext_iff]
  | succ p ih => rw [pow_succ, (hM.pow p).toBlock_mul hM, ih, pow_succ]

/-- For a labelling $b$ with finitely many labels, the block $(k, l)$ of a product is the sum over
the labels: $(M N)_{kl} = \sum_r M_{kr} N_{rl}$. -/
theorem toBlock_mul_eq_sum [Fintype α] (M N : Matrix m m R) (k l : α) :
    (M * N).toBlock (b · = k) (b · = l) =
      ∑ r, M.toBlock (b · = k) (b · = r) * N.toBlock (b · = r) (b · = l) := by
  classical
  ext i j
  simp only [toBlock_apply, Matrix.mul_apply, Matrix.sum_apply]
  rw [← Finset.sum_fiberwise Finset.univ b]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_subtype (Finset.univ.filter (b · = r)) (p := (b · = r)) (by simp)]

/-- If $M$ and $N$ are block triangular for a labelling $b$ with finitely many labels, then the
block $(k, l)$ of $M N$ involves only the labels between $k$ and $l$:
$$(M N)_{kl} = \sum_{k \le r \le l} M_{kr} N_{rl}.$$
-/
theorem BlockTriangular.toBlock_mul_eq_sum_Icc [Finite α] [LocallyFiniteOrder α]
    {M N : Matrix m m R} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (k l : α) :
    (M * N).toBlock (b · = k) (b · = l) =
      ∑ r ∈ Finset.Icc k l, M.toBlock (b · = k) (b · = r) * N.toBlock (b · = r) (b · = l) := by
  have := Fintype.ofFinite α
  rw [toBlock_mul_eq_sum]
  refine (Finset.sum_subset (Finset.subset_univ _) fun r _ hr => ?_).symm
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
  ext i j
  simp only [Matrix.mul_apply, toBlock_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rcases hr with hr | hr
  · rw [hM (by rw [x.2, i.2]; exact hr), zero_mul]
  · rw [hN (by rw [x.2, j.2]; exact hr), mul_zero]

end BlockTriangular

section Charpoly

variable [Fintype n] [DecidableEq n] [CommRing R]

/-- The characteristic polynomial of a lower triangular matrix $M$ is
$$\chi_M = \prod_i (X - m_{ii}).$$
This is the counterpart of Mathlib's `Matrix.charpoly_of_isUpperTriangular`. -/
theorem charpoly_of_isLowerTriangular (M : Matrix n n R) (hM : M.IsLowerTriangular) :
    M.charpoly = ∏ i, (Polynomial.X - Polynomial.C (M i i)) := by
  simp [charpoly, det_of_isLowerTriangular _ hM.charmatrix]

/-- Over a field, the spectrum of an upper triangular matrix $T$ is the set of its diagonal entries
$\{t_{ii}\}$, because $\chi_T = \prod_i (X - t_{ii})$. -/
theorem IsUpperTriangular.spectrum_eq {K : Type*} [Field K] {T : Matrix n n K}
    (hT : T.IsUpperTriangular) : spectrum K T = Set.range fun i => T i i := by
  ext μ
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_of_isUpperTriangular T hT, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero, Set.mem_range]
  exact exists_congr fun i => eq_comm

/-- Over a field, the spectrum of a lower triangular matrix $T$ is the set of its diagonal entries
$\{t_{ii}\}$. This is the counterpart of `Matrix.IsUpperTriangular.spectrum_eq`. -/
theorem IsLowerTriangular.spectrum_eq {K : Type*} [Field K] {T : Matrix n n K}
    (hT : T.IsLowerTriangular) : spectrum K T = Set.range fun i => T i i := by
  ext μ
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_of_isLowerTriangular T hT, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero, Set.mem_range]
  exact exists_congr fun i => eq_comm

end Charpoly

/-! ### Nonsingularity and inverses of triangular matrices -/

section Inverse

variable [Fintype n]

/-- Over a field, an upper triangular matrix $U$ is nonsingular if and only if $u_{ii} \neq 0$ for
every $i$. This is the first sentence of [quarteroni2000numerical] §3.2.

The proof uses that the determinant of $U$ is the product of its diagonal entries. -/
theorem IsUpperTriangular.isUnit_iff {K : Type*} [Field K] {U : Matrix n n K}
    (hU : U.IsUpperTriangular) : IsUnit U ↔ ∀ i, U i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, det_of_isUpperTriangular hU, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  simp

/-- Over a field, a lower triangular matrix $L$ is nonsingular if and only if $\ell_{ii} \neq 0$ for
every $i$. -/
theorem IsLowerTriangular.isUnit_iff {K : Type*} [Field K] {L : Matrix n n K}
    (hL : L.IsLowerTriangular) : IsUnit L ↔ ∀ i, L i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular L hL, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  simp

/-- Over a field, if $U$ is upper triangular and $u_{ii} \neq 0$ for every $i$, then $\det U$ is a
unit. This is the form of the hypothesis that the substitution and least-squares solvers use. -/
theorem IsUpperTriangular.isUnit_det_of_diag_ne_zero {K : Type*} [Field K] {U : Matrix n n K}
    (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) : IsUnit U.det :=
  (isUnit_iff_isUnit_det U).1 (hU.isUnit_iff.2 hd)

/-- Over a field, if $L$ is lower triangular and $\ell_{ii} \neq 0$ for every $i$, then $\det L$ is
a unit. -/
theorem IsLowerTriangular.isUnit_det_of_diag_ne_zero {K : Type*} [Field K] {L : Matrix n n K}
    (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0) : IsUnit L.det :=
  (isUnit_iff_isUnit_det L).1 (hL.isUnit_iff.2 hd)

variable [DecidableEq n] [CommRing R]

/-- Over a commutative ring, the inverse of an upper triangular matrix is upper triangular.

The statement needs no hypothesis, because the inverse of a singular matrix is $0$. -/
theorem IsUpperTriangular.inv {U : Matrix n n R} (hU : U.IsUpperTriangular) :
    U⁻¹.IsUpperTriangular := by
  by_cases h : IsUnit U.det
  · have : Invertible U := invertibleOfIsUnitDet U h
    exact blockTriangular_inv_of_blockTriangular hU
  · rw [nonsing_inv_apply_not_isUnit U h]
    exact blockTriangular_zero

/-- Over a commutative ring, the inverse of a lower triangular matrix is lower triangular.

The statement needs no hypothesis, because the inverse of a singular matrix is $0$. -/
theorem IsLowerTriangular.inv {L : Matrix n n R} (hL : L.IsLowerTriangular) :
    L⁻¹.IsLowerTriangular := by
  by_cases h : IsUnit L.det
  · have : Invertible L := invertibleOfIsUnitDet L h
    exact blockTriangular_inv_of_blockTriangular hL
  · rw [nonsing_inv_apply_not_isUnit L h]
    exact blockTriangular_zero

/-- Over a commutative ring with an involution, a unitary upper triangular matrix $U$ is diagonal:
$U = \operatorname{diag}(u_{ii})$. The reason is that its inverse $U^H$ is both upper and lower
triangular. -/
theorem IsUpperTriangular.eq_diagonal_of_mem_unitaryGroup [StarRing R] {U : Matrix n n R}
    (hU : U.IsUpperTriangular) (hUu : U ∈ unitaryGroup n R) : U = diagonal fun i => U i i := by
  have hinv : U⁻¹ = star U := inv_eq_left_inv ((mem_unitaryGroup_iff').1 hUu)
  have hst : (star U).IsUpperTriangular := by rw [← hinv]; exact hU.inv
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [diagonal_apply_ne _ hij.ne]
    have := hst hij
    rwa [star_apply, star_eq_zero] at this
  · rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij.ne', hU hij]

/-- Over a commutative ring with an involution, a unitary lower triangular matrix $L$ is diagonal:
$L = \operatorname{diag}(\ell_{ii})$. This is the counterpart of
`Matrix.IsUpperTriangular.eq_diagonal_of_mem_unitaryGroup`. -/
theorem IsLowerTriangular.eq_diagonal_of_mem_unitaryGroup [StarRing R] {L : Matrix n n R}
    (hL : L.IsLowerTriangular) (hLu : L ∈ unitaryGroup n R) : L = diagonal fun i => L i i := by
  have hinv : L⁻¹ = star L := inv_eq_left_inv ((mem_unitaryGroup_iff').1 hLu)
  have hst : (star L).IsLowerTriangular := by rw [← hinv]; exact hL.inv
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [diagonal_apply_ne _ hij.ne, hL hij]
  · rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij.ne']
    have := hst hij
    rwa [star_apply, star_eq_zero] at this

end Inverse

/-! ### Unit triangular matrices -/

section UnitTriangular

/-- A square matrix $L$ is **unit lower triangular** if it is lower triangular and $\ell_{ii} = 1$
for every $i$. This is the shape of the factor $L$ of an LU factorization,
[quarteroni2000numerical] §1.6.2. -/
structure IsUnitLowerTriangular [Zero R] [One R] (L : Matrix n n R) : Prop where
  /-- The matrix is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- The diagonal entries are $1$. -/
  diag_eq_one : ∀ i, L i i = 1

/-- A square matrix $U$ is **unit upper triangular** if it is upper triangular and $u_{ii} = 1$ for
every $i$. This is the shape of the factor $U$ of a $U L$ factorization, [golub2013matrix]
§3.1.7. -/
structure IsUnitUpperTriangular [Zero R] [One R] (U : Matrix n n R) : Prop where
  /-- The matrix is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- The diagonal entries are $1$. -/
  diag_eq_one : ∀ i, U i i = 1

section Basic

variable [Zero R] [One R] {L U : Matrix n n R}

/-- The identity matrix is unit lower triangular. -/
theorem isUnitLowerTriangular_one : (1 : Matrix n n R).IsUnitLowerTriangular :=
  ⟨blockTriangular_one, fun i => one_apply_eq i⟩

/-- The identity matrix is unit upper triangular. -/
theorem isUnitUpperTriangular_one : (1 : Matrix n n R).IsUnitUpperTriangular :=
  ⟨blockTriangular_one, fun i => one_apply_eq i⟩

/-- The transpose $U^T$ is unit lower triangular if and only if $U$ is unit upper triangular. -/
theorem isUnitLowerTriangular_transpose_iff :
    Uᵀ.IsUnitLowerTriangular ↔ U.IsUnitUpperTriangular :=
  ⟨fun h => ⟨fun _ _ hij => h.isLowerTriangular hij, h.diag_eq_one⟩,
    fun h => ⟨fun _ _ hij => h.isUpperTriangular hij, h.diag_eq_one⟩⟩

/-- The transpose $L^T$ is unit upper triangular if and only if $L$ is unit lower triangular. -/
theorem isUnitUpperTriangular_transpose_iff :
    Lᵀ.IsUnitUpperTriangular ↔ L.IsUnitLowerTriangular :=
  ⟨fun h => ⟨fun _ _ hij => h.isUpperTriangular hij, h.diag_eq_one⟩,
    fun h => ⟨fun _ _ hij => h.isLowerTriangular hij, h.diag_eq_one⟩⟩

end Basic

variable [Fintype n]

/-- The product of two unit lower triangular matrices is unit lower triangular. This is the last
bullet of [quarteroni2000numerical] §1.6.2.

The product is lower triangular, and its diagonal is the product of the two unit diagonals. -/
theorem IsUnitLowerTriangular.mul [NonAssocSemiring R] {L₁ L₂ : Matrix n n R}
    (h₁ : L₁.IsUnitLowerTriangular) (h₂ : L₂.IsUnitLowerTriangular) :
    (L₁ * L₂).IsUnitLowerTriangular where
  isLowerTriangular := h₁.isLowerTriangular.mul h₂.isLowerTriangular
  diag_eq_one i := by
    rw [h₁.isLowerTriangular.mul_apply_self h₂.isLowerTriangular, h₁.diag_eq_one,
      h₂.diag_eq_one, one_mul]

/-- The product of two unit upper triangular matrices is unit upper triangular. -/
theorem IsUnitUpperTriangular.mul [NonAssocSemiring R] {U₁ U₂ : Matrix n n R}
    (h₁ : U₁.IsUnitUpperTriangular) (h₂ : U₂.IsUnitUpperTriangular) :
    (U₁ * U₂).IsUnitUpperTriangular where
  isUpperTriangular := h₁.isUpperTriangular.mul h₂.isUpperTriangular
  diag_eq_one i := by
    rw [h₁.isUpperTriangular.mul_apply_self h₂.isUpperTriangular, h₁.diag_eq_one,
      h₂.diag_eq_one, one_mul]

/-- Over a commutative ring, a unit lower triangular matrix has determinant $1$. -/
theorem IsUnitLowerTriangular.det_eq_one [CommRing R] {L : Matrix n n R}
    (hL : L.IsUnitLowerTriangular) : L.det = 1 := by
  rw [det_of_isLowerTriangular L hL.isLowerTriangular]
  exact Finset.prod_eq_one fun i _ => hL.diag_eq_one i

/-- Over a commutative ring, a unit upper triangular matrix has determinant $1$. -/
theorem IsUnitUpperTriangular.det_eq_one [CommRing R] {U : Matrix n n R}
    (hU : U.IsUnitUpperTriangular) : U.det = 1 := by
  rw [det_of_isUpperTriangular hU.isUpperTriangular]
  exact Finset.prod_eq_one fun i _ => hU.diag_eq_one i

/-- Over a commutative ring, a unit lower triangular matrix is invertible. -/
theorem IsUnitLowerTriangular.isUnit [CommRing R] {L : Matrix n n R}
    (hL : L.IsUnitLowerTriangular) : IsUnit L :=
  (isUnit_iff_isUnit_det L).2 (by rw [hL.det_eq_one]; exact isUnit_one)

/-- Over a commutative ring, a unit upper triangular matrix is invertible. -/
theorem IsUnitUpperTriangular.isUnit [CommRing R] {U : Matrix n n R}
    (hU : U.IsUnitUpperTriangular) : IsUnit U :=
  (isUnit_iff_isUnit_det U).2 (by rw [hU.det_eq_one]; exact isUnit_one)

/-- Over a commutative ring, the inverse of a unit lower triangular matrix is unit lower triangular.

The inverse of a lower triangular matrix is lower triangular, and the diagonal of $L^{-1} L = I$
is the product of the diagonals. -/
theorem IsUnitLowerTriangular.inv [CommRing R] {L : Matrix n n R}
    (hL : L.IsUnitLowerTriangular) : L⁻¹.IsUnitLowerTriangular := by
  have : Invertible L := hL.isUnit.invertible
  have hinv : L⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular hL.isLowerTriangular
  refine ⟨hinv, fun i => ?_⟩
  have h := congrFun (congrFun (nonsing_inv_mul L (isUnit_iff_isUnit_det L |>.1 hL.isUnit)) i) i
  rwa [hinv.mul_apply_self hL.isLowerTriangular, hL.diag_eq_one, mul_one, one_apply_eq] at h

/-- Over a commutative ring, the inverse of a unit upper triangular matrix is unit upper triangular,
by the argument of `Matrix.IsUnitLowerTriangular.inv`. -/
theorem IsUnitUpperTriangular.inv [CommRing R] {U : Matrix n n R}
    (hU : U.IsUnitUpperTriangular) : U⁻¹.IsUnitUpperTriangular := by
  have : Invertible U := hU.isUnit.invertible
  have hinv : U⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular hU.isUpperTriangular
  refine ⟨hinv, fun i => ?_⟩
  have h := congrFun (congrFun (nonsing_inv_mul U (isUnit_iff_isUnit_det U |>.1 hU.isUnit)) i) i
  rwa [hinv.mul_apply_self hU.isUpperTriangular, hU.diag_eq_one, mul_one, one_apply_eq] at h

end UnitTriangular

end Matrix
