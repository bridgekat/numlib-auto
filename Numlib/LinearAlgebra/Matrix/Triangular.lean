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

The vocabulary of triangular matrices beyond Mathlib's `Matrix.IsUpperTriangular` and
`Matrix.IsLowerTriangular` (which are `Matrix.BlockTriangular` for `id` and for
`OrderDual.toDual`), on a matrix indexed by any linearly ordered type.

## Main definitions

* `Matrix.blockDiagPart`, `Matrix.blockStrictLower`, `Matrix.blockStrictUpper`: the same three
  parts for a block labelling `π : n → ι` of the indices (the entries with `π i = π j`,
  `π j < π i`, `π i < π j`), which reduce to the pointwise ones for `π = id`.
* `Matrix.strictLower`, `Matrix.strictUpper`, `Matrix.diagPart`: the three parts a matrix splits
  into, `Matrix.diagPart_add_strictLower_add_strictUpper`, and the signed form `A = D - E - F` of
  the classical splittings behind the Jacobi, Gauss–Seidel and SOR iterations; over a field, the
  diagonal part is a unit exactly when the diagonal has no zero (`Matrix.isUnit_diagPart_iff`),
  and its inverse is then the diagonal of the inverses (`Matrix.inv_diagPart`).
* `Matrix.IsUnitLowerTriangular`, `Matrix.IsUnitUpperTriangular`: triangular with ones on the
  diagonal, the shapes of the factors of an LU factorization and of its `U L` dual. Transposition
  exchanges them (`Matrix.isUnitLowerTriangular_transpose_iff`).

## Main results

* `Matrix.IsUpperTriangular.isUnit_iff`, `Matrix.IsLowerTriangular.isUnit_iff`: a triangular
  matrix is nonsingular exactly when its diagonal has no zero entry, since its determinant is the
  product of the diagonal; `Matrix.IsUpperTriangular.isUnit_det_of_diag_ne_zero` and its lower
  twin give the determinant form.
* `Matrix.IsUpperTriangular.inv`, `Matrix.IsLowerTriangular.inv`: the inverse of a triangular
  matrix is triangular of the same kind, with no hypothesis (a singular matrix has inverse `0`).
* `Matrix.IsUpperTriangular.mul_apply_self`, `Matrix.IsLowerTriangular.mul_apply_self`: the
  diagonal of a product of two triangular matrices is the product of the diagonals; hence
  `Matrix.IsUnitLowerTriangular.mul`, `.inv`, `.det_eq_one` and their upper duals.
* `Matrix.IsUpperTriangular.isLowerTriangular_orderDual`,
  `Matrix.IsLowerTriangular.isUpperTriangular_orderDual`: a triangular matrix is triangular of the
  other kind on the dual order, the bridge through which backward substitution is forward
  substitution on `nᵒᵈ` (`Numlib/Direct/Substitution`).
* `Matrix.charpoly_of_isLowerTriangular`: the mirror of Mathlib's
  `Matrix.charpoly_of_isUpperTriangular`; `Matrix.IsUpperTriangular.spectrum_eq`,
  `Matrix.IsLowerTriangular.spectrum_eq`: over a field the spectrum of a triangular matrix is the
  set of its diagonal entries.
* Entries of products: `Matrix.IsUpperTriangular.mul_apply` (a sum over the indices between),
  `Matrix.IsUpperTriangular.pow_apply_self` (each with its lower twin),
  `Matrix.mul_transpose_apply_of_lower`, `Matrix.transpose_mul_apply_of_upper` and
  `Matrix.mul_mul_transpose_apply_of_isDiag` (the entries of `G Hᵀ`, `Gᵀ H` and `L D Lᵀ`, sums
  over `k ≤ min i j`), `Matrix.col_zero_eq_smul_of_eq_mul` (the first column of `Z T`).
* `Matrix.BlockTriangular.toBlock_mul`, `.toBlock_pow`, `.toBlock_mul_eq_sum_Icc`: the diagonal
  blocks of products and powers of block triangular matrices, and the blocks of a product.
* `Matrix.IsUpperTriangular.eq_diagonal_of_mem_unitaryGroup` (and the lower version): a unitary
  triangular matrix is diagonal.

## Implementation notes

Mathlib's `Matrix.BlockTriangular M b` unfolds to `b j < b i → M i j = 0`, so `BlockTriangular ·
id` is *upper* triangularity and the lower-triangular statement is the one for
`OrderDual.toDual`. That is why `Matrix.strictLower_blockTriangular` and
`Matrix.strictUpper_blockTriangular` are stated with different order maps.

## References

* [quarteroni2000numerical] §1.6.2, §3.2.
* [golub2013matrix] §3.1.7.
-/

namespace Matrix

variable {n R : Type*} [LinearOrder n]

/-! ### The triangular parts -/

section Parts

variable [Zero R]

/-- Strict lower triangular part. -/
def strictLower (A : Matrix n n R) : Matrix n n R := Matrix.of fun i j => if j < i then A i j else 0

/-- Strict upper triangular part. -/
def strictUpper (A : Matrix n n R) : Matrix n n R := Matrix.of fun i j => if i < j then A i j else 0

/-- Diagonal part. -/
def diagPart [DecidableEq n] (A : Matrix n n R) : Matrix n n R := Matrix.diagonal A.diag

/-- The entries of the strict lower triangular part. -/
@[simp]
theorem strictLower_apply (A : Matrix n n R) (i j : n) :
    strictLower A i j = if j < i then A i j else 0 := rfl

/-- The entries of the strict upper triangular part. -/
@[simp]
theorem strictUpper_apply (A : Matrix n n R) (i j : n) :
    strictUpper A i j = if i < j then A i j else 0 := rfl

omit [LinearOrder n] in
/-- The entries of the diagonal part. -/
@[simp]
theorem diagPart_apply [DecidableEq n] (A : Matrix n n R) (i j : n) :
    diagPart A i j = if i = j then A i i else 0 := diagonal_apply _ _ _

/-- The strict lower part is lower triangular, that is, block triangular for `OrderDual.toDual`;
see the implementation notes for why the order map is not `id`. -/
theorem strictLower_blockTriangular (A : Matrix n n R) :
    (strictLower A).BlockTriangular OrderDual.toDual := fun _ _ h => by
  simp [asymm (OrderDual.toDual_lt_toDual.mp h)]

/-- The strict upper part is upper triangular, that is, block triangular for `id`. -/
theorem strictUpper_blockTriangular (A : Matrix n n R) :
    (strictUpper A).BlockTriangular id := fun i j h => by
  simp only [strictUpper_apply, ite_eq_right_iff]
  exact fun h' => absurd h' (asymm h)

/-- The transpose of the strictly lower part is the strictly upper part of the transpose. -/
theorem strictLower_transpose (A : Matrix n n R) : (strictLower A)ᵀ = strictUpper Aᵀ := by
  ext i j
  simp

/-- The transpose of the strictly upper part is the strictly lower part of the transpose. -/
theorem strictUpper_transpose (A : Matrix n n R) : (strictUpper A)ᵀ = strictLower Aᵀ := by
  ext i j
  simp

omit [LinearOrder n] in
/-- The transpose of the diagonal part is the diagonal part of the transpose. -/
theorem diagPart_transpose [DecidableEq n] (A : Matrix n n R) : (diagPart A)ᵀ = diagPart Aᵀ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

end Parts

/-- Every matrix is the sum of its diagonal, strictly lower and strictly upper parts: the three
parts partition the entries, so nothing is counted twice and nothing is missed.  The signed form
below is the splitting convention of the classical stationary iterations. -/
theorem diagPart_add_strictLower_add_strictUpper [DecidableEq n] [AddCommMonoid R]
    (A : Matrix n n R) : diagPart A + strictLower A + strictUpper A = A := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, asymm h]
  · simp
  · simp [h, h.ne', asymm h]

/-- The splitting convention `A = D - E - F` of the classical stationary iterations, with
`E = -strictLower A` and `F = -strictUpper A`. -/
theorem diagPart_sub_neg_strictLower_sub_neg_strictUpper [DecidableEq n] [AddCommGroup R]
    (A : Matrix n n R) : diagPart A - (-strictLower A) - (-strictUpper A) = A := by
  rw [sub_neg_eq_add, sub_neg_eq_add, diagPart_add_strictLower_add_strictUpper]

/-! ### The block parts for a block labelling -/

section BlockParts

variable {m ι : Type*}

section Zero

variable [Zero R]

/-- The **block diagonal part** of `A` for the block labelling `π`: the entries whose row and column
carry the same label, [saad2003iterative] `D` of (4.15). -/
def blockDiagPart [DecidableEq ι] (π : m → ι) (A : Matrix m m R) : Matrix m m R :=
  Matrix.of fun i j => if π i = π j then A i j else 0

/-- Entries of the block diagonal part: those whose row and column carry the same label. -/
@[simp]
theorem blockDiagPart_apply [DecidableEq ι] (π : m → ι) (A : Matrix m m R) (i j : m) :
    blockDiagPart π A i j = if π i = π j then A i j else 0 := rfl

/-- The **strict block-lower part** of `A` for the block labelling `π`, [saad2003iterative] `-E` of
(4.15). -/
def blockStrictLower [LinearOrder ι] (π : m → ι) (A : Matrix m m R) : Matrix m m R :=
  Matrix.of fun i j => if π j < π i then A i j else 0

/-- Entries of the strict block-lower part: those whose column label is below the row label. -/
@[simp]
theorem blockStrictLower_apply [LinearOrder ι] (π : m → ι) (A : Matrix m m R) (i j : m) :
    blockStrictLower π A i j = if π j < π i then A i j else 0 := rfl

/-- The **strict block-upper part** of `A` for the block labelling `π`, [saad2003iterative] `-F` of
(4.15). -/
def blockStrictUpper [LinearOrder ι] (π : m → ι) (A : Matrix m m R) : Matrix m m R :=
  Matrix.of fun i j => if π i < π j then A i j else 0

/-- Entries of the strict block-upper part: those whose row label is below the column label. -/
@[simp]
theorem blockStrictUpper_apply [LinearOrder ι] (π : m → ι) (A : Matrix m m R) (i j : m) :
    blockStrictUpper π A i j = if π i < π j then A i j else 0 := rfl

/-- With the identity labelling the strict block-lower part is the strictly lower part. -/
@[simp]
theorem blockStrictLower_id (A : Matrix n n R) : blockStrictLower id A = strictLower A := rfl

/-- With the identity labelling the strict block-upper part is the strictly upper part. -/
@[simp]
theorem blockStrictUpper_id (A : Matrix n n R) : blockStrictUpper id A = strictUpper A := rfl

omit [LinearOrder n] in
/-- With the identity labelling the block diagonal part is the diagonal part. -/
@[simp]
theorem blockDiagPart_id [DecidableEq n] (A : Matrix n n R) : blockDiagPart id A = diagPart A := by
  ext i j
  rw [blockDiagPart_apply, diagPart, Matrix.diagonal_apply]
  split <;> simp_all [Matrix.diag]

end Zero

/-- **[saad2003iterative] (4.15)**: a matrix is the sum of its block-diagonal, strict block-lower
and strict block-upper parts, which in [saad2003iterative] letters is `A = D - E - F`. -/
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
/-- The diagonal part of `A` is a unit exactly when every diagonal entry of `A` is nonzero.  This is
the hypothesis every classical splitting is built on. -/
theorem isUnit_diagPart_iff (A : Matrix n n 𝕜) : IsUnit (diagPart A) ↔ ∀ i, A i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, diagPart, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp [Matrix.diag]

omit [LinearOrder n] in
/-- The inverse of the diagonal part is the diagonal matrix of the inverses.  Every entrywise
computation with a splitting goes through this, because `Matrix.inv_diagonal` inverts the diagonal
in the Pi ring and is therefore `0` when one entry vanishes. -/
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
/-- Row `i` of `D v` is `a_ii v_i`. -/
theorem diagPart_mulVec_apply [DecidableEq n] (A : Matrix n n R) (v : n → R) (i : n) :
    (diagPart A *ᵥ v) i = A i i * v i := by
  rw [diagPart, mulVec_diagonal]
  rfl

/-- Row `i` of `L v` is `∑_{j < i} a_ij v_j`. -/
theorem strictLower_mulVec_apply (A : Matrix n n R) (v : n → R) (i : n) :
    (strictLower A *ᵥ v) i = ∑ j ∈ univ.filter (· < i), A i j * v j := by
  simp [mulVec, dotProduct, sum_filter, ite_mul]

/-- Row `i` of `U v` is `∑_{i < j} a_ij v_j`. -/
theorem strictUpper_mulVec_apply (A : Matrix n n R) (v : n → R) (i : n) :
    (strictUpper A *ᵥ v) i = ∑ j ∈ univ.filter (i < ·), A i j * v j := by
  simp [mulVec, dotProduct, sum_filter, ite_mul]

omit [LinearOrder n] in
/-- Row `i` of `A v` split into the diagonal term and the rest. -/
theorem mulVec_apply_eq_add_sum_erase [DecidableEq n] (A : Matrix n n R) (v : n → R) (i : n) :
    (A *ᵥ v) i = A i i * v i + ∑ j ∈ univ.erase i, A i j * v j := by
  rw [mulVec, dotProduct, ← add_sum_erase _ _ (mem_univ i)]

end MulVec

/-! ### The order-dual reading -/

section OrderDual

variable [Zero R] {U L : Matrix n n R}

/-- An upper triangular matrix on `n` is a lower triangular matrix on the dual order `nᵒᵈ`. -/
theorem IsUpperTriangular.isLowerTriangular_orderDual (hU : U.IsUpperTriangular) :
    IsLowerTriangular (m := nᵒᵈ) U := fun i j h => hU (i := i) (j := j) h

/-- A lower triangular matrix on `n` is an upper triangular matrix on the dual order `nᵒᵈ`. -/
theorem IsLowerTriangular.isUpperTriangular_orderDual (hL : L.IsLowerTriangular) :
    IsUpperTriangular (m := nᵒᵈ) L := fun i j h => hL (i := i) (j := j) h

end OrderDual

/-! ### Diagonals of triangular products -/

section Diag

variable [Fintype n] [NonUnitalNonAssocSemiring R]

/-- The diagonal of a product of two upper triangular matrices is the product of the diagonals.
-/
theorem IsUpperTriangular.mul_apply_self {M N : Matrix n n R} (hM : M.IsUpperTriangular)
    (hN : N.IsUpperTriangular) (i : n) : (M * N) i i = M i i * N i i :=
  hM.mul_apply_self_of_injective hN Function.injective_id i

/-- The diagonal of a product of two lower triangular matrices is the product of the diagonals.
-/
theorem IsLowerTriangular.mul_apply_self {M N : Matrix n n R} (hM : M.IsLowerTriangular)
    (hN : N.IsLowerTriangular) (i : n) : (M * N) i i = M i i * N i i :=
  hM.mul_apply_self_of_injective hN OrderDual.toDual.injective i

/-- An entry of a product of upper triangular matrices is a sum over the indices between. -/
theorem IsUpperTriangular.mul_apply {M N : Matrix n n R} (hM : M.IsUpperTriangular)
    (hN : N.IsUpperTriangular) [LocallyFiniteOrder n] (i j : n) :
    (M * N) i j = ∑ k ∈ Finset.Icc i j, M i k * N k j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  rcases hk with hk | hk
  · rw [hM hk, zero_mul]
  · rw [hN hk, mul_zero]

/-- An entry of a product of lower triangular matrices is a sum over the indices between. -/
theorem IsLowerTriangular.mul_apply {M N : Matrix n n R} (hM : M.IsLowerTriangular)
    (hN : N.IsLowerTriangular) [LocallyFiniteOrder n] (i j : n) :
    (M * N) i j = ∑ k ∈ Finset.Icc j i, M i k * N k j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  rcases hk with hk | hk
  · rw [hN (i := k) (j := j) hk, mul_zero]
  · rw [hM (i := i) (j := k) hk, zero_mul]

/-- The entry `(i, j)` of `G Hᵀ` for lower triangular `G` and `H` is `∑_{k ≤ min i j} g_ik h_jk`. -/
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

/-- The entry `(i, j)` of `Gᵀ H` for upper triangular `G` and `H` is `∑_{k ≤ min i j} g_ki h_kj`,
the dual of `Matrix.mul_transpose_apply_of_lower`. -/
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

/-- The entry `(i, j)` of `L D Lᵀ` for a lower triangular `L` and a diagonal `D` is
`∑_{k ≤ min i j} l_ik d_k l_jk`. -/
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

/-- The diagonal of a power of an upper triangular matrix. -/
theorem IsUpperTriangular.pow_apply_self [Fintype n] [Semiring R] {M : Matrix n n R}
    (hM : M.IsUpperTriangular) (m : ℕ) (i : n) : (M ^ m) i i = M i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, IsUpperTriangular.mul_apply_self (hM.pow m) hM, ih, pow_succ]

/-- The diagonal of a power of a lower triangular matrix. -/
theorem IsLowerTriangular.pow_apply_self [Fintype n] [Semiring R] {M : Matrix n n R}
    (hM : M.IsLowerTriangular) (m : ℕ) (i : n) : (M ^ m) i i = M i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, IsLowerTriangular.mul_apply_self (hM.pow m) hM, ih, pow_succ]

omit [LinearOrder n] in
/-- `L D Lᵀ` is symmetric for a diagonal `D`. -/
theorem isSymm_mul_mul_transpose_of_isDiag [Fintype n] [CommSemiring R] (L : Matrix n n R)
    {D : Matrix n n R} (hD : D.IsDiag) : (L * D * Lᵀ).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hD.isSymm.eq, Matrix.mul_assoc]

/-- On `Fin N`, upper triangular is the condition `A i j = 0` for `j < i` on values. -/
theorem isUpperTriangular_iff_fin [Zero R] {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsUpperTriangular ↔ ∀ i j : Fin N, (j : ℕ) < i → A i j = 0 :=
  ⟨fun h _ _ hij => h (Fin.lt_def.2 hij), fun h _ _ hij => h _ _ (Fin.lt_def.1 hij)⟩

/-- On `Fin N`, lower triangular is the condition `A i j = 0` for `i < j` on values. -/
theorem isLowerTriangular_iff_fin [Zero R] {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsLowerTriangular ↔ ∀ i j : Fin N, (i : ℕ) < j → A i j = 0 :=
  ⟨fun h _ _ hij => h (Fin.lt_def.2 hij), fun h _ _ hij => h _ _ (Fin.lt_def.1 hij)⟩

/-- The first column of `M = Z T` with `T` upper triangular is `T₀₀ Z e₀`. -/
theorem col_zero_eq_smul_of_eq_mul [CommRing R] {N : ℕ} {M Z T : Matrix (Fin (N + 1))
    (Fin (N + 1)) R} (hM : M = Z * T) (hT : T.IsUpperTriangular) : M.col 0 = T 0 0 • Z.col 0 := by
  ext i
  rw [hM, col_apply, mul_apply, Finset.sum_eq_single 0, Pi.smul_apply, col_apply, smul_eq_mul,
    mul_comm]
  · intro l _ hl
    rw [hT (Fin.pos_iff_ne_zero.2 hl), mul_zero]
  · simp

/-! ### Diagonal blocks of block triangular products -/

section BlockTriangular

variable {m α : Type*} [Fintype m] [LinearOrder α] {b : m → α} [CommRing R]

/-- The diagonal blocks of a product of block triangular matrices are the products of the diagonal
blocks. -/
theorem BlockTriangular.toBlock_mul {M N : Matrix m m R} (hM : M.BlockTriangular b)
    (hN : N.BlockTriangular b) (k : α) :
    (M * N).toBlock (b · = k) (b · = k) =
      M.toBlock (b · = k) (b · = k) * N.toBlock (b · = k) (b · = k) := by
  classical
  rw [toBlock_mul_eq_add _ (b · = k), add_eq_left]
  ext i j
  simp only [mul_apply, toBlock_apply, zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hl : b l ≠ k := l.2
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hM (by rw [i.2]; exact h), zero_mul]
  · rw [hN (by rw [j.2]; exact h), mul_zero]

/-- The diagonal blocks of the powers of a block triangular matrix. -/
theorem BlockTriangular.toBlock_pow [DecidableEq m] {M : Matrix m m R} (hM : M.BlockTriangular b)
    (k : α) (p : ℕ) :
    (M ^ p).toBlock (b · = k) (b · = k) = M.toBlock (b · = k) (b · = k) ^ p := by
  induction p with
  | zero => ext i j; simp [one_apply, Subtype.ext_iff]
  | succ p ih => rw [pow_succ, (hM.pow p).toBlock_mul hM, ih, pow_succ]

/-- A block of a product, summed over the block index. -/
theorem toBlock_mul_eq_sum [Fintype α] (M N : Matrix m m R) (k l : α) :
    (M * N).toBlock (b · = k) (b · = l) =
      ∑ r, M.toBlock (b · = k) (b · = r) * N.toBlock (b · = r) (b · = l) := by
  classical
  ext i j
  simp only [toBlock_apply, Matrix.mul_apply, Matrix.sum_apply]
  rw [← Finset.sum_fiberwise Finset.univ b]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_subtype (Finset.univ.filter (b · = r)) (p := (b · = r)) (by simp)]

/-- A block of a product of block triangular matrices only involves the block indices between. -/
theorem BlockTriangular.toBlock_mul_eq_sum_Icc [Finite α] [LocallyFiniteOrder α]
    {M N : Matrix m m R} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (k l : α) :
    (M * N).toBlock (b · = k) (b · = l) =
      ∑ r ∈ Finset.Icc k l, M.toBlock (b · = k) (b · = r) * N.toBlock (b · = r) (b · = l) := by
  have := Fintype.ofFinite α
  rw [toBlock_mul_eq_sum]
  refine (Finset.sum_subset (Finset.subset_univ _) fun r _ hr => ?_).symm
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
  ext i j
  simp only [Matrix.mul_apply, toBlock_apply, zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rcases hr with hr | hr
  · rw [hM (by rw [x.2, i.2]; exact hr), zero_mul]
  · rw [hN (by rw [x.2, j.2]; exact hr), mul_zero]

end BlockTriangular

section Charpoly

variable [Fintype n] [DecidableEq n] [CommRing R]

/-- The characteristic polynomial of a lower triangular matrix is `∏ᵢ (X - a_ii)`, the mirror of
Mathlib's `Matrix.charpoly_of_isUpperTriangular`. -/
theorem charpoly_of_isLowerTriangular (M : Matrix n n R) (hM : M.IsLowerTriangular) :
    M.charpoly = ∏ i, (Polynomial.X - Polynomial.C (M i i)) := by
  simp [charpoly, det_of_isLowerTriangular _ hM.charmatrix]

/-- **The spectrum of an upper triangular matrix is the set of its diagonal entries**, over any
field: `charpoly T = ∏ᵢ (X - Tᵢᵢ)`. -/
theorem IsUpperTriangular.spectrum_eq {K : Type*} [Field K] {T : Matrix n n K}
    (hT : T.IsUpperTriangular) : spectrum K T = Set.range fun i => T i i := by
  ext μ
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_of_isUpperTriangular T hT, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero, Set.mem_range]
  exact exists_congr fun i => eq_comm

/-- The spectrum of a lower triangular matrix is the set of its diagonal entries, the mirror of
`Matrix.IsUpperTriangular.spectrum_eq`. -/
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

/-- An upper triangular matrix is nonsingular exactly when its diagonal has no zero entry
([quarteroni2000numerical] §3.2, first sentence): its determinant is the product of the diagonal. -/
theorem IsUpperTriangular.isUnit_iff {K : Type*} [Field K] {U : Matrix n n K}
    (hU : U.IsUpperTriangular) : IsUnit U ↔ ∀ i, U i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, det_of_isUpperTriangular hU, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  simp

/-- A lower triangular matrix is nonsingular exactly when its diagonal has no zero entry. -/
theorem IsLowerTriangular.isUnit_iff {K : Type*} [Field K] {L : Matrix n n K}
    (hL : L.IsLowerTriangular) : IsUnit L ↔ ∀ i, L i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular L hL, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  simp

@[deprecated (since := "2026-09-30")]
alias isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular := IsUpperTriangular.isUnit_iff

@[deprecated (since := "2026-09-30")]
alias isUnit_iff_forall_diag_ne_zero_of_isLowerTriangular := IsLowerTriangular.isUnit_iff

/-- An upper triangular matrix with no zero on its diagonal has a unit determinant, the form the
substitution and least-squares solvers consume. -/
theorem IsUpperTriangular.isUnit_det_of_diag_ne_zero {K : Type*} [Field K] {U : Matrix n n K}
    (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) : IsUnit U.det :=
  (isUnit_iff_isUnit_det U).1 (hU.isUnit_iff.2 hd)

/-- A lower triangular matrix with no zero on its diagonal has a unit determinant. -/
theorem IsLowerTriangular.isUnit_det_of_diag_ne_zero {K : Type*} [Field K] {L : Matrix n n K}
    (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0) : IsUnit L.det :=
  (isUnit_iff_isUnit_det L).1 (hL.isUnit_iff.2 hd)

variable [DecidableEq n] [CommRing R]

/-- The inverse of an upper triangular matrix is upper triangular. No hypothesis is needed: a
singular matrix has inverse `0`. -/
theorem IsUpperTriangular.inv {U : Matrix n n R} (hU : U.IsUpperTriangular) :
    U⁻¹.IsUpperTriangular := by
  by_cases h : IsUnit U.det
  · have : Invertible U := invertibleOfIsUnitDet U h
    exact blockTriangular_inv_of_blockTriangular hU
  · rw [nonsing_inv_apply_not_isUnit U h]
    exact blockTriangular_zero

/-- The inverse of a lower triangular matrix is lower triangular. -/
theorem IsLowerTriangular.inv {L : Matrix n n R} (hL : L.IsLowerTriangular) :
    L⁻¹.IsLowerTriangular := by
  by_cases h : IsUnit L.det
  · have : Invertible L := invertibleOfIsUnitDet L h
    exact blockTriangular_inv_of_blockTriangular hL
  · rw [nonsing_inv_apply_not_isUnit L h]
    exact blockTriangular_zero

/-- A unitary upper triangular matrix is diagonal: its inverse `Uᴴ` is both upper and lower
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

/-- A unitary lower triangular matrix is diagonal, the transpose of
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

/-- Unit lower triangular: lower triangular with ones on the diagonal, the shape of the `L`
factor of an LU factorization ([quarteroni2000numerical] §1.6.2). -/
structure IsUnitLowerTriangular [Zero R] [One R] (L : Matrix n n R) : Prop where
  /-- The matrix is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- The diagonal entries are `1`. -/
  diag_eq_one : ∀ i, L i i = 1

/-- Unit upper triangular: upper triangular with ones on the diagonal, the dual of
`Matrix.IsUnitLowerTriangular` and the shape of the `U` factor of a `U L` factorization
([golub2013matrix] §3.1.7). -/
structure IsUnitUpperTriangular [Zero R] [One R] (U : Matrix n n R) : Prop where
  /-- The matrix is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- The diagonal entries are `1`. -/
  diag_eq_one : ∀ i, U i i = 1

section Basic

variable [Zero R] [One R] {L U : Matrix n n R}

/-- The identity is unit lower triangular. -/
theorem isUnitLowerTriangular_one : (1 : Matrix n n R).IsUnitLowerTriangular :=
  ⟨blockTriangular_one, fun i => one_apply_eq i⟩

/-- The identity is unit upper triangular. -/
theorem isUnitUpperTriangular_one : (1 : Matrix n n R).IsUnitUpperTriangular :=
  ⟨blockTriangular_one, fun i => one_apply_eq i⟩

/-- Transposition turns a unit upper triangular matrix into a unit lower triangular one. -/
theorem isUnitLowerTriangular_transpose_iff :
    Uᵀ.IsUnitLowerTriangular ↔ U.IsUnitUpperTriangular :=
  ⟨fun h => ⟨fun _ _ hij => h.isLowerTriangular hij, h.diag_eq_one⟩,
    fun h => ⟨fun _ _ hij => h.isUpperTriangular hij, h.diag_eq_one⟩⟩

/-- Transposition turns a unit lower triangular matrix into a unit upper triangular one. -/
theorem isUnitUpperTriangular_transpose_iff :
    Lᵀ.IsUnitUpperTriangular ↔ L.IsUnitLowerTriangular :=
  ⟨fun h => ⟨fun _ _ hij => h.isUpperTriangular hij, h.diag_eq_one⟩,
    fun h => ⟨fun _ _ hij => h.isLowerTriangular hij, h.diag_eq_one⟩⟩

end Basic

variable [Fintype n]

/-- The product of two unit lower triangular matrices is unit lower triangular
([quarteroni2000numerical] §1.6.2, last bullet): the product is lower triangular, and its
diagonal is the product of the two unit diagonals. -/
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

/-- A unit lower triangular matrix has determinant `1`. -/
theorem IsUnitLowerTriangular.det_eq_one [CommRing R] {L : Matrix n n R}
    (hL : L.IsUnitLowerTriangular) : L.det = 1 := by
  rw [det_of_isLowerTriangular L hL.isLowerTriangular]
  exact Finset.prod_eq_one fun i _ => hL.diag_eq_one i

/-- A unit upper triangular matrix has determinant `1`. -/
theorem IsUnitUpperTriangular.det_eq_one [CommRing R] {U : Matrix n n R}
    (hU : U.IsUnitUpperTriangular) : U.det = 1 := by
  rw [det_of_isUpperTriangular hU.isUpperTriangular]
  exact Finset.prod_eq_one fun i _ => hU.diag_eq_one i

/-- A unit lower triangular matrix is a unit. -/
theorem IsUnitLowerTriangular.isUnit [CommRing R] {L : Matrix n n R}
    (hL : L.IsUnitLowerTriangular) : IsUnit L :=
  (isUnit_iff_isUnit_det L).2 (by rw [hL.det_eq_one]; exact isUnit_one)

/-- A unit upper triangular matrix is a unit. -/
theorem IsUnitUpperTriangular.isUnit [CommRing R] {U : Matrix n n R}
    (hU : U.IsUnitUpperTriangular) : IsUnit U :=
  (isUnit_iff_isUnit_det U).2 (by rw [hU.det_eq_one]; exact isUnit_one)

/-- The inverse of a unit lower triangular matrix is unit lower triangular: the inverse of a
lower triangular matrix is lower triangular, and the diagonal of `L⁻¹ * L = 1` is the product of
the diagonals. -/
theorem IsUnitLowerTriangular.inv [CommRing R] {L : Matrix n n R}
    (hL : L.IsUnitLowerTriangular) : L⁻¹.IsUnitLowerTriangular := by
  have : Invertible L := hL.isUnit.invertible
  have hinv : L⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular hL.isLowerTriangular
  refine ⟨hinv, fun i => ?_⟩
  have h := congrFun (congrFun (nonsing_inv_mul L (isUnit_iff_isUnit_det L |>.1 hL.isUnit)) i) i
  rwa [hinv.mul_apply_self hL.isLowerTriangular, hL.diag_eq_one, mul_one, one_apply_eq] at h

/-- The inverse of a unit upper triangular matrix is unit upper triangular, by the same argument
as `Matrix.IsUnitLowerTriangular.inv`. -/
theorem IsUnitUpperTriangular.inv [CommRing R] {U : Matrix n n R}
    (hU : U.IsUnitUpperTriangular) : U⁻¹.IsUnitUpperTriangular := by
  have : Invertible U := hU.isUnit.invertible
  have hinv : U⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular hU.isUpperTriangular
  refine ⟨hinv, fun i => ?_⟩
  have h := congrFun (congrFun (nonsing_inv_mul U (isUnit_iff_isUnit_det U |>.1 hU.isUnit)) i) i
  rwa [hinv.mul_apply_self hU.isUpperTriangular, hU.diag_eq_one, mul_one, one_apply_eq] at h

end UnitTriangular

end Matrix
