/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Hessenberg and tridiagonal matrices; triangular parts

Basic predicates on matrices indexed by a linearly ordered type, and the strict lower / strict
upper / diagonal parts used by the classical splittings `A = D - E - F` behind the Jacobi,
Gauss–Seidel and SOR iterations.

## Main definitions

* `Matrix.IsUpperHessenberg`, `Matrix.IsTridiagonal`: zero below the first subdiagonal, and zero
  outside the three central diagonals. Both are stated over a bare `LinearOrder` on the index type,
  as "no index lies strictly between the two", which on `Fin n` is the usual condition on the
  difference of the indices.
* `Matrix.IsUpperHessenbergRect`: the rectangular `(m + 1) × m` form of the same condition, as in
  the matrix `H̄ₘ` of the Arnoldi process.
* `Matrix.strictLower`, `Matrix.strictUpper`, `Matrix.diagPart`: the three parts a matrix splits
  into, `Matrix.diagPart_add_strictLower_add_strictUpper`; over a field, the diagonal part is a
  unit exactly when the diagonal has no zero (`Matrix.isUnit_diagPart_iff`), and its inverse is
  then the diagonal of the inverses (`Matrix.inv_diagPart`).

## Implementation notes

Mathlib's `Matrix.BlockTriangular M b` unfolds to `b j < b i → M i j = 0`, so `BlockTriangular ·
id` is *upper* triangularity (`Matrix.IsUpperTriangular`) and the lower-triangular statement is
the one for `OrderDual.toDual`. That is why `Matrix.strictLower_blockTriangular` and
`Matrix.strictUpper_blockTriangular` are stated with different order maps.

## Bandwidths and the named shapes

* `Matrix.HasLowerBandwidth A p`, `Matrix.HasUpperBandwidth A q`: an entry `A i j` vanishes as soon
  as more than `p` indices lie in `[j, i)` (respectively more than `q` in `[i, j)`). On `Fin N` the
  count is `i - j`, so these are the conditions `i > j + p` and `j > i + q` of
  [quarteroni2000numerical] §1.6.3 (`Matrix.hasLowerBandwidth_iff_fin`); on a general finite
  linear order they need no arithmetic on the indices, in the spirit of `Matrix.IsUpperHessenberg`.
  Bands `0` are the triangular shapes, bands `1` the Hessenberg and tridiagonal ones
  (`Matrix.hasLowerBandwidth_zero_iff`, `Matrix.isTridiagonal_iff_hasBandwidth_one`), sums keep
  the larger band and products add bands (`Matrix.HasLowerBandwidth.mul`), which is how `L U` is
  read back in banded storage.
* `Matrix.IsUpperBidiagonal`, `Matrix.IsLowerBidiagonal`: the two bidiagonal shapes, the shape of
  the Golub–Kahan bidiagonalization and of the factors of a tridiagonal matrix.
* `Matrix.IsUnitLowerTriangular`: lower triangular with unit diagonal, the shape of the `L`
  factor of an LU factorization; closed under products and inverses because the diagonal of a
  product of two triangular matrices is the product of the diagonals
  (`Matrix.BlockTriangular.mul_apply_self_of_injective`).
* `Matrix.tridiagonalOf b d c`: the tridiagonal matrix `tridiag(b, d, c)` with the given
  subdiagonal, diagonal and superdiagonal, on `Fin (N + 1)`, with its three-term product formula
  `Matrix.tridiagonalOf_mulVec`.
-/


namespace Matrix

variable {n R : Type*} [LinearOrder n]

/-- Upper Hessenberg: zero below the first subdiagonal. "Below the first subdiagonal" is spelled
as "some index lies strictly between the column and the row", which needs no arithmetic on the
index type and is the usual condition `j + 1 < i` on `Fin n`. -/
def IsUpperHessenberg [Zero R] (H : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, j < k ∧ k < i) → H i j = 0

/-- Tridiagonal: zero outside the three central diagonals, that is, upper Hessenberg together with
its mirror image above the first superdiagonal. -/
def IsTridiagonal [Zero R] (T : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, j < k ∧ k < i) ∨ (∃ k, i < k ∧ k < j) → T i j = 0

/-- A tridiagonal matrix is upper Hessenberg: tridiagonality is the Hessenberg condition together
with its mirror image above the first superdiagonal, so it is the stronger of the two. -/
theorem IsTridiagonal.isUpperHessenberg [Zero R] {T : Matrix n n R} (hT : T.IsTridiagonal) :
    T.IsUpperHessenberg := fun i j h => hT i j (Or.inl h)

/-- Rectangular upper Hessenberg (`(m+1) × m`, as in Arnoldi's `H̄_m`). -/
def IsUpperHessenbergRect [Zero R] {m : ℕ} (H : Matrix (Fin (m + 1)) (Fin m) R) : Prop :=
  ∀ (i : Fin (m + 1)) (j : Fin m), (j : ℕ) + 1 < (i : ℕ) → H i j = 0

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

section Bidiagonal

variable [Zero R]

/-- Upper bidiagonal: zero off the diagonal and the first superdiagonal. As in
`Matrix.IsTridiagonal`, "on the first superdiagonal" is spelled as "no index lies strictly between
the row and the column". This is the shape of the Golub–Kahan bidiagonalization
([quarteroni2000numerical] (5.57)) and of the `U` factor of a tridiagonal matrix. -/
def IsUpperBidiagonal (B : Matrix n n R) : Prop :=
  ∀ i j, j < i ∨ (∃ k, i < k ∧ k < j) → B i j = 0

/-- Lower bidiagonal: zero off the diagonal and the first subdiagonal, the shape of the `L` factor
of a tridiagonal matrix. -/
def IsLowerBidiagonal (B : Matrix n n R) : Prop :=
  ∀ i j, i < j ∨ (∃ k, j < k ∧ k < i) → B i j = 0

/-- An upper bidiagonal matrix is upper triangular. -/
theorem IsUpperBidiagonal.isUpperTriangular {B : Matrix n n R} (hB : B.IsUpperBidiagonal) :
    B.IsUpperTriangular := fun i j h => hB i j (Or.inl h)

/-- An upper bidiagonal matrix is tridiagonal. -/
theorem IsUpperBidiagonal.isTridiagonal {B : Matrix n n R} (hB : B.IsUpperBidiagonal) :
    B.IsTridiagonal := fun i j h =>
  hB i j (h.imp_left fun ⟨_, hk⟩ => hk.1.trans hk.2)

/-- The transpose of an upper bidiagonal matrix is upper Hessenberg. -/
theorem IsUpperBidiagonal.transpose_isUpperHessenberg {B : Matrix n n R}
    (hB : B.IsUpperBidiagonal) : Bᵀ.IsUpperHessenberg := fun i j h => hB j i (Or.inr h)

/-- A lower bidiagonal matrix is lower triangular. -/
theorem IsLowerBidiagonal.isLowerTriangular {B : Matrix n n R} (hB : B.IsLowerBidiagonal) :
    B.IsLowerTriangular := fun i j h => hB i j (Or.inl h)

/-- A lower bidiagonal matrix is tridiagonal. -/
theorem IsLowerBidiagonal.isTridiagonal {B : Matrix n n R} (hB : B.IsLowerBidiagonal) :
    B.IsTridiagonal := fun i j h =>
  hB i j (h.symm.imp_left fun ⟨_, hk⟩ => hk.1.trans hk.2)

/-- A lower bidiagonal matrix is upper Hessenberg. -/
theorem IsLowerBidiagonal.isUpperHessenberg {B : Matrix n n R} (hB : B.IsLowerBidiagonal) :
    B.IsUpperHessenberg := hB.isTridiagonal.isUpperHessenberg

/-- Transposition exchanges the two bidiagonal shapes. -/
theorem isLowerBidiagonal_transpose_iff {B : Matrix n n R} :
    Bᵀ.IsLowerBidiagonal ↔ B.IsUpperBidiagonal :=
  ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

/-- Transposition exchanges the two bidiagonal shapes. -/
theorem isUpperBidiagonal_transpose_iff {B : Matrix n n R} :
    Bᵀ.IsUpperBidiagonal ↔ B.IsLowerBidiagonal :=
  ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

end Bidiagonal

section Hermitian

/-- A symmetric upper Hessenberg matrix is tridiagonal: an entry above the first superdiagonal is
the mirror image of one below the first subdiagonal, which is zero ([quarteroni2000numerical]
Remark 5.4). -/
theorem IsUpperHessenberg.isTridiagonal_of_isSymm [Zero R] {H : Matrix n n R}
    (hH : H.IsUpperHessenberg) (hs : H.IsSymm) : H.IsTridiagonal := fun i j h => by
  rcases h with h | h
  · exact hH i j h
  · rw [← hs.apply i j]
    exact hH j i h

/-- A Hermitian upper Hessenberg matrix is tridiagonal ([quarteroni2000numerical] Remark 5.4). -/
theorem IsUpperHessenberg.isTridiagonal_of_isHermitian [AddMonoid R] [StarAddMonoid R]
    {H : Matrix n n R} (hH : H.IsUpperHessenberg) (hs : H.IsHermitian) : H.IsTridiagonal :=
  fun i j h => by
  rcases h with h | h
  · exact hH i j h
  · rw [← hs.apply i j, hH j i h, star_zero]

end Hermitian

section Diag

variable {α : Type*} [LinearOrder α] {b : n → α} [Fintype n] [NonUnitalNonAssocSemiring R]

omit [LinearOrder n] in
/-- The diagonal of a product of two block triangular matrices with singleton blocks is the
product of the diagonals: in `∑ k, M i k * N k i` every term with `k ≠ i` has `b k ≠ b i`, and one
of the two factors then vanishes. -/
theorem BlockTriangular.mul_apply_self_of_injective {M N : Matrix n n R}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (hb : Function.Injective b) (i : n) :
    (M * N) i i = M i i * N i i := by
  rw [mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne (hb.ne hk) with h | h
  · rw [hM h, zero_mul]
  · rw [hN h, mul_zero]

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

end Diag

section Charpoly

variable [Fintype n] [DecidableEq n] [CommRing R]

/-- The characteristic polynomial of a lower triangular matrix is `∏ᵢ (X - a_ii)`, the mirror of
Mathlib's `Matrix.charpoly_of_isUpperTriangular`. -/
theorem charpoly_of_isLowerTriangular (M : Matrix n n R) (hM : M.IsLowerTriangular) :
    M.charpoly = ∏ i, (Polynomial.X - Polynomial.C (M i i)) := by
  simp [charpoly, det_of_isLowerTriangular _ hM.charmatrix]

end Charpoly

section UnitLowerTriangular

/-- Unit lower triangular: lower triangular with ones on the diagonal, the shape of the `L`
factor of an LU factorization ([quarteroni2000numerical] §1.6.2). -/
structure IsUnitLowerTriangular [Zero R] [One R] (L : Matrix n n R) : Prop where
  /-- The matrix is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- The diagonal entries are `1`. -/
  diag_eq_one : ∀ i, L i i = 1

/-- The identity is unit lower triangular. -/
theorem isUnitLowerTriangular_one [Zero R] [One R] : (1 : Matrix n n R).IsUnitLowerTriangular :=
  ⟨blockTriangular_one, fun i => one_apply_eq i⟩

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

/-- A unit lower triangular matrix has determinant `1`. -/
theorem IsUnitLowerTriangular.det_eq_one [CommRing R] {L : Matrix n n R}
    (hL : L.IsUnitLowerTriangular) : L.det = 1 := by
  rw [det_of_isLowerTriangular L hL.isLowerTriangular]
  exact Finset.prod_eq_one fun i _ => hL.diag_eq_one i

/-- A unit lower triangular matrix is a unit. -/
theorem IsUnitLowerTriangular.isUnit [CommRing R] {L : Matrix n n R}
    (hL : L.IsUnitLowerTriangular) : IsUnit L :=
  (isUnit_iff_isUnit_det L).2 (by rw [hL.det_eq_one]; exact isUnit_one)

/-- The inverse of an upper triangular matrix is upper triangular. No hypothesis is needed: a
singular matrix has inverse `0`. -/
theorem IsUpperTriangular.inv [CommRing R] [DecidableEq n] {U : Matrix n n R}
    (hU : U.IsUpperTriangular) : U⁻¹.IsUpperTriangular := by
  by_cases h : IsUnit U.det
  · have : Invertible U := invertibleOfIsUnitDet U h
    exact blockTriangular_inv_of_blockTriangular hU
  · rw [nonsing_inv_apply_not_isUnit U h]
    exact blockTriangular_zero

/-- The inverse of a lower triangular matrix is lower triangular. -/
theorem IsLowerTriangular.inv [CommRing R] [DecidableEq n] {L : Matrix n n R}
    (hL : L.IsLowerTriangular) : L⁻¹.IsLowerTriangular := by
  by_cases h : IsUnit L.det
  · have : Invertible L := invertibleOfIsUnitDet L h
    exact blockTriangular_inv_of_blockTriangular hL
  · rw [nonsing_inv_apply_not_isUnit L h]
    exact blockTriangular_zero

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

end UnitLowerTriangular

section Bandwidth

open Finset

variable [Fintype n]

/-- Counting indices in a half-open interval, on a finite linear order. -/
theorem card_filter_le_lt_pos_iff (i j : n) :
    0 < #{k | j ≤ k ∧ k < i} ↔ j < i := by
  rw [Finset.card_pos]
  constructor
  · rintro ⟨k, hk⟩
    simp only [mem_filter, mem_univ, true_and] at hk
    exact hk.1.trans_lt hk.2
  · intro h
    exact ⟨j, by simp [h]⟩

/-- More than one index lies in `[j, i)` exactly when some index lies strictly between `j` and
`i`. -/
theorem one_lt_card_filter_le_lt_iff (i j : n) :
    1 < #{k | j ≤ k ∧ k < i} ↔ ∃ k, j < k ∧ k < i := by
  rw [Finset.one_lt_card]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [mem_filter, mem_univ, true_and] at ha hb
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨b, ha.1.trans_lt h, hb.2⟩
    · exact ⟨a, hb.1.trans_lt h, ha.2⟩
  · rintro ⟨k, hk₁, hk₂⟩
    exact ⟨j, by simp [hk₁.trans hk₂], k, by simp [hk₁.le, hk₂], hk₁.ne⟩

/-- The interval `[j, i)` is covered by `[j, l)` and `[l, i)`, whatever `l` is. -/
theorem card_filter_le_lt_le_add (i j l : n) :
    #{k | j ≤ k ∧ k < i} ≤ #{k | j ≤ k ∧ k < l} + #{k | l ≤ k ∧ k < i} := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro k hk
  simp only [mem_filter, mem_univ, true_and, mem_union] at hk ⊢
  rcases lt_or_ge k l with h | h
  · exact Or.inl ⟨hk.1, h⟩
  · exact Or.inr ⟨h, hk.2⟩

/-- A larger interval holds more indices. -/
theorem card_filter_le_lt_mono {i i' j j' : n} (hj : j' ≤ j) (hi : i ≤ i') :
    #{k | j ≤ k ∧ k < i} ≤ #{k | j' ≤ k ∧ k < i'} := by
  refine Finset.card_le_card fun k hk => ?_
  simp only [mem_filter, mem_univ, true_and] at hk ⊢
  exact ⟨hj.trans hk.1, hk.2.trans_le hi⟩

/-- The interval `[j, i)` misses `i`, so it holds at most `card n - 1` indices. -/
theorem card_filter_le_lt_le_card_sub_one (i j : n) :
    #{k | j ≤ k ∧ k < i} ≤ Fintype.card n - 1 := by
  rw [← Finset.card_univ, ← Finset.card_erase_of_mem (mem_univ i)]
  refine Finset.card_le_card fun k hk => ?_
  simp only [mem_filter, mem_univ, true_and, mem_erase, and_true] at hk ⊢
  exact hk.2.ne

/-- On `Fin N`, the interval `[j, i)` holds `i - j` indices. -/
theorem card_filter_le_lt_fin {N : ℕ} (i j : Fin N) : #{k | j ≤ k ∧ k < i} = i - j := by
  rw [← Fin.card_Ico]
  congr 1
  ext k
  simp [Finset.mem_Ico]

variable [Zero R]

/-- `A.HasLowerBandwidth p`: an entry `A i j` vanishes as soon as more than `p` indices lie in the
half-open interval `[j, i)`. On `Fin N` the count is `i - j`, so this is the condition `i > j + p`
of [quarteroni2000numerical] §1.6.3 (`Matrix.hasLowerBandwidth_iff_fin`); `p = 0` is upper
triangularity and `p = 1` the upper Hessenberg shape. -/
def HasLowerBandwidth (A : Matrix n n R) (p : ℕ) : Prop :=
  ∀ i j, p < #{k | j ≤ k ∧ k < i} → A i j = 0

/-- `A.HasUpperBandwidth q`: an entry `A i j` vanishes as soon as more than `q` indices lie in
`[i, j)`, the condition `j > i + q` of [quarteroni2000numerical] §1.6.3; `q = 0` is lower
triangularity. It is the lower bandwidth of the transpose
(`Matrix.hasUpperBandwidth_iff_transpose`). -/
def HasUpperBandwidth (A : Matrix n n R) (q : ℕ) : Prop :=
  ∀ i j, q < #{k | i ≤ k ∧ k < j} → A i j = 0

variable {A B : Matrix n n R} {p q : ℕ}

/-- The upper bandwidth of a matrix is the lower bandwidth of its transpose. -/
theorem hasUpperBandwidth_iff_transpose : A.HasUpperBandwidth q ↔ Aᵀ.HasLowerBandwidth q :=
  forall_comm

/-- The lower bandwidth of a matrix is the upper bandwidth of its transpose. -/
theorem hasLowerBandwidth_iff_transpose : A.HasLowerBandwidth p ↔ Aᵀ.HasUpperBandwidth p :=
  forall_comm

/-- On `Fin N`, lower bandwidth `p` is the usual condition: `A i j = 0` whenever `i > j + p`. -/
theorem hasLowerBandwidth_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.HasLowerBandwidth p ↔ ∀ i j : Fin N, (j : ℕ) + p < (i : ℕ) → A i j = 0 := by
  simp only [HasLowerBandwidth, card_filter_le_lt_fin]
  exact forall₂_congr fun i j => by constructor <;> intro h hij <;> apply h <;> omega

/-- On `Fin N`, upper bandwidth `q` is the usual condition: `A i j = 0` whenever `j > i + q`. -/
theorem hasUpperBandwidth_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.HasUpperBandwidth q ↔ ∀ i j : Fin N, (i : ℕ) + q < (j : ℕ) → A i j = 0 := by
  simp only [HasUpperBandwidth, card_filter_le_lt_fin]
  exact forall₂_congr fun i j => by constructor <;> intro h hij <;> apply h <;> omega

/-- A band is a band for every larger width. -/
theorem HasLowerBandwidth.mono (h : A.HasLowerBandwidth p) (hpq : p ≤ q) :
    A.HasLowerBandwidth q := fun i j hij => h i j (hpq.trans_lt hij)

/-- A band is a band for every larger width. -/
theorem HasUpperBandwidth.mono (h : A.HasUpperBandwidth p) (hpq : p ≤ q) :
    A.HasUpperBandwidth q := fun i j hij => h i j (hpq.trans_lt hij)

/-- Every matrix has lower bandwidth `card n - 1`. -/
theorem hasLowerBandwidth_card_sub_one : A.HasLowerBandwidth (Fintype.card n - 1) :=
  fun i j hij => absurd (card_filter_le_lt_le_card_sub_one i j) (not_le.2 hij)

/-- Every matrix has upper bandwidth `card n - 1`. -/
theorem hasUpperBandwidth_card_sub_one : A.HasUpperBandwidth (Fintype.card n - 1) :=
  fun i j hij => absurd (card_filter_le_lt_le_card_sub_one j i) (not_le.2 hij)

/-- Lower bandwidth `0` is upper triangularity ([quarteroni2000numerical] §1.6.2–1.6.3). -/
theorem hasLowerBandwidth_zero_iff : A.HasLowerBandwidth 0 ↔ A.IsUpperTriangular := by
  simp only [HasLowerBandwidth, card_filter_le_lt_pos_iff]
  exact ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

/-- Upper bandwidth `0` is lower triangularity. -/
theorem hasUpperBandwidth_zero_iff : A.HasUpperBandwidth 0 ↔ A.IsLowerTriangular := by
  simp only [HasUpperBandwidth, card_filter_le_lt_pos_iff]
  exact ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

/-- A matrix is diagonal exactly when both its bandwidths are `0`. -/
theorem isDiag_iff_hasBandwidth_zero :
    A.IsDiag ↔ A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 0 := by
  rw [hasLowerBandwidth_zero_iff, hasUpperBandwidth_zero_iff]
  refine ⟨fun h => ⟨fun i j hij => h (hij : j < i).ne',
    fun i j hij => h (OrderDual.toDual_lt_toDual.1 hij).ne⟩, fun h i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact h.2 hlt
  · exact h.1 hlt

/-- Lower bandwidth `1` is the upper Hessenberg shape. -/
theorem isUpperHessenberg_iff_hasLowerBandwidth_one :
    A.IsUpperHessenberg ↔ A.HasLowerBandwidth 1 := by
  simp only [HasLowerBandwidth, one_lt_card_filter_le_lt_iff]
  rfl

/-- On `Fin N`, upper Hessenberg is the condition `A i j = 0` for `j + 1 < i`. -/
theorem isUpperHessenberg_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsUpperHessenberg ↔ ∀ i j : Fin N, (j : ℕ) + 1 < (i : ℕ) → A i j = 0 := by
  rw [isUpperHessenberg_iff_hasLowerBandwidth_one, hasLowerBandwidth_iff_fin]

/-- Tridiagonal means both bandwidths are `1` ([quarteroni2000numerical] §1.6.3). -/
theorem isTridiagonal_iff_hasBandwidth_one :
    A.IsTridiagonal ↔ A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 1 := by
  simp only [HasLowerBandwidth, HasUpperBandwidth, one_lt_card_filter_le_lt_iff]
  exact ⟨fun h => ⟨fun i j hij => h i j (Or.inl hij), fun i j hij => h i j (Or.inr hij)⟩,
    fun h i j hij => hij.elim (h.1 i j) (h.2 i j)⟩

/-- A lower bidiagonal matrix has bandwidths `1` and `0`. -/
theorem IsLowerBidiagonal.hasBandwidth (hB : A.IsLowerBidiagonal) :
    A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 0 :=
  ⟨(isTridiagonal_iff_hasBandwidth_one.1 hB.isTridiagonal).1,
    hasUpperBandwidth_zero_iff.2 hB.isLowerTriangular⟩

/-- An upper bidiagonal matrix has bandwidths `0` and `1`. -/
theorem IsUpperBidiagonal.hasBandwidth (hB : A.IsUpperBidiagonal) :
    A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 1 :=
  ⟨hasLowerBandwidth_zero_iff.2 hB.isUpperTriangular,
    (isTridiagonal_iff_hasBandwidth_one.1 hB.isTridiagonal).2⟩

/-- The strict lower part inherits the lower bandwidth. -/
theorem HasLowerBandwidth.strictLower (h : A.HasLowerBandwidth p) :
    (strictLower A).HasLowerBandwidth p := fun i j hij => by
  rw [strictLower_apply, h i j hij, ite_self]

/-- The strict upper part inherits the upper bandwidth. -/
theorem HasUpperBandwidth.strictUpper (h : A.HasUpperBandwidth q) :
    (strictUpper A).HasUpperBandwidth q := fun i j hij => by
  rw [strictUpper_apply, h i j hij, ite_self]

/-- The strict upper part has lower bandwidth `0`. -/
theorem strictUpper_hasLowerBandwidth_zero : (strictUpper A).HasLowerBandwidth 0 :=
  hasLowerBandwidth_zero_iff.2 (strictUpper_blockTriangular A)

/-- The strict lower part has upper bandwidth `0`. -/
theorem strictLower_hasUpperBandwidth_zero : (strictLower A).HasUpperBandwidth 0 :=
  hasUpperBandwidth_zero_iff.2 (strictLower_blockTriangular A)

/-- The diagonal part has lower bandwidth `0`. -/
theorem diagPart_hasLowerBandwidth_zero : (diagPart A).HasLowerBandwidth 0 :=
  hasLowerBandwidth_zero_iff.2 (blockTriangular_diagonal _)

/-- The diagonal part has upper bandwidth `0`. -/
theorem diagPart_hasUpperBandwidth_zero : (diagPart A).HasUpperBandwidth 0 :=
  hasUpperBandwidth_zero_iff.2 (blockTriangular_diagonal _)

end Bandwidth

section BandwidthAlgebra

open Finset

variable [Fintype n] {p p' q q' : ℕ}

/-- Sums keep the larger lower bandwidth. -/
theorem HasLowerBandwidth.add [AddZeroClass R] {A B : Matrix n n R} (hA : A.HasLowerBandwidth p)
    (hB : B.HasLowerBandwidth p') : (A + B).HasLowerBandwidth (max p p') := fun i j hij => by
  rw [add_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), add_zero]

/-- Sums keep the larger upper bandwidth. -/
theorem HasUpperBandwidth.add [AddZeroClass R] {A B : Matrix n n R} (hA : A.HasUpperBandwidth q)
    (hB : B.HasUpperBandwidth q') : (A + B).HasUpperBandwidth (max q q') := fun i j hij => by
  rw [add_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), add_zero]

/-- Scalar multiples keep the lower bandwidth. -/
theorem HasLowerBandwidth.smul {S : Type*} [Zero R] [SMulZeroClass S R] {A : Matrix n n R}
    (hA : A.HasLowerBandwidth p) (c : S) : (c • A).HasLowerBandwidth p := fun i j hij => by
  rw [smul_apply, hA i j hij, smul_zero]

/-- Scalar multiples keep the upper bandwidth. -/
theorem HasUpperBandwidth.smul {S : Type*} [Zero R] [SMulZeroClass S R] {A : Matrix n n R}
    (hA : A.HasUpperBandwidth q) (c : S) : (c • A).HasUpperBandwidth q := fun i j hij => by
  rw [smul_apply, hA i j hij, smul_zero]

/-- Negation keeps the lower bandwidth. -/
theorem HasLowerBandwidth.neg [NegZeroClass R] {A : Matrix n n R} (hA : A.HasLowerBandwidth p) :
    (-A).HasLowerBandwidth p := fun i j hij => by rw [neg_apply, hA i j hij, neg_zero]

/-- Negation keeps the upper bandwidth. -/
theorem HasUpperBandwidth.neg [NegZeroClass R] {A : Matrix n n R} (hA : A.HasUpperBandwidth q) :
    (-A).HasUpperBandwidth q := fun i j hij => by rw [neg_apply, hA i j hij, neg_zero]

/-- Differences keep the larger lower bandwidth. -/
theorem HasLowerBandwidth.sub [SubNegZeroMonoid R] {A B : Matrix n n R}
    (hA : A.HasLowerBandwidth p) (hB : B.HasLowerBandwidth p') :
    (A - B).HasLowerBandwidth (max p p') := fun i j hij => by
  rw [sub_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), sub_zero]

/-- Differences keep the larger upper bandwidth. -/
theorem HasUpperBandwidth.sub [SubNegZeroMonoid R] {A B : Matrix n n R}
    (hA : A.HasUpperBandwidth q) (hB : B.HasUpperBandwidth q') :
    (A - B).HasUpperBandwidth (max q q') := fun i j hij => by
  rw [sub_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), sub_zero]

variable [NonUnitalNonAssocSemiring R] {A B : Matrix n n R}

/-- Bandwidths add under products ([quarteroni2000numerical] §1.6.3): in `∑ k, A i k * B k j`, a
nonzero term needs at most `p` indices in `[k, i)` and at most `p'` in `[j, k)`, and these two
intervals cover `[j, i)`. -/
theorem HasLowerBandwidth.mul (hA : A.HasLowerBandwidth p) (hB : B.HasLowerBandwidth p') :
    (A * B).HasLowerBandwidth (p + p') := fun i j hij => by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : p < #{l | k ≤ l ∧ l < i}
  · rw [hA i k hk, zero_mul]
  · rw [hB k j, mul_zero]
    have := card_filter_le_lt_le_add i j k
    omega

/-- Bandwidths add under products, the upper version. -/
theorem HasUpperBandwidth.mul (hA : A.HasUpperBandwidth q) (hB : B.HasUpperBandwidth q') :
    (A * B).HasUpperBandwidth (q + q') := fun i j hij => by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : q < #{l | i ≤ l ∧ l < k}
  · rw [hA i k hk, zero_mul]
  · rw [hB k j, mul_zero]
    have := card_filter_le_lt_le_add j i k
    omega

/-- An upper triangular matrix times an upper Hessenberg matrix is upper Hessenberg
([quarteroni2000numerical] §5.6.4, `R Q` in the QR iteration): bandwidths `0` and `1` add up to
`1`. -/
theorem IsUpperTriangular.mul_isUpperHessenberg {T H : Matrix n n R} (hT : T.IsUpperTriangular)
    (hH : H.IsUpperHessenberg) : (T * H).IsUpperHessenberg :=
  isUpperHessenberg_iff_hasLowerBandwidth_one.2 <| by
    simpa using (hasLowerBandwidth_zero_iff.2 hT).mul
      (isUpperHessenberg_iff_hasLowerBandwidth_one.1 hH)

/-- An upper Hessenberg matrix times an upper triangular matrix is upper Hessenberg
([quarteroni2000numerical] §5.6.3, `Q = H R⁻¹`). -/
theorem IsUpperHessenberg.mul_isUpperTriangular {H T : Matrix n n R} (hH : H.IsUpperHessenberg)
    (hT : T.IsUpperTriangular) : (H * T).IsUpperHessenberg :=
  isUpperHessenberg_iff_hasLowerBandwidth_one.2 <| by
    simpa using (isUpperHessenberg_iff_hasLowerBandwidth_one.1 hH).mul
      (hasLowerBandwidth_zero_iff.2 hT)

end BandwidthAlgebra

section TridiagonalOf

open Finset

variable {S : Type*} [Zero R] {N : ℕ}

/-- The tridiagonal matrix `tridiag(b, d, c)` of [quarteroni2000numerical] §1.6.3: `d` on the
diagonal, `b` on the subdiagonal (`b i` at `(i + 1, i)`) and `c` on the superdiagonal (`c i` at
`(i, i + 1)`), zero elsewhere. The book's `b₁, …, b_{n-1}`, `d₁, …, d_n` are `0`-indexed here, on
`Fin (N + 1)`. -/
def tridiagonalOf (b : Fin N → R) (d : Fin (N + 1) → R) (c : Fin N → R) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then d i
    else if h : (i : ℕ) = j + 1 then b ⟨j, by omega⟩
    else if h' : (j : ℕ) = i + 1 then c ⟨i, by omega⟩
    else 0

variable (b : Fin N → R) (d : Fin (N + 1) → R) (c : Fin N → R)

/-- The diagonal of `tridiag(b, d, c)`. -/
@[simp]
theorem tridiagonalOf_apply_self (i : Fin (N + 1)) : tridiagonalOf b d c i i = d i := by
  simp [tridiagonalOf]

/-- The subdiagonal of `tridiag(b, d, c)`. -/
@[simp]
theorem tridiagonalOf_apply_succ_castSucc (i : Fin N) :
    tridiagonalOf b d c i.succ i.castSucc = b i := by
  simp [tridiagonalOf]

/-- The superdiagonal of `tridiag(b, d, c)`. -/
@[simp]
theorem tridiagonalOf_apply_castSucc_succ (i : Fin N) :
    tridiagonalOf b d c i.castSucc i.succ = c i := by
  have h : (i : ℕ) ≠ i + 1 + 1 := by omega
  simp [tridiagonalOf, h]

/-- Away from the three central diagonals, `tridiag(b, d, c)` vanishes. -/
theorem tridiagonalOf_apply_of_ne {i j : Fin (N + 1)} (hij : (i : ℕ) ≠ j)
    (h₁ : (i : ℕ) ≠ j + 1) (h₂ : (j : ℕ) ≠ i + 1) : tridiagonalOf b d c i j = 0 := by
  simp [tridiagonalOf, hij, h₁, h₂]

/-- `tridiag(b, d, c)` is tridiagonal. -/
theorem isTridiagonal_tridiagonalOf : (tridiagonalOf b d c).IsTridiagonal := by
  intro i j h
  refine tridiagonalOf_apply_of_ne b d c ?_ ?_ ?_ <;>
    rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp only [Fin.lt_def] at hk <;> omega

/-- Transposition exchanges the two off-diagonals. -/
theorem tridiagonalOf_transpose : (tridiagonalOf b d c)ᵀ = tridiagonalOf c d b := by
  ext i j
  simp only [transpose_apply, tridiagonalOf, of_apply]
  split_ifs <;> first | rfl | omega | exact congrArg d (Fin.ext (by omega))

/-- Each term of `(tridiag(b, d, c) * x) i`, split into its three possible contributions. -/
theorem tridiagonalOf_apply_mul_eq [NonUnitalNonAssocSemiring S]
    (b : Fin N → S) (d : Fin (N + 1) → S) (c : Fin N → S) (x : Fin (N + 1) → S)
    (i j : Fin (N + 1)) :
    tridiagonalOf b d c i j * x j =
      (if j = i then d i * x i else 0) +
        (if h : (j : ℕ) + 1 = i then b ⟨j, by omega⟩ * x j else 0) +
        (if h : (j : ℕ) = i + 1 then c ⟨i, by omega⟩ * x j else 0) := by
  by_cases hij : i = j
  · subst hij
    simp [tridiagonalOf]
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp only [tridiagonalOf, of_apply, hij', ite_false, Ne.symm hij]
    split_ifs <;> first | omega | simp

/-- A sum over `Fin M` supported at the predecessor of `i`. -/
theorem sum_dite_val_add_one_eq {S : Type*} [AddCommMonoid S] {M : ℕ} (i : Fin M)
    (f : (j : Fin M) → (j : ℕ) + 1 = i → S) :
    ∑ j : Fin M, (if h : (j : ℕ) + 1 = i then f j h else 0) =
      if h : 0 < (i : ℕ) then f ⟨i - 1, by omega⟩ (by simp; omega) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i - 1, by omega⟩]
    · have h' : ((⟨i - 1, by omega⟩ : Fin M) : ℕ) + 1 = i := by simp; omega
      simp only [h', dite_true]
    · intro j _ hj
      have h' : ¬ ((j : ℕ) + 1 = i) := fun h' => hj (Fin.ext (by simp; omega))
      simp only [h', dite_false]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have h' : ¬ ((j : ℕ) + 1 = i) := by omega
    simp only [h', dite_false]

/-- A sum over `Fin M` supported at the successor of `i`. -/
theorem sum_dite_val_eq_add_one {S : Type*} [AddCommMonoid S] {M : ℕ} (i : Fin M)
    (f : (j : Fin M) → (j : ℕ) = i + 1 → S) :
    ∑ j : Fin M, (if h : (j : ℕ) = i + 1 then f j h else 0) =
      if h : (i : ℕ) + 1 < M then f ⟨i + 1, h⟩ rfl else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i + 1, by omega⟩]
    · simp only [dite_true]
    · intro j _ hj
      have h' : ¬ ((j : ℕ) = i + 1) := fun h' => hj (Fin.ext (by simp; omega))
      simp only [h', dite_false]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have h' : ¬ ((j : ℕ) = i + 1) := by omega
    simp only [h', dite_false]

/-- The three-term formula `(T x)ᵢ = bᵢ₋₁ xᵢ₋₁ + dᵢ xᵢ + cᵢ xᵢ₊₁` for `T = tridiag(b, d, c)`, with
the boundary terms absent at `i = 0` and `i = N`. -/
theorem tridiagonalOf_mulVec [NonUnitalNonAssocSemiring S]
    (b : Fin N → S) (d : Fin (N + 1) → S) (c : Fin N → S) (x : Fin (N + 1) → S)
    (i : Fin (N + 1)) :
    (tridiagonalOf b d c *ᵥ x) i =
      (if h : 0 < (i : ℕ) then b ⟨i - 1, by omega⟩ * x ⟨i - 1, by omega⟩ else 0) +
        d i * x i +
        (if h : (i : ℕ) < N then c ⟨i, h⟩ * x ⟨i + 1, by omega⟩ else 0) := by
  simp only [mulVec, dotProduct, tridiagonalOf_apply_mul_eq, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_dite_val_add_one_eq,
    sum_dite_val_eq_add_one]
  split_ifs <;> first | omega | abel

end TridiagonalOf

/-! ### The rectangular product rule -/

section Rectangular

/-- **The rectangular product rule** behind the trapezoidal shapes, the rectangular form of
`Matrix.BlockTriangular.mul` with a block map on each of the three index types: if `A i k = 0`
whenever `c k < b i` and `B k j = 0` whenever `d j < c k`, then `(A * B) i j = 0` whenever
`d j < b i`, because every term `A i k * B k j` of the product has `c k < b i` or
`d j < b i ≤ c k`. -/
theorem mul_apply_eq_zero_of_lt {α l m n R : Type*} [LinearOrder α] [Fintype m]
    [NonUnitalNonAssocSemiring R] {b : l → α} {c : m → α} {d : n → α} {A : Matrix l m R}
    {B : Matrix m n R} (hA : ∀ i k, c k < b i → A i k = 0) (hB : ∀ k j, d j < c k → B k j = 0)
    {i : l} {j : n} (hij : d j < b i) : (A * B) i j = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (c k) (b i) with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k j (hij.trans_le h), mul_zero]

end Rectangular

end Matrix
