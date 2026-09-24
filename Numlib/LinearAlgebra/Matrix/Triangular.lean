/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Block`, beside `Matrix.IsUpperTriangular`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Block

/-!
# Triangular matrices and the triangular parts of a matrix

The vocabulary of triangular matrices beyond Mathlib's `Matrix.IsUpperTriangular` and
`Matrix.IsLowerTriangular` (which are `Matrix.BlockTriangular` for `id` and for
`OrderDual.toDual`), on a matrix indexed by any linearly ordered type.

## Main definitions

* `Matrix.strictLower`, `Matrix.strictUpper`, `Matrix.diagPart`: the three parts a matrix splits
  into, `Matrix.diagPart_add_strictLower_add_strictUpper`, and the signed form `A = D - E - F` of
  the classical splittings behind the Jacobi, Gauss–Seidel and SOR iterations; over a field, the
  diagonal part is a unit exactly when the diagonal has no zero (`Matrix.isUnit_diagPart_iff`),
  and its inverse is then the diagonal of the inverses (`Matrix.inv_diagPart`).
* `Matrix.IsUnitLowerTriangular`, `Matrix.IsUnitUpperTriangular`: triangular with ones on the
  diagonal, the shapes of the factors of an LU factorization and of its `U L` dual. Transposition
  exchanges them (`Matrix.isUnitLowerTriangular_transpose_iff`).

## Main results

* `Matrix.isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular` (and the lower version): a
  triangular matrix is nonsingular exactly when its diagonal has no zero entry, since its
  determinant is the product of the diagonal.
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
  `Matrix.charpoly_of_isUpperTriangular`.

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

end Diag

section Charpoly

variable [Fintype n] [DecidableEq n] [CommRing R]

/-- The characteristic polynomial of a lower triangular matrix is `∏ᵢ (X - a_ii)`, the mirror of
Mathlib's `Matrix.charpoly_of_isUpperTriangular`. -/
theorem charpoly_of_isLowerTriangular (M : Matrix n n R) (hM : M.IsLowerTriangular) :
    M.charpoly = ∏ i, (Polynomial.X - Polynomial.C (M i i)) := by
  simp [charpoly, det_of_isLowerTriangular _ hM.charmatrix]

end Charpoly

/-! ### Nonsingularity and inverses of triangular matrices -/

section Inverse

variable [Fintype n]

/-- An upper triangular matrix is nonsingular exactly when its diagonal has no zero entry
([quarteroni2000numerical] §3.2, first sentence): its determinant is the product of the diagonal. -/
theorem isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular {K : Type*} [Field K]
    {U : Matrix n n K} (hU : U.IsUpperTriangular) : IsUnit U ↔ ∀ i, U i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, det_of_isUpperTriangular hU, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  simp

/-- A lower triangular matrix is nonsingular exactly when its diagonal has no zero entry. -/
theorem isUnit_iff_forall_diag_ne_zero_of_isLowerTriangular {K : Type*} [Field K]
    {L : Matrix n n K} (hL : L.IsLowerTriangular) : IsUnit L ↔ ∀ i, L i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular L hL, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  simp

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
