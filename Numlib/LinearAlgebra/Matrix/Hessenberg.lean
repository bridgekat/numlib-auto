/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Block

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
  into, `Matrix.diagPart_add_strictLower_add_strictUpper`.

## Implementation notes

Mathlib's `Matrix.BlockTriangular M b` unfolds to `b j < b i → M i j = 0`, so `BlockTriangular ·
id` is *upper* triangularity (`Matrix.IsUpperTriangular`) and the lower-triangular statement is
the one for `OrderDual.toDual`. That is why `Matrix.strictLower_blockTriangular` and
`Matrix.strictUpper_blockTriangular` are stated with different order maps.
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

end Matrix
