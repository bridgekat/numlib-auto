/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.PlaneRotation`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Plane rotations

The **plane rotation** `Matrix.planeRotation j k c s` is the real matrix that agrees with the
identity outside the rows and columns `j`, `k` and carries the `2 × 2` block `!![c, -s; s, c]` on
them: for `c = cos θ` and `s = sin θ` it rotates the `(j, k)`-coordinate plane by the angle `θ`
and fixes its orthogonal complement. It is the Givens rotation of numerical linear algebra, and
the one-parameter family that every rotation-based algorithm is built from.

## Main definitions

* `Matrix.planeRotation j k c s`: the rotation of the `(j, k)`-plane with cosine `c` and sine `s`.

## Main results

* `Matrix.mul_planeRotation_apply`, `Matrix.transpose_planeRotation_mul_apply`: multiplying by a
  plane rotation on the right combines the columns `j`, `k`, and multiplying by its transpose on
  the left combines the rows `j`, `k`; every other entry is left alone.
* `Matrix.transpose_planeRotation_mul_self`: a plane rotation with `c ^ 2 + s ^ 2 = 1` is
  orthogonal.
* `Matrix.conj_planeRotation_apply_of_ne` and the entry formulas `conj_planeRotation_apply_jj`,
  `_kk`, `_jk`, `_col_j`, `_col_k`, `_row_j`, `_row_k`: the entries of the conjugate `Rᵀ M R` of
  an arbitrary square matrix `M` by a plane rotation `R`, entry by entry, which is the form in
  which an algorithm reads off what one rotation did.

## Implementation notes

The sign convention is that of Jacobi's method: the rows `j`, `k` of the rotation are `(c, -s)`
and `(s, c)`, so that `Rᵀ` rotates counterclockwise. Nothing here assumes `c ^ 2 + s ^ 2 = 1`
except the orthogonality statement, and nothing needs an order on the index type; `j ≠ k` is a
hypothesis of every lemma, the definition being degenerate at `j = k`.

Consumers: Jacobi's eigenvalue algorithm (`Numlib/Eigen/Jacobi`), which conjugates a symmetric
matrix by a rotation chosen to annihilate one off-diagonal entry; the Givens `QR` factorization
of a Hessenberg matrix (`Numlib/LinearAlgebra/Matrix/QR`); and the complex Givens rotations of
the progressive `QR` factorization in `Numlib/Krylov/Hessenberg`, `Krylov.givensMatrix`, which
are the same construction with a phase.

## TODO

Generalize to `planeEmbed j k G`, the embedding of an arbitrary `2 × 2` matrix `G` into the
`(j, k)`-plane over any semiring: the rotation is `planeEmbed j k !![c, -s; s, c]`, the complex
Givens rotation of `Numlib/Krylov/Hessenberg` is `planeEmbed k (k+1) !![conj c, conj s; -s, c]`
(the bridge `Krylov.givensMatrix_eq_planeEmbed` is planned there), and the row/column action,
`planeEmbed_mul_planeEmbed`, `det_planeEmbed` and the unitary-group membership
`planeEmbed_mem_unitaryGroup_iff` would then be proved once for both. The Givens pair `(c, s)`
annihilating one entry of a real vector, `givensPair`, belongs here as well.
-/

open Finset

namespace Matrix

variable {n : Type*} [DecidableEq n]

/-- The rotation of the `(j,k)`-plane with cosine `c` and sine `s`: the identity matrix with its
`j`-th and `k`-th rows replaced by `(c, -s)` and `(s, c)` in the columns `j` and `k`. -/
def planeRotation (j k : n) (c s : ℝ) : Matrix n n ℝ := Matrix.of fun p q =>
  if p = j then (if q = j then c else if q = k then -s else 0)
  else if p = k then (if q = j then s else if q = k then c else 0)
  else if p = q then 1 else 0

variable {j k : n} {c s : ℝ}

/-- The entries of a plane rotation, written so that each column is a linear combination of
Kronecker deltas. -/
theorem planeRotation_apply (hjk : j ≠ k) (t q : n) :
    planeRotation j k c s t q =
      if q = j then (if t = j then c else 0) + (if t = k then s else 0)
      else if q = k then (if t = j then -s else 0) + (if t = k then c else 0)
      else if t = q then 1 else 0 := by
  have hkj : k ≠ j := hjk.symm
  unfold planeRotation
  simp only [Matrix.of_apply]
  by_cases htj : t = j
  · by_cases hqj : q = j
    · simp [htj, hqj, hjk]
    · by_cases hqk : q = k
      · simp [htj, hqk, hjk]
      · simp [htj, hqj, hqk, Ne.symm hqj]
  · by_cases htk : t = k
    · by_cases hqj : q = j
      · simp [htk, hqj, hkj]
      · by_cases hqk : q = k
        · simp [htk, hqk, hkj]
        · simp [htk, hqj, hqk, Ne.symm hqk]
    · by_cases hqj : q = j
      · simp [htj, htk, hqj]
      · by_cases hqk : q = k
        · simp [htj, htk, hqk]
        · simp [htj, htk, hqj, hqk]

variable [Fintype n]

/-- Multiplying on the right by a plane rotation combines the `j`-th and `k`-th columns. -/
theorem mul_planeRotation_apply (hjk : j ≠ k) (M : Matrix n n ℝ) (p q : n) :
    (M * planeRotation j k c s) p q =
      if q = j then c * M p j + s * M p k
      else if q = k then -s * M p j + c * M p k
      else M p q := by
  rw [Matrix.mul_apply]
  simp only [planeRotation_apply hjk]
  split_ifs with h1 h2
  · simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq', mul_comm]
  · simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq', mul_comm]
  · simp [mul_ite, Finset.sum_ite_eq']

/-- Multiplying on the left by the transpose of a plane rotation combines the `j`-th and `k`-th
rows. -/
theorem transpose_planeRotation_mul_apply (hjk : j ≠ k) (M : Matrix n n ℝ) (p q : n) :
    ((planeRotation j k c s)ᵀ * M) p q =
      if p = j then c * M j q + s * M k q
      else if p = k then -s * M j q + c * M k q
      else M p q := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, planeRotation_apply hjk]
  split_ifs with h1 h2
  · simp [add_mul, Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq']
  · simp [add_mul, Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq']
  · simp [ite_mul, Finset.sum_ite_eq']

/-- A plane rotation is orthogonal. -/
theorem transpose_planeRotation_mul_self (hjk : j ≠ k) (hcs : c ^ 2 + s ^ 2 = 1) :
    (planeRotation j k c s)ᵀ * planeRotation j k c s = 1 := by
  have hkj : k ≠ j := hjk.symm
  ext p q
  rw [transpose_planeRotation_mul_apply hjk]
  simp only [planeRotation_apply hjk, Matrix.one_apply, hjk, hkj, ite_true, ite_false,
    add_zero, zero_add]
  split_ifs <;> simp_all <;> nlinarith [hcs]

/-! ### Conjugation by a plane rotation -/

/-- Conjugating by a plane rotation leaves every entry outside the `j`-th and `k`-th rows and
columns alone. -/
theorem conj_planeRotation_apply_of_ne (hjk : j ≠ k) (M : Matrix n n ℝ) {p q : n}
    (hpj : p ≠ j) (hpk : p ≠ k) (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p q = M p q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk,
    hpj, hpk, hqj, hqk]

/-- The `(j,j)` entry of a matrix conjugated by a plane rotation. -/
theorem conj_planeRotation_apply_jj (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j j
      = c * (c * M j j + s * M j k) + s * (c * M k j + s * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk]
  ring

/-- The `(k,k)` entry of a matrix conjugated by a plane rotation. -/
theorem conj_planeRotation_apply_kk (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k k
      = -s * (-s * M j j + c * M j k) + c * (-s * M k j + c * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

/-- The `(j,k)` entry of a matrix conjugated by a plane rotation: the entry the Jacobi angle is
chosen to annihilate. -/
theorem conj_planeRotation_apply_jk (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j k
      = c * (-s * M j j + c * M j k) + s * (-s * M k j + c * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

/-- The `(p,j)` entry after a plane rotation, for `p` outside the rotated plane. -/
theorem conj_planeRotation_apply_col_j (hjk : j ≠ k) (M : Matrix n n ℝ) {p : n}
    (hpj : p ≠ j) (hpk : p ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p j = c * M p j + s * M p k := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hpj, hpk]

/-- The `(p,k)` entry after a plane rotation, for `p` outside the rotated plane. -/
theorem conj_planeRotation_apply_col_k (hjk : j ≠ k) (M : Matrix n n ℝ) {p : n}
    (hpj : p ≠ j) (hpk : p ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p k = -s * M p j + c * M p k := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hpj, hpk,
    Ne.symm hjk]

/-- The `(j,q)` entry after a plane rotation, for `q` outside the rotated plane. -/
theorem conj_planeRotation_apply_row_j (hjk : j ≠ k) (M : Matrix n n ℝ) {q : n}
    (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j q = c * M j q + s * M k q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hqj, hqk]

/-- The `(k,q)` entry after a plane rotation, for `q` outside the rotated plane. -/
theorem conj_planeRotation_apply_row_k (hjk : j ≠ k) (M : Matrix n n ℝ) {q : n}
    (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k q = -s * M j q + c * M k q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hqj, hqk,
    Ne.symm hjk]

end Matrix
