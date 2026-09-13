/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LU`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# One step of Gaussian elimination

One step of Gaussian elimination at a pivot `p`, applied to a square matrix `M` indexed by a
finite linear order `n`: the rows strictly below `p` have `M i p / M p p` times the row `p`
subtracted from them, and every other row is left alone. It is the elementary operation from which
the `LU` factorization (`Numlib/LinearAlgebra/Matrix/LU`) and the incomplete factorizations of
`Numlib/LinearSolve/Preconditioner/ILU` are built.

## Main definitions

* `Matrix.elimMultipliers M p`: the matrix `N` of multipliers, `M i p / M p p` in the column `p`
  below the pivot and zero elsewhere.
* `Matrix.elimMul M p`: the unipotent factor `G = 1 + N` of the step.
* `Matrix.elimStep M p`: the eliminated matrix `M - N M = (1 - N) M`.

## Main results

* `Matrix.elimStep_apply_pivot`: the step annihilates the pivot column below the pivot, and
  `Matrix.elimStep_apply_of_not_lt` says it changes nothing above it.
* `Matrix.elimMultipliers_mul_self`: `N * N = 0`, so that `G⁻¹ = 1 - N`
  (`Matrix.inv_elimMul`), the Gaussian transformation `M_p = 1 - m_p e_pᵀ` of
  Quarteroni–Sacco–Saleri (3.36).
* `Matrix.elimMul_mul_elimStep`: the factorization `M = G * elimStep M p` of one step.

## Implementation notes

The index type is kept fixed: elimination is written as multiplication by the unipotent `G` on
the whole of `n`, rather than as a Schur complement on the smaller index type `{i // i ≠ p}`. The
accumulated `L` factor of a factorization is then a product of the matrices `elimMul`, and no
reindexing appears anywhere in the statements; the same step read on the smaller index type is
`Matrix.schurComplementSingle` of `Numlib/LinearAlgebra/Matrix/SchurComplement`. Only the strict
order `p < i` of the index type is used, to say which rows lie below the pivot.

Everything is over a field, and nothing here is numerical: pivoting and the growth factor belong
to the `LU` modules.

## References

* Saad, *Iterative Methods for Sparse Linear Systems*, §10.3.
* Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §3.3.1.

## TODO

The rest of the planned module, Gaussian elimination as *functions* whose outputs are the `LU`
factors of `Numlib/LinearAlgebra/Matrix/LU`:

* the stages `gemStage A k = A^{(k+1)}` of the Gaussian elimination method on `Fin N`
  (Quarteroni–Sacco–Saleri (3.29)), with `gemStage A (k+1) = gaussTransform … * gemStage A k` and
  the factorization `A = L U` read off the stages and the multipliers ((3.37));
* the Doolittle recurrence `luPacked` ((3.43)), a *total* function on any finite linear order by
  well-founded recursion on the number of indices below `min i j`, with junk `x / 0 = 0` at a zero
  pivot; `isLU_luLower_luUpper` says it is right whenever the strict leading principal
  submatrices are nonsingular, and by uniqueness it then agrees with the elimination stages and
  with every other loop order. Crout is Doolittle of the transpose.

Pivoting and the growth factor are `Numlib/LinearAlgebra/Matrix/LU/Pivoting`; the prototype is
`notes/qss/ch03/proto/ProtoLU.lean`.
-/

namespace Matrix

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

end Matrix
