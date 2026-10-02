/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Matrix.Mul`, beside `Matrix.col_mul_eq_mulVec_col`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Mul

/-!
# Columns and rows of products

The columns of `B - M A` are `B.col q - M *ᵥ A.col q` and the rows of `B - A M` are
`B.row r - A.row r ᵥ* M` (`Matrix.col_sub_mul`, `Matrix.row_sub_mul_eq_sub_vecMul`): the form in
which a columnwise or rowwise error bound for one step of an elimination or orthogonal update is
read off a matrix statement. Both are definitional, like Mathlib's `Matrix.col_mul_eq_mulVec_col`
and `Matrix.row_mul_eq_vecMul_row`; over a commutative ring the row form is also
`B.row r - Mᵀ *ᵥ A.row r` (`Matrix.row_sub_mul`).

A matrix that acts on each column of `V` as a scalar is diagonalized by `V`:
`A V = V diag (γ)` when `A (V.col k) = γ k • V.col k`
(`Matrix.mul_eq_mul_diagonal_of_forall_mulVec_col`), and dually `diag (γ) V = V A` when
`V.row k ᵥ* A = γ k • V.row k` (`Matrix.diagonal_mul_eq_mul_of_forall_vecMul_row`).
-/

namespace Matrix

variable {ι κ R : Type*} [Fintype ι]

/-- `(B - M A).col q = B.col q - M (A.col q)`. -/
theorem col_sub_mul [NonUnitalNonAssocRing R] (B : Matrix ι κ R) (M : Matrix ι ι R)
    (A : Matrix ι κ R) (q : κ) : (B - M * A).col q = B.col q - M *ᵥ A.col q :=
  rfl

/-- `(B - A M).row r = B.row r - A.row r ᵥ* M`. -/
theorem row_sub_mul_eq_sub_vecMul [NonUnitalNonAssocRing R] (B : Matrix κ ι R)
    (A : Matrix κ ι R) (M : Matrix ι ι R) (r : κ) :
    (B - A * M).row r = B.row r - A.row r ᵥ* M :=
  rfl

/-- `(B - A M).row r = B.row r - Mᵀ (A.row r)`, the `mulVec` form of
`Matrix.row_sub_mul_eq_sub_vecMul` over a commutative ring. -/
theorem row_sub_mul [NonUnitalCommRing R] (B : Matrix κ ι R) (A : Matrix κ ι R)
    (M : Matrix ι ι R) (r : κ) : (B - A * M).row r = B.row r - Mᵀ *ᵥ A.row r := by
  rw [row_sub_mul_eq_sub_vecMul, mulVec_transpose]

/-- A matrix whose action on each column of `V` is multiplication by `γ k` satisfies
`A V = V diag (γ)`. -/
theorem mul_eq_mul_diagonal_of_forall_mulVec_col [CommSemiring R] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι R} {V : Matrix ι κ R} {γ : κ → R} (h : ∀ k, A *ᵥ V.col k = γ k • V.col k) :
    A * V = V * diagonal γ := by
  ext j k
  have hk := congrFun (h k) j
  rw [Pi.smul_apply, smul_eq_mul] at hk
  rw [mul_diagonal, mul_comm (V j k)]
  exact hk

/-- A matrix whose action on each row of `V` (from the right) is multiplication by `γ k` satisfies
`diag (γ) V = V A`; the row twin of `Matrix.mul_eq_mul_diagonal_of_forall_mulVec_col`. -/
theorem diagonal_mul_eq_mul_of_forall_vecMul_row [NonUnitalNonAssocSemiring R] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι ι R} {V : Matrix κ ι R} {γ : κ → R}
    (h : ∀ k, V.row k ᵥ* A = γ k • V.row k) : diagonal γ * V = V * A := by
  ext k j
  have hk := congrFun (h k) j
  rw [Pi.smul_apply, smul_eq_mul] at hk
  rw [diagonal_mul]
  exact hk.symm

end Matrix
