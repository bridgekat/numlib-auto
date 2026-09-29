/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Matrix.Mul`, beside `Matrix.col_mul_eq_mulVec_col`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Mul

/-!
# Columns and rows of an update `B - M A`

The columns of `B - M A` are `B.col q - M *ᵥ A.col q` and the rows of `B - A M` are
`B.row r - Mᵀ *ᵥ A.row r` (`Matrix.col_sub_mul`, `Matrix.row_sub_mul`): the form in which a
columnwise or rowwise error bound for one step of an elimination or orthogonal update is read off
a matrix statement. Both are definitional, like Mathlib's `Matrix.col_mul_eq_mulVec_col`.
-/

namespace Matrix

variable {ι κ R : Type*} [Fintype ι]

/-- `(B - M A).col q = B.col q - M (A.col q)`. -/
theorem col_sub_mul [NonUnitalNonAssocRing R] (B : Matrix ι κ R) (M : Matrix ι ι R)
    (A : Matrix ι κ R) (q : κ) : (B - M * A).col q = B.col q - M *ᵥ A.col q :=
  rfl

/-- `(B - A M).row r = B.row r - Mᵀ (A.row r)`. -/
theorem row_sub_mul [NonUnitalCommRing R] (B : Matrix κ ι R) (A : Matrix κ ι R)
    (M : Matrix ι ι R) (r : κ) : (B - A * M).row r = B.row r - Mᵀ *ᵥ A.row r := by
  ext j
  simp only [row_apply, sub_apply, Pi.sub_apply]
  rw [show (A * M) r j = (A r ᵥ* M) j from rfl, ← mulVec_transpose]
  rfl

end Matrix
