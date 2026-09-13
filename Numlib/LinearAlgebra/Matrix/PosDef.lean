/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.PosDef`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive definite matrices over a ring with trivial star

Mathlib's `Matrix.PosSemidef` and `Matrix.PosDef` bundle `Matrix.IsHermitian`, which over a ring
whose star is trivial — the real numbers, in every use a numerical method makes of a symmetric
positive definite system — is `Matrix.IsSymm` (`Matrix.isHermitian_iff_isSymm`). The two lemmas
below take that step under one name, so that a positive definite real matrix can be handed to a
theorem stated for a symmetric one.
-/

namespace Matrix

variable {n R : Type*} [Ring R] [PartialOrder R] [StarRing R] [TrivialStar R] {A : Matrix n n R}

/-- Over a ring with trivial star, a positive semidefinite matrix is symmetric. -/
theorem PosSemidef.isSymm (hA : A.PosSemidef) : A.IsSymm := isHermitian_iff_isSymm.1 hA.1

/-- Over a ring with trivial star, a positive definite matrix is symmetric. -/
theorem PosDef.isSymm (hA : A.PosDef) : A.IsSymm := isHermitian_iff_isSymm.1 hA.1

end Matrix
