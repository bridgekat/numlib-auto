/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.ProdLp`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The dimension of an `L^p` product

`WithLp p (E × F)` is linearly equivalent to `E × F` (`WithLp.linearEquiv`), so its dimension is
`finrank E + finrank F`: `WithLp.finrank_prod`. It is what the dimension count of the Hermitian
dilation `WithLp 2 (E × F)` of an operator `E → F` needs.
-/

open Module

namespace WithLp

variable (p : ENNReal) (R E F : Type*) [Ring R] [StrongRankCondition R] [AddCommGroup E]
  [Module R E] [Module.Free R E] [Module.Finite R E] [AddCommGroup F] [Module R F]
  [Module.Free R F] [Module.Finite R F]

/-- The dimension of the `L^p` product `WithLp p (E × F)` is `finrank E + finrank F`. -/
theorem finrank_prod : finrank R (WithLp p (E × F)) = finrank R E + finrank R F :=
  (WithLp.linearEquiv p R (E × F)).finrank_eq.trans Module.finrank_prod

end WithLp
