/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.ProdLp`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The dimension of an $L^p$ product

Let $R$ be a ring with the strong rank condition, and let $E$ and $F$ be finite free $R$-modules.
The $L^p$ product `WithLp p (E × F)` is linearly equivalent to the product of $E$ and $F$
(`WithLp.linearEquiv`), so its rank over $R$ is $\operatorname{finrank} E + \operatorname{finrank}
F$. The dimension count of the Hermitian dilation `WithLp 2 (E × F)` of an operator $E \to F$ uses
this fact.

## Main results

* `WithLp.finrank_prod`: the rank of `WithLp p (E × F)` is $\operatorname{finrank} E +
  \operatorname{finrank} F$.
-/

open Module

namespace WithLp

variable (p : ENNReal) (R E F : Type*) [Ring R] [StrongRankCondition R] [AddCommGroup E]
  [Module R E] [Module.Free R E] [Module.Finite R E] [AddCommGroup F] [Module R F]
  [Module.Free R F] [Module.Finite R F]

/-- Let $R$ be a ring with the strong rank condition, let $E$ and $F$ be finite free $R$-modules,
and let $p \in [0, \infty]$. The $L^p$ product `WithLp p (E × F)` has rank
$\operatorname{finrank}_R E + \operatorname{finrank}_R F$ over $R$. -/
theorem finrank_prod : finrank R (WithLp p (E × F)) = finrank R E + finrank R F :=
  (WithLp.linearEquiv p R (E × F)).finrank_eq.trans Module.finrank_prod

end WithLp
