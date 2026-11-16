/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Dimension.Finrank`, beside `LinearEquiv.finrank_map_eq`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The dimension of the image of a subspace under an injective map

Let $R$ be a ring, let $f \colon M \to N$ be an injective linear map of $R$-modules, and let $S$ be
a submodule of $M$. This module proves that the image $f(S)$ has the same dimension as $S$. This is
the injective-map counterpart of Mathlib's `LinearEquiv.finrank_map_eq`, and the dimension form of
`Submodule.equivMapOfInjective`. It is the step by which a subspace of a smaller space is carried
into a larger one in the arguments of the Courant–Fischer theorem and of Sylvester's law of inertia.

## Main results

* `LinearMap.finrank_map_of_injective`: for an injective linear map $f$, $\dim f(S) = \dim S$.
-/

open Module

namespace LinearMap

/-- Let $R$ be a ring, let $f \colon M \to N$ be an injective linear map of $R$-modules, and let $S$
be a submodule of $M$. Then $\dim f(S) = \dim S$.

The dimension is `Module.finrank`. The proof applies `Module.finrank` to the linear equivalence
`Submodule.equivMapOfInjective` between $S$ and $f(S)$. -/
theorem finrank_map_of_injective {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f)
    (S : Submodule R M) : finrank R (S.map f) = finrank R S :=
  (Submodule.equivMapOfInjective f hf S).finrank_eq.symm

end LinearMap
