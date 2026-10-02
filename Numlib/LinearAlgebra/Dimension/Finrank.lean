/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Dimension.Finrank`, beside `LinearEquiv.finrank_map_eq`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The dimension of the image of a subspace under an injective map

`LinearMap.finrank_map_of_injective`: an injective linear map preserves the dimension of every
subspace it is applied to, the `finrank` form of `Submodule.equivMapOfInjective` and the
injective-map counterpart of Mathlib's `LinearEquiv.finrank_map_eq`. It is the step by which a
subspace of a smaller space is carried into a larger one in every Courant–Fischer and Sylvester
inertia argument.
-/

open Module

namespace LinearMap

/-- The dimension of the image of a subspace under an injective linear map is the dimension of
the subspace: the `finrank` form of `Submodule.equivMapOfInjective`. -/
theorem finrank_map_of_injective {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f)
    (S : Submodule R M) : finrank R (S.map f) = finrank R S :=
  (Submodule.equivMapOfInjective f hf S).finrank_eq.symm

end LinearMap
