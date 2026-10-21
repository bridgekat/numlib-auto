/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Dimension.Constructions`, by `Module.finrank_tensorProduct`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic

/-!
# The dimension of the range of a tensor product of linear maps

`TensorProduct.finrank_range_map`: over a field, the range of `f ⊗ g` has dimension
`dim range f · dim range g`. The map `f ⊗ g` factors as the surjection
`f.rangeRestrict ⊗ g.rangeRestrict` followed by the inclusion of `range f ⊗ range g`, which is
injective because vector spaces are flat, so `Module.finrank_tensorProduct` applies. It is the
linear-map form of the rank of a Kronecker product (`Matrix.rank_kronecker`).
-/

namespace TensorProduct

variable {K : Type*} [Field K]

/-- Over a field, the range of `f ⊗ g` has dimension `dim range f · dim range g`. -/
theorem finrank_range_map {M N P Q : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    (f : M →ₗ[K] P) (g : N →ₗ[K] Q) :
    Module.finrank K (LinearMap.range (TensorProduct.map f g))
      = Module.finrank K (LinearMap.range f) * Module.finrank K (LinearMap.range g) := by
  have h : TensorProduct.map f g = TensorProduct.map (LinearMap.range f).subtype
      (LinearMap.range g).subtype ∘ₗ TensorProduct.map f.rangeRestrict g.rangeRestrict := by
    rw [← TensorProduct.map_comp, LinearMap.subtype_comp_rangeRestrict,
      LinearMap.subtype_comp_rangeRestrict]
  rw [h, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2
      (TensorProduct.map_surjective f.surjective_rangeRestrict g.surjective_rangeRestrict)),
    LinearMap.finrank_range_of_inj (TensorProduct.map_injective_of_flat_flat _ _
      (Submodule.injective_subtype _) (Submodule.injective_subtype _)),
    Module.finrank_tensorProduct]

end TensorProduct
