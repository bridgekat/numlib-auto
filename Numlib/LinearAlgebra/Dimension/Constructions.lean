/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $K$ be a field, and let $f \colon M \to P$ and $g \colon N \to Q$ be linear maps between vector
spaces over $K$. This module proves that the range of the tensor product
$f \otimes g \colon M \otimes N \to P \otimes Q$ has dimension $\dim \operatorname{range} f \cdot
\dim \operatorname{range} g$. This is the linear-map form of the rank of a Kronecker product,
`Matrix.rank_kronecker`.

## Main results

* `TensorProduct.finrank_range_map`: $\dim \operatorname{range}(f \otimes g) = \dim
  \operatorname{range} f \cdot \dim \operatorname{range} g$.

## Proof outline

The map $f \otimes g$ factors as a surjection of $M \otimes N$ onto $\operatorname{range} f \otimes
\operatorname{range} g$, followed by the map that $\operatorname{range} f \otimes
\operatorname{range} g \to P \otimes Q$ induces from the two inclusions. This second map is
injective because vector spaces are flat. Thus the range of $f \otimes g$ is isomorphic to
$\operatorname{range} f \otimes \operatorname{range} g$, and `Module.finrank_tensorProduct` gives
its dimension.

## Implementation notes

* The dimension is `Module.finrank`, which is $0$ for an infinite-dimensional space. The identity
  holds with this convention, and no space is assumed finite-dimensional.
* The surjection in the proof is the tensor product of `LinearMap.rangeRestrict f` and
  `LinearMap.rangeRestrict g`, the maps with their codomains restricted to their ranges.
-/

namespace TensorProduct

variable {K : Type*} [Field K]

/-- Let $K$ be a field, and let $f \colon M \to P$ and $g \colon N \to Q$ be linear maps between
vector spaces over $K$. Then
$$\dim \operatorname{range}(f \otimes g) = \dim \operatorname{range} f \cdot \dim
  \operatorname{range} g.$$

The dimension is `Module.finrank`, which is $0$ for an infinite-dimensional space, so no space
needs to be finite-dimensional. The map $f \otimes g$ is `TensorProduct.map f g`. The proof
factors $f \otimes g$ through $\operatorname{range} f \otimes \operatorname{range} g$, whose
inclusion into $P \otimes Q$ is injective because vector spaces are flat. -/
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
