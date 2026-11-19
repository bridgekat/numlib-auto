/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Topology.BorsukUlam.OpenAI.Simplicial.OddSphereDimensionBoundFintype

/-!
# Borsuk–Ulam dimension bound

A continuous map between finite-dimensional real spheres that preserves
antipodes bounds the dimension of the domain by that of the codomain.
-/

namespace Numlib

/-- The odd-map form of Borsuk–Ulam. A continuous antipode-preserving map
between real unit spheres can only increase the ambient dimension.

The simplicial proof is from the OpenAI `math` repository. Its source
revision and local import path changes are recorded with the vendored files. -/
theorem oddSphereDimensionBound {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
    (hf : ContinuousOn f {x | ‖x‖ = 1})
    (hnorm : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hodd : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    Fintype.card ι ≤ Fintype.card κ :=
  OAI.BorsukNine.SimplicialChains.odd_sphere_dimension_bound_fintype f hf hnorm hodd

end Numlib
