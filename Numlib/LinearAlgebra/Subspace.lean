/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The affine hull of a set containing the origin

Let $C$ be a subset of a vector space $E$ over a field $K$. If $0 \in C$, then the affine hull of
$C$ and the linear hull of $C$ agree. Mathlib states this for the sets as `affineSpan_insert_zero`.
This module states it for the direction: $\operatorname{vectorSpan}_K C = \operatorname{span}_K C$,
which is the form that other modules rewrite with. This is Theorem 1.1 of [rockafellar1970convex]
(the affine sets that contain the origin are exactly the subspaces), stated for an arbitrary module
over a field. Nothing here is about convexity.

## Main results

* `vectorSpan_eq_span_of_zero_mem`: if $0 \in C$, then $\operatorname{vectorSpan}_K C =
  \operatorname{span}_K C$.

## Implementation notes

* Nothing in this module is specific to numerical analysis.
-/

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Let $E$ be a vector space over a field $K$, and let $C \subseteq E$ contain $0$. Then the
direction of the affine hull of $C$ is the linear hull of $C$:
$$\operatorname{vectorSpan}_K C = \operatorname{span}_K C.$$

This is the direction form of Mathlib's `affineSpan_insert_zero`, and the content of Theorem 1.1
of [rockafellar1970convex]. -/
theorem vectorSpan_eq_span_of_zero_mem {C : Set E} (h0 : (0 : E) ∈ C) :
    vectorSpan K C = Submodule.span K C := by
  have h : affineSpan K C = (Submodule.span K C).toAffineSubspace := AffineSubspace.coe_injective
    (by rw [← Set.insert_eq_of_mem h0, affineSpan_insert_zero, Submodule.span_insert_zero])
  rw [← direction_affineSpan, h, Submodule.toAffineSubspace_direction]
