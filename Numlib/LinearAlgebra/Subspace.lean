import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The affine hull of a set containing the origin

Upstreaming candidate: nothing here is specific to numerical analysis.

A set containing the origin has the same affine hull and linear hull. Mathlib states this for the
*sets* as `affineSpan_insert_zero`; `vectorSpan_eq_span_of_zero_mem` is the same fact for the
*direction*, `vectorSpan K C = span K C`, which is the form its consumers rewrite with. It is
**Rockafellar, Theorem 1.1** — the affine sets through the origin are exactly the subspaces —
stated for an arbitrary module over a field; nothing here is about convexity.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §1.
-/

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- For a set containing the origin the affine hull and the linear hull agree: the direction form
of Mathlib's `affineSpan_insert_zero`. -/
theorem vectorSpan_eq_span_of_zero_mem {C : Set E} (h0 : (0 : E) ∈ C) :
    vectorSpan K C = Submodule.span K C := by
  have h : affineSpan K C = (Submodule.span K C).toAffineSubspace := AffineSubspace.coe_injective
    (by rw [← Set.insert_eq_of_mem h0, affineSpan_insert_zero, Submodule.span_insert_zero]; rfl)
  rw [← direction_affineSpan, h, Submodule.toAffineSubspace_direction]
