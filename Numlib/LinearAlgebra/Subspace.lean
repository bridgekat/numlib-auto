import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The affine hull of a set containing the origin

A set containing the origin has the same affine hull and linear hull: Mathlib's
`vectorSpan_eq_span_vsub_set_right` subtracts a chosen base point, and when that point can be taken
to be `0` the subtraction disappears. That is `vectorSpan_eq_span_of_zero_mem`, and it is
**Rockafellar, Theorem 1.1** in the form its consumers use it — the affine sets through the origin
are exactly the subspaces. Alongside it, `vectorSpan_eq_of_affineSpan_eq` turns equal affine hulls
into equal directions, hence equal `finrank`. Stated for an arbitrary module over a field; nothing
here is about convexity.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §1.
-/

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- For a set containing the origin the affine hull and the linear hull agree. -/
theorem vectorSpan_eq_span_of_zero_mem {C : Set E} (h0 : (0 : E) ∈ C) :
    vectorSpan K C = Submodule.span K C := by
  rw [vectorSpan_eq_span_vsub_set_right K h0]
  congr 1
  ext x
  simp

/-- Sets with the same affine hull have the same direction. Rockafellar's Corollary 6.3.1 (`cl C`
and `ri C` have the same dimension as `C`) is this applied to the equalities of Theorem 6.3. -/
theorem vectorSpan_eq_of_affineSpan_eq {S T : Set E}
    (h : affineSpan K S = affineSpan K T) : vectorSpan K S = vectorSpan K T := by
  rw [← direction_affineSpan K S, ← direction_affineSpan K T, h]
