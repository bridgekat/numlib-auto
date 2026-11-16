/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Span.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Rescaling a spanning family

Let $K$ be a division ring, $M$ a $K$-module and $(v_j)_{j \in \iota}$ a family of vectors in $M$.
If each $c_j \in K$ is nonzero, then the families $(c_j v_j)_j$ and $(v_j)_j$ span the same
submodule. This is the form for families of Mathlib's `Submodule.span_smul_eq_of_isUnit`. Subspace
iteration uses it to rescale the iterates $A^k x_j$ by $l_j^{-k}$ without a change of the subspace
that they span.

## Main results

* `Submodule.span_range_smul_of_ne_zero`: rescaling each vector of a family by a nonzero scalar does
  not change its span.
-/

namespace Submodule

/-- Let $K$ be a division ring, $M$ a $K$-module, $(v_j)_{j \in \iota}$ a family in $M$ and
$(c_j)_{j \in \iota}$ a family of scalars in $K$ with $c_j \neq 0$ for all $j$. Then
$$\operatorname{span}_K \{c_j v_j : j \in \iota\} = \operatorname{span}_K \{v_j : j \in
  \iota\}.$$
-/
theorem span_range_smul_of_ne_zero {K M ι : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]
    (c : ι → K) (hc : ∀ j, c j ≠ 0) (v : ι → M) :
    span K (Set.range fun j => c j • v j) = span K (Set.range v) := by
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    exact smul_mem _ _ (subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    have hvj : v j = (c j)⁻¹ • (c j • v j) := by
      rw [smul_smul, inv_mul_cancel₀ (hc j), one_smul]
    rw [hvj]
    exact smul_mem _ _ (subset_span ⟨j, rfl⟩)

end Submodule
