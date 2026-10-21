/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Span.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Rescaling a spanning family

Multiplying each vector of a family by a nonzero scalar does not change its span
(`Submodule.span_range_smul_of_ne_zero`), the family form of Mathlib's
`Submodule.span_smul_eq_of_isUnit`. Subspace iteration uses it to rescale the iterates
`A^k x_j` by `l_j^{-k}` without changing the subspace they span.
-/

namespace Submodule

/-- **Rescaling each vector of a family by a nonzero scalar keeps its span.** -/
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
