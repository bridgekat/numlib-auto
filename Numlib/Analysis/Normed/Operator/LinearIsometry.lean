/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.LinearIsometry`, beside `Submodule.subtypeₗᵢ`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The inclusion of nested subspaces as a linear isometry

`Submodule.inclusionₗᵢ h : K →ₗᵢ[R] L` for `h : K ≤ L`, the isometric form of
`Submodule.inclusion`, as `Submodule.subtypeₗᵢ` is that of `Submodule.subtype`.
-/

namespace Submodule

variable {R E : Type*} [Ring R] [SeminormedAddCommGroup E] [Module R E]

/-- The subspace inclusion `K ≤ L` as a linear isometry. -/
def inclusionₗᵢ {K L : Submodule R E} (h : K ≤ L) : K →ₗᵢ[R] L where
  toLinearMap := Submodule.inclusion h
  norm_map' _ := rfl

@[simp]
theorem coe_inclusionₗᵢ {K L : Submodule R E} (h : K ≤ L) :
    ⇑(inclusionₗᵢ h) = Submodule.inclusion h :=
  rfl

end Submodule
