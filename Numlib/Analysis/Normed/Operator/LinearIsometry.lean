/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.LinearIsometry`, beside `Submodule.subtypeₗᵢ`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The inclusion of nested subspaces as a linear isometry

For submodules $K \le L$ of a seminormed module $E$ over a ring $R$, the inclusion $K \to L$
preserves the norm. This file bundles it as the linear isometry `Submodule.inclusionₗᵢ`, the
isometric form of `Submodule.inclusion`, in the same way as `Submodule.subtypeₗᵢ` is the isometric
form of `Submodule.subtype`.

## Main definitions

* `Submodule.inclusionₗᵢ`: the inclusion $K \to L$ for $K \le L$, as a linear isometry.
-/

namespace Submodule

variable {R E : Type*} [Ring R] [SeminormedAddCommGroup E] [Module R E]

/-- The inclusion $K \to L$ of submodules $K \le L$ of a seminormed module, as a linear isometry.
Its underlying linear map is `Submodule.inclusion`. -/
def inclusionₗᵢ {K L : Submodule R E} (h : K ≤ L) : K →ₗᵢ[R] L where
  toLinearMap := Submodule.inclusion h
  norm_map' _ := rfl

/-- The underlying function of `Submodule.inclusionₗᵢ h` is `Submodule.inclusion h`. -/
@[simp]
theorem coe_inclusionₗᵢ {K L : Submodule R E} (h : K ≤ L) :
    ⇑(inclusionₗᵢ h) = Submodule.inclusion h :=
  rfl

end Submodule
