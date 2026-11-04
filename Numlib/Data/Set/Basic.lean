/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Set.Image

/-!
# Basic lemmas on sets

* `Set.setOf_add_mem_univ`: the translates of a point that lie in `univ` form `univ`; the set of
  feasible displacements `{e | y + e ∈ X}` for `X = univ`.
-/

namespace Set

/-- `{e | y + e ∈ univ} = univ`. -/
@[simp]
theorem setOf_add_mem_univ {α : Type*} [Add α] (y : α) :
    {e : α | y + e ∈ (univ : Set α)} = univ :=
  preimage_univ

end Set
