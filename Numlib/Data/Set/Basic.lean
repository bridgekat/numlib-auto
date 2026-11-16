/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Set.Image

/-!
# Feasible displacements in the whole space

For a set $X$ in a type $\alpha$ with an addition and a point $y \in \alpha$, the feasible
displacements from $y$ are the elements of $\{e \in \alpha : y + e \in X\}$. This module records
that every displacement is feasible when $X$ is the whole type.

## Main results

* `Set.setOf_add_mem_univ`: $\{e \in \alpha : y + e \in \alpha\} = \alpha$.
-/

namespace Set

/-- Let $\alpha$ be a type with an addition and let $y \in \alpha$. Then
$$\{e \in \alpha : y + e \in \alpha\} = \alpha.$$
That is, when the constraint set is the whole type `Set.univ`, every displacement $e$ from $y$
is feasible. -/
@[simp]
theorem setOf_add_mem_univ {α : Type*} [Add α] (y : α) :
    {e : α | y + e ∈ (univ : Set α)} = univ :=
  preimage_univ

end Set
