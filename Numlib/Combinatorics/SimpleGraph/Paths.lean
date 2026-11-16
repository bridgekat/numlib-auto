/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Combinatorics.SimpleGraph.Paths`, beside
`SimpleGraph.Walk.endpoint_notMem_support_takeUntil`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# The start of a path is not in the support of a strict final segment

A path in a simple graph visits its first vertex $u$ only at the start. So the part of the path
after an intermediate vertex $w \neq u$ does not contain $u$. This mirrors Mathlib's
`SimpleGraph.Walk.endpoint_notMem_support_takeUntil`.

## Main results

* `SimpleGraph.Walk.start_notMem_support_dropUntil`: the part of a path from $u$ after a vertex
  $w \neq u$ of the path does not contain $u$.
-/

namespace SimpleGraph.Walk

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v w : V}

/-- Let $p$ be a path from $u$ to $v$ in a simple graph, and let $w \neq u$ be a vertex of $p$. Then
the part of $p$ from $w$ to $v$ does not contain $u$.

The part of $p$ from $w$ to $v$ is `SimpleGraph.Walk.dropUntil`. -/
lemma start_notMem_support_dropUntil {p : G.Walk u v} (hp : p.IsPath) (hw : w ∈ p.support)
    (h : u ≠ w) : u ∉ (p.dropUntil w hw).support := by
  intro hu
  have hsupp : p.support = (p.takeUntil w hw).support ++ (p.dropUntil w hw).support.tail := by
    conv_lhs => rw [← p.take_spec hw]
    rw [support_append]
  have hnd : ((p.takeUntil w hw).support ++ (p.dropUntil w hw).support.tail).Nodup := by
    rw [← hsupp]
    exact hp.support_nodup
  refine List.disjoint_of_nodup_append hnd (start_mem_support _) ?_
  rw [← cons_tail_support] at hu
  exact (List.mem_cons.1 hu).resolve_left h

end SimpleGraph.Walk
