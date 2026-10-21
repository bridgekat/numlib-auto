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

`SimpleGraph.Walk.start_notMem_support_dropUntil`: a path meets its first vertex only at the
start, so the part of it after an intermediate vertex `w ≠ u` avoids `u` — the mirror of Mathlib's
`SimpleGraph.Walk.endpoint_notMem_support_takeUntil`.
-/

namespace SimpleGraph.Walk

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v w : V}

/-- Dropping a strict initial segment of a path removes the start vertex from the support. -/
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
