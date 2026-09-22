/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.MetricSpace.Bounded`, beside
`NormedSpace.unbounded_univ`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A nonempty bounded set of a nontrivial normed space has nonempty frontier

In a nontrivial real normed space the whole space is unbounded
(`NormedSpace.unbounded_univ`), so a nonempty bounded set is neither `∅` nor `univ`; a connected
space having no other clopen sets, its frontier is nonempty
(`Bornology.IsBounded.frontier_nonempty`). The statement holds over any nontrivially normed
field; it is written over `ℝ` so that the field is inferable at the use sites.
-/

open Set

/-- A nonempty bounded subset of a nontrivial real normed space has nonempty frontier: the whole
space is unbounded, and the empty set and the whole space are the only sets with empty
frontier. -/
theorem Bornology.IsBounded.frontier_nonempty {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] [PreconnectedSpace E] {s : Set E}
    (hb : Bornology.IsBounded s) (hne : s.Nonempty) : (frontier s).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
  rcases h with h | h
  · exact hne.ne_empty h
  · exact NormedSpace.unbounded_univ ℝ E (h ▸ hb)
