/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $E$ be a nontrivial real normed space. This file proves that the frontier of a nonempty bounded
set $s \subseteq E$ is nonempty. The whole space is unbounded (`NormedSpace.unbounded_univ`), so $s$
is neither $\emptyset$ nor $E$. In a connected space, $\emptyset$ and the whole space are the only
sets that are both open and closed, and these are exactly the sets with empty frontier.

## Main results

* `Bornology.IsBounded.frontier_nonempty`: a nonempty bounded subset of a nontrivial, connected real
  normed space has nonempty frontier.

## Implementation notes

* The statement holds over any nontrivially normed field. It is written over $\mathbb{R}$ so that
  the field can be inferred where the lemma is used.
* The space is assumed to be preconnected (`PreconnectedSpace E`). Every real normed space is path
  connected, by the Mathlib instance `NormedSpace.instPathConnectedSpace`, but this file does not
  import the module `Mathlib.Analysis.Normed.Module.Convex` that contains it.
-/

open Set

/-- Let $E$ be a real normed space with $E \neq \{0\}$, and assume that $E$ is preconnected. If
$s \subseteq E$ is bounded and nonempty, then the frontier of $s$ is nonempty.

The proof uses that the whole space is unbounded, and that $\emptyset$ and $E$ are the only
subsets of the connected space $E$ with empty frontier. -/
theorem Bornology.IsBounded.frontier_nonempty {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] [PreconnectedSpace E] {s : Set E}
    (hb : Bornology.IsBounded s) (hne : s.Nonempty) : (frontier s).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
  rcases h with h | h
  · exact hne.ne_empty h
  · exact NormedSpace.unbounded_univ ℝ E (h ▸ hb)
