/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Combinatorics.SimpleGraph.Clique`, beside `IsIndepSet` and `indepNum`.
Keep it free of dependencies on the rest of `Numlib`.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Ring

/-!
# How large a maximal independent set must be

Let $G$ be a finite simple graph on the vertex set $V$ with maximum degree $\Delta$. A **maximal**
independent set $s$ of $G$ is an independent set to which no vertex can be added. Every vertex
outside $s$ has a neighbour in $s$, so $V$ is covered by $s$ together with the neighbourhoods of the
members of $s$. Counting gives $|V| \le (\Delta + 1) |s|$, that is, $|s| \ge |V| / (1 + \Delta)$.
The degree bound is used only on the members of $s$, so a sharper form asks for it there alone. This
makes the heuristic "take the vertices of low degree first" a statement rather than advice.

The bound justifies the independent set orderings of a sparse matrix in [saad2003iterative], §3.3.3.
An independent set of size $|s|$ gives a diagonal leading block of size $|s|$ in the reordered
matrix, so the bound says how much of the matrix one elimination step can clear.

## Main results

* `SimpleGraph.exists_adj_of_maximal_isIndepSet`: every vertex outside a maximal independent set has
  a neighbour in it.
* `SimpleGraph.card_le_mul_card_of_maximal_isIndepSet_of_forall_degree_le`: if every member of a
  maximal independent set $s$ has degree at most $\nu$, then $|V| \le (\nu + 1) |s|$.
* `SimpleGraph.card_le_mul_card_of_maximal_isIndepSet`: every maximal independent set $s$ satisfies
  $|V| \le (\Delta + 1) |s|$.

## Implementation notes

* [saad2003iterative] states the bound for the set that a greedy algorithm produces. The argument
  needs no algorithm, only maximality, and so the results here are stated for every maximal
  independent set.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s : Finset V}

/-- A maximal independent set **dominates**. Let $s$ be a maximal independent set of a simple graph
$G$, and let $v \notin s$. Then $v$ has a neighbour $w \in s$.

Otherwise $v$ could be added to $s$. -/
theorem exists_adj_of_maximal_isIndepSet (hs : Maximal G.IsIndepSet (s : Set V)) {v : V}
    (hv : v ∉ s) : ∃ w ∈ s, G.Adj w v := by
  by_contra! h
  have hins : G.IsIndepSet (insert v (s : Set V)) := by
    intro x hx y hy hxy hadj
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hxy rfl
    · exact h y hy hadj.symm
    · exact h x hx hadj
    · exact hs.1 hx hy hxy hadj
  exact hv (by simpa using hs.2 hins (Set.subset_insert _ _) (Set.mem_insert _ _))

variable [Fintype V] [DecidableRel G.Adj]

/-- Let $G$ be a finite simple graph on $V$, let $s$ be a maximal independent set of $G$, and let
$\nu \in \mathbb{N}$ with $\deg w \le \nu$ for every $w \in s$. Then
$$|V| \le (\nu + 1) \, |s|.$$

Every vertex is in $s$ or is a neighbour of a member of $s$. So $V$ is covered by $s$ together
with the $|s|$ neighbourhoods of the members of $s$, each of size at most $\nu$. -/
theorem card_le_mul_card_of_maximal_isIndepSet_of_forall_degree_le
    (hs : Maximal G.IsIndepSet (s : Set V)) {ν : ℕ} (hν : ∀ w ∈ s, G.degree w ≤ ν) :
    Fintype.card V ≤ (ν + 1) * s.card := by
  classical
  have hsub : (univ : Finset V) ⊆ s ∪ s.biUnion fun w => G.neighborFinset w := by
    intro v _
    by_cases hv : v ∈ s
    · exact mem_union_left _ hv
    · obtain ⟨w, hw, hadj⟩ := exists_adj_of_maximal_isIndepSet hs hv
      exact mem_union_right _ (mem_biUnion.2 ⟨w, hw, by simpa using hadj⟩)
  calc Fintype.card V = #(univ : Finset V) := card_univ.symm
    _ ≤ #(s ∪ s.biUnion fun w => G.neighborFinset w) := card_le_card hsub
    _ ≤ #s + #(s.biUnion fun w => G.neighborFinset w) := card_union_le _ _
    _ ≤ #s + ∑ w ∈ s, G.degree w := Nat.add_le_add_left card_biUnion_le _
    _ ≤ #s + ∑ _w ∈ s, ν := Nat.add_le_add_left (sum_le_sum hν) _
    _ = (ν + 1) * #s := by rw [sum_const, smul_eq_mul]; ring

/-- Let $G$ be a finite simple graph on $V$ with maximum degree $\Delta$, and let $s$ be a maximal
independent set of $G$. Then
$$|V| \le (\Delta + 1) \, |s|, \qquad \text{that is,} \qquad |s| \ge \frac{|V|}{1 + \Delta}.$$
This is the bound on the size of an independent set in [saad2003iterative], §3.3.3. -/
theorem card_le_mul_card_of_maximal_isIndepSet (hs : Maximal G.IsIndepSet (s : Set V)) :
    Fintype.card V ≤ (G.maxDegree + 1) * s.card :=
  card_le_mul_card_of_maximal_isIndepSet_of_forall_degree_le hs fun w _ => G.degree_le_maxDegree w

end SimpleGraph
