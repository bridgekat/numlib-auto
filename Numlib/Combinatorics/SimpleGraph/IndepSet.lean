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

A *maximal* independent set of a finite simple graph — one that no vertex can be added to — is
large: every vertex outside it has a neighbour inside it, so the whole vertex type is covered by
the set together with the neighbourhoods of its members, and counting gives
`Fintype.card V ≤ (G.maxDegree + 1) * s.card`
(`SimpleGraph.card_le_mul_card_of_maximal_isIndepSet`), that is `|s| ≥ |V| / (1 + Δ)`. The degree
bound is only ever used on the members of `s`, so the sharper
`SimpleGraph.card_le_mul_card_of_maximal_isIndepSet_of_forall_degree_le` asks for it there alone;
that is what makes the heuristic "take the vertices of low degree first" a statement rather than
advice.

The bound is the whole justification of the independent-set reorderings of a sparse matrix in
Saad[^saad-iterative] §3.3.3: an independent set of size `s` gives a diagonal leading block of
size `s` in the reordered matrix, so the bound says how much of the matrix one elimination step
can clear. Saad states it for the set his greedy algorithm produces; the argument he gives needs
no algorithm, only maximality, and that is how it is stated here.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s : Finset V}

/-- A maximal independent set *dominates*: every vertex outside it has a neighbour inside it,
since otherwise it could be added to the set. -/
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

/-- The size of a maximal independent set, with the degree bound taken over the members of the
set only: if every `w ∈ s` has `G.degree w ≤ ν`, then `Fintype.card V ≤ (ν + 1) * s.card`.

Every vertex is either in `s` or a neighbour of a member of `s`, so the vertex type is covered by
`s` together with the `s.card` neighbourhoods of its members, each of size at most `ν`. -/
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

/-- Saad's bound on the size of a maximal independent set: for a maximal independent set `s` of a
finite simple graph, `Fintype.card V ≤ (G.maxDegree + 1) * s.card`, that is
`|s| ≥ |V| / (1 + Δ)`. -/
theorem card_le_mul_card_of_maximal_isIndepSet (hs : Maximal G.IsIndepSet (s : Set V)) :
    Fintype.card V ≤ (G.maxDegree + 1) * s.card :=
  card_le_mul_card_of_maximal_isIndepSet_of_forall_degree_le hs fun w _ => G.degree_le_maxDegree w

end SimpleGraph
