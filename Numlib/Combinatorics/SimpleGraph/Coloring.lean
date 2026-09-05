/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex`.
Keep it free of dependencies on the rest of `Numlib`.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Greedy colouring of a finite simple graph

`SimpleGraph.greedyColoring G v` colours the vertices of a finite simple graph, along a linear
order on the vertex type, with the least natural number that no already-coloured neighbour of `v`
carries. It is a proper colouring (`SimpleGraph.greedyColoring_isColoring`) and it uses at most
`G.maxDegree + 1` colours (`SimpleGraph.greedyColoring_le_maxDegree`), because at each vertex the
colours ruled out are the values at its earlier neighbours, of which there are at most
`G.degree v`. Since the bound does not depend on the order, every finite simple graph satisfies
`G.Colorable (G.maxDegree + 1)` (`SimpleGraph.colorable_maxDegree_add_one`) — a brick Mathlib's
colouring files, which relate `chromaticNumber` to no degree at all, do not have.

On a bipartite graph greedy is optimal, but only if the order is a traversal order: if every
vertex that is not the least of its connected component has an *earlier neighbour*, then
`G.greedyColoring v ≤ 1` for every `v` (`SimpleGraph.greedyColoring_le_one_of_isBipartite`).
The hypothesis cannot be dropped. On the path `0 — 2 — 3 — 1` with the order `0 < 1 < 2 < 3`,
vertex `1` is not the least of its connected component and has no earlier neighbour; greedy then
gives colour `0` to `0` and to `1`, colour `1` to `2` and colour `2` to `3`, so it uses three
colours on a two-colourable graph.

Both facts are used by the multicolour reorderings of a sparse matrix in Saad[^saad-iterative]
§3.3.3: the diagonal blocks of an ordering that groups the indices by colour are diagonal
matrices, so `G.maxDegree + 1` blocks always suffice, and two blocks suffice when the adjacency
graph is bipartite. No traversal is formalized: greedy colouring is a function of the order alone,
and the orders the book's algorithms produce are the ones satisfying the hypothesis above.

## Implementation notes

The recursion defining `SimpleGraph.greedyColoring` is on the number of vertices below `v`, which
decreases along `<` on a `Fintype`; `Nat.sInf` of the complement of the finite set of excluded
colours makes it total with no further well-foundedness argument. That set of excluded colours is
`SimpleGraph.greedyExcludedColors`, and the two facts the rest of the file rests on are that the
greedy colour avoids it (`SimpleGraph.greedyColoring_notMem_excludedColors`) and is at most its
cardinality (`SimpleGraph.greedyColoring_le_card_excludedColors`).

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [LinearOrder V] (G : SimpleGraph V)

/-- A vertex has strictly fewer predecessors than any vertex above it: the measure that makes the
recursion defining `SimpleGraph.greedyColoring` terminate. -/
private theorem card_filter_lt_lt_card_filter_lt [Fintype V] {v w : V} (h : w < v) :
    #{x ∈ univ | x < w} < #{x ∈ univ | x < v} := by
  refine card_lt_card ((ssubset_iff_of_subset fun x hx => ?_).2 ⟨w, by simp [h], by simp⟩)
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  exact hx.trans h

/-- The greedy sequential colouring of a finite simple graph along a linear order on its vertices:
`G.greedyColoring v` is the least natural number that no neighbour of `v` below `v` carries.

Colours are numbered from `0`. The definition is a function of the order alone, and says nothing
about how the order is produced; the traversals that compute such an order in practice are not
formalized. -/
noncomputable def greedyColoring [Fintype V] (v : V) : ℕ :=
  sInf {k | ∀ w, w < v → G.Adj w v → greedyColoring w ≠ k}
termination_by #{x ∈ univ | x < v}
decreasing_by exact card_filter_lt_lt_card_filter_lt ‹_›

variable [Fintype V]

theorem greedyColoring_def (v : V) :
    G.greedyColoring v = sInf {k | ∀ w, w < v → G.Adj w v → G.greedyColoring w ≠ k} := by
  rw [greedyColoring]

open scoped Classical in
/-- The colours already carried by the neighbours of `v` that precede it in the order: exactly the
colours the greedy choice at `v` must avoid. -/
noncomputable def greedyExcludedColors (v : V) : Finset ℕ :=
  {w ∈ (univ : Finset V) | w < v ∧ G.Adj w v}.image G.greedyColoring

variable {G}

@[simp]
theorem mem_greedyExcludedColors {v : V} {k : ℕ} :
    k ∈ G.greedyExcludedColors v ↔ ∃ w, w < v ∧ G.Adj w v ∧ G.greedyColoring w = k := by
  simp only [greedyExcludedColors, mem_image, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨w, ⟨hlt, hadj⟩, hc⟩ => ⟨w, hlt, hadj, hc⟩,
    fun ⟨w, hlt, hadj, hc⟩ => ⟨w, ⟨hlt, hadj⟩, hc⟩⟩

/-- Below the cardinality of a finite set of naturals there is a number the set misses. -/
private theorem exists_le_card_notMem (t : Finset ℕ) : ∃ k ≤ #t, k ∉ t := by
  by_contra! h
  have hsub : range (#t + 1) ⊆ t := fun k hk => h k (by simpa [Nat.lt_succ_iff] using hk)
  have := card_le_card hsub
  rw [card_range] at this
  omega

private theorem greedyColoring_eq_sInf (v : V) :
    G.greedyColoring v = sInf {k | k ∉ G.greedyExcludedColors v} := by
  rw [greedyColoring_def]
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, mem_greedyExcludedColors, not_exists]
  refine ⟨fun h w hw => ?_, fun h w hlt hadj hc => h w ⟨hlt, hadj, hc⟩⟩
  exact h w hw.1 hw.2.1 hw.2.2

/-- The greedy colour of `v` is not the colour of any earlier neighbour of `v`. -/
theorem greedyColoring_notMem_excludedColors (v : V) :
    G.greedyColoring v ∉ G.greedyExcludedColors v := by
  obtain ⟨k, -, hk⟩ := exists_le_card_notMem (G.greedyExcludedColors v)
  have hne : {k | k ∉ G.greedyExcludedColors v}.Nonempty := ⟨k, hk⟩
  rw [greedyColoring_eq_sInf]
  exact Nat.sInf_mem hne

/-- The greedy colour of `v` is at most the number of colours it has to avoid. -/
theorem greedyColoring_le_card_excludedColors (v : V) :
    G.greedyColoring v ≤ #(G.greedyExcludedColors v) := by
  obtain ⟨k, hk, hk'⟩ := exists_le_card_notMem (G.greedyExcludedColors v)
  have hmem : k ∈ {k | k ∉ G.greedyExcludedColors v} := hk'
  rw [greedyColoring_eq_sInf]
  exact (Nat.sInf_le hmem).trans hk

/-- The greedy colouring gives an earlier neighbour a different colour. -/
theorem greedyColoring_ne_of_lt_of_adj {v w : V} (hlt : w < v) (h : G.Adj w v) :
    G.greedyColoring w ≠ G.greedyColoring v := fun hc =>
  greedyColoring_notMem_excludedColors v (mem_greedyExcludedColors.2 ⟨w, hlt, h, hc⟩)

/-- The greedy colouring is a proper colouring. -/
theorem greedyColoring_ne_of_adj {v w : V} (h : G.Adj v w) :
    G.greedyColoring v ≠ G.greedyColoring w := by
  rcases lt_or_gt_of_ne (G.ne_of_adj h) with hlt | hlt
  · exact greedyColoring_ne_of_lt_of_adj hlt h
  · exact (greedyColoring_ne_of_lt_of_adj hlt h.symm).symm

variable (G)

/-- The greedy colouring, packaged as a `SimpleGraph.Coloring` by natural numbers. -/
noncomputable def greedyColoring_isColoring : G.Coloring ℕ :=
  Coloring.mk G.greedyColoring fun h => greedyColoring_ne_of_adj h

@[simp]
theorem greedyColoring_isColoring_apply (v : V) :
    G.greedyColoring_isColoring v = G.greedyColoring v := rfl

variable [DecidableRel G.Adj]

/-- At `v` the greedy colouring has to avoid at most `G.degree v` colours, the ones carried by the
earlier neighbours of `v`. -/
theorem card_greedyExcludedColors_le_degree (v : V) :
    #(G.greedyExcludedColors v) ≤ G.degree v := by
  have hsub : G.greedyExcludedColors v ⊆ (G.neighborFinset v).image G.greedyColoring := by
    intro k hk
    obtain ⟨w, -, hadj, hc⟩ := mem_greedyExcludedColors.1 hk
    exact mem_image.2 ⟨w, (mem_neighborFinset G v w).2 hadj.symm, hc⟩
  exact (card_le_card hsub).trans card_image_le

/-- The greedy colouring uses at most `G.maxDegree + 1` colours: at `v` the excluded colours are
the values at the earlier neighbours of `v`, at most `G.degree v ≤ G.maxDegree` of them, so the
least natural number outside them is at most `G.maxDegree`. -/
theorem greedyColoring_le_maxDegree (v : V) : G.greedyColoring v ≤ G.maxDegree :=
  ((greedyColoring_le_card_excludedColors v).trans
    (G.card_greedyExcludedColors_le_degree v)).trans (G.degree_le_maxDegree v)

end SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every finite simple graph can be coloured with `G.maxDegree + 1` colours: greedy colouring
along any linear order on the vertices does it, and the bound does not depend on the order. -/
theorem colorable_maxDegree_add_one : G.Colorable (G.maxDegree + 1) := by
  let _ : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Equiv.injective _)
  exact (colorable_iff_exists_bdd_nat_coloring _).2
    ⟨G.greedyColoring_isColoring, fun v => Nat.lt_succ_of_le (G.greedyColoring_le_maxDegree v)⟩

end SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

/-- Two of the three values of a `Fin 2` are equal as soon as both differ from the third. -/
private theorem fin_two_eq_of_ne_of_ne {a b c : Fin 2} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  revert ha hb; revert a b c; decide

/-- With three values of `Fin 2` of which two differ, being equal to one is failing to be equal
to the other. -/
private theorem fin_two_eq_iff_ne {a b c : Fin 2} (h : b ≠ c) : a = c ↔ ¬ a = b := by
  revert h; revert a b c; decide

/-- The same trichotomy among three natural numbers that are at most one. -/
private theorem nat_eq_iff_ne {x y z : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1) (h : y ≠ z) :
    x = z ↔ ¬ x = y := by omega

/-- The induction behind `SimpleGraph.greedyColoring_le_one_of_isBipartite`: along a traversal
order the greedy colouring of a two-colourable graph is a two-colouring, and below every vertex it
agrees with the given one up to a swap. -/
private theorem greedyColoring_le_one_aux (C : G.Coloring (Fin 2))
    (hord : ∀ v : V, (∃ u, u < v ∧ G.Reachable u v) → ∃ w, w < v ∧ G.Adj w v) (v : V) :
    G.greedyColoring v ≤ 1 ∧
      ∀ u, u < v → G.Reachable u v → (C u = C v ↔ G.greedyColoring u = G.greedyColoring v) := by
  induction v using WellFoundedLT.induction with
  | ind v ih =>
  by_cases hex : ∃ u, u < v ∧ G.Reachable u v
  · obtain ⟨w, hwv, hadj⟩ := hord v hex
    -- Every earlier neighbour of `v` carries the same colour as `w` does.
    have key : ∀ u, u < v → G.Adj u v → G.greedyColoring u = G.greedyColoring w := by
      intro u huv hu
      have hCuw : C u = C w := fin_two_eq_of_ne_of_ne (C.valid hu) (C.valid hadj)
      have hru : G.Reachable u w := hu.reachable.trans hadj.symm.reachable
      rcases lt_trichotomy u w with h | rfl | h
      · exact ((ih w hwv).2 u h hru).1 hCuw
      · rfl
      · exact (((ih u huv).2 w h hru.symm).1 hCuw.symm).symm
    -- so the colours excluded at `v` are exactly the colour of `w`.
    have hexcl : G.greedyExcludedColors v = {G.greedyColoring w} := by
      ext k
      simp only [mem_greedyExcludedColors, mem_singleton]
      refine ⟨fun ⟨u, hu, hadju, hc⟩ => hc.symm.trans (key u hu hadju), fun hk => ?_⟩
      exact ⟨w, hwv, hadj, hk.symm⟩
    have hle : G.greedyColoring v ≤ 1 := by
      have h := greedyColoring_le_card_excludedColors (G := G) v
      rw [hexcl, card_singleton] at h
      omega
    have hne : G.greedyColoring w ≠ G.greedyColoring v :=
      greedyColoring_ne_of_lt_of_adj hwv hadj
    have hwle : G.greedyColoring w ≤ 1 := (ih w hwv).1
    have hCwv : C w ≠ C v := C.valid hadj
    refine ⟨hle, fun u huv hru => ?_⟩
    have hule : G.greedyColoring u ≤ 1 := (ih u huv).1
    have hruw : G.Reachable u w := hru.trans hadj.symm.reachable
    have hkey : C u = C w ↔ G.greedyColoring u = G.greedyColoring w := by
      rcases lt_trichotomy u w with h | rfl | h
      · exact (ih w hwv).2 u h hruw
      · exact ⟨fun _ => rfl, fun _ => rfl⟩
      · refine ⟨fun h' => ?_, fun h' => ?_⟩
        · exact (((ih u huv).2 w h hruw.symm).1 h'.symm).symm
        · exact (((ih u huv).2 w h hruw.symm).2 h'.symm).symm
    rw [fin_two_eq_iff_ne hCwv, nat_eq_iff_ne hule hwle hle hne, hkey]
  · -- `v` is the least vertex of its connected component: it has no earlier neighbour at all.
    have hexcl : G.greedyExcludedColors v = ∅ := by
      ext k
      simp only [mem_greedyExcludedColors, notMem_empty, iff_false, not_exists]
      rintro w ⟨hlt, hadj, -⟩
      exact hex ⟨w, hlt, hadj.reachable⟩
    refine ⟨?_, fun u hu hru => absurd ⟨u, hu, hru⟩ hex⟩
    have h := greedyColoring_le_card_excludedColors (G := G) v
    rw [hexcl, card_empty] at h
    omega

/-- Greedy colouring is optimal on a bipartite graph, provided the order is a traversal order:
if `G` is two-colourable and every vertex that is not the least of its connected component has an
earlier neighbour, then `G.greedyColoring v ≤ 1` for every `v`.

The hypothesis on the order is necessary; the module docstring has a four-vertex path on which
greedy uses three colours without it. -/
theorem greedyColoring_le_one_of_isBipartite (hG : G.Colorable 2)
    (hord : ∀ v : V, (∃ u, u < v ∧ G.Reachable u v) → ∃ w, w < v ∧ G.Adj w v) (v : V) :
    G.greedyColoring v ≤ 1 :=
  (greedyColoring_le_one_aux hG.some hord v).1

end SimpleGraph
