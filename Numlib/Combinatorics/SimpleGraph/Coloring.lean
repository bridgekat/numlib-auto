/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex`.
Keep it free of dependencies on the rest of `Numlib`.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Numlib.Data.Finset.Card

/-!
# Greedy colouring of a finite simple graph

Let $G$ be a finite simple graph whose vertex set carries a linear order. The greedy colouring gives
each vertex $v$, in increasing order, the least natural number that no earlier neighbour of $v$
carries. It is a proper colouring, and it uses at most $\Delta(G) + 1$ colours, where $\Delta(G)$ is
the maximum degree: at each vertex $v$ the excluded colours are the colours of its earlier
neighbours, and there are at most $\deg v$ of them. The bound does not depend on the order, so every
finite simple graph is $(\Delta(G) + 1)$-colourable. Mathlib's colouring files do not relate the
chromatic number to the degrees.

On a bipartite graph the greedy colouring is optimal, but only for a traversal order: if every
vertex that is not the least of its connected component has an earlier neighbour, then the greedy
colouring uses only the colours $0$ and $1$. The hypothesis cannot be dropped. On the path
$0 - 2 - 3 - 1$ with the order $0 < 1 < 2 < 3$, vertex $1$ is not the least of its connected
component and has no earlier neighbour. The greedy colouring gives colour $0$ to $0$ and to $1$,
colour $1$ to $2$, and colour $2$ to $3$, so it uses three colours on a two-colourable graph.

## Main definitions

* `SimpleGraph.greedyColoring`: the greedy colour of a vertex.
* `SimpleGraph.greedyColoring_isColoring`: the greedy colouring as a proper colouring by natural
  numbers.

## Main results

* `SimpleGraph.greedyColoring_le_maxDegree`: every greedy colour is at most $\Delta(G)$.
* `SimpleGraph.colorable_maxDegree_add_one`: every finite simple graph is
  $(\Delta(G) + 1)$-colourable.
* `SimpleGraph.greedyColoring_le_one_of_isBipartite`: on a two-colourable graph with a traversal
  order, every greedy colour is at most $1$.

## Implementation notes

* The multicolour orderings of a sparse matrix in [saad2003iterative], §3.3.3, use both facts. In an
  ordering that groups the indices by colour, the diagonal blocks are diagonal matrices. So
  $\Delta(G) + 1$ blocks always suffice, and two blocks suffice when the adjacency graph is
  bipartite.
* No traversal is formalized. The greedy colouring is a function of the order alone, and the orders
  that the algorithms of [saad2003iterative] produce are the orders that satisfy the hypothesis of
  `SimpleGraph.greedyColoring_le_one_of_isBipartite`.
* Colours are natural numbers, numbered from $0$.
* The recursion that defines `SimpleGraph.greedyColoring` is on the number of vertices below $v$,
  which decreases along $<$ on a finite type. The infimum `sInf` of the complement of the finite set
  of excluded colours makes the definition total with no further well-foundedness argument. The set
  of excluded colours is `SimpleGraph.greedyExcludedColors`. The rest of the file rests on two
  facts: the greedy colour is not in this set (`SimpleGraph.greedyColoring_notMem_excludedColors`),
  and it is at most the cardinality of this set
  (`SimpleGraph.greedyColoring_le_card_excludedColors`).
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [LinearOrder V] (G : SimpleGraph V)

/-- The **greedy sequential colouring** of a finite simple graph $G$ along a linear order on its
vertices: the colour of $v$ is the least natural number that no neighbour $w < v$ of $v$
carries,
$$c(v) = \min \{ k \in \mathbb{N} : c(w) \neq k \text{ for all neighbours } w < v \text{ of } v
  \}.$$

Colours are numbered from $0$. The definition is a function of the order alone, and it says
nothing about how the order is produced. The traversals that compute such an order in practice
are not formalized. -/
noncomputable def greedyColoring [Fintype V] (v : V) : ℕ :=
  sInf {k | ∀ w, w < v → G.Adj w v → greedyColoring w ≠ k}
termination_by #{x ∈ univ | x < v}
decreasing_by exact card_filter_lt_lt_of_lt ‹_›

variable [Fintype V]

/-- The defining equation of the greedy colouring: $c(v)$ is the least $k \in \mathbb{N}$ that is
different from $c(w)$ for every neighbour $w < v$ of $v$.

A definition by well-founded recursion does not give this equation by `rfl`. -/
theorem greedyColoring_def (v : V) :
    G.greedyColoring v = sInf {k | ∀ w, w < v → G.Adj w v → G.greedyColoring w ≠ k} := by
  rw [greedyColoring]

open scoped Classical in
/-- The **excluded colours** at $v$: the set of colours $c(w)$ of the neighbours $w < v$ of $v$. The
greedy colour of $v$ must avoid exactly these colours. -/
noncomputable def greedyExcludedColors (v : V) : Finset ℕ :=
  {w ∈ (univ : Finset V) | w < v ∧ G.Adj w v}.image G.greedyColoring

variable {G}

/-- A natural number $k$ is an excluded colour at $v$ if and only if $k = c(w)$ for some neighbour
$w < v$ of $v$. -/
@[simp]
theorem mem_greedyExcludedColors {v : V} {k : ℕ} :
    k ∈ G.greedyExcludedColors v ↔ ∃ w, w < v ∧ G.Adj w v ∧ G.greedyColoring w = k := by
  simp only [greedyExcludedColors, mem_image, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨w, ⟨hlt, hadj⟩, hc⟩ => ⟨w, hlt, hadj, hc⟩,
    fun ⟨w, hlt, hadj, hc⟩ => ⟨w, ⟨hlt, hadj⟩, hc⟩⟩

/-- The greedy colour of $v$ is the least natural number that is not an excluded colour at $v$. -/
private theorem greedyColoring_eq_sInf (v : V) :
    G.greedyColoring v = sInf {k | k ∉ G.greedyExcludedColors v} := by
  rw [greedyColoring_def]
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, mem_greedyExcludedColors, not_exists]
  refine ⟨fun h w hw => ?_, fun h w hlt hadj hc => h w ⟨hlt, hadj, hc⟩⟩
  exact h w hw.1 hw.2.1 hw.2.2

/-- The greedy colour of $v$ is not an excluded colour at $v$, that is, it is not the colour of any
earlier neighbour of $v$. -/
theorem greedyColoring_notMem_excludedColors (v : V) :
    G.greedyColoring v ∉ G.greedyExcludedColors v := by
  obtain ⟨k, -, hk⟩ := exists_le_card_notMem (G.greedyExcludedColors v)
  have hne : {k | k ∉ G.greedyExcludedColors v}.Nonempty := ⟨k, hk⟩
  rw [greedyColoring_eq_sInf]
  exact Nat.sInf_mem hne

/-- The greedy colour of $v$ is at most the number of excluded colours at $v$. -/
theorem greedyColoring_le_card_excludedColors (v : V) :
    G.greedyColoring v ≤ #(G.greedyExcludedColors v) := by
  obtain ⟨k, hk, hk'⟩ := exists_le_card_notMem (G.greedyExcludedColors v)
  have hmem : k ∈ {k | k ∉ G.greedyExcludedColors v} := hk'
  rw [greedyColoring_eq_sInf]
  exact (Nat.sInf_le hmem).trans hk

/-- If $w < v$ and $w$ is adjacent to $v$, then $c(w) \neq c(v)$. -/
theorem greedyColoring_ne_of_lt_of_adj {v w : V} (hlt : w < v) (h : G.Adj w v) :
    G.greedyColoring w ≠ G.greedyColoring v := fun hc =>
  greedyColoring_notMem_excludedColors v (mem_greedyExcludedColors.2 ⟨w, hlt, h, hc⟩)

/-- The greedy colouring is proper: if $v$ and $w$ are adjacent, then $c(v) \neq c(w)$. -/
theorem greedyColoring_ne_of_adj {v w : V} (h : G.Adj v w) :
    G.greedyColoring v ≠ G.greedyColoring w := by
  rcases lt_or_gt_of_ne (G.ne_of_adj h) with hlt | hlt
  · exact greedyColoring_ne_of_lt_of_adj hlt h
  · exact (greedyColoring_ne_of_lt_of_adj hlt h.symm).symm

variable (G)

/-- The greedy colouring, as a proper colouring of $G$ by natural numbers (a `SimpleGraph.Coloring`
with colours in $\mathbb{N}$). -/
noncomputable def greedyColoring_isColoring : G.Coloring ℕ :=
  Coloring.mk G.greedyColoring fun h => greedyColoring_ne_of_adj h

/-- The greedy colouring as a proper colouring takes the value $c(v)$ at $v$. -/
@[simp]
theorem greedyColoring_isColoring_apply (v : V) :
    G.greedyColoring_isColoring v = G.greedyColoring v := rfl

variable [DecidableRel G.Adj]

/-- At each vertex $v$, the number of excluded colours is at most the degree of $v$. -/
theorem card_greedyExcludedColors_le_degree (v : V) :
    #(G.greedyExcludedColors v) ≤ G.degree v := by
  have hsub : G.greedyExcludedColors v ⊆ (G.neighborFinset v).image G.greedyColoring := by
    intro k hk
    obtain ⟨w, -, hadj, hc⟩ := mem_greedyExcludedColors.1 hk
    exact mem_image.2 ⟨w, (mem_neighborFinset G v w).2 hadj.symm, hc⟩
  exact (card_le_card hsub).trans card_image_le

/-- Let $G$ be a finite simple graph with a linear order on its vertices, and let $\Delta(G)$ be its
maximum degree. Then the greedy colour of every vertex $v$ satisfies
$$c(v) \le \Delta(G),$$
so the greedy colouring uses at most $\Delta(G) + 1$ colours.

At $v$ the excluded colours are the colours of the earlier neighbours of $v$, and there are at
most $\deg v \le \Delta(G)$ of them. So the least natural number outside them is at most
$\Delta(G)$. -/
theorem greedyColoring_le_maxDegree (v : V) : G.greedyColoring v ≤ G.maxDegree :=
  ((greedyColoring_le_card_excludedColors v).trans
    (G.card_greedyExcludedColors_le_degree v)).trans (G.degree_le_maxDegree v)

end SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every finite simple graph $G$ is $(\Delta(G) + 1)$-colourable, where $\Delta(G)$ is the maximum
degree of $G$.

The proof uses the greedy colouring along an arbitrary linear order on the vertices. The bound
does not depend on the order. -/
theorem colorable_maxDegree_add_one : G.Colorable (G.maxDegree + 1) := by
  let _ : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Equiv.injective _)
  exact (colorable_iff_exists_bdd_nat_coloring _).2
    ⟨G.greedyColoring_isColoring, fun v => Nat.lt_succ_of_le (G.greedyColoring_le_maxDegree v)⟩

end SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

/-- If $a, b, c \in \{0, 1\}$ with $a \neq c$ and $b \neq c$, then $a = b$. -/
private theorem fin_two_eq_of_ne_of_ne {a b c : Fin 2} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  revert ha hb; revert a b c; decide

/-- If $a, b, c \in \{0, 1\}$ with $b \neq c$, then $a = c$ if and only if $a \neq b$. -/
private theorem fin_two_eq_iff_ne {a b c : Fin 2} (h : b ≠ c) : a = c ↔ ¬ a = b := by
  revert h; revert a b c; decide

/-- If $x, y, z \in \{0, 1\}$ with $y \neq z$, then $x = z$ if and only if $x \neq y$. -/
private theorem nat_eq_iff_ne {x y z : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1) (h : y ≠ z) :
    x = z ↔ ¬ x = y := by omega

/-- Let $G$ have a proper two-colouring $C$, and let the order be a traversal order. Then for every
vertex $v$, $c(v) \le 1$, and for every $u < v$ reachable from $v$, $C(u) = C(v)$ if and only if
$c(u) = c(v)$. -/
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

/-- The **greedy colouring is optimal on a bipartite graph**, for a traversal order. Let $G$ be a
two-colourable finite simple graph with a linear order on its vertices. Suppose that every
vertex $v$ that has a vertex $u < v$ in its connected component has a neighbour $w < v$. Then
the greedy colour of every vertex $v$ satisfies $c(v) \le 1$.

The hypothesis on the order is necessary. On the path $0 - 2 - 3 - 1$ with the order
$0 < 1 < 2 < 3$, the greedy colouring uses three colours; see the module doc comment of
`Numlib.Combinatorics.SimpleGraph.Coloring`. -/
theorem greedyColoring_le_one_of_isBipartite (hG : G.Colorable 2)
    (hord : ∀ v : V, (∃ u, u < v ∧ G.Reachable u v) → ∃ w, w < v ∧ G.Adj w v) (v : V) :
    G.greedyColoring v ≤ 1 :=
  (greedyColoring_le_one_aux hG.some hord v).1

end SimpleGraph
