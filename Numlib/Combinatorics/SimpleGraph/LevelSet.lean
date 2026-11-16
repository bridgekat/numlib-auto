/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Combinatorics.SimpleGraph.Metric`.
Keep it free of dependencies on the rest of `Numlib`.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Distance spheres of a simple graph, and their separating property

Let $G$ be a simple graph and let $v$ be a vertex. The sphere $S_k(v)$ is the set of vertices that
are reachable from $v$ and at distance exactly $k$ from $v$. It is the $k$-th level set of a
breadth-first traversal from $v$. The spheres around $v$ are pairwise disjoint and cover the
connected component of $v$. The key fact is that an edge changes the distance to $v$ by at most one.
So no edge joins two spheres whose indices differ by two or more, and every sphere separates the
spheres below it from the spheres above it.

These facts are the graph-theoretic content of the level set orderings of a sparse matrix in
[saad2003iterative], §3.3.3 and §3.6.2: the Cuthill–McKee ordering and the separators of nested
dissection. An ordering that lists the vertices in the order of their distance to a root makes the
matrix block tridiagonal.

## Main definitions

* `SimpleGraph.sphere`: the set $S_k(v)$ of vertices reachable from $v$ at distance exactly $k$.

## Main results

* `SimpleGraph.dist_le_dist_add_one_of_adj`: if $u$ and $w$ are adjacent, then
  $d(v, w) \le d(v, u) + 1$.
* `SimpleGraph.abs_dist_sub_dist_le_one_of_adj`: if $u$ and $w$ are adjacent, then
  $|d(v, u) - d(v, w)| \le 1$.
* `SimpleGraph.pairwiseDisjoint_sphere`: distinct spheres around $v$ are disjoint.
* `SimpleGraph.iUnion_sphere`: the spheres around $v$ cover the connected component of $v$.
* `SimpleGraph.not_adj_of_two_le_dist_sub_dist`: no edge joins $S_k(v)$ and $S_l(v)$ when
  $l \ge k + 2$.
* `SimpleGraph.isSeparator_sphere`: no edge joins a sphere of index less than $k$ and a sphere of
  index greater than $k$.

## Implementation notes

* The distance $d(v, u)$ is `SimpleGraph.dist`. It has the value $0$ when $u$ is not reachable from
  $v$.
* No traversal is formalized. The sets that a breadth-first search marks at step $k$ are exactly the
  spheres, so the results are stated about `SimpleGraph.dist`.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v w : V} {k l : ℕ}

/-! ### An edge changes the distance to a root by at most one -/

/-- Let $u$ and $w$ be adjacent vertices of a simple graph $G$, and let $v$ be a vertex. Then
$$d(v, w) \le d(v, u) + 1.$$

No reachability hypothesis is needed. If $v$ reaches neither $u$ nor $w$, then both distances
are $0$. -/
theorem dist_le_dist_add_one_of_adj (h : G.Adj u w) (v : V) : G.dist v w ≤ G.dist v u + 1 := by
  have h' := h.reachable.dist_triangle_right (G := G) v
  rwa [dist_eq_one_iff_adj.2 h] at h'

/-- Let $u$ and $w$ be adjacent vertices of a simple graph $G$, and let $v$ be a vertex. Then the
distances to $v$ of the two endpoints differ by at most one:
$$|d(v, u) - d(v, w)| \le 1.$$
-/
theorem abs_dist_sub_dist_le_one_of_adj (h : G.Adj u w) (v : V) :
    |(G.dist v u : ℤ) - (G.dist v w : ℤ)| ≤ 1 := by
  have h₁ := dist_le_dist_add_one_of_adj h v
  have h₂ := dist_le_dist_add_one_of_adj h.symm v
  rw [abs_le]
  omega

/-! ### The spheres around a root -/

/-- The **sphere** of radius $k$ around a vertex $v$ of a simple graph $G$: the set
$$S_k(v) = \{ u : u \text{ is reachable from } v \text{ and } d(v, u) = k \}.$$
It is the $k$-th level set of a breadth-first traversal from $v$.

Reachability is part of the definition because `SimpleGraph.dist` has the value $0$ on a pair of
vertices that are not connected. Without it, $S_0(v)$ would contain every vertex outside the
connected component of $v$. -/
def sphere (G : SimpleGraph V) (v : V) (k : ℕ) : Set V := {u | G.Reachable v u ∧ G.dist v u = k}

/-- A vertex $u$ is in $S_k(v)$ if and only if $u$ is reachable from $v$ and $d(v, u) = k$. -/
@[simp]
theorem mem_sphere : u ∈ G.sphere v k ↔ G.Reachable v u ∧ G.dist v u = k := Iff.rfl

/-- The sphere of radius $0$ around $v$ is $\{v\}$. -/
@[simp]
theorem sphere_zero (G : SimpleGraph V) (v : V) : G.sphere v 0 = {v} := by
  ext u
  simp only [mem_sphere, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hr, hd⟩
    exact (hr.dist_eq_zero_iff.1 hd).symm
  · rintro rfl
    exact ⟨Reachable.refl _, dist_self⟩

/-- Distinct spheres around the same vertex are disjoint: $S_k(v) \cap S_l(v) = \emptyset$ for
$k \neq l$. -/
theorem pairwiseDisjoint_sphere (G : SimpleGraph V) (v : V) :
    Pairwise (Function.onFun Disjoint (G.sphere v)) := by
  intro k l hkl
  simp only [Function.onFun, Set.disjoint_left]
  intro u hu hu'
  exact hkl ((mem_sphere.1 hu).2.symm.trans (mem_sphere.1 hu').2)

/-- The spheres around $v$ cover the connected component of $v$: $\bigcup_k S_k(v)$ is the set of
vertices in the connected component of $v$. -/
theorem iUnion_sphere (G : SimpleGraph V) (v : V) :
    ⋃ k, G.sphere v k = (G.connectedComponentMk v).supp := by
  ext u
  simp only [Set.mem_iUnion, mem_sphere, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  exact ⟨fun ⟨_, h, _⟩ => h.symm, fun h => ⟨G.dist v u, h.symm, rfl⟩⟩

/-! ### The spheres are separators -/

/-- Let $u \in S_k(v)$ and $w \in S_l(v)$ with $l \ge k + 2$. Then $u$ and $w$ are not adjacent. -/
theorem not_adj_of_two_le_dist_sub_dist (hu : u ∈ G.sphere v k) (hw : w ∈ G.sphere v l)
    (hkl : k + 2 ≤ l) : ¬ G.Adj u w := fun h => by
  have h' := dist_le_dist_add_one_of_adj h v
  rw [(mem_sphere.1 hu).2, (mem_sphere.1 hw).2] at h'
  omega

/-- Every sphere is a separator. Let $v$ be a vertex of a simple graph $G$ and let
$k \in \mathbb{N}$. Then no edge joins a vertex of $\bigcup_{i < k} S_i(v)$ and a vertex of
$\bigcup_{i > k} S_i(v)$. So the deletion of $S_k(v)$ separates the spheres of smaller index
from the spheres of larger index.

This gives the separators of the level set orderings of a sparse matrix and of nested
dissection. For $k = 0$ the statement is vacuous, because the first union is empty. -/
theorem isSeparator_sphere (G : SimpleGraph V) (v : V) (k : ℕ) :
    ∀ u ∈ ⋃ i < k, G.sphere v i, ∀ w ∈ ⋃ i, G.sphere v (k + 1 + i), ¬ G.Adj u w := by
  intro u hu w hw
  simp only [Set.mem_iUnion, exists_prop] at hu hw
  obtain ⟨i, hik, hui⟩ := hu
  obtain ⟨j, hwj⟩ := hw
  exact not_adj_of_two_le_dist_sub_dist hui hwj (by omega)

end SimpleGraph
