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

`SimpleGraph.sphere G v k` is the set of vertices at distance exactly `k` from `v` and reachable
from it: the `k`-th *level set* of a breadth-first traversal rooted at `v`. The spheres are pairwise
disjoint and cover the connected component of `v` (`SimpleGraph.pairwiseDisjoint_sphere`,
`SimpleGraph.iUnion_sphere`), and the one fact that makes them useful is that an edge changes the
distance to the root by at most one (`SimpleGraph.dist_le_dist_add_one_of_adj`,
`SimpleGraph.abs_dist_sub_dist_le_one_of_adj`). Hence no edge joins two spheres whose indices differ
by two or more (`SimpleGraph.not_adj_of_two_le_dist_sub_dist`), so every sphere separates the
spheres below it from the spheres above it (`SimpleGraph.isSeparator_sphere`).

This is the graph-theoretic content behind the level-set reorderings of a sparse matrix — the
Cuthill–McKee ordering and the separators of nested dissection — of [saad2003iterative] §3.3.3 and
§3.6.2: a reordering that lists the vertices in order of their distance to a root makes the matrix
block tridiagonal. The algorithm is not needed for that, because the sets a breadth-first search
marks at step `k` are exactly the distance spheres, so the theorems below are stated about
`SimpleGraph.dist` and about no traversal.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v w : V} {k l : ℕ}

/-! ### An edge changes the distance to a root by at most one -/

/-- Appending an edge to a geodesic: if `u` and `w` are adjacent then `w` is at most one step
further from `v` than `u` is. No reachability hypothesis is needed, because if `v` reaches neither
of them both distances are `0`. -/
theorem dist_le_dist_add_one_of_adj (h : G.Adj u w) (v : V) : G.dist v w ≤ G.dist v u + 1 := by
  have h' := h.reachable.dist_triangle_right (G := G) v
  rwa [dist_eq_one_iff_adj.2 h] at h'

/-- The symmetric form of `SimpleGraph.dist_le_dist_add_one_of_adj`: the distances to a root of the
two endpoints of an edge differ by at most one. -/
theorem abs_dist_sub_dist_le_one_of_adj (h : G.Adj u w) (v : V) :
    |(G.dist v u : ℤ) - (G.dist v w : ℤ)| ≤ 1 := by
  have h₁ := dist_le_dist_add_one_of_adj h v
  have h₂ := dist_le_dist_add_one_of_adj h.symm v
  rw [abs_le]
  omega

/-! ### The spheres around a root -/

/-- `G.sphere v k` is the set of vertices reachable from `v` and at distance exactly `k` from it:
the `k`-th level set of a breadth-first traversal rooted at `v`.

Reachability is part of the definition because `SimpleGraph.dist` is junk-valued at `0` on an
unreachable pair, which would otherwise put the whole of the rest of the graph into `G.sphere v 0`.
-/
def sphere (G : SimpleGraph V) (v : V) (k : ℕ) : Set V := {u | G.Reachable v u ∧ G.dist v u = k}

/-- Membership in a sphere, unfolded. -/
@[simp]
theorem mem_sphere : u ∈ G.sphere v k ↔ G.Reachable v u ∧ G.dist v u = k := Iff.rfl

/-- The sphere of radius zero is the root alone. -/
@[simp]
theorem sphere_zero (G : SimpleGraph V) (v : V) : G.sphere v 0 = {v} := by
  ext u
  simp only [mem_sphere, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hr, hd⟩
    exact (hr.dist_eq_zero_iff.1 hd).symm
  · rintro rfl
    exact ⟨Reachable.refl _, dist_self⟩

/-- Distinct spheres around the same root are disjoint. -/
theorem pairwiseDisjoint_sphere (G : SimpleGraph V) (v : V) :
    Pairwise (Function.onFun Disjoint (G.sphere v)) := by
  intro k l hkl
  simp only [Function.onFun, Set.disjoint_left]
  intro u hu hu'
  exact hkl ((mem_sphere.1 hu).2.symm.trans (mem_sphere.1 hu').2)

/-- The spheres around `v` cover the connected component of `v`. -/
theorem iUnion_sphere (G : SimpleGraph V) (v : V) :
    ⋃ k, G.sphere v k = (G.connectedComponentMk v).supp := by
  ext u
  simp only [Set.mem_iUnion, mem_sphere, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  exact ⟨fun ⟨_, h, _⟩ => h.symm, fun h => ⟨G.dist v u, h.symm, rfl⟩⟩

/-! ### The spheres are separators -/

/-- No edge joins two level sets whose indices differ by two or more. -/
theorem not_adj_of_two_le_dist_sub_dist (hu : u ∈ G.sphere v k) (hw : w ∈ G.sphere v l)
    (hkl : k + 2 ≤ l) : ¬ G.Adj u w := fun h => by
  have h' := dist_le_dist_add_one_of_adj h v
  rw [(mem_sphere.1 hu).2, (mem_sphere.1 hw).2] at h'
  omega

/-- Every sphere is a separator: deleting `G.sphere v k` leaves no edge between the union of the
spheres of smaller index and the union of the spheres of larger index.

This is the supply of separators behind the level-set reorderings of a sparse matrix and behind
nested dissection. The statement is vacuous at `k = 0`, where the first union is empty. -/
theorem isSeparator_sphere (G : SimpleGraph V) (v : V) (k : ℕ) :
    ∀ u ∈ ⋃ i < k, G.sphere v i, ∀ w ∈ ⋃ i, G.sphere v (k + 1 + i), ¬ G.Adj u w := by
  intro u hu w hw
  simp only [Set.mem_iUnion, exists_prop] at hu hw
  obtain ⟨i, hik, hui⟩ := hu
  obtain ⟨j, hwj⟩ := hw
  exact not_adj_of_two_le_dist_sub_dist hui hwj (by omega)

end SimpleGraph
