import Numlib.Combinatorics.SimpleGraph.IndepSet
import Numlib.LinearAlgebra.Sparse.Reordering

/-!
# Saad §3.3: permutations and reorderings

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §3.3: Definition 3.1 and Proposition 3.2 (§3.3.1), the relation with the adjacency graph
(§3.3.2), the three common reorderings (§3.3.3) and irreducibility (§3.3.4).

§3.3.1 is Mathlib.  Saad's row and column `π`-permutations of `A` are `A.submatrix π id` and
`A.submatrix id π`, his `P_π` is `Equiv.Perm.permMatrix`, and Proposition 3.2 is
`PEquiv.toMatrix_toPEquiv_mul` and `PEquiv.mul_toMatrix_toPEquiv`; even the anti-homomorphism
convention of (3.1) is Mathlib's `Matrix.permMatrix_mul`.  The symmetric permutation
`A.submatrix σ σ = P_σ A P_σᵀ`, which every later chapter uses, is
`Matrix.submatrix_eq_permMatrix_mul_mul_transpose`.

The reorderings of §3.3.3 are Algorithms 3.1–3.6, whose theorems are about the *labelling* they
produce and not about the recursion, so nothing here formalizes a traversal: the level-set
statement is about `SimpleGraph.dist`, the multicolour statement about a proper colouring, the
independent-set statement about a maximal independent set.  That is how
`Numlib/LinearAlgebra/Sparse/Reordering` and `Numlib/Combinatorics/SimpleGraph` state them, and
this file specializes them to a matrix.  The exception is greedy colouring itself, about which the
book does make claims (Algorithm 3.6 uses two colours on a bipartite graph under a suitable
traversal, and never more than `maxDegree + 1`); those are `greedy_coloring_bounds`.

**No pattern-symmetry hypothesis is needed except for the colouring bounds.**  `Matrix.adjGraph`
is the *symmetrized* graph `SimpleGraph.fromRel (A · · ≠ 0)`, so a nonzero off-diagonal entry
already is an adjacency, and the level-set, independent-set and multicolour block statements hold
for an arbitrary pattern.  Symmetry enters only where the *degree* of the symmetrized graph has to
be bounded by a count of nonzeros in one row, that is in `exists_multicoloring` and in
`greedy_coloring_bounds`.  For the same reason the level-set statement needs no connectedness: an
index unreachable from the root has distance zero, on both sides of the comparison.

Two things get no declaration.  Reverse Cuthill–McKee is given by the book as an observation of
George's, with a picture and no statement, and this edition proves no bandwidth or profile bound
to compare against.  And the book's warning that a *nonsymmetric* permutation does not preserve
the adjacency graph is recorded here rather than proved, the book giving no statement either: for
`A = !![0, 1; 1, 0]` the graph of `A` is the edge `0 — 1`, while `A.submatrix id (Equiv.swap 0 1)`
is the identity matrix, whose graph has no edge at all — so a one-sided permutation can destroy
connectivity, and `adjGraph_submatrix` really does need `σ` on both sides.
-/

open Finset Matrix

namespace SaadSparse.Chapter03

variable {n : ℕ}

/-! ### §3.3.1 Permutation matrices: Definition 3.1 and Proposition 3.2 -/

/-- **Saad Definition 3.1 and Proposition 3.2**, with the symmetric permutation of §3.3.1: the row
`π`-permutation `A_{π,*}` of `A` is `A.submatrix π id = P_π A`, the column `π`-permutation
`A_{*,π}` is `A.submatrix id π = A P_πᵀ`, permutation matrices are orthogonal, and the symmetric
permutation `A.submatrix π π = P_π A P_πᵀ` is a similarity transformation.

Every clause is Mathlib's `PEquiv.toMatrix_toPEquiv_mul`, `PEquiv.mul_toMatrix_toPEquiv`,
`Matrix.transpose_permMatrix` and `Matrix.permMatrix_mul`.  Problem P-3.3 is the same lemmas read
in the direction `P_π = I_{π,*}`, which is the first clause at `A = 1`. -/
theorem proposition_3_2 (A : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) :
    A.submatrix π id = π.permMatrix ℝ * A ∧
      A.submatrix id π = A * (π.permMatrix ℝ)ᵀ ∧
      (π.permMatrix ℝ)ᵀ * π.permMatrix ℝ = 1 ∧
      (π.permMatrix ℝ)⁻¹ = (π.permMatrix ℝ)ᵀ ∧
      A.submatrix π π = π.permMatrix ℝ * A * (π.permMatrix ℝ)ᵀ := by
  have hunit : (π.permMatrix ℝ)ᵀ * π.permMatrix ℝ = 1 := by
    rw [transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  refine ⟨(PEquiv.toMatrix_toPEquiv_mul _ A).symm, ?_, hunit, inv_eq_left_inv hunit,
    submatrix_eq_permMatrix_mul_mul_transpose A π⟩
  rw [transpose_permMatrix]
  exact (PEquiv.mul_toMatrix_toPEquiv A (π⁻¹ : Equiv.Perm (Fin n))).symm

/-! ### §3.3.2 Relations with the adjacency graph -/

/-- **Saad §3.3.2**: a symmetric permutation only relabels the adjacency graph.  Both the directed
graph of the pattern and its symmetrized form are carried across by `σ`, so colourability,
connectivity and irreducibility are invariants of a symmetric permutation — which is why every
reordering of the book is `A.submatrix σ σ`.  Packaged as a graph isomorphism this is
`Matrix.adjGraphIso`. -/
theorem adjGraph_submatrix (A : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) :
    (∀ i j, (A.submatrix σ σ).adjDigraph.Adj i j ↔ A.adjDigraph.Adj (σ i) (σ j)) ∧
      (∀ i j, (A.submatrix σ σ).adjGraph.Adj i j ↔ A.adjGraph.Adj (σ i) (σ j)) ∧
      (∀ k : ℕ, (A.submatrix σ σ).adjGraph.Colorable k ↔ A.adjGraph.Colorable k) ∧
      ((A.submatrix σ σ).adjGraph.Preconnected ↔ A.adjGraph.Preconnected) ∧
      ((A.submatrix σ σ).IsPatternIrreducible ↔ A.IsPatternIrreducible) := by
  refine ⟨adjDigraph_submatrix_adj A σ, adjGraph_submatrix_adj A σ,
    fun k => colorable_adjGraph_submatrix_iff A σ, preconnected_adjGraph_submatrix_iff A σ,
    ⟨fun h => ?_, fun h => h.submatrix σ⟩⟩
  have h' := h.submatrix σ⁻¹
  rw [submatrix_submatrix, ← Equiv.Perm.coe_mul, mul_inv_cancel] at h'
  simpa using h'

/-! ### §3.3.3 Common reorderings: level sets -/

/-- **Saad §3.3.3, level-set orderings**: the distances to a root of the two indices of a nonzero
off-diagonal entry differ by at most one, so an entry two or more levels off the diagonal band
vanishes, and any ordering monotone in the distance to the root — breadth-first search (Algorithm
3.1) and Cuthill–McKee (Algorithms 3.2 and 3.3) — makes `A.submatrix σ σ` block tridiagonal with
the level sets `SimpleGraph.sphere` as its blocks.  The last clause is the separator form that
§3.6.2 reuses for nested dissection: no edge joins the ball of radius `k` to the levels beyond
`k + 1`, so removing level `k` disconnects the graph.

`Matrix.abs_dist_sub_dist_le_one_of_apply_ne_zero`, `Matrix.apply_eq_zero_of_dist_lt` and
`SimpleGraph.isSeparator_sphere`.  The book leaves the connectedness of the graph implicit — the
traversal does not exhaust the vertices without it — but none of these statements needs it, since
an index unreachable from `v` has distance zero on both sides. -/
theorem levelSet_blockTridiagonal (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n) :
    (∀ i j, A i j ≠ 0 → i ≠ j →
        |(A.adjGraph.dist v i : ℤ) - (A.adjGraph.dist v j : ℤ)| ≤ 1) ∧
      (∀ i j, A.adjGraph.dist v i + 2 ≤ A.adjGraph.dist v j → A i j = 0) ∧
      (∀ i j, A.adjGraph.dist v j + 2 ≤ A.adjGraph.dist v i → A i j = 0) ∧
      (∀ (k : ℕ) (u : Fin n), u ∈ ⋃ i, ⋃ (_ : i < k), A.adjGraph.sphere v i →
        ∀ w ∈ ⋃ i, A.adjGraph.sphere v (k + 1 + i), ¬ A.adjGraph.Adj u w) :=
  ⟨fun _ _ h hij => abs_dist_sub_dist_le_one_of_apply_ne_zero h hij v,
    fun _ _ h => apply_eq_zero_of_dist_lt v h,
    fun _ _ h => apply_eq_zero_of_dist_lt' v h,
    fun k => A.adjGraph.isSeparator_sphere v k⟩

/-! ### §3.3.3 Common reorderings: independent sets -/

/-- **Saad §3.3.3, the size of an independent set**: a maximal independent set `S` of indices of an
`n × n` matrix satisfies `n ≤ (Δ + 1) |S|`, that is `|S| ≥ n / (1 + Δ)`, with `Δ` the maximum
degree of the adjacency graph; and the sharper form in which the degree bound is required only at
the members of `S`.  `SimpleGraph.card_le_mul_card_of_maximal_isIndepSet`.

Saad states the bound for the set Algorithm 3.4 produces; the argument he gives — every index is
in `S` or adjacent to a member of it — proves it for any maximal independent set, which is how it
is stated.  The heuristic recurrence `n_i = n_{i-1} - ν_i - 1` after it is a rule of thumb, as the
book says. -/
theorem indepSet_card_ge (A : Matrix (Fin n) (Fin n) ℝ) [DecidableRel A.adjGraph.Adj]
    {s : Finset (Fin n)} (hs : Maximal A.adjGraph.IsIndepSet (s : Set (Fin n))) (ν : ℕ) :
    n ≤ (A.adjGraph.maxDegree + 1) * #s ∧
      ((∀ w ∈ s, A.adjGraph.degree w ≤ ν) → n ≤ (ν + 1) * #s) := by
  constructor
  · simpa using SimpleGraph.card_le_mul_card_of_maximal_isIndepSet hs
  · intro hν
    simpa using SimpleGraph.card_le_mul_card_of_maximal_isIndepSet_of_forall_degree_le hs hν

/-- **Saad §3.3.3, the form (3.3)**: if the first block of indices of a reordering is an
independent set of the adjacency graph, then the leading diagonal block of the reordered matrix is
*diagonal*, so `A.submatrix σ σ` has the shape `[[D, E], [F, C]]` with `D` diagonal.
`Matrix.apply_eq_zero_of_isIndepSet`. -/
theorem equation_3_3 (A : Matrix (Fin n) (Fin n) ℝ) {s : Set (Fin n)}
    (hs : A.adjGraph.IsIndepSet s) (σ : Equiv.Perm (Fin n)) :
    (∀ i j, i ∈ s → j ∈ s → i ≠ j → A i j = 0) ∧
      (∀ i j, σ i ∈ s → σ j ∈ s → i ≠ j → (A.submatrix σ σ) i j = 0) :=
  ⟨fun _ _ hi hj hij => apply_eq_zero_of_isIndepSet hs hi hj hij,
    fun _ _ hi hj hij => apply_eq_zero_of_isIndepSet hs hi hj (σ.injective.ne hij)⟩

/-! ### §3.3.3 Common reorderings: multicolouring -/

/-- **Saad §3.3.3, multicolour orderings**: two distinct indices of the same colour of a proper
colouring of the adjacency graph carry no entry, so grouping the indices by colour makes every
diagonal block of `A.submatrix σ σ` a diagonal matrix.
`Matrix.apply_eq_zero_of_coloring_eq`; no hypothesis on the pattern is needed, because
`Matrix.adjGraph` is already the symmetrized graph.

With two colours this is Saad's Property A (Definition 4.11) and the block form (4.42); the bridge
to `SaadSparse.Chapter04.HasPropertyA` belongs on the Chapter 4 side, which imports this one. -/
theorem multicoloring_blocks {α : Type*} (A : Matrix (Fin n) (Fin n) ℝ)
    (c : A.adjGraph.Coloring α) (σ : Equiv.Perm (Fin n)) :
    (∀ i j, i ≠ j → c i = c j → A i j = 0) ∧
      (∀ i j, i ≠ j → c (σ i) = c (σ j) → (A.submatrix σ σ) i j = 0) :=
  ⟨fun _ _ hij h => apply_eq_zero_of_coloring_eq c hij h,
    fun _ _ hij h => apply_eq_zero_of_coloring_eq c (σ.injective.ne hij) h⟩

/-- **Saad §3.3.3 and Problem P-3.10**: a matrix with a symmetric pattern and at most `ν`
off-diagonal nonzeros in each row admits a multicolour ordering with `ν + 1` colours.
`Matrix.exists_coloring_of_le_maxDegree`, the greedy bound applied to the adjacency graph.

Symmetry of the pattern is what is needed here and nowhere else in §3.3.3: the degree of the
*symmetrized* graph at `i` is a count of nonzeros of row `i` only when a nonzero `A j i` forces a
nonzero `A i j`.  Note that the count excludes the diagonal, since Saad's adjacency graph has a
self-loop at every nonzero diagonal entry and the reorderings act on the loopless graph. -/
theorem exists_multicoloring (A : Matrix (Fin n) (Fin n) ℝ) {ν : ℕ}
    (hsymm : ∀ i j, A i j ≠ 0 → A j i ≠ 0)
    (hrow : ∀ i, #{j ∈ univ | j ≠ i ∧ A i j ≠ 0} ≤ ν) :
    ∃ c : Fin n → Fin (ν + 1), ∀ i j, i ≠ j → c i = c j → A i j = 0 :=
  exists_coloring_of_le_maxDegree hsymm hrow

/-- The maximum degree of the adjacency graph of a matrix with a symmetric pattern is bounded by a
count of off-diagonal nonzeros in a single row.  This is the one step of §3.3.3 that needs pattern
symmetry; it is proved inside `Matrix.exists_coloring_of_le_maxDegree` and wants a name of its own
in `Numlib/LinearAlgebra/Sparse/Reordering`. -/
private theorem maxDegree_adjGraph_le {A : Matrix (Fin n) (Fin n) ℝ}
    [DecidableRel A.adjGraph.Adj] {ν : ℕ} (hsymm : ∀ i j, A i j ≠ 0 → A j i ≠ 0)
    (hrow : ∀ i, #{j ∈ univ | j ≠ i ∧ A i j ≠ 0} ≤ ν) : A.adjGraph.maxDegree ≤ ν := by
  refine SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun i => ?_
  refine le_trans (Finset.card_le_card ?_) (hrow i)
  intro j hj
  rw [SimpleGraph.mem_neighborFinset, adjGraph_adj] at hj
  exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hj.1.symm, hj.2.elim id fun h => hsymm _ _ h⟩

/-- **Saad §3.3.3 and Problems P-3.9, P-3.10, P-3.11**: the greedy colouring of Algorithm 3.6
applied to the adjacency graph of `A` never uses more than `ν + 1` colours, where `ν` bounds the
number of off-diagonal nonzeros in a row (P-3.10); and on a matrix whose adjacency graph is
bipartite it uses only two, provided the traversal visits, after the first index of each connected
component, only indices adjacent to an already-visited one — the hypothesis of P-3.11(b), which
breadth-first search satisfies and an arbitrary traversal does not (P-3.11(a)).

`SimpleGraph.greedyColoring_le_maxDegree` and `SimpleGraph.greedyColoring_le_one_of_isBipartite`.
The order along which the colouring proceeds is the given `LinearOrder` on the index type, so the
"traversal" of Algorithm 3.6 is the identity ordering of a matrix already reordered.  Problem
P-3.9, that the five-point grid is two-coloured, is the second clause at the graph of
`SaadSparse.Chapter02.laplacian2D`. -/
theorem greedy_coloring_bounds (A : Matrix (Fin n) (Fin n) ℝ) {ν : ℕ}
    (hsymm : ∀ i j, A i j ≠ 0 → A j i ≠ 0)
    (hrow : ∀ i, #{j ∈ univ | j ≠ i ∧ A i j ≠ 0} ≤ ν) :
    (∀ v, A.adjGraph.greedyColoring v ≤ ν) ∧
      (A.adjGraph.Colorable 2 →
        (∀ v : Fin n, (∃ u, u < v ∧ A.adjGraph.Reachable u v) →
          ∃ w, w < v ∧ A.adjGraph.Adj w v) →
        ∀ v, A.adjGraph.greedyColoring v ≤ 1) := by
  classical
  exact ⟨fun v => (A.adjGraph.greedyColoring_le_maxDegree v).trans
      (maxDegree_adjGraph_le hsymm hrow),
    fun h2 hord v => SimpleGraph.greedyColoring_le_one_of_isBipartite h2 hord v⟩

/-! ### §3.3.4 Irreducibility -/

/-- **Saad §3.3.4**: a matrix is *reducible* when a symmetric permutation puts it in block upper
triangular form, and *irreducible* otherwise; equivalently, its adjacency graph is strongly
connected, which is what Saad's "connected", read for a directed graph with directed paths, means.
That equivalence is the definition of `Matrix.IsPatternIrreducible`, and the block form is
`Matrix.isPatternIrreducible_iff_forall_submatrix_not_blockTriangular`.

The hypothesis `2 ≤ n` is necessary: irreducibility asks for a path of *positive* length between
every pair of indices, so the `1 × 1` zero matrix is reducible while its index type has no proper
nonempty subset to split.  This is the notion Definition 4.5, Theorem 4.7, Corollary 4.8 and
Theorem 4.9 of the Chapter 4 surface use.  The full Frobenius normal form — the diagonal blocks
are the strongly connected components in a topological order — is not proved. -/
theorem isPatternIrreducible_iff (A : Matrix (Fin n) (Fin n) ℝ) (hn : 2 ≤ n) :
    (A.IsPatternIrreducible ↔ ∀ (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)),
        s.Nonempty → s ≠ univ → ∃ i ∈ s, ∃ j ∉ s, (A.submatrix σ σ) i j ≠ 0) ∧
      (¬ A.IsPatternIrreducible ↔ ∃ (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)),
        s.Nonempty ∧ s ≠ univ ∧ ∀ i ∈ s, ∀ j ∉ s, (A.submatrix σ σ) i j = 0) :=
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  ⟨isPatternIrreducible_iff_forall_submatrix_not_blockTriangular,
    not_isPatternIrreducible_iff_exists_submatrix_blockTriangular⟩

end SaadSparse.Chapter03
