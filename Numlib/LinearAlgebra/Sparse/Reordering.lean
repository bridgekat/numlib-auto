/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: beside `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Numlib.Combinatorics.SimpleGraph.Coloring
import Numlib.Combinatorics.SimpleGraph.LevelSet
import Numlib.LinearAlgebra.Sparse.Pattern

/-!
# What a graph ordering does to the pattern of a matrix

Let $A$ be a square matrix indexed by a type $n$, and let $G(A)$ be its pattern graph
`Matrix.adjGraph`, in which two distinct indices $i \neq j$ are adjacent when $a_{ij} \neq 0$ or
$a_{ji} \neq 0$. The three reorderings of [saad2003iterative], §3.3.3 (level sets from breadth-first
search or Cuthill–McKee, independent sets, and multicoloring) each label the vertices of $G(A)$.
Each labelling gives a block structure of the permuted matrix $A_{\sigma\sigma}$ (`A.submatrix σ σ`)
for every permutation $\sigma$ that is compatible with the labelling. This module translates the
graph-theoretic facts into statements about matrix entries. The statements are about the labelling,
not about a permutation, so no reordering algorithm has to be formalized. The graph theory is in
`Numlib.Combinatorics.SimpleGraph.LevelSet` and `Numlib.Combinatorics.SimpleGraph.Coloring`.

If $a_{ij} \neq 0$ with $i \neq j$, the distances of $i$ and $j$ to a root $v$ in $G(A)$ differ by
at most one. Hence an ordering in which the distance to $v$ is monotone is block tridiagonal, with
the level sets as blocks. Two distinct indices of the same color of a proper coloring of $G(A)$
carry no entry, so a color-grouped ordering has diagonal matrices as its diagonal blocks. An
independent set is the two-class case, which gives the block form (3.3) of [saad2003iterative] with
a diagonal leading block. A matrix with a symmetric pattern and at most $\nu$ off-diagonal nonzeros
in each row always has such a coloring with $\nu + 1$ colors.

## Main results

* `Matrix.abs_dist_sub_dist_le_one_of_apply_ne_zero`: if $a_{ij} \neq 0$ and $i \neq j$, then
  $|d(v, i) - d(v, j)| \le 1$ for every root $v$.
* `Matrix.apply_eq_zero_of_dist_lt`: if $d(v, i) + 2 \le d(v, j)$, then $a_{ij} = 0$.
* `Matrix.apply_eq_zero_of_dist_lt'`: if $d(v, j) + 2 \le d(v, i)$, then $a_{ij} = 0$.
* `Matrix.apply_eq_zero_of_coloring_eq`: if $c$ is a proper coloring of $G(A)$, $i \neq j$ and
  $c(i) = c(j)$, then $a_{ij} = 0$.
* `Matrix.apply_eq_zero_of_isIndepSet`: if $i \neq j$ lie in an independent set of $G(A)$, then
  $a_{ij} = 0$.
* `Matrix.maxDegree_adjGraph_le`: for a symmetric pattern, the maximum degree of $G(A)$ is at most
  any bound on the number of off-diagonal nonzeros in a row.
* `Matrix.exists_coloring_of_le_maxDegree`: a symmetric pattern with at most $\nu$ off-diagonal
  nonzeros in each row has a labelling by $\nu + 1$ classes in which two distinct indices with the
  same label carry no entry.

## Implementation notes

* The graph `Matrix.adjGraph A` is the symmetrized pattern graph `SimpleGraph.fromRel (A · · ≠ 0)`.
  A nonzero off-diagonal entry is therefore an edge without any symmetry hypothesis on the pattern,
  and the first five results have no such hypothesis.
* The level-set results do not need every index to be reachable from the root, because
  `SimpleGraph.abs_dist_sub_dist_le_one_of_adj` does not need it. The distance `SimpleGraph.dist` is
  zero between vertices that are not connected.
* Only `Matrix.maxDegree_adjGraph_le`, and through it `Matrix.exists_coloring_of_le_maxDegree`,
  needs a symmetric pattern. It needs it to bound the degree of the symmetrized graph by a count of
  nonzeros in one row.
* Algorithms 3.1–3.6 of [saad2003iterative] are not formalized. The theorems hold for every
  labelling with the stated property, which includes the labellings that the algorithms compute.
-/

open Finset

namespace Matrix

variable {n R : Type*} [Zero R] {A : Matrix n n R}

/-! ### Level-set orderings -/

/-- Let $A$ be a square matrix indexed by $n$, and let $d$ be the graph distance in the pattern
graph $G(A)$ (`Matrix.adjGraph`). If $a_{ij} \neq 0$ and $i \neq j$, then for every root $v$,
$$|d(v, i) - d(v, j)| \le 1.$$

This is the property of [saad2003iterative], §3.3.3, that makes the level sets separators. The
distance `SimpleGraph.dist` is a natural number, and it is zero between vertices that are not
connected; the difference is taken in $\mathbb{Z}$. No symmetry of the pattern is needed,
because $G(A)$ is symmetrized. -/
theorem abs_dist_sub_dist_le_one_of_apply_ne_zero {i j : n} (h : A i j ≠ 0) (hij : i ≠ j)
    (v : n) : |(A.adjGraph.dist v i : ℤ) - (A.adjGraph.dist v j : ℤ)| ≤ 1 :=
  SimpleGraph.abs_dist_sub_dist_le_one_of_adj (adjGraph_adj.2 ⟨hij, Or.inl h⟩) v

/-- A **level-set ordering is block tridiagonal** ([saad2003iterative], §3.3.3). Let $A$ be a square
matrix indexed by $n$, let $d$ be the graph distance in the pattern graph $G(A)$, and let $v$ be
a root. If $d(v, i) + 2 \le d(v, j)$, then $a_{ij} = 0$.

The result is stated for the labelling $i \mapsto d(v, i)$, not for a permutation. For every
permutation $\sigma$ along which this labelling is monotone, it says that $A_{\sigma\sigma}$
(`A.submatrix σ σ`) is block tridiagonal, with the level sets
`SimpleGraph.sphere (Matrix.adjGraph A) v k` as its blocks. A breadth-first or Cuthill–McKee
reordering produces such a permutation.

The hypothesis is $d(v, i) + 2 \le d(v, j)$, not $d(v, i) < d(v, j)$: adjacent levels can carry
entries, and only a gap of two or more levels forces a zero. -/
theorem apply_eq_zero_of_dist_lt {i j : n} (v : n)
    (h : A.adjGraph.dist v i + 2 ≤ A.adjGraph.dist v j) : A i j = 0 := by
  by_contra h0
  have hij : i ≠ j := by rintro rfl; omega
  have := abs_dist_sub_dist_le_one_of_apply_ne_zero h0 hij v
  rw [abs_le] at this
  omega

/-- Let $A$ be a square matrix indexed by $n$, let $d$ be the graph distance in the pattern graph
$G(A)$, and let $v$ be a root. If $d(v, j) + 2 \le d(v, i)$, then $a_{ij} = 0$. This is the
mirror image of `Matrix.apply_eq_zero_of_dist_lt`. -/
theorem apply_eq_zero_of_dist_lt' {i j : n} (v : n)
    (h : A.adjGraph.dist v j + 2 ≤ A.adjGraph.dist v i) : A i j = 0 := by
  by_contra h0
  have hij : i ≠ j := by rintro rfl; omega
  have := abs_dist_sub_dist_le_one_of_apply_ne_zero h0 hij v
  rw [abs_le] at this
  omega

/-! ### Multicolor and independent-set orderings -/

/-- A **multicolor ordering has diagonal diagonal blocks** ([saad2003iterative], §3.3.3). Let $A$ be
a square matrix indexed by $n$, and let $c$ be a proper coloring of the pattern graph $G(A)$
with colors in a type $\alpha$. If $i \neq j$ and $c(i) = c(j)$, then $a_{ij} = 0$.

With two colors, this is Property A (Definition 4.11) of [saad2003iterative] and its equation
(4.42). -/
theorem apply_eq_zero_of_coloring_eq {α : Type*} (c : A.adjGraph.Coloring α) {i j : n}
    (hij : i ≠ j) (h : c i = c j) : A i j = 0 := by
  by_contra h0
  exact c.valid (adjGraph_adj.2 ⟨hij, Or.inl h0⟩) h

/-- An **independent set is a diagonal block** ([saad2003iterative], §3.3.3). Let $A$ be a square
matrix indexed by $n$, and let $s$ be an independent set of the pattern graph $G(A)$. If
$i, j \in s$ and $i \neq j$, then $a_{ij} = 0$.

This is the diagonal leading block of the block form (3.3) of [saad2003iterative]. -/
theorem apply_eq_zero_of_isIndepSet {s : Set n} (hs : A.adjGraph.IsIndepSet s) {i j : n}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) : A i j = 0 := by
  by_contra h0
  exact (SimpleGraph.isIndepSet_iff _).1 hs hi hj hij (adjGraph_adj.2 ⟨hij, Or.inl h0⟩)

/-- The **degree of the pattern graph counts one row** ([saad2003iterative], §3.3.3). Let $A$ be a
square matrix indexed by a finite type $n$, with a symmetric pattern: $a_{ij} \neq 0$ implies
$a_{ji} \neq 0$. If each row $i$ has at most $\nu$ nonzero entries $a_{ij}$ with $j \neq i$,
then the maximum degree of the pattern graph $G(A)$ is at most $\nu$.

This is the one step of §3.3.3 that needs a symmetric pattern. The graph `Matrix.adjGraph` is
symmetrized and has no loops: it joins $i$ to $j$ when $a_{ij} \neq 0$ or $a_{ji} \neq 0$.
Without symmetry, the degree at $i$ also counts the nonzeros of column $i$. The count in the
hypothesis excludes the diagonal: the adjacency graph of [saad2003iterative] has a self-loop at
every nonzero diagonal entry, but the reorderings act on the graph without loops. -/
theorem maxDegree_adjGraph_le [Fintype n] [DecidableEq n] [DecidableEq R]
    [DecidableRel A.adjGraph.Adj] {ν : ℕ} (hsymm : ∀ i j, A i j ≠ 0 → A j i ≠ 0)
    (hrow : ∀ i, #{j ∈ univ | j ≠ i ∧ A i j ≠ 0} ≤ ν) : A.adjGraph.maxDegree ≤ ν := by
  refine SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun i => ?_
  refine le_trans (Finset.card_le_card ?_) (hrow i)
  intro j hj
  rw [SimpleGraph.mem_neighborFinset, adjGraph_adj] at hj
  exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hj.1.symm, hj.2.elim id fun h => hsymm _ _ h⟩

/-- A **multicolor ordering with $\nu + 1$ blocks always exists** ([saad2003iterative], §3.3.3 and
Problem P-3.10). Let $A$ be a square matrix indexed by a finite type $n$, with a symmetric
pattern: $a_{ij} \neq 0$ implies $a_{ji} \neq 0$. If each row $i$ has at most $\nu$ nonzero
entries $a_{ij}$ with $j \neq i$, then there is a labelling $c \colon n \to \{0, \dots, \nu\}$
such that
$$i \neq j \text{ and } c(i) = c(j) \implies a_{ij} = 0.$$

The proof applies the greedy coloring bound `SimpleGraph.colorable_maxDegree_add_one` to the
pattern graph, whose degree is bounded by `Matrix.maxDegree_adjGraph_le`. The labels are
`Fin (ν + 1)`. -/
theorem exists_coloring_of_le_maxDegree [Fintype n] [DecidableEq n] [DecidableEq R] {ν : ℕ}
    (hsymm : ∀ i j, A i j ≠ 0 → A j i ≠ 0)
    (hrow : ∀ i, #{j ∈ univ | j ≠ i ∧ A i j ≠ 0} ≤ ν) :
    ∃ c : n → Fin (ν + 1), ∀ i j, i ≠ j → c i = c j → A i j = 0 := by
  let _ : DecidableRel A.adjGraph.Adj := fun _ _ => decidable_of_iff _ adjGraph_adj.symm
  obtain ⟨c⟩ := (A.adjGraph.colorable_maxDegree_add_one).mono
    (Nat.succ_le_succ (maxDegree_adjGraph_le hsymm hrow))
  exact ⟨c, fun i j hij h => apply_eq_zero_of_coloring_eq c hij h⟩

end Matrix
