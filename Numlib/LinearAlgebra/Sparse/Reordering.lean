/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: beside `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Combinatorics.SimpleGraph.Coloring
import Numlib.Combinatorics.SimpleGraph.LevelSet
import Numlib.LinearAlgebra.Sparse.Pattern
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# What a graph ordering does to the pattern of a matrix

Each of the three reorderings of Saad[^saad-iterative] §3.3.3 — level sets (breadth-first search,
Cuthill–McKee), independent sets, multicolouring — is a *labelling* of the vertices of
`Matrix.adjGraph A`, and each gives a block structure of `A.submatrix σ σ` for any permutation `σ`
compatible with the labelling. The graph-theoretic content lives in
`Numlib/Combinatorics/SimpleGraph`; what is here is only the translation to matrix entries, and it
is stated for the labelling rather than for a permutation, so that no algorithm has to be
formalized:

* `Matrix.abs_dist_sub_dist_le_one_of_apply_ne_zero`: a nonzero off-diagonal entry joins two
  indices whose distances to a root differ by at most one, so
  `Matrix.apply_eq_zero_of_dist_lt` says that a distance-monotone reordering is block
  tridiagonal with the level sets as its blocks;
* `Matrix.apply_eq_zero_of_coloring_eq`: two indices of the same colour of a proper colouring of
  the pattern graph carry no entry, so the diagonal blocks of a colour-grouped reordering are
  diagonal matrices, and `Matrix.apply_eq_zero_of_isIndepSet` is the two-class case, Saad's block
  form (3.3) with a diagonal leading block;
* `Matrix.exists_coloring_of_le_maxDegree`: a symmetric pattern with at most `ν` off-diagonal
  nonzeros in each row always admits such a labelling into `ν + 1` classes.

Algorithms 3.1–3.6 are not formalized: the theorems hold for *any* labelling with the stated
property, including the ones the algorithms compute.

## Implementation notes

`Matrix.adjGraph A` is the *symmetrized* pattern graph, `SimpleGraph.fromRel (A · · ≠ 0)`, so a
nonzero off-diagonal entry is an edge with no symmetry hypothesis on the pattern at all; the plan
budgeted an `A.IsSymm` hypothesis for the first three results and none of them needs it. Nor does
the level-set result need every index to be reachable from the root, because
`SimpleGraph.abs_dist_sub_dist_le_one_of_adj` does not: unreachable indices have distance zero on
both sides. Only `Matrix.exists_coloring_of_le_maxDegree` needs pattern symmetry, and it needs it
to bound the degree of the *symmetrized* graph by a count of nonzeros in one row.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003. §3.3.3 describes the level-set, independent-set and multicolour orderings; (4.42)
  and Definition 4.11 are the two-colour case, Property A.
-/

open Finset

namespace Matrix

variable {n R : Type*} [Zero R] {A : Matrix n n R}

/-! ### Level-set orderings -/

/-- **Saad §3.3.3, the property that makes level sets separators**: the distances to a root of
the two indices of a nonzero off-diagonal entry differ by at most one. -/
theorem abs_dist_sub_dist_le_one_of_apply_ne_zero {i j : n} (h : A i j ≠ 0) (hij : i ≠ j)
    (v : n) : |(A.adjGraph.dist v i : ℤ) - (A.adjGraph.dist v j : ℤ)| ≤ 1 :=
  SimpleGraph.abs_dist_sub_dist_le_one_of_adj (adjGraph_adj.2 ⟨hij, Or.inl h⟩) v

/-- **A level-set ordering is block tridiagonal** (Saad, *Iterative Methods for Sparse Linear
Systems*, §3.3.3): an entry whose row is two or more levels below its column vanishes.

Stated for the labelling `i ↦ dist v i` rather than for a permutation: for any `σ` along which
that labelling is monotone, this says that `A.submatrix σ σ` is block tridiagonal with the level
sets `SimpleGraph.sphere (adjGraph A) v k` as its blocks, which is what a breadth-first or
Cuthill–McKee reordering produces.

The hypothesis is `dist v i + 2 ≤ dist v j`, not `dist v i < dist v j`: adjacent levels do carry
entries, and only a gap of two or more forces a zero. -/
theorem apply_eq_zero_of_dist_lt {i j : n} (v : n)
    (h : A.adjGraph.dist v i + 2 ≤ A.adjGraph.dist v j) : A i j = 0 := by
  by_contra h0
  have hij : i ≠ j := by rintro rfl; omega
  have := abs_dist_sub_dist_le_one_of_apply_ne_zero h0 hij v
  rw [abs_le] at this
  omega

/-- The mirror image of `Matrix.apply_eq_zero_of_dist_lt`: an entry whose column is two or
more levels below its row vanishes. -/
theorem apply_eq_zero_of_dist_lt' {i j : n} (v : n)
    (h : A.adjGraph.dist v j + 2 ≤ A.adjGraph.dist v i) : A i j = 0 := by
  by_contra h0
  have hij : i ≠ j := by rintro rfl; omega
  have := abs_dist_sub_dist_le_one_of_apply_ne_zero h0 hij v
  rw [abs_le] at this
  omega

/-! ### Multicolour and independent-set orderings -/

/-- **A multicolour ordering has diagonal diagonal blocks** (Saad, *Iterative Methods for Sparse
Linear Systems*, §3.3.3): two distinct indices of the same colour of a proper colouring of the
pattern graph carry no entry.

With two colours this is Saad's Property A (Definition 4.11) and his (4.42). -/
theorem apply_eq_zero_of_coloring_eq {α : Type*} (c : A.adjGraph.Coloring α) {i j : n}
    (hij : i ≠ j) (h : c i = c j) : A i j = 0 := by
  by_contra h0
  exact c.valid (adjGraph_adj.2 ⟨hij, Or.inl h0⟩) h

/-- **An independent set is a diagonal block** (Saad, *Iterative Methods for Sparse Linear
Systems*, §3.3.3): the entries between two distinct indices of an independent set of the pattern
graph vanish, which is the diagonal leading block of Saad's block form (3.3). -/
theorem apply_eq_zero_of_isIndepSet {s : Set n} (hs : A.adjGraph.IsIndepSet s) {i j : n}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) : A i j = 0 := by
  by_contra h0
  exact (SimpleGraph.isIndepSet_iff _).1 hs hi hj hij (adjGraph_adj.2 ⟨hij, Or.inl h0⟩)

/-- **A multicolour ordering with `ν + 1` blocks always exists** (Saad, *Iterative Methods for
Sparse Linear Systems*, §3.3.3 and Problem P-3.10): a matrix with a symmetric pattern and at most
`ν` off-diagonal nonzeros in each row admits a labelling of its indices by `Fin (ν + 1)` in which
two distinct indices of the same label carry no entry.

The greedy colouring bound `SimpleGraph.colorable_maxDegree_add_one` applied to the pattern graph,
whose degree at `i` is the number of off-diagonal nonzeros of row `i` once the pattern is
symmetric. -/
theorem exists_coloring_of_le_maxDegree [Fintype n] [DecidableEq n] [DecidableEq R] {ν : ℕ}
    (hsymm : ∀ i j, A i j ≠ 0 → A j i ≠ 0)
    (hrow : ∀ i, #{j ∈ univ | j ≠ i ∧ A i j ≠ 0} ≤ ν) :
    ∃ c : n → Fin (ν + 1), ∀ i j, i ≠ j → c i = c j → A i j = 0 := by
  let _ : DecidableRel A.adjGraph.Adj := fun _ _ => decidable_of_iff _ adjGraph_adj.symm
  have hdeg : ∀ i, A.adjGraph.degree i ≤ ν := by
    intro i
    refine le_trans (Finset.card_le_card ?_) (hrow i)
    intro j hj
    rw [SimpleGraph.mem_neighborFinset, adjGraph_adj] at hj
    refine Finset.mem_filter.2 ⟨Finset.mem_univ j, hj.1.symm, ?_⟩
    exact hj.2.elim id fun h => hsymm _ _ h
  obtain ⟨c⟩ := (A.adjGraph.colorable_maxDegree_add_one).mono
    (Nat.succ_le_succ (SimpleGraph.maxDegree_le_of_forall_degree_le _ _ hdeg))
  exact ⟨c, fun i j hij h => apply_eq_zero_of_coloring_eq c hij h⟩

end Matrix
