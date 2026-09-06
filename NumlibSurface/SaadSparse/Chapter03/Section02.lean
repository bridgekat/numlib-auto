import Numlib.LinearAlgebra.Sparse.Pattern

/-!
# §3.2 Graph representations

Section 3.2 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the adjacency graph of a sparse matrix, and the relation between the pattern of a
product and the paths of that graph.

Everything here specializes `Numlib/LinearAlgebra/Sparse/Pattern`, where the two modelling
decisions the book forces are made. Saad's adjacency graph is *directed* and carries a self-loop at
every nonzero diagonal entry — he says so in Problems P-3.4 and P-3.10 — so its carrier is
`Matrix.adjDigraph`, a `Digraph`; `Matrix.adjGraph` is the symmetrized loopless `SimpleGraph` that
the reorderings of §3.3.3 act on, and `Matrix.adjQuiver` is the same relation once more in the
shape Mathlib's path API consumes. And every claim of the section about the pattern of a sum or a
product silently assumes that no numerical cancellation occurs; the containment holds
unconditionally, and the equality is stated here for entrywise nonnegative matrices, where
cancellation cannot happen.

§3.2.2, the graphs of matrices arising from partial differential equations, states nothing: that
the adjacency graph is "often" the mesh graph is hedged and set as Problem P-3.1, and the
quotient-graph storage saving is a counting remark.
-/

open Matrix

namespace SaadSparse.Ch03

variable {n : ℕ}

/-! ### §3.2.1 The adjacency graph of a matrix -/

/-- Saad §3.2.1, the definition read at matrix level: the adjacency graph of `A` has an arrow from
`i` to `j` exactly when `A i j ≠ 0`, so it is directed and has a self-loop at every nonzero
diagonal entry. When the pattern is symmetric — `A i j ≠ 0 ↔ A j i ≠ 0`, which the book's
"symmetric nonzero pattern" means — the symmetrized graph loses nothing off the diagonal: `i` and
`j` are adjacent in it exactly when they are distinct and joined by an arrow. -/
theorem adjDigraph_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ i j, A.adjDigraph.Adj i j ↔ A i j ≠ 0) ∧
      ((∀ i j, A i j ≠ 0 ↔ A j i ≠ 0) →
        ∀ i j, A.adjGraph.Adj i j ↔ i ≠ j ∧ A.adjDigraph.Adj i j) :=
  ⟨fun _ _ => Iff.rfl,
    fun h _ _ => adjGraph_adj_iff_of_forall_ne_zero fun i j hij => (h i j).1 hij⟩

/-! ### §3.2.1 and Problems P-3.2, P-3.4, P-3.5: patterns of sums, powers and products -/

/-- Saad §3.2.1 and Problem P-3.4: an edge of the graph of `A ^ k` carries a path of length `k` in
the graph of `A`. This direction needs no hypothesis. The converse is false by cancellation and
true for entrywise nonnegative matrices, where it is Mathlib's
`Matrix.pow_apply_pos_iff_nonempty_path`. -/
theorem pattern_pow (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) {i j : Fin n} (h : (A ^ k) i j ≠ 0) :
    letI := A.adjQuiver
    ∃ p : Quiver.Path i j, p.length = k :=
  A.exists_path_length_of_pow_apply_ne_zero k h

/-- Saad Problem P-3.2, the containment half: the pattern of `A + B` is contained in the union of
the patterns of `A` and of `B`. -/
theorem pattern_add {A B : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : (A + B) i j ≠ 0) :
    A i j ≠ 0 ∨ B i j ≠ 0 :=
  not_and_or.1 fun hz => h (by simp [Matrix.add_apply, hz.1, hz.2])

/-- Saad Problem P-3.2, the equality half: for entrywise nonnegative matrices no cancellation can
occur, so the pattern of `A + B` *is* the union of the patterns of `A` and of `B`. -/
theorem pattern_add_of_nonneg {A B : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j) (i j : Fin n) :
    0 < (A + B) i j ↔ 0 < A i j ∨ 0 < B i j := by
  rw [Matrix.add_apply]
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    rw [le_antisymm hc.1 (hA i j), le_antisymm hc.2 (hB i j), add_zero] at h
    exact lt_irrefl 0 h
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg h (hB i j)
    · exact add_pos_of_nonneg_of_pos (hA i j) h

/-- Saad Problem P-3.5: if `A` and `B` are entrywise nonnegative with all diagonal entries nonzero,
then the pattern of `A * B` contains the union of the patterns of `A` and of `B` — a nonzero
`A i j` pairs with `B j j`, and `A i i` with `B i j`. The nonnegativity is the book's
no-cancellation convention made precise, and it cannot be dropped: the diagonal hypothesis alone
leaves `A i j * B j j` free to cancel against the other terms of the sum. The book's practical
point, that it is better to store `A` and `B` than their product, is a remark. -/
theorem problem_3_5 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j) (hAd : ∀ i, 0 < A i i) (hBd : ∀ i, 0 < B i i) {i j : Fin n}
    (h : 0 < A i j ∨ 0 < B i j) : 0 < (A * B) i j := by
  rcases h with h | h
  · exact mul_apply_pos_of_pos_of_pos hA hB h (hBd j)
  · exact mul_apply_pos_of_pos_of_pos hA hB (hAd i) h

end SaadSparse.Ch03
