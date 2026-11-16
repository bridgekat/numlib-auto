/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Sparse.Pattern

/-!
# Saad, Section 3.2: Graph representations

This module formalizes §3.2 of [saad2003iterative]: the adjacency graph of a sparse matrix
$A \in \mathbb{R}^{n \times n}$, which has an arrow from $i$ to $j$ exactly when $a_{ij} \neq 0$,
and the relation between the patterns of sums, powers and products of matrices and the paths of that
graph. A nonzero entry of $A^k$ gives a path of length $k$, the pattern of $A + B$ is contained in
the union of the patterns of $A$ and $B$, and for entrywise nonnegative matrices with positive
diagonal the pattern of $AB$ contains that union. Everything specializes
`Numlib.LinearAlgebra.Sparse.Pattern`.

## Main results

* §3.2.1, `SaadSparse.Chapter03.adjDigraph_eq`: the arrows of the adjacency graph are the nonzero
  entries, and for a symmetric pattern the symmetrized graph loses nothing off the diagonal.
* §3.2.1 and Problem P-3.4, `SaadSparse.Chapter03.pattern_pow`: a nonzero entry $(A^k)_{ij}$ gives a
  path of length $k$ from $i$ to $j$.
* Problem P-3.2, `SaadSparse.Chapter03.pattern_add` and
  `SaadSparse.Chapter03.pattern_add_of_nonneg`: the pattern of $A + B$ is contained in the union of
  the patterns, with equality for entrywise nonnegative matrices.
* Problem P-3.5, `SaadSparse.Chapter03.problem_3_5`: for entrywise nonnegative matrices with
  positive diagonal, the pattern of $AB$ contains the union of the patterns of $A$ and $B$.

## Implementation notes

* The adjacency graph of the source is directed and has a self-loop at every nonzero diagonal entry,
  as Problems P-3.4 and P-3.10 say. Its Lean form is `Matrix.adjDigraph`, a `Digraph`. The
  symmetrized loopless `SimpleGraph` on which the reorderings of §3.3.3 act is `Matrix.adjGraph`,
  and `Matrix.adjQuiver` is the same relation as the arrow relation of a quiver, which is the form
  that the path API of Mathlib uses.

## Deviations from the source

* **§3.2.1 and Problems P-3.2, P-3.4 and P-3.5, the patterns of sums, powers and products**
  (reading). The source assumes without saying so that no numerical cancellation occurs. The library
  proves the containments without a hypothesis, and the equalities for entrywise nonnegative
  matrices, where no cancellation can happen. See `SaadSparse.Chapter03.pattern_add_of_nonneg` and
  `SaadSparse.Chapter03.problem_3_5`.

## Not formalized

* **§3.2.2, the graphs of matrices that arise from partial differential equations.** The section
  states nothing there: the claim that the adjacency graph is "often" the mesh graph is hedged and
  set as Problem P-3.1, and the storage saving of quotient graphs is a counting remark.
-/

open Matrix

namespace SaadSparse.Chapter03

variable {n : ℕ}

/-! ### §3.2.1 The adjacency graph of a matrix -/

/-- **Section 3.2.1** of [saad2003iterative], the adjacency graph of a matrix. Let
$A \in \mathbb{R}^{n \times n}$. Then the following hold.

* The adjacency graph of $A$ has an arrow from $i$ to $j$ exactly when $a_{ij} \neq 0$. So it is
  directed, and it has a self-loop at every nonzero diagonal entry.
* If the pattern of $A$ is symmetric, that is $a_{ij} \neq 0 \iff a_{ji} \neq 0$ for all $i, j$,
  then $i$ and $j$ are adjacent in the symmetrized graph exactly when $i \neq j$ and there is an
  arrow from $i$ to $j$.

The symmetry hypothesis is what the source means by a "symmetric nonzero pattern". The directed
graph is `Matrix.adjDigraph`, and the symmetrized loopless graph is `Matrix.adjGraph`. -/
theorem adjDigraph_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ i j, A.adjDigraph.Adj i j ↔ A i j ≠ 0) ∧
      ((∀ i j, A i j ≠ 0 ↔ A j i ≠ 0) →
        ∀ i j, A.adjGraph.Adj i j ↔ i ≠ j ∧ A.adjDigraph.Adj i j) :=
  ⟨fun _ _ => Iff.rfl,
    fun h _ _ => adjGraph_adj_iff_of_forall_ne_zero fun i j hij => (h i j).1 hij⟩

/-! ### §3.2.1 and Problems P-3.2, P-3.4, P-3.5: patterns of sums, powers and products -/

/-- **Section 3.2.1** and **Problem P-3.4** of [saad2003iterative]. Let
$A \in \mathbb{R}^{n \times n}$ and $k \in \mathbb{N}$. If $(A^k)_{ij} \neq 0$, then there is a
path of length $k$ from $i$ to $j$ in the adjacency graph of $A$.

This direction needs no hypothesis. The converse is false because of cancellation. It is true
for entrywise nonnegative matrices, where it is Mathlib's
`Matrix.pow_apply_pos_iff_nonempty_path`. The path is a `Quiver.Path` in the quiver
`Matrix.adjQuiver A`. -/
theorem pattern_pow (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) {i j : Fin n} (h : (A ^ k) i j ≠ 0) :
    letI := A.adjQuiver
    ∃ p : Quiver.Path i j, p.length = k :=
  A.exists_path_length_of_pow_apply_ne_zero k h

/-- **Problem P-3.2** of [saad2003iterative], the containment. Let
$A, B \in \mathbb{R}^{n \times n}$. If $(A + B)_{ij} \neq 0$, then $a_{ij} \neq 0$ or
$b_{ij} \neq 0$. So the pattern of $A + B$ is contained in the union of the patterns of $A$ and
of $B$. -/
theorem pattern_add {A B : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : (A + B) i j ≠ 0) :
    A i j ≠ 0 ∨ B i j ≠ 0 :=
  not_and_or.1 fun hz => h (by simp [Matrix.add_apply, hz.1, hz.2])

/-- **Problem P-3.2** of [saad2003iterative], the equality. Let $A, B \in \mathbb{R}^{n \times n}$
be entrywise nonnegative. Then for all $i, j$
$$(A + B)_{ij} > 0 \iff a_{ij} > 0 \text{ or } b_{ij} > 0.$$
So the pattern of $A + B$ is the union of the patterns of $A$ and of $B$.

**Reading.** The source assumes that no cancellation occurs. Entrywise nonnegativity makes this
precise, because then no cancellation can occur. -/
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

/-- **Problem P-3.5** of [saad2003iterative]. Let $A, B \in \mathbb{R}^{n \times n}$ be entrywise
nonnegative, with $a_{ii} > 0$ and $b_{ii} > 0$ for every $i$. If $a_{ij} > 0$ or $b_{ij} > 0$,
then $(AB)_{ij} > 0$. So the pattern of $AB$ contains the union of the patterns of $A$ and of
$B$.

**Reading.** The source asks for nonzero diagonal entries, under its convention that no
cancellation occurs. Here the matrices are entrywise nonnegative, and this cannot be dropped:
the diagonal hypothesis alone leaves $a_{ij} b_{jj}$ free to cancel against the other terms of
the sum.

A nonzero $a_{ij}$ pairs with $b_{jj}$, and $a_{ii}$ pairs with a nonzero $b_{ij}$. The
practical point of the source, that it is better to store $A$ and $B$ than their product, is a
remark. -/
theorem problem_3_5 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j) (hAd : ∀ i, 0 < A i i) (hBd : ∀ i, 0 < B i i) {i j : Fin n}
    (h : 0 < A i j ∨ 0 < B i j) : 0 < (A * B) i j := by
  rcases h with h | h
  · exact mul_apply_pos_of_pos_of_pos hA hB h (hBd j)
  · exact mul_apply_pos_of_pos_of_pos hA hB (hAd i) h

end SaadSparse.Chapter03
