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
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Block
import Numlib.Combinatorics.Relation.StronglyConnected
import Numlib.LinearAlgebra.Sparse.Pattern

/-!
# The Frobenius normal form

Let $A$ be a square matrix, and consider its adjacency digraph, with an arrow $i \to j$ whenever
$a_{ij} \neq 0$. Two indices are strongly connected if each is reachable from the other. After a
suitable symmetric permutation of its indices, $A$ is block upper triangular, and its diagonal
blocks are the *strongly connected components* of the adjacency digraph. This is the **Frobenius
normal form** of [saad2003iterative], §3.3.4.

The source prints only the shape of the reduced matrix, and says that "each partition corresponds to
a connected component". Two additions make this a theorem. The components are the *strongly*
connected ones, since the adjacency digraph of a general matrix is directed. And the components must
be listed in an order in which every arrow points forward; without this order no permutation makes
the matrix block triangular. That order comes from `Relation.exists_rank_stronglyConnected`.

## Main results

* `Matrix.exists_blockTriangular_stronglyConnected`: there is a block index $b$ for which $A$ is
  block upper triangular and whose fibres are exactly the strongly connected components.
* `Matrix.exists_perm_submatrix_blockTriangular`: the form of the source for indices in
  $\{0, \dots, N - 1\}$. After a symmetric permutation the block index is monotone, so the blocks
  are contiguous.
* `Matrix.stronglyConnected_of_isPatternIrreducible`: an irreducible matrix has a single strongly
  connected component, so its Frobenius normal form is the matrix itself.

## Implementation notes

* The first form uses no ordering of the index type, and its blocks need not be contiguous. The
  second form applies the permutation as `A.submatrix σ σ`, which is $P A P^T$ by
  `Matrix.submatrix_eq_permMatrix_mul_mul_transpose`.
* `Matrix.stronglyConnected_of_isPatternIrreducible` checks that the strongly connected components
  here agree with the irreducibility `Matrix.IsPatternIrreducible` of
  `Numlib.LinearAlgebra.Sparse.Pattern`.
-/

open Quiver

namespace Matrix

variable {n R : Type*}

section Zero

variable [Zero R]

/-- The **Frobenius normal form**, in the form that needs no ordering of the index type. Let $A$ be
a square matrix over a type with zero, with a finite index set. Then there is a function $b$
from the indices to $\mathbb{N}$ such that

* $A$ is block upper triangular for $b$: $a_{ij} = 0$ whenever $b(j) < b(i)$;
* $b(i) = b(j)$ if and only if $i$ and $j$ are strongly connected in the adjacency digraph of
  $A$.

Block triangularity is `Matrix.BlockTriangular A b`. Its content is that $b$ does not decrease
along an arrow $i \to j$, that is, along a nonzero entry $a_{ij}$. -/
theorem exists_blockTriangular_stronglyConnected [Finite n] (A : Matrix n n R) :
    ∃ b : n → ℕ, A.BlockTriangular b ∧
      ∀ i j, b i = b j ↔ Relation.StronglyConnected A.adjDigraph.Adj i j := by
  obtain ⟨b, hmono, hfib⟩ := Relation.exists_rank_stronglyConnected A.adjDigraph.Adj
  refine ⟨b, fun i j hij => ?_, hfib⟩
  by_contra h
  exact absurd (hmono i j h) (not_le.2 hij)

/-- The **Frobenius normal form** in the shape of [saad2003iterative], §3.3.4. Let $A$ be an
$N \times N$ matrix over a type with zero. Then there are a permutation $\sigma$ of
$\{0, \dots, N - 1\}$ and a monotone function $b$ from $\{0, \dots, N - 1\}$ to $\mathbb{N}$
such that the permuted matrix $(a_{\sigma(i) \sigma(j)})_{i,j}$ is block upper triangular for
$b$, and $b(i) = b(j)$ if and only if $\sigma(i)$ and $\sigma(j)$ are strongly connected in the
adjacency digraph of $A$.

Since $b$ is monotone, each diagonal block is an interval of indices. The blocks are the
strongly connected components, listed in an order in which every arrow points forward. The
permutation sorts the block index of `Matrix.exists_blockTriangular_stronglyConnected`. -/
theorem exists_perm_submatrix_blockTriangular {N : ℕ} (A : Matrix (Fin N) (Fin N) R) :
    ∃ (σ : Equiv.Perm (Fin N)) (b : Fin N → ℕ), Monotone b ∧
      (A.submatrix σ σ).BlockTriangular b ∧
      ∀ i j, b i = b j ↔ Relation.StronglyConnected A.adjDigraph.Adj (σ i) (σ j) := by
  obtain ⟨c, htri, hfib⟩ := exists_blockTriangular_stronglyConnected A
  exact ⟨Tuple.sort c, c ∘ Tuple.sort c, Tuple.monotone_sort c, fun _ _ hij => htri hij,
    fun i j => hfib _ _⟩

end Zero

section Normed

variable [NormedAddCommGroup R] {A : Matrix n n R}

/-- Let $A$ be a square matrix over a normed additive group. A path from $i$ to $j$ in the adjacency
quiver `Matrix.adjQuiver A` is a chain of nonzero entries, so $j$ is reachable from $i$ in the
adjacency digraph of $A$. -/
theorem reflTransGen_adjDigraph_of_path {i j : n} (p : @Quiver.Path n A.adjQuiver i j) :
    Relation.ReflTransGen A.adjDigraph.Adj i j := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons _ e ih => exact ih.tail (apply_ne_zero_of_adjHom e)

/-- Let $A$ be a square matrix over a normed additive group. If $A$ is pattern-irreducible, then any
two indices are strongly connected in its adjacency digraph. Thus the Frobenius normal form of
an irreducible matrix has one block, the matrix itself. -/
theorem stronglyConnected_of_isPatternIrreducible (hA : A.IsPatternIrreducible) (i j : n) :
    Relation.StronglyConnected A.adjDigraph.Adj i j :=
  ⟨reflTransGen_adjDigraph_of_path (hA.exists_pos_length_path i j).choose,
    reflTransGen_adjDigraph_of_path (hA.exists_pos_length_path j i).choose⟩

end Normed

end Matrix
