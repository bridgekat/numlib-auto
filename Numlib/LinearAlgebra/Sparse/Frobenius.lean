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

Every square matrix is block upper triangular once its indices are sorted the right way, and the
diagonal blocks are then the *strongly connected components* of its adjacency digraph. This is the
**Frobenius normal form** of [saad2003iterative] §3.3.4.

The book prints only the shape of the reduced matrix and says that "each partition corresponds to a
connected component". Two things have to be added to make that a theorem. The components meant are
the *strongly* connected ones, since the adjacency graph of a general matrix is directed; and the
components have to be listed in an order in which every arrow points forward, without which no
permutation triangulates the matrix. That order is `Relation.exists_rank_stronglyConnected`.

## Main results

* `Matrix.exists_blockTriangular_stronglyConnected`: a block index `b` making `A` block upper
  triangular whose fibres are exactly the strongly connected components. No ordering of the index
  type is used, and the blocks need not be contiguous.
* `Matrix.exists_perm_submatrix_blockTriangular`: the book's form, for indices `Fin N`. A symmetric
  permutation `A ↦ A.submatrix σ σ` — that is, `P A Pᵀ`, by
  `Matrix.submatrix_eq_permMatrix_mul_mul_transpose` — makes the block index monotone, so the blocks
  are contiguous and the matrix is block upper triangular in the literal sense.
* `Matrix.stronglyConnected_of_isPatternIrreducible`: an irreducible matrix has a single component,
  so its Frobenius normal form is the matrix itself. This is the consistency check between the
  components here and the irreducibility of `Numlib/LinearAlgebra/Sparse/Pattern`.
-/

open Quiver

namespace Matrix

variable {n R : Type*}

section Zero

variable [Zero R]

/-- **The Frobenius normal form**, in the form that needs no ordering of the index type: a square
matrix has a block index `b` making it block upper triangular, whose fibres are exactly the strongly
connected components of its adjacency digraph.

`Matrix.BlockTriangular A b` says that `A i j = 0` whenever `b j < b i`, so the content is that the
rank `b` never decreases along an arrow `i ⟶ j`, that is, along a nonzero entry `A i j`. -/
theorem exists_blockTriangular_stronglyConnected [Finite n] (A : Matrix n n R) :
    ∃ b : n → ℕ, A.BlockTriangular b ∧
      ∀ i j, b i = b j ↔ Relation.StronglyConnected A.adjDigraph.Adj i j := by
  obtain ⟨b, hmono, hfib⟩ := Relation.exists_rank_stronglyConnected A.adjDigraph.Adj
  refine ⟨b, fun i j hij => ?_, hfib⟩
  by_contra h
  exact absurd (hmono i j h) (not_le.2 hij)

/-- **The Frobenius normal form** in the book's shape: a symmetric permutation makes a square matrix
block upper triangular with *contiguous* diagonal blocks, and the blocks are the strongly connected
components of the adjacency digraph, listed in an order in which every arrow points forward.

The permutation is the one that sorts the block index of
`Matrix.exists_blockTriangular_stronglyConnected`; the monotonicity of `b` is what makes each block
an interval of indices. -/
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

/-- A path in the adjacency quiver is a chain of nonzero entries, hence reachability in the
adjacency digraph. -/
theorem reflTransGen_adjDigraph_of_path {i j : n} (p : @Quiver.Path n A.adjQuiver i j) :
    Relation.ReflTransGen A.adjDigraph.Adj i j := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons _ e ih => exact ih.tail (apply_ne_zero_of_adjHom e)

/-- A pattern-irreducible matrix is a single strongly connected component, so the Frobenius normal
form of an irreducible matrix has one block: the matrix itself. -/
theorem stronglyConnected_of_isPatternIrreducible (hA : A.IsPatternIrreducible) (i j : n) :
    Relation.StronglyConnected A.adjDigraph.Adj i j :=
  ⟨reflTransGen_adjDigraph_of_path (hA.exists_pos_length_path i j).choose,
    reflTransGen_adjDigraph_of_path (hA.exists_pos_length_path j i).choose⟩

end Normed

end Matrix
