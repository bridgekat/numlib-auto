/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Combinatorics.SimpleGraph.IndepSet
import Numlib.LinearAlgebra.Sparse.Frobenius
import Numlib.LinearAlgebra.Sparse.Reordering

/-!
# Saad, Section 3.3: Permutations and reorderings

This module formalizes §3.3 of [saad2003iterative]: permutation matrices (Definition 3.1 and
Proposition 3.2, §3.3.1), the effect of a symmetric permutation $A \mapsto P A P^T$ on the adjacency
graph (§3.3.2, with Example 3.3), the three common reorderings by level sets, independent sets and
multicolouring (§3.3.3), and irreducibility with the Frobenius normal form (§3.3.4). A symmetric
permutation only relabels the adjacency graph. A level-set ordering makes the reordered matrix block
tridiagonal, an independent set gives a diagonal leading block, and a proper colouring gives
diagonal blocks on the diagonal. A matrix is irreducible exactly when its adjacency graph is
strongly connected, and every matrix is symmetrically permuted to block upper triangular form whose
diagonal blocks are the strongly connected components.

The proofs specialize `Numlib.LinearAlgebra.Sparse.Pattern`,
`Numlib.LinearAlgebra.Sparse.Reordering`, `Numlib.LinearAlgebra.Sparse.Frobenius`,
`Numlib.Combinatorics.SimpleGraph.LevelSet`, `Numlib.Combinatorics.SimpleGraph.IndepSet` and
`Numlib.Combinatorics.SimpleGraph.Coloring`. The content of §3.3.1 is in Mathlib.

## Main results

* Definition 3.1 and Proposition 3.2, `SaadSparse.Chapter03.proposition_3_2`: the row and column
  permutations of $A$ are $P_\pi A$ and $A P_\pi^T$, permutation matrices are orthogonal, and
  $P_\pi A P_\pi^T$ is a similarity transformation of $A$.
* §3.3.2, `SaadSparse.Chapter03.adjGraph_submatrix`: a symmetric permutation relabels the adjacency
  graph and preserves colourability, connectivity and irreducibility.
* Example 3.3, `SaadSparse.Chapter03.example_3_3`: the $9 \times 9$ arrow matrix has the star as its
  adjacency graph, one elimination step on it fills the whole trailing block, and after the
  reversing permutation it has an $LU$ factorization without fill-in.
* §3.3.3, level sets, `SaadSparse.Chapter03.levelSet_blockTridiagonal`: the distances to a root of
  the two indices of a nonzero off-diagonal entry differ by at most one, so a level-set ordering
  gives a block tridiagonal matrix, and each level set is a separator.
* §3.3.3, independent sets, `SaadSparse.Chapter03.indepSet_card_ge`: a maximal independent set $S$
  satisfies $|S| \ge n / (1 + \Delta)$, with $\Delta$ the maximum degree.
* Equation (3.3), `SaadSparse.Chapter03.equation_3_3`: the entries of $A$ between two distinct
  indices of an independent set vanish, so the block of these indices in the reordered matrix is
  diagonal.
* §3.3.3, multicolouring, `SaadSparse.Chapter03.multicoloring_blocks`: the entries of $A$ between
  two distinct indices of the same colour vanish, so the diagonal blocks of a multicolour ordering
  are diagonal.
* §3.3.3 and Problem P-3.10, `SaadSparse.Chapter03.exists_multicoloring`: a matrix with a symmetric
  pattern and at most $\nu$ off-diagonal nonzeros in each row has a multicolour ordering with
  $\nu + 1$ colours.
* Algorithm 3.6 and Problems P-3.9 to P-3.11, `SaadSparse.Chapter03.greedy_coloring_bounds`: the
  greedy colouring uses at most $\nu + 1$ colours, and two colours on a bipartite graph under a
  traversal in which every index after the first of its component has an earlier neighbour.
* §3.3.4, `SaadSparse.Chapter03.isPatternIrreducible_iff`: for $n \ge 2$, a matrix is reducible
  exactly when a symmetric permutation puts it in block upper triangular form.
* §3.3.4, `SaadSparse.Chapter03.frobenius_normal_form`: a symmetric permutation puts every square
  matrix in block upper triangular form whose diagonal blocks are the strongly connected components
  of its adjacency graph.

## Implementation notes

* The row permutation $A_{\pi,\ast}$ of the source is `A.submatrix π id`.
  The column permutation $A_{\ast,\pi}$ is `A.submatrix id π`.
  The permutation matrix $P_\pi$ is `Equiv.Perm.permMatrix`. Proposition 3.2 is
  `PEquiv.toMatrix_toPEquiv_mul` and `PEquiv.mul_toMatrix_toPEquiv`, and the anti-homomorphism
  convention of (3.1) is `Matrix.permMatrix_mul`. The identity
  $A_{\sigma,\sigma} = P_\sigma A P_\sigma^T$, which every later chapter uses, is
  `Matrix.submatrix_eq_permMatrix_mul_mul_transpose`.
* The reorderings of §3.3.3 are Algorithms 3.1 to 3.6. Their properties concern the labelling that
  they produce, not the traversal, so no traversal is formalized: the level-set statement is about
  the graph distance `SimpleGraph.dist`, the multicolour statement about a proper colouring, and the
  independent-set statement about a maximal independent set. The exception is the greedy colouring
  of Algorithm 3.6, about which the source makes claims; these are
  `SaadSparse.Chapter03.greedy_coloring_bounds`.
* The graph of the reorderings is `Matrix.adjGraph`, the symmetrized loopless graph: distinct
  indices $i, j$ are adjacent when $a_{ij} \neq 0$ or $a_{ji} \neq 0$. So a nonzero off-diagonal
  entry is always an edge, and the statements on level sets, independent sets and multicolour blocks
  hold for an arbitrary pattern. A symmetric pattern is needed only where the degree of this graph
  must be bounded by the count of nonzeros in one row, in
  `SaadSparse.Chapter03.exists_multicoloring` and `SaadSparse.Chapter03.greedy_coloring_bounds`.
* The source warns that a nonsymmetric permutation does not preserve the adjacency graph, and gives
  no statement. The warning is recorded here and not proved. For $A = \begin{bmatrix} 0 & 1 \\ 1 & 0
  \end{bmatrix}$ the graph of $A$ has the edge between the two indices, while the column permutation
  of $A$ by the transposition is the identity matrix, whose graph has no edge. So a one-sided
  permutation can destroy connectivity, and `SaadSparse.Chapter03.adjGraph_submatrix` needs the
  permutation on both sides.
* Indices are $0$-based: index $i$ of the source is `i - 1` here.

## Deviations from the source

* **Example 3.3, the arrow matrix** (reading). Figure 3.4 prints a pattern and no values, so the
  pattern is the hypothesis and every clause holds for every matrix with it. The fill claims are
  stated for one elimination step and for an exhibited $LU$ factorization. See
  `SaadSparse.Chapter03.example_3_3`.
* **§3.3.3, level-set orderings** (generalization). The source leaves the connectedness of the graph
  implicit. The statements hold without it. See `SaadSparse.Chapter03.levelSet_blockTridiagonal`.
* **§3.3.3, the size of an independent set** (generalization). The source states the bound for the
  set that Algorithm 3.4 produces. It holds for every maximal independent set. See
  `SaadSparse.Chapter03.indepSet_card_ge`.
* **Algorithm 3.6 and Problem P-3.11** (reading). The traversal of the greedy colouring is the order
  of the index set, so it is the identity ordering of a matrix that is already reordered. See
  `SaadSparse.Chapter03.greedy_coloring_bounds`.
* **§3.3.4, irreducibility** (reading). The "connected" adjacency graph of the source is read as
  strongly connected, with directed paths of positive length, and the equivalence with the block
  form needs $n \ge 2$. See `SaadSparse.Chapter03.isPatternIrreducible_iff`.
* **§3.3.4, the Frobenius normal form** (reading). The source says that each block "corresponds to a
  connected component". The blocks are the strongly connected components, listed in an order in
  which every arrow points forward. See `SaadSparse.Chapter03.frobenius_normal_form`.

## Not formalized

* **Examples 3.4, 3.5 and 3.6.** Each is a run on the finite element mesh of Figure 2.10, which the
  source text does not reproduce. Example 3.4 also compares orderings by bandwidth and profile,
  which this edition does not define. The optimality claim of Example 3.5 is hedged by the source as
  a "may well be". The four-colour count of Example 3.6 is an instance of
  `SaadSparse.Chapter03.greedy_coloring_bounds` and `SaadSparse.Chapter03.exists_multicoloring`.
* **The reverse Cuthill–McKee ordering.** The source gives it as an observation with a picture and
  no statement, and this edition proves no bandwidth or profile bound to compare against.
* **Problem P-3.12**, that the structural inverse of an irreducible matrix is dense. It needs a
  notion of the structural inverse, which the chapter does not define.
-/

open Finset Matrix

namespace SaadSparse.Chapter03

variable {n : ℕ}

/-! ### §3.3.1 Permutation matrices: Definition 3.1 and Proposition 3.2 -/

/-- **Definition 3.1** and **Proposition 3.2** of [saad2003iterative], with the symmetric
permutation of §3.3.1. Let $A \in \mathbb{R}^{n \times n}$, let $\pi$ be a permutation of
$\{1, \dots, n\}$, and let $P_\pi$ be its permutation matrix. Then the row $\pi$-permutation
$A_{\pi,\ast}$, with rows $a_{\pi(i),\ast}$, and the column $\pi$-permutation $A_{\ast,\pi}$, with
columns $a_{\ast,\pi(j)}$, satisfy
$$A_{\pi,\ast} = P_\pi A, \qquad A_{\ast,\pi} = A P_\pi^T, \qquad P_\pi^T P_\pi = I, \qquad
  P_\pi^{-1} = P_\pi^T,$$
and the symmetric permutation satisfies $A_{\pi,\pi} = P_\pi A P_\pi^T$, so it is a similarity
transformation of $A$.

The row permutation $A_{\pi,\ast}$ is `A.submatrix π id`.
The column permutation $A_{\ast,\pi}$ is `A.submatrix id π`.
The symmetric permutation $A_{\pi,\pi}$ is `A.submatrix π π`.
The permutation matrix $P_\pi$ is `Equiv.Perm.permMatrix`. The clauses are Mathlib's
`PEquiv.toMatrix_toPEquiv_mul`, `PEquiv.mul_toMatrix_toPEquiv`, `Matrix.transpose_permMatrix`
and `Matrix.permMatrix_mul`. Problem P-3.3, $P_\pi = I_{\pi,\ast}$, is the first clause at
$A = I$. -/
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

/-- **Section 3.3.2** of [saad2003iterative], a symmetric permutation relabels the adjacency graph.
Let $A \in \mathbb{R}^{n \times n}$ and let $\sigma$ be a permutation of the indices. Then for
all $i, j$ there is an arrow from $i$ to $j$ in the adjacency graph of $A_{\sigma,\sigma}$ if
and only if there is an arrow from $\sigma(i)$ to $\sigma(j)$ in that of $A$, and the same holds
for the edges of the symmetrized graphs. Consequently, for every $k$ the symmetrized graph of
$A_{\sigma,\sigma}$ is $k$-colourable if and only if that of $A$ is, it is connected if and only
if that of $A$ is, and $A_{\sigma,\sigma}$ is irreducible if and only if $A$ is.

This is why every reordering of the source is a symmetric permutation $A_{\sigma,\sigma}$, which
is `A.submatrix σ σ`. The directed graph is `Matrix.adjDigraph` and the symmetrized graph is
`Matrix.adjGraph`. Connectivity is `SimpleGraph.Preconnected`. As a graph isomorphism, the
relabelling is `Matrix.adjGraphIso`. -/
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

/-! ### §3.3.2 Example 3.3, the arrow matrix -/

/-- The $L$ factor of the reversed arrow matrix of Figure 3.5: the identity together with the last
row $l_j / d_j$. -/
private noncomputable def arrowL (B : Matrix (Fin 9) (Fin 9) ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.of fun i j => if i = j then 1 else if i = 8 then B 8 j / B j j else 0

/-- The $U$ factor of the reversed arrow matrix of Figure 3.5: the diagonal together with the last
column, whose bottom entry is the Schur complement $s - \sum_k l_k u_k / d_k$. -/
private noncomputable def arrowU (B : Matrix (Fin 9) (Fin 9) ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.of fun i j =>
    if j = 8 then (if i = 8 then B 8 8 - ∑ k ∈ univ.erase 8, B 8 k * B k 8 / B k k else B i 8)
    else if i = j then B i i else 0

/-- **Example 3.3** of [saad2003iterative], the arrow matrix. Let $A \in \mathbb{R}^{9 \times 9}$
have its nonzero entries exactly on the diagonal, in the first row and in the first column, that
is $a_{ij} \neq 0 \iff i = j \text{ or } i = 1 \text{ or } j = 1$. Let $\sigma$ be the reversing
permutation $9, 8, \dots, 1$, and let $B = A_{\sigma,\sigma}$. Then the following hold.

* The adjacency graph of $A$ is the star of Figure 3.4: distinct $i$ and $j$ are adjacent if and
  only if $i = 1$ or $j = 1$.
* The nonzero entries of $B$ lie exactly on the diagonal, in the last row and in the last column
  (Figure 3.5), and distinct $i$ and $j$ are adjacent in the graph of $B$ if and only if $i = 9$
  or $j = 9$.
* One step of Gaussian elimination on $A$ fills the whole trailing block: for all distinct
  $i, j \ge 2$, $$a_{ij} - \frac{a_{i1} a_{1j}}{a_{11}} \neq 0,$$ although $a_{ij} = 0$.
* $B$ has a factorization $B = LU$ without fill-in: $L$ is unit lower triangular, $U$ is upper
  triangular, and $l_{ij} = u_{ij} = 0$ wherever $b_{ij} = 0$.

Because the graph is a star, the source prefers the name "star matrix". The fill-ins of the
third clause are the "disastrous fill-ins" of the source. They need no assumption on the values:
the entry produced is $-a_{i1} a_{1j} / a_{11}$, a quotient of products of nonzero numbers. The
fourth clause is the statement of the source that the $L$ and $U$ parts of the $LU$
factorization of $B$ have the same structure as the lower and upper parts of $B$.

**Reading.** The source prints a pattern and no values. Here the pattern is the hypothesis, and
every clause holds for every matrix with this pattern. The fill claims are stated for one
elimination step and for an exhibited factorization, which is as far as §3.3 can state them. The
characterization of the fill of complete Gaussian elimination is
`SaadSparse.Chapter10.theorem_10_6`, and this example is its smallest instance.

Indices are $0$-based: index $1$ of the source is `0` and index $9$ is `8`. The permutation
$\sigma$ is `Fin.revPerm`, which maps `i` to `8 - i`, and $B$ is
`A.submatrix Fin.revPerm Fin.revPerm`. The factors are exhibited, so no existence theorem for
$LU$ is needed. -/
theorem example_3_3 (A : Matrix (Fin 9) (Fin 9) ℝ)
    (hA : ∀ i j, A i j ≠ 0 ↔ i = j ∨ i = 0 ∨ j = 0) :
    (∀ i j, A.adjGraph.Adj i j ↔ i ≠ j ∧ (i = 0 ∨ j = 0)) ∧
      (∀ i j, A.submatrix Fin.revPerm Fin.revPerm i j ≠ 0 ↔ i = j ∨ i = 8 ∨ j = 8) ∧
      (∀ i j, (A.submatrix Fin.revPerm Fin.revPerm).adjGraph.Adj i j ↔ i ≠ j ∧ (i = 8 ∨ j = 8)) ∧
      (∀ i j, i ≠ 0 → j ≠ 0 → i ≠ j → A i j - A i 0 * A 0 j / A 0 0 ≠ 0) ∧
      ∃ L U : Matrix (Fin 9) (Fin 9) ℝ,
        (∀ i, L i i = 1) ∧ (∀ i j, i < j → L i j = 0) ∧ (∀ i j, j < i → U i j = 0) ∧
          L * U = A.submatrix Fin.revPerm Fin.revPerm ∧
          ∀ i j, A.submatrix Fin.revPerm Fin.revPerm i j = 0 → L i j = 0 ∧ U i j = 0 := by
  have hle : ∀ i : Fin 9, i ≤ 8 := by decide
  have hrev : ∀ i : Fin 9, i.rev = 0 ↔ i = 8 := by decide
  -- the star graph of Figure 3.4
  have hgraph : ∀ i j, A.adjGraph.Adj i j ↔ i ≠ j ∧ (i = 0 ∨ j = 0) := by
    intro i j
    rw [Matrix.adjGraph_adj, hA, hA]
    refine and_congr_right fun hij => ⟨fun h => ?_, fun h => Or.inl (Or.inr h)⟩
    rcases h with h | h <;> rcases h with h | h <;>
      first
        | exact absurd h hij
        | exact absurd h.symm hij
        | tauto
  -- the pattern of the reordered matrix, Figure 3.5
  have hB : ∀ i j, A.submatrix Fin.revPerm Fin.revPerm i j ≠ 0 ↔ i = j ∨ i = 8 ∨ j = 8 := by
    intro i j
    rw [Matrix.submatrix_apply, Fin.revPerm_apply, Fin.revPerm_apply, hA, Fin.rev_inj, hrev, hrev]
  -- the reordering only relabels the graph
  have hgraph' : ∀ i j, (A.submatrix Fin.revPerm Fin.revPerm).adjGraph.Adj i j ↔
      i ≠ j ∧ (i = 8 ∨ j = 8) := by
    intro i j
    rw [(adjGraph_submatrix A Fin.revPerm).2.1 i j, hgraph, Fin.revPerm_apply, Fin.revPerm_apply,
      ne_eq, Fin.rev_inj, hrev, hrev]
  -- one step of Gaussian elimination fills the trailing block
  have hfill : ∀ i j : Fin 9, i ≠ 0 → j ≠ 0 → i ≠ j → A i j - A i 0 * A 0 j / A 0 0 ≠ 0 := by
    intro i j hi hj hij
    have h0 : A i j = 0 := by
      by_contra h
      rcases (hA i j).1 h with h | h | h
      exacts [hij h, hi h, hj h]
    rw [h0, zero_sub, neg_ne_zero]
    exact div_ne_zero (mul_ne_zero ((hA i 0).2 (Or.inr (Or.inr rfl)))
      ((hA 0 j).2 (Or.inr (Or.inl rfl)))) ((hA 0 0).2 (Or.inl rfl))
  set B := A.submatrix Fin.revPerm Fin.revPerm with hBdef
  have hdiag : ∀ i, B i i ≠ 0 := fun i => (hB i i).2 (Or.inl rfl)
  refine ⟨hgraph, hB, hgraph', hfill, arrowL B, arrowU B, fun i => by simp [arrowL],
    fun i j hij => ?_, fun i j hij => ?_, ?_, fun i j h => ?_⟩
  -- `L` is unit lower triangular
  · have hi8 : i ≠ 8 := fun h => absurd (hle j) (not_le.2 (h ▸ hij))
    simp [arrowL, hij.ne, hi8]
  -- `U` is upper triangular
  · have hj8 : j ≠ 8 := fun h => absurd (hle i) (not_le.2 (h ▸ hij))
    simp [arrowU, hj8, hij.ne']
  -- the factorization is exact
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hie : i = 8
    · subst hie
      rw [← Finset.sum_erase_add _ _ (mem_univ (8 : Fin 9))]
      by_cases hj8 : j = 8
      · subst hj8
        have hterm : ∀ k ∈ univ.erase (8 : Fin 9),
            arrowL B 8 k * arrowU B k 8 = B 8 k * B k 8 / B k k := by
          intro k hk
          have hk8 : k ≠ 8 := Finset.ne_of_mem_erase hk
          have hLk : arrowL B 8 k = B 8 k / B k k := by simp [arrowL, Ne.symm hk8]
          have hUk : arrowU B k 8 = B k 8 := by simp [arrowU, hk8]
          rw [hLk, hUk]
          ring
        rw [Finset.sum_congr rfl hterm]
        have hL88 : arrowL B 8 8 = 1 := by simp [arrowL]
        have hU88 : arrowU B 8 8 = B 8 8 - ∑ k ∈ univ.erase 8, B 8 k * B k 8 / B k k := by
          simp [arrowU]
        rw [hL88, hU88]
        ring
      · have hterm : ∀ k ∈ univ.erase (8 : Fin 9),
            arrowL B 8 k * arrowU B k j = if k = j then B 8 j else 0 := by
          intro k hk
          have hk8 : k ≠ 8 := Finset.ne_of_mem_erase hk
          have hLk : arrowL B 8 k = B 8 k / B k k := by simp [arrowL, Ne.symm hk8]
          have hUk : arrowU B k j = if k = j then B k k else 0 := by simp [arrowU, hj8]
          rw [hLk, hUk]
          split_ifs with h
          · subst h
            field_simp [hdiag k]
          · ring
        rw [Finset.sum_congr rfl hterm,
          Finset.sum_ite_eq' (univ.erase (8 : Fin 9)) j fun _ => B 8 j]
        have hjmem : j ∈ univ.erase (8 : Fin 9) := Finset.mem_erase.2 ⟨hj8, mem_univ j⟩
        have hU8j : arrowU B 8 j = 0 := by simp [arrowU, hj8, Ne.symm hj8]
        simp [hjmem, hU8j]
    · have hL : ∀ k, arrowL B i k = if i = k then 1 else 0 := by
        intro k
        simp [arrowL, hie]
      simp_rw [hL, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq univ i fun k => arrowU B k j]
      simp only [mem_univ, ite_true]
      by_cases hj8 : j = 8
      · subst hj8
        simp [arrowU, hie]
      · by_cases hij : i = j
        · subst hij
          simp [arrowU, hj8]
        · have hBij : B i j = 0 := by
            by_contra hc
            rcases (hB i j).1 hc with h | h | h
            exacts [hij h, hie h, hj8 h]
          simp [arrowU, hj8, hij, hBij]
  -- no fill-in
  · have h' : ¬ (i = j ∨ i = 8 ∨ j = 8) := fun hc => (hB i j).2 hc h
    have hij : i ≠ j := fun hc => h' (Or.inl hc)
    have hi8 : i ≠ 8 := fun hc => h' (Or.inr (Or.inl hc))
    have hj8 : j ≠ 8 := fun hc => h' (Or.inr (Or.inr hc))
    exact ⟨by simp [arrowL, hij, hi8], by simp [arrowU, hj8, hij]⟩

/-! ### §3.3.3 Common reorderings: level sets -/

/-- **Section 3.3.3** of [saad2003iterative], level-set orderings. Let
$A \in \mathbb{R}^{n \times n}$, let $v$ be a root index, and let $d(i)$ be the distance from
$v$ to $i$ in the symmetrized adjacency graph of $A$, with $d(i) = 0$ when $i$ is not reachable
from $v$. Then the following hold.

* If $a_{ij} \neq 0$ and $i \neq j$, then $|d(i) - d(j)| \le 1$.
* If $d(i) + 2 \le d(j)$ or $d(j) + 2 \le d(i)$, then $a_{ij} = 0$.
* For every $k$, no index $u$ reachable from $v$ with $d(u) < k$ is adjacent to an index $w$
  reachable from $v$ with $d(w) \ge k + 1$. So the level set $\{u : d(u) = k\}$ separates the
  indices before it from the indices after it.

So any ordering in which $d$ is nondecreasing, such as breadth-first search (Algorithm 3.1) and
Cuthill–McKee (Algorithms 3.2 and 3.3), makes $A_{\sigma,\sigma}$ block tridiagonal with the
level sets as its blocks. The separator form of the last clause is the one that §3.6.2 uses for
nested dissection.

**Generalization.** The source leaves the connectedness of the graph implicit, because the
traversal does not reach every index without it. The statements do not need it, since an index
unreachable from $v$ has distance zero on both sides of each comparison.

The distance is `SimpleGraph.dist` in `Matrix.adjGraph`, and the level set of distance $k$ is
`SimpleGraph.sphere`, which contains only indices reachable from $v$. The clauses are
`Matrix.abs_dist_sub_dist_le_one_of_apply_ne_zero`, `Matrix.apply_eq_zero_of_dist_lt` and
`SimpleGraph.isSeparator_sphere`. -/
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

/-- **Section 3.3.3** of [saad2003iterative], the size of an independent set. Let
$A \in \mathbb{R}^{n \times n}$, let $\Delta$ be the maximum degree of its symmetrized adjacency
graph, and let $S$ be a maximal independent set of this graph. Then
$$n \le (\Delta + 1) |S|, \qquad \text{that is} \qquad |S| \ge \frac{n}{1 + \Delta}.$$
Moreover, for every $\nu \in \mathbb{N}$, if every member of $S$ has degree at most $\nu$, then
$n \le (\nu + 1) |S|$.

**Generalization.** The source states the bound for the set that Algorithm 3.4 produces. Its
argument, that every index is in $S$ or adjacent to a member of $S$, proves the bound for every
maximal independent set, and this is how it is stated here.

The heuristic recurrence $n_i = n_{i-1} - \nu_i - 1$ after the bound is a rule of thumb, as the
source says, and is not formalized. The proof is
`SimpleGraph.card_le_mul_card_of_maximal_isIndepSet`. -/
theorem indepSet_card_ge (A : Matrix (Fin n) (Fin n) ℝ) [DecidableRel A.adjGraph.Adj]
    {s : Finset (Fin n)} (hs : Maximal A.adjGraph.IsIndepSet (s : Set (Fin n))) (ν : ℕ) :
    n ≤ (A.adjGraph.maxDegree + 1) * #s ∧
      ((∀ w ∈ s, A.adjGraph.degree w ≤ ν) → n ≤ (ν + 1) * #s) := by
  constructor
  · simpa using SimpleGraph.card_le_mul_card_of_maximal_isIndepSet hs
  · intro hν
    simpa using SimpleGraph.card_le_mul_card_of_maximal_isIndepSet_of_forall_degree_le hs hν

/-- **Equation (3.3)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and let $S$ be an
independent set of its symmetrized adjacency graph. Then $a_{ij} = 0$ for all distinct
$i, j \in S$. Moreover, for every permutation $\sigma$, the entry $(i, j)$ of
$A_{\sigma,\sigma}$ is zero whenever $i \neq j$ and $\sigma(i), \sigma(j) \in S$.

So if a reordering puts the indices of $S$ first, the leading diagonal block of the reordered
matrix is diagonal, and $A_{\sigma,\sigma}$ has the form (3.3),
$\begin{bmatrix} D & E \\ F & C \end{bmatrix}$ with $D$ diagonal. The proof is
`Matrix.apply_eq_zero_of_isIndepSet`. -/
theorem equation_3_3 (A : Matrix (Fin n) (Fin n) ℝ) {s : Set (Fin n)}
    (hs : A.adjGraph.IsIndepSet s) (σ : Equiv.Perm (Fin n)) :
    (∀ i j, i ∈ s → j ∈ s → i ≠ j → A i j = 0) ∧
      (∀ i j, σ i ∈ s → σ j ∈ s → i ≠ j → (A.submatrix σ σ) i j = 0) :=
  ⟨fun _ _ hi hj hij => apply_eq_zero_of_isIndepSet hs hi hj hij,
    fun _ _ hi hj hij => apply_eq_zero_of_isIndepSet hs hi hj (σ.injective.ne hij)⟩

/-! ### §3.3.3 Common reorderings: multicolouring -/

/-- **Section 3.3.3** of [saad2003iterative], multicolour orderings. Let
$A \in \mathbb{R}^{n \times n}$ and let $c$ be a proper colouring of its symmetrized adjacency
graph. Then $a_{ij} = 0$ for all distinct $i, j$ with $c(i) = c(j)$. Moreover, for every
permutation $\sigma$, the entry $(i, j)$ of $A_{\sigma,\sigma}$ is zero whenever $i \neq j$ and
$c(\sigma(i)) = c(\sigma(j))$. So an ordering that groups the indices by colour makes every
diagonal block of $A_{\sigma,\sigma}$ a diagonal matrix.

No hypothesis on the pattern is needed, because `Matrix.adjGraph` is already the symmetrized
graph. The proof is `Matrix.apply_eq_zero_of_coloring_eq`. With two colours this is Property A
(Definition 4.11) and the block form (4.42) of the source. The relation with
`SaadSparse.Chapter04.HasPropertyA` belongs in Chapter 4, which imports this module. -/
theorem multicoloring_blocks {α : Type*} (A : Matrix (Fin n) (Fin n) ℝ)
    (c : A.adjGraph.Coloring α) (σ : Equiv.Perm (Fin n)) :
    (∀ i j, i ≠ j → c i = c j → A i j = 0) ∧
      (∀ i j, i ≠ j → c (σ i) = c (σ j) → (A.submatrix σ σ) i j = 0) :=
  ⟨fun _ _ hij h => apply_eq_zero_of_coloring_eq c hij h,
    fun _ _ hij h => apply_eq_zero_of_coloring_eq c (σ.injective.ne hij) h⟩

/-- **Section 3.3.3** and **Problem P-3.10** of [saad2003iterative]. Let
$A \in \mathbb{R}^{n \times n}$ have a symmetric pattern, that is $a_{ij} \neq 0$ implies
$a_{ji} \neq 0$, and let each row of $A$ have at most $\nu$ nonzero off-diagonal entries. Then
there is a colouring $c$ of the indices with $\nu + 1$ colours such that $a_{ij} = 0$ for all
distinct $i, j$ with $c(i) = c(j)$. So $A$ has a multicolour ordering with $\nu + 1$ colours.

A symmetric pattern is needed here and nowhere else in §3.3.3: the degree of index $i$ in the
symmetrized graph is the count of nonzeros in row $i$ only when a nonzero $a_{ji}$ forces a
nonzero $a_{ij}$. The count excludes the diagonal, because the adjacency graph of the source has
a self-loop at every nonzero diagonal entry and the reorderings act on the loopless graph. The
colours are `Fin (ν + 1)`, and the proof is `Matrix.exists_coloring_of_le_maxDegree`, the greedy
bound applied to the adjacency graph. -/
theorem exists_multicoloring (A : Matrix (Fin n) (Fin n) ℝ) {ν : ℕ}
    (hsymm : ∀ i j, A i j ≠ 0 → A j i ≠ 0)
    (hrow : ∀ i, #{j ∈ univ | j ≠ i ∧ A i j ≠ 0} ≤ ν) :
    ∃ c : Fin n → Fin (ν + 1), ∀ i j, i ≠ j → c i = c j → A i j = 0 :=
  exists_coloring_of_le_maxDegree hsymm hrow

/-- **Algorithm 3.6** and **Problems P-3.9, P-3.10 and P-3.11** of [saad2003iterative], the greedy
colouring. Let $A \in \mathbb{R}^{n \times n}$ have a symmetric pattern, that is $a_{ij} \neq 0$
implies $a_{ji} \neq 0$, and let each row of $A$ have at most $\nu$ nonzero off-diagonal
entries. Colour the indices greedily in increasing order, giving each index the least colour in
$\{0, 1, 2, \dots\}$ that no earlier neighbour has. Then the following hold.

* Every colour is at most $\nu$, so the greedy colouring uses at most $\nu + 1$ colours (Problem
  P-3.10).
* Suppose that the symmetrized adjacency graph of $A$ is bipartite, and that every index $v$
  that is reachable from an earlier index has an earlier neighbour. Then every colour is at most
  $1$, so the greedy colouring uses two colours (Problem P-3.11(b)).

Breadth-first search gives an order with the property of the second clause, and an arbitrary
traversal does not (Problem P-3.11(a)).

**Reading.** The traversal of Algorithm 3.6 is the order of the index set `Fin n`, so it is the
identity ordering of a matrix that is already reordered.

The greedy colouring is `SimpleGraph.greedyColoring` of `Matrix.adjGraph`, and the clauses are
`SimpleGraph.greedyColoring_le_maxDegree` and
`SimpleGraph.greedyColoring_le_one_of_isBipartite`. Problem P-3.9, that the graph of the
five-point grid is two-coloured, is the second clause for the graph of
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
      (Matrix.maxDegree_adjGraph_le hsymm hrow),
    fun h2 hord v => SimpleGraph.greedyColoring_le_one_of_isBipartite h2 hord v⟩

/-! ### §3.3.4 Irreducibility -/

/-- **Section 3.3.4** of [saad2003iterative], irreducibility. A matrix
$A \in \mathbb{R}^{n \times n}$ is irreducible when every ordered pair of indices is joined by a
directed path of positive length in its adjacency graph, and reducible otherwise. Let $n \ge 2$.
Then $A$ is irreducible if and only if, for every permutation $\sigma$ and every nonempty proper
subset $s$ of the indices, some entry $(i, j)$ of $A_{\sigma,\sigma}$ with $i \in s$ and
$j \notin s$ is nonzero. Equivalently, $A$ is reducible if and only if there are a permutation
$\sigma$ and a nonempty proper subset $s$ such that every entry $(i, j)$ of $A_{\sigma,\sigma}$
with $i \in s$ and $j \notin s$ is zero, which is the block triangular form of the source.

**Reading.** The source calls $A$ irreducible when its adjacency graph is "connected". This is
read for a directed graph with directed paths, that is as strongly connected. The hypothesis
$n \ge 2$ is needed: irreducibility asks for a path of positive length between every pair of
indices, so the $1 \times 1$ zero matrix is reducible, while its index set has no nonempty
proper subset.

Irreducibility is `Matrix.IsPatternIrreducible`, and its unfolding to paths is
`Matrix.isPatternIrreducible_iff`. The block form is
`Matrix.isPatternIrreducible_iff_forall_submatrix_not_blockTriangular`. This is the notion that
Definition 4.5, Theorem 4.7, Corollary 4.8 and Theorem 4.9 of Chapter 4 use. The full Frobenius
normal form is `SaadSparse.Chapter03.frobenius_normal_form`. -/
theorem isPatternIrreducible_iff (A : Matrix (Fin n) (Fin n) ℝ) (hn : 2 ≤ n) :
    (A.IsPatternIrreducible ↔ ∀ (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)),
        s.Nonempty → s ≠ univ → ∃ i ∈ s, ∃ j ∉ s, (A.submatrix σ σ) i j ≠ 0) ∧
      (¬ A.IsPatternIrreducible ↔ ∃ (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)),
        s.Nonempty ∧ s ≠ univ ∧ ∀ i ∈ s, ∀ j ∉ s, (A.submatrix σ σ) i j = 0) :=
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  ⟨isPatternIrreducible_iff_forall_submatrix_not_blockTriangular,
    not_isPatternIrreducible_iff_exists_submatrix_blockTriangular⟩

/-- **Section 3.3.4** of [saad2003iterative], the Frobenius normal form. Let
$A \in \mathbb{R}^{n \times n}$. Then there are a permutation $\sigma$ and a nondecreasing map
$b$ from the indices to $\mathbb{N}$ such that $A_{\sigma,\sigma}$ is block upper triangular for
$b$, that is its entry $(i, j)$ is zero whenever $b(j) < b(i)$, and $b(i) = b(j)$ if and only if
$\sigma(i)$ and $\sigma(j)$ are strongly connected in the adjacency graph of $A$. So the
diagonal blocks are the strongly connected components of the adjacency graph, and they are
listed in an order in which every arrow points forward.

**Reading.** The source prints only the shape of the reduced matrix, and says that each block
"corresponds to a connected component". The graph is directed, so the components are the
strongly connected ones, for the arrow relation $a_{ij} \neq 0$. They must be listed in a
topological order, because otherwise no permutation makes the matrix block triangular. The
monotonicity of $b$ and the block triangular form state this together, and the monotonicity of
$b$ also makes each block an interval of consecutive indices.

Strong connection is `Relation.StronglyConnected` for the arrows of `Matrix.adjDigraph`, and the
block form is `Matrix.BlockTriangular`. The proof specializes
`Matrix.exists_perm_submatrix_blockTriangular`, and `A.submatrix σ σ` is $P_\sigma A P_\sigma^T$
by `Matrix.submatrix_eq_permMatrix_mul_mul_transpose`. An irreducible matrix has a single block,
by `Matrix.stronglyConnected_of_isPatternIrreducible`. -/
theorem frobenius_normal_form (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (σ : Equiv.Perm (Fin n)) (b : Fin n → ℕ), Monotone b ∧
      (A.submatrix σ σ).BlockTriangular b ∧
      ∀ i j, b i = b j ↔ Relation.StronglyConnected A.adjDigraph.Adj (σ i) (σ j) :=
  Matrix.exists_perm_submatrix_blockTriangular A

end SaadSparse.Chapter03
