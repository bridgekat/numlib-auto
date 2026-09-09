import Numlib.Combinatorics.SimpleGraph.IndepSet
import Numlib.LinearAlgebra.Sparse.Frobenius
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

§3.3.2 gets Example 3.3, the `9 × 9` arrow matrix, as `example_3_3`.  Figure 3.4 prints a pattern
and no values — nonzeros on the diagonal and in the first row and column — so the pattern is the
hypothesis and every clause holds of every matrix carrying it: the adjacency graph is the star, the
reversing permutation `9, 8, …, 1` turns the pattern upside down and only relabels the graph, one
elimination step on the original fills the whole trailing block, and the reordered matrix has an
exhibited `L U` factorization whose factors vanish wherever it does.  The last two are the fill
claims of the example, stated as far as §3.3 reaches; the characterization of the fill of *complete*
Gaussian elimination is `SaadSparse.Chapter10.theorem_10_6`, which this example instantiates.

§3.3.4 gets two: the reducibility characterization `isPatternIrreducible_iff`, and the Frobenius
normal form `frobenius_normal_form`, whose block index is the topological ordering of the strongly
connected components of `Numlib/Combinatorics/Relation/StronglyConnected`.

Examples 3.4, 3.5 and 3.6 are not tracked, all three for the same reason: each is a run on the
finite element mesh of Figure 2.10, which the source text does not reproduce, so there is no graph
to state them over and no statement to plan.  Example 3.4 compares two orderings by bandwidth and
profile, which this
edition never defines either; Example 3.5's optimality claim the book itself hedges as a "may well
be"; and the four-colour count of Example 3.6 is an instance of `greedy_coloring_bounds` and
`exists_multicoloring`, which are proved here in general.

Two more things get no declaration.  Reverse Cuthill–McKee is given by the book as an observation
of George's, with a picture and no statement, and this edition proves no bandwidth or profile bound
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

/-! ### §3.3.2 Example 3.3, the arrow matrix -/

/-- The `L` factor of the reversed arrow matrix of Figure 3.5: the identity together with the last
row `l_j / d_j`.  Nothing but the last row is filled, which is Example 3.3's claim. -/
private noncomputable def arrowL (B : Matrix (Fin 9) (Fin 9) ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.of fun i j => if i = j then 1 else if i = 8 then B 8 j / B j j else 0

/-- The `U` factor of the reversed arrow matrix of Figure 3.5: the diagonal of `B` together with its
last column, whose bottom entry is the Schur complement `s - ∑ l_k u_k / d_k`. -/
private noncomputable def arrowU (B : Matrix (Fin 9) (Fin 9) ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.of fun i j =>
    if j = 8 then (if i = 8 then B 8 8 - ∑ k ∈ univ.erase 8, B 8 k * B k 8 / B k k else B i 8)
    else if i = j then B i i else 0

/-- **Saad Example 3.3**, the `9 × 9` "arrow" matrix of Figure 3.4 and the reversing permutation
`9, 8, …, 1`.  The book prints a *pattern* and no values: nonzeros on the diagonal and in the first
row and the first column.  That pattern is the hypothesis, and every clause below holds of every
matrix carrying it.

* The adjacency graph is the star of Figure 3.4: index `1` is adjacent to all the others and no two
  others are adjacent, which is why Saad prefers "star matrix" to "arrow matrix".
* The reversing permutation `σ : i ↦ 9 - i`, applied symmetrically, turns the pattern upside down —
  nonzeros on the diagonal and in the *last* row and column, Figure 3.5 — and only relabels the
  graph, by `adjGraph_submatrix`: the star is now centred at `9`.
* On the original matrix one step of Gaussian elimination fills the whole trailing block: every
  off-diagonal entry of `a_ij - a_i1 a_1j / a_11` with `i, j ≠ 1` is nonzero, and none of them was.
  These are Saad's "disastrous fill-ins", and no assumption on the values is needed: the entry
  produced is `-a_i1 a_1j / a_11`, a quotient of products of nonzeros.
* On the reordered matrix there is no fill-in at all: it has an exact factorization `L U` with `L`
  unit lower triangular, `U` upper triangular and *both factors vanishing wherever the matrix
  does*, which is Saad's "the `L` and `U` parts of the `LU` factorization will have the same
  structure as the lower and upper parts of `A`".  The factors are exhibited, so no existence
  theorem for `LU` is needed.

The fill claims are about one elimination step and about an exhibited factorization, which is as
far as §3.3 can state them: the characterization of the fill of *complete* Gaussian elimination is
Theorem 10.6, and this example is its smallest instance. -/
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
Theorem 4.9 of the Chapter 4 surface use.  The full Frobenius normal form is
`SaadSparse.Chapter03.frobenius_normal_form` below. -/
theorem isPatternIrreducible_iff (A : Matrix (Fin n) (Fin n) ℝ) (hn : 2 ≤ n) :
    (A.IsPatternIrreducible ↔ ∀ (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)),
        s.Nonempty → s ≠ univ → ∃ i ∈ s, ∃ j ∉ s, (A.submatrix σ σ) i j ≠ 0) ∧
      (¬ A.IsPatternIrreducible ↔ ∃ (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)),
        s.Nonempty ∧ s ≠ univ ∧ ∀ i ∈ s, ∀ j ∉ s, (A.submatrix σ σ) i j = 0) :=
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  ⟨isPatternIrreducible_iff_forall_submatrix_not_blockTriangular,
    not_isPatternIrreducible_iff_exists_submatrix_blockTriangular⟩

/-- **Saad §3.3.4, the Frobenius normal form**: a symmetric permutation puts any square matrix in
block upper triangular form whose diagonal blocks are the strongly connected components of its
adjacency graph, listed in an order in which every arrow points forward.

The book prints only the shape of the reduced matrix and says that each partition "corresponds to
a connected component".  Two things are added here to make that a theorem.  The graph is directed,
so the components meant are the *strongly* connected ones, `Relation.StronglyConnected` of the
arrow relation `A i j ≠ 0`; and they have to be listed in a topological order, without which no
permutation triangulates the matrix — that is what `Monotone b` and `Matrix.BlockTriangular`
together say, `Monotone b` being also what makes each block an interval of consecutive indices.
The backbone is `Matrix.exists_perm_submatrix_blockTriangular`, and `A.submatrix σ σ` is `P A Pᵀ`
by `Matrix.submatrix_eq_permMatrix_mul_mul_transpose`.  An irreducible matrix has a single block,
`Matrix.stronglyConnected_of_isPatternIrreducible`. -/
theorem frobenius_normal_form (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (σ : Equiv.Perm (Fin n)) (b : Fin n → ℕ), Monotone b ∧
      (A.submatrix σ σ).BlockTriangular b ∧
      ∀ i j, b i = b j ↔ Relation.StronglyConnected A.adjDigraph.Adj (σ i) (σ j) :=
  Matrix.exists_perm_submatrix_blockTriangular A

end SaadSparse.Chapter03
