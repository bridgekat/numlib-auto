/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: beside `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`.
Keep it free of dependencies on the rest of `Numlib`.
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Permutation
import Numlib.Combinatorics.Quiver.Path

/-!
# The pattern of a matrix and the graphs it defines

The *pattern* of a square matrix $A$ is the set of positions $(i, j)$ with $a_{ij} \neq 0$. The
sparse-matrix reorderings of [saad2003iterative], §3.2–3.3, act on the graph of the pattern. The
source uses three versions of this graph, and this module defines all three: the *adjacency
digraph*, with an arrow $i \to j$ exactly when $a_{ij} \neq 0$; the undirected loopless *pattern
graph*, in which $i \neq j$ are adjacent when $a_{ij} \neq 0$ or $a_{ji} \neq 0$; and the *adjacency
quiver*, the same relation in the form that Mathlib's path API uses. A symmetric permutation
$A \mapsto P A P^T$ only relabels the vertices of these graphs. A permutation that is not symmetric
does not; this is the warning of the source, and the reason why its reorderings are always
symmetric.

The module also defines two properties of a pattern. The pattern is *symmetric* when $a_{ij}$ and
$a_{ji}$ are zero or nonzero together. The matrix is *pattern-irreducible* when its adjacency
digraph is strongly connected, and the main theorem characterizes reducibility: on at least two
indices, $A$ is not pattern-irreducible exactly when a symmetric permutation puts it in block
triangular form. Finally, a nonzero entry of a product $A B$ forces matching nonzero entries of $A$
and $B$, with no hypothesis.

## Main definitions

* `Matrix.adjDigraph`: the adjacency digraph of [saad2003iterative], with an arrow $i \to j$ exactly
  when $a_{ij} \neq 0$.
* `Matrix.adjGraph`: the undirected loopless graph of the pattern.
* `Matrix.adjQuiver`: the adjacency digraph as a quiver.
* `Matrix.IsPatternSymm`: the pattern is symmetric, that is, $A$ is structurally symmetric in the
  words of [golub2013matrix], §11.1.9.
* `Matrix.IsPatternIrreducible`: the irreducibility of [saad2003iterative], §3.3.4, for an arbitrary
  matrix: the adjacency digraph is strongly connected.

## Main results

* `Matrix.adjDigraph_submatrix_adj`, `Matrix.adjGraphIso`: a symmetric permutation is a relabelling
  of the adjacency digraph and of the pattern graph.
* `Matrix.adjGraph_adj_iff_of_isSymm`: for a symmetric matrix, off the diagonal the pattern graph
  and the adjacency digraph carry the same information.
* `Matrix.isPatternSymm_iff_adjDigraph_symm`: the pattern is symmetric exactly when the adjacency
  digraph is symmetric.
* `Matrix.exists_apply_ne_zero_of_mul_apply_ne_zero`,
  `Matrix.exists_path_length_of_pow_apply_ne_zero`: a nonzero entry $(AB)_{ij}$ forces
  $a_{ik} \neq 0$ and $b_{kj} \neq 0$ for some $k$, and a nonzero entry of $A^k$ forces a path of
  length $k$.
* `Matrix.isPatternIrreducible_iff_isIrreducible`, `Matrix.isPatternIrreducible_iff_exists_pow_pos`:
  for an entrywise nonnegative real matrix, pattern irreducibility is Mathlib's irreducibility; in
  general it is the positivity of an entry of some power of the matrix of entrywise norms, for each
  pair of indices.
* `Matrix.IsPatternIrreducible.forall_of_closed`: a property that holds at one index and propagates
  along the nonzero entries of an irreducible matrix holds at every index.
* `Matrix.isPatternIrreducible_iff_forall_submatrix_not_blockTriangular`: on at least two indices,
  $A$ is pattern-irreducible exactly when no symmetric permutation puts it in block triangular form.

## Implementation notes

* The adjacency digraph is *directed*, and it *has a loop* at every nonzero diagonal entry. Thus
  `SimpleGraph` is the wrong type for it, and it is a `Digraph`.
* `Digraph` has no walks in Mathlib, so the module also needs a quiver. The quiver
  `Matrix.adjQuiver A` is `Matrix.toQuiver` of the matrix of entrywise norms, so it is
  *definitionally* the quiver of Mathlib's `Matrix.IsIrreducible`, and no path has to be transported
  between the two.
* `Matrix.IsPatternIrreducible A` is `Matrix.IsIrreducible` of the matrix of entrywise norms
  $(\|a_{ij}\|)$. Mathlib's `Matrix.IsIrreducible` applies only to entrywise nonnegative matrices,
  while the notion of [saad2003iterative] applies to any matrix. The entrywise norm is nonnegative
  and vanishes exactly where the matrix does, so it carries any pattern into Mathlib's setting.
* The full Frobenius normal form, whose diagonal blocks are the strongly connected components in a
  topological order, is in `Numlib.LinearAlgebra.Sparse.Frobenius`.
-/

open Quiver

namespace Matrix

variable {n R S : Type*}

/-! ### The adjacency digraph, graph and quiver of a pattern -/

section Zero

variable [Zero R] [Zero S]

/-- The **adjacency graph** of a square matrix $A$ in the sense of [saad2003iterative]: the digraph
on the index set with an arrow $i \to j$ exactly when $a_{ij} \neq 0$. It is directed, and it
has a loop at every nonzero diagonal entry. -/
def adjDigraph (A : Matrix n n R) : Digraph n where
  Adj i j := A i j ≠ 0

/-- There is an arrow $i \to j$ in the adjacency digraph of $A$ if and only if $a_{ij} \neq 0$. -/
@[simp]
theorem adjDigraph_adj {A : Matrix n n R} {i j : n} : A.adjDigraph.Adj i j ↔ A i j ≠ 0 := Iff.rfl

/-- There is an arrow $i \to j$ in the adjacency digraph of $A^T$ if and only if there is an arrow
$j \to i$ in the adjacency digraph of $A$: transposition reverses the arrows. -/
@[simp]
theorem adjDigraph_transpose_adj {A : Matrix n n R} {i j : n} :
    Aᵀ.adjDigraph.Adj i j ↔ A.adjDigraph.Adj j i := Iff.rfl

/-- Let $f$ be a map with $f(x) = 0$ if and only if $x = 0$, for example the norm, or the inclusion
of the real numbers in the complex numbers. Then the matrix $(f(a_{ij}))$ has the same adjacency
digraph as $A$. -/
theorem adjDigraph_map (A : Matrix n n R) (f : R → S) (hf : ∀ x, f x = 0 ↔ x = 0) :
    (A.map f).adjDigraph = A.adjDigraph := by
  ext i j
  simp [adjDigraph, hf]

/-- The **pattern graph** of a square matrix $A$: the undirected loopless graph on the index set in
which $i$ and $j$ are adjacent when $i \neq j$ and $a_{ij} \neq 0$ or $a_{ji} \neq 0$. The
sparse-matrix reorderings of [saad2003iterative], §3.3.3, act on this graph. -/
def adjGraph (A : Matrix n n R) : SimpleGraph n := SimpleGraph.fromRel fun i j => A i j ≠ 0

/-- Two indices $i$ and $j$ are adjacent in the pattern graph of $A$ if and only if $i \neq j$ and
$a_{ij} \neq 0$ or $a_{ji} \neq 0$. -/
@[simp]
theorem adjGraph_adj {A : Matrix n n R} {i j : n} :
    A.adjGraph.Adj i j ↔ i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0) :=
  SimpleGraph.fromRel_adj _ _ _

/-- Let $A$ be a square matrix such that $a_{ij} \neq 0$ implies $a_{ji} \neq 0$. Then $i$ and $j$
are adjacent in the pattern graph if and only if $i \neq j$ and there is an arrow $i \to j$ in
the adjacency digraph. -/
theorem adjGraph_adj_iff_of_forall_ne_zero {A : Matrix n n R}
    (hA : ∀ i j, A i j ≠ 0 → A j i ≠ 0) {i j : n} :
    A.adjGraph.Adj i j ↔ i ≠ j ∧ A.adjDigraph.Adj i j := by
  simp only [adjGraph_adj, adjDigraph_adj, and_congr_right_iff]
  exact fun _ => ⟨fun h => h.elim id fun h' => hA _ _ h', Or.inl⟩

/-- Let $A$ be a symmetric matrix, $A^T = A$. Then $i$ and $j$ are adjacent in the pattern graph of
$A$ if and only if $i \neq j$ and there is an arrow $i \to j$ in the adjacency digraph of $A$.
Thus, off the diagonal, the two graphs carry the same information. -/
theorem adjGraph_adj_iff_of_isSymm {A : Matrix n n R} (hA : A.IsSymm) {i j : n} :
    A.adjGraph.Adj i j ↔ i ≠ j ∧ A.adjDigraph.Adj i j :=
  adjGraph_adj_iff_of_forall_ne_zero fun i j h => by rwa [hA.apply]

end Zero

section Quiver

variable [Norm R]

/-- The **adjacency quiver** of a square matrix $A$: the quiver on the index set with an arrow
$i \to j$ for every nonzero entry $a_{ij}$.

It is defined as `Matrix.toQuiver` of the matrix of entrywise norms $(\|a_{ij}\|)$, so that it
is *definitionally* the quiver of Mathlib's `Matrix.IsIrreducible`. The lemmas
`Matrix.nonempty_adjQuiver_hom_iff` and `Matrix.adjHom` relate it to `Matrix.adjDigraph`. The
quiver is needed beside the digraph only because `Digraph` has no walks in Mathlib. -/
@[instance_reducible]
noncomputable def adjQuiver (A : Matrix n n R) : Quiver n := (A.map (‖·‖)).toQuiver

end Quiver

section Normed

variable [NormedAddCommGroup R] {A : Matrix n n R}

/-- Let $A$ be a square matrix over a normed additive group. There is an arrow $i \to j$ in the
adjacency quiver of $A$ if and only if $a_{ij} \neq 0$. Thus the quiver carries the same
relation as `Matrix.adjDigraph`. -/
@[simp]
theorem nonempty_adjQuiver_hom_iff {i j : n} :
    Nonempty (@Quiver.Hom n A.adjQuiver i j) ↔ A i j ≠ 0 :=
  ⟨fun ⟨e⟩ => norm_pos_iff.1 e.down, fun h => ⟨PLift.up (norm_pos_iff.2 h)⟩⟩

/-- The arrow $i \to j$ of the adjacency quiver given by a nonzero entry $a_{ij}$. -/
def adjHom {i j : n} (h : A i j ≠ 0) : @Quiver.Hom n A.adjQuiver i j :=
  PLift.up (norm_pos_iff.2 h)

/-- An arrow $i \to j$ of the adjacency quiver gives $a_{ij} \neq 0$. -/
theorem apply_ne_zero_of_adjHom {i j : n} (e : @Quiver.Hom n A.adjQuiver i j) : A i j ≠ 0 :=
  norm_pos_iff.1 e.down

end Normed

/-! ### Symmetric permutations are relabellings -/

section Submatrix

variable [Zero R]

/-- A symmetric permutation of a matrix is a relabelling of its adjacency digraph
([saad2003iterative], §3.3.2). For a permutation $\sigma$ of the indices, there is an arrow
$i \to j$ in the adjacency digraph of $(a_{\sigma(i) \sigma(j)})_{i,j}$ if and only if there is
an arrow $\sigma(i) \to \sigma(j)$ in the adjacency digraph of $A$. The statement holds by
definition. -/
theorem adjDigraph_submatrix_adj (A : Matrix n n R) (σ : Equiv.Perm n) (i j : n) :
    (A.submatrix σ σ).adjDigraph.Adj i j ↔ A.adjDigraph.Adj (σ i) (σ j) := Iff.rfl

/-- A symmetric permutation of a matrix is a relabelling of its pattern graph: for a permutation
$\sigma$ of the indices, $\sigma$ is a graph isomorphism from the pattern graph of
$(a_{\sigma(i) \sigma(j)})_{i,j}$ to the pattern graph of $A$. -/
def adjGraphIso (A : Matrix n n R) (σ : Equiv.Perm n) :
    (A.submatrix σ σ).adjGraph ≃g A.adjGraph where
  toEquiv := σ
  map_rel_iff' := by
    intro i j
    simp [adjGraph_adj, σ.injective.ne_iff]

/-- The isomorphism `Matrix.adjGraphIso A σ` maps $i$ to $\sigma(i)$. -/
@[simp]
theorem adjGraphIso_apply (A : Matrix n n R) (σ : Equiv.Perm n) (i : n) :
    adjGraphIso A σ i = σ i := rfl

/-- For a permutation $\sigma$ of the indices, $i$ and $j$ are adjacent in the pattern graph of
$(a_{\sigma(i) \sigma(j)})_{i,j}$ if and only if $\sigma(i)$ and $\sigma(j)$ are adjacent in the
pattern graph of $A$. This is the undirected form of `Matrix.adjDigraph_submatrix_adj`. -/
@[simp]
theorem adjGraph_submatrix_adj (A : Matrix n n R) (σ : Equiv.Perm n) (i j : n) :
    (A.submatrix σ σ).adjGraph.Adj i j ↔ A.adjGraph.Adj (σ i) (σ j) :=
  ((adjGraphIso A σ).map_adj_iff).symm

/-- A symmetric permutation keeps colourability of the pattern graph: for a permutation $\sigma$ and
$k \in \mathbb{N}$, the pattern graph of $(a_{\sigma(i) \sigma(j)})_{i,j}$ has a $k$-colouring
if and only if the pattern graph of $A$ has one. -/
theorem colorable_adjGraph_submatrix_iff (A : Matrix n n R) (σ : Equiv.Perm n) {k : ℕ} :
    (A.submatrix σ σ).adjGraph.Colorable k ↔ A.adjGraph.Colorable k :=
  ⟨fun h => SimpleGraph.Colorable.of_hom (adjGraphIso A σ).symm.toHom h,
    fun h => SimpleGraph.Colorable.of_hom (adjGraphIso A σ).toHom h⟩

/-- A symmetric permutation keeps connectedness of the pattern graph: for a permutation $\sigma$,
the pattern graph of $(a_{\sigma(i) \sigma(j)})_{i,j}$ is preconnected if and only if the
pattern graph of $A$ is preconnected. -/
theorem preconnected_adjGraph_submatrix_iff (A : Matrix n n R) (σ : Equiv.Perm n) :
    (A.submatrix σ σ).adjGraph.Preconnected ↔ A.adjGraph.Preconnected :=
  (adjGraphIso A σ).preconnected_iff

end Submatrix

/-! ### Structural symmetry -/

section PatternSymm

variable [Zero R]

/-- A square matrix $A$ is **structurally symmetric**, or has a **symmetric pattern**, when for all
$i$ and $j$
$$a_{ij} \neq 0 \iff a_{ji} \neq 0$$
([golub2013matrix], §11.1.9). Equivalently, its adjacency digraph is symmetric. Symmetric
matrices are structurally symmetric (`Matrix.IsSymm.isPatternSymm`), and so are their row and
column scalings (`Matrix.IsPatternSymm.diagonal_mul_mul_diagonal`). -/
def IsPatternSymm (A : Matrix n n R) : Prop := ∀ i j, A i j ≠ 0 ↔ A j i ≠ 0

/-- The pattern of $A$ is symmetric if and only if the adjacency digraph of $A$ is symmetric: an
arrow $i \to j$ gives an arrow $j \to i$. -/
theorem isPatternSymm_iff_adjDigraph_symm {A : Matrix n n R} :
    A.IsPatternSymm ↔ ∀ i j, A.adjDigraph.Adj i j → A.adjDigraph.Adj j i :=
  ⟨fun h i j => (h i j).1, fun h i j => ⟨h i j, h j i⟩⟩

/-- Let $A$ be a structurally symmetric matrix indexed by $n$, and let $e$ be any map from an index
set $m$ to $n$. Then the matrix $(a_{e(i) e(j)})_{i,j \in m}$ is structurally symmetric. In
particular, a symmetric permutation $P A P^T$ of a structurally symmetric matrix is structurally
symmetric. -/
theorem IsPatternSymm.submatrix {A : Matrix n n R} (h : A.IsPatternSymm) {m : Type*}
    (e : m → n) : (A.submatrix e e).IsPatternSymm :=
  fun i j => h (e i) (e j)

/-- A symmetric matrix, $A^T = A$, is structurally symmetric. -/
theorem IsSymm.isPatternSymm {A : Matrix n n R} (h : A.IsSymm) : A.IsPatternSymm :=
  fun i j => by rw [h.apply i j]

/-- Let $R$ be a semiring with no zero divisors, let $A$ be a structurally symmetric square matrix
over $R$, and let $d_1$ and $d_2$ be vectors with no zero entry. Then $\operatorname{diag}(d_1)
\, A \, \operatorname{diag}(d_2)$ is structurally symmetric. This covers the "symmetric matrices
whose rows and/or columns are scaled" of [golub2013matrix], §11.1.9. -/
theorem IsPatternSymm.diagonal_mul_mul_diagonal {R : Type*} [Semiring R] [NoZeroDivisors R]
    [Fintype n] [DecidableEq n] {A : Matrix n n R} (h : A.IsPatternSymm) {d₁ d₂ : n → R}
    (hd₁ : ∀ i, d₁ i ≠ 0) (hd₂ : ∀ i, d₂ i ≠ 0) :
    (diagonal d₁ * A * diagonal d₂).IsPatternSymm := by
  intro i j
  simp only [mul_diagonal, diagonal_mul, ne_eq, mul_eq_zero, hd₁, hd₂, false_or, or_false]
  exact h i j

end PatternSymm

section PermMatrix

variable [Fintype n] [DecidableEq n] [NonAssocSemiring R]

/-- Let $A$ be a square matrix over a semiring and let $\sigma$ be a permutation of the indices,
with permutation matrix $P$ (`Equiv.Perm.permMatrix`). Then the symmetric permutation
$(a_{\sigma(i) \sigma(j)})_{i,j}$ is $P A P^T$, the form in which [saad2003iterative] writes it. -/
theorem submatrix_eq_permMatrix_mul_mul_transpose (A : Matrix n n R) (σ : Equiv.Perm n) :
    A.submatrix σ σ = σ.permMatrix R * A * (σ.permMatrix R)ᵀ := by
  rw [transpose_permMatrix]
  rw [show σ.permMatrix R = σ.toPEquiv.toMatrix from rfl,
    show (σ⁻¹).permMatrix R = (σ⁻¹).toPEquiv.toMatrix from rfl,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix]
  rfl

end PermMatrix

/-!
### The pattern of a product

Every claim of [saad2003iterative] about the pattern of a product assumes that no numerical
cancellation occurs. The direction that holds with no hypothesis is that a nonzero entry of $A B$
forces a nonzero entry of $A$ and one of $B$ in matching positions; hence a nonzero entry of $A^k$
forces a path of length $k$ in the adjacency quiver. The converse is false in general, because of
cancellation. It is true for entrywise nonnegative matrices, where it is
`Matrix.mul_apply_pos_of_pos_of_pos` here and Mathlib's `Matrix.pow_apply_pos_iff_nonempty_path` for
powers.
-/

section Mul

variable [Fintype n]

/-- Let $A$ and $B$ be square matrices over a non-unital non-associative semiring with a finite
index set. If $(AB)_{ij} \neq 0$, then there is an index $k$ with $a_{ik} \neq 0$ and
$b_{kj} \neq 0$. Thus the pattern of a product is contained in the composite of the patterns. No
hypothesis is needed for this direction; the converse fails because of cancellation. -/
theorem exists_apply_ne_zero_of_mul_apply_ne_zero [NonUnitalNonAssocSemiring R]
    {A B : Matrix n n R} {i j : n} (h : (A * B) i j ≠ 0) : ∃ k, A i k ≠ 0 ∧ B k j ≠ 0 := by
  by_contra! hc
  refine h ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases eq_or_ne (A i k) 0 with hk | hk
  · simp [hk]
  · simp [hc k hk]

/-- Let $A$ and $B$ be entrywise nonnegative square matrices over a strictly ordered semiring, with
a finite index set. If $a_{ik} > 0$ and $b_{kj} > 0$ for some $k$, then $(AB)_{ij} > 0$. This is
the converse of `Matrix.exists_apply_ne_zero_of_mul_apply_ne_zero`, which holds here because no
cancellation can occur.

Problem P-3.5 of [saad2003iterative], that the patterns of $A$ and of $B$ are contained in that
of $AB$ when both have a nonzero diagonal, is this statement at $k = j$ and at $k = i$. -/
theorem mul_apply_pos_of_pos_of_pos [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    {A B : Matrix n n R} (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) {i j k : n}
    (h₁ : 0 < A i k) (h₂ : 0 < B k j) : 0 < (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_pos' (fun l _ => mul_nonneg (hA i l) (hB l j))
    ⟨k, Finset.mem_univ k, mul_pos h₁ h₂⟩

/-- Let $A$ be a square matrix over a normed ring with a finite index set, and let
$k \in \mathbb{N}$. If $(A^k)_{ij} \neq 0$, then there is a path of length $k$ from $i$ to $j$
in the adjacency quiver of $A$. This is the direction of [saad2003iterative], §3.2.1, that needs
no hypothesis. -/
theorem exists_path_length_of_pow_apply_ne_zero [DecidableEq n] [NormedRing R]
    (A : Matrix n n R) (k : ℕ) {i j : n} (h : (A ^ k) i j ≠ 0) :
    letI := A.adjQuiver
    ∃ p : Path i j, p.length = k := by
  let _ : Quiver n := A.adjQuiver
  induction k generalizing j with
  | zero =>
    obtain rfl : i = j := by
      by_contra hij
      exact h (by rw [pow_zero, one_apply_ne hij])
    exact ⟨Path.nil, rfl⟩
  | succ k ih =>
    rw [pow_succ] at h
    obtain ⟨l, hl, hlj⟩ := exists_apply_ne_zero_of_mul_apply_ne_zero h
    obtain ⟨p, hp⟩ := ih hl
    exact ⟨p.cons (adjHom hlj), by simp [Path.length_cons, hp]⟩

end Mul

/-!
### Irreducibility of a pattern

`Matrix.IsPatternIrreducible A` is the irreducibility of [saad2003iterative], §3.3.4: the adjacency
digraph is strongly connected. For an entrywise nonnegative real matrix it agrees with Mathlib's
`Matrix.IsIrreducible`, and its algebraic form is the positivity of an entry of some power of the
matrix of entrywise norms. Every use of irreducibility goes through the induction principle
`Matrix.IsPatternIrreducible.forall_of_closed`: a property that holds at one index and propagates
along the nonzero entries holds at every index.
-/

section Irreducible

/-- **Pattern irreducibility**, the irreducibility of [saad2003iterative], §3.3.4, for an arbitrary
square matrix $A$: the matrix of entrywise norms $(\|a_{ij}\|)$ is irreducible in the sense of
Mathlib's `Matrix.IsIrreducible`. Over a normed additive group this means that the adjacency
digraph of $A$ is strongly connected: any two indices, also equal ones, are joined by a path of
positive length in `Matrix.adjQuiver A` (`Matrix.isPatternIrreducible_iff`).

Mathlib's predicate applies only to entrywise nonnegative matrices. The entrywise norm is
nonnegative and vanishes exactly where the matrix does, so it carries an arbitrary pattern into
Mathlib's setting. -/
def IsPatternIrreducible [Norm R] (A : Matrix n n R) : Prop := (A.map (‖·‖)).IsIrreducible

variable [NormedAddCommGroup R] {A : Matrix n n R}

/-- Let $A$ be a square matrix over a normed additive group. Then $A$ is pattern-irreducible if and
only if for every ordered pair $(i, j)$ of indices there is a path of positive length from $i$
to $j$ in the adjacency quiver of $A$. -/
theorem isPatternIrreducible_iff :
    A.IsPatternIrreducible ↔
      letI := A.adjQuiver; ∀ i j : n, ∃ p : Path i j, 0 < p.length := by
  refine ⟨fun h => h.connected, fun h => ⟨fun i j => ?_, h⟩⟩
  rw [map_apply]
  exact norm_nonneg _

/-- If $A$ is pattern-irreducible, then for all indices $i$ and $j$ there is a path of positive
length from $i$ to $j$ in the adjacency quiver of $A$. -/
theorem IsPatternIrreducible.exists_pos_length_path (h : A.IsPatternIrreducible) (i j : n) :
    letI := A.adjQuiver; ∃ p : Path i j, 0 < p.length := isPatternIrreducible_iff.1 h i j

/-- The induction principle that every use of irreducibility goes through. Let $A$ be a
pattern-irreducible matrix over a normed additive group, and let $P$ be a property of indices
such that $P(i)$ and $a_{ij} \neq 0$ imply $P(j)$. If $P$ holds at one index, then $P$ holds at
every index. The reason is that the adjacency quiver of an irreducible matrix has a path from
any index to any other. -/
theorem IsPatternIrreducible.forall_of_closed (hA : A.IsPatternIrreducible)
    {P : n → Prop} (hstep : ∀ i j, P i → A i j ≠ 0 → P j) {i : n} (hi : P i) (j : n) : P j := by
  let _ : Quiver n := A.adjQuiver
  obtain ⟨p, -⟩ := hA.exists_pos_length_path i j
  induction p with
  | nil => exact hi
  | cons _ e ih => exact hstep _ _ ih (apply_ne_zero_of_adjHom e)

/-- Let $A$ be a square matrix over a normed additive group with at least two indices. Then $A$ is
pattern-irreducible if and only if for all indices $i$ and $j$ there is a path from $i$ to $j$
in the adjacency quiver of $A$. With two indices, a path of length zero from an index to itself
can be replaced by a path through a second index. -/
theorem isPatternIrreducible_iff_nonempty_path [Nontrivial n] :
    A.IsPatternIrreducible ↔ letI := A.adjQuiver; ∀ i j : n, Nonempty (Path i j) := by
  let _ : Quiver n := A.adjQuiver
  refine ⟨fun h i j => ?_, fun h => ?_⟩
  · obtain ⟨p, -⟩ := h.exists_pos_length_path i j
    exact ⟨p⟩
  refine isPatternIrreducible_iff.2 fun i j => ?_
  obtain ⟨k, hk⟩ := exists_ne i
  obtain ⟨p⟩ := h i k
  obtain ⟨q⟩ := h k j
  refine ⟨p.comp q, ?_⟩
  rcases Nat.eq_zero_or_pos p.length with hp | hp
  · exact absurd (Path.eq_of_length_zero p hp) (Ne.symm hk)
  · simpa [Path.length_comp] using Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _)

/-- Let $A$ be a real square matrix with $a_{ij} \ge 0$ for all $i$ and $j$. Then $A$ is
pattern-irreducible if and only if it is irreducible in the sense of Mathlib's
`Matrix.IsIrreducible`: for such a matrix the irreducibility of [saad2003iterative] is
Mathlib's. -/
theorem isPatternIrreducible_iff_isIrreducible {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    A.IsPatternIrreducible ↔ A.IsIrreducible := by
  have h : A.map (‖·‖) = A := by
    ext i j
    simp [Real.norm_eq_abs, abs_of_nonneg (hA i j)]
  rw [IsPatternIrreducible, h]

/-- Let $A$ be a square matrix over a normed additive group with a finite index set, and let $|A|$
be the matrix of entrywise norms $(\|a_{ij}\|)$. Then $A$ is pattern-irreducible if and only if
for all indices $i$ and $j$ there is $k > 0$ with $((|A|)^k)_{ij} > 0$. -/
theorem isPatternIrreducible_iff_exists_pow_pos [Fintype n] [DecidableEq n] :
    A.IsPatternIrreducible ↔ ∀ i j, ∃ k > 0, 0 < ((A.map (‖·‖)) ^ k) i j :=
  isIrreducible_iff_exists_pow_pos fun i j => by
    rw [map_apply]
    exact norm_nonneg _

/-- The matrix $A^T$ is pattern-irreducible if and only if $A$ is pattern-irreducible: transposition
reverses every arrow of the adjacency quiver. -/
@[simp] theorem isPatternIrreducible_transpose_iff :
    Aᵀ.IsPatternIrreducible ↔ A.IsPatternIrreducible := by
  rw [IsPatternIrreducible, IsPatternIrreducible, transpose_map, isIrreducible_transpose_iff]

/-- The relabelling by a permutation $\sigma$, as a map from the adjacency quiver of
$(b_{\sigma(i) \sigma(j)})_{i,j}$ to the adjacency quiver of $B$. -/
private noncomputable abbrev submatrixPrefunctor (B : Matrix n n R) (σ : Equiv.Perm n) :
    @Prefunctor n (B.submatrix σ σ).adjQuiver n B.adjQuiver :=
  @Prefunctor.mk n (B.submatrix σ σ).adjQuiver n B.adjQuiver σ fun {_ _} e => e

private theorem isPatternIrreducible_of_submatrix {σ : Equiv.Perm n}
    (h : (A.submatrix σ σ).IsPatternIrreducible) : A.IsPatternIrreducible := by
  have key : ∀ i j : n, letI := A.adjQuiver; ∃ q : Path (σ i) (σ j), 0 < q.length := by
    intro i j
    obtain ⟨p, hp⟩ := h.exists_pos_length_path i j
    refine ⟨@Prefunctor.mapPath n (A.submatrix σ σ).adjQuiver n A.adjQuiver
      (submatrixPrefunctor A σ) i j p, ?_⟩
    rwa [@Prefunctor.length_mapPath n n (A.submatrix σ σ).adjQuiver A.adjQuiver
      (submatrixPrefunctor A σ) i j p]
  refine isPatternIrreducible_iff.2 fun a b => ?_
  have h' := key (σ.symm a) (σ.symm b)
  rwa [σ.apply_symm_apply, σ.apply_symm_apply] at h'

/-- If $A$ is pattern-irreducible and $\sigma$ is a permutation of the indices, then
$(a_{\sigma(i) \sigma(j)})_{i,j}$ is pattern-irreducible. -/
theorem IsPatternIrreducible.submatrix (h : A.IsPatternIrreducible) (σ : Equiv.Perm n) :
    (A.submatrix σ σ).IsPatternIrreducible := by
  refine isPatternIrreducible_of_submatrix (σ := σ⁻¹) ?_
  have h' : (A.submatrix σ σ).submatrix (⇑σ⁻¹) (⇑σ⁻¹) = A := by
    rw [submatrix_submatrix, ← Equiv.Perm.coe_mul, mul_inv_cancel]
    simp
  rwa [h']

/-! ### Reducibility is a block triangular form -/

variable [Fintype n]

/-- The core of the characterization of reducibility in [saad2003iterative]. Let $A$ be a square
matrix over a normed additive group with a finite index set of at least two elements. Then $A$
is not pattern-irreducible if and only if there is a set $s$ of indices with $s \neq \emptyset$
and $s$ not the whole index set, such that $a_{ij} = 0$ for all $i \in s$ and $j \notin s$. In
matrix terms, $A$ is already block triangular for the split of the indices into $s$ and its
complement.

The hypothesis of at least two indices is necessary. Irreducibility asks for a path of
*positive* length between every pair of indices, so the $1 \times 1$ zero matrix is reducible,
but its index set has no nonempty proper subset. -/
theorem not_isPatternIrreducible_iff_exists_forall_apply_eq_zero [Nontrivial n] :
    ¬ A.IsPatternIrreducible ↔
      ∃ s : Finset n, s.Nonempty ∧ s ≠ Finset.univ ∧ ∀ i ∈ s, ∀ j ∉ s, A i j = 0 := by
  classical
  let _ : Quiver n := A.adjQuiver
  constructor
  · intro h
    obtain ⟨i, hi⟩ : ∃ i : n, ¬ ∀ j : n, ∃ p : Path i j, 0 < p.length := by
      by_contra hc
      refine h (isPatternIrreducible_iff.2 fun i j => ?_)
      by_contra hp
      exact hc ⟨i, fun hall => hp (hall j)⟩
    obtain ⟨j, hj⟩ : ∃ j : n, ¬ ∃ p : Path i j, 0 < p.length := by
      by_contra hc
      refine hi fun j => ?_
      by_contra hp
      exact hc ⟨j, hp⟩
    set s : Finset n := {k ∈ Finset.univ | ∃ p : Path i k, 0 < p.length} with hs
    have hmem : ∀ k : n, k ∈ s ↔ ∃ p : Path i k, 0 < p.length := by
      intro k
      simp [hs]
    have hclosed : ∀ k ∈ s, ∀ l : n, A k l ≠ 0 → l ∈ s := by
      intro k hk l hkl
      obtain ⟨p, hp⟩ := (hmem k).1 hk
      exact (hmem l).2 ⟨p.cons (adjHom hkl), by simp [Path.length_cons]⟩
    by_cases hne : s.Nonempty
    · refine ⟨s, hne, fun hsu => hj ((hmem j).1 (hsu ▸ Finset.mem_univ j)), fun k hk l hl => ?_⟩
      by_contra hkl
      exact hl (hclosed k hk l hkl)
    · refine ⟨{i}, Finset.singleton_nonempty i, ?_, fun k hk l _ => ?_⟩
      · obtain ⟨b, hb⟩ := exists_ne i
        exact fun hsu => hb (Finset.mem_singleton.1 (hsu ▸ Finset.mem_univ b))
      · rw [Finset.mem_singleton] at hk
        subst hk
        by_contra hkl
        exact hne ⟨l, (hmem l).2 ⟨Path.nil.cons (adjHom hkl), by simp [Path.length_cons]⟩⟩
  · rintro ⟨s, ⟨i, hi⟩, hsu, hzero⟩ hirr
    obtain ⟨j, hj⟩ : ∃ j : n, j ∉ s := by
      by_contra hc
      exact hsu (Finset.eq_univ_iff_forall.2 (by simpa using hc))
    have hstay : ∀ (k : n) (q : Path i k), k ∈ s := by
      intro k q
      induction q with
      | nil => exact hi
      | cons _ e ih =>
        by_contra hc
        exact apply_ne_zero_of_adjHom e (hzero _ ih _ hc)
    obtain ⟨p, -⟩ := hirr.exists_pos_length_path i j
    exact hj (hstay j p)

/-- The characterization of irreducibility of [saad2003iterative], §3.3.4. Let $A$ be a square
matrix over a normed additive group with a finite index set of at least two elements. Then $A$
is pattern-irreducible if and only if no symmetric permutation puts it in block triangular form:
for every permutation $\sigma$ and every set $s$ of indices with $s \neq \emptyset$ and $s$ not
the whole index set, there are $i \in s$ and $j \notin s$ with $a_{\sigma(i) \sigma(j)} \neq 0$.

The negation, `Matrix.not_isPatternIrreducible_iff_exists_submatrix_blockTriangular`, is the
form that the source states. Neither form says anything about the finer Frobenius normal form,
whose diagonal blocks are the strongly connected components in a topological order. -/
theorem isPatternIrreducible_iff_forall_submatrix_not_blockTriangular [Nontrivial n] :
    A.IsPatternIrreducible ↔
      ∀ (σ : Equiv.Perm n) (s : Finset n), s.Nonempty → s ≠ Finset.univ →
        ∃ i ∈ s, ∃ j ∉ s, (A.submatrix σ σ) i j ≠ 0 := by
  constructor
  · intro h σ s hs hsu
    by_contra hc
    refine not_isPatternIrreducible_iff_exists_forall_apply_eq_zero.2
      ⟨s, hs, hsu, fun i hi j hj => ?_⟩ (h.submatrix σ)
    by_contra hij
    exact hc ⟨i, hi, j, hj, hij⟩
  · intro h
    by_contra hc
    obtain ⟨s, hs, hsu, hzero⟩ := not_isPatternIrreducible_iff_exists_forall_apply_eq_zero.1 hc
    obtain ⟨i, hi, j, hj, hij⟩ := h 1 s hs hsu
    exact hij (by simpa using hzero i hi j hj)

/-- The characterization of reducibility of [saad2003iterative], §3.3.4, in the words of the source.
Let $A$ be a square matrix over a normed additive group with a finite index set of at least two
elements. Then $A$ is not pattern-irreducible if and only if there are a permutation $\sigma$ of
the indices and a set $s$ of indices with $s \neq \emptyset$ and $s$ not the whole index set,
such that $a_{\sigma(i) \sigma(j)} = 0$ for all $i \in s$ and $j \notin s$. That is, a symmetric
permutation puts $A$ in block triangular form. -/
theorem not_isPatternIrreducible_iff_exists_submatrix_blockTriangular [Nontrivial n] :
    ¬ A.IsPatternIrreducible ↔
      ∃ (σ : Equiv.Perm n) (s : Finset n), s.Nonempty ∧ s ≠ Finset.univ ∧
        ∀ i ∈ s, ∀ j ∉ s, (A.submatrix σ σ) i j = 0 := by
  rw [not_isPatternIrreducible_iff_exists_forall_apply_eq_zero]
  refine ⟨fun ⟨s, hs, hsu, hzero⟩ => ⟨1, s, hs, hsu, fun i hi j hj => by
    simpa using hzero i hi j hj⟩, fun ⟨σ, s, hs, hsu, hzero⟩ => ?_⟩
  by_contra hc
  have h : A.IsPatternIrreducible := by
    by_contra h'
    exact hc (not_isPatternIrreducible_iff_exists_forall_apply_eq_zero.1 h')
  obtain ⟨i, hi, j, hj, hij⟩ :=
    isPatternIrreducible_iff_forall_submatrix_not_blockTriangular.1 h σ s hs hsu
  exact hij (hzero i hi j hj)

end Irreducible

end Matrix
