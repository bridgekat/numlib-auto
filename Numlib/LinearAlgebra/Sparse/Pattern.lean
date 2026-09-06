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

/-!
# The pattern of a matrix and the graphs it defines

The *pattern* of a square matrix is the set of positions where it is nonzero, and the graph of the
pattern is what the sparse-matrix reorderings of [saad2003iterative] §3.2–3.3 act on. Three carriers
are needed, because the book uses all three:

* `Matrix.adjDigraph A : Digraph n` has an arrow `i ⟶ j` exactly when `A i j ≠ 0`. This is
  [saad2003iterative] adjacency graph: it is *directed*, and it *has a self-loop* at every nonzero
  diagonal entry, so `SimpleGraph` is the wrong carrier for it.
* `Matrix.adjGraph A : SimpleGraph n` is the symmetrized, loopless graph — `i` and `j` are adjacent
  when `i ≠ j` and one of `A i j`, `A j i` is nonzero. This is the graph the reorderings of §3.3.3
  act on, and for a matrix with a symmetric pattern it carries the same information as the digraph
  off the diagonal (`Matrix.adjGraph_adj_iff_of_isSymm`).
* `Matrix.adjQuiver A : Quiver n` is the same relation once more, in the shape Mathlib's path API
  consumes, since `Digraph` has no walks. It is `Matrix.toQuiver` of the entrywise norm, so it is
  *definitionally* the quiver of Mathlib's `Matrix.IsIrreducible`, and no path has to be transported
  between the two.

A symmetric permutation is a relabelling of all three: `Matrix.adjDigraph_submatrix_adj` and its
packaged form `Matrix.adjGraphIso`. A nonsymmetric one is not, which is the book's warning and the
reason its reorderings are always `A.submatrix σ σ`.

## Irreducibility

`Matrix.IsPatternIrreducible A` is [saad2003iterative] irreducibility (§3.3.4): the adjacency
digraph is strongly connected. It is defined as `Matrix.IsIrreducible (A.map ‖·‖)`, because
Mathlib's `Matrix.IsIrreducible` is stated for entrywise nonnegative matrices only, while
[saad2003iterative] notion applies to an arbitrary matrix; the entrywise norm is nonnegative and
vanishes exactly where the matrix does, so it carries an arbitrary pattern into Mathlib's setting.
For an entrywise nonnegative real matrix the two agree
(`Matrix.isPatternIrreducible_iff_isIrreducible`).

The theorem of the section is the reducibility characterization
`Matrix.isPatternIrreducible_iff_forall_submatrix_not_blockTriangular`: a matrix fails to be
pattern-irreducible exactly when a symmetric permutation puts it in block triangular form. It needs
`[Nontrivial n]`, and genuinely so: irreducibility asks for a path of *positive* length between
every pair of indices, so the `1 × 1` zero matrix is reducible while its index type has no proper
nonempty subset to split. The full Frobenius normal form — the diagonal blocks are the strongly
connected components, in a topological order — is not proved here; it needs a
strongly-connected-component and topological-sort API for digraphs that Mathlib does not have.

## The pattern of a product

Every claim of the book about the pattern of a product assumes away numerical cancellation. The
unconditional half is `Matrix.exists_apply_ne_zero_of_mul_apply_ne_zero`: a nonzero entry of `A B`
forces a nonzero entry of `A` and one of `B` in the matching positions, hence
`Matrix.exists_path_length_of_pow_apply_ne_zero`, a nonzero entry of `A ^ k` forces a path of length
`k` in the adjacency quiver. The converse is false by cancellation and true for entrywise
nonnegative matrices, where it is `Matrix.mul_apply_pos_of_pos_of_pos` here and Mathlib's
`Matrix.pow_apply_pos_iff_nonempty_path` for powers.
-/

open Quiver

namespace Matrix

variable {n R S : Type*}

/-! ### The adjacency digraph, graph and quiver of a pattern -/

section Zero

variable [Zero R] [Zero S]

/-- [saad2003iterative] adjacency graph of a square matrix: the digraph on the index type with an
arrow `i ⟶ j` exactly when `A i j ≠ 0`. It is directed, and it has a self-loop at every nonzero
diagonal entry. -/
def adjDigraph (A : Matrix n n R) : Digraph n where
  Adj i j := A i j ≠ 0

/-- The arrows of the adjacency digraph are the nonzero entries. -/
@[simp]
theorem adjDigraph_adj {A : Matrix n n R} {i j : n} : A.adjDigraph.Adj i j ↔ A i j ≠ 0 := Iff.rfl

/-- Transposing a matrix reverses the arrows of its adjacency digraph. -/
@[simp]
theorem adjDigraph_transpose_adj {A : Matrix n n R} {i j : n} :
    Aᵀ.adjDigraph.Adj i j ↔ A.adjDigraph.Adj j i := Iff.rfl

/-- The adjacency digraph only sees the pattern, so an entrywise map that vanishes exactly at zero —
the norm, or the inclusion of the reals in the complexes — leaves it unchanged. -/
theorem adjDigraph_map (A : Matrix n n R) (f : R → S) (hf : ∀ x, f x = 0 ↔ x = 0) :
    (A.map f).adjDigraph = A.adjDigraph := by
  ext i j
  simp [adjDigraph, hf]

/-- The undirected, loopless graph of the pattern of a square matrix: `i` and `j` are adjacent when
`i ≠ j` and at least one of `A i j`, `A j i` is nonzero. This is the graph the sparse-matrix
reorderings act on. -/
def adjGraph (A : Matrix n n R) : SimpleGraph n := SimpleGraph.fromRel fun i j => A i j ≠ 0

/-- The edges of the pattern graph: distinct indices carrying a nonzero entry one way or the other.
-/
@[simp]
theorem adjGraph_adj {A : Matrix n n R} {i j : n} :
    A.adjGraph.Adj i j ↔ i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0) :=
  SimpleGraph.fromRel_adj _ _ _

/-- If the pattern of `A` is symmetric then off the diagonal the undirected graph and the adjacency
digraph carry the same information. -/
theorem adjGraph_adj_iff_of_forall_ne_zero {A : Matrix n n R}
    (hA : ∀ i j, A i j ≠ 0 → A j i ≠ 0) {i j : n} :
    A.adjGraph.Adj i j ↔ i ≠ j ∧ A.adjDigraph.Adj i j := by
  simp only [adjGraph_adj, adjDigraph_adj, and_congr_right_iff]
  exact fun _ => ⟨fun h => h.elim id fun h' => hA _ _ h', Or.inl⟩

/-- For a symmetric matrix, off the diagonal the undirected graph and the adjacency digraph carry
the same information. -/
theorem adjGraph_adj_iff_of_isSymm {A : Matrix n n R} (hA : A.IsSymm) {i j : n} :
    A.adjGraph.Adj i j ↔ i ≠ j ∧ A.adjDigraph.Adj i j :=
  adjGraph_adj_iff_of_forall_ne_zero fun i j h => by rwa [hA.apply]

end Zero

section Quiver

variable [Norm R]

/-- The pattern of a square matrix as a quiver, with an arrow `i ⟶ j` for every nonzero entry.

It is defined as `Matrix.toQuiver` of the entrywise norm, so that it is *definitionally* the quiver
Mathlib's `Matrix.IsIrreducible` is stated over; `Matrix.nonempty_adjQuiver_hom_iff` and
`Matrix.adjHom` are the dictionary to `Matrix.adjDigraph`. A quiver is needed beside the digraph
only because `Digraph` has no walks in Mathlib. -/
@[instance_reducible]
noncomputable def adjQuiver (A : Matrix n n R) : Quiver n := (A.map (‖·‖)).toQuiver

end Quiver

section Normed

variable [NormedAddCommGroup R] {A : Matrix n n R}

/-- The arrows of the adjacency quiver are the nonzero entries, so it carries the same relation as
`Matrix.adjDigraph`. -/
@[simp]
theorem nonempty_adjQuiver_hom_iff {i j : n} :
    Nonempty (@Quiver.Hom n A.adjQuiver i j) ↔ A i j ≠ 0 :=
  ⟨fun ⟨e⟩ => norm_pos_iff.1 e.down, fun h => ⟨PLift.up (norm_pos_iff.2 h)⟩⟩

/-- The arrow of the adjacency quiver carried by a nonzero entry. -/
def adjHom {i j : n} (h : A i j ≠ 0) : @Quiver.Hom n A.adjQuiver i j :=
  PLift.up (norm_pos_iff.2 h)

/-- An arrow of the adjacency quiver witnesses a nonzero entry. -/
theorem apply_ne_zero_of_adjHom {i j : n} (e : @Quiver.Hom n A.adjQuiver i j) : A i j ≠ 0 :=
  norm_pos_iff.1 e.down

/-- A prefunctor preserves the length of a path. -/
private theorem length_mapPath {U W : Type*} [Quiver U] [Quiver W] (F : U ⥤q W) {a b : U}
    (p : Path a b) : (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [Prefunctor.mapPath_cons, Path.length_cons, ih]

end Normed

/-! ### Symmetric permutations are relabellings -/

section Submatrix

variable [Zero R]

/-- [saad2003iterative] §3.3.2: a symmetric permutation of a matrix is a relabelling of its
adjacency digraph. The statement is definitional. -/
theorem adjDigraph_submatrix_adj (A : Matrix n n R) (σ : Equiv.Perm n) (i j : n) :
    (A.submatrix σ σ).adjDigraph.Adj i j ↔ A.adjDigraph.Adj (σ i) (σ j) := Iff.rfl

/-- A symmetric permutation of a matrix is a relabelling of its undirected pattern graph. -/
def adjGraphIso (A : Matrix n n R) (σ : Equiv.Perm n) :
    (A.submatrix σ σ).adjGraph ≃g A.adjGraph where
  toEquiv := σ
  map_rel_iff' := by
    intro i j
    simp [adjGraph_adj, σ.injective.ne_iff]

/-- The relabelling `Matrix.adjGraphIso` acts by the permutation it is built from. -/
@[simp]
theorem adjGraphIso_apply (A : Matrix n n R) (σ : Equiv.Perm n) (i : n) :
    adjGraphIso A σ i = σ i := rfl

/-- The undirected form of `Matrix.adjDigraph_submatrix_adj`. -/
@[simp]
theorem adjGraph_submatrix_adj (A : Matrix n n R) (σ : Equiv.Perm n) (i j : n) :
    (A.submatrix σ σ).adjGraph.Adj i j ↔ A.adjGraph.Adj (σ i) (σ j) :=
  ((adjGraphIso A σ).map_adj_iff).symm

/-- A symmetric permutation preserves colourability of the pattern graph. -/
theorem colorable_adjGraph_submatrix_iff (A : Matrix n n R) (σ : Equiv.Perm n) {k : ℕ} :
    (A.submatrix σ σ).adjGraph.Colorable k ↔ A.adjGraph.Colorable k :=
  ⟨fun h => SimpleGraph.Colorable.of_hom (adjGraphIso A σ).symm.toHom h,
    fun h => SimpleGraph.Colorable.of_hom (adjGraphIso A σ).toHom h⟩

/-- A symmetric permutation preserves connectedness of the pattern graph. -/
theorem preconnected_adjGraph_submatrix_iff (A : Matrix n n R) (σ : Equiv.Perm n) :
    (A.submatrix σ σ).adjGraph.Preconnected ↔ A.adjGraph.Preconnected :=
  (adjGraphIso A σ).preconnected_iff

end Submatrix

section PermMatrix

variable [Fintype n] [DecidableEq n] [NonAssocSemiring R]

/-- [saad2003iterative] `P A Pᵀ` form of a symmetric permutation, for `P` the permutation matrix of
`σ`. -/
theorem submatrix_eq_permMatrix_mul_mul_transpose (A : Matrix n n R) (σ : Equiv.Perm n) :
    A.submatrix σ σ = σ.permMatrix R * A * (σ.permMatrix R)ᵀ := by
  rw [transpose_permMatrix]
  rw [show σ.permMatrix R = σ.toPEquiv.toMatrix from rfl,
    show (σ⁻¹).permMatrix R = (σ⁻¹).toPEquiv.toMatrix from rfl,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix]
  rfl

end PermMatrix

/-! ### The pattern of a product -/

section Mul

variable [Fintype n]

/-- The pattern of a product is contained in the composite of the patterns: a nonzero entry of `A *
B` forces matching nonzero entries of `A` and of `B`. No hypothesis is needed for this direction;
the converse fails by cancellation. -/
theorem exists_apply_ne_zero_of_mul_apply_ne_zero [NonUnitalNonAssocSemiring R]
    {A B : Matrix n n R} {i j : n} (h : (A * B) i j ≠ 0) : ∃ k, A i k ≠ 0 ∧ B k j ≠ 0 := by
  by_contra! hc
  refine h ?_
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases eq_or_ne (A i k) 0 with hk | hk
  · simp [hk]
  · simp [hc k hk]

/-- The converse, for entrywise nonnegative matrices, where no cancellation can happen: a nonzero
entry of `A` and a matching nonzero entry of `B` force a nonzero entry of `A * B`.

[saad2003iterative] Problem P-3.5, that the patterns of `A` and of `B` are contained in that of `A *
B` when both have a nonzero diagonal, is this at `k = j` and at `k = i`. -/
theorem mul_apply_pos_of_pos_of_pos [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    {A B : Matrix n n R} (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) {i j k : n}
    (h₁ : 0 < A i k) (h₂ : 0 < B k j) : 0 < (A * B) i j := by
  rw [mul_apply]
  exact Finset.sum_pos' (fun l _ => mul_nonneg (hA i l) (hB l j))
    ⟨k, Finset.mem_univ k, mul_pos h₁ h₂⟩

/-- A nonzero entry of `A ^ k` forces a path of length `k` in the adjacency quiver:
[saad2003iterative] §3.2.1, in the direction that needs no hypothesis. -/
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

/-! ### Irreducibility of a pattern -/

section Irreducible

/-- [saad2003iterative] irreducibility of an arbitrary square matrix over a normed additive group:
the adjacency digraph is strongly connected, in the sense that any two indices are joined by a path
of positive length in `Matrix.adjQuiver`.

It is `Matrix.IsIrreducible` of the entrywise norm, which is nonnegative and vanishes exactly where
the matrix does; Mathlib's predicate is available only for entrywise nonnegative matrices, and this
is the composite that carries an arbitrary pattern into it. -/
def IsPatternIrreducible [Norm R] (A : Matrix n n R) : Prop := (A.map (‖·‖)).IsIrreducible

variable [NormedAddCommGroup R] {A : Matrix n n R}

/-- Pattern irreducibility unfolded: every ordered pair of indices is joined by a path of positive
length in the adjacency quiver. -/
theorem isPatternIrreducible_iff :
    A.IsPatternIrreducible ↔
      letI := A.adjQuiver; ∀ i j : n, ∃ p : Path i j, 0 < p.length := by
  refine ⟨fun h => h.connected, fun h => ⟨fun i j => ?_, h⟩⟩
  rw [map_apply]
  exact norm_nonneg _

/-- The path of positive length that pattern irreducibility provides. -/
theorem IsPatternIrreducible.exists_pos_length_path (h : A.IsPatternIrreducible) (i j : n) :
    letI := A.adjQuiver; ∃ p : Path i j, 0 < p.length := isPatternIrreducible_iff.1 h i j

/-- On at least two indices, pattern irreducibility is plain strong connectivity of the adjacency
quiver: a path joining an index to itself may then be routed through a second index. -/
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

/-- For an entrywise nonnegative real matrix, [saad2003iterative] irreducibility is Mathlib's. -/
theorem isPatternIrreducible_iff_isIrreducible {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    A.IsPatternIrreducible ↔ A.IsIrreducible := by
  have h : A.map (‖·‖) = A := by
    ext i j
    simp [Real.norm_eq_abs, abs_of_nonneg (hA i j)]
  rw [IsPatternIrreducible, h]

/-- Relabelling by a permutation carries paths of the pattern quiver of `B.submatrix σ σ` to paths
of the pattern quiver of `B`. -/
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
    rwa [@length_mapPath n n (A.submatrix σ σ).adjQuiver A.adjQuiver
      (submatrixPrefunctor A σ) i j p]
  refine isPatternIrreducible_iff.2 fun a b => ?_
  have h' := key (σ.symm a) (σ.symm b)
  rwa [σ.apply_symm_apply, σ.apply_symm_apply] at h'

/-- Pattern irreducibility is invariant under a symmetric permutation. -/
theorem IsPatternIrreducible.submatrix (h : A.IsPatternIrreducible) (σ : Equiv.Perm n) :
    (A.submatrix σ σ).IsPatternIrreducible := by
  refine isPatternIrreducible_of_submatrix (σ := σ⁻¹) ?_
  have h' : (A.submatrix σ σ).submatrix (⇑σ⁻¹) (⇑σ⁻¹) = A := by
    rw [submatrix_submatrix, ← Equiv.Perm.coe_mul, mul_inv_cancel]
    simp
  rwa [h']

/-! #### Reducibility is a block triangular form -/

variable [Fintype n]

/-- The core of [saad2003iterative] reducibility characterization: a matrix on at least two indices
fails to be pattern-irreducible exactly when the indices split into a proper nonempty part `s` and
its complement with every entry from `s` to the complement zero — in matrix terms, exactly when `A`
is already in block triangular form for that split.

`[Nontrivial n]` is necessary: irreducibility asks for a path of *positive* length between every
pair of indices, so the `1 × 1` zero matrix is reducible while its index type has no proper nonempty
subset. -/
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

/-- [saad2003iterative] §3.3.4: a matrix on at least two indices is pattern-irreducible exactly when
no symmetric permutation puts it in block triangular form — for every permutation and every proper
nonempty set of indices, some entry leads out of the set.

The negation, `Matrix.not_isPatternIrreducible_iff_exists_submatrix_blockTriangular`, is the form
the book states. Neither says anything about the finer Frobenius normal form, whose diagonal blocks
are the strongly connected components in a topological order. -/
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

/-- [saad2003iterative] §3.3.4 in the book's own words: a matrix on at least two indices fails to be
pattern-irreducible exactly when a symmetric permutation puts it in block triangular form. -/
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
