/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.ENat.Lattice
import Numlib.Combinatorics.SimpleGraph.Paths
import Numlib.LinearAlgebra.Sparse.Pattern
import Numlib.Preconditioner.ILU

/-!
# The level of fill and fill-paths

The static pattern of the incomplete factorization $\mathrm{ILU}(p)$ keeps the positions whose
*level of fill* is at most $p$ ([saad2003iterative], §10.3.3). For a square matrix $A$ of order $n$,
the level is $0$ at the nonzero entries of $A$ and on the diagonal, and $\infty$ elsewhere
(Definition 10.5). The elimination of the pivot $k$ lowers the level of every position $(i, j)$ with
$i, j > k$ to
$$\operatorname{lev}_{ij} := \min\{\operatorname{lev}_{ij}, \operatorname{lev}_{ik} +
  \operatorname{lev}_{kj} + 1\},$$
which is the recurrence (10.17). The zero pattern of $\mathrm{ILU}(p)$ is the set of positions whose
final level exceeds $p$. For $p = 0$ it is the zero pattern of $\mathrm{ILU}(0)$.

The level of fill has a reading in the adjacency graph of $A$. A *fill-path* between $i$ and $j$ is
a path in this graph whose interior vertices are all numbered below both $i$ and $j$. For a matrix
with a symmetric pattern, the final level of fill at an off-diagonal position $(i, j)$ is $p$ if and
only if $p + 1$ is the least length of a fill-path between $i$ and $j$ (Theorem 10.7 of
[saad2003iterative]). The level is finite, that is, complete Gaussian elimination fills the
position, if and only if a fill-path exists. This is the fill-path theorem of Rose and Tarjan
(Theorem 10.6 of [saad2003iterative]).

## Main definitions

* `Matrix.initialLevel`: the initial level of fill, $0$ on the pattern of $A$ and on the diagonal
  and $\infty$ elsewhere.
* `Matrix.levelOfFill`: the level of fill after $k$ elimination steps, defined by the recurrence
  (10.17).
* `Matrix.levelPattern`: the zero pattern of $\mathrm{ILU}(p)$.
* `Matrix.IsFillPath`: a fill-path in the adjacency graph.

## Main results

* `Matrix.levelPattern_zero`: the pattern of $\mathrm{ILU}(0)$ is the off-diagonal zero pattern of
  $A$.
* `Matrix.levelOfFill_eq_iff_isLeast`: for a symmetric pattern, the final level at $(i, j)$ with
  $i \neq j$ is $p$ if and only if $p + 1$ is the least length of a fill-path between $i$ and $j$.
* `Matrix.levelOfFill_ne_top_iff`: for a symmetric pattern, the final level at $(i, j)$ with
  $i \neq j$ is finite if and only if a fill-path between $i$ and $j$ exists.

## Implementation notes

* The index type is `Fin n`, because the recurrence eliminates the pivots in their natural order.
  Indices start at $0$. The entries of the matrix are in any type with a zero.
* Levels are in `ℕ∞`, with `⊤` for the level $\infty$.
* `Matrix.levelOfFill A k` is the level after the pivots $0, \dots, k - 1$ have been eliminated, and
  `Matrix.levelOfFill A n` is the final level.
* The adjacency graph is `Matrix.adjGraph`: two distinct indices $i$ and $j$ are adjacent when
  $a_{ij} \neq 0$ or $a_{ji} \neq 0$.
* No separate symbolic model of the elimination is needed: the recurrence (10.17), read for
  finiteness, is that model.
-/

namespace Matrix

variable {n : ℕ} {R : Type*} [Zero R]

open scoped Classical in
/-- The **initial level of fill** (Definition 10.5 of [saad2003iterative]):
$\operatorname{lev}_{ij} = 0$ if $a_{ij} \neq 0$ or $i = j$, and
$\operatorname{lev}_{ij} = \infty$ otherwise. -/
noncomputable def initialLevel (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : ℕ∞ :=
  if A i j ≠ 0 ∨ i = j then 0 else ⊤

/-- The **level of fill after $k$ elimination steps** (the recurrence (10.17) of
[saad2003iterative]). At step $0$ it is the initial level `Matrix.initialLevel`. The elimination
of the pivot $k$ changes the level at $(i, j)$ only when $i > k$ and $j > k$, and then sets
$$\operatorname{lev}^{(k+1)}_{ij} = \min\bigl\{\operatorname{lev}^{(k)}_{ij}, \
  \operatorname{lev}^{(k)}_{ik} + \operatorname{lev}^{(k)}_{kj} + 1\bigr\}.$$

The condition $i, j > k$ is the range of the two loops in line 5 of Algorithm 10.2 of
[saad2003iterative]. Positions outside this range do not change at step $k$. So
`levelOfFill A (min i j) i j` is already the level after all the updates (10.17)
(`Matrix.levelOfFill_eq_of_min_le`), and `levelOfFill A n` is this final level at every
position.

The book writes the update in place inside Algorithm 10.2. The step index makes it a function.
The condition $i, j > k$ is necessary. Without it, the recurrence is the Floyd–Warshall
algorithm, which computes the distance in the adjacency graph and not the length of a fill-path,
and it reports fill at positions that Gaussian elimination never changes. For example, take the
symmetric pattern with the edges $0 - 2$ and $1 - 2$ and no edge $0 - 1$. A step at the pivot
$2$ without the condition gives $\operatorname{lev}_{01} = 1$, but row $0$ is never modified.
The reading of (10.17) in the book contains the condition: the level at step $k - 1$ is given by
a shortest path through $V_{k-1} = \{1, \dots, k - 1\}$ between two vertices $i$ and $j$ that
are not in $V_{k-1}$. This reading is `Matrix.levelOfFill_eq_iff_isLeast`. -/
noncomputable def levelOfFill (A : Matrix (Fin n) (Fin n) R) : ℕ → Fin n → Fin n → ℕ∞
  | 0, i, j => initialLevel A i j
  | k + 1, i, j =>
    if h : k < (i : ℕ) ∧ k < (j : ℕ) then
      min (levelOfFill A k i j)
        (levelOfFill A k i ⟨k, h.1.trans i.isLt⟩ + levelOfFill A k ⟨k, h.1.trans i.isLt⟩ j + 1)
    else levelOfFill A k i j

/-- Before any elimination, the level of fill is the initial level. -/
@[simp]
theorem levelOfFill_zero (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    levelOfFill A 0 i j = initialLevel A i j := rfl

/-- The recurrence (10.17) at step $k + 1$: if $k < i$ and $k < j$, then
$\operatorname{lev}^{(k+1)}_{ij} = \min\{\operatorname{lev}^{(k)}_{ij},
\operatorname{lev}^{(k)}_{ik} + \operatorname{lev}^{(k)}_{kj} + 1\}$, and otherwise
$\operatorname{lev}^{(k+1)}_{ij} = \operatorname{lev}^{(k)}_{ij}$. -/
theorem levelOfFill_succ (A : Matrix (Fin n) (Fin n) R) (k : ℕ) (i j : Fin n) :
    levelOfFill A (k + 1) i j =
      if h : k < (i : ℕ) ∧ k < (j : ℕ) then
        min (levelOfFill A k i j)
          (levelOfFill A k i ⟨k, h.1.trans i.isLt⟩ + levelOfFill A k ⟨k, h.1.trans i.isLt⟩ j + 1)
      else levelOfFill A k i j := rfl

/-- If $k < i$ and $k < j$, and $K$ is the index with value $k$, then
$\operatorname{lev}^{(k+1)}_{ij} = \min\{\operatorname{lev}^{(k)}_{ij},
\operatorname{lev}^{(k)}_{iK} + \operatorname{lev}^{(k)}_{Kj} + 1\}$. These are the conditions
of line 5 of Algorithm 10.2 of [saad2003iterative]. -/
theorem levelOfFill_succ_eq (A : Matrix (Fin n) (Fin n) R) {k : ℕ} {i j : Fin n}
    (hi : k < (i : ℕ)) (hj : k < (j : ℕ)) (K : Fin n) (hK : (K : ℕ) = k) :
    levelOfFill A (k + 1) i j =
      min (levelOfFill A k i j) (levelOfFill A k i K + levelOfFill A k K j + 1) := by
  have hKeq : K = ⟨k, hi.trans i.isLt⟩ := Fin.ext hK
  rw [hKeq, levelOfFill_succ]
  split_ifs with h
  · rfl
  · exact absurd ⟨hi, hj⟩ h

/-- If $k < i$ and $k < j$, and $K$ is the index with value $k$, then
$\operatorname{lev}^{(k+1)}_{ij} \le \operatorname{lev}^{(k)}_{iK} +
\operatorname{lev}^{(k)}_{Kj} + 1$. -/
theorem levelOfFill_succ_le (A : Matrix (Fin n) (Fin n) R) {k : ℕ} {i j : Fin n}
    (hi : k < (i : ℕ)) (hj : k < (j : ℕ)) (K : Fin n) (hK : (K : ℕ) = k) :
    levelOfFill A (k + 1) i j ≤ levelOfFill A k i K + levelOfFill A k K j + 1 := by
  rw [levelOfFill_succ_eq A hi hj K hK]
  exact min_le_right _ _

/-- If $k < i$ and $k < j$ do not both hold, then $\operatorname{lev}^{(k+1)}_{ij} =
\operatorname{lev}^{(k)}_{ij}$. These are the positions that line 5 of Algorithm 10.2 of
[saad2003iterative] skips. -/
theorem levelOfFill_succ_of_not_lt (A : Matrix (Fin n) (Fin n) R) {k : ℕ} {i j : Fin n}
    (h : ¬(k < (i : ℕ) ∧ k < (j : ℕ))) :
    levelOfFill A (k + 1) i j = levelOfFill A k i j := by
  rw [levelOfFill_succ]
  split_ifs
  rfl

/-- A level of fill never increases during the elimination: $\operatorname{lev}^{(k+1)}_{ij} \le
\operatorname{lev}^{(k)}_{ij}$. -/
theorem levelOfFill_le_succ (A : Matrix (Fin n) (Fin n) R) (k : ℕ) (i j : Fin n) :
    levelOfFill A (k + 1) i j ≤ levelOfFill A k i j := by
  rw [levelOfFill_succ]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- If $k \le m$, then $\operatorname{lev}^{(m)}_{ij} \le \operatorname{lev}^{(k)}_{ij}$. -/
theorem levelOfFill_le_of_le (A : Matrix (Fin n) (Fin n) R) {k m : ℕ} (h : k ≤ m) (i j : Fin n) :
    levelOfFill A m i j ≤ levelOfFill A k i j := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact (levelOfFill_le_succ A m i j).trans ih

/-- If $\min\{i, j\} \le k \le m$, then $\operatorname{lev}^{(m)}_{ij} =
\operatorname{lev}^{(k)}_{ij}$. Thus the level at $(i, j)$ does not change after step
$\min\{i, j\}$, and `levelOfFill A (min i j) i j` is already the level after all the updates
(10.17). -/
theorem levelOfFill_eq_of_min_le (A : Matrix (Fin n) (Fin n) R) {i j : Fin n} {k m : ℕ}
    (hk : min (i : ℕ) (j : ℕ) ≤ k) (hkm : k ≤ m) :
    levelOfFill A m i j = levelOfFill A k i j := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [levelOfFill_succ_of_not_lt A ?_, ih]
    rintro ⟨h1, h2⟩
    exact absurd (lt_min h1 h2) (not_lt.2 (hk.trans hm))

/-- For every $k$, $\operatorname{lev}^{(k)}_{ij} > 0$ if and only if
$\operatorname{lev}^{(0)}_{ij} > 0$, because every update adds $1$ to a sum of levels. Thus a
position that is nonzero in $A$ or on the diagonal keeps level $0$ during the whole elimination,
as the book remarks, and no other position gets level $0$. -/
theorem zero_lt_levelOfFill_iff (A : Matrix (Fin n) (Fin n) R) (k : ℕ) (i j : Fin n) :
    0 < levelOfFill A k i j ↔ 0 < initialLevel A i j := by
  induction k with
  | zero => rw [levelOfFill_zero]
  | succ k ih =>
    rw [levelOfFill_succ]
    split_ifs with h
    · exact ⟨fun hlt => ih.1 (lt_min_iff.1 hlt).1,
        fun hlt => lt_min_iff.2 ⟨ih.2 hlt, lt_of_lt_of_le zero_lt_one le_add_self⟩⟩
    · exact ih

/-- The **zero pattern $P_p$ of $\mathrm{ILU}(p)$** (§10.3.3 and Algorithm 10.5 of
[saad2003iterative]): the set of positions $(i, j)$ whose final level of fill
$\operatorname{lev}^{(n)}_{ij}$ is greater than $p$. -/
noncomputable def levelPattern (A : Matrix (Fin n) (Fin n) R) (p : ℕ) : Set (Fin n × Fin n) :=
  {q | (p : ℕ∞) < levelOfFill A n q.1 q.2}

/-- A diagonal position has level of fill $0$ and is never in the pattern of $\mathrm{ILU}(p)$. So
the existence theorem `Matrix.IsMMatrix.exists_isILU` applies to $\mathrm{ILU}(p)$ for every
$p$. -/
theorem diag_notMem_levelPattern (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i : Fin n) :
    (i, i) ∉ levelPattern A p := by
  intro hq
  have hpos : 0 < levelOfFill A n i i := lt_of_le_of_lt zero_le hq
  rw [zero_lt_levelOfFill_iff, initialLevel, ite_eq_left (Or.inr rfl)] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- The case $p = 0$ gives $\mathrm{ILU}(0)$ (§10.3.3 of [saad2003iterative]): the pattern $P_0$ is
the off-diagonal zero pattern `Matrix.zeroPattern` of $A$, so it is the pattern of
`Matrix.IsILU0`. -/
theorem levelPattern_zero (A : Matrix (Fin n) (Fin n) R) : levelPattern A 0 = A.zeroPattern := by
  ext ⟨i, j⟩
  change ((0 : ℕ) : ℕ∞) < levelOfFill A n i j ↔ (i, j) ∈ A.zeroPattern
  rw [Nat.cast_zero, zero_lt_levelOfFill_iff, Matrix.mem_zeroPattern, initialLevel]
  by_cases h : A i j ≠ 0 ∨ i = j
  · rw [ite_eq_left h]
    simp only [lt_self_iff_false, false_iff, not_and, not_not]
    exact fun h1 => h.resolve_left (not_not_intro h1)
  · rw [ite_eq_right h]
    rw [not_or, not_not] at h
    exact iff_of_true (lt_of_lt_of_le zero_lt_one le_top) ⟨h.1, h.2⟩

/-! ### Fill-paths -/

section FillPath

variable {A : Matrix (Fin n) (Fin n) R}

/-- A **fill-path** between $i$ and $j$ (§10.3.3 of [saad2003iterative]): a path in the adjacency
graph of $A$ such that every vertex other than the endpoints $i$ and $j$ is less than $i$ and
less than $j$.

The graph is `Matrix.adjGraph`, the symmetric graph without loops of the pattern of $A$. For a
symmetric pattern it loses no information off the diagonal
(`Matrix.adjGraph_adj_iff_of_forall_ne_zero`). The symmetry of the pattern is a necessary
hypothesis of the two characterizations below. The level of fill (10.17) is computed from the
directed pattern, so without symmetry the fill-path would also have to be directed. -/
def IsFillPath {i j : Fin n} (w : A.adjGraph.Walk i j) : Prop :=
  w.IsPath ∧ ∀ v ∈ w.support, v ≠ i → v ≠ j → v < i ∧ v < j

/-- A walk in the adjacency graph is a fill-walk if every vertex other than its endpoints $i$ and
$j$ is less than $i$ and less than $j$; unlike a fill-path, it can repeat vertices. -/
private def IsFillWalk {i j : Fin n} (w : A.adjGraph.Walk i j) : Prop :=
  ∀ v ∈ w.support, v ≠ i → v ≠ j → v < i ∧ v < j

/-- For a symmetric pattern, $i$ and $j$ are adjacent in the adjacency graph if and only if
$i \neq j$ and $a_{ij} \neq 0$. -/
private theorem adjGraph_adj_iff (hsymm : A.IsPatternSymm) (i j : Fin n) :
    A.adjGraph.Adj i j ↔ i ≠ j ∧ A i j ≠ 0 :=
  adjGraph_adj_iff_of_forall_ne_zero fun i j => (hsymm i j).1

/-- Half of Theorem 10.7 of [saad2003iterative]: if $i \neq j$, $m \le i$, $m \le j$, and $w$ is a
path between $i$ and $j$ whose interior vertices are all less than $m$, then
$\operatorname{lev}^{(m)}_{ij} + 1 \le \operatorname{length}(w)$. -/
private theorem levelOfFill_add_one_le_length (hsymm : A.IsPatternSymm) :
    ∀ (m : ℕ) {i j : Fin n} (w : A.adjGraph.Walk i j), i ≠ j → w.IsPath →
      (∀ v ∈ w.support, v ≠ i → v ≠ j → (v : ℕ) < m) → m ≤ (i : ℕ) → m ≤ (j : ℕ) →
      levelOfFill A m i j + 1 ≤ (w.length : ℕ∞) := by
  intro m
  induction m with
  | zero =>
    intro i j w hij hp hint _ _
    have hsub : w.support.toFinset ⊆ ({i, j} : Finset (Fin n)) := by
      intro v hv
      rw [List.mem_toFinset] at hv
      by_cases hvi : v = i
      · simp [hvi]
      · by_cases hvj : v = j
        · simp [hvj]
        · exact absurd (hint v hv hvi hvj) (Nat.not_lt_zero _)
    have hcard : w.support.length ≤ 2 := by
      rw [← List.toFinset_card_of_nodup hp.support_nodup]
      exact (Finset.card_le_card hsub).trans
        ((Finset.card_insert_le _ _).trans (by simp))
    rw [SimpleGraph.Walk.length_support] at hcard
    have hpos : w.length ≠ 0 := fun h => hij (SimpleGraph.Walk.eq_of_length_eq_zero h)
    have hlen : w.length = 1 := by omega
    have hadj : A.adjGraph.Adj i j := by
      have h1 : (0 : ℕ) < w.length := by omega
      have h2 := w.adj_getVert_succ h1
      rw [SimpleGraph.Walk.getVert_zero, show (0 : ℕ) + 1 = w.length by omega,
        SimpleGraph.Walk.getVert_length] at h2
      exact h2
    have hlev : levelOfFill A 0 i j = 0 := by
      rw [levelOfFill_zero, initialLevel]
      simp [((adjGraph_adj_iff hsymm i j).1 hadj).2]
    rw [hlev, hlen]
    simp
  | succ m ih =>
    intro i j w hij hp hint hmi hmj
    have hmn : m < n := by omega
    obtain ⟨K, hK⟩ : ∃ K : Fin n, (K : ℕ) = m := ⟨⟨m, hmn⟩, rfl⟩
    have hKlti : K < i := by rw [Fin.lt_def, hK]; omega
    have hKltj : K < j := by rw [Fin.lt_def, hK]; omega
    by_cases hKmem : K ∈ w.support
    · have hKi : K ≠ i := ne_of_lt hKlti
      have hKj : K ≠ j := ne_of_lt hKltj
      have hjnot := SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hKmem hKj.symm
      have hinot := SimpleGraph.Walk.start_notMem_support_dropUntil hp hKmem (Ne.symm hKi)
      have hint1 : ∀ v ∈ (w.takeUntil K hKmem).support, v ≠ i → v ≠ K → (v : ℕ) < m := by
        intro v hv hvi hvK
        have hvw : v ∈ w.support :=
          SimpleGraph.Walk.support_takeUntil_subset_support _ _ hv
        have hvj : v ≠ j := fun h => hjnot (h ▸ hv)
        have hlt := hint v hvw hvi hvj
        have hne : (v : ℕ) ≠ m := fun h => hvK (Fin.ext (h.trans hK.symm))
        omega
      have hint2 : ∀ v ∈ (w.dropUntil K hKmem).support, v ≠ K → v ≠ j → (v : ℕ) < m := by
        intro v hv hvK hvj
        have hvw : v ∈ w.support :=
          SimpleGraph.Walk.support_dropUntil_subset_support _ _ hv
        have hvi : v ≠ i := fun h => hinot (h ▸ hv)
        have hlt := hint v hvw hvi hvj
        have hne : (v : ℕ) ≠ m := fun h => hvK (Fin.ext (h.trans hK.symm))
        omega
      have h1 := ih (w.takeUntil K hKmem) (Ne.symm hKi) (hp.takeUntil hKmem) hint1
        (by omega) (by omega)
      have h2 := ih (w.dropUntil K hKmem) hKj (hp.dropUntil hKmem) hint2 (by omega) (by omega)
      have hlen : (w.takeUntil K hKmem).length + (w.dropUntil K hKmem).length = w.length := by
        conv_rhs => rw [← w.take_spec hKmem]
        rw [SimpleGraph.Walk.length_append]
      have hstep := levelOfFill_succ_le A (i := i) (j := j) (by omega) (by omega) K hK
      calc levelOfFill A (m + 1) i j + 1
          ≤ levelOfFill A m i K + levelOfFill A m K j + 1 + 1 :=
            add_le_add hstep (le_refl (1 : ℕ∞))
        _ = levelOfFill A m i K + 1 + (levelOfFill A m K j + 1) := by ring
        _ ≤ ((w.takeUntil K hKmem).length : ℕ∞) + ((w.dropUntil K hKmem).length : ℕ∞) :=
            add_le_add h1 h2
        _ = (w.length : ℕ∞) := by rw [← Nat.cast_add, hlen]
    · have hint' : ∀ v ∈ w.support, v ≠ i → v ≠ j → (v : ℕ) < m := by
        intro v hv hvi hvj
        have hlt := hint v hv hvi hvj
        have hne : (v : ℕ) ≠ m := fun h => by
          rw [show K = v from Fin.ext (hK.trans h.symm)] at hKmem
          exact hKmem hv
        omega
      exact le_trans (add_le_add (levelOfFill_le_succ A m i j) (le_refl (1 : ℕ∞)))
        (ih w hij hp hint' (by omega) (by omega))

/-- The other half of Theorem 10.7 of [saad2003iterative]: if $i \neq j$ and
$\operatorname{lev}^{(m)}_{ij} = p$ is finite, there is a fill-walk of length $p + 1$ between
$i$ and $j$. -/
private theorem exists_fillWalk_of_levelOfFill (hsymm : A.IsPatternSymm) :
    ∀ (m : ℕ) {i j : Fin n} {p : ℕ}, i ≠ j → levelOfFill A m i j = (p : ℕ∞) →
      ∃ w : A.adjGraph.Walk i j, w.length = p + 1 ∧ IsFillWalk w := by
  intro m
  induction m with
  | zero =>
    intro i j p hij hlev
    rw [levelOfFill_zero, initialLevel] at hlev
    split_ifs at hlev with hcond
    · have hp : p = 0 := by exact_mod_cast hlev.symm
      have hadj : A.adjGraph.Adj i j :=
        (adjGraph_adj_iff hsymm i j).2 ⟨hij, hcond.resolve_right hij⟩
      refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, by simp [hp], ?_⟩
      intro v hv hvi hvj
      have hv' : v = i ∨ v = j := by simpa using hv
      rcases hv' with h | h
      exacts [absurd h hvi, absurd h hvj]
    · exact absurd hlev (by simp)
  | succ m ih =>
    intro i j p hij hlev
    by_cases hguard : m < (i : ℕ) ∧ m < (j : ℕ)
    · obtain ⟨K, hK⟩ : ∃ K : Fin n, (K : ℕ) = m := ⟨⟨m, hguard.1.trans i.isLt⟩, rfl⟩
      rw [levelOfFill_succ_eq A hguard.1 hguard.2 K hK] at hlev
      have hKlti : K < i := by rw [Fin.lt_def, hK]; exact hguard.1
      have hKltj : K < j := by rw [Fin.lt_def, hK]; exact hguard.2
      rcases min_cases (levelOfFill A m i j)
          (levelOfFill A m i K + levelOfFill A m K j + 1) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at hlev
        exact ih hij hlev
      · rw [he] at hlev
        have htop : levelOfFill A m i K + levelOfFill A m K j + 1 ≠ ⊤ := by
          rw [hlev]
          exact ENat.natCast_ne_top p
        have h1 : levelOfFill A m i K ≠ ⊤ := by
          intro h
          rw [h] at htop
          simp at htop
        have h2 : levelOfFill A m K j ≠ ⊤ := by
          intro h
          rw [h] at htop
          simp at htop
        obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 h1
        obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 h2
        rw [← ha, ← hb] at hlev
        have hab : a + b + 1 = p := by exact_mod_cast hlev
        obtain ⟨w1, hw1len, hw1⟩ := ih (Ne.symm (ne_of_lt hKlti)) ha.symm
        obtain ⟨w2, hw2len, hw2⟩ := ih (ne_of_lt hKltj) hb.symm
        refine ⟨w1.append w2, ?_, ?_⟩
        · rw [SimpleGraph.Walk.length_append, hw1len, hw2len]
          omega
        · intro v hv hvi hvj
          rw [SimpleGraph.Walk.support_append, List.mem_append] at hv
          by_cases hvK : v = K
          · exact ⟨hvK ▸ hKlti, hvK ▸ hKltj⟩
          · rcases hv with hv | hv
            · exact ⟨(hw1 v hv hvi hvK).1, lt_trans (hw1 v hv hvi hvK).2 hKltj⟩
            · have hv' : v ∈ w2.support := by
                rw [← SimpleGraph.Walk.cons_tail_support]
                exact List.mem_cons_of_mem _ hv
              exact ⟨lt_trans (hw2 v hv' hvK hvj).1 hKlti, (hw2 v hv' hvK hvj).2⟩
    · rw [levelOfFill_succ_of_not_lt A hguard] at hlev
      exact ih hij hlev

/-- Let $A$ have a symmetric pattern, let $i \neq j$, and let $w$ be a fill-path between $i$ and
$j$. Then
$$\operatorname{lev}^{(n)}_{ij} + 1 \le \operatorname{length}(w).$$
-/
theorem levelOfFill_add_one_le_of_isFillPath (hsymm : A.IsPatternSymm)
    {i j : Fin n} (hij : i ≠ j) {w : A.adjGraph.Walk i j} (hw : IsFillPath w) :
    levelOfFill A n i j + 1 ≤ (w.length : ℕ∞) := by
  rw [levelOfFill_eq_of_min_le A (k := min (i : ℕ) (j : ℕ)) le_rfl
    (le_of_lt (lt_of_le_of_lt (min_le_left _ _) i.isLt))]
  refine levelOfFill_add_one_le_length hsymm _ w hij hw.1 (fun v hv hvi hvj => ?_)
    (min_le_left _ _) (min_le_right _ _)
  exact lt_min (Fin.lt_def.1 (hw.2 v hv hvi hvj).1) (Fin.lt_def.1 (hw.2 v hv hvi hvj).2)

/-- Let $A$ have a symmetric pattern, and let $i \neq j$. If the final level of fill
$\operatorname{lev}^{(n)}_{ij}$ is a natural number $p$, then there is a fill-path of length
exactly $p + 1$ between $i$ and $j$. -/
theorem exists_isFillPath_of_levelOfFill (hsymm : A.IsPatternSymm) {i j : Fin n}
    (hij : i ≠ j) {p : ℕ} (hlev : levelOfFill A n i j = (p : ℕ∞)) :
    ∃ w : A.adjGraph.Walk i j, IsFillPath w ∧ w.length = p + 1 := by
  obtain ⟨w, hwlen, hw⟩ := exists_fillWalk_of_levelOfFill hsymm n hij hlev
  have hpath : IsFillPath w.bypass :=
    ⟨w.bypass_isPath, fun v hv hvi hvj =>
      hw v (SimpleGraph.Walk.support_bypass_subset_support w hv) hvi hvj⟩
  refine ⟨w.bypass, hpath, ?_⟩
  have hle : w.bypass.length ≤ p + 1 := hwlen ▸ w.length_bypass_le_length
  have hge := levelOfFill_add_one_le_of_isFillPath hsymm hij hpath
  rw [hlev] at hge
  have hge' : p + 1 ≤ w.bypass.length := by exact_mod_cast hge
  omega

/-- The **fill-path characterization of the level of fill** (Theorem 10.7 of [saad2003iterative]).
Let $A$ be a square matrix of order $n$ with a symmetric pattern, that is, $a_{ij} \neq 0$ if
and only if $a_{ji} \neq 0$. Let $i \neq j$ and let $p$ be a natural number. Then the final
level of fill at $(i, j)$ is $p$ if and only if $p + 1$ is the least length of a fill-path
between $i$ and $j$:
$$\operatorname{lev}^{(n)}_{ij} = p \iff p + 1 = \min\{\operatorname{length}(w) : w \text{ is a
  fill-path between } i \text{ and } j\}.$$

The minimality is what the proof in the book uses to show that $\operatorname{lev}_{ij}$ cannot
be smaller. The theorem is about the recurrence (10.17), and not about the alternative
recurrence (10.18), which has a different characterization. The symmetry of the pattern lets the
undirected adjacency graph carry the directed information from which (10.17) is computed.

The final level is `Matrix.levelOfFill A n`, the minimum is `IsLeast`, and the pattern symmetry
is `Matrix.IsPatternSymm`. -/
theorem levelOfFill_eq_iff_isLeast (hsymm : A.IsPatternSymm) {i j : Fin n} (hij : i ≠ j)
    (p : ℕ) :
    levelOfFill A n i j = (p : ℕ∞) ↔
      IsLeast {ℓ : ℕ | ∃ w : A.adjGraph.Walk i j, IsFillPath w ∧ w.length = ℓ} (p + 1) := by
  constructor
  · intro hlev
    obtain ⟨w, hw, hwlen⟩ := exists_isFillPath_of_levelOfFill hsymm hij hlev
    refine ⟨⟨w, hw, hwlen⟩, ?_⟩
    rintro ℓ ⟨w', hw', rfl⟩
    have hle := levelOfFill_add_one_le_of_isFillPath hsymm hij hw'
    rw [hlev] at hle
    exact_mod_cast hle
  · rintro ⟨⟨w, hw, hwlen⟩, hmin⟩
    have hub := levelOfFill_add_one_le_of_isFillPath hsymm hij hw
    rw [hwlen] at hub
    have hne : levelOfFill A n i j ≠ ⊤ := by
      intro h
      rw [h] at hub
      simp at hub
    obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.1 hne
    obtain ⟨w', hw', hw'len⟩ := exists_isFillPath_of_levelOfFill hsymm hij hq.symm
    have h1 : p + 1 ≤ q + 1 := hmin ⟨w', hw', hw'len⟩
    have h2 : q + 1 ≤ p + 1 := by
      rw [← hq] at hub
      exact_mod_cast hub
    rw [← hq, show q = p by omega]

/-- The **fill-path theorem** (Theorem 10.6 of [saad2003iterative], after Rose and Tarjan, and
George and Liu). Let $A$ be a square matrix of order $n$ with a symmetric pattern, and let
$i \neq j$. Then the position $(i, j)$ is filled at the end of Gaussian elimination, that is,
its final level of fill is finite, if and only if there is a fill-path between $i$ and $j$.

This is the finiteness part of `Matrix.levelOfFill_eq_iff_isLeast`: the recurrence (10.17), read
for finiteness, is the symbolic elimination. -/
theorem levelOfFill_ne_top_iff (hsymm : A.IsPatternSymm) {i j : Fin n} (hij : i ≠ j) :
    levelOfFill A n i j ≠ ⊤ ↔ ∃ w : A.adjGraph.Walk i j, IsFillPath w := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.1 h
    obtain ⟨w, hw, _⟩ := exists_isFillPath_of_levelOfFill hsymm hij hq.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩ hc
    have hle := levelOfFill_add_one_le_of_isFillPath hsymm hij hw
    rw [hc] at hle
    simp at hle

end FillPath

/-- A position $(i, j)$ is outside the pattern of $\mathrm{ILU}(p)$ for some $p$ if and only if its
final level of fill is finite. -/
theorem exists_notMem_levelPattern_iff (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (∃ p : ℕ, (i, j) ∉ levelPattern A p) ↔ levelOfFill A n i j ≠ ⊤ := by
  constructor
  · rintro ⟨p, hp⟩ hc
    rw [levelPattern, Set.mem_ofPred_eq, hc] at hp
    exact hp (by simp)
  · intro h
    obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.1 h
    refine ⟨q, ?_⟩
    rw [levelPattern, Set.mem_ofPred_eq, ← hq]
    simp

end Matrix
