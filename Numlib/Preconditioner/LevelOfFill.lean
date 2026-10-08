import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.ENat.Lattice
import Numlib.LinearAlgebra.Sparse.Pattern
import Numlib.Preconditioner.ILU

/-!
# The level of fill and fill-paths

The static pattern of the incomplete factorization `ILU(p)` keeps the positions whose *level of
fill* is at most `p` ([saad2003iterative] §10.3.3).  The level starts at `0` on the pattern of `A`
and on the diagonal and at `⊤` elsewhere (`Matrix.initialLevel`, the book's Definition 10.5), and
eliminating the pivot `k` lowers the level of every entry `(i, j)` with `i, j > k` to
`min (lev i j) (lev i k + lev k j + 1)` (`Matrix.levelOfFill A k`, the recurrence (10.17), with
the elimination step as its first argument).  `Matrix.levelPattern A p` is the zero pattern of
`ILU(p)`; `Matrix.levelPattern_zero` identifies `p = 0` with the pattern of `ILU(0)`.

The level of fill has a graph reading.  A *fill-path* between `i` and `j` is a path of the
adjacency graph `Matrix.adjGraph` whose interior vertices are numbered below both endpoints
(`Matrix.IsFillPath`).  For a symmetric pattern (`Matrix.IsPatternSymm`) the final level of fill
at an off-diagonal position is `p` exactly when `p + 1` is the least length of a fill-path
(`Matrix.levelOfFill_eq_iff_isLeast`, [saad2003iterative] Theorem 10.7), and it is finite —
the entry is filled by complete Gaussian elimination — exactly when a fill-path exists
(`Matrix.levelOfFill_ne_top_iff`, the fill-path theorem of Rose–Tarjan, [saad2003iterative]
Theorem 10.6).  No separate symbolic model of the elimination is needed: (10.17) read for
finiteness is that model.

The index type is `Fin n`, since the recurrence eliminates the pivots in their natural order; the
entries live in any type with a zero.
-/

namespace Matrix

variable {n : ℕ} {R : Type*} [Zero R]

open scoped Classical in
/-- The initial level of fill ([saad2003iterative] Definition 10.5): `0` at a nonzero entry and on
the diagonal, `∞` elsewhere. -/
noncomputable def initialLevel (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : ℕ∞ :=
  if A i j ≠ 0 ∨ i = j then 0 else ⊤

/-- The level of fill after `k` elimination steps ([saad2003iterative] (10.17)): eliminating the
pivot `k` updates the level at `(i, j)` by `lev i j := min (lev i j) (lev i k + lev k j + 1)`, *for
the entries `i > k` and `j > k`* — the range of the two loops of line 5 of [saad2003iterative]
Algorithm 10.2, and the `dif` guard below.  Entries outside that range are not touched at step `k`,
so `levelOfFill A (min i j) i j` is already "the level of fill value after all the updates (10.17)
have been performed" (`levelOfFill_eq_of_min_le`), and `levelOfFill A n` is that value for every
entry at once.

The book writes the update in place inside its Algorithm 10.2, so carrying the step index is what
makes it a function.  The guard is not decoration: without it the recurrence would be plain
Floyd–Warshall, computing the distance in the adjacency graph rather than the length of a
*fill*-path, and it would report fill at positions Gaussian elimination never touches — for the
symmetric pattern with edges `0 — 2` and `1 — 2` and no edge `0 — 1`, an unguarded step at the pivot
`2` would give `lev 0 1 = 1`, while row `0` is never modified at all.  The book's own reading of
(10.17) carries the guard: the fill-level at step `k - 1` is the shortest path through
`V_{k-1} = {1, …, k-1}`, taken between two vertices `i, j` that are *not* in `V_{k-1}`.  That
reading is `Matrix.levelOfFill_eq_iff_isLeast`. -/
noncomputable def levelOfFill (A : Matrix (Fin n) (Fin n) R) : ℕ → Fin n → Fin n → ℕ∞
  | 0, i, j => initialLevel A i j
  | k + 1, i, j =>
    if h : k < (i : ℕ) ∧ k < (j : ℕ) then
      min (levelOfFill A k i j)
        (levelOfFill A k i ⟨k, h.1.trans i.isLt⟩ + levelOfFill A k ⟨k, h.1.trans i.isLt⟩ j + 1)
    else levelOfFill A k i j

/-- Before any elimination the level of fill is the initial level. -/
@[simp]
theorem levelOfFill_zero (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    levelOfFill A 0 i j = initialLevel A i j := rfl

/-- The recurrence (10.17), unfolded at step `k + 1`. -/
theorem levelOfFill_succ (A : Matrix (Fin n) (Fin n) R) (k : ℕ) (i j : Fin n) :
    levelOfFill A (k + 1) i j =
      if h : k < (i : ℕ) ∧ k < (j : ℕ) then
        min (levelOfFill A k i j)
          (levelOfFill A k i ⟨k, h.1.trans i.isLt⟩ + levelOfFill A k ⟨k, h.1.trans i.isLt⟩ j + 1)
      else levelOfFill A k i j := rfl

/-- The update (10.17) at the pivot `k`, with the pivot named: this is `levelOfFill_succ` with the
side conditions `k < i` and `k < j` of line 5 of Algorithm 10.2 discharged. -/
theorem levelOfFill_succ_eq (A : Matrix (Fin n) (Fin n) R) {k : ℕ} {i j : Fin n}
    (hi : k < (i : ℕ)) (hj : k < (j : ℕ)) (K : Fin n) (hK : (K : ℕ) = k) :
    levelOfFill A (k + 1) i j =
      min (levelOfFill A k i j) (levelOfFill A k i K + levelOfFill A k K j + 1) := by
  have hKeq : K = ⟨k, hi.trans i.isLt⟩ := Fin.ext hK
  rw [hKeq, levelOfFill_succ]
  split_ifs with h
  · rfl
  · exact absurd ⟨hi, hj⟩ h

/-- Step `k + 1` bounds the level at `(i, j)` by the path through the pivot `k`. -/
theorem levelOfFill_succ_le (A : Matrix (Fin n) (Fin n) R) {k : ℕ} {i j : Fin n}
    (hi : k < (i : ℕ)) (hj : k < (j : ℕ)) (K : Fin n) (hK : (K : ℕ) = k) :
    levelOfFill A (k + 1) i j ≤ levelOfFill A k i K + levelOfFill A k K j + 1 := by
  rw [levelOfFill_succ_eq A hi hj K hK]
  exact min_le_right _ _

/-- Entry `(i, j)` is not touched at a step whose pivot is not smaller than both `i` and `j`: those
are the entries line 5 of Algorithm 10.2 skips. -/
theorem levelOfFill_succ_of_not_lt (A : Matrix (Fin n) (Fin n) R) {k : ℕ} {i j : Fin n}
    (h : ¬(k < (i : ℕ) ∧ k < (j : ℕ))) :
    levelOfFill A (k + 1) i j = levelOfFill A k i j := by
  rw [levelOfFill_succ]
  split_ifs
  rfl

/-- A level of fill never increases along the elimination. -/
theorem levelOfFill_le_succ (A : Matrix (Fin n) (Fin n) R) (k : ℕ) (i j : Fin n) :
    levelOfFill A (k + 1) i j ≤ levelOfFill A k i j := by
  rw [levelOfFill_succ]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- The monotone form of `levelOfFill_le_succ`. -/
theorem levelOfFill_le_of_le (A : Matrix (Fin n) (Fin n) R) {k m : ℕ} (h : k ≤ m) (i j : Fin n) :
    levelOfFill A m i j ≤ levelOfFill A k i j := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact (levelOfFill_le_succ A m i j).trans ih

/-- Entry `(i, j)` stops changing after step `min (i, j)`: `levelOfFill A (min i j) i j` is already
"the level of fill value after all the updates (10.17) have been performed". -/
theorem levelOfFill_eq_of_min_le (A : Matrix (Fin n) (Fin n) R) {i j : Fin n} {k m : ℕ}
    (hk : min (i : ℕ) (j : ℕ) ≤ k) (hkm : k ≤ m) :
    levelOfFill A m i j = levelOfFill A k i j := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [levelOfFill_succ_of_not_lt A ?_, ih]
    rintro ⟨h1, h2⟩
    exact absurd (lt_min h1 h2) (not_lt.2 (hk.trans hm))

/-- A level of fill is never created: it is positive after `k` steps exactly when it was positive at
the start, because every update adds `1` to a sum of levels. This is the book's remark that an entry
nonzero in `A` keeps level `0` throughout the elimination. -/
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

/-- The zero pattern `P_p` of `ILU(p)` ([saad2003iterative] §10.3.3, Algorithm 10.5) is the set of
positions whose level of fill, after all the updates (10.17), exceeds `p`. -/
noncomputable def levelPattern (A : Matrix (Fin n) (Fin n) R) (p : ℕ) : Set (Fin n × Fin n) :=
  {q | (p : ℕ∞) < levelOfFill A n q.1 q.2}

/-- A diagonal position has level of fill `0` throughout and is never in the `ILU(p)` pattern, so
the existence theorem `Matrix.IsMMatrix.exists_isILU` applies to `ILU(p)` for every `p`. -/
theorem diag_notMem_levelPattern (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i : Fin n) :
    (i, i) ∉ levelPattern A p := by
  intro hq
  have hpos : 0 < levelOfFill A n i i := lt_of_le_of_lt zero_le hq
  rw [zero_lt_levelOfFill_iff, initialLevel, ite_eq_left (Or.inr rfl)] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **`p = 0` recovers `ILU(0)`** ([saad2003iterative] §10.3.3): the pattern `P₀` is exactly the
off-diagonal zero pattern of `A`, so `levelPattern A 0` is the pattern of `Matrix.IsILU0`. -/
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

/-- A *fill-path* between `i` and `j` ([saad2003iterative] §10.3.3): a path of the adjacency graph
of `A` all of whose vertices except the two endpoints `i` and `j` are numbered less than `i` and
than `j`.

The graph is `Matrix.adjGraph`, the symmetrized loopless graph of the pattern, which for a symmetric
pattern loses nothing off the diagonal (`Matrix.adjGraph_adj_iff_of_forall_ne_zero`).  Symmetry of
the pattern is a real hypothesis of the two characterizations below and not a convenience: the level
of fill (10.17) is computed from the *directed* pattern, so without it the fill-path would have to
be directed too. -/
def IsFillPath {i j : Fin n} (w : A.adjGraph.Walk i j) : Prop :=
  w.IsPath ∧ ∀ v ∈ w.support, v ≠ i → v ≠ j → v < i ∧ v < j

/-- The vertex condition of a fill-path without the requirement that no vertex repeat.  The
recursion (10.17) produces these directly, by concatenation at the pivot, and
`SimpleGraph.Walk.bypass` turns one into a fill-path no longer than it. -/
private def IsFillWalk {i j : Fin n} (w : A.adjGraph.Walk i j) : Prop :=
  ∀ v ∈ w.support, v ≠ i → v ≠ j → v < i ∧ v < j

/-- For a symmetric pattern the adjacency graph joins `i` and `j` exactly when they are distinct and
`a_ij ≠ 0`. -/
private theorem adjGraph_adj_iff (hsymm : A.IsPatternSymm) (i j : Fin n) :
    A.adjGraph.Adj i j ↔ i ≠ j ∧ A i j ≠ 0 :=
  adjGraph_adj_iff_of_forall_ne_zero fun i j => (hsymm i j).1

/-- A path meets its first vertex only at the start: the part of it after an intermediate vertex `k`
avoids `i`. -/
private theorem notMem_support_dropUntil {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {i j k : V} {w : G.Walk i j} (hp : w.IsPath) (hk : k ∈ w.support) (hki : k ≠ i) :
    i ∉ (w.dropUntil k hk).support := by
  intro hi
  have hsupp : w.support = (w.takeUntil k hk).support ++ (w.dropUntil k hk).support.tail := by
    conv_lhs => rw [← w.take_spec hk]
    rw [SimpleGraph.Walk.support_append]
  have hnd : ((w.takeUntil k hk).support ++ (w.dropUntil k hk).support.tail).Nodup := by
    rw [← hsupp]
    exact hp.support_nodup
  refine List.disjoint_of_nodup_append hnd (SimpleGraph.Walk.start_mem_support _) ?_
  rw [← SimpleGraph.Walk.cons_tail_support] at hi
  exact (List.mem_cons.1 hi).resolve_left (Ne.symm hki)

/-- **Half of Theorem 10.7**: a fill-path of length `ℓ` forces the level of fill to be at most
`ℓ - 1`.

The induction is on the number `m` of eliminated pivots, splitting the path at the pivot `m`
whenever it passes through it.  The two halves are again fill-paths — this is where the path has to
be a path and not merely a walk, since the prefix must avoid `j` and the suffix must avoid `i` — and
each of them has all its interior vertices below `m`, so the inductive hypothesis applies to both
and the update (10.17) at the pivot `m` combines the two bounds. -/
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
    have hmn : m < n := by have := i.isLt; omega
    obtain ⟨K, hK⟩ : ∃ K : Fin n, (K : ℕ) = m := ⟨⟨m, hmn⟩, rfl⟩
    have hKlti : K < i := by rw [Fin.lt_def, hK]; omega
    have hKltj : K < j := by rw [Fin.lt_def, hK]; omega
    by_cases hKmem : K ∈ w.support
    · have hKi : K ≠ i := ne_of_lt hKlti
      have hKj : K ≠ j := ne_of_lt hKltj
      have hjnot := SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hKmem hKj.symm
      have hinot := notMem_support_dropUntil hp hKmem hKi
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

/-- **The other half of Theorem 10.7**: a finite level of fill produces a fill-walk of the matching
length, by concatenating at the pivot at which the level was last lowered.  The walk need not be a
path, and `SimpleGraph.Walk.bypass` repairs that afterwards. -/
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

/-- A fill-path is never shorter than `lev_ij + 1`.  This is `levelOfFill_add_one_le_length` read at
the last step that can touch `(i, j)`, namely `min (i, j)`. -/
theorem levelOfFill_add_one_le_of_isFillPath (hsymm : A.IsPatternSymm)
    {i j : Fin n} (hij : i ≠ j) {w : A.adjGraph.Walk i j} (hw : IsFillPath w) :
    levelOfFill A n i j + 1 ≤ (w.length : ℕ∞) := by
  rw [levelOfFill_eq_of_min_le A (k := min (i : ℕ) (j : ℕ)) le_rfl
    (le_of_lt (lt_of_le_of_lt (min_le_left _ _) i.isLt))]
  refine levelOfFill_add_one_le_length hsymm _ w hij hw.1 (fun v hv hvi hvj => ?_)
    (min_le_left _ _) (min_le_right _ _)
  exact lt_min (Fin.lt_def.1 (hw.2 v hv hvi hvj).1) (Fin.lt_def.1 (hw.2 v hv hvi hvj).2)

/-- A level of fill equal to `p` produces a fill-path of length exactly `p + 1`: the fill-walk of
`exists_fillWalk_of_levelOfFill`, shortened to a path by `SimpleGraph.Walk.bypass`, cannot have come
out shorter, because `levelOfFill_add_one_le_of_isFillPath` bounds every fill-path from below. -/
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

/-- **The fill-path characterization of the level of fill** ([saad2003iterative] Theorem 10.7):
for a symmetric pattern, at the completion of the elimination an off-diagonal position `(i, j)`
has level of fill `p` exactly when `p + 1` is the *least* length of a fill-path between `i` and
`j`.  The minimality is what the book's proof uses when it argues that `lev(a_ij)` cannot be
smaller.

`levelOfFill A n` is the level after all the updates (10.17), and the theorem is about that
recurrence and not about the alternative (10.18), whose characterization differs.  Symmetry of the
pattern is what makes the undirected adjacency graph carry the directed information (10.17) is
computed from. -/
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

/-- **The fill-path theorem** ([saad2003iterative] Theorem 10.6, after Rose–Tarjan and
George–Liu): for a symmetric pattern, the off-diagonal entry `(i, j)` is filled at the completion
of Gaussian elimination — its level of fill is finite — exactly when there is a fill-path between
`i` and `j`.  It is the `⊤`/non-`⊤` shadow of `Matrix.levelOfFill_eq_iff_isLeast`: the recurrence
(10.17) read for finiteness is the symbolic elimination. -/
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

/-- A position survives the `ILU(p)` pattern for some `p` exactly when its level of fill is finite.
-/
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
