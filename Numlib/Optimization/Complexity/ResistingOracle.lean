/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.ZeroChain
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The resisting oracle: general methods behave like zero-respecting ones

This module proves the orthogonal-embedding argument of Carmon, Duchi, Hinder and Sidford (*Lower
bounds for finding stationary points I*, Propositions 1 and 2 and Appendix A), which
[cartis2022evaluation] cites without proof as Theorem 4.2.4. Let $M$ be a deterministic $p$-th order
method and let $f : \mathbb{R}^n \to \mathbb{R}$. Run $M$ on a suitably rotated copy
$f \circ U^T : \mathbb{R}^{n+T} \to \mathbb{R}$ of $f$, where
$U : \mathbb{R}^n \to \mathbb{R}^{n+T}$ is a linear isometry. During its first $T$ iterations, $M$
then produces the images under $U$ of the iterates of a zero-respecting method on $f$. Consequently,
the complexity of the zero-respecting methods on a class of functions that is closed under
orthogonal embeddings is at most the complexity of any class of methods on it.

## Main results

* `Optimization.exists_zeroRespecting_simulation`: for every method $M$ and horizon $T$ there is a
  zero-respecting method $Z$ such that, for every $C^p$ function $f$, some isometry $U$ satisfies
  $U^T z_k = x_k$ for $k < T$, where $z_k$ are the iterates of $M$ on $f \circ U^T$ and $x_k$ are
  the iterates of $Z$ on $f$.
* `Optimization.classComplexity_zeroRespecting_le`: the first part of Theorem 4.2.4 of
  [cartis2022evaluation], $\#_\varepsilon(\mathcal{M}_{ZR}(p), \mathcal{F}) \le
  \#_\varepsilon(\mathcal{M}, \mathcal{F})$ for every class of methods $\mathcal{M}$ and every class
  $\mathcal{F}$ of functions that is closed under orthogonal embeddings.
* `Optimization.le_classComplexity_comp_adjoint` and
  `Optimization.le_classComplexity_of_comp_adjoint_mem`: the second part of Theorem 4.2.4 of
  [cartis2022evaluation].

## Proof outline

The zero-respecting method `Optimization.ResistingOracle.simMethod` on $\mathbb{R}^n$ simulates $M$
on $\mathbb{R}^{n+T}$ and builds the isometry $U$ lazily, by a deterministic "lazy Gram–Schmidt"
process. It keeps columns $u_j \in \mathbb{R}^{n+T}$ for $j = 1, \dots, n$. The column $u_j$ is zero
while the coordinate $j$ is not yet *discovered*, that is, while no derivative of order
$1, \dots, p$ of $f$ at a past iterate is nonzero in the direction $e_j$. When $e_j$ is discovered,
$u_j$ is chosen as a unit vector orthogonal to all chosen columns and to all simulated queries
$z_0, \dots, z_k$ of $M$; this is possible as long as $k < T$. The method $M$ is answered with the
jets of $f$ pushed forward by the partial isometry, and the simulating method outputs
$x_{k+1} = (\langle u_j, z_{k+1} \rangle)_j$, so it is zero-respecting by construction. Completing
the columns at the end gives an isometry $U$ with $U^T z_k = x_k$ for $k < T$. The jets of
$f \circ U^T$ at the queries are the answers used in the simulation, so the true run of $M$ on
$f \circ U^T$ is the simulated one.

## Implementation notes

* The construction does not need the methods to start at $0$. The results therefore hold for every
  class of methods $\mathcal{M}$, in particular for `Optimization.methodClass p`.
* The transpose $U^T$ of an isometry is `Optimization.isometryAdjoint U`.
-/

open Set Filter
open scoped InnerProductSpace

namespace Optimization

namespace ResistingOracle

variable {n m p : ℕ}

/-! ### Columns, coordinates and pushed-forward jets -/

/-- The coordinate map $z \mapsto (\langle c_j, z \rangle)_j$ from $\mathbb{R}^m$ to $\mathbb{R}^n$
of a family of columns $c_1, \dots, c_n \in \mathbb{R}^m$. It is the adjoint of the map
$x \mapsto \sum_j x_j c_j$. -/
noncomputable def colAdjoint (c : Fin n → EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∑ j, (innerSL ℝ (c j)).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- The $j$-th coordinate of `Optimization.ResistingOracle.colAdjoint c z` is
$\langle c_j, z \rangle$. -/
@[simp]
theorem colAdjoint_apply (c : Fin n → EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin m))
    (j : Fin n) : colAdjoint c z j = ⟪c j, z⟫_ℝ := by
  simp [colAdjoint, Pi.single_apply]

/-- The jet $a$ on $\mathbb{R}^n$ pushed forward to $\mathbb{R}^m$ by a linear map
$P : \mathbb{R}^m \to \mathbb{R}^n$: each multilinear map $a_q$ is composed with $P$ in every
argument. If $a$ is the jet of $f$ at $Pz$, the result is the jet of $f \circ P$ at $z$. -/
noncomputable def pushJet (a : Jet (EuclideanSpace ℝ (Fin n)) p)
    (P : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Jet (EuclideanSpace ℝ (Fin m)) p :=
  fun q => (a q).compContinuousLinearMap fun _ => P

/-- The coordinate $j$ is **discovered** by time $k$ for the answers $a$ if, for some $i \le k$ and
some order $q \in \{1, \dots, p\}$, the basis vector $e_j$ is not a null direction of the
derivative $a_i^{(q)}$. -/
def Discovered (a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p) (k : ℕ) (j : Fin n) : Prop :=
  ∃ i ≤ k, ∃ q : Fin (p + 1), 1 ≤ (q : ℕ) ∧
    ¬ IsNullDirection (a i q) (EuclideanSpace.single j (1 : ℝ))

/-- A coordinate that is discovered by time $k$ is discovered by every later time $k' \ge k$. -/
theorem Discovered.mono {a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} {k k' : ℕ} {j : Fin n}
    (h : Discovered a k j) (hk : k ≤ k') : Discovered a k' j := by
  obtain ⟨i, hi, q, hq, h⟩ := h
  exact ⟨i, hi.trans hk, q, hq, h⟩

/-- Whether a coordinate is discovered by time $k$ depends only on the answers $a_0, \dots, a_k$. -/
theorem Discovered.congr {a a' : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} {k : ℕ}
    (h : ∀ i ≤ k, a i = a' i) (j : Fin n) : Discovered a k j ↔ Discovered a' k j := by
  constructor
  · rintro ⟨i, hi, q, hq, hn⟩; exact ⟨i, hi, q, hq, by rwa [← h i hi]⟩
  · rintro ⟨i, hi, q, hq, hn⟩; exact ⟨i, hi, q, hq, by rwa [h i hi]⟩

/-- Let $v \in \mathbb{R}^n$ vanish at every coordinate that is discovered by time $k$. Then $v$ is
a null direction of every derivative $a_i^{(q)}$ with $i \le k$ and $1 \le q \le p$. -/
theorem isNullDirection_of_forall_discovered {a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} {k i : ℕ}
    (hi : i ≤ k) {q : Fin (p + 1)} (hq : 1 ≤ (q : ℕ)) {v : EuclideanSpace ℝ (Fin n)}
    (hv : ∀ j, Discovered a k j → v j = 0) : IsNullDirection (a i q) v := by
  have hspan : v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
    ext j'; simp [Pi.single_apply]
  rw [hspan]
  refine isNullDirection_of_mem_span (S := range fun j : Fin n =>
    v j • EuclideanSpace.single j (1 : ℝ)) ?_ (Submodule.sum_mem _ fun j _ =>
      Submodule.subset_span ⟨j, rfl⟩)
  rintro _ ⟨j, rfl⟩
  by_cases hj : Discovered a k j
  · dsimp only
    rw [hv j hj, zero_smul]; exact isNullDirection_zero
  · refine IsNullDirection.smul ?_ _
    by_contra hn
    exact hj ⟨i, hi, q, hq, hn⟩

/-! ### One extension step -/

/-- A family $c$ **extends** the columns $\mathrm{prev}$ on the set $D$ of discovered coordinates,
avoiding the finite set $A$ of vectors, if the columns outside $D$ are zero, the nonzero columns
of $\mathrm{prev}$ in $D$ are kept, the new columns in $D$ are unit vectors orthogonal to $A$,
and all columns are pairwise orthogonal. -/
structure IsExtension (D : Set (Fin n)) (prev c : Fin n → EuclideanSpace ℝ (Fin m))
    (A : Finset (EuclideanSpace ℝ (Fin m))) : Prop where
  /-- Every column outside $D$ is zero. -/
  eq_zero : ∀ j, j ∉ D → c j = 0
  /-- Every column in $D$ that is nonzero in $\mathrm{prev}$ is kept. -/
  eq_prev : ∀ j ∈ D, prev j ≠ 0 → c j = prev j
  /-- Every column in $D$ that is zero in $\mathrm{prev}$ becomes a unit vector. -/
  norm_eq_one : ∀ j ∈ D, prev j = 0 → ‖c j‖ = 1
  /-- Every column in $D$ that is zero in $\mathrm{prev}$ becomes orthogonal to every vector of $A$.
  -/
  inner_eq_zero : ∀ j ∈ D, prev j = 0 → ∀ z ∈ A, ⟪c j, z⟫_ℝ = 0
  /-- Distinct columns are orthogonal. -/
  pairwise : Pairwise fun j j' => ⟪c j, c j'⟫_ℝ = 0

open Classical in
/-- A chosen extension of $\mathrm{prev}$ on $D$ avoiding $A$, in the sense of
`Optimization.ResistingOracle.IsExtension`. If no extension exists, it is the zero family. -/
noncomputable def extend (D : Set (Fin n)) (prev : Fin n → EuclideanSpace ℝ (Fin m))
    (A : Finset (EuclideanSpace ℝ (Fin m))) : Fin n → EuclideanSpace ℝ (Fin m) :=
  if h : ∃ c, IsExtension D prev c A then h.choose else 0

variable {D : Set (Fin n)} {prev : Fin n → EuclideanSpace ℝ (Fin m)}
  {A : Finset (EuclideanSpace ℝ (Fin m))}

/-- If an extension exists, then `Optimization.ResistingOracle.extend D prev A` is an extension. -/
theorem extend_spec (h : ∃ c, IsExtension D prev c A) : IsExtension D prev (extend D prev A) A := by
  simp only [extend, h, dite_true]
  exact h.choose_spec

/-- The chosen extension is zero at every coordinate outside $D$. -/
theorem extend_eq_zero {j : Fin n} (hj : j ∉ D) : extend D prev A j = 0 := by
  by_cases h : ∃ c, IsExtension D prev c A
  · exact (extend_spec h).eq_zero j hj
  · simp only [extend, h, dite_false, Pi.zero_apply]

/-- The columns of the chosen extension are pairwise orthogonal. -/
theorem extend_pairwise : Pairwise fun j j' => ⟪extend D prev A j, extend D prev A j'⟫_ℝ = 0 := by
  by_cases h : ∃ c, IsExtension D prev c A
  · exact (extend_spec h).pairwise
  · simp only [extend, h, dite_false]
    intro j j' _
    simp

/-- Let the columns $\mathrm{prev}$ be pairwise orthogonal, and let the finite set
$A \subseteq \mathbb{R}^m$ satisfy $|A| + n \le m$. Then an extension of $\mathrm{prev}$ on $D$
avoiding $A$ exists. -/
theorem exists_isExtension (D : Set (Fin n))
    (hprev : Pairwise fun j j' => ⟪prev j, prev j'⟫_ℝ = 0) (A : Finset (EuclideanSpace ℝ (Fin m)))
    (hA : A.card + n ≤ m) : ∃ c, IsExtension D prev c A := by
  classical
  set P : Finset (Fin n) := Finset.univ.filter fun j => prev j ≠ 0 with hP
  set N : Finset (Fin n) := Finset.univ.filter fun j => j ∈ D ∧ prev j = 0 with hN
  set B : Finset (EuclideanSpace ℝ (Fin m)) := A ∪ P.image prev
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin m)) := Submodule.span ℝ (B : Set _)
  have hK : Module.finrank ℝ K ≤ A.card + P.card :=
    (finrank_span_finset_le_card B).trans
      (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_left Finset.card_image_le _))
  have hPN : P.card + N.card ≤ n := by
    rw [← Finset.card_union_of_disjoint]
    · exact (Finset.card_le_univ _).trans (by simp)
    · rw [Finset.disjoint_left]
      intro j hjP hjN
      simp only [hP, hN, Finset.mem_filter, Finset.mem_univ, true_and] at hjP hjN
      exact hjP hjN.2
  have hKo := Submodule.finrank_add_finrank_orthogonal K
  rw [finrank_euclideanSpace_fin] at hKo
  have hNK : Fintype.card N ≤ Fintype.card (Fin (Module.finrank ℝ Kᗮ)) := by
    simp only [Fintype.card_coe, Fintype.card_fin]
    omega
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hNK
  set b := stdOrthonormalBasis ℝ Kᗮ
  have hmemK : ∀ z ∈ A, z ∈ K := fun z hz =>
    Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_union_left _ hz))
  have hprevK : ∀ j, prev j ∈ K := by
    intro j
    by_cases hj : prev j = 0
    · rw [hj]; exact K.zero_mem
    · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (by simp [hP, hj]))))
  have hbK : ∀ i, (b i : EuclideanSpace ℝ (Fin m)) ∈ Kᗮ := fun i => (b i).2
  have hmemN : ∀ {j}, j ∈ N ↔ j ∈ D ∧ prev j = 0 := by simp [hN]
  refine ⟨fun j => if hj : j ∈ N then (b (ι ⟨j, hj⟩) : EuclideanSpace ℝ (Fin m))
    else if j ∈ D then prev j else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have : j ∉ N := fun h => hj (hmemN.1 h).1
    simp [this, hj]
  · intro j hj hpj
    have : j ∉ N := fun h => hpj (hmemN.1 h).2
    simp [this, hj]
  · intro j hj hpj
    have hjN : j ∈ N := hmemN.2 ⟨hj, hpj⟩
    simp only [hjN, dite_true]
    rw [Submodule.norm_coe]
    exact b.orthonormal.1 _
  · intro j hj hpj z hz
    have hjN : j ∈ N := hmemN.2 ⟨hj, hpj⟩
    simp only [hjN, dite_true]
    exact Submodule.inner_left_of_mem_orthogonal (hmemK z hz) (hbK _)
  · intro j j' hjj'
    by_cases hj : j ∈ N <;> by_cases hj' : j' ∈ N
    · simp only [hj, hj', dite_true]
      rw [← Submodule.coe_inner]
      refine b.orthonormal.2 fun h => hjj' ?_
      have := ι.injective h
      exact congrArg Subtype.val this
    · simp only [hj, hj', dite_true, dite_false]
      split_ifs
      · exact Submodule.inner_left_of_mem_orthogonal (hprevK j') (hbK _)
      · exact inner_zero_right _
    · simp only [hj, hj', dite_true, dite_false]
      split_ifs
      · exact Submodule.inner_right_of_mem_orthogonal (hprevK j) (hbK _)
      · exact inner_zero_left _
    · simp only [hj, hj', dite_false]
      split_ifs
      · exact hprev hjj'
      all_goals simp

/-! ### The simulation -/

section Simulation

variable (M : OracleMethod (EuclideanSpace ℝ (Fin m)) (Jet (EuclideanSpace ℝ (Fin m)) p))
  (a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p)

/-- The simulated queries of $M$ when the answers are the jets $a$ pushed forward by the column
families $c$: $z_0$ is the initial point of $M$, and $z_{k+1}$ is the next point of $M$ for the
answers $a_i \circ c_i^T$, $i = 0, \dots, k$.

Here $a_i \circ c_i^T$ is `Optimization.ResistingOracle.pushJet (a i)
(Optimization.ResistingOracle.colAdjoint (c i))`. -/
noncomputable def query (c : ℕ → Fin n → EuclideanSpace ℝ (Fin m)) : ℕ → EuclideanSpace ℝ (Fin m)
  | 0 => M.x₀
  | k + 1 => M.next k fun i => pushJet (a i) (colAdjoint (c i))

/-- The query $z_k$ depends only on the column families $c_i$ with $i < k$. -/
theorem query_congr {c c' : ℕ → Fin n → EuclideanSpace ℝ (Fin m)} {k : ℕ}
    (h : ∀ i < k, c i = c' i) : query M a c k = query M a c' k := by
  rcases k with _ | k
  · rfl
  · simp only [query]
    congr 1
    funext i
    rw [h i (by omega)]

/-- The columns after the answer at time $k$: the columns of time $k - 1$ (zero for $k = 0$)
extended to the coordinates discovered by time $k$, avoiding the queries $z_0, \dots, z_k$. -/
noncomputable def cols (k : ℕ) : Fin n → EuclideanSpace ℝ (Fin m) :=
  extend {j | Discovered a k j}
    (match k with
      | 0 => 0
      | k' + 1 => cols k')
    ((Finset.range (k + 1)).image (query M a fun i => if _ : i < k then cols i else 0))
termination_by k
decreasing_by all_goals omega

/-- The columns before the answer at time $k$: zero for $k = 0$, and the columns after the answer at
time $k - 1$ for $k \ge 1$. -/
noncomputable def prevCols : ℕ → Fin n → EuclideanSpace ℝ (Fin m)
  | 0 => 0
  | k + 1 => cols M a k

/-- The simulated queries $z_k$, computed with the columns `Optimization.ResistingOracle.cols`. -/
noncomputable def z : ℕ → EuclideanSpace ℝ (Fin m) := query M a (cols M a)

/-- The first simulated query $z_0$ is the initial point of $M$. -/
theorem z_zero : z M a 0 = M.x₀ := rfl

/-- The simulated query $z_{k+1}$ is the next point of $M$ for the answers $a_i$ pushed forward by
the columns after time $i$, $i = 0, \dots, k$. -/
theorem z_succ (k : ℕ) :
    z M a (k + 1) = M.next k fun i => pushJet (a i) (colAdjoint (cols M a i)) := rfl

/-- The columns after time $k$ are the chosen extension of the columns before time $k$ to the
coordinates discovered by time $k$, avoiding the queries $z_0, \dots, z_k$. -/
theorem cols_eq (k : ℕ) : cols M a k =
    extend {j | Discovered a k j} (prevCols M a k) ((Finset.range (k + 1)).image (z M a)) := by
  rw [cols.eq_def]
  congr 1
  · refine Finset.image_congr fun i hi => query_congr M a fun i' hi' => ?_
    rw [Finset.mem_coe, Finset.mem_range] at hi
    simp only [show i' < k from by omega, dite_true]

/-- A column whose coordinate is not discovered by time $k$ is zero after time $k$. -/
theorem cols_eq_zero {k : ℕ} {j : Fin n} (hj : ¬ Discovered a k j) : cols M a k j = 0 := by
  rw [cols_eq]; exact extend_eq_zero hj

/-- The columns after time $k$ are pairwise orthogonal. -/
theorem cols_pairwise (k : ℕ) : Pairwise fun j j' => ⟪cols M a k j, cols M a k j'⟫_ℝ = 0 := by
  rw [cols_eq]; exact extend_pairwise

/-- The columns before time $k$ are pairwise orthogonal. -/
theorem prevCols_pairwise (k : ℕ) :
    Pairwise fun j j' => ⟪prevCols M a k j, prevCols M a k j'⟫_ℝ = 0 := by
  rcases k with _ | k
  · intro j j' _; simp [prevCols]
  · exact cols_pairwise M a k

/-- If the column $j$ before time $k$ is nonzero, then $k = k' + 1$ for some $k'$, the coordinate
$j$ is discovered by time $k'$, and the column equals the column $j$ after time $k'$. -/
theorem discovered_of_prevCols_ne_zero {k : ℕ} {j : Fin n} (h : prevCols M a k j ≠ 0) :
    ∃ k', k = k' + 1 ∧ Discovered a k' j ∧ prevCols M a k j = cols M a k' j := by
  rcases k with _ | k
  · exact absurd rfl h
  · exact ⟨k, rfl, not_not.1 fun hd => h (cols_eq_zero M a hd), rfl⟩

/-- If $n + k < m$, then the columns after time $k$ are an extension of the columns before time $k$
on the coordinates discovered by time $k$, avoiding the queries $z_0, \dots, z_k$. -/
theorem isExtension_cols {k : ℕ} (hk : n + k < m) :
    IsExtension {j | Discovered a k j} (prevCols M a k) (cols M a k)
      ((Finset.range (k + 1)).image (z M a)) := by
  rw [cols_eq]
  refine extend_spec (exists_isExtension _ (prevCols_pairwise M a k) _ ?_)
  have := (Finset.card_image_le (s := Finset.range (k + 1)) (f := z M a))
  rw [Finset.card_range] at this
  omega

/-- If $n + k < m$, then every column whose coordinate is discovered by time $k$ is a unit vector
after time $k$. -/
theorem norm_cols {k : ℕ} (hk : n + k < m) {j : Fin n} (hj : Discovered a k j) :
    ‖cols M a k j‖ = 1 := by
  induction k with
  | zero =>
    exact (isExtension_cols M a hk).norm_eq_one j hj rfl
  | succ k ih =>
    by_cases hp : prevCols M a (k + 1) j = 0
    · exact (isExtension_cols M a hk).norm_eq_one j hj hp
    · rw [(isExtension_cols M a hk).eq_prev j hj hp]
      obtain ⟨k', hk', hd, he⟩ := discovered_of_prevCols_ne_zero M a hp
      cases hk'
      rw [he]
      exact ih (by omega) hd

/-- Once chosen, a column never changes: if $n + k < m$, $i \le k$ and the coordinate $j$ is
discovered by time $i$, then the column $j$ after time $k$ equals the column $j$ after time $i$. -/
theorem cols_stable {k i : ℕ} (hk : n + k < m) (hik : i ≤ k) {j : Fin n}
    (hj : Discovered a i j) : cols M a k j = cols M a i j := by
  induction k with
  | zero => rw [Nat.le_zero.1 hik]
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hik with hik | rfl
    · have hd : Discovered a k j := hj.mono (by omega)
      have hne : prevCols M a (k + 1) j ≠ 0 := by
        change cols M a k j ≠ 0
        intro h0
        have := norm_cols M a (by omega) hd
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      rw [(isExtension_cols M a hk).eq_prev j (hd.mono k.le_succ) hne]
      exact ih (by omega) (by omega)
    · rfl

/-- A column is orthogonal to every query made before its coordinate was discovered. Let $n + k < m$
and $i \le k$, and suppose that for $i \ge 1$ the coordinate $j$ is not discovered by time
$i - 1$. Then the column $j$ after time $k$ is orthogonal to $z_i$. -/
theorem inner_cols_z {k i : ℕ} (hk : n + k < m) (hik : i ≤ k) {j : Fin n}
    (hj : ∀ i', i = i' + 1 → ¬ Discovered a i' j) : ⟪cols M a k j, z M a i⟫_ℝ = 0 := by
  induction k with
  | zero =>
    by_cases hd : Discovered a 0 j
    · exact (isExtension_cols M a hk).inner_eq_zero j hd rfl _
        (Finset.mem_image_of_mem _ (by simp; omega))
    · rw [cols_eq_zero M a hd, inner_zero_left]
  | succ k ih =>
    by_cases hd : Discovered a (k + 1) j
    · by_cases hp : prevCols M a (k + 1) j = 0
      · exact (isExtension_cols M a hk).inner_eq_zero j hd hp _
          (Finset.mem_image_of_mem _ (by simp; omega))
      · rw [(isExtension_cols M a hk).eq_prev j hd hp]
        obtain ⟨k', hk', hd', he⟩ := discovered_of_prevCols_ne_zero M a hp
        cases hk'
        rw [he]
        rcases Nat.lt_or_eq_of_le hik with hik | rfl
        · exact ih (by omega) (by omega)
        · exact absurd hd' (hj k rfl)
    · rw [cols_eq_zero M a hd, inner_zero_left]

/-- The simulated iterates of the zero-respecting method: $x_0 = 0$ and
$x_{k+1} = (\langle u_j, z_{k+1} \rangle)_j$, where $u_j$ are the columns after time $k$. -/
noncomputable def simIter : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => 0
  | k + 1 => colAdjoint (cols M a k) (z M a (k + 1))

/-- The $j$-th coordinate of $x_{k+1}$ is the inner product of the column $j$ after time $k$ with
$z_{k+1}$. -/
theorem simIter_succ_apply (k : ℕ) (j : Fin n) :
    simIter M a (k + 1) j = ⟪cols M a k j, z M a (k + 1)⟫_ℝ := by
  simp [simIter]

/-- If the answers $a$ and $a'$ agree up to time $k$, then their columns agree after every time
$i \le k$. -/
theorem cols_congr {a a' : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} {k : ℕ}
    (h : ∀ i ≤ k, a i = a' i) : ∀ i ≤ k, cols M a i = cols M a' i := by
  induction k with
  | zero =>
    intro i hi
    obtain rfl := Nat.le_zero.1 hi
    rw [cols_eq, cols_eq]
    have hD : {j | Discovered a 0 j} = {j | Discovered a' 0 j} := by
      ext j; exact Discovered.congr h j
    have hP : prevCols M a 0 = prevCols M a' 0 := rfl
    have hZ : (Finset.range 1).image (z M a) = (Finset.range 1).image (z M a') := by
      simp only [Finset.range_one, Finset.image_singleton, z_zero]
    rw [hD, hP, hZ]
  | succ k ih =>
    have ih' := ih fun i hi => h i (by omega)
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact ih' i (by omega)
    · rw [cols_eq, cols_eq]
      have hD : {j | Discovered a (k + 1) j} = {j | Discovered a' (k + 1) j} := by
        ext j; exact Discovered.congr h j
      have hP : prevCols M a (k + 1) = prevCols M a' (k + 1) := ih' k le_rfl
      have hZ : (Finset.range (k + 2)).image (z M a) = (Finset.range (k + 2)).image (z M a') := by
        refine Finset.image_congr fun i hi => ?_
        rw [Finset.mem_coe, Finset.mem_range] at hi
        rcases i with _ | i
        · rw [z_zero, z_zero]
        · rw [z_succ, z_succ]
          congr 1
          funext i'
          rw [h i' (by omega), ih' i' (by omega)]
      rw [hD, hP, hZ]

/-- If the answers $a$ and $a'$ agree up to time $k$, then their simulated iterates $x_{k+1}$ agree.
-/
theorem simIter_congr {a a' : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} {k : ℕ}
    (h : ∀ i ≤ k, a i = a' i) : simIter M a (k + 1) = simIter M a' (k + 1) := by
  have hc := cols_congr M h
  simp only [simIter, z_succ]
  rw [hc k le_rfl]
  congr 2
  funext i
  rw [h i (by omega), hc i (by omega)]

end Simulation

/-! ### Completion of the columns -/

section Completion

variable {T : ℕ}
  (M : OracleMethod (EuclideanSpace ℝ (Fin (n + T))) (Jet (EuclideanSpace ℝ (Fin (n + T))) p))
  (a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p)

/-- The final columns in $\mathbb{R}^{n+T}$: the columns after time $T - 1$, completed by unit
vectors orthogonal to the queries $z_0, \dots, z_{T-1}$ and to the other columns. -/
noncomputable def finalCols : Fin n → EuclideanSpace ℝ (Fin (n + T)) :=
  extend univ (prevCols M a T) ((Finset.range T).image (z M a))

/-- The final columns are an extension, on all coordinates, of the columns after time $T - 1$,
avoiding the queries $z_0, \dots, z_{T-1}$. -/
theorem isExtension_finalCols :
    IsExtension univ (prevCols M a T) (finalCols M a) ((Finset.range T).image (z M a)) := by
  refine extend_spec (exists_isExtension _ (prevCols_pairwise M a T) _ ?_)
  have := (Finset.card_image_le (s := Finset.range T) (f := z M a))
  rw [Finset.card_range] at this
  omega

/-- If $i < T$ and the coordinate $j$ is discovered by time $i$, then the final column $j$ equals
the column $j$ after time $i$. -/
theorem finalCols_eq {i : ℕ} (hi : i < T) {j : Fin n} (hj : Discovered a i j) :
    finalCols M a j = cols M a i j := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  have hd : Discovered a T' j := hj.mono (by omega)
  have hne : prevCols M a (T' + 1) j ≠ 0 := by
    change cols M a T' j ≠ 0
    intro h0
    have := norm_cols M a (by omega) hd
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [(isExtension_finalCols M a).eq_prev j (mem_univ _) hne]
  exact cols_stable M a (by omega) (by omega) hj

/-- Every final column is a unit vector. -/
theorem norm_finalCols (j : Fin n) : ‖finalCols M a j‖ = 1 := by
  by_cases hp : prevCols M a T j = 0
  · exact (isExtension_finalCols M a).norm_eq_one j (mem_univ _) hp
  · rw [(isExtension_finalCols M a).eq_prev j (mem_univ _) hp]
    obtain ⟨k', hk', hd, he⟩ := discovered_of_prevCols_ne_zero M a hp
    rw [he]
    exact norm_cols M a (by omega) hd

/-- The final columns are orthonormal. -/
theorem orthonormal_finalCols : Orthonormal ℝ (finalCols M a) :=
  ⟨norm_finalCols M a, (isExtension_finalCols M a).pairwise⟩

/-- Let $i < T$, and suppose that for $i \ge 1$ the coordinate $j$ is not discovered by time
$i - 1$. Then the final column $j$ is orthogonal to $z_i$. -/
theorem inner_finalCols_z {i : ℕ} (hi : i < T) {j : Fin n}
    (hj : ∀ i', i = i' + 1 → ¬ Discovered a i' j) : ⟪finalCols M a j, z M a i⟫_ℝ = 0 := by
  by_cases hp : prevCols M a T j = 0
  · exact (isExtension_finalCols M a).inner_eq_zero j (mem_univ _) hp _
      (Finset.mem_image_of_mem _ (Finset.mem_range.2 hi))
  · rw [(isExtension_finalCols M a).eq_prev j (mem_univ _) hp]
    obtain ⟨k', hk', hd, he⟩ := discovered_of_prevCols_ne_zero M a hp
    rw [he]
    exact inner_cols_z M a (by omega) (by omega) hj

/-- The final columns map the queries to the simulated iterates: $U^T z_i = x_i$ for $i < T$. -/
theorem colAdjoint_finalCols_z {i : ℕ} (hi : i < T) :
    colAdjoint (finalCols M a) (z M a i) = simIter M a i := by
  ext j
  rw [colAdjoint_apply]
  rcases i with _ | i
  · rw [inner_finalCols_z M a hi (fun i' h => absurd h (by omega))]
    rfl
  · rw [simIter_succ_apply]
    by_cases hd : Discovered a i j
    · rw [finalCols_eq M a (by omega) hd]
    · rw [cols_eq_zero M a hd, inner_zero_left]
      exact inner_finalCols_z M a hi fun i' h => by cases h; exact hd

/-- For $i < T$, the answer $a_i$ pushed forward by the final columns equals the answer $a_i$ pushed
forward by the columns after time $i$. -/
theorem pushJet_finalCols {i : ℕ} (hi : i < T) :
    pushJet (a i) (colAdjoint (finalCols M a)) = pushJet (a i) (colAdjoint (cols M a i)) := by
  funext q
  ext w
  simp only [pushJet, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine apply_eq_of_forall_sub_isNullDirection fun s => ?_
  have hq : 1 ≤ (q : ℕ) := by have := s.2; omega
  refine isNullDirection_of_forall_discovered le_rfl hq fun j hj => ?_
  rw [PiLp.sub_apply, colAdjoint_apply, colAdjoint_apply, finalCols_eq M a hi hj, sub_self]

/-- The adjoint of the coordinate map of the columns $c$ maps the basis vector $e_j$ to $c_j$. -/
theorem adjoint_colAdjoint_single (c : Fin n → EuclideanSpace ℝ (Fin m)) (j : Fin n) :
    (colAdjoint c).adjoint (EuclideanSpace.single j (1 : ℝ)) = c j := by
  refine ext_inner_right ℝ fun z => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, EuclideanSpace.inner_single_left, colAdjoint_apply]
  simp

/-- The adjoint of the coordinate map of the final columns maps the standard basis of $\mathbb{R}^n$
to an orthonormal family. -/
theorem orthonormal_adjoint_colAdjoint_finalCols :
    Orthonormal ℝ (((colAdjoint (finalCols M a)).adjoint :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + T))) ∘
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) := by
  have h : (((colAdjoint (finalCols M a)).adjoint :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + T))) ∘
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) = finalCols M a := by
    funext j
    simp only [Function.comp_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe, adjoint_colAdjoint_single]
  rw [h]
  exact orthonormal_finalCols M a

/-- The standard basis of $\mathbb{R}^n$ is orthonormal. -/
theorem orthonormal_basisFun_toBasis :
    Orthonormal ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis := by
  rw [OrthonormalBasis.coe_toBasis]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal

/-- The linear isometry $U : \mathbb{R}^n \to \mathbb{R}^{n+T}$ whose columns are the final columns.
-/
noncomputable def isometry : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + T)) :=
  LinearMap.isometryOfOrthonormal
    ((colAdjoint (finalCols M a)).adjoint :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + T)))
    (v := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) orthonormal_basisFun_toBasis
    (orthonormal_adjoint_colAdjoint_finalCols M a)

/-- The transpose $U^T$ of the isometry $U$ is the coordinate map of the final columns. -/
theorem isometryAdjoint_isometry :
    isometryAdjoint (isometry M a) = colAdjoint (finalCols M a) := by
  have h : (isometry M a).toContinuousLinearMap = (colAdjoint (finalCols M a)).adjoint := by
    ext1 x; rfl
  rw [isometryAdjoint, h, ContinuousLinearMap.adjoint_adjoint]

end Completion

/-! ### The simulating zero-respecting method -/

section Method

/-- A finite list of answers $b_0, \dots, b_k$, extended by zero to a sequence. -/
noncomputable def extendAnswers {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (b : Fin (k + 1) → Jet E p) : ℕ → Jet E p :=
  fun i => if h : i < k + 1 then b ⟨i, h⟩ else 0

/-- The zero-respecting method that simulates $M$ on $\mathbb{R}^{n+T}$. In dimension $n$ it starts
at $0$ and outputs the simulated iterates $x_{k+1} = (\langle u_j, z_{k+1} \rangle)_j$ for the
answers it has received. -/
noncomputable def simMethod (M : JetMethod p) (T : ℕ) : JetMethod p := fun n =>
  { x₀ := 0
    next := fun k b => simIter (M (n + T)) (extendAnswers b) (k + 1) }

variable (M : JetMethod p) (T : ℕ) (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)

/-- The answers that `Optimization.ResistingOracle.simMethod M T` receives on $f$: the jets of order
$p$ of $f$ at its iterates. -/
noncomputable abbrev simAnswers : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p :=
  fun i => jetOracle f p ((simMethod M T n).iterate (jetOracle f p) i)

/-- The $k$-th iterate of `Optimization.ResistingOracle.simMethod M T` on $f$ is the simulated
iterate $x_k$ for the answers that this method receives. -/
theorem simMethod_iterate (k : ℕ) :
    (simMethod M T n).iterate (jetOracle f p) k = simIter (M (n + T)) (simAnswers M T n f) k := by
  rcases k with _ | k
  · rfl
  · rw [OracleMethod.iterate_succ]
    refine simIter_congr (M (n + T)) fun i hi => ?_
    simp only [extendAnswers, show i < k + 1 from by omega, dite_true]

/-- The method `Optimization.ResistingOracle.simMethod M T` is zero-respecting for every function in
every dimension. -/
theorem simMethod_mem_zeroRespectingClass : simMethod M T ∈ zeroRespectingClass p := by
  intro n f
  refine ⟨rfl, fun k j hj => ?_⟩
  rw [simMethod_iterate, simIter_succ_apply, cols_eq_zero, inner_zero_left]
  rintro ⟨i, hi, q, hq, hn⟩
  exact hn (hj q hq (by omega) i hi)

/-- Let $f : \mathbb{R}^n \to \mathbb{R}$ be $C^p$. For every $k \le T$, the $k$-th iterate of $M$
on $f \circ U^T$ is the simulated query $z_k$: the real run of $M$ is the simulated one. -/
theorem iterate_comp_isometryAdjoint {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ p f) :
    ∀ k ≤ T, (M (n + T)).iterate
        (jetOracle (f ∘ isometryAdjoint (isometry (M (n + T)) (simAnswers M T n f))) p) k =
      z (M (n + T)) (simAnswers M T n f) k := by
  set a := simAnswers M T n f
  set U := isometry (M (n + T)) a
  have hjet : ∀ i < T, jetOracle (f ∘ isometryAdjoint U) p (z (M (n + T)) a i) =
      pushJet (a i) (colAdjoint (cols (M (n + T)) a i)) := by
    intro i hi
    rw [← pushJet_finalCols _ _ hi]
    funext q
    rw [jetOracle_apply, iteratedFDeriv_comp_isometryAdjoint U hf
      (by exact_mod_cast Nat.lt_succ_iff.1 q.2), isometryAdjoint_isometry,
      colAdjoint_finalCols_z _ _ hi, ← simMethod_iterate]
    rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · rfl
    · rw [OracleMethod.iterate_succ, z_succ]
      congr 1
      funext i
      have hi : (i : ℕ) ≤ k := Nat.lt_succ_iff.1 i.2
      rw [ih i (by omega) (by omega), hjet i (by omega)]

end Method

end ResistingOracle

open ResistingOracle

variable {p : ℕ}

/-- **The resisting oracle.** Let $M$ be a $p$-th order method and let $T \in \mathbb{N}$. Then
there is a zero-respecting method $Z \in \mathcal{M}_{ZR}(p)$ with the following property. For
every dimension $n$ and every $C^p$ function $f : \mathbb{R}^n \to \mathbb{R}$, some linear
isometry $U : \mathbb{R}^n \to \mathbb{R}^{n+T}$ satisfies $U^T z_k = x_k$ for all $k < T$,
where $z_k$ are the iterates of $M$ on $f_U = f \circ U^T$ and $x_k$ are the iterates of $Z$ on
$f$. If moreover $f$ is differentiable, then for every $\varepsilon$ the first
$\varepsilon$-stationary iterate of $M$ on $f_U$ comes no earlier than that of $Z$ on $f$, up to
the horizon:
$$\min\{T, k_\varepsilon(Z, f)\} \le k_\varepsilon(M, f_U).$$
This is Propositions 1 and 2 of Carmon, Duchi, Hinder and Sidford, and the proof of Theorem
4.2.4 of [cartis2022evaluation].

The indices $k_\varepsilon$ are `Optimization.firstStationaryIndex`, with values in `ℕ∞`; the
value is $\infty$ when no iterate is $\varepsilon$-stationary. The method $Z$ is
`Optimization.ResistingOracle.simMethod M T`. -/
theorem exists_zeroRespecting_simulation (M : JetMethod p) (T : ℕ) :
    ∃ Z ∈ zeroRespectingClass p, ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ p f →
      ∃ U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + T)),
        (∀ k < T, isometryAdjoint U (M.iter (n + T) (f ∘ isometryAdjoint U) k) = Z.iter n f k) ∧
        (Differentiable ℝ f → ∀ ε, min (T : ℕ∞) (firstStationaryIndex (Z.iter n f) f ε) ≤
          firstStationaryIndex (M.iter (n + T) (f ∘ isometryAdjoint U)) (f ∘ isometryAdjoint U)
            ε) := by
  refine ⟨simMethod M T, simMethod_mem_zeroRespectingClass M T, ?_⟩
  intro n f hf
  refine ⟨isometry (M (n + T)) (simAnswers M T n f), ?_, ?_⟩
  · intro k hk
    rw [JetMethod.iter, JetMethod.iter, iterate_comp_isometryAdjoint M T n hf k hk.le,
      isometryAdjoint_isometry, colAdjoint_finalCols_z _ _ hk]
    exact (simMethod_iterate M T n f k).symm
  · intro hd ε
    refine min_firstStationaryIndex_le fun k hk h => ?_
    rw [norm_fderiv_comp_isometryAdjoint _ _ (hd _)] at h
    rw [JetMethod.iter, iterate_comp_isometryAdjoint M T n hf k hk.le,
      isometryAdjoint_isometry, colAdjoint_finalCols_z _ _ hk] at h
    rwa [JetMethod.iter, simMethod_iterate]

/-- **Theorem 4.2.4** of [cartis2022evaluation], first part. Let $\mathcal{M}$ be any class of
$p$-th order methods, for example $\mathcal{M}(p)$. Let $\mathcal{F}$ be a class of functions of
variable dimension such that every $f \in \mathcal{F}$ is $C^p$ and differentiable, and such
that $\mathcal{F}$ is closed under orthogonal embeddings: if $f : \mathbb{R}^n \to \mathbb{R}$
is in $\mathcal{F}$, then $f \circ U^T : \mathbb{R}^m \to \mathbb{R}$ is in $\mathcal{F}$ for
every $m$ and every linear isometry $U : \mathbb{R}^n \to \mathbb{R}^m$. Then for every
$\varepsilon$,
$$\#_\varepsilon(\mathcal{M}_{ZR}(p), \mathcal{F}) \le \#_\varepsilon(\mathcal{M},
  \mathcal{F}).$$

The complexity $\#_\varepsilon$ is `Optimization.classComplexity`. The class
`Optimization.smoothClass Δ L p` with $L \ge 0$ is closed under orthogonal embeddings by
`Optimization.comp_adjoint_mem_smoothClass`. -/
theorem classComplexity_zeroRespecting_le (𝓜 : Set (JetMethod p))
    {𝓕 : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)}
    (h𝓕 : ∀ F ∈ 𝓕, ∀ (m : ℕ) (U : EuclideanSpace ℝ (Fin F.1) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)),
      (⟨m, F.2 ∘ isometryAdjoint U⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ) ∈ 𝓕)
    (hreg : ∀ F ∈ 𝓕, ContDiff ℝ p F.2 ∧ Differentiable ℝ F.2) (ε : ℝ) :
    classComplexity (zeroRespectingClass p) 𝓕 ε ≤ classComplexity 𝓜 𝓕 ε := by
  rw [le_classComplexity_iff_forall_lt]
  intro M _ k hk
  obtain ⟨k₀, rfl⟩ : ∃ k₀ : ℕ, k = k₀ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hk) |>.imp
    fun _ h => h.symm
  obtain ⟨Z, hZ, hsim⟩ := exists_zeroRespecting_simulation M (k₀ + 1)
  obtain ⟨⟨n, f⟩, hF, hkF⟩ := le_classComplexity_iff_forall_lt.1 le_rfl Z hZ k₀ hk
  obtain ⟨U, -, hU⟩ := hsim n f (hreg _ hF).1
  refine ⟨_, h𝓕 _ hF _ U, lt_of_lt_of_le ?_ (hU (hreg _ hF).2 ε)⟩
  exact lt_min (by exact_mod_cast Nat.lt_succ_self k₀) hkF

/-- **Theorem 4.2.4** of [cartis2022evaluation], second part. Let $\mathcal{M}$ be any class of
$p$-th order methods, for example $\mathcal{M}(p)$. Let $f : \mathbb{R}^n \to \mathbb{R}$ be
$C^p$ and differentiable, and let $\bar k \in \mathbb{N}$ satisfy
$\#_\varepsilon(\mathcal{M}_{ZR}(p), \{f\}) \ge \bar k$. Then $\#_\varepsilon(\mathcal{M},
\{f_U\}) \ge \bar k$, where $\{f_U\}$ is the set of all functions $f \circ U^T : \mathbb{R}^{n +
\bar k} \to \mathbb{R}$ with $U : \mathbb{R}^n \to \mathbb{R}^{n + \bar k}$ a linear isometry. -/
theorem le_classComplexity_comp_adjoint (𝓜 : Set (JetMethod p)) {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ p f) (hd : Differentiable ℝ f) {ε : ℝ}
    {k : ℕ} (hk : (k : ℕ∞) ≤ classComplexity (zeroRespectingClass p) {⟨n, f⟩} ε) :
    (k : ℕ∞) ≤ classComplexity 𝓜 {F | ∃ U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + k)), F = ⟨n + k, f ∘ isometryAdjoint U⟩} ε := by
  refine le_classComplexity_of_forall_exists fun M _ => ?_
  obtain ⟨Z, hZ, hsim⟩ := exists_zeroRespecting_simulation M k
  obtain ⟨U, -, hU⟩ := hsim n f hf
  refine ⟨_, ⟨U, rfl⟩, ?_⟩
  have h1 := le_classComplexity_singleton_iff.1 hk Z hZ
  exact (le_min le_rfl h1).trans (hU hd ε)

/-- **Theorem 4.2.4** of [cartis2022evaluation], second part, for a larger class. Let $\mathcal{M}$
be any class of $p$-th order methods. Let $f : \mathbb{R}^n \to \mathbb{R}$ be $C^p$ and
differentiable, and let $\bar k \in \mathbb{N}$ satisfy $\#_\varepsilon(\mathcal{M}_{ZR}(p),
\{f\}) \ge \bar k$. If a class $\mathcal{F}$ contains every function $f \circ U^T :
\mathbb{R}^{n + \bar k} \to \mathbb{R}$ with $U : \mathbb{R}^n \to \mathbb{R}^{n + \bar k}$ a
linear isometry, then $\#_\varepsilon(\mathcal{M}, \mathcal{F}) \ge \bar k$. -/
theorem le_classComplexity_of_comp_adjoint_mem (𝓜 : Set (JetMethod p)) {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ p f) (hd : Differentiable ℝ f) {ε : ℝ}
    {k : ℕ} (hk : (k : ℕ∞) ≤ classComplexity (zeroRespectingClass p) {⟨n, f⟩} ε)
    {𝓕 : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)}
    (h𝓕 : ∀ U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + k)),
      (⟨n + k, f ∘ isometryAdjoint U⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ) ∈ 𝓕) :
    (k : ℕ∞) ≤ classComplexity 𝓜 𝓕 ε :=
  (le_classComplexity_comp_adjoint 𝓜 hf hd hk).trans
    (classComplexity_mono_right fun _ ⟨U, hU⟩ => hU ▸ h𝓕 U)

end Optimization
