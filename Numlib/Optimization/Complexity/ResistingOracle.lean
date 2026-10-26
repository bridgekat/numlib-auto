import Numlib.Optimization.Complexity.ZeroChain
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The resisting oracle: general methods behave like zero-respecting ones

The orthogonal-embedding argument of Carmon, Duchi, Hinder and Sidford (*Lower bounds for finding
stationary points I*, Propositions 1 and 2 and Appendix A), cited without proof as Theorem 4.2.4
of [cartis2022evaluation]: every deterministic `p`-th order method `M`, run on a suitably rotated
copy `f ∘ Uᵀ : ℝ^{n+T} → ℝ` of `f : ℝ^n → ℝ`, produces during its first `T` iterations the images
under `U` of the iterates of a zero-respecting method on `f`.

## Construction

The zero-respecting method `simMethod M T` on `ℝ^n` simulates `M` on `ℝ^{n+T}` and builds the
isometry `U` lazily (a deterministic "lazy Gram–Schmidt"). It keeps columns `u_j ∈ ℝ^{n+T}`,
`j : Fin n`, zero for coordinates that are not yet *discovered* (no derivative of order
`1, …, p` of `f` at a past iterate is nonzero in the direction `e_j`). When `e_j` is discovered,
`u_j` is chosen as a unit vector orthogonal to all chosen columns and to all simulated queries
`z_0, …, z_k` of `M` (possible as long as `k < T`). `M` is answered with the jets of `f`
pushed forward by the partial isometry, and the simulating method outputs
`x_{k+1} = (⟪u_j, z_{k+1}⟫)_j`, so it is zero-respecting by construction. Completing the columns
at the end gives an isometry `U` with `Uᵀ z_k = x_k` for `k < T`, and the jets of `f ∘ Uᵀ` at the
queries are the answers used in the simulation, so the true run of `M` on `f ∘ Uᵀ` is the
simulated one.

## Main results

* `Optimization.exists_zeroRespecting_simulation`: the simulation statement.
* `Optimization.classComplexity_zeroRespecting_le`: Theorem 4.2.4, first part,
  `#_ε(𝓜_ZR(p), 𝓕) ≤ #_ε(𝓜, 𝓕)` for every class of functions closed under orthogonal embeddings.
* `Optimization.le_classComplexity_comp_adjoint`: Theorem 4.2.4, second part.

The construction does not need the methods to start at `0`, so the results hold for every class of
methods `𝓜`, in particular for `methodClass p`.
-/

open Set Filter
open scoped InnerProductSpace

namespace Optimization

namespace ResistingOracle

variable {n m p : ℕ}

/-! ### Columns, coordinates and pushed-forward jets -/

/-- The coordinate map `z ↦ (⟪c_j, z⟫)_j` of a family of columns `c : Fin n → ℝ^m` (the adjoint
of `x ↦ ∑ x_j c_j`). -/
noncomputable def colAdjoint (c : Fin n → EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∑ j, (innerSL ℝ (c j)).smulRight (EuclideanSpace.single j (1 : ℝ))

@[simp]
theorem colAdjoint_apply (c : Fin n → EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin m))
    (j : Fin n) : colAdjoint c z j = ⟪c j, z⟫_ℝ := by
  simp [colAdjoint, Pi.single_apply]

/-- The jet `a` pushed forward to `ℝ^m` by the linear map `P : ℝ^m → ℝ^n`: the jet of `f ∘ P`
when `a` is the jet of `f`. -/
noncomputable def pushJet (a : Jet (EuclideanSpace ℝ (Fin n)) p)
    (P : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Jet (EuclideanSpace ℝ (Fin m)) p :=
  fun q => (a q).compContinuousLinearMap fun _ => P

/-- Coordinate `j` is *discovered* by time `k` for the answers `a`: some answer `a_i`, `i ≤ k`,
has a derivative of order `q ∈ [1 : p]` for which `e_j` is not a null direction. -/
def Discovered (a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p) (k : ℕ) (j : Fin n) : Prop :=
  ∃ i ≤ k, ∃ q : Fin (p + 1), 1 ≤ (q : ℕ) ∧
    ¬ IsNullDirection (a i q) (EuclideanSpace.single j (1 : ℝ))

theorem Discovered.mono {a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} {k k' : ℕ} {j : Fin n}
    (h : Discovered a k j) (hk : k ≤ k') : Discovered a k' j := by
  obtain ⟨i, hi, q, hq, h⟩ := h
  exact ⟨i, hi.trans hk, q, hq, h⟩

theorem Discovered.congr {a a' : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} {k : ℕ}
    (h : ∀ i ≤ k, a i = a' i) (j : Fin n) : Discovered a k j ↔ Discovered a' k j := by
  constructor
  · rintro ⟨i, hi, q, hq, hn⟩; exact ⟨i, hi, q, hq, by rwa [← h i hi]⟩
  · rintro ⟨i, hi, q, hq, hn⟩; exact ⟨i, hi, q, hq, by rwa [h i hi]⟩

/-- A vector whose discovered coordinates vanish is a null direction of every derivative of order
`q ≥ 1` in the answers up to time `k`. -/
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

/-- `c` extends the columns `prev` on the set of discovered coordinates `D`, avoiding the vectors
of `A`: undiscovered columns are zero, existing nonzero columns are kept, new columns are unit
vectors orthogonal to `A`, and all columns are pairwise orthogonal. -/
structure IsExtension (D : Set (Fin n)) (prev c : Fin n → EuclideanSpace ℝ (Fin m))
    (A : Finset (EuclideanSpace ℝ (Fin m))) : Prop where
  eq_zero : ∀ j, j ∉ D → c j = 0
  eq_prev : ∀ j ∈ D, prev j ≠ 0 → c j = prev j
  norm_eq_one : ∀ j ∈ D, prev j = 0 → ‖c j‖ = 1
  inner_eq_zero : ∀ j ∈ D, prev j = 0 → ∀ z ∈ A, ⟪c j, z⟫_ℝ = 0
  pairwise : Pairwise fun j j' => ⟪c j, c j'⟫_ℝ = 0

open Classical in
/-- A choice of extension (the zero family if there is none). -/
noncomputable def extend (D : Set (Fin n)) (prev : Fin n → EuclideanSpace ℝ (Fin m))
    (A : Finset (EuclideanSpace ℝ (Fin m))) : Fin n → EuclideanSpace ℝ (Fin m) :=
  if h : ∃ c, IsExtension D prev c A then h.choose else 0

variable {D : Set (Fin n)} {prev : Fin n → EuclideanSpace ℝ (Fin m)}
  {A : Finset (EuclideanSpace ℝ (Fin m))}

theorem extend_spec (h : ∃ c, IsExtension D prev c A) : IsExtension D prev (extend D prev A) A := by
  simp only [extend, h, dite_true]
  exact h.choose_spec

theorem extend_eq_zero {j : Fin n} (hj : j ∉ D) : extend D prev A j = 0 := by
  by_cases h : ∃ c, IsExtension D prev c A
  · exact (extend_spec h).eq_zero j hj
  · simp only [extend, h, dite_false, Pi.zero_apply]

theorem extend_pairwise : Pairwise fun j j' => ⟪extend D prev A j, extend D prev A j'⟫_ℝ = 0 := by
  by_cases h : ∃ c, IsExtension D prev c A
  · exact (extend_spec h).pairwise
  · simp only [extend, h, dite_false]
    intro j j' _
    simp

/-- An extension exists when the dimension `m` leaves room for `n` columns orthogonal to `A`. -/
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

/-- The simulated queries of `M` when the answers are the jets `a` pushed forward by the column
families `c`: `z_0 = x₀` and `z_{k+1} = M.next k (a_0 ∘ c_0ᵀ, …, a_k ∘ c_kᵀ)`. -/
noncomputable def query (c : ℕ → Fin n → EuclideanSpace ℝ (Fin m)) : ℕ → EuclideanSpace ℝ (Fin m)
  | 0 => M.x₀
  | k + 1 => M.next k fun i => pushJet (a i) (colAdjoint (c i))

theorem query_congr {c c' : ℕ → Fin n → EuclideanSpace ℝ (Fin m)} {k : ℕ}
    (h : ∀ i < k, c i = c' i) : query M a c k = query M a c' k := by
  rcases k with _ | k
  · rfl
  · simp only [query]
    congr 1
    funext i
    rw [h i (by omega)]

/-- The columns after the answer at time `k`: the columns of time `k - 1` extended to the
coordinates discovered by time `k`, avoiding the queries `z_0, …, z_k`. -/
noncomputable def cols (k : ℕ) : Fin n → EuclideanSpace ℝ (Fin m) :=
  extend {j | Discovered a k j}
    (match k with
      | 0 => 0
      | k' + 1 => cols k')
    ((Finset.range (k + 1)).image (query M a fun i => if _ : i < k then cols i else 0))
termination_by k
decreasing_by all_goals omega

/-- The columns before the answer at time `k`. -/
noncomputable def prevCols : ℕ → Fin n → EuclideanSpace ℝ (Fin m)
  | 0 => 0
  | k + 1 => cols M a k

/-- The simulated queries `z_k`. -/
noncomputable def z : ℕ → EuclideanSpace ℝ (Fin m) := query M a (cols M a)

theorem z_zero : z M a 0 = M.x₀ := rfl

theorem z_succ (k : ℕ) :
    z M a (k + 1) = M.next k fun i => pushJet (a i) (colAdjoint (cols M a i)) := rfl

theorem cols_eq (k : ℕ) : cols M a k =
    extend {j | Discovered a k j} (prevCols M a k) ((Finset.range (k + 1)).image (z M a)) := by
  rw [cols.eq_def]
  congr 1
  · refine Finset.image_congr fun i hi => query_congr M a fun i' hi' => ?_
    rw [Finset.mem_coe, Finset.mem_range] at hi
    simp only [show i' < k from by omega, dite_true]

theorem cols_eq_zero {k : ℕ} {j : Fin n} (hj : ¬ Discovered a k j) : cols M a k j = 0 := by
  rw [cols_eq]; exact extend_eq_zero hj

theorem cols_pairwise (k : ℕ) : Pairwise fun j j' => ⟪cols M a k j, cols M a k j'⟫_ℝ = 0 := by
  rw [cols_eq]; exact extend_pairwise

theorem prevCols_pairwise (k : ℕ) :
    Pairwise fun j j' => ⟪prevCols M a k j, prevCols M a k j'⟫_ℝ = 0 := by
  rcases k with _ | k
  · intro j j' _; simp [prevCols]
  · exact cols_pairwise M a k

theorem discovered_of_prevCols_ne_zero {k : ℕ} {j : Fin n} (h : prevCols M a k j ≠ 0) :
    ∃ k', k = k' + 1 ∧ Discovered a k' j ∧ prevCols M a k j = cols M a k' j := by
  rcases k with _ | k
  · exact absurd rfl h
  · exact ⟨k, rfl, not_not.1 fun hd => h (cols_eq_zero M a hd), rfl⟩

theorem isExtension_cols {k : ℕ} (hk : n + k < m) :
    IsExtension {j | Discovered a k j} (prevCols M a k) (cols M a k)
      ((Finset.range (k + 1)).image (z M a)) := by
  rw [cols_eq]
  refine extend_spec (exists_isExtension _ (prevCols_pairwise M a k) _ ?_)
  have := (Finset.card_image_le (s := Finset.range (k + 1)) (f := z M a))
  rw [Finset.card_range] at this
  omega

/-- Discovered columns are unit vectors (while the dimension allows the construction). -/
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

/-- Once chosen, columns never change. -/
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

/-- A column is orthogonal to every query made before its coordinate was discovered. -/
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

/-- The simulated iterates `x_0 = 0`, `x_{k+1} = (⟪u_j, z_{k+1}⟫)_j` of the zero-respecting
method. -/
noncomputable def simIter : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => 0
  | k + 1 => colAdjoint (cols M a k) (z M a (k + 1))

theorem simIter_succ_apply (k : ℕ) (j : Fin n) :
    simIter M a (k + 1) j = ⟪cols M a k j, z M a (k + 1)⟫_ℝ := by
  simp [simIter]

/-- The simulated iterates only depend on the answers up to the current time. -/
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

/-- The final columns: the columns after time `T - 1` completed by unit vectors orthogonal to the
queries `z_0, …, z_{T-1}`. -/
noncomputable def finalCols : Fin n → EuclideanSpace ℝ (Fin (n + T)) :=
  extend univ (prevCols M a T) ((Finset.range T).image (z M a))

theorem isExtension_finalCols :
    IsExtension univ (prevCols M a T) (finalCols M a) ((Finset.range T).image (z M a)) := by
  refine extend_spec (exists_isExtension _ (prevCols_pairwise M a T) _ ?_)
  have := (Finset.card_image_le (s := Finset.range T) (f := z M a))
  rw [Finset.card_range] at this
  omega

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

theorem norm_finalCols (j : Fin n) : ‖finalCols M a j‖ = 1 := by
  by_cases hp : prevCols M a T j = 0
  · exact (isExtension_finalCols M a).norm_eq_one j (mem_univ _) hp
  · rw [(isExtension_finalCols M a).eq_prev j (mem_univ _) hp]
    obtain ⟨k', hk', hd, he⟩ := discovered_of_prevCols_ne_zero M a hp
    rw [he]
    exact norm_cols M a (by omega) hd

theorem orthonormal_finalCols : Orthonormal ℝ (finalCols M a) :=
  ⟨norm_finalCols M a, (isExtension_finalCols M a).pairwise⟩

theorem inner_finalCols_z {i : ℕ} (hi : i < T) {j : Fin n}
    (hj : ∀ i', i = i' + 1 → ¬ Discovered a i' j) : ⟪finalCols M a j, z M a i⟫_ℝ = 0 := by
  by_cases hp : prevCols M a T j = 0
  · exact (isExtension_finalCols M a).inner_eq_zero j (mem_univ _) hp _
      (Finset.mem_image_of_mem _ (Finset.mem_range.2 hi))
  · rw [(isExtension_finalCols M a).eq_prev j (mem_univ _) hp]
    obtain ⟨k', hk', hd, he⟩ := discovered_of_prevCols_ne_zero M a hp
    rw [he]
    exact inner_cols_z M a (by omega) (by omega) hj

/-- The completed columns map the queries to the simulated iterates: `Uᵀ z_i = x_i`, `i < T`. -/
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

/-- Before time `T`, pushing the answers forward with the final columns or with the current
columns gives the same jets. -/
theorem pushJet_finalCols {i : ℕ} (hi : i < T) :
    pushJet (a i) (colAdjoint (finalCols M a)) = pushJet (a i) (colAdjoint (cols M a i)) := by
  funext q
  ext w
  simp only [pushJet, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine apply_eq_of_forall_sub_isNullDirection fun s => ?_
  have hq : 1 ≤ (q : ℕ) := by have := s.2; omega
  refine isNullDirection_of_forall_discovered le_rfl hq fun j hj => ?_
  rw [PiLp.sub_apply, colAdjoint_apply, colAdjoint_apply, finalCols_eq M a hi hj, sub_self]

theorem adjoint_colAdjoint_single (c : Fin n → EuclideanSpace ℝ (Fin m)) (j : Fin n) :
    (colAdjoint c).adjoint (EuclideanSpace.single j (1 : ℝ)) = c j := by
  refine ext_inner_right ℝ fun z => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, EuclideanSpace.inner_single_left, colAdjoint_apply]
  simp

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

theorem orthonormal_basisFun_toBasis :
    Orthonormal ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis := by
  rw [OrthonormalBasis.coe_toBasis]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal

/-- The isometry `U : ℝ^n → ℝ^{n+T}` with columns `finalCols`. -/
noncomputable def isometry : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + T)) :=
  LinearMap.isometryOfOrthonormal
    ((colAdjoint (finalCols M a)).adjoint :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + T)))
    (v := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) orthonormal_basisFun_toBasis
    (orthonormal_adjoint_colAdjoint_finalCols M a)

theorem isometryAdjoint_isometry :
    isometryAdjoint (isometry M a) = colAdjoint (finalCols M a) := by
  have h : (isometry M a).toContinuousLinearMap = (colAdjoint (finalCols M a)).adjoint := by
    ext1 x; rfl
  rw [isometryAdjoint, h, ContinuousLinearMap.adjoint_adjoint]

end Completion

/-! ### The simulating zero-respecting method -/

section Method

/-- A finite list of answers extended by zero to a sequence. -/
noncomputable def extendAnswers {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (b : Fin (k + 1) → Jet E p) : ℕ → Jet E p :=
  fun i => if h : i < k + 1 then b ⟨i, h⟩ else 0

/-- The zero-respecting method simulating `M` on `ℝ^{n+T}`: in dimension `n` it starts at `0` and
outputs the simulated iterates `x_{k+1} = (⟪u_j, z_{k+1}⟫)_j`. -/
noncomputable def simMethod (M : JetMethod p) (T : ℕ) : JetMethod p := fun n =>
  { x₀ := 0
    next := fun k b => simIter (M (n + T)) (extendAnswers b) (k + 1) }

variable (M : JetMethod p) (T : ℕ) (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)

/-- The answers received by `simMethod M T` on `f`. -/
noncomputable abbrev simAnswers : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p :=
  fun i => jetOracle f p ((simMethod M T n).iterate (jetOracle f p) i)

theorem simMethod_iterate (k : ℕ) :
    (simMethod M T n).iterate (jetOracle f p) k = simIter (M (n + T)) (simAnswers M T n f) k := by
  rcases k with _ | k
  · rfl
  · rw [OracleMethod.iterate_succ]
    refine simIter_congr (M (n + T)) fun i hi => ?_
    simp only [extendAnswers, show i < k + 1 from by omega, dite_true]

/-- `simMethod M T` is zero-respecting for every function. -/
theorem simMethod_mem_zeroRespectingClass : simMethod M T ∈ zeroRespectingClass p := by
  intro n f
  refine ⟨rfl, fun k j hj => ?_⟩
  rw [simMethod_iterate, simIter_succ_apply, cols_eq_zero, inner_zero_left]
  rintro ⟨i, hi, q, hq, hn⟩
  exact hn (hj q hq (by omega) i hi)

/-- The real run of `M` on `f ∘ Uᵀ` is the simulated one, for `k ≤ T`. -/
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

/-- **The resisting oracle** (Carmon–Duchi–Hinder–Sidford, Propositions 1 and 2; the proof of
Theorem 4.2.4 of [cartis2022evaluation]). For every `p`-th order method `M` and horizon `T` there
is a zero-respecting method `Z ∈ 𝓜_ZR(p)` such that for every dimension `n` and every `C^p`
function `f : ℝ^n → ℝ` some linear isometry `U : ℝ^n → ℝ^{n+T}` satisfies
`Uᵀ z_k = x_k` for `k < T`, where `z_k` are the iterates of `M` on `f_U = f ∘ Uᵀ` and `x_k` those
of `Z` on `f`. If moreover `f` is differentiable, the first `ε`-stationary iterate of `M` on `f_U`
comes no earlier than that of `Z` on `f`, up to the horizon:
`min T k_ε(Z, f) ≤ k_ε(M, f_U)`. -/
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

/-- **Theorem 4.2.4 of [cartis2022evaluation]**, first part:
`#_ε(𝓜_ZR(p), 𝓕) ≤ #_ε(𝓜, 𝓕)` for every class of methods `𝓜` (in particular `𝓜(p)`) and every
class of differentiable `C^p` functions `𝓕` closed under orthogonal embeddings
`f ↦ f ∘ Uᵀ` (such as `smoothClass Δ L p`, by `comp_adjoint_mem_smoothClass`). -/
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

/-- **Theorem 4.2.4 of [cartis2022evaluation]**, second part. If `f : ℝ^n → ℝ` is differentiable
and `C^p` and `#_ε(𝓜_ZR(p), {f}) ≥ k̄`, then `#_ε(𝓜, {f_U}) ≥ k̄` for every class of methods `𝓜`
(in particular `𝓜(p)`), where `{f_U}` is the set of all `f ∘ Uᵀ : ℝ^{n+k̄} → ℝ` with
`U : ℝ^n → ℝ^{n+k̄}` a linear isometry. -/
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

/-- **Theorem 4.2.4 of [cartis2022evaluation]**, second part, for a class `𝓕` containing all the
rotated copies `f ∘ Uᵀ : ℝ^{n+k̄} → ℝ`: `#_ε(𝓜_ZR(p), {f}) ≥ k̄` implies `#_ε(𝓜, 𝓕) ≥ k̄`. -/
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
