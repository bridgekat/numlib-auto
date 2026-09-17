/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Compact`, beside `FredholmAlternative.lean` and
`Mathlib.Analysis.Normed.Operator.Fredholm`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Fredholm.Open
import Numlib.Analysis.Normed.Module.Quotient
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Analysis.Normed.Operator.Riesz
import Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange

/-!
# Compact operators on Banach spaces: Schauder's theorem, the Fredholm alternative, the spectrum

The Banach-space half of [brezis2011functional] §6.1–§6.3, on top of the closure properties,
eigenvalue accumulation and closed-range results of `Numlib.Analysis.Normed.Operator.Compact`
and the Riesz ascent–descent theory of `Numlib.Analysis.Normed.Operator.Riesz`.

## Main statements

* `IsCompactOperator.strongDualMap`, `IsCompactOperator.of_strongDualMap`,
  `isCompactOperator_strongDualMap_iff` — **Schauder's theorem**: `T` is compact iff its Banach
  adjoint `T* = ContinuousLinearMap.strongDualMap T` is (Theorem 6.4). The direct half is a
  total-boundedness argument: the functionals of the unit ball of `F*` are `1`-Lipschitz on the
  totally bounded set `T(B_E)`, so finitely many values determine `T* v` up to `ε`. The converse
  goes through `T**` and the isometric embedding of `F` into `F**`.
* `IsCompactOperator.tendsto_of_tendsto_toWeakSpace`,
  `IsCompactOperator.of_forall_tendsto_of_tendsto_toWeakSpace` — a compact operator maps weakly
  convergent sequences to norm-convergent ones, and on a reflexive domain this characterizes
  compactness (Remark 2 of §6.1).
* `IsCompactOperator.isFredholm_smul_one_sub`, `IsCompactOperator.index_smul_one_sub` —
  `μ • 1 - T` is a **Fredholm operator of index zero** for `T` compact and `μ ≠ 0`, in the sense
  of Mathlib's `ContinuousLinearMap.IsFredholm` and `LinearMap.index`; with
  `ContinuousLinearMap.IsFredholm.add_isCompactOperator` and
  `ContinuousLinearMap.IsFredholm.index_add_isCompactOperator` — a compact perturbation of a
  Fredholm operator is Fredholm with the same index (the Comments on Chapter 6, property (c),
  which Mathlib's Fredholm theory does not have). The index is constant along the homotopy
  `A + t • T`, `t ∈ [0, 1]`, by `ContinuousLinearMap.index_continuousOn_isFredholm`.
* `IsCompactOperator.finrank_ker_smul_one_sub_eq_finrank_ker_strongDualMap` and
  `IsCompactOperator.range_smul_one_sub_eq_strongDualCoannihilator_ker_strongDualMap` — the
  **Fredholm alternative** in Banach form, `dim N(I - T) = dim N(I - T*)` and
  `R(I - T) = N(I - T*)^⊥` (Theorem 6.6 (d) and (b)); the dimension count goes through
  `ContinuousLinearMap.finrank_ker_strongDualMap_eq_finrank_quotient_range`, the identification
  of `N(A*)` with the dual of the cokernel of a closed-range operator
  (`Numlib.Analysis.Normed.Module.Quotient`).
* `IsCompactOperator.zero_mem_spectrum`, `IsCompactOperator.countable_setOf_hasEigenvalue`,
  `IsCompactOperator.tendsto_zero_of_injective_of_forall_hasEigenvalue`,
  `IsCompactOperator.finite_or_exists_enumeration_spectrum` — the **spectrum of a compact
  operator** (Theorem 6.8 and Lemma 6.2): `0 ∈ σ(T)` in infinite dimension, and `σ(T) ∖ {0}` is
  finite or a sequence of eigenvalues tending to `0`.

## Conventions

The Banach adjoint is `ContinuousLinearMap.strongDualMap T` (Mathlib's `precomp 𝕜 T`) of
`Numlib.Analysis.Normed.Operator.Unbounded.Adjoint`; annihilators are
`Submodule.strongDualAnnihilator` and `Submodule.strongDualCoannihilator`. Scalars are `RCLike 𝕜`
where the dual, Hahn–Banach or a real homotopy enters (Schauder, the weak-convergence
characterization, the index), a complete nontrivially normed field for the Fredholm property
itself (through the Riesz decomposition, without Hahn–Banach) and for the spectrum.
-/

open Filter Topology Metric Set Module
open scoped ContinuousLinearMap

namespace IsCompactOperator

/-! ### Schauder's theorem -/

section Schauder

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Schauder's theorem**, direct half ([brezis2011functional] Theorem 6.4): the Banach adjoint
of a compact operator between normed spaces is compact. No completeness of `E` or `F` is
needed.

`T* '' B_{F*}` is totally bounded in the complete space `E*`: cover the totally bounded set
`T(B_E)` by finitely many balls of radius `ε` with centers `y ∈ t`; the values `v ↦ (v y)_{y ∈ t}`
of the unit ball of `F*` form a bounded, hence totally bounded, subset of the finite-dimensional
`t → 𝕜`, so finitely many functionals `v_w` are `ε`-close to every `v ∈ B_{F*}` at all `y ∈ t`,
and then `‖(v - v_w) (T u)‖ ≤ ‖v - v_w‖ ‖T u - y‖ + ‖(v - v_w) y‖ < 3 ε` on `B_E`. -/
theorem strongDualMap {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    IsCompactOperator T.strongDualMap := by
  classical
  have key := isCompactOperator_iff_isCompact_closure_image_closedBall
    (T.strongDualMap : StrongDual 𝕜 F →ₗ[𝕜] StrongDual 𝕜 E) one_pos
  rw [ContinuousLinearMap.coe_coe] at key
  rw [key]
  refine TotallyBounded.isCompact_of_isClosed (TotallyBounded.closure ?_) isClosed_closure
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set ε' := ε / 5 with hε'
  have hε'0 : 0 < ε' := by positivity
  -- a finite `ε'`-net `t` of `T(B_E)`
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨t, ht, hKt⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded ε' hε'0
  have : Fintype t := ht.fintype
  -- the values on `t` of the functionals of the unit ball form a bounded set of `t → 𝕜`
  set Φ : StrongDual 𝕜 F → (t → 𝕜) := fun v y => v y with hΦ
  obtain ⟨R, hR⟩ := (ht.image norm).bddAbove
  have hΦB : Φ '' closedBall 0 1 ⊆ closedBall 0 (max R 0) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro y
    calc ‖Φ v y‖ = ‖v y‖ := rfl
      _ ≤ ‖v‖ * ‖(y : F)‖ := v.le_opNorm _
      _ ≤ 1 * R := by
          gcongr
          · exact mem_closedBall_zero_iff.1 hv
          · exact hR ⟨y, y.2, rfl⟩
      _ ≤ max R 0 := by rw [one_mul]; exact le_max_left _ _
  obtain ⟨W, hW, hΦW⟩ := Metric.totallyBounded_iff.1
    ((isCompact_closedBall (0 : t → 𝕜) (max R 0)).totallyBounded.subset hΦB) ε' hε'0
  -- for each center `w`, a functional of the unit ball whose values are `ε'`-close to `w`
  let pick : (t → 𝕜) → StrongDual 𝕜 F := fun w =>
    if h : ∃ v ∈ closedBall (0 : StrongDual 𝕜 F) 1, dist (Φ v) w < ε' then h.choose else 0
  refine ⟨T.strongDualMap '' (pick '' W), (hW.image _).image _, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨w, hw, hvw⟩ := mem_iUnion₂.1 (hΦW ⟨v, hv, rfl⟩)
  have hex : ∃ v' ∈ closedBall (0 : StrongDual 𝕜 F) 1, dist (Φ v') w < ε' := ⟨v, hv, hvw⟩
  have hpick : pick w = hex.choose := dite_eq_left_of_eq_true (eq_true hex)
  obtain ⟨hv'B, hv'w⟩ := hex.choose_spec
  refine mem_iUnion₂.2 ⟨T.strongDualMap (pick w), ⟨pick w, ⟨w, hw, rfl⟩, rfl⟩, ?_⟩
  rw [mem_ball, dist_eq_norm, ← map_sub, hpick]
  -- `‖(v - v') (T u)‖ < ε` for every unit `u`
  have hclose : ∀ y : t, ‖(v - hex.choose) y‖ < 2 * ε' := fun y => by
    have h1 : dist (Φ v y) (w y) < ε' := (dist_pi_lt_iff hε'0).1 hvw y
    have h2 : dist (Φ hex.choose y) (w y) < ε' := (dist_pi_lt_iff hε'0).1 hv'w y
    rw [sub_apply, ← dist_eq_norm]
    calc dist (v y) (hex.choose y) ≤ dist (v y) (w y) + dist (hex.choose y) (w y) :=
          dist_triangle_right _ _ _
      _ < ε' + ε' := add_lt_add h1 h2
      _ = 2 * ε' := (two_mul _).symm
  have hnorm : ‖v - hex.choose‖ ≤ 2 := by
    calc ‖v - hex.choose‖ ≤ ‖v‖ + ‖hex.choose‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (mem_closedBall_zero_iff.1 hv) (mem_closedBall_zero_iff.1 hv'B)
      _ = 2 := by norm_num
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm (C := 4 * ε') (by positivity)
    fun u hu => ?_) (by rw [hε']; linarith)
  obtain ⟨y, hy, hTuy⟩ := mem_iUnion₂.1 (hKt (hTK ⟨u, by simp [hu], rfl⟩))
  rw [ContinuousLinearMap.strongDualMap_apply]
  calc ‖(v - hex.choose) (T u)‖
      = ‖(v - hex.choose) (T u - y) + (v - hex.choose) y‖ := by rw [map_sub, sub_add_cancel]
    _ ≤ ‖(v - hex.choose) (T u - y)‖ + ‖(v - hex.choose) y‖ := norm_add_le _ _
    _ ≤ ‖v - hex.choose‖ * ‖T u - y‖ + ‖(v - hex.choose) y‖ := by
        gcongr; exact (v - hex.choose).le_opNorm _
    _ ≤ 2 * ε' + 2 * ε' := by
        gcongr
        · have h := (mem_ball.1 hTuy).le
          rw [dist_eq_norm] at h
          exact h
        · exact (hclose ⟨y, hy⟩).le
    _ = 4 * ε' := by ring

/-- **Schauder's theorem**, converse ([brezis2011functional] Theorem 6.4): if the Banach adjoint
of `T : E →L[𝕜] F` is compact, with `F` complete, then `T` is compact. `T** ∘ J_E = J_F ∘ T` with
`J_E`, `J_F` the canonical embeddings into the biduals, `T**` is compact by the direct half, so
`J_F(T(B_E))` lies in a compact set, and `J_F` is a closed embedding (`F` complete). -/
theorem of_strongDualMap [CompleteSpace F] {T : E →L[𝕜] F}
    (hT : IsCompactOperator T.strongDualMap) : IsCompactOperator T := by
  have key := isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[𝕜] F) one_pos
  rw [ContinuousLinearMap.coe_coe] at key
  rw [key]
  obtain ⟨K, hK, hTK⟩ := hT.strongDualMap.image_closedBall_subset_compact 1
  set J := NormedSpace.inclusionInDoubleDual 𝕜 F with hJ
  have hJemb : Topology.IsClosedEmbedding J :=
    (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := F)).isometry.isClosedEmbedding
  refine (hJemb.isCompact_preimage hK).closure_of_subset ?_
  rintro _ ⟨u, hu, rfl⟩
  refine hTK ⟨NormedSpace.inclusionInDoubleDual 𝕜 E u, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    calc ‖NormedSpace.inclusionInDoubleDual 𝕜 E u‖
        = ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E) u‖ := rfl
      _ = ‖u‖ := (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).norm_map u
      _ ≤ 1 := mem_closedBall_zero_iff.1 hu
  · ext v
    rfl

/-- **Schauder's theorem** ([brezis2011functional] Theorem 6.4): for `T : E →L[𝕜] F` with `F`
complete, `T*` is compact iff `T` is. -/
theorem _root_.isCompactOperator_strongDualMap_iff [CompleteSpace F] (T : E →L[𝕜] F) :
    IsCompactOperator T.strongDualMap ↔ IsCompactOperator T :=
  ⟨of_strongDualMap, strongDualMap⟩

end Schauder

/-! ### Compact operators and weak convergence -/

section Weak

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A compact operator maps weakly convergent sequences to norm-convergent ones**
([brezis2011functional] §6.1, Remark 2): if `u n ⇀ x` then `T (u n) → T x`. The sequence is
bounded (`exists_norm_le_of_tendsto_toWeakSpace`), so its image lies in a compact set; every
subsequence of `T (u n)` has a further subsequence converging to some `w`, and `w = T x` because
the functionals separate points. -/
theorem tendsto_of_tendsto_toWeakSpace {T : E →L[𝕜] F} (hT : IsCompactOperator T) {u : ℕ → E}
    {x : E} (hu : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    Tendsto (fun n => T (u n)) atTop (𝓝 (T x)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakSpace hu
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact C
  have hmem : ∀ n, T (u n) ∈ K := fun n => hTK ⟨u n, mem_closedBall_zero_iff.2 (hC n), rfl⟩
  rw [tendsto_toWeakSpace_iff] at hu
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨w, -, φ, hφ, hlim⟩ := hK.tendsto_subseq fun n => hmem (ns n)
  refine ⟨φ, ?_⟩
  -- the limit is `T x`: test against every functional
  have hw : w = T x := by
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun v => ?_
    have h1 : Tendsto (fun n => v (T (u (ns (φ n))))) atTop (𝓝 (v w)) :=
      (v.continuous.tendsto w).comp hlim
    have h2 : Tendsto (fun n => v (T (u (ns (φ n))))) atTop (𝓝 (v (T x))) :=
      (hu (v.comp T)).comp (hns.comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique h1 h2
  rw [← hw]
  exact hlim

/-- **The converse on a reflexive domain** ([brezis2011functional] §6.1, Remark 2, which cites
Exercise 6.7): an operator on a reflexive space that maps weakly convergent sequences to
norm-convergent ones is compact. A bounded sequence has a weakly convergent subsequence
(`NormedSpace.exists_subseq_forall_dual_tendsto`), whose image converges by hypothesis, so
`closure (T(B_E))` is sequentially compact, hence compact. -/
theorem of_forall_tendsto_of_tendsto_toWeakSpace [NormedSpace.IsReflexive 𝕜 E] (T : E →L[𝕜] F)
    (h : ∀ (u : ℕ → E) (x : E), Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop
      (𝓝 (toWeakSpace 𝕜 E x)) → Tendsto (fun n => T (u n)) atTop (𝓝 (T x))) :
    IsCompactOperator T := by
  have key := isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[𝕜] F) one_pos
  rw [ContinuousLinearMap.coe_coe] at key
  rw [key]
  refine IsSeqCompact.isCompact fun y hy => ?_
  -- approximate each `y n` by `T (u n)` with `u n` in the unit ball
  have happrox : ∀ n, ∃ u ∈ closedBall (0 : E) 1, dist (y n) (T u) < 1 / (n + 1) := fun n => by
    obtain ⟨_, ⟨u, hu, rfl⟩, hd⟩ :=
      Metric.mem_closure_iff.1 (hy n) (1 / (n + 1)) (by positivity)
    exact ⟨u, hu, hd⟩
  choose u hu hyu using happrox
  obtain ⟨x, φ, hφ, hweak⟩ := NormedSpace.exists_subseq_forall_dual_tendsto (𝕜 := 𝕜)
    (C := 1) fun n => mem_closedBall_zero_iff.1 (hu n)
  have hTu : Tendsto (fun n => T (u (φ n))) atTop (𝓝 (T x)) :=
    h (fun n => u (φ n)) x (tendsto_toWeakSpace_iff.2 hweak)
  have hdist : Tendsto (fun n => dist (y (φ n)) (T (u (φ n)))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (hyu (φ n)).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  refine ⟨T x, ?_, φ, hφ, ?_⟩
  · exact mem_closure_of_tendsto hTu (Eventually.of_forall fun n => ⟨u (φ n), hu _, rfl⟩)
  · exact tendsto_of_tendsto_of_dist hTu (by simpa [dist_comm] using hdist)

end Weak

/-! ### The Fredholm alternative: `μ • 1 - T` is Fredholm of index zero -/

section Fredholm

open LinearMap.FiniteRangeSetoid

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **`μ • 1 - T` is a Fredholm operator** for `T` compact on a Banach space and `μ ≠ 0`, in the
sense of Mathlib's `ContinuousLinearMap.IsFredholm` ([brezis2011functional] Comments on
Chapter 6, 1: "`A = I - T` with `T ∈ K(E)` is a Fredholm operator"). By the Riesz decomposition
`X = N(A^ν) ⊕ R(A^ν)` (`IsCompactOperator.exists_riesz_index`): `R(A^ν)` is closed, of finite
codimension (its complement `N(A^ν)` is finite-dimensional), invariant under `A`, and `A`
restricts to a bijection of it (injective because `N(A) ∩ R(A^ν) ⊆ N(A^ν) ∩ R(A^ν) = 0`,
onto because `R(A^(ν+1)) = R(A^ν)`), hence to an isomorphism by the open mapping theorem; this is
Mathlib's criterion `ContinuousLinearMap.IsFredholm.of_isInvertible_restrict`. No Hahn–Banach is
used. -/
theorem isFredholm_smul_one_sub {T : X →L[𝕜] X} (hT : IsCompactOperator T) {μ : 𝕜}
    (hμ : μ ≠ 0) : (μ • (1 : X →L[𝕜] X) - T).IsFredholm := by
  set A : X →L[𝕜] X := μ • (1 : X →L[𝕜] X) - T with hA
  obtain ⟨ν, -, hker, hrange, hcompl⟩ := hT.exists_riesz_index hμ
  set R : Submodule 𝕜 X := (A ^ ν).range with hR
  have hRc : IsClosed (R : Set X) := hT.isClosed_range_pow hμ ν
  have hfin : FiniteDimensional 𝕜 ((A ^ ν).ker) := hT.finiteDimensional_ker_pow hμ ν
  have hRcofg : R.CoFG :=
    Submodule.FG.cofg_of_isCompl hcompl (Module.Finite.iff_fg.1 hfin)
  -- `A` maps `R(A^ν)` into `R(A^(ν+1)) ⊆ R(A^ν)`
  have hmaps : MapsTo A R R := by
    rintro _ ⟨y, rfl⟩
    refine A.range_pow_anti (Nat.le_succ ν) ⟨y, ?_⟩
    change (A ^ (ν + 1)) y = A ((A ^ ν) y)
    exact A.pow_succ_apply' ν y
  refine ContinuousLinearMap.IsFredholm.of_isInvertible_restrict hRc hRc hmaps ?_
  -- the restriction is a continuous bijection between Banach spaces
  refine ⟨ContinuousLinearEquiv.ofBijective (A.restrict hmaps) ?_ ?_, rfl⟩
  · -- injective: an element of `N(A) ∩ R(A^ν)` lies in `N(A^ν) ∩ R(A^ν) = 0`
    refine LinearMap.ker_eq_bot'.2 fun x hx => ?_
    have hx' : A x = 0 := congrArg Subtype.val hx
    have hle : A.ker ≤ (A ^ ν).ker := by
      have h1 : (A ^ 1).ker ≤ (A ^ max ν 1).ker := A.ker_pow_mono (le_max_right ν 1)
      rwa [pow_one, hker _ (le_max_left ν 1)] at h1
    exact Subtype.ext (Submodule.disjoint_def.1 hcompl.disjoint x (hle hx') x.2)
  · -- onto: `R(A^(ν+1)) = R(A^ν)`
    refine LinearMap.range_eq_top.2 fun z => ?_
    have hz : (z : X) ∈ (A ^ (ν + 1)).range := by rw [hrange _ (Nat.le_succ ν)]; exact z.2
    obtain ⟨w, hw⟩ := hz
    refine ⟨⟨(A ^ ν) w, ⟨w, rfl⟩⟩, Subtype.ext ?_⟩
    change A ((A ^ ν) w) = z
    rw [← A.pow_succ_apply']
    exact hw

end Fredholm

end IsCompactOperator

namespace ContinuousLinearMap

section Perturbation

open LinearMap.FiniteRangeSetoid

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **A compact perturbation of a Fredholm operator is Fredholm** ([brezis2011functional]
Comments on Chapter 6, 1, property (c), first clause). With `B` a quasi-inverse of `A`
(`B ∘ A = 1 + R`, `R` of finite rank), `B ∘ (A + T)` agrees with `1 + B ∘ T` modulo finite rank,
and `1 + B ∘ T` is Fredholm since `B ∘ T` is compact
(`IsCompactOperator.isFredholm_smul_one_sub`); `B` is Fredholm too, so `A + T` is. -/
theorem IsFredholm.add_isCompactOperator {A T : X →L[𝕜] X} (hA : A.IsFredholm)
    (hT : IsCompactOperator T) : (A + T).IsFredholm := by
  obtain ⟨B, hB⟩ := hA.exists_isQuasiInverse
  have hBfred : B.IsFredholm := .of_isQuasiInverse hB.symm
  have hK : IsCompactOperator (B ∘L T) := hT.clm_comp B
  have hK' : IsCompactOperator (-(B ∘L T)) := hK.neg
  have h1 : (1 + B ∘L T).IsFredholm := by
    have := hK'.isFredholm_smul_one_sub (μ := (1 : 𝕜)) one_ne_zero
    rwa [one_smul, sub_neg_eq_add] at this
  have h2 : (B ∘L (A + T)).toLinearMap ≈ (1 + B ∘L T).toLinearMap := by
    rw [equiv_iff_hasFiniteRange]
    have := equiv_iff_hasFiniteRange.1 hB.1
    convert this using 1
    ext x
    simp only [LinearMap.sub_apply, coe_coe, comp_apply, add_apply, map_add, one_apply_eq_self,
      LinearMap.comp_apply, LinearMap.id_apply]
    abel
  exact hBfred.comp_iff_right.1 (h1.congr (Setoid.symm h2))

end Perturbation

section PerturbationRCLike

open LinearMap.FiniteRangeSetoid

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **A compact perturbation does not change the Fredholm index** ([brezis2011functional]
Comments on Chapter 6, 1, property (c), second clause): `(A + T).index = A.index` for `A`
Fredholm and `T` compact. The path `t ↦ A + t • T`, `t ∈ ℝ`, consists of Fredholm operators
(`IsFredholm.add_isCompactOperator`), and the index is locally constant on the Fredholm operators
(`ContinuousLinearMap.index_continuousOn_isFredholm`), hence constant on the connected `ℝ`. -/
theorem IsFredholm.index_add_isCompactOperator {A T : X →L[𝕜] X} (hA : A.IsFredholm)
    (hT : IsCompactOperator T) : (A + T).index = A.index := by
  let γ : ℝ → X →L[𝕜] X := fun t => A + ((t : 𝕜) • T)
  have hγ : Continuous γ :=
    continuous_const.add ((RCLike.continuous_ofReal (K := 𝕜)).smul continuous_const)
  have hfred : ∀ t, (γ t).IsFredholm := fun t => hA.add_isCompactOperator (hT.smul _)
  have hcont : Continuous fun t => (γ t).index :=
    index_continuousOn_isFredholm.comp_continuous hγ hfred
  have h := PreconnectedSpace.constant inferInstance hcont (x := (1 : ℝ)) (y := 0)
  simpa [γ] using h

/-- **`μ • 1 - T` has Fredholm index zero** for `T` compact and `μ ≠ 0` ([brezis2011functional]
Comments on Chapter 6, 1: "`A = I - T` … is a Fredholm operator of index zero"): the index of
the invertible `μ • 1` is zero, and the compact perturbation `-T` does not change it. -/
theorem _root_.IsCompactOperator.index_smul_one_sub {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0) :
    (μ • (1 : X →L[𝕜] X) - T).index = 0 := by
  have hfred : (μ • (1 : X →L[𝕜] X)).IsFredholm := by
    refine .of_isQuasiInverse (v := μ⁻¹ • (1 : X →L[𝕜] X)) ⟨?_, ?_⟩
    · change ((μ⁻¹ • (1 : X →L[𝕜] X)) ∘L (μ • 1)).toLinearMap ≈ LinearMap.id
      rw [show (μ⁻¹ • (1 : X →L[𝕜] X)) ∘L (μ • 1) = 1 by
        ext x; simp [smul_smul, hμ]]
      exact Setoid.refl _
    · change ((μ • (1 : X →L[𝕜] X)) ∘L (μ⁻¹ • 1)).toLinearMap ≈ LinearMap.id
      rw [show (μ • (1 : X →L[𝕜] X)) ∘L (μ⁻¹ • 1) = 1 by
        ext x; simp [smul_smul, hμ]]
      exact Setoid.refl _
  have hbij : Function.Bijective (μ • (1 : X →L[𝕜] X)) := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨μ⁻¹ • y, ?_⟩⟩
    · exact smul_right_injective X hμ (by simpa using hxy : μ • x = μ • y)
    · simp [smul_smul, hμ]
  rw [sub_eq_add_neg, hfred.index_add_isCompactOperator hT.neg]
  exact LinearMap.index_of_bijective hbij

end PerturbationRCLike

/-! ### The kernel of the adjoint and the cokernel -/

section Cokernel

variable {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **The kernel of the adjoint of a closed-range operator has the dimension of the cokernel**:
`dim N(A*) = dim (Y ⧸ R(A))` for `A : X →L[𝕜] Y` with closed range, both sides being `0` when
infinite. This is the step "`R(I - T) = N(I - T*)^⊥` has finite codimension `d*`" of the proof
of [brezis2011functional] Theorem 6.6 (d): `N(A*) = R(A)^⊥`
(`ContinuousLinearMap.ker_strongDualMap_eq_annihilator_range`) and `codim M = dim M^⊥` for a
closed `M` (`Submodule.finrank_quotient_eq_finrank_strongDualAnnihilator`). -/
theorem finrank_ker_strongDualMap_eq_finrank_quotient_range (A : X →L[𝕜] Y)
    (hA : IsClosed (A.range : Set Y)) :
    finrank 𝕜 A.strongDualMap.ker = finrank 𝕜 (Y ⧸ A.range) := by
  have : IsClosed ((LinearMap.range (A : X →ₗ[𝕜] Y) : Submodule 𝕜 Y) : Set Y) := hA
  rw [ker_strongDualMap_eq_annihilator_range,
    Submodule.finrank_quotient_eq_finrank_strongDualAnnihilator]

end Cokernel

end ContinuousLinearMap

namespace IsCompactOperator

section FredholmAlternative

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The adjoint of `μ • 1 - T` is `μ • 1 - T*`. -/
theorem _root_.ContinuousLinearMap.strongDualMap_smul_one_sub (T : X →L[𝕜] X) (μ : 𝕜) :
    (μ • (1 : X →L[𝕜] X) - T).strongDualMap =
      μ • (1 : StrongDual 𝕜 X →L[𝕜] StrongDual 𝕜 X) - T.strongDualMap := by
  rw [ContinuousLinearMap.strongDualMap_sub, ContinuousLinearMap.strongDualMap_smul,
    ContinuousLinearMap.one_def, ContinuousLinearMap.strongDualMap_id]
  rfl

/-- **The Fredholm alternative, clause (d), Banach form** ([brezis2011functional]
Theorem 6.6 (d)): `dim N(μ - T) = dim N(μ - T*)` for `T` compact on a Banach space and `μ ≠ 0`.
The index of `μ • 1 - T` is zero, so `dim N(μ - T) = dim (X ⧸ R(μ - T))`, and the cokernel has
the dimension of `N((μ - T)*)`
(`ContinuousLinearMap.finrank_ker_strongDualMap_eq_finrank_quotient_range`). -/
theorem finrank_ker_smul_one_sub_eq_finrank_ker_strongDualMap {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0) :
    finrank 𝕜 (μ • (1 : X →L[𝕜] X) - T).ker =
      finrank 𝕜 (μ • (1 : StrongDual 𝕜 X →L[𝕜] StrongDual 𝕜 X) - T.strongDualMap).ker := by
  have h := hT.index_smul_one_sub hμ
  rw [LinearMap.index_eq_finrank_sub, sub_eq_zero] at h
  rw [← ContinuousLinearMap.strongDualMap_smul_one_sub,
    ContinuousLinearMap.finrank_ker_strongDualMap_eq_finrank_quotient_range _
      (hT.isClosed_range_smul_sub hμ)]
  exact_mod_cast h

omit [CompleteSpace X] in
/-- **The Fredholm alternative, clause (b), Banach form** ([brezis2011functional]
Theorem 6.6 (b), second clause): `R(μ - T) = N(μ - T*)^⊥` for `T` compact on a normed space
and `μ ≠ 0` — the equation `(μ - T) u = f` is solvable iff `v f = 0` for every `v ∈ X*` with
`T* v = μ v`. The range is closed (`IsCompactOperator.isClosed_range_smul_sub`), so
`ContinuousLinearMap.range_eq_strongDualCoannihilator_ker_strongDualMap` applies; no
completeness is needed. -/
theorem range_smul_one_sub_eq_strongDualCoannihilator_ker_strongDualMap {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0) :
    (μ • (1 : X →L[𝕜] X) - T).range =
      (μ • (1 : StrongDual 𝕜 X →L[𝕜] StrongDual 𝕜 X) -
        T.strongDualMap).ker.strongDualCoannihilator := by
  rw [← ContinuousLinearMap.strongDualMap_smul_one_sub]
  refine ContinuousLinearMap.range_eq_strongDualCoannihilator_ker_strongDualMap _ ?_
  have := hT.isClosed_range_smul_sub hμ
  rwa [LinearMap.coe_range, ContinuousLinearMap.coe_coe] at this

end FredholmAlternative

/-! ### The spectrum of a compact operator -/

section Spectrum

open Module.End

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- **`0` is in the spectrum of a compact operator on an infinite-dimensional Banach space**
([brezis2011functional] Theorem 6.8 (a)): otherwise `T` would be invertible and `1 = T⁻¹ ∘ T`
compact, which forces finite dimension (`isCompactOperator_id_iff_finiteDimensional`). -/
theorem zero_mem_spectrum [LocallyCompactSpace 𝕜] [CompleteSpace X] {T : X →L[𝕜] X}
    (hT : IsCompactOperator T)
    (hX : ¬ FiniteDimensional 𝕜 X) : (0 : 𝕜) ∈ spectrum 𝕜 T := by
  rw [spectrum.mem_iff, map_zero, zero_sub, IsUnit.neg_iff]
  rintro ⟨u, hu⟩
  refine hX ((isCompactOperator_id_iff_finiteDimensional (𝕜 := 𝕜) (E := X)).1 ?_)
  have h1 : ((1 : X →L[𝕜] X) : X → X) = id := rfl
  have h2 : (1 : X →L[𝕜] X) = (u⁻¹ : (X →L[𝕜] X)ˣ) ∘L T := by
    rw [← ContinuousLinearMap.mul_def, ← hu, u.inv_mul]
  rw [← h1, h2]
  exact hT.clm_comp _

/-- **The nonzero eigenvalues of a compact operator are countable** (the bookkeeping behind
[brezis2011functional] Theorem 6.8 (c)): they are the union over `n` of the finite sets of
eigenvalues of modulus at least `1 / (n + 1)`
(`IsCompactOperator.finite_setOf_hasEigenvalue_norm_le`). -/
theorem countable_setOf_hasEigenvalue {T : X →L[𝕜] X} (hT : IsCompactOperator T) :
    {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 X) μ ∧ μ ≠ 0}.Countable := by
  have hcov : {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 X) μ ∧ μ ≠ 0} ⊆
      ⋃ n : ℕ, {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 X) μ ∧ 1 / (n + 1 : ℝ) ≤ ‖μ‖} := by
    rintro μ ⟨hμ, hμ0⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hμ0)
    exact mem_iUnion.2 ⟨n, hμ, hn.le⟩
  exact (countable_iUnion fun n =>
    (hT.finite_setOf_hasEigenvalue_norm_le (by positivity)).countable).mono hcov

/-- **A sequence of distinct eigenvalues of a compact operator tends to `0`**
([brezis2011functional] Lemma 6.2, in the strengthened form that the sequence converges, to
`0`): for `ε > 0` only finitely many eigenvalues have modulus at least `ε`, so an injective
sequence of eigenvalues eventually has modulus below `ε`. -/
theorem tendsto_zero_of_injective_of_forall_hasEigenvalue {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) {f : ℕ → 𝕜} (hf : Function.Injective f)
    (hev : ∀ n, HasEigenvalue (T : Module.End 𝕜 X) (f n)) : Tendsto f atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hfin : (f ⁻¹' {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 X) μ ∧ ε ≤ ‖μ‖}).Finite :=
    (hT.finite_setOf_hasEigenvalue_norm_le hε).preimage hf.injOn
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
  by_contra h
  have hmem : n ∈ f ⁻¹' {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 X) μ ∧ ε ≤ ‖μ‖} :=
    ⟨hev n, not_lt.1 h⟩
  exact absurd (hN hmem) (by omega)

/-- **The nonzero spectrum of a compact operator is finite or a sequence tending to `0`**
([brezis2011functional] Theorem 6.8 (c); the book's case `σ(T) = {0}` is the empty instance of
"finite"): `σ(T) ∖ {0}` consists of eigenvalues
(`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`), is countable, and when infinite it is
enumerated injectively by `ℕ`, the enumeration tending to `0` by
`IsCompactOperator.tendsto_zero_of_injective_of_forall_hasEigenvalue`. -/
theorem finite_or_exists_enumeration_spectrum [CompleteSpace X] {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) :
    (spectrum 𝕜 T \ {0}).Finite ∨ ∃ f : ℕ → 𝕜, Function.Injective f ∧
      Set.range f = spectrum 𝕜 T \ {0} ∧ Tendsto f atTop (𝓝 0) := by
  have hset : spectrum 𝕜 T \ {0} = {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 X) μ ∧ μ ≠ 0} := by
    ext μ
    simp only [Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨hμ, hμ0⟩
      exact ⟨(hT.hasEigenvalue_iff_mem_spectrum hμ0).2 hμ, hμ0⟩
    · rintro ⟨hμ, hμ0⟩
      exact ⟨(hT.hasEigenvalue_iff_mem_spectrum hμ0).1 hμ, hμ0⟩
  by_cases hfin : (spectrum 𝕜 T \ {0}).Finite
  · exact Or.inl hfin
  · refine Or.inr ?_
    have hcount : (spectrum 𝕜 T \ {0}).Countable := hset ▸ hT.countable_setOf_hasEigenvalue
    obtain ⟨_⟩ := Set.countable_infinite_iff_nonempty_denumerable.1 ⟨hcount, hfin⟩
    let e : ↥(spectrum 𝕜 T \ {0}) ≃ ℕ := Denumerable.eqv _
    refine ⟨fun n => (e.symm n : 𝕜), Subtype.val_injective.comp e.symm.injective, ?_, ?_⟩
    · rw [Set.range_comp', e.symm.range_eq_univ, Set.image_univ, Subtype.range_coe]
    · refine hT.tendsto_zero_of_injective_of_forall_hasEigenvalue
        (Subtype.val_injective.comp e.symm.injective) fun n => ?_
      have hmem : ((e.symm n : 𝕜)) ∈ {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 X) μ ∧ μ ≠ 0} :=
        hset ▸ (e.symm n).2
      exact hmem.1

end Spectrum

end IsCompactOperator
