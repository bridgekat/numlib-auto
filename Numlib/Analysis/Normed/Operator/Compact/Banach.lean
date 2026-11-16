/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

This file proves the Banach-space part of [brezis2011functional], §6.1–§6.3, on top of the closure
properties, the accumulation of eigenvalues and the closed range of
`Numlib.Analysis.Normed.Operator.Compact`, and the Riesz theory of ascent and descent of
`Numlib.Analysis.Normed.Operator.Riesz`. Let $T^*$ denote the Banach adjoint of a bounded operator
$T : E \to F$, the map $F^* \to E^*$ with $T^* v = v \circ T$. Then $T$ is compact if and only if
$T^*$ is compact, when $F$ is complete (Schauder's theorem, Theorem 6.4). A compact operator maps
weakly convergent sequences to norm-convergent ones, and on a reflexive domain this property
characterizes compactness (Remark 2 of §6.1).

For a compact operator $T$ on a Banach space $X$ and $\mu \neq 0$, the operator $\mu I - T$ is
Fredholm of index zero, and a compact perturbation of a Fredholm operator is Fredholm with the same
index (property (c) in the Comments on Chapter 6). This gives the Fredholm alternative in Banach
form, $\dim N(\mu I - T) = \dim N(\mu I - T^*)$ and $R(\mu I - T) = N(\mu I - T^*)^\perp$ (Theorem
6.6(d) and (b)). Finally, $0 \in \sigma(T)$ in infinite dimension, and $\sigma(T) \setminus \{0\}$
is finite or a sequence of eigenvalues that tends to $0$ (Theorem 6.8 and Lemma 6.2).

## Main results

* `IsCompactOperator.strongDualMap`, `IsCompactOperator.of_strongDualMap`,
  `isCompactOperator_strongDualMap_iff`: **Schauder's theorem**, $T$ is compact if and only if $T^*$
  is compact.
* `IsCompactOperator.tendsto_of_tendsto_toWeakSpace`: a compact operator maps weakly convergent
  sequences to norm-convergent ones.
* `IsCompactOperator.of_forall_tendsto_of_tendsto_toWeakSpace`: on a reflexive space, an operator
  that maps weakly convergent sequences to norm-convergent ones is compact.
* `IsCompactOperator.isFredholm_smul_one_sub`, `IsCompactOperator.index_smul_one_sub`: $\mu I - T$
  is a Fredholm operator of index zero for compact $T$ and $\mu \neq 0$.
* `ContinuousLinearMap.IsFredholm.add_isCompactOperator`,
  `ContinuousLinearMap.IsFredholm.index_add_isCompactOperator`: a compact perturbation of a Fredholm
  operator is Fredholm with the same index.
* `ContinuousLinearMap.finrank_ker_strongDualMap_eq_finrank_quotient_range`: for an operator $A$
  with closed range, $\dim N(A^*)$ is the codimension of $R(A)$.
* `IsCompactOperator.finrank_ker_smul_one_sub_eq_finrank_ker_strongDualMap`:
  $\dim N(\mu I - T) = \dim N(\mu I - T^*)$.
* `IsCompactOperator.range_smul_one_sub_eq_strongDualCoannihilator_ker_strongDualMap`:
  $R(\mu I - T) = N(\mu I - T^*)^\perp$.
* `IsCompactOperator.zero_mem_spectrum`: $0 \in \sigma(T)$ in infinite dimension.
* `IsCompactOperator.countable_setOf_hasEigenvalue`: the nonzero eigenvalues are countable.
* `IsCompactOperator.tendsto_zero_of_injective_of_forall_hasEigenvalue`: a sequence of distinct
  eigenvalues tends to $0$.
* `IsCompactOperator.finite_or_exists_enumeration_spectrum`: $\sigma(T) \setminus \{0\}$ is finite
  or the range of an injective sequence that tends to $0$.

## Implementation notes

* The Banach adjoint $T^*$ is `ContinuousLinearMap.strongDualMap T` (Mathlib's
  `ContinuousLinearMap.precomp 𝕜 T`) from `Numlib.Analysis.Normed.Operator.Unbounded.Adjoint`. The
  annihilators are `Submodule.strongDualAnnihilator` and `Submodule.strongDualCoannihilator`.
* $\mu I - T$ is `μ • (1 : X →L[𝕜] X) - T`. Fredholm operators and the index are Mathlib's
  `ContinuousLinearMap.IsFredholm` and `LinearMap.index`, with index
  $= \dim N - \operatorname{codim} R$.
* The scalars are `RCLike 𝕜` where the dual, the Hahn–Banach theorem or a real homotopy enters:
  Schauder's theorem, the characterization by weak convergence, and the index. The Fredholm property
  itself is proved over a complete nontrivially normed field, through the Riesz decomposition and
  without the Hahn–Banach theorem, and so are the results on the spectrum.
* The index is constant along the path $A + tT$, $t \in \mathbb{R}$, by Mathlib's
  `ContinuousLinearMap.index_continuousOn_isFredholm`; Mathlib's Fredholm theory does not have the
  invariance of the index under compact perturbations.
* `ContinuousLinearMap.finrank_ker_strongDualMap_eq_finrank_quotient_range` identifies $N(A^*)$ with
  the dual of the cokernel of a closed-range operator, using
  `Numlib.Analysis.Normed.Module.Quotient`.
-/

open Filter Topology Metric Set Module
open scoped ContinuousLinearMap

namespace IsCompactOperator

/-! ### Schauder's theorem -/

section Schauder

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Schauder's theorem, direct half.** Let $E$ and $F$ be normed spaces over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $T : E \to F$ be a compact operator. Then the
Banach adjoint $T^* : F^* \to E^*$ is a compact operator. This is the direct half of Theorem 6.4
of [brezis2011functional]; no completeness of $E$ or $F$ is needed.

The set $T^*(B_{F^*})$ is totally bounded in the complete space $E^*$. Cover the totally bounded
set $T(B_E)$ by finitely many balls of radius $\varepsilon$ with centres $y \in t$. The values
$(v(y))_{y \in t}$ of the functionals $v$ of the unit ball of $F^*$ form a bounded, hence
totally bounded, subset of the finite-dimensional space $\mathbb{K}^t$. So finitely many
functionals $v_w$ are $\varepsilon$-close to every $v \in B_{F^*}$ at all $y \in t$, and then
$|(v - v_w)(Tu)| \le \|v - v_w\| \, \|Tu - y\| + |(v - v_w)(y)| < 3\varepsilon$ on $B_E$. -/
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

/-- **Schauder's theorem, converse half.** Let $E$ be a normed space and $F$ a Banach space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $T : E \to F$ be a bounded linear operator.
If the Banach adjoint $T^*$ is a compact operator, then $T$ is a compact operator. This is the
converse half of Theorem 6.4 of [brezis2011functional].

Let $J_E$ and $J_F$ be the canonical embeddings into the biduals. Then $T^{**} J_E = J_F T$, and
$T^{**}$ is compact by the direct half. So $J_F(T(B_E))$ lies in a compact set, and $J_F$ is a
closed embedding because $F$ is complete. -/
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

/-- **Schauder's theorem.** Let $E$ be a normed space and $F$ a Banach space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $T : E \to F$ be a bounded linear operator.
Then $T^*$ is a compact operator if and only if $T$ is a compact operator. This is Theorem 6.4
of [brezis2011functional]. -/
theorem _root_.isCompactOperator_strongDualMap_iff [CompleteSpace F] (T : E →L[𝕜] F) :
    IsCompactOperator T.strongDualMap ↔ IsCompactOperator T :=
  ⟨of_strongDualMap, strongDualMap⟩

end Schauder

/-! ### Compact operators and weak convergence -/

section Weak

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A compact operator maps weakly convergent sequences to norm-convergent ones.** Let $E$ and $F$
be normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T : E \to F$ be a compact
operator, and let $u_n \rightharpoonup x$ weakly in $E$. Then $T u_n \to T x$ in norm. This is
Remark 2 of §6.1 of [brezis2011functional].

The sequence is bounded (`exists_norm_le_of_tendsto_toWeakSpace`), so its image lies in a
compact set. Every subsequence of $(T u_n)$ has a further subsequence that converges to some
$w$, and $w = Tx$ because the functionals separate points. -/
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

/-- **The converse on a reflexive domain.** Let $E$ be a reflexive space and $F$ a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $T : E \to F$ be a bounded linear operator
such that $u_n \rightharpoonup x$ weakly implies $T u_n \to T x$ in norm, for every sequence
$(u_n)$ and every $x$. Then $T$ is a compact operator. This is the converse in Remark 2 of §6.1
of [brezis2011functional], which cites Exercise 6.7.

A bounded sequence has a weakly convergent subsequence
(`NormedSpace.exists_subseq_forall_dual_tendsto`), whose image converges by hypothesis. So the
closure of $T(B_E)$ is sequentially compact, hence compact. -/
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

/-! ### The Fredholm alternative: $\mu I - T$ is Fredholm of index zero -/

section Fredholm

open LinearMap.FiniteRangeSetoid

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **$\mu I - T$ is a Fredholm operator.** Let $X$ be a Banach space over a complete nontrivially
normed field, let $T : X \to X$ be a compact operator, and let $\mu \neq 0$. Then $\mu I - T$ is
a Fredholm operator in the sense of `ContinuousLinearMap.IsFredholm`. This is a statement in the
Comments on Chapter 6 of [brezis2011functional], item 1: "$A = I - T$ with $T \in K(E)$ is a
Fredholm operator".

No Hahn–Banach theorem is used. Let $A = \mu I - T$, with Riesz decomposition
$X = N(A^\nu) \oplus R(A^\nu)$ (`IsCompactOperator.exists_riesz_index`). The subspace $R(A^\nu)$
is closed, of finite codimension because its complement $N(A^\nu)$ is finite-dimensional, and
invariant under $A$. The operator $A$ restricts to a bijection of $R(A^\nu)$: it is injective
because $N(A) \cap R(A^\nu) \subseteq N(A^\nu) \cap R(A^\nu) = 0$, and onto because
$R(A^{\nu+1}) = R(A^\nu)$. By the open mapping theorem the restriction is an isomorphism, and
Mathlib's criterion `ContinuousLinearMap.IsFredholm.of_isInvertible_restrict` applies. -/
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

/-- **A compact perturbation of a Fredholm operator is Fredholm.** Let $X$ be a Banach space over a
complete nontrivially normed field, let $A : X \to X$ be a Fredholm operator, and let
$T : X \to X$ be a compact operator. Then $A + T$ is a Fredholm operator. This is the first
clause of property (c) in the Comments on Chapter 6 of [brezis2011functional], item 1.

Let $B$ be a quasi-inverse of $A$, with $BA = I + R$ and $R$ of finite rank. Then $B(A + T)$
agrees with $I + BT$ up to an operator of finite rank, and $I + BT$ is Fredholm because $BT$ is
compact (`IsCompactOperator.isFredholm_smul_one_sub`). The operator $B$ is Fredholm too, so
$A + T$ is Fredholm. -/
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

/-- **A compact perturbation does not change the Fredholm index.** Let $X$ be a Banach space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $A : X \to X$ be a Fredholm operator, and let
$T : X \to X$ be a compact operator. Then $$\operatorname{ind}(A + T) = \operatorname{ind}(A).$$
This is the second clause of property (c) in the Comments on Chapter 6 of
[brezis2011functional], item 1.

The path $t \mapsto A + tT$, $t \in \mathbb{R}$, consists of Fredholm operators
(`ContinuousLinearMap.IsFredholm.add_isCompactOperator`). The index is locally constant on the
Fredholm operators (`ContinuousLinearMap.index_continuousOn_isFredholm`), and hence constant on
the connected set $\mathbb{R}$. -/
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

/-- **$\mu I - T$ has Fredholm index zero.** Let $X$ be a Banach space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T : X \to X$ be a compact operator, and let
$\mu \neq 0$. Then $\operatorname{ind}(\mu I - T) = 0$. This is a statement in the Comments on
Chapter 6 of [brezis2011functional], item 1: "$A = I - T$ … is a Fredholm operator of index
zero".

The index of the invertible operator $\mu I$ is zero, and the compact perturbation $-T$ does not
change it. -/
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

/-- **The kernel of the adjoint of a closed-range operator has the dimension of the cokernel.** Let
$X$ and $Y$ be normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$A : X \to Y$ be a bounded linear operator with closed range. Then $$\dim N(A^*) = \dim (Y /
R(A)),$$ where a dimension is taken to be $0$ when the space is infinite-dimensional
(`Module.finrank`).

This is the step "$R(I - T) = N(I - T^*)^\perp$ has finite codimension $d^*$" in the proof of
Theorem 6.6(d) of [brezis2011functional]. It combines $N(A^*) = R(A)^\perp$
(`ContinuousLinearMap.ker_strongDualMap_eq_annihilator_range`) with
$\operatorname{codim} M = \dim M^\perp$ for a closed subspace $M$
(`Submodule.finrank_quotient_eq_finrank_strongDualAnnihilator`). -/
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
/-- Let $X$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T : X \to X$ be a
bounded linear operator, and let $\mu \in \mathbb{K}$. Then the Banach adjoint of $\mu I - T$ is
$\mu I - T^*$. -/
theorem _root_.ContinuousLinearMap.strongDualMap_smul_one_sub (T : X →L[𝕜] X) (μ : 𝕜) :
    (μ • (1 : X →L[𝕜] X) - T).strongDualMap =
      μ • (1 : StrongDual 𝕜 X →L[𝕜] StrongDual 𝕜 X) - T.strongDualMap := by
  rw [ContinuousLinearMap.strongDualMap_sub, ContinuousLinearMap.strongDualMap_smul,
    ContinuousLinearMap.one_def, ContinuousLinearMap.strongDualMap_id]
  rfl

/-- **The Fredholm alternative, clause (d), in Banach form.** Let $X$ be a Banach space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T : X \to X$ be a compact operator, and let
$\mu \neq 0$. Then $$\dim N(\mu I - T) = \dim N(\mu I - T^*).$$ This is Theorem 6.6(d) of
[brezis2011functional], with $\mu I$ in place of $I$.

The index of $\mu I - T$ is zero, so $\dim N(\mu I - T) = \dim (X / R(\mu I - T))$, and the
cokernel has the dimension of $N((\mu I - T)^*)$ by
`ContinuousLinearMap.finrank_ker_strongDualMap_eq_finrank_quotient_range`. -/
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
/-- **The Fredholm alternative, clause (b), in Banach form.** Let $X$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T : X \to X$ be a compact operator, and let
$\mu \neq 0$. Then $$R(\mu I - T) = N(\mu I - T^*)^\perp = \{x \in X : v(x) = 0 \text{ for every
} v \in X^* \text{ with } T^* v = \mu v\}.$$ So the equation $(\mu I - T) u = f$ is solvable if
and only if $v(f) = 0$ for every $v \in X^*$ with $T^* v = \mu v$. This is the second clause of
Theorem 6.6(b) of [brezis2011functional], with $\mu I$ in place of $I$.

No completeness is needed. The range is closed (`IsCompactOperator.isClosed_range_smul_sub`), so
`ContinuousLinearMap.range_eq_strongDualCoannihilator_ker_strongDualMap` applies. The orthogonal
$N^\perp$ of a subspace $N \subseteq X^*$ is `Submodule.strongDualCoannihilator`, a subspace of
$X$. -/
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

/-- **$0$ is in the spectrum of a compact operator on an infinite-dimensional space.** Let $X$ be a
normed space over a complete, locally compact, nontrivially normed field, and suppose that $X$
is not finite-dimensional. If $T : X \to X$ is a compact operator, then $0 \in \sigma(T)$. This
is Theorem 6.8(a) of [brezis2011functional].

Otherwise $T$ would be invertible, and $I = T^{-1} T$ would be compact, which forces finite
dimension (`isCompactOperator_id_iff_finiteDimensional`). The spectrum is `spectrum 𝕜 T` in the
algebra of bounded operators on $X$. -/
theorem zero_mem_spectrum [LocallyCompactSpace 𝕜] {T : X →L[𝕜] X}
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

/-- **The nonzero eigenvalues of a compact operator are countable.** Let $X$ be a normed space over
a complete nontrivially normed field, and let $T : X \to X$ be a compact operator. Then the set
of nonzero eigenvalues of $T$ is countable.

This is the counting step behind Theorem 6.8(c) of [brezis2011functional]. The set is the union
over $n$ of the finite sets of eigenvalues of modulus at least $1/(n + 1)$
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

/-- **A sequence of distinct eigenvalues of a compact operator tends to $0$.** Let $X$ be a normed
space over a complete nontrivially normed field, let $T : X \to X$ be a compact operator, and
let $(\mu_n)_{n \in \mathbb{N}}$ be an injective sequence of eigenvalues of $T$. Then
$\mu_n \to 0$. This is a strengthened form of Lemma 6.2 of [brezis2011functional], in which the
convergence of the sequence, to $0$, is part of the conclusion.

For $\varepsilon > 0$ only finitely many eigenvalues have modulus at least $\varepsilon$, so an
injective sequence of eigenvalues eventually has modulus less than $\varepsilon$. -/
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

/-- **The nonzero spectrum of a compact operator is finite or a sequence that tends to $0$.** Let
$X$ be a Banach space over a complete nontrivially normed field, and let $T : X \to X$ be a
compact operator. Then either $\sigma(T) \setminus \{0\}$ is finite, or there is an injective
sequence $(\mu_n)_{n \in \mathbb{N}}$ with $\{\mu_n : n \in \mathbb{N}\} = \sigma(T) \setminus
\{0\}$ and $\mu_n \to 0$. This is Theorem 6.8(c) of [brezis2011functional]; the case
$\sigma(T) = \{0\}$ of the book is the case of the empty finite set.

The set $\sigma(T) \setminus \{0\}$ consists of eigenvalues
(`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`) and is countable. When it is infinite, it
has an injective enumeration by $\mathbb{N}$, which tends to $0$ by
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
