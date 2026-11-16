/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.Analysis.Normed.Module.BestApprox`, beside `Metric.infDist`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Best approximation from a subset of a normed space

Let $K$ be a subset of a seminormed space $V$ and let $u \in V$. An element $v \in K$ is a **best
approximation** of $u$ from $K$ if $\|u - v\| \le \|u - w\|$ for every $w \in K$, that is, if
$\|u - v\| = \operatorname{dist}(u, K)$. The map that sends $u$ to its best approximation is the
metric projection onto $K$. This module proves that best approximations exist from
finite-dimensional subspaces ([han2009theoretical], Theorem 3.3.16; [kress1998numerical], Theorem
3.50) and from nonempty closed subsets of finite-dimensional subspaces ([han2009theoretical],
Theorem 3.3.15), and that they are unique from convex sets in strictly convex spaces
([han2009theoretical], Theorem 3.3.21). In an inner product space, it characterizes the best
approximation from a convex set by a variational inequality, and the best approximation from a
subspace as the orthogonal projection ([han2009theoretical], Lemma 3.4.1 and Theorem 3.4.6;
[kress1998numerical], Theorem 3.51).

It also proves the Lebesgue lemma for a bounded projection $P$ with range $S$: $\|u - Pu\| \le (1 +
\|P\|) \operatorname{dist}(u, S)$ ([han2009theoretical], (3.7.11), (3.7.14) and (3.7.21)). This is
the abstract form of the quasi-optimality estimates of projection methods.

## Main definitions

* `IsBestApprox`: $v \in K$ minimizes $\|u - v\|$ over $K$. By
  `isBestApprox_iff_norm_sub_eq_infDist` it is equivalent to
  $\|u - v\| = \operatorname{dist}(u, K)$, so either form can serve as the definition.
* `bestApprox`: the metric projection $P_K u$ as a function: a best approximation of $u$ from $K$
  when one exists, and $u$ otherwise.

## Main results

* `exists_isBestApprox_of_finiteDimensional`,
  `exists_isBestApprox_of_isClosed_of_finiteDimensional`: best approximations exist from a
  finite-dimensional subspace, and from a nonempty closed subset of a finite-dimensional subspace.
* `convex_setOf_isBestApprox`: the best approximations from a convex set form a convex set.
* `IsBestApprox.unique`: in a strictly convex space, the best approximation from a convex set is
  unique.
* `isBestApprox_iff_inner_le_zero`: in a real inner product space, $v$ is the best approximation
  from a convex set $K$ if and only if $\langle u - v, w - v \rangle \le 0$ for all $w \in K$.
* `IsBestApprox.dist_le_dist`: the metric projection onto a convex set in a real inner product space
  is monotone and nonexpansive.
* `isBestApprox_iff_mem_orthogonal`, `isBestApprox_starProjection`,
  `IsBestApprox.eq_starProjection`: the best approximation from a subspace $K$ is characterized by
  $u - v \in K^\perp$, and it is the orthogonal projection.
* `isBestApprox_sum_iff`: the normal equations for the best approximation from a span.
* `norm_sub_apply_le_of_isIdempotentElem`: the Lebesgue lemma $\|u - Pu\| \le (1 + \|P\|)
  \operatorname{dist}(u, \operatorname{range} P)$, with the sharper form
  `norm_sub_apply_le_of_isIdempotentElem'` with the constant $\|I - P\|$.
* `one_le_norm_of_isIdempotentElem`: a nonzero bounded projection has norm at least $1$.

## Implementation notes

* `bestApprox K u` is defined in every seminormed space without hypotheses, so that it can always be
  written. The theorems carry the hypotheses. In a strictly convex space and for convex $K$, it is
  the unique best approximation whenever a best approximation exists (`IsBestApprox.bestApprox_eq`,
  `bestApprox_eq_self_of_mem`). It is the projection $P_K$ of [brezis2011functional], §5.1, and of
  [han2009theoretical], §3.4. Its theory in Hilbert spaces (existence, the variational
  characterization, nonexpansiveness) is in `Numlib.Analysis.InnerProductSpace.ConvexProjection`.
* The characterizations in inner product spaces connect `IsBestApprox` with Mathlib's orthogonal
  projection `Submodule.starProjection` and with `norm_eq_iInf_iff_real_inner_le_zero`.
* The results are general facts about normed and inner product spaces, without approximation theory
  in them. The approximation, Fourier, eigenvalue and variational modules of the library use them as
  the abstract form of a quasi-optimality estimate.
-/

section Normed

variable {V : Type*} [SeminormedAddCommGroup V]

/-- Let $K$ be a subset of a seminormed group $V$ and let $u \in V$. An element $v$ is a **best
approximation** of $u$ from $K$ if $v \in K$ and
$$\|u - v\| \le \|u - w\| \quad \text{for every } w \in K.$$
-/
def IsBestApprox (K : Set V) (u v : V) : Prop := v ∈ K ∧ ∀ w ∈ K, ‖u - v‖ ≤ ‖u - w‖

/-- If $v$ is a best approximation of $u$ from $K$, then $\|u - v\| = \operatorname{dist}(u, K)$:
the infimum that defines `Metric.infDist` is a minimum, attained at $v$. -/
theorem IsBestApprox.norm_sub_eq_infDist {K : Set V} {u v : V} (h : IsBestApprox K u v) :
    ‖u - v‖ = Metric.infDist u K := by
  refine le_antisymm ((Metric.le_infDist ⟨v, h.1⟩).2 fun w hw => ?_) ?_
  · rw [dist_eq_norm]; exact h.2 w hw
  · rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem h.1

/-- Let $v \in K$. Then $v$ is a best approximation of $u$ from $K$ if and only if
$\|u - v\| = \operatorname{dist}(u, K)$. So the pointwise minimality of `IsBestApprox` and the
metric description agree, and either can serve as the definition. -/
theorem isBestApprox_iff_norm_sub_eq_infDist {K : Set V} {u v : V} (hv : v ∈ K) :
    IsBestApprox K u v ↔ ‖u - v‖ = Metric.infDist u K := by
  refine ⟨IsBestApprox.norm_sub_eq_infDist, fun h => ⟨hv, fun w hw => ?_⟩⟩
  rw [h, ← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem hw

open scoped Classical in
/-- The **metric projection** of $u$ onto $K$, written $P_K u$ in [brezis2011functional], §5.1 (the
notation after Theorem 5.2), and in [han2009theoretical], §3.4. It is a best approximation of
$u$ from $K$ when one exists, and it is $u$ otherwise.

The definition needs no hypotheses, so that $P_K u$ can always be written. The theorems carry
the hypotheses: existence in a Hilbert space for a nonempty closed convex set $K$, and
uniqueness in a strictly convex space. -/
noncomputable def bestApprox (K : Set V) (u : V) : V :=
  if h : ∃ v, IsBestApprox K u v then h.choose else u

/-- If a best approximation of $u$ from $K$ exists, then `bestApprox K u` is a best approximation of
$u$ from $K$. -/
theorem isBestApprox_bestApprox {K : Set V} {u : V} (h : ∃ v, IsBestApprox K u v) :
    IsBestApprox K u (bestApprox K u) := by
  rw [bestApprox, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

end Normed

section Real

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- If $a + b = 1$, then $a (u - v_1) + b (u - v_2) = u - (a v_1 + b v_2)$. -/
private theorem sub_combo {a b : ℝ} (hab : a + b = 1) (u v₁ v₂ : V) :
    a • (u - v₁) + b • (u - v₂) = u - (a • v₁ + b • v₂) := by
  rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]

/-- Let $V$ be a real seminormed space, let $K \subseteq V$ be convex, and let $u \in V$. Then the
set of best approximations of $u$ from $K$ is convex. This is Theorem 3.3.12 of
[han2009theoretical]. -/
theorem convex_setOf_isBestApprox {K : Set V} (hK : Convex ℝ K) (u : V) :
    Convex ℝ {v | IsBestApprox K u v} := by
  rintro v₁ h₁ v₂ h₂ a b ha hb hab
  refine ⟨hK h₁.1 h₂.1 ha hb hab, fun w hw => ?_⟩
  have h₂₁ : ‖u - v₂‖ ≤ ‖u - v₁‖ := h₂.2 _ h₁.1
  calc ‖u - (a • v₁ + b • v₂)‖ = ‖a • (u - v₁) + b • (u - v₂)‖ := by rw [sub_combo hab]
    _ ≤ a * ‖u - v₁‖ + b * ‖u - v₂‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ (a + b) * ‖u - v₁‖ := by nlinarith
    _ ≤ ‖u - w‖ := by rw [hab, one_mul]; exact h₁.2 w hw

end Real

section Existence

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Let $V$ be a normed space over a locally compact nontrivially normed field, let $S$ be a
finite-dimensional subspace of $V$, and let $K \subseteq S$ be closed and nonempty. Then every
$u \in V$ has a best approximation from $K$. This is Theorem 3.3.15 of [han2009theoretical].

The proof uses that closed bounded subsets of the finite-dimensional subspace $S$ are compact.
No convexity of $K$ is needed. -/
theorem exists_isBestApprox_of_isClosed_of_finiteDimensional
    [LocallyCompactSpace 𝕜] {K : Set V} (hK : IsClosed K) (hne : K.Nonempty) (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (u : V) :
    ∃ v, IsBestApprox K u v := by
  obtain ⟨v₀, hv₀⟩ := hne
  have : ProperSpace S := FiniteDimensional.proper 𝕜 S
  have hcont : Continuous fun w : S => ‖u - (w : V)‖ :=
    (continuous_const.sub continuous_subtype_val).norm
  have hTc : IsCompact {w : S | (w : V) ∈ K ∧ ‖u - (w : V)‖ ≤ ‖u - v₀‖} := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((hK.preimage continuous_subtype_val).inter (isClosed_le hcont continuous_const)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : S)) (r := ‖u‖ + ‖u - v₀‖)).subset ?_
    rintro w ⟨-, hw⟩
    have hb : ‖(w : V)‖ ≤ ‖u‖ + ‖u - v₀‖ :=
      calc ‖(w : V)‖ = ‖u - (u - (w : V))‖ := by rw [sub_sub_cancel]
        _ ≤ ‖u‖ + ‖u - (w : V)‖ := norm_sub_le _ _
        _ ≤ ‖u‖ + ‖u - v₀‖ := by gcongr
    simpa [Metric.mem_closedBall, dist_zero_right] using hb
  obtain ⟨w, hwT, hmin⟩ := hTc.exists_isMinOn ⟨⟨v₀, hKS hv₀⟩, hv₀, le_rfl⟩ hcont.continuousOn
  refine ⟨(w : V), hwT.1, fun z hz => ?_⟩
  by_cases hz' : ‖u - z‖ ≤ ‖u - v₀‖
  · exact isMinOn_iff.1 hmin ⟨z, hKS hz⟩ ⟨hz, hz'⟩
  · exact hwT.2.trans (not_le.1 hz').le

/-- Let $V$ be a normed space over a complete, locally compact nontrivially normed field, and let
$K$ be a finite-dimensional subspace of $V$. Then every $u \in V$ has a best approximation from
$K$. This is Theorem 3.3.16 of [han2009theoretical] and Theorem 3.50 of [kress1998numerical]. -/
theorem exists_isBestApprox_of_finiteDimensional [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜]
    (K : Submodule 𝕜 V) [FiniteDimensional 𝕜 K] (u : V) :
    ∃ v, IsBestApprox (K : Set V) u v :=
  exists_isBestApprox_of_isClosed_of_finiteDimensional K.closed_of_finiteDimensional
    ⟨0, K.zero_mem⟩ K le_rfl u

end Existence

section Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]

/-- Let $V$ be a strictly convex real normed space and let $K \subseteq V$ be convex. If $v_1$ and
$v_2$ are best approximations of $u$ from $K$, then $v_1 = v_2$. This is Theorem 3.3.21 of
[han2009theoretical]. -/
theorem IsBestApprox.unique {K : Set V} (hK : Convex ℝ K) {u v₁ v₂ : V} (h₁ : IsBestApprox K u v₁)
    (h₂ : IsBestApprox K u v₂) : v₁ = v₂ := by
  by_contra hne
  have hab : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  have hlt : ‖(2 : ℝ)⁻¹ • (u - v₁) + (2 : ℝ)⁻¹ • (u - v₂)‖ < ‖u - v₁‖ :=
    norm_combo_lt_of_ne le_rfl (h₂.2 _ h₁.1) (fun h => hne (sub_right_injective h))
      (by norm_num) (by norm_num) hab
  rw [sub_combo hab] at hlt
  exact absurd (h₁.2 _ (hK h₁.1 h₂.1 (by norm_num) (by norm_num) hab)) (not_le.2 hlt)

/-- Let $V$ be a strictly convex real normed space and let $K \subseteq V$ be convex. If $v$ is a
best approximation of $u$ from $K$, then the metric projection is $P_K u = v$: the element $v$
shows that a best approximation exists, and best approximations are unique. -/
theorem IsBestApprox.bestApprox_eq {K : Set V} (hK : Convex ℝ K) {u v : V}
    (h : IsBestApprox K u v) : bestApprox K u = v :=
  (isBestApprox_bestApprox ⟨v, h⟩).unique hK h

/-- Let $V$ be a strictly convex real normed space and let $K \subseteq V$ be convex. Every
$u \in K$ is its own metric projection: $P_K u = u$. -/
theorem bestApprox_eq_self_of_mem {K : Set V} (hK : Convex ℝ K) {u : V} (hu : u ∈ K) :
    bestApprox K u = u :=
  IsBestApprox.bestApprox_eq hK ⟨hu, fun w _ => by rw [sub_self, norm_zero]; exact norm_nonneg _⟩

end Uniqueness

section RealHilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Let $V$ be a real inner product space, let $K \subseteq V$ be convex, and let $v \in K$. Then
$v$ is a best approximation of $u$ from $K$ if and only if
$$\langle u - v, w - v \rangle \le 0 \quad \text{for every } w \in K.$$
This is Lemma 3.4.1 of [han2009theoretical].

The proof uses Mathlib's `norm_eq_iInf_iff_real_inner_le_zero`. -/
theorem isBestApprox_iff_inner_le_zero {K : Set V} (hK : Convex ℝ K) {u v : V} (hv : v ∈ K) :
    IsBestApprox K u v ↔ ∀ w ∈ K, inner ℝ (u - v) (w - v) ≤ 0 := by
  rw [isBestApprox_iff_norm_sub_eq_infDist hv, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  exact norm_eq_iInf_iff_real_inner_le_zero hK hv

/-- Let $V$ be a real inner product space and let $K \subseteq V$ be convex. If $v_1$ and $v_2$ are
best approximations from $K$ of $u_1$ and $u_2$, then
$$\langle v_1 - v_2, u_1 - u_2 \rangle \ge 0 \quad \text{and} \quad \|v_1 - v_2\| \le \|u_1 -
  u_2\|.$$
So the metric projection onto a convex set is monotone and nonexpansive. This is Proposition
3.4.4 of [han2009theoretical]. -/
theorem IsBestApprox.dist_le_dist {K : Set V} (hK : Convex ℝ K) {u₁ u₂ v₁ v₂ : V}
    (h₁ : IsBestApprox K u₁ v₁) (h₂ : IsBestApprox K u₂ v₂) :
    0 ≤ inner ℝ (v₁ - v₂) (u₁ - u₂) ∧ ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ := by
  have e₁ := (isBestApprox_iff_inner_le_zero hK h₁.1).1 h₁ v₂ h₂.1
  have e₂ := (isBestApprox_iff_inner_le_zero hK h₂.1).1 h₂ v₁ h₁.1
  have expand : inner ℝ (u₁ - v₁) (v₂ - v₁) + inner ℝ (u₂ - v₂) (v₁ - v₂)
      = ‖v₁ - v₂‖ ^ 2 - inner ℝ (v₁ - v₂) (u₁ - u₂) := by
    rw [← real_inner_self_eq_norm_sq, real_inner_comm (v₂ - v₁) (u₁ - v₁),
      real_inner_comm (v₁ - v₂) (u₂ - v₂)]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have key : ‖v₁ - v₂‖ ^ 2 ≤ inner ℝ (v₁ - v₂) (u₁ - u₂) := by linarith
  refine ⟨(sq_nonneg _).trans key, ?_⟩
  rcases (norm_nonneg (v₁ - v₂)).eq_or_lt with h | h
  · rw [← h]; exact norm_nonneg _
  · nlinarith [real_inner_le_norm (v₁ - v₂) (u₁ - u₂)]

end RealHilbert

section Hilbert

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Let $V$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$, and let
$(u_j)_{j \in \iota}$ be a family in $V$. A vector $x$ lies in the orthogonal complement of the
span of the $u_j$ if and only if $\langle u_j, x \rangle = 0$ for every $j$. -/
theorem Submodule.mem_orthogonal_span_range_iff {ι : Type*} (u : ι → V) (x : V) :
    x ∈ (Submodule.span 𝕜 (Set.range u))ᗮ ↔ ∀ j, inner 𝕜 (u j) x = 0 := by
  rw [Submodule.mem_orthogonal']
  refine ⟨fun h j => inner_eq_zero_symm.1 (h _ (Submodule.subset_span (Set.mem_range_self j))),
    fun h y hy => ?_⟩
  have hle : Submodule.span 𝕜 (Set.range u) ≤
      LinearMap.ker ((innerSL 𝕜 x : V →L[𝕜] 𝕜) : V →ₗ[𝕜] 𝕜) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    exact fun j => inner_eq_zero_symm.2 (h j)
  exact hle hy

/-- Let $V$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$, let $K$ be a subspace of
$V$, and let $v \in K$. Then $v$ is a best approximation of $u$ from $K$ if and only if
$u - v \in K^\perp$. This is Theorem 3.4.6 of [han2009theoretical] and Theorem 3.51 of
[kress1998numerical]. -/
theorem isBestApprox_iff_mem_orthogonal (K : Submodule 𝕜 V) {u v : V} (hv : v ∈ K) :
    IsBestApprox (K : Set V) u v ↔ u - v ∈ Kᗮ := by
  rw [isBestApprox_iff_norm_sub_eq_infDist hv, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rw [Submodule.mem_orthogonal']
  exact K.norm_eq_iInf_iff_inner_eq_zero hv

/-- Let $V$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$, and let $K$ be a subspace
of $V$ that has an orthogonal projection $P_K$. Then $P_K u$ is a best approximation of $u$ from
$K$. This is Theorems 3.4.6 and 3.4.7 of [han2009theoretical] and Theorem 3.52 of
[kress1998numerical].

The orthogonal projection is Mathlib's `Submodule.starProjection`, under the hypothesis
`Submodule.HasOrthogonalProjection`. -/
theorem isBestApprox_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] (u : V) :
    IsBestApprox (K : Set V) u (K.starProjection u) :=
  (isBestApprox_iff_mem_orthogonal K (K.starProjection_apply_mem u)).2
    (K.sub_starProjection_mem_orthogonal u)

/-- Let $V$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$, and let $K$ be a subspace
of $V$ that has an orthogonal projection $P_K$. If $v$ is a best approximation of $u$ from $K$,
then $v = P_K u$. With `isBestApprox_starProjection`, this identifies the metric projection onto
a closed subspace of a Hilbert space with the orthogonal projection `Submodule.starProjection`. -/
theorem IsBestApprox.eq_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] {u v : V}
    (h : IsBestApprox (K : Set V) u v) : v = K.starProjection u :=
  (Submodule.eq_starProjection_of_mem_orthogonal h.1
    ((isBestApprox_iff_mem_orthogonal K h.1).1 h)).symm

/-- The **normal equations**. Let $V$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$,
let $(u_i)_{i \in \iota}$ be a finite family in $V$, let $(a_i)_{i \in \iota}$ be scalars, and
let $w \in V$. Then $\sum_i a_i u_i$ is a best approximation of $w$ from the span of the $u_i$
if and only if
$$\sum_i a_i \langle u_j, u_i \rangle = \langle u_j, w \rangle \quad \text{for every } j.$$
This is Corollary 3.53 of [kress1998numerical].

The vectors $u_i$ need not be linearly independent. -/
theorem isBestApprox_sum_iff {ι : Type*} [Fintype ι] (u : ι → V) (a : ι → 𝕜) (w : V) :
    IsBestApprox (Submodule.span 𝕜 (Set.range u) : Set V) w (∑ i, a i • u i) ↔
      ∀ j, ∑ i, a i * inner 𝕜 (u j) (u i) = inner 𝕜 (u j) w := by
  rw [isBestApprox_iff_mem_orthogonal _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))),
    Submodule.mem_orthogonal_span_range_iff]
  simp only [inner_sub_right, inner_sum, inner_smul_right]
  exact forall_congr' fun _ => by rw [sub_eq_zero, eq_comm]

end Hilbert

section Lebesgue

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Let $S$ be a nonempty subset of a normed space $V$, let $C \ge 0$, and let $u \in V$. If
$r \le C \|u - q\|$ for every $q \in S$, then $r \le C \operatorname{dist}(u, S)$. -/
theorem Metric.le_mul_infDist {C r : ℝ} {u : V} {S : Set V} (hC : 0 ≤ C) (hS : S.Nonempty)
    (h : ∀ q ∈ S, r ≤ C * ‖u - q‖) : r ≤ C * Metric.infDist u S := by
  rcases hC.lt_or_eq with hC' | hC'
  · refine (div_le_iff₀' hC').1 ((Metric.le_infDist hS).2 fun q hq => ?_)
    rw [dist_eq_norm, div_le_iff₀' hC']
    exact h q hq
  · obtain ⟨q, hq⟩ := hS
    have := h q hq
    rw [← hC'] at this ⊢
    simpa using this

/-- Let $P$ be a bounded linear operator on a normed space $V$ with $P^2 = P$, and let $q$ be in the
range of $P$. Then for every $u \in V$,
$$\|u - Pu\| \le (1 + \|P\|) \|u - q\|.$$
-/
theorem norm_sub_apply_le_of_isIdempotentElem_of_mem (P : V →L[𝕜] V) (hP : IsIdempotentElem P)
    (u : V) {q : V} (hq : q ∈ LinearMap.range (P : V →ₗ[𝕜] V)) :
    ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - q‖ := by
  have key : u - P u = (u - q) - P (u - q) := by
    rw [map_sub, show P q = q from
      (LinearMap.IsIdempotentElem.mem_range_iff
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).1 hq]; abel
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  rw [add_mul, one_mul]
  gcongr
  exact P.le_opNorm _

/-- The **Lebesgue lemma**. Let $P$ be a bounded linear operator on a normed space $V$ with
$P^2 = P$, and let $S$ be the range of $P$. Then for every $u \in V$,
$$\|u - Pu\| \le (1 + \|P\|) \operatorname{dist}(u, S).$$
So $Pu$ is a quasi-best approximation of $u$ from $S$, with the quasi-optimality constant
$1 + \|P\|$.

This is the abstract form of the estimates (3.7.11), (3.7.14) and (3.7.21) of
[han2009theoretical] for particular projection methods. -/
theorem norm_sub_apply_le_of_isIdempotentElem (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ (1 + ‖P‖) * Metric.infDist u (LinearMap.range (P : V →ₗ[𝕜] V) : Set V) :=
  Metric.le_mul_infDist (by positivity) ⟨0, zero_mem _⟩ fun _ hq =>
    norm_sub_apply_le_of_isIdempotentElem_of_mem P hP u hq

/-- Let $P$ be a bounded linear operator on a normed space $V$ with $P^2 = P$, and let $S$ be the
range of $P$. Then for every $u \in V$,
$$\|u - Pu\| \le \|I - P\| \operatorname{dist}(u, S).$$
This is sharper than `norm_sub_apply_le_of_isIdempotentElem`, because $\|I - P\| \le 1 + \|P\|$. -/
theorem norm_sub_apply_le_of_isIdempotentElem' (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ ‖(1 : V →L[𝕜] V) - P‖ *
      Metric.infDist u (LinearMap.range (P : V →ₗ[𝕜] V) : Set V) := by
  refine Metric.le_mul_infDist (norm_nonneg _) ⟨0, zero_mem _⟩ fun q hq => ?_
  have key : u - P u = ((1 : V →L[𝕜] V) - P) (u - q) := by
    change u - P u = (u - q) - P (u - q)
    rw [map_sub, show P q = q from
      (LinearMap.IsIdempotentElem.mem_range_iff
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).1 hq]; abel
  rw [key]
  exact ((1 : V →L[𝕜] V) - P).le_opNorm _

/-- Let $P$ be a bounded linear operator on a normed space with $P^2 = P$ and $P \ne 0$. Then
$\|P\| \ge 1$. This is Exercise 3.6.7 of [han2009theoretical]. -/
theorem one_le_norm_of_isIdempotentElem {P : V →L[𝕜] V} (hP : IsIdempotentElem P) (h0 : P ≠ 0) :
    1 ≤ ‖P‖ := by
  have hpos : 0 < ‖P‖ := norm_pos_iff.2 h0
  have hle : ‖P‖ ≤ ‖P‖ * ‖P‖ := by
    conv_lhs => rw [← hP]
    exact norm_mul_le P P
  nlinarith

end Lebesgue
