/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Compact`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Collectively compact families of operators

A family $(K_i)_{i \in \iota}$ of bounded linear operators $V \to W$ is **collectively compact**
when there is a neighbourhood $U$ of the origin such that $\bigcup_i K_i(U)$ has compact closure.
This is the exact analogue of Mathlib's `IsCompactOperator`, so that a constant family is
collectively compact precisely when its member is a compact operator.

The point of the notion is that a collectively compact family with $K_n \to K$ pointwise satisfies
$\|(K - K_n) K_n\| \to 0$, although $\|K - K_n\|$ need not tend to zero. This makes the Nyström
method for integral equations of the second kind stable, and it is the hypothesis of Anselone's
perturbation theorem. This is the theory of Anselone [anselone1971collectively], as presented in
[han2009theoretical], Section 12.4.3 (assumptions A1–A3 and Lemma 12.4.7) and Section 12.1 (Lemmas
12.1.3 and 12.1.4).

The file also proves the two consequences of the Banach–Steinhaus theorem on which both this theory
and the theory of projection methods rest. A pointwise convergent sequence of bounded operators on a
Banach space converges uniformly on every compact set. Hence $\|A_n M\| \to 0$ whenever $A_n \to 0$
pointwise and $M$ is a compact operator. With $A_n = I - P_n$ this is the estimate
$\|K - P_n K\| \to 0$ that makes a projection method for an equation of the second kind convergent,
and with $A_n = K - K_n$ it is one clause of the lemma on collective compactness.

## Main definitions

* `IsCollectivelyCompact`: a family of operators maps one neighbourhood of the origin into a
  relatively compact set.

## Main results

* `tendstoUniformlyOn_of_tendsto_of_isCompact`: pointwise convergence of bounded operators on a
  Banach space is uniform on compact sets.
* `tendsto_opNorm_comp_of_isCompactOperator`: if $A_n \to 0$ pointwise and $M$ is compact, then
  $\|A_n M\| \to 0$.
* `IsCollectivelyCompact.isCompactOperator`, `isCollectivelyCompact_const_iff`,
  `IsCollectivelyCompact.comp`: each member of a collectively compact family is compact, a constant
  family is collectively compact if and only if its member is compact, and a reindexed family is
  collectively compact.
* `IsCollectivelyCompact.isCompactOperator_of_tendsto`: a pointwise limit of a collectively compact
  sequence is a compact operator.
* `IsCollectivelyCompact.exists_opNorm_le`: a collectively compact family is uniformly bounded.
* `IsCollectivelyCompact.tendsto_opNorm_sub_comp`: if $K_n \to L$ pointwise, then
  $\|(L - K_n) K_n\| \to 0$.
-/

open Filter Topology Metric Set Bornology

section OpNorm

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Let $V$ and $W$ be normed spaces over a nontrivially normed field, let $c$ be a scalar with
$\|c\| > 1$, and let $r > 0$ and $C \ge 0$. If a continuous linear map $f : V \to W$ satisfies
$\|f x\| \le C$ for every $x$ with $\|x\| < r$, then $\|f\| \le \|c\| C / r$. The factor $\|c\|$
is needed over a general nontrivially normed field, whose norm need not take the value $1$. -/
theorem ContinuousLinearMap.opNorm_le_of_forall_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {f : V →L[𝕜] W}
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (h : ∀ x : V, ‖x‖ < r → ‖f x‖ ≤ C) : ‖f‖ ≤ ‖c‖ / r * C := by
  refine ContinuousLinearMap.opNorm_le_of_shell hr (by positivity) hc fun x hx hlt => ?_
  refine (h x hlt).trans ?_
  calc C = ‖c‖ / r * C * (r / ‖c‖) := by field_simp
    _ ≤ ‖c‖ / r * C * ‖x‖ := mul_le_mul_of_nonneg_left hx (by positivity)

end OpNorm

section UniformOnCompact

variable {𝕜 U V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Pointwise convergence of bounded operators is uniform on compact sets.** Let $V$ be a Banach
space and $W$ a normed space over a nontrivially normed field, and let
$L, A_0, A_1, \dots : V \to W$ be bounded linear operators with $A_n x \to L x$ for every
$x \in V$. Then $A_n \to L$ uniformly on every compact set $S \subseteq V$. This is Lemma 12.1.3
of [han2009theoretical].

The uniform boundedness principle makes the family equicontinuous, and equicontinuity turns a
finite net of a compact set into a uniform estimate. -/
theorem tendstoUniformlyOn_of_tendsto_of_isCompact [CompleteSpace V] {A : ℕ → V →L[𝕜] W}
    {L : V →L[𝕜] W} (hA : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (L x)))
    {S : Set V} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n => (A n : V → W)) L atTop S := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ n, ‖A n‖ ≤ M := by
    refine banach_steinhaus fun x => ?_
    obtain ⟨C, hC⟩ :=
      isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (hA x))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (A 0)) (hM 0)
  obtain ⟨C, hCpos, hCge⟩ : ∃ C : ℝ, 0 < C ∧ ‖L‖ + M ≤ C :=
    ⟨M + ‖L‖ + 1, by linarith [norm_nonneg L], by linarith⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, htf, hts⟩ :=
    Metric.totallyBounded_iff.1 hS.totallyBounded (ε / (3 * C)) (by positivity)
  have hev : ∀ᶠ n in atTop, ∀ y ∈ t, ‖L y - A n y‖ < ε / 3 := by
    rw [htf.eventually_all]
    intro y _
    have h0 : Tendsto (fun n => L y - A n y) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := L y)).sub (hA y)
    exact NormedAddGroup.tendsto_nhds_zero.1 h0 (ε / 3) (by positivity)
  filter_upwards [hev] with n hn x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hts hx)
  rw [mem_ball, dist_eq_norm] at hxy
  rw [dist_eq_norm]
  have hsplit : L x - A n x = L (x - y) + (L y - A n y) + A n (y - x) := by
    simp only [map_sub]
    abel
  have h1 : ‖L (x - y)‖ ≤ ‖L‖ * (ε / (3 * C)) :=
    (L.le_opNorm _).trans (by gcongr)
  have h2 : ‖A n (y - x)‖ ≤ M * (ε / (3 * C)) := by
    refine ((A n).le_opNorm _).trans ?_
    rw [norm_sub_rev]
    exact mul_le_mul (hM n) hxy.le (norm_nonneg _) hM0
  have h3 := hn y hy
  have hkey : ‖L x - A n x‖ ≤ ‖L (x - y)‖ + ‖L y - A n y‖ + ‖A n (y - x)‖ := by
    rw [hsplit]
    exact norm_add₃_le
  have hfrac : ‖L‖ * (ε / (3 * C)) + M * (ε / (3 * C)) ≤ ε / 3 := by
    rw [← add_mul]
    calc (‖L‖ + M) * (ε / (3 * C)) ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hCge (by positivity)
      _ = ε / 3 := by field_simp
  linarith

/-- Let $U$ be a normed space, $V$ a Banach space and $W$ a normed space over a nontrivially normed
field. Let $A_0, A_1, \dots : V \to W$ be bounded linear operators with $A_n x \to 0$ for every
$x \in V$, and let $M : U \to V$ be a compact operator. Then $$\|A_n M\| \to 0.$$

This is Lemma 12.1.4 of [han2009theoretical], with $A_n = I - P_n$ for pointwise convergent
projections $P_n$, which gives $\|K - P_n K\| \to 0$ for compact $K$. It is also Lemma 12.4.7(3)
of [han2009theoretical], with $A_n = K - K_n$. The norm of $A_n M$ is controlled by the values
of $A_n$ on the relatively compact image under $M$ of a ball, and on that set the convergence is
uniform. -/
theorem tendsto_opNorm_comp_of_isCompactOperator [CompleteSpace V] {A : ℕ → V →L[𝕜] W}
    (hA : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 0)) {M : U →L[𝕜] V}
    (hM : IsCompactOperator M) :
    Tendsto (fun n => ‖A n ∘L M‖) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hMc : IsCompact (closure (M '' closedBall (0 : U) 1)) :=
    (isCompactOperator_iff_isCompact_closure_image_closedBall (M : U →ₗ[𝕜] V) one_pos).1 hM
  have hA0 : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (((0 : V →L[𝕜] W) : V → W) x)) := by
    simpa using hA
  have hunif : TendstoUniformlyOn (fun n => (A n : V → W)) ((0 : V →L[𝕜] W) : V → W) atTop
      (closure (M '' closedBall 0 1)) :=
    tendstoUniformlyOn_of_tendsto_of_isCompact hA0 hMc
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε / (2 * ‖c‖)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hbound : ∀ x : U, ‖x‖ < 1 → ‖(A n ∘L M) x‖ ≤ ε / (2 * ‖c‖) := by
    intro x hx
    have hmem : M x ∈ closure (M '' closedBall (0 : U) 1) :=
      subset_closure ⟨x, mem_closedBall_zero_iff.2 hx.le, rfl⟩
    have hd := hN n hn (M x) hmem
    simp only [zero_apply, dist_zero_left] at hd
    rw [ContinuousLinearMap.comp_apply]
    exact hd.le
  refine lt_of_le_of_lt
    (ContinuousLinearMap.opNorm_le_of_forall_norm_lt hc one_pos (by positivity) hbound) ?_
  have heq : ‖c‖ / 1 * (ε / (2 * ‖c‖)) = ε / 2 := by
    rw [div_one]
    field_simp
  rw [heq]
  linarith

end UniformOnCompact

/-- **Collectively compact family.** Let $V$ and $W$ be normed spaces over a nontrivially normed
field. A family $(K_i)_{i \in \iota}$ of bounded linear operators $V \to W$ is **collectively
compact** if there is a neighbourhood $U$ of $0$ in $V$ such that the closure of
$\bigcup_{i \in \iota} K_i(U)$ is compact.

This is the exact analogue of Mathlib's `IsCompactOperator` for a family. A constant family is
collectively compact precisely when its member is a compact operator
(`isCollectivelyCompact_const_iff`). It is assumption A3 of the theory of collectively compact
operator approximations in [han2009theoretical], Section 12.4.3. -/
def IsCollectivelyCompact {ι 𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (K : ι → V →L[𝕜] W) : Prop :=
  ∃ U ∈ 𝓝 (0 : V), IsCompact (closure (⋃ i, K i '' U))

namespace IsCollectivelyCompact

section Family

variable {ι ι' 𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {K : ι → V →L[𝕜] W}

/-- Every member $K_i$ of a collectively compact family is a compact operator. -/
theorem isCompactOperator (hK : IsCollectivelyCompact K) (i : ι) : IsCompactOperator (K i) := by
  obtain ⟨U, hU, hcpt⟩ := hK
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2 ⟨U, hU, _, hcpt, ?_⟩
  exact (subset_iUnion (fun j => K j '' U) i).trans subset_closure

/-- If $(K_i)_{i \in \iota}$ is collectively compact and $f : \iota' \to \iota$ is any map, then
$(K_{f(j)})_{j \in \iota'}$ is collectively compact. In particular, a subfamily of a
collectively compact family is collectively compact. -/
theorem comp (hK : IsCollectivelyCompact K) (f : ι' → ι) : IsCollectivelyCompact (K ∘ f) := by
  obtain ⟨U, hU, hcpt⟩ := hK
  refine ⟨U, hU, hcpt.of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
  exact iUnion_subset fun j => subset_iUnion (fun i => K i '' U) (f j)

end Family

end IsCollectivelyCompact

section Const

variable {ι 𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Let $\iota$ be nonempty and let $T : V \to W$ be a bounded linear operator. The constant family
$(T)_{i \in \iota}$ is collectively compact if and only if $T$ is a compact operator. -/
theorem isCollectivelyCompact_const_iff [Nonempty ι] {T : V →L[𝕜] W} :
    IsCollectivelyCompact (fun _ : ι => T) ↔ IsCompactOperator T := by
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image]
  simp only [IsCollectivelyCompact, iUnion_const]

end Const

namespace IsCollectivelyCompact

section Limit

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **A pointwise limit of a collectively compact sequence is a compact operator.** Let $V$ and $W$
be normed spaces over a nontrivially normed field, and let $(K_n)_{n \in \mathbb{N}}$ be a
collectively compact sequence of bounded linear operators $V \to W$. If $L : V \to W$ is a
bounded linear operator with $K_n x \to L x$ for every $x$, then $L$ is a compact operator. This
is Lemma 12.4.7(1) of [han2009theoretical].

The image under $L$ of the neighbourhood of the origin in the definition lies in the compact set
of the definition. -/
theorem isCompactOperator_of_tendsto {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {K : ℕ → V →L[𝕜] W} {L : V →L[𝕜] W} (hK : IsCollectivelyCompact K)
    (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) :
    IsCompactOperator L := by
  obtain ⟨U, hU, hcpt⟩ := hK
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2 ⟨U, hU, _, hcpt, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine isClosed_closure.mem_of_tendsto (hL x) (Eventually.of_forall fun n => ?_)
  exact subset_closure (mem_iUnion.2 ⟨n, ⟨x, hx, rfl⟩⟩)

/-- **A collectively compact family is uniformly bounded.** If $(K_i)_{i \in \iota}$ is a
collectively compact family of bounded linear operators between normed spaces, then there is $C$
with $\|K_i\| \le C$ for all $i$. This is Lemma 12.4.7(2) of [han2009theoretical].

The compact set of the definition is bounded. -/
theorem exists_opNorm_le {ι W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {K : ι → V →L[𝕜] W} (hK : IsCollectivelyCompact K) : ∃ C, ∀ i, ‖K i‖ ≤ C := by
  obtain ⟨U, hU, hcpt⟩ := hK
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hcpt.isBounded
  refine ⟨‖c‖ / r * max M 0, fun i =>
    ContinuousLinearMap.opNorm_le_of_forall_norm_lt hc hr (le_max_right _ _) fun x hx => ?_⟩
  exact (hM _ (subset_closure
    (mem_iUnion.2 ⟨i, ⟨x, hrU (mem_ball_zero_iff.2 hx), rfl⟩⟩))).trans (le_max_left _ _)

/-- **The estimate behind collectively compact approximation.** Let $V$ be a Banach space over a
nontrivially normed field, let $(K_n)_{n \in \mathbb{N}}$ be a collectively compact sequence of
bounded linear operators on $V$, and let $L$ be a bounded linear operator on $V$ with
$K_n x \to L x$ for every $x$. Then $$\|(L - K_n) K_n\| \to 0,$$ although $\|L - K_n\|$ need not
tend to zero. This is Lemma 12.4.7(4) of [han2009theoretical]. -/
theorem tendsto_opNorm_sub_comp [CompleteSpace V] {K : ℕ → V →L[𝕜] V} {L : V →L[𝕜] V}
    (hK : IsCollectivelyCompact K) (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) :
    Tendsto (fun n => ‖(L - K n) ∘L K n‖) atTop (𝓝 0) := by
  obtain ⟨U, hU, hcpt⟩ := hK
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hunif : TendstoUniformlyOn (fun n => (K n : V → V)) L atTop (closure (⋃ i, K i '' U)) :=
    tendstoUniformlyOn_of_tendsto_of_isCompact hL hcpt
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε * r / (2 * ‖c‖)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hbound : ∀ x : V, ‖x‖ < r → ‖((L - K n) ∘L K n) x‖ ≤ ε * r / (2 * ‖c‖) := by
    intro x hx
    have hmem : K n x ∈ closure (⋃ i, K i '' U) :=
      subset_closure (mem_iUnion.2 ⟨n, ⟨x, hrU (mem_ball_zero_iff.2 hx), rfl⟩⟩)
    have hd := hN n hn (K n x) hmem
    rw [dist_eq_norm] at hd
    simpa using hd.le
  refine lt_of_le_of_lt
    (ContinuousLinearMap.opNorm_le_of_forall_norm_lt hc hr (by positivity) hbound) ?_
  have heq : ‖c‖ / r * (ε * r / (2 * ‖c‖)) = ε / 2 := by field_simp
  rw [heq]
  linarith

end Limit

end IsCollectivelyCompact
