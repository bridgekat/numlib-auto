/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, beside the embeddings of
`Numlib/Analysis/Sobolev/EmbeddingDomain.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.EmbeddingDomain
import Numlib.Analysis.Sobolev.Extension
import Numlib.MeasureTheory.Function.LpSpace.KolmogorovRiesz
import Numlib.Topology.ContinuousMap.ArzelaAscoli

/-!
# The Rellich–Kondrachov theorem

Let $\Omega \subseteq \mathbb{R}^N$ be open, let $1 \le p < \infty$, and for $p < N$ let $p^*$ be
the Sobolev exponent, $1/p^* = 1/p - 1/N$. An injection between normed spaces is compact when it is
a compact embedding: a bounded injective linear map that sends every bounded sequence to a sequence
with a convergent subsequence. The **Rellich–Kondrachov theorem**, Theorem 9.16 of
[brezis2011functional], says that for a bounded open set $\Omega$ of class $C^1$ the injections
$$W^{1,p}(\Omega) \subset L^q(\Omega),\ q \in [1, p^*), \text{ if } p < N, \qquad
W^{1,p}(\Omega) \subset L^q(\Omega),\ q \in [p, \infty), \text{ if } p = N,$$
$$W^{1,p}(\Omega) \subset C(\overline{\Omega}) \text{ if } p > N$$
are compact, and in particular that $W^{1,p}(\Omega) \subset L^p(\Omega)$ is compact. This file
proves these clauses.

The file also proves several extensions. At $q = p$ no case distinction is needed:
$W^{1,p}(\Omega) \subset L^p(\Omega)$ is compact for every $1 \le p < \infty$, in every dimension,
on every extension domain of finite measure. On $W_0^{1,p}(\Omega)$ the clauses of Theorem 9.16 hold
for an arbitrary open set of finite measure, with no regularity of $\Omega$ (Remark 20 of Chapter 9
of [brezis2011functional]); this gives the compactness of $H_0^1(\Omega) \subset L^2(\Omega)$ that
the proofs of Theorems 9.23 and 9.31 use. At higher order, on an extension domain of finite measure,
the injection $W^{k+1,p}(\Omega) \subset W^{k,p}(\Omega)$ is compact, and $W^{k,p}(\Omega)$ embeds
compactly in $L^q(\Omega)$ or $C(\overline{\Omega})$ for $k < N/p$, $k = N/p$ and $k > N/p$; these
are Theorems 7.3.8 and 7.3.9 of [han2009theoretical] under the extension hypothesis. Finally, for
$p = \infty$, the injection $W^{k,\infty}(\Omega) \subset W^{l,\infty}(\Omega)$ for $l < k$ is
compact on a bounded $W^{1,\infty}$-extension domain.

## Main definitions

* `ContinuousMap.extendZero`: the extension by zero to the whole space of a continuous function on a
  subset $K$.
* `ContinuousMap.extendZeroToLpL`: extension by zero as a bounded linear map
  $C(K, \mathbb{R}) \to L^p(\Omega)$, for a compact $K \supseteq \Omega$ and $\mu(\Omega) < \infty$.

## Main results

* `HasSobolevExtensionOn.isCompactEmbedding_toLpOn_of_le_of_lt`: a subspace $S$ of $W^{1,p}(\Omega)$
  with an extension operator, on a set of finite measure, embeds compactly in $L^q(\Omega)$ for
  $p \le q < p^*$.
* `SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn`: the same for $1 \le q < p^*$.
* `HasSobolevExtensionOn.isCompactEmbedding_toLpOn_self`: such a subspace embeds compactly in
  $L^p(\Omega)$ for every $1 \le p < \infty$ and every $N$.
* `SobolevEuclidean.isCompactEmbedding_toLp_of_lt`: Theorem 9.16 for $p < N$ and $1 \le q < p^*$.
* `SobolevEuclidean.isCompactEmbedding_toLp_of_le`,
  `SobolevEuclidean.isCompactEmbedding_toLp_of_eq`: Theorem 9.16 for $N \ge 2$, $p \ge N$ and every
  $1 \le q < \infty$.
* `SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt`: Theorem 9.16 for $p > N$, into
  $C(K)$ for a compact $K \supseteq \Omega$.
* `SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one`,
  `SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one`: $W^{1,p}(\Omega) \subset L^p(\Omega)$ is
  compact on a bounded $C^1$ domain unless $N = 1 = p$.
* `SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain`:
  $W^{1,p}(\Omega) \subset L^p(\Omega)$ is compact on every extension domain of finite measure.
* `SobolevEuclideanZero.isCompactEmbedding_toLp`, `SobolevEuclideanZero.isCompactOperator_fnL`:
  $W_0^{1,p}(\Omega) \subset L^p(\Omega)$ is compact on every open set of finite measure.
* `SobolevEuclideanZero.isCompactEmbedding_toLp_of_lt`,
  `SobolevEuclideanZero.isCompactEmbedding_toLp_of_eq`,
  `SobolevEuclideanZero.isCompactEmbedding_toContinuousMapOnL`: the other clauses of Theorem 9.16 on
  $W_0^{1,p}(\Omega)$.
* `SobolevMultiIndex.isCompactEmbedding_of_forall_weakDeriv_eq`: the inductive step from
  $W^{k+1,p} \subset W^{k,p}$ to $W^{k+2,p} \subset W^{k+1,p}$.
* `SobolevEuclidean.isCompactEmbedding_toLower_of_lt`,
  `SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain`,
  `SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt`:
  $W^{k,p}(\Omega) \subset W^{l,p}(\Omega)$ is compact for $l < k$.
* `SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_lt`,
  `SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_eq`,
  `SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`: the compact embeddings of
  $W^{k,p}(\Omega)$ into $L^q(\Omega)$ and $C(K)$ for $k < N/p$, $k = N/p$ and $k > N/p$.
* `SobolevEuclidean.isCompactEmbedding_fnL_top`,
  `SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt`: the compact embeddings
  $W^{1,\infty}(\Omega) \subset L^\infty(\Omega)$ and $W^{k,\infty}(\Omega) \subset
  W^{l,\infty}(\Omega)$, $l < k$.

## Proof outline

The case $p < N$ is proved for a subspace $S$ of $W^{1,p}(\Omega)$ with an extension operator
$P : S \to W^{1,p}(\mathbb{R}^N)$, on a set $\Omega$ of finite measure. The family
$\mathcal{F} = P(B_S)$, the image of the unit ball, is bounded in $L^q(\mathbb{R}^N)$ by Corollary
9.10 of [brezis2011functional], and it has a uniform modulus of continuity under translation in
$L^q$: Proposition 9.3 gives it in $L^p$, and interpolation with the $L^{p^*}$ bound gives it in
$L^q$. The Kolmogorov–M. Riesz–Fréchet theorem then makes the restrictions to $\Omega$ relatively
compact, and these restrictions are the image of $B_S$. For $q < p$ the case $q = p$ is composed
with the continuous inclusion $L^p(\Omega) \subset L^q(\Omega)$. At $q = p$ the interpolation is not
needed, so this case holds for every $p$. The cases $p \ge N$ with $N \ge 2$ reduce to $p < N$
through a continuous injection $W^{1,p}(\Omega) \subset W^{1,r}(\Omega)$ with $r < N$ and $r^* > q$.
The case $p > N$ is the Arzelà–Ascoli theorem for the uniformly bounded and uniformly Hölder
continuous representatives. The higher orders follow by induction on $k$: for a bounded sequence
$u_n$, one subsequence makes $u_n$ and all $\partial_i u_n$ converge in $W^{k,p}(\Omega)$, so that
every $\partial^\beta u_n$ converges in $L^p(\Omega)$. The case $p = \infty$ is the Arzelà–Ascoli
theorem for the Lipschitz representatives.

## Implementation notes

* A compact embedding is `IsCompactEmbedding` of `Numlib.Analysis.Normed.Operator.Embedding`. The
  injections into $L^q(\Omega)$ are `SobolevMultiIndex.toLpₗ` for the whole space and
  `SobolevMultiIndex.toLpₗOn` for a subspace, and `SobolevMultiIndex.fnL` at $q = p$. The injections
  into $C(K)$ are `HasSobolevExtensionOn.toContinuousMapOnL` and `SobolevEuclidean.toContinuousMapL`
  of `Numlib.Analysis.Sobolev.EmbeddingDomain`, which take the continuous representative. The
  injection $W^{k,p}(\Omega) \to W^{l,p}(\Omega)$ is `SobolevMultiIndex.toLowerOrderL`.
* Where the membership of $u$ in $L^q(\Omega)$ is not automatic, a statement takes it as a
  hypothesis or asserts that it holds, because the maps into $L^q(\Omega)$ need it as an argument.
* The exponents $p$ and $q$ are finite (`ℝ≥0`) with $1 \le p$, except in the statements for
  $p = \infty$ and in the general lemmas. The Sobolev exponent $p^*$ is a variable `p'` with the
  hypothesis $1/p' = 1/p - 1/N$.
* The space $C(\overline{\Omega})$ is $C(K, \mathbb{R})$ for a compact set $K \supseteq \Omega$,
  typically $K = \overline{\Omega}$.
* An open set of class $C^1$ is `IsContDiffChartDomain 1` (by local charts), and the dimension of
  these statements is written $N = d + 1$. A bounded $C^1$ domain is an extension domain by Theorem
  9.7 of [brezis2011functional] (`IsSobolevExtensionDomain.of_isContDiffChartDomain`). For every
  exponent at once this is `IsSobolevExtensionDomainAll.of_isContDiffChartDomain`, the hypothesis of
  Corollary 9.15.
* On a bounded $C^1$ domain, `SobolevEuclidean.isCompactEmbedding_toLp_self` covers
  $W^{1,p}(\Omega) \subset L^p(\Omega)$ for $p < N$ or $N \ge 2$, and
  `SobolevEuclidean.isCompactEmbedding_toLp_self_of_gt` adds $N = 1 < p$ through
  $C(\overline{\Omega})$ and extension by zero. This leaves out only $N = 1 = p$, where $\Omega$ is
  a union of intervals and the one-dimensional theory applies.
  `SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain` covers $N = 1 = p$ on
  extension domains.
* The results of [han2009theoretical] are stated on Lipschitz domains. Here they are proved on
  extension domains, which include the bounded $C^1$ domains.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

/-! ### The abstract Rellich–Kondrachov lemma -/

section Rellich

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- **Uniform translation estimate in $L^q$ for a bounded set of $W^{1,p}(\mathbb{R}^N)$.** Let
$1 \le p < N$, let $p^*$ be given by $1/p^* = 1/p - 1/N$, let $p \le q < p^*$, and let
$M \in \mathbb{R}$. Then there are $\theta > 0$ and $K < \infty$ such that every
$v \in W^{1,p}(\mathbb{R}^N)$ with $\|v\| \le M$ satisfies
$$\|\tau_h v - v\|_{L^q(\mathbb{R}^N)} \le \|h\|^\theta K \qquad \text{for all } h \in
  \mathbb{R}^N,$$
where $(\tau_h v)(x) = v(x + h)$.

This is the estimate in the proof of Theorem 9.16 of [brezis2011functional]. Proposition 9.3
bounds $\|\tau_h v - v\|_p$, Corollary 9.10 gives $\|\tau_h v - v\|_{p^*} \le 2 \|v\|_{p^*}$
with a bound on $\|v\|_{p^*}$, and the interpolation inequality between $L^p$ and $L^{p^*}$
combines the two. In the proof $\theta \in (0, 1]$ is the interpolation parameter of $q$ between
$p$ and $p^*$; the statement asserts only $\theta > 0$. The constant $K$ depends only on $M$,
$p$, $q$ and $N$. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_sub_translate_le {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q < p') (M : ℝ) :
    ∃ (θ : ℝ) (K : ℝ≥0∞), 0 < θ ∧ K ≠ ⊤ ∧ ∀ v : SobolevEuclidean N 1 p ⊤, ‖v‖ ≤ M →
      ∀ h : EuclideanSpace ℝ (Fin N),
        eLpNorm (fun x ↦ fn v (x + h) - fn v x) q volume ≤ ‖h‖ₑ ^ θ * K := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_inv_eq_ofReal_mul_inv_add (r := (q : ℝ≥0∞))
    (q := (p' : ℝ≥0∞)) hp0 (by exact_mod_cast hpq) (by exact_mod_cast hqp'.le)
  have hθpos : 0 < θ := by
    rcases hθ0.eq_or_lt with rfl | h
    · exfalso
      simp only [ENNReal.ofReal_zero, zero_mul, sub_zero, ENNReal.ofReal_one, one_mul,
        zero_add] at hθ
      exact hqp'.ne (by exact_mod_cast inv_inj.1 hθ)
    · exact h
  set A : ℝ≥0∞ := N * ENNReal.ofReal M with hA
  set B : ℝ≥0∞ := 2 * ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N * M) with hB
  have hAt : A ≠ ⊤ := by
    rw [hA]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hBt : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  refine ⟨θ, A ^ θ * B ^ (1 - θ), hθpos,
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ0 hAt)
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hBt), fun v hv h ↦ ?_⟩
  have hg : AEStronglyMeasurable (fn v) volume := (SobolevEuclidean.memLp_fn v).aestronglyMeasurable
  have hgh : AEStronglyMeasurable (fun x ↦ fn v (x + h)) volume :=
    hg.comp_quasiMeasurePreserving (measurePreserving_add_right volume h).quasiMeasurePreserving
  -- the `L^p` translation estimate
  have h1 : eLpNorm (fun x ↦ fn v (x + h) - fn v x) p volume ≤ ‖h‖ₑ * A := by
    refine (SobolevEuclidean.eLpNorm_fn_sub_translate_le ENNReal.coe_ne_top v h).trans ?_
    refine mul_le_mul' le_rfl ((SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le v).trans ?_)
    rw [hA]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hv)
  -- the `L^{p*}` bound
  have h2 : eLpNorm (fun x ↦ fn v (x + h) - fn v x) p' volume ≤ B := by
    have hsub : (fun x ↦ fn v (x + h) - fn v x) = (fun x ↦ fn v (x + h)) - fn v := by
      funext x
      simp
    rw [hsub]
    refine (eLpNorm_sub_le (hp1.trans (by exact_mod_cast hpq.trans hqp'.le))).trans ?_
    rw [eLpNorm_comp_add_right hg h, ← two_mul, hB]
    refine mul_le_mul' le_rfl ((SobolevEuclidean.eLpNorm_fn_le_norm_of_eq hpN hp' v).trans ?_)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hv (by positivity))
  -- interpolation
  calc eLpNorm (fun x ↦ fn v (x + h) - fn v x) q volume
      ≤ eLpNorm (fun x ↦ fn v (x + h) - fn v x) p volume ^ θ
        * eLpNorm (fun x ↦ fn v (x + h) - fn v x) p' volume ^ (1 - θ) :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (hgh.sub hg) hθ0 hθ1 hθ
    _ ≤ (‖h‖ₑ * A) ^ θ * B ^ (1 - θ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow h1 hθ0) (ENNReal.rpow_le_rpow h2 (by linarith))
    _ = ‖h‖ₑ ^ θ * (A ^ θ * B ^ (1 - θ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0, mul_assoc]

/-- Let $\theta > 0$, $K < \infty$ and $\varepsilon > 0$. Then there is $\delta > 0$ such that
$\|h\|^\theta K < \varepsilon$ for every $h \in \mathbb{R}^N$ with $\|h\| < \delta$. -/
theorem EuclideanSpace.exists_pos_forall_enorm_rpow_mul_lt {θ : ℝ} (hθ : 0 < θ) {K : ℝ≥0∞}
    (hK : K ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ < δ → ‖h‖ₑ ^ θ * K < ε := by
  have hlim : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ ^ θ * K) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ ^ θ) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ) (𝓝 0) (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))
      have := ((ENNReal.continuous_rpow_const (y := θ)).tendsto (0 : ℝ≥0∞)).comp h0
      rw [ENNReal.zero_rpow_of_pos hθ] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hK)
  obtain ⟨δ, hδ, hδ0⟩ := ((hlim.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ0, fun h hh ↦ lt_of_le_of_lt ?_ hδ⟩
  rw [← ofReal_norm]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hh.le) hθ.le) le_rfl

/-- Let $S$ be a subspace of $W^{1,p}(\Omega)$ and let $P : S \to W^{1,p}(\mathbb{R}^N)$ be a
bounded linear map with $Pu = u$ almost everywhere on $\Omega$ for every $u \in S$. Let
$q \ge 1$, and suppose that every $u \in S$ lies in $L^q(\Omega)$ and every $Pu$ lies in
$L^q(\mathbb{R}^N)$. Then the image of $u \in S$ in $L^q(\Omega)$ is the restriction to $\Omega$
of $Pu \in L^q(\mathbb{R}^N)$.

Thus the image of the unit ball of $S$ in $L^q(\Omega)$ is the set of restrictions to $\Omega$
of the family $\mathcal{F} = P(B_S)$ in the proof of Theorem 9.16 of [brezis2011functional]. The
restriction is `MeasureTheory.Lp.restrictCLM`. -/
theorem HasSobolevExtensionOn.toLpₗOn_eq_restrictCLM [Fact (1 ≤ (q : ℝ≥0∞))]
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤)
    (hP : ∀ u : S, fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fn (u : SobolevEuclidean N 1 p Ω))
    (h : ∀ u : S, MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hmem : ∀ u : S, MemLp (fn (P u)) q volume) (u : S) :
    toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S h u
      = Lp.restrictCLM ℝ ℝ q volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ((hmem u).toLp _) := by
  refine Lp.ext ((toLpₗOn_coeFn h u).trans ?_)
  have e1 : fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      (hmem u).toLp (fn (P u)) :=
    Filter.EventuallyEq.symm (ae_restrict_of_ae (MemLp.coeFn_toLp (hmem u)))
  exact ((hP u).symm.trans e1).trans (Lp.coeFn_restrictCLM _ _).symm

/-- Let $S$ be a subspace of $W^{1,p}(\Omega)$, let $P : S \to W^{1,p}(\mathbb{R}^N)$ be a bounded
linear map, let $1 \le p < N$, let $1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. Then the
family $\mathcal{F} = \{Pu : u \in S,\ \|u\| \le 1\}$ is bounded in $L^q(\mathbb{R}^N)$.

This is a step of the proof of Theorem 9.16 of [brezis2011functional], by Corollary 9.10. -/
theorem HasSobolevExtensionOn.isBounded_image_closedBall [Fact (1 ≤ (q : ℝ≥0∞))]
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    Bornology.IsBounded ((fun u : S ↦
      (SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp' (P u)).toLp _) ''
        closedBall (0 : S) 1) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨(1 + SobolevEuclidean.gnsConst N p * N) * ‖P‖, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hPu : ‖P u‖ ≤ ‖P‖ := by
    calc ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖P‖ := mul_one _
  have hC0 : (0 : ℝ) ≤ 1 + SobolevEuclidean.gnsConst N p * N :=
    add_nonneg zero_le_one (mul_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg _))
  have hb := SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' (P u)
  rw [mem_closedBall_zero_iff, Lp.norm_toLp]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg hC0 (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left hPu hC0

/-- Let $S$ be a subspace of $W^{1,p}(\Omega)$, let $P : S \to W^{1,p}(\mathbb{R}^N)$ be a bounded
linear map, let $1 \le p < N$, let $1/p^* = 1/p - 1/N$, and let $p \le q < p^*$. Then the family
$\mathcal{F} = \{Pu : u \in S,\ \|u\| \le 1\}$, viewed in $L^q(\mathbb{R}^N)$, is uniformly
continuous under translation: for every $\varepsilon > 0$ there is $\delta > 0$ such that
$$\|\tau_h f - f\|_{L^q(\mathbb{R}^N)} < \varepsilon \qquad \text{for all } f \in \mathcal{F}
  \text{ and all } h \text{ with } \|h\| < \delta.$$

This is the hypothesis of the Kolmogorov–M. Riesz–Fréchet theorem in the proof of Theorem 9.16
of [brezis2011functional]. It follows from
`SobolevEuclidean.exists_forall_eLpNorm_fn_sub_translate_le`. -/
theorem HasSobolevExtensionOn.uniform_translate_image_closedBall
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q < p') :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ (fun u : S ↦
      (SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _) ''
        closedBall (0 : S) 1, ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ < δ →
          eLpNorm (fun x ↦ f (x + h) - f x) q volume < ε := by
  obtain ⟨θ, K, hθ, hK, hmod⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_sub_translate_le (q := q) hpN hp' hpq hqp' ‖P‖
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := EuclideanSpace.exists_pos_forall_enorm_rpow_mul_lt (N := N) hθ hK hε
  refine ⟨δ, hδ0, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ h hh
  have hPu : ‖P u‖ ≤ ‖P‖ := by
    calc ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖P‖ := mul_one _
  have hGae := MemLp.coeFn_toLp (SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u))
  have hae : (fun x ↦ ((SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _)
        (x + h) - ((SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _) x)
      =ᵐ[volume] fun x ↦ fn (P u) (x + h) - fn (P u) x := by
    have h1 := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hGae
    filter_upwards [h1, hGae] with x hx1 hx2
    simp only [Function.comp_apply] at hx1
    rw [hx1, hx2]
  rw [eLpNorm_congr_ae hae]
  exact (hmod (P u) hPu h).trans_lt (hδ h hh)

/-- **The abstract Rellich–Kondrachov lemma for $p \le q < p^*$.** Let
$\Omega \subseteq \mathbb{R}^N$ be open with finite measure, let $1 \le p < N$, let
$1/p^* = 1/p - 1/N$, and let $p \le q < p^*$. Let $S$ be a subspace of $W^{1,p}(\Omega)$ that
has a Sobolev extension operator. Then the injection $S \subset L^q(\Omega)$ is a compact
embedding.

This is the case $p < N$ of Theorem 9.16 of [brezis2011functional], in the generality of its
proof. The extension operator is `HasSobolevExtensionOn S`. The image of the unit ball is the
set of restrictions to $\Omega$ of the family $\mathcal{F} = P(B_S) \subseteq
W^{1,p}(\mathbb{R}^N)$, which is bounded in $L^q(\mathbb{R}^N)$ by Corollary 9.10 and uniformly
continuous under translation in $L^q$ by
`SobolevEuclidean.exists_forall_eLpNorm_fn_sub_translate_le`. The Kolmogorov–M. Riesz–Fréchet
theorem `MeasureTheory.Lp.isCompact_closure_image_restrictCLM_of_uniform_translate` then makes
the restrictions relatively compact. -/
theorem HasSobolevExtensionOn.isCompactEmbedding_toLpOn_of_le_of_lt [Fact (1 ≤ (q : ℝ≥0∞))]
    (hS : HasSobolevExtensionOn S) (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q < p') :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le)) := by
  obtain ⟨P, hP⟩ := id hS
  have hcont := hS.isContinuousEmbedding_toLpOn_of_le_of_le hpN hp' hpq hqp'.le
  obtain ⟨ι, hι⟩ : ∃ ι : S →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ι = hcont.toContinuousLinearMap := ⟨_, rfl⟩
  have hιapply : ∀ u : S, ι u = Lp.restrictCLM ℝ ℝ q volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
      ((SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _) := by
    intro u
    rw [hι, IsContinuousEmbedding.coe_toContinuousLinearMap]
    exact HasSobolevExtensionOn.toLpₗOn_eq_restrictCLM P hP _
      (fun u ↦ SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)) u
  have himg : ⇑ι '' closedBall 0 1 = Lp.restrictCLM ℝ ℝ q volume
      (Ω : Set (EuclideanSpace ℝ (Fin N))) '' ((fun u : S ↦
        (SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _) ''
          closedBall (0 : S) 1) := by
    rw [Set.image_image]
    exact Set.image_congr fun u _ ↦ hιapply u
  have hK' : IsCompact (closure (⇑ι '' closedBall 0 1)) := by
    rw [himg]
    exact Lp.isCompact_closure_image_restrictCLM_of_uniform_translate ENNReal.coe_ne_top
      (HasSobolevExtensionOn.isBounded_image_closedBall P hpN hp' hpq hqp'.le)
      (HasSobolevExtensionOn.uniform_translate_image_closedBall P hpN hp' hpq hqp') hΩ
  have := isCompactEmbedding_of_isCompact_closure_image_closedBall (hι ▸ hcont.injective) hK'
  rw [hι] at this
  exact this

end Rellich

/-! ### Theorem 9.16, the case $p < N$, for $1 \le q < p^*$ -/

section RellichLt

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open with finite measure, let $1 \le p < N$, let
$1/p^* = 1/p - 1/N$, and let $q \le p^*$. Let $S$ be a subspace of $W^{1,p}(\Omega)$ that has a
Sobolev extension operator. Then every $u \in S$ lies in $L^q(\Omega)$.

For $q \le p$ this is the inclusion $L^p(\Omega) \subset L^q(\Omega)$ on a set of finite
measure, and for $p \le q \le p^*$ it is Corollary 9.14 of [brezis2011functional]. -/
theorem HasSobolevExtensionOn.memLp_fn_of_le_sobolevConj (hS : HasSobolevExtensionOn S)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q ≤ p') (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  rcases le_or_gt p q with hpq | hqp
  · exact hS.memLp_fn_of_le_of_le hpN hp' hpq hqp' u
  · have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      isFiniteMeasure_restrict.2 hΩ
    exact (SobolevMultiIndex.memLp (u : SobolevEuclidean N 1 p Ω)).mono_exponent
      (by exact_mod_cast hqp.le)

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- Let $0 < p < N$ and let $1/p^* = 1/p - 1/N$. Then $p < p^*$. -/
theorem NNReal.lt_sobolevConj {p' : ℝ≥0} (hp0 : 0 < p) (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) : p < p' := by
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (NNReal.coe_nonneg p) (by exact_mod_cast hpN)
  have hp'0 : (0 : ℝ) < (p' : ℝ)⁻¹ := by
    rw [hp', sub_pos]
    exact inv_strictAnti₀ (by exact_mod_cast hp0) (by exact_mod_cast hpN)
  have h : (p' : ℝ)⁻¹ < (p : ℝ)⁻¹ := by
    rw [hp']
    exact sub_lt_self _ (by positivity)
  have := (inv_lt_inv₀ (inv_pos.1 hp'0) (by exact_mod_cast hp0)).1 h
  exact_mod_cast this

/-- **The abstract Rellich–Kondrachov lemma.** Let $\Omega \subseteq \mathbb{R}^N$ be open with
finite measure, let $1 \le p < N$, let $1/p^* = 1/p - 1/N$, and let $1 \le q < p^*$. Let $S$ be
a subspace of $W^{1,p}(\Omega)$ that has a Sobolev extension operator. Then the injection
$S \subset L^q(\Omega)$ is a compact embedding.

This is the case $p < N$ of Theorem 9.16 of [brezis2011functional], in the generality of its
proof. The injection is `SobolevMultiIndex.toLpₗOn`. For $q \ge p$ this is
`HasSobolevExtensionOn.isCompactEmbedding_toLpOn_of_le_of_lt`. For $q < p$ it is the case
$q = p$ followed by the continuous inclusion $L^p(\Omega) \subset L^q(\Omega)$, as in the proof
of the source: "since $\Omega$ is bounded, we may always assume that $q \ge p$". -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn [Fact (1 ≤ (q : ℝ≥0∞))]
    (hS : HasSobolevExtensionOn S) (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q < p') :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_of_le_sobolevConj hΩ hpN hp' hqp'.le)) := by
  rcases le_or_gt p q with hpq | hqp
  · exact hS.isCompactEmbedding_toLpOn_of_le_of_lt hΩ hpN hp' hpq hqp'
  · have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      isFiniteMeasure_restrict.2 hΩ
    have hp0 : 0 < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
    have hc := hS.isCompactEmbedding_toLpOn_of_le_of_lt hΩ hpN hp' le_rfl
      (NNReal.lt_sobolevConj hp0 hpN hp')
    have hqp' : (q : ℝ≥0∞) ≤ p := by exact_mod_cast hqp.le
    have hmono := Lp.isContinuousEmbedding_monoExponentL (G := ℝ)
      (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) hqp'
    have hcomp := hc.comp_isContinuousEmbedding hmono
    convert hcomp using 1
    refine LinearMap.ext fun u ↦ Lp.ext ?_
    refine (toLpₗOn_coeFn _ u).trans ?_
    refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_monoExponentL hqp' _).symm
    exact (toLpₗOn_coeFn _ u).symm

end RellichLt

/-! ### Theorem 9.16 on the whole space $W^{1,p}(\Omega)$ of a bounded $C^1$ domain -/

section RellichTop

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Let $1 \le p, q \le \infty$, and suppose that every $u \in W^{k,p}(\Omega)$ lies in
$L^q(\Omega)$. If the injection into $L^q(\Omega)$ of the subspace $W^{k,p}(\Omega)$ of itself
is a compact embedding, then so is the injection $W^{k,p}(\Omega) \subset L^q(\Omega)$.

The two maps differ by the identification of $W^{k,p}(\Omega)$ with its subspace `⊤`. The
statement holds on an open subset $\Omega$ of a normed space $E$ with a measure $\mu$ and a
basis $b$, for functions with values in a normed space $F$. -/
theorem SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Ω : Opens E} {μ : Measure E}
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E)))
    (hc : IsCompactEmbedding (toLpₗOn F b k p Ω μ ⊤ fun u ↦ h u)) :
    IsCompactEmbedding (toLpₗ F b k p Ω μ h) := by
  have hι : IsContinuousEmbedding ((LinearMap.id (R := ℝ)).codRestrict
      (⊤ : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)) fun _ ↦ Submodule.mem_top) :=
    ⟨fun u v huv ↦ by simpa using congrArg Subtype.val huv, 1, fun u ↦ by simp⟩
  have := hι.comp_isCompactEmbedding hc
  convert this using 1
  exact LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn h u).trans
    (toLpₗOn_coeFn (S := ⊤) (fun u ↦ h u) ⟨u, Submodule.mem_top⟩).symm)

/-- **The Rellich–Kondrachov theorem for $p < N$.** Let $N \ge 1$, let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, let $1 \le p < N$, let
$1/p^* = 1/p - 1/N$, and let $1 \le q < p^*$. Then the injection
$W^{1,p}(\Omega) \subset L^q(\Omega)$ is compact. This is Theorem 9.16 of
[brezis2011functional], the case $p < N$.

The dimension is written $N = d + 1$, and the class $C^1$ is `IsContDiffChartDomain 1`. The
proof applies `SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn` with
$S = W^{1,p}(\Omega)$ and the extension operator of Theorem 9.7
(`IsSobolevExtensionDomain.of_isContDiffChartDomain`). A bounded $\Omega$ has a bounded boundary
and finite measure. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_lt {d : ℕ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) {p' : ℝ≥0}
    (hpN : p < ((d + 1 : ℕ) : ℝ≥0)) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹)
    (hqp' : q < p') :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      fun u ↦ (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
        (hb.closure.subset frontier_subset_closure)).memLp_fn_of_le_sobolevConj
          hb.measure_lt_top.ne hpN hp' hqp'.le ⟨u, Submodule.mem_top⟩) :=
  SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top _
    (SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn
      (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
        (hb.closure.subset frontier_subset_closure)) hb.measure_lt_top.ne hpN hp' hqp')

end RellichTop

/-! ### Theorem 9.16, the case $p > N$: Arzelà–Ascoli -/

section RellichGt

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- **The abstract Rellich–Kondrachov lemma for $p > N$.** Let $N < p < \infty$, let $S$ be a
subspace of $W^{1,p}(\Omega)$ that has a Sobolev extension operator, and let
$K \supseteq \Omega$ be compact. Then the map $S \to C(K, \mathbb{R})$ that takes the continuous
representative is a compact embedding.

This is the case $p > N$ of Theorem 9.16 of [brezis2011functional], in the generality of its
proof. The map is `HasSobolevExtensionOn.toContinuousMapOnL`. The image of the unit ball is
bounded in the supremum norm and uniformly Hölder continuous, hence equicontinuous, and $K$ is
compact, so the Arzelà–Ascoli theorem `ContinuousMap.isCompact_closure_of_forall_norm_le`
applies. -/
theorem HasSobolevExtensionOn.isCompactEmbedding_toContinuousMapOnL (hS : HasSobolevExtensionOn S)
    (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    IsCompactEmbedding (hS.toContinuousMapOnL hp K).toLinearMap := by
  refine isCompactEmbedding_of_isCompact_closure_image_closedBall
    (hS.toContinuousMapOnL_injective hp hK) ?_
  obtain ⟨C₁, hC₁0, hC₁⟩ := hS.exists_forall_norm_toContinuousMapOnL_le hp K
  obtain ⟨C₂, hC₂0, hC₂⟩ := hS.exists_forall_norm_toContinuousMapOnL_sub_le hp K
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hα : (0 : ℝ) < 1 - N / (p : ℝ) := sub_pos.2 ((div_lt_one hp0).2 hp)
  refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := C₁) ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩ x
    refine (ContinuousMap.norm_coe_le_norm _ x).trans ((hC₁ u).trans ?_)
    calc C₁ * ‖u‖ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) hC₁0
      _ = C₁ := mul_one _
  · refine Metric.equicontinuous_of_continuity_modulus (fun d ↦ C₂ * d ^ (1 - N / (p : ℝ))) ?_ _ ?_
    · have h1 : Tendsto (fun d : ℝ ↦ d ^ (1 - N / (p : ℝ))) (𝓝 0) (𝓝 0) := by
        have := (Real.continuous_rpow_const hα.le).tendsto 0
        rwa [Real.zero_rpow hα.ne'] at this
      simpa using h1.const_mul C₂
    · rintro x y ⟨_, ⟨u, hu, rfl⟩⟩
      simp only [dist_eq_norm, Subtype.dist_eq]
      refine (hC₂ u x y).trans ?_
      rw [← dist_eq_norm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _)
      calc C₂ * ‖u‖ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) hC₂0
        _ = C₂ := mul_one _

/-- **The Rellich–Kondrachov theorem for $p > N$.** Let $N \ge 1$, let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, let $N < p < \infty$, and
let $K \supseteq \Omega$ be compact, for example $K = \overline{\Omega}$. Then the injection
$W^{1,p}(\Omega) \subset C(K)$ is compact. This is Theorem 9.16 of [brezis2011functional],
"$W^{1,p}(\Omega) \subset C(\overline{\Omega})$ if $p > N$".

The dimension is written $N = d + 1$, and the class $C^1$ is `IsContDiffChartDomain 1`. The
injection is `SobolevEuclidean.toContinuousMapL`, which takes the continuous representative. -/
theorem SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ K) :
    IsCompactEmbedding (SobolevEuclidean.toContinuousMapL
      (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
        (hb.closure.subset frontier_subset_closure)) hp K).toLinearMap := by
  have hc := (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
    (hb.closure.subset frontier_subset_closure)).isCompactEmbedding_toContinuousMapOnL hp hK
  have hι : IsContinuousEmbedding ((LinearMap.id (R := ℝ)).codRestrict
      (⊤ : Submodule ℝ (SobolevEuclidean (d + 1) 1 p Ω)) fun _ ↦ Submodule.mem_top) :=
    ⟨fun u v huv ↦ by simpa using congrArg Subtype.val huv, 1, fun u ↦ by simp⟩
  exact hι.comp_isCompactEmbedding hc

end RellichGt

/-! ### Theorem 9.16, the cases $p \ge N$, by lowering the exponent -/

section RellichGe

open SobolevMultiIndex

/-- Let $N \ge 2$ and $q \ge N$. Then there is $r$ with $1 \le r < N$ and $1/(2q) = 1/r - 1/N$; thus
the Sobolev exponent of $r$ is $r^* = 2q > q$.

This is the auxiliary exponent by which the proof of Theorem 9.16 of [brezis2011functional]
reduces the case $p \ge N$ to the case $p < N$: "the case $p = N$ reduces to the case $p < N$". -/
theorem NNReal.exists_lowerExponent {N : ℕ} (hN : 2 ≤ N) {q : ℝ≥0} (hq : (N : ℝ≥0) ≤ q) :
    ∃ r : ℝ≥0, 1 ≤ r ∧ r < N ∧ ((2 * q : ℝ≥0) : ℝ)⁻¹ = (r : ℝ)⁻¹ - (N : ℝ)⁻¹ ∧ q < 2 * q := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (zero_lt_two.trans_le hN)
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le hN0 (by exact_mod_cast hq)
  have hq0' : (0 : ℝ≥0) < q := by exact_mod_cast hq0
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (N : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : (0 : ℝ≥0) < (N : ℝ≥0)⁻¹ + (2 * q)⁻¹ := by positivity
  refine ⟨((N : ℝ≥0)⁻¹ + (2 * q)⁻¹)⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [one_le_inv₀ hpos]
    have h1 : (N : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hNr
    have h2 : (2 * q : ℝ)⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    have : (((N : ℝ≥0)⁻¹ + (2 * q)⁻¹ : ℝ≥0) : ℝ) ≤ 1 := by
      push_cast
      linarith
    exact_mod_cast this
  · rw [inv_lt_comm₀ hpos (by exact_mod_cast hN0)]
    exact lt_add_of_pos_right _ (by positivity)
  · push_cast
    rw [inv_inv]
    ring
  · exact lt_mul_left hq0' one_lt_two

/-- **The Rellich–Kondrachov theorem for $p \ge N$, $N \ge 2$.** Let $N \ge 2$, let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, let $N \le p < \infty$,
and let $1 \le q < \infty$. Suppose that every $u \in W^{1,p}(\Omega)$ lies in $L^q(\Omega)$.
Then the injection $W^{1,p}(\Omega) \subset L^q(\Omega)$ is compact.

This covers the case $p = N$, $q \in [N, \infty)$ of Theorem 9.16 of [brezis2011functional], and
for $p > N$ the compact injection into $L^p(\Omega)$ of the last sentence of the theorem. The
proof follows the source: "the case $p = N$ reduces to the case $p < N$". The injection
$W^{1,p}(\Omega) \subset W^{1,r}(\Omega)$ is continuous for an $r < N$ with $r^* > q$
(`NNReal.exists_lowerExponent`), and $W^{1,r}(\Omega) \subset L^q(\Omega)$ is compact by the
case $p < N$. The dimension is written $N = d + 1$ with $d \ge 1$, and the membership in
$L^q(\Omega)$ is the hypothesis `h`, so that the injection is defined. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_le {d : ℕ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hd : 1 ≤ d)
    (hp : ((d + 1 : ℕ) : ℝ≥0) ≤ p)
    (h : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsCompactEmbedding
      (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume h) := by
  have hN : 2 ≤ d + 1 := by omega
  obtain ⟨r, hr1, hrN, hr', hq2⟩ := NNReal.exists_lowerExponent (N := d + 1) hN
    (q := max q ((d + 1 : ℕ) : ℝ≥0)) (le_max_right _ _)
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  have hqr : q < 2 * max q ((d + 1 : ℕ) : ℝ≥0) := lt_of_le_of_lt (le_max_left _ _) hq2
  have hc := SobolevEuclidean.isCompactEmbedding_toLp_of_lt (p := r) (q := q) hΩ hb hrN hr' hqr
  have hrp : (r : ℝ≥0∞) ≤ p := by exact_mod_cast hrN.le.trans hp
  have hι := isContinuousEmbedding_toLowerExponentL (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (k := 1) (p := (p : ℝ≥0∞))
    (r := (r : ℝ≥0∞)) (μ := volume) (Ω := Ω) hb.measure_lt_top.ne hrp
  have := hι.comp_isCompactEmbedding hc
  convert this using 1
  refine LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn h u).trans ?_)
  exact ((toLpₗ_coeFn (fun v ↦ (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
    (hb.closure.subset frontier_subset_closure)).memLp_fn_of_le_sobolevConj hb.measure_lt_top.ne
      hrN hr' hqr.le ⟨v, Submodule.mem_top⟩) _).trans
    (fn_toLowerExponentL hb.measure_lt_top.ne hrp u)).symm

/-- **The Rellich–Kondrachov theorem for $p = N$.** Let $N \ge 2$, let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, and let
$1 \le q < \infty$. Suppose that every $u \in W^{1,N}(\Omega)$ lies in $L^q(\Omega)$. Then the
injection $W^{1,N}(\Omega) \subset L^q(\Omega)$ is compact. This is Theorem 9.16 of
[brezis2011functional], the case $p = N$.

The source states the case $p = N$ for $q \in [N, \infty)$. The statement here needs only
$q \ge 1$, because it is `SobolevEuclidean.isCompactEmbedding_toLp_of_le` at $p = N$. The
dimension is written $N = d + 1$ with $d \ge 1$, and the membership in $L^q(\Omega)$ is the
hypothesis `h`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_eq {d : ℕ} {q : ℝ≥0}
    [Fact (1 ≤ (((d + 1 : ℕ) : ℝ≥0) : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hd : 1 ≤ d)
    (h : ∀ u : SobolevEuclidean (d + 1) 1 ((d + 1 : ℕ) : ℝ≥0) Ω,
      MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1
      ((d + 1 : ℕ) : ℝ≥0) Ω volume h) :=
  SobolevEuclidean.isCompactEmbedding_toLp_of_le hΩ hb hd le_rfl h

/-- **The Rellich–Kondrachov theorem, the injection into $L^p$.** Let $N \ge 1$, let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, and let $1 \le p < \infty$
with $p < N$ or $N \ge 2$. Then the injection $W^{1,p}(\Omega) \subset L^p(\Omega)$ is compact.
This is the last sentence of Theorem 9.16 of [brezis2011functional]: "in particular
$W^{1,p}(\Omega) \subset L^p(\Omega)$ with compact injection".

The case $N = 1 \le p$ is not covered here;
`SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one` covers it for $p > 1$. The dimension
is written $N = d + 1$. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_self {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hd : p < ((d + 1 : ℕ) : ℝ≥0) ∨ 1 ≤ d) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      fun u ↦ SobolevMultiIndex.memLp u) := by
  rcases lt_or_ge p ((d + 1 : ℕ) : ℝ≥0) with hpN | hpN
  · have hp0 : 0 < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
    obtain ⟨p', hp'⟩ : ∃ p' : ℝ≥0, (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ :=
      ⟨(p⁻¹ - ((d + 1 : ℕ) : ℝ≥0)⁻¹)⁻¹, by
        rw [NNReal.coe_inv, NNReal.coe_sub (by
          exact_mod_cast (inv_strictAnti₀ hp0 hpN).le), inv_inv]
        simp⟩
    exact SobolevEuclidean.isCompactEmbedding_toLp_of_lt hΩ hb hpN hp'
      (NNReal.lt_sobolevConj hp0 hpN hp')
  · rcases hd with hd | hd
    · exact absurd hpN (not_le.2 hd)
    · exact SobolevEuclidean.isCompactEmbedding_toLp_of_le hΩ hb hd hpN _

/-- Let $N \ge 1$, let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, and let
$1 \le p < \infty$ with $p < N$ or $N \ge 2$. Then the bounded injection
$W^{1,p}(\Omega) \to L^p(\Omega)$, `SobolevMultiIndex.fnL`, is a compact embedding. This is
`SobolevEuclidean.isCompactEmbedding_toLp_self` for the bundled injection. -/
theorem SobolevEuclidean.isCompactEmbedding_fnL {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hd : p < ((d + 1 : ℕ) : ℝ≥0) ∨ 1 ≤ d) :
    IsCompactEmbedding (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω
      volume).toLinearMap := by
  rw [← toLpₗ_self]
  exact SobolevEuclidean.isCompactEmbedding_toLp_self hΩ hb hd

end RellichGe

/-! ### Extension by zero of a continuous function on a compact set, into $L^p(\Omega)$ -/

section ExtendZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {K : Set E} [CompactSpace K] {Ω : Set E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace ContinuousMap

open scoped Classical in
variable (K) in
/-- Let $K \subseteq E$. The **extension by zero** of $f \in C(K, \mathbb{R})$ is the function on
$E$ that equals $f(x)$ for $x \in K$ and $0$ for $x \notin K$. -/
def extendZero (f : C(K, ℝ)) : E → ℝ := fun x ↦ if h : x ∈ K then f ⟨x, h⟩ else 0

omit [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [CompactSpace K] in
/-- The extension by zero of $f \in C(K, \mathbb{R})$ takes the value $f(x)$ at every $x \in K$. -/
theorem extendZero_of_mem (f : C(K, ℝ)) {x : E} (hx : x ∈ K) :
    extendZero K f x = f ⟨x, hx⟩ := by
  simp [extendZero, hx]

omit [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- Let $K$ be compact. The extension by zero $\tilde f$ of $f \in C(K, \mathbb{R})$ satisfies
$|\tilde f(x)| \le \|f\|_\infty$ for every $x \in E$. -/
theorem norm_extendZero_le (f : C(K, ℝ)) (x : E) : ‖extendZero K f x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ K
  · rw [extendZero_of_mem f hx]
    exact f.norm_coe_le_norm _
  · simp [extendZero, hx]

omit [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [CompactSpace K] in
/-- The extension by zero of $f \in C(K, \mathbb{R})$ is continuous on $K$. -/
theorem continuousOn_extendZero (f : C(K, ℝ)) : ContinuousOn (extendZero K f) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  funext x
  exact extendZero_of_mem f x.2

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
/-- Let $K$ be compact and let $\Omega \subseteq K$ be measurable with $\mu(\Omega) < \infty$. Then
for every exponent $p$ the extension by zero of $f \in C(K, \mathbb{R})$ lies in $L^p(\Omega)$. -/
theorem memLp_extendZero (f : C(K, ℝ)) (hΩK : Ω ⊆ K) (hΩ : MeasurableSet Ω) (hμ : μ Ω ≠ ⊤) :
    MemLp (extendZero K f) p (μ.restrict Ω) := by
  have : IsFiniteMeasure (μ.restrict Ω) := ⟨by simpa [Measure.restrict_apply_univ] using hμ.lt_top⟩
  exact MemLp.of_bound (((continuousOn_extendZero f).mono hΩK).aestronglyMeasurable (μ := μ) hΩ)
    ‖f‖ (Eventually.of_forall (norm_extendZero_le f))

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
/-- Let $K$ be compact and let $\Omega \subseteq K$ be measurable. Then for every exponent $p$ the
extension by zero $\tilde f$ of $f \in C(K, \mathbb{R})$ satisfies
$$\|\tilde f\|_{L^p(\Omega)} \le \mu(\Omega)^{1/p} \|f\|_\infty.$$
Here $1/p$ is read as $0$ for $p = 0$ and for $p = \infty$, so that the factor
$\mu(\Omega)^{1/p}$ is then $1$. -/
theorem eLpNorm_extendZero_le (f : C(K, ℝ)) (hΩK : Ω ⊆ K) (hΩ : MeasurableSet Ω) :
    eLpNorm (extendZero K f) p (μ.restrict Ω) ≤ μ Ω ^ p.toReal⁻¹ * ENNReal.ofReal ‖f‖ := by
  refine (eLpNorm_le_of_ae_bound (C := ‖f‖) ?_ (Eventually.of_forall (norm_extendZero_le f))).trans
    (le_of_eq ?_)
  · exact ((continuousOn_extendZero f).mono hΩK).aestronglyMeasurable hΩ
  · rw [Measure.restrict_apply_univ]

variable (μ K Ω p) in
/-- Let $K \subseteq E$ be compact, let $\Omega \subseteq K$ be measurable with
$\mu(\Omega) < \infty$, and let $1 \le p \le \infty$. **Extension by zero into $L^p(\Omega)$**
is the bounded linear map $C(K, \mathbb{R}) \to L^p(\Omega)$ that sends $f$ to the restriction
to $\Omega$ of its extension by zero. Its norm is at most $\mu(\Omega)^{1/p}$.

Composed with the map $W^{1,p}(\Omega) \to C(\overline{\Omega}, \mathbb{R})$ that takes the
continuous representative (Morrey's theorem), it gives the injection
$W^{1,p}(\Omega) \subset L^p(\Omega)$ through $C(\overline{\Omega})$. By this route Theorem 9.16
of [brezis2011functional] gives "$W^{1,p}(\Omega) \subset L^p(\Omega)$ with compact injection"
for $p > N$. -/
def extendZeroToLpL (hΩK : Ω ⊆ K) (hΩ : MeasurableSet Ω) (hμ : μ Ω ≠ ⊤) :
    C(K, ℝ) →L[ℝ] Lp ℝ p (μ.restrict Ω) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (memLp_extendZero f hΩK hΩ hμ).toLp _
      map_add' := fun f g ↦ by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ K <;> simp [extendZero, hx]
      map_smul' := fun c f ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ K <;> simp [extendZero, hx] }
    (μ Ω ^ p.toReal⁻¹).toReal fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal (norm_nonneg f),
        ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ) ENNReal.ofReal_ne_top) ?_
      exact eLpNorm_extendZero_le f hΩK hΩ

omit [NormedSpace ℝ E] in
/-- As an element of $L^p(\Omega)$, the image of $f \in C(K, \mathbb{R})$ under extension by zero
equals the extension by zero of $f$ almost everywhere on $\Omega$. -/
theorem coeFn_extendZeroToLpL (hΩK : Ω ⊆ K) (hΩ : MeasurableSet Ω) (hμ : μ Ω ≠ ⊤) (f : C(K, ℝ)) :
    extendZeroToLpL μ K Ω p hΩK hΩ hμ f =ᵐ[μ.restrict Ω] extendZero K f :=
  MemLp.coeFn_toLp (memLp_extendZero f hΩK hΩ hμ)

omit [NormedSpace ℝ E] in
/-- **Extension by zero is injective.** Let $\Omega \subseteq E$ be open with
$\mu(\Omega) < \infty$, let $K$ be compact with
$\Omega \subseteq K \subseteq \overline{\Omega}$, and let $\mu$ be positive on nonempty open
sets. Then extension by zero $C(K, \mathbb{R}) \to L^p(\Omega)$ is injective: a continuous
function on $K$ that vanishes almost everywhere on $\Omega$ vanishes on $\Omega$, hence on
$K \subseteq \overline{\Omega}$. -/
theorem extendZeroToLpL_injective
    [μ.IsOpenPosMeasure] (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω) (hΩo : IsOpen Ω) (hμ : μ Ω ≠ ⊤) :
    Function.Injective (extendZeroToLpL μ K Ω p hΩK hΩo.measurableSet hμ) := by
  intro f g hfg
  have h1 : extendZero K f =ᵐ[μ.restrict Ω] extendZero K g :=
    (coeFn_extendZeroToLpL hΩK hΩo.measurableSet hμ f).symm.trans
      ((Lp.ext_iff.1 hfg).trans (coeFn_extendZeroToLpL hΩK hΩo.measurableSet hμ g))
  have h2 : EqOn (extendZero K f) (extendZero K g) Ω :=
    Measure.eqOn_open_of_ae_eq h1 hΩo ((continuousOn_extendZero f).mono hΩK)
      ((continuousOn_extendZero g).mono hΩK)
  have h3 : EqOn (extendZero K f) (extendZero K g) K :=
    h2.of_subset_closure (continuousOn_extendZero f) (continuousOn_extendZero g) hΩK hKΩ
  ext ⟨x, hx⟩
  have := h3 hx
  rwa [extendZero_of_mem f hx, extendZero_of_mem g hx] at this

omit [NormedSpace ℝ E] in
/-- Let $\Omega \subseteq E$ be open with $\mu(\Omega) < \infty$, let $K$ be compact with
$\Omega \subseteq K \subseteq \overline{\Omega}$, and let $\mu$ be positive on nonempty open
sets. Then extension by zero $C(K, \mathbb{R}) \to L^p(\Omega)$ is a continuous embedding. -/
theorem isContinuousEmbedding_extendZeroToLpL
    [μ.IsOpenPosMeasure] (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω) (hΩo : IsOpen Ω)
    (hμ : μ Ω ≠ ⊤) :
    IsContinuousEmbedding (extendZeroToLpL μ K Ω p hΩK hΩo.measurableSet hμ).toLinearMap :=
  ⟨extendZeroToLpL_injective hΩK hKΩ hΩo hμ, _,
    (extendZeroToLpL μ K Ω p hΩK hΩo.measurableSet hμ).le_opNorm⟩

end ContinuousMap

end ExtendZero

/-! ### Theorem 9.16 for $p > N$: the injection into $L^p(\Omega)$ through $C(\overline{\Omega})$ -/

section RellichGtSelf

open SobolevMultiIndex

/-- **The injection $W^{1,p}(\Omega) \subset L^p(\Omega)$ factors through $C(\overline{\Omega})$ for
$p > N$.** Let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain of finite measure
with compact closure, and let $N < p < \infty$. Then the injection
$W^{1,p}(\Omega) \subset L^p(\Omega)$ is the composition of the map $W^{1,p}(\Omega) \to
C(\overline{\Omega}, \mathbb{R})$ that takes the continuous representative and extension by zero
$C(\overline{\Omega}, \mathbb{R}) \to L^p(\Omega)$.

The first map is `SobolevEuclidean.toContinuousMapL`, and the second is
`ContinuousMap.extendZeroToLpL`. -/
theorem SobolevEuclidean.toLpₗ_eq_extendZeroToLpL_comp_toContinuousMapL {N : ℕ}
    {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p)
    [CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))]
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (fun u ↦ memLp u)
      = (ContinuousMap.extendZeroToLpL volume (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))
          (Ω : Set (EuclideanSpace ℝ (Fin N))) p subset_closure Ω.isOpen.measurableSet
          hμ).toLinearMap ∘ₗ
        (SobolevEuclidean.toContinuousMapL hΩ hp
          (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))).toLinearMap := by
  refine LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn _ u).trans ?_)
  refine Filter.EventuallyEq.trans ?_ (ContinuousMap.coeFn_extendZeroToLpL subset_closure
    Ω.isOpen.measurableSet hμ (SobolevEuclidean.toContinuousMapL hΩ hp
      (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) u)).symm
  refine (SobolevEuclidean.fn_ae_eq_toContinuousMapL hΩ hp u).trans ?_
  refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx ↦ ?_
  rw [ContinuousMap.extendZero_of_mem _ (subset_closure hx)]
  rfl

/-- **The Rellich–Kondrachov theorem, the injection into $L^p$ for $p > N$.** Let $N \ge 1$, let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, and let $N < p < \infty$.
Then the injection $W^{1,p}(\Omega) \subset L^p(\Omega)$ is compact.

It is the compact injection $W^{1,p}(\Omega) \subset C(\overline{\Omega})$ followed by the
continuous extension by zero $C(\overline{\Omega}) \to L^p(\Omega)$. This covers the case
$N = 1 < p$ of the last sentence of Theorem 9.16 of [brezis2011functional], which
`SobolevEuclidean.isCompactEmbedding_toLp_self` leaves out. The dimension is written
$N = d + 1$. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_self_of_gt {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      fun u ↦ SobolevMultiIndex.memLp u) := by
  have : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  rw [SobolevEuclidean.toLpₗ_eq_extendZeroToLpL_comp_toContinuousMapL
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure)) hp hb.measure_lt_top.ne]
  exact (SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt hΩ hb hp subset_closure)
    |>.comp_isContinuousEmbedding
      (ContinuousMap.isContinuousEmbedding_extendZeroToLpL subset_closure subset_rfl Ω.isOpen _)

/-- **The Rellich–Kondrachov theorem, the injection into $L^p$.** Let $N \ge 1$, let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, and let $1 \le p < \infty$
with $p \ne 1$ or $N \ge 2$. Then the injection $W^{1,p}(\Omega) \subset L^p(\Omega)$ is
compact. This is the last sentence of Theorem 9.16 of [brezis2011functional].

The three cases $p < N$ (`SobolevEuclidean.isCompactEmbedding_toLp_self`), $N \le p$ with
$N \ge 2$ (lowering the exponent) and $p > N$ (through $C(\overline{\Omega})$) together leave
out only $N = 1 = p$. The dimension is written $N = d + 1$. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hd : p ≠ 1 ∨ 1 ≤ d) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      fun u ↦ SobolevMultiIndex.memLp u) := by
  rcases lt_or_ge p ((d + 1 : ℕ) : ℝ≥0) with hpN | hpN
  · exact SobolevEuclidean.isCompactEmbedding_toLp_self hΩ hb (Or.inl hpN)
  rcases hd with hp | hd
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
      exact SobolevEuclidean.isCompactEmbedding_toLp_self_of_gt hΩ hb
        (by simpa using lt_of_le_of_ne hp1 (Ne.symm hp))
    · exact SobolevEuclidean.isCompactEmbedding_toLp_self hΩ hb (Or.inr hd)
  · exact SobolevEuclidean.isCompactEmbedding_toLp_self hΩ hb (Or.inr hd)

/-- Let $N \ge 1$, let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, and let
$1 \le p < \infty$ with $p \ne 1$ or $N \ge 2$. Then the bounded injection
$W^{1,p}(\Omega) \to L^p(\Omega)$, `SobolevMultiIndex.fnL`, is a compact embedding. This is
`SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one` for the bundled injection. -/
theorem SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hd : p ≠ 1 ∨ 1 ≤ d) :
    IsCompactEmbedding (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω
      volume).toLinearMap := by
  rw [← toLpₗ_self]
  exact SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one hΩ hb hd

end RellichGtSelf

/-! ### Compact injection $W^{k+1,p}(\Omega) \subset W^{k,p}(\Omega)$ between successive orders -/

section LowerOrder

/-- **A common convergent subsequence for finitely many sequences.** Let $\kappa : V \to W$ be a
compact embedding of normed spaces, and let $(u_{i,n})_n$, for $i$ in a finite index set, be
bounded sequences in $V$. Then there is one strictly increasing
$\varphi : \mathbb{N} \to \mathbb{N}$ such that $\kappa(u_{i,\varphi(n)})$ converges in $W$ for
every $i$.

The images lie in a finite product of compact sets. -/
theorem IsCompactEmbedding.exists_subseq_forall_tendsto {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 W] {κ : V →ₗ[𝕜] W} (h : IsCompactEmbedding κ) {ι : Type*} [Finite ι]
    (u : ι → ℕ → V) (hu : ∀ i, ∃ M : ℝ, ∀ n, ‖u i n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ w : W, Tendsto (fun n ↦ κ (u i (φ n))) atTop (𝓝 w) := by
  choose M hM using hu
  have hK : ∀ i, IsCompact (closure (κ '' closedBall 0 (M i))) := fun i ↦
    h.isCompactOperator.isCompact_closure_image_closedBall (M i)
  have hmem : ∀ n, (fun i ↦ κ (u i n)) ∈ Set.univ.pi fun i ↦ closure (κ '' closedBall 0 (M i)) :=
    fun n i _ ↦ subset_closure ⟨u i n, by simpa using hM i n, rfl⟩
  obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_univ_pi hK).tendsto_subseq hmem
  exact ⟨φ, hφ, fun i ↦ ⟨a i, tendsto_pi_nhds.1 ha i⟩⟩

/-- **The sequential criterion for a compact embedding.** Let $\iota : V \to W$ be a bounded linear
map that is a continuous embedding. If every bounded sequence $(u_n)$ in $V$ has a subsequence
$(u_{\varphi(n)})$ such that $\iota(u_{\varphi(n)})$ converges in $W$, then $\iota$ is a compact
embedding. -/
theorem IsCompactEmbedding.of_forall_exists_subseq_tendsto {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 W] {ι : V →L[𝕜] W} (hι : IsContinuousEmbedding ι.toLinearMap)
    (h : ∀ u : ℕ → V, (∃ M : ℝ, ∀ n, ‖u n‖ ≤ M) →
      ∃ (φ : ℕ → ℕ) (w : W), StrictMono φ ∧ Tendsto (fun n ↦ ι (u (φ n))) atTop (𝓝 w)) :
    IsCompactEmbedding ι.toLinearMap :=
  { hι with exists_subseq_tendsto := h }

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

/-- Let $F$ be complete, let $\mu$ be locally finite and finite on compact sets, and let $(x_n)$ be
a sequence in $W^{k,p}(\Omega)$. If for every multi-index $\alpha$ with $|\alpha| \le k$ the
weak derivatives $\partial^\alpha x_n$ converge in $L^p(\Omega)$, then $(x_n)$ converges in
$W^{k,p}(\Omega)$.

The space $W^{k,p}(\Omega)$ is a closed subspace (`SobolevMultiIndex.isClosed`) of an $\ell^p$
product of copies of $L^p(\Omega)$, and convergence in this product is convergence of each
component. -/
theorem SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv
    {x : ℕ → SobolevMultiIndex F b k p Ω μ}
    (h : ∀ α, ∃ L : Lp F p (μ.restrict (Ω : Set E)),
      Tendsto (fun n ↦ weakDeriv (x n) α) atTop (𝓝 L)) :
    ∃ y : SobolevMultiIndex F b k p Ω μ, Tendsto x atTop (𝓝 y) := by
  choose L hL using h
  have hconv : Tendsto (fun n ↦ (x n : SobolevMultiIndexTuple F ι k p Ω μ)) atTop
      (𝓝 (WithLp.toLp p L)) := by
    have h1 : Tendsto (fun n ↦ fun α ↦ weakDeriv (x n) α) atTop (𝓝 L) := tendsto_pi_nhds.2 hL
    have h2 := ((PiLp.continuous_toLp p fun _ : MultiIndexLE ι k ↦ Lp F p (μ.restrict (Ω : Set E)))
      |>.tendsto L).comp h1
    convert h2 using 1
    funext n
    rfl
  have hy : WithLp.toLp p L ∈ SobolevMultiIndex F b k p Ω μ :=
    SobolevMultiIndex.isClosed.mem_of_tendsto hconv (Eventually.of_forall fun n ↦ (x n).2)
  exact ⟨⟨WithLp.toLp p L, hy⟩, tendsto_subtype_rng.2 hconv⟩

end LowerOrder

section LowerOrderAbstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

namespace SobolevMultiIndex

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- Let $k' \le k$, let $u \in W^{k,p}(\Omega)$, and let $|\alpha| \le k'$. Then the weak derivative
$\partial^\alpha$ of the image of $u$ under the injection
$W^{k,p}(\Omega) \to W^{k',p}(\Omega)$, `SobolevMultiIndex.toLowerOrderL`, is
$\partial^\alpha u$. -/
theorem weakDeriv_toLowerOrderL {k' : ℕ} (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k') :
    weakDeriv (toLowerOrderL F b p Ω μ hk u) α = weakDeriv u ⟨α.1, α.2.trans hk⟩ :=
  rfl

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- Let $u \in W^{k,p}(\Omega)$. The only component of the image of $u$ in $W^{0,p}(\Omega)$ under
`SobolevMultiIndex.toLowerOrderL` is the function $u$, as an element of $L^p(\Omega)$
(`SobolevMultiIndex.fnL`). -/
theorem weakDeriv_toLowerOrderL_zero (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι 0) :
    weakDeriv (toLowerOrderL F b p Ω μ (Nat.zero_le k) u) α = fnL F b k p Ω μ u := by
  obtain rfl : α = 0 := Subtype.ext (funext fun i ↦ Nat.le_zero.1
    ((Finset.single_le_sum (f := α.1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans α.2))
  rfl

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- Let $u \in W^{k+1,p}(\Omega)$ and let $|\alpha| \le k$. Then the weak derivative
$\partial^\alpha$ of the partial derivative $\partial_i u \in W^{k,p}(\Omega)$,
`SobolevMultiIndex.partialDerivL`, is $\partial^{\alpha + e_i} u$. -/
theorem weakDeriv_partialDerivL (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ)
    (α : MultiIndexLE ι k) :
    weakDeriv (partialDerivL F b p Ω μ i u) α = weakDeriv u (MultiIndexLE.addSingle i α) :=
  rfl

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- For $k' \le k$ the injection $W^{k,p}(\Omega) \to W^{k',p}(\Omega)$ does not increase norms:
$\|u\|_{W^{k',p}(\Omega)} \le \|u\|_{W^{k,p}(\Omega)}$. -/
theorem norm_toLowerOrderL_apply_le {k' : ℕ} (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ) :
    ‖toLowerOrderL F b p Ω μ hk u‖ ≤ ‖u‖ :=
  norm_toLowerOrder_le hk u

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- The partial derivative $\partial_i : W^{k+1,p}(\Omega) \to W^{k,p}(\Omega)$ does not increase
norms: $\|\partial_i u\|_{W^{k,p}(\Omega)} \le \|u\|_{W^{k+1,p}(\Omega)}$. -/
theorem norm_partialDerivL_apply_le (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    ‖partialDerivL F b p Ω μ i u‖ ≤ ‖u‖ :=
  norm_partialDeriv_le i u

variable [FiniteDimensional ℝ E] [BorelSpace E]

omit [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- Let $E$ be finite-dimensional and $F$ complete. For $k' \le k$ the injection
$W^{k,p}(\Omega) \to W^{k',p}(\Omega)$, `SobolevMultiIndex.toLowerOrderL`, is a continuous
embedding. -/
theorem isContinuousEmbedding_toLowerOrderL {k' : ℕ} (hk : k' ≤ k) :
    IsContinuousEmbedding (toLowerOrderL F b p Ω μ hk).toLinearMap :=
  ⟨toLowerOrderL_injective hk, 1, fun u ↦ by rw [one_mul]; exact norm_toLowerOrder_le hk u⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The base case of the compact injection between successive orders.** Let $F$ be complete, let
$\mu$ be locally finite and finite on compact sets, and let
$T : W^{1,p}(\Omega) \to W^{0,p}(\Omega)$ be a bounded linear map and a continuous embedding
whose only component is the function: the component of order $0$ of $Tv$ is $v$, as an element
of $L^p(\Omega)$. If the injection $W^{1,p}(\Omega) \to L^p(\Omega)$, `SobolevMultiIndex.fnL`,
is a compact embedding, then so is $T$.

The operator $T$ is a variable, so that the lemma applies to `SobolevMultiIndex.toLowerOrderL`
without unfolding it. -/
theorem isCompactEmbedding_of_forall_weakDeriv_eq_fnL
    {T : SobolevMultiIndex F b 1 p Ω μ →L[ℝ] SobolevMultiIndex F b 0 p Ω μ}
    (hTc : ∀ (v : SobolevMultiIndex F b 1 p Ω μ) (α : MultiIndexLE ι 0),
      weakDeriv (T v) α = fnL F b 1 p Ω μ v)
    (hι : IsContinuousEmbedding T.toLinearMap)
    (hc : IsCompactEmbedding (fnL F b 1 p Ω μ).toLinearMap) :
    IsCompactEmbedding T.toLinearMap := by
  refine IsCompactEmbedding.of_forall_exists_subseq_tendsto hι fun u hu ↦ ?_
  obtain ⟨φ, w, hφ, hw⟩ := hc.exists_subseq_tendsto u hu
  have hcomp : ∀ α : MultiIndexLE ι 0, ∃ L : Lp F p (μ.restrict (Ω : Set E)),
      Tendsto (fun n ↦ weakDeriv (T (u (φ n))) α) atTop (𝓝 L) := fun α ↦
    ⟨w, by simpa only [hTc, ContinuousLinearMap.coe_coe] using hw⟩
  obtain ⟨y, hy⟩ := SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv hcomp
  exact ⟨φ, y, hφ, hy⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The inductive step of the compact injection between successive orders.** Let $F$ be complete
and let $\mu$ be locally finite and finite on compact sets. Let
$$T : W^{k+2,p}(\Omega) \to W^{k+1,p}(\Omega), \qquad T' : W^{k+1,p}(\Omega) \to
  W^{k,p}(\Omega), \qquad D_i : W^{k+2,p}(\Omega) \to W^{k+1,p}(\Omega)$$
be bounded linear maps, for $i$ in the index set of the basis, such that $T$ and $T'$ keep the
components of order at most $k + 1$ and $k$, $D_i$ is the partial derivative, $\partial^\gamma
(D_i v) = \partial^{\gamma + e_i} v$, and $\|Tv\| \le \|v\|$ and $\|D_i v\| \le \|v\|$ for all
$v$. If $T$ is a continuous embedding and $T'$ is a compact embedding, then $T$ is a compact
embedding.

For a bounded sequence $u_n$ in $W^{k+2,p}(\Omega)$, the sequences $Tu_n$ and $D_i u_n$ are
bounded in $W^{k+1,p}(\Omega)$, so along a common subsequence their images under $T'$ converge
in $W^{k,p}(\Omega)$. Every component $\partial^\beta u_n$ with $|\beta| \le k + 1$ is a
component of one of them, because $\partial^\beta = \partial^{\beta'} \partial_i$ when
$|\beta| = k + 1$. Hence every component converges in $L^p(\Omega)$, and $Tu_n$ converges in
$W^{k+1,p}(\Omega)$ by `SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv`. -/
theorem isCompactEmbedding_of_forall_weakDeriv_eq
    {T : SobolevMultiIndex F b (k + 1 + 1) p Ω μ →L[ℝ] SobolevMultiIndex F b (k + 1) p Ω μ}
    {T' : SobolevMultiIndex F b (k + 1) p Ω μ →L[ℝ] SobolevMultiIndex F b k p Ω μ}
    {D : ι → SobolevMultiIndex F b (k + 1 + 1) p Ω μ →L[ℝ] SobolevMultiIndex F b (k + 1) p Ω μ}
    (hTc : ∀ (v : SobolevMultiIndex F b (k + 1 + 1) p Ω μ) (β : MultiIndexLE ι (k + 1)),
      weakDeriv (T v) β = weakDeriv v ⟨β.1, β.2.trans (Nat.le_succ _)⟩)
    (hT'c : ∀ (v : SobolevMultiIndex F b (k + 1) p Ω μ) (γ : MultiIndexLE ι k),
      weakDeriv (T' v) γ = weakDeriv v ⟨γ.1, γ.2.trans (Nat.le_succ _)⟩)
    (hDc : ∀ (i : ι) (v : SobolevMultiIndex F b (k + 1 + 1) p Ω μ) (γ : MultiIndexLE ι (k + 1)),
      weakDeriv (D i v) γ = weakDeriv v (MultiIndexLE.addSingle i γ))
    (hTn : ∀ v, ‖T v‖ ≤ ‖v‖) (hDn : ∀ i v, ‖D i v‖ ≤ ‖v‖)
    (hι : IsContinuousEmbedding T.toLinearMap) (ih : IsCompactEmbedding T'.toLinearMap) :
    IsCompactEmbedding T.toLinearMap := by
  refine IsCompactEmbedding.of_forall_exists_subseq_tendsto hι fun u hu ↦ ?_
  obtain ⟨M, hM⟩ := hu
  -- the sequences `u_n` and `∂_i u_n` in `W^{k+1,p}(Ω)`
  obtain ⟨t, ht⟩ : ∃ t : Option ι → ℕ → SobolevMultiIndex F b (k + 1) p Ω μ,
      t = fun i n ↦ Option.elim i (T (u n)) (fun i ↦ D i (u n)) := ⟨_, rfl⟩
  have htb : ∀ i, ∃ M : ℝ, ∀ n, ‖t i n‖ ≤ M := fun i ↦ ⟨M, fun n ↦ by
    rw [ht]
    rcases i with _ | i
    · exact (hTn _).trans (hM n)
    · exact (hDn i _).trans (hM n)⟩
  obtain ⟨φ, hφ, hlim⟩ := ih.exists_subseq_forall_tendsto t htb
  choose w hw using hlim
  have hw' : ∀ (i : Option ι) (γ : MultiIndexLE ι k),
      Tendsto (fun n ↦ weakDeriv (T' (t i (φ n))) γ) atTop (𝓝 (weakDeriv (w i) γ)) := fun i γ ↦
    ((weakDerivL F b k p Ω μ γ).continuous.tendsto (w i)).comp (hw i)
  -- convergence of every component of `u (φ n)` in `W^{k+1,p}(Ω)`
  have hcomp : ∀ β : MultiIndexLE ι (k + 1), ∃ L : Lp F p (μ.restrict (Ω : Set E)),
      Tendsto (fun n ↦ weakDeriv (T (u (φ n))) β) atTop (𝓝 L) := by
    intro β
    rcases Nat.lt_or_ge (∑ j, β.1 j) (k + 1) with hlt | hge
    · -- `|β| ≤ k`: a component of `u_n` in `W^{k,p}(Ω)`
      have hβ : ∑ j, β.1 j ≤ k := Nat.lt_succ_iff.1 hlt
      refine ⟨weakDeriv (w none) ⟨β.1, hβ⟩, ?_⟩
      have := hw' none ⟨β.1, hβ⟩
      simp only [ht, Option.elim, hT'c, hTc] at this ⊢
      exact this
    · -- `|β| = k + 1`: `β = β' + e_i`, a component of `∂_i u_n` in `W^{k,p}(Ω)`
      obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, β.1 i ≠ 0 :=
        Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := β.1) (by omega)
      obtain ⟨β', hβ'⟩ : ∃ β' : ι → ℕ, β.1 = β' + Pi.single i 1 := by
        refine ⟨β.1 - Pi.single i 1, funext fun j ↦ ?_⟩
        by_cases hj : j = i
        · subst hj
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
          omega
        · simp [Pi.single_eq_of_ne hj]
      have hβ'k : ∑ j, β' j ≤ k := by
        have := β.2
        rw [hβ'] at this
        simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
          ite_true] at this
        omega
      have hβeq : (⟨β.1, β.2.trans (Nat.le_succ _)⟩ : MultiIndexLE ι (k + 1 + 1))
          = MultiIndexLE.addSingle i (⟨β', hβ'k.trans (Nat.le_succ k)⟩ : MultiIndexLE ι (k + 1)) :=
        Subtype.ext hβ'
      refine ⟨weakDeriv (w (some i)) ⟨β', hβ'k⟩, ?_⟩
      have := hw' (some i) ⟨β', hβ'k⟩
      simp only [ht, Option.elim, hT'c, hDc, hTc, hβeq] at this ⊢
      exact this
  obtain ⟨y, hy⟩ := SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv hcomp
  exact ⟨φ, y, hφ, hy⟩

end SobolevMultiIndex

end LowerOrderAbstract

section LowerOrderOfFnL

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and $1 \le p \le \infty$. If the injection
$W^{1,p}(\Omega) \to L^p(\Omega)$, `SobolevMultiIndex.fnL`, is a compact embedding, then for
every $k$ the injection $W^{k+1,p}(\Omega) \to W^{k,p}(\Omega)$,
`SobolevMultiIndex.toLowerOrderL`, is a compact embedding.

The proof is by induction on $k$. The inductive step is
`SobolevMultiIndex.isCompactEmbedding_of_forall_weakDeriv_eq` for the maps that forget the
components of highest order and for the partial derivatives. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isCompactEmbedding_fnL
    (hc : IsCompactEmbedding
      (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).toLinearMap) (k : ℕ) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω
      volume (Nat.le_succ k)).toLinearMap := by
  induction k with
  | zero =>
    exact isCompactEmbedding_of_forall_weakDeriv_eq_fnL (weakDeriv_toLowerOrderL_zero)
      (isContinuousEmbedding_toLowerOrderL (Nat.zero_le 1)) hc
  | succ k ih =>
    exact isCompactEmbedding_of_forall_weakDeriv_eq (weakDeriv_toLowerOrderL (Nat.le_succ (k + 1)))
      (weakDeriv_toLowerOrderL (Nat.le_succ k))
      (weakDeriv_partialDerivL (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
        (p := p) (Ω := Ω) (μ := volume))
      (norm_toLowerOrderL_apply_le _) (norm_partialDerivL_apply_le)
      (isContinuousEmbedding_toLowerOrderL (Nat.le_succ (k + 1))) ih

end LowerOrderOfFnL

section RellichLower

open SobolevMultiIndex

variable {d : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The compact injection between successive orders on a $C^1$ domain.** Let $N \ge 1$, let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set of class $C^1$, and let $1 \le p < \infty$
with $p \ne 1$ or $N \ge 2$. Then for every $k$ the injection
$W^{k+1,p}(\Omega) \subset W^{k,p}(\Omega)$ is compact. This is Theorem 7.3.9 of
[han2009theoretical] on a $C^1$ domain, and Theorem 9.16 of [brezis2011functional] iterated.

The injection is `SobolevMultiIndex.toLowerOrderL`, and the dimension is written $N = d + 1$.
The proof is `SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isCompactEmbedding_fnL` with
the base case `SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLower_of_lt
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hd : p ≠ 1 ∨ 1 ≤ d)
    (k : ℕ) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p Ω
      volume (Nat.le_succ k)).toLinearMap :=
  SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isCompactEmbedding_fnL
    (SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one hΩ hb hd) k

end RellichLower

/-! ### The abstract Rellich–Kondrachov lemma at $q = p$: every $1 \le p < \infty$, every $N$ -/

section RellichSelf

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- Let $S$ be a subspace of $W^{1,p}(\Omega)$ and let $P : S \to W^{1,p}(\mathbb{R}^N)$ be a
bounded linear map. Then the family $\mathcal{F} = \{Pu : u \in S,\ \|u\| \le 1\}$ is bounded in
$L^p(\mathbb{R}^N)$, by $\|P\|$. -/
theorem HasSobolevExtensionOn.isBounded_image_closedBall_self
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) :
    Bornology.IsBounded ((fun u : S ↦ (SobolevEuclidean.memLp_fn (P u)).toLp _) ''
      closedBall (0 : S) 1) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨‖P‖, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hPu : ‖P u‖ ≤ ‖P‖ := by
    calc ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖P‖ := mul_one _
  have hb : eLpNorm (fn (P u)) p volume ≤ ENNReal.ofReal ‖P u‖ := by
    rw [← eLpNorm_restrict_coe_top]
    exact SobolevMultiIndex.eLpNorm_fn_le_ofReal_norm (P u)
  rw [mem_closedBall_zero_iff, Lp.norm_toLp]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans ?_
  rw [ENNReal.toReal_ofReal (norm_nonneg _)]
  exact hPu

/-- Let $1 \le p < \infty$, let $S$ be a subspace of $W^{1,p}(\Omega)$, and let
$P : S \to W^{1,p}(\mathbb{R}^N)$ be a bounded linear map. Then the family
$\mathcal{F} = \{Pu : u \in S,\ \|u\| \le 1\}$, viewed in $L^p(\mathbb{R}^N)$, is uniformly
continuous under translation: for every $\varepsilon > 0$ there is $\delta > 0$ such that
$$\|\tau_h f - f\|_{L^p(\mathbb{R}^N)} < \varepsilon \qquad \text{for all } f \in \mathcal{F}
  \text{ and all } h \text{ with } \|h\| < \delta.$$

This is the hypothesis of the Kolmogorov–M. Riesz–Fréchet theorem in the proof of Theorem 9.16
of [brezis2011functional] at $q = p$, where no interpolation is needed. Proposition 9.3 gives
$\|\tau_h v - v\|_p \le \|h\| \|\nabla v\|_p \le \|h\| N \|P\|$. -/
theorem HasSobolevExtensionOn.uniform_translate_image_closedBall_self
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ (fun u : S ↦
      (SobolevEuclidean.memLp_fn (P u)).toLp _) '' closedBall (0 : S) 1,
        ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ < δ →
          eLpNorm (fun x ↦ f (x + h) - f x) p volume < ε := by
  intro ε hε
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = N * ENNReal.ofReal ‖P‖ := ⟨_, rfl⟩
  have hAt : A ≠ ⊤ := by
    rw [hA]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  obtain ⟨δ, hδ0, hδ⟩ := EuclideanSpace.exists_pos_forall_enorm_rpow_mul_lt (N := N) one_pos hAt hε
  refine ⟨δ, hδ0, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ h hh
  have hPu : ‖P u‖ ≤ ‖P‖ := by
    calc ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖P‖ := mul_one _
  have hGae := MemLp.coeFn_toLp (SobolevEuclidean.memLp_fn (P u))
  have hae : (fun x ↦ ((SobolevEuclidean.memLp_fn (P u)).toLp _) (x + h)
        - ((SobolevEuclidean.memLp_fn (P u)).toLp _) x)
      =ᵐ[volume] fun x ↦ fn (P u) (x + h) - fn (P u) x := by
    have h1 := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hGae
    filter_upwards [h1, hGae] with x hx1 hx2
    simp only [Function.comp_apply] at hx1
    rw [hx1, hx2]
  rw [eLpNorm_congr_ae hae]
  refine lt_of_le_of_lt ?_ (hδ h hh)
  rw [ENNReal.rpow_one, hA]
  refine (SobolevEuclidean.eLpNorm_fn_sub_translate_le ENNReal.coe_ne_top (P u) h).trans ?_
  refine mul_le_mul' le_rfl ((SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le (P u)).trans ?_)
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hPu)

/-- Let $S$ be a subspace of $W^{1,p}(\Omega)$ and let $P : S \to W^{1,p}(\mathbb{R}^N)$ be a
bounded linear map with $Pu = u$ almost everywhere on $\Omega$ for every $u \in S$. Then the
image of $u \in S$ in $L^p(\Omega)$ is the restriction to $\Omega$ of
$Pu \in L^p(\mathbb{R}^N)$.

Thus the image of the unit ball of $S$ in $L^p(\Omega)$ is the set of restrictions to $\Omega$
of the family $\mathcal{F} = P(B_S)$. The image in $L^p(\Omega)$ is `SobolevMultiIndex.fnL` on
the subspace. -/
theorem HasSobolevExtensionOn.fnL_comp_subtypeL_apply (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤)
    (hP : ∀ u : S, fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fn (u : SobolevEuclidean N 1 p Ω)) (u : S) :
    (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume ∘L S.subtypeL) u
      = Lp.restrictCLM ℝ ℝ p volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
          ((SobolevEuclidean.memLp_fn (P u)).toLp _) := by
  refine Lp.ext (Filter.EventuallyEq.trans ?_ (Lp.coeFn_restrictCLM _ _).symm)
  refine Filter.EventuallyEq.trans (hP u).symm (Filter.EventuallyEq.symm ?_)
  exact ae_restrict_of_ae (MemLp.coeFn_toLp (SobolevEuclidean.memLp_fn (P u)))

/-- Let $1 \le p < \infty$, let $\Omega \subseteq \mathbb{R}^N$ be open with finite measure, and let
$S$ be a subspace of $W^{1,p}(\Omega)$ that has a Sobolev extension operator. Then the image of
the unit ball of $S$ in $L^p(\Omega)$ has compact closure.

The image is the set of restrictions to $\Omega$ of the family $\mathcal{F} = P(B_S) \subseteq
W^{1,p}(\mathbb{R}^N)$. This family is bounded in $L^p(\mathbb{R}^N)$ and uniformly continuous
under translation in $L^p$ by Proposition 9.3 of [brezis2011functional], so the Kolmogorov–M.
Riesz–Fréchet theorem
`MeasureTheory.Lp.isCompact_closure_image_restrictCLM_of_uniform_translate` applies. -/
theorem HasSobolevExtensionOn.isCompact_closure_image_closedBall_self
    (hS : HasSobolevExtensionOn S)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompact (closure (⇑(fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume ∘L
      S.subtypeL) '' closedBall 0 1)) := by
  obtain ⟨P, hP⟩ := id hS
  have himg : ⇑(fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume ∘L S.subtypeL) ''
      closedBall 0 1 = Lp.restrictCLM ℝ ℝ p volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ''
        ((fun u : S ↦ (SobolevEuclidean.memLp_fn (P u)).toLp _) '' closedBall (0 : S) 1) := by
    rw [Set.image_image]
    exact Set.image_congr fun u _ ↦ HasSobolevExtensionOn.fnL_comp_subtypeL_apply P hP u
  rw [himg]
  exact Lp.isCompact_closure_image_restrictCLM_of_uniform_translate ENNReal.coe_ne_top
    (HasSobolevExtensionOn.isBounded_image_closedBall_self P)
    (HasSobolevExtensionOn.uniform_translate_image_closedBall_self P) hΩ

/-- **The abstract Rellich–Kondrachov lemma at $q = p$.** Let $1 \le p < \infty$, let
$\Omega \subseteq \mathbb{R}^N$ be open with finite measure, in any dimension $N$, and let $S$
be a subspace of $W^{1,p}(\Omega)$ that has a Sobolev extension operator. Then the injection
$S \subset L^p(\Omega)$ is a compact embedding.

This is the last sentence of Theorem 9.16 of [brezis2011functional],
"$W^{1,p}(\Omega) \subset L^p(\Omega)$ with compact injection", in the generality of its proof.
It needs no case distinction between $p < N$, $p = N$ and $p > N$, which the proof uses only for
the exponents $q \ne p$. The injection is `SobolevMultiIndex.toLpₗOn`, and the proof is
`HasSobolevExtensionOn.isCompact_closure_image_closedBall_self`. -/
theorem HasSobolevExtensionOn.isCompactEmbedding_toLpOn_self (hS : HasSobolevExtensionOn S)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      fun u ↦ memLp (u : SobolevEuclidean N 1 p Ω)) := by
  rw [toLpₗOn_self]
  exact isCompactEmbedding_of_isCompact_closure_image_closedBall
    (fun _ _ huv ↦ Subtype.ext (fnL_injective huv))
    (hS.isCompact_closure_image_closedBall_self hΩ)

/-- **The Rellich–Kondrachov theorem, the injection into $L^p$, on an extension domain.** Let
$1 \le p < \infty$ and let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain of
finite measure. Then the injection $W^{1,p}(\Omega) \subset L^p(\Omega)$ is compact. This is the
last sentence of Theorem 9.16 of [brezis2011functional].

The statement holds in every dimension and for every $p$, including the case $N = 1 = p$ that
`SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one` leaves out. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      fun u ↦ SobolevMultiIndex.memLp u) :=
  SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top _ (hΩ.isCompactEmbedding_toLpOn_self hμ)

end RellichSelf

/-! ### Remark 20: the compactness clauses on $W_0^{1,p}(\Omega)$ of an arbitrary open set -/

section RellichZero

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

namespace SobolevEuclideanZero

/-- **The compact injection $W_0^{1,p}(\Omega) \subset L^p(\Omega)$ on an arbitrary open set.** Let
$1 \le p < \infty$ and let $\Omega \subseteq \mathbb{R}^N$ be an open set of finite measure, for
example a bounded one, with no regularity, in any dimension $N$. Then the injection
$W_0^{1,p}(\Omega) \subset L^p(\Omega)$ is compact. This is the compactness clause of Remark 20
in Chapter 9 of [brezis2011functional]: "Similarly, the conclusion of Theorem 9.16 is true for
$W_0^{1,p}(\Omega)$ with an arbitrary bounded open set $\Omega$".

The proof is `HasSobolevExtensionOn.isCompactEmbedding_toLpOn_self` with $S = W_0^{1,p}(\Omega)$
and extension by zero (`SobolevEuclideanZero.hasSobolevExtensionOn`). The clauses for the other
exponents $q$ of Theorem 9.16 are `SobolevEuclideanZero.isCompactEmbedding_toLp_of_lt` ($p < N$,
$1 \le q < p^*$), `SobolevEuclideanZero.isCompactEmbedding_toLp_of_eq` ($p = N \ge 2$,
$N \le q < \infty$) and `SobolevEuclideanZero.isCompactEmbedding_toContinuousMapOnL` ($p > N$,
into $C(\overline{\Omega})$). This is the compactness of the injection
$H_0^1(\Omega) \subset L^2(\Omega)$ that the proofs of Theorems 9.23 and 9.31 use
(`SobolevEuclideanZero.isCompactOperator_fnL`). -/
theorem isCompactEmbedding_toLp (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclideanZero N 1 p Ω) fun u ↦ memLp (u : SobolevEuclidean N 1 p Ω)) :=
  hasSobolevExtensionOn.isCompactEmbedding_toLpOn_self hΩ

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- Let $1 \le p < \infty$ and let $\Omega \subseteq \mathbb{R}^N$ be an open set of finite measure.
Then the bounded injection $W_0^{1,p}(\Omega) \to L^p(\Omega)$, `SobolevMultiIndexZero.fnL`, is
a compact embedding. This follows from Remark 20 in Chapter 9 of [brezis2011functional].

The exponent is stated as an element of $[1, \infty]$ with $p \ne \infty$, the form that the
elliptic theory at $p = 2$ uses. -/
theorem isCompactEmbedding_fnL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactEmbedding (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 p Ω volume).toLinearMap := by
  lift p to ℝ≥0 using hp
  have h := isCompactEmbedding_toLp (p := p) (Ω := Ω) hΩ
  rwa [SobolevMultiIndexZero.toLpₗOn_eq_fnL (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)
    (μ := volume)] at h

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- Let $1 \le p < \infty$ and let $\Omega \subseteq \mathbb{R}^N$ be an open set of finite measure.
Then the injection $W_0^{1,p}(\Omega) \to L^p(\Omega)$ is a compact operator.

This is the form of `SobolevEuclideanZero.isCompactEmbedding_toLp` that the Fredholm alternative
for the elliptic Dirichlet problem uses at $p = 2$, as in the proof of Theorem 9.23 of
[brezis2011functional]: "$T : L^2 \to L^2$ is a compact operator since $\Omega$ is bounded". -/
theorem isCompactOperator_fnL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactOperator (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 p Ω volume) :=
  (isCompactEmbedding_fnL hp hΩ).isCompactOperator

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an open set of finite measure, let $1 \le p < N$, let
$1/p^* = 1/p - 1/N$, and let $q \le p^*$. Then every $u \in W_0^{1,p}(\Omega)$ lies in
$L^q(\Omega)$. This is the membership for the case $p < N$ of Remark 20 in Chapter 9 of
[brezis2011functional]. -/
theorem memLp_fn_of_le_sobolevConj (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q ≤ p')
    (u : SobolevEuclideanZero N 1 p Ω) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hasSobolevExtensionOn.memLp_fn_of_le_sobolevConj hΩ hpN hp' hqp' u

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set of finite measure, let
$1 \le p < N$, let $1/p^* = 1/p - 1/N$, and let $1 \le q < p^*$. Then the injection
$W_0^{1,p}(\Omega) \subset L^q(\Omega)$ is compact. This is Remark 20 in Chapter 9 of
[brezis2011functional] for the first case of Theorem 9.16. -/
theorem isCompactEmbedding_toLp_of_lt [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q < p') :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclideanZero N 1 p Ω) (memLp_fn_of_le_sobolevConj hΩ hpN hp' hqp'.le)) :=
  SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn hasSobolevExtensionOn hΩ hpN
    hp' hqp'

/-- Let $N \ge 2$, let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set of finite measure,
and let $N \le q < \infty$. Then the injection $W_0^{1,N}(\Omega) \subset L^q(\Omega)$ is
compact. This is Remark 20 in Chapter 9 of [brezis2011functional] for the second case of Theorem
9.16.

The injection $W_0^{1,N}(\Omega) \subset W_0^{1,r}(\Omega)$ is continuous for an $r < N$ with
$r^* > q$ (`SobolevMultiIndexZero.toLowerExponentL`), and
$W_0^{1,r}(\Omega) \subset L^q(\Omega)$ is compact by the case $p < N$. -/
theorem isCompactEmbedding_toLp_of_eq [Fact (1 ≤ (N : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N Ω volume
      (SobolevEuclideanZero N 1 N Ω) (memLp_fn_of_eq hN hq)) := by
  obtain ⟨r, hr1, hrN, hr', hq2⟩ := NNReal.exists_lowerExponent hN hq
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  have hrp : (r : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by exact_mod_cast hrN.le
  exact SobolevMultiIndex.isCompactEmbedding_toLpₗOn_of_comp
    (SobolevMultiIndexZero.toLowerExponentL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1
      (N : ℝ≥0∞) (r : ℝ≥0∞) volume hΩ hrp)
    (SobolevMultiIndexZero.isContinuousEmbedding_toLowerExponentL hΩ hrp)
    (SobolevMultiIndexZero.fn_toLowerExponentL hΩ hrp)
    (SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn
      (S := SobolevEuclideanZero N 1 r Ω) hasSobolevExtensionOn hΩ hrN hr' hq2) _

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, let $N < p < \infty$, and let
$K \supseteq \Omega$ be compact, for example $K = \overline{\Omega}$ for a bounded $\Omega$.
Then the map $W_0^{1,p}(\Omega) \to C(K)$ that takes the continuous representative is a compact
embedding. This is Remark 20 in Chapter 9 of [brezis2011functional] for the third case of
Theorem 9.16: "$W_0^{1,p}(\Omega) \subset C(\overline{\Omega})$ with compact injection".

The map is `HasSobolevExtensionOn.toContinuousMapOnL` for extension by zero. -/
theorem isCompactEmbedding_toContinuousMapOnL (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))}
    [CompactSpace K] (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    IsCompactEmbedding
      ((hasSobolevExtensionOn (N := N) (p := p) (Ω := Ω)).toContinuousMapOnL hp K).toLinearMap :=
  hasSobolevExtensionOn.isCompactEmbedding_toContinuousMapOnL hp hK

end SobolevEuclideanZero

end RellichZero

/-! ### Compact injection $W^{k+1,p}(\Omega) \subset W^{k,p}(\Omega)$ on an extension domain -/

section CompactLower

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The compact injection between successive orders on an extension domain.** Let
$1 \le p < \infty$, let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain of
finite measure, in any dimension $N$, and let $k \ge 0$. Then the injection
$W^{k+1,p}(\Omega) \subset W^{k,p}(\Omega)$ is compact. This is Theorem 7.3.9 of
[han2009theoretical], with the Lipschitz domain of the source replaced by an extension domain.

The injection is `SobolevMultiIndex.toLowerOrderL`. The proof is by induction on $k$ from the
compact injection $W^{1,p}(\Omega) \subset L^p(\Omega)$
(`SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain`, which needs no
case distinction on $p$ and $N$), with the inductive step
`SobolevMultiIndex.isCompactEmbedding_of_forall_weakDeriv_eq` as in
`SobolevEuclidean.isCompactEmbedding_toLower_of_lt`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (k : ℕ) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω
      volume (Nat.le_succ k)).toLinearMap := by
  have hc := SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain hΩ hμ
  rw [toLpₗ_self] at hc
  exact SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isCompactEmbedding_fnL hc k

end CompactLower

/-! ### Composition lemmas for the embeddings of $W^{k,p}(\Omega)$ -/

section Composition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (1 ≤ q)] {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- Let $E$ be finite-dimensional, $F$ complete, $\mu(\Omega) < \infty$ and
$1 \le q \le p \le \infty$, and suppose that every $u \in W^{k,p}(\Omega)$ lies in
$L^q(\Omega)$. Then the injection $W^{k,p}(\Omega) \subset L^q(\Omega)$ is a continuous
embedding.

The bound is Hölder's inequality $\|f\|_q \le \mu(\Omega)^{1/q - 1/p} \|f\|_p$. -/
theorem isContinuousEmbedding_toLpₗ_of_le (hΩ : μ Ω ≠ ⊤) (hqp : q ≤ p)
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E))) :
    IsContinuousEmbedding (toLpₗ F b k p Ω μ h) := by
  have hfin : μ (Ω : Set E) ^ (1 / q.toReal - 1 / p.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by
      have hp0 : (0 : ℝ≥0∞) < p := zero_lt_one.trans_le Fact.out
      rcases eq_or_ne p ⊤ with rfl | hp
      · simp only [ENNReal.toReal_top, div_zero, sub_zero]
        positivity
      · have hq0 : 0 < q.toReal :=
          ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' (ne_top_of_le_ne_top hp hqp)
        have := ENNReal.toReal_mono hp hqp
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hq0 this) hΩ
  refine isContinuousEmbedding_toLpₗ_of_eLpNorm_le h
    (C := (μ (Ω : Set E) ^ (1 / q.toReal - 1 / p.toReal)).toReal) fun u ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin, mul_comm]
  calc eLpNorm (fn u) q (μ.restrict (Ω : Set E))
      ≤ eLpNorm (fn u) p (μ.restrict (Ω : Set E))
        * (μ.restrict (Ω : Set E)) Set.univ ^ (1 / q.toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp (memLp u).aestronglyMeasurable
    _ ≤ ENNReal.ofReal ‖u‖ * μ (Ω : Set E) ^ (1 / q.toReal - 1 / p.toReal) := by
        rw [Measure.restrict_apply_univ]
        exact mul_le_mul' (eLpNorm_fn_le_ofReal_norm u) le_rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- **Pull-back of a compact embedding.** Let $1 \le p, q, r \le \infty$, and let
$T : W^{k,p}(\Omega) \to W^{k',r}(\Omega)$ be a bounded linear map and a continuous embedding
with $Tu = u$ almost everywhere on $\Omega$. If every $v \in W^{k',r}(\Omega)$ lies in
$L^q(\Omega)$ and the injection $W^{k',r}(\Omega) \subset L^q(\Omega)$ is compact, then every
$u \in W^{k,p}(\Omega)$ lies in $L^q(\Omega)$ and the injection
$W^{k,p}(\Omega) \subset L^q(\Omega)$ is compact. -/
theorem isCompactEmbedding_toLpₗ_of_comp {k' : ℕ} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (T : SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k' r Ω μ)
    (hT : IsContinuousEmbedding T.toLinearMap)
    (hfn : ∀ u, fn (T u) =ᵐ[μ.restrict (Ω : Set E)] fn u)
    {h' : ∀ v : SobolevMultiIndex F b k' r Ω μ, MemLp (fn v) q (μ.restrict (Ω : Set E))}
    (hc : IsCompactEmbedding (toLpₗ F b k' r Ω μ h')) :
    ∃ h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E)),
      IsCompactEmbedding (toLpₗ F b k p Ω μ h) := by
  refine ⟨fun u ↦ (memLp_congr_ae (hfn u)).1 (h' (T u)), ?_⟩
  have := hT.comp_isCompactEmbedding hc
  convert this using 1
  refine LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn _ u).trans ?_)
  exact (hfn u).symm.trans (toLpₗ_coeFn h' (T u)).symm

end SobolevMultiIndex

end Composition

/-! ### Rellich–Kondrachov at every order on an extension domain -/

section HigherOrder

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Let $N \ge 2$, let $\Omega \subseteq \mathbb{R}^N$ be an extension domain for every exponent
with finite measure, let $N \le p < \infty$, and let $1 \le q < \infty$. Then every
$u \in W^{1,p}(\Omega)$ lies in $L^q(\Omega)$, and the injection
$W^{1,p}(\Omega) \subset L^q(\Omega)$ is compact.

This generalizes `SobolevEuclidean.isCompactEmbedding_toLp_of_le` from $C^1$ chart domains to
extension domains. The injection $W^{1,p}(\Omega) \subset W^{1,r}(\Omega)$ is continuous for an
$r < N$ with $r^* > q$, and $W^{1,r}(\Omega) \subset L^q(\Omega)$ is compact by the case $r < N$
(`SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn`). -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_le_of_isSobolevExtensionDomainAll
    {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hN : 2 ≤ N) (hp : (N : ℝ≥0) ≤ p) :
    ∃ h : ∀ u : SobolevEuclidean N 1 p Ω,
        MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      IsCompactEmbedding
        (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume h) := by
  obtain ⟨r, hr1, hrN, hr', hq2⟩ := NNReal.exists_lowerExponent hN
    (q := max q (N : ℝ≥0)) (le_max_right _ _)
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  have hqr : q < 2 * max q (N : ℝ≥0) := lt_of_le_of_lt (le_max_left _ _) hq2
  have hc := SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top
    (fun u ↦ (hΩ r).memLp_fn_of_le_sobolevConj hμ hrN hr' hqr.le ⟨u, Submodule.mem_top⟩)
    (SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn (hΩ r) hμ hrN hr' hqr)
  have hrp : (r : ℝ≥0∞) ≤ p := by exact_mod_cast hrN.le.trans hp
  exact isCompactEmbedding_toLpₗ_of_comp (toLowerExponentL ℝ _ 1 p r volume hμ hrp)
    (isContinuousEmbedding_toLowerExponentL hμ hrp) (fn_toLowerExponentL hμ hrp) hc

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain, let $N < p < \infty$, and
let $K \supseteq \Omega$ be compact. Then the map $W^{1,p}(\Omega) \to C(K)$ that takes the
continuous representative, `SobolevEuclidean.toContinuousMapL`, is a compact embedding.

This generalizes `SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt` from $C^1$ chart
domains to extension domains. The proof is the Arzelà–Ascoli argument of
`HasSobolevExtensionOn.isCompactEmbedding_toContinuousMapOnL`. -/
theorem SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_isSobolevExtensionDomain
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N p Ω) (hp : (N : ℝ≥0) < p)
    {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    IsCompactEmbedding (SobolevEuclidean.toContinuousMapL hΩ hp K).toLinearMap := by
  have hc := hΩ.isCompactEmbedding_toContinuousMapOnL hp hK
  have hι : IsContinuousEmbedding ((LinearMap.id (R := ℝ)).codRestrict
      (⊤ : Submodule ℝ (SobolevEuclidean N 1 p Ω)) fun _ ↦ Submodule.mem_top) :=
    ⟨fun u v huv ↦ by simpa using congrArg Subtype.val huv, 1, fun u ↦ by simp⟩
  exact hι.comp_isCompactEmbedding hc

/-- **The Rellich–Kondrachov theorem at order $k + 1 < N/p$.** Let $\Omega \subseteq \mathbb{R}^N$
be an extension domain for every exponent with finite measure, let $1 \le p < \infty$ with
$k + 1 < N/p$, let $1/p^* = 1/p - (k+1)/N$, and let $1 \le q < p^*$. Then every
$u \in W^{k+1,p}(\Omega)$ lies in $L^q(\Omega)$, and the injection
$W^{k+1,p}(\Omega) \subset L^q(\Omega)$ is compact. This is Theorem 7.3.8(a) of
[han2009theoretical], with the Lipschitz domain of the source replaced by an extension domain.

The injection $W^{k+1,p}(\Omega) \subset W^{1,r}(\Omega)$ with $1/r = 1/p - k/N$ is continuous,
and $W^{1,r}(\Omega) \subset L^q(\Omega)$ is compact for $q < r^* = p^*$. -/
theorem SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_lt (k : ℕ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hk : ((k + 1 : ℕ) : ℝ) < N / p)
    {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (k + 1 : ℕ) / N) (hq : q < p') :
    ∃ h : ∀ u : SobolevEuclidean N (k + 1) p Ω,
        MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      IsCompactEmbedding
        (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume h) := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hN0 : (0 : ℝ) < N :=
    (div_pos_iff_of_pos_right hp0).1 (lt_of_le_of_lt (Nat.cast_nonneg _) hk)
  push_cast at hk
  have hk' : ((k : ℝ) + 1) / N < (p : ℝ)⁻¹ := by
    rw [div_lt_iff₀ hN0, inv_mul_eq_div]
    exact hk
  -- the intermediate exponent `1/r = 1/p − k/N`
  have hrinv_pos : (0 : ℝ) < (p : ℝ)⁻¹ - k / N := by
    have : (k : ℝ) / N < ((k : ℝ) + 1) / N :=
      div_lt_div_of_pos_right (by linarith) hN0
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ) = ((p : ℝ)⁻¹ - k / N)⁻¹ :=
    ⟨⟨_, inv_nonneg.2 hrinv_pos.le⟩, rfl⟩
  have hrinv : (r : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / N := by rw [hr, inv_inv]
  have hr0 : (0 : ℝ) < r := by rw [hr]; exact inv_pos.2 hrinv_pos
  have hpr : p ≤ r := by
    rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hr0 hp0, hrinv]
    exact sub_le_self _ (by positivity)
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
  have hN : 2 ≤ N ∨ 1 < p := by
    left
    have h1 : (1 : ℝ) < N / p := lt_of_le_of_lt (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hk
    have h2 : (p : ℝ) < N := by rwa [lt_div_iff₀ hp0, one_mul] at h1
    have h3 : (1 : ℝ) < N := lt_of_le_of_lt (by exact_mod_cast hp1) h2
    exact_mod_cast h3
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_orderOne k hΩ hN hpr hrinv.ge
  have hTemb : IsContinuousEmbedding T.toLinearMap :=
    ⟨fun u v huv ↦ ext_of_fn_ae_eq ((hT u).symm.trans (huv ▸ hT v)), _, T.le_opNorm⟩
  -- `r < N` and `r* = p*`
  have hrN : r < N := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_natCast, ← inv_lt_inv₀ hN0 hr0, hrinv]
    have : (k : ℝ) / N + (N : ℝ)⁻¹ = ((k : ℝ) + 1) / N := by
      rw [add_div, one_div]
    linarith
  have hp'r : (p' : ℝ)⁻¹ = (r : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
    rw [hp', hrinv]
    push_cast
    ring
  exact isCompactEmbedding_toLpₗ_of_comp T hTemb hT
    (SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top
      (fun u ↦ (hΩ r).memLp_fn_of_le_sobolevConj hμ hrN hp'r hq.le ⟨u, Submodule.mem_top⟩)
      (SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn (hΩ r) hμ hrN hp'r hq))

/-- **The Rellich–Kondrachov theorem at order $k + 1 = N/p$.** Let $N \ge 2$, let
$\Omega \subseteq \mathbb{R}^N$ be an extension domain for every exponent with finite measure,
let $1 \le p < \infty$ with $k + 1 = N/p$, and let $1 \le q < \infty$. Then every
$u \in W^{k+1,p}(\Omega)$ lies in $L^q(\Omega)$, and the injection
$W^{k+1,p}(\Omega) \subset L^q(\Omega)$ is compact. This is the compact form of Theorem 7.3.8(b)
of [han2009theoretical].

The injection $W^{k+1,p}(\Omega) \subset W^{1,N}(\Omega)$ is continuous, and then
`SobolevEuclidean.isCompactEmbedding_toLp_of_le_of_isSobolevExtensionDomainAll` applies. -/
theorem SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_eq (k : ℕ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hN : 2 ≤ N)
    (hk : ((k + 1 : ℕ) : ℝ) = N / p) :
    ∃ h : ∀ u : SobolevEuclidean N (k + 1) p Ω,
        MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      IsCompactEmbedding
        (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume h) := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have : Fact (1 ≤ ((N : ℝ≥0) : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ N)⟩
  have hpinv : (p : ℝ)⁻¹ = ((k + 1 : ℕ) : ℝ) / N := by
    rw [hk, div_div, mul_comm, ← div_div, div_self hN0.ne', one_div]
  have hpN : p ≤ (N : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast, ← inv_le_inv₀ hN0 hp0, hpinv, ← one_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_pos k) hN0.le
  have hrinv : (p : ℝ)⁻¹ - k / N ≤ ((N : ℝ≥0) : ℝ)⁻¹ := by
    rw [hpinv, NNReal.coe_natCast]
    refine le_of_eq ?_
    push_cast
    ring
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_orderOne k hΩ (Or.inl hN) hpN
    hrinv
  have hTemb : IsContinuousEmbedding T.toLinearMap :=
    ⟨fun u v huv ↦ ext_of_fn_ae_eq ((hT u).symm.trans (huv ▸ hT v)), _, T.le_opNorm⟩
  obtain ⟨h', hc⟩ :=
    SobolevEuclidean.isCompactEmbedding_toLp_of_le_of_isSobolevExtensionDomainAll (q := q) hΩ hμ
      hN le_rfl
  exact isCompactEmbedding_toLpₗ_of_comp T hTemb hT hc

end HigherOrder

/-!
### Compact embeddings of $W^{k,p}(\Omega)$ into $C(K)$, and into $W^{l,p}(\Omega)$ for $l < k$
-/

section HigherOrderContinuous

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The Rellich–Kondrachov theorem at order $k + 1 > N/p$, into $C(K)$.** Let
$\Omega \subseteq \mathbb{R}^N$ be an extension domain for every exponent, let
$1 \le p < \infty$ with $N \ge 2$ or $p > 1$, let $N/p < k + 1$, and let $K \supseteq \Omega$ be
compact. Then there is a bounded linear map $\iota : W^{k+1,p}(\Omega) \to C(K, \mathbb{R})$
with the following properties: every $u$ has a representative $\tilde u$ that is continuous on
$\mathbb{R}^N$ and equals $u$ almost everywhere on $\Omega$, with $\iota u = \tilde u|_K$; and
$\iota$ is a compact embedding.

This is Theorem 7.3.8(c) of [han2009theoretical] with $\beta = 0$ and with $k - [N/p] - 1$
replaced by $0$, and Example 7.4.2 of the same source at $p = 2$. The injection
$W^{k+1,p}(\Omega) \subset W^{1,r}(\Omega)$ is continuous for the $r > N$ of
`NNReal.exists_morrey_exponent`, and then
`SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_isSobolevExtensionDomain` applies. -/
theorem SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order (k : ℕ) {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hk : (N : ℝ) / p < (k + 1 : ℕ)) {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    ∃ ι : SobolevEuclidean N (k + 1) p Ω →L[ℝ] C(K, ℝ),
      (∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x : K, ι u x = ũ x) ∧
      IsCompactEmbedding ι.toLinearMap := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ≥0) < p := zero_lt_one.trans_le hp1
  obtain ⟨r, hpr, hNr, hr, -⟩ := NNReal.exists_morrey_exponent (N := N) k hp0 hk
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_orderOne k hΩ hN hpr hr
  have hTemb : IsContinuousEmbedding T.toLinearMap :=
    ⟨fun u v huv ↦ ext_of_fn_ae_eq ((hT u).symm.trans (huv ▸ hT v)), _, T.le_opNorm⟩
  refine ⟨(SobolevEuclidean.toContinuousMapL (hΩ r) hNr K).comp T, fun u ↦ ?_,
    hTemb.comp_isCompactEmbedding
      (SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_isSobolevExtensionDomain (hΩ r)
        hNr hK)⟩
  refine ⟨_, (SobolevEuclidean.contRep hNr _).continuous,
    (hT u).symm.trans (SobolevEuclidean.fn_ae_eq_toContinuousMapL (hΩ r) hNr (T u)),
    fun x ↦ rfl⟩

/-- **The compact injection $W^{k,p}(\Omega) \subset W^{l,p}(\Omega)$ for $l < k$.** Let
$1 \le p < \infty$ and let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain of
finite measure. Then for $l < k$ the injection $W^{k,p}(\Omega) \subset W^{l,p}(\Omega)$ is
compact. This is Theorem 7.3.9 of [han2009theoretical] for $1 \le p < \infty$.

The injection is `SobolevMultiIndex.toLowerOrderL`. It is the compact injection
$W^{k,p}(\Omega) \subset W^{k-1,p}(\Omega)$ followed by the continuous injection
$W^{k-1,p}(\Omega) \subset W^{l,p}(\Omega)$. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {k l : ℕ} (hlk : l < k) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω
      volume hlk.le).toLinearMap := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc := SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain hΩ hμ k
  have hl : l ≤ k := Nat.lt_succ_iff.1 hlk
  have hι := isContinuousEmbedding_toLowerOrderL (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := (p : ℝ≥0∞)) (Ω := Ω) (μ := volume) hl
  have := hc.comp_isContinuousEmbedding hι
  convert this using 1
  exact LinearMap.ext fun u ↦ rfl

end HigherOrderContinuous

/-! ### The case $p = \infty$: the injection $W^{1,\infty}(\Omega) \subset L^\infty(\Omega)$ -/

section RellichTop

open SobolevMultiIndex

/-- Let $f$ be almost everywhere strongly measurable and let $L \ge 0$. If
$\|f\|_{L^\infty(\mu)} \le L$, then $\|f(x)\| \le L$ for almost every $x$. -/
theorem MeasureTheory.ae_norm_le_of_eLpNorm_top_le {α G : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup G] {f : α → G} (hf : AEStronglyMeasurable f μ) {L : ℝ}
    (hL : 0 ≤ L) (h : eLpNorm f ⊤ μ ≤ ENNReal.ofReal L) : ∀ᵐ x ∂μ, ‖f x‖ ≤ L := by
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [← eLpNorm_exponent_top hf] at hx
  rw [← ENNReal.ofReal_le_ofReal_iff hL, ofReal_norm]
  exact hx.trans h

/-- Let $g_1, g_2 \in L^\infty(\mu)$ be real, let $g_1 = v_1$ and $g_2 = v_2$ almost everywhere, and
let $D \ge 0$. If $|v_1(x) - v_2(x)| \le D$ for almost every $x$, then
$\operatorname{dist}(g_1, g_2) \le D$ in $L^\infty(\mu)$. -/
theorem MeasureTheory.Lp.dist_le_of_ae_eq_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g₁ g₂ : Lp ℝ ⊤ μ) {v₁ v₂ : α → ℝ} (h₁ : g₁ =ᵐ[μ] v₁) (h₂ : g₂ =ᵐ[μ] v₂) {D : ℝ}
    (hD : 0 ≤ D) (h : ∀ᵐ x ∂μ, ‖v₁ x - v₂ x‖ ≤ D) : dist g₁ g₂ ≤ D := by
  rw [Lp.dist_def]
  have hae : ∀ᵐ x ∂μ, ‖(⇑g₁ - ⇑g₂) x‖ ≤ D := by
    filter_upwards [h₁, h₂, h] with x hx₁ hx₂ hx
    rw [Pi.sub_apply, hx₁, hx₂]
    exact hx
  have := eLpNorm_le_of_ae_bound (p := ⊤)
    ((Lp.aestronglyMeasurable g₁).sub (Lp.aestronglyMeasurable g₂)) hae
  simp only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul] at this
  calc (eLpNorm (⇑g₁ - ⇑g₂) ⊤ μ).toReal ≤ (ENNReal.ofReal D).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    _ = D := ENNReal.toReal_ofReal hD

/-- **The Arzelà–Ascoli theorem for a uniformly bounded, uniformly Lipschitz sequence.** Let $K$ be
a compact subset of a pseudometric space $E$, and let $v_n : E \to \mathbb{R}$ be functions that
are all Lipschitz with the same constant $L$ and satisfy $|v_n(x)| \le R$ for all $n$ and $x$.
Then there is a strictly increasing $\varphi : \mathbb{N} \to \mathbb{N}$ such that
$(v_{\varphi(n)})$ is uniformly Cauchy on $K$: for every $\varepsilon > 0$ there is $n_0$ with
$$|v_{\varphi(m)}(x) - v_{\varphi(n)}(x)| < \varepsilon \qquad \text{for all } m, n \ge n_0
  \text{ and } x \in K.$$

The proof applies `ContinuousMap.isCompact_closure_of_forall_norm_le` to the restrictions to
$K$. -/
theorem exists_strictMono_forall_dist_lt_of_lipschitzWith {E : Type*}
    [PseudoMetricSpace E] {K : Set E} (hK : IsCompact K) (v : ℕ → E → ℝ) {L : ℝ≥0} {R : ℝ}
    (hvl : ∀ n, LipschitzWith L (v n)) (hvb : ∀ n x, ‖v n x‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ε > 0, ∃ n₀, ∀ m ≥ n₀, ∀ n ≥ n₀, ∀ x ∈ K,
      dist (v (φ m) x) (v (φ n) x) < ε := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨f, hf⟩ : ∃ f : ℕ → C(K, ℝ), ∀ n x, f n x = v n x :=
    ⟨fun n ↦ ⟨fun x ↦ v n x, (hvl n).continuous.comp continuous_subtype_val⟩, fun _ _ ↦ rfl⟩
  have hcomp : IsCompact (closure (Set.range f)) := by
    refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := R) ?_ ?_
    · rintro _ ⟨n, rfl⟩ x
      rw [hf]
      exact hvb n x
    · refine Metric.equicontinuous_of_continuity_modulus (fun d ↦ (L : ℝ) * d) ?_ _ ?_
      · have : Tendsto (fun d : ℝ ↦ (L : ℝ) * d) (𝓝 0) (𝓝 ((L : ℝ) * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rwa [mul_zero] at this
      · rintro x y ⟨_, ⟨n, rfl⟩⟩
        simp only [hf, Subtype.dist_eq]
        exact (hvl n).dist_le_mul x y
  obtain ⟨g, -, φ, hφ, hlim⟩ :=
    hcomp.tendsto_subseq (x := f) fun n ↦ subset_closure (Set.mem_range_self n)
  refine ⟨φ, hφ, fun ε hε ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
  refine ⟨n₀, fun m hm n hn x hx ↦ ?_⟩
  have := ContinuousMap.dist_apply_le_dist (f := f (φ m)) (g := f (φ n)) ⟨x, hx⟩
  rw [hf, hf] at this
  exact this.trans_lt (hn₀ m hm n hn)

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The Lipschitz representative of an element of $W^{1,\infty}(\mathbb{R}^N)$.** There is a
constant $C \ge 0$ with the following property. For every $R \ge 0$ and every
$U \in W^{1,\infty}(\mathbb{R}^N)$ with $\|U\| \le R$, there is a function $v$ on $\mathbb{R}^N$
such that $U = v$ almost everywhere, $v$ is Lipschitz with constant $CR$, and $|v(x)| \le R$ for
every $x$.

The constant $C$ depends only on $N$; it comes from
`SobolevMultiIndex.exists_hasWeakFDerivOn_fn`. The Lipschitz representative is Remark 7 in
Chapter 9 of [brezis2011functional] on the convex set $\mathbb{R}^N$
(`HasWeakFDerivOn.exists_lipschitzOnWith_ae_eq_of_convex`). The bound $|v| \le R$ holds almost
everywhere by the $L^\infty$ norm, and everywhere by continuity, because Lebesgue measure is
positive on nonempty open sets. -/
theorem SobolevEuclidean.exists_lipschitzWith_ae_eq_top_of_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 0 ≤ R → ∀ U : SobolevEuclidean N 1 ⊤ ⊤, ‖U‖ ≤ R →
      ∃ v : EuclideanSpace ℝ (Fin N) → ℝ, fn U =ᵐ[volume] v ∧
        LipschitzWith (Real.toNNReal (C * R)) v ∧ ∀ x, ‖v x‖ ≤ R := by
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card (Fin N) •
      ‖(EuclideanSpace.basisFun (Fin N) ℝ).toBasis.equivFunL.toContinuousLinearMap‖ := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  refine ⟨Cb * N, by positivity, fun R hR U hU ↦ ?_⟩
  obtain ⟨w, hw, hwp, -, hwn⟩ := exists_hasWeakFDerivOn_fn U
  -- the almost everywhere bound of the weak derivative
  have hwae : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
      Set (EuclideanSpace ℝ (Fin N))), ‖w x‖ ≤ Cb * N * R := by
    have h1 : ∀ i : Fin N, eLpNorm (weakDeriv U (MultiIndexLE.single i)) ⊤
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
          Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal R := fun i ↦ by
      rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ← Lp.norm_def]
      exact ENNReal.ofReal_le_ofReal ((norm_weakDeriv_le U _).trans hU)
    have hwn' : eLpNorm w ⊤ (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
        Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal Cb *
          ∑ i, eLpNorm (weakDeriv U (MultiIndexLE.single i)) ⊤
            (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
              Set (EuclideanSpace ℝ (Fin N)))) := by
      rw [hCb]; exact hwn
    refine MeasureTheory.ae_norm_le_of_eLpNorm_top_le hwp.aestronglyMeasurable (by positivity)
      (hwn'.trans ?_)
    calc ENNReal.ofReal Cb * ∑ i, eLpNorm (weakDeriv U (MultiIndexLE.single i)) ⊤
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
            Set (EuclideanSpace ℝ (Fin N))))
        ≤ ENNReal.ofReal Cb * ∑ _i : Fin N, ENNReal.ofReal R := by
          gcongr with i
          exact h1 i
      _ = ENNReal.ofReal (Cb * N * R) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCb0, ENNReal.ofReal_natCast]
          ring
  -- the Lipschitz representative
  have hconv : Convex ℝ ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
      Set (EuclideanSpace ℝ (Fin N))) := by
    rw [Opens.coe_top]; exact convex_univ
  obtain ⟨v, hv, hvl⟩ := hw.exists_lipschitzOnWith_ae_eq_of_convex hconv (by positivity) hwae
  rw [Opens.coe_top, lipschitzOnWith_univ] at hvl
  rw [Opens.coe_top, Measure.restrict_univ] at hv
  -- the bound, almost everywhere by the `L^∞` norm, everywhere by continuity
  have hvae : ∀ᵐ x ∂volume, ‖v x‖ ≤ R := by
    have h1 : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
        Set (EuclideanSpace ℝ (Fin N))), ‖fn U x‖ ≤
          ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ ⊤ volume U‖ :=
      MeasureTheory.Lp.ae_norm_le_norm_top
        (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ ⊤ volume U)
    have h2 := (ae_restrict_iff' (⊤ : Opens (EuclideanSpace ℝ (Fin N))).isOpen.measurableSet).1 h1
    filter_upwards [h2, hv] with x hx hvx
    rw [← hvx]
    exact (hx (by simp)).trans ((norm_fnL_apply_le U).trans hU)
  have hcl : IsClosed {x | ‖v x‖ ≤ R} :=
    isClosed_le (continuous_norm.comp hvl.continuous) continuous_const
  have hset : {x | ‖v x‖ ≤ R} = univ :=
    hcl.closure_eq.symm.trans (Measure.dense_of_ae hvae).closure_eq
  exact ⟨v, hv, hvl, fun x ↦ eq_univ_iff_forall.1 hset x⟩

/-- **The compact injection $W^{1,\infty}(\Omega) \subset L^\infty(\Omega)$.** Let
$\Omega \subseteq \mathbb{R}^N$ be a bounded $W^{1,\infty}$-extension domain. Then the injection
$W^{1,\infty}(\Omega) \to L^\infty(\Omega)$, `SobolevMultiIndex.fnL`, is a compact embedding.
This is the case $p = \infty$, which the results for $p < \infty$ above do not cover; with
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt` it gives Theorem 7.3.9 of
[han2009theoretical] at $p = \infty$.

For a bounded sequence $u_n$, the extensions $Pu_n \in W^{1,\infty}(\mathbb{R}^N)$ have
Lipschitz representatives $v_n$ that are uniformly bounded and uniformly Lipschitz
(`SobolevEuclidean.exists_lipschitzWith_ae_eq_top_of_norm_le`). On the compact set
$\overline{\Omega}$ the Arzelà–Ascoli theorem gives a uniformly Cauchy subsequence
(`exists_strictMono_forall_dist_lt_of_lipschitzWith`). This subsequence is Cauchy in
$L^\infty(\Omega)$ (`MeasureTheory.Lp.dist_le_of_ae_eq_top`), hence convergent. -/
theorem SobolevEuclidean.isCompactEmbedding_fnL_top (hΩ : IsSobolevExtensionDomain N ⊤ Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    IsCompactEmbedding
      (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ Ω volume).toLinearMap := by
  refine IsCompactEmbedding.of_forall_exists_subseq_tendsto isContinuousEmbedding_fnL
    fun u hu ↦ ?_
  obtain ⟨M, hM⟩ := hu
  obtain ⟨P, hP⟩ := hΩ
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_lipschitzWith_ae_eq_top_of_norm_le (N := N)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- the extensions `P u_n`, bounded in `W^{1,∞}(ℝ^N)`, and their Lipschitz representatives
  have hrep : ∀ n, ∃ v : EuclideanSpace ℝ (Fin N) → ℝ,
      fn (u n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v ∧
      LipschitzWith (Real.toNNReal (C * (‖P‖ * M))) v ∧ ∀ x, ‖v x‖ ≤ ‖P‖ * M := fun n ↦ by
    have hUn : ‖P ⟨u n, Submodule.mem_top⟩‖ ≤ ‖P‖ * M :=
      (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _))
    obtain ⟨v, hv, hvl, hvb⟩ := hC (‖P‖ * M) (by positivity) _ hUn
    exact ⟨v, (hP ⟨u n, Submodule.mem_top⟩).symm.trans (ae_restrict_of_ae hv), hvl, hvb⟩
  choose v hv hvl hvb using hrep
  -- Arzelà–Ascoli on the compact `closure Ω`
  obtain ⟨φ, hφ, hφc⟩ := exists_strictMono_forall_dist_lt_of_lipschitzWith
    hb.isCompact_closure v hvl hvb
  -- the subsequence is Cauchy in `L^∞(Ω)`
  have hcauchy : CauchySeq fun n ↦
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ Ω volume (u (φ n)) := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨n₀, hn₀⟩ := hφc (ε / 2) (by positivity)
    refine ⟨n₀, fun m hm n hn ↦ ?_⟩
    refine (MeasureTheory.Lp.dist_le_of_ae_eq_top _ _ (hv (φ m)) (hv (φ n)) (D := ε / 2)
      (by positivity) ?_).trans_lt (by linarith)
    filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet] with x hx
    rw [← dist_eq_norm]
    exact (hn₀ m hm n hn x (subset_closure hx)).le
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨φ, w, hφ, hw⟩

end RellichTop

/-! ### The case $p = \infty$ at every order: the injection into $W^{l,\infty}(\Omega)$, $l < k$ -/

section RellichTopHigher

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The compact injection $W^{k+1,\infty}(\Omega) \subset W^{k,\infty}(\Omega)$.** Let
$\Omega \subseteq \mathbb{R}^N$ be a bounded $W^{1,\infty}$-extension domain. Then for every $k$
the injection $W^{k+1,\infty}(\Omega) \subset W^{k,\infty}(\Omega)$,
`SobolevMultiIndex.toLowerOrderL`, is compact.

The proof is by induction on $k$ from the compact injection
$W^{1,\infty}(\Omega) \subset L^\infty(\Omega)$ (`SobolevEuclidean.isCompactEmbedding_fnL_top`),
with the inductive step `SobolevMultiIndex.isCompactEmbedding_of_forall_weakDeriv_eq` as in
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain` for
$p < \infty$. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top
    (hΩ : IsSobolevExtensionDomain N ⊤ Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (k : ℕ) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis ⊤ Ω
      volume (Nat.le_succ k)).toLinearMap :=
  SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isCompactEmbedding_fnL
    (SobolevEuclidean.isCompactEmbedding_fnL_top hΩ hb) k

/-- **The compact injection $W^{k,\infty}(\Omega) \subset W^{l,\infty}(\Omega)$ for $l < k$.** Let
$\Omega \subseteq \mathbb{R}^N$ be a bounded $W^{1,\infty}$-extension domain. Then for $l < k$
the injection $W^{k,\infty}(\Omega) \subset W^{l,\infty}(\Omega)$ is compact. This is Theorem
7.3.9 of [han2009theoretical] at $p = \infty$.

The injection is `SobolevMultiIndex.toLowerOrderL`. It is the compact injection
$W^{k,\infty}(\Omega) \subset W^{k-1,\infty}(\Omega)$ followed by the continuous injection
$W^{k-1,\infty}(\Omega) \subset W^{l,\infty}(\Omega)$. This is the counterpart of
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt` for $p < \infty$. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt
    (hΩ : IsSobolevExtensionDomain N ⊤ Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) {k l : ℕ} (hlk : l < k) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis ⊤ Ω
      volume hlk.le).toLinearMap := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc := SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top hΩ hb k
  have hl : l ≤ k := Nat.lt_succ_iff.1 hlk
  have hι := isContinuousEmbedding_toLowerOrderL (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := ⊤) (Ω := Ω) (μ := volume) hl
  have := hc.comp_isContinuousEmbedding hι
  convert this using 1
  exact LinearMap.ext fun u ↦ rfl

end RellichTopHigher
