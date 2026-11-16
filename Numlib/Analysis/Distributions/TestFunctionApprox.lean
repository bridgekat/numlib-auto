/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Distribution.TestFunction
import Numlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Uniform approximation by test functions

Let $E$ be a finite-dimensional real normed space and let $\Omega \subseteq E$ be open. Let $f$ be
continuous on $\overline{\Omega}$, with $f = 0$ on the boundary $\partial \Omega$ and $f(x) \to 0$
as $x \to \infty$ in $\Omega$. This is the class of functions $u_0 \in C(\overline{\Omega})$ with
$u_0 = 0$ on $\Gamma$ in Corollary 10.5 of [brezis2011functional] and its footnote 6. This module
proves that such an $f$ is the uniform limit on $\Omega$ of a sequence of test functions
$\varphi_n \in \mathcal{D}(\Omega)$, the approximation that the proof of that corollary calls easily
established.

When $\Omega$ is bounded and $E$ is proper, the condition at infinity holds for every function,
because the filter of the points of $\Omega$ that tend to infinity is trivial.

## Main results

* `Bornology.IsBounded.cocompact_inf_principal_eq_bot` and
  `Bornology.IsBounded.tendsto_cocompact_inf_principal`: on a bounded set of a proper space, the
  filter at infinity along the set is trivial, so every function tends to every limit there.
* `exists_isCompact_subset_abs_lt`: for every $\varepsilon > 0$ there is a compact
  $K \subseteq \Omega$ with $|f| < \varepsilon$ on $\Omega \setminus K$.
* `continuous_indicator_mul_of_tsupport_subset`: for a continuous cut-off $\eta$ with support in
  $\Omega$, the function $\eta f$, extended by $0$ outside $\Omega$, is continuous.
* `exists_testFunction_abs_sub_le_of_hasCompactSupport`: a continuous function with compact support
  in $\Omega$ is uniformly approximated by test functions of $\Omega$.
* `exists_testFunction_abs_sub_le`: for every $\varepsilon > 0$ there is
  $\varphi \in \mathcal{D}(\Omega)$ with $|\varphi - f| \le \varepsilon$ on $\Omega$.
* `exists_testFunction_tendsto_of_continuousOn`: there is a sequence
  $\varphi_n \in \mathcal{D}(\Omega)$ with $\varphi_n \to f$ uniformly on $\Omega$.

## Proof outline

First, $|f|$ is small outside a compact set $K \subseteq \Omega$. A smooth cut-off $\eta$ that is
equal to $1$ on $K$ and has support in $\Omega$ makes $\eta f$, extended by $0$, a continuous
function with compact support in $\Omega$ that is close to $f$ on $\Omega$. A mollification of
$\eta f$ approximates it uniformly.

## Implementation notes

* The condition at infinity is `Tendsto f (cocompact E ⊓ 𝓟 Ω) (𝓝 0)`, the boundary is `frontier Ω`,
  and a test function of $\Omega$ is an element of Mathlib's `𝓓(Ω, ℝ)`, for $\Omega$ given as an
  element of `TopologicalSpace.Opens E`.
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions Topology

noncomputable section

/-- Let $E$ be a proper pseudometric space and let $s \subseteq E$ be bounded. Then the filter at
infinity along $s$ is trivial: `cocompact E ⊓ 𝓟 s = ⊥`. The reason is that $s$ is disjoint from
the complement of the compact set $\overline{s}$. -/
theorem Bornology.IsBounded.cocompact_inf_principal_eq_bot {E : Type*} [PseudoMetricSpace E]
    [ProperSpace E] {s : Set E} (hs : Bornology.IsBounded s) : cocompact E ⊓ 𝓟 s = ⊥ :=
  Filter.inf_eq_bot_iff.2 ⟨(closure s)ᶜ, hs.isCompact_closure.compl_mem_cocompact, s,
    mem_principal_self _, Set.eq_empty_iff_forall_notMem.2 fun _ hx ↦ hx.1 (subset_closure hx.2)⟩

/-- Let $E$ be a proper pseudometric space, let $s \subseteq E$ be bounded, and let
$f \colon E \to F$ be any function into a topological space. Then for every $y \in F$,
$f(x) \to y$ as $x \to \infty$ along $s$, because the filter `cocompact E ⊓ 𝓟 s` is trivial. -/
theorem Bornology.IsBounded.tendsto_cocompact_inf_principal {E F : Type*} [PseudoMetricSpace E]
    [ProperSpace E] [TopologicalSpace F] {s : Set E} (hs : Bornology.IsBounded s) (f : E → F)
    (y : F) : Tendsto f (cocompact E ⊓ 𝓟 s) (𝓝 y) := by
  rw [hs.cocompact_inf_principal_eq_bot]
  exact tendsto_bot

section Approximation

variable {E : Type*} [NormedAddCommGroup E]

/-- Let $E$ be a normed group, let $\Omega \subseteq E$ be open, and let $f \colon E \to \mathbb{R}$
be continuous on $\overline{\Omega}$, with $f = 0$ on $\partial \Omega$ and $f(x) \to 0$ as
$x \to \infty$ along $\Omega$. Then for every $\varepsilon > 0$ there is a compact set
$K \subseteq \Omega$ such that
$$|f(x)| < \varepsilon \quad \text{for all } x \in \Omega \setminus K.$$

Far from the origin, this is the hypothesis at infinity. Near the boundary, the set
$\{|f| < \varepsilon\}$ is relatively open in $\overline{\Omega}$ and contains
$\partial \Omega$, so its complement in a compact set is a compact subset of $\Omega$. The
boundary is `frontier Ω`, and the limit at infinity is along the filter `cocompact E ⊓ 𝓟 Ω`. -/
theorem exists_isCompact_subset_abs_lt {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ}
    (hf : ContinuousOn f (closure Ω)) (hf0 : ∀ x ∈ frontier Ω, f x = 0)
    (hft : Tendsto f (cocompact E ⊓ 𝓟 Ω) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧ ∀ x ∈ Ω \ K, |f x| < ε := by
  -- the tail
  have htail := (Metric.tendsto_nhds.1 hft) ε hε
  rw [eventually_inf_principal, hasBasis_cocompact.eventually_iff] at htail
  obtain ⟨C, hC, hCf⟩ := htail
  -- the relatively open set `{|f| < ε}`
  obtain ⟨V, hV, hVf⟩ := continuousOn_iff'.1 hf (ball 0 ε) isOpen_ball
  refine ⟨(C ∩ closure Ω) \ V, (hC.inter_right isClosed_closure).diff hV, fun x hx ↦ ?_,
    fun x hx ↦ ?_⟩
  · -- `K ⊆ Ω`: a point of `closure Ω` outside `V` is not on the frontier
    obtain ⟨⟨-, hxc⟩, hxV⟩ := hx
    by_contra hxΩ
    have hxΓ : x ∈ frontier Ω := by
      rw [frontier, hΩ.interior_eq]
      exact ⟨hxc, hxΩ⟩
    have : x ∈ f ⁻¹' ball 0 ε ∩ closure Ω := by
      refine ⟨?_, hxc⟩
      simp [hf0 x hxΓ, hε]
    rw [hVf] at this
    exact hxV this.1
  · obtain ⟨hxΩ, hxK⟩ := hx
    by_cases hxC : x ∈ C
    · have hxV : x ∈ V := by
        by_contra hxV
        exact hxK ⟨⟨hxC, subset_closure hxΩ⟩, hxV⟩
      have : x ∈ V ∩ closure Ω := ⟨hxV, subset_closure hxΩ⟩
      rw [← hVf] at this
      simpa [dist_eq_norm] using this.1
    · simpa [dist_eq_norm] using hCf hxC hxΩ

/-- Let $\Omega \subseteq E$ be open, let $f \colon E \to \mathbb{R}$ be continuous on $\Omega$, and
let $\eta \colon E \to \mathbb{R}$ be continuous with
$\operatorname{supp} \eta \subseteq \Omega$, where $\operatorname{supp}$ is the closed support.
Then the function equal to $\eta f$ on $\Omega$ and to $0$ outside $\Omega$ is continuous on
$E$. -/
theorem continuous_indicator_mul_of_tsupport_subset {Ω : Set E} (hΩ : IsOpen Ω) {f η : E → ℝ}
    (hf : ContinuousOn f Ω) (hη : Continuous η) (hηΩ : tsupport η ⊆ Ω) :
    Continuous (Ω.indicator fun x ↦ η x * f x) := by
  refine continuous_of_cover_nhds (s := fun b : Bool ↦ if b then Ω else (tsupport η)ᶜ)
    (fun x ↦ ?_) (fun b ↦ ?_)
  · by_cases hx : x ∈ Ω
    · exact ⟨true, by simpa using hΩ.mem_nhds hx⟩
    · refine ⟨false, by simpa using (isClosed_tsupport η).isOpen_compl.mem_nhds fun h ↦ hx (hηΩ h)⟩
  · cases b with
    | true =>
      change ContinuousOn _ Ω
      exact (hη.continuousOn.mul hf).congr fun x hx ↦ by simp [indicator_of_mem hx]
    | false =>
      change ContinuousOn _ (tsupport η)ᶜ
      refine (continuousOn_const (c := (0 : ℝ))).congr fun x hx ↦ ?_
      by_cases hxΩ : x ∈ Ω
      · simp [indicator_of_mem hxΩ, image_eq_zero_of_notMem_tsupport hx]
      · simp [indicator_of_notMem hxΩ]

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Let $E$ be a finite-dimensional real normed space, let $\Omega \subseteq E$ be open, and let
$g \colon E \to \mathbb{R}$ be continuous with compact support
$\operatorname{supp} g \subseteq \Omega$. Then for every $\varepsilon > 0$ there is a test
function $\varphi \in \mathcal{D}(\Omega)$ with
$$|\varphi(x) - g(x)| \le \varepsilon \quad \text{for all } x \in E.$$

The test function is a mollification $\rho_\delta \star g$, at a scale $\delta$ smaller than the
distance from $\operatorname{supp} g$ to the complement of $\Omega$ and smaller than the modulus
of uniform continuity of $g$ at $\varepsilon$ (`ContDiffBump.dist_normed_convolution_le`). -/
theorem exists_testFunction_abs_sub_le_of_hasCompactSupport {Ω : Opens E} {g : E → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω) {ε : ℝ}
    (hε : 0 < ε) : ∃ φ : 𝓓(Ω, ℝ), ∀ x, |φ x - g x| ≤ ε := by
  obtain ⟨δ₁, hδ₁, hδ₁Ω⟩ := hgc.exists_cthickening_subset_open Ω.isOpen hgΩ
  obtain ⟨δ₂, hδ₂, hδ₂g⟩ :=
    Metric.uniformContinuous_iff.1 (hgc.uniformContinuous_of_continuous hg) ε hε
  set δ : ℝ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  let ρ : ContDiffBump (0 : E) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let μ : Measure E := Measure.addHaar
  set ψ : E → ℝ := ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g with hψ
  have hψs : ContDiff ℝ ∞ ψ :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (n := ⊤) _ ρ.contDiff_normed
      hg.locallyIntegrable
  have hψc : HasCompactSupport ψ := ρ.hasCompactSupport_normed.convolution _ hgc
  have hψΩ : tsupport ψ ⊆ Ω := by
    refine (closure_mono (support_convolution_subset _)).trans ?_
    refine (closure_minimal ?_ isClosed_cthickening).trans hδ₁Ω
    rintro _ ⟨y, hy, z, hz, rfl⟩
    rw [ρ.support_normed_eq] at hy
    refine mem_cthickening_of_dist_le (y + z) z δ₁ _ (subset_closure hz) ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    exact (mem_ball_zero_iff.1 hy).le.trans (min_le_left _ _)
  refine ⟨⟨ψ, hψs, hψc, hψΩ⟩, fun x ↦ ?_⟩
  rw [← Real.dist_eq]
  refine ρ.dist_normed_convolution_le hg.aestronglyMeasurable fun y hy ↦ (hδ₂g ?_).le
  exact (mem_ball.1 hy).trans_le (min_le_right _ _)

/-- Let $E$ be a finite-dimensional real normed space, let $\Omega \subseteq E$ be open, and let
$f \colon E \to \mathbb{R}$ be continuous on $\overline{\Omega}$, with $f = 0$ on
$\partial \Omega$ and $f(x) \to 0$ as $x \to \infty$ along $\Omega$. Then for every
$\varepsilon > 0$ there is a test function $\varphi \in \mathcal{D}(\Omega)$ with
$$|\varphi(x) - f(x)| \le \varepsilon \quad \text{for all } x \in \Omega.$$

This is the approximation that [brezis2011functional] calls easily established in the proof of
Corollary 10.5. The condition at infinity holds for every bounded $\Omega$. By
`exists_isCompact_subset_abs_lt`, $|f| \le \varepsilon / 2$ outside a compact
$K \subseteq \Omega$. A smooth cut-off $\eta$, equal to $1$ on $K$ and with support in $\Omega$,
makes $\eta f$, extended by $0$, continuous with compact support in $\Omega$ and
$\varepsilon/2$-close to $f$ on $\Omega$. A mollification of $\eta f$ is $\varepsilon/2$-close
to it everywhere (`exists_testFunction_abs_sub_le_of_hasCompactSupport`). -/
theorem exists_testFunction_abs_sub_le {Ω : Opens E} {f : E → ℝ}
    (hf : ContinuousOn f (closure Ω)) (hf0 : ∀ x ∈ frontier Ω, f x = 0)
    (hft : Tendsto f (cocompact E ⊓ 𝓟 Ω) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, ℝ), ∀ x ∈ Ω, |φ x - f x| ≤ ε := by
  obtain ⟨K, hK, hKΩ, hKf⟩ := exists_isCompact_subset_abs_lt Ω.isOpen hf hf0 hft (half_pos hε)
  obtain ⟨η, hη, hηc, hηΩ, hη1, hη01⟩ :=
    exists_contDiff_one_on_of_isCompact_of_isOpen hK Ω.isOpen hKΩ
  set g : E → ℝ := (Ω : Set E).indicator fun x ↦ η x * f x with hg
  have hsupp : Function.support g ⊆ Function.support η := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h
    apply hx
    by_cases hxΩ : x ∈ (Ω : Set E)
    · simp [hg, indicator_of_mem hxΩ, h]
    · simp [hg, indicator_of_notMem hxΩ]
  have hgc : Continuous g :=
    continuous_indicator_mul_of_tsupport_subset Ω.isOpen (hf.mono subset_closure) hη.continuous
      hηΩ
  have hgs : HasCompactSupport g := hηc.mono hsupp
  have hgΩ : tsupport g ⊆ Ω := (closure_mono hsupp).trans hηΩ
  obtain ⟨φ, hφ⟩ := exists_testFunction_abs_sub_le_of_hasCompactSupport hgc hgs hgΩ (half_pos hε)
  refine ⟨φ, fun x hx ↦ ?_⟩
  have hgf : |g x - f x| ≤ ε / 2 := by
    simp only [hg, indicator_of_mem hx]
    by_cases hxK : x ∈ K
    · simp [hη1 x hxK, (half_pos hε).le]
    · have h2 := hKf x ⟨hx, hxK⟩
      rw [show η x * f x - f x = (η x - 1) * f x by ring, abs_mul]
      have h1 : |η x - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(hη01 x).1, (hη01 x).2]
      calc |η x - 1| * |f x| ≤ 1 * (ε / 2) := mul_le_mul h1 h2.le (abs_nonneg _) zero_le_one
        _ = ε / 2 := one_mul _
  calc |φ x - f x| = |(φ x - g x) + (g x - f x)| := by ring_nf
    _ ≤ |φ x - g x| + |g x - f x| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hφ x) hgf
    _ = ε := add_halves ε

/-- Let $E$ be a finite-dimensional real normed space, let $\Omega \subseteq E$ be open, and let
$f \colon E \to \mathbb{R}$ be continuous on $\overline{\Omega}$, with $f = 0$ on
$\partial \Omega$ and $f(x) \to 0$ as $x \to \infty$ along $\Omega$. Then there is a sequence of
test functions $\varphi_n \in \mathcal{D}(\Omega)$ such that $\varphi_n \to f$ uniformly on
$\Omega$.

These are the approximants $u_{0n}$ in the proof of Corollary 10.5 of [brezis2011functional],
and the condition at infinity is its footnote 6. The condition holds for every bounded $\Omega$.
The proof applies `exists_testFunction_abs_sub_le` with $\varepsilon = 1/(n+1)$. The source also
asks that $\varphi_n \to f$ in $L^2(\Omega)$. Corollary 10.5 does not need this, because the
heat semigroup is a contraction in $L^\infty$ (`Heat.IsSolution.eLpNorm_top_le`). -/
theorem exists_testFunction_tendsto_of_continuousOn {Ω : Opens E} {f : E → ℝ}
    (hf : ContinuousOn f (closure Ω)) (hf0 : ∀ x ∈ frontier Ω, f x = 0)
    (hft : Tendsto f (cocompact E ⊓ 𝓟 Ω) (𝓝 0)) :
    ∃ φ : ℕ → 𝓓(Ω, ℝ), TendstoUniformlyOn (fun n x ↦ φ n x) f atTop Ω := by
  have h : ∀ n : ℕ, ∃ φ : 𝓓(Ω, ℝ), ∀ x ∈ Ω, |φ x - f x| ≤ 1 / (n + 1) := fun n ↦
    exists_testFunction_abs_sub_le hf hf0 hft (by positivity)
  choose φ hφ using h
  refine ⟨φ, Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop n₀] with n hn x hx
  rw [Real.dist_eq, abs_sub_comm]
  refine (hφ n x hx).trans_lt (lt_of_le_of_lt ?_ hn₀)
  gcongr

end Approximation
