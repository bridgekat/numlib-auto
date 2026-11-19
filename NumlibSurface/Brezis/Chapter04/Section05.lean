/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.MeasureTheory.Function.LpSpace.KolmogorovRiesz
import Numlib.Topology.ContinuousMap.ArzelaAscoli
import NumlibSurface.Brezis.Chapter04.Section04

/-!
# Brezis, Section 4.5: Criterion for strong compactness in $L^p$

This module formalizes Section 4.5 of [brezis2011functional] for real-valued functions on
$\mathbb{R}^N$ with Lebesgue measure. The first result is the Ascoli–Arzelà theorem: a bounded,
uniformly equicontinuous set of continuous functions on a compact metric space has compact closure
(Theorem 4.25). The main result is the Kolmogorov–M. Riesz–Fréchet theorem (Theorem 4.26). Let
$\mathcal{F}$ be a bounded set in $L^p(\mathbb{R}^N)$, $1 \le p < \infty$, such that
$$\lim_{|h| \to 0} \|\tau_h f - f\|_p = 0 \quad \text{uniformly in } f \in \mathcal{F}, \qquad
  (\tau_h f)(x) = f(x + h). \qquad (22)$$
Then the restrictions of the functions of $\mathcal{F}$ to a set $\Omega$ of finite measure form a
set with compact closure in $L^p(\Omega)$. With the tightness condition (27), $\mathcal{F}$ itself
has compact closure in $L^p(\mathbb{R}^N)$ (Corollary 4.27), and the converse holds (Remark 13). The
module also proves the continuity of translation in $L^q$ (Lemma 4.3), the compactness of
$G \star \mathcal{B}$ for $G \in L^1$ and bounded $\mathcal{B}$ (Corollary 4.28), and gives an
example that the hypotheses of Theorem 4.26 do not give compactness in $L^p(\mathbb{R}^N)$ (Remark
12).

The results are instances of the backbone modules `Numlib.Topology.ContinuousMap.ArzelaAscoli` and
`Numlib.MeasureTheory.Function.LpSpace.KolmogorovRiesz`. The second module works over any
finite-dimensional real normed space with a Haar measure and with vector values. It also proves the
converse of Corollary 4.27 (`MeasureTheory.Lp.uniform_translate_of_isCompact_closure` and
`MeasureTheory.Lp.tight_of_isCompact_closure`) and the translation invariance
`MeasureTheory.eLpNorm_comp_add_right`.

## Main results

* Theorem 4.25 (Ascoli–Arzelà), `Brezis.Chapter04.theorem_4_25`: a bounded, uniformly equicontinuous
  subset of $C(K)$ has compact closure.
* Theorem 4.26 (Kolmogorov–M. Riesz–Fréchet), `Brezis.Chapter04.theorem_4_26`: a bounded set in
  $L^p(\mathbb{R}^N)$ that satisfies (22) has compact closure after restriction to a set of finite
  measure.
* Corollary 4.27, `Brezis.Chapter04.corollary_4_27`: a bounded set that satisfies (22) and the
  tightness condition (27) has compact closure in $L^p(\mathbb{R}^N)$.
* Lemma 4.3, `Brezis.Chapter04.lemma_4_3`: for $G \in L^q(\mathbb{R}^N)$, $1 \le q < \infty$,
  $\|\tau_h G - G\|_q \to 0$ as $h \to 0$.
* Corollary 4.28, `Brezis.Chapter04.corollary_4_28`: for $G \in L^1$ and bounded
  $\mathcal{B} \subseteq L^p$, the set $G \star \mathcal{B}$ has compact closure after restriction
  to a set of finite measure.
* Remark 12, `Brezis.Chapter04.remark_4_12`: the hypotheses of Theorem 4.26 do not give compact
  closure in $L^p(\mathbb{R}^N)$.
* Exercise 4.34, `Brezis.Chapter04.uniform_translate_of_isCompact_closure` and
  `Brezis.Chapter04.tight_of_isCompact_closure`: a set with compact closure in $L^p(\mathbb{R}^N)$
  satisfies (22) and (27).
* Remark 13, `Brezis.Chapter04.remark_4_13`: a set in $L^p(\mathbb{R}^N)$ has compact closure if and
  only if it is bounded and satisfies (22) and (27).

## Conventions

* The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)`, with the local notation `𝔼`, and Lebesgue
  measure `volume`.
* The translate $\tau_h f$ of $f \in L^p$ is written on the underlying function, as
  `fun x => f (x + h)`. The norm $\|\tau_h f - f\|_p$ is
  `eLpNorm (fun x => f (x + h) - f x) p volume`, with values in $[0, +\infty]$.
* Condition (22) is stated with a real $\varepsilon$: for every $\varepsilon > 0$ there is
  $\delta > 0$ with $\|\tau_h f - f\|_p < \varepsilon$ for all $f \in \mathcal{F}$ and all
  $|h| < \delta$.
* The restriction $\mathcal{F}|_\Omega$ is the image of $\mathcal{F}$ under the backbone's
  `MeasureTheory.Lp.restrictCLM ℝ ℝ p volume Ω`.

## Deviations from the source

* **Theorem 4.26 and Corollary 4.28** (generalization). Restriction may be to any set of finite
  outer measure. See `Brezis.Chapter04.theorem_4_26` and `Brezis.Chapter04.corollary_4_28`.
* **Translation invariance in the proof of Lemma 4.3** (generalization). The seminorm identity
  allows all extended nonnegative exponents and a.e. measurable functions. See
  `Brezis.Chapter04.eLpNorm_comp_add_right` and `Brezis.Chapter04.eLpNorm_comp_add_right_real`.
* **Remark 12 and Exercise 4.33** (reading). The counterexample uses translates of an interval
  indicator. The exercise treats any nonzero compactly supported continuous seed. See
  `Brezis.Chapter04.remark_4_12`.
* **Exercise 4.34** (reading). The results apply to sets with compact closure. The tightness
  statement gives a bounded measurable set, which can be enlarged to an open ball. See
  `Brezis.Chapter04.uniform_translate_of_isCompact_closure` and
  `Brezis.Chapter04.tight_of_isCompact_closure`.
-/

open Filter MeasureTheory Metric Topology
open scoped ENNReal

namespace Brezis.Chapter04

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **Theorem 4.25** of [brezis2011functional] (Ascoli–Arzelà). Let $K$ be a compact metric space
and let $\mathcal{H}$ be a bounded subset of $C(K)$, that is, $|f(x)| \le M$ for some $M$, all
$f \in \mathcal{H}$ and all $x \in K$. Assume that $\mathcal{H}$ is uniformly equicontinuous:
for every $\varepsilon > 0$ there is $\delta > 0$ such that
$$d(x_1, x_2) < \delta \implies |f(x_1) - f(x_2)| < \varepsilon \quad \text{for all } f \in
  \mathcal{H}.$$
Then the closure of $\mathcal{H}$ in $C(K)$ is compact.

The space $C(K)$ is `C(K, ℝ)` with the uniform norm. -/
theorem theorem_4_25 {K : Type*} [MetricSpace K] [CompactSpace K] {H : Set C(K, ℝ)}
    (hbdd : ∃ M : ℝ, ∀ f ∈ H, ∀ x, |f x| ≤ M)
    (hequi : ∀ ε > 0, ∃ δ > 0, ∀ x₁ x₂ : K, dist x₁ x₂ < δ → ∀ f ∈ H, |f x₁ - f x₂| < ε) :
    IsCompact (closure H) := by
  obtain ⟨M, hM⟩ := hbdd
  refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := M)
    (fun f hf x => by simpa only [Real.norm_eq_abs] using hM f hf x) ?_
  refine UniformEquicontinuous.equicontinuous (Metric.uniformEquicontinuous_iff.2 fun ε hε => ?_)
  obtain ⟨δ, hδ, h⟩ := hequi ε hε
  refine ⟨δ, hδ, fun x y hxy f => ?_⟩
  rw [Real.dist_eq]
  exact h x y hxy f f.2

/-- Condition (22) of [brezis2011functional], stated with a real $\varepsilon > 0$, implies the same
condition with $\varepsilon \in (0, +\infty]$, which is the form of the backbone. -/
theorem uniform_translate_of_real {p : ℝ≥0∞} {F : Set (Lp ℝ p (volume : Measure 𝔼))}
    (hτ : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : 𝔼, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ h : 𝔼, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p volume < ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hτ (min ε 1).toReal
    (ENNReal.toReal_pos (lt_min hε one_pos).ne'
      ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne)
  refine ⟨δ, hδ, fun f hf t ht => (h f hf t ht).trans_le ?_⟩
  rw [ENNReal.ofReal_toReal ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne]
  exact min_le_left _ _

/-- **Theorem 4.26** of [brezis2011functional] (Kolmogorov–M. Riesz–Fréchet). Let $\mathcal{F}$ be a
bounded set in $L^p(\mathbb{R}^N)$ with $1 \le p < \infty$. Assume that
$$\lim_{|h| \to 0} \|\tau_h f - f\|_p = 0 \quad \text{uniformly in } f \in \mathcal{F}. \qquad
  (22)$$
Let $\Omega \subseteq \mathbb{R}^N$ have finite measure. Then the closure of
$\mathcal{F}|_\Omega$ in $L^p(\Omega)$ is compact.

**Generalization.** The source assumes that $\Omega$ is measurable. The proof does not need
this, and the formal statement holds for every set $\Omega$ of finite outer measure. -/
theorem theorem_4_26 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {F : Set (Lp ℝ p (volume : Measure 𝔼))}
    (hF : Bornology.IsBounded F)
    (hτ : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : 𝔼, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε)
    {Ω : Set 𝔼} (hΩ : volume Ω < ∞) :
    IsCompact (closure (Lp.restrictCLM ℝ ℝ p volume Ω '' F)) :=
  Lp.isCompact_closure_image_restrictCLM_of_uniform_translate hp hF (uniform_translate_of_real hτ)
    hΩ.ne

/-- **Corollary 4.27** of [brezis2011functional]. Let $\mathcal{F}$ be a bounded set in
$L^p(\mathbb{R}^N)$ with $1 \le p < \infty$. Assume that $\mathcal{F}$ satisfies (22), and that
for every $\varepsilon > 0$ there is a bounded measurable set $\Omega \subseteq \mathbb{R}^N$
with
$$\|f\|_{L^p(\mathbb{R}^N \setminus \Omega)} < \varepsilon \quad \text{for all } f \in
  \mathcal{F}. \qquad (27)$$
Then $\mathcal{F}$ has compact closure in $L^p(\mathbb{R}^N)$.

The norm on $\mathbb{R}^N \setminus \Omega$ is the norm of `Ωᶜ.indicator f` in
$L^p(\mathbb{R}^N)$. -/
theorem corollary_4_27 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {F : Set (Lp ℝ p (volume : Measure 𝔼))} (hF : Bornology.IsBounded F)
    (hτ : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : 𝔼, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε)
    (htight : ∀ ε > (0 : ℝ), ∃ Ω : Set 𝔼, Bornology.IsBounded Ω ∧ MeasurableSet Ω ∧
      ∀ f ∈ F, eLpNorm (Ωᶜ.indicator f) p volume < ENNReal.ofReal ε) :
    IsCompact (closure F) := by
  refine Lp.isCompact_closure_of_uniform_translate_of_tight hp hF (uniform_translate_of_real hτ)
    fun ε hε => ?_
  obtain ⟨Ω, hΩb, hΩm, h⟩ := htight (min ε 1).toReal
    (ENNReal.toReal_pos (lt_min hε one_pos).ne'
      ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne)
  refine ⟨Ω, hΩb, hΩm, fun f hf => (h f hf).trans_le ?_⟩
  rw [ENNReal.ofReal_toReal ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne]
  exact min_le_left _ _

/-- **Lemma 4.3** of [brezis2011functional]. Let $G \in L^q(\mathbb{R}^N)$ with $1 \le q < \infty$.
Then
$$\lim_{h \to 0} \|\tau_h G - G\|_q = 0.$$
-/
theorem lemma_4_3 {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞) {G : 𝔼 → ℝ} (hG : MemLp G q volume) :
    Tendsto (fun h : 𝔼 => eLpNorm (fun x => G (x + h) - G x) q volume) (𝓝 0) (𝓝 0) := by
  have h1 : Tendsto (fun h : 𝔼 => -h) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔼))).neg
  refine ((hG.tendsto_eLpNorm_sub_translate Fact.out hq).comp h1).congr fun h => ?_
  simp only [Function.comp_apply, sub_neg_eq_add]

/-- **Corollary 4.28** of [brezis2011functional]. Let $G \in L^1(\mathbb{R}^N)$, let
$1 \le p < \infty$, and let $\mathcal{B}$ be a bounded set in $L^p(\mathbb{R}^N)$. Let
$\mathcal{F} = G \star \mathcal{B} = \{G \star u : u \in \mathcal{B}\}$. Then for every
$\Omega \subseteq \mathbb{R}^N$ of finite measure, the closure of $\mathcal{F}|_\Omega$ in
$L^p(\Omega)$ is compact.

The convolution with $G$ is the backbone's bounded operator `MeasureTheory.Lp.convolutionCLM`,
whose values are a.e. the convolutions $G \star u$ (`MeasureTheory.Lp.coeFn_convolutionCLM`).

**Generalization.** The restriction may be to any set of finite outer measure. -/
theorem corollary_4_28 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {G : 𝔼 → ℝ}
    (hG : Integrable G volume) {B : Set (Lp ℝ p (volume : Measure 𝔼))} (hB : Bornology.IsBounded B)
    {Ω : Set 𝔼} (hΩ : volume Ω < ∞) :
    IsCompact (closure (Lp.restrictCLM ℝ ℝ p volume Ω '' (Lp.convolutionCLM ℝ p hG '' B))) :=
  Lp.isCompact_closure_image_restrictCLM_convolutionCLM hp hG hB hΩ.ne

/-! ### Remark 12: the hypotheses of Theorem 4.26 do not give compactness in $L^p(\mathbb{R}^N)$ -/

/-- Translation preserves the $L^p$ norm on $\mathbb{R}$: for an a.e. strongly measurable
$f : \mathbb{R} \to \mathbb{R}$ and $h \in \mathbb{R}$, $\|f(\cdot + h)\|_p = \|f\|_p$.

**Generalization.** The $L^p$ norm identity used in the proof of Lemma 4.3 extends to the seminorm
of an a.e. measurable function and any extended nonnegative exponent. -/
theorem eLpNorm_comp_add_right_real {f : ℝ → ℝ} {p : ℝ≥0∞} (hf : AEStronglyMeasurable f volume)
    (h : ℝ) : eLpNorm (fun x => f (x + h)) p volume = eLpNorm f p volume :=
  MeasureTheory.eLpNorm_comp_add_right hf h

/-- **Remark 12** in Chapter 4 of [brezis2011functional], with Exercise 4.33. The hypotheses of
Theorem 4.26 do not imply that $\mathcal{F}$ has compact closure in $L^p(\mathbb{R}^N)$.
Precisely, for $1 \le p < \infty$ there is a bounded set $\mathcal{F}$ in $L^p(\mathbb{R})$ that
satisfies (22) and does not have compact closure in $L^p(\mathbb{R})$.

The example is the set of the translates $\varphi(\cdot + n)$, $n \in \mathbb{N}$, of the
indicator function $\varphi$ of $[0, 1)$. It satisfies (22) because translation is an isometry
of $L^p$ and $\varphi$ satisfies Lemma 4.3. Its closure is not compact, because the translates
are at mutual distance at least $1$.

**Reading.** The exercise gives a family for an arbitrary nonzero continuous seed with compact
support. The interval indicator supplies an alternative witness for the existential claim. -/
theorem remark_4_12 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ F : Set (Lp ℝ p (volume : Measure ℝ)), Bornology.IsBounded F ∧
      (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : ℝ, ‖h‖ < δ →
        eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε) ∧
      ¬ IsCompact (closure F) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set φ : ℝ → ℝ := (Set.Ico (0 : ℝ) 1).indicator fun _ => 1 with hφ
  have hφp : MemLp φ p volume :=
    memLp_indicator_const p measurableSet_Ico.nullMeasurableSet 1 (Or.inr measure_Ico_lt_top.ne)
  have hτ : ∀ t : ℝ, MemLp (fun x => φ (x + t)) p volume := fun t =>
    hφp.comp_measurePreserving (measurePreserving_add_right volume t)
  set x : ℕ → Lp ℝ p (volume : Measure ℝ) := fun n => (hτ n).toLp _ with hx
  refine ⟨Set.range x, ?_, ?_, ?_⟩
  · -- bounded: every translate has the norm of `φ`
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨(eLpNorm φ p volume).toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [mem_closedBall_zero_iff, hx, Lp.norm_toLp]
    exact ENNReal.toReal_mono hφp.eLpNorm_ne_top
      (eLpNorm_comp_add_right_real hφp.aestronglyMeasurable (n : ℝ)).le
  · -- (22): uniformly in `n`, from Lemma 4.3 for `φ` and the invariance of the norm
    intro ε hε
    have hlim := hφp.tendsto_eLpNorm_sub_translate Fact.out hp
    have hev := ENNReal.tendsto_nhds_zero.1 hlim (ENNReal.ofReal (ε / 2))
      (ENNReal.ofReal_pos.2 (by positivity))
    obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨δ, hδ, ?_⟩
    rintro _ ⟨n, rfl⟩ h hh
    have h1 : eLpNorm (fun y => φ (y - -h) - φ y) p volume ≤ ENNReal.ofReal (ε / 2) :=
      hδε (by simpa [dist_zero_right] using hh)
    simp only [sub_neg_eq_add] at h1
    have hcoe : ⇑(x n) =ᵐ[volume] fun y => φ (y + n) := (hτ n).coeFn_toLp
    have hcoe' : (fun y => (x n) (y + h)) =ᵐ[volume] fun y => φ (y + h + n) :=
      hcoe.comp_tendsto (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae
    calc eLpNorm (fun y => (x n) (y + h) - (x n) y) p volume
        = eLpNorm (fun y => φ (y + n + h) - φ (y + n)) p volume := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [hcoe, hcoe'] with y hy hy'
          rw [hy, hy', add_right_comm]
      _ = eLpNorm (fun y => φ (y + h) - φ y) p volume :=
          eLpNorm_comp_add_right_real ((hτ h).aestronglyMeasurable.sub hφp.aestronglyMeasurable)
            (n : ℝ)
      _ ≤ ENNReal.ofReal (ε / 2) := h1
      _ < ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, hε⟩
  · -- not relatively compact: the translates are `1`-separated
    intro hK
    have hsep : ∀ m n : ℕ, m ≠ n → 1 ≤ dist (x m) (x n) := by
      intro m n hmn
      rw [Lp.dist_def]
      set A : Set ℝ := Set.Ico (-(m : ℝ)) (1 - m) with hA
      have hAvol : volume A = 1 := by rw [hA, Real.volume_Ico]; simp
      have hae : (⇑(x m) - ⇑(x n)) =ᵐ[volume.restrict A] fun _ => (1 : ℝ) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ico]
        filter_upwards [(hτ m).coeFn_toLp, (hτ n).coeFn_toLp] with y hym hyn hyA
        rw [Pi.sub_apply, hym, hyn, hφ]
        obtain ⟨hy1, hy2⟩ := hyA
        have h1 : y + m ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have h2 : y + n ∉ Set.Ico (0 : ℝ) 1 := by
          rcases lt_or_gt_of_ne hmn with h | h
          · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
            exact fun hy => by linarith [hy.2]
          · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
            exact fun hy => by linarith [hy.1]
        rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, sub_zero]
      have hle : (1 : ℝ≥0∞) ≤ eLpNorm (⇑(x m) - ⇑(x n)) p volume := by
        calc (1 : ℝ≥0∞) = eLpNorm (fun _ : ℝ => (1 : ℝ)) p (volume.restrict A) := by
              rw [eLpNorm_const' _ hp0 hp, Measure.restrict_apply_univ, hAvol]
              simp
          _ = eLpNorm (⇑(x m) - ⇑(x n)) p (volume.restrict A) := (eLpNorm_congr_ae hae).symm
          _ ≤ eLpNorm (⇑(x m) - ⇑(x n)) p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
      have hne : eLpNorm (⇑(x m) - ⇑(x n)) p volume ≠ ∞ := by
        rw [← eLpNorm_congr_ae (Lp.coeFn_sub (x m) (x n))]
        exact (Lp.memLp (x m - x n)).eLpNorm_ne_top
      simpa using ENNReal.toReal_mono hne hle
    obtain ⟨a, -, ψ, hψ, hψa⟩ := hK.isSeqCompact (x := x) fun n => subset_closure ⟨n, rfl⟩
    obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.1 (Filter.Tendsto.cauchySeq hψa) 1 one_pos
    have h1 := hM M le_rfl (M + 1) (Nat.le_succ M)
    exact absurd h1 (not_lt.2 (hsep _ _ (hψ.injective.ne (Nat.succ_ne_self M).symm)))

/-! ### Remark 13: the converse of Corollary 4.27 -/

/-- Translation preserves the $L^p$ norm on $\mathbb{R}^N$: for an a.e. strongly measurable
$f : \mathbb{R}^N \to \mathbb{R}$ and $h \in \mathbb{R}^N$, $\|f(\cdot + h)\|_p = \|f\|_p$.

**Generalization.** The $L^p$ norm identity used in the proof of Lemma 4.3 extends to the seminorm
of an a.e. measurable function and any extended nonnegative exponent. -/
theorem eLpNorm_comp_add_right {f : 𝔼 → ℝ} {p : ℝ≥0∞} (hf : AEStronglyMeasurable f volume)
    (h : 𝔼) : eLpNorm (fun x => f (x + h)) p volume = eLpNorm f p volume :=
  MeasureTheory.eLpNorm_comp_add_right hf h

/-- **Exercise 4.34** of [brezis2011functional], uniform continuity of translation. Let
$1 \le p < \infty$ and let $\mathcal{F} \subseteq L^p(\mathbb{R}^N)$ have compact closure. Then
$\mathcal{F}$ satisfies (22).

This is the backbone's `MeasureTheory.Lp.uniform_translate_of_isCompact_closure`, with a real
$\varepsilon$ as in the source.

**Generalization.** The exercise assumes that $\mathcal{F}$ itself is compact. The statement
applies the result to its compact closure. -/
theorem uniform_translate_of_isCompact_closure {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {F : Set (Lp ℝ p (volume : Measure 𝔼))} (hF : IsCompact (closure F)) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : 𝔼, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε := fun ε hε =>
  Lp.uniform_translate_of_isCompact_closure hp hF (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)

/-- **Exercise 4.34** of [brezis2011functional], tightness. Let $1 \le p < \infty$ and let
$\mathcal{F} \subseteq L^p(\mathbb{R}^N)$ have compact closure. Then $\mathcal{F}$ satisfies
(27): for every $\varepsilon > 0$ there is a bounded measurable set
$\Omega \subseteq \mathbb{R}^N$ with $\|f\|_{L^p(\mathbb{R}^N \setminus \Omega)} < \varepsilon$
for all $f \in \mathcal{F}$.

This is the backbone's `MeasureTheory.Lp.tight_of_isCompact_closure`, with a real $\varepsilon$
as in the source.

**Reading.** The exercise assumes a compact $\mathcal{F}$ and gives a bounded open set $\Omega$.
The library assumes a compact closure and gives a bounded measurable set, which can be enlarged
to an open ball while preserving the tail bound. -/
theorem tight_of_isCompact_closure {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {F : Set (Lp ℝ p (volume : Measure 𝔼))} (hF : IsCompact (closure F)) :
    ∀ ε > (0 : ℝ), ∃ Ω : Set 𝔼, Bornology.IsBounded Ω ∧ MeasurableSet Ω ∧
      ∀ f ∈ F, eLpNorm (Ωᶜ.indicator f) p volume < ENNReal.ofReal ε := fun ε hε =>
  Lp.tight_of_isCompact_closure hp hF (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)

/-- **Remark 13** in Chapter 4 of [brezis2011functional]. Let $1 \le p < \infty$ and
$\mathcal{F} \subseteq L^p(\mathbb{R}^N)$. Then $\mathcal{F}$ has compact closure in
$L^p(\mathbb{R}^N)$ if and only if $\mathcal{F}$ is bounded, satisfies (22) and satisfies (27).

This is a complete characterization of the relatively compact subsets of $L^p(\mathbb{R}^N)$.
The direction "only if" is the converse of Corollary 4.27, Exercise 4.34 of the source. -/
theorem remark_4_13 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (F : Set (Lp ℝ p (volume : Measure 𝔼))) :
    IsCompact (closure F) ↔
      Bornology.IsBounded F ∧
      (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : 𝔼, ‖h‖ < δ →
        eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε) ∧
      ∀ ε > (0 : ℝ), ∃ Ω : Set 𝔼, Bornology.IsBounded Ω ∧ MeasurableSet Ω ∧
        ∀ f ∈ F, eLpNorm (Ωᶜ.indicator f) p volume < ENNReal.ofReal ε :=
  ⟨fun hF => ⟨hF.isBounded.subset subset_closure, uniform_translate_of_isCompact_closure hp hF,
    tight_of_isCompact_closure hp hF⟩,
    fun ⟨hF, hτ, htight⟩ => corollary_4_27 hp hF hτ htight⟩

end Brezis.Chapter04
