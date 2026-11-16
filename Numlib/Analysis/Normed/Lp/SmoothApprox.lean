/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.SmoothApprox`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Smooth functions with compact support in an open set are dense in $L^p$ of that set

Let $E$ be a finite-dimensional real normed space and let $1 \le p < \infty$. Mathlib's
`MeasureTheory.Lp.dense_hasCompactSupport_contDiff` says that the smooth functions with compact
support are dense in $L^p(E, \mu)$. It puts no condition on the support: for an open set
$\Omega \subseteq E$, an approximant of a function in $L^p(\Omega)$ may have support outside
$\Omega$. This module proves the stronger statement
`MeasureTheory.Lp.dense_contDiff_tsupport_subset`: the approximants can be chosen with compact
support contained in $\Omega$. This is the density of $C_c^\infty(\Omega)$ in $L^p(\Omega)$.

## Main results

* `exists_contDiff_one_on_of_isCompact_of_isOpen`: for a compact set $K$ inside an open set $U$,
  there is a smooth function with values in $[0, 1]$ that is $1$ on $K$ and has compact support
  inside $U$.
* `MeasureTheory.MemLp.exists_isCompact_eLpNorm_indicator_compl_le`: a function in $L^p(\Omega)$ is,
  up to a small $L^p$ error, supported in a compact subset of $\Omega$.
* `MeasureTheory.MemLp.exists_contDiff_tsupport_subset`: every function in $L^p(\Omega)$ is
  approximated in $L^p$ by smooth functions with compact support inside $\Omega$.
* `MeasureTheory.Lp.dense_contDiff_tsupport_subset`: the same statement as a density in the space
  $L^p(\Omega)$.

## Proof outline

A function in $L^p(\Omega)$ can fail to have compact support inside $\Omega$ in two ways: it has
mass far away, and it has mass near the boundary of $\Omega$. Mathlib has a lemma for each.
`MeasureTheory.MemLp.exists_eLpNorm_indicator_compl_lt` gives a set of finite measure that carries
all but $\varepsilon$ of the function, and `MeasureTheory.MemLp.eLpNorm_indicator_le` is the
absolute continuity of the $L^p$ norm. Inner regularity turns the first set into a compact subset of
$\Omega$. When the function $f_1$ is supported in a compact set $K \subseteq \Omega$, a smooth
approximant $g$ of $f_1$ is multiplied by a smooth cut-off $\eta$ that is $1$ on $K$ and has support
in $\Omega$. Since $\eta f_1 = f_1$, the error does not increase: $|\eta (f_1 - g)| \le |f_1 - g|$
pointwise.

## Implementation notes

* The cut-off function comes from the partition of unity API for manifolds,
  `exists_contMDiffMap_zero_one_of_isClosed`, read back through `contMDiff_iff_contDiff`.
-/

open MeasureTheory Set Topology

open scoped ContDiff ENNReal Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A **smooth Urysohn function**. Let $E$ be a finite-dimensional real normed space, let
$K \subseteq E$ be compact, let $U \subseteq E$ be open, and let $K \subseteq U$. Then there is
a smooth function $\eta \colon E \to \mathbb{R}$ with compact support contained in $U$, such
that $\eta(x) = 1$ for every $x \in K$ and $0 \le \eta(x) \le 1$ for every $x \in E$. -/
theorem exists_contDiff_one_on_of_isCompact_of_isOpen {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ x ∈ K, η x = 1) ∧ ∀ x, η x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, E)) (n := (⊤ : ℕ∞))
      (isOpen_interior.isClosed_compl) hK.isClosed
      (disjoint_compl_left_iff_subset.2 hKL)
  have hsupp : Function.support (f : E → ℝ) ⊆ interior L := by
    intro x hx
    by_contra hc
    exact hx (hf0 hc)
  have htsupp : tsupport (f : E → ℝ) ⊆ L :=
    (closure_mono hsupp).trans (hL.isClosed.closure_subset_iff.2 interior_subset)
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff,
    hL.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hLU, fun x hx => hf1 hx, hf01⟩

variable {F : Type*} [NormedAddCommGroup F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $E$ be a normed group with its Borel $\sigma$-algebra, let $\mu$ be a measure on $E$ that is
inner regular with respect to compact sets on the sets of finite measure, let
$\Omega \subseteq E$ be measurable, and let $1 \le p < \infty$. Let $F$ be a normed group, and
let $f \colon E \to F$ lie in $L^p$ of the restriction of $\mu$ to $\Omega$. Then for every
$\varepsilon \in (0, \infty]$ there is a compact set $K \subseteq \Omega$ with
$$\|f \mathbf{1}_{E \setminus K}\|_{L^p(\Omega, \mu)} \le \varepsilon.$$

The mass of $f$ far away is controlled by the tightness of a single $L^p$ function. The mass
near the boundary of $\Omega$ is controlled by the absolute continuity of the $L^p$ norm
together with inner regularity. -/
theorem MeasureTheory.MemLp.exists_isCompact_eLpNorm_indicator_compl_le
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.InnerRegularCompactLTTop]
    {Ω : Set E} (hΩ : MeasurableSet Ω) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {f : E → F} (hf : MemLp f p (μ.restrict Ω)) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧
      eLpNorm (Kᶜ.indicator f) p (μ.restrict Ω) ≤ ε := by
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := by
    simp only [ENNReal.div_pos_iff]
    exact ⟨hε, by norm_num⟩
  obtain ⟨δ, hδ0, hδ⟩ := hf.eLpNorm_indicator_le hp1 hp hε2
  obtain ⟨s, hsm, hsfin, hs⟩ := hf.exists_eLpNorm_indicator_compl_lt hp hε2.ne'
  have hA : MeasurableSet (s ∩ Ω) := hsm.inter hΩ
  have hAfin : μ (s ∩ Ω) ≠ ⊤ := by
    rw [Measure.restrict_apply hsm] at hsfin
    exact hsfin.ne
  obtain ⟨K, hKA, hKc, hKlt⟩ := hA.exists_isCompact_sdiff_lt (μ := μ) hAfin hδ0.ne'
  refine ⟨K, hKc, hKA.trans inter_subset_right, ?_⟩
  have hcongr : Kᶜ.indicator f
      =ᵐ[μ.restrict Ω] (fun x => sᶜ.indicator f x + ((s ∩ Ω) \ K).indicator f x) := by
    filter_upwards [ae_restrict_mem hΩ] with x hxΩ
    by_cases hxK : x ∈ K
    · have hxs : x ∈ s := (hKA hxK).1
      simp [hxK, hxs]
    · by_cases hxs : x ∈ s
      · simp [hxK, hxs, hxΩ]
      · simp [hxK, hxs]
  rw [eLpNorm_congr_ae hcongr]
  refine le_trans (eLpNorm_add_le hp1) ?_
  have h2 : eLpNorm (((s ∩ Ω) \ K).indicator f) p (μ.restrict Ω) ≤ ε / 2 :=
    hδ _ (hA.diff hKc.measurableSet).nullMeasurableSet
      (le_trans (Measure.restrict_apply_le _ _) hKlt.le)
  exact le_trans (add_le_add hs.le h2) (by rw [ENNReal.add_halves])

/-- Let $E$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, let $F$ be a
real normed space, and let $\mu$ be a measure on $E$ that is finite on compact sets and inner
regular with respect to compact sets on the sets of finite measure. Let $\Omega \subseteq E$ be
open, let $1 \le p < \infty$, and let $f \colon E \to F$ lie in $L^p$ of the restriction of
$\mu$ to $\Omega$. Then for every $\varepsilon > 0$ there is a smooth function
$g \colon E \to F$ with compact support contained in $\Omega$ such that
$$\|f - g\|_{L^p(\Omega, \mu)} \le \varepsilon.$$
-/
theorem MeasureTheory.MemLp.exists_contDiff_tsupport_subset
    [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F]
    {μ : Measure E} [μ.InnerRegularCompactLTTop] [IsFiniteMeasureOnCompacts μ]
    {Ω : Set E} (hΩ : IsOpen Ω) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {f : E → F} (hf : MemLp f p (μ.restrict Ω)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ω ∧
      eLpNorm (f - g) p (μ.restrict Ω) ≤ ENNReal.ofReal ε := by
  have hres : IsFiniteMeasureOnCompacts (μ.restrict Ω) :=
    ⟨fun K hK => lt_of_le_of_lt (Measure.restrict_apply_le _ _) hK.measure_lt_top⟩
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨K, hKc, hKΩ, hK⟩ := hf.exists_isCompact_eLpNorm_indicator_compl_le hΩ.measurableSet hp1 hp
    (ε := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.2 hε2).ne'
  have hf₁mem : MemLp (K.indicator f) p (μ.restrict Ω) :=
    hf.indicator hKc.measurableSet.nullMeasurableSet
  obtain ⟨g, hg1, hg2, hg3⟩ := hf₁mem.exist_eLpNorm_sub_le hp hp1 hε2
  obtain ⟨η, hη1, hη2, hη3, hη4, hη5⟩ := exists_contDiff_one_on_of_isCompact_of_isOpen hKc hΩ hKΩ
  have hsupp : Function.support (fun x => η x • g x) ⊆ Function.support η := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h
    exact hx (by rw [h, zero_smul])
  refine ⟨fun x => η x • g x, hη2.mono hsupp, hη1.smul hg2, (closure_mono hsupp).trans hη3, ?_⟩
  have hdecomp : f - (fun x => η x • g x)
      = (f - K.indicator f) + (fun x => η x • (K.indicator f x - g x)) := by
    funext x
    by_cases hxK : x ∈ K
    · simp only [Pi.sub_apply, Pi.add_apply, Set.indicator_of_mem hxK, hη4 x hxK, one_smul,
        sub_self, zero_add]
    · simp only [Pi.sub_apply, Pi.add_apply, Set.indicator_of_notMem hxK, smul_sub, smul_zero,
        sub_zero, zero_sub]
      abel
  have hcompl : f - K.indicator f = Kᶜ.indicator f := by
    funext x
    by_cases hxK : x ∈ K <;> simp [hxK]
  have hmeas2 : AEStronglyMeasurable (fun x => η x • (K.indicator f x - g x)) (μ.restrict Ω) :=
    hη1.continuous.aestronglyMeasurable.smul
      (hf₁mem.aestronglyMeasurable.sub hg2.continuous.aestronglyMeasurable)
  have hsmul : eLpNorm (fun x => η x • (K.indicator f x - g x)) p (μ.restrict Ω)
      ≤ eLpNorm (K.indicator f - g) p (μ.restrict Ω) := by
    refine eLpNorm_mono hmeas2 fun x => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη5 x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hη5 x).2
  rw [hdecomp]
  refine le_trans (eLpNorm_add_le hp1) ?_
  rw [hcompl]
  refine le_trans (add_le_add hK (hsmul.trans hg3)) ?_
  rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]

/-- Let $E$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, let $F$ be a
real normed space, and let $\mu$ be a measure on $E$ that is finite on compact sets and inner
regular with respect to compact sets on the sets of finite measure. Let $\Omega \subseteq E$ be
open and let $1 \le p < \infty$. Then the classes in $L^p(\Omega, \mu; F)$ that have a smooth
representative with compact support contained in $\Omega$ are dense in $L^p(\Omega, \mu; F)$.

This is the density form of `MeasureTheory.MemLp.exists_contDiff_tsupport_subset`, in the shape
of Mathlib's `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`. -/
theorem MeasureTheory.Lp.dense_contDiff_tsupport_subset
    [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F]
    {μ : Measure E} [μ.InnerRegularCompactLTTop] [IsFiniteMeasureOnCompacts μ]
    {Ω : Set E} (hΩ : IsOpen Ω) {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense {f : Lp F p (μ.restrict Ω) | ∃ g : E → F, f =ᵐ[μ.restrict Ω] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ω} := by
  have hres : IsFiniteMeasureOnCompacts (μ.restrict Ω) :=
    ⟨fun K hK => lt_of_le_of_lt (Measure.restrict_apply_le _ _) hK.measure_lt_top⟩
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ :=
    (Lp.memLp f).exists_contDiff_tsupport_subset hΩ hp1.out hp hε
  have hg5 : MemLp g p (μ.restrict Ω) := hg2.continuous.memLp_of_hasCompactSupport hg1
  refine ⟨hg5.toLp, ⟨g, hg5.coeFn_toLp, hg1, hg2, hg3⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← ENNReal.le_ofReal_iff_toReal_le ((Lp.memLp f).sub (Lp.memLp hg5.toLp)).eLpNorm_ne_top hε.le]
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) hg4
  filter_upwards [hg5.coeFn_toLp] with x hx
  simp [hx]
