/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.SmoothApprox`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Smooth functions supported in an open set are dense in `Lᵖ` of that set

Mathlib's `MeasureTheory.Lp.dense_hasCompactSupport_contDiff` says that the smooth compactly
supported functions on a finite-dimensional real normed space `E` are dense in `Lᵖ(μ)`, for
`1 ≤ p < ∞`. Nothing there restricts the *support*: an approximant to a function of `Lᵖ(Ω)`, for
`Ω ⊆ E` open, may well spill out of `Ω`. This file removes that spill:
`MeasureTheory.Lp.dense_contDiff_tsupport_subset` produces approximants whose support is a compact
subset of `Ω`, which is the density of `C₀^∞(Ω)` in `Lᵖ(Ω)`.

## Main statements

* `exists_contDiff_one_on_of_isCompact_of_isOpen` — the smooth Urysohn function of a compact set
  inside an open one: smooth, valued in `[0, 1]`, equal to `1` on the compact set, and with compact
  support inside the open one.
* `MeasureTheory.MemLp.exists_isCompact_eLpNorm_indicator_compl_le` — an `Lᵖ(Ω)` function is, up to
  a small `Lᵖ` error, supported in a compact subset of `Ω`.
* `MeasureTheory.MemLp.exists_contDiff_tsupport_subset` and
  `MeasureTheory.Lp.dense_contDiff_tsupport_subset` — the approximation and its `Dense` form.

## Implementation notes

The two ingredients are exactly the two ways an `Lᵖ` function can fail to be compactly supported
inside `Ω`: mass far away, and mass near the boundary. Mathlib has a lemma for each —
`MeasureTheory.MemLp.exists_eLpNorm_indicator_compl_lt` gives a set of finite measure carrying all
but `ε` of the function, and `MeasureTheory.MemLp.eLpNorm_indicator_le` is the absolute continuity
of the `Lᵖ` norm — and inner regularity turns the first set into a compact subset of `Ω`. Once the
function is supported in a compact `K ⊆ Ω`, a smooth approximant `g` of it is multiplied by a
smooth cut-off `η` that is `1` on `K` and supported in `Ω`: since `η` also fixes the localized
function, the error only shrinks, `η (f₁ - g)` being pointwise no larger than `f₁ - g`.

The cut-off comes from the manifold partition-of-unity API,
`exists_contMDiffMap_zero_one_of_isClosed`, read back through `contMDiff_iff_contDiff`.
-/

open MeasureTheory Set Topology

open scoped ContDiff ENNReal Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A smooth Urysohn function for a compact set inside an open set**: smooth, valued in `[0, 1]`,
equal to `1` on `K`, and with compact support contained in `U`. -/
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
/-- **An `Lᵖ` function on a set `Ω` is, up to a small `Lᵖ` error, supported in a compact subset of
`Ω`.** The mass far away is cut by the tightness of a single `Lᵖ` function, the mass near the
boundary by the absolute continuity of the `Lᵖ` norm together with inner regularity. -/
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
  refine le_trans (eLpNorm_add_le (hf.1.indicator hsm.compl)
    (hf.1.indicator (hA.diff hKc.measurableSet)) hp1) ?_
  have h2 : eLpNorm (((s ∩ Ω) \ K).indicator f) p (μ.restrict Ω) ≤ ε / 2 :=
    hδ _ (hA.diff hKc.measurableSet) (le_trans (Measure.restrict_apply_le _ _) hKlt.le)
  exact le_trans (add_le_add hs.le h2) (by rw [ENNReal.add_halves])

/-- **Smooth functions compactly supported inside an open set `Ω` approximate every `Lᵖ(Ω)`
function**, for `1 ≤ p < ∞`. -/
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
  have hf₁mem : MemLp (K.indicator f) p (μ.restrict Ω) := hf.indicator hKc.measurableSet
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
    hη1.continuous.aestronglyMeasurable.smul (hf₁mem.1.sub hg2.continuous.aestronglyMeasurable)
  have hsmul : eLpNorm (fun x => η x • (K.indicator f x - g x)) p (μ.restrict Ω)
      ≤ eLpNorm (K.indicator f - g) p (μ.restrict Ω) := by
    refine eLpNorm_mono fun x => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη5 x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hη5 x).2
  rw [hdecomp]
  refine le_trans (eLpNorm_add_le (hf.1.sub hf₁mem.1) hmeas2 hp1) ?_
  rw [hcompl]
  refine le_trans (add_le_add hK (hsmul.trans hg3)) ?_
  rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]

/-- **Smooth functions compactly supported inside an open set `Ω` are dense in `Lᵖ(Ω)`**, for
`1 ≤ p < ∞`: the `Dense` form of
`MeasureTheory.MemLp.exists_contDiff_tsupport_subset`, matching Mathlib's
`MeasureTheory.Lp.dense_hasCompactSupport_contDiff`. -/
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
