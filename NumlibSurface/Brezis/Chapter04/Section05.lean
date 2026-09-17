import Numlib.MeasureTheory.Function.LpSpace.KolmogorovRiesz
import Numlib.Topology.ContinuousMap.ArzelaAscoli
import NumlibSurface.Brezis.Chapter04.Section04

/-!
# Brezis §4.5: criterion for strong compactness in `L^p`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §4.5: the Ascoli–Arzelà theorem (4.25), the
Kolmogorov–M. Riesz–Fréchet theorem (4.26) with its corollaries 4.27–4.28, Lemma 4.3 and
Remarks 12–13, on `ℝ^N = EuclideanSpace ℝ (Fin N)` with Lebesgue measure and real values. The
backbone is `Numlib/Topology/ContinuousMap/ArzelaAscoli` and
`Numlib/MeasureTheory/Function/LpSpace/KolmogorovRiesz` (over any finite-dimensional real normed
space with a Haar measure), of which the nodes here are instances. The translation
`τ_h f (x) = f (x + h)` is written on the coerced function, `fun x => f (x + h)`, and the book's
uniform continuity (22) is stated with a real `ε` as `‖τ_h f - f‖_p < ε` in `[0, ∞]`; the
restriction `F|_Ω` is the backbone's `Lp.restrictCLM ℝ ℝ p volume Ω`.

## Main results

* `theorem_4_25` — Ascoli–Arzelà.
* `theorem_4_26` — Kolmogorov–M. Riesz–Fréchet: a bounded family with uniformly continuous
  translates has compact closure after restriction to any set of finite measure.
* `corollary_4_27` — with tightness, compact closure in `L^p(ℝ^N)` itself; `remark_4_13` — the
  converse, a complete characterization of the relatively compact subsets of `L^p(ℝ^N)`.
* `corollary_4_28`, `lemma_4_3` — the family `G ⋆ B` for `G ∈ L^1` and bounded `B ⊆ L^p`, and the
  continuity of translation in `L^q`.
* `remark_4_12` — the hypotheses of Theorem 4.26 do not give compact closure in `L^p(ℝ^N)`.
-/

open Filter MeasureTheory Metric Topology
open scoped ENNReal

namespace Brezis.Chapter04

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **Theorem 4.25 (Ascoli–Arzelà).** Let `K` be a compact metric space and `H ⊆ C(K)` bounded
and uniformly equicontinuous: for every `ε > 0` there is `δ > 0` with `|f x₁ - f x₂| < ε` for
all `f ∈ H` whenever `d(x₁, x₂) < δ`. Then the closure of `H` in `C(K)` is compact. -/
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

/-- The book's hypothesis (22), with a real `ε`, gives the backbone's form with `ε ∈ [0, ∞]`. -/
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

/-- **Theorem 4.26 (Kolmogorov–M. Riesz–Fréchet).** Let `F` be a bounded set in `L^p(ℝ^N)`,
`1 ≤ p < ∞`, such that `‖τ_h f - f‖_p → 0` as `|h| → 0` uniformly in `f ∈ F` (22). Then the
closure of `F|_Ω` in `L^p(Ω)` is compact for every `Ω ⊆ ℝ^N` of finite measure (the book asks
`Ω` measurable; it is not needed). -/
theorem theorem_4_26 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {F : Set (Lp ℝ p (volume : Measure 𝔼))}
    (hF : Bornology.IsBounded F)
    (hτ : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : 𝔼, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε)
    {Ω : Set 𝔼} (hΩ : volume Ω < ∞) :
    IsCompact (closure (Lp.restrictCLM ℝ ℝ p volume Ω '' F)) :=
  Lp.isCompact_closure_image_restrictCLM_of_uniform_translate hp hF (uniform_translate_of_real hτ)
    hΩ.ne

/-- **Corollary 4.27.** Let `F` be a bounded set in `L^p(ℝ^N)`, `1 ≤ p < ∞`, satisfying (22) and
the tightness condition (27): for every `ε > 0` there is a bounded measurable `Ω ⊆ ℝ^N` with
`‖f‖_{L^p(ℝ^N ∖ Ω)} < ε` for all `f ∈ F`. Then `F` has compact closure in `L^p(ℝ^N)`. -/
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

/-- **Lemma 4.3.** For `G ∈ L^q(ℝ^N)`, `1 ≤ q < ∞`, `‖τ_h G - G‖_q → 0` as `h → 0`. -/
theorem lemma_4_3 {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞) {G : 𝔼 → ℝ} (hG : MemLp G q volume) :
    Tendsto (fun h : 𝔼 => eLpNorm (fun x => G (x + h) - G x) q volume) (𝓝 0) (𝓝 0) := by
  have h1 : Tendsto (fun h : 𝔼 => -h) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔼))).neg
  refine ((hG.tendsto_eLpNorm_sub_translate Fact.out hq).comp h1).congr fun h => ?_
  simp only [Function.comp_apply, sub_neg_eq_add]

/-- **Corollary 4.28.** Let `G ∈ L^1(ℝ^N)` and `B ⊆ L^p(ℝ^N)` bounded, `1 ≤ p < ∞`; then the
family `F = G ⋆ B` has compact closure in `L^p(Ω)` after restriction to any `Ω` of finite
measure. The convolution with `G` is the backbone's bounded operator `Lp.convolutionCLM`, whose
values are a.e. the convolutions `G ⋆ u` (`Lp.coeFn_convolutionCLM`). -/
theorem corollary_4_28 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {G : 𝔼 → ℝ}
    (hG : Integrable G volume) {B : Set (Lp ℝ p (volume : Measure 𝔼))} (hB : Bornology.IsBounded B)
    {Ω : Set 𝔼} (hΩ : volume Ω < ∞) :
    IsCompact (closure (Lp.restrictCLM ℝ ℝ p volume Ω '' (Lp.convolutionCLM ℝ p hG '' B))) :=
  Lp.isCompact_closure_image_restrictCLM_convolutionCLM hp hG hB hΩ.ne

/-! ### Remark 12: the hypotheses of Theorem 4.26 do not give compactness in `L^p(ℝ^N)` -/

/-- The translation `x ↦ x + h` preserves `eLpNorm` on `ℝ`. -/
theorem eLpNorm_comp_add_right_real {f : ℝ → ℝ} {p : ℝ≥0∞} (hf : AEStronglyMeasurable f volume)
    (h : ℝ) : eLpNorm (fun x => f (x + h)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right volume h)

/-- **Remark 12 (and Exercise 4.33).** The hypotheses of Theorem 4.26 do not imply that `F`
itself has compact closure in `L^p(ℝ^N)`: on `ℝ`, the translates `φ(· + n)`, `n ∈ ℕ`, of the
indicator function `φ` of `[0, 1)` form a bounded family satisfying (22) — their translates are
uniformly continuous in `L^p` because translation is an isometry of `L^p` and `φ` satisfies
Lemma 4.3 — whose closure is not compact, the translates being pairwise at distance at least
`1`. -/
theorem remark_4_12 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ F : Set (Lp ℝ p (volume : Measure ℝ)), Bornology.IsBounded F ∧
      (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : ℝ, ‖h‖ < δ →
        eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε) ∧
      ¬ IsCompact (closure F) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set φ : ℝ → ℝ := (Set.Ico (0 : ℝ) 1).indicator fun _ => 1 with hφ
  have hφp : MemLp φ p volume :=
    memLp_indicator_const p measurableSet_Ico 1 (Or.inr measure_Ico_lt_top.ne)
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

/-- The translation `x ↦ x + h` preserves `eLpNorm` on `ℝ^N`. -/
theorem eLpNorm_comp_add_right {f : 𝔼 → ℝ} {p : ℝ≥0∞} (hf : AEStronglyMeasurable f volume)
    (h : 𝔼) : eLpNorm (fun x => f (x + h)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right volume h)

/-- **Exercise 4.34, the uniform continuity of translation**: a relatively compact `F ⊆ L^p(ℝ^N)`,
`1 ≤ p < ∞`, satisfies (22). Each of the finitely many centres of an `ε`-net satisfies
Lemma 4.3, and translation is an isometry of `L^p`. -/
theorem uniform_translate_of_isCompact_closure {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {F : Set (Lp ℝ p (volume : Measure 𝔼))} (hF : IsCompact (closure F)) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ F, ∀ h : 𝔼, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p volume < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨t, ht, htF⟩ := Metric.totallyBounded_iff.1 hF.totallyBounded (ε / 4) (by positivity)
  -- Lemma 4.3 for the finitely many centres
  have hev : ∀ᶠ h : 𝔼 in 𝓝 0, ∀ g ∈ t,
      eLpNorm (fun x => g (x + h) - g x) p volume ≤ ENNReal.ofReal (ε / 4) := by
    rw [Filter.eventually_all_finite ht]
    intro g _
    exact ENNReal.tendsto_nhds_zero.1 (lemma_4_3 hp (Lp.memLp g)) _
      (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun f hf h hh => ?_⟩
  obtain ⟨g, hgt, hfg⟩ := Set.mem_iUnion₂.1 (htF (subset_closure hf))
  rw [Metric.mem_ball, Lp.dist_def] at hfg
  have hne : eLpNorm (⇑f - ⇑g) p volume ≠ ∞ := by
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub f g)]
    exact (Lp.memLp (f - g)).eLpNorm_ne_top
  have hfg' : eLpNorm (⇑f - ⇑g) p volume < ENNReal.ofReal (ε / 4) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hne).2 hfg
  have hg := hδε (by simpa [dist_zero_right] using hh) g hgt
  have hsplit : (fun x => f (x + h) - f x) =
      (fun x => (⇑f - ⇑g) (x + h)) + (fun x => g (x + h) - g x) - (⇑f - ⇑g) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  calc eLpNorm (fun x => f (x + h) - f x) p volume
      ≤ eLpNorm ((fun x => (⇑f - ⇑g) (x + h)) + fun x => g (x + h) - g x) p volume +
          eLpNorm (⇑f - ⇑g) p volume := by
        rw [hsplit]
        exact eLpNorm_sub_le Fact.out
    _ ≤ eLpNorm (fun x => (⇑f - ⇑g) (x + h)) p volume +
          eLpNorm (fun x => g (x + h) - g x) p volume + eLpNorm (⇑f - ⇑g) p volume := by
        gcongr
        exact eLpNorm_add_le Fact.out
    _ = eLpNorm (⇑f - ⇑g) p volume + eLpNorm (fun x => g (x + h) - g x) p volume +
          eLpNorm (⇑f - ⇑g) p volume := by
        rw [eLpNorm_comp_add_right ((Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g))]
    _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add (ENNReal.add_lt_add_of_lt_of_le
          (hg.trans_lt ENNReal.ofReal_lt_top).ne hfg' hg) hfg'
    _ < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, hε⟩

/-- **Exercise 4.34, tightness**: a relatively compact `F ⊆ L^p(ℝ^N)`, `1 ≤ p < ∞`, satisfies
(27): the finitely many centres of an `ε`-net are each concentrated on a compact set, and the
union of these sets works for all of `F`. -/
theorem tight_of_isCompact_closure {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {F : Set (Lp ℝ p (volume : Measure 𝔼))} (hF : IsCompact (closure F)) :
    ∀ ε > (0 : ℝ), ∃ Ω : Set 𝔼, Bornology.IsBounded Ω ∧ MeasurableSet Ω ∧
      ∀ f ∈ F, eLpNorm (Ωᶜ.indicator f) p volume < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨t, ht, htF⟩ := Metric.totallyBounded_iff.1 hF.totallyBounded (ε / 3) (by positivity)
  -- each centre is concentrated on a compact set
  have hK : ∀ g : Lp ℝ p (volume : Measure 𝔼), ∃ K : Set 𝔼, IsCompact K ∧
      eLpNorm (Kᶜ.indicator g) p volume ≤ ENNReal.ofReal (ε / 3) := fun g => by
    have hg : MemLp g p ((volume : Measure 𝔼).restrict Set.univ) := by
      rw [Measure.restrict_univ]; exact Lp.memLp g
    obtain ⟨K, hK, -, hKg⟩ := hg.exists_isCompact_eLpNorm_indicator_compl_le MeasurableSet.univ
      Fact.out hp (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < ε / 3)).ne'
    rw [Measure.restrict_univ] at hKg
    exact ⟨K, hK, hKg⟩
  choose K hKc hKg using hK
  refine ⟨⋃ g ∈ t, K g, (Bornology.isBounded_biUnion ht).2 fun g _ => (hKc g).isBounded,
    ht.measurableSet_biUnion fun g _ => (hKc g).measurableSet, fun f hf => ?_⟩
  obtain ⟨g, hgt, hfg⟩ := Set.mem_iUnion₂.1 (htF (subset_closure hf))
  rw [Metric.mem_ball, Lp.dist_def] at hfg
  have hne : eLpNorm (⇑f - ⇑g) p volume ≠ ∞ := by
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub f g)]
    exact (Lp.memLp (f - g)).eLpNorm_ne_top
  have hfg' : eLpNorm (⇑f - ⇑g) p volume < ENNReal.ofReal (ε / 3) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hne).2 hfg
  set Ω : Set 𝔼 := ⋃ g ∈ t, K g with hΩ
  have hΩm : MeasurableSet Ω := ht.measurableSet_biUnion fun g _ => (hKc g).measurableSet
  have hsplit : Ωᶜ.indicator ⇑f = Ωᶜ.indicator (⇑f - ⇑g) + Ωᶜ.indicator ⇑g := by
    rw [← Set.indicator_add', sub_add_cancel]
  have hsub : Ωᶜ ⊆ (K g)ᶜ := Set.compl_subset_compl.2 (Set.subset_biUnion_of_mem hgt)
  calc eLpNorm (Ωᶜ.indicator ⇑f) p volume
      ≤ eLpNorm (Ωᶜ.indicator (⇑f - ⇑g)) p volume + eLpNorm (Ωᶜ.indicator ⇑g) p volume := by
        rw [hsplit]
        exact eLpNorm_add_le Fact.out
    _ ≤ eLpNorm (⇑f - ⇑g) p volume + eLpNorm ((K g)ᶜ.indicator ⇑g) p volume := by
        gcongr
        · exact eLpNorm_indicator_le _ hΩm.compl
        · rw [show Ωᶜ.indicator ⇑g = Ωᶜ.indicator ((K g)ᶜ.indicator ⇑g) by
            rw [Set.indicator_indicator, Set.inter_eq_left.2 hsub]]
          exact eLpNorm_indicator_le _ hΩm.compl
    _ < ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
        ENNReal.add_lt_add_of_lt_of_le ((hKg g).trans_lt ENNReal.ofReal_lt_top).ne hfg' (hKg g)
    _ < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, hε⟩

/-- **Remark 13.** The converse of Corollary 4.27 holds (Exercise 4.34), so a set `F ⊆ L^p(ℝ^N)`,
`1 ≤ p < ∞`, has compact closure if and only if it is bounded, satisfies (22) and satisfies
(27): a complete characterization of the relatively compact subsets of `L^p(ℝ^N)`. -/
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
