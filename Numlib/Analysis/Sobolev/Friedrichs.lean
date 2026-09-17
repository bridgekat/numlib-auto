/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Mollification.lean` and `Numlib/Analysis/Sobolev/Density.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Cutoff

/-!
# Approximation in `W^{1,p}(Ω)` on an arbitrary open set, and the characterizations of `W^{1,p}`

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.1: what
surrounds Theorem 9.2 (Friedrichs) — the convergence of approximate identities in `L^p`, the
local approximation with an `L^∞` bound preserved, and the first characterization of `W^{1,p}`
(Proposition 9.3, (i) ⇒ (ii)).

What `Numlib/Analysis/Sobolev/Density.lean` already gives: the whole-space clause of Theorem 9.2 is
`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm` at order `1`, and the local
approximation on one relatively compact open `ω ⋐ Ω` is
`MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`; both are proved there. The nodes of this module
that are not yet written — Theorem 9.2 with a single sequence for all `ω ⋐ Ω`, Lemma 9.1 for
`ρ ∈ L^1`, Remark 1, the remaining implications of Proposition 9.3 and Remark 7 — are recorded in
`plans/Numlib/Analysis/Sobolev/Friedrichs.toml`.

## Main results

* `MeasureTheory.tendsto_eLpNorm_convolution_sub_of_tendsto_support`: **approximate identities
  converge in `L^p`**, for nonnegative integrable kernels of integral one whose supports shrink to
  the origin — the general form of `ContDiffBump.tendsto_eLpNorm_convolution_sub`, which the
  one-sided mollifiers of the proof of Proposition 9.18 need;
* `HasWeakFDerivOn.abs_integral_smul_fderiv_le`: **Proposition 9.3, (i) ⇒ (ii)** with the book's
  constant `C = ‖∇u‖_{L^p(Ω)}`;
* `HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm_of_ae_norm_le`: **the local
  approximation with an `L^∞` bound preserved**, the sentence "checking the proof of Theorem 9.2
  we see that `‖u_n‖_∞ ≤ ‖u‖_∞`" of the proof of Proposition 9.4, which the endpoint product rule
  `L^p × L^∞` needs.

## References

[brezis2011functional], §9.1: Theorem 9.2, Proposition 9.3 and the proof of Proposition 9.4;
§9.4, proof of Proposition 9.18.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Topology

noncomputable section

/-! ### Approximate identities converge in `L^p` -/

section ApproximateIdentity

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ℝ≥0∞} {f : G → F}

/-- **Approximate identities converge in `L^p`**: if the kernels `ρ n` are nonnegative,
integrable, of integral `1`, supported in balls of radii `r n → 0`, and the convolutions
`ρ n ⋆ f` exist, then `ρ n ⋆ f → f` in `L^p` for `f ∈ L^p`, `1 ≤ p < ∞`. The bound
`MeasureTheory.eLpNorm_convolution_sub_rpow_le` is the `ρ n`-average of the translation errors
`‖f(· − t) − f‖_p^p` over `‖t‖ ≤ r n`, which is small by the continuity of translation
`MeasureTheory.MemLp.tendsto_eLpNorm_sub_translate`. `ContDiffBump.tendsto_eLpNorm_convolution_sub`
is the special case of normalized bumps; the general form is what the one-sided mollifiers
`ρ_n(x) = n^N ρ(nx)`, `supp ρ ⊆ {1/2 < x_N < 1}`, of [brezis2011functional] §9.4, proof of
Proposition 9.18 (iii) ⇒ (i), need. -/
theorem MeasureTheory.tendsto_eLpNorm_convolution_sub_of_tendsto_support {ι : Type*}
    {l : Filter ι} {ρ : ι → G → ℝ} {r : ι → ℝ} (hρ₀ : ∀ i t, 0 ≤ ρ i t)
    (hρ : ∀ i, Integrable (ρ i) μ) (hρ₁ : ∀ i, ∫ t, ρ i t ∂μ = 1)
    (hsupp : ∀ i, Function.support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0))
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : MemLp f p μ) :
    Tendsto (fun i ↦ eLpNorm (ρ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f - f) p μ) l (𝓝 0) := by
  have hq1 : (1 : ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hq0 : (0 : ℝ) < p.toReal := lt_of_lt_of_le one_pos hq1
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hnhds : {t : G | eLpNorm (fun x ↦ f (x - t) - f x) p μ < ε} ∈ 𝓝 (0 : G) :=
    hf.tendsto_eLpNorm_sub_translate hp hp' (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hnhds
  filter_upwards [hr (Iio_mem_nhds hδ)] with i hi
  have hkey : eLpNorm (ρ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f - f) p μ ^ p.toReal
      ≤ ε ^ p.toReal := by
    refine (eLpNorm_convolution_sub_rpow_le hp hp' hf (hρ₀ i) (hρ i) (hρ₁ i)).trans ?_
    have hpt : ∀ t : G, ‖ρ i t‖ₑ * eLpNorm (fun x ↦ f (x - t) - f x) p μ ^ p.toReal
        ≤ ‖ρ i t‖ₑ * ε ^ p.toReal := by
      intro t
      by_cases ht : t ∈ ball (0 : G) δ
      · gcongr
        exact (hδsub ht).le
      · have h0 : ρ i t = 0 := by
          rw [← Function.notMem_support]
          intro hmem
          exact ht (closedBall_subset_ball (show r i < δ from hi) (hsupp i hmem))
        simp [h0]
    calc ∫⁻ t, ‖ρ i t‖ₑ * eLpNorm (fun x ↦ f (x - t) - f x) p μ ^ p.toReal ∂μ
        ≤ ∫⁻ t, ‖ρ i t‖ₑ * ε ^ p.toReal ∂μ := lintegral_mono hpt
      _ = ε ^ p.toReal := by
          rw [lintegral_mul_const'' _ (hρ i).aestronglyMeasurable.enorm,
            lintegral_enorm_eq_one (hρ₀ i) (hρ i) (hρ₁ i), one_mul]
  exact (ENNReal.rpow_le_rpow_iff hq0).1 hkey

end ApproximateIdentity

/-! ### Proposition 9.3, (i) ⇒ (ii) -/

section Characterization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {u : E → F} {w : E → E →L[ℝ] F} {p q : ℝ≥0∞}

/-- **Proposition 9.3, (i) ⇒ (ii)**, with the book's constant: if `w` is the weak derivative of
`u` on `Ω` and `p, q` are Hölder conjugate, then for every test function `φ` on `Ω` and every
direction `y`, `‖∫_Ω (∂_y φ) u‖ ≤ ‖y‖ ‖w‖_{L^p(Ω)} ‖φ‖_{L^q(Ω)}`: the defining identity turns the
integral into `∫_Ω φ (w y)`, and Hölder's inequality bounds it. This is the implication
[brezis2011functional] Proposition 9.3 calls obvious, with `C = ‖∇u‖_{L^p(Ω)}`, and it holds for
`p = 1` as well (Remark 6). -/
theorem HasWeakFDerivOn.abs_integral_smul_fderiv_le (h : HasWeakFDerivOn u w Ω μ)
    [ENNReal.HolderConjugate p q] (φ : 𝓓(Ω, ℝ)) (y : E) :
    ‖∫ x in (Ω : Set E), fderiv ℝ φ x y • u x ∂μ‖ₑ
      ≤ ‖y‖ₑ * eLpNorm w p (μ.restrict (Ω : Set E)) * eLpNorm φ q (μ.restrict (Ω : Set E)) := by
  rw [h.integral_smul_eq φ y, enorm_neg]
  have hw : AEStronglyMeasurable w (μ.restrict (Ω : Set E)) :=
    h.locallyIntegrableOn_weakDeriv.aestronglyMeasurable
  have hwy : AEStronglyMeasurable (fun x ↦ w x y) (μ.restrict (Ω : Set E)) :=
    (ContinuousLinearMap.apply ℝ F y).continuous.comp_aestronglyMeasurable hw
  calc ‖∫ x in (Ω : Set E), φ x • w x y ∂μ‖ₑ
      ≤ eLpNorm φ q (μ.restrict (Ω : Set E)) * eLpNorm (fun x ↦ w x y) p (μ.restrict (Ω : Set E)) :=
        enorm_integral_smul_le_eLpNorm_mul_eLpNorm
    _ ≤ eLpNorm φ q (μ.restrict (Ω : Set E)) * (‖y‖ₑ * eLpNorm w p (μ.restrict (Ω : Set E))) := by
        gcongr
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p hwy (Eventually.of_forall fun x ↦ ?_)
        rw [mul_comm]
        exact (w x).le_opENorm y
    _ = ‖y‖ₑ * eLpNorm w p (μ.restrict (Ω : Set E)) * eLpNorm φ q (μ.restrict (Ω : Set E)) := by
        ring

end Characterization

section BoundedApprox

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {n : ℕ} {y : Fin n → E}
  {f w : E → F} {p : ℝ≥0∞}

omit [CompleteSpace F] in
/-- **Mollification by a normalized bump does not increase an `L^∞` bound**: if `‖h‖ ≤ M`
almost everywhere, then `‖(φ.normed μ ⋆ h) x‖ ≤ M` at every point, `φ.normed μ` being a
nonnegative kernel of integral one. -/
theorem ContDiffBump.norm_convolution_normed_le_of_ae_norm_le (φ : ContDiffBump (0 : E))
    {h : E → F} {M : ℝ} (hM : ∀ᵐ z ∂μ, ‖h z‖ ≤ M) (x : E) :
    ‖(φ.normed μ ⋆[lsmul ℝ ℝ, μ] h) x‖ ≤ M := by
  rw [convolution_def]
  have hbound : ∀ᵐ t ∂μ, ‖lsmul ℝ ℝ (φ.normed μ t) (h (x - t))‖ ≤ φ.normed μ t * M := by
    filter_upwards [(measurePreserving_sub_left_of_isAddRightInvariant μ x)
      |>.quasiMeasurePreserving.tendsto_ae.eventually hM] with t ht
    rw [lsmul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left ht (φ.nonneg_normed t)
  refine (norm_integral_le_of_norm_le (φ.integrable_normed.mul_const M) hbound).trans (le_of_eq ?_)
  rw [integral_mul_const, φ.integral_normed, one_mul]

/-- **The local approximation with an `L^∞` bound preserved**: the local approximation
`HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm` of
`Numlib/Analysis/Sobolev/Mollification.lean` — on an open `V` with compact closure in `Ω`, smooth
`g j` with `g j → f` and `∂^y (g j) → w` in `L^p(V)` — with the additional conclusion
`‖g j x‖ ≤ M` for all `j` and `x` whenever `‖f‖ ≤ M` almost everywhere on `Ω`. The approximants
are mollifications, by nonnegative normalized bumps, of a truncation of `f`, and such a
mollification never exceeds the essential bound of the function
(`ContDiffBump.norm_convolution_normed_le_of_ae_norm_le`). This is the sentence "checking the
proof of Theorem 9.2, we see easily that we have further `‖u_n‖_∞ ≤ ‖u‖_∞`" of
[brezis2011functional] §9.1, proof of Proposition 9.4, in the local form that the endpoint product
rule `L^p × L^∞` needs. -/
theorem HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm_of_ae_norm_le
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) (hf : LocallyMemLpOn f p Ω μ)
    (hw : LocallyMemLpOn w p Ω μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖f x‖ ≤ M) {V : Set E} (hVo : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ (Ω : Set E)) :
    ∃ g : ℕ → E → F, (∀ j, ContDiff ℝ ∞ (g j)) ∧ (∀ j, MemLp (g j) p (μ.restrict V)) ∧
      (∀ j, MemLp (fun x ↦ iteratedFDeriv ℝ n (g j) x y) p (μ.restrict V)) ∧
      (∀ j x, ‖g j x‖ ≤ M) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ g j x - f x) p (μ.restrict V)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ n (g j) x y - w x) p (μ.restrict V))
        atTop (𝓝 0) := by
  obtain ⟨W, -, hWo, hVW, -, hWc, hWΩ, -⟩ := hVc.exists_pos_forall_closedBall_subset Ω.isOpen hVΩ
  obtain ⟨V', ε, hV'o, hVV', hε, -, -, hV'ball⟩ := hVc.exists_pos_forall_closedBall_subset hWo hVW
  set C : Set E := closure W with hCdef
  have hCmeas : MeasurableSet C := hWc.isClosed.measurableSet
  have hWC : W ⊆ interior C := interior_maximal subset_closure hWo
  have hVC : V ⊆ C := (subset_closure.trans hVW).trans subset_closure
  set f' : E → F := C.indicator f with hf'def
  set w' : E → F := C.indicator w with hw'def
  have hf'Lp : MemLp f' p μ :=
    (memLp_indicator_iff_restrict hCmeas).2 (hf.memLp_restrict_of_compact_subset hp' hWΩ hWc)
  have hw'Lp : MemLp w' p μ :=
    (memLp_indicator_iff_restrict hCmeas).2 (hw.memLp_restrict_of_compact_subset hp' hWΩ hWc)
  have hf'loc : LocallyIntegrable f' μ := hf'Lp.locallyIntegrable hp
  have hf'M : ∀ᵐ z ∂μ, ‖f' z‖ ≤ M := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hM] with z hz
    by_cases hzC : z ∈ C
    · rw [hf'def, Set.indicator_of_mem hzC]
      exact hz (hWΩ hzC)
    · rw [hf'def, Set.indicator_of_notMem hzC, norm_zero]
      exact hM0
  have hint : HasWeakIteratedLineDerivOn y f' w' ⟨interior C, isOpen_interior⟩ μ :=
    (h.mono (interior_subset.trans hWΩ)).congr_ae
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) f).symm)
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) w).symm)
  set φ : ℕ → ContDiffBump (0 : E) := fun j ↦
    ⟨ε / (2 * (j + 2)), ε / (j + 2), by positivity, by
      apply div_lt_div_of_pos_left hε (by positivity)
      nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]⟩ with hφdef
  have hrOut : ∀ j, (φ j).rOut = ε / (j + 2) := fun j ↦ rfl
  have hrOutle : ∀ j, (φ j).rOut ≤ ε := fun j ↦ by
    rw [hrOut]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have htend : Tendsto (fun j ↦ (φ j).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set g : ℕ → E → F := fun j ↦ (φ j).normed μ ⋆[lsmul ℝ ℝ, μ] f' with hgdef
  have hball : ∀ j, ∀ x ∈ V, closedBall x (φ j).rOut ⊆ interior C := fun j x hx ↦
    ((closedBall_subset_closedBall (hrOutle j)).trans
      (hV'ball x (hVV' (subset_closure hx)))).trans hWC
  have hderivEq : ∀ j, ∀ x ∈ V, iteratedFDeriv ℝ n (g j) x y
      = ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] w') x := fun j x hx ↦
    hint.iteratedFDeriv_convolution (φ j).contDiff_normed
      (le_of_eq ((φ j).tsupport_normed_eq (μ := μ))) (hball j x hx)
  have hconvLp : ∀ (j : ℕ) (c : E → F), MemLp c p μ →
      MemLp ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] c) p μ := fun j _ hc ↦
    MemLp.convolution hp (memLp_one_iff_integrable.2 (φ j).integrable_normed) hc
  refine ⟨g, fun j ↦ (φ j).hasCompactSupport_normed.contDiff_convolution_left _
    (φ j).contDiff_normed hf'loc, fun j ↦ (hconvLp j f' hf'Lp).restrict V, fun j ↦ ?_,
    fun j x ↦ (φ j).norm_convolution_normed_le_of_ae_norm_le hf'M x, ?_, ?_⟩
  · refine ((hconvLp j w' hw'Lp).restrict V).ae_eq ?_
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    exact (hderivEq j x hx).symm
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ContDiffBump.tendsto_eLpNorm_convolution_sub htend hp hp' hf'Lp)
      (fun _ ↦ zero_le) (fun j ↦ ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    simp [hgdef, hf'def, Set.indicator_of_mem (hVC hx)]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ContDiffBump.tendsto_eLpNorm_convolution_sub htend hp hp' hw'Lp)
      (fun _ ↦ zero_le) (fun j ↦ ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    rw [hderivEq j x hx]
    simp [hw'def, Set.indicator_of_mem (hVC hx)]

end BoundedApprox
