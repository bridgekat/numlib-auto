import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Numlib.Analysis.Convolution.Lp
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.MeasureTheory.Function.EssSupport
import NumlibSurface.Brezis.Chapter04.Section03

/-!
# Brezis §4.4: convolution and regularization

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §4.4, on `ℝ^N = EuclideanSpace ℝ (Fin N)` with
Lebesgue measure. The book's convolution `(f ⋆ g)(x) = ∫ f(x - y) g(y) dy` is Mathlib's
`f ⋆[mul ℝ ℝ, volume] g`, `(f ⋆ g)(x) = ∫ f(t) g(x - t) dt`, after the substitution `y ↦ x - y`
(`MeasureTheory.convolution_eq_swap`). Mathlib's `Mathlib/Analysis/Convolution` carries the
pointwise theory (Propositions 4.19–4.20, Corollary 4.24); the `L^p` theory is the backbone
`Numlib/Analysis/Convolution/Lp` (Theorem 4.15, Proposition 4.16, Theorem 4.22, Theorem 4.33),
the essential support is `Numlib/MeasureTheory/Function/EssSupport` (Proposition 4.17, Remark 9,
Proposition 4.18, Remark 10), and Corollary 4.23 is `Numlib/Analysis/Normed/Lp/SmoothApprox`.
The book's `L^p_loc(Ω)` and the sequences of mollifiers are the definitions `MemLpLoc` and
`IsMollifierSeq`, named by content.

## Main results

* `theorem_4_15` — Young's inequality `‖f ⋆ g‖_p ≤ ‖f‖_1 ‖g‖_p`, with the a.e. existence of the
  integral; `theorem_4_33` — its general form `‖f ⋆ g‖_r ≤ ‖f‖_p ‖g‖_q`.
* `proposition_4_16` — `∫ (f ⋆ g) h = ∫ g (f̌ ⋆ h)`.
* `proposition_4_17`, `remark_4_9`, `proposition_4_18`, `remark_4_10` — the support of a
  measurable function and the support of a convolution.
* `MemLpLoc`, `memLpLoc_one_iff_locallyIntegrableOn`, `MemLpLoc.memLpLoc_one` — `L^p_loc(Ω)`.
* `proposition_4_19`, `proposition_4_20` — continuity and differentiability of `f ⋆ g` for
  `f ∈ C_c`, resp. `C_c^k`, and `g ∈ L^1_loc`.
* `IsMollifierSeq`, `isMollifierSeq_contDiffBump`, `proposition_4_21`, `theorem_4_22` —
  mollifiers and the convergence `ρₙ ⋆ f → f`, uniformly on compact sets for continuous `f` and
  in `L^p` for `f ∈ L^p`, `p < ∞`.
* `corollary_4_23`, `corollary_4_24` — density of `C_c^∞(Ω)` in `L^p(Ω)`, and the fundamental
  lemma `∫ u f = 0` for all `f ∈ C_c^∞(Ω)` implies `u = 0` a.e.
-/

open Filter MeasureTheory Metric Topology
open scoped ContDiff Convolution Pointwise

namespace Brezis.Chapter04

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-! ### Young's inequality and the adjoint identity -/

/-- The bilinear map `mul ℝ ℝ` is `lsmul ℝ ℝ`: the two spellings of the real convolution. -/
theorem lsmul_eq_mul_real : ContinuousLinearMap.lsmul ℝ ℝ = ContinuousLinearMap.mul ℝ ℝ :=
  ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => by simp

/-- The operator norm of the multiplication of `ℝ` is at most `1`, in `ENNReal`. -/
theorem enorm_mul_real_le_one : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- **Theorem 4.15 (Young).** For `f ∈ L^1(ℝ^N)` and `g ∈ L^p(ℝ^N)`, `1 ≤ p ≤ ∞`: for a.e. `x`
the function `y ↦ f (x - y) g y` is integrable, so that `(f ⋆ g)(x) = ∫ f (x - y) g y dy` is
defined; and `f ⋆ g ∈ L^p` with `‖f ⋆ g‖_p ≤ ‖f‖_1 ‖g‖_p`. -/
theorem theorem_4_15 {p : ENNReal} [Fact (1 ≤ p)] {f g : 𝔼 → ℝ} (hf : MemLp f 1 volume)
    (hg : MemLp g p volume) :
    (∀ᵐ x ∂(volume : Measure 𝔼), Integrable (fun y => f (x - y) * g y) volume) ∧
    MemLp (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) p volume ∧
    eLpNorm (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) p volume ≤
      eLpNorm f 1 volume * eLpNorm g p volume := by
  refine ⟨?_, hf.convolution (L := ContinuousLinearMap.mul ℝ ℝ) Fact.out hg, ?_⟩
  · filter_upwards [hf.ae_convolutionExistsAt (L := ContinuousLinearMap.mul ℝ ℝ) Fact.out hg]
      with x hx
    exact convolutionExistsAt_flip.2 hx
  · refine (eLpNorm_convolution_le (L := ContinuousLinearMap.mul ℝ ℝ) Fact.out
      hf.aestronglyMeasurable hg.aestronglyMeasurable).trans ?_
    rw [mul_assoc]
    exact mul_le_of_le_one_left bot_le enorm_mul_real_le_one

/-- **Proposition 4.16.** For `f ∈ L^1`, `g ∈ L^p` and `h ∈ L^{p'}` on `ℝ^N`,
`∫ (f ⋆ g) h = ∫ g (f̌ ⋆ h)`, where `f̌ x = f (-x)`. -/
theorem proposition_4_16 {p q : ENNReal} [p.HolderConjugate q] {f g h : 𝔼 → ℝ}
    (hf : MemLp f 1 volume) (hg : MemLp g p volume) (hh : MemLp h q volume) :
    ∫ x, (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x * h x =
      ∫ y, g y * ((f ∘ Neg.neg) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] h) y :=
  integral_convolution_mul hf hg hh

/-! ### Support and convolution -/

/-- **Proposition 4.17 (and the definition of the support).** For any `f : ℝ^N → ℝ`, let `ω` be
the union of all open sets on which `f = 0` a.e.; then `f = 0` a.e. on `ω`, and `supp f` is by
definition the complement of `ω`. The backbone's `MeasureTheory.essSupport volume f` is this
`supp f`: its complement is `ω` (first clause), and `f = 0` a.e. off it (second clause). -/
theorem proposition_4_17 (f : 𝔼 → ℝ) :
    (essSupport (volume : Measure 𝔼) f)ᶜ =
      ⋃₀ {U : Set 𝔼 | IsOpen U ∧ ∀ᵐ x ∂(volume : Measure 𝔼), x ∈ U → f x = 0} ∧
    ∀ᵐ x ∂(volume : Measure 𝔼), x ∉ essSupport volume f → f x = 0 := by
  refine ⟨?_, ae_eq_zero_of_notMem_essSupport⟩
  rw [essSupport, Measure.compl_support_eq_sUnion]
  congr 1
  ext U
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun hU => ?_
  rw [Measure.restrict_apply hU.measurableSet, measure_eq_zero_iff_ae_notMem]
  refine eventually_congr (Eventually.of_forall fun x => ?_)
  simp only [Set.mem_inter_iff, Function.mem_support, not_and, not_not]

/-- **Remark 9.** (a) If `f₁ = f₂` a.e. then `supp f₁ = supp f₂`, so `supp f` is well defined
for `f ∈ L^p`; (b) for a continuous `f`, `supp f` is the usual support, the closure of
`{f ≠ 0}`. -/
theorem remark_4_9 :
    (∀ f₁ f₂ : 𝔼 → ℝ, f₁ =ᵐ[(volume : Measure 𝔼)] f₂ →
      essSupport (volume : Measure 𝔼) f₁ = essSupport volume f₂) ∧
    ∀ f : 𝔼 → ℝ, Continuous f → essSupport (volume : Measure 𝔼) f = tsupport f :=
  ⟨fun _ _ h => essSupport_congr_ae h, fun _ hf => essSupport_eq_tsupport hf⟩

/-- **Proposition 4.18.** For `f ∈ L^1(ℝ^N)` and `g ∈ L^p(ℝ^N)`,
`supp (f ⋆ g) ⊆ closure (supp f + supp g)`. (The backbone's
`MeasureTheory.essSupport_convolution_subset` needs no integrability at all.) -/
theorem proposition_4_18 (f g : 𝔼 → ℝ) :
    essSupport (volume : Measure 𝔼) (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) ⊆
      closure (essSupport volume f + essSupport volume g) :=
  essSupport_convolution_subset _

/-- **Remark 10.** If `f` and `g` both have compact support then so does `f ⋆ g`. (The book's
second sentence, that this may fail if only one of them has compact support, has no example in
the text and is not formalized.) -/
theorem remark_4_10 {f g : 𝔼 → ℝ} (hf : IsCompact (essSupport (volume : Measure 𝔼) f))
    (hg : IsCompact (essSupport (volume : Measure 𝔼) g)) :
    IsCompact (essSupport (volume : Measure 𝔼) (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g)) :=
  (hf.add hg).closure.of_isClosed_subset isClosed_essSupport (proposition_4_18 f g)

/-! ### `L^p_loc` -/

/-- **The definition of `L^p_loc(Ω)`.** For `Ω ⊆ ℝ^N` open and `1 ≤ p ≤ ∞`, `f : Ω → ℝ`
belongs to `L^p_loc(Ω)` if `f χ_K ∈ L^p(Ω)` for every compact `K ⊆ Ω`. -/
def MemLpLoc (f : 𝔼 → ℝ) (p : ENNReal) (Ω : Set 𝔼) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → MemLp (K.indicator f) p (volume.restrict Ω)

/-- `L^1_loc(Ω)` is Mathlib's `LocallyIntegrableOn f Ω volume`, for open `Ω`. -/
theorem memLpLoc_one_iff_locallyIntegrableOn {f : 𝔼 → ℝ} {Ω : Set 𝔼} (hΩ : IsOpen Ω) :
    MemLpLoc f 1 Ω ↔ LocallyIntegrableOn f Ω volume := by
  rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
  refine forall_congr' fun K => forall_congr' fun hKΩ => forall_congr' fun hK => ?_
  rw [memLp_one_iff_integrable, integrable_indicator_iff hK.measurableSet, IntegrableOn,
    Measure.restrict_restrict hK.measurableSet, Set.inter_eq_left.2 hKΩ]
  rfl

/-- "Note that if `f ∈ L^p_loc(Ω)` then `f ∈ L^1_loc(Ω)`", for `1 ≤ p`: on the compact `K`
the measure is finite and `L^p ⊆ L^1`. -/
theorem MemLpLoc.memLpLoc_one {f : 𝔼 → ℝ} {p : ENNReal} [Fact (1 ≤ p)] {Ω : Set 𝔼}
    (hf : MemLpLoc f p Ω) : MemLpLoc f 1 Ω := by
  intro K hKΩ hK
  have h : MemLp f p ((volume.restrict Ω).restrict K) := by
    rw [memLp_iff, ← eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet]
    exact hf K hKΩ hK
  have : IsFiniteMeasure ((volume.restrict Ω).restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (Measure.le_iff'.1 Measure.restrict_le_self K).trans_lt hK.measure_lt_top⟩
  rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet]
  exact (h.mono_exponent Fact.out).eLpNorm_lt_top

/-- **Proposition 4.19.** For `f ∈ C_c(ℝ^N)` and `g ∈ L^1_loc(ℝ^N)`, `(f ⋆ g)(x)` is well
defined for every `x`, and `f ⋆ g` is continuous. -/
theorem proposition_4_19 {f g : 𝔼 → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : MemLpLoc g 1 Set.univ) :
    ConvolutionExists f g (ContinuousLinearMap.mul ℝ ℝ) volume ∧
      Continuous (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) := by
  have hg' : LocallyIntegrable g volume :=
    locallyIntegrableOn_univ.1 ((memLpLoc_one_iff_locallyIntegrableOn isOpen_univ).1 hg)
  exact ⟨hfs.convolutionExists_left _ hf hg', hfs.continuous_convolution_left _ hf hg'⟩

/-- Differentiating a convolution moves the derivative onto the `C^1` compactly supported
factor: `∇ (f ⋆ g) = (∇ f) ⋆ g`. Local helper — the `C^1` form of the backbone's
`MeasureTheory.LocallyIntegrable.fderiv_convolution_left_apply`, which asks for a smooth `f`;
it belongs beside it in `Numlib/Analysis/Convolution/Lp.lean`. -/
theorem fderiv_convolution_left_apply_of_contDiff_one {f g : 𝔼 → ℝ} (hg : LocallyIntegrable g)
    (hfs : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (x v : 𝔼) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x v =
      ((fun t => fderiv ℝ f t v) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x := by
  rw [(hfs.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hf hg x).fderiv]
  have hex : ConvolutionExistsAt (fderiv ℝ f) g x ((ContinuousLinearMap.mul ℝ ℝ).precompL 𝔼)
      volume :=
    HasCompactSupport.convolutionExists_left _ (hfs.fderiv ℝ) (hf.continuous_fderiv one_ne_zero)
      hg x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex, convolution_def]
  rfl

/-- **Proposition 4.20.** For `f ∈ C_c^k(ℝ^N)`, `k ≥ 1`, and `g ∈ L^1_loc(ℝ^N)`, `f ⋆ g ∈ C^k`
and `∇ (f ⋆ g) = (∇ f) ⋆ g`; in particular for `f ∈ C_c^∞`, `f ⋆ g ∈ C^∞` and
`D^α (f ⋆ g) = (D^α f) ⋆ g` for every `α` — stated for the iterated derivative of any order
along any tuple of directions, of which `D^α` along the coordinate directions is the special
case. The book states the `D^α` formula for `|α| ≤ k` and `f ∈ C_c^k`; the backbone's
`MeasureTheory.LocallyIntegrable.iteratedFDeriv_convolution_left_apply` carries it for smooth
`f` only, and this node follows it (the `C^k` case is recorded as a request). -/
theorem proposition_4_20 {k : ℕ∞} (hk : 1 ≤ k) {f g : 𝔼 → ℝ} (hf : ContDiff ℝ k f)
    (hfs : HasCompactSupport f) (hg : MemLpLoc g 1 Set.univ) :
    ContDiff ℝ k (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) ∧
    (∀ x v : 𝔼, fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x v =
      ((fun t => fderiv ℝ f t v) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x) ∧
    (ContDiff ℝ ∞ f → ∀ (n : ℕ) (x : 𝔼) (y : Fin n → 𝔼),
      iteratedFDeriv ℝ n (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x y =
        ((fun z => iteratedFDeriv ℝ n f z y) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x) := by
  have hg' : LocallyIntegrable g volume :=
    locallyIntegrableOn_univ.1 ((memLpLoc_one_iff_locallyIntegrableOn isOpen_univ).1 hg)
  refine ⟨hfs.contDiff_convolution_left _ hf hg', fun x v =>
    fderiv_convolution_left_apply_of_contDiff_one hg' hfs (hf.of_le (by exact_mod_cast hk)) x v,
    fun hf' n x y => hg'.iteratedFDeriv_convolution_left_apply n hfs hf' x y⟩

/-! ### Mollifiers -/

/-- **The definition of a sequence of mollifiers.** `(ρₙ)_{n ≥ 1}` is a sequence of mollifiers
when `ρₙ ∈ C_c^∞(ℝ^N)`, `supp ρₙ ⊆ closedBall 0 (1 / n)`, `∫ ρₙ = 1` and `ρₙ ≥ 0` for every
`n ≥ 1`. -/
def IsMollifierSeq (ρ : ℕ → 𝔼 → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) ∧
    tsupport (ρ n) ⊆ closedBall 0 (1 / n) ∧ ∫ x, ρ n x = 1 ∧ ∀ x, 0 ≤ ρ n x

/-- "It is easy to generate a sequence of mollifiers": the normalized bump functions of
Mathlib's `ContDiffBump` with outer radius at most `1 / n` form a sequence of mollifiers (the
book's `ρ(x) = exp (1 / (|x|² - 1))` is the bump Mathlib builds in inner product spaces). -/
theorem isMollifierSeq_contDiffBump (φ : ℕ → ContDiffBump (0 : 𝔼))
    (hφ : ∀ n : ℕ, 1 ≤ n → (φ n).rOut ≤ 1 / n) :
    IsMollifierSeq fun n => (φ n).normed volume := fun n hn =>
  ⟨(φ n).contDiff_normed, (φ n).hasCompactSupport_normed,
    by rw [(φ n).tsupport_normed_eq]; exact closedBall_subset_closedBall (hφ n hn),
    (φ n).integral_normed, (φ n).nonneg_normed⟩

/-- The supports of a sequence of mollifiers shrink to `0`: `Tendsto (support (ρ n)) atTop
(𝓝 0).smallSets`, the form of the hypothesis in Mathlib's `convolution_tendsto_right` and the
backbone's `tendsto_eLpNorm_convolution_sub`. -/
theorem IsMollifierSeq.tendsto_support {ρ : ℕ → 𝔼 → ℝ} (hρ : IsMollifierSeq ρ) :
    Tendsto (fun n => Function.support (ρ n)) atTop (𝓝 (0 : 𝔼)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro t ht
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
  refine eventually_atTop.2 ⟨max (n₀ + 1) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnn₀ : (1 : ℝ) / n < ε := by
    refine lt_of_le_of_lt ?_ hn₀
    have : (n₀ + 1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
    exact one_div_le_one_div_of_le (by positivity) this
  refine (subset_tsupport _).trans ((hρ n hn1).2.2.1.trans ?_)
  exact (closedBall_subset_ball hnn₀).trans hεt

/-- **Proposition 4.21.** For a sequence of mollifiers `(ρₙ)` and `f ∈ C(ℝ^N)`, `ρₙ ⋆ f → f`
uniformly on compact sets (Mathlib's `convolution_tendsto_right` at every point). -/
theorem proposition_4_21 {ρ : ℕ → 𝔼 → ℝ} (hρ : IsMollifierSeq ρ) {f : 𝔼 → ℝ}
    (hf : Continuous f) :
    TendstoLocallyUniformly (fun n => ρ n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) f atTop := by
  rw [← lsmul_eq_mul_real, tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have h1 : Tendsto (fun y : ℕ × 𝔼 => f y.2) (atTop ×ˢ 𝓝 x) (𝓝 (f x)) :=
    hf.continuousAt.tendsto.comp tendsto_snd
  have h2 : Tendsto (fun y : ℕ × 𝔼 => (ρ y.1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (f x)) := by
    refine convolution_tendsto_right (g := fun _ => f) (φ := fun y : ℕ × 𝔼 => ρ y.1)
      (k := fun y => y.2) ?_ ?_ ?_ ?_ ?_ tendsto_snd
    · exact ((eventually_ge_atTop 1).mono fun n hn => (hρ n hn).2.2.2.2).prod_inl (𝓝 x)
    · exact ((eventually_ge_atTop 1).mono fun n hn => (hρ n hn).2.2.2.1).prod_inl (𝓝 x)
    · exact hρ.tendsto_support.comp tendsto_fst
    · exact Eventually.of_forall fun _ => hf.aestronglyMeasurable
    · exact hf.continuousAt.tendsto.comp tendsto_snd
  exact (h1.prodMk_nhds h2).mono_right (nhds_le_uniformity _)

/-- **Theorem 4.22.** For a sequence of mollifiers `(ρₙ)`, `1 ≤ p < ∞` and `f ∈ L^p(ℝ^N)`,
`ρₙ ⋆ f → f` in `L^p`. The backbone's `MeasureTheory.tendsto_eLpNorm_convolution_sub` (by the
continuity of translation, not by the book's density argument). -/
theorem theorem_4_22 {ρ : ℕ → 𝔼 → ℝ} (hρ : IsMollifierSeq ρ) {p : ENNReal} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {f : 𝔼 → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun n => eLpNorm (ρ n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f - f) p volume) atTop
      (𝓝 0) := by
  rw [← lsmul_eq_mul_real]
  refine tendsto_eLpNorm_convolution_sub ?_ ?_ ?_ hρ.tendsto_support Fact.out hp hf
  · exact (eventually_ge_atTop 1).mono fun n hn => (hρ n hn).2.2.2.2
  · exact (eventually_ge_atTop 1).mono fun n hn =>
      (hρ n hn).1.continuous.integrable_of_hasCompactSupport (hρ n hn).2.1
  · exact (eventually_ge_atTop 1).mono fun n hn => (hρ n hn).2.2.2.1

/-- **Corollary 4.23.** For `Ω ⊆ ℝ^N` open and `1 ≤ p < ∞`, `C_c^∞(Ω)` is dense in `L^p(Ω)`:
the classes of smooth functions with compact support in `Ω` form a dense subset of
`L^p(Ω) = Lp ℝ p (volume.restrict Ω)`. -/
theorem corollary_4_23 {Ω : Set 𝔼} (hΩ : IsOpen Ω) {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense {g : Lp ℝ p (volume.restrict Ω) | ∃ φ : 𝔼 → ℝ, ⇑g =ᵐ[volume.restrict Ω] φ ∧
      HasCompactSupport φ ∧ ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ Ω} :=
  Lp.dense_contDiff_tsupport_subset hΩ hp

/-- **Corollary 4.24.** For `Ω ⊆ ℝ^N` open and `u ∈ L^1_loc(Ω)` with `∫ u f = 0` for every
`f ∈ C_c^∞(Ω)`, `u = 0` a.e. on `Ω` (Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem corollary_4_24 {Ω : Set 𝔼} (hΩ : IsOpen Ω) {u : 𝔼 → ℝ} (hu : MemLpLoc u 1 Ω)
    (h : ∀ f : 𝔼 → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ω →
      ∫ x, u x * f x = 0) :
    ∀ᵐ x ∂(volume : Measure 𝔼), x ∈ Ω → u x = 0 :=
  hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((memLpLoc_one_iff_locallyIntegrableOn hΩ).1 hu) fun f hf hfs hfΩ => by
      simpa only [smul_eq_mul, mul_comm] using h f hf hfs hfΩ

/-- **Theorem 4.33 (Young, general form; Comments on chapter 4).** For `f ∈ L^p(ℝ^N)` and
`g ∈ L^q(ℝ^N)`, `1 ≤ p, q ≤ ∞`, with `1 / r = 1 / p + 1 / q - 1 ≥ 0` (spelled
`1 / p + 1 / q = 1 + 1 / r` in `[0, ∞]`), `f ⋆ g ∈ L^r` and `‖f ⋆ g‖_r ≤ ‖f‖_p ‖g‖_q`. -/
theorem theorem_4_33 {p q r : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpqr : 1 / p + 1 / q = 1 + 1 / r) {f g : 𝔼 → ℝ} (hf : MemLp f p volume)
    (hg : MemLp g q volume) :
    MemLp (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) r volume ∧
    eLpNorm (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
  have h : eLpNorm (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
    refine (eLpNorm_convolution_le_of_inv_add_inv (L := ContinuousLinearMap.mul ℝ ℝ) Fact.out
      Fact.out hpqr hf.aestronglyMeasurable hg.aestronglyMeasurable).trans ?_
    rw [mul_assoc]
    exact mul_le_of_le_one_left bot_le enorm_mul_real_le_one
  exact ⟨memLp_iff.2 (h.trans_lt (ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top)), h⟩

end Brezis.Chapter04
