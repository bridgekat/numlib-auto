/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convolution.Lp`, beside `Mathlib.Analysis.Convolution`, whose
pointwise theory of the convolution this continues on the `L^p` side.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# `L^p` estimates for convolutions, and `L^p` convergence of mollification

`Mathlib/Analysis/Convolution.lean` builds the convolution `f ⋆[L, μ] g` and its pointwise theory
-- existence, support, continuity, smoothness, and pointwise or almost-everywhere convergence of
`φ_ε ⋆ f` to `f` -- but it contains no estimate on the *size* of a convolution in `L^p`. This file
supplies that estimate in the case that mollification needs, and the `L^p` convergence of
mollification that follows from it.

The main estimate is the `L^1 ∗ L^p → L^p` case of Young's convolution inequality,
`eLpNorm (f ⋆[L, μ] g) p μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ`, for `1 ≤ p ≤ ∞` and a
right-invariant measure on a measurable additive group. The general form `1/p + 1/q = 1 + 1/r` is
*not* proved here. For the classical statements see for instance E. H. Lieb and M. Loss,
*Analysis*, 2nd edition, American Mathematical Society, 2001, chapter 4, or H. Brezis, *Functional
Analysis, Sobolev Spaces and Partial Differential Equations*, Springer, 2011, chapter 4.

## Main results

* `ENNReal.rpow_lintegral_mul_le`: Jensen's inequality for the convex function `t ↦ t ^ p` against
  a weight, `(∫⁻ a, w a * h a ∂μ) ^ p ≤ (∫⁻ a, w a ∂μ) ^ (p - 1) * ∫⁻ a, w a * h a ^ p ∂μ`.
* `ENNReal.lintegral_rpow_lintegral_mul_le`: the weighted form of Minkowski's integral inequality
  obtained from it by Tonelli's theorem. This is the analytic core of everything below.
* `MeasureTheory.eLpNorm_convolution_le` and `MeasureTheory.MemLp.convolution`: Young's convolution
  inequality in the case `L^1 ∗ L^p → L^p`, and the resulting membership statement.
* `MeasureTheory.eLpNorm_convolution_lsmul_le`: the same inequality with constant `1`, for the
  convolution of a scalar function against a vector-valued one.
* `MeasureTheory.MemLp.tendsto_eLpNorm_sub_translate`: translation is continuous on `L^p`, in the
  form `‖f (· - t) - f‖_p → 0` as `t → 0`.
* `ContDiffBump.tendsto_eLpNorm_convolution_sub`: mollification converges in `L^p`. For
  `f ∈ L^p(μ)` with `p ≠ ∞` and a family of bump functions whose outer radii tend to `0`, the
  mollifications `(φ i).normed μ ⋆ f` tend to `f` in `L^p`.

## Implementation notes

Young's inequality is proved from Jensen's inequality rather than from Minkowski's integral
inequality or from reading `f ⋆ g` as a Bochner integral valued in `L^p`. Writing `w = ‖f ·‖ₑ` and
using the convexity of `t ↦ t ^ p`, Jensen's inequality for the measure `w dμ` bounds
`(∫⁻ w h) ^ p` by `(∫⁻ w) ^ (p - 1) * ∫⁻ w h ^ p`; Tonelli's theorem and the translation
invariance of `μ` then finish the estimate in one step each. The advantage over the other two
routes is that no integrability hypothesis is needed anywhere: the bound `‖∫ ...‖ₑ ≤ ∫⁻ ‖...‖ₑ`
holds unconditionally, because a Bochner integral that does not converge is `0`, so
`MeasureTheory.eLpNorm_convolution_le` asks only for measurability. Jensen's inequality itself is
`ENNReal.lintegral_mul_norm_pow_le`, the two-exponent form of Hölder's inequality, applied to
`w * h = w ^ (1 - 1/p) * (w * h ^ p) ^ (1/p)`.

Minkowski's integral inequality `‖∫ F (·, t) dt‖_p ≤ ∫ ‖F (·, t)‖_p dt` is *not* proved here, and
is not what `ENNReal.lintegral_rpow_lintegral_mul_le` says: the latter carries a weight and pays
for it with a factor `(∫⁻ w) ^ (p - 1)`, which is what makes it provable from Hölder's inequality
alone. Both consumers below normalize the weight to `∫⁻ w = 1`, where the two agree.

`ContDiffBump.tendsto_eLpNorm_convolution_sub` is proved from the weighted Minkowski inequality
and the continuity of translation on `L^p` directly, without the usual detour through the density
of the compactly supported continuous functions in `L^p`: a normalized bump is a probability
density concentrating at `0`, so the weighted inequality turns the `L^p` error of mollification
into an average of the translation errors `‖f (· - t) - f‖_p` over the support of the bump, and
continuity of translation makes those uniformly small. The continuity of translation is in turn
read off Mathlib's continuity of the action of `Gᵈᵃᵃ` on `MeasureTheory.Lp`,
`MeasureTheory.Lp.instContinuousVAddDomAddAct`.
-/

open Filter Function MeasureTheory MeasureTheory.Measure Metric Topology
open ContinuousLinearMap DomAddAct
open scoped Convolution ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- Almost every slice of an almost-everywhere measurable function on a product is
almost-everywhere measurable. This is the `AEMeasurable` companion of
`MeasureTheory.Integrable.prod_right_ae`. -/
theorem AEMeasurable.prod_right_ae {γ : Type*} [MeasurableSpace γ] [SFinite ν] {f : α × β → γ}
    (hf : AEMeasurable f (μ.prod ν)) : ∀ᵐ x ∂μ, AEMeasurable (fun y => f (x, y)) ν := by
  obtain ⟨g, hg, hfg⟩ := hf
  exact (ae_ae_of_ae_prod hfg).mono fun x hx => ⟨fun y => g (x, y), by fun_prop, hx⟩

namespace ENNReal

/-- **Jensen's inequality** for the convex function `t ↦ t ^ p` on `ℝ≥0∞`, `1 ≤ p`, against a
weight `w`: the `p`-th power of the `w`-average of `h` is at most the `w`-average of `h ^ p`, in
the unnormalized form that does not ask `∫⁻ w` to be finite or nonzero.

This is Hölder's inequality applied to `w * h = w ^ (1 - 1/p) * (w * h ^ p) ^ (1/p)`. -/
theorem rpow_lintegral_mul_le {p : ℝ} (hp : 1 ≤ p) {w h : α → ℝ≥0∞}
    (hw : AEMeasurable w μ) (hh : AEMeasurable h μ) :
    (∫⁻ a, w a * h a ∂μ) ^ p ≤ (∫⁻ a, w a ∂μ) ^ (p - 1) * ∫⁻ a, w a * h a ^ p ∂μ := by
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le one_pos hp
  have hr : (0:ℝ) ≤ 1 / p := by positivity
  have hq : (0:ℝ) ≤ 1 - 1 / p := by
    simp only [sub_nonneg]
    rw [div_le_one hp0]
    exact hp
  have hqr : 1 - 1 / p + 1 / p = 1 := by ring
  have key : ∀ a, w a * h a = w a ^ (1 - 1 / p) * (w a * h a ^ p) ^ (1 / p) := fun a => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne',
      ENNReal.rpow_one, ← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hq hr, hqr, ENNReal.rpow_one]
  have step : ∫⁻ a, w a * h a ∂μ
      ≤ (∫⁻ a, w a ∂μ) ^ (1 - 1 / p) * (∫⁻ a, w a * h a ^ p ∂μ) ^ (1 / p) := by
    simp_rw [key]
    exact ENNReal.lintegral_mul_norm_pow_le hw (hw.mul (hh.pow_const p)) hq hr hqr
  calc (∫⁻ a, w a * h a ∂μ) ^ p
      ≤ ((∫⁻ a, w a ∂μ) ^ (1 - 1 / p) * (∫⁻ a, w a * h a ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow step hp0.le
    _ = (∫⁻ a, w a ∂μ) ^ (p - 1) * ∫⁻ a, w a * h a ^ p ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
        congr 2
        field_simp

/-- A weighted form of **Minkowski's integral inequality**: the `L^p` norm of a weighted average
of the functions `H · t` is controlled by the weighted average of their `L^p` norms, up to the
factor `(∫⁻ w) ^ (p - 1)` that disappears when the weight is a probability density.

Unlike Minkowski's integral inequality proper, which needs a duality argument, this follows from
`ENNReal.rpow_lintegral_mul_le` and Tonelli's theorem. -/
theorem lintegral_rpow_lintegral_mul_le [SFinite μ] [SFinite ν] {p : ℝ} (hp : 1 ≤ p)
    {w : β → ℝ≥0∞} {H : α → β → ℝ≥0∞}
    (hw : AEMeasurable w ν) (hH : AEMeasurable (uncurry H) (μ.prod ν)) :
    ∫⁻ x, (∫⁻ t, w t * H x t ∂ν) ^ p ∂μ
      ≤ (∫⁻ t, w t ∂ν) ^ (p - 1) * ∫⁻ t, w t * ∫⁻ x, H x t ^ p ∂μ ∂ν := by
  have hslice : ∀ᵐ x ∂μ, AEMeasurable (fun t => H x t) ν := hH.prod_right_ae
  have hslice' : ∀ᵐ t ∂ν, AEMeasurable (fun x => H x t) μ := hH.prod_swap.prod_right_ae
  have hprod : AEMeasurable (uncurry fun (x : α) (t : β) => w t * H x t ^ p) (μ.prod ν) :=
    hw.comp_snd.mul (hH.pow_const p)
  calc ∫⁻ x, (∫⁻ t, w t * H x t ∂ν) ^ p ∂μ
      ≤ ∫⁻ x, (∫⁻ t, w t ∂ν) ^ (p - 1) * ∫⁻ t, w t * H x t ^ p ∂ν ∂μ :=
        lintegral_mono_ae (hslice.mono fun x hx => rpow_lintegral_mul_le hp hw hx)
    _ = (∫⁻ t, w t ∂ν) ^ (p - 1) * ∫⁻ x, ∫⁻ t, w t * H x t ^ p ∂ν ∂μ :=
        lintegral_const_mul'' _ hprod.lintegral_prod_right
    _ = (∫⁻ t, w t ∂ν) ^ (p - 1) * ∫⁻ t, ∫⁻ x, w t * H x t ^ p ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hprod]
    _ = (∫⁻ t, w t ∂ν) ^ (p - 1) * ∫⁻ t, w t * ∫⁻ x, H x t ^ p ∂μ ∂ν := by
        congr 1
        exact lintegral_congr_ae (hslice'.mono fun t ht =>
          lintegral_const_mul'' _ (ht.pow_const p))

end ENNReal

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}

/-- The unprimed companion of `MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm'`. -/
theorem lintegral_rpow_enorm_eq_rpow_eLpNorm (hp₀ : p ≠ 0) (hp : p ≠ ∞) {f : α → F} :
    ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ = eLpNorm f p μ ^ p.toReal := by
  rw [eLpNorm_eq_eLpNorm' hp₀ hp,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp₀ hp)]

/-- The Lebesgue integral of the enorm of a nonnegative probability density is `1`. -/
theorem lintegral_enorm_eq_one {φ : α → ℝ} (hφ₀ : ∀ t, 0 ≤ φ t) (hφ : Integrable φ μ)
    (hφ₁ : ∫ t, φ t ∂μ = 1) : ∫⁻ t, ‖φ t‖ₑ ∂μ = 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hφ]
  simp_rw [Real.norm_of_nonneg (hφ₀ _)]
  rw [hφ₁, ENNReal.ofReal_one]

/-! ### Young's convolution inequality in the case `L¹ ∗ Lᵖ → Lᵖ` -/

section Young

variable {𝕜 G E E' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  [MeasurableSpace G] [AddGroup G] {μ : Measure G}
  {f : G → E} {g : G → E'} {L : E →L[𝕜] E' →L[𝕜] F}

/-- The convolution is pointwise dominated by the convolution of the norms, with no integrability
hypothesis: a Bochner integral that does not converge is `0`. -/
theorem enorm_convolution_le (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun _ => L.le_opENorm₂ _ _)

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [μ.IsAddRightInvariant]

/-- The right-hand factor of a convolution integrand, seen as a function on `G × G`, is
almost-everywhere strongly measurable. -/
theorem AEStronglyMeasurable.comp_fst_sub_snd (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun z : G × G => g (z.1 - z.2)) (μ.prod μ) :=
  (hg.mono_ac (quasiMeasurePreserving_sub_of_right_invariant μ
    μ).absolutelyContinuous).comp_measurable measurable_sub

/-- **Young's convolution inequality** in the case `L¹ ∗ Lᵖ → Lᵖ` with `p ≠ ∞`. -/
theorem eLpNorm_convolution_le_of_ne_top (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) p μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq1 : (1:ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hq0 : (0:ℝ) < p.toReal := lt_of_lt_of_le one_pos hq1
  set w : G → ℝ≥0∞ := fun t => ‖L‖ₑ * ‖f t‖ₑ with hw_def
  have hw : AEMeasurable w μ := hf.enorm.const_mul _
  have hH : AEMeasurable (uncurry fun x t : G => ‖g (x - t)‖ₑ) (μ.prod μ) :=
    (AEStronglyMeasurable.comp_fst_sub_snd hg).enorm
  set C : ℝ≥0∞ := ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ with hC
  have hinv : ∀ t : G, ∫⁻ x, ‖g (x - t)‖ₑ ^ p.toReal ∂μ = C :=
    fun t => lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ ^ p.toReal) t
  have key : ∫⁻ x, ‖(f ⋆[L, μ] g) x‖ₑ ^ p.toReal ∂μ ≤ (∫⁻ t, w t ∂μ) ^ p.toReal * C := by
    calc ∫⁻ x, ‖(f ⋆[L, μ] g) x‖ₑ ^ p.toReal ∂μ
        ≤ ∫⁻ x, (∫⁻ t, w t * ‖g (x - t)‖ₑ ∂μ) ^ p.toReal ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (enorm_convolution_le x) hq0.le
      _ ≤ (∫⁻ t, w t ∂μ) ^ (p.toReal - 1) *
            ∫⁻ t, w t * ∫⁻ x, ‖g (x - t)‖ₑ ^ p.toReal ∂μ ∂μ :=
          ENNReal.lintegral_rpow_lintegral_mul_le hq1 hw hH
      _ = (∫⁻ t, w t ∂μ) ^ (p.toReal - 1) * ((∫⁻ t, w t ∂μ) * C) := by
          simp_rw [hinv]
          rw [lintegral_mul_const'' _ hw]
      _ = (∫⁻ t, w t ∂μ) ^ p.toReal * C := by
          rw [← mul_assoc]
          congr 1
          nth_rewrite 2 [← ENNReal.rpow_one (∫⁻ t, w t ∂μ)]
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one]
          congr 1
          ring
  have hwint : ∫⁻ t, w t ∂μ = ‖L‖ₑ * eLpNorm f 1 μ := by
    rw [hw_def, lintegral_const_mul'' _ hf.enorm, eLpNorm_one_eq_lintegral_enorm]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
  calc (∫⁻ x, ‖(f ⋆[L, μ] g) x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ ((∫⁻ t, w t ∂μ) ^ p.toReal * C) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow key (by positivity)
    _ = (∫⁻ t, w t ∂μ) * C ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
    _ = ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ := by
        rw [hwint, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']

/-- **Young's convolution inequality** in the case `L¹ ∗ L^∞ → L^∞`. -/
theorem eLpNormEssSup_convolution_le (hf : AEStronglyMeasurable f μ) :
    eLpNormEssSup (f ⋆[L, μ] g) μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNormEssSup g μ := by
  rw [eLpNormEssSup]
  refine essSup_le_of_ae_le _ (Eventually.of_forall fun x => ?_)
  refine (enorm_convolution_le x).trans ?_
  have hae : ∀ᵐ t ∂μ, ‖g (x - t)‖ₑ ≤ eLpNormEssSup g μ :=
    (quasiMeasurePreserving_sub_left_of_right_invariant μ x).ae
      (_root_.ae_le_essSup (μ := μ) (f := fun y => ‖g y‖ₑ))
  calc ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ
      ≤ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * eLpNormEssSup g μ ∂μ :=
        lintegral_mono_ae (hae.mono fun t ht => by gcongr)
    _ = ‖L‖ₑ * eLpNorm f 1 μ * eLpNormEssSup g μ := by
        rw [lintegral_mul_const'' _ (hf.enorm.const_mul _), lintegral_const_mul'' _ hf.enorm,
          eLpNorm_one_eq_lintegral_enorm]

/-- **Young's convolution inequality** in the case `L¹ ∗ Lᵖ → Lᵖ`, for every `1 ≤ p ≤ ∞`.

Only measurability is assumed: where the convolution fails to exist it is `0`, and the bound holds
there for free. -/
theorem eLpNorm_convolution_le (hp : 1 ≤ p) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) p μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · simpa [eLpNorm_exponent_top] using eLpNormEssSup_convolution_le (L := L) (g := g) hf
  · exact eLpNorm_convolution_le_of_ne_top hp hp' hf hg

/-- `Lᵖ` is a module over `L¹` under convolution: the convolution of an `L¹` function with an `Lᵖ`
function is in `Lᵖ`. -/
theorem MemLp.convolution (hp : 1 ≤ p) (hf : MemLp f 1 μ) (hg : MemLp g p μ) :
    MemLp (f ⋆[L, μ] g) p μ := by
  refine ⟨(hf.aestronglyMeasurable.convolution_integrand L
    hg.aestronglyMeasurable).integral_prod_right', ?_⟩
  refine lt_of_le_of_lt
    (eLpNorm_convolution_le hp hf.aestronglyMeasurable hg.aestronglyMeasurable) ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp [enorm_lt_top]) hf.eLpNorm_lt_top)
    hg.eLpNorm_lt_top

/-- **Young's convolution inequality** for the convolution of a scalar function against a
vector-valued one, where the constant is `1`. -/
theorem eLpNorm_convolution_lsmul_le {φ : G → ℝ} {h : G → F} (hp : 1 ≤ p)
    (hφ : AEStronglyMeasurable φ μ) (hh : AEStronglyMeasurable h μ) :
    eLpNorm (φ ⋆[lsmul ℝ ℝ, μ] h) p μ ≤ eLpNorm φ 1 μ * eLpNorm h p μ := by
  refine (eLpNorm_convolution_le hp hφ hh).trans ?_
  calc ‖(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)‖ₑ * eLpNorm φ 1 μ * eLpNorm h p μ
      ≤ 1 * eLpNorm φ 1 μ * eLpNorm h p μ := by gcongr; exact opENorm_lsmul_le
    _ = eLpNorm φ 1 μ * eLpNorm h p μ := by rw [one_mul]

end Young

/-! ### Continuity of translation on `Lᵖ` -/

section Translation

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure] {f : G → F}

/-- **Continuity of translation on `Lᵖ`**: for `f ∈ Lᵖ` with `1 ≤ p < ∞`, the `Lᵖ` distance
between `f` and its translate by `t` tends to `0` as `t` tends to `0`.

This is a restatement of the continuity of the action of `Gᵈᵃᵃ` on `MeasureTheory.Lp`,
`MeasureTheory.Lp.instContinuousVAddDomAddAct`. -/
theorem MemLp.tendsto_eLpNorm_sub_translate (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun t : G => eLpNorm (fun x => f (x - t) - f x) p μ) (𝓝 0) (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have : Fact (p ≠ ∞) := ⟨hp'⟩
  have key : ∀ t : G,
      eLpNorm (fun x => f (x - t) - f x) p μ = ‖(mk (-t) +ᵥ hf.toLp f) - hf.toLp f‖ₑ := by
    intro t
    rw [Lp.enorm_def]
    refine (eLpNorm_congr_ae ?_).symm
    have h1 : ((mk (-t) +ᵥ hf.toLp f : Lp F p μ) : G → F) =ᵐ[μ] fun x => f (x - t) := by
      rw [mk_vadd_toLp]
      refine (MemLp.coeFn_toLp _).trans (Eventually.of_forall fun x => ?_)
      simp [neg_add_eq_sub]
    exact (Lp.coeFn_sub _ _).trans (h1.sub hf.coeFn_toLp)
  simp_rw [key]
  have h₁ : Continuous fun t : G => (mk (-t) : Gᵈᵃᵃ) :=
    mkHomeomorph.continuous.comp continuous_neg
  have h₂ : Continuous fun t : G => mk (-t) +ᵥ hf.toLp f :=
    continuous_vadd.comp (h₁.prodMk continuous_const)
  have h₃ : Tendsto (fun t : G => mk (-t) +ᵥ hf.toLp f) (𝓝 0) (𝓝 (hf.toLp f)) :=
    h₂.tendsto' 0 _ (by simp)
  have hcont : Tendsto (fun t : G => (mk (-t) +ᵥ hf.toLp f) - hf.toLp f) (𝓝 0) (𝓝 0) := by
    simpa using h₃.sub (tendsto_const_nhds (x := hf.toLp f))
  simpa [comp_def] using (continuous_enorm.tendsto (0 : Lp F p μ)).comp hcont

end Translation

/-! ### `Lᵖ` convergence of mollification -/

section Mollifier

variable {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure G} {f : G → F} {φ : G → ℝ}

/-- Convolving with a probability density `φ` and subtracting averages the translation errors:
the mollification error at `x` is dominated by the `φ`-average of `‖f (x - t) - f x‖`. -/
theorem enorm_convolution_sub_le (hφ : Integrable φ μ) (hφ₁ : ∫ t, φ t ∂μ = 1)
    (hex : ConvolutionExists φ f (lsmul ℝ ℝ) μ) (x : G) :
    ‖(φ ⋆[lsmul ℝ ℝ, μ] f - f) x‖ₑ ≤ ∫⁻ t, ‖φ t‖ₑ * ‖f (x - t) - f x‖ₑ ∂μ := by
  have hid : (φ ⋆[lsmul ℝ ℝ, μ] f - f) x = ∫ t, φ t • (f (x - t) - f x) ∂μ := by
    have h1 : Integrable (fun t => φ t • f (x - t)) μ := hex x
    have h2 : Integrable (fun t => φ t • f x) μ := hφ.smul_const _
    simp only [smul_sub]
    rw [integral_sub h1 h2, integral_smul_const, hφ₁, one_smul]
    rfl
  rw [hid]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t => ?_)
  rw [enorm_smul]

variable [NormedSpace ℝ G] [FiniteDimensional ℝ G] [BorelSpace G] [μ.IsAddHaarMeasure]

/-- The `Lᵖ` error of mollification by a probability density `φ` is bounded by the `φ`-average of
the `p`-th powers of the translation errors `‖f (· - t) - f‖_p`. -/
theorem eLpNorm_convolution_sub_rpow_le (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : MemLp f p μ)
    (hφ₀ : ∀ t, 0 ≤ φ t) (hφ : Integrable φ μ) (hφ₁ : ∫ t, φ t ∂μ = 1)
    (hex : ConvolutionExists φ f (lsmul ℝ ℝ) μ) :
    eLpNorm (φ ⋆[lsmul ℝ ℝ, μ] f - f) p μ ^ p.toReal
      ≤ ∫⁻ t, ‖φ t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq1 : (1:ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hq0 : (0:ℝ) < p.toReal := lt_of_lt_of_le one_pos hq1
  have hH : AEMeasurable (uncurry fun x t : G => ‖f (x - t) - f x‖ₑ) (μ.prod μ) :=
    ((AEStronglyMeasurable.comp_fst_sub_snd hf.aestronglyMeasurable).sub
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst)).enorm
  rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp']
  calc ∫⁻ x, ‖(φ ⋆[lsmul ℝ ℝ, μ] f - f) x‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, (∫⁻ t, ‖φ t‖ₑ * ‖f (x - t) - f x‖ₑ ∂μ) ^ p.toReal ∂μ :=
        lintegral_mono fun x =>
          ENNReal.rpow_le_rpow (enorm_convolution_sub_le hφ hφ₁ hex x) hq0.le
    _ ≤ (∫⁻ t, ‖φ t‖ₑ ∂μ) ^ (p.toReal - 1) *
          ∫⁻ t, ‖φ t‖ₑ * ∫⁻ x, ‖f (x - t) - f x‖ₑ ^ p.toReal ∂μ ∂μ :=
        ENNReal.lintegral_rpow_lintegral_mul_le hq1 hφ.aestronglyMeasurable.enorm hH
    _ = ∫⁻ t, ‖φ t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal ∂μ := by
        rw [lintegral_enorm_eq_one hφ₀ hφ hφ₁, ENNReal.one_rpow, one_mul]
        exact lintegral_congr fun t => by
          rw [lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp']

/-- **Mollification converges in `Lᵖ`.** If `f ∈ Lᵖ(μ)` with `1 ≤ p < ∞` and the outer radii of a
family of bump functions tend to `0`, then the mollifications `(φ i).normed μ ⋆ f` tend to `f` in
`Lᵖ(μ)`.

This is the `Lᵖ` counterpart of `ContDiffBump.convolution_tendsto_right`, which gives the
pointwise convergence for a continuous `f`. -/
theorem _root_.ContDiffBump.tendsto_eLpNorm_convolution_sub {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : G)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun i => eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f) p μ) l (𝓝 0) := by
  have hq1 : (1:ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hq0 : (0:ℝ) < p.toReal := lt_of_lt_of_le one_pos hq1
  have hloc : LocallyIntegrable f μ := hf.locallyIntegrable hp
  have hex : ∀ i, ConvolutionExists ((φ i).normed μ) f (lsmul ℝ ℝ) μ := fun i =>
    (φ i).hasCompactSupport_normed.convolutionExists_left _ (φ i).continuous_normed hloc
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hnhds : {t : G | eLpNorm (fun x => f (x - t) - f x) p μ < ε} ∈ 𝓝 (0 : G) :=
    hf.tendsto_eLpNorm_sub_translate hp hp' (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hnhds
  filter_upwards [hφ (Iio_mem_nhds hδ)] with i hi
  have hkey : eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f) p μ ^ p.toReal ≤ ε ^ p.toReal := by
    refine (eLpNorm_convolution_sub_rpow_le hp hp' hf (φ i).nonneg_normed
      (φ i).integrable_normed (φ i).integral_normed (hex i)).trans ?_
    have hpt : ∀ t : G, ‖(φ i).normed μ t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal
        ≤ ‖(φ i).normed μ t‖ₑ * ε ^ p.toReal := by
      intro t
      by_cases ht : t ∈ ball (0 : G) δ
      · gcongr
        exact (hδsub ht).le
      · have h0 : (φ i).normed μ t = 0 := by
          rw [← notMem_support, (φ i).support_normed_eq]
          exact fun hmem => ht (ball_subset_ball hi.le hmem)
        simp [h0]
    calc ∫⁻ t, ‖(φ i).normed μ t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal ∂μ
        ≤ ∫⁻ t, ‖(φ i).normed μ t‖ₑ * ε ^ p.toReal ∂μ := lintegral_mono hpt
      _ = ε ^ p.toReal := by
          rw [lintegral_mul_const'' _ (φ i).continuous_normed.aestronglyMeasurable.enorm,
            lintegral_enorm_eq_one (φ i).nonneg_normed (φ i).integrable_normed
              (φ i).integral_normed, one_mul]
  exact (ENNReal.rpow_le_rpow_iff hq0).1 hkey

end Mollifier

end MeasureTheory
