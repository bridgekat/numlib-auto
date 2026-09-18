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
import Numlib.Analysis.Calculus.IteratedFDeriv
import Numlib.MeasureTheory.Function.LpInterpolation

/-!
# `L^p` estimates for convolutions, and `L^p` convergence of mollification

`Mathlib/Analysis/Convolution.lean` builds the convolution `f ⋆[L, μ] g` and its pointwise theory
-- existence, support, continuity, smoothness, and pointwise or almost-everywhere convergence of
`φ_ε ⋆ f` to `f` -- but it contains no estimate on the *size* of a convolution in `L^p`. This file
supplies those estimates, and the `L^p` convergence of mollification that follows from them.

The main estimate is Young's convolution inequality. Its `L^1 ∗ L^p → L^p` case,
`eLpNorm (f ⋆[L, μ] g) p μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ` for `1 ≤ p ≤ ∞`, holds over any
right-invariant measure on a measurable additive group; the general form `1/p + 1/q = 1 + 1/r`
asks for a measure invariant under negation as well, because its proof integrates a reflected
translate of `g`. Minkowski's integral inequality is proved here in both a weighted and an
unweighted form. For the classical statements see for instance E. H. Lieb and M. Loss, *Analysis*,
2nd edition, American Mathematical Society, 2001, chapters 2 and 4, or H. Brezis, *Functional
Analysis, Sobolev Spaces and Partial Differential Equations*, Springer, 2011, chapter 4.

## Main results

* `ENNReal.rpow_lintegral_mul_le`: Jensen's inequality for the convex function `t ↦ t ^ p` against
  a weight, `(∫⁻ a, w a * h a ∂μ) ^ p ≤ (∫⁻ a, w a ∂μ) ^ (p - 1) * ∫⁻ a, w a * h a ^ p ∂μ`.
* `ENNReal.lintegral_rpow_lintegral_mul_le`: the weighted form of Minkowski's integral inequality
  obtained from it by Tonelli's theorem. This is the analytic core of the `L^1 ∗ L^p` estimate.
* `ENNReal.lintegral_rpow_lintegral_le`: Minkowski's integral inequality proper, in the unweighted
  form `‖∫ H (·, t) dt‖_p ≤ ∫ ‖H (·, t)‖_p dt`, for a σ-finite `μ`.
* `MeasureTheory.eLpNorm_convolution_le` and `MeasureTheory.MemLp.convolution`: Young's convolution
  inequality in the case `L^1 ∗ L^p → L^p`, and the resulting membership statement.
* `MeasureTheory.MemLp.ae_convolutionExistsAt`: the convolution of an `L^1` function with an `L^p`
  function exists almost everywhere, for every `1 ≤ p ≤ ∞`.
* `MeasureTheory.Lp.convolutionCLM`: convolution with a fixed integrable kernel as a bounded
  operator on `Lp F p μ`, of norm at most the `L^1` norm of the kernel
  (`MeasureTheory.Lp.norm_convolutionCLM_le`).
* `MeasureTheory.integral_convolution_mul`: the adjoint identity `∫ (f ⋆ g) h = ∫ g (f̌ ⋆ h)` for
  `f ∈ L^1`, `g ∈ L^p`, `h ∈ L^q` with `1/p + 1/q = 1`, where `f̌ x = f (-x)`.
* `MeasureTheory.eLpNorm_convolution_le_of_inv_add_inv`: Young's convolution inequality in its
  general form `1/p + 1/q = 1 + 1/r`, over a measure that is also invariant under negation.
* `MeasureTheory.eLpNorm_convolution_lsmul_le`: the same inequality with constant `1`, for the
  convolution of a scalar function against a vector-valued one.
* `MeasureTheory.MemLp.tendsto_eLpNorm_sub_translate`: translation is continuous on `L^p`, in the
  form `‖f (· - t) - f‖_p → 0` as `t → 0`.
* `MeasureTheory.tendsto_eLpNorm_convolution_sub` and
  `ContDiffBump.tendsto_eLpNorm_convolution_sub`: mollification converges in `L^p`. For
  `f ∈ L^p(μ)` with `p ≠ ∞` and an approximate identity --
  nonnegative probability densities `φ i` whose supports shrink to `0`, for instance normalized
  bump functions whose outer radii tend to `0` -- the mollifications `φ i ⋆ f` tend to `f` in
  `L^p`.
* `MeasureTheory.tendsto_integral_mul_of_tendsto_eLpNorm`,
  `MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm` and
  `MeasureTheory.enorm_integral_smul_le_of_bound`: the estimates that pass to the limit in an
  integral along a sequence converging in `L^p` -- Hölder's inequality in the limit, the comparison
  of `L^1` with `L^p` on a finite measure, and the bound of an integral against a bounded scalar
  factor.
* `MeasureTheory.LocallyIntegrable.fderiv_convolution_left_apply` and
  `MeasureTheory.LocallyIntegrable.iteratedFDeriv_convolution_left_apply`: differentiating a
  convolution, once in a fixed direction (a `C¹` factor suffices) or `n` times along a tuple of
  directions, moves the derivatives onto the compactly supported factor (smooth for the iterated
  form: the induction uses the symmetry of the second derivative); and
  `MeasureTheory.LocallyIntegrableOn.convolutionExistsAt`: a convolution against a compactly
  supported continuous function exists as soon as the other factor is locally integrable on an open
  set containing the closed ball carrying the support.

## Implementation notes

The `L^1 ∗ L^p → L^p` case of Young's inequality is proved from Jensen's inequality rather than
from Minkowski's integral inequality or from reading `f ⋆ g` as a Bochner integral valued in
`L^p`. Writing `w = ‖f ·‖ₑ` and
using the convexity of `t ↦ t ^ p`, Jensen's inequality for the measure `w dμ` bounds
`(∫⁻ w h) ^ p` by `(∫⁻ w) ^ (p - 1) * ∫⁻ w h ^ p`; Tonelli's theorem and the translation
invariance of `μ` then finish the estimate in one step each. The advantage over the other two
routes is that no integrability hypothesis is needed anywhere: the bound `‖∫ ...‖ₑ ≤ ∫⁻ ‖...‖ₑ`
holds unconditionally, because a Bochner integral that does not converge is `0`, so
`MeasureTheory.eLpNorm_convolution_le` asks only for measurability. Jensen's inequality itself is
`ENNReal.lintegral_mul_norm_pow_le`, the two-exponent form of Hölder's inequality, applied to
`w * h = w ^ (1 - 1/p) * (w * h ^ p) ^ (1/p)`.

The two forms of Minkowski's integral inequality proved here are independent.
`ENNReal.lintegral_rpow_lintegral_mul_le` carries a weight and pays for it with a factor
`(∫⁻ w) ^ (p - 1)`, which is what makes it provable from Hölder's inequality alone, and it is all
the mollification estimates below need, since they normalize the weight to `∫⁻ w = 1`. The
unweighted `ENNReal.lintegral_rpow_lintegral_le` is *not* a corollary of it -- taking the weight to
be `1` there costs a factor `ν univ ^ (p - 1)`, vacuous for an infinite `ν` -- and is proved by
duality instead: write `F ^ p = F ^ (p - 1) * F`, apply Tonelli's theorem and Hölder's inequality
with the exponents `p / (p - 1)` and `p`, and divide by `(∫⁻ F ^ p) ^ (1 - 1/p)`. That division
needs the quantity to be finite, which is what `ENNReal.lintegral_rpow_le_of_truncation_le`
arranges, and it is the only reason `μ` is asked to be σ-finite there.

The general form of Young's inequality comes out of the three-exponent Hölder inequality
`ENNReal.lintegral_mul_mul_norm_pow_le` applied to the splitting
`‖f t‖ * ‖g (x - t)‖ = (‖f t‖ ^ p * ‖g (x - t)‖ ^ q) ^ (1/r) * (‖f t‖ ^ p) ^ (1/p - 1/r) *
(‖g (x - t)‖ ^ q) ^ (1/q - 1/r)`, followed by Tonelli's theorem;
`MeasureTheory.lintegral_enorm_convolution_rpow_le` is that argument with the exponents as real
numbers. Only the endpoint `r = ∞` needs a separate treatment, because `p = ∞` and `q = ∞` both
force `r = ∞`. Both the splitting and the endpoint case integrate `t ↦ ‖g (x - t)‖`, so both need
the reflection `t ↦ x - t` to preserve `μ`; that is where `MeasureTheory.Measure.IsNegInvariant`
enters, and it is why the `L^1 ∗ L^p → L^p` case is kept as a separate theorem rather than
specialized from the general one.

`MeasureTheory.tendsto_eLpNorm_convolution_sub` is proved from the weighted Minkowski inequality
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

/-- **Hölder's inequality** for three functions and three nonnegative exponents summing to `1`.
This is the three-function form of `ENNReal.lintegral_mul_norm_pow_le`. -/
theorem lintegral_mul_mul_norm_pow_le {f g h : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    ∫⁻ x, f x ^ a * g x ^ b * h x ^ c ∂μ
      ≤ (∫⁻ x, f x ∂μ) ^ a * (∫⁻ x, g x ∂μ) ^ b * (∫⁻ x, h x ∂μ) ^ c := by
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 3))
    (f := ![f, g, h]) (p := ![a, b, c])
    (fun i _ => by fin_cases i <;> assumption)
    (by simpa [Fin.sum_univ_three] using habc)
    (fun i _ => by fin_cases i <;> assumption)
  simpa [Fin.prod_univ_three] using key

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


/-! ### Minkowski's integral inequality -/

/-- **Truncation for a σ-finite measure.** A bound on `∫⁻ x, G x ^ p ∂μ` that holds for every
measurable `G ≤ F` whose `p`-th moment is finite holds for `F` itself.

Capping the values of `F` at `n` and its support at the `n`-th of the sets exhausting `μ` gives an
increasing sequence of such `G`, converging pointwise to `F`; monotone convergence then finishes.
This is what lets an argument that has to divide by `∫⁻ x, F x ^ p ∂μ`, and therefore needs it
finite, conclude in general. -/
theorem lintegral_rpow_le_of_truncation_le [SigmaFinite μ] {p : ℝ} (hp : 0 < p)
    {F : α → ℝ≥0∞} (hF : Measurable F) {c : ℝ≥0∞}
    (h : ∀ G : α → ℝ≥0∞, Measurable G → (∀ x, G x ≤ F x) → ∫⁻ x, G x ^ p ∂μ ≠ ∞ →
      ∫⁻ x, G x ^ p ∂μ ≤ c) :
    ∫⁻ x, F x ^ p ∂μ ≤ c := by
  set G : ℕ → α → ℝ≥0∞ :=
    fun n => (spanningSets μ n).indicator (fun x => min (F x) n) with hGdef
  have hGmeas : ∀ n, Measurable (G n) := fun n =>
    (hF.min measurable_const).indicator (measurableSet_spanningSets μ n)
  have hGle : ∀ n x, G n x ≤ F x := by
    intro n x
    by_cases hx : x ∈ spanningSets μ n
    · simpa only [hGdef, Set.indicator_of_mem hx] using min_le_left _ _
    · simp [hGdef, Set.indicator_of_notMem hx]
  have hGmono : Monotone G := by
    intro m n hmn x
    by_cases hx : x ∈ spanningSets μ m
    · rw [hGdef]
      simp only [Set.indicator_of_mem hx,
        Set.indicator_of_mem (monotone_spanningSets μ hmn hx)]
      exact min_le_min_left _ (by exact_mod_cast hmn)
    · simp [hGdef, Set.indicator_of_notMem hx]
  have hGsup : ∀ x, ⨆ n, G n x = F x := by
    intro x
    refine le_antisymm (iSup_le fun n => hGle n x) (le_of_forall_lt fun b hb => ?_)
    obtain ⟨n₁, hn₁⟩ := ENNReal.exists_nat_gt hb.ne_top
    obtain ⟨n₀, hn₀⟩ : ∃ n, x ∈ spanningSets μ n :=
      Set.mem_iUnion.1 (by simp [iUnion_spanningSets])
    refine lt_of_lt_of_le ?_ (le_iSup (fun n => G n x) (max n₀ n₁))
    have hx : x ∈ spanningSets μ (max n₀ n₁) := monotone_spanningSets μ (le_max_left _ _) hn₀
    simp only [hGdef, Set.indicator_of_mem hx]
    exact lt_min hb (lt_of_lt_of_le hn₁ (by exact_mod_cast le_max_right n₀ n₁))
  have hfin : ∀ n, ∫⁻ x, G n x ^ p ∂μ ≠ ∞ := by
    intro n
    have hbound : ∀ x, G n x ^ p
        ≤ (spanningSets μ n).indicator (fun _ => (n : ℝ≥0∞) ^ p) x := by
      intro x
      by_cases hx : x ∈ spanningSets μ n
      · simp only [hGdef, Set.indicator_of_mem hx]
        exact ENNReal.rpow_le_rpow (min_le_right _ _) hp.le
      · simp [hGdef, Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
    rw [lintegral_indicator_const (measurableSet_spanningSets μ n)]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le (by simp))
      (measure_spanningSets_lt_top μ n).ne
  calc ∫⁻ x, F x ^ p ∂μ = ∫⁻ x, ⨆ n, G n x ^ p ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [← hGsup x]
        exact (ENNReal.orderIsoRpow p hp).map_iSup _
    _ = ⨆ n, ∫⁻ x, G n x ^ p ∂μ :=
        lintegral_iSup (fun n => (hGmeas n).pow_const p)
          (fun m n hmn x => ENNReal.rpow_le_rpow (hGmono hmn x) hp.le)
    _ ≤ c := iSup_le fun n => h (G n) (hGmeas n) (hGle n) (hfin n)

/-- The duality step in Minkowski's integral inequality: a minorant `G` of `x ↦ ∫⁻ t, H x t ∂ν`
whose `p`-th moment is finite already has that moment bounded by the right-hand side of the
inequality.

Writing `G ^ p = G ^ (p - 1) * G`, bounding the last factor by the integral it lies below,
exchanging the order of integration and applying Hölder's inequality with the exponents
`p / (p - 1)` and `p` bounds `∫⁻ G ^ p` by `(∫⁻ G ^ p) ^ (1 - 1/p)` times the right-hand side; the
finiteness of `∫⁻ G ^ p` is what lets that factor be cancelled. -/
theorem lintegral_rpow_le_of_le_lintegral [SFinite μ] [SFinite ν] {p : ℝ} (hp : 1 < p)
    {H : α → β → ℝ≥0∞} (hH : Measurable (uncurry H)) {G : α → ℝ≥0∞} (hG : Measurable G)
    (hGF : ∀ x, G x ≤ ∫⁻ t, H x t ∂ν) (hfin : ∫⁻ x, G x ^ p ∂μ ≠ ∞) :
    ∫⁻ x, G x ^ p ∂μ ≤ (∫⁻ t, (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν) ^ p := by
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hp1 : (0:ℝ) < p - 1 := by linarith
  set q := p / (p - 1) with hqdef
  have hqpos : (0:ℝ) < q := by rw [hqdef]; positivity
  have hqp : Real.HolderConjugate q p :=
    ⟨by rw [hqdef]; field_simp; ring, hqpos, hp0⟩
  have hconj : 1 / q + 1 / p = 1 := by simpa using hqp.one_div_add_one_div
  have hmulq : (p - 1) * q = p := by rw [hqdef]; field_simp
  have hsplit : ∀ x : ℝ≥0∞, x ^ (p - 1) * x = x ^ p := by
    intro x
    have h1 : x ^ (p - 1) * x ^ (1:ℝ) = x ^ (p - 1 + 1) :=
      (ENNReal.rpow_add_of_nonneg _ _ hp1.le zero_le_one).symm
    simpa using h1
  have hmeasR : Measurable fun t => (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) :=
    ((hH.pow_const p).lintegral_prod_left').pow_const _
  set B := ∫⁻ x, G x ^ p ∂μ with hB
  set R := ∫⁻ t, (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν with hR
  have hstep : B ≤ B ^ (1 / q) * R := by
    calc B = ∫⁻ x, G x ^ (p - 1) * G x ∂μ :=
          lintegral_congr fun x => (hsplit (G x)).symm
      _ ≤ ∫⁻ x, G x ^ (p - 1) * ∫⁻ t, H x t ∂ν ∂μ :=
          lintegral_mono fun x => by gcongr; exact hGF x
      _ = ∫⁻ x, ∫⁻ t, G x ^ (p - 1) * H x t ∂ν ∂μ :=
          lintegral_congr fun x =>
            (lintegral_const_mul _ (hH.comp measurable_prodMk_left)).symm
      _ = ∫⁻ t, ∫⁻ x, G x ^ (p - 1) * H x t ∂μ ∂ν :=
          lintegral_lintegral_swap
            (((hG.pow_const _).comp measurable_fst).mul hH).aemeasurable
      _ ≤ ∫⁻ t, B ^ (1 / q) * (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν := by
          refine lintegral_mono fun t => ?_
          have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hqp
            (hG.pow_const (p - 1)).aemeasurable
            (hH.comp (measurable_prodMk_right (y := t))).aemeasurable
          simp only [Pi.mul_apply] at hhold
          refine hhold.trans_eq ?_
          congr 2
          exact lintegral_congr fun x => by rw [← ENNReal.rpow_mul, hmulq]
      _ = B ^ (1 / q) * R := lintegral_const_mul _ hmeasR
  rcases eq_or_ne B 0 with hB0 | hB0
  · simp [hB0]
  have hpos : (0:ℝ≥0∞) < B ^ (1 / q) := ENNReal.rpow_pos (pos_iff_ne_zero.2 hB0) hfin
  have hnetop : B ^ (1 / q) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin
  have hkey : B ^ (1 / p) ≤ R := by
    refine (ENNReal.mul_le_mul_iff_right hpos.ne' hnetop).1 (le_trans (le_of_eq ?_) hstep)
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hconj,
      ENNReal.rpow_one]
  calc B = (B ^ (1 / p)) ^ p := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    _ ≤ R ^ p := ENNReal.rpow_le_rpow hkey hp0.le

/-- **Minkowski's integral inequality** for a measurable integrand. See
`ENNReal.lintegral_rpow_lintegral_le` for the version that asks for measurability only almost
everywhere. -/
theorem lintegral_rpow_lintegral_le_of_measurable [SigmaFinite μ] [SFinite ν] {p : ℝ} (hp : 1 ≤ p)
    {H : α → β → ℝ≥0∞} (hH : Measurable (uncurry H)) :
    (∫⁻ x, (∫⁻ t, H x t ∂ν) ^ p ∂μ) ^ (1 / p)
      ≤ ∫⁻ t, (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp only [ENNReal.rpow_one, div_self (one_ne_zero' ℝ)]
    exact le_of_eq (lintegral_lintegral_swap hH.aemeasurable)
  · have hp0 : (0:ℝ) < p := lt_trans one_pos hp1
    have hF : Measurable fun x => ∫⁻ t, H x t ∂ν := hH.lintegral_prod_right'
    have hmain : ∫⁻ x, (∫⁻ t, H x t ∂ν) ^ p ∂μ
        ≤ (∫⁻ t, (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν) ^ p :=
      lintegral_rpow_le_of_truncation_le hp0 hF fun G hG hGF hGfin =>
        lintegral_rpow_le_of_le_lintegral hp1 hH hG hGF hGfin
    calc (∫⁻ x, (∫⁻ t, H x t ∂ν) ^ p ∂μ) ^ (1 / p)
        ≤ ((∫⁻ t, (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν) ^ p) ^ (1 / p) :=
          ENNReal.rpow_le_rpow hmain (by positivity)
      _ = ∫⁻ t, (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- **Minkowski's integral inequality**, `1 ≤ p`: the `L^p` norm of an integral is at most the
integral of the `L^p` norms.

Unlike `ENNReal.lintegral_rpow_lintegral_mul_le` this carries no weight and no compensating factor,
and it is not a corollary of that inequality: putting the weight `1` there costs a factor
`ν univ ^ (p - 1)`, which is vacuous when `ν` is infinite. It is proved by duality instead, and `μ`
is asked to be σ-finite for the truncation the duality argument needs. See for instance
E. H. Lieb and M. Loss, *Analysis*, 2nd edition, American Mathematical Society, 2001, section 2.4.
-/
theorem lintegral_rpow_lintegral_le [SigmaFinite μ] [SFinite ν] {p : ℝ} (hp : 1 ≤ p)
    {H : α → β → ℝ≥0∞} (hH : AEMeasurable (uncurry H) (μ.prod ν)) :
    (∫⁻ x, (∫⁻ t, H x t ∂ν) ^ p ∂μ) ^ (1 / p)
      ≤ ∫⁻ t, (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν := by
  obtain ⟨K, hKmeas, hKae⟩ := hH
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ t ∂ν, H x t = K (x, t) := ae_ae_of_ae_prod hKae
  have h2 : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, H x t = K (x, t) :=
    ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := ν)
      (ν := μ)).quasiMeasurePreserving.ae hKae)
  have hL : ∫⁻ x, (∫⁻ t, H x t ∂ν) ^ p ∂μ = ∫⁻ x, (∫⁻ t, K (x, t) ∂ν) ^ p ∂μ := by
    refine lintegral_congr_ae (h1.mono fun x hx => ?_)
    dsimp only
    rw [lintegral_congr_ae hx]
  have hR : ∫⁻ t, (∫⁻ x, H x t ^ p ∂μ) ^ (1 / p) ∂ν
      = ∫⁻ t, (∫⁻ x, K (x, t) ^ p ∂μ) ^ (1 / p) ∂ν := by
    refine lintegral_congr_ae (h2.mono fun t ht => ?_)
    dsimp only
    rw [lintegral_congr_ae (ht.mono fun x hx => by rw [hx])]
  rw [hL, hR]
  exact lintegral_rpow_lintegral_le_of_measurable (H := fun x t => K (x, t)) hp hKmeas


end ENNReal

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}

/-- The square of the `L²` seminorm is the Lebesgue integral of the squared norms. -/
theorem sq_eLpNorm_two {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {f : E → ℂ}
    {μ : Measure E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 ∂μ := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm (μ := μ) (p := 2) (f := f)
    (by norm_num) (by norm_num) hf
  have h2 : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ (2 : ℕ) := fun x ↦ by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [ENNReal.toReal_ofNat, h2] at h
  exact h.symm

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
theorem enorm_convolution_le_lintegral_enorm (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun _ => L.le_opENorm₂ _ _)

/-- The convolution is additive in its first factor at every point where both convolutions
exist, subtraction version of `MeasureTheory.ConvolutionExistsAt.add_distrib`. -/
theorem ConvolutionExistsAt.sub_distrib {f' : G → E} {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f' g x L μ) :
    ((f - f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x - (f' ⋆[L, μ] g) x := by
  simp only [convolution_def, Pi.sub_apply, L.map_sub₂, integral_sub hfg hfg']

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [μ.IsAddRightInvariant]

/-- The right-hand factor of a convolution integrand, seen as a function on `G × G`, is
almost-everywhere strongly measurable. -/
theorem AEStronglyMeasurable.comp_fst_sub_snd (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun z : G × G => g (z.1 - z.2)) (μ.prod μ) :=
  (hg.mono_ac (quasiMeasurePreserving_sub_of_right_invariant μ
    μ).absolutelyContinuous).comp_measurable measurable_sub

omit [NormedSpace ℝ F] in
/-- The intermediate estimate of the `L¹ ∗ Lᵖ → Lᵖ` case of Young's inequality, for `p ≠ ∞`: the
`p`-th moment of the convolution of the norms, `x ↦ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ`, is at
most `(‖L‖ₑ * ‖f‖₁) ^ p * ‖g‖ₚ ^ p`. This is the weighted Minkowski inequality
`ENNReal.lintegral_rpow_lintegral_mul_le` with the weight `‖L‖ₑ * ‖f ·‖ₑ`, followed by the
translation invariance of `μ`; it carries both the norm bound
`MeasureTheory.eLpNorm_convolution_le_of_ne_top` and the almost-everywhere existence
`MeasureTheory.MemLp.ae_convolutionExistsAt`. -/
theorem lintegral_rpow_lintegral_enorm_mul_enorm_sub_le (L : E →L[𝕜] E' →L[𝕜] F) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, (∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ) ^ p.toReal ∂μ
      ≤ (‖L‖ₑ * eLpNorm f 1 μ) ^ p.toReal * eLpNorm g p μ ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq1 : (1:ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  set w : G → ℝ≥0∞ := fun t => ‖L‖ₑ * ‖f t‖ₑ with hw_def
  have hw : AEMeasurable w μ := hf.enorm.const_mul _
  have hH : AEMeasurable (uncurry fun x t : G => ‖g (x - t)‖ₑ) (μ.prod μ) :=
    (AEStronglyMeasurable.comp_fst_sub_snd hg).enorm
  have hinv : ∀ t : G, ∫⁻ x, ‖g (x - t)‖ₑ ^ p.toReal ∂μ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ :=
    fun t => lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ ^ p.toReal) t
  have hwint : ∫⁻ t, w t ∂μ = ‖L‖ₑ * eLpNorm f 1 μ := by
    rw [hw_def, lintegral_const_mul'' _ hf.enorm, eLpNorm_one_eq_lintegral_enorm hf]
  calc ∫⁻ x, (∫⁻ t, w t * ‖g (x - t)‖ₑ ∂μ) ^ p.toReal ∂μ
      ≤ (∫⁻ t, w t ∂μ) ^ (p.toReal - 1) *
          ∫⁻ t, w t * ∫⁻ x, ‖g (x - t)‖ₑ ^ p.toReal ∂μ ∂μ :=
        ENNReal.lintegral_rpow_lintegral_mul_le hq1 hw hH
    _ = (∫⁻ t, w t ∂μ) ^ (p.toReal - 1) * ((∫⁻ t, w t ∂μ) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ) := by
        simp_rw [hinv]
        rw [lintegral_mul_const'' _ hw]
    _ = (∫⁻ t, w t ∂μ) ^ p.toReal * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
        rw [← mul_assoc]
        congr 1
        nth_rewrite 2 [← ENNReal.rpow_one (∫⁻ t, w t ∂μ)]
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one]
        congr 1
        ring
    _ = (‖L‖ₑ * eLpNorm f 1 μ) ^ p.toReal * eLpNorm g p μ ^ p.toReal := by
        rw [hwint, lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hg]

/-- **Young's convolution inequality** in the case `L¹ ∗ Lᵖ → Lᵖ` with `p ≠ ∞`. -/
theorem eLpNorm_convolution_le_of_ne_top (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) p μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq0 : (0:ℝ) < p.toReal := ENNReal.toReal_pos hp0 hp'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' (hf.convolution L hg)]
  calc (∫⁻ x, ‖(f ⋆[L, μ] g) x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (∫⁻ x, (∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        gcongr with x
        exact enorm_convolution_le_lintegral_enorm x
    _ ≤ ((‖L‖ₑ * eLpNorm f 1 μ) ^ p.toReal * eLpNorm g p μ ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr
        exact lintegral_rpow_lintegral_enorm_mul_enorm_sub_le L hp hp' hf hg
    _ = ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

omit [NormedSpace ℝ F] in
/-- The convolution of the norms is bounded pointwise by `‖L‖ₑ * ‖f‖₁ * ‖g‖_∞`; this is the
`L¹ ∗ L^∞` case of Young's inequality before the essential supremum is taken. -/
theorem lintegral_enorm_mul_enorm_sub_le_eLpNormEssSup (L : E →L[𝕜] E' →L[𝕜] F)
    (hf : AEStronglyMeasurable f μ) (x : G) :
    ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNormEssSup g μ := by
  have hae : ∀ᵐ t ∂μ, ‖g (x - t)‖ₑ ≤ eLpNormEssSup g μ :=
    (quasiMeasurePreserving_sub_left_of_right_invariant μ x).ae
      (_root_.ae_le_essSup (μ := μ) (f := fun y => ‖g y‖ₑ))
  calc ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ
      ≤ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * eLpNormEssSup g μ ∂μ :=
        lintegral_mono_ae (hae.mono fun t ht => by gcongr)
    _ = ‖L‖ₑ * eLpNorm f 1 μ * eLpNormEssSup g μ := by
        rw [lintegral_mul_const'' _ (hf.enorm.const_mul _), lintegral_const_mul'' _ hf.enorm,
          eLpNorm_one_eq_lintegral_enorm hf]

/-- **Young's convolution inequality** in the case `L¹ ∗ L^∞ → L^∞`. -/
theorem eLpNormEssSup_convolution_le (hf : AEStronglyMeasurable f μ) :
    eLpNormEssSup (f ⋆[L, μ] g) μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNormEssSup g μ := by
  rw [eLpNormEssSup]
  refine essSup_le_of_ae_le _ (Eventually.of_forall fun x => ?_)
  exact (enorm_convolution_le_lintegral_enorm x).trans
    (lintegral_enorm_mul_enorm_sub_le_eLpNormEssSup L hf x)

/-- **Young's convolution inequality** in the case `L¹ ∗ Lᵖ → Lᵖ`, for every `1 ≤ p ≤ ∞`.

Only measurability is assumed: where the convolution fails to exist it is `0`, and the bound holds
there for free. -/
theorem eLpNorm_convolution_le (hp : 1 ≤ p) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) p μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · rw [eLpNorm_exponent_top (hf.convolution L hg), eLpNorm_exponent_top hg]
    exact eLpNormEssSup_convolution_le hf
  · exact eLpNorm_convolution_le_of_ne_top hp hp' hf hg

/-- `Lᵖ` is a module over `L¹` under convolution: the convolution of an `L¹` function with an `Lᵖ`
function is in `Lᵖ`. -/
theorem MemLp.convolution (hp : 1 ≤ p) (hf : MemLp f 1 μ) (hg : MemLp g p μ) :
    MemLp (f ⋆[L, μ] g) p μ := by
  refine lt_of_le_of_lt
    (eLpNorm_convolution_le hp hf.aestronglyMeasurable hg.aestronglyMeasurable) ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp [enorm_lt_top]) hf.eLpNorm_lt_top)
    hg.eLpNorm_lt_top

omit [NormedSpace ℝ F] in
/-- **The convolution of an `L¹` function with an `Lᵖ` function exists almost everywhere**
([brezis2011functional] Theorem 4.15, first sentence): for `f ∈ L¹` and `g ∈ Lᵖ`, `1 ≤ p ≤ ∞`,
the integrand `t ↦ L (f t) (g (x - t))` is integrable for almost every `x`. Mathlib has the case
`p = 1` (`MeasureTheory.Integrable.ae_convolution_exists`); for `p ≠ ∞` the `p`-th moment of the
convolution of the norms is finite by
`MeasureTheory.lintegral_rpow_lintegral_enorm_mul_enorm_sub_le`, so that convolution is finite
almost everywhere, and for `p = ∞` it is bounded everywhere. -/
theorem MemLp.ae_convolutionExistsAt (hp : 1 ≤ p) (hf : MemLp f 1 μ) (hg : MemLp g p μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt f g x L μ := by
  have hmeas : ∀ x, AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ := fun x =>
    hf.aestronglyMeasurable.convolution_integrand_snd L hg.aestronglyMeasurable x
  have hbound : ∀ x, ∫⁻ t, ‖L (f t) (g (x - t))‖ₑ ∂μ
      ≤ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ :=
    fun x => lintegral_mono fun t => L.le_opENorm₂ _ _
  suffices h : ∀ᵐ x ∂μ, ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ < ∞ by
    filter_upwards [h] with x hx
    exact ⟨hmeas x, (hbound x).trans_lt hx⟩
  rcases eq_or_ne p ∞ with rfl | hp'
  · refine Eventually.of_forall fun x => ?_
    refine (lintegral_enorm_mul_enorm_sub_le_eLpNormEssSup L hf.aestronglyMeasurable
      x).trans_lt ?_
    rw [← eLpNorm_exponent_top hg.aestronglyMeasurable]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top hf.eLpNorm_lt_top)
      hg.eLpNorm_lt_top
  · have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
    have hq0 : (0:ℝ) < p.toReal := ENNReal.toReal_pos hp0 hp'
    have hI : AEMeasurable (fun x => ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ) μ :=
      ((hf.aestronglyMeasurable.enorm.comp_snd.const_mul _).mul
        (AEStronglyMeasurable.comp_fst_sub_snd
          hg.aestronglyMeasurable).enorm).lintegral_prod_right'
    have hfin : ∫⁻ x, (∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ) ^ p.toReal ∂μ ≠ ∞ := by
      refine ((lintegral_rpow_lintegral_enorm_mul_enorm_sub_le L hp hp' hf.aestronglyMeasurable
        hg.aestronglyMeasurable).trans_lt ?_).ne
      exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg hq0.le
          (ENNReal.mul_ne_top enorm_ne_top hf.eLpNorm_ne_top))
        (ENNReal.rpow_lt_top_of_nonneg hq0.le hg.eLpNorm_ne_top)
    filter_upwards [ae_lt_top' (hI.pow_const _) hfin] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hq0).1 hx

omit [MeasurableNeg G] [SFinite μ] in
/-- Translating a convolution translates its first factor:
`(f ⋆ g) (x + h) = (f (· + h) ⋆ g) x`. -/
theorem convolution_apply_add_right (x h : G) :
    (f ⋆[L, μ] g) (x + h) = ((fun t => f (t + h)) ⋆[L, μ] g) x := by
  simp only [convolution_def]
  rw [← integral_add_right_eq_self (fun t => L (f t) (g (x + h - t))) h]
  simp only [add_sub_add_right_eq_sub]

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

/-! ### Convolution with a fixed kernel as an operator on `Lᵖ` -/

section ConvolutionCLM

variable {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant] [NormedSpace ℝ F] {K : G → ℝ}

variable (F p) in
/-- **Convolution with a fixed integrable kernel** `K` as a bounded operator on `Lp F p μ`,
`f ↦ K ⋆ f` ([brezis2011functional] Corollary 4.28, the operator `u ↦ G ⋆ u`). Its values are in
`Lᵖ` by Young's inequality (`MeasureTheory.MemLp.convolution`), it is linear because the
convolution is linear in its second factor wherever the integral exists, which is almost
everywhere (`MeasureTheory.MemLp.ae_convolutionExistsAt`), and its norm is at most `‖K‖₁`
(`MeasureTheory.eLpNorm_convolution_lsmul_le`). -/
noncomputable def Lp.convolutionCLM [Fact (1 ≤ p)] (hK : Integrable K μ) :
    Lp F p μ →L[ℝ] Lp F p μ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ((memLp_one_iff_integrable.2 hK).convolution (L := lsmul ℝ ℝ) Fact.out
          (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        rw [convolution_congr _ (ae_eq_refl K) (Lp.coeFn_add f g)]
        filter_upwards [(memLp_one_iff_integrable.2 hK).ae_convolutionExistsAt (L := lsmul ℝ ℝ)
          Fact.out (Lp.memLp f),
          (memLp_one_iff_integrable.2 hK).ae_convolutionExistsAt (L := lsmul ℝ ℝ) Fact.out
          (Lp.memLp g)] with x hf hg
        exact hf.distrib_add hg
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        rw [convolution_congr _ (ae_eq_refl K) (Lp.coeFn_smul c f), convolution_smul] }
    (eLpNorm K 1 μ).toReal fun f => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono
        (ENNReal.mul_ne_top (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top
          (Lp.memLp f).eLpNorm_ne_top) ?_
      exact eLpNorm_convolution_lsmul_le Fact.out hK.aestronglyMeasurable
        (Lp.aestronglyMeasurable f)

/-- The operator `MeasureTheory.Lp.convolutionCLM` is the convolution, almost everywhere. -/
theorem Lp.coeFn_convolutionCLM [Fact (1 ≤ p)] (hK : Integrable K μ) (f : Lp F p μ) :
    ⇑(Lp.convolutionCLM F p hK f) =ᵐ[μ] K ⋆[lsmul ℝ ℝ, μ] f :=
  MemLp.coeFn_toLp
    ((memLp_one_iff_integrable.2 hK).convolution (L := lsmul ℝ ℝ) Fact.out (Lp.memLp f))

/-- The operator norm of the convolution with `K` is at most `‖K‖₁`
([brezis2011functional] Corollary 4.28, Exercise 4.32). -/
theorem Lp.norm_convolutionCLM_le [Fact (1 ≤ p)] (hK : Integrable K μ) :
    ‖Lp.convolutionCLM F p hK‖ ≤ (eLpNorm K 1 μ).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- **Young's inequality on `Lᵖ`**: `‖K ⋆ f‖ₚ ≤ ‖K‖₁ * ‖f‖ₚ`. -/
theorem Lp.norm_convolutionCLM_apply_le [Fact (1 ≤ p)] (hK : Integrable K μ) (f : Lp F p μ) :
    ‖Lp.convolutionCLM F p hK f‖ ≤ (eLpNorm K 1 μ).toReal * ‖f‖ :=
  (Lp.convolutionCLM F p hK).le_of_opNorm_le (Lp.norm_convolutionCLM_le hK) f

end ConvolutionCLM

/-! ### Young's convolution inequality in its general form -/

section YoungGeneral

variable {𝕜 G E E' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  [MeasurableSpace G] [AddGroup G] {μ : Measure G}
  {f : G → E} {g : G → E'} {L : E →L[𝕜] E' →L[𝕜] F}
  [MeasurableAdd₂ G] [MeasurableNeg G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]

/-- On an additive group carrying a measure that is invariant under right translation and under
negation, the reflection `t ↦ x - t` is measure preserving. This is the counterpart of
`MeasureTheory.measurePreserving_sub_left`, which assumes left instead of right invariance. -/
theorem measurePreserving_sub_left_of_isAddRightInvariant (μ : Measure G) [μ.IsAddRightInvariant]
    [μ.IsNegInvariant] (x : G) : MeasurePreserving (fun t => x - t) μ μ := by
  have h := (measurePreserving_neg μ).comp (measurePreserving_sub_right μ x)
  simpa [Function.comp_def, neg_sub] using h

/-- Reflection invariance of the `Lᵖ` seminorm: `‖g (x - ·)‖_p = ‖g‖_p`. -/
theorem eLpNorm_comp_sub_left (hg : AEStronglyMeasurable g μ) (x : G) :
    eLpNorm (fun t => g (x - t)) p μ = eLpNorm g p μ :=
  eLpNorm_comp_measurePreserving hg (measurePreserving_sub_left_of_isAddRightInvariant μ x)

/-- Reflection invariance of the Lebesgue integral, with no measurability hypothesis. This is the
counterpart of `MeasureTheory.lintegral_sub_left_eq_self`, which assumes left instead of right
invariance. -/
theorem lintegral_sub_left_eq_self_of_isAddRightInvariant (h : G → ℝ≥0∞) (x : G) :
    ∫⁻ t, h (x - t) ∂μ = ∫⁻ t, h t ∂μ :=
  calc ∫⁻ t, h (x - t) ∂μ = ∫⁻ t, (fun s => h (-s)) (t - x) ∂μ := by simp_rw [neg_sub]
    _ = ∫⁻ t, h (-t) ∂μ := lintegral_sub_right_eq_self (fun s => h (-s)) x
    _ = ∫⁻ t, h t ∂μ := lintegral_neg_eq_self h

variable [SFinite μ]

/-- The analytic core of Young's convolution inequality in its general form, with the exponents
as real numbers: for `1 ≤ P, Q` and `0 < R` with `1/P + 1/Q = 1 + 1/R`,
`∫⁻ ‖f ⋆ g‖ ^ R ≤ ‖L‖ ^ R * (∫⁻ ‖f‖ ^ P) ^ (R/P) * (∫⁻ ‖g‖ ^ Q) ^ (R/Q)`.

The proof is the three-exponent Hölder inequality `ENNReal.lintegral_mul_mul_norm_pow_le` applied
to the splitting `‖f t‖ * ‖g (x - t)‖ = (‖f t‖ ^ P * ‖g (x - t)‖ ^ Q) ^ (1/R) *
(‖f t‖ ^ P) ^ (1/P - 1/R) * (‖g (x - t)‖ ^ Q) ^ (1/Q - 1/R)`, followed by Tonelli's theorem. Both
the `Q`-th moment of the reflected translate `g (x - ·)` and the exchange of the two integrations
use the invariance of `μ`. -/
theorem lintegral_enorm_convolution_rpow_le {P Q R : ℝ} (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hR : 0 < R)
    (hPQR : 1 / P + 1 / Q = 1 + 1 / R)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖(f ⋆[L, μ] g) x‖ₑ ^ R ∂μ
      ≤ ‖L‖ₑ ^ R * (∫⁻ t, ‖f t‖ₑ ^ P ∂μ) ^ (R / P) * (∫⁻ t, ‖g t‖ₑ ^ Q ∂μ) ^ (R / Q) := by
  have hP0 : (0:ℝ) < P := lt_of_lt_of_le one_pos hP
  have hQ0 : (0:ℝ) < Q := lt_of_lt_of_le one_pos hQ
  have hQ1 : 1 / Q ≤ 1 := by rw [div_le_one hQ0]; exact hQ
  have hP1 : 1 / P ≤ 1 := by rw [div_le_one hP0]; exact hP
  have ha₁ : (0:ℝ) ≤ 1 / R := by positivity
  have ha₂ : (0:ℝ) ≤ 1 / P - 1 / R := by linarith
  have ha₃ : (0:ℝ) ≤ 1 / Q - 1 / R := by linarith
  have hsum : 1 / R + (1 / P - 1 / R) + (1 / Q - 1 / R) = 1 := by linarith
  have hgx : ∀ x : G, AEStronglyMeasurable (fun t => g (x - t)) μ := fun x =>
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant μ x)
  have hBx : ∀ x : G, ∫⁻ t, ‖g (x - t)‖ₑ ^ Q ∂μ = ∫⁻ t, ‖g t‖ₑ ^ Q ∂μ := fun x =>
    lintegral_sub_left_eq_self_of_isAddRightInvariant (fun s => ‖g s‖ₑ ^ Q) x
  have hprod : AEMeasurable (uncurry fun x t : G => ‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q) (μ.prod μ) :=
    (hf.enorm.comp_snd.pow_const P).mul
      ((AEStronglyMeasurable.comp_fst_sub_snd hg).enorm.pow_const Q)
  have hCmeas : AEMeasurable (fun x => ∫⁻ t, ‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q ∂μ) μ :=
    hprod.lintegral_prod_right'
  have hCint : ∫⁻ x, (∫⁻ t, ‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q ∂μ) ∂μ
      = (∫⁻ t, ‖f t‖ₑ ^ P ∂μ) * ∫⁻ t, ‖g t‖ₑ ^ Q ∂μ := by
    calc ∫⁻ x, (∫⁻ t, ‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q ∂μ) ∂μ
        = ∫⁻ t, ∫⁻ x, ‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q ∂μ ∂μ := lintegral_lintegral_swap hprod
      _ = ∫⁻ t, ‖f t‖ₑ ^ P * ∫⁻ x, ‖g (x - t)‖ₑ ^ Q ∂μ ∂μ :=
          lintegral_congr fun t => lintegral_const_mul'' _
            ((hg.comp_quasiMeasurePreserving
              (measurePreserving_sub_right μ t).quasiMeasurePreserving).enorm.pow_const Q)
      _ = ∫⁻ t, ‖f t‖ₑ ^ P * ∫⁻ x, ‖g x‖ₑ ^ Q ∂μ ∂μ :=
          lintegral_congr fun t => by
            rw [lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ ^ Q) t]
      _ = (∫⁻ t, ‖f t‖ₑ ^ P ∂μ) * ∫⁻ t, ‖g t‖ₑ ^ Q ∂μ :=
          lintegral_mul_const'' _ (hf.enorm.pow_const P)
  have hrw : ∀ u v : ℝ≥0∞,
      (u ^ P * v ^ Q) ^ (1 / R) * (u ^ P) ^ (1 / P - 1 / R)
        * (v ^ Q) ^ (1 / Q - 1 / R) = u * v := by
    intro u v
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha₁]
    calc (u ^ P) ^ (1/R) * (v ^ Q) ^ (1/R) * (u ^ P) ^ (1/P - 1/R) * (v ^ Q) ^ (1/Q - 1/R)
        = ((u ^ P) ^ (1/R) * (u ^ P) ^ (1/P - 1/R))
            * ((v ^ Q) ^ (1/R) * (v ^ Q) ^ (1/Q - 1/R)) := by ring
      _ = (u ^ P) ^ (1/P) * (v ^ Q) ^ (1/Q) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ ha₁ ha₂, ← ENNReal.rpow_add_of_nonneg _ _ ha₁ ha₃,
            show 1/R + (1/P - 1/R) = 1/P by ring, show 1/R + (1/Q - 1/R) = 1/Q by ring]
      _ = u * v := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel hP0.ne',
            mul_one_div_cancel hQ0.ne', ENNReal.rpow_one, ENNReal.rpow_one]
  have hpoint : ∀ x : G, ‖(f ⋆[L, μ] g) x‖ₑ ≤ ‖L‖ₑ *
      ((∫⁻ t, ‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q ∂μ) ^ (1 / R)
        * (∫⁻ t, ‖f t‖ₑ ^ P ∂μ) ^ (1 / P - 1 / R)
        * (∫⁻ t, ‖g t‖ₑ ^ Q ∂μ) ^ (1 / Q - 1 / R)) := by
    intro x
    refine (enorm_convolution_le_lintegral_enorm x).trans ?_
    have h0 : ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ
        = ‖L‖ₑ * ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ := by
      simp_rw [mul_assoc]
      exact lintegral_const_mul'' _ (hf.enorm.mul (hgx x).enorm)
    rw [h0, ← hBx x]
    gcongr
    calc ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ
        = ∫⁻ t, (‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q) ^ (1/R) * (‖f t‖ₑ ^ P) ^ (1/P - 1/R)
              * (‖g (x - t)‖ₑ ^ Q) ^ (1/Q - 1/R) ∂μ :=
          lintegral_congr fun t => (hrw _ _).symm
      _ ≤ _ := ENNReal.lintegral_mul_mul_norm_pow_le
            ((hf.enorm.pow_const P).mul ((hgx x).enorm.pow_const Q))
            (hf.enorm.pow_const P) ((hgx x).enorm.pow_const Q) ha₁ ha₂ ha₃ hsum
  have halg : ∀ a A B : ℝ≥0∞,
      a ^ R * A ^ ((1/P - 1/R) * R) * B ^ ((1/Q - 1/R) * R) * (A * B)
        = a ^ R * A ^ (R/P) * B ^ (R/Q) := by
    intro a A B
    have e1 : ((1:ℝ)/P - 1/R) * R + 1 = R / P := by field_simp; ring
    have e2 : ((1:ℝ)/Q - 1/R) * R + 1 = R / Q := by field_simp; ring
    calc a ^ R * A ^ ((1/P - 1/R) * R) * B ^ ((1/Q - 1/R) * R) * (A * B)
        = a ^ R * (A ^ ((1/P - 1/R) * R) * A ^ (1:ℝ)) * (B ^ ((1/Q - 1/R) * R) * B ^ (1:ℝ)) := by
          simp only [ENNReal.rpow_one]; ring
      _ = a ^ R * A ^ (R/P) * B ^ (R/Q) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg ha₂ hR.le) zero_le_one,
            ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg ha₃ hR.le) zero_le_one, e1, e2]
  have hbound : ∀ x : G, ‖(f ⋆[L, μ] g) x‖ₑ ^ R
      ≤ ‖L‖ₑ ^ R * (∫⁻ t, ‖f t‖ₑ ^ P ∂μ) ^ ((1/P - 1/R) * R)
          * (∫⁻ t, ‖g t‖ₑ ^ Q ∂μ) ^ ((1/Q - 1/R) * R)
        * ∫⁻ t, ‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q ∂μ := by
    intro x
    refine (ENNReal.rpow_le_rpow (hpoint x) hR.le).trans_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hR.le, ENNReal.mul_rpow_of_nonneg _ _ hR.le,
      ENNReal.mul_rpow_of_nonneg _ _ hR.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul, one_div_mul_cancel hR.ne', ENNReal.rpow_one]
    ring
  calc ∫⁻ x, ‖(f ⋆[L, μ] g) x‖ₑ ^ R ∂μ
      ≤ ∫⁻ x, ‖L‖ₑ ^ R * (∫⁻ t, ‖f t‖ₑ ^ P ∂μ) ^ ((1/P - 1/R) * R)
            * (∫⁻ t, ‖g t‖ₑ ^ Q ∂μ) ^ ((1/Q - 1/R) * R)
          * ∫⁻ t, ‖f t‖ₑ ^ P * ‖g (x - t)‖ₑ ^ Q ∂μ ∂μ := lintegral_mono hbound
    _ = ‖L‖ₑ ^ R * (∫⁻ t, ‖f t‖ₑ ^ P ∂μ) ^ ((1/P - 1/R) * R)
            * (∫⁻ t, ‖g t‖ₑ ^ Q ∂μ) ^ ((1/Q - 1/R) * R)
          * ((∫⁻ t, ‖f t‖ₑ ^ P ∂μ) * ∫⁻ t, ‖g t‖ₑ ^ Q ∂μ) := by
        rw [lintegral_const_mul'' _ hCmeas, hCint]
    _ = ‖L‖ₑ ^ R * (∫⁻ t, ‖f t‖ₑ ^ P ∂μ) ^ (R/P) * (∫⁻ t, ‖g t‖ₑ ^ Q ∂μ) ^ (R/Q) :=
        halg _ _ _

/-- **Young's convolution inequality** in the case `r = ∞`, that is, for Hölder conjugate `p` and
`q`: the convolution of an `Lᵖ` function with an `L^q` function is bounded. -/
theorem eLpNormEssSup_convolution_le_of_inv_add_inv {p q : ℝ≥0∞}
    (hpq : 1 / p + 1 / q = 1) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNormEssSup (f ⋆[L, μ] g) μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  have : ENNReal.HolderTriple p q 1 := ⟨by simpa [one_div] using hpq⟩
  refine essSup_le_of_ae_le _ (Eventually.of_forall fun x => ?_)
  have hgx : AEStronglyMeasurable (fun t => g (x - t)) μ :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant μ x)
  have h1 : ‖(f ⋆[L, μ] g) x‖ₑ ≤ eLpNorm (fun t => L (f t) (g (x - t))) 1 μ :=
    (enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one
  refine h1.trans ?_
  have h2 := eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm (p := p) (q := q) (r := 1) L hf hgx
  rwa [eLpNorm_comp_sub_left hg x] at h2

/-- **Young's convolution inequality** in its general form, for a finite `r`. -/
theorem eLpNorm_convolution_le_of_inv_add_inv_of_ne_top {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hr : r ≠ ∞) (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
  have hinv : p⁻¹ + q⁻¹ = 1 + r⁻¹ := by simpa [one_div] using hpqr
  have hr0 : r ≠ 0 := by
    rintro rfl
    have hle : p⁻¹ + q⁻¹ ≤ 2 := by
      simpa [one_add_one_eq_two] using
        add_le_add (ENNReal.inv_le_one.2 hp) (ENNReal.inv_le_one.2 hq)
    rw [hinv] at hle
    simp at hle
  have hlt : (1:ℝ≥0∞) < 1 + r⁻¹ :=
    ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.2 hr)
  have hpt : p ≠ ∞ := by
    rintro rfl
    rw [ENNReal.inv_top, zero_add] at hinv
    have h : q⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hq
    rw [hinv] at h
    exact absurd h (not_le.2 hlt)
  have hqt : q ≠ ∞ := by
    rintro rfl
    rw [ENNReal.inv_top, add_zero] at hinv
    have h : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
    rw [hinv] at h
    exact absurd h (not_le.2 hlt)
  have hP1 : (1:ℝ) ≤ p.toReal := by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp
  have hQ1 : (1:ℝ) ≤ q.toReal := by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hqt hq
  have hR0 : (0:ℝ) < r.toReal := ENNReal.toReal_pos hr0 hr
  have hreal : 1 / p.toReal + 1 / q.toReal = 1 + 1 / r.toReal := by
    have h := congrArg ENNReal.toReal hinv
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp0) (ENNReal.inv_ne_top.2 hq0),
      ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.inv_ne_top.2 hr0)] at h
    simpa [ENNReal.toReal_inv, one_div] using h
  have hcore := lintegral_enorm_convolution_rpow_le (L := L) hP1 hQ1 hR0 hreal hf hg
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hpt hf,
    lintegral_rpow_enorm_eq_rpow_eLpNorm hq0 hqt hg, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_div_cancel₀ _ (ne_of_gt (lt_of_lt_of_le one_pos hP1)),
    mul_div_cancel₀ _ (ne_of_gt (lt_of_lt_of_le one_pos hQ1))] at hcore
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr (hf.convolution L hg)]
  calc (∫⁻ x, ‖(f ⋆[L, μ] g) x‖ₑ ^ r.toReal ∂μ) ^ (1 / r.toReal)
      ≤ (‖L‖ₑ ^ r.toReal * eLpNorm f p μ ^ r.toReal * eLpNorm g q μ ^ r.toReal)
          ^ (1 / r.toReal) := ENNReal.rpow_le_rpow hcore (by positivity)
    _ = ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hR0.le, ← ENNReal.mul_rpow_of_nonneg _ _ hR0.le,
          ← ENNReal.rpow_mul, mul_one_div_cancel hR0.ne', ENNReal.rpow_one]

/-- **Young's convolution inequality** in its general form: for `1 ≤ p, q ≤ ∞` and an exponent `r`
with `1/p + 1/q = 1 + 1/r`, `‖f ⋆ g‖_r ≤ ‖L‖ * ‖f‖_p * ‖g‖_q`.

The measure is asked to be invariant under negation on top of being invariant under right
translation: the proof integrates `t ↦ ‖g (x - t)‖`, so it needs the reflection `t ↦ x - t` to
preserve `μ`. The case `q = 1`, `r = p` is `MeasureTheory.eLpNorm_convolution_le`, which is proved
separately because it needs no such hypothesis. See for instance E. H. Lieb and M. Loss,
*Analysis*, 2nd edition, American Mathematical Society, 2001, section 4.2. -/
theorem eLpNorm_convolution_le_of_inv_add_inv {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rcases eq_or_ne r ∞ with rfl | hr
  · rw [eLpNorm_exponent_top (hf.convolution L hg)]
    exact eLpNormEssSup_convolution_le_of_inv_add_inv (by simpa using hpqr) hf hg
  · exact eLpNorm_convolution_le_of_inv_add_inv_of_ne_top hp hq hr hpqr hf hg

/-- **The adjoint identity for the convolution** ([brezis2011functional] Proposition 4.16): for
`f ∈ L¹`, `g ∈ Lᵖ` and `h ∈ L^q` with `1/p + 1/q = 1`, writing `f̌ x = f (-x)`,
`∫ (f ⋆ g) h = ∫ g (f̌ ⋆ h)`. The function `(x, t) ↦ f t * g (x - t) * h x` is integrable on
`μ × μ` by Young's and Hölder's inequalities, and the identity is Fubini's theorem for it after
the measure-preserving change of variables `(x, t) ↦ (x - t, -t)`. -/
theorem integral_convolution_mul {𝕂 : Type*} [RCLike 𝕂] {p q : ℝ≥0∞} [p.HolderConjugate q]
    {f g h : G → 𝕂} (hf : MemLp f 1 μ) (hg : MemLp g p μ) (hh : MemLp h q μ) :
    ∫ x, (f ⋆[mul 𝕂 𝕂, μ] g) x * h x ∂μ = ∫ y, g y * ((f ∘ Neg.neg) ⋆[mul 𝕂 𝕂, μ] h) y ∂μ := by
  have hp : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  set Φ : G × G → 𝕂 := fun z => f z.2 * g (z.1 - z.2) * h z.1 with hΦ
  set Ψ : G × G → 𝕂 := fun z => g z.1 * (f (-z.2) * h (z.1 - z.2)) with hΨ
  set T : G × G → G × G := fun z => (z.1 - z.2, -z.2) with hT
  have hTmp : MeasurePreserving T (μ.prod μ) (μ.prod μ) := by
    have h1 : MeasurePreserving (fun z : G × G => (z.1 - z.2, z.2)) (μ.prod μ) (μ.prod μ) :=
      measurePreserving_sub_prod μ μ
    have h2 : MeasurePreserving (Prod.map (id : G → G) (Neg.neg : G → G)) (μ.prod μ)
        (μ.prod μ) :=
      (MeasurePreserving.id μ).prod (measurePreserving_neg μ)
    exact h2.comp h1
  have hΨT : Ψ ∘ T = Φ := by
    funext z
    simp only [Function.comp_apply, hΨ, hΦ, hT, neg_neg, sub_neg_eq_add, sub_add_cancel]
    ring
  have hfneg : AEStronglyMeasurable (fun t => f (-t)) μ :=
    hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_neg μ)
  have hΨm : AEStronglyMeasurable Ψ (μ.prod μ) :=
    hg.aestronglyMeasurable.comp_fst.mul
      (hfneg.comp_snd.mul (AEStronglyMeasurable.comp_fst_sub_snd hh.aestronglyMeasurable))
  have hΦm : AEStronglyMeasurable Φ (μ.prod μ) := by
    rw [← hΨT]
    exact hΨm.comp_measurePreserving hTmp
  have hΦi : Integrable Φ (μ.prod μ) := by
    refine (integrable_prod_iff hΦm).2 ⟨?_, ?_⟩
    · filter_upwards [hf.ae_convolutionExistsAt (L := mul 𝕂 𝕂) hp hg] with x hx
      exact hx.mul_const (h x)
    · have hN : MemLp ((fun t => ‖f t‖) ⋆[mul ℝ ℝ, μ] fun t => ‖g t‖) p μ :=
        MemLp.convolution hp hf.norm hg.norm
      have hprod : MemLp (fun x => ((fun t => ‖f t‖) ⋆[mul ℝ ℝ, μ] fun t => ‖g t‖) x * ‖h x‖)
          1 μ :=
        hN.fun_mul hh.norm
      refine (memLp_one_iff_integrable.1 hprod).congr (Eventually.of_forall fun x => ?_)
      simp only [hΦ, norm_mul, convolution_def, ContinuousLinearMap.mul_apply']
      rw [integral_mul_const]
  have hΨi : Integrable Ψ (μ.prod μ) := by
    rw [← hΨT] at hΦi
    exact (hTmp.integrable_comp hΨm).1 hΦi
  calc ∫ x, (f ⋆[mul 𝕂 𝕂, μ] g) x * h x ∂μ
      = ∫ x, ∫ t, Φ (x, t) ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hΦ, convolution_def, ContinuousLinearMap.mul_apply']
        rw [integral_mul_const]
    _ = ∫ z, Φ z ∂(μ.prod μ) := (integral_prod Φ hΦi).symm
    _ = ∫ z, Ψ (T z) ∂(μ.prod μ) := by rw [← hΨT]; rfl
    _ = ∫ z, Ψ z ∂(μ.prod μ) := by
        rw [← integral_map hTmp.measurable.aemeasurable (by rwa [hTmp.map_eq]), hTmp.map_eq]
    _ = ∫ y, ∫ s, Ψ (y, s) ∂μ ∂μ := integral_prod Ψ hΨi
    _ = ∫ y, g y * ((f ∘ Neg.neg) ⋆[mul 𝕂 𝕂, μ] h) y ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hΨ, convolution_def, ContinuousLinearMap.mul_apply', Function.comp_apply]
        rw [integral_const_mul]

end YoungGeneral


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
at a point `x` where the convolution exists, the mollification error is dominated by the
`φ`-average of `‖f (x - t) - f x‖`. -/
theorem enorm_convolution_sub_le (hφ : Integrable φ μ) (hφ₁ : ∫ t, φ t ∂μ = 1) (x : G)
    (hex : ConvolutionExistsAt φ f x (lsmul ℝ ℝ) μ) :
    ‖(φ ⋆[lsmul ℝ ℝ, μ] f - f) x‖ₑ ≤ ∫⁻ t, ‖φ t‖ₑ * ‖f (x - t) - f x‖ₑ ∂μ := by
  have hid : (φ ⋆[lsmul ℝ ℝ, μ] f - f) x = ∫ t, φ t • (f (x - t) - f x) ∂μ := by
    have h1 : Integrable (fun t => φ t • f (x - t)) μ := hex
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
    (hφ₀ : ∀ t, 0 ≤ φ t) (hφ : Integrable φ μ) (hφ₁ : ∫ t, φ t ∂μ = 1) :
    eLpNorm (φ ⋆[lsmul ℝ ℝ, μ] f - f) p μ ^ p.toReal
      ≤ ∫⁻ t, ‖φ t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq1 : (1:ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hq0 : (0:ℝ) < p.toReal := lt_of_lt_of_le one_pos hq1
  have hex : ∀ᵐ x ∂μ, ConvolutionExistsAt φ f x (lsmul ℝ ℝ) μ :=
    (memLp_one_iff_integrable.2 hφ).ae_convolutionExistsAt hp hf
  have hH : AEMeasurable (uncurry fun x t : G => ‖f (x - t) - f x‖ₑ) (μ.prod μ) :=
    ((AEStronglyMeasurable.comp_fst_sub_snd hf.aestronglyMeasurable).sub
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst)).enorm
  have hmeas : AEStronglyMeasurable (φ ⋆[lsmul ℝ ℝ, μ] f - f) μ :=
    (hφ.aestronglyMeasurable.convolution (lsmul ℝ ℝ) hf.aestronglyMeasurable).sub
      hf.aestronglyMeasurable
  rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hmeas]
  calc ∫⁻ x, ‖(φ ⋆[lsmul ℝ ℝ, μ] f - f) x‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, (∫⁻ t, ‖φ t‖ₑ * ‖f (x - t) - f x‖ₑ ∂μ) ^ p.toReal ∂μ :=
        lintegral_mono_ae (hex.mono fun x hx =>
          ENNReal.rpow_le_rpow (enorm_convolution_sub_le hφ hφ₁ x hx) hq0.le)
    _ ≤ (∫⁻ t, ‖φ t‖ₑ ∂μ) ^ (p.toReal - 1) *
          ∫⁻ t, ‖φ t‖ₑ * ∫⁻ x, ‖f (x - t) - f x‖ₑ ^ p.toReal ∂μ ∂μ :=
        ENNReal.lintegral_rpow_lintegral_mul_le hq1 hφ.aestronglyMeasurable.enorm hH
    _ = ∫⁻ t, ‖φ t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal ∂μ := by
        rw [lintegral_enorm_eq_one hφ₀ hφ hφ₁, ENNReal.one_rpow, one_mul]
        refine lintegral_congr fun t => ?_
        have hm : AEStronglyMeasurable (fun x => f (x - t) - f x) μ :=
          (hf.aestronglyMeasurable.comp_measurePreserving
            (measurePreserving_sub_right μ t)).sub hf.aestronglyMeasurable
        rw [lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hm]

/-- **Mollification by an approximate identity converges in `Lᵖ`**
([brezis2011functional] Theorem 4.22). If `f ∈ Lᵖ(μ)` with `1 ≤ p < ∞` and `φ i` are
eventually nonnegative probability densities whose supports shrink to `0`, then the
mollifications `φ i ⋆ f` tend to `f` in `Lᵖ(μ)`. The support hypothesis is the one of
`MeasureTheory.convolution_tendsto_right`: `Tendsto (fun i => support (φ i)) l (𝓝 0).smallSets`.

The `Lᵖ` error of mollification is bounded by the `φ i`-average of the translation errors
(`MeasureTheory.eLpNorm_convolution_sub_rpow_le`), which are uniformly small on the support of
`φ i` once it lies in a small enough ball, by the continuity of translation
(`MeasureTheory.MemLp.tendsto_eLpNorm_sub_translate`). -/
theorem tendsto_eLpNorm_convolution_sub {ι : Type*} {l : Filter ι} {φ : ι → G → ℝ}
    (hφ₀ : ∀ᶠ i in l, ∀ t, 0 ≤ φ i t) (hφ : ∀ᶠ i in l, Integrable (φ i) μ)
    (hφ₁ : ∀ᶠ i in l, ∫ t, φ i t ∂μ = 1)
    (hsupp : Tendsto (fun i => support (φ i)) l (𝓝 0).smallSets)
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun i => eLpNorm (φ i ⋆[lsmul ℝ ℝ, μ] f - f) p μ) l (𝓝 0) := by
  have hq1 : (1:ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hq0 : (0:ℝ) < p.toReal := lt_of_lt_of_le one_pos hq1
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hnhds : {t : G | eLpNorm (fun x => f (x - t) - f x) p μ < ε} ∈ 𝓝 (0 : G) :=
    hf.tendsto_eLpNorm_sub_translate hp hp' (Iio_mem_nhds hε)
  filter_upwards [hφ₀, hφ, hφ₁, tendsto_smallSets_iff.1 hsupp _ hnhds] with i hi₀ hi hi₁ hisupp
  have hkey : eLpNorm (φ i ⋆[lsmul ℝ ℝ, μ] f - f) p μ ^ p.toReal ≤ ε ^ p.toReal := by
    refine (eLpNorm_convolution_sub_rpow_le hp hp' hf hi₀ hi hi₁).trans ?_
    have hpt : ∀ t : G, ‖φ i t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal
        ≤ ‖φ i t‖ₑ * ε ^ p.toReal := by
      intro t
      by_cases ht : t ∈ support (φ i)
      · gcongr
        exact (hisupp ht).le
      · simp [notMem_support.1 ht]
    calc ∫⁻ t, ‖φ i t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal ∂μ
        ≤ ∫⁻ t, ‖φ i t‖ₑ * ε ^ p.toReal ∂μ := lintegral_mono hpt
      _ = ε ^ p.toReal := by
          rw [lintegral_mul_const'' _ hi.aestronglyMeasurable.enorm,
            lintegral_enorm_eq_one hi₀ hi hi₁, one_mul]
  exact (ENNReal.rpow_le_rpow_iff hq0).1 hkey

/-- **Mollification converges in `Lᵖ`.** If `f ∈ Lᵖ(μ)` with `1 ≤ p < ∞` and the outer radii of a
family of bump functions tend to `0`, then the mollifications `(φ i).normed μ ⋆ f` tend to `f` in
`Lᵖ(μ)`.

This is the `Lᵖ` counterpart of `ContDiffBump.convolution_tendsto_right`, which gives the
pointwise convergence for a continuous `f`; it is the case of
`MeasureTheory.tendsto_eLpNorm_convolution_sub` where the approximate identity consists of
normalized bump functions. -/
theorem _root_.ContDiffBump.tendsto_eLpNorm_convolution_sub {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : G)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun i => eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f) p μ) l (𝓝 0) :=
  MeasureTheory.tendsto_eLpNorm_convolution_sub
    (Eventually.of_forall fun i => (φ i).nonneg_normed)
    (Eventually.of_forall fun i => (φ i).integrable_normed)
    (Eventually.of_forall fun i => (φ i).integral_normed)
    (ContDiffBump.tendsto_support_normed_smallSets hφ) hp hp' hf

end Mollifier

/-! ### Limits of `L^p` pairings

Three estimates that are used to pass to the limit in an integral along a sequence converging in
`L^p`: Hölder's inequality in the limit, the comparison of `L^1` with `L^p` on a finite measure,
and the bound of an integral against a bounded scalar factor. -/

section Limits

/-- **Hölder's inequality in the limit**: if `a j → a₀` in `L^p` and `b ∈ L^q` with `p` and `q`
Hölder conjugate, then the pairings `∫ b (a j)` converge to `∫ b a₀`. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    {a : ℕ → α → ℝ} {a₀ b : α → ℝ} (ha : ∀ j, MemLp (a j) p μ) (ha₀ : MemLp a₀ p μ)
    (hb : MemLp b q μ)
    (hlim : Tendsto (fun j ↦ eLpNorm (fun x ↦ a j x - a₀ x) p μ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x, b x * a j x ∂μ) atTop (𝓝 (∫ x, b x * a₀ x ∂μ)) := by
  have hint : ∀ c : α → ℝ, MemLp c p μ → Integrable (fun x ↦ b x * c x) μ := fun c hc ↦
    memLp_one_iff_integrable.1 (hb.fun_mul hc)
  have h0 : Tendsto (fun j ↦ eLpNorm (fun x ↦ a j x - a₀ x) p μ * eLpNorm b q μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hlim (Or.inr hb.eLpNorm_lt_top.ne)
  have hup : Tendsto (fun j ↦ (eLpNorm (fun x ↦ a j x - a₀ x) p μ * eLpNorm b q μ).toReal)
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = (0 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.tendsto_toReal (by simp)).comp h0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun j ↦ norm_nonneg _) (fun j ↦ ?_)
  · have hfin : eLpNorm (fun x ↦ a j x - a₀ x) p μ * eLpNorm b q μ ≠ ⊤ :=
      ENNReal.mul_ne_top ((ha j).sub ha₀).eLpNorm_lt_top.ne hb.eLpNorm_lt_top.ne
    have e : (∫ x, b x * a j x ∂μ) - ∫ x, b x * a₀ x ∂μ = ∫ x, b x * (a j x - a₀ x) ∂μ := by
      rw [← integral_sub (hint _ (ha j)) (hint _ ha₀)]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have h1 : ‖∫ x, b x * (a j x - a₀ x) ∂μ‖ₑ ≤ eLpNorm (fun x ↦ b x * (a j x - a₀ x)) 1 μ :=
      (enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one
    have h2 : eLpNorm (fun x ↦ b x * (a j x - a₀ x)) 1 μ
        ≤ eLpNorm (fun x ↦ a j x - a₀ x) p μ * eLpNorm b q μ := by
      have hs := eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) (p := q) (q := p) (r := 1)
        (f := fun x ↦ a j x - a₀ x) (φ := b) hb.aestronglyMeasurable
        ((ha j).aestronglyMeasurable.sub ha₀.aestronglyMeasurable)
        (hpqr := ENNReal.HolderTriple.symm)
      rw [mul_comm]
      exact le_of_le_of_eq hs (by rfl)
    rw [e]
    calc ‖∫ x, b x * (a j x - a₀ x) ∂μ‖
        = ‖∫ x, b x * (a j x - a₀ x) ∂μ‖ₑ.toReal := by
          rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
      _ ≤ _ := ENNReal.toReal_mono hfin (h1.trans h2)

/-- On a finite measure, convergence to zero in `L^p` implies convergence to zero in `L^1`: the
exponents are ordered the other way from the inclusion of the spaces, and the loss is a power of
the total mass. -/
theorem tendsto_eLpNorm_one_of_tendsto_eLpNorm [IsFiniteMeasure μ] (hp : 1 ≤ p)
    {h : ℕ → α → F} (hmeas : ∀ j, AEStronglyMeasurable (h j) μ)
    (hlim : Tendsto (fun j ↦ eLpNorm (h j) p μ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ eLpNorm (h j) 1 μ) atTop (𝓝 0) := by
  set C : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) with hC
  have hCfin : C ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg ?_ (measure_ne_top μ Set.univ)
    simp only [ENNReal.toReal_one, div_one, sub_nonneg]
    rcases eq_or_ne p ⊤ with rfl | hpt
    · simp
    · have h1 : (1 : ℝ) ≤ p.toReal := by
        rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp
      rw [div_le_one (by linarith)]
      exact h1
  have hb : Tendsto (fun j ↦ eLpNorm (h j) p μ * C) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hlim (Or.inr hCfin)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ ↦ zero_le)
    (fun j ↦ ?_)
  exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hmeas j)

/-- An integral against a bounded scalar factor is bounded by that factor times the `L^1` norm. -/
theorem enorm_integral_smul_le_of_bound [NormedSpace ℝ F] {b : α → ℝ} {C : ℝ}
    (hC : ∀ x, |b x| ≤ C) {h : α → F} :
    ‖∫ x, b x • h x ∂μ‖ₑ ≤ ENNReal.ofReal C * eLpNorm h 1 μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ x, ‖b x • h x‖ₑ ∂μ ≤ ENNReal.ofReal C * ∫⁻ x, ‖h x‖ₑ ∂μ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun x ↦ ?_
        rw [enorm_smul]
        gcongr
        simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (hC x)
    _ ≤ ENNReal.ofReal C * eLpNorm h 1 μ := by gcongr; exact lintegral_enorm_le_eLpNorm_one

end Limits

/-! ### Derivatives of a convolution -/

section ConvolutionDeriv

variable {E E₁ E₂ V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {L : E₁ →L[ℝ] E₂ →L[ℝ] V} {g : E → E₂}

/-- Differentiating a convolution in a fixed direction moves the derivative onto the `C¹`,
compactly supported factor. This is `HasCompactSupport.hasFDerivAt_convolution_left` with the
`ContinuousLinearMap.precompL` bookkeeping unwound by evaluating at a direction. -/
theorem LocallyIntegrable.fderiv_convolution_left_apply
    (hg : LocallyIntegrable g μ) {φ : E → E₁} (hcφ : HasCompactSupport φ) (hφ : ContDiff ℝ 1 φ)
    (x v : E) :
    fderiv ℝ (φ ⋆[L, μ] g) x v = ((fun t ↦ fderiv ℝ φ t v) ⋆[L, μ] g) x := by
  rw [(hcφ.hasFDerivAt_convolution_left L hφ hg x).fderiv]
  have hex : ConvolutionExistsAt (fderiv ℝ φ) g x (L.precompL E) μ :=
    HasCompactSupport.convolutionExists_left _ (hcφ.fderiv ℝ) (hφ.continuous_fderiv one_ne_zero)
      hg x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex, convolution_def]
  rfl

open scoped ContDiff in
/-- Differentiating a convolution `n` times along a tuple of directions moves all `n` derivatives
onto the smooth, compactly supported factor. The induction peels the directions off the front of
the tuple with `ContDiff.iteratedFDeriv_succ_apply_left'`, so that no reversal of the tuple
appears. -/
theorem LocallyIntegrable.iteratedFDeriv_convolution_left_apply (hg : LocallyIntegrable g μ) :
    ∀ (n : ℕ) {φ : E → E₁}, HasCompactSupport φ → ContDiff ℝ ∞ φ → ∀ (x : E) (y : Fin n → E),
      _root_.iteratedFDeriv ℝ n (φ ⋆[L, μ] g) x y
        = ((fun z ↦ _root_.iteratedFDeriv ℝ n φ z y) ⋆[L, μ] g) x := by
  intro n
  induction n with
  | zero => intro φ _ _ x y; simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro φ hcφ hφ x y
    have hconv : ContDiff ℝ ∞ (φ ⋆[L, μ] g) := hcφ.contDiff_convolution_left L hφ hg
    set ψ : E → E₁ := fun t ↦ fderiv ℝ φ t (y 0) with hψ
    have hψc : ContDiff ℝ ∞ ψ := (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hψs : HasCompactSupport ψ := hcφ.fderiv_apply ℝ (y 0)
    have hfun : (fun z ↦ fderiv ℝ (φ ⋆[L, μ] g) z (y 0)) = ψ ⋆[L, μ] g :=
      funext fun z ↦ hg.fderiv_convolution_left_apply hcφ (hφ.of_le (by simp)) z (y 0)
    rw [hconv.iteratedFDeriv_succ_apply_left' n y x, hfun, ih hψs hψc x (Fin.tail y)]
    exact congrArg (fun h ↦ (h ⋆[L, μ] g) x)
      (funext fun z ↦ (hφ.iteratedFDeriv_succ_apply_left' n y z).symm)

/-- A convolution against a compactly supported continuous function only sees the other factor on
the closed ball whose radius is that of the support, so it exists as soon as that factor is
locally integrable on an open set containing the ball. -/
theorem LocallyIntegrableOn.convolutionExistsAt {U : Set E}
    (hg : LocallyIntegrableOn g U μ) {φ : E → E₁} (hφ : Continuous φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ U) :
    ConvolutionExistsAt φ g x L μ := by
  have hcφ : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 ε) isClosed_closure hsupp
  set g' : E → E₂ := (closedBall x ε).indicator g with hg'
  have hg'loc : LocallyIntegrable g' μ :=
    ((hg.integrableOn_compact_subset hx (isCompact_closedBall x ε)).integrable_indicator
      measurableSet_closedBall).locallyIntegrable
  refine (HasCompactSupport.convolutionExists_left L hcφ hφ hg'loc x).congr
    (Eventually.of_forall fun t ↦ ?_)
  rcases eq_or_ne (φ t) 0 with h0 | h0
  · simp [h0]
  · have ht : t ∈ closedBall (0 : E) ε := hsupp (subset_tsupport _ h0)
    have : x - t ∈ closedBall x ε := by
      simpa [mem_closedBall, dist_eq_norm] using (by simpa using ht : ‖t‖ ≤ ε)
    simp [hg', Set.indicator_of_mem this]

end ConvolutionDeriv

end MeasureTheory
