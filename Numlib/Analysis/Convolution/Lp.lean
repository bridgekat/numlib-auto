/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# $L^p$ estimates for convolutions, and $L^p$ convergence of mollification

Let $G$ be a measurable additive group with a right-invariant measure $\mu$, and let $L$ be a
continuous bilinear map. The convolution of $f$ and $g$ with respect to $L$ is $(f \star g)(x) =
\int L(f(t), g(x - t)) \, d\mu(t)$. Mathlib's `Mathlib.Analysis.Convolution` gives its pointwise
theory: existence, support, continuity, smoothness, and pointwise or almost-everywhere convergence
of $\varphi_\varepsilon \star f$ to $f$. It has no estimate of the size of a convolution in $L^p$.
This module proves these estimates and the $L^p$ convergence of mollification that follows from
them. The main estimate is **Young's convolution inequality**. Its case $L^1 \star L^p \to L^p$,
$$\|f \star g\|_p \le \|L\| \, \|f\|_1 \, \|g\|_p \qquad (1 \le p \le \infty),$$
holds for every s-finite right-invariant measure on a measurable additive group. The general form,
with $1/p + 1/q = 1 + 1/r$, needs a measure that is also invariant under negation, because its proof
integrates a reflected translate of $g$.

The module also proves Minkowski's integral inequality in a weighted and an unweighted form, the
adjoint identity $\int (f \star g) h = \int g (\check f \star h)$ with $\check f(x) = f(-x)$,
convolution with a fixed integrable kernel as a bounded operator on $L^p$, the continuity of
translation on $L^p$, and the formulas for the derivatives of a convolution. For the classical
statements, see Chapter 4 of [brezis2011functional], or E. H. Lieb and M. Loss, *Analysis*, 2nd
edition, American Mathematical Society, 2001, Chapters 2 and 4.

## Main results

* `ENNReal.rpow_lintegral_mul_le`: Jensen's inequality for $t \mapsto t^p$ against a weight $w$,
  $(\int w h)^p \le (\int w)^{p - 1} \int w h^p$.
* `ENNReal.lintegral_rpow_lintegral_mul_le`: the weighted form of Minkowski's integral inequality,
  which follows from it by Tonelli's theorem.
* `ENNReal.lintegral_rpow_lintegral_le`: Minkowski's integral inequality $\| \int H(\cdot, t) \, dt
  \|_p \le \int \|H(\cdot, t)\|_p \, dt$, for a σ-finite $\mu$.
* `MeasureTheory.eLpNorm_convolution_le` and `MeasureTheory.MemLp.convolution`: Young's inequality
  in the case $L^1 \star L^p \to L^p$, and the resulting membership $f \star g \in L^p$.
* `MeasureTheory.MemLp.ae_convolutionExistsAt`: the convolution of an $L^1$ function with an $L^p$
  function exists almost everywhere, for every $1 \le p \le \infty$.
* `MeasureTheory.Lp.convolutionCLM` and `MeasureTheory.Lp.norm_convolutionCLM_le`: convolution with
  a fixed integrable kernel $K$ is a bounded operator on $L^p$ of norm at most $\|K\|_1$.
* `MeasureTheory.integral_convolution_mul`: the adjoint identity
  $\int (f \star g) h = \int g (\check f \star h)$ for $f \in L^1$, $g \in L^p$, $h \in L^q$ with
  $1/p + 1/q = 1$.
* `MeasureTheory.eLpNorm_convolution_le_of_inv_add_inv`: Young's inequality in the general form
  $1/p + 1/q = 1 + 1/r$, for a measure that is also invariant under negation.
* `MeasureTheory.eLpNorm_convolution_lsmul_le`: Young's inequality with constant $1$ for the
  convolution of a real function with a vector-valued one.
* `MeasureTheory.MemLp.tendsto_eLpNorm_sub_translate`: translation is continuous on $L^p$:
  $\|f(\cdot - t) - f\|_p \to 0$ as $t \to 0$.
* `MeasureTheory.tendsto_eLpNorm_convolution_sub` and
  `ContDiffBump.tendsto_eLpNorm_convolution_sub`: for $f \in L^p$ with $p < \infty$ and an
  approximate identity $(\varphi_i)$, such as normalized bump functions whose outer radii tend to
  $0$, $\varphi_i \star f \to f$ in $L^p$.
* `MeasureTheory.tendsto_integral_mul_of_tendsto_eLpNorm`,
  `MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm` and
  `MeasureTheory.enorm_integral_smul_le_of_bound`: three estimates for passing to the limit in an
  integral along a sequence that converges in $L^p$.
* `MeasureTheory.LocallyIntegrable.fderiv_convolution_left_apply` and
  `MeasureTheory.LocallyIntegrable.iteratedFDeriv_convolution_left_apply`: derivatives of
  $\varphi \star g$ fall on the compactly supported factor $\varphi$, once in a fixed direction for
  a $C^1$ factor, or $n$ times along a tuple of directions for a smooth factor.
* `MeasureTheory.LocallyIntegrableOn.convolutionExistsAt`: a convolution with a continuous function
  supported in a closed ball exists as soon as the other factor is locally integrable on a set that
  contains the translated ball.

## Proof outline

The case $L^1 \star L^p \to L^p$ of Young's inequality is proved from Jensen's inequality, and not
from Minkowski's integral inequality or from reading $f \star g$ as a Bochner integral with values
in $L^p$. With the weight $w = \|f(\cdot)\|$, Jensen's inequality for the measure $w \, d\mu$ and
the convex function $t \mapsto t^p$ bounds $(\int w h)^p$ by $(\int w)^{p - 1} \int w h^p$.
Tonelli's theorem and the translation invariance of $\mu$ then finish the estimate. Jensen's
inequality itself is Hölder's inequality applied to $w h = w^{1 - 1/p} (w h^p)^{1/p}$.

The unweighted Minkowski inequality is proved by duality. Write $F^p = F^{p - 1} F$, apply Tonelli's
theorem and Hölder's inequality with the exponents $p / (p - 1)$ and $p$, and divide by
$(\int F^p)^{1 - 1/p}$. The general form of Young's inequality comes from the three-exponent Hölder
inequality applied to the splitting
$$\|f(t)\| \, \|g(x - t)\| = \big(\|f(t)\|^p \|g(x - t)\|^q\big)^{1/r} \,
  \big(\|f(t)\|^p\big)^{1/p - 1/r} \, \big(\|g(x - t)\|^q\big)^{1/q - 1/r},$$
followed by Tonelli's theorem. The $L^p$ convergence of mollification is proved from the weighted
Minkowski inequality and the continuity of translation on $L^p$, without the usual approximation by
compactly supported continuous functions. A normalized bump is a probability density concentrated
near $0$, so the weighted inequality bounds the $L^p$ error of mollification by an average of the
translation errors $\|f(\cdot - t) - f\|_p$ over the support of the bump, and these errors are
uniformly small there.

## Implementation notes

* The $L^p$ seminorm $\|f\|_p$ is `MeasureTheory.eLpNorm f p μ`, with values in $[0, \infty]$, and
  $\|L\|$ is the extended norm `‖L‖ₑ`. The convolution is `f ⋆[L, μ] g`.
* The case $L^1 \star L^p \to L^p$ needs no integrability hypothesis, only measurability. The bound
  $\|\int \cdots\| \le \int \|\cdots\|$ holds unconditionally, because a Bochner integral that does
  not converge is $0$. This is an advantage of the route through Jensen's inequality.
* The two forms of Minkowski's inequality are independent. `ENNReal.lintegral_rpow_lintegral_mul_le`
  has a weight and the factor $(\int w)^{p - 1}$, so it follows from Hölder's inequality alone. The
  mollification estimates need only this form, because they normalize the weight to $\int w = 1$.
  `ENNReal.lintegral_rpow_lintegral_le` is not a corollary of it: the weight $1$ there gives the
  factor $\nu(\beta)^{p - 1}$, which is infinite when $\nu$ is infinite. The division in its proof
  needs $\int F^p < \infty$, which `ENNReal.lintegral_rpow_le_of_truncation_le` arranges. This is
  the only reason why $\mu$ must be σ-finite there.
* `MeasureTheory.lintegral_enorm_convolution_rpow_le` is the general form of Young's inequality with
  the exponents as real numbers. Only the endpoint $r = \infty$ needs a separate proof, because
  $p = \infty$ and $q = \infty$ both force $r = \infty$. Both the splitting and the endpoint case
  integrate $t \mapsto \|g(x - t)\|$, so they need the reflection $t \mapsto x - t$ to preserve
  $\mu$. This is where `MeasureTheory.Measure.IsNegInvariant` is used, and it is why the case
  $L^1 \star L^p \to L^p$ is a separate theorem and not a special case of the general one.
* The continuity of translation on $L^p$ is read off from Mathlib's continuity of the action of
  `Gᵈᵃᵃ` on `MeasureTheory.Lp`, `MeasureTheory.Lp.instContinuousVAddDomAddAct`.
-/

open Filter Function MeasureTheory MeasureTheory.Measure Metric Topology
open ContinuousLinearMap DomAddAct
open scoped Convolution ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- Let $\mu$ be a measure on $\alpha$ and let $\nu$ be an s-finite measure on $\beta$. If $f$ is
almost-everywhere measurable on $\alpha \times \beta$ for $\mu \times \nu$, then for
$\mu$-almost every $x$ the slice $y \mapsto f(x, y)$ is almost-everywhere measurable for $\nu$.

This is the counterpart for `AEMeasurable` of `MeasureTheory.Integrable.prod_right_ae`. -/
theorem AEMeasurable.prod_right_ae {γ : Type*} [MeasurableSpace γ] [SFinite ν] {f : α × β → γ}
    (hf : AEMeasurable f (μ.prod ν)) : ∀ᵐ x ∂μ, AEMeasurable (fun y => f (x, y)) ν := by
  obtain ⟨g, hg, hfg⟩ := hf
  exact (ae_ae_of_ae_prod hfg).mono fun x hx => ⟨fun y => g (x, y), by fun_prop, hx⟩

namespace ENNReal

/-- **Hölder's inequality** for three functions. Let $f, g, h \colon \alpha \to [0, \infty]$ be
almost-everywhere measurable and let $a, b, c \ge 0$ with $a + b + c = 1$. Then
$$\int f^a g^b h^c \, d\mu \le \Big(\int f \, d\mu\Big)^a \Big(\int g \, d\mu\Big)^b \Big(\int h
  \, d\mu\Big)^c.$$

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

/-- **Jensen's inequality** for the convex function $t \mapsto t^p$ on $[0, \infty]$. Let $p \ge 1$
and let $w, h \colon \alpha \to [0, \infty]$ be almost-everywhere measurable. Then
$$\Big(\int w h \, d\mu\Big)^p \le \Big(\int w \, d\mu\Big)^{p - 1} \int w h^p \, d\mu.$$
This is the unnormalized form of the inequality "the $p$-th power of the $w$-average of $h$ is
at most the $w$-average of $h^p$", and it does not ask $\int w$ to be finite or nonzero.

The proof is Hölder's inequality applied to $w h = w^{1 - 1/p} (w h^p)^{1/p}$. -/
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

/-- A weighted form of **Minkowski's integral inequality**. Let $\mu$ and $\nu$ be s-finite, let
$p \ge 1$, let $w \colon \beta \to [0, \infty]$ be almost-everywhere measurable, and let
$H \colon \alpha \times \beta \to [0, \infty]$ be almost-everywhere measurable for
$\mu \times \nu$. Then
$$\int \Big(\int w(t) H(x, t) \, d\nu(t)\Big)^p d\mu(x) \le \Big(\int w \, d\nu\Big)^{p - 1}
  \int w(t) \int H(x, t)^p \, d\mu(x) \, d\nu(t).$$
So the $L^p$ norm of a weighted average of the functions $H(\cdot, t)$ is bounded by the
weighted average of their $L^p$ norms, up to the factor $(\int w)^{p - 1}$, which is $1$ when
$w$ is a probability density.

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

/-- **Truncation for a σ-finite measure.** Let $\mu$ be σ-finite, let $p > 0$, let
$F \colon \alpha \to [0, \infty]$ be measurable and let $c \in [0, \infty]$. Suppose that
$\int G^p \, d\mu \le c$ for every measurable $G \le F$ with $\int G^p \, d\mu < \infty$. Then
$\int F^p \, d\mu \le c$.

Capping the values of $F$ at $n$ and its support at the $n$-th set of an exhausting sequence for
$\mu$ gives an increasing sequence of such $G$ that converges pointwise to $F$, and monotone
convergence finishes the proof. This lets an argument that must divide by $\int F^p \, d\mu$,
and so needs it finite, conclude in general. -/
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

/-- The duality step of Minkowski's integral inequality. Let $\mu$ and $\nu$ be s-finite, let
$p > 1$, let $H \colon \alpha \times \beta \to [0, \infty]$ be measurable, and let
$G \colon \alpha \to [0, \infty]$ be measurable with $G(x) \le \int H(x, t) \, d\nu(t)$ for all
$x$ and $\int G^p \, d\mu < \infty$. Then
$$\int G^p \, d\mu \le \Big(\int \Big(\int H(x, t)^p \, d\mu(x)\Big)^{1/p} d\nu(t)\Big)^p.$$

Write $G^p = G^{p - 1} G$, bound the last factor by the integral above it, exchange the order of
integration and apply Hölder's inequality with the exponents $p / (p - 1)$ and $p$. This bounds
$\int G^p$ by $(\int G^p)^{1 - 1/p}$ times the right-hand side, and the finiteness of $\int G^p$
lets this factor cancel. -/
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

/-- **Minkowski's integral inequality** for a measurable integrand. Let $\mu$ be σ-finite, let $\nu$
be s-finite, let $p \ge 1$ and let $H \colon \alpha \times \beta \to [0, \infty]$ be measurable.
Then
$$\Big(\int \Big(\int H(x, t) \, d\nu(t)\Big)^p d\mu(x)\Big)^{1/p} \le \int \Big(\int H(x, t)^p
  \, d\mu(x)\Big)^{1/p} d\nu(t).$$
See `ENNReal.lintegral_rpow_lintegral_le` for the version that asks for measurability only
almost everywhere. -/
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

/-- **Minkowski's integral inequality.** Let $\mu$ be σ-finite, let $\nu$ be s-finite, let
$p \ge 1$, and let $H \colon \alpha \times \beta \to [0, \infty]$ be almost-everywhere
measurable for $\mu \times \nu$. Then
$$\Big(\int \Big(\int H(x, t) \, d\nu(t)\Big)^p d\mu(x)\Big)^{1/p} \le \int \Big(\int H(x, t)^p
  \, d\mu(x)\Big)^{1/p} d\nu(t).$$
So the $L^p$ norm of an integral is at most the integral of the $L^p$ norms.

Unlike `ENNReal.lintegral_rpow_lintegral_mul_le`, this inequality has no weight and no
compensating factor, and it is not a corollary of that inequality: the weight $1$ there gives
the factor $\nu(\beta)^{p - 1}$, which is infinite when $\nu$ is infinite. It is proved by
duality instead, and $\mu$ must be σ-finite for the truncation that the duality argument needs.
See for instance E. H. Lieb and M. Loss, *Analysis*, 2nd edition, American Mathematical Society,
2001, Section 2.4. -/
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

/-- For an almost-everywhere strongly measurable $f \colon E \to \mathbb{C}$, the square of the
$L^2$ seminorm is the integral of $|f|^2$:
$$\|f\|_2^2 = \int |f(\xi)|^2 \, d\mu(\xi).$$
-/
theorem sq_eLpNorm_two {E : Type*} [MeasurableSpace E] {f : E → ℂ}
    {μ : Measure E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 ∂μ := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm (μ := μ) (p := 2) (f := f)
    (by norm_num) (by norm_num) hf
  have h2 : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ (2 : ℕ) := fun x ↦ by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [ENNReal.toReal_ofNat, h2] at h
  exact h.symm

/-- If $\varphi \ge 0$ is integrable with $\int \varphi \, d\mu = 1$, then the Lebesgue integral
$\int |\varphi| \, d\mu$, computed in $[0, \infty]$, is $1$. -/
theorem lintegral_enorm_eq_one {φ : α → ℝ} (hφ₀ : ∀ t, 0 ≤ φ t) (hφ : Integrable φ μ)
    (hφ₁ : ∫ t, φ t ∂μ = 1) : ∫⁻ t, ‖φ t‖ₑ ∂μ = 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hφ]
  simp_rw [Real.norm_of_nonneg (hφ₀ _)]
  rw [hφ₁, ENNReal.ofReal_one]

/-! ### Young's convolution inequality in the case $L^1 \star L^p \to L^p$ -/

section Young

variable {𝕜 G E E' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  [MeasurableSpace G] [AddGroup G] {μ : Measure G}
  {f : G → E} {g : G → E'} {L : E →L[𝕜] E' →L[𝕜] F}

/-- The convolution is bounded pointwise by the convolution of the norms: for every $x$,
$$\|(f \star g)(x)\| \le \int \|L\| \, \|f(t)\| \, \|g(x - t)\| \, d\mu(t).$$
No integrability hypothesis is needed, because a Bochner integral that does not converge is $0$. -/
theorem enorm_convolution_le_lintegral_enorm (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun _ => L.le_opENorm₂ _ _)

/-- If the convolutions $f \star g$ and $f' \star g$ both exist at $x$, then $((f - f') \star
g)(x) = (f \star g)(x) - (f' \star g)(x)$. This is the version with subtraction of
`MeasureTheory.ConvolutionExistsAt.add_distrib`. -/
theorem ConvolutionExistsAt.sub_distrib {f' : G → E} {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f' g x L μ) :
    ((f - f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x - (f' ⋆[L, μ] g) x := by
  simp only [convolution_def, Pi.sub_apply, L.map_sub₂, integral_sub hfg hfg']

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [μ.IsAddRightInvariant]

/-- If $g$ is almost-everywhere strongly measurable for $\mu$, then $(x, t) \mapsto g(x - t)$ is
almost-everywhere strongly measurable for $\mu \times \mu$. This is the measurability of the
second factor of a convolution integrand. -/
theorem AEStronglyMeasurable.comp_fst_sub_snd (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun z : G × G => g (z.1 - z.2)) (μ.prod μ) :=
  (hg.mono_ac (quasiMeasurePreserving_sub_of_right_invariant μ
    μ).absolutelyContinuous).comp_measurable measurable_sub

omit [NormedSpace ℝ F] in
/-- Let $1 \le p < \infty$ and let $f$ and $g$ be almost-everywhere strongly measurable. Then the
convolution of the norms satisfies
$$\int \Big(\int \|L\| \, \|f(t)\| \, \|g(x - t)\| \, d\mu(t)\Big)^p d\mu(x) \le (\|L\| \,
  \|f\|_1)^p \, \|g\|_p^p.$$

This is the intermediate estimate of Young's inequality in the case $L^1 \star L^p \to L^p$. It
is the weighted Minkowski inequality `ENNReal.lintegral_rpow_lintegral_mul_le` with the weight
$\|L\| \, \|f(\cdot)\|$, followed by the translation invariance of $\mu$. It gives both the norm
bound `MeasureTheory.eLpNorm_convolution_le_of_ne_top` and the almost-everywhere existence
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

/-- **Young's convolution inequality** in the case $L^1 \star L^p \to L^p$ with $1 \le p < \infty$:
for almost-everywhere strongly measurable $f$ and $g$, $\|f \star g\|_p \le \|L\| \, \|f\|_1 \,
\|g\|_p$. -/
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
/-- If $f$ is almost-everywhere strongly measurable, then for every $x$,
$$\int \|L\| \, \|f(t)\| \, \|g(x - t)\| \, d\mu(t) \le \|L\| \, \|f\|_1 \, \|g\|_\infty,$$
where $\|g\|_\infty$ is the essential supremum of $\|g\|$. This is the case $L^1 \star L^\infty$
of Young's inequality before the essential supremum is taken. -/
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

/-- **Young's convolution inequality** in the case $L^1 \star L^\infty \to L^\infty$: if $f$ is
almost-everywhere strongly measurable, then $\|f \star g\|_\infty \le \|L\| \, \|f\|_1 \,
\|g\|_\infty$, where $\|\cdot\|_\infty$ is the essential supremum of the norm. -/
theorem eLpNormEssSup_convolution_le (hf : AEStronglyMeasurable f μ) :
    eLpNormEssSup (f ⋆[L, μ] g) μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNormEssSup g μ := by
  rw [eLpNormEssSup]
  refine essSup_le_of_ae_le _ (Eventually.of_forall fun x => ?_)
  exact (enorm_convolution_le_lintegral_enorm x).trans
    (lintegral_enorm_mul_enorm_sub_le_eLpNormEssSup L hf x)

/-- **Young's convolution inequality** in the case $L^1 \star L^p \to L^p$. Let $G$ be a measurable
additive group with an s-finite right-invariant measure $\mu$, let $1 \le p \le \infty$, and let
$f$ and $g$ be almost-everywhere strongly measurable. Then
$$\|f \star g\|_p \le \|L\| \, \|f\|_1 \, \|g\|_p.$$

Only measurability is assumed. Where the convolution does not exist, it is $0$, and the bound
holds there trivially. -/
theorem eLpNorm_convolution_le (hp : 1 ≤ p) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) p μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · rw [eLpNorm_exponent_top (hf.convolution L hg), eLpNorm_exponent_top hg]
    exact eLpNormEssSup_convolution_le hf
  · exact eLpNorm_convolution_le_of_ne_top hp hp' hf hg

/-- If $f \in L^1$, $g \in L^p$ and $1 \le p \le \infty$, then $f \star g \in L^p$. So $L^p$ is a
module over $L^1$ under convolution. -/
theorem MemLp.convolution (hp : 1 ≤ p) (hf : MemLp f 1 μ) (hg : MemLp g p μ) :
    MemLp (f ⋆[L, μ] g) p μ := by
  refine lt_of_le_of_lt
    (eLpNorm_convolution_le hp hf.aestronglyMeasurable hg.aestronglyMeasurable) ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp [enorm_lt_top]) hf.eLpNorm_lt_top)
    hg.eLpNorm_lt_top

omit [NormedSpace ℝ F] in
/-- **The convolution of an $L^1$ function with an $L^p$ function exists almost everywhere.** Let
$f \in L^1$, $g \in L^p$ and $1 \le p \le \infty$. Then for almost every $x$, the function
$t \mapsto L(f(t), g(x - t))$ is integrable.

This is the first sentence of Theorem 4.15 of [brezis2011functional]. Mathlib has the case
$p = 1$ (`MeasureTheory.Integrable.ae_convolution_exists`). For $p < \infty$, the $p$-th moment
of the convolution of the norms is finite by
`MeasureTheory.lintegral_rpow_lintegral_enorm_mul_enorm_sub_le`, so this convolution is finite
almost everywhere. For $p = \infty$, it is bounded everywhere. -/
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
/-- Translating a convolution translates its first factor: for all $x, h \in G$,
$$(f \star g)(x + h) = (f(\cdot + h) \star g)(x).$$
-/
theorem convolution_apply_add_right (x h : G) :
    (f ⋆[L, μ] g) (x + h) = ((fun t => f (t + h)) ⋆[L, μ] g) x := by
  simp only [convolution_def]
  rw [← integral_add_right_eq_self (fun t => L (f t) (g (x + h - t))) h]
  simp only [add_sub_add_right_eq_sub]

/-- **Young's convolution inequality** for the convolution of a real function $\varphi$ with a
vector-valued function $h$, with constant $1$: if $1 \le p \le \infty$ and $\varphi$ and $h$ are
almost-everywhere strongly measurable, then
$$\|\varphi \star h\|_p \le \|\varphi\|_1 \, \|h\|_p.$$
-/
theorem eLpNorm_convolution_lsmul_le {φ : G → ℝ} {h : G → F} (hp : 1 ≤ p)
    (hφ : AEStronglyMeasurable φ μ) (hh : AEStronglyMeasurable h μ) :
    eLpNorm (φ ⋆[lsmul ℝ ℝ, μ] h) p μ ≤ eLpNorm φ 1 μ * eLpNorm h p μ := by
  refine (eLpNorm_convolution_le hp hφ hh).trans ?_
  calc ‖(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)‖ₑ * eLpNorm φ 1 μ * eLpNorm h p μ
      ≤ 1 * eLpNorm φ 1 μ * eLpNorm h p μ := by gcongr; exact opENorm_lsmul_le
    _ = eLpNorm φ 1 μ * eLpNorm h p μ := by rw [one_mul]

end Young

/-! ### Convolution with a fixed kernel as an operator on $L^p$ -/

section ConvolutionCLM

variable {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant] [NormedSpace ℝ F] {K : G → ℝ}

variable (F p) in
/-- **Convolution with a fixed integrable kernel.** Let $G$ be a measurable additive group with an
s-finite right-invariant measure $\mu$, let $1 \le p \le \infty$, and let
$K \colon G \to \mathbb{R}$ be integrable. The map $f \mapsto K \star f$ is a bounded linear
operator on $L^p(G, F)$ of norm at most $\|K\|_1$.

This is the operator of convolution with a fixed kernel in Corollary 4.28 of
[brezis2011functional]. Its values are in $L^p$ by Young's inequality
(`MeasureTheory.MemLp.convolution`). It is linear because the convolution is linear in its
second factor wherever the integral exists, which is almost everywhere
(`MeasureTheory.MemLp.ae_convolutionExistsAt`). Its norm bound is
`MeasureTheory.eLpNorm_convolution_lsmul_le`. -/
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

/-- The operator `MeasureTheory.Lp.convolutionCLM` maps $f$ to a function that is equal to
$K \star f$ almost everywhere. -/
theorem Lp.coeFn_convolutionCLM [Fact (1 ≤ p)] (hK : Integrable K μ) (f : Lp F p μ) :
    ⇑(Lp.convolutionCLM F p hK f) =ᵐ[μ] K ⋆[lsmul ℝ ℝ, μ] f :=
  MemLp.coeFn_toLp
    ((memLp_one_iff_integrable.2 hK).convolution (L := lsmul ℝ ℝ) Fact.out (Lp.memLp f))

/-- The operator norm of convolution with $K$ on $L^p$ is at most $\|K\|_1$. This is in Corollary
4.28 and Exercise 4.32 of [brezis2011functional]. -/
theorem Lp.norm_convolutionCLM_le [Fact (1 ≤ p)] (hK : Integrable K μ) :
    ‖Lp.convolutionCLM F p hK‖ ≤ (eLpNorm K 1 μ).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- **Young's inequality on $L^p$**: for $f \in L^p$, $\|K \star f\|_p \le \|K\|_1 \, \|f\|_p$. -/
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

/-- Let $G$ be an additive group with a measure $\mu$ that is invariant under right translation and
under negation. Then for every $x \in G$ the reflection $t \mapsto x - t$ preserves $\mu$.

This is the counterpart of `MeasureTheory.measurePreserving_sub_left`, which assumes left
invariance instead of right invariance. -/
theorem measurePreserving_sub_left_of_isAddRightInvariant (μ : Measure G) [μ.IsAddRightInvariant]
    [μ.IsNegInvariant] (x : G) : MeasurePreserving (fun t => x - t) μ μ := by
  have h := (measurePreserving_neg μ).comp (measurePreserving_sub_right μ x)
  simpa [Function.comp_def, neg_sub] using h

/-- If $g$ is almost-everywhere strongly measurable, then $\|g(x - \cdot)\|_p = \|g\|_p$ for every
$x$. -/
theorem eLpNorm_comp_sub_left (hg : AEStronglyMeasurable g μ) (x : G) :
    eLpNorm (fun t => g (x - t)) p μ = eLpNorm g p μ :=
  eLpNorm_comp_measurePreserving hg (measurePreserving_sub_left_of_isAddRightInvariant μ x)

/-- For every function $h \colon G \to [0, \infty]$ and every $x \in G$, $\int h(x - t) \, d\mu(t) =
\int h(t) \, d\mu(t)$. No measurability is needed.

This is the counterpart of `MeasureTheory.lintegral_sub_left_eq_self`, which assumes left
invariance instead of right invariance. -/
theorem lintegral_sub_left_eq_self_of_isAddRightInvariant (h : G → ℝ≥0∞) (x : G) :
    ∫⁻ t, h (x - t) ∂μ = ∫⁻ t, h t ∂μ :=
  calc ∫⁻ t, h (x - t) ∂μ = ∫⁻ t, (fun s => h (-s)) (t - x) ∂μ := by simp_rw [neg_sub]
    _ = ∫⁻ t, h (-t) ∂μ := lintegral_sub_right_eq_self (fun s => h (-s)) x
    _ = ∫⁻ t, h t ∂μ := lintegral_neg_eq_self h

variable [SFinite μ]

/-- The analytic core of Young's convolution inequality in its general form, with real exponents.
Let $P, Q \ge 1$ and $R > 0$ with $1/P + 1/Q = 1 + 1/R$, and let $f$ and $g$ be
almost-everywhere strongly measurable. Then
$$\int \|(f \star g)(x)\|^R \, d\mu(x) \le \|L\|^R \Big(\int \|f\|^P \, d\mu\Big)^{R/P}
  \Big(\int \|g\|^Q \, d\mu\Big)^{R/Q}.$$

The proof applies the three-exponent Hölder inequality `ENNReal.lintegral_mul_mul_norm_pow_le`
to the splitting
$$\|f(t)\| \, \|g(x - t)\| = \big(\|f(t)\|^P \|g(x - t)\|^Q\big)^{1/R} \,
  \big(\|f(t)\|^P\big)^{1/P - 1/R} \, \big(\|g(x - t)\|^Q\big)^{1/Q - 1/R},$$
followed by Tonelli's theorem. Both the $Q$-th moment of the reflected translate $g(x - \cdot)$
and the exchange of the two integrals use the invariance of $\mu$. -/
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

/-- **Young's convolution inequality** in the case $r = \infty$, that is, for Hölder conjugate
exponents $p$ and $q$ with $1/p + 1/q = 1$: if $f$ and $g$ are almost-everywhere strongly
measurable, then $\|f \star g\|_\infty \le \|L\| \, \|f\|_p \, \|g\|_q$. So the convolution of
an $L^p$ function with an $L^q$ function is essentially bounded. -/
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

/-- **Young's convolution inequality** in its general form for $r < \infty$: if $p, q \ge 1$,
$1/p + 1/q = 1 + 1/r$, and $f$ and $g$ are almost-everywhere strongly measurable, then $\|f
\star g\|_r \le \|L\| \, \|f\|_p \, \|g\|_q$. -/
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

/-- **Young's convolution inequality.** Let $G$ be a measurable additive group with an s-finite
measure $\mu$ that is invariant under right translation and under negation. Let
$1 \le p, q \le \infty$ and let $r$ satisfy $1/p + 1/q = 1 + 1/r$. If $f$ and $g$ are
almost-everywhere strongly measurable, then
$$\|f \star g\|_r \le \|L\| \, \|f\|_p \, \|g\|_q.$$

The invariance under negation is needed because the proof integrates $t \mapsto \|g(x - t)\|$,
so the reflection $t \mapsto x - t$ must preserve $\mu$. The case $q = 1$, $r = p$ is
`MeasureTheory.eLpNorm_convolution_le`, which is proved separately because it does not need this
hypothesis. See for instance E. H. Lieb and M. Loss, *Analysis*, 2nd edition, American
Mathematical Society, 2001, Section 4.2. -/
theorem eLpNorm_convolution_le_of_inv_add_inv {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rcases eq_or_ne r ∞ with rfl | hr
  · rw [eLpNorm_exponent_top (hf.convolution L hg)]
    exact eLpNormEssSup_convolution_le_of_inv_add_inv (by simpa using hpqr) hf hg
  · exact eLpNorm_convolution_le_of_inv_add_inv_of_ne_top hp hq hr hpqr hf hg

/-- **The adjoint identity for the convolution.** Let $G$ be a measurable additive group with an
s-finite measure $\mu$ that is invariant under right translation and under negation, and let
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Let $p$ and $q$ be Hölder conjugate exponents, and
let $f \in L^1$, $g \in L^p$ and $h \in L^q$ be functions $G \to \mathbb{K}$. Then, with
$\check f(x) = f(-x)$,
$$\int (f \star g)(x) \, h(x) \, d\mu(x) = \int g(y) \, (\check f \star h)(y) \, d\mu(y).$$

This is Proposition 4.16 of [brezis2011functional]. The convolutions are taken for
multiplication in $\mathbb{K}$. The function $(x, t) \mapsto f(t) g(x - t) h(x)$ is integrable
on $G \times G$ by Young's and Hölder's inequalities, and the identity is Fubini's theorem for
it after the measure-preserving change of variables $(x, t) \mapsto (x - t, -t)$. -/
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


/-! ### Continuity of translation on $L^p$ -/

section Translation

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure] {f : G → F}

/-- **Continuity of translation on $L^p$.** Let $G$ be a finite-dimensional real normed space with a
Haar measure $\mu$, let $1 \le p < \infty$ and let $f \in L^p$. Then
$$\|f(\cdot - t) - f\|_p \to 0 \quad \text{as } t \to 0.$$

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

/-! ### Convergence of mollification in $L^p$ -/

section Mollifier

variable {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure G} {f : G → F} {φ : G → ℝ}

/-- Let $\varphi$ be integrable with $\int \varphi \, d\mu = 1$, and let the convolution
$\varphi \star f$ exist at $x$. Then
$$\|(\varphi \star f)(x) - f(x)\| \le \int |\varphi(t)| \, \|f(x - t) - f(x)\| \, d\mu(t).$$
So at $x$, the mollification error is bounded by a $|\varphi|$-average of the translation
errors. -/
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

/-- Let $G$ be a finite-dimensional real normed space with a Haar measure $\mu$, let
$1 \le p < \infty$, let $f \in L^p$, and let $\varphi \ge 0$ be integrable with
$\int \varphi \, d\mu = 1$. Then
$$\|\varphi \star f - f\|_p^p \le \int \varphi(t) \, \|f(\cdot - t) - f\|_p^p \, d\mu(t).$$
So the $L^p$ error of mollification is bounded by the $\varphi$-average of the $p$-th powers of
the translation errors. -/
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

/-- **Mollification by an approximate identity converges in $L^p$.** Let $G$ be a finite-dimensional
real normed space with a Haar measure $\mu$, let $1 \le p < \infty$ and let $f \in L^p(\mu)$.
Let $(\varphi_i)$ be a family of real functions indexed along a filter $l$ such that, eventually
along $l$, $\varphi_i \ge 0$, $\varphi_i$ is integrable and $\int \varphi_i \, d\mu = 1$, and
such that the supports of the $\varphi_i$ shrink to $0$: for every neighbourhood $U$ of $0$,
eventually $\operatorname{supp} \varphi_i \subseteq U$. Then
$$\|\varphi_i \star f - f\|_p \to 0 \quad \text{along } l.$$

This is Theorem 4.22 of [brezis2011functional]. The support hypothesis is the one of
`MeasureTheory.convolution_tendsto_right`: `Tendsto (fun i => support (φ i)) l (𝓝 0).smallSets`.
The $L^p$ error is bounded by the $\varphi_i$-average of the translation errors
(`MeasureTheory.eLpNorm_convolution_sub_rpow_le`). These are uniformly small on the support of
$\varphi_i$ once it lies in a small enough ball, by the continuity of translation
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

/-- **Mollification converges in $L^p$.** Let $G$ be a finite-dimensional real normed space with a
Haar measure $\mu$, let $1 \le p < \infty$ and let $f \in L^p(\mu)$. Let $(\varphi_i)$ be a
family of bump functions about $0$, indexed along a filter $l$, whose outer radii tend to $0$
along $l$. Then the mollifications by the normalized bump functions tend to $f$ in $L^p(\mu)$:
$$\|\tilde\varphi_i \star f - f\|_p \to 0, \qquad \tilde\varphi_i = \varphi_i \Big/ \int
  \varphi_i \, d\mu.$$

The normalized bump function $\tilde\varphi_i$ is `(φ i).normed μ`. This is the $L^p$
counterpart of `ContDiffBump.convolution_tendsto_right`, which gives pointwise convergence for a
continuous $f$. It is the case of `MeasureTheory.tendsto_eLpNorm_convolution_sub` in which the
approximate identity consists of normalized bump functions. -/
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

/-!
### Limits of $L^p$ pairings

Three estimates for passing to the limit in an integral along a sequence that converges in $L^p$:
Hölder's inequality in the limit, the comparison of $L^1$ with $L^p$ for a finite measure, and the
bound of an integral against a bounded scalar factor.
-/

section Limits

/-- **Hölder's inequality in the limit.** Let $p$ and $q$ be Hölder conjugate exponents, let
$a_j, a_0 \in L^p$ and $b \in L^q$ be real functions, and let $\|a_j - a_0\|_p \to 0$. Then
$$\int b \, a_j \, d\mu \to \int b \, a_0 \, d\mu.$$
-/
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

/-- Let $\mu$ be a finite measure, let $p \ge 1$, and let $(h_j)$ be almost-everywhere strongly
measurable functions with $\|h_j\|_p \to 0$. Then $\|h_j\|_1 \to 0$. The loss in the comparison
of the two norms is a power of the total mass of $\mu$. -/
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

/-- Let $b$ be a real function with $|b(x)| \le C$ for all $x$, and let $h$ be a function with
values in a real normed space. Then
$$\Big\| \int b(x) \, h(x) \, d\mu(x) \Big\| \le C \, \|h\|_1.$$
The factor $C$ enters as `ENNReal.ofReal C`. No integrability is assumed. -/
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

/-- Let $E$ be a finite-dimensional real normed space with a Haar measure $\mu$, let $g$ be locally
integrable, and let $\varphi$ be a $C^1$ function with compact support. Then for all
$x, v \in E$,
$$D(\varphi \star g)(x)\,v = \big((t \mapsto D\varphi(t)\,v) \star g\big)(x).$$
So differentiating a convolution in a fixed direction moves the derivative onto the compactly
supported factor.

This is `HasCompactSupport.hasFDerivAt_convolution_left` with the `ContinuousLinearMap.precompL`
bookkeeping removed by evaluation at a direction. -/
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
/-- Let $E$ be a finite-dimensional real normed space with a Haar measure $\mu$ and let $g$ be
locally integrable. Then for every $n$, every smooth function $\varphi$ with compact support,
every $x \in E$ and every tuple of directions $y = (y_1, \dots, y_n)$,
$$D^n(\varphi \star g)(x)\,y = \big((z \mapsto D^n\varphi(z)\,y) \star g\big)(x).$$
So differentiating a convolution $n$ times moves all $n$ derivatives onto the smooth, compactly
supported factor.

The derivatives are Mathlib's `iteratedFDeriv`. The induction takes the directions off the front
of the tuple with `ContDiff.iteratedFDeriv_succ_apply_left'`, so that the tuple is never
reversed. That step uses the symmetry of the second derivative, and this is why $\varphi$ must
be smooth here, while `MeasureTheory.LocallyIntegrable.fderiv_convolution_left_apply` needs only
a $C^1$ factor. -/
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

/-- Let $E$ be a finite-dimensional real normed space with a Haar measure $\mu$, let
$U \subseteq E$, let $g$ be locally integrable on $U$, and let $\varphi$ be continuous with
$\operatorname{supp} \varphi \subseteq \overline{B}(0, \varepsilon)$. If
$\overline{B}(x, \varepsilon) \subseteq U$, then the convolution $\varphi \star g$ exists at
$x$.

The convolution at $x$ sees $g$ only on the closed ball $\overline{B}(x, \varepsilon)$. The
support of $\varphi$ is its closed support `tsupport φ`. The set $U$ need not be open. -/
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
