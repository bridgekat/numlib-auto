/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The Laplace transform

Let $E$ be a complex normed space and $f : \mathbb{R} \to E$. The Laplace transform of $f$ is
$$\mathcal{L}[f](s) = \int_0^\infty e^{-st} f(t)\,dt, \qquad s \in \mathbb{C},$$
taken in the conditional (improper) sense of the textbooks: the limit of the truncated integrals
$\int_0^T$ as $T \to \infty$. This file defines the transform, its region of convergence and its
abscissa of convergence. It proves that convergence at $s_0$ implies convergence on the half-plane
$\operatorname{Re} s > \operatorname{Re} s_0$, the relation to the Fourier transform, the transforms
of the unit step and of a derivative, and the transform of a sample-and-hold function. It also
defines the Z-transform of a sampled sequence and identifies it with the discrete Laplace transform.
The material is [quarteroni2000numerical], §10.11.3–10.11.4 (Definitions 10.2–10.3, Property 10.4,
Examples 10.8–10.9). The convergence theory follows D. V. Widder, *The Laplace Transform*, Chapter
II.

## Main definitions

* `LaplaceTransform.truncated`: the truncated Laplace integral $\int_0^T e^{-st} f(t)\,dt$.
* `LaplaceTransform.Converges`: the Laplace integral converges at $s$, that is, the truncated
  integrals have a limit as $T \to \infty$.
* `LaplaceTransform.laplaceTransform`: that limit, the Laplace transform $\mathcal{L}[f](s)$, and
  $0$ where the integral does not converge.
* `LaplaceTransform.abscissaOfConvergence`: the infimum $\lambda \in [-\infty, \infty]$ of the real
  parts of the points at which the Laplace integral converges.
* `zTransform`: the Z-transform $Z(z) = \sum_{n \ge 0} f(n\Delta t) z^{-n}$ of the samples of $f$.

## Main results

* `LaplaceTransform.laplaceTransform_eq_integral`: under absolute convergence, the transform is the
  Lebesgue integral over $(0, \infty)$.
* `LaplaceTransform.integrableOn_of_re_le`: absolute convergence at $s_0$ implies absolute
  convergence at every $s$ with $\operatorname{Re} s \ge \operatorname{Re} s_0$.
* `LaplaceTransform.converges_of_re_lt`: Property 10.4 of [quarteroni2000numerical], convergence at
  $s_0$ implies convergence at every $s$ with $\operatorname{Re} s > \operatorname{Re} s_0$.
* `LaplaceTransform.converges_of_abscissaOfConvergence_lt`: the Laplace integral converges on the
  open half-plane $\operatorname{Re} s > \lambda$.
* `LaplaceTransform.laplaceTransform_eq_fourier`: $\mathcal{L}[f](\sigma + i\omega) =
  \mathcal{F}(e^{-\sigma t} \tilde f)(\omega/2\pi)$, with $\tilde f$ the extension of $f$ by zero.
* `LaplaceTransform.laplaceTransform_indicator_Ioi`, `LaplaceTransform.converges_indicator_Ioi_iff`:
  Example 10.8, the unit step has transform $1/s$, and its integral converges exactly when
  $\operatorname{Re} s > 0$.
* `LaplaceTransform.laplaceTransform_deriv`: Example 10.9, $\mathcal{L}[y'](s) =
  s\,\mathcal{L}[y](s) - y(0)$.
* `LaplaceTransform.laplaceTransform_stepFun`: the transform of the sample-and-hold function $f_0$
  is $\frac{1 - e^{-s\Delta t}}{s} \sum_{n \ge 0} f(n\Delta t) e^{-ns\Delta t}$.
* `summable_zTransform`: the Cauchy–Hadamard root test for the Z-transform.
* `zTransform_eq_discreteLaplace`: the Z-transform at $z = e^{s\Delta t}$ is the discrete Laplace
  transform $\sum_{n \ge 0} f(n\Delta t) e^{-ns\Delta t}$.

## Proof outline

For Property 10.4, let $\varphi(T) = \int_0^T e^{-s_0 t} f(t)\,dt$, which is continuous, bounded and
convergent. Widder's integration by parts against $\varphi$ writes $\int_0^T e^{-st} f$ as
$e^{-\delta T} \varphi(T) + \delta \int_0^T e^{-\delta t} \varphi(t)\,dt$ with $\delta = s - s_0$,
and both terms converge when $\operatorname{Re} \delta > 0$. Since $f$ is only locally integrable,
the integration by parts (`LaplaceTransform.integral_smul_eq_smul_integral_sub`) is proved with
absolutely continuous functions and the Lebesgue differentiation theorem.

## Implementation notes

* Mathlib has no Laplace transform. The closest object is the Mellin transform in
  `Mathlib.Analysis.MellinTransform`, which is an absolutely convergent Bochner integral. The
  substitution $t = e^{-u}$ that relates the two is not used here, because Property 10.4 is about
  conditional convergence.
* The transform takes the junk value $0$ where the Laplace integral does not converge.
* The abscissa of convergence is an extended real number (`EReal`): $+\infty$ when the integral
  converges nowhere, and $-\infty$ when it converges at points of arbitrarily negative real part.
* [quarteroni2000numerical], §10.11.4, prints the substitution between the Z-transform and the
  discrete Laplace transform as $z = e^{-s\Delta t}$. With $Z(z) = \sum f(n\Delta t) z^{-n}$, the
  correct substitution is $z = e^{s\Delta t}$, which `zTransform_eq_discreteLaplace` uses.
-/

open MeasureTheory Filter Function Topology Complex Set

open scoped FourierTransform

namespace LaplaceTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Definitions -/

/-- The **truncated Laplace integral**: for a complex normed space $E$, a function
$f : \mathbb{R} \to E$, $s \in \mathbb{C}$ and $T \in \mathbb{R}$,
$$\int_0^T e^{-st} f(t)\,dt.$$

For $T < 0$ this is the oriented integral $-\int_T^0$. -/
noncomputable def truncated (f : ℝ → E) (s : ℂ) (T : ℝ) : E :=
  ∫ t in (0 : ℝ)..T, Complex.exp (-(s * t)) • f t

/-- The defining formula of `LaplaceTransform.truncated`: the truncated integral at $T$ is
$\int_0^T e^{-st} f(t)\,dt$. -/
theorem truncated_def (f : ℝ → E) (s : ℂ) (T : ℝ) :
    truncated f s T = ∫ t in (0 : ℝ)..T, Complex.exp (-(s * t)) • f t := rfl

/-- The **Laplace integral converges at $s$**: there is $L \in E$ such that the truncated integrals
$\int_0^T e^{-st} f(t)\,dt$ tend to $L$ as $T \to \infty$. This is the convergence of Definition
10.2 of [quarteroni2000numerical].

This is conditional (improper) convergence. Absolute convergence, the integrability of
$t \mapsto e^{-st} f(t)$ on $(0, \infty)$, is stronger and implies it
(`LaplaceTransform.converges_of_integrableOn`). -/
def Converges (f : ℝ → E) (s : ℂ) : Prop :=
  ∃ L : E, Tendsto (truncated f s) atTop (𝓝 L)

open Classical in
/-- The **Laplace transform** of Definition 10.2 of [quarteroni2000numerical]:
$$\mathcal{L}[f](s) = \int_0^\infty e^{-st} f(t)\,dt = \lim_{T \to \infty} \int_0^T e^{-st}
  f(t)\,dt$$
where the Laplace integral converges at $s$, and $\mathcal{L}[f](s) = 0$ where it does not
converge.

The limit is chosen from `LaplaceTransform.Converges`; `LaplaceTransform.tendsto_truncated`
shows that it is the limit. Under absolute convergence the transform is the Lebesgue integral
over $(0, \infty)$ (`LaplaceTransform.laplaceTransform_eq_integral`). -/
noncomputable def laplaceTransform (f : ℝ → E) (s : ℂ) : E :=
  if h : Converges f s then h.choose else 0

/-- If the Laplace integral of $f$ converges at $s$, then the truncated integrals
$\int_0^T e^{-st} f(t)\,dt$ tend to $\mathcal{L}[f](s)$ as $T \to \infty$. -/
theorem tendsto_truncated {f : ℝ → E} {s : ℂ} (h : Converges f s) :
    Tendsto (truncated f s) atTop (𝓝 (laplaceTransform f s)) := by
  rw [laplaceTransform, dite_eq_left h]
  exact h.choose_spec

/-- If the truncated integrals $\int_0^T e^{-st} f(t)\,dt$ tend to $L$ as $T \to \infty$, then
$\mathcal{L}[f](s) = L$. -/
theorem laplaceTransform_eq_of_tendsto {f : ℝ → E} {s : ℂ} {L : E}
    (h : Tendsto (truncated f s) atTop (𝓝 L)) : laplaceTransform f s = L :=
  tendsto_nhds_unique (tendsto_truncated ⟨L, h⟩) h

/-- If the Laplace integral of $f$ does not converge at $s$, then $\mathcal{L}[f](s) = 0$. -/
theorem laplaceTransform_of_not_converges {f : ℝ → E} {s : ℂ} (h : ¬ Converges f s) :
    laplaceTransform f s = 0 := by
  rw [laplaceTransform, dite_eq_right h]

/-- If $t \mapsto e^{-st} f(t)$ is integrable on $(0, \infty)$, then the Laplace integral of $f$
converges at $s$. -/
theorem converges_of_integrableOn {f : ℝ → E} {s : ℂ}
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • f t) (Ioi 0)) : Converges f s :=
  ⟨_, intervalIntegral_tendsto_integral_Ioi 0 h tendsto_id⟩

/-- **Under absolute convergence the transform is the Lebesgue integral**: if
$t \mapsto e^{-st} f(t)$ is integrable on $(0, \infty)$, then
$$\mathcal{L}[f](s) = \int_{(0, \infty)} e^{-st} f(t)\,dt.$$

The proof uses `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`. -/
theorem laplaceTransform_eq_integral {f : ℝ → E} {s : ℂ}
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • f t) (Ioi 0)) :
    laplaceTransform f s = ∫ t : ℝ in Ioi 0, Complex.exp (-(s * t)) • f t :=
  laplaceTransform_eq_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 h tendsto_id)

/-- For $s \in \mathbb{C}$ and $t \in \mathbb{R}$, $|e^{-st}| = e^{-(\operatorname{Re} s)\,t}$. -/
theorem norm_exp_neg_mul (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-(s * t))‖ = Real.exp (-(s.re * t)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- **Absolute convergence propagates to the right**: let $s_0, s \in \mathbb{C}$ with
$\operatorname{Re} s_0 \le \operatorname{Re} s$. If $t \mapsto e^{-s_0 t} f(t)$ is integrable on
$(0, \infty)$ and $f$ is almost everywhere strongly measurable on $(0, \infty)$, then
$t \mapsto e^{-st} f(t)$ is integrable on $(0, \infty)$.

The proof uses $|e^{-st}| = e^{-(\operatorname{Re} s)\,t} \le e^{-(\operatorname{Re} s_0)\,t}$
for $t \ge 0$. -/
theorem integrableOn_of_re_le {f : ℝ → E} {s₀ s : ℂ}
    (h₀ : IntegrableOn (fun t : ℝ => Complex.exp (-(s₀ * t)) • f t) (Ioi 0))
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hs : s₀.re ≤ s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • f t) (Ioi 0) := by
  refine Integrable.mono' h₀.norm ((Continuous.aestronglyMeasurable (by fun_prop)).smul hf) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_smul, norm_smul, norm_exp_neg_mul, norm_exp_neg_mul]
  gcongr
  exact le_of_lt ht

/-- The **abscissa of convergence** $\lambda$ of Property 10.4 of [quarteroni2000numerical]: the
infimum, in the extended reals $[-\infty, \infty]$, of the real parts of the points
$s \in \mathbb{C}$ at which the Laplace integral of $f$ converges.

It is $+\infty$ when the integral converges nowhere, and $-\infty$ when it converges at points
of arbitrarily negative real part. The integral converges on the open half-plane
$\operatorname{Re} s > \lambda$ (`LaplaceTransform.converges_of_abscissaOfConvergence_lt`). -/
noncomputable def abscissaOfConvergence (f : ℝ → E) : EReal :=
  sInf ((fun s : ℂ => (s.re : EReal)) '' {s | Converges f s})

/-! ### The relation to the Fourier transform, and the unit step -/

/-- **The relation to the Fourier transform**, stated after Definition 10.2 of
[quarteroni2000numerical]: let $f : \mathbb{R} \to \mathbb{C}$ and
$s = \sigma + i\omega \in \mathbb{C}$, and suppose that $t \mapsto e^{-st} f(t)$ is integrable
on $(0, \infty)$. Then
$$\mathcal{L}[f](\sigma + i\omega) = \mathcal{F}\bigl(e^{-\sigma t} \tilde
  f\bigr)\Bigl(\frac{\omega}{2\pi}\Bigr),$$
where $\tilde f$ equals $f$ on $t > 0$ and $0$ on $t \le 0$.

Here $\mathcal{F}$ is Mathlib's Fourier transform `𝓕`, whose kernel is $e^{-2\pi i \nu t}$; this
is why the argument is $\omega/2\pi$. The source writes $\mathcal{F}(e^{-\sigma t} \tilde f)$
with no argument. -/
theorem laplaceTransform_eq_fourier {f : ℝ → ℂ} {s : ℂ}
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * f t) (Ioi 0)) :
    laplaceTransform f s =
      𝓕 (fun t : ℝ => Complex.exp (-(s.re * t)) * Set.indicator (Ioi 0) f t)
        (s.im / (2 * Real.pi)) := by
  rw [laplaceTransform_eq_integral h, Real.fourier_real_eq_integral_exp_smul,
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  by_cases ht : t ∈ Ioi 0
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, ← mul_assoc, ← Complex.exp_add]
    congr 2
    have hre : -2 * Real.pi * t * (s.im / (2 * Real.pi)) = -(t * s.im) := by
      field_simp
    rw [hre]
    apply Complex.ext <;> simp [mul_comm]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero, mul_zero]

/-- **The Laplace transform of the unit step**, Example 10.8 of [quarteroni2000numerical]: for
$s \in \mathbb{C}$ with $\operatorname{Re} s > 0$, the indicator function
$\mathbf{1}_{(0, \infty)}$ has the transform
$$\mathcal{L}[\mathbf{1}_{(0, \infty)}](s) = \int_0^\infty e^{-st}\,dt = \frac{1}{s}.$$
-/
theorem laplaceTransform_indicator_Ioi {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t : ℝ => Set.indicator (Ioi 0) (fun _ => (1 : ℂ)) t) s = 1 / s := by
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • (Ioi 0).indicator
      (fun _ => (1 : ℂ)) t) (Ioi 0) := by
    refine (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    simp [Set.indicator_of_mem ht]
  rw [laplaceTransform_eq_integral hint]
  have := integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => Complex.exp (-s * t))
    (f := fun t : ℝ => Complex.exp (-(s * t)) • (Ioi 0).indicator (fun _ => (1 : ℂ)) t)
    (fun t ht => by simp [Set.indicator_of_mem ht]), this]
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  field_simp
  simp

/-! ### The region of convergence -/

section IBP

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let $F$ be a real normed space and $h : \mathbb{R} \to F$ be integrable on the interval between
$a$ and $b$, and let $c$ lie in that interval. Then the primitive $x \mapsto \int_c^x h$ is
absolutely continuous on the interval between $a$ and $b$.

This extends Mathlib's `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`,
which is stated for real-valued $h$, through the bound $\|\int_x^y h\| \le |\int_x^y \|h\||$. -/
theorem _root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral'
    {h : ℝ → F} {a b c : ℝ} (hh : IntervalIntegrable h volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, h v) a b := by
  have hR := hh.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  unfold AbsolutelyContinuousOnInterval at hR ⊢
  refine squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ hR
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  refine Finset.sum_le_sum fun i hi => ?_
  obtain ⟨hx, hy⟩ := hnI.1 i hi
  have hcx : IntervalIntegrable h volume c (I i).1 := hh.mono_set (uIcc_subset_uIcc hc hx)
  have hcy : IntervalIntegrable h volume c (I i).2 := hh.mono_set (uIcc_subset_uIcc hc hy)
  rw [dist_eq_norm, dist_eq_norm, intervalIntegral.integral_interval_sub_left hcx hcy,
    intervalIntegral.integral_interval_sub_left hcx.norm hcy.norm, Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

end IBP

variable [CompleteSpace E]

/-- **Integration by parts against a primitive.** Let $E$ be a complete complex normed space, let
$T \ge 0$, let $g : \mathbb{R} \to E$ be integrable on $[0, T]$, and let
$u : \mathbb{R} \to \mathbb{C}$ be differentiable with a continuous derivative $u'$. With
$\Phi(t) = \int_0^t g$,
$$\int_0^T u(t)\, g(t)\,dt = u(T)\, \Phi(T) - \int_0^T u'(t)\, \Phi(t)\,dt.$$

Since $g$ is only integrable, $\Phi$ is differentiable only almost everywhere, by the Lebesgue
differentiation theorem `IntervalIntegrable.ae_hasDerivAt_integral`. The difference of the two
sides is an absolutely continuous function of $T$ whose derivative vanishes almost everywhere.
So it is constant (`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`), and it
vanishes at $0$. -/
theorem integral_smul_eq_smul_integral_sub {g : ℝ → E} {u u' : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hg : IntervalIntegrable g volume 0 T) (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') :
    ∫ t in (0 : ℝ)..T, u t • g t
      = u T • (∫ t in (0 : ℝ)..T, g t)
        - ∫ t in (0 : ℝ)..T, u' t • (∫ r in (0 : ℝ)..t, g r) := by
  set Φ : ℝ → E := fun x => ∫ r in (0 : ℝ)..x, g r with hΦ
  have hucont : Continuous u := continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt
  have huC1 : ContDiff ℝ 1 u := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hu x).differentiableAt.restrictScalars ℝ, ?_⟩
    have : deriv u = u' := funext fun x => (hu x).deriv
    rw [this]
    exact hu'
  -- the four absolutely continuous pieces
  have hΦ_ac : AbsolutelyContinuousOnInterval Φ 0 T :=
    hg.absolutelyContinuousOnInterval_intervalIntegral' (by simp)
  have hΦ_cont : ContinuousOn Φ (uIcc 0 T) :=
    intervalIntegral.continuousOn_primitive_interval' hg (by simp)
  have hu_ac : AbsolutelyContinuousOnInterval u 0 T :=
    (huC1.contDiffOn (s := uIcc 0 T)).absolutelyContinuousOnInterval
  have hug : IntervalIntegrable (fun t => u t • g t) volume 0 T :=
    hg.continuousOn_smul hucont.continuousOn
  have hu'Φ : IntervalIntegrable (fun t => u' t • Φ t) volume 0 T :=
    (hu'.continuousOn.smul hΦ_cont).intervalIntegrable
  set Ψ : ℝ → E := fun x => (∫ t in (0 : ℝ)..x, u t • g t) - u x • Φ x
    + ∫ t in (0 : ℝ)..x, u' t • Φ t with hΨ
  have hΨ_ac : AbsolutelyContinuousOnInterval Ψ 0 T :=
    ((hug.absolutelyContinuousOnInterval_intervalIntegral' (by simp)).sub
      (hu_ac.smul hΦ_ac)).add (hu'Φ.absolutelyContinuousOnInterval_intervalIntegral' (by simp))
  -- its derivative vanishes almost everywhere on `[0, T]`
  have hΨ_deriv : ∀ᵐ x, x ∈ uIcc 0 T → HasDerivAt Ψ 0 x := by
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have hT' : ∀ᵐ x : ℝ, x ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hg.ae_hasDerivAt_integral, hug.ae_hasDerivAt_integral, h0, hT']
      with x hx1 hx2 hx0 hxT hxI
    have hxIoo : x ∈ Ioo 0 T := by
      rw [uIcc_of_le hT] at hxI
      exact ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxT⟩
    have hd1 : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, u t • g t) (u x • g x) x :=
      hx2 hxI 0 (by simp)
    have hdΦ : HasDerivAt Φ (g x) x := hx1 hxI 0 (by simp)
    have hd2 : HasDerivAt (fun y => u y • Φ y) (u x • g x + u' x • Φ x) x :=
      (hu x).smul hdΦ
    have hd3 : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, u' t • Φ t) (u' x • Φ x) x := by
      refine intervalIntegral.integral_hasDerivAt_right
        (hu'Φ.mono_set (uIcc_subset_uIcc_left
          (by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self hxIoo)))
        ?_ ?_
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          ((hu'.continuousOn.smul hΦ_cont).mono (by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self))
          x hxIoo
      · exact (hu'.continuousOn.smul hΦ_cont).continuousAt
          (by rw [uIcc_of_le hT]; exact Icc_mem_nhds hxIoo.1 hxIoo.2)
    have key : HasDerivAt Ψ (u x • g x - (u x • g x + u' x • Φ x) + u' x • Φ x) x :=
      (hd1.sub hd2).add hd3
    rw [show u x • g x - (u x • g x + u' x • Φ x) + u' x • Φ x = 0 by abel] at key
    exact key
  obtain ⟨C, hC⟩ := hΨ_ac.const_of_ae_hasDerivAt_zero hΨ_deriv
  have hΨ0 : Ψ 0 = 0 := by simp [hΨ, hΦ]
  have hΨT : Ψ T = 0 := by rw [hC T (by simp), ← hC 0 (by simp), hΨ0]
  have hΨT' : (∫ t in (0 : ℝ)..T, u t • g t) - u T • Φ T
      + ∫ t in (0 : ℝ)..T, u' t • Φ t = 0 := hΨT
  apply eq_of_sub_eq_zero
  convert hΨT' using 1
  abel

omit [CompleteSpace E] in
/-- If $f$ is locally integrable on $[0, \infty)$, then for every $s \in \mathbb{C}$ and $T \ge 0$
the integrand $t \mapsto e^{-st} f(t)$ of the Laplace integral is integrable on $[0, T]$. -/
theorem intervalIntegrable_exp_smul {f : ℝ → E} (hf : LocallyIntegrableOn f (Ici 0)) (s : ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => Complex.exp (-(s * t)) • f t) volume 0 T := by
  have h1 : IntegrableOn f (Icc 0 T) :=
    hf.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  have h2 : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr h1
  exact h2.continuousOn_smul (Continuous.continuousOn (by fun_prop))

omit [CompleteSpace E] in
/-- If $f$ is locally integrable on $[0, \infty)$, then for every $s \in \mathbb{C}$ the truncated
Laplace integral $T \mapsto \int_0^T e^{-st} f(t)\,dt$ is continuous on $[0, \infty)$. -/
theorem continuousOn_truncated {f : ℝ → E} (hf : LocallyIntegrableOn f (Ici 0)) (s : ℂ) :
    ContinuousOn (truncated f s) (Ici 0) := by
  intro x hx
  have hx' : (0 : ℝ) ≤ x := hx
  have h := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_exp_smul hf s (by linarith : (0 : ℝ) ≤ x + 1))
    (by simp : (0 : ℝ) ∈ uIcc 0 (x + 1))
  rw [uIcc_of_le (by linarith)] at h
  refine (h x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin (mem_nhdsWithin.mpr ?_)
  exact ⟨Iio (x + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, hy.1.le⟩⟩

/-- **Property 10.4 of [quarteroni2000numerical]**, first part: let $E$ be a complete complex normed
space, and let $f : \mathbb{R} \to E$ be locally integrable on $[0, \infty)$. If the Laplace
integral of $f$ converges at $s_0 \in \mathbb{C}$, then it converges at every $s \in \mathbb{C}$
with $\operatorname{Re} s > \operatorname{Re} s_0$. This is Theorem II.1 of Widder, *The Laplace
Transform*.

Let $\delta = s - s_0$ and $\varphi(T) = \int_0^T e^{-s_0 t} f(t)\,dt$, which is continuous,
bounded and convergent. Integration by parts
(`LaplaceTransform.integral_smul_eq_smul_integral_sub`) gives
$$\int_0^T e^{-st} f(t)\,dt = e^{-\delta T} \varphi(T) + \delta \int_0^T e^{-\delta t}
  \varphi(t)\,dt.$$
The first term tends to $0$, and the integral converges absolutely because $\varphi$ is bounded
and $\operatorname{Re} \delta > 0$. -/
theorem converges_of_re_lt {f : ℝ → E} (hf : LocallyIntegrableOn f (Ici 0)) {s₀ s : ℂ}
    (h₀ : Converges f s₀) (hs : s₀.re < s.re) : Converges f s := by
  obtain ⟨L, hL⟩ := h₀
  set δ : ℂ := s - s₀ with hδ
  have hδre : 0 < δ.re := by rw [hδ, Complex.sub_re]; linarith
  set φ := truncated f s₀ with hφ
  -- the derivative of the exponential weight
  have hu : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(δ * t)))
      (-δ * Complex.exp (-(δ * x))) x := by
    intro x
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(δ * z)))
        (Complex.exp (-(δ * x)) * -(δ * 1)) x :=
      ((hasDerivAt_id (x : ℂ)).const_mul δ).neg.cexp
    exact (h1.comp_ofReal).congr_deriv (by ring)
  -- the integration by parts identity, for every `T ≥ 0`
  have hIBP : ∀ T, 0 ≤ T → truncated f s T
      = Complex.exp (-(δ * T)) • φ T + δ • ∫ t in (0 : ℝ)..T, Complex.exp (-(δ * t)) • φ t := by
    intro T hT
    have hg := intervalIntegrable_exp_smul hf s₀ hT
    have key := integral_smul_eq_smul_integral_sub hT hg hu (by fun_prop)
    have hlhs : truncated f s T
        = ∫ t in (0 : ℝ)..T, Complex.exp (-(δ * t)) • (Complex.exp (-(s₀ * t)) • f t) := by
      rw [truncated_def]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [smul_smul, ← Complex.exp_add]
      congr 2
      rw [hδ]
      ring
    rw [hlhs, key]
    simp only [neg_mul, neg_smul, intervalIntegral.integral_neg, sub_neg_eq_add, mul_smul,
      intervalIntegral.integral_smul]
    rfl
  -- the boundary term tends to zero
  have hexp : Tendsto (fun T : ℝ => Complex.exp (-(δ * T))) atTop (𝓝 0) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    have : (fun T : ℝ => (-(δ * (T : ℂ))).re) = fun T => -(δ.re * T) := by
      funext T
      simp
    rw [this]
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hδre)
  have h1 : Tendsto (fun T : ℝ => Complex.exp (-(δ * T)) • φ T) atTop (𝓝 0) :=
    hexp.zero_smul_isBoundedUnder_le hL.norm.isBoundedUnder_le
  -- the remaining integral converges absolutely
  have hφcont : ContinuousOn φ (Ici 0) := continuousOn_truncated hf s₀
  obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ Ici (0 : ℝ), ‖φ t‖ ≤ C := by
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hL.norm.eventually (gt_mem_nhds (lt_add_one ‖L‖)))
    obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hφcont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) (max T₀ 0) ⊆ Ici 0))
    refine ⟨max C₁ (‖L‖ + 1), fun t ht => ?_⟩
    by_cases htT : t ≤ max T₀ 0
    · exact (hC₁ t ⟨ht, htT⟩).trans (le_max_left _ _)
    · exact (hT₀ t ((le_max_left _ _).trans (not_le.mp htT).le)).le.trans (le_max_right _ _)
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(δ * t)) • φ t) (Ioi 0) := by
    have hexpint : IntegrableOn (fun t : ℝ => C * Real.exp (-δ.re * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hδre) 0).const_mul C
    refine Integrable.mono' hexpint ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).smul
        ((hφcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_smul, norm_exp_neg_mul, neg_mul, mul_comm]
      gcongr
      exact hC t (mem_Ici.mpr (mem_Ioi.mp ht).le)
  have h2 : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, Complex.exp (-(δ * t)) • φ t) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, Complex.exp (-(δ * t)) • φ t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  refine ⟨0 + δ • ∫ t : ℝ in Ioi 0, Complex.exp (-(δ * t)) • φ t, ?_⟩
  refine (h1.add (h2.const_smul δ)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (hIBP T hT).symm

/-- **Property 10.4 of [quarteroni2000numerical]**, second part: let $E$ be a complete complex
normed space, and let $f : \mathbb{R} \to E$ be locally integrable on $[0, \infty)$. Then the
Laplace integral of $f$ converges at every $s \in \mathbb{C}$ with
$\operatorname{Re} s > \lambda$, where $\lambda$ is the abscissa of convergence of $f$.

So the integral converges on the open half-plane to the right of the abscissa of convergence,
and everywhere when $\lambda = -\infty$. -/
theorem converges_of_abscissaOfConvergence_lt {f : ℝ → E} (hf : LocallyIntegrableOn f (Ici 0))
    {s : ℂ} (hs : abscissaOfConvergence f < (s.re : EReal)) : Converges f s := by
  have hne : ((fun s : ℂ => (s.re : EReal)) '' {s | Converges f s}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [abscissaOfConvergence, h, sInf_empty] at hs
    exact not_top_lt hs
  obtain ⟨x, ⟨s₀, hs₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hs
  exact converges_of_re_lt hf hs₀ (EReal.coe_lt_coe_iff.mp hlt)

/-! ### The unit step and the transform of a derivative -/

/-- **The transform of a derivative**, Example 10.9 and (10.83) of [quarteroni2000numerical]: let
$E$ be a complete complex normed space, let $y : \mathbb{R} \to E$ be of class $C^1$, and let
$s \in \mathbb{C}$. Suppose that $t \mapsto e^{-st} y(t)$ and $t \mapsto e^{-st} y'(t)$ are
integrable on $(0, \infty)$, and that $e^{-st} y(t) \to 0$ as $t \to \infty$. Then
$$\mathcal{L}[y'](s) = s\,\mathcal{L}[y](s) - y(0).$$

The proof integrates by parts on $[0, T]$ and lets $T \to \infty$. Consequently, the solution of
$y' + ay = g$, $y(0) = y_0$, satisfies $(s + a) Y(s) = G(s) + y_0$ wherever the three transforms
converge absolutely. -/
theorem laplaceTransform_deriv {y : ℝ → E} {s : ℂ} (hy : ContDiff ℝ 1 y)
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • y t) (Ioi 0))
    (h' : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • deriv y t) (Ioi 0))
    (hlim : Tendsto (fun t : ℝ => Complex.exp (-(s * t)) • y t) atTop (𝓝 0)) :
    laplaceTransform (deriv y) s = s • laplaceTransform y s - y 0 := by
  have hu : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(s * t)))
      (-s * Complex.exp (-(s * x))) x := by
    intro x
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(s * z)))
        (Complex.exp (-(s * x)) * -(s * 1)) x :=
      ((hasDerivAt_id (x : ℂ)).const_mul s).neg.cexp
    exact (h1.comp_ofReal).congr_deriv (by ring)
  have hyd : ∀ x : ℝ, HasDerivAt y (deriv y x) x := fun x =>
    (hy.differentiable one_ne_zero x).hasDerivAt
  have hy' : Continuous (deriv y) := hy.continuous_deriv le_rfl
  -- integration by parts on `[0, T]`
  have hIBP : ∀ T : ℝ, truncated (deriv y) s T
      = Complex.exp (-(s * T)) • y T - y 0 + s • truncated y s T := by
    intro T
    rw [truncated_def, intervalIntegral.integral_smul_deriv_eq_deriv_smul (fun x _ => hu x)
      (fun x _ => hyd x) (Continuous.intervalIntegrable (by fun_prop) _ _)
      (hy'.intervalIntegrable _ _), truncated_def]
    simp only [neg_mul, neg_smul, intervalIntegral.integral_neg, sub_neg_eq_add, mul_smul,
      intervalIntegral.integral_smul]
    simp
  -- the limits
  have h1 : Tendsto (truncated (deriv y) s) atTop (𝓝 (laplaceTransform (deriv y) s)) :=
    tendsto_truncated (converges_of_integrableOn h')
  have h2 : Tendsto (fun T : ℝ => Complex.exp (-(s * T)) • y T - y 0 + s • truncated y s T)
      atTop (𝓝 (0 - y 0 + s • laplaceTransform y s)) :=
    (hlim.sub_const _).add ((tendsto_truncated (converges_of_integrableOn h)).const_smul s)
  have := tendsto_nhds_unique h1 (h2.congr fun T => (hIBP T).symm)
  rw [this]
  abel

/-- **The region of convergence of the unit step**, Example 10.8 of [quarteroni2000numerical]: for
$s \in \mathbb{C}$, the Laplace integral of $\mathbf{1}_{(0, \infty)}$ converges at $s$ if and
only if $\operatorname{Re} s > 0$. So its abscissa of convergence is $0$.

For $\operatorname{Re} s \le 0$ the truncated integral is $T$ when $s = 0$, and otherwise
$(1 - e^{-sT})/s$. Its convergence would force $e^{-sT}$ to converge to a limit $M$ with
$|M| \ge 1$. Then $e^{-sh} M = M$ for every shift $h$, so $h \mapsto e^{-sh}$ is constant, and
its derivative $-s$ at $0$ vanishes. -/
theorem converges_indicator_Ioi_iff {s : ℂ} :
    Converges (fun t : ℝ => Set.indicator (Ioi 0) (fun _ => (1 : ℂ)) t) s ↔ 0 < s.re := by
  constructor
  · rintro ⟨L, hL⟩
    by_contra hre
    rw [not_lt] at hre
    -- the truncated integrals in closed form
    have htr : ∀ T : ℝ, 0 ≤ T → truncated (fun t : ℝ => Set.indicator (Ioi 0)
        (fun _ => (1 : ℂ)) t) s T = ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) := by
      intro T hT
      rw [truncated_def]
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      rw [uIoc_of_le hT] at ht
      simp [Set.indicator_of_mem (show t ∈ Ioi 0 from ht.1)]
    by_cases hs0 : s = 0
    · -- the truncated integral is `T` itself, unbounded
      subst hs0
      have hT : Tendsto (fun T : ℝ => ‖truncated (fun t : ℝ => Set.indicator (Ioi (0 : ℝ))
          (fun _ => (1 : ℂ)) t) 0 T‖) atTop atTop := by
        refine tendsto_id.congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        rw [htr T hT]
        simp [abs_of_nonneg hT]
      exact not_tendsto_atTop_of_tendsto_nhds hL.norm hT
    · -- `e^{-sT} = 1 - s · truncated` converges, to a nonzero limit, and is periodic-like
      have hexp : Tendsto (fun T : ℝ => Complex.exp (-(s * T))) atTop (𝓝 (1 - s * L)) := by
        have h1 : Tendsto (fun T : ℝ => 1 - s * truncated (fun t : ℝ => Set.indicator (Ioi 0)
            (fun _ => (1 : ℂ)) t) s T) atTop (𝓝 (1 - s * L)) :=
          (hL.const_mul s).const_sub 1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        rw [htr T hT, integral_exp_mul_complex (neg_ne_zero.mpr hs0)]
        field_simp
        simp
      set M := 1 - s * L with hM
      -- the limit has norm at least one
      have hM1 : 1 ≤ ‖M‖ := by
        refine ge_of_tendsto hexp.norm ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        rw [norm_exp_neg_mul]
        exact Real.one_le_exp (by nlinarith)
      have hM0 : M ≠ 0 := fun h => by rw [h, norm_zero] at hM1; linarith
      -- the exponential factor `e^{-s h}` is `1` for every shift `h`
      have hshift : ∀ h : ℝ, Complex.exp (-(s * h)) = 1 := by
        intro h
        have h1 : Tendsto (fun T : ℝ => Complex.exp (-(s * (T + h)))) atTop (𝓝 M) := by
          have := hexp.comp (tendsto_atTop_add_const_right atTop h tendsto_id)
          refine this.congr fun T => ?_
          simp [Function.comp]
        have h2 : Tendsto (fun T : ℝ => Complex.exp (-(s * (T + h)))) atTop
            (𝓝 (Complex.exp (-(s * h)) * M)) := by
          refine (hexp.const_mul (Complex.exp (-(s * h)))).congr fun T => ?_
          rw [← Complex.exp_add]
          congr 1
          ring
        have := tendsto_nhds_unique h2 h1
        exact (mul_left_eq_self₀.mp this).resolve_right hM0
      -- so its derivative at `0`, which is `-s`, vanishes
      have hd : HasDerivAt (fun h : ℝ => Complex.exp (-(s * h))) (-s) 0 := by
        have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(s * z)))
            (Complex.exp (-(s * (0 : ℝ))) * -(s * 1)) ((0 : ℝ) : ℂ) :=
          ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul s).neg.cexp
        exact (h1.comp_ofReal).congr_deriv (by simp)
      have hd' : HasDerivAt (fun h : ℝ => Complex.exp (-(s * h))) 0 0 :=
        (hasDerivAt_const (0 : ℝ) (1 : ℂ)).congr_of_eventuallyEq
          (Eventually.of_forall fun h => hshift h)
      exact hs0 (neg_eq_zero.mp (hd.unique hd'))
  · intro hs
    exact converges_of_integrableOn ((integrableOn_exp_mul_complex_Ioi (a := -s)
      (by simpa using hs) 0).congr_fun (fun t ht => by simp [Set.indicator_of_mem ht])
      measurableSet_Ioi)

/-! ### The sample-and-hold function and the Z-transform -/

/-- For $\Delta t > 0$, the sampling intervals $[n\Delta t, (n + 1)\Delta t)$, $n \in \mathbb{N}$,
cover $[0, \infty)$. -/
theorem iUnion_Ico_nat_mul {Δt : ℝ} (hΔt : 0 < Δt) :
    ⋃ n : ℕ, Ico ((n : ℝ) * Δt) ((n + 1) * Δt) = Ici 0 := by
  ext t
  simp only [mem_iUnion, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨n, hn, -⟩
    exact le_trans (by positivity) hn
  · intro ht
    refine ⟨⌊t / Δt⌋₊, ?_, ?_⟩
    · rw [← le_div_iff₀ hΔt]
      exact Nat.floor_le (div_nonneg ht hΔt.le)
    · rw [← div_lt_iff₀ hΔt]
      exact Nat.lt_floor_add_one _

/-- For $\Delta t > 0$, the sampling intervals $[n\Delta t, (n + 1)\Delta t)$, $n \in \mathbb{N}$,
are pairwise disjoint. -/
theorem pairwise_disjoint_Ico_nat_mul {Δt : ℝ} (hΔt : 0 < Δt) :
    Pairwise (Disjoint on fun n : ℕ => Ico ((n : ℝ) * Δt) ((n + 1) * Δt)) := by
  intro m n hmn
  simp only [Function.onFun, Set.Ico_disjoint_Ico]
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · have : ((m : ℝ) + 1) * Δt ≤ n * Δt := by
      gcongr
      exact_mod_cast h
    exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
  · have : ((n : ℝ) + 1) * Δt ≤ m * Δt := by
      gcongr
      exact_mod_cast h
    exact (min_le_right _ _).trans (this.trans (le_max_left _ _))

/-- **The Laplace transform of the sample-and-hold function**, §10.11.4 of
[quarteroni2000numerical]: let $f : \mathbb{R} \to \mathbb{C}$, let $\Delta t > 0$, and let
$f_0(t) = f(\lfloor t/\Delta t \rfloor \Delta t)$, which equals $f(n\Delta t)$ on
$[n\Delta t, (n + 1)\Delta t)$. Let $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$, and
suppose that $\sum_{n \ge 0} |f(n\Delta t)|\, e^{-n (\operatorname{Re} s) \Delta t}$ converges.
Then
$$\mathcal{L}[f_0](s) = \frac{1 - e^{-s\Delta t}}{s} \sum_{n \ge 0} f(n\Delta t)\, e^{-ns\Delta
  t}.$$

The integral over $(0, \infty)$ splits over the sampling intervals. On the $n$-th interval
$e^{-st}$ integrates to $(e^{-ns\Delta t} - e^{-(n+1)s\Delta t})/s$. The series is the discrete
Laplace transform of $f_0$, and it is the Z-transform of the samples at $z = e^{s\Delta t}$
(`zTransform_eq_discreteLaplace`). -/
theorem laplaceTransform_stepFun {f : ℝ → ℂ} {Δt : ℝ} (hΔt : 0 < Δt) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun n : ℕ => ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt))) :
    laplaceTransform (fun t : ℝ => f (⌊t / Δt⌋ * Δt)) s
      = ((1 - Complex.exp (-(s * Δt))) / s)
        * ∑' n : ℕ, f (n * Δt) * Complex.exp (-(n * s * Δt)) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  set f₀ : ℝ → ℂ := fun t => f (⌊t / Δt⌋ * Δt) with hf₀
  set g : ℝ → ℂ := fun t => Complex.exp (-(s * t)) • f₀ t with hg
  set S : ℕ → Set ℝ := fun n => Ico ((n : ℝ) * Δt) ((n + 1) * Δt) with hS
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => measurableSet_Ico
  have hSle : ∀ n : ℕ, (n : ℝ) * Δt ≤ (n + 1) * Δt := fun n => by nlinarith
  -- on each sampling interval, `f₀` is the sample
  have hf₀_piece : ∀ n : ℕ, ∀ t ∈ S n, f₀ t = f (n * Δt) := by
    intro n t ht
    have hfl : ⌊t / Δt⌋ = (n : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor
      · rw [le_div_iff₀ hΔt]
        exact ht.1
      · rw [div_lt_iff₀ hΔt]
        exact ht.2
    simp only [hf₀, hfl, Int.cast_natCast]
  -- the integral over each sampling interval
  have hpiece : ∀ n : ℕ, ∫ t in S n, g t
      = f (n * Δt)
        * ((Complex.exp (-(s * (n * Δt))) - Complex.exp (-(s * ((n + 1) * Δt)))) / s) := by
    intro n
    rw [setIntegral_congr_fun (hSmeas n) (f := g)
      (g := fun t : ℝ => Complex.exp (-s * t) * f (n * Δt))
      (fun t ht => by simp only [hg, smul_eq_mul]; rw [hf₀_piece n t ht, neg_mul]),
      integral_mul_const, hS]
    simp only
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hSle n),
      integral_exp_mul_complex (neg_ne_zero.mpr hs0)]
    have e1 : Complex.exp (-s * ((((n : ℝ) + 1) * Δt : ℝ) : ℂ))
        = Complex.exp (-(s * ((n + 1) * Δt))) := by congr 1; push_cast; ring
    have e2 : Complex.exp (-s * (((n : ℝ) * Δt : ℝ) : ℂ))
        = Complex.exp (-(s * (n * Δt))) := by congr 1; push_cast; ring
    rw [e1, e2]
    field_simp
    ring
  -- integrability on each sampling interval, with a summable bound on the norms
  have hpiece_int : ∀ n, IntegrableOn g (S n) := by
    intro n
    refine IntegrableOn.congr_fun (f := fun t : ℝ => Complex.exp (-(s * t)) * f (n * Δt)) ?_
      (fun t ht => ?_) (hSmeas n)
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ico_subset_Icc_self
    · simp only [hg, smul_eq_mul]
      rw [hf₀_piece n t ht]
  have hnorm_piece : ∀ n, ∫ t in S n, ‖g t‖
      ≤ ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt)) * Δt := by
    intro n
    calc ∫ t in S n, ‖g t‖
        ≤ ∫ _ in S n, ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt)) := by
          refine setIntegral_mono_on (hpiece_int n).norm (integrableOn_const ?_) (hSmeas n)
            fun t ht => ?_
          · rw [hS]
            simp only
            rw [Real.volume_Ico]
            exact ENNReal.ofReal_ne_top
          · simp only [hg, norm_smul, hf₀_piece n t ht, norm_exp_neg_mul]
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
            have := ht.1
            nlinarith
      _ = ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt)) * Δt := by
          rw [setIntegral_const, smul_eq_mul, hS]
          simp only
          rw [Real.volume_real_Ico_of_le (hSle n)]
          ring
  have hint : IntegrableOn g (⋃ n, S n) :=
    integrableOn_iUnion_of_summable_integral_norm hpiece_int
      (Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm_piece
        (hsum.mul_right Δt))
  have hSunion : ⋃ n, S n = Ici 0 := iUnion_Ico_nat_mul hΔt
  rw [laplaceTransform_eq_integral (hint.mono_set (hSunion ▸ Ioi_subset_Ici_self)),
    ← integral_Ici_eq_integral_Ioi, ← hSunion,
    integral_iUnion hSmeas (pairwise_disjoint_Ico_nat_mul hΔt) hint]
  simp only [hpiece]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [show Complex.exp (-(s * ((n + 1) * Δt)))
      = Complex.exp (-(s * (n * Δt))) * Complex.exp (-(s * Δt)) by
    rw [← Complex.exp_add]; congr 1; ring]
  rw [show Complex.exp (-(n * s * Δt)) = Complex.exp (-(s * (n * Δt))) by congr 1; ring]
  field_simp

end LaplaceTransform

/-- The **Z-transform** of the samples $f(n\Delta t)$, Definition 10.3 and (10.84) of
[quarteroni2000numerical]: for $f : \mathbb{R} \to \mathbb{C}$, $\Delta t \in \mathbb{R}$ and
$z \in \mathbb{C}$,
$$Z(z) = \sum_{n \ge 0} f(n\Delta t)\, z^{-n}.$$
This is a power series in $z^{-1}$, and it converges for $|z| > \limsup_n |f(n\Delta t)|^{1/n}$
(`summable_zTransform`).

The sum is Mathlib's `tsum`, which is $0$ where the series is not summable. At $z = 0$ the Lean
convention $0^{-1} = 0$ applies. -/
noncomputable def zTransform (f : ℝ → ℂ) (Δt : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, f (n * Δt) * z⁻¹ ^ n

/-- **The Cauchy–Hadamard root test for the Z-transform**: let $f : \mathbb{R} \to \mathbb{C}$,
$\Delta t \in \mathbb{R}$ and $z \in \mathbb{C}$. If
$$R = \limsup_{n \to \infty} |f(n\Delta t)|^{1/n} < |z|,$$
with the limit superior taken in $[0, \infty]$, then the series
$\sum_{n \ge 0} f(n\Delta t)\, z^{-n}$ is summable.

The limit superior is taken in `ℝ≥0∞`, through the extended norm `‖·‖ₑ`. So an unbounded
sequence of roots gives $R = \infty$ and no $z$. In $\mathbb{R}$, the `limsup` of an unbounded
sequence is the junk value $0$, and the statement would be false. The proof chooses
$R < r < |z|$; then $|f(n\Delta t)| \le r^n$ eventually, and the geometric series
$\sum (r/|z|)^n$ dominates the terms. -/
theorem summable_zTransform {f : ℝ → ℂ} {Δt : ℝ} {z : ℂ}
    (hz : Filter.limsup (fun n : ℕ => ‖f (n * Δt)‖ₑ ^ (1 / (n : ℝ))) atTop < ‖z‖ₑ) :
    Summable fun n : ℕ => f (n * Δt) * z⁻¹ ^ n := by
  obtain ⟨r, hr, hrz⟩ := exists_between hz
  have hrtop : r ≠ ⊤ := (hrz.trans_le le_top).ne
  set ρ : ℝ := r.toReal with hρ
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hz0 : 0 < ‖z‖ := by
    have := ENNReal.toReal_strict_mono (enorm_ne_top) hrz
    rw [toReal_enorm] at this
    exact hρ0.trans_lt this
  have hρz : ρ < ‖z‖ := by
    have := ENNReal.toReal_strict_mono (enorm_ne_top) hrz
    rwa [toReal_enorm] at this
  have hev : ∀ᶠ n : ℕ in atTop, ‖f (n * Δt)‖ₑ ^ (1 / (n : ℝ)) < r :=
    Filter.eventually_lt_of_limsup_lt hr
  have hbound : ∀ᶠ n : ℕ in atTop, ‖f (n * Δt) * z⁻¹ ^ n‖ ≤ (ρ / ‖z‖) ^ n := by
    filter_upwards [hev, Filter.eventually_ge_atTop 1] with n hn hn1
    have hn0 : n ≠ 0 := by omega
    have hlt : ‖f (n * Δt)‖ ^ ((n : ℝ)⁻¹) < ρ := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity),
        ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hrtop] at *
      simpa [one_div] using hn
    have hle : ‖f (n * Δt)‖ ≤ ρ ^ n := by
      have := pow_le_pow_left₀ (by positivity) hlt.le n
      rwa [Real.rpow_inv_natCast_pow (norm_nonneg _) hn0] at this
    rw [norm_mul, norm_pow, norm_inv, div_pow, div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  refine Summable.of_norm_bounded_eventually (g := fun n => (ρ / ‖z‖) ^ n)
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hz0).mpr hρz)) ?_
  rwa [Nat.cofinite_eq_atTop]

/-- **The Z-transform is the discrete Laplace transform** under $z = e^{s\Delta t}$: for
$f : \mathbb{R} \to \mathbb{C}$, $\Delta t \in \mathbb{R}$ and $s \in \mathbb{C}$,
$$Z(e^{s\Delta t}) = \sum_{n \ge 0} f(n\Delta t)\, e^{-ns\Delta t},$$
which is the series of `LaplaceTransform.laplaceTransform_stepFun`. So, under the hypotheses of
that theorem, $\mathcal{L}[f_0](s) = \frac{1 - e^{-s\Delta t}}{s}\, Z(e^{s\Delta t})$.

[quarteroni2000numerical], §10.11.4, prints the substitution as $z = e^{-s\Delta t}$. With
$Z(z) = \sum f(n\Delta t) z^{-n}$ and the discrete Laplace transform
$Z^d(s) = \sum f(n\Delta t) e^{-ns\Delta t}$, the correct substitution is $z = e^{s\Delta t}$. -/
theorem zTransform_eq_discreteLaplace (f : ℝ → ℂ) {Δt : ℝ} (s : ℂ) :
    zTransform f Δt (Complex.exp (s * Δt))
      = ∑' n : ℕ, f (n * Δt) * Complex.exp (-(n * s * Δt)) := by
  unfold zTransform
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
  congr 2
  ring
