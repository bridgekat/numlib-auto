/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.FourierIntegral
import Numlib.Analysis.Wavelet.Multiresolution

/-!
# The continuous wavelet transform

Let $h : \mathbb{R} \to \mathbb{C}$ be an elementary wavelet. Dilation and translation generate the
family of **wavelets**
$$h_{s,\tau}(t) = s^{-1/2}\, h\Bigl(\frac{t - \tau}{s}\Bigr), \qquad s > 0,\ \tau \in \mathbb{R}.$$
The Fourier transform $\mathcal{F} h_{s,\tau}(\nu) = \sqrt{s}\, \mathcal{F}h(s\nu)\, e^{-2\pi i \nu
\tau}$ is the filter of the wavelet transform. The **continuous wavelet transform** of
$f \in L^2(\mathbb{R})$ is $W_f(s, \tau) = \int f(t)\, \overline{h_{s,\tau}(t)}\,dt = \langle
h_{s,\tau}, f \rangle$. This file proves its expression on the Fourier side through Plancherel's
identity. It also defines the **discrete wavelets** $h_{j,k}(t) = s_0^{-j/2} h(s_0^{-j} t -
k\tau_0)$, which sample the scale logarithmically and the shift proportionally to the scale. At the
dyadic parameters $s_0 = 2$, $\tau_0 = 1$, they are the dyadic system $2^{j'/2} \psi(2^{j'} t - k)$
of `Numlib.Analysis.Wavelet.Multiresolution`, with the level index reversed, $j' = -j$. The material
is [quarteroni2000numerical], §10.12 (Definition 10.4, (10.85)–(10.87) and §10.12.2).

## Main definitions

* `Wavelet.dilateTranslate`: the wavelet $h_{s,\tau}$.
* `Wavelet.continuousTransform`: the continuous wavelet transform $W_f(s, \tau)$.
* `Wavelet.discrete`: the discrete wavelets $h_{j,k}$.
* `Wavelet.discreteTransform`: the discrete wavelet transform $W_f(j, k)$.

## Main results

* `Wavelet.memLp_dilateTranslate`, `Wavelet.eLpNorm_dilateTranslate`: for $s > 0$, $h_{s,\tau}$ is
  in $L^2$ with the $L^2$ norm of $h$.
* `Wavelet.integrable_dilateTranslate`: $h_{s,\tau}$ is integrable when $h$ is.
* `Wavelet.fourier_dilateTranslate`: the filter (10.86), $\mathcal{F} h_{s,\tau}(\nu) = \sqrt{s}\,
  \mathcal{F}h(s\nu)\, e^{-2\pi i \nu \tau}$.
* `Wavelet.continuousTransform_eq_inner`: for $f, h \in L^2$,
  $W_f(s, \tau) = \langle h_{s,\tau}, f \rangle$.
* `Wavelet.continuousTransform_eq_integral_fourier`: the transform as a bank of filters, $W_f(s,
  \tau) = \sqrt{s} \int \mathcal{F}f(\nu)\, \overline{\mathcal{F}h(s\nu)}\, e^{2\pi i \nu
  \tau}\,d\nu$ for $f, h \in L^1 \cap L^2$.
* `Wavelet.discrete_two_one_ae_eq_scalingSystem`: at $s_0 = 2$, $\tau_0 = 1$, the discrete wavelets
  of an $L^2$ function $\psi$ are almost everywhere the dyadic system `scalingSystem ψ (-j) k`.
* `Wavelet.discrete_two_one_eq_waveletSystem`: for the wavelet `mraWavelet φ` of a scaling
  function, the discrete wavelets are almost everywhere `waveletSystem φ (-j) k`.

## Implementation notes

* The other wavelet modules start from the dyadic case, because [han2009theoretical], §4.4–4.5,
  states only that case.
* Dilation as a unitary operator of the real space $L^2(\mathbb{R})$ is
  `MeasureTheory.Lp.dilationₗᵢ` in `Numlib.Analysis.Wavelet.Haar`, and translation is
  `MeasureTheory.Lp.translationₗᵢ` in `Numlib.Analysis.Wavelet.Multiresolution`. The pointwise
  family here is what these operators act on when $h$ is given as a function, and
  `Wavelet.discrete_two_one_ae_eq_scalingSystem` translates between the two.
* The orthonormality and reconstruction theorems for the dyadic system are
  `IsMultiresolutionAnalysis.orthonormal_waveletSystem_prod` and
  `IsMultiresolutionAnalysis.hasSum_inner_smul_waveletSystem`.
* The module does not formalize the inversion formula of the continuous wavelet transform
  (Calderón's admissibility condition $\int |\mathcal{F}h(\nu)|^2 / |\nu|\,d\nu < \infty$ and $f =
  C_h^{-1} \iint W_f(s, \tau)\, h_{s,\tau}\,ds\,d\tau / s^2$), which [quarteroni2000numerical] does
  not state either. It also does not formalize the Heisenberg uncertainty inequality, which is
  absent from Mathlib.
-/

open MeasureTheory Filter Topology Complex

open scoped FourierTransform ComplexConjugate Real ENNReal

namespace Wavelet

/-! ### Dilations and translations of an elementary wavelet -/

/-- **The wavelet $h_{s,\tau}$**, (10.85) of [quarteroni2000numerical]: for an elementary wavelet
$h : \mathbb{R} \to \mathbb{C}$, a scale $s$ and a shift $\tau \in \mathbb{R}$,
$$h_{s,\tau}(t) = s^{-1/2}\, h\Bigl(\frac{t - \tau}{s}\Bigr).$$

The definition is meant for $s > 0$, where the factor $s^{-1/2}$ preserves the $L^2$ norm
(`Wavelet.eLpNorm_dilateTranslate`). For $s \le 0$ the Lean conventions $\sqrt{s} = 0$ and
$0^{-1} = 0$ give $h_{s,\tau} = 0$. -/
noncomputable def dilateTranslate (h : ℝ → ℂ) (s τ : ℝ) : ℝ → ℂ :=
  fun t => (Real.sqrt s : ℂ)⁻¹ * h ((t - τ) / s)

/-- The defining formula of `Wavelet.dilateTranslate`: $h_{s,\tau}(t) = (\sqrt{s})^{-1}\, h((t -
\tau)/s)$. -/
theorem dilateTranslate_apply (h : ℝ → ℂ) (s τ t : ℝ) :
    dilateTranslate h s τ t = (Real.sqrt s : ℂ)⁻¹ * h ((t - τ) / s) := rfl

/-- For $s > 0$ and $\tau \in \mathbb{R}$, the image of the Lebesgue measure under the affine change
of variables $t \mapsto (t - \tau)/s$ is $s$ times the Lebesgue measure. -/
theorem map_volume_sub_div {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    Measure.map (fun t : ℝ => (t - τ) / s) volume = ENNReal.ofReal s • volume := by
  have hfun : (fun t : ℝ => (t - τ) / s) = (fun u : ℝ => s⁻¹ * u) ∘ fun t : ℝ => t - τ := by
    funext t
    simp [div_eq_inv_mul]
  rw [hfun, ← Measure.map_map (measurable_const_mul _) (measurable_sub_const _),
    map_sub_right_eq_self, Real.map_volume_mul_left (inv_ne_zero hs.ne'), inv_inv, abs_of_pos hs]

/-- For all $s, \tau \in \mathbb{R}$, the map $t \mapsto (t - \tau)/s$ is almost everywhere
measurable with respect to the Lebesgue measure. -/
theorem aemeasurable_sub_div (s τ : ℝ) : AEMeasurable (fun t : ℝ => (t - τ) / s) volume :=
  ((measurable_sub_const τ).div_const s).aemeasurable

/-- If $h \in L^2(\mathbb{R})$, $s > 0$ and $\tau \in \mathbb{R}$, then
$h_{s,\tau} \in L^2(\mathbb{R})$. -/
theorem memLp_dilateTranslate {h : ℝ → ℂ} (hh : MemLp h 2) {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    MemLp (dilateTranslate h s τ) 2 := by
  have h1 : MemLp h 2 (Measure.map (fun t : ℝ => (t - τ) / s) volume) := by
    rw [map_volume_sub_div hs]
    exact hh.smul_measure ENNReal.ofReal_ne_top
  exact ((memLp_map_measure_iff h1.aestronglyMeasurable (aemeasurable_sub_div s τ)).mp
    h1).const_mul _

/-- **The normalization of the wavelets**: if $h$ is almost everywhere strongly measurable, $s > 0$
and $\tau \in \mathbb{R}$, then
$$\|h_{s,\tau}\|_{L^2} = \|h\|_{L^2}.$$
This is the reason for the factor $s^{-1/2}$.

The norms are the extended norms `eLpNorm`, so the identity also holds when $h \notin L^2$, with
both sides infinite. -/
theorem eLpNorm_dilateTranslate {h : ℝ → ℂ} (hh : AEStronglyMeasurable h volume) {s : ℝ}
    (hs : 0 < s) (τ : ℝ) : eLpNorm (dilateTranslate h s τ) 2 volume = eLpNorm h 2 volume := by
  have hsq : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hmap := map_volume_sub_div hs τ
  have hh' : AEStronglyMeasurable h (Measure.map (fun t : ℝ => (t - τ) / s) volume) := by
    rw [hmap]
    exact hh.mono_ac Measure.smul_absolutelyContinuous
  have h1 := eLpNorm_map_measure (p := 2) hh' (aemeasurable_sub_div s τ)
  rw [hmap, eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ hh] at h1
  have h2 : dilateTranslate h s τ = ((Real.sqrt s : ℂ)⁻¹) • (h ∘ fun t => (t - τ) / s) := by
    funext t
    simp [dilateTranslate_apply]
  rw [h2, eLpNorm_const_smul, ← h1, smul_eq_mul, ← mul_assoc]
  have h3 : ‖((Real.sqrt s : ℂ)⁻¹)‖ₑ * ENNReal.ofReal s ^ ((1 : ℝ≥0∞) / 2).toReal = 1 := by
    rw [enorm_inv (by exact_mod_cast hsq.ne'), ← ofReal_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hsq, show ((1 : ℝ≥0∞) / 2).toReal = (1 / 2 : ℝ) by simp,
      ENNReal.ofReal_rpow_of_nonneg hs.le (by norm_num), ← Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_inv_of_pos hsq, ← ENNReal.ofReal_mul (inv_nonneg.mpr hsq.le),
      inv_mul_cancel₀ hsq.ne', ENNReal.ofReal_one]
  rw [h3, one_mul]

/-- If $h$ is integrable, $s \neq 0$ and $\tau \in \mathbb{R}$, then $h_{s,\tau}$ is integrable. -/
theorem integrable_dilateTranslate {h : ℝ → ℂ} (hh : Integrable h) {s : ℝ} (hs : s ≠ 0)
    (τ : ℝ) : Integrable (dilateTranslate h s τ) :=
  ((hh.comp_div hs).comp_sub_right τ).const_mul _

/-- **The filter of the wavelet transform**, (10.86) of [quarteroni2000numerical]: for
$h : \mathbb{R} \to \mathbb{C}$, $s > 0$ and $\tau, \nu \in \mathbb{R}$,
$$\mathcal{F} h_{s,\tau}(\nu) = \sqrt{s}\, \mathcal{F}h(s\nu)\, e^{-2\pi i \nu \tau}.$$
In the variable $\omega = 2\pi\nu$ this is the source's $H_{s,\tau}(\omega) = \sqrt{s}\,
H(s\omega)\, e^{-i\omega\tau}$. A dilation by $s$ in time is a contraction by $s$ in frequency,
so $1/s$ plays the role of a frequency.

The proof uses the translation and scaling rules `Real.fourierIntegral_comp_sub_right` and
`Real.fourierIntegral_comp_mul_left`. No integrability is needed: if $h$ is not integrable, both
sides are $0$. -/
theorem fourier_dilateTranslate {h : ℝ → ℂ} {s : ℝ} (hs : 0 < s) (τ ν : ℝ) :
    𝓕 (dilateTranslate h s τ) ν
      = Real.sqrt s * 𝓕 h (s * ν) * Complex.exp (-(2 * π * ν * τ) * I) := by
  have hsq : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h1 : dilateTranslate h s τ
      = fun t => ((Real.sqrt s : ℂ)⁻¹) • (fun v : ℝ => (fun u : ℝ => h (s⁻¹ * u)) (v - τ)) t := by
    funext t
    simp only [dilateTranslate_apply, smul_eq_mul, div_eq_inv_mul]
  rw [h1, Real.fourierIntegral_const_smul,
    Real.fourierIntegral_comp_sub_right (fun u : ℝ => h (s⁻¹ * u)) τ ν,
    Real.fourierIntegral_comp_mul_left (inv_ne_zero hs.ne'), abs_inv, inv_inv, div_inv_eq_mul,
    abs_of_pos hs]
  simp only [smul_eq_mul, Circle.smul_def, Real.fourierChar_apply, Complex.real_smul]
  have hs' : (Real.sqrt s : ℂ) * Real.sqrt s = s := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]
  rw [mul_comm ν s]
  have hexp : Complex.exp (↑(2 * π * -(τ * ν)) * I) = Complex.exp (-(2 * π * ν * τ) * I) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  have hsqC : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
  field_simp
  rw [← hs']
  ring

/-! ### The continuous wavelet transform -/

/-- **The continuous wavelet transform**, Definition 10.4 and (10.87) of [quarteroni2000numerical]:
for $f, h : \mathbb{R} \to \mathbb{C}$ and $s, \tau \in \mathbb{R}$,
$$W_f(s, \tau) = \int_{\mathbb{R}} f(t)\, \overline{h_{s,\tau}(t)}\,dt.$$
As a function of the scale $s$ and the time shift $\tau$, it is the time-scale representation of
$f$.

For $f, h \in L^2$ and $s > 0$ it is the inner product $\langle h_{s,\tau}, f \rangle$ of $L^2$,
in Mathlib's convention that the inner product is conjugate-linear in the first argument
(`Wavelet.continuousTransform_eq_inner`). The integral is a Bochner integral, which is $0$ when
the integrand is not integrable. -/
noncomputable def continuousTransform (h f : ℝ → ℂ) (s τ : ℝ) : ℂ :=
  ∫ t, f t * conj (dilateTranslate h s τ t)

/-- The defining formula of `Wavelet.continuousTransform`: $W_f(s, \tau) = \int f(t)\,
\overline{h_{s,\tau}(t)}\,dt$. -/
theorem continuousTransform_def (h f : ℝ → ℂ) (s τ : ℝ) :
    continuousTransform h f s τ = ∫ t, f t * conj (dilateTranslate h s τ t) := rfl

/-- If $h, f \in L^2(\mathbb{R})$, $s > 0$ and $\tau \in \mathbb{R}$, then the wavelet transform is
the $L^2$ inner product $W_f(s, \tau) = \langle h_{s,\tau}, f \rangle$. -/
theorem continuousTransform_eq_inner {h f : ℝ → ℂ} (hh : MemLp h 2) (hf : MemLp f 2) {s : ℝ}
    (hs : 0 < s) (τ : ℝ) :
    continuousTransform h f s τ
      = inner ℂ ((memLp_dilateTranslate hh hs τ).toLp _) (hf.toLp f) := by
  rw [L2.inner_def, continuousTransform_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_dilateTranslate hh hs τ).coeFn_toLp, hf.coeFn_toLp] with t h1 h2
  rw [RCLike.inner_apply', h1, h2, mul_comm]

/-- **The wavelet transform as a bank of filters**, the Fourier-side form of (10.87) in §10.12.1 of
[quarteroni2000numerical]: let $f, h \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$, $s > 0$ and
$\tau \in \mathbb{R}$. Then
$$W_f(s, \tau) = \sqrt{s} \int_{\mathbb{R}} \mathcal{F}f(\nu)\, \overline{\mathcal{F}h(s\nu)}\,
  e^{2\pi i \nu \tau}\,d\nu.$$
In the variable $\omega = 2\pi\nu$ this is the source's $\frac{\sqrt{s}}{2\pi} \int F(\omega)\,
\overline{H(s\omega)}\, e^{i\omega\tau}\,d\omega$.

The proof applies Plancherel's identity on $L^1 \cap L^2$
(`Real.integral_conj_fourier_mul_fourier`) to $h_{s,\tau}$ and $f$, followed by the filter
identity `Wavelet.fourier_dilateTranslate`. -/
theorem continuousTransform_eq_integral_fourier {h f : ℝ → ℂ} (hh1 : MemLp h 1) (hh2 : MemLp h 2)
    (hf1 : MemLp f 1) (hf2 : MemLp f 2) {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    continuousTransform h f s τ
      = Real.sqrt s * ∫ ν, 𝓕 f ν * conj (𝓕 h (s * ν)) * Complex.exp ((2 * π * ν * τ) * I) := by
  have hd1 : MemLp (dilateTranslate h s τ) 1 :=
    memLp_one_iff_integrable.mpr
      (integrable_dilateTranslate (memLp_one_iff_integrable.mp hh1) hs.ne' τ)
  have hd2 : MemLp (dilateTranslate h s τ) 2 := memLp_dilateTranslate hh2 hs τ
  have hpl := Real.integral_conj_fourier_mul_fourier hd1 hd2 hf1 hf2
  rw [continuousTransform_def, ← integral_const_mul]
  rw [show (∫ t, f t * conj (dilateTranslate h s τ t))
      = ∫ t, conj (dilateTranslate h s τ t) * f t from
    integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _), ← hpl]
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only
  rw [fourier_dilateTranslate hs, map_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-! ### Discrete wavelets -/

/-- **The discrete wavelets**, §10.12.2 of [quarteroni2000numerical]: for a scale step $s_0$, a
shift step $\tau_0$ and integers $j, k$, the discrete wavelet is the wavelet of scale
$s = s_0^j$ and shift $\tau = k \tau_0 s_0^j$,
$$h_{j,k}(t) = s_0^{-j/2}\, h\bigl(s_0^{-j}(t - k\tau_0 s_0^j)\bigr) = s_0^{-j/2}\, h(s_0^{-j}
  t - k\tau_0).$$
The shift step is proportional to the scale, so the wavelets of small scale (large negative $j$)
are concentrated and finely spaced.

The source takes $s_0 > 1$; the definition has no hypothesis on $s_0$. The second form is
`Wavelet.discrete_apply`. -/
noncomputable def discrete (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (j k : ℤ) : ℝ → ℂ :=
  dilateTranslate h (s₀ ^ j) (k * τ₀ * s₀ ^ j)

/-- The defining formula of `Wavelet.discrete`: $h_{j,k} = h_{s_0^j,\, k\tau_0 s_0^j}$. -/
theorem discrete_def (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (j k : ℤ) :
    discrete h s₀ τ₀ j k = dilateTranslate h (s₀ ^ j) (k * τ₀ * s₀ ^ j) := rfl

/-- The discrete wavelet in the second form of the source: for $s_0 > 0$, $\tau_0 \in \mathbb{R}$
and integers $j, k$,
$$h_{j,k}(t) = s_0^{-j/2}\, h(s_0^{-j} t - k\tau_0).$$
-/
theorem discrete_apply (h : ℝ → ℂ) {s₀ : ℝ} (hs₀ : 0 < s₀) (τ₀ : ℝ) (j k : ℤ) (t : ℝ) :
    discrete h s₀ τ₀ j k t = (Real.sqrt (s₀ ^ j) : ℂ)⁻¹ * h (s₀ ^ (-j) * t - k * τ₀) := by
  rw [discrete_def, dilateTranslate_apply]
  congr 2
  have : s₀ ^ j ≠ 0 := zpow_ne_zero j hs₀.ne'
  rw [zpow_neg]
  field_simp

/-- **The discrete wavelet transform**, §10.12.2 of [quarteroni2000numerical]: for
$f, h : \mathbb{R} \to \mathbb{C}$, $s_0, \tau_0 \in \mathbb{R}$ and integers $j, k$,
$$W_f(j, k) = \int_{\mathbb{R}} f(t)\, \overline{h_{j,k}(t)}\,dt.$$
It is the continuous transform sampled at the discrete scales and shifts
(`Wavelet.discreteTransform_eq_continuousTransform`).

The source writes $f \in L^1(\mathbb{R})$. The natural domain is $L^2(\mathbb{R})$, where the
transform is the inner product $\langle h_{j,k}, f \rangle$. -/
noncomputable def discreteTransform (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (f : ℝ → ℂ) (j k : ℤ) : ℂ :=
  ∫ t, f t * conj (discrete h s₀ τ₀ j k t)

/-- The discrete wavelet transform is the continuous transform at the scale $s_0^j$ and the shift
$k\tau_0 s_0^j$: $W_f(j, k) = W_f(s_0^j, k\tau_0 s_0^j)$. -/
theorem discreteTransform_eq_continuousTransform (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (f : ℝ → ℂ) (j k : ℤ) :
    discreteTransform h s₀ τ₀ f j k = continuousTransform h f (s₀ ^ j) (k * τ₀ * s₀ ^ j) := rfl

open MeasureTheory.Lp in
/-- **The dyadic discrete wavelets are the dyadic system of a scaling function**: let
$\psi \in L^2(\mathbb{R})$ be real, viewed as a complex function. For $s_0 = 2$, $\tau_0 = 1$
and integers $j, k$, the discrete wavelet $h_{j,k}$ of $\psi$ is, almost everywhere, the
function $2^{-j/2} \psi(2^{-j} t - k)$ that represents `scalingSystem ψ (-j) k`.

The level index is reversed between the two conventions: the scale $2^j$ of the source is the
level $-j$ of a multiresolution analysis. The proof unfolds `MeasureTheory.Lp.dilationₗᵢ` and
`MeasureTheory.Lp.translationₗᵢ` on representatives. -/
theorem discrete_two_one_ae_eq_scalingSystem (ψ : Lp ℝ 2 (volume : Measure ℝ)) (j k : ℤ) :
    discrete (fun t => ((ψ : ℝ → ℝ) t : ℂ)) 2 1 j k
      =ᵐ[volume] fun t => ((scalingSystem ψ (-j) k : ℝ → ℝ) t : ℂ) := by
  have hc : ((2 : ℝ) ^ (-j)) ≠ 0 := zpow_ne_zero _ two_ne_zero
  have hd := dilationₗᵢ_apply ((2 : ℝ) ^ (-j)) hc (translates ψ k)
  have ht := ae_comp_const_mul hc (translationₗᵢ_apply (-(k : ℝ)) ψ)
  filter_upwards [hd, ht] with t hdt htt
  rw [scalingSystem, hdt]
  simp only [translates] at htt ⊢
  rw [htt, discrete_apply _ two_pos]
  rw [abs_of_pos (zpow_pos two_pos _), ← Real.sqrt_eq_rpow, zpow_neg, Real.sqrt_inv]
  push_cast
  congr 3
  ring

/-- **The dyadic discrete wavelets of a multiresolution analysis**: let
$\varphi \in L^2(\mathbb{R})$ be real, and let $\psi$ be the wavelet `mraWavelet φ`. For
$s_0 = 2$, $\tau_0 = 1$ and integers $j, k$, the discrete wavelet $h_{j,k}$ of $\psi$ is, almost
everywhere, the function that represents `waveletSystem φ (-j) k`.

So the orthonormality `IsMultiresolutionAnalysis.orthonormal_waveletSystem_prod` and the
reconstruction formula `IsMultiresolutionAnalysis.hasSum_inner_smul_waveletSystem` are the
statements of [quarteroni2000numerical], §10.12.2, about orthonormal wavelet bases. -/
theorem discrete_two_one_eq_waveletSystem (φ : Lp ℝ 2 (volume : Measure ℝ)) (j k : ℤ) :
    discrete (fun t => ((mraWavelet φ : ℝ → ℝ) t : ℂ)) 2 1 j k
      =ᵐ[volume] fun t => ((waveletSystem φ (-j) k : ℝ → ℝ) t : ℂ) :=
  discrete_two_one_ae_eq_scalingSystem (mraWavelet φ) j k

end Wavelet
