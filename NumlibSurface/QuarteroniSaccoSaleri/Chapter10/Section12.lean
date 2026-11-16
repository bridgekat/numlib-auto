/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Numlib.Analysis.Fourier.Uncertainty
import Numlib.Analysis.Wavelet.ContinuousTransform

/-!
# Quarteroni, Sacco and Saleri, Section 10.12: The wavelet transform

This module formalizes Section 10.12 of [quarteroni2000numerical]. From an elementary wavelet $h$,
translations and dilations generate the wavelets $h_{s,\tau}(t) = s^{-1/2} h((t - \tau)/s)$ (10.85),
whose Fourier transform is given by (10.86). The continuous wavelet transform $W_f(s, \tau) = \int
f(t) \overline{h_{s,\tau}(t)} \, dt$ (Definition 10.4, (10.87)) is also a bank of filters on the
Fourier side. The module states the Heisenberg inequality $\Delta t \, \Delta\omega \ge 1/2$
(10.88), the Fourier transforms of the Haar wavelet (Example 10.10) and of the Morlet wavelet
(Example 10.11), and the discrete and orthonormal wavelets of Section 10.12.2 with the
reconstruction formula.

The continuous side comes from `Numlib.Analysis.Wavelet.ContinuousTransform`. The discrete side at
the dyadic parameters $s_0 = 2$, $\tau_0 = 1$ comes from `Numlib.Analysis.Wavelet.Multiresolution`
and `Numlib.Analysis.Wavelet.Haar`. The Heisenberg inequality comes from
`Numlib.Analysis.Fourier.Uncertainty`.

## Main definitions

* Equation (10.85), `QuarteroniSaccoSaleri.Chapter10.wavelet`: the wavelet $h_{s,\tau}$.
* Definition 10.4, `QuarteroniSaccoSaleri.Chapter10.definition_10_4`: the continuous wavelet
  transform $W_f(s, \tau)$.
* Equation (10.88), `QuarteroniSaccoSaleri.Chapter10.timeResolution` and
  `QuarteroniSaccoSaleri.Chapter10.freqResolution`: the resolutions $\Delta t$ in time and
  $\Delta\omega$ in angular frequency.
* Example 10.10, `QuarteroniSaccoSaleri.Chapter10.haarWavelet`: the Haar wavelet.
* Example 10.11, `QuarteroniSaccoSaleri.Chapter10.morletWavelet`: the Morlet wavelet.
* Section 10.12.2, `QuarteroniSaccoSaleri.Chapter10.discreteWavelet` and
  `QuarteroniSaccoSaleri.Chapter10.discreteWaveletTransform`: the discrete wavelets $h_{j,k}$ and
  the discrete wavelet transform $W_f(j, k)$.

## Main results

* Equation (10.86), `QuarteroniSaccoSaleri.Chapter10.equation_10_86`: $\mathcal{F} h_{s,\tau}(\nu) =
  \sqrt{s} \, \mathcal{F} h(s\nu) e^{-2\pi i\nu\tau}$.
* Definition 10.4, `QuarteroniSaccoSaleri.Chapter10.definition_10_4_eq_inner` and
  `QuarteroniSaccoSaleri.Chapter10.continuousTransform_eq_integral_fourier`: $W_f(s, \tau)$ as the
  $L^2$ inner product of $h_{s,\tau}$ and $f$, and as a bank of filters on the Fourier side.
* Equation (10.88), `QuarteroniSaccoSaleri.Chapter10.equation_10_88`: the Heisenberg inequality
  $\Delta t \, \Delta\omega \ge 1/2$.
* Example 10.10, `QuarteroniSaccoSaleri.Chapter10.example_10_10`: the Fourier transform of the Haar
  wavelet.
* Example 10.11, `QuarteroniSaccoSaleri.Chapter10.example_10_11`: the Fourier transform of the real
  part of the Morlet wavelet.
* Section 10.12.2, `QuarteroniSaccoSaleri.Chapter10.discreteWaveletTransform_eq`: the discrete
  transform samples the continuous one.
* Section 10.12.2, `QuarteroniSaccoSaleri.Chapter10.discreteWavelet_two_one` and
  `QuarteroniSaccoSaleri.Chapter10.orthonormalWavelet_reconstruction`: the dyadic discrete wavelets
  of a multiresolution analysis are its wavelet system, they are orthonormal, and they reconstruct
  every $f \in L^2(\mathbb{R})$ with the constant $A = 1$.

## Conventions

* The book writes its Fourier transforms in the angular frequency $\omega = 2\pi\nu$. The statements
  here use the frequency $\nu$ of Mathlib's `𝓕`, and the doc comments give both forms.
* The book's discrete wavelets are $s_0^{-j/2} h(s_0^{-j} t - k\tau_0)$, and the backbone's wavelet
  system is $2^{j/2} \psi(2^j x - k)$. At $s_0 = 2$, $\tau_0 = 1$ the level index is reversed,
  $j \mapsto -j$.

## Deviations from the source

* **The bandwidth $\Delta\omega$ of Section 10.12.1** (typo). The book prints an outer square where
  a square root is meant. See `QuarteroniSaccoSaleri.Chapter10.freqResolution`.
* **The resolution in time $\Delta t$ in (10.88)** (reading). The book uses $\Delta t$ without a
  definition. The library uses the root mean square spread of $|h|^2$. See
  `QuarteroniSaccoSaleri.Chapter10.timeResolution`.
* **Equation (10.88)** (reading). The book states the inequality for a general signal. The library
  states it for a nonzero Schwartz function. See `QuarteroniSaccoSaleri.Chapter10.equation_10_88`.
* **Example 10.10** (correction). The book prints the transform
  $4i e^{-i\omega/2}(1 - \cos(\omega/2))/\omega$. It is
  $2i e^{-i\omega/2}(1 - \cos(\omega/2))/\omega$. See
  `QuarteroniSaccoSaleri.Chapter10.example_10_10`.
* **Example 10.11** (correction). The book prints the constant $\sqrt{\pi}$. It is $\sqrt{\pi/2}$.
  See `QuarteroniSaccoSaleri.Chapter10.example_10_11`.
* **The discrete wavelet transform of Section 10.12.2** (reading). The book defines it for
  $f \in L^1(\mathbb{R})$. It is the $L^2$ inner product and lives on $L^2(\mathbb{R})$. See
  `QuarteroniSaccoSaleri.Chapter10.discreteWaveletTransform`.
* **The reconstruction formula of Section 10.12.2** (reading). The constant $A$ is $1$ for an
  orthonormal basis. See `QuarteroniSaccoSaleri.Chapter10.orthonormalWavelet_reconstruction`.

## Not formalized

* **The discussion of the bandwidth and of the quality factor after Example 10.11.** It is prose.
* **The Heisenberg inequality (10.88) for a general signal in $L^2(\mathbb{R})$.** It needs $t h(t)$
  and $\nu \mathcal{F} h(\nu)$ in $L^2$ and a density argument.
-/

open MeasureTheory Filter Topology Complex Set

open scoped FourierTransform ComplexConjugate Real SchwartzMap

namespace QuarteroniSaccoSaleri.Chapter10

/-! ### Equations (10.85)–(10.87): wavelets and the continuous wavelet transform -/

/-- **Equation (10.85)** of [quarteroni2000numerical]. Let $h : \mathbb{R} \to \mathbb{C}$ be an
elementary wavelet, let $s > 0$ be a dilation and $\tau \in \mathbb{R}$ a translation. The
**wavelet** $h_{s,\tau}$ is
$$h_{s,\tau}(t) = s^{-1/2} h\Bigl(\frac{t - \tau}{s}\Bigr).$$

The book takes $h \in L^2(\mathbb{R})$. The definition is the backbone's
`Wavelet.dilateTranslate`, and it gives a value for every $s \in \mathbb{R}$, with the Lean
conventions $\sqrt{s} = 0$ for $s < 0$ and $0^{-1} = 0$. -/
noncomputable def wavelet (h : ℝ → ℂ) (s τ : ℝ) : ℝ → ℂ := Wavelet.dilateTranslate h s τ

/-- For $h : \mathbb{R} \to \mathbb{C}$ and $s, \tau, t \in \mathbb{R}$, the wavelet (10.85) is
$h_{s,\tau}(t) = (\sqrt{s})^{-1} h((t - \tau)/s)$. -/
theorem wavelet_apply (h : ℝ → ℂ) (s τ t : ℝ) :
    wavelet h s τ t = (Real.sqrt s : ℂ)⁻¹ * h ((t - τ) / s) := rfl

/-- **Equation (10.86)** of [quarteroni2000numerical], the filter of the wavelet transform. Let
$h : \mathbb{R} \to \mathbb{C}$, $s > 0$ and $\tau, \nu \in \mathbb{R}$. Then
$$\mathcal{F} h_{s,\tau}(\nu) = \sqrt{s} \, \mathcal{F} h(s\nu) \, e^{-2\pi i\nu\tau}.$$
In the variable $\omega = 2\pi\nu$ of the book this is $H_{s,\tau}(\omega) = \sqrt{s} H(s\omega)
e^{-i\omega\tau}$.

A dilation $t/s$ in time is a contraction $s\omega$ in frequency, so $1/s$ plays the role of the
frequency, and $s$ is called the scale. The proof specializes `Wavelet.fourier_dilateTranslate`. -/
theorem equation_10_86 (h : ℝ → ℂ) {s : ℝ} (hs : 0 < s) (τ ν : ℝ) :
    𝓕 (wavelet h s τ) ν = Real.sqrt s * 𝓕 h (s * ν) * Complex.exp (-(2 * π * ν * τ) * I) :=
  Wavelet.fourier_dilateTranslate hs τ ν

/-- **Definition 10.4** of [quarteroni2000numerical], (10.87). Let
$h, f : \mathbb{R} \to \mathbb{C}$ and $s, \tau \in \mathbb{R}$. The **continuous wavelet
transform** of $f$ with respect to the elementary wavelet $h$ is
$$W_f(s, \tau) = \int_{-\infty}^{\infty} f(t) \overline{h_{s,\tau}(t)} \, dt,$$
a function of the scale $s$ and the time shift $\tau$, called the time-scale representation of
$f$.

The book takes $f \in L^2(\mathbb{R})$. The integral is the Bochner integral, which is $0$ when
the integrand is not integrable. The definition is the backbone's `Wavelet.continuousTransform`
by `QuarteroniSaccoSaleri.Chapter10.definition_10_4_eq_continuousTransform`. -/
noncomputable def definition_10_4 (h f : ℝ → ℂ) (s τ : ℝ) : ℂ :=
  ∫ t : ℝ, f t * conj (wavelet h s τ t)

/-- For $h, f : \mathbb{R} \to \mathbb{C}$ and $s, \tau \in \mathbb{R}$, the continuous wavelet
transform of Definition 10.4 is the backbone's `Wavelet.continuousTransform h f s τ`. -/
theorem definition_10_4_eq_continuousTransform (h f : ℝ → ℂ) (s τ : ℝ) :
    definition_10_4 h f s τ = Wavelet.continuousTransform h f s τ := rfl

/-- **Definition 10.4** of [quarteroni2000numerical], as an inner product. Let
$h, f \in L^2(\mathbb{R})$, $s > 0$ and $\tau \in \mathbb{R}$. Then $W_f(s, \tau)$ is the $L^2$
inner product $(f, h_{s,\tau})$ of the book.

In Lean the inner product is `inner ℂ` of the classes of $h_{s,\tau}$ and $f$ in
`MeasureTheory.Lp ℂ 2`. Mathlib's inner product is conjugate-linear in the first argument, so
the order of the arguments is the reverse of the book's. -/
theorem definition_10_4_eq_inner {h f : ℝ → ℂ} (hh : MemLp h 2) (hf : MemLp f 2) {s : ℝ}
    (hs : 0 < s) (τ : ℝ) :
    definition_10_4 h f s τ
      = inner ℂ ((Wavelet.memLp_dilateTranslate hh hs τ).toLp _) (hf.toLp f) :=
  Wavelet.continuousTransform_eq_inner hh hf hs τ

/-- **Definition 10.4** of [quarteroni2000numerical], the wavelet transform as a bank of filters
(the formula after (10.88)). Let $h, f \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$, $s > 0$ and
$\tau \in \mathbb{R}$. Then
$$W_f(s, \tau) = \sqrt{s} \int_{-\infty}^{\infty} \mathcal{F} f(\nu) \, \overline{\mathcal{F}
  h(s\nu)} \, e^{2\pi i\nu\tau} \, d\nu.$$
In the variable $\omega = 2\pi\nu$ this is the book's $\frac{\sqrt{s}}{2\pi} \int F(\omega)
\overline{H(s\omega)} e^{i\omega\tau} \, d\omega$.

The proof applies the identity of Plancherel to $h_{s,\tau}$ and $f$, with (10.86). It
specializes `Wavelet.continuousTransform_eq_integral_fourier`. -/
theorem continuousTransform_eq_integral_fourier {h f : ℝ → ℂ} (hh1 : MemLp h 1) (hh2 : MemLp h 2)
    (hf1 : MemLp f 1) (hf2 : MemLp f 2) {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    definition_10_4 h f s τ
      = Real.sqrt s * ∫ ν, 𝓕 f ν * conj (𝓕 h (s * ν)) * Complex.exp ((2 * π * ν * τ) * I) :=
  Wavelet.continuousTransform_eq_integral_fourier hh1 hh2 hf1 hf2 hs τ

/-! ### Equation (10.88): the Heisenberg inequality -/

/-- **Equation (10.88)** of [quarteroni2000numerical], the resolution in time. For
$h : \mathbb{R} \to \mathbb{C}$ the **resolution in time** is
$$\Delta t = \Bigl(\frac{\int t^2 |h(t)|^2 \, dt}{\int |h(t)|^2 \, dt}\Bigr)^{1/2},$$
the root mean square spread of $|h|^2$ about the origin.

**Reading.** The book uses $\Delta t$ in (10.88) without a definition. This is the standard
definition, and its counterpart in frequency is the bandwidth $\Delta\omega$ of Section 10.12.1.

The integrals are Bochner integrals, which are $0$ when the integrand is not integrable, and
division by $0$ gives $0$. -/
noncomputable def timeResolution (h : ℝ → ℂ) : ℝ :=
  Real.sqrt ((∫ t : ℝ, t ^ 2 * ‖h t‖ ^ 2) / ∫ t : ℝ, ‖h t‖ ^ 2)

/-- **Section 10.12.1** of [quarteroni2000numerical], the bandwidth. For
$h : \mathbb{R} \to \mathbb{C}$ with Fourier transform $H(\omega) = \mathcal{F} h(\omega/2\pi)$
in the variable $\omega = 2\pi\nu$, the **resolution in angular frequency** is
$$\Delta\omega = \Bigl(\frac{\int \omega^2 |H(\omega)|^2 \, d\omega}{\int |H(\omega)|^2 \,
  d\omega}\Bigr)^{1/2}.$$

**Typo.** The book's display has an outer square where the square root is meant. The square root
makes (10.88) dimensionally correct, and the relation $\Delta\omega_s = \Delta\omega/s$ in the
display after it requires it.

The integrals are Bochner integrals, which are $0$ when the integrand is not integrable, and
division by $0$ gives $0$. -/
noncomputable def freqResolution (h : ℝ → ℂ) : ℝ :=
  Real.sqrt ((∫ ω : ℝ, ω ^ 2 * ‖𝓕 h (ω / (2 * π))‖ ^ 2) / ∫ ω : ℝ, ‖𝓕 h (ω / (2 * π))‖ ^ 2)

/-- **Equation (10.88)** of [quarteroni2000numerical], the Heisenberg inequality. Let $h$ be a
nonzero Schwartz function on $\mathbb{R}$ with complex values. Then
$$\Delta t \, \Delta\omega \ge \frac{1}{2}.$$
So the resolutions in time and in frequency cannot both be small: a signal is not a point of the
time-frequency plane, but occupies a rectangle of area at least $1/2$.

**Reading.** The book states the inequality for a general signal. It is stated here for a
Schwartz function. In this class all four integrals in $\Delta t$ and $\Delta\omega$ converge,
and the backbone's `SchwartzMap.heisenberg_uncertainty` is proved there. The statement for
general $h \in L^2(\mathbb{R})$ needs $t h(t)$ and $\nu \mathcal{F} h(\nu)$ in $L^2$ and a
density argument, and it is not formalized.

The change from the frequency $\nu$ of Mathlib's `𝓕` to $\omega = 2\pi\nu$ multiplies the
numerator of $\Delta\omega^2$ by $8\pi^3$ and its denominator by $2\pi$. So $\Delta\omega^2 =
4\pi^2 \int \nu^2 |\mathcal{F} h|^2 / \int |h|^2$, and the backbone bound $(\int |h|^2)^2 \le
16\pi^2 (\int t^2 |h|^2)(\int \nu^2 |\mathcal{F} h|^2)$ is exactly
$\Delta t^2 \Delta\omega^2 \ge 1/4$. -/
theorem equation_10_88 (h : 𝓢(ℝ, ℂ)) (hne : (h : ℝ → ℂ) ≠ 0) :
    1 / 2 ≤ timeResolution (h : ℝ → ℂ) * freqResolution (h : ℝ → ℂ) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set A := ∫ t : ℝ, t ^ 2 * ‖h t‖ ^ 2 with hAdef
  set N := ∫ t : ℝ, ‖h t‖ ^ 2 with hNdef
  set B := ∫ v : ℝ, v ^ 2 * ‖𝓕 (h : ℝ → ℂ) v‖ ^ 2 with hBdef
  have hA0 : 0 ≤ A := integral_nonneg fun t => by positivity
  have hB0 : 0 ≤ B := integral_nonneg fun t => by positivity
  have hN0 : 0 < N := by
    rw [hNdef, integral_pos_iff_support_of_nonneg (fun t => by positivity)
      (SchwartzMap.integrable_norm_sq h)]
    have hsupp : Function.support (fun t : ℝ => ‖h t‖ ^ 2) = {t : ℝ | h t ≠ 0} := by
      ext t
      simp [Function.mem_support]
    obtain ⟨t₀, ht₀⟩ : ∃ t, (h : ℝ → ℂ) t ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (funext hc)
    rw [hsupp]
    exact (isOpen_ne_fun h.continuous continuous_const).measure_pos volume ⟨t₀, ht₀⟩
  have hplan : ∫ v : ℝ, ‖𝓕 (h : ℝ → ℂ) v‖ ^ 2 = N := by
    have hp := SchwartzMap.integral_norm_sq_fourier h
    rw [SchwartzMap.fourier_coe] at hp
    exact hp
  have hden : (∫ ω : ℝ, ‖𝓕 (h : ℝ → ℂ) (ω / (2 * π))‖ ^ 2) = 2 * π * N := by
    rw [Measure.integral_comp_div (fun v : ℝ => ‖𝓕 (h : ℝ → ℂ) v‖ ^ 2) (2 * π), hplan,
      abs_of_pos hpi, smul_eq_mul]
  have hnum : (∫ ω : ℝ, ω ^ 2 * ‖𝓕 (h : ℝ → ℂ) (ω / (2 * π))‖ ^ 2) = 8 * π ^ 3 * B := by
    have hc := Measure.integral_comp_div
      (fun v : ℝ => (2 * π * v) ^ 2 * ‖𝓕 (h : ℝ → ℂ) v‖ ^ 2) (2 * π)
    have hl : (∫ ω : ℝ, (2 * π * (ω / (2 * π))) ^ 2 * ‖𝓕 (h : ℝ → ℂ) (ω / (2 * π))‖ ^ 2)
        = ∫ ω : ℝ, ω ^ 2 * ‖𝓕 (h : ℝ → ℂ) (ω / (2 * π))‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hω : 2 * π * (ω / (2 * π)) = ω := by field_simp
      simp only [hω]
    have hr : (∫ v : ℝ, (2 * π * v) ^ 2 * ‖𝓕 (h : ℝ → ℂ) v‖ ^ 2) = 4 * π ^ 2 * B := by
      rw [hBdef, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      ring
    rw [hl, hr, abs_of_pos hpi, smul_eq_mul] at hc
    rw [hc]
    ring
  have hkey : N ^ 2 ≤ 16 * π ^ 2 * A * B := SchwartzMap.heisenberg_uncertainty h
  rw [timeResolution, freqResolution, hden, hnum, ← hAdef, ← hNdef,
    ← Real.sqrt_mul (by positivity)]
  have hprod : A / N * (8 * π ^ 3 * B / (2 * π * N)) = 4 * π ^ 2 * A * B / N ^ 2 := by
    field_simp
    ring
  rw [hprod, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hkey]

/-! ### Examples 10.10–10.11 -/

/-- **Example 10.10** of [quarteroni2000numerical], the Haar wavelet. The **Haar wavelet** is the
function $h$ with $h(x) = 1$ for $0 < x < 1/2$, $h(x) = -1$ for $1/2 < x < 1$, and $h(x) = 0$
otherwise.

Up to a null set, it is the function of the backbone's `Haar.waveletFun 0 0`, by
`QuarteroniSaccoSaleri.Chapter10.haarWavelet_ae_eq_waveletFun`. -/
noncomputable def haarWavelet (x : ℝ) : ℂ :=
  Set.indicator (Ioo 0 (1 / 2)) (fun _ => (1 : ℂ)) x - Set.indicator (Ioo (1 / 2) 1) (fun _ => 1) x

/-- The Haar wavelet of Example 10.10 is equal almost everywhere to the Haar wavelet
`Haar.waveletFun 0 0` of level $0$ of `Numlib.Analysis.Wavelet.Haar`, read as a complex
function. -/
theorem haarWavelet_ae_eq_waveletFun :
    haarWavelet =ᵐ[volume] fun x => ((Haar.waveletFun 0 0 : ℝ → ℝ) x : ℂ) := by
  have h := Haar.waveletFun_eq_sub_indicator 0 0
  have hd0 : Haar.dyadic (0 + 1) (2 * 0) = Ico 0 (1 / 2) := by
    simp [Haar.dyadic]
  have hd1 : Haar.dyadic (0 + 1) (2 * 0 + 1) = Ico (1 / 2) 1 := by
    simp [Haar.dyadic]
    norm_num
  have hcoe : (Haar.waveletFun 0 0 : ℝ → ℝ) =ᵐ[volume] fun x =>
      Set.indicator (Ico 0 (1 / 2)) (fun _ => (1 : ℝ)) x
        - Set.indicator (Ico (1 / 2) 1) (fun _ => (1 : ℝ)) x := by
    rw [h]
    filter_upwards [Lp.coeFn_sub (indicatorConstLp 2 (Haar.measurableSet_dyadic (0 + 1) (2 * 0))
        (Haar.volume_dyadic_ne_top (0 + 1) (2 * 0)) (√((2 : ℝ) ^ (0 : ℤ))))
        (indicatorConstLp 2 (Haar.measurableSet_dyadic (0 + 1) (2 * 0 + 1))
          (Haar.volume_dyadic_ne_top (0 + 1) (2 * 0 + 1)) (√((2 : ℝ) ^ (0 : ℤ)))),
      indicatorConstLp_coeFn (p := 2) (hs := Haar.measurableSet_dyadic (0 + 1) (2 * 0))
        (hμs := Haar.volume_dyadic_ne_top (0 + 1) (2 * 0)) (c := √((2 : ℝ) ^ (0 : ℤ))),
      indicatorConstLp_coeFn (p := 2) (hs := Haar.measurableSet_dyadic (0 + 1) (2 * 0 + 1))
        (hμs := Haar.volume_dyadic_ne_top (0 + 1) (2 * 0 + 1)) (c := √((2 : ℝ) ^ (0 : ℤ)))]
      with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, hd0, hd1]
    simp
  -- the open and the half-open intervals differ by a null set
  have hae1 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
  have hae2 : ∀ᵐ x : ℝ, x ≠ 1 / 2 := by simp [ae_iff, measure_singleton]
  filter_upwards [hcoe, hae1, hae2] with x hx h0 hhalf
  have e1 : x ∈ Ioo (0 : ℝ) (1 / 2) ↔ x ∈ Ico (0 : ℝ) (1 / 2) := by
    simp only [mem_Ioo, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm h0), h2⟩
  have e2 : x ∈ Ioo (1 / 2 : ℝ) 1 ↔ x ∈ Ico (1 / 2 : ℝ) 1 := by
    simp only [mem_Ioo, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm hhalf), h2⟩
  rw [hx, haarWavelet]
  by_cases h1 : x ∈ Ioo (0 : ℝ) (1 / 2)
  · have h2 : x ∉ Ioo (1 / 2 : ℝ) 1 := fun h => by linarith [h1.2, h.1]
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem (e1.mp h1), Set.indicator_of_notMem h2,
      Set.indicator_of_notMem (fun h => h2 (e2.mpr h))]
    simp
  · have h1' : x ∉ Ico (0 : ℝ) (1 / 2) := fun h => h1 (e1.mpr h)
    by_cases h2 : x ∈ Ioo (1 / 2 : ℝ) 1
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1', Set.indicator_of_mem h2,
        Set.indicator_of_mem (e2.mp h2)]
      simp
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1', Set.indicator_of_notMem h2,
        Set.indicator_of_notMem (fun h => h2 (e2.mpr h))]
      simp

/-- **Example 10.10** of [quarteroni2000numerical], the Fourier transform of the Haar wavelet. For
$\nu \neq 0$,
$$\mathcal{F} h(\nu) = \frac{i e^{-i\pi\nu} (1 - \cos(\pi\nu))}{\pi\nu}.$$
In the variable $\omega = 2\pi\nu$ this is $H(\omega) = 2i e^{-i\omega/2}(1 -
\cos(\omega/2))/\omega$ for $\omega \neq 0$. Its modulus is even.

**Correction.** The book prints $4i$ in place of $2i$. Indeed $\int_0^{1/2} e^{-i\omega t} \,
dt - \int_{1/2}^1 e^{-i\omega t} \, dt = (1 - e^{-i\omega/2})^2/(i\omega)$ and $(1 -
e^{-i\omega/2})^2 = -2 e^{-i\omega/2}(1 - \cos(\omega/2))$.

The proof integrates $e^{-2\pi i\nu t}$ over $(0, 1/2)$ and $(1/2, 1)$ and uses the formula of
Euler for $\cos(\pi\nu)$. -/
theorem example_10_10 {ν : ℝ} (hν : ν ≠ 0) :
    𝓕 haarWavelet ν
      = I * Complex.exp (-(π * ν) * I) * (1 - Real.cos (π * ν)) / (π * ν) := by
  have hπν : (π : ℂ) * ν ≠ 0 := by exact_mod_cast (mul_ne_zero Real.pi_ne_zero hν)
  have hc : (-(2 * (π : ℂ) * ν)) * I ≠ 0 := by
    refine mul_ne_zero (neg_ne_zero.mpr ?_) Complex.I_ne_zero
    exact_mod_cast (by positivity : (2 * π * ν : ℝ) ≠ 0)
  -- the integrand splits into the two intervals
  have hind : (fun t : ℝ => Complex.exp (↑(-2 * π * t * ν) * I) • haarWavelet t)
      = fun t => (Ioo (0 : ℝ) (1 / 2)).indicator
            (fun t : ℝ => Complex.exp ((-(2 * (π : ℂ) * ν)) * I * t)) t
          - (Ioo (1 / 2 : ℝ) 1).indicator
            (fun t : ℝ => Complex.exp ((-(2 * (π : ℂ) * ν)) * I * t)) t := by
    funext t
    have he : Complex.exp (↑(-2 * π * t * ν) * I)
        = Complex.exp ((-(2 * (π : ℂ) * ν)) * I * t) := by
      congr 1
      push_cast
      ring
    simp only [haarWavelet, smul_eq_mul, Set.indicator_apply, mul_sub, mul_ite, mul_one, mul_zero,
      he]
  have hexp : ∀ a b : ℝ, a ≤ b → ∫ t in Ioo a b, Complex.exp ((-(2 * (π : ℂ) * ν)) * I * t)
      = (Complex.exp ((-(2 * (π : ℂ) * ν)) * I * b) - Complex.exp ((-(2 * (π : ℂ) * ν)) * I * a))
        / ((-(2 * (π : ℂ) * ν)) * I) := by
    intro a b hab
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      integral_exp_mul_complex hc]
  have hint : ∀ a b : ℝ, IntegrableOn (fun t : ℝ => Complex.exp ((-(2 * (π : ℂ) * ν)) * I * t))
      (Ioo a b) :=
    fun a b => (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  rw [Real.fourier_real_eq_integral_exp_smul, hind, integral_sub
    ((integrable_indicator_iff measurableSet_Ioo).mpr (hint _ _))
    ((integrable_indicator_iff measurableSet_Ioo).mpr (hint _ _)),
    integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioo,
    hexp 0 (1 / 2) (by norm_num), hexp (1 / 2) 1 (by norm_num)]
  -- Euler's formula at `θ = πν`
  have hcos := Complex.two_cos ((π * ν : ℝ) : ℂ)
  push_cast at hcos ⊢
  have e1 : Complex.exp (-(2 * (π : ℂ) * ν) * I * (1 / 2)) = Complex.exp (-(π * ν) * I) := by
    congr 1; ring
  have e2 : Complex.exp (-(2 * (π : ℂ) * ν) * I * 1) = Complex.exp (-(π * ν) * I) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Complex.exp (-(π * ν : ℂ) * I) * Complex.exp ((π * ν : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [e1, e2, mul_zero, Complex.exp_zero]
  field_simp
  rw [neg_mul] at hcos e3
  linear_combination (-(1 / (ν : ℂ))) * e3 - (Complex.exp (-((π : ℂ) * ν * I)) / ν) * hcos
    - (2 * Complex.exp (-((π : ℂ) * ν * I)) * (1 - Complex.cos ((π : ℂ) * ν)) / ν) * Complex.I_sq

/-- **Example 10.11** of [quarteroni2000numerical], the Morlet wavelet. For
$\omega_0 \in \mathbb{R}$ the **Morlet wavelet** is $h(x) = e^{i\omega_0 x} e^{-x^2/2}$. -/
noncomputable def morletWavelet (ω₀ : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((ω₀ * x) * I) * Real.exp (-(x ^ 2 / 2))

/-- **Example 10.11** of [quarteroni2000numerical], the Fourier transform of the Morlet wavelet. Let
$\omega_0, \nu \in \mathbb{R}$. The real part $\cos(\omega_0 x) e^{-x^2/2}$ of the Morlet
wavelet has the Fourier transform
$$\mathcal{F}\bigl(\cos(\omega_0 x) e^{-x^2/2}\bigr)(\nu) = \sqrt{\pi/2} \, \bigl(e^{-(2\pi\nu -
  \omega_0)^2/2} + e^{-(2\pi\nu + \omega_0)^2/2}\bigr).$$
In the variable $\omega = 2\pi\nu$ this is $H(\omega) = \sqrt{\pi/2} \, (e^{-(\omega -
\omega_0)^2/2} + e^{-(\omega + \omega_0)^2/2})$, which is real, positive and even.

**Correction.** The book prints the constant $\sqrt{\pi}$. The Gaussian $e^{-x^2/2}$ has the
transform $\sqrt{2\pi} e^{-\omega^2/2}$, and the formula of Euler for the cosine halves it.

The proof uses Mathlib's `fourierIntegral_gaussian`. -/
theorem example_10_11 (ω₀ ν : ℝ) :
    𝓕 (fun x : ℝ => ((Real.cos (ω₀ * x) * Real.exp (-(x ^ 2 / 2)) : ℝ) : ℂ)) ν
      = ((Real.sqrt (π / 2) * (Real.exp (-((2 * π * ν - ω₀) ^ 2 / 2))
          + Real.exp (-((2 * π * ν + ω₀) ^ 2 / 2))) : ℝ) : ℂ) := by
  have hb : (0 : ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  -- the two Gaussian integrals
  have hG : ∀ t : ℝ, ∫ x : ℝ, Complex.exp (I * t * x) * Complex.exp (-(1 / 2 : ℂ) * x ^ 2)
      = ((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(t : ℂ) ^ 2 / 2) := by
    intro t
    rw [fourierIntegral_gaussian hb (t : ℂ)]
    congr 1
    · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
      push_cast
      congr 1
      ring
    · congr 1
      ring
  have hintG : ∀ t : ℝ, Integrable fun x : ℝ =>
      Complex.exp (I * t * x) * Complex.exp (-(1 / 2 : ℂ) * x ^ 2) := by
    intro t
    have := integrable_cexp_quadratic hb (I * t) 0
    refine this.congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← Complex.exp_add]
    congr 1
    ring
  -- Euler's formula for the cosine
  have hsplit : ∀ x : ℝ, Complex.exp (↑(-2 * π * x * ν) * I)
      • ((Real.cos (ω₀ * x) * Real.exp (-(x ^ 2 / 2)) : ℝ) : ℂ)
      = (1 / 2 : ℂ) * (Complex.exp (I * ((ω₀ - 2 * π * ν : ℝ) : ℂ) * x)
          * Complex.exp (-(1 / 2 : ℂ) * x ^ 2)
        + Complex.exp (I * ((-ω₀ - 2 * π * ν : ℝ) : ℂ) * x)
          * Complex.exp (-(1 / 2 : ℂ) * x ^ 2)) := by
    intro x
    have h2cos := Complex.two_cos ((ω₀ * x : ℝ) : ℂ)
    rw [smul_eq_mul]
    push_cast at h2cos ⊢
    have : Complex.exp (-2 * (π : ℂ) * x * ν * I) = Complex.exp (-(2 * π * ν * x) * I) := by
      congr 1; ring
    rw [this]
    rw [show Complex.exp (I * (ω₀ - 2 * π * ν) * x) = Complex.exp ((ω₀ * x) * I)
          * Complex.exp (-(2 * π * ν * x) * I) by rw [← Complex.exp_add]; congr 1; ring,
      show Complex.exp (I * (-ω₀ - 2 * π * ν) * x) = Complex.exp (-(ω₀ * x) * I)
          * Complex.exp (-(2 * π * ν * x) * I) by rw [← Complex.exp_add]; congr 1; ring,
      show Complex.exp (-(1 / 2 : ℂ) * x ^ 2) = Complex.exp (-(x ^ 2 / 2)) by congr 1; ring]
    linear_combination
      (Complex.exp (-(2 * π * ν * x) * I) * Complex.exp (-(x ^ 2 / 2 : ℂ)) / 2) * h2cos
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [hsplit]
  rw [integral_const_mul, integral_add (hintG _) (hintG _), hG, hG]
  push_cast
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.div_rpow Real.pi_pos.le (by norm_num),
    Real.mul_rpow (by norm_num) Real.pi_pos.le]
  push_cast
  set s2 : ℂ := (((2 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hs2
  have h2 : s2 ≠ 0 := by
    rw [hs2]
    exact_mod_cast (Real.rpow_pos_of_pos two_pos _).ne'
  have h22 : s2 * s2 = 2 := by
    rw [hs2, ← Complex.ofReal_mul, ← Real.rpow_add two_pos]
    norm_num
  have hinv : s2⁻¹ = s2 / 2 := by
    rw [eq_div_iff two_ne_zero, ← h22]
    field_simp
  rw [show (-(((ω₀ : ℂ) - 2 * π * ν) ^ 2) / 2) = -((2 * π * ν - ω₀ : ℂ) ^ 2 / 2) by ring,
    show (-(((-ω₀ : ℂ) - 2 * π * ν) ^ 2) / 2) = -((2 * π * ν + ω₀ : ℂ) ^ 2 / 2) by ring,
    div_eq_mul_inv (((π ^ (1 / 2 : ℝ) : ℝ)) : ℂ) s2, hinv]
  ring

/-! ### Section 10.12.2: discrete and orthonormal wavelets -/

/-- **Section 10.12.2** of [quarteroni2000numerical], the discrete wavelets. Let
$h : \mathbb{R} \to \mathbb{C}$, $s_0, \tau_0 \in \mathbb{R}$ and $j, k \in \mathbb{Z}$. The
scale $s = s_0^j$ and the shift $\tau = k\tau_0 s_0^j$ give the **discrete wavelet**
$$h_{j,k}(t) = h_{s_0^j, k\tau_0 s_0^j}(t) = s_0^{-j/2} h(s_0^{-j} t - k\tau_0).$$

The book takes $s_0 > 1$. The definition is the backbone's `Wavelet.discrete`, and
`Wavelet.discrete_apply` gives the second form. -/
noncomputable def discreteWavelet (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (j k : ℤ) : ℝ → ℂ :=
  Wavelet.discrete h s₀ τ₀ j k

/-- **Section 10.12.2** of [quarteroni2000numerical], the discrete wavelet transform. Let
$h, f : \mathbb{R} \to \mathbb{C}$, $s_0, \tau_0 \in \mathbb{R}$ and $j, k \in \mathbb{Z}$. The
**discrete wavelet transform** is
$$W_f(j, k) = \int_{-\infty}^{\infty} f(t) \overline{h_{j,k}(t)} \, dt.$$

**Reading.** The book defines the transform for $f \in L^1(\mathbb{R})$. It is the $L^2$ inner
product of $h_{j,k}$ and $f$, and its natural domain is $L^2(\mathbb{R})$.

The definition is the backbone's `Wavelet.discreteTransform`. -/
noncomputable def discreteWaveletTransform (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (f : ℝ → ℂ) (j k : ℤ) : ℂ :=
  Wavelet.discreteTransform h s₀ τ₀ f j k

/-- **Section 10.12.2** of [quarteroni2000numerical]. For $h, f : \mathbb{R} \to \mathbb{C}$,
$s_0, \tau_0 \in \mathbb{R}$ and $j, k \in \mathbb{Z}$, the discrete wavelet transform samples
the continuous one: $W_f(j, k) = W_f(s_0^j, k\tau_0 s_0^j)$. -/
theorem discreteWaveletTransform_eq (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (f : ℝ → ℂ) (j k : ℤ) :
    discreteWaveletTransform h s₀ τ₀ f j k = definition_10_4 h f (s₀ ^ j) (k * τ₀ * s₀ ^ j) := rfl

/-- **Section 10.12.2** of [quarteroni2000numerical], the dyadic case. Let
$\varphi \in L^2(\mathbb{R})$ be real-valued, let $\psi$ be the wavelet `mraWavelet φ` that
$\varphi$ generates, and let $j, k \in \mathbb{Z}$. At $s_0 = 2$ and $\tau_0 = 1$ the discrete
wavelet $\psi_{j,k}$ of the book is equal almost everywhere to the element
`waveletSystem φ (-j) k` of the backbone's wavelet system, $2^{-j/2} \psi(2^{-j} t - k)$.

The level index is reversed between the two conventions. The statement holds for every
$\varphi$; it is used for the scaling function of a multiresolution analysis. The proof
specializes `Wavelet.discrete_two_one_eq_waveletSystem`. -/
theorem discreteWavelet_two_one (φ : Lp ℝ 2 (volume : Measure ℝ)) (j k : ℤ) :
    discreteWavelet (fun t => ((mraWavelet φ : ℝ → ℝ) t : ℂ)) 2 1 j k
      =ᵐ[volume] fun t => ((waveletSystem φ (-j) k : ℝ → ℝ) t : ℂ) :=
  Wavelet.discrete_two_one_eq_waveletSystem φ j k

/-- **Section 10.12.2** of [quarteroni2000numerical], orthonormal wavelet bases and the
reconstruction formula. Let $(V_j)_{j \in \mathbb{Z}}$ with the scaling function $\varphi$ be a
multiresolution analysis of $L^2(\mathbb{R})$, and let $\psi_{j,k}$ = `waveletSystem φ j k` be
its wavelet system. Then the family $(\psi_{j,k})_{(j,k) \in \mathbb{Z}^2}$ is orthonormal,
$$\int \psi_{i,j} \, \psi_{k,l} = \delta_{ik} \delta_{jl}, \qquad i, j, k, l \in \mathbb{Z},$$
and every $f \in L^2(\mathbb{R})$ is reconstructed as
$$f = A \sum_{(j,k) \in \mathbb{Z}^2} (f, \psi_{j,k}) \, \psi_{j,k}, \qquad A = 1,$$
with unconditional convergence in $L^2(\mathbb{R})$.

**Reading.** The book leaves the constant $A$ open. For an orthonormal basis it is $1$. A value
$A \neq 1$ would occur for tight frames, which the book does not introduce.

Here $L^2(\mathbb{R})$ is the space of real functions `MeasureTheory.Lp ℝ 2`, and the
multiresolution analysis is `IsMultiresolutionAnalysis V φ`. The Haar wavelet is the instance
`Haar.isMultiresolutionAnalysis`. The proof specializes
`IsMultiresolutionAnalysis.orthonormal_waveletSystem_prod` and
`IsMultiresolutionAnalysis.hasSum_inner_smul_waveletSystem`. -/
theorem orthonormalWavelet_reconstruction {V : ℤ → Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ))}
    {φ : Lp ℝ 2 (volume : Measure ℝ)} (h : IsMultiresolutionAnalysis V φ) :
    Orthonormal ℝ (fun jk : ℤ × ℤ => waveletSystem φ jk.1 jk.2) ∧
      ∀ f : Lp ℝ 2 (volume : Measure ℝ),
        HasSum (fun jk : ℤ × ℤ =>
          (inner ℝ (waveletSystem φ jk.1 jk.2) f) • waveletSystem φ jk.1 jk.2) f :=
  ⟨h.orthonormal_waveletSystem_prod, h.hasSum_inner_smul_waveletSystem⟩

end QuarteroniSaccoSaleri.Chapter10
