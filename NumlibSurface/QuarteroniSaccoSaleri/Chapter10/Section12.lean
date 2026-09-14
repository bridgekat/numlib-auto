import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Numlib.Analysis.Wavelet.ContinuousTransform

/-!
# Quarteroni–Sacco–Saleri §10.12: the wavelet transform

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.12.

The wavelets `h_{s,τ}(t) = s^{-1/2} h((t − τ)/s)` generated from an elementary wavelet by
translations and dilations (10.85) and their Fourier transform (10.86), the continuous wavelet
transform (Definition 10.4, (10.87)) and its expression on the Fourier side as a bank of filters,
the Heisenberg inequality (10.88), the Haar (Example 10.10) and Morlet (Example 10.11) wavelets,
and the discrete and orthonormal wavelets of §10.12.2 with the reconstruction formula.

The continuous side is `Numlib/Analysis/Wavelet/ContinuousTransform`; the discrete side at the
dyadic parameters `s₀ = 2`, `τ₀ = 1` is `Numlib/Analysis/Wavelet/{Multiresolution, Haar}`, with the
level index reversed (`j ↦ −j`) between the book's `s₀^{-j/2} h(s₀^{-j} t − k)` and the backbone's
`2^{j/2} ψ(2^j x − k)`. The book writes its transforms in the variable `ω = 2πν`; the statements
below are in the frequency `ν` of Mathlib's `𝓕`.

## Main definitions

* `wavelet h s τ` — `h_{s,τ}` (10.85).
* `definition_10_4 h f s τ` — the continuous wavelet transform `W_f(s, τ)`.
* `haarWavelet`, `morletWavelet ω₀` — the elementary wavelets of Examples 10.10–10.11.
* `discreteWavelet h s₀ τ₀ j k`, `discreteWaveletTransform h s₀ τ₀ f j k` — §10.12.2.

## Main results

* `equation_10_86` — the filter `𝓕 h_{s,τ}(ν) = √s 𝓕h(sν) e^{-2πiντ}`.
* `definition_10_4_eq_inner`, `continuousTransform_eq_integral_fourier` — `W_f(s, τ)` as the `L²`
  inner product `⟪h_{s,τ}, f⟫` and as a bank of filters on the Fourier side.
* `example_10_10`, `example_10_11` — the transforms of the Haar wavelet and of the real part of the
  Morlet wavelet.
* `discreteWavelet_two_one`, `orthonormalWavelet_reconstruction` — the dyadic discrete wavelets
  of a multiresolution analysis are its `waveletSystem`, orthonormal, and reconstruct every
  `f ∈ L²(ℝ)` with the constant `A = 1`.

## Errata

* Example 10.10: the transform of the Haar wavelet is `2i e^{-iω/2}(1 − cos(ω/2))/ω`, not
  `4i e^{-iω/2}(1 − cos(ω/2))/ω`:
  `∫_0^{1/2} e^{-iωt} dt − ∫_{1/2}^1 e^{-iωt} dt = (1 − e^{-iω/2})²/(iω)` and
  `(1 − e^{-iω/2})² = −2 e^{-iω/2}(1 − cos(ω/2))`.
* Example 10.11: the constant is `√(π/2)`, not `√π`: the Gaussian `e^{-x²/2}` transforms to
  `√(2π) e^{-ω²/2}`, and Euler's formula halves it.
* §10.12.2 defines the discrete wavelet transform "for `f ∈ L¹(ℝ)`"; it is the `L²` inner product
  and lives on `L²(ℝ)`. The reconstruction constant `A` is `1` for an orthonormal basis.

## Not formalized

The Heisenberg inequality (10.88): the book defines neither `Δt` nor `Δω`, and Mathlib has no
uncertainty principle (`equation_10_88` stays an open node of the plan with the reason). The
bandwidth and quality-factor discussion after Example 10.11 is prose.
-/

open MeasureTheory Filter Topology Complex Set

open scoped FourierTransform ComplexConjugate Real

namespace QuarteroniSaccoSaleri.Chapter10

/-! ### (10.85)–(10.87): wavelets and the continuous wavelet transform -/

/-- **(10.85), the wavelet** `h_{s,τ}(t) = s^{-1/2} h((t − τ)/s)` obtained from the elementary
wavelet `h ∈ L²(ℝ)` by the translation `τ` and the dilation `s > 0`: the backbone's
`Wavelet.dilateTranslate`. -/
noncomputable def wavelet (h : ℝ → ℂ) (s τ : ℝ) : ℝ → ℂ := Wavelet.dilateTranslate h s τ

theorem wavelet_apply (h : ℝ → ℂ) (s τ t : ℝ) :
    wavelet h s τ t = (Real.sqrt s : ℂ)⁻¹ * h ((t - τ) / s) := rfl

/-- **(10.86), the filter of the wavelet transform.** In the variable `ω = 2πν`, the Fourier
transform of `h_{s,τ}` is `H_{s,τ}(ω) = √s H(sω) e^{-iωτ}`, that is
`𝓕 h_{s,τ}(ν) = √s 𝓕h(sν) e^{-2πiντ}`: a dilation `t/s` in time is a contraction `sω` in
frequency, so `1/s` plays the role of the frequency (the *scale*). The backbone's
`Wavelet.fourier_dilateTranslate`. -/
theorem equation_10_86 (h : ℝ → ℂ) {s : ℝ} (hs : 0 < s) (τ ν : ℝ) :
    𝓕 (wavelet h s τ) ν = Real.sqrt s * 𝓕 h (s * ν) * Complex.exp (-(2 * π * ν * τ) * I) :=
  Wavelet.fourier_dilateTranslate hs τ ν

/-- **Definition 10.4, (10.87).** The continuous wavelet transform of `f ∈ L²(ℝ)` with respect
to the elementary wavelet `h`, `W_f(s, τ) = ∫ f(t) conj (h_{s,τ}(t)) dt`, a function of the
scale `s` and the time shift `τ` — the *time-scale representation* of `f`. The backbone's
`Wavelet.continuousTransform`. -/
noncomputable def definition_10_4 (h f : ℝ → ℂ) (s τ : ℝ) : ℂ :=
  ∫ t : ℝ, f t * conj (wavelet h s τ t)

/-- The book's continuous wavelet transform is the backbone's `Wavelet.continuousTransform`. -/
theorem definition_10_4_eq_continuousTransform (h f : ℝ → ℂ) (s τ : ℝ) :
    definition_10_4 h f s τ = Wavelet.continuousTransform h f s τ := rfl

/-- For `f, h ∈ L²(ℝ)`, `W_f(s, τ)` is the inner product `⟪h_{s,τ}, f⟫_{L²}` in Mathlib's
convention (conjugate-linear in the first argument) — the book's `(f, h_{s,τ})`. -/
theorem definition_10_4_eq_inner {h f : ℝ → ℂ} (hh : MemLp h 2) (hf : MemLp f 2) {s : ℝ}
    (hs : 0 < s) (τ : ℝ) :
    definition_10_4 h f s τ
      = inner ℂ ((Wavelet.memLp_dilateTranslate hh hs τ).toLp _) (hf.toLp f) :=
  Wavelet.continuousTransform_eq_inner hh hf hs τ

/-- **The wavelet transform as a bank of filters** (the unnumbered formula after (10.88)): for
`f, h ∈ L¹ ∩ L²` and `s > 0`, `W_f(s, τ) = √s ∫ 𝓕f(ν) conj (𝓕h(sν)) e^{2πiντ} dν` — the book's
`(√s/2π) ∫ F(ω) conj (H(sω)) e^{iωτ} dω` in `ω = 2πν`. Plancherel's identity applied to `h_{s,τ}`
and `f` with (10.86): the backbone's `Wavelet.continuousTransform_eq_integral_fourier`. -/
theorem continuousTransform_eq_integral_fourier {h f : ℝ → ℂ} (hh1 : MemLp h 1) (hh2 : MemLp h 2)
    (hf1 : MemLp f 1) (hf2 : MemLp f 2) {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    definition_10_4 h f s τ
      = Real.sqrt s * ∫ ν, 𝓕 f ν * conj (𝓕 h (s * ν)) * Complex.exp ((2 * π * ν * τ) * I) :=
  Wavelet.continuousTransform_eq_integral_fourier hh1 hh2 hf1 hf2 hs τ

/-! ### Examples 10.10–10.11 -/

/-- **The Haar wavelet** of Example 10.10: `h = 1` on `(0, 1/2)`, `−1` on `(1/2, 1)`, `0`
otherwise. Up to a null set it is the function underlying the backbone's `Haar.waveletFun 0 0`
(`haarWavelet_ae_eq_waveletFun`). -/
noncomputable def haarWavelet (x : ℝ) : ℂ :=
  Set.indicator (Ioo 0 (1 / 2)) (fun _ => (1 : ℂ)) x - Set.indicator (Ioo (1 / 2) 1) (fun _ => 1) x

/-- The Haar wavelet of Example 10.10 is, almost everywhere, the level-`0` Haar wavelet of
`Numlib/Analysis/Wavelet/Haar`. -/
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

/-- **Example 10.10, the Haar wavelet.** Its Fourier transform, in the variable `ω = 2πν`, is
`H(ω) = 2i e^{-iω/2}(1 − cos(ω/2))/ω` for `ω ≠ 0`, i.e. `𝓕 h(ν) = i e^{-iπν}(1 − cos(πν))/(πν)`,
whose modulus is even. Erratum: the book prints `4i` for `2i`. Direct integration of `e^{-2πiνt}`
over `(0, 1/2)` and `(1/2, 1)`, and Euler's formula for `cos(πν)`. -/
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

/-- **The Morlet wavelet** of Example 10.11, `h(x) = e^{iω₀x} e^{-x²/2}`. -/
noncomputable def morletWavelet (ω₀ : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((ω₀ * x) * I) * Real.exp (-(x ^ 2 / 2))

/-- **Example 10.11, the Morlet wavelet.** The real part `cos(ω₀x) e^{-x²/2}` of the Morlet
wavelet has the real, positive, even Fourier transform
`H(ω) = √(π/2) (e^{-(ω−ω₀)²/2} + e^{-(ω+ω₀)²/2})` in the variable `ω = 2πν`. Erratum: the book
prints `√π`; the Gaussian `e^{-x²/2}` transforms to `√(2π) e^{-ω²/2}` and Euler's formula halves
it. Mathlib's `fourierIntegral_gaussian`. -/
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

/-! ### §10.12.2: discrete and orthonormal wavelets -/

/-- **The discrete wavelets (§10.12.2).** For `s₀ > 1` and `τ₀ ∈ ℝ`, the scale `s = s₀^j` and
the shift `τ = k τ₀ s₀^j`, `j, k ∈ ℤ`, give `h_{j,k}(t) = s₀^{-j/2} h(s₀^{-j} t − k τ₀)`: the
backbone's `Wavelet.discrete`, whose `Wavelet.discrete_apply` is this second form. -/
noncomputable def discreteWavelet (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (j k : ℤ) : ℝ → ℂ :=
  Wavelet.discrete h s₀ τ₀ j k

/-- **The discrete wavelet transform (§10.12.2)**, `W_f(j, k) = ∫ f(t) conj (h_{j,k}(t)) dt` — on
`L²(ℝ)`, where it is the inner product `⟪h_{j,k}, f⟫` (the book says `L¹`). -/
noncomputable def discreteWaveletTransform (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (f : ℝ → ℂ) (j k : ℤ) : ℂ :=
  Wavelet.discreteTransform h s₀ τ₀ f j k

/-- The discrete wavelet transform samples the continuous one at `s = s₀^j`, `τ = k τ₀ s₀^j`. -/
theorem discreteWaveletTransform_eq (h : ℝ → ℂ) (s₀ τ₀ : ℝ) (f : ℝ → ℂ) (j k : ℤ) :
    discreteWaveletTransform h s₀ τ₀ f j k = definition_10_4 h f (s₀ ^ j) (k * τ₀ * s₀ ^ j) := rfl

/-- **The dyadic case.** At `s₀ = 2`, `τ₀ = 1`, the discrete wavelets of the wavelet
`ψ = mraWavelet φ` of a multiresolution analysis are the `waveletSystem φ (−j) k` of
`Numlib/Analysis/Wavelet/Multiresolution`, almost everywhere — the level index is reversed between
the two conventions. The backbone's `Wavelet.discrete_two_one_eq_waveletSystem`. -/
theorem discreteWavelet_two_one (φ : Lp ℝ 2 (volume : Measure ℝ)) (j k : ℤ) :
    discreteWavelet (fun t => ((mraWavelet φ : ℝ → ℝ) t : ℂ)) 2 1 j k
      =ᵐ[volume] fun t => ((waveletSystem φ (-j) k : ℝ → ℝ) t : ℂ) :=
  Wavelet.discrete_two_one_eq_waveletSystem φ j k

/-- **Orthonormal wavelet bases and the reconstruction formula (§10.12.2).** For the wavelet of a
multiresolution analysis `V, φ`, the dyadic family `h_{j,k} = waveletSystem φ j k` is orthonormal,
`∫ h_{i,j} conj (h_{k,l}) = δ_{ik} δ_{jl}` for all `i, j, k, l ∈ ℤ`, and every `f ∈ L²(ℝ)` is
reconstructed as `f = A ∑_{j,k} W_f(j,k) h_{j,k}` with `A = 1` — the constant is `1` for an
orthonormal basis (`A ≠ 1` would occur for tight frames, which the book does not introduce). The
Haar wavelet is the instance `Haar.isMultiresolutionAnalysis`. The backbone's
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
