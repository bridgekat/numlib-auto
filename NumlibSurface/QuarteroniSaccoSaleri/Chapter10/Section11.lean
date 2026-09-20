import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Numlib.Analysis.Convolution.Bochner
import Numlib.Analysis.Fourier.FourierIntegral
import Numlib.Analysis.Fourier.Periodisation
import Numlib.Analysis.SpecialFunctions.LaplaceTransform

/-!
# Quarteroni–Sacco–Saleri §10.11: transforms and their applications

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.11.

The Fourier transform (Definition 10.1), the inversion theorem (Property 10.3) and the five
properties (10.75)–(10.77) with Examples 10.5–10.6; linear time-invariant systems, the transfer
function (10.81), the ideal low-pass filter (Example 10.7) and the sampling formula (10.82); the
Laplace transform (Definition 10.2), the unit step (Example 10.8), the region of convergence
(Property 10.4) and the transform of a derivative (Example 10.9); the Z-transform
(Definition 10.3) and the discrete Laplace transform (10.84).

The book's Fourier transform `F(ν) = ∫ f(t) e^{-2πiνt} dt` is exactly Mathlib's `𝓕 f`
(`Real.fourierIntegral`), with no renormalization (`definition_10_1_eq_fourierIntegral`). The
Laplace and Z transforms are `Numlib/Analysis/SpecialFunctions/LaplaceTransform`, where the Laplace
transform is the limit of the truncated integrals, as in Definition 10.2, and the Fourier facts the
book uses that Mathlib does not state are `Numlib/Analysis/Fourier/FourierIntegral` and
`Numlib/Analysis/Fourier/Periodisation`.

## Main definitions

* `definition_10_1 f`, `definition_10_1_inv F` — the Fourier transform and its inverse in the
  book's form, with `definition_10_1_eq_fourierIntegral` and
  `definition_10_1_inv_eq_fourierIntegralInv`.
* `equation_10_77 f g` — the convolution `(f ⋆ g)(t) = ∫ f(τ) g(t − τ) dτ`.
* `definition_10_2 f s`, `laplace f s` — the existence of the Laplace integral and the Laplace
  transform, with `definition_10_2_iff`, `laplace_eq_laplaceTransform` and the Fourier relation
  `definition_10_2_fourier`.
* `definition_10_3 f Δt z` — the Z-transform.

## Main results

* `property_10_3` — the inversion theorem: `g = 𝓕⁻¹ F` is continuous, tends to `0` at infinity,
  equals `f` almost everywhere and at every continuity point of `f`.
* `equation_10_75`, `property_scaling`, `property_duality`, `property_parity`, `equation_10_76` —
  properties 1–5.
* `example_10_5_rect`, `example_10_5_saw`, `example_10_6` — the transforms of the rectangle, of
  the sawtooth, and of the constant and the cosine as Dirac masses.
* `equation_10_80` — a bounded operator on `L¹(ℝ)` commuting with every translation commutes
  with every convolution, `S(f ⋆ g) = f ⋆ S(g)`; the shift-invariant linear system, with the
  continuity the book's argument silently needs.
* `equation_10_81`, `example_10_7`, `equation_10_82` — the transfer function, the ideal low-pass
  filter, and the sampling (aliasing) formula.
* `example_10_8`, `property_10_4`, `example_10_9`, `example_10_9_solution` — the unit step, the
  region of convergence, and the transform of `y' + a y = g`.
* `definition_10_3_summable`, `definition_10_3_eq_discreteLaplace` — the root test and the
  identification of the Z-transform with the discrete Laplace transform.

## Errata

* (10.76), second identity, is stated for `f, g ∈ L¹` alone; `𝓕 f ⋆ 𝓕 g` need not exist. It holds
  when moreover `𝓕 g ∈ L¹` (`Real.fourier_mul_eq_convolution`).
* §10.11.3 writes `L(s) = F(e^{-σt} f̃)` without an argument; it is `𝓕(e^{-σt} f̃)(ω/2π)` in the
  `e^{-2πiνt}` convention of Definition 10.1.
* §10.11.4: the substitution relating the Z-transform to the discrete Laplace transform is
  `z = e^{sΔt}`, not `e^{-sΔt}`.
* The Cauchy–Hadamard radius `R = limsup |f(nΔt)|^{1/n}` must be read in `[0, ∞]`.

* (10.80), `S(f ⋆ g) = f ⋆ S(g)` for a "linear shift-invariant system" `S`, is not a
  mathematical statement as printed (no domain, no continuity of `S`), and "an immediate
  consequence of the linearity and shift-invariance" is not a proof: the convolution is an
  integral of translates, which only a *continuous* `S` passes through. `equation_10_80` takes
  `S` bounded on `L¹(ℝ)` and commuting with the translations, and proves the identity from the
  Bochner-integral reading of the convolution (`Numlib.Analysis.Convolution.Bochner`); its
  consequences (10.81) are stated for a system *given* as a convolution.

## Not formalized

The second claim of Example 10.7 (the spectrum of the output is `I H`) is (10.81) with `h ∉ L¹`,
and is not stated.
-/

open MeasureTheory Filter Topology Complex Set

open scoped FourierTransform ComplexConjugate Real Convolution

namespace QuarteroniSaccoSaleri.Chapter10

/-! ### Definition 10.1: the Fourier transform -/

/-- **Definition 10.1.** For `f ∈ L¹(ℝ)`, the Fourier transform of `f` is
`F(ν) = ∫_{-∞}^{∞} f(t) e^{-2πiνt} dt`, `ν ∈ ℝ`; the inverse transform is `definition_10_1_inv`.
This is Mathlib's `𝓕 f` (`definition_10_1_eq_fourierIntegral`). -/
noncomputable def definition_10_1 (f : ℝ → ℂ) (ν : ℝ) : ℂ :=
  ∫ t : ℝ, f t * Complex.exp (-(2 * π * ν * t) * I)

/-- The inverse Fourier transform of Definition 10.1, `f(t) = ∫ F(ν) e^{2πiνt} dν`. -/
noncomputable def definition_10_1_inv (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ν : ℝ, F ν * Complex.exp ((2 * π * ν * t) * I)

/-- The book's transform is Mathlib's `𝓕`, with no renormalization. -/
theorem definition_10_1_eq_fourierIntegral (f : ℝ → ℂ) : definition_10_1 f = 𝓕 f := by
  funext ν
  rw [definition_10_1, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- The book's inverse transform is Mathlib's `𝓕⁻`. -/
theorem definition_10_1_inv_eq_fourierIntegralInv (F : ℝ → ℂ) : definition_10_1_inv F = 𝓕⁻ F := by
  funext t
  rw [definition_10_1_inv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-! ### Property 10.3: the inversion theorem -/

/-- **Property 10.3 (inversion theorem).** Let `f ∈ L¹(ℝ)` with `F = 𝓕 f ∈ L¹(ℝ)`, and let
`g(t) = ∫ F(ν) e^{2πiνt} dν`. Then `g` is continuous, `g(t) → 0` as `t → ±∞`, and `f = g` almost
everywhere; at every continuity point `t` of `f`, `f(t) = g(t)`. The Cauchy principal value of the
book is the Bochner integral since `F ∈ L¹`. Continuity is `Real.continuous_fourierIntegralInv`,
the decay is the Riemann–Lebesgue lemma `Real.zero_at_infty_fourier`, the almost-everywhere
equality is `Real.ae_eq_fourierInv_fourier`, and the pointwise one is Mathlib's
`MeasureTheory.Integrable.fourierInv_fourier_eq`. -/
theorem property_10_3 {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (definition_10_1 f)) :
    Continuous (definition_10_1_inv (definition_10_1 f)) ∧
      Tendsto (definition_10_1_inv (definition_10_1 f)) (cocompact ℝ) (𝓝 0) ∧
      f =ᵐ[volume] definition_10_1_inv (definition_10_1 f) ∧
      ∀ t, ContinuousAt f t → definition_10_1_inv (definition_10_1 f) t = f t := by
  rw [definition_10_1_eq_fourierIntegral] at hF ⊢
  rw [definition_10_1_inv_eq_fourierIntegralInv]
  refine ⟨Real.continuous_fourierIntegralInv hF, ?_, Real.ae_eq_fourierInv_fourier hf hF,
    fun t ht => hf.fourierInv_fourier_eq hF ht⟩
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact Real.zero_at_infty_fourier _

/-! ### Properties 1–5 -/

/-- **(10.75), property 1 (linearity).** For integrable `f, g` and `α, β ∈ ℂ`,
`𝓕(αf + βg) = α 𝓕 f + β 𝓕 g`, and likewise for the inverse transform. -/
theorem equation_10_75 {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (α β : ℂ) (ν : ℝ) :
    𝓕 (fun t => α * f t + β * g t) ν = α * 𝓕 f ν + β * 𝓕 g ν ∧
      𝓕⁻ (fun t => α * f t + β * g t) ν = α * 𝓕⁻ f ν + β * 𝓕⁻ g ν := by
  have hlin : ∀ w : ℝ, 𝓕 (fun t => α * f t + β * g t) w = α * 𝓕 f w + β * 𝓕 g w := by
    intro w
    have h1 : (fun t => α * f t + β * g t) = (fun t => α • f t) + fun t => β • g t := by
      funext t
      simp [smul_eq_mul]
    have h2 : 𝓕 ((fun t => α • f t) + fun t => β • g t) w
        = 𝓕 (fun t => α • f t) w + 𝓕 (fun t => β • g t) w :=
      congrFun (VectorFourier.fourierIntegral_add (L := innerₗ ℝ) Real.continuous_fourierChar
        continuous_inner (hf.smul α) (hg.smul β)) w
    rw [h1, h2, Real.fourierIntegral_const_smul, Real.fourierIntegral_const_smul, smul_eq_mul,
      smul_eq_mul]
  refine ⟨hlin ν, ?_⟩
  simp only [Real.fourierInv_eq_fourier_neg]
  exact hlin (-ν)

/-- **Property 2 (scaling).** For `α ≠ 0` and `f_α(t) = f(αt)`, `𝓕 f_α(ν) = |α|⁻¹ 𝓕 f(ν/α)`.
The backbone's `Real.fourierIntegral_comp_mul_left`. -/
theorem property_scaling {α : ℝ} (hα : α ≠ 0) (f : ℝ → ℂ) (ν : ℝ) :
    𝓕 (fun t => f (α * t)) ν = ((|α|⁻¹ : ℝ) : ℂ) * 𝓕 f (ν / α) := by
  rw [Real.fourierIntegral_comp_mul_left hα, Complex.real_smul]

/-- **Property 3 (duality).** If `f` is continuous and integrable with `𝓕 f` integrable, then
`g(t) = 𝓕 f(−t)` has Fourier transform `𝓕 g = f`. The book states it with no hypotheses; the
continuity (or the almost-everywhere equality of Property 10.3) is needed. Mathlib's
`fourierInv_eq_fourier_comp_neg` and `Continuous.fourierInv_fourier_eq`. -/
theorem property_duality {f : ℝ → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hF : Integrable (𝓕 f)) :
    𝓕 (fun t => 𝓕 f (-t)) = f := by
  rw [← Real.fourierInv_eq_fourier_comp_neg]
  exact hc.fourierInv_fourier_eq hf hF

/-- **Property 4 (parity).** If `f` is real-valued, integrable and even then `𝓕 f` is real-valued
and even; if `f` is real-valued, integrable and odd then `𝓕 f` is purely imaginary and odd. The
backbone's `Real.fourierIntegral_even_real` and `Real.fourierIntegral_odd_real`. -/
theorem property_parity {f : ℝ → ℝ} (hf : Integrable f) (ν : ℝ) :
    ((∀ t, f (-t) = f t) →
        (𝓕 (fun t => (f t : ℂ)) ν).im = 0 ∧
          𝓕 (fun t => (f t : ℂ)) (-ν) = 𝓕 (fun t => (f t : ℂ)) ν) ∧
      ((∀ t, f (-t) = -f t) →
        (𝓕 (fun t => (f t : ℂ)) ν).re = 0 ∧
          𝓕 (fun t => (f t : ℂ)) (-ν) = -𝓕 (fun t => (f t : ℂ)) ν) :=
  ⟨fun heven => Real.fourierIntegral_even_real hf heven ν,
    fun hodd => Real.fourierIntegral_odd_real hf hodd ν⟩

/-- **(10.77), the convolution** `(f ⋆ g)(t) = ∫_{-∞}^{∞} f(τ) g(t − τ) dτ`; Mathlib's
`MeasureTheory.convolution` with the multiplication of `ℂ` (`equation_10_77_eq_convolution`). -/
noncomputable def equation_10_77 (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ τ : ℝ, f τ * g (t - τ)

theorem equation_10_77_eq_convolution (f g : ℝ → ℂ) :
    equation_10_77 f g = f ⋆[ContinuousLinearMap.mul ℂ ℂ] g := rfl

/-- The convolution (10.77) of two functions of `L¹(ℝ)` is in `L¹(ℝ)`
(`MeasureTheory.Integrable.integrable_convolution`). -/
theorem equation_10_77_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (equation_10_77 f g) := by
  rw [equation_10_77_eq_convolution]
  exact hf.integrable_convolution _ hg

/-- **(10.76), property 5 (convolution and product).** For `f, g ∈ L¹(ℝ)`, `𝓕(f ⋆ g) = 𝓕 f · 𝓕 g`
(Mathlib's `Real.fourier_mul_convolution_eq`); and `𝓕(f g) = 𝓕 f ⋆ 𝓕 g` when moreover
`𝓕 g ∈ L¹(ℝ)` (`Real.fourier_mul_eq_convolution`) — the book states the second identity for
`f, g ∈ L¹` alone, which is insufficient. -/
theorem equation_10_76 {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∀ ν, 𝓕 (equation_10_77 f g) ν = 𝓕 f ν * 𝓕 g ν) ∧
      (Integrable (𝓕 g) → 𝓕 (fun t => f t * g t) = equation_10_77 (𝓕 f) (𝓕 g)) := by
  refine ⟨fun ν => ?_, fun hG => ?_⟩
  · rw [equation_10_77_eq_convolution]
    exact Real.fourier_mul_convolution_eq hf hg ν
  · rw [equation_10_77_eq_convolution]
    exact Real.fourier_mul_eq_convolution hf hg hG

/-! ### Examples 10.5–10.7 and the transfer function -/

/-- The transform of the indicator of an interval `[-a, a]` at `ν ≠ 0`, the computation behind
Example 10.5: `∫_{-a}^{a} e^{-2πiνt} dt = sin(2πνa)/(πν)`. -/
theorem fourierIntegral_indicator_Icc {a : ℝ} (ha : 0 < a) {ν : ℝ} (hν : ν ≠ 0) :
    𝓕 (Set.indicator (Icc (-a) a) fun _ => (1 : ℂ)) ν
      = ((Real.sin (2 * π * ν * a) / (π * ν) : ℝ) : ℂ) := by
  have h2πν : (2 * π * ν : ℝ) ≠ 0 := by positivity
  have hc : (-(2 * (π : ℂ) * ν)) * I ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast h2πν)) Complex.I_ne_zero
  have hind : (fun v : ℝ => Complex.exp (↑(-2 * π * v * ν) * I)
      • (Icc (-a) a).indicator (fun _ => (1 : ℂ)) v)
      = (Icc (-a) a).indicator fun v : ℝ => Complex.exp ((-(2 * (π : ℂ) * ν)) * I * v) := by
    funext v
    by_cases hv : v ∈ Icc (-a) a
    · simp only [Set.indicator_of_mem hv, smul_eq_mul, mul_one]
      congr 1
      push_cast
      ring
    · simp [Set.indicator_of_notMem hv]
  rw [Real.fourier_real_eq_integral_exp_smul, hind, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_exp_mul_complex hc]
  have h2sin := Complex.two_sin ((2 * π * ν * a : ℝ) : ℂ)
  have hπν : (π : ℂ) * ν ≠ 0 := by exact_mod_cast (mul_ne_zero Real.pi_ne_zero hν)
  push_cast at h2sin ⊢
  rw [show (-(2 * ↑π * ↑ν) * I * ↑a : ℂ) = -(2 * π * ν * a) * I by ring,
    show (-(2 * ↑π * ↑ν) * I * -↑a : ℂ) = (2 * π * ν * a) * I by ring]
  field_simp
  rw [show -(2 * (π : ℂ) * ν * a * I) = -(2 * π * ν * a) * I by ring]
  linear_combination (-I / ν) * h2sin
    - ((Complex.exp (-(2 * π * ν * a) * I) - Complex.exp ((2 * π * ν * a) * I)) / ν) * Complex.I_sq

/-- **Example 10.5, the rectangular function.** For `A, T > 0` and `r = A · 1_{[-T/2, T/2]}`,
`𝓕 r(ν) = A T sin(πνT)/(πνT)` for `ν ≠ 0`, and `𝓕 r(0) = A T`. -/
theorem example_10_5_rect {A T : ℝ} (hT : 0 < T) (ν : ℝ) :
    (ν ≠ 0 → 𝓕 (fun t => (A : ℂ) * Set.indicator (Icc (-(T / 2)) (T / 2)) (fun _ => (1 : ℂ)) t) ν
        = ((A * T * (Real.sin (π * ν * T) / (π * ν * T)) : ℝ) : ℂ)) ∧
      𝓕 (fun t => (A : ℂ) * Set.indicator (Icc (-(T / 2)) (T / 2)) (fun _ => (1 : ℂ)) t) 0
        = ((A * T : ℝ) : ℂ) := by
  have hsmul : ∀ ν, 𝓕 (fun t => (A : ℂ) * Set.indicator (Icc (-(T / 2)) (T / 2))
      (fun _ => (1 : ℂ)) t) ν
      = (A : ℂ) * 𝓕 (Set.indicator (Icc (-(T / 2)) (T / 2)) fun _ => (1 : ℂ)) ν := by
    intro ν
    have := Real.fourierIntegral_const_smul (A : ℂ)
      (Set.indicator (Icc (-(T / 2)) (T / 2)) fun _ => (1 : ℂ)) ν
    simpa [smul_eq_mul] using this
  refine ⟨fun hν => ?_, ?_⟩
  · rw [hsmul, fourierIntegral_indicator_Icc (by positivity) hν,
      show 2 * π * ν * (T / 2) = π * ν * T by ring]
    have hπν : π * ν * T ≠ 0 := by positivity
    have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
    push_cast
    field_simp
  · rw [hsmul, Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_smul]
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith : -(T / 2) ≤ T / 2), Complex.real_smul, mul_one]
    push_cast
    ring

/-- **Example 10.5, the sawtooth function.** For `A, T > 0`, the transform of `s(t) = 2At/T` on
`[-T/2, T/2]`, `0` elsewhere, is `𝓕 s(ν) = i (A T/(πνT)) (cos(πνT) − sin(πνT)/(πνT))` for `ν ≠ 0`,
purely imaginary and odd. The primitive `e^{-2πiνt}(it/(2πν) + 1/(4π²ν²))` of `t e^{-2πiνt}` and
Euler's formulas. -/
theorem example_10_5_saw {A T : ℝ} (hT : 0 < T) {ν : ℝ} (hν : ν ≠ 0) :
    𝓕 (fun t => Set.indicator (Icc (-(T / 2)) (T / 2)) (fun t : ℝ => ((2 * A * t / T : ℝ) : ℂ)) t) ν
      = I * ((A * T / (π * ν * T) : ℝ) : ℂ)
          * ((Real.cos (π * ν * T) - Real.sin (π * ν * T) / (π * ν * T) : ℝ) : ℂ) := by
  set ω : ℝ := 2 * π * ν with hω
  have hω0 : ω ≠ 0 := by positivity
  have hωC : (ω : ℂ) ≠ 0 := by exact_mod_cast hω0
  -- the primitive of `t e^{-iωt}`
  set F : ℝ → ℂ := fun t => Complex.exp (-(ω * t) * I) * (I * t / ω + 1 / ω ^ 2) with hF
  have hF' : ∀ t : ℝ, HasDerivAt F (t * Complex.exp (-(ω * t) * I)) t := by
    intro t
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(ω * z) * I))
        (Complex.exp (-(ω * t) * I) * (-(ω * 1) * I)) (t : ℂ) :=
      (((hasDerivAt_id (t : ℂ)).const_mul (ω : ℂ)).neg.mul_const I).cexp
    have h1' : HasDerivAt (fun t : ℝ => Complex.exp (-(ω * t) * I))
        (Complex.exp (-(ω * t) * I) * (-(ω : ℂ) * I)) t :=
      (h1.comp_ofReal).congr_deriv (by ring)
    have h2 : HasDerivAt (fun z : ℂ => I * z / ω + 1 / ω ^ 2) (I * 1 / ω) (t : ℂ) :=
      (((hasDerivAt_id (t : ℂ)).const_mul I).div_const (ω : ℂ)).add_const _
    have h2' : HasDerivAt (fun t : ℝ => (I * t / ω + 1 / ω ^ 2 : ℂ)) (I / ω) t :=
      (h2.comp_ofReal).congr_deriv (by ring)
    refine (h1'.mul h2').congr_deriv ?_
    field_simp
    linear_combination (-(ω : ℂ) * t) * Complex.I_sq
  have hind : (fun v : ℝ => Complex.exp (↑(-2 * π * v * ν) * I) • (Icc (-(T / 2)) (T / 2)).indicator
      (fun t : ℝ => ((2 * A * t / T : ℝ) : ℂ)) v)
      = (Icc (-(T / 2)) (T / 2)).indicator fun t : ℝ =>
          ((2 * A / T : ℝ) : ℂ) * (t * Complex.exp (-(ω * t) * I)) := by
    funext v
    by_cases hv : v ∈ Icc (-(T / 2)) (T / 2)
    · simp only [Set.indicator_of_mem hv, smul_eq_mul, hω]
      push_cast
      ring_nf
    · simp [Set.indicator_of_notMem hv]
  rw [Real.fourier_real_eq_integral_exp_smul, hind, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF' t)
      ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  simp only [hF]
  -- Euler's formulas at `θ = πνT = ω T/2`
  have hcos := Complex.two_cos ((π * ν * T : ℝ) : ℂ)
  have hsin := Complex.two_sin ((π * ν * T : ℝ) : ℂ)
  have hπνT : (π * ν * T : ℂ) ≠ 0 := by exact_mod_cast (by positivity : π * ν * T ≠ 0)
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [hω] at hωC ⊢
  push_cast at hωC hcos hsin ⊢
  rw [show (-(2 * (π : ℂ) * ν * (T / 2)) * I) = -(π * ν * T) * I by ring,
    show (-(2 * (π : ℂ) * ν * -(T / 2)) * I) = (π * ν * T) * I by ring]
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  field_simp
  ring_nf at hcos hsin ⊢
  linear_combination (-(A : ℂ) * (π * ν * T) * I) * hcos + ((A : ℂ) * I) * hsin
    + ((A : ℂ) * (Complex.exp (-((π : ℂ) * ν * T * I)) - Complex.exp ((π : ℂ) * ν * T * I)))
        * Complex.I_sq

/-- **Example 10.6, (10.78)–(10.79).** As tempered distributions, the Fourier transform of the
constant `A` is `A δ_0`, and that of `A cos(2πν₀t)` is `(A/2)(δ_{ν₀} + δ_{-ν₀})`, where `δ_a` is the
Dirac mass `⟨δ_a, φ⟩ = φ(a)` (Mathlib's `TemperedDistribution.delta`). Pairing with a Schwartz `φ`:
`⟨𝓕 f, φ⟩ = ∫ f · 𝓕 φ`, and `∫ e^{2πiνt} 𝓕 φ(t) dt = 𝓕⁻(𝓕 φ)(ν) = φ(ν)` by the inversion formula
on the Schwartz space. -/
theorem example_10_6 (A ν₀ : ℝ) :
    𝓕 ((Function.HasTemperateGrowth.const (E := ℝ) (A : ℂ)).toTemperedDistribution volume)
        = (A : ℂ) • TemperedDistribution.delta (0 : ℝ) ∧
      𝓕 ((by fun_prop : (fun t : ℝ => (A : ℂ) * Real.cos (2 * π * ν₀ * t)).HasTemperateGrowth
          ).toTemperedDistribution volume)
        = ((A : ℂ) / 2) • (TemperedDistribution.delta ν₀ + TemperedDistribution.delta (-ν₀)) := by
  -- the key evaluation: `∫ e^{2πiνt} 𝓕 φ(t) dt = φ ν`
  have key : ∀ (φ : SchwartzMap ℝ ℂ) (ν : ℝ),
      ∫ t : ℝ, Complex.exp ((2 * π * ν * t) * I) * 𝓕 (φ : ℝ → ℂ) t = φ ν := by
    intro φ ν
    have h := congrFun (SchwartzMap.fourierInv_coe (𝓕 φ)) ν
    rw [FourierTransform.fourierInv_fourier_eq φ] at h
    rw [h, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul,
      SchwartzMap.fourier_coe]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · ext φ
    simp only [TemperedDistribution.fourier_apply,
      Function.HasTemperateGrowth.toTemperedDistribution_apply, smul_apply,
      TemperedDistribution.delta_apply, smul_eq_mul, SchwartzMap.fourier_coe]
    rw [integral_mul_const, ← key φ 0]
    simp [mul_comm]
  · ext φ
    simp only [TemperedDistribution.fourier_apply,
      Function.HasTemperateGrowth.toTemperedDistribution_apply, smul_apply, add_apply,
      TemperedDistribution.delta_apply, smul_eq_mul, SchwartzMap.fourier_coe]
    rw [← key φ ν₀, ← key φ (-ν₀)]
    have hcos : ∀ t : ℝ, ((A : ℂ) * Real.cos (2 * π * ν₀ * t))
        = (A : ℂ) / 2 * (Complex.exp ((2 * π * ν₀ * t) * I)
          + Complex.exp ((2 * π * -ν₀ * t) * I)) := by
      intro t
      have := Complex.two_cos ((2 * π * ν₀ * t : ℝ) : ℂ)
      push_cast at this ⊢
      rw [show (2 * (π : ℂ) * -ν₀ * t) * I = -(2 * π * ν₀ * t) * I by ring]
      linear_combination ((A : ℂ) / 2) * this
    have hint : ∀ ν : ℝ,
        Integrable (fun t : ℝ => Complex.exp ((2 * π * ν * t) * I) * 𝓕 (φ : ℝ → ℂ) t) := by
      intro ν
      refine (𝓕 φ).integrable.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
        (Eventually.of_forall fun t => ?_)
      rw [show ((2 * π * ν * t : ℂ)) * I = ((2 * π * ν * t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    simp only [hcos]
    rw [← integral_add (hint ν₀) (hint (-ν₀)), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    push_cast
    ring

/-- **(10.80), the shift-invariant linear system.** The book's `S` is "a linear operator" on
unspecified "admissible input functions" with `S(i(· − t₀)) = u(· − t₀)` for every `t₀`, and
`S(f ⋆ g) = f ⋆ S(g)` is called an immediate consequence of linearity and shift invariance. It is
not: `f ⋆ g = ∫ f(τ) τ_τ g dτ` is a *continuous* superposition of translates, not a finite linear
combination, and passing `S` through that integral needs `S` to be continuous — linearity and
shift invariance alone do not suffice (nor does the book give `S` a domain or a topology).

The formalization takes `S` to be a bounded linear operator on `L¹(ℝ)` commuting with every
translation `τ_{t₀} u = u(· − t₀)` (`MeasureTheory.Lp.translateₗᵢ`): `L¹` is the space in which
the book's inputs `f, g` and the convolution (10.77) live, boundedness is the continuity the
argument needs, and `S(f ⋆ g) = f ⋆ S(g)` then holds almost everywhere for all `f, g ∈ L¹(ℝ)`.
The proof is the book's, made rigorous: `f ⋆ g` is the `L¹`-valued Bochner integral of the
translates (`MeasureTheory.Lp.integral_smul_translateₗᵢ_eq_toL1`), `S` passes through the integral
and through each translate (`MeasureTheory.Lp.coeFn_toL1_convolution_of_translateₗᵢ_comm`). -/
theorem equation_10_80 (S : Lp ℂ 1 (volume : Measure ℝ) →L[ℂ] Lp ℂ 1 (volume : Measure ℝ))
    (hS : ∀ (t₀ : ℝ) (i : Lp ℂ 1 (volume : Measure ℝ)),
      S (Lp.translateₗᵢ ℂ ℂ 1 t₀ i) = Lp.translateₗᵢ ℂ ℂ 1 t₀ (S i))
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ⇑(S ((equation_10_77_integrable hf hg).toL1 (equation_10_77 f g)))
      =ᵐ[volume] equation_10_77 f (S (hg.toL1 g)) := by
  have hmul : ContinuousLinearMap.mul ℂ ℂ = ContinuousLinearMap.lsmul ℂ ℂ := by
    ext
    simp
  have hg' : Integrable (hg.toL1 g) volume := L1.integrable_coeFn _
  have h1 : (equation_10_77_integrable hf hg).toL1 (equation_10_77 f g)
      = (hf.integrable_convolution (ContinuousLinearMap.lsmul ℂ ℂ) hg').toL1 _ := by
    rw [Integrable.toL1_eq_toL1_iff, equation_10_77_eq_convolution, hmul]
    exact Eventually.of_forall (congrFun (convolution_congr _ (ae_eq_refl f) hg.coeFn_toL1.symm))
  rw [h1]
  refine (Lp.coeFn_toL1_convolution_of_translateₗᵢ_comm S hS hf (hg.toL1 g)).trans ?_
  rw [equation_10_77_eq_convolution, hmul]

/-- **(10.81), the transfer function.** If the output of a system is the convolution `u = i ⋆ h` of
the input `i ∈ L¹` with the impulse response `h ∈ L¹`, then `U(ν) = I(ν) H(ν)` for the transforms
`U = 𝓕 u`, `I = 𝓕 i`, `H = 𝓕 h`; `H` is the transfer function. This is (10.76). -/
theorem equation_10_81 {i h : ℝ → ℂ} (hi : Integrable i) (hh : Integrable h) (ν : ℝ) :
    𝓕 (equation_10_77 i h) ν = 𝓕 i ν * 𝓕 h ν :=
  (equation_10_76 hi hh).1 ν

/-- **Example 10.7, the ideal low-pass filter.** For `ν₀ > 0` and the transfer function
`H = 1_{[-ν₀/2, ν₀/2]}`, the impulse response `h = 𝓕⁻¹ H` is `h(t) = ν₀ sin(πν₀t)/(πν₀t)` for
`t ≠ 0` and `h(0) = ν₀`: the rectangle of Example 10.5 with `A = 1`, `T = ν₀`, under
`𝓕⁻¹ H(t) = 𝓕 H(−t)`. The output `u = i ⋆ h` of an input `i` has the spectrum `I H`, i.e. `I` on
`|ν| ≤ ν₀/2` and `0` outside, by (10.81); since `h ∉ L¹`, that clause needs the `L²` theory and is
not stated here. -/
theorem example_10_7 {ν₀ : ℝ} (hν₀ : 0 < ν₀) (t : ℝ) :
    (t ≠ 0 → 𝓕⁻ (Set.indicator (Icc (-(ν₀ / 2)) (ν₀ / 2)) fun _ => (1 : ℂ)) t
        = ((ν₀ * (Real.sin (π * ν₀ * t) / (π * ν₀ * t)) : ℝ) : ℂ)) ∧
      𝓕⁻ (Set.indicator (Icc (-(ν₀ / 2)) (ν₀ / 2)) fun _ => (1 : ℂ)) 0 = (ν₀ : ℂ) := by
  have h1 := example_10_5_rect (A := 1) hν₀ (-t)
  have h0 := example_10_5_rect (A := 1) hν₀ 0
  simp only [Complex.ofReal_one, one_mul] at h1 h0
  refine ⟨fun ht => ?_, ?_⟩
  · rw [Real.fourierInv_eq_fourier_neg, h1.1 (neg_ne_zero.mpr ht)]
    congr 1
    rw [show π * -t * ν₀ = -(π * ν₀ * t) by ring, Real.sin_neg, neg_div_neg_eq]
  · rw [Real.fourierInv_eq_fourier_neg, neg_zero, h0.2]

/-- **(10.82), the sampling (aliasing) formula.** For a continuous input `i` vanishing outside a
bounded interval, a sampling step `Δt > 0` and a frequency `ν` at which the periodic repetition
`∑_j I(ν − j/Δt)` of `I = 𝓕 i` converges absolutely,

`Ĩ(ν) = Δt ∑_{k ∈ ℤ} i(kΔt) e^{-2πiνkΔt} = ∑_{j ∈ ℤ} I(ν − j/Δt)`:

the trapezoidal approximation of `I(ν)` is the periodic repetition of `I` with period `1/Δt`.
The backbone's `Real.tsum_fourierIntegral_sub_div_eq_tsum_mul`, from Mathlib's Poisson summation;
the book's derivation through the sampled signal `∑ i(kΔt) δ(· − kΔt)` is distributional. For `i`
supported in `[0, T₀]` the left side is the finite sum `Δt ∑_{k=0}^{n-1} i(kΔt) e^{-2πiνkΔt}` of the
book (its `i` may jump at `0` and `T₀`, where the sum sees the average of the one-sided limits —
hence the continuity hypothesis). -/
theorem equation_10_82 {i : ℝ → ℂ} (hi : Continuous i) (hsupp : HasCompactSupport i) {Δt : ℝ}
    (hΔt : 0 < Δt) {ν : ℝ} (hsum : Summable fun j : ℤ => 𝓕 i (ν - j / Δt)) :
    Δt * ∑' k : ℤ, i (k * Δt) * Complex.exp (-(2 * π * ν * k * Δt) * I)
      = ∑' j : ℤ, 𝓕 i (ν - j / Δt) := by
  refine (Real.tsum_fourierIntegral_sub_div_eq_tsum_mul hi (b := 2) one_lt_two ?_ hΔt hsum).symm
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [hsupp.compl_mem_cocompact] with x hx
  rw [Set.mem_compl_iff] at hx
  rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, zero_mul]

/-! ### Definition 10.2: the Laplace transform -/

/-- **Definition 10.2.** For `f ∈ L¹_loc([0, ∞))` and `s = σ + iω ∈ ℂ`, the Laplace integral of `f`
exists when `∫_0^∞ f(t) e^{-st} dt = lim_{T → ∞} ∫_0^T f(t) e^{-st} dt` exists; this is
`LaplaceTransform.Converges f s` (`definition_10_2_iff`), and the Laplace transform `L(s) = ℒ[f](s)`
is that limit, `laplace f s = LaplaceTransform.laplaceTransform f s`. -/
def definition_10_2 (f : ℝ → ℂ) (s : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(s * t))) atTop (𝓝 L)

/-- The Laplace transform `L(s) = ∫_0^∞ f(t) e^{-st} dt` of Definition 10.2, as the limit of the
truncated integrals — the backbone's `LaplaceTransform.laplaceTransform`. -/
noncomputable def laplace (f : ℝ → ℂ) (s : ℂ) : ℂ := LaplaceTransform.laplaceTransform f s

/-- The truncated integral of Definition 10.2 is the backbone's `LaplaceTransform.truncated`. -/
theorem intervalIntegral_mul_exp_eq_truncated (f : ℝ → ℂ) (s : ℂ) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(s * t)) = LaplaceTransform.truncated f s T := by
  rw [LaplaceTransform.truncated_def]
  exact intervalIntegral.integral_congr fun t _ => by rw [smul_eq_mul, mul_comm]

/-- The existence of the Laplace integral in the book's sense is the backbone's `Converges`. -/
theorem definition_10_2_iff (f : ℝ → ℂ) (s : ℂ) :
    definition_10_2 f s ↔ LaplaceTransform.Converges f s := by
  simp only [definition_10_2, LaplaceTransform.Converges, intervalIntegral_mul_exp_eq_truncated]

/-- Where the Laplace integral exists, the transform is its value. -/
theorem laplace_eq_of_tendsto {f : ℝ → ℂ} {s L : ℂ}
    (h : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(s * t))) atTop (𝓝 L)) :
    laplace f s = L := by
  simp only [intervalIntegral_mul_exp_eq_truncated] at h
  exact LaplaceTransform.laplaceTransform_eq_of_tendsto h

/-- **The relation to the Fourier transform** (after Definition 10.2): for `f` with `e^{-st} f`
integrable on `(0, ∞)`, `L(σ + iω) = F(e^{-σt} f̃)(ω/2π)` with `f̃ = f` on `t > 0` and `0` on
`t ≤ 0` — the argument `ω/2π`, which the book omits, because Definition 10.1 carries `e^{-2πiνt}`.
The backbone's `LaplaceTransform.laplaceTransform_eq_fourier`. -/
theorem definition_10_2_fourier {f : ℝ → ℂ} {s : ℂ}
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * f t) (Ioi 0)) :
    laplace f s = definition_10_1 (fun t => Complex.exp (-(s.re * t)) * Set.indicator (Ioi 0) f t)
      (s.im / (2 * π)) := by
  rw [definition_10_1_eq_fourierIntegral, laplace]
  exact LaplaceTransform.laplaceTransform_eq_fourier h

/-- **Example 10.8.** The Laplace transform of the unit step `f(t) = 1` for `t > 0`, `0` otherwise,
is `L(s) = ∫_0^∞ e^{-st} dt = 1/s`, and the Laplace integral exists exactly when `Re s > 0`. -/
theorem example_10_8 (s : ℂ) :
    (0 < s.re → laplace (fun t : ℝ => Set.indicator (Ioi 0) (fun _ => (1 : ℂ)) t) s = 1 / s) ∧
      (definition_10_2 (fun t : ℝ => Set.indicator (Ioi 0) (fun _ => (1 : ℂ)) t) s ↔ 0 < s.re) :=
  ⟨fun hs => LaplaceTransform.laplaceTransform_indicator_Ioi hs,
    (definition_10_2_iff _ _).trans LaplaceTransform.converges_indicator_Ioi_iff⟩

/-- **Property 10.4.** If the Laplace integral of `f ∈ L¹_loc([0, ∞))` exists at `s = s̄`, then it
exists at every `s` with `Re s > Re s̄`. Hence, with `λ` the infimum of the real parts at which it
exists (the abscissa of convergence, `LaplaceTransform.abscissaOfConvergence f`, an extended real),
the Laplace integral exists in the half-plane `Re s > λ` — and for every `s` when `λ = −∞`. -/
theorem property_10_4 {f : ℝ → ℂ} (hf : LocallyIntegrableOn f (Ici 0)) :
    (∀ s₀ s : ℂ, definition_10_2 f s₀ → s₀.re < s.re → definition_10_2 f s) ∧
      (∀ s : ℂ, LaplaceTransform.abscissaOfConvergence f < (s.re : EReal) → definition_10_2 f s) ∧
      (LaplaceTransform.abscissaOfConvergence f = ⊥ → ∀ s : ℂ, definition_10_2 f s) := by
  refine ⟨fun s₀ s h hs => ?_, fun s hs => ?_, fun hbot s => ?_⟩
  · rw [definition_10_2_iff] at h ⊢
    exact LaplaceTransform.converges_of_re_lt hf h hs
  · rw [definition_10_2_iff]
    exact LaplaceTransform.converges_of_abscissaOfConvergence_lt hf hs
  · rw [definition_10_2_iff]
    exact LaplaceTransform.converges_of_abscissaOfConvergence_lt hf
      (by rw [hbot]; exact EReal.bot_lt_coe _)

/-- **Example 10.9, (10.83).** Let `y ∈ C¹` solve `y'(t) + a y(t) = g(t)` with `y(0) = y₀`, and let
`s` be such that the Laplace integrals of `y`, `y'` and `g` converge absolutely and
`e^{-st} y(t) → 0`. Then `s Y(s) − y₀ + a Y(s) = G(s)`: the transform of a derivative
(`LaplaceTransform.laplaceTransform_deriv`) and the linearity of the transform. -/
theorem example_10_9 {y g : ℝ → ℂ} {a s : ℂ} (hy : ContDiff ℝ 1 y)
    (hode : ∀ t, deriv y t + a * y t = g t)
    (hint : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • y t) (Ioi 0))
    (hint' : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • deriv y t) (Ioi 0))
    (hlim : Tendsto (fun t : ℝ => Complex.exp (-(s * t)) • y t) atTop (𝓝 0)) :
    s * laplace y s - y 0 + a * laplace y s = laplace g s := by
  have hg : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • g t) (Ioi 0) := by
    refine (hint'.add (hint.smul a)).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hode t]
    ring
  have hderiv := LaplaceTransform.laplaceTransform_deriv hy hint hint' hlim
  have h2 : IntegrableOn (fun t : ℝ => a • (Complex.exp (-(s * t)) • y t)) (Ioi 0) := hint.smul a
  have h1 : ∫ t : ℝ in Ioi 0, Complex.exp (-(s * t)) • g t
      = (∫ t : ℝ in Ioi 0, Complex.exp (-(s * t)) • deriv y t)
        + a • ∫ t : ℝ in Ioi 0, Complex.exp (-(s * t)) • y t := by
    rw [← integral_smul, ← integral_add hint' h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul, ← hode t]
    ring
  simp only [laplace]
  rw [LaplaceTransform.laplaceTransform_eq_integral hg, h1,
    ← LaplaceTransform.laplaceTransform_eq_integral hint',
    ← LaplaceTransform.laplaceTransform_eq_integral hint, hderiv, smul_eq_mul, smul_eq_mul]

/-- **Example 10.9, the solution.** For `a ≠ 0` the function
`y(t) = (1/a)(1 − e^{-at}) + y₀ e^{-at}` satisfies `y' + a y = 1` and `y(0) = y₀`, the solution of
`y' + a y = g` for the unit-step forcing `g = 1` that the book obtains by inverting
`Y(s) = (1/a)(1/s − 1/(s + a)) + y₀/(s + a)`. Direct differentiation. -/
theorem example_10_9_solution {a : ℂ} (ha : a ≠ 0) (y₀ : ℂ) :
    (∀ t : ℝ, HasDerivAt
        (fun t : ℝ => (1 / a) * (1 - Complex.exp (-(a * t))) + y₀ * Complex.exp (-(a * t)))
        (1 - a * ((1 / a) * (1 - Complex.exp (-(a * t))) + y₀ * Complex.exp (-(a * t)))) t) ∧
      (1 / a) * (1 - Complex.exp (-(a * (0 : ℝ)))) + y₀ * Complex.exp (-(a * (0 : ℝ))) = y₀ := by
  refine ⟨fun t => ?_, by simp⟩
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-(a * t))) (-a * Complex.exp (-(a * t))) t := by
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(a * z)))
        (Complex.exp (-(a * t)) * -(a * 1)) (t : ℂ) :=
      ((hasDerivAt_id (t : ℂ)).const_mul a).neg.cexp
    exact (h1.comp_ofReal).congr_deriv (by ring)
  have := ((hexp.const_sub 1).const_mul (1 / a)).add (hexp.const_mul y₀)
  refine this.congr_deriv ?_
  field_simp
  ring

/-! ### Definition 10.3: the Z-transform -/

/-- **Definition 10.3, (10.84).** For `f` defined on `t ≥ 0` and a time step `Δt > 0`, the
Z-transform of the samples `f(nΔt)` is `Z(z) = ∑_{n ≥ 0} f(nΔt) z^{-n}`, `z ∈ ℂ` — the backbone's
`zTransform`. -/
noncomputable def definition_10_3 (f : ℝ → ℂ) (Δt : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, f (n * Δt) * z⁻¹ ^ n

/-- The book's Z-transform is the backbone's `zTransform`. -/
theorem definition_10_3_eq_zTransform (f : ℝ → ℂ) (Δt : ℝ) (z : ℂ) :
    definition_10_3 f Δt z = zTransform f Δt z := rfl

/-- **The convergence of (10.84).** The series converges for `|z| > R = limsup_n |f(nΔt)|^{1/n}`,
the limsup taken in `[0, ∞]` (`ℝ≥0∞`, through `‖·‖ₑ`): the Cauchy–Hadamard root test
`summable_zTransform`. -/
theorem definition_10_3_summable {f : ℝ → ℂ} {Δt : ℝ} {z : ℂ}
    (hz : Filter.limsup (fun n : ℕ => ‖f (n * Δt)‖ₑ ^ (1 / (n : ℝ))) atTop < ‖z‖ₑ) :
    Summable fun n : ℕ => f (n * Δt) * z⁻¹ ^ n :=
  summable_zTransform hz

/-- **The Z-transform as a discrete Laplace transform (§10.11.4).** For the piecewise constant
`f₀(t) = f(nΔt)` on `[nΔt, (n+1)Δt)` (`f₀(t) = f(⌊t/Δt⌋Δt)`), `Re s > 0` and
`∑_n |f(nΔt)| e^{-n Re s Δt} < ∞`, the Laplace transform of `f₀` is
`L(s) = ((1 − e^{-sΔt})/s) ∑_{n ≥ 0} f(nΔt) e^{-nsΔt}`, and the series — the discrete Laplace
transform `Z^d(s)` — is the Z-transform at `z = e^{sΔt}`, so that
`L(s) = ((1 − e^{-sΔt})/s) Z(e^{sΔt})`.
Erratum: the book prints the substitution as `z = e^{-sΔt}`. The backbone's
`LaplaceTransform.laplaceTransform_stepFun` and `zTransform_eq_discreteLaplace`. -/
theorem definition_10_3_eq_discreteLaplace {f : ℝ → ℂ} {Δt : ℝ} (hΔt : 0 < Δt) {s : ℂ}
    (hs : 0 < s.re) (hsum : Summable fun n : ℕ => ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt))) :
    definition_10_3 f Δt (Complex.exp (s * Δt))
        = ∑' n : ℕ, f (n * Δt) * Complex.exp (-(n * s * Δt)) ∧
      laplace (fun t : ℝ => f (⌊t / Δt⌋ * Δt)) s
        = ((1 - Complex.exp (-(s * Δt))) / s) * definition_10_3 f Δt (Complex.exp (s * Δt)) := by
  refine ⟨zTransform_eq_discreteLaplace f s, ?_⟩
  rw [definition_10_3_eq_zTransform, zTransform_eq_discreteLaplace, laplace]
  exact LaplaceTransform.laplaceTransform_stepFun hΔt hs hsum

end QuarteroniSaccoSaleri.Chapter10
