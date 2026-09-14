/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.Inversion` and `Mathlib.Analysis.Fourier.Convolution`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Elementary properties of the Fourier integral

Facts about the Fourier integral `𝓕 f ν = ∫ f t exp (-2πi ν t) dt` of an integrable function that
Mathlib's `Mathlib/Analysis/Fourier/{FourierTransform, Inversion, Convolution}.lean` do not state
in the form a textbook uses ([quarteroni2000numerical] §10.11.1, Property 10.3 and the properties
numbered 1–5 after it):

* `Real.continuous_fourierIntegral`, `Real.continuous_fourierIntegralInv` — the transform and the
  inverse transform of an integrable function are continuous; a specialization of
  `VectorFourier.fourierIntegral_continuous`.
* `Real.ae_eq_fourierInv_fourier` — **almost-everywhere Fourier inversion**: for `f` and `𝓕 f`
  integrable, `f = 𝓕⁻ (𝓕 f)` almost everywhere, with no continuity hypothesis. Mathlib's
  `MeasureTheory.Integrable.fourierInv_fourier_eq` gives the pointwise identity at continuity
  points only. The proof here is by duality rather than by the Gaussian regularization of
  Mathlib's proof: for every smooth compactly supported test function `φ`, the multiplication
  formula `∫ (𝓕 F) φ = ∫ F (𝓕 φ)` (`VectorFourier.integral_bilin_fourierIntegral_eq_flip`) applied
  twice gives `∫ φ • 𝓕⁻ (𝓕 f) = ∫ (𝓕 (𝓕⁻ φ)) • f = ∫ φ • f`, using the continuous inversion
  formula for the Schwartz function `φ`; two locally integrable functions with the same integrals
  against all test functions agree almost everywhere
  (`ae_eq_of_integral_contDiff_smul_eq`).
* `Real.fourierIntegral_const_smul`, `Real.fourierIntegral_comp_add_right`,
  `Real.fourierIntegral_comp_sub_right`, `Real.fourierIntegral_fourierChar_mul`,
  `Real.fourierIntegral_comp_mul_left` — the transform of a constant multiple, the translation
  rule `𝓕 (f (· − a)) ν = 𝐞 (−a ν) • 𝓕 f ν`, the modulation rule
  `𝓕 (𝐞 (−(· a)) • f) ν = 𝓕 f (ν + a)`, and the scaling rule `𝓕 (f (a ·)) ν = |a|⁻¹ 𝓕 f (ν / a)`.
* `Real.fourierIntegral_even_eq_integral_cos`, `Real.fourierIntegral_even_real`,
  `Real.fourierIntegral_odd_eq_integral_sin`, `Real.fourierIntegral_odd_real` — the parity
  rules: the transform of a real even function is the cosine transform, real and even; that of a
  real odd function is `-i` times the sine transform, purely imaginary and odd.
* `Real.fourier_mul_eq_convolution` — the transform of a product is the convolution of the
  transforms, `𝓕 (f g) = 𝓕 f ⋆ 𝓕 g`, for `f, g ∈ L¹` with `𝓕 g ∈ L¹`. Mathlib has the dual
  statement `Real.fourier_mul_convolution_eq` (`𝓕 (f ⋆ g) = 𝓕 f · 𝓕 g`) and the Schwartz-class
  form `SchwartzMap.fourier_convolution`. The proof is Fubini after writing `g` as the inverse
  transform of `𝓕 g` almost everywhere, which is where `ae_eq_fourierInv_fourier` enters; the
  textbook states the identity for `f, g ∈ L¹` alone, where the right side need not exist.
* `Real.coeFn_fourier_toLp`, `Real.integral_conj_fourier_mul_fourier` — **the `L²` transform on
  `L¹ ∩ L²`**: Mathlib's unitary `MeasureTheory.Lp.fourierTransformₗᵢ` on `L²`, defined by
  extension from the Schwartz space, agrees almost everywhere with the Fourier integral of an
  `L¹ ∩ L²` function, and therefore Plancherel's identity `∫ conj (𝓕 f) 𝓕 g = ∫ conj f · g` holds
  for `f, g ∈ L¹ ∩ L²` with the integrals written out. The identification again goes through
  tempered distributions: the two transforms of `f` define the same distribution
  (`MeasureTheory.Lp.fourier_toTemperedDistribution_eq` and the multiplication formula), and both
  are locally integrable.

The statements that do not use the order of `ℝ` are given on a finite-dimensional real inner
product space `V`, the setting of Mathlib's `𝓕`; the scaling and parity rules are on `ℝ`.
-/

open MeasureTheory Filter Topology Complex

open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace Real

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Continuity -/

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourierIntegral {f : V → E} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

/-- The inverse Fourier transform of an integrable function is continuous. -/
theorem continuous_fourierIntegralInv {f : V → E} (hf : Integrable f) : Continuous (𝓕⁻ f) := by
  rw [fourierInv_eq_fourier_comp_neg]
  exact continuous_fourierIntegral hf.comp_neg

/-! ### Almost-everywhere inversion -/

/-- **Almost-everywhere Fourier inversion** ([quarteroni2000numerical] Property 10.3): if `f` and
`𝓕 f` are integrable then `f = 𝓕⁻ (𝓕 f)` almost everywhere. No continuity of `f` is assumed; at
a continuity point the identity holds pointwise, which is Mathlib's
`MeasureTheory.Integrable.fourierInv_fourier_eq`.

The proof tests both sides against a smooth compactly supported `φ`: by the multiplication formula
applied twice, `∫ φ • 𝓕⁻ (𝓕 f) = ∫ (𝓕⁻ φ) • 𝓕 f = ∫ (𝓕 (𝓕⁻ φ)) • f = ∫ φ • f`, the last step by
the continuous inversion formula for the Schwartz function `φ`. -/
theorem ae_eq_fourierInv_fourier [CompleteSpace E] {f : V → E} (hf : Integrable f)
    (h'f : Integrable (𝓕 f)) : f =ᵐ[volume] 𝓕⁻ (𝓕 f) := by
  refine ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable
    (continuous_fourierIntegralInv h'f).locallyIntegrable fun g hg hgs => ?_
  -- the test function as a complex Schwartz function
  set φ : SchwartzMap V ℂ := (hgs.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg) with hφ
  have hφ_int : Integrable (fun x => (g x : ℂ)) := φ.integrable
  have hφ_inv_int : Integrable (𝓕⁻ fun x => (g x : ℂ)) := by
    have := (𝓕⁻ φ).integrable (μ := volume)
    rwa [SchwartzMap.fourierInv_coe] at this
  have hφ_fourier_int : Integrable (𝓕 fun x => (g x : ℂ)) := by
    have := (𝓕 φ).integrable (μ := volume)
    rwa [SchwartzMap.fourier_coe] at this
  have hinv : 𝓕 (𝓕⁻ fun x => (g x : ℂ)) = fun x => (g x : ℂ) :=
    Continuous.fourier_fourierInv_eq (Complex.continuous_ofReal.comp hg.continuous) hφ_int
      hφ_fourier_int
  have hsmul : ∀ (c : ℝ) (v : E), c • v = (c : ℂ) • v := fun c v =>
    RCLike.real_smul_eq_coe_smul (K := ℂ) c v
  simp only [hsmul]
  have hL : Continuous fun p : V × V => (innerₗ V) p.1 p.2 := continuous_inner
  have hL' : Continuous fun p : V × V => (-innerₗ V) p.1 p.2 := continuous_inner.neg
  have hflip : (-innerₗ V).flip = -innerₗ V := by
    ext x y
    simp [real_inner_comm]
  have hflip' : (innerₗ V).flip = innerₗ V := by
    ext x y
    simp
  -- first application: move `𝓕⁻` from `𝓕 f` onto the test function
  have h1 : ∫ x, (g x : ℂ) • 𝓕⁻ (𝓕 f) x = ∫ x, (𝓕⁻ fun y => (g y : ℂ)) x • 𝓕 f x := by
    have := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).flip (e := 𝐞) (L := -innerₗ V)
      Real.continuous_fourierChar hL' h'f hφ_int
    simp only [hflip, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] at this
    exact this
  -- second application: move `𝓕` from `f` onto the test function
  have h2 : ∫ x, (𝓕⁻ fun y => (g y : ℂ)) x • 𝓕 f x
      = ∫ x, (𝓕 (𝓕⁻ fun y => (g y : ℂ))) x • f x := by
    have := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).flip (e := 𝐞) (L := innerₗ V)
      Real.continuous_fourierChar hL hf hφ_inv_int
    simp only [hflip', ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] at this
    exact this
  rw [h1, h2, hinv]

/-! ### Linearity, modulation and scaling -/

/-- The Fourier transform of a constant multiple, pointwise: `𝓕 (c • f) ν = c • 𝓕 f ν`. -/
theorem fourierIntegral_const_smul (c : ℂ) (f : V → E) (ν : V) :
    𝓕 (fun t => c • f t) ν = c • 𝓕 f ν :=
  congrFun (VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ V) f c) ν

/-- **The translation rule**, pointwise: `𝓕 (fun v => f (v + v₀)) w = 𝐞 ⟪v₀, w⟫ • 𝓕 f w`,
Mathlib's `VectorFourier.fourierIntegral_comp_add_right` for `𝓕`. -/
theorem fourierIntegral_comp_add_right (f : V → E) (v₀ w : V) :
    𝓕 (fun v => f (v + v₀)) w = 𝐞 ⟪v₀, w⟫ • 𝓕 f w :=
  congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ V) f v₀) w

/-- **The translation rule** on the line: `𝓕 (fun t => f (t - a)) ν = 𝐞 (-(a ν)) • 𝓕 f ν`, that
is, a delay by `a` multiplies the transform by the phase `e^{-2πiaν}`. -/
theorem fourierIntegral_comp_sub_right (f : ℝ → E) (a ν : ℝ) :
    𝓕 (fun t => f (t - a)) ν = 𝐞 (-(a * ν)) • 𝓕 f ν := by
  have := fourierIntegral_comp_add_right f (-a) ν
  simp only [← sub_eq_add_neg] at this
  rw [this]
  congr 2
  simp [mul_comm]

/-- **The modulation rule**: multiplying by the character `t ↦ 𝐞 (-(t a))` translates the
transform by `a`, `𝓕 (fun t => 𝐞 (-(t a)) • f t) ν = 𝓕 f (ν + a)`. -/
theorem fourierIntegral_fourierChar_mul (f : ℝ → E) (a ν : ℝ) :
    𝓕 (fun t => (𝐞 (-(t * a)) : ℂ) • f t) ν = 𝓕 f (ν + a) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Circle.smul_def, smul_smul]
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 3
  ring

/-- **The scaling rule** ([quarteroni2000numerical] §10.11.1, property 2): for `a ≠ 0`,
`𝓕 (fun t => f (a * t)) ν = |a|⁻¹ • 𝓕 f (ν / a)`. The change of variables `t ↦ a t` in the
defining integral, `MeasureTheory.Measure.integral_comp_mul_left`, which needs no integrability. -/
theorem fourierIntegral_comp_mul_left {a : ℝ} (ha : a ≠ 0) (f : ℝ → E) (ν : ℝ) :
    𝓕 (fun t => f (a * t)) ν = |a|⁻¹ • 𝓕 f (ν / a) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have hG : (fun t : ℝ => Complex.exp (↑(-2 * π * t * ν) * I) • f (a * t))
      = fun t : ℝ => (fun u : ℝ => Complex.exp (↑(-2 * π * u * (ν / a)) * I) • f u) (a * t) := by
    funext t
    simp only
    congr 3
    field_simp
  rw [hG, MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => Complex.exp (↑(-2 * π * u * (ν / a)) * I) • f u) a, abs_inv]

/-! ### Parity -/

/-- **The transform of a real even function is its cosine transform**: for `f : ℝ → ℝ` integrable
and even, `𝓕 f ν = ∫ f t cos (2 π ν t) dt`. Expanding `e^{-2πiνt} = cos (2πνt) - i sin (2πνt)`,
the sine term integrates to zero because its integrand is odd. -/
theorem fourierIntegral_even_eq_integral_cos {f : ℝ → ℝ} (hf : Integrable f)
    (heven : ∀ t, f (-t) = f t) (ν : ℝ) :
    𝓕 (fun t => (f t : ℂ)) ν = ((∫ t, f t * Real.cos (2 * π * ν * t) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hsplit : ∀ t : ℝ, Complex.exp (↑(-2 * π * t * ν) * I) • (f t : ℂ)
      = ((f t * Real.cos (2 * π * ν * t) : ℝ) : ℂ)
        + I * ((f t * Real.sin (-2 * π * t * ν) : ℝ) : ℂ) := by
    intro t
    rw [Complex.exp_mul_I, smul_eq_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * t * ν = -(2 * π * ν * t) by ring, Real.cos_neg]
    push_cast
    ring
  have hcos : Integrable fun t => f t * Real.cos (2 * π * ν * t) :=
    hf.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun t => by
      simpa using Real.abs_cos_le_one _)
  have hsin : Integrable fun t => f t * Real.sin (-2 * π * t * ν) :=
    hf.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun t => by
      simpa using Real.abs_sin_le_one _)
  have hodd : ∫ t, f t * Real.sin (-2 * π * t * ν) = 0 := by
    have h := MeasureTheory.integral_neg_eq_self (fun t => f t * Real.sin (-2 * π * t * ν)) volume
    have h' : ∀ t, f (-t) * Real.sin (-2 * π * -t * ν) = -(f t * Real.sin (-2 * π * t * ν)) := by
      intro t
      rw [heven, show -2 * π * -t * ν = -(-2 * π * t * ν) by ring, Real.sin_neg]
      ring
    simp only [h', integral_neg] at h
    linarith
  have hcosC : Integrable fun t => ((f t * Real.cos (2 * π * ν * t) : ℝ) : ℂ) := hcos.ofReal
  have hsinC : Integrable fun t => ((f t * Real.sin (-2 * π * t * ν) : ℝ) : ℂ) := hsin.ofReal
  simp only [hsplit]
  rw [integral_add hcosC (hsinC.const_mul I), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, hodd]
  simp

/-- **Parity, even case** ([quarteroni2000numerical] §10.11.1, property 4): the Fourier transform
of a real-valued, integrable, even function is real-valued and even. -/
theorem fourierIntegral_even_real {f : ℝ → ℝ} (hf : Integrable f) (heven : ∀ t, f (-t) = f t)
    (ν : ℝ) :
    (𝓕 (fun t => (f t : ℂ)) ν).im = 0 ∧
      𝓕 (fun t => (f t : ℂ)) (-ν) = 𝓕 (fun t => (f t : ℂ)) ν := by
  refine ⟨?_, ?_⟩
  · rw [fourierIntegral_even_eq_integral_cos hf heven, Complex.ofReal_im]
  · rw [fourierIntegral_even_eq_integral_cos hf heven,
      fourierIntegral_even_eq_integral_cos hf heven]
    congr 2
    funext t
    rw [show 2 * π * -ν * t = -(2 * π * ν * t) by ring, Real.cos_neg]

/-- **The transform of a real odd function is `-i` times its sine transform**: for `f : ℝ → ℝ`
integrable and odd, `𝓕 f ν = -i ∫ f t sin (2 π ν t) dt`; the cosine term integrates to zero. -/
theorem fourierIntegral_odd_eq_integral_sin {f : ℝ → ℝ} (hf : Integrable f)
    (hodd : ∀ t, f (-t) = -f t) (ν : ℝ) :
    𝓕 (fun t => (f t : ℂ)) ν = -I * ((∫ t, f t * Real.sin (2 * π * ν * t) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hsplit : ∀ t : ℝ, Complex.exp (↑(-2 * π * t * ν) * I) • (f t : ℂ)
      = ((f t * Real.cos (2 * π * ν * t) : ℝ) : ℂ)
        - I * ((f t * Real.sin (2 * π * ν * t) : ℝ) : ℂ) := by
    intro t
    rw [Complex.exp_mul_I, smul_eq_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * t * ν = -(2 * π * ν * t) by ring, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hcos : Integrable fun t => f t * Real.cos (2 * π * ν * t) :=
    hf.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun t => by
      simpa using Real.abs_cos_le_one _)
  have hsin : Integrable fun t => f t * Real.sin (2 * π * ν * t) :=
    hf.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun t => by
      simpa using Real.abs_sin_le_one _)
  have hzero : ∫ t, f t * Real.cos (2 * π * ν * t) = 0 := by
    have h := MeasureTheory.integral_neg_eq_self (fun t => f t * Real.cos (2 * π * ν * t)) volume
    have h' : ∀ t, f (-t) * Real.cos (2 * π * ν * -t) = -(f t * Real.cos (2 * π * ν * t)) := by
      intro t
      rw [hodd, show 2 * π * ν * -t = -(2 * π * ν * t) by ring, Real.cos_neg]
      ring
    simp only [h', integral_neg] at h
    linarith
  have hcosC : Integrable fun t => ((f t * Real.cos (2 * π * ν * t) : ℝ) : ℂ) := hcos.ofReal
  have hsinC : Integrable fun t => ((f t * Real.sin (2 * π * ν * t) : ℝ) : ℂ) := hsin.ofReal
  simp only [hsplit]
  rw [integral_sub hcosC (hsinC.const_mul I), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, hzero]
  simp

/-- **Parity, odd case** ([quarteroni2000numerical] §10.11.1, property 4): the Fourier transform
of a real-valued, integrable, odd function is purely imaginary and odd. -/
theorem fourierIntegral_odd_real {f : ℝ → ℝ} (hf : Integrable f) (hodd : ∀ t, f (-t) = -f t)
    (ν : ℝ) :
    (𝓕 (fun t => (f t : ℂ)) ν).re = 0 ∧
      𝓕 (fun t => (f t : ℂ)) (-ν) = -𝓕 (fun t => (f t : ℂ)) ν := by
  refine ⟨?_, ?_⟩
  · rw [fourierIntegral_odd_eq_integral_sin hf hodd]
    simp
  · rw [fourierIntegral_odd_eq_integral_sin hf hodd, fourierIntegral_odd_eq_integral_sin hf hodd]
    have : (fun t => f t * Real.sin (2 * π * -ν * t))
        = fun t => -(f t * Real.sin (2 * π * ν * t)) := by
      funext t
      rw [show 2 * π * -ν * t = -(2 * π * ν * t) by ring, Real.sin_neg]
      ring
    rw [this, integral_neg]
    push_cast
    ring

/-! ### The transform of a product -/

open scoped Convolution in
/-- **The transform of a product is the convolution of the transforms**
([quarteroni2000numerical] (10.76), second identity): for `f, g` integrable with `𝓕 g`
integrable, `𝓕 (f g) = 𝓕 f ⋆ 𝓕 g`, where `(F ⋆ G) ξ = ∫ F (ξ - η) G η dη` is Mathlib's
`MeasureTheory.convolution` with the multiplication of `ℂ`. Fubini, after replacing `g` almost
everywhere by `𝓕⁻ (𝓕 g)` (`ae_eq_fourierInv_fourier`); the textbook states the identity for
`f, g ∈ L¹` alone, where the convolution of the transforms need not exist. -/
theorem fourier_mul_eq_convolution {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hg' : Integrable (𝓕 g)) :
    𝓕 (f * g) = 𝓕 f ⋆[ContinuousLinearMap.mul ℂ ℂ] 𝓕 g := by
  funext ξ
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.mul_apply']
  -- replace `g` by the inverse transform of its transform, almost everywhere
  have hae : (fun t => 𝐞 (-⟪t, ξ⟫) • (f * g) t) =ᵐ[volume]
      fun t => 𝐞 (-⟪t, ξ⟫) • (f t * 𝓕⁻ (𝓕 g) t) := by
    filter_upwards [ae_eq_fourierInv_fourier hg hg'] with t ht
    rw [Pi.mul_apply, ht]
  rw [Real.fourier_eq, integral_congr_ae hae]
  -- the characters combine, and the double integral is integrable on the product
  have hchar : ∀ t η : V, ((𝐞 (-⟪t, ξ⟫) : Circle) : ℂ) * (𝐞 ⟪η, t⟫ : Circle)
      = (𝐞 (-⟪t, ξ - η⟫) : Circle) := by
    intro t η
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_sub_right, real_inner_comm η t]
    congr 2
    ring
  have hint : Integrable (fun p : V × V => ((𝐞 (-⟪p.1, ξ⟫) : Circle) : ℂ) * f p.1
      * ((𝐞 ⟪p.2, p.1⟫ : Circle) * 𝓕 g p.2)) (volume.prod volume) := by
    have h1 : Integrable (fun p : V × V => f p.1 * 𝓕 g p.2) (volume.prod volume) :=
      hf.mul_prod hg'
    have h2 : Integrable (fun p : V × V => (((𝐞 (-⟪p.1, ξ⟫) : Circle) : ℂ)
        * (𝐞 ⟪p.2, p.1⟫ : Circle)) * (f p.1 * 𝓕 g p.2)) (volume.prod volume) := by
      refine h1.bdd_mul (c := 1) ?_ (Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ ?_)
        · exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
        · exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
      · rw [norm_mul, Circle.norm_coe, Circle.norm_coe, mul_one]
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp only
    ring
  calc ∫ t, 𝐞 (-⟪t, ξ⟫) • (f t * 𝓕⁻ (𝓕 g) t)
      = ∫ t, ∫ η, ((𝐞 (-⟪t, ξ⟫) : Circle) : ℂ) * f t * ((𝐞 ⟪η, t⟫ : Circle) * 𝓕 g η) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]
        rw [← integral_const_mul, ← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun η => by ring)
    _ = ∫ η, ∫ t, ((𝐞 (-⟪t, ξ⟫) : Circle) : ℂ) * f t * ((𝐞 ⟪η, t⟫ : Circle) * 𝓕 g η) :=
        integral_integral_swap hint
    _ = ∫ η, 𝓕 f (ξ - η) * 𝓕 g η := by
        refine integral_congr_ae (Eventually.of_forall fun η => ?_)
        simp only
        rw [Real.fourier_eq f (ξ - η), ← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [Circle.smul_def, smul_eq_mul]
        rw [← hchar t η]
        ring

/-! ### The `L²` transform on `L¹ ∩ L²` -/

section L2

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The `L²` Fourier transform agrees with the Fourier integral on `L¹ ∩ L²`**: for `f` in
`L¹ ∩ L²`, Mathlib's unitary transform `MeasureTheory.Lp.fourierTransformₗᵢ` of the `L²` class of
`f` is, almost everywhere, the Fourier integral `𝓕 f`. Both define the same tempered distribution —
the `L²` transform by `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`, the integral by the
multiplication formula `∫ (𝓕 φ) • f = ∫ φ • 𝓕 f` — and both are locally integrable. -/
theorem coeFn_fourier_toLp {f : V → F} (hf1 : MemLp f 1) (hf2 : MemLp f 2) :
    ⇑(𝓕 (hf2.toLp f) : Lp F 2 volume) =ᵐ[volume] 𝓕 f := by
  have key := Lp.fourier_toTemperedDistribution_eq (hf2.toLp f)
  have hf1' : Integrable f := memLp_one_iff_integrable.mp hf1
  refine (ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (hf2.toLp f) : Lp F 2 volume)).locallyIntegrable (by norm_num))
    (continuous_fourierIntegral hf1').locallyIntegrable fun g hg hgs => ?_)
  set φ : SchwartzMap V ℂ := (hgs.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg) with hφ
  have hsmul : ∀ (c : ℝ) (v : F), c • v = (c : ℂ) • v := fun c v =>
    RCLike.real_smul_eq_coe_smul (K := ℂ) c v
  simp only [hsmul]
  have hkey := congrArg (fun T : TemperedDistribution V F => T φ) key
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hkey
  have hφ_int : Integrable (fun x => (g x : ℂ)) := φ.integrable
  have hflip : (innerₗ V).flip = innerₗ V := by
    ext x y
    simp
  have hmul := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (L := innerₗ V)
    Real.continuous_fourierChar continuous_inner hφ_int hf1'
  rw [hflip] at hmul
  calc ∫ x, (g x : ℂ) • (𝓕 (hf2.toLp f) : Lp F 2 volume) x
      = ∫ x, φ x • (𝓕 (hf2.toLp f) : Lp F 2 volume) x := rfl
    _ = ∫ x, (𝓕 φ) x • (hf2.toLp f : Lp F 2 volume) x := hkey.symm
    _ = ∫ x, (𝓕 fun y => (g y : ℂ)) x • f x := by
        refine integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx, SchwartzMap.fourier_coe]
        rfl
    _ = ∫ x, (g x : ℂ) • 𝓕 f x := hmul

/-- **Plancherel's identity on `L¹ ∩ L²`**: for `f, g ∈ L¹ ∩ L²`,
`∫ conj (𝓕 f) · 𝓕 g = ∫ conj f · g`, the inner product `⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` of `L²` written as
integrals of the pointwise transforms. Mathlib's `MeasureTheory.Lp.inner_fourier_eq` read through
`coeFn_fourier_toLp`. -/
theorem integral_conj_fourier_mul_fourier {f g : V → ℂ} (hf1 : MemLp f 1) (hf2 : MemLp f 2)
    (hg1 : MemLp g 1) (hg2 : MemLp g 2) :
    ∫ x, conj (𝓕 f x) * 𝓕 g x = ∫ x, conj (f x) * g x := by
  have h := Lp.inner_fourier_eq (hf2.toLp f) (hg2.toLp g)
  rw [L2.inner_def, L2.inner_def] at h
  simp only [RCLike.inner_apply'] at h
  have e1 : ∫ a, conj ((𝓕 (hf2.toLp f) : Lp ℂ 2 volume) a) * (𝓕 (hg2.toLp g) : Lp ℂ 2 volume) a
      = ∫ x, conj (𝓕 f x) * 𝓕 g x := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_fourier_toLp hf1 hf2, coeFn_fourier_toLp hg1 hg2] with x hx hy
    rw [hx, hy]
  have e2 : ∫ a, conj ((hf2.toLp f : Lp ℂ 2 volume) a) * (hg2.toLp g : Lp ℂ 2 volume) a
      = ∫ x, conj (f x) * g x := by
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with x hx hy
    rw [hx, hy]
  rw [e1, e2] at h
  exact h

end L2

end Real
