/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $V$ be a finite-dimensional real inner product space with its Lebesgue measure, and let $E$ be a
complex normed space. The Fourier transform of an integrable $f : V \to E$ and the inverse transform
of an integrable $g : V \to E$ are
$$\mathcal{F} f(w) = \int_V e^{-2\pi i \langle v, w \rangle} f(v) \, dv, \qquad \mathcal{F}^{-1}
  g(v) = \int_V e^{2\pi i \langle v, w \rangle} g(w) \, dw.$$
This file proves facts about the Fourier integral that Mathlib
(`Mathlib.Analysis.Fourier.FourierTransform`, `Mathlib.Analysis.Fourier.Inversion`,
`Mathlib.Analysis.Fourier.Convolution`) does not state in the form that a textbook uses. They are
Property 10.3 of [quarteroni2000numerical], §10.11.1, and the properties numbered 1–5 after it. The
transform and the inverse transform of an integrable function are continuous. If $f$ and
$\mathcal{F} f$ are integrable, then $f = \mathcal{F}^{-1} \mathcal{F} f$ almost everywhere. The
file proves the rules for a constant multiple, a translation, a modulation and a scaling, and the
rules of parity for a real function. The transform of a product is the convolution of the
transforms. On $L^1 \cap L^2$, the $L^2$ transform of Mathlib agrees with the Fourier integral, so
that Plancherel's identity holds there with the integrals written out.

## Main results

* `Real.continuous_fourierIntegral` and `Real.continuous_fourierIntegralInv`: the transform and the
  inverse transform of an integrable function are continuous.
* `Real.ae_eq_fourierInv_fourier`: **Fourier inversion almost everywhere**,
  $f = \mathcal{F}^{-1} \mathcal{F} f$ a.e. for integrable $f$ and $\mathcal{F} f$.
* `Real.fourierIntegral_comp_sub_right`: the translation rule $\mathcal{F}(f(\cdot - a))(\nu) =
  e^{-2\pi i a \nu} \mathcal{F} f(\nu)$.
* `Real.fourierIntegral_fourierChar_mul`: the modulation rule $\mathcal{F}(e^{-2\pi i a \cdot}
  f)(\nu) = \mathcal{F} f(\nu + a)$.
* `Real.fourierIntegral_comp_mul_left`: the scaling rule $\mathcal{F}(f(a \cdot))(\nu) = |a|^{-1}
  \mathcal{F} f(\nu/a)$.
* `Real.fourierIntegral_even_eq_integral_cos` and `Real.fourierIntegral_even_real`: the transform of
  a real even function is its cosine transform, and it is real and even.
* `Real.fourierIntegral_odd_eq_integral_sin` and `Real.fourierIntegral_odd_real`: the transform of a
  real odd function is $-i$ times its sine transform, and it is purely imaginary and odd.
* `Real.fourier_mul_eq_convolution`: $\mathcal{F}(fg) = \mathcal{F} f \star \mathcal{F} g$ for
  $f, g, \mathcal{F} g \in L^1$.
* `Real.coeFn_fourier_toLp`: on $L^1 \cap L^2$, the $L^2$ transform is the Fourier integral almost
  everywhere.
* `Real.integral_conj_fourier_mul_fourier`: Plancherel's identity $\int \overline{\mathcal{F} f} \,
  \mathcal{F} g = \int \bar f g$ for $f, g \in L^1 \cap L^2$.

## Proof outline

The inversion almost everywhere is proved by duality, not by the Gaussian regularization of
Mathlib's proof. Let $\varphi$ be a smooth function with compact support. The multiplication formula
$\int (\mathcal{F} F) \varphi = \int F (\mathcal{F} \varphi)$
(`VectorFourier.integral_bilin_fourierIntegral_eq_flip`), applied twice, gives $\int \varphi \,
\mathcal{F}^{-1} \mathcal{F} f = \int \mathcal{F}(\mathcal{F}^{-1} \varphi) \, f = \int \varphi f$.
The last step is the inversion formula for the Schwartz function $\varphi$. Two locally integrable
functions with the same integrals against all such $\varphi$ agree almost everywhere
(`ae_eq_of_integral_contDiff_smul_eq`).

The convolution identity is Fubini's theorem, after $g$ is replaced almost everywhere by
$\mathcal{F}^{-1} \mathcal{F} g$. The identification of the two transforms on $L^1 \cap L^2$ again
goes through tempered distributions: the two transforms of $f$ define the same tempered distribution
(`MeasureTheory.Lp.fourier_toTemperedDistribution_eq` and the multiplication formula), and both are
locally integrable.

## Notation

* `𝓕 f` and `𝓕⁻ f`: the Fourier transform $\mathcal{F} f$ and the inverse transform
  $\mathcal{F}^{-1} f$ of Mathlib.
* `𝐞 x`: Mathlib's `Real.fourierChar`, the character $e^{2\pi i x}$.

## Implementation notes

* The statements that do not use the order of $\mathbb{R}$ are stated on a finite-dimensional real
  inner product space $V$, the setting of Mathlib's `𝓕`. The translation, modulation, scaling and
  parity rules on the line are stated on $\mathbb{R}$.
* Mathlib's `MeasureTheory.Integrable.fourierInv_fourier_eq` gives the inversion formula at the
  points of continuity only.
* Mathlib has the dual convolution statement `Real.fourier_mul_convolution_eq`, $\mathcal{F}(f \star
  g) = \mathcal{F} f \cdot \mathcal{F} g$, and the form `SchwartzMap.fourier_convolution` for the
  Schwartz class.
* The $L^2$ transform is Mathlib's unitary `MeasureTheory.Lp.fourierTransformₗᵢ`, defined by
  extension from the Schwartz space.
-/

open MeasureTheory Filter Topology Complex

open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace Real

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Continuity -/

/-- The Fourier transform $\mathcal{F} f$ of an integrable function $f : V \to E$ is continuous.

This is a special case of Mathlib's `VectorFourier.fourierIntegral_continuous`. -/
theorem continuous_fourierIntegral {f : V → E} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

/-- The inverse Fourier transform $\mathcal{F}^{-1} f$ of an integrable function $f : V \to E$ is
continuous. -/
theorem continuous_fourierIntegralInv {f : V → E} (hf : Integrable f) : Continuous (𝓕⁻ f) := by
  rw [fourierInv_eq_fourier_comp_neg]
  exact continuous_fourierIntegral hf.comp_neg

/-! ### Fourier inversion almost everywhere -/

/-- **Fourier inversion almost everywhere.** Let $E$ be a complex Banach space, and let
$f : V \to E$ be integrable with $\mathcal{F} f$ integrable. Then
$$f = \mathcal{F}^{-1}(\mathcal{F} f) \quad \text{almost everywhere.}$$
No continuity of $f$ is assumed. This is Property 10.3 of [quarteroni2000numerical].

At a point of continuity of $f$ the identity holds pointwise, which is Mathlib's
`MeasureTheory.Integrable.fourierInv_fourier_eq`. The idea of the proof: test both sides against
a smooth compactly supported $\varphi$. The multiplication formula, applied twice, gives $\int
\varphi \, \mathcal{F}^{-1} \mathcal{F} f = \int (\mathcal{F}^{-1} \varphi) \, \mathcal{F} f =
\int \mathcal{F}(\mathcal{F}^{-1} \varphi) \, f = \int \varphi f$, where the last step is the
inversion formula for the Schwartz function $\varphi$. -/
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

/-! ### Linearity, translation, modulation and scaling -/

/-- The Fourier transform of a constant multiple: for $c \in \mathbb{C}$, $f : V \to E$ and
$\nu \in V$, $\mathcal{F}(c f)(\nu) = c \, \mathcal{F} f(\nu)$.

No integrability of $f$ is needed: Mathlib's integral of a function that is not integrable is
$0$. -/
theorem fourierIntegral_const_smul (c : ℂ) (f : V → E) (ν : V) :
    𝓕 (fun t => c • f t) ν = c • 𝓕 f ν :=
  congrFun (VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ V) f c) ν

/-- **The translation rule** on $V$: for $f : V \to E$ and $v_0, w \in V$,
$$\mathcal{F}\bigl(f(\cdot + v_0)\bigr)(w) = e^{2\pi i \langle v_0, w \rangle} \, \mathcal{F}
  f(w).$$

This is Mathlib's `VectorFourier.fourierIntegral_comp_add_right`, stated for `𝓕`. -/
theorem fourierIntegral_comp_add_right (f : V → E) (v₀ w : V) :
    𝓕 (fun v => f (v + v₀)) w = 𝐞 ⟪v₀, w⟫ • 𝓕 f w :=
  congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ V) f v₀) w

/-- **The translation rule** on the line: for $f : \mathbb{R} \to E$ and $a, \nu \in \mathbb{R}$,
$$\mathcal{F}\bigl(f(\cdot - a)\bigr)(\nu) = e^{-2\pi i a \nu} \, \mathcal{F} f(\nu).$$
So a delay by $a$ multiplies the transform by the phase $e^{-2\pi i a \nu}$. -/
theorem fourierIntegral_comp_sub_right (f : ℝ → E) (a ν : ℝ) :
    𝓕 (fun t => f (t - a)) ν = 𝐞 (-(a * ν)) • 𝓕 f ν := by
  have := fourierIntegral_comp_add_right f (-a) ν
  simp only [← sub_eq_add_neg] at this
  rw [this]
  congr 2
  simp [mul_comm]

/-- **The modulation rule**: for $f : \mathbb{R} \to E$ and $a, \nu \in \mathbb{R}$,
$$\mathcal{F}\bigl(t \mapsto e^{-2\pi i t a} f(t)\bigr)(\nu) = \mathcal{F} f(\nu + a).$$
So multiplication by the character $t \mapsto e^{-2\pi i t a}$ translates the transform by $a$. -/
theorem fourierIntegral_fourierChar_mul (f : ℝ → E) (a ν : ℝ) :
    𝓕 (fun t => (𝐞 (-(t * a)) : ℂ) • f t) ν = 𝓕 f (ν + a) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Circle.smul_def, smul_smul]
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 3
  ring

/-- **The scaling rule** (property 2 of [quarteroni2000numerical], §10.11.1). For $a \in \mathbb{R}$
with $a \ne 0$, $f : \mathbb{R} \to E$ and $\nu \in \mathbb{R}$,
$$\mathcal{F}\bigl(f(a \cdot)\bigr)(\nu) = |a|^{-1} \, \mathcal{F} f(\nu/a).$$

The proof is the change of variables $t \mapsto at$ in the defining integral
(`MeasureTheory.Measure.integral_comp_mul_left`), which needs no integrability. -/
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

/-- **The transform of a real function in real form.** For an integrable
$f : \mathbb{R} \to \mathbb{R}$ and $\nu \in \mathbb{R}$,
$$\mathcal{F} f(\nu) = \int f(t) \cos(2\pi \nu t) \, dt - i \int f(t) \sin(2\pi \nu t) \, dt,$$
because $e^{-2\pi i \nu t} = \cos(2\pi \nu t) - i \sin(2\pi \nu t)$. -/
theorem fourierIntegral_ofReal_eq_integral_cos_sub_integral_sin {f : ℝ → ℝ} (hf : Integrable f)
    (ν : ℝ) :
    𝓕 (fun t => (f t : ℂ)) ν = ((∫ t, f t * Real.cos (2 * π * ν * t) : ℝ) : ℂ)
      - I * ((∫ t, f t * Real.sin (2 * π * ν * t) : ℝ) : ℂ) := by
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
  have hcosC : Integrable fun t => ((f t * Real.cos (2 * π * ν * t) : ℝ) : ℂ) := hcos.ofReal
  have hsinC : Integrable fun t => ((f t * Real.sin (2 * π * ν * t) : ℝ) : ℂ) := hsin.ofReal
  simp only [hsplit]
  rw [integral_sub hcosC (hsinC.const_mul I), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal]

/-- **The transform of a real even function is its cosine transform.** For an integrable
$f : \mathbb{R} \to \mathbb{R}$ with $f(-t) = f(t)$ for all $t$, and $\nu \in \mathbb{R}$,
$$\mathcal{F} f(\nu) = \int f(t) \cos(2\pi \nu t) \, dt.$$
The sine term of `Real.fourierIntegral_ofReal_eq_integral_cos_sub_integral_sin` is $0$, because
its integrand is odd. -/
theorem fourierIntegral_even_eq_integral_cos {f : ℝ → ℝ} (hf : Integrable f)
    (heven : ∀ t, f (-t) = f t) (ν : ℝ) :
    𝓕 (fun t => (f t : ℂ)) ν = ((∫ t, f t * Real.cos (2 * π * ν * t) : ℝ) : ℂ) := by
  have hodd : ∫ t, f t * Real.sin (2 * π * ν * t) = 0 := by
    have h := MeasureTheory.integral_neg_eq_self (fun t => f t * Real.sin (2 * π * ν * t)) volume
    have h' : ∀ t, f (-t) * Real.sin (2 * π * ν * -t) = -(f t * Real.sin (2 * π * ν * t)) := by
      intro t
      rw [heven, show 2 * π * ν * -t = -(2 * π * ν * t) by ring, Real.sin_neg]
      ring
    simp only [h', integral_neg] at h
    linarith
  rw [fourierIntegral_ofReal_eq_integral_cos_sub_integral_sin hf, hodd]
  simp

/-- **Parity, even case** (property 4 of [quarteroni2000numerical], §10.11.1). Let
$f : \mathbb{R} \to \mathbb{R}$ be integrable and even. Then for every $\nu \in \mathbb{R}$,
$\mathcal{F} f(\nu)$ is real and $\mathcal{F} f(-\nu) = \mathcal{F} f(\nu)$. -/
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

/-- **The transform of a real odd function is $-i$ times its sine transform.** For an integrable
$f : \mathbb{R} \to \mathbb{R}$ with $f(-t) = -f(t)$ for all $t$, and $\nu \in \mathbb{R}$,
$$\mathcal{F} f(\nu) = -i \int f(t) \sin(2\pi \nu t) \, dt.$$
The cosine term is $0$, because its integrand is odd. -/
theorem fourierIntegral_odd_eq_integral_sin {f : ℝ → ℝ} (hf : Integrable f)
    (hodd : ∀ t, f (-t) = -f t) (ν : ℝ) :
    𝓕 (fun t => (f t : ℂ)) ν = -I * ((∫ t, f t * Real.sin (2 * π * ν * t) : ℝ) : ℂ) := by
  have hzero : ∫ t, f t * Real.cos (2 * π * ν * t) = 0 := by
    have h := MeasureTheory.integral_neg_eq_self (fun t => f t * Real.cos (2 * π * ν * t)) volume
    have h' : ∀ t, f (-t) * Real.cos (2 * π * ν * -t) = -(f t * Real.cos (2 * π * ν * t)) := by
      intro t
      rw [hodd, show 2 * π * ν * -t = -(2 * π * ν * t) by ring, Real.cos_neg]
      ring
    simp only [h', integral_neg] at h
    linarith
  rw [fourierIntegral_ofReal_eq_integral_cos_sub_integral_sin hf, hzero]
  simp

/-- **Parity, odd case** (property 4 of [quarteroni2000numerical], §10.11.1). Let
$f : \mathbb{R} \to \mathbb{R}$ be integrable and odd. Then for every $\nu \in \mathbb{R}$,
$\mathcal{F} f(\nu)$ is purely imaginary and $\mathcal{F} f(-\nu) = -\mathcal{F} f(\nu)$. -/
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
/-- **The transform of a product is the convolution of the transforms** ((10.76) of
[quarteroni2000numerical], second identity). Let $f, g : V \to \mathbb{C}$ be integrable, with
$\mathcal{F} g$ integrable. Then
$$\mathcal{F}(fg) = \mathcal{F} f \star \mathcal{F} g, \qquad (F \star G)(\xi) = \int_V F(\eta)
  \, G(\xi - \eta) \, d\eta.$$

The convolution is Mathlib's `MeasureTheory.convolution` with the multiplication of
$\mathbb{C}$. The proof is Fubini's theorem, after $g$ is replaced almost everywhere by
$\mathcal{F}^{-1} \mathcal{F} g$ (`Real.ae_eq_fourierInv_fourier`). The textbook states the
identity for $f, g \in L^1$ alone, where the convolution of the transforms need not exist; the
hypothesis that $\mathcal{F} g$ is integrable is added here. -/
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

/-! ### The $L^2$ transform on $L^1 \cap L^2$ -/

section L2

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The $L^2$ Fourier transform agrees with the Fourier integral on $L^1 \cap L^2$.** Let $F$ be a
complex Hilbert space, and let $f : V \to F$ be in $L^1 \cap L^2$. Then the $L^2$ transform of
the class of $f$ in $L^2$ is equal to the Fourier integral $\mathcal{F} f$ almost everywhere.

The $L^2$ transform is Mathlib's unitary `MeasureTheory.Lp.fourierTransformₗᵢ`. The idea of the
proof: both functions define the same tempered distribution (the $L^2$ transform by
`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`, the integral by the multiplication formula
$\int (\mathcal{F} \varphi) f = \int \varphi \, \mathcal{F} f$), and both are locally
integrable. -/
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

/-- **Plancherel's identity on $L^1 \cap L^2$.** For $f, g : V \to \mathbb{C}$ in $L^1 \cap L^2$,
$$\int_V \overline{\mathcal{F} f(x)} \, \mathcal{F} g(x) \, dx = \int_V \overline{f(x)} \, g(x)
  \, dx.$$
This is the identity $\langle \mathcal{F} f, \mathcal{F} g \rangle = \langle f, g \rangle$ of
$L^2$, written as integrals of the pointwise transforms.

The proof reads Mathlib's `MeasureTheory.Lp.inner_fourier_eq` through `Real.coeFn_fourier_toLp`. -/
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
