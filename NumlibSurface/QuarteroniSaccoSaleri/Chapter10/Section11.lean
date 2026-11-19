/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Numlib.Analysis.Convolution.Bochner
import Numlib.Analysis.Fourier.FourierIntegral
import Numlib.Analysis.Fourier.Periodisation
import Numlib.Analysis.SpecialFunctions.LaplaceTransform

/-!
# Quarteroni, Sacco and Saleri, Section 10.11: Transforms and their applications

This module formalizes Section 10.11 of [quarteroni2000numerical]. The Fourier transform of
$f \in L^1(\mathbb{R})$ is $F(\nu) = \int_{-\infty}^{\infty} f(t) e^{-2\pi i \nu t} \, dt$
(Definition 10.1). The module states the inversion theorem (Property 10.3), the five properties of
the transform (10.75)–(10.77) with Examples 10.5–10.6, linear time-invariant systems with the
transfer function (10.81), the ideal low-pass filter (Example 10.7) and the sampling formula
(10.82). It then states the Laplace transform $L(s) = \int_0^\infty f(t) e^{-st} \, dt$ (Definition
10.2) with the unit step (Example 10.8), the region of convergence (Property 10.4) and the transform
of a derivative (Example 10.9), and the Z-transform $Z(z) = \sum_{n \ge 0} f(n\Delta t) z^{-n}$
(Definition 10.3) with the discrete Laplace transform (10.84).

The Fourier transform of the book is Mathlib's `Real.fourierIntegral`, written `𝓕`, with no change
of normalization. The Laplace transform and the Z-transform come from
`Numlib.Analysis.SpecialFunctions.LaplaceTransform`, where the Laplace transform is the limit of the
truncated integrals, as in Definition 10.2. The facts about the Fourier transform that Mathlib does
not state come from `Numlib.Analysis.Fourier.FourierIntegral`,
`Numlib.Analysis.Fourier.Periodisation` and `Numlib.Analysis.Convolution.Bochner`.

## Main definitions

* Definition 10.1, `QuarteroniSaccoSaleri.Chapter10.definition_10_1` and
  `QuarteroniSaccoSaleri.Chapter10.definition_10_1_inv`: the Fourier transform and its inverse.
* Equation (10.77), `QuarteroniSaccoSaleri.Chapter10.equation_10_77`: the convolution $(f \star
  g)(t) = \int f(\tau) g(t - \tau) \, d\tau$.
* Definition 10.2, `QuarteroniSaccoSaleri.Chapter10.definition_10_2` and
  `QuarteroniSaccoSaleri.Chapter10.laplace`: the existence of the Laplace integral, and the Laplace
  transform.
* Definition 10.3, `QuarteroniSaccoSaleri.Chapter10.definition_10_3`: the Z-transform.

## Main results

* Definition 10.1, `QuarteroniSaccoSaleri.Chapter10.definition_10_1_eq_fourierIntegral` and
  `QuarteroniSaccoSaleri.Chapter10.definition_10_1_inv_eq_fourierIntegralInv`: the transforms of the
  book are Mathlib's `𝓕` and `𝓕⁻`.
* Property 10.3, `QuarteroniSaccoSaleri.Chapter10.property_10_3`: the inversion theorem.
* Equation (10.75), `QuarteroniSaccoSaleri.Chapter10.equation_10_75`: property 1, linearity.
* Property 2, `QuarteroniSaccoSaleri.Chapter10.property_scaling`: the transform of $f(\alpha t)$ is
  $|\alpha|^{-1} F(\nu/\alpha)$.
* Property 3, `QuarteroniSaccoSaleri.Chapter10.property_duality`: the transform of $F(-t)$ is $f$.
* Property 4, `QuarteroniSaccoSaleri.Chapter10.property_parity`: the transform of a real even (odd)
  function is real and even (purely imaginary and odd).
* Equation (10.77), `QuarteroniSaccoSaleri.Chapter10.equation_10_77_integrable`: the convolution of
  two functions of $L^1(\mathbb{R})$ is in $L^1(\mathbb{R})$.
* Equation (10.76), `QuarteroniSaccoSaleri.Chapter10.equation_10_76`: property 5, the transform of a
  convolution is the product of the transforms, and conversely.
* Example 10.5, `QuarteroniSaccoSaleri.Chapter10.example_10_5_rect` and
  `QuarteroniSaccoSaleri.Chapter10.example_10_5_saw`: the transforms of the rectangular and the
  sawtooth functions.
* Example 10.6, `QuarteroniSaccoSaleri.Chapter10.example_10_6`: the transforms of a constant and of
  a cosine are Dirac masses (10.78)–(10.79).
* Equation (10.80), `QuarteroniSaccoSaleri.Chapter10.equation_10_80`: a bounded operator on
  $L^1(\mathbb{R})$ that commutes with translations satisfies $S(f \star g) = f \star S(g)$.
* Equation (10.81), `QuarteroniSaccoSaleri.Chapter10.equation_10_81`: the transfer function,
  $U(\nu) = I(\nu) H(\nu)$.
* Example 10.7, `QuarteroniSaccoSaleri.Chapter10.example_10_7`: the impulse response of the ideal
  low-pass filter.
* Equation (10.82), `QuarteroniSaccoSaleri.Chapter10.equation_10_82`: the sampling formula.
* Definition 10.2, `QuarteroniSaccoSaleri.Chapter10.definition_10_2_fourier`: the Laplace transform
  as a Fourier transform.
* Example 10.8, `QuarteroniSaccoSaleri.Chapter10.example_10_8`: the Laplace transform of the unit
  step is $1/s$ for $\operatorname{Re} s > 0$.
* Property 10.4, `QuarteroniSaccoSaleri.Chapter10.property_10_4`: the Laplace integral exists in the
  half-plane to the right of the abscissa of convergence.
* Example 10.9, `QuarteroniSaccoSaleri.Chapter10.example_10_9` and
  `QuarteroniSaccoSaleri.Chapter10.example_10_9_solution`: the Laplace transform of $y' + ay = g$,
  and the solution for $g = 1$.
* Definition 10.3, `QuarteroniSaccoSaleri.Chapter10.definition_10_3_summable`: the convergence of
  the Z-transform outside the Cauchy–Hadamard radius.
* Equation (10.84), `QuarteroniSaccoSaleri.Chapter10.definition_10_3_eq_discreteLaplace`: the
  Z-transform is the discrete Laplace transform.

## Deviations from the source

* **Definition 10.1, equation (10.74), and properties 2 and 5** (generalization). The Fourier,
  inverse Fourier, and convolution formulas use total Bochner integrals. The inverse formula
  agrees with the symmetric principal-value limit for the integrable transforms used in Property
  10.3. Scaling holds for all functions under this integral convention.
* **Examples 10.5–10.7 and equation (10.81)** (reading). The rectangle and sawtooth allow any
  real amplitude. The rectangle and ideal filter give the removable value at zero, while the
  sawtooth theorem treats nonzero frequencies. Example 10.6 states the constant and cosine
  identities as tempered distributions. `equation_10_81` assumes an integrable input and impulse
  response and takes the output to be their convolution.
* **Equation (10.82)** (reading). The discrete samples range over all integers and the pointwise
  alias sum assumes summability in addition to the continuity and compact-support hypotheses.
* **Definitions 10.2 and 10.3** (generalization). The Laplace predicate uses total truncated
  integrals without assuming local integrability and the transform is assigned zero outside
  convergence. The Fourier relation assumes absolute integrability. The Z-transform definition
  accepts any real sample step, with a total infinite sum. The discrete Laplace identity assumes
  $\operatorname{Re}s>0$ and absolute summability.
* **Example 10.9** (reading). `example_10_9` uses the factor $e^{-st}$ in the Laplace
  integration, with sufficient integrability and decay for integration by parts. The printed
  prose says $e^{st}$. `example_10_9_solution` establishes the ODE and initial value for $a\neq
  0$ by differentiating the formula.
* **Property 3** (correction). The book states the duality with no hypotheses. The library assumes
  that $f$ is continuous and that $f$ and $F$ are integrable. See
  `QuarteroniSaccoSaleri.Chapter10.property_duality`.
* **Equation (10.76), second identity** (correction). The book states $\mathcal{F}(fg) = F \star G$
  for $f, g \in L^1$ alone, where $F \star G$ need not exist. The library also assumes $G \in L^1$.
  See `QuarteroniSaccoSaleri.Chapter10.equation_10_76`.
* **Equation (10.80)** (correction). As printed, the identity has no domain and no continuity of
  $S$, and linearity and shift invariance do not prove it. The library takes $S$ bounded on
  $L^1(\mathbb{R})$ and commuting with translations. See
  `QuarteroniSaccoSaleri.Chapter10.equation_10_80`.
* **Equation (10.82)** (reading). The book derives the formula through a distributional sampled
  signal, for an input that may jump at the ends of its support. The library assumes the input
  continuous with compact support. See `QuarteroniSaccoSaleri.Chapter10.equation_10_82`.
* **The Laplace transform as a Fourier transform (Section 10.11.3)** (reading). The book writes
  $L(s) = \mathcal{F}(e^{-\sigma t} \tilde f)$ without an argument. The argument is $\omega/2\pi$.
  See `QuarteroniSaccoSaleri.Chapter10.definition_10_2_fourier`.
* **The Cauchy–Hadamard radius of the Z-transform** (reading). The radius
  $R = \limsup |f(n\Delta t)|^{1/n}$ is read in $[0, \infty]$. See
  `QuarteroniSaccoSaleri.Chapter10.definition_10_3_summable`.
* **The discrete Laplace transform (Section 10.11.4)** (typo). The book prints the substitution
  $z = e^{-s\Delta t}$. It is $z = e^{s\Delta t}$. See
  `QuarteroniSaccoSaleri.Chapter10.definition_10_3_eq_discreteLaplace`.

## Not formalized

* **Example 10.7, second claim** (the spectrum of the output is $IH$). It is (10.81) with
  $h \notin L^1$, which needs the $L^2$ theory of the transform.
-/

open MeasureTheory Filter Topology Complex Set

open scoped FourierTransform ComplexConjugate Real Convolution

namespace QuarteroniSaccoSaleri.Chapter10

/-! ### Definition 10.1: the Fourier transform -/

/-- **Definition 10.1** of [quarteroni2000numerical]. For $f \in L^1(\mathbb{R})$ the **Fourier
transform** of $f$ is
$$F(\nu) = \int_{-\infty}^{\infty} f(t) e^{-2\pi i \nu t} \, dt, \qquad \nu \in \mathbb{R}.$$

The definition is the Bochner integral, which is $0$ when the integrand is not integrable. It is
Mathlib's `𝓕 f` by `QuarteroniSaccoSaleri.Chapter10.definition_10_1_eq_fourierIntegral`. The
inverse transform is `QuarteroniSaccoSaleri.Chapter10.definition_10_1_inv`.

**Generalization.** The identity uses total Bochner integration and arbitrary functions. In the
inverse transform, the integral agrees with the symmetric limit under the source's
integrability assumption. -/
noncomputable def definition_10_1 (f : ℝ → ℂ) (ν : ℝ) : ℂ :=
  ∫ t : ℝ, f t * Complex.exp (-(2 * π * ν * t) * I)

/-- **Definition 10.1** of [quarteroni2000numerical], the inverse transform. For
$F : \mathbb{R} \to \mathbb{C}$ the **inverse Fourier transform** is
$$f(t) = \int_{-\infty}^{\infty} F(\nu) e^{2\pi i \nu t} \, d\nu, \qquad t \in \mathbb{R}.$$

**Generalization.** The identity uses total Bochner integration and arbitrary functions. In the
inverse transform, the integral agrees with the symmetric limit under the source's
integrability assumption. -/
noncomputable def definition_10_1_inv (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ν : ℝ, F ν * Complex.exp ((2 * π * ν * t) * I)

/-- **Definition 10.1** of [quarteroni2000numerical], identification with Mathlib. For every
$f : \mathbb{R} \to \mathbb{C}$ the Fourier transform of the book is Mathlib's Fourier transform
`𝓕 f`, with no change of normalization. -/
theorem definition_10_1_eq_fourierIntegral (f : ℝ → ℂ) : definition_10_1 f = 𝓕 f := by
  funext ν
  rw [definition_10_1, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- **Definition 10.1** of [quarteroni2000numerical], identification with Mathlib. For every
$F : \mathbb{R} \to \mathbb{C}$ the inverse transform of the book is Mathlib's inverse Fourier
transform `𝓕⁻ F`. -/
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

/-- **Property 10.3** of [quarteroni2000numerical] (inversion theorem). Let $f \in L^1(\mathbb{R})$
with $F = \mathcal{F} f \in L^1(\mathbb{R})$, and let
$g(t) = \int F(\nu) e^{2\pi i \nu t} \, d\nu$. Then $g$ is continuous, $g(t) \to 0$ as
$|t| \to \infty$, $f = g$ almost everywhere, and $f(t) = g(t)$ at every point $t$ where $f$ is
continuous.

The book writes $g$ as a Cauchy principal value. Since $F \in L^1$, it is the Bochner integral.
The continuity is `Real.continuous_fourierIntegralInv`, the decay is the Riemann–Lebesgue lemma
`Real.zero_at_infty_fourier`, the equality almost everywhere is `Real.ae_eq_fourierInv_fourier`,
and the equality at points of continuity is Mathlib's
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

/-! ### Properties 1–5 of the Fourier transform -/

/-- **Equation (10.75)** of [quarteroni2000numerical], property 1 (linearity). Let
$f, g \in L^1(\mathbb{R})$, $\alpha, \beta \in \mathbb{C}$ and $\nu \in \mathbb{R}$. Then
$$\mathcal{F}(\alpha f + \beta g)(\nu) = \alpha \mathcal{F} f(\nu) + \beta \mathcal{F} g(\nu),$$
and the same holds for the inverse transform $\mathcal{F}^{-1}$. -/
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

/-- **Section 10.11** of [quarteroni2000numerical], property 2 of the Fourier transform (scaling).
Let $\alpha \in \mathbb{R}$ with $\alpha \neq 0$, let $f : \mathbb{R} \to \mathbb{C}$, and let
$f_\alpha(t) = f(\alpha t)$. Then for every $\nu \in \mathbb{R}$
$$\mathcal{F} f_\alpha(\nu) = |\alpha|^{-1} \mathcal{F} f(\nu/\alpha).$$

The statement needs no integrability, because both sides are $0$ when $f$ is not integrable. The
proof specializes `Real.fourierIntegral_comp_mul_left`.

**Generalization.** The identity uses total Bochner integration and arbitrary functions. In the
inverse transform, the integral agrees with the symmetric limit under the source's
integrability assumption. -/
theorem property_scaling {α : ℝ} (hα : α ≠ 0) (f : ℝ → ℂ) (ν : ℝ) :
    𝓕 (fun t => f (α * t)) ν = ((|α|⁻¹ : ℝ) : ℂ) * 𝓕 f (ν / α) := by
  rw [Real.fourierIntegral_comp_mul_left hα, Complex.real_smul]

/-- **Section 10.11** of [quarteroni2000numerical], property 3 of the Fourier transform (duality).
Let $f : \mathbb{R} \to \mathbb{C}$ be continuous and integrable, with $\mathcal{F} f$
integrable. Then $g(t) = \mathcal{F} f(-t)$ has the Fourier transform $\mathcal{F} g = f$.

**Correction.** The book states the property with no hypotheses. The continuity of $f$ is
needed, or else the conclusion holds only almost everywhere, as in Property 10.3.

The proof uses Mathlib's `fourierInv_eq_fourier_comp_neg` and
`Continuous.fourierInv_fourier_eq`. -/
theorem property_duality {f : ℝ → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hF : Integrable (𝓕 f)) :
    𝓕 (fun t => 𝓕 f (-t)) = f := by
  rw [← Real.fourierInv_eq_fourier_comp_neg]
  exact hc.fourierInv_fourier_eq hf hF

/-- **Section 10.11** of [quarteroni2000numerical], property 4 of the Fourier transform (parity).
Let $f : \mathbb{R} \to \mathbb{R}$ be integrable and let $\nu \in \mathbb{R}$. If $f$ is even,
then $\mathcal{F} f(\nu)$ is real and $\mathcal{F} f(-\nu) = \mathcal{F} f(\nu)$. If $f$ is odd,
then $\mathcal{F} f(\nu)$ is purely imaginary and $\mathcal{F} f(-\nu) = -\mathcal{F} f(\nu)$.

The transform is taken of $f$ read as a complex function. The proof specializes
`Real.fourierIntegral_even_real` and `Real.fourierIntegral_odd_real`. -/
theorem property_parity {f : ℝ → ℝ} (hf : Integrable f) (ν : ℝ) :
    ((∀ t, f (-t) = f t) →
        (𝓕 (fun t => (f t : ℂ)) ν).im = 0 ∧
          𝓕 (fun t => (f t : ℂ)) (-ν) = 𝓕 (fun t => (f t : ℂ)) ν) ∧
      ((∀ t, f (-t) = -f t) →
        (𝓕 (fun t => (f t : ℂ)) ν).re = 0 ∧
          𝓕 (fun t => (f t : ℂ)) (-ν) = -𝓕 (fun t => (f t : ℂ)) ν) :=
  ⟨fun heven => Real.fourierIntegral_even_real hf heven ν,
    fun hodd => Real.fourierIntegral_odd_real hf hodd ν⟩

/-- **Equation (10.77)** of [quarteroni2000numerical]. For $f, g : \mathbb{R} \to \mathbb{C}$ the
**convolution** is
$$(f \star g)(t) = \int_{-\infty}^{\infty} f(\tau) g(t - \tau) \, d\tau.$$

It is Mathlib's `MeasureTheory.convolution` with the multiplication of $\mathbb{C}$, by
`QuarteroniSaccoSaleri.Chapter10.equation_10_77_eq_convolution`.

**Generalization.** The identity uses total Bochner integration and arbitrary functions. In the
inverse transform, the integral agrees with the symmetric limit under the source's
integrability assumption. -/
noncomputable def equation_10_77 (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ τ : ℝ, f τ * g (t - τ)

/-- For $f, g : \mathbb{R} \to \mathbb{C}$, the convolution (10.77) is Mathlib's convolution
`f ⋆[ContinuousLinearMap.mul ℂ ℂ] g` with the multiplication of $\mathbb{C}$. -/
theorem equation_10_77_eq_convolution (f g : ℝ → ℂ) :
    equation_10_77 f g = f ⋆[ContinuousLinearMap.mul ℂ ℂ] g := rfl

/-- **Equation (10.77)** of [quarteroni2000numerical], integrability. If $f, g \in L^1(\mathbb{R})$,
then $f \star g \in L^1(\mathbb{R})$.

The proof specializes `MeasureTheory.Integrable.integrable_convolution`. -/
theorem equation_10_77_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (equation_10_77 f g) := by
  rw [equation_10_77_eq_convolution]
  exact hf.integrable_convolution _ hg

/-- **Equation (10.76)** of [quarteroni2000numerical], property 5 (convolution and product). Let
$f, g \in L^1(\mathbb{R})$. Then $\mathcal{F}(f \star g)(\nu) = \mathcal{F} f(\nu) \,
\mathcal{F} g(\nu)$ for every $\nu \in \mathbb{R}$. If moreover
$\mathcal{F} g \in L^1(\mathbb{R})$, then $\mathcal{F}(fg) = \mathcal{F} f \star \mathcal{F} g$.

**Correction.** The book states the second identity for $f, g \in L^1$ alone. Then
$\mathcal{F} f \star \mathcal{F} g$ need not exist, so the hypothesis $\mathcal{F} g \in L^1$ is
added.

The first identity is Mathlib's `Real.fourier_mul_convolution_eq`, and the second is
`Real.fourier_mul_eq_convolution`. -/
theorem equation_10_76 {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∀ ν, 𝓕 (equation_10_77 f g) ν = 𝓕 f ν * 𝓕 g ν) ∧
      (Integrable (𝓕 g) → 𝓕 (fun t => f t * g t) = equation_10_77 (𝓕 f) (𝓕 g)) := by
  refine ⟨fun ν => ?_, fun hG => ?_⟩
  · rw [equation_10_77_eq_convolution]
    exact Real.fourier_mul_convolution_eq hf hg ν
  · rw [equation_10_77_eq_convolution]
    exact Real.fourier_mul_eq_convolution hf hg hG

/-! ### Examples 10.5–10.7 and the transfer function -/

/-- Let $a > 0$ and $\nu \neq 0$. The Fourier transform of the indicator function of $[-a, a]$ is
$$\int_{-a}^{a} e^{-2\pi i \nu t} \, dt = \frac{\sin(2\pi\nu a)}{\pi\nu}.$$
This is the computation behind Example 10.5. -/
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

/-- **Example 10.5** of [quarteroni2000numerical], the rectangular function. Let $A \in \mathbb{R}$,
$T > 0$, and let $r(t) = A$ for $|t| \le T/2$ and $r(t) = 0$ otherwise. Then
$$\mathcal{F} r(\nu) = AT \frac{\sin(\pi\nu T)}{\pi\nu T} \quad (\nu \neq 0), \qquad \mathcal{F}
  r(0) = AT.$$

**Generalization.** Allows any real amplitude and gives the removable sinc value at zero
explicitly. -/
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

/-- **Example 10.5** of [quarteroni2000numerical], the sawtooth function. Let $A \in \mathbb{R}$,
$T > 0$, and let $s(t) = 2At/T$ for $|t| \le T/2$ and $s(t) = 0$ otherwise. Then for
$\nu \neq 0$
$$\mathcal{F} s(\nu) = i \frac{AT}{\pi\nu T} \Bigl(\cos(\pi\nu T) - \frac{\sin(\pi\nu T)}{\pi\nu
  T}\Bigr),$$
which is purely imaginary and odd in $\nu$.

The proof uses the primitive $e^{-2\pi i\nu t}\bigl(it/(2\pi\nu) + 1/(4\pi^2\nu^2)\bigr)$ of
$t e^{-2\pi i\nu t}$ and the formulas of Euler.

**Reading.** Allows any real amplitude and states the printed fraction for nonzero frequency. -/
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

/-- **Example 10.6** of [quarteroni2000numerical], (10.78)–(10.79). Let $A, \nu_0 \in \mathbb{R}$.
As tempered distributions, the Fourier transform of the constant function $A$ is $A \delta_0$,
and the Fourier transform of $A \cos(2\pi\nu_0 t)$ is
$\frac{A}{2}(\delta_{\nu_0} + \delta_{-\nu_0})$. Here $\delta_a$ is the Dirac mass,
$\langle \delta_a, \varphi \rangle = \varphi(a)$.

The Dirac mass is Mathlib's `TemperedDistribution.delta`. For a Schwartz function $\varphi$ the
pairing is $\langle \mathcal{F} f, \varphi \rangle = \int f \, \mathcal{F}\varphi$, and $\int
e^{2\pi i\nu t} \mathcal{F}\varphi(t) \, dt = \mathcal{F}^{-1}(\mathcal{F}\varphi)(\nu) =
\varphi(\nu)$ by the inversion formula on the Schwartz space.

**Reading.** States the identities in the space of tempered distributions. The principal-value
limit and the action of a Dirac mass on a test function are not separately stated here. -/
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

/-- **Equation (10.80)** of [quarteroni2000numerical], the linear shift-invariant system. Let $S$ be
a bounded linear operator on $L^1(\mathbb{R})$ that commutes with every translation
$\tau_{t_0} u = u(\cdot - t_0)$, $t_0 \in \mathbb{R}$. Then for all $f, g \in L^1(\mathbb{R})$
$$S(f \star g) = f \star S(g)$$
almost everywhere.

**Correction.** The book's $S$ is a linear operator on unspecified admissible input functions
with $S(i(\cdot - t_0)) = u(\cdot - t_0)$ for every $t_0$, and the book calls
$S(f \star g) = f \star S(g)$ an immediate consequence of linearity and shift invariance. It is
not. The convolution $f \star g = \int f(\tau) \tau_\tau g \, d\tau$ is a continuous
superposition of translates, not a finite linear combination, and $S$ passes through this
integral only if $S$ is continuous. The book gives $S$ neither a domain nor a topology. Here $S$
acts on $L^1(\mathbb{R})$, the space of the inputs $f, g$ and of the convolution (10.77), and
boundedness is the continuity that the argument needs.

The translation is `MeasureTheory.Lp.translateₗᵢ`. The proof is the argument of the book, made
rigorous: $f \star g$ is the $L^1$-valued Bochner integral of the translates of $g$
(`MeasureTheory.Lp.integral_smul_translateₗᵢ_eq_toL1`), and $S$ passes through the integral and
through each translate (`MeasureTheory.Lp.coeFn_toL1_convolution_of_translateₗᵢ_comm`). -/
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

/-- **Equation (10.81)** of [quarteroni2000numerical], the transfer function. Let the output of a
system be the convolution $u = i \star h$ of the input $i \in L^1(\mathbb{R})$ with the impulse
response $h \in L^1(\mathbb{R})$. Then for every $\nu \in \mathbb{R}$
$$U(\nu) = I(\nu) H(\nu),$$
where $U$, $I$ and $H$ are the Fourier transforms of $u$, $i$ and $h$. The function $H$ is the
**transfer function**.

This is the first identity of (10.76).

**Reading.** Assumes the input and impulse response are integrable and uses their convolution
for the output. The theorem does not apply the system operator to a Dirac mass. -/
theorem equation_10_81 {i h : ℝ → ℂ} (hi : Integrable i) (hh : Integrable h) (ν : ℝ) :
    𝓕 (equation_10_77 i h) ν = 𝓕 i ν * 𝓕 h ν :=
  (equation_10_76 hi hh).1 ν

/-- **Example 10.7** of [quarteroni2000numerical], the ideal low-pass filter. Let $\nu_0 > 0$ and
let the transfer function $H$ be the indicator function of $[-\nu_0/2, \nu_0/2]$. Then the
impulse response $h = \mathcal{F}^{-1} H$ is
$$h(t) = \nu_0 \frac{\sin(\pi\nu_0 t)}{\pi\nu_0 t} \quad (t \neq 0), \qquad h(0) = \nu_0.$$

This is the rectangle of Example 10.5 with $A = 1$ and $T = \nu_0$, since
$\mathcal{F}^{-1} H(t) = \mathcal{F} H(-t)$. The second claim of the example, that the output
$u = i \star h$ has the spectrum $IH$, is not stated: it is (10.81) with $h \notin L^1$, which
needs the $L^2$ theory.

**Partial.** Computes the impulse response and includes its removable value at zero. The
output-spectrum assertion for this ideal filter is outside the theorem.

**Reading.** First claim only, with positive cutoff and removable value at zero.
-/
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

/-- **Equation (10.82)** of [quarteroni2000numerical], the sampling (aliasing) formula. Let the
input $i : \mathbb{R} \to \mathbb{C}$ be continuous and vanish outside a bounded interval, let
$\Delta t > 0$, and let $I = \mathcal{F} i$. Let $\nu \in \mathbb{R}$ be a frequency at which
the periodic repetition $\sum_{j \in \mathbb{Z}} I(\nu - j/\Delta t)$ converges absolutely. Then
$$\tilde I(\nu) = \Delta t \sum_{k \in \mathbb{Z}} i(k\Delta t) e^{-2\pi i\nu k\Delta t} =
  \sum_{j \in \mathbb{Z}} I(\nu - j/\Delta t).$$
So the trapezoidal approximation $\tilde I$ of $I$ is the periodic repetition of $I$ with period
$1/\Delta t$.

**Reading.** The book derives the formula through the sampled signal
$\sum_k i(k\Delta t) \delta(\cdot - k\Delta t)$, which is a distribution. For $i$ supported in
$[0, T_0]$ the left side is the finite sum $\Delta t \sum_{k=0}^{n-1} i(k\Delta t) e^{-2\pi i\nu
k\Delta t}$ of the book. The input of the book may jump at $0$ and $T_0$, where the sum sees the
average of the one-sided limits. For this reason the input is assumed continuous here.

The proof specializes `Real.tsum_fourierIntegral_sub_div_eq_tsum_mul`, which comes from
Mathlib's Poisson summation formula.

**Reading.** The frequency-side sum is assumed summable at the requested frequency. The samples
range over all integers. -/
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

/-- **Definition 10.2** of [quarteroni2000numerical]. Let $f : \mathbb{R} \to \mathbb{C}$ and
$s = \sigma + i\omega \in \mathbb{C}$. The **Laplace integral** of $f$ **exists** at $s$ if the
limit
$$\int_0^\infty f(t) e^{-st} \, dt = \lim_{T \to \infty} \int_0^T f(t) e^{-st} \, dt$$
exists.

The book takes $f \in L^1_{\mathrm{loc}}([0, \infty))$. The definition does not assume it. The
predicate is `LaplaceTransform.Converges f s` by
`QuarteroniSaccoSaleri.Chapter10.definition_10_2_iff`, and the transform is
`QuarteroniSaccoSaleri.Chapter10.laplace`.

**Generalization.** Uses total truncated integrals with no separate local integrability
premise. The transform is set to zero when their limit fails to exist. -/
def definition_10_2 (f : ℝ → ℂ) (s : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(s * t))) atTop (𝓝 L)

/-- **Definition 10.2** of [quarteroni2000numerical], the transform. For
$f : \mathbb{R} \to \mathbb{C}$ and $s \in \mathbb{C}$, the **Laplace transform** is
$L(s) = \int_0^\infty f(t) e^{-st} \, dt$, the limit of the truncated integrals
$\int_0^T f(t) e^{-st} \, dt$ as $T \to \infty$. Where this limit does not exist, the value is
$0$.

The definition is the backbone's `LaplaceTransform.laplaceTransform`.

**Generalization.** Uses total truncated integrals with no separate local integrability
premise. The transform is set to zero when their limit fails to exist. -/
noncomputable def laplace (f : ℝ → ℂ) (s : ℂ) : ℂ := LaplaceTransform.laplaceTransform f s

/-- For $f : \mathbb{R} \to \mathbb{C}$, $s \in \mathbb{C}$ and $T \in \mathbb{R}$, the truncated
integral $\int_0^T f(t) e^{-st} \, dt$ of Definition 10.2 is the backbone's
`LaplaceTransform.truncated f s T`. -/
theorem intervalIntegral_mul_exp_eq_truncated (f : ℝ → ℂ) (s : ℂ) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(s * t)) = LaplaceTransform.truncated f s T := by
  rw [LaplaceTransform.truncated_def]
  exact intervalIntegral.integral_congr fun t _ => by rw [smul_eq_mul, mul_comm]

/-- For $f : \mathbb{R} \to \mathbb{C}$ and $s \in \mathbb{C}$, the Laplace integral of $f$ exists
at $s$ in the sense of Definition 10.2 if and only if `LaplaceTransform.Converges f s` holds. -/
theorem definition_10_2_iff (f : ℝ → ℂ) (s : ℂ) :
    definition_10_2 f s ↔ LaplaceTransform.Converges f s := by
  simp only [definition_10_2, LaplaceTransform.Converges, intervalIntegral_mul_exp_eq_truncated]

/-- Let $f : \mathbb{R} \to \mathbb{C}$ and $s, L \in \mathbb{C}$. If
$\int_0^T f(t) e^{-st} \, dt \to L$ as $T \to \infty$, then the Laplace transform of $f$ at $s$
is $L$.

**Generalization.** Uses total truncated integrals with no separate local integrability
premise. The transform is set to zero when their limit fails to exist. -/
theorem laplace_eq_of_tendsto {f : ℝ → ℂ} {s L : ℂ}
    (h : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(s * t))) atTop (𝓝 L)) :
    laplace f s = L := by
  simp only [intervalIntegral_mul_exp_eq_truncated] at h
  exact LaplaceTransform.laplaceTransform_eq_of_tendsto h

/-- **Section 10.11.3** of [quarteroni2000numerical], the relation to the Fourier transform. Let
$f : \mathbb{R} \to \mathbb{C}$ and $s = \sigma + i\omega \in \mathbb{C}$, and let
$e^{-st} f(t)$ be integrable on $(0, \infty)$. Let $\tilde f(t) = f(t)$ for $t > 0$ and
$\tilde f(t) = 0$ for $t \le 0$. Then
$$L(\sigma + i\omega) = \mathcal{F}\bigl(e^{-\sigma t} \tilde
  f\bigr)\Bigl(\frac{\omega}{2\pi}\Bigr).$$

**Reading.** The book writes $L(s) = \mathcal{F}(e^{-\sigma t} \tilde f)$ without the argument.
The argument is $\omega/2\pi$, because Definition 10.1 uses $e^{-2\pi i\nu t}$.

The proof specializes `LaplaceTransform.laplaceTransform_eq_fourier`.

**Reading.** The ordinary Fourier integral requires absolute integrability of the exponentially
weighted input. -/
theorem definition_10_2_fourier {f : ℝ → ℂ} {s : ℂ}
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * f t) (Ioi 0)) :
    laplace f s = definition_10_1 (fun t => Complex.exp (-(s.re * t)) * Set.indicator (Ioi 0) f t)
      (s.im / (2 * π)) := by
  rw [definition_10_1_eq_fourierIntegral, laplace]
  exact LaplaceTransform.laplaceTransform_eq_fourier h

/-- **Example 10.8** of [quarteroni2000numerical]. Let $f$ be the unit step, $f(t) = 1$ for $t > 0$
and $f(t) = 0$ otherwise, and let $s \in \mathbb{C}$. If $\operatorname{Re} s > 0$, then
$$L(s) = \int_0^\infty e^{-st} \, dt = \frac{1}{s}.$$
The Laplace integral of $f$ exists at $s$ if and only if $\operatorname{Re} s > 0$. -/
theorem example_10_8 (s : ℂ) :
    (0 < s.re → laplace (fun t : ℝ => Set.indicator (Ioi 0) (fun _ => (1 : ℂ)) t) s = 1 / s) ∧
      (definition_10_2 (fun t : ℝ => Set.indicator (Ioi 0) (fun _ => (1 : ℂ)) t) s ↔ 0 < s.re) :=
  ⟨fun hs => LaplaceTransform.laplaceTransform_indicator_Ioi hs,
    (definition_10_2_iff _ _).trans LaplaceTransform.converges_indicator_Ioi_iff⟩

/-- **Property 10.4** of [quarteroni2000numerical]. Let $f : \mathbb{R} \to \mathbb{C}$ be locally
integrable on $[0, \infty)$. Then:
* if the Laplace integral of $f$ exists at $\bar s$, then it exists at every $s$ with
  $\operatorname{Re} s > \operatorname{Re} \bar s$;
* let $\lambda \in [-\infty, \infty]$ be the infimum of the real parts of the points where the
  Laplace integral exists (the abscissa of convergence); then the Laplace integral exists at
  every $s$ with $\operatorname{Re} s > \lambda$;
* if $\lambda = -\infty$, then the Laplace integral exists at every $s \in \mathbb{C}$.

The abscissa of convergence is `LaplaceTransform.abscissaOfConvergence f`, an extended real
number. It is $+\infty$ when the integral exists nowhere. -/
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

/-- **Example 10.9** of [quarteroni2000numerical], (10.83). Let $a, s \in \mathbb{C}$, and let
$y : \mathbb{R} \to \mathbb{C}$ be of class $C^1$ with $y'(t) + a y(t) = g(t)$ for all $t$. Let
$e^{-st} y(t)$ and $e^{-st} y'(t)$ be integrable on $(0, \infty)$, and let $e^{-st} y(t) \to 0$
as $t \to \infty$. Then the Laplace transforms $Y$ of $y$ and $G$ of $g$ satisfy
$$s Y(s) - y(0) + a Y(s) = G(s).$$

The proof uses the transform of a derivative (`LaplaceTransform.laplaceTransform_deriv`) and the
linearity of the transform. The integrability of $e^{-st} g(t)$ is not a hypothesis, because it
follows from the equation.

**Reading.** Uses the factor $e^{-st}$, which gives the printed identity, while the preceding
sentence prints $e^{st}$. Integrability of the weighted function and its derivative and
vanishing of the endpoint term are explicit. -/
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

/-- **Example 10.9** of [quarteroni2000numerical], the solution. Let $a, y_0 \in \mathbb{C}$ with
$a \neq 0$. The function
$$y(t) = \frac{1}{a}(1 - e^{-at}) + y_0 e^{-at}$$
satisfies $y'(t) = 1 - a y(t)$ for every $t \in \mathbb{R}$, and $y(0) = y_0$.

So $y$ solves $y' + ay = g$ for the unit-step forcing $g = 1$. The book obtains $y$ by inverting
$Y(s) = \frac{1}{a}\bigl(\frac{1}{s} - \frac{1}{s + a}\bigr) + \frac{y_0}{s + a}$. The proof
differentiates $y$ directly.

**Reading.** Verifies the formula by differentiating it for $a\neq 0$ and evaluating the
initial value, without using an inverse Laplace operator. -/
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

/-- **Definition 10.3** of [quarteroni2000numerical], (10.84). Let $f : \mathbb{R} \to \mathbb{C}$
and let $\Delta t$ be a time step. The **Z-transform** of the samples $f(n\Delta t)$ is
$$Z(z) = \sum_{n=0}^{\infty} f(n\Delta t) z^{-n}, \qquad z \in \mathbb{C}.$$

The sum is Mathlib's `tsum`, which is $0$ when the series does not converge absolutely. The
definition is the backbone's `zTransform` by
`QuarteroniSaccoSaleri.Chapter10.definition_10_3_eq_zTransform`.

**Generalization.** The sample step is any real number. The series is total, and the root-test
bound uses an extended nonnegative radius. -/
noncomputable def definition_10_3 (f : ℝ → ℂ) (Δt : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, f (n * Δt) * z⁻¹ ^ n

/-- For $f : \mathbb{R} \to \mathbb{C}$, $\Delta t \in \mathbb{R}$ and $z \in \mathbb{C}$, the
Z-transform of Definition 10.3 is the backbone's `zTransform f Δt z`. -/
theorem definition_10_3_eq_zTransform (f : ℝ → ℂ) (Δt : ℝ) (z : ℂ) :
    definition_10_3 f Δt z = zTransform f Δt z := rfl

/-- **Definition 10.3** of [quarteroni2000numerical], the convergence of (10.84). Let
$f : \mathbb{R} \to \mathbb{C}$, $\Delta t \in \mathbb{R}$ and $z \in \mathbb{C}$. If
$$R = \limsup_{n \to \infty} |f(n\Delta t)|^{1/n} < |z|,$$
then the series $\sum_{n \ge 0} f(n\Delta t) z^{-n}$ converges absolutely.

**Reading.** The radius $R$ is read in $[0, \infty]$. In Lean the upper limit is taken in
`ENNReal`, through the extended norm `‖·‖ₑ`.

The proof is the Cauchy–Hadamard root test `summable_zTransform`.

**Generalization.** The sample step is any real number. The series is total, and the root-test
bound uses an extended nonnegative radius. -/
theorem definition_10_3_summable {f : ℝ → ℂ} {Δt : ℝ} {z : ℂ}
    (hz : Filter.limsup (fun n : ℕ => ‖f (n * Δt)‖ₑ ^ (1 / (n : ℝ))) atTop < ‖z‖ₑ) :
    Summable fun n : ℕ => f (n * Δt) * z⁻¹ ^ n :=
  summable_zTransform hz

/-- **Section 10.11.4** of [quarteroni2000numerical], the Z-transform as a discrete Laplace
transform. Let $f : \mathbb{R} \to \mathbb{C}$, $\Delta t > 0$, and $s \in \mathbb{C}$ with
$\operatorname{Re} s > 0$, and let $\sum_n |f(n\Delta t)| e^{-n \operatorname{Re} s \, \Delta t}
< \infty$. Let $f_0(t) = f(\lfloor t/\Delta t \rfloor \Delta t)$, the step function equal to
$f(n\Delta t)$ on $[n\Delta t, (n+1)\Delta t)$. Then the discrete Laplace transform is the
Z-transform at $z = e^{s\Delta t}$,
$$Z(e^{s\Delta t}) = \sum_{n=0}^{\infty} f(n\Delta t) e^{-ns\Delta t},$$
and the Laplace transform of $f_0$ is
$$L(s) = \frac{1 - e^{-s\Delta t}}{s} \, Z(e^{s\Delta t}).$$

**Typo.** The book prints the substitution as $z = e^{-s\Delta t}$.

The proof specializes `LaplaceTransform.laplaceTransform_stepFun` and
`zTransform_eq_discreteLaplace`.

**Reading.** Assumes absolute summability of the weighted samples and $\operatorname{Re}s>0$ to
identify the transform of the piecewise constant function. -/
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
