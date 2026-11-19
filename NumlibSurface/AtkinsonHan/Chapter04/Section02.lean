/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Atkinson and Han, Section 4.2: The Fourier transform

This module formalizes Section 4.2 of [han2009theoretical], the Fourier transform on $\mathbb{R}^d$.
The book's transform (4.2.3) is
$$\hat f(\xi) = (\mathcal{F} f)(\xi) = (2\pi)^{-d/2} \int_{\mathbb{R}^d} f(x)\, e^{-i x \cdot \xi}
  \, dx,$$
and its inverse (4.2.4) has the factor $e^{i x \cdot \xi}$ instead. Mathlib's transform
`FourierTransform.fourier` uses the character $e^{-2\pi i x \cdot \xi}$ and no prefactor, so the two
are related by $\hat f(\xi) = (2\pi)^{-d/2} (\mathcal{F}_{\mathrm{Mathlib}} f)((2\pi)^{-1} \xi)$.
This one identity carries the Mathlib results to the book's normalization: linearity (4.2.5), the
bound (4.2.6), the differentiation and multiplication rules (4.2.7) and (4.2.8), the multiplication
formula (4.2.10), the inversion formula (4.2.11), the transform on the Schwartz space and on
tempered distributions (Definitions 4.2.1–4.2.3), and Plancherel's theorem (Theorem 4.2.4) on the
Schwartz space and on $L^2(\mathbb{R}^d)$.

The Schwartz space, the tempered distributions and the Fourier transform on them are Mathlib's
`SchwartzMap`, `TemperedDistribution` and their Fourier transforms. Definitions 4.2.1–4.2.3 are
therefore stated as identifications with these objects, not as new definitions.

## Main definitions

* Equations (4.2.1) and (4.2.3), `AtkinsonHan.Chapter04.bookConst` and `bookFourier`: the
  constant $(2\pi)^{-d/2}$ and the book's Fourier transform $\hat f$.
* Equation (4.2.4), `AtkinsonHan.Chapter04.bookFourierInv`: the book's inverse Fourier transform.
* Definition 4.2.1 and equation (4.2.9), `AtkinsonHan.Chapter04.bookFourierCLM`: the book's
  transform as a continuous linear map of the Schwartz space $\mathcal{S}(\mathbb{R}^d)$ into
  itself.
* Definition 4.2.2, `AtkinsonHan.Chapter04.definition_4_2_2` and
  `AtkinsonHan.Chapter04.definition_4_2_2_seq`: a linear functional on $\mathcal{S}(\mathbb{R}^d)$
  is a tempered distribution if and only if it is continuous, and if and only if it is sequentially
  continuous.
* Definition 4.2.3, `AtkinsonHan.Chapter04.bookFourierTD`: the Fourier transform of a tempered
  distribution, defined by duality.
* Theorem 4.2.4, `AtkinsonHan.Chapter04.bookFourierSchwartzEquiv` and
  `AtkinsonHan.Chapter04.bookFourierL2`: the book's transform as a linear bijection of
  $\mathcal{S}(\mathbb{R}^d)$, and its extension to a linear isometry of $L^2(\mathbb{R}^d)$ onto
  itself.

## Main results

* Equation (4.2.5), `AtkinsonHan.Chapter04.equation_4_2_5`: the transform is linear on integrable
  functions.
* Equation (4.2.6), `AtkinsonHan.Chapter04.equation_4_2_6` and
  `AtkinsonHan.Chapter04.continuous_bookFourier`: $|\hat f(\xi)| \le (2\pi)^{-d/2} \|f\|_{L^1}$, and
  $\hat f$ is continuous for $f \in L^1$.
* Equation (4.2.7), `AtkinsonHan.Chapter04.equation_4_2_7` and
  `AtkinsonHan.Chapter04.equation_4_2_7_dim_one`: the transform of a directional derivative
  $\partial_v f$ is $i (v \cdot \xi) \hat f(\xi)$, and in one dimension
  $\widehat{f'}(\xi) = i \xi \hat f(\xi)$.
* Equation (4.2.8), `AtkinsonHan.Chapter04.equation_4_2_8`: in one dimension, the transform of
  $x f(x)$ is $i \hat f'(\xi)$.
* Equation (4.2.10), `AtkinsonHan.Chapter04.equation_4_2_10`: $\int \hat f g = \int f \hat g$ for
  integrable $f$ and $g$.
* Equations (4.2.4) and (4.2.11), `AtkinsonHan.Chapter04.equation_4_2_11`: the inversion formula
  $\mathcal{F}^{-1} \hat f = f$ for continuous integrable $f$ with integrable $\hat f$.
* Definition 4.2.1, `AtkinsonHan.Chapter04.definition_4_2_1`: the continuous linear map on
  $\mathcal{S}(\mathbb{R}^d)$ is the book's transform.
* Equation (4.2.12), `AtkinsonHan.Chapter04.equation_4_2_12`: an $L^p$ function is a tempered
  distribution through $\langle f, \varphi \rangle = \int f \varphi$, and for $f \in L^1$ its
  distributional transform is the function $\hat f$.
* Definition 4.2.3 and equation (4.2.13), `AtkinsonHan.Chapter04.definition_4_2_3`: $\langle \hat u,
  \varphi \rangle = \langle u, \hat \varphi \rangle$.
* Theorem 4.2.4 (Plancherel's theorem), `AtkinsonHan.Chapter04.theorem_4_2_4` and
  `AtkinsonHan.Chapter04.theorem_4_2_4_l2`: the transform preserves the $L^2$ norm of a Schwartz
  function, and its extension to $L^2(\mathbb{R}^d)$ is an isometry onto $L^2(\mathbb{R}^d)$.
* `AtkinsonHan.Chapter04.bookFourier_eq_fourier`,
  `AtkinsonHan.Chapter04.bookFourier_eq_vectorFourier` and
  `AtkinsonHan.Chapter04.bookFourierInv_eq_fourierInv`: the relations between the book's transforms
  and Mathlib's.

## Conventions

* The book's $\mathbb{R}^d$ is a finite-dimensional real inner product space $V$, with
  $d = \dim_{\mathbb{R}} V$ (`Module.finrank ℝ V`) and $x \cdot \xi$ the inner product. For
  $V = \mathbb{R}^d$ this is the book's statement. At $V = \mathbb{R}$ the one-dimensional rules can
  be read off directly from Mathlib.
* Functions are complex valued: $f : V \to \mathbb{C}$, and the Schwartz space is `𝓢(V, ℂ)`.

## Implementation notes

* The prefactor $(2\pi)^{-d/2}$ is the definition `AtkinsonHan.Chapter04.bookConst`, not an inlined
  expression. The inversion formula and Plancherel's theorem both need the identity
  $(2\pi)^{-d/2} \cdot (2\pi)^{-d/2} (2\pi)^d = 1$, which cancels the Jacobian $(2\pi)^d$ of the
  change of variables $\xi = 2\pi u$.
* The transform `AtkinsonHan.Chapter04.bookFourier` is a Bochner integral, so it is $0$ at every
  $\xi$ where the integrand is not integrable.

## Deviations from the source

* **Equations (4.2.3)–(4.2.6)** (reading). The integral transforms are total on functions.
  The norm estimate is given pointwise, and the declared inversion theorem assumes continuity
  to obtain a pointwise equality.
* **Equations (4.2.7)–(4.2.8)** (reading). The declarations give first-order derivative
  and moment rules under integrability assumptions, with (4.2.8) stated in one dimension.
* **(4.2.10) and Definition 4.2.2** (generalization). The bilinear formula needs only
  integrability, and the tempered-distribution characterizations apply beyond Euclidean spaces.
* **Theorem 4.2.4** (reading). The isometric equivalence is extended from the Schwartz space
  by density. Agreement with the integral transform is proved on Schwartz functions.

## Not formalized

* Equation (4.2.7) for a multi-index $\alpha$ with $|\alpha| \ge 2$, $\widehat{\partial^\alpha
  f}(\xi) = (i\xi)^\alpha \hat f(\xi)$. It is the first-order rule iterated $|\alpha|$ times.
* Equation (4.2.8) in dimension $d \ge 2$.
* The explicit $L^2$ limits of truncated integrals (4.2.14)–(4.2.15) and agreement with the
  integral transform on all of $L^1 \cap L^2$ in (4.2.16)–(4.2.17).
-/

namespace AtkinsonHan.Chapter04

open MeasureTheory Module Real VectorFourier

open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The constant $(2\pi)^{-d/2}$ of (4.2.1) in dimension $d = \dim_{\mathbb{R}} V$, defined as
$(2\pi)^{-d/2}$ with a real exponent.

It is the constant that makes the Fourier transform an isometry of $L^2$ (Theorem 4.2.4 of
[han2009theoretical]). It appears in the book's transform `AtkinsonHan.Chapter04.bookFourier`
and in its inverse `AtkinsonHan.Chapter04.bookFourierInv`. -/
noncomputable def bookConst (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (2 * π) ^ (-(finrank ℝ V : ℝ) / 2)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The constant $(2\pi)^{-d/2}$ is positive. -/
theorem bookConst_pos : 0 < bookConst V := by
  rw [bookConst]
  positivity

/-- **Equations (4.2.1) and (4.2.3)** of [han2009theoretical]. Let $V$ be a real inner product space
of finite dimension $d$. The **Fourier transform** of $f : V \to \mathbb{C}$ is the function
$$\hat f(\xi) = (2\pi)^{-d/2} \int_V e^{-i x \cdot \xi} f(x) \, dx, \qquad \xi \in V.$$

The integral is the Bochner integral for the volume measure on $V$. It is $0$ when the integrand
is not integrable, so $\hat f(\xi) = 0$ for every $\xi$ if $f$ is not integrable.

**Reading.** The source defines the integral transform on $L^1$. The Bochner integral
extends the formula to all functions by returning zero when the integrand is not integrable. -/
noncomputable def bookFourier (f : V → ℂ) (ξ : V) : ℂ :=
  (bookConst V : ℝ) • ∫ x : V, Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * f x

/-- The book's transform is Mathlib's Fourier integral `VectorFourier.fourierIntegral` for the
character $t \mapsto e^{it}$ (`Real.probChar`) and the pairing given by the inner product,
multiplied by $(2\pi)^{-d/2}$: for every $f : V \to \mathbb{C}$ and $\xi \in V$,
$$\hat f(\xi) = (2\pi)^{-d/2} \int_V e^{-i x \cdot \xi} f(x) \, dx$$
with the integral written as `VectorFourier.fourierIntegral Real.probChar volume (innerₗ V) f
ξ`. -/
theorem bookFourier_eq_vectorFourier (f : V → ℂ) (ξ : V) :
    bookFourier f ξ =
      (bookConst V : ℝ) • fourierIntegral Real.probChar volume (innerₗ V) f ξ := by
  rw [bookFourier, fourierIntegral_probChar]
  simp [smul_eq_mul]

/-- The relation between the book's Fourier transform and Mathlib's transform $\mathcal{F}$, which
uses the character $e^{-2\pi i x \cdot \xi}$ and no prefactor. For every $f : V \to \mathbb{C}$
and $\xi \in V$,
$$\hat f(\xi) = (2\pi)^{-d/2} \, (\mathcal{F} f)\bigl((2\pi)^{-1} \xi\bigr).$$

There is no hypothesis on $f$: when $f$ is not integrable, both sides are $0$. The results of
this module on inversion and on $L^2$ are proved through this identity. -/
theorem bookFourier_eq_fourier (f : V → ℂ) (ξ : V) :
    bookFourier f ξ = (bookConst V : ℝ) • 𝓕 f ((2 * π)⁻¹ • ξ) := by
  rw [bookFourier, Real.fourier_eq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Circle.smul_def, Real.fourierChar_apply, real_inner_smul_right]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 2
  push_cast
  field_simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem continuous_innerₗ : Continuous fun p : V × V => innerₗ V p.1 p.2 := by
  simp only [innerₗ_apply_apply]
  exact continuous_inner

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem norm_exp_neg_inner_mul_I (x ξ : V) :
    ‖Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  simp [Complex.norm_exp]

private theorem integrable_exp_mul {f : V → ℂ} (hf : Integrable f) (ξ : V) :
    Integrable fun x : V => Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * f x :=
  Integrable.bdd_mul (c := 1) hf (by fun_prop)
    (Filter.Eventually.of_forall fun x => (norm_exp_neg_inner_mul_I x ξ).le)

/-- **Equation (4.2.5)** of [han2009theoretical]. Let $f, g : V \to \mathbb{C}$ be integrable, and
let $a, b \in \mathbb{C}$. Then the Fourier transform is linear:
$$\widehat{(af + bg)}(\xi) = a \hat f(\xi) + b \hat g(\xi) \qquad \text{for all } \xi \in V.$$
-/
theorem equation_4_2_5 {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) (a b : ℂ) (ξ : V) :
    bookFourier (fun x => a * f x + b * g x) ξ
      = a * bookFourier f ξ + b * bookFourier g ξ := by
  simp only [bookFourier, Complex.real_smul]
  rw [show (fun x : V => Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * (a * f x + b * g x))
      = fun x : V => a * (Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * f x)
        + b * (Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * g x) from funext fun x => by ring,
    integral_add ((integrable_exp_mul hf ξ).const_mul a)
      ((integrable_exp_mul hg ξ).const_mul b),
    integral_const_mul, integral_const_mul]
  ring

/-- **Equation (4.2.6)** of [han2009theoretical], the bound. For every function
$f : V \to \mathbb{C}$ and every $\xi \in V$,
$$|\hat f(\xi)| \le (2\pi)^{-d/2} \int_V |f(x)| \, dx.$$
Thus the transform maps $L^1(\mathbb{R}^d)$ into $L^\infty(\mathbb{R}^d)$, with $\|\hat
f\|_\infty \le (2\pi)^{-d/2} \|f\|_{L^1}$.

The statement has no integrability hypothesis. If $f$ is not integrable, then $\hat f(\xi) = 0$
and the bound is trivial.

**Reading.** The source gives an $L^\infty$ norm bound for integrable data. Here the bound
is pointwise, also allowing nonintegrable inputs via the total Bochner integral. -/
theorem equation_4_2_6 (f : V → ℂ) (ξ : V) :
    ‖bookFourier f ξ‖ ≤ bookConst V * ∫ x : V, ‖f x‖ := by
  rw [bookFourier_eq_vectorFourier, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg bookConst_pos.le]
  exact mul_le_mul_of_nonneg_left
    (norm_fourierIntegral_le_integral_norm _ _ _ _ _) bookConst_pos.le

/-- **Equation (4.2.6)** of [han2009theoretical], continuity. If $f : V \to \mathbb{C}$ is
integrable, then $\hat f$ is continuous on $V$. -/
theorem continuous_bookFourier {f : V → ℂ} (hf : Integrable f) : Continuous (bookFourier f) := by
  simp only [funext fun ξ => bookFourier_eq_vectorFourier f ξ]
  exact (fourierIntegral_continuous Real.continuous_probChar continuous_innerₗ
    hf).const_smul (bookConst V)

/-- **Equation (4.2.10)** of [han2009theoretical] (the multiplication formula). Let
$f, g : V \to \mathbb{C}$ be integrable. Then
$$\int_V \hat f(\xi) \, g(\xi) \, d\xi = \int_V f(x) \, \hat g(x) \, dx.$$

The proof is Fubini's theorem for $f(x) g(\xi) e^{-i x \cdot \xi}$. The formula shows that
Definition 4.2.3 agrees with (4.2.3) on $L^1$; see `AtkinsonHan.Chapter04.equation_4_2_12`.

**Generalization.** The book states the identity for Schwartz functions. It also holds
for all integrable $f$ and $g$. -/
theorem equation_4_2_10 {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ : V, bookFourier f ξ * g ξ = ∫ x : V, f x * bookFourier g x := by
  have key := integral_fourierIntegral_smul_eq_flip Real.continuous_probChar
    continuous_innerₗ hf hg
  simp only [smul_eq_mul, flip_innerₗ] at key
  simp only [bookFourier_eq_vectorFourier, Complex.real_smul]
  have e1 : ∫ ξ : V, (bookConst V : ℂ) * fourierIntegral Real.probChar volume (innerₗ V) f ξ * g ξ
      = (bookConst V : ℂ) *
        ∫ ξ : V, fourierIntegral Real.probChar volume (innerₗ V) f ξ * g ξ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)
  have e2 : ∫ x : V, f x * ((bookConst V : ℂ) * fourierIntegral Real.probChar volume (innerₗ V) g x)
      = (bookConst V : ℂ) *
        ∫ x : V, f x * fourierIntegral Real.probChar volume (innerₗ V) g x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [e1, e2, key]

/-- **Equation (4.2.4)** of [han2009theoretical]. The **inverse Fourier transform** of
$f : V \to \mathbb{C}$ is the function
$$(\mathcal{F}^{-1} f)(x) = (2\pi)^{-d/2} \int_V e^{i x \cdot \xi} f(\xi) \, d\xi, \qquad x \in
  V.$$

As for `AtkinsonHan.Chapter04.bookFourier`, the integral is $0$ when the integrand is not
integrable.

**Reading.** This is the integral expression of the inverse. It is defined for all functions
by the total Bochner integral; inversion for continuous integrable data with integrable
transform is stated separately. -/
noncomputable def bookFourierInv (f : V → ℂ) (x : V) : ℂ :=
  (bookConst V : ℝ) • ∫ ξ : V, Complex.exp (((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * f ξ

/-- The relation between the book's inverse transform and Mathlib's inverse transform
$\mathcal{F}^{-1}$: for every $f : V \to \mathbb{C}$ and $x \in V$,
$$(\mathcal{F}^{-1}_{\mathrm{book}} f)(x) = (2\pi)^{-d/2} \, (\mathcal{F}^{-1}
  f)\bigl((2\pi)^{-1} x\bigr).$$
This is the counterpart of `AtkinsonHan.Chapter04.bookFourier_eq_fourier`. -/
theorem bookFourierInv_eq_fourierInv (f : V → ℂ) (x : V) :
    bookFourierInv f x = (bookConst V : ℝ) • 𝓕⁻ f ((2 * π)⁻¹ • x) := by
  rw [bookFourierInv, Real.fourierInv_eq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [Circle.smul_def, Real.fourierChar_apply, real_inner_smul_right, real_inner_comm x ξ]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 2
  push_cast
  field_simp

omit [MeasurableSpace V] [BorelSpace V] in
/-- The identity $(2\pi)^{-d/2} \cdot \bigl((2\pi)^{-d/2} (2\pi)^d\bigr) = 1$, which cancels the
Jacobian of the change of variables $\xi = 2\pi u$. -/
private theorem bookConst_sq_mul_pow :
    bookConst V * (bookConst V * (2 * π) ^ finrank ℝ V) = 1 := by
  rw [bookConst, ← Real.rpow_natCast (2 * π) (finrank ℝ V), ← mul_assoc,
    ← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity),
    show -(finrank ℝ V : ℝ) / 2 + -(finrank ℝ V : ℝ) / 2 + (finrank ℝ V : ℝ) = 0 by ring,
    Real.rpow_zero]

/-- Mathlib's inverse transform of $\hat f$ at $w$ is $(2\pi)^{-d/2} (2\pi)^d$ times Mathlib's
inverse transform of $\mathcal{F} f$ at $2\pi w$. -/
private theorem fourierInv_bookFourier (f : V → ℂ) (w : V) :
    𝓕⁻ (bookFourier f) w
      = ((bookConst V * (2 * π) ^ finrank ℝ V : ℝ) : ℂ) * 𝓕⁻ (𝓕 f) ((2 * π) • w) := by
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have e1 : 𝓕⁻ (bookFourier f) w
      = ((bookConst V : ℝ) : ℂ) * ∫ v : V, (𝐞 ⟪v, w⟫ : ℂ) * 𝓕 f ((2 * π)⁻¹ • v) := by
    rw [Real.fourierInv_eq, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [bookFourier_eq_fourier, Circle.smul_def, Complex.real_smul]
    ring
  have e2 : ∫ u : V, (𝐞 ⟪(2 * π) • u, w⟫ : ℂ) * 𝓕 f ((2 * π)⁻¹ • (2 * π) • u)
      = 𝓕⁻ (𝓕 f) ((2 * π) • w) := by
    rw [Real.fourierInv_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [smul_smul, inv_mul_cancel₀ hπ, one_smul, real_inner_smul_left, ← real_inner_smul_right]
    exact (Circle.smul_def _ _).symm
  have hcv := Measure.integral_comp_smul (volume : Measure V)
    (fun v : V => (𝐞 ⟪v, w⟫ : ℂ) * 𝓕 f ((2 * π)⁻¹ • v)) (2 * π)
  rw [abs_of_pos (by positivity : (0 : ℝ) < ((2 * π) ^ finrank ℝ V)⁻¹)] at hcv
  have e3 : ∫ v : V, (𝐞 ⟪v, w⟫ : ℂ) * 𝓕 f ((2 * π)⁻¹ • v)
      = ((2 * π) ^ finrank ℝ V : ℝ) • 𝓕⁻ (𝓕 f) ((2 * π) • w) := by
    rw [← e2, hcv, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  rw [e1, e3, Complex.real_smul]
  push_cast
  ring

/-- **Equations (4.2.4) and (4.2.11)** of [han2009theoretical] (the inversion formula). Let
$f : V \to \mathbb{C}$ be continuous and integrable, and let $\hat f$ be integrable. Then
$\mathcal{F}^{-1} \hat f = f$, that is,
$$f(x) = (2\pi)^{-d/2} \int_V e^{i x \cdot \xi} \hat f(\xi) \, d\xi \qquad \text{for all } x \in
  V.$$

The proof specializes Mathlib's inversion theorem for $\mathcal{F}$ through
`AtkinsonHan.Chapter04.bookFourier_eq_fourier` and
`AtkinsonHan.Chapter04.bookFourierInv_eq_fourierInv`.

**Reading.** The book states almost-everywhere inversion for integrable data and transform
in (4.2.4), and pointwise inversion for Schwartz data in (4.2.11). This theorem gives
pointwise inversion under continuity and integrability of $f$ and integrability of $\hat f$. -/
theorem equation_4_2_11 {f : V → ℂ} (hf : Continuous f) (hfi : Integrable f)
    (hFi : Integrable (bookFourier f)) : bookFourierInv (bookFourier f) = f := by
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have hFourier : Integrable (𝓕 f) := by
    have hc : ((bookConst V : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr bookConst_pos.ne'
    have h1 : Integrable fun ξ : V => 𝓕 f ((2 * π)⁻¹ • ξ) := by
      refine (Integrable.const_mul hFi ((bookConst V : ℂ)⁻¹)).congr
        (Filter.Eventually.of_forall fun ξ => ?_)
      dsimp only
      rw [bookFourier_eq_fourier, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    exact (integrable_comp_smul_iff volume (𝓕 f) (by positivity)).mp h1
  have hconst := bookConst_sq_mul_pow (V := V)
  funext x
  rw [bookFourierInv_eq_fourierInv, fourierInv_bookFourier, smul_smul, mul_inv_cancel₀ hπ,
    one_smul, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hconst, Complex.ofReal_one,
    one_mul, hf.fourierInv_fourier_eq hfi hFourier]

/-- **Theorem 4.2.4** of [han2009theoretical] (Plancherel's theorem), on the Schwartz space. For
every Schwartz function $f \in \mathcal{S}(V)$ with values in $\mathbb{C}$,
$$\int_V |\hat f(\xi)|^2 \, d\xi = \int_V |f(x)|^2 \, dx.$$
This is (4.2.18) for Schwartz functions: the normalization $(2\pi)^{-d/2}$ is the one for which
the transform preserves the $L^2$ norm.

The extension of the transform to all of $L^2(\mathbb{R}^d)$, which is (4.2.14)–(4.2.17), is
`AtkinsonHan.Chapter04.bookFourierL2`, and the full theorem on $L^2(\mathbb{R}^d)$ is
`AtkinsonHan.Chapter04.theorem_4_2_4_l2`. -/
theorem theorem_4_2_4 (f : 𝓢(V, ℂ)) :
    ∫ ξ : V, ‖bookFourier f ξ‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2 := by
  have hπ : ((2 * π)⁻¹ : ℝ) ≠ 0 := by positivity
  have e1 : ∀ ξ : V, ‖bookFourier (⇑f) ξ‖ ^ 2
      = bookConst V ^ 2 * ‖𝓕 (⇑f) ((2 * π)⁻¹ • ξ)‖ ^ 2 := fun ξ => by
    rw [bookFourier_eq_fourier, norm_smul, Real.norm_eq_abs, abs_of_pos bookConst_pos, mul_pow]
  have hcv := Measure.integral_comp_smul (volume : Measure V)
    (fun ξ : V => ‖𝓕 (⇑f) ξ‖ ^ 2) ((2 * π)⁻¹)
  rw [inv_pow, inv_inv, abs_of_pos (by positivity)] at hcv
  have h1 : bookConst V ^ 2 * (2 * π) ^ finrank ℝ V = 1 := by
    rw [← bookConst_sq_mul_pow (V := V)]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e1), integral_const_mul, hcv, smul_eq_mul,
    ← mul_assoc, h1, one_mul, ← SchwartzMap.fourier_coe f, SchwartzMap.integral_norm_sq_fourier]

/-- **Equation (4.2.7)** of [han2009theoretical], first order. Let $f : V \to \mathbb{C}$ be
integrable and differentiable, with integrable derivative
$Df : V \to \mathcal{L}(V, \mathbb{C})$. Then for every direction $v \in V$ the transform of the
directional derivative $\partial_v f(x) = Df(x) v$ is
$$\widehat{\partial_v f}(\xi) = i \, (v \cdot \xi) \, \hat f(\xi) \qquad \text{for all } \xi \in
  V.$$

The book states the rule for a multi-index $\alpha$: $\widehat{\partial^\alpha f}(\xi) =
(i\xi)^\alpha \hat f(\xi)$. The general case is this first-order rule iterated $|\alpha|$ times,
and it is not stated here. The derivative is the Fréchet derivative `fderiv ℝ f`.

**Reading.** The book states a multi-index identity for Schwartz data. This first-order
version allows any direction and differentiable integrable data with integrable derivative. -/
theorem equation_4_2_7 {f : V → ℂ} (hf : Integrable f) (hf' : Differentiable ℝ f)
    (hfd : Integrable (fderiv ℝ f)) (v ξ : V) :
    bookFourier (fun x => fderiv ℝ f x v) ξ
      = Complex.I * ((⟪v, ξ⟫ : ℝ) : ℂ) * bookFourier f ξ := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : 𝓕 (fun x : V => fderiv ℝ f x v) ((2 * π)⁻¹ • ξ)
      = ((2 : ℂ) * π * Complex.I) * ((⟪(2 * π)⁻¹ • ξ, v⟫ : ℝ) : ℂ)
        * 𝓕 f ((2 * π)⁻¹ • ξ) := by
    rw [← Real.fourier_continuousLinearMap_apply hfd, Real.fourier_fderiv hf hf' hfd]
    simp only [fourierSMulRight_apply, neg_apply, innerSL_apply_apply ℝ, Complex.real_smul,
      smul_eq_mul, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]
    ring
  rw [bookFourier_eq_fourier, bookFourier_eq_fourier, key, real_inner_smul_left,
    real_inner_comm ξ v, Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp

/-- **Equation (4.2.7)** of [han2009theoretical], in one dimension. Let
$f : \mathbb{R} \to \mathbb{C}$ be integrable and differentiable, with integrable derivative
$f'$. Then
$$\widehat{f'}(\xi) = i \xi \hat f(\xi) \qquad \text{for all } \xi \in \mathbb{R}.$$

At $V = \mathbb{R}$ the book's rule and Mathlib's `Real.fourier_deriv` differ only by the
scaling of the argument.

**Reading.** This is the one-dimensional first-derivative specialization, with integrability
assumptions in place of the Schwartz hypothesis. -/
theorem equation_4_2_7_dim_one {f : ℝ → ℂ} (hf : Integrable f) (hf' : Differentiable ℝ f)
    (hfd : Integrable (deriv f)) (ξ : ℝ) :
    bookFourier (deriv f) ξ = Complex.I * ξ * bookFourier f ξ := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [bookFourier_eq_fourier, bookFourier_eq_fourier]
  simp only [Real.fourier_deriv hf hf' hfd, Complex.real_smul, smul_eq_mul, smul_eq_mul]
  rw [show ((2 : ℂ) * (π : ℝ) * Complex.I * (((2 * π)⁻¹ * ξ : ℝ) : ℂ)) = Complex.I * ξ by
    push_cast
    field_simp]
  ring

/-- Mathlib's transform of $x \mapsto c \, g(x)$ is $c$ times the transform of $g$, for
$g : \mathbb{R} \to \mathbb{C}$ and $c \in \mathbb{C}$. -/
private theorem fourier_const_mul (c : ℂ) (g : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun x : ℝ => c * g x) w = c * 𝓕 g w := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Circle.smul_def, Circle.smul_def]
  ring

/-- **Equation (4.2.8)** of [han2009theoretical], in one dimension. Let
$f : \mathbb{R} \to \mathbb{C}$ be integrable, and let $x \mapsto x f(x)$ be integrable. Then
$$\widehat{(x f(x))}(\xi) = i \, \frac{d}{d\xi} \hat f(\xi) \qquad \text{for all } \xi \in
  \mathbb{R}.$$

The proof goes through `AtkinsonHan.Chapter04.bookFourier_eq_fourier`. The rescaling
$\xi \mapsto (2\pi)^{-1} \xi$ of the argument gives a chain-rule factor $(2\pi)^{-1}$, and this
factor cancels the $2\pi$ in the exponent of Mathlib's character. Therefore the constant in the
book's normalization is $i$.

**Reading.** The book states the multi-index identity on the Schwartz space. This is the
one-dimensional, first-order rule for integrable inputs with integrable first moment. -/
theorem equation_4_2_8 {f : ℝ → ℂ} (hf : Integrable f) (hfx : Integrable fun x : ℝ => x • f x)
    (ξ : ℝ) :
    bookFourier (fun x : ℝ => (x : ℂ) * f x) ξ = Complex.I * deriv (bookFourier f) ξ := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hmul : (fun x : ℝ => (-2 * (π : ℂ) * Complex.I * (x : ℂ)) • f x)
      = fun x : ℝ => (-2 * (π : ℂ) * Complex.I) * ((x : ℂ) * f x) :=
    funext fun x => by rw [smul_eq_mul]; ring
  -- the derivative of Mathlib's transform, rescaled and renormalised
  have hinner : HasDerivAt (fun t : ℝ => (2 * π)⁻¹ * t) ((2 * π)⁻¹) ξ := by
    simpa using (hasDerivAt_id ξ).const_mul ((2 * π)⁻¹ : ℝ)
  have hcomp : HasDerivAt (fun t : ℝ => 𝓕 f ((2 * π)⁻¹ * t))
      ((2 * π)⁻¹ • 𝓕 (fun x : ℝ => (-2 * (π : ℂ) * Complex.I * (x : ℂ)) • f x)
        ((2 * π)⁻¹ * ξ)) ξ :=
    (Real.hasDerivAt_fourier hf hfx ((2 * π)⁻¹ * ξ)).scomp ξ hinner
  have hbook : HasDerivAt (bookFourier f)
      (-Complex.I * bookFourier (fun x : ℝ => (x : ℂ) * f x) ξ) ξ := by
    have h := hcomp.const_smul (bookConst ℝ : ℝ)
    rw [hmul, fourier_const_mul] at h
    have hval : (bookConst ℝ : ℝ) • ((2 * π)⁻¹ • (-2 * (π : ℂ) * Complex.I *
          𝓕 (fun x : ℝ => (x : ℂ) * f x) ((2 * π)⁻¹ * ξ)))
        = -Complex.I * bookFourier (fun x : ℝ => (x : ℂ) * f x) ξ := by
      rw [bookFourier_eq_fourier]
      simp only [Complex.real_smul, smul_eq_mul]
      push_cast
      field_simp
    rw [hval] at h
    rw [show bookFourier f = ((bookConst ℝ : ℝ) • fun t : ℝ => 𝓕 f ((2 * π)⁻¹ * t)) from
      funext fun t => bookFourier_eq_fourier f t]
    exact h
  rw [hbook.deriv, ← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

/-- **Definition 4.2.1 and equation (4.2.9)** of [han2009theoretical]. The book's Fourier transform
as a continuous linear map of the Schwartz space $\mathcal{S}(V)$ of complex-valued functions
into itself. It is defined as
$$\varphi \mapsto (2\pi)^{-d/2} \, (\mathcal{F} \varphi)\bigl((2\pi)^{-1} \, \cdot\bigr),$$
where $\mathcal{F}$ is Mathlib's transform on the Schwartz space.

The Schwartz space of Definition 4.2.1 is Mathlib's `SchwartzMap`. Mathlib's
`SchwartzMap.fourierTransformCLM` gives the statement (4.2.9) for $\mathcal{F}$. The dilation
$\xi \mapsto (2\pi)^{-1} \xi$ is a continuous linear equivalence of $V$, so composition with it
preserves $\mathcal{S}(V)$. `AtkinsonHan.Chapter04.definition_4_2_1` shows that the map is
`AtkinsonHan.Chapter04.bookFourier`. -/
noncomputable def bookFourierCLM : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  (bookConst V : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * π)⁻¹ : ℝ) (by positivity)))).comp
      (SchwartzMap.fourierTransformCLM ℂ)

/-- **Definition 4.2.1** of [han2009theoretical]. For every Schwartz function
$\varphi \in \mathcal{S}(V)$ and every $\xi \in V$, the continuous linear map
`AtkinsonHan.Chapter04.bookFourierCLM` gives $\hat\varphi(\xi)$, the book's transform (4.2.1).

**Reading.** The book's decay conditions are represented by Mathlib's Schwartz space.
This theorem computes the action of the bounded transform on that space. -/
theorem definition_4_2_1 (f : 𝓢(V, ℂ)) (ξ : V) : bookFourierCLM f ξ = bookFourier f ξ := by
  rw [bookFourier_eq_fourier, Complex.real_smul, bookFourierCLM]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.fourier_coe, smul_eq_mul]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Definition 4.2.2** of [han2009theoretical]. The space $\mathcal{S}'(\mathbb{R}^d)$ of
**tempered distributions** is the space of all continuous linear functionals on the Schwartz
space $\mathcal{S}(\mathbb{R}^d)$. The formal statement: a linear functional $T$ on
$\mathcal{S}(V)$ agrees with a tempered distribution $u$, that is $u(\varphi) = T(\varphi)$ for
all $\varphi$, if and only if $T$ is continuous.

The space of tempered distributions is Mathlib's `TemperedDistribution`, with notation
`𝓢'(E, F)`. Because this space is defined as the dual space, the definition is stated as a
characterization of the linear functionals that come from it. The statement holds for every real
inner product space $V$, not only for a finite-dimensional one.
`AtkinsonHan.Chapter04.definition_4_2_2_seq` is the sequential form.

**Generalization.** The characterization is valid for an arbitrary real inner product
space, while the source uses $\mathbb R^d$. -/
theorem definition_4_2_2 (T : 𝓢(V, ℂ) →ₗ[ℂ] ℂ) :
    (∃ u : 𝓢'(V, ℂ), ∀ φ, u φ = T φ) ↔ Continuous T := by
  constructor
  · rintro ⟨u, hu⟩
    have hcont : Continuous fun φ : 𝓢(V, ℂ) => u φ :=
      (u : 𝓢(V, ℂ) →L[ℂ] ℂ).continuous
    simpa only [funext hu] using hcont
  · intro h
    exact ⟨(⟨T, h⟩ : 𝓢(V, ℂ) →L[ℂ] ℂ), fun _ => rfl⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Definition 4.2.2** of [han2009theoretical], the sequential form in the remark after the
definition. A linear functional $T$ on $\mathcal{S}(\mathbb{R}^d)$ is a tempered distribution if
and only if $\varphi_n \to \varphi$ in $\mathcal{S}(\mathbb{R}^d)$ implies
$T(\varphi_n) \to T(\varphi)$.

The Schwartz space is metrizable, so sequential continuity is the same as continuity. As in
`AtkinsonHan.Chapter04.definition_4_2_2`, "is a tempered distribution" means that some
$u \in \mathcal{S}'(V)$ satisfies $u(\varphi) = T(\varphi)$ for all $\varphi$, and the statement
holds for every real inner product space $V$.

**Generalization.** Sequential continuity gives the same characterization for arbitrary
real inner product spaces in the Mathlib presentation. -/
theorem definition_4_2_2_seq (T : 𝓢(V, ℂ) →ₗ[ℂ] ℂ) :
    (∃ u : 𝓢'(V, ℂ), ∀ φ, u φ = T φ) ↔
      ∀ (φ : ℕ → 𝓢(V, ℂ)) (ψ : 𝓢(V, ℂ)), Filter.Tendsto φ Filter.atTop (nhds ψ) →
        Filter.Tendsto (fun n => T (φ n)) Filter.atTop (nhds (T ψ)) := by
  rw [definition_4_2_2, continuous_iff_seqContinuous]
  exact ⟨fun h φ ψ hφ => h hφ, fun h _ _ hφ => h _ _ hφ⟩

/-- **Definition 4.2.3** of [han2009theoretical]. The **Fourier transform of a tempered
distribution** $u \in \mathcal{S}'(\mathbb{R}^d)$ is the tempered distribution $\hat u$ defined
by $\langle \hat u, \varphi \rangle = \langle u, \hat \varphi \rangle$ for
$\varphi \in \mathcal{S}(\mathbb{R}^d)$. It is a continuous linear map of
$\mathcal{S}'(\mathbb{R}^d)$ into itself.

The map is precomposition with `AtkinsonHan.Chapter04.bookFourierCLM`, for the topology of
pointwise convergence on $\mathcal{S}'(V)$.

**Reading.** The source gives the action on test functions. This packages the same action
as a continuous linear map for the topology of pointwise convergence. -/
noncomputable def bookFourierTD : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ bookFourierCLM

/-- **Definition 4.2.3 and equation (4.2.13)** of [han2009theoretical]. For every tempered
distribution $u$ and every Schwartz function $\varphi$,
$$\langle \hat u, \varphi \rangle = \langle u, \hat\varphi \rangle.$$
-/
theorem definition_4_2_3 (u : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    bookFourierTD u φ = u (bookFourierCLM φ) :=
  rfl

/-- **Equation (4.2.12)** of [han2009theoretical]. Let $1 \le p \le \infty$.

1. A function $g \in L^p(V)$ defines a tempered distribution through the pairing $\langle g,
   \varphi \rangle = \int_V \varphi(x) \, g(x) \, dx$.
2. For $f \in L^1(V)$, the Fourier transform of $f$ as a tempered distribution (Definition
   4.2.3) is the function $\hat f$ of (4.2.3): for every Schwartz function $\varphi$,
$$\langle \hat f, \varphi \rangle = \int_V \varphi(\xi) \, \hat f(\xi) \, d\xi.$$

The second part means that Definition 4.2.3 extends the transform of the integrable functions.
The book says that this "can be verified by applying Fubini's theorem"; the proof uses the
multiplication formula (4.2.10), `AtkinsonHan.Chapter04.equation_4_2_10`. The tempered
distribution of an $L^p$ function is Mathlib's `MeasureTheory.Lp.toTemperedDistribution`. -/
theorem equation_4_2_12 {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : Lp ℂ p (volume : Measure V))
    (f : Lp ℂ 1 (volume : Measure V)) (φ : 𝓢(V, ℂ)) :
    Lp.toTemperedDistribution g φ = ∫ x : V, φ x * (g : V → ℂ) x ∧
      bookFourierTD (Lp.toTemperedDistribution f) φ
        = ∫ ξ : V, φ ξ * bookFourier (f : V → ℂ) ξ := by
  have hf : Integrable (f : V → ℂ) := L1.integrable_coeFn f
  have hφ : Integrable (φ : V → ℂ) := φ.integrable
  refine ⟨by simp [Lp.toTemperedDistribution_apply], ?_⟩
  rw [definition_4_2_3, Lp.toTemperedDistribution_apply]
  calc ∫ x : V, (bookFourierCLM φ) x • (f : V → ℂ) x
      = ∫ x : V, (f : V → ℂ) x * bookFourier (φ : V → ℂ) x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [smul_eq_mul, definition_4_2_1]
        ring
    _ = ∫ ξ : V, φ ξ * bookFourier (f : V → ℂ) ξ := by
        rw [← equation_4_2_10 hf hφ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => mul_comm _ _)

/-! ### The transform on `L²` -/

/-- Composition with a continuous linear equivalence $e$ of $V$, as a linear equivalence of
$\mathcal{S}(V)$. -/
private noncomputable def schwartzCompEquiv (e : V ≃L[ℝ] V) : 𝓢(V, ℂ) ≃ₗ[ℂ] 𝓢(V, ℂ) :=
  LinearEquiv.ofLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e).toLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e.symm).toLinearMap
    (by ext φ x; simp) (by ext φ x; simp)

/-- The dilation $\xi \mapsto (2\pi)^{-1} \xi$ of $V$, as a continuous linear equivalence. -/
private noncomputable def bookDilation : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * π)⁻¹ : ℝ) (by positivity))

/-- The book's Fourier transform as a **linear bijection of the Schwartz space** $\mathcal{S}(V)$
onto itself. It is Mathlib's Fourier transform on $\mathcal{S}(V)$, followed by composition with
the dilation $\xi \mapsto (2\pi)^{-1} \xi$ and by multiplication with the constant
$(2\pi)^{-d/2}$. Each of these three maps is invertible.

This map supports Theorem 4.2.4 of [han2009theoretical].
`AtkinsonHan.Chapter04.bookFourierSchwartzEquiv_apply` shows that it is
`AtkinsonHan.Chapter04.bookFourier` on Schwartz functions. -/
noncomputable def bookFourierSchwartzEquiv : 𝓢(V, ℂ) ≃ₗ[ℂ] 𝓢(V, ℂ) :=
  (FourierTransform.fourierEquiv ℂ 𝓢(V, ℂ)).trans ((schwartzCompEquiv bookDilation).trans
    (LinearEquiv.smulOfNeZero ℂ 𝓢(V, ℂ) (bookConst V : ℂ)
      (Complex.ofReal_ne_zero.mpr bookConst_pos.ne')))

/-- For every Schwartz function $\varphi$ and every $\xi \in V$, the linear bijection
`AtkinsonHan.Chapter04.bookFourierSchwartzEquiv` gives $\hat\varphi(\xi)$, the book's transform
(4.2.1). -/
@[simp]
theorem bookFourierSchwartzEquiv_apply (φ : 𝓢(V, ℂ)) (ξ : V) :
    bookFourierSchwartzEquiv φ ξ = bookFourier φ ξ := by
  rw [← definition_4_2_1]
  rfl

/-- For a Schwartz function $g$, the square of the $L^2$ norm of $g$ is $\int_V |g(x)|^2 \, dx$. -/
private theorem norm_toLp_two_sq (g : 𝓢(V, ℂ)) :
    ‖g.toLp 2 (volume : Measure V)‖ ^ 2 = ∫ x : V, ‖g x‖ ^ 2 := by
  have hint : (0 : ℝ) ≤ ∫ x : V, ‖g x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) 2
  have hpow : ∀ x : V, ‖g x‖ ^ (2 : ℝ) = ‖g x‖ ^ (2 : ℕ) := fun x =>
    Real.rpow_natCast ‖g x‖ 2
  rw [SchwartzMap.norm_toLp' (p := 2) (by simp) (by simp)]
  simp only [ENNReal.toReal_ofNat]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hint,
    show (2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  exact integral_congr_ae (Filter.Eventually.of_forall hpow)

/-- The book's transform preserves the $L^2$ norm of a Schwartz function; this is Theorem 4.2.4 in
the form that the extension to $L^2$ uses. -/
private theorem norm_toLp_bookFourier_eq (φ : 𝓢(V, ℂ)) :
    ‖(bookFourierSchwartzEquiv φ).toLp 2 (volume : Measure V)‖
      = ‖φ.toLp 2 (volume : Measure V)‖ := by
  have h := theorem_4_2_4 (V := V) φ
  have h1 := norm_toLp_two_sq (bookFourierSchwartzEquiv φ)
  have h2 := norm_toLp_two_sq φ
  simp only [bookFourierSchwartzEquiv_apply] at h1
  have hsq : ‖(bookFourierSchwartzEquiv φ).toLp 2 (volume : Measure V)‖ ^ 2
      = ‖φ.toLp 2 (volume : Measure V)‖ ^ 2 := by rw [h1, h2, h]
  have hnn := norm_nonneg ((bookFourierSchwartzEquiv φ).toLp 2 (volume : Measure V))
  have hnn' := norm_nonneg (φ.toLp 2 (volume : Measure V))
  nlinarith [hsq]

/-- **Theorem 4.2.4 and equations (4.2.14)–(4.2.18)** of [han2009theoretical]. The Fourier transform
on $L^2(\mathbb{R}^d)$: the unique continuous extension of the book's transform from the
Schwartz space to a linear isometry of $L^2(V)$ onto itself.

Since $\mathcal{S}(V)$ is dense in $L^2(V)$, the continuous extension is unique. On
$L^1 \cap L^2$ the source identifies it with the integral (4.2.16). The book also
characterizes the transform and its inverse via the truncated-integral limits
(4.2.14)–(4.2.15).
`AtkinsonHan.Chapter04.theorem_4_2_4_l2` shows that it agrees with
`AtkinsonHan.Chapter04.bookFourier` on the Schwartz space and that it is an isometry, (4.2.18).
Because it is an equivalence, it is onto.

This is Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ` in the book's normalization. It is built
in the same way, by extension from the Schwartz space, and not by rescaling Mathlib's map. A
rescaling would need the dilation as a linear isometry of $L^2(V)$, and
`MeasureTheory.Lp.dilationₗᵢ` gives this only for real scalars in one real dimension.

**Reading.** The book characterizes the $L^2$ transform by limits of truncated integrals.
The definition extends the transform from Schwartz functions by continuity. The theorem
`theorem_4_2_4_l2` proves agreement on Schwartz data. -/
noncomputable def bookFourierL2 : (Lp (α := V) ℂ 2) ≃ₗᵢ[ℂ] (Lp (α := V) ℂ 2) :=
  (bookFourierSchwartzEquiv (V := V)).extendOfIsometry
    (SchwartzMap.toLpCLM ℂ (E := V) ℂ 2 volume) (SchwartzMap.toLpCLM ℂ (E := V) ℂ 2 volume)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    norm_toLp_bookFourier_eq

/-- **Theorem 4.2.4 and equation (4.2.18)** of [han2009theoretical] (Plancherel's theorem), on
$L^2(\mathbb{R}^d)$. The extension $\mathcal{F} : L^2(V) \to L^2(V)$ of the book's transform
(`AtkinsonHan.Chapter04.bookFourierL2`) has the following properties:

1. it is an isometry: $\|\mathcal{F} f\|_{L^2} = \|f\|_{L^2}$ for all $f \in L^2(V)$;
2. it maps $L^2(V)$ onto $L^2(V)$;
3. on the Schwartz space it is the book's transform: for every $\varphi \in \mathcal{S}(V)$,
   $\mathcal{F}$ maps the class of $\varphi$ in $L^2(V)$ to the class of $\hat\varphi$, where
   $\hat\varphi$ is computed by `AtkinsonHan.Chapter04.bookFourierSchwartzEquiv`;
4. for every $\varphi \in \mathcal{S}(V)$ and $\xi \in V$, the value of that Schwartz function
   at $\xi$ is the integral $\hat\varphi(\xi)$ of (4.2.3), as computed by
   `AtkinsonHan.Chapter04.bookFourier`. -/
theorem theorem_4_2_4_l2 :
    (∀ f : Lp (α := V) ℂ 2, ‖bookFourierL2 f‖ = ‖f‖) ∧
      Function.Surjective (bookFourierL2 (V := V)) ∧
      (∀ φ : 𝓢(V, ℂ),
          bookFourierL2 (φ.toLp 2 volume) = (bookFourierSchwartzEquiv φ).toLp 2 volume) ∧
        ∀ (φ : 𝓢(V, ℂ)) (ξ : V), bookFourierSchwartzEquiv φ ξ = bookFourier φ ξ :=
  ⟨fun f => bookFourierL2.norm_map f, bookFourierL2.surjective,
    fun φ => LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ φ, bookFourierSchwartzEquiv_apply⟩

end AtkinsonHan.Chapter04
