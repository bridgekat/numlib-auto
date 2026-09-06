import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Atkinson–Han §4.2: the Fourier transform

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §4.2.

Almost everything the section states is in Mathlib, and what is left is a matter of
*normalisation*. The book's transform (4.2.1) is

`𝓕_book f ξ = (2 π)^{-d/2} ∫ f x exp (-i ⟪x, ξ⟫) dx`,

while Mathlib's `𝓕` uses the analyst's character `exp (-2 π i ⟪x, ξ⟫)` and no prefactor. The two
are related by `bookFourier_eq_fourier`,

`𝓕_book f ξ = (2 π)^{-d/2} • 𝓕 f ((2 π)⁻¹ • ξ)`,

and that single lemma carries every Mathlib result across. The book's transform is also, exactly,
Mathlib's `VectorFourier.fourierIntegral` for the *probabilist* character `Real.probChar`
(`bookFourier_eq_vectorFourier`), which is what the statements not involving inversion use.

Everything is stated over a finite-dimensional real inner product space rather than over
`EuclideanSpace ℝ (Fin d)` alone, with `d = finrank ℝ V`: that is the same statement for the
book's `ℝ^d`, and it lets the one-dimensional rules be read off at `V = ℝ`, where Mathlib states
them.

Definitions 4.2.1, 4.2.2 and 4.2.3 are Mathlib's `SchwartzMap` (`𝓢(E, F)`),
`TemperedDistribution` (`𝓢'(E, F)`) and the Fourier transform on the latter, so they are stated
as identifications rather than as new definitions.

## Main definitions

* `bookConst` — the normalising constant `(2 π)^{-d/2}` of (4.2.1), in `d = finrank ℝ V`.
* `bookFourier`, `bookFourierInv` — the book's transform (4.2.1) and its inverse (4.2.4).
* `bookFourierCLM` — the same transform as a continuous linear map `𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)`
  (Definition 4.2.1), and `bookFourierTD` its extension to `𝓢'(V, ℂ)` (Definitions 4.2.2–4.2.3).

## Main results

* `bookFourier_eq_fourier`, `bookFourier_eq_vectorFourier`, `bookFourierInv_eq_fourierInv` — the
  normalisation bridges to Mathlib's `𝓕`, `𝓕⁻` and `VectorFourier.fourierIntegral`. Everything
  below is proved through them.
* `equation_4_2_5` — (4.2.5), linearity.
* `equation_4_2_6`, `continuous_bookFourier` — (4.2.6), the transform maps `L¹` into `L^∞` with
  `‖f̂‖_∞ ≤ (2 π)^{-d/2} ‖f‖_{L¹}`, and its values are continuous.
* `equation_4_2_7`, `equation_4_2_7_dim_one` — (4.2.7), the differentiation rule
  `𝓕(∂_v f) ξ = i ⟪v, ξ⟫ 𝓕 f ξ`, and the one-dimensional form `𝓕(f') ξ = i ξ 𝓕 f ξ`.
* `equation_4_2_8` — (4.2.8) in one dimension, the multiplication rule
  `𝓕(x f(x)) ξ = i (𝓕 f)' ξ`.
* `equation_4_2_10` — (4.2.10), the multiplication formula `∫ f̂ g = ∫ f ĝ`.
* `equation_4_2_11` — (4.2.4) and (4.2.11), the inversion formula.
* `equation_4_2_12` — (4.2.12), an `L^p` function as a tempered distribution, and the consistency
  of Definition 4.2.3 with the integral (4.2.3) on `L¹`.
* `theorem_4_2_4` — Theorem 4.2.4 with (4.2.18), Plancherel's theorem on `𝓢(V, ℂ)`.
* `bookFourierSchwartzEquiv`, `bookFourierL2`, `theorem_4_2_4_l2` — Theorem 4.2.4 with
  (4.2.14)–(4.2.18) on `L²(ℝ^d)`: the transform, extended from the Schwartz space, is an isometry
  of `L²(ℝ^d)` onto itself.
* `definition_4_2_1`, `definition_4_2_3` — the two bundled transforms agree with `bookFourier`
  and with the duality formula (4.2.13).

## Implementation notes

The prefactor `(2 π)^{-d/2}` is named `bookConst` rather than inlined, so that the two places
where it has to cancel the Jacobian `(2 π)^d` of the rescaling `ξ ↦ (2 π)⁻¹ • ξ` — the inversion
formula and Plancherel — can both cite one identity, `bookConst V * (bookConst V * (2 π)^d) = 1`.
-/

namespace AtkinsonHan.Chapter04

open MeasureTheory Module Real VectorFourier

open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The book's normalising constant `(2 π)^{-d/2}` in dimension `d = finrank ℝ V`. It is the
constant that makes the transform an isometry of `L²` (Theorem 4.2.4). -/
noncomputable def bookConst (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (2 * π) ^ (-(finrank ℝ V : ℝ) / 2)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The normalising constant of (4.2.1) is positive, so it may be divided by and pulled out of
a norm. -/
theorem bookConst_pos : 0 < bookConst V := by
  rw [bookConst]
  positivity

/-- The book's Fourier transform (4.2.1), (4.2.3):
`𝓕_book f ξ = (2 π)^{-d/2} ∫ f x exp (-i ⟪x, ξ⟫) dx` on a `d`-dimensional real inner product
space. -/
noncomputable def bookFourier (f : V → ℂ) (ξ : V) : ℂ :=
  (bookConst V : ℝ) • ∫ x : V, Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * f x

/-- The book's transform is Mathlib's vector-valued Fourier integral for the probabilist
character `exp (i t)`, which is the convention without the `2 π` in the exponent. -/
theorem bookFourier_eq_vectorFourier (f : V → ℂ) (ξ : V) :
    bookFourier f ξ =
      (bookConst V : ℝ) • fourierIntegral Real.probChar volume (innerₗ V) f ξ := by
  rw [bookFourier, fourierIntegral_probChar]
  simp [smul_eq_mul]

/-- **The normalisation bridge**: the book's transform is Mathlib's `𝓕` rescaled in both the
value and the argument. Every statement of this section about inversion or about `L²` goes
through this lemma. -/
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

/-- (4.2.5): the Fourier transform is linear. -/
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

/-- (4.2.6): the Fourier transform maps `L¹` into `L^∞`, with `‖f̂‖_∞ ≤ (2 π)^{-d/2} ‖f‖_{L¹}`. -/
theorem equation_4_2_6 (f : V → ℂ) (ξ : V) :
    ‖bookFourier f ξ‖ ≤ bookConst V * ∫ x : V, ‖f x‖ := by
  rw [bookFourier_eq_vectorFourier, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg bookConst_pos.le]
  exact mul_le_mul_of_nonneg_left
    (norm_fourierIntegral_le_integral_norm _ _ _ _ _) bookConst_pos.le

/-- (4.2.6): the Fourier transform of an `L¹` function is continuous. -/
theorem continuous_bookFourier {f : V → ℂ} (hf : Integrable f) : Continuous (bookFourier f) := by
  simp only [funext fun ξ => bookFourier_eq_vectorFourier f ξ]
  exact (fourierIntegral_continuous Real.continuous_probChar continuous_innerₗ
    hf).const_smul (bookConst V)

/-- (4.2.10), the multiplication formula: `∫ f̂ g = ∫ f ĝ`. It is Fubini applied to
`f x * g ξ * exp (-i ⟪x, ξ⟫)`, and it is what makes Definition 4.2.3 consistent with (4.2.3)
on `L¹`. -/
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

/-- The book's inverse Fourier transform (4.2.4):
`𝓕⁻¹_book f x = (2 π)^{-d/2} ∫ f ξ exp (i ⟪x, ξ⟫) dξ`. -/
noncomputable def bookFourierInv (f : V → ℂ) (x : V) : ℂ :=
  (bookConst V : ℝ) • ∫ ξ : V, Complex.exp (((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * f ξ

/-- The bridge for the inverse transform, the mirror of `bookFourier_eq_fourier`. -/
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
/-- The prefactor squared cancels the Jacobian of the change of variables `ξ = 2 π u`: this is
the whole reason for the book's normalisation `(2 π)^{-d/2}`. -/
private theorem bookConst_sq_mul_pow :
    bookConst V * (bookConst V * (2 * π) ^ finrank ℝ V) = 1 := by
  rw [bookConst, ← Real.rpow_natCast (2 * π) (finrank ℝ V), ← mul_assoc,
    ← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity),
    show -(finrank ℝ V : ℝ) / 2 + -(finrank ℝ V : ℝ) / 2 + (finrank ℝ V : ℝ) = 0 by ring,
    Real.rpow_zero]

/-- The change of variables `ξ = 2 π u`, whose Jacobian `(2 π)^d` is what the book's prefactor
`(2 π)^{-d/2}` squares to cancel. -/
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

/-- (4.2.4) and (4.2.11), **the inversion formula**: for `f` continuous and integrable whose
transform is integrable, `f x = (2 π)^{-d/2} ∫ f̂ ξ exp (i ⟪x, ξ⟫) dξ`. -/
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

/-- Theorem 4.2.4 with (4.2.14)-(4.2.18), **Plancherel's theorem**, on the Schwartz space: the
book's normalisation `(2 π)^{-d/2}` is precisely the one that makes the Fourier transform preserve
the `L²` norm. The extension to all of `L²(ℝ^d)`, which is (4.2.14)–(4.2.17), is Mathlib's
`MeasureTheory.Lp.fourierTransformₗᵢ` composed with the `L²` dilation by `2 π`; that dilation is
`MeasureTheory.Lp.dilationₗᵢ` of `Numlib.Analysis.Wavelet.Haar`, which exists only for
`Lp ℝ 2 (volume : Measure ℝ)` — real scalars in one real dimension — and generalising it to a Haar
measure on a finite-dimensional space with complex values is the whole of what the `L²` statement
still needs. -/
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

/-- **(4.2.7)** in `d` dimensions, at first order: the Fourier transform turns the derivative of
`f` in a direction `v` into multiplication by `i ⟪v, ξ⟫`. The book states the rule for an
arbitrary multi-index, `𝓕(∂^α f) ξ = (i ξ)^α 𝓕 f ξ`; the general case is this one iterated
`|α|` times, and the first-order form is the one the applications to differential equations use.
-/
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

/-- (4.2.7) in one dimension: the Fourier transform turns differentiation into multiplication by
`i ξ`. At `V = ℝ` the book's normalising constant cancels, so the book's rule and Mathlib's
`Real.fourier_deriv` differ only by the argument scaling. -/
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

/-- Pulling a constant out of Mathlib's Fourier transform. -/
private theorem fourier_const_mul (c : ℂ) (g : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun x : ℝ => c * g x) w = c * 𝓕 g w := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Circle.smul_def, Circle.smul_def]
  ring

/-- **(4.2.8)** in one dimension: the Fourier transform turns multiplication by the variable into
differentiation, `𝓕(x f(x)) ξ = i (𝓕 f)'(ξ)`. This is the rule in which the argument rescaling
`ξ ↦ (2 π)⁻¹ ξ` of `bookFourier_eq_fourier` contributes a chain-rule factor `(2 π)⁻¹`, and that
factor is exactly what cancels the `2 π` in the exponent of Mathlib's character; in the book's
normalisation the constant is a bare `i`. -/
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

/-- Definition 4.2.1 and (4.2.9): the book's Fourier transform is a continuous linear map of the
Schwartz space `𝓢(ℝ^d)` into itself. Mathlib's `SchwartzMap.fourierTransformCLM` says this for
`𝓕`; the book's transform differs from it by the constant `(2 π)^{-d/2}` and by the dilation
`ξ ↦ ξ / (2 π)`, which is a continuous linear equivalence and therefore preserves `𝓢`. -/
noncomputable def bookFourierCLM : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  (bookConst V : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * π)⁻¹ : ℝ) (by positivity)))).comp
      (SchwartzMap.fourierTransformCLM ℂ)

/-- The continuous linear map of Definition 4.2.1 is the book's Fourier transform. -/
theorem definition_4_2_1 (f : 𝓢(V, ℂ)) (ξ : V) : bookFourierCLM f ξ = bookFourier f ξ := by
  rw [bookFourier_eq_fourier, Complex.real_smul, bookFourierCLM]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.fourier_coe, smul_eq_mul]
  rfl

/-- Definitions 4.2.2 and 4.2.3: the tempered distributions `𝓢'(ℝ^d)` are Mathlib's
`TemperedDistribution`, the continuous linear functionals on `𝓢(ℝ^d)`, and the book's Fourier
transform extends to them by duality. -/
noncomputable def bookFourierTD : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ bookFourierCLM

/-- (4.2.13): the Fourier transform of a tempered distribution is defined by `⟨f̂, φ⟩ = ⟨f, φ̂⟩`. -/
theorem definition_4_2_3 (u : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    bookFourierTD u φ = u (bookFourierCLM φ) :=
  rfl

/-- **(4.2.12)**: an `L^p` function `f` is a tempered distribution through the pairing
`⟨f, φ⟩ = ∫ f φ` — that is Mathlib's `MeasureTheory.Lp.toTemperedDistribution` — and, for
`f ∈ L¹`, the distributional transform of Definition 4.2.3 is the integral (4.2.3): the two
readings of `f̂` agree, so Definition 4.2.3 extends the transform of §4.2.1 rather than replacing
it. The second clause is the book's remark that "this can be verified by applying Fubini's
theorem", which is the multiplication formula (4.2.10). -/
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

/-- Precomposition with a linear homeomorphism of the underlying space, as a linear equivalence
of the Schwartz space; Mathlib has it as a continuous linear map only. -/
private noncomputable def schwartzCompEquiv (e : V ≃L[ℝ] V) : 𝓢(V, ℂ) ≃ₗ[ℂ] 𝓢(V, ℂ) :=
  LinearEquiv.ofLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e).toLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e.symm).toLinearMap
    (by ext φ x; simp) (by ext φ x; simp)

/-- The dilation of the argument by `(2 π)⁻¹`, the change of variables that separates the book's
transform from Mathlib's. -/
private noncomputable def bookDilation : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * π)⁻¹ : ℝ) (by positivity))

/-- **The book's Fourier transform as a linear equivalence of the Schwartz space.** It is
Mathlib's, followed by the dilation `ξ ↦ (2 π)⁻¹ ξ` of the argument and the constant
`(2 π)^{-d/2}`, each of which is invertible; `bookFourierSchwartzEquiv_apply` says it is
`bookFourier`. -/
noncomputable def bookFourierSchwartzEquiv : 𝓢(V, ℂ) ≃ₗ[ℂ] 𝓢(V, ℂ) :=
  (FourierTransform.fourierEquiv ℂ 𝓢(V, ℂ)).trans ((schwartzCompEquiv bookDilation).trans
    (LinearEquiv.smulOfNeZero ℂ 𝓢(V, ℂ) (bookConst V : ℂ)
      (Complex.ofReal_ne_zero.mpr bookConst_pos.ne')))

@[simp]
theorem bookFourierSchwartzEquiv_apply (φ : 𝓢(V, ℂ)) (ξ : V) :
    bookFourierSchwartzEquiv φ ξ = bookFourier φ ξ := by
  rw [← definition_4_2_1]
  rfl

/-- The `L²` norm of a Schwartz function, as the integral the book writes. -/
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

/-- The book's transform preserves the `L²` norm of a Schwartz function: Theorem 4.2.4 read
through `SchwartzMap.norm_toLp'`. -/
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

/-- **Theorem 4.2.4** on `L²(ℝ^d)`, with (4.2.14)–(4.2.18): the book's Fourier transform extends
from the Schwartz space to a linear isometry of `L²(ℝ^d)` *onto* itself.

The extension is the unique continuous one, since `𝓢(ℝ^d)` is dense in `L²(ℝ^d)`; on `L¹ ∩ L²` it
is still given by the integral (4.2.16), and in general it is the `L²` limit (4.2.14) of the
truncated integrals, which is what a continuous extension means.  `theorem_4_2_4_l2` records that
it agrees with `bookFourier` on the Schwartz space and that it is an isometry, (4.2.18); being an
equivalence it is onto, and its inverse is the transform of (4.2.15) and (4.2.17).

This is Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ` in the book's normalisation, and is built
the same way, by extending from the Schwartz space rather than by rescaling that map: the
rescaling would need the dilation as a linear isometry of `L²(ℝ^d)`, which
`MeasureTheory.Lp.dilationₗᵢ` supplies only for real scalars in one real dimension. -/
noncomputable def bookFourierL2 : (Lp (α := V) ℂ 2) ≃ₗᵢ[ℂ] (Lp (α := V) ℂ 2) :=
  (bookFourierSchwartzEquiv (V := V)).extendOfIsometry
    (SchwartzMap.toLpCLM ℂ (E := V) ℂ 2 volume) (SchwartzMap.toLpCLM ℂ (E := V) ℂ 2 volume)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    norm_toLp_bookFourier_eq

/-- **Theorem 4.2.4** with **(4.2.18)** on `L²(ℝ^d)`: the book's Fourier transform maps `L²(ℝ^d)`
onto `L²(ℝ^d)` and is an isometry there, and on the Schwartz space it is still the transform
(4.2.3). -/
theorem theorem_4_2_4_l2 :
    (∀ f : Lp (α := V) ℂ 2, ‖bookFourierL2 f‖ = ‖f‖) ∧
      Function.Surjective (bookFourierL2 (V := V)) ∧
      (∀ φ : 𝓢(V, ℂ),
          bookFourierL2 (φ.toLp 2 volume) = (bookFourierSchwartzEquiv φ).toLp 2 volume) ∧
        ∀ (φ : 𝓢(V, ℂ)) (ξ : V), bookFourierSchwartzEquiv φ ξ = bookFourier φ ξ :=
  ⟨fun f => bookFourierL2.norm_map f, bookFourierL2.surjective,
    fun φ => LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ φ, bookFourierSchwartzEquiv_apply⟩

end AtkinsonHan.Chapter04
