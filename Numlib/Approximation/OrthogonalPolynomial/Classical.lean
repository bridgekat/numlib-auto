/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Numlib.Algebra.Polynomial.Derivative
import Numlib.Analysis.SpecialFunctions.PolynomialExp
import Numlib.Approximation.OrthogonalPolynomial

/-!
# The classical weights and their orthogonal polynomials

This module treats the classical weights other than the Legendre weight of
`Numlib.Approximation.OrthogonalPolynomial`: the Chebyshev weight $(1 - x^2)^{-1/2}$ on $(-1, 1)$,
the Jacobi weights $(1 - x)^\alpha (1 + x)^\beta$ on $(-1, 1)$, the Laguerre weight $e^{-x}$ on
$(0, \infty)$ and the Hermite weight $e^{-x^2}$ on $\mathbb{R}$. Each is shown to be a weight in the
sense of `OrthogonalPolynomial.IsWeight`, so that the monic orthogonal polynomials $p_n$, Gauss
quadrature (`Quadrature.exists_gauss`) and the rest of the general theory apply. The classical
polynomials, the Chebyshev polynomials $T_n$, the Laguerre polynomials $\mathcal{L}_n$ and the
physicists' Hermite polynomials $H_n$, are identified with $p_n$ up to their leading coefficients.
The recurrence coefficients $\alpha_n$ and $\beta_n$ of the Legendre, Laguerre and Hermite weights
are computed in closed form. The presentation follows [quarteroni2000numerical], §10.1 and
§10.5–10.6, and [han2009theoretical], §3.5.

The Laguerre and Hermite polynomials are defined by recurrences. Their Rodrigues formulas and
orthogonality relations rest on an algebraic form of Rodrigues' formula: $\mathcal{L}_n$ is the
$n$-th iterate of $f \mapsto f' - f$ applied to $x^n$, and $H_n$ is the $n$-th iterate of
$f \mapsto 2x f - f'$ applied to $1$. The recurrences follow from the commutation relations of these
operators with multiplication by $x$. Orthogonality follows from $n$ integrations by parts on
$(0, \infty)$ or on $\mathbb{R}$, because $e^{-x} (f' - f) = (e^{-x} f)'$ and
$e^{-x^2} (2x f - f') = -(e^{-x^2} f)'$.

## Main definitions

* `OrthogonalPolynomial.chebyshevMeasure`: the Chebyshev weight $(1 - x^2)^{-1/2} \, dx$ on
  $(-1, 1)$.
* `OrthogonalPolynomial.jacobiMeasure`: the Jacobi weight $(1 - x)^\alpha (1 + x)^\beta \, dx$ on
  $(-1, 1)$.
* `OrthogonalPolynomial.laguerreMeasure`: the Laguerre weight $e^{-x} \, dx$ on $(0, \infty)$.
* `OrthogonalPolynomial.hermiteMeasure`: the Hermite weight $e^{-x^2} \, dx$ on $\mathbb{R}$.
* `Polynomial.laguerre`: the Laguerre polynomial $\mathcal{L}_n = e^x \frac{d^n}{dx^n} (e^{-x}
  x^n)$, defined by its three-term recurrence.
* `Polynomial.physHermite`: the physicists' Hermite polynomial
  $H_n = (-1)^n e^{x^2} \frac{d^n}{dx^n} e^{-x^2}$, defined by $H_{n+1} = 2x H_n - H_n'$.

## Main results

* `OrthogonalPolynomial.isWeight_chebyshevMeasure`, `OrthogonalPolynomial.isWeight_jacobiMeasure`
  (for $\alpha, \beta > -1$), `OrthogonalPolynomial.isWeight_laguerreMeasure`,
  `OrthogonalPolynomial.isWeight_hermiteMeasure`: the four classical weights are weights.
* `OrthogonalPolynomial.jacobiMeasure_zero_zero`,
  `OrthogonalPolynomial.jacobiMeasure_neg_half_neg_half`: the Legendre and the Chebyshev weights are
  the Jacobi weights with $\alpha = \beta = 0$ and $\alpha = \beta = -1/2$.
* `OrthogonalPolynomial.family_chebyshevMeasure_eq`,
  `OrthogonalPolynomial.family_laguerreMeasure_eq`, `OrthogonalPolynomial.family_hermiteMeasure_eq`:
  the monic orthogonal polynomials of the classical weights are the monic rescalings of $T_n$,
  $\mathcal{L}_n$ and $H_n$.
* `Polynomial.laguerre_eq_deriv_exp_mul`, `Polynomial.physHermite_eq_deriv_gaussian`: the Rodrigues
  formulas.
* `Polynomial.integral_laguerre_mul_laguerre`, `Polynomial.integral_physHermite_mul_physHermite`:
  the orthogonality relations, with the squared norms $(n!)^2$ and $2^n n! \sqrt\pi$.
* `OrthogonalPolynomial.alpha_beta_legendreMeasure`,
  `OrthogonalPolynomial.alpha_beta_laguerreMeasure`,
  `OrthogonalPolynomial.alpha_beta_hermiteMeasure`: the recurrence coefficients of the three
  weights, which [quarteroni2000numerical], §10.6 (Programs 82–84), tabulates. They are read off the
  classical recurrences by `OrthogonalPolynomial.alpha_succ_eq_and_beta_eq_of_recurrence`.

## Implementation notes

* `OrthogonalPolynomial.chebyshevMeasure` is Mathlib's `Polynomial.Chebyshev.measureT`, so that
  Mathlib's results on that measure apply unchanged.
* The Jacobi, Laguerre and Hermite weights are Lebesgue measure, restricted to the interval, with
  the density given by `ENNReal.ofReal`.
* `Polynomial.laguerre` is the unnormalized family of [quarteroni2000numerical], §10.5, with leading
  coefficient $(-1)^n$ and $\mathcal{L}_n(0) = n!$. It is $n!$ times the normalized Laguerre
  polynomial $L_n$ of most references, which is not used here.
* `Polynomial.physHermite` is defined in the same way as Mathlib defines the probabilists' Hermite
  polynomials `Polynomial.hermite`, by an operator recursion. The two families are related by
  $H_n(x) = 2^{n/2} He_n(\sqrt 2 \, x)$; this relation is not used.
-/

open MeasureTheory Polynomial Real Set Filter Topology

open scoped Nat

noncomputable section

namespace OrthogonalPolynomial

/-! ### Weights given by a density -/

/-- Let $\mu \neq 0$ be a measure on $\mathbb{R}$ that is absolutely continuous with respect to
Lebesgue measure, and such that $x \mapsto x^n$ is $\mu$-integrable for every $n$. Then $\mu$ is
a weight.

A finite set has Lebesgue measure zero, so $\mu$ gives no mass to it, and the complement of a
finite set has the full mass of $\mu$. -/
theorem isWeight_of_absolutelyContinuous {μ : Measure ℝ} (hac : μ ≪ volume) (hμ : μ ≠ 0)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) : IsWeight μ where
  integrable_pow := hint
  measure_compl_ne_zero {s} hs := by
    intro h
    have hs0 : μ s = 0 := hac (hs.measure_zero volume)
    have huniv : μ univ = 0 := by
      rw [← measure_add_measure_compl hs.measurableSet, hs0, h, add_zero]
    exact hμ (Measure.measure_univ_eq_zero.mp huniv)

/-- Let $\mu$ be a measure on $\mathbb{R}$, and let $f \colon \mathbb{R} \to \mathbb{R}$ satisfy
$\int f \, d\mu \neq 0$. Then $\mu \neq 0$. -/
theorem ne_zero_of_integral_ne_zero {μ : Measure ℝ} {f : ℝ → ℝ} (h : ∫ x, f x ∂μ ≠ 0) :
    μ ≠ 0 := fun h0 => h (by rw [h0, integral_zero_measure])

/-- Let $\nu$ be a measure on $\mathbb{R}$, and let $\rho$ be measurable with $\rho \ge 0$
$\nu$-almost everywhere. Then for every $f \colon \mathbb{R} \to \mathbb{R}$,
$$\int f \, d(\rho \, \nu) = \int \rho f \, d\nu,$$
where $\rho \, \nu$ is the measure with density $\rho$ with respect to $\nu$. -/
theorem integral_withDensity_ofReal {ν : Measure ℝ} {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    (hnn : ∀ᵐ x ∂ν, 0 ≤ ρ x) (f : ℝ → ℝ) :
    ∫ x, f x ∂(ν.withDensity fun x => ENNReal.ofReal (ρ x)) = ∫ x, ρ x * f x ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hnn] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

/-- Let $\nu$ be a measure on $\mathbb{R}$, and let $\rho$ be measurable with $\rho \ge 0$
$\nu$-almost everywhere. Then $f$ is integrable for the measure $\rho \, \nu$ with density
$\rho$ if and only if $\rho f$ is $\nu$-integrable. -/
theorem integrable_withDensity_ofReal_iff {ν : Measure ℝ} {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    (hnn : ∀ᵐ x ∂ν, 0 ≤ ρ x) (f : ℝ → ℝ) :
    Integrable f (ν.withDensity fun x => ENNReal.ofReal (ρ x)) ↔
      Integrable (fun x => ρ x * f x) ν := by
  rw [integrable_withDensity_iff hρ.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [hnn] with x hx
  rw [ENNReal.toReal_ofReal hx, mul_comm]

/-! ### The Chebyshev weight -/

/-- The **Chebyshev weight**: the measure $(1 - x^2)^{-1/2} \, dx$ on $(-1, 1)$. This is (10.9) of
[quarteroni2000numerical].

The measure is Mathlib's `Polynomial.Chebyshev.measureT`, so that
`Polynomial.Chebyshev.integral_measureT` and the orthogonality relations of the $T_n$ apply
unchanged. Mathlib restricts the density to $(-1, 1]$; the point $1$ has measure zero. -/
abbrev chebyshevMeasure : Measure ℝ := Polynomial.Chebyshev.measureT

/-- The Chebyshev weight is absolutely continuous with respect to Lebesgue measure. -/
theorem chebyshevMeasure_absolutelyContinuous : chebyshevMeasure ≪ volume :=
  (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
    (withDensity_absolutelyContinuous _ _)

/-- The Chebyshev weight has total mass $\int_{-1}^{1} (1 - x^2)^{-1/2} \, dx = \pi$. -/
theorem integral_one_chebyshevMeasure : ∫ _x, (1 : ℝ) ∂chebyshevMeasure = π := by
  have h := Polynomial.Chebyshev.integral_eval_T_real_measureT_zero
  simpa using h

/-- **The Chebyshev weight is a weight.** Continuous functions are integrable for it, and it is a
nonzero measure that is absolutely continuous with respect to Lebesgue measure. -/
theorem isWeight_chebyshevMeasure : IsWeight chebyshevMeasure :=
  isWeight_of_absolutelyContinuous chebyshevMeasure_absolutelyContinuous
    (ne_zero_of_integral_ne_zero (f := fun _ => (1 : ℝ))
      (by rw [integral_one_chebyshevMeasure]; exact pi_ne_zero))
    fun n => Polynomial.Chebyshev.integrable_measureT (by fun_prop)

/-- The Chebyshev weight gives no mass to $\mathbb{R} \setminus [-1, 1]$. -/
theorem chebyshevMeasure_compl_Icc : chebyshevMeasure (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [chebyshevMeasure, Chebyshev.measureT, Measure.restrict_apply' measurableSet_Ioc]
  have hempty : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioc (-1 : ℝ) 1 = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => ht.1 (Ioc_subset_Icc_self ht.2)
  rw [hempty, measure_empty]

/-- **The monic orthogonal polynomials of the Chebyshev weight are the monic rescalings of the
Chebyshev polynomials.** For every $n$,
$$p_n = 2^{-(n-1)} \, T_n,$$
where $n - 1$ is truncated subtraction, so that $p_0 = T_0 = 1$. This follows
[quarteroni2000numerical], §10.1.1. -/
theorem family_chebyshevMeasure_eq (n : ℕ) :
    family chebyshevMeasure n = C ((2 : ℝ) ^ (n - 1))⁻¹ * Polynomial.Chebyshev.T ℝ n := by
  have h := family_eq_of_orthogonal isWeight_chebyshevMeasure
    (q := fun n : ℕ => Polynomial.Chebyshev.T ℝ n)
    (fun n => by rw [Polynomial.Chebyshev.degree_T]; simp)
    (fun m n hmn =>
      Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne (Nat.ne_of_gt hmn))
    n
  rw [h, Polynomial.Chebyshev.leadingCoeff_T]
  simp

/-! ### The Jacobi weights -/

/-- The **Jacobi weight** with real exponents $\alpha$ and $\beta$: the measure
$$(1 - x)^\alpha (1 + x)^\beta \, dx$$
on $(-1, 1)$. This follows [quarteroni2000numerical], Remark 10.1. -/
def jacobiMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity fun x =>
    ENNReal.ofReal ((1 - x) ^ α * (1 + x) ^ β)

private theorem measurable_jacobiDensity (α β : ℝ) :
    Measurable fun x : ℝ => (1 - x) ^ α * (1 + x) ^ β := by fun_prop

private theorem jacobiDensity_nonneg (α β : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), 0 ≤ (1 - x) ^ α * (1 + x) ^ β := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun x hx => ?_
  exact mul_nonneg (rpow_nonneg (by linarith [hx.2]) _) (rpow_nonneg (by linarith [hx.1]) _)

/-- For every $f \colon \mathbb{R} \to \mathbb{R}$, the integral against the Jacobi weight is
$$\int f \, d\mu_{\alpha,\beta} = \int_{(-1, 1)} (1 - x)^\alpha (1 + x)^\beta f(x) \, dx.$$
-/
theorem integral_jacobiMeasure (α β : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂jacobiMeasure α β = ∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β * f x :=
  integral_withDensity_ofReal (measurable_jacobiDensity α β) (jacobiDensity_nonneg α β) f

/-- A function $f$ is integrable for the Jacobi weight if and only if
$(1 - x)^\alpha (1 + x)^\beta f(x)$ is integrable on $(-1, 1)$. -/
theorem integrable_jacobiMeasure_iff (α β : ℝ) (f : ℝ → ℝ) :
    Integrable f (jacobiMeasure α β) ↔
      IntegrableOn (fun x => (1 - x) ^ α * (1 + x) ^ β * f x) (Ioo (-1 : ℝ) 1) :=
  integrable_withDensity_ofReal_iff (measurable_jacobiDensity α β) (jacobiDensity_nonneg α β) f

/-- Let $\alpha, \beta > -1$, and let $g$ be continuous. Then $(1 - x)^\alpha (1 + x)^\beta g(x)$ is
integrable on $(-1, 1)$.

The proof splits the interval at $0$. On each half one factor is continuous, and the other is a
power $t^r$ with $r > -1$, which is integrable at its endpoint. -/
theorem integrableOn_jacobiDensity_mul {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {g : ℝ → ℝ}
    (hg : Continuous g) :
    IntegrableOn (fun x => (1 - x) ^ α * (1 + x) ^ β * g x) (Ioo (-1 : ℝ) 1) := by
  have hleft : IntervalIntegrable (fun x : ℝ => (1 + x) ^ β) volume (-1) 0 := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hβ).comp_add_right 1
    simp only [zero_sub, sub_self] at h
    have heq : (fun x : ℝ => (1 + x) ^ β) = fun x => (x + 1) ^ β := by
      funext x
      rw [add_comm]
    rw [heq]
    exact h
  have hright : IntervalIntegrable (fun x : ℝ => (1 - x) ^ α) volume 0 1 := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hα).comp_sub_left 1
    simp only [sub_zero, sub_self] at h
    exact h.symm
  have h1 : IntervalIntegrable (fun x => (1 - x) ^ α * (1 + x) ^ β * g x) volume (-1) 0 := by
    have hc : ContinuousOn (fun x : ℝ => (1 - x) ^ α * g x) (uIcc (-1) 0) := by
      refine ContinuousOn.mul (ContinuousOn.rpow_const (by fun_prop) fun x hx => ?_)
        hg.continuousOn
      rw [uIcc_of_le (by norm_num)] at hx
      exact Or.inl (by linarith [hx.2])
    refine (hleft.continuousOn_mul hc).congr fun x _ => ?_
    ring
  have h2 : IntervalIntegrable (fun x => (1 - x) ^ α * (1 + x) ^ β * g x) volume 0 1 := by
    have hc : ContinuousOn (fun x : ℝ => (1 + x) ^ β * g x) (uIcc 0 1) := by
      refine ContinuousOn.mul (ContinuousOn.rpow_const (by fun_prop) fun x hx => ?_)
        hg.continuousOn
      rw [uIcc_of_le (by norm_num)] at hx
      exact Or.inl (by linarith [hx.1])
    refine (hright.mul_continuousOn hc).congr fun x _ => ?_
    ring
  have h := h1.trans h2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
  exact h.mono_set Ioo_subset_Ioc_self

/-- **The Jacobi weights are weights** for $\alpha, \beta > -1$. This follows
[quarteroni2000numerical], Remark 10.1.

The moments are finite because the density is integrable near each endpoint, and the density is
positive on $(-1, 1)$. -/
theorem isWeight_jacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IsWeight (jacobiMeasure α β) := by
  refine isWeight_of_absolutelyContinuous ((withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)) ?_ fun n => ?_
  · intro h0
    have h := congrArg (fun μ : Measure ℝ => μ univ) h0
    simp only [jacobiMeasure, Measure.coe_zero, Pi.zero_apply] at h
    rw [withDensity_apply_eq_zero' (measurable_jacobiDensity α β).ennreal_ofReal.aemeasurable,
      inter_univ, Measure.restrict_apply' measurableSet_Ioo] at h
    have hsub : Ioo (-1 : ℝ) 1 ⊆ {x | ENNReal.ofReal ((1 - x) ^ α * (1 + x) ^ β) ≠ 0} ∩
        Ioo (-1) 1 := by
      intro x hx
      refine ⟨fun h0 => ?_, hx⟩
      have hpos : 0 < (1 - x) ^ α * (1 + x) ^ β :=
        mul_pos (rpow_pos_of_pos (by linarith [hx.2]) _) (rpow_pos_of_pos (by linarith [hx.1]) _)
      exact absurd (ENNReal.ofReal_eq_zero.mp h0) (not_le.mpr hpos)
    have := measure_mono_null hsub h
    rw [Real.volume_Ioo] at this
    norm_num at this
  · rw [integrable_jacobiMeasure_iff]
    exact integrableOn_jacobiDensity_mul hα hβ (continuous_pow n)

/-- For all real $\alpha$ and $\beta$, the Jacobi weight gives no mass to
$\mathbb{R} \setminus [-1, 1]$. -/
theorem jacobiMeasure_compl_Icc (α β : ℝ) : jacobiMeasure α β (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply' measurableSet_Ioo]
  have hempty : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioo (-1 : ℝ) 1 = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => ht.1 (Ioo_subset_Icc_self ht.2)
  rw [hempty, measure_empty]

/-- The Jacobi weight with $\alpha = \beta = 0$ is the Legendre weight
`OrthogonalPolynomial.legendreMeasure`. This is stated in [quarteroni2000numerical], Remark
10.1. -/
theorem jacobiMeasure_zero_zero : jacobiMeasure 0 0 = legendreMeasure := by
  rw [jacobiMeasure]
  simp only [rpow_zero, mul_one, ENNReal.ofReal_one]
  exact withDensity_one

/-- The Jacobi weight with $\alpha = \beta = -1/2$ is the Chebyshev weight. This is stated in
[quarteroni2000numerical], Remark 10.1.

On $(-1, 1)$ both densities are $(1 - x^2)^{-1/2}$. Mathlib's measure is restricted to
$(-1, 1]$, and its density at the point $1$ is $0$, because `Real.sqrt 0` is $0$ and the inverse
of $0$ is $0$. -/
theorem jacobiMeasure_neg_half_neg_half : jacobiMeasure (-1 / 2) (-1 / 2) = chebyshevMeasure := by
  rw [jacobiMeasure]
  unfold chebyshevMeasure Polynomial.Chebyshev.measureT
  rw [restrict_withDensity measurableSet_Ioc, restrict_Ioo_eq_restrict_Ioc]
  refine withDensity_congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun x hx => ?_
  have h1 : 0 ≤ 1 - x := by linarith [hx.2]
  have h2 : 0 ≤ 1 + x := by linarith [hx.1]
  have hsq : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hval : (1 - x) ^ (-1 / 2 : ℝ) * (1 + x) ^ (-1 / 2 : ℝ) = (√(1 - x ^ 2))⁻¹ := by
    rw [← mul_rpow h1 h2, show (1 - x) * (1 + x) = 1 - x ^ 2 by ring, sqrt_eq_rpow,
      ← rpow_neg hsq]
    norm_num
  rw [hval, ENNReal.ofReal_eq_coe_nnreal (by positivity)]
  congr 1
  ext
  simp [Real.sqrt_inv]

/-! ### The Laguerre polynomials -/

end OrthogonalPolynomial

namespace Polynomial

/-- The **Laguerre polynomials** $\mathcal{L}_n = e^x \frac{d^n}{dx^n} (e^{-x} x^n)$, defined by
their three-term recurrence:
$$\mathcal{L}_0 = 1, \qquad \mathcal{L}_1 = 1 - x, \qquad \mathcal{L}_{n+2} = (2n + 3 - x) \,
  \mathcal{L}_{n+1} - (n + 1)^2 \, \mathcal{L}_n.$$
This is the unnormalized family of [quarteroni2000numerical], §10.5.

The polynomial $\mathcal{L}_n$ has leading coefficient $(-1)^n$, and $\mathcal{L}_n(0) = n!$.
The normalized polynomial $L_n = \mathcal{L}_n / n!$ of most references is not used. Rodrigues'
formula is `Polynomial.laguerre_eq_deriv_exp_mul`. -/
def laguerre : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 - X
  | (n + 2) => (C (2 * (n : ℝ) + 3) - X) * laguerre (n + 1) - C (((n : ℝ) + 1) ^ 2) * laguerre n

/-- The zeroth Laguerre polynomial is $\mathcal{L}_0 = 1$. -/
@[simp]
theorem laguerre_zero : laguerre 0 = 1 := rfl

/-- The first Laguerre polynomial is $\mathcal{L}_1 = 1 - x$. -/
@[simp]
theorem laguerre_one : laguerre 1 = 1 - X := rfl

/-- The **three-term recurrence** of the Laguerre polynomials: for every $n$,
$$\mathcal{L}_{n+2} = (2n + 3 - x) \, \mathcal{L}_{n+1} - (n + 1)^2 \, \mathcal{L}_n.$$
This is the recurrence of [quarteroni2000numerical], §10.5. -/
theorem laguerre_succ_succ (n : ℕ) :
    laguerre (n + 2) =
      (C (2 * (n : ℝ) + 3) - X) * laguerre (n + 1) - C (((n : ℝ) + 1) ^ 2) * laguerre n := rfl

/-- For every $n$, the polynomials $\mathcal{L}_n$ and $\mathcal{L}_{n+1}$ have the degrees $n$ and
$n + 1$ and the leading coefficients $(-1)^n$ and $(-1)^{n+1}$. -/
private theorem degree_leadingCoeff_laguerre_aux (n : ℕ) :
    ((laguerre n).degree = n ∧ (laguerre n).leadingCoeff = (-1) ^ n) ∧
      ((laguerre (n + 1)).degree = (n + 1 : ℕ) ∧
        (laguerre (n + 1)).leadingCoeff = (-1) ^ (n + 1)) := by
  induction n with
  | zero =>
    refine ⟨⟨by simp, by simp⟩, ?_⟩
    have h : laguerre 1 = -(X - C 1) := by rw [laguerre_one, C_1]; ring
    rw [h, degree_neg, degree_X_sub_C, leadingCoeff_neg, leadingCoeff_X_sub_C]
    simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨⟨hd0, hl0⟩, ⟨hd1, hl1⟩⟩ := ih
    have hfac : (C (2 * (n : ℝ) + 3) - X : ℝ[X]) = -(X - C (2 * (n : ℝ) + 3)) := by ring
    have hdeg1 : ((C (2 * (n : ℝ) + 3) - X) * laguerre (n + 1)).degree =
        ((n + 2 : ℕ) : WithBot ℕ) := by
      rw [hfac, neg_mul, degree_neg, degree_mul, degree_X_sub_C, hd1]
      norm_cast
      omega
    have hlc1 : ((C (2 * (n : ℝ) + 3) - X) * laguerre (n + 1)).leadingCoeff = (-1) ^ (n + 2) := by
      rw [hfac, neg_mul, leadingCoeff_neg, leadingCoeff_mul, leadingCoeff_X_sub_C, hl1, one_mul,
        pow_succ]
      ring
    have hdeg0 : (C (((n : ℝ) + 1) ^ 2) * laguerre n).degree < ((n + 2 : ℕ) : WithBot ℕ) := by
      refine (degree_mul_le _ _).trans_lt ?_
      rw [hd0]
      calc (C (((n : ℝ) + 1) ^ 2) : ℝ[X]).degree + (n : WithBot ℕ) ≤ 0 + (n : WithBot ℕ) := by
            gcongr; exact degree_C_le
        _ = (n : WithBot ℕ) := zero_add _
        _ < ((n + 2 : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : n < n + 2)
    rw [show n + 1 + 1 = n + 2 from rfl, laguerre_succ_succ]
    rw [← hdeg1] at hdeg0
    refine ⟨?_, ?_⟩
    · rw [degree_sub_eq_left_of_degree_lt hdeg0, hdeg1]
    · rw [leadingCoeff_sub_of_degree_lt hdeg0, hlc1]

/-- For every $n$, the Laguerre polynomial $\mathcal{L}_n$ has degree $n$. -/
@[simp]
theorem degree_laguerre (n : ℕ) : (laguerre n).degree = n :=
  (degree_leadingCoeff_laguerre_aux n).1.1

/-- For every $n$, the Laguerre polynomial $\mathcal{L}_n$ has leading coefficient $(-1)^n$. -/
@[simp]
theorem leadingCoeff_laguerre (n : ℕ) : (laguerre n).leadingCoeff = (-1) ^ n :=
  (degree_leadingCoeff_laguerre_aux n).1.2

/-- For every $n$, the Laguerre polynomial $\mathcal{L}_n$ has natural degree $n$. -/
theorem natDegree_laguerre (n : ℕ) : (laguerre n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_laguerre n)

/-- For every $n$, the Laguerre polynomial $\mathcal{L}_n$ is nonzero. -/
theorem laguerre_ne_zero (n : ℕ) : laguerre n ≠ 0 := fun h => by
  have := degree_laguerre n
  rw [h, degree_zero] at this
  exact absurd this (by simp)

/-!
### The algebraic Rodrigues formula for the Laguerre polynomials

On polynomials, the operator $T f = f' - f$ is $e^x \frac{d}{dx} e^{-x}$, so $\mathcal{L}_n$ is the
$n$-th iterate of $T$ applied to $x^n$. The three-term recurrence follows from the commutation
relation of $T$ with multiplication by $x$.
-/

/-- The operator $T f = f' - f$ on polynomials. -/
private def lagT (f : ℝ[X]) : ℝ[X] := derivative f - f

private theorem lagT_add (f g : ℝ[X]) : lagT (f + g) = lagT f + lagT g := by
  simp only [lagT, derivative_add]; ring

private theorem lagT_C_mul (c : ℝ) (f : ℝ[X]) : lagT (C c * f) = C c * lagT f := by
  simp only [lagT, derivative_C_mul]; ring

private theorem lagT_X_mul (f : ℝ[X]) : lagT (X * f) = X * lagT f + f := by
  simp only [lagT, derivative_mul, derivative_X]; ring

private theorem iterate_lagT_add (k : ℕ) (f g : ℝ[X]) :
    lagT^[k] (f + g) = lagT^[k] f + lagT^[k] g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, lagT_add, ih]

private theorem iterate_lagT_C_mul (k : ℕ) (c : ℝ) (f : ℝ[X]) :
    lagT^[k] (C c * f) = C c * lagT^[k] f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, lagT_C_mul, ih]

/-- The commutation relation $T^{k+1} (x f) = x \, T^{k+1} f + (k + 1) \, T^k f$. -/
private theorem iterate_lagT_X_mul (k : ℕ) (f : ℝ[X]) :
    lagT^[k + 1] (X * f) = X * lagT^[k + 1] f + C ((k : ℝ) + 1) * lagT^[k] f := by
  induction k with
  | zero => simp [lagT_X_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply' lagT (k + 1), ih, lagT_add, lagT_X_mul, lagT_C_mul,
      ← Function.iterate_succ_apply' lagT (k + 1), ← Function.iterate_succ_apply' lagT k]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring

/-- The derivative commutes with every iterate of $T$: $(T^k f)' = T^k (f')$. -/
private theorem derivative_iterate_lagT (k : ℕ) (f : ℝ[X]) :
    derivative (lagT^[k] f) = lagT^[k] (derivative f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    simp only [lagT, derivative_sub]

/-- The iterates $R_n = T^n x^n$ satisfy $R_{n+1} = x (R_n' - R_n) + (n + 1) R_n$. -/
private theorem iterate_lagT_succ_eq (n : ℕ) :
    lagT^[n + 1] (X ^ (n + 1)) =
      X * (derivative (lagT^[n] (X ^ n)) - lagT^[n] (X ^ n)) +
        C ((n : ℝ) + 1) * lagT^[n] (X ^ n) := by
  rw [pow_succ', iterate_lagT_X_mul, Function.iterate_succ_apply']
  rfl

/-- The iterates $R_n = T^n x^n$ satisfy $R_{n+1}' = (n + 1)(R_n' - R_n)$. -/
private theorem derivative_iterate_lagT_succ (n : ℕ) :
    derivative (lagT^[n + 1] (X ^ (n + 1))) =
      C ((n : ℝ) + 1) * (derivative (lagT^[n] (X ^ n)) - lagT^[n] (X ^ n)) := by
  rw [derivative_iterate_lagT, derivative_X_pow, Nat.add_sub_cancel, iterate_lagT_C_mul,
    Function.iterate_succ_apply']
  push_cast
  rfl

/-- The algebraic Rodrigues formula: $\mathcal{L}_n = T^n x^n$, where $T f = f' - f$. -/
private theorem laguerre_eq_iterate_lagT (n : ℕ) : laguerre n = lagT^[n] (X ^ n) := by
  set R : ℕ → ℝ[X] := fun n => lagT^[n] (X ^ n) with hR
  have hA : ∀ n, R (n + 1) = X * (derivative (R n) - R n) + C ((n : ℝ) + 1) * R n :=
    iterate_lagT_succ_eq
  have hB : ∀ n, derivative (R (n + 1)) = C ((n : ℝ) + 1) * (derivative (R n) - R n) :=
    derivative_iterate_lagT_succ
  have hrec : ∀ n, R (n + 2) =
      (C (2 * (n : ℝ) + 3) - X) * R (n + 1) - C (((n : ℝ) + 1) ^ 2) * R n := by
    intro n
    have h1 := hA (n + 1)
    have h2 := hB n
    have h0 := hA n
    push_cast at h1
    simp only [map_add, map_mul, map_natCast, map_one, map_ofNat, map_pow] at h1 h2 h0 ⊢
    linear_combination h1 + X * h2 - ((n : ℝ[X]) + 1) * h0
  suffices h : ∀ n, laguerre n = R n ∧ laguerre (n + 1) = R (n + 1) from (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [hR], ?_⟩
    rw [laguerre_one, hA 0]
    simp [hR]
    ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, laguerre_succ_succ, hrec, ih.1, ih.2]

/-- For every $n$, the Laguerre polynomials satisfy $\mathcal{L}_{n+1} = x (\mathcal{L}_n' -
\mathcal{L}_n) + (n + 1) \mathcal{L}_n$. -/
theorem laguerre_succ_eq (n : ℕ) :
    laguerre (n + 1) =
      X * (derivative (laguerre n) - laguerre n) + C ((n : ℝ) + 1) * laguerre n := by
  rw [laguerre_eq_iterate_lagT, laguerre_eq_iterate_lagT]
  exact iterate_lagT_succ_eq n

/-- For every $n$, the Laguerre polynomials satisfy $\mathcal{L}_{n+1}' = (n + 1)(\mathcal{L}_n' -
\mathcal{L}_n)$. -/
theorem derivative_laguerre_succ (n : ℕ) :
    derivative (laguerre (n + 1)) = C ((n : ℝ) + 1) * (derivative (laguerre n) - laguerre n) := by
  rw [laguerre_eq_iterate_lagT, laguerre_eq_iterate_lagT]
  exact derivative_iterate_lagT_succ n

/-- For every $n$, the Laguerre polynomials satisfy
$$x \, \mathcal{L}_{n+1}' = (n + 1) \, \mathcal{L}_{n+1} - (n + 1)^2 \, \mathcal{L}_n.$$
This is the identity that gives the weights of the Gauss–Laguerre rule. -/
theorem X_mul_derivative_laguerre_succ (n : ℕ) :
    X * derivative (laguerre (n + 1)) =
      C ((n : ℝ) + 1) * laguerre (n + 1) - C (((n : ℝ) + 1) ^ 2) * laguerre n := by
  have h1 := laguerre_succ_eq n
  have h2 := derivative_laguerre_succ n
  rw [h2]
  simp only [map_pow]
  linear_combination -(C ((n : ℝ) + 1)) * h1

/-- For every $n$, the Laguerre polynomial satisfies $\mathcal{L}_n(0) = n!$. -/
theorem laguerre_eval_zero (n : ℕ) : (laguerre n).eval 0 = n ! := by
  suffices h : ∀ n, (laguerre n).eval 0 = n ! ∧ (laguerre (n + 1)).eval 0 = (n + 1) ! from (h n).1
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, laguerre_succ_succ]
    simp only [eval_sub, eval_mul, eval_C, eval_X, ih.1, ih.2, Nat.factorial_succ]
    push_cast
    ring

/-- For $k \le n$, the polynomial $x^{n-k}$ divides $T^k x^n$, because $T$ lowers by at most one the
power of $x$ that divides a polynomial. -/
private theorem X_pow_dvd_iterate_lagT (n k : ℕ) (hk : k ≤ n) :
    X ^ (n - k) ∣ lagT^[k] (X ^ n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih (by omega)
    have hm : n - k = n - (k + 1) + 1 := by omega
    rw [Function.iterate_succ_apply', hg, hm]
    simp only [lagT, derivative_mul, derivative_X_pow, Nat.add_sub_cancel]
    exact dvd_sub (dvd_add ⟨C ((n - (k + 1) + 1 : ℕ) : ℝ) * g, by ring⟩
      ⟨X * derivative g, by ring⟩) ⟨X * g, by ring⟩

private theorem eval_zero_iterate_lagT (n k : ℕ) (hk : k < n) :
    (lagT^[k] (X ^ n)).eval 0 = 0 := by
  obtain ⟨g, hg⟩ := X_pow_dvd_iterate_lagT n k hk.le
  rw [hg, eval_mul, eval_pow, eval_X, zero_pow (by omega), zero_mul]

/-! ### The analytic Rodrigues formula for the Laguerre polynomials -/

/-- For a polynomial $f$, the derivative of $e^{-x} f(x)$ is $e^{-x} (T f)(x)$. -/
private theorem hasDerivAt_exp_neg_mul_eval (f : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => exp (-y) * f.eval y) (exp (-x) * (lagT f).eval x) x := by
  have h1 : HasDerivAt (fun y : ℝ => exp (-y)) (exp (-x) * (-1)) x :=
    (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have h2 := f.hasDerivAt x
  refine (h1.mul h2).congr_deriv ?_
  simp only [lagT, eval_sub]
  ring

private theorem iterate_deriv_exp_neg_mul_eval (k : ℕ) (f : ℝ[X]) :
    deriv^[k] (fun y => exp (-y) * f.eval y) = fun y => exp (-y) * (lagT^[k] f).eval y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext y
    exact (hasDerivAt_exp_neg_mul_eval _ y).deriv

/-- **Rodrigues' formula for the Laguerre polynomials**: for every $n$ and every $x \in \mathbb{R}$,
$$\mathcal{L}_n(x) = e^x \, \frac{d^n}{dx^n} \bigl(e^{-x} x^n\bigr).$$
This is the formula of [quarteroni2000numerical], §10.5. -/
theorem laguerre_eq_deriv_exp_mul (n : ℕ) (x : ℝ) :
    (laguerre n).eval x = exp x * deriv^[n] (fun y => exp (-y) * y ^ n) x := by
  have h := congrFun (iterate_deriv_exp_neg_mul_eval n (X ^ n)) x
  simp only [eval_pow, eval_X] at h
  rw [h, ← laguerre_eq_iterate_lagT, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-! ### Orthogonality of the Laguerre polynomials -/

/-- One integration by parts on $(0, \infty)$: for polynomials $p$ and $q$ with $q(0) = 0$,
$\int_0^\infty p \, e^{-x} \, T q \, dx = -\int_0^\infty p' \, e^{-x} q \, dx$. -/
private theorem integral_eval_mul_exp_neg_mul_lagT {p q : ℝ[X]} (hq : q.eval 0 = 0) :
    ∫ x in Ioi (0 : ℝ), p.eval x * (exp (-x) * (lagT q).eval x) =
      -∫ x in Ioi (0 : ℝ), (derivative p).eval x * (exp (-x) * q.eval x) := by
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y => p.eval y) ((derivative p).eval x) x :=
    fun x _ => p.hasDerivAt x
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y => exp (-y) * q.eval y)
      (exp (-x) * (lagT q).eval x) x := fun x _ => hasDerivAt_exp_neg_mul_eval q x
  have hint1 : IntegrableOn (fun x => p.eval x * (exp (-x) * (lagT q).eval x)) (Ioi 0) := by
    refine (integrableOn_eval_mul_exp_neg (p * lagT q)).congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [eval_mul]
    ring
  have hint2 : IntegrableOn (fun x => (derivative p).eval x * (exp (-x) * q.eval x)) (Ioi 0) := by
    refine (integrableOn_eval_mul_exp_neg (derivative p * q)).congr_fun (fun x _ => ?_)
      measurableSet_Ioi
    simp only [eval_mul]
    ring
  have hzero : Tendsto ((fun y => p.eval y) * fun y => exp (-y) * q.eval y) (𝓝[>] 0)
      (𝓝 (p.eval 0 * (exp (-0) * q.eval 0))) := by
    refine ((p.continuous.mul (continuous_neg.rexp.mul q.continuous)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hinfty : Tendsto ((fun y => p.eval y) * fun y => exp (-y) * q.eval y) atTop (𝓝 0) := by
    refine (p * q).tendsto_div_exp_atTop.congr fun x => ?_
    simp only [Pi.mul_apply, eval_mul, div_eq_mul_inv, ← Real.exp_neg]
    ring
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hint1 hint2 hzero hinfty
  rw [h, hq]
  simp

/-- For $k \le n$ and every polynomial $p$, $\int_0^\infty p \, e^{-x} \, T^k x^n \, dx = (-1)^k
\int_0^\infty p^{(k)} e^{-x} x^n \, dx$, by $k$ integrations by parts. -/
private theorem integral_eval_mul_exp_neg_mul_iterate_lagT (p : ℝ[X]) (n : ℕ) :
    ∀ k ≤ n, ∫ x in Ioi (0 : ℝ), p.eval x * (exp (-x) * (lagT^[k] (X ^ n)).eval x) =
      (-1) ^ k * ∫ x in Ioi (0 : ℝ), (derivative^[k] p).eval x * (exp (-x) * x ^ n) := by
  intro k
  induction k generalizing p with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hk
    rw [Function.iterate_succ_apply',
      integral_eval_mul_exp_neg_mul_lagT (eval_zero_iterate_lagT n k (by omega)),
      ih (derivative p) (by omega), Function.iterate_succ_apply, pow_succ]
    ring

/-- For every $n$, the Gamma integral at $n + 1$ is
$$\int_0^\infty e^{-x} x^n \, dx = n!.$$
-/
theorem integral_exp_neg_mul_pow (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), exp (-x) * x ^ n = n ! := by
  have h := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [add_sub_cancel_right, rpow_natCast]

/-- For every polynomial $p$, $\int_0^\infty p \, \mathcal{L}_n \, e^{-x} \, dx = (-1)^n
\int_0^\infty p^{(n)} e^{-x} x^n \, dx$. -/
private theorem integral_eval_mul_laguerre_mul_exp_neg (p : ℝ[X]) (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), p.eval x * (laguerre n).eval x * exp (-x) =
      (-1) ^ n * ∫ x in Ioi (0 : ℝ), (derivative^[n] p).eval x * (exp (-x) * x ^ n) := by
  rw [← integral_eval_mul_exp_neg_mul_iterate_lagT p n n le_rfl, ← laguerre_eq_iterate_lagT]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- **Orthogonality of the Laguerre polynomials** on $(0, \infty)$ for the weight $e^{-x}$: for all
$n$ and $m$,
$$\int_0^\infty \mathcal{L}_n(x) \, \mathcal{L}_m(x) \, e^{-x} \, dx = \begin{cases} (n!)^2 &
  \text{if } n = m, \\ 0 & \text{if } n \neq m. \end{cases}$$
This follows [quarteroni2000numerical], §10.5.

After $n$ integrations by parts, $\int_0^\infty \mathcal{L}_m \mathcal{L}_n e^{-x} \, dx =
(-1)^n \int_0^\infty \mathcal{L}_m^{(n)} e^{-x} x^n \, dx$. This vanishes for $m < n$, and for
$m = n$ it is $(-1)^n \, n! \, (-1)^n \int_0^\infty x^n e^{-x} \, dx = (n!)^2$. -/
theorem integral_laguerre_mul_laguerre (n m : ℕ) :
    ∫ x in Ioi (0 : ℝ), (laguerre n).eval x * (laguerre m).eval x * exp (-x) =
      if n = m then ((n ! : ℝ)) ^ 2 else 0 := by
  -- the case `m < n` through the derivative of `ℒ_m`
  have hlt : ∀ m n : ℕ, m < n →
      ∫ x in Ioi (0 : ℝ), (laguerre m).eval x * (laguerre n).eval x * exp (-x) = 0 := by
    intro m n hmn
    rw [integral_eval_mul_laguerre_mul_exp_neg,
      iterate_derivative_eq_zero (by rw [natDegree_laguerre]; exact hmn)]
    simp
  split_ifs with h
  · subst h
    rw [integral_eval_mul_laguerre_mul_exp_neg, iterate_derivative_eq_C_of_natDegree_eq
      (natDegree_laguerre n), leadingCoeff_laguerre]
    simp only [eval_C]
    rw [integral_const_mul, integral_exp_neg_mul_pow n]
    have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      simp
    linear_combination ((n ! : ℝ)) ^ 2 * hsq
  · rcases lt_or_gt_of_ne h with hnm | hnm
    · exact hlt n m hnm
    · exact (setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring).trans (hlt m n hnm)

end Polynomial

namespace OrthogonalPolynomial

/-! ### The Laguerre weight -/

/-- The **Laguerre weight**: the measure $e^{-x} \, dx$ on $(0, \infty)$. This follows
[quarteroni2000numerical], §10.5. -/
def laguerreMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun x => ENNReal.ofReal (exp (-x))

/-- For every $f \colon \mathbb{R} \to \mathbb{R}$, the integral against the Laguerre weight is
$\int_0^\infty e^{-x} f(x) \, dx$. -/
theorem integral_laguerreMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂laguerreMeasure = ∫ x in Ioi (0 : ℝ), exp (-x) * f x :=
  integral_withDensity_ofReal (by fun_prop) (Eventually.of_forall fun x => (exp_pos _).le) f

/-- A function $f$ is integrable for the Laguerre weight if and only if $e^{-x} f(x)$ is integrable
on $(0, \infty)$. -/
theorem integrable_laguerreMeasure_iff (f : ℝ → ℝ) :
    Integrable f laguerreMeasure ↔ IntegrableOn (fun x => exp (-x) * f x) (Ioi 0) :=
  integrable_withDensity_ofReal_iff (by fun_prop) (Eventually.of_forall fun x => (exp_pos _).le) f

/-- The Laguerre weight has total mass $1$: $\|p_0\|^2 = \int_0^\infty e^{-x} \, dx = 1$. -/
theorem normSq_laguerreMeasure_zero : normSq laguerreMeasure 0 = 1 := by
  rw [normSq, family_zero, integral_laguerreMeasure]
  have h := Polynomial.integral_exp_neg_mul_pow 0
  simpa using h

/-- **The Laguerre weight is a weight.** This follows [quarteroni2000numerical], §10.5.

Its moments are the Gamma integrals $n!$, and it is a nonzero measure that is absolutely
continuous with respect to Lebesgue measure. -/
theorem isWeight_laguerreMeasure : IsWeight laguerreMeasure := by
  refine isWeight_of_absolutelyContinuous ((withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
    (ne_zero_of_integral_ne_zero (f := fun _ => (1 : ℝ)) ?_) fun n => ?_
  · have h := normSq_laguerreMeasure_zero
    rw [normSq, family_zero] at h
    simpa using h.trans_ne one_ne_zero
  · rw [integrable_laguerreMeasure_iff]
    refine (Polynomial.integrableOn_eval_mul_exp_neg (X ^ n)).congr_fun (fun x _ => ?_)
      measurableSet_Ioi
    simp only [eval_pow, eval_X]
    ring

/-- The Laguerre weight gives no mass to $\mathbb{R} \setminus (0, \infty)$, because it has a
density with respect to Lebesgue measure restricted to $(0, \infty)$. -/
theorem laguerreMeasure_compl_Ioi : laguerreMeasure (Ioi (0 : ℝ))ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply' measurableSet_Ioi, Set.compl_inter_self, measure_empty]

/-- For the Laguerre weight, almost every point $t$ satisfies $t \ge 0$. -/
theorem laguerreMeasure_ae_nonneg : ∀ᵐ t ∂laguerreMeasure, (0 : ℝ) ≤ t := by
  have h : ∀ᵐ t ∂laguerreMeasure, t ∈ Ioi (0 : ℝ) := by
    rw [MeasureTheory.ae_iff]; exact laguerreMeasure_compl_Ioi
  filter_upwards [h] with t ht using le_of_lt ht

/-- **The monic orthogonal polynomials of the Laguerre weight** are $p_n = (-1)^n \mathcal{L}_n$ for
every $n$. Hence the nodes of the Gauss–Laguerre rule are the zeros of $\mathcal{L}_n$. This is
(10.41) of [quarteroni2000numerical]. -/
theorem family_laguerreMeasure_eq (n : ℕ) :
    family laguerreMeasure n = C ((-1 : ℝ) ^ n) * Polynomial.laguerre n := by
  have h := family_eq_of_orthogonal isWeight_laguerreMeasure (q := Polynomial.laguerre)
    Polynomial.degree_laguerre
    (fun m n hmn => by
      rw [integral_laguerreMeasure]
      have := Polynomial.integral_laguerre_mul_laguerre n m
      rw [ite_eq_right (Nat.ne_of_gt hmn)] at this
      exact (setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring).trans this) n
  rw [h, Polynomial.leadingCoeff_laguerre, ← inv_pow, inv_neg, inv_one]

/-- For every $n$, the squared norm of the $n$-th monic orthogonal polynomial of the Laguerre weight
is $\|p_n\|^2 = (n!)^2$. -/
theorem normSq_laguerreMeasure (n : ℕ) : normSq laguerreMeasure n = ((n ! : ℝ)) ^ 2 := by
  rw [normSq_eq_of_family_eq (family_laguerreMeasure_eq n), integral_laguerreMeasure]
  have h := Polynomial.integral_laguerre_mul_laguerre n n
  rw [ite_eq_left rfl] at h
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  rw [hsq, one_mul, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- The monic three-term recurrence of the Laguerre weight: for every $n$,
$$p_{n+2} = (x - (2n + 3)) \, p_{n+1} - (n + 1)^2 \, p_n.$$
It follows from `Polynomial.laguerre_succ_succ` and the leading coefficients $(-1)^n$. -/
theorem family_laguerreMeasure_recurrence (n : ℕ) :
    family laguerreMeasure (n + 2) = (X - C (2 * (n : ℝ) + 3)) * family laguerreMeasure (n + 1) -
      C (((n : ℝ) + 1) ^ 2) * family laguerreMeasure n := by
  rw [family_laguerreMeasure_eq, family_laguerreMeasure_eq, family_laguerreMeasure_eq,
    Polynomial.laguerre_succ_succ]
  simp only [map_pow, map_neg, map_one]
  ring

/-- The recurrence coefficients $\alpha_k$ of the Laguerre weight are $\alpha_k = 2k + 1$ for every
$k$. This is Program 83 of [quarteroni2000numerical], §10.6. -/
theorem alpha_laguerreMeasure (k : ℕ) : alpha laguerreMeasure k = 2 * k + 1 := by
  cases k with
  | zero =>
    refine alpha_zero_eq_of_family_one ?_
    rw [family_laguerreMeasure_eq, Polynomial.laguerre_one]
    simp only [pow_one, map_neg, map_one, Nat.cast_zero, mul_zero, zero_add]
    ring
  | succ k =>
    rw [(alpha_succ_eq_and_beta_eq_of_recurrence isWeight_laguerreMeasure
      (family_laguerreMeasure_recurrence k)).1]
    push_cast
    ring

/-- The recurrence coefficients $\beta_k$ of the Laguerre weight are $\beta_k = (k + 1)^2$ for every
$k$. This is Program 83 of [quarteroni2000numerical], §10.6. -/
theorem beta_laguerreMeasure (k : ℕ) : beta laguerreMeasure k = ((k : ℝ) + 1) ^ 2 :=
  (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_laguerreMeasure
    (family_laguerreMeasure_recurrence k)).2

/-- **The recurrence coefficients of the Laguerre weight**: for every $k$,
$$\alpha_k = 2k + 1, \qquad \beta_k = (k + 1)^2,$$
and the total mass is $\|p_0\|^2 = 1$. This is Program 83 of [quarteroni2000numerical], §10.6. -/
theorem alpha_beta_laguerreMeasure :
    (∀ k, alpha laguerreMeasure k = 2 * k + 1) ∧ (∀ k, beta laguerreMeasure k = ((k : ℝ) + 1) ^ 2)
      ∧ normSq laguerreMeasure 0 = 1 :=
  ⟨alpha_laguerreMeasure, beta_laguerreMeasure, normSq_laguerreMeasure_zero⟩

/-! ### The Hermite polynomials -/

end OrthogonalPolynomial

namespace Polynomial

/-- The **physicists' Hermite polynomials** $H_n = (-1)^n e^{x^2} \frac{d^n}{dx^n} e^{-x^2}$,
defined by the operator recursion
$$H_0 = 1, \qquad H_{n+1} = 2x H_n - H_n'.$$
This follows [quarteroni2000numerical], §10.5.

The polynomial $H_n$ has leading coefficient $2^n$. The three-term recurrence
$H_{n+2} = 2x H_{n+1} - 2(n + 1) H_n$ is `Polynomial.physHermite_succ_succ`, and Rodrigues'
formula is `Polynomial.physHermite_eq_deriv_gaussian`. The definition follows Mathlib's
definition of the probabilists' Hermite polynomials `Polynomial.hermite`; the two families are
related by $H_n(x) = 2^{n/2} He_n(\sqrt 2 \, x)$, a relation that is not used. -/
def physHermite : ℕ → ℝ[X]
  | 0 => 1
  | (n + 1) => 2 * X * physHermite n - derivative (physHermite n)

/-- The zeroth Hermite polynomial is $H_0 = 1$. -/
@[simp]
theorem physHermite_zero : physHermite 0 = 1 := rfl

/-- For every $n$, the Hermite polynomials satisfy $H_{n+1} = 2x H_n - H_n'$. -/
theorem physHermite_succ (n : ℕ) :
    physHermite (n + 1) = 2 * X * physHermite n - derivative (physHermite n) := rfl

/-- The first Hermite polynomial is $H_1 = 2x$. -/
@[simp]
theorem physHermite_one : physHermite 1 = 2 * X := by
  rw [physHermite_succ, physHermite_zero, derivative_one]
  ring

/-- For every $n$, the Hermite polynomials satisfy $H_{n+1}' = 2(n + 1) H_n$. -/
theorem derivative_physHermite_succ (n : ℕ) :
    derivative (physHermite (n + 1)) = C (2 * ((n : ℝ) + 1)) * physHermite n := by
  induction n with
  | zero =>
    rw [physHermite_one, physHermite_zero, ← C_ofNat, derivative_C_mul_X]
    simp
  | succ n ih =>
    rw [physHermite_succ (n + 1), derivative_sub, derivative_mul, ih, derivative_C_mul,
      physHermite_succ n]
    simp only [derivative_mul, derivative_X, derivative_ofNat, map_mul, map_add, map_ofNat,
      map_natCast, map_one]
    push_cast
    ring

/-- The **three-term recurrence** of the physicists' Hermite polynomials: for every $n$,
$$H_{n+2} = 2x H_{n+1} - 2(n + 1) H_n.$$
This is the recurrence of [quarteroni2000numerical], §10.5. -/
theorem physHermite_succ_succ (n : ℕ) :
    physHermite (n + 2) = 2 * X * physHermite (n + 1) - C (2 * ((n : ℝ) + 1)) * physHermite n := by
  rw [physHermite_succ (n + 1), derivative_physHermite_succ]

/-- For every $n$, the Hermite polynomial $H_n$ has degree $n$ and leading coefficient $2^n$. -/
private theorem degree_leadingCoeff_physHermite_aux (n : ℕ) :
    (physHermite n).degree = n ∧ (physHermite n).leadingCoeff = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hd, hl⟩ := ih
    have hne : physHermite n ≠ 0 := fun h => by
      rw [h, degree_zero] at hd
      exact absurd hd (by simp)
    have h2X : (2 * X : ℝ[X]) = C 2 * X := by rw [C_ofNat]
    have hdeg1 : (2 * X * physHermite n).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [h2X, degree_mul, degree_C_mul_X (by norm_num), hd]
      norm_cast
      omega
    have hlc1 : (2 * X * physHermite n).leadingCoeff = 2 ^ (n + 1) := by
      rw [h2X, leadingCoeff_mul, leadingCoeff_C_mul_X, hl, pow_succ]
      ring
    have hdeg0 : (derivative (physHermite n)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
      refine (degree_derivative_le).trans_lt ?_
      rw [hd]
      exact_mod_cast (by omega : n < n + 1)
    rw [physHermite_succ]
    rw [← hdeg1] at hdeg0
    exact ⟨by rw [degree_sub_eq_left_of_degree_lt hdeg0, hdeg1],
      by rw [leadingCoeff_sub_of_degree_lt hdeg0, hlc1]⟩

/-- For every $n$, the Hermite polynomial $H_n$ has degree $n$. -/
@[simp]
theorem degree_physHermite (n : ℕ) : (physHermite n).degree = n :=
  (degree_leadingCoeff_physHermite_aux n).1

/-- For every $n$, the Hermite polynomial $H_n$ has leading coefficient $2^n$. -/
@[simp]
theorem leadingCoeff_physHermite (n : ℕ) : (physHermite n).leadingCoeff = 2 ^ n :=
  (degree_leadingCoeff_physHermite_aux n).2

/-- For every $n$, the Hermite polynomial $H_n$ has natural degree $n$. -/
theorem natDegree_physHermite (n : ℕ) : (physHermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_physHermite n)

/-! ### Rodrigues' formula for the Hermite polynomials -/

/-- The operator $S f = 2x f - f'$ on polynomials, whose $n$-th iterate applied to $1$ is $H_n$. -/
private def herS (f : ℝ[X]) : ℝ[X] := 2 * X * f - derivative f

private theorem physHermite_eq_iterate_herS (n : ℕ) : physHermite n = herS^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, physHermite_succ]; rfl

/-- For a polynomial $f$, the derivative of $e^{-x^2} f(x)$ is $-e^{-x^2} (S f)(x)$. -/
private theorem hasDerivAt_exp_neg_sq_mul_eval (f : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => exp (-y ^ 2) * f.eval y) (-(exp (-x ^ 2) * (herS f).eval x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => exp (-y ^ 2)) (exp (-x ^ 2) * (-(2 * x))) x := by
    have h := (hasDerivAt_pow 2 x).neg
    have := (Real.hasDerivAt_exp (-x ^ 2)).comp x h
    refine this.congr_deriv ?_
    norm_num
  have h2 := f.hasDerivAt x
  refine (h1.mul h2).congr_deriv ?_
  simp only [herS, eval_sub, eval_mul, eval_ofNat, eval_X]
  ring

private theorem iterate_deriv_exp_neg_sq_mul_eval (k : ℕ) (f : ℝ[X]) :
    deriv^[k] (fun y => exp (-y ^ 2) * f.eval y) =
      fun y => (-1) ^ k * (exp (-y ^ 2) * (herS^[k] f).eval y) := by
  induction k with
  | zero => funext y; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext y
    rw [deriv_const_mul _ (hasDerivAt_exp_neg_sq_mul_eval _ y).differentiableAt,
      (hasDerivAt_exp_neg_sq_mul_eval _ y).deriv, pow_succ]
    ring

/-- **Rodrigues' formula for the physicists' Hermite polynomials**: for every $n$ and every
$x \in \mathbb{R}$,
$$H_n(x) = (-1)^n e^{x^2} \, \frac{d^n}{dx^n} e^{-x^2}.$$
This is the formula of [quarteroni2000numerical], §10.5. -/
theorem physHermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) :
    (physHermite n).eval x = (-1) ^ n * exp (x ^ 2) * deriv^[n] (fun y => exp (-y ^ 2)) x := by
  have h := congrFun (iterate_deriv_exp_neg_sq_mul_eval n 1) x
  simp only [eval_one, mul_one] at h
  rw [h, ← physHermite_eq_iterate_herS]
  have e1 : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have e2 : exp (x ^ 2) * exp (-x ^ 2) = 1 := by rw [← exp_add]; simp
  calc (physHermite n).eval x
      = ((-1 : ℝ) ^ n * (-1) ^ n) * (exp (x ^ 2) * exp (-x ^ 2)) * (physHermite n).eval x := by
        rw [e1, e2]; ring
    _ = _ := by ring

/-! ### Orthogonality of the Hermite polynomials -/

/-- One integration by parts on $\mathbb{R}$: for polynomials $p$ and $q$, $\int p \, e^{-x^2} \, S
q \, dx = \int p' \, e^{-x^2} q \, dx$. -/
private theorem integral_eval_mul_exp_neg_sq_mul_herS (p q : ℝ[X]) :
    ∫ x, p.eval x * (exp (-x ^ 2) * (herS q).eval x) =
      ∫ x, (derivative p).eval x * (exp (-x ^ 2) * q.eval x) := by
  have hu : ∀ x ∈ tsupport (fun y => exp (-y ^ 2) * q.eval y),
      HasDerivAt (fun y => p.eval y) ((derivative p).eval x) x := fun x _ => p.hasDerivAt x
  have hv : ∀ x ∈ tsupport (fun y => p.eval y), HasDerivAt (fun y => exp (-y ^ 2) * q.eval y)
      (-(exp (-x ^ 2) * (herS q).eval x)) x := fun x _ => hasDerivAt_exp_neg_sq_mul_eval q x
  have hint1 : Integrable ((fun y => p.eval y) * fun x => -(exp (-x ^ 2) * (herS q).eval x)) := by
    refine ((integrable_eval_mul_exp_neg_sq (p * herS q)).neg).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, Pi.neg_apply, eval_mul]
    ring
  have hint2 :
      Integrable ((fun y => (derivative p).eval y) * fun y => exp (-y ^ 2) * q.eval y) := by
    refine (integrable_eval_mul_exp_neg_sq (derivative p * q)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, eval_mul]
    ring
  have hbot : Tendsto ((fun y => p.eval y) * fun y => exp (-y ^ 2) * q.eval y) atBot (𝓝 0) := by
    refine (tendsto_eval_mul_exp_neg_sq_atBot (p * q)).congr fun x => ?_
    simp only [Pi.mul_apply, eval_mul]
    ring
  have htop : Tendsto ((fun y => p.eval y) * fun y => exp (-y ^ 2) * q.eval y) atTop (𝓝 0) := by
    refine (tendsto_eval_mul_exp_neg_sq_atTop (p * q)).congr fun x => ?_
    simp only [Pi.mul_apply, eval_mul]
    ring
  have h := integral_mul_deriv_eq_deriv_mul hu hv hint1 hint2 hbot htop
  simp only [sub_zero, mul_neg, integral_neg] at h
  linarith

/-- For every $k$ and every polynomial $p$, $\int p \, e^{-x^2} \, S^k 1 \, dx = \int p^{(k)}
e^{-x^2} \, dx$, by $k$ integrations by parts. -/
private theorem integral_eval_mul_exp_neg_sq_mul_iterate_herS (k : ℕ) (p : ℝ[X]) :
    ∫ x, p.eval x * (exp (-x ^ 2) * (herS^[k] 1).eval x) =
      ∫ x, (derivative^[k] p).eval x * exp (-x ^ 2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', integral_eval_mul_exp_neg_sq_mul_herS, ih,
      Function.iterate_succ_apply]

/-- For every polynomial $p$, $\int p \, H_n \, e^{-x^2} \, dx = \int p^{(n)} e^{-x^2} \, dx$. -/
private theorem integral_eval_mul_physHermite_mul_exp_neg_sq (p : ℝ[X]) (n : ℕ) :
    ∫ x, p.eval x * (physHermite n).eval x * exp (-x ^ 2) =
      ∫ x, (derivative^[n] p).eval x * exp (-x ^ 2) := by
  rw [← integral_eval_mul_exp_neg_sq_mul_iterate_herS n p, ← physHermite_eq_iterate_herS]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

/-- **Orthogonality of the physicists' Hermite polynomials** on $\mathbb{R}$ for the weight
$e^{-x^2}$: for all $n$ and $m$,
$$\int_{-\infty}^{\infty} H_n(x) \, H_m(x) \, e^{-x^2} \, dx = \begin{cases} 2^n \, n! \,
  \sqrt\pi & \text{if } n = m, \\ 0 & \text{if } n \neq m. \end{cases}$$
This follows [quarteroni2000numerical], §10.5.

After $n$ integrations by parts, $\int H_m H_n e^{-x^2} \, dx = \int H_m^{(n)} e^{-x^2} \, dx$.
This vanishes for $m < n$, and for $m = n$ it is $2^n n! \int e^{-x^2} \, dx = 2^n n! \sqrt\pi$. -/
theorem integral_physHermite_mul_physHermite (n m : ℕ) :
    ∫ x, (physHermite n).eval x * (physHermite m).eval x * exp (-x ^ 2) =
      if n = m then 2 ^ n * (n ! : ℝ) * √π else 0 := by
  have hlt : ∀ m n : ℕ, m < n →
      ∫ x, (physHermite m).eval x * (physHermite n).eval x * exp (-x ^ 2) = 0 := by
    intro m n hmn
    rw [integral_eval_mul_physHermite_mul_exp_neg_sq,
      iterate_derivative_eq_zero (by rw [natDegree_physHermite]; exact hmn)]
    simp
  split_ifs with h
  · subst h
    rw [integral_eval_mul_physHermite_mul_exp_neg_sq, iterate_derivative_eq_C_of_natDegree_eq
      (natDegree_physHermite n), leadingCoeff_physHermite]
    simp only [eval_C]
    rw [integral_const_mul]
    have hg := integral_gaussian 1
    simp only [neg_one_mul, div_one] at hg
    rw [hg]
    ring
  · rcases lt_or_gt_of_ne h with hnm | hnm
    · exact hlt n m hnm
    · exact (integral_congr_ae (Eventually.of_forall fun x => by ring)).trans (hlt m n hnm)

end Polynomial

namespace OrthogonalPolynomial

/-! ### The Hermite weight -/

/-- The **Hermite weight**: the measure $e^{-x^2} \, dx$ on $\mathbb{R}$. This follows
[quarteroni2000numerical], §10.5. -/
def hermiteMeasure : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (exp (-x ^ 2))

/-- For every $f \colon \mathbb{R} \to \mathbb{R}$, the integral against the Hermite weight is
$\int e^{-x^2} f(x) \, dx$. -/
theorem integral_hermiteMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂hermiteMeasure = ∫ x, exp (-x ^ 2) * f x :=
  integral_withDensity_ofReal (by fun_prop) (Eventually.of_forall fun x => (exp_pos _).le) f

/-- A function $f$ is integrable for the Hermite weight if and only if $e^{-x^2} f(x)$ is integrable
on $\mathbb{R}$. -/
theorem integrable_hermiteMeasure_iff (f : ℝ → ℝ) :
    Integrable f hermiteMeasure ↔ Integrable fun x => exp (-x ^ 2) * f x :=
  integrable_withDensity_ofReal_iff (by fun_prop) (Eventually.of_forall fun x => (exp_pos _).le) f

/-- The Hermite weight has total mass $\sqrt\pi$: $\|p_0\|^2 = \int e^{-x^2} \, dx = \sqrt\pi$. -/
theorem normSq_hermiteMeasure_zero : normSq hermiteMeasure 0 = √π := by
  rw [normSq, family_zero, integral_hermiteMeasure]
  have hg := integral_gaussian 1
  simp only [neg_one_mul, div_one] at hg
  simpa using hg

/-- **The Hermite weight is a weight.** This follows [quarteroni2000numerical], §10.5.

Its moments are finite Gaussian integrals, and it is a nonzero measure that is absolutely
continuous with respect to Lebesgue measure. -/
theorem isWeight_hermiteMeasure : IsWeight hermiteMeasure := by
  refine isWeight_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)
    (ne_zero_of_integral_ne_zero (f := fun _ => (1 : ℝ)) ?_) fun n => ?_
  · have h := normSq_hermiteMeasure_zero
    rw [normSq, family_zero] at h
    simpa using h.trans_ne (sqrt_pos.mpr pi_pos).ne'
  · rw [integrable_hermiteMeasure_iff]
    refine (Polynomial.integrable_eval_mul_exp_neg_sq (X ^ n)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [eval_pow, eval_X]
    ring

/-- **The monic orthogonal polynomials of the Hermite weight** are $p_n = 2^{-n} H_n$ for every $n$.
Hence the nodes of the Gauss–Hermite rule are the zeros of $H_n$. This is (10.42) of
[quarteroni2000numerical]. -/
theorem family_hermiteMeasure_eq (n : ℕ) :
    family hermiteMeasure n = C ((2 : ℝ) ^ n)⁻¹ * Polynomial.physHermite n := by
  have h := family_eq_of_orthogonal isWeight_hermiteMeasure (q := Polynomial.physHermite)
    Polynomial.degree_physHermite
    (fun m n hmn => by
      rw [integral_hermiteMeasure]
      have := Polynomial.integral_physHermite_mul_physHermite n m
      rw [ite_eq_right (Nat.ne_of_gt hmn)] at this
      exact (integral_congr_ae (Eventually.of_forall fun x => by ring)).trans this) n
  rw [h, Polynomial.leadingCoeff_physHermite]

/-- For every $n$, the squared norm of the $n$-th monic orthogonal polynomial of the Hermite weight
is
$$\|p_n\|^2 = \frac{n! \, \sqrt\pi}{2^n}.$$
-/
theorem normSq_hermiteMeasure (n : ℕ) : normSq hermiteMeasure n = (n ! : ℝ) * √π / 2 ^ n := by
  rw [normSq_eq_of_family_eq (family_hermiteMeasure_eq n), integral_hermiteMeasure]
  have h := Polynomial.integral_physHermite_mul_physHermite n n
  rw [ite_eq_left rfl] at h
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [show ∫ x, exp (-x ^ 2) * (Polynomial.physHermite n).eval x ^ 2 =
      ∫ x, (Polynomial.physHermite n).eval x * (Polynomial.physHermite n).eval x * exp (-x ^ 2)
      from integral_congr_ae (Eventually.of_forall fun x => by ring), h]
  field_simp

/-- The monic three-term recurrence of the Hermite weight: for every $n$,
$$p_{n+2} = (x - 0) \, p_{n+1} - \frac{n + 1}{2} \, p_n.$$
It follows from `Polynomial.physHermite_succ_succ` and the leading coefficients $2^n$. The term
$x - 0$ keeps the form of `OrthogonalPolynomial.alpha_succ_eq_and_beta_eq_of_recurrence`. -/
theorem family_hermiteMeasure_recurrence (n : ℕ) :
    family hermiteMeasure (n + 2) = (X - C 0) * family hermiteMeasure (n + 1) -
      C (((n : ℝ) + 1) / 2) * family hermiteMeasure n := by
  rw [family_hermiteMeasure_eq, family_hermiteMeasure_eq, family_hermiteMeasure_eq,
    Polynomial.physHermite_succ_succ]
  have e1 : ((2 : ℝ) ^ (n + 2))⁻¹ * 2 = ((2 : ℝ) ^ (n + 1))⁻¹ := by
    field_simp
    ring
  have e2 : ((2 : ℝ) ^ (n + 2))⁻¹ * (2 * ((n : ℝ) + 1)) = ((n : ℝ) + 1) / 2 * ((2 : ℝ) ^ n)⁻¹ := by
    field_simp
    ring
  calc C ((2 : ℝ) ^ (n + 2))⁻¹ * (2 * X * Polynomial.physHermite (n + 1) -
        C (2 * ((n : ℝ) + 1)) * Polynomial.physHermite n)
      = C (((2 : ℝ) ^ (n + 2))⁻¹ * 2) * X * Polynomial.physHermite (n + 1) -
          C (((2 : ℝ) ^ (n + 2))⁻¹ * (2 * ((n : ℝ) + 1))) * Polynomial.physHermite n := by
        simp only [C_mul, C_ofNat]
        ring
    _ = _ := by
        rw [e1, e2, C_mul, C_0, sub_zero]
        ring

/-- The recurrence coefficients $\alpha_k$ of the Hermite weight are $\alpha_k = 0$ for every $k$.
This is Program 84 of [quarteroni2000numerical], §10.6. -/
theorem alpha_hermiteMeasure (k : ℕ) : alpha hermiteMeasure k = 0 := by
  cases k with
  | zero =>
    refine alpha_zero_eq_of_family_one ?_
    rw [family_hermiteMeasure_eq, Polynomial.physHermite_one, C_0, sub_zero, ← C_ofNat,
      ← mul_assoc, ← C_mul]
    norm_num
  | succ k =>
    exact (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_hermiteMeasure
      (family_hermiteMeasure_recurrence k)).1

/-- The recurrence coefficients $\beta_k$ of the Hermite weight are $\beta_k = (k + 1)/2$ for every
$k$. This is Program 84 of [quarteroni2000numerical], §10.6. -/
theorem beta_hermiteMeasure (k : ℕ) : beta hermiteMeasure k = ((k : ℝ) + 1) / 2 :=
  (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_hermiteMeasure
    (family_hermiteMeasure_recurrence k)).2

/-- **The recurrence coefficients of the Hermite weight**: for every $k$,
$$\alpha_k = 0, \qquad \beta_k = \frac{k + 1}{2},$$
and the total mass is $\|p_0\|^2 = \sqrt\pi$. This is Program 84 of [quarteroni2000numerical],
§10.6. -/
theorem alpha_beta_hermiteMeasure :
    (∀ k, alpha hermiteMeasure k = 0) ∧ (∀ k, beta hermiteMeasure k = ((k : ℝ) + 1) / 2) ∧
      normSq hermiteMeasure 0 = √π :=
  ⟨alpha_hermiteMeasure, beta_hermiteMeasure, normSq_hermiteMeasure_zero⟩

/-! ### The recurrence coefficients of the Legendre weight -/

/-- For every $n$, the leading coefficients of consecutive Legendre polynomials satisfy
$$\operatorname{lc}(P_{n+1}) = \frac{2n + 1}{n + 1} \, \operatorname{lc}(P_n).$$
This is read off the three-term recurrence `Polynomial.legendre_recurrence`. -/
theorem leadingCoeff_legendre_succ (n : ℕ) :
    (Polynomial.legendre (n + 1)).leadingCoeff =
      (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (Polynomial.legendre n).leadingCoeff := by
  cases n with
  | zero => simp [Polynomial.legendre_zero, Polynomial.legendre_one]
  | succ n =>
    have hrec := Polynomial.legendre_recurrence n
    have hne : ((n : ℝ[X]) + 2) ≠ 0 := by
      rw [← C_eq_natCast, ← C_ofNat, ← C_add]
      exact C_ne_zero.mpr (by positivity)
    have hlhs : (((n : ℝ[X]) + 2) * Polynomial.legendre (n + 2)).leadingCoeff =
        ((n : ℝ) + 2) * (Polynomial.legendre (n + 2)).leadingCoeff := by
      rw [leadingCoeff_mul, ← C_eq_natCast, ← C_ofNat, ← C_add, leadingCoeff_C]
    have hdeg1 : ((2 * (n : ℝ[X]) + 3) * X * Polynomial.legendre (n + 1)).degree =
        ((n + 2 : ℕ) : WithBot ℕ) := by
      rw [← C_eq_natCast, ← C_ofNat, ← C_ofNat, ← C_mul, ← C_add, degree_mul, degree_mul,
        degree_C (by positivity), degree_X, Polynomial.degree_legendre]
      norm_cast
      omega
    have hdeg0 : (((n : ℝ[X]) + 1) * Polynomial.legendre n).degree < ((n + 2 : ℕ) : WithBot ℕ) := by
      rw [← C_eq_natCast, ← C_1, ← C_add, degree_mul, degree_C (by positivity), zero_add,
        Polynomial.degree_legendre]
      exact_mod_cast (by omega : n < n + 2)
    have hrhs : ((2 * (n : ℝ[X]) + 3) * X * Polynomial.legendre (n + 1) -
        ((n : ℝ[X]) + 1) * Polynomial.legendre n).leadingCoeff =
        (2 * (n : ℝ) + 3) * (Polynomial.legendre (n + 1)).leadingCoeff := by
      rw [← hdeg1] at hdeg0
      rw [leadingCoeff_sub_of_degree_lt hdeg0, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_X,
        ← C_eq_natCast, ← C_ofNat, ← C_ofNat, ← C_mul, ← C_add, leadingCoeff_C, mul_one]
    have h := congrArg leadingCoeff hrec
    rw [hlhs, hrhs] at h
    push_cast
    field_simp
    linear_combination h

/-- The monic three-term recurrence of the Legendre weight: for every $n$,
$$p_{n+2} = (x - 0) \, p_{n+1} - \frac{(n + 1)^2}{4 (n + 1)^2 - 1} \, p_n.$$
It follows from `Polynomial.legendre_recurrence` and the leading coefficients of the Legendre
polynomials. -/
theorem family_legendreMeasure_recurrence (n : ℕ) :
    family legendreMeasure (n + 2) = (X - C 0) * family legendreMeasure (n + 1) -
      C (((n : ℝ) + 1) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2 - 1)) * family legendreMeasure n := by
  have hl1 := leadingCoeff_legendre_succ n
  have hl2 : (Polynomial.legendre (n + 2)).leadingCoeff =
      (2 * ((n : ℝ) + 1) + 1) / (((n : ℝ) + 1) + 1) *
        (Polynomial.legendre (n + 1)).leadingCoeff := by
    have := leadingCoeff_legendre_succ (n + 1)
    push_cast at this
    exact this
  have hl0 : (Polynomial.legendre n).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero n)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have h21 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h23 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h4 : 4 * ((n : ℝ) + 1) ^ 2 - 1 = (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) := by ring
  have hL2 : Polynomial.legendre (n + 2) = C ((n : ℝ) + 2)⁻¹ *
      (C (2 * (n : ℝ) + 3) * X * Polynomial.legendre (n + 1) -
        C ((n : ℝ) + 1) * Polynomial.legendre n) := by
    have hrec := Polynomial.legendre_recurrence n
    have this : C ((n : ℝ) + 2)⁻¹ * (((n : ℝ[X]) + 2) * Polynomial.legendre (n + 2)) =
        C ((n : ℝ) + 2)⁻¹ * ((2 * (n : ℝ[X]) + 3) * X * Polynomial.legendre (n + 1) -
          ((n : ℝ[X]) + 1) * Polynomial.legendre n) := by
      rw [hrec]
    rw [show ((n : ℝ[X]) + 2) = C ((n : ℝ) + 2) by rw [map_add, map_natCast, map_ofNat],
      ← mul_assoc, ← C_mul, inv_mul_cancel₀ hn2, C_1, one_mul] at this
    rw [this]
    congr 2
    · simp only [map_add, map_mul, map_natCast, map_ofNat]
    · simp only [map_add, map_natCast, map_one]
  simp only [family_eq_legendre]
  have e1 : ((Polynomial.legendre (n + 2)).leadingCoeff)⁻¹ * ((n : ℝ) + 2)⁻¹ *
      (2 * (n : ℝ) + 3) = ((Polynomial.legendre (n + 1)).leadingCoeff)⁻¹ := by
    rw [hl2, hl1]
    field_simp
    ring
  have e2 : ((Polynomial.legendre (n + 2)).leadingCoeff)⁻¹ * ((n : ℝ) + 2)⁻¹ * ((n : ℝ) + 1) =
      ((n : ℝ) + 1) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2 - 1) *
        ((Polynomial.legendre n).leadingCoeff)⁻¹ := by
    rw [hl2, hl1, h4]
    field_simp
    ring
  calc C ((Polynomial.legendre (n + 2)).leadingCoeff)⁻¹ * Polynomial.legendre (n + 2)
      = C (((Polynomial.legendre (n + 2)).leadingCoeff)⁻¹ * ((n : ℝ) + 2)⁻¹ *
            (2 * (n : ℝ) + 3)) * (X * Polynomial.legendre (n + 1)) -
          C (((Polynomial.legendre (n + 2)).leadingCoeff)⁻¹ * ((n : ℝ) + 2)⁻¹ * ((n : ℝ) + 1)) *
            Polynomial.legendre n := by
        rw [hL2]
        simp only [C_mul]
        ring
    _ = _ := by
        rw [e1, e2, C_mul, C_0, sub_zero]
        ring

/-- The recurrence coefficients $\alpha_k$ of the Legendre weight are $\alpha_k = 0$ for every $k$.
This is Program 82 of [quarteroni2000numerical], §10.6. -/
theorem alpha_legendreMeasure (k : ℕ) : alpha legendreMeasure k = 0 := by
  cases k with
  | zero =>
    refine alpha_zero_eq_of_family_one ?_
    rw [family_eq_legendre, Polynomial.legendre_one]
    simp
  | succ k =>
    exact (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_legendreMeasure
      (family_legendreMeasure_recurrence k)).1

/-- The recurrence coefficients $\beta_k$ of the Legendre weight are, for every $k$,
$$\beta_k = \frac{(k + 1)^2}{4 (k + 1)^2 - 1}.$$
This is Program 82 of [quarteroni2000numerical], §10.6. -/
theorem beta_legendreMeasure (k : ℕ) :
    beta legendreMeasure k = ((k : ℝ) + 1) ^ 2 / (4 * ((k : ℝ) + 1) ^ 2 - 1) :=
  (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_legendreMeasure
    (family_legendreMeasure_recurrence k)).2

/-- For every $n$, the squared norm of the $n$-th monic orthogonal polynomial of the Legendre weight
is
$$\|p_n\|^2 = \frac{2}{(2n + 1) \operatorname{lc}(P_n)^2}.$$
-/
theorem normSq_legendreMeasure (n : ℕ) :
    normSq legendreMeasure n =
      2 / ((2 * (n : ℝ) + 1) * (Polynomial.legendre n).leadingCoeff ^ 2) := by
  rw [normSq_eq_of_family_eq (family_eq_legendre n), integral_legendreMeasure,
    Polynomial.integral_legendre_sq]
  have hlc : (Polynomial.legendre n).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero n)
  have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The Legendre weight has total mass $2$: $\|p_0\|^2 = 2$. -/
theorem normSq_legendreMeasure_zero : normSq legendreMeasure 0 = 2 := by
  rw [normSq, family_zero, integral_legendreMeasure]
  simp
  norm_num

/-- **The recurrence coefficients of the Legendre weight**: for every $k$,
$$\alpha_k = 0, \qquad \beta_k = \frac{(k + 1)^2}{4 (k + 1)^2 - 1},$$
and the total mass is $\|p_0\|^2 = 2$. This is Program 82 of [quarteroni2000numerical], §10.6. -/
theorem alpha_beta_legendreMeasure :
    (∀ k, alpha legendreMeasure k = 0) ∧
      (∀ k, beta legendreMeasure k = ((k : ℝ) + 1) ^ 2 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) ∧
        normSq legendreMeasure 0 = 2 :=
  ⟨alpha_legendreMeasure, beta_legendreMeasure, normSq_legendreMeasure_zero⟩

end OrthogonalPolynomial

end
