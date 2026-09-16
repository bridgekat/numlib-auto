import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Numlib.Approximation.OrthogonalPolynomial

/-!
# The classical weights and their orthogonal polynomials

The classical weights beyond the Legendre family of `Numlib/Approximation/OrthogonalPolynomial`:
the Chebyshev weight `(1 - x²)^{-1/2}` on `(-1, 1)`, the Jacobi weights `(1 - x)^α (1 + x)^β`,
the Laguerre weight `e^{-x}` on `(0, ∞)` and the Hermite weight `e^{-x²}` on `ℝ`. Each is shown to
satisfy `OrthogonalPolynomial.IsWeight` — finite moments and infinite support — so that
`OrthogonalPolynomial.family`, `Quadrature.exists_gauss` and the whole general theory apply; the
classical polynomials (`Polynomial.Chebyshev.T`, `Polynomial.laguerre`, `Polynomial.physHermite`)
are identified with the monic `family` up to their leading coefficients, and the recurrence
coefficients `OrthogonalPolynomial.alpha`, `OrthogonalPolynomial.beta` are computed in closed form.

## Main definitions

* `OrthogonalPolynomial.chebyshevMeasure` is Mathlib's `Polynomial.Chebyshev.measureT`;
  `OrthogonalPolynomial.jacobiMeasure α β`, `OrthogonalPolynomial.laguerreMeasure` and
  `OrthogonalPolynomial.hermiteMeasure` are Lebesgue measure with the classical densities.
* `Polynomial.laguerre n` is the unnormalized Laguerre polynomial `ℒ_n = e^x (d/dx)^n (e^{-x} x^n)`
  of [quarteroni2000numerical] §10.5, defined by its three-term recurrence
  `ℒ_{n+2} = (2n + 3 - X) ℒ_{n+1} - (n + 1)² ℒ_n`; it has leading coefficient `(-1)^n` and
  `ℒ_n(0) = n!`, and is `n!` times the normalized Laguerre polynomial of most references.
* `Polynomial.physHermite n` is the physicists' Hermite polynomial
  `H_n = (-1)^n e^{x²} (d/dx)^n e^{-x²}`, defined as Mathlib defines the probabilists'
  `Polynomial.hermite`, by the operator recursion `H_{n+1} = 2X H_n - H_n'`; the three-term
  recurrence `H_{n+2} = 2X H_{n+1} - 2(n + 1) H_n` is `Polynomial.physHermite_succ_succ`. Its
  leading coefficient is `2^n`, and it is related to Mathlib's family by
  `H_n(x) = 2^{n/2} He_n(√2 x)`.

## Main results

* `OrthogonalPolynomial.isWeight_chebyshevMeasure`, `isWeight_jacobiMeasure` (for
  `α, β > -1`), `isWeight_laguerreMeasure`, `isWeight_hermiteMeasure`.
* `OrthogonalPolynomial.jacobiMeasure_zero_zero` and `jacobiMeasure_neg_half_neg_half`: the
  Legendre and Chebyshev weights are the Jacobi weights with `α = β = 0` and `α = β = -1/2`.
* `OrthogonalPolynomial.family_chebyshevMeasure_eq`, `family_laguerreMeasure_eq`,
  `family_hermiteMeasure_eq`: the monic orthogonal polynomials of the classical weights are the
  monic rescalings of `T_n`, `ℒ_n`, `H_n`.
* `Polynomial.laguerre_eq_deriv_exp_mul` and `Polynomial.physHermite_eq_deriv_gaussian` are the
  Rodrigues formulas, and `Polynomial.integral_laguerre_mul_laguerre`,
  `Polynomial.integral_physHermite_mul_physHermite` the orthogonality relations with the norms
  `(n!)²` and `2^n n! √π`. Both rest on the *algebraic* form of Rodrigues' formula: `ℒ_n` is the
  `n`-th iterate of `f ↦ f' - f` on `X^n`, and `H_n` the `n`-th iterate of `f ↦ 2X f - f'` on
  `1`; the classical recurrences follow from the commutation relations of these operators with
  multiplication by `X`, and orthogonality from `n` integrations by parts on `(0, ∞)` or `ℝ`,
  since `e^{-x} (f' - f) = (e^{-x} f)'` and `e^{-x²} (2x f - f') = -(e^{-x²} f)'`.
* `OrthogonalPolynomial.alpha_beta_legendreMeasure`, `alpha_beta_laguerreMeasure`,
  `alpha_beta_hermiteMeasure`: the recurrence coefficients of the three weights, which
  [quarteroni2000numerical] §10.6 (Programs 82–84) tabulates, read off the classical recurrences by
  `OrthogonalPolynomial.alpha_succ_eq_and_beta_eq_of_recurrence`.

## References

[quarteroni2000numerical] §10.1, §10.5–10.6; [han2009theoretical] §3.5.
-/

open MeasureTheory Polynomial Real Set Filter Topology

open scoped Nat

noncomputable section

namespace OrthogonalPolynomial

/-! ### Weights given by a density -/

/-- A nonzero measure absolutely continuous with respect to Lebesgue measure charges the
complement of every finite set, so it is a weight as soon as its moments are finite. -/
theorem isWeight_of_absolutelyContinuous {μ : Measure ℝ} (hac : μ ≪ volume) (hμ : μ ≠ 0)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) : IsWeight μ where
  integrable_pow := hint
  measure_compl_ne_zero {s} hs := by
    intro h
    have hs0 : μ s = 0 := hac (hs.measure_zero volume)
    have huniv : μ univ = 0 := by
      rw [← measure_add_measure_compl hs.measurableSet, hs0, h, add_zero]
    exact hμ (Measure.measure_univ_eq_zero.mp huniv)

/-- A measure against which some function has nonzero integral is nonzero. -/
theorem ne_zero_of_integral_ne_zero {μ : Measure ℝ} {f : ℝ → ℝ} (h : ∫ x, f x ∂μ ≠ 0) :
    μ ≠ 0 := fun h0 => h (by rw [h0, integral_zero_measure])

/-- Integration against a density given as `ENNReal.ofReal` of a nonnegative function. -/
theorem integral_withDensity_ofReal {ν : Measure ℝ} {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    (hnn : ∀ᵐ x ∂ν, 0 ≤ ρ x) (f : ℝ → ℝ) :
    ∫ x, f x ∂(ν.withDensity fun x => ENNReal.ofReal (ρ x)) = ∫ x, ρ x * f x ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hnn] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

/-- Integrability against a density given as `ENNReal.ofReal` of a nonnegative function. -/
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

/-- The Chebyshev weight `(1 - x²)^{-1/2}` on `(-1, 1)`: Mathlib's `Polynomial.Chebyshev.measureT`,
so that `Polynomial.Chebyshev.integral_measureT` and the orthogonality relations of `T_n` apply
unchanged.

Reference: [quarteroni2000numerical] (10.9). -/
abbrev chebyshevMeasure : Measure ℝ := Polynomial.Chebyshev.measureT

theorem chebyshevMeasure_absolutelyContinuous : chebyshevMeasure ≪ volume :=
  (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
    (withDensity_absolutelyContinuous _ _)

/-- The Chebyshev weight has total mass `π`. -/
theorem integral_one_chebyshevMeasure : ∫ _x, (1 : ℝ) ∂chebyshevMeasure = π := by
  have h := Polynomial.Chebyshev.integral_eval_T_real_measureT_zero
  simpa using h

/-- **The Chebyshev weight is a weight**: continuous functions are integrable for it, and it is a
nonzero measure absolutely continuous with respect to Lebesgue measure. -/
theorem isWeight_chebyshevMeasure : IsWeight chebyshevMeasure :=
  isWeight_of_absolutelyContinuous chebyshevMeasure_absolutelyContinuous
    (ne_zero_of_integral_ne_zero (f := fun _ => (1 : ℝ))
      (by rw [integral_one_chebyshevMeasure]; exact pi_ne_zero))
    fun n => Polynomial.Chebyshev.integrable_measureT (by fun_prop)

/-- The Chebyshev weight gives no mass outside `[-1, 1]`. -/
theorem chebyshevMeasure_compl_Icc : chebyshevMeasure (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [chebyshevMeasure, Chebyshev.measureT, Measure.restrict_apply' measurableSet_Ioc]
  have hempty : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioc (-1 : ℝ) 1 = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => ht.1 (Ioc_subset_Icc_self ht.2)
  rw [hempty, measure_empty]

/-- **The monic orthogonal polynomials of the Chebyshev weight are the monic rescalings of the
Chebyshev polynomials**: `family chebyshevMeasure n = 2^{-(n-1)} T_n` (and `1` at `n = 0`).

Reference: [quarteroni2000numerical] §10.1.1. -/
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

/-- The Jacobi weight `(1 - x)^α (1 + x)^β` on `(-1, 1)`, with real exponents.

Reference: [quarteroni2000numerical] Remark 10.1. -/
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

/-- An integral against the Jacobi weight. -/
theorem integral_jacobiMeasure (α β : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂jacobiMeasure α β = ∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β * f x :=
  integral_withDensity_ofReal (measurable_jacobiDensity α β) (jacobiDensity_nonneg α β) f

/-- Integrability for the Jacobi weight. -/
theorem integrable_jacobiMeasure_iff (α β : ℝ) (f : ℝ → ℝ) :
    Integrable f (jacobiMeasure α β) ↔
      IntegrableOn (fun x => (1 - x) ^ α * (1 + x) ^ β * f x) (Ioo (-1 : ℝ) 1) :=
  integrable_withDensity_ofReal_iff (measurable_jacobiDensity α β) (jacobiDensity_nonneg α β) f

/-- The Jacobi density times a continuous function is integrable on `(-1, 1)` when both exponents
exceed `-1`: split at `0`, where on each half one factor is continuous and the other is a power
`t^r` with `r > -1`, integrable at its endpoint. -/
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

/-- **The Jacobi weights are weights** for `α, β > -1`: the moments are finite because the
density is integrable near each endpoint, and the density is positive on `(-1, 1)`.

Reference: [quarteroni2000numerical] Remark 10.1. -/
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

/-- The Jacobi weight `(1 - x)^α (1 + x)^β dx` on `(-1, 1)` gives no mass outside `[-1, 1]`. -/
theorem jacobiMeasure_compl_Icc (α β : ℝ) : jacobiMeasure α β (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply' measurableSet_Ioo]
  have hempty : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioo (-1 : ℝ) 1 = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => ht.1 (Ioo_subset_Icc_self ht.2)
  rw [hempty, measure_empty]

/-- The Jacobi weight with `α = β = 0` is the Legendre weight.

Reference: [quarteroni2000numerical] Remark 10.1. -/
theorem jacobiMeasure_zero_zero : jacobiMeasure 0 0 = legendreMeasure := by
  rw [jacobiMeasure]
  simp only [rpow_zero, mul_one, ENNReal.ofReal_one]
  exact withDensity_one

/-- The Jacobi weight with `α = β = -1/2` is the Chebyshev weight: on `(-1, 1]` both densities
are `(1 - x²)^{-1/2}`, both vanishing at `1`.

Reference: [quarteroni2000numerical] Remark 10.1. -/
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

/-- **The Laguerre polynomials** `ℒ_n = e^x (d/dx)^n (e^{-x} x^n)`, defined by their three-term
recurrence `ℒ_0 = 1`, `ℒ_1 = 1 - X`, `ℒ_{n+2} = (2n + 3 - X) ℒ_{n+1} - (n + 1)² ℒ_n`. This is the
unnormalized family of [quarteroni2000numerical] §10.5, with leading coefficient `(-1)^n` and
`ℒ_n(0) = n!`; the normalized `L_n = ℒ_n / n!` of most references is not used here.
`Polynomial.laguerre_eq_deriv_exp_mul` is Rodrigues' formula. -/
def laguerre : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 - X
  | (n + 2) => (C (2 * (n : ℝ) + 3) - X) * laguerre (n + 1) - C (((n : ℝ) + 1) ^ 2) * laguerre n

@[simp]
theorem laguerre_zero : laguerre 0 = 1 := rfl

@[simp]
theorem laguerre_one : laguerre 1 = 1 - X := rfl

/-- The three-term recurrence of the Laguerre polynomials, [quarteroni2000numerical] §10.5. -/
theorem laguerre_succ_succ (n : ℕ) :
    laguerre (n + 2) =
      (C (2 * (n : ℝ) + 3) - X) * laguerre (n + 1) - C (((n : ℝ) + 1) ^ 2) * laguerre n := rfl

/-- The degree and leading coefficient of `ℒ_n`, proved together by a two-step induction. -/
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

/-- `ℒ_n` has degree `n`. -/
@[simp]
theorem degree_laguerre (n : ℕ) : (laguerre n).degree = n :=
  (degree_leadingCoeff_laguerre_aux n).1.1

/-- `ℒ_n` has leading coefficient `(-1)^n`. -/
@[simp]
theorem leadingCoeff_laguerre (n : ℕ) : (laguerre n).leadingCoeff = (-1) ^ n :=
  (degree_leadingCoeff_laguerre_aux n).1.2

theorem natDegree_laguerre (n : ℕ) : (laguerre n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_laguerre n)

theorem laguerre_ne_zero (n : ℕ) : laguerre n ≠ 0 := fun h => by
  have := degree_laguerre n
  rw [h, degree_zero] at this
  exact absurd this (by simp)

/-! #### The algebraic Rodrigues formula

The operator `f ↦ f' - f` is `e^x (d/dx) e^{-x}` on polynomials, so `ℒ_n` is its `n`-th iterate
on `X^n`. The three-term recurrence follows from the commutation relation of the operator with
multiplication by `X`. -/

/-- The operator `f ↦ f' - f` on polynomials. -/
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

/-- The commutation relation `T^{k+1} (X f) = X T^{k+1} f + (k + 1) T^k f`. -/
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

/-- The derivative commutes with `T`. -/
private theorem derivative_iterate_lagT (k : ℕ) (f : ℝ[X]) :
    derivative (lagT^[k] f) = lagT^[k] (derivative f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    simp only [lagT, derivative_sub]

/-- The iterates `R_n = T^n X^n` satisfy `R_{n+1} = X (R_n' - R_n) + (n + 1) R_n`. -/
private theorem iterate_lagT_succ_eq (n : ℕ) :
    lagT^[n + 1] (X ^ (n + 1)) =
      X * (derivative (lagT^[n] (X ^ n)) - lagT^[n] (X ^ n)) +
        C ((n : ℝ) + 1) * lagT^[n] (X ^ n) := by
  rw [pow_succ', iterate_lagT_X_mul, Function.iterate_succ_apply']
  rfl

/-- The iterates `R_n = T^n X^n` satisfy `R_{n+1}' = (n + 1)(R_n' - R_n)`. -/
private theorem derivative_iterate_lagT_succ (n : ℕ) :
    derivative (lagT^[n + 1] (X ^ (n + 1))) =
      C ((n : ℝ) + 1) * (derivative (lagT^[n] (X ^ n)) - lagT^[n] (X ^ n)) := by
  rw [derivative_iterate_lagT, derivative_X_pow, Nat.add_sub_cancel, iterate_lagT_C_mul,
    Function.iterate_succ_apply']
  push_cast
  rfl

/-- **The algebraic Rodrigues formula**: `ℒ_n` is the `n`-th iterate of `f ↦ f' - f` on `X^n`.
The iterates satisfy the identities `R_{n+1} = X (R_n' - R_n) + (n + 1) R_n` and
`R_{n+1}' = (n + 1)(R_n' - R_n)`, which combine into the three-term recurrence defining `ℒ_n`. -/
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

/-- `ℒ_{n+1} = X (ℒ_n' - ℒ_n) + (n + 1) ℒ_n`. -/
theorem laguerre_succ_eq (n : ℕ) :
    laguerre (n + 1) =
      X * (derivative (laguerre n) - laguerre n) + C ((n : ℝ) + 1) * laguerre n := by
  rw [laguerre_eq_iterate_lagT, laguerre_eq_iterate_lagT]
  exact iterate_lagT_succ_eq n

/-- `ℒ_{n+1}' = (n + 1)(ℒ_n' - ℒ_n)`. -/
theorem derivative_laguerre_succ (n : ℕ) :
    derivative (laguerre (n + 1)) = C ((n : ℝ) + 1) * (derivative (laguerre n) - laguerre n) := by
  rw [laguerre_eq_iterate_lagT, laguerre_eq_iterate_lagT]
  exact derivative_iterate_lagT_succ n

/-- `X ℒ_{n+1}' = (n + 1) ℒ_{n+1} - (n + 1)² ℒ_n`, the identity that gives the Gauss–Laguerre
weights. -/
theorem X_mul_derivative_laguerre_succ (n : ℕ) :
    X * derivative (laguerre (n + 1)) =
      C ((n : ℝ) + 1) * laguerre (n + 1) - C (((n : ℝ) + 1) ^ 2) * laguerre n := by
  have h1 := laguerre_succ_eq n
  have h2 := derivative_laguerre_succ n
  rw [h2]
  simp only [map_pow]
  linear_combination -(C ((n : ℝ) + 1)) * h1

/-- `ℒ_n(0) = n!`. -/
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

/-- `X^{n-k}` divides `T^k X^n` for `k ≤ n`: applying `T` lowers the power of `X` dividing a
polynomial by at most one. -/
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

/-! #### The analytic Rodrigues formula -/

/-- `e^{-x} (T f)(x)` is the derivative of `e^{-x} f(x)`. -/
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

/-- **Rodrigues' formula for the Laguerre polynomials**:
`ℒ_n(x) = e^x (d/dx)^n (e^{-x} x^n)`.

Reference: [quarteroni2000numerical] §10.5. -/
theorem laguerre_eq_deriv_exp_mul (n : ℕ) (x : ℝ) :
    (laguerre n).eval x = exp x * deriv^[n] (fun y => exp (-y) * y ^ n) x := by
  have h := congrFun (iterate_deriv_exp_neg_mul_eval n (X ^ n)) x
  simp only [eval_pow, eval_X] at h
  rw [h, ← laguerre_eq_iterate_lagT, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-! #### Orthogonality -/

/-- A polynomial times `e^{-x}` is integrable on `(0, ∞)`: each monomial is a Gamma integrand. -/
private theorem integrableOn_eval_mul_exp_neg (p : ℝ[X]) :
    IntegrableOn (fun x => p.eval x * exp (-x)) (Ioi 0) := by
  have hmono : ∀ i : ℕ, IntegrableOn (fun x : ℝ => x ^ i * exp (-x)) (Ioi 0) := by
    intro i
    have h := Real.GammaIntegral_convergent (s := (i : ℝ) + 1) (by positivity)
    refine (h.congr_fun (fun x hx => ?_) measurableSet_Ioi)
    simp only [add_sub_cancel_right, rpow_natCast]
    ring
  have heq : (fun x => p.eval x * exp (-x)) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (hmono i).const_mul _

/-- A polynomial times `e^{-x}` tends to `0` at `+∞`. -/
private theorem tendsto_eval_mul_exp_neg_atTop (p : ℝ[X]) :
    Tendsto (fun x => p.eval x * exp (-x)) atTop (𝓝 0) := by
  have heq : (fun x => p.eval x * exp (-x)) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  have h : Tendsto (fun x => ∑ i ∈ Finset.range (p.natDegree + 1),
      p.coeff i * (x ^ i * exp (-x))) atTop (𝓝 (∑ i ∈ Finset.range (p.natDegree + 1),
      p.coeff i * 0)) :=
    tendsto_finsetSum _ fun i _ => (tendsto_pow_mul_exp_neg_atTop_nhds_zero i).const_mul _
  simpa using h

/-- **One integration by parts on `(0, ∞)`**: for polynomials `p`, `q` with `q(0) = 0`,
`∫_0^∞ p e^{-x} (T q) = -∫_0^∞ p' e^{-x} q`, since `e^{-x} T q = (e^{-x} q)'` and the boundary
terms vanish. -/
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
    refine (tendsto_eval_mul_exp_neg_atTop (p * q)).congr fun x => ?_
    simp only [Pi.mul_apply, eval_mul]
    ring
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hint1 hint2 hzero hinfty
  rw [h, hq]
  simp

/-- `∫_0^∞ p e^{-x} (T^k X^n) = (-1)^k ∫_0^∞ p^{(k)} e^{-x} x^n` for `k ≤ n`: `k` integrations by
parts. -/
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

/-- `∫_0^∞ e^{-x} x^n = n!`, the Gamma integral at `n + 1`. -/
theorem integral_exp_neg_mul_pow (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), exp (-x) * x ^ n = n ! := by
  have h := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [add_sub_cancel_right, rpow_natCast]

/-- `∫_0^∞ p ℒ_n e^{-x} = (-1)^n ∫_0^∞ p^{(n)} e^{-x} x^n` for every polynomial `p`. -/
private theorem integral_eval_mul_laguerre_mul_exp_neg (p : ℝ[X]) (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), p.eval x * (laguerre n).eval x * exp (-x) =
      (-1) ^ n * ∫ x in Ioi (0 : ℝ), (derivative^[n] p).eval x * (exp (-x) * x ^ n) := by
  rw [← integral_eval_mul_exp_neg_mul_iterate_lagT p n n le_rfl, ← laguerre_eq_iterate_lagT]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- The `n`-th derivative of a polynomial of degree `n` is the constant `n!` times its leading
coefficient. -/
private theorem iterate_derivative_natDegree_eq_C {p : ℝ[X]} {n : ℕ} (hp : p.natDegree = n) :
    derivative^[n] p = C ((n ! : ℝ) * p.leadingCoeff) := by
  have hdeg : (derivative^[n] p).natDegree ≤ 0 := by
    have := natDegree_iterate_derivative p n
    rwa [hp, Nat.sub_self] at this
  rw [eq_C_of_natDegree_le_zero hdeg, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    leadingCoeff, hp, nsmul_eq_mul]

/-- **Orthogonality of the Laguerre polynomials** on `(0, ∞)` for the weight `e^{-x}`, with the
norms `∫_0^∞ ℒ_n² e^{-x} = (n!)²`.

By `n` integrations by parts, `∫_0^∞ ℒ_m ℒ_n e^{-x} = (-1)^n ∫_0^∞ ℒ_m^{(n)} e^{-x} x^n`, which
vanishes for `m < n` and equals `(-1)^n n! (-1)^n ∫_0^∞ x^n e^{-x} = (n!)²` for `m = n`.

Reference: [quarteroni2000numerical] §10.5. -/
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
    rw [integral_eval_mul_laguerre_mul_exp_neg, iterate_derivative_natDegree_eq_C
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

/-- The Laguerre weight `e^{-x}` on `(0, ∞)`.

Reference: [quarteroni2000numerical] §10.5. -/
def laguerreMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun x => ENNReal.ofReal (exp (-x))

/-- An integral against the Laguerre weight. -/
theorem integral_laguerreMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂laguerreMeasure = ∫ x in Ioi (0 : ℝ), exp (-x) * f x :=
  integral_withDensity_ofReal (by fun_prop) (Eventually.of_forall fun x => (exp_pos _).le) f

/-- Integrability for the Laguerre weight. -/
theorem integrable_laguerreMeasure_iff (f : ℝ → ℝ) :
    Integrable f laguerreMeasure ↔ IntegrableOn (fun x => exp (-x) * f x) (Ioi 0) :=
  integrable_withDensity_ofReal_iff (by fun_prop) (Eventually.of_forall fun x => (exp_pos _).le) f

/-- The Laguerre weight has total mass `1`. -/
theorem normSq_laguerreMeasure_zero : normSq laguerreMeasure 0 = 1 := by
  rw [normSq, family_zero, integral_laguerreMeasure]
  have h := Polynomial.integral_exp_neg_mul_pow 0
  simpa using h

/-- **The Laguerre weight is a weight**: its moments are the Gamma integrals `n!`, and it is a
nonzero measure absolutely continuous with respect to Lebesgue measure.

Reference: [quarteroni2000numerical] §10.5. -/
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

/-- **The Laguerre weight gives no mass outside `(0, ∞)`**: it is a density against Lebesgue
measure restricted to `(0, ∞)`. -/
theorem laguerreMeasure_compl_Ioi : laguerreMeasure (Ioi (0 : ℝ))ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply' measurableSet_Ioi, Set.compl_inter_self, measure_empty]

/-- Almost every point for the Laguerre weight is nonnegative. -/
theorem laguerreMeasure_ae_nonneg : ∀ᵐ t ∂laguerreMeasure, (0 : ℝ) ≤ t := by
  have h : ∀ᵐ t ∂laguerreMeasure, t ∈ Ioi (0 : ℝ) := by
    rw [MeasureTheory.ae_iff]; exact laguerreMeasure_compl_Ioi
  filter_upwards [h] with t ht using le_of_lt ht

/-- **The monic orthogonal polynomials of the Laguerre weight are `(-1)^n ℒ_n`**, so the
Gauss–Laguerre nodes are the zeros of `ℒ_n`.

Reference: [quarteroni2000numerical] (10.41). -/
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

/-- The squared norm of the `n`-th monic Laguerre polynomial is `(n!)²`. -/
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

/-- The monic three-term recurrence of the Laguerre family, from `Polynomial.laguerre_succ_succ`
and the leading coefficients `(-1)^n`. -/
theorem family_laguerreMeasure_recurrence (n : ℕ) :
    family laguerreMeasure (n + 2) = (X - C (2 * (n : ℝ) + 3)) * family laguerreMeasure (n + 1) -
      C (((n : ℝ) + 1) ^ 2) * family laguerreMeasure n := by
  rw [family_laguerreMeasure_eq, family_laguerreMeasure_eq, family_laguerreMeasure_eq,
    Polynomial.laguerre_succ_succ]
  simp only [map_pow, map_neg, map_one]
  ring

/-- The recurrence coefficients of the Laguerre weight, [quarteroni2000numerical] §10.6
(Program 83): `α_k = 2k + 1`. -/
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

/-- The recurrence coefficients of the Laguerre weight, [quarteroni2000numerical] §10.6
(Program 83): `β_k = (k + 1)²`. -/
theorem beta_laguerreMeasure (k : ℕ) : beta laguerreMeasure k = ((k : ℝ) + 1) ^ 2 :=
  (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_laguerreMeasure
    (family_laguerreMeasure_recurrence k)).2

/-- **The recurrence coefficients of the Laguerre weight** (Program 83 of
[quarteroni2000numerical] §10.6): `α_k = 2k + 1`, `β_k = (k + 1)²`, and the total mass is `1`. -/
theorem alpha_beta_laguerreMeasure :
    (∀ k, alpha laguerreMeasure k = 2 * k + 1) ∧ (∀ k, beta laguerreMeasure k = ((k : ℝ) + 1) ^ 2)
      ∧ normSq laguerreMeasure 0 = 1 :=
  ⟨alpha_laguerreMeasure, beta_laguerreMeasure, normSq_laguerreMeasure_zero⟩

/-! ### The Hermite polynomials -/

end OrthogonalPolynomial

namespace Polynomial

/-- **The physicists' Hermite polynomials** `H_n = (-1)^n e^{x²} (d/dx)^n e^{-x²}`, defined as
Mathlib defines the probabilists' `Polynomial.hermite`, by the operator recursion
`H_0 = 1`, `H_{n+1} = 2X H_n - H_n'`. They have leading coefficient `2^n`, satisfy the three-term
recurrence `H_{n+2} = 2X H_{n+1} - 2(n + 1) H_n` (`Polynomial.physHermite_succ_succ`) and
Rodrigues' formula `Polynomial.physHermite_eq_deriv_gaussian`, and are related to Mathlib's
family by `H_n(x) = 2^{n/2} He_n(√2 x)`.

Reference: [quarteroni2000numerical] §10.5. -/
def physHermite : ℕ → ℝ[X]
  | 0 => 1
  | (n + 1) => 2 * X * physHermite n - derivative (physHermite n)

@[simp]
theorem physHermite_zero : physHermite 0 = 1 := rfl

theorem physHermite_succ (n : ℕ) :
    physHermite (n + 1) = 2 * X * physHermite n - derivative (physHermite n) := rfl

@[simp]
theorem physHermite_one : physHermite 1 = 2 * X := by
  rw [physHermite_succ, physHermite_zero, derivative_one]
  ring

/-- `H_{n+1}' = 2(n + 1) H_n`. -/
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

/-- The three-term recurrence of the physicists' Hermite polynomials,
`H_{n+2} = 2X H_{n+1} - 2(n + 1) H_n`.

Reference: [quarteroni2000numerical] §10.5. -/
theorem physHermite_succ_succ (n : ℕ) :
    physHermite (n + 2) = 2 * X * physHermite (n + 1) - C (2 * ((n : ℝ) + 1)) * physHermite n := by
  rw [physHermite_succ (n + 1), derivative_physHermite_succ]

/-- The degree and leading coefficient of `H_n`. -/
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

/-- `H_n` has degree `n`. -/
@[simp]
theorem degree_physHermite (n : ℕ) : (physHermite n).degree = n :=
  (degree_leadingCoeff_physHermite_aux n).1

/-- `H_n` has leading coefficient `2^n`. -/
@[simp]
theorem leadingCoeff_physHermite (n : ℕ) : (physHermite n).leadingCoeff = 2 ^ n :=
  (degree_leadingCoeff_physHermite_aux n).2

theorem natDegree_physHermite (n : ℕ) : (physHermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_physHermite n)

/-! #### The Rodrigues formula -/

/-- The operator `f ↦ 2X f - f'`, whose `n`-th iterate on `1` is `H_n`. -/
private def herS (f : ℝ[X]) : ℝ[X] := 2 * X * f - derivative f

private theorem physHermite_eq_iterate_herS (n : ℕ) : physHermite n = herS^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, physHermite_succ]; rfl

/-- `-e^{-x²} (S f)(x)` is the derivative of `e^{-x²} f(x)`. -/
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

/-- **Rodrigues' formula for the physicists' Hermite polynomials**:
`H_n(x) = (-1)^n e^{x²} (d/dx)^n e^{-x²}`.

Reference: [quarteroni2000numerical] §10.5. -/
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

/-! #### Orthogonality -/

/-- A polynomial times `e^{-x²}` is integrable on `ℝ`. -/
private theorem integrable_eval_mul_exp_neg_sq (p : ℝ[X]) :
    Integrable fun x => p.eval x * exp (-x ^ 2) := by
  have hmono : ∀ i : ℕ, Integrable fun x : ℝ => x ^ i * exp (-x ^ 2) := by
    intro i
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := i) (by
      exact_mod_cast (by omega : -1 < (i : ℤ)))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp [rpow_natCast]
  have heq : (fun x => p.eval x * exp (-x ^ 2)) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x ^ 2)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (hmono i).const_mul _

/-- `x^i e^{-x²}` tends to `0` at `+∞`. -/
private theorem tendsto_pow_mul_exp_neg_sq_atTop (i : ℕ) :
    Tendsto (fun x : ℝ => x ^ i * exp (-x ^ 2)) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun x : ℝ => (1 / 2) * x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hexp : Tendsto (fun x : ℝ => exp (-(1 / 2) * x)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp hhalf
    refine this.congr fun x => ?_
    simp only [Function.comp_apply, neg_mul]
  have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg one_pos (i : ℝ)).trans_tendsto hexp
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp [rpow_natCast]

/-- A polynomial times `e^{-x²}` tends to `0` at `+∞`. -/
private theorem tendsto_eval_mul_exp_neg_sq_atTop (p : ℝ[X]) :
    Tendsto (fun x => p.eval x * exp (-x ^ 2)) atTop (𝓝 0) := by
  have heq : (fun x => p.eval x * exp (-x ^ 2)) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x ^ 2)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  have h : Tendsto (fun x => ∑ i ∈ Finset.range (p.natDegree + 1),
      p.coeff i * (x ^ i * exp (-x ^ 2))) atTop (𝓝 (∑ i ∈ Finset.range (p.natDegree + 1),
      p.coeff i * 0)) :=
    tendsto_finsetSum _ fun i _ => (tendsto_pow_mul_exp_neg_sq_atTop i).const_mul _
  simpa using h

/-- A polynomial times `e^{-x²}` tends to `0` at `-∞`, by symmetry. -/
private theorem tendsto_eval_mul_exp_neg_sq_atBot (p : ℝ[X]) :
    Tendsto (fun x => p.eval x * exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := (tendsto_eval_mul_exp_neg_sq_atTop (p.comp (-X))).comp tendsto_neg_atBot_atTop
  refine h.congr fun x => ?_
  simp [eval_comp]

/-- **One integration by parts on `ℝ`**: for polynomials `p`, `q`,
`∫ p e^{-x²} (S q) = ∫ p' e^{-x²} q`, since `e^{-x²} S q = -(e^{-x²} q)'` and the boundary terms
vanish. -/
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

/-- `∫ p e^{-x²} (S^k 1) = ∫ p^{(k)} e^{-x²}`: `k` integrations by parts. -/
private theorem integral_eval_mul_exp_neg_sq_mul_iterate_herS (k : ℕ) (p : ℝ[X]) :
    ∫ x, p.eval x * (exp (-x ^ 2) * (herS^[k] 1).eval x) =
      ∫ x, (derivative^[k] p).eval x * exp (-x ^ 2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', integral_eval_mul_exp_neg_sq_mul_herS, ih,
      Function.iterate_succ_apply]

/-- `∫ p H_n e^{-x²} = ∫ p^{(n)} e^{-x²}` for every polynomial `p`. -/
private theorem integral_eval_mul_physHermite_mul_exp_neg_sq (p : ℝ[X]) (n : ℕ) :
    ∫ x, p.eval x * (physHermite n).eval x * exp (-x ^ 2) =
      ∫ x, (derivative^[n] p).eval x * exp (-x ^ 2) := by
  rw [← integral_eval_mul_exp_neg_sq_mul_iterate_herS n p, ← physHermite_eq_iterate_herS]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

/-- **Orthogonality of the physicists' Hermite polynomials** on `ℝ` for the weight `e^{-x²}`,
with the norms `∫ H_n² e^{-x²} = 2^n n! √π`.

By `n` integrations by parts, `∫ H_m H_n e^{-x²} = ∫ H_m^{(n)} e^{-x²}`, which vanishes for
`m < n` and equals `2^n n! ∫ e^{-x²} = 2^n n! √π` for `m = n`.

Reference: [quarteroni2000numerical] §10.5. -/
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
    rw [integral_eval_mul_physHermite_mul_exp_neg_sq, iterate_derivative_natDegree_eq_C
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

/-- The Hermite weight `e^{-x²}` on `ℝ`.

Reference: [quarteroni2000numerical] §10.5. -/
def hermiteMeasure : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (exp (-x ^ 2))

/-- An integral against the Hermite weight. -/
theorem integral_hermiteMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂hermiteMeasure = ∫ x, exp (-x ^ 2) * f x :=
  integral_withDensity_ofReal (by fun_prop) (Eventually.of_forall fun x => (exp_pos _).le) f

/-- Integrability for the Hermite weight. -/
theorem integrable_hermiteMeasure_iff (f : ℝ → ℝ) :
    Integrable f hermiteMeasure ↔ Integrable fun x => exp (-x ^ 2) * f x :=
  integrable_withDensity_ofReal_iff (by fun_prop) (Eventually.of_forall fun x => (exp_pos _).le) f

/-- The Hermite weight has total mass `√π`. -/
theorem normSq_hermiteMeasure_zero : normSq hermiteMeasure 0 = √π := by
  rw [normSq, family_zero, integral_hermiteMeasure]
  have hg := integral_gaussian 1
  simp only [neg_one_mul, div_one] at hg
  simpa using hg

/-- **The Hermite weight is a weight**: its moments are finite Gaussian integrals, and it is a
nonzero measure absolutely continuous with respect to Lebesgue measure.

Reference: [quarteroni2000numerical] §10.5. -/
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

/-- **The monic orthogonal polynomials of the Hermite weight are `2^{-n} H_n`**, so the
Gauss–Hermite nodes are the zeros of `H_n`.

Reference: [quarteroni2000numerical] (10.42). -/
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

/-- The squared norm of the `n`-th monic Hermite polynomial is `n! √π / 2^n`. -/
theorem normSq_hermiteMeasure (n : ℕ) : normSq hermiteMeasure n = (n ! : ℝ) * √π / 2 ^ n := by
  rw [normSq_eq_of_family_eq (family_hermiteMeasure_eq n), integral_hermiteMeasure]
  have h := Polynomial.integral_physHermite_mul_physHermite n n
  rw [ite_eq_left rfl] at h
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [show ∫ x, exp (-x ^ 2) * (Polynomial.physHermite n).eval x ^ 2 =
      ∫ x, (Polynomial.physHermite n).eval x * (Polynomial.physHermite n).eval x * exp (-x ^ 2)
      from integral_congr_ae (Eventually.of_forall fun x => by ring), h]
  field_simp

/-- The monic three-term recurrence of the Hermite family, from `Polynomial.physHermite_succ_succ`
and the leading coefficients `2^n`. -/
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

/-- The recurrence coefficients of the Hermite weight, [quarteroni2000numerical] §10.6
(Program 84): `α_k = 0`. -/
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

/-- The recurrence coefficients of the Hermite weight, [quarteroni2000numerical] §10.6
(Program 84): `β_k = (k + 1) / 2`. -/
theorem beta_hermiteMeasure (k : ℕ) : beta hermiteMeasure k = ((k : ℝ) + 1) / 2 :=
  (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_hermiteMeasure
    (family_hermiteMeasure_recurrence k)).2

/-- **The recurrence coefficients of the Hermite weight** (Program 84 of
[quarteroni2000numerical] §10.6): `α_k = 0`, `β_k = (k + 1)/2`, and the total mass is `√π`. -/
theorem alpha_beta_hermiteMeasure :
    (∀ k, alpha hermiteMeasure k = 0) ∧ (∀ k, beta hermiteMeasure k = ((k : ℝ) + 1) / 2) ∧
      normSq hermiteMeasure 0 = √π :=
  ⟨alpha_hermiteMeasure, beta_hermiteMeasure, normSq_hermiteMeasure_zero⟩

/-! ### The recurrence coefficients of the Legendre weight -/

/-- The leading coefficients of consecutive Legendre polynomials: `lc(L_{n+1}) = (2n+1)/(n+1)
lc(L_n)`, read off the three-term recurrence. -/
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
    have hpos : ((n : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    linear_combination h

/-- The monic three-term recurrence of the Legendre family, from `Polynomial.legendre_recurrence`
and the leading coefficients. -/
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

/-- The recurrence coefficients of the Legendre weight, [quarteroni2000numerical] §10.6
(Program 82): `α_k = 0`. -/
theorem alpha_legendreMeasure (k : ℕ) : alpha legendreMeasure k = 0 := by
  cases k with
  | zero =>
    refine alpha_zero_eq_of_family_one ?_
    rw [family_eq_legendre, Polynomial.legendre_one]
    simp
  | succ k =>
    exact (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_legendreMeasure
      (family_legendreMeasure_recurrence k)).1

/-- The recurrence coefficients of the Legendre weight, [quarteroni2000numerical] §10.6
(Program 82): `β_k = (k+1)² / (4(k+1)² - 1)`. -/
theorem beta_legendreMeasure (k : ℕ) :
    beta legendreMeasure k = ((k : ℝ) + 1) ^ 2 / (4 * ((k : ℝ) + 1) ^ 2 - 1) :=
  (alpha_succ_eq_and_beta_eq_of_recurrence isWeight_legendreMeasure
    (family_legendreMeasure_recurrence k)).2

/-- The squared norm of the `n`-th monic Legendre polynomial, `2 / ((2n + 1) lc(L_n)²)`. -/
theorem normSq_legendreMeasure (n : ℕ) :
    normSq legendreMeasure n =
      2 / ((2 * (n : ℝ) + 1) * (Polynomial.legendre n).leadingCoeff ^ 2) := by
  rw [normSq_eq_of_family_eq (family_eq_legendre n), integral_legendreMeasure,
    Polynomial.integral_legendre_sq]
  have hlc : (Polynomial.legendre n).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero n)
  have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The Legendre weight has total mass `2`. -/
theorem normSq_legendreMeasure_zero : normSq legendreMeasure 0 = 2 := by
  rw [normSq, family_zero, integral_legendreMeasure]
  simp
  norm_num

/-- **The recurrence coefficients of the Legendre weight** (Program 82 of
[quarteroni2000numerical] §10.6): `α_k = 0`, `β_k = (k+1)²/(4(k+1)² - 1)`, and the total mass is
`2`. -/
theorem alpha_beta_legendreMeasure :
    (∀ k, alpha legendreMeasure k = 0) ∧
      (∀ k, beta legendreMeasure k = ((k : ℝ) + 1) ^ 2 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) ∧
        normSq legendreMeasure 0 = 2 :=
  ⟨alpha_legendreMeasure, beta_legendreMeasure, normSq_legendreMeasure_zero⟩

end OrthogonalPolynomial

end
