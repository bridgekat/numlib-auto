import Numlib.Approximation.OrthogonalPolynomial

/-!
# Atkinson–Han §3.5: orthogonal polynomials

Statements from Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework* (3rd ed.), §3.5.

The section states no numbered result — it is the book's catalogue of the families that §3.7 and
Chapter 5 cite — so the nodes here are the displayed formulas (3.5.1)–(3.5.9). They rest on the
backbone `Numlib/Approximation/OrthogonalPolynomial`, where the family attached to a measure lives.

## Main results

* `weightMeasure`, `isWeight_weightMeasure` — the weighted space `L²_w(-1, 1)` of (3.5.1), and the
  fact that a positive integrable weight satisfies the backbone's `IsWeight`.
* `equation_3_5_2` — `L²_w(-1, 1)` is a Hilbert space, and the truncated expansion is the best
  approximation from `𝒫_N`. The book notes that this is an instance of (3.4.6), which is
  `equation_3_4_6` of §3.4.
* `equation_3_5_5` — the Legendre family: the Jacobi weight at `α = β = 0`, the Rodrigues formula
  (3.5.4), orthogonality (3.5.5), the recursion (3.5.6), and the Legendre differential equation.
* `equation_3_5_9` — the Chebyshev family: `Tₙ(x) = cos (n arccos x)`, the orthogonality (3.5.9)
  for the weight `(1 - x²)^{-1/2}`, and the recursion `T_{n+1} = 2 x Tₙ - T_{n-1}`.

## Conventions

The book's "weight function" — `w > 0` and integrable on `(-1, 1)` — is a measure here,
`weightMeasure w = w(x) dx` restricted to `(-1, 1)`, and the backbone's standing hypothesis on it
is `OrthogonalPolynomial.IsWeight`: finite moments and no finite set carrying the whole mass.
`isWeight_weightMeasure` is the bridge, so the book's hypotheses are what the reader supplies.

## Not formalized here

The Sobolev-norm error estimates for `P_N u` and `P_{1,N} u` quoted after (3.5.2) and (3.5.7):
they need `Hˢ(-1, 1)`, and the book itself refers the reader elsewhere for them.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/

open MeasureTheory Polynomial Real

open scoped Nat

namespace AtkinsonHan.Ch03

/-! ### The weighted space (3.5.1) -/

/-- **(3.5.1)**, the weighted space `L²_w(-1, 1)`: the measure `w(x) dx` on the interval `(-1, 1)`,
of which the book's `L²_w(-1, 1)` is the `L²` space, `Lp ℝ 2 (weightMeasure w)`. -/
noncomputable def weightMeasure (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity fun x => ENNReal.ofReal (w x)

/-- A weight function in the book's sense — measurable, positive on `(-1, 1)` and integrable
there — gives a measure satisfying the backbone's standing hypothesis
`OrthogonalPolynomial.IsWeight`, so it has a family of orthogonal polynomials. -/
theorem isWeight_weightMeasure {w : ℝ → ℝ} (hmeas : Measurable w)
    (hpos : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < w x)
    (hint : IntegrableOn w (Set.Ioo (-1 : ℝ) 1)) :
    OrthogonalPolynomial.IsWeight (weightMeasure w) := by
  have hmeasE : Measurable fun x => ENNReal.ofReal (w x) := hmeas.ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)), ENNReal.ofReal (w x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  constructor
  · intro n
    rw [weightMeasure, integrable_withDensity_iff hmeasE hlt]
    have hae : (fun x : ℝ => x ^ n * (ENNReal.ofReal (w x)).toReal)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x => x ^ n * w x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [ENNReal.toReal_ofReal (hpos x hx).le]
    refine Integrable.congr ?_ hae.symm
    refine Integrable.mono' hint.abs
      (((continuous_pow n).measurable.mul hmeas).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx1 : |x| ≤ 1 := abs_le.2 ⟨hx.1.le, hx.2.le⟩
    calc ‖x ^ n * w x‖ = |x| ^ n * |w x| := by
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
      _ ≤ 1 ^ n * |w x| := by gcongr
      _ = |w x| := by rw [one_pow, one_mul]
  · intro s hs hzero
    have hsc : MeasurableSet sᶜ := hs.measurableSet.compl
    have hinter : MeasurableSet (sᶜ ∩ Set.Ioo (-1 : ℝ) 1) := hsc.inter measurableSet_Ioo
    have hvol : volume (sᶜ ∩ Set.Ioo (-1 : ℝ) 1) ≠ 0 := by
      rw [show sᶜ ∩ Set.Ioo (-1 : ℝ) 1 = Set.Ioo (-1 : ℝ) 1 \ s by ext x; simp [and_comm],
        measure_sdiff_null (hs.measure_zero volume), Real.volume_Ioo]
      norm_num
    rw [weightMeasure, withDensity_apply _ hsc, Measure.restrict_restrict hsc,
      lintegral_eq_zero_iff hmeasE] at hzero
    have hfalse : ∀ᵐ x ∂(volume.restrict (sᶜ ∩ Set.Ioo (-1 : ℝ) 1)), False := by
      filter_upwards [hzero, ae_restrict_mem hinter] with x hx hxmem
      rw [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
      exact absurd hx (not_le.mpr (hpos x hxmem.2))
    refine hvol ?_
    rw [← Measure.restrict_eq_zero]
    exact ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse)

/-- **(3.5.1)–(3.5.2).** The weighted space `L²_w(-1, 1)` is a Hilbert space, and the truncated
expansion `P_N u = ∑_{n ≤ N} ξₙ pₙ`, with `ξₙ = (u, pₙ)_w / ‖pₙ‖²_w` in the orthogonal polynomials
of the weight, is the best approximation of `u` from the polynomials of degree at most `N`. The
book notes that this is an instance of (3.4.6), which is `equation_3_4_6`. -/
theorem equation_3_5_2 {w : ℝ → ℝ} (hw : OrthogonalPolynomial.IsWeight (weightMeasure w)) (N : ℕ)
    (u : Lp ℝ 2 (weightMeasure w)) :
    CompleteSpace (Lp ℝ 2 (weightMeasure w)) ∧
      IsBestApprox
        (↑(Submodule.map hw.toLpₗ (Polynomial.degreeLE ℝ (N : WithBot ℕ))) :
          Set (Lp ℝ 2 (weightMeasure w))) u
        (∑ k : Fin (N + 1),
          (inner ℝ (hw.toLpₗ (OrthogonalPolynomial.family (weightMeasure w) k)) u /
              OrthogonalPolynomial.normSq (weightMeasure w) k) •
            hw.toLpₗ (OrthogonalPolynomial.family (weightMeasure w) k)) :=
  ⟨inferInstance, OrthogonalPolynomial.isBestApprox_truncation hw N u⟩

/-! ### The Legendre family -/

/-- **(3.5.3)–(3.5.6)**, the Legendre family. The Jacobi weight at `α = β = 0` is Lebesgue measure
on `(-1, 1)`; the Rodrigues formula (3.5.4) `Pₙ = (2ⁿ n!)⁻¹ (d/dx)ⁿ (x² - 1)ⁿ` defines `Pₙ`, whose
monic rescaling is the `n`-th orthogonal polynomial of that weight; the `Pₙ` are orthogonal with
`(Pₘ, Pₙ)₀ = 2 δₘₙ/(2n + 1)` (3.5.5); and they satisfy the recursion (3.5.6) and the Legendre
differential equation. -/
theorem equation_3_5_5 (m n : ℕ) :
    OrthogonalPolynomial.legendreMeasure = volume.restrict (Set.Ioo (-1 : ℝ) 1) ∧
      legendre n = C ((2 ^ n * n ! : ℝ)⁻¹) * derivative^[n] ((X ^ 2 - 1) ^ n) ∧
      OrthogonalPolynomial.family OrthogonalPolynomial.legendreMeasure n =
        C ((legendre n).leadingCoeff)⁻¹ * legendre n ∧
      (∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x) =
        (if m = n then 2 / (2 * (n : ℝ) + 1) else 0) ∧
      ((n : ℝ[X]) + 2) * legendre (n + 2) =
        (2 * (n : ℝ[X]) + 3) * X * legendre (n + 1) - ((n : ℝ[X]) + 1) * legendre n ∧
      (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (legendre n)) + 2 * X * derivative (legendre n) =
        (n : ℝ[X]) * ((n : ℝ[X]) + 1) * legendre n :=
  ⟨rfl, rfl, OrthogonalPolynomial.family_eq_legendre n, integral_legendre_mul_legendre m n,
    legendre_recurrence n, legendre_ode n⟩

/-! ### The Chebyshev family -/

/-- **(3.5.8)–(3.5.9)**, the Chebyshev family. For the weight `(1 - x²)^{-1/2}` the orthogonal
polynomials are `Tₙ(x) = cos (n arccos x)`, with `(Tₘ, Tₙ)_w = (π/2) cₙ δₘₙ` where `c₀ = 2` and
`cₙ = 1` for `n ≥ 1` (3.5.9), and they satisfy the recursion `T_{n+1} = 2 x Tₙ - T_{n-1}`. -/
theorem equation_3_5_9 (m n : ℕ) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, (Chebyshev.T ℝ n).eval x = Real.cos (n * Real.arccos x)) ∧
      (∫ x in (-1 : ℝ)..1,
          (Chebyshev.T ℝ m).eval x * (Chebyshev.T ℝ n).eval x / √(1 - x ^ 2)) =
        (if m ≠ n then 0 else if n = 0 then π else π / 2) ∧
      Chebyshev.T ℝ ((n : ℤ) + 2) =
        2 * X * Chebyshev.T ℝ ((n : ℤ) + 1) - Chebyshev.T ℝ (n : ℤ) := by
  refine ⟨fun x hx => ?_, Chebyshev.integral_T_mul_T_div_sqrt m n, Chebyshev.T_add_two ℝ n⟩
  rw [← Real.cos_arccos hx.1 hx.2, Chebyshev.T_real_cos, Real.cos_arccos hx.1 hx.2]
  norm_cast

end AtkinsonHan.Ch03
