/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.OrthogonalPolynomial

/-!
# Atkinson and Han, Section 3.5: Orthogonal polynomials

This module formalizes §3.5 of [han2009theoretical], the catalogue of orthogonal polynomial families
that §3.7 and Chapter 5 cite. A weight function $w$ on $(-1, 1)$ defines the Hilbert space
$L^2_w(-1, 1)$ with inner product $(u, v)_w = \int_{-1}^{1} w(x) u(x) v(x)\, dx$ (3.5.1). Its
orthogonal polynomials $p_0, p_1, \ldots$ give the best approximation
$P_N u = \sum_{n \le N} \xi_n p_n$, $\xi_n = (u, p_n)_w / \|p_n\|_w^2$, of $u$ by polynomials of
degree at most $N$ (3.5.2). The two families stated here are the Legendre polynomials $P_n$, with
weight $w = 1$, and the Chebyshev polynomials $T_n(x) = \cos(n \arccos x)$, with weight
$(1 - x^2)^{-1/2}$.

The section has no numbered theorem, so the declarations state selected displayed formulas
from (3.5.1)–(3.5.9). The proofs specialize
`Numlib.Approximation.OrthogonalPolynomial`,
where the family of orthogonal polynomials of a measure is defined.

## Main definitions

* Equation (3.5.1), `AtkinsonHan.Chapter03.weightMeasure`: the measure $w(x)\, dx$ on $(-1, 1)$,
  whose $L^2$ space is $L^2_w(-1, 1)$.

## Main results

* Equation (3.5.1), `AtkinsonHan.Chapter03.isWeight_weightMeasure`: a measurable weight that is
  positive and integrable on $(-1, 1)$ satisfies the backbone's standing hypothesis
  `OrthogonalPolynomial.IsWeight`.
* Equations (3.5.1)–(3.5.2), `AtkinsonHan.Chapter03.equation_3_5_2`: $L^2_w(-1, 1)$ is a Hilbert
  space, and the truncated orthogonal expansion $P_N u$ is the best approximation of $u$ by
  polynomials of degree at most $N$.
* Equations (3.5.3)–(3.5.6), `AtkinsonHan.Chapter03.equation_3_5_5`: the Legendre polynomials
  satisfy the Rodrigues formula, the orthogonality relation, the three-term recursion and the
  Legendre differential equation.
* Equations (3.5.8)–(3.5.9), `AtkinsonHan.Chapter03.equation_3_5_9`: the Chebyshev polynomials
  satisfy $T_n(x) = \cos(n \arccos x)$, the orthogonality relation and the three-term recursion.

## Conventions

* The book's weight function, positive almost everywhere and integrable, is a measure here:
  `AtkinsonHan.Chapter03.weightMeasure w` is $w(x)\, dx$ restricted to $(-1, 1)$. The backbone's
  standing hypothesis on such a measure is `OrthogonalPolynomial.IsWeight`: all moments are finite
  and no finite set carries the whole mass. `AtkinsonHan.Chapter03.isWeight_weightMeasure` derives
  it from the pointwise-positive variant of the book's hypotheses on $w$.
* The book's $L^2_w(-1, 1)$ is `Lp ℝ 2 (AtkinsonHan.Chapter03.weightMeasure w)`.

## Deviations from the source

* **Equations (3.5.1)–(3.5.2)** (reading). The weight measure truncates negative values at zero.
  The sufficient criterion for a weight assumes positivity at every interior point, while the
  book assumes it almost everywhere. The projection uses a monic orthogonal polynomial family.

## Not formalized

* **The general Jacobi weight family (3.5.3).** The sheet treats the Legendre and Chebyshev cases.

* **The Sobolev norm error estimates for $P_N u$ and $P_{1,N} u$ quoted after (3.5.2) and (3.5.7).**
  They need the Sobolev spaces $H^s(-1, 1)$, and the book refers the reader elsewhere for them.
-/

open MeasureTheory Polynomial Real

open scoped Nat

namespace AtkinsonHan.Chapter03

/-! ### The weighted space (3.5.1) -/

/-- **Equation (3.5.1)** of [han2009theoretical]. For a function $w : \mathbb{R} \to \mathbb{R}$,
the **weighted measure** $w(x)\, dx$ on the interval $(-1, 1)$. The book's weighted space
$L^2_w(-1, 1)$ is the $L^2$ space of this measure, `Lp ℝ 2 (weightMeasure w)`.

The density is $\max\{w(x), 0\}$, through `ENNReal.ofReal`, so negative values of $w$ count as
$0$. For a weight in the book's sense, $w > 0$ on $(-1, 1)$, this makes no difference.

**Reading.** The definition extends the source's positive weights by truncating negative
values to zero. For a source weight, the density agrees with $w$ almost everywhere. -/
noncomputable def weightMeasure (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity fun x => ENNReal.ofReal (w x)

/-- **Equation (3.5.1)** of [han2009theoretical], the hypotheses on the weight. Let
$w : \mathbb{R} \to \mathbb{R}$ be measurable, with $w(x) > 0$ for all $x \in (-1, 1)$ and $w$
integrable on $(-1, 1)$. Then the measure $w(x)\, dx$ on $(-1, 1)$ satisfies the backbone's
standing hypothesis `OrthogonalPolynomial.IsWeight`: all its moments are finite and no finite
set carries all its mass. So the weight has a family of orthogonal polynomials.

**Reading.** The book asks for positivity almost everywhere and integrability on the
interval. This sufficient-condition theorem assumes pointwise positivity in the interior
and global measurability. -/
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

/-- **Equations (3.5.1)–(3.5.2)** of [han2009theoretical]. Let $w$ be a weight on $(-1, 1)$ whose
measure $w(x)\, dx$ satisfies `OrthogonalPolynomial.IsWeight`, and let $p_0, p_1, \ldots$ be its
monic orthogonal polynomials. Then $L^2_w(-1, 1)$ is complete, and for every
$u \in L^2_w(-1, 1)$ and $N \ge 0$ the truncated expansion
$$P_N u = \sum_{n=0}^{N} \xi_n p_n, \qquad \xi_n = \frac{(u, p_n)_w}{\|p_n\|_w^2},$$
is a best approximation of $u$ from the polynomials of degree at most $N$.

The book notes that this is an instance of (3.4.6), which is
`AtkinsonHan.Chapter03.equation_3_4_6`. The polynomials $p_n$ are `OrthogonalPolynomial.family
(weightMeasure w) n`, and $\|p_n\|_w^2$ is `OrthogonalPolynomial.normSq (weightMeasure w) n`.

**Reading.** The declaration uses the backbone's measure hypotheses and the monic
orthogonal polynomial family. The formula for the projection is independent of this
normalization. -/
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

/-- **Equations (3.5.3)–(3.5.6)** of [han2009theoretical], the Legendre polynomials. Let
$m, n \ge 0$. Then

* the Jacobi weight with $\alpha = \beta = 0$ is the Lebesgue measure on $(-1, 1)$;
* the Legendre polynomial is given by the Rodrigues formula (3.5.4), $P_n(x) = \dfrac{1}{2^n n!}
  \dfrac{d^n}{dx^n} (x^2 - 1)^n$;
* $P_n$ divided by its leading coefficient is the $n$-th monic orthogonal polynomial of that
  weight;
* $\int_{-1}^{1} P_m(x) P_n(x)\, dx = \dfrac{2}{2n + 1} \delta_{mn}$ (3.5.5);
* $(n + 2) P_{n+2}(x) = (2n + 3)\, x P_{n+1}(x) - (n + 1) P_n(x)$ (3.5.6);
* $(x^2 - 1) P_n''(x) + 2x P_n'(x) = n(n + 1) P_n(x)$, the Legendre differential equation.

The recursion is stated with the index shifted so that all indices are natural numbers. $P_n$ is
`Polynomial.legendre n`, and the Lebesgue measure on $(-1, 1)$ is
`OrthogonalPolynomial.legendreMeasure`. -/
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

/-- **Equations (3.5.8)–(3.5.9)** of [han2009theoretical], the Chebyshev polynomials. Let
$m, n \ge 0$ and let $T_n$ be the Chebyshev polynomial of the first kind. Then

* $T_n(x) = \cos(n \arccos x)$ for $x \in [-1, 1]$;
* $T_m$ and $T_n$ satisfy the unnumbered orthogonality relation below for the weight
  $(1 - x^2)^{-1/2}$;
* $T_{n+2}(x) = 2x\, T_{n+1}(x) - T_n(x)$, the recurrence (3.5.9).

The orthogonality relation is
$$\int_{-1}^{1} \frac{T_m(x) T_n(x)}{\sqrt{1 - x^2}}\, dx
  = \begin{cases} 0, & m \neq n, \\ \pi, & m = n = 0, \\ \pi/2, & m = n \ge 1. \end{cases}$$

The book writes the orthogonality relation as $(T_m, T_n)_w = (\pi/2)\, c_n \delta_{mn}$ with
$c_0 = 2$ and $c_n = 1$ for $n \ge 1$. $T_n$ is Mathlib's `Polynomial.Chebyshev.T ℝ n`. -/
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

end AtkinsonHan.Chapter03
