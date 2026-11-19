/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Numlib.Approximation.OrthogonalPolynomial.Classical
import Numlib.Approximation.SingularIntegral
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section07

/-!
# Quarteroni, Sacco and Saleri, Section 9.8: Singular integrals

This module formalizes Section 9.8 of [quarteroni2000numerical], on three kinds of singular
integral. A function with a *finite jump* at a known interior point $c$ (Section 9.8.1) is handled
by (9.46), $\int_a^b f = \int_a^c f + \int_c^b f$, and any formula of the previous sections on the
two pieces. An *integrable endpoint singularity* (Section 9.8.2), $f(x) = \varphi(x)/(x - a)^\mu$
with $0 \le \mu < 1$ and $|\varphi| \le M$, obeys the a priori bound
$|I(f)| \le M (b - a)^{1-\mu}/(1 - \mu)$. Method 1 replaces the singular piece
$I_1 = \int_a^{a+\varepsilon} f$ by the closed form of the integral of the Taylor polynomial of
$\varphi$ (9.47)–(9.48), and applies a composite Newton–Cotes formula to the remaining
$I_2 = \int_{a+\varepsilon}^b f$ (9.49). Method 2 subtracts the Taylor polynomial $\Phi_p$ on the
whole interval: it integrates $\Phi_p/(x - a)^\mu$ exactly (9.51) and leaves the regularized
integrand (9.52). Example 9.10 evaluates the Fresnel integral $\int_0^{\pi/2} \cos x/\sqrt{x}\,dx$
by integrating its Taylor series term by term. On an *unbounded interval* (Section 9.8.3),
(9.53)–(9.54) define the improper integral, the decay condition $x^{1+\rho} f(x) \to 0$ makes a
continuous $f$ integrable, Method 2 is the substitution $x = 1/t$ (9.55), and Method 3 is
Gauss–Laguerre and Gauss–Hermite quadrature.

The backbone is `Numlib.Approximation.SingularIntegral` for Sections 9.8.2–9.8.3, in the namespace
`Quadrature`; `Numlib.Approximation.NewtonCotes` through
`QuarteroniSaccoSaleri.Chapter09.theorem_9_3_even` of Section 9.4; and the Laguerre and Hermite
weights of `Numlib.Approximation.OrthogonalPolynomial.Classical` together with
`Quadrature.exists_gauss`.

## Main results

* Equation (9.46), `QuarteroniSaccoSaleri.Chapter09.equation_9_46`: additivity of the integral at a
  jump, for a function continuous on $[a, c)$ and on $(c, b]$ and bounded.
* Section 9.8.2, `QuarteroniSaccoSaleri.Chapter09.singularIntegral_bound`: the a priori bound
  $|I(f)| \le M (b - a)^{1-\mu}/(1 - \mu)$.
* Equation (9.47), `QuarteroniSaccoSaleri.Chapter09.equation_9_47`: Taylor's formula with the
  Lagrange remainder.
* Section 9.8.2, `QuarteroniSaccoSaleri.Chapter09.integral_taylorSum_div_rpow`: the closed form of
  $\int_a^b \Phi_p(x)/(x - a)^\mu\,dx$.
* Equation (9.48), `QuarteroniSaccoSaleri.Chapter09.equation_9_48`: the truncation error of
  Method 1.
* Equation (9.49), `QuarteroniSaccoSaleri.Chapter09.equation_9_49`: the a priori bound on the error
  $E_2$ of the Newton–Cotes formula on $[a + \varepsilon, b]$.
* Example 9.10, `QuarteroniSaccoSaleri.Chapter09.example_9_10`: the series for the Fresnel integral
  (9.50).
* Equation (9.51), `QuarteroniSaccoSaleri.Chapter09.equation_9_51`: the exact singular part of
  Method 2.
* Equation (9.52), `QuarteroniSaccoSaleri.Chapter09.equation_9_52`: the regularized integrand
  $g(x) = (x - a)^{p+1-\mu} \varphi^{(p+1)}(\xi(x))/(p + 1)!$.
* Section 9.8.2, `QuarteroniSaccoSaleri.Chapter09.equation_9_52_regularity`: $g$, extended by $0$ at
  $a$, is of class $C^p$ on $[a, b]$, and its first $p$ derivatives vanish at $a$.
* Equation (9.53), `QuarteroniSaccoSaleri.Chapter09.equation_9_53`: the improper integral is a limit
  of proper integrals.
* Equation (9.54), `QuarteroniSaccoSaleri.Chapter09.equation_9_54`: the integral over $\mathbb{R}$
  splits at any point $c$.
* Section 9.8.3, `QuarteroniSaccoSaleri.Chapter09.integrable_of_tendsto_rpow_mul`: the decay
  condition implies integrability.
* Equation (9.55), `QuarteroniSaccoSaleri.Chapter09.equation_9_55`: the substitution $x = 1/t$.
* Section 9.8.3, `QuarteroniSaccoSaleri.Chapter09.gaussLaguerre`: Method 3 with the weight $e^{-x}$
  on $(0, \infty)$.
* Section 9.8.3, `QuarteroniSaccoSaleri.Chapter09.gaussHermite`: Method 3 with the weight $e^{-x^2}$
  on $\mathbb{R}$.

## Conventions

* As in Sections 9.2–9.4, $f \in C^k([a, b])$ is `ContDiffOn ℝ (k : ℕ) f U` for an open set
  $U \supseteq [a, b]$, so that the derivatives `iteratedDeriv k f` are the two-sided ones.
* The Taylor polynomial $\Phi_p$ of (9.47) is written as the explicit sum
  $\sum_{k=0}^{p} \varphi^{(k)}(a)(x - a)^k/k!$. The backbone knows it as
  `taylorWithinEval φ p Set.univ a` (`Quadrature.taylorWithinEval_univ_eq_sum`).
* The exponent $\mu$ of the singularity is a real number, and $(x - a)^\mu$ is `Real.rpow`.

## Deviations from the source

* **(9.46)–(9.48)** (reading). `QuarteroniSaccoSaleri.Chapter09.equation_9_46` uses boundedness
  and continuity on the two half-open intervals without assuming one-sided limits. The singular
  endpoint estimates require the integrability or regularity hypotheses stated by each theorem.
* **(9.51) and (9.52)** (generalization). `QuarteroniSaccoSaleri.Chapter09.equation_9_51`
  integrates the finite Taylor sum for all $\mu<1$.
  `QuarteroniSaccoSaleri.Chapter09.equation_9_52` uses a pointwise witness and gives the
  integral identity for every real $\mu$. The regularity theorem imposes $\mu<1$.
* **(9.53)–(9.54)** (scope). The theorems use Lebesgue integrability and therefore cover
  absolute convergence. The printed definitions also allow conditionally convergent improper
  integrals.
* **§9.8.3, Gaussian rules** (scope). `QuarteroniSaccoSaleri.Chapter09.gaussLaguerre` and
  `QuarteroniSaccoSaleri.Chapter09.gaussHermite` give existence of positive weights with
  polynomial exactness. Their statements omit the identification of the nodes as roots of the
  specified orthogonal polynomials.
* **Equation (9.49)** (scope). The bound uses the constant $|M_n|/n^{n+3}$ printed in (9.49),
  which agrees with the correction to (9.26) in Section 9.4. The choice of $m$ that sets the bound
  to $\delta/2$ remains outside `QuarteroniSaccoSaleri.Chapter09.equation_9_49`.
* **The sentence after (9.52)** (generalization). The regularity of $g$ holds for every $\mu < 1$,
  without the standing assumption $0 \le \mu$ of the source. See
  `QuarteroniSaccoSaleri.Chapter09.equation_9_52_regularity`.
* **Equation (9.55)** (typo). The source prints $I_2 = \int_0^{1/c} f(t) t^{-2}\,dt$; the integrand
  should be $f(1/t) t^{-2}$. See `QuarteroniSaccoSaleri.Chapter09.equation_9_55`.

## Not formalized

* **The application of a composite Newton–Cotes error estimate to $I_1$ after (9.52)**, for
  $p \ge n + 2$ ($n$ even) or $p \ge n + 1$ ($n$ odd).
  `QuarteroniSaccoSaleri.Chapter09.theorem_9_3_even` asks for smoothness on an open set that
  contains $[a, b]$, while $g$ is of class $C^p$ on $[a, b]$ only, and the library has no $C^p$
  extension of $g$ across the endpoints.
* **Examples 9.11 and 9.12.** They are numerical runs.
-/

open MeasureTheory Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b c ε ρ μ : ℝ} {f φ : ℝ → ℝ} {U : Set ℝ} {n p m : ℕ}

/-! ### §9.8.1 Functions with finite jump discontinuities -/

/-- **Equation (9.46)** of [quarteroni2000numerical]. Let $a \le c \le b$, let $f$ be continuous on
$[a, c)$ and on $(c, b]$, and let $|f(x)| \le M$ for all $x \in [a, b]$. Then $f$ is integrable
on $[a, c]$ and on $[c, b]$, and
$$I(f) = \int_a^b f(x)\,dx = \int_a^c f(x)\,dx + \int_c^b f(x)\,dx.$$

Such an $f$ may have a finite jump at $c$. Any integration formula of the previous sections can
then be used on $[a, c^-]$ and on $[c^+, b]$ to approximate $I(f)$.

**Reading.** Proves interval integrability of both halves without requiring one-sided limits, with
an overall pointwise bound.
-/
theorem equation_9_46 (hac : a ≤ c) (hcb : c ≤ b) {M : ℝ} (hf₁ : ContinuousOn f (Ico a c))
    (hf₂ : ContinuousOn f (Ioc c b)) (hM : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    IntervalIntegrable f volume a c ∧ IntervalIntegrable f volume c b ∧
      ∫ x in a..b, f x = (∫ x in a..c, f x) + ∫ x in c..b, f x := by
  have h₁ : IntervalIntegrable f volume a c := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hac,
      ← integrableOn_congr_set_ae Ioo_ae_eq_Ioc]
    refine IntegrableOn.of_bound measure_Ioo_lt_top
      ((hf₁.mono Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo) M ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hM x ⟨hx.1.le, hx.2.le.trans hcb⟩
  have h₂ : IntervalIntegrable f volume c b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcb]
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      (hf₂.aestronglyMeasurable measurableSet_Ioc) M ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hM x ⟨hac.trans hx.1.le, hx.2⟩
  exact ⟨h₁, h₂, (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm⟩

/-! ### §9.8.2 Integrals of infinite functions: the a priori bound -/

/-- **Section 9.8.2** of [quarteroni2000numerical], the a priori bound. Let $a < b$ and
$0 \le \mu < 1$, let $\varphi$ be continuous on $(a, b]$, and let $|\varphi(x)| \le M$ for all
$x \in (a, b]$. Then $f(x) = \varphi(x)/(x - a)^\mu$ is integrable on $[a, b]$, and
$$|I(f)| \le M \lim_{t \to a^+} \int_t^b (x - a)^{-\mu}\,dx = \frac{M (b - a)^{1-\mu}}{1 -
  \mu}.$$

**Reading.** Adds explicit continuity on the half-open interval to justify integrability and states
bound with integrability.
-/
theorem singularIntegral_bound (hab : a < b) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hφ : ContinuousOn φ (Ioc a b)) {M : ℝ} (hM : ∀ x ∈ Ioc a b, |φ x| ≤ M) :
    IntervalIntegrable (fun x => φ x / (x - a) ^ μ) volume a b ∧
      |∫ x in a..b, φ x / (x - a) ^ μ| ≤ M * (b - a) ^ (1 - μ) / (1 - μ) :=
  ⟨Quadrature.intervalIntegrable_div_rpow hab hμ0 hμ1
      (hφ.aestronglyMeasurable measurableSet_Ioc) hM,
    Quadrature.abs_integral_div_rpow_le hab hμ1 hM⟩

/-! ### The Taylor expansion (9.47) and its exact contribution -/

/-- **Equation (9.47)** of [quarteroni2000numerical], Taylor's formula with the Lagrange remainder.
Let $\varphi$ be of class $C^{p+1}$ on an open set $U \supseteq [a, b]$, and let $x \in (a, b]$.
Then there is $\xi(x) \in (a, x)$ such that
$$\varphi(x) = \Phi_p(x) + \frac{(x - a)^{p+1}}{(p + 1)!} \varphi^{(p+1)}(\xi(x)), \qquad
  \Phi_p(x) = \sum_{k=0}^{p} \frac{\varphi^{(k)}(a)}{k!} (x - a)^k.$$

**Reading.** Taylor formula with open-neighborhood smoothness and on x>a only.
-/
theorem equation_9_47 (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hφ : ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) φ U) {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ ξ ∈ Ioo a x, φ x = (∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ))
      + (x - a) ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * iteratedDeriv (p + 1) φ ξ := by
  have hsub : uIcc a x ⊆ U := by
    rw [uIcc_of_le hx.1.le]
    exact (Icc_subset_Icc_right hx.2).trans hUab
  obtain ⟨ξ, hξ, h⟩ := Quadrature.exists_sub_taylorWithinEval_univ_eq hx.1.ne hU hsub hφ
  rw [uIoo_of_le hx.1.le] at hξ
  rw [Quadrature.taylorWithinEval_univ_eq_sum] at h
  exact ⟨ξ, hξ, by linear_combination h⟩

/-- Let $a \le b$, let $\mu < 1$, let $\varphi : \mathbb{R} \to \mathbb{R}$, and let
$p \in \mathbb{N}$. Then the Taylor polynomial $\Phi_p$ of $\varphi$ at $a$, divided by the
weight $(x - a)^\mu$, has the integral
$$\int_a^b \frac{\Phi_p(x)}{(x - a)^\mu}\,dx = (b - a)^{1-\mu} \sum_{k=0}^{p} \frac{(b - a)^k
  \varphi^{(k)}(a)}{k!\,(k + 1 - \mu)}.$$

At $b = a + \varepsilon$ this is the truncated sum of Method 1, and it is the exact part (9.51)
of Method 2. The proof is the backbone's `Quadrature.integral_sum_mul_pow_div_rpow` with
$c_k = \varphi^{(k)}(a)/k!$.

**Reading.** Exact polynomial integral for all μ<1, including negative μ, arbitrary derivative data
via total evaluation.
-/
theorem integral_taylorSum_div_rpow (hab : a ≤ b) (hμ1 : μ < 1) (φ : ℝ → ℝ) (p : ℕ) :
    (∫ x in a..b, (∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
      = (b - a) ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1),
          (b - a) ^ k * iteratedDeriv k φ a / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 - μ)) := by
  have e : ∀ x : ℝ, (∑ k ∈ Finset.range (p + 1),
      iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ))
      = ∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a / (Nat.factorial k : ℝ) * (x - a) ^ k :=
    fun x => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [Quadrature.integral_sum_mul_pow_div_rpow hab hμ1
    (fun k => iteratedDeriv k φ a / (Nat.factorial k : ℝ)) p]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [mul_div_assoc', div_div])

/-! ### Method 1: truncation (9.48)–(9.49) -/

/-- **Equation (9.48)** of [quarteroni2000numerical], the truncation error of Method 1. Let
$\varepsilon > 0$ and $0 \le \mu < 1$, let $\varphi$ be of class $C^{p+1}$ on an open set
$U \supseteq [a, a + \varepsilon]$, and let $|\varphi^{(p+1)}(x)| \le M$ for all
$x \in [a, a + \varepsilon]$. Then the $p$-th order Taylor expansion (9.47) of $\varphi$ around
$a$ gives the closed form
$$\int_a^{a+\varepsilon} \frac{\Phi_p(x)}{(x - a)^\mu}\,dx = \varepsilon^{1-\mu} \sum_{k=0}^{p}
  \frac{\varepsilon^k \varphi^{(k)}(a)}{k!\,(k + 1 - \mu)},$$
and the error $E_1$ made by replacing $I_1 = \int_a^{a+\varepsilon} \varphi(x)/(x - a)^\mu\,dx$
by this finite sum satisfies
$$|E_1| \le \frac{\varepsilon^{p+2-\mu}}{(p + 1)!\,(p + 2 - \mu)} M.$$

The book writes $M$ as $\max_{a \le x \le a+\varepsilon} |\varphi^{(p+1)}(x)|$.

**Reading.** Uses a supplied bound on the derivative and adds exact weighted Taylor polynomial
integral.
-/
theorem equation_9_48 (hε : 0 < ε) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hU : IsOpen U)
    (hUab : Icc a (a + ε) ⊆ U) (hφ : ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) φ U) {M : ℝ}
    (hM : ∀ x ∈ Icc a (a + ε), |iteratedDeriv (p + 1) φ x| ≤ M) :
    (∫ x in a..(a + ε), (∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
        = ε ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1),
            ε ^ k * iteratedDeriv k φ a / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 - μ)) ∧
      |(∫ x in a..(a + ε), φ x / (x - a) ^ μ) - ε ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1),
            ε ^ k * iteratedDeriv k φ a / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 - μ))|
        ≤ ε ^ ((p : ℝ) + 2 - μ) / ((Nat.factorial (p + 1) : ℝ) * ((p : ℝ) + 2 - μ)) * M := by
  have hle : a ≤ a + ε := by linarith
  have hclosed := integral_taylorSum_div_rpow (a := a) (b := a + ε) hle hμ1 φ p
  rw [add_sub_cancel_left] at hclosed
  refine ⟨hclosed, ?_⟩
  set S : ℝ → ℝ := fun x => ∑ k ∈ Finset.range (p + 1),
    iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ) with hSdef
  have hScont : Continuous S := by
    refine continuous_finsetSum _ fun k _ => ?_
    fun_prop
  have hφc : ContinuousOn φ (Icc a (a + ε)) := hφ.continuousOn.mono hUab
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφc
  obtain ⟨MS, hMS⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := S) (s := Icc a (a + ε)) hScont.continuousOn
  have hint₁ : IntervalIntegrable (fun x => φ x / (x - a) ^ μ) volume a (a + ε) :=
    Quadrature.intervalIntegrable_div_rpow (by linarith) hμ0 hμ1
      ((hφc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
      fun x hx => by simpa [Real.norm_eq_abs] using hMφ x (Ioc_subset_Icc_self hx)
  have hint₂ : IntervalIntegrable (fun x => S x / (x - a) ^ μ) volume a (a + ε) :=
    Quadrature.intervalIntegrable_div_rpow (by linarith) hμ0 hμ1
      (hScont.continuousOn.aestronglyMeasurable measurableSet_Ioc)
      fun x hx => by simpa [Real.norm_eq_abs] using hMS x (Ioc_subset_Icc_self hx)
  have hbound := Quadrature.abs_integral_taylorRemainder_div_rpow_le hε hμ1 hU hUab hφ hM
  have hS : ∀ x, taylorWithinEval φ p univ a x = S x := fun x =>
    Quadrature.taylorWithinEval_univ_eq_sum φ p a x
  simp_rw [hS] at hbound
  have hsplit : (∫ x in a..(a + ε), (φ x - S x) / (x - a) ^ μ)
      = (∫ x in a..(a + ε), φ x / (x - a) ^ μ) - ∫ x in a..(a + ε), S x / (x - a) ^ μ := by
    simp_rw [sub_div]
    exact intervalIntegral.integral_sub hint₁ hint₂
  rwa [hsplit, hclosed] at hbound

/-- **Equation (9.49)** of [quarteroni2000numerical], the a priori bound on the error $E_2$. Let
$n \ge 2$ be even, let $\varepsilon > 0$ with $a + \varepsilon < b$, let $m \ge 1$, let
$\varphi$ be of class $C^{n+2}$ on an open set $U \supseteq [a, b]$, and let
$$\Bigl|\frac{d^{n+2}}{dx^{n+2}} \frac{\varphi(x)}{(x - a)^\mu}\Bigr| \le
  \mathcal{M}^{(n+2)}(\varepsilon) \qquad \text{for all } x \in [a + \varepsilon, b].$$
Let $I_2 = \int_{a+\varepsilon}^b \varphi(x)/(x - a)^\mu\,dx$ be approximated by the composite
closed Newton–Cotes formula with $m$ subintervals and $n + 1$ nodes on each. Then the error
satisfies
$$|E_2| \le \mathcal{M}^{(n+2)}(\varepsilon) \frac{b - a - \varepsilon}{(n + 2)!}
  \frac{|M_n|}{n^{n+3}} \Bigl(\frac{b - a - \varepsilon}{m}\Bigr)^{n+2}.$$

**Correction.** The constant $|M_n|/n^{n+3}$ is the one of (9.26) as corrected in
`QuarteroniSaccoSaleri.Chapter09.theorem_9_3_even`.

The book defines $\mathcal{M}^{(n+2)}(\varepsilon)$ as the maximum of the left side over
$[a + \varepsilon, b]$. The statement holds for every real $\mu$. The proof applies Theorem 9.3
on $[a + \varepsilon, b]$. -/
theorem equation_9_49 (hn : Even n) (hn0 : 0 < n) (hε : 0 < ε) (hab : a + ε < b) (hm : 1 ≤ m)
    (hU : IsOpen U) (hUab : Icc a b ⊆ U) (hφ : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) φ U)
    {Mn : ℝ} (hM : ∀ x ∈ Icc (a + ε) b,
      |iteratedDeriv (n + 2) (fun y => φ y / (y - a) ^ μ) x| ≤ Mn) :
    |(∫ x in (a + ε)..b, φ x / (x - a) ^ μ)
        - Quadrature.compositeNewtonCotes n (fun x => φ x / (x - a) ^ μ) (a + ε) b m|
      ≤ Mn * ((b - a - ε) / (Nat.factorial (n + 2) : ℝ))
          * (|Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3))
          * ((b - a - ε) / m) ^ (n + 2) := by
  have hsub : Icc (a + ε) b ⊆ U ∩ Ioi a := fun x hx =>
    ⟨hUab ⟨by linarith [hx.1], hx.2⟩, by simp only [mem_Ioi]; linarith [hx.1]⟩
  obtain ⟨ξ, hξ, h⟩ := theorem_9_3_even hn hn0 hab hm (hU.inter isOpen_Ioi) hsub
    (Quadrature.contDiffOn_div_rpow hφ)
  have hba : (0 : ℝ) ≤ b - (a + ε) := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnpow : (0 : ℝ) < (n : ℝ) ^ (n + 3) := by positivity
  have hA : (0 : ℝ) ≤ (b - (a + ε)) / (Nat.factorial (n + 2) : ℝ) :=
    div_nonneg hba (by positivity)
  have hB : (0 : ℝ) ≤ |Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3) :=
    div_nonneg (abs_nonneg _) hnpow.le
  have hC : (0 : ℝ) ≤ ((b - (a + ε)) / (m : ℝ)) ^ (n + 2) :=
    pow_nonneg (div_nonneg hba (by positivity)) _
  rw [show b - a - ε = b - (a + ε) by ring, h, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA,
    abs_of_nonneg hC, abs_div, abs_of_pos hnpow]
  calc (b - (a + ε)) / (Nat.factorial (n + 2) : ℝ)
          * (|Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3))
          * ((b - (a + ε)) / (m : ℝ)) ^ (n + 2)
          * |iteratedDeriv (n + 2) (fun y => φ y / (y - a) ^ μ) ξ|
      ≤ (b - (a + ε)) / (Nat.factorial (n + 2) : ℝ)
          * (|Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3))
          * ((b - (a + ε)) / (m : ℝ)) ^ (n + 2) * Mn :=
        mul_le_mul_of_nonneg_left (hM ξ hξ) (mul_nonneg (mul_nonneg hA hB) hC)
    _ = Mn * ((b - (a + ε)) / (Nat.factorial (n + 2) : ℝ))
          * (|Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3))
          * ((b - (a + ε)) / (m : ℝ)) ^ (n + 2) := by ring

/-! ### Example 9.10, the Fresnel integral -/

/-- **Example 9.10** of [quarteroni2000numerical], the Fresnel integral (9.50). Expansion of the
integrand in a Taylor series around the origin and integration term by term give
$$\int_0^{\pi/2} \frac{\cos x}{\sqrt{x}}\,dx = \sum_{k=0}^{\infty} \frac{(-1)^k}{(2k)!}
  \frac{(\pi/2)^{2k+1/2}}{2k + 1/2},$$
where the series converges.

The statement is a `HasSum`. The proof uses dominated convergence with the summable bound
$(\pi/2)^{2k} x^{-1/2}/(2k)!$. -/
theorem example_9_10 :
    HasSum (fun k : ℕ => (-1) ^ k / (Nat.factorial (2 * k) : ℝ) *
        ((π / 2) ^ (2 * (k : ℝ) + 1 / 2) / (2 * (k : ℝ) + 1 / 2)))
      (∫ x in (0 : ℝ)..(π / 2), cos x / √x) := by
  have hπ : (0 : ℝ) < π / 2 := by positivity
  have hinj : Function.Injective fun k : ℕ => 2 * k := fun i j h => by
    have h' : 2 * i = 2 * j := h
    omega
  have hsum₀ : Summable fun k : ℕ => (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) := by
    simpa [Function.comp_def] using
      (Real.summable_pow_div_factorial (π / 2)).comp_injective hinj
  have key : HasSum (fun k : ℕ => ∫ x in (0 : ℝ)..(π / 2),
      (-1) ^ k / (Nat.factorial (2 * k) : ℝ) * (x ^ (2 * k) / √x))
      (∫ x in (0 : ℝ)..(π / 2), cos x / √x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k x => (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) * x ^ (-(1 / 2) : ℝ))
      (fun k => (Measurable.aestronglyMeasurable (by fun_prop)).restrict) (fun k => ?_) ?_ ?_ ?_
    · filter_upwards with x hx
      rw [uIoc_of_le hπ.le] at hx
      have hx0 : 0 < x := hx.1
      have hsx : 0 < √x := Real.sqrt_pos.2 hx0
      have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by positivity
      have hneg : |(-1 : ℝ) ^ k| = 1 := by simp
      have hrpow : x ^ (-(1 / 2) : ℝ) = 1 / √x := by
        rw [Real.rpow_neg hx0.le, Real.sqrt_eq_rpow]
        exact (one_div _).symm
      calc ‖(-1 : ℝ) ^ k / (Nat.factorial (2 * k) : ℝ) * (x ^ (2 * k) / √x)‖
          = x ^ (2 * k) / ((Nat.factorial (2 * k) : ℝ) * √x) := by
            rw [Real.norm_eq_abs, abs_mul, abs_div, abs_div, hneg, abs_of_pos hfac,
              abs_of_nonneg (pow_nonneg hx0.le (2 * k)), abs_of_nonneg (Real.sqrt_nonneg x)]
            ring
        _ ≤ (π / 2) ^ (2 * k) / ((Nat.factorial (2 * k) : ℝ) * √x) :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0.le hx.2 _) (by positivity)
        _ = (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) * x ^ (-(1 / 2) : ℝ) := by
            rw [hrpow]; ring
    · filter_upwards with x _
      exact hsum₀.mul_right _
    · have heq : (fun t : ℝ => ∑' k : ℕ,
          (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) * t ^ (-(1 / 2) : ℝ))
          = fun t : ℝ => (∑' k : ℕ, (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
              * t ^ (-(1 / 2) : ℝ) := funext fun t => tsum_mul_right
      rw [heq]
      exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
    · filter_upwards with x _
      have h := (Real.hasSum_cos x).div_const (√x)
      refine h.congr_fun fun k => ?_
      ring
  have hterm : ∀ k : ℕ, (∫ x in (0 : ℝ)..(π / 2),
      (-1) ^ k / (Nat.factorial (2 * k) : ℝ) * (x ^ (2 * k) / √x))
      = (-1) ^ k / (Nat.factorial (2 * k) : ℝ) *
        ((π / 2) ^ (2 * (k : ℝ) + 1 / 2) / (2 * (k : ℝ) + 1 / 2)) := by
    intro k
    have h : ∀ x : ℝ, x ^ (2 * k) / √x = (x - 0) ^ (2 * k) / (x - 0) ^ (1 / 2 : ℝ) := by
      intro x
      rw [sub_zero, ← Real.sqrt_eq_rpow]
    have hexp : ((2 * k : ℕ) : ℝ) + 1 - 1 / 2 = 2 * (k : ℝ) + 1 / 2 := by push_cast; ring
    simp_rw [h]
    rw [intervalIntegral.integral_const_mul,
      Quadrature.integral_pow_div_rpow hπ.le (by norm_num) (2 * k), sub_zero, hexp]
  simpa only [hterm] using key

/-! ### Method 2: subtraction of the Taylor polynomial (9.51)–(9.52) -/

/-- **Equation (9.51)** of [quarteroni2000numerical], the exact singular part of Method 2. Write
$$I(f) = \int_a^b \frac{\varphi(x) - \Phi_p(x)}{(x - a)^\mu}\,dx + \int_a^b
  \frac{\Phi_p(x)}{(x - a)^\mu}\,dx = I_1 + I_2.$$
Let $a \le b$, let $\mu < 1$, let $\varphi : \mathbb{R} \to \mathbb{R}$, and let
$p \in \mathbb{N}$. Then the second integral is
$$I_2 = (b - a)^{1-\mu} \sum_{k=0}^{p} \frac{(b - a)^k \varphi^{(k)}(a)}{k!\,(k + 1 - \mu)}.$$

**Reading.** Exact Taylor polynomial formula, with all μ<1 and no smoothness hypothesis needed for
coefficient data.
-/
theorem equation_9_51 (hab : a ≤ b) (hμ1 : μ < 1) (φ : ℝ → ℝ) (p : ℕ) :
    (∫ x in a..b, (∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
      = (b - a) ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1),
          (b - a) ^ k * iteratedDeriv k φ a / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 - μ)) :=
  integral_taylorSum_div_rpow hab hμ1 φ p

/-- **Equation (9.52)** of [quarteroni2000numerical], the regularized integrand of Method 2. Let
$a < b$, let $\varphi$ be of class $C^{p+1}$ on an open set $U \supseteq [a, b]$, and let
$\mu \in \mathbb{R}$. Then there is a function $\xi$ with $\xi(x) \in (a, x)$ for every
$x \in (a, b]$, the Lagrange point of (9.47), such that
$$\frac{\varphi(x) - \Phi_p(x)}{(x - a)^\mu} = \frac{(x - a)^{p+1-\mu}}{(p + 1)!}
  \varphi^{(p+1)}(\xi(x)) \qquad \text{for every } x \in (a, b],$$
and therefore
$$I_1 = \int_a^b \frac{(x - a)^{p+1-\mu}}{(p + 1)!} \varphi^{(p+1)}(\xi(x))\,dx = \int_a^b
  g(x)\,dx.$$

**Reading.** Gives pointwise witness function and integral equality for any μ; regularity is stated
separately.
-/
theorem equation_9_52 (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hφ : ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) φ U) (μ : ℝ) :
    ∃ ξ : ℝ → ℝ, (∀ x ∈ Ioc a b, ξ x ∈ Ioo a x) ∧
      (∀ x ∈ Ioc a b, (φ x - ∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ
        = (x - a) ^ ((p : ℝ) + 1 - μ) * iteratedDeriv (p + 1) φ (ξ x)
            / (Nat.factorial (p + 1) : ℝ)) ∧
      (∫ x in a..b, (φ x - ∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
        = ∫ x in a..b, (x - a) ^ ((p : ℝ) + 1 - μ) * iteratedDeriv (p + 1) φ (ξ x)
            / (Nat.factorial (p + 1) : ℝ) := by
  have step : ∀ x ∈ Ioc a b, ∃ t ∈ Ioo a x,
      (φ x - ∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ
        = (x - a) ^ ((p : ℝ) + 1 - μ) * iteratedDeriv (p + 1) φ t
            / (Nat.factorial (p + 1) : ℝ) := by
    intro x hx
    obtain ⟨t, ht, h⟩ := equation_9_47 hU hUab hφ hx
    refine ⟨t, ht, ?_⟩
    have hxa : (0 : ℝ) < x - a := by linarith [hx.1]
    have hpow : (x - a) ^ (p + 1) / (x - a) ^ μ = (x - a) ^ ((p : ℝ) + 1 - μ) := by
      rw [show ((p : ℝ) + 1 - μ) = ((p + 1 : ℕ) : ℝ) - μ by push_cast; ring,
        Real.rpow_sub hxa, Real.rpow_natCast]
    rw [h, add_sub_cancel_left, ← hpow]
    ring
  choose! ξ hξmem hξeq using step
  refine ⟨ξ, hξmem, hξeq, intervalIntegral.integral_congr_ae ?_⟩
  rw [uIoc_of_le hab.le]
  filter_upwards with x hx using hξeq x hx

/-- **Section 9.8.2** of [quarteroni2000numerical], the sentence after (9.52). Let $a < b$, let
$\mu < 1$, and let $\varphi$ be of class $C^{p+1}$ on an open set $U \supseteq [a, b]$. Let
$g(x) = (\varphi(x) - \Phi_p(x))/(x - a)^\mu$ for $x \neq a$, and $g(a) = 0$. Then $g$ is of
class $C^p$ on $[a, b]$, and its derivatives of order $j \le p$ within $[a, b]$ vanish at $a$.

**Generalization.** The source assumes $0 \le \mu < 1$ throughout the section. The statement
here holds for every $\mu < 1$.

The book says that the regularized integrand does not blow up at $a$: "its first $p$ derivatives
are finite at $x = a$". The proof is the backbone's
`Quadrature.contDiffOn_taylorRemainder_div_rpow` and
`Quadrature.iteratedDerivWithin_taylorRemainder_div_rpow_eq_zero`. The book uses this regularity
to apply a composite Newton–Cotes error estimate to $I_1$; that step is not formalized (see the
module doc comment). -/
theorem equation_9_52_regularity (hab : a < b) (hμ1 : μ < 1) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hφ : ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) φ U) :
    ContDiffOn ℝ (p : WithTop ℕ∞) (fun x => if x = a then 0 else
        (φ x - ∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ) (Icc a b) ∧
      ∀ j ≤ p, iteratedDerivWithin j (fun x => if x = a then 0 else
        (φ x - ∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
        (Icc a b) a = 0 := by
  have hg : (fun x => if x = a then 0 else
      (φ x - ∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
      = fun x => if x = a then 0 else (φ x - taylorWithinEval φ p univ a x) / (x - a) ^ μ := by
    funext x
    rw [Quadrature.taylorWithinEval_univ_eq_sum]
  rw [hg]
  exact ⟨Quadrature.contDiffOn_taylorRemainder_div_rpow hab hμ1 hU hUab hφ, fun j hj =>
    Quadrature.iteratedDerivWithin_taylorRemainder_div_rpow_eq_zero hab hμ1 hU hUab hφ hj⟩

/-! ### §9.8.3 Integrals over unbounded intervals -/

/-- **Equation (9.53)** of [quarteroni2000numerical]. Let $f$ be integrable over $(a, \infty)$. Then
the integral is the limit of the proper integrals:
$$I(f) = \int_a^\infty f(x)\,dx = \lim_{t \to +\infty} \int_a^t f(x)\,dx.$$

**Scope.** The hypothesis is Lebesgue integrability on the half-line. The source's improper-
limit definition also covers conditionally convergent examples. -/
theorem equation_9_53 (hf : IntegrableOn f (Ioi a)) :
    Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 (∫ x in Ioi a, f x)) :=
  intervalIntegral_tendsto_integral_Ioi a hf tendsto_id

/-- **Equation (9.54)** of [quarteroni2000numerical]. Let $f : \mathbb{R} \to \mathbb{R}$ be
integrable over $\mathbb{R}$. Then for every $c \in \mathbb{R}$,
$$\int_{-\infty}^{c} f(x)\,dx + \int_c^\infty f(x)\,dx = \int_{-\infty}^{\infty} f(x)\,dx.$$

So the definition of the integral over $\mathbb{R}$ as the sum of the two improper integrals
does not depend on the choice of $c$.

**Reading.** Requires Lebesgue integrability on the whole real line.
-/
theorem equation_9_54 (hf : Integrable f) (c : ℝ) :
    (∫ x in Iic c, f x) + (∫ x in Ioi c, f x) = ∫ x, f x :=
  intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn

/-- **Section 9.8.3** of [quarteroni2000numerical], a sufficient condition for integrability. Let
$f$ be continuous on $[a, +\infty)$, and let there be $\rho > 0$ with
$$\lim_{x \to +\infty} x^{1+\rho} f(x) = 0,$$
that is, $f$ is infinitesimal of order greater than $1$ with respect to $1/x$. Then $f$ is
integrable over $(a, +\infty)$. -/
theorem integrable_of_tendsto_rpow_mul (hf : ContinuousOn f (Ici a)) (hρ : 0 < ρ)
    (hlim : Tendsto (fun x => x ^ (1 + ρ) * f x) atTop (𝓝 0)) : IntegrableOn f (Ioi a) :=
  Quadrature.integrableOn_Ioi_of_tendsto_rpow_mul hf hρ hlim

/-- **Equation (9.55)** of [quarteroni2000numerical], Method 2 for unbounded intervals. Let $c > 0$.
The change of variable $x = 1/t$ transforms $I_2 = \int_c^\infty f(x)\,dx$ into an integral over
the bounded interval $(0, 1/c)$:
$$\int_c^\infty f(x)\,dx = \int_0^{1/c} \frac{f(1/t)}{t^2}\,dt.$$

**Typo.** The source prints $I_2 = \int_0^{1/c} f(t) t^{-2}\,dt$, where it means $f(1/t)$.

The identity has no integrability hypothesis; it holds for every $f$, with the convention that
the Lean integral of a function that is not integrable is $0$. -/
theorem equation_9_55 (hc : 0 < c) (f : ℝ → ℝ) :
    ∫ x in Ioi c, f x = ∫ t in Ioo 0 (1 / c), f (1 / t) / t ^ 2 :=
  Quadrature.integral_Ioi_eq_integral_Ioo_inv hc f

/-! ### Method 3: Gauss–Laguerre and Gauss–Hermite -/

/-- **Section 9.8.3** of [quarteroni2000numerical], Method 3 with Gauss–Laguerre formulae. For every
$n$ there are $n$ distinct nodes $x_0, \dots, x_{n-1}$ and positive weights
$\alpha_0, \dots, \alpha_{n-1}$ such that
$$\sum_{k=0}^{n-1} \alpha_k p(x_k) = \int_0^\infty e^{-x} p(x)\,dx$$
for every polynomial $p$ of degree at most $2n - 1$.

The book takes as nodes the zeros of the Laguerre polynomial $\mathcal{L}_n$ of Section 10.5,
the $n$-th orthogonal polynomial for the weight $e^{-x}$ on $(0, \infty)$. The statement here
asserts only the existence of the nodes and weights. The proof applies `Quadrature.exists_gauss`
to the Laguerre weight of `Numlib.Approximation.OrthogonalPolynomial.Classical`.

**Reading.** Existential positive-weight quadrature exact below degree 2n without identifying nodes
as roots.
-/
theorem gaussLaguerre (n : ℕ) :
    ∃ x w : Fin n → ℝ, Function.Injective x ∧ (∀ i, 0 < w i) ∧
      ∀ P : Polynomial ℝ, P.degree < (2 * n : ℕ) →
        ∑ i, w i * P.eval (x i) = ∫ t in Ioi (0 : ℝ), exp (-t) * P.eval t := by
  obtain ⟨x, w, hx, hw, h⟩ :=
    Quadrature.exists_gauss OrthogonalPolynomial.isWeight_laguerreMeasure n
  exact ⟨x, w, hx, hw, fun P hP =>
    (h P hP).trans (OrthogonalPolynomial.integral_laguerreMeasure _)⟩

/-- **Section 9.8.3** of [quarteroni2000numerical], Method 3 with Gauss–Hermite formulae. For every
$n$ there are $n$ distinct nodes $x_0, \dots, x_{n-1}$ and positive weights
$\alpha_0, \dots, \alpha_{n-1}$ such that
$$\sum_{k=0}^{n-1} \alpha_k p(x_k) = \int_{-\infty}^{\infty} e^{-x^2} p(x)\,dx$$
for every polynomial $p$ of degree at most $2n - 1$.

The book takes as nodes the zeros of the Hermite polynomial of Section 10.5, the $n$-th
orthogonal polynomial for the weight $e^{-x^2}$ on $\mathbb{R}$. The statement here asserts only
the existence of the nodes and weights. The proof applies `Quadrature.exists_gauss` to the
Hermite weight of `Numlib.Approximation.OrthogonalPolynomial.Classical`.

**Reading.** Existential positive-weight quadrature exact below degree 2n without identifying nodes
as roots.
-/
theorem gaussHermite (n : ℕ) :
    ∃ x w : Fin n → ℝ, Function.Injective x ∧ (∀ i, 0 < w i) ∧
      ∀ P : Polynomial ℝ, P.degree < (2 * n : ℕ) →
        ∑ i, w i * P.eval (x i) = ∫ t : ℝ, exp (-t ^ 2) * P.eval t := by
  obtain ⟨x, w, hx, hw, h⟩ :=
    Quadrature.exists_gauss OrthogonalPolynomial.isWeight_hermiteMeasure n
  exact ⟨x, w, hx, hw, fun P hP =>
    (h P hP).trans (OrthogonalPolynomial.integral_hermiteMeasure _)⟩

end QuarteroniSaccoSaleri.Chapter09
