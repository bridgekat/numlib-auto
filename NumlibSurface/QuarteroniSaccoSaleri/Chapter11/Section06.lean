/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section03
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section05

/-!
# Quarteroni, Sacco and Saleri, Section 11.6: Analysis of Multistep Methods

This module formalizes Section 11.6 of [quarteroni2000numerical]. For the linear multistep method
(11.45) with $p + 1$ steps, Theorem 11.3 expresses consistency and order by algebraic conditions on
the coefficients, (11.52) and (11.53). Applied to the test problem $y' = \lambda y$, the method
becomes a linear difference equation (11.54) with the characteristic polynomial
$\Pi(r) = \rho(r) - h\lambda\,\sigma(r)$ (11.55), where
$$\rho(r) = r^{p+1} - \sum_{j=0}^{p} a_j r^{p-j}, \qquad \sigma(r) = b_{-1} r^{p+1} + \sum_{j=0}^{p}
  b_j r^{p-j}$$
are the first and second characteristic polynomials. The root condition (Definition 11.10) asks that
the roots of $\rho$ lie in the closed unit disc and that those of modulus one be simple; the strong
and the absolute root conditions (Definitions 11.11 and 11.12) are variants. The method is
zero-stable (Definition 11.13) if and only if it satisfies the root condition (Theorem 11.4, with
Lemma 11.3 and the estimate (11.65)). The module checks the root condition for the one-step, Adams,
midpoint, Simpson and BDF methods (Section 11.6.3), and proves that a consistent method is
convergent if and only if it satisfies the root condition (Theorem 11.5), so that convergence is
equivalent to zero-stability (Corollary 11.1).

The last part, Section 11.6.4, treats absolute stability: the region $\mathcal{A}$ of a multistep
method is the set of $z = h\lambda$ for which all roots of $\Pi$ lie in the open unit disc. The
module defines A-stability and $\vartheta$-stability, proves the explicit clause of Property 11.2,
describes the region $\mathcal{A}^*$ of Remark 11.3, and defines relative stability (11.66). The
proofs specialize the backbone module `Numlib.ODE.Multistep` at $E = \mathbb{R}$, and at
$E = \mathbb{C}$ for the test problem, with `Numlib.Analysis.LinearRecurrence` for Lemma 11.3.

## Main definitions

* Section 11.6.2, `QuarteroniSaccoSaleri.Chapter11.characteristicPolynomials`: the first and second
  characteristic polynomials $(\rho, \sigma)$.
* Equation (11.55), `QuarteroniSaccoSaleri.Chapter11.equation_11_55`: the characteristic polynomial
  $\Pi = \rho - z\sigma$ at $z = h\lambda$.
* Definition 11.10, `QuarteroniSaccoSaleri.Chapter11.definition_11_10`: the root condition (11.56).
* Definition 11.11, `QuarteroniSaccoSaleri.Chapter11.definition_11_11`: the strong root condition
  (11.57).
* Definition 11.12, `QuarteroniSaccoSaleri.Chapter11.definition_11_12`: the absolute root condition.
* Equation (11.59), `QuarteroniSaccoSaleri.Chapter11.equation_11_59`: the perturbed method.
* Definition 11.13, `QuarteroniSaccoSaleri.Chapter11.definition_11_13`: zero-stability of multistep
  methods.
* Section 11.6.4, `QuarteroniSaccoSaleri.Chapter11.absolutelyStable`: absolute stability of a
  multistep method for $\lambda$ and $h$.
* Section 11.6.4, `QuarteroniSaccoSaleri.Chapter11.equation_11_26_multistep`: the region of absolute
  stability $\mathcal{A}$ of a multistep method.
* Section 11.6.4, `QuarteroniSaccoSaleri.Chapter11.aStableMultistep`,
  `QuarteroniSaccoSaleri.Chapter11.thetaStable`: A-stability and $\vartheta$-stability.
* Remark 11.3, `QuarteroniSaccoSaleri.Chapter11.remark_11_3`: the region $\mathcal{A}^*$ of bounded
  solutions.
* Equation (11.66), `QuarteroniSaccoSaleri.Chapter11.equation_11_66`: relative stability.

## Main results

* Theorem 11.3, `QuarteroniSaccoSaleri.Chapter11.theorem_11_3`: the method is consistent if and only
  if (11.52) holds.
* Theorem 11.3, `QuarteroniSaccoSaleri.Chapter11.theorem_11_3_order`: the method has order $q$ if
  and only if (11.52) and (11.53) hold.
* Section 11.6.2, `QuarteroniSaccoSaleri.Chapter11.consistencyRoot`: a consistent method has
  $\rho(1) = 0$ and $\rho'(1) = \sigma(1)$.
* Equation (11.54), `QuarteroniSaccoSaleri.Chapter11.equation_11_54`: on the test problem the method
  is a linear difference equation with the characteristic polynomial $\Pi$.
* Theorem 11.4, `QuarteroniSaccoSaleri.Chapter11.theorem_11_4`,
  `QuarteroniSaccoSaleri.Chapter11.theorem_11_4_mpr`,
  `QuarteroniSaccoSaleri.Chapter11.theorem_11_4_mp`: zero-stability for every Lipschitz problem is
  equivalent to the root condition.
* Lemma 11.3, `QuarteroniSaccoSaleri.Chapter11.lemma_11_3_complex`,
  `QuarteroniSaccoSaleri.Chapter11.lemma_11_3`: the solutions of (11.28) satisfy the bound (11.63)
  if and only if $\Pi$ satisfies the root condition.
* Equation (11.65), `QuarteroniSaccoSaleri.Chapter11.equation_11_65`: under the root condition,
  $|z_n - u_n| \le K(\varepsilon_0 + T\varepsilon_1)$.
* Section 11.6.3, `QuarteroniSaccoSaleri.Chapter11.oneStep_zeroStable`,
  `QuarteroniSaccoSaleri.Chapter11.adams_zeroStable`,
  `QuarteroniSaccoSaleri.Chapter11.midpoint_zeroStable`,
  `QuarteroniSaccoSaleri.Chapter11.simpson_zeroStable`,
  `QuarteroniSaccoSaleri.Chapter11.bdf_zeroStable_of_le_two`,
  `QuarteroniSaccoSaleri.Chapter11.bdf_zeroStable`: the consistent one-step methods, the Adams
  methods, the midpoint and Simpson methods and the BDF methods of Table 11.2 satisfy the root
  condition.
* Theorem 11.5, `QuarteroniSaccoSaleri.Chapter11.theorem_11_5_mpr`,
  `QuarteroniSaccoSaleri.Chapter11.theorem_11_5_order`,
  `QuarteroniSaccoSaleri.Chapter11.theorem_11_5_mp`, `QuarteroniSaccoSaleri.Chapter11.theorem_11_5`:
  a consistent method is convergent if and only if it satisfies the root condition.
* Corollary 11.1, `QuarteroniSaccoSaleri.Chapter11.corollary_11_1`: a consistent method is
  convergent if and only if it is zero-stable.
* Section 11.6.4, `QuarteroniSaccoSaleri.Chapter11.absoluteStability`: $z \in \mathcal{A}$ if and
  only if $1 - zb_{-1} \neq 0$ and all roots of $\Pi$ lie in the open unit disc.
* Section 11.6.4, `QuarteroniSaccoSaleri.Chapter11.thetaStable_iff`,
  `QuarteroniSaccoSaleri.Chapter11.backwardEuler_aStable`,
  `QuarteroniSaccoSaleri.Chapter11.crankNicolson_aStable`: A-stability and $\vartheta$-stability,
  and the A-stability of backward Euler and Crank–Nicolson.
* Property 11.2, `QuarteroniSaccoSaleri.Chapter11.property_11_2_explicit`: an explicit method is
  neither A-stable nor $\vartheta$-stable.
* Remark 11.3, `QuarteroniSaccoSaleri.Chapter11.remark_11_3_iff`,
  `QuarteroniSaccoSaleri.Chapter11.remark_11_3_midpoint`,
  `QuarteroniSaccoSaleri.Chapter11.remark_11_3_zeroStable`: the region $\mathcal{A}^*$, its value
  for the midpoint method, and $0 \in \mathcal{A}^*$ as zero-stability.

## Conventions

* As in Section 11.5, a method is `M : ODE.LinearMultistep` with the coefficients $a_j$, $b_j$ and
  $b_{-1}$, and it has $p + 1$ steps.
* "$f$ is Lipschitz in $y$ uniformly on $[t_0, t_0 + T]$" is the hypothesis
  $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for all $t \in [t_0, t_0 + T]$ and
  $y_1, y_2 \in \mathbb{R}$.
* A solution of the Cauchy problem enters Theorem 11.5 through the two-sided derivative,
  `HasDerivAt y (f t (y t)) t` for every $t \in [t_0, t_0 + T]$. The local truncation error of
  Definition 11.8 is built from this derivative.
* The roots of $\rho$, $\sigma$ and $\Pi$ are taken in $\mathbb{C}$.

## Deviations from the source

* **Theorem 11.3** (reading). The consistency and order equivalences concern all sufficiently
  smooth curves. For a single exact curve such as $y=0$, a residual can vanish without the
  coefficient conditions.
* **Equations (11.54)–(11.57) and Definition 11.12** (reading). The normalized recurrence in
  `equation_11_54` requires $1-h\lambda b_{-1}\ne 0$. The strong root condition permits $1$ as a
  boundary root but does not assert its existence unless consistency supplies it. The absolute
  root condition quantifies over positive steps.
* **Definition 11.13, Lemma 11.3 and equation (11.65)** (reading). Stability compares orbits
  with arbitrary initial data and does not prescribe how the unperturbed startup values were
  obtained. The recurrence bound in Lemma 11.3 also allows a vanishing constant coefficient and
  is stated over both $\mathbb R$ and $\mathbb C$. The estimate (11.65) keeps a uniform constant
  existential and takes uniform bounds on the startup and forcing errors over the horizon.
* **Theorem 11.5 and Corollary 11.1** (reading). The convergence bound is a modulus that tends
  to zero jointly with step size and startup error. It quantifies over uniformly Lipschitz
  fields, and Corollary 11.1 imposes continuity of the field along the solution curve. The order
  bound gives a constant times the sum of the startup error and $h^q$.
* **Section 11.6.4, absolute and angular stability and Property 11.2** (reading). The absolute
  stability region excludes a zero leading coefficient and asks for decay of all orbits.
  `thetaStable` describes the sector by $|\arg(-z)|<\vartheta$ and accepts all real angles. The
  explicit part of Property 11.2 assumes $\sum_j a_j=1$ and $\vartheta>0$ for the angular claim.
* **Remark 11.3** (reading). The boundedness region excludes a zero leading coefficient and
  quantifies over all orbits. `remark_11_3_iff` proves inclusion of the decay region and the
  equivalent root test. The source also discusses the closure of the decay region.
* **Theorem 11.4** (generalization). The book states the theorem for consistent methods. Consistency
  is not needed. See `QuarteroniSaccoSaleri.Chapter11.theorem_11_4`.
* **Remark 11.3, the midpoint method** (correction). The book prints $\mathcal{A}^* = \{i\alpha :
  \alpha \in [-1, 1]\}$. The end points do not belong to it:
  $\mathcal{A}^* = \{i\alpha : |\alpha| < 1\}$. See
  `QuarteroniSaccoSaleri.Chapter11.remark_11_3_midpoint`.
* **Equation (11.66)** (reading). The bound is read on the grid of the bounded interval $[0, T]$,
  not for all $n$. See `QuarteroniSaccoSaleri.Chapter11.equation_11_66`.

## Not formalized

* **Property 11.1** (the first Dahlquist barrier): no zero-stable linear multistep method with $p$
  steps has order greater than $p + 1$ if $p$ is odd, or $p + 2$ if $p$ is even. The statement can
  be written with the definitions of the library, but its proof is missing: Dahlquist's argument
  ([hairer1993solving], Section III.3, Theorem 3.5) uses the Möbius transform
  $z \mapsto (1 + z)/(1 - z)$, the expansion of $(\rho/\sigma)(\zeta) - \log\zeta$, and the
  positivity of the coefficients of power series such as $z/\log((1 + z)/(1 - z))$, which neither
  Mathlib nor the library provides. The book quotes the result without proof.
* **Property 11.2, except its explicit clause.** The order barrier, that no A-stable linear
  multistep method has order greater than $2$, needs a Riesz–Herglotz positivity argument in
  addition to the tools of Property 11.1. The book states that for every $\vartheta \in (0, \pi/2)$
  there are $\vartheta$-stable methods with $p$ steps and order $p$ only for $p = 3$ and $p = 4$.
  The standard statement, Widlund's theorem, is that such methods exist for $p = 3, 4$; among the
  A-stable methods, the trapezoidal rule has the smallest error constant. This clause is existential
  and needs a construction of two methods and the computation of their regions. The book quotes both
  clauses without proof.
* **The relative stability of methods that satisfy the strong root condition** (Section 11.6.4): the
  claim that the strong root condition implies (11.66).
-/

open Set Filter Topology Asymptotics ODE Polynomial
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h t : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### Theorem 11.3: consistency and order through the coefficients -/

/-- **Theorem 11.3** of [quarteroni2000numerical], consistency. A linear multistep method with
$p + 1$ steps is consistent (Definition 11.9) if and only if
$$\sum_{j=0}^{p} a_j = 1, \qquad -\sum_{j=0}^{p} j a_j + \sum_{j=-1}^{p} b_j = 1. \qquad
  \text{(11.52)}$$

The proof specializes `ODE.LinearMultistep.isConsistent_iff`.

**Reading.** The equivalence concerns the properties of the method quantified over sufficiently
smooth curves. The coefficient conditions need not hold when the residual vanishes along one
curve. -/
theorem theorem_11_3 (M : LinearMultistep) :
    definition_11_9_method M ↔
      ∑ j, M.a j = 1 ∧ -∑ j : Fin (M.p + 1), (j : ℝ) * M.a j + (M.bm1 + ∑ j, M.b j) = 1 := by
  rw [definition_11_9_method, LinearMultistep.isConsistent_iff, LinearMultistep.orderCondition_zero,
    LinearMultistep.orderCondition_one]

/-- **Theorem 11.3** of [quarteroni2000numerical], order. Let $q \ge 1$. A linear multistep method
with $p + 1$ steps has order $q$ (Definition 11.9) if and only if it satisfies the consistency
conditions (11.52) and
$$\sum_{j=0}^{p} (-j)^i a_j + i \sum_{j=-1}^{p} (-j)^{i-1} b_j = 1, \qquad i = 2, \dots, q.
  \qquad \text{(11.53)}$$

In the Lean statement, the term of $b_{-1}$ in the second sum is $b_{-1}$ itself, since
$(-(-1))^{i-1} = 1$. The proof specializes `ODE.LinearMultistep.hasOrder_iff`.

**Reading.** The equivalence concerns the properties of the method quantified over sufficiently
smooth curves. The coefficient conditions need not hold when the residual vanishes along one
curve. -/
theorem theorem_11_3_order (M : LinearMultistep) {q : ℕ} (hq : 1 ≤ q) :
    definition_11_9_order_method M q ↔
      (∑ j, M.a j = 1 ∧ -∑ j : Fin (M.p + 1), (j : ℝ) * M.a j + (M.bm1 + ∑ j, M.b j) = 1) ∧
        ∀ i, 2 ≤ i → i ≤ q → ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ i * M.a j +
          i * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (i - 1) * M.b j) = 1 := by
  rw [definition_11_9_order_method, LinearMultistep.hasOrder_iff]
  constructor
  · intro H
    exact ⟨⟨(LinearMultistep.orderCondition_zero M).1 (H 0 (Nat.zero_le q)),
      (LinearMultistep.orderCondition_one M).1 (H 1 hq)⟩, fun i _ hiq => H i hiq⟩
  · rintro ⟨⟨h0, h1⟩, H⟩ i hi
    match i with
    | 0 => exact (LinearMultistep.orderCondition_zero M).2 h0
    | 1 => exact (LinearMultistep.orderCondition_one M).2 h1
    | i + 2 => exact H (i + 2) (by omega) hi

/-! ### (11.54)–(11.55): the test problem and the characteristic polynomials -/

/-- **Section 11.6.2** of [quarteroni2000numerical], the characteristic polynomials. For a linear
multistep method with $p + 1$ steps, the **first and second characteristic polynomials** are
$$\rho(r) = r^{p+1} - \sum_{j=0}^{p} a_j r^{p-j}, \qquad \sigma(r) = b_{-1} r^{p+1} +
  \sum_{j=0}^{p} b_j r^{p-j}.$$
The definition gives the pair $(\rho, \sigma)$ of real polynomials.

The polynomials are `ODE.LinearMultistep.rho` and `ODE.LinearMultistep.sigma`. -/
noncomputable def characteristicPolynomials (M : LinearMultistep) : ℝ[X] × ℝ[X] :=
  (M.rho, M.sigma)

/-- **Section 11.6.2** of [quarteroni2000numerical]. For every $r \in \mathbb{R}$,
$\rho(r) = r^{p+1} - \sum_{j=0}^{p} a_j r^{p-j}$ and $\sigma(r) = b_{-1} r^{p+1} +
\sum_{j=0}^{p} b_j r^{p-j}$. -/
theorem characteristicPolynomials_eval (M : LinearMultistep) (r : ℝ) :
    (characteristicPolynomials M).1.eval r =
        r ^ (M.p + 1) - ∑ j : Fin (M.p + 1), M.a j * r ^ (M.p - j) ∧
      (characteristicPolynomials M).2.eval r =
        M.bm1 * r ^ (M.p + 1) + ∑ j : Fin (M.p + 1), M.b j * r ^ (M.p - j) :=
  ⟨M.eval_rho r, M.eval_sigma r⟩

/-- **Section 11.6.2** of [quarteroni2000numerical]. The first characteristic polynomial $\rho$ is
monic of degree $p + 1$. -/
theorem characteristicPolynomials_degree (M : LinearMultistep) :
    (characteristicPolynomials M).1.Monic ∧ (characteristicPolynomials M).1.degree = M.p + 1 :=
  ⟨M.rho_monic, M.degree_rho⟩

/-- **Equation (11.55)** of [quarteroni2000numerical]. For a linear multistep method and
$z = h\lambda \in \mathbb{C}$, the **characteristic polynomial** of the method on the test
problem is
$$\Pi(r) = \rho(r) - z\,\sigma(r),$$
a polynomial with complex coefficients.

The definition is `ODE.LinearMultistep.charPoly`. -/
noncomputable def equation_11_55 (M : LinearMultistep) (z : ℂ) : ℂ[X] :=
  M.charPoly z

/-- **Equation (11.55)** of [quarteroni2000numerical]. For every $z \in \mathbb{C}$,
$\Pi = \rho - z\sigma$ in $\mathbb{C}[r]$, and for $z = 0$, $\Pi = \rho$. -/
theorem equation_11_55_eq (M : LinearMultistep) (z : ℂ) :
    equation_11_55 M z = (characteristicPolynomials M).1.map (algebraMap ℝ ℂ) -
        C z * (characteristicPolynomials M).2.map (algebraMap ℝ ℂ) ∧
      equation_11_55 M 0 = (characteristicPolynomials M).1.map (algebraMap ℝ ℂ) :=
  ⟨rfl, M.charPoly_zero⟩

/-- **Section 11.6.2** of [quarteroni2000numerical], the consistency root. If a linear multistep
method is consistent, then $r_0 = 1$ is a root of $\rho$, $\rho(1) = 0$, and
$$\rho'(1) = \sigma(1).$$

The proof specializes `ODE.LinearMultistep.rho_isRoot_one` and
`ODE.LinearMultistep.derivative_rho_eval_one_eq_sigma`. -/
theorem consistencyRoot (M : LinearMultistep) (hM : definition_11_9_method M) :
    (characteristicPolynomials M).1.IsRoot 1 ∧
      (derivative (characteristicPolynomials M).1).eval 1 =
        (characteristicPolynomials M).2.eval 1 := by
  rw [definition_11_9_method, LinearMultistep.isConsistent_iff] at hM
  exact ⟨M.rho_isRoot_one hM.1, M.derivative_rho_eval_one_eq_sigma hM.1 hM.2⟩

/-- **Equation (11.54)** of [quarteroni2000numerical], the method on the test problem. Let
$\lambda \in \mathbb{C}$, $h \in \mathbb{R}$, and let $u$ be a complex sequence. Then:

* $u$ is computed by the method (11.45) on the test problem (11.24) with step $h$ from $t_0 = 0$
  if and only if for every $n \ge p$
$$u_{n+1} = \sum_{j=0}^{p} a_j u_{n-j} + h\lambda \Bigl(\sum_{j=0}^{p} b_j u_{n-j} + b_{-1}
  u_{n+1}\Bigr);$$
* if $1 - h\lambda b_{-1} \neq 0$, then $u$ is computed by the method if and only if it solves a
  homogeneous linear recurrence of order $p + 1$, whose characteristic polynomial is
  $(1 - h\lambda b_{-1})^{-1}\,\Pi(r)$ with $z = h\lambda$.

The recurrence is `ODE.LinearMultistep.toLinearRecurrence M (h * lam)`, with the coefficients
$(a_{p-i} + h\lambda b_{p-i})/(1 - h\lambda b_{-1})$. The proof uses
`ODE.LinearMultistep.isOrbit_testField_iff` and
`ODE.LinearMultistep.charPoly_toLinearRecurrence`.

**Reading.** The test recurrence can be normalized to monic form when its leading coefficient
$1-h\lambda b_{-1}$ is nonzero. -/
theorem equation_11_54 (M : LinearMultistep) (lam : ℂ) (u : ℕ → ℂ) :
    (M.IsOrbit (testProblem lam) h 0 u ↔ ∀ n, M.p ≤ n → u (n + 1) =
      ∑ j : Fin (M.p + 1), (M.a j : ℂ) * u (n - j) +
        h * lam * (∑ j : Fin (M.p + 1), (M.b j : ℂ) * u (n - j) + M.bm1 * u (n + 1))) ∧
    (1 - (h : ℂ) * lam * M.bm1 ≠ 0 →
      (M.IsOrbit (testProblem lam) h 0 u ↔ (M.toLinearRecurrence (h * lam)).IsSolution u) ∧
      (M.toLinearRecurrence (h * lam)).charPoly =
        C (1 - (h : ℂ) * lam * M.bm1)⁻¹ * equation_11_55 M (h * lam)) := by
  refine ⟨?_, fun hz => ⟨M.isOrbit_testField_iff hz, M.charPoly_toLinearRecurrence hz⟩⟩
  rw [LinearMultistep.isOrbit_iff]
  simp only [testProblem, testField, Complex.real_smul, Complex.ofReal_mul]
  have key : ∀ m, ∑ j : Fin (M.p + 1), (M.a j : ℂ) * u (m + M.p - j) +
      h * ∑ j : Fin (M.p + 1), (M.b j : ℂ) * (lam * u (m + M.p - j)) +
      h * M.bm1 * (lam * u (m + M.p + 1)) =
      ∑ j : Fin (M.p + 1), (M.a j : ℂ) * u (m + M.p - j) +
      h * lam * (∑ j : Fin (M.p + 1), (M.b j : ℂ) * u (m + M.p - j) + M.bm1 * u (m + M.p + 1)) := by
    intro m
    have hS : ∑ j : Fin (M.p + 1), (M.b j : ℂ) * (lam * u (m + M.p - j)) =
        lam * ∑ j : Fin (M.p + 1), (M.b j : ℂ) * u (m + M.p - j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hS]
    ring
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact (H m).trans (key m)
  · intro H n
    exact (H (n + M.p) (Nat.le_add_left _ _)).trans (key n).symm

/-! ### Definitions 11.10–11.12: the root conditions -/

/-- **Definition 11.10** of [quarteroni2000numerical] (the root condition). A linear multistep
method satisfies the **root condition** (11.56) if the roots $r_j \in \mathbb{C}$ of the first
characteristic polynomial $\rho$ satisfy
$$|r_j| \le 1, \quad \text{and} \quad r_j \text{ is simple if } |r_j| = 1.$$

The definition is `ODE.LinearMultistep.SatisfiesRootCondition`, which is
`Polynomial.SatisfiesRootCondition` for $\rho$ viewed in $\mathbb{C}[r]$. -/
def definition_11_10 (M : LinearMultistep) : Prop :=
  M.SatisfiesRootCondition

/-- **Definition 11.10** of [quarteroni2000numerical], in the terms of the book. A linear multistep
method satisfies the root condition if and only if every root $r \in \mathbb{C}$ of $\rho$ has
$|r| \le 1$, and $\rho'(r) \neq 0$ when $|r| = 1$.

The proof uses `Polynomial.satisfiesRootCondition_iff_derivative`. -/
theorem definition_11_10_iff (M : LinearMultistep) :
    definition_11_10 M ↔ ∀ r : ℂ, ((characteristicPolynomials M).1.map (algebraMap ℝ ℂ)).IsRoot r →
      ‖r‖ ≤ 1 ∧ (‖r‖ = 1 →
        ¬ (derivative ((characteristicPolynomials M).1.map (algebraMap ℝ ℂ))).IsRoot r) :=
  Polynomial.satisfiesRootCondition_iff_derivative (M.rho_monic.map _).ne_zero

/-- **Definition 11.11** of [quarteroni2000numerical] (the strong root condition). A linear
multistep method satisfies the **strong root condition** (11.57) if it satisfies the root
condition and $r_0 = 1$ is the only root of $\rho$ of modulus one, that is $|r_j| < 1$ for
$j = 1, \dots, p$.

The definition is `ODE.LinearMultistep.SatisfiesStrongRootCondition`.

**Reading.** The root $1$ is the sole allowed boundary root. The definition also accepts
polynomials with all roots strictly in the disk. Consistency supplies the root $1$ when
assumed. -/
def definition_11_11 (M : LinearMultistep) : Prop :=
  M.SatisfiesStrongRootCondition

/-- **Definition 11.11** of [quarteroni2000numerical]. A linear multistep method satisfies the
strong root condition if and only if it satisfies the root condition and every root $r \neq 1$
of $\rho$ has $|r| < 1$.

**Reading.** The root $1$ is the sole allowed boundary root. The definition also accepts
polynomials with all roots strictly in the disk. Consistency supplies the root $1$ when
assumed. -/
theorem definition_11_11_iff (M : LinearMultistep) :
    definition_11_11 M ↔ definition_11_10 M ∧
      ∀ r : ℂ, ((characteristicPolynomials M).1.map (algebraMap ℝ ℂ)).IsRoot r → r ≠ 1 → ‖r‖ < 1 :=
  Iff.rfl

/-- **Definition 11.12** of [quarteroni2000numerical] (the absolute root condition). Let
$\lambda \in \mathbb{C}$. A linear multistep method satisfies the **absolute root condition**
for $\lambda$ if there is $h_0 > 0$ such that the roots $r_j(h\lambda)$ of $\Pi$ satisfy
$$|r_j(h\lambda)| < 1 \qquad \text{for all } j \text{ and all } h \in (0, h_0].$$

The definition is `ODE.LinearMultistep.SatisfiesAbsRootCondition`.

**Reading.** Uses $0<h\leq h_0$, as appropriate for the positive step size. -/
def definition_11_12 (M : LinearMultistep) (lam : ℂ) : Prop :=
  M.SatisfiesAbsRootCondition lam

/-- **Definition 11.12** of [quarteroni2000numerical]. A linear multistep method satisfies the
absolute root condition for $\lambda$ if and only if there is $h_0 > 0$ such that for every
$h \in (0, h_0]$, every root $r$ of $\Pi$ at $z = h\lambda$ has $|r| < 1$.

**Reading.** Uses $0<h\leq h_0$, as appropriate for the positive step size. -/
theorem definition_11_12_iff (M : LinearMultistep) (lam : ℂ) :
    definition_11_12 M lam ↔ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀,
      ∀ r : ℂ, (equation_11_55 M (h * lam)).IsRoot r → ‖r‖ < 1 :=
  Iff.rfl

/-! ### Definition 11.13 and Theorem 11.4: zero-stability -/

/-- **Equation (11.59)** of [quarteroni2000numerical], the perturbed method. Let $M$ be a linear
multistep method with $p + 1$ steps, $f : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$,
$h, t_0 \in \mathbb{R}$ and $\delta : \mathbb{N} \to \mathbb{R}$. A sequence $z$ **solves the
perturbed method** if for every $n \ge p$
$$z_{n+1} = \sum_{j=0}^{p} a_j z_{n-j} + h \Bigl[\sum_{j=0}^{p} b_j f(t_{n-j}, z_{n-j}) + b_{-1}
  f(t_{n+1}, z_{n+1}) + \delta_{n+1}\Bigr].$$

The definition is `ODE.LinearMultistep.IsOrbitWith`. The starting values $z_0, \dots, z_p$ are
free.

**Generalization.** The equation describes all later steps of an orbit. Perturbed startup
conditions and the upper grid cutoff are separate. -/
def equation_11_59 (M : LinearMultistep) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (δ z : ℕ → ℝ) : Prop :=
  M.IsOrbitWith f h t₀ δ z

/-- **Equation (11.59)** of [quarteroni2000numerical]. A sequence $z$ solves the perturbed method if
and only if for every $n \ge p$
$$z_{n+1} = \sum_{j=0}^{p} a_j z_{n-j} + h \Bigl(\sum_{j=0}^{p} b_j f(t_{n-j}, z_{n-j}) + b_{-1}
  f(t_{n+1}, z_{n+1}) + \delta_{n+1}\Bigr).$$

**Generalization.** The equation describes all later steps of an orbit. Perturbed startup
conditions and the upper grid cutoff are separate. -/
theorem equation_11_59_iff (M : LinearMultistep) (δ z : ℕ → ℝ) :
    equation_11_59 M f h t₀ δ z ↔ ∀ n, M.p ≤ n → z (n + 1) =
      ∑ j : Fin (M.p + 1), M.a j * z (n - j) +
        h * (∑ j : Fin (M.p + 1), M.b j * f (grid t₀ h (n - j)) (z (n - j)) +
          M.bm1 * f (grid t₀ h (n + 1)) (z (n + 1)) + δ (n + 1)) := by
  rw [equation_11_59, LinearMultistep.isOrbitWith_iff]
  simp only [smul_eq_mul, grid]
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    refine (H m).trans ?_
    ring
  · intro H n
    refine (H (n + M.p) (Nat.le_add_left _ _)).trans ?_
    ring

/-- **Definition 11.13** of [quarteroni2000numerical] (zero-stability of multistep methods). Let $M$
be a linear multistep method with $p + 1$ steps, $f : \mathbb{R} \times \mathbb{R} \to
\mathbb{R}$ and $t_0, T \in \mathbb{R}$. The method is **zero-stable** for the Cauchy problem
with the field $f$ on $[t_0, t_0 + T]$ if there are $h_0 > 0$ and $C > 0$ with the following
property. Let $h \in (0, h_0]$ and $\varepsilon \ge 0$, let $|\delta_k| \le \varepsilon$ for
$0 \le k \le N_h$, let $u$ solve the method (11.60), and let $z$ solve the perturbed method
(11.59) with the starting values $z_k = u_k + \delta_k$, $k = 0, \dots, p$. Then (11.58) holds:
$$|z_n - u_n| \le C\varepsilon, \qquad 0 \le n \le N_h.$$

The definition is `ODE.LinearMultistep.IsZeroStable`. The book writes the starting values as
$w_k + \delta_k$ and $w_k$.

**Reading.** The estimate concerns all existing perturbed and unperturbed orbits with the
declared difference of starting values. The unperturbed startup method is left unspecified. -/
def definition_11_13 (M : LinearMultistep) (f : ℝ → ℝ → ℝ) (t₀ T : ℝ) : Prop :=
  M.IsZeroStable f t₀ T

/-- **Definition 11.13** of [quarteroni2000numerical]. A linear multistep method is zero-stable for
$f$ on $[t_0, t_0 + T]$ if and only if there are $h_0 > 0$ and $C > 0$ such that for all
$h \in (0, h_0]$, all $\varepsilon \ge 0$ and all $\delta$ with $|\delta_k| \le \varepsilon$ for
$k \le N_h$, every solution $u$ of (11.45) and every solution $z$ of (11.59) with
$z_k = u_k + \delta_k$ for $k \le p$ satisfy $|z_n - u_n| \le C\varepsilon$ for $n \le N_h$.

**Reading.** The estimate concerns all existing perturbed and unperturbed orbits with the
declared difference of starting values. The unperturbed startup method is left unspecified. -/
theorem definition_11_13_iff (M : LinearMultistep) :
    definition_11_13 M f t₀ T ↔
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Ioc 0 h₀, ∀ ε : ℝ, 0 ≤ ε → ∀ δ : ℕ → ℝ,
        (∀ k ≤ gridCount T h, |δ k| ≤ ε) → ∀ u z : ℕ → ℝ, equation_11_45 M f h t₀ u →
          equation_11_59 M f h t₀ δ z → (∀ k ≤ M.p, z k = u k + δ k) →
            ∀ n ≤ gridCount T h, |z n - u n| ≤ C * ε := by
  unfold definition_11_13 LinearMultistep.IsZeroStable equation_11_45 equation_11_59 gridCount
  simp only [Real.norm_eq_abs]

/-- **Theorem 11.4** of [quarteroni2000numerical] (zero-stability and the root condition). Let
$T > 0$. A linear multistep method is zero-stable on $[t_0, t_0 + T]$ for every field $f$ that
is Lipschitz in $y$ uniformly on $[t_0, t_0 + T]$, that is
$|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for some $L$, if and only if it satisfies the root
condition.

**Generalization.** The book states the theorem for consistent methods. Consistency is not
needed.

The proof specializes `ODE.LinearMultistep.isZeroStable_iff_satisfiesRootCondition`. -/
theorem theorem_11_4 (M : LinearMultistep) (hT : 0 < T) :
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
        definition_11_13 M f t₀ T) ↔ definition_11_10 M := by
  unfold definition_11_13 definition_11_10
  rw [← M.isZeroStable_iff_satisfiesRootCondition hT]
  constructor
  · intro H f L hf
    exact H f L fun t ht y₁ y₂ => by
      have := (hf t ht).dist_le_mul y₁ y₂
      rwa [Real.dist_eq, Real.dist_eq] at this
  · intro H f L hf
    exact H f (Real.toNNReal L) fun t ht => LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

/-- **Theorem 11.4** of [quarteroni2000numerical], sufficiency. Let a linear multistep method
satisfy the root condition, let $T \ge 0$, and let $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$
for all $t \in [t_0, t_0 + T]$ and $y_1, y_2 \in \mathbb{R}$. Then the method is zero-stable for
$f$ on $[t_0, t_0 + T]$.

The proof specializes `ODE.LinearMultistep.isZeroStable_of_satisfiesRootCondition`.

**Generalization.** These implications do not require consistency. Sufficiency uses a Lipschitz
field, and the necessity proof uses only the zero field on a positive horizon. -/
theorem theorem_11_4_mpr (M : LinearMultistep) (hroot : definition_11_10 M) (hT : 0 ≤ T) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) :
    definition_11_13 M f t₀ T :=
  M.isZeroStable_of_satisfiesRootCondition (L := Real.toNNReal L) hroot hT fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

/-- **Theorem 11.4** of [quarteroni2000numerical], necessity. Let $T > 0$. If a linear multistep
method is zero-stable on $[t_0, t_0 + T]$ for the problem $y' = 0$, then it satisfies the root
condition.

The proof specializes `ODE.LinearMultistep.satisfiesRootCondition_of_isZeroStable`.

**Generalization.** These implications do not require consistency. Sufficiency uses a Lipschitz
field, and the necessity proof uses only the zero field on a positive horizon. -/
theorem theorem_11_4_mp (M : LinearMultistep) (hT : 0 < T)
    (hzs : definition_11_13 M (fun _ _ => 0) t₀ T) : definition_11_10 M :=
  M.satisfiesRootCondition_of_isZeroStable hT hzs

/-- **Lemma 11.3** of [quarteroni2000numerical], over $\mathbb{C}$. Let $k \ge 1$ and
$\alpha_0, \dots, \alpha_{k-1} \in \mathbb{C}$. There is $M > 0$ such that every solution $u$ of
the difference equation (11.28) with any right-hand side $\varphi$ satisfies
$$|u_n| \le M \Bigl(\max_{0 \le j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr) \qquad \text{for
  all } n \qquad \text{(11.63)}$$
if and only if the characteristic polynomial (11.30) satisfies the root condition.

The book cites the lemma without proof. The proof specializes
`LinearRecurrence.exists_forall_norm_le_iff_satisfiesRootCondition`.

**Generalization.** A single constant works for every forcing and solution of the supplied
constant-coefficient recurrence. The statement also allows a vanishing constant coefficient. -/
theorem lemma_11_3_complex {k : ℕ} (hk : 0 < k) (α : Fin k → ℂ) :
    (∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → ℂ, (equation_11_28 α).IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin k, ‖u j‖) + ∑ l ∈ Finset.Icc k n, ‖φ l‖)) ↔
      (equation_11_30 α).SatisfiesRootCondition := by
  rw [equation_11_30_eq]
  exact (equation_11_28 α).exists_forall_norm_le_iff_satisfiesRootCondition hk

/-- **Lemma 11.3** of [quarteroni2000numerical]. Let $k \ge 1$ and
$\alpha_0, \dots, \alpha_{k-1} \in \mathbb{R}$. There is $M > 0$ such that every real solution
$u$ of the difference equation (11.28) with any real right-hand side $\varphi$ satisfies
$$|u_n| \le M \Bigl(\max_{0 \le j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr) \qquad \text{for
  all } n \qquad \text{(11.63)}$$
if and only if the characteristic polynomial (11.30), viewed in $\mathbb{C}[r]$, satisfies the
root condition.

The bound follows from the complex case applied to the real sequences viewed as complex ones.
The converse uses the real unbounded solution of
`LinearRecurrence.exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition`.

**Generalization.** A single constant works for every forcing and solution of the supplied
constant-coefficient recurrence. The statement also allows a vanishing constant coefficient. -/
theorem lemma_11_3 {k : ℕ} (hk : 0 < k) (α : Fin k → ℝ) :
    (∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → ℝ, (equation_11_28 α).IsSolutionWith φ u → ∀ n,
      |u n| ≤ M * ((⨆ j : Fin k, |u j|) + ∑ l ∈ Finset.Icc k n, |φ l|)) ↔
      ((equation_11_30 α).map (algebraMap ℝ ℂ)).SatisfiesRootCondition := by
  have hchar : ((equation_11_28 α).map (algebraMap ℝ ℂ)).charPoly =
      (equation_11_30 α).map (algebraMap ℝ ℂ) := by
    rw [LinearRecurrence.charPoly_map, equation_11_30_eq]
  constructor
  · rintro ⟨M, hM0, hM⟩
    by_contra hroot
    rw [← hchar] at hroot
    obtain ⟨u, hu, hu'⟩ :=
      (equation_11_28 α).exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition hroot
    refine hu' ⟨M * ((⨆ j : Fin k, |u j|) + ∑ l ∈ Finset.Icc k 0, |(0 : ℝ)|), ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hM 0 u (((equation_11_28 α).isSolutionWith_zero_iff u).2 hu) n
    simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero] at this ⊢
    exact this
  · intro hroot
    rw [← hchar] at hroot
    obtain ⟨M, hM0, hM⟩ :=
      ((equation_11_28 α).map (algebraMap ℝ ℂ)).exists_forall_norm_le_iff_satisfiesRootCondition
        hk |>.2 hroot
    refine ⟨M, hM0, fun φ u hu n => ?_⟩
    have := hM _ _ ((equation_11_28 α).isSolutionWith_map (algebraMap ℝ ℂ) hu) n
    simpa only [Function.comp_apply, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs, LinearRecurrence.map_order, equation_11_28_order] using this

/-- **Equation (11.65)** of [quarteroni2000numerical], the zero-stability estimate. Let a linear
multistep method with $p + 1$ steps satisfy the root condition, let $T \ge 0$, and let
$|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for all $t \in [t_0, t_0 + T]$ and
$y_1, y_2 \in \mathbb{R}$. Then there are $h_0 > 0$ and $K > 0$ with the following property. Let
$h \in (0, h_0]$ and $\varepsilon_0, \varepsilon_1 \ge 0$, let $u$ solve the method (11.60), and
let $z$ solve the perturbed method (11.59), with $|z_k - u_k| \le \varepsilon_0$ for $k \le p$
and $|\delta_k| \le \varepsilon_1$ for $p + 1 \le k \le N_h$. Then
$$|z_n - u_n| \le K (\varepsilon_0 + T\varepsilon_1), \qquad 0 \le n \le N_h.$$

The book gives the constant explicitly, $2M e^{TQ} \{(p + 1)\Delta_{[0,p]} +
T\Delta_{[p+1,n]}\}$ with $h_0 = 1/Q$. The proof specializes
`ODE.LinearMultistep.norm_sub_le_of_satisfiesRootCondition`.

**Reading.** Gives a uniform constant and independent bounds for the startup errors and later
forcing over the finite horizon. -/
theorem equation_11_65 (M : LinearMultistep) (hroot : definition_11_10 M) (hT : 0 ≤ T) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ h ∈ Ioc 0 h₀, ∀ ε₀ ε₁ : ℝ, 0 ≤ ε₀ → 0 ≤ ε₁ →
      ∀ δ u z : ℕ → ℝ, equation_11_45 M f h t₀ u → equation_11_59 M f h t₀ δ z →
        (∀ k ≤ M.p, |z k - u k| ≤ ε₀) → (∀ k, M.p + 1 ≤ k → k ≤ gridCount T h → |δ k| ≤ ε₁) →
          ∀ n ≤ gridCount T h, |z n - u n| ≤ K * (ε₀ + T * ε₁) := by
  have hf' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  obtain ⟨h₀, hh₀, K, hK, hest⟩ := M.norm_sub_le_of_satisfiesRootCondition hroot hT hf'
  refine ⟨h₀, hh₀, K, hK, fun h hh ε₀ ε₁ hε₀ hε₁ δ u z hu hz hzu hδ n hn => ?_⟩
  exact hest h hh hε₀ hε₁ (fun m _ => (M.isOrbit_iff_rhs.1 hu) m) (fun m _ => hz m)
    (fun k hk => hzu k hk) (fun k hk hk' => hδ k hk hk') n hn

/-! ### §11.6.3: zero-stability of the classical methods -/

/-- **Section 11.6.3** of [quarteroni2000numerical], consistent one-step methods are zero-stable.

* Every linear multistep method with $p = 0$ and $a_0 = 1$ satisfies the root condition, and it
  is zero-stable on $[t_0, t_0 + T]$, $T \ge 0$, for every field $f$ with
  $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ on $[t_0, t_0 + T]$.
* For all $b_0, b_{-1} \in \mathbb{R}$, the one-step method
  $u_{n+1} = u_n + h(b_0 f_n + b_{-1} f_{n+1})$ has $\rho(r) = r - 1$.

The proof uses `ODE.LinearMultistep.satisfiesRootCondition_of_p_eq_zero` and
`ODE.LinearMultistep.rho_ofOneStep`.

**Generalization.** Only the first consistency condition is needed for the characteristic root
and stability for uniformly Lipschitz fields. -/
theorem oneStep_zeroStable :
    (∀ M : LinearMultistep, M.p = 0 → ∑ j, M.a j = 1 → definition_11_10 M ∧
      ∀ (t₀ T : ℝ) (f : ℝ → ℝ → ℝ) (L : ℝ), 0 ≤ T →
        (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
          definition_11_13 M f t₀ T) ∧
    ∀ b₀ bm1 : ℝ, (characteristicPolynomials (LinearMultistep.ofOneStep 1 b₀ bm1)).1 = X - 1 := by
  refine ⟨fun M hp h0 => ?_, fun b₀ bm1 => ?_⟩
  · have hroot : definition_11_10 M :=
      M.satisfiesRootCondition_of_p_eq_zero hp ((LinearMultistep.orderCondition_zero M).2 h0)
    exact ⟨hroot, fun t₀ T f L hT hf => theorem_11_4_mpr M hroot hT hf⟩
  · rw [characteristicPolynomials, LinearMultistep.rho_ofOneStep, C_1]

/-- **Section 11.6.3** of [quarteroni2000numerical], the Adams methods are zero-stable.

* Every Adams method (11.49) with $p + 1$ steps has $\rho(r) = r^p (r - 1)$, with the roots $1$
  and $0$ (of multiplicity $p$). So it satisfies the root condition, and it is zero-stable on
  $[t_0, t_0 + T]$, $T \ge 0$, for every field $f$ with
  $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ on $[t_0, t_0 + T]$.
* For every $p$, the methods `ODE.LinearMultistep.adamsBashforth p` and
  `ODE.LinearMultistep.adamsMoulton p` satisfy the root condition.

The proof uses `ODE.LinearMultistep.rho_of_a_single`,
`ODE.LinearMultistep.satisfiesRootCondition_of_a_single` and
`ODE.LinearMultistep.adams_satisfiesRootCondition`. -/
theorem adams_zeroStable :
    (∀ M : LinearMultistep, equation_11_49 M →
      (characteristicPolynomials M).1 = X ^ M.p * (X - 1) ∧ definition_11_10 M ∧
      ∀ (t₀ T : ℝ) (f : ℝ → ℝ → ℝ) (L : ℝ), 0 ≤ T →
        (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
          definition_11_13 M f t₀ T) ∧
    ∀ p : ℕ, definition_11_10 (LinearMultistep.adamsBashforth p) ∧
      definition_11_10 (LinearMultistep.adamsMoulton p) := by
  refine ⟨fun M hM => ?_, fun p => LinearMultistep.adams_satisfiesRootCondition p⟩
  have hroot : definition_11_10 M := M.satisfiesRootCondition_of_a_single hM
  refine ⟨?_, hroot, fun t₀ T f L hT hf => theorem_11_4_mpr M hroot hT hf⟩
  rw [characteristicPolynomials, M.rho_of_a_single hM, C_1]

/-- **Section 11.6.3** of [quarteroni2000numerical], the midpoint method is zero-stable. The
midpoint method (11.43) has $\rho(r) = r^2 - 1$, with the simple roots $\pm 1$. So it satisfies
the root condition, and it is zero-stable on $[t_0, t_0 + T]$, $T \ge 0$, for every field $f$
with $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ on $[t_0, t_0 + T]$.

The proof uses `ODE.LinearMultistep.midpoint_satisfiesRootCondition`. -/
theorem midpoint_zeroStable :
    (characteristicPolynomials equation_11_43).1 = X ^ 2 - 1 ∧ definition_11_10 equation_11_43 ∧
      ∀ (t₀ T : ℝ) (f : ℝ → ℝ → ℝ) (L : ℝ), 0 ≤ T →
        (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
          definition_11_13 equation_11_43 f t₀ T :=
  ⟨LinearMultistep.rho_midpoint, LinearMultistep.midpoint_satisfiesRootCondition,
    fun _ _ _ _ hT hf => theorem_11_4_mpr _ LinearMultistep.midpoint_satisfiesRootCondition hT hf⟩

/-- **Section 11.6.3** of [quarteroni2000numerical], the Simpson method is zero-stable. The Simpson
method (11.44) has $\rho(r) = r^2 - 1$, with the simple roots $\pm 1$. So it satisfies the root
condition, and it is zero-stable on $[t_0, t_0 + T]$, $T \ge 0$, for every field $f$ with
$|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ on $[t_0, t_0 + T]$.

The proof uses `ODE.LinearMultistep.simpson_satisfiesRootCondition`. -/
theorem simpson_zeroStable :
    (characteristicPolynomials equation_11_44).1 = X ^ 2 - 1 ∧ definition_11_10 equation_11_44 ∧
      ∀ (t₀ T : ℝ) (f : ℝ → ℝ → ℝ) (L : ℝ), 0 ≤ T →
        (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
          definition_11_13 equation_11_44 f t₀ T :=
  ⟨LinearMultistep.rho_simpson, LinearMultistep.simpson_satisfiesRootCondition,
    fun _ _ _ _ hT hf => theorem_11_4_mpr _ LinearMultistep.simpson_satisfiesRootCondition hT hf⟩

/-- **Section 11.6.3** of [quarteroni2000numerical], the BDF methods with $p \le 2$. The BDF methods
of the rows $p = 0, 1, 2$ of Table 11.2 satisfy the root condition. The polynomial $\rho$ has
the roots $1$ and $1/3$ for $p = 1$, and $1$ and $(7 \pm i\sqrt{39})/22$ for $p = 2$.

The proof uses `ODE.LinearMultistep.bdf_satisfiesRootCondition`. The rows $p = 3, 4, 5$ are in
`QuarteroniSaccoSaleri.Chapter11.bdf_zeroStable`.

**Specialization.** The declaration gives the root condition for the first three rows.
`bdf_zeroStable` covers all six. -/
theorem bdf_zeroStable_of_le_two (k : Fin 6) (hk : k ≤ 2) : definition_11_10 (bdf k) :=
  LinearMultistep.bdf_satisfiesRootCondition k hk

/-- **Section 11.6.3** of [quarteroni2000numerical], the BDF methods are zero-stable. Each of the
six BDF methods of Table 11.2, $p = 0, \dots, 5$, satisfies the root condition.

The book states that the BDF methods are zero-stable for $p \le 5$ and quotes the result without
proof. For $p \le 2$ this is `QuarteroniSaccoSaleri.Chapter11.bdf_zeroStable_of_le_two`. For
$p = 3, 4, 5$, the proof locates the roots of the factor $\rho(r)/(r - 1)$ inside the unit disc
by the Schur–Cohn recursion, in `ODE.LinearMultistep.bdf_satisfiesRootCondition_all`. -/
theorem bdf_zeroStable (k : Fin 6) : definition_11_10 (bdf k) :=
  LinearMultistep.bdf_satisfiesRootCondition_all k

/-! ### Theorem 11.5 and Corollary 11.1: convergence -/

/-- **Theorem 11.5** of [quarteroni2000numerical], sufficiency. Let a linear multistep method with
$p + 1$ steps satisfy the root condition, let $T \ge 0$, and let
$|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for all $t \in [t_0, t_0 + T]$ and
$y_1, y_2 \in \mathbb{R}$. Let $y'(t) = f(t, y(t))$ for every $t \in [t_0, t_0 + T]$, and let
the method be consistent along $y$. Then there are $h_0 > 0$ and a function $C(\varepsilon, h)$
with $C(\varepsilon, h) \to 0$ as $\varepsilon \to 0^+$ and $h \to 0^+$, such that for every
$h \in (0, h_0]$ every sequence $u$ computed by the method satisfies
$$|u_n - y_n| \le C\Bigl(\max_{0 \le k \le p} |u_k - y_k|, h\Bigr), \qquad 0 \le n \le N_h.$$
So the error tends to zero when the error of the starting values does.

The limit of $C$ is taken along `𝓝[≥] 0 ×ˢ 𝓝[>] 0`. The proof specializes
`ODE.LinearMultistep.isConvergentFor_of_satisfiesRootCondition`.

**Reading.** The error is controlled jointly by the step size and the maximum startup error.
The orbit estimates are uniform over all startup values. The necessity argument uses the zero
field. -/
theorem theorem_11_5_mpr (M : LinearMultistep) (hroot : definition_11_10 M) (hT : 0 ≤ T) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) (hcons : definition_11_9 M t₀ T y) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
      Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
      ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M f h t₀ u → ∀ n ≤ gridCount T h,
        |u n - y (grid t₀ h n)| ≤ C (⨆ k : Fin (M.p + 1), |u k - y (grid t₀ h k)|) h := by
  have hf' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  exact M.isConvergentFor_of_satisfiesRootCondition hroot hT hf' hy hcons

/-- **Theorem 11.5** of [quarteroni2000numerical], the order of convergence. Let a linear multistep
method with $p + 1$ steps satisfy the root condition, let $T \ge 0$, and let
$|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for all $t \in [t_0, t_0 + T]$ and
$y_1, y_2 \in \mathbb{R}$. Let $y'(t) = f(t, y(t))$ for every $t \in [t_0, t_0 + T]$, and let
the method have order $q$ along $y$. Then there are $h_0 > 0$ and $K > 0$ such that for every
$h \in (0, h_0]$ every sequence $u$ computed by the method satisfies
$$|u_n - y_n| \le K \Bigl(\max_{0 \le k \le p} |u_k - y_k| + h^q\Bigr), \qquad 0 \le n \le
  N_h.$$
So starting errors of size $O(h^q)$ give a global error of size $O(h^q)$.

The proof specializes `ODE.LinearMultistep.isConvergentWithOrderFor_of_satisfiesRootCondition`.

**Reading.** The error is controlled jointly by the step size and the maximum startup error.
The orbit estimates are uniform over all startup values. The necessity argument uses the zero
field. -/
theorem theorem_11_5_order (M : LinearMultistep) (hroot : definition_11_10 M) (hT : 0 ≤ T) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) {q : ℕ}
    (hord : definition_11_9_order M t₀ T y q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M f h t₀ u →
      ∀ n ≤ gridCount T h,
        |u n - y (grid t₀ h n)| ≤ K * ((⨆ k : Fin (M.p + 1), |u k - y (grid t₀ h k)|) + h ^ q) := by
  have hf' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  exact M.isConvergentWithOrderFor_of_satisfiesRootCondition hroot hT hf' hy hord

/-- **Theorem 11.5** of [quarteroni2000numerical], necessity. Let $T > 0$, and let a linear
multistep method be convergent for the problem $y' = 0$ with the solution $y = 0$: there are
$h_0 > 0$ and $C(\varepsilon, h) \to 0$ as $\varepsilon \to 0^+$ and $h \to 0^+$ such that for
every $h \in (0, h_0]$ every sequence $u$ computed by the method for $f = 0$ satisfies
$|u_n| \le C(\max_{k \le p} |u_k|, h)$ for $0 \le n \le N_h$. Then the method satisfies the root
condition.

The proof specializes `ODE.LinearMultistep.satisfiesRootCondition_of_isConvergentFor`.

**Reading.** The error is controlled jointly by the step size and the maximum startup error.
The orbit estimates are uniform over all startup values. The necessity argument uses the zero
field. -/
theorem theorem_11_5_mp (M : LinearMultistep) (hT : 0 < T)
    (hconv : ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
      Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
      ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M (fun _ _ => 0) h t₀ u →
        ∀ n ≤ gridCount T h, |u n| ≤ C (⨆ k : Fin (M.p + 1), |u k|) h) :
    definition_11_10 M := by
  refine M.satisfiesRootCondition_of_isConvergentFor (t₀ := t₀) hT ?_
  simpa only [LinearMultistep.IsConvergentFor, Real.norm_eq_abs, sub_zero, equation_11_45,
    gridCount, grid] using hconv

/-- **Theorem 11.5** of [quarteroni2000numerical] (convergence). Let $T > 0$, and let a linear
multistep method with $p + 1$ steps be consistent. Then the following are equivalent:

* for every field $f$ with $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ on $[t_0, t_0 + T]$, and
  every $y$ with $y'(t) = f(t, y(t))$ on $[t_0, t_0 + T]$ along which the method is consistent,
  the method is convergent in the sense of `QuarteroniSaccoSaleri.Chapter11.theorem_11_5_mpr`:
  there are $h_0 > 0$ and $C(\varepsilon, h) \to 0$ with $|u_n - y_n| \le C(\max_{k \le p}
  |u_k - y_k|, h)$ for $h \in (0, h_0]$ and $n \le N_h$;
* the method satisfies the root condition.

**Reading.** The error is controlled jointly by the step size and the maximum startup error.
The orbit estimates are uniform over all startup values. The necessity argument uses the zero
field. -/
theorem theorem_11_5 (M : LinearMultistep) (hcons : definition_11_9_method M) (hT : 0 < T) :
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ) (y : ℝ → ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
      (∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) → definition_11_9 M t₀ T y →
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
        Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
        ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M f h t₀ u → ∀ n ≤ gridCount T h,
          |u n - y (grid t₀ h n)| ≤ C (⨆ k : Fin (M.p + 1), |u k - y (grid t₀ h k)|) h) ↔
      definition_11_10 M := by
  constructor
  · intro H
    refine theorem_11_5_mp (t₀ := t₀) M hT ?_
    have := H (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ _ => by simp)
      (fun _ _ => hasDerivAt_const _ _) (hcons t₀ T hT _ contDiff_const)
    simpa only [sub_zero] using this
  · intro hroot f L y hf hy hc
    exact theorem_11_5_mpr M hroot hT.le hf hy hc

/-- **Corollary 11.1** of [quarteroni2000numerical] (the equivalence theorem). Let $T > 0$, and let
a linear multistep method be consistent. Then the method is convergent, in the sense of
`QuarteroniSaccoSaleri.Chapter11.theorem_11_5_mpr`, for every Cauchy problem on $[t_0, t_0 + T]$
whose field is Lipschitz in $y$ and whose solution is $C^1$, if and only if it is zero-stable
for every field that is Lipschitz in $y$ on $[t_0, t_0 + T]$. Both conditions are the root
condition, by Theorems 11.4 and 11.5.

A $C^1$ solution is a function $y$ with $y'(t) = f(t, y(t))$ on $[t_0, t_0 + T]$ such that
$t \mapsto f(t, y(t))$ is continuous there. The proof specializes
`ODE.LinearMultistep.isConvergentFor_iff_isZeroStable`.

**Reading.** The error is controlled jointly by the step size and the maximum startup error.
The orbit estimates are uniform over all startup values. The necessity argument uses the zero
field. -/
theorem corollary_11_1 (M : LinearMultistep) (hcons : definition_11_9_method M) (hT : 0 < T) :
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ) (y : ℝ → ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
      (∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) →
      ContinuousOn (fun t => f t (y t)) (Icc t₀ (t₀ + T)) →
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
        Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
        ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M f h t₀ u → ∀ n ≤ gridCount T h,
          |u n - y (grid t₀ h n)| ≤ C (⨆ k : Fin (M.p + 1), |u k - y (grid t₀ h k)|) h) ↔
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
        definition_11_13 M f t₀ T) := by
  rw [theorem_11_4 M hT]
  have key := M.isConvergentFor_iff_isZeroStable (t₀ := t₀) hcons hT
  rw [M.isZeroStable_iff_satisfiesRootCondition hT] at key
  change _ ↔ M.SatisfiesRootCondition
  rw [← key]
  constructor
  · intro H f L y hf hy hcont
    exact H f L y (fun t ht y₁ y₂ => by
      have := (hf t ht).dist_le_mul y₁ y₂
      rwa [Real.dist_eq, Real.dist_eq] at this) hy hcont
  · intro H f L y hf hy hcont
    exact H f (Real.toNNReal L) y (fun t ht => LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
      hy hcont

/-! ### §11.6.4: absolute stability of multistep methods -/

/-- **Section 11.6.4** of [quarteroni2000numerical], absolute stability of a multistep method. Let
$\lambda \in \mathbb{C}$ and $h \in \mathbb{R}$. A linear multistep method is **absolutely
stable** for $\lambda$ and $h$ if $1 - h\lambda b_{-1} \neq 0$, so that the method determines
its solution, and every sequence that it computes on the test problem (11.24) with step $h$ from
$t_0 = 0$ tends to $0$.

This is Definition 11.6 for the method (11.45).

**Reading.** Fixed-step stability excludes a zero leading coefficient and asks for decay of
every orbit. The equivalence for sufficiently small positive steps can shrink the step bound to
avoid this singularity. -/
def absolutelyStable (M : LinearMultistep) (lam : ℂ) (h : ℝ) : Prop :=
  1 - (h : ℂ) * lam * M.bm1 ≠ 0 ∧
    ∀ u : ℕ → ℂ, M.IsOrbit (testProblem lam) h 0 u → Tendsto u atTop (𝓝 0)

/-- **Section 11.6.4** of [quarteroni2000numerical], the region of absolute stability (11.26) of a
multistep method: the set $\mathcal{A}$ of the $z \in \mathbb{C}$ with $1 - zb_{-1} \neq 0$ such
that every solution of the recurrence (11.54) at $z$ tends to $0$.

The definition is `ODE.LinearMultistep.absStabilityRegion`.

**Reading.** Fixed-step stability excludes a zero leading coefficient and asks for decay of
every orbit. The equivalence for sufficiently small positive steps can shrink the step bound to
avoid this singularity. -/
def equation_11_26_multistep (M : LinearMultistep) : Set ℂ :=
  M.absStabilityRegion

/-- **Section 11.6.4** of [quarteroni2000numerical], absolute stability of multistep methods. For a
linear multistep method:

* the method is absolutely stable for $\lambda$ and $h$ if and only if
  $h\lambda \in \mathcal{A}$;
* $z \in \mathcal{A}$ if and only if $1 - zb_{-1} \neq 0$ and every root $r$ of $\Pi$ at $z$ has
  $|r| < 1$;
* the method satisfies the absolute root condition (Definition 11.12) for $\lambda$ if and only
  if there is $h_0 > 0$ such that it is absolutely stable for $\lambda$ and every
  $h \in (0, h_0]$.

The proof uses `ODE.LinearMultistep.isAbsStable_iff_mem`,
`ODE.LinearMultistep.mem_absStabilityRegion_iff` and
`ODE.LinearMultistep.satisfiesAbsRootCondition_iff`.

**Reading.** Fixed-step stability excludes a zero leading coefficient and asks for decay of
every orbit. The equivalence for sufficiently small positive steps can shrink the step bound to
avoid this singularity. -/
theorem absoluteStability (M : LinearMultistep) :
    (∀ (lam : ℂ) (h : ℝ), absolutelyStable M lam h ↔ (h : ℂ) * lam ∈ equation_11_26_multistep M) ∧
    (∀ z : ℂ, z ∈ equation_11_26_multistep M ↔
      1 - z * M.bm1 ≠ 0 ∧ ∀ r : ℂ, (equation_11_55 M z).IsRoot r → ‖r‖ < 1) ∧
    ∀ lam : ℂ, definition_11_12 M lam ↔
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, absolutelyStable M lam h := by
  refine ⟨fun lam h => M.isAbsStable_iff_mem lam, fun z => M.mem_absStabilityRegion_iff z,
    fun lam => ?_⟩
  rw [definition_11_12, M.satisfiesAbsRootCondition_iff]
  exact exists_congr fun h₀ => and_congr_right fun _ => forall₂_congr fun h _ =>
    (M.isAbsStable_iff_mem lam).symm

/-- **Section 11.6.4** of [quarteroni2000numerical], A-stability of a multistep method. A linear
multistep method is **A-stable** if its region of absolute stability contains the open left
half-plane, $\mathcal{A} \supseteq \mathbb{C}^-$.

The definition is `ODE.LinearMultistep.IsAStable`. -/
def aStableMultistep (M : LinearMultistep) : Prop :=
  M.IsAStable

/-- **Section 11.6.4** of [quarteroni2000numerical], $\vartheta$-stability. Let
$\vartheta \in \mathbb{R}$. A linear multistep method is **$\vartheta$-stable** if its region of
absolute stability contains the sector
$$\{z \in \mathbb{C} : z \neq 0, \ -\vartheta < \pi - \arg z < \vartheta\},$$
written $|\arg(-z)| < \vartheta$.

The book takes $\vartheta \in (0, \pi/2)$; the definition accepts every real $\vartheta$. It is
`ODE.LinearMultistep.IsThetaStable`.

**Generalization.** Uses $|\arg(-z)|<\vartheta$ for $z\ne 0$. The definition accepts angles
outside the open interval $(0,\pi/2)$ of the source. -/
def thetaStable (M : LinearMultistep) (ϑ : ℝ) : Prop :=
  M.IsThetaStable ϑ

/-- **Section 11.6.4** of [quarteroni2000numerical]. For a linear multistep method and
$\vartheta \in \mathbb{R}$:

* the method is A-stable if and only if every $z$ with $\operatorname{Re} z < 0$ lies in
  $\mathcal{A}$;
* the method is $\vartheta$-stable if and only if every $z \neq 0$ with $|\arg(-z)| < \vartheta$
  lies in $\mathcal{A}$;
* if the method is A-stable and $\vartheta \le \pi/2$, it is $\vartheta$-stable.

**Generalization.** Uses $|\arg(-z)|<\vartheta$ for $z\ne 0$. The definition accepts angles
outside the open interval $(0,\pi/2)$ of the source. -/
theorem thetaStable_iff (M : LinearMultistep) (ϑ : ℝ) :
    (aStableMultistep M ↔ ∀ z : ℂ, z.re < 0 → z ∈ equation_11_26_multistep M) ∧
    (thetaStable M ϑ ↔
      ∀ z : ℂ, z ≠ 0 → |Complex.arg (-z)| < ϑ → z ∈ equation_11_26_multistep M) ∧
    (aStableMultistep M → ϑ ≤ Real.pi / 2 → thetaStable M ϑ) :=
  ⟨Iff.rfl, Iff.rfl, fun hA hϑ => LinearMultistep.IsAStable.isThetaStable M hA hϑ⟩

/-- **Section 11.6.4** of [quarteroni2000numerical], backward Euler and Crank–Nicolson. As linear
multistep methods, backward Euler (`QuarteroniSaccoSaleri.Chapter11.bdf 0`) and Crank–Nicolson
(`ODE.LinearMultistep.adamsMoulton 1`) are A-stable. The regions of absolute stability of
forward Euler, backward Euler and Crank–Nicolson as linear multistep methods are their regions
as one-step methods (Section 11.3).

Forward Euler is `ODE.LinearMultistep.adamsBashforth 0`. The proof uses
`ODE.LinearMultistep.absStabilityRegion_ofOneStep`. -/
theorem backwardEuler_aStable :
    aStableMultistep (bdf 0) ∧ aStableMultistep (LinearMultistep.adamsMoulton 1) ∧
    equation_11_26_multistep (LinearMultistep.adamsBashforth 0) =
      equation_11_26 (fun f => OneStep.ofIncrement (OneStep.forwardEuler f)) ∧
    equation_11_26_multistep (bdf 0) =
      equation_11_26 (fun f => OneStep.ofIncrement (OneStep.backwardEuler f)) ∧
    equation_11_26_multistep (LinearMultistep.adamsMoulton 1) =
      equation_11_26 (fun f => OneStep.ofIncrement (OneStep.crankNicolson f)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := LinearMultistep.absStabilityRegion_ofOneStep
  refine ⟨h4, h5, ?_, ?_, ?_⟩
  · rw [equation_11_26_multistep, LinearMultistep.adamsBashforth_zero_eq]
    exact h1
  · exact h2
  · rw [equation_11_26_multistep, LinearMultistep.adamsMoulton_one_eq]
    exact h3

/-- **Section 11.6.4** of [quarteroni2000numerical]. Crank–Nicolson, as the linear multistep method
`ODE.LinearMultistep.adamsMoulton 1`, is A-stable. -/
theorem crankNicolson_aStable : aStableMultistep (LinearMultistep.adamsMoulton 1) :=
  backwardEuler_aStable.2.1

/-- **Property 11.2** of [quarteroni2000numerical], the clause on explicit methods. Let a linear
multistep method be explicit, $b_{-1} = 0$, and let $\sum_{j=0}^{p} a_j = 1$. Then the method is
not A-stable, and it is not $\vartheta$-stable for any $\vartheta > 0$.

The statement assumes the first consistency condition $\sum_j a_j = 1$ of (11.52). The region of
absolute stability misses points $-t$ with $t > 0$ arbitrarily large: $\Pi$ at $z = -t$ is monic
of degree $p + 1$, a monic polynomial with all roots in the open unit disc is bounded by
$2^{p+1}$ on the closed disc, and $|\rho(x_0) + t\sigma(x_0)| \ge t|\sigma(x_0)| - |\rho(x_0)|$
at a point $x_0 \in [0, 1]$ with $\sigma(x_0) \neq 0$. The proof specializes
`ODE.LinearMultistep.not_isAStable_of_bm1_eq_zero` and
`ODE.LinearMultistep.not_isThetaStable_of_bm1_eq_zero`. The other clauses of Property 11.2 are
not formalized.

**Partial.** Treats the explicit clause assuming $\sum_j a_j=1$ and positive sector angle. The
remaining order and existence statements are separate.

**Reading.** Explicit impossibility with ∑ a_j=1 and positive θ; omits later clauses.
-/
theorem property_11_2_explicit (M : LinearMultistep) (hex : ¬ M.IsImplicit)
    (h0 : ∑ j, M.a j = 1) :
    ¬ aStableMultistep M ∧ ∀ ϑ : ℝ, 0 < ϑ → ¬ thetaStable M ϑ := by
  have hb : M.bm1 = 0 := not_not.1 hex
  have h0' : M.orderCondition 0 := (LinearMultistep.orderCondition_zero M).2 h0
  exact ⟨M.not_isAStable_of_bm1_eq_zero hb h0',
    fun ϑ hϑ => M.not_isThetaStable_of_bm1_eq_zero hb h0' hϑ⟩

/-- **Remark 11.3** of [quarteroni2000numerical], the region $\mathcal{A}^*$. For a linear multistep
method, $\mathcal{A}^*$ is the set of $z = h\lambda \in \mathbb{C}$ with $1 - zb_{-1} \neq 0$
such that every solution of the recurrence (11.54) at $z$ is bounded: there is $C > 0$ with
$|u_n| \le C$ for all $n \ge 0$.

The definition is `ODE.LinearMultistep.absStabilityRegionStar`.

**Reading.** Requires boundedness of every recurrence solution at nonsingular parameters. The
general closure claim in the remark is not included. -/
def remark_11_3 (M : LinearMultistep) : Set ℂ :=
  M.absStabilityRegionStar

/-- **Remark 11.3** of [quarteroni2000numerical]. For a linear multistep method:

* $z \in \mathcal{A}^*$ if and only if $1 - zb_{-1} \neq 0$ and every solution of the recurrence
  (11.54) at $z$ is bounded;
* $h\lambda \in \mathcal{A}^*$ if and only if $1 - h\lambda b_{-1} \neq 0$ and every sequence
  that the method computes on the test problem with step $h$ from $t_0 = 0$ is bounded;
* $\mathcal{A} \subseteq \mathcal{A}^*$;
* $z \in \mathcal{A}^*$ if and only if $1 - zb_{-1} \neq 0$ and $\Pi$ at $z$ satisfies the root
  condition.

The last part follows from Lemma 11.3, in `ODE.LinearMultistep.mem_absStabilityRegionStar_iff`.

**Reading.** Requires boundedness of every recurrence solution at nonsingular parameters. The
general closure claim in the remark is not included. -/
theorem remark_11_3_iff (M : LinearMultistep) :
    (∀ z : ℂ, z ∈ remark_11_3 M ↔ 1 - z * M.bm1 ≠ 0 ∧ ∀ u : ℕ → ℂ,
      (M.toLinearRecurrence z).IsSolution u → BddAbove (Set.range fun n => ‖u n‖)) ∧
    (∀ (lam : ℂ) (h : ℝ), (h : ℂ) * lam ∈ remark_11_3 M ↔
      1 - (h : ℂ) * lam * M.bm1 ≠ 0 ∧
      ∀ u : ℕ → ℂ, M.IsOrbit (testProblem lam) h 0 u → BddAbove (Set.range fun n => ‖u n‖)) ∧
    equation_11_26_multistep M ⊆ remark_11_3 M ∧
    ∀ z : ℂ, z ∈ remark_11_3 M ↔
      1 - z * M.bm1 ≠ 0 ∧ (equation_11_55 M z).SatisfiesRootCondition := by
  refine ⟨fun z => Iff.rfl, fun lam h => ?_, M.absStabilityRegion_subset_star,
    fun z => M.mem_absStabilityRegionStar_iff z⟩
  change (1 - (h : ℂ) * lam * M.bm1 ≠ 0 ∧ ∀ u : ℕ → ℂ,
    (M.toLinearRecurrence (h * lam)).IsSolution u → BddAbove (Set.range fun n => ‖u n‖)) ↔ _
  exact and_congr_right fun hz => forall_congr' fun u =>
    imp_congr_left (M.isOrbit_testField_iff hz).symm

/-- **Remark 11.3** of [quarteroni2000numerical], the midpoint method. For the midpoint method
(11.43), $\mathcal{A} = \emptyset$ and
$$\mathcal{A}^* = \{i\alpha : \alpha \in \mathbb{R}, \ |\alpha| < 1\}.$$

**Correction.** The book prints $\alpha \in [-1, 1]$. At $\alpha = \pm 1$ the root $\pm i$ of
$\Pi(r) = r^2 \mp 2ir - 1$ is double, so $n(\pm i)^n$ is an unbounded solution, and
$\pm i \notin \mathcal{A}^*$.

The proof uses `ODE.LinearMultistep.absStabilityRegion_midpoint`. -/
theorem remark_11_3_midpoint :
    equation_11_26_multistep equation_11_43 = ∅ ∧
      remark_11_3 equation_11_43 = {z | ∃ α : ℝ, |α| < 1 ∧ z = α * Complex.I} :=
  LinearMultistep.absStabilityRegion_midpoint

/-- **Remark 11.3** of [quarteroni2000numerical], zero-stability. Let $T > 0$. A linear multistep
method has $0 \in \mathcal{A}^*$ if and only if it is zero-stable on $[t_0, t_0 + T]$ for every
field $f$ that is Lipschitz in $y$ on $[t_0, t_0 + T]$.

At $z = 0$, $\Pi = \rho$, so $0 \in \mathcal{A}^*$ is the root condition, which is
zero-stability by Theorem 11.4. The proof uses
`ODE.LinearMultistep.zero_mem_absStabilityRegionStar_iff`.

**Reading.** The equivalence concerns zero-stability for every uniformly Lipschitz field on a
positive finite horizon. -/
theorem remark_11_3_zeroStable (M : LinearMultistep) (hT : 0 < T) :
    (0 : ℂ) ∈ remark_11_3 M ↔ ∀ (f : ℝ → ℝ → ℝ) (L : ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
        definition_11_13 M f t₀ T := by
  rw [theorem_11_4 M hT, remark_11_3, LinearMultistep.zero_mem_absStabilityRegionStar_iff]
  rfl

/-- **Equation (11.66)** of [quarteroni2000numerical], relative stability. Let
$\lambda \in \mathbb{C}$ and $h_0, T \in \mathbb{R}$. A linear multistep method with $p + 1$
steps is **relatively stable** for $\lambda$ with the threshold $h_0$ on $[0, T]$ if for every
$h \in (0, h_0]$ there is $C > 0$ such that every sequence $u$ computed by the method on the
test problem (11.24) with step $h$ satisfies
$$|u_n| \le C (|u_0| + \dots + |u_p|), \qquad p + 1 \le n \le N_h.$$

**Reading.** The bound is read on the grid of the bounded interval $[0, T]$. As printed, for all
$n$, it fails for every method whose principal root has modulus greater than $1$, for example
when $\operatorname{Re}\lambda > 0$.

The claim of the book that the strong root condition implies (11.66) is not formalized. -/
def equation_11_66 (M : LinearMultistep) (lam : ℂ) (h₀ T : ℝ) : Prop :=
  ∀ h ∈ Ioc 0 h₀, ∃ C : ℝ, 0 < C ∧ ∀ u : ℕ → ℂ, M.IsOrbit (testProblem lam) h 0 u →
    ∀ n, M.p + 1 ≤ n → n ≤ gridCount T h → ‖u n‖ ≤ C * ∑ k : Fin (M.p + 1), ‖u k‖

end QuarteroniSaccoSaleri.Chapter11
