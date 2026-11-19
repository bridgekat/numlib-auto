/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.NewtonCotes

/-!
# Quarteroni, Sacco and Saleri, Section 9.2: Interpolatory quadratures

This module formalizes Section 9.2 of [quarteroni2000numerical], on the Lagrange quadrature formulae
(9.2) with $n = 0, 1, 2$ nodes beyond the first. These are the midpoint formula (9.5),
$I_0(f) = (b - a) f((a + b)/2)$, the trapezoidal formula (9.11),
$I_1(f) = \frac{b - a}{2} (f(a) + f(b))$, and the Cavalieri–Simpson formula (9.15), $I_2(f) =
\frac{b - a}{6} (f(a) + 4 f(\frac{a + b}{2}) + f(b))$. For each formula the module proves the error
formula, (9.6), (9.12) and (9.16), the degree of exactness, and the error of the composite formula
on $m$ panels of width $H = (b - a)/m$, (9.8), (9.14) and (9.17). The discrete mean value theorem
(Theorem 9.1) collects the panel errors of a composite formula into one value of the derivative.

The rules are the backbone rules of `Numlib.Approximation.NewtonCotes` (`Quadrature.midpointRule`,
`Quadrature.midpointSum`) and `Numlib.Approximation.CompositeQuadrature` (`Quadrature.trapezoidSum`,
`Quadrature.simpsonSum`). The single-panel formulae (9.11) and (9.15) are the composite sums with
one panel. The error formulae come from the Peano-kernel mean value theorems of those modules, and
the discrete mean value theorem is `ContinuousOn.exists_sum_mul_eq_mul_sum` of
`Numlib.Topology.Order.IntermediateValue`.

## Main results

* Equation (9.6), `QuarteroniSaccoSaleri.Chapter09.equation_9_6`: the midpoint error is
  $\frac{h^3}{3} f''(\xi)$ with $h = (b - a)/2$.
* Section 9.2.1, `QuarteroniSaccoSaleri.Chapter09.midpoint_degreeOfExactness`: the midpoint formula
  has degree of exactness $1$.
* Equation (9.7), `QuarteroniSaccoSaleri.Chapter09.equation_9_7`: the composite midpoint formula
  written out.
* Equation (9.8), `QuarteroniSaccoSaleri.Chapter09.equation_9_8`: the composite midpoint error is
  $\frac{b - a}{24} H^2 f''(\xi)$.
* Theorem 9.1, `QuarteroniSaccoSaleri.Chapter09.theorem_9_1`: the discrete mean value theorem (9.9),
  for weights of one sign.
* Equation (9.12), `QuarteroniSaccoSaleri.Chapter09.equation_9_12`: the trapezoidal error is
  $-\frac{h^3}{12} f''(\xi)$ with $h = b - a$.
* Equations (9.13)–(9.14), `QuarteroniSaccoSaleri.Chapter09.equation_9_14`: the two forms of the
  composite trapezoidal formula.
* Section 9.2.2, `QuarteroniSaccoSaleri.Chapter09.compositeTrapezoidalError`: the composite
  trapezoidal error is $-\frac{b - a}{12} H^2 f''(\xi)$.
* Equation (9.16), `QuarteroniSaccoSaleri.Chapter09.equation_9_16`: the Cavalieri–Simpson error is
  $-\frac{h^5}{90} f^{(4)}(\xi)$ with $h = (b - a)/2$.
* Section 9.2.3, `QuarteroniSaccoSaleri.Chapter09.simpson_degreeOfExactness`: the Cavalieri–Simpson
  formula has degree of exactness $3$.
* Equation (9.17), `QuarteroniSaccoSaleri.Chapter09.equation_9_17`: the composite Cavalieri–Simpson
  formula written out.
* Section 9.2.3, `QuarteroniSaccoSaleri.Chapter09.compositeSimpsonError`: the composite
  Cavalieri–Simpson error is $-\frac{b - a}{180} (H/2)^4 f^{(4)}(\xi)$.
* Exercise 9.1, `QuarteroniSaccoSaleri.Chapter09.exercise_9_1`: the error constants of the
  trapezoidal and midpoint formulae are in the ratio $-2$, so $E_1(p) = -2 E_0(p)$ for every
  polynomial $p$ of degree at most $2$.

## Conventions

* A function $f \in C^k([a, b])$ is `f : ℝ → ℝ` with `ContDiffOn ℝ k f U` on an open set
  $U \supseteq [a, b]$, as Chapter 8 reads Theorem 8.2 and as the backbone states its error
  formulae. The derivative $f^{(k)}(\xi)$ is `iteratedDeriv k f ξ`.
* The book puts the intermediate point $\xi$ of every error formula in the open interval $(a, b)$.
  The formulae (9.6) and (9.12) are stated so. The formula (9.16) and the composite formulae give
  $\xi \in [a, b]$, which is what the discrete mean value theorem on the closed interval gives (the
  backbone's `Quadrature.sub_composite_simpson_eq` and its companions).
* The composite mesh is $H = (b - a)/m$ with $m \ge 1$ panels, as the book writes it.
* Exercise 9.k is Exercise k of Chapter 9.

## Deviations from the source

* **Theorem 9.1** (reading). `QuarteroniSaccoSaleri.Chapter09.theorem_9_1` reads common sign as
  all nonnegative or all nonpositive, allowing zero weights.
* **(9.6), (9.8), (9.12) and the composite errors** (reading). Smoothness is expressed on an
  open neighbourhood of the integration interval.
  `QuarteroniSaccoSaleri.Chapter09.equation_9_8`,
  `QuarteroniSaccoSaleri.Chapter09.compositeTrapezoidalError` and
  `QuarteroniSaccoSaleri.Chapter09.compositeSimpsonError` give witnesses in the closed interval.
  The source gives interior witnesses.
* **(9.7), (9.13)–(9.14) and (9.17)** (generalization). The algebraic quadrature sums accept
  arbitrary real panel widths. The midpoint identity also allows no panels and gives an empty
  sum.
* **Exercise 9.1** (scope). `QuarteroniSaccoSaleri.Chapter09.exercise_9_1` proves the two kernel
  constants and the exact signed error ratio on polynomials of degree at most two. The source
  asks for an approximate ratio on general inputs.
* **Equation (9.16)** (reading). Smoothness is expressed on an open neighbourhood of $[a,b]$,
  and the error formula supplies $\xi \in [a,b]$. See
  `QuarteroniSaccoSaleri.Chapter09.equation_9_16`.

## Not formalized

* **Example 9.1.** It is a numerical table.
-/

open Set intervalIntegral
open scoped Polynomial

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ}

/-! ### From $C^k$ on an open neighbourhood to the derivatives on $[a, b]$ -/

/-- Let $U \supseteq [a, b]$ be open, let $f$ be of class $C^N$ on $U$, and let $j < N$. Then at
every point $x \in [a, b]$ the derivative of $f^{(j)}$ exists and equals $f^{(j+1)}(x)$.

This lemma turns the regularity hypothesis of the book into the explicit derivative hypotheses
of the backbone's Peano-kernel theorems. -/
theorem hasDerivAt_iteratedDeriv_of_contDiffOn (hU : IsOpen U) (hUab : Icc a b ⊆ U) {N : ℕ}
    (hf : ContDiffOn ℝ N f U) {j : ℕ} (hj : j < N) :
    ∀ x ∈ Icc a b, HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x :=
  fun _ hx => hf.hasDerivAt_iteratedDeriv_of_isOpen hU hj (hUab hx)

/-- Let $U \supseteq [a, b]$ be open and let $f$ be of class $C^N$ on $U$ with $N > 0$. Then at
every point $x \in [a, b]$ the function $f$ has the derivative $f'(x)$, written
`iteratedDeriv 1 f x`. -/
theorem hasDerivAt_of_contDiffOn (hU : IsOpen U) (hUab : Icc a b ⊆ U) {N : ℕ}
    (hf : ContDiffOn ℝ N f U) (hN : 0 < N) :
    ∀ x ∈ Icc a b, HasDerivAt f (iteratedDeriv 1 f x) x := fun x hx => by
  simpa using hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf hN x hx

/-- Let $U \supseteq [a, b]$ be open and let $f$ be of class $C^N$ on $U$. Then $f^{(N)}$ is
continuous on $[a, b]$. -/
theorem continuousOn_iteratedDeriv_of_contDiffOn (hU : IsOpen U) (hUab : Icc a b ⊆ U) {N : ℕ}
    (hf : ContDiffOn ℝ N f U) : ContinuousOn (iteratedDeriv N f) (Icc a b) :=
  (hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab

/-! ### Theorem 9.1 -/

/-- **Theorem 9.1** of [quarteroni2000numerical] (discrete mean value theorem). Let $a \le b$, let
$u \in C^0([a, b])$, let $x_0, \dots, x_s$ be $s + 1$ points in $[a, b]$, and let
$\delta_0, \dots, \delta_s$ be $s + 1$ constants that are all nonnegative or all nonpositive.
Then there exists $\eta \in [a, b]$ such that
$$\sum_{j=0}^{s} \delta_j u(x_j) = u(\eta) \sum_{j=0}^{s} \delta_j. \qquad (9.9)$$

The proof applies the backbone's `ContinuousOn.exists_sum_mul_eq_mul_sum` for nonnegative
weights, to $-\delta$ when the weights are nonpositive.

**Reading.** Interprets same sign as all weakly nonnegative or all weakly nonpositive, explicitly
allowing zeros.
-/
theorem theorem_9_1 (hab : a ≤ b) {u : ℝ → ℝ} (hu : ContinuousOn u (Icc a b)) {s : ℕ}
    {x : Fin (s + 1) → ℝ} (hx : ∀ j, x j ∈ Icc a b) {δ : Fin (s + 1) → ℝ}
    (hδ : (∀ j, 0 ≤ δ j) ∨ ∀ j, δ j ≤ 0) :
    ∃ η ∈ Icc a b, ∑ j, δ j * u (x j) = u η * ∑ j, δ j := by
  rcases hδ with hδ | hδ
  · exact hu.exists_sum_mul_eq_mul_sum hab hx hδ
  · obtain ⟨η, hη, h⟩ := hu.exists_sum_mul_eq_mul_sum hab hx (δ := fun j => -δ j)
      fun j => neg_nonneg.2 (hδ j)
    refine ⟨η, hη, ?_⟩
    simp only [neg_mul, Finset.sum_neg_distrib, mul_neg, neg_inj] at h
    exact h

/-! ### The midpoint formula (9.5)–(9.8) -/

/-- **Equation (9.6)** of [quarteroni2000numerical], the midpoint error. Let $a < b$ and
$f \in C^2([a, b])$. The error of the midpoint formula (9.5), $I_0(f) = (b - a) f((a + b)/2)$,
is
$$E_0(f) = \int_a^b f(x)\,dx - I_0(f) = \frac{h^3}{3} f''(\xi), \qquad h = \frac{b - a}{2},$$
for some $\xi \in (a, b)$.

The proof uses the Peano identity `Quadrature.sub_midpoint_eq_integral_peanoKernel` with the
nonnegative kernel `Quadrature.midpointKernel`, whose integral is $(b - a)^3/24 = h^3/3$, and
the weighted mean value theorem on the open interval.

**Reading.** Uses C² on open neighborhood and states the same midpoint constant with interior
witness.
-/
theorem equation_9_6 (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - (b - a) * f ((a + b) / 2)
      = ((b - a) / 2) ^ 3 / 3 * iteratedDeriv 2 f ξ := by
  have hf2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have hpeano := Quadrature.sub_midpoint_eq_integral_peanoKernel hab.le
    (hasDerivAt_of_contDiffOn hU hUab hf2 two_pos)
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf2 one_lt_two)
    ((continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2).intervalIntegrable_of_Icc hab.le)
  rw [Quadrature.midpointRule] at hpeano
  rw [hpeano]
  obtain ⟨ξ, hξ, h⟩ := intervalIntegral.exists_mem_Ioo_integral_mul_eq_mul_integral hab
    (Quadrature.continuous_midpointKernel a b).continuousOn
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2)
    (fun t _ => Quadrature.midpointKernel_nonneg a b t)
    (by rw [Quadrature.integral_midpointKernel hab.le]; positivity)
  refine ⟨ξ, hξ, ?_⟩
  rw [h, Quadrature.integral_midpointKernel hab.le]
  ring

/-- **Section 9.2.1** of [quarteroni2000numerical], degree of exactness of the midpoint formula. Let
$a < b$. The midpoint formula (9.5) is exact for every polynomial of degree at most $1$, and it
is not exact for $x^2$:
$$\int_a^b x^2\,dx \neq (b - a) \Bigl(\frac{a + b}{2}\Bigr)^2.$$

The book says that "the midpoint rule has degree of exactness equal to $1$". For degree at most
$1$ the error (9.6) vanishes, because $f'' = 0$. -/
theorem midpoint_degreeOfExactness (hab : a < b) :
    (∀ p : ℝ[X], p.degree ≤ 1 →
        (∫ x in a..b, p.eval x) = (b - a) * p.eval ((a + b) / 2)) ∧
      (∫ x in a..b, x ^ 2) ≠ (b - a) * ((a + b) / 2) ^ 2 := by
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨ξ, -, h⟩ := equation_9_6 (f := fun x => p.eval x) hab isOpen_univ (subset_univ _)
      (p.contDiffOn_eval 2 univ)
    have h2 : iteratedDeriv 2 (fun x => p.eval x) ξ = 0 := by
      have hdeg : p.natDegree < 2 :=
        Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_degree_le.2 hp)
      rw [Polynomial.iteratedDeriv_eval, Polynomial.iterate_derivative_eq_zero hdeg]
      simp
    rw [h2, mul_zero, sub_eq_zero] at h
    exact h
  · rw [integral_pow]
    intro h
    have : (b - a) ^ 3 = 0 := by push_cast at h; nlinarith
    exact (pow_ne_zero 3 (sub_ne_zero.2 hab.ne')) this

/-- **Equation (9.8)** of [quarteroni2000numerical], the composite midpoint error. Let $a < b$, let
$m \ge 1$, let $H = (b - a)/m$, and let $f \in C^2([a, b])$. The composite midpoint formula
(9.7), $I_{0,m}(f) = H \sum_{k=0}^{m-1} f(a + (2k + 1) H/2)$, has the error
$$E_{0,m}(f) = \int_a^b f(x)\,dx - I_{0,m}(f) = \frac{b - a}{24} H^2 f''(\xi)$$
for some $\xi \in [a, b]$.

The composite formula is `Quadrature.midpointSum f a H m`. The proof applies (9.6) on each panel
and Theorem 9.1 with $u = f''$ and $\delta_j = 1$.

**Reading.** The derivative is taken on an open neighbourhood of $[a,b]$. The composite error
theorem gives its witness in $[a,b]$, while the printed formula places it in $(a,b)$. -/
theorem equation_9_8 (hab : a < b) {m : ℕ} (hm : 1 ≤ m) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.midpointSum f a ((b - a) / m) m
      = (b - a) / 24 * ((b - a) / m) ^ 2 * iteratedDeriv 2 f ξ := by
  have hf2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  exact Quadrature.sub_composite_midpoint_eq hab hm rfl (hasDerivAt_of_contDiffOn hU hUab hf2
    two_pos) (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf2 one_lt_two)
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2)

/-- **Equation (9.7)** of [quarteroni2000numerical], the composite midpoint formula. For every
$H \in \mathbb{R}$ and $m \in \mathbb{N}$, the composite midpoint sum
`Quadrature.midpointSum f a H m` is
$$I_{0,m}(f) = H \sum_{k=0}^{m-1} f(x_k), \qquad x_k = a + \frac{(2k + 1) H}{2}.$$

**Reading.** Algebraic identity for any real step H and zero allowed panels as empty sum.
-/
theorem equation_9_7 (H : ℝ) (m : ℕ) :
    Quadrature.midpointSum f a H m = H * ∑ k ∈ Finset.range m, f (a + (2 * k + 1) * H / 2) := by
  rw [Quadrature.midpointSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring_nf

/-! ### The trapezoidal formula (9.11)–(9.14) -/

/-- **Equation (9.12)** of [quarteroni2000numerical], the trapezoidal error. Let $a < b$ and
$f \in C^2([a, b])$. The error of the trapezoidal formula (9.11),
$I_1(f) = \frac{b - a}{2} (f(a) + f(b))$, is
$$E_1(f) = \int_a^b f(x)\,dx - I_1(f) = -\frac{h^3}{12} f''(\xi), \qquad h = b - a,$$
for some $\xi \in (a, b)$.

The proof uses the Peano identity `Quadrature.sub_trapezoid_eq_integral_peanoKernel` with the
nonpositive kernel $(t - a)(t - b)/2$, whose integral is $-(b - a)^3/12$, and the weighted mean
value theorem on the open interval.

**Reading.** Uses C² on open neighborhood with unchanged trapezoidal coefficient and interior
witness.
-/
theorem equation_9_12 (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - (b - a) / 2 * (f a + f b)
      = -(b - a) ^ 3 / 12 * iteratedDeriv 2 f ξ := by
  have hf2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  rw [Quadrature.sub_trapezoid_eq_integral_peanoKernel
    (by rw [huIcc]; exact hasDerivAt_of_contDiffOn hU hUab hf2 two_pos)
    (by rw [huIcc]; exact hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf2 one_lt_two)
    ((continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2).intervalIntegrable_of_Icc hab.le)]
  obtain ⟨ξ, hξ, h⟩ := intervalIntegral.exists_mem_Ioo_integral_mul_eq_mul_integral_of_nonpos hab
    (K := fun t => (t - a) * (t - b) / 2) (by fun_prop)
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2)
    (fun t ht => by
      have : (t - a) * (t - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1])
        (by linarith [ht.2])
      linarith)
    (by
      rw [Quadrature.integral_peanoKernel]
      have : 0 < (b - a) ^ 3 := by positivity
      linarith)
  refine ⟨ξ, hξ, ?_⟩
  rw [h, Quadrature.integral_peanoKernel]
  ring

/-- **Equations (9.13)–(9.14)** of [quarteroni2000numerical], the composite trapezoidal formula. Let
$m \ge 1$, let $H \in \mathbb{R}$, and let $x_k = a + kH$. The composite trapezoidal sum
`Quadrature.trapezoidSum f a H m` satisfies
$$I_{1,m}(f) = \frac{H}{2} \sum_{k=0}^{m-1} \bigl(f(x_k) + f(x_{k+1})\bigr) \qquad (9.13)$$
and
$$I_{1,m}(f) = H \Bigl[\frac{f(x_0)}{2} + f(x_1) + \dots + f(x_{m-1}) + \frac{f(x_m)}{2}\Bigr].
  \qquad (9.14)$$

The second form counts each interior node twice in the first form. The book takes
$H = (b - a)/m$; the identities hold for every $H$.

**Reading.** Algebraic identities for arbitrary real H with m≥1.
-/
theorem equation_9_14 {m : ℕ} (hm : 1 ≤ m) (H : ℝ) :
    (Quadrature.trapezoidSum f a H m
        = ∑ k ∈ Finset.range m, H / 2 * (f (a + k * H) + f (a + (k + 1) * H))) ∧
      Quadrature.trapezoidSum f a H m
        = H * ((f a + f (a + m * H)) / 2 + ∑ k ∈ Finset.Ico 1 m, f (a + k * H)) :=
  ⟨rfl, Quadrature.trapezoidSum_eq hm⟩

/-- **Section 9.2.2** of [quarteroni2000numerical], the composite trapezoidal error. Let $a < b$,
let $m \ge 1$, let $H = (b - a)/m$, and let $f \in C^2([a, b])$. The composite trapezoidal
formula (9.14) has the error
$$E_{1,m}(f) = \int_a^b f(x)\,dx - I_{1,m}(f) = -\frac{b - a}{12} H^2 f''(\xi)$$
for some $\xi \in [a, b]$.

**Reading.** Open-neighborhood smoothness and closed witness in place of interior.
-/
theorem compositeTrapezoidalError (hab : a < b) {m : ℕ} (hm : 1 ≤ m) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.trapezoidSum f a ((b - a) / m) m
      = -(b - a) / 12 * ((b - a) / m) ^ 2 * iteratedDeriv 2 f ξ := by
  have hf2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  obtain ⟨ξ, hξ, h⟩ := Quadrature.sub_composite_trapezoid_eq hab hm rfl
    (hasDerivAt_of_contDiffOn hU hUab hf2 two_pos)
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf2 one_lt_two)
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2)
  exact ⟨ξ, hξ, by rw [h]; ring⟩

/-! ### The Cavalieri–Simpson formula (9.15)–(9.17) -/

/-- **Equation (9.16)** of [quarteroni2000numerical], the Cavalieri–Simpson error. Let $a < b$ and
let $f$ be four times continuously differentiable on an open neighbourhood of $[a,b]$.
The error of the Cavalieri–Simpson formula (9.15), $I_2(f) = \frac{b -
a}{6} (f(a) + 4 f(\frac{a + b}{2}) + f(b))$, is
$$E_2(f) = \int_a^b f(x)\,dx - I_2(f) = -\frac{h^5}{90} f^{(4)}(\xi), \qquad h = \frac{b -
  a}{2},$$
for some $\xi \in [a, b]$.

**Reading.** The book assumes $f \in C^4([a,b])$ and gives $\xi \in (a,b)$. The theorem uses
smoothness on a neighbourhood so that ordinary derivatives are available at the endpoints.
The backbone's error theorem gives $\xi \in [a,b]$.

The proof uses `Quadrature.sub_composite_simpson_eq` on one panel, with
$-(b - a)^5/2880 = -h^5/90$. -/
theorem equation_9_16 (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - (b - a) / 6 * (f a + 4 * f ((a + b) / 2) + f b)
      = -((b - a) / 2) ^ 5 / 90 * iteratedDeriv 4 f ξ := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  obtain ⟨ξ, hξ, h⟩ := Quadrature.sub_composite_simpson_eq hab one_pos (h := b - a) (by simp)
    (hasDerivAt_of_contDiffOn hU hUab hf4 four_pos)
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4)
  refine ⟨ξ, hξ, ?_⟩
  rw [Quadrature.simpsonSum, Finset.sum_range_one] at h
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul] at h
  rw [show a + (b - a) / 2 = (a + b) / 2 by ring, show a + (b - a) = b by ring] at h
  rw [h]
  ring

/-- **Section 9.2.3** of [quarteroni2000numerical], degree of exactness of the Cavalieri–Simpson
formula. Let $a < b$. The formula (9.15) is exact for every polynomial of degree at most $3$,
and it is not exact for $x^4$.

The book says that "(9.15) has degree of exactness equal to $3$". For degree at most $3$ the
error (9.16) vanishes, because $f^{(4)} = 0$. -/
theorem simpson_degreeOfExactness (hab : a < b) :
    (∀ p : ℝ[X], p.degree ≤ 3 →
        (∫ x in a..b, p.eval x) = (b - a) / 6 * (p.eval a + 4 * p.eval ((a + b) / 2) + p.eval b)) ∧
      (∫ x in a..b, x ^ 4) ≠ (b - a) / 6 * (a ^ 4 + 4 * ((a + b) / 2) ^ 4 + b ^ 4) := by
  refine ⟨fun p hp => Quadrature.integral_eq_simpson_of_natDegree_le hab.le
    (Polynomial.natDegree_le_iff_degree_le.2 hp), ?_⟩
  rw [integral_pow]
  intro h
  have : (b - a) ^ 5 = 0 := by push_cast at h; nlinarith
  exact (pow_ne_zero 5 (sub_ne_zero.2 hab.ne')) this

/-- **Section 9.2.3** of [quarteroni2000numerical], the composite Cavalieri–Simpson error. Let
$a < b$, let $m \ge 1$, let $H = (b - a)/m$, and let $f \in C^4([a, b])$. The composite
Cavalieri–Simpson formula (9.17), with the nodes $x_k = a + kH/2$, has the error
$$E_{2,m}(f) = \int_a^b f(x)\,dx - I_{2,m}(f) = -\frac{b - a}{180} \Bigl(\frac{H}{2}\Bigr)^4
  f^{(4)}(\xi)$$
for some $\xi \in [a, b]$.

The composite formula is the backbone's `Quadrature.simpsonSum f a H m`.

**Reading.** Open-neighborhood smoothness and closed witness in place of interior.
-/
theorem compositeSimpsonError (hab : a < b) {m : ℕ} (hm : 1 ≤ m) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.simpsonSum f a ((b - a) / m) m
      = -(b - a) / 180 * ((b - a) / m / 2) ^ 4 * iteratedDeriv 4 f ξ := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  obtain ⟨ξ, hξ, h⟩ := Quadrature.sub_composite_simpson_eq hab hm rfl
    (hasDerivAt_of_contDiffOn hU hUab hf4 four_pos)
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4)
  exact ⟨ξ, hξ, by rw [h]; ring⟩

/-- **Equation (9.17)** of [quarteroni2000numerical], the composite Cavalieri–Simpson formula. Let
$m \ge 1$, let $H \in \mathbb{R}$, and let $x_k = a + kH/2$ for $k = 0, \dots, 2m$. The
composite Simpson sum `Quadrature.simpsonSum f a H m` is
$$I_{2,m}(f) = \frac{H}{6} \Bigl[f(x_0) + 2 \sum_{r=1}^{m-1} f(x_{2r}) + 4 \sum_{s=0}^{m-1}
  f(x_{2s+1}) + f(x_{2m})\Bigr].$$

The book takes $H = (b - a)/m$; the identity holds for every $H$.

**Reading.** Algebraic weights for arbitrary real H and positive panel count.
-/
theorem equation_9_17 {m : ℕ} (hm : 1 ≤ m) (H : ℝ) :
    Quadrature.simpsonSum f a H m
      = H / 6 * (f a + 2 * ∑ r ∈ Finset.Ico 1 m, f (a + (2 * r) * (H / 2))
        + 4 * ∑ s ∈ Finset.range m, f (a + (2 * s + 1) * (H / 2)) + f (a + (2 * m) * (H / 2))) := by
  set g : ℕ → ℝ := fun j => f (a + j * (H / 2)) with hg
  have hnode : ∀ j : ℕ, f (a + j * H) = g (2 * j) := fun j => by
    simp only [hg]; push_cast; ring_nf
  have hmid : ∀ j : ℕ, f (a + j * H + H / 2) = g (2 * j + 1) := fun j => by
    simp only [hg]; push_cast; ring_nf
  have hodd : ∀ s : ℕ, f (a + (2 * s + 1) * (H / 2)) = g (2 * s + 1) := fun s => by
    simp only [hg]; push_cast; ring_nf
  have heven : ∀ r : ℕ, f (a + (2 * r) * (H / 2)) = g (2 * r) := fun r => by
    simp only [hg]; push_cast; ring_nf
  -- the even-node sums: `∑_{j<m} g(2j)` and `∑_{j<m} g(2(j+1))` against the interior sum
  have hbot : ∑ j ∈ Finset.range m, g (2 * j) = g 0 + ∑ r ∈ Finset.Ico 1 m, g (2 * r) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm]
  have htop : ∑ j ∈ Finset.range m, g (2 * (j + 1))
      = (∑ j ∈ Finset.range m, g (2 * j)) + g (2 * m) - g 0 := by
    have h1 := Finset.sum_range_succ' (fun j => g (2 * j)) m
    have h2 := Finset.sum_range_succ (fun j => g (2 * j)) m
    simp only [mul_zero] at h1 h2
    linarith
  have hsplit : Quadrature.simpsonSum f a H m
      = ∑ j ∈ Finset.range m, H / 6 * (g (2 * j) + 4 * g (2 * j + 1) + g (2 * (j + 1))) := by
    rw [Quadrature.simpsonSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hnode j, hmid j, show a + ((j : ℝ) + 1) * H = a + ((j + 1 : ℕ) : ℝ) * H by push_cast; ring,
      hnode (j + 1)]
  have hlin : ∑ j ∈ Finset.range m, H / 6 * (g (2 * j) + 4 * g (2 * j + 1) + g (2 * (j + 1)))
      = H / 6 * ((∑ j ∈ Finset.range m, g (2 * j)) + 4 * ∑ j ∈ Finset.range m, g (2 * j + 1)
        + ∑ j ∈ Finset.range m, g (2 * (j + 1))) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, hlin, htop, hbot]
  simp only [hodd, heven]
  have hg0 : g 0 = f a := by simp [hg]
  rw [hg0]
  ring

/-! ### Exercise 1 -/

/-- **Exercise 9.1** of [quarteroni2000numerical], in its exact form. Let $a < b$. The error
constants of (9.12) and (9.6) are
$$\int_a^b \frac{(t - a)(t - b)}{2}\,dt = -\frac{(b - a)^3}{12}, \qquad \int_a^b K_0(t)\,dt =
  \frac{(b - a)^3}{24},$$
where $K_0$ is the Peano kernel `Quadrature.midpointKernel` of the midpoint formula. They are in
the ratio $-2$. Hence for every polynomial $p$ of degree at most $2$, whose second derivative is
constant, the trapezoidal and midpoint errors satisfy $E_1(p) = -2 E_0(p)$.

The exercise is cited in Example 9.4, and the book writes the result as
$|E_1(f)| \simeq 2 |E_0(f)|$.

**Scope.** The exact signed relation is for polynomial inputs with a constant second
derivative. For general smooth inputs, the two error formulas can evaluate the derivative at
different points. -/
theorem exercise_9_1 (hab : a < b) :
    ((∫ t in a..b, (t - a) * (t - b) / 2) = -(b - a) ^ 3 / 12 ∧
      (∫ t in a..b, Quadrature.midpointKernel a b t) = (b - a) ^ 3 / 24) ∧
    ∀ p : ℝ[X], p.degree ≤ 2 →
      (∫ x in a..b, p.eval x) - (b - a) / 2 * (p.eval a + p.eval b)
        = -2 * ((∫ x in a..b, p.eval x) - (b - a) * p.eval ((a + b) / 2)) := by
  refine ⟨⟨Quadrature.integral_peanoKernel, Quadrature.integral_midpointKernel hab.le⟩,
    fun p hp => ?_⟩
  have hpc : ContDiffOn ℝ 2 (fun x => p.eval x) univ := p.contDiffOn_eval 2 univ
  obtain ⟨ξ, -, h1⟩ := equation_9_12 hab isOpen_univ (subset_univ _) hpc
  obtain ⟨η, -, h0⟩ := equation_9_6 hab isOpen_univ (subset_univ _) hpc
  -- the second derivative of a quadratic is constant
  have hconst : iteratedDeriv 2 (fun x => p.eval x) ξ = iteratedDeriv 2 (fun x => p.eval x) η := by
    rw [Polynomial.iteratedDeriv_eval]
    have hdeg : (Polynomial.derivative^[2] p).natDegree = 0 := by
      have h2 : p.natDegree ≤ 2 := Polynomial.natDegree_le_iff_degree_le.2 hp
      have := Polynomial.natDegree_iterate_derivative p 2
      omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hdeg
    simp [← hc]
  rw [h1, h0, hconst]
  ring

end QuarteroniSaccoSaleri.Chapter09
