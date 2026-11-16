/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 9.3: Newton–Cotes formulae

This module formalizes Section 9.3 of [quarteroni2000numerical]. The Newton–Cotes formulae are the
Lagrange quadrature formulae (9.2) at equally spaced nodes. The *closed* formulae have the nodes
$x_i = a + ih$ with $h = (b - a)/n$ and $n \ge 1$, so that $x_0 = a$ and $x_n = b$. The *open*
formulae have the nodes $x_i = a + (i + 1)h$ with $h = (b - a)/(n + 2)$ and $n \ge 0$. In both cases
the weights are $\alpha_i = h w_i$, where $w_i = \int_0^n \varphi_i(t)\,dt$ for the closed and
$w_i = \int_{-1}^{n+1} \varphi_i(t)\,dt$ for the open formulae, and $\varphi_i$ is the Lagrange
basis polynomial at the integer nodes $0, \dots, n$. So the $w_i$ depend only on $n$, and
$w_i = w_{n-i}$ (Table 9.2). Theorem 9.2 gives the error (9.19) for even $n$, with the degree of
exactness $n + 1$, and the degree of exactness $n$ for odd $n$. Its proof uses the
divided-difference form (9.21) of the error and the derivative identity (9.22) of Exercise 9.4.
Table 9.6 shows a negative weight of the closed formula with nine nodes.

The backbone is `Numlib.Approximation.NewtonCotes`. It supplies the weights
`Quadrature.newtonCotesWeight` and `Quadrature.openNewtonCotesWeight`, the rules
`Quadrature.closedNewtonCotes` and `Quadrature.openNewtonCotes`, the constants
`Quadrature.newtonCotesM`, `Quadrature.newtonCotesK` and their open versions, and the error theorems
for even $n$, `Quadrature.exists_sub_closedNewtonCotes_eq_of_even` and
`Quadrature.exists_sub_openNewtonCotes_eq_of_even`. The divided difference $f[x_0, \dots, x_n, x]$
is `DividedDifference.newton f (Fin.snoc x t)` of Chapter 8, and (9.21) is the integrated form of
(8.20), `QuarteroniSaccoSaleri.Chapter08.equation_8_20`.

## Main results

* Section 9.3, `QuarteroniSaccoSaleri.Chapter09.closedNewtonCotes_eq_lagrangeQuadrature`: the closed
  Lagrange formula at equispaced nodes is $h \sum_i w_i f(x_i)$ with weights $w_i$ that do not
  depend on $[a, b]$.
* Section 9.3, `QuarteroniSaccoSaleri.Chapter09.openNewtonCotes_eq_lagrangeQuadrature`: the same for
  the open formulae; for $n = 0$ the open formula is the midpoint formula.
* Section 9.3, `QuarteroniSaccoSaleri.Chapter09.newtonCotesWeight_symm`: the symmetry
  $w_i = w_{n-i}$.
* Table 9.2, `QuarteroniSaccoSaleri.Chapter09.table_9_2`: the first columns of the table of weights.
* Theorem 9.2, `QuarteroniSaccoSaleri.Chapter09.theorem_9_2_closed_even`: the error (9.19) of the
  closed formulae with even $n$.
* Theorem 9.2, `QuarteroniSaccoSaleri.Chapter09.theorem_9_2_M_closed`: the constant $M_n$ of the
  closed formulae, and $M_n < 0$.
* Theorem 9.2, `QuarteroniSaccoSaleri.Chapter09.theorem_9_2_open_even`: the error (9.19) of the open
  formulae with even $n$, with $M_n > 0$.
* Theorem 9.2, `QuarteroniSaccoSaleri.Chapter09.theorem_9_2_degreeOfExactness_even`: the closed
  formulae with even $n$ have degree of exactness $n + 1$.
* Theorem 9.2, `QuarteroniSaccoSaleri.Chapter09.theorem_9_2_order_even`: their error is
  $O(h^{n+3})$.
* Theorem 9.2, `QuarteroniSaccoSaleri.Chapter09.theorem_9_2_degreeOfExactness_odd`: the closed
  formulae with odd $n$ have degree of exactness $n$, with the error $h^{n+2} K_n$ at $x^{n+1}$.
* Theorem 9.2, `QuarteroniSaccoSaleri.Chapter09.theorem_9_2_order_odd`: their error is $O(h^{n+2})$.
* Equation (9.21), `QuarteroniSaccoSaleri.Chapter09.equation_9_21`: the error is $\int_a^b f[x_0,
  \dots, x_n, x]\, \omega_{n+1}(x)\,dx$.
* Exercise 9.4, `QuarteroniSaccoSaleri.Chapter09.exercise_9_4`: the derivative identity (9.22),
  $\frac{d}{dx} f[x_0, \dots, x_n, x] = f[x_0, \dots, x_n, x, x]$.
* Table 9.6, `QuarteroniSaccoSaleri.Chapter09.table_9_6`: the weight $w_2$ of the closed formula
  with $n = 8$ is negative.

## Conventions

* As in Section 9.2, $f \in C^k([a, b])$ is `ContDiffOn ℝ k f U` on an open set
  $U \supseteq [a, b]$, and $f^{(k)}$ is `iteratedDeriv k f`.
* The nodal polynomial $\pi_{n+1}(t) = \prod_{i=0}^{n} (t - i)$ is the backbone's
  `Quadrature.intNodal n`, whose evaluation is given by `Quadrature.intNodal_eval`.
* Exercise 9.k is Exercise k of Chapter 9.

## Not formalized

* **Theorem 9.2, the error formula (9.20) for odd $n$**, closed and open. The book states it without
  proof. It needs the constant sign of the Peano kernel of order $n$ of a rule with an odd number of
  panels. This reduces to an inequality on the partial sums of the Newton–Cotes weights, which exact
  rational arithmetic confirms for every odd $n \le 31$ but which has no formal proof. The module
  doc comment of `Numlib.Approximation.NewtonCotes` gives the reduction. The two consequences of
  (9.20), the degree of exactness and the order of infinitesimal, are formalized without it.
* **Table 9.2, the remaining columns.** They are damaged in the source.
* **Examples 9.2 and 9.3, Tables 9.3–9.5.** They are numerical.
-/

open Set intervalIntegral
open scoped Polynomial

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ}

/-! ### The weights do not depend on the interval -/

/-- **Section 9.3** of [quarteroni2000numerical], the closed Newton–Cotes formulae. Let $n \ge 1$,
let $a < b$, let $h = (b - a)/n$, and let $x_i = a + ih$ for $i = 0, \dots, n$. Then the weights
of the Lagrange quadrature formula (9.2) at these nodes are
$$\alpha_i = \int_a^b l_i(x)\,dx = h w_i, \qquad w_i = \int_0^n \varphi_i(t)\,dt,$$
and for every $f$ the formula is $I_n(f) = h \sum_{i=0}^{n} w_i f(x_i)$.

The weights $w_i$ are `Quadrature.newtonCotesWeight n i`, which do not depend on $[a, b]$, and
the rule is the backbone's `Quadrature.closedNewtonCotes n f a b`. -/
theorem closedNewtonCotes_eq_lagrangeQuadrature (hn : 1 ≤ n) (hab : a < b) :
    (∀ i, lagrangeWeights (fun k : Fin (n + 1) => a + k * ((b - a) / n)) a b i
        = (b - a) / n * Quadrature.newtonCotesWeight n i) ∧
      ∀ f : ℝ → ℝ, lagrangeQuadrature (fun k : Fin (n + 1) => a + k * ((b - a) / n)) a b f
        = Quadrature.closedNewtonCotes n f a b :=
  ⟨fun i => Quadrature.integral_basis_eq_mul_newtonCotesWeight hn hab i, fun f =>
    (Quadrature.closedNewtonCotes_eq_sum_integral_basis hn hab f).symm⟩

/-- **Section 9.3** of [quarteroni2000numerical], the open Newton–Cotes formulae. Let $n \ge 0$, let
$a < b$, let $h = (b - a)/(n + 2)$, and let $x_i = a + (i + 1)h$ for $i = 0, \dots, n$. Then the
weights of the Lagrange quadrature formula (9.2) at these nodes are $\alpha_i = h w_i$ with
$w_i = \int_{-1}^{n+1} \varphi_i(t)\,dt$, and for every $f$ the formula is
$I_n(f) = h \sum_{i=0}^{n} w_i f(x_i)$. In the case $n = 0$, $w_0 = 2$, and the formula is the
midpoint formula (9.5), $I_0(f) = (b - a) f((a + b)/2)$.

The weights $w_i$ are `Quadrature.openNewtonCotesWeight n i`, and the rule is the backbone's
`Quadrature.openNewtonCotes n f a b`. -/
theorem openNewtonCotes_eq_lagrangeQuadrature (hab : a < b) :
    (∀ i, lagrangeWeights (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) a b i
        = (b - a) / (n + 2) * Quadrature.openNewtonCotesWeight n i) ∧
      (∀ f : ℝ → ℝ,
        lagrangeQuadrature (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) a b f
          = Quadrature.openNewtonCotes n f a b) ∧
      Quadrature.openNewtonCotesWeight 0 0 = 2 ∧
      ∀ f : ℝ → ℝ, Quadrature.openNewtonCotes 0 f a b = (b - a) * f ((a + b) / 2) :=
  ⟨fun i => Quadrature.integral_basis_eq_mul_openNewtonCotesWeight hab i, fun f =>
    (Quadrature.openNewtonCotes_eq_sum_integral_basis hab f).symm,
    by rw [Quadrature.openNewtonCotesWeight_zero]; rfl,
    fun f => Quadrature.openNewtonCotes_zero f a b⟩

/-- **Section 9.3** of [quarteroni2000numerical], symmetry of the weights. For every $n$ and every
$i = 0, \dots, n$, the weights satisfy $w_{n-i} = w_i$, both for the closed and for the open
formulae.

The book says that "the weights $w_i$ and $w_{n-i}$ are equal". The substitution
$t \mapsto n - t$ carries $\varphi_i$ to $\varphi_{n-i}$ and the reference interval to itself. -/
theorem newtonCotesWeight_symm (n : ℕ) (i : Fin (n + 1)) :
    Quadrature.newtonCotesWeight n (Fin.rev i) = Quadrature.newtonCotesWeight n i ∧
      Quadrature.openNewtonCotesWeight n (Fin.rev i) = Quadrature.openNewtonCotesWeight n i :=
  ⟨Quadrature.newtonCotesWeight_symm i, Quadrature.openNewtonCotesWeight_symm i⟩

/-- **Table 9.2** of [quarteroni2000numerical], the first columns. The weights $w_i$ of the closed
formulae are $(1/2, 1/2)$ for $n = 1$, $(1/3, 4/3, 1/3)$ for $n = 2$, and $(3/8, 9/8, 9/8, 3/8)$
for $n = 3$. The weights of the open formulae are $(2)$ for $n = 0$ and $(8/3, -4/3, 8/3)$ for
$n = 2$.

The last case shows "the presence of negative weights in open formulae for $n \ge 2$". The
remaining columns of the printed table are damaged in the source and are not stated. -/
theorem table_9_2 :
    Quadrature.newtonCotesWeight 1 = ![1 / 2, 1 / 2] ∧
      Quadrature.newtonCotesWeight 2 = ![1 / 3, 4 / 3, 1 / 3] ∧
      Quadrature.newtonCotesWeight 3 = ![3 / 8, 9 / 8, 9 / 8, 3 / 8] ∧
      Quadrature.openNewtonCotesWeight 0 = ![2] ∧
      Quadrature.openNewtonCotesWeight 2 = ![8 / 3, -4 / 3, 8 / 3] :=
  ⟨Quadrature.newtonCotesWeight_one, Quadrature.newtonCotesWeight_two,
    Quadrature.newtonCotesWeight_three, Quadrature.openNewtonCotesWeight_zero,
    Quadrature.openNewtonCotesWeight_two⟩

/-! ### Theorem 9.2 -/

/-- **Theorem 9.2** of [quarteroni2000numerical], closed formulae with even $n$, equation (9.19).
Let $n \ge 2$ be even, let $a < b$, and let $f \in C^{n+2}([a, b])$. Then the error of the
closed Newton–Cotes formula is
$$E_n(f) = \int_a^b f(x)\,dx - I_n(f) = \frac{M_n}{(n + 2)!} h^{n+3} f^{(n+2)}(\xi), \qquad h =
  \frac{b - a}{n},$$
for some $\xi \in (a, b)$, where $M_n = \int_0^n t\, \pi_{n+1}(t)\,dt$.

The constant $M_n$ is `Quadrature.newtonCotesM n`;
`QuarteroniSaccoSaleri.Chapter09.theorem_9_2_M_closed` gives its value and sign. The proof is
the backbone's `Quadrature.exists_sub_closedNewtonCotes_eq_of_even`, which follows the book:
(9.21), integration by parts against $W(x) = \int_a^x \omega_{n+1}$, (9.22), the positivity of
$W$ inside $(a, b)$, and the mean value theorem. -/
theorem theorem_9_2_closed_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - Quadrature.closedNewtonCotes n f a b
      = Quadrature.newtonCotesM n / (n + 2).factorial * ((b - a) / n) ^ (n + 3)
        * iteratedDeriv (n + 2) f ξ :=
  Quadrature.exists_sub_closedNewtonCotes_eq_of_even hn hn0 hab hU hUab hf

/-- **Theorem 9.2** of [quarteroni2000numerical], the constant $M_n$ of the closed formulae. Let
$n \ge 2$ be even. Then
$$M_n = \int_0^n t\, \pi_{n+1}(t)\,dt, \qquad \pi_{n+1}(t) = \prod_{i=0}^{n} (t - i),$$
and $M_n < 0$.

The book quotes the sign from [isaacson1994analysis]. -/
theorem theorem_9_2_M_closed (hn : Even n) (hn0 : 0 < n) :
    Quadrature.newtonCotesM n = (∫ t in (0 : ℝ)..n, t * ∏ i : Fin (n + 1), (t - (i : ℕ))) ∧
      Quadrature.newtonCotesM n < 0 :=
  ⟨by simp only [Quadrature.newtonCotesM, Quadrature.intNodal_eval],
    Quadrature.newtonCotesM_neg hn hn0⟩

/-- **Theorem 9.2** of [quarteroni2000numerical], open formulae with even $n$, equation (9.19). Let
$n \ge 0$ be even, let $a < b$, and let $f \in C^{n+2}([a, b])$. Then the error of the open
Newton–Cotes formula is
$$E_n(f) = \frac{M_n}{(n + 2)!} h^{n+3} f^{(n+2)}(\xi), \qquad h = \frac{b - a}{n + 2},$$
for some $\xi \in (a, b)$, where
$$M_n = \int_{-1}^{n+1} t\, \pi_{n+1}(t)\,dt > 0.$$
For $n = 0$, where $M_0 = 2/3$ and $h = (b - a)/2$, this is the midpoint error (9.6).

The book states the open case without proof and refers to [isaacson1994analysis]. The constant
is `Quadrature.openNewtonCotesM n`, positive by `Quadrature.openNewtonCotesM_pos`. The proof is
the backbone's `Quadrature.exists_sub_openNewtonCotes_eq_of_even`, along the same route as the
closed case: (9.21), integration by parts against $W(x) = \int_a^x \omega_{n+1}$ (which for the
open nodes is negative inside $(a, b)$), (9.22), the Peano kernel theorem and the mean value
theorem. -/
theorem theorem_9_2_open_even (hn : Even n) (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    (∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - Quadrature.openNewtonCotes n f a b
        = Quadrature.openNewtonCotesM n / (n + 2).factorial * ((b - a) / (n + 2)) ^ (n + 3)
          * iteratedDeriv (n + 2) f ξ) ∧
      Quadrature.openNewtonCotesM n
          = ∫ t in (-1 : ℝ)..((n : ℝ) + 1), t * ∏ i : Fin (n + 1), (t - (i : ℕ)) ∧
        0 < Quadrature.openNewtonCotesM n :=
  ⟨Quadrature.exists_sub_openNewtonCotes_eq_of_even hn hab hU hUab hf,
    by simp only [Quadrature.openNewtonCotesM, Quadrature.intNodal_eval],
    Quadrature.openNewtonCotesM_pos hn⟩

/-- **Theorem 9.2** of [quarteroni2000numerical], degree of exactness of the closed formulae with
even $n$. Let $n \ge 2$ be even and let $a < b$. Then the closed Newton–Cotes formula is exact
for every polynomial of degree at most $n + 1$, and it is not exact for $x^{n+2}$.

The book says: "From (9.19), it turns out that the degree of exactness is equal to $n + 1$." -/
theorem theorem_9_2_degreeOfExactness_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) :
    (∀ p : ℝ[X], p.degree ≤ n + 1 →
        (∫ x in a..b, p.eval x) = Quadrature.closedNewtonCotes n (fun x => p.eval x) a b) ∧
      (∫ x in a..b, x ^ (n + 2)) ≠ Quadrature.closedNewtonCotes n (fun x => x ^ (n + 2)) a b :=
  ⟨fun _ hp => Quadrature.integral_eq_closedNewtonCotes_of_even hn hn0 hab hp,
    Quadrature.not_integral_eq_closedNewtonCotes_of_even hn hn0 hab⟩

/-- **Theorem 9.2** of [quarteroni2000numerical], order of infinitesimal of the closed formulae with
even $n$. Let $n \ge 2$ be even, let $a < b$, let $f \in C^{n+2}([a, b])$, and let
$|f^{(n+2)}(x)| \le M$ for all $x \in [a, b]$. Then
$$|E_n(f)| \le \frac{|M_n|}{(n + 2)!} M h^{n+3}, \qquad h = \frac{b - a}{n}.$$

The book says that "the order of infinitesimal is $n + 3$": the error is $O(h^{n+3})$. -/
theorem theorem_9_2_order_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |iteratedDeriv (n + 2) f x| ≤ M) :
    |(∫ x in a..b, f x) - Quadrature.closedNewtonCotes n f a b|
      ≤ |Quadrature.newtonCotesM n| / (n + 2).factorial * M * ((b - a) / n) ^ (n + 3) := by
  obtain ⟨ξ, hξ, h⟩ := theorem_9_2_closed_even hn hn0 hab hU hUab hf
  have hh : (0 : ℝ) ≤ ((b - a) / n) ^ (n + 3) := by
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    positivity
  rw [h, abs_mul, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n + 2).factorial),
    abs_of_nonneg hh]
  calc |Quadrature.newtonCotesM n| / (n + 2).factorial * ((b - a) / n) ^ (n + 3)
        * |iteratedDeriv (n + 2) f ξ|
      ≤ |Quadrature.newtonCotesM n| / (n + 2).factorial * ((b - a) / n) ^ (n + 3) * M := by
        gcongr
        exact hM ξ (Ioo_subset_Icc_self hξ)
    _ = _ := by ring

/-- **Theorem 9.2** of [quarteroni2000numerical], degree of exactness of the closed formulae with
odd $n$. Let $n$ be odd and let $a < b$. Then the closed Newton–Cotes formula is exact for every
polynomial of degree at most $n$. At $x^{n+1}$ its error is
$$E_n(x^{n+1}) = h^{n+2} K_n, \qquad h = \frac{b - a}{n}, \qquad K_n = \int_0^n
  \pi_{n+1}(t)\,dt,$$
and the formula is not exact for $x^{n+1}$.

The book says: "The degree of exactness is thus equal to $n$." The constant $K_n$ is
`Quadrature.newtonCotesK n`, and it is negative by `Quadrature.newtonCotesK_neg`. The error at
the first monomial that the formula does not reproduce is the one that (9.20) predicts, so this
fixes the constant $K_n$ of (9.20), although (9.20) itself is not formalized. -/
theorem theorem_9_2_degreeOfExactness_odd (hn : Odd n) (hab : a < b) :
    (∀ p : ℝ[X], p.degree ≤ n →
        (∫ x in a..b, p.eval x) = Quadrature.closedNewtonCotes n (fun x => p.eval x) a b) ∧
      ((∫ x in a..b, x ^ (n + 1))
            - Quadrature.closedNewtonCotes n (fun x => x ^ (n + 1)) a b
          = ((b - a) / n) ^ (n + 2) * Quadrature.newtonCotesK n ∧
        (∫ x in a..b, x ^ (n + 1)) ≠ Quadrature.closedNewtonCotes n (fun x => x ^ (n + 1)) a b) :=
  ⟨fun _ hp => Quadrature.integral_eq_closedNewtonCotes_of_degree_le hn.pos hab hp,
    Quadrature.integral_sub_closedNewtonCotes_pow_eq hn.pos hab,
    Quadrature.not_integral_eq_closedNewtonCotes_of_odd hn hab⟩

/-- **Theorem 9.2** of [quarteroni2000numerical], order of infinitesimal of the closed formulae with
odd $n$. Let $n$ be odd, let $a < b$, let $f \in C^{n+1}([a, b])$, and let
$|f^{(n+1)}(x)| \le M$ for all $x \in [a, b]$. Then
$$|E_n(f)| \le \frac{M}{(n + 1)!} \Bigl(\int_0^n |\pi_{n+1}(t)|\,dt\Bigr) h^{n+2}, \qquad h =
  \frac{b - a}{n}.$$

The book says that "the order of infinitesimal is $n + 2$": the error is $O(h^{n+2})$. The book
reads the order from (9.20), which is not formalized. The backbone proves the bound directly
from the Lagrange interpolation error (`Quadrature.abs_sub_closedNewtonCotes_le_of_contDiffOn`).
The constant $\int_0^n |\pi_{n+1}|$ is therefore larger than the sharp constant
$|K_n| = |\int_0^n \pi_{n+1}|$. -/
theorem theorem_9_2_order_odd (hn : Odd n) (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |iteratedDeriv (n + 1) f x| ≤ M) :
    |(∫ x in a..b, f x) - Quadrature.closedNewtonCotes n f a b|
      ≤ M / (n + 1).factorial * ((b - a) / n) ^ (n + 2)
        * ∫ t in (0 : ℝ)..n, |∏ i : Fin (n + 1), (t - (i : ℕ))| := by
  simpa only [Quadrature.intNodal_eval] using
    Quadrature.abs_sub_closedNewtonCotes_le_of_contDiffOn hn.pos hab hU hUab hf hM

/-! ### The divided-difference form of the error -/

/-- **Equation (9.21)** of [quarteroni2000numerical]. Let $a \le b$, let $x_0, \dots, x_n$ be
distinct real numbers, and let $f \in C^0([a, b])$. Then the error of the Lagrange quadrature
formula (9.2) at these nodes is
$$E_n(f) = \int_a^b f(x)\,dx - I_n(f) = \int_a^b f[x_0, \dots, x_n, x]\, \omega_{n+1}(x)\,dx,
  \qquad \omega_{n+1}(x) = \prod_{i=0}^{n} (x - x_i).$$

The divided difference $f[x_0, \dots, x_n, x]$ is `DividedDifference.newton f (Fin.snoc x t)`.
The proof integrates (8.20) of Chapter 8, $f - \Pi_n f = \omega_{n+1} f[x_0, \dots, x_n, \cdot]$
off the nodes, over $[a, b]$; the nodes form a null set. -/
theorem equation_9_21 (hab : a ≤ b) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hf : ContinuousOn f (Icc a b)) :
    (∫ t in a..b, f t) - lagrangeQuadrature x a b f
      = ∫ t in a..b, DividedDifference.newton f (Fin.snoc x t) * ∏ i, (t - x i) := by
  rw [lagrangeQuadrature_eq_integral_interpolate, ← integral_sub (hf.intervalIntegrable_of_Icc hab)
    ((Polynomial.continuous _).intervalIntegrable _ _)]
  refine integral_congr_ae ?_
  filter_upwards [(Set.finite_range x).countable.ae_notMem MeasureTheory.volume] with t ht _
  rw [Chapter08.equation_8_20 f hx fun i hi => ht ⟨i, hi⟩, mul_comm]

/-- **Exercise 9.4** of [quarteroni2000numerical], equation (9.22). Let $x_0, \dots, x_n$ be
distinct real numbers, let $x$ be a point that is not a node, and let $f$ be differentiable at
$x$. Then
$$\frac{d}{dx} f[x_0, \dots, x_n, x] = f[x_0, \dots, x_n, x, x].$$

The confluent divided difference on the right is the coefficient of $X^{n+2}$ in the Hermite
interpolant of $f$ at the simple nodes $x_0, \dots, x_n$ and the double node $x$, which is
`Hermite.interpolate (Fin.snoc x t) (Fin.snoc (fun _ => 0) 1) f`. The proof is the backbone's
`DividedDifference.hasDerivAt_newton_snoc`. -/
theorem exercise_9_4 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {t : ℝ}
    (ht : t ∉ Set.range x) (hf : DifferentiableAt ℝ f t) :
    HasDerivAt (fun y => DividedDifference.newton f (Fin.snoc x y))
      ((Hermite.interpolate (Fin.snoc x t) (Fin.snoc (fun _ => 0) 1) f).coeff (n + 2)) t :=
  DividedDifference.hasDerivAt_newton_snoc hx ht hf

/-! ### Table 9.6 -/

/-- **Table 9.6** of [quarteroni2000numerical]. The weight $w_2$ of the closed Newton–Cotes formula
with $n = 8$ is negative.

The book uses the table to show that "the weights of the closed Newton–Cotes formula with
$n = 8$ do not have the same sign". The value of $w_2$ is $-928/28350$; the printed table lists
the weights scaled by $4$, with the signs lost. The proof uses the moment equations
$\sum_i w_i i^k = 8^{k+1}/(k + 1)$ for $k = 0, \dots, 8$, which determine the weights. -/
theorem table_9_6 : Quadrature.newtonCotesWeight 8 2 < 0 := by
  set w := Quadrature.newtonCotesWeight 8 with hw
  have h : ∀ k : ℕ, k ≤ 8 → w 0 * 0 ^ k + w 1 * 1 ^ k + w 2 * 2 ^ k + w 3 * 3 ^ k + w 4 * 4 ^ k
      + w 5 * 5 ^ k + w 6 * 6 ^ k + w 7 * 7 ^ k + w 8 * 8 ^ k = (8 : ℝ) ^ (k + 1) / (k + 1) := by
    intro k hk
    have := Quadrature.sum_newtonCotesWeight_mul_pow (n := 8) (k := k) (by norm_num) hk
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Fin.isValue,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_zero] at this
    rw [← this]
    push_cast
    ring
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num)
  have h7 := h 7 (by norm_num)
  have h8 := h 8 (by norm_num)
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8
  linarith

end QuarteroniSaccoSaleri.Chapter09
