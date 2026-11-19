/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 9.5: Hermite quadrature formulae

This module formalizes Section 9.5 of [quarteroni2000numerical]. The Hermite interpolant (9.28) of
$f$ at distinct nodes $x_0, \dots, x_n$ is
$$H_{2n+1} f = \sum_{i=0}^{n} f(x_i) \mathcal{L}_i + \sum_{i=0}^{n} f'(x_i) \mathcal{M}_i, \qquad
  \mathcal{L}_k = \Bigl[1 - \frac{\omega''(x_k)}{\omega'(x_k)} (x - x_k)\Bigr] l_k^2, \qquad
  \mathcal{M}_k = (x - x_k) l_k^2.$$
Its integral is the Hermite quadrature formula (9.29), $I_n(f) = \sum_k \alpha_k f(x_k) + \sum_k
\beta_k f'(x_k)$ with $\alpha_k = I(\mathcal{L}_k)$ and $\beta_k = I(\mathcal{M}_k)$, which has
degree of exactness $2n + 1$. For $n = 1$ at the nodes $a, b$ it is the corrected trapezoidal
formula (9.30), whose error is $\frac{h^5}{720} f^{(4)}(\xi)$ (9.31). In the composite form (9.32)
the corrections at the interior nodes cancel, only the end correction
$\frac{H^2}{12} (f'(a) - f'(b))$ remains, and the error has order $4$ in $H$, as Example 9.5
observes. Exercise 9.9, cited there, compares (9.31) with the Simpson error (9.16).

The backbone is the Hermite part of `Numlib.Approximation.NewtonCotes`: `Quadrature.hermiteBasisL`,
`Quadrature.hermiteBasisM`, `Quadrature.hermiteQuadrature`,
`Quadrature.integral_eq_hermiteQuadrature_of_degree_le`, `Quadrature.correctedTrapezoid`,
`Quadrature.correctedTrapezoidSum` and their error theorems. The Hermite interpolant is
`Hermite.interpolate x (fun _ => 1) f` of Chapter 8, and (9.28) is Example 8.6 read with the
normalization of the cardinal polynomials of the book.

## Main results

* Section 9.5, `QuarteroniSaccoSaleri.Chapter09.hermiteBasisL_eq_example_8_6_A`: the cardinal
  polynomial $\mathcal{L}_k$ is the polynomial $A_k$ of Example 8.6.
* Section 9.5, `QuarteroniSaccoSaleri.Chapter09.hermiteBasisM_eq_example_8_6_B`: the cardinal
  polynomial $\mathcal{M}_k$ is the polynomial $B_k$ of Example 8.6.
* Equation (9.28), `QuarteroniSaccoSaleri.Chapter09.equation_9_28`: the Hermite interpolant in the
  cardinal basis $\mathcal{L}_k, \mathcal{M}_k$.
* Equation (9.29), `QuarteroniSaccoSaleri.Chapter09.equation_9_29`: the Hermite quadrature formula
  is the integral of the Hermite interpolant.
* Section 9.5, `QuarteroniSaccoSaleri.Chapter09.hermiteQuadrature_degreeOfExactness`: the degree of
  exactness is $2n + 1$.
* Equation (9.30), `QuarteroniSaccoSaleri.Chapter09.equation_9_30`: the corrected trapezoidal
  formula and its weights.
* Equation (9.31), `QuarteroniSaccoSaleri.Chapter09.equation_9_31`: its error is
  $\frac{h^5}{720} f^{(4)}(\xi)$ with $h = b - a$.
* Equation (9.32), `QuarteroniSaccoSaleri.Chapter09.equation_9_32`: the composite formula, with the
  interior corrections cancelled.
* Section 9.5, `QuarteroniSaccoSaleri.Chapter09.compositeCorrectedTrapezoidalError`: its error is
  $\frac{(b - a) H^4}{720} f^{(4)}(\xi)$.
* Exercise 9.9, `QuarteroniSaccoSaleri.Chapter09.exercise_9_9`: $E_1^{corr}(f) = -4 E_2(f)$ for
  every $f$ with constant fourth derivative.

## Conventions

* As in Section 9.2, $f \in C^k([a, b])$ is `ContDiffOn ℝ k f U` on an open set
  $U \supseteq [a, b]$.
* The derivative $f'$ is `deriv f`, so that $f \in C^4([a, b])$ supplies it.
* The book puts the points $\xi$ of (9.31) and of the composite error in $(a, b)$. The statements
  here give $\xi \in [a, b]$.
* Exercise 9.k is Exercise k of Chapter 9.

## Deviations from the source

* **(9.28)–(9.30)** (reading). `QuarteroniSaccoSaleri.Chapter09.equation_9_28` uses the total
  derivative, and the quadrature sums can also take independent derivative data.
  `QuarteroniSaccoSaleri.Chapter09.hermiteQuadrature_degreeOfExactness` proves exactness through
  degree $2n+1$ without a sharpness statement.
* **(9.31) and the composite error** (reading and extension). Smoothness is expressed on an open
  neighbourhood and the witness lies in the closed interval.
  `QuarteroniSaccoSaleri.Chapter09.compositeCorrectedTrapezoidalError` gives an exact error
  formula where the source discusses the fourth-order rate.
* **Exercise 9.9** (scope). `QuarteroniSaccoSaleri.Chapter09.exercise_9_9` gives the signed
  error ratio on polynomials of degree at most four, where the fourth derivative is constant.
* **Equation (9.32)** (correction). The source prints the end correction
  $\frac{(b - a)^2}{12} [f'(a) - f'(b)]$. On $m$ panels it is $\frac{H^2}{12} [f'(a) - f'(b)]$ with
  $H = (b - a)/m$. See `QuarteroniSaccoSaleri.Chapter09.equation_9_32`.

## Not formalized

* **Example 9.5.** It is a numerical table.
-/

open Set intervalIntegral Polynomial
open scoped Polynomial

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ}

/-! ### The Hermite interpolant (9.28) and the Hermite formula (9.29) -/

/-- Let $x_0, \dots, x_n$ be distinct. Then for each $k$ the cardinal polynomial $\mathcal{L}_k$ of
the book is the osculatory basis polynomial $A_k$ of Example 8.6,
`QuarteroniSaccoSaleri.Chapter08.example_8_6_A`.

The two polynomials agree because $\omega''(x_k)/\omega'(x_k) = 2 l_k'(x_k)$
(`Lagrange.eval_derivative_basis_self`). -/
theorem hermiteBasisL_eq_example_8_6_A {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (k : Fin (n + 1)) : Quadrature.hermiteBasisL x k = Chapter08.example_8_6_A x k := by
  rw [Quadrature.hermiteBasisL, Chapter08.example_8_6_A, Lagrange.eval_derivative_basis_self hx]
  congr 2
  rw [mul_assoc, ← C_ofNat, mul_comm (X - C (x k)), ← mul_assoc, ← C_mul]
  congr 2
  rw [mul_div_assoc', mul_div_mul_left _ _ (two_ne_zero' ℝ)]

/-- For all nodes $x_0, \dots, x_n$ and each $k$, the cardinal polynomial
$\mathcal{M}_k = (x - x_k) l_k^2$ of the book is the polynomial $B_k$ of Example 8.6,
`QuarteroniSaccoSaleri.Chapter08.example_8_6_B`.

**Reading.** Total basis expression equality allows coincident nodes.
-/
theorem hermiteBasisM_eq_example_8_6_B (x : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    Quadrature.hermiteBasisM x k = Chapter08.example_8_6_B x k := rfl

/-- **Equation (9.28)** of [quarteroni2000numerical]. Let $x_0, \dots, x_n$ be distinct and let
$f : \mathbb{R} \to \mathbb{R}$. Then the Hermite interpolating polynomial of $f$ (Section 8.4)
at these nodes, for the $2(n + 1)$ values $f(x_k)$ and $f'(x_k)$, is
$$H_{2n+1} f = \sum_{i=0}^{n} f(x_i) \mathcal{L}_i + \sum_{i=0}^{n} f'(x_i) \mathcal{M}_i,$$
where $\mathcal{L}_k = [1 - (\omega''(x_k)/\omega'(x_k))(x - x_k)] l_k^2$ and
$\mathcal{M}_k = (x - x_k) l_k^2$ are polynomials of $\mathbb{P}_{2n+1}$.

The interpolant is `Hermite.interpolate x (fun _ => 1) f`, and $f'$ is `deriv f`. The statement
is Example 8.6 of Chapter 8 with $\omega''(x_k)/\omega'(x_k) = 2 l_k'(x_k)$.

**Reading.** Uses total derivative for arbitrary f instead of requiring defined derivative data.
-/
theorem equation_9_28 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (f : ℝ → ℝ) :
    Hermite.interpolate x (fun _ => 1) f
      = ∑ i, C (f (x i)) * Quadrature.hermiteBasisL x i
        + ∑ i, C (deriv f (x i)) * Quadrature.hermiteBasisM x i := by
  rw [Chapter08.example_8_6 hx f, Finset.sum_add_distrib]
  simp only [hermiteBasisL_eq_example_8_6_A hx, hermiteBasisM_eq_example_8_6_B]

/-- **Equation (9.29)** of [quarteroni2000numerical], the Hermite quadrature formula. Let
$x_0, \dots, x_n$ be distinct, let $a, b \in \mathbb{R}$, and let
$f : \mathbb{R} \to \mathbb{R}$. For every function $f'$ the backbone's
`Quadrature.hermiteQuadrature x a b f f'` is
$$I_n(f) = \sum_{k=0}^{n} \alpha_k f(x_k) + \sum_{k=0}^{n} \beta_k f'(x_k), \qquad \alpha_k =
  \int_a^b \mathcal{L}_k, \qquad \beta_k = \int_a^b \mathcal{M}_k.$$
When $f'$ is the derivative of $f$, this is the integral over $[a, b]$ of the Hermite
interpolant (9.28) of $f$.

**Reading.** First identity allows arbitrary independently supplied derivative values; second uses
total derivative in the exact Hermite integral identity.
-/
theorem equation_9_29 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (a b : ℝ) (f : ℝ → ℝ) :
    (∀ f' : ℝ → ℝ, Quadrature.hermiteQuadrature x a b f f'
        = ∑ k, (∫ t in a..b, (Quadrature.hermiteBasisL x k).eval t) * f (x k)
          + ∑ k, (∫ t in a..b, (Quadrature.hermiteBasisM x k).eval t) * f' (x k)) ∧
      Quadrature.hermiteQuadrature x a b f (deriv f)
        = ∫ t in a..b, (Hermite.interpolate x (fun _ => 1) f).eval t := by
  refine ⟨fun _ => rfl, ?_⟩
  rw [equation_9_28 hx f]
  simp only [eval_add, eval_finsetSum, eval_mul, eval_C]
  rw [integral_add
    ((by fun_prop : Continuous fun t => ∑ k, f (x k) * (Quadrature.hermiteBasisL x k).eval t)
      |>.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t =>
      ∑ k, deriv f (x k) * (Quadrature.hermiteBasisM x k).eval t) |>.intervalIntegrable _ _),
    integral_finsetSum fun k _ => ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _,
    integral_finsetSum fun k _ => ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _,
    Quadrature.hermiteQuadrature]
  simp only [integral_const_mul]
  congr 1 <;> exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Section 9.5** of [quarteroni2000numerical], degree of exactness of the Hermite formula. Let
$x_0, \dots, x_n$ be distinct, let $a, b \in \mathbb{R}$, and let $p$ be a polynomial of degree
at most $2n + 1$. Then
$$\int_a^b p(t)\,dt = \sum_{k=0}^{n} \alpha_k p(x_k) + \sum_{k=0}^{n} \beta_k p'(x_k).$$

The book says: "Formula (9.29) has degree of exactness equal to $2n + 1$." The reason is that
$p$ is its own Hermite interpolant. The proof is the backbone's
`Quadrature.integral_eq_hermiteQuadrature_of_degree_le`.

**Scope.** This proves exactness through degree $2n+1$. The source's exact-degree statement
also excludes higher degree. -/
theorem hermiteQuadrature_degreeOfExactness {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (a b : ℝ) {p : ℝ[X]} (hp : p.degree ≤ (2 * n + 1 : ℕ)) :
    (∫ t in a..b, p.eval t)
      = Quadrature.hermiteQuadrature x a b (fun t => p.eval t) (fun t => (derivative p).eval t) :=
  Quadrature.integral_eq_hermiteQuadrature_of_degree_le hx a b hp

/-! ### The corrected trapezoidal formula (9.30)–(9.32) -/

/-- **Equation (9.30)** of [quarteroni2000numerical], the corrected trapezoidal formula. Let
$a \neq b$. With $n = 1$ and the nodes $x_0 = a$, $x_1 = b$, the Hermite formula is the
**corrected trapezoidal formula**
$$I_1^{corr}(f) = \frac{b - a}{2} [f(a) + f(b)] + \frac{(b - a)^2}{12} [f'(a) - f'(b)]$$
for all functions $f$ and $f'$. Its weights are $\alpha_0 = \alpha_1 = (b - a)/2$,
$\beta_0 = (b - a)^2/12$ and $\beta_1 = -\beta_0$.

The identity of the two functionals is the backbone's
`Quadrature.hermiteQuadrature_two_eq_correctedTrapezoid`. The weights follow from it at
functions that vanish at one node.

**Correction.** Same corrected weights, with arbitrary independently supplied derivative function
and ordered or reversed distinct endpoints.
-/
theorem equation_9_30 (hab : a ≠ b) :
    (∀ f f' : ℝ → ℝ, Quadrature.hermiteQuadrature ![a, b] a b f f'
        = (b - a) / 2 * (f a + f b) + (b - a) ^ 2 / 12 * (f' a - f' b)) ∧
      (∫ t in a..b, (Quadrature.hermiteBasisL ![a, b] 0).eval t) = (b - a) / 2 ∧
      (∫ t in a..b, (Quadrature.hermiteBasisL ![a, b] 1).eval t) = (b - a) / 2 ∧
      (∫ t in a..b, (Quadrature.hermiteBasisM ![a, b] 0).eval t) = (b - a) ^ 2 / 12 ∧
      (∫ t in a..b, (Quadrature.hermiteBasisM ![a, b] 1).eval t) = -((b - a) ^ 2 / 12) := by
  have key : ∀ f f' : ℝ → ℝ, Quadrature.hermiteQuadrature ![a, b] a b f f'
      = (b - a) / 2 * (f a + f b) + (b - a) ^ 2 / 12 * (f' a - f' b) := fun f f' =>
    Quadrature.hermiteQuadrature_two_eq_correctedTrapezoid hab f f'
  refine ⟨key, ?_, ?_, ?_, ?_⟩
  · have h := key (fun t => if t = a then 1 else 0) 0
    simp [Quadrature.hermiteQuadrature, Fin.sum_univ_two, hab.symm] at h
    linarith
  · have h := key (fun t => if t = b then 1 else 0) 0
    simp [Quadrature.hermiteQuadrature, Fin.sum_univ_two, hab] at h
    linarith
  · have h := key 0 (fun t => if t = a then 1 else 0)
    simp [Quadrature.hermiteQuadrature, Fin.sum_univ_two, hab.symm] at h
    linarith
  · have h := key 0 (fun t => if t = b then 1 else 0)
    simp [Quadrature.hermiteQuadrature, Fin.sum_univ_two, hab] at h
    linarith

/-- **Equation (9.31)** of [quarteroni2000numerical]. Let $a \le b$ and $f \in C^4([a, b])$. Then
the error of the corrected trapezoidal formula (9.30) is
$$E_1^{corr}(f) = \int_a^b f(x)\,dx - I_1^{corr}(f) = \frac{h^5}{720} f^{(4)}(\xi), \qquad h =
  b - a,$$
for some $\xi \in [a, b]$.

The error has order $h^5$, like the Cavalieri–Simpson formula, against the $h^3$ of (9.12). The
book puts $\xi$ in $(a, b)$. The proof is the backbone's
`Quadrature.exists_sub_correctedTrapezoid_eq`.

**Reading.** Uses open-neighborhood C⁴ and closed witness, including degenerate a=b.
-/
theorem equation_9_31 (hab : a ≤ b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.correctedTrapezoid f (deriv f) a b
      = (b - a) ^ 5 / 720 * iteratedDeriv 4 f ξ := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have h1 := hasDerivAt_of_contDiffOn hU hUab hf4 four_pos
  rw [iteratedDeriv_one] at h1
  exact Quadrature.exists_sub_correctedTrapezoid_eq hab h1
    (by simpa using hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num : 1 < 4))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4)

/-- **Equation (9.32)** of [quarteroni2000numerical], the composite corrected trapezoidal formula.
Let $f, f' : \mathbb{R} \to \mathbb{R}$, let $m \ge 1$, let $H = (b - a)/m$, and let
$x_k = a + kH$. Then the composite formula `Quadrature.correctedTrapezoidSum f f' a b m` is
$$I_{1,m}^{corr}(f) = H \Bigl\{\frac{1}{2} [f(x_0) + f(x_m)] + f(x_1) + \dots +
  f(x_{m-1})\Bigr\} + \frac{H^2}{12} [f'(a) - f'(b)],$$
and it equals the sum over the $m$ panels of the corrected trapezoidal formulae (9.30).

**Correction.** The source prints the end correction $\frac{(b - a)^2}{12} [f'(a) - f'(b)]$. On
$m$ panels the constant is $H^2/12$, as in Program 75 of the book (`(h^2/12)*(f1a-f1b)`) and as
the cancellation argument gives.

The panel corrections $\frac{H^2}{12} (f'(x_k) - f'(x_{k+1}))$ telescope, so the first
derivatives at the interior nodes $x_1, \dots, x_{m-1}$ cancel. -/
theorem equation_9_32 (f f' : ℝ → ℝ) (a b : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Quadrature.correctedTrapezoidSum f f' a b m
        = (b - a) / m * ((f a + f (a + m * ((b - a) / m))) / 2
            + ∑ k ∈ Finset.Ico 1 m, f (a + k * ((b - a) / m)))
          + ((b - a) / m) ^ 2 / 12 * (f' a - f' b) ∧
      ∑ j ∈ Finset.range m,
          Quadrature.correctedTrapezoid f f' (a + j * ((b - a) / m)) (a + (j + 1) * ((b - a) / m))
        = Quadrature.correctedTrapezoidSum f f' a b m :=
  ⟨by rw [Quadrature.correctedTrapezoidSum, Quadrature.trapezoidSum_eq hm],
    (Quadrature.correctedTrapezoidSum_eq_sum f f' a b m).symm⟩

/-- **Section 9.5** of [quarteroni2000numerical], the error of (9.32). Let $a < b$, let $m \ge 1$,
let $H = (b - a)/m$, and let $f \in C^4([a, b])$. Then
$$\int_a^b f(x)\,dx - I_{1,m}^{corr}(f) = \frac{(b - a) H^4}{720} f^{(4)}(\xi)$$
for some $\xi \in [a, b]$.

This is the order $4$ that Example 9.5 observes. The proof is the backbone's
`Quadrature.sub_correctedTrapezoidSum_eq`.

**Reading.** Derives exact fourth-order composite error with closed witness beyond the source's
numerical rate discussion.
-/
theorem compositeCorrectedTrapezoidalError (hab : a < b) {m : ℕ} (hm : 1 ≤ m) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.correctedTrapezoidSum f (deriv f) a b m
      = (b - a) * ((b - a) / m) ^ 4 / 720 * iteratedDeriv 4 f ξ := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have h1 := hasDerivAt_of_contDiffOn hU hUab hf4 four_pos
  rw [iteratedDeriv_one] at h1
  exact Quadrature.sub_correctedTrapezoidSum_eq hab hm h1
    (by simpa using hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num : 1 < 4))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4)

/-! ### Exercise 9 -/

/-- **Exercise 9.9** of [quarteroni2000numerical], in its exact form. Let $a < b$ and let $p$ be a
polynomial of degree at most $4$. Then the error of the corrected trapezoidal formula (9.30) and
the error of the Cavalieri–Simpson formula (9.15) on $[a, b]$ satisfy
$$E_1^{corr}(p) = -4 E_2(p).$$

The exercise is cited in Example 9.5, and the book writes the result as
$|E_1^{corr}(f)| \simeq 4 |E_2(f)|$. The error constants of (9.31) and (9.16) are $h^5/720$ and
$-(h/2)^5/90 = -h^5/2880$ with $h = b - a$, in the ratio $-4$, and the fourth derivative of $p$
is constant.

**Correction.** Exact signed ratio of corrected-trapezoidal to Simpson error for polynomials of
degree at most four.
-/
theorem exercise_9_9 (hab : a < b) {p : ℝ[X]} (hp : p.degree ≤ 4) :
    (∫ x in a..b, p.eval x)
        - Quadrature.correctedTrapezoid (fun x => p.eval x) (deriv fun x => p.eval x) a b
      = -4 * ((∫ x in a..b, p.eval x)
        - (b - a) / 6 * (p.eval a + 4 * p.eval ((a + b) / 2) + p.eval b)) := by
  have hpc : ContDiffOn ℝ 4 (fun x => p.eval x) univ := p.contDiffOn_eval 4 univ
  obtain ⟨ξ, -, h1⟩ := equation_9_31 hab.le isOpen_univ (subset_univ _) hpc
  obtain ⟨η, -, h2⟩ := equation_9_16 hab isOpen_univ (subset_univ _) hpc
  have hconst : iteratedDeriv 4 (fun x => p.eval x) ξ = iteratedDeriv 4 (fun x => p.eval x) η := by
    rw [Polynomial.iteratedDeriv_eval]
    have hdeg : (Polynomial.derivative^[4] p).natDegree = 0 := by
      have h4 : p.natDegree ≤ 4 := Polynomial.natDegree_le_iff_degree_le.2 hp
      have := Polynomial.natDegree_iterate_derivative p 4
      omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hdeg
    simp [← hc]
  rw [h1, h2, hconst]
  ring

end QuarteroniSaccoSaleri.Chapter09
