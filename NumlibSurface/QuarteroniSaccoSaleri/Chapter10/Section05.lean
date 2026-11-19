/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Quadrature
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 10.5: Gaussian integration over unbounded intervals

This module formalizes Section 10.5 of [quarteroni2000numerical], on integration over the half line
and over the whole real line by interpolatory Gaussian formulae whose nodes are the zeros of the
Laguerre and Hermite polynomials. The Laguerre polynomials $\mathcal{L}_n(x) = e^x
\frac{d^n}{dx^n}(e^{-x} x^n)$ are orthogonal on $[0, \infty)$ for the weight $e^{-x}$ and satisfy
$\mathcal{L}_{n+1} = (2n + 1 - x) \mathcal{L}_n - n^2 \mathcal{L}_{n-1}$. With $f = e^{-x} \varphi$,
the Gauss–Laguerre formula (10.41), with the $n$ zeros of $\mathcal{L}_n$ as nodes and the weights
$\alpha_k = (n!)^2 x_k / \mathcal{L}_{n+1}(x_k)^2$, is exact for $\varphi \in \mathbb{P}_{2n-1}$.
The Hermite polynomials $\mathcal{H}_n(x) = (-1)^n e^{x^2} \frac{d^n}{dx^n} e^{-x^2}$ are orthogonal
on $\mathbb{R}$ for the weight $e^{-x^2}$ and satisfy $\mathcal{H}_{n+1} = 2x \mathcal{H}_n - 2n
\mathcal{H}_{n-1}$. The Gauss–Hermite formula (10.42), with the zeros of $\mathcal{H}_n$ and the
weights $\alpha_k = 2^{n+1} n! \sqrt{\pi} / \mathcal{H}_{n+1}(x_k)^2$, is exact for
$\varphi \in \mathbb{P}_{2n-1}$.

The remainder terms of (10.41) and (10.42) have the mean value forms
$\frac{(n!)^2}{(2n)!} \varphi^{(2n)}(\xi)$ and $\frac{n! \sqrt{\pi}}{2^n (2n)!}
\varphi^{(2n)}(\xi)$. The book quotes them from Davis and Rabinowitz (1975). The proofs specialize
`Numlib.Approximation.OrthogonalPolynomial.Classical` for the polynomials and their weights, the
closed forms of the weights in `Numlib.Approximation.GaussLobatto`, the Gauss rule (10.16) of
Section 10.2, and the Gauss remainder `Quadrature.exists_gauss_error_eq_of_convex` for a weight
carried by a convex set.

## Main results

* Section 10.5, `QuarteroniSaccoSaleri.Chapter10.laguerre`: Rodrigues' formula, the three-term
  recurrence and the orthogonality $\int_0^\infty \mathcal{L}_n \mathcal{L}_m e^{-x} \, dx = (n!)^2
  \delta_{nm}$ of the Laguerre polynomials.
* Equation (10.41), `QuarteroniSaccoSaleri.Chapter10.equation_10_41`: $\mathcal{L}_n$ has $n$
  distinct zeros, and with them the weights $(n!)^2 x_k / \mathcal{L}_{n+1}(x_k)^2$ are positive and
  integrate $e^{-x} \varphi$ exactly for every $\varphi \in \mathbb{P}_{2n-1}$.
* Equation (10.41), `QuarteroniSaccoSaleri.Chapter10.equation_10_41_error`: the error of the
  Gauss–Laguerre formula is $\frac{(n!)^2}{(2n)!} \varphi^{(2n)}(\xi)$ for some
  $\xi \in (0, \infty)$.
* Section 10.5, `QuarteroniSaccoSaleri.Chapter10.hermite`: Rodrigues' formula, the three-term
  recurrence and the orthogonality $\int \mathcal{H}_n \mathcal{H}_m e^{-x^2} \, dx = 2^n n!
  \sqrt{\pi} \delta_{nm}$ of the Hermite polynomials.
* Equation (10.42), `QuarteroniSaccoSaleri.Chapter10.equation_10_42`: $\mathcal{H}_n$ has $n$
  distinct zeros, and with them the weights $2^{n+1} n! \sqrt{\pi} / \mathcal{H}_{n+1}(x_k)^2$ are
  positive and integrate $e^{-x^2} \varphi$ exactly for every $\varphi \in \mathbb{P}_{2n-1}$.
* Equation (10.42), `QuarteroniSaccoSaleri.Chapter10.equation_10_42_error`: the error of the
  Gauss–Hermite formula is $\frac{n! \sqrt{\pi}}{2^n (2n)!} \varphi^{(2n)}(\xi)$ for some
  $\xi \in \mathbb{R}$.

## Conventions

* The $n$ nodes $x_1, \dots, x_n$ of the book are an injective family `x : Fin n → ℝ`.
* Exactness on $\mathbb{P}_{2n-1}$ is stated for real polynomials $\varphi$ of degree at most
  $2n - 1$, in the form of the book $\int_0^\infty e^{-x} \varphi(x) \, dx = \sum_k \alpha_k
  \varphi(x_k)$, and $\int_{-\infty}^\infty e^{-x^2} \varphi(x) \, dx = \sum_k \alpha_k
  \varphi(x_k)$ for Hermite.
* The Laguerre polynomials are `Polynomial.laguerre`. The Hermite polynomials are the physicists'
  family `Polynomial.physHermite`; Mathlib's `Polynomial.hermite` is the probabilists' family. The
  weights $e^{-x}$ on $(0, \infty)$ and $e^{-x^2}$ on $\mathbb{R}$ are
  `OrthogonalPolynomial.laguerreMeasure` and `OrthogonalPolynomial.hermiteMeasure`.

## Implementation notes

* The backbone states the formulas for the weights with $n + 1$ nodes. The proofs reach them by
  writing $n = m + 1$.
* The integrand $\varphi$ of the book is written `g` in the remainder theorems, because
  `open scoped Nat`, which gives the factorial notation `n !`, makes `φ` a token.

## Deviations from the source

* **Equations (10.41) and (10.42), optimal degree** (partial). `equation_10_41` and
  `equation_10_42` give the nodes and weights and exactness through $2n-1$. The book also
  asserts that this degree is optimal.
* **Equation (10.41), the remainder** (reading). The book assumes
  $\varphi \in C^{2n}([0, +\infty))$. The library assumes that $\varphi$ is $C^{2n}$ on all of
  $\mathbb{R}$, the form in which the backbone states the Hermite interpolation error. See
  `QuarteroniSaccoSaleri.Chapter10.equation_10_41_error`.
* **Equations (10.41) and (10.42), the remainders** (reading). The book leaves the convergence of
  the integral implicit. The library assumes that $e^{-x} \varphi$ is integrable on $(0, \infty)$,
  and that $e^{-x^2} \varphi$ is integrable on $\mathbb{R}$. See
  `QuarteroniSaccoSaleri.Chapter10.equation_10_41_error` and
  `QuarteroniSaccoSaleri.Chapter10.equation_10_42_error`.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter10

variable {n : ℕ}

/-! ### The Laguerre polynomials and the Gauss–Laguerre formula (10.41) -/

/-- **Section 10.5** of [quarteroni2000numerical], the Laguerre polynomials. For $n, m \ge 0$ and
$x \in \mathbb{R}$, the Laguerre polynomials satisfy Rodrigues' formula
$$\mathcal{L}_n(x) = e^x \frac{d^n}{dx^n} \left(e^{-x} x^n\right),$$
the three-term relation $\mathcal{L}_{n+1} = (2n + 1 - x) \mathcal{L}_n - n^2 \mathcal{L}_{n-1}$
for $n \ge 0$, with $\mathcal{L}_{-1} = 0$ and $\mathcal{L}_0 = 1$, and the orthogonality
relation for the weight $w(x) = e^{-x}$ on $[0, \infty)$:
$$\int_0^\infty \mathcal{L}_n(x) \mathcal{L}_m(x) e^{-x} \, dx = (n!)^2 \delta_{nm}.$$

The recurrence is stated as $\mathcal{L}_0 = 1$, $\mathcal{L}_1 = 1 - x$ (the step $n = 0$), and
$\mathcal{L}_{n+2} = (2(n + 1) + 1 - x) \mathcal{L}_{n+1} - (n + 1)^2 \mathcal{L}_n$. The proof
uses the backbone's `Polynomial.laguerre_eq_deriv_exp_mul`, `Polynomial.laguerre_succ_succ` and
`Polynomial.integral_laguerre_mul_laguerre`. -/
theorem laguerre (n m : ℕ) (x : ℝ) :
    (Polynomial.laguerre n).eval x = exp x * deriv^[n] (fun y => exp (-y) * y ^ n) x ∧
      Polynomial.laguerre 0 = 1 ∧ Polynomial.laguerre 1 = 1 - X ∧
      Polynomial.laguerre (n + 2) =
        (C (2 * ((n : ℝ) + 1) + 1) - X) * Polynomial.laguerre (n + 1) -
          C (((n : ℝ) + 1) ^ 2) * Polynomial.laguerre n ∧
      ∫ x in Ioi (0 : ℝ), (Polynomial.laguerre n).eval x * (Polynomial.laguerre m).eval x *
        exp (-x) = if n = m then (n ! : ℝ) ^ 2 else 0 :=
  ⟨Polynomial.laguerre_eq_deriv_exp_mul n x, Polynomial.laguerre_zero, Polynomial.laguerre_one, by
    rw [show 2 * ((n : ℝ) + 1) + 1 = 2 * n + 3 by ring]
    exact Polynomial.laguerre_succ_succ n, Polynomial.integral_laguerre_mul_laguerre n m⟩

/-- **Equation (10.41)** of [quarteroni2000numerical], the Gauss–Laguerre formula: nodes, weights
and exactness. Let $n \ge 1$. The Laguerre polynomial $\mathcal{L}_n$ has $n$ distinct zeros
$x_1, \dots, x_n$. For any $n$ distinct zeros of $\mathcal{L}_n$, the weights $\alpha_k = (n!)^2
x_k / \mathcal{L}_{n+1}(x_k)^2$ are positive, and
$$\int_0^\infty e^{-x} \varphi(x) \, dx = \sum_{k=1}^n \alpha_k \varphi(x_k) \quad \text{for
  every } \varphi \in \mathbb{P}_{2n-1}.$$
So the formula is exact for $f = \varphi e^{-x}$ with $\varphi \in \mathbb{P}_{2n-1}$: it has
degree of exactness $2n - 1$.

The zeros of $\mathcal{L}_n$ are those of the monic orthogonal polynomial of the weight $e^{-x}$
(`OrthogonalPolynomial.family_laguerreMeasure_eq`). So exactness is (10.16) with the
interpolatory weights, which `Quadrature.laguerreGaussWeight_eq` puts in closed form. The
remainder term of (10.41) is `QuarteroniSaccoSaleri.Chapter10.equation_10_41_error`.

**Partial.** The exactness conclusion covers all degrees through $2n-1$. The text also states
the optimality of that degree.

**Reading.** Same weights and exactness through 2n−1, without optimality.
-/
theorem equation_10_41 (hn : 1 ≤ n) :
    (∃ x : Fin n → ℝ, Function.Injective x ∧ ∀ k, (Polynomial.laguerre n).eval (x k) = 0) ∧
      ∀ x : Fin n → ℝ, Function.Injective x → (∀ k, (Polynomial.laguerre n).eval (x k) = 0) →
        (∀ k, 0 < (n ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 1)).eval (x k) ^ 2) ∧
        ∀ p : ℝ[X], p.degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) →
          ∫ x in Ioi (0 : ℝ), exp (-x) * p.eval x =
            ∑ k, (n ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 1)).eval (x k) ^ 2 *
              p.eval (x k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw := isWeight_laguerreMeasure
  have hfam : ∀ x : ℝ, (family laguerreMeasure (m + 1)).eval x = 0 ↔
      (Polynomial.laguerre (m + 1)).eval x = 0 := fun x => by
    rw [family_laguerreMeasure_eq, eval_mul, eval_C, mul_eq_zero, or_iff_right (by simp)]
  refine ⟨?_, fun x hx hroot => ?_⟩
  · obtain ⟨x, hx, hroot⟩ := exists_gauss_nodes hw m
    exact ⟨x, hx, fun k => (hfam _).mp (hroot k)⟩
  -- the interpolatory weights are exact and equal the closed form
  set α : Fin (m + 1) → ℝ := fun k => ∫ t, (Lagrange.basis Finset.univ x k).eval t ∂laguerreMeasure
    with hα
  have hint : IsInterpolatoryMeasure laguerreMeasure α x := fun k => rfl
  have hexact : IsExactOnMeasure laguerreMeasure α x (2 * m + 1) :=
    (equation_10_16 hw hx α).mpr ⟨fun k => (hfam _).mpr (hroot k), hint⟩
  have hform : ∀ k, α k = ((m + 1)! : ℝ) ^ 2 * x k /
      (Polynomial.laguerre (m + 1 + 1)).eval (x k) ^ 2 := fun k =>
    laguerreGaussWeight_eq hx hint hroot k
  refine ⟨fun k => hform k ▸ pos_of_isExactOnMeasure_of_le hw hx (by omega) hexact k,
    fun p hp => ?_⟩
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at hp
  rw [← integral_laguerreMeasure, ← hexact p hp]
  exact Finset.sum_congr rfl fun k _ => by rw [hform k]

/-- **Equation (10.41)** of [quarteroni2000numerical], the remainder of the Gauss–Laguerre formula.
Let $n \ge 1$, let $x_1, \dots, x_n$ be distinct zeros of $\mathcal{L}_n$, and let $\alpha_k =
(n!)^2 x_k / \mathcal{L}_{n+1}(x_k)^2$. Let $g : \mathbb{R} \to \mathbb{R}$ be $2n$ times
continuously differentiable on $\mathbb{R}$, with $e^{-x} g$ integrable on $(0, \infty)$. Then
there is $\xi \in (0, \infty)$ with
$$\int_0^\infty e^{-x} g(x) \, dx - \sum_{k=1}^n \alpha_k g(x_k) = \frac{(n!)^2}{(2n)!}
  g^{(2n)}(\xi).$$

**Reading.** The book assumes $g \in C^{2n}([0, +\infty))$. The statement here assumes that $g$
is $C^{2n}$ on all of $\mathbb{R}$, the form in which the backbone states the Hermite
interpolation error. The book leaves the convergence of the integral implicit; here it is the
hypothesis that $e^{-x} g$ is integrable.

The book quotes the remainder from Davis and Rabinowitz (1975). The proof is
`Quadrature.exists_gauss_error_eq_of_convex` for the weight
`OrthogonalPolynomial.laguerreMeasure`, carried by the convex set $(0, \infty)$. The nodes lie
in $(0, \infty)$ by `OrthogonalPolynomial.lt_root_family`, and $\int p_n^2 \, d\mu = (n!)^2$ by
`OrthogonalPolynomial.normSq_laguerreMeasure`. -/
theorem equation_10_41_error (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : Function.Injective x)
    (hroot : ∀ k, (Polynomial.laguerre n).eval (x k) = 0) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) g)
    (hint : IntegrableOn (fun t => exp (-t) * g t) (Ioi 0)) :
    ∃ ξ ∈ Ioi (0 : ℝ),
      (∫ t in Ioi (0 : ℝ), exp (-t) * g t) -
          ∑ k, (n ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 1)).eval (x k) ^ 2 * g (x k) =
        ((n ! : ℝ) ^ 2 / (2 * n)!) * iteratedDeriv (2 * n) g ξ := by
  have hw := isWeight_laguerreMeasure
  set α : Fin n → ℝ :=
    fun k => (n ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 1)).eval (x k) ^ 2
  have hfam : ∀ k, (family laguerreMeasure n).eval (x k) = 0 := fun k => by
    rw [family_laguerreMeasure_eq, eval_mul, eval_C, hroot k, mul_zero]
  have hxmem : ∀ k, x k ∈ Ioi (0 : ℝ) := fun k =>
    lt_root_family hw laguerreMeasure_ae_nonneg (hfam k)
  have hexact0 : IsExactOnMeasure laguerreMeasure α x (2 * n - 1) := by
    intro p hp
    rw [integral_laguerreMeasure]
    exact (((equation_10_41 hn).2 x hx hroot).2 p hp).symm
  have hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ k, α k * p.eval (x k) = ∫ t, p.eval t ∂laguerreMeasure := by
    have h := isExactOnMeasure_iff_forall_degree_lt.mp hexact0
    rwa [show 2 * n - 1 + 1 = 2 * n by omega] at h
  have hgint : Integrable g laguerreMeasure := (integrable_laguerreMeasure_iff g).mpr hint
  obtain ⟨ξ, hξ, heq⟩ := exists_gauss_error_eq_of_convex hw (convex_Ioi 0)
    laguerreMeasure_compl_Ioi hx hxmem hexact hg hgint
  refine ⟨ξ, hξ, ?_⟩
  rw [← integral_laguerreMeasure, heq, normSq_laguerreMeasure]
  ring

/-! ### The Hermite polynomials and the Gauss–Hermite formula (10.42) -/

/-- **Section 10.5** of [quarteroni2000numerical], the Hermite polynomials. For $n, m \ge 0$ and
$x \in \mathbb{R}$, the Hermite polynomials satisfy Rodrigues' formula
$$\mathcal{H}_n(x) = (-1)^n e^{x^2} \frac{d^n}{dx^n} e^{-x^2},$$
the recurrence $\mathcal{H}_{n+1} = 2x \mathcal{H}_n - 2n \mathcal{H}_{n-1}$ for $n \ge 0$, with
$\mathcal{H}_{-1} = 0$ and $\mathcal{H}_0 = 1$, and the orthogonality relation for the weight
$w(x) = e^{-x^2}$ on $\mathbb{R}$:
$$\int_{-\infty}^\infty \mathcal{H}_n(x) \mathcal{H}_m(x) e^{-x^2} \, dx = 2^n n! \sqrt{\pi} \,
  \delta_{nm}.$$

The recurrence is stated as $\mathcal{H}_0 = 1$, $\mathcal{H}_1 = 2x$, and $\mathcal{H}_{n+2} =
2x \mathcal{H}_{n+1} - 2(n + 1) \mathcal{H}_n$. These are the physicists' Hermite polynomials,
the backbone's `Polynomial.physHermite`; Mathlib's `Polynomial.hermite` is the probabilists'
family. The proof uses `Polynomial.physHermite_eq_deriv_gaussian`,
`Polynomial.physHermite_succ_succ` and `Polynomial.integral_physHermite_mul_physHermite`. -/
theorem hermite (n m : ℕ) (x : ℝ) :
    (Polynomial.physHermite n).eval x =
        (-1) ^ n * exp (x ^ 2) * deriv^[n] (fun y => exp (-y ^ 2)) x ∧
      Polynomial.physHermite 0 = 1 ∧ Polynomial.physHermite 1 = 2 * X ∧
      Polynomial.physHermite (n + 2) =
        2 * X * Polynomial.physHermite (n + 1) - C (2 * ((n : ℝ) + 1)) * Polynomial.physHermite n ∧
      ∫ x, (Polynomial.physHermite n).eval x * (Polynomial.physHermite m).eval x * exp (-x ^ 2) =
        if n = m then 2 ^ n * (n ! : ℝ) * √π else 0 :=
  ⟨Polynomial.physHermite_eq_deriv_gaussian n x, Polynomial.physHermite_zero,
    Polynomial.physHermite_one, Polynomial.physHermite_succ_succ n,
    Polynomial.integral_physHermite_mul_physHermite n m⟩

/-- **Equation (10.42)** of [quarteroni2000numerical], the Gauss–Hermite formula: nodes, weights and
exactness. Let $n \ge 1$. The Hermite polynomial $\mathcal{H}_n$ has $n$ distinct zeros
$x_1, \dots, x_n$. For any $n$ distinct zeros of $\mathcal{H}_n$, the weights $\alpha_k =
2^{n+1} n! \sqrt{\pi} / \mathcal{H}_{n+1}(x_k)^2$ are positive, and
$$\int_{-\infty}^{\infty} e^{-x^2} \varphi(x) \, dx = \sum_{k=1}^n \alpha_k \varphi(x_k) \quad
  \text{for every } \varphi \in \mathbb{P}_{2n-1}.$$
So the formula is exact for $f = \varphi e^{-x^2}$ with $\varphi \in \mathbb{P}_{2n-1}$: it has
degree of exactness $2n - 1$.

The proof is as for (10.41), through `OrthogonalPolynomial.family_hermiteMeasure_eq`, (10.16)
and `Quadrature.hermiteGaussWeight_eq`. The remainder term of (10.42) is
`QuarteroniSaccoSaleri.Chapter10.equation_10_42_error`.

**Partial.** The exactness conclusion covers all degrees through $2n-1$. The text also states
the optimality of that degree.

**Reading.** Same weights and exactness through 2n−1, without optimality.
-/
theorem equation_10_42 (hn : 1 ≤ n) :
    (∃ x : Fin n → ℝ, Function.Injective x ∧ ∀ k, (Polynomial.physHermite n).eval (x k) = 0) ∧
      ∀ x : Fin n → ℝ, Function.Injective x → (∀ k, (Polynomial.physHermite n).eval (x k) = 0) →
        (∀ k, 0 < 2 ^ (n + 1) * (n ! : ℝ) * √π / (Polynomial.physHermite (n + 1)).eval (x k) ^ 2) ∧
        ∀ p : ℝ[X], p.degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) →
          ∫ x, exp (-x ^ 2) * p.eval x =
            ∑ k, 2 ^ (n + 1) * (n ! : ℝ) * √π / (Polynomial.physHermite (n + 1)).eval (x k) ^ 2 *
              p.eval (x k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw := isWeight_hermiteMeasure
  have hfam : ∀ x : ℝ, (family hermiteMeasure (m + 1)).eval x = 0 ↔
      (Polynomial.physHermite (m + 1)).eval x = 0 := fun x => by
    rw [family_hermiteMeasure_eq, eval_mul, eval_C, mul_eq_zero, or_iff_right (by simp)]
  refine ⟨?_, fun x hx hroot => ?_⟩
  · obtain ⟨x, hx, hroot⟩ := exists_gauss_nodes hw m
    exact ⟨x, hx, fun k => (hfam _).mp (hroot k)⟩
  set α : Fin (m + 1) → ℝ := fun k => ∫ t, (Lagrange.basis Finset.univ x k).eval t ∂hermiteMeasure
    with hα
  have hint : IsInterpolatoryMeasure hermiteMeasure α x := fun k => rfl
  have hexact : IsExactOnMeasure hermiteMeasure α x (2 * m + 1) :=
    (equation_10_16 hw hx α).mpr ⟨fun k => (hfam _).mpr (hroot k), hint⟩
  have hform : ∀ k, α k = 2 ^ (m + 1 + 1) * ((m + 1)! : ℝ) * √π /
      (Polynomial.physHermite (m + 1 + 1)).eval (x k) ^ 2 := fun k =>
    hermiteGaussWeight_eq hx hint hroot k
  refine ⟨fun k => hform k ▸ pos_of_isExactOnMeasure_of_le hw hx (by omega) hexact k,
    fun p hp => ?_⟩
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at hp
  rw [← integral_hermiteMeasure, ← hexact p hp]
  exact Finset.sum_congr rfl fun k _ => by rw [hform k]


/-- **Equation (10.42)** of [quarteroni2000numerical], the remainder of the Gauss–Hermite formula.
Let $n \ge 1$, let $x_1, \dots, x_n$ be distinct zeros of $\mathcal{H}_n$, and let $\alpha_k =
2^{n+1} n! \sqrt{\pi} / \mathcal{H}_{n+1}(x_k)^2$. Let $g \in C^{2n}(\mathbb{R})$, with
$e^{-x^2} g$ integrable on $\mathbb{R}$. Then there is $\xi \in \mathbb{R}$ with
$$\int_{-\infty}^\infty e^{-x^2} g(x) \, dx - \sum_{k=1}^n \alpha_k g(x_k) = \frac{n!
  \sqrt{\pi}}{2^n (2n)!} g^{(2n)}(\xi).$$

**Reading.** The book leaves the convergence of the integral implicit; here it is the hypothesis
that $e^{-x^2} g$ is integrable.

The proof is `Quadrature.exists_gauss_error_eq_of_convex` for
`OrthogonalPolynomial.hermiteMeasure`, carried by the convex set $\mathbb{R}$, with
$\int p_n^2 \, d\mu = n! \sqrt{\pi} / 2^n$ (`OrthogonalPolynomial.normSq_hermiteMeasure`). -/
theorem equation_10_42_error (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : Function.Injective x)
    (hroot : ∀ k, (Polynomial.physHermite n).eval (x k) = 0) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) g)
    (hint : Integrable fun t => exp (-t ^ 2) * g t) :
    ∃ ξ : ℝ,
      (∫ t, exp (-t ^ 2) * g t) -
          ∑ k, 2 ^ (n + 1) * (n ! : ℝ) * √π / (Polynomial.physHermite (n + 1)).eval (x k) ^ 2 *
            g (x k) =
        ((n ! : ℝ) * √π / (2 ^ n * (2 * n)!)) * iteratedDeriv (2 * n) g ξ := by
  have hw := isWeight_hermiteMeasure
  set α : Fin n → ℝ :=
    fun k => 2 ^ (n + 1) * (n ! : ℝ) * √π / (Polynomial.physHermite (n + 1)).eval (x k) ^ 2
  have hexact0 : IsExactOnMeasure hermiteMeasure α x (2 * n - 1) := by
    intro p hp
    rw [integral_hermiteMeasure]
    exact (((equation_10_42 hn).2 x hx hroot).2 p hp).symm
  have hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ k, α k * p.eval (x k) = ∫ t, p.eval t ∂hermiteMeasure := by
    have h := isExactOnMeasure_iff_forall_degree_lt.mp hexact0
    rwa [show 2 * n - 1 + 1 = 2 * n by omega] at h
  have hgint : Integrable g hermiteMeasure := (integrable_hermiteMeasure_iff g).mpr hint
  obtain ⟨ξ, -, heq⟩ := exists_gauss_error_eq_of_convex hw convex_univ (by simp) hx
    (fun _ => Set.mem_univ _) hexact hg hgint
  refine ⟨ξ, ?_⟩
  rw [← integral_hermiteMeasure, heq, normSq_hermiteMeasure]
  ring

end QuarteroniSaccoSaleri.Chapter10
