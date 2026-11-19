/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Lagrange
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Approximation.Quadrature

/-!
# Quarteroni, Sacco and Saleri, Section 9.1: Quadrature formulae

This module formalizes Section 9.1 of [quarteroni2000numerical], which sets up the vocabulary of
Chapter 9. A quadrature formula $I_n(f) = \int_a^b f_n(x) \, dx$ integrates an approximant $f_n$ of
$f$ (9.1), and its error $E_n(f) = I(f) - I_n(f)$ satisfies $|E_n(f)| \le \int_a^b |f - f_n| \le
(b - a) \|f - f_n\|_\infty$. With $f_n = \Pi_n f$, the interpolating polynomial at $n + 1$ distinct
nodes, one obtains the Lagrange quadrature formula $I_n(f) = \sum_i f(x_i) \int_a^b l_i(x) \, dx$
(9.2). It has the general form $I_n(f) = \sum_i \alpha_i f(x_i)$ (9.3), with nodes $x_i$ and weights
$\alpha_i$. The degree of exactness of a formula is the largest $r$ with $I_n(f) = I(f)$ for every
$f \in \mathbb{P}_r$. An interpolatory formula on $n + 1$ distinct nodes has degree of exactness at
least $n$, and conversely a formula on $n + 1$ distinct nodes that is exact on $\mathbb{P}_n$ is
interpolatory; for the converse the book cites Isaacson and Keller [isaacson1994analysis], p. 316.

The backbone module `Numlib.Approximation.Quadrature` treats quadrature rules on `C([a, b], ℝ)`. A
rule with weights `w` and nodes `x` is the functional `Quadrature.functional w x`, exactness on
$\mathbb{P}_d$ for a target functional `L` is `Quadrature.IsExactOn L w x d`, and "interpolatory" is
`Quadrature.IsInterpolatory L w x`. The two facts above are the two directions of
`Quadrature.isInterpolatory_iff_isExactOn`. The target functional here is the integral over
$[a, b]$, `ContinuousMap.integralIccCLM hab b` of `Numlib.Analysis.Calculus.ContDiffMapIcc`.

## Main definitions

* (9.2)–(9.3), `QuarteroniSaccoSaleri.Chapter09.lagrangeWeights`: the weights
  $\alpha_i = \int_a^b l_i(x) \, dx$.
* (9.2), `QuarteroniSaccoSaleri.Chapter09.lagrangeQuadrature`: the Lagrange quadrature formula
  $\sum_i \alpha_i f(x_i)$.

## Main results

* Section 9.1, `QuarteroniSaccoSaleri.Chapter09.quadratureError_le_integral_abs`:
  $|E_n(f)| \le \int_a^b |f(x) - f_n(x)| \, dx$.
* Section 9.1, `QuarteroniSaccoSaleri.Chapter09.quadratureError_le`: $|E_n(f)| \le (b - a) M$ if
  $|f - f_n| \le M$ on $[a, b]$.
* (9.1)–(9.2), `QuarteroniSaccoSaleri.Chapter09.lagrangeQuadrature_eq_integral_interpolate`: the
  Lagrange quadrature formula is the integral of the interpolating polynomial.
* Section 9.1, `QuarteroniSaccoSaleri.Chapter09.isInterpolatory_lagrangeQuadrature`: the Lagrange
  quadrature formula is interpolatory for the integral on `C([a, b], ℝ)`.
* Section 9.1, `QuarteroniSaccoSaleri.Chapter09.lagrangeQuadrature_eq_functional`: at a continuous
  function, the formula is the rule `Quadrature.functional` with the weights $\int_a^b l_i$.
* Section 9.1, `QuarteroniSaccoSaleri.Chapter09.degreeOfExactness_ge_of_interpolatory`: an
  interpolatory formula on $n + 1$ distinct nodes is exact on $\mathbb{P}_n$.
* Section 9.1, `QuarteroniSaccoSaleri.Chapter09.isInterpolatory_of_degreeOfExactness`: a formula on
  $n + 1$ distinct nodes that is exact on $\mathbb{P}_n$ has the weights $\int_a^b l_i$.

## Conventions

* The nodes are real numbers `x : Fin (n + 1) → ℝ` in $[a, b]$, the book's $x_0, \ldots, x_n$, and
  "distinct" is `Function.Injective x`.
* The characteristic Lagrange polynomial $l_i$ of Section 8.1 is `Lagrange.basis Finset.univ x i`,
  and the interpolating polynomial $\Pi_n f$ is `Lagrange.interpolate Finset.univ x (fun i => f (x
  i))`.
* The condition $f \in \mathbb{P}_r$ is `p.degree ≤ r` for a real polynomial `p`.

## Implementation notes

* The bridge to the backbone reads the nodes as points of the subtype `Icc a b`, and a real function
  on $[a, b]$ as the continuous map that it restricts to. The function `Set.IccExtend` goes the
  other way.
* The backbone lemma `Quadrature.isExactOn_integralIccCLM_iff` says that "degree of exactness at
  least $d$" for a formula $\sum_i \alpha_i f(x_i)$ on $[a, b]$, stated on real polynomials, is
  `Quadrature.IsExactOn` for the integral functional.

## Deviations from the source

* **§9.1, quadrature error** (hypotheses).
  `QuarteroniSaccoSaleri.Chapter09.quadratureError_le_integral_abs` and
  `QuarteroniSaccoSaleri.Chapter09.quadratureError_le` assume continuity of the approximant as
  well as the target function. The latter uses a pointwise bound in place of the displayed sup
  norm.
* **(9.1)–(9.3)** (generalization). `QuarteroniSaccoSaleri.Chapter09.lagrangeQuadrature` and its
  integral identity use the total algebraic Lagrange formula, which is defined for coincident
  nodes. The polynomial exactness and converse retain distinct nodes.
-/

open Set intervalIntegral
open scoped Polynomial

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {n : ℕ}

/-! ### The quadrature error of an approximant -/

/-- **Section 9.1** of [quarteroni2000numerical], the error estimate, first half. Let $a \le b$, and
let $f$ and $f_n$ be continuous on $[a, b]$. Then the error $E_n(f) = I(f) - I_n(f)$ of the
formula (9.1), $I_n(f) = \int_a^b f_n(x) \, dx$, satisfies
$$|E_n(f)| \le \int_a^b |f(x) - f_n(x)| \, dx.$$

**Reading.** Assumes the approximant is continuous as well as the integrand.
-/
theorem quadratureError_le_integral_abs (hab : a ≤ b) {f fn : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfn : ContinuousOn fn (Icc a b)) :
    |(∫ x in a..b, f x) - ∫ x in a..b, fn x| ≤ ∫ x in a..b, |f x - fn x| := by
  rw [← integral_sub (hf.intervalIntegrable_of_Icc hab) (hfn.intervalIntegrable_of_Icc hab)]
  exact abs_integral_le_integral_abs hab

/-- **Section 9.1** of [quarteroni2000numerical], the error estimate. Let $a \le b$, let $f$ and
$f_n$ be continuous on $[a, b]$, and let $|f(x) - f_n(x)| \le M$ for all $x \in [a, b]$. Then
the error of the formula (9.1) satisfies
$$|E_n(f)| \le (b - a) M.$$

The bound $M$ can be $\|f - f_n\|_\infty$. The book uses the estimate in the form: if
$\|f - f_n\|_\infty < \varepsilon$ for some $n$, then $|E_n(f)| \le \varepsilon (b - a)$.

**Reading.** Uses a pointwise bound M rather than the explicit sup norm, and assumes both functions
continuous.
-/
theorem quadratureError_le (hab : a ≤ b) {f fn : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hfn : ContinuousOn fn (Icc a b)) {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x - fn x| ≤ M) :
    |(∫ x in a..b, f x) - ∫ x in a..b, fn x| ≤ (b - a) * M := by
  rw [← integral_sub (hf.intervalIntegrable_of_Icc hab) (hfn.intervalIntegrable_of_Icc hab)]
  have h := norm_integral_le_of_norm_le_const (a := a) (b := b) (f := fun x => f x - fn x)
    (C := M) fun x hx => by
      rw [uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact hM x (Ioc_subset_Icc_self hx)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab), mul_comm] at h
  exact h

/-! ### The Lagrange quadrature formula (9.2)–(9.3) -/

/-- **Equations (9.2)–(9.3)** of [quarteroni2000numerical], the weights. Let $x_0, \ldots, x_n$ be
real nodes and $a, b \in \mathbb{R}$. The **weights of the Lagrange quadrature formula** are
$$\alpha_i = \int_a^b l_i(x) \, dx, \qquad i = 0, \ldots, n,$$
where $l_i$ is the characteristic Lagrange polynomial of the nodes (Section 8.1).

**Reading.** Uses total Lagrange basis formula for all node arrays, including collisions.
-/
noncomputable def lagrangeWeights (x : Fin (n + 1) → ℝ) (a b : ℝ) (i : Fin (n + 1)) : ℝ :=
  ∫ t in a..b, (Lagrange.basis Finset.univ x i).eval t

/-- **Equation (9.2)** of [quarteroni2000numerical], the Lagrange quadrature formula. Let
$x_0, \ldots, x_n$ be real nodes, $a, b \in \mathbb{R}$ and $f : \mathbb{R} \to \mathbb{R}$. The
**Lagrange quadrature formula** is
$$I_n(f) = \sum_{i=0}^n \alpha_i f(x_i), \qquad \alpha_i = \int_a^b l_i(x) \, dx.$$

It is an instance of the general formula (9.3), $I_n(f) = \sum_i \alpha_i f(x_i)$, with the
weights `QuarteroniSaccoSaleri.Chapter09.lagrangeWeights`.

**Reading.** Defines weighted sum for all real endpoints and nodes, without distinctness or
membership.
-/
noncomputable def lagrangeQuadrature (x : Fin (n + 1) → ℝ) (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, lagrangeWeights x a b i * f (x i)

/-- The Lagrange quadrature formula, written out as in (9.2): $I_n(f) = \sum_{i=0}^n \left( \int_a^b
l_i(t) \, dt \right) f(x_i)$. -/
theorem lagrangeQuadrature_def (x : Fin (n + 1) → ℝ) (a b : ℝ) (f : ℝ → ℝ) :
    lagrangeQuadrature x a b f
      = ∑ i, (∫ t in a..b, (Lagrange.basis Finset.univ x i).eval t) * f (x i) := rfl

/-- **Equations (9.1)–(9.2)** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be real nodes,
$a, b \in \mathbb{R}$ and $f : \mathbb{R} \to \mathbb{R}$. Then the Lagrange quadrature formula
is the formula (9.1) with $f_n = \Pi_n f$, the interpolating polynomial of $f$ at the nodes:
$$I_n(f) = \int_a^b \Pi_n f(x) \, dx.$$

The proof is the linearity of the integral applied to the Lagrange form
$\Pi_n f = \sum_i f(x_i) l_i$.

**Generalization.** The algebraic identity uses the total Lagrange formula for every array of
nodes. Polynomial interpolation of the given values and the exactness result use distinct
nodes. -/
theorem lagrangeQuadrature_eq_integral_interpolate (x : Fin (n + 1) → ℝ) (a b : ℝ) (f : ℝ → ℝ) :
    lagrangeQuadrature x a b f
      = ∫ t in a..b, (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t := by
  simp only [lagrangeQuadrature, lagrangeWeights, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  rw [integral_finsetSum fun i _ =>
    ((Polynomial.continuous _).const_mul (f (x i))).intervalIntegrable _ _]
  simp_rw [integral_const_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ### The formula in the vocabulary of the backbone -/

/-- **Section 9.1** of [quarteroni2000numerical], the Lagrange quadrature formula is interpolatory.
Let $a \le b$ and let $x_0, \ldots, x_n \in [a, b]$. Then the weights $\int_a^b l_i$, with the
nodes read as points of $[a, b]$, form an interpolatory rule for the integral over $[a, b]$ on
`C([a, b], ℝ)`: each weight is the integral of the Lagrange basis function `Lagrange.basisCM` of
the nodes.

Interpolatory is `Quadrature.IsInterpolatory`, and the integral is
`ContinuousMap.integralIccCLM hab b`.

**Reading.** Backbone property uses existence of the displayed basis weights and does not require
distinct nodes.
-/
theorem isInterpolatory_lagrangeQuadrature (hab : a ≤ b) {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) :
    Quadrature.IsInterpolatory (ContinuousMap.integralIccCLM hab b) (lagrangeWeights x a b)
      fun i => (⟨x i, hx i⟩ : Icc a b) := by
  intro i
  rw [ContinuousMap.integralIccCLM_apply, lagrangeWeights]
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  rw [ContinuousMap.coe_IccExtend, IccExtend_of_mem hab _ ht, Lagrange.basisCM_apply]

/-- **Section 9.1** of [quarteroni2000numerical], the formula as a backbone rule. Let $a \le b$, let
$x_0, \ldots, x_n \in [a, b]$, and let $f$ be a continuous function on $[a, b]$. Then the
Lagrange quadrature formula at the extension of $f$ to $\mathbb{R}$ equals the rule
`Quadrature.functional` with the weights $\int_a^b l_i$ at the nodes, applied to $f$.

The extension is `Set.IccExtend hab f`, which is constant outside $[a, b]$. -/
theorem lagrangeQuadrature_eq_functional (hab : a ≤ b) {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (f : C(Icc a b, ℝ)) :
    lagrangeQuadrature x a b (IccExtend hab f)
      = Quadrature.functional (lagrangeWeights x a b) (fun i => (⟨x i, hx i⟩ : Icc a b)) f := by
  rw [Quadrature.functional_apply, lagrangeQuadrature]
  exact Finset.sum_congr rfl fun i _ => by rw [IccExtend_of_mem hab _ (hx i)]

/-! ### The degree of exactness of interpolatory formulae -/

/-- **Section 9.1** of [quarteroni2000numerical], degree of exactness of an interpolatory formula.
Let $a \le b$, let $x_0, \ldots, x_n \in [a, b]$ be distinct, and let $p$ be a real polynomial
of degree at most $n$. Then
$$I_n(p) = \int_a^b p(t) \, dt.$$
In the words of the book: "Any interpolatory quadrature formula that makes use of $n + 1$
distinct nodes has degree of exactness equal to at least $n$."

The reason is that $\Pi_n p = p$. The proof applies the forward direction of
`Quadrature.isInterpolatory_iff_isExactOn` to
`QuarteroniSaccoSaleri.Chapter09.isInterpolatory_lagrangeQuadrature`. -/
theorem degreeOfExactness_ge_of_interpolatory (hab : a ≤ b) {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (hinj : Function.Injective x) {p : ℝ[X]} (hp : p.degree ≤ n) :
    lagrangeQuadrature x a b (fun t => p.eval t) = ∫ t in a..b, p.eval t := by
  have hinj' : Function.Injective fun i => (⟨x i, hx i⟩ : Icc a b) := fun i j h =>
    hinj (congrArg Subtype.val h)
  exact (Quadrature.isExactOn_integralIccCLM_iff hab hx _ n).1
    ((Quadrature.isInterpolatory_iff_isExactOn hinj').1
      (isInterpolatory_lagrangeQuadrature hab hx)) p hp

/-- **Section 9.1** of [quarteroni2000numerical], the converse. Let $a \le b$, let
$x_0, \ldots, x_n \in [a, b]$ be distinct, and let $\alpha_0, \ldots, \alpha_n \in \mathbb{R}$
with
$$\sum_{i=0}^n \alpha_i p(x_i) = \int_a^b p(t) \, dt$$
for every real polynomial $p$ of degree at most $n$. Then $\alpha_i = \int_a^b l_i(t) \, dt$ for
every $i$, so the formula is the Lagrange quadrature formula (9.2). In the words of the book,
which cites Isaacson and Keller [isaacson1994analysis], p. 316: "a quadrature formula using
$n + 1$ distinct nodes and having degree of exactness equal at least to $n$ is necessarily of
interpolatory type."

The proof is the reverse direction of `Quadrature.isInterpolatory_iff_isExactOn`. -/
theorem isInterpolatory_of_degreeOfExactness (hab : a ≤ b) {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (hinj : Function.Injective x) {α : Fin (n + 1) → ℝ}
    (hexact : ∀ p : ℝ[X], p.degree ≤ n → ∑ i, α i * p.eval (x i) = ∫ t in a..b, p.eval t) :
    α = lagrangeWeights x a b := by
  have hinj' : Function.Injective fun i => (⟨x i, hx i⟩ : Icc a b) := fun i j h =>
    hinj (congrArg Subtype.val h)
  funext i
  exact ((Quadrature.isInterpolatory_iff_isExactOn hinj').2
    ((Quadrature.isExactOn_integralIccCLM_iff hab hx α n).2 hexact) i).trans
    (isInterpolatory_lagrangeQuadrature hab hx i).symm

end QuarteroniSaccoSaleri.Chapter09
