/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Numlib.Approximation.OrthogonalPolynomial.Classical
import Numlib.Approximation.Quadrature
import Numlib.Approximation.TrapezoidExactness

/-!
# Gauss–Lobatto quadrature and the classical Gauss rules

Let $\mu$ be a weight on $\mathbb{R}$, let $p_k$ be its monic orthogonal polynomials and let
$\|p_k\|^2 = \int p_k^2 \, d\mu$. For a weight carried by $[-1, 1]$ and $n \ge 1$, the
**Gauss–Lobatto rule** has $n + 1$ distinct nodes $-1 = \bar x_0 < \dots < \bar x_n = 1$ and
positive weights, and it integrates every polynomial of degree at most $2n - 1$ exactly. Its
interior nodes are the roots of the orthogonal polynomial $q_{n-1}$ of degree $n - 1$ for the
modified weight $(1 - x^2)\mu$, and its nodal polynomial is the **Lobatto nodal polynomial**
$\bar\omega = (x^2 - 1) q_{n-1}$. The **Gauss–Radau rule** of a weight carried by $[a, b]$ fixes one
node at an endpoint and is exact to degree $2n$. The file also proves the closed forms of the
classical rules: the Legendre, Laguerre and Hermite Gauss weights, the Chebyshev–Gauss–Lobatto rule
at the extrema $\cos(j\pi/n)$ of $T_n$, the Legendre–Gauss–Lobatto weights
$2/(n(n+1) L_n(\bar x_j)^2)$, and the discrete Chebyshev and Legendre transforms.

The presentation follows [quarteroni2000numerical], §10.2–10.5. The computation of the weights
through the Christoffel–Darboux kernel follows Davis and Rabinowitz, *Methods of Numerical
Integration*, §2.7; see also [kress1998numerical], §9.3.

## Main definitions

* `OrthogonalPolynomial.lobattoMeasure`: the modified weight $(1 - x^2)\mu$.
* `OrthogonalPolynomial.radauMeasure`: the modified weight $(x - a)\mu$.
* `Quadrature.lobattoNodal`: the Lobatto nodal polynomial $\bar\omega = (x^2 - 1) q_{n-1}$.
* `Polynomial.Chebyshev.lobattoWeight`: the Chebyshev–Gauss–Lobatto weights $\pi/(d_j n)$, with
  $d_0 = d_n = 2$ and $d_j = 1$ otherwise.
* `Polynomial.Chebyshev.sumExtrema`: the Chebyshev–Gauss–Lobatto sum
  $\sum_{j=0}^n \frac{\pi}{d_j n} P(\cos(j\pi/n))$.

## Main results

* `Quadrature.exists_gaussLobatto`: a weight carried by $[-1, 1]$ has a Gauss–Lobatto rule with
  $n + 1$ nodes, positive weights and degree of exactness $2n - 1$.
* `Quadrature.exists_gaussRadau` and `Quadrature.exists_gaussRadau_right`: a weight carried by
  $[a, b]$ has Gauss–Radau rules with $n + 1$ nodes, the fixed node $a$ or $b$, positive weights and
  degree of exactness $2n$.
* `Quadrature.lobattoNodal_eq_add_smul` and `Quadrature.eq_lobattoNodal_of_eval_eq_zero`:
  $\bar\omega = p_{n+1} + a p_n + b p_{n-1}$ for unique reals $a$ and $b$, namely the ones for which
  the right side vanishes at $\pm 1$.
* `Quadrature.weight_eq_of_nodal_eq`: the weights of an interpolatory rule whose nodal polynomial is
  $p_{n+1} + a p_n + b p_{n-1}$ are $w_j = (\|p_n\|^2 - b \|p_{n-1}\|^2)/(p_n(x_j)\, \omega'(x_j))$.
* `Quadrature.gaussWeight_eq`: the Gauss weights are $w_j = \|p_n\|^2/(p_n(x_j)\, p_{n+1}'(x_j))$.
* `Quadrature.legendreGaussWeight_eq`, `Quadrature.laguerreGaussWeight_eq` and
  `Quadrature.hermiteGaussWeight_eq`: the closed forms of the Legendre, Laguerre and Hermite Gauss
  weights.
* `Polynomial.Chebyshev.integral_eq_sumExtrema`: the Chebyshev–Gauss–Lobatto rule with $n + 1$ nodes
  is exact on the polynomials of degree less than $2n$.
* `Quadrature.derivative_family_jacobiMeasure`: the derivative of the monic Jacobi polynomial
  $J_n^{(\alpha,\beta)}$ is $n J_{n-1}^{(\alpha+1,\beta+1)}$.
* `Quadrature.legendreLobattoWeight_eq`: the Legendre–Gauss–Lobatto weights are
  $2/(n(n+1) L_n(\bar x_j)^2)$.
* `Polynomial.Chebyshev.interpolate_eq_sum_cdt` and `Quadrature.interpolate_eq_sum_dlt`: the
  discrete Chebyshev and Legendre transforms.

## Proof outline

The modified weight $(1 - x^2)\mu$ is again a weight carried by $[-1, 1]$, so $q_{n-1}$ has $n - 1$
simple roots in $(-1, 1)$. The polynomial $\bar\omega$ is $\mu$-orthogonal to the polynomials of
degree at most $n - 2$, because $\int \bar\omega p \, d\mu = -\int q_{n-1} p \, d((1 - x^2)\mu)$.
Jacobi's theorem `Quadrature.isExactOnMeasure_add_iff` with $m = n - 1$ then gives the degree of
exactness $2n - 1$ for the interpolatory rule at the roots of $\bar\omega$. The weights are positive
by `Quadrature.pos_of_isExactOnMeasure`, with the test polynomials $(1 \mp x) q_{n-1}^2$ at the
endpoints and $(1 - x^2)(q_{n-1}/(x - \bar x_i))^2$ at the interior nodes. The Gauss–Radau rule has
the nodal polynomial $(x - a) q_n$, with $q_n$ orthogonal for $(x - a)\mu$; the rule with the fixed
node $b$ is that rule for the reflected weight.

All closed-form weights come from one identity. If the nodal polynomial of an interpolatory rule is
$\omega = p_{n+1} + a p_n + b p_{n-1}$, the Christoffel–Darboux identity
`OrthogonalPolynomial.christoffel_darboux` gives $p_n(x_j)\, \omega/(x - x_j) = \|p_n\|^2 K_n(x_j,
\cdot) - b \|p_{n-1}\|^2 K_{n-1}(x_j, \cdot)$, whose integral is $\|p_n\|^2 - b \|p_{n-1}\|^2$. With
$a = b = 0$ this gives the Gauss weights, which the Legendre, Laguerre and Hermite identities turn
into the classical formulas. With the Lobatto nodal polynomial of the Legendre weight it gives
$2/(n(n+1) L_n(\bar x_j)^2)$. The derivative of a Jacobi polynomial is a Jacobi polynomial of the
shifted weight, by one integration by parts; so the interior Lobatto nodes of a Jacobi weight are
the zeros of $(J_n^{(\alpha,\beta)})'$, and for the Legendre weight the zeros of $L_n'$. The
Chebyshev–Gauss–Lobatto rule follows from the discrete orthogonality of the cosines, and the two
discrete transforms are instances of `Quadrature.interpolate_eq_sum_discreteInner_smul`.

## Notation

* $p_k$ is `OrthogonalPolynomial.family μ k`, the monic orthogonal polynomial of degree $k$ for
  $\mu$, and $\|p_k\|^2$ is `OrthogonalPolynomial.normSq μ k`.
* $L_n$ is the Legendre polynomial `Polynomial.legendre n`.
* $\mathcal{L}_n$ is the Laguerre polynomial `Polynomial.laguerre n`.
* $H_n$ is the physicists' Hermite polynomial `Polynomial.physHermite n`.
* $T_n$ is the Chebyshev polynomial of the first kind `Polynomial.Chebyshev.T ℝ n`.
* $\operatorname{lc}(P)$ is the leading coefficient of a polynomial $P$.

## Implementation notes

* A weight is `OrthogonalPolynomial.IsWeight`: all moments are finite and the measure is not carried
  by a finite set. "Carried by $[-1, 1]$" is the hypothesis $\mu([-1, 1]^c) = 0$.
* A rule is a pair of `Fin`-indexed vectors of nodes $x$ and weights $w$.
  `Quadrature.IsExactOnMeasure μ w x d` says that the rule integrates every polynomial of degree at
  most $d$ exactly, and `Quadrature.IsInterpolatoryMeasure μ w x` says that
  $w_i = \int \ell_i \, d\mu$ for the Lagrange basis polynomials $\ell_i$ of the nodes.
* The Lobatto nodal polynomial is not built from the ansatz of the source, which chooses $a$ and $b$
  so that $p_{n+1} + a p_n + b p_{n-1}$ vanishes at $\pm 1$. It is built from the equivalent form
  $(x^2 - 1) q_{n-1}$. The equivalence is `Quadrature.lobattoNodal_eq_add_smul` together with
  `Quadrature.eq_lobattoNodal_of_eval_eq_zero`.
* Both modified weights are weights by one lemma, `OrthogonalPolynomial.isWeight_withDensity_eval`:
  a nonzero polynomial density that is nonnegative almost everywhere keeps a weight a weight.
* The Laguerre polynomials are the unnormalized $\mathcal{L}_n$ of [quarteroni2000numerical], §10.5,
  with leading coefficient $(-1)^n$. The Hermite polynomials are the physicists' $H_n$, with leading
  coefficient $2^n$.
-/

open MeasureTheory Polynomial Real Set Filter Topology

open scoped Nat

noncomputable section

namespace OrthogonalPolynomial

variable {μ : Measure ℝ}

/-! ### The modified weight $(1 - x^2)\mu$ -/

/-- The **Lobatto modified weight** of a measure $\mu$ on $\mathbb{R}$ is the measure
$(1 - x^2)_+ \, d\mu(x)$. For a weight carried by $[-1, 1]$ it is the weight $(1 - x^2)\mu$,
whose orthogonal polynomials supply the interior Gauss–Lobatto nodes of $\mu$.

The density is `ENNReal.ofReal (1 - x ^ 2)`, so it is $0$ outside $[-1, 1]$. -/
abbrev lobattoMeasure (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity fun x => ENNReal.ofReal (1 - x ^ 2)

/-- Let $\mu$ be a measure on $\mathbb{R}$ with $\mu([-1, 1]^c) = 0$, and let
$f : \mathbb{R} \to \mathbb{R}$. Then $$\int f \, d((1 - x^2)\mu) = \int (1 - x^2) f(x) \,
d\mu(x).$$
-/
theorem integral_lobattoMeasure (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (f : ℝ → ℝ) :
    ∫ x, f x ∂lobattoMeasure μ = ∫ x, (1 - x ^ 2) * f x ∂μ := by
  refine integral_withDensity_ofReal (by fun_prop) ?_ f
  have hae : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hsupp
  filter_upwards [hae] with x hx
  nlinarith [hx.1, hx.2]

/-- Let $\mu$ be a measure on $\mathbb{R}$ with $\mu([-1, 1]^c) = 0$. Then the modified weight
$(1 - x^2)\mu$ also gives no mass to the complement of $[-1, 1]$. -/
theorem lobattoMeasure_compl_Icc (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) :
    lobattoMeasure μ (Icc (-1 : ℝ) 1)ᶜ = 0 :=
  withDensity_absolutelyContinuous μ _ hsupp

/-- For all real $\alpha$ and $\beta$, the Lobatto modified weight of the Jacobi weight
$(1 - x)^\alpha (1 + x)^\beta \, dx$ on $(-1, 1)$ is the Jacobi weight
$(1 - x)^{\alpha+1} (1 + x)^{\beta+1} \, dx$. -/
theorem lobattoMeasure_jacobiMeasure (α β : ℝ) :
    lobattoMeasure (jacobiMeasure α β) = jacobiMeasure (α + 1) (β + 1) := by
  rw [lobattoMeasure, jacobiMeasure, jacobiMeasure, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  refine withDensity_congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun x hx => ?_
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h1' : 0 ≤ 1 - x := by linarith [hx.2]
  have h2' : 0 ≤ 1 + x := by linarith [hx.1]
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity), rpow_add_one h1, rpow_add_one h2]
  congr 1
  ring

/-- **A polynomial density keeps a weight a weight.** Let $\mu$ be a weight on $\mathbb{R}$ and let
$q \neq 0$ be a polynomial with $q \ge 0$ $\mu$-almost everywhere. Then the measure $q \, d\mu$
is a weight.

Its moments are moments of $\mu$ times the coefficients of $q$. If it gave no mass to the
complement of a finite set $s$, then $\mu$ would give no mass to the complement of $s$ together
with the finitely many roots of $q$. -/
theorem isWeight_withDensity_eval (hw : IsWeight μ) {q : ℝ[X]} (hq : q ≠ 0)
    (hnn : ∀ᵐ x ∂μ, 0 ≤ q.eval x) :
    IsWeight (μ.withDensity fun x => ENNReal.ofReal (q.eval x)) := by
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (q.eval x)) μ :=
    (ENNReal.measurable_ofReal.comp q.continuous.measurable).aemeasurable
  constructor
  · intro n
    rw [integrable_withDensity_ofReal_iff q.continuous.measurable hnn]
    exact (hw.integrable_eval (q * X ^ n)).congr (Eventually.of_forall fun x => by simp)
  · intro s hs h
    rw [withDensity_apply_eq_zero' hmeas] at h
    have hneg : μ {x | ¬0 ≤ q.eval x} = 0 := ae_iff.mp hnn
    refine hw.measure_compl_ne_zero ((Polynomial.finite_setOfPred_isRoot hq).union hs) ?_
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h hneg)
    simp only [mem_compl_iff, mem_union, Set.mem_ofPred_eq, not_or, IsRoot.def] at hx
    rcases lt_or_gt_of_ne hx.1 with hlt | hgt
    · exact Or.inr (not_le.mpr hlt)
    · exact Or.inl ⟨(ENNReal.ofReal_pos.mpr hgt).ne', hx.2⟩

/-- Let $\mu$ be a weight on $\mathbb{R}$ with $\mu([-1, 1]^c) = 0$. Then the measure
$(1 - x^2) \, d\mu(x)$ is a weight.

This is `OrthogonalPolynomial.isWeight_withDensity_eval` with the density $1 - x^2$, which is
nonnegative on $[-1, 1]$. -/
theorem isWeight_withDensity_one_sub_sq (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) :
    IsWeight (μ.withDensity fun x => ENNReal.ofReal (1 - x ^ 2)) := by
  have hae : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hsupp
  have hq : (1 - X ^ 2 : ℝ[X]) ≠ 0 := fun h => by
    simpa using congrArg (eval 0) h
  have h := isWeight_withDensity_eval hw hq (by
    filter_upwards [hae] with x hx
    simp only [eval_sub, eval_one, eval_pow, eval_X]
    nlinarith [hx.1, hx.2])
  simpa only [eval_sub, eval_one, eval_pow, eval_X] using h

/-- Let $\mu$ be a weight on $\mathbb{R}$ with $\mu([-1, 1]^c) = 0$. Then the Lobatto modified
weight $(1 - x^2)\mu$ is a weight. -/
theorem isWeight_lobattoMeasure (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) :
    IsWeight (lobattoMeasure μ) :=
  isWeight_withDensity_one_sub_sq hw hsupp

/-! ### The modified weight $(x - a)\mu$ -/

/-- The **Radau modified weight** of a measure $\mu$ on $\mathbb{R}$ at the point $a$ is the measure
$(x - a)_+ \, d\mu(x)$. For a weight carried by $[a, b]$ it is the weight $(x - a)\mu$ carried
by $[a, b]$ (`OrthogonalPolynomial.isWeight_radauMeasure`), whose orthogonal polynomials supply
the interior Gauss–Radau nodes of $\mu$ with the fixed node $a$.

This is the one-endpoint counterpart of `OrthogonalPolynomial.lobattoMeasure`. The density is
`ENNReal.ofReal (x - a)`, so it is $0$ to the left of $a$. -/
abbrev radauMeasure (μ : Measure ℝ) (a : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ENNReal.ofReal (x - a)

/-- Let $\mu$ be a measure on $\mathbb{R}$ with $\mu([a, b]^c) = 0$, and let
$f : \mathbb{R} \to \mathbb{R}$. Then $$\int f \, d((x - a)\mu) = \int (x - a) f(x) \,
d\mu(x).$$
-/
theorem integral_radauMeasure {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0) (f : ℝ → ℝ) :
    ∫ x, f x ∂radauMeasure μ a = ∫ x, (x - a) * f x ∂μ := by
  refine integral_withDensity_ofReal (by fun_prop) ?_ f
  have hae : ∀ᵐ x ∂μ, x ∈ Icc a b := by
    rw [ae_iff]
    exact hsupp
  filter_upwards [hae] with x hx
  linarith [hx.1]

/-- Let $\mu$ be a measure on $\mathbb{R}$ with $\mu([a, b]^c) = 0$. Then the modified weight
$(x - a)\mu$ also gives no mass to the complement of $[a, b]$. -/
theorem radauMeasure_compl_Icc {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0) :
    radauMeasure μ a (Icc a b)ᶜ = 0 :=
  withDensity_absolutelyContinuous μ _ hsupp

/-- Let $\mu$ be a weight on $\mathbb{R}$ with $\mu([a, b]^c) = 0$. Then the Radau modified weight
$(x - a)\mu$ is a weight.

This is `OrthogonalPolynomial.isWeight_withDensity_eval` with the density $x - a$, which is
nonnegative on $[a, b]$. -/
theorem isWeight_radauMeasure (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0) :
    IsWeight (radauMeasure μ a) := by
  have hae : ∀ᵐ x ∂μ, x ∈ Icc a b := by
    rw [ae_iff]
    exact hsupp
  have h := isWeight_withDensity_eval hw (X_sub_C_ne_zero a) (by
    filter_upwards [hae] with x hx
    simp only [eval_sub, eval_X, eval_C]
    linarith [hx.1])
  simpa only [eval_sub, eval_X, eval_C] using h

end OrthogonalPolynomial

namespace Quadrature

open OrthogonalPolynomial

variable {μ : Measure ℝ}

/-! ### The Lobatto nodal polynomial -/

/-- The **Lobatto nodal polynomial** of a measure $\mu$ on $\mathbb{R}$ with $n + 1$ nodes is
$$\bar\omega = (x^2 - 1)\, q_{n-1},$$ where $q_{n-1}$ is the monic orthogonal polynomial of
degree $n - 1$ for the modified weight $(1 - x^2)\mu$. For a weight carried by $[-1, 1]$ and
$n \ge 1$, it is monic of degree $n + 1$, it vanishes at $\pm 1$, and it is $\mu$-orthogonal to
the polynomials of degree at most $n - 2$. Its roots are the Gauss–Lobatto nodes of $\mu$; see
equation (10.17) of [quarteroni2000numerical].

$q_{n-1}$ is `OrthogonalPolynomial.family (OrthogonalPolynomial.lobattoMeasure μ) (n - 1)`. The
index $n - 1$ is subtraction in $\mathbb{N}$, so for $n = 0$ the polynomial is $x^2 - 1$. -/
def lobattoNodal (μ : Measure ℝ) (n : ℕ) : ℝ[X] :=
  (X ^ 2 - 1) * family (lobattoMeasure μ) (n - 1)

/-- The Lobatto nodal polynomial $\bar\omega$ is monic, for every measure $\mu$ and every $n$. -/
theorem lobattoNodal_monic (μ : Measure ℝ) (n : ℕ) : (lobattoNodal μ n).Monic := by
  have h : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (1 : ℝ) (two_ne_zero)
    rwa [C_1] at this
  exact h.mul (monic_family _ _)

/-- For every measure $\mu$ and every $n \ge 1$, the Lobatto nodal polynomial $\bar\omega$ has
degree $n + 1$. -/
theorem degree_lobattoNodal (μ : Measure ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (lobattoNodal μ n).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
  have h : (X ^ 2 - 1 : ℝ[X]).degree = 2 := by
    have := degree_X_pow_sub_C (two_pos) (1 : ℝ)
    rwa [C_1] at this
  rw [lobattoNodal, degree_mul, h, degree_family]
  norm_cast
  omega

/-- The Lobatto nodal polynomial vanishes at $1$: $\bar\omega(1) = 0$. -/
theorem lobattoNodal_eval_one (μ : Measure ℝ) (n : ℕ) : (lobattoNodal μ n).eval 1 = 0 := by
  simp [lobattoNodal]

/-- The Lobatto nodal polynomial vanishes at $-1$: $\bar\omega(-1) = 0$. -/
theorem lobattoNodal_eval_neg_one (μ : Measure ℝ) (n : ℕ) : (lobattoNodal μ n).eval (-1) = 0 := by
  simp [lobattoNodal]

/-- **The Lobatto nodal polynomial is orthogonal to the polynomials of degree at most $n - 2$.** Let
$\mu$ be a weight on $\mathbb{R}$ with $\mu([-1, 1]^c) = 0$, let $n \ge 2$, and let $p$ be a
polynomial of degree at most $n - 2$. Then $$\int \bar\omega(t)\, p(t) \, d\mu(t) = 0.$$

Against $\mu$, $\bar\omega p = -(1 - x^2) q_{n-1} p$, so the integral is $-\int q_{n-1} p$
against the modified weight, and $q_{n-1}$ is orthogonal to the polynomials of degree less than
$n - 1$. See [quarteroni2000numerical], §10.2. -/
theorem integral_lobattoNodal_mul_of_degree_le (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]} (hp : p.degree ≤ ((n - 2 : ℕ) : WithBot ℕ)) :
    ∫ t, (lobattoNodal μ n).eval t * p.eval t ∂μ = 0 := by
  have hw' := isWeight_lobattoMeasure hw hsupp
  have h := integral_family_mul_of_degree_lt hw' (n := n - 1) (q := p)
    (hp.trans_lt (by exact_mod_cast (by omega : n - 2 < n - 1)))
  rw [integral_lobattoMeasure hsupp] at h
  rw [← neg_eq_zero, ← integral_neg, ← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [lobattoNodal, eval_mul, eval_sub, eval_pow, eval_X, eval_one]
  ring

/-- **The source form of the Lobatto nodal polynomial.** Let $\mu$ be a weight on $\mathbb{R}$ with
$\mu([-1, 1]^c) = 0$, and let $n \ge 1$. Then there are real numbers $a$ and $b$ with
$$\bar\omega = p_{n+1} + a\, p_n + b\, p_{n-1}.$$ This is the form of equation (10.17) of
[quarteroni2000numerical].

The polynomial $\bar\omega - p_{n+1}$ has degree at most $n$, and its coefficients on $p_k$ for
$k \le n - 2$ vanish by `Quadrature.integral_lobattoNodal_mul_of_degree_le`. -/
theorem lobattoNodal_eq_add_smul (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ a b : ℝ, lobattoNodal μ n = family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) := by
  have hdeg : (lobattoNodal μ n - family μ (n + 1)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have := degree_sub_lt_left (p := lobattoNodal μ n) (q := family μ (n + 1))
      (by rw [degree_lobattoNodal μ hn, degree_family]) (lobattoNodal_monic μ n).ne_zero
      (by rw [(lobattoNodal_monic μ n).leadingCoeff, (monic_family μ (n + 1)).leadingCoeff])
    rwa [degree_lobattoNodal μ hn] at this
  have hexp := eq_sum_family hw hdeg
  -- the coefficients below `n - 1` vanish
  have hcoeff : ∀ k < n - 1,
      ∫ x, (lobattoNodal μ n - family μ (n + 1)).eval x * (family μ k).eval x ∂μ = 0 := by
    intro k hk
    have h1 : ∫ x, (lobattoNodal μ n).eval x * (family μ k).eval x ∂μ = 0 :=
      integral_lobattoNodal_mul_of_degree_le hw hsupp (by omega)
        (by rw [degree_family]; exact_mod_cast (by omega : k ≤ n - 2))
    have h2 : ∫ x, (family μ (n + 1)).eval x * (family μ k).eval x ∂μ = 0 :=
      integral_family_mul_family hw (by omega)
    have hev : ∀ x, (lobattoNodal μ n - family μ (n + 1)).eval x * (family μ k).eval x =
        (lobattoNodal μ n).eval x * (family μ k).eval x -
          (family μ (n + 1)).eval x * (family μ k).eval x := by
      intro x
      simp only [eval_sub]
      ring
    simp only [hev]
    rw [integral_sub (hw.integrable_eval_mul _ _) (hw.integrable_eval_mul _ _), h1, h2, sub_zero]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨(∫ x, (lobattoNodal μ (m + 1) - family μ (m + 1 + 1)).eval x *
      (family μ (m + 1)).eval x ∂μ) / normSq μ (m + 1),
    (∫ x, (lobattoNodal μ (m + 1) - family μ (m + 1 + 1)).eval x *
      (family μ m).eval x ∂μ) / normSq μ m, ?_⟩
  rw [Nat.add_sub_cancel]
  have hsplit : lobattoNodal μ (m + 1) = family μ (m + 1 + 1) +
      (lobattoNodal μ (m + 1) - family μ (m + 1 + 1)) := by ring
  conv_lhs => rw [hsplit, hexp]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero fun k hk => by
      rw [hcoeff k (by simpa using Finset.mem_range.mp hk), zero_div, zero_smul]]
  simp only [smul_eq_C_mul, zero_add]
  ring

/-- **Uniqueness of the source form of the Lobatto nodal polynomial.** Let $\mu$ be a weight on
$\mathbb{R}$ with $\mu([-1, 1]^c) = 0$, let $n \ge 1$, and let $a, b \in \mathbb{R}$. If
$p_{n+1} + a\, p_n + b\, p_{n-1}$ vanishes at $1$ and at $-1$, then $$p_{n+1} + a\, p_n + b\,
p_{n-1} = \bar\omega.$$ So the coefficients $a$ and $b$ of `Quadrature.lobattoNodal_eq_add_smul`
are unique, and they are the ones of equation (10.17) of [quarteroni2000numerical].

Such a combination is $(x^2 - 1) r$ with $r$ monic of degree $n - 1$. The polynomial $r$ is
orthogonal to the polynomials of degree less than $n - 1$ for the modified weight, because the
combination is $\mu$-orthogonal to them. So $r = q_{n-1}$. -/
theorem eq_lobattoNodal_of_eval_eq_zero (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (h1 : (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval 1 = 0)
    (h2 : (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval (-1) = 0) :
    family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) = lobattoNodal μ n := by
  have hw' := isWeight_lobattoMeasure hw hsupp
  set g := family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) with hg
  -- degree and leading coefficient of `g`
  have hlt : (C a * family μ n + C b * family μ (n - 1)).degree < (family μ (n + 1)).degree := by
    rw [degree_family]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · refine (degree_mul_le _ _).trans_lt ?_
      rw [degree_family]
      calc (C a : ℝ[X]).degree + (n : WithBot ℕ) ≤ 0 + (n : WithBot ℕ) := by
            gcongr; exact degree_C_le
        _ < ((n + 1 : ℕ) : WithBot ℕ) := by
            rw [zero_add]; exact_mod_cast Nat.lt_succ_self n
    · refine (degree_mul_le _ _).trans_lt ?_
      rw [degree_family]
      calc (C b : ℝ[X]).degree + ((n - 1 : ℕ) : WithBot ℕ) ≤ 0 + ((n - 1 : ℕ) : WithBot ℕ) := by
            gcongr; exact degree_C_le
        _ < ((n + 1 : ℕ) : WithBot ℕ) := by
            rw [zero_add]; exact_mod_cast (by omega : n - 1 < n + 1)
  have hgdeg : g.degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [hg, add_assoc, degree_add_eq_left_of_degree_lt hlt, degree_family]
  have hgmonic : g.Monic := by
    rw [Monic, hg, add_assoc, leadingCoeff_add_of_degree_lt' hlt]
    exact (monic_family μ (n + 1)).leadingCoeff
  -- `g` is orthogonal to the polynomials of degree `< n - 1`
  have hgorth : ∀ p : ℝ[X], p.degree < ((n - 1 : ℕ) : WithBot ℕ) →
      ∫ x, g.eval x * p.eval x ∂μ = 0 := by
    intro p hp
    have e1 := integral_family_mul_of_degree_lt hw (n := n + 1) (q := p)
      (hp.trans_le (by exact_mod_cast (by omega : n - 1 ≤ n + 1)))
    have e2 := integral_family_mul_of_degree_lt hw (n := n) (q := p)
      (hp.trans_le (by exact_mod_cast (by omega : n - 1 ≤ n)))
    have e3 := integral_family_mul_of_degree_lt hw (n := n - 1) (q := p) hp
    have hev : ∀ x, g.eval x * p.eval x = (family μ (n + 1)).eval x * p.eval x +
        a * ((family μ n).eval x * p.eval x) + b * ((family μ (n - 1)).eval x * p.eval x) := by
      intro x
      simp only [hg, eval_add, eval_mul, eval_C]
      ring
    simp only [hev]
    have i1 : Integrable (fun x => (family μ (n + 1)).eval x * p.eval x) μ :=
      hw.integrable_eval_mul _ _
    have i2 : Integrable (fun x => a * ((family μ n).eval x * p.eval x)) μ :=
      (hw.integrable_eval_mul _ _).const_mul _
    have i3 : Integrable (fun x => b * ((family μ (n - 1)).eval x * p.eval x)) μ :=
      (hw.integrable_eval_mul _ _).const_mul _
    have i12 : Integrable (fun x => (family μ (n + 1)).eval x * p.eval x +
        a * ((family μ n).eval x * p.eval x)) μ := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      e1, e2, e3]
    ring
  -- `g = (X² - 1) r`
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℝ[X], g = (X - C 1) * r₁ :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr h1).symm⟩
  have hr₁root : r₁.eval (-1) = 0 := by
    have h := h2
    rw [hr₁, eval_mul, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r : ℝ[X], r₁ = (X - C (-1)) * r :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hr₁root).symm⟩
  have hgr : g = (X ^ 2 - 1) * r := by
    rw [hr₁, hr, C_neg, C_1]
    ring
  have hquad : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (1 : ℝ) two_ne_zero
    rwa [C_1] at this
  have hquadnat : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
    have := natDegree_X_pow_sub_C (n := 2) (1 : ℝ)
    rwa [C_1] at this
  have hr0 : r ≠ 0 := fun h => hgmonic.ne_zero (by rw [hgr, h, mul_zero])
  have hrnat : r.natDegree = n - 1 := by
    have h := natDegree_eq_of_degree_eq_some hgdeg
    rw [hgr, natDegree_mul hquad.ne_zero hr0, hquadnat] at h
    omega
  have hrdeg : r.degree = ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hr0, hrnat]
  have hrmonic : r.Monic := by
    have h := hgmonic.leadingCoeff
    rwa [hgr, leadingCoeff_mul, hquad.leadingCoeff, one_mul] at h
  -- `r` is the `(n-1)`-st orthogonal polynomial of the modified weight
  have hr_eq : r = family (lobattoMeasure μ) (n - 1) := by
    refine sub_eq_zero.mp (eq_zero_of_degree_lt hw' (n := n - 1) ?_ ?_)
    · have := degree_sub_lt_left (p := r) (q := family (lobattoMeasure μ) (n - 1))
        (by rw [hrdeg, degree_family]) hr0
        (by rw [hrmonic.leadingCoeff, (monic_family _ _).leadingCoeff])
      rwa [hrdeg] at this
    · intro k hk
      have e1 : ∫ x, r.eval x * (family (lobattoMeasure μ) k).eval x ∂lobattoMeasure μ = 0 := by
        rw [integral_lobattoMeasure hsupp]
        have h := hgorth (family (lobattoMeasure μ) k) (by rw [degree_family]; exact_mod_cast hk)
        rw [← neg_eq_zero, ← integral_neg, ← h]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        rw [hgr]
        simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one]
        ring
      have e2 : ∫ x, (family (lobattoMeasure μ) (n - 1)).eval x *
          (family (lobattoMeasure μ) k).eval x ∂lobattoMeasure μ = 0 :=
        integral_family_mul_family hw' (by omega)
      have hev : ∀ x, (r - family (lobattoMeasure μ) (n - 1)).eval x *
          (family (lobattoMeasure μ) k).eval x =
          r.eval x * (family (lobattoMeasure μ) k).eval x -
            (family (lobattoMeasure μ) (n - 1)).eval x * (family (lobattoMeasure μ) k).eval x := by
        intro x
        simp only [eval_sub]
        ring
      simp only [hev]
      rw [integral_sub (hw'.integrable_eval_mul _ _) (hw'.integrable_eval_mul _ _), e1, e2,
        sub_zero]
  rw [hgr, hr_eq]
  rfl

/-- Let $\mu$ be a weight on $\mathbb{R}$ with $\mu([-1, 1]^c) = 0$ and let $n \ge 1$. Let a rule
have $n + 1$ distinct nodes $x_i$ and weights $w_i$, let it be interpolatory for $\mu$, and let
its nodal polynomial $\prod_i (x - x_i)$ be the Lobatto nodal polynomial $\bar\omega$. Then the
rule integrates every polynomial of degree at most $2n - 1$ exactly against $\mu$.

The proof is Jacobi's theorem `Quadrature.isExactOnMeasure_add_iff` with
`Quadrature.integral_lobattoNodal_mul_of_degree_le`. -/
theorem isExactOnMeasure_of_nodal_eq_lobattoNodal {n : ℕ} (hw : IsWeight μ)
    (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (hn : 1 ≤ n) {x α : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure μ α x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal μ n) :
    IsExactOnMeasure μ α x (2 * n - 1) := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    exact (isInterpolatoryMeasure_iff_isExactOnMeasure hw hx).mp hint
  · rw [show 2 * n - 1 = n + (n - 1) by omega, isExactOnMeasure_add_iff hw (by omega) hx α]
    refine ⟨hint, fun p hp => ?_⟩
    rw [hnodal]
    exact integral_lobattoNodal_mul_of_degree_le hw hsupp hn2
      (hp.trans (by exact_mod_cast (by omega : n - 1 - 1 ≤ n - 2)))

/-! ### Positivity of weights, and the weights through the Christoffel–Darboux kernel -/

/-- **The weights of a rule whose nodal polynomial is $p_{n+2} + a p_{n+1} + b p_n$.** Let $\mu$ be
a weight on $\mathbb{R}$, and let a rule be interpolatory for $\mu$ with $n + 2$ distinct nodes
$x_j$ and weights $w_j$. Let its nodal polynomial be $\omega = p_{n+2} + a\, p_{n+1} + b\, p_n$
for real numbers $a$ and $b$, and let $\|p_{n+1}\|^2 - b \|p_n\|^2 \neq 0$. Then for every $j$,
$p_{n+1}(x_j) \neq 0$ and $$w_j = \frac{\|p_{n+1}\|^2 - b \|p_n\|^2}{p_{n+1}(x_j)\,
\omega'(x_j)}.$$ This identity gives both the Gauss weights ($a = b = 0$) and the Gauss–Lobatto
weights.

The Christoffel–Darboux identity at $t = x_j$ gives $p_{n+1}(x_j)\, \omega/(x - x_j) =
\|p_{n+1}\|^2 K_{n+1}(x_j, \cdot) - b \|p_n\|^2 K_n(x_j, \cdot)$, whose integral is
$\|p_{n+1}\|^2 - b \|p_n\|^2$. On the other side, $\omega/(x - x_j)$ is $\omega'(x_j)$ times the
Lagrange basis polynomial of $x_j$. The computation follows Davis and Rabinowitz, *Methods of
Numerical Integration*, §2.7. -/
theorem weight_eq_of_nodal_eq (hw : IsWeight μ) {n : ℕ} {x w : Fin (n + 2) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure μ w x) {a b : ℝ}
    (hnodal : Lagrange.nodal Finset.univ x =
      family μ (n + 2) + C a * family μ (n + 1) + C b * family μ n)
    (hb : normSq μ (n + 1) - b * normSq μ n ≠ 0) (j : Fin (n + 2)) :
    (family μ (n + 1)).eval (x j) ≠ 0 ∧
      w j = (normSq μ (n + 1) - b * normSq μ n) /
        ((family μ (n + 1)).eval (x j) *
          (derivative (Lagrange.nodal Finset.univ x)).eval (x j)) := by
  set E := Lagrange.nodal (Finset.univ.erase j) x with hE
  have hωE : Lagrange.nodal Finset.univ x = (X - C (x j)) * E :=
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ j)
  have hω'ne : (derivative (Lagrange.nodal Finset.univ x)).eval (x j) ≠ 0 := by
    have h := Lagrange.nodalWeight_ne_zero hx.injOn (Finset.mem_univ j)
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ j)] at h
    intro h0
    exact h (by rw [h0, inv_zero])
  -- the root relation at `x j`
  have hroot : (family μ (n + 2)).eval (x j) + a * (family μ (n + 1)).eval (x j) +
      b * (family μ n).eval (x j) = 0 := by
    have h := Lagrange.eval_nodal_at_node (s := Finset.univ) (v := x) (Finset.mem_univ j)
    rw [hnodal] at h
    simpa [eval_add, eval_mul, eval_C] using h
  -- the key identity `p_{n+1}(x_j) E = h_{n+1} K_{n+1} - b h_n K_n`
  have hkey : C ((family μ (n + 1)).eval (x j)) * E =
      C (normSq μ (n + 1)) * cdKernel μ (n + 1) (x j) -
        C (b * normSq μ n) * cdKernel μ n (x j) := by
    refine mul_left_cancel₀ (X_sub_C_ne_zero (x j)) ?_
    have hCD1 := christoffel_darboux hw (n + 1) (x j)
    have hCD0 := christoffel_darboux hw n (x j)
    have hrootC : C ((family μ (n + 2)).eval (x j)) + C a * C ((family μ (n + 1)).eval (x j)) +
        C b * C ((family μ n).eval (x j)) = 0 := by
      rw [← C_mul, ← C_mul, ← C_add, ← C_add, hroot, C_0]
    have hω : (X - C (x j)) * E = family μ (n + 2) + C a * family μ (n + 1) + C b * family μ n :=
      hωE.symm.trans hnodal
    rw [C_mul]
    linear_combination C ((family μ (n + 1)).eval (x j)) * hω - hCD1 + C b * hCD0 +
      family μ (n + 1) * hrootC
  -- integrate the key identity
  have hintE : (family μ (n + 1)).eval (x j) * ∫ t, E.eval t ∂μ =
      normSq μ (n + 1) - b * normSq μ n := by
    have h := congrArg (fun q : ℝ[X] => ∫ t, q.eval t ∂μ) hkey
    simp only [eval_mul, eval_C, eval_sub] at h
    rw [integral_const_mul, integral_sub ((hw.integrable_eval _).const_mul _)
      ((hw.integrable_eval _).const_mul _), integral_const_mul, integral_const_mul,
      integral_eval_cdKernel hw, integral_eval_cdKernel hw, mul_one, mul_one] at h
    exact h
  have hpne : (family μ (n + 1)).eval (x j) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hintE
    exact hb hintE.symm
  refine ⟨hpne, ?_⟩
  rw [hint j, Lagrange.basis_eq_C_nodalWeight_mul_nodal_erase (Finset.mem_univ j),
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ j)]
  simp only [eval_mul, eval_C]
  rw [integral_const_mul, ← hE, ← hintE]
  field_simp

/-- **The Gauss weights through the Christoffel–Darboux kernel.** Let $\mu$ be a weight on
$\mathbb{R}$, and let a rule be interpolatory for $\mu$ with $N + 1$ distinct nodes $x_j$ and
weights $w_j$, whose nodal polynomial is $p_{N+1}$. Then for every $j$, $p_N(x_j) \neq 0$ and
$$w_j = \frac{\|p_N\|^2}{p_N(x_j)\, p_{N+1}'(x_j)}.$$

This is the case $a = b = 0$ of `Quadrature.weight_eq_of_nodal_eq`. It is the common source of
equations (10.32), (10.41) and (10.42) of [quarteroni2000numerical]; see also Davis and
Rabinowitz, *Methods of Numerical Integration*, §2.7. -/
theorem gaussWeight_eq (hw : IsWeight μ) {N : ℕ} {x w : Fin (N + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure μ w x)
    (hnodal : Lagrange.nodal Finset.univ x = family μ (N + 1)) (j : Fin (N + 1)) :
    (family μ N).eval (x j) ≠ 0 ∧
      w j = normSq μ N /
        ((family μ N).eval (x j) * (derivative (family μ (N + 1))).eval (x j)) := by
  cases N with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst hj
    have h1 : family μ (0 + 1) = X - C (alpha μ 0) := family_one μ
    refine ⟨by simp, ?_⟩
    rw [hint 0, h1, derivative_sub, derivative_X, derivative_C, sub_zero, eval_one,
      family_zero, eval_one, one_mul, div_one, normSq, family_zero]
    simp
  | succ N =>
    have h := weight_eq_of_nodal_eq hw hx hint (a := 0) (b := 0)
      (by rw [hnodal, C_0, zero_mul, zero_mul, add_zero, add_zero]) (by
        rw [zero_mul, sub_zero]; exact normSq_ne_zero hw _) j
    rw [zero_mul, sub_zero, hnodal] at h
    exact h

/-! ### The Gauss–Lobatto rule -/

/-- **Gauss–Lobatto quadrature.** Let $\mu$ be a weight on $\mathbb{R}$ with $\mu([-1, 1]^c) = 0$,
and let $n \ge 1$. Then there are $n + 1$ distinct nodes $x_0, \dots, x_n \in [-1, 1]$ with
$x_0 = -1$ and $x_n = 1$, and positive weights $w_0, \dots, w_n$, such that the rule integrates
every polynomial of degree at most $2n - 1$ exactly against $\mu$. Moreover, the nodal
polynomial of the rule is the Lobatto nodal polynomial `Quadrature.lobattoNodal μ n`, and the
rule is interpolatory. This is the rule of equations (10.17)–(10.18) of
[quarteroni2000numerical].

The interior nodes are the $n - 1$ roots of $q_{n-1}$, which lie in $(-1, 1)$. Exactness is
Jacobi's theorem `Quadrature.isExactOnMeasure_add_iff` with
`Quadrature.integral_lobattoNodal_mul_of_degree_le`. The weights are positive by
`Quadrature.pos_of_isExactOnMeasure`, with the test polynomials $(1 \mp x) q_{n-1}^2$ at the
endpoints and $(1 - x^2)(q_{n-1}/(x - \bar x_i))^2$ at the interior nodes. -/
theorem exists_gaussLobatto (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ x w : Fin (n + 1) → ℝ, Function.Injective x ∧ x 0 = -1 ∧ x (Fin.last n) = 1 ∧
      (∀ i, x i ∈ Icc (-1 : ℝ) 1) ∧ (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w x (2 * n - 1) ∧
        Lagrange.nodal Finset.univ x = lobattoNodal μ n ∧ IsInterpolatoryMeasure μ w x := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw' := isWeight_lobattoMeasure hw hsupp
  have hsupp' := lobattoMeasure_compl_Icc hsupp
  have hae : ∀ᵐ t ∂μ, t ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hsupp
  -- the interior nodes
  obtain ⟨y, hyinj, hyprod⟩ := exists_injective_family_eq_prod hw' m
  have hymem : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i =>
    root_family_mem_Ioo hw' hsupp' (by
      rw [hyprod, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
  have hq : Lagrange.nodal Finset.univ y = family (lobattoMeasure μ) m := by
    rw [Lagrange.nodal_eq, hyprod]
  -- the nodes
  set x : Fin (m + 2) → ℝ := Fin.cons (-1) (Fin.snoc y 1) with hx
  have hx0 : x 0 = -1 := Fin.cons_zero _ _
  have hxlast : x (Fin.last (m + 1)) = 1 := by
    rw [hx, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
  have hxint : ∀ i : Fin m, x (Fin.succ (Fin.castSucc i)) = y i := fun i => by
    rw [hx, Fin.cons_succ, Fin.snoc_castSucc]
  have hnodes : ∀ k : Fin (m + 2), x k = -1 ∨ x k = 1 ∨ ∃ i, x k = y i := by
    intro k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
    · exact Or.inl hx0
    · rcases Fin.eq_castSucc_or_eq_last k' with ⟨i, rfl⟩ | rfl
      · exact Or.inr (Or.inr ⟨i, hxint i⟩)
      · exact Or.inr (Or.inl (by rw [Fin.succ_last]; exact hxlast))
  have hxmem : ∀ k, x k ∈ Icc (-1 : ℝ) 1 := by
    intro k
    rcases hnodes k with h | h | ⟨i, h⟩
    · rw [h]; exact ⟨le_rfl, by norm_num⟩
    · rw [h]; exact ⟨by norm_num, le_rfl⟩
    · rw [h]; exact Ioo_subset_Icc_self (hymem i)
  have hxinj : Function.Injective x := by
    rw [hx, Fin.cons_injective_iff, Fin.snoc_injective_iff]
    refine ⟨?_, hyinj, ?_⟩
    · rintro ⟨i, hi⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc] at hi
        exact absurd hi (hymem j).1.ne'
      · rw [Fin.snoc_last] at hi
        norm_num at hi
    · rintro ⟨i, hi⟩
      exact absurd hi (hymem i).2.ne
  -- the nodal polynomial
  have hnodal : Lagrange.nodal Finset.univ x = lobattoNodal μ (m + 1) := by
    rw [Lagrange.nodal_eq, Fin.prod_univ_succ, Fin.prod_univ_castSucc, lobattoNodal,
      Nat.add_sub_cancel, hyprod]
    simp only [hx0, hxint, Fin.succ_last, hxlast, C_neg, C_1]
    ring
  -- the weights
  set w : Fin (m + 2) → ℝ := fun i => ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ with hw_def
  have hint : IsInterpolatoryMeasure μ w x := fun i => rfl
  -- exactness
  have hexact : IsExactOnMeasure μ w x (2 * (m + 1) - 1) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact (isInterpolatoryMeasure_iff_isExactOnMeasure hw hxinj).mp hint
    · rw [show 2 * (m + 1) - 1 = m + 1 + m by omega, isExactOnMeasure_add_iff hw hm hxinj]
      refine ⟨hint, fun p hp => ?_⟩
      rw [hnodal]
      exact integral_lobattoNodal_mul_of_degree_le hw hsupp (by omega)
        (hp.trans (by exact_mod_cast (by omega : m - 1 ≤ m + 1 - 2)))
  -- positivity of the weights
  have hqnat : (Lagrange.nodal Finset.univ y).natDegree = m := by
    rw [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
  have hqy : ∀ i, (Lagrange.nodal Finset.univ y).eval (y i) = 0 := fun i =>
    Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hqne : ∀ t : ℝ, (∀ i, t ≠ y i) → (Lagrange.nodal Finset.univ y).eval t ≠ 0 := by
    intro t ht
    rw [Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (ht i)
  have hdeg2 : (2 * (m + 1) - 1 : ℕ) = 2 * m + 1 := by omega
  have hpos : ∀ k, 0 < w k := by
    intro k
    rcases hnodes k with hk | hk | ⟨i, hk⟩
    · -- the node `-1`: test polynomial `(1 - X) q²`
      set p : ℝ[X] := (1 - X) * Lagrange.nodal Finset.univ y ^ 2 with hp
      have hval : 0 < p.eval (x k) := by
        rw [hp, hk]
        simp only [eval_mul, eval_sub, eval_one, eval_X, eval_pow]
        have := hqne (-1) fun i => (hymem i).1.ne
        positivity
      have hp0 : p ≠ 0 := fun h => by
        rw [h, eval_zero] at hval
        exact lt_irrefl _ hval
      refine pos_of_isExactOnMeasure hw hexact ?_ hp0 ?_ k ?_ hval
      · refine degree_le_of_natDegree_le ?_
        rw [hdeg2, hp]
        have h1 : (1 - X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
        have h2 : (Lagrange.nodal Finset.univ y ^ 2).natDegree ≤ 2 * m :=
          natDegree_pow_le.trans (by rw [hqnat])
        exact natDegree_mul_le.trans (by omega)
      · filter_upwards [hae] with t ht
        simp only [hp, eval_mul, eval_sub, eval_one, eval_X, eval_pow]
        exact mul_nonneg (by linarith [ht.2]) (sq_nonneg _)
      · intro k' hk'
        have hne : x k' ≠ x k := fun h => hk' (hxinj h)
        rcases hnodes k' with h' | h' | ⟨j, h'⟩
        · exact absurd (h'.trans hk.symm) hne
        · rw [hp, h']; simp
        · rw [hp, h']; simp [hqy j]
    · -- the node `1`: test polynomial `(1 + X) q²`
      set p : ℝ[X] := (1 + X) * Lagrange.nodal Finset.univ y ^ 2 with hp
      have hval : 0 < p.eval (x k) := by
        rw [hp, hk]
        simp only [eval_mul, eval_add, eval_one, eval_X, eval_pow]
        have := hqne 1 fun i => (hymem i).2.ne'
        positivity
      have hp0 : p ≠ 0 := fun h => by
        rw [h, eval_zero] at hval
        exact lt_irrefl _ hval
      refine pos_of_isExactOnMeasure hw hexact ?_ hp0 ?_ k ?_ hval
      · refine degree_le_of_natDegree_le ?_
        rw [hdeg2, hp]
        have h1 : (1 + X : ℝ[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
        have h2 : (Lagrange.nodal Finset.univ y ^ 2).natDegree ≤ 2 * m :=
          natDegree_pow_le.trans (by rw [hqnat])
        exact natDegree_mul_le.trans (by omega)
      · filter_upwards [hae] with t ht
        simp only [hp, eval_mul, eval_add, eval_one, eval_X, eval_pow]
        exact mul_nonneg (by linarith [ht.1]) (sq_nonneg _)
      · intro k' hk'
        have hne : x k' ≠ x k := fun h => hk' (hxinj h)
        rcases hnodes k' with h' | h' | ⟨j, h'⟩
        · rw [hp, h']; simp
        · exact absurd (h'.trans hk.symm) hne
        · rw [hp, h']; simp [hqy j]
    · -- an interior node `y i`: test polynomial `(1 - X²) (q / (X - y i))²`
      set p : ℝ[X] := (1 - X ^ 2) * Lagrange.nodal (Finset.univ.erase i) y ^ 2 with hp
      have hEnat : (Lagrange.nodal (Finset.univ.erase i) y).natDegree = m - 1 := by
        rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
      have hEval : (Lagrange.nodal (Finset.univ.erase i) y).eval (y i) ≠ 0 := by
        rw [Lagrange.eval_nodal]
        refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun h => ?_
        exact (Finset.mem_erase.mp hj).1 (hyinj h).symm
      have hval : 0 < p.eval (x k) := by
        rw [hp, hk]
        simp only [eval_mul, eval_sub, eval_one, eval_X, eval_pow]
        have h1 := (hymem i).1
        have h2 := (hymem i).2
        have hsq : 0 < 1 - y i ^ 2 := by nlinarith
        positivity
      have hp0 : p ≠ 0 := fun h => by
        rw [h, eval_zero] at hval
        exact lt_irrefl _ hval
      refine pos_of_isExactOnMeasure hw hexact ?_ hp0 ?_ k ?_ hval
      · refine degree_le_of_natDegree_le ?_
        rw [hdeg2, hp]
        refine natDegree_mul_le.trans ?_
        have h1 : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
        have h2 : (Lagrange.nodal (Finset.univ.erase i) y ^ 2).natDegree ≤ 2 * (m - 1) :=
          natDegree_pow_le.trans (by rw [hEnat])
        have hm : 1 ≤ m := Nat.succ_le_of_lt (Fin.pos i)
        omega
      · filter_upwards [hae] with t ht
        simp only [hp, eval_mul, eval_sub, eval_one, eval_X, eval_pow]
        exact mul_nonneg (by nlinarith [ht.1, ht.2]) (sq_nonneg _)
      · intro k' hk'
        have hne : x k' ≠ x k := fun h => hk' (hxinj h)
        rcases hnodes k' with h' | h' | ⟨j, h'⟩
        · rw [hp, h']; simp
        · rw [hp, h']; simp
        · have hji : j ≠ i := fun h => hne (by rw [h', hk, h])
          rw [hp, h']
          simp [Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
  exact ⟨x, w, hxinj, hx0, hxlast, hxmem, hpos, hexact, hnodal, hint⟩

/-- **Gauss–Radau quadrature.** Let $\mu$ be a weight on $\mathbb{R}$ with $\mu([a, b]^c) = 0$, and
let $n \in \mathbb{N}$. Then there are $n + 1$ distinct nodes $x_0, \dots, x_n \in [a, b]$ with
$x_0 = a$, and positive weights $w_0, \dots, w_n$, such that the rule integrates every
polynomial of degree at most $2n$ exactly against $\mu$. Moreover, the nodal polynomial of the
rule is $(x - a) q_n$, where $q_n$ is the monic orthogonal polynomial of degree $n$ for the
modified weight $(x - a)\mu$, and the rule is interpolatory. See equation (10.2.8) of
[golub2013matrix] and §10.2 of [quarteroni2000numerical].

The interior nodes are the $n$ roots of $q_n$, which lie in $(a, b)$. Exactness is Jacobi's
theorem `Quadrature.isExactOnMeasure_add_iff` with $m = n$, since $\int (x - a) q_n p \, d\mu =
\int q_n p \, d((x - a)\mu)$ vanishes for $\deg p < n$. The weights are positive by
`Quadrature.pos_of_isExactOnMeasure`, with the test polynomials $q_n^2$ at $a$ and
$(x - a)(q_n/(x - x_i))^2$ at the interior nodes. The modified weight is
`OrthogonalPolynomial.radauMeasure μ a`. The rule with the fixed node at the right end is
`Quadrature.exists_gaussRadau_right`. -/
theorem exists_gaussRadau (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0) (n : ℕ) :
    ∃ x w : Fin (n + 1) → ℝ, Function.Injective x ∧ x 0 = a ∧ (∀ i, x i ∈ Icc a b) ∧
      (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w x (2 * n) ∧
        Lagrange.nodal Finset.univ x = (X - C a) * family (radauMeasure μ a) n ∧
          IsInterpolatoryMeasure μ w x := by
  classical
  have hw' := isWeight_radauMeasure hw hsupp
  have hsupp' := radauMeasure_compl_Icc (a := a) hsupp
  have hae : ∀ᵐ t ∂μ, t ∈ Icc a b := by
    rw [ae_iff]
    exact hsupp
  have hab : a ≤ b := by
    by_contra h
    refine hw.measure_compl_ne_zero Set.finite_empty ?_
    rwa [← Icc_eq_empty h]
  -- the interior nodes
  obtain ⟨y, hyinj, hyprod⟩ := exists_injective_family_eq_prod hw' n
  have hymem : ∀ i, y i ∈ Ioo a b := fun i =>
    root_family_mem_Ioo hw' hsupp' (by
      rw [hyprod, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
  have hq : Lagrange.nodal Finset.univ y = family (radauMeasure μ a) n := by
    rw [Lagrange.nodal_eq, hyprod]
  -- the nodes
  set x : Fin (n + 1) → ℝ := Fin.cons a y with hx
  have hx0 : x 0 = a := Fin.cons_zero _ _
  have hxs : ∀ i : Fin n, x i.succ = y i := fun i => Fin.cons_succ _ _ _
  have hxmem : ∀ k, x k ∈ Icc a b := by
    intro k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · rw [hx0]; exact ⟨le_rfl, hab⟩
    · rw [hxs]; exact Ioo_subset_Icc_self (hymem i)
  have hxinj : Function.Injective x := by
    rw [hx, Fin.cons_injective_iff]
    exact ⟨fun ⟨i, hi⟩ => (hymem i).1.ne' hi, hyinj⟩
  -- the nodal polynomial
  have hnodal : Lagrange.nodal Finset.univ x = (X - C a) * family (radauMeasure μ a) n := by
    rw [Lagrange.nodal_eq, Fin.prod_univ_succ, hx0, ← hq, Lagrange.nodal_eq]
    simp only [hxs]
  -- the weights
  set w : Fin (n + 1) → ℝ := fun i => ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ with hw_def
  have hint : IsInterpolatoryMeasure μ w x := fun i => rfl
  -- exactness
  have hexact : IsExactOnMeasure μ w x (2 * n) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (isInterpolatoryMeasure_iff_isExactOnMeasure hw hxinj).mp hint
    · rw [two_mul, isExactOnMeasure_add_iff hw hn hxinj]
      refine ⟨hint, fun p hp => ?_⟩
      have h := integral_family_mul_of_degree_lt hw' (n := n) (q := p)
        (hp.trans_lt (by exact_mod_cast (by omega : n - 1 < n)))
      rw [integral_radauMeasure hsupp] at h
      rw [← h, hnodal]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      ring
  -- positivity of the weights
  have hqnat : (Lagrange.nodal Finset.univ y).natDegree = n := by
    rw [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
  have hqy : ∀ i, (Lagrange.nodal Finset.univ y).eval (y i) = 0 := fun i =>
    Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hqa : (Lagrange.nodal Finset.univ y).eval a ≠ 0 := by
    rw [Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hymem i).1.ne
  have hpos : ∀ k, 0 < w k := by
    intro k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · -- the node `a`: test polynomial `q²`
      set p : ℝ[X] := Lagrange.nodal Finset.univ y ^ 2 with hp
      have hval : 0 < p.eval (x 0) := by
        rw [hp, hx0, eval_pow]
        positivity
      have hp0 : p ≠ 0 := fun h => by
        rw [h, eval_zero] at hval
        exact lt_irrefl _ hval
      refine pos_of_isExactOnMeasure hw hexact ?_ hp0 ?_ 0 ?_ hval
      · refine degree_le_of_natDegree_le ?_
        rw [hp]
        exact natDegree_pow_le.trans (by rw [hqnat])
      · exact Eventually.of_forall fun t => by rw [hp, eval_pow]; positivity
      · intro k' hk'
        rcases Fin.eq_zero_or_eq_succ k' with rfl | ⟨j, rfl⟩
        · exact absurd rfl hk'
        · rw [hp, hxs, eval_pow, hqy, zero_pow two_ne_zero]
    · -- an interior node `y i`: test polynomial `(X - a) (q / (X - y i))²`
      set p : ℝ[X] := (X - C a) * Lagrange.nodal (Finset.univ.erase i) y ^ 2 with hp
      have hEnat : (Lagrange.nodal (Finset.univ.erase i) y).natDegree = n - 1 := by
        rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
      have hEval : (Lagrange.nodal (Finset.univ.erase i) y).eval (y i) ≠ 0 := by
        rw [Lagrange.eval_nodal]
        refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun h => ?_
        exact (Finset.mem_erase.mp hj).1 (hyinj h).symm
      have hval : 0 < p.eval (x i.succ) := by
        rw [hp, hxs]
        simp only [eval_mul, eval_sub, eval_X, eval_C, eval_pow]
        have h1 : 0 < y i - a := sub_pos.mpr (hymem i).1
        positivity
      have hp0 : p ≠ 0 := fun h => by
        rw [h, eval_zero] at hval
        exact lt_irrefl _ hval
      refine pos_of_isExactOnMeasure hw hexact ?_ hp0 ?_ i.succ ?_ hval
      · refine degree_le_of_natDegree_le ?_
        rw [hp]
        refine natDegree_mul_le.trans ?_
        have h1 : (X - C a : ℝ[X]).natDegree ≤ 1 := (natDegree_X_sub_C a).le
        have h2 : (Lagrange.nodal (Finset.univ.erase i) y ^ 2).natDegree ≤ 2 * (n - 1) :=
          natDegree_pow_le.trans (by rw [hEnat])
        have hn : 1 ≤ n := Nat.succ_le_of_lt (Fin.pos i)
        omega
      · filter_upwards [hae] with t ht
        simp only [hp, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
        exact mul_nonneg (by linarith [ht.1]) (sq_nonneg _)
      · intro k' hk'
        rcases Fin.eq_zero_or_eq_succ k' with rfl | ⟨j, rfl⟩
        · rw [hp, hx0]
          simp
        · have hji : j ≠ i := fun h => hk' (by rw [h])
          rw [hp, hxs]
          simp [Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
  exact ⟨x, w, hxinj, hx0, hxmem, hpos, hexact, hnodal, hint⟩

/-- **Gauss–Radau quadrature with the fixed node at the right end.** Let $\mu$ be a weight on
$\mathbb{R}$ with $\mu([a, b]^c) = 0$, and let $n \in \mathbb{N}$. Then there are $n + 1$
distinct nodes $x_0, \dots, x_n \in [a, b]$ with $x_0 = b$, and positive weights
$w_0, \dots, w_n$, such that the rule integrates every polynomial of degree at most $2n$ exactly
against $\mu$. See equation (10.2.9) of [golub2013matrix].

The rule is the rule of `Quadrature.exists_gaussRadau` for the reflected weight
$\mu \circ (x \mapsto -x)$, which is carried by $[-b, -a]$, transported back along
$x \mapsto -x$ by `Quadrature.isExactOnMeasure_map_affine`. -/
theorem exists_gaussRadau_right (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0) (n : ℕ) :
    ∃ x w : Fin (n + 1) → ℝ, Function.Injective x ∧ x 0 = b ∧ (∀ i, x i ∈ Icc a b) ∧
      (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w x (2 * n) := by
  have hν := hw.map_affine (c := -1) (by norm_num) 0
  have hsupp' : (μ.map fun t => -1 * t + 0) (Icc (-b) (-a))ᶜ = 0 := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    refine measure_mono_null (fun t ht => ?_) hsupp
    simp only [mem_preimage, mem_compl_iff, mem_Icc, not_and_or, not_le] at ht ⊢
    rcases ht with h | h
    · right; linarith
    · left; linarith
  obtain ⟨x, w, hx, h0, hmem, hpos, hex, -⟩ := exists_gaussRadau hν hsupp' n
  have hmap : (μ.map fun t => -1 * t + 0).map (fun t => -1 * t + 0) = μ := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    convert Measure.map_id using 2
    funext t
    simp
  have hex' := isExactOnMeasure_map_affine hex (-1) 0
  rw [hmap] at hex'
  refine ⟨(fun t => -1 * t + 0) ∘ x, w, fun i j hij => hx (by simpa using hij), by simp [h0],
    fun i => ?_, hpos, hex'⟩
  obtain ⟨h1, h2⟩ := hmem i
  simp only [Function.comp_apply]
  constructor <;> linarith

/-! ### The classical Gauss weights -/

/-- **The Legendre–Gauss weights.** Let a rule be interpolatory for the Legendre weight $dx$ on
$(-1, 1)$, with $n + 1$ distinct nodes $x_j$ that are zeros of $L_{n+1}$, and with weights
$w_j$. Then for every $j$, $$w_j = \frac{2}{(1 - x_j^2)\, L_{n+1}'(x_j)^2}.$$ This is equation
(10.32) of [quarteroni2000numerical].

`Quadrature.gaussWeight_eq` gives $w_j = 2/((n + 1) L_n(x_j) L_{n+1}'(x_j))$, and
$(1 - x_j^2) L_{n+1}'(x_j) = (n + 1) L_n(x_j)$ at a root of $L_{n+1}$ by the Legendre
differential identities. -/
theorem legendreGaussWeight_eq {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hroot : ∀ j, (Polynomial.legendre (n + 1)).eval (x j) = 0) (j : Fin (n + 1)) :
    w j = 2 / ((1 - x j ^ 2) * (derivative (Polynomial.legendre (n + 1))).eval (x j) ^ 2) := by
  have hroot' : ∀ j, (family legendreMeasure (n + 1)).eval (x j) = 0 := fun j => by
    rw [family_eq_legendre, eval_mul, hroot j, mul_zero]
  obtain ⟨hpne, hw⟩ := gaussWeight_eq isWeight_legendreMeasure hx hint
    (nodal_eq_family_of_forall_eval_eq_zero _ hx hroot') j
  have hlc1 := leadingCoeff_legendre_succ n
  have hlcn : (Polynomial.legendre n).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero n)
  rw [family_eq_legendre, eval_mul, eval_C] at hpne
  have hLn : (Polynomial.legendre n).eval (x j) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
  -- the identity `(1 - x_j²) L_{n+1}'(x_j) = (n + 1) L_n(x_j)` at a root of `L_{n+1}`
  have hid : (1 - x j ^ 2) * (derivative (Polynomial.legendre (n + 1))).eval (x j) =
      ((n : ℝ) + 1) * (Polynomial.legendre n).eval (x j) := by
    have h1 := congrArg (fun p : ℝ[X] => p.eval (x j))
      (Polynomial.quad_mul_derivative_legendre (n + 1))
    have h2 := congrArg (fun p : ℝ[X] => p.eval (x j)) (Polynomial.legendre_recurrence n)
    simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_one, eval_natCast, eval_ofNat,
      hroot j] at h1 h2
    push_cast at h1 h2
    linear_combination -h1 - h2
  have hL' : (derivative (Polynomial.legendre (n + 1))).eval (x j) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hid
    exact hLn (by
      have := hid.symm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hR : (1 - x j ^ 2) * (derivative (Polynomial.legendre (n + 1))).eval (x j) ^ 2 =
      ((n : ℝ) + 1) * (Polynomial.legendre n).eval (x j) *
        (derivative (Polynomial.legendre (n + 1))).eval (x j) := by
    rw [pow_two ((derivative (Polynomial.legendre (n + 1))).eval (x j)), ← mul_assoc, hid]
  rw [hw, normSq_legendreMeasure, family_eq_legendre, family_eq_legendre, derivative_C_mul,
    eval_mul, eval_mul, eval_C, eval_C, hlc1, hR]
  field_simp

/-- **The Gauss–Laguerre weights.** Let a rule be interpolatory for the Laguerre weight
$e^{-x} \, dx$ on $(0, \infty)$, with $n + 1$ distinct nodes $x_k$ that are zeros of
$\mathcal{L}_{n+1}$, and with weights $w_k$. Then for every $k$, $$w_k = \frac{((n + 1)!)^2\,
x_k}{\mathcal{L}_{n+2}(x_k)^2}.$$ This is equation (10.41) of [quarteroni2000numerical], with
$n + 1$ nodes in place of $n$.

`Quadrature.gaussWeight_eq` gives $w_k = -(n!)^2/(\mathcal{L}_n(x_k) \mathcal{L}_{n+1}'(x_k))$,
and at a root of $\mathcal{L}_{n+1}$ both $x_k \mathcal{L}_{n+1}'(x_k)$ and
$\mathcal{L}_{n+2}(x_k)$ equal $-(n + 1)^2 \mathcal{L}_n(x_k)$. The polynomials $\mathcal{L}_k$
are the unnormalized `Polynomial.laguerre k`, with leading coefficient $(-1)^k$. -/
theorem laguerreGaussWeight_eq {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure laguerreMeasure w x)
    (hroot : ∀ k, (Polynomial.laguerre (n + 1)).eval (x k) = 0) (k : Fin (n + 1)) :
    w k = ((n + 1) ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 2)).eval (x k) ^ 2 := by
  have hroot' : ∀ k, (family laguerreMeasure (n + 1)).eval (x k) = 0 := fun k => by
    rw [family_laguerreMeasure_eq, eval_mul, hroot k, mul_zero]
  obtain ⟨hpne, hw⟩ := gaussWeight_eq isWeight_laguerreMeasure hx hint
    (nodal_eq_family_of_forall_eval_eq_zero _ hx hroot') k
  rw [family_laguerreMeasure_eq, eval_mul, eval_C] at hpne
  have hLn : (Polynomial.laguerre n).eval (x k) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
  have hxk : x k ≠ 0 := by
    intro h
    have := hroot k
    rw [h, Polynomial.laguerre_eval_zero] at this
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _) this
  -- the two identities at a root of `ℒ_{n+1}`
  have hA : x k * (derivative (Polynomial.laguerre (n + 1))).eval (x k) =
      -(((n : ℝ) + 1) ^ 2) * (Polynomial.laguerre n).eval (x k) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (x k)) (Polynomial.X_mul_derivative_laguerre_succ n)
    simp only [eval_mul, eval_sub, eval_X, eval_C, hroot k] at h
    linear_combination h
  have hB : (Polynomial.laguerre (n + 2)).eval (x k) =
      -(((n : ℝ) + 1) ^ 2) * (Polynomial.laguerre n).eval (x k) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (x k)) (Polynomial.laguerre_succ_succ n)
    simp only [eval_mul, eval_sub, eval_X, eval_C, hroot k] at h
    linear_combination h
  have hL' : (derivative (Polynomial.laguerre (n + 1))).eval (x k) =
      -(((n : ℝ) + 1) ^ 2) * (Polynomial.laguerre n).eval (x k) / x k := by
    rw [← hA]
    field_simp
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hprod : (-1 : ℝ) ^ n * (-1) ^ (n + 1) = -1 := by
    rw [← pow_add, show n + (n + 1) = 2 * n + 1 by ring, pow_succ, pow_mul]
    simp
  rw [hw, normSq_laguerreMeasure, family_laguerreMeasure_eq, family_laguerreMeasure_eq,
    derivative_C_mul, eval_mul, eval_mul, eval_C, eval_C,
    show (-1 : ℝ) ^ n * (Polynomial.laguerre n).eval (x k) *
      ((-1) ^ (n + 1) * (derivative (Polynomial.laguerre (n + 1))).eval (x k)) =
      ((-1 : ℝ) ^ n * (-1) ^ (n + 1)) * ((Polynomial.laguerre n).eval (x k) *
        (derivative (Polynomial.laguerre (n + 1))).eval (x k)) by ring, hprod, hL', hB,
    Nat.factorial_succ]
  push_cast
  field_simp

/-- **The Gauss–Hermite weights.** Let a rule be interpolatory for the Hermite weight
$e^{-x^2} \, dx$ on $\mathbb{R}$, with $n + 1$ distinct nodes $x_k$ that are zeros of $H_{n+1}$,
and with weights $w_k$. Then for every $k$, $$w_k = \frac{2^{n+2} (n + 1)!\,
\sqrt{\pi}}{H_{n+2}(x_k)^2}.$$ This is equation (10.42) of [quarteroni2000numerical], with
$n + 1$ nodes in place of $n$.

`Quadrature.gaussWeight_eq` gives $w_k = 2^{n+1} n! \sqrt{\pi}/(H_n(x_k) H_{n+1}'(x_k))$, and
$H_{n+1}' = 2(n + 1) H_n$ and $H_{n+2}(x_k) = -2(n + 1) H_n(x_k)$ at a root of $H_{n+1}$. The
polynomials $H_k$ are the physicists' Hermite polynomials `Polynomial.physHermite k`. -/
theorem hermiteGaussWeight_eq {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure hermiteMeasure w x)
    (hroot : ∀ k, (Polynomial.physHermite (n + 1)).eval (x k) = 0) (k : Fin (n + 1)) :
    w k = 2 ^ (n + 2) * ((n + 1) ! : ℝ) * √π / (Polynomial.physHermite (n + 2)).eval (x k) ^ 2 := by
  have hroot' : ∀ k, (family hermiteMeasure (n + 1)).eval (x k) = 0 := fun k => by
    rw [family_hermiteMeasure_eq, eval_mul, hroot k, mul_zero]
  obtain ⟨hpne, hw⟩ := gaussWeight_eq isWeight_hermiteMeasure hx hint
    (nodal_eq_family_of_forall_eval_eq_zero _ hx hroot') k
  rw [family_hermiteMeasure_eq, eval_mul, eval_C] at hpne
  have hHn : (Polynomial.physHermite n).eval (x k) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
  have hB : (Polynomial.physHermite (n + 2)).eval (x k) =
      -(2 * ((n : ℝ) + 1)) * (Polynomial.physHermite n).eval (x k) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (x k)) (Polynomial.physHermite_succ_succ n)
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_ofNat, hroot k] at h
    linear_combination h
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [hw, normSq_hermiteMeasure, family_hermiteMeasure_eq, family_hermiteMeasure_eq,
    derivative_C_mul, Polynomial.derivative_physHermite_succ, eval_mul, eval_mul, eval_mul, eval_C,
    eval_C, eval_C, hB, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end Quadrature

/-! ### The Chebyshev–Gauss–Lobatto rule -/

namespace Polynomial.Chebyshev

open Quadrature

variable {n : ℕ}

/-- The factor $d_j$ of the Chebyshev–Gauss–Lobatto rule with $n + 1$ nodes: $d_j = 2$ if $j = 0$ or
$j = n$, and $d_j = 1$ otherwise. See equation (10.21) of [quarteroni2000numerical]. -/
def lobattoFactor (n j : ℕ) : ℝ := if j = 0 ∨ j = n then 2 else 1

/-- The factor $d_j$ is positive. -/
theorem lobattoFactor_pos (n j : ℕ) : 0 < lobattoFactor n j := by
  unfold lobattoFactor
  split_ifs <;> norm_num

/-- If $j \neq 0$ and $j \neq n$, then $d_j = 1$. -/
theorem lobattoFactor_of_ne {n j : ℕ} (h0 : j ≠ 0) (hn : j ≠ n) : lobattoFactor n j = 1 := by
  rw [lobattoFactor, ite_eq_right (not_or.mpr ⟨h0, hn⟩)]

/-- The **Chebyshev–Gauss–Lobatto weights** $$w_j = \frac{\pi}{d_j\, n},$$ with $d_0 = d_n = 2$ and
$d_j = 1$ at the interior nodes. See equation (10.21) of [quarteroni2000numerical].

For $n = 0$ the Lean value is $\pi/0 = 0$. -/
def lobattoWeight (n j : ℕ) : ℝ := π / (lobattoFactor n j * n)

/-- For $n \neq 0$ every Chebyshev–Gauss–Lobatto weight $\pi/(d_j n)$ is positive. -/
theorem lobattoWeight_pos {n : ℕ} (hn : n ≠ 0) (j : ℕ) : 0 < lobattoWeight n j :=
  div_pos pi_pos (mul_pos (lobattoFactor_pos n j) (by positivity))

/-- The **Chebyshev–Gauss–Lobatto sum** of a polynomial $P$: $$\sum_{j=0}^n \frac{\pi}{d_j\, n}\,
P\Big(\cos\frac{j\pi}{n}\Big),$$ over the extrema $\cos(j\pi/n)$ of $T_n$. See equation (10.21)
of [quarteroni2000numerical].

The nodes are `Polynomial.Chebyshev.node n j`. The sum is the counterpart of Mathlib's
`Polynomial.Chebyshev.sumZeroes` for the Chebyshev–Gauss rule. -/
def sumExtrema (n : ℕ) (P : ℝ[X]) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), lobattoWeight n j * P.eval (node n j)

/-- The Chebyshev–Gauss–Lobatto sum is additive: the sum of $\sum_{i \in s} P_i$ is the sum over
$i \in s$ of the sums of $P_i$. -/
theorem sumExtrema_sum (n : ℕ) {ι : Type*} (s : Finset ι) (P : ι → ℝ[X]) :
    sumExtrema n (∑ i ∈ s, P i) = ∑ i ∈ s, sumExtrema n (P i) := by
  simp only [sumExtrema, eval_finsetSum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The Chebyshev–Gauss–Lobatto sum is homogeneous: the sum of $cP$ is $c$ times the sum of $P$. -/
theorem sumExtrema_smul (n : ℕ) (c : ℝ) (P : ℝ[X]) : sumExtrema n (c • P) = c * sumExtrema n P := by
  simp only [sumExtrema, eval_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The extrema of $T_n$ are symmetric under $j \mapsto 2n - j$: for $j \le 2n$,
$\cos((2n - j)\pi/n) = \cos(j\pi/n)$. -/
theorem node_two_mul_sub {n j : ℕ} (hj : j ≤ 2 * n) : node n (2 * n - j) = node n j := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [node]
  rw [node, node, Nat.cast_sub hj]
  push_cast
  rw [show (2 * (n : ℝ) - j) * π / n = 2 * π - j * π / n by field_simp, cos_two_pi_sub]

/-- **The Chebyshev–Gauss–Lobatto sum is a trapezoidal sum over a full period.** For $n \neq 0$ and
every polynomial $P$, $$\sum_{j=0}^n \frac{\pi}{d_j\, n}\, P\Big(\cos\frac{j\pi}{n}\Big) =
\frac{\pi}{2n} \sum_{j=0}^{2n-1} P\Big(\cos\frac{j\pi}{n}\Big).$$

The half weights at the endpoints are the two halves of the periodic trapezoidal rule, and each
interior node appears twice in a period. -/
theorem sumExtrema_eq_sum_range (hn : n ≠ 0) (P : ℝ[X]) :
    sumExtrema n P = π / (2 * n) * ∑ j ∈ Finset.range (2 * n), P.eval (node n j) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  set g : ℕ → ℝ := fun j => P.eval (node n j) with hg
  -- the full period splits into `[0, n]` and `(n, 2n)`, the second half mirroring `(0, n)`
  have hsplit : ∑ j ∈ Finset.range (2 * n), g j =
      ∑ j ∈ Finset.range (n + 1), g j + ∑ j ∈ Finset.Ico 1 n, g j := by
    rw [← Finset.sum_range_add_sum_Ico g (show n + 1 ≤ 2 * n by omega)]
    congr 1
    have := Finset.sum_Ico_reflect g 1 (n := 2 * n) (m := n) (by omega)
    rw [show 2 * n + 1 - n = n + 1 by omega, show 2 * n + 1 - 1 = 2 * n by omega] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    simp only [hg, node_two_mul_sub (by omega : j ≤ 2 * n)]
  have hmid : ∑ j ∈ Finset.range (n + 1), g j = g 0 + ∑ j ∈ Finset.Ico 1 n, g j + g n := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n)]
  have hmidw : sumExtrema n P = lobattoWeight n 0 * g 0 +
      ∑ j ∈ Finset.Ico 1 n, lobattoWeight n j * g j + lobattoWeight n n * g n := by
    rw [sumExtrema, Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n)]
  have hint : ∑ j ∈ Finset.Ico 1 n, lobattoWeight n j * g j =
      π / n * ∑ j ∈ Finset.Ico 1 n, g j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [lobattoWeight, lobattoFactor_of_ne (by omega) (by omega), one_mul]
  have hw0 : lobattoWeight n 0 = π / (2 * n) := by simp [lobattoWeight, lobattoFactor]
  have hwn : lobattoWeight n n = π / (2 * n) := by simp [lobattoWeight, lobattoFactor]
  rw [hmidw, hint, hw0, hwn, hsplit, hmid]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

/-- For $n \neq 0$, the Chebyshev–Gauss–Lobatto sum of $T_0$ is $\pi$. -/
theorem sumExtrema_T_zero (hn : n ≠ 0) : sumExtrema n (T ℝ 0) = π := by
  rw [sumExtrema_eq_sum_range hn]
  simp only [T_zero, eval_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

/-- For $n \neq 0$ and $0 < k < 2n$, the Chebyshev–Gauss–Lobatto sum of $T_k$ is $0$.

Over a full period the sum is the real part of a sum of $2n$-th roots of unity, which vanishes
by `Quadrature.sum_exp_angleNode`. -/
theorem sumExtrema_T_of_pos_of_lt (hn : n ≠ 0) {k : ℕ} (hk0 : 0 < k) (hk : k < 2 * n) :
    sumExtrema n (T ℝ k) = 0 := by
  rw [sumExtrema_eq_sum_range hn]
  refine mul_eq_zero_of_right _ ?_
  have hcos : ∀ j : ℕ, (T ℝ k).eval (node n j) = Real.cos ((k : ℤ) * angleNode (2 * n) j) := by
    intro j
    rw [node, T_real_cos, angleNode]
    congr 1
    push_cast
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  simp only [hcos]
  have h := sum_exp_angleNode (N := 2 * n) (by omega) (k : ℤ)
  have hndvd : ¬ ((2 * n : ℕ) : ℤ) ∣ (k : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro hdvd
    exact absurd (Nat.le_of_dvd hk0 hdvd) (not_le.mpr hk)
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [ite_eq_right (by exact_mod_cast hndvd)] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.exp_ofReal_mul_I_re]
  push_cast
  ring_nf

/-- **Chebyshev–Gauss–Lobatto quadrature.** Let $n \neq 0$ and let $P$ be a polynomial of degree
less than $2n$. Then $$\int_{-1}^1 \frac{P(x)}{\sqrt{1 - x^2}} \, dx = \sum_{j=0}^n
\frac{\pi}{d_j\, n}\, P\Big(\cos\frac{j\pi}{n}\Big).$$ This is equation (10.21) of
[quarteroni2000numerical].

The weight is Mathlib's `Polynomial.Chebyshev.measureT`. By linearity it suffices to treat $T_k$
for $k < 2n$, where both sides are $\pi$ for $k = 0$ and $0$ otherwise. -/
theorem integral_eq_sumExtrema {n : ℕ} {P : ℝ[X]} (hn : n ≠ 0) (hP : P.degree < 2 * n) :
    ∫ x, P.eval x ∂measureT = sumExtrema n P := by
  have hmem : P ∈ degreeLT ℝ (2 * n) := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTSequence ℝ) (by simp),
    show Set.Iio (2 * n) = Finset.range (2 * n) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp_rw [eval_finsetSum, eval_smul]
  rw [MeasureTheory.integral_finsetSum, sumExtrema_sum]
  · simp_rw [sumExtrema_smul, smul_eq_mul, MeasureTheory.integral_const_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [chebyshevTSequence]
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [Nat.cast_zero, integral_eval_T_real_measureT_zero, sumExtrema_T_zero hn]
    · rw [integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast hi0),
        sumExtrema_T_of_pos_of_lt hn (Nat.pos_of_ne_zero hi0) (Finset.mem_range.mp hi)]
  · simp_rw [← eval_smul]
    exact fun i _ => integrable_measureT (by fun_prop)

/-- **Chebyshev–Gauss–Lobatto quadrature as an exactness statement.** For $n \neq 0$, the rule with
the nodes $\cos(j\pi/n)$ and the weights $\pi/(d_j n)$, $j = 0, \dots, n$, integrates every
polynomial of degree at most $2n - 1$ exactly against the Chebyshev weight
$(1 - x^2)^{-1/2} \, dx$ on $(-1, 1)$.

The statement is `Quadrature.IsExactOnMeasure` for `OrthogonalPolynomial.chebyshevMeasure`, with
nodes and weights indexed by `Fin (n + 1)`. -/
theorem isExactOnMeasure_lobattoWeight_node (hn : n ≠ 0) :
    IsExactOnMeasure OrthogonalPolynomial.chebyshevMeasure
      (fun j : Fin (n + 1) => lobattoWeight n j) (fun j : Fin (n + 1) => node n j) (2 * n - 1) := by
  intro P hP
  rw [integral_eq_sumExtrema hn (hP.trans_lt (by exact_mod_cast (by omega : 2 * n - 1 < 2 * n))),
    sumExtrema, ← Fin.sum_univ_eq_sum_range (fun j => lobattoWeight n j * P.eval (node n j))]

/-- For every $n$, the Chebyshev–Gauss–Lobatto nodes $\cos(j\pi/n)$, $j = 0, \dots, n$, are
distinct. -/
theorem injective_node (n : ℕ) : Function.Injective fun j : Fin (n + 1) => node n j := by
  intro i j hij
  have hi : (i : ℕ) ∈ (↑(Finset.range (n + 1)) : Set ℕ) := by
    simp only [Finset.coe_range, mem_Iio]
    exact i.is_lt
  have hj : (j : ℕ) ∈ (↑(Finset.range (n + 1)) : Set ℕ) := by
    simp only [Finset.coe_range, mem_Iio]
    exact j.is_lt
  exact Fin.ext ((strictAntiOn_node n).injOn hi hj hij)

/-- **The discrete norms of the Chebyshev polynomials for the Gauss–Lobatto rule.** Let $n \neq 0$,
let $\bar x_j = \cos(j\pi/n)$, and let $(f, g)_n = \sum_{j=0}^n \frac{\pi}{d_j n} f(\bar x_j)
g(\bar x_j)$. Then for $k, l \le n$, $$(T_k, T_l)_n = \begin{cases} \pi & \text{if } k = l
\text{ and } k \in \{0, n\}, \\ \pi/2 & \text{if } k = l \text{ and } 0 < k < n, \\ 0 & \text{if
} k \neq l. \end{cases}$$ This is the discrete inner product of §10.3 of
[quarteroni2000numerical].

Below the degree of exactness the discrete inner product is the continuous one. At $k = l = n$
it is the direct sum $\sum_j \pi/(d_j n) = \pi$, twice the continuous value $\pi/2$; this is the
hint of Exercise 10.2 of [quarteroni2000numerical]. The inner product is
`Quadrature.discreteInner`. -/
theorem discreteInner_T_T (hn : n ≠ 0) {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) :
    discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j : Fin (n + 1) => node n j)
        (fun t => (T ℝ k).eval t) (fun t => (T ℝ l).eval t) =
      if k = l then (if k = 0 ∨ k = n then π else π / 2) else 0 := by
  have hsum : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j)
      (fun j : Fin (n + 1) => node n j) (fun t => (T ℝ k).eval t) (fun t => (T ℝ l).eval t) =
      sumExtrema n (T ℝ k * T ℝ l) := by
    rw [discreteInner, sumExtrema,
      ← Fin.sum_univ_eq_sum_range (fun j => lobattoWeight n j * (T ℝ k * T ℝ l).eval (node n j))]
    exact Finset.sum_congr rfl fun j _ => by rw [eval_mul, mul_assoc]
  have hdeg : (T ℝ k * T ℝ l).degree = ((k + l : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_T, degree_T]
    simp
  rw [hsum]
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl]
    by_cases hkn : k = n
    · subst hkn
      rw [ite_eq_left (Or.inr rfl), sumExtrema, ← sumExtrema_T_zero hn, sumExtrema]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [eval_mul, eval_T_real_node (Finset.mem_Iic.mpr (Finset.mem_range_succ_iff.mp hj)),
        T_zero, eval_one]
      rw [← mul_pow]
      norm_num
    · rw [← integral_eq_sumExtrema hn (by rw [hdeg]; exact_mod_cast (by omega : k + k < 2 * n))]
      simp only [eval_mul]
      rcases eq_or_ne k 0 with rfl | hk0
      · rw [ite_eq_left (Or.inl rfl)]
        exact integral_eval_T_real_mul_self_measureT_zero
      · rw [ite_eq_right (not_or.mpr ⟨hk0, hkn⟩)]
        exact integral_T_real_mul_self_measureT_of_ne_zero hk0
  · rw [ite_eq_right hkl,
      ← integral_eq_sumExtrema hn (by rw [hdeg]; exact_mod_cast (by omega : k + l < 2 * n))]
    simp only [eval_mul]
    exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hkl

/-- **The discrete Chebyshev transform.** Let $n \neq 0$, let $\bar x_j = \cos(j\pi/n)$ and let
$f : \mathbb{R} \to \mathbb{R}$. Then the Lagrange interpolant of $f$ at the nodes
$\bar x_0, \dots, \bar x_n$ is $$\sum_{k=0}^n \tilde f_k T_k, \qquad \tilde f_k = \frac{2}{n\,
d_k} \sum_{j=0}^n \frac{1}{d_j} \cos\frac{kj\pi}{n}\, f(\bar x_j).$$ This is equations
(10.29)–(10.31) and Exercise 10.2 of [quarteroni2000numerical].

The proof is `Quadrature.interpolate_eq_sum_discreteInner_smul` for the Chebyshev weight, with
the discrete norms `Polynomial.Chebyshev.discreteInner_T_T` and $T_k(\bar x_j) = \cos(kj\pi/n)$. -/
theorem interpolate_eq_sum_cdt (hn : n ≠ 0) (f : ℝ → ℝ) :
    Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => node n j) (fun j => f (node n j)) =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (2 / (n * lobattoFactor n k) * ∑ j ∈ Finset.range (n + 1),
          (lobattoFactor n j)⁻¹ * Real.cos ((k : ℝ) * (j : ℝ) * π / n) * f (node n j)) * T ℝ k := by
  have hw := OrthogonalPolynomial.isWeight_chebyshevMeasure
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [interpolate_eq_sum_discreteInner_smul hw hn1 (injective_node n)
    (fun i => lobattoWeight_pos hn i) (isExactOnMeasure_lobattoWeight_node hn) f,
    ← Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (2 / (n * lobattoFactor n k) *
      ∑ j ∈ Finset.range (n + 1), (lobattoFactor n j)⁻¹ * Real.cos ((k : ℝ) * (j : ℝ) * π / n) *
        f (node n j)) * T ℝ k) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
  set c : ℝ := ((2 : ℝ) ^ ((k : ℕ) - 1))⁻¹ with hc
  rw [OrthogonalPolynomial.family_chebyshevMeasure_eq]
  have e1 : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j) f
      (fun t => (Polynomial.C c * T ℝ k).eval t) =
      c * discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j) f
        (fun t => (T ℝ k).eval t) := by
    simp only [discreteInner, eval_mul, eval_C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j)
      (fun t => (Polynomial.C c * T ℝ k).eval t) (fun t => (Polynomial.C c * T ℝ k).eval t) =
      c ^ 2 * discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j)
        (fun t => (T ℝ k).eval t) (fun t => (T ℝ k).eval t) := by
    simp only [discreteInner, eval_mul, eval_C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hv := discreteInner_T_T hn hk hk
  rw [ite_eq_left rfl] at hv
  have hvd : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j)
      (fun t => (T ℝ k).eval t) (fun t => (T ℝ k).eval t) = π * lobattoFactor n k / 2 := by
    rw [hv, lobattoFactor]
    split_ifs <;> ring
  have hf : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j) f
      (fun t => (T ℝ k).eval t) = π / n * ∑ j ∈ Finset.range (n + 1),
        (lobattoFactor n j)⁻¹ * Real.cos ((k : ℝ) * (j : ℝ) * π / n) * f (node n j) := by
    rw [discreteInner, Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range (fun j => π / n * ((lobattoFactor n j)⁻¹ *
        Real.cos ((k : ℝ) * (j : ℝ) * π / n) * f (node n j))) (n + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd := lobattoFactor_pos n j
    rw [lobattoWeight, node, T_real_cos]
    push_cast
    rw [show ((k : ℕ) : ℝ) * ((j : ℕ) * π / n) = (k : ℝ) * (j : ℝ) * π / n by ring]
    field_simp
  rw [e1, e2, hvd, hf, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  have hd := lobattoFactor_pos n k
  generalize (∑ j ∈ Finset.range (n + 1),
    (lobattoFactor n j)⁻¹ * Real.cos ((k : ℝ) * (j : ℝ) * π / n) * f (node n j)) = S
  rw [hc]
  field_simp

end Polynomial.Chebyshev

namespace Quadrature

open OrthogonalPolynomial

/-! ### The derivative of a Jacobi polynomial -/

/-- For $\alpha, \beta > -1$ and a polynomial $p$ of degree less than $n - 1$, $\int_{-1}^1
(J_n^{(\alpha,\beta)})'(x)\, p(x)\, (1 - x)^{\alpha+1} (1 + x)^{\beta+1} \, dx = 0$, by one
integration by parts; this is the step behind Remark 10.2 of [quarteroni2000numerical]. -/
private theorem integral_derivative_family_jacobiMeasure_mul {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {n : ℕ} {p : ℝ[X]} (hp : p.degree < ((n - 1 : ℕ) : WithBot ℕ)) :
    ∫ x, (derivative (family (jacobiMeasure α β) n)).eval x * p.eval x
      ∂jacobiMeasure (α + 1) (β + 1) = 0 := by
  have hw := isWeight_jacobiMeasure hα hβ
  have hα1 : 0 < α + 1 := by linarith
  have hβ1 : 0 < β + 1 := by linarith
  set J := family (jacobiMeasure α β) n with hJ
  set r : ℝ[X] := (1 - X ^ 2) * derivative p +
    p * (C (β + 1) * (1 - X) - C (α + 1) * (1 + X)) with hr
  -- the degree of the bracket polynomial
  have hrdeg : r.degree < n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- `n ≤ 1`: `p = 0`
      have hp0 : p = 0 := by
        have : p.degree < 0 := by
          refine hp.trans_le ?_
          have : n - 1 = 0 := by omega
          rw [this]
          exact le_rfl
        exact degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp this)
      rw [hr, hp0]
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hpnat : p.natDegree ≤ m := by
        rcases eq_or_ne p 0 with rfl | hp0
        · simp
        · have := (natDegree_lt_iff_degree_lt hp0).mpr hp
          omega
      refine lt_of_le_of_lt (degree_le_natDegree) ?_
      have h1 : ((1 - X ^ 2) * derivative p).natDegree ≤ m + 1 := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · have : derivative p = 0 := by
            rw [derivative_eq_zero]
            omega
          rw [this, mul_zero, natDegree_zero]
          exact Nat.zero_le _
        · refine natDegree_mul_le.trans ?_
          have ha : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
          have hb : (derivative p).natDegree ≤ m - 1 :=
            (natDegree_derivative_le p).trans (by omega)
          omega
      have h2 : (p * (C (β + 1) * (1 - X) - C (α + 1) * (1 + X))).natDegree ≤ m + 1 := by
        refine natDegree_mul_le.trans ?_
        have hb : (C (β + 1) * (1 - X) - C (α + 1) * (1 + X) : ℝ[X]).natDegree ≤ 1 := by
          refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
          · exact (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (by simp))
          · exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
        omega
      have := (natDegree_add_le _ _).trans (max_le h1 h2)
      exact_mod_cast Nat.lt_of_le_of_lt this (by omega)
  -- the function whose derivative is integrated
  set F : ℝ → ℝ := fun x => J.eval x * p.eval x * ((1 - x) ^ (α + 1) * (1 + x) ^ (β + 1)) with hF
  set F' : ℝ → ℝ := fun x => (1 - x) ^ α * (1 + x) ^ β *
    ((derivative J).eval x * p.eval x * (1 - x ^ 2) + J.eval x * r.eval x) with hF'
  have hderiv : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (F' x) x := by
    intro x hx
    have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
    have h1x' : 1 + x ≠ 0 := by linarith [hx.1]
    have hd0 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
    have hd0' : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hd1 : HasDerivAt (fun y : ℝ => (1 - y) ^ (α + 1))
        (-1 * (α + 1) * (1 - x) ^ (α + 1 - 1)) x := hd0.rpow_const (Or.inl h1x)
    have hd2 : HasDerivAt (fun y : ℝ => (1 + y) ^ (β + 1))
        (1 * (β + 1) * (1 + x) ^ (β + 1 - 1)) x := hd0'.rpow_const (Or.inl h1x')
    have := ((J.hasDerivAt x).mul (p.hasDerivAt x)).mul (hd1.mul hd2)
    refine this.congr_deriv ?_
    simp only [hF', hr, Pi.mul_apply, add_sub_cancel_right, eval_add, eval_mul, eval_sub, eval_one,
      eval_pow, eval_X, eval_C]
    rw [rpow_add_one h1x, rpow_add_one h1x']
    ring
  have hcont : Continuous F := by
    simp only [hF]
    refine (J.continuous.mul p.continuous).mul (Continuous.mul ?_ ?_)
    · exact (continuous_rpow_const hα1.le).comp (continuous_const.sub continuous_id)
    · exact (continuous_rpow_const hβ1.le).comp (continuous_const.add continuous_id)
  have hF1 : F 1 = 0 := by
    rw [hF]
    simp [zero_rpow hα1.ne']
  have hFm1 : F (-1) = 0 := by
    rw [hF]
    simp [zero_rpow hβ1.ne']
  have hint1 : IntegrableOn (fun x => (1 - x) ^ α * (1 + x) ^ β *
      ((derivative J).eval x * p.eval x * (1 - x ^ 2))) (Ioo (-1 : ℝ) 1) :=
    integrableOn_jacobiDensity_mul hα hβ (by fun_prop)
  have hint2 : IntegrableOn (fun x => (1 - x) ^ α * (1 + x) ^ β * (J.eval x * r.eval x))
      (Ioo (-1 : ℝ) 1) :=
    integrableOn_jacobiDensity_mul hα hβ (by fun_prop)
  have hint' : IntervalIntegrable F' volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    exact integrableOn_jacobiDensity_mul hα hβ (by fun_prop)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (-1 : ℝ) < 1) hderiv hint'
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [hF1, hFm1, sub_zero, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo] at hFTC
  have hsplit : ∫ x in Ioo (-1 : ℝ) 1, F' x =
      (∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β *
        ((derivative J).eval x * p.eval x * (1 - x ^ 2))) +
      ∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β * (J.eval x * r.eval x) := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF']
    ring
  have hJr : ∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β * (J.eval x * r.eval x) = 0 := by
    rw [← integral_jacobiMeasure]
    exact integral_family_mul_of_degree_lt hw hrdeg
  rw [hsplit, hJr, add_zero] at hFTC
  rw [integral_jacobiMeasure, ← hFTC]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
  have h1x' : 1 + x ≠ 0 := by linarith [hx.1]
  rw [rpow_add_one h1x, rpow_add_one h1x']
  ring

/-- **The derivative of a Jacobi polynomial is a Jacobi polynomial of the shifted weight.** Let
$\alpha, \beta > -1$ and $n \ge 1$, and let $J_k^{(\alpha,\beta)}$ be the monic orthogonal
polynomial of degree $k$ for the Jacobi weight $(1 - x)^\alpha (1 + x)^\beta \, dx$ on
$(-1, 1)$. Then $$\big(J_n^{(\alpha,\beta)}\big)' = n\, J_{n-1}^{(\alpha+1,\beta+1)}.$$ Since
the Lobatto modified weight of the Jacobi weight with exponents $(\alpha, \beta)$ is the Jacobi
weight with exponents $(\alpha + 1, \beta + 1)$, the interior Gauss–Lobatto nodes of a Jacobi
weight are the zeros of $(J_n^{(\alpha,\beta)})'$. This is Remark 10.2 of
[quarteroni2000numerical], with the weight read as $(1 - x)^\alpha (1 + x)^\beta$.

Both sides are $n$ times a monic polynomial of degree $n - 1$. The left side is orthogonal to
the polynomials of degree less than $n - 1$ for the shifted weight, by one integration by parts
in which the boundary terms vanish because $\alpha + 1, \beta + 1 > 0$. The polynomial
$J_k^{(\alpha,\beta)}$ is `OrthogonalPolynomial.family (OrthogonalPolynomial.jacobiMeasure α β)
k`. -/
theorem derivative_family_jacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (hn : 1 ≤ n) :
    derivative (family (jacobiMeasure α β) n) =
      C (n : ℝ) * family (jacobiMeasure (α + 1) (β + 1)) (n - 1) := by
  have hw' := isWeight_jacobiMeasure (by linarith : -1 < α + 1) (by linarith : -1 < β + 1)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set J' := derivative (family (jacobiMeasure α β) n) with hJ'
  have hnat : (family (jacobiMeasure α β) n).natDegree = n :=
    natDegree_eq_of_degree_eq_some (degree_family _ _)
  have hJ'deg : J'.degree = ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [hJ', degree_derivative (by rw [hnat]; omega), hnat]
  have hJ'lc : J'.leadingCoeff = n := by
    rw [hJ', leadingCoeff_derivative, (monic_family _ _).leadingCoeff, hnat, one_mul]
  have hJ'ne : J' ≠ 0 := fun h => by
    rw [h, leadingCoeff_zero] at hJ'lc
    exact hnR hJ'lc.symm
  set r : ℝ[X] := C (n : ℝ)⁻¹ * J' with hr
  have hrdeg : r.degree = ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [hr, degree_C_mul (inv_ne_zero hnR), hJ'deg]
  have hrmonic : r.Monic := by
    rw [Monic, hr, leadingCoeff_mul, leadingCoeff_C, hJ'lc, inv_mul_cancel₀ hnR]
  have hr_eq : r = family (jacobiMeasure (α + 1) (β + 1)) (n - 1) := by
    refine sub_eq_zero.mp (eq_zero_of_degree_lt hw' (n := n - 1) ?_ ?_)
    · have := degree_sub_lt_left (p := r) (q := family (jacobiMeasure (α + 1) (β + 1)) (n - 1))
        (by rw [hrdeg, degree_family]) hrmonic.ne_zero
        (by rw [hrmonic.leadingCoeff, (monic_family _ _).leadingCoeff])
      rwa [hrdeg] at this
    · intro k hk
      have e1 : ∫ x, r.eval x * (family (jacobiMeasure (α + 1) (β + 1)) k).eval x
          ∂jacobiMeasure (α + 1) (β + 1) = 0 := by
        have h := integral_derivative_family_jacobiMeasure_mul hα hβ (n := n)
          (p := family (jacobiMeasure (α + 1) (β + 1)) k) (by rw [degree_family]; exact_mod_cast hk)
        rw [← hJ'] at h
        simp only [hr, eval_mul, eval_C, mul_assoc]
        rw [integral_const_mul, h, mul_zero]
      have e2 : ∫ x, (family (jacobiMeasure (α + 1) (β + 1)) (n - 1)).eval x *
          (family (jacobiMeasure (α + 1) (β + 1)) k).eval x ∂jacobiMeasure (α + 1) (β + 1) = 0 :=
        integral_family_mul_family hw' (by omega)
      have hev : ∀ x, (r - family (jacobiMeasure (α + 1) (β + 1)) (n - 1)).eval x *
          (family (jacobiMeasure (α + 1) (β + 1)) k).eval x =
          r.eval x * (family (jacobiMeasure (α + 1) (β + 1)) k).eval x -
            (family (jacobiMeasure (α + 1) (β + 1)) (n - 1)).eval x *
              (family (jacobiMeasure (α + 1) (β + 1)) k).eval x := by
        intro x
        simp only [eval_sub]
        ring
      simp only [hev]
      rw [integral_sub (hw'.integrable_eval_mul _ _) (hw'.integrable_eval_mul _ _), e1, e2,
        sub_zero]
  rw [← hr_eq, hr, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hnR, C_1, one_mul]

/-- The Jacobi weight $(1 - x)(1 + x) \, dx$ on $(-1, 1)$, with $\alpha = \beta = 1$, is the Lobatto
modified weight $(1 - x^2) \, dx$ of the Legendre weight. -/
theorem _root_.OrthogonalPolynomial.jacobiMeasure_one_one :
    jacobiMeasure 1 1 = lobattoMeasure legendreMeasure := by
  rw [jacobiMeasure]
  refine withDensity_congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun x _ => ?_
  simp only [rpow_one]
  congr 1
  ring

/-- **The interior Legendre–Gauss–Lobatto nodes are the zeros of $L_n'$.** For $n \ge 1$, $$L_n' = n
\operatorname{lc}(L_n)\, q_{n-1},$$ where $q_{n-1}$ is the monic orthogonal polynomial of degree
$n - 1$ for the modified weight $(1 - x^2) \, dx$ on $(-1, 1)$. So the Lobatto nodal polynomial
of the Legendre weight is a multiple of $(1 - x^2) L_n'$. See equation (10.33) of
[quarteroni2000numerical].

This is the Legendre case $\alpha = \beta = 0$ of `Quadrature.derivative_family_jacobiMeasure`. -/
theorem derivative_legendre_eq_family {n : ℕ} (hn : 1 ≤ n) :
    derivative (Polynomial.legendre n) =
      C ((n : ℝ) * (Polynomial.legendre n).leadingCoeff) * family (lobattoMeasure legendreMeasure)
        (n - 1) := by
  have h := derivative_family_jacobiMeasure (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0) hn
  rw [jacobiMeasure_zero_zero, zero_add, jacobiMeasure_one_one, family_eq_legendre,
    derivative_C_mul] at h
  have hlc : (Polynomial.legendre n).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero n)
  calc derivative (Polynomial.legendre n)
      = C (Polynomial.legendre n).leadingCoeff *
          (C ((Polynomial.legendre n).leadingCoeff)⁻¹ * derivative (Polynomial.legendre n)) := by
        rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
    _ = C (Polynomial.legendre n).leadingCoeff *
          (C (n : ℝ) * family (lobattoMeasure legendreMeasure) (n - 1)) := by rw [h]
    _ = _ := by rw [← mul_assoc, ← C_mul, mul_comm (Polynomial.legendre n).leadingCoeff]

end Quadrature

namespace Quadrature

open OrthogonalPolynomial

/-! ### The Legendre–Gauss–Lobatto weights -/

/-- The identity $(x^2 - 1) L_{m+1}' = (m + 1)(x L_{m+1} - L_m)$, from the two Legendre differential
identities. -/
private theorem quad_mul_derivative_legendre_succ (m : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (Polynomial.legendre (m + 1)) =
      C ((m : ℝ) + 1) * (X * Polynomial.legendre (m + 1) - Polynomial.legendre m) := by
  have h1 := Polynomial.quad_mul_derivative_legendre m
  have h2 := Polynomial.derivative_legendre_succ m
  rw [h2]
  simp only [map_add, map_natCast, map_one]
  linear_combination X * h1

/-- The Lobatto nodal polynomial of the Legendre weight with $m + 2$ nodes is
$x\, p_{m+1} - c\, p_m$ with $c = \operatorname{lc}(L_m)/\operatorname{lc}(L_{m+1})$, for the
monic Legendre polynomials $p_k$. -/
private theorem lobattoNodal_legendreMeasure_eq (m : ℕ) :
    lobattoNodal legendreMeasure (m + 1) =
      X * family legendreMeasure (m + 1) -
        C ((Polynomial.legendre m).leadingCoeff / (Polynomial.legendre (m + 1)).leadingCoeff) *
          family legendreMeasure m := by
  have hlcm : (Polynomial.legendre m).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero m)
  have hlcm1 : (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero (m + 1))
  have hne : ((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    mul_ne_zero (by positivity) hlcm1
  have hq : family (lobattoMeasure legendreMeasure) m =
      C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
        derivative (Polynomial.legendre (m + 1)) := by
    have h := derivative_legendre_eq_family (n := m + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    rw [h, ← mul_assoc, ← C_mul]
    push_cast
    rw [inv_mul_cancel₀ hne, C_1, one_mul]
  rw [lobattoNodal, Nat.add_sub_cancel, hq, family_eq_legendre, family_eq_legendre]
  calc (X ^ 2 - 1) * (C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
        derivative (Polynomial.legendre (m + 1)))
      = C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
          ((X ^ 2 - 1) * derivative (Polynomial.legendre (m + 1))) := by ring
    _ = C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
          (C ((m : ℝ) + 1) * (X * Polynomial.legendre (m + 1) - Polynomial.legendre m)) := by
        rw [quad_mul_derivative_legendre_succ]
    _ = _ := by
        rw [← mul_assoc, ← C_mul]
        have e1 : (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ * ((m : ℝ) + 1) =
            ((Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ := by
          field_simp
        have e2 : (Polynomial.legendre m).leadingCoeff /
            (Polynomial.legendre (m + 1)).leadingCoeff * ((Polynomial.legendre m).leadingCoeff)⁻¹ =
            ((Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ := by
          field_simp
        rw [e1, mul_sub, ← mul_assoc (C _) (C _), ← C_mul, e2]
        ring

/-- The derivative of the Lobatto nodal polynomial of the Legendre weight with $m + 2$ nodes is
$(m + 2)\, p_{m+1}$, by the Legendre differential equation. -/
private theorem derivative_lobattoNodal_legendreMeasure (m : ℕ) :
    derivative (lobattoNodal legendreMeasure (m + 1)) =
      C ((m : ℝ) + 2) * family legendreMeasure (m + 1) := by
  have hlcm1 : (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero (m + 1))
  have hne : ((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    mul_ne_zero (by positivity) hlcm1
  have hq : family (lobattoMeasure legendreMeasure) m =
      C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
        derivative (Polynomial.legendre (m + 1)) := by
    have h := derivative_legendre_eq_family (n := m + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    rw [h, ← mul_assoc, ← C_mul]
    push_cast
    rw [inv_mul_cancel₀ hne, C_1, one_mul]
  have hode := Polynomial.legendre_ode (m + 1)
  push_cast at hode
  rw [lobattoNodal, Nat.add_sub_cancel, hq, family_eq_legendre,
    show (X ^ 2 - 1) * (C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
      derivative (Polynomial.legendre (m + 1))) =
      C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
        ((X ^ 2 - 1) * derivative (Polynomial.legendre (m + 1))) by ring,
    derivative_C_mul, derivative_mul]
  have hder : derivative (X ^ 2 - 1 : ℝ[X]) = 2 * X := by
    rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, C_eq_natCast]
    norm_num
  rw [hder]
  have e : (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (Polynomial.legendre (m + 1))) +
      2 * X * derivative (Polynomial.legendre (m + 1)) =
      C (((m : ℝ) + 1) * ((m : ℝ) + 2)) * Polynomial.legendre (m + 1) := by
    rw [hode]
    simp only [map_mul, map_add, map_natCast, map_one, map_ofNat]
    ring
  rw [show 2 * X * derivative (Polynomial.legendre (m + 1)) +
      (X ^ 2 - 1) * derivative (derivative (Polynomial.legendre (m + 1))) =
      (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (Polynomial.legendre (m + 1))) +
        2 * X * derivative (Polynomial.legendre (m + 1)) by ring, e,
    ← mul_assoc (C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹), ← C_mul,
    ← mul_assoc (C ((m : ℝ) + 2)), ← C_mul]
  congr 2
  field_simp

/-- At the $m + 2$ Legendre–Gauss–Lobatto nodes, `Quadrature.weight_eq_of_nodal_eq` gives
$p_{m+1}(\bar x_j) \neq 0$ and $w_j = c \|p_m\|^2/(p_{m+1}(\bar x_j)\, \bar\omega'(\bar x_j))$
with $c = \operatorname{lc}(L_m)/\operatorname{lc}(L_{m+1})$, since the Lobatto nodal polynomial
is $p_{m+2} + (\beta_m - c)\, p_m$, where $\beta_m$ is the coefficient of the three-term
recurrence of the monic Legendre polynomials. -/
private theorem weight_eq_of_nodal_eq_lobattoNodal {m : ℕ} {x w : Fin (m + 1 + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure (m + 1))
    (j : Fin (m + 1 + 1)) :
    (family legendreMeasure (m + 1)).eval (x j) ≠ 0 ∧
      w j = (Polynomial.legendre m).leadingCoeff / (Polynomial.legendre (m + 1)).leadingCoeff *
          normSq legendreMeasure m /
        ((family legendreMeasure (m + 1)).eval (x j) *
          (derivative (Lagrange.nodal Finset.univ x)).eval (x j)) := by
  have hw := isWeight_legendreMeasure
  have hlcm : (Polynomial.legendre m).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero m)
  have hlcm1 : (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero (m + 1))
  set c : ℝ := (Polynomial.legendre m).leadingCoeff / (Polynomial.legendre (m + 1)).leadingCoeff
    with hc
  have hc0 : c ≠ 0 := div_ne_zero hlcm hlcm1
  -- the Lobatto nodal polynomial in the textbook form
  have hnodal' : Lagrange.nodal Finset.univ x = family legendreMeasure (m + 2) +
      C 0 * family legendreMeasure (m + 1) +
        C (beta legendreMeasure m - c) * family legendreMeasure m := by
    rw [hnodal, lobattoNodal_legendreMeasure_eq, three_term_recurrence hw m,
      alpha_legendreMeasure, C_0, sub_zero, C_sub]
    ring
  have hb : normSq legendreMeasure (m + 1) - (beta legendreMeasure m - c) * normSq legendreMeasure m
      ≠ 0 := by
    rw [normSq_succ hw m, show beta legendreMeasure m * normSq legendreMeasure m -
      (beta legendreMeasure m - c) * normSq legendreMeasure m =
        c * normSq legendreMeasure m by ring]
    exact mul_ne_zero hc0 (normSq_ne_zero hw m)
  obtain ⟨hpne, hwj⟩ := weight_eq_of_nodal_eq hw hx hint hnodal' hb j
  rw [normSq_succ hw m, show beta legendreMeasure m * normSq legendreMeasure m -
    (beta legendreMeasure m - c) * normSq legendreMeasure m = c * normSq legendreMeasure m by ring]
    at hwj
  exact ⟨hpne, hwj⟩

/-- **The Legendre–Gauss–Lobatto weights.** Let $n \ge 1$, and let a rule be interpolatory for the
Legendre weight $dx$ on $(-1, 1)$, with $n + 1$ distinct nodes $\bar x_j$ and weights $w_j$,
whose nodal polynomial is the Lobatto nodal polynomial of the Legendre weight. Then every
weight, at the endpoints included, is $$w_j = \frac{2}{n(n + 1)\, L_n(\bar x_j)^2}.$$ This is
equation (10.34) of [quarteroni2000numerical]; the rule of `Quadrature.exists_gaussLobatto` for
the Legendre weight satisfies the hypotheses.

The Lobatto nodal polynomial is $p_{n+1} + b\, p_{n-1}$ with $b = \beta_{n-1} -
\operatorname{lc}(L_{n-1})/\operatorname{lc}(L_n)$, where $p_k$ are the monic Legendre
polynomials and $\beta_{n-1}$ is a coefficient of their three-term recurrence. So
`Quadrature.weight_eq_of_nodal_eq` gives $w_j = (\|p_n\|^2 - b \|p_{n-1}\|^2)/(p_n(\bar x_j)\,
\bar\omega'(\bar x_j))$, and $\bar\omega' = (n + 1) p_n$ by the Legendre differential equation.
The computation follows Davis and Rabinowitz, *Methods of Numerical Integration*, §2.7. -/
theorem legendreLobattoWeight_eq {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n) (j : Fin (n + 1)) :
    w j = 2 / ((n : ℝ) * ((n : ℝ) + 1) * (Polynomial.legendre n).eval (x j) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlcm : (Polynomial.legendre m).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero m)
  have hlcm1 : (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero (m + 1))
  have hlcsucc := leadingCoeff_legendre_succ m
  obtain ⟨hpne, hwj⟩ := weight_eq_of_nodal_eq_lobattoNodal hx hint hnodal j
  rw [family_eq_legendre, eval_mul, eval_C] at hpne
  have hL : (Polynomial.legendre (m + 1)).eval (x j) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
  have h2m : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  rw [hwj, hnodal, derivative_lobattoNodal_legendreMeasure, family_eq_legendre,
    normSq_legendreMeasure, hlcsucc]
  simp only [eval_mul, eval_C]
  push_cast
  field_simp
  ring

/-- Let $n \ge 1$, and let $\bar x_0, \dots, \bar x_n$ be distinct nodes whose nodal polynomial is
the Lobatto nodal polynomial of the Legendre weight. Then $L_n(\bar x_j) \neq 0$ for every $j$.

In the computation of the weights by `Quadrature.weight_eq_of_nodal_eq`, $p_n(\bar x_j)$ is a
factor of a nonzero quantity. -/
theorem legendre_eval_ne_zero_of_nodal_eq_lobattoNodal {n : ℕ} (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n) (j : Fin (n + 1)) :
    (Polynomial.legendre n).eval (x j) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpne := (weight_eq_of_nodal_eq_lobattoNodal hx (w := fun i =>
    ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂legendreMeasure) (fun _ => rfl) hnodal j).1
  rw [family_eq_legendre, eval_mul, eval_C] at hpne
  exact fun h => hpne (by rw [h, mul_zero])

/-- **The discrete norms of the Legendre polynomials for the Legendre–Gauss–Lobatto rule.** Let
$n \ge 1$, and let a rule be interpolatory for the Legendre weight, with $n + 1$ distinct nodes
$\bar x_j$ and weights $w_j$, whose nodal polynomial is the Lobatto nodal polynomial of the
Legendre weight and which integrates every polynomial of degree at most $2n - 1$ exactly. Let
$(f, g)_n = \sum_j w_j f(\bar x_j) g(\bar x_j)$. Then for $k, l \le n$, $$(L_k, L_l)_n =
\begin{cases} 2/(2k + 1) & \text{if } k = l < n, \\ 2/n & \text{if } k = l = n, \\ 0 & \text{if
} k \neq l. \end{cases}$$ This is the discrete inner product of §10.4 of
[quarteroni2000numerical].

For $k, l$ with $k + l \le 2n - 1$ the value follows from exactness. The value
$(L_n, L_n)_n = 2/n$ follows from the weights $2/(n(n + 1) L_n(\bar x_j)^2)$ of
`Quadrature.legendreLobattoWeight_eq`; this is the hint of Exercise 10.6 of
[quarteroni2000numerical]. The inner product is `Quadrature.discreteInner`. -/
theorem discreteInner_legendre_legendre {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n)
    (hexact : IsExactOnMeasure legendreMeasure w x (2 * n - 1)) {k l : ℕ} (hk : k ≤ n)
    (hl : l ≤ n) :
    discreteInner w x (fun t => (Polynomial.legendre k).eval t)
        (fun t => (Polynomial.legendre l).eval t) =
      if k = l then (if k = n then (2 : ℝ) / n else 2 / (2 * (k : ℝ) + 1)) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl]
    by_cases hkn : k = n
    · subst hkn
      rw [ite_eq_left rfl, discreteInner]
      have hval : ∀ i, w i * (Polynomial.legendre k).eval (x i) *
          (Polynomial.legendre k).eval (x i) = 2 / (k * (k + 1)) := by
        intro i
        rw [legendreLobattoWeight_eq hn hx hint hnodal i]
        have := legendre_eval_ne_zero_of_nodal_eq_lobattoNodal hn hx hnodal i
        field_simp
      simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      push_cast
      field_simp
    · rw [ite_eq_right hkn, discreteInner_eq_integral_of_degree_le hexact
        (by rw [Polynomial.degree_legendre]; exact_mod_cast (by omega : k + k ≤ 2 * n - 1)),
        integral_legendreMeasure, Polynomial.integral_legendre_mul_legendre, ite_eq_left rfl]
  · rw [ite_eq_right hkl, discreteInner_eq_integral_of_degree_le hexact
      (by rw [Polynomial.degree_legendre, Polynomial.degree_legendre]
          exact_mod_cast (by omega : k + l ≤ 2 * n - 1)),
      integral_legendreMeasure, Polynomial.integral_legendre_mul_legendre, ite_eq_right hkl]

/-- **The discrete Legendre transform.** Let $n \ge 1$, and let a rule be interpolatory for the
Legendre weight, with $n + 1$ distinct nodes $\bar x_i$ and positive weights $w_i$, whose nodal
polynomial is the Lobatto nodal polynomial of the Legendre weight and which integrates every
polynomial of degree at most $2n - 1$ exactly. Let $f : \mathbb{R} \to \mathbb{R}$. Then the
Lagrange interpolant of $f$ at the nodes is $\sum_{k=0}^n \tilde f_k L_k$, with $$\tilde f_k =
\frac{2k + 1}{n(n + 1)} \sum_i \frac{L_k(\bar x_i) f(\bar x_i)}{L_n(\bar x_i)^2} \quad (k < n),
\qquad \tilde f_n = \frac{1}{n + 1} \sum_i \frac{f(\bar x_i)}{L_n(\bar x_i)}.$$ This is
equations (10.38)–(10.40) and Exercise 10.6 of [quarteroni2000numerical].

The proof is `Quadrature.interpolate_eq_sum_discreteInner_smul` for the Legendre weight, with
the discrete norms `Quadrature.discreteInner_legendre_legendre` and the weights
`Quadrature.legendreLobattoWeight_eq`. -/
theorem interpolate_eq_sum_dlt {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hwpos : ∀ i, 0 < w i)
    (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n)
    (hexact : IsExactOnMeasure legendreMeasure w x (2 * n - 1)) (f : ℝ → ℝ) :
    Lagrange.interpolate Finset.univ x (fun i => f (x i)) =
      ∑ k ∈ Finset.range (n + 1),
        C (if k = n then 1 / ((n : ℝ) + 1) * ∑ i, f (x i) / (Polynomial.legendre n).eval (x i)
          else (2 * k + 1) / ((n : ℝ) * ((n : ℝ) + 1)) *
            ∑ i, (Polynomial.legendre k).eval (x i) * f (x i) /
              (Polynomial.legendre n).eval (x i) ^ 2) * Polynomial.legendre k := by
  have hw := isWeight_legendreMeasure
  have hLn : ∀ i, (Polynomial.legendre n).eval (x i) ≠ 0 := fun i =>
    legendre_eval_ne_zero_of_nodal_eq_lobattoNodal hn hx hnodal i
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [interpolate_eq_sum_discreteInner_smul hw hn hx hwpos hexact f,
    ← Fin.sum_univ_eq_sum_range (fun k => C (if k = n then 1 / ((n : ℝ) + 1) *
      ∑ i, f (x i) / (Polynomial.legendre n).eval (x i)
      else (2 * k + 1) / ((n : ℝ) * ((n : ℝ) + 1)) *
        ∑ i, (Polynomial.legendre k).eval (x i) * f (x i) /
          (Polynomial.legendre n).eval (x i) ^ 2) * Polynomial.legendre k) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
  have hlc : (Polynomial.legendre k).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero k)
  set c : ℝ := ((Polynomial.legendre k).leadingCoeff)⁻¹ with hc
  rw [family_eq_legendre]
  have e1 : discreteInner w x f (fun t => (C c * Polynomial.legendre k).eval t) =
      c * discreteInner w x f (fun t => (Polynomial.legendre k).eval t) := by
    simp only [discreteInner, eval_mul, eval_C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : discreteInner w x (fun t => (C c * Polynomial.legendre k).eval t)
      (fun t => (C c * Polynomial.legendre k).eval t) =
      c ^ 2 * discreteInner w x (fun t => (Polynomial.legendre k).eval t)
        (fun t => (Polynomial.legendre k).eval t) := by
    simp only [discreteInner, eval_mul, eval_C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hv := discreteInner_legendre_legendre hn hx hint hnodal hexact hk hk
  rw [ite_eq_left rfl] at hv
  have hf : discreteInner w x f (fun t => (Polynomial.legendre k).eval t) =
      2 / ((n : ℝ) * ((n : ℝ) + 1)) * ∑ i, (Polynomial.legendre k).eval (x i) * f (x i) /
        (Polynomial.legendre n).eval (x i) ^ 2 := by
    rw [discreteInner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [legendreLobattoWeight_eq hn hx hint hnodal i]
    have := hLn i
    field_simp
  rw [e1, e2, hv, hf, ← mul_assoc, ← C_mul]
  congr 2
  by_cases hkn : (k : ℕ) = n
  · rw [ite_eq_left hkn, ite_eq_left hkn]
    have hS : ∑ i, (Polynomial.legendre k).eval (x i) * f (x i) /
        (Polynomial.legendre n).eval (x i) ^ 2 =
        ∑ i, f (x i) / (Polynomial.legendre n).eval (x i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hkn]
      have := hLn i
      field_simp
    rw [hS, hc]
    field_simp
  · rw [ite_eq_right hkn, ite_eq_right hkn]
    have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    rw [hc]
    field_simp

end Quadrature

end
