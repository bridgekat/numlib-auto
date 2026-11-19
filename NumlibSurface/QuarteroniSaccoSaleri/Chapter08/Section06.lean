/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.BSpline
import Numlib.Approximation.Spline
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 8.6: Approximation by splines

This module formalizes Section 8.6 of [quarteroni2000numerical]. Let
$a = x_0 < x_1 < \cdots < x_n = b$ be nodes of $[a, b]$. A spline of degree $k$ is a function of
class $C^{k-1}$ on $[a, b]$ that is a polynomial of degree at most $k$ on every panel
$[x_j, x_{j+1}]$ (Definition 8.1). The splines of degree $k$ form a space $\mathcal{S}_k$ of
dimension $n + k$, with the periodic (8.44) and natural (8.45) end conditions as special classes.
Section 8.6.1 constructs the cubic spline $s_3$ that interpolates values $f_i$ at the nodes from its
moments $M_i = s_3''(x_i)$: they solve the tridiagonal system (8.47)–(8.48), which has a unique
solution for every closure of type (8.48). The module states the natural, clamped, periodic and
not-a-knot splines, the cardinal spline basis, the minimum norm property of Holladay (Property 8.2),
and the error of the clamped spline (Property 8.3, with non-sharp constants). Section 8.6.2 defines
the normalized B-spline $B_{i,k+1}$ as a scaled divided difference of a truncated power (Definition
8.2), and states its explicit form (8.53), its support and positivity, the Cox–de Boor recursion
(8.54), coincident knots (Remark 8.3), the uniform cubic B-spline (Example 8.9), the B-spline basis
(8.55)–(8.56), the endpoint values (8.57) and the knot insertion of Boehm (Remark 8.4).

The proofs specialize the backbone modules `Numlib.Approximation.Spline` (the spline space
`Spline.splineSpace`, the interpolatory cubic splines `Spline.IsCubicInterp`, the moment system
`Spline.momentMatrix`, the cardinal basis `Spline.cardinalBasis` and the lemmas of Holladay) and
`Numlib.Approximation.BSpline` (the B-spline `BSpline.bspline` of the Cox–de Boor recursion, the
divided-difference form `BSpline.nform` and the B-spline basis).

## Main definitions

* Definition 8.1, `QuarteroniSaccoSaleri.Chapter08.definition_8_1`: the space $\mathcal{S}_k$ of
  splines of degree $k$ on the nodes $x_0, \ldots, x_n$.
* (8.44), `QuarteroniSaccoSaleri.Chapter08.equation_8_44`: the periodic end conditions
  $s^{(m)}(a) = s^{(m)}(b)$, $m = 0, \ldots, k - 1$.
* (8.45), `QuarteroniSaccoSaleri.Chapter08.equation_8_45`: the natural end conditions of a spline of
  odd degree $2l - 1$.
* Section 8.6.1, `QuarteroniSaccoSaleri.Chapter08.IsCubicInterpSpline`: the cubic spline that
  interpolates the values $f_i$ at the nodes.
* Definition 8.2, `QuarteroniSaccoSaleri.Chapter08.definition_8_2`: the normalized B-spline
  $B_{i,k+1}(x) = (x_{i+k+1} - x_i) g[x_i, \ldots, x_{i+k+1}]$ with $g(t) = (t - x)_+^k$.
* Remark 8.3, `QuarteroniSaccoSaleri.Chapter08.remark_8_3_confluent`: the divided differences at
  partially coincident nodes.

## Main results

* Definition 8.1, `QuarteroniSaccoSaleri.Chapter08.mem_definition_8_1_iff`: the conditions
  (8.41)–(8.42) for an element of $\mathcal{S}_k$.
* Definition 8.1, `QuarteroniSaccoSaleri.Chapter08.definition_8_1_finrank`:
  $\dim \mathcal{S}_k = n + k$.
* (8.44), `QuarteroniSaccoSaleri.Chapter08.equation_8_44_three_iff`: the periodic end conditions of
  a cubic spline.
* (8.45), `QuarteroniSaccoSaleri.Chapter08.equation_8_45_two_iff`: the natural end conditions of a
  cubic spline are $s''(a) = s''(b) = 0$.
* Exercise 10 of Chapter 8, `QuarteroniSaccoSaleri.Chapter08.exercise_8_10`: the monomials
  $1, x, \ldots, x^k$ and the truncated powers $(x - x_i)_+^k$ at the internal nodes form a basis of
  $\mathcal{S}_k$.
* (8.46), `QuarteroniSaccoSaleri.Chapter08.equation_8_46`: $s_3''$ is linear on each panel, with the
  moments as end values.
* (8.46), `QuarteroniSaccoSaleri.Chapter08.equation_8_46_integrated`: the formula for $s_3$ on each
  panel in terms of the moments and the data.
* (8.47), `QuarteroniSaccoSaleri.Chapter08.equation_8_47`: $\mu_i M_{i-1} + 2 M_i + \lambda_i
  M_{i+1} = d_i$ at the internal nodes.
* (8.48), `QuarteroniSaccoSaleri.Chapter08.equation_8_48_iff`: the tridiagonal system (8.48) is
  (8.47) together with the two closure rows.
* (8.48), `QuarteroniSaccoSaleri.Chapter08.equation_8_48`: for $0 \le \lambda_0, \mu_n \le 1$, the
  system (8.48) has exactly one solution.
* (8.48), `QuarteroniSaccoSaleri.Chapter08.equation_8_48_spline`: exactly one interpolatory cubic
  spline satisfies a closure of type (8.48).
* (8.48), `QuarteroniSaccoSaleri.Chapter08.equation_8_48_prolonged`: the closure
  $\lambda_0 = \mu_n = 1$, $d_0 = d_1$, $d_n = d_{n-1}$.
* Section 8.6.1, `QuarteroniSaccoSaleri.Chapter08.naturalCubicSpline_existsUnique`,
  `QuarteroniSaccoSaleri.Chapter08.clampedCubicSpline_existsUnique`,
  `QuarteroniSaccoSaleri.Chapter08.periodicCubicSpline_existsUnique` and
  `QuarteroniSaccoSaleri.Chapter08.notAKnotSpline_existsUnique`: existence and uniqueness of the
  natural, clamped, periodic and not-a-knot splines.
* Section 8.6.1, `QuarteroniSaccoSaleri.Chapter08.cardinalSplineBasis`: the cardinal splines
  $\varphi_0, \ldots, \varphi_{n+2}$ form a basis of $\mathcal{S}_3$.
* Section 8.6.1, `QuarteroniSaccoSaleri.Chapter08.cardinalSplineBasis_clampedInterp`: the clamped
  spline in the cardinal basis.
* Property 8.2, `QuarteroniSaccoSaleri.Chapter08.property_8_2`: $\int_a^b [s_3''(x)]^2 \, dx \le
  \int_a^b [f''(x)]^2 \, dx$ for the natural spline $s_3$ of $f$ (8.49).
* Property 8.2, `QuarteroniSaccoSaleri.Chapter08.property_8_2_eq_iff`: equality holds in (8.49) if
  and only if $f = s_3$.
* Exercise 11 of Chapter 8, `QuarteroniSaccoSaleri.Chapter08.exercise_8_11` and
  `QuarteroniSaccoSaleri.Chapter08.exercise_8_11_eq_iff`: Property 8.2 for the clamped spline.
* Section 8.6.1, `QuarteroniSaccoSaleri.Chapter08.clampedSpline_bestApprox_deriv2`: $s_f''$ is the
  best approximation of $f''$ in $L^2$ among the second derivatives of cubic splines.
* Property 8.3, `QuarteroniSaccoSaleri.Chapter08.property_8_3_weak`: the error bounds of order
  $h^{4-r}$, $r = 0, 1, 2$, for the clamped spline, with non-sharp constants.
* Definition 8.2, `QuarteroniSaccoSaleri.Chapter08.definition_8_2_eq_bspline`: for $k \ge 1$ the
  B-spline of Definition 8.2 is the B-spline of the recursion (8.54).
* (8.53), `QuarteroniSaccoSaleri.Chapter08.equation_8_53`: the explicit form of $B_{i,k+1}$.
* Section 8.6.2, `QuarteroniSaccoSaleri.Chapter08.bSpline_support`,
  `QuarteroniSaccoSaleri.Chapter08.bSpline_nonneg` and
  `QuarteroniSaccoSaleri.Chapter08.bSpline_pos`: $B_{i,k+1}$ vanishes outside $[x_i, x_{i+k+1}]$, is
  nonnegative, and is positive on $(x_i, x_{i+k+1})$.
* Section 8.6.2, `QuarteroniSaccoSaleri.Chapter08.bSpline_minimalSupport` and
  `QuarteroniSaccoSaleri.Chapter08.bSpline_minimalSupport_eq_zero`: $B_{i,k+1}$ is the unique
  nonzero spline of minimum support, up to a scalar factor.
* (8.54), `QuarteroniSaccoSaleri.Chapter08.equation_8_54_zero` and
  `QuarteroniSaccoSaleri.Chapter08.equation_8_54`: the Cox–de Boor recursion.
* (8.54), `QuarteroniSaccoSaleri.Chapter08.equation_8_54_definition_8_2`: the B-splines of
  Definition 8.2 satisfy the recursion.
* Remark 8.3, `QuarteroniSaccoSaleri.Chapter08.remark_8_3_left` and
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_right`: $B_{i,k+1}$ at $k + 1$ coincident knots.
* Example 8.9, `QuarteroniSaccoSaleri.Chapter08.example_8_9`: the cubic B-spline on equally spaced
  knots.
* (8.55)–(8.56), `QuarteroniSaccoSaleri.Chapter08.equation_8_56` and
  `QuarteroniSaccoSaleri.Chapter08.equation_8_56_repr`: the B-splines form a basis of
  $\mathcal{S}_k$.
* (8.57), `QuarteroniSaccoSaleri.Chapter08.equation_8_57` and
  `QuarteroniSaccoSaleri.Chapter08.equation_8_57_right`: with coincident fictitious knots,
  $s_k(a) = c_{-k}$ and $s_k(b) = c_{n-1}$.
* Remark 8.4, `QuarteroniSaccoSaleri.Chapter08.remark_8_4`: the knot insertion of Boehm.

## Conventions

* The nodes are `x : ℕ → ℝ` with `IsIntervalPartition a b n x`, that is,
  $a = x_0 < x_1 < \cdots < x_n = b$. There are $n$ panels $[x_{i-1}, x_i]$, $1 \le i \le n$, of
  lengths $h_i = x_i - x_{i-1}$.
* A spline is a function `s : ℝ → ℝ` considered on $[a, b]$. Its derivatives at a point of $[a, b]$
  are the derivatives within $[a, b]$, `derivWithin s (Icc a b)` and
  `iteratedDerivWithin 2 s (Icc a b)`. So the moment $M_i = s''(x_i)$ is
  `iteratedDerivWithin 2 s (Icc a b) (x i)`, which is `Spline.moment a b x s i`.
* The space $\mathcal{S}_k$ is a submodule of `C(Icc a b, ℝ)`. The lemma
  `QuarteroniSaccoSaleri.Chapter08.mem_definition_8_1_three_iff` connects it with the functions on
  $\mathbb{R}$ of `Spline.IsCubicSpline`.
* The knots of B-splines are indexed by $\mathbb{N}$. The book's $B_{i,k+1}$, of degree $k$, is
  `BSpline.bspline x k i`. The fictitious knots $x_{-k}, \ldots, x_{-1}$ of (8.55) are the knots
  $x_0, \ldots, x_{k-1}$ of a shifted sequence whose data knots are
  $x_k = a < \cdots < x_{n+k} = b$. The book's index $i = -k, \ldots, n - 1$ is the index $i + k$
  here.

## Deviations from the source

* **Representation.** The spline subspace uses continuous restrictions and applies the dimension
  theorem on positive-degree partitions. See `QuarteroniSaccoSaleri.Chapter08.definition_8_1`,
  `QuarteroniSaccoSaleri.Chapter08.mem_definition_8_1_iff`.
* **Convention.** Endpoints use within-interval derivatives; the natural condition has a separate
  degree parameter. See `QuarteroniSaccoSaleri.Chapter08.equation_8_44`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_45`.
* **Reading.** The twice-integrated moment formula includes the final panel. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_46`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_46_integrated`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_47`.
* **Reading.** The spline closure system makes the endpoint coefficient range and panel count
  explicit, with uniqueness on the interval. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_48_iff`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_48`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_48_spline`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_48_prolonged`.
* **Reading.** Closure uniqueness is on the spline interval. Periodic and not-a-knot cases specify
  endpoint data and panel-count requirements. See
  `QuarteroniSaccoSaleri.Chapter08.naturalCubicSpline_existsUnique`,
  `QuarteroniSaccoSaleri.Chapter08.clampedCubicSpline_existsUnique`,
  `QuarteroniSaccoSaleri.Chapter08.periodicCubicSpline_existsUnique`,
  `QuarteroniSaccoSaleri.Chapter08.notAKnotSpline_existsUnique`.
* **Reading.** The second-derivative best approximation property uses the derivative-matched clamped
  spline. See `QuarteroniSaccoSaleri.Chapter08.clampedSpline_bestApprox_deriv2`.
* **Specialization.** The clamped estimate gives weaker constants for orders zero through two, with
  the second derivative estimated at the knots. See
  `QuarteroniSaccoSaleri.Chapter08.property_8_3_weak`.
* **Convention.** The raw divided-difference form uses totalized division and agrees with the
  recursive B-spline for distinct knots and positive degree. See
  `QuarteroniSaccoSaleri.Chapter08.definition_8_2`,
  `QuarteroniSaccoSaleri.Chapter08.definition_8_2_apply`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_53`,
  `QuarteroniSaccoSaleri.Chapter08.definition_8_2_eq_bspline`.
* **Reading.** Minimal support is unique up to scalar, and the support and nonnegativity theorems
  allow repeated knots. See `QuarteroniSaccoSaleri.Chapter08.bSpline_support`,
  `QuarteroniSaccoSaleri.Chapter08.bSpline_nonneg`, `QuarteroniSaccoSaleri.Chapter08.bSpline_pos`,
  `QuarteroniSaccoSaleri.Chapter08.bSpline_minimalSupport`,
  `QuarteroniSaccoSaleri.Chapter08.bSpline_minimalSupport_eq_zero`.
* **Convention.** The degree-zero B-spline uses a half-open rather than closed interval. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_54_zero`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_54`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_54_definition_8_2`.
* **Correction.** The confluent difference at m+1 identical nodes uses derivative order m. See
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_confluent`,
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_confluent_of_lt`,
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_confluent_const`,
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_confluent_eq`.
* **Generalization.** The repeated-knot formulas drop exterior inequalities and use half-open
  support. See `QuarteroniSaccoSaleri.Chapter08.remark_8_3_left`,
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_right`.
* **Representation.** The explicit cubic uses half-open branches with the same values at all knots.
  See `QuarteroniSaccoSaleri.Chapter08.example_8_9`.
* **Specialization.** The B-spline basis uses a shifted zero-based index and strictly increasing
  extended knots. See `QuarteroniSaccoSaleri.Chapter08.equation_8_56`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_56_repr`.
* **Convention.** The final B-spline coefficient is the left-hand limit at the right endpoint. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_57`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_57_right`.
* **Correction.** Knot insertion corrects the previous-coefficient index and the refined sum's term
  count, and uses strict interior insertion. See `QuarteroniSaccoSaleri.Chapter08.remark_8_4`.
* **(8.46), integrated form** (generalization). The source states the formula for
  $i = 1, \ldots, n - 1$. It holds on every panel. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_46_integrated`.
* **The not-a-knot spline** (correction). The source does not require $n \ge 3$. For $n = 2$ the two
  conditions coincide, and the spline is not unique. See
  `QuarteroniSaccoSaleri.Chapter08.notAKnotSpline_existsUnique`.
* **Property 8.3** (reading). The source does not say which end conditions it means. The statement
  is for the clamped spline; for the natural spline it is false unless $f''(a) = f''(b) = 0$. See
  `QuarteroniSaccoSaleri.Chapter08.property_8_3_weak`.
* **(8.54), degree zero** (reading). The source prints the closed interval $[x_i, x_{i+1}]$ for
  $B_{i,1}$. The half-open interval $[x_i, x_{i+1})$ is used. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_54_zero`.
* **Remark 8.3, coincident nodes** (typo). The source prints $f^{(n+1)}(x_0)/(n+1)!$ for
  $f[x_0, \ldots, x_0]$ with $n + 1$ nodes. The value is $f^{(n)}(x_0)/n!$. See
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_confluent_const`.
* **Remark 8.3, coincident knots** (generalization). The hypotheses $x_{i-1} < x_i$ at the left and
  $x_{i+k+1} < x_{i+k+2}$ at the right are not needed. See
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_left` and
  `QuarteroniSaccoSaleri.Chapter08.remark_8_3_right`.
* **(8.55)–(8.56)** (reading). The source allows coincident fictitious knots. The basis is stated
  for strictly increasing knots. See `QuarteroniSaccoSaleri.Chapter08.equation_8_56`.
* **(8.57), right endpoint** (reading). With the half-open convention of (8.54), every B-spline
  vanishes at $b$, so $s_k(b) = c_{n-1}$ is stated as a left limit. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_57_right`.
* **Remark 8.4, coefficients** (typo). The source prints $d_i = \omega_i c_i + (1 - \omega_i) c_i$.
  The second coefficient is $c_{i-1}$. See `QuarteroniSaccoSaleri.Chapter08.remark_8_4`.
* **Remark 8.4, the new knot** (reading). The source allows $\tilde x \in [x_j, x_{j+1})$. The knots
  are strictly increasing and $\tilde x$ lies in the open panel $(x_j, x_{j+1})$ of the data range.
  See `QuarteroniSaccoSaleri.Chapter08.remark_8_4`.

## Not formalized

* **Property 8.3, the sharp constants and the case $r = 3$.** The source states $\|f^{(r)} -
  s_3^{(r)}\|_\infty \le C_r h^{4-r} \|f^{(4)}\|_\infty$ for $r = 0, 1, 2, 3$, where
  $h = \max_i h_i$ and $\beta = h / \min_i h_i$, with $C_0 = 5/384$, $C_1 = 1/24$, $C_2 = 3/8$ and
  $C_3 = (\beta + \beta^{-1})/2$, without proof or citation. These are the constants of Hall and
  Meyer (*Optimal error bounds for cubic spline interpolation*, J. Approx. Theory 16, 1976) for the
  clamped spline. The backbone has no bound with these constants, and no bound at all for $r = 3$,
  the only case in which the mesh ratio $\beta$ enters, because $s_3'''$ jumps at the nodes. The
  bounds of order $h^{4-r}$ for $r = 0, 1, 2$ with other constants are
  `QuarteroniSaccoSaleri.Chapter08.property_8_3_weak`.
* **Example 8.8**, a table.
* **Remark 8.2**, on software.
-/

open Filter MeasureTheory Polynomial Set
open scoped Topology

namespace QuarteroniSaccoSaleri.Chapter08

variable {a b : ℝ} {n k : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ} {s : ℝ → ℝ}

/-! ### Definition 8.1: splines of degree $k$ -/

/-- **Definition 8.1** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be $n + 1$ distinct
nodes of $[a, b]$ with $a = x_0 < x_1 < \cdots < x_n = b$. A function $s_k$ on $[a, b]$ is a
**spline of degree $k$** relative to the nodes $x_j$ if
$$s_k|_{[x_j, x_{j+1}]} \in \mathbb{P}_k, \quad j = 0, \ldots, n - 1, \qquad (8.41)$$
$$s_k \in C^{k-1}[a, b]. \qquad (8.42)$$
The space $\mathcal{S}_k$ consists of these splines.

The space is `Spline.splineSpace a b n x k (k - 1)`, a submodule of `C(Icc a b, ℝ)`. The
definition does not assume that the nodes increase; the theorems that need it assume
`IsIntervalPartition a b n x`.

**Reading.** The spline space consists of continuous restrictions to the interval that have a
representative with the required panel polynomials and smoothness. The definition accepts arbitrary
knot arrays and uses truncated natural subtraction at degree zero; dimension and basis theorems
assume a positive degree and a partition.
-/
noncomputable def definition_8_1 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Submodule ℝ C(Icc a b, ℝ) :=
  Spline.splineSpace a b n x k (k - 1)

/-- **Definition 8.1** of [quarteroni2000numerical], the conditions (8.41)–(8.42). Let
$a, b \in \mathbb{R}$, let $x_0, x_1, \ldots$ be real numbers, and let $v$ be a continuous
function on $[a, b]$. Then $v \in \mathcal{S}_k$ if and only if $v$ is the restriction to
$[a, b]$ of a function $g : \mathbb{R} \to \mathbb{R}$ of class $C^{k-1}$ on $[a, b]$ that
agrees on every panel $[x_j, x_{j+1}]$, $j < n$, with a polynomial of degree at most $k$.

**Reading.** The spline space consists of continuous restrictions to the interval that have a
representative with the required panel polynomials and smoothness. The definition accepts arbitrary
knot arrays and uses truncated natural subtraction at degree zero; dimension and basis theorems
assume a positive degree and a partition.
-/
theorem mem_definition_8_1_iff (v : C(Icc a b, ℝ)) :
    v ∈ definition_8_1 a b n x k ↔ ∃ g : ℝ → ℝ, ContDiffOn ℝ (k - 1 : ℕ) g (Icc a b) ∧
      (∀ t : Icc a b, v t = g t) ∧
      ∀ j < n, ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn g p.eval (Icc (x j) (x (j + 1))) :=
  Iff.rfl

/-- **Definition 8.1** of [quarteroni2000numerical], the dimension. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, and let $k \ge 1$. Then
$$\dim \mathcal{S}_k = n + k.$$

This is the count (8.43) of the book, $(k + 1) n - k (n - 1)$. The proof specializes
`Spline.finrank_splineSpace` with smoothness $r = k - 1$, which gives
$n (k - (k - 1)) + (k - 1) + 1$. -/
theorem definition_8_1_finrank (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Module.finrank ℝ (definition_8_1 a b n x k) = n + k := by
  rw [definition_8_1, Spline.finrank_splineSpace hx hn (Nat.sub_le k 1)]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  ring

/-- **Equation (8.44)** of [quarteroni2000numerical], periodic splines. Let
$s : \mathbb{R} \to \mathbb{R}$ and $k \in \mathbb{N}$. The function $s$ satisfies the
**periodic end conditions** on $[a, b]$ if
$$s^{(m)}(a) = s^{(m)}(b), \qquad m = 0, 1, \ldots, k - 1,$$
with the derivatives taken within $[a, b]$.

For $k = 0$ the natural subtraction gives $k - 1 = 0$, so the condition is $s(a) = s(b)$.

**Reading.** Endpoint derivatives are taken within the closed interval. The natural-end predicate is
parameterized by l independently of spline degree. The book uses it for l at least two and odd
degree $2l-1$, avoiding the truncated bounds at smaller parameters.
-/
def equation_8_44 (a b : ℝ) (k : ℕ) (s : ℝ → ℝ) : Prop :=
  ∀ m ≤ k - 1, iteratedDerivWithin m s (Icc a b) a = iteratedDerivWithin m s (Icc a b) b

/-- **Equation (8.44)** of [quarteroni2000numerical], for cubic splines. Let
$s : \mathbb{R} \to \mathbb{R}$. The periodic end conditions with $k = 3$ hold if and only if
$s(a) = s(b)$, $s'(a) = s'(b)$ and $s''(a) = s''(b)$, with the derivatives taken within
$[a, b]$.

The last two conditions are `Spline.IsPeriodicEnd a b s`. -/
theorem equation_8_44_three_iff :
    equation_8_44 a b 3 s ↔ s a = s b ∧ Spline.IsPeriodicEnd a b s := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by norm_num), by simpa using h 1 (by norm_num), h 2 le_rfl⟩
  · rintro ⟨h0, h1, h2⟩ m hm
    interval_cases m
    · simpa using h0
    · simpa using h1
    · exact h2

/-- **Equation (8.45)** of [quarteroni2000numerical], natural splines. Let
$s : \mathbb{R} \to \mathbb{R}$ and $l \in \mathbb{N}$, and let $k = 2l - 1$. The function $s$
satisfies the **natural end conditions** on $[a, b]$ if
$$s^{(l+j)}(a) = s^{(l+j)}(b) = 0, \qquad j = 0, 1, \ldots, l - 2,$$
with the derivatives taken within $[a, b]$.

The source takes $l \ge 2$. For $l \le 1$ the natural subtraction gives $l - 2 = 0$, so the
definition still imposes the condition with $j = 0$.

**Reading.** Endpoint derivatives are taken within the closed interval. The natural-end predicate is
parameterized by l independently of spline degree. The book uses it for l at least two and odd
degree $2l-1$, avoiding the truncated bounds at smaller parameters.
-/
def equation_8_45 (a b : ℝ) (l : ℕ) (s : ℝ → ℝ) : Prop :=
  ∀ j ≤ l - 2, iteratedDerivWithin (l + j) s (Icc a b) a = 0 ∧
    iteratedDerivWithin (l + j) s (Icc a b) b = 0

/-- **Equation (8.45)** of [quarteroni2000numerical], for cubic splines. Let
$s : \mathbb{R} \to \mathbb{R}$. The natural end conditions with $l = 2$ hold if and only if
$s''(a) = s''(b) = 0$, with the derivatives taken within $[a, b]$. -/
theorem equation_8_45_two_iff :
    equation_8_45 a b 2 s ↔
      iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0 := by
  constructor
  · intro h
    simpa using h 0 le_rfl
  · rintro ⟨h0, h1⟩ j hj
    obtain rfl : j = 0 := by omega
    exact ⟨h0, h1⟩

/-- **Equation (8.48)** of [quarteroni2000numerical], the natural closure. Let
$a = x_0 < x_1 < \cdots < x_n = b$ and $s : \mathbb{R} \to \mathbb{R}$. The natural end
conditions $s''(a) = s''(b) = 0$ hold if and only if the moments of $s$ satisfy the closure of
type (8.48) with $\lambda_0 = \mu_n = d_0 = d_n = 0$.

The closure is `Spline.HasClosure a b n x 0 0 0 0 s`. -/
theorem equation_8_45_two_iff_hasClosure (hx : IsIntervalPartition a b n x) :
    equation_8_45 a b 2 s ↔ Spline.HasClosure a b n x 0 0 0 0 s := by
  rw [equation_8_45_two_iff, Spline.HasClosure]
  simp only [Spline.moment, hx.first, hx.last, zero_mul, add_zero, zero_add, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or]

/-- **Exercise 10 of Chapter 8** of [quarteroni2000numerical]. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, and let $k \ge 1$. Let $g = n - 1$ be the
number of internal nodes. Then the functions
$$1, x, x^2, \ldots, x^k, (x - x_1)_+^k, \ldots, (x - x_g)_+^k$$
form a basis of $\mathcal{S}_k$. So every $s_k \in \mathcal{S}_k$ can be written uniquely as
$s_k(x) = \sum_{i=0}^k b_i x^i + \sum_{i=1}^g c_i (x - x_i)_+^k$.

The basis is indexed by `Fin (n + k)`. Its first $k + 1$ vectors are the monomials, and the
vector with index $i > k$ is the truncated power $(x - x_{i-k})_+^k$ =
`Quadrature.truncPow k x (x (i - k))`. The proof is `Spline.exists_basis_truncPow`. -/
theorem exercise_8_10 (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ B : Module.Basis (Fin (n + k)) ℝ (definition_8_1 a b n x k),
      (∀ i : Fin (n + k), (i : ℕ) ≤ k → ∀ t : Icc a b,
        (B i : C(Icc a b, ℝ)) t = (t : ℝ) ^ (i : ℕ)) ∧
      ∀ i : Fin (n + k), k < i → ∀ t : Icc a b,
        (B i : C(Icc a b, ℝ)) t = Quadrature.truncPow k (t : ℝ) (x (i - k)) :=
  Spline.exists_basis_truncPow hx hn hk

/-! ### Section 8.6.1: interpolatory cubic splines -/

/-- **Section 8.6.1** of [quarteroni2000numerical], the interpolatory cubic spline. Let
$a, b \in \mathbb{R}$, let $x_0, \ldots, x_n$ be nodes and $f_0, \ldots, f_n$ values. A function
$s : \mathbb{R} \to \mathbb{R}$ is a **cubic spline interpolating the values $f_i$** if $s$ is
of class $C^2$ on $[a, b]$, $s$ is a polynomial of degree at most $3$ on every panel
$[x_{i-1}, x_i]$, $1 \le i \le n$, and $s(x_i) = f_i$ for $i = 0, \ldots, n$.

The definition is `Spline.IsCubicInterp a b n x f s`. The book writes $m_i = s'(x_i)$ and
$M_i = s''(x_i)$, with the derivatives taken within $[a, b]$. -/
abbrev IsCubicInterpSpline (a b : ℝ) (n : ℕ) (x f : ℕ → ℝ) (s : ℝ → ℝ) : Prop :=
  Spline.IsCubicInterp a b n x f s

/-- A function $s$ is a cubic spline interpolating the values $f_i$ if and only if $s$ is of class
$C^2$ on $[a, b]$, $s$ agrees with a polynomial of degree at most $3$ on every panel
$[x_{i-1}, x_i]$, $1 \le i \le n$, and $s(x_i) = f_i$ for $i \le n$. -/
theorem isCubicInterpSpline_iff :
    IsCubicInterpSpline a b n x f s ↔ ContDiffOn ℝ 2 s (Icc a b) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∃ p : ℝ[X], p.degree ≤ 3 ∧ EqOn s p.eval (Icc (x (i - 1)) (x i))) ∧
      ∀ i ≤ n, s (x i) = f i :=
  ⟨fun h => ⟨h.contDiffOn, h.piecewise, h.interp⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- **Definition 8.1** of [quarteroni2000numerical], the cubic case. A continuous function $v$ on
$[a, b]$ lies in $\mathcal{S}_3$ if and only if $v$ is the restriction to $[a, b]$ of a function
$s : \mathbb{R} \to \mathbb{R}$ that is of class $C^2$ on $[a, b]$ and a polynomial of degree at
most $3$ on every panel.

The second condition is `Spline.IsCubicSpline a b n x s`. -/
theorem mem_definition_8_1_three_iff (v : C(Icc a b, ℝ)) :
    v ∈ definition_8_1 a b n x 3 ↔
      ∃ s : ℝ → ℝ, Spline.IsCubicSpline a b n x s ∧ ∀ t : Icc a b, v t = s t := by
  have h2 : ((3 - 1 : ℕ) : WithTop ℕ∞) = 2 := by norm_num
  rw [mem_definition_8_1_iff, h2]
  constructor
  · rintro ⟨g, hg, hv, hp⟩
    refine ⟨g, ⟨hg, fun i hi1 hin => ?_⟩, hv⟩
    obtain ⟨p, hpd, hpe⟩ := hp (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at hpe
    exact ⟨p, hpd, hpe⟩
  · rintro ⟨g, hg, hv⟩
    refine ⟨g, hg.contDiffOn, hv, fun j hj => ?_⟩
    obtain ⟨p, hpd, hpe⟩ := hg.piecewise (j + 1) (by omega) hj
    rw [Nat.add_sub_cancel] at hpe
    exact ⟨p, hpd, hpe⟩

/-- **Definition 8.1** of [quarteroni2000numerical], the cubic case. If
$s : \mathbb{R} \to \mathbb{R}$ is of class $C^2$ on $[a, b]$ and a polynomial of degree at most
$3$ on every panel, then the restriction of $s$ to $[a, b]$ lies in $\mathcal{S}_3$. -/
theorem mem_definition_8_1_three_of_isCubicSpline (hs : Spline.IsCubicSpline a b n x s) :
    (⟨(Icc a b).domRestrict s, hs.contDiffOn.continuousOn.domRestrict⟩ : C(Icc a b, ℝ)) ∈
      definition_8_1 a b n x 3 :=
  (mem_definition_8_1_three_iff _).mpr ⟨s, hs, fun _ => rfl⟩

section Cubic

variable (hx : IsIntervalPartition a b n x)
include hx

/-- **Equation (8.46)** of [quarteroni2000numerical]. Let $a = x_0 < x_1 < \cdots < x_n = b$, let
$s_3$ be a cubic spline interpolating the values $f_i$ at the nodes, and let $M_i = s_3''(x_i)$.
Let $1 \le i \le n$ and $h_i = x_i - x_{i-1}$. Then $s_3''$ is linear on $[x_{i-1}, x_i]$:
$$s_3''(x) = M_{i-1} \frac{x_i - x}{h_i} + M_i \frac{x - x_{i-1}}{h_i}, \qquad x \in [x_{i-1},
  x_i].$$

The second derivative is taken within $[a, b]$. On each panel the spline is the panel cubic of
its moments (`Spline.IsCubicInterp.eqOn_panelCubic`), whose second derivative is
`Spline.panelCubicD2_apply`.

**Reading.** Endpoint derivatives are taken within the interval and the integrated expression is
stated on every panel, including the final panel omitted in the source's integrated formula range.
-/
theorem equation_8_46 (hs : IsCubicInterpSpline a b n x f s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {t : ℝ} (ht : t ∈ Icc (x (i - 1)) (x i)) :
    iteratedDerivWithin 2 s (Icc a b) t
      = iteratedDerivWithin 2 s (Icc a b) (x (i - 1)) * (x i - t) / (x i - x (i - 1))
        + iteratedDerivWithin 2 s (Icc a b) (x i) * (t - x (i - 1)) / (x i - x (i - 1)) := by
  have hlt : x (i - 1) < x i := hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have heq := hs.eqOn_panelCubic hx hi1 hin
  rw [(Spline.derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn hlt hsub heq ht).2]
  exact Spline.panelCubicD2_apply x f (Spline.moment a b x s) hlt t

/-- **Equation (8.46)** of [quarteroni2000numerical], integrated twice. Let
$a = x_0 < x_1 < \cdots < x_n = b$, let $s_3$ be a cubic spline interpolating the values $f_i$
at the nodes, and let $M_i = s_3''(x_i)$. Let $1 \le i \le n$ and $h_i = x_i - x_{i-1}$. Then
for $x \in [x_{i-1}, x_i]$,
$$s_3(x) = M_{i-1} \frac{(x_i - x)^3}{6 h_i} + M_i \frac{(x - x_{i-1})^3}{6 h_i} + C_{i-1} (x -
  x_{i-1}) + \tilde C_{i-1},$$
where the conditions $s_3(x_{i-1}) = f_{i-1}$ and $s_3(x_i) = f_i$ give
$$\tilde C_{i-1} = f_{i-1} - M_{i-1} \frac{h_i^2}{6}, \qquad C_{i-1} = \frac{f_i -
  f_{i-1}}{h_i} - \frac{h_i}{6} (M_i - M_{i-1}).$$

**Generalization.** The source states the formula for $i = 1, \ldots, n - 1$. It holds on every
panel, $i = 1, \ldots, n$.

**Reading.** Endpoint derivatives are taken within the interval and the integrated expression is
stated on every panel, including the final panel omitted in the source's integrated formula range.
-/
theorem equation_8_46_integrated (hs : IsCubicInterpSpline a b n x f s) {i : ℕ} (hi1 : 1 ≤ i)
    (hin : i ≤ n) {t : ℝ} (ht : t ∈ Icc (x (i - 1)) (x i)) :
    s t = iteratedDerivWithin 2 s (Icc a b) (x (i - 1)) * (x i - t) ^ 3 / (6 * (x i - x (i - 1)))
      + iteratedDerivWithin 2 s (Icc a b) (x i) * (t - x (i - 1)) ^ 3 / (6 * (x i - x (i - 1)))
      + ((f i - f (i - 1)) / (x i - x (i - 1)) - (x i - x (i - 1)) / 6
          * (iteratedDerivWithin 2 s (Icc a b) (x i)
            - iteratedDerivWithin 2 s (Icc a b) (x (i - 1)))) * (t - x (i - 1))
      + (f (i - 1)
          - iteratedDerivWithin 2 s (Icc a b) (x (i - 1)) * (x i - x (i - 1)) ^ 2 / 6) := by
  rw [hs.eqOn_panelCubic hx hi1 hin ht, Spline.panelCubic_apply]
  rfl

/-- **Equation (8.47)** of [quarteroni2000numerical], the M-continuity system. Let
$a = x_0 < x_1 < \cdots < x_n = b$, let $s_3$ be a cubic spline interpolating the values $f_i$
at the nodes, and let $M_i = s_3''(x_i)$ and $h_i = x_i - x_{i-1}$. Then for
$i = 1, \ldots, n - 1$,
$$\mu_i M_{i-1} + 2 M_i + \lambda_i M_{i+1} = d_i,$$
where
$$\mu_i = \frac{h_i}{h_i + h_{i+1}}, \qquad \lambda_i = \frac{h_{i+1}}{h_i + h_{i+1}}, \qquad
  d_i = \frac{6}{h_i + h_{i+1}} \left( \frac{f_{i+1} - f_i}{h_{i+1}} - \frac{f_i - f_{i-1}}{h_i}
  \right).$$

The equations express the continuity of $s_3'$ at the internal nodes. The proof is
`Spline.IsCubicInterp.isMomentEq`.

**Reading.** Endpoint derivatives are taken within the interval and the integrated expression is
stated on every panel, including the final panel omitted in the source's integrated formula range.
-/
theorem equation_8_47 (hs : IsCubicInterpSpline a b n x f s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    (x i - x (i - 1)) / ((x i - x (i - 1)) + (x (i + 1) - x i))
        * iteratedDerivWithin 2 s (Icc a b) (x (i - 1))
      + 2 * iteratedDerivWithin 2 s (Icc a b) (x i)
      + (x (i + 1) - x i) / ((x i - x (i - 1)) + (x (i + 1) - x i))
        * iteratedDerivWithin 2 s (Icc a b) (x (i + 1))
      = 6 / ((x i - x (i - 1)) + (x (i + 1) - x i))
        * ((f (i + 1) - f i) / (x (i + 1) - x i) - (f i - f (i - 1)) / (x i - x (i - 1))) := by
  have h := hs.isMomentEq hx hi1 hin
  simp only [Spline.IsMomentEq, Spline.panelLength, Spline.moment, Nat.add_sub_cancel] at h
  exact h

/-- **Equation (8.48)** of [quarteroni2000numerical], the system. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, let $f_0, \ldots, f_n$ be values, let
$\lambda_0, \mu_n, d_0, d_n \in \mathbb{R}$, and let $M_0, \ldots, M_n \in \mathbb{R}$. With
$h_i = x_i - x_{i-1}$ and the coefficients $\mu_i$, $\lambda_i$, $d_i$ of (8.47), the
tridiagonal system
$$\begin{bmatrix} 2 & \lambda_0 & & & \\ \mu_1 & 2 & \lambda_1 & & \\ & \ddots & \ddots & \ddots
  & \\ & & \mu_{n-1} & 2 & \lambda_{n-1} \\ & & & \mu_n & 2 \end{bmatrix} \begin{bmatrix} M_0 \\
  M_1 \\ \vdots \\ M_{n-1} \\ M_n \end{bmatrix} = \begin{bmatrix} d_0 \\ d_1 \\ \vdots \\
  d_{n-1} \\ d_n \end{bmatrix}$$
holds if and only if the equations (8.47) hold for $i = 1, \ldots, n - 1$,
$2 M_0 + \lambda_0 M_1 = d_0$, and $\mu_n M_{n-1} + 2 M_n = d_n$.

The system is `Spline.momentMatrix n h lam0 mun *ᵥ M = Spline.momentRhs n h f d0 dn` with $h$ =
`Spline.panelLength x`. The proof is `Spline.momentMatrix_mulVec_eq_iff`.

**Reading.** Spline uniqueness means equality on the spline interval. Matrix solvability uses
endpoint off-diagonal coefficients in the unit interval; the prolongation needs at least two panels
so that the adjacent interior expressions are defined.
-/
theorem equation_8_48_iff (hn : 1 ≤ n) (lam0 mun d0 dn : ℝ) (M : ℕ → ℝ) :
    (Spline.momentMatrix n (Spline.panelLength x) lam0 mun).mulVec
        (fun i : Fin (n + 1) => M i) = Spline.momentRhs n (Spline.panelLength x) f d0 dn ↔
      (∀ i, 1 ≤ i → i < n →
        (x i - x (i - 1)) / ((x i - x (i - 1)) + (x (i + 1) - x i)) * M (i - 1) + 2 * M i
          + (x (i + 1) - x i) / ((x i - x (i - 1)) + (x (i + 1) - x i)) * M (i + 1)
          = 6 / ((x i - x (i - 1)) + (x (i + 1) - x i))
            * ((f (i + 1) - f i) / (x (i + 1) - x i) - (f i - f (i - 1)) / (x i - x (i - 1)))) ∧
      2 * M 0 + lam0 * M 1 = d0 ∧ mun * M (n - 1) + 2 * M n = dn := by
  rw [Spline.momentMatrix_mulVec_eq_iff hx hn]
  have he : ∀ i ≤ n, Spline.extendFin (fun i : Fin (n + 1) => M i) i = M i := fun i hi => by
    rw [Spline.extendFin_of_lt _ (by omega)]
  simp only [Spline.IsMomentEq, Spline.panelLength, Nat.add_sub_cancel]
  rw [he 0 (by omega), he 1 hn, he (n - 1) (by omega), he n le_rfl]
  refine and_congr (forall_congr' fun i => forall_congr' fun hi1 => forall_congr' fun hin => ?_)
    Iff.rfl
  rw [he (i - 1) (by omega), he i hin.le, he (i + 1) hin]

/-- **Equation (8.48)** of [quarteroni2000numerical], unique solvability. Let
$a = x_0 < x_1 < \cdots < x_n = b$, let $0 \le \lambda_0 \le 1$ and $0 \le \mu_n \le 1$, and let
$f_0, \ldots, f_n$ and $d_0, d_n$ be real numbers. Then the tridiagonal system (8.48) has
exactly one solution $M = (M_0, \ldots, M_n)$.

The matrix is strictly diagonally dominant, hence nonsingular (`Spline.isUnit_momentMatrix`).

**Reading.** Spline uniqueness means equality on the spline interval. Matrix solvability uses
endpoint off-diagonal coefficients in the unit interval; the prolongation needs at least two panels
so that the adjacent interior expressions are defined.
-/
theorem equation_8_48 {lam0 mun : ℝ} (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun)
    (hm1 : mun ≤ 1) (f : ℕ → ℝ) (d0 dn : ℝ) :
    ∃! M : Fin (n + 1) → ℝ, (Spline.momentMatrix n (Spline.panelLength x) lam0 mun).mulVec M
      = Spline.momentRhs n (Spline.panelLength x) f d0 dn := by
  have hA := Spline.isUnit_momentMatrix (h := Spline.panelLength x) (n := n)
    (fun i hi1 hin => hx.panelLength_pos hi1 hin) hl0 hl1 hm0 hm1
  obtain ⟨M, hM⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hA
    (Spline.momentRhs n (Spline.panelLength x) f d0 dn)
  exact ⟨M, hM, fun N hN => Matrix.mulVec_injective_iff_isUnit.mpr hA (hN.trans hM.symm)⟩

/-- **Equation (8.48)** of [quarteroni2000numerical], the interpolatory cubic spline with a closure
of type (8.48). Let $a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, let
$0 \le \lambda_0 \le 1$ and $0 \le \mu_n \le 1$, and let $f_0, \ldots, f_n$ and $d_0, d_n$ be
real numbers. Then there is a cubic spline $s$ interpolating the values $f_i$ whose moments
$M_i = s''(x_i)$ satisfy
$$2 M_0 + \lambda_0 M_1 = d_0, \qquad \mu_n M_{n-1} + 2 M_n = d_n,$$
and any two such splines agree on $[a, b]$.

The proof is `Spline.existsUnique_isCubicInterp_of_closure`.

**Reading.** Spline uniqueness means equality on the spline interval. Matrix solvability uses
endpoint off-diagonal coefficients in the unit interval; the prolongation needs at least two panels
so that the adjacent interior expressions are defined.
-/
theorem equation_8_48_spline (hn : 1 ≤ n) {lam0 mun : ℝ} (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1)
    (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) (f : ℕ → ℝ) (d0 dn : ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧
        2 * iteratedDerivWithin 2 s (Icc a b) (x 0) + lam0 * iteratedDerivWithin 2 s (Icc a b) (x 1)
          = d0 ∧
        mun * iteratedDerivWithin 2 s (Icc a b) (x (n - 1))
          + 2 * iteratedDerivWithin 2 s (Icc a b) (x n) = dn) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ →
        (2 * iteratedDerivWithin 2 s₁ (Icc a b) (x 0)
          + lam0 * iteratedDerivWithin 2 s₁ (Icc a b) (x 1) = d0 ∧
          mun * iteratedDerivWithin 2 s₁ (Icc a b) (x (n - 1))
            + 2 * iteratedDerivWithin 2 s₁ (Icc a b) (x n) = dn) →
        IsCubicInterpSpline a b n x f s₂ →
        (2 * iteratedDerivWithin 2 s₂ (Icc a b) (x 0)
          + lam0 * iteratedDerivWithin 2 s₂ (Icc a b) (x 1) = d0 ∧
          mun * iteratedDerivWithin 2 s₂ (Icc a b) (x (n - 1))
            + 2 * iteratedDerivWithin 2 s₂ (Icc a b) (x n) = dn) →
        EqOn s₁ s₂ (Icc a b) :=
  Spline.existsUnique_isCubicInterp_of_closure hx hn hl0 hl1 hm0 hm1 f d0 dn

/-- **Equation (8.48)** of [quarteroni2000numerical], the closure $\lambda_0 = \mu_n = 1$,
$d_0 = d_1$, $d_n = d_{n-1}$. Let $a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 2$, and let
$f_0, \ldots, f_n$ be real numbers. Then there is a cubic spline $s$ interpolating the values
$f_i$ whose moments satisfy
$$2 M_0 + M_1 = d_1, \qquad M_{n-1} + 2 M_n = d_{n-1},$$
with $d_1$ and $d_{n-1}$ as in (8.47), and any two such splines agree on $[a, b]$.

The book calls this the popular choice, which "corresponds to prolongating the spline outside
the end points of the interval $[a, b]$ and treating $a$ and $b$ as internal points".

**Reading.** Spline uniqueness means equality on the spline interval. Matrix solvability uses
endpoint off-diagonal coefficients in the unit interval; the prolongation needs at least two panels
so that the adjacent interior expressions are defined.
-/
theorem equation_8_48_prolonged (hn : 2 ≤ n) (f : ℕ → ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧
        2 * iteratedDerivWithin 2 s (Icc a b) (x 0) + 1 * iteratedDerivWithin 2 s (Icc a b) (x 1)
          = 6 / ((x 1 - x 0) + (x 2 - x 1))
            * ((f 2 - f 1) / (x 2 - x 1) - (f 1 - f 0) / (x 1 - x 0)) ∧
        1 * iteratedDerivWithin 2 s (Icc a b) (x (n - 1))
          + 2 * iteratedDerivWithin 2 s (Icc a b) (x n)
          = 6 / ((x (n - 1) - x (n - 1 - 1)) + (x n - x (n - 1)))
            * ((f n - f (n - 1)) / (x n - x (n - 1))
              - (f (n - 1) - f (n - 1 - 1)) / (x (n - 1) - x (n - 1 - 1)))) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ →
        (2 * iteratedDerivWithin 2 s₁ (Icc a b) (x 0)
          + 1 * iteratedDerivWithin 2 s₁ (Icc a b) (x 1)
          = 6 / ((x 1 - x 0) + (x 2 - x 1))
            * ((f 2 - f 1) / (x 2 - x 1) - (f 1 - f 0) / (x 1 - x 0)) ∧
          1 * iteratedDerivWithin 2 s₁ (Icc a b) (x (n - 1))
            + 2 * iteratedDerivWithin 2 s₁ (Icc a b) (x n)
            = 6 / ((x (n - 1) - x (n - 1 - 1)) + (x n - x (n - 1)))
              * ((f n - f (n - 1)) / (x n - x (n - 1))
                - (f (n - 1) - f (n - 1 - 1)) / (x (n - 1) - x (n - 1 - 1)))) →
        IsCubicInterpSpline a b n x f s₂ →
        (2 * iteratedDerivWithin 2 s₂ (Icc a b) (x 0)
          + 1 * iteratedDerivWithin 2 s₂ (Icc a b) (x 1)
          = 6 / ((x 1 - x 0) + (x 2 - x 1))
            * ((f 2 - f 1) / (x 2 - x 1) - (f 1 - f 0) / (x 1 - x 0)) ∧
          1 * iteratedDerivWithin 2 s₂ (Icc a b) (x (n - 1))
            + 2 * iteratedDerivWithin 2 s₂ (Icc a b) (x n)
            = 6 / ((x (n - 1) - x (n - 1 - 1)) + (x n - x (n - 1)))
              * ((f n - f (n - 1)) / (x n - x (n - 1))
                - (f (n - 1) - f (n - 1 - 1)) / (x (n - 1) - x (n - 1 - 1)))) →
        EqOn s₁ s₂ (Icc a b) :=
  equation_8_48_spline hx (by omega) zero_le_one le_rfl zero_le_one le_rfl f _ _

/-! ### The natural, clamped, periodic and not-a-knot splines -/

/-- **Section 8.6.1** of [quarteroni2000numerical], the natural cubic spline. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, and let $f_0, \ldots, f_n$ be real numbers.
Then there is a cubic spline $s$ interpolating the values $f_i$ with the natural end conditions
$s''(a) = s''(b) = 0$ of (8.45), and any two such splines agree on $[a, b]$.

The book obtains the natural spline by setting $\lambda_0 = \mu_n = d_0 = d_n = 0$ in (8.48).
The spline is `Spline.naturalInterp n x f` on $[a, b]$.

**Reading.** Uniqueness is on the spline interval. The periodic result assumes matching endpoint
data and at least two panels. The not-a-knot conditions require at least three panels to be
distinct, since with two panels both conditions use the same knot.
-/
theorem naturalCubicSpline_existsUnique (hn : 1 ≤ n) (f : ℕ → ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧ equation_8_45 a b 2 s) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ → equation_8_45 a b 2 s₁ →
        IsCubicInterpSpline a b n x f s₂ → equation_8_45 a b 2 s₂ → EqOn s₁ s₂ (Icc a b) := by
  have h := Spline.existsUnique_isCubicInterp_of_closure hx hn le_rfl zero_le_one le_rfl
    zero_le_one f 0 0
  simp only [← equation_8_45_two_iff_hasClosure hx] at h
  exact h

/-- **Section 8.6.1** of [quarteroni2000numerical], the natural cubic spline. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. If $s$ is a cubic spline interpolating the
values $f_i$ with $s''(a) = s''(b) = 0$, then $s$ agrees with `Spline.naturalInterp n x f` on
$[a, b]$. -/
theorem IsCubicInterpSpline.eqOn_naturalInterp (hn : 1 ≤ n) (hs : IsCubicInterpSpline a b n x f s)
    (hnat : equation_8_45 a b 2 s) : EqOn s (Spline.naturalInterp n x f) (Icc a b) :=
  hs.eqOn_cubicInterp hx hn le_rfl zero_le_one le_rfl zero_le_one
    ((equation_8_45_two_iff_hasClosure hx).mp hnat)

/-- **Section 8.6.1** of [quarteroni2000numerical], the clamped cubic spline. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, let $f_0, \ldots, f_n$ be real numbers, and
let $f'_0, f'_n \in \mathbb{R}$. Then there is a cubic spline $s$ interpolating the values $f_i$
with $s'(a) = f'_0$ and $s'(b) = f'_n$, and any two such splines agree on $[a, b]$.

The derivatives are taken within $[a, b]$. The book describes this closure as one of the form
(8.48) with $\lambda_0 = \mu_n = 1$, used when the derivatives $f'(a)$ and $f'(b)$ are
available; see also Exercise 11. The spline is `Spline.clampedInterp n x f f'0 f'n` on $[a, b]$.

**Reading.** Uniqueness is on the spline interval. The periodic result assumes matching endpoint
data and at least two panels. The not-a-knot conditions require at least three panels to be
distinct, since with two panels both conditions use the same knot.
-/
theorem clampedCubicSpline_existsUnique (hn : 1 ≤ n) (f : ℕ → ℝ) (f'0 f'n : ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧ derivWithin s (Icc a b) a = f'0 ∧
        derivWithin s (Icc a b) b = f'n) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ →
        derivWithin s₁ (Icc a b) a = f'0 ∧ derivWithin s₁ (Icc a b) b = f'n →
        IsCubicInterpSpline a b n x f s₂ →
        derivWithin s₂ (Icc a b) a = f'0 ∧ derivWithin s₂ (Icc a b) b = f'n →
        EqOn s₁ s₂ (Icc a b) := by
  have hab := hx.lt_of_pos hn
  refine ⟨⟨Spline.clampedInterp n x f f'0 f'n,
    (Spline.isCubicInterp_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl).1, ?_, ?_⟩,
    fun s₁ s₂ h₁ hc₁ h₂ hc₂ => ?_⟩
  · rw [((Spline.contDiff_clampedInterp hx hn f'0 f'n).differentiable (by norm_num) a).derivWithin
      (uniqueDiffOn_Icc hab a (left_mem_Icc.mpr hab.le))]
    exact (Spline.deriv_clampedInterp_endpoints hx hn f'0 f'n).1
  · rw [((Spline.contDiff_clampedInterp hx hn f'0 f'n).differentiable (by norm_num) b).derivWithin
      (uniqueDiffOn_Icc hab b (right_mem_Icc.mpr hab.le))]
    exact (Spline.deriv_clampedInterp_endpoints hx hn f'0 f'n).2
  · exact h₁.eqOn_of_hasClosure hx hn zero_le_one le_rfl zero_le_one le_rfl
      (h₁.hasClosure_of_derivWithin hx hn hc₁.1 hc₁.2) h₂
      (h₂.hasClosure_of_derivWithin hx hn hc₂.1 hc₂.2)

/-- **Section 8.6.1** of [quarteroni2000numerical], the clamped cubic spline. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. If $s$ is a cubic spline interpolating the
values $f_i$ with $s'(a) = f'_0$ and $s'(b) = f'_n$, then $s$ agrees with
`Spline.clampedInterp n x f f'0 f'n` on $[a, b]$. -/
theorem IsCubicInterpSpline.eqOn_clampedInterp (hn : 1 ≤ n) (hs : IsCubicInterpSpline a b n x f s)
    {f'0 f'n : ℝ} (h0 : derivWithin s (Icc a b) a = f'0) (h1 : derivWithin s (Icc a b) b = f'n) :
    EqOn s (Spline.clampedInterp n x f f'0 f'n) (Icc a b) :=
  hs.eqOn_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl
    (hs.hasClosure_of_derivWithin hx hn h0 h1)

/-- **Equation (8.44)** of [quarteroni2000numerical], the periodic cubic spline. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 2$, and let $f_0, \ldots, f_n$ be real numbers
with $f_0 = f_n$. Then there is a cubic spline $s$ interpolating the values $f_i$ with the
periodic end conditions
$$s(a) = s(b), \qquad s'(a) = s'(b), \qquad s''(a) = s''(b),$$
and any two such splines agree on $[a, b]$.

The uniqueness needs only the two conditions on the derivatives. The proof is
`Spline.existsUnique_isCubicInterp_periodic`.

**Reading.** Uniqueness is on the spline interval. The periodic result assumes matching endpoint
data and at least two panels. The not-a-knot conditions require at least three panels to be
distinct, since with two panels both conditions use the same knot.
-/
theorem periodicCubicSpline_existsUnique (hn : 2 ≤ n) (hf : f 0 = f n) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧ equation_8_44 a b 3 s) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ → equation_8_44 a b 3 s₁ →
        IsCubicInterpSpline a b n x f s₂ → equation_8_44 a b 3 s₂ → EqOn s₁ s₂ (Icc a b) := by
  obtain ⟨⟨s, hs, hp⟩, huniq⟩ := Spline.existsUnique_isCubicInterp_periodic hx hn f
  refine ⟨⟨s, hs, (equation_8_44_three_iff).mpr ⟨?_, hp⟩⟩, fun s₁ s₂ h₁ hp₁ h₂ hp₂ =>
    huniq s₁ s₂ h₁ ((equation_8_44_three_iff).mp hp₁).2 h₂ ((equation_8_44_three_iff).mp hp₂).2⟩
  rw [← hx.first, ← hx.last, hs.interp 0 (Nat.zero_le n), hs.interp n le_rfl, hf]

/-- **Section 8.6.1** of [quarteroni2000numerical], the not-a-knot spline. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 3$, and let $f_0, \ldots, f_n$ be real numbers.
Then there is a cubic spline $s$ interpolating the values $f_i$ that is a single cubic
polynomial on $[x_0, x_2]$ and on $[x_{n-2}, x_n]$, and any two such splines agree on $[a, b]$.

**Correction.** The source does not require $n \ge 3$. The hypothesis is necessary: for $n = 2$
the two conditions coincide, and they do not determine the spline.

The closure enforces the continuity of $s_3'''$ at $x_1$ and at $x_{n-1}$. Since $s_3'''$ is
constant on each panel, this means that the cubic pieces on the first two and on the last two
panels coincide, so the active knots are $x_0, x_2, \ldots, x_{n-2}, x_n$. The closure is
`Spline.IsNotAKnot n x s`, and the proof is `Spline.existsUnique_isCubicInterp_notAKnot`.

**Reading.** Uniqueness is on the spline interval. The periodic result assumes matching endpoint
data and at least two panels. The not-a-knot conditions require at least three panels to be
distinct, since with two panels both conditions use the same knot.
-/
theorem notAKnotSpline_existsUnique (hn : 3 ≤ n) (f : ℕ → ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧ Spline.IsNotAKnot n x s) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ → Spline.IsNotAKnot n x s₁ →
        IsCubicInterpSpline a b n x f s₂ → Spline.IsNotAKnot n x s₂ → EqOn s₁ s₂ (Icc a b) :=
  Spline.existsUnique_isCubicInterp_notAKnot hx hn f

/-! ### The cardinal spline basis -/

variable (hn : 1 ≤ n)
include hn

/-- Let $a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. Every cardinal spline $\varphi_i$ is of
class $C^2$ on $[a, b]$ and a polynomial of degree at most $3$ on every panel. -/
theorem isCubicSpline_cardinalBasis (i : ℕ) :
    Spline.IsCubicSpline a b n x (Spline.cardinalBasis n x i) := by
  unfold Spline.cardinalBasis
  split_ifs <;> exact (Spline.isCubicInterp_clampedInterp hx hn _ _ _).toIsCubicSpline

/-- Let $a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. Every cardinal spline $\varphi_i$ is of
class $C^2$ on $\mathbb{R}$. -/
theorem contDiff_cardinalBasis (i : ℕ) : ContDiff ℝ 2 (Spline.cardinalBasis n x i) := by
  unfold Spline.cardinalBasis
  split_ifs <;> exact Spline.contDiff_clampedInterp hx hn _ _

/-- **Section 8.6.1** of [quarteroni2000numerical], the cardinal spline basis at the nodes. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. For every $i$ and every $j \le n$,
$\varphi_i(x_j) = \delta_{ij}$. In particular $\varphi_{n+1}$ and $\varphi_{n+2}$ vanish at
every node.

The cardinal splines are `Spline.cardinalBasis n x i`. The proof is
`Spline.cardinalBasis_apply_node`. -/
theorem cardinalSplineBasis_apply_node (i : ℕ) {j : ℕ} (hj : j ≤ n) :
    Spline.cardinalBasis n x i (x j) = if i = j then 1 else 0 :=
  Spline.cardinalBasis_apply_node hx hn i hj

/-- **Section 8.6.1** of [quarteroni2000numerical], the cardinal spline basis at $x_0 = a$. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. For every $i$, $\varphi_i'(a) = 1$ if
$i = n + 1$, and $\varphi_i'(a) = 0$ otherwise, with the derivative taken within $[a, b]$. -/
theorem derivWithin_cardinalSplineBasis_left (i : ℕ) :
    derivWithin (Spline.cardinalBasis n x i) (Icc a b) a = if i = n + 1 then 1 else 0 := by
  have hab := hx.lt_of_pos hn
  rw [((contDiff_cardinalBasis hx hn i).differentiable (by norm_num) a).derivWithin
    (uniqueDiffOn_Icc hab a (left_mem_Icc.mpr hab.le))]
  exact Spline.deriv_cardinalBasis_left hx hn i

/-- **Section 8.6.1** of [quarteroni2000numerical], the cardinal spline basis at $x_n = b$. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. For $i \le n + 2$, $\varphi_i'(b) = 1$ if
$i = n + 2$, and $\varphi_i'(b) = 0$ otherwise, with the derivative taken within $[a, b]$. -/
theorem derivWithin_cardinalSplineBasis_right {i : ℕ} (hi : i ≤ n + 2) :
    derivWithin (Spline.cardinalBasis n x i) (Icc a b) b = if i = n + 2 then 1 else 0 := by
  have hab := hx.lt_of_pos hn
  rw [((contDiff_cardinalBasis hx hn i).differentiable (by norm_num) b).derivWithin
    (uniqueDiffOn_Icc hab b (right_mem_Icc.mpr hab.le))]
  exact Spline.deriv_cardinalBasis_right hx hn hi

/-- **Section 8.6.1** of [quarteroni2000numerical], the cardinal spline basis. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. The $n + 3$ cubic splines
$\varphi_0, \ldots, \varphi_{n+2}$ defined by
$$\varphi_i(x_j) = \delta_{ij}, \quad \varphi_i'(x_0) = \varphi_i'(x_n) = 0 \quad (i \le n),$$
$$\varphi_{n+1}(x_j) = 0, \quad \varphi_{n+1}'(x_0) = 1, \quad \varphi_{n+1}'(x_n) = 0,$$
$$\varphi_{n+2}(x_j) = 0, \quad \varphi_{n+2}'(x_0) = 0, \quad \varphi_{n+2}'(x_n) = 1,$$
restricted to $[a, b]$, form a basis of $\mathcal{S}_3$, "whose dimension is equal to $n + 3$".

The functions are `Spline.cardinalBasis n x i`. They are linearly independent: evaluate a
vanishing combination at the nodes and differentiate it at the endpoints. There are
$n + 3 = \dim \mathcal{S}_3$ of them. -/
theorem cardinalSplineBasis :
    ∃ B : Module.Basis (Fin (n + 3)) ℝ (definition_8_1 a b n x 3),
      ∀ (i : Fin (n + 3)) (t : Icc a b),
        (B i : C(Icc a b, ℝ)) t = Spline.cardinalBasis n x i t := by
  classical
  have hab := hx.lt_of_pos hn
  set v : Fin (n + 3) → definition_8_1 a b n x 3 := fun i =>
    ⟨_, mem_definition_8_1_three_of_isCubicSpline (isCubicSpline_cardinalBasis hx hn i)⟩ with hv
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    -- the vanishing combination, as a function on `ℝ`
    set Φ : ℝ → ℝ := fun t => ∑ i : Fin (n + 3), g i * Spline.cardinalBasis n x i t with hΦ
    have hΦ0 : EqOn Φ 0 (Icc a b) := by
      intro t ht
      have := congrArg (fun w : definition_8_1 a b n x 3 => (w : C(Icc a b, ℝ)) ⟨t, ht⟩) hg
      simpa [hv, hΦ, Submodule.coe_sum, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.coe_mk, Set.domRestrict_apply] using this
    have hΦd : ∀ t, HasDerivAt Φ (∑ i : Fin (n + 3), g i * deriv (Spline.cardinalBasis n x i) t)
        t := by
      intro t
      rw [hΦ]
      exact HasDerivAt.fun_sum fun (i : Fin (n + 3)) _ =>
        (((contDiff_cardinalBasis hx hn i).differentiable (by norm_num) t).hasDerivAt).const_mul
          (g i)
    have hderiv : ∀ t ∈ Icc a b, ∑ i : Fin (n + 3), g i * deriv (Spline.cardinalBasis n x i) t
        = 0 := by
      intro t ht
      rw [← HasDerivWithinAt.derivWithin (HasDerivAt.hasDerivWithinAt (hΦd t))
        (uniqueDiffOn_Icc hab t ht), derivWithin_congr hΦ0 (hΦ0 ht)]
      simp
    have hsingle : ∀ j : Fin (n + 3),
        ∑ i : Fin (n + 3), g i * (if (i : ℕ) = j then 1 else 0) = g j := by
      intro j
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        rw [ite_eq_right (fun h => hij (Fin.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    -- the coefficients of `φ_0, …, φ_n`
    have hnode : ∀ j : Fin (n + 3), (j : ℕ) ≤ n → g j = 0 := by
      intro j hj
      have := hΦ0 ⟨hx.left_le hj, hx.le_right hj⟩
      simp only [hΦ, Pi.zero_apply, cardinalSplineBasis_apply_node hx hn _ hj] at this
      rwa [hsingle j] at this
    -- the coefficients of `φ_{n+1}` and `φ_{n+2}`
    have hleft := hderiv a (left_mem_Icc.mpr hab.le)
    have hright := hderiv b (right_mem_Icc.mpr hab.le)
    simp only [Spline.deriv_cardinalBasis_left hx hn] at hleft
    have hright' : ∑ i : Fin (n + 3), g i * (if (i : ℕ) = n + 2 then 1 else 0) = 0 := by
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hright
      rw [Spline.deriv_cardinalBasis_right hx hn (Nat.lt_succ_iff.mp i.2)]
    rw [hsingle ⟨n + 1, by omega⟩] at hleft
    rw [hsingle ⟨n + 2, by omega⟩] at hright'
    intro i
    rcases Nat.lt_or_ge (i : ℕ) (n + 1) with hi | hi
    · exact hnode i (by omega)
    · rcases Nat.lt_or_ge (i : ℕ) (n + 2) with hi' | hi'
      · have hi1 : i = ⟨n + 1, by omega⟩ := Fin.ext (show (i : ℕ) = n + 1 by omega)
        rw [hi1]
        exact hleft
      · have hi2 : i = ⟨n + 2, by omega⟩ := Fin.ext (show (i : ℕ) = n + 2 by omega)
        rw [hi2]
        exact hright'
  have hcard : Fintype.card (Fin (n + 3)) = Module.finrank ℝ (definition_8_1 a b n x 3) := by
    rw [Fintype.card_fin, definition_8_1_finrank hx hn (by norm_num)]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i t => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-- **Section 8.6.1** of [quarteroni2000numerical], the clamped spline in the cardinal basis. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$. If $s_3$ is a cubic spline interpolating the
values $f_i$ with $s_3'(x_0) = f'_0$ and $s_3'(x_n) = f'_n$, then on $[a, b]$
$$s_3(x) = \sum_{i=0}^n f_i \varphi_i(x) + f'_0 \varphi_{n+1}(x) + f'_n \varphi_{n+2}(x).$$

The proof is `Spline.clampedInterp_eq_sum_cardinalBasis`. -/
theorem cardinalSplineBasis_clampedInterp (hs : IsCubicInterpSpline a b n x f s) {f'0 f'n : ℝ}
    (h0 : derivWithin s (Icc a b) a = f'0) (h1 : derivWithin s (Icc a b) b = f'n) :
    EqOn s (∑ i ∈ Finset.range (n + 1), f i • Spline.cardinalBasis n x i
        + f'0 • Spline.cardinalBasis n x (n + 1) + f'n • Spline.cardinalBasis n x (n + 2))
      (Icc a b) :=
  (hs.eqOn_clampedInterp hx hn h0 h1).trans
    (Spline.clampedInterp_eq_sum_cardinalBasis hn f f'0 f'n ▸ fun _ _ => rfl)

/-! ### Property 8.2: the minimum norm property -/

variable {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Icc a b))
include hF

/-- **Property 8.2** of [quarteroni2000numerical] (minimum norm property of Holladay). Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, and
let $s_3$ be the natural cubic spline interpolating $f$ at the nodes. Then
$$\int_a^b [s_3''(x)]^2 \, dx \le \int_a^b [f''(x)]^2 \, dx. \qquad (8.49)$$

The second derivatives are taken within $[a, b]$. The proof is
`Spline.integral_sq_deriv2_le_of_end`. It rests on the orthogonality
$\int_a^b (f'' - s_3'') s_3'' \, dx = 0$, obtained by integration by parts on every panel. -/
theorem property_8_2 (hs : IsCubicInterpSpline a b n x (fun i => F (x i)) s)
    (hnat : equation_8_45 a b 2 s) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 F (Icc a b) t ^ 2 :=
  Spline.integral_sq_deriv2_le_of_end hx hn hF hs (Or.inl ((equation_8_45_two_iff).mp hnat))

/-- **Property 8.2** of [quarteroni2000numerical], the equality case. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, and
let $s_3$ be the natural cubic spline interpolating $f$ at the nodes. Then equality holds in
(8.49) if and only if $f = s_3$ on $[a, b]$.

The forward direction is `Spline.eqOn_of_integral_sq_deriv2_eq`. The converse holds because the
second derivatives within $[a, b]$ of two functions that agree on $[a, b]$ agree. -/
theorem property_8_2_eq_iff (hs : IsCubicInterpSpline a b n x (fun i => F (x i)) s)
    (hnat : equation_8_45 a b 2 s) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      = ∫ t in a..b, iteratedDerivWithin 2 F (Icc a b) t ^ 2 ↔ EqOn F s (Icc a b) := by
  refine ⟨Spline.eqOn_of_integral_sq_deriv2_eq hx hn hF hs
    (Or.inl ((equation_8_45_two_iff).mp hnat)), fun heq => ?_⟩
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (hx.lt_of_pos hn).le] at ht
  rw [iteratedDerivWithin_congr heq ht]

/-- **Exercise 11 of Chapter 8** of [quarteroni2000numerical]. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, and
let $s$ be the cubic spline interpolating $f$ at the nodes with $s'(a) = f'(a)$ and
$s'(b) = f'(b)$. Then
$$\int_a^b [s''(x)]^2 \, dx \le \int_a^b [f''(x)]^2 \, dx.$$

This is Property 8.2 for the clamped spline. The integration by parts of the hint is
`Spline.integral_sub_deriv2_mul_deriv2_eq`, whose boundary terms $[(f' - s') s'']_a^b$ vanish
under the clamped conditions. -/
theorem exercise_8_11 (hs : IsCubicInterpSpline a b n x (fun i => F (x i)) s)
    (h0 : derivWithin s (Icc a b) a = derivWithin F (Icc a b) a)
    (h1 : derivWithin s (Icc a b) b = derivWithin F (Icc a b) b) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 F (Icc a b) t ^ 2 :=
  Spline.integral_sq_deriv2_le_of_end hx hn hF hs (Or.inr ⟨h0, h1⟩)

/-- **Exercise 11 of Chapter 8** of [quarteroni2000numerical], the equality case. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, and
let $s$ be the cubic spline interpolating $f$ at the nodes with $s'(a) = f'(a)$ and
$s'(b) = f'(b)$. Then equality holds in $\int_a^b [s'']^2 \le \int_a^b [f'']^2$ if and only if
$f = s$ on $[a, b]$. -/
theorem exercise_8_11_eq_iff (hs : IsCubicInterpSpline a b n x (fun i => F (x i)) s)
    (h0 : derivWithin s (Icc a b) a = derivWithin F (Icc a b) a)
    (h1 : derivWithin s (Icc a b) b = derivWithin F (Icc a b) b) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      = ∫ t in a..b, iteratedDerivWithin 2 F (Icc a b) t ^ 2 ↔ EqOn F s (Icc a b) := by
  refine ⟨Spline.eqOn_of_integral_sq_deriv2_eq hx hn hF hs (Or.inr ⟨h0, h1⟩), fun heq => ?_⟩
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (hx.lt_of_pos hn).le] at ht
  rw [iteratedDerivWithin_congr heq ht]

/-- **Section 8.6.1** of [quarteroni2000numerical], the best approximation property of the clamped
spline (the display after Property 8.2). Let $a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$,
let $f$ be of class $C^2$ on $[a, b]$, and let $s_f$ be the cubic spline interpolating $f$ at
the nodes with $s_f'(a) = f'(a)$ and $s_f'(b) = f'(b)$. Then for every $s \in \mathcal{S}_3$,
$$\int_a^b [f''(x) - s_f''(x)]^2 \, dx \le \int_a^b [f''(x) - s''(x)]^2 \, dx.$$

Here $s \in \mathcal{S}_3$ means `Spline.IsCubicSpline a b n x s` (see
`QuarteroniSaccoSaleri.Chapter08.mem_definition_8_1_three_iff`). The proof is
`Spline.integral_sq_sub_deriv2_clampedInterp_le` for $s_f$ = `Spline.clampedInterp`, which
agrees with every such $s_f$ on $[a, b]$.

**Reading.** The best approximation property is for the clamped interpolant of F with matching
boundary slopes. It minimizes squared second-derivative error over the entire cubic spline space on
that partition.
-/
theorem clampedSpline_bestApprox_deriv2 {sf : ℝ → ℝ}
    (hsf : IsCubicInterpSpline a b n x (fun i => F (x i)) sf)
    (h0 : derivWithin sf (Icc a b) a = derivWithin F (Icc a b) a)
    (h1 : derivWithin sf (Icc a b) b = derivWithin F (Icc a b) b)
    (hs : Spline.IsCubicSpline a b n x s) :
    ∫ t in a..b, (iteratedDerivWithin 2 F (Icc a b) t - iteratedDerivWithin 2 sf (Icc a b) t) ^ 2
      ≤ ∫ t in a..b,
          (iteratedDerivWithin 2 F (Icc a b) t - iteratedDerivWithin 2 s (Icc a b) t) ^ 2 := by
  have heq := hsf.eqOn_clampedInterp hx hn h0 h1
  have hcongr : ∀ t ∈ uIcc a b, (iteratedDerivWithin 2 F (Icc a b) t
      - iteratedDerivWithin 2 sf (Icc a b) t) ^ 2
      = (iteratedDerivWithin 2 F (Icc a b) t - iteratedDerivWithin 2 (Spline.clampedInterp n x
          (fun i => F (x i)) (derivWithin F (Icc a b) a) (derivWithin F (Icc a b) b))
            (Icc a b) t) ^ 2 := by
    intro t ht
    rw [uIcc_of_le (hx.lt_of_pos hn).le] at ht
    rw [iteratedDerivWithin_congr heq ht]
  rw [intervalIntegral.integral_congr hcongr]
  exact Spline.integral_sq_sub_deriv2_clampedInterp_le hx hn hF hs

end Cubic

/-! ### Property 8.3: the error of the clamped interpolatory cubic spline -/

/-- **Property 8.3** of [quarteroni2000numerical], with non-sharp constants. Let
$a = x_0 < x_1 < \cdots < x_n = b$ with $n \ge 1$, and let every panel have length at most $h$.
Let $f : \mathbb{R} \to \mathbb{R}$ be of class $C^4$ with $|f^{(4)}| \le K$ on $[a, b]$, and
let $s_3$ be the clamped cubic spline that interpolates $f$ at the nodes with $s_3'(a) = f'(a)$
and $s_3'(b) = f'(b)$. Then
$$|f(x) - s_3(x)| \le \tfrac{7}{8} h^4 K, \qquad |f'(x) - s_3'(x)| \le \tfrac{7}{4} h^3 K \qquad
  (x \in [a, b]),$$
$$|f''(x_i) - s_3''(x_i)| \le \tfrac{3}{4} h^2 K \qquad (i = 0, \ldots, n).$$

**Reading.** The source does not say which end conditions it means. The statement is about the
clamped spline. For the natural spline it is false unless $f''(a) = f''(b) = 0$: the natural
spline of $f(t) = t^2$ is not $t^2$, because a natural spline has $s''(a) = s''(b) = 0$, so the
left-hand side is positive while $f^{(4)} = 0$; near the ends the error of the natural spline is
only $O(h^2)$.

This is Property 8.3 for $r = 0, 1, 2$, with the constants $7/8$, $7/4$ and $3/4$ in place of
the sharp constants $5/384$, $1/24$ and $3/8$ of the book, and with the case $r = 2$ only at the
nodes. The sharp constants and the case $r = 3$ are not formalized; they are the constants of
Hall and Meyer for the clamped spline. Their proof writes the error on each panel through the
cubic Hermite interpolant of $f$ with the slopes $s_3'(x_i)$, bounds the slope errors through
the inverse $A^{-1}$ of the tridiagonal moment system, with $\|A^{-1}\|_\infty \le 1/2$ by
diagonal dominance, and uses the sharp Hermite constant $1/384$. The spline is
`Spline.clampedInterp`, and
`QuarteroniSaccoSaleri.Chapter08.IsCubicInterpSpline.eqOn_clampedInterp` identifies every
clamped interpolatory cubic spline with it on $[a, b]$. The proof uses
`Spline.norm_sub_clampedInterp_le`, `Spline.norm_deriv_sub_clampedInterp_le` and
`Spline.norm_deriv2_sub_clampedInterp_le`.

**Reading.** The interpolant is clamped and the function is globally four times continuously
differentiable. The theorem gives weaker constants for orders zero, one and two, evaluates order two
only at the nodes, and does not give the printed third-derivative estimate. The printed rates can
fail for natural end conditions, for instance for a quadratic with nonzero second derivative.
-/
theorem property_8_3_weak {f : ℝ → ℝ} {K hm : ℝ} (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (hf : ContDiff ℝ 4 f) (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    (hmesh : ∀ i, 1 ≤ i → i ≤ n → Spline.panelLength x i ≤ hm) :
    (∀ t ∈ Icc a b, |f t - Spline.clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) t|
        ≤ 7 / 8 * hm ^ 4 * K) ∧
      (∀ t ∈ Icc a b, |deriv f t
        - deriv (Spline.clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b)) t|
        ≤ 7 / 4 * hm ^ 3 * K) ∧
      (∀ i ≤ n, |iteratedDeriv 2 f (x i)
        - iteratedDeriv 2 (Spline.clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b))
            (x i)| ≤ 3 / 4 * hm ^ 2 * K) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun i hi => ?_⟩
  · rw [abs_sub_comm]
    exact Spline.norm_sub_clampedInterp_le hx hn hf hK hmesh ht
  · rw [abs_sub_comm]
    exact Spline.norm_deriv_sub_clampedInterp_le hx hn hf hK hmesh ht
  · rw [abs_sub_comm]
    exact Spline.norm_deriv2_sub_clampedInterp_le hx hn hf hK hmesh hi

/-! ### Section 8.6.2: B-splines -/

/-- **Definition 8.2** of [quarteroni2000numerical], the normalized B-spline. Let $x_0, x_1, \ldots$
be real numbers and $k, i \in \mathbb{N}$. The **normalized B-spline** $B_{i,k+1}$ of degree $k$
relative to the nodes $x_i, \ldots, x_{i+k+1}$ is
$$B_{i,k+1}(x) = (x_{i+k+1} - x_i) \, g[x_i, \ldots, x_{i+k+1}], \qquad (8.51)$$
where $g(t) = (t - x)_+^k$ (8.52) and $g[x_i, \ldots, x_{i+k+1}]$ is the Newton divided
difference of Section 8.2.

The book takes the nodes distinct. The truncated power $(t - x)_+^k$ is
`Quadrature.truncPow k t x`. The definition is the divided-difference form `BSpline.nform`, and
`QuarteroniSaccoSaleri.Chapter08.definition_8_2_eq_bspline` identifies it with the Cox–de Boor
B-spline `BSpline.bspline x k i`.

**Reading.** The nonconfluent divided-difference expression uses total division at repeated knots,
unlike the confluent extension in Remark 8.3. Its equivalence to the Cox–de Boor recursion is proved
for strictly increasing knots and positive degrees, where the degree-zero endpoint convention is
irrelevant.
-/
noncomputable def definition_8_2 (x : ℕ → ℝ) (k i : ℕ) : ℝ → ℝ :=
  BSpline.nform x k i

/-- **Definition 8.2** of [quarteroni2000numerical], the formulas (8.51)–(8.52). For all
$x_0, x_1, \ldots$, $k$, $i$ and $t$,
$$B_{i,k+1}(t) = (x_{i+k+1} - x_i) \, g[x_i, \ldots, x_{i+k+1}], \qquad g(s) = (s - t)_+^k,$$
with the Newton divided difference `DividedDifference.newton`.

**Reading.** The nonconfluent divided-difference expression uses total division at repeated knots,
unlike the confluent extension in Remark 8.3. Its equivalence to the Cox–de Boor recursion is proved
for strictly increasing knots and positive degrees, where the degree-zero endpoint convention is
irrelevant.
-/
theorem definition_8_2_apply (x : ℕ → ℝ) (k i : ℕ) (t : ℝ) :
    definition_8_2 x k i t = (x (i + k + 1) - x i) *
      DividedDifference.newton (fun s => Quadrature.truncPow k s t)
        fun j : Fin (k + 2) => x (i + j) :=
  rfl

/-- **Definition 8.2** of [quarteroni2000numerical], agreement with the recursion. Let
$x_0 < x_1 < \cdots$ be strictly increasing and let $k \ge 1$. Then the B-spline $B_{i,k+1}$ of
Definition 8.2 equals the B-spline `BSpline.bspline x k i` of the Cox–de Boor recursion (8.54).

For $k = 0$ the two differ at the knots: Definition 8.2 gives the indicator function of
$(x_i, x_{i+1}]$, and the recursion gives that of $[x_i, x_{i+1})$. The proof is
`BSpline.nform_eq_bspline`.

**Reading.** The nonconfluent divided-difference expression uses total division at repeated knots,
unlike the confluent extension in Remark 8.3. Its equivalence to the Cox–de Boor recursion is proved
for strictly increasing knots and positive degrees, where the degree-zero endpoint convention is
irrelevant.
-/
theorem definition_8_2_eq_bspline (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) :
    definition_8_2 x k i = BSpline.bspline x k i :=
  BSpline.nform_eq_bspline hx hk i

/-- **Equation (8.53)** of [quarteroni2000numerical], the explicit form. For all $x_0, x_1, \ldots$,
$k$, $i$ and $t$,
$$B_{i,k+1}(t) = (x_{i+k+1} - x_i) \sum_{j=0}^{k+1} \frac{(x_{i+j} - t)_+^k}{\prod_{l \neq j}
  (x_{i+j} - x_{i+l})},$$
where the product runs over $l \in \{0, \ldots, k + 1\}$, $l \neq j$.

The book obtains it by substituting (8.18) into (8.51). It is the definition of the divided
difference, unfolded. For coincident nodes a denominator is zero, and the division in Lean gives
$0$ for that term.

**Reading.** The nonconfluent divided-difference expression uses total division at repeated knots,
unlike the confluent extension in Remark 8.3. Its equivalence to the Cox–de Boor recursion is proved
for strictly increasing knots and positive degrees, where the degree-zero endpoint convention is
irrelevant.
-/
theorem equation_8_53 (x : ℕ → ℝ) (k i : ℕ) (t : ℝ) :
    definition_8_2 x k i t = (x (i + k + 1) - x i) * ∑ j : Fin (k + 2),
      Quadrature.truncPow k (x (i + j)) t / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)) :=
  rfl

/-- **Section 8.6.2** of [quarteroni2000numerical], the support. Let $x_0 \le x_1 \le \cdots$ be
nondecreasing. Then $B_{i,k+1}(t) = 0$ for $t \notin [x_i, x_{i+k+1}]$: "$B_{i,k+1}(x)$ is non
null only within the interval $[x_i, x_{i+k+1}]$".

The B-spline is `BSpline.bspline x k i`. The proof is `BSpline.bspline_eq_zero_of_notMem`, which
gives the smaller support $[x_i, x_{i+k+1})$.

**Reading.** Support and nonnegativity allow repeated knots in a monotone sequence. Strict
positivity uses distinct knots on the open support interval. Minimal support at positive degree
means uniqueness up to scalar, with smaller support forcing the zero spline.
-/
theorem bSpline_support (hx : Monotone x) {i : ℕ} {t : ℝ} (ht : t ∉ Icc (x i) (x (i + k + 1))) :
    BSpline.bspline x k i t = 0 :=
  BSpline.bspline_eq_zero_of_notMem hx fun h => ht (Ico_subset_Icc_self h)

/-- **Section 8.6.2** of [quarteroni2000numerical], positivity (quoted by the book from de Boor).
Let $x_0 \le x_1 \le \cdots$ be nondecreasing. Then $B_{i,k+1}(t) \ge 0$ for all $i$ and $t$.

The proof is `BSpline.bspline_nonneg`.

**Reading.** Support and nonnegativity allow repeated knots in a monotone sequence. Strict
positivity uses distinct knots on the open support interval. Minimal support at positive degree
means uniqueness up to scalar, with smaller support forcing the zero spline.
-/
theorem bSpline_nonneg (hx : Monotone x) (i : ℕ) (t : ℝ) : 0 ≤ BSpline.bspline x k i t :=
  BSpline.bspline_nonneg hx

/-- **Section 8.6.2** of [quarteroni2000numerical], positivity on the open support. Let
$x_0 < x_1 < \cdots$ be strictly increasing. Then $B_{i,k+1}(t) > 0$ for
$t \in (x_i, x_{i+k+1})$.

The proof is `BSpline.bspline_pos`.

**Reading.** Support and nonnegativity allow repeated knots in a monotone sequence. Strict
positivity uses distinct knots on the open support interval. Minimal support at positive degree
means uniqueness up to scalar, with smaller support forcing the zero spline.
-/
theorem bSpline_pos (hx : StrictMono x) {i : ℕ} {t : ℝ} (ht : t ∈ Ioo (x i) (x (i + k + 1))) :
    0 < BSpline.bspline x k i t :=
  BSpline.bspline_pos hx ht

/-- **Section 8.6.2** of [quarteroni2000numerical], minimal support (quoted by the book from
Schoenberg). Let $x_0 < x_1 < \cdots$ be strictly increasing, let $k \ge 1$, and let
$s : \mathbb{R} \to \mathbb{R}$ be of class $C^{k-1}$, zero outside $[x_i, x_{i+k+1}]$, and a
polynomial of degree at most $k$ on each $[x_j, x_{j+1}]$, $i \le j \le i + k$. Then
$s = c B_{i,k+1}$ for some $c \in \mathbb{R}$.

This is the first half of the statement that "$B_{i,k+1}$ is the unique non null spline of
minimum support relative to the nodes $x_i, \ldots, x_{i+k+1}$". The proof is
`BSpline.exists_eq_smul_bspline`: both $s$ and $B_{i,k+1}$ are combinations of the powers
$(x - x_j)^k$ whose jump coefficients lie in the kernel of
$c \mapsto \sum_{j=i}^{i+k+1} c_j (x - x_j)^k$, which has dimension one by a Vandermonde
argument.

**Reading.** Support and nonnegativity allow repeated knots in a monotone sequence. Strict
positivity uses distinct knots on the open support interval. Minimal support at positive degree
means uniqueness up to scalar, with smaller support forcing the zero spline.
-/
theorem bSpline_minimalSupport (hx : StrictMono x) (hk : 1 ≤ k) {i : ℕ} {s : ℝ → ℝ}
    (hs : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) s)
    (h0 : ∀ t ∉ Icc (x i) (x (i + k + 1)), s t = 0)
    (hp : ∀ j, i ≤ j → j ≤ i + k →
      ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn s p.eval (Icc (x j) (x (j + 1)))) :
    ∃ c : ℝ, s = c • BSpline.bspline x k i :=
  BSpline.exists_eq_smul_bspline hx hk hs h0 hp

/-- **Section 8.6.2** of [quarteroni2000numerical], minimality of the support. Let
$x_0 < x_1 < \cdots$ be strictly increasing, let $k \ge 1$, and let
$s : \mathbb{R} \to \mathbb{R}$ be of class $C^{k-1}$, zero outside $[x_i, x_{i+k}]$, and a
polynomial of degree at most $k$ on each $[x_j, x_{j+1}]$, $i \le j < i + k$. Then $s = 0$. So
no nonzero spline of degree $k$ has support in fewer than $k + 2$ consecutive nodes.

By `QuarteroniSaccoSaleri.Chapter08.bSpline_minimalSupport`, $s$ is a multiple of $B_{i,k+1}$,
and $B_{i,k+1}$ is positive on $(x_{i+k}, x_{i+k+1})$, where $s$ vanishes.

**Reading.** Support and nonnegativity allow repeated knots in a monotone sequence. Strict
positivity uses distinct knots on the open support interval. Minimal support at positive degree
means uniqueness up to scalar, with smaller support forcing the zero spline.
-/
theorem bSpline_minimalSupport_eq_zero (hx : StrictMono x) (hk : 1 ≤ k) {i : ℕ} {s : ℝ → ℝ}
    (hs : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) s)
    (h0 : ∀ t ∉ Icc (x i) (x (i + k)), s t = 0)
    (hp : ∀ j, i ≤ j → j < i + k →
      ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn s p.eval (Icc (x j) (x (j + 1)))) :
    s = 0 := by
  have hlt : x (i + k) < x (i + k + 1) := hx (Nat.lt_succ_self _)
  have h0' : ∀ t ∉ Icc (x i) (x (i + k + 1)), s t = 0 := fun t ht =>
    h0 t fun h => ht ⟨h.1, h.2.trans hlt.le⟩
  have hp' : ∀ j, i ≤ j → j ≤ i + k →
      ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn s p.eval (Icc (x j) (x (j + 1))) := by
    intro j hij hjk
    rcases Nat.lt_or_ge j (i + k) with h | h
    · exact hp j hij h
    · obtain rfl : j = i + k := by omega
      refine ⟨0, by simp, EqOn.of_subset_closure (s := Ioc (x (i + k)) (x (i + k + 1)))
        (fun t ht => ?_) hs.continuous.continuousOn (0 : ℝ[X]).continuous.continuousOn
        Ioc_subset_Icc_self (by rw [closure_Ioc hlt.ne])⟩
      rw [eval_zero]
      exact h0 t fun h' => absurd h'.2 (not_le.mpr ht.1)
  obtain ⟨c, hc⟩ := bSpline_minimalSupport hx hk hs h0' hp'
  set t := (x (i + k) + x (i + k + 1)) / 2 with ht
  have htm : t ∈ Ioo (x (i + k)) (x (i + k + 1)) := ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
  have hst : s t = 0 := h0 t fun h => absurd h.2 (not_le.mpr htm.1)
  have hpos : 0 < BSpline.bspline x k i t :=
    bSpline_pos hx ⟨(hx.monotone (Nat.le_add_right i k)).trans_lt htm.1, htm.2⟩
  have hc0 : c = 0 := by
    have := congrFun hc t
    rw [hst, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hpos.ne'
  rw [hc, hc0, zero_smul]

/-- **Equation (8.54)** of [quarteroni2000numerical], degree zero. For all $x_0, x_1, \ldots$, $i$
and $t$, $B_{i,1}(t) = 1$ if $t \in [x_i, x_{i+1})$ and $B_{i,1}(t) = 0$ otherwise.

**Reading.** The source prints the closed interval $[x_i, x_{i+1}]$. With the closed interval,
two consecutive B-splines of degree zero would both be $1$ at a shared knot, and the partition
of unity would fail. The half-open interval is used.

This is the definition `BSpline.bspline_zero`.

**Reading.** The zero-degree indicator is left-closed and right-open so neighboring panels do not
both count a shared endpoint. The recurrence for the divided-difference representation is identified
in positive degree on strictly increasing knots.
-/
theorem equation_8_54_zero (x : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    BSpline.bspline x 0 i t = if t ∈ Ico (x i) (x (i + 1)) then 1 else 0 :=
  BSpline.bspline_zero x i t

/-- **Equation (8.54)** of [quarteroni2000numerical], the Cox–de Boor recursion. Let
$x_0 < x_1 < \cdots$ be strictly increasing and $k \in \mathbb{N}$. Then for all $i$ and $t$,
$$B_{i,k+2}(t) = \frac{t - x_i}{x_{i+k+1} - x_i} B_{i,k+1}(t) + \frac{x_{i+k+2} - t}{x_{i+k+2} -
  x_{i+1}} B_{i+1,k+1}(t).$$

This is the second line of (8.54) for the degree $k + 1$; the index $k \ge 1$ of the book is the
order. The proof is `BSpline.bspline_succ`, whose weights `BSpline.weight` are the displayed
quotients when the knots are distinct.

**Reading.** The zero-degree indicator is left-closed and right-open so neighboring panels do not
both count a shared endpoint. The recurrence for the divided-difference representation is identified
in positive degree on strictly increasing knots.
-/
theorem equation_8_54 (hx : StrictMono x) (k i : ℕ) (t : ℝ) :
    BSpline.bspline x (k + 1) i t
      = (t - x i) / (x (i + k + 1) - x i) * BSpline.bspline x k i t
        + (x (i + k + 2) - t) / (x (i + k + 2) - x (i + 1)) * BSpline.bspline x k (i + 1) t := by
  rw [BSpline.bspline_succ]
  simp only [BSpline.weight]
  have h1 : x (i + (k + 1)) ≠ x i := (hx (by omega : i < i + (k + 1))).ne'
  have h2 : x (i + 1 + (k + 1)) ≠ x (i + 1) := (hx (by omega : i + 1 < i + 1 + (k + 1))).ne'
  rw [ite_eq_right h1, ite_eq_right h2, show i + (k + 1) = i + k + 1 by omega,
    show i + 1 + (k + 1) = i + k + 2 by omega]
  have h2' : x (i + k + 2) - x (i + 1) ≠ 0 := by
    rw [show i + k + 2 = i + 1 + (k + 1) by omega]
    exact sub_ne_zero.mpr h2
  have h3 : 1 - (t - x (i + 1)) / (x (i + k + 2) - x (i + 1))
      = (x (i + k + 2) - t) / (x (i + k + 2) - x (i + 1)) := by
    field_simp
    ring
  rw [h3]

/-- **Equation (8.54)** of [quarteroni2000numerical], for the B-splines of Definition 8.2. Let
$x_0 < x_1 < \cdots$ be strictly increasing and $k \ge 1$. Then the B-splines of Definition 8.2
satisfy the Cox–de Boor recursion: for all $i$ and $t$,
$$B_{i,k+2}(t) = \frac{t - x_i}{x_{i+k+1} - x_i} B_{i,k+1}(t) + \frac{x_{i+k+2} - t}{x_{i+k+2} -
  x_{i+1}} B_{i+1,k+1}(t).$$

The book says that the recursion "is usually preferred to (8.53) when evaluating a B-spline".

**Reading.** The zero-degree indicator is left-closed and right-open so neighboring panels do not
both count a shared endpoint. The recurrence for the divided-difference representation is identified
in positive degree on strictly increasing knots.
-/
theorem equation_8_54_definition_8_2 (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) (t : ℝ) :
    definition_8_2 x (k + 1) i t
      = (t - x i) / (x (i + k + 1) - x i) * definition_8_2 x k i t
        + (x (i + k + 2) - t) / (x (i + k + 2) - x (i + 1)) * definition_8_2 x k (i + 1) t := by
  rw [definition_8_2_eq_bspline hx (by omega), definition_8_2_eq_bspline hx hk,
    definition_8_2_eq_bspline hx hk]
  exact equation_8_54 hx k i t

/-- **Remark 8.3** of [quarteroni2000numerical], divided differences at coincident nodes. Let
$f : \mathbb{R} \to \mathbb{R}$ and let $x_0 \le x_1 \le \cdots \le x_n$. The **confluent
divided difference** $f[x_0, \ldots, x_n]$ is defined by the recursion
$$f[x_0, \ldots, x_n] = \frac{f[x_1, \ldots, x_n] - f[x_0, \ldots, x_{n-1}]}{x_n - x_0} \quad
  \text{if } x_0 < x_n, \qquad f[x_0, \ldots, x_n] = \frac{f^{(n)}(x_0)}{n!} \quad \text{if }
  x_0 = x_1 = \cdots = x_n.$$

**Typo.** The source prints $f^{(n+1)}(x_0)/(n+1)!$ in the second case. The value is
$f^{(n)}(x_0)/n!$; for example $f[x_0, x_0] = f'(x_0)$.

The definition is `DividedDifference.confluent`. It applies to every family of nodes
$x_0, \ldots, x_n$: $f[x_0] = f(x_0)$, and for $n \ge 1$ the derivative value is used whenever
$x_0 = x_n$ and the quotient otherwise. For nondecreasing nodes, $x_0 = x_n$ means that all
nodes coincide.

**Correction.** For m+1 equal nodes the value uses the derivative of order m divided by m factorial.
The source prints derivative and factorial one order too high. The equivalence with the raw formula
is stated for distinct nodes.
-/
noncomputable def remark_8_3_confluent (f : ℝ → ℝ) {m : ℕ} (v : Fin (m + 1) → ℝ) : ℝ :=
  DividedDifference.confluent f v

/-- **Remark 8.3** of [quarteroni2000numerical], the recursion. Let $f : \mathbb{R} \to \mathbb{R}$
and let $v_0, \ldots, v_{m+1}$ be nodes with $v_0 < v_{m+1}$. Then
$$f[v_0, \ldots, v_{m+1}] = \frac{f[v_1, \ldots, v_{m+1}] - f[v_0, \ldots, v_m]}{v_{m+1} -
  v_0}.$$

**Correction.** For m+1 equal nodes the value uses the derivative of order m divided by m factorial.
The source prints derivative and factorial one order too high. The equivalence with the raw formula
is stated for distinct nodes.
-/
theorem remark_8_3_confluent_of_lt (f : ℝ → ℝ) {m : ℕ} {v : Fin (m + 2) → ℝ}
    (h : v 0 < v (Fin.last (m + 1))) :
    remark_8_3_confluent f v
      = (remark_8_3_confluent f (Fin.tail v) - remark_8_3_confluent f (Fin.init v))
        / (v (Fin.last (m + 1)) - v 0) := by
  rw [remark_8_3_confluent, DividedDifference.confluent_succ, ite_eq_right h.ne]
  rfl

/-- **Remark 8.3** of [quarteroni2000numerical], coincident nodes. Let
$f : \mathbb{R} \to \mathbb{R}$, $m \in \mathbb{N}$ and $x_0 \in \mathbb{R}$. At $m + 1$ copies
of the node $x_0$,
$$f[x_0, \ldots, x_0] = \frac{f^{(m)}(x_0)}{m!}.$$

The proof is `DividedDifference.confluent_const`.

**Correction.** For m+1 equal nodes the value uses the derivative of order m divided by m factorial.
The source prints derivative and factorial one order too high. The equivalence with the raw formula
is stated for distinct nodes.
-/
theorem remark_8_3_confluent_const (f : ℝ → ℝ) (m : ℕ) (x₀ : ℝ) :
    remark_8_3_confluent f (fun _ : Fin (m + 1) => x₀) = iteratedDeriv m f x₀ / m.factorial :=
  DividedDifference.confluent_const f x₀

/-- **Remark 8.3** of [quarteroni2000numerical], distinct nodes. Let $f : \mathbb{R} \to \mathbb{R}$
and let $v_0, \ldots, v_m$ be distinct nodes. Then the confluent divided difference
$f[v_0, \ldots, v_m]$ is the Newton divided difference of Section 8.2.

The proof is `DividedDifference.confluent_eq_newton`.

**Correction.** For m+1 equal nodes the value uses the derivative of order m divided by m factorial.
The source prints derivative and factorial one order too high. The equivalence with the raw formula
is stated for distinct nodes.
-/
theorem remark_8_3_confluent_eq (f : ℝ → ℝ) {m : ℕ} {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) : remark_8_3_confluent f v = DividedDifference.newton f v :=
  DividedDifference.confluent_eq_newton f hv

/-- **Remark 8.3** of [quarteroni2000numerical], $k + 1$ coincident knots at the left. Let
$x_i = x_{i+1} = \cdots = x_{i+k} < x_{i+k+1}$. Then
$$B_{i,k+1}(t) = \left( \frac{x_{i+k+1} - t}{x_{i+k+1} - x_i} \right)^k \quad \text{for } t \in
  [x_i, x_{i+k+1}),$$
and $B_{i,k+1}(t) = 0$ otherwise.

**Generalization.** The source also assumes $x_{i-1} < x_i$, which is not needed. The source
prints the closed interval $[x_i, x_{i+k+1}]$; the formula gives $0$ at the right end anyway.

The proof is `BSpline.bspline_apply_of_coincident_left`.

**Generalization.** The neighboring exterior strict inequalities are omitted. The formula is given
on a half-open support, so the right-repeated case uses zero at the right endpoint instead of its
left-hand limit.
-/
theorem remark_8_3_left {i : ℕ} (hcoin : ∀ j, i ≤ j → j ≤ i + k → x j = x i)
    (hlt : x i < x (i + k + 1)) (t : ℝ) :
    BSpline.bspline x k i t = if t ∈ Ico (x i) (x (i + k + 1)) then
      ((x (i + k + 1) - t) / (x (i + k + 1) - x i)) ^ k else 0 :=
  BSpline.bspline_apply_of_coincident_left hcoin hlt t

/-- **Remark 8.3** of [quarteroni2000numerical], $k + 1$ coincident knots at the right. Let
$x_0 \le x_1 \le \cdots$ be nondecreasing with $x_i < x_{i+1} = \cdots = x_{i+k+1}$. Then
$$B_{i,k+1}(t) = \left( \frac{t - x_i}{x_{i+k+1} - x_i} \right)^k \quad \text{for } t \in [x_i,
  x_{i+k+1}),$$
and $B_{i,k+1}(t) = 0$ otherwise.

**Generalization.** The source also assumes $x_{i+k+1} < x_{i+k+2}$, which is not needed.

The proof is `BSpline.bspline_apply_of_coincident_right`.

**Generalization.** The neighboring exterior strict inequalities are omitted. The formula is given
on a half-open support, so the right-repeated case uses zero at the right endpoint instead of its
left-hand limit.
-/
theorem remark_8_3_right (hx : Monotone x) {i : ℕ}
    (hcoin : ∀ j, i + 1 ≤ j → j ≤ i + k + 1 → x j = x (i + k + 1)) (hlt : x i < x (i + k + 1))
    (t : ℝ) :
    BSpline.bspline x k i t = if t ∈ Ico (x i) (x (i + k + 1)) then
      ((t - x i) / (x (i + k + 1) - x i)) ^ k else 0 :=
  BSpline.bspline_apply_of_coincident_right hx hcoin hlt t

/-- **Example 8.9** of [quarteroni2000numerical], the cubic B-spline on equally spaced knots. Let
$h > 0$ and $x_j = x_0 + jh$ for all $j$. Then $6 h^3 B_{i,4}(t)$ equals
* $(t - x_i)^3$ for $t \in [x_i, x_{i+1})$;
* $h^3 + 3h^2 (t - x_{i+1}) + 3h (t - x_{i+1})^2 - 3 (t - x_{i+1})^3$ for
  $t \in [x_{i+1}, x_{i+2})$;
* $h^3 + 3h^2 (x_{i+3} - t) + 3h (x_{i+3} - t)^2 - 3 (x_{i+3} - t)^3$ for
  $t \in [x_{i+2}, x_{i+3})$;
* $(x_{i+4} - t)^3$ for $t \in [x_{i+3}, x_{i+4})$;
* $0$ otherwise.

The proof is `BSpline.bspline_uniform_cubic`.

**Reading.** The branches use half-open intervals to make a single-valued case split. The adjacent
polynomial formulas agree at the knots and the value at the rightmost knot is zero.
-/
theorem example_8_9 {x₀ h : ℝ} (hh : 0 < h) (hx : ∀ j, x j = x₀ + j * h) (i : ℕ) (t : ℝ) :
    6 * h ^ 3 * BSpline.bspline x 3 i t =
      if t ∈ Ico (x i) (x (i + 1)) then (t - x i) ^ 3
      else if t ∈ Ico (x (i + 1)) (x (i + 2)) then
        h ^ 3 + 3 * h ^ 2 * (t - x (i + 1)) + 3 * h * (t - x (i + 1)) ^ 2 - 3 * (t - x (i + 1)) ^ 3
      else if t ∈ Ico (x (i + 2)) (x (i + 3)) then
        h ^ 3 + 3 * h ^ 2 * (x (i + 3) - t) + 3 * h * (x (i + 3) - t) ^ 2 - 3 * (x (i + 3) - t) ^ 3
      else if t ∈ Ico (x (i + 3)) (x (i + 4)) then (x (i + 4) - t) ^ 3 else 0 :=
  BSpline.bspline_uniform_cubic hh hx i t

/-- **Equations (8.55)–(8.56)** of [quarteroni2000numerical], the B-spline basis of $\mathcal{S}_k$.
Let $n, k \ge 1$, and let $x_0 < x_1 < \cdots$ be strictly increasing knots with $x_k = a$ and
$x_{n+k} = b$. Then the $n + k$ B-splines $B_{i,k+1}$, $i = 0, \ldots, n + k - 1$, restricted to
$[a, b]$, form a basis of the space $\mathcal{S}_k$ on the nodes
$a = x_k < \cdots < x_{n+k} = b$. So every $s_k \in \mathcal{S}_k$ can be written uniquely as
$s_k = \sum_i c_i B_{i,k+1}$ (8.56), where the $c_i$ are its B-spline coefficients.

**Reading.** The source adds $2k$ fictitious nodes $x_{-k} \le \cdots \le x_{-1} \le x_0 = a$
and $b = x_n \le x_{n+1} \le \cdots \le x_{n+k}$ (8.55), which may coincide. Here they are
strictly increasing. The case of coincident fictitious knots appears in (8.57).

In the shifted indexing the knots $x_0, \ldots, x_{k-1}$ are the fictitious knots
$x_{-k}, \ldots, x_{-1}$ of the book, and the index $i$ is the book's $i - k$, so the book's sum
runs over $i = -k, \ldots, n - 1$. The coefficients are
`QuarteroniSaccoSaleri.Chapter08.equation_8_56_repr`. The proof is
`BSpline.exists_basis_bspline`.

**Reading.** The basis and expansion assume all extended knots are strictly increasing, while the
text also permits repeating artificial knots. Indices are shifted by k so that the first B-spline
has index zero.
-/
theorem equation_8_56 (hx : StrictMono x) (hn : 1 ≤ n) (hk : 1 ≤ k) (hxa : x k = a)
    (hxb : x (n + k) = b) :
    ∃ B : Module.Basis (Fin (n + k)) ℝ (definition_8_1 a b n (fun j => x (j + k)) k),
      ∀ (i : Fin (n + k)) (t : Icc a b), (B i : C(Icc a b, ℝ)) t = BSpline.bspline x k i t := by
  subst hxa hxb
  exact BSpline.exists_basis_bspline hx hn hk

/-- **Equation (8.56)** of [quarteroni2000numerical], the B-spline coefficients. Let $n, k \ge 1$,
and let $x_0 < x_1 < \cdots$ be strictly increasing knots with $x_k = a$ and $x_{n+k} = b$. Then
every $s_k$ in the space $\mathcal{S}_k$ on the nodes $x_k < \cdots < x_{n+k}$ has unique
coefficients $c_0, \ldots, c_{n+k-1}$ with
$$s_k(t) = \sum_{i=0}^{n+k-1} c_i B_{i,k+1}(t), \qquad t \in [a, b].$$

**Reading.** The basis and expansion assume all extended knots are strictly increasing, while the
text also permits repeating artificial knots. Indices are shifted by k so that the first B-spline
has index zero.
-/
theorem equation_8_56_repr (hx : StrictMono x) (hn : 1 ≤ n) (hk : 1 ≤ k) (hxa : x k = a)
    (hxb : x (n + k) = b) (v : C(Icc a b, ℝ))
    (hv : v ∈ definition_8_1 a b n (fun j => x (j + k)) k) :
    ∃! c : Fin (n + k) → ℝ, ∀ t : Icc a b, v t = ∑ i, c i * BSpline.bspline x k i t := by
  obtain ⟨B, hB⟩ := equation_8_56 hx hn hk hxa hxb
  have hval : ∀ (c : Fin (n + k) → ℝ) (t : Icc a b),
      ((∑ i, c i • B i : definition_8_1 a b n (fun j => x (j + k)) k) : C(Icc a b, ℝ)) t
        = ∑ i, c i * BSpline.bspline x k i t := by
    intro c t
    simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, hB]
  refine ⟨B.repr ⟨v, hv⟩, fun t => ?_, fun c hc => ?_⟩
  · have := hval (B.repr ⟨v, hv⟩) t
    rwa [B.sum_repr ⟨v, hv⟩] at this
  · have hsum : ∑ i, c i • B i = ⟨v, hv⟩ := by
      ext t
      rw [hval]
      exact (hc t).symm
    rw [← hsum, B.repr_sum_self]

/-- **Equation (8.57)** of [quarteroni2000numerical], the left endpoint. Let
$x_0 \le x_1 \le \cdots$ be nondecreasing with $n \ge 1$, $x_0 = \cdots = x_k$ and
$x_k < x_{k+1}$, and let $c_0, c_1, \ldots$ be real numbers. Then
$s_k = \sum_{i=0}^{n+k-1} c_i B_{i,k+1}$ satisfies $s_k(x_k) = c_0$.

In the indexing of the book the hypothesis is $x_{-k} = \cdots = x_0 = a$, and the conclusion is
$s_k(a) = c_{-k}$. The proof is `BSpline.sum_smul_bspline_left`.

**Reading.** The repeated left endpoint has the first coefficient as its value. At the repeated
right endpoint the half-open B-splines vanish, so the last coefficient is obtained as the one-sided
limit from inside the interval.
-/
theorem equation_8_57 (hx : Monotone x) (hn : 1 ≤ n) (hcoin : ∀ j ≤ k, x j = x k)
    (hlt : x k < x (k + 1)) (c : ℕ → ℝ) :
    ∑ i ∈ Finset.range (n + k), c i * BSpline.bspline x k i (x k) = c 0 :=
  BSpline.sum_smul_bspline_left hx hn hcoin hlt c

/-- **Equation (8.57)** of [quarteroni2000numerical], the right endpoint. Let
$x_0 \le x_1 \le \cdots$ be nondecreasing with $n \ge 1$, $x_{n+k-1} < x_{n+k}$ and
$x_{n+k} = \cdots = x_{n+2k}$, and let $c_0, c_1, \ldots$ be real numbers. Then
$s_k = \sum_{i=0}^{n+k-1} c_i B_{i,k+1}$ satisfies
$$\lim_{t \to x_{n+k}^-} s_k(t) = c_{n+k-1}.$$

**Reading.** The source states $s_k(b) = c_{n-1}$. With the half-open convention of (8.54),
every B-spline vanishes at $b$, so the value at $b$ is read as the limit from the left.

In the indexing of the book the hypothesis is $x_n = \cdots = x_{n+k} = b$, and $c_{n+k-1}$ here
is the book's $c_{n-1}$. The proof is `BSpline.sum_smul_bspline_right`.

**Reading.** The repeated left endpoint has the first coefficient as its value. At the repeated
right endpoint the half-open B-splines vanish, so the last coefficient is obtained as the one-sided
limit from inside the interval.
-/
theorem equation_8_57_right (hx : Monotone x) (hn : 1 ≤ n)
    (hcoin : ∀ j, n + k ≤ j → j ≤ n + 2 * k → x j = x (n + k)) (hlt : x (n + k - 1) < x (n + k))
    (c : ℕ → ℝ) :
    Tendsto (fun t => ∑ i ∈ Finset.range (n + k), c i * BSpline.bspline x k i t)
      (𝓝[<] x (n + k)) (𝓝 (c (n + k - 1))) :=
  BSpline.sum_smul_bspline_right hx hn hcoin hlt c

/-- **Remark 8.4** of [quarteroni2000numerical] (knot insertion of Boehm). Let $x_0 < x_1 < \cdots$
be strictly increasing, let $k \ge 1$, let $k \le j < n + k$, and let
$\tilde x \in (x_j, x_{j+1})$. Let $\tilde x_0, \tilde x_1, \ldots$ be the knot sequence with
$\tilde x$ inserted after $x_j$, and let $\tilde B_{i,k+1}$ be its B-splines. Let
$c_0, c_1, \ldots$ be real numbers. Then for every $t$,
$$\sum_{i=0}^{n+k} d_i \tilde B_{i,k+1}(t) = \sum_{i=0}^{n+k-1} c_i B_{i,k+1}(t),$$
where $d_i = \omega_i c_i + (1 - \omega_i) c_{i-1}$ with $\omega_i = 1$ for $i + k \le j$,
$\omega_i = (\tilde x - x_i)/(x_{i+k} - x_i)$ for $j - k < i \le j$, and $\omega_i = 0$ for
$i > j$.

**Typo.** The source prints $c_i$ in both places of the formula for $d_i$. The second
coefficient is $c_{i-1}$.

**Reading.** The source allows $\tilde x \in [x_j, x_{j+1})$. Here the knots are strictly
increasing and $\tilde x$ lies in the open panel, because the case $\tilde x = x_j$ creates a
double knot, for which the divided-difference proof of `BSpline.bspline_eq_insert_comb` does not
apply. The condition $k \le j < n + k$ says that the new knot falls in a panel of the data
range; this makes the two end coefficients right.

The refined knots are `BSpline.insertKnot x j xt`, and the coefficients $d_i$ are
`BSpline.insertKnotCoeff x k j xt c i`. The proof is `BSpline.sum_smul_bspline_insertKnot`.

**Correction.** The second coefficient in the refinement formula is the preceding old coefficient.
The refined sum also has one more term. The theorem handles insertion strictly inside a panel of
strictly increasing knots.
-/
theorem remark_8_4 (hx : StrictMono x) (hk : 1 ≤ k) {j : ℕ} (hkj : k ≤ j) (hjn : j < n + k)
    {xt : ℝ} (hxt : xt ∈ Ioo (x j) (x (j + 1))) (c : ℕ → ℝ) (t : ℝ) :
    ∑ i ∈ Finset.range (n + k + 1),
        BSpline.insertKnotCoeff x k j xt c i * BSpline.bspline (BSpline.insertKnot x j xt) k i t
      = ∑ i ∈ Finset.range (n + k), c i * BSpline.bspline x k i t :=
  BSpline.sum_smul_bspline_insertKnot hx hk hxt hkj hjn c t

end QuarteroniSaccoSaleri.Chapter08
