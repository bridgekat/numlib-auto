/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 10.7: Approximation of a function in the least-squares sense

This module formalizes Section 10.7 of [quarteroni2000numerical]. For a weight $w$ and
$f \in L^2_w$, the **least-squares polynomial** $r_n \in \mathbb{P}_n$ minimizes $\|f - p_n\|_w$
over $\mathbb{P}_n$; it is the truncation $f_n$ of the generalized Fourier series of Section 10.1.
The discrete truncation $f_n^*$, computed with the discrete scalar product of a Gauss–Lobatto rule,
is the interpolant at the Gauss–Lobatto nodes, so $\|f - f_n^*\|_n = 0$.

Section 10.7.1 treats discrete least squares. For $m + 1$ data $(x_i, y_i)$ with distinct abscissae
and weights $w_j > 0$, the polynomial $p_n \in \mathbb{P}_n$, $n \le m$, that minimizes
$\sum_j w_j |p_n(x_j) - y_j|^2$ (10.44) exists and is unique; for $n = m$ it is the interpolant. The
reason is that $|||q||| = (\sum_j w_j q(x_j)^2)^{1/2}$ (10.45) is an essentially strict seminorm
(Exercise 10.7). If $p_n = \sum_j a_j \varphi_j$ in a basis of $\mathbb{P}_n$, the coefficients
solve the normal equations $B^T W B a = B^T W y$ (10.46) with $b_{ij} = \varphi_j(x_i)$. For $n = 1$
(linear regression) the coefficients have a closed form. The proofs specialize
`OrthogonalPolynomial.isBestApprox_truncation` and the best-approximation theory of
`Numlib.Analysis.Normed.Module.BestApprox`.

## Main definitions

* Equations (10.43)–(10.44), `QuarteroniSaccoSaleri.Chapter10.IsDiscreteLeastSquares`: $p$ is a
  discrete least-squares polynomial of degree at most $n$ for the data $(x_i, y_i)$ and the weights
  $w_j$.
* Section 10.7.1, `QuarteroniSaccoSaleri.Chapter10.weightedEval` and
  `QuarteroniSaccoSaleri.Chapter10.weightedData`: the map $q \mapsto (\sqrt{w_j} q(x_j))_j$ and the
  vector $(\sqrt{w_j} y_j)_j$ of $\mathbb{R}^{m+1}$, which turn the discrete problem into a
  Euclidean best-approximation problem.

## Main results

* Section 10.7, `QuarteroniSaccoSaleri.Chapter10.leastSquaresPolynomial_isBestApprox`: the
  least-squares polynomial exists, is unique, and is the truncation $f_n$ of (10.2).
* Section 10.7, `QuarteroniSaccoSaleri.Chapter10.discreteTruncation_eq_interpolate`: for the
  discrete scalar product of a Gauss–Lobatto rule, the discrete truncation is the interpolant at the
  nodes, and $\|f - f_n^*\|_n = 0$.
* Equations (10.43)–(10.44), `QuarteroniSaccoSaleri.Chapter10.equation_10_44`: the discrete
  least-squares polynomial exists and is unique, and for $n = m$ it is the interpolating polynomial.
* Equation (10.45) and Exercise 10.7, `QuarteroniSaccoSaleri.Chapter10.exercise_10_7`: (10.45) is a
  seminorm on the polynomials, a norm on $\mathbb{P}_n$ for $n \le m$, and essentially strict.
* Section 10.7.1, `QuarteroniSaccoSaleri.Chapter10.isDiscreteLeastSquares_sum_iff`: the normal
  equations in summed form.
* Equation (10.46), `QuarteroniSaccoSaleri.Chapter10.equation_10_46`: the normal equations in matrix
  form $B^T W B a = B^T W y$.
* Section 10.7.1, `QuarteroniSaccoSaleri.Chapter10.linearRegression_coeff`: the closed-form
  coefficients of the regression line.

## Conventions

* The data are `x y : Fin (m + 1) → ℝ` with `Function.Injective x`, and the weights are
  `w : Fin (m + 1) → ℝ` with `∀ j, 0 < w j`.
* The space $\mathbb{P}_n$ is the set of real polynomials of degree at most $n$. A basis of it is a
  linearly independent family `φ : Fin (n + 1) → ℝ[X]` of polynomials of degree at most $n$.
* The seminorm (10.45) is `QuarteroniSaccoSaleri.Chapter10.discreteNorm w x` of Section 10.1,
  applied to the polynomial function.
* In the linear regression, the data are the values $y_j = Y(x_j)$ of a function $Y$, as the book
  stipulates.

## Implementation notes

* The weighted evaluation map $q \mapsto (\sqrt{w_j} q(x_j))_j$ turns (10.44) into the problem of
  the distance from $(\sqrt{w_j} y_j)_j$ to the image of $\mathbb{P}_n$, a finite-dimensional
  subspace of $\mathbb{R}^{m+1}$. There best approximations exist, are unique, and are characterized
  by the normal equations `isBestApprox_sum_iff`.
* The essentially strict property is the equality case of the triangle inequality in a strictly
  convex space (`sameRay_iff_norm_add`).

## Deviations from the source

* **Equation (10.46)** (generalization). The book prints $B^T B a = B^T y$, which omits the weight
  matrix that its display before (10.46) carries. The library states $B^T W B a = B^T W y$ with
  $W = \operatorname{diag}(w_j)$; the printed form is the case $w_j = 1$. See
  `QuarteroniSaccoSaleri.Chapter10.equation_10_46`.
* **Exercise 10.7, essential strictness** (reading). The book asks for "nonnull $\alpha, \beta$".
  The library reads this as $(\alpha, \beta) \neq (0, 0)$, because when $f$ vanishes at all the
  nodes the pair $(1, 0)$ is the only choice. See `QuarteroniSaccoSaleri.Chapter10.exercise_10_7`.
* **Section 10.7.1, linear regression** (generalization). The book defines the discrete scalar
  product $(f, g)_m$ without the weights $w_j$. The library includes the weights, as the system that
  the formulas solve does; the printed form is the case $w_j = 1$. See
  `QuarteroniSaccoSaleri.Chapter10.linearRegression_coeff`.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {μ : Measure ℝ} {n : ℕ}

/-! ### The continuous least-squares polynomial -/

/-- **Section 10.7** of [quarteroni2000numerical], the least-squares polynomial. Let $\mu$ be a
weight and $f \in L^2_w$. There is a unique $r_n \in \mathbb{P}_n$ with
$$\|f - r_n\|_w = \min_{p_n \in \mathbb{P}_n} \|f - p_n\|_w,$$
and it is the truncation $f_n$ of order $n$ of the generalized Fourier series of $f$,
(10.2)–(10.3).

The space $\mathbb{P}_n$ is its image in `Lp ℝ 2 μ`, and the minimum is `IsBestApprox`.
Existence and the identification are `QuarteroniSaccoSaleri.Chapter10.equation_10_3`. Uniqueness
is `IsBestApprox.unique`, because $L^2_w$ is strictly convex. -/
theorem leastSquaresPolynomial_isBestApprox (hw : IsWeight μ) (n : ℕ) (f : Lp ℝ 2 μ) :
    (∃! r, IsBestApprox ((degreeLE ℝ n).map hw.toLpₗ : Set (Lp ℝ 2 μ)) f r) ∧
      ∀ r, IsBestApprox ((degreeLE ℝ n).map hw.toLpₗ : Set (Lp ℝ 2 μ)) f r →
        r = truncation hw n f := by
  have hbest : IsBestApprox ((degreeLE ℝ n).map hw.toLpₗ : Set (Lp ℝ 2 μ)) f
      (truncation hw n f) := by
    rw [truncation_eq]
    exact isBestApprox_truncation hw n f
  have huniq : ∀ r, IsBestApprox ((degreeLE ℝ n).map hw.toLpₗ : Set (Lp ℝ 2 μ)) f r →
      r = truncation hw n f := fun r hr =>
    hr.unique (Submodule.convex _) hbest
  exact ⟨⟨_, hbest, huniq⟩, huniq⟩

/-- **Section 10.7** of [quarteroni2000numerical], the discrete truncation is the Gauss–Lobatto
interpolant. Let $\mu$ be a weight and $n \ge 1$, and let a rule have $n + 1$ distinct nodes
$x_i$, positive weights and degree of exactness $2n - 1$, as the Gauss–Lobatto rule of
`QuarteroniSaccoSaleri.Chapter10.equation_10_18` does. If the discrete scalar product of this
rule is used in (10.5), then for every $f$ the discrete truncation $f_n^*$ of (10.4) equals the
interpolating polynomial $\Pi^{GL}_{n,w} f$ at the nodes, and
$$\|f - f_n^*\|_n = 0.$$
So (10.6) holds trivially.

The Chebyshev case is (10.29) and the Legendre case is (10.38). The proof specializes
`Quadrature.interpolate_eq_sum_discreteInner_smul`. -/
theorem discreteTruncation_eq_interpolate (hw : IsWeight μ) (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) {w : Fin (n + 1) → ℝ} (hwpos : ∀ i, 0 < w i)
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) (f : ℝ → ℝ) :
    discreteTruncation μ w x n f = Lagrange.interpolate Finset.univ x (fun i => f (x i)) ∧
      discreteNorm w x (f - fun t => (discreteTruncation μ w x n f).eval t) = 0 := by
  have hinterp : discreteTruncation μ w x n f =
      Lagrange.interpolate Finset.univ x fun i => f (x i) :=
    (interpolate_eq_sum_discreteInner_smul hw hn hx hwpos hexact f).symm
  refine ⟨hinterp, ?_⟩
  rw [discreteNorm, Real.sqrt_eq_zero', discreteInner]
  refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
  rw [hinterp, Pi.sub_apply, Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ i),
    sub_self, mul_zero]

/-! ### Section 10.7.1: Discrete least-squares approximation -/

section Discrete

variable {m : ℕ} {x y w : Fin (m + 1) → ℝ}

/-- **Equations (10.43)–(10.44)** of [quarteroni2000numerical], the discrete least-squares
polynomial. Given $m + 1$ pairs of data $(x_i, y_i)$ and weights $w_j$, a polynomial $p_n$ is a
**discrete least-squares polynomial** of degree at most $n$ if $p_n \in \mathbb{P}_n$ and
$$\sum_j w_j |p_n(x_j) - y_j|^2 \le \sum_j w_j |q_n(x_j) - y_j|^2 \quad \text{for all } q_n \in
  \mathbb{P}_n. \tag{10.44}$$

The definition does not require $w_j > 0$; the theorems below assume it. -/
def IsDiscreteLeastSquares (x y w : Fin (m + 1) → ℝ) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.degree ≤ n ∧ ∀ q : ℝ[X], q.degree ≤ n →
    ∑ j, w j * |p.eval (x j) - y j| ^ 2 ≤ ∑ j, w j * |q.eval (x j) - y j| ^ 2

/-- Supports Section 10.7.1. The weighted evaluation map $q \mapsto (\sqrt{w_j} q(x_j))_j$ is a
linear map from the real polynomials to the Euclidean space $\mathbb{R}^{m+1}$. For $w_j \ge 0$,
$\|q\|^2 = \sum_j w_j q(x_j)^2$ is the square of the seminorm (10.45). -/
noncomputable def weightedEval (x w : Fin (m + 1) → ℝ) :
    ℝ[X] →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) where
  toFun q := WithLp.toLp 2 fun j => √(w j) * q.eval (x j)
  map_add' p q := by
    ext j
    simp [mul_add]
  map_smul' c q := by
    ext j
    simp [mul_left_comm]

/-- Supports Section 10.7.1. The weighted data vector $(\sqrt{w_j} y_j)_j$ of the Euclidean space
$\mathbb{R}^{m+1}$. -/
noncomputable def weightedData (y w : Fin (m + 1) → ℝ) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 fun j => √(w j) * y j

/-- The component of index $j$ of the weighted evaluation of $q$ is $\sqrt{w_j} q(x_j)$. -/
@[simp]
theorem weightedEval_apply (x w : Fin (m + 1) → ℝ) (q : ℝ[X]) (j : Fin (m + 1)) :
    weightedEval x w q j = √(w j) * q.eval (x j) := rfl

/-- The component of index $j$ of the weighted data vector is $\sqrt{w_j} y_j$. -/
@[simp]
theorem weightedData_apply (y w : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    weightedData y w j = √(w j) * y j := rfl

/-- Supports Section 10.7.1. If $w_j \ge 0$ for all $j$, then the inner product of the weighted
evaluations of $p$ and $q$ is the discrete scalar product $\sum_j w_j p(x_j) q(x_j)$. -/
theorem inner_weightedEval (hw : ∀ j, 0 ≤ w j) (p q : ℝ[X]) :
    inner ℝ (weightedEval x w p) (weightedEval x w q) =
      ∑ j, w j * p.eval (x j) * q.eval (x j) := by
  simp only [PiLp.inner_apply, weightedEval_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := Real.mul_self_sqrt (hw j)
  linear_combination (p.eval (x j) * q.eval (x j)) * this

/-- Supports Section 10.7.1. If $w_j \ge 0$ for all $j$, then the inner product of the weighted
evaluation of $p$ with the weighted data vector is $\sum_j w_j p(x_j) y_j$. -/
theorem inner_weightedEval_weightedData (hw : ∀ j, 0 ≤ w j) (p : ℝ[X]) :
    inner ℝ (weightedEval x w p) (weightedData y w) = ∑ j, w j * p.eval (x j) * y j := by
  simp only [PiLp.inner_apply, weightedEval_apply, weightedData_apply, RCLike.inner_apply,
    conj_trivial]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := Real.mul_self_sqrt (hw j)
  linear_combination (p.eval (x j) * y j) * this

/-- Supports equation (10.45). If $w_j \ge 0$ for all $j$, then the squared norm of the weighted
evaluation of $q$ is $\sum_j w_j q(x_j)^2$, the square of the seminorm (10.45). -/
theorem norm_weightedEval_sq (hw : ∀ j, 0 ≤ w j) (q : ℝ[X]) :
    ‖weightedEval x w q‖ ^ 2 = ∑ j, w j * q.eval (x j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weightedEval_apply, mul_pow, Real.sq_sqrt (hw j)]

/-- Supports equation (10.44). If $w_j \ge 0$ for all $j$, then the squared distance between the
weighted evaluation of $q$ and the weighted data vector is $\sum_j w_j |q(x_j) - y_j|^2$. -/
theorem norm_weightedEval_sub_weightedData_sq (hw : ∀ j, 0 ≤ w j) (q : ℝ[X]) :
    ‖weightedEval x w q - weightedData y w‖ ^ 2 = ∑ j, w j * |q.eval (x j) - y j| ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.sub_apply, weightedEval_apply, weightedData_apply, ← mul_sub, mul_pow,
    Real.sq_sqrt (hw j), sq_abs]

/-- Supports equation (10.45). If $w_j > 0$ for all $j$, then the weighted evaluation of $q$ is zero
if and only if $q(x_j) = 0$ for all $j$. -/
theorem weightedEval_eq_zero_iff (hw : ∀ j, 0 < w j) (q : ℝ[X]) :
    weightedEval x w q = 0 ↔ ∀ j, q.eval (x j) = 0 := by
  constructor
  · intro h j
    have hj := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v j) h
    simp only [weightedEval_apply, PiLp.zero_apply, mul_eq_zero] at hj
    exact hj.resolve_left (Real.sqrt_pos.mpr (hw j)).ne'
  · intro h
    ext j
    simp [h j]

/-- Supports equation (10.45): the seminorm is a norm on $\mathbb{P}_n$ for $n \le m$. Let the nodes
$x_0, \dots, x_m$ be distinct, let $w_j > 0$, and let $n \le m$. If $q \in \mathbb{P}_n$ and the
weighted evaluation of $q$ is zero, then $q = 0$: a polynomial of degree at most $n \le m$ that
vanishes at $m + 1$ distinct nodes is zero. -/
theorem eq_zero_of_weightedEval_eq_zero (hx : Function.Injective x) (hw : ∀ j, 0 < w j)
    (hnm : n ≤ m) {q : ℝ[X]} (hq : q.degree ≤ n) (h : weightedEval x w q = 0) : q = 0 := by
  refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hx.injOn ?_
    fun j _ => (weightedEval_eq_zero_iff hw q).mp h j
  rw [Finset.card_univ, Fintype.card_fin]
  exact hq.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hnm)

/-- Supports equation (10.44): the discrete problem is a Euclidean best-approximation problem. If
$w_j \ge 0$ for all $j$, then $p$ is a discrete least-squares polynomial of degree at most $n$
if and only if $p \in \mathbb{P}_n$ and $(\sqrt{w_j} p(x_j))_j$ is a best approximation of
$(\sqrt{w_j} y_j)_j$ from the image of $\mathbb{P}_n$ under the weighted evaluation map. -/
theorem isDiscreteLeastSquares_iff (hw : ∀ j, 0 ≤ w j) (p : ℝ[X]) :
    IsDiscreteLeastSquares x y w n p ↔ p.degree ≤ n ∧
      IsBestApprox (((degreeLE ℝ n).map (weightedEval x w) :
          Submodule ℝ (EuclideanSpace ℝ (Fin (m + 1)))) : Set (EuclideanSpace ℝ (Fin (m + 1))))
        (weightedData y w) (weightedEval x w p) := by
  constructor
  · rintro ⟨hp, hmin⟩
    refine ⟨hp, ⟨p, mem_degreeLE.mpr hp, rfl⟩, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    rw [norm_sub_rev, norm_sub_rev _ (weightedEval x w q),
      ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_weightedEval_sub_weightedData_sq hw,
      norm_weightedEval_sub_weightedData_sq hw]
    exact hmin q (mem_degreeLE.mp hq)
  · rintro ⟨hp, -, hmin⟩
    refine ⟨hp, fun q hq => ?_⟩
    have := hmin _ ⟨q, mem_degreeLE.mpr hq, rfl⟩
    rwa [norm_sub_rev, norm_sub_rev _ (weightedEval x w q),
      ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_weightedEval_sub_weightedData_sq hw,
      norm_weightedEval_sub_weightedData_sq hw] at this

/-- **Equations (10.43)–(10.44)** of [quarteroni2000numerical]. Let $(x_i, y_i)$, $i = 0, \dots, m$,
be data with distinct abscissae, let $w_j > 0$, and let $n \le m$. Then the discrete
least-squares problem (10.44) has a unique solution $p_n \in \mathbb{P}_n$. If $n = m$, then
$p_n$ is the interpolating polynomial of degree $n$ at the nodes $x_i$.

The proof uses the existence and uniqueness of the best approximation from the
finite-dimensional subspace, the image of $\mathbb{P}_n$ in $\mathbb{R}^{m+1}$
(`exists_isBestApprox_of_finiteDimensional`, `IsBestApprox.unique`). It pulls the result back
along the weighted evaluation map, which is injective on $\mathbb{P}_n$
(`QuarteroniSaccoSaleri.Chapter10.eq_zero_of_weightedEval_eq_zero`). -/
theorem equation_10_44 (hx : Function.Injective x) (hw : ∀ j, 0 < w j) (hnm : n ≤ m)
    (y : Fin (m + 1) → ℝ) :
    (∃! p, IsDiscreteLeastSquares x y w n p) ∧
      (n = m → ∀ p, IsDiscreteLeastSquares x y w n p →
        p = Lagrange.interpolate Finset.univ x y) := by
  have hw' : ∀ j, 0 ≤ w j := fun j => (hw j).le
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin (m + 1))) := (degreeLE ℝ n).map (weightedEval x w)
    with hK
  -- uniqueness
  have huniq : ∀ p q, IsDiscreteLeastSquares x y w n p → IsDiscreteLeastSquares x y w n q →
      p = q := by
    intro p q hp hq
    rw [isDiscreteLeastSquares_iff hw'] at hp hq
    have h := hp.2.unique K.convex hq.2
    rw [← sub_eq_zero, ← map_sub] at h
    exact sub_eq_zero.mp (eq_zero_of_weightedEval_eq_zero hx hw hnm
      ((degree_sub_le _ _).trans (max_le hp.1 hq.1)) h)
  refine ⟨?_, fun hnm' p hp => huniq p _ hp ?_⟩
  · obtain ⟨v, hv⟩ := exists_isBestApprox_of_finiteDimensional K (weightedData y w)
    obtain ⟨p, hp, rfl⟩ := hv.1
    exact ⟨p, (isDiscreteLeastSquares_iff hw' p).mpr ⟨mem_degreeLE.mp hp, hv⟩,
      fun q hq => huniq q p hq ((isDiscreteLeastSquares_iff hw' p).mpr ⟨mem_degreeLE.mp hp, hv⟩)⟩
  · subst hnm'
    refine ⟨?_, fun q _ => ?_⟩
    · have := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (n + 1)))) (r := y)
        hx.injOn
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact Order.le_of_lt_succ (by exact_mod_cast this)
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun j _ => ?_))
        (Finset.sum_nonneg fun j _ => mul_nonneg (hw' j) (by positivity))
      rw [Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ j), sub_self, abs_zero,
        zero_pow two_ne_zero, mul_zero]

/-- **Equation (10.45)** and **Exercise 10.7** of [quarteroni2000numerical]. Let the nodes
$x_0, \dots, x_m$ be distinct, let $w_j > 0$, and let $n \le m$. Then:

* the seminorm $|||q||| = (\sum_j w_j q(x_j)^2)^{1/2}$ of (10.45) is the discrete seminorm
  `QuarteroniSaccoSaleri.Chapter10.discreteNorm w x` of Section 10.1, evaluated at the
  polynomial function;
* it is a seminorm on the real polynomials;
* it is a norm on $\mathbb{P}_n$: if $q \in \mathbb{P}_n$ and $|||q||| = 0$, then $q = 0$;
* it is **essentially strict**: if $|||f + g||| = |||f||| + |||g|||$, then there are
  $(\alpha, \beta) \neq (0, 0)$ with $\alpha f(x_i) + \beta g(x_i) = 0$ for $i = 0, \dots, m$.

**Reading.** The book asks for "nonnull $\alpha, \beta$". When $f$ vanishes at all the nodes,
the pair $(1, 0)$ is the only choice, so this cannot mean that both are nonzero. It is read as
$(\alpha, \beta) \neq (0, 0)$.

The seminorm is the Euclidean norm pulled back along the weighted evaluation map. The
essentially strict property is the equality case of the triangle inequality in the strictly
convex space $\mathbb{R}^{m+1}$ (`sameRay_iff_norm_add`), which makes $(\sqrt{w_j} f(x_j))_j$
and $(\sqrt{w_j} g(x_j))_j$ linearly dependent. -/
theorem exercise_10_7 (hx : Function.Injective x) (hw : ∀ j, 0 < w j) (hnm : n ≤ m) :
    (∀ q : ℝ[X], discreteNorm w x (fun t => q.eval t) = √(∑ j, w j * q.eval (x j) ^ 2)) ∧
      (∃ N : Seminorm ℝ ℝ[X], ∀ q, N q = discreteNorm w x fun t => q.eval t) ∧
      (∀ q : ℝ[X], q.degree ≤ n → discreteNorm w x (fun t => q.eval t) = 0 → q = 0) ∧
      ∀ f g : ℝ[X], discreteNorm w x (fun t => (f + g).eval t) =
          discreteNorm w x (fun t => f.eval t) + discreteNorm w x (fun t => g.eval t) →
        ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ i, α * f.eval (x i) + β * g.eval (x i) = 0 := by
  have hw' : ∀ j, 0 ≤ w j := fun j => (hw j).le
  have hnorm : ∀ q : ℝ[X], discreteNorm w x (fun t => q.eval t) = ‖weightedEval x w q‖ := by
    intro q
    rw [discreteNorm, discreteInner, ← Real.sqrt_sq (norm_nonneg _), norm_weightedEval_sq hw']
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨fun q => by rw [hnorm, ← Real.sqrt_sq (norm_nonneg _), norm_weightedEval_sq hw'],
    ⟨(normSeminorm ℝ (EuclideanSpace ℝ (Fin (m + 1)))).comp (weightedEval x w), fun q => by
      rw [Seminorm.comp_apply, coe_normSeminorm, hnorm]⟩, fun q hq h0 => ?_, fun f g hfg => ?_⟩
  · rw [hnorm, norm_eq_zero] at h0
    exact eq_zero_of_weightedEval_eq_zero hx hw hnm hq h0
  · rw [hnorm, hnorm, hnorm, map_add] at hfg
    have hcomp : ∀ (α β : ℝ) (i : Fin (m + 1)),
        (α • weightedEval x w f + β • weightedEval x w g) i =
          √(w i) * (α * f.eval (x i) + β * g.eval (x i)) := fun α β i => by
      simp only [PiLp.add_apply, PiLp.smul_apply, weightedEval_apply, smul_eq_mul]
      ring
    have hzero : ∀ α β : ℝ, α • weightedEval x w f + β • weightedEval x w g = 0 →
        ∀ i, α * f.eval (x i) + β * g.eval (x i) = 0 := fun α β h i => by
      have hi := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v i) h
      simp only [hcomp, PiLp.zero_apply, mul_eq_zero] at hi
      exact hi.resolve_left (Real.sqrt_pos.mpr (hw i)).ne'
    rcases sameRay_iff_norm_add.mpr hfg with hf0 | hg0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩
    · exact ⟨1, 0, Or.inl one_ne_zero, hzero 1 0 (by rw [hf0, smul_zero, zero_smul, add_zero])⟩
    · exact ⟨0, 1, Or.inr one_ne_zero, hzero 0 1 (by rw [hg0, smul_zero, zero_smul, add_zero])⟩
    · exact ⟨r₁, -r₂, Or.inl hr₁.ne', hzero r₁ (-r₂) (by rw [neg_smul, hr, add_neg_cancel])⟩

/-- A linearly independent family of $n + 1$ polynomials of degree at most $n$ spans $\mathbb{P}_n$.
-/
theorem span_range_eq_degreeLE {φ : Fin (n + 1) → ℝ[X]} (hdeg : ∀ j, (φ j).degree ≤ n)
    (hli : LinearIndependent ℝ φ) : Submodule.span ℝ (Set.range φ) = degreeLE ℝ n := by
  rw [← degreeLT_succ_eq_degreeLE]
  have : FiniteDimensional ℝ (degreeLT ℝ (n + 1)) :=
    (degreeLTEquiv ℝ (n + 1)).symm.finiteDimensional
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.range_subset_iff.mpr
    fun j => mem_degreeLT.mpr ((hdeg j).trans_lt (by exact_mod_cast Nat.lt_succ_self n)))) ?_
  rw [finrank_span_eq_card hli, Fintype.card_fin, LinearEquiv.finrank_eq (degreeLTEquiv ℝ (n + 1)),
    Module.finrank_fin_fun]

/-- **Section 10.7.1** of [quarteroni2000numerical], the system of normal equations in the summed
form that the book displays before (10.46). Let $w_j > 0$, and let $\varphi_0, \dots, \varphi_n$
be a basis of $\mathbb{P}_n$. Then $p_n = \sum_k a_k \varphi_k$ solves (10.44) if and only if
$$\sum_k a_k \sum_j w_j \varphi_k(x_j) \varphi_i(x_j) = \sum_j w_j y_j \varphi_i(x_j) \qquad
  \text{for all } i = 0, \dots, n.$$

This is the characterization `isBestApprox_sum_iff` of best approximations from the span of the
vectors $(\sqrt{w_j} \varphi_k(x_j))_j$, $k = 0, \dots, n$. -/
theorem isDiscreteLeastSquares_sum_iff (hw : ∀ j, 0 < w j) {φ : Fin (n + 1) → ℝ[X]}
    (hdeg : ∀ j, (φ j).degree ≤ n) (hli : LinearIndependent ℝ φ) (a : Fin (n + 1) → ℝ) :
    IsDiscreteLeastSquares x y w n (∑ k, C (a k) * φ k) ↔
      ∀ i, ∑ k, a k * ∑ j, w j * (φ k).eval (x j) * (φ i).eval (x j) =
        ∑ j, w j * y j * (φ i).eval (x j) := by
  have hw' : ∀ j, 0 ≤ w j := fun j => (hw j).le
  have hdegsum : (∑ k, C (a k) * φ k).degree ≤ n :=
    (degree_sum_le _ _).trans (Finset.sup_le fun k _ =>
      (degree_mul_le _ _).trans (by
        calc (C (a k)).degree + (φ k).degree ≤ 0 + n := by gcongr; exacts [degree_C_le, hdeg k]
          _ = n := zero_add _))
  rw [isDiscreteLeastSquares_iff hw', and_iff_right hdegsum]
  have hK : (((degreeLE ℝ n).map (weightedEval x w) :
      Submodule ℝ (EuclideanSpace ℝ (Fin (m + 1)))) : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      (Submodule.span ℝ (Set.range (weightedEval x w ∘ φ)) :
        Submodule ℝ (EuclideanSpace ℝ (Fin (m + 1)))) := by
    rw [Set.range_comp, ← Submodule.map_span, span_range_eq_degreeLE hdeg hli]
  have hT : weightedEval x w (∑ k, C (a k) * φ k) = ∑ k, a k • weightedEval x w (φ k) := by
    simp only [← smul_eq_C_mul, map_sum, map_smul]
  rw [hK, hT]
  refine (isBestApprox_sum_iff (⇑(weightedEval x w) ∘ φ) a (weightedData y w)).trans ?_
  simp only [Function.comp_apply, inner_weightedEval hw', inner_weightedEval_weightedData hw']
  refine forall_congr' fun i => ?_
  rw [show (∑ j, w j * (φ i).eval (x j) * y j) = ∑ j, w j * y j * (φ i).eval (x j) from
    Finset.sum_congr rfl fun j _ => by ring]
  refine Eq.congr_left (Finset.sum_congr rfl fun k _ => ?_)
  rw [show (∑ j, w j * (φ i).eval (x j) * (φ k).eval (x j)) =
    ∑ j, w j * (φ k).eval (x j) * (φ i).eval (x j) from Finset.sum_congr rfl fun j _ => by ring]

/-- **Equation (10.46)** of [quarteroni2000numerical], the normal equations in matrix form. Let
$w_j > 0$, and let $\varphi_0, \dots, \varphi_n$ be a basis of $\mathbb{P}_n$. Let $B$ be the
$(m + 1) \times (n + 1)$ matrix with entries $b_{ij} = \varphi_j(x_i)$, let
$W = \operatorname{diag}(w_0, \dots, w_m)$, let $a \in \mathbb{R}^{n+1}$ be the vector of
coefficients, and let $y \in \mathbb{R}^{m+1}$ be the data. Then $p_n = \sum_j a_j \varphi_j$
solves (10.44) if and only if
$$B^T W B a = B^T W y.$$

**Generalization.** The book prints $B^T B a = B^T y$, which omits the weight matrix that its
display before (10.46) carries. The printed form is the case $w_j = 1$, the least-squares
solution of the overdetermined system $Ba = y$ of Section 3.13. -/
theorem equation_10_46 (hw : ∀ j, 0 < w j) {φ : Fin (n + 1) → ℝ[X]}
    (hdeg : ∀ j, (φ j).degree ≤ n) (hli : LinearIndependent ℝ φ) (a : Fin (n + 1) → ℝ) :
    IsDiscreteLeastSquares x y w n (∑ k, C (a k) * φ k) ↔
      ((Matrix.of fun i j => (φ j).eval (x i)).transpose * Matrix.diagonal w *
          Matrix.of fun i j => (φ j).eval (x i)).mulVec a =
        ((Matrix.of fun i j => (φ j).eval (x i)).transpose * Matrix.diagonal w).mulVec y := by
  rw [isDiscreteLeastSquares_sum_iff hw hdeg hli a, funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_mul]
  rw [show (∑ k, a k * ∑ j, w j * (φ k).eval (x j) * (φ i).eval (x j)) =
      ∑ k, ∑ j, (φ i).eval (x j) * w j * (φ k).eval (x j) * a k from
    Finset.sum_congr rfl fun k _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring]
  exact Eq.congr_right (Finset.sum_congr rfl fun j _ => by ring)

/-- **Section 10.7.1** of [quarteroni2000numerical], linear regression. Let $m \ge 1$, let the nodes
$x_0, \dots, x_m$ be distinct, let $w_j > 0$, and let $y_j = Y(x_j)$ be the values of a function
$Y$. For $n = 1$ the solution of (10.44) is a linear function $a_0 + a_1 x$, the **linear
regression** of the data. Let $\varphi_0 = 1$, $\varphi_1 = x$, and let
$(f, g)_m = \sum_j w_j f(x_j) g(x_j)$. If $a_0 + a_1 x$ solves (10.44), then
$$D = (\varphi_1, \varphi_1)_m (\varphi_0, \varphi_0)_m - (\varphi_0, \varphi_1)_m^2 > 0,$$
and
$$a_0 = \frac{(Y, \varphi_0)_m (\varphi_1, \varphi_1)_m - (Y, \varphi_1)_m (\varphi_1,
  \varphi_0)_m}{D}, \qquad a_1 = \frac{(Y, \varphi_1)_m (\varphi_0, \varphi_0)_m - (Y,
  \varphi_0)_m (\varphi_1, \varphi_0)_m}{D}.$$

**Generalization.** The book defines $(\cdot, \cdot)_m$ without the weights $w_j$. Here the
scalar product carries the weights, as the system that the formulas solve does; the printed form
is the case $w_j = 1$.

The proof applies Cramer's rule to the $2 \times 2$ normal equations
`QuarteroniSaccoSaleri.Chapter10.isDiscreteLeastSquares_sum_iff`. The inequality $D > 0$ is the
strict Cauchy–Schwarz inequality for $(\sqrt{w_j})_j$ and $(\sqrt{w_j} x_j)_j$, which are
linearly independent when two nodes differ. -/
theorem linearRegression_coeff (hx : Function.Injective x) (hw : ∀ j, 0 < w j) (hm : 1 ≤ m)
    (Y : ℝ → ℝ) {a₀ a₁ : ℝ}
    (h : IsDiscreteLeastSquares x (fun j => Y (x j)) w 1 (C a₀ + C a₁ * X)) :
    0 < discreteInner w x id id * discreteInner w x (fun _ => 1) (fun _ => 1) -
        discreteInner w x (fun _ => 1) id ^ 2 ∧
      a₀ = (discreteInner w x Y (fun _ => 1) * discreteInner w x id id -
          discreteInner w x Y id * discreteInner w x id (fun _ => 1)) /
        (discreteInner w x id id * discreteInner w x (fun _ => 1) (fun _ => 1) -
          discreteInner w x (fun _ => 1) id ^ 2) ∧
      a₁ = (discreteInner w x Y id * discreteInner w x (fun _ => 1) (fun _ => 1) -
          discreteInner w x Y (fun _ => 1) * discreteInner w x id (fun _ => 1)) /
        (discreteInner w x id id * discreteInner w x (fun _ => 1) (fun _ => 1) -
          discreteInner w x (fun _ => 1) id ^ 2) := by
  have hw' : ∀ j, 0 ≤ w j := fun j => (hw j).le
  -- the normal equations for the basis `1, X`
  have hli : LinearIndependent ℝ ![(1 : ℝ[X]), X] := by
    refine (LinearIndependent.pair_iff' one_ne_zero).mpr fun c hc => ?_
    have := congrArg (fun p : ℝ[X] => p.coeff 1) hc
    simp [Polynomial.coeff_one] at this
  have hsys : ∀ i : Fin 2, ∑ k : Fin 2, ![a₀, a₁] k *
      ∑ j, w j * (![(1 : ℝ[X]), X] k).eval (x j) * (![(1 : ℝ[X]), X] i).eval (x j) =
        ∑ j, w j * Y (x j) * (![(1 : ℝ[X]), X] i).eval (x j) :=
    (isDiscreteLeastSquares_sum_iff (y := fun j => Y (x j)) hw
      (φ := ![(1 : ℝ[X]), X]) (fun j => by fin_cases j <;> simp) hli ![a₀, a₁]).mp (by
        convert h using 1
        simp [Fin.sum_univ_two])
  have h0 := hsys 0
  have h1 := hsys 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, eval_one, eval_X,
    mul_one] at h0 h1
  -- the four inner products as sums
  simp only [discreteInner, id, mul_one]
  set S0 : ℝ := ∑ j, w j with hS0
  set S1 : ℝ := ∑ j, w j * x j with hS1
  set S2 : ℝ := ∑ j, w j * x j * x j with hS2
  set T0 : ℝ := ∑ j, w j * Y (x j) with hT0
  set T1 : ℝ := ∑ j, w j * Y (x j) * x j with hT1
  -- `D ≥ 0` is Cauchy–Schwarz for `u = (√wⱼ)`, `v = (√wⱼ xⱼ)`
  set u := weightedEval x w 1 with hu
  set v := weightedEval x w X with hv
  have huu : inner ℝ u u = S0 := by
    rw [hu, inner_weightedEval hw']
    simp [hS0]
  have huv : inner ℝ u v = S1 := by
    rw [hu, hv, inner_weightedEval hw']
    simp [hS1]
  have hvv : inner ℝ v v = S2 := by
    rw [hv, inner_weightedEval hw']
    simp [hS2]
  have hD0 : 0 ≤ S2 * S0 - S1 ^ 2 := by
    have := real_inner_mul_inner_self_le u v
    rw [huu, huv, hvv] at this
    nlinarith
  -- `D ≠ 0`: equality in Cauchy–Schwarz would make all the nodes equal
  have hu0 : u ≠ 0 := fun h0 => by
    have := (weightedEval_eq_zero_iff hw 1).mp h0 0
    simp at this
  have hne : ∀ j : Fin (m + 1), j ≠ 0 → x j ≠ x 0 := fun j hj h => hj (hx h)
  have hidx : (⟨1, by omega⟩ : Fin (m + 1)) ≠ 0 := by simp
  have hv0 : v ≠ 0 := fun h0 => by
    have h := (weightedEval_eq_zero_iff hw X).mp h0
    simp only [eval_X] at h
    exact hne _ hidx (by rw [h, h])
  have hD : S2 * S0 - S1 ^ 2 ≠ 0 := by
    intro hD
    have hcs : ‖inner ℝ u v‖ = ‖u‖ * ‖v‖ := by
      rw [Real.norm_eq_abs, ← sq_eq_sq₀ (abs_nonneg _) (by positivity), sq_abs, mul_pow,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, huu, huv, hvv]
      linear_combination -hD
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hu0 hv0).mp hcs
    have hxj : ∀ j, x j = r := fun j => by
      have hj := congrArg (fun z : EuclideanSpace ℝ (Fin (m + 1)) => z j) hr
      simp only [hv, hu, PiLp.smul_apply, weightedEval_apply, eval_X, eval_one, smul_eq_mul,
        mul_one] at hj
      have hsq := (Real.sqrt_pos.mpr (hw j)).ne'
      field_simp at hj
      linarith
    exact hne _ hidx (by rw [hxj, hxj])
  refine ⟨lt_of_le_of_ne hD0 (Ne.symm hD), ?_, ?_⟩
  · rw [eq_div_iff hD]
    linear_combination S2 * h0 - S1 * h1
  · rw [eq_div_iff hD]
    linear_combination S0 * h1 - S1 * h0

end Discrete

end QuarteroniSaccoSaleri.Chapter10
