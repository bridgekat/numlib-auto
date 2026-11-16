/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Numlib.Analysis.Calculus.Taylor
import Numlib.Analysis.Fourier.OddExtension
import Numlib.Analysis.PDE.Heat.Classical

/-!
# Sine-series solutions of the heat equation on $(0, \pi)$

Let $\nu \in \mathbb{R}$, $n \in \mathbb{N}$ and $b_0, \dots, b_{n-1} \in \mathbb{R}$. The finite
sine series
$$u(x, t) = \sum_{j < n} b_j \, e^{-\nu (j + 1)^2 t} \sin((j + 1) x)$$
solves the heat equation $\partial_t u = \nu \partial_{xx} u$ on $(0, \pi) \times \mathbb{R}$ with
homogeneous Dirichlet boundary values and the initial datum $\sum_{j < n} b_j \sin((j + 1) x)$. This
module proves that $u$ is a classical solution, that it satisfies the maximum principle, and that
its derivatives obey explicit bounds on $\mathbb{R} \times [0, \infty)$.

Numerical texts use these solutions to analyze finite difference schemes for the heat equation by
Taylor expansion, as in Examples 6.2.4, 6.2.8, 6.3.3 and 6.3.4 of [han2009theoretical]; see also
§10.1 of [brezis2011functional]. The series is $C^\infty$ on $\mathbb{R} \times \mathbb{R}$, each of
its derivatives is a finite sum of the same shape, and so each derivative is bounded on
$\mathbb{R} \times [0, \infty)$ by an explicit constant.

## Main definitions

* `Heat.sineSeries`: the finite sine series $u$.
* `Heat.sineSeriesDerivX`: the $m$-th derivative of $u$ in $x$, $\sum_{j < n} b_j e^{-\nu (j+1)^2 t}
  (j+1)^m \sin((j+1) x + m\pi/2)$.
* `Heat.sineSeriesDerivT`: the $m$-th derivative of $u$ in $t$, $\sum_{j < n} b_j (-\nu (j+1)^2)^m
  e^{-\nu (j+1)^2 t} \sin((j+1) x)$.

## Main results

* `Heat.hasDerivAt_sineSeriesDerivX` and `Heat.hasDerivAt_sineSeriesDerivT`: the derivative of the
  $m$-th function of each family is the $(m+1)$-th.
* `Heat.abs_sineSeriesDerivX_le` and `Heat.abs_sineSeriesDerivT_le`: for $t \ge 0$ the $m$-th
  derivatives are bounded by $\sum_j |b_j| (j+1)^m$ and $\sum_j |b_j| (\nu (j+1)^2)^m$.
* `Heat.sineSeries_isClassicalSolution`: $u$ is a classical solution of the heat equation on
  $(0, \pi) \times (0, T)$ for every $T$.
* `Heat.abs_sineSeries_le`: the maximum principle $|u(x, t)| \le M$ on $[0, \pi] \times [0, T]$ when
  $|u(\cdot, 0)| \le M$ on $[0, \pi]$.
* `Heat.sineSeries_neg_left` and `Heat.sineSeries_add_two_pi_left`: $u$ is odd and $2\pi$-periodic
  in $x$.
* `Heat.abs_sineSeries_sub_forward_time_le`, `Heat.abs_sineSeries_sub_backward_time_le` and
  `Heat.abs_sineSeries_centred_sub_le`: the Taylor bounds that the analysis of a finite difference
  scheme needs, for all $x$ and for $t \ge 0$.

## Implementation notes

* A point of the strip is a pair $p = (x, t) \in \mathbb{R} \times \mathbb{R}$, and the coefficients
  are a sequence $b : \mathbb{N} \to \mathbb{R}$ of which only $b_0, \dots, b_{n-1}$ enter.
* The two families of derivatives are the input that the Taylor bounds of
  `Numlib.Analysis.Calculus.Taylor` require.
* The value of $u$ at $t = 0$ is the sine polynomial `sinePolynomial` of
  `Numlib.Analysis.Fourier.SineBasis`, a continuous function on $[0, \pi]$
  (`Heat.sineSeries_zero_right_eq`).
* The odd $2\pi$-periodic extension of a function on $[0, \pi]$, and the uniform density of the sine
  polynomials in $C_0[0, \pi]$ (Exercise 6.2.1 of [han2009theoretical]), are in
  `Numlib.Analysis.Fourier.OddExtension`.
-/

open Filter Set Topology Finset InnerProductSpace Laplacian
open scoped Real

namespace Heat

/-! ### The finite sine series and its derivative towers -/

section SineSeries

variable (ν : ℝ) (n : ℕ) (b : ℕ → ℝ)

/-- The **finite sine series** with diffusion constant $\nu$ and coefficients $b_0, \dots, b_{n-1}$
is
$$u(x, t) = \sum_{j < n} b_j \, e^{-\nu (j + 1)^2 t} \sin((j + 1) x).$$
It solves the heat equation $\partial_t u = \nu \partial_{xx} u$ on $(0, \pi)$ with homogeneous
Dirichlet boundary values and the initial datum $\sum_{j < n} b_j \sin((j + 1) x)$. -/
noncomputable def sineSeries (p : ℝ × ℝ) : ℝ :=
  ∑ j ∈ range n, b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * Real.sin (((j : ℝ) + 1) * p.1)

/-- The $m$-th derivative in $x$ of the sine series, written with the phase shift
$\sin^{(m)} y = \sin(y + m\pi/2)$:
$$\partial_x^m u(x, t) = \sum_{j < n} b_j \, e^{-\nu (j + 1)^2 t} (j + 1)^m \sin\Bigl((j + 1)
  x + \frac{m\pi}{2}\Bigr).$$
-/
noncomputable def sineSeriesDerivX (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ j ∈ range n, b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * ((j : ℝ) + 1) ^ m *
    Real.sin (((j : ℝ) + 1) * p.1 + m * (π / 2))

/-- The $m$-th derivative in $t$ of the sine series:
$$\partial_t^m u(x, t) = \sum_{j < n} b_j \, (-\nu (j + 1)^2)^m \, e^{-\nu (j + 1)^2 t}
  \sin((j + 1) x).$$
-/
noncomputable def sineSeriesDerivT (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ j ∈ range n, b j * (-ν * ((j : ℝ) + 1) ^ 2) ^ m * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) *
    Real.sin (((j : ℝ) + 1) * p.1)

variable {ν n b}

/-- The $0$-th derivative in $x$ of the sine series is the sine series itself. -/
theorem sineSeriesDerivX_zero : sineSeriesDerivX ν n b 0 = sineSeries ν n b := by
  funext p
  simp only [sineSeriesDerivX, sineSeries, Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]

/-- The $0$-th derivative in $t$ of the sine series is the sine series itself. -/
theorem sineSeriesDerivT_zero : sineSeriesDerivT ν n b 0 = sineSeries ν n b := by
  funext p
  simp only [sineSeriesDerivT, sineSeries, pow_zero, mul_one]

/-- The second derivative in $x$ of the sine series is $-\sum_{j < n} b_j \, e^{-\nu (j + 1)^2 t}
(j + 1)^2 \sin((j + 1) x)$. -/
theorem sineSeriesDerivX_two (p : ℝ × ℝ) :
    sineSeriesDerivX ν n b 2 p = -∑ j ∈ range n,
      b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * ((j : ℝ) + 1) ^ 2 *
        Real.sin (((j : ℝ) + 1) * p.1) := by
  simp only [sineSeriesDerivX, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((2 : ℕ) : ℝ) * (π / 2) = π by push_cast; ring, Real.sin_add_pi]
  ring

/-- The fourth derivative in $x$ of the sine series is $\sum_{j < n} b_j \, e^{-\nu (j + 1)^2 t}
(j + 1)^4 \sin((j + 1) x)$. -/
theorem sineSeriesDerivX_four (p : ℝ × ℝ) :
    sineSeriesDerivX ν n b 4 p = ∑ j ∈ range n,
      b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * ((j : ℝ) + 1) ^ 4 *
        Real.sin (((j : ℝ) + 1) * p.1) := by
  simp only [sineSeriesDerivX]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((4 : ℕ) : ℝ) * (π / 2) = (1 : ℕ) * (2 * π) by push_cast; ring,
    Real.sin_add_nat_mul_two_pi]

/-- For all $m \in \mathbb{N}$ and $x, t \in \mathbb{R}$, the function
$y \mapsto \partial_x^m u(y, t)$ (`Heat.sineSeriesDerivX`) has derivative
$\partial_x^{m+1} u(x, t)$ at $x$. -/
theorem hasDerivAt_sineSeriesDerivX (m : ℕ) (x t : ℝ) :
    HasDerivAt (fun y => sineSeriesDerivX ν n b m (y, t)) (sineSeriesDerivX ν n b (m + 1) (x, t))
      x := by
  unfold sineSeriesDerivX
  refine HasDerivAt.fun_sum (A := fun j y => b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * t) *
    ((j : ℝ) + 1) ^ m * Real.sin (((j : ℝ) + 1) * y + m * (π / 2))) fun j _ => ?_
  have h1 : HasDerivAt (fun y : ℝ => ((j : ℝ) + 1) * y + m * (π / 2)) ((j : ℝ) + 1) x := by
    simpa using ((hasDerivAt_id x).const_mul ((j : ℝ) + 1)).add_const (m * (π / 2))
  have h2 := ((Real.hasDerivAt_sin _).comp x h1).const_mul
    (b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * t) * ((j : ℝ) + 1) ^ m)
  refine h2.congr_deriv ?_
  rw [← Real.sin_add_pi_div_two]
  push_cast
  rw [show ((j : ℝ) + 1) * x + (m + 1) * (π / 2) = (j + 1) * x + m * (π / 2) + π / 2 by ring]
  ring

/-- For all $m \in \mathbb{N}$ and $x, t \in \mathbb{R}$, the function
$s \mapsto \partial_t^m u(x, s)$ (`Heat.sineSeriesDerivT`) has derivative
$\partial_t^{m+1} u(x, t)$ at $t$. -/
theorem hasDerivAt_sineSeriesDerivT (m : ℕ) (x t : ℝ) :
    HasDerivAt (fun s => sineSeriesDerivT ν n b m (x, s)) (sineSeriesDerivT ν n b (m + 1) (x, t))
      t := by
  unfold sineSeriesDerivT
  refine HasDerivAt.fun_sum (A := fun j s => b j * (-ν * ((j : ℝ) + 1) ^ 2) ^ m *
    Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * s) * Real.sin (((j : ℝ) + 1) * x)) fun j _ => ?_
  have h1 : HasDerivAt (fun s : ℝ => -ν * ((j : ℝ) + 1) ^ 2 * s) (-ν * ((j : ℝ) + 1) ^ 2) t :=
    (hasDerivAt_id t).const_mul (-ν * ((j : ℝ) + 1) ^ 2) |>.congr_deriv (mul_one _)
  have h2 := (((Real.hasDerivAt_exp _).comp t h1).const_mul
    (b j * (-ν * ((j : ℝ) + 1) ^ 2) ^ m)).mul_const (Real.sin (((j : ℝ) + 1) * x))
  refine h2.congr_deriv ?_
  simp only [pow_succ]
  ring

/-- The sine series satisfies the heat equation: at every point,
$\partial_t u = \nu \, \partial_x^2 u$, where the two sides are `Heat.sineSeriesDerivT` with
$m = 1$ and $\nu$ times `Heat.sineSeriesDerivX` with $m = 2$. -/
theorem sineSeriesDerivT_one (p : ℝ × ℝ) :
    sineSeriesDerivT ν n b 1 p = ν * sineSeriesDerivX ν n b 2 p := by
  rw [sineSeriesDerivX_two, sineSeriesDerivT, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Let $\nu \ge 0$ and $m \in \mathbb{N}$. At every point $(x, t)$ with $t \ge 0$,
$$|\partial_x^m u(x, t)| \le \sum_{j < n} |b_j| (j + 1)^m.$$
-/
theorem abs_sineSeriesDerivX_le (hν : 0 ≤ ν) (m : ℕ) {p : ℝ × ℝ} (hp : 0 ≤ p.2) :
    |sineSeriesDerivX ν n b m p| ≤ ∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ m := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ m)]
  have he : Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) ≤ 1 := by
    have : 0 ≤ ν * ((j : ℝ) + 1) ^ 2 * p.2 := by positivity
    exact Real.exp_le_one_iff.2 (by linarith)
  have hs := Real.abs_sin_le_one (((j : ℝ) + 1) * p.1 + m * (π / 2))
  calc |b j| * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * ((j : ℝ) + 1) ^ m *
        |Real.sin (((j : ℝ) + 1) * p.1 + m * (π / 2))|
      ≤ |b j| * 1 * ((j : ℝ) + 1) ^ m * 1 := by gcongr
    _ = |b j| * ((j : ℝ) + 1) ^ m := by ring

/-- Let $\nu \ge 0$ and $m \in \mathbb{N}$. At every point $(x, t)$ with $t \ge 0$,
$$|\partial_t^m u(x, t)| \le \sum_{j < n} |b_j| (\nu (j + 1)^2)^m.$$
-/
theorem abs_sineSeriesDerivT_le (hν : 0 ≤ ν) (m : ℕ) {p : ℝ × ℝ} (hp : 0 ≤ p.2) :
    |sineSeriesDerivT ν n b m p| ≤ ∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_pow, abs_mul, abs_neg,
    abs_of_nonneg hν, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ 2)]
  have he : Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) ≤ 1 := by
    have : 0 ≤ ν * ((j : ℝ) + 1) ^ 2 * p.2 := by positivity
    exact Real.exp_le_one_iff.2 (by linarith)
  have hs := Real.abs_sin_le_one (((j : ℝ) + 1) * p.1)
  calc |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) *
        |Real.sin (((j : ℝ) + 1) * p.1)|
      ≤ |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m * 1 * 1 := by gcongr
    _ = |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m := by ring

/-- The sine series is continuous on $\mathbb{R} \times \mathbb{R}$. -/
theorem continuous_sineSeries : Continuous (sineSeries ν n b) := by
  unfold sineSeries
  fun_prop

/-- For every $t$, the function $y \mapsto u(y, t)$ is $C^k$ for every $k$, including $k = \infty$
and $k = \omega$. -/
theorem contDiff_sineSeries_fst {k : WithTop ℕ∞} (t : ℝ) :
    ContDiff ℝ k fun y => sineSeries ν n b (y, t) := by
  unfold sineSeries
  fun_prop

/-- The sine series vanishes at $x = 0$: $u(0, t) = 0$ for every $t$. -/
theorem sineSeries_zero_left (t : ℝ) : sineSeries ν n b (0, t) = 0 := by
  simp [sineSeries]

/-- The sine series vanishes at $x = \pi$: $u(\pi, t) = 0$ for every $t$. -/
theorem sineSeries_pi_left (t : ℝ) : sineSeries ν n b (π, t) = 0 := by
  unfold sineSeries
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show ((j : ℝ) + 1) * π = ((j + 1 : ℕ) : ℝ) * π by push_cast; ring, Real.sin_nat_mul_pi,
    mul_zero]

/-- At $t = 0$ the sine series is the sine polynomial: $u(x, 0) = \sum_{j < n} b_j \sin((j + 1) x)$.
-/
theorem sineSeries_zero_right (x : ℝ) :
    sineSeries ν n b (x, 0) = ∑ j ∈ range n, b j * Real.sin (((j : ℝ) + 1) * x) := by
  simp [sineSeries]

/-- For $\nu = 0$ the sine series with coefficients $c$ is the sine polynomial
$\sum_{j < n} c_j \sin((j + 1) y)$ at every time $t$. In this form the results on the spatial
derivatives of the series apply to a sine polynomial alone. -/
theorem sineSeries_zero_nu_eq (n : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (fun y => sineSeries 0 n c (y, t))
      = fun y => ∑ j ∈ range n, c j * Real.sin (((j : ℝ) + 1) * y) := by
  funext y
  simp [sineSeries]

/-- The sine series is odd in $x$: $u(-x, t) = -u(x, t)$. -/
theorem sineSeries_neg_left (x t : ℝ) : sineSeries ν n b (-x, t) = -sineSeries ν n b (x, t) := by
  simp only [sineSeries, mul_neg, Real.sin_neg, ← Finset.sum_neg_distrib]

/-- The sine series is $2\pi$-periodic in $x$: $u(x + 2\pi, t) = u(x, t)$. -/
theorem sineSeries_add_two_pi_left (x t : ℝ) :
    sineSeries ν n b (x + 2 * π, t) = sineSeries ν n b (x, t) := by
  unfold sineSeries
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((j : ℝ) + 1) * (x + 2 * π) = ((j : ℝ) + 1) * x + ((j + 1 : ℕ) : ℝ) * (2 * π) by
    push_cast; ring, Real.sin_add_nat_mul_two_pi]

/-- For all $x, t$, the Laplacian on $\mathbb{R}$ of $y \mapsto u(y, t)$ at $x$ is the second
derivative $\partial_x^2 u(x, t)$ given by `Heat.sineSeriesDerivX` with $m = 2$. -/
theorem laplacian_sineSeries_fst (x t : ℝ) :
    Δ (fun y => sineSeries ν n b (y, t)) x = sineSeriesDerivX ν n b 2 (x, t) := by
  rw [laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, iteratedDeriv_one]
  have h0 : deriv (fun y => sineSeries ν n b (y, t))
      = fun y => sineSeriesDerivX ν n b 1 (y, t) := by
    funext y
    rw [← sineSeriesDerivX_zero]
    exact (hasDerivAt_sineSeriesDerivX 0 y t).deriv
  rw [h0]
  exact (hasDerivAt_sineSeriesDerivX 1 x t).deriv

/-- For all $x, t$, the derivative of $s \mapsto u(x, s)$ at $t$ is $\partial_t u(x, t)$ given by
`Heat.sineSeriesDerivT` with $m = 1$. -/
theorem deriv_sineSeries_snd (x t : ℝ) :
    deriv (fun s => sineSeries ν n b (x, s)) t = sineSeriesDerivT ν n b 1 (x, t) := by
  rw [← sineSeriesDerivT_zero]
  exact (hasDerivAt_sineSeriesDerivT 0 x t).deriv

/-- **The sine series is a classical solution of the heat equation.** For all
$\nu, T \in \mathbb{R}$, the sine series is a classical solution of
$\partial_t u = \nu \partial_{xx} u$ on $(0, \pi) \times (0, T)$ in the sense of
`Heat.IsClassicalSolution`, with $E = \mathbb{R}$ and $\Omega = (0, \pi)$. -/
theorem sineSeries_isClassicalSolution (T : ℝ) :
    IsClassicalSolution ν (Ioo 0 π) T (sineSeries ν n b) where
  continuousOn := continuous_sineSeries.continuousOn
  differentiableAt_snd x _ t _ := by
    rw [← sineSeriesDerivT_zero]
    exact (hasDerivAt_sineSeriesDerivT 0 x t).differentiableAt
  contDiffAt_fst x _ t _ := (contDiff_sineSeries_fst t).contDiffAt
  deriv_eq_laplacian x _ t _ := by
    rw [deriv_sineSeries_snd, laplacian_sineSeries_fst, sineSeriesDerivT_one]

/-- **The maximum principle for the sine series.** Let $\nu > 0$, $T > 0$ and $M \in \mathbb{R}$. If
$|u(y, 0)| \le M$ for all $y \in [0, \pi]$, then
$$|u(x, t)| \le M \quad \text{for all } x \in [0, \pi],\ t \in [0, T].$$

The proof applies `Heat.IsClassicalSolution.abs_le_of_eq_zero_frontier` with $E = \mathbb{R}$
and $\Omega = (0, \pi)$. -/
theorem abs_sineSeries_le (hν : 0 < ν) {T : ℝ} (hT : 0 < T) {M : ℝ}
    (hM : ∀ y ∈ Icc (0 : ℝ) π, |sineSeries ν n b (y, 0)| ≤ M) :
    ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc 0 T, |sineSeries ν n b (x, t)| ≤ M := by
  have hcl : closure (Ioo (0 : ℝ) π) = Icc 0 π := closure_Ioo Real.pi_pos.ne
  have hfr : frontier (Ioo (0 : ℝ) π) = {0, π} := frontier_Ioo Real.pi_pos
  have := (sineSeries_isClassicalSolution (ν := ν) (n := n) (b := b) T).abs_le_of_eq_zero_frontier
    isOpen_Ioo (Metric.isBounded_Ioo 0 π) hν hT (fun x hx t _ => ?_) (M := M) ?_
  · intro x hx t ht
    exact this x (hcl ▸ hx) t ht
  · rw [hfr] at hx
    rcases hx with rfl | rfl
    · exact sineSeries_zero_left t
    · exact sineSeries_pi_left t
  · intro y hy
    exact hM y (hcl ▸ hy)

/-!
### Taylor bounds for the sine series

A finite difference scheme for the heat equation needs two expansions of the sine series, for all
$x \in \mathbb{R}$ and $t \ge 0$: the expansion in time to second order, forward and backward, and
the centred second difference in space to fourth order. The constants are
$\sum_j |b_j| (\nu (j + 1)^2)^2$ and $\sum_j |b_j| (j + 1)^4$.
-/

/-- **Forward expansion in time.** Let $\nu \ge 0$, $x \in \mathbb{R}$ and $t, k \ge 0$. Then
$$|u(x, t + k) - u(x, t) - k \, \partial_t u(x, t)| \le \Bigl(\sum_{j < n} |b_j| (\nu (j +
  1)^2)^2\Bigr) \frac{k^2}{2}.$$
-/
theorem abs_sineSeries_sub_forward_time_le (hν : 0 ≤ ν) {x t k : ℝ} (ht : 0 ≤ t) (hk : 0 ≤ k) :
    |sineSeries ν n b (x, t + k) - sineSeries ν n b (x, t) - k * sineSeriesDerivT ν n b 1 (x, t)|
      ≤ (∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) * k ^ 2 / 2 := by
  have h := norm_sub_sub_smul_le_mul_sq_div_two (a := t) (b := t + k)
    (y := fun s => sineSeries ν n b (x, s)) (y' := fun s => sineSeriesDerivT ν n b 1 (x, s))
    (y'' := fun s => sineSeriesDerivT ν n b 2 (x, s))
    (M := ∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) (by linarith)
    (fun s _ => by
      rw [← sineSeriesDerivT_zero]
      exact (hasDerivAt_sineSeriesDerivT 0 x s).hasDerivWithinAt)
    (fun s _ => (hasDerivAt_sineSeriesDerivT 1 x s).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact abs_sineSeriesDerivT_le hν 2 (p := (x, s)) (by linarith [hs.1]))
  rw [smul_eq_mul, Real.norm_eq_abs, add_sub_cancel_left] at h
  exact h

/-- **Backward expansion in time.** Let $\nu \ge 0$, $x \in \mathbb{R}$ and $t, k \ge 0$. Then
$$|u(x, t + k) - u(x, t) - k \, \partial_t u(x, t + k)| \le \Bigl(\sum_{j < n} |b_j| (\nu (j +
  1)^2)^2\Bigr) \frac{k^2}{2}.$$
-/
theorem abs_sineSeries_sub_backward_time_le (hν : 0 ≤ ν) {x t k : ℝ} (ht : 0 ≤ t) (hk : 0 ≤ k) :
    |sineSeries ν n b (x, t + k) - sineSeries ν n b (x, t)
        - k * sineSeriesDerivT ν n b 1 (x, t + k)|
      ≤ (∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) * k ^ 2 / 2 := by
  have h := norm_sub_sub_smul_le_mul_sq_div_two' (a := t) (b := t + k)
    (y := fun s => sineSeries ν n b (x, s)) (y' := fun s => sineSeriesDerivT ν n b 1 (x, s))
    (y'' := fun s => sineSeriesDerivT ν n b 2 (x, s))
    (M := ∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) (by linarith)
    (fun s _ => by
      rw [← sineSeriesDerivT_zero]
      exact (hasDerivAt_sineSeriesDerivT 0 x s).hasDerivWithinAt)
    (fun s _ => (hasDerivAt_sineSeriesDerivT 1 x s).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact abs_sineSeriesDerivT_le hν 2 (p := (x, s)) (by linarith [hs.1]))
  rw [smul_eq_mul, Real.norm_eq_abs, add_sub_cancel_left] at h
  have e : sineSeries ν n b (x, t + k) - sineSeries ν n b (x, t)
        - k * sineSeriesDerivT ν n b 1 (x, t + k)
      = -(sineSeries ν n b (x, t) - sineSeries ν n b (x, t + k)
        - (t - (t + k)) * sineSeriesDerivT ν n b 1 (x, t + k)) := by ring
  rw [e, abs_neg]
  exact h

/-- **Centred second difference in space.** Let $\nu \ge 0$, $x \in \mathbb{R}$, $t \ge 0$ and
$h \ge 0$. Then
$$|u(x + h, t) - 2 u(x, t) + u(x - h, t) - h^2 \partial_x^2 u(x, t)| \le \Bigl(\sum_{j < n}
  |b_j| (j + 1)^4\Bigr) \frac{h^4}{12}.$$
-/
theorem abs_sineSeries_centred_sub_le (hν : 0 ≤ ν) {x t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    |sineSeries ν n b (x + h, t) - 2 * sineSeries ν n b (x, t) + sineSeries ν n b (x - h, t)
        - h ^ 2 * sineSeriesDerivX ν n b 2 (x, t)|
      ≤ (∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4) * h ^ 4 / 12 := by
  have hy : ∀ m < 4, ∀ s ∈ Icc (x - h) (x + h),
      HasDerivWithinAt (fun y => sineSeriesDerivX ν n b m (y, t))
        (sineSeriesDerivX ν n b (m + 1) (s, t)) (Icc (x - h) (x + h)) s :=
    fun m _ s _ => (hasDerivAt_sineSeriesDerivX m s t).hasDerivWithinAt
  have hK : ∀ s ∈ Icc (x - h) (x + h),
      ‖sineSeriesDerivX ν n b 4 (s, t)‖ ≤ ∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4 := fun s _ => by
    rw [Real.norm_eq_abs]
    exact abs_sineSeriesDerivX_le hν 4 (p := (s, t)) ht
  have hx : x ∈ Icc (x - h) (x + h) := ⟨by linarith, by linarith⟩
  have hr := norm_sub_sum_smul_le (y := fun m y => sineSeriesDerivX ν n b m (y, t)) 4 hy hK hx
    (right_mem_Icc.2 (by linarith))
  have hl := norm_sub_sum_smul_le (y := fun m y => sineSeriesDerivX ν n b m (y, t)) 4 hy hK hx
    (left_mem_Icc.2 (by linarith))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, smul_eq_mul,
    Real.norm_eq_abs, sineSeriesDerivX_zero, add_sub_cancel_left, sub_sub_cancel_left, abs_neg,
    abs_of_nonneg hh] at hr hl
  push_cast at hr hl
  have e : sineSeries ν n b (x + h, t) - 2 * sineSeries ν n b (x, t) + sineSeries ν n b (x - h, t)
        - h ^ 2 * sineSeriesDerivX ν n b 2 (x, t)
      = (sineSeries ν n b (x + h, t) - (0 + h ^ 0 / 1 * sineSeries ν n b (x, t)
          + h ^ 1 / 1 * sineSeriesDerivX ν n b 1 (x, t)
          + h ^ 2 / 2 * sineSeriesDerivX ν n b 2 (x, t)
          + h ^ 3 / 6 * sineSeriesDerivX ν n b 3 (x, t)))
        + (sineSeries ν n b (x - h, t) - (0 + (-h) ^ 0 / 1 * sineSeries ν n b (x, t)
          + (-h) ^ 1 / 1 * sineSeriesDerivX ν n b 1 (x, t)
          + (-h) ^ 2 / 2 * sineSeriesDerivX ν n b 2 (x, t)
          + (-h) ^ 3 / 6 * sineSeriesDerivX ν n b 3 (x, t))) := by
    ring
  rw [e]
  calc _ ≤ (∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4) * h ^ 4 / 24
        + (∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4) * h ^ 4 / 24 :=
        (abs_add_le _ _).trans (add_le_add hr hl)
    _ = (∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4) * h ^ 4 / 12 := by ring

end SineSeries

end Heat

/-! ### The sine series at $t = 0$ -/

/-- For $x \in [0, \pi]$, the value $u(x, 0)$ of the sine series with coefficients $c$ is the value
at $x$ of the sine polynomial `sinePolynomial n c`, that is, $\sum_{j < n} c_j \sin((j + 1) x)$. -/
theorem Heat.sineSeries_zero_right_eq (ν : ℝ) (n : ℕ) (c : ℕ → ℝ) (x : Icc (0 : ℝ) π) :
    Heat.sineSeries ν n c ((x : ℝ), 0) = sinePolynomial n c x := by
  rw [Heat.sineSeries_zero_right, sinePolynomial_apply]
