/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter13.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter13.Section07

/-!
# Quarteroni, Sacco and Saleri, Section 13.8: Analysis of the finite difference methods

This module formalizes Section 13.8 of [quarteroni2000numerical], the consistency, stability and
convergence of the finite difference schemes of Section 13.7 for the transport equation
$u_t + a u_x = 0$, and of the leap-frog and Newmark schemes for the wave equation. Consistency
(Section 13.8.1) means that the local truncation error $\tau(\Delta t, \Delta x) = \sup_{j,n}
|\tau_j^n|$ tends to $0$. The exact solution of (13.26) is the travelling wave $u_0(x - at)$, so
$\tau_j^n$ is a combination of values of $u_0$ near the foot $\xi = x_j - a t^n$ of the
characteristic. The orders $O(\Delta t + \Delta x^2)$,
$O(\Delta x^2/\Delta t + \Delta t + \Delta x^2)$, $O(\Delta t^2 + \Delta x^2)$ and
$O(\Delta t + \Delta x)$ of Table 13.1 are proved with explicit constants.

Stability (13.46) in the discrete norms (13.47) is a uniform bound on the powers of the scheme over
a finite time interval. The CFL condition $|a\lambda| \le 1$ (13.48) of Section 13.8.3 is necessary
for convergence, because of the numerical domain of dependence: the value at $(0, 1)$ depends on the
datum only on $|x| \le 1/\lambda$, while the exact solution depends on it at $-a$. It is not
sufficient, because the forward Euler/centred scheme satisfies it and is unstable. Under the CFL
condition the upwind and Lax–Friedrichs schemes are monotone, hence nonexpansive in $\ell^1$ and
subject to the discrete maximum principle (13.53). The von Neumann analysis of Section 13.8.4
diagonalizes the periodic scheme in the discrete Fourier basis (13.52): Theorem 13.1 states that
$|\gamma_k| \le 1$ for all amplification factors $\gamma_k$ gives stability in
$\|\cdot\|_{\Delta,2}$. The amplification factors of the four explicit schemes and of the implicit
scheme give the conditions $\lambda |a| \le 1$ for upwind (Exercise 6), $|\lambda a| \le 1$ for
Lax–Friedrichs and Lax–Wendroff, and no condition for backward Euler/centred (Exercise 7). Remark
13.4 on the stability of the leap-frog and Newmark schemes holds in the energy variables of the wave
equation. The proofs specialize the backbone modules `Numlib.FiniteDifference.Stencil`,
`Numlib.FiniteDifference.VonNeumann` and `Numlib.FiniteDifference.Hyperbolic`.

## Main definitions

* Section 13.8.1, `QuarteroniSaccoSaleri.Chapter13.truncationError`: the local truncation error of a
  scheme at the foot $\xi$ of a characteristic.
* Section 13.8.1, `QuarteroniSaccoSaleri.Chapter13.isConsistent`: consistency of a family of
  schemes.
* Section 13.8.1, `QuarteroniSaccoSaleri.Chapter13.isOfOrder`: order $p$ in time and $q$ in space.
* Section 13.8.1, `QuarteroniSaccoSaleri.Chapter13.isConvergent`: convergence of a family of schemes
  on the grid over a finite time interval.
* (13.47), `QuarteroniSaccoSaleri.Chapter13.equation_13_47`: the discrete norms $\|v\|_{\Delta,p}$.
* (13.46), `QuarteroniSaccoSaleri.Chapter13.equation_13_46`: stability of a family of schemes.
* (13.48), `QuarteroniSaccoSaleri.Chapter13.equation_13_48`: the CFL condition $|a\lambda| \le 1$.

## Main results

* Section 13.8.1, `QuarteroniSaccoSaleri.Chapter13.truncationError_eq`: the truncation error is the
  residual of the exact solution in the scheme.
* Section 13.8.1, `QuarteroniSaccoSaleri.Chapter13.isOfOrder_isConsistent`: a scheme of positive
  order in time and in space is consistent.
* Table 13.1, `QuarteroniSaccoSaleri.Chapter13.table_13_1_truncation_forwardEulerCentred`: forward
  Euler/centred has truncation error $O(\Delta t + \Delta x^2)$.
* Table 13.1, `QuarteroniSaccoSaleri.Chapter13.table_13_1_truncation_laxFriedrichs`: Lax–Friedrichs
  has truncation error $O(\Delta x^2/\Delta t + \Delta t + \Delta x^2)$.
* Table 13.1, `QuarteroniSaccoSaleri.Chapter13.table_13_1_truncation_laxWendroff`: Lax–Wendroff has
  truncation error $O(\Delta t^2 + \Delta x^2)$.
* Table 13.1, `QuarteroniSaccoSaleri.Chapter13.table_13_1_truncation_upwind`: upwind has truncation
  error $O(\Delta t + \Delta x)$.
* Section 13.8.1, `QuarteroniSaccoSaleri.Chapter13.leapFrog_truncation`: the leap-frog scheme is
  second order accurate.
* Section 13.8.1, `QuarteroniSaccoSaleri.Chapter13.newmark_truncation`: the Newmark scheme with
  $\theta = 1/2$ is second order accurate.
* Exercise 7, `QuarteroniSaccoSaleri.Chapter13.exercise_13_7`: backward Euler/centred is
  unconditionally stable in $\|\cdot\|_{\Delta,2}$.
* Section 13.8.3, `QuarteroniSaccoSaleri.Chapter13.numericalDomainOfDependence`: after $n$ steps of
  a three-point scheme, the value at $j$ depends only on the values at $j - n, \ldots, j + n$.
* (13.49), `QuarteroniSaccoSaleri.Chapter13.equation_13_49`: the CFL condition holds if and only if
  the domain of dependence lies in the numerical one.
* Section 13.8.3, `QuarteroniSaccoSaleri.Chapter13.cfl_necessary`: if $|a|\lambda > 1$, a
  three-point scheme does not converge for some smooth datum.
* Section 13.8.3, `QuarteroniSaccoSaleri.Chapter13.upwind_isMonotone`: under the CFL condition the
  upwind and Lax–Friedrichs stencils are monotone.
* Section 13.8.3, `QuarteroniSaccoSaleri.Chapter13.upwind_discreteNorm_le`: under the CFL condition
  the upwind scheme is nonexpansive in $\|\cdot\|_{\Delta,1}$.
* Section 13.8.3, `QuarteroniSaccoSaleri.Chapter13.laxFriedrichs_discreteNorm_le`: under the CFL
  condition the Lax–Friedrichs scheme is nonexpansive in $\|\cdot\|_{\Delta,1}$.
* (13.52), `QuarteroniSaccoSaleri.Chapter13.equation_13_52`: each Fourier mode is an eigenvector of
  a periodic scheme, with eigenvalue $\gamma_k$.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.amplificationFactor_forwardEulerCentred`: the
  forward Euler/centred factor $\gamma_k = 1 - i\lambda a \sin\varphi_k$ has $|\gamma_k| > 1$ when
  $\lambda a \sin\varphi_k \neq 0$.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.forwardEulerCentred_not_isStable`: forward
  Euler/centred is unstable for every $\lambda > 0$ and $a \neq 0$.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.exactSolution_abs_le`: the exact solution is
  bounded by the supremum of its datum.
* Theorem 13.1, `QuarteroniSaccoSaleri.Chapter13.theorem_13_1`: if $|\gamma_k| \le 1$ for all $k$,
  the periodic scheme is nonexpansive in the $\ell^2$ norm.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.theorem_13_1_necessary`: a stable periodic scheme
  has $|\gamma_k| \le 1 + 2(C - 1)\Delta t/T$.
* Exercise 6, `QuarteroniSaccoSaleri.Chapter13.exercise_13_6`: the upwind amplification factor, and
  $|\gamma_k| \le 1$ for all $k$ if and only if $\lambda |a| \le 1$.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.upwind_stable_l2`: under the CFL condition the
  periodic upwind scheme is stable in the $\ell^2$ norm.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.amplificationFactor_laxFriedrichs`: the
  Lax–Friedrichs amplification factor, and $|\gamma_k| \le 1$ for all $k$ if and only if
  $|\lambda a| \le 1$.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.amplificationFactor_laxWendroff`: the
  Lax–Wendroff amplification factor, and $|\gamma_k| \le 1$ for all $k$ if and only if
  $|\lambda a| \le 1$.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.laxWendroff_stable`: under the CFL condition the
  periodic Lax–Wendroff scheme is stable in the $\ell^2$ norm.
* Section 13.8.4, `QuarteroniSaccoSaleri.Chapter13.amplificationFactor_backwardEulerCentred`: the
  backward Euler/centred factor $1/(1 + i\lambda a \sin\varphi_k)$ has modulus at most $1$.
* (13.53), `QuarteroniSaccoSaleri.Chapter13.equation_13_53`: the discrete maximum principle for the
  upwind scheme.
* Remark 13.4, `QuarteroniSaccoSaleri.Chapter13.remark_13_4_leapFrog_constantMode`: the leap-frog
  scheme has the unbounded solution $u_j^n = n$ with bounded data.
* Remark 13.4, `QuarteroniSaccoSaleri.Chapter13.remark_13_4_leapFrog`: under the strict CFL
  condition $|\gamma|\lambda < 1$ the leap-frog scheme is stable in the energy variables.
* Remark 13.4, `QuarteroniSaccoSaleri.Chapter13.remark_13_4_newmark`: for
  $2\beta \ge \theta \ge 1/2$ the Newmark scheme is unconditionally stable in the energy variables.

## Implementation notes

* A stencil acts on grid functions $\mathbb{Z} \to \mathbb{R}$; on $\ell^p(\mathbb{Z})$ it is the
  bounded operator `FiniteDifference.Stencil.lpCLM`. The discrete norm is $\|v\|_{\Delta,p} = \Delta
  x^{1/p} \|v\|_{\ell^p}$.
* The von Neumann analysis works on the periodic grid of $N$ points, with complex grid functions in
  `EuclideanSpace ℂ (Fin N)`. A stencil becomes a circulant matrix through
  `FiniteDifference.Stencil.toPeriodic` and `FiniteDifference.periodicScheme`, and the phase of the
  $k$-th mode is $\varphi_k = 2\pi k/N$, `FiniteDifference.Hyperbolic.gridPhase`.
* The truncation error is expressed at the foot $\xi$ of the characteristic, so it is a function of
  the datum $u_0$ of one variable.

## Deviations from the source

* **Residual and consistency in §13.8.1** (correction). The first displayed residual for forward
  Euler/centered subtracts the spatial advection difference. Applying (13.37) gives a plus sign.
  The definitions use the characteristic foot on the whole real line, and the real supremum in
  the consistency predicate defaults to zero for unbounded error. The order estimates state
  global derivative hypotheses and explicit constants. See
  `QuarteroniSaccoSaleri.Chapter13.truncationError_eq` and
  `QuarteroniSaccoSaleri.Chapter13.isConsistent`.
* **Equations (13.46)–(13.49)** (reading). Convergence is uniform over a specified finite
  horizon, and stability uses bounded linear operators on a mesh family. The discrete norm also
  permits general $p$. The domain-of-dependence result gives the stencil cone bound; the cone
  can contain nodes on which a particular stencil does not depend. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_46` and
  `QuarteroniSaccoSaleri.Chapter13.numericalDomainOfDependence`.
* **Equation (13.52) and Theorem 13.1** (specialization). Fourier evolution and the
  contractivity estimates use a finite periodic grid and an arbitrary complex convolution; the
  single-mode formula does not assert convergence of an infinite Fourier series. The forward
  Euler instability theorem exhibits a refining periodic family, and the explicit CFL necessity
  proof concerns convergence. See `QuarteroniSaccoSaleri.Chapter13.theorem_13_1` and
  `QuarteroniSaccoSaleri.Chapter13.cfl_necessary`.
* **Equation (13.53)** (reading). The maximum principle states upper and lower bounds on bounded
  grid data for both upwind directions. At positive speed the two convex-combination weights are
  both nonnegative under CFL, where the source says either is nonnegative. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_53`.
* **CFL condition, Section 13.8.3** (correction). The source presents CFL as equivalent to
  stability. The formal result proves necessity for convergence of three-point schemes. Forward
  Euler/centred can satisfy CFL and still be unstable. See
  `QuarteroniSaccoSaleri.Chapter13.cfl_necessary` and
  `QuarteroniSaccoSaleri.Chapter13.forwardEulerCentred_not_isStable`.
* **Leap-frog accuracy, Section 13.8.1** (generalization). The source states second order accuracy
  for $\Delta t = \Delta x$. The truncation error is $O(\Delta t^2 + \Delta x^2)$ for every ratio
  $\Delta t/\Delta x$. See `QuarteroniSaccoSaleri.Chapter13.leapFrog_truncation`.
* **Newmark accuracy, Section 13.8.1** (correction). The source states second order accuracy for the
  Newmark scheme without a condition. It needs $\theta = 1/2$. See
  `QuarteroniSaccoSaleri.Chapter13.newmark_truncation`.
* **Upwind amplification factor for $a < 0$, Section 13.8.4** (typo). The source prints the factor
  with $e^{-ikh} - 1$; the scheme gives $e^{ikh} - 1$. The modulus and the stability condition do
  not change. See `QuarteroniSaccoSaleri.Chapter13.exercise_13_6`.
* **Remark 13.4, leap-frog** (correction). The source states stability under
  $\Delta t \le \Delta x/|\gamma|$. In the state $(u^{n+1}, u^n)$ this is false for every CFL
  number. The library states stability in the energy variables, under the strict condition
  $|\gamma|\lambda < 1$. See `QuarteroniSaccoSaleri.Chapter13.remark_13_4_leapFrog_constantMode` and
  `QuarteroniSaccoSaleri.Chapter13.remark_13_4_leapFrog`.
* **Remark 13.4, Newmark** (reading). The source does not say in which norm the Newmark scheme is
  stable. The library reads stability in the energy variables. See
  `QuarteroniSaccoSaleri.Chapter13.remark_13_4_newmark`.
-/

open Set Matrix FiniteDifference
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### Section 13.8.1: consistency and order -/

/-- **Section 13.8.1** of [quarteroni2000numerical], the local truncation error. Let $c$ be a
stencil with weights $c_s$, let $a, \Delta t, \Delta x \in \mathbb{R}$ and
$u_0 : \mathbb{R} \to \mathbb{R}$. The **local truncation error** of $c$ for the exact solution
$u_0(x - at)$, at the grid point whose characteristic has the foot $\xi = x_j - a t^n$, is
$$\tau(\xi) = \frac{1}{\Delta t} \Bigl[u_0(\xi - a \Delta t) - \sum_s c_s\, u_0(\xi - s \Delta
  x)\Bigr].$$

The definition is `FiniteDifference.Hyperbolic.truncationError`.

**Typo.** The source's displayed centered-forward residual subtracts the spatial advection
term. The step (13.37) gives a plus sign in the residual. -/
noncomputable def truncationError (c : Stencil) (a Δt Δx : ℝ) (u₀ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  Hyperbolic.truncationError c a Δt Δx u₀ ξ

/-- **Section 13.8.1** of [quarteroni2000numerical], the truncation error as a residual. Let
$a \in \mathbb{R}$, $u_0 : \mathbb{R} \to \mathbb{R}$, let $u$ be a solution of (13.26), let $c$
be a stencil, $\Delta t \ge 0$, $\Delta x \in \mathbb{R}$, $j \in \mathbb{Z}$ and
$n \in \mathbb{N}$. With $x_j = j \Delta x$ and $t^n = n \Delta t$,
$$\tau(x_j - a t^n) = \frac{1}{\Delta t} \Bigl[u(x_j, t^{n+1}) - \bigl(c\, u(\cdot,
  t^n)\bigr)_j\Bigr],$$
where $c$ acts on the grid values $i \mapsto u(x_i, t^n)$.

**Generalization.** The formula concerns arbitrary stencils and includes zero time step under
total division. -/
theorem truncationError_eq {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hu : equation_13_26 a u₀ u)
    (c : Stencil) {Δt Δx : ℝ} (hΔt : 0 ≤ Δt) (j : ℤ) (n : ℕ) :
    truncationError c a Δt Δx u₀ ((j : ℝ) * Δx - a * (n * Δt))
      = (u ((j : ℝ) * Δx) (((n : ℝ) + 1) * Δt)
          - Stencil.apply c (fun i : ℤ => u ((i : ℝ) * Δx) (n * Δt)) j) / Δt :=
  Hyperbolic.truncationError_eq_of_isSolution hu c hΔt j n

/-- **Section 13.8.1** of [quarteroni2000numerical], consistency. Let $c(\Delta t, \Delta x)$ be a
family of stencils, $a \in \mathbb{R}$ and $u_0 : \mathbb{R} \to \mathbb{R}$. The family is
**consistent** if
$$\tau(\Delta t, \Delta x) = \sup_{\xi \in \mathbb{R}} |\tau(\xi)| \to 0$$
as $\Delta t \to 0^+$ and $\Delta x \to 0^+$ independently.

The definition is `FiniteDifference.Hyperbolic.IsConsistent`. The supremum is the Lean supremum
`⨆`, which is $0$ for an unbounded set of values.

**Reading.** The supremum ranges over all real characteristic feet. Lean's real supremum is
zero if the errors are unbounded. -/
def isConsistent (c : ℝ → ℝ → Stencil) (a : ℝ) (u₀ : ℝ → ℝ) : Prop :=
  Hyperbolic.IsConsistent c a u₀

/-- **Section 13.8.1** of [quarteroni2000numerical], the order of a scheme. Let
$c(\Delta t, \Delta x)$ be a family of stencils, $a \in \mathbb{R}$,
$u_0 : \mathbb{R} \to \mathbb{R}$ and $p, q \in \mathbb{N}$. The family has **order $p$ in time
and $q$ in space** if there are $C$ and $\delta_0 > 0$ such that
$$|\tau(\xi)| \le C (\Delta t^p + \Delta x^q)$$
for all $\Delta t, \Delta x \in (0, \delta_0]$ and all $\xi \in \mathbb{R}$.

The definition is `FiniteDifference.Hyperbolic.IsOfOrder`.

**Reading.** The uniform estimate is over real characteristic feet for one fixed datum. Natural
orders, including zero, are represented. -/
def isOfOrder (c : ℝ → ℝ → Stencil) (a : ℝ) (u₀ : ℝ → ℝ) (p q : ℕ) : Prop :=
  Hyperbolic.IsOfOrder c a u₀ p q

/-- **Section 13.8.1** of [quarteroni2000numerical]. Let $c(\Delta t, \Delta x)$ be a family of
stencils, $a \in \mathbb{R}$ and $u_0 : \mathbb{R} \to \mathbb{R}$. If the family has order
$p \neq 0$ in time and $q \neq 0$ in space, then it is consistent.

**Reading.** Uses positive orders and the total-supremum interpretation.
-/
theorem isOfOrder_isConsistent {c : ℝ → ℝ → Stencil} {a : ℝ} {u₀ : ℝ → ℝ} {p q : ℕ} (hp : p ≠ 0)
    (hq : q ≠ 0) (h : isOfOrder c a u₀ p q) : isConsistent c a u₀ :=
  Hyperbolic.IsOfOrder.isConsistent hp hq h

/-- **Table 13.1** of [quarteroni2000numerical], the forward Euler/centred scheme. Let
$u_0 : \mathbb{R} \to \mathbb{R}$ be of class $C^3$ with $|u_0''| \le M_2$ and
$|u_0'''| \le M_3$, let $a \in \mathbb{R}$, $\Delta t, \Delta x > 0$ and
$\lambda = \Delta t/\Delta x$. Then the truncation error of the scheme (13.37) satisfies, for
every $\xi$,
$$|\tau(\xi)| \le \frac{a^2}{2} M_2 \Delta t + \frac{|a|}{6} M_3 \Delta x^2.$$
So the error is $O(\Delta t + \Delta x^2)$.

Table 13.1 gives the same order for the backward Euler/centred scheme; this theorem treats the
forward scheme.

**Reading.** The source gives this order in the prose of §13.8.1. The estimate supplies
explicit global derivative bounds and constants. -/
theorem table_13_1_truncation_forwardEulerCentred {u₀ : ℝ → ℝ} {M₂ M₃ a Δt Δx lam : ℝ}
    (hu : ContDiff ℝ 3 u₀) (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (equation_13_37 a lam) a Δt Δx u₀ ξ|
      ≤ a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2 :=
  Hyperbolic.abs_truncationError_forwardEulerCentred_le hu hM₂ hM₃ hΔt hΔx hlam ξ

/-- **Table 13.1** of [quarteroni2000numerical], the Lax–Friedrichs scheme. Let
$u_0 : \mathbb{R} \to \mathbb{R}$ be of class $C^3$ with $|u_0''| \le M_2$ and
$|u_0'''| \le M_3$, let $a \in \mathbb{R}$, $\Delta t, \Delta x > 0$ and
$\lambda = \Delta t/\Delta x$. Then the truncation error of the scheme (13.39) satisfies, for
every $\xi$,
$$|\tau(\xi)| \le \frac{M_2}{2} \frac{\Delta x^2}{\Delta t} + \frac{a^2}{2} M_2 \Delta t +
  \frac{|a|}{6} M_3 \Delta x^2.$$
So the error is $O(\Delta x^2/\Delta t + \Delta t + \Delta x^2)$.

**Reading.** Under the displayed derivative bounds the pure spatial term is bounded by order
$\Delta x^2$. Table 13.1 gives order $\Delta x$ for that term. -/
theorem table_13_1_truncation_laxFriedrichs {u₀ : ℝ → ℝ} {M₂ M₃ a Δt Δx lam : ℝ}
    (hu : ContDiff ℝ 3 u₀) (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (equation_13_39 a lam) a Δt Δx u₀ ξ|
      ≤ M₂ / 2 * Δx ^ 2 / Δt + a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2 :=
  Hyperbolic.abs_truncationError_laxFriedrichs_le hu hM₂ hM₃ hΔt hΔx hlam ξ

/-- **Table 13.1** of [quarteroni2000numerical], the Lax–Wendroff scheme. Let
$u_0 : \mathbb{R} \to \mathbb{R}$ be of class $C^4$ with $|u_0'''| \le M_3$ and
$|u_0''''| \le M_4$, let $a \in \mathbb{R}$, $0 < \Delta t \le 1$, $0 < \Delta x \le 1$ and
$\lambda = \Delta t/\Delta x$. Then the truncation error of the scheme (13.40) satisfies, for
every $\xi$,
$$|\tau(\xi)| \le \frac{|a|^3}{6} M_3 \Delta t^2 + \Bigl(\frac{|a|}{6} M_3 + \frac{|a| +
  a^2}{24} M_4\Bigr) \Delta x^2.$$
So the error is $O(\Delta t^2 + \Delta x^2)$; it is the only second-order scheme of Section
13.7.

**Reading.** The order estimate makes the global derivative bounds and the small-step range
explicit. -/
theorem table_13_1_truncation_laxWendroff {u₀ : ℝ → ℝ} {M₃ M₄ a Δt Δx lam : ℝ}
    (hu : ContDiff ℝ 4 u₀) (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃)
    (hM₄ : ∀ y, |iteratedDeriv 4 u₀ y| ≤ M₄) (hΔt : 0 < Δt) (hΔt1 : Δt ≤ 1) (hΔx : 0 < Δx)
    (hΔx1 : Δx ≤ 1) (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (equation_13_40 a lam) a Δt Δx u₀ ξ|
      ≤ |a| ^ 3 / 6 * M₃ * Δt ^ 2 + (|a| / 6 * M₃ + (|a| + a ^ 2) / 24 * M₄) * Δx ^ 2 :=
  Hyperbolic.abs_truncationError_laxWendroff_le hu hM₃ hM₄ hΔt hΔt1 hΔx hΔx1 hlam ξ

/-- **Table 13.1** of [quarteroni2000numerical], the upwind scheme. Let
$u_0 : \mathbb{R} \to \mathbb{R}$ be of class $C^2$ with $|u_0''| \le M_2$, let
$a \in \mathbb{R}$, $\Delta t, \Delta x > 0$ and $\lambda = \Delta t/\Delta x$. Then the
truncation error of the scheme (13.41) satisfies, for every $\xi$,
$$|\tau(\xi)| \le \frac{a^2}{2} M_2 \Delta t + \frac{|a|}{2} M_2 \Delta x.$$
So the error is $O(\Delta t + \Delta x)$.

**Reading.** The estimate makes the second derivative bound and its constants explicit. -/
theorem table_13_1_truncation_upwind {u₀ : ℝ → ℝ} {M₂ a Δt Δx lam : ℝ} (hu : ContDiff ℝ 2 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (equation_13_41 a lam) a Δt Δx u₀ ξ|
      ≤ a ^ 2 / 2 * M₂ * Δt + |a| / 2 * M₂ * Δx :=
  Hyperbolic.abs_truncationError_upwind_le hu hM₂ hΔt hΔx hlam ξ

/-- **Section 13.8.1** of [quarteroni2000numerical], accuracy of the leap-frog scheme. Let
$u : \mathbb{R}^2 \to \mathbb{R}$ have iterated partial derivatives
$D_{ij} = \partial_x^i \partial_t^j u$ of all orders, with $|\partial_t^4 u| \le M$ and
$|\partial_x^4 u| \le M'$ on $\mathbb{R}^2$. Let $\gamma \in \mathbb{R}$ and
$\Delta t, \Delta x > 0$. Then for all $x, t$,
$$\Bigl|\frac{u(x, t + \Delta t) - 2u(x, t) + u(x, t - \Delta t)}{\Delta t^2} - \gamma^2
  \frac{u(x + \Delta x, t) - 2u(x, t) + u(x - \Delta x, t)}{\Delta x^2} - (u_{tt} - \gamma^2
  u_{xx})(x, t)\Bigr| \le \frac{M}{12} \Delta t^2 + \frac{\gamma^2 M'}{12} \Delta x^2.$$
On a solution of the wave equation the last term in the absolute value vanishes, so the
truncation error of (13.44) is $O(\Delta t^2 + \Delta x^2)$.

**Generalization.** The source states that the leap-frog method is second order accurate if
$\Delta t = \Delta x$. The bound holds for every ratio $\Delta t/\Delta x$.

The family $D$ is `HasPartialDerivs u D`. Each second central difference is a symmetric Taylor
expansion of third order, whose odd terms cancel. The proof specializes
`FiniteDifference.Hyperbolic.abs_residual_leapFrog_le`. -/
theorem leapFrog_truncation {u : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {γ M M' Δt Δx : ℝ}
    (hD : HasPartialDerivs u D) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hM : ∀ y s, |D 0 4 y s| ≤ M) (hM' : ∀ y s, |D 4 0 y s| ≤ M') (x t : ℝ) :
    |(u x (t + Δt) - 2 * u x t + u x (t - Δt)) / Δt ^ 2
        - γ ^ 2 * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2)
        - (D 0 2 x t - γ ^ 2 * D 2 0 x t)|
      ≤ M / 12 * Δt ^ 2 + γ ^ 2 * M' / 12 * Δx ^ 2 :=
  Hyperbolic.abs_residual_leapFrog_le hD hΔt hΔx hM hM' x t


/-- **Section 13.8.1** of [quarteroni2000numerical], accuracy of the Newmark scheme. Let
$u : \mathbb{R}^2 \to \mathbb{R}$ have iterated partial derivatives
$D_{ij} = \partial_x^i \partial_t^j u$ of all orders, with $|D_{ij}| \le M$ on $\mathbb{R}^2$
for all $i + j \le 4$, and let $u$ solve the wave equation $u_{tt} = \gamma^2 u_{xx}$ on
$\mathbb{R}^2$. Let $\beta \in \mathbb{R}$, $0 < \Delta t \le 1$, $\Delta x > 0$ and
$\lambda = \Delta t/\Delta x$, and write $\delta^2 w(x) = w(x + \Delta x) - 2w(x) + w(x - \Delta
x)$. Insert $u$ and $v = u_t$ into the two relations of (13.45) and divide by $\Delta t$. Then
for all $x, t$ the first residual satisfies
$$\Bigl|\frac{1}{\Delta t}\Bigl[u(x, t + \Delta t) - u(x, t) - \Delta t\, u_t(x, t) -
  (\gamma\lambda)^2 \bigl(\beta\, \delta^2 u(x, t + \Delta t) + (\tfrac{1}{2} - \beta)\,
  \delta^2 u(x, t)\bigr)\Bigr]\Bigr| \le M \Bigl[\Bigl(\frac{1}{6} + \frac{3}{2} \gamma^2
  |\beta|\Bigr) \Delta t^2 + \frac{\gamma^2 (|\beta| + |\tfrac{1}{2} - \beta|)}{12} \Delta
  x^2\Bigr],$$
and for $\theta = 1/2$ the second residual satisfies
$$\Bigl|\frac{1}{\Delta t}\Bigl[u_t(x, t + \Delta t) - u_t(x, t) -
  \frac{(\gamma\lambda)^2}{\Delta t} \bigl(\tfrac{1}{2}\, \delta^2 u(x, t + \Delta t) +
  \tfrac{1}{2}\, \delta^2 u(x, t)\bigr)\Bigr]\Bigr| \le M \Bigl[\Bigl(\frac{1}{6} +
  \frac{\gamma^2}{4}\Bigr) \Delta t^2 + \frac{\gamma^2}{12} \Delta x^2\Bigr].$$
So both residuals are $O(\Delta t^2 + \Delta x^2)$: the first for every $\beta$, the second for
$\theta = 1/2$.

**Correction.** The source states that the Newmark method is second order accurate, without a
condition on $\theta$. The velocity update is the $\theta$-method for $v' = u_{tt}$, and its
leading error term is $(\frac{1}{2} - \theta) \Delta t\, u_{ttt}$, which vanishes only for
$\theta = 1/2$. The theorem states the case $\theta = 1/2$. The numerical experiments of Table
13.3 of the source use $\theta = 1/2$.

The first estimate uses the wave equation, and the second uses it differentiated once in time,
$u_{ttt} = \gamma^2 u_{xxt}$. The proof specializes
`FiniteDifference.Hyperbolic.abs_residual_newmark_le`. -/
theorem newmark_truncation {u : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {γ β M Δt Δx lam : ℝ}
    (hD : HasPartialDerivs u D) (hΔt : 0 < Δt) (hΔt1 : Δt ≤ 1) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (hwave : ∀ y s, D 0 2 y s = γ ^ 2 * D 2 0 y s)
    (hM : ∀ i j, i + j ≤ 4 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |(u x (t + Δt) - u x t - (Δt * D 0 1 x t
          + (γ * lam) ^ 2
            * (β * (u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt))
              + (1 / 2 - β) * (u (x + Δx) t - 2 * u x t + u (x - Δx) t)))) / Δt|
        ≤ M * ((1 / 6 + 3 / 2 * γ ^ 2 * |β|) * Δt ^ 2
          + γ ^ 2 * (|β| + |1 / 2 - β|) / 12 * Δx ^ 2) ∧
      |(D 0 1 x (t + Δt) - D 0 1 x t - (γ * lam) ^ 2 / Δt
          * (1 / 2 * (u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt))
            + (1 - 1 / 2) * (u (x + Δx) t - 2 * u x t + u (x - Δx) t))) / Δt|
        ≤ M * ((1 / 6 + γ ^ 2 / 4) * Δt ^ 2 + γ ^ 2 / 12 * Δx ^ 2) :=
  Hyperbolic.abs_residual_newmark_le hD hΔt hΔt1 hΔx hlam hwave hM x t
/-- **Section 13.8.1** of [quarteroni2000numerical], convergence. Let $a \in \mathbb{R}$,
$u_0 : \mathbb{R} \to \mathbb{R}$, let $c(\Delta t, \Delta x)$ be a family of stencils and
$T \in \mathbb{R}$. The family is **convergent** over $[0, T]$ if for every $\varepsilon > 0$
there is $\delta_0 > 0$ such that for all $\Delta t, \Delta x \in (0, \delta_0]$ and all $n, j$
with $n \Delta t \le T$
$$\bigl|u_0(x_j - a t^n) - \bigl(c(\Delta t, \Delta x)^n u_0|_{\text{grid}}\bigr)_j\bigr| \le
  \varepsilon,$$
where $u_0|_{\text{grid}}$ is the grid function $i \mapsto u_0(x_i)$.

The definition is `FiniteDifference.Hyperbolic.IsConvergent`. The steps $\Delta t$ and
$\Delta x$ tend to $0$ independently.

**Reading.** Convergence is uniform on the grid up to a specified finite time $T$ and uses the
exact transported datum. -/
def isConvergent (a : ℝ) (u₀ : ℝ → ℝ) (c : ℝ → ℝ → Stencil) (T : ℝ) : Prop :=
  Hyperbolic.IsConvergent a u₀ c T

/-! ### Section 13.8.2: the discrete norms and stability -/

/-- **Equation (13.47)** of [quarteroni2000numerical], the discrete norms. For $p \in [1, \infty]$,
$\Delta x \in \mathbb{R}$ and $v \in \ell^p(\mathbb{Z})$,
$$\|v\|_{\Delta,p} = \Delta x^{1/p} \|v\|_{\ell^p} = \Bigl(\Delta x \sum_j |v_j|^p\Bigr)^{1/p}$$
for finite $p$ and $\Delta x \ge 0$, and $\|v\|_{\Delta,\infty} = \sup_j |v_j|$.

The definition is `FiniteDifference.discreteNorm`.

**Generalization.** The formula is defined for general $p$, including the printed
$p=1,2,\infty$. -/
noncomputable def equation_13_47 (p : ℝ≥0∞) (Δx : ℝ) (v : lp (fun _ : ℤ => ℝ) p) : ℝ :=
  FiniteDifference.discreteNorm p Δx v

/-- **Equation (13.46)** of [quarteroni2000numerical], stability. Let $(Q_i)$ be a family of bounded
operators on normed spaces $E_i$, with time steps $\Delta t_i$ and space steps $\Delta x_i$. The
family is **stable** if for every $T > 0$ there are $C_T$ and $\delta_0 > 0$ such that
$$\|Q_i^n\| \le C_T$$
whenever $\Delta t_i, \Delta x_i \in (0, \delta_0]$ and $n \Delta t_i \le T$. For grid functions
this is $\|u^n\|_\Delta \le C_T \|u^0\|_\Delta$.

The definition is `FiniteDifference.IsStableFamily`. The spaces $E_i$ may depend on $i$, so that
periodic grids and the whole line are both covered.

**Reading.** The stability definition quantifies over bounded linear operators on a family of
meshes. The source also discusses nonlinear updates. -/
def equation_13_46 {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (Δt Δx : ι → ℝ) (Q : ∀ i, E i →L[ℝ] E i) : Prop :=
  FiniteDifference.IsStableFamily Δt Δx Q

/-- **Exercise 7 of Chapter 13** of [quarteroni2000numerical]. Let $a, \lambda \in \mathbb{R}$,
$\Delta x \ge 0$ and $u \in \ell^2(\mathbb{Z})$. The implicit backward Euler/centred scheme
(13.43) satisfies
$$\|B^{-1} u\|_{\Delta,2} \le \|u\|_{\Delta,2},$$
so it is unconditionally stable in $\|\cdot\|_{\Delta,2}$ with constant $1$. Section 13.8.2 of
the source uses this result.

The reason is that the centred difference is skew-adjoint, so $\langle Bu, u \rangle = \|u\|^2$.

**Reading.** One-step estimate on all ℓ² inputs with nonnegative spatial scale.
-/
theorem exercise_13_7 {a lam Δx : ℝ} (hΔx : 0 ≤ Δx) (u : lp (fun _ : ℤ => ℝ) 2) :
    equation_13_47 2 Δx (equation_13_43 a lam u) ≤ equation_13_47 2 Δx u := by
  refine mul_le_mul_of_nonneg_left (Hyperbolic.norm_backwardEulerCentred_apply_le a lam u)
    (Real.rpow_nonneg hΔx _)

/-! ### Section 13.8.3: the CFL condition -/

/-- **Equation (13.48)** of [quarteroni2000numerical], the CFL condition. For
$a, \lambda \in \mathbb{R}$, the **CFL condition** is
$$|a\lambda| \le 1.$$
The number $a\lambda$ is the CFL number.

The definition is `FiniteDifference.Hyperbolic.CFL`. The variants of Section 13.8.3 for a
variable speed field and for a hyperbolic system are `FiniteDifference.Hyperbolic.CFLVariable`
and `FiniteDifference.Hyperbolic.CFLSystem`. -/
def equation_13_48 (a lam : ℝ) : Prop := Hyperbolic.CFL a lam

/-- **Section 13.8.3** of [quarteroni2000numerical], the numerical domain of dependence. Let $c$ be
a stencil with $c_s = 0$ for $|s| > 1$, let $n \in \mathbb{N}$, $j \in \mathbb{Z}$, and let
$u, v : \mathbb{Z} \to \mathbb{R}$ with $u_i = v_i$ whenever $|i - j| \le n$. Then
$$(c^n u)_j = (c^n v)_j.$$
So the numerical domain of dependence of $(x_j, t^n)$ lies in
$\{x : |x - x_j| \le n \Delta x = t^n/\lambda\}$.

**Reading.** The cone bounds the possible dependence. It is an upper bound even when some
stencil weights vanish. -/
theorem numericalDomainOfDependence {c : Stencil} (hc : ∀ s ∈ c.support, |s| ≤ 1) (n : ℕ)
    {u v : ℤ → ℝ} {j : ℤ} (h : ∀ i : ℤ, |i - j| ≤ (n : ℤ) → u i = v i) :
    (Stencil.apply c)^[n] u j = (Stencil.apply c)^[n] v j :=
  Stencil.iterate_apply_congr_of_eqOn hc n (by simpa using h)

/-- **Equation (13.49)** of [quarteroni2000numerical]. Let $a \in \mathbb{R}$, $\lambda > 0$,
$\bar x \in \mathbb{R}$ and $\bar t > 0$. Then the CFL condition $|a\lambda| \le 1$ holds if and
only if the domain of dependence $\{\bar x - a \bar t\}$ of (13.31) lies in the limit numerical
domain of dependence $\{x : |x - \bar x| \le \bar t/\lambda\}$, that is,
$$|(\bar x - a \bar t) - \bar x| \le \bar t/\lambda.$$

**Specialization.** The characteristic-foot inequality is the scalar, positive-time and
positive-mesh-ratio case. -/
theorem equation_13_49 {a lam xb tb : ℝ} (hlam : 0 < lam) (htb : 0 < tb) :
    equation_13_48 a lam ↔ |(xb - a * tb) - xb| ≤ tb / lam := by
  rw [equation_13_48, Hyperbolic.CFL, show (xb - a * tb) - xb = -(a * tb) from by ring, abs_neg,
    abs_mul, abs_mul, abs_of_pos htb, abs_of_pos hlam, le_div_iff₀ hlam]
  constructor <;> intro h <;> nlinarith [abs_nonneg a]

/-- **Section 13.8.3** of [quarteroni2000numerical], the CFL condition is necessary for convergence.
Let $a \in \mathbb{R}$ and $\lambda > 0$ with $|a| \lambda > 1$, and let $c(\Delta t, \Delta x)$
be a family of stencils whose weights $c_s$ vanish for $|s| > 1$. Then there is a smooth
($C^\infty$) datum $u_0$ for which the family is not convergent over $[0, 1]$.

**Correction.** The source calls the CFL condition necessary and sufficient. It is not
sufficient: the forward Euler/centred scheme satisfies it and is unstable (see
`QuarteroniSaccoSaleri.Chapter13.forwardEulerCentred_not_isStable`). Only the necessary half is
stated.

The numerical value at $(0, 1)$ depends on the datum only on $|x| \le 1/\lambda$, while the
exact solution there is $u_0(-a)$. A smooth bump datum concentrated at $-a$, with $u_0(-a) = 1$,
vanishes on $|x| \le 1/\lambda$. Convergence in the sense of
`QuarteroniSaccoSaleri.Chapter13.isConvergent` asks for all small $\Delta t$ and $\Delta x$
independently, and the number $\lambda$ is not tied to the family $c$. The proof specializes
`FiniteDifference.Hyperbolic.not_isConvergent_of_one_lt_abs_mul`.

**Reading.** The counterexample proves necessity for convergence on the unit time horizon. -/
theorem cfl_necessary {a lam : ℝ} (hlam : 0 < lam) (hcfl : 1 < |a| * lam)
    (c : ℝ → ℝ → Stencil) (hc : ∀ Δt Δx : ℝ, ∀ s ∈ (c Δt Δx).support, |s| ≤ 1) :
    ∃ u₀ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u₀ ∧ ¬isConvergent a u₀ c 1 :=
  Hyperbolic.not_isConvergent_of_one_lt_abs_mul hlam hcfl c hc

/-- **Section 13.8.3** of [quarteroni2000numerical], monotonicity. Let $a, \lambda \in \mathbb{R}$
with $0 \le \lambda |a| \le 1$ and $|\lambda a| \le 1$. Then the upwind stencil (13.41) and the
Lax–Friedrichs stencil (13.39) are monotone: their weights are nonnegative and sum to $1$.

Monotonicity is `FiniteDifference.Stencil.IsMonotone`.

**Generalization.** The theorem packages the convex stencil conditions for both schemes and
covers both upwind directions. -/
theorem upwind_isMonotone {a lam : ℝ} (h0 : 0 ≤ lam * |a|) (h1 : lam * |a| ≤ 1)
    (h2 : |lam * a| ≤ 1) :
    Stencil.IsMonotone (equation_13_41 a lam) ∧ Stencil.IsMonotone (equation_13_39 a lam) :=
  ⟨Hyperbolic.upwind_isMonotone h0 h1, Hyperbolic.laxFriedrichs_isMonotone h2⟩

/-- **Section 13.8.3** of [quarteroni2000numerical], $\ell^1$ stability of the upwind scheme. Let
$a, \lambda \in \mathbb{R}$ with $0 \le \lambda |a| \le 1$, let $\Delta x \ge 0$ and
$u \in \ell^1(\mathbb{Z})$. Then one step $Q$ of the upwind scheme (13.41) satisfies
$$\|Q u\|_{\Delta,1} \le \|u\|_{\Delta,1},$$
so (13.46) holds with $C_T = 1$.

**Reading.** Same one-step ℓ¹ contraction for either sign of speed and nonnegative spatial scale.
-/
theorem upwind_discreteNorm_le {a lam Δx : ℝ} (hΔx : 0 ≤ Δx) (h0 : 0 ≤ lam * |a|)
    (h1 : lam * |a| ≤ 1) (u : lp (fun _ : ℤ => ℝ) 1) :
    equation_13_47 1 Δx (Stencil.lpCLM (equation_13_41 a lam) 1 u) ≤ equation_13_47 1 Δx u :=
  mul_le_mul_of_nonneg_left
    ((Hyperbolic.upwind_isMonotone h0 h1).norm_lpCLM_apply_le u) (Real.rpow_nonneg hΔx _)

/-- **Section 13.8.3** of [quarteroni2000numerical], $\ell^1$ stability of the Lax–Friedrichs
scheme. Let $a, \lambda \in \mathbb{R}$ with $|\lambda a| \le 1$, let $\Delta x \ge 0$ and
$u \in \ell^1(\mathbb{Z})$. Then one step $Q$ of the Lax–Friedrichs scheme (13.39) satisfies
$$\|Q u\|_{\Delta,1} \le \|u\|_{\Delta,1}.$$
-/
theorem laxFriedrichs_discreteNorm_le {a lam Δx : ℝ} (hΔx : 0 ≤ Δx) (h : |lam * a| ≤ 1)
    (u : lp (fun _ : ℤ => ℝ) 1) :
    equation_13_47 1 Δx (Stencil.lpCLM (equation_13_39 a lam) 1 u) ≤ equation_13_47 1 Δx u :=
  mul_le_mul_of_nonneg_left
    ((Hyperbolic.laxFriedrichs_isMonotone h).norm_lpCLM_apply_le u) (Real.rpow_nonneg hΔx _)

/-! ### Section 13.8.4: the von Neumann analysis -/

/-- **Equation (13.52)** of [quarteroni2000numerical]. Let $N \in \mathbb{N}$, let
$c \in \mathbb{C}^N$ be the weights of a scheme with constant coefficients on the periodic grid
of $N$ points, and let $Q$ be its circulant matrix. Then for every $k$ and $n$ the Fourier mode
$e_k$, $(e_k)_j = e^{2\pi i jk/N}$, satisfies
$$Q^n e_k = \gamma_k^n e_k,$$
where $\gamma_k$ is the amplification factor of the $k$-th mode. So the scheme multiplies the
$k$-th Fourier coefficient of $u^0$ by $\gamma_k^n$, which gives the representation
$u_j^n = \sum_k \alpha_k \gamma_k^n e^{ikjh}$ of (13.52).

The matrix $Q$ is `FiniteDifference.periodicScheme c`, and the mode is
`FiniteDifference.fourierMode`. The amplification factor is
`FiniteDifference.amplificationFactor c k`, the discrete Fourier transform of $c$ at $k$.

**Specialization.** The theorem gives exact evolution of one mode on a finite periodic grid,
for a general convolution. -/
theorem equation_13_52 {N : ℕ} (c : Fin N → ℂ) (k : Fin N) (n : ℕ) :
    (FiniteDifference.periodicScheme c ^ n) *ᵥ FiniteDifference.fourierMode N k
      = FiniteDifference.amplificationFactor c k ^ n • FiniteDifference.fourierMode N k :=
  FiniteDifference.periodicScheme_pow_mulVec_fourierMode c k n

/-- **Section 13.8.4** of [quarteroni2000numerical], the forward Euler/centred amplification factor.
Let $N \ge 1$, $a, \lambda \in \mathbb{R}$ and $\varphi_k = 2\pi k/N$. The amplification factor
of the scheme (13.37) on the periodic grid of $N$ points is
$$\gamma_k = 1 - i \lambda a \sin\varphi_k, \qquad |\gamma_k|^2 = 1 + (\lambda a
  \sin\varphi_k)^2,$$
and $|\gamma_k| > 1$ whenever $\lambda a \sin\varphi_k \neq 0$. So the scheme is unconditionally
unstable.

**Specialization.** The amplification factor and its growth condition are on a finite periodic
grid. -/
theorem amplificationFactor_forwardEulerCentred {N : ℕ} [NeZero N] (a lam : ℝ) (k : Fin N) :
    FiniteDifference.amplificationFactor
        (Stencil.toPeriodic N (equation_13_37 a lam)) k
        = 1 - Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ) ∧
      ‖FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_37 a lam)) k‖ ^ 2
        = 1 + (lam * a) ^ 2 * Real.sin (Hyperbolic.gridPhase N k) ^ 2 ∧
      (lam * a * Real.sin (Hyperbolic.gridPhase N k) ≠ 0 →
        1 < ‖FiniteDifference.amplificationFactor
          (Stencil.toPeriodic N (equation_13_37 a lam)) k‖) :=
  ⟨Hyperbolic.amplificationFactor_forwardEulerCentred a lam k,
    Hyperbolic.norm_amplificationFactor_forwardEulerCentred_sq a lam k,
    fun h => Hyperbolic.one_lt_norm_amplificationFactor_forwardEulerCentred h⟩

/-- **Section 13.8.4** of [quarteroni2000numerical], instability of the forward Euler/centred
scheme. Let $a \neq 0$ and $\lambda > 0$. The family of the schemes (13.37) on the periodic
grids of $m + 8$ points, $m \in \mathbb{N}$, with $\Delta x = 2\pi/(m + 8)$ and
$\Delta t = \lambda \Delta x$, is not stable in the sense of (13.46) for the $\ell^2$ norm. So
the CFL condition is not sufficient for stability.

On every grid the mode nearest to $\varphi = \pi/2$ has
$|\gamma_k| \ge \sqrt{1 + (\lambda a)^2/2} > 1$. The family is
`FiniteDifference.Hyperbolic.forwardEulerCentredFamily`, as real-linear operators on
`EuclideanSpace ℂ (Fin (m + 8))`.

**Reading.** The instability is witnessed by a concrete refining periodic family with fixed
positive mesh ratio and nonzero speed. -/
theorem forwardEulerCentred_not_isStable {a lam : ℝ} (ha : a ≠ 0) (hlam : 0 < lam) :
    ¬equation_13_46 (fun m : ℕ => lam * (2 * Real.pi / (m + 8)))
      (fun m : ℕ => 2 * Real.pi / (m + 8)) (Hyperbolic.forwardEulerCentredFamily a lam) :=
  Hyperbolic.forwardEulerCentred_not_isStableFamily ha hlam

/-- **Section 13.8.4** of [quarteroni2000numerical], the bound of the exact solution. Let
$a \in \mathbb{R}$, let $u_0 : \mathbb{R} \to \mathbb{R}$ have $|u_0|$ bounded above, and let
$u$ be a solution of (13.26). Then for all $x$ and all $t \ge 0$
$$|u(x, t)| = |u_0(x - at)| \le \sup_s |u_0(s)|.$$
The growth of the centred scheme is measured against this bound.

**Generalization.** A real supremum replaces the maximum. Bounded initial data suffice. -/
theorem exactSolution_abs_le {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hu : equation_13_26 a u₀ u)
    (hb : BddAbove (range fun s => |u₀ s|)) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |u x t| ≤ ⨆ s, |u₀ s| :=
  hu.abs_le_sup hb x ht

/-- **Theorem 13.1** of [quarteroni2000numerical]. Let $N \in \mathbb{N}$ and let
$c \in \mathbb{C}^N$ be the weights of a periodic scheme $Q$ with amplification factors
$\gamma_k$. If $|\gamma_k| \le 1$ for every $k$, then for all $n \in \mathbb{N}$ and
$u \in \mathbb{C}^N$
$$\|Q^n u\|_2 \le \|u\|_2.$$
So the scheme is stable in $\|\cdot\|_{\Delta,2}$ with constant $1$.

The proof uses the discrete Parseval identity, from Lemma 10.1 of the source.

**Reading.** The result is power contractivity for a finite periodic convolution, the setting
of the source's proof. -/
theorem theorem_13_1 {N : ℕ} (c : Fin N → ℂ)
    (h : ∀ k, ‖FiniteDifference.amplificationFactor c k‖ ≤ 1) (n : ℕ)
    (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (FiniteDifference.periodicScheme c ^ n) u‖ ≤ ‖u‖ :=
  FiniteDifference.norm_toEuclideanLin_periodicScheme_pow_le c h n u

/-- **Section 13.8.4** of [quarteroni2000numerical], the converse of Theorem 13.1, which the source
uses in its proof of instability. Let $N \in \mathbb{N}$, $c \in \mathbb{C}^N$ the weights of a
periodic scheme $Q$, $C \ge 1$, $\Delta t > 0$ and $T \ge 2\Delta t$, and suppose that
$\|Q^n\| \le C$ whenever $n \Delta t \le T$. Then for every $k$:

* $|\gamma_k|^n \le \|Q^n\|$ for every $n \in \mathbb{N}$;
* $|\gamma_k| \le 1 + 2(C - 1)\Delta t/T$.

The operator norm is the norm of `Matrix.toEuclideanCLM`, the matrix as an operator on
$\mathbb{C}^N$ with the Euclidean norm. -/
theorem theorem_13_1_necessary {N : ℕ} (c : Fin N → ℂ) {C Δt T : ℝ} (hC : 1 ≤ C) (hΔt : 0 < Δt)
    (hΔT : Δt ≤ T / 2)
    (hstab : ∀ n : ℕ, (n : ℝ) * Δt ≤ T →
      ‖toEuclideanCLM (𝕜 := ℂ) (FiniteDifference.periodicScheme c ^ n)‖ ≤ C) (k : Fin N) :
    (∀ n : ℕ, ‖FiniteDifference.amplificationFactor c k‖ ^ n
        ≤ ‖toEuclideanCLM (𝕜 := ℂ) (FiniteDifference.periodicScheme c ^ n)‖) ∧
      ‖FiniteDifference.amplificationFactor c k‖ ≤ 1 + 2 * (C - 1) * Δt / T :=
  ⟨fun n => FiniteDifference.norm_amplificationFactor_pow_le c k n,
    FiniteDifference.norm_amplificationFactor_le_one_add_of_forall_norm_pow_le c hC hΔt hΔT
      hstab k⟩

/-- **Exercise 6 of Chapter 13** of [quarteroni2000numerical], the upwind amplification factor. Let
$N \ge 2$, $a \in \mathbb{R}$, $\lambda \ge 0$ and $\varphi_k = 2\pi k/N$. The amplification
factor of the upwind scheme (13.41) on the periodic grid of $N$ points is
$$\gamma_k = 1 - \lambda |a| (1 - \cos\varphi_k) - i \lambda a \sin\varphi_k,$$
for both signs of $a$, and
$$|\gamma_k|^2 = 1 - 2\lambda |a| (1 - \lambda |a|)(1 - \cos\varphi_k).$$
Hence $|\gamma_k| \le 1$ for every $k$ if and only if $\lambda |a| \le 1$, the CFL condition.

**Typo.** For $a < 0$, Section 13.8.4 of the source prints the amplification factor with
$e^{-ikh} - 1$. The scheme gives $e^{ikh} - 1$. The modulus, and so the stability condition,
does not change. The single formula above covers both signs, as does
`FiniteDifference.Hyperbolic.amplificationFactor_upwind`. -/
theorem exercise_13_6 {N : ℕ} [NeZero N] (hN : 2 ≤ N) {a lam : ℝ} (hlam : 0 ≤ lam) (k : Fin N) :
    FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_41 a lam)) k
        = ((1 - lam * |a| * (1 - Real.cos (Hyperbolic.gridPhase N k)) : ℝ) : ℂ)
          - Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ) ∧
      ‖FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_41 a lam)) k‖ ^ 2
        = 1 - 2 * (lam * |a|) * (1 - lam * |a|)
          * (1 - Real.cos (Hyperbolic.gridPhase N k)) ∧
      ((∀ k : Fin N, ‖FiniteDifference.amplificationFactor
          (Stencil.toPeriodic N (equation_13_41 a lam)) k‖ ≤ 1) ↔ lam * |a| ≤ 1) :=
  ⟨Hyperbolic.amplificationFactor_upwind a lam k,
    Hyperbolic.norm_amplificationFactor_upwind_sq a lam k,
    Hyperbolic.norm_amplificationFactor_upwind_le_one_iff hN hlam⟩

/-- **Section 13.8.4** of [quarteroni2000numerical], $\ell^2$ stability of the upwind scheme. Let
$N \ge 2$, $a \in \mathbb{R}$ and $\lambda \ge 0$ with $\lambda |a| \le 1$, and let $Q$ be the
upwind scheme (13.41) on the periodic grid of $N$ points. Then for all $n$ and
$u \in \mathbb{C}^N$
$$\|Q^n u\|_2 \le \|u\|_2.$$

This follows from Theorem 13.1 and Exercise 6.

**Specialization.** The contractivity conclusion is for the finite periodic grid. -/
theorem upwind_stable_l2 {N : ℕ} [NeZero N] (hN : 2 ≤ N) {a lam : ℝ} (hlam : 0 ≤ lam)
    (h : lam * |a| ≤ 1) (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin
        (FiniteDifference.periodicScheme (Stencil.toPeriodic N (equation_13_41 a lam)) ^ n) u‖
      ≤ ‖u‖ :=
  theorem_13_1 _ ((Hyperbolic.norm_amplificationFactor_upwind_le_one_iff hN hlam).2 h) n u

/-- **Section 13.8.4** of [quarteroni2000numerical], the Lax–Friedrichs amplification factor (see
also Figure 13.7). Let $N \ge 3$, $a, \lambda \in \mathbb{R}$ and $\varphi_k = 2\pi k/N$. The
amplification factor of the scheme (13.39) on the periodic grid of $N$ points is
$$\gamma_k = \cos\varphi_k - i \lambda a \sin\varphi_k, \qquad |\gamma_k|^2 = \cos^2\varphi_k +
  (\lambda a)^2 \sin^2\varphi_k,$$
and $|\gamma_k| \le 1$ for every $k$ if and only if $|\lambda a| \le 1$.

**Reading.** This derives the periodic Fourier factor and sharp CFL test for the Lax–Friedrichs
stencil. -/
theorem amplificationFactor_laxFriedrichs {N : ℕ} [NeZero N] (hN : 3 ≤ N) (a lam : ℝ)
    (k : Fin N) :
    FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_39 a lam)) k
        = (Real.cos (Hyperbolic.gridPhase N k) : ℂ)
          - Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ) ∧
      ‖FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_39 a lam)) k‖ ^ 2
        = Real.cos (Hyperbolic.gridPhase N k) ^ 2
          + (lam * a) ^ 2 * Real.sin (Hyperbolic.gridPhase N k) ^ 2 ∧
      ((∀ k : Fin N, ‖FiniteDifference.amplificationFactor
          (Stencil.toPeriodic N (equation_13_39 a lam)) k‖ ≤ 1) ↔ |lam * a| ≤ 1) :=
  ⟨Hyperbolic.amplificationFactor_laxFriedrichs a lam k,
    Hyperbolic.norm_amplificationFactor_laxFriedrichs_sq a lam k,
    Hyperbolic.norm_amplificationFactor_laxFriedrichs_le_one_iff hN a lam⟩

/-- **Section 13.8.4** of [quarteroni2000numerical], the Lax–Wendroff amplification factor (see also
Figure 13.7). Let $N \ge 2$, $a, \lambda \in \mathbb{R}$ and $\varphi_k = 2\pi k/N$. The
amplification factor of the scheme (13.40) on the periodic grid of $N$ points is
$$\gamma_k = 1 - (\lambda a)^2 (1 - \cos\varphi_k) - i \lambda a \sin\varphi_k, \qquad
  |\gamma_k|^2 = 1 - (\lambda a)^2 (1 - (\lambda a)^2)(1 - \cos\varphi_k)^2,$$
and $|\gamma_k| \le 1$ for every $k$ if and only if $|\lambda a| \le 1$.

The source writes the modulus as $|\gamma_k|^2 = 1 - 4(\lambda a)^2 (1 - (\lambda a)^2)
\sin^4(\varphi_k/2)$, which is the same.

**Reading.** This gives the periodic Fourier factor and sharp CFL test for the Lax–Wendroff
stencil. -/
theorem amplificationFactor_laxWendroff {N : ℕ} [NeZero N] (hN : 2 ≤ N) (a lam : ℝ) (k : Fin N) :
    FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_40 a lam)) k
        = ((1 - (lam * a) ^ 2 * (1 - Real.cos (Hyperbolic.gridPhase N k)) : ℝ) : ℂ)
          - Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ) ∧
      ‖FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_40 a lam)) k‖ ^ 2
        = 1 - (lam * a) ^ 2 * (1 - (lam * a) ^ 2)
          * (1 - Real.cos (Hyperbolic.gridPhase N k)) ^ 2 ∧
      ((∀ k : Fin N, ‖FiniteDifference.amplificationFactor
          (Stencil.toPeriodic N (equation_13_40 a lam)) k‖ ≤ 1) ↔ |lam * a| ≤ 1) :=
  ⟨Hyperbolic.amplificationFactor_laxWendroff a lam k,
    Hyperbolic.norm_amplificationFactor_laxWendroff_sq a lam k,
    Hyperbolic.norm_amplificationFactor_laxWendroff_le_one_iff hN a lam⟩

/-- **Section 13.8.4** of [quarteroni2000numerical], $\ell^2$ stability of the Lax–Wendroff scheme.
Let $N \ge 2$ and $a, \lambda \in \mathbb{R}$ with $|\lambda a| \le 1$, and let $Q$ be the
Lax–Wendroff scheme (13.40) on the periodic grid of $N$ points. Then for all $n$ and
$u \in \mathbb{C}^N$
$$\|Q^n u\|_2 \le \|u\|_2.$$

The source refers to the literature for this result. Here it follows from Theorem 13.1, because
$|\gamma_k| \le 1$ for every $k$.

**Specialization.** The discrete contractivity estimate is for a finite periodic grid. -/
theorem laxWendroff_stable {N : ℕ} [NeZero N] (hN : 2 ≤ N) {a lam : ℝ} (h : |lam * a| ≤ 1)
    (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin
        (FiniteDifference.periodicScheme (Stencil.toPeriodic N (equation_13_40 a lam)) ^ n) u‖
      ≤ ‖u‖ :=
  theorem_13_1 _ ((Hyperbolic.norm_amplificationFactor_laxWendroff_le_one_iff hN a lam).2 h) n u

/-- **Section 13.8.4** of [quarteroni2000numerical], the backward Euler/centred amplification factor
(see also Section 13.8.2 and Figure 13.7). Let $N \ge 1$, $a, \lambda \in \mathbb{R}$ and
$\varphi_k = 2\pi k/N$. The amplification factor of the implicit scheme (13.43) on the periodic
grid of $N$ points is
$$\gamma_k = \frac{1}{1 + i \lambda a \sin\varphi_k}, \qquad |\gamma_k| \le 1,$$
for every $\lambda$, $a$ and $k$. This is the periodic counterpart of Exercise 7.

The factor is `FiniteDifference.amplificationFactor₂` of the left stencil
$u_j + \frac{\lambda a}{2}(u_{j+1} - u_{j-1})$ and the identity stencil: the quotient of their
amplification factors.

**Reading.** This gives the finite periodic Fourier factor behind unconditional stability. -/
theorem amplificationFactor_backwardEulerCentred {N : ℕ} [NeZero N] (a lam : ℝ) (k : Fin N) :
    FiniteDifference.amplificationFactor₂
        (Stencil.toPeriodic N (Stencil.threePoint (-(lam * a / 2)) 1 (lam * a / 2)))
        (Stencil.toPeriodic N (Stencil.threePoint 0 1 0)) k
        = 1 / (1 + Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ)) ∧
      ‖FiniteDifference.amplificationFactor₂
        (Stencil.toPeriodic N (Stencil.threePoint (-(lam * a / 2)) 1 (lam * a / 2)))
        (Stencil.toPeriodic N (Stencil.threePoint 0 1 0)) k‖ ≤ 1 :=
  ⟨Hyperbolic.amplificationFactor₂_backwardEulerCentred a lam k,
    Hyperbolic.norm_amplificationFactor₂_backwardEulerCentred_le_one a lam k⟩

/-- **Equation (13.53)** of [quarteroni2000numerical], the discrete maximum principle. Let
$a, \lambda \in \mathbb{R}$ with $0 \le \lambda |a| \le 1$, and let
$u : \mathbb{Z} \to \mathbb{R}$ be bounded. Then the iterates of the upwind scheme (13.41)
satisfy, for all $n$ and $j$,
$$\inf_i u_i \le (Q^n u)_j \le \sup_i u_i.$$
So $\|u^n\|_{\Delta,\infty} \le \|u^0\|_{\Delta,\infty}$.

**Reading.** The formal maximum principle uses infimum and supremum bounds on bounded grid
data, for either sign of the speed. -/
theorem equation_13_53 {a lam : ℝ} (h0 : 0 ≤ lam * |a|) (h1 : lam * |a| ≤ 1) {u : ℤ → ℝ}
    (hba : BddAbove (range u)) (hbb : BddBelow (range u)) (n : ℕ) (j : ℤ) :
    ⨅ i, u i ≤ (Stencil.apply (equation_13_41 a lam))^[n] u j ∧
      (Stencil.apply (equation_13_41 a lam))^[n] u j ≤ ⨆ i, u i :=
  ⟨(Hyperbolic.upwind_isMonotone h0 h1).iInf_le_iterate_apply hbb n j,
    (Hyperbolic.upwind_isMonotone h0 h1).iterate_apply_le_iSup hba n j⟩

/-!
### Remark 13.4: the schemes for the wave equation

Remark 13.4 of [quarteroni2000numerical] states that the leap-frog scheme (13.44) is stable under
the CFL restriction $\Delta t \le \Delta x/|\gamma|$, and that the Newmark scheme (13.45) is
unconditionally stable for $2\beta \ge \theta \ge 1/2$. Read as (13.46) for the state
$(u^{n+1}, u^n)$, the leap-frog claim is false at every CFL number, because of the spatially
constant mode. What the wave equation controls is its energy. In the energy variables, the discrete
velocity $(u^{n+1} - u^n)/\Delta t$ and the discrete gradient $\nabla_h u^n/\Delta x$, both claims
are true, the leap-frog claim under the strict condition $|\gamma|\lambda < 1$. Both results
specialize the abstract theorems `FiniteDifference.Hyperbolic.leapFrog_stability` and
`FiniteDifference.Hyperbolic.newmark_stability` for a symmetric positive semidefinite operator, here
`FiniteDifference.Hyperbolic.discreteWaveOp γ Δx`, the operator $-\gamma^2 \delta^2/\Delta x^2$ on
$\ell^2(\mathbb{Z})$. Since $\|v\|_{\Delta,2}^2 = \Delta x \|v\|^2$, the inequalities hold in the
discrete norm (13.47) as in the $\ell^2$ norm: the factor $\Delta x$ cancels.
-/

section WaveEquation

open scoped RealInnerProductSpace

/-- **Remark 13.4** of [quarteroni2000numerical], the leap-frog method in the state
$(u^{n+1}, u^n)$. Let $\gamma, \lambda \in \mathbb{R}$. The spatially constant grid function
$u_j^n = n$ satisfies the leap-frog scheme (13.44), with $u^0 = 0$ and $u^1 = 1$, and it is
unbounded: there is no $C$ with $|u_j^n| \le C$ for all $n$ and $j$.

**Correction.** The source states that the leap-frog method is stable under the CFL restriction
$\Delta t \le \Delta x/|\gamma|$. For the state $(u^{n+1}, u^n)$ no stability estimate (13.46)
can hold, however small the CFL number $\gamma\lambda$ is: the data of this solution are bounded
and its iterates are not. They are unbounded in $\|\cdot\|_{\Delta,\infty}$, and in
$\|\cdot\|_{\Delta,2}$ on every periodic grid. The claim is true in the energy variables; see
`QuarteroniSaccoSaleri.Chapter13.remark_13_4_leapFrog`.

Both sides of the scheme vanish identically for this solution. It is the mode $k = 0$ of the von
Neumann analysis: $\varphi_0 = 0$ gives the amplification matrix $G_0 = \begin{bmatrix} 2 & -1
\\ 1 & 0 \end{bmatrix}$, a Jordan block with $G_0^n = \begin{bmatrix} n + 1 & -n \\ n & 1 - n
\end{bmatrix}$. There the scheme reproduces the exact solution $u_0 + v_0 t$ of a spatially
constant wave, which the norms (13.47) cannot bound by the data. The bound also fails to be
uniform in $k$: for $|c| < 1$ the powers have the Chebyshev form
$G^n = U_{n-1}(c) G - U_{n-2}(c) I$ with $U_{n-1}(\cos\vartheta) =
\sin(n\vartheta)/\sin\vartheta$, and on the first mode $\vartheta \approx \gamma\lambda\Delta x$
and $n \approx T/(\lambda\Delta x)$ give $\sin(n\vartheta)/\sin\vartheta \approx \sin(\gamma
T)/(\gamma\lambda\Delta x) \to \infty$. -/
theorem remark_13_4_leapFrog_constantMode (γ lam : ℝ) :
    let u : ℕ → ℤ → ℝ := fun n _ => n
    equation_13_44 γ lam u ∧ u 0 = 0 ∧ u 1 = 1 ∧ ¬∃ C : ℝ, ∀ n j, |u n j| ≤ C := by
  intro u
  refine ⟨fun n j => by simp only [u]; push_cast; ring, funext fun j => by simp [u],
    funext fun j => by simp [u], ?_⟩
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h := hC n 0
  rw [show u n 0 = (n : ℝ) from rfl, abs_of_nonneg (Nat.cast_nonneg n)] at h
  exact absurd h (not_le.2 hn)

/-- **Remark 13.4** of [quarteroni2000numerical], the leap-frog method. Let $\gamma \neq 0$,
$\Delta t, \Delta x > 0$, $\lambda = \Delta t/\Delta x$ with $|\gamma| \lambda < 1$, and let
$(u^n)$ be a sequence in $\ell^2(\mathbb{Z})$ that satisfies the leap-frog scheme (13.44). Then
for every $n$
$$\frac{\|u^{n+1} - u^n\|^2}{\Delta t^2} + \gamma^2 \frac{\|\nabla_h u^n\|^2}{\Delta x^2} \le
  \frac{1 + |\gamma|\lambda}{1 - |\gamma|\lambda} \Bigl(\frac{\|u^1 - u^0\|^2}{\Delta t^2} +
  \gamma^2 \frac{\|\nabla_h u^0\|^2}{\Delta x^2}\Bigr),$$
where $(\nabla_h u)_j = u_{j+1} - u_j$ is the forward difference.

**Correction.** The source states stability under $\Delta t \le \Delta x/|\gamma|$, without
naming the norm. In the state $(u^{n+1}, u^n)$ and the norms (13.47) the claim is false at every
CFL number (see `QuarteroniSaccoSaleri.Chapter13.remark_13_4_leapFrog_constantMode`). This
theorem states it in the energy variables, under the strict condition $|\gamma|\lambda < 1$. At
$|\gamma|\lambda = 1$ the equivalence of the conserved energy with the left-hand side
degenerates.

No finite time interval is needed: a discrete energy is conserved exactly
(`FiniteDifference.Hyperbolic.leapFrogEnergy_succ`), and it is equivalent to the left-hand side
with the constants $1 \pm |\gamma|\lambda$. The hypothesis $\gamma \neq 0$ excludes only the
degenerate case in which (13.44) has no space operator and the CFL restriction says nothing. The
forward difference is `FiniteDifference.Hyperbolic.forwardDiffCLM`. -/
theorem remark_13_4_leapFrog {γ Δt Δx lam : ℝ} (hγ : γ ≠ 0) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (hcfl : |γ| * lam < 1) {u : ℕ → lp (fun _ : ℤ => ℝ) 2}
    (h : equation_13_44 γ lam fun n => ⇑(u n)) (n : ℕ) :
    ‖u (n + 1) - u n‖ ^ 2 / Δt ^ 2 + γ ^ 2 * ‖Hyperbolic.forwardDiffCLM (u n)‖ ^ 2 / Δx ^ 2
      ≤ (1 + |γ| * lam) / (1 - |γ| * lam)
        * (‖u 1 - u 0‖ ^ 2 / Δt ^ 2
          + γ ^ 2 * ‖Hyperbolic.forwardDiffCLM (u 0)‖ ^ 2 / Δx ^ 2) := by
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hkap : 0 < |γ| * lam := mul_pos (abs_pos.2 hγ) hlampos
  have hop := Hyperbolic.isLeapFrogOp_of_isLeapFrog hΔx.ne' hlam h
  have hA := Hyperbolic.discreteWaveOp_isSymmetricBoundedBy γ Δx
  have hCFLeq : Δt ^ 2 * (4 * γ ^ 2 / Δx ^ 2) = 4 * (|γ| * lam) ^ 2 := by
    rw [hlam, mul_pow, sq_abs]
    field_simp
  have hst := Hyperbolic.leapFrog_stability hA hkap hcfl hCFLeq.le hop n
  simp only [ContinuousLinearMap.coe_coe] at hst
  have hΔt2 : (0 : ℝ) < Δt ^ 2 := by positivity
  have hL : ∀ m : ℕ, ‖u (m + 1) - u m‖ ^ 2 / Δt ^ 2
      + γ ^ 2 * ‖Hyperbolic.forwardDiffCLM (u m)‖ ^ 2 / Δx ^ 2
      = (‖u (m + 1) - u m‖ ^ 2
        + Δt ^ 2 * ⟪Hyperbolic.discreteWaveOp γ Δx (u m), u m⟫) / Δt ^ 2 := by
    intro m
    rw [Hyperbolic.inner_discreteWaveOp_self]
    field_simp
  have h0 := hL 0
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h0
  rw [hL n, h0, ← mul_div_assoc]
  gcongr

/-- **Remark 13.4** of [quarteroni2000numerical], the Newmark method. Let
$\gamma, \beta, \theta \in \mathbb{R}$ with $\frac{1}{2} \le \theta \le 2\beta$, let
$\Delta t, \Delta x > 0$ and $\lambda = \Delta t/\Delta x$, and let $(u^n)$ and $(v^n)$ be
sequences in $\ell^2(\mathbb{Z})$ that satisfy the Newmark scheme (13.45). Then for every $n$
$$\|v^n\|^2 + \gamma^2 \frac{\|\nabla_h u^n\|^2}{\Delta x^2} \le \|v^0\|^2 + \gamma^2
  \frac{\|\nabla_h u^0\|^2}{\Delta x^2} + \frac{\Delta t^2 (2\beta - \theta)}{2}
  \Bigl(\frac{\gamma^2}{\Delta x^2}\Bigr)^2 \|\delta^2 u^0\|^2,$$
where $\nabla_h$ is the forward difference and $(\delta^2 u)_j = u_{j+1} - 2u_j + u_{j-1}$. So
the scheme is unconditionally stable, for every $\Delta t$ and $\Delta x$, in this energy.

**Reading.** The source states that the Newmark method is unconditionally stable for
$2\beta \ge \theta \ge \frac{1}{2}$, and cites a reference for it, without naming the norm. The
theorem reads stability in the energy $\|v^n\|^2 + \gamma^2 \|\nabla_h u^n\|^2/\Delta x^2$. In
the state $(u, \Delta t\, v)$ the claim fails: on the constant mode this state is advanced by
the Jordan block $\begin{bmatrix} 1 & 1 \\ 0 & 1 \end{bmatrix}$, whose powers grow linearly.

The extra term on the right is the one that the parameters of the method add; it vanishes
exactly when $2\beta = \theta$, and for $2\beta = \theta = 1/2$ the energy is conserved. The
operators are `FiniteDifference.Hyperbolic.forwardDiffCLM` and
`FiniteDifference.Hyperbolic.secondDiffCLM`. -/
theorem remark_13_4_newmark {γ Δt Δx lam β θ : ℝ} (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (hth : 1 / 2 ≤ θ) (hbt : θ ≤ 2 * β)
    {u v : ℕ → lp (fun _ : ℤ => ℝ) 2}
    (h : equation_13_45 γ lam Δt β θ (fun n => ⇑(u n)) fun n => ⇑(v n)) (n : ℕ) :
    ‖v n‖ ^ 2 + γ ^ 2 * ‖Hyperbolic.forwardDiffCLM (u n)‖ ^ 2 / Δx ^ 2
      ≤ ‖v 0‖ ^ 2 + γ ^ 2 * ‖Hyperbolic.forwardDiffCLM (u 0)‖ ^ 2 / Δx ^ 2
        + Δt ^ 2 * (2 * β - θ) / 2 * (γ ^ 2 / Δx ^ 2) ^ 2
          * ‖Hyperbolic.secondDiffCLM (u 0)‖ ^ 2 := by
  have hop := Hyperbolic.isNewmarkOp_of_isNewmark hΔt.ne' hΔx.ne' hlam h
  have hA := Hyperbolic.discreteWaveOp_isSymmetricBoundedBy γ Δx
  have hst := Hyperbolic.newmark_stability hA hth hbt hop n
  simp only [ContinuousLinearMap.coe_coe] at hst
  have hnorm : ∀ w : lp (fun _ : ℤ => ℝ) 2,
      ‖Hyperbolic.discreteWaveOp γ Δx w‖ ^ 2
        = (γ ^ 2 / Δx ^ 2) ^ 2 * ‖Hyperbolic.secondDiffCLM w‖ ^ 2 := by
    intro w
    have hw : Hyperbolic.discreteWaveOp γ Δx w
        = (-(γ ^ 2 / Δx ^ 2)) • Hyperbolic.secondDiffCLM w := rfl
    rw [hw, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq]
  rw [Hyperbolic.inner_discreteWaveOp_self, Hyperbolic.inner_discreteWaveOp_self,
    hnorm] at hst
  have he : ∀ w : lp (fun _ : ℤ => ℝ) 2,
      γ ^ 2 / Δx ^ 2 * ‖Hyperbolic.forwardDiffCLM w‖ ^ 2
        = γ ^ 2 * ‖Hyperbolic.forwardDiffCLM w‖ ^ 2 / Δx ^ 2 := fun w => by ring
  rw [he, he] at hst
  linarith

end WaveEquation

end QuarteroniSaccoSaleri.Chapter13
