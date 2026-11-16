/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Analysis.Calculus.PartialDeriv
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.PDE.Transport
import Numlib.FiniteDifference.Derivative
import Numlib.FiniteDifference.VonNeumann
import Numlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Finite difference schemes for the linear transport equation

This module studies the finite difference schemes of §13.7 of [quarteroni2000numerical] for the
transport equation $u_t + a u_x = 0$, $a \in \mathbb{R}$, and their analysis in §13.8–13.9. The grid
is $x_j = j \Delta x$, $t^n = n \Delta t$, with the mesh ratio $\lambda = \Delta t / \Delta x$. An
explicit scheme is a stencil $c$ (`FiniteDifference.Stencil`) that maps the grid values $u^n$ to
$u^{n+1}_j = \sum_s c_s u^n_{j-s}$; a three-point stencil with the weights $(c_-, c_0, c_+)$ gives
$u^{n+1}_j = c_- u^n_{j-1} + c_0 u^n_j + c_+ u^n_{j+1}$. The four explicit three-point schemes are
forward Euler/centred, Lax–Friedrichs, Lax–Wendroff and upwind. The module also treats the implicit
backward Euler/centred scheme on $\ell^2(\mathbb{Z})$, and the leap-frog and Newmark schemes for the
wave equation $u_{tt} = \gamma^2 u_{xx}$.

The main results are the following. The truncation errors of the four explicit schemes have the
orders of Table 13.1 of [quarteroni2000numerical], with explicit constants. The CFL condition
$|a \lambda| \le 1$ is necessary for convergence, but it is not sufficient: the forward
Euler/centred scheme is unstable for every $\lambda$. Upwind and Lax–Friedrichs are monotone under
the CFL condition, and the amplification factors of upwind, Lax–Friedrichs and Lax–Wendroff have
modulus at most $1$ exactly under it. The backward Euler/centred scheme is unconditionally stable in
$\ell^2$. A solution of the equivalent (modified) equation $v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$
leaves the schemes a residual of higher order than the exact solution does. The leap-frog scheme
conserves a discrete energy, and the Newmark scheme does not increase one for
$2\beta \ge \theta \ge 1/2$.

## Main definitions

* `FiniteDifference.Hyperbolic.forwardEulerCentred`, `FiniteDifference.Hyperbolic.laxFriedrichs`,
  `FiniteDifference.Hyperbolic.laxWendroff`, `FiniteDifference.Hyperbolic.upwind`: the explicit
  schemes (13.37), (13.39), (13.40) and (13.41).
* `FiniteDifference.Hyperbolic.artificialViscosity`: the forward Euler/centred scheme with an
  artificial viscosity $k$, (13.42).
* `FiniteDifference.Hyperbolic.backwardEulerCentred`: the solution operator of the implicit scheme
  (13.43) on $\ell^2(\mathbb{Z})$.
* `FiniteDifference.Hyperbolic.truncationError`: the local truncation error on the exact solution
  $u_0(x - a t)$.
* `FiniteDifference.Hyperbolic.IsOfOrder`, `FiniteDifference.Hyperbolic.IsConsistent`,
  `FiniteDifference.Hyperbolic.IsConvergent`: order, consistency and convergence of a family of
  schemes.
* `FiniteDifference.Hyperbolic.CFL`: the CFL condition $|a \lambda| \le 1$.
* `FiniteDifference.Hyperbolic.IsLeapFrog`, `FiniteDifference.Hyperbolic.IsNewmark`: the schemes
  (13.44) and (13.45) for the wave equation.
* `FiniteDifference.Hyperbolic.amplificationError`, `FiniteDifference.Hyperbolic.dispersionError`:
  the dissipation and dispersion errors of §13.9.
* `FiniteDifference.Hyperbolic.IsModifiedSolution`: a classical solution of the equivalent equation
  (13.56).
* `FiniteDifference.Hyperbolic.leapFrogEnergy`, `FiniteDifference.Hyperbolic.newmarkEnergy`: the
  discrete energies of the leap-frog and Newmark schemes.

## Main results

* `FiniteDifference.Hyperbolic.abs_truncationError_laxWendroff_le` and its companions: the
  truncation errors of Table 13.1, $O(\Delta t + \Delta x^2)$,
  $O(\Delta x^2/\Delta t + \Delta t + \Delta x^2)$, $O(\Delta t^2 + \Delta x^2)$ and
  $O(\Delta t + \Delta x)$.
* `FiniteDifference.Hyperbolic.not_isConvergent_of_one_lt_abs_mul`: if $|a| \lambda > 1$, no
  three-point scheme family converges for every smooth datum.
* `FiniteDifference.Hyperbolic.forwardEulerCentred_not_isStableFamily`: the forward Euler/centred
  scheme is unstable for every $\lambda > 0$.
* `FiniteDifference.Hyperbolic.upwind_isMonotone`,
  `FiniteDifference.Hyperbolic.laxFriedrichs_isMonotone`: upwind and Lax–Friedrichs are monotone
  under the CFL condition.
* `FiniteDifference.Hyperbolic.norm_amplificationFactor_upwind_le_one_iff` and its companions: for
  upwind, Lax–Friedrichs and Lax–Wendroff, all amplification factors have modulus at most $1$ if and
  only if the CFL condition holds.
* `FiniteDifference.Hyperbolic.norm_backwardEulerCentred_apply_le`: the backward Euler/centred
  scheme does not increase the $\ell^2$ norm.
* `FiniteDifference.Hyperbolic.abs_residual_threePoint_le_of_isModifiedSolution`: the third-order
  equivalent equation of a conservative three-point scheme.
* `FiniteDifference.Hyperbolic.leapFrog_stability`, `FiniteDifference.Hyperbolic.newmark_stability`:
  energy stability of the leap-frog scheme under the strict CFL condition, and of the Newmark scheme
  for $2\beta \ge \theta \ge 1/2$.

## Proof outline

Every explicit scheme is a `FiniteDifference.Stencil`, so the numerical domain of dependence, the
discrete maximum principle, the $\ell^p$ bounds and the amplification factors come from
`Numlib.FiniteDifference.Stencil` and `Numlib.FiniteDifference.VonNeumann` and are not proved again
for each scheme. The exact solution of $u_t + a u_x = 0$ is the travelling wave $u_0(x - a t)$
(`Transport.IsSolution.eq_comp_sub`). So the truncation error at a grid point is a combination of
values of the function $u_0$ of one variable near the foot $\xi = x_j - a t^n$ of the
characteristic, and Taylor's theorem with the Lagrange remainder (`Numlib.Analysis.Calculus.Taylor`)
gives the truncation errors. For the necessity of the CFL condition, the numerical domain of
dependence at $(0, 1)$ misses the foot $-a$ of the characteristic, so a bump datum concentrated at
$-a$ defeats every three-point scheme. The equivalent equations come from a Taylor expansion of the
residual of a three-point scheme in both variables, into which the equivalent equation,
differentiated, is substituted.

## Implementation notes

* A family of schemes is a function `c : ℝ → ℝ → Stencil` of $(\Delta t, \Delta x)$. Order,
  consistency and convergence let $\Delta t$ and $\Delta x$ tend to $0$ independently.
* The implicit backward Euler/centred scheme is the inverse of the operator
  $1 + (\lambda a / 2) D_0$ on $\ell^2(\mathbb{Z})$, where $D_0$ is the centred difference. Since
  $D_0$ is skew-adjoint, this operator is coercive with constant $1$, and its inverse is a
  contraction.
* The leap-frog and Newmark schemes are also stated for an abstract symmetric positive semidefinite
  operator $A$ on a real inner product space, which stands for the discretization
  $-\gamma^2 \delta^2 / \Delta x^2$ of $-\gamma^2 \partial_x^2$.
* §13.8.3 of [quarteroni2000numerical] calls the CFL condition necessary and sufficient for
  stability. It is necessary (`FiniteDifference.Hyperbolic.not_isConvergent_of_one_lt_abs_mul`) but
  not sufficient (`FiniteDifference.Hyperbolic.forwardEulerCentred_not_isStableFamily`); for each of
  the other schemes, sufficiency is proved separately.
* The source prints the expansion (13.58) of the upwind residual with
  $a(v_x + (\Delta x/2) v_{xx})$. The correct sign is $a(v_x - (\Delta x/2) v_{xx})$
  (`FiniteDifference.Hyperbolic.abs_residual_upwind_sub_le_two`).
* The text after (13.60) of the source gives $\nu = (a/6)(a^2 \Delta t^2 - \Delta x^2)$ for the
  upwind scheme, which disagrees with Table 13.2. The value of the table is used and is correct
  (`FiniteDifference.Hyperbolic.abs_residual_upwind_le_of_isModifiedSolution_third`).
* The source states that the Newmark scheme is second-order accurate. The residual of the velocity
  update is of second order only for $\theta = 1/2$
  (`FiniteDifference.Hyperbolic.abs_residual_newmark_le`).
* Remark 13.4 of the source states stability of the leap-frog and Newmark schemes. The statements
  hold for the discrete energy, not for the Euclidean norm of the state; see the sectioning comment
  before `FiniteDifference.Hyperbolic.IsLeapFrogOp`.
-/

open Set Filter Topology Finset Function Complex Matrix
open scoped Real ENNReal Nat

namespace FiniteDifference

namespace Hyperbolic

/-! ### The schemes of §13.7 -/

/-- The **forward Euler/centred scheme**: the three-point stencil
$$u^{n+1}_j = u^n_j - \frac{\lambda a}{2} (u^n_{j+1} - u^n_{j-1}),$$
with the weights $(\lambda a/2, 1, -\lambda a/2)$. This is (13.37) of [quarteroni2000numerical]. -/
noncomputable def forwardEulerCentred (a lam : ℝ) : Stencil :=
  Stencil.threePoint (lam * a / 2) 1 (-(lam * a / 2))

/-- The **Lax–Friedrichs scheme**: the three-point stencil
$$u^{n+1}_j = \frac{1}{2} (u^n_{j+1} + u^n_{j-1}) - \frac{\lambda a}{2} (u^n_{j+1} -
  u^n_{j-1}),$$
with the weights $((1 + \lambda a)/2, 0, (1 - \lambda a)/2)$. This is (13.39) of
[quarteroni2000numerical]. -/
noncomputable def laxFriedrichs (a lam : ℝ) : Stencil :=
  Stencil.threePoint ((1 + lam * a) / 2) 0 ((1 - lam * a) / 2)

/-- The **Lax–Wendroff scheme**: the three-point stencil
$$u^{n+1}_j = u^n_j - \frac{\lambda a}{2} (u^n_{j+1} - u^n_{j-1}) + \frac{\lambda^2 a^2}{2}
  (u^n_{j+1} - 2 u^n_j + u^n_{j-1}).$$
This is (13.40) of [quarteroni2000numerical]. -/
noncomputable def laxWendroff (a lam : ℝ) : Stencil :=
  Stencil.threePoint (lam * a / 2 * (1 + lam * a)) (1 - (lam * a) ^ 2)
    (lam * a / 2 * (lam * a - 1))

/-- The **upwind scheme**: the three-point stencil
$$u^{n+1}_j = u^n_j - \frac{\lambda a}{2} (u^n_{j+1} - u^n_{j-1}) + \frac{\lambda |a|}{2}
  (u^n_{j+1} - 2 u^n_j + u^n_{j-1}),$$
with the weights $(\lambda \max\{a, 0\}, 1 - \lambda |a|, \lambda \max\{-a, 0\})$. This is
(13.41) of [quarteroni2000numerical]. -/
noncomputable def upwind (a lam : ℝ) : Stencil :=
  Stencil.threePoint (lam * max a 0) (1 - lam * |a|) (lam * max (-a) 0)

/-- The **forward Euler/centred scheme with artificial viscosity** $k$: the three-point stencil
$$u^{n+1}_j = u^n_j - \frac{\lambda a}{2} (u^n_{j+1} - u^n_{j-1}) + \frac{k}{2 \Delta x^2}
  (u^n_{j+1} - 2 u^n_j + u^n_{j-1}).$$
This is (13.42) of [quarteroni2000numerical].

The scheme is defined for every $\Delta x$; at $\Delta x = 0$ the quotient $k / \Delta x^2$ is
$0$. -/
noncomputable def artificialViscosity (a lam Δx k : ℝ) : Stencil :=
  Stencil.threePoint (lam * a / 2 + k / (2 * Δx ^ 2)) (1 - k / Δx ^ 2)
    (-(lam * a / 2) + k / (2 * Δx ^ 2))

/-- Two three-point stencils with equal weights are equal. -/
theorem threePoint_congr {cm c0 cp cm' c0' cp' : ℝ} (hm : cm = cm') (h0 : c0 = c0')
    (hp : cp = cp') : Stencil.threePoint cm c0 cp = Stencil.threePoint cm' c0' cp' := by
  rw [hm, h0, hp]

/-- The positive part of $a \in \mathbb{R}$ is $\max\{a, 0\} = (a + |a|)/2$. -/
theorem max_zero_eq (a : ℝ) : max a 0 = (a + |a|) / 2 := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

/-- The negative part of $a \in \mathbb{R}$ is $\max\{-a, 0\} = (|a| - a)/2$. -/
theorem max_neg_zero_eq (a : ℝ) : max (-a) 0 = (|a| - a) / 2 := by
  rw [max_zero_eq, abs_neg]; ring

/-- The **upwind scheme for a right-moving wave**: for $a > 0$ the upwind scheme is the three-point
stencil
$$u^{n+1}_j = u^n_j - \lambda a (u^n_j - u^n_{j-1}).$$
This is (13.50) of [quarteroni2000numerical]. -/
theorem upwind_eq_of_pos {a : ℝ} (ha : 0 < a) (lam : ℝ) :
    upwind a lam = Stencil.threePoint (lam * a) (1 - lam * a) 0 :=
  threePoint_congr (by rw [max_eq_left ha.le]) (by rw [abs_of_pos ha])
    (by rw [max_eq_right (by linarith), mul_zero])

/-- The **upwind scheme for a left-moving wave**: for $a < 0$ the upwind scheme is the three-point
stencil
$$u^{n+1}_j = u^n_j - \lambda a (u^n_{j+1} - u^n_j).$$
This is in §13.7.1 of [quarteroni2000numerical]. -/
theorem upwind_eq_of_neg {a : ℝ} (ha : a < 0) (lam : ℝ) :
    upwind a lam = Stencil.threePoint 0 (1 + lam * a) (-(lam * a)) :=
  threePoint_congr (by rw [max_eq_right ha.le, mul_zero]) (by rw [abs_of_neg ha]; ring)
    (by rw [max_eq_left (by linarith)]; ring)

/-!
### Numerical fluxes and artificial viscosities (Table 13.1)

A conservative scheme with the linear numerical flux $h(u, v) = \alpha u + \beta v$ is $u^{n+1}_j =
u^n_j - \lambda (h(u^n_j, u^n_{j+1}) - h(u^n_{j-1}, u^n_j))$ (`FiniteDifference.Stencil.ofFlux`,
(13.36) of [quarteroni2000numerical]). Each of the four explicit schemes is conservative, and each
of the last three is the forward Euler/centred scheme with an artificial viscosity $k$, with the
values of $k$ of Table 13.1.
-/

/-- The forward Euler/centred scheme is the conservative scheme with the numerical flux
$h(u, v) = \frac{1}{2} a (u + v)$. This is (13.38) of [quarteroni2000numerical]. -/
theorem forwardEulerCentred_eq_ofFlux (a lam : ℝ) :
    forwardEulerCentred a lam = Stencil.ofFlux lam (a / 2) (a / 2) :=
  threePoint_congr (by ring) (by ring) (by ring)

/-- Let $\lambda \neq 0$. The Lax–Friedrichs scheme is the conservative scheme with the numerical
flux
$$h(u, v) = \frac{1}{2} \bigl[a (u + v) - \lambda^{-1} (v - u)\bigr].$$
This is in §13.7.1 of [quarteroni2000numerical]. -/
theorem laxFriedrichs_eq_ofFlux {lam : ℝ} (hlam : lam ≠ 0) (a : ℝ) :
    laxFriedrichs a lam = Stencil.ofFlux lam (a / 2 + 1 / (2 * lam)) (a / 2 - 1 / (2 * lam)) :=
  threePoint_congr (by field_simp; try ring) (by field_simp; try ring) (by field_simp; try ring)

/-- The Lax–Wendroff scheme is the conservative scheme with the numerical flux
$$h(u, v) = \frac{1}{2} \bigl[a (u + v) - \lambda a^2 (v - u)\bigr].$$
This is in §13.7.1 of [quarteroni2000numerical]. -/
theorem laxWendroff_eq_ofFlux (a lam : ℝ) :
    laxWendroff a lam
      = Stencil.ofFlux lam (a / 2 + lam * a ^ 2 / 2) (a / 2 - lam * a ^ 2 / 2) :=
  threePoint_congr (by ring) (by ring) (by ring)

/-- The upwind scheme is the conservative scheme with the numerical flux
$$h(u, v) = \frac{1}{2} \bigl[a (u + v) - |a| (v - u)\bigr].$$
This is in §13.7.1 of [quarteroni2000numerical]. -/
theorem upwind_eq_ofFlux (a lam : ℝ) :
    upwind a lam = Stencil.ofFlux lam ((a + |a|) / 2) ((a - |a|) / 2) :=
  threePoint_congr (by rw [max_zero_eq]; try ring) (by ring)
    (by rw [max_neg_zero_eq]; try ring)

/-- Let $\Delta x \neq 0$. The Lax–Friedrichs scheme is the forward Euler/centred scheme with the
artificial viscosity $k = \Delta x^2$. This is in Table 13.1 of [quarteroni2000numerical]. -/
theorem laxFriedrichs_eq_artificialViscosity {Δx : ℝ} (hΔx : Δx ≠ 0) (a lam : ℝ) :
    laxFriedrichs a lam = artificialViscosity a lam Δx (Δx ^ 2) :=
  threePoint_congr (by field_simp; try ring) (by field_simp; try ring) (by field_simp; try ring)

/-- Let $\Delta x \neq 0$ and $\lambda = \Delta t / \Delta x$. The Lax–Wendroff scheme is the
forward Euler/centred scheme with the artificial viscosity $k = a^2 \Delta t^2$. This is in
Table 13.1 of [quarteroni2000numerical]. -/
theorem laxWendroff_eq_artificialViscosity {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx)
    (a : ℝ) : laxWendroff a lam = artificialViscosity a lam Δx (a ^ 2 * Δt ^ 2) := by
  subst hlam
  exact threePoint_congr (by field_simp; try ring) (by field_simp; try ring)
    (by field_simp; try ring)

/-- Let $\Delta x \neq 0$ and $\lambda = \Delta t / \Delta x$. The upwind scheme is the forward
Euler/centred scheme with the artificial viscosity $k = |a| \Delta x \Delta t$. This is in Table
13.1 of [quarteroni2000numerical]. -/
theorem upwind_eq_artificialViscosity {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx)
    (a : ℝ) : upwind a lam = artificialViscosity a lam Δx (|a| * Δx * Δt) := by
  subst hlam
  exact threePoint_congr (by rw [max_zero_eq]; field_simp; try ring) (by field_simp; try ring)
    (by rw [max_neg_zero_eq]; field_simp; try ring)

/-! ### Monotone schemes and the discrete maximum principle -/

/-- The weight of the three-point stencil with weights $(c_-, c_0, c_+)$ at the offset
$s \in \mathbb{Z}$ is $c_-$ for $s = 1$, $c_0$ for $s = 0$, $c_+$ for $s = -1$, and $0$
otherwise.

The offset $s$ is the one of `FiniteDifference.Stencil.apply`, which reads $u_{j-s}$; so $c_-$,
at $s = 1$, multiplies $u_{j-1}$. -/
theorem threePoint_coe_apply (cm c0 cp : ℝ) (s : ℤ) :
    Stencil.threePoint cm c0 cp s
      = (if 1 = s then cm else 0) + (if 0 = s then c0 else 0) + (if -1 = s then cp else 0) := by
  simp [Stencil.threePoint, Finsupp.single_apply]

/-- A three-point stencil with nonnegative weights $c_-, c_0, c_+$ whose sum is $1$ is monotone
(`FiniteDifference.Stencil.IsMonotone`). -/
theorem isMonotone_threePoint {cm c0 cp : ℝ} (hm : 0 ≤ cm) (h0 : 0 ≤ c0) (hp : 0 ≤ cp)
    (hsum : cm + c0 + cp = 1) : Stencil.IsMonotone (Stencil.threePoint cm c0 cp) := by
  refine ⟨fun s => ?_, by rw [Stencil.threePoint_sum]; exact hsum⟩
  rw [threePoint_coe_apply]
  split_ifs <;> linarith

/-- The **upwind scheme is monotone under the CFL condition**: if $0 \le \lambda |a| \le 1$, its
weights are nonnegative and sum to $1$. This is in §13.8.3 of [quarteroni2000numerical].

By the results on monotone stencils in `Numlib.FiniteDifference.Stencil`, the scheme then
satisfies the discrete maximum principle (13.53) and does not increase any $\ell^p$ norm. -/
theorem upwind_isMonotone {a lam : ℝ} (h0 : 0 ≤ lam * |a|) (h1 : lam * |a| ≤ 1) :
    Stencil.IsMonotone (upwind a lam) := by
  have hsum : lam * max a 0 + (1 - lam * |a|) + lam * max (-a) 0 = 1 := by
    rw [max_zero_eq, max_neg_zero_eq]; ring
  rcases le_total a 0 with ha | ha
  · have e1 : max a 0 = 0 := max_eq_right ha
    have e2 : max (-a) 0 = |a| := by rw [max_neg_zero_eq, abs_of_nonpos ha]; ring
    exact isMonotone_threePoint (by rw [e1, mul_zero]) (by linarith) (by rw [e2]; exact h0) hsum
  · have e1 : max a 0 = a := max_eq_left ha
    have e2 : max (-a) 0 = 0 := max_eq_right (by linarith)
    have e3 : |a| = a := abs_of_nonneg ha
    exact isMonotone_threePoint (by rw [e1, ← e3]; exact h0) (by linarith)
      (by rw [e2, mul_zero]) hsum

/-- The **Lax–Friedrichs scheme is monotone under the CFL condition**: if $|\lambda a| \le 1$, its
weights $(1 \pm \lambda a)/2$ are nonnegative and sum to $1$. This is in §13.8.3 of
[quarteroni2000numerical]. -/
theorem laxFriedrichs_isMonotone {a lam : ℝ} (h : |lam * a| ≤ 1) :
    Stencil.IsMonotone (laxFriedrichs a lam) := by
  rw [abs_le] at h
  exact isMonotone_threePoint (by linarith [h.1]) le_rfl (by linarith [h.2]) (by ring)

/-! ### The local truncation error -/

/-- The **local truncation error** of the stencil $c$ for $u_t + a u_x = 0$ on the exact solution
$u(x, t) = u_0(x - a t)$, at the grid point whose characteristic foot is $\xi$:
$$\tau = \frac{1}{\Delta t} \Bigl( u_0(\xi - a \Delta t) - \sum_s c_s u_0(\xi - s \Delta x)
  \Bigr).$$
Here $u_0(\xi - a \Delta t)$ is the exact solution one step later and the sum is the scheme
applied to the exact solution. This is the truncation error of §13.8.1 of
[quarteroni2000numerical]; `FiniteDifference.Hyperbolic.truncationError_eq_of_isSolution` gives
the form at a grid point.

At $\Delta t = 0$ the quotient is $0$. -/
noncomputable def truncationError (c : Stencil) (a Δt Δx : ℝ) (u₀ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (u₀ (ξ - a * Δt) - Stencil.apply c (fun i : ℤ => u₀ (ξ + i * Δx)) 0) / Δt

/-- The truncation error of the three-point stencil with weights $(c_-, c_0, c_+)$ is
$$\tau = \frac{1}{\Delta t} \bigl( u_0(\xi - a \Delta t) - c_- u_0(\xi - \Delta x) - c_0
  u_0(\xi) - c_+ u_0(\xi + \Delta x) \bigr).$$
-/
theorem truncationError_threePoint (cm c0 cp a Δt Δx : ℝ) (u₀ : ℝ → ℝ) (ξ : ℝ) :
    truncationError (Stencil.threePoint cm c0 cp) a Δt Δx u₀ ξ
      = (u₀ (ξ - a * Δt) - (cm * u₀ (ξ - Δx) + c0 * u₀ ξ + cp * u₀ (ξ + Δx))) / Δt := by
  rw [truncationError, Stencil.threePoint_apply]
  simp only [smul_eq_mul]
  push_cast
  ring_nf

/-- The **truncation error is the residual of the exact solution**. Let $u$ be a classical solution
of $u_t + a u_x = 0$ on $t \ge 0$ with $u(\cdot, 0) = u_0$ (`Transport.IsSolution`), let $c$ be
a stencil, $\Delta t \ge 0$, $j \in \mathbb{Z}$ and $n \in \mathbb{N}$. With
$\xi = x_j - a t^n$, the foot of the characteristic through $(x_j, t^n)$,
$$\tau(\xi) = \frac{1}{\Delta t} \Bigl( u(x_j, t^{n+1}) - \sum_s c_s u(x_{j-s}, t^n) \Bigr).$$
This is the truncation error in the form of §13.8.1 of [quarteroni2000numerical]. -/
theorem truncationError_eq_of_isSolution {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : Transport.IsSolution (fun _ _ => a) 0 0 u₀ u) (c : Stencil) {Δt Δx : ℝ} (hΔt : 0 ≤ Δt)
    (j : ℤ) (n : ℕ) :
    truncationError c a Δt Δx u₀ ((j : ℝ) * Δx - a * (n * Δt))
      = (u ((j : ℝ) * Δx) (((n : ℝ) + 1) * Δt)
          - Stencil.apply c (fun i : ℤ => u ((i : ℝ) * Δx) (n * Δt)) j) / Δt := by
  have hn : (0 : ℝ) ≤ n * Δt := mul_nonneg (Nat.cast_nonneg n) hΔt
  have hn1 : (0 : ℝ) ≤ ((n : ℝ) + 1) * Δt := by positivity
  rw [truncationError, hu.eq_comp_sub _ hn1]
  congr 2
  · congr 1
    ring
  · rw [Stencil.apply_apply, Stencil.apply_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hu.eq_comp_sub _ hn]
    congr 2
    push_cast
    ring

/-! ### Consistency, order and convergence -/

/-- A family of stencils $c(\Delta t, \Delta x)$ is **of order $p$ in time and $q$ in space** for
the speed $a$ and the datum $u_0$ if there are $C$ and $\delta_0 > 0$ with
$$|\tau(\xi)| \le C (\Delta t^p + \Delta x^q)$$
for all $\Delta t, \Delta x \in (0, \delta_0]$ and all $\xi \in \mathbb{R}$, where $\tau$ is the
truncation error (`FiniteDifference.Hyperbolic.truncationError`) of $c(\Delta t, \Delta x)$.
This is the definition of §13.8.1 of [quarteroni2000numerical]. -/
def IsOfOrder (c : ℝ → ℝ → Stencil) (a : ℝ) (u₀ : ℝ → ℝ) (p q : ℕ) : Prop :=
  ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ Δt Δx : ℝ, 0 < Δt → Δt ≤ δ₀ → 0 < Δx → Δx ≤ δ₀ → ∀ ξ : ℝ,
    |truncationError (c Δt Δx) a Δt Δx u₀ ξ| ≤ C * (Δt ^ p + Δx ^ q)

/-- A family of stencils $c(\Delta t, \Delta x)$ is **consistent** for the speed $a$ and the datum
$u_0$ if
$$\tau(\Delta t, \Delta x) = \sup_{\xi \in \mathbb{R}} |\tau_\xi| \to 0$$
as $\Delta t \to 0^+$ and $\Delta x \to 0^+$ independently, where $\tau_\xi$ is the truncation
error (`FiniteDifference.Hyperbolic.truncationError`) of $c(\Delta t, \Delta x)$. This is the
definition of §13.8.1 of [quarteroni2000numerical].

The supremum is the real supremum `iSup`, which is $0$ when the set of values is unbounded
above. -/
def IsConsistent (c : ℝ → ℝ → Stencil) (a : ℝ) (u₀ : ℝ → ℝ) : Prop :=
  Tendsto (fun d : ℝ × ℝ => ⨆ ξ : ℝ, |truncationError (c d.1 d.2) a d.1 d.2 u₀ ξ|)
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Let $p, q \ge 1$. A family of stencils that is of order $p$ in time and $q$ in space
(`FiniteDifference.Hyperbolic.IsOfOrder`) is consistent
(`FiniteDifference.Hyperbolic.IsConsistent`). This is in §13.8.1 of [quarteroni2000numerical]. -/
theorem IsOfOrder.isConsistent {c : ℝ → ℝ → Stencil} {a : ℝ} {u₀ : ℝ → ℝ} {p q : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : IsOfOrder c a u₀ p q) : IsConsistent c a u₀ := by
  obtain ⟨C, δ₀, hδ₀, hC⟩ := h
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  have hle : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ≤ δ₀ := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [Ioo_mem_nhds (by linarith : -δ₀ < (0 : ℝ)) hδ₀] with x hx using hx.2.le
  have hone : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x ∧ x ≤ δ₀ := hpos.and hle
  refine squeeze_zero' (g := fun d : ℝ × ℝ => C * (d.1 ^ p + d.2 ^ q))
    (Filter.Eventually.of_forall fun d => Real.iSup_nonneg fun _ => abs_nonneg _) ?_ ?_
  · filter_upwards [hone.prod_mk hone] with d hd
    exact ciSup_le fun ξ => hC d.1 d.2 hd.1.1 hd.1.2 hd.2.1 hd.2.2 ξ
  · have h1 : Tendsto (fun d : ℝ × ℝ => d.1 ^ p) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (continuous_pow p).continuousAt.tendsto.comp
        ((tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds)
      simpa [Function.comp_def, zero_pow hp] using h
    have h2 : Tendsto (fun d : ℝ × ℝ => d.2 ^ q) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (continuous_pow q).continuousAt.tendsto.comp
        ((tendsto_snd (f := 𝓝[>] (0 : ℝ)) (g := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds)
      simpa [Function.comp_def, zero_pow hq] using h
    simpa using ((h1.add h2).const_mul C)

/-- A family of stencils $c(\Delta t, \Delta x)$ is **convergent** on the horizon $T$, for the speed
$a$ and the datum $u_0$, if for every $\varepsilon > 0$ there is $\delta_0 > 0$ such that
$$\bigl| u_0(x_j - a t^n) - (c(\Delta t, \Delta x)^n u^0)_j \bigr| \le \varepsilon$$
for all $\Delta t, \Delta x \in (0, \delta_0]$, all $j \in \mathbb{Z}$ and all
$n \in \mathbb{N}$ with $n \Delta t \le T$. Here $u^0_i = u_0(x_i)$ is the sampled datum and
$u_0(x_j - a t^n)$ is the exact solution at $(x_j, t^n)$. This is convergence at the grid
points, as in §13.8.1 of [quarteroni2000numerical].

The steps $\Delta t$ and $\Delta x$ tend to $0$ independently, so the definition asks for
convergence at every mesh ratio. -/
def IsConvergent (a : ℝ) (u₀ : ℝ → ℝ) (c : ℝ → ℝ → Stencil) (T : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ₀ > 0, ∀ Δt Δx : ℝ, 0 < Δt → Δt ≤ δ₀ → 0 < Δx → Δx ≤ δ₀ → ∀ (n : ℕ) (j : ℤ),
    (n : ℝ) * Δt ≤ T →
      |u₀ ((j : ℝ) * Δx - a * (n * Δt))
        - (Stencil.apply (c Δt Δx))^[n] (fun i : ℤ => u₀ ((i : ℝ) * Δx)) j| ≤ ε

/-! ### The truncation errors of the four schemes (Table 13.1) -/

section Truncation

variable {u₀ : ℝ → ℝ} {M₂ M₃ M₄ a Δt Δx lam ξ : ℝ}

/-- Let $u_0$ be $C^2$ with $|u_0''| \le M_2$. Then $|u_0(z - b s) - u_0(z) + b s u_0'(z)| \le M_2
(b s)^2 / 2$. -/
private theorem abs_timeRemainder_one_le (hu : ContDiff ℝ 2 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (b s z : ℝ) :
    |u₀ (z - b * s) - u₀ z + b * s * deriv u₀ z| ≤ M₂ * (b * s) ^ 2 / 2 := by
  have hb := abs_taylor_one hu hM₂ z (-(b * s))
  rw [show z + -(b * s) = z - b * s from by ring,
    show u₀ (z - b * s) - u₀ z - -(b * s) * deriv u₀ z
      = u₀ (z - b * s) - u₀ z + b * s * deriv u₀ z from by ring,
    show (-(b * s)) ^ 2 = (b * s) ^ 2 from by ring] at hb
  exact hb

/-- Let $u_0$ be $C^3$ with $|u_0'''| \le M_3$ and $w > 0$. Then $|u_0(z - w) - u_0(z) + w u_0'(z) -
(w^2/2) u_0''(z)| \le M_3 w^3 / 6$. -/
private theorem abs_spaceRemainder_two_left_le (hu : ContDiff ℝ 3 u₀)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) {w : ℝ} (hw : 0 < w) (z : ℝ) :
    |u₀ (z - w) - u₀ z + w * deriv u₀ z - w ^ 2 / 2 * iteratedDeriv 2 u₀ z|
      ≤ M₃ * w ^ 3 / 6 := by
  have hb := abs_taylor_two hu hM₃ z (-w)
  rw [show z + -w = z - w from by ring,
    show u₀ (z - w) - u₀ z - -w * deriv u₀ z - (-w) ^ 2 / 2 * iteratedDeriv 2 u₀ z
      = u₀ (z - w) - u₀ z + w * deriv u₀ z - w ^ 2 / 2 * iteratedDeriv 2 u₀ z from by ring,
    abs_neg, abs_of_pos hw] at hb
  exact hb

/-- Let $u_0$ be $C^3$ with $|u_0'''| \le M_3$ and $w > 0$. Then $|u_0(z + w) - u_0(z) - w u_0'(z) -
(w^2/2) u_0''(z)| \le M_3 w^3 / 6$. -/
private theorem abs_spaceRemainder_two_right_le (hu : ContDiff ℝ 3 u₀)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) {w : ℝ} (hw : 0 < w) (z : ℝ) :
    |u₀ (z + w) - u₀ z - w * deriv u₀ z - w ^ 2 / 2 * iteratedDeriv 2 u₀ z|
      ≤ M₃ * w ^ 3 / 6 := by
  have hb := abs_taylor_two hu hM₃ z w
  rwa [abs_of_pos hw] at hb

/-- The **truncation error of the forward Euler/centred scheme** is $O(\Delta t + \Delta x^2)$. Let
$u_0$ be $C^3$ with $|u_0''| \le M_2$ and $|u_0'''| \le M_3$, let $\Delta t, \Delta x > 0$ and
$\lambda = \Delta t / \Delta x$. Then for every $\xi$,
$$|\tau(\xi)| \le \frac{a^2}{2} M_2 \Delta t + \frac{|a|}{6} M_3 \Delta x^2.$$
This is the entry of Table 13.1 of [quarteroni2000numerical]. -/
theorem abs_truncationError_forwardEulerCentred_le (hu : ContDiff ℝ 3 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (forwardEulerCentred a lam) a Δt Δx u₀ ξ|
      ≤ a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2 := by
  subst hlam
  have hu2 : ContDiff ℝ 2 u₀ := hu.of_le (by norm_num)
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hR := abs_timeRemainder_one_le hu2 hM₂ a Δt ξ
  have hQ := abs_spaceRemainder_two_left_le hu hM₃ hΔx ξ
  have hP := abs_spaceRemainder_two_right_le hu hM₃ hΔx ξ
  have hid : truncationError (forwardEulerCentred a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
      = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ)
        - Δt / Δx * a / 2
          * ((u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)
            - (u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)) := by
    rw [forwardEulerCentred, truncationError_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |truncationError (forwardEulerCentred a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
      = |truncationError (forwardEulerCentred a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
        rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M₂ * (a * Δt) ^ 2 / 2 + Δt / Δx * |a| / 2 * (M₃ * Δx ^ 3 / 6 + M₃ * Δx ^ 3 / 6) := by
        rw [hid]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, show |Δt / Δx * a / 2| = Δt / Δx * |a| / 2 by
          rw [abs_div, abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]; norm_num]
        gcongr
        exact (abs_sub _ _).trans (by gcongr)
    _ = (a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2) * Δt := by field_simp; try ring

/-- The **truncation error of the Lax–Friedrichs scheme** is
$O(\Delta x^2/\Delta t + \Delta t + \Delta x^2)$. Let $u_0$ be $C^3$ with $|u_0''| \le M_2$ and
$|u_0'''| \le M_3$, let $\Delta t, \Delta x > 0$ and $\lambda = \Delta t / \Delta x$. Then for
every $\xi$,
$$|\tau(\xi)| \le \frac{M_2}{2} \frac{\Delta x^2}{\Delta t} + \frac{a^2}{2} M_2 \Delta t +
  \frac{|a|}{6} M_3 \Delta x^2.$$
This is the entry of Table 13.1 of [quarteroni2000numerical].

The bound tends to $0$ only if $\Delta x^2 / \Delta t \to 0$. -/
theorem abs_truncationError_laxFriedrichs_le (hu : ContDiff ℝ 3 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (laxFriedrichs a lam) a Δt Δx u₀ ξ|
      ≤ M₂ / 2 * Δx ^ 2 / Δt + a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2 := by
  subst hlam
  have hu2 : ContDiff ℝ 2 u₀ := hu.of_le (by norm_num)
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hR := abs_timeRemainder_one_le hu2 hM₂ a Δt ξ
  have hQ := abs_spaceRemainder_two_left_le hu hM₃ hΔx ξ
  have hP := abs_spaceRemainder_two_right_le hu hM₃ hΔx ξ
  have hT : |u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ| ≤ M₂ * Δx ^ 2 / 2 := by
    simpa using abs_timeRemainder_one_le hu2 hM₂ 1 Δx ξ
  have hS : |u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ| ≤ M₂ * Δx ^ 2 / 2 :=
    abs_taylor_one hu2 hM₂ ξ Δx
  have hid : truncationError (laxFriedrichs a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
      = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ)
        - ((u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ)
            + (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ)) / 2
        + Δt / Δx * a / 2
          * ((u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)
            - (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)) := by
    rw [laxFriedrichs, truncationError_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |truncationError (laxFriedrichs a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
      = |truncationError (laxFriedrichs a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
        rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M₂ * (a * Δt) ^ 2 / 2 + (M₂ * Δx ^ 2 / 2 + M₂ * Δx ^ 2 / 2) / 2
        + Δt / Δx * |a| / 2 * (M₃ * Δx ^ 3 / 6 + M₃ * Δx ^ 3 / 6) := by
        rw [hid]
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans ?_) ?_)
        · refine add_le_add hR ?_
          rw [abs_div, show |(2 : ℝ)| = 2 from abs_of_pos two_pos]
          gcongr
          exact (abs_add_le _ _).trans (add_le_add hS hT)
        · rw [abs_mul, show |Δt / Δx * a / 2| = Δt / Δx * |a| / 2 by
            rw [abs_div, abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]; norm_num]
          gcongr
          exact (abs_sub _ _).trans (by gcongr)
    _ = (M₂ / 2 * Δx ^ 2 / Δt + a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2) * Δt := by
        field_simp; try ring

/-- The **truncation error of the upwind scheme** is $O(\Delta t + \Delta x)$. Let $u_0$ be $C^2$
with $|u_0''| \le M_2$, let $\Delta t, \Delta x > 0$ and $\lambda = \Delta t / \Delta x$. Then
for every $\xi$,
$$|\tau(\xi)| \le \frac{a^2}{2} M_2 \Delta t + \frac{|a|}{2} M_2 \Delta x.$$
This is the entry of Table 13.1 of [quarteroni2000numerical]. -/
theorem abs_truncationError_upwind_le (hu : ContDiff ℝ 2 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (upwind a lam) a Δt Δx u₀ ξ|
      ≤ a ^ 2 / 2 * M₂ * Δt + |a| / 2 * M₂ * Δx := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ 0)
  have hR := abs_timeRemainder_one_le hu hM₂ a Δt ξ
  have hT : |u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ| ≤ M₂ * Δx ^ 2 / 2 := by
    simpa using abs_timeRemainder_one_le hu hM₂ 1 Δx ξ
  have hS : |u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ| ≤ M₂ * Δx ^ 2 / 2 := abs_taylor_one hu hM₂ ξ Δx
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hid : truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
        = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ)
          + Δt / Δx * a * (u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ) := by
      rw [upwind_eq_of_neg ha, truncationError_threePoint]
      field_simp
      ring
    refine le_of_mul_le_mul_right ?_ hΔt
    calc |truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
        = |truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
          rw [abs_mul, abs_of_pos hΔt]
      _ ≤ M₂ * (a * Δt) ^ 2 / 2 + Δt / Δx * |a| * (M₂ * Δx ^ 2 / 2) := by
          rw [hid]
          refine (abs_add_le _ _).trans (add_le_add hR ?_)
          rw [abs_mul, show |Δt / Δx * a| = Δt / Δx * |a| by
            rw [abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]]
          gcongr
      _ = (a ^ 2 / 2 * M₂ * Δt + |a| / 2 * M₂ * Δx) * Δt := by field_simp; try ring
  · subst ha
    have hid : truncationError (upwind 0 (Δt / Δx)) 0 Δt Δx u₀ ξ = 0 := by
      rw [upwind, truncationError_threePoint]
      norm_num
    rw [hid, abs_zero]
    positivity
  · have hid : truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
        = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ)
          - Δt / Δx * a * (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ) := by
      rw [upwind_eq_of_pos ha, truncationError_threePoint]
      field_simp
      ring
    refine le_of_mul_le_mul_right ?_ hΔt
    calc |truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
        = |truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
          rw [abs_mul, abs_of_pos hΔt]
      _ ≤ M₂ * (a * Δt) ^ 2 / 2 + Δt / Δx * |a| * (M₂ * Δx ^ 2 / 2) := by
          rw [hid]
          refine (abs_sub _ _).trans (add_le_add hR ?_)
          rw [abs_mul, show |Δt / Δx * a| = Δt / Δx * |a| by
            rw [abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]]
          gcongr
      _ = (a ^ 2 / 2 * M₂ * Δt + |a| / 2 * M₂ * Δx) * Δt := by field_simp; try ring

/-- The **truncation error of the Lax–Wendroff scheme** is $O(\Delta t^2 + \Delta x^2)$; it is the
only second-order scheme of §13.7 of [quarteroni2000numerical]. Let $u_0$ be $C^4$ with
$|u_0'''| \le M_3$ and $|u_0''''| \le M_4$, let $0 < \Delta t \le 1$, $0 < \Delta x \le 1$ and
$\lambda = \Delta t / \Delta x$. Then for every $\xi$,
$$|\tau(\xi)| \le \frac{|a|^3}{6} M_3 \Delta t^2 + \Bigl( \frac{|a|}{6} M_3 + \frac{|a| +
  a^2}{24} M_4 \Bigr) \Delta x^2.$$
This is the entry of Table 13.1 of [quarteroni2000numerical]. -/
theorem abs_truncationError_laxWendroff_le (hu : ContDiff ℝ 4 u₀)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) (hM₄ : ∀ y, |iteratedDeriv 4 u₀ y| ≤ M₄)
    (hΔt : 0 < Δt) (hΔt1 : Δt ≤ 1) (hΔx : 0 < Δx) (hΔx1 : Δx ≤ 1) (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (laxWendroff a lam) a Δt Δx u₀ ξ|
      ≤ |a| ^ 3 / 6 * M₃ * Δt ^ 2 + (|a| / 6 * M₃ + (|a| + a ^ 2) / 24 * M₄) * Δx ^ 2 := by
  subst hlam
  have hu3 : ContDiff ℝ 3 u₀ := hu.of_le (by norm_num)
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM₄0 : 0 ≤ M₄ := (abs_nonneg _).trans (hM₄ 0)
  have hE : |u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ
      - (a * Δt) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ| ≤ M₃ * |a * Δt| ^ 3 / 6 := by
    have h := abs_taylor_two hu3 hM₃ ξ (-(a * Δt))
    rw [show ξ + -(a * Δt) = ξ - a * Δt from by ring,
      show u₀ (ξ - a * Δt) - u₀ ξ - -(a * Δt) * deriv u₀ ξ
          - (-(a * Δt)) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
        = u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ
          - (a * Δt) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ from by ring, abs_neg] at h
    exact h
  have hFp : |u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
      - Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ| ≤ M₄ * Δx ^ 4 / 24 := abs_taylor_three hu hM₄ ξ Δx
  have hFm : |u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
      + Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ| ≤ M₄ * Δx ^ 4 / 24 := by
    have h := abs_taylor_three hu hM₄ ξ (-Δx)
    rw [show ξ + -Δx = ξ - Δx from by ring,
      show u₀ (ξ - Δx) - u₀ ξ - -Δx * deriv u₀ ξ - (-Δx) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
          - (-Δx) ^ 3 / 6 * iteratedDeriv 3 u₀ ξ
        = u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
          + Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ from by ring,
      show (-Δx) ^ 4 = Δx ^ 4 from by ring] at h
    exact h
  have hd3 : |iteratedDeriv 3 u₀ ξ| ≤ M₃ := hM₃ ξ
  have hid : truncationError (laxWendroff a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
      = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ
          - (a * Δt) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)
        + Δt / Δx * a * Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ
        + Δt / Δx * a / 2
          * ((u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
              - Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ)
            - (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
              + Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ))
        - (Δt / Δx) ^ 2 * a ^ 2 / 2
          * ((u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
              - Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ)
            + (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
              + Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ)) := by
    rw [laxWendroff, truncationError_threePoint]
    field_simp
    ring
  have habs1 : |Δt / Δx * a * Δx ^ 3 / 6| = Δt / Δx * |a| * Δx ^ 3 / 6 := by
    rw [abs_div, abs_mul, abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx,
      abs_of_pos (by positivity : (0 : ℝ) < Δx ^ 3), abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  have habs2 : |Δt / Δx * a / 2| = Δt / Δx * |a| / 2 := by
    rw [abs_div, abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]; norm_num
  have habs3 : |(Δt / Δx) ^ 2 * a ^ 2 / 2| = (Δt / Δx) ^ 2 * a ^ 2 / 2 :=
    abs_of_nonneg (by positivity)
  have hstep : |truncationError (laxWendroff a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
      ≤ M₃ * |a * Δt| ^ 3 / 6 + Δt / Δx * |a| * Δx ^ 3 / 6 * M₃
        + Δt / Δx * |a| / 2 * (M₄ * Δx ^ 4 / 24 + M₄ * Δx ^ 4 / 24)
        + (Δt / Δx) ^ 2 * a ^ 2 / 2 * (M₄ * Δx ^ 4 / 24 + M₄ * Δx ^ 4 / 24) := by
    calc |truncationError (laxWendroff a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
        = |truncationError (laxWendroff a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
          rw [abs_mul, abs_of_pos hΔt]
      _ ≤ _ := by
          rw [hid]
          refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add ((abs_add_le _ _).trans (add_le_add hE ?_)) ?_)) ?_)
          · rw [abs_mul, habs1]
            gcongr
          · rw [abs_mul, habs2]
            gcongr
            exact (abs_sub _ _).trans (by gcongr)
          · rw [abs_mul, habs3]
            gcongr
            exact (abs_add_le _ _).trans (by gcongr)
  have hrw : M₃ * |a * Δt| ^ 3 / 6 + Δt / Δx * |a| * Δx ^ 3 / 6 * M₃
        + Δt / Δx * |a| / 2 * (M₄ * Δx ^ 4 / 24 + M₄ * Δx ^ 4 / 24)
        + (Δt / Δx) ^ 2 * a ^ 2 / 2 * (M₄ * Δx ^ 4 / 24 + M₄ * Δx ^ 4 / 24)
      = (|a| ^ 3 / 6 * M₃ * Δt ^ 2 + |a| / 6 * M₃ * Δx ^ 2 + |a| / 24 * M₄ * Δx ^ 3
          + a ^ 2 / 24 * M₄ * (Δt * Δx ^ 2)) * Δt := by
    rw [abs_mul, abs_of_pos hΔt, mul_pow]
    field_simp
    ring
  have e1 : Δx ^ 3 ≤ Δx ^ 2 := by nlinarith
  have e2 : Δt * Δx ^ 2 ≤ Δx ^ 2 := by nlinarith
  have g1 : |a| / 24 * M₄ * Δx ^ 3 ≤ |a| / 24 * M₄ * Δx ^ 2 :=
    mul_le_mul_of_nonneg_left e1 (mul_nonneg (by positivity) hM₄0)
  have g2 : a ^ 2 / 24 * M₄ * (Δt * Δx ^ 2) ≤ a ^ 2 / 24 * M₄ * Δx ^ 2 :=
    mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hM₄0)
  refine le_of_mul_le_mul_right ?_ hΔt
  refine (hstep.trans (le_of_eq hrw)).trans (mul_le_mul_of_nonneg_right ?_ hΔt.le)
  nlinarith [g1, g2]

end Truncation

/-! ### The CFL condition -/

/-- The **Courant–Friedrichs–Lewy (CFL) condition** for the speed $a$ and the mesh ratio
$\lambda = \Delta t / \Delta x$ is $|a \lambda| \le 1$. This is (13.48) of
[quarteroni2000numerical]. -/
def CFL (a lam : ℝ) : Prop := |a * lam| ≤ 1

/-- The **CFL condition for a variable speed** $a(x, t)$ is
$$\Delta t \sup_{(x, t) \in \mathbb{R}^2} |a(x, t)| \le \Delta x.$$
This is in §13.8.3 of [quarteroni2000numerical].

The supremum is the real supremum `iSup`, which is $0$ when $|a|$ is unbounded; then the
condition reduces to $0 \le \Delta x$. -/
def CFLVariable (a : ℝ → ℝ → ℝ) (Δt Δx : ℝ) : Prop :=
  Δt * (⨆ q : ℝ × ℝ, |a q.1 q.2|) ≤ Δx

/-- The **CFL condition for a hyperbolic system** with the eigenvalues $\lambda_1, \dots, \lambda_p$
is $|\lambda_k \Delta t / \Delta x| \le 1$ for every $k$. This is in §13.8.3 of
[quarteroni2000numerical]. -/
def CFLSystem {p : ℕ} (lam : Fin p → ℝ) (Δt Δx : ℝ) : Prop := ∀ k, |lam k * Δt / Δx| ≤ 1

/-! ### The CFL condition is necessary -/

/-- Iterating a stencil on the zero grid function gives zero. -/
private theorem iterate_apply_zero (c : Stencil) (n : ℕ) :
    (Stencil.apply c)^[n] (0 : ℤ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    exact map_zero (Stencil.applyₗ c)

/-- The **CFL condition is necessary for convergence**. Let $\lambda > 0$ with $|a| \lambda > 1$,
and let $c(\Delta t, \Delta x)$ be any family of stencils supported in $\{-1, 0, 1\}$. Then
there is a smooth datum $u_0$ for which the family is not convergent on the horizon $T = 1$
(`FiniteDifference.Hyperbolic.IsConvergent`). This is in §13.8.3 of [quarteroni2000numerical].

The steps are chosen with $\Delta t = \lambda \Delta x$. The numerical domain of dependence of
the point $(0, 1)$ then lies in $|x| \le 1/\lambda$
(`FiniteDifference.Stencil.iterate_apply_congr_of_eqOn`), while the exact solution there is the
datum at $-a$, which lies outside. So a smooth bump datum concentrated near $-a$ gives the
numerical value $0$ and the exact value $1$. §13.8.3 of the source also calls the CFL condition
sufficient for stability; this is false, because the forward Euler/centred scheme is unstable
for every $\lambda$ (`FiniteDifference.Hyperbolic.forwardEulerCentred_not_isStableFamily`). -/
theorem not_isConvergent_of_one_lt_abs_mul {a lam : ℝ} (hlam : 0 < lam) (hcfl : 1 < |a| * lam)
    (c : ℝ → ℝ → Stencil) (hc : ∀ Δt Δx : ℝ, ∀ s ∈ (c Δt Δx).support, |s| ≤ 1) :
    ∃ u₀ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u₀ ∧ ¬ IsConvergent a u₀ c 1 := by
  have hinv : 1 / lam < |a| := by rw [div_lt_iff₀ hlam]; linarith
  set r : ℝ := (|a| - 1 / lam) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  set f : ContDiffBump (-a) := ⟨r / 2, r, by positivity, by linarith⟩ with hf
  refine ⟨f, f.contDiff, ?_⟩
  intro hconv
  obtain ⟨δ₀, hδ₀, hbound⟩ := hconv (1 / 2) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / δ₀) (1 / (lam * δ₀)))
  set n : ℕ := m + 1 with hn
  have hmax : 0 < max (1 / δ₀) (1 / (lam * δ₀)) := lt_max_of_lt_left (by positivity)
  have hnR : max (1 / δ₀) (1 / (lam * δ₀)) < (n : ℝ) := by
    rw [hn]
    push_cast
    linarith
  have hnpos : (0 : ℝ) < n := lt_trans hmax hnR
  set Δt : ℝ := 1 / n with hΔt
  set Δx : ℝ := 1 / (n * lam) with hΔx
  have hΔtpos : 0 < Δt := by rw [hΔt]; positivity
  have hΔxpos : 0 < Δx := by rw [hΔx]; positivity
  have hΔtle : Δt ≤ δ₀ := by
    rw [hΔt, div_le_iff₀ hnpos]
    have h1 : 1 / δ₀ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hnR
    rw [div_lt_iff₀ hδ₀] at h1
    linarith
  have hΔxle : Δx ≤ δ₀ := by
    rw [hΔx, div_le_iff₀ (by positivity)]
    have h1 : 1 / (lam * δ₀) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hnR
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  have hnΔt : (n : ℝ) * Δt = 1 := by rw [hΔt]; field_simp
  have hnΔx : (n : ℝ) * Δx = 1 / lam := by rw [hΔx]; field_simp
  have hzero : ∀ i : ℤ, |i - 0| ≤ (n : ℤ) * 1 → f ((i : ℝ) * Δx) = 0 := by
    intro i hi
    have hiabs : |(i : ℝ)| ≤ (n : ℝ) := by
      rw [sub_zero, mul_one] at hi
      exact_mod_cast hi
    have hbd : |(i : ℝ) * Δx| ≤ 1 / lam := by
      rw [abs_mul, abs_of_pos hΔxpos, ← hnΔx]
      exact mul_le_mul_of_nonneg_right hiabs hΔxpos.le
    have hdist : r ≤ |(i : ℝ) * Δx - -a| := by
      have h1 : |a| - |(i : ℝ) * Δx| ≤ |(i : ℝ) * Δx + a| := by
        have h4 := abs_sub ((i : ℝ) * Δx + a) ((i : ℝ) * Δx)
        rw [show (i : ℝ) * Δx + a - (i : ℝ) * Δx = a from by ring] at h4
        linarith
      have h3 : (i : ℝ) * Δx - -a = (i : ℝ) * Δx + a := by ring
      rw [h3]
      rw [hr]
      linarith
    refine f.zero_of_le_dist ?_
    rw [Real.dist_eq]
    exact hdist
  have hnum : (Stencil.apply (c Δt Δx))^[n] (fun i : ℤ => f ((i : ℝ) * Δx)) 0 = 0 := by
    rw [Stencil.iterate_apply_congr_of_eqOn (hc Δt Δx) n (v := (0 : ℤ → ℝ)) hzero,
      iterate_apply_zero]
    rfl
  have hexact : f ((0 : ℤ) * Δx - a * ((n : ℝ) * Δt)) = 1 := by
    rw [hnΔt]
    have h0 : ((0 : ℤ) : ℝ) * Δx - a * 1 = -a := by push_cast; ring
    rw [h0]
    exact f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
  have := hbound Δt Δx hΔtpos hΔtle hΔxpos hΔxle n 0 (by rw [hnΔt])
  rw [hnum, hexact] at this
  norm_num at this

/-! ### Multi-level schemes for the wave equation -/

/-- The **leap-frog scheme** for the wave equation $u_{tt} = \gamma^2 u_{xx}$: the grid values
$u^n_j$ satisfy
$$u^{n+2}_j - 2 u^{n+1}_j + u^n_j = (\gamma \lambda)^2 (u^{n+1}_{j+1} - 2 u^{n+1}_j +
  u^{n+1}_{j-1})$$
for all $n \in \mathbb{N}$ and $j \in \mathbb{Z}$. This is (13.44) of [quarteroni2000numerical]. -/
def IsLeapFrog (γ lam : ℝ) (u : ℕ → ℤ → ℝ) : Prop :=
  ∀ n j, u (n + 2) j - 2 * u (n + 1) j + u n j
    = (γ * lam) ^ 2 * (u (n + 1) (j + 1) - 2 * u (n + 1) j + u (n + 1) (j - 1))

/-- The **Newmark scheme** for the wave equation $u_{tt} = \gamma^2 u_{xx}$, with the parameters
$\beta$ and $\theta$ and the auxiliary velocity $v$: for all $n \in \mathbb{N}$ and
$j \in \mathbb{Z}$, with $\delta^2 w_j = w_{j+1} - 2 w_j + w_{j-1}$,
$$u^{n+1}_j - u^n_j = \Delta t\, v^n_j + (\gamma \lambda)^2 \bigl(\beta\, \delta^2 u^{n+1}_j +
  (\tfrac{1}{2} - \beta)\, \delta^2 u^n_j\bigr),$$
$$v^{n+1}_j - v^n_j = \frac{(\gamma \lambda)^2}{\Delta t} \bigl(\theta\, \delta^2 u^{n+1}_j +
  (1 - \theta)\, \delta^2 u^n_j\bigr).$$
This is (13.45) of [quarteroni2000numerical], where $\beta \in [0, 1/2]$ and
$\theta \in [0, 1]$.

The definition puts no condition on $\beta$ and $\theta$. -/
def IsNewmark (γ lam Δt β θ : ℝ) (u v : ℕ → ℤ → ℝ) : Prop :=
  ∀ n j,
    u (n + 1) j - u n j = Δt * v n j
        + (γ * lam) ^ 2 * (β * (u (n + 1) (j + 1) - 2 * u (n + 1) j + u (n + 1) (j - 1))
          + (1 / 2 - β) * (u n (j + 1) - 2 * u n j + u n (j - 1))) ∧
      v (n + 1) j - v n j = (γ * lam) ^ 2 / Δt
        * (θ * (u (n + 1) (j + 1) - 2 * u (n + 1) j + u (n + 1) (j - 1))
          + (1 - θ) * (u n (j + 1) - 2 * u n j + u n (j - 1)))

/-! ### Amplification factors -/

section Amplification

variable {N : ℕ}

/-- The **phase angle of the $k$-th mode** on the periodic grid of $N$ points is
$\varphi_k = 2 \pi k / N$. This is in §13.9 of [quarteroni2000numerical]. -/
noncomputable def gridPhase (N : ℕ) (k : Fin N) : ℝ := 2 * π * k / N

/-- The phase angle $\varphi_k$, as a complex number, is $2 \pi k / N$. -/
private theorem ofReal_gridPhase (N : ℕ) (k : Fin N) :
    ((gridPhase N k : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * ((k : ℕ) : ℂ) / (N : ℂ) := by
  rw [gridPhase]
  push_cast
  ring

/-- For real $x$, $e^{i x} = \cos x + i \sin x$. -/
private theorem exp_mul_I' (x : ℝ) :
    Complex.exp (I * x) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- For real $x$, $e^{-i x} = \cos x - i \sin x$. -/
private theorem exp_neg_mul_I' (x : ℝ) :
    Complex.exp (-(I * x)) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * I := by
  rw [show -(I * (x : ℂ)) = I * ((-x : ℝ) : ℂ) by push_cast; ring, exp_mul_I', Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

/-- For real $x$ and $y$, $|x + i y|^2 = x^2 + y^2$. -/
private theorem normSq_add_mul_I' (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

variable [NeZero N]

/-- The **amplification factor of the forward Euler/centred scheme** on the periodic grid of $N$
points is
$$\gamma_k = 1 - i \lambda a \sin \varphi_k.$$
This is in §13.8.4 of [quarteroni2000numerical]. -/
theorem amplificationFactor_forwardEulerCentred (a lam : ℝ) (k : Fin N) :
    amplificationFactor (Stencil.toPeriodic N (forwardEulerCentred a lam)) k
      = 1 - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ) := by
  rw [forwardEulerCentred, Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I']
  push_cast
  ring

/-- The squared modulus of the amplification factor of the forward Euler/centred scheme is
$$|\gamma_k|^2 = 1 + (\lambda a \sin \varphi_k)^2,$$
which is at least $1$ for every mesh. This is in §13.8.4 of [quarteroni2000numerical]. -/
theorem norm_amplificationFactor_forwardEulerCentred_sq (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor (Stencil.toPeriodic N (forwardEulerCentred a lam)) k‖ ^ 2
      = 1 + (lam * a) ^ 2 * Real.sin (gridPhase N k) ^ 2 := by
  rw [amplificationFactor_forwardEulerCentred,
    show (1 : ℂ) - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
      = ((1 : ℝ) : ℂ) + ((-(lam * a * Real.sin (gridPhase N k)) : ℝ) : ℂ) * I by push_cast; ring,
    normSq_add_mul_I']
  ring

/-- The **forward Euler/centred scheme amplifies every mode with
$\lambda a \sin \varphi_k \neq 0$**: for such $k$, $|\gamma_k| > 1$. This is in §13.8.4 of
[quarteroni2000numerical]. -/
theorem one_lt_norm_amplificationFactor_forwardEulerCentred {a lam : ℝ} {k : Fin N}
    (h : lam * a * Real.sin (gridPhase N k) ≠ 0) :
    1 < ‖amplificationFactor (Stencil.toPeriodic N (forwardEulerCentred a lam)) k‖ := by
  have hsq := norm_amplificationFactor_forwardEulerCentred_sq a lam k
  have hpos : 0 < (lam * a * Real.sin (gridPhase N k)) ^ 2 := by positivity
  nlinarith [norm_nonneg (amplificationFactor (Stencil.toPeriodic N (forwardEulerCentred a lam)) k)]

/-- The **amplification factor of the upwind scheme** on the periodic grid of $N$ points is
$$\gamma_k = 1 - \lambda |a| (1 - \cos \varphi_k) - i \lambda a \sin \varphi_k,$$
one formula for both signs of $a$. This is Exercise 13.6 of [quarteroni2000numerical]. -/
theorem amplificationFactor_upwind (a lam : ℝ) (k : Fin N) :
    amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k
      = ((1 - lam * |a| * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ) := by
  rw [upwind, Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I',
    max_zero_eq, max_neg_zero_eq]
  push_cast
  ring

/-- The squared modulus of the amplification factor of the upwind scheme is
$$|\gamma_k|^2 = 1 - 2 \lambda |a| (1 - \lambda |a|) (1 - \cos \varphi_k).$$
This is Exercise 13.6 of [quarteroni2000numerical]. -/
theorem norm_amplificationFactor_upwind_sq (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k‖ ^ 2
      = 1 - 2 * (lam * |a|) * (1 - lam * |a|) * (1 - Real.cos (gridPhase N k)) := by
  have hpy := Real.sin_sq_add_cos_sq (gridPhase N k)
  have habs : |a| ^ 2 = a ^ 2 := sq_abs a
  rw [amplificationFactor_upwind,
    show ((1 - lam * |a| * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
      = ((1 - lam * |a| * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        + ((-(lam * a * Real.sin (gridPhase N k)) : ℝ) : ℂ) * I by push_cast; ring,
    normSq_add_mul_I']
  linear_combination (lam ^ 2 * a ^ 2) * hpy
    + (lam ^ 2 * ((1 - Real.cos (gridPhase N k)) ^ 2 - 2 * (1 - Real.cos (gridPhase N k)))) * habs

/-- The **amplification factor of the Lax–Friedrichs scheme** on the periodic grid of $N$ points is
$$\gamma_k = \cos \varphi_k - i \lambda a \sin \varphi_k.$$
-/
theorem amplificationFactor_laxFriedrichs (a lam : ℝ) (k : Fin N) :
    amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k
      = (Real.cos (gridPhase N k) : ℂ) - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ) := by
  rw [laxFriedrichs, Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I']
  push_cast
  ring

/-- The squared modulus of the amplification factor of the Lax–Friedrichs scheme is
$$|\gamma_k|^2 = \cos^2 \varphi_k + (\lambda a)^2 \sin^2 \varphi_k.$$
-/
theorem norm_amplificationFactor_laxFriedrichs_sq (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k‖ ^ 2
      = Real.cos (gridPhase N k) ^ 2 + (lam * a) ^ 2 * Real.sin (gridPhase N k) ^ 2 := by
  rw [amplificationFactor_laxFriedrichs,
    show (Real.cos (gridPhase N k) : ℂ) - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
      = ((Real.cos (gridPhase N k) : ℝ) : ℂ)
        + ((-(lam * a * Real.sin (gridPhase N k)) : ℝ) : ℂ) * I by push_cast; ring,
    normSq_add_mul_I']
  ring

/-- The **amplification factor of the Lax–Wendroff scheme** on the periodic grid of $N$ points is
$$\gamma_k = 1 - (\lambda a)^2 (1 - \cos \varphi_k) - i \lambda a \sin \varphi_k.$$
-/
theorem amplificationFactor_laxWendroff (a lam : ℝ) (k : Fin N) :
    amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k
      = ((1 - (lam * a) ^ 2 * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ) := by
  rw [laxWendroff, Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I']
  push_cast
  ring

/-- The squared modulus of the amplification factor of the Lax–Wendroff scheme is
$$|\gamma_k|^2 = 1 - (\lambda a)^2 \bigl(1 - (\lambda a)^2\bigr) (1 - \cos \varphi_k)^2,$$
which equals $1 - 4 (\lambda a)^2 (1 - (\lambda a)^2) \sin^4(\varphi_k / 2)$. -/
theorem norm_amplificationFactor_laxWendroff_sq (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k‖ ^ 2
      = 1 - (lam * a) ^ 2 * (1 - (lam * a) ^ 2) * (1 - Real.cos (gridPhase N k)) ^ 2 := by
  have hpy := Real.sin_sq_add_cos_sq (gridPhase N k)
  rw [amplificationFactor_laxWendroff,
    show ((1 - (lam * a) ^ 2 * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
      = ((1 - (lam * a) ^ 2 * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        + ((-(lam * a * Real.sin (gridPhase N k)) : ℝ) : ℂ) * I by push_cast; ring,
    normSq_add_mul_I']
  linear_combination ((lam * a) ^ 2) * hpy

/-!
### The stability conditions of Table 13.1

By von Neumann's sufficient condition, Theorem 13.1 of [quarteroni2000numerical]
(`FiniteDifference.norm_toEuclideanLin_periodicScheme_pow_le`), a periodic scheme whose
amplification factors all have modulus at most $1$ satisfies $\|Q^n u\|_2 \le \|u\|_2$ for every
$n$. The results below characterize this condition for the upwind, Lax–Friedrichs and Lax–Wendroff
schemes.
-/

omit [NeZero N] in
/-- On a grid of $N \ge 2$ points, the mode $k = 1$ has $\cos \varphi_1 < 1$. -/
private theorem cos_gridPhase_lt_one (hN : 2 ≤ N) {k : Fin N} (hk : (k : ℕ) = 1) :
    Real.cos (gridPhase N k) < 1 := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hval : gridPhase N k = 2 * π / N := by rw [gridPhase, hk]; push_cast; ring
  have hpos : 0 < gridPhase N k := by rw [hval]; positivity
  have hle : gridPhase N k ≤ π := by
    rw [hval, div_le_iff₀ hN0]
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  simpa using Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hle hpos

omit [NeZero N] in
/-- On a grid of $N \ge 3$ points, the mode $k = 1$ has $\sin \varphi_1 > 0$. -/
private theorem sin_gridPhase_pos (hN : 3 ≤ N) {k : Fin N} (hk : (k : ℕ) = 1) :
    0 < Real.sin (gridPhase N k) := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hval : gridPhase N k = 2 * π / N := by rw [gridPhase, hk]; push_cast; ring
  have hpos : 0 < gridPhase N k := by rw [hval]; positivity
  have hlt : gridPhase N k < π := by
    rw [hval, div_lt_iff₀ hN0]
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi hpos hlt

/-- The **stability condition of the upwind scheme is the CFL condition**. Let $N \ge 2$ and
$\lambda \ge 0$. All amplification factors of the upwind scheme on the periodic grid of $N$
points have modulus at most $1$ if and only if $\lambda |a| \le 1$. This is Exercise 13.6 of
[quarteroni2000numerical]. -/
theorem norm_amplificationFactor_upwind_le_one_iff (hN : 2 ≤ N) {a lam : ℝ} (hlam : 0 ≤ lam) :
    (∀ k : Fin N, ‖amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k‖ ≤ 1)
      ↔ lam * |a| ≤ 1 := by
  have hmul : 0 ≤ lam * |a| := mul_nonneg hlam (abs_nonneg a)
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    set k₁ : Fin N := ⟨1, by omega⟩ with hk₁def
    have hk₁ : (k₁ : ℕ) = 1 := rfl
    have hk := h k₁
    have hsq := norm_amplificationFactor_upwind_sq a lam k₁
    have hcos := cos_gridPhase_lt_one hN hk₁
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k₁)
    have hsq1 := (sq_le_one_iff₀ hnn).mpr hk
    have h3 : 2 * (lam * |a|) * (1 - lam * |a|) * (1 - Real.cos (gridPhase N k₁)) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by linarith)
    linarith
  · intro h k
    have hsq := norm_amplificationFactor_upwind_sq a lam k
    have hcos : Real.cos (gridPhase N k) ≤ 1 := Real.cos_le_one _
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k)
    have h3 : 0 ≤ 2 * (lam * |a|) * (1 - lam * |a|) * (1 - Real.cos (gridPhase N k)) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    exact (sq_le_one_iff₀ hnn).mp (by linarith)

/-- The **stability condition of the Lax–Friedrichs scheme is the CFL condition**. Let $N \ge 3$.
All amplification factors of the Lax–Friedrichs scheme on the periodic grid of $N$ points have
modulus at most $1$ if and only if $|\lambda a| \le 1$. This is in §13.8.3 of
[quarteroni2000numerical]. -/
theorem norm_amplificationFactor_laxFriedrichs_le_one_iff (hN : 3 ≤ N) (a lam : ℝ) :
    (∀ k : Fin N, ‖amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k‖ ≤ 1)
      ↔ |lam * a| ≤ 1 := by
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    set k₁ : Fin N := ⟨1, by omega⟩ with hk₁def
    have hk₁ : (k₁ : ℕ) = 1 := rfl
    have hk := h k₁
    have hsq := norm_amplificationFactor_laxFriedrichs_sq a lam k₁
    have hsin := sin_gridPhase_pos hN hk₁
    have hpy := Real.sin_sq_add_cos_sq (gridPhase N k₁)
    have habs : 1 < (lam * a) ^ 2 := by nlinarith [abs_nonneg (lam * a), sq_abs (lam * a)]
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k₁)
    have hsq1 := (sq_le_one_iff₀ hnn).mpr hk
    have hs2 : 0 < Real.sin (gridPhase N k₁) ^ 2 := by positivity
    have h3 : 0 < ((lam * a) ^ 2 - 1) * Real.sin (gridPhase N k₁) ^ 2 :=
      mul_pos (by linarith) hs2
    nlinarith
  · intro h k
    have hsq := norm_amplificationFactor_laxFriedrichs_sq a lam k
    have hpy := Real.sin_sq_add_cos_sq (gridPhase N k)
    have habs : (lam * a) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (lam * a), sq_abs (lam * a)]
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k)
    have h3 : 0 ≤ (1 - (lam * a) ^ 2) * Real.sin (gridPhase N k) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    exact (sq_le_one_iff₀ hnn).mp (by nlinarith)

/-- The **stability condition of the Lax–Wendroff scheme is the CFL condition**. Let $N \ge 2$. All
amplification factors of the Lax–Wendroff scheme on the periodic grid of $N$ points have modulus
at most $1$ if and only if $|\lambda a| \le 1$. This is in §13.8.3 of [quarteroni2000numerical]. -/
theorem norm_amplificationFactor_laxWendroff_le_one_iff (hN : 2 ≤ N) (a lam : ℝ) :
    (∀ k : Fin N, ‖amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k‖ ≤ 1)
      ↔ |lam * a| ≤ 1 := by
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    set k₁ : Fin N := ⟨1, by omega⟩ with hk₁def
    have hk₁ : (k₁ : ℕ) = 1 := rfl
    have hk := h k₁
    have hsq := norm_amplificationFactor_laxWendroff_sq a lam k₁
    have hcos := cos_gridPhase_lt_one hN hk₁
    have habs : 1 < (lam * a) ^ 2 := by nlinarith [abs_nonneg (lam * a), sq_abs (lam * a)]
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k₁)
    have hsq1 := (sq_le_one_iff₀ hnn).mpr hk
    have hc2 : 0 < (1 - Real.cos (gridPhase N k₁)) ^ 2 := by positivity
    have h3 : (lam * a) ^ 2 * (1 - (lam * a) ^ 2) * (1 - Real.cos (gridPhase N k₁)) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) hc2
    linarith
  · intro h k
    have hsq := norm_amplificationFactor_laxWendroff_sq a lam k
    have habs : (lam * a) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (lam * a), sq_abs (lam * a)]
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k)
    have h3 : 0 ≤ (lam * a) ^ 2 * (1 - (lam * a) ^ 2) * (1 - Real.cos (gridPhase N k)) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (sq_nonneg _)
    exact (sq_le_one_iff₀ hnn).mp (by linarith)

/-- The **amplification factor of the backward Euler/centred scheme** $u^{n+1}_j + (\lambda
a/2)(u^{n+1}_{j+1} - u^{n+1}_{j-1}) = u^n_j$ on the periodic grid of $N$ points is
$$\gamma_k = \frac{1}{1 + i \lambda a \sin \varphi_k}.$$
This is (13.43) of [quarteroni2000numerical].

The scheme is the implicit two-level scheme of `FiniteDifference.amplificationFactor₂`, with the
three-point stencil of weights $(-\lambda a/2, 1, \lambda a/2)$ on the left and the identity
stencil on the right. -/
theorem amplificationFactor₂_backwardEulerCentred (a lam : ℝ) (k : Fin N) :
    amplificationFactor₂ (Stencil.toPeriodic N (Stencil.threePoint (-(lam * a / 2)) 1
        (lam * a / 2))) (Stencil.toPeriodic N (Stencil.threePoint 0 1 0)) k
      = 1 / (1 + I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)) := by
  rw [amplificationFactor₂, Stencil.amplificationFactor_toPeriodic_threePoint,
    Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I']
  push_cast
  ring_nf

/-- The **backward Euler/centred scheme is unconditionally stable in $\ell^2$**: for all $a$,
$\lambda$ and $k$, its amplification factor satisfies $|\gamma_k| \le 1$. This is in §13.8.2 of
[quarteroni2000numerical]. -/
theorem norm_amplificationFactor₂_backwardEulerCentred_le_one (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor₂ (Stencil.toPeriodic N (Stencil.threePoint (-(lam * a / 2)) 1
        (lam * a / 2))) (Stencil.toPeriodic N (Stencil.threePoint 0 1 0)) k‖ ≤ 1 := by
  rw [amplificationFactor₂_backwardEulerCentred, norm_div, norm_one]
  have hden : ‖(1 : ℂ) + I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)‖ ^ 2
      = 1 + (lam * a) ^ 2 * Real.sin (gridPhase N k) ^ 2 := by
    rw [show (1 : ℂ) + I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
        = ((1 : ℝ) : ℂ) + ((lam * a * Real.sin (gridPhase N k) : ℝ) : ℂ) * I by push_cast; ring,
      normSq_add_mul_I']
    ring
  have h1 : 1 ≤ ‖(1 : ℂ) + I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)‖ :=
    (one_le_sq_iff₀ (norm_nonneg _)).mp (by
      rw [hden]
      nlinarith [sq_nonneg (lam * a), sq_nonneg (Real.sin (gridPhase N k))])
  rw [div_le_one (by linarith)]
  exact h1

end Amplification

/-! ### The implicit backward Euler/centred scheme on $\ell^2(\mathbb{Z})$ -/

section Implicit

/-- The **centred difference** $(D_0 u)_j = u_{j+1} - u_{j-1}$, as a bounded operator on
$\ell^2(\mathbb{Z})$. It appears in (13.43) of [quarteroni2000numerical]. -/
noncomputable def centredDiffCLM : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  Stencil.lpCLM (Stencil.threePoint (-1) 0 1) 2

/-- The centred difference acts by $(D_0 u)_j = u_{j+1} - u_{j-1}$. -/
theorem centredDiffCLM_apply (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    centredDiffCLM u j = u (j + 1) - u (j - 1) := by
  rw [centredDiffCLM, Stencil.lpCLM_apply, Stencil.threePoint_apply]
  simp only [smul_eq_mul, neg_mul, one_mul, zero_mul]
  ring

/-- The shifts $(S_s u)_j = u_{j-s}$ on $\ell^2(\mathbb{Z})$ satisfy $S_s S_t = S_{s+t}$. -/
private theorem shift_shift (s t : ℤ) (u : lp (fun _ : ℤ => ℝ) 2) :
    lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 s (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 t u)
      = lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (s + t) u := by
  refine lp.ext (funext fun j => ?_)
  simp only [lp.shiftₗᵢ_apply]
  rw [sub_sub]

/-- The shift $S_0$ is the identity. -/
private theorem shift_zero (u : lp (fun _ : ℤ => ℝ) 2) :
    lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 0 u = u := by
  refine lp.ext (funext fun j => ?_)
  simp

/-- The **shift is unitary**: the shift $(S_s u)_j = u_{j-s}$ on $\ell^2(\mathbb{Z})$ satisfies
$\langle S_s u, v \rangle = \langle u, S_{-s} v \rangle$ for all $u, v$. -/
theorem inner_shift_left (s : ℤ) (u v : lp (fun _ : ℤ => ℝ) 2) :
    inner ℝ (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 s u) v
      = inner ℝ u (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-s) v) := by
  have hv : lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 s (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-s) v) = v := by
    rw [shift_shift, add_neg_cancel, shift_zero]
  conv_lhs => rw [← hv]
  exact (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 s).inner_map_map u _

/-- The centred difference is $D_0 = S_{-1} - S_1$, where $(S_s u)_j = u_{j-s}$. -/
private theorem centredDiffCLM_eq_sub (u : lp (fun _ : ℤ => ℝ) 2) :
    centredDiffCLM u
      = lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-1) u - lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 1 u := by
  refine lp.ext (funext fun j => ?_)
  rw [lp.coeFn_sub]
  simp [centredDiffCLM_apply, sub_neg_eq_add]

/-- The **centred difference is skew-adjoint** on $\ell^2(\mathbb{Z})$: $\langle D_0 u, v \rangle =
-\langle u, D_0 v \rangle$ for all $u, v$. This is in Exercise 13.7 of
[quarteroni2000numerical]. -/
theorem inner_centredDiffCLM_left (u v : lp (fun _ : ℤ => ℝ) 2) :
    inner ℝ (centredDiffCLM u) v = -inner ℝ u (centredDiffCLM v) := by
  rw [centredDiffCLM_eq_sub u, centredDiffCLM_eq_sub v, inner_sub_left, inner_sub_right,
    inner_shift_left, inner_shift_left]
  norm_num

/-- The **quadratic form of the centred difference vanishes**: $\langle D_0 u, u \rangle = 0$ for
every $u \in \ell^2(\mathbb{Z})$. This is the telescoping sum of Exercise 13.7 of
[quarteroni2000numerical]. -/
theorem inner_centredDiffCLM_self (u : lp (fun _ : ℤ => ℝ) 2) :
    inner ℝ (centredDiffCLM u) u = 0 := by
  have h := inner_centredDiffCLM_left u u
  have h2 : inner ℝ u (centredDiffCLM u) = inner ℝ (centredDiffCLM u) u := real_inner_comm _ _
  linarith

/-- The **operator of the implicit backward Euler/centred scheme**, $B = 1 + (\lambda a / 2) D_0$ on
$\ell^2(\mathbb{Z})$, which acts on the new time level: the scheme is $B u^{n+1} = u^n$. This is
(13.43) of [quarteroni2000numerical]. -/
noncomputable def backwardEulerCentredOp (a lam : ℝ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  ContinuousLinearMap.id ℝ _ + (lam * a / 2) • centredDiffCLM

/-- The scheme operator acts by $(B u)_j = u_j + (\lambda a / 2)(u_{j+1} - u_{j-1})$. -/
theorem backwardEulerCentredOp_apply (a lam : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    backwardEulerCentredOp a lam u j = u j + lam * a / 2 * (u (j + 1) - u (j - 1)) := by
  have h : backwardEulerCentredOp a lam u = u + (lam * a / 2) • centredDiffCLM u := rfl
  rw [h, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    centredDiffCLM_apply]

/-- The **scheme operator is coercive with constant $1$**: $\|u\|^2 \le \langle B u, u \rangle$ for
every $u \in \ell^2(\mathbb{Z})$. In fact $\langle B u, u \rangle = \|u\|^2$, because the
centred difference is skew-adjoint. This is in Exercise 13.7 of [quarteroni2000numerical]. -/
theorem backwardEulerCentredOp_isCoerciveWith (a lam : ℝ) :
    ((backwardEulerCentredOp a lam : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2) :
      lp (fun _ : ℤ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℤ => ℝ) 2).IsCoerciveWith 1 := by
  intro u
  have hB : (backwardEulerCentredOp a lam) u = u + (lam * a / 2) • centredDiffCLM u := rfl
  rw [ContinuousLinearMap.coe_coe, hB, inner_add_left, real_inner_smul_left,
    inner_centredDiffCLM_self]
  simp

/-- The **solution operator of the implicit backward Euler/centred scheme**: the inverse of
$B = 1 + (\lambda a / 2) D_0$ on $\ell^2(\mathbb{Z})$. The inverse exists and is a contraction
because $B$ is coercive with constant $1$. This is in §13.8.2 of [quarteroni2000numerical].

The inverse comes from the Lax–Milgram theorem
`ContinuousLinearMap.exists_equiv_of_isCoerciveWith`. -/
noncomputable def backwardEulerCentred (a lam : ℝ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  ((ContinuousLinearMap.exists_equiv_of_isCoerciveWith one_pos
    (backwardEulerCentredOp_isCoerciveWith a lam)).choose.symm :
      lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2)

/-- The solution operator solves the implicit scheme: $w = B^{-1} u$ satisfies
$$w_j + \frac{\lambda a}{2} (w_{j+1} - w_{j-1}) = u_j,$$
that is, $u^{n+1} = B^{-1} u^n$ solves (13.43) of [quarteroni2000numerical]. -/
theorem backwardEulerCentred_spec (a lam : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) :
    backwardEulerCentredOp a lam (backwardEulerCentred a lam u) = u := by
  have hspec := (ContinuousLinearMap.exists_equiv_of_isCoerciveWith one_pos
    (backwardEulerCentredOp_isCoerciveWith a lam)).choose_spec
  have key : ∀ x, backwardEulerCentredOp a lam x
      = (ContinuousLinearMap.exists_equiv_of_isCoerciveWith one_pos
        (backwardEulerCentredOp_isCoerciveWith a lam)).choose x :=
    fun x => (congrFun (congrArg DFunLike.coe hspec.1) x).symm
  rw [key]
  exact ContinuousLinearEquiv.apply_symm_apply _ u

/-- The **implicit backward Euler/centred scheme is unconditionally stable** in the discrete
$\ell^2$ norm, with constant $1$: for every $a$ and every $\lambda$, $\|B^{-1} u\| \le \|u\|$
for $u \in \ell^2(\mathbb{Z})$, so $\|u^{n+1}\| \le \|u^n\|$. This is in §13.8.2 and Exercise
13.7 of [quarteroni2000numerical]. -/
theorem norm_backwardEulerCentred_apply_le (a lam : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) :
    ‖backwardEulerCentred a lam u‖ ≤ ‖u‖ := by
  have hspec := (ContinuousLinearMap.exists_equiv_of_isCoerciveWith one_pos
    (backwardEulerCentredOp_isCoerciveWith a lam)).choose_spec
  have hn : ‖backwardEulerCentred a lam‖ ≤ 1 := hspec.2.trans (le_of_eq one_div_one)
  have h3 := (backwardEulerCentred a lam).le_of_opNorm_le hn u
  rwa [one_mul] at h3

end Implicit

/-! ### The unconditional instability of the forward Euler/centred scheme -/

section Instability

/-- A periodic grid of $m + 8$ points is nonempty. -/
instance neZero_add_eight (m : ℕ) : NeZero (m + 8) := ⟨by omega⟩

/-- The **forward Euler/centred family** on the periodic grids of $N = m + 8$ points of $[0, 2\pi]$:
for each $m$, the matrix of the forward Euler/centred scheme on the periodic grid, as a
real-linear operator on $\mathbb{C}^{N}$ with the Euclidean norm. The intended steps are
$\Delta x = 2\pi/N$ and $\Delta t = \lambda \Delta x$. -/
noncomputable def forwardEulerCentredFamily (a lam : ℝ) (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + 8)) →L[ℝ] EuclideanSpace ℂ (Fin (m + 8)) :=
  (toEuclideanCLM (𝕜 := ℂ)
    (periodicScheme (Stencil.toPeriodic (m + 8) (forwardEulerCentred a lam)))).restrictScalars ℝ

/-- On a grid of $N = m + 8$ points, the phase $\varphi_k$ with $k = \lfloor N/4 \rfloor$ lies in
$(\pi/4, \pi/2]$, so $\sin^2 \varphi_k > 1/2$. -/
private theorem half_lt_sin_sq_gridPhase (m : ℕ) :
    1 / 2 < Real.sin (gridPhase (m + 8) ⟨(m + 8) / 4, by omega⟩) ^ 2 := by
  set N : ℕ := m + 8 with hN
  set q : ℕ := N / 4 with hq
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have h4q : 4 * q ≤ N := by omega
  have hq4 : N < 4 * q + 4 := by omega
  have hN8 : 8 ≤ N := by omega
  have h4qR : 4 * (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast h4q
  have hq4R : (N : ℝ) < 4 * (q : ℝ) + 4 := by exact_mod_cast hq4
  have hN8R : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hval : gridPhase N ⟨q, by omega⟩ = 2 * π * q / N := rfl
  have hpi := Real.pi_pos
  have hupper : gridPhase N ⟨q, by omega⟩ ≤ π / 2 := by
    rw [hval, div_le_iff₀ hNpos]
    nlinarith
  have hlower : π / 4 < gridPhase N ⟨q, by omega⟩ := by
    rw [hval, lt_div_iff₀ hNpos]
    nlinarith
  have hsin : Real.sin (π / 4) < Real.sin (gridPhase N ⟨q, by omega⟩) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hupper hlower
  rw [Real.sin_pi_div_four] at hsin
  have h2 : (0 : ℝ) < √2 / 2 := by positivity
  have hsq : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  nlinarith [hsin, h2, hsq]

/-- The **forward Euler/centred scheme is unconditionally unstable**. Let $a \neq 0$ and
$\lambda > 0$. The family of forward Euler/centred schemes on the periodic grids of $N = m + 8$
points, with $\Delta x = 2\pi/N$ and $\Delta t = \lambda \Delta x$
(`FiniteDifference.Hyperbolic.forwardEulerCentredFamily`), is not stable in the sense of (13.46)
of [quarteroni2000numerical] (`FiniteDifference.IsStableFamily`). This is in §13.8.4 of
[quarteroni2000numerical]. So the CFL condition is not sufficient for stability.

The mode $k$ nearest to $\varphi = \pi/2$ has $|\gamma_k| \ge \sqrt{1 + (\lambda a)^2/2} > 1$ on
every grid, so $\|Q^n\|_2$ grows past every bound as the mesh is refined at fixed $\lambda$. -/
theorem forwardEulerCentred_not_isStableFamily {a lam : ℝ} (ha : a ≠ 0) (hlam : 0 < lam) :
    ¬FiniteDifference.IsStableFamily (fun m : ℕ => lam * (2 * π / (m + 8)))
      (fun m : ℕ => 2 * π / (m + 8)) (forwardEulerCentredFamily a lam) := by
  intro hstab
  obtain ⟨C, δ₀, hδ₀, hC⟩ := hstab 1 one_pos
  have hpi := Real.pi_pos
  have hla : 0 < (lam * a) ^ 2 := by positivity
  set ρ : ℝ := √(1 + (lam * a) ^ 2 / 2) with hρdef
  have hρ1 : 1 < ρ := by
    rw [hρdef]
    exact (Real.lt_sqrt zero_le_one).2 (by nlinarith)
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt C hρ1
  obtain ⟨m, hm⟩ := exists_nat_gt
    (max (2 * π * lam * (n₀ + 1)) (2 * π / δ₀ * (1 + lam)))
  set N : ℕ := m + 8 with hNdef
  have hNR : max (2 * π * lam * (n₀ + 1)) (2 * π / δ₀ * (1 + lam)) < (N : ℝ) := by
    rw [hNdef]
    push_cast
    linarith
  have h1 : 2 * π * lam * (n₀ + 1) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hNR
  have h2 : 2 * π / δ₀ * (1 + lam) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hNR
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  -- the two step sizes are below `δ₀`
  have hΔxpos : (0 : ℝ) < 2 * π / N := by positivity
  have hΔtpos : (0 : ℝ) < lam * (2 * π / N) := by positivity
  have hδ : 2 * π * (1 + lam) < δ₀ * N := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hδ₀] at h2
    linarith
  have hΔxle : 2 * π / N ≤ δ₀ := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hΔtle : lam * (2 * π / N) ≤ δ₀ := by
    rw [mul_div_assoc', div_le_iff₀ hNpos]
    nlinarith
  -- the number of steps
  set n : ℕ := ⌊1 / (lam * (2 * π / N))⌋₊ with hndef
  have hxpos : (0 : ℝ) < 1 / (lam * (2 * π / N)) := by positivity
  have hnle : (n : ℝ) * (lam * (2 * π / N)) ≤ 1 := by
    have := Nat.floor_le hxpos.le
    rw [← hndef] at this
    calc (n : ℝ) * (lam * (2 * π / N)) ≤ (1 / (lam * (2 * π / N))) * (lam * (2 * π / N)) := by
          exact mul_le_mul_of_nonneg_right this hΔtpos.le
      _ = 1 := by field_simp
  have hnbig : n₀ ≤ n := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt : (n : ℝ) + 1 ≤ n₀ := by exact_mod_cast hcon
    have hfl : 1 / (lam * (2 * π / N)) < (n : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (1 / (lam * (2 * π / N)))
      rw [← hndef] at this
      exact this
    have hinv : (N : ℝ) / (2 * π * lam) = 1 / (lam * (2 * π / N)) := by field_simp
    rw [← hinv] at hfl
    rw [div_lt_iff₀ (by positivity)] at hfl
    nlinarith
  -- the mode nearest to `π/2`
  have hsin := half_lt_sin_sq_gridPhase m
  have hgam : ρ ≤ ‖FiniteDifference.amplificationFactor
      (Stencil.toPeriodic N (forwardEulerCentred a lam)) ⟨N / 4, by omega⟩‖ := by
    have hsq := norm_amplificationFactor_forwardEulerCentred_sq (N := N) a lam ⟨N / 4, by omega⟩
    have hge : ρ ^ 2 ≤ ‖FiniteDifference.amplificationFactor
        (Stencil.toPeriodic N (forwardEulerCentred a lam)) ⟨N / 4, by omega⟩‖ ^ 2 := by
      rw [hsq, hρdef, Real.sq_sqrt (by positivity)]
      nlinarith
    nlinarith [norm_nonneg (FiniteDifference.amplificationFactor
      (Stencil.toPeriodic N (forwardEulerCentred a lam)) (⟨N / 4, by omega⟩ : Fin N))]
  have hlow : ρ ^ n ≤ ‖forwardEulerCentredFamily a lam m ^ n‖ := by
    rw [forwardEulerCentredFamily, ← ContinuousLinearMap.restrictScalars_pow,
      ContinuousLinearMap.norm_restrictScalars, ← map_pow]
    exact le_trans (pow_le_pow_left₀ hρ0 hgam n)
      (norm_amplificationFactor_pow_le _ ⟨N / 4, by omega⟩ n)
  have hcast : ((N : ℕ) : ℝ) = (m : ℝ) + 8 := by rw [hNdef]; push_cast; ring
  have hup := hC m (by simpa only [← hcast] using hΔtpos) (by simpa only [← hcast] using hΔtle)
    (by simpa only [← hcast] using hΔxpos) (by simpa only [← hcast] using hΔxle) n
    (by simpa only [← hcast] using hnle)
  have hmono : ρ ^ n₀ ≤ ρ ^ n := pow_le_pow_right₀ hρ1.le hnbig
  linarith

end Instability

/-!
### Dissipation and dispersion (§13.9)

The exact solution multiplies the $k$-th harmonic by $g_k = e^{-i a k \Delta t}$ per time step, a
number of modulus $1$, and the scheme multiplies it by its amplification factor $\gamma_k$. The
ratio of the moduli is the dissipation error, and the ratio of the phase speeds is the dispersion
error.
-/

/-- The **exact amplification factor** of the $k$-th harmonic: the exact solution of
$u_t + a u_x = 0$ multiplies $e^{i k x}$ by $g_k = e^{-i a k \Delta t}$ per time step. This is
(13.54) of [quarteroni2000numerical]. -/
noncomputable def exactAmplification (a Δt : ℝ) (k : ℤ) : ℂ := Complex.exp (-(I * a * k * Δt))

/-- The powers of the exact amplification factor are $g_k^n = e^{-i a k (n \Delta t)}$. -/
theorem exactAmplification_pow (a Δt : ℝ) (k : ℤ) (n : ℕ) :
    exactAmplification a Δt k ^ n = Complex.exp (-(I * a * k * ((n : ℝ) * Δt))) := by
  rw [exactAmplification, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The **phase angle of the $k$-th harmonic** on a grid of spacing $\Delta x$ is
$\varphi_k = k \Delta x$. This is in §13.9 of [quarteroni2000numerical]. -/
noncomputable def phaseAngle (k : ℤ) (Δx : ℝ) : ℝ := k * Δx

/-- Let $\Delta x \neq 0$ and $\lambda = \Delta t / \Delta x$. Then the exact amplification factor
is $g_k = e^{-i a \lambda \varphi_k}$ with $\varphi_k = k \Delta x$. This is (13.55) of
[quarteroni2000numerical]. -/
theorem exactAmplification_eq_phaseAngle {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx)
    (a : ℝ) (k : ℤ) :
    exactAmplification a Δt k = Complex.exp (-(I * ((a * lam * phaseAngle k Δx : ℝ) : ℂ))) := by
  subst hlam
  have hx : (a * (Δt / Δx) * ((k : ℝ) * Δx) : ℝ) = a * (k : ℝ) * Δt := by
    field_simp
    try ring
  rw [exactAmplification, phaseAngle, hx]
  congr 1
  push_cast
  ring

/-- The **exact solution neither amplifies nor damps any harmonic**: $|g_k| = 1$. This is in §13.9
of [quarteroni2000numerical]. -/
theorem norm_exactAmplification (a Δt : ℝ) (k : ℤ) : ‖exactAmplification a Δt k‖ = 1 := by
  rw [exactAmplification, Complex.norm_exp]
  simp

/-- The **amplification (dissipation) error** of a numerical amplification factor $\gamma_k$ is
$\varepsilon_a = |\gamma_k| / |g_k| = |\gamma_k|$. This is in §13.9 of
[quarteroni2000numerical]. -/
noncomputable def amplificationError (γ : ℂ) : ℝ := ‖γ‖

/-- The **dispersion error** of a numerical amplification factor
$\gamma_k = |\gamma_k| e^{-i \omega \Delta t}$ is the ratio $\omega / (k a)$ of the numerical
phase speed to the exact one,
$$\varepsilon_d = \frac{-\arg \gamma_k}{a \lambda \varphi_k}.$$
This is in §13.9 of [quarteroni2000numerical].

The argument is the principal argument in $(-\pi, \pi]$. For $a \lambda \varphi_k = 0$ the
quotient is $0$. -/
noncomputable def dispersionError (a lam phi : ℝ) (γ : ℂ) : ℝ :=
  -Complex.arg γ / (a * lam * phi)

/-- The exact amplification factor has the dissipation error $1$: the exact solution has no
dissipation. -/
theorem amplificationError_exactAmplification (a Δt : ℝ) (k : ℤ) :
    amplificationError (exactAmplification a Δt k) = 1 := norm_exactAmplification a Δt k

/-- Let $\Delta x \neq 0$, $\lambda = \Delta t / \Delta x$ and $0 < |a \lambda \varphi_k| < \pi$, so
that the phase is not ambiguous. Then the exact amplification factor has the dispersion error
$1$: the exact solution has no dispersion. This is in §13.9 of [quarteroni2000numerical]. -/
theorem dispersionError_exactAmplification {a lam Δt Δx : ℝ} {k : ℤ} (hΔx : Δx ≠ 0)
    (hlam : lam = Δt / Δx) (h0 : a * lam * phaseAngle k Δx ≠ 0)
    (hπ : |a * lam * phaseAngle k Δx| < π) :
    dispersionError a lam (phaseAngle k Δx) (exactAmplification a Δt k) = 1 := by
  rw [dispersionError, exactAmplification_eq_phaseAngle hΔx hlam]
  have harg : Complex.arg (Complex.exp (-(I * ((a * lam * phaseAngle k Δx : ℝ) : ℂ))))
      = -(a * lam * phaseAngle k Δx) := by
    rw [show -(I * ((a * lam * phaseAngle k Δx : ℝ) : ℂ))
        = ((-(a * lam * phaseAngle k Δx) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    refine Complex.arg_cos_add_sin_mul_I ?_
    rw [abs_lt] at hπ
    rw [Set.mem_Ioc]
    exact ⟨by linarith [hπ.2], by linarith [hπ.1]⟩
  rw [harg, neg_neg, div_self h0]

/-! ### Equivalent (modified) equations (§13.9.1) -/

/-- The **residual of a stencil** $c$ on a function $v$ of two variables, at $(x, t)$:
$$\frac{1}{\Delta t} \Bigl( v(x, t + \Delta t) - \sum_s c_s v(x - s \Delta x, t) \Bigr),$$
the amount by which $v$ fails to satisfy the difference equation, divided by $\Delta t$. On the
travelling wave $u_0(x - a t)$ it is the local truncation error
(`FiniteDifference.Hyperbolic.residual_comp_sub`). This is in §13.9.1 of
[quarteroni2000numerical].

At $\Delta t = 0$ the quotient is $0$. -/
noncomputable def residual (c : Stencil) (Δt Δx : ℝ) (v : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  (v x (t + Δt) - Stencil.apply c (fun i : ℤ => v (x + i * Δx) t) 0) / Δt

/-- The residual of the three-point stencil with weights $(c_-, c_0, c_+)$ is
$$\frac{1}{\Delta t} \bigl( v(x, t + \Delta t) - c_- v(x - \Delta x, t) - c_0 v(x, t) - c_+
  v(x + \Delta x, t) \bigr).$$
-/
theorem residual_threePoint (cm c0 cp Δt Δx : ℝ) (v : ℝ → ℝ → ℝ) (x t : ℝ) :
    residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
      = (v x (t + Δt) - (cm * v (x - Δx) t + c0 * v x t + cp * v (x + Δx) t)) / Δt := by
  rw [residual, Stencil.threePoint_apply]
  simp only [smul_eq_mul]
  push_cast
  ring_nf

/-- The **residual on the exact travelling wave is the local truncation error**: the residual of $c$
on $(x, t) \mapsto u_0(x - a t)$ at $(x, t)$ is the truncation error
(`FiniteDifference.Hyperbolic.truncationError`) at $\xi = x - a t$. This is in §13.8.1 and
§13.9.1 of [quarteroni2000numerical]. -/
theorem residual_comp_sub (c : Stencil) (a Δt Δx : ℝ) (u₀ : ℝ → ℝ) (x t : ℝ) :
    residual c Δt Δx (fun x t => u₀ (x - a * t)) x t
      = truncationError c a Δt Δx u₀ (x - a * t) := by
  rw [residual, truncationError]
  congr 2
  · congr 1
    ring
  · rw [Stencil.apply_apply, Stencil.apply_apply]
    exact Finset.sum_congr rfl fun s _ => by congr 2; ring

/-- A **classical solution of the equivalent (modified) equation**
$$v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$$
is a function $v$ of two variables that has partial derivatives $v_x$, $v_t$, $v_{xx}$,
$v_{xt}$, $v_{xxx}$, $v_{xxt}$ on the whole plane and satisfies the equation at every point. The
term $\mu v_{xx}$ is the dissipative term and $\nu v_{xxx}$ is the dispersive term. This is
(13.56) of [quarteroni2000numerical].

The partial derivatives exist in the sense of `Transport.HasPartialsOn` on $\mathbb{R}^2$: $v$
has the partial derivatives $(v_x, v_t)$, $v_x$ has $(v_{xx}, v_{xt})$, and $v_{xx}$ has
$(v_{xxx}, v_{xxt})$. -/
def IsModifiedSolution (a mu nu : ℝ) (v : ℝ → ℝ → ℝ) : Prop :=
  ∃ vx vt vxx vxt vxxx vxxt : ℝ → ℝ → ℝ,
    Transport.HasPartialsOn Set.univ v vx vt ∧ Transport.HasPartialsOn Set.univ vx vxx vxt ∧
      Transport.HasPartialsOn Set.univ vxx vxxx vxxt ∧
      ∀ x t : ℝ, vt x t + a * vx x t = mu * vxx x t + nu * vxxx x t

/-!
### Taylor expansion along the coordinate lines

In this section $D_{i,j} = \partial_x^i \partial_t^j v$ is a family of iterated partial derivatives
of $v$ (`HasPartialDerivs`), and each bound on a derivative holds on the whole plane.
-/

section PartialTaylor

variable {v : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {M : ℝ} {i j : ℕ}

/-- **First-order Taylor expansion in space.** If $|D_{i+2,j}| \le M$, then for all $x$, $t$, $h$,
$$|D_{i,j}(x + h, t) - D_{i,j}(x, t) - h D_{i+1,j}(x, t)| \le M h^2 / 2.$$
-/
theorem abs_taylor_fst_one (hD : HasPartialDerivs v D) (hM : ∀ y s, |D (i + 2) j y s| ≤ M)
    (x t h : ℝ) : |D i j (x + h) t - D i j x t - h * D (i + 1) j x t| ≤ M * h ^ 2 / 2 := by
  have hc : ContDiff ℝ 2 fun y => D i j y t := by exact_mod_cast hD.contDiff_fst 2 i j t
  have hb : ∀ y, |iteratedDeriv 2 (fun y => D i j y t) y| ≤ M := by
    rw [hD.iteratedDeriv_fst]
    exact fun y => hM y t
  simpa [hD.deriv_fst] using abs_taylor_one hc hb x h

/-- **Second-order Taylor expansion in space.** If $|D_{i+3,j}| \le M$, then for all $x$, $t$, $h$,
$$\Bigl|D_{i,j}(x + h, t) - D_{i,j}(x, t) - h D_{i+1,j}(x, t) - \frac{h^2}{2} D_{i+2,j}(x,
  t)\Bigr| \le \frac{M |h|^3}{6}.$$
-/
theorem abs_taylor_fst_two (hD : HasPartialDerivs v D) (hM : ∀ y s, |D (i + 3) j y s| ≤ M)
    (x t h : ℝ) :
    |D i j (x + h) t - D i j x t - h * D (i + 1) j x t - h ^ 2 / 2 * D (i + 2) j x t|
      ≤ M * |h| ^ 3 / 6 := by
  have hc : ContDiff ℝ 3 fun y => D i j y t := by exact_mod_cast hD.contDiff_fst 3 i j t
  have hb : ∀ y, |iteratedDeriv 3 (fun y => D i j y t) y| ≤ M := by
    rw [hD.iteratedDeriv_fst]
    exact fun y => hM y t
  simpa [hD.deriv_fst, hD.iteratedDeriv_fst] using abs_taylor_two hc hb x h

/-- **Third-order Taylor expansion in space.** If $|D_{i+4,j}| \le M$, then for all $x$, $t$, $h$,
$$\Bigl|D_{i,j}(x + h, t) - D_{i,j}(x, t) - h D_{i+1,j}(x, t) - \frac{h^2}{2} D_{i+2,j}(x, t) -
  \frac{h^3}{6} D_{i+3,j}(x, t)\Bigr| \le \frac{M h^4}{24}.$$
-/
theorem abs_taylor_fst_three (hD : HasPartialDerivs v D) (hM : ∀ y s, |D (i + 4) j y s| ≤ M)
    (x t h : ℝ) :
    |D i j (x + h) t - D i j x t - h * D (i + 1) j x t - h ^ 2 / 2 * D (i + 2) j x t
        - h ^ 3 / 6 * D (i + 3) j x t| ≤ M * h ^ 4 / 24 := by
  have hc : ContDiff ℝ 4 fun y => D i j y t := by exact_mod_cast hD.contDiff_fst 4 i j t
  have hb : ∀ y, |iteratedDeriv 4 (fun y => D i j y t) y| ≤ M := by
    rw [hD.iteratedDeriv_fst]
    exact fun y => hM y t
  simpa [hD.deriv_fst, hD.iteratedDeriv_fst] using abs_taylor_three hc hb x h

/-- **First-order Taylor expansion in time.** If $|D_{i,j+2}| \le M$, then for all $x$, $t$, $h$,
$$|D_{i,j}(x, t + h) - D_{i,j}(x, t) - h D_{i,j+1}(x, t)| \le M h^2 / 2.$$
-/
theorem abs_taylor_snd_one (hD : HasPartialDerivs v D) (hM : ∀ y s, |D i (j + 2) y s| ≤ M)
    (x t h : ℝ) : |D i j x (t + h) - D i j x t - h * D i (j + 1) x t| ≤ M * h ^ 2 / 2 :=
  abs_taylor_fst_one hD.swap (fun y s => hM s y) t x h

/-- **Second-order Taylor expansion in time.** If $|D_{i,j+3}| \le M$, then for all $x$, $t$, $h$,
$$\Bigl|D_{i,j}(x, t + h) - D_{i,j}(x, t) - h D_{i,j+1}(x, t) - \frac{h^2}{2} D_{i,j+2}(x,
  t)\Bigr| \le \frac{M |h|^3}{6}.$$
-/
theorem abs_taylor_snd_two (hD : HasPartialDerivs v D) (hM : ∀ y s, |D i (j + 3) y s| ≤ M)
    (x t h : ℝ) :
    |D i j x (t + h) - D i j x t - h * D i (j + 1) x t - h ^ 2 / 2 * D i (j + 2) x t|
      ≤ M * |h| ^ 3 / 6 :=
  abs_taylor_fst_two hD.swap (fun y s => hM s y) t x h

/-- **Third-order Taylor expansion in time.** If $|D_{i,j+4}| \le M$, then for all $x$, $t$, $h$,
$$\Bigl|D_{i,j}(x, t + h) - D_{i,j}(x, t) - h D_{i,j+1}(x, t) - \frac{h^2}{2} D_{i,j+2}(x, t) -
  \frac{h^3}{6} D_{i,j+3}(x, t)\Bigr| \le \frac{M h^4}{24}.$$
-/
theorem abs_taylor_snd_three (hD : HasPartialDerivs v D) (hM : ∀ y s, |D i (j + 4) y s| ≤ M)
    (x t h : ℝ) :
    |D i j x (t + h) - D i j x t - h * D i (j + 1) x t - h ^ 2 / 2 * D i (j + 2) x t
        - h ^ 3 / 6 * D i (j + 3) x t| ≤ M * h ^ 4 / 24 :=
  abs_taylor_fst_three hD.swap (fun y s => hM s y) t x h

/-- The **second central difference in the first variable approximates the second partial
derivative**. If $|D_{i+4,j}| \le M$ and $h > 0$, then for all $x$, $t$,
$$\Bigl| \frac{D_{i,j}(x + h, t) - 2 D_{i,j}(x, t) + D_{i,j}(x - h, t)}{h^2} - D_{i+2,j}(x, t)
  \Bigr| \le \frac{M h^2}{12}.$$

The proof applies `FiniteDifference.abs_secondDiff_sub_le` to the functions
$y \mapsto D_{i+m,j}(y, t)$ on $[x - h, x + h]$. -/
theorem abs_secondDiff_fst_sub_le (hD : HasPartialDerivs v D)
    (hM : ∀ y s, |D (i + 4) j y s| ≤ M) {h : ℝ} (hh : 0 < h) (x t : ℝ) :
    |(D i j (x + h) t - 2 * D i j x t + D i j (x - h) t) / h ^ 2 - D (i + 2) j x t|
      ≤ M * h ^ 2 / 12 := by
  have key := FiniteDifference.abs_secondDiff_sub_le (y := fun m y => D (i + m) j y t)
    (a := x - h) (b := x + h)
    (fun m _ s _ => (hD.hasPartialDerivFst (i + m) j s t).hasDerivWithinAt) (fun s _ => hM s t)
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ hh.le
  simp only [add_zero] at key
  have hh2 : (0 : ℝ) < h ^ 2 := by positivity
  rw [show (D i j (x + h) t - 2 * D i j x t + D i j (x - h) t) / h ^ 2 - D (i + 2) j x t
      = (D i j (x + h) t - 2 * D i j x t + D i j (x - h) t - h ^ 2 * D (i + 2) j x t) / h ^ 2 by
    field_simp, abs_div, abs_of_pos hh2, div_le_iff₀ hh2]
  linarith

/-- The **second central difference in the second variable approximates the second partial
derivative**. If $|D_{i,j+4}| \le M$ and $h > 0$, then for all $x$, $t$,
$$\Bigl| \frac{D_{i,j}(x, t + h) - 2 D_{i,j}(x, t) + D_{i,j}(x, t - h)}{h^2} - D_{i,j+2}(x, t)
  \Bigr| \le \frac{M h^2}{12}.$$
-/
theorem abs_secondDiff_snd_sub_le (hD : HasPartialDerivs v D)
    (hM : ∀ y s, |D i (j + 4) y s| ≤ M) {h : ℝ} (hh : 0 < h) (x t : ℝ) :
    |(D i j x (t + h) - 2 * D i j x t + D i j x (t - h)) / h ^ 2 - D i (j + 2) x t|
      ≤ M * h ^ 2 / 12 :=
  abs_secondDiff_fst_sub_le hD.swap (fun y s => hM s y) hh t x

/-! ### The residual of a three-point scheme, expanded -/

/-- The **residual of a three-point scheme expanded to third order**. Let $v$ have the iterated
partial derivatives $D_{i,j} = \partial_x^i \partial_t^j v$, with $|D_{i,j}| \le M$ for
$i + j = 4$, let $c_-, c_0, c_+ \in \mathbb{R}$ and $\Delta t > 0$. Then the residual
$$\tau = \frac{1}{\Delta t} \bigl[v(x, t + \Delta t) - (c_- v(x - \Delta x, t) + c_0 v(x, t) +
  c_+ v(x + \Delta x, t))\bigr]$$
of the three-point stencil satisfies
$$\Bigl| \tau - \Bigl( v_t + \frac{\Delta t}{2} v_{tt} + \frac{\Delta t^2}{6} v_{ttt} -
  \frac{1}{\Delta t} \Bigl[ (c_- + c_0 + c_+ - 1) v + \Delta x (c_+ - c_-) v_x + \frac{\Delta
  x^2}{2} (c_+ + c_-) v_{xx} + \frac{\Delta x^3}{6} (c_+ - c_-) v_{xxx} \Bigr] \Bigr) \Bigr| \le
  M \Bigl( \frac{\Delta t^3}{24} + \frac{(|c_-| + |c_+|) \Delta x^4}{24 \Delta t} \Bigr),$$
with all derivatives at $(x, t)$. This is in §13.9.1 of [quarteroni2000numerical].

The proof is Taylor's formula in $t$ along the vertical line and in $x$ along the horizontal
line through $(x, t)$. Every computation of an equivalent equation in §13.9.1 is algebra on this
estimate. -/
theorem residual_threePoint_expansion (hD : HasPartialDerivs v D)
    (hM : ∀ i j, i + j = 4 → ∀ y s, |D i j y s| ≤ M) (cm c0 cp : ℝ) {Δt Δx : ℝ} (hΔt : 0 < Δt)
    (x t : ℝ) :
    |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
          - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
            + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)|
      ≤ M * (Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) := by
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hv : D 0 0 = v := hD.eq_zero_zero
  have hRt : |v x (t + Δt) - v x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t
      - Δt ^ 3 / 6 * D 0 3 x t| ≤ M * Δt ^ 4 / 24 := by
    have h := abs_taylor_snd_three hD (hM 0 4 rfl) x t Δt
    rwa [hv] at h
  have hRp : |v (x + Δx) t - v x t - Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
      - Δx ^ 3 / 6 * D 3 0 x t| ≤ M * Δx ^ 4 / 24 := by
    have h := abs_taylor_fst_three hD (hM 4 0 rfl) x t Δx
    rwa [hv] at h
  have hRm : |v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
      + Δx ^ 3 / 6 * D 3 0 x t| ≤ M * Δx ^ 4 / 24 := by
    have h := abs_taylor_fst_three hD (hM 4 0 rfl) x t (-Δx)
    rw [hv, show x + -Δx = x - Δx from by ring,
      show v (x - Δx) t - v x t - -Δx * D 1 0 x t - (-Δx) ^ 2 / 2 * D 2 0 x t
          - (-Δx) ^ 3 / 6 * D 3 0 x t
        = v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
          + Δx ^ 3 / 6 * D 3 0 x t from by ring,
      show M * (-Δx) ^ 4 / 24 = M * Δx ^ 4 / 24 from by ring] at h
    exact h
  have hid : (residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
          - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
            + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)) * Δt
      = (v x (t + Δt) - v x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t
          - Δt ^ 3 / 6 * D 0 3 x t)
        - cm * (v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
            + Δx ^ 3 / 6 * D 3 0 x t)
        - cp * (v (x + Δx) t - v x t - Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
            - Δx ^ 3 / 6 * D 3 0 x t) := by
    rw [residual_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
          - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
            + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t
            + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)| * Δt
      = |(residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
            - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
              + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t
              + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)) * Δt| := by
        rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M * Δt ^ 4 / 24 + |cm| * (M * Δx ^ 4 / 24) + |cp| * (M * Δx ^ 4 / 24) := by
        rw [hid]
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
          (add_le_add hRt ?_)) ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hRm (abs_nonneg cm)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hRp (abs_nonneg cp)
    _ = M * (Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) * Δt := by
        field_simp
        ring

/-! ### The equivalent equation of the upwind scheme -/

/-- The **first Taylor expansion of the upwind residual**. Let $a > 0$, $\Delta t, \Delta x > 0$,
$\lambda = \Delta t / \Delta x$, and let $v$ have the iterated partial derivatives $D_{i,j}$
with $|D_{i,j}| \le M$ for $i + j = 2$. Then the residual $\tau$ of the upwind scheme (13.41) on
$v$ satisfies
$$|\tau - (v_t + a v_x)| \le \frac{\Delta t}{2} M + \frac{a \Delta x}{2} M,$$
with the derivatives at $(x, t)$. This is the expansion (13.57) of [quarteroni2000numerical]. -/
theorem abs_residual_upwind_sub_le (hD : HasPartialDerivs v D) {a Δt Δx lam : ℝ} (ha : 0 < a)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hM₂ : ∀ i j, i + j = 2 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |residual (upwind a lam) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)|
      ≤ Δt / 2 * M + a * Δx / 2 * M := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hv : D 0 0 = v := hD.eq_zero_zero
  have hRt : |v x (t + Δt) - v x t - Δt * D 0 1 x t| ≤ M * Δt ^ 2 / 2 := by
    have h := abs_taylor_snd_one hD (hM₂ 0 2 rfl) x t Δt
    rwa [hv] at h
  have hRm : |v (x - Δx) t - v x t + Δx * D 1 0 x t| ≤ M * Δx ^ 2 / 2 := by
    have h := abs_taylor_fst_one hD (hM₂ 2 0 rfl) x t (-Δx)
    rw [hv, show x + -Δx = x - Δx from by ring,
      show v (x - Δx) t - v x t - -Δx * D 1 0 x t
        = v (x - Δx) t - v x t + Δx * D 1 0 x t from by ring,
      show M * (-Δx) ^ 2 / 2 = M * Δx ^ 2 / 2 from by ring] at h
    exact h
  have hid : (residual (upwind a (Δt / Δx)) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)) * Δt
      = (v x (t + Δt) - v x t - Δt * D 0 1 x t)
        - Δt / Δx * a * (v (x - Δx) t - v x t + Δx * D 1 0 x t) := by
    rw [upwind_eq_of_pos ha, residual_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |residual (upwind a (Δt / Δx)) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)| * Δt
      = |(residual (upwind a (Δt / Δx)) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)) * Δt| := by
        rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M * Δt ^ 2 / 2 + Δt / Δx * a * (M * Δx ^ 2 / 2) := by
        rw [hid]
        refine (abs_sub _ _).trans (add_le_add hRt ?_)
        rw [abs_mul, show |Δt / Δx * a| = Δt / Δx * a by
          rw [abs_of_nonneg (by positivity)]]
        exact mul_le_mul_of_nonneg_left hRm (by positivity)
    _ = (Δt / 2 * M + a * Δx / 2 * M) * Δt := by field_simp

/-- The **second Taylor expansion of the upwind residual**. Let $a > 0$, $\Delta t, \Delta x > 0$,
$\lambda = \Delta t / \Delta x$, and let $v$ have the iterated partial derivatives $D_{i,j}$
with $|D_{i,j}| \le M$ for $i + j = 3$. Then the residual $\tau$ of the upwind scheme on $v$
satisfies
$$\Bigl|\tau - \Bigl(v_t + \frac{\Delta t}{2} v_{tt} + a v_x - \frac{a \Delta x}{2}
  v_{xx}\Bigr)\Bigr| \le \frac{\Delta t^2}{6} M + \frac{a \Delta x^2}{6} M,$$
with the derivatives at $(x, t)$. This is the expansion (13.58) of [quarteroni2000numerical].

The source prints (13.58) with $a (v_x + (\Delta x/2) v_{xx})$. The backward difference
$(v(x, t) - v(x - \Delta x, t))/\Delta x$ is $v_x - (\Delta x/2) v_{xx} + O(\Delta x^2)$, so the
sign in the source is an error. The minus sign is the one that gives
$\mu = a \Delta x/2 - a^2 \Delta t/2$ in (13.59). -/
theorem abs_residual_upwind_sub_le_two (hD : HasPartialDerivs v D) {a Δt Δx lam : ℝ} (ha : 0 < a)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hM₃ : ∀ i j, i + j = 3 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |residual (upwind a lam) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)|
      ≤ Δt ^ 2 / 6 * M + a * Δx ^ 2 / 6 * M := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hv : D 0 0 = v := hD.eq_zero_zero
  have hRt : |v x (t + Δt) - v x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t|
      ≤ M * Δt ^ 3 / 6 := by
    have h := abs_taylor_snd_two hD (hM₃ 0 3 rfl) x t Δt
    rw [hv, abs_of_pos hΔt] at h
    exact h
  have hRm : |v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t|
      ≤ M * Δx ^ 3 / 6 := by
    have h := abs_taylor_fst_two hD (hM₃ 3 0 rfl) x t (-Δx)
    rw [hv, show x + -Δx = x - Δx from by ring,
      show v (x - Δx) t - v x t - -Δx * D 1 0 x t - (-Δx) ^ 2 / 2 * D 2 0 x t
        = v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t from by ring,
      abs_neg, abs_of_pos hΔx] at h
    exact h
  have hid : (residual (upwind a (Δt / Δx)) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)) * Δt
      = (v x (t + Δt) - v x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t)
        - Δt / Δx * a * (v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t) := by
    rw [upwind_eq_of_pos ha, residual_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |residual (upwind a (Δt / Δx)) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)| * Δt
      = |(residual (upwind a (Δt / Δx)) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t
            - a * Δx / 2 * D 2 0 x t)) * Δt| := by rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M * Δt ^ 3 / 6 + Δt / Δx * a * (M * Δx ^ 3 / 6) := by
        rw [hid]
        refine (abs_sub _ _).trans (add_le_add hRt ?_)
        rw [abs_mul, show |Δt / Δx * a| = Δt / Δx * a by
          rw [abs_of_nonneg (by positivity)]]
        exact mul_le_mul_of_nonneg_left hRm (by positivity)
    _ = (Δt ^ 2 / 6 * M + a * Δx ^ 2 / 6 * M) * Δt := by field_simp

/-- A solution $v$ of the equivalent equation $v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$
(`FiniteDifference.Hyperbolic.IsModifiedSolution`) satisfies the equation in terms of any family
$D_{i,j}$ of its iterated partial derivatives:
$$D_{0,1} + a D_{1,0} = \mu D_{2,0} + \nu D_{3,0}$$
at every point.

The definition of the equivalent equation names its partial derivatives existentially; they
agree with the family $D$ because the derivative of a function is unique. -/
theorem IsModifiedSolution.eq_of_hasPartialDerivs {a mu nu : ℝ} (hv : IsModifiedSolution a mu nu v)
    (hD : HasPartialDerivs v D) (x t : ℝ) :
    D 0 1 x t + a * D 1 0 x t = mu * D 2 0 x t + nu * D 3 0 x t := by
  obtain ⟨vx, vt, vxx, vxt, vxxx, vxxt, h1, h2, h3, heq⟩ := hv
  have hv0 : HasPartialDerivFst v (D 1 0) := by
    rw [← hD.eq_zero_zero]
    exact hD.hasPartialDerivFst 0 0
  have hv1 : HasPartialDerivSnd v (D 0 1) := by
    rw [← hD.eq_zero_zero]
    exact hD.hasPartialDerivSnd 0 0
  have e1 : ∀ y s, vx y s = D 1 0 y s :=
    HasPartialDerivFst.congr (Transport.hasPartialDerivFst_of_hasPartialsOn h1) hv0 fun _ _ => rfl
  have e2 : ∀ y s, vt y s = D 0 1 y s :=
    HasPartialDerivSnd.congr (Transport.hasPartialDerivSnd_of_hasPartialsOn h1) hv1 fun _ _ => rfl
  have e3 : ∀ y s, vxx y s = D 2 0 y s :=
    HasPartialDerivFst.congr (Transport.hasPartialDerivFst_of_hasPartialsOn h2)
      (hD.hasPartialDerivFst 1 0) e1
  have e4 : ∀ y s, vxxx y s = D 3 0 y s :=
    HasPartialDerivFst.congr (Transport.hasPartialDerivFst_of_hasPartialsOn h3)
      (hD.hasPartialDerivFst 2 0) e3
  rw [← e1, ← e2, ← e3, ← e4]
  exact heq x t

/-- The **equivalent equation differentiated**. If $v$ solves
$v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$ and $D_{i,j}$ are its iterated partial derivatives,
then for all $i, j \in \mathbb{N}$ and at every point,
$$D_{i,j+1} + a D_{i+1,j} = \mu D_{i+2,j} + \nu D_{i+3,j},$$
which is $\partial_x^i \partial_t^j$ applied to (13.56) of [quarteroni2000numerical]. -/
theorem IsModifiedSolution.partial_eq {a mu nu : ℝ} (hv : IsModifiedSolution a mu nu v)
    (hD : HasPartialDerivs v D) (i j : ℕ) (x t : ℝ) :
    D i (j + 1) x t + a * D (i + 1) j x t = mu * D (i + 2) j x t + nu * D (i + 3) j x t := by
  have stepFst : ∀ i j : ℕ, (∀ y s : ℝ, D i (j + 1) y s + a * D (i + 1) j y s
        = mu * D (i + 2) j y s + nu * D (i + 3) j y s) →
      ∀ y s : ℝ, D (i + 1) (j + 1) y s + a * D (i + 2) j y s
        = mu * D (i + 3) j y s + nu * D (i + 4) j y s := fun i j h =>
    HasPartialDerivFst.congr
      ((hD.hasPartialDerivFst i (j + 1)).add ((hD.hasPartialDerivFst (i + 1) j).const_mul a))
      (((hD.hasPartialDerivFst (i + 2) j).const_mul mu).add
        ((hD.hasPartialDerivFst (i + 3) j).const_mul nu)) h
  have stepSnd : ∀ i j : ℕ, (∀ y s : ℝ, D i (j + 1) y s + a * D (i + 1) j y s
        = mu * D (i + 2) j y s + nu * D (i + 3) j y s) →
      ∀ y s : ℝ, D i (j + 2) y s + a * D (i + 1) (j + 1) y s
        = mu * D (i + 2) (j + 1) y s + nu * D (i + 3) (j + 1) y s := fun i j h =>
    HasPartialDerivSnd.congr
      ((hD.hasPartialDerivSnd i (j + 1)).add ((hD.hasPartialDerivSnd (i + 1) j).const_mul a))
      (((hD.hasPartialDerivSnd (i + 2) j).const_mul mu).add
        ((hD.hasPartialDerivSnd (i + 3) j).const_mul nu)) h
  have key : ∀ j i : ℕ, ∀ y s : ℝ, D i (j + 1) y s + a * D (i + 1) j y s
      = mu * D (i + 2) j y s + nu * D (i + 3) j y s := by
    intro j
    induction j with
    | zero =>
      intro i
      induction i with
      | zero => exact hv.eq_of_hasPartialDerivs hD
      | succ i ih => exact stepFst i 0 ih
    | succ j ihj => exact fun i => stepSnd i j (ihj i)
  exact key j i x t

/-- The **second-order equivalent equation of the upwind scheme**. Let $a > 0$,
$\Delta t, \Delta x > 0$, $\lambda = \Delta t / \Delta x$ and
$\mu = a \Delta x/2 - a^2 \Delta t/2$. Let $v$ solve $v_t + a v_x = \mu v_{xx}$, with iterated
partial derivatives $D_{i,j}$ such that $|D_{i,j}| \le M$ for $i + j = 3$. Then the residual of
the upwind scheme on $v$ satisfies
$$|\tau(x, t)| \le M (1 + a)^3 (\Delta t^2 + \Delta t \Delta x + \Delta x^2).$$
This is (13.59) of [quarteroni2000numerical]. The bound is one order better than the bound
$O(\Delta t + \Delta x)$ for a solution of the transport equation itself
(`FiniteDifference.Hyperbolic.abs_truncationError_upwind_le`).

The equation, differentiated (`FiniteDifference.Hyperbolic.IsModifiedSolution.partial_eq`),
gives $v_{tt} = a^2 v_{xx} + \mu (v_{xxt} - a v_{xxx})$. This cancels the term
$(\Delta t/2) v_{tt}$ of (13.58) against $-(a \Delta x/2) v_{xx}$ exactly for the stated value
of $\mu$. -/
theorem abs_residual_upwind_le_of_isModifiedSolution (hD : HasPartialDerivs v D)
    {a mu Δt Δx lam : ℝ} (ha : 0 < a) (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hmu : mu = a * Δx / 2 - a ^ 2 * Δt / 2) (hv : IsModifiedSolution a mu 0 v)
    (hM : ∀ i j, i + j = 3 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |residual (upwind a lam) Δt Δx v x t|
      ≤ M * (1 + a) ^ 3 * (Δt ^ 2 + Δt * Δx + Δx ^ 2) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 3 rfl 0 0)
  have hE := abs_residual_upwind_sub_le_two hD ha hΔt hΔx hlam hM x t
  -- the equation and its two derivatives
  have p00 : D 0 1 x t + a * D 1 0 x t = mu * D 2 0 x t + 0 * D 3 0 x t :=
    hv.eq_of_hasPartialDerivs hD x t
  have p01 : D 0 2 x t + a * D 1 1 x t = mu * D 2 1 x t + 0 * D 3 1 x t :=
    hv.partial_eq hD 0 1 x t
  have p10 : D 1 1 x t + a * D 2 0 x t = mu * D 3 0 x t + 0 * D 4 0 x t :=
    hv.partial_eq hD 1 0 x t
  have hkey : residual (upwind a lam) Δt Δx v x t
      = Δt * mu / 2 * (D 2 1 x t - a * D 3 0 x t)
        + (residual (upwind a lam) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)) := by
    linear_combination p00 + (Δt / 2) * p01 - (a * Δt / 2) * p10 + D 2 0 x t * hmu
  have hmuabs : |mu| ≤ a * Δx / 2 + a ^ 2 * Δt / 2 := by
    rw [hmu]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ a * Δx / 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2 * Δt / 2)]
  have hb1 : |D 2 1 x t - a * D 3 0 x t| ≤ M + a * M := by
    refine (abs_sub _ _).trans (add_le_add (hM 2 1 rfl x t) ?_)
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hM 3 0 rfl x t) ha.le
  calc |residual (upwind a lam) Δt Δx v x t|
      ≤ |Δt * mu / 2 * (D 2 1 x t - a * D 3 0 x t)|
        + |residual (upwind a lam) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)| := by
        conv_lhs => rw [hkey]
        exact abs_add_le _ _
    _ ≤ Δt * (a * Δx / 2 + a ^ 2 * Δt / 2) / 2 * (M + a * M)
        + (Δt ^ 2 / 6 * M + a * Δx ^ 2 / 6 * M) := by
        refine add_le_add ?_ hE
        rw [abs_mul, abs_div, abs_mul, abs_of_pos hΔt, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        refine mul_le_mul ?_ hb1 (abs_nonneg _) (by positivity)
        gcongr
    _ = M * ((1 + a) * a / 4 * (Δt * Δx) + ((1 + a) * a ^ 2 / 4 + 1 / 6) * Δt ^ 2
        + a / 6 * Δx ^ 2) := by ring
    _ ≤ M * ((1 + a) ^ 3 * (Δt * Δx) + (1 + a) ^ 3 * Δt ^ 2 + (1 + a) ^ 3 * Δx ^ 2) := by
        have h1 : (1 + a) * a / 4 ≤ (1 + a) ^ 3 := by nlinarith [ha.le, sq_nonneg a]
        have h2 : (1 + a) * a ^ 2 / 4 + 1 / 6 ≤ (1 + a) ^ 3 := by nlinarith [ha.le, sq_nonneg a]
        have h3 : a / 6 ≤ (1 + a) ^ 3 := by nlinarith [ha.le, sq_nonneg a]
        refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ ?_) ?_) hM0
        · exact mul_le_mul_of_nonneg_right h1 (by positivity)
        · exact mul_le_mul_of_nonneg_right h2 (by positivity)
        · exact mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = M * (1 + a) ^ 3 * (Δt ^ 2 + Δt * Δx + Δx ^ 2) := by ring

/-! ### The third-order equivalent equation of a three-point scheme -/

/-- For real $c$, $d$ and $N$ with $|d| \le N$, $|c d| \le |c| N$. -/
private theorem abs_mul_le_of_abs_le {c d N : ℝ} (h : |d| ≤ N) : |c * d| ≤ |c| * N := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

/-- The **third-order equivalent equation of a conservative three-point scheme**. Let
$\Delta t, \Delta x > 0$ and $\lambda = \Delta t / \Delta x$. Let the three-point stencil with
weights $(c_-, c_0, c_+)$ be consistent, $c_- + c_0 + c_+ = 1$, with $c_+ - c_- = -\lambda a$,
and let $\mu$ and $\nu$ satisfy
$$\frac{\Delta x^2}{2} (c_+ + c_-) = \Delta t \Bigl(\mu + \frac{a^2 \Delta t}{2}\Bigr), \qquad
  \nu + \frac{a \Delta x^2}{6} = a \mu \Delta t + \frac{a^3 \Delta t^2}{6}.$$
Let $v$ solve the equivalent equation $v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$, with iterated
partial derivatives $D_{i,j}$ such that $|D_{i,j}| \le M$ for $i + j \le 5$. Then the residual
of the scheme on $v$ satisfies
$$|\tau(x, t)| \le M \Bigl( \frac{\Delta t}{2} (\mu^2 + |a| |\nu| + |\mu| |\nu| + |\nu|) +
  \frac{\Delta t^2}{6} (a^2 + |a| + 1)(|\mu| + |\nu|) + \frac{\Delta t^3}{24} + \frac{(|c_-| +
  |c_+|) \Delta x^4}{24 \Delta t} \Bigr).$$
This is in §13.9.1 and Table 13.2 of [quarteroni2000numerical]; the relations for $\mu$ and
$\nu$ give the coefficients of Warming and Hyett.

Every term of the bound carries a factor $\mu^2$, $\mu \nu$, $\nu$, $\Delta t \mu$ or
$\Delta t \nu$, apart from the fourth-order remainders. The term $O(\Delta x)$ in $v_{xx}$ and
the term $O(\Delta x^2)$ in $v_{xxx}$ both cancel, and this is what fixes $\mu$ and $\nu$. With
$\lambda$ fixed, $\mu = O(\Delta x)$ and $\nu = O(\Delta x^2)$, so the bound is $O(\Delta x^3)$,
one order better than for the second-order equivalent equation. The proof substitutes
$\partial_t = -a \partial_x + \mu \partial_x^2 + \nu \partial_x^3$ five times
(`FiniteDifference.Hyperbolic.IsModifiedSolution.partial_eq`) into the two time derivatives of
`FiniteDifference.Hyperbolic.residual_threePoint_expansion`, which is why partial derivatives up
to order $5$ enter. -/
theorem abs_residual_threePoint_le_of_isModifiedSolution (hD : HasPartialDerivs v D)
    {a mu nu Δt Δx lam cm c0 cp : ℝ} (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hsum : cm + c0 + cp = 1) (hdiff : cp - cm = -(lam * a))
    (hplus : Δx ^ 2 / 2 * (cp + cm) = Δt * (mu + a ^ 2 * Δt / 2))
    (hnu : nu + a * Δx ^ 2 / 6 = a * mu * Δt + a ^ 3 * Δt ^ 2 / 6)
    (hv : IsModifiedSolution a mu nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (x t : ℝ) :
    |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t|
      ≤ M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by omega) 0 0)
  have hexp := residual_threePoint_expansion (Δx := Δx) hD (fun i j h => hM i j (by omega))
    cm c0 cp hΔt x t
  have q00 : D 0 1 x t + a * D 1 0 x t = mu * D 2 0 x t + nu * D 3 0 x t :=
    hv.eq_of_hasPartialDerivs hD x t
  have q01 : D 0 2 x t + a * D 1 1 x t = mu * D 2 1 x t + nu * D 3 1 x t :=
    hv.partial_eq hD 0 1 x t
  have q10 : D 1 1 x t + a * D 2 0 x t = mu * D 3 0 x t + nu * D 4 0 x t :=
    hv.partial_eq hD 1 0 x t
  have q20 : D 2 1 x t + a * D 3 0 x t = mu * D 4 0 x t + nu * D 5 0 x t :=
    hv.partial_eq hD 2 0 x t
  have q02 : D 0 3 x t + a * D 1 2 x t = mu * D 2 2 x t + nu * D 3 2 x t :=
    hv.partial_eq hD 0 2 x t
  have q11 : D 1 2 x t + a * D 2 1 x t = mu * D 3 1 x t + nu * D 4 1 x t :=
    hv.partial_eq hD 1 1 x t
  have hE : D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
        - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
          + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt
      = D 0 1 x t + a * D 1 0 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
        - (mu + a ^ 2 * Δt / 2) * D 2 0 x t + a * Δx ^ 2 / 6 * D 3 0 x t := by
    rw [hsum, hdiff, hplus]
    field_simp
    ring
  have hE2 : D 0 1 x t + a * D 1 0 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
        - (mu + a ^ 2 * Δt / 2) * D 2 0 x t + a * Δx ^ 2 / 6 * D 3 0 x t
      = (Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
        + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
        + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
        + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
        + Δt ^ 2 * mu / 6 * D 2 2 x t
        + Δt ^ 2 * nu / 6 * D 3 2 x t := by
    linear_combination q00 + (Δt / 2) * q01 - (a * Δt / 2) * q10
      + (mu * Δt / 2 + a ^ 2 * Δt ^ 2 / 6) * q20 + (Δt ^ 2 / 6) * q02 - (a * Δt ^ 2 / 6) * q11
      + D 3 0 x t * hnu
  have hkey : residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
      = ((Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
          + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
          + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
          + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
          + Δt ^ 2 * mu / 6 * D 2 2 x t
          + Δt ^ 2 * nu / 6 * D 3 2 x t)
        + (residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
            - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
              + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t
              + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)) := by
    linear_combination hE.trans hE2
  have hT : |(Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
        + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
        + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
        + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
        + Δt ^ 2 * mu / 6 * D 2 2 x t
        + Δt ^ 2 * nu / 6 * D 3 2 x t|
      ≤ (|Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6|
          + |Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6|
          + |Δt * nu / 2 - Δt ^ 2 * a * mu / 6| + |-(Δt ^ 2 * a * nu / 6)|
          + |Δt ^ 2 * mu / 6| + |Δt ^ 2 * nu / 6|) * M := by
    have b1 := abs_mul_le_of_abs_le (c := Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6)
      (hM 4 0 (by omega) x t)
    have b2 := abs_mul_le_of_abs_le (c := Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6)
      (hM 5 0 (by omega) x t)
    have b3 := abs_mul_le_of_abs_le (c := Δt * nu / 2 - Δt ^ 2 * a * mu / 6)
      (hM 3 1 (by omega) x t)
    have b4 := abs_mul_le_of_abs_le (c := -(Δt ^ 2 * a * nu / 6)) (hM 4 1 (by omega) x t)
    have b5 := abs_mul_le_of_abs_le (c := Δt ^ 2 * mu / 6) (hM 2 2 (by omega) x t)
    have b6 := abs_mul_le_of_abs_le (c := Δt ^ 2 * nu / 6) (hM 3 2 (by omega) x t)
    calc |(Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
          + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
          + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
          + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
          + Δt ^ 2 * mu / 6 * D 2 2 x t
          + Δt ^ 2 * nu / 6 * D 3 2 x t|
        ≤ |Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6| * M
            + |Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6| * M
            + |Δt * nu / 2 - Δt ^ 2 * a * mu / 6| * M + |-(Δt ^ 2 * a * nu / 6)| * M
            + |Δt ^ 2 * mu / 6| * M + |Δt ^ 2 * nu / 6| * M :=
          (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
            ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
              ((abs_add_le _ _).trans (add_le_add b1 b2)) b3)) b4)) b5)) b6)
      _ = _ := by ring
  have hcoef : |Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6|
        + |Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6|
        + |Δt * nu / 2 - Δt ^ 2 * a * mu / 6| + |-(Δt ^ 2 * a * nu / 6)|
        + |Δt ^ 2 * mu / 6| + |Δt ^ 2 * nu / 6|
      ≤ Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
        + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6 := by
    have e1 : |Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6|
        ≤ Δt * (mu ^ 2 + |a| * |nu|) / 2 + Δt ^ 2 * a ^ 2 * |mu| / 6 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_of_pos hΔt, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg mu)]
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
          abs_of_nonneg (sq_nonneg a), abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e2 : |Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6|
        ≤ Δt * (|mu| * |nu|) / 2 + Δt ^ 2 * a ^ 2 * |nu| / 6 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos hΔt,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact le_of_eq (by ring)
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
          abs_of_nonneg (sq_nonneg a), abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e3 : |Δt * nu / 2 - Δt ^ 2 * a * mu / 6|
        ≤ Δt * |nu| / 2 + Δt ^ 2 * |a| * |mu| / 6 := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_of_pos hΔt, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e4 : |-(Δt ^ 2 * a * nu / 6)| = Δt ^ 2 * |a| * |nu| / 6 := by
      rw [abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e5 : |Δt ^ 2 * mu / 6| = Δt ^ 2 * |mu| / 6 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e6 : |Δt ^ 2 * nu / 6| = Δt ^ 2 * |nu| / 6 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    rw [e4, e5, e6]
    linarith [e1, e2, e3]
  calc |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t|
      ≤ |(Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
          + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
          + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
          + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
          + Δt ^ 2 * mu / 6 * D 2 2 x t
          + Δt ^ 2 * nu / 6 * D 3 2 x t|
        + |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
            - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
              + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t
              + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)| := by
        conv_lhs => rw [hkey]
        exact abs_add_le _ _
    _ ≤ (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6) * M
        + M * (Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) :=
        add_le_add (hT.trans (mul_le_mul_of_nonneg_right hcoef hM0)) hexp
    _ = M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) := by ring

/-- The **third-order equivalent equation of the upwind scheme**. Let $a > 0$,
$\Delta t, \Delta x > 0$, $\lambda = \Delta t / \Delta x$,
$$\mu = \frac{a \Delta x}{2} - \frac{a^2 \Delta t}{2}, \qquad \nu = -\frac{a}{6} (\Delta x^2 - 3
  a \Delta x \Delta t + 2 a^2 \Delta t^2).$$
Let $v$ solve $v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$, with iterated partial derivatives
$D_{i,j}$ such that $|D_{i,j}| \le M$ for $i + j \le 5$. Then the residual of the upwind scheme
on $v$ satisfies
$$|\tau(x, t)| \le M \Bigl( \frac{\Delta t}{2} (\mu^2 + |a| |\nu| + |\mu| |\nu| + |\nu|) +
  \frac{\Delta t^2}{6} (a^2 + |a| + 1)(|\mu| + |\nu|) + \frac{\Delta t^3}{24} + \frac{\lambda a
  \Delta x^4}{24 \Delta t} \Bigr).$$
With $\lambda$ fixed this is $O(\Delta x^3)$, one order better than (13.59). This is (13.60) and
the upwind row of Table 13.2 of [quarteroni2000numerical].

The text after (13.60) of the source gives $\nu = (a/6)(a^2 \Delta t^2 - \Delta x^2)$, which
disagrees with Table 13.2. The value of the table, used here, is the correct one: the text omits
the contribution $-2 a \mu \partial_x^3$ when it substitutes $v_{tt}$. -/
theorem abs_residual_upwind_le_of_isModifiedSolution_third (hD : HasPartialDerivs v D)
    {a mu nu Δt Δx lam : ℝ} (ha : 0 < a) (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hmu : mu = a * Δx / 2 - a ^ 2 * Δt / 2)
    (hnu : nu = -(a / 6) * (Δx ^ 2 - 3 * a * Δx * Δt + 2 * a ^ 2 * Δt ^ 2))
    (hv : IsModifiedSolution a mu nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (x t : ℝ) :
    |residual (upwind a lam) Δt Δx v x t|
      ≤ M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + lam * a * Δx ^ 4 / (24 * Δt)) := by
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  rw [upwind_eq_of_pos ha]
  refine (abs_residual_threePoint_le_of_isModifiedSolution hD hΔt hΔx hlam (by ring) (by ring)
    ?_ ?_ hv hM x t).trans ?_
  · rw [hmu, hlam]
    field_simp
    ring
  · rw [hnu, hmu]
    ring
  · have hcc : |lam * a| + |(0 : ℝ)| = lam * a := by
      rw [abs_of_pos (by positivity), abs_zero, add_zero]
    rw [hcc]

/-- The **third-order equivalent equation of the Lax–Friedrichs scheme**. Let
$\Delta t, \Delta x > 0$, $\lambda = \Delta t / \Delta x$,
$$\mu = \frac{\Delta x^2}{2 \Delta t} \bigl(1 - (a \lambda)^2\bigr), \qquad \nu = \frac{a \Delta
  x^2}{3} \bigl(1 - (a \lambda)^2\bigr).$$
Let $v$ solve $v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$, with iterated partial derivatives
$D_{i,j}$ such that $|D_{i,j}| \le M$ for $i + j \le 5$. Then the residual of the Lax–Friedrichs
scheme on $v$ satisfies
$$|\tau(x, t)| \le M \Bigl( \frac{\Delta t}{2} (\mu^2 + |a| |\nu| + |\mu| |\nu| + |\nu|) +
  \frac{\Delta t^2}{6} (a^2 + |a| + 1)(|\mu| + |\nu|) + \frac{\Delta t^3}{24} + \frac{(1 +
  |\lambda a|) \Delta x^4}{24 \Delta t} \Bigr),$$
which is $O(\Delta x^3)$ for fixed $\lambda$. This is in Table 13.2 and Exercise 13.8 of
[quarteroni2000numerical].

Here $\mu = O(\Delta x^2 / \Delta t)$, which is why the Lax–Friedrichs scheme is consistent only
when $\Delta x^2 / \Delta t \to 0$. -/
theorem abs_residual_laxFriedrichs_le_of_isModifiedSolution (hD : HasPartialDerivs v D)
    {a mu nu Δt Δx lam : ℝ} (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hmu : mu = Δx ^ 2 / (2 * Δt) * (1 - (a * lam) ^ 2))
    (hnu : nu = a * Δx ^ 2 / 3 * (1 - (a * lam) ^ 2))
    (hv : IsModifiedSolution a mu nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (x t : ℝ) :
    |residual (laxFriedrichs a lam) Δt Δx v x t|
      ≤ M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + (1 + |lam * a|) * Δx ^ 4 / (24 * Δt)) := by
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by omega) 0 0)
  rw [laxFriedrichs]
  refine (abs_residual_threePoint_le_of_isModifiedSolution hD hΔt hΔx hlam (by ring) (by ring)
    ?_ ?_ hv hM x t).trans ?_
  · rw [hmu, hlam]
    field_simp
    ring
  · rw [hnu, hmu, hlam]
    field_simp
    ring
  · have hcc : |(1 + lam * a) / 2| + |(1 - lam * a) / 2| ≤ 1 + |lam * a| := by
      have h1 : |(1 + lam * a) / 2| ≤ (1 + |lam * a|) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
        exact (abs_add_le _ _).trans (by rw [abs_one])
      have h2 : |(1 - lam * a) / 2| ≤ (1 + |lam * a|) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
        exact (abs_sub _ _).trans (by rw [abs_one])
      linarith
    gcongr

/-- The **third-order equivalent equation of the Lax–Wendroff scheme**. Let
$\Delta t, \Delta x > 0$, $\lambda = \Delta t / \Delta x$ and
$$\nu = \frac{a \Delta x^2}{6} \bigl((a \lambda)^2 - 1\bigr).$$
Let $v$ solve $v_t + a v_x = \nu v_{xxx}$, with iterated partial derivatives $D_{i,j}$ such that
$|D_{i,j}| \le M$ for $i + j \le 5$. Then the residual of the Lax–Wendroff scheme on $v$
satisfies
$$|\tau(x, t)| \le M \Bigl( \frac{\Delta t}{2} (|a| |\nu| + |\nu|) + \frac{\Delta t^2}{6} (a^2 +
  |a| + 1) |\nu| + \frac{\Delta t^3}{24} + \frac{|\lambda a| (1 + |\lambda a|) \Delta x^4}{24
  \Delta t} \Bigr),$$
which is $O(\Delta x^3)$ for fixed $\lambda$. This is in Table 13.2 and Exercise 13.8 of
[quarteroni2000numerical].

The coefficient $\mu$ is $0$: the scheme is second-order accurate, so it has no dissipative
term. -/
theorem abs_residual_laxWendroff_le_of_isModifiedSolution (hD : HasPartialDerivs v D)
    {a nu Δt Δx lam : ℝ} (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hnu : nu = a * Δx ^ 2 / 6 * ((a * lam) ^ 2 - 1))
    (hv : IsModifiedSolution a 0 nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (x t : ℝ) :
    |residual (laxWendroff a lam) Δt Δx v x t|
      ≤ M * (Δt * (|a| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * |nu| / 6
          + Δt ^ 3 / 24 + |lam * a| * (1 + |lam * a|) * Δx ^ 4 / (24 * Δt)) := by
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by omega) 0 0)
  rw [laxWendroff]
  refine (abs_residual_threePoint_le_of_isModifiedSolution hD hΔt hΔx hlam (by ring) (by ring)
    ?_ ?_ hv hM x t).trans ?_
  · rw [hlam]
    field_simp
    ring
  · rw [hnu, hlam]
    field_simp
    ring
  · have hb : |1 + lam * a| ≤ 1 + |lam * a| := by
      have h := abs_add_le (1 : ℝ) (lam * a)
      rw [abs_one] at h
      exact h
    have hb2 : |lam * a - 1| ≤ 1 + |lam * a| := by
      have h := abs_sub (lam * a) (1 : ℝ)
      rw [abs_one] at h
      linarith
    have hcc : |lam * a / 2 * (1 + lam * a)| + |lam * a / 2 * (lam * a - 1)|
        ≤ |lam * a| * (1 + |lam * a|) := by
      have h1 : |lam * a / 2 * (1 + lam * a)| ≤ |lam * a| / 2 * (1 + |lam * a|) := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
      have h2 : |lam * a / 2 * (lam * a - 1)| ≤ |lam * a| / 2 * (1 + |lam * a|) := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left hb2 (by positivity)
      linarith
    simp only [abs_zero]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have hfac : (|lam * a / 2 * (1 + lam * a)| + |lam * a / 2 * (lam * a - 1)|) * Δx ^ 4
        / (24 * Δt) ≤ |lam * a| * (1 + |lam * a|) * Δx ^ 4 / (24 * Δt) := by
      gcongr
    linarith [hfac]

/-! ### The truncation errors of the leap-frog and Newmark schemes -/

/-- The **leap-frog scheme is second-order accurate**. Let $u$ have the iterated partial derivatives
$D_{i,j} = \partial_x^i \partial_t^j u$, with $|u_{tttt}| \le M$ and $|u_{xxxx}| \le M'$, and
let $\Delta t, \Delta x > 0$. Then for all $x$, $t$,
$$\Bigl| \frac{u(x, t + \Delta t) - 2 u(x, t) + u(x, t - \Delta t)}{\Delta t^2} - \gamma^2
  \frac{u(x + \Delta x, t) - 2 u(x, t) + u(x - \Delta x, t)}{\Delta x^2} - (u_{tt} - \gamma^2
  u_{xx})(x, t) \Bigr| \le \frac{M}{12} \Delta t^2 + \frac{\gamma^2 M'}{12} \Delta x^2.$$
On a solution of the wave equation the last term on the left vanishes, so the truncation error
of the leap-frog scheme (13.44) is $O(\Delta t^2 + \Delta x^2)$, for every ratio
$\Delta t / \Delta x$ and not only for $\Delta t = \Delta x$. This is in §13.8.1 of
[quarteroni2000numerical].

Both second central differences are symmetric third-order Taylor expansions, whose odd terms
cancel. -/
theorem abs_residual_leapFrog_le {u : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {γ M M' Δt Δx : ℝ}
    (hD : HasPartialDerivs u D) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hM : ∀ y s, |D 0 4 y s| ≤ M) (hM' : ∀ y s, |D 4 0 y s| ≤ M') (x t : ℝ) :
    |(u x (t + Δt) - 2 * u x t + u x (t - Δt)) / Δt ^ 2
        - γ ^ 2 * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2)
        - (D 0 2 x t - γ ^ 2 * D 2 0 x t)|
      ≤ M / 12 * Δt ^ 2 + γ ^ 2 * M' / 12 * Δx ^ 2 := by
  have hu : D 0 0 = u := hD.eq_zero_zero
  have h1 : |(u x (t + Δt) - 2 * u x t + u x (t - Δt)) / Δt ^ 2 - D 0 2 x t|
      ≤ M * Δt ^ 2 / 12 := by
    have h := abs_secondDiff_snd_sub_le (i := 0) (j := 0) hD hM hΔt x t
    rwa [hu] at h
  have h2 : |(u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t|
      ≤ M' * Δx ^ 2 / 12 := by
    have h := abs_secondDiff_fst_sub_le (i := 0) (j := 0) hD hM' hΔx x t
    rwa [hu] at h
  have hid : (u x (t + Δt) - 2 * u x t + u x (t - Δt)) / Δt ^ 2
        - γ ^ 2 * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2)
        - (D 0 2 x t - γ ^ 2 * D 2 0 x t)
      = ((u x (t + Δt) - 2 * u x t + u x (t - Δt)) / Δt ^ 2 - D 0 2 x t)
        - γ ^ 2 * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t) := by ring
  rw [hid]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (sq_nonneg γ)]
  calc |(u x (t + Δt) - 2 * u x t + u x (t - Δt)) / Δt ^ 2 - D 0 2 x t|
        + γ ^ 2 * |(u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t|
      ≤ M * Δt ^ 2 / 12 + γ ^ 2 * (M' * Δx ^ 2 / 12) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg γ))
    _ = M / 12 * Δt ^ 2 + γ ^ 2 * M' / 12 * Δx ^ 2 := by ring

/-- The **Newmark scheme is second-order accurate for $\theta = 1/2$**. Let $u$ be a solution of the
wave equation $u_{tt} = \gamma^2 u_{xx}$ with iterated partial derivatives
$D_{i,j} = \partial_x^i \partial_t^j u$ such that $|D_{i,j}| \le M$ for $i + j \le 4$, and let
$0 < \Delta t \le 1$, $\Delta x > 0$ and $\lambda = \Delta t / \Delta x$. Insert $u$ and
$v = u_t$ into the two relations (13.45) of [quarteroni2000numerical] and divide each by
$\Delta t$; write $\delta^2 w(x) = w(x + \Delta x) - 2 w(x) + w(x - \Delta x)$. Then for every
$\beta$ and all $x$, $t$,
$$\Bigl| \frac{1}{\Delta t} \Bigl( u(x, t + \Delta t) - u(x, t) - \Delta t\, u_t(x, t) - (\gamma
  \lambda)^2 \bigl(\beta\, \delta^2 u(x, t + \Delta t) + (\tfrac{1}{2} - \beta)\, \delta^2 u(x,
  t)\bigr) \Bigr) \Bigr| \le M \Bigl( \Bigl(\frac{1}{6} + \frac{3}{2} \gamma^2 |\beta|\Bigr)
  \Delta t^2 + \frac{\gamma^2 (|\beta| + |\tfrac{1}{2} - \beta|)}{12} \Delta x^2 \Bigr),$$
and, for $\theta = 1/2$,
$$\Bigl| \frac{1}{\Delta t} \Bigl( u_t(x, t + \Delta t) - u_t(x, t) - \frac{(\gamma
  \lambda)^2}{\Delta t} \bigl(\tfrac{1}{2}\, \delta^2 u(x, t + \Delta t) + \tfrac{1}{2}\,
  \delta^2 u(x, t)\bigr) \Bigr) \Bigr| \le M \Bigl( \Bigl(\frac{1}{6} + \frac{\gamma^2}{4}\Bigr)
  \Delta t^2 + \frac{\gamma^2}{12} \Delta x^2 \Bigr).$$
This is in §13.8.1 of [quarteroni2000numerical].

The source states second order without a condition on $\theta$. The velocity update is the
$\theta$-method for $v' = u_{tt}$, and its leading error term is
$(\frac{1}{2} - \theta) \Delta t\, u_{ttt}$, which vanishes only for $\theta = 1/2$; the theorem
proves only the case $\theta = 1/2$ and does not prove the failure for other $\theta$. The first
relation uses the wave equation itself, and the second uses it differentiated once in time,
$u_{ttt} = \gamma^2 u_{xxt}$. -/
theorem abs_residual_newmark_le {u : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {γ β M Δt Δx lam : ℝ}
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
        ≤ M * ((1 / 6 + γ ^ 2 / 4) * Δt ^ 2 + γ ^ 2 / 12 * Δx ^ 2) := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hu : D 0 0 = u := hD.eq_zero_zero
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 4 (by norm_num) 0 0)
  have hzero : D 0 2 x t - γ ^ 2 * D 2 0 x t = 0 := by rw [hwave x t]; ring
  have hwave3 : ∀ y s, D 0 3 y s = γ ^ 2 * D 2 1 y s :=
    HasPartialDerivSnd.congr (hD.hasPartialDerivSnd 0 2)
      ((hD.hasPartialDerivSnd 2 0).const_mul (γ ^ 2)) hwave
  have hzero3 : D 0 3 x t - γ ^ 2 * D 2 1 x t = 0 := by rw [hwave3 x t]; ring
  have hE1 : |u x (t + Δt) - u x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t|
      ≤ M * Δt ^ 3 / 6 := by
    have h := abs_taylor_snd_two (i := 0) (j := 0) hD (hM 0 3 (by norm_num)) x t Δt
    rw [hu, abs_of_pos hΔt] at h
    exact h
  have heps : |D 0 1 x (t + Δt) - D 0 1 x t - Δt * D 0 2 x t - Δt ^ 2 / 2 * D 0 3 x t|
      ≤ M * Δt ^ 3 / 6 := by
    have h := abs_taylor_snd_two (i := 0) (j := 1) hD (hM 0 4 (by norm_num)) x t Δt
    rw [abs_of_pos hΔt] at h
    exact h
  have hep : |(u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2
      - D 2 0 x (t + Δt)| ≤ M * Δx ^ 2 / 12 := by
    have h := abs_secondDiff_fst_sub_le (i := 0) (j := 0) hD
      (hM 4 0 (by norm_num)) hΔx x (t + Δt)
    rwa [hu] at h
  have heq : |(u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t|
      ≤ M * Δx ^ 2 / 12 := by
    have h := abs_secondDiff_fst_sub_le (i := 0) (j := 0) hD
      (hM 4 0 (by norm_num)) hΔx x t
    rwa [hu] at h
  have he1 : |D 2 0 x (t + Δt) - D 2 0 x t - Δt * D 2 1 x t| ≤ M * Δt ^ 2 / 2 :=
    abs_taylor_snd_one (i := 2) (j := 0) hD (hM 2 2 (by norm_num)) x t Δt
  have hb21 : |D 2 1 x t| ≤ M := hM 2 1 (by norm_num) x t
  constructor
  · have hid : (u x (t + Δt) - u x t - (Δt * D 0 1 x t
          + (γ * (Δt / Δx)) ^ 2
            * (β * (u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt))
              + (1 / 2 - β) * (u (x + Δx) t - 2 * u x t + u (x - Δx) t)))) / Δt * Δt
        = (u x (t + Δt) - u x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t)
          + Δt ^ 2 / 2 * (D 0 2 x t - γ ^ 2 * D 2 0 x t)
          - γ ^ 2 * Δt ^ 2 * β
            * ((u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2
              - D 2 0 x (t + Δt))
          - γ ^ 2 * Δt ^ 2 * (1 / 2 - β)
            * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t)
          - γ ^ 2 * Δt ^ 2 * β * (D 2 0 x (t + Δt) - D 2 0 x t - Δt * D 2 1 x t)
          - γ ^ 2 * Δt ^ 3 * β * D 2 1 x t := by
      field_simp
      ring
    rw [hzero, mul_zero, add_zero] at hid
    refine le_of_mul_le_mul_right ?_ hΔt
    calc |(u x (t + Δt) - u x t - (Δt * D 0 1 x t
            + (γ * (Δt / Δx)) ^ 2
              * (β * (u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt))
                + (1 / 2 - β) * (u (x + Δx) t - 2 * u x t + u (x - Δx) t)))) / Δt| * Δt
        = |(u x (t + Δt) - u x t - (Δt * D 0 1 x t
            + (γ * (Δt / Δx)) ^ 2
              * (β * (u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt))
                + (1 / 2 - β) * (u (x + Δx) t - 2 * u x t + u (x - Δx) t)))) / Δt * Δt| := by
          rw [abs_mul, abs_of_pos hΔt]
      _ ≤ M * Δt ^ 3 / 6 + γ ^ 2 * Δt ^ 2 * |β| * (M * Δx ^ 2 / 12)
          + γ ^ 2 * Δt ^ 2 * |1 / 2 - β| * (M * Δx ^ 2 / 12)
          + γ ^ 2 * Δt ^ 2 * |β| * (M * Δt ^ 2 / 2) + γ ^ 2 * Δt ^ 3 * |β| * M := by
          rw [hid]
          have habs : ∀ c d e : ℝ, |c| ≤ e →
              |γ ^ 2 * Δt ^ 2 * d * c| ≤ γ ^ 2 * Δt ^ 2 * |d| * e := by
            intro c d e hc
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg γ),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ Δt ^ 2)]
            exact mul_le_mul_of_nonneg_left hc (by positivity)
          have habs' : |γ ^ 2 * Δt ^ 3 * β * D 2 1 x t| ≤ γ ^ 2 * Δt ^ 3 * |β| * M := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg γ),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ Δt ^ 3)]
            exact mul_le_mul_of_nonneg_left hb21 (by positivity)
          refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
            ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
              (add_le_add hE1 (habs _ _ _ hep))) (habs _ _ _ heq))) (habs _ _ _ he1))) habs')
      _ ≤ M * ((1 / 6 + 3 / 2 * γ ^ 2 * |β|) * Δt ^ 2
          + γ ^ 2 * (|β| + |1 / 2 - β|) / 12 * Δx ^ 2) * Δt := by
          have hd : (0 : ℝ) ≤ Δt - Δt ^ 2 := by nlinarith
          have hd2 : (0 : ℝ) ≤ Δt ^ 3 - Δt ^ 4 := by nlinarith
          have k1 : (0 : ℝ) ≤ γ ^ 2 * |β| * M * Δx ^ 2 * (Δt - Δt ^ 2) :=
            mul_nonneg (by positivity) hd
          have k2 : (0 : ℝ) ≤ γ ^ 2 * |1 / 2 - β| * M * Δx ^ 2 * (Δt - Δt ^ 2) :=
            mul_nonneg (by positivity) hd
          have k3 : (0 : ℝ) ≤ γ ^ 2 * |β| * M * (Δt ^ 3 - Δt ^ 4) :=
            mul_nonneg (by positivity) hd2
          nlinarith [k1, k2, k3]
  · have hid : (D 0 1 x (t + Δt) - D 0 1 x t - (γ * (Δt / Δx)) ^ 2 / Δt
          * (1 / 2 * (u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt))
            + (1 - 1 / 2) * (u (x + Δx) t - 2 * u x t + u (x - Δx) t))) / Δt * Δt
        = (D 0 1 x (t + Δt) - D 0 1 x t - Δt * D 0 2 x t - Δt ^ 2 / 2 * D 0 3 x t)
          + Δt * (D 0 2 x t - γ ^ 2 * D 2 0 x t)
          + Δt ^ 2 / 2 * (D 0 3 x t - γ ^ 2 * D 2 1 x t)
          - γ ^ 2 * Δt / 2
            * ((u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2
              - D 2 0 x (t + Δt))
          - γ ^ 2 * Δt / 2
            * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t)
          - γ ^ 2 * Δt / 2 * (D 2 0 x (t + Δt) - D 2 0 x t - Δt * D 2 1 x t) := by
      field_simp
      ring
    rw [hzero, hzero3, mul_zero, mul_zero, add_zero, add_zero] at hid
    refine le_of_mul_le_mul_right ?_ hΔt
    calc |(D 0 1 x (t + Δt) - D 0 1 x t - (γ * (Δt / Δx)) ^ 2 / Δt
            * (1 / 2 * (u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt))
              + (1 - 1 / 2) * (u (x + Δx) t - 2 * u x t + u (x - Δx) t))) / Δt| * Δt
        = |(D 0 1 x (t + Δt) - D 0 1 x t - (γ * (Δt / Δx)) ^ 2 / Δt
            * (1 / 2 * (u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt))
              + (1 - 1 / 2) * (u (x + Δx) t - 2 * u x t + u (x - Δx) t))) / Δt * Δt| := by
          rw [abs_mul, abs_of_pos hΔt]
      _ ≤ M * Δt ^ 3 / 6 + γ ^ 2 * Δt / 2 * (M * Δx ^ 2 / 12)
          + γ ^ 2 * Δt / 2 * (M * Δx ^ 2 / 12) + γ ^ 2 * Δt / 2 * (M * Δt ^ 2 / 2) := by
          rw [hid]
          have habs : ∀ c e : ℝ, |c| ≤ e → |γ ^ 2 * Δt / 2 * c| ≤ γ ^ 2 * Δt / 2 * e := by
            intro c e hc
            rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (sq_nonneg γ), abs_of_pos hΔt,
              abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            exact mul_le_mul_of_nonneg_left hc (by positivity)
          exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
            ((abs_sub _ _).trans (add_le_add heps (habs _ _ hep))) (habs _ _ heq)))
            (habs _ _ he1))
      _ ≤ M * ((1 / 6 + γ ^ 2 / 4) * Δt ^ 2 + γ ^ 2 / 12 * Δx ^ 2) * Δt := by
          nlinarith [mul_nonneg hM0 (sq_nonneg Δx), mul_nonneg hM0 (sq_nonneg Δt),
            mul_nonneg (mul_nonneg hM0 (sq_nonneg γ)) (sq_nonneg Δx),
            mul_nonneg (mul_nonneg hM0 (sq_nonneg γ)) (sq_nonneg Δt),
            sq_nonneg γ, hΔt.le, hΔx.le]

end PartialTaylor

/-!
### The energy of the second-order schemes for the wave equation

Remark 13.4 of [quarteroni2000numerical] states that the leap-frog scheme (13.44) is stable under
the CFL condition and that the Newmark scheme (13.45) is unconditionally stable for
$2\beta \ge \theta \ge 1/2$. Neither statement is about the Euclidean norm of the state
$(u^{n+1}, u^n)$. On the constant mode the amplification matrix of the leap-frog scheme is
$\begin{bmatrix} 2 & -1 \\ 1 & 0 \end{bmatrix}$, a Jordan block whose powers grow linearly for every
CFL number, and the state $(u, \Delta t\, v)$ of the Newmark scheme has the Jordan block
$\begin{bmatrix} 1 & 1 \\ 0 & 1 \end{bmatrix}$ there. What both schemes control is the energy
$\|u_t\|^2 + \gamma^2 \|u_x\|^2$ of the wave equation, and that is what this section proves.

Both schemes are stated for an abstract symmetric positive semidefinite operator $A$ on a real inner
product space, which stands for the discretization of $-\gamma^2 \partial_x^2$. The leap-frog energy
is conserved exactly, and it is equivalent to $\|u^{n+1} - u^n\|^2 + \Delta t^2 \langle A u^n, u^n
\rangle$ with the constants $1 \pm \kappa$ whenever $\Delta t^2 \lambda_{\max} \le 4 \kappa^2$. For
the discrete Laplacian, $\lambda_{\max} = 4 \gamma^2 / \Delta x^2$ and
$\kappa = |\gamma| \Delta t / \Delta x$, so this hypothesis with $\kappa < 1$ is the strict CFL
condition. The Newmark energy does not increase for $2\beta \ge \theta \ge 1/2$, with no restriction
on $\Delta t$. The concrete operator on $\ell^2(\mathbb{Z})$ is $-(\gamma^2 / \Delta x^2) \delta^2$,
where $\delta^2$ is the second difference; summation by parts turns its quadratic form into
$(\gamma^2 / \Delta x^2) \|\nabla_h u\|^2$, and this makes it positive semidefinite and bounded by
$4 \gamma^2 / \Delta x^2$.
-/

section SecondOrderEnergy

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →ₗ[ℝ] E} {lmax Δt β θ : ℝ} {u v : ℕ → E}

/-- **Cauchy–Schwarz inequality for a positive semidefinite symmetric operator**, in scaled form.
Let $A$ be a symmetric operator on a real inner product space with $0 \le \langle A x, x \rangle
\le \lambda_{\max} \|x\|^2$ for all $x$. Then for all $t \in \mathbb{R}$ and $x, y$,
$$2 |t| |\langle A x, y \rangle| \le t^2 \langle A x, x \rangle + \langle A y, y \rangle.$$

The proof expands $0 \le \langle A (t x \mp y), t x \mp y \rangle$. Only the lower bound $0$ is
used. -/
theorem two_mul_abs_inner_le (hA : A.IsSymmetricBoundedBy 0 lmax) (t : ℝ) (x y : E) :
    2 * |t| * |⟪A x, y⟫| ≤ t ^ 2 * ⟪A x, x⟫ + ⟪A y, y⟫ := by
  have hpos : ∀ z : E, 0 ≤ ⟪A z, z⟫ := by
    intro z
    have h := hA.le_re_inner z
    simpa using h
  have hsymm : ∀ p q : E, ⟪A p, q⟫ = ⟪A q, p⟫ := by
    intro p q
    rw [hA.isSymmetric p q, real_inner_comm]
  have expand : ∀ s : ℝ, ⟪A (s • x - y), s • x - y⟫
      = s ^ 2 * ⟪A x, x⟫ - 2 * s * ⟪A x, y⟫ + ⟪A y, y⟫ := by
    intro s
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hsymm y x]
    ring
  have h1 := hpos (t • x - y)
  have h2 := hpos ((-t) • x - y)
  rw [expand] at h1
  rw [expand] at h2
  have hkey : |2 * t * ⟪A x, y⟫| ≤ t ^ 2 * ⟪A x, x⟫ + ⟪A y, y⟫ := by
    rw [abs_le]
    constructor <;> nlinarith [h1, h2]
  calc 2 * |t| * |⟪A x, y⟫| = |2 * t * ⟪A x, y⟫| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ _ := hkey

/-! ### Leap-frog -/

/-- The **leap-frog scheme for the abstract wave equation** $u'' + A u = 0$, with $A$ a linear
operator on a real inner product space: the sequence $u^n$ satisfies
$$u^{n+2} - 2 u^{n+1} + u^n = -\Delta t^2 A u^{n+1}$$
for every $n \in \mathbb{N}$. It is the operator form of (13.44) of [quarteroni2000numerical],
which is the case $A = -\gamma^2 \delta^2 / \Delta x^2$
(`FiniteDifference.Hyperbolic.isLeapFrogOp_of_isLeapFrog`). -/
def IsLeapFrogOp (A : E →ₗ[ℝ] E) (Δt : ℝ) (u : ℕ → E) : Prop :=
  ∀ n, u (n + 2) - (2 : ℝ) • u (n + 1) + u n = (-(Δt ^ 2)) • A (u (n + 1))

/-- The **discrete energy of the leap-frog scheme**:
$$E^n = \|u^{n+1} - u^n\|^2 + \Delta t^2 \langle A u^{n+1}, u^n \rangle.$$
Divided by $\Delta t^2$, it is a discretization of the energy
$\|u_t\|^2 + \langle A u, u \rangle$ of the wave equation, with the potential term evaluated at
two consecutive levels. -/
noncomputable def leapFrogEnergy (A : E →ₗ[ℝ] E) (Δt : ℝ) (u : ℕ → E) (n : ℕ) : ℝ :=
  ‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u (n + 1)), u n⟫

/-- The **leap-frog scheme conserves its energy**: if $A$ is symmetric and $u$ satisfies the
leap-frog scheme, then $E^{n+1} = E^n$ for every $n$ and every $\Delta t$. -/
theorem leapFrogEnergy_succ (hA : A.IsSymmetric) (h : IsLeapFrogOp A Δt u) (n : ℕ) :
    leapFrogEnergy A Δt u (n + 1) = leapFrogEnergy A Δt u n := by
  have hsymm : ∀ p q : E, ⟪A p, q⟫ = ⟪A q, p⟫ := fun p q => by
    rw [hA p q, real_inner_comm]
  have hstep : u (n + 2) - (2 : ℝ) • u (n + 1) + u n = (-(Δt ^ 2)) • A (u (n + 1)) := h n
  have hdiff : ‖u (n + 2) - u (n + 1)‖ ^ 2 - ‖u (n + 1) - u n‖ ^ 2
      = ⟪u (n + 2) - u n, u (n + 2) - (2 : ℝ) • u (n + 1) + u n⟫ := by
    simp only [inner_sub_left, inner_add_right, inner_sub_right, real_inner_smul_right,
      @norm_sub_sq_real]
    have e1 : ⟪u n, u (n + 2)⟫ = ⟪u (n + 2), u n⟫ := real_inner_comm _ _
    have e2 : ⟪u (n + 1), u n⟫ = ⟪u n, u (n + 1)⟫ := real_inner_comm _ _
    have e3 : ⟪u (n + 2), u (n + 2)⟫ = ‖u (n + 2)‖ ^ 2 := real_inner_self_eq_norm_sq _
    have e4 : ⟪u n, u n⟫ = ‖u n‖ ^ 2 := real_inner_self_eq_norm_sq _
    linarith
  have hcross : ⟪u (n + 2) - u n, u (n + 2) - (2 : ℝ) • u (n + 1) + u n⟫
      = -(Δt ^ 2 * (⟪A (u (n + 1)), u (n + 2)⟫ - ⟪A (u (n + 1)), u n⟫)) := by
    rw [hstep, real_inner_smul_right, inner_sub_left, real_inner_comm (u (n + 2)),
      real_inner_comm (u n)]
    ring
  have hlast : ⟪A (u (n + 2)), u (n + 1)⟫ = ⟪A (u (n + 1)), u (n + 2)⟫ :=
    hsymm (u (n + 2)) (u (n + 1))
  change ‖u (n + 2) - u (n + 1)‖ ^ 2 + Δt ^ 2 * ⟪A (u (n + 2)), u (n + 1)⟫
    = ‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u (n + 1)), u n⟫
  rw [hcross] at hdiff
  rw [hlast]
  linarith

/-- If $A$ is symmetric and $u$ satisfies the leap-frog scheme, then the leap-frog energy satisfies
$E^n = E^0$ for every $n$. -/
theorem leapFrogEnergy_eq_zero (hA : A.IsSymmetric) (h : IsLeapFrogOp A Δt u) (n : ℕ) :
    leapFrogEnergy A Δt u n = leapFrogEnergy A Δt u 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [leapFrogEnergy_succ hA h k, ih]

/-- The **leap-frog energy is equivalent to the energy of the state**. Let $A$ be symmetric with $0
\le \langle A x, x \rangle \le \lambda_{\max} \|x\|^2$, let $\kappa > 0$ and
$\Delta t^2 \lambda_{\max} \le 4 \kappa^2$. Then for every sequence $u$ and every $n$,
$$\bigl| E^n - (\|u^{n+1} - u^n\|^2 + \Delta t^2 \langle A u^n, u^n \rangle) \bigr| \le \kappa
  \bigl(\|u^{n+1} - u^n\|^2 + \Delta t^2 \langle A u^n, u^n \rangle\bigr).$$

This is where the CFL condition enters. The bound is uniform over all modes, the constant mode
included, and does not need $u$ to satisfy the scheme. -/
theorem abs_leapFrogEnergy_sub_le (hA : A.IsSymmetricBoundedBy 0 lmax) {kap : ℝ} (hkap : 0 < kap)
    (hCFL : Δt ^ 2 * lmax ≤ 4 * kap ^ 2) (u : ℕ → E) (n : ℕ) :
    |leapFrogEnergy A Δt u n - (‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫)|
      ≤ kap * (‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫) := by
  set D := u (n + 1) - u n with hD
  have hexp : leapFrogEnergy A Δt u n - (‖D‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫)
      = Δt ^ 2 * ⟪A D, u n⟫ := by
    have hsplit : A (u (n + 1)) = A D + A (u n) := by rw [hD, map_sub]; abel
    rw [leapFrogEnergy, hsplit, inner_add_left]
    ring
  have hcs := two_mul_abs_inner_le hA (1 / (2 * kap)) D (u n)
  have hbd : ⟪A D, D⟫ ≤ lmax * ‖D‖ ^ 2 := by simpa using hA.re_inner_le D
  have hDt : (0 : ℝ) ≤ Δt ^ 2 := sq_nonneg _
  have habs : (0 : ℝ) < 1 / (2 * kap) := by positivity
  rw [abs_of_pos habs] at hcs
  have hkey : Δt ^ 2 * |⟪A D, u n⟫| ≤ kap * (‖D‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫) := by
    have h1 : |⟪A D, u n⟫| ≤ 1 / (4 * kap) * ⟪A D, D⟫ + kap * ⟪A (u n), u n⟫ := by
      have h2 : 2 * (1 / (2 * kap)) = 1 / kap := by field_simp
      rw [h2] at hcs
      have h3 : 1 / kap * |⟪A D, u n⟫| ≤ (1 / (2 * kap)) ^ 2 * ⟪A D, D⟫ + ⟪A (u n), u n⟫ := hcs
      have h4 : (1 / (2 * kap)) ^ 2 = 1 / (4 * kap ^ 2) := by field_simp; ring
      rw [h4] at h3
      have h5 := mul_le_mul_of_nonneg_left h3 hkap.le
      calc |⟪A D, u n⟫| = kap * (1 / kap * |⟪A D, u n⟫|) := by field_simp
        _ ≤ kap * (1 / (4 * kap ^ 2) * ⟪A D, D⟫ + ⟪A (u n), u n⟫) := h5
        _ = 1 / (4 * kap) * ⟪A D, D⟫ + kap * ⟪A (u n), u n⟫ := by field_simp
    have h5 : Δt ^ 2 * (1 / (4 * kap) * ⟪A D, D⟫) ≤ kap * ‖D‖ ^ 2 := by
      have h6 : Δt ^ 2 * ⟪A D, D⟫ ≤ Δt ^ 2 * (lmax * ‖D‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbd hDt
      have h7 : Δt ^ 2 * (lmax * ‖D‖ ^ 2) ≤ 4 * kap ^ 2 * ‖D‖ ^ 2 := by nlinarith
      have h8 : Δt ^ 2 * (1 / (4 * kap) * ⟪A D, D⟫) = 1 / (4 * kap) * (Δt ^ 2 * ⟪A D, D⟫) := by
        ring
      have h9 : (0 : ℝ) < 1 / (4 * kap) := by positivity
      rw [h8]
      calc 1 / (4 * kap) * (Δt ^ 2 * ⟪A D, D⟫)
          ≤ 1 / (4 * kap) * (4 * kap ^ 2 * ‖D‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (h6.trans h7) h9.le
        _ = kap * ‖D‖ ^ 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hDt]
  rw [hexp, abs_mul, abs_of_nonneg hDt]
  exact hkey

/-- **Energy stability of the leap-frog scheme**. Let $A$ be symmetric with $0 \le \langle A x, x
\rangle \le \lambda_{\max} \|x\|^2$, let $0 < \kappa < 1$ and
$\Delta t^2 \lambda_{\max} \le 4 \kappa^2$ (the strict CFL condition), and let $u$ satisfy the
leap-frog scheme. Then for every $n$,
$$\|u^{n+1} - u^n\|^2 + \Delta t^2 \langle A u^n, u^n \rangle \le \frac{1 + \kappa}{1 - \kappa}
  \bigl(\|u^1 - u^0\|^2 + \Delta t^2 \langle A u^0, u^0 \rangle\bigr).$$
No time horizon is needed. This is the stability of the leap-frog scheme in Remark 13.4 of
[quarteroni2000numerical], stated for the energy. -/
theorem leapFrog_stability (hA : A.IsSymmetricBoundedBy 0 lmax) {kap : ℝ} (hkap : 0 < kap)
    (hkap1 : kap < 1) (hCFL : Δt ^ 2 * lmax ≤ 4 * kap ^ 2) (h : IsLeapFrogOp A Δt u) (n : ℕ) :
    ‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫
      ≤ (1 + kap) / (1 - kap) * (‖u 1 - u 0‖ ^ 2 + Δt ^ 2 * ⟪A (u 0), u 0⟫) := by
  have hn := abs_leapFrogEnergy_sub_le hA hkap hCFL u n
  have h0 := abs_leapFrogEnergy_sub_le hA hkap hCFL u 0
  have hE := leapFrogEnergy_eq_zero hA.isSymmetric h n
  rw [abs_le] at hn h0
  have h1 : (0 : ℝ) < 1 - kap := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  have e1 : u (0 + 1) = u 1 := rfl
  rw [e1] at h0
  nlinarith [hn.1, hn.2, h0.1, h0.2, hE]

/-! ### Newmark -/

/-- The **Newmark scheme for the abstract wave equation** $u'' + A u = 0$, with the parameters
$\beta$ and $\theta$ and the auxiliary velocity $v$: for every $n \in \mathbb{N}$,
$$u^{n+1} - u^n = \Delta t\, v^n - \Delta t^2 \bigl(\beta A u^{n+1} + (\tfrac{1}{2} - \beta) A
  u^n\bigr),$$
$$v^{n+1} - v^n = -\Delta t \bigl(\theta A u^{n+1} + (1 - \theta) A u^n\bigr).$$
It is the operator form of (13.45) of [quarteroni2000numerical], which is the case
$A = -\gamma^2 \delta^2 / \Delta x^2$ (`FiniteDifference.Hyperbolic.isNewmarkOp_of_isNewmark`). -/
def IsNewmarkOp (A : E →ₗ[ℝ] E) (Δt β θ : ℝ) (u v : ℕ → E) : Prop :=
  ∀ n, u (n + 1) - u n
        = Δt • v n - (Δt ^ 2) • (β • A (u (n + 1)) + (1 / 2 - β) • A (u n)) ∧
      v (n + 1) - v n = (-Δt) • (θ • A (u (n + 1)) + (1 - θ) • A (u n))

/-- The **discrete energy of the Newmark scheme**:
$$E^n = \|v^n\|^2 + \langle A u^n, u^n \rangle + \frac{\Delta t^2 (2\beta - \theta)}{2} \|A
  u^n\|^2,$$
the kinetic and the potential energy plus a term that the parameters of the method add. For
$\theta = 2\beta$ it is exactly $\|v^n\|^2 + \langle A u^n, u^n \rangle$. -/
noncomputable def newmarkEnergy (A : E →ₗ[ℝ] E) (Δt β θ : ℝ) (u v : ℕ → E) (n : ℕ) : ℝ :=
  ‖v n‖ ^ 2 + ⟪A (u n), u n⟫ + Δt ^ 2 * (2 * β - θ) / 2 * ‖A (u n)‖ ^ 2

/-- The **energy identity of the Newmark scheme**. Let $A$ be symmetric and let $(u, v)$ satisfy the
Newmark scheme. With $D = u^{n+1} - u^n$,
$$E^{n+1} - E^n = -(2\theta - 1) \langle A D, D \rangle - \Delta t^2 (2\beta - \theta)(\theta -
  \tfrac{1}{2}) \|A D\|^2.$$
There is no condition on $\Delta t$, $\beta$ or $\theta$. -/
theorem newmarkEnergy_succ_sub (hA : A.IsSymmetric) (h : IsNewmarkOp A Δt β θ u v) (n : ℕ) :
    newmarkEnergy A Δt β θ u v (n + 1) - newmarkEnergy A Δt β θ u v n
      = -(2 * θ - 1) * ⟪A (u (n + 1) - u n), u (n + 1) - u n⟫
        - Δt ^ 2 * (2 * β - θ) * (θ - 1 / 2) * ‖A (u (n + 1) - u n)‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := h n
  have hAD : A (u (n + 1) - u n) = A (u (n + 1)) - A (u n) := map_sub _ _ _
  have hw : θ • A (u (n + 1)) + (1 - θ) • A (u n) = A (θ • u (n + 1) + (1 - θ) • u n) := by
    simp [map_add, map_smul]
  have e2 : Δt • v n = (u (n + 1) - u n)
      + (Δt ^ 2) • (β • A (u (n + 1)) + (1 / 2 - β) • A (u n)) := by
    rw [h1]; abel
  have hsum : Δt • (v (n + 1) + v n) = (2 : ℝ) • (u (n + 1) - u n)
      + (Δt ^ 2 * (2 * β - θ)) • (A (u (n + 1)) - A (u n)) := by
    have e : v (n + 1) + v n = (v (n + 1) - v n) + (v n + v n) := by abel
    rw [e, smul_add, smul_add, h2, e2, smul_smul]
    module
  have hvel : ‖v (n + 1)‖ ^ 2 - ‖v n‖ ^ 2 = ⟪v (n + 1) - v n, v (n + 1) + v n⟫ := by
    simp only [inner_sub_left, inner_add_right]
    have f1 : ⟪v (n + 1), v (n + 1)⟫ = ‖v (n + 1)‖ ^ 2 := real_inner_self_eq_norm_sq _
    have f2 : ⟪v n, v n⟫ = ‖v n‖ ^ 2 := real_inner_self_eq_norm_sq _
    have f3 : ⟪v n, v (n + 1)⟫ = ⟪v (n + 1), v n⟫ := real_inner_comm _ _
    linarith
  have hA1 : ⟪A (θ • u (n + 1) + (1 - θ) • u n), Δt • (v (n + 1) + v n)⟫
      = 2 * ⟪A (θ • u (n + 1) + (1 - θ) • u n), u (n + 1) - u n⟫
        + Δt ^ 2 * (2 * β - θ)
          * ⟪A (θ • u (n + 1) + (1 - θ) • u n), A (u (n + 1)) - A (u n)⟫ := by
    rw [hsum, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [real_inner_smul_right] at hA1
  have hkey : ‖v (n + 1)‖ ^ 2 - ‖v n‖ ^ 2
      = -(2 * ⟪A (θ • u (n + 1) + (1 - θ) • u n), u (n + 1) - u n⟫)
        - Δt ^ 2 * (2 * β - θ)
          * ⟪A (θ • u (n + 1) + (1 - θ) • u n), A (u (n + 1)) - A (u n)⟫ := by
    rw [hvel, h2, hw, real_inner_smul_left]
    linear_combination -hA1
  have hsq : ⟪A (u (n + 1)), u n⟫ = ⟪A (u n), u (n + 1)⟫ := by
    rw [hA (u (n + 1)) (u n), real_inner_comm]
  have hpq : ⟪A (u (n + 1)), A (u n)⟫ = ⟪A (u n), A (u (n + 1))⟫ := real_inner_comm _ _
  have e1 : ⟪A (θ • u (n + 1) + (1 - θ) • u n), u (n + 1) - u n⟫
      = θ * ⟪A (u (n + 1)), u (n + 1)⟫ - (2 * θ - 1) * ⟪A (u n), u (n + 1)⟫
        - (1 - θ) * ⟪A (u n), u n⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_sub_right, real_inner_smul_left]
    rw [hsq]
    ring
  have e5 : ⟪A (θ • u (n + 1) + (1 - θ) • u n), A (u (n + 1)) - A (u n)⟫
      = θ * ⟪A (u (n + 1)), A (u (n + 1))⟫ - (2 * θ - 1) * ⟪A (u n), A (u (n + 1))⟫
        - (1 - θ) * ⟪A (u n), A (u n)⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_sub_right, real_inner_smul_left]
    rw [hpq]
    ring
  have e3 : ⟪A (u (n + 1) - u n), u (n + 1) - u n⟫
      = ⟪A (u (n + 1)), u (n + 1)⟫ - 2 * ⟪A (u n), u (n + 1)⟫ + ⟪A (u n), u n⟫ := by
    rw [hAD, inner_sub_left, inner_sub_right, inner_sub_right, hsq]
    ring
  have e4 : ‖A (u (n + 1) - u n)‖ ^ 2 = ⟪A (u (n + 1)), A (u (n + 1))⟫
      - 2 * ⟪A (u n), A (u (n + 1))⟫ + ⟪A (u n), A (u n)⟫ := by
    rw [← real_inner_self_eq_norm_sq, hAD, inner_sub_left, inner_sub_right, inner_sub_right, hpq]
    ring
  have hnq : ‖A (u (n + 1))‖ ^ 2 = ⟪A (u (n + 1)), A (u (n + 1))⟫ :=
    (real_inner_self_eq_norm_sq _).symm
  have hnp : ‖A (u n)‖ ^ 2 = ⟪A (u n), A (u n)⟫ := (real_inner_self_eq_norm_sq _).symm
  rw [e1, e5] at hkey
  simp only [newmarkEnergy]
  rw [e3, e4, hnq, hnp]
  linear_combination hkey

/-- The **Newmark energy does not increase when $2\beta \ge \theta \ge 1/2$**. Let $A$ be symmetric
with $0 \le \langle A x, x \rangle \le \lambda_{\max} \|x\|^2$, let $1/2 \le \theta \le 2\beta$,
and let $(u, v)$ satisfy the Newmark scheme. Then $E^{n+1} \le E^n$ for every $n$ and every
$\Delta t$. This is the unconditional stability in Remark 13.4 of [quarteroni2000numerical]. -/
theorem newmarkEnergy_succ_le (hA : A.IsSymmetricBoundedBy 0 lmax) (hth : 1 / 2 ≤ θ)
    (hbt : θ ≤ 2 * β) (h : IsNewmarkOp A Δt β θ u v) (n : ℕ) :
    newmarkEnergy A Δt β θ u v (n + 1) ≤ newmarkEnergy A Δt β θ u v n := by
  have hid := newmarkEnergy_succ_sub hA.isSymmetric h n
  have hpos : 0 ≤ ⟪A (u (n + 1) - u n), u (n + 1) - u n⟫ := by
    simpa using hA.le_re_inner (u (n + 1) - u n)
  have h1 : 0 ≤ (2 * θ - 1) * ⟪A (u (n + 1) - u n), u (n + 1) - u n⟫ :=
    mul_nonneg (by linarith) hpos
  have h2 : 0 ≤ Δt ^ 2 * (2 * β - θ) * (θ - 1 / 2) * ‖A (u (n + 1) - u n)‖ ^ 2 := by
    positivity
  linarith

/-- Let $A$ be symmetric with $0 \le \langle A x, x \rangle \le \lambda_{\max} \|x\|^2$, let
$1/2 \le \theta \le 2\beta$, and let $(u, v)$ satisfy the Newmark scheme. Then the Newmark
energy satisfies $E^n \le E^0$ for every $n$. -/
theorem newmarkEnergy_le (hA : A.IsSymmetricBoundedBy 0 lmax) (hth : 1 / 2 ≤ θ)
    (hbt : θ ≤ 2 * β) (h : IsNewmarkOp A Δt β θ u v) (n : ℕ) :
    newmarkEnergy A Δt β θ u v n ≤ newmarkEnergy A Δt β θ u v 0 := by
  induction n with
  | zero => exact le_refl _
  | succ k ih => exact (newmarkEnergy_succ_le hA hth hbt h k).trans ih

/-- **Unconditional stability of the Newmark scheme**. Let $A$ be symmetric with $0 \le \langle A x,
x \rangle \le \lambda_{\max} \|x\|^2$, let $1/2 \le \theta \le 2\beta$, and let $(u, v)$ satisfy
the Newmark scheme. Then for every $n$ and every $\Delta t$,
$$\|v^n\|^2 + \langle A u^n, u^n \rangle \le \|v^0\|^2 + \langle A u^0, u^0 \rangle +
  \frac{\Delta t^2 (2\beta - \theta)}{2} \|A u^0\|^2.$$
This is the unconditional stability in Remark 13.4 of [quarteroni2000numerical], stated for the
energy. -/
theorem newmark_stability (hA : A.IsSymmetricBoundedBy 0 lmax) (hth : 1 / 2 ≤ θ)
    (hbt : θ ≤ 2 * β) (h : IsNewmarkOp A Δt β θ u v) (n : ℕ) :
    ‖v n‖ ^ 2 + ⟪A (u n), u n⟫
      ≤ ‖v 0‖ ^ 2 + ⟪A (u 0), u 0⟫ + Δt ^ 2 * (2 * β - θ) / 2 * ‖A (u 0)‖ ^ 2 := by
  have hmono := newmarkEnergy_le hA hth hbt h n
  have hextra : 0 ≤ Δt ^ 2 * (2 * β - θ) / 2 * ‖A (u n)‖ ^ 2 := by
    positivity
  simp only [newmarkEnergy] at hmono
  linarith

/-! ### The discrete wave operator on $\ell^2(\mathbb{Z})$ -/

/-- The **forward difference** $(\nabla_h u)_j = u_{j+1} - u_j$, as a bounded operator on
$\ell^2(\mathbb{Z})$. -/
noncomputable def forwardDiffCLM : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  Stencil.lpCLM (Stencil.threePoint 0 (-1) 1) 2

/-- The forward difference acts by $(\nabla_h u)_j = u_{j+1} - u_j$. -/
theorem forwardDiffCLM_apply (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    forwardDiffCLM u j = u (j + 1) - u j := by
  rw [forwardDiffCLM, Stencil.lpCLM_apply, Stencil.threePoint_apply]
  simp only [smul_eq_mul, neg_mul, one_mul, zero_mul]
  ring

/-- The **second difference** $(\delta^2 u)_j = u_{j+1} - 2 u_j + u_{j-1}$, as a bounded operator on
$\ell^2(\mathbb{Z})$. It is the space operator of the leap-frog and Newmark schemes. -/
noncomputable def secondDiffCLM : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  Stencil.lpCLM (Stencil.threePoint 1 (-2) 1) 2

/-- The second difference acts by $(\delta^2 u)_j = u_{j+1} - 2 u_j + u_{j-1}$. -/
theorem secondDiffCLM_apply (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    secondDiffCLM u j = u (j + 1) - 2 * u j + u (j - 1) := by
  rw [secondDiffCLM, Stencil.lpCLM_apply, Stencil.threePoint_apply]
  simp only [smul_eq_mul, neg_mul, one_mul]
  ring

/-- The forward difference is $\nabla_h = S_{-1} - 1$, where $(S_s u)_j = u_{j-s}$. -/
private theorem forwardDiffCLM_eq_sub (u : lp (fun _ : ℤ => ℝ) 2) :
    forwardDiffCLM u = lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-1) u - u := by
  refine lp.ext (funext fun j => ?_)
  rw [lp.coeFn_sub]
  simp [forwardDiffCLM_apply, sub_neg_eq_add]

/-- The second difference is $\delta^2 = S_{-1} - 2 + S_1$, where $(S_s u)_j = u_{j-s}$. -/
private theorem secondDiffCLM_eq_sub (u : lp (fun _ : ℤ => ℝ) 2) :
    secondDiffCLM u
      = lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-1) u - (2 : ℝ) • u
        + lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 1 u := by
  refine lp.ext (funext fun j => ?_)
  rw [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul]
  simp [secondDiffCLM_apply, sub_neg_eq_add]

/-- **Summation by parts** on $\ell^2(\mathbb{Z})$: $\langle \nabla_h u, \nabla_h w \rangle =
-\langle \delta^2 u, w \rangle$ for all $u, w$. -/
theorem inner_forwardDiffCLM (u w : lp (fun _ : ℤ => ℝ) 2) :
    ⟪forwardDiffCLM u, forwardDiffCLM w⟫ = -⟪secondDiffCLM u, w⟫ := by
  rw [forwardDiffCLM_eq_sub u, forwardDiffCLM_eq_sub w, secondDiffCLM_eq_sub u]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_add_left, inner_sub_left,
    inner_shift_left, inner_shift_left, inner_shift_left, real_inner_smul_left]
  rw [shift_shift, show (- -1 + -1 : ℤ) = 0 by norm_num, shift_zero]
  ring

/-- The **discrete wave operator** $-(\gamma^2 / \Delta x^2) \delta^2$ on $\ell^2(\mathbb{Z})$: the
space operator of the wave equation $u_{tt} = \gamma^2 u_{xx}$, discretized by centred
differences, in (13.44)–(13.45) of [quarteroni2000numerical]. -/
noncomputable def discreteWaveOp (γ Δx : ℝ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  (-(γ ^ 2 / Δx ^ 2)) • secondDiffCLM

/-- The discrete wave operator acts by $u \mapsto -(\gamma^2 / \Delta x^2)(u_{j+1} - 2 u_j +
u_{j-1})$. -/
theorem discreteWaveOp_apply (γ Δx : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    discreteWaveOp γ Δx u j = -(γ ^ 2 / Δx ^ 2) * (u (j + 1) - 2 * u j + u (j - 1)) := by
  have h : discreteWaveOp γ Δx u = (-(γ ^ 2 / Δx ^ 2)) • secondDiffCLM u := rfl
  rw [h, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, secondDiffCLM_apply]

/-- The bilinear form of the discrete wave operator is the discrete Dirichlet form: $\langle A u, w
\rangle = (\gamma^2 / \Delta x^2) \langle \nabla_h u, \nabla_h w \rangle$, where
$A = -(\gamma^2 / \Delta x^2) \delta^2$. -/
theorem inner_discreteWaveOp (γ Δx : ℝ) (u w : lp (fun _ : ℤ => ℝ) 2) :
    ⟪discreteWaveOp γ Δx u, w⟫ = γ ^ 2 / Δx ^ 2 * ⟪forwardDiffCLM u, forwardDiffCLM w⟫ := by
  have h : discreteWaveOp γ Δx u = (-(γ ^ 2 / Δx ^ 2)) • secondDiffCLM u := rfl
  rw [h, real_inner_smul_left, inner_forwardDiffCLM]
  ring

/-- The quadratic form of the discrete wave operator $A$ is $\langle A u, u \rangle = (\gamma^2 /
\Delta x^2) \|\nabla_h u\|^2$, the discrete form of $\gamma^2 \int u_x^2$. -/
theorem inner_discreteWaveOp_self (γ Δx : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) :
    ⟪discreteWaveOp γ Δx u, u⟫ = γ ^ 2 / Δx ^ 2 * ‖forwardDiffCLM u‖ ^ 2 := by
  rw [inner_discreteWaveOp, real_inner_self_eq_norm_sq]

/-- The forward difference satisfies $\|\nabla_h u\| \le 2 \|u\|$ on $\ell^2(\mathbb{Z})$. -/
theorem norm_forwardDiffCLM_le (u : lp (fun _ : ℤ => ℝ) 2) :
    ‖forwardDiffCLM u‖ ≤ 2 * ‖u‖ := by
  rw [forwardDiffCLM_eq_sub]
  refine (norm_sub_le _ _).trans ?_
  rw [(lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-1)).norm_map]
  ring_nf
  exact le_refl _

/-- The **discrete wave operator is symmetric and positive semidefinite, with quadratic form bounded
by $4 \gamma^2 / \Delta x^2$**: $A = -(\gamma^2 / \Delta x^2) \delta^2$ satisfies
$$0 \le \langle A u, u \rangle \le \frac{4 \gamma^2}{\Delta x^2} \|u\|^2.$$
This is the discrete counterpart of $0 \le -\gamma^2 \partial_x^2 \le 4 \gamma^2 / \Delta x^2$,
and the source of the constant in the CFL condition. -/
theorem discreteWaveOp_isSymmetricBoundedBy (γ Δx : ℝ) :
    ((discreteWaveOp γ Δx : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2) :
      lp (fun _ : ℤ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℤ => ℝ) 2).IsSymmetricBoundedBy 0
      (4 * γ ^ 2 / Δx ^ 2) := by
  have hc : (0 : ℝ) ≤ γ ^ 2 / Δx ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    change ⟪discreteWaveOp γ Δx x, y⟫ = ⟪x, discreteWaveOp γ Δx y⟫
    have h1 : ⟪x, discreteWaveOp γ Δx y⟫ = ⟪discreteWaveOp γ Δx y, x⟫ := real_inner_comm _ _
    have h2 : ⟪forwardDiffCLM y, forwardDiffCLM x⟫ = ⟪forwardDiffCLM x, forwardDiffCLM y⟫ :=
      real_inner_comm _ _
    rw [h1, inner_discreteWaveOp, inner_discreteWaveOp, h2]
  · intro x
    change 0 * ‖x‖ ^ 2 ≤ RCLike.re (inner ℝ (discreteWaveOp γ Δx x) x)
    simp only [RCLike.re_to_real, zero_mul]
    rw [inner_discreteWaveOp_self]
    positivity
  · intro x
    change RCLike.re (inner ℝ (discreteWaveOp γ Δx x) x) ≤ _
    simp only [RCLike.re_to_real]
    rw [inner_discreteWaveOp_self]
    have h1 : ‖forwardDiffCLM x‖ ^ 2 ≤ (2 * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_forwardDiffCLM_le x) 2
    calc γ ^ 2 / Δx ^ 2 * ‖forwardDiffCLM x‖ ^ 2
        ≤ γ ^ 2 / Δx ^ 2 * (2 * ‖x‖) ^ 2 := mul_le_mul_of_nonneg_left h1 hc
      _ = 4 * γ ^ 2 / Δx ^ 2 * ‖x‖ ^ 2 := by ring

/-- The **leap-frog scheme (13.44) is the operator scheme of the discrete wave operator**. Let
$\Delta x \neq 0$, $\lambda = \Delta t / \Delta x$, and let $u^n \in \ell^2(\mathbb{Z})$ satisfy
the leap-frog scheme (`FiniteDifference.Hyperbolic.IsLeapFrog`). Then $u$ satisfies the abstract
leap-frog scheme (`FiniteDifference.Hyperbolic.IsLeapFrogOp`) for
$A = -(\gamma^2 / \Delta x^2) \delta^2$. -/
theorem isLeapFrogOp_of_isLeapFrog {γ lam Δt Δx : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx)
    {u : ℕ → lp (fun _ : ℤ => ℝ) 2} (h : IsLeapFrog γ lam fun n => ⇑(u n)) :
    IsLeapFrogOp
      ((discreteWaveOp γ Δx : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2) :
        lp (fun _ : ℤ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℤ => ℝ) 2) Δt u := by
  intro n
  refine lp.ext (funext fun j => ?_)
  have hstep := h n j
  simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_coe, discreteWaveOp_apply]
  rw [hstep, hlam]
  field_simp

/-- The **Newmark scheme (13.45) is the operator scheme of the discrete wave operator**. Let
$\Delta t \neq 0$, $\Delta x \neq 0$, $\lambda = \Delta t / \Delta x$, and let
$u^n, v^n \in \ell^2(\mathbb{Z})$ satisfy the Newmark scheme
(`FiniteDifference.Hyperbolic.IsNewmark`). Then $(u, v)$ satisfies the abstract Newmark scheme
(`FiniteDifference.Hyperbolic.IsNewmarkOp`) for $A = -(\gamma^2 / \Delta x^2) \delta^2$. -/
theorem isNewmarkOp_of_isNewmark {γ lam Δt Δx β θ : ℝ} (hΔt : Δt ≠ 0) (hΔx : Δx ≠ 0)
    (hlam : lam = Δt / Δx) {u v : ℕ → lp (fun _ : ℤ => ℝ) 2}
    (h : IsNewmark γ lam Δt β θ (fun n => ⇑(u n)) fun n => ⇑(v n)) :
    IsNewmarkOp
      ((discreteWaveOp γ Δx : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2) :
        lp (fun _ : ℤ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℤ => ℝ) 2) Δt β θ u v := by
  intro n
  constructor
  · refine lp.ext (funext fun j => ?_)
    have hstep := (h n j).1
    simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe, discreteWaveOp_apply]
    rw [hstep, hlam]
    field_simp
    ring
  · refine lp.ext (funext fun j => ?_)
    have hstep := (h n j).2
    simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe, discreteWaveOp_apply]
    rw [hstep, hlam]
    field_simp
    ring

end SecondOrderEnergy

end Hyperbolic

end FiniteDifference
