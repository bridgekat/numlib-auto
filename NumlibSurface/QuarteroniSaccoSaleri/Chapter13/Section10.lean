/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Transport
import Numlib.Variational.EllipticInterval
import Numlib.Variational.Evolution
import Numlib.Variational.SpaceTimeGalerkin

/-!
# Quarteroni, Sacco and Saleri, Section 13.10: Finite elements for hyperbolic equations

This module formalizes §13.10 of [quarteroni2000numerical] and Exercises 13.9 and 13.10, on finite
element methods for the scalar transport problem (13.64)
$$u_t + a u_x + a_0 u = f \quad \text{in } Q_T = (\alpha, \beta) \times (0, T), \qquad
  u(\alpha, t) = \varphi(t), \qquad u(x, 0) = u_0(x),$$
with $a = a(x) > 0$, so that $x = \alpha$ is the inflow boundary. Section 13.10.1 studies two
semi-discretizations in space on the piecewise polynomials of degree at most $r$ on a partition
$\alpha = x_0 < \dots < x_n = \beta$, with the $L^2(\alpha, \beta)$ inner product. The continuous
Galerkin method (13.65) uses the continuous piecewise polynomials $V_h = X_h^r$, the test space
$V_h^{in}$ of those that vanish at $\alpha$, and the form $b_t(u, v) = \sum_j \int_{I_j} (a u' +
a_0(\cdot, t) u) v$. The discontinuous Galerkin method (13.68) uses all piecewise polynomials
$W_h = Y_h^r$ and the upwind form $b_t^{DG}(u, v) = b_t(u, v) + \sum_j a(x_j) [u]_j v^+(x_j)$.
Section 13.10.2 discretizes (13.65) in time by the backward Euler method (13.70).

All stability estimates come from the energy identity
$$b_t^{DG}(v, v) = \tfrac12 a(\beta) v^-(\beta)^2 + \tfrac12 \sum_j a(x_j) [v]_j^2 +
  \int_\alpha^\beta \bigl(a_0(\cdot, t) - \tfrac12 a'\bigr) v^2$$
and the corresponding identity for $b_t$ on $V_h$. With a lower bound $\mu_0 \le a_0 - a'/2$, they
give (13.66) and (13.69) when $\mu_0 > 0$, Exercise 13.10 for any $\mu_0$, and the unconditional
stability of (13.70) when $\mu_0 \ge 0$. With a bound $\mu^*(t)$ on $|a_0 - a'/2|$, they give
(13.67), with no sign condition. The source quotes the convergence rates $O(h^r)$ for continuous and
$O(h^{r+1/2})$ for discontinuous elements from [quarteroni1994numerical] without proof; here they
are proved with explicit constants. The proofs specialize `Numlib.Analysis.PDE.Transport`,
`Numlib.Variational.Evolution` and `Numlib.Variational.SpaceTimeGalerkin`.

## Main definitions

* Equation (13.64), `QuarteroniSaccoSaleri.Chapter13.equation_13_64`: the classical solutions of the
  transport problem.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.inflowSpace`: the test space $V_h^{in}$ of
  continuous piecewise polynomials that vanish at $\alpha$.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.transportForm`: the form $b_t(u, v) = \sum_j
  \int_{I_j} (a u' + a_0(\cdot, t) u) v$.
* Equation (13.65), `QuarteroniSaccoSaleri.Chapter13.equation_13_65`: the continuous Galerkin
  semi-discretization with $\varphi = 0$.
* Equation (13.68), `QuarteroniSaccoSaleri.Chapter13.equation_13_68`: the discontinuous Galerkin
  semi-discretization with the upwind form.
* Equation (13.70), `QuarteroniSaccoSaleri.Chapter13.equation_13_70`: one backward Euler step for
  (13.65).

## Main results

* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.transportForm_apply_self`: the energy identity
  $b_t(v, v) = \frac12 a(\beta) v(\beta)^2 - \frac12 a(\alpha) v(\alpha)^2 + \int_\alpha^\beta
  (a_0 - a'/2) v^2$ on $V_h$.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.le_transportForm_restrict`: if
  $c \le a_0 - a'/2$, then $c \|v\|^2 + \frac12 a(\beta) v(\beta)^2 \le b_t(v, v)$ on $V_h^{in}$.
* Equation (13.66), `QuarteroniSaccoSaleri.Chapter13.equation_13_66`: the stability estimate of the
  continuous Galerkin method under $0 < \mu_0 \le a_0 - a'/2$.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.equation_13_66_conservation`: for $f = 0$ and
  $a_0 - a'/2 \ge 0$, the norm $\|u_h(t)\|$ is nonincreasing.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.equation_13_66_conservation_le`: under the same
  conditions, $\|u_h(t)\| \le \|u_{0,h}\|$.
* Equation (13.67), `QuarteroniSaccoSaleri.Chapter13.equation_13_67`: the stability estimate of the
  continuous Galerkin method with an exponential factor, without a sign condition on $a_0 - a'/2$.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.dgUpwindForm_apply_self`: the energy identity of
  the upwind form on $W_h$.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.le_dgUpwindForm`: if $c \le a_0 - a'/2$, then $c
  \|v\|^2 + \frac12 a(\beta) v^-(\beta)^2 + \frac12 \sum_j a(x_j) [v]_j^2 \le b_t^{DG}(v, v)$.
* Equation (13.69), `QuarteroniSaccoSaleri.Chapter13.equation_13_69`: the stability estimate of the
  discontinuous Galerkin method.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.cG_convergence`: the error of continuous
  elements of degree $r$ is $O(\|u_0 - u_{0,h}\| + h^r)$.
* Section 13.10.1, `QuarteroniSaccoSaleri.Chapter13.dG_convergence`: the error of discontinuous
  elements of degree $r$ is $O(\|u_0 - u_{0,h}\| + h^{r+1/2})$.
* Section 13.10.2, `QuarteroniSaccoSaleri.Chapter13.equation_13_70_stability`: one step of (13.70)
  is stable for every $\Delta t > 0$.
* Section 13.10.2, `QuarteroniSaccoSaleri.Chapter13.equation_13_70_sum`: the stability estimate of
  (13.70) summed over the steps.
* Section 13.10.2, `QuarteroniSaccoSaleri.Chapter13.equation_13_70_norm_le`: the iterates of (13.70)
  satisfy $\|u_h^m\| \le \|u_h^0\|$.
* Exercise 13.9, `QuarteroniSaccoSaleri.Chapter13.exercise_13_9`: the estimate (13.67).
* Exercise 13.10, `QuarteroniSaccoSaleri.Chapter13.exercise_13_10`: the estimate (13.69) for $f = 0$
  and $\varphi = 0$.

## Conventions

* The partition is a strictly increasing map `x : Fin (n + 1) → ℝ`, given by the instance
  `Fact (StrictMono x)`. The left end of the interval is `x 0` and the right end is
  `x (Fin.last n)`. The condition that there is at least one panel is the hypothesis `hn : 0 < n`.
* The space of piecewise polynomials of degree at most $r$ is `BrokenPolynomial x r`, with the
  $L^2(\alpha, \beta)$ inner product. The space $V_h = X_h^r$ is `BrokenPolynomial.continuous x r`.
* The value $v^+(x_j)$ from the panel to the right of $x_j$ is `BrokenPolynomial.traceRight v j`,
  and the value $v^-(x_j)$ from the panel to the left is `BrokenPolynomial.traceLeft v j`, with the
  convention $v^-(x_0) = 0$. The jump $[v]_j = v^+(x_j) - v^-(x_j)$ is `BrokenPolynomial.jump v j`,
  so that $[v]_0 = v^+(\alpha)$.
* The coefficients are functions `a : ℝ → ℝ` and `a₀ : ℝ → ℝ → ℝ`, with `a₀ s t` for $a_0(x, t)$.
  Interval integrability on $[\alpha, \beta]$ is the hypothesis that makes the forms bounded and
  bilinear. Where the integration by parts needs it, $a$ is differentiable on $[\alpha, \beta]$ with
  a continuous derivative.

## Implementation notes

* The source $f(t)$ is an element of the discrete space, so that `‖f t‖` is its $L^2(\alpha, \beta)$
  norm. A general $f(t) \in L^2(\alpha, \beta)$ enters (13.65) and (13.68) only through its $L^2$
  projection, whose norm is at most $\|f(t)\|_{L^2}$, so the estimates are those of the source.
* Both semi-discretizations are `Variational.IsSemidiscreteGalerkin`, and (13.70) is
  `Variational.IsThetaStep` with $\theta = 1$.
* In (13.68) the inflow value $U_h^-(x_0, t) = \varphi(t)$ of the source is moved to the right-hand
  side as the term $a(\alpha) \varphi(t) v^+(\alpha)$, and the form uses the convention
  $u^-(x_0) = 0$.
* The convergence estimates take the regularity of the exact solution as hypotheses:
  $u(\cdot, t) \in H^{r+1}(\alpha, \beta)$ uniformly in $t$, and for continuous elements also
  $\partial_t u(\cdot, t)$.

## Deviations from the source

* **Equations (13.64)–(13.65)** (reading). The classical problem uses the closed rectangle,
  requires corner compatibility, and permits any advection coefficient. The continuous Galerkin
  problem covers homogeneous inflow with a piecewise polynomial representative of the load. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_64` and
  `QuarteroniSaccoSaleri.Chapter13.equation_13_65`.
* **Equation (13.68)** (reading). The discontinuous problem retains the time dependence of the
  reaction coefficient and writes the inflow term on the load side. It uses a piecewise
  polynomial volume-load representative. See `QuarteroniSaccoSaleri.Chapter13.equation_13_68`.
* **Equation (13.70)** (specialization). The one-step equation covers homogeneous inflow with
  initial data passed separately. The norm estimate assumes explicit nonnegative bulk and
  outflow dissipation. See `QuarteroniSaccoSaleri.Chapter13.equation_13_70_norm_le`.
* **(13.66) and (13.67)** (reading). The source prints the boundary term as
  $a(\beta) \int_0^t u_h^2(\tau) \, d\tau$; it is read as
  $a(\beta) \int_0^t u_h(\beta, \tau)^2 \, d\tau$. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_66` and
  `QuarteroniSaccoSaleri.Chapter13.equation_13_67`.
* **Conservation of the energy after (13.66)** (correction). The source asks for $f = a_0 = 0$, but
  the energy identity then also needs $a' \le 0$; the statement asks for $f = 0$ and
  $a_0 - a'/2 \ge 0$. See `QuarteroniSaccoSaleri.Chapter13.equation_13_66_conservation`.
* **(13.69)** (reading). The source has an unspecified constant $C$ and the jump sum from $j = 0$;
  the statement has explicit constants, the term for $j = 0$ as
  $a(\alpha)(u_h^+(\alpha) - \varphi)^2$, and the outflow term in addition. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_69`.
* **Error estimate for continuous elements in §13.10.1** (reading). The source prints the boundary
  term at the inflow end $\alpha$, where it vanishes; the statement has it at the outflow end
  $\beta$. See `QuarteroniSaccoSaleri.Chapter13.cG_convergence`.
* **Convergence estimate for discontinuous elements in §13.10.1** (reading). The source uses the
  maximum in time and integrals up to $T$. The statement bounds the error at each $t \le T$ and
  its accumulated terms up to $t$, with explicit dependence on the mesh ratio. See
  `QuarteroniSaccoSaleri.Chapter13.dG_convergence`.
* **Display after (13.70)** (correction). The source prints the term $a(\beta)(u_h^{n+1}(\beta))^2$;
  the derivation gives $\frac12 a(\beta)(u_h^{n+1}(\beta))^2$, and the printed inequality does not
  follow. See `QuarteroniSaccoSaleri.Chapter13.equation_13_70_stability`.
* **Summed display after (13.70)** (reading). The source prints the boundary term as
  $a(\beta)(u_h^{j+1}(\beta))^2$ summed over $j = 1, \dots, m$; it is read as $u_h^j(\beta)^2$. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_70_sum`.
* **Summed display after (13.70)** (typo). The source drops the factor $\mu_0$ from
  $2 \Delta t \sum_j \mu_0 \|u_h^j\|^2$. See `QuarteroniSaccoSaleri.Chapter13.equation_13_70_sum`.
* **Exercise 13.10** (reading). The exercise asks for (13.69) when $f = 0$; the statement also takes
  $\varphi = 0$. See `QuarteroniSaccoSaleri.Chapter13.exercise_13_10`.

## Not formalized

* **The continuous Galerkin method (13.65) with a nonzero inflow datum.** It is the same equation on
  the affine space $\varphi_h(t) + V_h^{in}$.
-/

open Set MeasureTheory Polynomial Real
open scoped RealInnerProductSpace Interval

noncomputable section

namespace QuarteroniSaccoSaleri.Chapter13

section Transport

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ} [hx : Fact (StrictMono x)] {a : ℝ → ℝ}
  {a₀ : ℝ → ℝ → ℝ}

/-! ### The transport problem (13.64) -/

/-- **Equation (13.64)** of [quarteroni2000numerical]. Let $a : \mathbb{R} \to \mathbb{R}$,
$a_0, f : \mathbb{R}^2 \to \mathbb{R}$, $\varphi, u_0 : \mathbb{R} \to \mathbb{R}$ and
$\alpha, \beta, T \in \mathbb{R}$. A function $u = u(x, t)$ is a **classical solution of the
transport problem** if $u$ is differentiable on the closed strip
$[\alpha, \beta] \times [0, T]$, relative to the strip, and
$$u_t + a(x) u_x + a_0(x, t) u = f(x, t) \quad \text{on } [\alpha, \beta] \times [0, T],$$
$$u(\alpha, t) = \varphi(t) \quad (t \in [0, T]), \qquad u(x, 0) = u_0(x) \quad (x \in [\alpha,
  \beta]).$$

The source assumes $a(x) > 0$ on $[\alpha, \beta]$, which makes $x = \alpha$ the inflow
boundary. This positivity is not part of the definition; it is a hypothesis of the results that
need it. The definition is `Transport.IsInflowSolution`.

**Reading.** The solution identity holds on the closed rectangle and includes corner
compatibility. Positivity of the transport speed is a separate hypothesis for results that need
it. -/
def equation_13_64 (a : ℝ → ℝ) (a₀ f : ℝ → ℝ → ℝ) (φ u₀ : ℝ → ℝ) (α β T : ℝ)
    (u : ℝ → ℝ → ℝ) : Prop :=
  Transport.IsInflowSolution a a₀ f φ u₀ α β T u

omit hx in
/-- The transport problem (13.64) written out: $u$ is a classical solution if and only if there are
functions $u_x$ and $u_t$ that are the partial derivatives of $u$ on
$[\alpha, \beta] \times [0, T]$, in the sense of `Transport.HasPartialsOn`, such that
$u_t + a u_x + a_0 u = f$ on the strip, $u(\alpha, t) = \varphi(t)$ for $t \in [0, T]$, and
$u(x, 0) = u_0(x)$ for $x \in [\alpha, \beta]$.

**Reading.** Unfolds the stronger closed-rectangle classical solution predicate.
-/
theorem equation_13_64_def (a : ℝ → ℝ) (a₀ f : ℝ → ℝ → ℝ) (φ u₀ : ℝ → ℝ) (α β T : ℝ)
    (u : ℝ → ℝ → ℝ) :
    equation_13_64 a a₀ f φ u₀ α β T u ↔
      ∃ ux ut : ℝ → ℝ → ℝ, Transport.HasPartialsOn (Icc α β ×ˢ Icc 0 T) u ux ut ∧
        (∀ y ∈ Icc α β, ∀ t ∈ Icc (0 : ℝ) T,
          ut y t + a y * ux y t + a₀ y t * u y t = f y t) ∧
        (∀ t ∈ Icc (0 : ℝ) T, u α t = φ t) ∧ ∀ y ∈ Icc α β, u y 0 = u₀ y :=
  Iff.rfl

/-! ### The finite element spaces and the transport form -/

/-- **Section 13.10.1** of [quarteroni2000numerical], the test space $V_h^{in}$. Let
$\alpha = x_0 < \dots < x_n = \beta$ be a partition with $n \ge 1$, and let $r \in \mathbb{N}$.
The **inflow test space**
$$V_h^{in} = \{v \in V_h : v(\alpha) = 0\}$$
is the space of continuous piecewise polynomials of degree at most $r$ that vanish at the inflow
end $\alpha$.

It is a submodule of `BrokenPolynomial x r`: the intersection of
`BrokenPolynomial.continuous x r`, which is $V_h = X_h^r$, with the kernel of the trace
$v \mapsto v^+(x_0)$.

**Generalization.** The continuous vanishing-trace space permits a single panel. -/
def inflowSpace (x : Fin (n + 1) → ℝ) (r : ℕ) (hn : 0 < n) :
    Submodule ℝ (BrokenPolynomial x r) :=
  BrokenPolynomial.continuous x r ⊓ LinearMap.ker (BrokenPolynomial.traceRightₗ x r ⟨0, hn⟩)

omit hx in
/-- A piecewise polynomial $v$ lies in $V_h^{in}$ if and only if $v$ is continuous and
$v^+(\alpha) = 0$. -/
theorem mem_inflowSpace_iff {hn : 0 < n} {v : BrokenPolynomial x r} :
    v ∈ inflowSpace x r hn ↔
      v ∈ BrokenPolynomial.continuous x r ∧ BrokenPolynomial.traceRight v ⟨0, hn⟩ = 0 :=
  Iff.rfl

variable (x r) in
/-- **Section 13.10.1** of [quarteroni2000numerical], the form of (13.65). Let $a$ and, for each
$t$, $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$. For each time $t$, the **transport
form** on the piecewise polynomials of degree at most $r$ is
$$b_t(u, v) = \sum_{j=0}^{n-1} \int_{x_j}^{x_{j+1}} \bigl(a u_j' + a_0(\cdot, t) u_j\bigr)
  v_j,$$
where $u_j$ and $v_j$ are the polynomials of $u$ and $v$ on the panel $[x_j, x_{j+1}]$. It is a
bounded bilinear form for the $L^2(\alpha, \beta)$ inner product.

The form is `Variational.transportForm` with the reaction coefficient $a_0(\cdot, t)$.

**Generalization.** The panel integrals define a continuous bilinear form on the whole broken-
polynomial space. -/
def transportForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n))) (t : ℝ) :
    SesqForm ℝ (BrokenPolynomial x r) :=
  Variational.transportForm x r ha (ha₀ t)

/-- The transport form is the sum of the panel integrals: $b_t(u, v) = \sum_j \int_{x_j}^{x_{j+1}}
(a u_j' + a_0(\cdot, t) u_j) v_j$.

**Reading.** Sum over broken panels, including discontinuous trial and test functions.
-/
theorem transportForm_apply (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n))) (t : ℝ)
    (u v : BrokenPolynomial x r) :
    transportForm x r ha ha₀ t u v = ∑ i, ∫ s in x i.castSucc..x i.succ,
      (a s * (u i).derivative.eval s + a₀ s t * (u i).eval s) * (v i).eval s := rfl

/-! ### The continuous Galerkin semi-discretization (13.65) -/

/-- **Equation (13.65)** of [quarteroni2000numerical], with the inflow datum $\varphi = 0$. Let
$n \ge 1$, let $a$ and $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let $f(t)$ be a
piecewise polynomial for each $t$, let $u_{0,h} \in V_h^{in}$, and let $T \in \mathbb{R}$. A
curve $u_h : \mathbb{R} \to V_h^{in}$ **solves the continuous Galerkin semi-discretization** if
$u_h(0) = u_{0,h}$ and, for every $t \in [0, T]$, $u_h$ has a derivative $\partial_t u_h(t)$
relative to $[0, T]$ with
$$(\partial_t u_h(t), v_h)_{L^2} + b_t(u_h(t), v_h) = (f(t), v_h)_{L^2}
  \quad \text{for all } v_h \in V_h^{in}.$$

The case of a nonzero datum $u_h(\alpha, t) = \varphi_h(t)$ is the same equation on the affine
space $\varphi_h(t) + V_h^{in}$ and is not stated separately. The definition is
`Variational.IsSemidiscreteGalerkin` for the restriction of
`QuarteroniSaccoSaleri.Chapter13.transportForm` to $V_h^{in}$.

**Specialization.** The inflow value is zero, the volume load is represented by a broken
polynomial, and the time interval is closed. -/
def equation_13_65 (hn : 0 < n) (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (f : ℝ → BrokenPolynomial x r) (u₀h : inflowSpace x r hn) (T : ℝ)
    (uh : ℝ → inflowSpace x r hn) : Prop :=
  Variational.IsSemidiscreteGalerkin
    (fun t => (transportForm x r ha ha₀ t).restrict (inflowSpace x r hn))
    (fun t => (innerSL ℝ (f t)).comp (inflowSpace x r hn).subtypeL) u₀h T uh

/-- **Section 13.10.1** of [quarteroni2000numerical], the energy identity for (13.66). Let
$n \ge 1$, let $a$ and $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, and let $a$ be
differentiable on $[\alpha, \beta]$ with $a'$ continuous there. For every continuous piecewise
polynomial $v \in V_h$ and every $t$,
$$b_t(v, v) = \tfrac12 a(\beta) v(\beta)^2 - \tfrac12 a(\alpha) v(\alpha)^2 + \int_\alpha^\beta
  \bigl(a_0(\cdot, t) - \tfrac12 a'\bigr) v^2.$$

The proof integrates by parts on each panel; the boundary terms telescope because $v$ has no
interior jumps. Here $v(\beta)$ is `BrokenPolynomial.traceLeft v (Fin.last n)`, $v(\alpha)$ is
`BrokenPolynomial.traceRight v ⟨0, hn⟩`, and the integral is a sum of panel integrals.

**Generalization.** The energy identity retains both endpoint traces before enforcing
homogeneous inflow. -/
theorem transportForm_apply_self (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (hn : 0 < n) (t : ℝ)
    {v : BrokenPolynomial x r} (hv : v ∈ BrokenPolynomial.continuous x r) :
    transportForm x r ha ha₀ t v v
      = a (x (Fin.last n)) * BrokenPolynomial.traceLeft v (Fin.last n) ^ 2 / 2
        - a (x 0) * BrokenPolynomial.traceRight v ⟨0, hn⟩ ^ 2 / 2
        + ∑ i, ∫ s in x i.castSucc..x i.succ, (a₀ s t - deriv a s / 2) * (v i).eval s ^ 2 :=
  Variational.transportForm_apply_self_of_continuous ha (ha₀ t) hd hd' hn hv

/-- **Section 13.10.1** of [quarteroni2000numerical], the coercivity behind (13.66) and (13.67). Let
$n \ge 1$, let $a$ and $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let $a$ be
differentiable on $[\alpha, \beta]$ with $a'$ continuous there, and let $c, t \in \mathbb{R}$
with $c \le a_0(x, t) - a'(x)/2$ for all $x \in [\alpha, \beta]$. Then for every
$v \in V_h^{in}$
$$c \|v\|_{L^2}^2 + \tfrac12 a(\beta) v(\beta)^2 \le b_t(v, v).$$
The choice $c = \mu_0 > 0$ gives (13.66), and the choice $c = -\mu^*(t)$ gives (13.67).

The inflow term of `QuarteroniSaccoSaleri.Chapter13.transportForm_apply_self` vanishes on
$V_h^{in}$. The theorem is `Variational.le_transportForm_restrict` at the time $t$.

**Reading.** States coercivity with a general lower coefficient bound and explicit outflow trace.
-/
theorem le_transportForm_restrict (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (hn : 0 < n) {t c : ℝ}
    (hc : ∀ s ∈ Icc (x 0) (x (Fin.last n)), c ≤ a₀ s t - deriv a s / 2)
    (v : inflowSpace x r hn) :
    c * ‖v‖ ^ 2
        + a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
      ≤ (transportForm x r ha ha₀ t).restrict (inflowSpace x r hn) v v :=
  Variational.le_transportForm_restrict ha (ha₀ t) hd hd' hn hc (fun _ hv => hv) v

/-- Along a curve $u_h$ in $V_h^{in}$ that is continuous on $[0, T]$, the outflow term
$t \mapsto a(\beta) u_h(\beta, t)^2$ is continuous on $[0, T]$. -/
private theorem continuousOn_outflow {hn : 0 < n} {T : ℝ} {uh : ℝ → inflowSpace x r hn}
    (h : ContinuousOn uh (Icc 0 T)) :
    ContinuousOn (fun s => a (x (Fin.last n))
      * BrokenPolynomial.traceLeft (uh s : BrokenPolynomial x r) (Fin.last n) ^ 2) (Icc 0 T) := by
  have hc : Continuous fun v : inflowSpace x r hn =>
      BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n) :=
    (BrokenPolynomial.continuous_traceLeft (Fin.last n)).comp continuous_subtype_val
  exact continuousOn_const.mul ((hc.comp_continuousOn h).pow 2)

/-- For a piecewise polynomial $g$, the functional $v \mapsto (g, v)_{L^2}$ on $V_h^{in}$ has norm
at most $\|g\|_{L^2}$. -/
private theorem norm_source_le {hn : 0 < n} (g : BrokenPolynomial x r) :
    ‖(innerSL ℝ g).comp (inflowSpace x r hn).subtypeL‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
    simpa using abs_real_inner_le_norm g (v : BrokenPolynomial x r)

/-- **Equation (13.66)** of [quarteroni2000numerical]. Let $n \ge 1$, let $a$ and $a_0(\cdot, t)$ be
integrable on $[\alpha, \beta]$, let $a$ be differentiable on $[\alpha, \beta]$ with $a'$
continuous there, and let $u_h$ solve the continuous Galerkin semi-discretization (13.65) with
$\varphi = 0$, the source $f$ and the initial value $u_{0,h}$. Let $\mu_0 > 0$ with
$\mu_0 \le a_0(x, t) - a'(x)/2$ for all $t \in [0, T]$ and $x \in [\alpha, \beta]$, and let
$t \mapsto \|f(t)\|_{L^2}$ be continuous on $[0, T]$. Then for every $t \in [0, T]$
$$\|u_h(t)\|_{L^2}^2 + \int_0^t \bigl(\mu_0 \|u_h(\tau)\|_{L^2}^2 + a(\beta) u_h(\beta,
  \tau)^2\bigr) \, d\tau \le \|u_{0,h}\|_{L^2}^2 + \frac{1}{\mu_0} \int_0^t \|f(\tau)\|_{L^2}^2
  \, d\tau.$$

**Reading.** The source prints the boundary term as $a(\beta) \int_0^t u_h^2(\tau) \, d\tau$. It
is read as $a(\beta) \int_0^t u_h(\beta, \tau)^2 \, d\tau$.

The proof applies `Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le` with the
coercivity `QuarteroniSaccoSaleri.Chapter13.le_transportForm_restrict`. -/
theorem equation_13_66 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {f : ℝ → BrokenPolynomial x r} {u₀h : inflowSpace x r hn} {T : ℝ}
    {uh : ℝ → inflowSpace x r hn} (h : equation_13_65 hn ha ha₀ f u₀h T uh)
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hf : ContinuousOn (fun s => ‖f s‖) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, (μ₀ * ‖uh s‖ ^ 2 + a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (uh s : BrokenPolynomial x r) (Fin.last n) ^ 2)
      ≤ ‖u₀h‖ ^ 2 + μ₀⁻¹ * ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2 :=
  h.norm_sq_add_integral_le (Q := fun _ v => a (x (Fin.last n))
      * BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2) hμ
    (continuousOn_outflow h.continuousOn)
    (fun s hs v => le_transportForm_restrict ha ha₀ hd hd' hn (hμ₀ s hs) v) hf
    (fun s _ => norm_source_le (f s)) ht

/-- **Section 13.10.1** of [quarteroni2000numerical], conservation of the energy after (13.66). Let
$n \ge 1$, let $a$ and $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let $a$ be
differentiable on $[\alpha, \beta]$ with $a'$ continuous there, and let $u_h$ solve (13.65) with
$\varphi = 0$ and $f = 0$. If $a(\beta) \ge 0$ and $a_0(x, t) - a'(x)/2 \ge 0$ for all
$t \in [0, T]$ and $x \in [\alpha, \beta]$, then $t \mapsto \|u_h(t)\|_{L^2}$ is nonincreasing
on $[0, T]$.

**Correction.** The source states the conservation of the energy when $f = a_0 = 0$. Then the
energy identity also needs $a' \le 0$, which holds for a constant convective term. The statement
here asks for $a_0 - a'/2 \ge 0$ instead. -/
theorem equation_13_66_conservation (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {u₀h : inflowSpace x r hn} {T : ℝ} {uh : ℝ → inflowSpace x r hn}
    (h : equation_13_65 hn ha ha₀ 0 u₀h T uh) (hβ : 0 ≤ a (x (Fin.last n)))
    (hpos : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a₀ s t - deriv a s / 2) :
    AntitoneOn (fun t => ‖uh t‖) (Icc 0 T) := by
  refine h.norm_le_of_nonneg (fun t => by simp) fun t htmem v => ?_
  have := le_transportForm_restrict ha ha₀ hd hd' hn (hpos t htmem) v
  simp only [RCLike.re_to_real, zero_mul]
  nlinarith [sq_nonneg (BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n))]

/-- **Section 13.10.1** of [quarteroni2000numerical], conservation of the energy in the form of the
source. Under the hypotheses of `QuarteroniSaccoSaleri.Chapter13.equation_13_66_conservation`
($u_h$ solves (13.65) with $\varphi = 0$ and $f = 0$, $a(\beta) \ge 0$, and $a_0 - a'/2 \ge 0$
on $[\alpha, \beta] \times [0, T]$), we have $\|u_h(t)\|_{L^2} \le \|u_{0,h}\|_{L^2}$ for every
$t \in [0, T]$.

**Correction.** As in `QuarteroniSaccoSaleri.Chapter13.equation_13_66_conservation`, the
condition $f = a_0 = 0$ of the source is replaced by $f = 0$ and $a_0 - a'/2 \ge 0$. -/
theorem equation_13_66_conservation_le (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {u₀h : inflowSpace x r hn} {T : ℝ} {uh : ℝ → inflowSpace x r hn}
    (h : equation_13_65 hn ha ha₀ 0 u₀h T uh) (hβ : 0 ≤ a (x (Fin.last n)))
    (hpos : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a₀ s t - deriv a s / 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) : ‖uh t‖ ≤ ‖u₀h‖ := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, ht.1.trans ht.2⟩
  have h1 : uh 0 = u₀h := h.1
  simpa [h1] using equation_13_66_conservation ha ha₀ hd hd' h hβ hpos h0 ht ht.1

/-- **Equation (13.67)** of [quarteroni2000numerical]. Let $n \ge 1$, let $a$ and $a_0(\cdot, t)$ be
integrable on $[\alpha, \beta]$, let $a$ be differentiable on $[\alpha, \beta]$ with $a'$
continuous there, and let $u_h$ solve (13.65) with $\varphi = 0$, the source $f$ and the initial
value $u_{0,h}$. Let $a(\beta) \ge 0$, let $\mu^*$ be continuous and nonnegative on $[0, T]$
with $|a_0(x, t) - a'(x)/2| \le \mu^*(t)$ for all $t \in [0, T]$ and $x \in [\alpha, \beta]$,
and let $t \mapsto \|f(t)\|_{L^2}$ be continuous on $[0, T]$. Then for every $t \in [0, T]$
$$\|u_h(t)\|_{L^2}^2 + a(\beta) \int_0^t u_h(\beta, \tau)^2 \, d\tau
  \le \Bigl(\|u_{0,h}\|_{L^2}^2 + \int_0^t \|f(\tau)\|_{L^2}^2 \, d\tau\Bigr)
  \exp \int_0^t \bigl(1 + 2\mu^*(\tau)\bigr) \, d\tau.$$
This estimate holds without the condition $\mu_0 > 0$ of (13.66).

**Reading.** As in (13.66), the boundary term printed $a(\beta) \int_0^t u_h^2(\tau) \, d\tau$
is read as $a(\beta) \int_0^t u_h(\beta, \tau)^2 \, d\tau$.

The source writes $\mu$ for $a_0 - a'/2$, and $\mu^*(t)$ is any bound for $\max_{x \in [\alpha,
\beta]} |a_0(x, t) - a'(x)/2|$. The proof uses Gronwall's lemma, through
`Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le_exp`, with the coercivity
`QuarteroniSaccoSaleri.Chapter13.le_transportForm_restrict` at $c = -\mu^*(t)$.

**Reading.** The Gronwall exponent uses a continuous nonnegative bound for the absolute
reaction-minus-half-derivative, allowing a bound larger than the source maximum. -/
theorem equation_13_67 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {f : ℝ → BrokenPolynomial x r} {u₀h : inflowSpace x r hn} {T : ℝ}
    {uh : ℝ → inflowSpace x r hn} (h : equation_13_65 hn ha ha₀ f u₀h T uh)
    (hβ : 0 ≤ a (x (Fin.last n))) {m : ℝ → ℝ} (hm : ContinuousOn m (Icc 0 T))
    (hm0 : ∀ t ∈ Icc 0 T, 0 ≤ m t)
    (hmax : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t - deriv a s / 2| ≤ m t)
    (hf : ContinuousOn (fun s => ‖f s‖) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (uh s : BrokenPolynomial x r) (Fin.last n) ^ 2
      ≤ (‖u₀h‖ ^ 2 + ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) * exp (∫ s in (0 : ℝ)..t, (1 + 2 * m s)) :=
  h.norm_sq_add_integral_le_exp (Q := fun _ v => a (x (Fin.last n))
      * BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2) hm hm0
    (fun _ _ => mul_nonneg hβ (sq_nonneg _)) (continuousOn_outflow h.continuousOn)
    (fun s hs v => le_transportForm_restrict ha ha₀ hd hd' hn
      (fun y hy => neg_le_of_abs_le (hmax s hs y hy)) v) hf
    (fun s _ => norm_source_le (f s)) ht

/-- **Exercise 13.9** of [quarteroni2000numerical]. The exercise asks for a proof of (13.67). Under
the hypotheses of `QuarteroniSaccoSaleri.Chapter13.equation_13_67`, the solution $u_h$ of
(13.65) with $\varphi = 0$ satisfies, for every $t \in [0, T]$,
$$\|u_h(t)\|_{L^2}^2 + a(\beta) \int_0^t u_h(\beta, \tau)^2 \, d\tau
  \le \Bigl(\|u_{0,h}\|_{L^2}^2 + \int_0^t \|f(\tau)\|_{L^2}^2 \, d\tau\Bigr)
  \exp \int_0^t \bigl(1 + 2\mu^*(\tau)\bigr) \, d\tau.$$

The statement is that of `QuarteroniSaccoSaleri.Chapter13.equation_13_67`, recorded under the
name of the exercise.

**Correction.** Same explicit hypotheses and energy bound as the corrected version of (13.67).
-/
theorem exercise_13_9 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {f : ℝ → BrokenPolynomial x r} {u₀h : inflowSpace x r hn} {T : ℝ}
    {uh : ℝ → inflowSpace x r hn} (h : equation_13_65 hn ha ha₀ f u₀h T uh)
    (hβ : 0 ≤ a (x (Fin.last n))) {m : ℝ → ℝ} (hm : ContinuousOn m (Icc 0 T))
    (hm0 : ∀ t ∈ Icc 0 T, 0 ≤ m t)
    (hmax : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t - deriv a s / 2| ≤ m t)
    (hf : ContinuousOn (fun s => ‖f s‖) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (uh s : BrokenPolynomial x r) (Fin.last n) ^ 2
      ≤ (‖u₀h‖ ^ 2 + ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) * exp (∫ s in (0 : ℝ)..t, (1 + 2 * m s)) :=
  equation_13_67 ha ha₀ hd hd' h hβ hm hm0 hmax hf ht

/-! ### The discontinuous Galerkin semi-discretization (13.68) -/

/-- **Equation (13.68)** of [quarteroni2000numerical]. Let $n \ge 1$, let $a$ and $a_0(\cdot, t)$ be
integrable on $[\alpha, \beta]$, let $\varphi : \mathbb{R} \to \mathbb{R}$, let $f(t) \in W_h$
for each $t$, let $u_{0,h} \in W_h$, and let $T \in \mathbb{R}$. A curve
$u_h : \mathbb{R} \to W_h$ **solves the discontinuous Galerkin semi-discretization** if
$u_h(0) = u_{0,h}$ and, for every $t \in [0, T]$, $u_h$ has a derivative $\partial_t u_h(t)$
relative to $[0, T]$ with
$$(\partial_t u_h(t), v_h)_{L^2} + b_t^{DG}(u_h(t), v_h) = (f(t), v_h)_{L^2} + a(\alpha)
  \varphi(t) v_h^+(\alpha) \quad \text{for all } v_h \in W_h,$$
where
$$b_t^{DG}(u, v) = \sum_{j=0}^{n-1} \Bigl[\int_{x_j}^{x_{j+1}} \bigl(a u_j' + a_0(\cdot, t)
  u_j\bigr) v_j + a(x_j) \bigl(u^+(x_j) - u^-(x_j)\bigr) v^+(x_j)\Bigr]$$
with the convention $u^-(x_0) = 0$.

The source writes the inflow value as $U_h^-(x_0, t) = \varphi(t)$; here it is carried by the
source term on the right. The space $W_h = Y_h^r$ is `BrokenPolynomial x r`, and the form is
`Variational.dgUpwindForm`.

**Reading.** The reaction retains its time dependence, and the prescribed inflow enters as a
separate trace functional on the load side. -/
def equation_13_68 (hn : 0 < n) (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (φ : ℝ → ℝ) (f : ℝ → BrokenPolynomial x r) (u₀h : BrokenPolynomial x r) (T : ℝ)
    (uh : ℝ → BrokenPolynomial x r) : Prop :=
  Variational.IsSemidiscreteGalerkin (fun t => Variational.dgUpwindForm x r ha (ha₀ t))
    (fun t => innerSL ℝ (f t) + (a (x 0) * φ t) • BrokenPolynomial.traceRightL x r ⟨0, hn⟩)
    u₀h T uh

/-- **Section 13.10.1** of [quarteroni2000numerical], the energy identity for (13.69). Let $a$ and
$a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, and let $a$ be differentiable on
$[\alpha, \beta]$ with $a'$ continuous there. For every $v \in W_h$ and every $t$,
$$b_t^{DG}(v, v) = \tfrac12 a(\beta) v^-(\beta)^2 + \tfrac12 \sum_{j=0}^{n-1} a(x_j) [v]_j^2 +
  \int_\alpha^\beta \bigl(a_0(\cdot, t) - \tfrac12 a'\bigr) v^2,$$
with $[v]_0 = v^+(\alpha)$.

The proof integrates by parts on each panel and then uses, at each node, $\frac12 a (v^-)^2 -
\frac12 a (v^+)^2 + a [v] v^+ = \frac12 a [v]^2$.

**Reading.** Makes the outflow term and zero-exterior first jump explicit for the form.
-/
theorem dgUpwindForm_apply_self (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (t : ℝ)
    (v : BrokenPolynomial x r) :
    Variational.dgUpwindForm x r ha (ha₀ t) v v
      = a (x (Fin.last n)) * BrokenPolynomial.traceLeft v (Fin.last n) ^ 2 / 2
        + ∑ i : Fin n, a (x i.castSucc) * BrokenPolynomial.jump v i ^ 2 / 2
        + ∑ i, ∫ s in x i.castSucc..x i.succ, (a₀ s t - deriv a s / 2) * (v i).eval s ^ 2 :=
  Variational.dgUpwindForm_apply_self ha (ha₀ t) hd hd' v

/-- **Section 13.10.1** of [quarteroni2000numerical], the coercivity behind (13.69). Let $a$ and
$a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let $a$ be differentiable on
$[\alpha, \beta]$ with $a'$ continuous there, and let $c, t \in \mathbb{R}$ with
$c \le a_0(x, t) - a'(x)/2$ for all $x \in [\alpha, \beta]$. Then for every $v \in W_h$
$$c \|v\|_{L^2}^2 + \tfrac12 a(\beta) v^-(\beta)^2 + \tfrac12 \sum_{j=0}^{n-1} a(x_j) [v]_j^2
  \le b_t^{DG}(v, v).$$

The theorem is `Variational.le_dgUpwindForm` at the time $t$.

**Reading.** Explicit coercivity and boundary/jump terms under a general lower reaction bound.
-/
theorem le_dgUpwindForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {t c : ℝ}
    (hc : ∀ s ∈ Icc (x 0) (x (Fin.last n)), c ≤ a₀ s t - deriv a s / 2)
    (v : BrokenPolynomial x r) :
    c * ‖v‖ ^ 2 + a (x (Fin.last n)) * BrokenPolynomial.traceLeft v (Fin.last n) ^ 2 / 2
        + ∑ i : Fin n, a (x i.castSucc) * BrokenPolynomial.jump v i ^ 2 / 2
      ≤ Variational.dgUpwindForm x r ha (ha₀ t) v v :=
  Variational.le_dgUpwindForm ha (ha₀ t) hd hd' hc v

/-- **Equation (13.69)** of [quarteroni2000numerical]. Let $n \ge 1$, let $a$ and $a_0(\cdot, t)$ be
integrable on $[\alpha, \beta]$, let $a$ be differentiable on $[\alpha, \beta]$ with $a'$
continuous there, and let $u_h$ solve the discontinuous Galerkin semi-discretization (13.68)
with the inflow datum $\varphi$, the source $f$ and the initial value $u_{0,h}$. Let $\mu_0 > 0$
with $\mu_0 \le a_0(x, t) - a'(x)/2$ for all $t \in [0, T]$ and $x \in [\alpha, \beta]$, and let
$t \mapsto \|f(t)\|_{L^2}$ and $\varphi$ be continuous on $[0, T]$. Then for every
$t \in [0, T]$
$$\|u_h(t)\|^2 + \int_0^t \Bigl(\mu_0 \|u_h(\tau)\|^2 + a(\beta) u_h^-(\beta, \tau)^2 +
  a(\alpha) \bigl(u_h^+(\alpha, \tau) - \varphi(\tau)\bigr)^2 + \sum_{j=1}^{n-1} a(x_j)
  [u_h(\tau)]_j^2\Bigr) d\tau \le \|u_{0,h}\|^2 + \int_0^t \Bigl(\frac{1}{\mu_0} \|f(\tau)\|^2 +
  a(\alpha) \varphi(\tau)^2\Bigr) d\tau,$$
with the $L^2(\alpha, \beta)$ norm.

**Reading.** The source states (13.69) with an unspecified constant $C$ and the jump sum
$\sum_{j=0}^{n-1}$. Here the constants are explicit. The term for $j = 0$ is
$a(\alpha)(u_h^+(\alpha) - \varphi)^2$, which is the jump $[u_h]_0$ of the source, because the
source sets $U_h^-(x_0, t) = \varphi(t)$. The outflow term $a(\beta) u_h^-(\beta)^2$ appears in
addition.

The proof tests (13.68) with $v_h = u_h(t)$, uses
`QuarteroniSaccoSaleri.Chapter13.le_dgUpwindForm`, and integrates the resulting inequality with
`Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le_integral`. -/
theorem equation_13_69 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {φ : ℝ → ℝ}
    {f : ℝ → BrokenPolynomial x r} {u₀h : BrokenPolynomial x r} {T : ℝ}
    {uh : ℝ → BrokenPolynomial x r} (h : equation_13_68 hn ha ha₀ φ f u₀h T uh)
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hf : ContinuousOn (fun s => ‖f s‖) (Icc 0 T)) (hφ : ContinuousOn φ (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, (μ₀ * ‖uh s‖ ^ 2
          + a (x (Fin.last n)) * BrokenPolynomial.traceLeft (uh s) (Fin.last n) ^ 2
          + a (x 0) * (BrokenPolynomial.traceRight (uh s) ⟨0, hn⟩ - φ s) ^ 2
          + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2)
      ≤ ‖u₀h‖ ^ 2 + ∫ s in (0 : ℝ)..t, (μ₀⁻¹ * ‖f s‖ ^ 2 + a (x 0) * φ s ^ 2) := by
  have hcont := h.continuousOn
  have hw : ContinuousOn (fun s => μ₀ * ‖uh s‖ ^ 2
      + a (x (Fin.last n)) * BrokenPolynomial.traceLeft (uh s) (Fin.last n) ^ 2
      + a (x 0) * (BrokenPolynomial.traceRight (uh s) ⟨0, hn⟩ - φ s) ^ 2
      + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2) (Icc 0 T) := by
    refine ((((continuousOn_const.mul h.continuousOn_norm_sq).add (continuousOn_const.mul
      (((BrokenPolynomial.continuous_traceLeft (Fin.last n)).comp_continuousOn hcont).pow
        2))).add (continuousOn_const.mul
      ((((BrokenPolynomial.continuous_traceRight ⟨0, hn⟩).comp_continuousOn hcont).sub
        hφ).pow 2))).add ?_)
    exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
      (((BrokenPolynomial.continuous_jump j).comp_continuousOn hcont).pow 2)
  have hg : ContinuousOn (fun s => μ₀⁻¹ * ‖f s‖ ^ 2 + a (x 0) * φ s ^ 2) (Icc 0 T) :=
    (continuousOn_const.mul (hf.pow 2)).add (continuousOn_const.mul (hφ.pow 2))
  refine h.norm_sq_add_integral_le_integral hw hg (fun s hs => ?_) ht
  have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
  set v := uh s with hv
  have hb := le_dgUpwindForm ha ha₀ hd hd' (hμ₀ s hs') v
  have hjump0 : BrokenPolynomial.jump v ⟨0, hn⟩ = BrokenPolynomial.traceRight v ⟨0, hn⟩ :=
    BrokenPolynomial.jump_zero v hn
  have hcast : (⟨0, hn⟩ : Fin n).castSucc = (0 : Fin (n + 1)) := rfl
  have hsum : a (x 0) * BrokenPolynomial.traceRight v ⟨0, hn⟩ ^ 2
      + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x j.castSucc) * BrokenPolynomial.jump v j ^ 2
      = ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump v j ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n)), hjump0, hcast]
  have hhalf : ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump v j ^ 2 / 2
      = (∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump v j ^ 2) / 2 :=
    (Finset.sum_div _ _ _).symm
  have hexp : a (x 0) * (BrokenPolynomial.traceRight v ⟨0, hn⟩ - φ s) ^ 2
      = a (x 0) * BrokenPolynomial.traceRight v ⟨0, hn⟩ ^ 2
        - 2 * (a (x 0) * φ s * BrokenPolynomial.traceRight v ⟨0, hn⟩) + a (x 0) * φ s ^ 2 := by
    ring
  have hfv : ⟪f s, v⟫ ≤ ‖f s‖ * ‖v‖ := real_inner_le_norm _ _
  have hY := Variational.IsSemidiscreteGalerkin.two_mul_mul_norm_le hμ (‖f s‖) v
  have hdiv : ‖f s‖ ^ 2 / μ₀ = μ₀⁻¹ * ‖f s‖ ^ 2 := by ring
  have hF : (innerSL ℝ (f s) + (a (x 0) * φ s) • BrokenPolynomial.traceRightL x r ⟨0, hn⟩) v
      = ⟪f s, v⟫ + a (x 0) * φ s * BrokenPolynomial.traceRight v ⟨0, hn⟩ := by simp
  simp only [hF]
  linarith

/-- **Exercise 13.10** of [quarteroni2000numerical]. Let $n \ge 1$, let $a$ and $a_0(\cdot, t)$ be
integrable on $[\alpha, \beta]$, let $a$ be differentiable on $[\alpha, \beta]$ with $a'$
continuous there, and let $u_h$ solve (13.68) with $\varphi = 0$, $f = 0$ and the initial value
$u_{0,h}$. Let $\mu_0 \le a_0(x, t) - a'(x)/2$ for all $t \in [0, T]$ and
$x \in [\alpha, \beta]$. Then for every $t \in [0, T]$
$$\|u_h(t)\|^2 + \int_0^t \Bigl(2\mu_0 \|u_h(\tau)\|^2 + a(\beta) u_h^-(\beta, \tau)^2 +
  \sum_{j=0}^{n-1} a(x_j) [u_h(\tau)]_j^2\Bigr) d\tau \le \|u_{0,h}\|^2,$$
with the $L^2(\alpha, \beta)$ norm.

**Reading.** The exercise asks for a proof of (13.69) when $f = 0$. The statement here also
takes $\varphi = 0$. Then no term has to be absorbed, so the full jump sum and the sharp
coefficient $2\mu_0$ remain.

As the hint of the exercise says, the proof takes $v_h = u_h(t)$ in (13.68). No sign condition
on $\mu_0$ is needed. -/
theorem exercise_13_10 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {u₀h : BrokenPolynomial x r} {T : ℝ} {uh : ℝ → BrokenPolynomial x r}
    (h : equation_13_68 hn ha ha₀ 0 0 u₀h T uh) {μ₀ : ℝ}
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, (2 * μ₀ * ‖uh s‖ ^ 2
          + a (x (Fin.last n)) * BrokenPolynomial.traceLeft (uh s) (Fin.last n) ^ 2
          + ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2)
      ≤ ‖u₀h‖ ^ 2 := by
  have hcont := h.continuousOn
  have hw : ContinuousOn (fun s => 2 * μ₀ * ‖uh s‖ ^ 2
      + a (x (Fin.last n)) * BrokenPolynomial.traceLeft (uh s) (Fin.last n) ^ 2
      + ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2) (Icc 0 T) := by
    refine (((continuousOn_const.mul h.continuousOn_norm_sq).add (continuousOn_const.mul
      (((BrokenPolynomial.continuous_traceLeft (Fin.last n)).comp_continuousOn hcont).pow
        2))).add ?_)
    exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
      (((BrokenPolynomial.continuous_jump j).comp_continuousOn hcont).pow 2)
  have key := h.norm_sq_add_integral_le_integral (g := fun _ => (0 : ℝ)) hw continuousOn_const
    (fun s hs => ?_) ht
  · simpa using key
  · have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have hb := le_dgUpwindForm ha ha₀ hd hd' (hμ₀ s hs') (uh s)
    have hhalf : ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2 / 2
        = (∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2) / 2 :=
      (Finset.sum_div _ _ _).symm
    have hF : (innerSL ℝ ((0 : ℝ → BrokenPolynomial x r) s)
        + (a (x 0) * (0 : ℝ → ℝ) s) • BrokenPolynomial.traceRightL x r ⟨0, hn⟩) (uh s) = 0 := by
      simp
    simp only [hF]
    linarith

/-! ### The convergence estimate of the continuous Galerkin method -/

/-- **Section 13.10.1** of [quarteroni2000numerical], the error estimate for continuous finite
elements of degree $r$. Let $n \ge 1$ and $T > 0$, and let the partition have panels of length
at most $h$ and carry a Lagrange node system of degree $r$. Let $a$ and $a_0(\cdot, t)$ be
integrable on $[\alpha, \beta]$, let $a$ be differentiable on $[\alpha, \beta]$ with $a'$
continuous there, and let $|a| \le A$ on $[\alpha, \beta]$, $|a_0| \le A_0$ on
$[\alpha, \beta] \times [0, T]$, $a(\beta) \ge 0$, and $0 < \mu_0 \le a_0 - a'/2$ on
$[\alpha, \beta] \times [0, T]$. Let $u$ be a classical solution of (13.64) with $\varphi = 0$,
the source $f$ and the initial value $u_0$. Let $u_t(x, t)$ be the derivative of $u(x, \cdot)$
relative to $[0, T]$, with $u_t(\cdot, t)$ continuous on $[\alpha, \beta]$. For every
$t \in [0, T]$, let $u(\cdot, t)$ and $u_t(\cdot, t)$ agree almost everywhere on
$(\alpha, \beta)$ with functions of $H^{r+1}(\alpha, \beta)$ whose seminorms $|\cdot|_{H^{r+1}}$
are at most $M$ and $M'$. Let $f_h(t)$ satisfy $(f_h(t), v)_{L^2} = \int_\alpha^\beta f(\cdot,
t) v$ for all $v \in V_h^{in}$ and $t \in [0, T]$, and let $u_h$ solve (13.65) with the source
$f_h$ and the initial value $u_{0,h} \in V_h^{in}$. Then for every $t \in [0, T]$
$$\|u(t) - u_h(t)\|_{L^2} + \Bigl(\int_0^t a(\beta) |u(\beta, \tau) - u_h(\beta, \tau)|^2 \,
  d\tau\Bigr)^{1/2} \le \sqrt2 \Bigl(\|u_0 - u_{0,h}\|_{L^2} + h^r \bigl(2hM + \sqrt{T / \mu_0}
  \, (AM + h(M' + A_0 M))\bigr)\Bigr).$$

**Reading.** The source prints the boundary term at the inflow end $\alpha$, where it vanishes
identically, because $u$ and $u_h$ both satisfy the inflow condition. The term that the energy
estimate (13.66) controls, and the one stated here, is at the outflow end $\beta$.

The source quotes this estimate from [quarteroni1994numerical], §14.3.1, without proof, as
$O(\|u_0 - u_{0,h}\| + h^r)$ for a smooth solution $u$. Here the regularity is a hypothesis and
the constant is explicit. The bound holds for every $t$, which gives the maximum over $t$ in the
source. The $L^2$ norms are written as sums of panel integrals, and $u_h(\beta, \tau)$ is
`BrokenPolynomial.traceLeft`. The node system is `BrokenPolynomial.IsLagrangeNodes`, which
forces $r \ge 1$. The proof specializes `Variational.cG_error_le`. -/
theorem cG_convergence (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {T : ℝ} (hT : 0 < T)
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hβ : 0 ≤ a (x (Fin.last n))) {A A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {f : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : equation_13_64 a a₀ f 0 u₀ (x 0) (x (Fin.last n)) T u) {ut : ℝ → ℝ → ℝ}
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => ut y t) (Icc (x 0) (x (Fin.last n))))
    {M M' : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    (hreg' : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => ut y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M')
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : BrokenPolynomial.IsLagrangeNodes x r node) {h : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v ∈ inflowSpace x r hn,
      ⟪fh t, v⟫ = BrokenPolynomial.pairing (fun y => f y t) v)
    {u₀h : inflowSpace x r hn} {uh : ℝ → inflowSpace x r hn}
    (huh : equation_13_65 hn ha ha₀ fh u₀h T uh) {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - ((uh t : BrokenPolynomial x r) i).eval s) ^ 2)
      + √(∫ τ in (0 : ℝ)..t, a (x (Fin.last n)) * (u (x (Fin.last n)) τ
          - BrokenPolynomial.traceLeft (uh τ : BrokenPolynomial x r) (Fin.last n)) ^ 2)
    ≤ √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u₀ s - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
        + h ^ r * (2 * h * M + √(T / μ₀) * (A * M + h * (M' + A₀ * M)))) := by
  obtain ⟨ux, ut₀, hpart, hpde, hin, hinit⟩ := hu
  have hm : Monotone x := hx.out.monotone
  have hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y :=
    fun y hy t ht => hpart.hasDerivWithinAt_fst hy ht
  have hut₀ : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T, ut₀ y t = ut y t :=
    fun y hy t ht =>
      (uniqueDiffOn_Icc hT t ht).eq_deriv _ (hpart.hasDerivWithinAt_snd hy ht) (hut y hy t ht)
  have hpde' : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t := fun y hy t ht => by
    rw [← hut₀ y hy t ht]
    exact hpde y hy t ht
  have hin' : ∀ t ∈ Icc 0 T, u (x 0) t = 0 := fun t ht => by simpa using hin t ht
  have key := Variational.cG_error_le hn hT ha ha₀ hd hd' hμ hμ₀ hβ hA hA₀ hux hut hutc hpde' hin'
    hreg hreg' (fun v => mem_inflowSpace_iff) hnode hmesh hfh huh ht
  have e : ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2
      = ∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2 :=
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le (hm (Fin.castSucc_lt_succ (i := i)).le)] at hs
      rw [hinit s (BrokenPolynomial.Icc_panel_subset hm i hs)]
  rwa [e] at key

/-! ### The convergence estimate of the discontinuous Galerkin method -/

/-- **Section 13.10.1** of [quarteroni2000numerical], the convergence estimate for discontinuous
finite elements of degree $r$. Let $n \ge 1$ and $T > 0$, and let the partition have panels of
length between $h_{\min} > 0$ and $h$ and carry a node system of degree $r$. Let $a$ and
$a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let $a$ be differentiable on
$[\alpha, \beta]$ with $a'$ continuous there, and let $0 \le a \le A$ and $|a'| \le A'$ on
$[\alpha, \beta]$, $|a_0| \le A_0$ on $[\alpha, \beta] \times [0, T]$, and
$0 < \mu_0 \le a_0 - a'/2$ on $[\alpha, \beta] \times [0, T]$. Let $u$ be a classical solution
of (13.64) with the data $f$, $\varphi$ and $u_0$, continuous on
$[\alpha, \beta] \times [0, T]$. Let $u_t(x, t)$ be the derivative of $u(x, \cdot)$ relative to
$[0, T]$, with $u_t$ continuous on $[\alpha, \beta] \times [0, T]$. For every $t \in [0, T]$,
let $u(\cdot, t)$ agree almost everywhere on $(\alpha, \beta)$ with a function of
$H^{r+1}(\alpha, \beta)$ whose seminorm $|\cdot|_{H^{r+1}}$ is at most $M$. Let $f_h(t)$ satisfy
$(f_h(t), v)_{L^2} = \int_\alpha^\beta f(\cdot, t) v$ for all $v \in W_h$ and $t \in [0, T]$,
and let $u_h$ solve (13.68) with the datum $\varphi$, the source $f_h$ and the initial value
$u_{0,h}$. Then for every $t \in [0, T]$
$$\|u(t) - u_h(t)\| + \Bigl(\int_0^t \Bigl(\|u(\tau) - u_h(\tau)\|^2 + \sum_{j=1}^{n-1} a(x_j)
  [u_h(\tau)]_j^2 + a(\alpha) \bigl(u_h^+(\alpha, \tau) - \varphi(\tau)\bigr)^2\Bigr)
  d\tau\Bigr)^{1/2} \le \sqrt2 \Bigl(\sqrt{16 + 4/\mu_0} \, \|u_0 - u_{0,h}\| + \sqrt{C} \,
  h^{r+1/2}\Bigr),$$
with the $L^2(\alpha, \beta)$ norm, where $C$ is the explicit constant
`Variational.dgConst r A A' A₀ μ₀ T M h hmin`.

**Reading.** The original PDF integrates the jump sum over $[0,T]$. Here the bound is stated
for each $t \le T$, with integrals up to $t$ and a constant that depends on $h/h_{\min}$. The
jumps of $u - u_h$ are those of $-u_h$ at the interior nodes, because $u$ is continuous. At
$x_0 = \alpha$ the jump is $\varphi - u_h^+(\alpha)$, by the convention
$U_h^-(x_0, t) = \varphi(t)$ of (13.68).

The source quotes this estimate from [quarteroni1994numerical], §14.3.3, without proof, as
$O(\|u_0 - u_{0,h}\| + h^{r+1/2})$ for a smooth solution $u$. Here the regularity is a
hypothesis and the constant is explicit. The node system is `BrokenPolynomial.IsNodes`, and
$h^{r+1/2}$ is written `h ^ r * √h`. The proof specializes `Variational.dG_error_le`. -/
theorem dG_convergence (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {T : ℝ} (hT : 0 < T)
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hapos : ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a s) {A A' A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA' : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |deriv a s| ≤ A')
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {f : ℝ → ℝ → ℝ} {φ u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : equation_13_64 a a₀ f φ u₀ (x 0) (x (Fin.last n)) T u)
    (huc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {ut : ℝ → ℝ → ℝ}
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {M : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : BrokenPolynomial.IsNodes x r node) {h hmin : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc) {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v, ⟪fh t, v⟫ = BrokenPolynomial.pairing (fun y => f y t) v)
    {u₀h : BrokenPolynomial x r} {uh : ℝ → BrokenPolynomial x r}
    (huh : equation_13_68 hn ha ha₀ φ fh u₀h T uh) {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
      + √(∫ τ in (0 : ℝ)..t, ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              a (x i.castSucc) * BrokenPolynomial.jump (uh τ) i ^ 2)
          + a (x 0) * (BrokenPolynomial.traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2))
    ≤ √2 * (√(16 + 4 / μ₀) * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - (u₀h i).eval s) ^ 2)
        + √(Variational.dgConst r A A' A₀ μ₀ T M h hmin) * (h ^ r * √h)) := by
  obtain ⟨ux, ut₀, hpart, hpde, hin, hinit⟩ := hu
  have hm : Monotone x := hx.out.monotone
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hm (Fin.castSucc_lt_succ (i := i)).le
  have hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y :=
    fun y hy t ht => hpart.hasDerivWithinAt_fst hy ht
  have hut₀ : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T, ut₀ y t = ut y t :=
    fun y hy t ht =>
      (uniqueDiffOn_Icc hT t ht).eq_deriv _ (hpart.hasDerivWithinAt_snd hy ht) (hut y hy t ht)
  have hpde' : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t := fun y hy t ht => by
    rw [← hut₀ y hy t ht]
    exact hpde y hy t ht
  have key := Variational.dG_error_le hn hT ha ha₀ hd hd' hμ hμ₀ hapos hA hA' hA₀ huc hux hut
    hutc hpde' hin hreg hnode hmesh h0 hminle hfh huh ht
  have e : ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2
      = ∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - (u₀h i).eval s) ^ 2 :=
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le (hle i)] at hs
      rw [hinit s (BrokenPolynomial.Icc_panel_subset hm i hs)]
  rwa [e] at key

/-! ### Time discretization: backward Euler (13.70) -/

/-- **Equation (13.70)** of [quarteroni2000numerical], with the inflow datum $\varphi = 0$. Let
$n \ge 1$, let $a$ and $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let
$\Delta t, t_1 \in \mathbb{R}$, let $f_1$ be a piecewise polynomial, and let
$u_h^n, u_h^{n+1} \in V_h^{in}$. Then $u_h^{n+1}$ is a **backward Euler step** from $u_h^n$ if
$$\frac{1}{\Delta t} (u_h^{n+1} - u_h^n, v_h)_{L^2} + b_{t_1}(u_h^{n+1}, v_h) = (f_1, v_h)_{L^2}
  \quad \text{for all } v_h \in V_h^{in}.$$
Here $t_1 = t^{n+1}$ is the new time and $f_1 = f^{n+1}$ is the source at that time.

The definition is the θ-step `Variational.IsThetaStep` with $\theta = 1$ for the restriction of
the transport form at the time $t_1$ to $V_h^{in}$, with zero source at the old time. For
$\Delta t = 0$ the factor $1 / \Delta t$ is $0$, by the convention for division by zero.

**Specialization.** This is one update for homogeneous inflow with a polynomial representative
of the load. -/
def equation_13_70 (hn : 0 < n) (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (Δt t₁ : ℝ) (f₁ : BrokenPolynomial x r) (un un1 : inflowSpace x r hn) : Prop :=
  Variational.IsThetaStep ((transportForm x r ha ha₀ t₁).restrict (inflowSpace x r hn)) 1 Δt 0
    ((innerSL ℝ f₁).comp (inflowSpace x r hn).subtypeL) un un1

/-- A step of (13.70) with the source $f_1 = 0$ is a backward Euler θ-step
(`Variational.IsThetaStep` with $\theta = 1$) of the transport form on $V_h^{in}$ with zero
source functionals at both times. -/
theorem isThetaStep_of_equation_13_70 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    {hn : 0 < n} {Δt t₁ : ℝ} {un un1 : inflowSpace x r hn}
    (h : equation_13_70 hn ha ha₀ Δt t₁ 0 un un1) :
    Variational.IsThetaStep ((transportForm x r ha ha₀ t₁).restrict (inflowSpace x r hn))
      1 Δt 0 0 un un1 := fun v => by simpa using h v

/-- **Section 13.10.2** of [quarteroni2000numerical], stability of the backward Euler scheme
(13.70). Let $n \ge 1$, let $a$ and $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let $a$
be differentiable on $[\alpha, \beta]$ with $a'$ continuous there, let $\Delta t > 0$, and let
$\mu_0 \le a_0(x, t_1) - a'(x)/2$ for all $x \in [\alpha, \beta]$. If $u_h^{n+1}$ is a step of
(13.70) from $u_h^n$ at the time $t_1$ with $f = 0$, then
$$\frac{1}{2\Delta t} \bigl(\|u_h^{n+1}\|^2 - \|u_h^n\|^2\bigr) + \tfrac12 a(\beta)
  u_h^{n+1}(\beta)^2 + \mu_0 \|u_h^{n+1}\|^2 \le 0,$$
with the $L^2(\alpha, \beta)$ norm. No condition relates $\Delta t$ to the mesh.

**Correction.** The source prints the term $a(\beta)(u_h^{n+1}(\beta))^2$ without the factor
$\frac12$. The derivation that the source describes gives the factor: it tests with
$v_h = u_h^{n+1}$ and uses $(w - u, w) \ge \frac12 (\|w\|^2 - \|u\|^2)$ and the energy identity,
whose outflow term is $\frac12 a(\beta) v(\beta)^2$. The printed inequality is strictly stronger
and does not follow. -/
theorem equation_13_70_stability (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {Δt t₁ μ₀ : ℝ}
    (hΔt : 0 < Δt) (hμ₀ : ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t₁ - deriv a s / 2)
    {un un1 : inflowSpace x r hn} (h : equation_13_70 hn ha ha₀ Δt t₁ 0 un un1) :
    (2 * Δt)⁻¹ * (‖un1‖ ^ 2 - ‖un‖ ^ 2)
        + a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (un1 : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
        + μ₀ * ‖un1‖ ^ 2 ≤ 0 := by
  have hstep := (isThetaStep_of_equation_13_70 ha ha₀ h).norm_sq_add_two_mul_le hΔt
  have hb := le_transportForm_restrict ha ha₀ hd hd' hn hμ₀ un1
  have hkey : ‖un1‖ ^ 2 - ‖un‖ ^ 2 + 2 * Δt * (a (x (Fin.last n))
      * BrokenPolynomial.traceLeft (un1 : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
      + μ₀ * ‖un1‖ ^ 2) ≤ 0 := by nlinarith [hstep, hb, hΔt]
  have he : (2 * Δt)⁻¹ * (‖un1‖ ^ 2 - ‖un‖ ^ 2)
        + a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (un1 : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
        + μ₀ * ‖un1‖ ^ 2
      = (2 * Δt)⁻¹ * (‖un1‖ ^ 2 - ‖un‖ ^ 2 + 2 * Δt * (a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (un1 : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
          + μ₀ * ‖un1‖ ^ 2)) := by
    field_simp
    ring
  rw [he]
  have hpos : (0 : ℝ) < (2 * Δt)⁻¹ := by positivity
  nlinarith [hkey, hpos]

/-- **Section 13.10.2** of [quarteroni2000numerical], the summed stability estimate of (13.70). Let
$n \ge 1$, let $a$ and $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let $a$ be
differentiable on $[\alpha, \beta]$ with $a'$ continuous there, and let $\Delta t > 0$. Let
$\tau_0, \tau_1, \dots$ be times with $\mu_0 \le a_0(x, \tau_k) - a'(x)/2$ for all $k$ and all
$x \in [\alpha, \beta]$. Let $u_h^0, \dots, u_h^m \in V_h^{in}$, where each $u_h^{k+1}$ is a
step of (13.70) from $u_h^k$ at the time $\tau_k$ with $f = 0$. Then
$$\|u_h^m\|^2 + 2\Delta t \sum_{j=1}^m \bigl(\mu_0 \|u_h^j\|^2 + \tfrac12 a(\beta)
  u_h^j(\beta)^2\bigr) \le \|u_h^0\|^2,$$
with the $L^2(\alpha, \beta)$ norm.

**Reading.** The source prints the boundary term as $a(\beta)(u_h^{j+1}(\beta))^2$ summed over
$j = 1, \dots, m$. It is read as $u_h^j(\beta)^2$. The factor $\frac12$ is the correction of
`QuarteroniSaccoSaleri.Chapter13.equation_13_70_stability`.

**Typo.** The source drops the factor $\mu_0$ from $2\Delta t \sum_j \mu_0 \|u_h^j\|^2$.

The proof sums `QuarteroniSaccoSaleri.Chapter13.equation_13_70_stability` over the steps. The
reaction coefficient may depend on time. -/
theorem equation_13_70_sum (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {Δt μ₀ : ℝ}
    (hΔt : 0 < Δt) {τ : ℕ → ℝ} {uh : ℕ → inflowSpace x r hn} {m : ℕ}
    (hμ₀ : ∀ k, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s (τ k) - deriv a s / 2)
    (hstep : ∀ k < m, equation_13_70 hn ha ha₀ Δt (τ k) 0 (uh k) (uh (k + 1))) :
    ‖uh m‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range m, (μ₀ * ‖uh (k + 1)‖ ^ 2
        + a (x (Fin.last n)) * BrokenPolynomial.traceLeft
            (uh (k + 1) : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2)
      ≤ ‖uh 0‖ ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih fun k hk => hstep k (Nat.lt_succ_of_lt hk)
    have hlast := (isThetaStep_of_equation_13_70 ha ha₀
      (hstep m (Nat.lt_succ_self m))).norm_sq_add_two_mul_le hΔt
    have hb := le_transportForm_restrict ha ha₀ hd hd' hn (hμ₀ m) (uh (m + 1))
    rw [Finset.sum_range_succ, mul_add]
    nlinarith [hlast, hb, hΔt]

/-- **Section 13.10.2** of [quarteroni2000numerical], unconditional stability of (13.70). Let
$n \ge 1$, let $a$ and $a_0(\cdot, t)$ be integrable on $[\alpha, \beta]$, let $a$ be
differentiable on $[\alpha, \beta]$ with $a'$ continuous there, let $\Delta t > 0$,
$\mu_0 \ge 0$ and $a(\beta) \ge 0$. Let $\tau_0, \tau_1, \dots$ be times with
$\mu_0 \le a_0(x, \tau_k) - a'(x)/2$ for all $k$ and all $x \in [\alpha, \beta]$, and let
$u_h^0, \dots, u_h^m \in V_h^{in}$, where each $u_h^{k+1}$ is a step of (13.70) from $u_h^k$ at
the time $\tau_k$ with $f = 0$. Then $\|u_h^m\|_{L^2} \le \|u_h^0\|_{L^2}$, for every $m \ge 0$
and every time step $\Delta t > 0$.

**Reading.** The conclusion uses explicit nonnegativity of the bulk lower bound and the outflow
speed. -/
theorem equation_13_70_norm_le (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {Δt μ₀ : ℝ}
    (hΔt : 0 < Δt) (hμ : 0 ≤ μ₀) (hβ : 0 ≤ a (x (Fin.last n))) {τ : ℕ → ℝ}
    {uh : ℕ → inflowSpace x r hn} {m : ℕ}
    (hμ₀ : ∀ k, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s (τ k) - deriv a s / 2)
    (hstep : ∀ k < m, equation_13_70 hn ha ha₀ Δt (τ k) 0 (uh k) (uh (k + 1))) :
    ‖uh m‖ ≤ ‖uh 0‖ := by
  have hsum := equation_13_70_sum ha ha₀ hd hd' hΔt hμ₀ hstep
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range m, (μ₀ * ‖uh (k + 1)‖ ^ 2
      + a (x (Fin.last n)) * BrokenPolynomial.traceLeft
          (uh (k + 1) : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hle : ‖uh m‖ ^ 2 ≤ ‖uh 0‖ ^ 2 := by nlinarith [hsum, hnonneg, hΔt]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle

end Transport

end QuarteroniSaccoSaleri.Chapter13

end
