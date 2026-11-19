/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter13.Section06

/-!
# Conn, Gould and Toint, Section 13.9: Log barriers for general inequalities

This module formalizes the primal-dual logarithmic barrier method of [conn2000trust], Section 13.9,
for finitely many general inequality constraints $c_i(x) \ge 0$, $i \in \iota$, on a real normed
space $E$. For a barrier parameter $\mu > 0$ the barrier function is
$\phi(x) = f(x) - \mu \sum_i \log c_i(x)$. The Lagrangian is
$\ell(x, y) = f(x) - \sum_i y_i c_i(x)$, with dual variables $y_i > 0$. Algorithm 13.9.1 minimizes
$\phi$ for fixed $\mu$ by a trust-region method with the primal-dual model (13.9.4) and a
fraction-to-boundary test on every constraint. Algorithm 13.9.2 stops each inner run at the first
iterate that passes the outer stopping tests (13.9.6)–(13.9.8), and drives $\mu$ to zero.

Theorem 13.9.1 states that the outer stopping tests force the dual residual and the complementarity
products to zero, and give asymptotic nonnegativity of the Lagrangian Hessian on the nullspace of
the active constraint gradients. The barrier models of Section 13.6
(`ConnGouldToint.Chapter13.primalDualBarrierModel`) and the basic trust-region algorithm of Chapter
6 (`ConnGouldToint.Chapter06.btrRatio`, `ConnGouldToint.Chapter06.BTRRadiusUpdate`) supply the
ingredients.

## Main definitions

* Equation (13.9.4), `ConnGouldToint.Chapter13.generalPrimalDualBarrierModel`: the primal-dual model
  of the barrier term.
* Equation (13.9.6), `ConnGouldToint.Chapter13.generalBarrierDualResidual`: the dual residual
  $\nabla f(x) - \sum_i y_i \nabla c_i(x)$.
* Equation (13.9.8), `ConnGouldToint.Chapter13.generalBarrierLagrangianCurvature`: the quadratic
  form of the Lagrangian Hessian.
* Equations (13.9.6)–(13.9.8), `ConnGouldToint.Chapter13.GeneralPrimalDualBarrierStop`: the outer
  stopping tests.
* Algorithm 13.9.1, Step 3, `ConnGouldToint.Chapter13.generalBarrierAcceptanceRatio`: the reduction
  ratio with the fraction-to-boundary test.
* Algorithm 13.9.1, `ConnGouldToint.Chapter13.GeneralPrimalDualBarrierInnerRun`: a run of the inner
  trust-region iteration at a fixed barrier parameter.
* Algorithm 13.9.2, `ConnGouldToint.Chapter13.GeneralPrimalDualBarrierOuterRun`: a run of the outer
  iteration.

## Main results

* Theorem 13.9.1, `ConnGouldToint.Chapter13.theorem_13_9_1`: points that pass the stopping tests
  with vanishing tolerances satisfy the first-order conditions and the weak second-order condition
  in the limit.

## Deviations from the source

* **Representation.** The general barrier formulas use Fréchet derivatives and the positive barrier
  quadratic term. See `ConnGouldToint.Chapter13.generalPrimalDualBarrierModel`,
  `ConnGouldToint.Chapter13.generalBarrierDualResidual`,
  `ConnGouldToint.Chapter13.generalBarrierLagrangianCurvature`.
* **Reading.** The general stopping test uses componentwise complementarity, homogeneous curvature
  and strict primal-dual positivity. See `ConnGouldToint.Chapter13.GeneralPrimalDualBarrierStop`.
* **Representation.** The algorithms are presented as runs with an explicit slack-fraction guard and
  stopping conditions. See `ConnGouldToint.Chapter13.generalBarrierAcceptanceRatio`,
  `ConnGouldToint.Chapter13.GeneralPrimalDualBarrierInnerRun`,
  `ConnGouldToint.Chapter13.GeneralPrimalDualBarrierOuterRun`.
* **Generalization.** The curvature limit uses the unit ball and does not need the separate
  multiplier-error condition. See `ConnGouldToint.Chapter13.theorem_13_9_1`.
* **Equation (13.9.7)** (reading). The complementarity residual $C(x) y - \mu e$ is a vector, and
  the test bounds each component. See `ConnGouldToint.Chapter13.GeneralPrimalDualBarrierStop`.
* **Theorem 13.9.1** (reading). The infimum in (13.9.11) is over unit directions, as in the proof.
  See `ConnGouldToint.Chapter13.theorem_13_9_1`.
* **Theorem 13.9.1** (generalization). The multiplier-error assumption (13.9.10) is not needed: the
  complementarity test controls the barrier curvature on the inactive constraints. See
  `ConnGouldToint.Chapter13.theorem_13_9_1`.
-/

open Filter Set
open scoped Topology

namespace ConnGouldToint.Chapter13

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- **Equation (13.9.4)** of [conn2000trust]. Let $c_i : E \to \mathbb{R}$, $i \in \iota$, be the
constraint functions, let $x, s \in E$, $y \in \mathbb{R}^\iota$ and $\mu \in \mathbb{R}$. The
**primal-dual model of the barrier term** at $x$ for the step $s$ is
$$-\mu \sum_i \log c_i(x) - \mu \sum_i \frac{c_i'(x) s}{c_i(x)} + \frac12 \sum_i
  \frac{y_i}{c_i(x)} (c_i'(x) s)^2 - \frac12 \sum_i y_i\, c_i''(x)[s, s].$$

The first three terms are `ConnGouldToint.Chapter13.primalDualBarrierModel` applied to the
constraint values $c_i(x)$, the dual vector $y$ and the linearized steps $c_i'(x) s$.
Derivatives are Fréchet derivatives `fderiv`.

**Reading.** The residual and second derivative are expressed as a continuous linear functional and
its quadratic form. The model uses the positive diagonal term of the corrected primal-dual barrier
model, with the constraint-Hessian term subtracted.
-/
noncomputable def generalPrimalDualBarrierModel
    (c : ι → E → ℝ) (x s : E) (y : ι → ℝ) (μ : ℝ) : ℝ :=
  primalDualBarrierModel (fun i ↦ c i x) y (fun i ↦ fderiv ℝ (c i) x s) μ -
    (1 / 2 : ℝ) * ∑ i, y i * fderiv ℝ (fderiv ℝ (c i)) x s s

/-- **Equation (13.9.6)** of [conn2000trust]. The **dual residual** of $(x, y)$ is the covector
$$\nabla f(x) - \sum_i y_i \nabla c_i(x),$$
the derivative of the Lagrangian $\ell(\cdot, y) = f - \sum_i y_i c_i$ at $x$.

The residual is an element of the dual space `E →L[ℝ] ℝ`, and its norm is the operator norm.

**Reading.** The residual and second derivative are expressed as a continuous linear functional and
its quadratic form. The model uses the positive diagonal term of the corrected primal-dual barrier
model, with the constraint-Hessian term subtracted.
-/
noncomputable def generalBarrierDualResidual
    (f : E → ℝ) (c : ι → E → ℝ) (x : E) (y : ι → ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ f x - ∑ i, y i • fderiv ℝ (c i) x

/-- **Equation (13.9.8)** of [conn2000trust], Lagrangian Hessian. The quadratic form of the Hessian
of the Lagrangian in the direction $d$ is
$$f''(x)[d, d] - \sum_i y_i\, c_i''(x)[d, d].$$

**Reading.** The residual and second derivative are expressed as a continuous linear functional and
its quadratic form. The model uses the positive diagonal term of the corrected primal-dual barrier
model, with the constraint-Hessian term subtracted.
-/
noncomputable def generalBarrierLagrangianCurvature
    (f : E → ℝ) (c : ι → E → ℝ) (x : E) (y : ι → ℝ) (d : E) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x d d - ∑ i, y i * fderiv ℝ (fderiv ℝ (c i)) x d d

/-- **Equations (13.9.6)–(13.9.8)** of [conn2000trust], the outer stopping tests of Algorithm
13.9.2. The pair $(x, y)$ passes the tests with barrier parameter $\mu$ and tolerances
$\epsilon_D$, $\epsilon_C$, $\epsilon_E$ if $c_i(x) > 0$ and $y_i > 0$ for all $i$,
$$\Big\|\nabla f(x) - \sum_i y_i \nabla c_i(x)\Big\| \le \epsilon_D, \qquad |c_i(x) y_i - \mu|
  \le \epsilon_C \text{ for all } i,$$
and for every $d \in E$
$$f''(x)[d, d] - \sum_i y_i\, c_i''(x)[d, d] + \sum_i \frac{y_i}{c_i(x)} (c_i'(x) d)^2 \ge
  -\epsilon_E \|d\|^2.$$

**Reading.** In (13.9.7) the left side $C(x) y$ of the complementarity residual is a vector, so
the right side is read as the vector $\mu e$. The test bounds each component of
$C(x) y - \mu e$.

**Reading.** The printed complementarity expression is presented as a norm and mixes a vector with
identity notation. The formal residual is a vector tested componentwise. Curvature is tested
homogeneously on all directions and the current slack and multiplier are strictly positive.
-/
def GeneralPrimalDualBarrierStop (f : E → ℝ) (c : ι → E → ℝ) (x : E)
    (y : ι → ℝ) (μ εD εC εE : ℝ) : Prop :=
  (∀ i, 0 < c i x ∧ 0 < y i) ∧ ‖generalBarrierDualResidual f c x y‖ ≤ εD ∧
  (∀ i, |c i x * y i - μ| ≤ εC) ∧
  ∀ d : E, -εE * ‖d‖ ^ 2 ≤ generalBarrierLagrangianCurvature f c x y d +
    ∑ i, (y i / c i x) * (fderiv ℝ (c i) x d) ^ 2

/-- **Algorithm 13.9.1** of [conn2000trust], Step 3. Let $\phi$ be the barrier function, $m$ the
model, $\sigma$ the fraction-to-boundary parameter and $s$ the trial step at $x$. The
**acceptance ratio** is the usual reduction ratio
$$\rho = \frac{\phi(x) - \phi(x + s)}{m(x) - m(x + s)}$$
if $c_i(x + s) \ge \sigma c_i(x)$ for every $i$, and $0$ otherwise.

The value $0$ stands for rejection: it is below both acceptance thresholds, which are positive.
The ratio is `ConnGouldToint.Chapter06.btrRatio`.

**Reading.** The inner and outer algorithms are run predicates with explicit model, positivity and
accepted update conditions. The acceptance ratio is zero when the componentwise slack fraction
fails.
-/
noncomputable def generalBarrierAcceptanceRatio (c : ι → E → ℝ)
    (σ : ℝ) (φ m : E → ℝ) (x s : E) : ℝ :=
  open Classical in
  if ∀ i, σ * c i x ≤ c i (x + s) then Chapter06.btrRatio φ m x s else 0

/-- **Algorithm 13.9.1** of [conn2000trust]. A run of the inner trust-region iteration for the
barrier function $\phi(x) = f(x) - \mu \sum_i \log c_i(x)$ with fixed barrier parameter
$\mu > 0$ and fraction-to-boundary parameter $\sigma \in (0, 1)$. It consists of primal iterates
$x_j$, positive dual iterates $y_j$, steps $s_j$, radii $\Delta_j$ and models
$m_j = m_j^f + (\text{barrier model (13.9.4)})$, where the objective model $m_j^f$ agrees with
$f$ to first order at $x_j$ and has bounded Hessian on the strictly feasible part of the trust
region. Each step satisfies $\|s_j\| \le \Delta_j$, has positive predicted decrease and
satisfies the sufficient decrease test
$$\kappa \max\Big\{ g_j \min\Big\{\frac{g_j}{\beta_j}, \Delta_j\Big\},\ -\tau_j \min\{\tau_j^2,
  \Delta_j^2\} \Big\} \le m_j(x_j) - m_j(x_j + s_j),$$
where $g_j = \|\nabla m_j(x_j)\|$, $\beta_j = 1 + \sup_{\|v - x_j\| \le \Delta_j} \|\nabla^2
m_j(v)\|$ and $\tau_j = \min\{0, \inf_{\|v\| = 1} \nabla^2 m_j(x_j)[v, v]\}$. The step is
accepted when the ratio of `ConnGouldToint.Chapter13.generalBarrierAcceptanceRatio` is at least
$\eta_1$, and the radius follows the update rule (6.1.5).

Step 2 uses the ordinary sufficient decrease test, without a cap. The structure fixes no update
rule for the dual iterates; it requires only that they are positive.

**Reading.** The inner and outer algorithms are run predicates with explicit model, positivity and
accepted update conditions. The acceptance ratio is zero when the componentwise slack fraction
fails.
-/
structure GeneralPrimalDualBarrierInnerRun [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Chapter06.BTRParams) (f : E → ℝ) (c : ι → E → ℝ) (σ μ : ℝ) where
  /-- The primal iterates $x_j$. -/
  x : ℕ → E
  /-- The dual iterates $y_j$. -/
  y : ℕ → ι → ℝ
  /-- The trial steps $s_j$. -/
  s : ℕ → E
  /-- The trust-region radii $\Delta_j$. -/
  Δ : ℕ → ℝ
  /-- The models $m_j^f$ of the objective $f$. -/
  objectiveModel : ℕ → E → ℝ
  /-- The models $m_j$ of the barrier function. -/
  model : ℕ → E → ℝ
  /-- The curvature constants $\beta_j$ of the sufficient decrease test. -/
  β : ℕ → ℝ
  /-- The nonpositive least curvatures $\tau_j$ of the models at the iterates. -/
  τ : ℕ → ℝ
  /-- The constant $\kappa$ of the sufficient decrease test. -/
  κ : ℝ
  /-- The fraction-to-boundary parameter satisfies $0 < \sigma < 1$. -/
  fraction : σ ∈ Ioo (0 : ℝ) 1
  /-- The barrier parameter is positive. -/
  barrier_parameter_pos : 0 < μ
  /-- The starting point is strictly feasible: $c_i(x_0) > 0$ for all $i$. -/
  initial_slack_pos : ∀ i, 0 < c i (x 0)
  /-- The initial radius is positive. -/
  initial_radius_pos : 0 < Δ 0
  /-- Every dual iterate is positive: $y_{j, i} > 0$ for all $j$ and $i$. -/
  dual_pos : ∀ j i, 0 < y j i
  /-- The model is the objective model plus the barrier model (13.9.4): $m_j(x_j + v) = m_j^f(x_j +
  v) + (\text{barrier model at } x_j \text{ for } v)$. -/
  model_formula : ∀ j v, model j (x j + v) =
    objectiveModel j (x j + v) + generalPrimalDualBarrierModel c (x j) v (y j) μ
  /-- The objective model agrees with $f$ to first order at the iterate: $m_j^f(x_j) = f(x_j)$ and
  $\nabla m_j^f(x_j) = \nabla f(x_j)$. -/
  model_center : ∀ j, objectiveModel j (x j) = f (x j) ∧
    fderiv ℝ (objectiveModel j) (x j) = fderiv ℝ f (x j)
  /-- The objective model and its derivative are differentiable on the closed ball of radius
  $\Delta_j$ about $x_j$. -/
  model_twice_differentiable : ∀ j,
    DifferentiableOn ℝ (objectiveModel j) (Metric.closedBall (x j) (Δ j)) ∧
    DifferentiableOn ℝ (fderiv ℝ (objectiveModel j)) (Metric.closedBall (x j) (Δ j))
  /-- There is a constant $K$ with $\|\nabla^2 m_j^f(v)\| \le K$ for all $j$ and all strictly
  feasible $v$ in the closed ball of radius $\Delta_j$ about $x_j$. -/
  model_hessian_bound : ∃ K : ℝ, ∀ j v, v ∈ Metric.closedBall (x j) (Δ j) →
    (∀ i, 0 < c i v) → ‖fderiv ℝ (fderiv ℝ (objectiveModel j)) v‖ ≤ K
  /-- The curvature constant is $\beta_j = 1 + \sup \{\|\nabla^2 m_j(v)\| : \|v - x_j\| \le
  \Delta_j\}$. -/
  curvature_model : ∀ j, β j = 1 + sSup
    ((fun v ↦ ‖fderiv ℝ (fderiv ℝ (model j)) v‖) '' Metric.closedBall (x j) (Δ j))
  /-- The least curvature is $\tau_j = \min\{0, \inf \{\nabla^2 m_j(x_j)[v, v] : \|v\| = 1\}\}$. -/
  nonpositive_least_curvature : ∀ j, τ j = min 0
    (sInf ((fun v ↦ fderiv ℝ (fderiv ℝ (model j)) (x j) v v) '' Metric.sphere 0 1))
  /-- The step lies in the trust region: $\|s_j\| \le \Delta_j$. -/
  feasible_step : ∀ j, ‖s j‖ ≤ Δ j
  /-- The constant of the sufficient decrease test is positive. -/
  decrease_constant : 0 < κ
  /-- The step satisfies the sufficient decrease test $\kappa \max\{g_j \min\{g_j / \beta_j,
  \Delta_j\}, -\tau_j \min\{\tau_j^2, \Delta_j^2\}\} \le m_j(x_j) - m_j(x_j + s_j)$, with
  $g_j = \|\nabla m_j(x_j)\|$. -/
  sufficient_decrease : ∀ j,
    let g := ‖gradient (model j) (x j)‖
    κ * max (g * min (g / β j) (Δ j)) (-τ j * min (τ j ^ 2) (Δ j ^ 2)) ≤
      model j (x j) - model j (x j + s j)
  /-- The predicted decrease $m_j(x_j) - m_j(x_j + s_j)$ is positive. -/
  predicted_pos : ∀ j, 0 < model j (x j) - model j (x j + s j)
  /-- The trial point $x_j + s_j$ is accepted if and only if the acceptance ratio for the barrier
  function is at least $\eta_1$. -/
  iterate_update : ∀ j,
    let φ := fun v ↦ f v + logBarrier (fun i ↦ c i v) μ
    x (j + 1) = if P.η₁ ≤ generalBarrierAcceptanceRatio c σ φ (model j) (x j) (s j)
      then x j + s j else x j
  /-- The radius follows the update rule (6.1.5) with the acceptance ratio for the barrier function.
  -/
  radius_update : ∀ j,
    let φ := fun v ↦ f v + logBarrier (fun i ↦ c i v) μ
    Chapter06.BTRRadiusUpdate P (generalBarrierAcceptanceRatio c σ φ (model j) (x j) (s j))
      (Δ j) (Δ (j + 1))

/-- **Algorithm 13.9.2** of [conn2000trust]. A run of the outer iteration consists of points $x_k$,
positive dual vectors $y_k$, barrier parameters $\mu_k \to 0$, fraction-to-boundary parameters
$\sigma_k$ and, for each $k$, an inner run of Algorithm 13.9.1 with parameters $\sigma_k$ and
$\mu_k$. The inner run $k$ starts at $(x_k, y_k)$. It ends at $(x_{k+1}, y_{k+1})$, its first
iterate that passes the stopping tests (13.9.6)–(13.9.8) with tolerances $\epsilon_D(\mu_k)$,
$\epsilon_C(\mu_k)$ and $\epsilon_E(\mu_k)$. The tolerance functions are positive on
$(0, \infty)$ and tend to zero as $\mu \to 0^+$.

The barrier parameters are positive because each inner run requires it.

**Reading.** The inner and outer algorithms are run predicates with explicit model, positivity and
accepted update conditions. The acceptance ratio is zero when the componentwise slack fraction
fails.
-/
structure GeneralPrimalDualBarrierOuterRun [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Chapter06.BTRParams) (f : E → ℝ) (c : ι → E → ℝ) where
  /-- The outer iterates $x_k$. -/
  x : ℕ → E
  /-- The outer dual iterates $y_k$. -/
  y : ℕ → ι → ℝ
  /-- The barrier parameters $\mu_k$. -/
  μ : ℕ → ℝ
  /-- The fraction-to-boundary parameters $\sigma_k$ of the inner runs. -/
  σ : ℕ → ℝ
  /-- The dual-residual tolerance $\epsilon_D(\mu)$, as a function of the barrier parameter. -/
  εD : ℝ → ℝ
  /-- The complementarity tolerance $\epsilon_C(\mu)$, as a function of the barrier parameter. -/
  εC : ℝ → ℝ
  /-- The curvature tolerance $\epsilon_E(\mu)$, as a function of the barrier parameter. -/
  εE : ℝ → ℝ
  /-- The starting point is strictly feasible: $c_i(x_0) > 0$ for all $i$. -/
  initial_slack_pos : ∀ i, 0 < c i (x 0)
  /-- The starting dual vector is positive. -/
  initial_dual_pos : ∀ i, 0 < y 0 i
  /-- The three tolerances are positive at every positive barrier parameter. -/
  forcing_pos : ∀ μ > 0, 0 < εD μ ∧ 0 < εC μ ∧ 0 < εE μ
  /-- The three tolerances tend to zero as $\mu \to 0^+$. -/
  forcing_limit : Tendsto εD (𝓝[>] 0) (𝓝 0) ∧ Tendsto εC (𝓝[>] 0) (𝓝 0) ∧
    Tendsto εE (𝓝[>] 0) (𝓝 0)
  /-- The barrier parameters tend to zero. -/
  parameter_limit : Tendsto μ atTop (𝓝 0)
  /-- The inner run of Algorithm 13.9.1 at outer iteration $k$, with parameters $\sigma_k$ and
  $\mu_k$. -/
  inner : ∀ k, GeneralPrimalDualBarrierInnerRun P f c (σ k) (μ k)
  /-- The index at which the inner run $k$ stops. -/
  stopIndex : ℕ → ℕ
  /-- The inner run $k$ starts at $(x_k, y_k)$. -/
  start_inner : ∀ k, (inner k).x 0 = x k ∧ (inner k).y 0 = y k
  /-- The inner run $k$ ends at $(x_{k+1}, y_{k+1})$ at its stopping index. -/
  finish_inner : ∀ k, (inner k).x (stopIndex k) = x (k + 1) ∧
    (inner k).y (stopIndex k) = y (k + 1)
  /-- The point $(x_{k+1}, y_{k+1})$ passes the stopping tests with parameter $\mu_k$ and tolerances
  $\epsilon_D(\mu_k)$, $\epsilon_C(\mu_k)$, $\epsilon_E(\mu_k)$. -/
  stopping_test : ∀ k, GeneralPrimalDualBarrierStop f c (x (k + 1)) (y (k + 1)) (μ k)
    (εD (μ k)) (εC (μ k)) (εE (μ k))
  /-- No earlier iterate of the inner run $k$ passes the stopping tests. -/
  first_stop : ∀ k j, j < stopIndex k →
    ¬ GeneralPrimalDualBarrierStop f c ((inner k).x j) ((inner k).y j) (μ k)
      (εD (μ k)) (εC (μ k)) (εE (μ k))

/-- **Theorem 13.9.1** of [conn2000trust]. Let $(x_k, y_k)$ be indexed along a filter $l$, and let
$\mu_k$, $\epsilon_{D,k}$, $\epsilon_{C,k}$, $\epsilon_{E,k}$ tend to zero along $l$, with
$\epsilon_{E,k} \ge 0$. Suppose that $\|c_i'(x_k)\| \le K$ for all $k$ and $i$, with $K \ge 0$,
and that each $(x_k, y_k)$ passes the stopping tests (13.9.6)–(13.9.8) with parameter $\mu_k$
and these tolerances. Then along $l$
$$\Big\|\nabla f(x_k) - \sum_i y_{k,i} \nabla c_i(x_k)\Big\| \to 0 \quad\text{and}\quad
  c_i(x_k)\, y_{k,i} \to 0 \text{ for all } i.$$
Moreover, let $\mathcal{A} \subseteq \iota$ be a set such that every constraint
$i \notin \mathcal{A}$ satisfies $c_i(x_k) \ge \delta_i$ eventually along $l$ for some
$\delta_i > 0$. Then for every $\eta > 0$, eventually along $l$,
$$f''(x_k)[d, d] - \sum_i y_{k,i}\, c_i''(x_k)[d, d] \ge -\eta$$
for every $d$ with $\|d\| \le 1$ and $c_i'(x_k) d = 0$ for all $i \in \mathcal{A}$.

**Reading.** The infimum in the second-order conclusion (13.9.11) is taken over unit directions,
as in the proof of the source.

**Generalization.** The source also assumes the multiplier-error condition (13.9.10). It is not
needed: on the constraints outside $\mathcal{A}$, the complementarity test gives
$y_{k,i} / c_i(x_k) \to 0$, so the barrier curvature term of the stopping test vanishes on the
directions that the conclusion considers.

The first-order limits follow directly from the stopping tests.

**Generalization.** The theorem works along a filter for points passing the stopping tests. It omits
the printed multiplier-error hypothesis and requires a bound on constraint derivatives. The uniform
curvature condition is stated over the closed unit ball and tangent directions to the specified
active constraints.
-/
theorem theorem_13_9_1 {α : Type*} {l : Filter α} {f : E → ℝ} {c : ι → E → ℝ}
    {x : α → E} {y : α → ι → ℝ} {μ εD εC εE : α → ℝ} {K : ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hD : Tendsto εD l (𝓝 0))
    (hC : Tendsto εC l (𝓝 0)) (hE : Tendsto εE l (𝓝 0)) (hEpos : ∀ k, 0 ≤ εE k)
    (hK : 0 ≤ K) (hA : ∀ k i, ‖fderiv ℝ (c i) (x k)‖ ≤ K)
    (hs : ∀ k, GeneralPrimalDualBarrierStop f c (x k) (y k) (μ k) (εD k) (εC k) (εE k)) :
    Tendsto (fun k ↦ ‖generalBarrierDualResidual f c (x k) (y k)‖) l (𝓝 0) ∧
    Tendsto (fun k i ↦ c i (x k) * y k i) l (𝓝 0) ∧
    ∀ active : Set ι, (∀ i ∉ active, ∃ δ > 0, ∀ᶠ k in l, δ ≤ c i (x k)) →
      ∀ η, 0 < η → ∀ᶠ k in l, ∀ d : E, ‖d‖ ≤ 1 →
        (∀ i ∈ active, fderiv ℝ (c i) (x k) d = 0) →
        -η ≤ generalBarrierLagrangianCurvature f c (x k) (y k) d := by
  classical
  have hp (i : ι) : Tendsto (fun k ↦ c i (x k) * y k i) l (𝓝 0) := by
    have he : Tendsto (fun k ↦ c i (x k) * y k i - μ k) l (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun k ↦ by
        simpa only [Real.norm_eq_abs] using (hs k).2.2.1 i) hC
    simpa only [sub_add_cancel, add_zero] using he.add hμ
  refine ⟨squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ (hs k).2.1) hD,
    tendsto_pi_nhds.mpr hp, ?_⟩
  intro active hfree η hη
  let b (k : α) (i : ι) := if i ∈ active then 0 else (y k i / c i (x k)) * K ^ 2
  have hb : Tendsto (fun k ↦ ∑ i, b k i) l (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    apply tendsto_finsetSum Finset.univ
    intro i _
    by_cases ha : i ∈ active
    · simpa [b, ha] using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ)) l (𝓝 0))
    obtain ⟨δ, hδ, hxi⟩ := hfree i ha
    have hr : Tendsto (fun k ↦ y k i / c i (x k)) l (𝓝 0) := by
      apply squeeze_zero' (g := fun k ↦ (c i (x k) * y k i) / δ ^ 2)
      · exact Eventually.of_forall fun k ↦ div_nonneg ((hs k).1 i).2.le ((hs k).1 i).1.le
      · filter_upwards [hxi] with k hk
        have hpos := ((hs k).1 i).1
        have he : y k i / c i (x k) = (c i (x k) * y k i) / (c i (x k)) ^ 2 := by
          field_simp [hpos.ne']
        rw [he]
        exact div_le_div_of_nonneg_left (mul_nonneg hpos.le ((hs k).1 i).2.le)
          (sq_pos_of_pos hδ) ((sq_le_sq₀ hδ.le hpos.le).mpr hk)
      · simpa using (hp i).div_const (δ ^ 2)
    simpa [b, ha] using hr.mul_const (K ^ 2)
  have hlim : Tendsto (fun k ↦ εE k + ∑ i, b k i) l (𝓝 0) := by simpa using hE.add hb
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with k hk
  intro d hd hactive
  have hcorr : (∑ i, (y k i / c i (x k)) * (fderiv ℝ (c i) (x k) d) ^ 2) ≤ ∑ i, b k i := by
    apply Finset.sum_le_sum
    intro i _
    by_cases ha : i ∈ active
    · simp [b, ha, hactive i ha]
    · simp only [b, ite_eq_right ha]
      apply mul_le_mul_of_nonneg_left _ (div_nonneg ((hs k).1 i).2.le ((hs k).1 i).1.le)
      rw [← sq_abs (fderiv ℝ (c i) (x k) d)]
      apply (sq_le_sq₀ (abs_nonneg _) hK).mpr
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ (c i) (x k)).le_opNorm d).trans <|
        (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans (by simpa using hA k i)
  have hmul := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg d) zero_le_one).mpr hd) (hEpos k)
  norm_num at hmul
  linarith [(hs k).2.2.2 d]

end ConnGouldToint.Chapter13
