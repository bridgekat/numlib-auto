/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter15.Section04

/-!
# Conn, Gould and Toint, Section 15.4: Composite-step and infeasibility-reducing SQP variants

This module defines one iteration of the SQP variants of Algorithms 15.4.5–15.4.8 of [conn2000trust]
for the problem of minimizing $f(x)$ subject to $c(x) = 0$. The Byrd–Omojokun variants, Algorithms
15.4.5–15.4.7, keep the composite step $s = n + t$, the penalty update and the ratio test of
Algorithm 15.4.1, and replace individual step conditions. Algorithm 15.4.5 uses a normal step $n$
with a Cauchy-type decrease of $\|c(x) + A n\|$ and a decomposition into row-space and null-space
components (AA.1j and AA.1k). Algorithm 15.4.6 adds a second-order correction, and Algorithm 15.4.7
adds the negative-curvature condition AA.2d to the tangential step. The infeasibility-reducing
Algorithm 15.4.8 works on the primal and multiplier variables $z = (x, y)$ with the augmented merit
function
$$\phi(x, y) = f(x) - \langle c(x), y\rangle + \frac{\sigma}{2} \|c(x)\|^2,$$
and chooses the penalty $\sigma$ so that the predicted decrease is at least $\frac{\nu\sigma}{2}$
times the decrease of the squared linearized residual (15.4.171). The models and the penalty update
are those of `NumlibSurface.ConnGouldToint.Chapter15.Section04`.

## Main definitions

* Algorithm 15.4.8, Step 0, `ConnGouldToint.Chapter15.SQPVariantParams`: the trust-region parameters
  and the penalty constants.
* Algorithm 15.4.5, AA.1j and AA.1k, `ConnGouldToint.Chapter15.ByrdOmojokunNormalStep`: the
  conditions on the Byrd–Omojokun normal step.
* Algorithm 15.4.7, AA.1i and AA.2d, `ConnGouldToint.Chapter15.SQPSecondOrderTangentialStep`: the
  conditions on the second-order tangential step.
* Algorithms 15.4.5 and 15.4.7, `ConnGouldToint.Chapter15.SQPCompositeTrial`: the local data of a
  composite trial.
* Algorithm 15.4.1, Step 2, `ConnGouldToint.Chapter15.SQPCompositeTrial.penalty`: the inherited
  penalty update.
* Algorithms 15.4.5 and 15.4.7, `ConnGouldToint.Chapter15.SQPCompositeTrial.prediction`: the
  predicted decrease of the original composite trial.
* AA.1i, `ConnGouldToint.Chapter15.SQPCompositeTrial.cauchy`: the first-order tangential condition.
* Algorithm 15.4.5, `ConnGouldToint.Chapter15.algorithm_15_4_5`: one iteration with the
  Byrd–Omojokun normal step.
* Algorithm 15.4.6 and (15.4.153)–(15.4.156), `ConnGouldToint.Chapter15.algorithm_15_4_6`: one
  iteration with a second-order correction.
* Algorithm 15.4.7, `ConnGouldToint.Chapter15.algorithm_15_4_7`: one iteration of Algorithm 15.4.6
  with AA.2d.
* Section 15.4.3, `ConnGouldToint.Chapter15.infeasibilitySQPMerit`: the augmented merit function.
* Section 15.4.3, `ConnGouldToint.Chapter15.infeasibilitySQPModel`: the augmented model.
* Algorithm 15.4.8, Step 2, `ConnGouldToint.Chapter15.infeasibilitySQPPenaltyRequired`: the
  corrected required penalty.
* Algorithm 15.4.8, `ConnGouldToint.Chapter15.algorithm_15_4_8`: one iteration of the
  infeasibility-reducing algorithm.

## Main results

* Equation (15.4.121),
  `ConnGouldToint.Chapter15.ByrdOmojokunNormalStep.eq_zero_of_normal_stationary`: at a point with
  $A^* c = 0$ the normal step is zero.
* Algorithm 15.4.8, Step 2, `ConnGouldToint.Chapter15.infeasibilitySQPModel_zero`: the augmented
  model and the merit function agree at the center.
* Equation (15.4.171), `ConnGouldToint.Chapter15.infeasibilitySQPModel_drop`: the predicted decrease
  splits into the penalized decrease of the squared residual and the change of the other model
  terms.
* Equation (15.4.171), `ConnGouldToint.Chapter15.infeasibilitySQPPenaltyRequired_le_iff`: a penalty
  above the required value is exactly a penalty that satisfies (15.4.171).
* Algorithm 15.4.8, Step 2,
  `ConnGouldToint.Chapter15.infeasibilitySQPPenalty_printed_sign_counterexample`: the printed sign
  of the threshold can give a penalty that violates (15.4.171).
* Algorithm 15.4.8, Steps 2–4, `ConnGouldToint.Chapter15.algorithm_15_4_8_invariants`: an iteration
  keeps a positive radius, does not decrease the penalty, and satisfies (15.4.171).

## Conventions

* The Lagrangian is $f(x) - \langle c(x), y\rangle$: the constraint pairing is subtracted.

## Implementation notes

* An iteration is a predicate on the current data and the next iterate, radius and penalty. Each
  predicate requires a positive predicted decrease, so it describes only iterations that do not
  stop.
* The trust-region norm is a seminorm $p$ on $E$ with $p(v) = 0$ only for $v = 0$.
* In Algorithm 15.4.8 the step selection is a supplied predicate `approximate` for an approximate
  minimizer of the quadratic model on the stated feasible set. The multiplier component of the step
  is free.

## Deviations from the source

* **Algorithms 15.4.6 and 15.4.7, acceptance** (reading). The corrected trial is tested against the
  predicted decrease of the original composite trial, and a correction is tried only if it satisfies
  the norm cap. See `ConnGouldToint.Chapter15.algorithm_15_4_6`.
* **Section 15.4.3, augmented model** (correction). The constant term of the model is the Lagrangian
  value $f(x) - \langle c(x), y\rangle$, so that the squared residual penalty is counted once and
  the model agrees with the merit function at the center. See
  `ConnGouldToint.Chapter15.infeasibilitySQPModel`.
* **Algorithm 15.4.8, Step 2** (correction). The penalty threshold has the term
  $+2\delta_F / ((1 - \nu)\delta_N)$. The printed negative sign can leave the penalty too small for
  (15.4.171). See `ConnGouldToint.Chapter15.infeasibilitySQPPenalty_printed_sign_counterexample`.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

open Chapter06

/-- **Algorithm 15.4.8** of [conn2000trust], Step 0. The parameters of the SQP variants extend those
of the basic trust-region algorithm (`ConnGouldToint.Chapter06.BTRParams`) by a penalty fraction
$\nu \in (0, 1)$ and penalty growth constants $\tau_1 > 1$ and $\tau_2 > 0$. -/
structure SQPVariantParams extends BTRParams where
  /-- The fraction $\nu$ in the penalty thresholds. -/
  ν : ℝ
  /-- The growth factor $\tau_1$ of the penalty update. -/
  τ₁ : ℝ
  /-- The growth increment $\tau_2$ of the penalty update. -/
  τ₂ : ℝ
  /-- The penalty fraction is positive: $\nu > 0$. -/
  nu_pos : 0 < ν
  /-- The penalty fraction is below one: $\nu < 1$. -/
  nu_lt_one : ν < 1
  /-- The penalty grows by a factor larger than one: $\tau_1 > 1$. -/
  tau₁_gt_one : 1 < τ₁
  /-- The penalty grows by a positive increment: $\tau_2 > 0$. -/
  tau₂_pos : 0 < τ₂

/-! ### Byrd–Omojokun composite-step variants -/

section CompositeSteps

variable {E F U V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **Algorithm 15.4.5** of [conn2000trust], AA.1j and AA.1k. Let $A : E \to F$ be the constraint
Jacobian, $c \in F$ the constraint value and $p$ the trust-region norm. A normal step $n$ with
components $n_R \in U$ and $n_N \in V$ is a **Byrd–Omojokun normal step** if

* $p(n) \le \xi_N \Delta$;
* $\|c\| - \|c + A n\| \ge \kappa \dfrac{\|A^* c\|}{\|c\|} \min\Big\{\xi_N \Delta, \dfrac{\|A^*
  c\|}{\beta}\Big\}$;
* $R : U \to E$ and $N : V \to E$ are injective linear maps with ranges
  $\operatorname{range} A^*$ and $\ker A$, and $n = R n_R + N n_N$;
* $\|n_N\| \le \kappa_{drs} \|n_R\|$, and $n_R = 0$ if $A^* c = 0$.

The quotient $\|A^* c\| / \|c\|$ is $0$ when $c = 0$. -/
structure ByrdOmojokunNormalStep (c : F) (A : E →L[ℝ] F) (p : Seminorm ℝ E)
    (ξN Δ κ β κdrs : ℝ) (R : U →ₗ[ℝ] E) (N : V →ₗ[ℝ] E)
    (n : E) (nR : U) (nN : V) : Prop where
  /-- The normal step lies in its part of the trust region: $p(n) \le \xi_N \Delta$. -/
  radius : p n ≤ ξN * Δ
  /-- The normal step gives a Cauchy-type decrease of the linearized residual norm $\|c + A n\|$. -/
  decrease : κ * (‖A.adjoint c‖ / ‖c‖) *
    min (ξN * Δ) (‖A.adjoint c‖ / β) ≤ ‖c‖ - sqpNormalModel c A n
  /-- The range of $R$ is the range of $A^*$. -/
  row_range : LinearMap.range R = LinearMap.range A.adjoint.toLinearMap
  /-- The range of $N$ is the null space of $A$. -/
  null_range : LinearMap.range N = LinearMap.ker A.toLinearMap
  /-- The row-space coordinate map $R$ is injective. -/
  row_injective : Function.Injective R
  /-- The null-space coordinate map $N$ is injective. -/
  null_injective : Function.Injective N
  /-- The normal step is the sum of its row-space and null-space components: $n = R n_R + N n_N$. -/
  decomposition : n = R nR + N nN
  /-- The null-space component is bounded by the row-space component:
  $\|n_N\| \le \kappa_{drs} \|n_R\|$. -/
  null_bound : ‖nN‖ ≤ κdrs * ‖nR‖
  /-- At a normal-stationary point, $A^* c = 0$, the row-space component is zero. -/
  stationary_row : A.adjoint c = 0 → nR = 0

omit [CompleteSpace V] in
/-- **Equation (15.4.121)** of [conn2000trust]. If $n$ is a Byrd–Omojokun normal step and
$A^* c = 0$, then $n = 0$. -/
theorem ByrdOmojokunNormalStep.eq_zero_of_normal_stationary
    {c : F} {A : E →L[ℝ] F} {p : Seminorm ℝ E} {ξN Δ κ β κdrs : ℝ}
    {R : U →ₗ[ℝ] E} {N : V →ₗ[ℝ] E} {n : E} {nR : U} {nN : V}
    (h : ByrdOmojokunNormalStep c A p ξN Δ κ β κdrs R N n nR nN)
    (hz : A.adjoint c = 0) : n = 0 := by
  have hr := h.stationary_row hz
  have hn : nN = 0 := norm_le_zero_iff.mp (by simpa [hr] using h.null_bound)
  simp [h.decomposition, hr, hn]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Algorithm 15.4.7** of [conn2000trust], AA.1i and AA.2d. A tangential step $t$ after the normal
step $n$ is a **second-order tangential step** if $A t = 0$, $p(t) \le \xi_T \Delta$, and with
the tangential model $q^T(t) = \langle g + Hn, t\rangle + \frac12 \langle t, H t\rangle$,
$$q^T(0) - q^T(t) \ge \kappa_T \gamma \min\Big\{\frac{\xi_T \Delta}{b},
  \frac{\gamma}{\beta}\Big\}, \qquad \tau < 0 \implies q^T(0) - q^T(t) \ge -\kappa_2 \tau
  \Delta^2.$$
Here $\gamma$ is the norm of the reduced gradient, $b$ the norm of the null-space basis, $\beta$
a curvature bound and $\tau$ the curvature of the reduced Hessian, all supplied as real numbers. -/
structure SQPSecondOrderTangentialStep (A : E →L[ℝ] F) (g n t : E) (H : E →L[ℝ] E)
    (p : Seminorm ℝ E) (ξT Δ reducedGradient basisNorm κT β κ₂ τ : ℝ) : Prop where
  /-- The tangential step lies in the null space of $A$: $A t = 0$. -/
  tangent : A t = 0
  /-- The tangential step lies in its part of the trust region: $p(t) \le \xi_T \Delta$. -/
  radius : p t ≤ ξT * Δ
  /-- The tangential step gives the Cauchy-type decrease AA.1i of the tangential model. -/
  cauchy : κT * reducedGradient * min (ξT * Δ / basisNorm) (reducedGradient / β) ≤
    sqpTangentialModel g H n 0 - sqpTangentialModel g H n t
  /-- At negative curvature $\tau < 0$, the tangential step gives the decrease AA.2d of at least
  $-\kappa_2 \tau \Delta^2$. -/
  negative_curvature : τ < 0 → -(κ₂ * τ * Δ ^ 2) ≤
    sqpTangentialModel g H n 0 - sqpTangentialModel g H n t

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Algorithms 15.4.5 and 15.4.7** of [conn2000trust], trial data. A composite trial consists of
the iterate $x$, the normal step $n$, the tangential step $t$, a gradient $g$, a Jacobian $A$, a
Hessian approximation $H$, a trust-region norm $p$ with $p(v) = 0$ only for $v = 0$, the radius
$\Delta$, the previous penalty and the baseline penalty. The trial step is $n + t$. -/
structure SQPCompositeTrial (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  /-- The iterate $x$. -/
  x : E
  /-- The normal step $n$. -/
  n : E
  /-- The tangential step $t$. -/
  t : E
  /-- The gradient $g$ of the objective at $x$. -/
  g : E
  /-- The Jacobian $A$ of the constraints at $x$. -/
  A : E →L[ℝ] F
  /-- The Hessian approximation $H$. -/
  H : E →L[ℝ] E
  /-- The trust-region norm $p$, a seminorm on $E$. -/
  p : Seminorm ℝ E
  /-- The trust-region radius $\Delta$. -/
  radius : ℝ
  /-- The penalty of the previous iteration. -/
  previousPenalty : ℝ
  /-- The baseline penalty, a lower bound for the required penalty. -/
  penaltyBase : ℝ
  /-- The trust-region norm is definite: $p(v) = 0$ implies $v = 0$. -/
  norm_separates : ∀ v, p v = 0 → v = 0

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Algorithm 15.4.1** of [conn2000trust], Step 2, inherited by the composite variants. With the
normal decrease $\delta_N = \|c(x)\| - \|c(x) + A n\|$, the tangential decrease
$\delta_T = q^T(0) - q^T(t)$ and the objective model decrease $\delta_q = f(x) - q(n)$, where
$q(s) = f(x) + \langle g, s\rangle + \frac12 \langle s, Hs\rangle$, the required penalty is
$\max\{\sigma^B, -(\delta_q + \delta_T)/((1 - \nu)\delta_N)\}$ if $\delta_N > 0$ and the
baseline penalty $\sigma^B$ otherwise. The penalty is then
`ConnGouldToint.Chapter15.sqpPenaltyUpdate` applied to the required and the previous penalty. -/
noncomputable def SQPCompositeTrial.penalty (tr : SQPCompositeTrial E F) (P : SQPVariantParams)
    (f : E → ℝ) (c : E → F) : ℝ :=
  let normal := ‖c tr.x‖ - sqpNormalModel (c tr.x) tr.A tr.n
  let tangential := sqpTangentialModel tr.g tr.H tr.n 0 - sqpTangentialModel tr.g tr.H tr.n tr.t
  let dq := f tr.x - quadraticModel (f tr.x) tr.g tr.H.toLinearMap tr.n
  let required := if 0 < normal then
      max tr.penaltyBase (sqpPenaltyThreshold P.ν normal tangential dq)
    else tr.penaltyBase
  sqpPenaltyUpdate P.τ₁ P.τ₂ required tr.previousPenalty

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Algorithms 15.4.5 and 15.4.7** of [conn2000trust]. For a penalty $\sigma$, the predicted
decrease of a composite trial is $m(0) - m(n + t)$, where $m(s) = q(s) + \sigma \|c(x) + A s\|$
is the overall model (15.4.4).

The original trial $n + t$ determines the prediction, also when the acceptance test uses a
second-order correction. -/
noncomputable def SQPCompositeTrial.prediction (tr : SQPCompositeTrial E F) (f : E → ℝ)
    (c : E → F) (σ : ℝ) : ℝ :=
  let m := sqpOverallModel (f tr.x) tr.g tr.H (c tr.x) tr.A σ
  m 0 - m (tr.n + tr.t)

omit [CompleteSpace E] [CompleteSpace F] in
/-- **AA.1i** of [conn2000trust], first-order tangential condition. The tangential step $t$ of a
composite trial satisfies $A t = 0$, $p(t) \le \xi_T \Delta$ and
$$q^T(0) - q^T(t) \ge \kappa_T \gamma \min\Big\{\frac{\xi_T \Delta}{b},
  \frac{\gamma}{\beta}\Big\},$$
for the reduced-gradient norm $\gamma$, the basis norm $b$ and the curvature bound $\beta$. -/
def SQPCompositeTrial.cauchy (tr : SQPCompositeTrial E F)
    (ξT reducedGradient basisNorm κT β : ℝ) : Prop :=
  tr.A tr.t = 0 ∧ tr.p tr.t ≤ ξT * tr.radius ∧
    κT * reducedGradient * min (ξT * tr.radius / basisNorm) (reducedGradient / β) ≤
      sqpTangentialModel tr.g tr.H tr.n 0 - sqpTangentialModel tr.g tr.H tr.n tr.t

/-- **Algorithm 15.4.5** of [conn2000trust]. One iteration from a composite trial to the next
iterate $x'$, radius $\Delta'$ and penalty $\sigma$. The conditions are: $\Delta > 0$ and a
positive previous penalty; $\xi_N, \xi_T \in (0, 1]$, $\kappa_N > 0$, $\beta_N > 0$,
$\kappa_{drs} \ge 0$ and $\kappa_T > 0$; $A = c'(x)$ and $g = \nabla f(x)$; $n$ is a
Byrd–Omojokun normal step with the constants $\kappa = \kappa_N$ and $\beta = \beta_N$, the
bound $\kappa_{drs}$, the row-space coordinates $R$, the null-space coordinates $N$ and the
components $n_R$ and $n_N$; $t$ satisfies AA.1i with $\gamma = \|N^*(g + Hn)\|$, $b = \|N\|$ and
$\beta = 1 + \|N^* H N\|$; $\sigma$ is the inherited penalty; the predicted decrease of
$s = n + t$ is positive; $x' = x + s$ if the ratio $\rho$ of the merit function
$f + \sigma\|c\|$ is at least $\eta_1$ and $x' = x$ otherwise; and $\Delta'$ follows the basic
trust-region update for $\rho$. -/
def algorithm_15_4_5 (P : SQPVariantParams) (f : E → ℝ) (c : E → F)
    (tr : SQPCompositeTrial E F) (ξN ξT κN βN κdrs κT : ℝ)
    (R : U →ₗ[ℝ] E) (N : V →L[ℝ] E) (nR : U) (nN : V) (x' : E) (Δ' σ : ℝ) : Prop :=
  let pred := tr.prediction f c σ
  let merit := sqpMerit f c σ
  let s := tr.n + tr.t
  let gN := ‖N.adjoint (tr.g + tr.H tr.n)‖
  let HN := N.adjoint.comp (tr.H.comp N)
  0 < tr.radius ∧ 0 < tr.previousPenalty ∧
    ξN ∈ Set.Ioc 0 1 ∧ ξT ∈ Set.Ioc 0 1 ∧ 0 < κN ∧ 0 < βN ∧ 0 ≤ κdrs ∧ 0 < κT ∧
    tr.A = fderiv ℝ c tr.x ∧ tr.g = gradient f tr.x ∧
    ByrdOmojokunNormalStep (c tr.x) tr.A tr.p ξN tr.radius κN βN κdrs R N.toLinearMap tr.n nR nN ∧
    tr.cauchy ξT gN ‖N‖ κT (quadraticCurvatureBound HN) ∧
    σ = tr.penalty P f c ∧ 0 < pred ∧
    x' = Optimization.acceptStep P.η₁ merit tr.x s pred ∧
    BTRRadiusUpdate P.toBTRParams (Optimization.reductionRatio merit tr.x s pred) tr.radius Δ'

/-- **Algorithm 15.4.6** of [conn2000trust], with (15.4.153)–(15.4.156). One iteration of Algorithm
15.4.5 with a second-order correction $u$. In addition to the conditions of Algorithm 15.4.5 and
$\eta_{CS} > 0$:

* the normal step satisfies $p(n) = \xi_N \Delta$ or solves the linearized constraint,
  $c(x) + A n = 0$;
* when the original ratio is below $\eta_1$ and $c(x) + A n = 0$, the correction $u$ satisfies
  the supplied condition `correctionOK`, which selects a full or partial correction;
* the tested trial is $s + u$ if the original ratio is below $\eta_1$, $c(x) + A n = 0$ and
  $p(u) \le \eta_{CS} \Delta$, and $s$ otherwise;
* the ratio $\rho$ of the tested trial uses the predicted decrease of $s$, the iterate is
  accepted by this ratio and the radius follows the basic trust-region update for $\rho$;
* the radius is kept, $\Delta' = \Delta$, when the original trial $x + s$ is accepted with
  $\eta_1 \le \rho < \eta_2$ and $c(x) + An = 0$.

**Reading.** The corrected trial is tested against the predicted decrease of the original trial,
and the correction is tried only if it satisfies the norm cap. -/
def algorithm_15_4_6 (P : SQPVariantParams) (f : E → ℝ) (c : E → F)
    (tr : SQPCompositeTrial E F) (ξN ξT κN βN κdrs κT ηCS : ℝ)
    (R : U →ₗ[ℝ] E) (N : V →L[ℝ] E) (nR : U) (nN : V)
    (correctionOK : E → Prop) (correction x' : E) (Δ' σ : ℝ) : Prop :=
  open Classical in
  let pred := tr.prediction f c σ
  let merit := sqpMerit f c σ
  let s := tr.n + tr.t
  let exactNormal := c tr.x + tr.A tr.n = 0
  let original := Optimization.reductionRatio merit tr.x s pred
  let tested := if original < P.η₁ ∧ exactNormal ∧ tr.p correction ≤ ηCS * tr.radius
    then s + correction else s
  let ρ := Optimization.reductionRatio merit tr.x tested pred
  let gN := ‖N.adjoint (tr.g + tr.H tr.n)‖
  let HN := N.adjoint.comp (tr.H.comp N)
  0 < tr.radius ∧ 0 < tr.previousPenalty ∧
    ξN ∈ Set.Ioc 0 1 ∧ ξT ∈ Set.Ioc 0 1 ∧ 0 < κN ∧ 0 < βN ∧ 0 ≤ κdrs ∧ 0 < κT ∧
    0 < ηCS ∧ tr.A = fderiv ℝ c tr.x ∧ tr.g = gradient f tr.x ∧
    ByrdOmojokunNormalStep (c tr.x) tr.A tr.p ξN tr.radius κN βN κdrs R N.toLinearMap tr.n nR nN ∧
    (tr.p tr.n = ξN * tr.radius ∨ exactNormal) ∧
    tr.cauchy ξT gN ‖N‖ κT (quadraticCurvatureBound HN) ∧
    (original < P.η₁ → exactNormal → correctionOK correction) ∧
    σ = tr.penalty P f c ∧ 0 < pred ∧
    x' = Optimization.acceptStep P.η₁ merit tr.x tested pred ∧
    BTRRadiusUpdate P.toBTRParams ρ tr.radius Δ' ∧
    (P.η₁ ≤ ρ → ρ < P.η₂ → x' = tr.x + s → exactNormal → Δ' = tr.radius)

/-- **Algorithm 15.4.7** of [conn2000trust]. One iteration of Algorithm 15.4.6 with the
negative-curvature condition AA.2d: $\kappa_2 > 0$, $\tau = \inf\{\langle v, N^* H N v\rangle :
\|v\| = 1\}$, and if $\tau < 0$ then $q^T(0) - q^T(t) \ge -\kappa_2 \tau \Delta^2$.

The infimum is $0$ when $V$ is the zero space. -/
def algorithm_15_4_7 (P : SQPVariantParams) (f : E → ℝ) (c : E → F)
    (tr : SQPCompositeTrial E F) (ξN ξT κN βN κdrs κT κ₂ τ ηCS : ℝ)
    (R : U →ₗ[ℝ] E) (N : V →L[ℝ] E) (nR : U) (nN : V)
    (correctionOK : E → Prop) (correction x' : E) (Δ' σ : ℝ) : Prop :=
  let HN := N.adjoint.comp (tr.H.comp N)
  algorithm_15_4_6 P f c tr ξN ξT κN βN κdrs κT ηCS R N nR nN correctionOK correction x' Δ' σ ∧
    0 < κ₂ ∧ τ = sInf ((fun v : V ↦ ⟪v, HN v⟫) '' Metric.sphere 0 1) ∧
    (τ < 0 → -(κ₂ * τ * tr.radius ^ 2) ≤
      sqpTangentialModel tr.g tr.H tr.n 0 - sqpTangentialModel tr.g tr.H tr.n tr.t)

end CompositeSteps

/-! ### The infeasibility-reducing variant -/

section Infeasibility

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Section 15.4.3** of [conn2000trust], augmented merit function. For a penalty $\sigma$ and
$z = (x, y)$, the **augmented merit function** is
$$\phi(x, y) = f(x) - \langle c(x), y\rangle + \frac{\sigma}{2} \|c(x)\|^2.$$

The Lagrangian subtracts the constraint pairing. -/
noncomputable def infeasibilitySQPMerit (f : E → ℝ) (c : E → F)
    (σ : ℝ) (z : E × F) : ℝ :=
  f z.1 - ⟪c z.1, z.2⟫ + (σ / 2) * ‖c z.1‖ ^ 2

/-- **Section 15.4.3** of [conn2000trust], augmented model. At a center with objective value $f_0$,
constraint value $c$, multiplier $y$, gradient $g$, Hessian $H$ and Jacobian $A$, the
**augmented model** of a step $(s, d)$ is
$$m(s, d) = f_0 - \langle c, y\rangle + \langle g, s\rangle + \tfrac12 \langle s, H s\rangle -
  \langle c + A s, d\rangle + \frac{\sigma}{2} \|c + A s\|^2.$$

**Correction.** The constant term is the Lagrangian value $f_0 - \langle c, y\rangle$ without
the penalty term. The squared residual penalty is then counted once, and the model agrees with
the merit function at the center (`ConnGouldToint.Chapter15.infeasibilitySQPModel_zero`). -/
noncomputable def infeasibilitySQPModel (f₀ : ℝ) (c y : F) (g : E) (H : E →L[ℝ] E)
    (A : E →L[ℝ] F) (σ : ℝ) (step : E × F) : ℝ :=
  quadraticModel (f₀ - ⟪c, y⟫) g H.toLinearMap step.1 -
    ⟪c + A step.1, step.2⟫ + (σ / 2) * ‖c + A step.1‖ ^ 2

/-- **Algorithm 15.4.8** of [conn2000trust], Step 2. At $z = (x, y)$, the augmented model with
center data $f(x)$, $c(x)$ and $y$ takes the value $\phi(x, y)$ at the zero step, for every
gradient, Hessian, Jacobian and penalty. -/
theorem infeasibilitySQPModel_zero (f : E → ℝ) (c : E → F) (z : E × F)
    (g : E) (H : E →L[ℝ] E) (A : E →L[ℝ] F) (σ : ℝ) :
    infeasibilitySQPModel (f z.1) (c z.1) z.2 g H A σ 0 =
      infeasibilitySQPMerit f c σ z := by
  simp [infeasibilitySQPModel, infeasibilitySQPMerit, quadraticModel]

/-- **Equation (15.4.171)** of [conn2000trust]. The predicted decrease of the augmented model is
$$m(0) - m(s, d) = \frac{\sigma}{2} \big(\|c\|^2 - \|c + A s\|^2\big) - \Big(\langle g,
  s\rangle + \tfrac12 \langle s, Hs\rangle - \langle c + A s, d\rangle\Big).$$
-/
theorem infeasibilitySQPModel_drop (f₀ : ℝ) (c y : F) (g : E) (H : E →L[ℝ] E)
    (A : E →L[ℝ] F) (σ : ℝ) (step : E × F) :
    infeasibilitySQPModel f₀ c y g H A σ 0 - infeasibilitySQPModel f₀ c y g H A σ step =
      (σ / 2) * (‖c‖ ^ 2 - ‖c + A step.1‖ ^ 2) -
        (quadraticModel 0 g H.toLinearMap step.1 - ⟪c + A step.1, step.2⟫) := by
  simp [infeasibilitySQPModel, quadraticModel]
  ring

/-- **Algorithm 15.4.8** of [conn2000trust], corrected Step 2. With the decrease $\delta_N$ of the
squared linearized residual and the change $\delta_F$ of the other model terms, the **required
penalty** is
$$\max\Big\{\sigma^B, \frac{2\delta_F}{(1 - \nu)\delta_N}\Big\}.$$

**Correction.** The source prints the threshold with a negative sign. With $\delta_F$ written as
a change, the positive sign is the one that gives (15.4.171); see
`ConnGouldToint.Chapter15.infeasibilitySQPPenalty_printed_sign_counterexample`.

The quotient is $0$ when $\delta_N = 0$. Algorithm 15.4.8 then keeps the previous penalty. -/
noncomputable def infeasibilitySQPPenaltyRequired (ν δN δF base : ℝ) : ℝ :=
  max base (2 * δF / ((1 - ν) * δN))

/-- **Equation (15.4.171)** of [conn2000trust], corrected penalty threshold. Let $\nu < 1$ and
$\delta_N > 0$. Then the required penalty is at most $\sigma$ if and only if
$\sigma^B \le \sigma$ and
$$\frac{\nu\sigma}{2} \delta_N \le \frac{\sigma}{2} \delta_N - \delta_F.$$
-/
theorem infeasibilitySQPPenaltyRequired_le_iff {ν δN δF base σ : ℝ}
    (hν : ν < 1) (hN : 0 < δN) :
    infeasibilitySQPPenaltyRequired ν δN δF base ≤ σ ↔
      base ≤ σ ∧ (ν * σ / 2) * δN ≤ (σ / 2) * δN - δF := by
  rw [infeasibilitySQPPenaltyRequired, max_le_iff,
    div_le_iff₀ (mul_pos (sub_pos.mpr hν) hN)]
  constructor <;> rintro ⟨hbase, h⟩ <;> exact ⟨hbase, by linarith only [h]⟩

/-- **Algorithm 15.4.8** of [conn2000trust], Step 2, sign counterexample. Take $\nu = 1/2$,
$\delta_N = 1$, $\delta_F = 1$, $\sigma^B = 1$ and $\sigma = 1$. The printed threshold gives
$\max\{1, -2\delta_F/((1 - \nu)\delta_N)\} = 1 \le \sigma$, but (15.4.171) fails:
$\frac{\nu\sigma}{2}\delta_N = \frac14 > \frac{\sigma}{2}\delta_N - \delta_F = -\frac12$. -/
theorem infeasibilitySQPPenalty_printed_sign_counterexample :
    max (1 : ℝ) (-2 / ((1 - 1 / 2) * 1)) ≤ 1 ∧
      ¬ ((1 / 2 : ℝ) * 1 / 2) * 1 ≤ (1 / 2 : ℝ) * 1 - 1 := by
  norm_num [max_def]

/-- **Algorithm 15.4.8** of [conn2000trust]. One iteration from $z = (x, y)$ with radius $\Delta$
and previous penalty $\sigma^-$ to $z'$ with radius $\Delta'$ and penalty $\sigma$, for a normal
step $n$ and a step $(s, d)$. The conditions are:

* $\Delta > 0$, $\sigma^- > 0$, $A = c'(x)$, and $\langle g, v\rangle$ is the derivative of the
  Lagrangian $x \mapsto f(x) - \langle c(x), y\rangle$ in the direction $v$;
* the trust-region norm $p$ is definite, $n = 0$ if $c(x) = 0$, $p(n) \le \Delta$ and
  $\theta = \|c(x) + A n\| \le \|c(x)\|$, with $\theta < \|c(x)\|$ whenever some $u$ with
  $p(u) \le \Delta$ has $\|c(x) + A u\| < \|c(x)\|$;
* $\|c(x) + A s\| \le \theta$, $p(s) \le \Delta$, and $s$ is an approximate minimizer of
  $\langle g, s\rangle + \frac12 \langle s, Hs\rangle$ on $\{s : \|c(x) + A s\| \le \theta, \
  p(s) \le \Delta\}$ in the sense of the supplied predicate;
* $\sigma = \sigma^-$ if $\delta_N = \|c(x)\|^2 - \|c(x) + A s\|^2$ is zero, and otherwise the
  penalty update of `ConnGouldToint.Chapter15.sqpPenaltyUpdate` with the required penalty;
* the predicted decrease of the augmented model is positive, $z'$ is accepted by the ratio test
  for the augmented merit function, and $\Delta'$ follows the basic trust-region update.

The multiplier step $d$ is free. A zero predicted decrease ends the ratio-based iteration. -/
def algorithm_15_4_8 (P : SQPVariantParams) (f : E → ℝ) (c : E → F)
    (approximate : (E → ℝ) → Set E → E → Prop)
    (A : E →L[ℝ] F) (g : E) (H : E →L[ℝ] E) (p : Seminorm ℝ E) (base : ℝ)
    (z z' : E × F) (Δ Δ' previous σ : ℝ) (n : E) (step : E × F) : Prop :=
  let residual := c z.1
  let θ := ‖residual + A n‖
  let q := quadraticModel 0 g H.toLinearMap
  let δN := ‖residual‖ ^ 2 - ‖residual + A step.1‖ ^ 2
  let δF := q step.1 - ⟪residual + A step.1, step.2⟫
  let required := infeasibilitySQPPenaltyRequired P.ν δN δF base
  let m := infeasibilitySQPModel (f z.1) residual z.2 g H A σ
  let predicted := m 0 - m step
  let ρ := Optimization.reductionRatio (infeasibilitySQPMerit f c σ) z step predicted
  0 < Δ ∧ 0 < previous ∧
    A = fderiv ℝ c z.1 ∧
    (∀ v, ⟪g, v⟫ = fderiv ℝ (fun x ↦ f x - ⟪c x, z.2⟫) z.1 v) ∧
    (∀ v, p v = 0 → v = 0) ∧
    (residual = 0 → n = 0) ∧ p n ≤ Δ ∧ θ ≤ ‖residual‖ ∧
    ((∃ u, p u ≤ Δ ∧ ‖residual + A u‖ < ‖residual‖) → θ < ‖residual‖) ∧
    ‖residual + A step.1‖ ≤ θ ∧ p step.1 ≤ Δ ∧
    approximate q {s | ‖residual + A s‖ ≤ θ ∧ p s ≤ Δ} step.1 ∧
    σ = (if δN = 0 then previous else sqpPenaltyUpdate P.τ₁ P.τ₂ required previous) ∧
    0 < predicted ∧
    z' = Optimization.acceptStep P.η₁ (infeasibilitySQPMerit f c σ) z step predicted ∧
    BTRRadiusUpdate P.toBTRParams ρ Δ Δ'

/-- **Algorithm 15.4.8** of [conn2000trust], Steps 2–4. An iteration of Algorithm 15.4.8 gives
$\Delta' > 0$ and $\sigma^- \le \sigma$, and the predicted decrease satisfies (15.4.171):
$$\frac{\nu\sigma}{2} \big(\|c(x)\|^2 - \|c(x) + A s\|^2\big) \le m(0) - m(s, d).$$
-/
theorem algorithm_15_4_8_invariants {P : SQPVariantParams}
    {f : E → ℝ} {c : E → F} {approximate : (E → ℝ) → Set E → E → Prop}
    {A : E →L[ℝ] F} {g : E} {H : E →L[ℝ] E} {p : Seminorm ℝ E} {base : ℝ}
    {z z' : E × F} {Δ Δ' previous σ : ℝ} {n : E} {step : E × F}
    (h : algorithm_15_4_8 P f c approximate A g H p base z z' Δ Δ' previous σ n step) :
    0 < Δ' ∧ previous ≤ σ ∧
      (P.ν * σ / 2) * (‖c z.1‖ ^ 2 - ‖c z.1 + A step.1‖ ^ 2) ≤
        infeasibilitySQPModel (f z.1) (c z.1) z.2 g H A σ 0 -
          infeasibilitySQPModel (f z.1) (c z.1) z.2 g H A σ step := by
  obtain ⟨hΔ, -, -, -, -, -, -, hθ, -, hres, -, -, hσ, hd, -, hΔ'⟩ := h
  refine ⟨BTRRadiusUpdate.pos hΔ' hΔ, ?_, ?_⟩
  · rw [hσ]
    unfold sqpPenaltyUpdate
    split_ifs
    · exact le_rfl
    · exact le_rfl
    · exact (le_add_of_nonneg_right P.tau₂_pos.le).trans
        ((le_max_right _ _).trans (le_max_right _ _))
  · let δN := ‖c z.1‖ ^ 2 - ‖c z.1 + A step.1‖ ^ 2
    let δF := quadraticModel 0 g H.toLinearMap step.1 - ⟪c z.1 + A step.1, step.2⟫
    let required := infeasibilitySQPPenaltyRequired P.ν δN δF base
    change σ = (if δN = 0 then previous else sqpPenaltyUpdate P.τ₁ P.τ₂ required previous) at hσ
    change (P.ν * σ / 2) * δN ≤ _
    rw [infeasibilitySQPModel_drop]
    change (P.ν * σ / 2) * δN ≤ (σ / 2) * δN - δF
    have hN : 0 ≤ δN := sub_nonneg.mpr
      (pow_le_pow_left₀ (norm_nonneg _) (hres.trans hθ) 2)
    rcases hN.eq_or_lt with hN | hN
    · have hdrop := hd
      rw [infeasibilitySQPModel_drop] at hdrop
      change 0 < (σ / 2) * δN - δF at hdrop
      rw [← hN, mul_zero]
      simpa only [← hN, mul_zero] using hdrop.le
    · have hbound : required ≤ σ := by
        rw [hσ, ite_eq_right hN.ne', sqpPenaltyUpdate]
        split_ifs with hb
        · exact hb
        · exact le_max_left _ _
      exact ((infeasibilitySQPPenaltyRequired_le_iff P.nu_lt_one hN).mp hbound).2

end Infeasibility

end ConnGouldToint.Chapter15
