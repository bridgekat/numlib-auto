/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter08.Section03
import NumlibSurface.ConnGouldToint.Chapter15.Section04
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Conn, Gould and Toint, Section 15.4: Relaxed linearization SQP algorithms

This module defines the runs of the relaxed linearization SQP Algorithms 15.4.1–15.4.4 of
[conn2000trust] for the problem of minimizing $f(x)$ subject to $c(x) = 0$, with $c : E \to F$. At
the iterate $x_k$ with radius $\Delta_k$, Jacobian $A_k = c'(x_k)$ and Hessian approximation $H_k$,
the trial step is $s_k = n_k + t_k$. The normal step $n_k = \alpha_k n^C_k$ scales a solution
$n^C_k$ of the linearized constraint $A_k n + c(x_k) = 0$ into the trust region. The tangential step
$t_k$ lies in the null space of $A_k$ and gives a Cauchy-type decrease of the tangential model. The
penalty parameter $\sigma_k$ is updated from the normal, tangential and objective model decreases.
The step is accepted by the ratio test for the exact-penalty merit function
$f(x) + \sigma_k \|c(x)\|$ and the overall model $q_k(s) + \sigma_k \|c(x_k) + A_k s\|$. Algorithm
15.4.2 adds a second-order correction when the original trial fails, Algorithm 15.4.3 specifies the
full and partial corrections, and Algorithm 15.4.4 adds the negative-curvature condition AA.2d. The
models and the penalty update are those of `NumlibSurface.ConnGouldToint.Chapter15.Section04`.

## Main definitions

* Algorithm 15.4.1, `ConnGouldToint.Chapter15.RelaxedSQPParams`: the parameters of the algorithms.
* Algorithm 15.4.1, Steps 1–2, `ConnGouldToint.Chapter15.RelaxedSQPTrials`: the sequences of trial
  steps with the conditions AA.1g–AA.1i.
* Equation (15.4.9), `ConnGouldToint.Chapter15.RelaxedSQPTrials.normal`: the scaled normal step
  $n_k = \alpha_k n^C_k$.
* Algorithm 15.4.1, `ConnGouldToint.Chapter15.RelaxedSQPTrials.step`: the composite step
  $s_k = n_k + t_k$.
* Algorithm 15.4.1, Step 2, `ConnGouldToint.Chapter15.RelaxedSQPTrials.penalty`: the updated penalty
  parameter.
* Algorithm 15.4.1, Step 3, `ConnGouldToint.Chapter15.RelaxedSQPTrials.prediction`: the overall
  model decrease of the original trial.
* Algorithm 15.4.1, Step 3, `ConnGouldToint.Chapter15.RelaxedSQPTrials.ratio`: the merit ratio of a
  trial against that prediction.
* Algorithm 15.4.1, Steps 3–4, `ConnGouldToint.Chapter15.RelaxedSQPRun`: a run of Algorithm 15.4.1.
* Algorithms 15.4.2 and 15.4.3, `ConnGouldToint.Chapter15.relaxedSQPProbe`: the choice between the
  original trial and the corrected trial.
* Algorithm 15.4.2, `ConnGouldToint.Chapter15.RelaxedSQPCorrectedRun`: a run of Algorithm 15.4.2,
  with an optional norm cap on the correction.
* Algorithm 15.4.2, Step 3, `ConnGouldToint.Chapter15.RelaxedSQPCorrectedRun.probe`: the trial
  passed to the acceptance test.
* Algorithm 15.4.3, `ConnGouldToint.Chapter15.RelaxedSQPStructuredRun`: a run of Algorithm 15.4.3
  with full and partial corrections.
* Algorithm 15.4.4, `ConnGouldToint.Chapter15.RelaxedSQPSecondOrderRun`: a run of Algorithm 15.4.4
  with the condition AA.2d.

## Main results

* Algorithm 15.4.2, Step 3, `ConnGouldToint.Chapter15.relaxedSQPProbe_of_successful_original`: a
  successful original trial is used without correction.
* Algorithm 15.4.2, `ConnGouldToint.Chapter15.RelaxedSQPCorrectedRun.merit_drop_of_successful`: an
  accepted trial decreases the merit function by at least $\eta_1$ times the prediction of the
  original step.
* Algorithm 15.4.3, (15.4.95),
  `ConnGouldToint.Chapter15.RelaxedSQPStructuredRun.radius_eq_of_original_moderate`: the radius is
  kept after an accepted original trial with a moderate ratio and a small normal step.

## Implementation notes

* A run is a structure of sequences indexed by `ℕ` together with the conditions of the algorithm.
  Every iteration of a run has a strictly positive predicted decrease, so a run describes only
  iterations that do not stop.
* The null-space coordinates $N_k : W \to E$ are injective with range $\ker A_k$. They need not be
  orthonormal.
* The ratio and the acceptance use `Optimization.reductionRatio` and `Optimization.acceptStep`, and
  the radius update is `ConnGouldToint.Chapter06.BTRRadiusUpdate`.

## Deviations from the source

* **Algorithm 15.4.1, Step 2** (reading). When the normal model decrease is zero, the required
  penalty is the baseline value alone. See `ConnGouldToint.Chapter15.RelaxedSQPTrials.penalty`.
* **Algorithm 15.4.1** (generalization). The null-space coordinates need not be orthonormal. See
  `ConnGouldToint.Chapter15.RelaxedSQPTrials`.
* **Algorithms 15.4.2 and 15.4.3, acceptance** (reading). The original and the corrected trial are
  both tested against the predicted decrease of the original step. A correction that violates the
  norm cap is not tried, and the original ratio is kept. See
  `ConnGouldToint.Chapter15.relaxedSQPProbe` and `ConnGouldToint.Chapter15.RelaxedSQPCorrectedRun`.
* **Algorithm 15.4.3** (reading). The correction systems have unique solutions with a uniformly
  bounded inverse, as in the derivation of the correction estimates. See
  `ConnGouldToint.Chapter15.RelaxedSQPStructuredRun`.
* **Algorithm 15.4.4** (reading). The algorithm follows the boxed rule of the source and adds AA.2d
  to the tangential step of Algorithm 15.4.3. See
  `ConnGouldToint.Chapter15.RelaxedSQPSecondOrderRun`.
-/

open scoped RealInnerProductSpace Topology
open ConnGouldToint.Chapter06 Optimization Filter

namespace ConnGouldToint.Chapter15

variable {E F W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **Algorithm 15.4.1** of [conn2000trust], parameters. The parameters of relaxed linearization SQP
extend those of the basic trust-region algorithm (`ConnGouldToint.Chapter06.BTRParams`) by
fractions $\xi_N, \xi_T, \theta \in (0, 1]$ of the radius for the normal and tangential steps
and the normal scaling, a fraction $\nu \in (0, 1)$ in the penalty threshold, penalty growth
constants $\tau_1 > 1$ and $\tau_2 > 0$, a normal-step bound $\kappa_N > 0$ and a tangential
decrease coefficient $\kappa_T \in (0, 1)$. -/
structure RelaxedSQPParams extends BTRParams where
  /-- The fraction $\xi_N$ of the radius available to the normal step. -/
  ξN : ℝ
  /-- The fraction $\xi_T$ of the radius available to the tangential step. -/
  ξT : ℝ
  /-- The fraction $\theta$ in the lower end of the normal scaling interval. -/
  θ : ℝ
  /-- The fraction $\nu$ in the penalty threshold (15.4.8). -/
  ν : ℝ
  /-- The growth factor $\tau_1$ of the penalty update. -/
  τ₁ : ℝ
  /-- The growth increment $\tau_2$ of the penalty update. -/
  τ₂ : ℝ
  /-- The constant $\kappa_N$ of the normal-step bound $\|n^C_k\| \le \kappa_N \|c(x_k)\|$. -/
  κN : ℝ
  /-- The coefficient $\kappa_T$ of the tangential decrease condition AA.1i. -/
  κT : ℝ
  /-- The normal radius fraction lies in $(0, 1]$: $0 < \xi_N \le 1$. -/
  normal_fraction : ξN ∈ Set.Ioc 0 1
  /-- The tangential radius fraction lies in $(0, 1]$: $0 < \xi_T \le 1$. -/
  tangential_fraction : ξT ∈ Set.Ioc 0 1
  /-- The scaling fraction lies in $(0, 1]$: $0 < \theta \le 1$. -/
  scale_fraction : θ ∈ Set.Ioc 0 1
  /-- The penalty fraction lies in $(0, 1)$: $0 < \nu < 1$. -/
  penalty_fraction : ν ∈ Set.Ioo 0 1
  /-- The penalty grows by a factor larger than one: $\tau_1 > 1$. -/
  penalty_growth : 1 < τ₁
  /-- The penalty grows by a positive increment: $\tau_2 > 0$. -/
  penalty_increment : 0 < τ₂
  /-- The normal-step bound is positive: $\kappa_N > 0$. -/
  normal_bound : 0 < κN
  /-- The tangential decrease coefficient lies in $(0, 1)$: $0 < \kappa_T < 1$. -/
  tangential_decrease : κT ∈ Set.Ioo 0 1

/-- **Algorithm 15.4.1** of [conn2000trust], Steps 1–2, with AA.1g–AA.1i. Trial data for the problem
$\min f(x)$ subject to $c(x) = 0$. A value consists of sequences of iterates $x_k$, radii
$\Delta_k > 0$, symmetric Hessian approximations $H_k$, injective null-space coordinates
$N_k : W \to E$ with range $\ker A_k$, where $A_k = c'(x_k)$, trial normal steps $n^C_k$,
scalings $\alpha_k$, tangential steps $t_k$, baseline penalties and previous penalties, with a
positive initial previous penalty. The steps satisfy
$$A_k n^C_k + c(x_k) = 0, \qquad \|n^C_k\| \le \kappa_N \|c(x_k)\|, \qquad \|\alpha_k n^C_k\|
  \le \xi_N \Delta_k,$$
the normal scaling condition AA.1h, $A_k t_k = 0$, $\|t_k\| \le \xi_T \Delta_k$, and the
tangential decrease condition AA.1i
$$q^T_k(0) - q^T_k(t_k) \ge \kappa_T \|g^N_k\| \min\Big\{\frac{\xi_T \Delta_k}{\|N_k\|},
  \frac{\|g^N_k\|}{1 + \|H^N_k\|}\Big\},$$
where $n_k = \alpha_k n^C_k$, $g^N_k = N_k^*(\nabla f(x_k) + H_k n_k)$, $H^N_k = N_k^* H_k N_k$
and $q^T_k$ is the tangential model (15.4.5) after the normal step.

**Generalization.** The null-space coordinates $N_k$ need not be orthonormal.

The tangential model is `ConnGouldToint.Chapter15.sqpTangentialModel` and the scaling condition
is `ConnGouldToint.Chapter15.IsSQPNormalScaling`. The runs built on these data require a
strictly positive predicted decrease at every iteration. -/
structure RelaxedSQPTrials [CompleteSpace E] [CompleteSpace F]
    (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams) (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] where
  /-- The iterates $x_k$. -/
  x : ℕ → E
  /-- The trust-region radii $\Delta_k$. -/
  radius : ℕ → ℝ
  /-- The Hessian approximations $H_k$. -/
  H : ℕ → E →L[ℝ] E
  /-- The null-space coordinates $N_k : W \to E$. -/
  N : ℕ → W →L[ℝ] E
  /-- The trial normal steps $n^C_k$, before scaling. -/
  normalTrial : ℕ → E
  /-- The normal scalings $\alpha_k$. -/
  scale : ℕ → ℝ
  /-- The tangential steps $t_k$. -/
  tangential : ℕ → E
  /-- The baseline penalties $\sigma^B_k$, lower bounds for the required penalties. -/
  penaltyBase : ℕ → ℝ
  /-- The penalties $\sigma_{k-1}$ of the previous iterations, from which the update starts. -/
  previousPenalty : ℕ → ℝ
  /-- The initial previous penalty is positive. -/
  initial_penalty_pos : 0 < previousPenalty 0
  /-- Every radius is positive: $\Delta_k > 0$. -/
  radius_pos : ∀ k, 0 < radius k
  /-- Every Hessian approximation $H_k$ is symmetric. -/
  symmetric : ∀ k, (H k).toLinearMap.IsSymmetric
  /-- The range of $N_k$ is the null space of the Jacobian $A_k = c'(x_k)$. -/
  nullspace : ∀ k, LinearMap.range (N k).toLinearMap = LinearMap.ker (fderiv ℝ c (x k)).toLinearMap
  /-- The coordinate map $N_k$ is injective. -/
  coordinates_injective : ∀ k, Function.Injective (N k)
  /-- The trial normal step solves the linearized constraint: $A_k n^C_k + c(x_k) = 0$. -/
  normal_equation : ∀ k, fderiv ℝ c (x k) (normalTrial k) + c (x k) = 0
  /-- The trial normal step is bounded by the constraint value: $\|n^C_k\| \le \kappa_N \|c(x_k)\|$.
  -/
  normal_bound : ∀ k, ‖normalTrial k‖ ≤ P.κN * ‖c (x k)‖
  /-- The scaling $\alpha_k$ satisfies the normal scaling condition AA.1h. -/
  normal_scaling : ∀ k, IsSQPNormalScaling (normalTrial k) P.θ P.ξN (radius k) (scale k)
  /-- The scaled normal step lies in its part of the trust region:
  $\|\alpha_k n^C_k\| \le \xi_N \Delta_k$. -/
  normal_radius : ∀ k, ‖scale k • normalTrial k‖ ≤ P.ξN * radius k
  /-- The tangential step lies in the null space of the Jacobian: $A_k t_k = 0$. -/
  tangential_kernel : ∀ k, fderiv ℝ c (x k) (tangential k) = 0
  /-- The tangential step lies in its part of the trust region: $\|t_k\| \le \xi_T \Delta_k$. -/
  tangential_radius : ∀ k, ‖tangential k‖ ≤ P.ξT * radius k
  /-- The tangential step satisfies the Cauchy-type decrease condition AA.1i in the null-space
  coordinates. -/
  tangential_decrease : ∀ k,
    let n := scale k • normalTrial k
    let g := gradient f (x k)
    let gN := (N k).adjoint (g + H k n)
    let HN := (N k).adjoint.comp ((H k).comp (N k))
    P.κT * ‖gN‖ * min (P.ξT * radius k / ‖N k‖) (‖gN‖ / (1 + ‖HN‖)) ≤
      sqpTangentialModel g (H k) n 0 - sqpTangentialModel g (H k) n (tangential k)

namespace RelaxedSQPTrials

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace W]
  {f : E → ℝ} {c : E → F} {P : RelaxedSQPParams}

/-- **Equation (15.4.9)** of [conn2000trust]. The **normal step** is the scaled trial normal step
$n_k = \alpha_k n^C_k$. -/
noncomputable def normal (tr : RelaxedSQPTrials f c P W) (k : ℕ) : E :=
  tr.scale k • tr.normalTrial k

/-- **Algorithm 15.4.1** of [conn2000trust], composite step. The **trial step** is
$s_k = n_k + t_k$, the sum of the normal and the tangential step. -/
noncomputable def step (tr : RelaxedSQPTrials f c P W) (k : ℕ) : E :=
  tr.normal k + tr.tangential k

/-- **Algorithm 15.4.1** of [conn2000trust], Step 2. Let
$\delta^N_k = \|c(x_k)\| - \|c(x_k) + A_k n_k\|$ be the normal model decrease,
$\delta^T_k = q^T_k(0) - q^T_k(t_k)$ the tangential model decrease and
$\delta^q_k = q_k(0) - q_k(n_k)$ the objective model decrease along the normal step, where
$q_k(s) = f(x_k) + \langle \nabla f(x_k), s\rangle + \frac12 \langle s, H_k s\rangle$. The
required penalty is
$$\sigma^{\mathrm{req}}_k = \max\Big\{\sigma^B_k, -\frac{\delta^q_k + \delta^T_k}{(1 -
  \nu)\delta^N_k}\Big\} \ \text{ if } \delta^N_k > 0, \qquad \sigma^{\mathrm{req}}_k =
  \sigma^B_k \ \text{ otherwise},$$
with the baseline penalty $\sigma^B_k$. The **penalty** $\sigma_k$ is the previous penalty
$\sigma_{k-1}$ if $\sigma^{\mathrm{req}}_k \le \sigma_{k-1}$, and
$\max\{\sigma^{\mathrm{req}}_k, \tau_1 \sigma_{k-1}, \sigma_{k-1} + \tau_2\}$ otherwise.

**Reading.** At zero normal decrease the threshold (15.4.8) is not defined, and only the
baseline penalty is required.

The update is `ConnGouldToint.Chapter15.sqpPenaltyUpdate` and the threshold is
`ConnGouldToint.Chapter15.sqpPenaltyThreshold`. -/
noncomputable def penalty (tr : RelaxedSQPTrials f c P W) (k : ℕ) : ℝ :=
  let x := tr.x k
  let A := fderiv ℝ c x
  let g := gradient f x
  let H := tr.H k
  let n := tr.normal k
  let dN := sqpNormalModel (c x) A 0 - sqpNormalModel (c x) A n
  let dT := sqpTangentialModel g H n 0 - sqpTangentialModel g H n (tr.tangential k)
  let dq := quadraticModel (f x) g H.toLinearMap 0 - quadraticModel (f x) g H.toLinearMap n
  let required := if 0 < dN then
    max (tr.penaltyBase k) (sqpPenaltyThreshold P.ν dN dT dq)
    else tr.penaltyBase k
  sqpPenaltyUpdate P.τ₁ P.τ₂ required (tr.previousPenalty k)

/-- **Algorithm 15.4.1** of [conn2000trust], Step 3. The **predicted decrease** is
$m_k(0) - m_k(s_k)$, where $m_k(s) = q_k(s) + \sigma_k \|c(x_k) + A_k s\|$ is the overall model
(15.4.4) with the updated penalty $\sigma_k$. -/
noncomputable def prediction (tr : RelaxedSQPTrials f c P W) (k : ℕ) : ℝ :=
  let x := tr.x k
  let model := sqpOverallModel (f x) (gradient f x) (tr.H k) (c x) (fderiv ℝ c x)
    (tr.penalty k)
  model 0 - model (tr.step k)

/-- **Algorithm 15.4.1** of [conn2000trust], Step 3, and Algorithm 15.4.2, Step 3a. The **merit
ratio** of a trial $s$ is
$$\rho_k(s) = \frac{\phi_k(x_k) - \phi_k(x_k + s)}{m_k(0) - m_k(s_k)}, \qquad \phi_k(x) = f(x) +
  \sigma_k \|c(x)\|.$$
The denominator is the predicted decrease of the original trial $s_k$, also when $s$ is a
corrected trial. -/
noncomputable def ratio (tr : RelaxedSQPTrials f c P W) (k : ℕ) (s : E) : ℝ :=
  reductionRatio (sqpMerit f c (tr.penalty k)) (tr.x k) s (tr.prediction k)

end RelaxedSQPTrials

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace W]

/-- **Algorithm 15.4.1** of [conn2000trust], Steps 3–4. A **run** of the relaxed linearization
algorithm consists of trial data in which the previous penalty of iteration $k + 1$ is the
penalty $\sigma_k$, the predicted decrease is positive, $x_{k+1} = x_k + s_k$ if
$\rho_k(s_k) \ge \eta_1$ and $x_{k+1} = x_k$ otherwise, and the radius $\Delta_{k+1}$ follows
the basic trust-region update for the ratio $\rho_k(s_k)$. -/
structure RelaxedSQPRun (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams)
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] where
  /-- The trial data of the run. -/
  trials : RelaxedSQPTrials f c P W
  /-- The penalty is carried to the next iteration: $\sigma_k$ is the previous penalty of iteration
  $k + 1$. -/
  penalty_update : ∀ k, trials.previousPenalty (k + 1) = trials.penalty k
  /-- The predicted decrease of every iteration is positive. -/
  prediction_pos : ∀ k, 0 < trials.prediction k
  /-- The iterate is updated by the ratio test for the merit function $f + \sigma_k \|c\|$. -/
  iterate_update : ∀ k, trials.x (k + 1) =
    acceptStep P.η₁ (sqpMerit f c (trials.penalty k)) (trials.x k) (trials.step k)
      (trials.prediction k)
  /-- The radius follows the basic trust-region update for the ratio of the trial step. -/
  radius_update : ∀ k, BTRRadiusUpdate P.toBTRParams (trials.ratio k (trials.step k))
    (trials.radius k) (trials.radius (k + 1))

/-- **Algorithms 15.4.2 and 15.4.3** of [conn2000trust], trial selection. For a threshold $\eta$,
the ratio $\rho$ of the original trial $s$, a condition "the normal step is small", an optional
bound $r$ on the correction, and a correction $u$, the trial passed to the acceptance test is
$s + u$ if $\rho < \eta$, the normal step is small and $\|u\| \le r$ when the bound is present.
Otherwise it is $s$.

**Reading.** The norm cap (15.4.94) is checked before the correction is tried. A correction that
violates it is not tried, and the original ratio is kept. -/
noncomputable def relaxedSQPProbe (η ρ : ℝ) (smallNormal : Prop)
    (cap : Option ℝ) (s correction : E) : E :=
  open Classical in
  if ρ < η ∧ smallNormal ∧ ∀ r, cap = some r → ‖correction‖ ≤ r then
    s + correction
  else s

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Algorithm 15.4.2** of [conn2000trust], Step 3. If the original trial is successful,
$\rho \ge \eta$, then the selected trial is the original trial $s$. -/
theorem relaxedSQPProbe_of_successful_original {η ρ : ℝ} (h : η ≤ ρ)
    (smallNormal : Prop) (cap : Option ℝ) (s correction : E) :
    relaxedSQPProbe η ρ smallNormal cap s correction = s := by
  simp [relaxedSQPProbe, not_lt_of_ge h]

/-- **Algorithm 15.4.2** of [conn2000trust], with an optional norm cap on the correction. A **run
with second-order corrections** consists of trial data, a constant $\chi \in (0, \theta)$ and
corrections $u_k$. The penalty is carried to the next iteration and every predicted decrease is
positive. Let $\hat s_k$ be the trial chosen by `ConnGouldToint.Chapter15.relaxedSQPProbe` from
the original ratio $\rho_k(s_k)$, the condition $\|n_k\| \le \chi \xi_N \Delta_k$ and the cap at
$\Delta_k$. Then $x_{k+1} = x_k + \hat s_k$ if $\rho_k(\hat s_k) \ge \eta_1$ and $x_{k+1} = x_k$
otherwise, and the radius follows the basic trust-region update for $\rho_k(\hat s_k)$.

**Reading.** Both the original and the corrected trial are tested against the predicted decrease
of the original step $s_k$.

The cap is a function of the radius with values in `Option ℝ`. The default `fun _ ↦ none`
imposes no cap. -/
structure RelaxedSQPCorrectedRun (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams)
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (cap : ℝ → Option ℝ := fun _ ↦ none) where
  /-- The trial data of the run. -/
  trials : RelaxedSQPTrials f c P W
  /-- The constant $\chi$ of the small-normal-step test $\|n_k\| \le \chi \xi_N \Delta_k$. -/
  χ : ℝ
  /-- The constant $\chi$ of the small-normal-step test lies in $(0, \theta)$. -/
  normal_test : χ ∈ Set.Ioo 0 P.θ
  /-- The proposed second-order corrections $u_k$. -/
  correction : ℕ → E
  /-- The penalty is carried to the next iteration: $\sigma_k$ is the previous penalty of iteration
  $k + 1$. -/
  penalty_update : ∀ k, trials.previousPenalty (k + 1) = trials.penalty k
  /-- The predicted decrease of every iteration is positive. -/
  prediction_pos : ∀ k, 0 < trials.prediction k
  /-- The iterate is updated by the ratio test applied to the selected trial, with the prediction of
  the original step. -/
  iterate_update : ∀ k,
    let s := relaxedSQPProbe P.η₁ (trials.ratio k (trials.step k))
      (‖trials.normal k‖ ≤ χ * P.ξN * trials.radius k) (cap (trials.radius k))
      (trials.step k) (correction k)
    trials.x (k + 1) = acceptStep P.η₁ (sqpMerit f c (trials.penalty k))
      (trials.x k) s (trials.prediction k)
  /-- The radius follows the basic trust-region update for the ratio of the selected trial. -/
  radius_update : ∀ k,
    let s := relaxedSQPProbe P.η₁ (trials.ratio k (trials.step k))
      (‖trials.normal k‖ ≤ χ * P.ξN * trials.radius k) (cap (trials.radius k))
      (trials.step k) (correction k)
    BTRRadiusUpdate P.toBTRParams (trials.ratio k s) (trials.radius k) (trials.radius (k + 1))

namespace RelaxedSQPCorrectedRun

variable {f : E → ℝ} {c : E → F} {P : RelaxedSQPParams} {cap : ℝ → Option ℝ}

/-- **Algorithm 15.4.2** of [conn2000trust], Step 3. The trial of iteration $k$ passed to the
acceptance test: the original step $s_k$ or the corrected step $s_k + u_k$, as chosen by
`ConnGouldToint.Chapter15.relaxedSQPProbe`. -/
noncomputable def probe (run : RelaxedSQPCorrectedRun f c P W cap) (k : ℕ) : E :=
  let tr := run.trials
  relaxedSQPProbe P.η₁ (tr.ratio k (tr.step k)) (‖tr.normal k‖ ≤ run.χ * P.ξN * tr.radius k)
    (cap (tr.radius k)) (tr.step k) (run.correction k)

/-- **Algorithm 15.4.2** of [conn2000trust], merit decrease. If the selected trial $\hat s_k$ of a
run with corrections satisfies $\rho_k(\hat s_k) \ge \eta_1$, then
$$\phi_k(x_k) - \phi_k(x_{k+1}) \ge \eta_1 \,(m_k(0) - m_k(s_k)),$$
where $\phi_k = f + \sigma_k \|c\|$. The decrease is measured against the prediction of the
original step, for both the original and the corrected trial. -/
theorem merit_drop_of_successful (run : RelaxedSQPCorrectedRun f c P W cap) (k : ℕ)
    (h : P.η₁ ≤ run.trials.ratio k (run.probe k)) :
    P.η₁ * run.trials.prediction k ≤
      sqpMerit f c (run.trials.penalty k) (run.trials.x k) -
        sqpMerit f c (run.trials.penalty k) (run.trials.x (k + 1)) := by
  have hs : run.trials.x (k + 1) = run.trials.x k + run.probe k :=
    (run.iterate_update k).trans (acceptStep_of_le h)
  rw [hs]
  exact sub_le_of_le_reductionRatio (run.prediction_pos k) h

end RelaxedSQPCorrectedRun

/-- **Algorithm 15.4.3** of [conn2000trust], with (15.4.79), (15.4.81), (15.4.82), (15.4.85),
(15.4.94) and (15.4.95). A run of Algorithm 15.4.2 whose corrections have the norm cap
$\|u_k\| \le \kappa \Delta_k$ for a constant $\kappa > 0$, together with multipliers $y_k$,
shifts $v_k$, correction Hessians $H^C_k$ and correction gradients $g^C_k$, such that:

* $\|v_k\| \le C \|s_k\|$ for a constant $C \ge 0$;
* at every cluster point $(x_*, y_*)$ of $(x_k, y_k)$ there is $C \ge 0$ with $\|g^C_k\| \le C
  \max\{\|x_k - x_*\|, \|y_k - y_*\|\} \|s_k\|$ for all sufficiently large $k$;
* there is $K > 0$ such that at every iteration with $\rho_k(s_k) < \eta_1$ and
  $\|n_k\| \le \chi \xi_N \Delta_k$ the correction solves $H^C_k u_k - A^{C*}_k y = -\bar g_k$,
  $A^C_k u_k = -c(x_k + s_k)$ for some $y$, where $A^C_k = c'(x_k + v_k)$, and every system
  $H^C_k z_1 - A^{C*}_k z_2 = b_1$, $A^C_k z_1 = b_2$ has a unique solution with
  $\|z\| \le K \|b\|$;
* the radius is kept, $\Delta_{k+1} = \Delta_k$, when the original trial is accepted with
  $\eta_1 \le \rho < \eta_2$ and $\|n_k\| \le \chi \xi_N \Delta_k$.

Here $\bar g_k = g^C_k$ if $s_k$ solves the standard SQP equations
$H_k s_k + \nabla f(x_k) = A_k^* y$, $A_k s_k + c(x_k) = 0$ for some $y$ (a full correction),
and $\bar g_k = 0$ otherwise (a partial correction).

**Reading.** The source derives the correction estimates from a uniformly bounded inverse of the
correction KKT matrix. Here unique solvability with the bound $K$ is a condition of the run.

The norm on $E \times F$ is the maximum of the norms of the two components. -/
structure RelaxedSQPStructuredRun (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams)
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] where
  /-- The factor $\kappa > 0$ of the correction norm cap $\|u_k\| \le \kappa \Delta_k$ in (15.4.94).
  -/
  correctionFactor : ℝ
  /-- The factor of the correction norm cap is positive. -/
  correctionFactor_pos : 0 < correctionFactor
  /-- The underlying run of Algorithm 15.4.2, with the norm cap $\|u_k\| \le \kappa \Delta_k$. -/
  corrected : RelaxedSQPCorrectedRun f c P W (fun Δ ↦ some (correctionFactor * Δ))
  /-- The multiplier estimates $y_k$. -/
  multiplier : ℕ → F
  /-- The shifts $v_k$: the Jacobian of the correction is evaluated at $x_k + v_k$. -/
  correctionShift : ℕ → E
  /-- The Hessians $H^C_k$ of the correction systems. -/
  correctionHessian : ℕ → E →L[ℝ] E
  /-- The gradients $g^C_k$ of the full-correction systems. -/
  correctionGradient : ℕ → E
  /-- The shifts are of the order of the steps: $\|v_k\| \le C \|s_k\|$ for a constant $C \ge 0$. -/
  shift_bound : ∃ C ≥ 0, ∀ k, ‖correctionShift k‖ ≤ C * ‖corrected.trials.step k‖
  /-- At every cluster point $(x_*, y_*)$ of $(x_k, y_k)$, eventually $\|g^C_k\| \le C \max\{\|x_k -
  x_*\|, \|y_k - y_*\|\} \|s_k\|$ for a constant $C \ge 0$. -/
  correction_gradient_bound : ∀ xstar ystar,
    MapClusterPt (xstar, ystar) atTop (fun k ↦ (corrected.trials.x k, multiplier k)) →
    ∃ C ≥ 0, ∀ᶠ k in atTop,
      ‖correctionGradient k‖ ≤ C *
        max ‖corrected.trials.x k - xstar‖ ‖multiplier k - ystar‖ *
        ‖corrected.trials.step k‖
  /-- At a failed original trial with a small normal step, the correction solves the full or partial
  correction system, and every correction system has a unique solution bounded by a uniform
  constant $K > 0$ times the data. -/
  correction_system : ∃ K > 0, ∀ k,
    let trials := corrected.trials
    trials.ratio k (trials.step k) < P.η₁ →
    ‖trials.normal k‖ ≤ corrected.χ * P.ξN * trials.radius k →
    let x := trials.x k
    let s := trials.step k
    let A := fderiv ℝ c x
    let Ac := fderiv ℝ c (x + correctionShift k)
    let Hc := correctionHessian k
    let u := corrected.correction k
    let standard := ∃ y : F, trials.H k s + gradient f x = A.adjoint y ∧ A s + c x = 0
    let gc := open Classical in if standard then correctionGradient k else 0
    (∃ y : F, Hc u - Ac.adjoint y = -gc ∧ Ac u = -c (x + s)) ∧
      ∀ b : E × F, ∃ z : E × F,
        Hc z.1 - Ac.adjoint z.2 = b.1 ∧ Ac z.1 = b.2 ∧ ‖z‖ ≤ K * ‖b‖ ∧
          ∀ z' : E × F, Hc z'.1 - Ac.adjoint z'.2 = b.1 → Ac z'.1 = b.2 → z' = z
  /-- The radius is kept after an accepted original trial with $\eta_1 \le \rho < \eta_2$ and a
  small normal step, as in (15.4.95). -/
  keep_radius : ∀ k,
    let trials := corrected.trials
    let s := relaxedSQPProbe P.η₁ (trials.ratio k (trials.step k))
      (‖trials.normal k‖ ≤ corrected.χ * P.ξN * trials.radius k)
      (some (correctionFactor * trials.radius k)) (trials.step k) (corrected.correction k)
    P.η₁ ≤ trials.ratio k s → trials.ratio k s < P.η₂ →
    trials.x (k + 1) = trials.x k + trials.step k →
    ‖trials.normal k‖ ≤ corrected.χ * P.ξN * trials.radius k →
    trials.radius (k + 1) = trials.radius k

/-- **Algorithm 15.4.3** of [conn2000trust], (15.4.95). In a run of Algorithm 15.4.3, if the
original trial satisfies $\eta_1 \le \rho_k(s_k) < \eta_2$ and
$\|n_k\| \le \chi \xi_N \Delta_k$, then $\Delta_{k+1} = \Delta_k$. -/
theorem RelaxedSQPStructuredRun.radius_eq_of_original_moderate
    {f : E → ℝ} {c : E → F} {P : RelaxedSQPParams} (run : RelaxedSQPStructuredRun f c P W)
    (k : ℕ) (h₁ : P.η₁ ≤ run.corrected.trials.ratio k (run.corrected.trials.step k))
    (h₂ : run.corrected.trials.ratio k (run.corrected.trials.step k) < P.η₂)
    (hsmall : ‖run.corrected.trials.normal k‖ ≤ run.corrected.χ * P.ξN *
      run.corrected.trials.radius k) :
    run.corrected.trials.radius (k + 1) = run.corrected.trials.radius k := by
  let tr := run.corrected.trials
  have hp : run.corrected.probe k = tr.step k :=
    relaxedSQPProbe_of_successful_original h₁ _ _ _ _
  have h₁' : P.η₁ ≤ tr.ratio k (run.corrected.probe k) := by rw [hp]; exact h₁
  have h₂' : tr.ratio k (run.corrected.probe k) < P.η₂ := by rw [hp]; exact h₂
  have ha : tr.x (k + 1) = tr.x k + run.corrected.probe k :=
    (run.corrected.iterate_update k).trans (acceptStep_of_le h₁')
  have hs : tr.x (k + 1) = tr.x k + tr.step k := by rwa [hp] at ha
  exact run.keep_radius k h₁' h₂' hs hsmall

/-- **Algorithm 15.4.4** of [conn2000trust], with AA.2d. A run of Algorithm 15.4.3 together with a
constant $\kappa \in (0, 1/2)$ such that at every iteration
$$\tau_k < 0 \implies q^T_k(0) - q^T_k(t_k) \ge -\kappa \tau_k \Delta_k^2,$$
where $\tau_k$ is the infimum of the Rayleigh quotients $\langle w, H^N_k w\rangle / \|w\|^2$ of
the reduced Hessian $H^N_k = N_k^* H_k N_k$ over $w \ne 0$.

**Reading.** The algorithm follows the boxed rule of the source and adds the negative-curvature
condition AA.2d to the tangential step of Algorithm 15.4.3.

The infimum is `ConnGouldToint.Chapter08.hilbertRayleighFloor`. It is $0$ when $W$ is the zero
space. -/
structure RelaxedSQPSecondOrderRun (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams)
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] where
  /-- The underlying run of Algorithm 15.4.3. -/
  run : RelaxedSQPStructuredRun f c P W
  /-- The coefficient $\kappa$ of the negative-curvature condition AA.2d. -/
  κ : ℝ
  /-- The negative-curvature coefficient lies in $(0, 1/2)$. -/
  curvature_fraction : κ ∈ Set.Ioo 0 (1 / 2)
  /-- The tangential step satisfies the negative-curvature decrease AA.2d when the reduced Hessian
  has a negative Rayleigh quotient. -/
  curvature_decrease : ∀ k,
    let tr := run.corrected.trials
    let N := tr.N k
    let τ := Chapter08.hilbertRayleighFloor (N.adjoint.comp ((tr.H k).comp N))
    let m := sqpTangentialModel (gradient f (tr.x k)) (tr.H k) (tr.normal k)
    τ < 0 → -κ * τ * (tr.radius k) ^ 2 ≤ m 0 - m (tr.tangential k)

end ConnGouldToint.Chapter15
