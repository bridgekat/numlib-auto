/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Basic
import NumlibSurface.ConnGouldToint.Chapter06.Section03
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence
import Numlib.Optimization.ModelBased.RatioTest

/-!
# Conn, Gould and Toint, Section 15.4: Relaxed linearization SQP

Section 15.4 of [conn2000trust] studies composite-step trust-region SQP methods for minimizing
$f(x)$ subject to $c(x) = 0$. Progress is measured by the exact penalty function
$\phi_\sigma(x) = f(x) + \sigma \|c(x)\|$. A step $s = n + t$ consists of a normal step $n$, which
reduces the residual $\|c + A n\|$ of the linearized constraints, and a tangential step $t$ in the
null space of $A$, which reduces the quadratic model. The overall model is
$$m(s) = f + \langle g, s \rangle + \tfrac{1}{2} \langle s, H s \rangle + \sigma \|c + A s\|.$$
This module formalizes the models and their decrease identities, the penalty update of Algorithm
15.4.1, Lemmas 15.4.1–15.4.5, 15.4.7, 15.4.9, 15.4.17, 15.4.18 and 15.4.21, Theorems 15.4.6, 15.4.8,
15.4.10–15.4.12, 15.4.16 and 15.4.19, and Corollary 15.4.20, together with the radius and decrease
constants of their proofs. The Cauchy points and the quadratic model come from
`NumlibSurface.ConnGouldToint.Chapter06.Section03`, the Taylor estimates from
`Numlib.Analysis.Calculus.Taylor`, and the reduction ratio from
`Numlib.Optimization.ModelBased.RatioTest`.

## Main definitions

* Section 15.4.1.1, `ConnGouldToint.Chapter15.sqpMerit` and
  `ConnGouldToint.Chapter15.sqpNormalModel`: the merit function $f + \sigma \|c\|$ and the normal
  model $\|c + A n\|$.
* Equation (15.4.4), `ConnGouldToint.Chapter15.sqpOverallModel`: the overall model.
* Equation (15.4.5), `ConnGouldToint.Chapter15.sqpTangentialModel`: the tangential model after the
  normal step.
* Equation (15.4.8), `ConnGouldToint.Chapter15.sqpPenaltyThreshold`: the penalty threshold.
* Equation (15.4.12), `ConnGouldToint.Chapter15.IsSQPNormalScaling`: the scaling of the trial normal
  step (assumption AA.1h).
* Section 15.4.1.4, `ConnGouldToint.Chapter15.sqpNormalizedMerit`: the normalized merit function.
* Equations (15.4.45) and (15.4.127), `ConnGouldToint.Chapter15.sqpCriticalityNeighborhood`: the
  neighborhood on which a criticality measure stays positive.
* Equation (15.4.50), `ConnGouldToint.Chapter15.sqpNeighborhoodRadiusFloor`: the radius floor in the
  neighborhood.
* Equation (15.4.71), `ConnGouldToint.Chapter15.sqpTangentialAcceptanceRadius`: the radius below
  which the tangential trial is accepted.
* Equation (15.4.131), `ConnGouldToint.Chapter15.sqpNormalCurvatureBound`: the curvature bound
  $1 + B^2$ of the normal model.
* Equations (15.4.57) and (15.4.140), `ConnGouldToint.Chapter15.sqpFeasibilityExitCoeff` and
  `ConnGouldToint.Chapter15.sqpNormalCriticalityExitCoeff`: the decrease coefficients when the
  iterates leave a neighborhood.
* Algorithm 15.4.1, Step 2, `ConnGouldToint.Chapter15.sqpPenaltyUpdate`: the penalty update.
* Algorithm 15.4.1, `ConnGouldToint.Chapter15.SQPTangentialRun`: the scalar data of the tail of a
  run with a fixed penalty.

## Main results

* Equation (15.4.6), `ConnGouldToint.Chapter15.sqpOverallModel_decrease`: the overall model decrease
  splits into the tangential, normal and objective parts.
* Equations (15.4.7)–(15.4.8), `ConnGouldToint.Chapter15.sqpPenaltyThreshold_le_iff`: (15.4.7) holds
  exactly above the threshold.
* Equation (15.4.16), `ConnGouldToint.Chapter15.sqpNormalModel_decrease_scaled`: the exact normal
  decrease $\alpha \|c\|$.
* Lemma 15.4.1, `ConnGouldToint.Chapter15.lemma_15_4_1`: the normal decrease of the scaled step.
* Lemma 15.4.2, `ConnGouldToint.Chapter15.lemma_15_4_2`: the tangential Cauchy decrease in
  null-space coordinates.
* Lemma 15.4.3, `ConnGouldToint.Chapter15.lemma_15_4_3`: the model error is of order
  $(1 + \sigma) \|s\|^2$.
* Lemma 15.4.4, `ConnGouldToint.Chapter15.lemma_15_4_4`: at a noncritical iterate, small radii give
  acceptance.
* Lemma 15.4.5, `ConnGouldToint.Chapter15.lemma_15_4_5`: the normalized merit decreases along the
  successful iterates.
* Theorem 15.4.6, `ConnGouldToint.Chapter15.theorem_15_4_6`: the constraint residuals tend to zero.
* Lemma 15.4.7, `ConnGouldToint.Chapter15.lemma_15_4_7`: the normal decrease is at least
  $\|\alpha n_C\| / \kappa$.
* Theorem 15.4.8, `ConnGouldToint.Chapter15.theorem_15_4_8`: the penalty stabilizes and the normal
  objective loss is bounded by the normal decrease.
* Lemma 15.4.9, `ConnGouldToint.Chapter15.lemma_15_4_9`: a positive fraction of the tangential
  decrease bounds the model decrease from below.
* Theorems 15.4.10 and 15.4.11, `ConnGouldToint.Chapter15.theorem_15_4_10` and
  `ConnGouldToint.Chapter15.theorem_15_4_11`: the reduced gradient has limit inferior $0$, and limit
  $0$ under a variation bound.
* Theorem 15.4.12, `ConnGouldToint.Chapter15.theorem_15_4_12`: convergence of the composite-step
  method with corrections.
* Theorem 15.4.16, `ConnGouldToint.Chapter15.theorem_15_4_16`: some cluster point satisfies the
  second-order test.
* Lemma 15.4.17, `ConnGouldToint.Chapter15.lemma_15_4_17`: the Cauchy decrease of the normal model.
* Lemma 15.4.18, `ConnGouldToint.Chapter15.lemma_15_4_18`: at a noncritical iterate, small radii
  give acceptance.
* Theorem 15.4.19, `ConnGouldToint.Chapter15.theorem_15_4_19`: the normal criticality vector tends
  to zero.
* `ConnGouldToint.Chapter15.sqp_normal_criticality_of_accepted_decrease`: the same when the accepted
  decrease may come from a corrected trial, as in Theorem 15.4.23.
* Corollary 15.4.20, `ConnGouldToint.Chapter15.corollary_15_4_20`: the residuals tend to zero.
* Lemma 15.4.21, `ConnGouldToint.Chapter15.lemma_15_4_21`: the normal decrease is at least a
  multiple of the normal step.
* `ConnGouldToint.Chapter15.printed_tangential_coefficient_nonpos` and
  `ConnGouldToint.Chapter15.sqp_exit_max_counterexamples`: the printed constants in Lemma 15.4.9,
  (15.4.57) and (15.4.140) are wrong.

## Conventions

* The constraint map takes values in a real normed space $F$, and its Jacobian $A$ is
  `fderiv ℝ c x`. The quadratic model $q(s) = f_0 + \langle g, s \rangle + \frac{1}{2} \langle s, H
  s \rangle$ is `ConnGouldToint.Chapter06.quadraticModel`.
* The ratio $\rho$ is `Optimization.reductionRatio` of the merit function, the actual decrease
  divided by the predicted decrease $\delta$.
* The convergence theorems are stated for sequences of iterates, steps, radii and decreases with the
  properties of the algorithm as hypotheses: $S$ is the set of successful iterations,
  $\gamma \Delta_k \le \Delta_{k+1}$ always, $\Delta_{k+1} \le \gamma_2 \Delta_k$ with
  $\gamma_2 < 1$ after a rejection, and $\Delta_k \le \Delta_{k+1}$ after a very successful
  iteration.

## Deviations from the source

* **Representation.** The composite models use inner-product operators and normalize the tangential
  model at zero. See `ConnGouldToint.Chapter15.sqpMerit`, `ConnGouldToint.Chapter15.sqpNormalModel`,
  `ConnGouldToint.Chapter15.sqpOverallModel`, `ConnGouldToint.Chapter15.sqpTangentialModel`,
  `ConnGouldToint.Chapter15.sqpOverallModel_decrease`.
* **Convention.** The penalty threshold equivalence uses positive normal decrease; the scalar
  formula is totalized at zero. See `ConnGouldToint.Chapter15.sqpPenaltyThreshold`,
  `ConnGouldToint.Chapter15.sqpPenaltyThreshold_le_iff`.
* **Reading.** Normal scaling defines a zero-step branch and makes the stability bound on the
  unscaled normal solution explicit. See `ConnGouldToint.Chapter15.IsSQPNormalScaling`,
  `ConnGouldToint.Chapter15.sqpNormalModel_decrease_scaled`,
  `ConnGouldToint.Chapter15.lemma_15_4_1`, `ConnGouldToint.Chapter15.lemma_15_4_7`.
* **Reading.** The tangential Cauchy decrease is evaluated at the named Cauchy point. See
  `ConnGouldToint.Chapter15.lemma_15_4_2`.
* **Correction.** The merit-model error needs derivative control along the entire trial segment. See
  `ConnGouldToint.Chapter15.lemma_15_4_3`.
* **Reading.** The small-radius acceptance lemmas make uniform trial error and two-case predicted
  decrease explicit. See `ConnGouldToint.Chapter15.lemma_15_4_4`,
  `ConnGouldToint.Chapter15.lemma_15_4_18`.
* **Representation.** Normalized merit descent is stated on the accepted subsequence with positive
  nondecreasing weights. See `ConnGouldToint.Chapter15.sqpNormalizedMerit`,
  `ConnGouldToint.Chapter15.lemma_15_4_5`.
* **Generalization.** The same Lipschitz neighborhood lemma applies to both criticality measures.
  See `ConnGouldToint.Chapter15.sqpCriticalityNeighborhood`,
  `ConnGouldToint.Chapter15.sqpCriticalityNeighborhood_bounds`.
* **Correction.** The neighborhood radius floor depends on the entry radius as well as the success
  threshold. See `ConnGouldToint.Chapter15.sqpNeighborhoodRadiusFloor`,
  `ConnGouldToint.Chapter15.sqpNeighborhoodRadiusFloor_le`.
* **Correction.** The tangential acceptance threshold includes the effective decrease and
  model-error coefficients. See `ConnGouldToint.Chapter15.sqpTangentialAcceptanceRadius`,
  `ConnGouldToint.Chapter15.sqpTangentialAcceptanceRadius_ratio`.
* **Generalization.** The uniform normal curvature bound uses a Jacobian norm bound without assuming
  that it is attained. See `ConnGouldToint.Chapter15.sqpNormalCurvatureBound`,
  `ConnGouldToint.Chapter15.sqpNormalCurvatureBound_le`.
* **Correction.** The two exit cases combine with minima; explicit examples disprove the printed
  maxima. See `ConnGouldToint.Chapter15.sqpFeasibilityExitCoeff`,
  `ConnGouldToint.Chapter15.sqpFeasibilityExitCoeff_bound`,
  `ConnGouldToint.Chapter15.sqpNormalCriticalityExitCoeff`,
  `ConnGouldToint.Chapter15.sqpNormalCriticalityExitCoeff_bound`,
  `ConnGouldToint.Chapter15.sqp_exit_max_counterexamples`.
* **Reading.** The feasibility and normal-criticality limits expose trial errors, accepted-step
  variation and the rank bound needed for the corollary. See
  `ConnGouldToint.Chapter15.theorem_15_4_6`,
  `ConnGouldToint.Chapter15.sqp_normal_criticality_of_accepted_decrease`,
  `ConnGouldToint.Chapter15.theorem_15_4_19`, `ConnGouldToint.Chapter15.corollary_15_4_20`.
* **Reading.** Penalty stabilization is derived from explicit requirements and a positive additive
  increase. See `ConnGouldToint.Chapter15.sqpPenaltyUpdate`,
  `ConnGouldToint.Chapter15.sqpPenaltyUpdate_eventually_constant`,
  `ConnGouldToint.Chapter15.theorem_15_4_8`.
* **Correction.** The revised tangential coefficient is always positive on the stated domain, unlike
  the printed expression. See `ConnGouldToint.Chapter15.lemma_15_4_9`,
  `ConnGouldToint.Chapter15.printed_tangential_coefficient_nonpos`.
* **Correction.** The tangential limits require uniform trial model error and reduced-gradient
  controls, with extra variation control for a full limit. See
  `ConnGouldToint.Chapter15.SQPTangentialRun`,
  `ConnGouldToint.Chapter15.sqpReducedGradient_perturbation`,
  `ConnGouldToint.Chapter15.theorem_15_4_10`, `ConnGouldToint.Chapter15.theorem_15_4_11`.
* **Reading.** The normal Cauchy decrease uses the adjoint gradient and a totalized ratio. See
  `ConnGouldToint.Chapter15.lemma_15_4_17`.
* **Correction.** The normal-step estimate uses the corrected singular-value factor and explicit
  decomposition bounds. See `ConnGouldToint.Chapter15.lemma_15_4_21`.
* **Correction.** The corrected-step convergence uses original-trial small-radius success, with
  accepted-step control for the full tangential limit. See
  `ConnGouldToint.Chapter15.sqp_normal_correction_progress`,
  `ConnGouldToint.Chapter15.theorem_15_4_12`.
* **Correction.** The second-order limit theorem requires coverage of the curvature tail and uniform
  two-case decrease. See `ConnGouldToint.Chapter15.sqp_secondOrder_correction_progress`,
  `ConnGouldToint.Chapter15.theorem_15_4_16`.
* **Equation (15.4.12)** (reading). The scaling interval applies to a nonzero trial normal step; a
  zero trial step has the scaling $1$. See `ConnGouldToint.Chapter15.IsSQPNormalScaling`.
* **Lemma 15.4.2** (reading). The left-hand side is evaluated at the stated Cauchy step. See
  `ConnGouldToint.Chapter15.lemma_15_4_2`.
* **Lemma 15.4.3** (correction). The Lipschitz bounds hold along the full trial segment, including
  trial points that are rejected. See `ConnGouldToint.Chapter15.sqp_trialSegment_counterexample`.
* **Theorem 15.4.6** (reading). The radius argument uses the update after a very successful
  iteration. See `ConnGouldToint.Chapter15.theorem_15_4_6`.
* **Lemma 15.4.9** (correction). The coefficient $\nu \sigma / (\nu \sigma + B)$ is positive for
  every bound $B \ge 0$; the printed coefficient can be negative. See
  `ConnGouldToint.Chapter15.printed_tangential_coefficient_nonpos`.
* **Equation (15.4.50)** (correction). The radius floor includes the radius at entry to the
  neighborhood. See `ConnGouldToint.Chapter15.sqpNeighborhoodRadiusFloor_le`.
* **Equations (15.4.57) and (15.4.140)** (correction). The two exit cases give a common bound with
  the minimum of the two coefficients, not the maximum. See
  `ConnGouldToint.Chapter15.sqp_exit_max_counterexamples`.
* **Equation (15.4.71) and Theorem 15.4.10** (correction). The radius threshold includes the Cauchy
  decrease coefficient and the model error coefficient, and the error bound holds uniformly on the
  trial segments. See `ConnGouldToint.Chapter15.sqpTangentialAcceptanceRadius`.
* **Theorem 15.4.11** (correction). The uniform control of the variation of the reduced gradient on
  accepted steps is a hypothesis. See `ConnGouldToint.Chapter15.theorem_15_4_11`.
* **Theorem 15.4.12** (correction). The acceptance guarantee at small radii concerns the original
  trial, while the accepted decrease may come from either trial. See
  `ConnGouldToint.Chapter15.theorem_15_4_12`.
* **Theorem 15.4.16** (correction). The finite cluster set must control the tail of the iterates,
  and the proof uses the maximum curvature over the cluster points. See
  `ConnGouldToint.Chapter15.theorem_15_4_16`.
* **Lemma 15.4.18 and Theorem 15.4.19** (correction). The model error bound holds uniformly on the
  trial segments, and the variation of the normal criticality on accepted steps is controlled. See
  `ConnGouldToint.Chapter15.theorem_15_4_19`.
* **Equation (15.4.131)** (reading). The curvature bound uses a uniform bound on the Jacobian norms,
  not an attained maximum. See `ConnGouldToint.Chapter15.sqpNormalCurvatureBound_le`.
* **Lemma 15.4.21, equation (15.4.142)** (correction). The second entry of the minimum uses the
  reciprocal of the rank constant. See `ConnGouldToint.Chapter15.lemma_15_4_21`.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

open Chapter06

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Section 15.4.1.1** of [conn2000trust]. For $f : E \to \mathbb{R}$, $c : E \to F$ and
$\sigma \in \mathbb{R}$, the **exact penalty merit function** is
$\phi_\sigma(x) = f(x) + \sigma \|c(x)\|$.

**Reading.** The models are written on inner-product spaces. The tangential model omits its additive
constant, which cancels in model decrease. The decrease identity assumes a symmetric Hessian and a
tangential direction in the exact Jacobian kernel.
-/
noncomputable def sqpMerit (f : E → ℝ) (c : E → F) (σ : ℝ) (x : E) : ℝ :=
  f x + σ * ‖c x‖

/-- **Section 15.4.1.1** of [conn2000trust]. For $c \in F$ and a continuous linear map
$A : E \to F$, the **normal model** is the residual $\|c + A n\|$ of the linearized constraint
at the step $n$.

**Reading.** The models are written on inner-product spaces. The tangential model omits its additive
constant, which cancels in model decrease. The decrease identity assumes a symmetric Hessian and a
tangential direction in the exact Jacobian kernel.
-/
noncomputable def sqpNormalModel (c : F) (A : E →L[ℝ] F) (n : E) : ℝ :=
  ‖c + A n‖

/-- **Equation (15.4.4)** of [conn2000trust]. For $f_0, \sigma \in \mathbb{R}$, $g \in E$, a
continuous linear map $H : E \to E$, $c \in F$ and $A : E \to F$, the **overall model** is
$$m(s) = f_0 + \langle g, s \rangle + \tfrac{1}{2} \langle s, H s \rangle + \sigma \|c + A
  s\|.$$

**Reading.** The models are written on inner-product spaces. The tangential model omits its additive
constant, which cancels in model decrease. The decrease identity assumes a symmetric Hessian and a
tangential direction in the exact Jacobian kernel.
-/
noncomputable def sqpOverallModel (f₀ : ℝ) (g : E) (H : E →L[ℝ] E)
    (c : F) (A : E →L[ℝ] F) (σ : ℝ) (s : E) : ℝ :=
  quadraticModel f₀ g H.toLinearMap s + σ * sqpNormalModel c A s

/-- **Equation (15.4.5)** of [conn2000trust]. After the normal step $n$, the **tangential model** is
$$m_T(t) = \langle g + H n, t \rangle + \tfrac{1}{2} \langle t, H t \rangle.$$

**Reading.** The models are written on inner-product spaces. The tangential model omits its additive
constant, which cancels in model decrease. The decrease identity assumes a symmetric Hessian and a
tangential direction in the exact Jacobian kernel.
-/
noncomputable def sqpTangentialModel (g : E) (H : E →L[ℝ] E) (n t : E) : ℝ :=
  quadraticModel 0 (g + H n) H.toLinearMap t

/-- **Equation (15.4.6)** of [conn2000trust]. Let $H$ be symmetric, and let $A t = 0$. Then
$$m(0) - m(n + t) = \bigl(m_T(0) - m_T(t)\bigr) + \sigma \bigl(\|c\| - \|c + A n\|\bigr) +
  \bigl(q(0) - q(n)\bigr),$$
where $q(s) = f_0 + \langle g, s \rangle + \frac{1}{2} \langle s, H s \rangle$. The three terms
are the tangential decrease, the penalized decrease of the normal model, and the decrease of the
objective model along the normal step.

**Reading.** The models are written on inner-product spaces. The tangential model omits its additive
constant, which cancels in model decrease. The decrease identity assumes a symmetric Hessian and a
tangential direction in the exact Jacobian kernel.
-/
theorem sqpOverallModel_decrease (f₀ σ : ℝ) (g : E) (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (c : F) (A : E →L[ℝ] F) (n t : E) (ht : A t = 0) :
    sqpOverallModel f₀ g H c A σ 0 - sqpOverallModel f₀ g H c A σ (n + t) =
      (sqpTangentialModel g H n 0 - sqpTangentialModel g H n t) +
      σ * (sqpNormalModel c A 0 - sqpNormalModel c A n) +
      (quadraticModel f₀ g H.toLinearMap 0 - quadraticModel f₀ g H.toLinearMap n) := by
  have hs : ⟪n, H t⟫ = ⟪H n, t⟫ := (hH n t).symm
  simp [sqpOverallModel, sqpNormalModel, sqpTangentialModel, quadraticModel,
    inner_add_left, inner_add_right, ht, hs, real_inner_comm t (H n)]
  ring

/-- **Equation (15.4.8)** of [conn2000trust]. For the fraction $\nu$, the normal decrease
$\delta_N > 0$, the tangential decrease $\delta_T$ and the objective decrease $\delta_q$ along
the normal step, the **penalty threshold** is
$$\sigma_{\mathrm{req}} = -\frac{\delta_q + \delta_T}{(1 - \nu) \delta_N}.$$

**Reading.** The scalar threshold is totalized when the denominator vanishes. The equivalence with
sufficient overall decrease assumes positive normal decrease and a fraction below one.
-/
noncomputable def sqpPenaltyThreshold (ν dN dT dq : ℝ) : ℝ :=
  -(dq + dT) / ((1 - ν) * dN)

/-- **Equations (15.4.7)–(15.4.8)** of [conn2000trust]. Let $\nu < 1$ and $\delta_N > 0$. Then
$\sigma_{\mathrm{req}} \le \sigma$ if and only if
$$\nu \sigma \delta_N \le \delta_T + \sigma \delta_N + \delta_q,$$
that is, the overall model decrease is at least $\nu \sigma \delta_N$.

**Reading.** The scalar threshold is totalized when the denominator vanishes. The equivalence with
sufficient overall decrease assumes positive normal decrease and a fraction below one.
-/
theorem sqpPenaltyThreshold_le_iff {ν dN dT dq σ : ℝ} (hν : ν < 1) (hN : 0 < dN) :
    sqpPenaltyThreshold ν dN dT dq ≤ σ ↔ ν * σ * dN ≤ dT + σ * dN + dq := by
  unfold sqpPenaltyThreshold
  rw [div_le_iff₀ (mul_pos (sub_pos.mpr hν) hN)]
  constructor <;> intro h <;> linarith only [show σ * ((1 - ν) * dN) =
    σ * dN - ν * σ * dN by ring, h]

/-- **Equation (15.4.12)** of [conn2000trust] (assumption AA.1h). A factor $\alpha$ is an
**admissible scaling** of the trial normal step $n_C$ if $\alpha = 1$ when $n_C = 0$, and
otherwise
$$\min\Bigl\{1, \frac{\theta \xi \Delta}{\|n_C\|}\Bigr\} \le \alpha \le \min\Bigl\{1, \frac{\xi
  \Delta}{\|n_C\|}\Bigr\}.$$

**Reading.** The interval (15.4.12) divides by $\|n_C\|$, so it applies only to a nonzero trial
step. At a zero trial step the scaling is $1$.

**Reading.** Scaling chooses one when the trial normal step is zero, and otherwise uses the printed
interval. The step and decrease estimates take an explicit bound for the linearized normal solution.
-/
def IsSQPNormalScaling (nC : E) (θ ξ Δ α : ℝ) : Prop :=
  open Classical in
  if nC = 0 then α = 1 else
    α ∈ Set.Icc (min 1 (θ * ξ * Δ / ‖nC‖)) (min 1 (ξ * Δ / ‖nC‖))

/-- **Equation (15.4.16)** of [conn2000trust]. If $A n_C + c = 0$ and $\alpha \le 1$, then
$$\|c\| - \|c + \alpha A n_C\| = \alpha \|c\|.$$

**Reading.** Scaling chooses one when the trial normal step is zero, and otherwise uses the printed
interval. The step and decrease estimates take an explicit bound for the linearized normal solution.
-/
theorem sqpNormalModel_decrease_scaled {c : F} {A : E →L[ℝ] F} {nC : E} {α : ℝ}
    (hlin : A nC + c = 0) (hα : α ≤ 1) :
    sqpNormalModel c A 0 - sqpNormalModel c A (α • nC) = α * ‖c‖ := by
  have hn : A nC = -c := eq_neg_of_add_eq_zero_left hlin
  simp only [sqpNormalModel, map_zero, add_zero, map_smul, hn]
  rw [show c + α • (-c) = (1 - α) • c by rw [smul_neg, sub_smul, one_smul, sub_eq_add_neg],
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hα)]
  ring

/-- **Lemma 15.4.1** of [conn2000trust]. Let $\theta, \xi, \Delta \ge 0$ and $\kappa > 0$. Let $n_C$
satisfy $A n_C + c = 0$ and $\|n_C\| \le \kappa \|c\|$, and let $\alpha$ be an admissible
scaling of $n_C$. Then the normal decrease $\delta_N = \|c\| - \|c + \alpha A n_C\|$ satisfies
$$\min\Bigl\{\|c\|, \frac{\theta \xi}{\kappa} \Delta\Bigr\} \le \delta_N \le \|c\|.$$

The statement includes the case $n_C = 0$, in which $c = 0$.

**Reading.** Scaling chooses one when the trial normal step is zero, and otherwise uses the printed
interval. The step and decrease estimates take an explicit bound for the linearized normal solution.
-/
theorem lemma_15_4_1 {c : F} {A : E →L[ℝ] F} {nC : E} {θ ξ Δ α κ : ℝ}
    (hθ : 0 ≤ θ) (hξ : 0 ≤ ξ) (hΔ : 0 ≤ Δ) (hκ : 0 < κ)
    (hlin : A nC + c = 0) (hbound : ‖nC‖ ≤ κ * ‖c‖)
    (hscale : IsSQPNormalScaling nC θ ξ Δ α) :
    let dN := sqpNormalModel c A 0 - sqpNormalModel c A (α • nC)
    min ‖c‖ (θ * ξ / κ * Δ) ≤ dN ∧ dN ≤ ‖c‖ := by
  by_cases hn : nC = 0
  · have hc : c = 0 := by simpa [hn] using hlin
    simp [hc, hn, sqpNormalModel]
  have hn' : 0 < ‖nC‖ := norm_pos_iff.mpr hn
  simp only [IsSQPNormalScaling, ite_eq_right hn, Set.mem_Icc] at hscale
  have hα : α ≤ 1 := hscale.2.trans (min_le_left _ _)
  dsimp only
  rw [sqpNormalModel_decrease_scaled hlin hα]
  refine ⟨?_, mul_le_of_le_one_left (norm_nonneg c) hα⟩
  have hcompare : θ * ξ / κ * Δ ≤ (θ * ξ * Δ / ‖nC‖) * ‖c‖ := by
    have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ θ * ξ * Δ by positivity)
    field_simp
    nlinarith only [hh]
  have h := mul_le_mul_of_nonneg_right hscale.1 (norm_nonneg c)
  rw [min_mul_of_nonneg _ _ (norm_nonneg c), one_mul] at h
  exact (min_le_min le_rfl hcompare).trans h

/-- **Lemma 15.4.2** of [conn2000trust]. Let $N : Z \to E$ be an injective continuous linear map
between real inner product spaces. (In the source the columns of $N$ form a basis of the null
space of the constraint Jacobian, which makes $N$ injective; the lemma uses only injectivity.)
Let $g \in Z$, $H : Z \to Z$ continuous linear, $R \ge 0$, and let $z_C$ be a Cauchy point of
the reduced model $q(z) = \langle g, z \rangle + \frac{1}{2} \langle z, H z \rangle$ for the
trust-region norm $z \mapsto \|N z\|$ and the radius $R$. Then
$$\tfrac{1}{2} \|g\| \min\Bigl\{\frac{R}{\|N\|}, \frac{\|g\|}{1 + \|H\|}\Bigr\} \le -q(z_C).$$

**Reading.** The left-hand side of the source is evaluated at the stated Cauchy step $z_C$.

The Cauchy point is `ConnGouldToint.Chapter06.IsCauchyPoint`, and $1 + \|H\|$ is
`ConnGouldToint.Chapter06.quadraticCurvatureBound`.

**Reading.** The decrease is evaluated at the constrained Cauchy step appearing in the hypothesis.
The reduced-space embedding is supplied as an injective linear map and its operator norm bounds the
feasible ray.
-/
theorem lemma_15_4_2 {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (N : Z →L[ℝ] E) (hN : Function.Injective N) (g : Z) (H : Z →L[ℝ] Z)
    {R : ℝ} (hR : 0 ≤ R) {zC : Z}
    (hC : IsCauchyPoint (quadraticModel 0 g H.toLinearMap)
      ((normSeminorm ℝ E).comp N.toLinearMap) g R zC) :
    (1 / 2) * ‖g‖ * min (R / ‖N‖) (‖g‖ / quadraticCurvatureBound H) ≤
      0 - quadraticModel 0 g H.toLinearMap zC := by
  let p := (normSeminorm ℝ E).comp N.toLinearMap
  have hp (v : Z) (hv : p v = 0) : v = 0 := by
    change ‖N v‖ = 0 at hv
    exact hN ((norm_eq_zero.mp hv).trans N.map_zero.symm)
  have h := theorem_6_3_1 0 g H p hp hR hC
  by_cases hg : g = 0
  · simpa [hg] using h
  have hpg : 0 < ‖N g‖ := norm_pos_iff.mpr (fun hz => hg (hN (hz.trans N.map_zero.symm)))
  have hN' : 0 < ‖N‖ := by
    have hNnorm := N.le_opNorm g
    by_contra! hzero
    linarith [mul_nonpos_of_nonpos_of_nonneg hzero (norm_nonneg g)]
  have hratio : R / ‖N‖ ≤ cauchyNormRatio p g * R := by
    unfold cauchyNormRatio
    change R / ‖N‖ ≤ ‖g‖ / ‖N g‖ * R
    have hmul := mul_le_mul_of_nonneg_right (N.le_opNorm g) hR
    field_simp
    nlinarith only [hmul]
  rw [min_comm (R / ‖N‖)]
  exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl hratio) (by positivity)).trans h

/-- **Lemma 15.4.3** of [conn2000trust]. Let $E$ be complete, $f : E \to \mathbb{R}$, $c : E \to F$,
$x, s \in E$, $H : E \to E$ continuous linear, $\sigma \ge 0$, $L_c \ge 0$ and $\|H\| \le B$.
Suppose that $\|s\| \le \xi \Delta$, that $f$ and $c$ are differentiable at $x + t s$ for
$t \in [0, 1]$, and that
$$\|\nabla f(x + t s) - \nabla f(x)\| \le L_f t \|s\|, \qquad \|J(x + t s) - J(x)\| \le L_c t
  \|s\| \qquad (t \in [0, 1]).$$
Let $\kappa = \max\{(L_f + B)/2, L_c/2\}$ and let $e = |\phi_\sigma(x + s) - m(s)|$, where $m$
is the overall model with $f_0 = f(x)$, $g = \nabla f(x)$, $c = c(x)$ and $A = J(x)$. Then
$$e \le \kappa (1 + \sigma) \|s\|^2 \quad \text{and} \quad e \le \xi^2 \kappa (1 + \sigma)
  \Delta^2.$$

**Correction.** The Taylor assumptions are imposed on the full trial segment, including trial
points that the algorithm may reject. Lipschitz bounds near the iterates do not control the
rejected trial segments; see `ConnGouldToint.Chapter15.sqp_trialSegment_counterexample`.

The gradient is Mathlib's `gradient f x`.

**Correction.** The Lipschitz derivative bounds must hold along the whole trial segment, rather than
just on the iterates. The statement gives explicit model-error constants from the segment bounds.
-/
theorem lemma_15_4_3 [CompleteSpace E] {f : E → ℝ} {c : E → F} {x s : E}
    (H : E →L[ℝ] E) {σ Δ ξ Lf Lc B : ℝ}
    (hσ : 0 ≤ σ) (hs : ‖s‖ ≤ ξ * Δ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f (x + t • s))
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ c (x + t • s))
    (hLf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ f (x + t • s) - fderiv ℝ f x‖ ≤ Lf * (t * ‖s‖))
    (hLc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ c (x + t • s) - fderiv ℝ c x‖ ≤ Lc * (t * ‖s‖))
    (hLc₀ : 0 ≤ Lc) (hH : ‖H‖ ≤ B) :
    let κ := max ((Lf + B) / 2) (Lc / 2)
    let err := |sqpMerit f c σ (x + s) -
      sqpOverallModel (f x) (gradient f x) H (c x) (fderiv ℝ c x) σ s|
    err ≤ κ * (1 + σ) * ‖s‖ ^ 2 ∧ err ≤ ξ ^ 2 * κ * (1 + σ) * Δ ^ 2 := by
  let κ := max ((Lf + B) / 2) (Lc / 2)
  have hκ : 0 ≤ κ := (by linarith : 0 ≤ Lc / 2).trans (le_max_right _ _)
  have hF := norm_sub_firstOrder_le_of_lipschitz_on_segment hf hLf
  have hC := norm_sub_firstOrder_le_of_lipschitz_on_segment hc hLc
  have hh : |⟪s, H s⟫| ≤ B * ‖s‖ ^ 2 := calc
    _ ≤ ‖s‖ * ‖H s‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖s‖ * (‖H‖ * ‖s‖) := mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _)
    _ = ‖H‖ * ‖s‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hH (sq_nonneg _)
  have hobj : |f (x + s) - quadraticModel (f x) (gradient f x) H.toLinearMap s| ≤
      ((Lf + B) / 2) * ‖s‖ ^ 2 := by
    rw [Real.norm_eq_abs] at hF
    simp only [quadraticModel, ContinuousLinearMap.coe_coe, inner_gradient_left]
    rw [← sub_sub]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith only [hF, hh]
  have hcon : |‖c (x + s)‖ - sqpNormalModel (c x) (fderiv ℝ c x) s| ≤
      Lc / 2 * ‖s‖ ^ 2 := by
    unfold sqpNormalModel
    exact (abs_norm_sub_norm_le _ _).trans (by convert hC using 1; ring)
  have herr : |sqpMerit f c σ (x + s) -
      sqpOverallModel (f x) (gradient f x) H (c x) (fderiv ℝ c x) σ s| ≤
      κ * (1 + σ) * ‖s‖ ^ 2 := by
    unfold sqpMerit sqpOverallModel
    rw [show f (x + s) + σ * ‖c (x + s)‖ -
        (quadraticModel (f x) (gradient f x) H.toLinearMap s +
          σ * sqpNormalModel (c x) (fderiv ℝ c x) s) =
        (f (x + s) - quadraticModel (f x) (gradient f x) H.toLinearMap s) +
          σ * (‖c (x + s)‖ - sqpNormalModel (c x) (fderiv ℝ c x) s) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hσ]
    have h₁ := hobj.trans
      (mul_le_mul_of_nonneg_right (le_max_left ((Lf + B) / 2) (Lc / 2)) (sq_nonneg ‖s‖))
    have h₂ := hcon.trans
      (mul_le_mul_of_nonneg_right (le_max_right ((Lf + B) / 2) (Lc / 2)) (sq_nonneg ‖s‖))
    nlinarith only [h₁, mul_le_mul_of_nonneg_left h₂ hσ]
  refine ⟨herr, herr.trans ?_⟩
  calc
    _ ≤ κ * (1 + σ) * (ξ * Δ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs 2) (by positivity)
    _ = _ := by ring

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
private theorem sqp_acceptance_of_linear_decrease (f : E → ℝ) (c : E → F) (x : E)
    (s : ℝ → E) (m : ℝ → E → ℝ) (σ : ℝ → ℝ)
    {η C σmin : ℝ} (hη : η < 1) (hC : 0 ≤ C) (hmin : 0 < σmin)
    (hσ : ∀ r > 0, σmin ≤ σ r)
    (hcenter : ∀ r > 0, m r 0 = sqpMerit f c (σ r) x)
    (herr : ∀ r > 0, |sqpMerit f c (σ r) (x + s r) - m r (s r)| ≤
      C * (1 + σ r) * r ^ 2)
    (hdec : ∃ a > 0, ∃ b > 0, ∀ r ∈ Set.Ioc (0 : ℝ) b,
      a * (1 + σ r) * r ≤ m r 0 - m r (s r)) :
    ∃ r₀ > 0, ∀ r ∈ Set.Ioc (0 : ℝ) r₀,
      η ≤ Optimization.reductionRatio (sqpMerit f c (σ r)) x (s r) (m r 0 - m r (s r)) := by
  obtain ⟨a, ha, b, hb, hlin⟩ := hdec
  let r₀ := min b ((1 - η) * a / (C + 1))
  refine ⟨r₀, lt_min hb (by positivity), ?_⟩
  intro r hr
  have hrb : r ∈ Set.Ioc (0 : ℝ) b := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hd := hlin r hrb
  have hp : 0 < m r 0 - m r (s r) :=
    (mul_pos (mul_pos ha (by linarith [hσ r hr.1])) hr.1).trans_le hd
  have hsmall := (le_div_iff₀ (by positivity : 0 < C + 1)).mp
    (hr.2.trans (min_le_right _ _))
  have hcr : C * r ≤ (1 - η) * a := by
    linarith only [hsmall, hr.1]
  have hσ' : 0 ≤ 1 + σ r := by linarith [hσ r hr.1]
  have he : |sqpMerit f c (σ r) (x + s r) -
      (sqpMerit f c (σ r) x - (m r 0 - m r (s r)))| ≤
      (1 - η) * (m r 0 - m r (s r)) := by
    rw [← hcenter r hr.1, sub_sub_cancel]
    refine (herr r hr.1).trans ?_
    have hscale := mul_le_mul_of_nonneg_right hcr (mul_nonneg hσ' hr.1.le)
    have hpred := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hη.le)
    nlinarith only [hscale, hpred]
  have h := Optimization.le_reductionRatio_of_abs_sub_le hp he
  linarith only [h]

private theorem sqp_linear_decrease {σ d : ℝ → ℝ} {σmin : ℝ}
    (hmin : 0 < σmin) (hσ : ∀ r > 0, σmin ≤ σ r)
    (hcase :
      (∃ G R β ξ κ S : ℝ,
        0 < G ∧ 0 < R ∧ 0 < β ∧ 0 < ξ ∧ 0 < κ ∧ 0 ≤ S ∧
        ∀ r > 0, σ r ≤ S ∧ κ * G * min (ξ * r / R) (G / β) ≤ d r) ∨
      (∃ T ν b : ℝ, 0 < T ∧ 0 < ν ∧ 0 < b ∧
        ∀ r > 0, ν * σ r * min T (b * r) ≤ d r)) :
    ∃ a > 0, ∃ b > 0, ∀ r ∈ Set.Ioc (0 : ℝ) b, a * (1 + σ r) * r ≤ d r := by
  rcases hcase with ⟨G, R, β, ξ, κ, S, hG, hR, hβ, hξ, hκ, hS, hdec⟩ |
    ⟨T, ν, b, hT, hν, hb, hdec⟩
  · let a := κ * G * ξ / (R * (1 + S))
    let b := (G / β) * R / ξ
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    refine ⟨a, ha, b, hb, fun r hr => ?_⟩
    obtain ⟨hS', hdrop⟩ := hdec r hr.1
    have hm : ξ * r / R ≤ G / β := by
      apply (div_le_iff₀ hR).mpr
      have hh := (le_div_iff₀ hξ).mp (show r ≤ (G / β) * R / ξ from hr.2)
      rwa [mul_comm ξ r]
    rw [min_eq_left hm] at hdrop
    calc
      _ ≤ a * (1 + S) * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha.le) hr.1.le
      _ = κ * G * (ξ * r / R) := by
        dsimp [a]
        field_simp
      _ ≤ _ := hdrop
  · let a := ν * b * (σmin / (1 + σmin))
    refine ⟨a, by dsimp [a]; positivity, T / b,
      div_pos hT hb, fun r hr => ?_⟩
    have hm : b * r ≤ T := by
      rw [mul_comm]
      exact (le_div_iff₀ hb).mp hr.2
    have hσr := hσ r hr.1
    have hfrac : σmin / (1 + σmin) * (1 + σ r) ≤ σ r := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 1 + σmin)).mpr
      linarith only [hσr]
    have hdrop := hdec r hr.1
    rw [min_eq_right hm] at hdrop
    calc
      _ = (ν * b * r) * (σmin / (1 + σmin) * (1 + σ r)) := by dsimp [a]; ring
      _ ≤ (ν * b * r) * σ r :=
        mul_le_mul_of_nonneg_left hfrac (by positivity [hr.1])
      _ = ν * σ r * (b * r) := by ring
      _ ≤ _ := hdrop

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- **Lemma 15.4.4** of [conn2000trust]. Fix an iterate $x$, and for each radius $r > 0$ let $s_r$
be the step, $m_r$ the overall model and $\sigma_r \ge \sigma_{\min} > 0$ the penalty. Let
$\eta < 1$ and $C \ge 0$, and suppose that $m_r(0) = \phi_{\sigma_r}(x)$ and
$$|\phi_{\sigma_r}(x + s_r) - m_r(s_r)| \le C (1 + \sigma_r) r^2 \quad \text{for all } r > 0.$$
Suppose also one of the two cases:

* $c(x) = 0$, and there are $G, R, \beta, \xi, \kappa > 0$ and $S \ge 0$ with $\sigma_r \le S$
  and $\kappa G \min\{\xi r / R, G / \beta\} \le m_r(0) - m_r(s_r)$ for all $r > 0$;
* $c(x) \neq 0$, and there are $\nu, b > 0$ with $\nu \sigma_r \min\{\|c(x)\|, b r\} \le
  m_r(0) - m_r(s_r)$ for all $r > 0$.

Then there is $r_0 > 0$ such that the ratio satisfies $\rho \ge \eta$ for all $r \in (0, r_0]$.

In the feasible case the reduced gradient is nonzero and the penalty is bounded. The infeasible
case uses the penalty-weighted normal decrease, so the penalty need not be bounded above.

**Reading.** The small-radius acceptance argument uses an explicit uniform model-error bound for the
trial segment and lower bounds on predicted decrease for the two cases. The Byrd–Omojokun version
uses normal criticality where the first variant uses feasibility.
-/
theorem lemma_15_4_4 (f : E → ℝ) (c : E → F) (x : E)
    (s : ℝ → E) (m : ℝ → E → ℝ) (σ : ℝ → ℝ)
    {η C σmin : ℝ} (hη : η < 1) (hC : 0 ≤ C) (hmin : 0 < σmin)
    (hσ : ∀ r > 0, σmin ≤ σ r)
    (hcenter : ∀ r > 0, m r 0 = sqpMerit f c (σ r) x)
    (herr : ∀ r > 0, |sqpMerit f c (σ r) (x + s r) - m r (s r)| ≤
      C * (1 + σ r) * r ^ 2)
    (hcase :
      (c x = 0 ∧ ∃ G R β ξ κ S : ℝ,
        0 < G ∧ 0 < R ∧ 0 < β ∧ 0 < ξ ∧ 0 < κ ∧ 0 ≤ S ∧
        ∀ r > 0, σ r ≤ S ∧ κ * G * min (ξ * r / R) (G / β) ≤ m r 0 - m r (s r)) ∨
      (c x ≠ 0 ∧ ∃ ν b : ℝ, 0 < ν ∧ 0 < b ∧
        ∀ r > 0, ν * σ r * min ‖c x‖ (b * r) ≤ m r 0 - m r (s r))) :
    ∃ r₀ > 0, ∀ r ∈ Set.Ioc (0 : ℝ) r₀,
      η ≤ Optimization.reductionRatio (sqpMerit f c (σ r)) x (s r) (m r 0 - m r (s r)) := by
  apply sqp_acceptance_of_linear_decrease f c x s m σ hη hC hmin hσ hcenter herr
  apply sqp_linear_decrease hmin hσ
  rcases hcase with ⟨_, h⟩ | ⟨hc, ν, b, hν, hb, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨‖c x‖, ν, b, norm_pos_iff.mpr hc, hν, hb, h⟩

/-- **Section 15.4.1.4** of [conn2000trust]. For a lower bound $f_{\min}$ of the objective and
$\sigma \in \mathbb{R}$, the **normalized merit function** is
$(\phi_\sigma(x) - f_{\min}) / \sigma$.

**Reading.** The descent comparison is indexed directly by successive accepted states and a positive
nondecreasing penalty weight. The normalization allows a total quotient outside the domain used by
the lemma.
-/
noncomputable def sqpNormalizedMerit (f : E → ℝ) (c : E → F) (fmin σ : ℝ) (x : E) : ℝ :=
  (sqpMerit f c σ x - fmin) / σ

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- **Lemma 15.4.5** of [conn2000trust], on the subsequence of successful iterates. Let $x_i$ be the
successful iterates with $f(x_i) \ge f_{\min}$, let $\sigma_i > 0$ be nondecreasing,
$\eta \ge 0$ and $\delta_i \ge 0$, and suppose that
$$\eta \delta_i \le \phi_{\sigma_i}(x_i) - \phi_{\sigma_i}(x_{i+1}) \quad \text{for all } i.$$
Then the normalized merit values $\psi_i = (\phi_{\sigma_i}(x_i) - f_{\min}) / \sigma_i$ are
nonnegative, and $\psi_{i+j} \le \psi_i - \eta \delta_i / \sigma_i$ for all $i$ and $j > 0$.

**Reading.** Rejected iterations leave the iterate unchanged, so the lemma is stated on the
subsequence of successful iterates. The reduction condition compares consecutive points of this
subsequence at the old penalty.

**Reading.** The descent comparison is indexed directly by successive accepted states and a positive
nondecreasing penalty weight. The normalization allows a total quotient outside the domain used by
the lemma.
-/
theorem lemma_15_4_5 (f : E → ℝ) (c : E → F) (x : ℕ → E) (σ d : ℕ → ℝ)
    {fmin η : ℝ} (hf : ∀ i, fmin ≤ f (x i)) (hσ : ∀ i, 0 < σ i) (hmono : Monotone σ)
    (hη : 0 ≤ η) (hd : ∀ i, 0 ≤ d i)
    (haccept : ∀ i, η * d i ≤ sqpMerit f c (σ i) (x i) - sqpMerit f c (σ i) (x (i + 1))) :
    (∀ i, 0 ≤ sqpNormalizedMerit f c fmin (σ i) (x i)) ∧
    ∀ i j : ℕ, 0 < j →
      sqpNormalizedMerit f c fmin (σ (i + j)) (x (i + j)) ≤
        sqpNormalizedMerit f c fmin (σ i) (x i) - η * (d i / σ i) := by
  let v (i : ℕ) := sqpNormalizedMerit f c fmin (σ i) (x i)
  have hexpand (s : ℝ) (hs : s ≠ 0) (z : E) :
      sqpNormalizedMerit f c fmin s z = (f z - fmin) / s + ‖c z‖ := by
    unfold sqpNormalizedMerit sqpMerit
    field_simp
    ring
  have hstep (i : ℕ) : v (i + 1) ≤ v i - η * (d i / σ i) := by
    calc
      _ ≤ sqpNormalizedMerit f c fmin (σ i) (x (i + 1)) := by
        simp only [v, hexpand _ (hσ _).ne']
        exact add_le_add (div_le_div_of_nonneg_left (sub_nonneg.mpr (hf _))
          (hσ i) (hmono (Nat.le_succ i))) le_rfl
      _ ≤ _ := by
        dsimp [v, sqpNormalizedMerit]
        rw [← mul_div_assoc, ← sub_div]
        apply (div_le_div_iff_of_pos_right (hσ i)).mpr
        linarith only [haccept i]
  have hanti : Antitone v := antitone_nat_of_succ_le
    (fun i => (hstep i).trans (sub_le_self _ (mul_nonneg hη (div_nonneg (hd i) (hσ i).le))))
  refine ⟨fun i => ?_, fun i j hj => ?_⟩
  · rw [hexpand _ (hσ i).ne']
    exact add_nonneg (div_nonneg (sub_nonneg.mpr (hf i)) (hσ i).le) (norm_nonneg _)
  · exact (hanti (Nat.add_le_add_left hj i)).trans (hstep i)


/-- **Equations (15.4.45) and (15.4.127)** of [conn2000trust]. For a measure $u : E \to \mathbb{R}$,
a point $x$ and $\gamma \in \mathbb{R}$, the **criticality neighborhood** is the open ball
$B(x, u(x) / (2\gamma))$. It keeps the residual norm (15.4.45) or the normal criticality measure
(15.4.127) bounded away from zero.

**Generalization.** A common scalar neighborhood and Lipschitz estimate are used for the residual
norm and the normal criticality measure.
-/
noncomputable def sqpCriticalityNeighborhood (u : E → ℝ) (x : E) (γ : ℝ) : Set E :=
  Metric.ball x (u x / (2 * γ))

omit [InnerProductSpace ℝ E] in
/-- **Equations (15.4.44)–(15.4.47) and (15.4.126)–(15.4.128)** of [conn2000trust]. Let
$\gamma > 0$, and let $|u(y) - u(x)| \le \gamma \operatorname{dist}(y, x)$. If $y$ lies in the
criticality neighborhood of $x$, then
$$\tfrac{1}{2} u(x) < u(y) < \tfrac{3}{2} u(x).$$

**Generalization.** A common scalar neighborhood and Lipschitz estimate are used for the residual
norm and the normal criticality measure.
-/
theorem sqpCriticalityNeighborhood_bounds {u : E → ℝ} {x y : E} {γ : ℝ}
    (hγ : 0 < γ) (hLip : |u y - u x| ≤ γ * dist y x)
    (hy : y ∈ sqpCriticalityNeighborhood u x γ) :
    u x / 2 < u y ∧ u y < 3 * u x / 2 := by
  have hd : dist y x < u x / (2 * γ) := hy
  have h := (lt_div_iff₀ (show 0 < 2 * γ by positivity)).mp hd
  have hh := abs_le.mp hLip
  constructor <;> linarith

/-- **Equation (15.4.50)** of [conn2000trust], corrected. The **radius floor** is
$\gamma \min\{\Delta_N, r\}$, where $\Delta_N$ is the radius at entry to the criticality
neighborhood and $r$ is the threshold below which the radius does not decrease.

**Correction.** The floor includes the radius at entry, which can be smaller than the threshold
term.

**Correction.** The floor includes a minimum with the radius on entry to the neighborhood, because
the very-successful small-radius branch only promises nondecrease there.
-/
def sqpNeighborhoodRadiusFloor (γ entry threshold : ℝ) : ℝ :=
  γ * min entry threshold

private theorem sqp_radius_floor {Δ : ℕ → ℝ} {γ r : ℝ} {N : ℕ}
    (hγ : 0 ≤ γ) (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hsmall : ∀ k ≥ N, Δ k ≤ r → Δ k ≤ Δ (k + 1)) :
    ∀ k ≥ N, min (Δ N) (γ * r) ≤ Δ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact min_le_left _ _
  | succ k hk ih =>
    by_cases h : Δ k ≤ r
    · exact ih.trans (hsmall k hk h)
    · exact (min_le_right _ _).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_ge h) hγ).trans (hnext k))

/-- **Equation (15.4.50)** of [conn2000trust]. Let $\gamma \in [0, 1]$, $\Delta_N \ge 0$ and
$N \le k$. Suppose that $\gamma \Delta_j \le \Delta_{j+1}$ for all $j$, and that
$\Delta_j \le r$ implies $\Delta_j \le \Delta_{j+1}$ for all $j \ge N$. Then
$\gamma \min\{\Delta_N, r\} \le \Delta_k$.

**Correction.** The floor includes a minimum with the radius on entry to the neighborhood, because
the very-successful small-radius branch only promises nondecrease there.
-/
theorem sqpNeighborhoodRadiusFloor_le {Δ : ℕ → ℝ} {γ r : ℝ} {N k : ℕ}
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 0 ≤ Δ N) (hk : N ≤ k)
    (hnext : ∀ j, γ * Δ j ≤ Δ (j + 1))
    (hsmall : ∀ j ≥ N, Δ j ≤ r → Δ j ≤ Δ (j + 1)) :
    sqpNeighborhoodRadiusFloor γ (Δ N) r ≤ Δ k := by
  apply le_trans ?_ (sqp_radius_floor hγ.1 hnext hsmall k hk)
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hγ.1).trans
      (mul_le_of_le_one_left hN hγ.2)
  · exact mul_le_mul_of_nonneg_left (min_le_right _ _) hγ.1

/-- **Equation (15.4.71)** of [conn2000trust], corrected. The **tangential acceptance radius** is
$$\min\Bigl\{\frac{G}{\beta b}, \frac{(1 - \eta) \kappa G b}{C + 1}\Bigr\},$$
where $G$ is a lower bound for the reduced gradient, $\beta$ bounds the reduced curvature, $b$
converts the radius into the tangential radius in reduced coordinates, $\kappa$ includes the
fraction of the tangential Cauchy decrease required of the overall model, and $C$ bounds the
trial error coefficient.

**Correction.** The threshold includes the effective decrease coefficient $\kappa$ and the model
error coefficient $C$; see `ConnGouldToint.Chapter15.sqpTangentialAcceptanceRadius_ratio`.

**Correction.** The threshold accounts for both the size of the Cauchy-decrease regime and the
actual merit-model error coefficient. This ensures a positive prediction and the advertised ratio
bound.
-/
noncomputable def sqpTangentialAcceptanceRadius (G β b η κ C : ℝ) : ℝ :=
  min (G / (β * b)) ((1 - η) * κ * G * b / (C + 1))

/-- **Equation (15.4.71)** of [conn2000trust], acceptance estimate. Let $G, \beta, b, \kappa > 0$,
$\eta < 1$, $C \ge 0$ and $r > 0$, with $r$ at most the tangential acceptance radius. If the
predicted decrease satisfies $\kappa G \min\{b r, G / \beta\} \le \delta$ and the actual
decrease satisfies $|a - \delta| \le C r^2$, then $\eta \le a / \delta$.

**Correction.** The threshold accounts for both the size of the Cauchy-decrease regime and the
actual merit-model error coefficient. This ensures a positive prediction and the advertised ratio
bound.
-/
theorem sqpTangentialAcceptanceRadius_ratio {G β b η κ C r d actual : ℝ}
    (hG : 0 < G) (hβ : 0 < β) (hb : 0 < b) (hη : η < 1)
    (hκ : 0 < κ) (hC : 0 ≤ C) (hr : 0 < r)
    (hthreshold : r ≤ sqpTangentialAcceptanceRadius G β b η κ C)
    (hpred : κ * G * min (b * r) (G / β) ≤ d)
    (herr : |actual - d| ≤ C * r ^ 2) : η ≤ actual / d := by
  have hD : b * r ≤ G / β := by
    have hh := (le_div_iff₀ (mul_pos hβ hb)).mp (hthreshold.trans (min_le_left _ _))
    apply (le_div_iff₀ hβ).mpr
    nlinarith only [hh]
  rw [min_eq_left hD] at hpred
  have hpos : 0 < d := (mul_pos (mul_pos hκ hG) (mul_pos hb hr)).trans_le hpred
  have hCr : C * r ≤ (1 - η) * κ * G * b := by
    have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp
      (hthreshold.trans (min_le_right _ _))
    linarith only [hh, hr]
  have h₁ := mul_le_mul_of_nonneg_right hCr hr.le
  have h₂ := mul_le_mul_of_nonneg_left hpred (sub_nonneg.mpr hη.le)
  have he : |actual - d| ≤ (1 - η) * d := herr.trans (by nlinarith only [h₁, h₂])
  exact (le_div_iff₀ hpos).mpr (by linarith only [(abs_le.mp he).1])

/-- **Equation (15.4.131)** of [conn2000trust]. For an upper bound $B$ on the Jacobian norms along
the iterates, the **normal curvature bound** is $1 + B^2$.

**Reading.** The bound uses a uniform bound $B$ on the Jacobian norms and does not require that
a maximum is attained.

**Generalization.** A uniform bound on the Jacobian norms gives a valid bound on one plus the normal
curvature, without requiring that the largest Jacobian norm be attained.
-/
def sqpNormalCurvatureBound (B : ℝ) : ℝ := 1 + B ^ 2

/-- **Equation (15.4.131)** of [conn2000trust]. Let $X$ and $Y$ be real Hilbert spaces and
$A : X \to Y$ continuous linear with $\|A\| \le B$. Then $1 + \|A^* A\| \le 1 + B^2$.

**Generalization.** A uniform bound on the Jacobian norms gives a valid bound on one plus the normal
curvature, without requiring that the largest Jacobian norm be attained.
-/
theorem sqpNormalCurvatureBound_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) {B : ℝ} (hB : ‖A‖ ≤ B) :
    quadraticCurvatureBound (A.adjoint.comp A) ≤ sqpNormalCurvatureBound B := by
  rw [quadraticCurvatureBound, sqpNormalCurvatureBound,
    ContinuousLinearMap.norm_adjoint_comp_self]
  simpa only [pow_two] using add_le_add (le_refl (1 : ℝ)) (pow_le_pow_left₀ (norm_nonneg _) hB 2)

private theorem sqp_capped_drop_sum {v r : ℕ → ℝ} {a b T : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T) (hr : ∀ k, 0 ≤ r k)
    (n : ℕ) (hdrop : ∀ k < n, a * min T (b * r k) ≤ v k - v (k + 1)) :
    a * min T (b * ∑ k ∈ Finset.range n, r k) ≤ v 0 - v n := by
  induction n with
  | zero => simp [min_eq_right hT]
  | succ n ih =>
    have h₁ := ih (fun k hk ↦ hdrop k (hk.trans (Nat.lt_succ_self n)))
    have h₂ := hdrop n (Nat.lt_succ_self n)
    let u := b * ∑ k ∈ Finset.range n, r k
    let w := b * r n
    have hu : 0 ≤ u := mul_nonneg hb (Finset.sum_nonneg fun k _ ↦ hr k)
    have hw : 0 ≤ w := mul_nonneg hb (hr n)
    have hmin : min T (u + w) ≤ min T u + min T w := by
      rcases le_or_gt T u with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min hT hw))
      rcases le_or_gt T w with h' | h'
      · rw [min_eq_left h']
        exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min hT hu))
      · rw [min_eq_right h.le, min_eq_right h'.le]
        exact min_le_right _ _
    rw [Finset.sum_range_succ, mul_add]
    have hh := mul_le_mul_of_nonneg_left hmin ha
    change a * min T (u + w) ≤ _
    rw [mul_add] at hh
    linarith only [hh, h₁, h₂]

/-- **Equation (15.4.57)** of [conn2000trust], corrected. The **feasibility exit coefficient** is
$$\frac{\eta \nu}{2} \min\Bigl\{1, \frac{b}{\gamma \xi}\Bigr\}.$$

**Correction.** The source takes the maximum of the bounds of the two exit cases. A common lower
bound needs the minimum; see `ConnGouldToint.Chapter15.sqp_exit_max_counterexamples`.

**Correction.** Combining the two exit cases gives a minimum of the coefficients. A one-step
construction satisfies the decrease and displacement assumptions yet violates the printed maximum in
each formula.
-/
noncomputable def sqpFeasibilityExitCoeff (η ν b γ ξ : ℝ) : ℝ :=
  η * ν / 2 * min 1 (b / (γ * ξ))

/-- **Equation (15.4.57)** of [conn2000trust]. Let $\eta, \nu, b, u \ge 0$, $\gamma, \xi > 0$ and
$r_k \ge 0$. Suppose that the accepted steps leave the neighborhood (15.4.45),
$u / (2\gamma) \le \xi \sum_{k < n} r_k$, and that $\eta \nu \min\{u / 2, b r_k\} \le v_k -
v_{k+1}$ for $k < n$. Then the accumulated merit decrease satisfies
$$\frac{\eta \nu}{2} \min\Bigl\{1, \frac{b}{\gamma \xi}\Bigr\} u \le v_0 - v_n.$$

**Correction.** Combining the two exit cases gives a minimum of the coefficients. A one-step
construction satisfies the decrease and displacement assumptions yet violates the printed maximum in
each formula.
-/
theorem sqpFeasibilityExitCoeff_bound {v r : ℕ → ℝ} {η ν b γ ξ u : ℝ}
    (hη : 0 ≤ η) (hν : 0 ≤ ν) (hb : 0 ≤ b) (_hγ : 0 < γ) (hξ : 0 < ξ)
    (hu : 0 ≤ u) (hr : ∀ k, 0 ≤ r k) (n : ℕ)
    (hexit : u / (2 * γ) ≤ ξ * ∑ k ∈ Finset.range n, r k)
    (hdrop : ∀ k < n, η * ν * min (u / 2) (b * r k) ≤ v k - v (k + 1)) :
    sqpFeasibilityExitCoeff η ν b γ ξ * u ≤ v 0 - v n := by
  have hR : u / (2 * (γ * ξ)) ≤ ∑ k ∈ Finset.range n, r k := by
    rw [← mul_assoc, ← div_div]
    exact (div_le_iff₀ hξ).mpr (by simpa only [mul_comm] using hexit)
  have hmin := min_le_min_left (u / 2) (mul_le_mul_of_nonneg_left hR hb)
  have hd := (mul_le_mul_of_nonneg_left hmin (mul_nonneg hη hν)).trans
    (sqp_capped_drop_sum (mul_nonneg hη hν) hb (by positivity) hr n hdrop)
  calc
    _ = η * ν * ((u / 2) * min 1 (b / (γ * ξ))) := by
      unfold sqpFeasibilityExitCoeff
      ring
    _ = η * ν * min (u / 2) (b * (u / (2 * (γ * ξ)))) := by
      rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ u / 2), mul_one]
      congr 2
      ring
    _ ≤ _ := hd

/-- **Equation (15.4.140)** of [conn2000trust], corrected. The **normal criticality exit
coefficient** is
$$\frac{\eta \kappa \nu}{4 c_{\max}} \min\Bigl\{\frac{1}{\beta}, \frac{b}{\gamma \xi}\Bigr\}.$$

**Correction.** The source takes the maximum of the bounds of the two exit cases. A common lower
bound needs the minimum; see `ConnGouldToint.Chapter15.sqp_exit_max_counterexamples`.

**Correction.** Combining the two exit cases gives a minimum of the coefficients. A one-step
construction satisfies the decrease and displacement assumptions yet violates the printed maximum in
each formula.
-/
noncomputable def sqpNormalCriticalityExitCoeff (η κ ν cmax β b γ ξ : ℝ) : ℝ :=
  η * κ * ν / (4 * cmax) * min (1 / β) (b / (γ * ξ))

/-- **Equation (15.4.140)** of [conn2000trust]. Let $\eta, \kappa, \nu, b, u \ge 0$,
$c_{\max}, \beta, \gamma, \xi > 0$ and $r_k \ge 0$. Suppose that the accepted steps leave the
neighborhood (15.4.127), $u / (2\gamma) \le \xi \sum_{k < n} r_k$, and that
$$\frac{\eta \kappa \nu u}{2 c_{\max}} \min\Bigl\{\frac{u}{2 \beta}, b r_k\Bigr\} \le v_k -
  v_{k+1} \quad (k < n).$$
Then the normal criticality exit coefficient times $u^2$ is at most $v_0 - v_n$.

**Correction.** Combining the two exit cases gives a minimum of the coefficients. A one-step
construction satisfies the decrease and displacement assumptions yet violates the printed maximum in
each formula.
-/
theorem sqpNormalCriticalityExitCoeff_bound {v r : ℕ → ℝ}
    {η κ ν cmax β b γ ξ u : ℝ}
    (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (hcmax : 0 < cmax) (hβ : 0 < β)
    (hb : 0 ≤ b) (_hγ : 0 < γ) (hξ : 0 < ξ)
    (hu : 0 ≤ u) (hr : ∀ k, 0 ≤ r k) (n : ℕ)
    (hexit : u / (2 * γ) ≤ ξ * ∑ k ∈ Finset.range n, r k)
    (hdrop : ∀ k < n, (η * κ * ν * u / (2 * cmax)) * min (u / (2 * β)) (b * r k) ≤
      v k - v (k + 1)) :
    sqpNormalCriticalityExitCoeff η κ ν cmax β b γ ξ * u ^ 2 ≤ v 0 - v n := by
  let a := η * κ * ν * u / (2 * cmax)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hR : u / (2 * (γ * ξ)) ≤ ∑ k ∈ Finset.range n, r k := by
    rw [← mul_assoc, ← div_div]
    exact (div_le_iff₀ hξ).mpr (by simpa only [mul_comm] using hexit)
  have hmin := min_le_min_left (u / (2 * β)) (mul_le_mul_of_nonneg_left hR hb)
  have hd := (mul_le_mul_of_nonneg_left hmin ha).trans
    (sqp_capped_drop_sum ha hb (by positivity) hr n hdrop)
  calc
    _ = a * ((u / 2) * min (1 / β) (b / (γ * ξ))) := by
      unfold sqpNormalCriticalityExitCoeff a
      ring
    _ = a * min (u / (2 * β)) (b * (u / (2 * (γ * ξ)))) := by
      rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ u / 2)]
      congr 2 <;> ring
    _ ≤ _ := hd

/-- The maxima in (15.4.57) and (15.4.140) of [conn2000trust] can exceed the total merit decrease
that the accepted-step estimates and the exit distance permit. Take one step, $r_0 = 1$, with
both the acceptance and the normal fractions equal to $1/2$, and the merit values $v = (1/8, 0)$
and $w = (1/16, 0)$. The exit condition $1/2 \le r_0$ and the step estimates
$\frac{1}{4} \min\{1/2, 2 r_0\} \le v_0 - v_1$ and
$\frac{1}{8} \min\{1/2, 2 r_0\} \le w_0 - w_1$ hold, but
$$v_0 - v_1 < \tfrac{1}{8} \max\{1, 2\}, \qquad w_0 - w_1 < \tfrac{1}{16} \max\{1, 2\}.$$

**Correction.** Combining the two exit cases gives a minimum of the coefficients. A one-step
construction satisfies the decrease and displacement assumptions yet violates the printed maximum in
each formula.
-/
theorem sqp_exit_max_counterexamples :
    let r : ℕ → ℝ := fun _ ↦ 1
    let v : ℕ → ℝ := fun k ↦ if k = 0 then 1 / 8 else 0
    let w : ℕ → ℝ := fun k ↦ if k = 0 then 1 / 16 else 0
    (1 / 2 : ℝ) ≤ ∑ k ∈ Finset.range 1, r k ∧
      (∀ k < 1, (1 / 4 : ℝ) * min (1 / 2) (2 * r k) ≤ v k - v (k + 1)) ∧
      (∀ k < 1, (1 / 8 : ℝ) * min (1 / 2) (2 * r k) ≤ w k - w (k + 1)) ∧
      v 0 - v 1 < (1 / 8 : ℝ) * max 1 2 ∧
      w 0 - w 1 < (1 / 16 : ℝ) * max 1 2 := by
  intro r v w
  refine ⟨by norm_num [r], ?_, ?_, by norm_num [v, max_def], by norm_num [w, max_def]⟩
  · intro k hk
    have hk' : k = 0 := by omega
    norm_num [hk', r, v, min_def]
  · intro k hk
    have hk' : k = 0 := by omega
    norm_num [hk', r, w, min_def]

private def HasRelaxedProgress (u v Δ : ℕ → ℝ) (S : Set ℕ) : Prop :=
  ∀ ε > 0, ∃ (a b e r : ℝ) (K : ℕ), 0 < a ∧ 0 < b ∧ 0 < e ∧ 0 < r ∧
    ∀ k ≥ K, ε ≤ u k →
      (Δ k ≤ r → k ∈ S ∧ Δ k ≤ Δ (k + 1)) ∧
      (k ∈ S → a * min e (b * Δ k) ≤ v k - v (k + 1))

private theorem relaxed_progress_frequently_small {u v Δ : ℕ → ℝ} {S : Set ℕ}
    {γ γ₂ : ℝ} (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hv : ∀ k, 0 ≤ v k) (hΔ : ∀ k, 0 < Δ k)
    (hmono : Antitone v) (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, Δ (k + 1) ≤ γ₂ * Δ k)
    (hcontrol : HasRelaxedProgress u v Δ S) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ k ≥ N₀, u k < ε := by
  have hbdd : BddBelow (Set.range v) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hv k⟩
  have hlim := tendsto_atTop_ciInf hmono hbdd
  have hdiff : Filter.Tendsto (fun k => v k - v (k + 1)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, sub_self] using
      hlim.sub (hlim.comp (Filter.tendsto_add_atTop_nat 1))
  by_contra! hfail
  obtain ⟨a, b, e, r, K, ha, hb, he, hr, hcontrol⟩ := hcontrol ε hε
  let N := max K N₀
  let d := min (Δ N) (γ * r)
  have hd : 0 < d := lt_min (hΔ N) (mul_pos hγ hr)
  have hfloor : ∀ k ≥ N, d ≤ Δ k :=
    sqp_radius_floor hγ.le hnext (fun k hk h ↦ ((hcontrol k ((le_max_left _ _).trans hk)
      (hfail k ((le_max_right _ _).trans hk))).1 h).2)
  have hpos : 0 < a * min e (b * d) := mul_pos ha (lt_min he (mul_pos hb hd))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hpos))
  let M := max J N
  have hstop (k : ℕ) (hk : M ≤ k) : k ∉ S := by
    intro h
    have hkN := (le_max_right _ _).trans hk
    have hlow : a * min e (b * d) ≤ a * min e (b * Δ k) := mul_le_mul_of_nonneg_left
      (min_le_min le_rfl (mul_le_mul_of_nonneg_left (hfloor k hkN) hb.le)) ha.le
    exact (not_le_of_gt (hJ k ((le_max_left _ _).trans hk)))
      (hlow.trans ((hcontrol k ((le_max_left _ _).trans hkN)
        (hfail k ((le_max_right _ _).trans hkN))).2 h))
  have hpow (j : ℕ) : Δ (M + j) ≤ γ₂ ^ j * Δ M := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hmj : M ≤ M + j := Nat.le_add_right _ _
      change Δ (M + j + 1) ≤ γ₂ ^ (j + 1) * Δ M
      rw [pow_succ', mul_assoc]
      exact (hrej (M + j) (hstop _ hmj)).trans
        (mul_le_mul_of_nonneg_left ih hγ₂)
  have hzero : Filter.Tendsto (fun j => γ₂ ^ j * Δ M) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ₂ hγ₂').mul_const (Δ M)
  obtain ⟨j, hj⟩ := (hzero.eventually (gt_mem_nhds hd)).exists
  have hm : N ≤ M + j := (le_max_right J N).trans (Nat.le_add_right _ _)
  exact (not_le_of_gt hj) ((hfloor _ hm).trans (hpow j))

private theorem tendsto_zero_of_relaxed_steps {u v Δ : ℕ → ℝ} {S : Set ℕ}
    {γ γ₂ : ℝ}
    (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (hΔ : ∀ k, 0 < Δ k)
    (hmono : Antitone v) (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, Δ (k + 1) ≤ γ₂ * Δ k ∧ u (k + 1) = u k)
    (hmove : ∀ ε > 0, ∃ L ≥ 0, ∃ M : ℕ, ∀ k ≥ M, ε ≤ u k → k ∈ S →
      u k - u (k + 1) ≤ L * Δ k)
    (hcontrol : HasRelaxedProgress u v Δ S) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  have hbdd : BddBelow (Set.range v) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hv k⟩
  have hlim := tendsto_atTop_ciInf hmono hbdd
  have hdiff : Filter.Tendsto (fun k => v k - v (k + 1)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, sub_self] using
      hlim.sub (hlim.comp (Filter.tendsto_add_atTop_nat 1))
  have htail : Filter.Tendsto (fun k => v k - ⨅ j, v j) Filter.atTop (nhds 0) := by
    simpa using hlim.sub_const (⨅ j, v j)
  have hfreq := relaxed_progress_frequently_small hγ hγ₂ hγ₂' hv hΔ hmono hnext
    (fun k hk => (hrej k hk).1) hcontrol
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  obtain ⟨a, b, e₀, r, K, ha, hb, he₀, hr, hc⟩ := hcontrol e he
  obtain ⟨L, hL, M, hM⟩ := hmove e he
  let C := L / (a * b)
  have hC : 0 ≤ C := div_nonneg hL (mul_nonneg ha.le hb.le)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hdiff.eventually (gt_mem_nhds (mul_pos ha he₀)))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp
    (htail.eventually (gt_mem_nhds (div_pos he (by positivity : 0 < C + 1))))
  have hlocal (k : ℕ) (hk : max N (max K M) ≤ k) (hhigh : e ≤ u k) :
      u k - u (k + 1) ≤ C * (v k - v (k + 1)) := by
    by_cases hs : k ∈ S
    · have hdrop := (hc k ((le_max_left _ _).trans ((le_max_right _ _).trans hk)) hhigh).2 hs
      have hΔe : b * Δ k < e₀ := by
        by_contra! hh
        have hh' := mul_le_mul_of_nonneg_left (le_min le_rfl hh) ha.le
        exact (not_le_of_gt (hN k ((le_max_left _ _).trans hk))) (hh'.trans hdrop)
      rw [min_eq_right hΔe.le] at hdrop
      refine (hM k ((le_max_right _ _).trans ((le_max_right _ _).trans hk)) hhigh hs).trans ?_
      have h := mul_le_mul_of_nonneg_left hdrop hC
      have hid : C * (a * (b * Δ k)) = L * Δ k := by
        dsimp [C]
        field_simp
      rwa [hid] at h
    · rw [(hrej k hs).2, sub_self]
      exact mul_nonneg hC (sub_nonneg.mpr (hmono (Nat.le_succ k)))
  refine ⟨max (max N (max K M)) J, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu k)]
  by_contra! hhigh
  let j := Nat.find (hfreq e he k)
  have hj : k ≤ j ∧ u j < e := Nat.find_spec (hfreq e he k)
  have htel (i : ℕ) (hi : k ≤ i) : i ≤ j → u k - u i ≤ C * (v k - v i) := by
    induction i, hi using Nat.le_induction with
    | base => simp
    | succ i hi ih =>
      intro hij
      have hlt : i < j := Nat.lt_of_succ_le hij
      have hhi : e ≤ u i := le_of_not_gt fun h => Nat.find_min (hfreq e he k) hlt ⟨hi, h⟩
      linarith only [ih hlt.le, hlocal i (((le_max_left _ _).trans hk).trans hi) hhi]
  have hlow : e < u k - u j := by dsimp [e] at hj ⊢; linarith [hj.2]
  have hupper : C * (v k - v j) < e := calc
    _ ≤ (C + 1) * (v k - v j) :=
      mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr (hmono hj.1))
    _ ≤ (C + 1) * (v k - ⨅ i, v i) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left (ciInf_le hbdd j) _) (by positivity)
    _ < _ := by
      rw [mul_comm]
      exact (lt_div_iff₀ (by positivity : 0 < C + 1)).mp (hJ k ((le_max_right _ _).trans hk))
  exact (not_lt_of_ge (htel j hj.1 le_rfl)) (hupper.trans hlow)

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
private theorem sqp_tendsto_zero_of_normal_decrease (f : E → ℝ) (c : E → F) (x s : ℕ → E)
    (σ d Δ u : ℕ → ℝ)
    (S : Set ℕ) {fmin σmin η η₂ C L γ γ₂ : ℝ}
    (hη : 0 < η) (hη₂' : η₂ < 1) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hσmin : 0 < σmin) (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hf : ∀ k, fmin ≤ f (x k)) (hσ : ∀ k, σmin ≤ σ k) (hσmono : Monotone σ)
    (hΔ : ∀ k, 0 < Δ k) (hu : ∀ k, 0 ≤ u k)
    (hd_nonneg : ∀ k, 0 ≤ d k)
    (hpred : ∀ ε > 0, ∃ p > 0, ∃ b > 0, ∃ e > 0, ∀ k, ε ≤ u k →
      p * (1 + σ k) * min e (b * Δ k) ≤ d k)
    (herr : ∀ k, |sqpMerit f c (σ k) (x k + s k) -
      (sqpMerit f c (σ k) (x k) - d k)| ≤ C * (1 + σ k) * (Δ k) ^ 2)
    (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hacc : ∀ k ∈ S, η * d k ≤ sqpMerit f c (σ k) (x k) -
      sqpMerit f c (σ k) (x (k + 1)))
    (hvery : ∀ k, η₂ ≤ Optimization.reductionRatio
      (sqpMerit f c (σ k)) (x k) (s k) (d k) → k ∈ S ∧ Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, x (k + 1) = x k ∧ Δ (k + 1) ≤ γ₂ * Δ k)
    (hmove : ∀ k ∈ S, u k - u (k + 1) ≤ L * Δ k)
    (hstay : ∀ k ∉ S, u (k + 1) = u k) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  let v (k : ℕ) := sqpNormalizedMerit f c fmin (σ k) (x k)
  have hσpos (k : ℕ) := hσmin.trans_le (hσ k)
  have hexpand (r : ℝ) (hr : r ≠ 0) (z : E) :
      sqpNormalizedMerit f c fmin r z = (f z - fmin) / r + ‖c z‖ := by
    unfold sqpNormalizedMerit sqpMerit
    field_simp
    ring
  have hcompare (k : ℕ) : v (k + 1) ≤ sqpNormalizedMerit f c fmin (σ k) (x (k + 1)) := by
    simp only [v, hexpand _ (hσpos _).ne']
    exact add_le_add
      (div_le_div_of_nonneg_left (sub_nonneg.mpr (hf _)) (hσpos _) (hσmono (Nat.le_succ _)))
      le_rfl
  have hdrop (k : ℕ) (hk : k ∈ S) : η * (d k / σ k) ≤ v k - v (k + 1) := by
    have hactual := hacc k hk
    have hnorm : sqpNormalizedMerit f c fmin (σ k) (x (k + 1)) ≤ v k - η * (d k / σ k) := by
      dsimp [v, sqpNormalizedMerit]
      rw [← mul_div_assoc, ← sub_div]
      exact (div_le_div_iff_of_pos_right (hσpos k)).mpr (by linarith)
    linarith only [(hcompare k).trans hnorm]
  have hmono : Antitone v := antitone_nat_of_succ_le fun k => by
    by_cases hk : k ∈ S
    · have h := hdrop k hk
      have hn := mul_nonneg hη.le (div_nonneg (hd_nonneg k) (hσpos k).le)
      linarith
    · have h := hcompare k
      rwa [(hrej k hk).1] at h
  have hcontrol : HasRelaxedProgress u v Δ S := by
    intro ε hε
    obtain ⟨p, hp, b, hb, e, he, hdecrease⟩ := hpred ε hε
    let r := min (e / b) ((1 - η₂) * p * b / (C + 1))
    refine ⟨η * p, b, e, r, 0, mul_pos hη hp, hb, he,
      lt_min (div_pos he hb) (by positivity), fun k _ hk => ⟨?_, ?_⟩⟩
    · intro hr
      have hm : b * Δ k ≤ e := by
        have hh := (le_div_iff₀ hb).mp (hr.trans (min_le_left _ _))
        simpa only [mul_comm] using hh
      have hd := hdecrease k hk
      rw [min_eq_right hm] at hd
      have hs : 0 < 1 + σ k := by positivity [hσpos k]
      have hpos := (mul_pos (mul_pos hp hs) (mul_pos hb (hΔ k))).trans_le hd
      have hCΔ : C * Δ k ≤ (1 - η₂) * p * b := by
        have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp (hr.trans (min_le_right _ _))
        linarith only [hh, hΔ k]
      have hbound := mul_le_mul_of_nonneg_right hCΔ (mul_nonneg hs.le (hΔ k).le)
      have hbound' := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hη₂'.le)
      have hv : η₂ ≤ Optimization.reductionRatio
          (sqpMerit f c (σ k)) (x k) (s k) (d k) := by
        have h := Optimization.le_reductionRatio_of_abs_sub_le hpos
          ((herr k).trans (by nlinarith only [hbound, hbound']))
        linarith only [h]
      exact hvery k hv
    · intro hS
      have hd : p * min e (b * Δ k) ≤ d k / σ k := by
        apply (le_div_iff₀ (hσpos k)).mpr
        have hh := mul_le_mul_of_nonneg_right
          (show σ k ≤ 1 + σ k by linarith)
          (mul_nonneg hp.le (le_min he.le (mul_nonneg hb.le (hΔ k).le)))
        nlinarith only [hh, hdecrease k hk]
      rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left hd hη.le).trans (hdrop k hS)
  refine tendsto_zero_of_relaxed_steps hγ hγ₂ hγ₂'
    hu ?_ hΔ hmono hnext (fun k hk => ⟨(hrej k hk).2, hstay k hk⟩)
    (fun _ _ => ⟨L, hL, 0, fun k _ _ hk => hmove k hk⟩) hcontrol
  intro k
  rw [show v k = sqpNormalizedMerit f c fmin (σ k) (x k) from rfl,
    hexpand _ (hσpos k).ne']
  exact add_nonneg (div_nonneg (sub_nonneg.mpr (hf k)) (hσpos k).le) (norm_nonneg _)

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
private theorem sqp_actual_decrease_of_ratio (f : E → ℝ) (c : E → F) (x s : E)
    {σ η d : ℝ} (hη : 0 < η) (hd : 0 ≤ d)
    (hr : η ≤ Optimization.reductionRatio (sqpMerit f c σ) x s d) :
    η * d ≤ sqpMerit f c σ x - sqpMerit f c σ (x + s) := by
  have hp : 0 < d := by
    by_contra! h
    have hz := le_antisymm h hd
    simp [Optimization.reductionRatio, hz, not_le_of_gt hη] at hr
  exact (le_div_iff₀ hp).mp hr

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- **Theorem 15.4.6** of [conn2000trust]. Let $x_k$, $s_k$, $\sigma_k$, $\delta_k$ and
$\Delta_k > 0$ be the iterates, steps, penalties, predicted decreases and radii of a run, and
$S$ the set of successful iterations. Let $0 < \eta \le \eta_2 < 1$, $\nu, b > 0$, $C, L \ge 0$,
$\sigma_{\min} > 0$, $\gamma > 0$ and $0 \le \gamma_2 < 1$. Suppose that, for all $k$:

* $f(x_k) \ge f_{\min}$, $\sigma_k \ge \sigma_{\min}$, and $\sigma_k$ is nondecreasing;
* $k \in S$ if and only if $\rho_k \ge \eta$;
* $\nu \sigma_k \min\{\|c(x_k)\|, b \Delta_k\} \le \delta_k$;
* $|\phi_{\sigma_k}(x_k + s_k) - (\phi_{\sigma_k}(x_k) - \delta_k)| \le C (1 + \sigma_k)
  \Delta_k^2$;
* $\gamma \Delta_k \le \Delta_{k+1}$, and $\rho_k \ge \eta_2$ implies
  $\Delta_k \le \Delta_{k+1}$;
* if $k \in S$, then $x_{k+1} = x_k + s_k$ and $\|c(x_k + s_k) - c(x_k)\| \le L \Delta_k$;
* if $k \notin S$, then $x_{k+1} = x_k$ and $\Delta_{k+1} \le \gamma_2 \Delta_k$.

Then $c(x_k) \to 0$.

**Reading.** The radius argument uses the update after a very successful iteration,
$\Delta_k \le \Delta_{k+1}$ when $\rho_k \ge \eta_2$.

The lower bound on the model decrease combines (15.4.7) and Lemma 15.4.1, and the error bound is
the second inequality of Lemma 15.4.3. The variation bound on the constraints is required only
on the steps actually taken.

**Reading.** The limits use explicit predictions, uniform original-trial model errors, the ratio and
radius branches, and variation on accepted steps. Normal criticality is abstracted to a vector field
used at the iterates. Conversion to feasibility uses a uniform positive lower singular-value bound.
-/
theorem theorem_15_4_6 (f : E → ℝ) (c : E → F) (x s : ℕ → E) (σ d Δ : ℕ → ℝ)
    (S : Set ℕ) {fmin σmin η η₂ ν b C L γ γ₂ : ℝ}
    (hη : 0 < η) (hη₂ : η ≤ η₂) (hη₂' : η₂ < 1) (hν : 0 < ν) (hb : 0 < b) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hσmin : 0 < σmin) (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hf : ∀ k, fmin ≤ f (x k)) (hσ : ∀ k, σmin ≤ σ k) (hσmono : Monotone σ)
    (hΔ : ∀ k, 0 < Δ k)
    (hratio : ∀ k, k ∈ S ↔ η ≤ Optimization.reductionRatio
      (sqpMerit f c (σ k)) (x k) (s k) (d k))
    (hpred : ∀ k, ν * σ k * min ‖c (x k)‖ (b * Δ k) ≤ d k)
    (herr : ∀ k, |sqpMerit f c (σ k) (x k + s k) -
      (sqpMerit f c (σ k) (x k) - d k)| ≤ C * (1 + σ k) * (Δ k) ^ 2)
    (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hacc : ∀ k ∈ S, x (k + 1) = x k + s k)
    (hvery : ∀ k, η₂ ≤ Optimization.reductionRatio
      (sqpMerit f c (σ k)) (x k) (s k) (d k) → Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, x (k + 1) = x k ∧ Δ (k + 1) ≤ γ₂ * Δ k)
    (hmove : ∀ k ∈ S, ‖c (x k + s k) - c (x k)‖ ≤ L * Δ k) :
    Filter.Tendsto (fun k => c (x k)) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine sqp_tendsto_zero_of_normal_decrease f c x s σ d Δ (fun k => ‖c (x k)‖) S
    hη hη₂' hC hL hσmin hγ hγ₂ hγ₂' hf hσ hσmono hΔ
    (fun k => norm_nonneg _) ?_ ?_ herr hnext ?_
    (fun k hk => ⟨(hratio k).mpr (hη₂.trans hk), hvery k hk⟩) hrej ?_ ?_
  · intro k
    exact (mul_nonneg (mul_nonneg hν.le (hσmin.le.trans (hσ k)))
      (le_min (norm_nonneg _) (mul_nonneg hb.le (hΔ k).le))).trans (hpred k)
  · intro ε hε
    let p := ν * (σmin / (1 + σmin))
    refine ⟨p, by dsimp [p]; positivity, b, hb, ε, hε, fun k hk => ?_⟩
    have hh : σmin / (1 + σmin) * (1 + σ k) ≤ σ k := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 1 + σmin)).mpr
      linarith only [hσ k]
    have hcoeff : p * (1 + σ k) ≤ ν * σ k := by
      rw [show p * (1 + σ k) = ν * (σmin / (1 + σmin) * (1 + σ k)) by dsimp [p]; ring]
      exact mul_le_mul_of_nonneg_left hh hν.le
    exact (mul_le_mul hcoeff (min_le_min_right _ hk)
      (le_min hε.le (mul_nonneg hb.le (hΔ k).le))
      (mul_nonneg hν.le (hσmin.le.trans (hσ k)))).trans (hpred k)
  · intro k hk
    rw [hacc k hk]
    have hd := (mul_nonneg (mul_nonneg hν.le (hσmin.le.trans (hσ k)))
      (le_min (norm_nonneg _) (mul_nonneg hb.le (hΔ k).le))).trans (hpred k)
    exact sqp_actual_decrease_of_ratio f c (x k) (s k) hη hd ((hratio k).mp hk)
  · intro k hk
    rw [hacc k hk]
    calc
      _ ≤ ‖c (x k) - c (x k + s k)‖ := norm_sub_norm_le _ _
      _ = ‖c (x k + s k) - c (x k)‖ := norm_sub_rev _ _
      _ ≤ _ := hmove k hk
  · intro k hk
    rw [(hrej k hk).1]

/-- **Lemma 15.4.7** of [conn2000trust]. Let $\kappa > 0$, $A n_C + c = 0$,
$\|n_C\| \le \kappa \|c\|$ and $\alpha \in [0, 1]$. Then the normal decrease
$\delta_N = \|c\| - \|c + \alpha A n_C\|$ satisfies
$$\frac{1}{\kappa} \|\alpha n_C\| \le \delta_N \le \|c\|.$$

The exact reduction identity (15.4.16) gives the coefficient $1/\kappa$ directly, whichever
radius bound is active.

**Reading.** Scaling chooses one when the trial normal step is zero, and otherwise uses the printed
interval. The step and decrease estimates take an explicit bound for the linearized normal solution.
-/
theorem lemma_15_4_7 {c : F} {A : E →L[ℝ] F} {nC : E} {α κ : ℝ}
    (hκ : 0 < κ) (hlin : A nC + c = 0) (hbound : ‖nC‖ ≤ κ * ‖c‖)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let dN := sqpNormalModel c A 0 - sqpNormalModel c A (α • nC)
    (1 / κ) * ‖α • nC‖ ≤ dN ∧ dN ≤ ‖c‖ := by
  dsimp only
  rw [sqpNormalModel_decrease_scaled hlin hα.2,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hα.1]
  refine ⟨?_, mul_le_of_le_one_left (norm_nonneg _) hα.2⟩
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ hκ).mpr (by
    calc
      α * ‖nC‖ ≤ α * (κ * ‖c‖) := mul_le_mul_of_nonneg_left hbound hα.1
      _ = α * ‖c‖ * κ := by ring)

/-- **Algorithm 15.4.1**, Step 2, of [conn2000trust]. For constants $\tau_1, \tau_2$, the required
penalty $\sigma_{\mathrm{req}}$ and the previous penalty $\sigma$, the **penalty update** is
$$\sigma^+ = \begin{cases} \sigma & \text{if } \sigma_{\mathrm{req}} \le \sigma, \\
  \max\{\sigma_{\mathrm{req}}, \tau_1 \sigma, \sigma + \tau_2\} & \text{otherwise.}
  \end{cases}$$

**Reading.** The scalar update separates the auxiliary requirement and the model threshold,
including a zero normal decrease branch. Stabilization is proved from an eventual uniform bound on
the requirements and a positive additive upgrade whenever the weight changes.
-/
noncomputable def sqpPenaltyUpdate (τ₁ τ₂ required previous : ℝ) : ℝ :=
  if required ≤ previous then previous else max required (max (τ₁ * previous) (previous + τ₂))

/-- **Theorem 15.4.8** of [conn2000trust], the stabilization argument. Let $\tau_1 \ge 0$,
$\tau_2 > 0$ and $\sigma_0 > 0$, and let $\sigma_{k+1}$ be the penalty update of $\sigma_k$ with
the required penalty $r_k$. If $r_k \le B$ for all $k \ge K$, then there is $j \ge K$ with
$\sigma_j > 0$ and $\sigma_k = \sigma_j$ for all $k \ge j$.

Each increase adds at least $\tau_2$, so a bounded threshold allows only finitely many
increases.

**Reading.** The scalar update separates the auxiliary requirement and the model threshold,
including a zero normal decrease branch. Stabilization is proved from an eventual uniform bound on
the requirements and a positive additive upgrade whenever the weight changes.
-/
theorem sqpPenaltyUpdate_eventually_constant {τ₁ τ₂ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 < τ₂)
    {required σ : ℕ → ℝ} (hσ₀ : 0 < σ 0)
    (hupdate : ∀ k, σ (k + 1) = sqpPenaltyUpdate τ₁ τ₂ (required k) (σ k))
    {B : ℝ} {K : ℕ} (hrequired : ∀ k ≥ K, required k ≤ B) :
    ∃ j, K ≤ j ∧ 0 < σ j ∧ ∀ k ≥ j, σ k = σ j := by
  have hgap (k : ℕ) : σ (k + 1) = σ k ∨ τ₂ ≤ σ (k + 1) - σ k := by
    rw [hupdate, sqpPenaltyUpdate]
    split_ifs with h
    · exact Or.inl rfl
    · apply Or.inr
      have h := le_max_right (τ₁ * σ k) (σ k + τ₂)
      exact le_sub_iff_add_le.mpr (by linarith [h.trans (le_max_right (required k) _)])
  have hmono : Monotone σ := monotone_nat_of_le_succ fun k => by
    rcases hgap k with h | h
    · exact h.ge
    · linarith
  have hpos (k : ℕ) : 0 < σ k := hσ₀.trans_le (hmono (Nat.zero_le k))
  let M := max (σ K) (max B (max (τ₁ * B) (B + τ₂)))
  have hM : ∀ k ≥ K, σ k ≤ M := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ k hk ih =>
      rw [hupdate, sqpPenaltyUpdate]
      split_ifs with h
      · exact ih
      · have hsmall : σ k ≤ B := (lt_of_not_ge h).le.trans (hrequired k hk)
        have h₁ := hrequired k hk
        have h₂ := mul_le_mul_of_nonneg_left hsmall hτ₁
        have h₃ := add_le_add hsmall (le_refl τ₂)
        exact (max_le_max h₁ (max_le_max h₂ h₃)).trans (le_max_right _ _)
  have hbd : BddAbove (Set.range σ) := ⟨M, by
    rintro _ ⟨k, rfl⟩
    by_cases hk : K ≤ k
    · exact hM k hk
    · exact (hmono (le_of_not_ge hk)).trans (hM K le_rfl)⟩
  have hlim := tendsto_atTop_ciSup hmono hbd
  have hdiff : Filter.Tendsto (fun k => σ (k + 1) - σ k) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, sub_self] using
      (hlim.comp (Filter.tendsto_add_atTop_nat 1)).sub hlim
  obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hτ₂))
  let l := max K j
  refine ⟨l, le_max_left _ _, hpos l, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have heq : σ (k + 1) = σ k :=
      (hgap k).resolve_right (not_le_of_gt (hj k ((le_max_right K j).trans hk)))
    exact heq.trans ih

/-- **Theorem 15.4.8** of [conn2000trust]. Let $g_k, n_k \in E$, $H_k : E \to E$, and let
$\delta_{N,k}$, $\delta_{T,k}$ and $\sigma_k$ be the normal decreases, tangential decreases and
penalties. Let $G, B, U \ge 0$, $b > 0$, $\nu < 1$, $\tau_1 \ge 0$, $\tau_2 > 0$ and
$\sigma_0 > 0$. Suppose that $\|g_k\| \le G$, $\|H_k\| \le B$, $\delta_{T,k} \ge 0$ and the
auxiliary thresholds satisfy $a_k \le S$ for all $k$, and that
$b \|n_k\| \le \delta_{N,k} \le U$ for all $k \ge K$. Let $\delta_{q,k} = -\langle g_k, n_k
\rangle - \frac{1}{2} \langle n_k, H_k n_k \rangle$, and let $\sigma_{k+1}$ be the penalty
update of $\sigma_k$ with the required penalty $a_k$ if $\delta_{N,k} = 0$ and
$\max\{a_k, \sigma_{\mathrm{req},k}\}$ otherwise. Then there are $\sigma_{\max} > 0$, $C \ge 0$
and $j$ such that for all $k \ge j$, $\sigma_{k+1} = \sigma_{\max}$ and
$$\delta_{T,k} + (\sigma_{k+1} - C) \delta_{N,k} \le \delta_{T,k} + \sigma_{k+1} \delta_{N,k} +
  \delta_{q,k}.$$

The objective term along the normal step is bounded by a constant times the normal decrease, and
the penalty eventually stops increasing. The penalty used at iteration $k$ has index $k + 1$,
and index $0$ is the initial penalty.

**Reading.** The scalar update separates the auxiliary requirement and the model threshold,
including a zero normal decrease branch. Stabilization is proved from an eventual uniform bound on
the requirements and a positive additive upgrade whenever the weight changes.
-/
theorem theorem_15_4_8 (g n : ℕ → E) (H : ℕ → E →L[ℝ] E)
    (dN dT σ auxiliary : ℕ → ℝ) {G B U b S ν τ₁ τ₂ : ℝ} {K : ℕ}
    (hG : 0 ≤ G) (hB : 0 ≤ B) (hU : 0 ≤ U) (hb : 0 < b)
    (hν : ν < 1) (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 < τ₂) (hσ₀ : 0 < σ 0)
    (hg : ∀ k, ‖g k‖ ≤ G) (hH : ∀ k, ‖H k‖ ≤ B)
    (hN : ∀ k ≥ K, b * ‖n k‖ ≤ dN k ∧ dN k ≤ U)
    (hT : ∀ k, 0 ≤ dT k) (haux : ∀ k, auxiliary k ≤ S)
    (hupdate : ∀ k,
      let dq := -⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫
      let required := if dN k = 0 then auxiliary k
        else max (auxiliary k) (sqpPenaltyThreshold ν (dN k) (dT k) dq)
      σ (k + 1) = sqpPenaltyUpdate τ₁ τ₂ required (σ k)) :
    ∃ σmax > 0, ∃ C ≥ 0, ∃ j, ∀ k ≥ j,
      σ (k + 1) = σmax ∧
      dT k + (σ (k + 1) - C) * dN k ≤
        dT k + σ (k + 1) * dN k +
          (-⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫) := by
  let dq (k : ℕ) := -⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫
  let required (k : ℕ) := if dN k = 0 then auxiliary k
    else max (auxiliary k) (sqpPenaltyThreshold ν (dN k) (dT k) (dq k))
  let C := (G + (1 / 2) * B * (U / b)) / b
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdq (k : ℕ) (hk : K ≤ k) : -(C * dN k) ≤ dq k := by
    have hnc := (hN k hk).1
    have hn : ‖n k‖ ≤ U / b := (le_div_iff₀ hb).mpr (by linarith [(hN k hk).2])
    have h₁ : ⟪g k, n k⟫ ≤ G * ‖n k‖ :=
      (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hg k) (norm_nonneg _)))
    have h₂ : ⟪n k, H k (n k)⟫ ≤ B * (U / b) * ‖n k‖ := calc
      _ ≤ |⟪n k, H k (n k)⟫| := le_abs_self _
      _ ≤ ‖n k‖ * ‖H k (n k)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖n k‖ * (‖H k‖ * ‖n k‖) :=
        mul_le_mul_of_nonneg_left ((H k).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖n k‖ * (B * (U / b)) := by
        gcongr
        exact hH k
      _ = _ := by ring
    have hthird : (G + (1 / 2) * B * (U / b)) * ‖n k‖ ≤ C * dN k := by
      have h := mul_le_mul_of_nonneg_left hnc hC
      have hCb : C * b = G + (1 / 2) * B * (U / b) := div_mul_cancel₀ _ hb.ne'
      rwa [← mul_assoc, hCb] at h
    dsimp [dq]
    linarith only [h₁, h₂, hthird]
  have hrequired (k : ℕ) (hk : K ≤ k) : required k ≤ max S (C / (1 - ν)) := by
    dsimp [required]
    split_ifs with hz
    · exact (haux k).trans (le_max_left _ _)
    · have hdN : 0 < dN k := lt_of_le_of_ne
        ((mul_nonneg hb.le (norm_nonneg _)).trans (hN k hk).1) (Ne.symm hz)
      apply max_le (le_trans (haux k) (le_max_left _ _))
      apply le_trans _ (le_max_right _ _)
      unfold sqpPenaltyThreshold
      rw [div_le_iff₀ (mul_pos (sub_pos.mpr hν) hdN)]
      have hcancel : C / (1 - ν) * ((1 - ν) * dN k) = C * dN k := by
        rw [← mul_assoc, div_mul_cancel₀ _ (sub_pos.mpr hν).ne']
      rw [hcancel]
      linarith only [hdq k hk, hT k]
  obtain ⟨j, hKj, hpos, hstable⟩ :=
    sqpPenaltyUpdate_eventually_constant hτ₁ hτ₂ hσ₀ hupdate hrequired
  refine ⟨σ j, hpos, C, hC, j, fun k hk => ⟨hstable _ (hk.trans (Nat.le_succ k)), ?_⟩⟩
  change _ ≤ dT k + σ (k + 1) * dN k + dq k
  linarith only [hdq k (hKj.trans hk)]

/-- **Lemma 15.4.9** of [conn2000trust], corrected. Let $\nu, \sigma > 0$, $B \ge 0$ and
$\delta_N \ge 0$. If $\delta_T + (\sigma - B) \delta_N \le \delta_m$ and
$\nu \sigma \delta_N \le \delta_m$, then
$$0 < \frac{\nu \sigma}{\nu \sigma + B} \quad \text{and} \quad \frac{\nu \sigma}{\nu \sigma + B}
  \delta_T \le \delta_m.$$

**Correction.** The coefficient in the printed proof can be negative; see
`ConnGouldToint.Chapter15.printed_tangential_coefficient_nonpos`. The coefficient here is
positive for every bound $B \ge 0$ on the normal objective loss, even if the stabilized penalty
meets or exceeds $B$.

**Correction.** The bound uses the positive coefficient obtained by combining the two lower bounds
on overall decrease. The coefficient in the printed proof can be negative.
-/
theorem lemma_15_4_9 {ν σ B : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hB : 0 ≤ B)
    {dN dT dm : ℝ} (hN : 0 ≤ dN)
    (h₁ : dT + (σ - B) * dN ≤ dm) (h₂ : ν * σ * dN ≤ dm) :
    0 < ν * σ / (ν * σ + B) ∧ (ν * σ / (ν * σ + B)) * dT ≤ dm := by
  have hp : 0 < ν * σ := mul_pos hν hσ
  have hden : 0 < ν * σ + B := add_pos_of_pos_of_nonneg hp hB
  refine ⟨div_pos hp hden, ?_⟩
  have hT : dT ≤ dm + B * dN := by nlinarith only [h₁, mul_nonneg hσ.le hN]
  have hh := mul_le_mul_of_nonneg_left hT hp.le
  have hh' := mul_le_mul_of_nonneg_left h₂ hB
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hh, hh']

/-- The coefficient in the printed proof of Lemma 15.4.9 of [conn2000trust] can be negative:
$$\tfrac{1}{2} \min\Bigl\{1, \frac{\frac{1}{2} \cdot 2}{1 - 2}\Bigr\} < 0.$$
Here the penalty $2$ exceeds the bound $1$ on the normal objective loss. This shows the
correction in `ConnGouldToint.Chapter15.lemma_15_4_9`.

**Correction.** The bound uses the positive coefficient obtained by combining the two lower bounds
on overall decrease. The coefficient in the printed proof can be negative.
-/
theorem printed_tangential_coefficient_nonpos :
    (1 / 2 : ℝ) * min 1 ((1 / 2) * 2 / (1 - 2)) < 0 := by
  norm_num

/-- **Algorithm 15.4.1** of [conn2000trust], the tail with a fixed penalty. Let $P$ be the
parameters of the basic trust-region algorithm. The scalar data of the tail consist of the
reduced gradient norms $u_k$, their perturbations $w_k$ by the normal step, the shifted merit
values $v_k$ at the fixed penalty, the radii $\Delta_k$, the predicted decreases $\delta_k$, the
actual decreases $a_k$, and the set $S$ of successful iterations. They satisfy the fields below.

Here $u_k$ is the unshifted reduced gradient norm, $w_k$ includes the correction by the normal
step, and $v_k$ is the merit function shifted by a lower bound.

**Correction.** The stabilized-tail argument takes uniform model error, predicted decrease, and
convergence of the perturbation between base and shifted reduced gradients explicitly.
Whole-sequence convergence also assumes controlled reduced-gradient variation on accepted steps and
no change on rejection.
-/
structure SQPTangentialRun (P : BTRParams) (u w v Δ d actual : ℕ → ℝ) (S : Set ℕ) where
  /-- The reduced gradient norms are nonnegative. -/
  u_nonneg : ∀ k, 0 ≤ u k
  /-- The shifted merit values are nonnegative. -/
  merit_nonneg : ∀ k, 0 ≤ v k
  /-- The radii are positive. -/
  radius_pos : ∀ k, 0 < Δ k
  /-- The shifted merit values are nonincreasing. -/
  merit_antitone : Antitone v
  /-- The radius update satisfies $\gamma_1 \Delta_k \le \Delta_{k+1}$. -/
  radius_lower : ∀ k, P.γ₁ * Δ k ≤ Δ (k + 1)
  /-- After a rejection, $\Delta_{k+1} \le \gamma_2 \Delta_k$. -/
  radius_rejected : ∀ k ∉ S, Δ (k + 1) ≤ P.γ₂ * Δ k
  /-- After a success, $\eta_1 \delta_k \le v_k - v_{k+1}$. -/
  merit_successful : ∀ k ∈ S, P.η₁ * d k ≤ v k - v (k + 1)
  /-- If $a_k / \delta_k \ge \eta_2$, the iteration is successful and $\Delta_k \le \Delta_{k+1}$.
  -/
  very_successful : ∀ k, P.η₂ ≤ actual k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1)

/-- **Theorem 15.4.10** of [conn2000trust], the reduced gradient estimate. Let $H_k : E \to E$ with
$\|H_k\| \le B$, and let $N_k^T : E \to Z$ be continuous linear maps with $\|N_k^T\| \le D$ for
some $D \ge 0$. If the normal steps satisfy $n_k \to 0$, then
$$\|N_k^T (g_k + H_k n_k)\| - \|N_k^T g_k\| \to 0.$$

**Correction.** The stabilized-tail argument takes uniform model error, predicted decrease, and
convergence of the perturbation between base and shifted reduced gradients explicitly.
Whole-sequence convergence also assumes controlled reduced-gradient variation on accepted steps and
no change on rejection.
-/
theorem sqpReducedGradient_perturbation {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (g n : ℕ → E) (H : ℕ → E →L[ℝ] E) (NT : ℕ → E →L[ℝ] Z)
    {B D : ℝ} (hD : 0 ≤ D)
    (hH : ∀ k, ‖H k‖ ≤ B) (hNT : ∀ k, ‖NT k‖ ≤ D)
    (hn : Filter.Tendsto n Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ‖NT k (g k + H k (n k))‖ - ‖NT k (g k)‖)
      Filter.atTop (nhds 0) := by
  have hn' : Filter.Tendsto (fun k => ‖n k‖) Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hn
  refine squeeze_zero_norm' (a := fun k => D * (B * ‖n k‖)) ?_ ?_
  · apply Filter.Eventually.of_forall
    intro k
    calc
      _ ≤ ‖NT k (g k + H k (n k)) - NT k (g k)‖ := abs_norm_sub_norm_le _ _
      _ = ‖NT k (H k (n k))‖ := by rw [map_add, add_sub_cancel_left]
      _ ≤ ‖NT k‖ * ‖H k (n k)‖ := (NT k).le_opNorm _
      _ ≤ D * (B * ‖n k‖) := by
        exact mul_le_mul (hNT k) (((H k).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hH k) (norm_nonneg _))) (norm_nonneg _) hD
  · simpa only [mul_zero] using (hn'.const_mul B).const_mul D

private theorem tangentialProgress {P : BTRParams} {u w v Δ d actual : ℕ → ℝ} {S : Set ℕ}
    (run : SQPTangentialRun P u w v Δ d actual S)
    {κ b β C : ℝ} (hκ : 0 < κ) (hb : 0 < b) (hβ : 0 < β) (hC : 0 ≤ C)
    (hpert : Filter.Tendsto (fun k => w k - u k) Filter.atTop (nhds 0))
    (hpred : ∀ᶠ k in Filter.atTop, κ * w k * min (b * Δ k) (w k / β) ≤ d k)
    (herr : ∀ᶠ k in Filter.atTop, |actual k - d k| ≤ C * (Δ k) ^ 2) :
    HasRelaxedProgress u v Δ S := by
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  let r := sqpTangentialAcceptanceRadius e β b P.η₂ κ C
  have hr : 0 < r := lt_min (div_pos he (mul_pos hβ hb)) (by positivity [P.eta₂_lt_one])
  have hsmall := hpert.eventually (lt_mem_nhds (neg_neg_of_pos he))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp ((hsmall.and hpred).and herr)
  refine ⟨P.η₁ * κ * e, b, e / β, r, K, by positivity [P.eta₁_pos], hb,
    div_pos he hβ, hr, ?_⟩
  intro k hk hu
  have h := hK k hk
  have hw : e ≤ w k := by
    have ht : -e < w k - u k := h.1.1
    dsimp [e] at ht ⊢
    linarith
  have hbound : κ * e * min (b * Δ k) (e / β) ≤ d k := by
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hw hκ.le) ?_ ?_ ?_).trans h.1.2
    · exact min_le_min_left _ (div_le_div_of_nonneg_right hw hβ.le)
    · exact le_min (mul_nonneg hb.le (run.radius_pos k).le) (div_nonneg he.le hβ.le)
    · exact mul_nonneg hκ.le (he.le.trans hw)
  constructor
  · intro hΔ
    exact run.very_successful k (sqpTangentialAcceptanceRadius_ratio he hβ hb
      P.eta₂_lt_one hκ hC (run.radius_pos k) hΔ hbound h.2)
  · intro hkS
    have hh := mul_le_mul_of_nonneg_left hbound P.eta₁_pos.le
    rw [min_comm (e / β), mul_assoc P.η₁ κ]
    simpa only [mul_assoc] using hh.trans (run.merit_successful k hkS)

/-- **Theorem 15.4.10** of [conn2000trust], with uniform trial-segment control. Consider the tail
data of a run with a fixed penalty, and let $\kappa, b, \beta > 0$ and $C \ge 0$. Suppose that
$w_k - u_k \to 0$, and that for all large $k$
$$\kappa w_k \min\{b \Delta_k, w_k / \beta\} \le \delta_k, \qquad |a_k - \delta_k| \le C
  \Delta_k^2.$$
Then $\liminf_k u_k = 0$.

**Correction.** The error bound $|a_k - \delta_k| \le C \Delta_k^2$ holds uniformly on the trial
segments; see `ConnGouldToint.Chapter15.sqp_trialSegment_counterexample`. The radius threshold
in the proof includes the Cauchy coefficient; see
`ConnGouldToint.Chapter15.sqpTangentialAcceptanceRadius`.

The tail data are `ConnGouldToint.Chapter15.SQPTangentialRun`, with a bounded penalty and a
vanishing normal perturbation.

**Correction.** The stabilized-tail argument takes uniform model error, predicted decrease, and
convergence of the perturbation between base and shifted reduced gradients explicitly.
Whole-sequence convergence also assumes controlled reduced-gradient variation on accepted steps and
no change on rejection.
-/
theorem theorem_15_4_10 {P : BTRParams} {u w v Δ d actual : ℕ → ℝ} {S : Set ℕ}
    (run : SQPTangentialRun P u w v Δ d actual S)
    {κ b β C : ℝ} (hκ : 0 < κ) (hb : 0 < b) (hβ : 0 < β) (hC : 0 ≤ C)
    (hpert : Filter.Tendsto (fun k => w k - u k) Filter.atTop (nhds 0))
    (hpred : ∀ᶠ k in Filter.atTop, κ * w k * min (b * Δ k) (w k / β) ≤ d k)
    (herr : ∀ᶠ k in Filter.atTop, |actual k - d k| ≤ C * (Δ k) ^ 2) :
    Filter.liminf u Filter.atTop = 0 := by
  have hcontrol := tangentialProgress run hκ hb hβ hC hpert hpred herr
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in Filter.atTop, u k < ε :=
    Filter.frequently_atTop.mpr (relaxed_progress_frequently_small P.gamma₁_pos
      (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one run.merit_nonneg
      run.radius_pos run.merit_antitone run.radius_lower run.radius_rejected hcontrol ε hε)
  have hbdd : (Filter.atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) u :=
    ⟨0, show ∀ᶠ k in Filter.atTop, 0 ≤ u k from Filter.Eventually.of_forall run.u_nonneg⟩
  have hc : (Filter.atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) u := by
    refine ⟨1, fun b h => ?_⟩
    obtain ⟨k, hk, hbk⟩ := ((hfreq 1 zero_lt_one).and_eventually h).exists
    exact hbk.trans hk.le
  refine le_antisymm ?_ (Filter.le_liminf_of_le hc (Filter.Eventually.of_forall run.u_nonneg))
  by_contra! hp
  have hlim := Filter.liminf_le_of_frequently_le
    ((hfreq _ (half_pos hp)).mono fun _ h => h.le) hbdd
  linarith

/-- **Theorem 15.4.11** of [conn2000trust], with trial-segment and reduced-gradient control. Under
the hypotheses of Theorem 15.4.10, suppose also that $L \ge 0$, that
$u_k - u_{k+1} \le L \Delta_k$ for $k \in S$, and that $u_{k+1} = u_k$ for $k \notin S$. Then
$u_k \to 0$.

**Correction.** The uniform control of the variation of the reduced gradient on accepted steps
is a hypothesis. It follows, for example, from a Lipschitz reduced-gradient map and the bound on
the composite step by the radius.

**Correction.** The stabilized-tail argument takes uniform model error, predicted decrease, and
convergence of the perturbation between base and shifted reduced gradients explicitly.
Whole-sequence convergence also assumes controlled reduced-gradient variation on accepted steps and
no change on rejection.
-/
theorem theorem_15_4_11 {P : BTRParams} {u w v Δ d actual : ℕ → ℝ} {S : Set ℕ}
    (run : SQPTangentialRun P u w v Δ d actual S)
    {κ b β C L : ℝ} (hκ : 0 < κ) (hb : 0 < b) (hβ : 0 < β) (hC : 0 ≤ C)
    (hpert : Filter.Tendsto (fun k => w k - u k) Filter.atTop (nhds 0))
    (hpred : ∀ᶠ k in Filter.atTop, κ * w k * min (b * Δ k) (w k / β) ≤ d k)
    (herr : ∀ᶠ k in Filter.atTop, |actual k - d k| ≤ C * (Δ k) ^ 2)
    (hL : 0 ≤ L) (hmove : ∀ k ∈ S, u k - u (k + 1) ≤ L * Δ k)
    (hstay : ∀ k ∉ S, u (k + 1) = u k) :
    Filter.Tendsto u Filter.atTop (nhds 0) :=
  tendsto_zero_of_relaxed_steps P.gamma₁_pos
    (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one
    run.u_nonneg run.merit_nonneg run.radius_pos run.merit_antitone run.radius_lower
    (fun k hk => ⟨run.radius_rejected k hk, hstay k hk⟩)
    (fun _ _ => ⟨L, hL, 0, fun k _ _ hk => hmove k hk⟩)
    (tangentialProgress run hκ hb hβ hC hpert hpred herr)

/-- **Lemma 15.4.17** of [conn2000trust]. Let $E$ and $Z$ be real Hilbert spaces, $c \in Z$,
$A : E \to Z$ continuous linear and $R \ge 0$, and let $n$ be a Cauchy point of the normal model
$\|c + A n\|$ along $-A^* c$ in the Euclidean norm with radius $R$. Then
$$\frac{1}{2} \frac{\|A^* c\|}{\|c\|} \min\Bigl\{R, \frac{\|A^* c\|}{1 + \|A^* A\|}\Bigr\} \le
  \|c\| - \|c + A n\|.$$

Squaring the residual does not change the Cauchy point, so the Cauchy bound for the quadratic
model transfers to the unsquared normal model. When $c = 0$ the decrease is $0$ and the Lean
quotient $\|A^* c\| / \|c\|$ is $0$.

**Reading.** The bound is stated directly for the normal model with adjoint gradient and Gram
curvature. The ratio is totalized when the constraint residual is zero.
-/
theorem lemma_15_4_17 [CompleteSpace E]
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (c : Z) (A : E →L[ℝ] Z) {R : ℝ} (hR : 0 ≤ R) {n : E}
    (hC : IsCauchyPoint (sqpNormalModel c A) (normSeminorm ℝ E) (A.adjoint c) R n) :
    (1 / 2) * (‖A.adjoint c‖ / ‖c‖) *
      min R (‖A.adjoint c‖ / quadraticCurvatureBound (A.adjoint.comp A)) ≤
      sqpNormalModel c A 0 - sqpNormalModel c A n := by
  let H := A.adjoint.comp A
  let g := A.adjoint c
  have hmodel (s : E) :
      quadraticModel (‖c‖ ^ 2 / 2) g H.toLinearMap s = sqpNormalModel c A s ^ 2 / 2 := by
    simp only [quadraticModel, g, H, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      sqpNormalModel, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      A.adjoint_inner_left, A.adjoint_inner_right]
    rw [real_inner_comm (A s) c]
    ring
  have hCq : IsCauchyPoint (quadraticModel (‖c‖ ^ 2 / 2) g H.toLinearMap)
      (normSeminorm ℝ E) g R n := by
    refine ⟨isMinOn_iff.mpr (fun s hs => ?_), hC.2⟩
    rw [hmodel, hmodel]
    have hle := isMinOn_iff.mp hC.1 s hs
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hle _) (by norm_num)
  have hzero : (0 : E) ∈ cauchyArc (normSeminorm ℝ E) g R :=
    ⟨0, le_rfl, by simp, by simpa using hR⟩
  have hdec := isMinOn_iff.mp hC.1 0 hzero
  simp only [sqpNormalModel, map_zero, add_zero] at hdec ⊢
  by_cases hc : c = 0
  · simp only [hc, zero_add, norm_zero, norm_le_zero_iff, one_div, map_zero, div_zero, mul_zero,
      zero_div, zero_mul, zero_sub, Left.nonneg_neg_iff] at hdec ⊢
    exact hdec
  have hcp : 0 < ‖c‖ := norm_pos_iff.mpr hc
  by_cases hg : g = 0
  · change (1 / 2) * (‖g‖ / ‖c‖) * _ ≤ _
    simpa [hg] using sub_nonneg.mpr hdec
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hsq := theorem_6_3_1 (‖c‖ ^ 2 / 2) g H (normSeminorm ℝ E)
    (fun v hv => norm_eq_zero.mp hv) hR hCq
  have hratio : cauchyNormRatio (normSeminorm ℝ E) g = 1 := by
    change ‖g‖ / ‖g‖ = 1
    exact div_self hgn.ne'
  rw [hmodel, hratio, one_mul, min_comm] at hsq
  change (1 / 2) * (‖g‖ / ‖c‖) * min R (‖g‖ / quadraticCurvatureBound H) ≤ _
  have hprod := mul_nonneg (sub_nonneg.mpr hdec) (sub_nonneg.mpr hdec)
  unfold sqpNormalModel at hsq
  apply (le_of_mul_le_mul_right _ hcp)
  field_simp
  nlinarith only [hsq, hprod]

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- **Lemma 15.4.18** of [conn2000trust], with uniform trial-segment control. Fix an iterate $x$,
and for each radius $r > 0$ let $s_r$, $m_r$ and $\sigma_r \ge \sigma_{\min} > 0$ be the step,
the overall model and the penalty. Let $\eta < 1$ and $C \ge 0$, and suppose that
$m_r(0) = \phi_{\sigma_r}(x)$ and $|\phi_{\sigma_r}(x + s_r) - m_r(s_r)| \le C (1 + \sigma_r)
r^2$ for all $r > 0$. Let $u$ be the normal criticality and $v$ the tangential criticality, and
suppose one of the two cases:

* $u = 0$, $v > 0$, and there are $R, \beta, \xi, \kappa > 0$ and $S \ge 0$ with
  $\sigma_r \le S$ and $\kappa v \min\{\xi r / R, v / \beta\} \le m_r(0) - m_r(s_r)$ for all
  $r > 0$;
* $u > 0$, $\|c(x)\| > 0$, and there are $\kappa, \beta, \xi > 0$ with $\kappa \sigma_r (u /
  \|c(x)\|) \min\{\xi r, u / \beta\} \le m_r(0) - m_r(s_r)$ for all $r > 0$.

Then there is $r_0 > 0$ such that $\rho \ge \eta$ for all $r \in (0, r_0]$.

**Correction.** The model error bound is required uniformly along the trial segments.

**Reading.** The small-radius acceptance argument uses an explicit uniform model-error bound for the
trial segment and lower bounds on predicted decrease for the two cases. The Byrd–Omojokun version
uses normal criticality where the first variant uses feasibility.
-/
theorem lemma_15_4_18 (f : E → ℝ) (c : E → F) (x : E)
    (s : ℝ → E) (m : ℝ → E → ℝ) (σ : ℝ → ℝ)
    {η C σmin u v : ℝ} (hη : η < 1) (hC : 0 ≤ C) (hmin : 0 < σmin)
    (hσ : ∀ r > 0, σmin ≤ σ r)
    (hcenter : ∀ r > 0, m r 0 = sqpMerit f c (σ r) x)
    (herr : ∀ r > 0, |sqpMerit f c (σ r) (x + s r) - m r (s r)| ≤
      C * (1 + σ r) * r ^ 2)
    (hcase :
      (u = 0 ∧ 0 < v ∧ ∃ R β ξ κ S : ℝ,
        0 < R ∧ 0 < β ∧ 0 < ξ ∧ 0 < κ ∧ 0 ≤ S ∧
        ∀ r > 0, σ r ≤ S ∧ κ * v * min (ξ * r / R) (v / β) ≤ m r 0 - m r (s r)) ∨
      (0 < u ∧ 0 < ‖c x‖ ∧ ∃ κ β ξ : ℝ, 0 < κ ∧ 0 < β ∧ 0 < ξ ∧
        ∀ r > 0, κ * σ r * (u / ‖c x‖) * min (ξ * r) (u / β) ≤ m r 0 - m r (s r))) :
    ∃ r₀ > 0, ∀ r ∈ Set.Ioc (0 : ℝ) r₀,
      η ≤ Optimization.reductionRatio (sqpMerit f c (σ r)) x (s r) (m r 0 - m r (s r)) := by
  apply sqp_acceptance_of_linear_decrease f c x s m σ hη hC hmin hσ hcenter herr
  apply sqp_linear_decrease hmin hσ
  rcases hcase with ⟨_, hv, R, β, ξ, κ, S, hR, hβ, hξ, hκ, hS, h⟩ |
    ⟨hu, hc, κ, β, ξ, hκ, hβ, hξ, h⟩
  · exact Or.inl ⟨v, R, β, ξ, κ, S, hv, hR, hβ, hξ, hκ, hS, h⟩
  · refine Or.inr ⟨u / β, κ * (u / ‖c x‖), ξ, by positivity, by positivity, hξ,
      fun r hr => ?_⟩
    rw [min_comm]
    simpa only [mul_right_comm κ (u / ‖c x‖) (σ r)] using h r hr

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- The extension of Theorem 15.4.19 of [conn2000trust] to corrected accepted trials, used in
Theorem 15.4.23. Let $a : E \to E$ be the normal criticality vector, and let $x_k$, $s_k$,
$\sigma_k$, $\delta_k$, $\Delta_k > 0$ and $S$ be the iterates, steps, penalties, predicted
decreases, radii and successful iterations. Let $0 < \eta$, $\eta_2 < 1$,
$\kappa, c_{\max}, \beta, \xi > 0$, $C, L \ge 0$, $\sigma_{\min} > 0$, $\gamma > 0$ and
$0 \le \gamma_2 < 1$. Suppose that, for all $k$:

* $f(x_k) \ge f_{\min}$, $\sigma_k \ge \sigma_{\min}$, and $\sigma_k$ is nondecreasing;
* $\kappa \sigma_k (\|a(x_k)\| / c_{\max}) \min\{\xi \Delta_k, \|a(x_k)\| / \beta\} \le
  \delta_k$;
* $|\phi_{\sigma_k}(x_k + s_k) - (\phi_{\sigma_k}(x_k) - \delta_k)| \le C (1 + \sigma_k)
  \Delta_k^2$;
* $\gamma \Delta_k \le \Delta_{k+1}$, and $\rho_k \ge \eta_2$ for the original trial implies
  $k \in S$ and $\Delta_k \le \Delta_{k+1}$;
* if $k \in S$, then $\eta \delta_k \le \phi_{\sigma_k}(x_k) - \phi_{\sigma_k}(x_{k+1})$ and
  $\|a(x_k)\| - \|a(x_{k+1})\| \le L \Delta_k$;
* if $k \notin S$, then $x_{k+1} = x_k$ and $\Delta_{k+1} \le \gamma_2 \Delta_k$.

Then $a(x_k) \to 0$.

Unlike `ConnGouldToint.Chapter15.theorem_15_4_19`, the statement does not require
$x_{k+1} = x_k + s_k$ on successful iterations, nor that $k \in S$ exactly when
$\rho_k \ge \eta$, nor $\eta \le \eta_2$. The acceptance test concerns the original trial, and
the decrease concerns the accepted iterate. The uniform trial error and the variation bound on
accepted steps make explicit the regularity that the convergence argument needs.

**Reading.** The limits use explicit predictions, uniform original-trial model errors, the ratio and
radius branches, and variation on accepted steps. Normal criticality is abstracted to a vector field
used at the iterates. Conversion to feasibility uses a uniform positive lower singular-value bound.
-/
theorem sqp_normal_criticality_of_accepted_decrease (f : E → ℝ) (c : E → F) (a : E → E)
    (x s : ℕ → E) (σ d Δ : ℕ → ℝ) (S : Set ℕ)
    {fmin σmin η η₂ κ cmax β ξ C L γ γ₂ : ℝ}
    (hη : 0 < η) (hη₂' : η₂ < 1)
    (hκ : 0 < κ) (hcmax : 0 < cmax) (hβ : 0 < β) (hξ : 0 < ξ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hσmin : 0 < σmin)
    (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hf : ∀ k, fmin ≤ f (x k)) (hσ : ∀ k, σmin ≤ σ k) (hσmono : Monotone σ)
    (hΔ : ∀ k, 0 < Δ k)
    (hpred : ∀ k, κ * σ k * (‖a (x k)‖ / cmax) *
      min (ξ * Δ k) (‖a (x k)‖ / β) ≤ d k)
    (herr : ∀ k, |sqpMerit f c (σ k) (x k + s k) -
      (sqpMerit f c (σ k) (x k) - d k)| ≤ C * (1 + σ k) * (Δ k) ^ 2)
    (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hacc : ∀ k ∈ S, η * d k ≤ sqpMerit f c (σ k) (x k) -
      sqpMerit f c (σ k) (x (k + 1)))
    (hvery : ∀ k, η₂ ≤ Optimization.reductionRatio
      (sqpMerit f c (σ k)) (x k) (s k) (d k) → k ∈ S ∧ Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, x (k + 1) = x k ∧ Δ (k + 1) ≤ γ₂ * Δ k)
    (hmove : ∀ k ∈ S, ‖a (x k)‖ - ‖a (x (k + 1))‖ ≤ L * Δ k) :
    Filter.Tendsto (fun k => a (x k)) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine sqp_tendsto_zero_of_normal_decrease f c x s σ d Δ (fun k => ‖a (x k)‖) S
    hη hη₂' hC hL hσmin hγ hγ₂ hγ₂' hf hσ hσmono hΔ
    (fun k => norm_nonneg _) ?_ ?_ herr hnext hacc hvery hrej hmove ?_
  · intro k
    have hs := hσmin.trans_le (hσ k)
    exact (mul_nonneg (mul_nonneg (mul_nonneg hκ.le hs.le)
      (div_nonneg (norm_nonneg _) hcmax.le)) (le_min (mul_nonneg hξ.le (hΔ k).le)
      (div_nonneg (norm_nonneg _) hβ.le))).trans (hpred k)
  · intro ε hε
    let p := κ * (ε / cmax) * (σmin / (1 + σmin))
    refine ⟨p, by dsimp [p]; positivity, ξ, hξ, ε / β, div_pos hε hβ, fun k hk => ?_⟩
    have hs := hσmin.trans_le (hσ k)
    have hh : σmin / (1 + σmin) * (1 + σ k) ≤ σ k := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 1 + σmin)).mpr
      linarith only [hσ k]
    have hcoeff : p * (1 + σ k) ≤ κ * σ k * (‖a (x k)‖ / cmax) := calc
      _ = κ * (σmin / (1 + σmin) * (1 + σ k)) * (ε / cmax) := by dsimp [p]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hh hκ.le)
        (div_le_div_of_nonneg_right hk hcmax.le) (div_nonneg hε.le hcmax.le) (by positivity)
    rw [min_comm (ε / β)]
    exact (mul_le_mul hcoeff (min_le_min_left _ (div_le_div_of_nonneg_right hk hβ.le))
      (le_min (mul_nonneg hξ.le (hΔ k).le) (div_nonneg hε.le hβ.le)) (by positivity)).trans
      (hpred k)
  · intro k hk
    rw [(hrej k hk).1]

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- **Theorem 15.4.19** of [conn2000trust], with uniform trial-segment control. Let $a : E \to E$ be
the normal criticality vector, and let $x_k$, $s_k$, $\sigma_k$, $\delta_k$, $\Delta_k > 0$ and
$S$ be as in Theorem 15.4.6, with $0 < \eta \le \eta_2 < 1$, $\kappa, c_{\max}, \beta, \xi > 0$,
$C, L \ge 0$, $\sigma_{\min} > 0$, $\gamma > 0$ and $0 \le \gamma_2 < 1$. Suppose that
$f(x_k) \ge f_{\min}$, $\sigma_k \ge \sigma_{\min}$ is nondecreasing, $k \in S$ if and only if
$\rho_k \ge \eta$, and
$$\kappa \sigma_k \frac{\|a(x_k)\|}{c_{\max}} \min\Bigl\{\xi \Delta_k,
  \frac{\|a(x_k)\|}{\beta}\Bigr\} \le \delta_k$$
(the Cauchy estimate (15.4.133)). Suppose also that the error bound and the radius rules of
Theorem 15.4.6 hold, that $x_{k+1} = x_k + s_k$ and
$\|a(x_k)\| - \|a(x_k + s_k)\| \le L \Delta_k$ for $k \in S$, and that $x_{k+1} = x_k$ for
$k \notin S$. Then $a(x_k) \to 0$.

**Correction.** The uniform trial error bound and the bound on the variation of the normal
criticality on accepted steps are hypotheses; they make explicit the regularity that the
convergence argument needs.

**Reading.** The limits use explicit predictions, uniform original-trial model errors, the ratio and
radius branches, and variation on accepted steps. Normal criticality is abstracted to a vector field
used at the iterates. Conversion to feasibility uses a uniform positive lower singular-value bound.
-/
theorem theorem_15_4_19 (f : E → ℝ) (c : E → F) (a : E → E)
    (x s : ℕ → E) (σ d Δ : ℕ → ℝ) (S : Set ℕ)
    {fmin σmin η η₂ κ cmax β ξ C L γ γ₂ : ℝ}
    (hη : 0 < η) (hη₂ : η ≤ η₂) (hη₂' : η₂ < 1)
    (hκ : 0 < κ) (hcmax : 0 < cmax) (hβ : 0 < β) (hξ : 0 < ξ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hσmin : 0 < σmin)
    (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hf : ∀ k, fmin ≤ f (x k)) (hσ : ∀ k, σmin ≤ σ k) (hσmono : Monotone σ)
    (hΔ : ∀ k, 0 < Δ k)
    (hratio : ∀ k, k ∈ S ↔ η ≤ Optimization.reductionRatio
      (sqpMerit f c (σ k)) (x k) (s k) (d k))
    (hpred : ∀ k, κ * σ k * (‖a (x k)‖ / cmax) *
      min (ξ * Δ k) (‖a (x k)‖ / β) ≤ d k)
    (herr : ∀ k, |sqpMerit f c (σ k) (x k + s k) -
      (sqpMerit f c (σ k) (x k) - d k)| ≤ C * (1 + σ k) * (Δ k) ^ 2)
    (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hacc : ∀ k ∈ S, x (k + 1) = x k + s k)
    (hvery : ∀ k, η₂ ≤ Optimization.reductionRatio
      (sqpMerit f c (σ k)) (x k) (s k) (d k) → Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, x (k + 1) = x k ∧ Δ (k + 1) ≤ γ₂ * Δ k)
    (hmove : ∀ k ∈ S, ‖a (x k)‖ - ‖a (x k + s k)‖ ≤ L * Δ k) :
    Filter.Tendsto (fun k => a (x k)) Filter.atTop (nhds 0) := by
  refine sqp_normal_criticality_of_accepted_decrease f c a x s σ d Δ S
    hη hη₂' hκ hcmax hβ hξ hC hL hσmin hγ hγ₂ hγ₂' hf hσ hσmono hΔ
    hpred herr hnext ?_ (fun k hk => ⟨(hratio k).mpr (hη₂.trans hk), hvery k hk⟩) hrej ?_
  · intro k hk
    rw [hacc k hk]
    have hs := hσmin.trans_le (hσ k)
    have hd := (mul_nonneg (mul_nonneg (mul_nonneg hκ.le hs.le)
      (div_nonneg (norm_nonneg _) hcmax.le)) (le_min (mul_nonneg hξ.le (hΔ k).le)
      (div_nonneg (norm_nonneg _) hβ.le))).trans (hpred k)
    exact sqp_actual_decrease_of_ratio f c (x k) (s k) hη hd ((hratio k).mp hk)
  · intro k hk
    simpa only [hacc k hk] using hmove k hk

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- **Corollary 15.4.20** of [conn2000trust]. Let $m > 0$, and suppose that $m \|c_k\| \le \|a_k\|$
for all $k$, the uniform lower singular-value bound of assumption AA.14. If $a_k \to 0$, then
$c_k \to 0$.

**Reading.** The limits use explicit predictions, uniform original-trial model errors, the ratio and
radius branches, and variation on accepted steps. Normal criticality is abstracted to a vector field
used at the iterates. Conversion to feasibility uses a uniform positive lower singular-value bound.
-/
theorem corollary_15_4_20 (c : ℕ → F) (a : ℕ → E) {m : ℝ} (hm : 0 < m)
    (hrank : ∀ k, m * ‖c k‖ ≤ ‖a k‖)
    (hcrit : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Filter.Tendsto c Filter.atTop (nhds 0) := by
  have ha : Filter.Tendsto (fun k => ‖a k‖) Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hcrit
  refine squeeze_zero_norm' (a := fun k => ‖a k‖ / m) ?_ ?_
  · exact Filter.Eventually.of_forall (fun k => (le_div_iff₀ hm).mpr (by
      rw [mul_comm]
      exact hrank k))
  · simpa only [zero_div] using ha.div_const m

/-- **Lemma 15.4.21** of [conn2000trust], corrected. Let $E$ and $Z$ be real Hilbert spaces, $W$ a
real normed space, and for each $k$ let $c_k \in Z$, $A_k : E \to Z$, $N_k : W \to E$,
$n_k, r_k, z_k$ and $\Delta_k \ge 0$. Let $B > 0$, $M, J \ge 0$, $m, \mu, \kappa, \beta > 0$ and
$\xi \ge 0$. Suppose that for all $k$:

* $\|A_k^*\| \le B$ and $\|N_k\| \le M$;
* $n_k = A_k^* r_k + N_k z_k$ with $A_k N_k z_k = 0$ and $\|z_k\| \le J \|r_k\|$;
* $m \|c_k\| \le \|A_k^* c_k\|$ and $\mu \|r_k\| \le \|A_k A_k^* r_k\|$;
* $\|n_k\| \le \xi \Delta_k$ and
$$\kappa \frac{\|A_k^* c_k\|}{\|c_k\|} \min\Bigl\{\xi \Delta_k, \frac{\|A_k^*
  c_k\|}{\beta}\Bigr\} \le \delta_{N,k},$$
where $\delta_{N,k} = \|c_k\| - \|c_k + A_k n_k\|$.

Then there is $a > 0$ with $a \|n_k\| \le \delta_{N,k} \le \|c_k\|$ for all $k$.

**Correction.** In (15.4.142), the second entry of the minimum uses the reciprocal of the rank
constant. The rank lower bound is used in both factors of the Cauchy estimate.

**Correction.** The minimum uses the bound on the smallest singular value in the proper factor. The
estimate makes explicit the decomposition of the normal step, the bound on its null-space component,
and the relevant rank inequalities.
-/
theorem lemma_15_4_21 [CompleteSpace E]
    {Z W : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (c : ℕ → Z) (A : ℕ → E →L[ℝ] Z) (N : ℕ → W →L[ℝ] E)
    (n : ℕ → E) (r : ℕ → Z) (z : ℕ → W) (Δ : ℕ → ℝ)
    {B M J m μ κ ξ β : ℝ} (hB : 0 < B) (hM : 0 ≤ M) (hJ : 0 ≤ J)
    (hm : 0 < m) (hμ : 0 < μ) (hκ : 0 < κ) (hξ : 0 ≤ ξ) (hβ : 0 < β)
    (hΔ : ∀ k, 0 ≤ Δ k)
    (hA : ∀ k, ‖(A k).adjoint‖ ≤ B) (hN : ∀ k, ‖N k‖ ≤ M)
    (hpart : ∀ k, n k = (A k).adjoint (r k) + N k (z k))
    (hnull : ∀ k, A k (N k (z k)) = 0) (hbal : ∀ k, ‖z k‖ ≤ J * ‖r k‖)
    (hrank : ∀ k, m * ‖c k‖ ≤ ‖(A k).adjoint (c k)‖)
    (hrank₂ : ∀ k, μ * ‖r k‖ ≤ ‖A k ((A k).adjoint (r k))‖)
    (hstep : ∀ k, ‖n k‖ ≤ ξ * Δ k)
    (hcauchy : ∀ k, κ * (‖(A k).adjoint (c k)‖ / ‖c k‖) *
      min (ξ * Δ k) (‖(A k).adjoint (c k)‖ / β) ≤
        sqpNormalModel (c k) (A k) 0 - sqpNormalModel (c k) (A k) (n k)) :
    ∃ a > 0, ∀ k, let d := sqpNormalModel (c k) (A k) 0 - sqpNormalModel (c k) (A k) (n k)
      a * ‖n k‖ ≤ d ∧ d ≤ ‖c k‖ := by
  let C := (B + M * J) * (2 / μ)
  have hC : 0 < C := by dsimp [C]; positivity
  let p := min 1 (m / (β * C))
  have hp : 0 < p := lt_min zero_lt_one (by positivity)
  refine ⟨κ * m * p, by positivity, fun k => ?_⟩
  have hc := hcauchy k
  simp only [sqpNormalModel, map_zero, add_zero] at hc ⊢
  refine ⟨?_, sub_le_self _ (norm_nonneg _)⟩
  have hd := (show 0 ≤ κ * (‖(A k).adjoint (c k)‖ / ‖c k‖) *
    min (ξ * Δ k) (‖(A k).adjoint (c k)‖ / β) by positivity [hΔ k]).trans hc
  have hAn : ‖A k (n k)‖ ≤ 2 * ‖c k‖ := by
    calc
      _ = ‖(c k + A k (n k)) - c k‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖c k + A k (n k)‖ + ‖c k‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hr := hrank₂ k
  rw [← add_zero (A k ((A k).adjoint (r k))), ← hnull k, ← map_add, ← hpart k] at hr
  have hr' : ‖r k‖ ≤ (2 / μ) * ‖c k‖ := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hμ).mpr (by linarith only [hr.trans hAn])
  have hn : ‖n k‖ ≤ C * ‖c k‖ := calc
    _ ≤ ‖(A k).adjoint (r k)‖ + ‖N k (z k)‖ := by
      nth_rw 1 [hpart k]
      exact norm_add_le _ _
    _ ≤ B * ‖r k‖ + M * (J * ‖r k‖) := add_le_add
      (((A k).adjoint.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _)))
      (((N k).le_opNorm _).trans
        (mul_le_mul (hN k) (hbal k) (norm_nonneg _) hM))
    _ = (B + M * J) * ‖r k‖ := by ring
    _ ≤ _ := by
      dsimp [C]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hr' (by positivity)
  by_cases hz : c k = 0
  · have hh : ‖n k‖ = 0 := le_antisymm (by simpa only [hz, norm_zero, mul_zero] using hn)
      (norm_nonneg _)
    simpa only [hh, mul_zero] using hd
  have hcp : 0 < ‖c k‖ := norm_pos_iff.mpr hz
  have hratio : m ≤ ‖(A k).adjoint (c k)‖ / ‖c k‖ := (le_div_iff₀ hcp).mpr (hrank k)
  have hmin : p * ‖n k‖ ≤ min (ξ * Δ k) (‖(A k).adjoint (c k)‖ / β) := by
    refine le_min ((mul_le_of_le_one_left (norm_nonneg _) (min_le_left _ _)).trans (hstep k)) ?_
    calc
      _ ≤ (m / (β * C)) * (C * ‖c k‖) :=
        mul_le_mul (min_le_right _ _) hn (norm_nonneg _) (by positivity)
      _ = (m * ‖c k‖) / β := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (hrank k) hβ.le
  rw [mul_assoc]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hratio hκ.le) hmin
    (mul_nonneg hp.le (norm_nonneg _)) (by positivity)).trans hc

/-- **Theorem 15.4.12** of [conn2000trust], the small-radius guarantee for the original trial. Let
$A, b > 0$, $C \ge 0$ and $\Delta_k > 0$. Suppose that $A \min\{q_k, b \Delta_k\} \le \delta_k$,
$|a_k - \delta_k| \le C \Delta_k^2$, $\eta_1 \delta_k \le v_k - v_{k+1}$ for $k \in S$, and that
$a_k / \delta_k \ge \eta_2$ implies $k \in S$, $\Delta_k \le \Delta_{k+1}$ and that no
correction is made at $k$. Then for every $\epsilon > 0$ there are $a', b', e, r > 0$ and $K$
such that for all $k \ge K$ with $q_k \ge \epsilon$:

* if $\Delta_k \le r$, then $k \in S$, $\Delta_k \le \Delta_{k+1}$ and no correction is made at
  $k$;
* if $k \in S$, then $a' \min\{e, b' \Delta_k\} \le v_k - v_{k+1}$.

At positive normal criticality a small radius makes the original trial very successful, so the
correction branch is not used. Normalizing the actual and the predicted decrease by the same
positive factor does not change the ratio.

**Correction.** The small-radius success and nonshrinkage guarantee is for the original trial and
excludes the correction in that branch. Successful merit reduction is expressed using the original
prediction. The full tangential limit is conditional on accepted-step variation.
-/
theorem sqp_normal_correction_progress {P : BTRParams}
    (q v Δ d actual : ℕ → ℝ) (S corrections : Set ℕ)
    {A b C : ℝ} (hA : 0 < A) (hb : 0 < b) (hC : 0 ≤ C) (hΔ : ∀ k, 0 < Δ k)
    (hpred : ∀ k, A * min (q k) (b * Δ k) ≤ d k)
    (herr : ∀ k, |actual k - d k| ≤ C * Δ k ^ 2)
    (hmerit : ∀ k ∈ S, P.η₁ * d k ≤ v k - v (k + 1))
    (hvery : ∀ k, P.η₂ ≤ actual k / d k →
      k ∈ S ∧ Δ k ≤ Δ (k + 1) ∧ k ∉ corrections) :
    ∀ ε > 0, ∃ (a b₀ e r : ℝ) (K : ℕ), 0 < a ∧ 0 < b₀ ∧ 0 < e ∧ 0 < r ∧
      ∀ k ≥ K, ε ≤ q k →
        (Δ k ≤ r → k ∈ S ∧ Δ k ≤ Δ (k + 1) ∧ k ∉ corrections) ∧
        (k ∈ S → a * min e (b₀ * Δ k) ≤ v k - v (k + 1)) := by
  intro ε hε
  let r := min (ε / b) ((1 - P.η₂) * A * b / (C + 1))
  refine ⟨P.η₁ * A, b, ε, r, 0, mul_pos P.eta₁_pos hA, hb, hε,
    lt_min (div_pos hε hb) (by positivity [P.eta₂_lt_one]), fun k _ hk => ⟨?_, ?_⟩⟩
  · intro hsmall
    have hlen : b * Δ k ≤ ε := by
      rw [mul_comm]
      exact (le_div_iff₀ hb).mp (hsmall.trans (min_le_left _ _))
    have hd := hpred k
    rw [min_eq_right (hlen.trans hk)] at hd
    have hp : 0 < d k := (mul_pos hA (mul_pos hb (hΔ k))).trans_le hd
    have hthreshold : C * Δ k ≤ (1 - P.η₂) * A * b := by
      have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp (hsmall.trans (min_le_right _ _))
      linarith only [hh, hΔ k]
    have he : |actual k - d k| ≤ (1 - P.η₂) * d k := by
      have h₁ := mul_le_mul_of_nonneg_right hthreshold (hΔ k).le
      have h₂ := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr P.eta₂_lt_one.le)
      exact (herr k).trans (by nlinarith only [h₁, h₂])
    apply hvery k
    apply (le_div_iff₀ hp).mpr
    linarith only [(abs_le.mp he).1]
  · intro hs
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left (min_le_min_right _ hk) hA.le).trans (hpred k))
      P.eta₁_pos.le).trans (hmerit k hs)

/-- **Theorem 15.4.12** of [conn2000trust], corrected composite-step convergence. Consider the tail
data of a run with a fixed penalty and the hypotheses of Theorem 15.4.10, a set of correction
iterations, normal criticality values $0 \le q_k \le B$, and normal merit values $v_{N,k} \ge 0$
that are nonincreasing. Let $L \ge 0$, $\tau_1 \ge 0$, $\tau_2 > 0$ and $\sigma_0 > 0$. Suppose
that the penalties $\sigma_k$ follow the penalty update with the constants $\tau_1, \tau_2$ and
required penalties bounded by $B_\sigma$ for $k \ge K_\sigma$, that $q_{k+1} = q_k$ for
$k \notin S$, that $q_k - q_{k+1} \le L \Delta_k$ for $k \in S$ without correction, and that the
small-radius guarantee of `ConnGouldToint.Chapter15.sqp_normal_correction_progress` holds for
$q$ and $v_N$. Then:

* $q_k \to 0$;
* there is $j \ge K_\sigma$ with $\sigma_j > 0$ and $\sigma_k = \sigma_j$ for all $k \ge j$;
* $\liminf_k u_k = 0$;
* if there is $M \ge 0$ with $u_k - u_{k+1} \le M \Delta_k$ for $k \in S$ and $u_{k+1} = u_k$
  for $k \notin S$, then $u_k \to 0$.

**Correction.** The accepted decrease may come from either the original or the corrected trial,
while the small-radius guarantee concerns the original trial. A correction cannot occur at small
radii and positive normal criticality, so bounded constraints control even an unrestricted
correction in the feasibility proof. Convergence of the full reduced gradient needs the separate
variation estimate on accepted steps.

**Correction.** The small-radius success and nonshrinkage guarantee is for the original trial and
excludes the correction in that branch. Successful merit reduction is expressed using the original
prediction. The full tangential limit is conditional on accepted-step variation.
-/
theorem theorem_15_4_12 {P : BTRParams} {u w q vN v Δ d actual σ required : ℕ → ℝ}
    {S corrections : Set ℕ} (run : SQPTangentialRun P u w v Δ d actual S)
    {κ b β C L B τ₁ τ₂ Bσ : ℝ} {Kσ : ℕ}
    (hκ : 0 < κ) (hb : 0 < b) (hβ : 0 < β) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 < τ₂) (hσ₀ : 0 < σ 0)
    (hupdate : ∀ k, σ (k + 1) = sqpPenaltyUpdate τ₁ τ₂ (required k) (σ k))
    (hrequired : ∀ k ≥ Kσ, required k ≤ Bσ)
    (hq : ∀ k, 0 ≤ q k ∧ q k ≤ B) (hvN : ∀ k, 0 ≤ vN k) (hmono : Antitone vN)
    (hstayQ : ∀ k ∉ S, q (k + 1) = q k)
    (hstandard : ∀ k ∈ S, k ∉ corrections → q k - q (k + 1) ≤ L * Δ k)
    (hnormal : ∀ ε > 0, ∃ (a b₀ e r : ℝ) (K : ℕ), 0 < a ∧ 0 < b₀ ∧ 0 < e ∧ 0 < r ∧
      ∀ k ≥ K, ε ≤ q k →
        (Δ k ≤ r → k ∈ S ∧ Δ k ≤ Δ (k + 1) ∧ k ∉ corrections) ∧
        (k ∈ S → a * min e (b₀ * Δ k) ≤ vN k - vN (k + 1)))
    (hpert : Filter.Tendsto (fun k => w k - u k) Filter.atTop (nhds 0))
    (hpred : ∀ᶠ k in Filter.atTop, κ * w k * min (b * Δ k) (w k / β) ≤ d k)
    (herr : ∀ᶠ k in Filter.atTop, |actual k - d k| ≤ C * (Δ k) ^ 2) :
    Filter.Tendsto q Filter.atTop (nhds 0) ∧
      (∃ j, Kσ ≤ j ∧ 0 < σ j ∧ ∀ k ≥ j, σ k = σ j) ∧
      Filter.liminf u Filter.atTop = 0 ∧
      ((∃ M ≥ 0, (∀ k ∈ S, u k - u (k + 1) ≤ M * Δ k) ∧
        (∀ k ∉ S, u (k + 1) = u k)) → Filter.Tendsto u Filter.atTop (nhds 0)) := by
  have hcontrol : HasRelaxedProgress q vN Δ S := by
    intro ε hε
    obtain ⟨a, b₀, e, r, K, ha, hb₀, he, hr, h⟩ := hnormal ε hε
    exact ⟨a, b₀, e, r, K, ha, hb₀, he, hr, fun k hk he' =>
      ⟨fun hΔ => ⟨((h k hk he').1 hΔ).1, ((h k hk he').1 hΔ).2.1⟩, (h k hk he').2⟩⟩
  refine ⟨?_, sqpPenaltyUpdate_eventually_constant hτ₁ hτ₂ hσ₀ hupdate hrequired,
    theorem_15_4_10 run hκ hb hβ hC hpert hpred herr, ?_⟩
  · refine tendsto_zero_of_relaxed_steps P.gamma₁_pos
      (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one
      (fun k => (hq k).1) hvN run.radius_pos hmono run.radius_lower
      (fun k hk => ⟨run.radius_rejected k hk, hstayQ k hk⟩) ?_ hcontrol
    intro ε hε
    obtain ⟨a, b₀, e, r, K, ha, hb₀, he, hr, h⟩ := hnormal ε hε
    refine ⟨max L (B / r), le_trans hL (le_max_left _ _), K, fun k hk hcrit hS => ?_⟩
    by_cases hcor : k ∈ corrections
    · have hΔ : r < Δ k := lt_of_not_ge fun hh => ((h k hk hcrit).1 hh).2.2 hcor
      have hscale : B ≤ (B / r) * Δ k := by
        calc
          B = (B / r) * r := (div_mul_cancel₀ _ hr.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hΔ.le (div_nonneg hB hr.le)
      exact (sub_le_self _ (hq (k + 1)).1).trans
        ((hq k).2.trans (hscale.trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (run.radius_pos k).le)))
    · exact (hstandard k hS hcor).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (run.radius_pos k).le)
  · rintro ⟨M, hM, hmove, hstay⟩
    exact theorem_15_4_11 run hκ hb hβ hC hpert hpred herr hM hmove hstay

/-- **Equations (15.4.105)–(15.4.111)** of [conn2000trust], the two cases in the proof of Theorem
15.4.16. Let $\mu_k$ be the curvatures, $N$ the set of normal-dominated iterations, $A, B > 0$,
$C \ge 0$ and $\Delta_k > 0$. Suppose that:

* $A \Delta_k \le \delta_k$ for $k \in N$, and $B (-\mu_k) \Delta_k^2 \le \delta_k$ for
  $k \notin N$;
* the original trial satisfies $|a_k - \delta_k| \le C \Delta_k^2$ for $k \in N$;
* for every $\epsilon > 0$ there is $r > 0$ such that the corrected trial satisfies
  $|a^c_k - \delta_k| \le \epsilon \Delta_k^2$ for all large $k \notin N$ with $\Delta_k \le r$;
* $\eta_1 \delta_k \le v_k - v_{k+1}$ for $k \in S$;
* $k \in S$ and $\Delta_k \le \Delta_{k+1}$ if $a_k / \delta_k \ge \eta_2$, or if $k \notin N$
  and $a_k / \delta_k \ge \eta_1$, or if $k \notin N$, $a_k / \delta_k < \eta_1$ and
  $a^c_k / \delta_k \ge \eta_2$.

Then for every $\delta > 0$ there are $a, r > 0$ such that for all large $k$ with
$\mu_k \le -\delta$: if $\Delta_k \le r$, then $k \in S$ and $\Delta_k \le \Delta_{k+1}$; and if
$k \in S$, then $a \min\{r^2, \Delta_k^2\} \le v_k - v_{k+1}$.

The clipped bound applies also when a successful trial has a radius above the threshold $r$.

**Correction.** Finite limit points must cover the eventual curvature values, and the normal and
corrected tangential branches must give uniform accepted decrease whenever curvature is bounded away
from zero on the negative side. The conclusion is stated as a nonnegative curvature limit at one
first-order index.
-/
theorem sqp_secondOrder_correction_progress {P : BTRParams}
    (μ v Δ d original corrected : ℕ → ℝ) (S normal : Set ℕ)
    {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 ≤ C)
    (hΔ : ∀ k, 0 < Δ k)
    (hN : ∀ k ∈ normal, A * Δ k ≤ d k)
    (hT : ∀ k ∉ normal, B * (-μ k) * Δ k ^ 2 ≤ d k)
    (herror : ∀ k ∈ normal, |original k - d k| ≤ C * Δ k ^ 2)
    (hcorrected : ∀ ε > 0, ∃ r > 0, ∀ᶠ k in Filter.atTop, k ∉ normal → Δ k ≤ r →
      |corrected k - d k| ≤ ε * Δ k ^ 2)
    (hmerit : ∀ k ∈ S, P.η₁ * d k ≤ v k - v (k + 1))
    (hvery : ∀ k, P.η₂ ≤ original k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1))
    (haccepted : ∀ k ∉ normal, P.η₁ ≤ original k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1))
    (hcor : ∀ k ∉ normal, original k / d k < P.η₁ →
      P.η₂ ≤ corrected k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1)) :
    ∀ δ > 0, ∃ a > 0, ∃ r > 0, ∀ᶠ k in Filter.atTop, μ k ≤ -δ →
      (Δ k ≤ r → k ∈ S ∧ Δ k ≤ Δ (k + 1)) ∧
      (k ∈ S → a * min (r ^ 2) (Δ k ^ 2) ≤ v k - v (k + 1)) := by
  intro δ hδ
  let e := (1 - P.η₂) * (B * δ)
  have he : 0 < e := mul_pos (sub_pos.mpr P.eta₂_lt_one) (mul_pos hB hδ)
  obtain ⟨r₀, hr₀, h0⟩ := hcorrected e he
  let r := min r₀ (min 1 ((1 - P.η₂) * A / (C + 1)))
  have hr : 0 < r := lt_min hr₀ (lt_min zero_lt_one (by positivity [P.eta₂_lt_one]))
  let a := min (P.η₁ * A) (P.η₁ * (B * δ))
  have ha : 0 < a := lt_min (mul_pos P.eta₁_pos hA) (mul_pos P.eta₁_pos (mul_pos hB hδ))
  refine ⟨a, ha, r, hr, ?_⟩
  filter_upwards [h0] with k hk hcurv
  have htang (hn : k ∉ normal) : B * δ * Δ k ^ 2 ≤ d k := by
    have hh : δ ≤ -μ k := by linarith only [hcurv]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hB.le)
      (sq_nonneg _)).trans (hT k hn)
  constructor
  · intro hsmall
    by_cases hn : k ∈ normal
    · have hp : 0 < d k := (mul_pos hA (hΔ k)).trans_le (hN k hn)
      have hthreshold : C * Δ k ≤ (1 - P.η₂) * A := by
        have hh := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
        have ht := (le_div_iff₀ (by positivity : 0 < C + 1)).mp hh
        linarith only [ht, hΔ k]
      have herror' : |original k - d k| ≤ (1 - P.η₂) * d k := by
        have h₁ := mul_le_mul_of_nonneg_right hthreshold (hΔ k).le
        have h₂ := mul_le_mul_of_nonneg_left (hN k hn) (sub_nonneg.mpr P.eta₂_lt_one.le)
        exact (herror k hn).trans (by nlinarith only [h₁, h₂])
      apply hvery k
      apply (le_div_iff₀ hp).mpr
      linarith only [(abs_le.mp herror').1]
    · by_cases hs : P.η₁ ≤ original k / d k
      · exact haccepted k hn hs
      · apply hcor k hn (lt_of_not_ge hs)
        have hp : 0 < d k := (mul_pos (mul_pos hB hδ) (sq_pos_of_pos (hΔ k))).trans_le (htang hn)
        have hh := mul_le_mul_of_nonneg_left (htang hn) (sub_nonneg.mpr P.eta₂_lt_one.le)
        have herror' : |corrected k - d k| ≤ (1 - P.η₂) * d k :=
          (hk hn (hsmall.trans (min_le_left _ _))).trans (by dsimp [e]; nlinarith only [hh])
        apply (le_div_iff₀ hp).mpr
        linarith only [(abs_le.mp herror').1]
  · intro hS
    apply le_trans _ (hmerit k hS)
    have hm : 0 ≤ min (r ^ 2) (Δ k ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    by_cases hn : k ∈ normal
    · have hmin : min (r ^ 2) (Δ k ^ 2) ≤ Δ k := by
        by_cases hd : Δ k ≤ 1
        · exact (min_le_right _ _).trans
            (by nlinarith only [mul_nonneg (hΔ k).le (sub_nonneg.mpr hd)])
        · have hr₁ : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
          have hlarge : 1 ≤ Δ k := le_of_not_ge hd
          have hsq : r ^ 2 ≤ r := by nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr₁)]
          exact (min_le_left _ _).trans (hsq.trans (hr₁.trans hlarge))
      have hh := mul_le_mul (min_le_left (P.η₁ * A) (P.η₁ * (B * δ))) hmin hm
        (mul_nonneg P.eta₁_pos.le hA.le)
      exact hh.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hN k hn) P.eta₁_pos.le)
    · have hh := mul_le_mul (min_le_right (P.η₁ * A) (P.η₁ * (B * δ)))
        (min_le_right (r ^ 2) (Δ k ^ 2)) hm (by positivity [P.eta₁_pos])
      exact hh.trans (by rw [mul_assoc]; exact
        mul_le_mul_of_nonneg_left (htang hn) P.eta₁_pos.le)

/-- **Theorem 15.4.16** of [conn2000trust], corrected. Let $\iota$ be a nonempty finite set of
cluster points, each first-order critical, with limiting curvatures $\mu^*_i$. Let $\gamma > 0$
and $0 \le \gamma_2 < 1$. Suppose that the cluster set controls the tail: for every $a$ with
$\mu^*_i < a$ for all $i$, the curvatures satisfy $\mu_k \le a$ for all large $k$. Suppose that
$v_k \ge 0$ is nonincreasing, $\Delta_k > 0$, $\gamma \Delta_k \le \Delta_{k+1}$,
$\Delta_{k+1} \le \gamma_2 \Delta_k$ for $k \notin S$, and that the conclusion of
`ConnGouldToint.Chapter15.sqp_secondOrder_correction_progress` holds. Then some cluster point
$i$ is first-order critical with $\mu^*_i \ge 0$.

**Correction.** Finiteness of the cluster set alone allows subsequences that escape; the cluster
set must control the tail, as relative compactness ensures. If every cluster point fails the
second-order test, the maximum cluster curvature gives a uniform negative margin.

The decrease hypotheses are the small-radius and accepted-step consequences of the two
correction cases of the algorithm.

**Correction.** Finite limit points must cover the eventual curvature values, and the normal and
corrected tangential branches must give uniform accepted decrease whenever curvature is bounded away
from zero on the negative side. The conclusion is stated as a nonnegative curvature limit at one
first-order index.
-/
theorem theorem_15_4_16 {ι : Type*} [Finite ι] [Nonempty ι]
    (firstOrder : ι → Prop) (curvLimit : ι → ℝ) (μ v Δ : ℕ → ℝ) (S : Set ℕ)
    {γ γ₂ : ℝ} (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hfirst : ∀ i, firstOrder i)
    (hcover : ∀ a : ℝ, (∀ i, curvLimit i < a) → ∀ᶠ k in Filter.atTop, μ k ≤ a)
    (hv : ∀ k, 0 ≤ v k) (hmono : Antitone v) (hΔ : ∀ k, 0 < Δ k)
    (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, Δ (k + 1) ≤ γ₂ * Δ k)
    (hprogress : ∀ δ > 0, ∃ a > 0, ∃ r > 0, ∀ᶠ k in Filter.atTop, μ k ≤ -δ →
      (Δ k ≤ r → k ∈ S ∧ Δ k ≤ Δ (k + 1)) ∧
      (k ∈ S → a * min (r ^ 2) (Δ k ^ 2) ≤ v k - v (k + 1))) :
    ∃ i, firstOrder i ∧ 0 ≤ curvLimit i := by
  classical
  have := Fintype.ofFinite ι
  by_contra! hn
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ curvLimit Finset.univ_nonempty
  let δ := -(curvLimit i) / 2
  have hi' := hn i (hfirst i)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmargin : ∀ᶠ k in Filter.atTop, μ k ≤ -δ :=
    hcover _ (fun j => (hmax j (Finset.mem_univ j)).trans_lt (by dsimp [δ]; linarith))
  obtain ⟨a, ha, r, hr, hp⟩ := hprogress δ hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hmargin.and hp)
  let R (k : ℕ) := Δ k ^ 2
  have hcontrol : HasRelaxedProgress (fun _ => (1 : ℝ)) v R S := by
    intro ε hε
    refine ⟨a, 1, r ^ 2, r ^ 2, N, ha, zero_lt_one, sq_pos_of_pos hr,
      sq_pos_of_pos hr, fun k hk _ => ?_⟩
    obtain ⟨hs, hd⟩ := (hN k hk).2 (hN k hk).1
    refine ⟨fun hR => ?_, fun hS => by simpa only [R, one_mul] using hd hS⟩
    have hR' : Δ k ≤ r := by
      by_contra! h
      exact (not_le_of_gt (pow_lt_pow_left₀ h hr.le (by decide : (2 : ℕ) ≠ 0))) hR
    obtain ⟨hS, hinc⟩ := hs hR'
    exact ⟨hS, pow_le_pow_left₀ (hΔ k).le hinc _⟩
  have hnext' (k : ℕ) : γ ^ 2 * R k ≤ R (k + 1) := by
    simpa only [R, mul_pow] using pow_le_pow_left₀ (mul_nonneg hγ.le (hΔ k).le) (hnext k) 2
  have hrej' (k : ℕ) (hk : k ∉ S) : R (k + 1) ≤ γ₂ ^ 2 * R k := by
    simpa only [R, mul_pow] using pow_le_pow_left₀ (hΔ (k + 1)).le (hrej k hk) 2
  obtain ⟨k, _, hk⟩ := relaxed_progress_frequently_small (sq_pos_of_pos hγ)
    (sq_nonneg γ₂) (by nlinarith only [mul_nonneg hγ₂ (sub_nonneg.mpr hγ₂'.le), hγ₂'])
    hv (fun k => sq_pos_of_pos (hΔ k)) hmono hnext' hrej' hcontrol 1 zero_lt_one 0
  exact (lt_irrefl (1 : ℝ)) hk

end ConnGouldToint.Chapter15
