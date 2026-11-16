/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Numlib.Optimization.ModelBased.RatioTest
import Mathlib.Analysis.Calculus.Deriv.Pow
import Numlib.Optimization.ModelBased.SupportDescent
import Numlib.Optimization.Optimality.Clarke

/-!
# Conn, Gould and Toint, Section 11.1: Steepest descent for a nonsmooth objective

This module formalizes Section 11.1 of [conn2000trust], which extends the trust-region method to a
locally Lipschitz objective $f$ on a real Hilbert space $E$. Smoothness is replaced by the Clarke
directional derivative $f^\circ(x; d)$ and the Clarke subdifferential $\partial f(x) = \{g : \langle
g, d \rangle \le f^\circ(x; d) \text{ for all } d\}$. By the support representation (3.1.4), the
least slope $\min_{\|d\| \le 1} f^\circ(x; d)$ equals $-\|g^*(x)\|$, where $g^*(x)$ is the
minimum-norm Clarke subgradient, and $d^*(x) = -g^*(x)/\|g^*(x)\|$ is a steepest-descent direction
(Lemma 11.1.1). Away from a Clarke stationary point, $\|g^*\|$ is bounded below nearby (Lemma
11.1.2). A family of models $m(x, p, \cdot)$ that matches $f$ in value (11.1.1) and in Clarke
derivative (11.1.2) then gives a uniform model decrease along $d^*$ (Lemma 11.1.3, Corollary
11.1.4), provided that the models satisfy a uniform one-sided first-order estimate.

The Clarke calculus is that of `Numlib.Optimization.Optimality.Clarke`, and the steepest-descent
calculation comes from `Numlib.Optimization.ModelBased.SupportDescent` and the metric projection
`bestApprox`.

## Main definitions

* Equation (11.1.1), `ConnGouldToint.Chapter11.modelValueMatches`: $m(x, p, 0) = f(x)$.
* Equation (11.1.2), `ConnGouldToint.Chapter11.modelDerivativeMatches`: the Clarke derivatives of
  the model at $0$ and of $f$ at $x$ agree.
* Equation (11.1.3), `ConnGouldToint.Chapter11.IsSteepestDirection`: $d$ minimizes
  $f^\circ(x; \cdot)$ on the closed unit ball.
* Lemma 11.1.1, `ConnGouldToint.Chapter11.steepestSlope`: the least slope
  $\inf_{\|d\| \le 1} f^\circ(x; d)$.
* Equation (11.1.4), `ConnGouldToint.Chapter11.minimumNormSubgradient`: the minimum-norm Clarke
  subgradient $g^*(x)$.
* Equation (11.1.6), `ConnGouldToint.Chapter11.steepestDirection`: the direction
  $d^*(x) = -g^*(x)/\|g^*(x)\|$.
* Equation (11.1.7), `ConnGouldToint.Chapter11.IsModelMinimizer`: a minimizer of the model in the
  ball of radius $\Delta$.
* Equation (11.1.8), `ConnGouldToint.Chapter11.IsCauchyLength` and
  `ConnGouldToint.Chapter11.cauchyStep`: the Cauchy step length along a direction, and the Cauchy
  step.
* Equation (11.1.9), `ConnGouldToint.Chapter11.HasSufficientCauchyDecrease`: a step decreases the
  model by a fraction of the Cauchy decrease.
* Equation (11.1.14), `ConnGouldToint.Chapter11.NonsmoothTRRun.HasLocalSufficientDecrease`:
  Assumption AA.1n.
* Equation (11.1.15), `ConnGouldToint.Chapter11.NonsmoothTRParams`: the parameters of Algorithm
  11.1.1.
* Equation (11.1.16), `ConnGouldToint.Chapter11.NonsmoothRadiusUpdate`: the radius update, with the
  expansion capped at $\Delta_{\max}$.
* Algorithm 11.1.1, `ConnGouldToint.Chapter11.NonsmoothTRRun`: an infinite run of the nonsmooth
  trust-region algorithm.
* Algorithm 11.1.1, Step 3, `ConnGouldToint.Chapter11.NonsmoothTRRun.pred` and
  `ConnGouldToint.Chapter11.NonsmoothTRRun.ratio`: the predicted decrease and the reduction ratio.

## Main results

* Lemma 11.1.1, `ConnGouldToint.Chapter11.lemma_11_1_1`: $g^*(x)$ is a minimum-norm Clarke
  subgradient, $d^*(x)$ is a steepest-descent direction, and the least slope is $-\|g^*(x)\|$.
* After Lemma 11.1.1, `ConnGouldToint.Chapter11.steepestSlope_eq_zero_iff`: the least slope is $0$
  if and only if $0 \in \partial f(x)$.
* Lemma 11.1.2, `ConnGouldToint.Chapter11.lemma_11_1_2`: if $0 \notin \partial f(x)$, then $\|g^*\|$
  is bounded below by a positive constant near $x$.
* Lemma 11.1.3, `ConnGouldToint.Chapter11.lemma_11_1_3`: near a nonstationary point, the model
  decreases by at least $\|g^*(y)\| t/2$ along $t d^*(y)$ for small $t$.
* Equation (11.1.8), `ConnGouldToint.Chapter11.exists_cauchyLength_of_strict_decrease`: a continuous
  model that decreases at some positive length has a Cauchy length.
* Corollary 11.1.4, `ConnGouldToint.Chapter11.corollary_11_1_4`: near a nonstationary point, every
  Cauchy step decreases the model by at least $\|g^*(y)\| \min\{\delta, \Delta\}/2$.
* Equation (11.1.16), `ConnGouldToint.Chapter11.printedNonsmoothExpansion_infeasible`: at the radius
  cap, the printed very-successful interval is empty.
* Equation (11.1.16), `ConnGouldToint.Chapter11.nonsmoothRadiusUpdate_exists`: the capped update
  always has a legal new radius.
* Counterexample to Lemma 11.1.3 and Corollary 11.1.4,
  `ConnGouldToint.Chapter11.oscillatoryModel_pointwiseSmooth`,
  `ConnGouldToint.Chapter11.oscillatoryModel_fails_uniform_decrease` and
  `ConnGouldToint.Chapter11.oscillatoryModel_fails_cauchy_decrease`: a smooth family of models that
  matches $f$ in value and derivative but gives no uniform decrease.

## Notation

* $f^\circ(x; d)$: the Clarke directional derivative `Optimization.clarkeDerivative f x d`.
* $\partial f(x)$: the Clarke subdifferential `Optimization.clarkeSubgradient f x`.
* $g^*(x)$ and $d^*(x)$: the minimum-norm subgradient and the steepest-descent direction.

## Implementation notes

* A model is a function $m : E \to P \to E \to \mathbb{R}$ of the base point $x$, a parameter $p$ in
  a type $P$, and the step $s$. The trust region is a Euclidean ball.
* The local Lipschitz hypothesis is a set $U$ in the neighborhood filter of $x$ and a constant $L$
  with $f$ $L$-Lipschitz on $U$.

## Deviations from the source

* **Equation (11.1.16)** (correction). The printed very-successful interval
  $[\gamma_3 \Delta, \Delta_{\max}]$ is empty when $\Delta = \Delta_{\max}$. The lower bound is
  capped at $\min\{\gamma_3 \Delta, \Delta_{\max}\}$. See
  `ConnGouldToint.Chapter11.printedNonsmoothExpansion_infeasible`.
* **Algorithm 11.1.1, Step 3** (reading). A zero predicted decrease gives the ratio $0$, so the step
  is rejected. See `ConnGouldToint.Chapter11.NonsmoothTRRun.ratio`.
* **Lemma 11.1.3** (correction). Pointwise smooth model matching does not give a uniform decrease.
  The statement assumes a uniform one-sided first-order model estimate near the nonstationary point.
  See `ConnGouldToint.Chapter11.oscillatoryModel_fails_uniform_decrease`.
* **Corollary 11.1.4** (correction). The same counterexample shows that pointwise matching does not
  give the uniform Cauchy decrease; the statement assumes the same uniform estimate. See
  `ConnGouldToint.Chapter11.oscillatoryModel_fails_cauchy_decrease`.
-/

open Filter Metric ConvexAnalysis Optimization
open scoped Topology RealInnerProductSpace

namespace ConnGouldToint.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (11.1.1)** of [conn2000trust]. A family of models $m(x, p, \cdot)$ **matches the
value** of $f$ if $m(x, p, 0) = f(x)$ for every base point $x$ and every parameter $p$. -/
def modelValueMatches {P : Type*} (f : E → ℝ) (m : E → P → E → ℝ) : Prop :=
  ∀ x p, m x p 0 = f x

/-- **Equation (11.1.2)** of [conn2000trust]. A family of models $m(x, p, \cdot)$ **matches the
Clarke derivative** of $f$ if
$$m(x, p, \cdot)^\circ(0; d) = f^\circ(x; d)$$
for every base point $x$, every parameter $p$ and every direction $d \neq 0$. -/
def modelDerivativeMatches {P : Type*} (f : E → ℝ) (m : E → P → E → ℝ) : Prop :=
  ∀ x p d, d ≠ 0 → clarkeDerivative (m x p) 0 d = clarkeDerivative f x d

/-- **Equation (11.1.3)** of [conn2000trust]. A vector $d$ is a **steepest-descent direction** of
$f$ at $x$ if $\|d\| \le 1$ and $d$ minimizes $f^\circ(x; \cdot)$ on the closed unit ball. -/
def IsSteepestDirection (f : E → ℝ) (x d : E) : Prop :=
  ‖d‖ ≤ 1 ∧ IsMinOn (clarkeDerivative f x) (closedBall 0 1) d

/-- **Lemma 11.1.1** of [conn2000trust]. The **least slope** of $f$ at $x$ is
$$\inf_{\|d\| \le 1} f^\circ(x; d).$$

The infimum is the real `sInf`, which is $0$ for a set that is not bounded below. For a locally
Lipschitz $f$ the set is bounded. -/
noncomputable def steepestSlope (f : E → ℝ) (x : E) : ℝ :=
  sInf (clarkeDerivative f x '' closedBall 0 1)

/-- **Equation (11.1.4)** of [conn2000trust]. The **minimum-norm subgradient** $g^*(x)$ is the
metric projection of $0$ onto the Clarke subdifferential $\partial f(x)$.

It is `bestApprox (clarkeSubgradient f x) 0`, which is $0$ when no nearest point exists. -/
noncomputable def minimumNormSubgradient (f : E → ℝ) (x : E) : E :=
  bestApprox (clarkeSubgradient f x) 0

/-- **Equation (11.1.6)** of [conn2000trust]. The selected **steepest-descent direction** is
$d^*(x) = -g^*(x)/\|g^*(x)\|$, and $d^*(x) = 0$ when $g^*(x) = 0$. -/
noncomputable def steepestDirection (f : E → ℝ) (x : E) : E :=
  negativeUnit (minimumNormSubgradient f x)

/-- **Equation (11.1.15)** of [conn2000trust]. The parameters of Algorithm 11.1.1 are real numbers
$\eta_1, \eta_2, \gamma_1, \gamma_2, \gamma_3$ and a radius cap $\Delta_{\max}$ with
$$0 < \eta_1 \le \eta_2 < 1, \qquad 1/\gamma_3 \le \gamma_1 \le \gamma_2 < 1 < \gamma_3, \qquad
  \Delta_{\max} > 0.$$
-/
structure NonsmoothTRParams where
  /-- The acceptance threshold $\eta_1$. -/
  η₁ : ℝ
  /-- The very-successful threshold $\eta_2$. -/
  η₂ : ℝ
  /-- The smaller contraction factor $\gamma_1$. -/
  γ₁ : ℝ
  /-- The larger contraction factor $\gamma_2$. -/
  γ₂ : ℝ
  /-- The expansion factor $\gamma_3$. -/
  γ₃ : ℝ
  /-- The radius cap $\Delta_{\max}$. -/
  Δmax : ℝ
  /-- The acceptance threshold is positive: $\eta_1 > 0$. -/
  eta₁_pos : 0 < η₁
  /-- The thresholds are ordered: $\eta_1 \le \eta_2$. -/
  eta₁_le_eta₂ : η₁ ≤ η₂
  /-- The very-successful threshold is less than one: $\eta_2 < 1$. -/
  eta₂_lt_one : η₂ < 1
  /-- The expansion factor is larger than one: $\gamma_3 > 1$. -/
  gamma₃_gt_one : 1 < γ₃
  /-- The contraction is at most the inverse expansion: $1/\gamma_3 \le \gamma_1$. -/
  inv_gamma₃_le_gamma₁ : 1 / γ₃ ≤ γ₁
  /-- The contraction factors are ordered: $\gamma_1 \le \gamma_2$. -/
  gamma₁_le_gamma₂ : γ₁ ≤ γ₂
  /-- The larger contraction factor is less than one: $\gamma_2 < 1$. -/
  gamma₂_lt_one : γ₂ < 1
  /-- The radius cap is positive: $\Delta_{\max} > 0$. -/
  radiusMax_pos : 0 < Δmax

/-- **Equation (11.1.16)** of [conn2000trust], corrected. A new radius $\Delta'$ is a **legal
update** of $\Delta$ for the ratio $\rho$ if
* $\min\{\gamma_3 \Delta, \Delta_{\max}\} \le \Delta' \le \Delta_{\max}$ when $\rho \ge \eta_2$;
* $\gamma_2 \Delta \le \Delta' \le \Delta$ when $\eta_1 \le \rho < \eta_2$;
* $\gamma_1 \Delta \le \Delta' \le \gamma_2 \Delta$ when $\rho < \eta_1$.

**Correction.** The source prints the very-successful interval
$[\gamma_3 \Delta, \Delta_{\max}]$. It is empty when $\gamma_3 \Delta > \Delta_{\max}$, for
example at $\Delta = \Delta_{\max}$ (see
`ConnGouldToint.Chapter11.printedNonsmoothExpansion_infeasible`). Capping the lower bound at
$\Delta_{\max}$ keeps the interval nonempty. -/
structure NonsmoothRadiusUpdate (P : NonsmoothTRParams) (ρ Δ Δ' : ℝ) : Prop where
  /-- A very successful iteration expands the radius to at least
  $\min\{\gamma_3 \Delta, \Delta_{\max}\}$ and at most $\Delta_{\max}$. -/
  very_successful : P.η₂ ≤ ρ → min (P.γ₃ * Δ) P.Δmax ≤ Δ' ∧ Δ' ≤ P.Δmax
  /-- A successful iteration keeps the radius in $[\gamma_2 \Delta, \Delta]$. -/
  successful : P.η₁ ≤ ρ → ρ < P.η₂ → P.γ₂ * Δ ≤ Δ' ∧ Δ' ≤ Δ
  /-- An unsuccessful iteration contracts the radius into $[\gamma_1 \Delta, \gamma_2 \Delta]$. -/
  unsuccessful : ρ < P.η₁ → P.γ₁ * Δ ≤ Δ' ∧ Δ' ≤ P.γ₂ * Δ

/-- **Equation (11.1.16)** of [conn2000trust], printed form. At the radius cap there is no $\Delta'$
with $\gamma_3 \Delta_{\max} \le \Delta' \le \Delta_{\max}$, so the printed very-successful
interval is empty. -/
theorem printedNonsmoothExpansion_infeasible (P : NonsmoothTRParams) :
    ¬ ∃ Δ' : ℝ, P.γ₃ * P.Δmax ≤ Δ' ∧ Δ' ≤ P.Δmax := by
  rintro ⟨Δ', hlo, hhi⟩
  have hgt := mul_lt_mul_of_pos_right P.gamma₃_gt_one P.radiusMax_pos
  rw [one_mul] at hgt
  exact hgt.not_ge (hlo.trans hhi)

/-- **Equation (11.1.16)** of [conn2000trust], corrected. For every ratio $\rho$ and every radius
$\Delta \ge 0$ there is a legal update $\Delta'$ of $\Delta$ for $\rho$. -/
theorem nonsmoothRadiusUpdate_exists (P : NonsmoothTRParams) (ρ Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ∃ Δ', NonsmoothRadiusUpdate P ρ Δ Δ' := by
  by_cases h₂ : P.η₂ ≤ ρ
  · refine ⟨min (P.γ₃ * Δ) P.Δmax, ⟨fun _ ↦ ⟨le_rfl, min_le_right _ _⟩, ?_, ?_⟩⟩
    · exact fun _ h ↦ (h.not_ge h₂).elim
    · exact fun h ↦ (h.not_ge (P.eta₁_le_eta₂.trans h₂)).elim
  by_cases h₁ : P.η₁ ≤ ρ
  · refine ⟨Δ, ⟨fun h ↦ (h₂ h).elim, fun _ _ ↦ ⟨?_, le_rfl⟩, ?_⟩⟩
    · exact mul_le_of_le_one_left hΔ P.gamma₂_lt_one.le
    · exact fun h ↦ (h.not_ge h₁).elim
  · refine ⟨P.γ₂ * Δ, ⟨?_, fun h _ ↦ (h₁ h).elim, fun _ ↦ ⟨?_, le_rfl⟩⟩⟩
    · exact fun h ↦ (h₁ (P.eta₁_le_eta₂.trans h)).elim
    · exact mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ hΔ

/-- **Algorithm 11.1.1** of [conn2000trust]. An infinite run of the nonsmooth trust-region
algorithm, for parameters (11.1.15), an objective $f$ and a family of models $m(x, p, \cdot)$,
consists of iterates $x_k$, model parameters $p_k$, steps $s_k$ and radii $\Delta_k$ with
$0 < \Delta_0 \le \Delta_{\max}$, $\|s_k\| \le \Delta_k$, the next iterate $x_k + s_k$ if the
ratio
$$\rho_k = \frac{f(x_k) - f(x_k + s_k)}{m(x_k, p_k, 0) - m(x_k, p_k, s_k)}$$
satisfies $\rho_k \ge \eta_1$ and $x_k$ otherwise, and the radius update (11.1.16) with
$\rho_k$.

The trust region is a Euclidean ball. The value and derivative matching and the
sufficient-decrease condition are not part of the run; the theorems that need them take them as
hypotheses. -/
structure NonsmoothTRRun {I : Type*} (P : NonsmoothTRParams) (f : E → ℝ)
    (m : E → I → E → ℝ) where
  /-- The iterates $x_k$. -/
  x : ℕ → E
  /-- The model parameters $p_k$. -/
  parameter : ℕ → I
  /-- The trial steps $s_k$. -/
  s : ℕ → E
  /-- The trust-region radii $\Delta_k$. -/
  Δ : ℕ → ℝ
  /-- The initial radius is positive: $\Delta_0 > 0$. -/
  radius_initial_pos : 0 < Δ 0
  /-- The initial radius is at most the cap: $\Delta_0 \le \Delta_{\max}$. -/
  radius_initial_le : Δ 0 ≤ P.Δmax
  /-- Each step lies in the trust region: $\|s_k\| \le \Delta_k$. -/
  step_bound : ∀ k, ‖s k‖ ≤ Δ k
  /-- The next iterate is $x_k + s_k$ if $\rho_k \ge \eta_1$, and $x_k$ otherwise. -/
  next_x : ∀ k, x (k + 1) =
    if P.η₁ ≤ reductionRatio f (x k) (s k)
      (m (x k) (parameter k) 0 - m (x k) (parameter k) (s k))
    then x k + s k else x k
  /-- The next radius is a legal update (11.1.16) of $\Delta_k$ for $\rho_k$. -/
  next_radius : ∀ k, NonsmoothRadiusUpdate P
    (reductionRatio f (x k) (s k) (m (x k) (parameter k) 0 - m (x k) (parameter k) (s k)))
    (Δ k) (Δ (k + 1))

namespace NonsmoothTRRun

variable {I : Type*} {P : NonsmoothTRParams} {f : E → ℝ} {m : E → I → E → ℝ}

/-- **Algorithm 11.1.1** of [conn2000trust], Step 3. The predicted decrease at iteration $k$ is
$m(x_k, p_k, 0) - m(x_k, p_k, s_k)$. -/
def pred (R : NonsmoothTRRun P f m) (k : ℕ) : ℝ :=
  m (R.x k) (R.parameter k) 0 - m (R.x k) (R.parameter k) (R.s k)

/-- **Algorithm 11.1.1** of [conn2000trust], Step 3. The reduction ratio at iteration $k$ is the
actual decrease $f(x_k) - f(x_k + s_k)$ divided by the predicted decrease.

**Reading.** The source does not say what happens when the predicted decrease is $0$. Lean
division by $0$ gives the ratio $0 < \eta_1$, so such a step is rejected. -/
noncomputable def ratio (R : NonsmoothTRRun P f m) (k : ℕ) : ℝ :=
  reductionRatio f (R.x k) (R.s k) (R.pred k)

/-- **Equation (11.1.14)** of [conn2000trust], Assumption AA.1n. A run has **local sufficient
decrease** near $x$ if there are $\varepsilon, \delta > 0$ and $\kappa \in (0, 1)$ such that
every iterate $x_k$ in the open ball of radius $\varepsilon$ about $x$ satisfies
$$\kappa \|g^*(x_k)\| \min\{\delta, \Delta_k\} \le m(x_k, p_k, 0) - m(x_k, p_k, s_k).$$
-/
def HasLocalSufficientDecrease (R : NonsmoothTRRun P f m) (x : E) : Prop :=
  ∃ ε δ κ : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < κ ∧ κ < 1 ∧
    ∀ k, R.x k ∈ ball x ε →
      κ * ‖minimumNormSubgradient f (R.x k)‖ * min δ (R.Δ k) ≤ R.pred k

end NonsmoothTRRun

variable [CompleteSpace E]

/-- **Lemma 11.1.1** of [conn2000trust], with formula (11.1.6). Let $E$ be a real Hilbert space, and
let $f : E \to \mathbb{R}$ be Lipschitz on a neighborhood of $x$. Then:
* $g^*(x) \in \partial f(x)$, and $\|g^*(x)\| \le \|z\|$ for every $z \in \partial f(x)$;
* $d^*(x)$ is a steepest-descent direction of $f$ at $x$;
* $f^\circ(x; d^*(x))$ equals the least slope;
* the least slope equals $-\|g^*(x)\|$.

The proof uses the support representation (3.1.4) of the Clarke derivative, $f^\circ(x; d) =
\max_{g \in \partial f(x)} \langle g, d \rangle$, and the metric projection onto the closed
convex set $\partial f(x)$. -/
theorem lemma_11_1_1 {f : E → ℝ} {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    (minimumNormSubgradient f x ∈ clarkeSubgradient f x ∧
      ∀ z ∈ clarkeSubgradient f x, ‖minimumNormSubgradient f x‖ ≤ ‖z‖) ∧
    IsSteepestDirection f x (steepestDirection f x) ∧
    clarkeDerivative f x (steepestDirection f x) = steepestSlope f x ∧
    steepestSlope f x = -‖minimumNormSubgradient f x‖ := by
  have h := hasClarkeSupport_of_lipschitzOnWith hU hL
  let K := clarkeSubgradient f x
  have hcl := isClosed_clarkeSubgradient f x
  have hco := convex_clarkeSubgradient f x
  have hg := isBestApprox_bestApprox_of_isClosed h.nonempty hcl hco (0 : E)
  have hval := supportFn_negativeUnit_bestApprox h.nonempty hcl hco
  change supportFn (innerₗ E) K (steepestDirection f x) =
    ((-‖minimumNormSubgradient f x‖ : ℝ) : EReal) at hval
  rw [h] at hval
  have hval' := EReal.coe_eq_coe_iff.mp hval
  have hlo (d : E) (hd : ‖d‖ ≤ 1) :
      -‖minimumNormSubgradient f x‖ ≤ clarkeDerivative f x d := by
    have hh := neg_norm_bestApprox_le_supportFn h.nonempty hcl hco hd
    rw [h] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hdir : ‖steepestDirection f x‖ ≤ 1 := norm_negativeUnit_le_one _
  have hleast : IsLeast (clarkeDerivative f x '' closedBall 0 1)
      (-‖minimumNormSubgradient f x‖) := by
    refine ⟨⟨steepestDirection f x, mem_closedBall_zero_iff.mpr hdir, hval'⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hlo d (mem_closedBall_zero_iff.mp hd)
  have hslope : steepestSlope f x = -‖minimumNormSubgradient f x‖ := hleast.csInf_eq
  refine ⟨⟨hg.1, fun z hz ↦ ?_⟩, ⟨hdir, isMinOn_iff.mpr fun d hd ↦ ?_⟩,
    hval'.trans hslope.symm, hslope⟩
  · simpa [minimumNormSubgradient] using hg.2 z hz
  · exact hval'.le.trans (hlo d (mem_closedBall_zero_iff.mp hd))

/-- **Section 11.1** of [conn2000trust], after Lemma 11.1.1. Let $f$ be Lipschitz on a neighborhood
of $x$. The least slope of $f$ at $x$ is $0$ if and only if $x$ is Clarke stationary,
$0 \in \partial f(x)$. -/
theorem steepestSlope_eq_zero_iff {f : E → ℝ} {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    steepestSlope f x = 0 ↔ (0 : E) ∈ clarkeSubgradient f x := by
  have h := hasClarkeSupport_of_lipschitzOnWith hU hL
  rw [(lemma_11_1_1 hU hL).2.2.2, neg_eq_zero, norm_eq_zero]
  constructor
  · intro hg
    exact hg ▸ (lemma_11_1_1 hU hL).1.1
  · intro hzero
    apply (bestApprox_eq_iff h.nonempty (isClosed_clarkeSubgradient f x)
      (convex_clarkeSubgradient f x)).mpr
    exact ⟨hzero, by simp⟩

/-- **Equation (11.1.7)** of [conn2000trust]. A step $s$ is a **model minimizer** in radius $\Delta$
if $\|s\| \le \Delta$ and $s$ minimizes $m$ on the closed ball of radius $\Delta$ about $0$. -/
def IsModelMinimizer (m : E → ℝ) (Δ : ℝ) (s : E) : Prop :=
  ‖s‖ ≤ Δ ∧ IsMinOn m (closedBall 0 Δ) s

omit [CompleteSpace E] in
/-- **Equation (11.1.8)** of [conn2000trust]. A number $t$ is a **Cauchy length** of the model $m$
along $d$ in radius $\Delta$ if $t \in (0, \Delta]$ and $t$ minimizes $u \mapsto m(u d)$ on
$(0, \Delta]$. -/
def IsCauchyLength (m : E → ℝ) (d : E) (Δ t : ℝ) : Prop :=
  t ∈ Set.Ioc 0 Δ ∧ IsMinOn (fun u : ℝ ↦ m (u • d)) (Set.Ioc 0 Δ) t

/-- **Equation (11.1.8)** of [conn2000trust]. The **Cauchy step** of length $t$ along $d$ is $t d$.
-/
def cauchyStep (t : ℝ) (d : E) : E := t • d

/-- **Equation (11.1.9)** of [conn2000trust]. A step $s$ has **sufficient Cauchy decrease** relative
to the Cauchy step $s_C$ in radius $\Delta$ with constant $\kappa$ if $\|s\| \le \Delta$ and
$$\kappa \bigl(m(0) - m(s_C)\bigr) \le m(0) - m(s).$$
-/
def HasSufficientCauchyDecrease (m : E → ℝ) (s sC : E) (Δ κ : ℝ) : Prop :=
  ‖s‖ ≤ Δ ∧ κ * (m 0 - m sC) ≤ m 0 - m s

/-- **Lemma 11.1.2** of [conn2000trust]. Let $E$ be a real Hilbert space, and let
$f : E \to \mathbb{R}$ be Lipschitz on a neighborhood of $x$ with $0 \notin \partial f(x)$. Then
there are $\varepsilon, \kappa > 0$ with $\|g^*(y)\| \ge \kappa$ for every $y$ in the open ball
of radius $\varepsilon$ about $x$.

The proof fixes one strict descent direction at $x$ and uses the upper semicontinuity of its
Clarke derivative. -/
theorem lemma_11_1_2 {f : E → ℝ} {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hx : (0 : E) ∉ clarkeSubgradient f x) :
    ∃ ε κ : ℝ, 0 < ε ∧ 0 < κ ∧ ∀ y ∈ ball x ε, κ ≤ ‖minimumNormSubgradient f y‖ := by
  have h := lemma_11_1_1 hU hL
  let d := steepestDirection f x
  let κ := ‖minimumNormSubgradient f x‖ / 2
  have hg : minimumNormSubgradient f x ≠ 0 := fun he ↦ hx (he ▸ h.1.1)
  have hκ : 0 < κ := half_pos (norm_pos_iff.mpr hg)
  have hstrict : clarkeDerivative f x d < -κ := by
    change clarkeDerivative f x (steepestDirection f x) < -κ
    rw [h.2.2.1, h.2.2.2]
    dsimp [κ]
    linarith [norm_pos_iff.mpr hg]
  obtain ⟨V, hVU, hV, hxV⟩ := _root_.mem_nhds_iff.mp
    ((eventually_clarkeDerivative_le_of_lt hU hL hstrict).and hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  refine ⟨ε, κ, hε, hκ, fun y hy ↦ ?_⟩
  have hyV := hball hy
  have hUy : U ∈ 𝓝 y := Filter.mem_of_superset (hV.mem_nhds hyV) fun z hz ↦ (hVU hz).2
  have hyL := lemma_11_1_1 hUy hL
  have hySlope := isMinOn_iff.mp hyL.2.1.2 d (mem_closedBall_zero_iff.mpr h.2.1.1)
  rw [hyL.2.2.1, hyL.2.2.2] at hySlope
  linarith [(hVU hyV).1]

/-- **Section 11.1** of [conn2000trust], uniform one-sided model estimate. A family of models
$m(y, p, \cdot)$ satisfies the **uniform upper approximation** at $x$ if for every $\eta > 0$
there are $\varepsilon, \delta > 0$ such that
$$m(y, p, t d) - m(y, p, 0) \le t \bigl(m(y, p, \cdot)^\circ(0; d) + \eta\bigr)$$
for every $y$ in the open ball of radius $\varepsilon$ about $x$, every parameter $p$, every $d$
with $\|d\| \le 1$ and every $t \in (0, \delta]$.

This is the hypothesis that the corrected Lemma 11.1.3 and Corollary 11.1.4 add. -/
def UniformModelUpperApproximationAt {P : Type*} (m : E → P → E → ℝ) (x : E) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
    ∀ y ∈ ball x ε, ∀ (p : P) (d : E), ‖d‖ ≤ 1 → ∀ t ∈ Set.Ioc 0 δ,
      m y p (t • d) - m y p 0 ≤ t * (clarkeDerivative (m y p) 0 d + η)

/-- **Lemma 11.1.3** of [conn2000trust]. Let $E$ be a real Hilbert space, let $f : E \to \mathbb{R}$
be Lipschitz on a neighborhood of $x$ with $0 \notin \partial f(x)$, and let the models match
the Clarke derivative of $f$ (11.1.2) and satisfy the uniform upper approximation at $x$. Then
there are $\varepsilon, \delta > 0$ such that
$$\frac{\|g^*(y)\| t}{2} \le m(y, p, 0) - m(y, p, t d^*(y))$$
for every $y$ in the open ball of radius $\varepsilon$ about $x$, every parameter $p$ and every
$t \in [0, \delta]$.

**Correction.** The source derives the uniform decrease from the pointwise smoothness of the
models and the matching conditions. Pointwise regularity controls only a fixed model as the step
tends to zero, not varying parameters and base points. The model family
`ConnGouldToint.Chapter11.oscillatoryModel` is smooth and matches $f$, but fails the conclusion
(`ConnGouldToint.Chapter11.oscillatoryModel_fails_uniform_decrease`). The statement here assumes
the uniform estimate `ConnGouldToint.Chapter11.UniformModelUpperApproximationAt`. -/
theorem lemma_11_1_3 {P : Type*} {f : E → ℝ} {m : E → P → E → ℝ}
    {x : E} {U : Set E} {L : NNReal} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hx : (0 : E) ∉ clarkeSubgradient f x) (hm : modelDerivativeMatches f m)
    (happrox : UniformModelUpperApproximationAt m x) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ y ∈ ball x ε, ∀ (p : P) (t : ℝ), 0 ≤ t → t ≤ δ →
      ‖minimumNormSubgradient f y‖ * t / 2 ≤ m y p 0 - m y p (t • steepestDirection f y) := by
  obtain ⟨ε₀, κ, hε₀, hκ, hbound⟩ := lemma_11_1_2 hU hL hx
  obtain ⟨ε₁, δ, hε₁, hδ, happ⟩ := happrox (κ / 2) (half_pos hκ)
  obtain ⟨V, hVU, hV, hxV⟩ := _root_.mem_nhds_iff.mp hU
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  refine ⟨min ε₀ (min ε₁ ε₂), δ, lt_min hε₀ (lt_min hε₁ hε₂), hδ, ?_⟩
  intro y hy p t ht htδ
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hy₀ := ball_subset_ball (min_le_left ε₀ _) hy
  have hy₁ := ball_subset_ball ((min_le_right ε₀ _).trans (min_le_left ε₁ ε₂)) hy
  have hy₂ := ball_subset_ball ((min_le_right ε₀ _).trans (min_le_right ε₁ ε₂)) hy
  have hUy : U ∈ 𝓝 y := Filter.mem_of_superset (hV.mem_nhds (hball hy₂)) hVU
  have h := lemma_11_1_1 hUy hL
  have hg := hbound y hy₀
  have hdir : steepestDirection f y ≠ 0 := by
    have hn : 0 < ‖minimumNormSubgradient f y‖ := hκ.trans_le hg
    exact smul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hn.ne')) (norm_pos_iff.mp hn)
  have hdecr := happ y hy₁ p _ h.2.1.1 t ⟨ht, htδ⟩
  rw [hm y p _ hdir, h.2.2.1, h.2.2.2] at hdecr
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hg)]

omit [CompleteSpace E] in
/-- **Equation (11.1.8)** of [conn2000trust], existence of a Cauchy length. Let
$m : E \to \mathbb{R}$ be continuous, let $t_0 \in (0, \Delta]$, and let $m(t_0 d) < m(0)$. Then
$m$ has a Cauchy length along $d$ in radius $\Delta$.

The decrease at $t_0$ keeps the minimum away from the open end $0$ of the interval
$(0, \Delta]$. -/
theorem exists_cauchyLength_of_strict_decrease {m : E → ℝ} {d : E} {Δ t₀ : ℝ}
    (hm : Continuous m) (ht₀ : t₀ ∈ Set.Ioc 0 Δ) (hdec : m (t₀ • d) < m 0) :
    ∃ t, IsCauchyLength m d Δ t := by
  have ht₀' : t₀ ∈ Set.Icc 0 Δ := ⟨ht₀.1.le, ht₀.2⟩
  have hc : Continuous (fun t : ℝ ↦ m (t • d)) := hm.comp (continuous_id.smul continuous_const)
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨t₀, ht₀'⟩ hc.continuousOn
  have htpos : 0 < t := by
    by_contra! hn
    have hz := le_antisymm hn ht.1
    have h := isMinOn_iff.mp hmin t₀ ht₀'
    rw [hz, zero_smul] at h
    exact hdec.not_ge h
  refine ⟨t, ⟨htpos, ht.2⟩, isMinOn_iff.mpr fun u hu ↦ ?_⟩
  exact isMinOn_iff.mp hmin u ⟨hu.1.le, hu.2⟩

/-- **Corollary 11.1.4** of [conn2000trust]. Under the hypotheses of Lemma 11.1.3, assume also that
each model $m(y, p, \cdot)$ is continuous, and let $\Delta > 0$. Then there are
$\varepsilon, \delta > 0$ such that for every $y$ in the open ball of radius $\varepsilon$ about
$x$ and every parameter $p$, a Cauchy length along $d^*(y)$ in radius $\Delta$ exists, and every
such length $t$ satisfies
$$\frac{\|g^*(y)\| \min\{\delta, \Delta\}}{2} \le m(y, p, 0) - m(y, p, t d^*(y)).$$

**Correction.** As for Lemma 11.1.3, pointwise matching does not give this uniform decrease
(`ConnGouldToint.Chapter11.oscillatoryModel_fails_cauchy_decrease`), and the statement assumes
the uniform upper approximation.

The proof compares the Cauchy length with the trial length $\min\{\delta, \Delta\}$ of Lemma
11.1.3. -/
theorem corollary_11_1_4 {P : Type*} {f : E → ℝ} {m : E → P → E → ℝ}
    {x : E} {U : Set E} {L : NNReal} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hx : (0 : E) ∉ clarkeSubgradient f x) (hm : modelDerivativeMatches f m)
    (happrox : UniformModelUpperApproximationAt m x) (hcont : ∀ y p, Continuous (m y p))
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ y ∈ ball x ε, ∀ p : P,
      (∃ t, IsCauchyLength (m y p) (steepestDirection f y) Δ t) ∧
      ∀ t, IsCauchyLength (m y p) (steepestDirection f y) Δ t →
        ‖minimumNormSubgradient f y‖ * min δ Δ / 2 ≤
          m y p 0 - m y p (cauchyStep t (steepestDirection f y)) := by
  obtain ⟨ε, δ, hε, hδ, h⟩ := lemma_11_1_3 hU hL hx hm happrox
  obtain ⟨ε₀, κ, hε₀, hκ, hbound⟩ := lemma_11_1_2 hU hL hx
  refine ⟨min ε ε₀, δ, lt_min hε hε₀, hδ, fun y hy p ↦ ?_⟩
  have hyε := ball_subset_ball (min_le_left ε ε₀) hy
  have hyε₀ := ball_subset_ball (min_le_right ε ε₀) hy
  have hr := lt_min hδ hΔ
  have htrial := h y hyε p (min δ Δ) hr.le (min_le_left _ _)
  have hpos : 0 < ‖minimumNormSubgradient f y‖ * min δ Δ / 2 :=
    half_pos (mul_pos (hκ.trans_le (hbound y hyε₀)) hr)
  refine ⟨exists_cauchyLength_of_strict_decrease (hcont y p) ⟨hr, min_le_right _ _⟩
    (sub_pos.mp (hpos.trans_le htrial)), fun t ht ↦ ?_⟩
  have hmin := isMinOn_iff.mp ht.2 (min δ Δ) ⟨hr, min_le_right _ _⟩
  exact htrial.trans (sub_le_sub_left hmin _)

/-! ### Failure of uniformity for pointwise smooth models -/

/-- The objective $f(x) = x^2 - x$ on $\mathbb{R}$ of the counterexamples. It is smooth and bounded
below by $-1/4$. -/
noncomputable def oscillatoryObjective (x : ℝ) : ℝ := x ^ 2 - x

/-- **Section 11.1** of [conn2000trust], counterexample to Lemma 11.1.3 and Corollary 11.1.4. For
$x \in \mathbb{R}$ and a frequency $p > 0$, the model is
$$m(x, p, s) = f(x) + (2x - 1) \frac{\sin(p s)}{p},$$
with $f(x) = x^2 - x$. Each model has the derivative $2x - 1 = f'(x)$ at $s = 0$, but at the
base point $0$ the largest available decrease is at most $1/p$. -/
noncomputable def oscillatoryModel (x : ℝ) (p : {p : ℝ // 0 < p}) (s : ℝ) : ℝ :=
  oscillatoryObjective x + (2 * x - 1) * (Real.sin (p.val * s) / p.val)

private theorem oscillatoryObjective_strict (x : ℝ) :
    HasStrictDerivAt oscillatoryObjective (2 * x - 1) x := by
  unfold oscillatoryObjective
  convert (hasStrictDerivAt_pow 2 x).sub (hasStrictDerivAt_id x) using 1
  · rfl
  · ring

private theorem oscillatoryModel_strict (x : ℝ) (p : {p : ℝ // 0 < p}) :
    HasStrictDerivAt (oscillatoryModel x p) (2 * x - 1) 0 := by
  have hs := (((hasStrictDerivAt_id (0 : ℝ)).const_mul p.val).sin.div_const p.val)
  have hs' : HasStrictDerivAt (fun s : ℝ ↦ Real.sin (p.val * s) / p.val) 1 0 := by
    simpa [p.prop.ne'] using hs
  change HasStrictDerivAt
    (fun s : ℝ ↦ oscillatoryObjective x + (2 * x - 1) * (Real.sin (p.val * s) / p.val))
    (2 * x - 1) 0
  rw [hasStrictDerivAt_const_add_iff]
  simpa only [mul_one] using hs'.const_mul (2 * x - 1)

/-- **Section 11.1** of [conn2000trust], counterexample to Lemma 11.1.3 and Corollary 11.1.4. The
objective $f(x) = x^2 - x$ is infinitely differentiable with $f \ge -1/4$, each model
$m(x, p, \cdot)$ is infinitely differentiable, for every fixed step $s$ the model value is
continuous in $(x, p)$, and the family matches $f$ in value (11.1.1) and in Clarke derivative
(11.1.2). -/
theorem oscillatoryModel_pointwiseSmooth :
    ContDiff ℝ ⊤ oscillatoryObjective ∧ (∀ x, -(1 / 4 : ℝ) ≤ oscillatoryObjective x) ∧
    (∀ x p, ContDiff ℝ ⊤ (oscillatoryModel x p)) ∧
    (∀ s, Continuous (fun xp : ℝ × {p : ℝ // 0 < p} ↦ oscillatoryModel xp.1 xp.2 s)) ∧
    modelValueMatches oscillatoryObjective oscillatoryModel ∧
    modelDerivativeMatches oscillatoryObjective oscillatoryModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold oscillatoryObjective
    fun_prop
  · intro x
    unfold oscillatoryObjective
    nlinarith [sq_nonneg (x - 1 / 2)]
  · intro x p
    unfold oscillatoryModel
    fun_prop
  · intro s
    unfold oscillatoryModel oscillatoryObjective
    have hp : Continuous (fun xp : ℝ × {p : ℝ // 0 < p} ↦ xp.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hs : Continuous (fun xp : ℝ × {p : ℝ // 0 < p} ↦
        Real.sin (xp.2.val * s) / xp.2.val) :=
      (Real.continuous_sin.comp (hp.mul continuous_const)).div hp fun xp ↦ xp.2.prop.ne'
    fun_prop
  · intro x p
    simp [oscillatoryModel]
  · intro x p d _
    rw [clarkeDerivative_eq_of_hasStrictFDerivAt (oscillatoryModel_strict x p).hasStrictFDerivAt,
      clarkeDerivative_eq_of_hasStrictFDerivAt (oscillatoryObjective_strict x).hasStrictFDerivAt]

private theorem oscillatoryObjective_subgradient_zero :
    clarkeSubgradient oscillatoryObjective 0 = {(-1 : ℝ)} := by
  have hf : HasStrictDerivAt oscillatoryObjective (-1) 0 := by
    simpa using oscillatoryObjective_strict 0
  have h (d : ℝ) : clarkeDerivative oscillatoryObjective 0 d = -d := by
    rw [clarkeDerivative_eq_of_hasStrictFDerivAt hf.hasStrictFDerivAt]
    simp
  ext g
  change (∀ d : ℝ, inner ℝ g d ≤ clarkeDerivative oscillatoryObjective 0 d) ↔ g = -1
  simp only [h, RCLike.inner_apply, conj_trivial]
  constructor
  · intro hg
    have hp := hg 1
    have hm := hg (-1)
    linarith
  · rintro rfl d
    linarith

/-- At $0$, the objective $f(x) = x^2 - x$ has the minimum-norm Clarke subgradient $g^*(0) = -1$. -/
theorem oscillatoryObjective_minimumNorm :
    minimumNormSubgradient oscillatoryObjective 0 = -1 := by
  unfold minimumNormSubgradient
  rw [oscillatoryObjective_subgradient_zero]
  apply (bestApprox_eq_iff ⟨-1, by simp⟩ isClosed_singleton (convex_singleton _)).mpr
  simp

private theorem oscillatoryObjective_steepest :
    steepestDirection oscillatoryObjective 0 = 1 := by
  simp [steepestDirection, oscillatoryObjective_minimumNorm, negativeUnit]

/-- **Lemma 11.1.3** of [conn2000trust], counterexample to the printed statement. For every
$\delta > 0$ there are a frequency $p > 0$ and a step length $t \in (0, \delta]$ such that
$$m(0, p, 0) - m(0, p, t d^*(0)) < \frac{\|g^*(0)\| t}{2}.$$
So no uniform $\delta$ exists for the family `ConnGouldToint.Chapter11.oscillatoryModel`; the
model decrease can even be zero. -/
theorem oscillatoryModel_fails_uniform_decrease {δ : ℝ} (hδ : 0 < δ) :
    ∃ (p : {p : ℝ // 0 < p}) (t : ℝ), 0 < t ∧ t ≤ δ ∧
      oscillatoryModel 0 p 0 - oscillatoryModel 0 p
        (t • steepestDirection oscillatoryObjective 0) <
          ‖minimumNormSubgradient oscillatoryObjective 0‖ * t / 2 := by
  let p : {p : ℝ // 0 < p} := ⟨Real.pi / δ, div_pos Real.pi_pos hδ⟩
  refine ⟨p, δ, hδ, le_rfl, ?_⟩
  have hp : p.val * δ = Real.pi := div_mul_cancel₀ _ hδ.ne'
  simpa [oscillatoryModel, oscillatoryObjective_minimumNorm, oscillatoryObjective_steepest,
    smul_eq_mul, hp] using half_pos hδ

/-- **Corollary 11.1.4** of [conn2000trust], counterexample to the printed statement at the radius
$1$. For every $\delta > 0$ there are a frequency $p > 0$ and a Cauchy length $t$ of
$m(0, p, \cdot)$ along $d^*(0)$ in radius $1$ such that
$$m(0, p, 0) - m(0, p, t d^*(0)) < \frac{\|g^*(0)\| \min\{\delta, 1\}}{2}.$$
An exact Cauchy step exists, but its decrease tends to zero as the frequency grows. -/
theorem oscillatoryModel_fails_cauchy_decrease {δ : ℝ} (hδ : 0 < δ) :
    ∃ (p : {p : ℝ // 0 < p}) (t : ℝ),
      IsCauchyLength (oscillatoryModel 0 p) (steepestDirection oscillatoryObjective 0) 1 t ∧
      oscillatoryModel 0 p 0 - oscillatoryModel 0 p
        (cauchyStep t (steepestDirection oscillatoryObjective 0)) <
          ‖minimumNormSubgradient oscillatoryObjective 0‖ * min δ 1 / 2 := by
  let r := min δ (1 : ℝ)
  have hr : 0 < r := lt_min hδ zero_lt_one
  obtain ⟨a, ha⟩ := exists_gt (max Real.pi (2 / r))
  have haπ : Real.pi < a := (le_max_left _ _).trans_lt ha
  have ha' : 0 < a := Real.pi_pos.trans haπ
  let p : {p : ℝ // 0 < p} := ⟨a, ha'⟩
  let t := (Real.pi / 2) / a
  have ht : 0 < t := div_pos (half_pos Real.pi_pos) ha'
  have hta : a * t = Real.pi / 2 := by
    dsimp [t]
    rw [mul_comm, div_mul_cancel₀ _ ha'.ne']
  have ht₁ : t ≤ 1 := (div_le_one ha').mpr (by linarith [Real.pi_pos])
  refine ⟨p, t, ⟨⟨ht, ht₁⟩, ?_⟩, ?_⟩
  · apply isMinOn_iff.mpr
    intro u _
    have hsin := div_le_div_of_nonneg_right (Real.sin_le_one (a * u)) ha'.le
    simp only [oscillatoryObjective_steepest, smul_eq_mul, mul_one, oscillatoryModel]
    change oscillatoryObjective 0 + (2 * 0 - 1) * (Real.sin (a * t) / a) ≤
      oscillatoryObjective 0 + (2 * 0 - 1) * (Real.sin (a * u) / a)
    rw [hta, Real.sin_pi_div_two]
    linarith
  · have har : 2 / r < a := (le_max_right _ _).trans_lt ha
    have har' := (div_lt_iff₀ hr).mp har
    have hb : 1 / a < r / 2 := (div_lt_iff₀ ha').mpr (by linarith)
    simpa [oscillatoryModel, oscillatoryObjective_minimumNorm, oscillatoryObjective_steepest,
      cauchyStep, smul_eq_mul, p, hta, r] using hb

end ConnGouldToint.Chapter11
