/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpEDA
import NumlibSurface.CartisGouldToint.Chapter13.Section01

/-!
# Cartis, Gould and Toint, Section 13.3: Inexact algorithms using explicit dynamic accuracy

This module formalizes Section 13.3 of [cartis2022evaluation]. The section studies the trust-region
method TRqEDA (Algorithm 13.3.1) and the adaptive-regularization method ARqpEDA (Algorithm 13.3.2).
In these methods the derivative errors are enforceable and normalized, with $\kappa_{\nabla,i} = 1$
in (13.3.3)–(13.3.4):
$$\|\bar\nabla^i f(x_k) - \nabla^i f(x_k)\| \le h_{k,i}.$$
The function values are also inexact, $|\bar f(x_k) - f(x_k)| \le h_{k,0}$ and
$|\bar f(x_k + s_k) - f(x_k + s_k)| \le h_{k,0}$ (13.3.1)–(13.3.2), with a requested accuracy
$h_{k,0}$ that the method controls. Unlike the methods of Section 13.1, these methods have a
termination test, and the test certifies approximate optimality. Theorem 13.3.4 bounds the
evaluations of TRqEDA by $O(\epsilon_{\min}^{-(q+1)})$, and Theorem 13.3.8 bounds those of ARqpEDA
by $O(\max_j \epsilon_j^{-\pi_j})$, the orders of Section 13.1.

The notation is that of Section 13.1 (`NumlibSurface.CartisGouldToint.Chapter13.Section01`). The
proofs specialize `Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqEDA` and
`Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpEDA`.

## Main definitions

* Algorithm 13.3.1, `CartisGouldToint.Chapter13.algorithm_13_3_1`: a run of TRqEDA.
* Algorithm 13.3.2, `CartisGouldToint.Chapter13.algorithm_13_3_2`: a run of ARqpEDA.

## Main results

* Lemma 13.3.1, `CartisGouldToint.Chapter13.lemma_13_3_1`: a trial iteration of TRqEDA with a small
  radius is very successful.
* Lemma 13.3.2, `CartisGouldToint.Chapter13.lemma_13_3_2`: the predicted decrease and the decrease
  of $f$ at the trial and successful iterations of TRqEDA are at least of order
  $\epsilon_{\min}^{q+1}$.
* Lemma 13.3.3, `CartisGouldToint.Chapter13.lemma_13_3_3_i`,
  `CartisGouldToint.Chapter13.lemma_13_3_3_ii`: termination of TRqEDA certifies approximate
  optimality, and small accuracies make TRqEDA terminate.
* Theorem 13.3.4, `CartisGouldToint.Chapter13.theorem_13_3_4`: TRqEDA terminates at an approximate
  minimizer after $O(\epsilon_{\min}^{-(q+1)})$ function values and derivative estimates.
* Lemma 13.3.5, `CartisGouldToint.Chapter13.lemma_13_3_5`: the regularization parameters of ARqpEDA
  stay below $\sigma_{\max}$.
* Lemma 13.3.6, `CartisGouldToint.Chapter13.lemma_13_3_6_i`,
  `CartisGouldToint.Chapter13.lemma_13_3_6_ii`: termination of ARqpEDA certifies approximate
  optimality, and small accuracies make ARqpEDA terminate.
* Lemma 13.3.7, `CartisGouldToint.Chapter13.lemma_13_3_7`: the predicted decrease and the decrease
  of $f$ at the successful iterations of ARqpEDA that are not followed by an accuracy-improving
  iteration are at least of order $\min_j \epsilon_j^{\pi_j}$. The radius inequality that replaces
  Lemmas 13.1.16–13.1.17 is `CartisGouldToint.Chapter13.eda_radius_inequality`.
* Theorem 13.3.8, `CartisGouldToint.Chapter13.theorem_13_3_8_i`,
  `CartisGouldToint.Chapter13.theorem_13_3_8_ii`: ARqpEDA terminates at an approximate minimizer
  after $O(\max_j \epsilon_j^{-\pi_j})$ function values and derivative estimates, for $q \le 2$ and
  for $q > 2$. The common argument is `CartisGouldToint.Chapter13.arqpEDA_complexity`.
* Existence of runs, `CartisGouldToint.Chapter13.exists_algorithm_13_3_1`,
  `CartisGouldToint.Chapter13.exists_algorithm_13_3_2`: for every derivative oracle that satisfies
  (13.3.4), runs of TRqEDA, and runs of ARqpEDA with the radii control, exist.

## Implementation notes

* The runs reuse the iteration predicates `Optimization.TRqDAStep` and `Optimization.ARqpDAStep` of
  Section 13.1 (Steps 1, 2, 4 and 5 are those of the IDA algorithms) until the termination test
  holds (`Optimization.UntilHit`). They add the new Step 3, `Optimization.EDAStep3`:
  $0 < h_{k,0} \le \kappa_s \overline{\Delta T}$ ((13.3.9), (13.3.18)), inexact values $\bar f(x_k)$
  and $\bar f(x_k + s_k)$ within $h_{k,0}$ of $f$, and the ratio $\rho_k = (\bar f(x_k) -
  \bar f(x_k + s_k)) / \overline{\Delta T}$ ((13.3.10), (13.3.19)). The inexact values are the
  sequences `fx` and `fxs`.
* The proposition `R k` records that $\bar f(x_k)$ is recomputed in Step 3; otherwise $\bar f(x_k)$
  is the trial value of an earlier iteration at the same point. The number of function evaluations
  before iteration $k$ is `Optimization.edaFunEvalCount acc R k`, which is $|\mathcal{T} \cap [0,
  k)| + |\mathcal{T} \cap R \cap [0, k)| \le 2 |\mathcal{T} \cap [0, k)|$. There is no evaluation at
  Step 0.
* The Step-1 data (displacements and radii) and the error bounds of the oracle are required at every
  iteration that the run reaches, including the terminating one, where they certify approximate
  optimality.
* The algorithms and their analysis are those of the library (`Optimization.IsTRqEDARun`,
  `Optimization.IsARqpEDARun`), stated on a feasible set $X$ under the anchored smoothness
  hypothesis `LipschitzDerivsAnchored`. The predicates `CartisGouldToint.Chapter13.algorithm_13_3_1`
  and `CartisGouldToint.Chapter13.algorithm_13_3_2` are the case $X = \mathbb{R}^n$, and the results
  of this module are their instances under Assumption f.D0qL (f.D0pL).
* With inexact values, the iterates still stay in the sublevel set $\{y : f(y) \le f(x_0)\}$. On a
  successful iteration the values are within $h_{k,0} \le \kappa_s \overline{\Delta T}_k$ of $f$,
  and $\kappa_s \le \eta_1 / 4$ ((13.3.5), (13.3.13)) gives $f(x_k) - f(x_{k+1}) \ge \frac12 \eta_1
  \overline{\Delta T}_k > 0$.
* For $q \le 2$ the radius-one conclusion of Theorem 13.3.8 is derived from the certified radii
  $\delta^{(1)}_{k_\epsilon} \in (0, 1]^q$, as in Theorem 13.1.19.

## Deviations from the source

* **Algorithms 13.3.1 and 13.3.2, Step 3** (correction and generalization). The source permits
  reusing the immediately preceding trial value, which may be at a different point if the trial
  was rejected. The run instead permits reusing any prior trial value evaluated at the current
  point that meets the required accuracy. See `Optimization.EDAStep3`.
* **Algorithms 13.3.1 and 13.3.2** (inherited changes). The shared iteration rules include the
  TRqIDA initialization and Step 4 readings and the ARqpIDA Step 2 accuracy correction described
  in Section 13.1.
* **Theorem 13.3.4** (typo). The printed constants $\kappa^B_{\rm TRqEDA} = \frac{6!}{2! \, 2!} 2
  \kappa^B_{\rm TRqIDA}$ and $\kappa^C_{\rm TRqEDA} = \frac{6!}{2} 2 \kappa^C_{\rm TRqIDA}$ are
  garbled; the proof gives the factor $2$ only. See `CartisGouldToint.Chapter13.theorem_13_3_4`.
* **Theorem 13.3.4** (correction). The derivative count omits the initial estimate and the last
  accuracy-improving iteration; the constant is $\kappa^F + 2$, as in Theorem 13.1.8. See
  `CartisGouldToint.Chapter13.theorem_13_3_4`.
* **Lemma 13.3.5** (correction). The bound $\sigma_{\max}$ needs $\max(\kappa_s, \kappa_h)$ in place
  of $\kappa_s$, as in Lemma 13.1.14. See `CartisGouldToint.Chapter13.lemma_13_3_5`.
* **Lemma 13.3.7 and Theorem 13.3.8** (correction). The proof of the source reuses Lemmas
  13.1.16–13.1.17, whose hypothesis that $x_{k+1}$ is not approximately optimal does not follow from
  non-termination. The corrected argument needs $\theta < \varsigma / 2$, has $\varsigma/2 - \theta$
  in place of $1 - \theta$ and $4 \kappa_s$ in place of $3 \kappa_{\nabla,\max} \kappa_s$ in the
  constants. The count also includes short successful steps followed by a Step 1 pass with
  unchanged radii but insufficient accuracy to stop. See
  `CartisGouldToint.Chapter13.lemma_13_3_7`,
  `CartisGouldToint.Chapter13.theorem_13_3_8_i`, `CartisGouldToint.Chapter13.theorem_13_3_8_ii`.
-/

open Set Metric Finset Optimization
open scoped Nat

namespace CartisGouldToint.Chapter13

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)


/-! ### TRqEDA -/

section TRqEDA

variable {X : Set ℝⁿ} {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ}
  {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop} {L : ℕ → ℝ}
  {k : ℕ}

/-- **Algorithm 13.3.1** of [cartis2022evaluation] (TRqEDA), as a run predicate. The data are the
constants of TRqIDA with $\kappa_s \le \min(\eta_1, 1 - \eta_2) / 4$ (13.3.5), tolerances
$\epsilon \in (0, 1]^q$ with $\epsilon_{\min} \le \vartheta$, and a starting point $x_0$. A run
consists of the sequences of a TRqIDA run together with inexact values $\bar f(x_k)$ and
$\bar f(x_k + s_k)$, value accuracies $h_{k,0}$, and flags that mark the recomputation of
$\bar f(x_k)$. At every iteration that the run reaches, the derivative estimates satisfy
(13.3.4) and the Step-1 displacements satisfy (13.3.6). Until termination, every iteration
satisfies Steps 1, 2, 4 and 5 with the ratio (13.3.10)
$$\rho_k = \frac{\bar f(x_k) - \bar f(x_k + s_k)}{\overline{\Delta T}_{f,j_k}(x_k, s_k)},$$
and every trial iteration satisfies Step 3. The method terminates at the first iteration $k$ at
which (13.3.7) fails at every order and
$$\sum_{i=1}^q h_{k,i} \frac{\delta_k^i}{i!} \le \frac12 \varsigma \epsilon_{\min}
  \frac{\delta_k^q}{q!}, \qquad (13.3.8)$$
and it returns $x_\epsilon = x_k$ and $\delta_\epsilon = \min(\Delta_k, \vartheta)$.

The predicate is `Optimization.IsTRqEDARun` with the feasible set $X = \mathbb{R}^n$. The
termination test is `Optimization.edaStopTR`, Step 3 is `Optimization.EDAStep3`, and the ratio
is `Optimization.edaRatio`. An iteration $k$ is reached when the termination test fails at all
iterations before $k$.

**Correction and generalization.** A reused value must come from an earlier trial at the
current point and satisfy (13.3.1). The preceding trial in the printed reuse rule may have
been rejected, leaving its value at a different point. -/
abbrev algorithm_13_3_1 (f : ℝⁿ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x₀ : ℝⁿ)
    (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
    (R : ℕ → Prop) : Prop :=
  IsTRqEDARun f univ P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R

/-- **Lemma 13.3.1** of [cartis2022evaluation]. Assume f.D0qL. Let $k$ be a trial iteration of a
TRqEDA run that has not terminated at the iterations $0, \dots, k$, and let
$$\Delta_k \le \min\left(\vartheta, \frac{1 - \eta_2}{L_f + 4 (q+1)! \kappa_s}
  \hat\phi_{f,k}\right),$$
which is (13.1.28) with $\kappa_{\nabla,\max} = 1$. Then the iteration is very successful,
$\rho_k \ge \eta_2$ for the ratio (13.3.10), and $\Delta_{k+1} \ge \Delta_k$. -/
theorem lemma_13_3_1 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs) *
      trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k ∧
      Δ k ≤ Δ (k + 1) :=
  IsTRqEDARun.ratio_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk ha hΔ

/-- **Lemma 13.3.2** of [cartis2022evaluation]. Assume f.D0qL, let $\kappa_\Delta$ be admissible
with $\kappa_{\nabla,\max} = 1$, that is, $0 < \kappa_\Delta \le 1$ and $\kappa_\Delta \le
\gamma_1 (1 - \eta_2) / (L_f + 4 (q+1)! \kappa_s)$, and let $\kappa_\delta = \kappa_\Delta / 2$.
Every trial iteration $k \in \mathcal{T}$ of a TRqEDA run that has not terminated at the
iterations $0, \dots, k$ satisfies
$$\overline{\Delta T}_{f,j_k}(x_k, s_k) \ge \frac{(\varsigma \kappa_\delta)^{q+1}}{q!}
  \epsilon_{\min}^{q+1}, \qquad (13.1.34)$$
and if moreover $k \in \mathcal{S}$, then
$$f(x_k) - f(x_{k+1}) \ge \eta_1 \frac{(\varsigma \kappa_\delta)^{q+1}}{2 \, q!}
  \epsilon_{\min}^{q+1}. \qquad (13.1.35)$$

**Reading.** Same model and successful actual decreases, with any admissible kappa_Delta instead of
the inherited explicit recipe.
-/
theorem lemma_13_3_2 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k) :
    (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k →
        P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
          f (x k) - f (x (k + 1))) :=
  IsTRqEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hk ha

/-- **Lemma 13.3.3(i)** of [cartis2022evaluation]. If a TRqEDA run terminates at iteration $k$ (Step
1.4.1: (13.3.7) fails at every order and (13.3.8) holds), then $x_k$ is an
$(\epsilon, \delta_k)$-approximate $q$-th order minimizer with
$\delta_k = \min(\Delta_k, \vartheta)$.

No smoothness of $f$ is assumed. -/
theorem lemma_13_3_3_i (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) (hstop : edaStopTR P ε D Δ h dd k) :
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (fun _ => trqDARadius P Δ k) := by
  have := IsTRqEDARun.isEpsDeltaApprox_of_stop hrun hk hstop
  rwa [Set.setOf_add_mem_univ] at this

/-- **Lemma 13.3.3(ii)** of [cartis2022evaluation]. Assume f.D0qL, let $\kappa_\Delta$ be admissible
with $\kappa_{\nabla,\max} = 1$, and let $\kappa_\delta = \kappa_\Delta / 2$. Let $k$ be an
iteration that a TRqEDA run reaches, at which (13.3.7) fails at every order, and let
$$h_{k,i} \le \frac{\varsigma^{q+1} \kappa_\delta^q}{4 q!} \epsilon_{\min}^{q+1} \quad \text{for
  } i \in [1, q]. \qquad (13.1.37)$$
Then (13.3.8) holds: the method terminates at $k$ (Step 1.4.1) and does not branch to Step 5.

**Reading.** Same requested-accuracy bound after all witnesses fail, with arbitrary admissible
kappa_Delta.
-/
theorem lemma_13_3_3_ii (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trqDAFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopTR P ε D Δ h dd k :=
  IsTRqEDARun.stop_of_pass hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hk hpass hh

/-- **Theorem 13.3.4** of [cartis2022evaluation]. Assume f.D0qL and f.Bb with the lower bound
$f_{\rm low}$. Let $\kappa_\Delta$ be admissible with $\kappa_{\nabla,\max} = 1$, and let
$\kappa_\delta = \kappa_\Delta / 2$. Then every TRqEDA run terminates at some iteration
$k_\epsilon$, and $x_{k_\epsilon}$ is an $(\epsilon, \delta_\epsilon)$-approximate $q$-th order
minimizer with $\delta_\epsilon = \min(\Delta_{k_\epsilon}, \vartheta) \in (0, 1]$. Before
termination the method computes at most
$$2 \kappa^A \frac{f(x_0) - f_{\rm low}}{\epsilon_{\min}^{q+1}} + 2 \kappa^B |\log
  \epsilon_{\min}| + 2 \kappa^C$$
inexact function values and at most
$$\kappa^A \frac{f(x_0) - f_{\rm low}}{\epsilon_{\min}^{q+1}} + \kappa^E |\log
  \epsilon_{\min}| + \kappa^F + 2$$
derivative estimates, with the constants of Theorem 13.1.8 for $\kappa_{\nabla,\max} = 1$ and
$\bar L_f = L_f + \kappa_h$.

**Typo.** The source prints $\kappa^B_{\rm TRqEDA} = \frac{6!}{2! \, 2!} 2 \kappa^B_{\rm
TRqIDA}$ and $\kappa^C_{\rm TRqEDA} = \frac{6!}{2} 2 \kappa^C_{\rm TRqIDA}$. These constants are
garbled: the proof gives the factor $2$ only, because each trial iteration computes at most two
function values.

**Correction.** The derivative count of the source omits the initial estimate and the last
accuracy-improving iteration; the constant is $\kappa^F + 2$, as in Theorem 13.1.8.

The function values are counted by `Optimization.edaFunEvalCount`, and $\kappa_{\rm acc}$ is
`Optimization.trKappaAcc` with $\bar L_f = L_f + \kappa_h$ and $\kappa_{\nabla,\max} = 1$. -/
theorem theorem_13_3_4 (hf : AssumptionD0qL f P.q L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) :
    ∃ kε, IsFirstHit (edaStopTR P ε D Δ h dd) kε ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (fun _ => trqDARadius P Δ kε) ∧
      0 < trqDARadius P Δ kε ∧ trqDARadius P Δ kε ≤ 1 ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1)) +
          2 * (1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)|) +
          2 * (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| /
            |Real.log P.γh| + 2 := by
  have := IsTRqEDARun.complexity hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun y _ => hb y) hrun hκΔ
  simpa only [Set.setOf_add_mem_univ] using this

/-- Runs of **Algorithm 13.3.1** exist. Let the constants satisfy (13.3.5), let
$\epsilon \in (0, 1]^q$ with $\epsilon_{\min} \le \vartheta$, let $x_0$ be a starting point, and
let $O$ be a deterministic derivative oracle that satisfies (13.3.4) at every point for all
positive accuracies. Then there is a TRqEDA run whose derivative estimates are $O(x_k, h_k)$.

No smoothness of $f$ is assumed. The constructed run uses the exact function values
$\bar f = f$, recomputed at every trial iteration, and the value accuracies $h_{k,0} = \kappa_s
\overline{\Delta T}_{f,j_k}(x_k, s_k)$; the oracle is used only with positive accuracies.

**Reading.** Realizes the repaired run for an admissible derivative oracle, with exact objective
values as an allowed explicit-accuracy oracle.
-/
theorem exists_algorithm_13_3_1 {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ}
    (hκs : P.κs ≤ min P.η₁ (1 - P.η₂) / 4) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hϑ : epsMin P.q ε ≤ P.ϑ) (x₀ : ℝⁿ) (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.q, 0 < h' i) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.q (fun i => h' i)) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
      (R : ℕ → Prop), algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R ∧
        ∀ k, D k = O (x k) (h k) := by
  obtain ⟨x, Δ, h, dd, jk, s, acc, hx, hΔ, hh, hstep⟩ := exists_trqDA_run f P ε O x₀
  have hεmin : 0 < epsMin P.q ε := Optimization.epsMin_pos P.one_le_q fun j hj => (hε j hj).1
  refine ⟨x, Δ, h, _, dd, jk, s, acc, fun i => f (x i), fun i => f (x i + s i),
    fun i => P.κs * (O (x i) (h i)).taylorDecrement (jk i) (s i), fun _ => True,
    ⟨hκs, hε, hϑ, hx, mem_univ _, hΔ, hh, fun k _ => hO _ _ fun i hi =>
      ((trqDA_invariants (k := k) (fun i _ => hstep i) hΔ hh).2 i hi).1, fun k _ j hj => ?_,
      UntilHit.of_forall fun k => ⟨hstep k, fun ha => ?_⟩⟩, fun _ => rfl⟩
  · exact (hstep k).witness j hj
  · have hΔk := trqDA_delta_pos (k := k) (fun i _ => hstep i) hΔ
    obtain ⟨hφ, hdec⟩ := TRqDAStep.trqGap_ge (hstep k) ha hΔk
    have hφ0 : 0 < P.ς * epsMin P.q ε / 2 := by have := P.ς_pos; positivity
    have hδ := (trqDARadius_mem (P := P) hΔk).1
    have hpos : 0 < (O (x k) (h k)).taylorDecrement (jk k) (s k) :=
      lt_of_lt_of_le (by have := hφ0.trans_le hφ; positivity) hdec
    have h0 := (mul_pos P.κs_pos hpos).le
    exact ⟨mul_pos P.κs_pos hpos, le_rfl, by simpa using h0, by simpa using h0,
      fun hR => absurd trivial hR⟩

end TRqEDA

/-! ### ARqpEDA -/

section ARqpEDA

variable {X : Set ℝⁿ} {f : ℝⁿ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- **Algorithm 13.3.2** of [cartis2022evaluation] (ARqpEDA), as a run predicate. The data are the
constants of ARqpIDA with $\kappa_s \le \min(\eta_1, 1 - \eta_2) / 4$ (13.3.13), tolerances
$\epsilon \in (0, 1]^q$ with $\epsilon_j \le \delta_{0,j}$, and a starting point $x_0$. A run
consists of the sequences of an ARqpIDA run together with inexact values $\bar f(x_k)$ and
$\bar f(x_k + s_k)$, value accuracies $h_{k,0}$, and flags that mark the recomputation of
$\bar f(x_k)$. At every iteration that the run reaches, the derivative estimates satisfy
(13.3.4) up to the order $p$, and Step 1 (13.3.14)–(13.3.16) is performed. Until termination,
every iteration satisfies Steps 1, 2, 4 and 5 with the ratio (13.3.19)
$$\rho_k = \frac{\bar f(x_k) - \bar f(x_k + s_k)}{\overline{\Delta T}_{f,p}(x_k, s_k)},$$
and every trial iteration satisfies Step 3. The method terminates at the first iteration $k$ at
which (13.3.15) holds at every order and
$$\sum_{i=1}^j h_{k,i} \frac{(\delta^{(1)}_{k,j})^i}{i!} \le \frac12 \varsigma \epsilon_j
  \frac{(\delta^{(1)}_{k,j})^j}{j!} \quad \text{for every } j \in [1, q], \qquad (13.3.17)$$
and it returns $x_\epsilon = x_k$ and $\delta_\epsilon = \delta^{(1)}_k$.

The predicate is `Optimization.IsARqpEDARun` with the feasible set $X = \mathbb{R}^n$. The
termination test is `Optimization.edaStopAR`, and Step 1 is `Optimization.ARqpStep1`.

**Correction and generalization.** Step 3 can reuse any earlier trial value evaluated at
the current point that meets (13.3.1), as for `CartisGouldToint.Chapter13.algorithm_13_3_1`.
Step 2 checks derivative accuracy at all orders through $p$ for both step lengths, as in
`CartisGouldToint.Chapter13.algorithm_13_1_2`. -/
abbrev algorithm_13_3_2 (f : ℝⁿ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x₀ : ℝⁿ)
    (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ) (R : ℕ → Prop) : Prop :=
  IsARqpEDARun f univ P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R

/-- **Lemma 13.3.5** of [cartis2022evaluation]. Assume f.D0pL. Every iteration $k$ that an ARqpEDA
run reaches has $\sigma_k \le \sigma_{\max}$, where
$$\sigma_{\max} = \max\left(\sigma_0, \gamma_3 \frac{2 L_{f,p} + 4 (p+1)! \kappa_s'}{1 -
  \eta_2}\right), \qquad \kappa_s' = \max(\kappa_s, \kappa_h),$$
is the bound (13.1.77) of Lemma 13.1.14 with $\kappa_{\nabla,\max} = 1$.

**Correction.** The source has $\kappa_s$ in place of $\kappa_s'$, as in Lemma 13.1.14. The
proof applies the accuracy condition also to long steps, where only $h_{k,i} \le \kappa_h$ is
known.

The constant is `Optimization.arqpIDASigmaMax` with $\kappa_{\nabla,\max} = 1$. -/
theorem lemma_13_3_5 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : σ k ≤ arqpIDASigmaMax P (L P.p) 1 :=
  IsARqpEDARun.sigma_le hf.lipschitzDerivsAnchored (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk

/-- **Lemma 13.3.6(i)** of [cartis2022evaluation]. If an ARqpEDA run terminates at iteration $k$
(Step 1.5.1), then $\delta^{(1)}_k \in (0, 1]^q$ and $x_k$ is an
$(\epsilon, \delta^{(1)}_k)$-approximate $q$-th order minimizer.

No smoothness of $f$ is assumed. -/
theorem lemma_13_3_6_i (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) (hstop : edaStopAR P ε D δ₁ h dd k) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (δ₁ k) := by
  have := IsARqpEDARun.isEpsDeltaApprox_of_stop hrun hk hstop
  rwa [Set.setOf_add_mem_univ] at this

/-- **Lemma 13.3.6(ii)** of [cartis2022evaluation]. Assume f.D0pL and the radii control at every
iteration. Let $\sigma_{\max}$ be the bound of Lemma 13.3.5, $\bar L_f = L_f + \kappa_h$ and
$\kappa^{(1)}_\delta(\sigma) = \varsigma \theta / (24 \max(\bar L_f, \sigma))$. Let $k$ be an
iteration that an ARqpEDA run reaches, at which (13.3.15) holds at every order, and let
$$h_{k,i} \le \frac{\varsigma \kappa^{(1)}_\delta(\sigma_{\max})^q}{4 q!} \epsilon_{\min}^{q+1}
  \quad \text{for } i \in [1, p],$$
which is (13.1.78) with $\kappa_{\nabla,\max} = 1$. Then (13.3.17) holds, and the method
terminates at $k$.

**Correction.** Makes passage of the Step 1 witness tests explicit and uses weaker radii control and
the corrected sigma bound.
-/
theorem lemma_13_3_6_ii (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.ς * arKappaDelta1 P (lipMax L P.p + P.κh)
      (arqpIDASigmaMax P (L P.p) 1) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopAR P ε D δ₁ h dd k :=
  IsARqpEDARun.stop_of_pass hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hk hpass hh

/-- The radius inequality of ARqpEDA, which replaces Lemmas 13.1.16–13.1.17 in Section 13.3.2 of
[cartis2022evaluation]. Assume f.D0pL. Let iteration $k$ of an ARqpEDA run be reached and not
terminal, and let it be successful with $\|s_k\| < 1$. Suppose that Step 1 at $k + 1$ does not
pass every test (13.3.15) with unchanged radii, that is, it halves some radius or branches to
Step 2. Then for some $j \in [1, q]$, with $\delta = \delta_{k+1,j} = \delta_{s_k,j}$,
$$\left(\frac{\varsigma}{2} - \theta\right) \epsilon_j \frac{\delta^j}{j!} \le (L_{f,p} +
  \sigma_{\max} + 4 \kappa_s) \sum_{\ell=1}^j \frac{\delta^\ell}{\ell!} \|s_k\|^{p-\ell+1},$$
with $\sigma_{\max}$ of Lemma 13.3.5.

Step 1 at $k + 1$ provides a displacement in the ball of radius $\delta$ with a large inexact
decrement. Since the accuracies are inherited from iteration $k$, this gives
$\phi^\delta_{f,j}(x_{k+1}) > \frac12 \varsigma \epsilon_j \delta^j / j! - \kappa_s \sum_\ell
\delta^\ell / \ell! \, \|s_k\|^{p-\ell+1}$, and the model-optimality conditions (13.1.57) at
$s_k$ give the inequality.

**Correction.** Uses the failure of a Step 1 pass at unchanged radii in place of true nonoptimality,
and the corrected coefficient.
-/
theorem eda_radius_inequality (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hs1 : ‖s k‖ < 1)
    (hnot : ¬ ((∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd (k + 1) j) ∧
      ∀ j ∈ Finset.Icc 1 P.q, δ₁ (k + 1) j = δ (k + 1) j)) :
    ∃ j ∈ Finset.Icc 1 P.q, (P.ς / 2 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) 1 + 4 * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) :=
  IsARqpEDARun.measure_ineq hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk ha hρ hs1 hnot

/-- **Lemma 13.3.7** of [cartis2022evaluation]. Assume f.D0pL, the radii control at iteration $k$,
and $\theta < \varsigma / 2$. Let iteration $k$ of an ARqpEDA run be successful and let the run
not terminate at the iterations $0, \dots, k$. Suppose that $\|s_k\| \ge 1$, or that Step 1 at
$k + 1$ does not pass every test (13.3.15) with unchanged radii. Then
$$\overline{\Delta T}_{f,p}(x_k, s_k) \ge \kappa'_{\Delta m} \min_j \epsilon_j^{\pi_j} \quad
  \text{and} \quad f(x_k) - f(x_{k+1}) \ge \tfrac12 \eta_1 \kappa'_{\Delta m} \min_j
  \epsilon_j^{\pi_j},$$
where $\kappa'_{\Delta m}$ is the constant $\kappa_{\Delta m}$ of Lemma 13.1.18 with
$\varsigma/2 - \theta$ in place of $1 - \theta$, with
$A' = L_{f,p} + \sigma_{\max} + 4 \kappa_s$ in place of $A = L_{f,p} + \sigma_{\max} + 3
\kappa_{\nabla,\max} \kappa_s$ ($\sigma_{\max}$ of Lemma 13.3.5), and with
$\bar L_f = L_f + \kappa_h$.

**Correction.** The source asserts the decrease for every trial iteration before termination,
and proves the lemma "identically" to Lemma 13.1.18, through Lemmas 13.1.16–13.1.17. These
lemmas assume that $x_{k+1}$ is not approximately optimal, and non-termination of ARqpEDA at
$k + 1$ does not imply this. The corrected argument,
`CartisGouldToint.Chapter13.eda_radius_inequality`, needs $\theta < \varsigma / 2$ and changes
the constants. The successful iterations that the lemma does not cover are followed by an
accuracy-improving iteration (Step 1 branches to Step 5).

The predicate "Step 1 passes with unchanged radii" is `Optimization.edaPassUnchanged`, and $A'$
is `Optimization.arEDAConstA`. -/
theorem lemma_13_3_7 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc k) (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ)
          (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) /
          2 * epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ f (x k) - f (x (k + 1)) :=
  IsARqpEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hθ hk ha hρ hgood

/-- The counting argument of **Theorem 13.3.8** of [cartis2022evaluation], for any decrease
constant. Assume f.D0pL, f.Bb with the lower bound $f_{\rm low}$, and the radii control at every
iteration of an ARqpEDA run. Suppose that every successful iteration $k$ before termination with
$\|s_k\| \ge 1$, or with Step 1 at $k + 1$ not passing with unchanged radii, decreases $f$ by at
least $c > 0$. Then the run terminates at some iteration $k_\epsilon$, and $x_{k_\epsilon}$ is
an $(\epsilon, \delta^{(1)}_{k_\epsilon})$-approximate $q$-th order minimizer with
$\delta^{(1)}_{k_\epsilon} \in (0, 1]^q$. Let
$$N = \frac{f(x_0) - f_{\rm low}}{c}, \qquad M = \frac{p (q+1)}{|\log \gamma_h|} |\log
  \epsilon_{\min}| + \frac{|\log(\kappa_{\rm acc} / \kappa_h)|}{|\log \gamma_h|} + 1, \qquad
  c_T = 1 + \frac{|\log \gamma_1|}{\log \gamma_2}.$$
Before termination the method computes at most $2 ((N + M + 1) c_T + \log(\sigma_{\max} /
\sigma_0) / \log \gamma_2)$ inexact function values and at most $N + 2 M + 2$ derivative
estimates.

The number $M$ bounds the number of accuracy-improving iterations. The successful iterations
that the decrease hypothesis does not cover are followed by an accuracy-improving iteration, so
there are at most $M$ of them.

**Reading.** Counts from an arbitrary positive decrease for covered steps, charging the remaining
successful steps to later accuracy improvements.
-/
theorem arqpEDA_complexity (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i) {c : ℝ}
    (hc : 0 < c)
    (hdec : ∀ k, (∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) → ¬ acc k →
      P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k →
      (1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) → c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / c + (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / c + 2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have := IsARqpEDARun.complexity hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun y _ => hb y) hrun hrc hc hdec
  simpa only [Set.setOf_add_mem_univ] using this

/-- **Theorem 13.3.8** of [cartis2022evaluation], case $q \le 2$. Assume f.D0pL, f.Bb with the lower
bound $f_{\rm low}$, the radii control (13.1.69)–(13.1.70) at every iteration,
$\theta < \varsigma / 2$ and $q \le 2$. Then every ARqpEDA run terminates at some iteration
$k_\epsilon$. The iterate $x_{k_\epsilon}$ is an
$(\epsilon, \delta^{(1)}_{k_\epsilon})$-approximate $q$-th order minimizer with
$\delta^{(1)}_{k_\epsilon} \in (0, 1]^q$, and also satisfies $\phi^1_{f,j}(x_{k_\epsilon}) \le
\epsilon_j / j!$ for $j \in [1, q]$. Before termination the method computes at most $2 ((N +
M + 1) c_T + \log(\sigma_{\max} / \sigma_0) / \log \gamma_2)$ inexact function values and at
most $N + 2 M + 2$ derivative estimates, where
$$N = \kappa'^S \frac{f(x_0) - f_{\rm low}}{\min_j \epsilon_j^{(p+1)/(p-j+1)}}, \qquad
  \kappa'^S = \frac{2}{\eta_1 \kappa'_{\Delta m}}, \qquad \kappa'_{\Delta m} =
  \frac{\sigma_{\min}}{(p+1)!} \left(\frac{\varsigma/2 - \theta}{2 q!
  A'}\right)^{(p+1)/(p-q+1)},$$
$A' = L_{f,p} + \sigma_{\max} + 4 \kappa_s$, $M = \kappa^E |\log \epsilon_{\min}| + \kappa^F +
1$ (with $\kappa_{\nabla,\max} = 1$ and $\sigma_{\max}$ of Lemma 13.3.5), and
$c_T = 1 + |\log \gamma_1| / \log \gamma_2$. Both bounds are
$O(\max_j \epsilon_j^{-(p+1)/(p-j+1)})$, the order that the source claims.

**Correction.** The constants of the source rest on Lemma 13.3.7 as printed (see
`CartisGouldToint.Chapter13.lemma_13_3_7`). The theorem therefore needs the extra hypothesis
$\theta < \varsigma / 2$, the term $M$ in the number of successful iterations, and the corrected
constants; the derivative count also includes the initial estimate and the last
accuracy-improving iteration.

The conclusion with the radius one follows from the certified radii by
`Optimization.isEpsDeltaApprox_one_of_le_two`. The proof applies
`CartisGouldToint.Chapter13.arqpEDA_complexity` with the decrease of Lemma 13.3.7. -/
theorem theorem_13_3_8_i (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) (hq2 : P.q ≤ 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (δ₁ kε) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (fun _ => 1) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * ((2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) / (2 * P.q ! * arEDAConstA P L)) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) * (f x₀ - flow) /
              epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) / (2 * P.q ! * arEDAConstA P L)) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) * (f x₀ - flow) /
            epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hq2' : P.q ≤ 2 := hq2
  set κΔm := (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) / (2 * P.q ! * arEDAConstA P L)) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ))) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
      (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hf.one_le le_rfl)
  have ha0 : 0 < P.ς / 2 - P.θ := by linarith
  have hκpos : 0 < κΔm := by
    rw [← hκ']
    have hC : 0 < arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) := by
      have hk0 : 0 < arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
          (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) :=
        lt_min (arKappaDelta1_pos (by linarith)) (by positivity)
      unfold arStepConst arStepConstOf
      split_ifs
      positivity
    have := P.σmin_pos
    positivity
  have hmpos : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, hmem, happ, h1, h2⟩ := arqpEDA_complexity hf hb hrun hrc hc
    fun k hk ha hρ hgood => by
      have := (lemma_13_3_7 hf hrun (hrc k) hθ hk ha hρ hgood).2
      rwa [hm', hκ'] at this
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = 2 / (P.η₁ * κΔm) * (f x₀ - flow) / m := by
    have := P.η₁_pos; field_simp
  rw [hdiv] at h1 h2
  exact ⟨kε, hk, hmem, happ, isEpsDeltaApprox_one_of_le_two hq2 hmem happ, h1, h2⟩

/-- **Theorem 13.3.8** of [cartis2022evaluation], case $q > 2$. Under the hypotheses of
`CartisGouldToint.Chapter13.theorem_13_3_8_i` with $q > 2$ in place of $q \le 2$, every ARqpEDA
run terminates at some iteration $k_\epsilon$ with $x_{k_\epsilon}$ an
$(\epsilon, \delta^{(1)}_{k_\epsilon})$-approximate $q$-th order minimizer,
$\delta^{(1)}_{k_\epsilon} \in (0, 1]^q$, and the bounds of the case $q \le 2$ hold with the
exponents $\pi_j = j (p+1)/p$ and
$$\kappa'_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!} \left(\frac{(\varsigma/2 - \theta)
  \hat\kappa^{q-1}}{2 q! A'}\right)^{q(p+1)/p}, \qquad \hat\kappa =
  \min\left(\kappa_{\delta,\min}, \frac{\varsigma/2 - \theta}{2 q! A'}\right).$$
Both bounds are $O(\max_j \epsilon_j^{-j(p+1)/p})$.

**Correction.** As in `CartisGouldToint.Chapter13.theorem_13_3_8_i`, the theorem needs
$\theta < \varsigma / 2$, the term $M$ and the corrected constants. -/
theorem theorem_13_3_8_ii (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) (hq2 : 2 < P.q) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * ((2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) * arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
              (f x₀ - flow) /
              epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) * arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
              (f x₀ - flow) /
            epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hq2' : ¬ P.q ≤ 2 := not_le.2 hq2
  set κΔm := (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) * arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
      (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hf.one_le le_rfl)
  have ha0 : 0 < P.ς / 2 - P.θ := by linarith
  have hκpos : 0 < κΔm := by
    rw [← hκ']
    have hC : 0 < arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) := by
      have hk0 : 0 < arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
          (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) :=
        lt_min (arKappaDelta1_pos (by linarith)) (by positivity)
      unfold arStepConst arStepConstOf
      split_ifs
      positivity
    have := P.σmin_pos
    positivity
  have hmpos : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, hmem, happ, h1, h2⟩ := arqpEDA_complexity hf hb hrun hrc hc
    fun k hk ha hρ hgood => by
      have := (lemma_13_3_7 hf hrun (hrc k) hθ hk ha hρ hgood).2
      rwa [hm', hκ'] at this
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = 2 / (P.η₁ * κΔm) * (f x₀ - flow) / m := by
    have := P.η₁_pos; field_simp
  rw [hdiv] at h1 h2
  exact ⟨kε, hk, hmem, happ, h1, h2⟩

/-- Runs of **Algorithm 13.3.2** exist. Assume f.D0pL. Let the constants satisfy (13.3.13) and have
positive initial accuracies, let $\epsilon \in (0, 1]^q$ with $\epsilon_j \le \delta_{0,j}$, let
$x_0$ be a starting point, and let $O$ be a deterministic derivative oracle that satisfies
(13.3.4) at every point for all accuracies $h \in (0, \kappa_h]^p$. Then there is an ARqpEDA run
whose derivative estimates are $O(x_k, h_k)$ and which satisfies the radii control at every
iteration.

The constructed run uses the exact function values $\bar f = f$, recomputed at every trial
iteration, and the value accuracies $h_{k,0} = \kappa_s \overline{\Delta T}_{f,p}(x_k, s_k)$.
The proof specializes `CartisGouldToint.Chapter13.exists_algorithm_13_1_2` with
$\kappa_{\nabla,i} = 1$.

**Reading.** Produces a run of the revised scheme for an admissible derivative oracle and certifies
the sufficient radii control.
-/
theorem exists_algorithm_13_3_2 {f : ℝⁿ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {L : ℕ → ℝ}
    (hf : AssumptionD0pL f P.p L) (hκs : P.κs ≤ min P.η₁ (1 - P.η₂) / 4)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j)
    (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i)
    (x₀ : ℝⁿ) (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.p (fun i => h' i)) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ) (R : ℕ → Prop),
      algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R ∧
        (∀ k, D k = O (x k) (h k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc k := by
  obtain ⟨x, σ, δ, δ₁, δs, h, D, dd, jk, s, acc, hrun, hD, hrc⟩ :=
    exists_algorithm_13_1_2 O (κg := fun _ => 1) hf hε hεδ (fun _ _ => zero_le_one) hh₀ x₀
      fun y h' hh => (hO y h' hh).mono_err fun i _ => by simp
  have hone : ordMax P.p (fun _ => (1 : ℝ)) = 1 := by
    obtain ⟨j, _, he⟩ := exists_ordMax_eq (ε := fun _ => (1 : ℝ)) P.one_le_p
    exact he
  rw [hone, one_mul] at hrc
  refine ⟨x, σ, δ, δ₁, δs, h, D, dd, jk, s, acc, fun i => f (x i), fun i => f (x i + s i),
    fun i => P.κs * (D i).taylorDecrement P.p (s i), fun _ => True,
    ⟨hκs, hε, hεδ, hrun.x_zero, mem_univ _, hrun.σ_zero, hrun.δ_zero, hrun.h_zero,
      fun k _ => (hrun.oracle k).mono_err fun i _ => by simp,
      fun k _ => (hrun.step k).toARqpStep1,
      UntilHit.of_forall fun k => ⟨hrun.step k, fun ha => ?_⟩⟩,
    hD, hrc⟩
  have hpos := (ARqpDAStep.taylorDecrement_ge (hrun.step k) ha (fun j hj => (hε j hj).1)
    (hrun.sigma_pos k).le).2
  have h0 := (mul_pos P.κs_pos hpos).le
  exact ⟨mul_pos P.κs_pos hpos, le_rfl, by simpa using h0, by simpa using h0,
    fun hR => absurd trivial hR⟩
end ARqpEDA

end CartisGouldToint.Chapter13
