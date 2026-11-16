/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Existence
import Numlib.Optimization.Complexity.Telescoping
import Numlib.Optimization.ModelBased.RegularizationUpdate
import Numlib.Optimization.ModelBased.TaylorModel

/-!
# Generic runs of adaptive-regularization methods

Every adaptive-regularization (AR) method of [cartis2022evaluation] shares Steps 3–4 of its
iteration. These methods are Algorithms 2.4.1 (AR1), 3.3.1 (AR2), 4.1.1 (ARp), 5.1.1 (ARpLE), 5.5.1
(ARp-H), 6.2.1 (ARp-CC), 6.2.2 (ARp1-CC), 6.3.1 (ARpLE-CC), the inner runs of Algorithm 7.2.1,
12.2.2 (ARqp) and 14.1.1 (ARqpC), and, for single iterations, 13.1.2 (ARqpIDA) and 13.3.2 (ARqpEDA).
Given the ratio $\rho_k$ of iteration $k$, the trial point $x_k + s_k$ is accepted if and only if
$\eta_1 \le \rho_k$, and the regularization weight is updated by the rule (2.4.4):
$$\sigma_{k+1} \in \begin{cases} [\max(\sigma_{\min}, \gamma_1 \sigma_k), \sigma_k] & \text{if }
  \rho_k \ge \eta_2, \\ [\sigma_k, \gamma_2 \sigma_k] & \text{if } \eta_1 \le \rho_k < \eta_2, \\
  [\gamma_2 \sigma_k, \gamma_3 \sigma_k] & \text{if } \rho_k < \eta_1. \end{cases}$$
The methods differ only in three ingredients: the Step-1 termination test $\mathrm{stop}_1(k)$
together with an optional test $\mathrm{stop}_2(k)$ that is evaluated after the step is computed,
the Step-2 conditions $\mathrm{step}(k)$ on the step, and the ratio $\rho_k$. This file defines a
run with these ingredients as parameters and proves the facts that the complexity analyses of all AR
methods share.

A run terminates at the first $k$ with $\mathrm{stop}_1(k) \lor \mathrm{stop}_2(k)$. Below,
iteration $k$ is *reached* if the termination test fails at every $j < k$, and *before termination*
if it fails at every $j \le k$. Iteration $k$ is *successful* if $\eta_1 \le \rho_k$, and
$\mathcal{S}_k = \{j \le k \mid \eta_1 \le \rho_j\}$ is the set of successful iterations up to $k$.
The main results bound the weights by $\sigma_{\max} = \max(\sigma_0, \gamma_3 L / (1 - \eta_2))$
(Lemma 4.1.2), count the iterations by the successful ones (Lemma 2.4.1), and combine these counts
with a decrease per successful iteration into the evaluation bound (4.1.46) of the complexity
theorems.

## Main definitions

* `Optimization.ARParams`: the constants $\sigma_0, \sigma_{\min}, \eta_1, \eta_2, \gamma_1,
  \gamma_2, \gamma_3$ of (2.4.2).
* `Optimization.ARAcceptance`: Steps 3–4 of one iteration.
* `Optimization.IsARRun`: a run, with the rules imposed only before termination.
* `Optimization.taylorRatio`: the ratio (2.4.3), (3.3.7), (4.1.15) for exact Taylor models.
* `Optimization.arSigmaMax`: the bound $\sigma_{\max} = \max(\sigma_0, \gamma_3 L / (1 - \eta_2))$
  of (4.1.19).
* `Optimization.prevIterate`: the previous iterate, weight and step, which a termination test may
  read.

## Main results

* `Optimization.IsARRun.sigma_le_max`: the mechanism of Lemmas 2.4.2, 3.3.2 and 4.1.2, which bounds
  the weights when a large weight forces a very successful iteration.
* `Optimization.IsARRun.sigma_le`: Lemma 4.1.2 for every AR method with exact Taylor models, also on
  a convex feasible set.
* `Optimization.IsARRun.sub_ge_of_succ`, `Optimization.IsARRun.sub_ge_of_succ_taylor`: the decrease
  (4.1.37) on successful iterations.
* `Optimization.IsARRun.succ_count`, `Optimization.IsARRun.le_succ_count`: Lemma 2.4.1, which bounds
  the number of iterations by the number of successful ones.
* `Optimization.IsARRun.exists_isFirstHit_of_decrease`: the counting argument that ends the proofs
  of the complexity theorems (Theorems 2.4.4, 3.3.5, 4.1.5 and others), with the constants (4.1.46).
* `Optimization.IsARRun.forall_lt_not_stop_iff`, `Optimization.IsARRun.forall_le_not_stop_iff`,
  `Optimization.IsARRun.isFirstHit_stop_iff`, `Optimization.IsARRun.exists_last_succ`,
  `Optimization.IsARRun.eq_of_forall_not_succ`,
  `Optimization.IsARRun.card_successSet_le_card_succ_add_one`: facts about runs without a post-step
  test.
* `Optimization.exists_isARRun_prev`, `Optimization.exists_isARRun`: runs exist when an admissible
  step exists whenever the test fails. The test may read the previous iteration, as the third-order
  test of ARp does through the set $\mathcal{M}_k$.

## Implementation notes

* A run fixes nothing after termination: the step conditions and Steps 3–4 hold only at iterations
  before termination. The rule "for all $j \le k$ the test fails" is `Optimization.UntilHit`, and
  the termination index is `Optimization.IsFirstHit`.
* Iterations that leave both the iterate and the weight unchanged, such as the accuracy-improving
  iterations of Chapter 13, do not fit `Optimization.IsARRun`. Their rules for single iterations use
  `Optimization.ARAcceptance`.
-/

open Set Finset
open scoped Nat

namespace Optimization

/-- The constants of an adaptive-regularization method, as in (2.4.2), (3.3.3) and Step 0 of
Algorithms 4.1.1, 6.2.1, 12.2.2, 13.1.2 and 14.1.1 of [cartis2022evaluation]. They consist of
the initial weight $\sigma_0 > 0$, the lower bound $\sigma_{\min}$ with
$0 \le \sigma_{\min} \le \sigma_0$, the acceptance thresholds $0 < \eta_1 \le \eta_2 < 1$, and
the update factors $0 < \gamma_1 < 1 < \gamma_2 \le \gamma_3$.

The lower bound $\sigma_{\min} = 0$ is allowed, as ARp-H (Algorithm 5.5.1) needs. The strict
inequality $\gamma_2 < \gamma_3$ is not required, because no result uses it. -/
structure ARParams where
  /-- The initial regularization weight $\sigma_0$. -/
  σ₀ : ℝ
  /-- The lower bound $\sigma_{\min}$ on the regularization weight. -/
  σmin : ℝ
  /-- The threshold $\eta_1$ for successful iterations. -/
  η₁ : ℝ
  /-- The threshold $\eta_2$ for very successful iterations. -/
  η₂ : ℝ
  /-- The decrease factor $\gamma_1$ of very successful iterations. -/
  γ₁ : ℝ
  /-- The increase factor $\gamma_2$: the upper end for successful iterations and the lower end for
  unsuccessful iterations. -/
  γ₂ : ℝ
  /-- The largest increase factor $\gamma_3$. -/
  γ₃ : ℝ
  /-- The initial weight is positive: $\sigma_0 > 0$. -/
  σ₀_pos : 0 < σ₀
  /-- The lower bound is nonnegative: $\sigma_{\min} \ge 0$. -/
  σmin_nonneg : 0 ≤ σmin
  /-- The lower bound is at most the initial weight: $\sigma_{\min} \le \sigma_0$. -/
  σmin_le_σ₀ : σmin ≤ σ₀
  /-- The first threshold is positive: $\eta_1 > 0$. -/
  η₁_pos : 0 < η₁
  /-- The thresholds are ordered: $\eta_1 \le \eta_2$. -/
  η₁_le_η₂ : η₁ ≤ η₂
  /-- The second threshold is less than one: $\eta_2 < 1$. -/
  η₂_lt_one : η₂ < 1
  /-- The decrease factor is positive: $\gamma_1 > 0$. -/
  γ₁_pos : 0 < γ₁
  /-- The decrease factor is less than one: $\gamma_1 < 1$. -/
  γ₁_lt_one : γ₁ < 1
  /-- The increase factor is greater than one: $\gamma_2 > 1$. -/
  one_lt_γ₂ : 1 < γ₂
  /-- The increase factors are ordered: $\gamma_2 \le \gamma_3$. -/
  γ₂_le_γ₃ : γ₂ ≤ γ₃

namespace ARParams

variable (P : ARParams)

/-- The decrease factor of AR constants satisfies $\gamma_1 \le 1$. -/
theorem γ₁_le_one : P.γ₁ ≤ 1 := P.γ₁_lt_one.le

/-- The increase factor of AR constants satisfies $\gamma_2 \ge 1$. -/
theorem one_le_γ₂ : 1 ≤ P.γ₂ := P.one_lt_γ₂.le

/-- The increase factor of AR constants satisfies $\gamma_2 > 0$. -/
theorem γ₂_pos : 0 < P.γ₂ := one_pos.trans P.one_lt_γ₂

/-- The largest increase factor of AR constants satisfies $\gamma_3 > 1$. -/
theorem one_lt_γ₃ : 1 < P.γ₃ := P.one_lt_γ₂.trans_le P.γ₂_le_γ₃

/-- The largest increase factor of AR constants satisfies $\gamma_3 \ge 1$. -/
theorem one_le_γ₃ : 1 ≤ P.γ₃ := P.one_lt_γ₃.le

/-- The largest increase factor of AR constants satisfies $\gamma_3 > 0$. -/
theorem γ₃_pos : 0 < P.γ₃ := one_pos.trans P.one_lt_γ₃

/-- The second threshold of AR constants satisfies $\eta_2 > 0$. -/
theorem η₂_pos : 0 < P.η₂ := P.η₁_pos.trans_le P.η₁_le_η₂

/-- The second threshold of AR constants satisfies $1 - \eta_2 > 0$. -/
theorem one_sub_η₂_pos : 0 < 1 - P.η₂ := sub_pos.2 P.η₂_lt_one

/-- The increase factor of AR constants satisfies $\log \gamma_2 > 0$. -/
theorem log_γ₂_pos : 0 < Real.log P.γ₂ := Real.log_pos P.one_lt_γ₂

end ARParams

section Acceptance

variable {E : Type*} [Add E]

/-- **Steps 3–4 of one AR iteration**, as in (2.4.3)–(2.4.4), (4.1.15)–(4.1.16),
(12.2.30)–(12.2.31), (13.1.58)–(13.1.59) and (14.1.15)–(14.1.16) of [cartis2022evaluation].
Given AR constants, a ratio $\rho$, an iterate $x$, a step $s$ and a weight $\sigma$, the new
iterate $x'$ and the new weight $\sigma'$ are **admissible** if
$$x' = \begin{cases} x + s & \text{if } \eta_1 \le \rho, \\ x & \text{otherwise,} \end{cases}$$
and $\sigma'$ satisfies the update rule (2.4.4): $\max(\sigma_{\min}, \gamma_1 \sigma) \le
\sigma' \le \sigma$ if $\rho \ge \eta_2$, $\sigma \le \sigma' \le \gamma_2 \sigma$ if
$\eta_1 \le \rho < \eta_2$, and $\gamma_2 \sigma \le \sigma' \le \gamma_3 \sigma$ if
$\rho < \eta_1$.

The update rule is `Optimization.ARUpdate`. -/
def ARAcceptance (P : ARParams) (ρ : ℝ) (x s x' : E) (σ σ' : ℝ) : Prop :=
  x' = (if P.η₁ ≤ ρ then x + s else x) ∧ ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin ρ σ σ'

variable {P : ARParams} {ρ : ℝ} {x s x' : E} {σ σ' : ℝ}

/-- Steps 3–4 hold if and only if $x'$ is $x + s$ when $\eta_1 \le \rho$ and $x$ otherwise, and
$\sigma'$ satisfies the update rule (2.4.4). -/
theorem arAcceptance_iff :
    ARAcceptance P ρ x s x' σ σ' ↔
      x' = (if P.η₁ ≤ ρ then x + s else x) ∧ ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin ρ σ σ' :=
  Iff.rfl

namespace ARAcceptance

variable (h : ARAcceptance P ρ x s x' σ σ')
include h

/-- If Steps 3–4 hold, then the new weight satisfies the update rule (2.4.4). -/
theorem update : ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin ρ σ σ' := h.2

/-- If Steps 3–4 hold and the iteration is successful ($\eta_1 \le \rho$), then the new iterate is
the trial point: $x' = x + s$. -/
theorem eq_add (hρ : P.η₁ ≤ ρ) : x' = x + s := by
  rw [h.1, ite_eq_left hρ]

/-- If Steps 3–4 hold and the iteration is unsuccessful ($\rho < \eta_1$), then the iterate is kept:
$x' = x$. -/
theorem eq_self (hρ : ρ < P.η₁) : x' = x := by
  rw [h.1, ite_eq_right (not_le.2 hρ)]

/-- If Steps 3–4 hold, then the new iterate is the trial point or the old iterate: $x' = x + s$ or
$x' = x$. -/
theorem eq_add_or_eq_self : x' = x + s ∨ x' = x := by
  by_cases hρ : P.η₁ ≤ ρ
  · exact Or.inl (h.eq_add hρ)
  · exact Or.inr (h.eq_self (not_le.1 hρ))

/-- If Steps 3–4 hold and $\sigma > 0$, then $\sigma' > 0$. -/
theorem pos (hσ : 0 < σ) : 0 < σ' := h.2.pos P.γ₁_pos P.γ₂_pos hσ

/-- If Steps 3–4 hold and $\sigma \ge \sigma_{\min}$, then $\sigma' \ge \sigma_{\min}$. -/
theorem sigmaMin_le (hσ : P.σmin ≤ σ) : P.σmin ≤ σ' :=
  h.2.sigmaMin_le P.σmin_nonneg P.one_le_γ₂ hσ

/-- **Decrease on a successful iteration.** Let Steps 3–4 hold, let $w$ be an objective and
$\mathrm{pred} > 0$, and let the ratio be $\rho = (w(x) - w(x + s)) / \mathrm{pred}$. If
$\eta_1 \le \rho$, then $w(x) - w(x') \ge \eta_1 \, \mathrm{pred}$. -/
theorem sub_ge {w : E → ℝ} {pred : ℝ} (hρ : ρ = reductionRatio w x s pred) (hpred : 0 < pred)
    (hs : P.η₁ ≤ ρ) : P.η₁ * pred ≤ w x - w x' := by
  rw [h.eq_add hs]
  exact sub_le_of_le_reductionRatio hpred (hρ ▸ hs)

/-- Let Steps 3–4 hold, let $w$ be an objective and $\mathrm{pred} > 0$, and let the ratio be
$\rho = (w(x) - w(x + s)) / \mathrm{pred}$. Then the objective does not increase:
$w(x') \le w(x)$. -/
theorem le {w : E → ℝ} {pred : ℝ} (hρ : ρ = reductionRatio w x s pred) (hpred : 0 < pred) :
    w x' ≤ w x := by
  by_cases hs : P.η₁ ≤ ρ
  · have := h.sub_ge hρ hpred hs
    nlinarith [P.η₁_pos]
  · rw [h.eq_self (not_le.1 hs)]

end ARAcceptance

/-- **Existence of the next weight.** Let $\sigma \ge \sigma_{\min}$. For every ratio $\rho$,
iterate $x$ and step $s$ there is a weight $\sigma'$ such that Steps 3–4 hold with the new
iterate $x + s$ if $\eta_1 \le \rho$ and $x$ otherwise. Moreover $\sigma' \ge \sigma_{\min}$,
and $\sigma' > 0$ if $\sigma > 0$.

The proof takes the left ends of the intervals of (2.4.4):
$\sigma' = \max(\sigma_{\min}, \gamma_1 \sigma)$ after a very successful iteration,
$\sigma' = \sigma$ after a successful one and $\sigma' = \gamma_2 \sigma$ after an unsuccessful
one. -/
theorem exists_arAcceptance (P : ARParams) (ρ : ℝ) (x s : E) {σ : ℝ} (hσ : P.σmin ≤ σ) :
    ∃ σ', ARAcceptance P ρ x s (if P.η₁ ≤ ρ then x + s else x) σ σ' ∧ P.σmin ≤ σ' ∧
      (0 < σ → 0 < σ') := by
  have hσ0 : 0 ≤ σ := P.σmin_nonneg.trans hσ
  have hγσ : P.γ₁ * σ ≤ σ := mul_le_of_le_one_left hσ0 P.γ₁_le_one
  have hacc : ARAcceptance P ρ x s (if P.η₁ ≤ ρ then x + s else x) σ
      (if P.η₂ ≤ ρ then max P.σmin (P.γ₁ * σ) else if P.η₁ ≤ ρ then σ else P.γ₂ * σ) := by
    refine ⟨rfl, ⟨fun h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩⟩
    · rw [ite_eq_left h2]
      exact ⟨le_rfl, max_le hσ hγσ⟩
    · rw [ite_eq_right (not_le.2 h2), ite_eq_left h1]
      exact ⟨le_rfl, le_mul_of_one_le_left hσ0 P.one_le_γ₂⟩
    · rw [ite_eq_right (not_le.2 (h1.trans_le P.η₁_le_η₂)), ite_eq_right (not_le.2 h1)]
      exact ⟨le_rfl, mul_le_mul_of_nonneg_right P.γ₂_le_γ₃ hσ0⟩
  refine ⟨_, hacc, hacc.sigmaMin_le hσ, hacc.pos⟩

/-- Let $\rho \ge 1$ and $\sigma \ge \max(\sigma_{\min}, 0)$. Then for every iterate $x$ and step
$s$, Steps 3–4 hold with the new iterate $x + s$ and the unchanged weight $\sigma' = \sigma$.

An iteration with $\rho \ge 1 > \eta_2$ is very successful, and $\sigma$ lies in the interval
$[\max(\sigma_{\min}, \gamma_1 \sigma), \sigma]$ of (2.4.4) because $\gamma_1 \le 1$. -/
theorem arAcceptance_of_one_le (P : ARParams) {ρ : ℝ} (hρ : 1 ≤ ρ) (x s : E) {σ : ℝ}
    (hσ : P.σmin ≤ σ) (hσ0 : 0 ≤ σ) : ARAcceptance P ρ x s (x + s) σ σ := by
  have h1 : P.η₁ ≤ ρ := by linarith [P.η₁_le_η₂, P.η₂_lt_one]
  have h2 : P.η₂ ≤ ρ := by linarith [P.η₂_lt_one]
  refine ⟨by rw [ite_eq_left h1], fun _ => ⟨max_le hσ (mul_le_of_le_one_left hσ0 P.γ₁_le_one),
    le_rfl⟩, fun _ h => absurd h (not_lt.2 h2), fun h => absurd h (not_lt.2 h1)⟩

end Acceptance

/-- The termination test of an AR run at iteration $k$: the Step-1 test $\mathrm{stop}_1(k)$ or the
post-step test $\mathrm{stop}_2(k)$ holds. -/
abbrev IsARRun.Stop (stop₁ stop₂ : ℕ → Prop) (k : ℕ) : Prop := stop₁ k ∨ stop₂ k

/-- If the post-step test is always false, then the termination test of an AR run at iteration $k$
holds if and only if the Step-1 test $\mathrm{stop}_1(k)$ holds. -/
@[simp]
theorem IsARRun.stop_false_iff {stop₁ : ℕ → Prop} {k : ℕ} :
    IsARRun.Stop stop₁ (fun _ => False) k ↔ stop₁ k :=
  (or_false _).to_iff

/-- If the post-step test is always false, then the termination test fails at every $j < k$ if and
only if the Step-1 test fails at every $j < k$. -/
theorem IsARRun.forall_lt_not_stop_iff {stop₁ : ℕ → Prop} {k : ℕ} :
    (∀ j < k, ¬ IsARRun.Stop stop₁ (fun _ => False) j) ↔ ∀ j < k, ¬ stop₁ j := by
  simp [IsARRun.Stop]

/-- If the post-step test is always false, then the termination test fails at every $j \le k$ if and
only if the Step-1 test fails at every $j \le k$. -/
theorem IsARRun.forall_le_not_stop_iff {stop₁ : ℕ → Prop} {k : ℕ} :
    (∀ j ≤ k, ¬ IsARRun.Stop stop₁ (fun _ => False) j) ↔ ∀ j ≤ k, ¬ stop₁ j := by
  simp [IsARRun.Stop]

/-- If the post-step test is always false, then $k$ is the first index at which the termination test
holds if and only if $k$ is the first index at which the Step-1 test holds. -/
@[simp]
theorem IsARRun.isFirstHit_stop_iff {stop₁ : ℕ → Prop} {k : ℕ} :
    IsFirstHit (IsARRun.Stop stop₁ fun _ => False) k ↔ IsFirstHit stop₁ k := by
  simp [isFirstHit_iff, IsARRun.Stop]

/-- **A run of an adaptive-regularization method**, Steps 2–4 of Algorithms 2.4.1, 3.3.1, 4.1.1 and
12.2.2 of [cartis2022evaluation]. Let $P$ be AR constants, $\mathrm{stop}_1(k)$ the Step-1
termination test at iteration $k$, $\mathrm{stop}_2(k)$ a termination test evaluated after the
step has been computed, $\mathrm{step}(k)$ the Step-2 conditions on the trial step $s_k$, and
$\rho_k$ the ratio of iteration $k$. Sequences $(x_k)$, $(s_k)$ and $(\sigma_k)$ form a **run**
if

* $\sigma_0$ is the initial weight of $P$;
* the Step-2 conditions $\mathrm{step}(k)$ hold at every reached iteration $k$ at which the
  Step-1 test fails;
* Steps 3–4 (`Optimization.ARAcceptance`) hold at every iteration before termination, from
  $(x_k, s_k, \sigma_k)$ to $(x_{k+1}, \sigma_{k+1})$ with the ratio $\rho_k$.

The run terminates at the first $k$ with $\mathrm{stop}_1(k) \lor \mathrm{stop}_2(k)$. Iteration
$k$ is successful if $\eta_1 \le \rho_k$.

Iteration $k$ is reached if the termination test fails at every $j < k$, and it is before
termination if the test fails at every $j \le k$. For most methods $\mathrm{stop}_2$ is
`fun _ => False`; ARqp uses $m_k(s_k) = m_k(0)$, and ARp-H uses the test at the trial point. -/
structure IsARRun {E : Type*} [Add E] (P : ARParams) (stop₁ step stop₂ : ℕ → Prop) (ρ : ℕ → ℝ)
    (x s : ℕ → E) (σ : ℕ → ℝ) : Prop where
  /-- The initial weight is $\sigma_0$. -/
  sigma_zero : σ 0 = P.σ₀
  /-- Step 2 holds at every reached iteration whose Step-1 test fails, also at an iteration that
  then terminates by the post-step test. -/
  step : ∀ k, (∀ j < k, ¬ IsARRun.Stop stop₁ stop₂ j) → ¬ stop₁ k → step k
  /-- Steps 3–4 hold at every iteration before termination. -/
  accept : UntilHit (IsARRun.Stop stop₁ stop₂)
    fun k => ARAcceptance P (ρ k) (x k) (s k) (x (k + 1)) (σ k) (σ (k + 1))

/-- The ratio (2.4.3), (3.3.7), (4.1.15) of [cartis2022evaluation] for exact Taylor models: the
achieved decrease over the decrease of the Taylor polynomial,
$$\rho_k = \frac{f(x_k) - f(x_k + s_k)}{T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k)}.$$

The denominator is `(ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)`. If the denominator is
$0$, the ratio is $0$. -/
noncomputable def taylorRatio {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (p : ℕ) (x s : ℕ → E) (k : ℕ) : ℝ :=
  reductionRatio f (x k) (s k) ((ftaylorSeries ℝ f (x k)).taylorDecrement p (s k))

/-- The Taylor ratio is the reduction ratio of $f$ at $x_k$ and $s_k$ with the predicted decrease
$T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k)$. -/
theorem taylorRatio_def {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (p : ℕ) (x s : ℕ → E) (k : ℕ) :
    taylorRatio f p x s k =
      reductionRatio f (x k) (s k) ((ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) :=
  rfl

/-- The upper bound on the regularization weight,
$$\sigma_{\max} = \max\Bigl(\sigma_0, \frac{\gamma_3 L}{1 - \eta_2}\Bigr),$$
of (4.1.19) of [cartis2022evaluation]. For $p = 2$ it is (3.3.13). The bound (2.4.9) of AR1 is
`Optimization.arSigmaMax P (L / 2)`. -/
noncomputable def arSigmaMax (P : ARParams) (L : ℝ) : ℝ := max P.σ₀ (P.γ₃ * L / (1 - P.η₂))

/-- The bound $\sigma_{\max}$ equals $\max(\sigma_0, \gamma_3 L / (1 - \eta_2))$. -/
theorem arSigmaMax_def (P : ARParams) (L : ℝ) :
    arSigmaMax P L = max P.σ₀ (P.γ₃ * L / (1 - P.η₂)) := rfl

/-- The bound $\sigma_{\max}$ is at least $\sigma_0$. -/
theorem σ₀_le_arSigmaMax (P : ARParams) (L : ℝ) : P.σ₀ ≤ arSigmaMax P L := le_max_left _ _

/-- The bound $\sigma_{\max}$ is positive. -/
theorem arSigmaMax_pos (P : ARParams) (L : ℝ) : 0 < arSigmaMax P L :=
  P.σ₀_pos.trans_le (σ₀_le_arSigmaMax P L)

/-- The bound $\sigma_{\max}$ is monotone in $L$: if $L \le L'$, then
$\sigma_{\max}(L) \le \sigma_{\max}(L')$. -/
theorem arSigmaMax_mono (P : ARParams) {L L' : ℝ} (h : L ≤ L') :
    arSigmaMax P L ≤ arSigmaMax P L' :=
  max_le_max le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h P.γ₃_pos.le)
    P.one_sub_η₂_pos.le)

namespace IsARRun

section General

variable {E : Type*} [Add E] {P : ARParams} {stop₁ step stop₂ : ℕ → Prop} {ρ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ} (h : IsARRun P stop₁ step stop₂ ρ x s σ)
include h

/-- An AR run whose step conditions $\mathrm{step}(k)$ imply conditions $\mathrm{step}'(k)$ for
every $k$ is also a run with the step conditions $\mathrm{step}'$. -/
theorem mono {step' : ℕ → Prop} (hst : ∀ k, step k → step' k) :
    IsARRun P stop₁ step' stop₂ ρ x s σ :=
  ⟨h.sigma_zero, fun k hk h1 => hst k (h.step k hk h1), h.accept⟩

/-- In an AR run, the Step-2 conditions hold at every iteration before termination. -/
theorem step_of_forall_le {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) : step k :=
  h.step k (fun j hj => hk j hj.le) fun h1 => hk k le_rfl (Or.inl h1)

/-- In an AR run, the weight update (2.4.4) from $\sigma_k$ to $\sigma_{k+1}$ holds at every
iteration $k$ before termination. -/
theorem update {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) :
    ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin (ρ k) (σ k) (σ (k + 1)) :=
  (h.accept k hk).update

/-- In an AR run, a successful iteration $k$ before termination moves to the trial point:
$x_{k+1} = x_k + s_k$. -/
theorem eq_add_of_succ {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) (hs : P.η₁ ≤ ρ k) :
    x (k + 1) = x k + s k :=
  (h.accept k hk).eq_add hs

/-- In an AR run, an unsuccessful iteration $k$ before termination keeps the iterate:
$x_{k+1} = x_k$. -/
theorem eq_of_not_succ {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) (hs : ρ k < P.η₁) :
    x (k + 1) = x k :=
  (h.accept k hk).eq_self hs

private theorem updates {K : ℕ} (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j) :
    ∀ k < K, ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin (ρ k) (σ k) (σ (k + 1)) :=
  fun _ hk => h.update fun j hj => hK j (hj.trans_lt hk)

/-- In an AR run, if iteration $K$ is reached, then $\sigma_k > 0$ for every $k \le K$. -/
theorem sigma_pos {K : ℕ} (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j) : ∀ k ≤ K, 0 < σ k :=
  pos_of_arUpdate P.γ₁_pos P.γ₂_pos (h.sigma_zero ▸ P.σ₀_pos) (h.updates hK)

/-- In an AR run, if iteration $K$ is reached, then $\sigma_k \ge \sigma_{\min}$ for every
$k \le K$. -/
theorem sigmaMin_le {K : ℕ} (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j) : ∀ k ≤ K, P.σmin ≤ σ k :=
  le_sigma_of_arUpdate P.σmin_nonneg P.one_le_γ₂ (h.sigma_zero ▸ P.σmin_le_σ₀) (h.updates hK)

/-- **Upper bound on the regularization weight** for any AR run, the mechanism of Lemmas 2.4.2,
3.3.2, 4.1.2, 13.1.14 and 14.1.6 of [cartis2022evaluation]. Let $\bar\sigma \in \mathbb{R}$, and
assume that every iteration $k$ before termination with $\sigma_k \ge \bar\sigma$ is very
successful: $\eta_2 \le \rho_k$. If iteration $K$ is reached, then for every $k \le K$
$$\sigma_{\min} \le \sigma_k, \qquad 0 < \sigma_k, \qquad \sigma_k \le \max(\sigma_0, \gamma_3
  \bar\sigma).$$
-/
theorem sigma_le_max {σbar : ℝ}
    (hforce : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → σbar ≤ σ k → P.η₂ ≤ ρ k) {K : ℕ}
    (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j) :
    ∀ k ≤ K, P.σmin ≤ σ k ∧ 0 < σ k ∧ σ k ≤ max P.σ₀ (P.γ₃ * σbar) := by
  have hmax := sigma_le_max_of_arUpdate P.γ₁_pos P.γ₂_pos P.γ₂_le_γ₃ P.one_le_γ₃
    (h.sigma_zero ▸ P.σ₀_pos) (h.updates hK)
    (fun k hk => hforce k fun j hj => hK j (hj.trans_lt hk))
  rw [h.sigma_zero] at hmax
  exact fun k hk => ⟨h.sigmaMin_le hK k hk, h.sigma_pos hK k hk, hmax k hk⟩

/-- **The iterates stay in a set.** In an AR run, let $C$ contain $x_0$, and let $x_k + s_k \in C$
for every successful iteration $k$ before termination with $x_k \in C$. Then $x_k \in C$ for
every reached iteration $k$. -/
theorem mem {C : Set E} (h0 : x 0 ∈ C)
    (hC : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → x k ∈ C → P.η₁ ≤ ρ k → x k + s k ∈ C) :
    ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → x k ∈ C := by
  intro k
  induction k with
  | zero => exact fun _ => h0
  | succ k ih =>
    intro hk
    have hk' : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j := fun j hj => hk j (Nat.lt_succ_of_le hj)
    have hxk := ih fun j hj => hk' j hj.le
    by_cases hs : P.η₁ ≤ ρ k
    · rw [h.eq_add_of_succ hk' hs]
      exact hC k hk' hxk hs
    · rwa [h.eq_of_not_succ hk' (not_le.1 hs)]

/-- **Lemma 2.4.1** of [cartis2022evaluation] for any AR run, counted up to iteration $k$ inclusive.
Let iteration $k$ be before termination and let $\sigma_{k+1} \le \sigma_{\max}$. Then
$$k + 1 \le |\mathcal{S}_k| \Bigl(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Bigr) +
  \frac{\log(\sigma_{\max} / \sigma_0)}{\log \gamma_2},$$
where $\mathcal{S}_k = \{j \le k \mid \eta_1 \le \rho_j\}$.

The set $\mathcal{S}_k$ is `Optimization.successSet (fun j => P.η₁ ≤ ρ j) k`. -/
theorem succ_count {σmax : ℝ} {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j)
    (hmax : σ (k + 1) ≤ σmax) :
    (k + 1 : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ ρ j) k).card * (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ := by
  rw [← h.sigma_zero]
  exact succ_le_of_arUpdate P.γ₁_pos P.γ₁_le_one P.one_lt_γ₂ (h.sigma_zero ▸ P.σ₀_pos)
    (fun j hj => h.update fun i hi => hk i (hi.trans hj)) hmax

/-- **Lemma 2.4.1** of [cartis2022evaluation], (2.4.8), with the indexing of the source. Let
iteration $k$ be reached and let $\sigma_k \le \sigma_{\max}$. Then
$$k \le |\mathcal{S}_k| \Bigl(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Bigr) +
  \frac{\log(\sigma_{\max} / \sigma_0)}{\log \gamma_2},$$
where $\mathcal{S}_k = \{j \le k \mid \eta_1 \le \rho_j\}$.

The set $\mathcal{S}_k$ is `Optimization.successSet (fun j => P.η₁ ≤ ρ j) k`, which contains $k$
itself if $k$ is successful. -/
theorem le_succ_count {σmax : ℝ} {k : ℕ} (hk : ∀ j < k, ¬ Stop stop₁ stop₂ j)
    (hmax : σ k ≤ σmax) :
    (k : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ ρ j) k).card * (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ := by
  rw [← h.sigma_zero]
  exact le_of_arUpdate P.γ₁_pos P.γ₁_le_one P.one_lt_γ₂ (h.sigma_zero ▸ P.σ₀_pos)
    (h.updates hk) hmax

/-- **Decrease on successful iterations**, (4.1.37) of [cartis2022evaluation]. In an AR run, let
iteration $k$ be before termination, let $w$ be an objective and $\mathrm{pred}_k > 0$, and let
the ratio be $\rho_k = (w(x_k) - w(x_k + s_k)) / \mathrm{pred}_k$. If iteration $k$ is
successful, then
$$x_{k+1} = x_k + s_k \qquad \text{and} \qquad w(x_k) - w(x_{k+1}) \ge \eta_1 \,
  \mathrm{pred}_k.$$
-/
theorem sub_ge_of_succ {w : E → ℝ} {pred : ℕ → ℝ} {k : ℕ}
    (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) (hρ : ρ k = reductionRatio w (x k) (s k) (pred k))
    (hpred : 0 < pred k) (hs : P.η₁ ≤ ρ k) :
    x (k + 1) = x k + s k ∧ P.η₁ * pred k ≤ w (x k) - w (x (k + 1)) :=
  ⟨h.eq_add_of_succ hk hs, (h.accept k hk).sub_ge hρ hpred hs⟩

/-- **Monotonicity of the objective.** In an AR run, let iteration $K$ be reached, and for every
$k < K$ let $\rho_k = (w(x_k) - w(x_k + s_k)) / \mathrm{pred}_k$ with $\mathrm{pred}_k > 0$.
Then $w(x_j) \le w(x_i)$ for all $i \le j \le K$. -/
theorem objective_antitone {w : E → ℝ} {pred : ℕ → ℝ} {K : ℕ}
    (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j)
    (hρ : ∀ k < K, ρ k = reductionRatio w (x k) (s k) (pred k)) (hpred : ∀ k < K, 0 < pred k) :
    ∀ i j, i ≤ j → j ≤ K → w (x j) ≤ w (x i) := by
  intro i j hij hjK
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have hjK' : j < K := hjK
    exact ((h.accept j fun i hi => hK i (hi.trans_lt hjK')).le (hρ j hjK') (hpred j hjK')).trans
      (ih hjK'.le)

/-- The counting core of the complexity theorems: if the weights are bounded by $\sigma_{\max}$ and
the number of successful iterations by $N \ge 0$ before termination, the run terminates at some
$k_\varepsilon$ with $k_\varepsilon + 1 \le (1 + |\log \gamma_1| / \log \gamma_2) N +
\log(\sigma_{\max} / \sigma_0) / \log \gamma_2 + 1$ and at most $N + 1$ derivative evaluations. -/
private theorem exists_isFirstHit_of_card_le {σmax : ℝ}
    (hσmax : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → σ k ≤ σmax) {N : ℝ} (hN : 0 ≤ N)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) →
      ((successSet (fun j => P.η₁ ≤ ρ j) k).card : ℝ) ≤ N) :
    ∃ kε, IsFirstHit (Stop stop₁ stop₂) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * N +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1 ∧
      (derivEvalCount (fun k => P.η₁ ≤ ρ k) kε : ℝ) ≤ N + 1 := by
  have hσ₀ : P.σ₀ ≤ σmax := h.sigma_zero ▸ hσmax 0 fun _ h => absurd h (Nat.not_lt_zero _)
  have hlog := P.log_γ₂_pos
  have hA : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by positivity
  have hB : 0 ≤ Real.log (σmax / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 hσ₀)) hlog.le
  refine exists_isFirstHit_evalCount_le_of_counting hA hN (by positivity) (fun k hk => ?_) hsucc
  have := h.succ_count hk (hσmax (k + 1) fun j hj => hk j (Nat.lt_succ_iff.1 hj))
  linarith

/-- **Complexity bound for AR runs**, the common end of the proofs of Theorems 2.4.4, 3.3.5, 4.1.5,
5.1.7, 6.2.3, 6.2.5, 6.3.1, 12.2.14 and 14.1.10 of [cartis2022evaluation]. In an AR run, let
$\sigma_k \le \sigma_{\max}$ for every reached iteration $k$. Let $(V_k)$ be a potential, such
as $V_k = f(x_k)$, and let $V_{\mathrm{low}} \in \mathbb{R}$ and $\delta > 0$ satisfy

* $V_{k+1} \le V_k$ for every iteration $k$ before termination;
* $V_k \ge V_{\mathrm{low}}$ for every reached iteration $k$;
* $V_k - V_{k+1} \ge \delta$ for every successful iteration $k$ such that the termination test
  fails at every $j \le k + 1$.

Then the run terminates at some iteration $k_\varepsilon$, and with
$\kappa_A = 1 + |\log \gamma_1| / \log \gamma_2$,
$$k_\varepsilon + 1 \le \kappa_A \frac{V_0 - V_{\mathrm{low}}}{\delta} + \frac{|\log \gamma_1| +
  \log(\sigma_{\max} / \sigma_0)}{\log \gamma_2} + 2, \qquad |\{j < k_\varepsilon \mid \eta_1
  \le \rho_j\}| + 1 \le \frac{V_0 - V_{\mathrm{low}}}{\delta} + 2.$$
The left sides are the numbers of evaluations of the objective and of its derivatives.

These are the constants (4.1.46) of the source. The term $2$ accounts for the initial evaluation
and for the last successful iteration. The bound at $k = 0$ gives $\sigma_{\max} \ge \sigma_0$.
The two counts are `Optimization.funEvalCount` and `Optimization.derivEvalCount`, and
termination at $k_\varepsilon$ is `Optimization.IsFirstHit`. -/
theorem exists_isFirstHit_of_decrease {σmax : ℝ}
    (hσmax : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → σ k ≤ σmax) {V : ℕ → ℝ} {Vlow δ : ℝ}
    (hδ : 0 < δ) (hmono : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → V (k + 1) ≤ V k)
    (hlow : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → Vlow ≤ V k)
    (hdec : ∀ k, (∀ j ≤ k + 1, ¬ Stop stop₁ stop₂ j) → P.η₁ ≤ ρ k → δ ≤ V k - V (k + 1)) :
    ∃ kε, IsFirstHit (Stop stop₁ stop₂) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((V 0 - Vlow) / δ) +
        ((|Real.log P.γ₁| + Real.log (σmax / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ ρ k) kε : ℝ) ≤ (V 0 - Vlow) / δ + 2 := by
  set succ := fun k => P.η₁ ≤ ρ k
  have hV0 : 0 ≤ V 0 - Vlow := sub_nonneg.2 (hlow 0 fun _ h => absurd h (Nat.not_lt_zero _))
  have hsucc : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) →
      ((successSet succ k).card : ℝ) ≤ (V 0 - Vlow) / δ + 1 := by
    intro k hk
    cases k with
    | zero =>
      have : (successSet succ 0).card ≤ 1 := card_successSet_le
      have : ((successSet succ 0).card : ℝ) ≤ 1 := by exact_mod_cast this
      have : (0 : ℝ) ≤ (V 0 - Vlow) / δ := div_nonneg hV0 hδ.le
      linarith
    | succ m =>
      have hcard := card_mul_le_of_decrease (c := δ) (k := m)
        (T := successSet succ m) successSet_subset_range
        (fun j hj => hmono j fun i hi => hk i (hi.trans (hj.trans m.le_succ)))
        (fun j hj => by
          rw [mem_successSet] at hj
          exact hdec j (fun i hi => hk i (hi.trans (Nat.succ_le_succ hj.1))) hj.2)
        (hlow (m + 1) fun j hj => hk j hj.le)
      have h1 : ((successSet succ m).card : ℝ) ≤ (V 0 - Vlow) / δ := by
        rw [le_div_iff₀ hδ]; linarith
      have h2 : ((successSet succ (m + 1)).card : ℝ) ≤ (successSet succ m).card + 1 := by
        exact_mod_cast card_successSet_add_one_le
      linarith
  obtain ⟨k, hk, hF, hD⟩ := h.exists_isFirstHit_of_card_le hσmax
    (by have := div_nonneg hV0 hδ.le; positivity) hsucc
  have hlog := P.log_γ₂_pos
  refine ⟨k, hk, hF.trans_eq ?_, hD.trans_eq ?_⟩
  · field_simp
    ring
  · ring

/-- **Complexity bound with the decrease at the current iterate**, the end of the proof of Theorem
2.4.4 (AR1) of [cartis2022evaluation]. Make the hypotheses of
`Optimization.IsARRun.exists_isFirstHit_of_decrease`, but require the decrease
$V_k - V_{k+1} \ge \delta$ at every successful iteration $k$ before termination. Then the run
terminates at some iteration $k_\varepsilon$, and with
$\kappa_A = 1 + |\log \gamma_1| / \log \gamma_2$,
$$k_\varepsilon + 1 \le \kappa_A \frac{V_0 - V_{\mathrm{low}}}{\delta} +
  \frac{\log(\sigma_{\max} / \sigma_0)}{\log \gamma_2} + 1, \qquad |\{j < k_\varepsilon \mid
  \eta_1 \le \rho_j\}| + 1 \le \frac{V_0 - V_{\mathrm{low}}}{\delta} + 1.$$
-/
theorem exists_isFirstHit_of_decrease_of_le {σmax : ℝ}
    (hσmax : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → σ k ≤ σmax) {V : ℕ → ℝ} {Vlow δ : ℝ}
    (hδ : 0 < δ) (hmono : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → V (k + 1) ≤ V k)
    (hlow : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → Vlow ≤ V k)
    (hdec : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → P.η₁ ≤ ρ k → δ ≤ V k - V (k + 1)) :
    ∃ kε, IsFirstHit (Stop stop₁ stop₂) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((V 0 - Vlow) / δ) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1 ∧
      (derivEvalCount (fun k => P.η₁ ≤ ρ k) kε : ℝ) ≤ (V 0 - Vlow) / δ + 1 := by
  have hV0 : 0 ≤ V 0 - Vlow := sub_nonneg.2 (hlow 0 fun _ h => absurd h (Nat.not_lt_zero _))
  refine h.exists_isFirstHit_of_card_le hσmax (div_nonneg hV0 hδ.le) fun k hk => ?_
  have hcard := card_mul_le_of_decrease (c := δ) (k := k)
    (T := successSet (fun j => P.η₁ ≤ ρ j) k) successSet_subset_range
    (fun j hj => hmono j fun i hi => hk i (hi.trans hj))
    (fun j hj => by
      rw [mem_successSet] at hj
      exact hdec j (fun i hi => hk i (hi.trans hj.1)) hj.2)
    (hlow (k + 1) fun j hj => hk j (Nat.lt_succ_iff.1 hj))
  rw [le_div_iff₀ hδ]; linarith

omit h in
/-- In an AR run without a post-step test, let iteration $N$ be reached and $x_N \ne x_0$. Then
there is a successful iteration $i < N$ with $x_{i+1} = x_N$. -/
theorem exists_last_succ (h : IsARRun P stop₁ step (fun _ => False) ρ x s σ) :
    ∀ N, (∀ j < N, ¬ stop₁ j) → x N ≠ x 0 → ∃ i < N, P.η₁ ≤ ρ i ∧ x (i + 1) = x N :=
  fun N hN => Optimization.exists_last_succ (succ := fun i => P.η₁ ≤ ρ i) N fun _ hi hs =>
    h.eq_of_not_succ (forall_le_not_stop_iff.2 fun j hj => hN j (hj.trans_lt hi)) (not_le.1 hs)

end General

section NoPostStepTest

variable {E : Type*} [Add E] {P : ARParams} {stop₁ step : ℕ → Prop} {ρ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ}

/-- **The iterate between successful iterations.** In an AR run without a post-step test, let
$i \le j$, let the Step-1 test fail at every $m < j$, and let no iteration $m$ with
$i \le m < j$ be successful. Then $x_j = x_i$. -/
theorem eq_of_forall_not_succ
    (h : IsARRun P stop₁ step (fun _ => False) ρ x s σ) {i j : ℕ} (hij : i ≤ j)
    (hj : ∀ m < j, ¬ stop₁ m) (hns : ∀ m, i ≤ m → m < j → ρ m < P.η₁) : x j = x i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    rw [h.eq_of_not_succ (IsARRun.forall_le_not_stop_iff.2 fun m hm => hj m
      (Nat.lt_succ_of_le hm)) (hns j hij j.lt_succ_self)]
    exact ih (fun m hm => hj m (hm.trans j.lt_succ_self))
      fun m hm1 hm2 => hns m hm1 (hm2.trans j.lt_succ_self)

/-- **Counting at the iterate and after the step.** In an AR run without a post-step test, let $Q$
be a property of iterates and let iteration $k$ be before termination. Then
$$|\{j \le k \mid \eta_1 \le \rho_j, \ Q(x_j)\}| \le |\{j \le k \mid \eta_1 \le \rho_j, \
  Q(x_{j+1})\}| + 1.$$

The iterate $x_j$ is $x_{i+1}$ for the previous successful iteration $i$, except before the
first successful iteration. -/
theorem card_successSet_le_card_succ_add_one
    (h : IsARRun P stop₁ step (fun _ => False) ρ x s σ) (Q : E → Prop) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stop₁ j) :
    (successSet (fun j => P.η₁ ≤ ρ j ∧ Q (x j)) k).card ≤
      (successSet (fun j => P.η₁ ≤ ρ j ∧ Q (x (j + 1))) k).card + 1 := by
  classical
  set T := successSet (fun j => P.η₁ ≤ ρ j ∧ Q (x j)) k
  set T' := successSet (fun j => P.η₁ ≤ ρ j ∧ Q (x (j + 1))) k
  set pr : ℕ → ℕ := fun j => Nat.findGreatest (fun i => P.η₁ ≤ ρ i) (j - 1)
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun j => ∃ i < j, P.η₁ ≤ ρ i)
  have h1 : (T.filter (fun j => ¬ ∃ i < j, P.η₁ ≤ ρ i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, T, mem_successSet] at ha hb
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact hb.2 ⟨a, hlt, ha.1.2.1⟩
    · exact ha.2 ⟨b, hlt, hb.1.2.1⟩
  have h0 : (T.filter (fun j => ∃ i < j, P.η₁ ≤ ρ i)).card ≤ T'.card := by
    refine Finset.card_le_card_of_injOn pr (fun j hj => ?_) (fun a ha b hb hab => ?_)
    · simp only [Finset.mem_coe, Finset.mem_filter, T, mem_successSet] at hj
      obtain ⟨⟨hjk, -, hQ⟩, i, hij, hi⟩ := hj
      have hspec : P.η₁ ≤ ρ (pr j) :=
        Nat.findGreatest_spec (P := fun i => P.η₁ ≤ ρ i) (m := i) (n := j - 1) (by omega) hi
      have hle : pr j ≤ j - 1 := Nat.findGreatest_le _
      have hxeq : x j = x (pr j + 1) :=
        h.eq_of_forall_not_succ (i := pr j + 1) (j := j) (by omega)
          (fun m hm => hk m (by omega)) fun m hm1 hm2 =>
          not_le.1 (Nat.findGreatest_is_greatest (P := fun i => P.η₁ ≤ ρ i) (n := j - 1)
            (show pr j < m by omega) (by omega))
      simp only [Finset.mem_coe, T', mem_successSet]
      exact ⟨by omega, hspec, hxeq ▸ hQ⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, T, mem_successSet] at ha hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have h1 : a ≤ pr b := Nat.le_findGreatest (by omega) ha.1.2.1
        have h2 : pr a ≤ a - 1 := Nat.findGreatest_le _
        obtain ⟨i, hi, -⟩ := ha.2
        have : pr a = pr b := hab
        omega
      · have h1 : b ≤ pr a := Nat.le_findGreatest (by omega) hb.1.2.1
        have h2 : pr b ≤ b - 1 := Nat.findGreatest_le _
        obtain ⟨i, hi, -⟩ := hb.2
        have : pr a = pr b := hab
        omega
  omega

end NoPostStepTest

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {P : ARParams}
  {stop₁ step stop₂ : ℕ → Prop} {x s : ℕ → E} {σ : ℕ → ℝ} {f : E → ℝ} {p : ℕ}

/-- **Decrease on successful iterations with exact Taylor models**, Lemma 4.1.1 and (4.1.37) of
[cartis2022evaluation]. Let $E$ be a real inner product space and $f : E \to \mathbb{R}$, and
consider an AR run with the Taylor ratio `Optimization.taylorRatio f p x s`. Let iteration $k$
be before termination, let the step decrease the model, $m_k(s_k) < m_k(0)$ with $m_k(s) =
T_{f,p}(x_k, s) + \sigma_k \|s\|^{p+1} / (p+1)!$, and let iteration $k$ be successful. Then
$$x_{k+1} = x_k + s_k \qquad \text{and} \qquad f(x_k) - f(x_{k+1}) \ge \eta_1
  \frac{\sigma_k}{(p+1)!} \|s_k\|^{p+1}.$$
-/
theorem sub_ge_of_succ_taylor (h : IsARRun P stop₁ step stop₂ (taylorRatio f p x s) x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j)
    (hm : regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
      regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    x (k + 1) = x k + s k ∧
      P.η₁ * (σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) ≤ f (x k) - f (x (k + 1)) := by
  have hσ : 0 ≤ σ k := (h.sigma_pos (K := k) (fun j hj => hk j hj.le) k le_rfl).le
  have hdec := lt_taylorDecrement_of_regularizedModel_lt hm
  have hpos : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
    lt_of_le_of_lt (by positivity) hdec
  obtain ⟨heq, hge⟩ := h.sub_ge_of_succ (w := f)
    (pred := fun k => (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) hk rfl hpos hs
  exact ⟨heq, (mul_le_mul_of_nonneg_left hdec.le P.η₁_pos.le).trans hge⟩

/-- **Lemma 4.1.2** of [cartis2022evaluation], with $\nabla^p f$ Lipschitz only at the iterates.
Consider an AR run with the Taylor ratio `Optimization.taylorRatio f p x s`. Let $C$ be convex
with $x_0 \in C$, and let $f$ be $C^p$ at every point of $C$. Assume that for every iteration
$k$ before termination
$$\|\nabla^p f(y) - \nabla^p f(x_k)\| \le L \|y - x_k\| \qquad (y \in C),$$
and that every step that satisfies the step conditions at an iteration $k$ before termination
has $x_k + s_k \in C$ and $m_k(s_k) < m_k(0)$. Then for every reached iteration $k$
$$x_k \in C, \qquad \sigma_{\min} \le \sigma_k \le \sigma_{\max} = \max\Bigl(\sigma_0,
  \frac{\gamma_3 L}{1 - \eta_2}\Bigr).$$

The Lipschitz condition at the iterates is the condition (14.2.9) of the source when the
iterates lie in the anchor set. -/
theorem sigma_le_anchored (h : IsARRun P stop₁ step stop₂ (taylorRatio f p x s) x s σ)
    {C : Set E} {L : ℝ} (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f (x k)‖ ≤ L * ‖y - x k‖) (hx0 : x 0 ∈ C)
    (hstep : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → step k →
      x k + s k ∈ C ∧ regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
        regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0) :
    ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P L := by
  have hmem := h.mem (C := C) hx0 fun k hk _ _ => (hstep k hk (h.step_of_forall_le hk)).1
  have hforce : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → L / (1 - P.η₂) ≤ σ k →
      P.η₂ ≤ taylorRatio f p x s k := by
    intro k hk hσk
    obtain ⟨hxs, hm⟩ := hstep k hk (h.step_of_forall_le hk)
    have hσpos : 0 < σ k := h.sigma_pos (K := k) (fun j hj => hk j hj.le) k le_rfl
    have hdec := (lt_taylorDecrement_of_regularizedModel_lt hm).le
    have hfac : (0 : ℝ) < (p + 1)! := by positivity
    refine le_reductionRatio_of_lipschitzAnchored hC hf (hL k hk) (hmem k fun j hj => hk j hj.le)
      hxs
      (ne_zero_of_regularizedModel_lt hm) (c := 1 / ((p + 1)! : ℝ)) (by positivity) hσpos
      (by rw [one_div_mul_eq_div]; exact hdec) ?_
    rw [div_le_iff₀ P.one_sub_η₂_pos] at hσk
    rw [mul_one_div_cancel hfac.ne', one_mul]
    exact hσk
  intro k hk
  obtain ⟨hmin, -, hmax⟩ := h.sigma_le_max hforce hk k le_rfl
  refine ⟨hmem k hk, hmin, hmax.trans_eq ?_⟩
  rw [arSigmaMax_def, mul_div_assoc]

/-- **Lemma 4.1.2** of [cartis2022evaluation], (4.1.19), for every AR method with exact Taylor
models, also on a convex feasible set; §6.2.2 of the source states that Lemmas 4.1.1 and 4.1.2
continue to hold there. Consider an AR run with the Taylor ratio
`Optimization.taylorRatio f p x s`. Let $C$ be convex with $x_0 \in C$, let $f$ be $C^p$ at
every point of $C$, and let $\nabla^p f$ be Lipschitz continuous on $C$ with constant $L$.
Assume that every step that satisfies the step conditions at an iteration $k$ before termination
has $x_k + s_k \in C$ and decreases the model, $m_k(s_k) < m_k(0)$ (4.1.10). Then for every
reached iteration $k$
$$x_k \in C, \qquad \sigma_{\min} \le \sigma_k \le \sigma_{\max} = \max\Bigl(\sigma_0,
  \frac{\gamma_3 L}{1 - \eta_2}\Bigr).$$

A post-step test such as the test $m_k(s_k) = m_k(0)$ of ARqp can supply the strict model
decrease before termination. -/
theorem sigma_le (h : IsARRun P stop₁ step stop₂ (taylorRatio f p x s) x s σ) {C : Set E}
    {L : ℝ} (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : IteratedFDerivLipschitzOn f p L C) (hx0 : x 0 ∈ C)
    (hstep : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → step k →
      x k + s k ∈ C ∧ regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
        regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0) :
    ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P L := by
  have hmem := h.mem (C := C) hx0 fun k hk _ _ => (hstep k hk (h.step_of_forall_le hk)).1
  exact h.sigma_le_anchored hC hf (fun k hk y hy => iteratedFDerivLipschitzOn_iff.1 hL y hy (x k)
    (hmem k fun j hj => hk j hj.le)) hx0 hstep

end Taylor

end IsARRun

section Existence

/-- The previous iterate, weight and step of a run: `none` at iteration $0$, and
$(x_k, \sigma_k, s_k)$ at iteration $k + 1$.

A termination test that reads the previous iteration may depend on this value. An example is the
third-order test of ARp, through the set $\mathcal{M}_k$ of (4.1.14) of [cartis2022evaluation]. -/
def prevIterate {E : Type*} (x s : ℕ → E) (σ : ℕ → ℝ) : ℕ → Option (E × ℝ × E)
  | 0 => none
  | k + 1 => some (x k, σ k, s k)

/-- At iteration $0$ there is no previous iteration. -/
@[simp]
theorem prevIterate_zero {E : Type*} (x s : ℕ → E) (σ : ℕ → ℝ) : prevIterate x s σ 0 = none :=
  rfl

/-- At iteration $k + 1$ the previous iteration is $(x_k, \sigma_k, s_k)$. -/
@[simp]
theorem prevIterate_succ {E : Type*} (x s : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    prevIterate x s σ (k + 1) = some (x k, σ k, s k) := rfl

variable {E : Type*} [Add E]

/-- **Existence of AR runs** whose termination test reads the current iterate, the current weight
and the previous iteration (`Optimization.prevIterate`). Let $P$ be AR constants, $\mathrm{Inv}$
a property of iterates (for example membership in a feasible set), and $R$ any ratio function.
Assume that for every previous iteration, every iterate $y$ with $\mathrm{Inv}(y)$ and every
weight $\sigma \ge \sigma_{\min}$ with $\sigma > 0$ at which the test fails, there is a step $s$
with $\mathrm{stepOK}(y, \sigma, s)$ and $\mathrm{Inv}(y + s)$. Then for every $x_0$ with
$\mathrm{Inv}(x_0)$ there is a run from $x_0$ with no post-step test, the step conditions
$\mathrm{stepOK}(x_k, \sigma_k, s_k)$ and the ratio $\rho_k = R(x_k, \sigma_k, s_k)$, and
$\mathrm{Inv}(x_k)$ holds at every reached iteration $k$.

The proof chooses the new weights at the left ends of the intervals of (2.4.4). -/
theorem exists_isARRun_prev (P : ARParams) {Inv : E → Prop}
    {test : Option (E × ℝ × E) → E → ℝ → Prop} {stepOK : E → ℝ → E → Prop}
    (R : E → ℝ → E → ℝ)
    (hstep : ∀ prev y σ, Inv y → P.σmin ≤ σ → 0 < σ → ¬ test prev y σ →
      ∃ s, stepOK y σ s ∧ Inv (y + s))
    {x₀ : E} (hx₀ : Inv x₀) :
    ∃ x s : ℕ → E, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧
      IsARRun P (fun k => test (prevIterate x s σ k) (x k) (σ k))
        (fun k => stepOK (x k) (σ k) (s k)) (fun _ => False) (fun k => R (x k) (σ k) (s k))
        x s σ ∧
      ∀ k, (∀ j < k, ¬ test (prevIterate x s σ j) (x j) (σ j)) → Inv (x k) := by
  classical
  -- states `(x_k, σ_k, s_k, previous iteration)`
  let good : Option (E × ℝ × E) → E → ℝ → E → Prop := fun prev y σ s =>
    ¬ test prev y σ → stepOK y σ s ∧ Inv (y + s)
  have hchoose : ∀ prev y σ, Inv y → P.σmin ≤ σ → 0 < σ → ∃ s, good prev y σ s := by
    intro prev y σ hy hσ hσ0
    by_cases ht : test prev y σ
    · exact ⟨y, fun h' => absurd ht h'⟩
    · obtain ⟨s, hs⟩ := hstep prev y σ hy hσ hσ0 ht
      exact ⟨s, fun _ => hs⟩
  obtain ⟨s₀, hs₀⟩ := hchoose none x₀ P.σ₀ hx₀ P.σmin_le_σ₀ P.σ₀_pos
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant
    (α := E × ℝ × E × Option (E × ℝ × E))
    (init := fun a => a = (x₀, P.σ₀, s₀, none))
    (inv := fun _ a => Inv a.1 ∧ P.σmin ≤ a.2.1 ∧ 0 < a.2.1 ∧ good a.2.2.2 a.1 a.2.1 a.2.2.1)
    (stop := fun _ a => test a.2.2.2 a.1 a.2.1)
    (step := fun _ a b => ARAcceptance P (R a.1 a.2.1 a.2.2.1) a.1 a.2.2.1 b.1 a.2.1 b.2.1 ∧
      b.2.2.2 = some (a.1, a.2.1, a.2.2.1))
    ⟨_, rfl⟩
    (fun a ha => by
      subst ha
      exact ⟨hx₀, P.σmin_le_σ₀, P.σ₀_pos, hs₀⟩)
    (fun k a ha hnot => by
      obtain ⟨hInv, hmin, hpos, hgood⟩ := ha
      obtain ⟨hstepa, hInvs⟩ := hgood hnot
      obtain ⟨σ', hacc, hmin', hpos'⟩ :=
        exists_arAcceptance P (R a.1 a.2.1 a.2.2.1) a.1 a.2.2.1 hmin
      set x' := if P.η₁ ≤ R a.1 a.2.1 a.2.2.1 then a.1 + a.2.2.1 else a.1
      have hInv' : Inv x' := by
        rcases hacc.eq_add_or_eq_self with h' | h'
        · rw [h']; exact hInvs
        · rw [h']; exact hInv
      obtain ⟨s', hs'⟩ := hchoose (some (a.1, a.2.1, a.2.2.1)) x' σ' hInv' hmin' (hpos' hpos)
      exact ⟨(x', σ', s', some (a.1, a.2.1, a.2.2.1)), ⟨hInv', hmin', hpos' hpos, hs'⟩, hacc, rfl⟩)
  set x : ℕ → E := fun k => (r k).1
  set σ : ℕ → ℝ := fun k => (r k).2.1
  set s : ℕ → E := fun k => (r k).2.2.1
  have hprev : ∀ k, (∀ j < k, ¬ test (r j).2.2.2 (r j).1 (r j).2.1) →
      (r k).2.2.2 = prevIterate x s σ k := by
    intro k hk
    cases k with
    | zero => rw [hr0]; rfl
    | succ k => exact (hr k fun j hj => hk j (Nat.lt_succ_of_le hj)).2.2
  have hstopped : ∀ k, (∀ j < k, ¬ test (prevIterate x s σ j) (x j) (σ j)) →
      ∀ j < k, ¬ test (r j).2.2.2 (r j).1 (r j).2.1 := by
    intro k
    induction k with
    | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk j hj
      have ih' := ih fun i hi => hk i (hi.trans k.lt_succ_self)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih' j hj
      · rw [hprev j ih']
        exact hk j j.lt_succ_self
  have hle : ∀ k, (∀ j ≤ k, ¬ (test (prevIterate x s σ j) (x j) (σ j) ∨ False)) →
      ∀ j ≤ k, ¬ test (r j).2.2.2 (r j).1 (r j).2.1 := by
    intro k hk j hj
    exact hstopped (k + 1) (fun i hi => fun h' => hk i (Nat.lt_succ_iff.1 hi) (Or.inl h')) j
      (Nat.lt_succ_of_le hj)
  refine ⟨x, s, σ, by simp [x, hr0], ⟨by simp [σ, hr0], ?_, ?_⟩, ?_⟩
  · intro k hk h1
    have hk' := hle k (fun j hj => by
      rcases hj.lt_or_eq with hj | rfl
      · exact hk j hj
      · simpa using h1)
    have hp := hprev k fun j hj => hk' j hj.le
    have hgood := (hr k hk').1.2.2.2
    exact (hgood (by rw [hp]; exact h1)).1
  · intro k hk
    exact (hr k (hle k hk)).2.1
  · intro k hk
    cases k with
    | zero => simpa [x, hr0] using hx₀
    | succ k =>
      have hk' := hstopped (k + 1) hk
      have hall : ∀ j ≤ k, ¬ test (r j).2.2.2 (r j).1 (r j).2.1 :=
        fun j hj => hk' j (Nat.lt_succ_of_le hj)
      obtain ⟨⟨hInv, -, -, hgood⟩, hacc, -⟩ := hr k hall
      rcases hacc.eq_add_or_eq_self with h' | h'
      · change Inv (r (k + 1)).1
        rw [h']
        exact (hgood (hall k le_rfl)).2
      · change Inv (r (k + 1)).1
        rw [h']
        exact hInv

/-- **Existence of AR runs** with a termination test that reads only the current iterate. This
covers AR1, AR2, ARp with $q \le 2$, ARp-CC, ARp1-CC, ARpLE-CC and the inner runs of TPp-GC. Let
$P$ be AR constants, $\mathrm{Inv}$ a property of iterates, and $R$ any ratio function. Assume
that for every iterate $y$ with $\mathrm{Inv}(y)$ at which the test fails and every weight
$\sigma \ge \sigma_{\min}$ with $\sigma > 0$, there is a step $s$ with
$\mathrm{stepOK}(y, \sigma, s)$ and $\mathrm{Inv}(y + s)$. Then for every $x_0$ with
$\mathrm{Inv}(x_0)$ there is a run from $x_0$ with no post-step test, the step conditions
$\mathrm{stepOK}(x_k, \sigma_k, s_k)$ and the ratio $\rho_k = R(x_k, \sigma_k, s_k)$, and
$\mathrm{Inv}(x_k)$ holds at every reached iteration $k$. -/
theorem exists_isARRun (P : ARParams) {Inv : E → Prop} {test : E → Prop}
    {stepOK : E → ℝ → E → Prop} (R : E → ℝ → E → ℝ)
    (hstep : ∀ y σ, Inv y → P.σmin ≤ σ → 0 < σ → ¬ test y → ∃ s, stepOK y σ s ∧ Inv (y + s))
    {x₀ : E} (hx₀ : Inv x₀) :
    ∃ x s : ℕ → E, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧
      IsARRun P (fun k => test (x k)) (fun k => stepOK (x k) (σ k) (s k)) (fun _ => False)
        (fun k => R (x k) (σ k) (s k)) x s σ ∧
      ∀ k, (∀ j < k, ¬ test (x j)) → Inv (x k) :=
  exists_isARRun_prev P (test := fun _ y _ => test y) R
    (fun _ y σ hy hσ hσ0 ht => hstep y σ hy hσ hσ0 ht) hx₀

end Existence

end Optimization
