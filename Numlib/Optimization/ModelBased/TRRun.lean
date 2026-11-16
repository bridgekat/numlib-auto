/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Existence
import Numlib.Optimization.ModelBased.TrustRegionUpdate
import Numlib.Optimization.ModelBased.RatioTest

/-!
# Generic runs of trust-region methods

The trust-region methods of [cartis2022evaluation] share Steps 3 and 4 of each iteration. These
methods are TR1 (Algorithm 2.3.1), TR2 (Algorithm 3.2.1), TRε (Algorithm 3.4.1), TRq (Algorithm
12.2.1) and its variant for simple constraints in §14.2, and also the trial iterations of TRqIDA
(Algorithm 13.1.1) and TRqEDA (Algorithm 13.3.1). Given the ratio $\rho_k$ of the achieved to the
predicted decrease, the trial point $x_k + s_k$ is accepted if and only if $\rho_k \ge \eta_1$, and
the radius is updated by the rule (2.3.7). The methods differ only in the termination test of Step
1, in the conditions of Step 2 on the step (which include the trust-region constraint), and in the
predicted decrease that enters $\rho_k$.

This file defines a run of a generic trust-region method, in which the rules apply only before
termination. It proves for every run that the radii stay positive and bounded below, that the number
of iterations is bounded in terms of the number of successful iterations, and that successful
iterations decrease the objective. It also shows that runs exist when an admissible step exists
whenever the termination test fails.

## Main definitions

* `Optimization.TRParams`: the constants $\Delta_0, \eta_1, \eta_2, \gamma_1, \gamma_2, \gamma_3$ of
  (2.3.3).
* `Optimization.TRAcceptance`: Steps 3 and 4 of one iteration, the acceptance of the trial point and
  the radius update.
* `Optimization.IsTRRun`: a run of a trust-region method, with the rules imposed only before
  termination.

## Main results

* `Optimization.exists_trAcceptance`: an admissible new radius $\Delta' \le \Delta$ always exists.
* `Optimization.IsTRRun.delta_ge`: the lower bound $\Delta_k \ge \min(\Delta_0, \gamma_1 \theta_k)$
  on the radius, the mechanism of Lemmas 2.3.4, 3.2.5 and 12.2.3 of [cartis2022evaluation].
* `Optimization.IsTRRun.succ_count`: the number of iterations is bounded in terms of the number of
  successful iterations, as in Lemma 2.3.1 of [cartis2022evaluation].
* `Optimization.IsTRRun.sub_ge_of_succ`: a successful iteration decreases the objective by at least
  $\eta_1$ times the predicted decrease.
* `Optimization.exists_isTRRun`: a run exists from every starting point if an admissible step exists
  whenever the termination test fails.

## Implementation notes

* The conditions on the step and the ratio may depend on the iteration counter, for example through
  the model Hessians $B_k$ of TR1, and also on the current iterate and radius.
* An upper bound $\Delta_{k+1} \le \Delta_{\max}$, which TRq imposes, is an additional condition in
  the predicates of the specific methods. The new radius that `Optimization.exists_trAcceptance`
  gives never exceeds $\Delta_k$, so it satisfies every such bound.
* The rules before termination are stated with `Optimization.UntilHit`: a rule holds at iteration
  $k$ if the termination test failed at every $j \le k$.
-/

namespace Optimization

/-- The constants of a trust-region method, (2.3.3) of [cartis2022evaluation] and Step 0 of
Algorithms 2.3.1, 12.2.1 and 13.1.1: the initial radius $\Delta_0 > 0$, the acceptance
thresholds $0 < \eta_1 \le \eta_2 < 1$, and the radius factors
$0 < \gamma_1 \le \gamma_2 < 1 \le \gamma_3$. -/
structure TRParams where
  /-- The initial trust-region radius $\Delta_0$. -/
  Δ₀ : ℝ
  /-- The threshold $\eta_1$ of the ratio for successful iterations. -/
  η₁ : ℝ
  /-- The threshold $\eta_2$ of the ratio for very successful iterations. -/
  η₂ : ℝ
  /-- The smallest shrinking factor $\gamma_1$ of the radius. -/
  γ₁ : ℝ
  /-- The largest shrinking factor $\gamma_2$ of the radius. -/
  γ₂ : ℝ
  /-- The largest expansion factor $\gamma_3$ of the radius. -/
  γ₃ : ℝ
  /-- The initial radius is positive: $\Delta_0 > 0$. -/
  Δ₀_pos : 0 < Δ₀
  /-- The first threshold is positive: $\eta_1 > 0$. -/
  η₁_pos : 0 < η₁
  /-- The thresholds are ordered: $\eta_1 \le \eta_2$. -/
  η₁_le_η₂ : η₁ ≤ η₂
  /-- The second threshold is less than one: $\eta_2 < 1$. -/
  η₂_lt_one : η₂ < 1
  /-- The smallest shrinking factor is positive: $\gamma_1 > 0$. -/
  γ₁_pos : 0 < γ₁
  /-- The shrinking factors are ordered: $\gamma_1 \le \gamma_2$. -/
  γ₁_le_γ₂ : γ₁ ≤ γ₂
  /-- The largest shrinking factor is less than one: $\gamma_2 < 1$. -/
  γ₂_lt_one : γ₂ < 1
  /-- The expansion factor is at least one: $\gamma_3 \ge 1$. -/
  one_le_γ₃ : 1 ≤ γ₃

namespace TRParams

variable (P : TRParams)

/-- The largest shrinking factor is positive: $\gamma_2 > 0$. -/
theorem γ₂_pos : 0 < P.γ₂ := P.γ₁_pos.trans_le P.γ₁_le_γ₂

/-- The smallest shrinking factor is at most one: $\gamma_1 \le 1$. -/
theorem γ₁_le_one : P.γ₁ ≤ 1 := P.γ₁_le_γ₂.trans P.γ₂_lt_one.le

/-- The expansion factor is positive: $\gamma_3 > 0$. -/
theorem γ₃_pos : 0 < P.γ₃ := one_pos.trans_le P.one_le_γ₃

/-- The second threshold is positive: $\eta_2 > 0$. -/
theorem η₂_pos : 0 < P.η₂ := P.η₁_pos.trans_le P.η₁_le_η₂

/-- The number $1 - \eta_2$ is positive. -/
theorem one_sub_η₂_pos : 0 < 1 - P.η₂ := sub_pos.2 P.η₂_lt_one

/-- The smallest shrinking factor is less than one: $\gamma_1 < 1$. -/
theorem γ₁_lt_one : P.γ₁ < 1 := P.γ₁_le_γ₂.trans_lt P.γ₂_lt_one

end TRParams

section Acceptance

variable {E : Type*} [Add E]

/-- Steps 3 and 4 of one iteration of a trust-region method, (2.3.6)–(2.3.7), (12.2.4)–(12.2.5) and
(13.1.16)–(13.1.17) of [cartis2022evaluation]. Given the ratio $\rho$, the pair $(x', \Delta')$
is an **admissible outcome** of the iteration from $x$ with step $s$ and radius $\Delta$ if
$$x' = \begin{cases} x + s & \text{if } \rho \ge \eta_1, \\ x & \text{otherwise,} \end{cases}$$
and the new radius $\Delta'$ satisfies the update rule (2.3.7), `Optimization.TRUpdate`. -/
def TRAcceptance (P : TRParams) (ρ : ℝ) (x s x' : E) (Δ Δ' : ℝ) : Prop :=
  x' = (if P.η₁ ≤ ρ then x + s else x) ∧ TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ ρ Δ Δ'

variable {P : TRParams} {ρ : ℝ} {x s x' : E} {Δ Δ' : ℝ}

/-- The defining property of `Optimization.TRAcceptance`: $x'$ is $x + s$ if $\rho \ge \eta_1$ and
$x$ otherwise, and $\Delta'$ satisfies the update rule (2.3.7). -/
theorem trAcceptance_iff :
    TRAcceptance P ρ x s x' Δ Δ' ↔
      x' = (if P.η₁ ≤ ρ then x + s else x) ∧ TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ ρ Δ Δ' :=
  Iff.rfl

namespace TRAcceptance

variable (h : TRAcceptance P ρ x s x' Δ Δ')
include h

/-- In an admissible outcome, the new radius satisfies the update rule (2.3.7). -/
theorem update : TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ ρ Δ Δ' := h.2

/-- In an admissible outcome of a successful iteration ($\rho \ge \eta_1$), the new iterate is the
trial point: $x' = x + s$. -/
theorem eq_add (hρ : P.η₁ ≤ ρ) : x' = x + s := by
  rw [h.1, ite_eq_left hρ]

/-- In an admissible outcome of an unsuccessful iteration ($\rho < \eta_1$), the iterate does not
change: $x' = x$. -/
theorem eq_self (hρ : ρ < P.η₁) : x' = x := by
  rw [h.1, ite_eq_right (not_le.2 hρ)]

/-- In an admissible outcome, the new radius is positive if the old radius is positive. -/
theorem pos (hΔ : 0 < Δ) : 0 < Δ' :=
  h.2.pos P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one hΔ

/-- **Decrease on a successful iteration.** Let $(x', \Delta')$ be an admissible outcome, and let
$\rho = (f(x) - f(x + s)) / \mathrm{pred}$ with $\mathrm{pred} > 0$. If $\rho \ge \eta_1$, then
$$f(x) - f(x') \ge \eta_1 \, \mathrm{pred}.$$
-/
theorem sub_ge {f : E → ℝ} {pred : ℝ} (hρ : ρ = reductionRatio f x s pred) (hpred : 0 < pred)
    (hs : P.η₁ ≤ ρ) : P.η₁ * pred ≤ f x - f x' := by
  rw [h.eq_add hs]
  exact sub_le_of_le_reductionRatio hpred (hρ ▸ hs)

/-- Let $(x', \Delta')$ be an admissible outcome, and let $\rho = (f(x) - f(x + s)) / \mathrm{pred}$
with $\mathrm{pred} > 0$. Then the objective does not increase: $f(x') \le f(x)$. -/
theorem le {f : E → ℝ} {pred : ℝ} (hρ : ρ = reductionRatio f x s pred) (hpred : 0 < pred) :
    f x' ≤ f x := by
  by_cases hs : P.η₁ ≤ ρ
  · have := h.sub_ge hρ hpred hs
    nlinarith [P.η₁_pos]
  · rw [h.eq_self (not_le.1 hs)]

end TRAcceptance

/-- **Existence of the next radius.** Let $\Delta \ge 0$, and let the new iterate be $x + s$ if
$\rho \ge \eta_1$ and $x$ otherwise. Then there is a new radius $\Delta'$ that gives an
admissible outcome, with $\Delta' \le \Delta$, and with $\Delta' > 0$ if $\Delta > 0$.

The proof takes $\Delta' = \gamma_2 \Delta$ after an unsuccessful iteration ($\rho < \eta_1$)
and $\Delta' = \Delta$ after a successful iteration; the statement does not record this choice.
Because $\Delta' \le \Delta$, the new radius keeps every upper bound $\Delta \le \Delta_{\max}$. -/
theorem exists_trAcceptance (P : TRParams) (ρ : ℝ) (x s : E) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ Δ', TRAcceptance P ρ x s (if P.η₁ ≤ ρ then x + s else x) Δ Δ' ∧ Δ' ≤ Δ ∧
      (0 < Δ → 0 < Δ') := by
  refine ⟨if ρ < P.η₁ then P.γ₂ * Δ else Δ, ⟨rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h2
    rw [ite_eq_right (not_lt.2 (P.η₁_le_η₂.trans h2))]
    exact ⟨le_rfl, le_mul_of_one_le_left hΔ P.one_le_γ₃⟩
  · intro h1 _
    rw [ite_eq_right (not_lt.2 h1)]
    exact ⟨mul_le_of_le_one_left hΔ P.γ₂_lt_one.le, le_rfl⟩
  · intro h1
    rw [ite_eq_left h1]
    exact ⟨mul_le_mul_of_nonneg_right P.γ₁_le_γ₂ hΔ, le_rfl⟩
  · split_ifs
    · exact mul_le_of_le_one_left hΔ P.γ₂_lt_one.le
    · exact le_rfl
  · intro hΔ'
    split_ifs
    · exact mul_pos P.γ₂_pos hΔ'
    · exact hΔ'

/-- An iteration with ratio $\rho \ge 1$ is very successful and can keep the radius. If $\rho \ge 1$
and $\Delta \ge 0$, then $x' = x + s$ and $\Delta' = \Delta$ give an admissible outcome. -/
theorem trAcceptance_of_one_le (P : TRParams) {ρ : ℝ} (hρ : 1 ≤ ρ) (x s : E) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) : TRAcceptance P ρ x s (x + s) Δ Δ := by
  have h1 : P.η₁ ≤ ρ := by linarith [P.η₁_le_η₂, P.η₂_lt_one]
  have h2 : P.η₂ ≤ ρ := by linarith [P.η₂_lt_one]
  refine ⟨by rw [ite_eq_left h1], fun _ => ⟨le_rfl, le_mul_of_one_le_left hΔ P.one_le_γ₃⟩,
    fun _ h => absurd h (not_lt.2 h2), fun h => absurd h (not_lt.2 h1)⟩

end Acceptance

/-- A **run of a trust-region method**, Steps 2–4 of Algorithms 2.3.1, 3.2.1, 3.4.1 and 12.2.1 of
[cartis2022evaluation]. It consists of iterates $x_k$, trial steps $s_k$, radii $\Delta_k$ and
ratios $\rho_k$ such that
* the initial radius is $\Delta_0$ of the parameters `P`;
* at every iteration $k$ before termination, the step $s_k$ satisfies the conditions of Step 2;
* at every iteration $k$ before termination, $(x_{k+1}, \Delta_{k+1})$ is an admissible outcome
  of Steps 3 and 4, `Optimization.TRAcceptance`.

Here `stop k` is the termination test of Step 1 at iteration $k$, and `step k` is the set of
conditions of Step 2 on the trial step $s_k$, which include the trust-region constraint.
Iteration $k$ is before termination if the test failed at every $j \le k$. Iteration $k$ is
successful if and only if $\rho_k \ge \eta_1$. -/
structure IsTRRun {E : Type*} [Add E] (P : TRParams) (stop step : ℕ → Prop) (ρ : ℕ → ℝ)
    (x s : ℕ → E) (Δ : ℕ → ℝ) : Prop where
  /-- The initial radius is the constant $\Delta_0$ of the parameters. -/
  delta_zero : Δ 0 = P.Δ₀
  /-- The conditions of Step 2 on the trial step hold at every iteration before termination. -/
  step : UntilHit stop step
  /-- Steps 3 and 4 give an admissible outcome at every iteration before termination. -/
  accept : UntilHit stop fun k => TRAcceptance P (ρ k) (x k) (s k) (x (k + 1)) (Δ k) (Δ (k + 1))

namespace IsTRRun

variable {E : Type*} [Add E] {P : TRParams} {stop step : ℕ → Prop} {ρ : ℕ → ℝ} {x s : ℕ → E}
  {Δ : ℕ → ℝ} (h : IsTRRun P stop step ρ x s Δ)
include h

/-- A run with a stronger step condition is also a run with a weaker step condition. -/
theorem mono {step' : ℕ → Prop} (hst : ∀ k, step k → step' k) :
    IsTRRun P stop step' ρ x s Δ :=
  ⟨h.delta_zero, h.step.mono hst, h.accept⟩

/-- If the termination test failed at every $j \le k$, then $\Delta_{k+1}$ satisfies the update rule
(2.3.7) with ratio $\rho_k$. -/
theorem update {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j) :
    TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ (ρ k) (Δ k) (Δ (k + 1)) :=
  (h.accept k hk).update

/-- If the termination test failed at every $j \le k$ and iteration $k$ is successful
($\rho_k \ge \eta_1$), then $x_{k+1} = x_k + s_k$. -/
theorem eq_add_of_succ {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j) (hs : P.η₁ ≤ ρ k) :
    x (k + 1) = x k + s k :=
  (h.accept k hk).eq_add hs

/-- If the termination test failed at every $j \le k$ and iteration $k$ is unsuccessful
($\rho_k < \eta_1$), then $x_{k+1} = x_k$. -/
theorem eq_of_not_succ {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j) (hs : ρ k < P.η₁) :
    x (k + 1) = x k :=
  (h.accept k hk).eq_self hs

private theorem updates {K : ℕ} (hK : ∀ j < K, ¬ stop j) :
    ∀ k < K, TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ (ρ k) (Δ k) (Δ (k + 1)) :=
  fun _ hk => h.update fun j hj => hK j (hj.trans_lt hk)

/-- The radii are positive up to and including the first termination index: if the termination test
failed at every $j < K$, then $\Delta_k > 0$ for all $k \le K$. -/
theorem delta_pos {K : ℕ} (hK : ∀ j < K, ¬ stop j) : ∀ k ≤ K, 0 < Δ k :=
  pos_of_trUpdate P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one (h.delta_zero ▸ P.Δ₀_pos) (h.updates hK)

/-- **Lower bound on the radius** for every run of a trust-region method. Let $(\theta_k)$ be a real
sequence with $\theta_{k+1} \le \theta_k$ for all $k < K$. Suppose that the termination test
failed at every $j < K$, and that every iteration $k < K$ with $\Delta_k < \theta_k$ is very
successful ($\rho_k \ge \eta_2$). Then
$$\Delta_k \ge \min(\Delta_0, \gamma_1 \theta_k) \quad \text{for all } k \le K.$$

This is the mechanism of Lemmas 2.3.4, 3.2.5 and 12.2.3 of [cartis2022evaluation]. The proof
specializes `Optimization.le_delta_of_trUpdate`. -/
theorem delta_ge {θ : ℕ → ℝ} {K : ℕ} (hK : ∀ j < K, ¬ stop j)
    (hθ : ∀ k < K, θ (k + 1) ≤ θ k) (hforce : ∀ k < K, Δ k < θ k → P.η₂ ≤ ρ k) :
    ∀ k ≤ K, min P.Δ₀ (P.γ₁ * θ k) ≤ Δ k := by
  have := le_delta_of_trUpdate P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one (h.delta_zero ▸ P.Δ₀_pos)
    (h.updates hK) hθ hforce
  rwa [h.delta_zero] at this

/-- **Lower bound on the next radius.** Under the hypotheses of `Optimization.IsTRRun.delta_ge`,
$$\Delta_{k+1} \ge \min(\Delta_0, \gamma_1 \theta_k) \quad \text{for all } k < K.$$
-/
theorem delta_succ_ge {θ : ℕ → ℝ} {K : ℕ} (hK : ∀ j < K, ¬ stop j)
    (hθ : ∀ k < K, θ (k + 1) ≤ θ k) (hforce : ∀ k < K, Δ k < θ k → P.η₂ ≤ ρ k) :
    ∀ k < K, min P.Δ₀ (P.γ₁ * θ k) ≤ Δ (k + 1) := by
  have := le_delta_succ_of_trUpdate P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one (h.delta_zero ▸ P.Δ₀_pos)
    (h.updates hK) hθ hforce
  rwa [h.delta_zero] at this

/-- **Lemma 2.3.1** of [cartis2022evaluation] for every run of a trust-region method, with $k + 1$
updates. Let $\mathcal{S}_k = \{ j \le k : \rho_j \ge \eta_1 \}$ be the set of successful
iterations up to $k$. If the termination test failed at every $j \le k$ and
$0 < \Delta_{\min} \le \Delta_{k+1}$, then
$$k + 1 \le |\mathcal{S}_k| \left(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\right) +
  \frac{1}{|\log \gamma_2|} \left|\log \frac{\Delta_{\min}}{\Delta_0}\right|.$$
-/
theorem succ_count {Δmin : ℝ} {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j) (hmin : 0 < Δmin)
    (hΔmin : Δmin ≤ Δ (k + 1)) :
    (k + 1 : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ ρ j) k).card * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| := by
  rw [← h.delta_zero]
  exact succ_le_of_trUpdate P.γ₂_pos P.γ₂_lt_one P.one_le_γ₃
    (fun j hj => h.update fun i hi => hk i (hi.trans hj)) hmin hΔmin

/-- **Lemma 2.3.1** of [cartis2022evaluation], bound (2.3.11), with the indexing of the source, for
every run of a trust-region method. Let $\mathcal{S}_k = \{ j \le k : \rho_j \ge \eta_1 \}$. If
the termination test failed at every $j < k$ and $0 < \Delta_{\min} \le \Delta_k$, then
$$k \le |\mathcal{S}_k| \left(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\right) + \frac{1}{|\log
  \gamma_2|} \left|\log \frac{\Delta_{\min}}{\Delta_0}\right|.$$
-/
theorem le_succ_count {Δmin : ℝ} {k : ℕ} (hk : ∀ j < k, ¬ stop j) (hmin : 0 < Δmin)
    (hΔmin : Δmin ≤ Δ k) :
    (k : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ ρ j) k).card * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| := by
  rw [← h.delta_zero]
  exact le_of_trUpdate P.γ₂_pos P.γ₂_lt_one P.one_le_γ₃ (h.updates hk) hmin hΔmin

/-- **Decrease on successful iterations.** Suppose that the termination test failed at every
$j \le k$, that $\rho_k = (f(x_k) - f(x_k + s_k)) / \mathrm{pred}_k$ with $\mathrm{pred}_k > 0$,
and that iteration $k$ is successful ($\rho_k \ge \eta_1$). Then $x_{k+1} = x_k + s_k$ and
$$f(x_k) - f(x_{k+1}) \ge \eta_1 \, \mathrm{pred}_k.$$
-/
theorem sub_ge_of_succ {f : E → ℝ} {pred : ℕ → ℝ} {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j)
    (hρ : ρ k = reductionRatio f (x k) (s k) (pred k)) (hpred : 0 < pred k)
    (hs : P.η₁ ≤ ρ k) :
    x (k + 1) = x k + s k ∧ P.η₁ * pred k ≤ f (x k) - f (x (k + 1)) :=
  ⟨h.eq_add_of_succ hk hs, (h.accept k hk).sub_ge hρ hpred hs⟩

/-- **Monotonicity of the objective.** Suppose that the termination test failed at every $j < K$,
and that for every $k < K$ the ratio is $\rho_k = (f(x_k) - f(x_k + s_k)) / \mathrm{pred}_k$
with $\mathrm{pred}_k > 0$. Then $f(x_j) \le f(x_i)$ for all $i \le j \le K$. Thus
$k \mapsto f(x_k)$ is nonincreasing up to and including the first termination index. -/
theorem objective_antitone {f : E → ℝ} {pred : ℕ → ℝ} {K : ℕ} (hK : ∀ j < K, ¬ stop j)
    (hρ : ∀ k < K, ρ k = reductionRatio f (x k) (s k) (pred k)) (hpred : ∀ k < K, 0 < pred k) :
    ∀ i j, i ≤ j → j ≤ K → f (x j) ≤ f (x i) := by
  intro i j hij hjK
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have hjK' : j < K := hjK
    exact ((h.accept j fun i hi => hK i (hi.trans_lt hjK')).le (hρ j hjK') (hpred j hjK')).trans
      (ih hjK'.le)

end IsTRRun

section Existence

variable {E : Type*} [Add E]

/-- **Existence of runs of a trust-region method** with a termination test on the iterate. Let `Inv`
be a property of points, for example membership in a feasible set, or the true property if none
is needed. Suppose that for every iteration $k$, every point $y$ with `Inv y` at which the test
fails, and every radius $\Delta > 0$, there is a step $s$ that satisfies the step conditions
`stepOK k y Δ s` and has `Inv (y + s)`. Let $R$ be any ratio function. Then from every $x_0$
with `Inv x₀` there is a run with $x_0$ as its first iterate, with the termination test applied
to $x_k$, with the step conditions `stepOK k (x k) (Δ k) (s k)`, and with ratios
$\rho_k = R(k, x_k, \Delta_k, s_k)$. Along this run, `Inv` holds at every $x_k$ such that the
test failed at every $j < k$, so up to and including termination.

The step conditions and the ratio can depend on the iteration counter $k$, for example through
model Hessians $B_k$ chosen in advance. The proof takes the new radii of
`Optimization.exists_trAcceptance`, so that $\Delta_{k+1} \le \Delta_k$, but the statement does
not record this property. -/
theorem exists_isTRRun (P : TRParams) {Inv : E → Prop} {test : E → Prop}
    {stepOK : ℕ → E → ℝ → E → Prop} (R : ℕ → E → ℝ → E → ℝ)
    (hstep : ∀ k y Δ, Inv y → 0 < Δ → ¬ test y → ∃ s, stepOK k y Δ s ∧ Inv (y + s))
    {x₀ : E} (hx₀ : Inv x₀) :
    ∃ (x s : ℕ → E) (Δ : ℕ → ℝ), x 0 = x₀ ∧
      IsTRRun P (fun k => test (x k)) (fun k => stepOK k (x k) (Δ k) (s k))
        (fun k => R k (x k) (Δ k) (s k)) x s Δ ∧
      ∀ k, (∀ j < k, ¬ test (x j)) → Inv (x k) := by
  classical
  let good : ℕ → E → ℝ → E → Prop := fun k y Δ s => ¬ test y → stepOK k y Δ s ∧ Inv (y + s)
  have hgood : ∀ k y Δ, Inv y → 0 < Δ → ∃ s, good k y Δ s := by
    intro k y Δ hy hΔ
    by_cases ht : test y
    · exact ⟨y, fun h' => absurd ht h'⟩
    · obtain ⟨s, hs⟩ := hstep k y Δ hy hΔ ht
      exact ⟨s, fun _ => hs⟩
  let S : ℕ → E → ℝ → E := fun k y Δ =>
    if h : Inv y ∧ 0 < Δ then (hgood k y Δ h.1 h.2).choose else y
  have hS : ∀ k y Δ, Inv y → 0 < Δ → good k y Δ (S k y Δ) := fun k y Δ hy hΔ => by
    simp only [S, hy, hΔ, and_self, dite_true]
    exact (hgood k y Δ hy hΔ).choose_spec
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant
    (α := E × ℝ) (init := fun a => a = (x₀, P.Δ₀))
    (inv := fun _ a => Inv a.1 ∧ 0 < a.2) (stop := fun _ a => test a.1)
    (step := fun k a b =>
      TRAcceptance P (R k a.1 a.2 (S k a.1 a.2)) a.1 (S k a.1 a.2) b.1 a.2 b.2 ∧
        Inv b.1 ∧ 0 < b.2)
    ⟨_, rfl⟩ (fun a ha => by subst ha; exact ⟨hx₀, P.Δ₀_pos⟩) (fun k a ha hnot => by
      obtain ⟨Δ', hacc, -, hpos⟩ :=
        exists_trAcceptance P (R k a.1 a.2 (S k a.1 a.2)) a.1 (S k a.1 a.2) ha.2.le
      have hInv : Inv (if P.η₁ ≤ R k a.1 a.2 (S k a.1 a.2) then a.1 + S k a.1 a.2 else a.1) := by
        split_ifs
        · exact (hS k a.1 a.2 ha.1 ha.2 hnot).2
        · exact ha.1
      exact ⟨(_, Δ'), ⟨hInv, hpos ha.2⟩, hacc, hInv, hpos ha.2⟩)
  refine ⟨fun k => (r k).1, fun k => S k (r k).1 (r k).2, fun k => (r k).2, by simp only [hr0],
    ⟨by simp only [hr0], fun k hk => ?_, fun k hk => (hr k hk).2.1⟩, fun k hk => ?_⟩
  · obtain ⟨⟨hInv, hpos⟩, -⟩ := hr k hk
    exact (hS k _ _ hInv hpos (hk k le_rfl)).1
  · cases k with
    | zero => simpa [hr0] using hx₀
    | succ k => exact (hr k fun j hj => hk j (Nat.lt_succ_of_le hj)).2.2.1

end Existence

/-- Let $L \in \mathbb{N}$. Suppose that every iteration $i < L$ before termination at which the run
is still at its starting point ($x_i = x_0$) and has radius $\Delta_i \ge \gamma_1^i \Delta_0$
is unsuccessful ($\rho_i < \eta_1$). Then for every $i \le L$ such that the termination test
failed at every $l < i$,
$$x_i = x_0 \quad \text{and} \quad \Delta_i \ge \gamma_1^i \Delta_0.$$
-/
theorem IsTRRun.eq_zero_of_unsucc {E : Type*} [Add E] {P : TRParams} {stop step : ℕ → Prop}
    {ρ : ℕ → ℝ} {x s : ℕ → E} {Δ : ℕ → ℝ} (h : IsTRRun P stop step ρ x s Δ) {L : ℕ}
    (hunsucc : ∀ i < L, (∀ l ≤ i, ¬ stop l) → x i = x 0 → P.γ₁ ^ i * P.Δ₀ ≤ Δ i →
      ρ i < P.η₁) :
    ∀ i ≤ L, (∀ l < i, ¬ stop l) → x i = x 0 ∧ P.γ₁ ^ i * P.Δ₀ ≤ Δ i := by
  intro i
  induction i with
  | zero => intro _ _; exact ⟨rfl, by rw [pow_zero, one_mul, h.delta_zero]⟩
  | succ i ih =>
    intro hiL hstop
    have hk : ∀ l ≤ i, ¬ stop l := fun l hl => hstop l (by omega)
    obtain ⟨hxi, hΔi⟩ := ih (by omega) fun l hl => hk l hl.le
    have hρ := hunsucc i (by omega) hk hxi hΔi
    refine ⟨(h.eq_of_not_succ hk hρ).trans hxi, ?_⟩
    calc P.γ₁ ^ (i + 1) * P.Δ₀ = P.γ₁ * (P.γ₁ ^ i * P.Δ₀) := by ring
      _ ≤ P.γ₁ * Δ i := mul_le_mul_of_nonneg_left hΔi P.γ₁_pos.le
      _ ≤ Δ (i + 1) := ((h.accept i hk).2.unsuccessful hρ).1

end Optimization
