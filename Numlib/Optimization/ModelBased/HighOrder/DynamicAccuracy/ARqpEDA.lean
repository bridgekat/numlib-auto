/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqEDA

/-!
# Adaptive regularization with explicit dynamic accuracy (ARqpEDA)

This file analyses the adaptive-regularization method ARqpEDA (Algorithm 13.3.2 of
[cartis2022evaluation]). The method uses inexact function values $\overline{f}$ and inexact
derivatives with $\|\overline{\nabla}^i f(x_k) - \nabla^i f(x_k)\| \le h_{k,i}$ (13.3.4). Each
iteration is `Optimization.ARqpDAStep` with the ratio (13.3.19) of the inexact values, together with
Step 3 (`Optimization.EDAStep3`), which computes these values with the accuracy $h_{k,0}$. The
method stops at the first iteration that passes the certified test `Optimization.edaStopAR`. An
iteration $k$ is *reached* if the method has not stopped at any iteration $j < k$.

The setting is that of `Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA`: runs on a
feasible set $X$ (§14.2), and the smoothness hypothesis `LipschitzDerivsAnchored f C A 0 p L` with
normalized constants $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$. The objective does not increase along a run, so the
iterates lie in $A$. The unconstrained method of Chapter 13 is the case $X = C = A = E$. The
constants are those of ARqpIDA with $\kappa_{\nabla,\max} = 1$: $\overline{L}_f = L_f + \kappa_h$,
$\sigma_{\max}$ of (13.1.77), $\kappa_{\delta,\min} = \varsigma\theta/(24\max\{\overline{L}_f,
\sigma_{\max}\})$ and $\kappa_{\mathrm{acc}}$; the constant of the radius inequality is
$A_{\mathrm{E}} = L_{f,p} + \sigma_{\max} + 4\kappa_s$.

## Main definitions

* `Optimization.edaStopAR`: the termination test of ARqpEDA.
* `Optimization.IsARqpEDARun`: a run of ARqpEDA on a feasible set.
* `Optimization.arEDAConstA`: the constant $A_{\mathrm{E}}$.
* `Optimization.edaPassUnchanged`: Step 1 passes every test with unchanged radii.

## Main results

* `Optimization.IsARqpEDARun.objective_le`: the objective does not increase along a run.
* `Optimization.IsARqpEDARun.sigma_le`: $\sigma_k \le \sigma_{\max}$ (Lemma 13.3.5).
* `Optimization.IsARqpEDARun.isEpsDeltaApprox_of_stop`: termination certifies approximate optimality
  (Lemma 13.3.6 (i)).
* `Optimization.IsARqpEDARun.stop_of_pass`: accurate data give termination (Lemma 13.3.6 (ii)).
* `Optimization.IsARqpEDARun.measure_ineq`: the radius inequality, which replaces Lemma 13.1.16.
* `Optimization.IsARqpEDARun.step_bound`, `Optimization.IsARqpEDARun.decrease_ge`: the step is long
  and the decrease is sufficient (Lemma 13.3.7).
* `Optimization.IsARqpEDARun.card_acc_le`: the number of accuracy-improving iterations is bounded.
* `Optimization.IsARqpEDARun.complexity`: the complexity argument of Theorem 13.3.8 for any decrease
  constant.
* `Optimization.IsARqpEDARun.le_card_succ`: the number of iterations is bounded by the number of
  successful ones (Lemma 14.2.3, ARqpEDA case).
* `Optimization.IsARqpEDARun.complexity_of_radiiControl`: the evaluation complexity (Theorem 14.2.4,
  ARqpEDA case).

## Implementation notes

* The smoothness hypothesis is anchored at the iterates, and this suffices: the iterates lie in $A$,
  the derivative estimates are made at the iterates, and the trial points are related to the
  iterates by Taylor's theorem anchored at the iterate.
* The run predicate imposes the error model (13.3.4) and Step 1 at every iteration reached, and the
  full iteration only until termination (`Optimization.UntilHit`).
* The radius inequality applies at a successful iteration $k$ followed by an iteration $k + 1$ whose
  Step 1 does not pass every test with unchanged radii. Every other successful iteration with a
  short step is followed by an accuracy-improving iteration (Step 1 branches to Step 5).
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### ARqpEDA -/

/-- The termination test of ARqpEDA at iteration $k$ (Steps 1.5–1.5.1 of Algorithm 13.3.2 of
[cartis2022evaluation]): the test (13.3.15) holds at every order $j \in [1, q]$, and (13.3.17)
$$\sum_{i=1}^{j} h_{k,i}\frac{(\delta^{(1)}_{k,j})^i}{i!} \le
  \frac{\varsigma\varepsilon_j(\delta^{(1)}_{k,j})^j}{2\,j!}$$
holds for every $j \in [1, q]$.

The test (13.3.15) is `Optimization.arqpDAPass`. -/
def edaStopAR (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (δ₁ : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E) (k : ℕ) : Prop :=
  (∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j) ∧
    ∀ j ∈ Finset.Icc 1 P.q, ∑ i ∈ Finset.Icc 1 j, h k i * δ₁ k j ^ i / i ! ≤
      P.ς * ε j * δ₁ k j ^ j / j ! / 2

/-- A run of ARqpEDA on a feasible set (Algorithm 13.3.2 of [cartis2022evaluation]; ARqpEDA-SC of
§14.2). The data are the objective $f$, a feasible set $X$, the constants $P$ of ARqpIDA,
tolerances $\varepsilon$, a starting point $x_0$, the sequences of ARqpIDA, the inexact values
$\overline{f}(x_k)$ and $\overline{f}(x_k + s_k)$, their accuracies $h_{k,0}$, and flags that
say when $\overline{f}(x_k)$ is recomputed. The run requires: (13.3.13)
$\kappa_s \le \min\{\eta_1, 1 - \eta_2\}/4$; $\varepsilon_j \in (0, 1]$ and
$\varepsilon_j \le \delta_{0,j}$ for $j \in [1, q]$; $x_0 \in X$; the initial weight, radii and
accuracies of $P$; at every iteration reached, the error model (13.3.4) up to order $p$ and Step
1 (13.3.14)–(13.3.16) on $X$ (`Optimization.ARqpStep1`); and until termination
(`Optimization.edaStopAR`), `Optimization.ARqpDAStep` on $X$ with the ratio (13.3.19) at every
iteration and Step 3 (`Optimization.EDAStep3`) at every trial iteration.

The method returns $x_\varepsilon = x_k$ and $\delta_\varepsilon = \delta^{(1)}_k$. The
unconstrained method is the case $X = E$. -/
structure IsARqpEDARun (f : E → ℝ) (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ)
    (x₀ : E) (x : ℕ → E) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E)
    (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ) (R : ℕ → Prop) : Prop where
  /-- The constant of the accuracy test satisfies (13.3.13):
  $\kappa_s \le \min\{\eta_1, 1 - \eta_2\}/4$. -/
  κs_le : P.κs ≤ min P.η₁ (1 - P.η₂) / 4
  /-- The tolerances satisfy $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$. -/
  eps_mem : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1
  /-- The tolerances satisfy $\varepsilon_j \le \delta_{0,j}$ for $j \in [1, q]$. -/
  eps_le : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j
  /-- The first iterate is the starting point $x_0$. -/
  x_zero : x 0 = x₀
  /-- The starting point is feasible: $x_0 \in X$. -/
  x₀_mem : x₀ ∈ X
  /-- The initial weight is $\sigma_0$ of $P$. -/
  σ_zero : σ 0 = P.σ₀
  /-- The initial radii are $\delta_0$ of $P$. -/
  δ_zero : δ 0 = P.δ₀
  /-- The initial accuracies are $h_0$ of $P$. -/
  h_zero : h 0 = P.h₀
  /-- The error model (13.3.4) at every iteration $k$ reached: $\|\overline{\nabla}^i f(x_k) -
  \nabla^i f(x_k)\| \le h_{k,i}$ for $i \in [1, p]$. -/
  oracle : ∀ k, (∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) →
    JetApprox (ftaylorSeries ℝ f (x k)) (D k) P.p (fun i => h k i)
  /-- Step 1 holds on $X$ at every iteration reached. -/
  step1 : ∀ k, (∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) → ARqpStep1 X P ε x σ δ δ₁ D dd k
  /-- Until termination, every iteration satisfies Steps 1, 2, 4 and 5 with the ratio (13.3.19), and
  every trial iteration satisfies Step 3. -/
  run : UntilHit (edaStopAR P ε D δ₁ h dd) fun k =>
    ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc
        (edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)) k ∧
      (¬ acc k → EDAStep3 f P.κs ((D k).taylorDecrement P.p (s k)) x s acc fx fxs h₀ R k)

namespace IsARqpEDARun

variable {f : E → ℝ} {X : Set E} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E}
  {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop}
  (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
include hrun

/-- If the run has not terminated at any iteration $j \le k$, then `Optimization.ARqpDAStep` holds
at $k$ with the ratio (13.3.19). -/
theorem step {k : ℕ} (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc
      (edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)) k :=
  (hrun.run k hk).1

/-- If the run has not terminated at any iteration $j \le k$ and iteration $k$ is a trial iteration,
then Step 3 (`Optimization.EDAStep3`) holds at $k$. -/
theorem step3 {k : ℕ} (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k) :
    EDAStep3 f P.κs ((D k).taylorDecrement P.p (s k)) x s acc fx fxs h₀ R k :=
  (hrun.run k hk).2 ha

/-- If iteration $k$ is reached, then `Optimization.ARqpDAStep` holds at every iteration $i < k$. -/
theorem steps_lt {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc
      (edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)) i :=
  fun _ hi => hrun.step fun j hj => hk j (hj.trans_lt hi)

/-- At every iteration $k$ reached, $\sigma_k \ge \sigma_{\min}$, $\delta^{(0)}_{k,j} \in (0, 1]$
for $j \in [1, q]$, and $0 \le h_{k,i} \le \kappa_h$ for $i \in [1, p]$. -/
theorem invariants {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    P.σmin ≤ σ k ∧ (∀ j ∈ Finset.Icc 1 P.q, 0 < δ k j ∧ δ k j ≤ 1) ∧
      ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ h k i ∧ h k i ≤ P.κh :=
  arqpDA_invariants (hrun.steps_lt hk) hrun.σ_zero hrun.δ_zero hrun.h_zero

/-- At every iteration $k$ reached, the weight is positive: $\sigma_k > 0$. -/
theorem sigma_pos {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : 0 < σ k :=
  P.σmin_pos.trans_le (hrun.invariants hk).1

/-- For an ARqpEDA run, $\varepsilon_{\min} = \min_{j \in [1, q]} \varepsilon_j > 0$. -/
theorem epsMin_pos : 0 < epsMin P.q ε :=
  Optimization.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

/-- For an ARqpEDA run, $\varepsilon_{\min} = \min_{j \in [1, q]} \varepsilon_j \le 1$. -/
theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Optimization.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

/-- For an ARqpEDA run, $\kappa_s \le \eta_1/4$. -/
theorem kappaS_le_eta₁ : P.κs ≤ P.η₁ / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))

/-- For an ARqpEDA run, $\kappa_s \le (1 - \eta_2)/4$. -/
theorem kappaS_le_eta₂ : P.κs ≤ (1 - P.η₂) / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))

/-- The iterates reached are feasible: $x_k \in X$. -/
theorem mem {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : x k ∈ X :=
  arqpDA_mem (hrun.steps_lt hk) (hrun.x_zero ▸ hrun.x₀_mem)

/-- The objective does not increase along an ARqpEDA run on a feasible set: if iteration $k$ is
reached, then $f(x_k) \le f(x_0)$.

On a successful iteration the inexact values are within $h_{k,0} \le \kappa_s\overline{\Delta
T}_k \le \frac{\eta_1}{4}\overline{\Delta T}_k$ of $f$ ((13.3.13), (13.3.18)), where
$\overline{\Delta T}_k = \overline{\Delta T}_{f,p}(x_k, s_k)$. Hence $f(x_k) - f(x_{k+1}) \ge
\frac{\eta_1}{2}\overline{\Delta T}_k > 0$ by Lemma 13.1.13 of [cartis2022evaluation]. -/
theorem objective_le {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : f (x k) ≤ f x₀ := by
  rw [← hrun.x_zero]
  refine le_zero_of_forall_succ_le (u := fun i => f (x i)) fun i hi => ?_
  have hki : ∀ j ≤ i, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (hj.trans_lt hi)
  have hs := hrun.step hki
  by_cases hc : ¬ acc i ∧ P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i
  · have h3 := hrun.step3 hki hc.1
    have hpos := (ARqpDAStep.taylorDecrement_ge hs hc.1 (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos fun j hj => hk j (hj.trans hi)).le).2
    have hdec := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
      (h3.fxs_err.trans h3.h₀_le) hc.2 hrun.kappaS_le_eta₁
    have := mul_pos (half_pos P.η₁_pos) hpos
    rw [hs.iterate_succ_eq_add hc.1 hc.2]
    linarith
  · rw [hs.iterate_succ_eq hc]

/-- The iterates reached lie in every set $A$ that contains the sublevel set
$\{y \in X \mid f(y) \le f(x_0)\}$. -/
theorem mem_anchor {A : Set E} (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : x k ∈ A :=
  hAX _ (hrun.mem hk) (hrun.objective_le hk)

/-- The bound (13.1.63) of [cartis2022evaluation] with $\kappa_{\nabla,\max} = 1$. Assume the
smoothness hypothesis with $L_j \ge 1$ and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$. Then
$\|\overline{\nabla}^i f(x_k)\| \le L_f + \kappa_h$ for $i \in [1, p]$ at every iteration $k$
reached. -/
theorem norm_D_le {C A : Set E} {L : ℕ → ℝ} (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) : ‖D k i‖ ≤ lipMax L P.p + P.κh := by
  have h' : ‖D k i‖ ≤ ‖iteratedFDeriv ℝ i f (x k)‖ + h k i :=
    norm_le_of_jetApprox (hrun.oracle k hk) hi
  have := hf.norm_iteratedFDeriv_le_lipMax hL hi (hrun.mem_anchor hAX hk)
  have := ((hrun.invariants hk).2.2 i hi).2
  linarith

/-- The radii $\delta^{(1)}_{k,j}$ lie in $(0, 1]$ for $j \in [1, q]$ at every iteration $k$
reached. -/
theorem stepOneRadii_mem {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1 := fun j hj =>
  ⟨(hrun.step1 k hk).radius_pos j hj,
    ((hrun.step1 k hk).radius_le j hj).trans ((hrun.invariants hk).2.1 j hj).2⟩

end IsARqpEDARun

section ARqpEDA

variable {X C A : Set E} {f : E → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E}
  {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- The weights stay bounded. Assume the smoothness hypothesis with $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$. Then every iteration $k$ reached by ARqpEDA has
$\sigma_k \le \sigma_{\max}$, where $\sigma_{\max}$ is `Optimization.arqpIDASigmaMax` for
$L_{f,p}$ and $\kappa_{\nabla,\max} = 1$, that is (13.1.77) with
$\kappa_s' = \max\{\kappa_s, \kappa_h\}$. This is Lemma 13.3.5 of [cartis2022evaluation]. -/
theorem IsARqpEDARun.sigma_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : σ k ≤ arqpIDASigmaMax P (L P.p) 1 := by
  set κs' := max P.κs P.κh
  have hκs' : 0 ≤ κs' := P.κs_pos.le.trans (le_max_left _ _)
  set σbar := (2 * L P.p + 4 * (P.p + 1)! * κs' * 1) / (1 - P.η₂)
  set ρ := edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)
  have key : ∀ i < k, ¬ acc i → σbar ≤ σ i → P.η₂ ≤ ρ i := by
    intro i hi ha hσi
    have his : ∀ j ≤ i, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (hj.trans_lt hi)
    have hilt : ∀ j < i, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => his j hj.le
    have hs := hrun.step his
    have h3 := hrun.step3 his ha
    have h2 := hs.step2_of_not_acc ha
    obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs ha (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos hilt).le
    set t := ‖s i‖
    have hherr : ∀ l ∈ Finset.Icc 1 P.p, h i l ≤ 1 * κs' * t ^ (P.p - l + 1) := by
      intro l hl
      rw [one_mul]
      rcases lt_or_ge t 1 with ht | ht
      · exact (h2.accuracy_le_of_not_acc ha ht l hl).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · exact (((hrun.invariants hilt).2.2 l hl).2.trans (le_max_right _ _)).trans
          (le_mul_of_one_le_right hκs' (one_le_pow₀ ht))
    have hE := abs_taylorDecrement_sub_le_of_stepAccuracy zero_le_one hκs' (hrun.oracle i hilt)
      hherr le_rfl
    have hR := hf.abs_sub_taylorDecrement_le_of_le le_rfl (hrun.mem_anchor hAX hilt) (hXC h2.mem)
    have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
    have hσbar : (2 * L P.p + 4 * (P.p + 1)! * κs' * 1) ≤ (1 - P.η₂) * σ i := by
      have := (div_le_iff₀' P.one_sub_η₂_pos).1 hσi
      linarith
    have hval := h3.fx_err.trans h3.h₀_le
    have hval' := h3.fxs_err.trans h3.h₀_le
    have hκs4 := hrun.kappaS_le_eta₂
    refine le_div_of_inexact_error_le (fx := f (x i)) (fxs := f (x i + s i))
      (ΔT := (ftaylorSeries ℝ f (x i)).taylorDecrement P.p (s i)) hpos ?_
    have htp : 0 ≤ t ^ (P.p + 1) := by positivity
    have hmid : |f (x i + s i) - (f (x i) - (ftaylorSeries ℝ f (x i)).taylorDecrement P.p (s i))| +
        |(ftaylorSeries ℝ f (x i)).taylorDecrement P.p (s i) - (D i).taylorDecrement P.p (s i)| ≤
          (1 - P.η₂) / 2 * (D i).taylorDecrement P.p (s i) := by
      calc _ ≤ L P.p / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) + 2 * κs' * 1 * t ^ (P.p + 1) :=
            add_le_add hR (by rw [abs_sub_comm]; exact hE)
        _ = (2 * L P.p + 4 * (P.p + 1)! * κs' * 1) / (2 * (P.p + 1)!) * t ^ (P.p + 1) := by
            field_simp; ring
        _ ≤ (1 - P.η₂) * σ i / (2 * (P.p + 1)!) * t ^ (P.p + 1) := by gcongr
        _ = (1 - P.η₂) / 2 * (σ i / ((P.p + 1)! : ℝ) * t ^ (P.p + 1)) := by ring
        _ ≤ (1 - P.η₂) / 2 * (D i).taylorDecrement P.p (s i) :=
            mul_le_mul_of_nonneg_left hlow (by linarith [P.one_sub_η₂_pos])
    nlinarith
  have h := sigma_le_max_of_arUpdate_of_neutral (σ := σ) (K := k) (σbar := σbar)
    (ρ := ρ) P.γ₁_pos P.γ₂_pos P.γ₂_le_γ₃ P.one_le_γ₃ (hrun.σ_zero ▸ P.σ₀_pos) (fun i hi => by
      have his : ∀ j ≤ i, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (hj.trans_lt hi)
      by_cases ha : acc i
      · exact Or.inl ((hrun.step his).σ_acc ha)
      · exact Or.inr ⟨(hrun.step his).update ha, key i hi ha⟩) k le_rfl
  rw [hrun.σ_zero] at h
  exact h

/-- Termination certifies approximate optimality. If ARqpEDA terminates at iteration $k$ (Step
1.5.1), then $\delta^{(1)}_k \in (0, 1]^q$ and $x_k$ is an
$(\varepsilon, \delta^{(1)}_k)$-approximate $q$-th order minimizer of $f$ on $X$. This is Lemma
13.3.6 (i) of [cartis2022evaluation]. -/
theorem IsARqpEDARun.isEpsDeltaApprox_of_stop
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) (hstop : edaStopAR P ε D δ₁ h dd k) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) := by
  have hmem := hrun.stepOneRadii_mem hk
  refine ⟨hmem, fun j hj => ?_⟩
  have hor := (hrun.oracle k hk).mono P.q_le_p
  have hw := ((hrun.step1 k hk).witness j hj).2
  have hεj := hrun.eps_mem j hj
  refine taylorMeasure_le_of_inexact_certificate hor (Finset.mem_Icc.1 hj).2
    (by simpa using hrun.mem hk)
    (hmem j hj).1.le P.ς_pos hw (hstop.1 j hj) ((hstop.2 j hj).trans ?_)
  have : P.ς * ε j ≤ ε j := mul_le_of_le_one_left hεj.1.le P.ς_le_one
  have h0 : 0 ≤ δ₁ k j ^ j / (j ! : ℝ) := by have := (hmem j hj).1; positivity
  calc P.ς * ε j * δ₁ k j ^ j / j ! / 2 = P.ς * ε j * (δ₁ k j ^ j / j !) / 2 := by ring
    _ ≤ ε j * (δ₁ k j ^ j / j !) / 2 := by gcongr
    _ = ε j * δ₁ k j ^ j / j ! / 2 := by ring

/-- Accurate data give termination. Assume the smoothness hypothesis with $L_j \ge 1$,
$X \subseteq C$ and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f = L_f + \kappa_h$ at
every iteration. Let iteration $k$ be reached, let the test (13.3.15) hold at every order at
$k$, and let (13.1.78) hold with $\kappa_{\nabla,\max} = 1$:
$$h_{k,i} \le \frac{\varsigma\kappa_{\delta,\min}^q}{4\,q!}\varepsilon_{\min}^{q+1}, \qquad i
  \in [1, p],$$
with $\kappa_{\delta,\min} = \kappa^{(1)}_\delta(\sigma_{\max})$ for $\sigma_{\max}$ of Lemma
13.3.5. Then (13.3.17) holds and the method terminates at $k$. This is Lemma 13.3.6 (ii) of
[cartis2022evaluation]. -/
theorem IsARqpEDARun.stop_of_pass (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.ς * arKappaDelta1 P (lipMax L P.p + P.κh)
      (arqpIDASigmaMax P (L P.p) 1) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopAR P ε D δ₁ h dd k := by
  refine ⟨hpass, fun j hj => ?_⟩
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  set κ := arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hrad := arqpDA_radius_ge (hrun.steps_lt hk) (hrun.step1 k hk) hrun.σ_zero hrun.δ_zero
    hrun.h_zero hrun.eps_mem hrun.eps_le hLb
    (fun i hi ℓ hℓ => hrun.norm_D_le hf hL hAX (fun l hl => hk l (hl.trans_le hi)) hℓ)
    (fun i hi => IsARqpEDARun.sigma_le hf hXC hAX hrun fun l hl => hk l (hl.trans_le hi))
    (fun i _ => hrc i)
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hmem := hrun.stepOneRadii_mem hk j hj
  set δ := δ₁ k j
  set em := epsMin P.q ε
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hεj := hrun.eps_mem j hj
  set e := P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1)
  have he0 : 0 ≤ e := by positivity
  have hm0 : 0 ≤ κ * em := by positivity
  have hm1 : κ * em ≤ 1 := (mul_le_of_le_one_left hεmin.le hκ1).trans hεmin1
  have hδj : (κ * em) ^ P.q ≤ δ ^ j :=
    (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0
      ((mul_le_mul_of_nonneg_left (epsMin_le hj) hκ0.le).trans (hrad j hj).1) j)
  have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
  calc ∑ i ∈ Finset.Icc 1 j, h k i * δ ^ i / i ! ≤ ∑ i ∈ Finset.Icc 1 j, e * (δ ^ i / i !) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right
          (hh i (Finset.Icc_subset_Icc le_rfl (hjq.trans P.q_le_p) hi)) (by
            have := hmem.1; positivity)
    _ = e * ∑ i ∈ Finset.Icc 1 j, δ ^ i / i ! := by rw [Finset.mul_sum]
    _ ≤ e * 2 := mul_le_mul_of_nonneg_left
        ((sum_pow_div_factorial_le_two_mul hmem.1.le hmem.2 _).trans (by linarith [hmem.2])) he0
    _ = P.ς * em * (κ * em) ^ P.q / (2 * P.q !) := by simp only [e]; ring
    _ ≤ P.ς * ε j * δ ^ j / (2 * P.q !) :=
        div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (epsMin_le hj) hς.le)
          hδj (by positivity) (mul_nonneg hς.le hεj.1.le)) (by positivity)
    _ ≤ P.ς * ε j * δ ^ j / (2 * j !) := by
        gcongr
        exact mul_nonneg (mul_nonneg hς.le hεj.1.le) (pow_nonneg hmem.1.le _)
    _ = P.ς * ε j * δ ^ j / j ! / 2 := by ring

/-- The radius inequality for ARqpEDA, the counterpart of Lemmas 13.1.16–13.1.17 of
[cartis2022evaluation] for inexact function values. Assume the smoothness hypothesis with
$L_j \ge 1$, $X \subseteq C$ and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$. Let the run not
have terminated at any iteration $j \le k$, let iteration $k$ be a successful trial iteration
with $\|s_k\| < 1$, and suppose that Step 1 at $k + 1$ does not pass every test (13.3.15) with
unchanged radii, that is, it halves some radius or branches to Step 2. Then for some
$j \in [1, q]$, with $\delta = \delta^{(0)}_{k+1,j}$ $(= \delta_{s_k,j})$,
$$\Big(\frac{\varsigma}{2} - \theta\Big)\frac{\varepsilon_j\delta^j}{j!} \le (L_{f,p} +
  \sigma_{\max} + 4\kappa_s)\sum_{\ell=1}^{j} \frac{\delta^\ell}{\ell!}\|s_k\|^{p-\ell+1},$$
with $\sigma_{\max}$ of Lemma 13.3.5.

Step 1 at $k + 1$ provides a displacement in the ball of radius $\delta$ with a large inexact
decrement, whence $\phi^\delta_{f,j}(x_{k+1}) > \frac{1}{2}\varsigma\varepsilon_j\delta^j/j! -
\kappa_s\sum_\ell \delta^\ell/\ell!\,\|s_k\|^{p-\ell+1}$, since the accuracies are inherited
from iteration $k$. The proof then uses the model-optimality conditions (13.1.57) at $s_k$. -/
theorem IsARqpEDARun.measure_ineq (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hs1 : ‖s k‖ < 1)
    (hnot : ¬ ((∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd (k + 1) j) ∧
      ∀ j ∈ Finset.Icc 1 P.q, δ₁ (k + 1) j = δ (k + 1) j)) :
    ∃ j ∈ Finset.Icc 1 P.q, (P.ς / 2 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) 1 + 4 * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by
  have hs := hrun.step hk
  have h2 := hs.step2_of_not_acc ha
  have hklt : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j hj.le
  have hk1 : ∀ j < k + 1, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (Nat.lt_succ_iff.1 hj)
  have hS1 := hrun.step1 (k + 1) hk1
  -- a large inexact decrement at `x_{k+1}`
  obtain ⟨j, hj, d₀, hd₀n, hd₀X, hd₀⟩ : ∃ j ∈ Finset.Icc 1 P.q, ∃ d₀, ‖d₀‖ ≤ δ (k + 1) j ∧
      x (k + 1) + d₀ ∈ X ∧
      P.ς * ε j * δ (k + 1) j ^ j / j ! / 2 < (D (k + 1)).taylorDecrement j d₀ := by
    by_cases hall : ∀ j ∈ Finset.Icc 1 P.q, δ₁ (k + 1) j = δ (k + 1) j
    · have : ¬ ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd (k + 1) j := fun hp => hnot ⟨hp, hall⟩
      push Not at this
      obtain ⟨j, hj, hfail⟩ := this
      refine ⟨j, hj, dd (k + 1) j, ?_, (hS1.witness j hj).mem, ?_⟩
      · rw [← hall j hj]; exact (hS1.witness j hj).norm_le
      · unfold arqpDAPass at hfail; rw [← hall j hj]; exact not_le.1 hfail
    · push Not at hall
      obtain ⟨j, hj, hne⟩ := hall
      obtain ⟨-, -, d₀, hd₀n, hd₀X, hd₀⟩ :=
        hS1.halving j hj (lt_of_le_of_ne (hS1.radius_le j hj) hne)
      exact ⟨j, hj, d₀, hd₀n, hd₀X, hd₀⟩
  refine ⟨j, hj, ?_⟩
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hjp : j ≤ P.p := hjq.trans P.q_le_p
  have hx : x (k + 1) = x k + s k := hs.iterate_succ_eq_add ha hρ
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial ha, ite_eq_left ⟨hρ, hs1⟩]
  have hh : h (k + 1) = h k := hs.h_trial ha
  obtain ⟨hδmem, dm, hdm, hdmle⟩ := h2.radii_of_lt hs1 j hj
  set δv := δ (k + 1) j with hδv
  have hδv0 : 0 ≤ δv := by rw [hδv, hδ]; exact hδmem.1.le
  -- the exact measure at `x_{k+1}`
  have hbar : P.ς * ε j * δv ^ j / j ! / 2 <
      taylorMeasure (D (k + 1)) j δv {e | x (k + 1) + e ∈ X} :=
    hd₀.trans_le (taylorDecrement_le_taylorMeasure _ j ⟨mem_closedBall_zero_iff.2 hd₀n, hd₀X⟩)
  have hor1 := hrun.oracle (k + 1) hk1
  have htrans := taylorMeasure_le_add_of_jetApprox hor1.symm hjp
    (show (0 : E) ∈ {e | x (k + 1) + e ∈ X} by simpa using hrun.mem hk1) hδv0
  rw [hh] at htrans
  set e₀ := P.κs * ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) with he₀def
  have hacc := h2.accuracy_le_of_not_acc ha hs1
  have he₀ : ∑ i ∈ Finset.Icc 1 j, h k i * δv ^ i / i ! ≤ e₀ := by
    rw [he₀def, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have := hacc i (Finset.Icc_subset_Icc le_rfl hjp hi)
    have h0 : 0 ≤ δv ^ i / (i ! : ℝ) := by positivity
    calc h k i * δv ^ i / i ! = h k i * (δv ^ i / i !) := by ring
      _ ≤ P.κs * ‖s k‖ ^ (P.p - i + 1) * (δv ^ i / i !) := mul_le_mul_of_nonneg_right this h0
      _ = P.κs * (δv ^ i / i ! * ‖s k‖ ^ (P.p - i + 1)) := by ring
  have h₁ : P.ς / 2 * ε j * δv ^ j / (j ! : ℝ) - e₀ <
      taylorMeasure (ftaylorSeries ℝ f (x k + s k)) j δv {e | x k + s k + e ∈ X} := by
    rw [← hx]
    have : P.ς / 2 * ε j * δv ^ j / (j ! : ℝ) = P.ς * ε j * δv ^ j / j ! / 2 := by ring
    linarith
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j δv
      {e | x k + s k + e ∈ X} ≤ P.θ * ε j * δv ^ j / j ! := by
    have hw := hdm.2
    rw [hδv, hδ]
    have := hw.trans hdmle
    have hς := P.ς_pos
    rw [show P.ς * P.θ * ε j * δs k j ^ j / j ! = P.ς * (P.θ * ε j * δs k j ^ j / j !) by ring]
      at this
    exact le_of_mul_le_mul_left this hς
  have hxA := hrun.mem_anchor hAX hklt
  have := radius_inequality_of_measure_gt_anchored hf.convex
    (fun y hy => hf.contDiffAt_of_le le_rfl hy) (hf.lipschitzAt_of_le le_rfl hxA)
    (zero_le_one.trans (hL _ le_rfl)) (hf.subset hxA)
    (hXC h2.mem) (hrun.oracle k hklt) zero_le_one P.κs_pos.le
    (fun i hi => by rw [one_mul]; exact hacc i hi)
    (hrun.sigma_pos hklt).le (IsARqpEDARun.sigma_le hf hXC hAX hrun hklt) hjp
    (by simpa using h2.mem)
    hδv0 h₁ h₂
  have e : (L P.p + arqpIDASigmaMax P (L P.p) 1 + 3 * 1 * P.κs) *
      ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) + e₀ =
      (L P.p + arqpIDASigmaMax P (L P.p) 1 + 4 * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by ring
  rw [e] at this
  exact this.le

/-- The constant $A_{\mathrm{E}} = L_{f,p} + \sigma_{\max} + 4\kappa_s$ of the radius inequality of
ARqpEDA, with $\sigma_{\max}$ of `Optimization.arqpIDASigmaMax` for $L_{f,p}$ and
$\kappa_{\nabla,\max} = 1$ (Lemma 13.3.5 of [cartis2022evaluation]). -/
noncomputable def arEDAConstA (P : ARqpIDAParams) (L : ℕ → ℝ) : ℝ :=
  L P.p + arqpIDASigmaMax P (L P.p) 1 + 4 * P.κs

/-- If $L_{f,p} \ge 1$, then $A_{\mathrm{E}} \ge 1$. -/
theorem one_le_arEDAConstA {P : ARqpIDAParams} {L : ℕ → ℝ} (hL : 1 ≤ L P.p) :
    1 ≤ arEDAConstA P L := by
  have h1 : 0 ≤ arqpIDASigmaMax P (L P.p) 1 := P.σ₀_pos.le.trans (le_max_left _ _)
  have := P.κs_pos
  unfold arEDAConstA; linarith

/-- Step 1 at iteration $i$ passes every test (13.3.15) with unchanged radii: the test holds at
every order $j \in [1, q]$, and $\delta^{(1)}_{i,j} = \delta^{(0)}_{i,j}$ for every
$j \in [1, q]$. -/
def edaPassUnchanged (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (δ δ₁ : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E) (i : ℕ) : Prop :=
  (∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd i j) ∧ ∀ j ∈ Finset.Icc 1 P.q, δ₁ i j = δ i j

/-- The step-length bounds of ARqpEDA, as in `Optimization.IsARqpIDARun.step_bound`. Assume the
smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = L_f + \kappa_h$ at iteration $k$, and
$\theta < \varsigma/2$. Let the run not have terminated at any iteration $j \le k$, let
iteration $k$ be a successful trial iteration, and let $\|s_k\| \ge 1$ or Step 1 at $k + 1$ not
pass with unchanged radii (`Optimization.edaPassUnchanged`). Then for some $j \in [1, q]$,
either $\|s_k\| \ge 1$, or the conclusions of `Optimization.arqp_pow_ge_of_radius_ineq` hold
with $a = \varsigma/2 - \theta$, $A = A_{\mathrm{E}}$ and $\kappa = \kappa_{\delta,\min}$:
$$\frac{a}{2\,j!\,A_{\mathrm{E}}}\varepsilon_j \le \|s_k\|^{p-j+1} \text{ if } u, \qquad
  \frac{a}{2\,j!\,A_{\mathrm{E}}}\hat\kappa^{j-1}\varepsilon_j^j \le \|s_k\|^p \text{ if not }
  u,$$
with $\hat\kappa = \min\{\kappa_{\delta,\min}, a/(2\,q!\,A_{\mathrm{E}})\}$. -/
theorem IsARqpEDARun.step_bound (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((u → (P.ς / 2 - P.θ) / (2 * j ! * arEDAConstA P L) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ u → (P.ς / 2 - P.θ) / (2 * j ! * arEDAConstA P L) *
          arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) ^ (j - 1) *
            ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  have hnot := hgood.resolve_left (not_le.2 hs1)
  obtain ⟨j, hj, hineq⟩ := IsARqpEDARun.measure_ineq hf hL hXC hAX hrun hk ha hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step hk
  have hklt : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j hj.le
  have h2 := hs.step2_of_not_acc ha
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial ha, ite_eq_left ⟨hρ, hs1⟩]
  rw [hδ] at hineq
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  set κ := arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hεj := hrun.eps_mem j hj
  have hδpos := (h2.radii_of_lt hs1 j hj).1.1
  have hκε : κ * ε j ≤ δs k j :=
    hrc.kappa_mul_le ha hs1 hrun.eps_mem hLb (IsARqpEDARun.sigma_le hf hXC hAX hrun hklt) hj
  have hq2 : u → δs k j = 1 := fun hu => (hrc ha hs1).1 hu j hj
  have ht : 0 < ‖s k‖ := by
    have hpos := (ARqpDAStep.taylorDecrement_ge hs ha (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos hklt).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arEDAConstA P L := zero_lt_one.trans_le (one_le_arEDAConstA (hL _ le_rfl))
  exact arqp_pow_ge_of_radius_ineq (by linarith) hA hεj.1 ht hs1 hδpos hj P.q_le_p
    hκ0 hκε hq2 hineq

/-- Sufficient decrease. Assume the smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = L_f + \kappa_h$ at iteration $k$, and
$\theta < \varsigma/2$. Let the run not have terminated at any iteration $j \le k$, let
iteration $k$ be a successful trial iteration, and let $\|s_k\| \ge 1$ or Step 1 at $k + 1$ not
pass with unchanged radii. Then
$$\overline{\Delta T}_{f,p}(x_k, s_k) \ge \kappa'_{\Delta m}\min_{j \in [1, q]}
  \varepsilon_j^{\pi_j}, \qquad f(x_k) - f(x_{k+1}) \ge \tfrac{1}{2}\eta_1\kappa'_{\Delta
  m}\min_{j \in [1, q]} \varepsilon_j^{\pi_j},$$
with $\pi_j$ the exponent `Optimization.arPiOf u p j` and $\kappa'_{\Delta m}$ equal to
$\sigma_{\min}/(p+1)!$ times the step-length constant of `Optimization.arStepConstOf` for
$a = \varsigma/2 - \theta$, $A = A_{\mathrm{E}}$ and $\kappa = \kappa_{\delta,\min}$. This is
Lemma 13.3.7 of [cartis2022evaluation].

The constant $\kappa'_{\Delta m}$ is $\kappa_{\Delta m}$ of Lemma 13.1.18 with
$\varsigma/2 - \theta$ in place of $1 - \theta$, $L_{f,p} + \sigma_{\max} + 4\kappa_s$ in place
of $L_{f,p} + \sigma_{\max} + 3\kappa_{\nabla,\max}\kappa_s$, and
$\overline{L}_f = L_f + \kappa_h$. The remaining successful iterations are followed by an
accuracy-improving iteration (Step 1 branches to Step 5). -/
theorem IsARqpEDARun.decrease_ge (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} [Decidable u] (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
          (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) /
          2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) := by
  obtain ⟨j, hj, hb⟩ := IsARqpEDARun.step_bound hf hL hXC hAX hrun hrc hθ hk ha hρ hgood
  have hklt : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j hj.le
  have hs := hrun.step hk
  obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs ha (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos hklt).le
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hL _ le_rfl)
  have ht : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hεj := hrun.eps_mem j hj
  have ha0 : 0 < P.ς / 2 - P.θ := by linarith
  have ha1 : P.ς / 2 - P.θ ≤ 1 := by linarith [P.ς_le_one, P.θ_pos]
  have hC := arqp_pow_succ_ge ha0 ha1 hA hεj.1 hεj.2 ht
    (arKappaDelta1_pos (by linarith)) (arKappaDelta1_le_one hLb) hj P.q_le_p hb
  set C := arStepConstOf u P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
    (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg ha0.le (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ ε j ^ arPiOf u P.p j := epsMin_le hj
  have hmin0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    (Optimization.epsMin_pos P.one_le_q fun j hj =>
      Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _).le
  have hσ := (hrun.invariants hklt).1
  have h1 : P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤
      (D k).taylorDecrement P.p (s k) := by
    calc P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
        ≤ P.σmin / ((P.p + 1)! : ℝ) * (C * ε j ^ arPiOf u P.p j) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hC0)
            (div_nonneg P.σmin_pos.le hfp.le)
      _ ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) :=
          mul_le_mul (div_le_div_of_nonneg_right hσ hfp.le) hC
            (mul_nonneg hC0 (Real.rpow_nonneg hεj.1.le _))
            (div_nonneg (P.σmin_pos.le.trans hσ) hfp.le)
      _ ≤ _ := hlow
  refine ⟨h1, ?_⟩
  have h3 := hrun.step3 hk ha
  have h2 := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
    (h3.fxs_err.trans h3.h₀_le) hρ hrun.kappaS_le_eta₁
  rw [(hs.accept ha).eq_add hρ]
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
      = P.η₁ / 2 * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) := by ring
    _ ≤ P.η₁ / 2 * (D k).taylorDecrement P.p (s k) := by gcongr
    _ ≤ f (x k) - f (x k + s k) := h2

/-- The accuracy-improving iterations of ARqpEDA on a feasible set, in the proof of Theorem 13.3.8
of [cartis2022evaluation]. Assume the smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$
and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = L_f + \kappa_h$ at every iteration. If
the run has not terminated at any iteration $j \le k$, then
$$|\mathcal{A}_k| \le \frac{p(q+1)}{|\log\gamma_h|}|\log\varepsilon_{\min}| +
  \frac{|\log(\kappa_{\mathrm{acc}}/\kappa_h)|}{|\log\gamma_h|} + 1,$$
where $\mathcal{A}_k$ is the set of accuracy-improving iterations in $[0, k]$ and
$\kappa_{\mathrm{acc}}$ is `Optimization.arKappaAcc` with $\kappa_{\nabla,\max} = 1$. -/
theorem IsARqpEDARun.card_acc_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ((successSet acc k).card : ℝ) ≤
      P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
          (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
          P.κh)| / |Real.log P.γh| + 1 := by
  have hq := P.one_le_q
  have hp := P.one_le_p
  set stop := edaStopAR P ε D δ₁ h dd
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set Lb := lipMax L P.p + P.κh
  have hLb : 1 ≤ Lb := by have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  set σmax := arqpIDASigmaMax P (L P.p) 1
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  set κacc := arKappaAcc P κ Lb σmax 1
  have hκacc : 0 < κacc := arKappaAcc_pos hκ0 (by linarith) zero_le_one
  have hlogh : 0 < |Real.log P.γh| := abs_pos.2 (Real.log_neg P.γh_pos P.γh_lt_one).ne
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hpowq : em ^ (P.p * (P.q + 1)) ≤ em ^ (P.q + 1) :=
    pow_le_pow_of_le_one hεmin.le hεmin1 (by nlinarith)
  have h := card_accuracyImproving_le_of_pow_of_nonneg (acc := acc)
    (hmax := fun j => ordMax P.p (h j))
    (N := P.p * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.κh_nonneg hκacc hεmin
    ((ordMax_le_iff hp).2 fun i hi => by rw [hrun.h_zero]; exact P.h₀_le i hi)
    (fun j hj => (ordMax_le_iff hp).2 fun i hi =>
      ((hrun.invariants fun l hl => hk l (by omega)).2.2 i hi).2)
    (fun j hj ha => by
      rw [show h (j + 1) = fun i => P.γh * h j i from
        funext ((hrun.step fun i hi => hk i (hi.trans hj)).h_acc ha),
        ordMax_mul hp P.γh_pos.le])
    (fun j hj ha => by rw [(hrun.step fun i hi => hk i (hi.trans hj)).h_trial ha])
    (fun j hj ha => by
      have hjs : ∀ i ≤ j, ¬ stop i := fun i hi => hk i (hi.trans hj)
      have hjlt : ∀ i < j, ¬ stop i := fun i hi => hjs i hi.le
      by_contra hcon
      push Not at hcon
      have hhi : ∀ i ∈ Finset.Icc 1 P.p, h j i ≤ κacc * em ^ (P.p * (P.q + 1)) :=
        fun i hi => (le_ordMax hi).trans hcon
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd j i
      · have hrad := arqpDA_radius_ge (hrun.steps_lt hjlt) (hrun.step1 j hjlt) hrun.σ_zero
          hrun.δ_zero hrun.h_zero hrun.eps_mem hrun.eps_le hLb
          (fun i hi ℓ hℓ => hrun.norm_D_le hf hL hAX (fun l hl => hjlt l (hl.trans_le hi)) hℓ)
          (fun i hi => IsARqpEDARun.sigma_le hf hXC hAX hrun fun l hl => hjlt l (hl.trans_le hi))
          (fun i _ => hrc i)
        refine (((hrun.step hjs).step2 hfail).not_acc_of_le (σbar := σmax)
          (hrun.step1 j hjlt).radius_pos hLb (fun i hi => hrun.norm_D_le hf hL hAX hjlt hi)
          (hrun.sigma_pos hjlt).le hκ0.le (arKappaDelta1_le_one hLb) hrun.eps_mem
          (fun l hl => (hrad l hl).1) fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right arKappaAcc_le (by positivity)
      · push Not at hfail
        refine hjs j le_rfl
            (IsARqpEDARun.stop_of_pass hf hL hXC hAX hrun hrc hjlt hfail fun i hi => ?_)
        calc h j i ≤ κacc * em ^ (P.p * (P.q + 1)) := hhi i hi
          _ = 1 * κacc * em ^ (P.p * (P.q + 1)) := by ring
          _ ≤ P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_arKappaAcc_le hκ0.le zero_le_one) hpowq (by positivity)
                (by have := P.ς_pos; positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.p * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- The complexity argument of Theorem 13.3.8 of [cartis2022evaluation], for any decrease constant.
Assume $f \ge f_{\mathrm{low}}$ on $X$, the smoothness hypothesis with $L_j \ge 1$,
$X \subseteq C$ and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = L_f + \kappa_h$ at every iteration. Let
$c > 0$, and suppose that every successful trial iteration $k$ before termination, with
$\|s_k\| \ge 1$ or Step 1 at $k + 1$ not passing with unchanged radii, decreases $f$ by at least
$c$. Then the run terminates at some iteration $k_\varepsilon$, and $x_{k_\varepsilon}$ is an
$(\varepsilon, \delta^{(1)}_{k_\varepsilon})$-approximate $q$-th order minimizer on $X$ with
$\delta^{(1)}_{k_\varepsilon} \in (0, 1]^q$. Let
$$N = \frac{f(x_0) - f_{\mathrm{low}}}{c}, \qquad M =
  \frac{p(q+1)}{|\log\gamma_h|}|\log\varepsilon_{\min}| +
  \frac{|\log(\kappa_{\mathrm{acc}}/\kappa_h)|}{|\log\gamma_h|} + 1, \qquad c_T = 1 +
  \frac{|\log\gamma_1|}{\log\gamma_2}.$$
Then at most $2((N + M + 1)c_T + \log(\sigma_{\max}/\sigma_0)/\log\gamma_2)$ inexact function
evaluations and at most $N + 2M + 2$ derivative estimates are made.

The number $M$ bounds the accuracy-improving iterations. The successful iterations that the
decrease does not cover are followed by an accuracy-improving iteration, so there are at most
$M$ of them. The function evaluations are counted by `Optimization.edaFunEvalCount`, and the
derivative estimates by `Optimization.derivEvalCount` of the iterations that are
accuracy-improving or successful. -/
theorem IsARqpEDARun.complexity (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {c : ℝ}
    (hc : 0 < c)
    (hdec : ∀ k, (∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) → ¬ acc k →
      P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k →
      (1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) → c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
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
  have hq := P.one_le_q
  have hp := P.one_le_p
  set stop := edaStopAR P ε D δ₁ h dd
  set ρ := edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set Lb := lipMax L P.p + P.κh
  have hLb : 1 ≤ Lb := by have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  set σmax := arqpIDASigmaMax P (L P.p) 1
  have hσ₀ : P.σ₀ ≤ σmax := le_max_left _ _
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hf0 : 0 ≤ f x₀ - flow := sub_nonneg.2 (hb x₀ hrun.x₀_mem)
  set N := (f x₀ - flow) / c with hN_def
  have hN0 : 0 ≤ N := by positivity
  -- accuracy-improving iterations
  set κacc := arKappaAcc P κ Lb σmax 1
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hA : ∀ k, (∀ j ≤ k, ¬ stop j) → ((successSet acc k).card : ℝ) ≤ NA :=
    fun k hk => IsARqpEDARun.card_acc_le hf hL hXC hAX hrun hrc hk
  -- the objective does not increase before termination
  have hmono : ∀ j, (∀ i ≤ j, ¬ stop i) → f (x (j + 1)) ≤ f (x j) := by
    intro j hj
    have hs := hrun.step hj
    by_cases hsucc : ¬ acc j ∧ P.η₁ ≤ ρ j
    · have hjlt : ∀ i < j, ¬ stop i := fun i hi => hj i hi.le
      have h3 := hrun.step3 hj hsucc.1
      have hpos := (ARqpDAStep.taylorDecrement_ge hs hsucc.1 (fun l hl => (hrun.eps_mem l hl).1)
        (hrun.sigma_pos hjlt).le).2
      have h2 := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
        (h3.fxs_err.trans h3.h₀_le) hsucc.2 hrun.kappaS_le_eta₁
      rw [(hs.accept hsucc.1).eq_add hsucc.2]
      have := mul_pos (half_pos P.η₁_pos) hpos
      linarith
    · rw [hs.iterate_succ_eq hsucc]
  -- successful iterations
  set good : ℕ → Prop := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i ∧
    (1 ≤ ‖s i‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (i + 1))
  set bad : ℕ → Prop := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i ∧
    ¬ (1 ≤ ‖s i‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (i + 1))
  have hgood : ∀ k, (∀ j ≤ k + 1, ¬ stop j) → ((successSet good k).card : ℝ) ≤ N := by
    intro k hk
    rw [hN_def, le_div_iff₀ hc, mul_comm, ← hrun.x_zero]
    exact card_mul_le_of_decrease («φ» := fun i => f (x i)) successSet_subset_range
      (fun j hj => hmono j fun i hi => hk i (by omega))
      (fun j hj => by
        rw [mem_successSet] at hj
        exact hdec j (fun i hi => hk i (by omega)) hj.2.1 hj.2.2.1 hj.2.2.2)
      (hb _ (hrun.mem fun i hi => hk i hi.le))
  have hbad : ∀ k, (∀ j ≤ k + 1, ¬ stop j) →
      (successSet bad k).card ≤ (successSet acc (k + 1)).card := by
    intro k hk
    refine Finset.card_le_card_of_injOn (fun i => i + 1) (fun i hi => ?_)
      (fun a _ b _ hab => by simpa using hab)
    rw [Finset.mem_coe, mem_successSet] at hi ⊢
    obtain ⟨hik, -, -, hpu⟩ := hi
    push Not at hpu
    exact ⟨Nat.succ_le_succ hik,
      (hrun.step fun l hl => hk l (hl.trans (Nat.succ_le_succ hik))).acc_of_pass hpu.2.1⟩
  have hS : ∀ k, (∀ j ≤ k, ¬ stop j) →
      ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card : ℝ) ≤ N + NA + 1 := by
    intro k hk
    cases k with
    | zero =>
      have : (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) 0).card ≤ 1 := card_successSet_le
      have : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) 0).card : ℝ) ≤ 1 := by
        exact_mod_cast this
      linarith
    | succ k =>
      have h1 : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) (k + 1)).card : ℝ) ≤
          (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card + 1 := by
        exact_mod_cast card_successSet_add_one_le
      have hset : successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k =
          successSet (fun i => good i ∨ bad i) k := by
        ext i
        simp only [mem_successSet, good, bad]
        constructor
        · rintro ⟨hi, ha, hr⟩
          exact ⟨hi, (Classical.em (1 ≤ ‖s i‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (i + 1))).imp
            (fun h' => ⟨ha, hr, h'⟩) fun h' => ⟨ha, hr, h'⟩⟩
        · rintro ⟨hi, (⟨ha, hr, -⟩ | ⟨ha, hr, -⟩)⟩ <;> exact ⟨hi, ha, hr⟩
      have h2 := card_successSet_or (succ := good) (succ' := bad) (k := k)
        fun i _ hg hb => hb.2.2 hg.2.2
      rw [← hset] at h2
      have h3 := hgood k hk
      have h4 : ((successSet bad k).card : ℝ) ≤ (successSet acc (k + 1)).card := by
        exact_mod_cast hbad k hk
      have h5 := hA (k + 1) hk
      have : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card : ℝ) =
          (successSet good k).card + (successSet bad k).card := by exact_mod_cast h2
      linarith
  -- trial iterations
  have hlog2 : 0 < Real.log P.γ₂ := P.log_γ₂_pos
  set cT := 1 + |Real.log P.γ₁| / Real.log P.γ₂ with hcT
  have hcT0 : 0 ≤ cT := by positivity
  set NT := (N + NA + 1) * cT + Real.log (σmax / P.σ₀) / Real.log P.γ₂ with hNT_def
  have hNT0 : 0 ≤ NT := by
    have : 0 ≤ Real.log (σmax / P.σ₀) := Real.log_nonneg ((one_le_div P.σ₀_pos).2 hσ₀)
    positivity
  have hT : ∀ k, (∀ j ≤ k, ¬ stop j) → ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤ NT := by
    intro k hk
    have h1 := arqpDA_card_trial_le (fun i hi => hrun.step fun j hj => hk j (hj.trans hi))
      hrun.σ_zero hrun.δ_zero hrun.h_zero
      (IsARqpEDARun.sigma_le hf hXC hAX hrun fun j hj => hk j (Nat.lt_succ_iff.1 hj))
    have h2 := mul_le_mul_of_nonneg_right (hS k hk) hcT0
    linarith
  -- conclusion
  obtain ⟨kε, hkε, -, hTk, hAk⟩ := exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 hT hA
  have hSk := derivEvalCount_le_of_isFirstHit (by linarith) hkε hS
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ ρ i)) kε : ℝ) + 1 ≤
      derivEvalCount acc kε + derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  have hklt : ∀ j < kε, ¬ stop j := fun j hj => hkε.not_test_of_lt hj
  obtain ⟨hmem, happrox⟩ := IsARqpEDARun.isEpsDeltaApprox_of_stop hrun hklt hkε.test
  refine ⟨kε, hkε, hmem, happrox, ?_, ?_⟩
  · have := edaFunEvalCount_le acc R kε
    calc (edaFunEvalCount acc R kε : ℝ) ≤ 2 * ((derivEvalCount (fun i => ¬ acc i) kε : ℝ) - 1) :=
          this
      _ ≤ 2 * NT := by linarith
      _ = _ := by rw [hNT_def, hN_def, hNA_def]
  · calc _ ≤ (NA + 1) + (N + NA + 1 + 1) - 1 := by linarith
      _ = _ := by rw [hNA_def, hN_def]; ring

end ARqpEDA

section Iterations

variable {f : E → ℝ} {X C A X₀ : Set E} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E}
  {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L B : ℕ → ℝ} {u : Prop}

/-- Counting the iterations of a run. Assume the smoothness hypothesis with $L_j \ge 1$,
$X \subseteq C$ and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = L_f + \kappa_h$ at every iteration, in
either mode. Then every iteration $k$ reached, up to and including termination, satisfies
(14.2.13)
$$k \le \kappa_{\mathrm{uns}}|\mathcal{S}_k| + \kappa_{\mathrm{unc}}, \qquad
  \kappa_{\mathrm{uns}} = 1 + \frac{|\log\gamma_1|}{\log\gamma_2}, \qquad
  \kappa_{\mathrm{unc}} = \frac{\log(\sigma_{\max}/\sigma_0)}{\log\gamma_2} + N_{\mathcal{A}},$$
where $\mathcal{S}_k$ is the set of successful trial iterations in $[0, k]$ and
$N_{\mathcal{A}} = \frac{p(q+1)}{|\log\gamma_h|}|\log\varepsilon_{\min}| +
\frac{|\log(\kappa_{\mathrm{acc}}/\kappa_h)|}{|\log\gamma_h|} + 1$. This is Lemma 14.2.3 of
[cartis2022evaluation] for ARqpEDA. -/
theorem IsARqpEDARun.le_card_succ (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) P.log_γ₂_pos.le)
  have hσ : 0 ≤ Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 (le_max_left _ _))) P.log_γ₂_pos.le
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hT := arqpDA_card_trial_le (fun i hi => hrun.step fun j hj => hk' j (hj.trans hi))
    hrun.σ_zero hrun.δ_zero hrun.h_zero (IsARqpEDARun.sigma_le hf hXC hAX hrun hk)
  have hA := IsARqpEDARun.card_acc_le hf hL hXC hAX hrun hrc hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

/-- Evaluation complexity under the radii control. Assume $f \ge f_{\mathrm{low}}$ on $X$, the
smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = L_f + \kappa_h$ at every iteration, and
$\theta < \varsigma/2$. Then every ARqpEDA run on $X$ terminates at some iteration
$k_\varepsilon$, with $x_{k_\varepsilon} \in X$ an
$(\varepsilon, \delta^{(1)}_{k_\varepsilon})$-approximate $q$-th order minimizer on $X$ and
$\delta^{(1)}_{k_\varepsilon} \in (0, 1]^q$, after at most $2((N + M + 1)c_T +
\log(\sigma_{\max}/\sigma_0)/\log\gamma_2)$ inexact function evaluations and at most
$N + 2M + 2$ derivative estimates. Here $N = (f(x_0) - f_{\mathrm{low}})/c$ with $c =
\frac{1}{2}\eta_1\kappa'_{\Delta m}\min_j \varepsilon_j^{\pi_j}$ the decrease of
`Optimization.IsARqpEDARun.decrease_ge` (Lemma 14.2.2), and $M$ and $c_T$ are as in
`Optimization.IsARqpEDARun.complexity` (Theorem 13.3.8). This is Theorem 14.2.4 of
[cartis2022evaluation] for ARqpEDA.

The radii control may be in either mode $u$: unit radii $\delta_{s_k} = 1$, which Step 2
guarantees for $X = E$ with $q \le 2$ or for $q = 1$ with $X$ convex, with
$\pi_j = (p+1)/(p-j+1)$; or the lower bounds of the type (12.2.51) at every order, available for
every $q$ and $X$, with $\pi_j = j(p+1)/p$. Here $\pi_j$ is `Optimization.arPiOf u p j`. The
radii control of Theorem 13.1.19, `Optimization.RadiiControl`, is the mode $u = (q \le 2)$. -/
theorem IsARqpEDARun.complexity_of_radiiControl (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    [Decidable u] (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧ x kε ∈ X ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
              (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
              epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
            (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hL _ le_rfl)
  have hC := arStepConstOf_pos (u := u) (q := P.q) (p := P.p) (sub_pos.2 hθ)
    (zero_lt_one.trans_le hA) (arKappaDelta1_pos (Lb := lipMax L P.p + P.κh)
      (σ := arqpIDASigmaMax P (L P.p) 1) (P := P) (by linarith))
  have hm : 0 < epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    Optimization.epsMin_pos P.one_le_q fun j hj => Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
      (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
      epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  obtain ⟨kε, hk, hmem, happ, h1, h2⟩ := IsARqpEDARun.complexity hf hL hXC hAX hb hrun hrc hc
    fun k hk ha hρ hgood =>
        (IsARqpEDARun.decrease_ge hf hL hXC hAX hrun (hrc k) hθ hk ha hρ hgood).2
  exact ⟨kε, hk, hrun.mem fun j hj => hk.2 j hj, hmem, happ, h1, h2⟩

end Iterations

end Optimization
