/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Data.Nat.SeqAppend
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpDAStep

/-!
# Adaptive regularization with implicit dynamic accuracy (ARqpIDA)

This file analyses the adaptive-regularization method ARqpIDA (Algorithm 13.1.2 of
[cartis2022evaluation]). The method uses exact function values and inexact derivatives
$\overline{\nabla}^i f(x_k)$ with $\|\overline{\nabla}^i f(x_k) - \nabla^i f(x_k)\| \le
\kappa_{\nabla,i} h_{k,i}$ (13.1.2), and each iteration is `Optimization.ARqpDAStep` with the ratio
(13.1.58). The analysis is stated for runs on a feasible set $X$ (§14.2): Step-1 displacements $e$
satisfy $x_k + e \in X$, and trial points lie in $X$. The unconstrained method of Chapter 13 is the
case $X = C = A = E$ below.

The **smoothness hypothesis** is `LipschitzDerivsAnchored f C A 0 p L`: $C$ is open and convex,
$A \subseteq C$, $f$ is $C^p$ near every point of $C$, and for $j \in [0, p]$ the $j$-th derivative
satisfies $\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x - y\|$ for $x \in A$ and $y \in C$. The
constants are normalized, $L_j \ge 1$, and usually $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$. The objective does not increase along a run, so the
iterates lie in $A$. The analysis uses the constants $L_f = \max_{j \le p} L_j$,
$\kappa_{\nabla,\max} = \max_{i \in [1, p]} \kappa_{\nabla,i}$, $\overline{L}_f = L_f +
\kappa_{\nabla,\max}\kappa_h$, the bound $\sigma_{\max}$ of (13.1.77) on the weights,
$\kappa_{\delta,\min} = \varsigma\theta/(24\max\{\overline{L}_f, \sigma_{\max}\})$, and
$A_{\mathrm{c}} = L_{f,p} + \sigma_{\max} + 3\kappa_{\nabla,\max}\kappa_s$. An iterate is
approximately optimal if it is an $(\varepsilon, \delta)$-approximate $q$-th order minimizer on $X$
for some radii $\delta \in (0, 1]^q$. The sets $\mathcal{S}_k$ and $\mathcal{A}_k$ are the
successful and the accuracy-improving iterations in $[0, k]$.

## Main definitions

* `Optimization.IsARqpIDARun`: a run of ARqpIDA on a feasible set, with the ratio (13.1.58) of
  `Optimization.arqpIDARatio`.
* `Optimization.arqpIDATest`: the iterate $x_k$ is approximately optimal on $X$.
* `Optimization.arqpIDASigmaMax`, `Optimization.arConstA`, `Optimization.arKappaAcc`: the constants
  $\sigma_{\max}$, $A_{\mathrm{c}}$ and $\kappa_{\mathrm{acc}}$ of Lemmas 13.1.14–13.1.18 and
  Theorem 13.1.19.

## Main results

* `Optimization.IsARqpIDARun.not_acc_of_le`: small accuracies give a trial iteration (Lemma
  13.1.12).
* `Optimization.IsARqpIDARun.sigma_le`: $\sigma_k \le \sigma_{\max}$ (Lemma 13.1.14).
* `Optimization.IsARqpIDARun.arqpIDATest_of_pass`: certification of approximate optimality at Step 5
  (Lemma 13.1.15).
* `Optimization.IsARqpIDARun.measure_ineq`: the radius inequality (13.1.79) (Lemma 13.1.16).
* `Optimization.IsARqpIDARun.step_bound`, `Optimization.IsARqpIDARun.norm_step_ge`: the step is long
  (Lemma 13.1.17).
* `Optimization.IsARqpIDARun.decrease_ge`: sufficient decrease at successful iterations (Lemma
  13.1.18).
* `Optimization.IsARqpIDARun.card_acc_le`: the number of accuracy-improving iterations is bounded.
* `Optimization.IsARqpIDARun.complexity`: the complexity argument of Theorem 13.1.19 for any
  decrease constant.
* `Optimization.IsARqpIDARun.le_card_succ`: the number of iterations is bounded by the number of
  successful ones (Lemma 14.2.3, ARqpIDA case).
* `Optimization.IsARqpIDARun.complexity_of_radiiControl`: the evaluation complexity (Theorem 14.2.4,
  ARqpIDA case).
* `Optimization.IsARqpIDARun.measure_ineq_unit`, `Optimization.IsARqpIDARun.step_bound_unit`,
  `Optimization.IsARqpIDARun.decrease_ge_unit`: the argument with unit radii for $q \le 2$ without
  constraints.

## Proof outline

At a successful iteration followed by an iterate that is not approximately optimal, the radius
inequality (13.1.79) and the lower bound on the radii give a lower bound on $\|s_k\|$, hence on the
decrease $f(x_k) - f(x_{k+1})$. Since $f$ is bounded below on $X$, there are few such iterations.
Each accuracy-improving iteration multiplies the accuracies by $\gamma_h$, and small accuracies give
a trial iteration, so there are few accuracy-improving iterations. Finally, the number of trial
iterations is bounded by the number of successful ones (Lemma 13.1.9).

## Implementation notes

* The method has no termination rule. The results count the iterations before the first iterate that
  passes `Optimization.arqpIDATest`.
* The closedness of $X$ is not used.
* The smoothness hypothesis is anchored at the iterates, and this suffices: the iterates lie in $A$,
  the derivative estimates are made at the iterates, and the trial points are related to the
  iterates by Taylor's theorem anchored at the iterate.
* For $q \le 2$ without constraints, the map $\delta \mapsto \phi^\delta_j/\delta^j$ is
  non-increasing for $j \le 2$ (`Optimization.pow_div_mul_taylorMeasure_le`). This gives the results
  with unit radii for any radii of Step 2.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### ARqpIDA runs -/

/-- The ratio (13.1.58) of ARqpIDA, with exact function values:
$$\rho_k = \frac{f(x_k) - f(x_k + s_k)}{\overline{\Delta T}_{f,p}(x_k, s_k)}.$$
-/
noncomputable def arqpIDARatio (f : E → ℝ) (P : ARqpIDAParams)
    (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (x s : ℕ → E) (k : ℕ) : ℝ :=
  reductionRatio f (x k) (s k) ((D k).taylorDecrement P.p (s k))

/-- The test of approximate optimality for ARqpIDA on a feasible set ([cartis2022evaluation], §14.2,
(14.2.2)): $x_k$ is an $(\varepsilon, \delta)$-approximate $q$-th order minimizer of $f$ on $X$
for *some* radii $\delta \in (0, 1]^q$. That is, for some such $\delta$ and every
$j \in [1, q]$, the Taylor measure of $f$ at $x_k$ over the displacements $e$ with
$x_k + e \in X$ satisfies $\phi^{\delta_j}_{f,j}(x_k) \le \varepsilon_j\delta_j^j/j!$.

The unconstrained test is the case $X = E$. -/
def arqpIDATest (f : E → ℝ) (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → E)
    (k : ℕ) : Prop :=
  ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 P.q, δ' j ∈ Set.Ioc 0 1) ∧
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε δ'

/-- A run of ARqpIDA on a feasible set (Algorithm 13.1.2 of [cartis2022evaluation]; ARqpIDA-SC of
§14.2). The data are the objective $f$, a feasible set $X$, the unknown oracle constants
$\kappa_{\nabla,i}$, the constants $P$, tolerances $\varepsilon$, a starting point $x_0$, and
the sequences of iterates $x_k$, weights $\sigma_k$, radii $\delta^{(0)}_k$, $\delta^{(1)}_k$
and $\delta_{s_k}$, requested accuracies $h_{k,i}$, inexact derivative data $D_k$, Step-1
displacements $d_{k,j}$, orders $j_k$, steps $s_k$ and accuracy-improving flags. The run
requires: $\varepsilon_j \in (0, 1]$ and $\varepsilon_j \le \delta_{0,j}$ for $j \in [1, q]$;
$\kappa_{\nabla,i} \ge 0$ for $i \in [1, p]$; $x_0 \in X$; the initial weight, radii and
accuracies of $P$; the error model (13.1.2), $\|\overline{\nabla}^i f(x_k) - \nabla^i f(x_k)\|
\le \kappa_{\nabla,i} h_{k,i}$ for $i \in [1, p]$ and every $k$; and `Optimization.ARqpDAStep`
on $X$ with the ratio (13.1.58) at every iteration.

The method has no termination rule (see `Optimization.arqpIDATest`). The closedness of $X$ is
not used. The unconstrained method is the case $X = E$. The error model is
`Optimization.JetApprox` of the Taylor series `ftaylorSeries ℝ f (x k)` and $D_k$. -/
structure IsARqpIDARun (f : E → ℝ) (X : Set E) (κg : ℕ → ℝ) (P : ARqpIDAParams)
    (ε : ℕ → ℝ) (x₀ : E) (x : ℕ → E) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E)
    (acc : ℕ → Prop) : Prop where
  /-- The tolerances satisfy $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$. -/
  eps_mem : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1
  /-- The tolerances satisfy $\varepsilon_j \le \delta_{0,j}$ for $j \in [1, q]$ (13.1.51). -/
  eps_le : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j
  /-- The oracle constants satisfy $\kappa_{\nabla,i} \ge 0$ for $i \in [1, p]$. -/
  κg_nonneg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i
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
  /-- The error model (13.1.2): $\|\overline{\nabla}^i f(x_k) - \nabla^i f(x_k)\| \le
  \kappa_{\nabla,i} h_{k,i}$ for $i \in [1, p]$ and every $k$. -/
  oracle : ∀ k, JetApprox (ftaylorSeries ℝ f (x k)) (D k) P.p (fun i => κg i * h k i)
  /-- Steps 1–5 hold at every iteration, with the ratio (13.1.58). -/
  step : ∀ k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc (arqpIDARatio f P D x s) k

namespace IsARqpIDARun

variable {f : E → ℝ} {X : Set E} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop}
  (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
include hrun

/-- Along an ARqpIDA run, $\sigma_k \ge \sigma_{\min}$, $\delta^{(0)}_{k,j} \in (0, 1]$ for
$j \in [1, q]$, and $0 \le h_{k,i} \le \kappa_h$ for $i \in [1, p]$. -/
theorem invariants (k : ℕ) :
    P.σmin ≤ σ k ∧ (∀ j ∈ Finset.Icc 1 P.q, 0 < δ k j ∧ δ k j ≤ 1) ∧
      ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ h k i ∧ h k i ≤ P.κh :=
  arqpDA_invariants (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero

/-- Along an ARqpIDA run, the weights are positive: $\sigma_k > 0$. -/
theorem sigma_pos (k : ℕ) : 0 < σ k := P.σmin_pos.trans_le (hrun.invariants k).1

/-- For an ARqpIDA run, $\varepsilon_{\min} = \min_{j \in [1, q]} \varepsilon_j > 0$. -/
theorem epsMin_pos : 0 < epsMin P.q ε :=
  Optimization.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

/-- For an ARqpIDA run, $\varepsilon_{\min} = \min_{j \in [1, q]} \varepsilon_j \le 1$. -/
theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Optimization.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

/-- For an ARqpIDA run, $\kappa_{\nabla,\max} = \max_{i \in [1, p]} \kappa_{\nabla,i} \ge 0$. -/
theorem kappaMax_nonneg : 0 ≤ ordMax P.p κg := ordMax_nonneg hrun.κg_nonneg

/-- The iterates of an ARqpIDA run are feasible: $x_k \in X$. -/
theorem mem (k : ℕ) : x k ∈ X :=
  arqpDA_mem (fun i _ => hrun.step i) (hrun.x_zero ▸ hrun.x₀_mem)

/-- The objective does not increase along an ARqpIDA run on a feasible set: $f(x_k) \le f(x_0)$ for
every $k$.

The ratio uses exact function values, and the predicted decrease of a trial iteration is
positive (Lemma 13.1.13 of [cartis2022evaluation]), so a successful iteration does not increase
$f$. -/
theorem objective_le (k : ℕ) : f (x k) ≤ f x₀ := by
  rw [← hrun.x_zero]
  refine le_zero_of_forall_succ_le (u := fun i => f (x i)) fun i _ => ?_
  by_cases ha : acc i
  · simp only [(hrun.step i).x_acc ha, le_rfl]
  · exact ((hrun.step i).accept ha).le (w := f) rfl (ARqpDAStep.taylorDecrement_ge (hrun.step i) ha
      (fun j hj => (hrun.eps_mem j hj).1) (hrun.sigma_pos i).le).2

/-- The iterates of an ARqpIDA run lie in every set $A$ that contains the sublevel set
$\{y \in X \mid f(y) \le f(x_0)\}$. -/
theorem mem_anchor {A : Set E} (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) : x k ∈ A :=
  hAX _ (hrun.mem k) (hrun.objective_le k)

/-- The bound (13.1.63) of [cartis2022evaluation]. Assume the smoothness hypothesis with $L_j \ge 1$
and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$. Then $\|\overline{\nabla}^i f(x_k)\| \le
\overline{L}_f = L_f + \kappa_{\nabla,\max}\kappa_h$ for $i \in [1, p]$ and every $k$. -/
theorem norm_D_le {C A : Set E} {L : ℕ → ℝ} (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    ‖D k i‖ ≤ lipMax L P.p + ordMax P.p κg * P.κh :=
  hf.norm_le_of_jetApprox hL (hrun.mem_anchor hAX k) (hrun.oracle k) hrun.κg_nonneg
    (fun i hi => ((hrun.invariants k).2.2 i hi).1) (fun i hi => ((hrun.invariants k).2.2 i hi).2) hi

/-- If $L_j \ge 1$ for $j \le p$, then $\overline{L}_f = L_f + \kappa_{\nabla,\max}\kappa_h \ge 1$.
-/
theorem one_le_Lbar {L : ℕ → ℝ} (hL : ∀ j ≤ P.p, 1 ≤ L j) :
    1 ≤ lipMax L P.p + ordMax P.p κg * P.κh := by
  have := one_le_lipMax hL; have := hrun.kappaMax_nonneg; have := P.κh_nonneg; nlinarith

end IsARqpIDARun

section ARqpIDA

variable {X C A : Set E} {f : E → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- Accurate derivatives give trial iterations: the outcomes of Step 2 at iteration $k$ of an
ARqpIDA run. Assume the smoothness hypothesis with $L_j \ge 1$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at every iteration
$i < k$, and $\sigma_i \le \bar\sigma$ for $i \le k$. Then:
* if Step 2 is performed at $k$ (the test (13.1.53) fails at some order), then (13.1.74)
  $\Delta\overline{m}_k(s_k) \ge
  \varsigma\varepsilon_{j_k}(\delta^{(1)}_{k,j_k})^{j_k}/(4\,j_k!) > 0$, and $s_k \neq 0$;
* (13.1.71) $\delta^{(0)}_{k,j} \ge \delta^{(1)}_{k,j} \ge
  \kappa^{(1)}_\delta(\bar\sigma)\varepsilon_j$ for $j \in [1, q]$;
* if Step 2 is performed at $k$ and (13.1.73) $h_{k,i} \le
  \kappa_s(\varsigma\kappa^{(1)}_\delta(\bar\sigma)^q/(12\,q!\,\max\{\overline{L}_f,
  \bar\sigma\}))^p\varepsilon_{\min}^{p(q+1)}$ for $i \in [1, p]$, then iteration $k$ is not
  accuracy-improving.

This is Lemma 13.1.12 of [cartis2022evaluation]. Only the iterations $i < k$ enter the radius
bound at $k$, so the radii control is assumed only there. The constant $\kappa^{(1)}_\delta$ is
`Optimization.arKappaDelta1`. -/
theorem IsARqpIDARun.not_acc_of_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i < k, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {σbar : ℝ} (hσ : ∀ i ≤ k, σ i ≤ σbar) :
    ((∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
        0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ∧
        P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (s k) ∧
        s k ≠ 0) ∧
      (∀ j ∈ Finset.Icc 1 P.q,
        arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar * ε j ≤ δ₁ k j ∧
          δ₁ k j ≤ δ k j) ∧
      ((∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
        (∀ i ∈ Finset.Icc 1 P.p, h k i ≤
          P.κs * (P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar ^ P.q /
            (12 * P.q ! * max (lipMax L P.p + ordMax P.p κg * P.κh) σbar)) ^ P.p *
            epsMin P.q ε ^ (P.p * (P.q + 1))) → ¬ acc k) := by
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar hL
  have hrad := arqpDA_radius_ge (fun i _ => hrun.step i) (hrun.step k).toARqpStep1 hrun.σ_zero
    hrun.δ_zero hrun.h_zero
    hrun.eps_mem hrun.eps_le hLb (fun i _ ℓ hℓ => hrun.norm_D_le hf hL hAX i hℓ) hσ hrc
  refine ⟨fun hb => ?_, hrad, fun hb hh => ?_⟩
  · have h2 := (hrun.step k).step2 hb
    have hpos : 0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 := by
      have := P.ς_pos; have := (hrun.eps_mem _ h2.jk_mem).1
      have := (hrun.step k).radius_pos _ h2.jk_mem; positivity
    have hm := h2.model_dec.trans h2.dec_le
    refine ⟨hpos, hm, fun h0 => ?_⟩
    rw [h0, arModelDec, sub_self] at hm
    linarith
  · have h2 := (hrun.step k).step2 hb
    exact h2.not_acc_of_le ((hrun.step k).radius_pos) hLb
      (fun i hi => hrun.norm_D_le hf hL hAX k hi)
      (hrun.sigma_pos k).le (arKappaDelta1_pos (by linarith)).le
      (arKappaDelta1_le_one hLb) hrun.eps_mem (fun j hj => (hrad j hj).1) hh

/-! ### The regularization weights -/

/-- The bound (13.1.77) of [cartis2022evaluation] on the weights,
$$\sigma_{\max} = \max\Big\{\sigma_0, \frac{\gamma_3(2L_{f,p} +
  4(p+1)!\,\kappa_s'\kappa_{\nabla,\max})}{1 - \eta_2}\Big\}, \qquad \kappa_s' = \max\{\kappa_s,
  \kappa_h\}.$$
-/
noncomputable def arqpIDASigmaMax (P : ARqpIDAParams) (Lp κm : ℝ) : ℝ :=
  max P.σ₀ (P.γ₃ * ((2 * Lp + 4 * (P.p + 1)! * max P.κs P.κh * κm) / (1 - P.η₂)))

/-- Assume the smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$. Then every ARqpIDA run satisfies (13.1.77)
$$\sigma_k \le \sigma_{\max} \qquad \text{for all } k,$$
with $\sigma_{\max}$ of `Optimization.arqpIDASigmaMax` for $L_{f,p}$ and $\kappa_{\nabla,\max}$.
This is Lemma 13.1.14 of [cartis2022evaluation].

The constant $\kappa_s' = \max\{\kappa_s, \kappa_h\}$ covers the long steps $\|s_k\| \ge 1$,
where the accuracy test (13.1.46) is not performed and only $h_{k,i} \le \kappa_h$ is known. -/
theorem IsARqpIDARun.sigma_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (k : ℕ) :
    σ k ≤ arqpIDASigmaMax P (L P.p) (ordMax P.p κg) := by
  set κm := ordMax P.p κg
  set κs' := max P.κs P.κh
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  have hκs' : 0 ≤ κs' := P.κs_pos.le.trans (le_max_left _ _)
  have hLp : 1 ≤ L P.p := hL _ le_rfl
  set σbar := (2 * L P.p + 4 * (P.p + 1)! * κs' * κm) / (1 - P.η₂)
  have key : ∀ k, ¬ acc k → σbar ≤ σ k → P.η₂ ≤ arqpIDARatio f P D x s k := by
    intro k hk hσk
    have hs := hrun.step k
    have h2 := hs.step2_of_not_acc hk
    obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le
    set t := ‖s k‖
    have hherr : ∀ i ∈ Finset.Icc 1 P.p, κg i * h k i ≤ κm * κs' * t ^ (P.p - i + 1) := by
      intro i hi
      have hhi : h k i ≤ κs' * t ^ (P.p - i + 1) := by
        rcases lt_or_ge t 1 with ht | ht
        · exact (h2.accuracy_le_of_not_acc hk ht i hi).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        · exact (((hrun.invariants k).2.2 i hi).2.trans (le_max_right _ _)).trans
            (le_mul_of_one_le_right hκs' (one_le_pow₀ ht))
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) hhi ((hrun.invariants k).2.2 i hi).1 hκm
    have hE := abs_taylorDecrement_sub_le_of_stepAccuracy hκm hκs' (hrun.oracle k) hherr le_rfl
    have hR := hf.abs_sub_taylorDecrement_le_of_le le_rfl (hrun.mem_anchor hAX k) (hXC h2.mem)
    have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
    have hσbar : (2 * L P.p + 4 * (P.p + 1)! * κs' * κm) ≤ (1 - P.η₂) * σ k := by
      have := (div_le_iff₀' P.one_sub_η₂_pos).1 hσk
      linarith
    rw [arqpIDARatio, reductionRatio_def]
    refine le_div_of_inexact_error_le (fx := f (x k)) (fxs := f (x k + s k))
      (ΔT := (ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k)) hpos ?_
    rw [sub_self, sub_self, abs_zero, zero_add, add_zero]
    have htp : 0 ≤ t ^ (P.p + 1) := by positivity
    calc |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k))| +
          |(ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k) - (D k).taylorDecrement P.p (s k)|
        ≤ L P.p / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) + 2 * κs' * κm * t ^ (P.p + 1) :=
          add_le_add hR (by rw [abs_sub_comm]; exact hE)
      _ = (L P.p + 2 * (P.p + 1)! * κs' * κm) / (P.p + 1)! * t ^ (P.p + 1) := by
          field_simp
      _ ≤ (1 - P.η₂) * σ k / (P.p + 1)! * t ^ (P.p + 1) := by
          gcongr
          have : 0 ≤ (P.p + 1)! * κs' * κm := by positivity
          linarith
      _ = (1 - P.η₂) * (σ k / ((P.p + 1)! : ℝ) * t ^ (P.p + 1)) := by ring
      _ ≤ (1 - P.η₂) * (D k).taylorDecrement P.p (s k) :=
          mul_le_mul_of_nonneg_left hlow P.one_sub_η₂_pos.le
  have h := sigma_le_max_of_arUpdate_of_neutral (σ := σ) (K := k) (σbar := σbar)
    (ρ := arqpIDARatio f P D x s) P.γ₁_pos P.γ₂_pos P.γ₂_le_γ₃ P.one_le_γ₃
    (hrun.σ_zero ▸ P.σ₀_pos) (fun i _ => by
      by_cases ha : acc i
      · exact Or.inl ((hrun.step i).σ_acc ha)
      · exact Or.inr ⟨(hrun.step i).update ha, key i ha⟩) k le_rfl
  rwa [hrun.σ_zero] at h

/-! ### Certification and the radius inequality -/

/-- Certification at Step 5. Assume the smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at every iteration
$i < k$. Suppose that the test (13.1.53) holds at every order at iteration $k$, so that Step 1
branches to Step 5, and that (13.1.78)
$$\kappa_{\nabla,\max} h_{k,i} \le
  \frac{\varsigma\kappa_{\delta,\min}^q}{4\,q!}\varepsilon_{\min}^{q+1}, \qquad i \in [1, p].$$
Then $\delta^{(1)}_k \in (0, 1]^q$ and $x_k$ is an $(\varepsilon, \delta^{(1)}_k)$-approximate
$q$-th order minimizer of $f$ on $X$; in particular `Optimization.arqpIDATest` holds at $k$.
This is Lemma 13.1.15 of [cartis2022evaluation]. -/
theorem IsARqpIDARun.arqpIDATest_of_pass (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i < k, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, ordMax P.p κg * h k i ≤
      P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) ^ P.q / (4 * P.q !) *
        epsMin P.q ε ^ (P.q + 1)) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) ∧
        arqpIDATest f X P ε x k := by
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar hL
  set κ := arKappaDelta1 P Lb (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hrad := (IsARqpIDARun.not_acc_of_le hf hL hAX hrun hrc (k := k)
    (fun i _ => IsARqpIDARun.sigma_le hf hL hXC hAX hrun i)).2.1
  have hmem : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1 := fun j hj =>
    ⟨(hrun.step k).radius_pos j hj, (hrad j hj).2.trans ((hrun.invariants k).2.1 j hj).2⟩
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have happrox : IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) := by
    intro j hj
    obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
    set em := epsMin P.q ε
    have hw := ((hrun.step k).witness j hj).2
    have hm0 : 0 ≤ κ * em := by positivity
    have hm1 : κ * em ≤ 1 := (mul_le_of_le_one_left hεmin.le hκ1).trans hεmin1
    have hδj : (κ * em) ^ P.q ≤ δ₁ k j ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0
        ((mul_le_mul_of_nonneg_left (epsMin_le hj) hκ0.le).trans (hrad j hj).1) j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : P.ς * em ≤ ε j := (mul_le_of_le_one_left hεmin.le hς1).trans (epsMin_le hj)
    refine taylorMeasure_le_of_inexact_certificate_uniform ((hrun.oracle k).mono P.q_le_p) hj
      (by simpa using hrun.mem k) (hmem j hj).1.le (hmem j hj).2 hς hw (hpass j hj)
      (e := P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1)) (fun i hi => ?_) ?_
    · have hip : i ∈ Finset.Icc 1 P.p :=
        Finset.Icc_subset_Icc le_rfl (hjq.trans P.q_le_p) hi
      exact (mul_le_mul_of_nonneg_right (le_ordMax hip) ((hrun.invariants k).2.2 i hip).1).trans
        (hh i hip)
    · calc P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) =
            P.ς * em * (κ * em) ^ P.q / (4 * P.q !) := by ring
        _ ≤ ε j * δ₁ k j ^ j / (4 * P.q !) :=
            div_le_div_of_nonneg_right (mul_le_mul hεj hδj (pow_nonneg hm0 _)
              (hrun.eps_mem j hj).1.le) (by positivity)
        _ ≤ ε j * δ₁ k j ^ j / (4 * j !) := by
            gcongr
            exact mul_nonneg (hrun.eps_mem j hj).1.le (pow_nonneg (hmem j hj).1.le _)
  exact ⟨hmem, happrox, δ₁ k, hmem, happrox⟩

/-- The radius inequality. Assume the smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$. Let iteration $k$ of an ARqpIDA run be a
successful trial iteration with $\|s_k\| < 1$, and let $x_{k+1}$ not be an
$(\varepsilon, \delta^{(0)}_{k+1})$-approximate $q$-th order minimizer on $X$. Then for some
$j \in [1, q]$, with $\delta = \delta^{(0)}_{k+1,j}$, (13.1.79)
$$(1 - \theta)\frac{\varepsilon_j\delta^j}{j!} \le (L_{f,p} + \sigma_{\max} +
  3\kappa_{\nabla,\max}\kappa_s)\sum_{\ell=1}^{j} \frac{\delta^\ell}{\ell!}\|s_k\|^{p-\ell+1}.$$
This is Lemma 13.1.16 of [cartis2022evaluation].

The radii $\delta^{(0)}_{k+1}$ equal $\delta_{s_k}$, because the iteration is successful and the
step is short. -/
theorem IsARqpIDARun.measure_ineq (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hx : x (k + 1) = x k + s k := hs.iterate_succ_eq_add hk hρ
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial hk, ite_eq_left ⟨hρ, hs1⟩]
  unfold IsEpsDeltaApprox at hnot
  push Not at hnot
  obtain ⟨j, hj, hlt⟩ := hnot
  refine ⟨j, hj, ?_⟩
  obtain ⟨hδmem, dm, hdm, hdmle⟩ := h2.radii_of_lt hs1 j hj
  rw [hx] at hlt
  rw [hδ] at hlt ⊢
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j (δs k j)
      {e | x k + s k + e ∈ X} ≤ P.θ * ε j * δs k j ^ j / j ! := by
    have hw := hdm.2
    have := hw.trans hdmle
    have hς := P.ς_pos
    rw [show P.ς * P.θ * ε j * δs k j ^ j / j ! = P.ς * (P.θ * ε j * δs k j ^ j / j !) by ring]
      at this
    exact le_of_mul_le_mul_left this hς
  have hxA := hrun.mem_anchor hAX k
  have := radius_inequality_of_measure_gt_anchored hf.convex
    (fun y hy => hf.contDiffAt_of_le le_rfl hy) (hf.lipschitzAt_of_le le_rfl hxA)
    (zero_le_one.trans (hL _ le_rfl)) (hf.subset hxA)
    (hXC h2.mem) (hrun.oracle k) hrun.kappaMax_nonneg P.κs_pos.le
    (fun i hi => by
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) (h2.accuracy_le_of_not_acc hk hs1 i hi)
        ((hrun.invariants k).2.2 i hi).1 hrun.kappaMax_nonneg)
    (hrun.sigma_pos k).le (IsARqpIDARun.sigma_le hf hL hXC hAX hrun k) hjp (by simpa using h2.mem)
    hδmem.1.le
    (a := 1) (e₀ := 0) (by rw [one_mul, sub_zero]; exact hlt) h₂
  rw [add_zero] at this
  exact this.le

/-! ### Step length and decrease -/

/-- The constant $A_{\mathrm{c}} = L_{f,p} + \sigma_{\max} + 3\kappa_{\nabla,\max}\kappa_s$ of
Lemmas 13.1.16–13.1.18 of [cartis2022evaluation]. -/
noncomputable def arConstA (P : ARqpIDAParams) (L : ℕ → ℝ) (κm : ℝ) : ℝ :=
  L P.p + arqpIDASigmaMax P (L P.p) κm + 3 * κm * P.κs

/-- If $L_{f,p} \ge 1$ and $\kappa_{\nabla,\max} \ge 0$, then $A_{\mathrm{c}} \ge 1$. -/
theorem one_le_arConstA {P : ARqpIDAParams} {L : ℕ → ℝ} {κm : ℝ} (hL : 1 ≤ L P.p)
    (hκm : 0 ≤ κm) : 1 ≤ arConstA P L κm := by
  have h1 : 0 ≤ arqpIDASigmaMax P (L P.p) κm := P.σ₀_pos.le.trans (le_max_left _ _)
  have h2 : 0 ≤ 3 * κm * P.κs := by have := P.κs_pos; positivity
  unfold arConstA; linarith

/-- If $\overline{L} > 0$, $\sigma \le \sigma'$ and $e \ge 0$, then $\kappa^{(1)}_\delta(\sigma') e
\le \varsigma\theta e/(24\max\{\overline{L}, \sigma\})$. -/
theorem arKappaDelta1_mul_le {P : ARqpIDAParams} {Lb σ σ' e : ℝ} (hLb : 0 < Lb) (hσ : σ ≤ σ')
    (he : 0 ≤ e) : arKappaDelta1 P Lb σ' * e ≤ P.ς * P.θ * e / (24 * max Lb σ) := by
  have := P.ς_pos; have := P.θ_pos
  have hM : 0 < max Lb σ := lt_max_of_lt_left hLb
  have hM' : max Lb σ ≤ max Lb σ' := max_le_max le_rfl hσ
  rw [arKappaDelta1, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- The step-length bounds behind Lemmas 13.1.17 and 13.1.18 of [cartis2022evaluation]. Assume the
smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at iteration $k$. Let
iteration $k$ be a successful trial iteration, and let $x_{k+1}$ not be an
$(\varepsilon, \delta^{(0)}_{k+1})$-approximate $q$-th order minimizer on $X$. Then for some
$j \in [1, q]$, either $\|s_k\| \ge 1$, or the conclusions of
`Optimization.arqp_pow_ge_of_radius_ineq` hold with $a = 1 - \theta$, $A = A_{\mathrm{c}}$ and
$\kappa = \kappa_{\delta,\min}$:
$$\frac{1 - \theta}{2\,j!\,A_{\mathrm{c}}}\varepsilon_j \le \|s_k\|^{p-j+1} \text{ if } u,
  \qquad \frac{1 - \theta}{2\,j!\,A_{\mathrm{c}}}\hat\kappa^{j-1}\varepsilon_j^j \le \|s_k\|^p
  \text{ if not } u,$$
with $\hat\kappa = \min\{\kappa_{\delta,\min}, (1 - \theta)/(2\,q!\,A_{\mathrm{c}})\}$. -/
theorem IsARqpIDARun.step_bound (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((u → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ u → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) *
          arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
            (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  obtain ⟨j, hj, hineq⟩ := IsARqpIDARun.measure_ineq hf hL hXC hAX hrun hk hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial hk, ite_eq_left ⟨hρ, hs1⟩]
  rw [hδ] at hineq
  have hLb := hrun.one_le_Lbar hL
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  set κ := arKappaDelta1 P Lb (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hεj := hrun.eps_mem j hj
  have hδpos := (h2.radii_of_lt hs1 j hj).1.1
  have hκε : κ * ε j ≤ δs k j :=
    hrc.kappa_mul_le hk hs1 hrun.eps_mem hLb (IsARqpIDARun.sigma_le hf hL hXC hAX hrun k) hj
  have hq2 : u → δs k j = 1 := fun hu => (hrc hk hs1).1 hu j hj
  have ht : 0 < ‖s k‖ := by
    have hpos := (ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arConstA P L (ordMax P.p κg) := by
    have := hL _ le_rfl
    have : 0 ≤ arqpIDASigmaMax P (L P.p) (ordMax P.p κg) := (P.σ₀_pos.le).trans (le_max_left _ _)
    have := hrun.kappaMax_nonneg; have := P.κs_pos
    unfold arConstA; positivity
  exact arqp_pow_ge_of_radius_ineq (sub_pos.2 P.θ_lt_one) hA hεj.1 ht hs1 hδpos hj P.q_le_p
    hκ0 hκε hq2 hineq

/-- The step is long. Assume the smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at iteration $k$. Let
iteration $k$ be a successful trial iteration, and let $x_{k+1}$ not be an
$(\varepsilon, \delta^{(0)}_{k+1})$-approximate $q$-th order minimizer on $X$. Then for some
$j \in [1, q]$ (13.1.80):
* if $u$ holds (unit radii), $\|s_k\| \ge ((1 -
  \theta)/(2\,j!\,A_{\mathrm{c}}))^{1/(p-j+1)}\varepsilon_j^{1/(p-j+1)}$;
* if $u$ fails (radii bounded below), $\|s_k\| \ge ((1 -
  \theta)\hat\kappa^{j-1}/(2\,j!\,A_{\mathrm{c}}))^{1/p}\varepsilon_j^{j/p}$,

where $\hat\kappa = \min\{\kappa_{\delta,\min}, (1 - \theta)/(2\,q!\,A_{\mathrm{c}})\}$ and
$\kappa_{\delta,\min} = \varsigma\theta/(24\max\{\overline{L}_f, \sigma_{\max}\})$ (13.1.81).
This is Lemma 13.1.17 of [cartis2022evaluation].

The source states the two cases for $q \le 2$ and $q > 2$, which is the mode $u = (q \le 2)$ of
`Optimization.RadiiControl`. -/
theorem IsARqpIDARun.norm_step_ge (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    (u → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) *
        ε j ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) ≤ ‖s k‖) ∧
    (¬ u → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
          (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) /
          (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / (P.p : ℝ)) *
        ε j ^ ((j : ℝ) / P.p) ≤ ‖s k‖) := by
  obtain ⟨j, hj, hb⟩ := IsARqpIDARun.step_bound hf hL hXC hAX hrun hrc hk hρ hnot
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  set A := arConstA P L (ordMax P.p κg)
  have hLb := hrun.one_le_Lbar hL
  set κh := arKappaHat P.q (1 - P.θ) A (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
    (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))
  have hA : 1 ≤ A := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg
  have hθ := P.θ_pos
  have hθ1 := P.θ_lt_one
  have hεj := hrun.eps_mem j hj
  have hfj : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hden : 0 < 2 * (j ! : ℝ) * A := by nlinarith
  have hb0 : 0 ≤ (1 - P.θ) / (2 * j ! * A) := div_nonneg (by linarith) hden.le
  have hb1 : (1 - P.θ) / (2 * j ! * A) ≤ 1 := by
    rw [div_le_one hden]; nlinarith
  have hκh0 : 0 ≤ κh := le_min (arKappaDelta1_pos (by linarith)).le
    (div_nonneg (by linarith) (by nlinarith))
  have hκh1 : κh ≤ 1 := (min_le_left _ _).trans (arKappaDelta1_le_one hLb)
  have hB0 : 0 ≤ (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) := by
    exact div_nonneg (mul_nonneg (by linarith) (pow_nonneg hκh0 _)) hden.le
  have hB1 : (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) ≤ 1 := by
    rw [mul_div_right_comm]
    exact (mul_le_of_le_one_left (pow_nonneg hκh0 _) hb1).trans (pow_le_one₀ hκh0 hκh1)
  rcases hb with hs1 | ⟨hq2, hq3⟩
  · refine ⟨fun _ => ⟨j, hj, ?_⟩, fun _ => ⟨j, hj, ?_⟩⟩
    · exact ((mul_le_of_le_one_left (Real.rpow_nonneg hεj.1.le _)
        (Real.rpow_le_one hb0 hb1 (by positivity))).trans
        (Real.rpow_le_one hεj.1.le hεj.2 (by positivity))).trans hs1
    · exact ((mul_le_of_le_one_left (Real.rpow_nonneg hεj.1.le _)
        (Real.rpow_le_one hB0 hB1 (by positivity))).trans
        (Real.rpow_le_one hεj.1.le hεj.2 (by positivity))).trans hs1
  refine ⟨fun hq => ⟨j, hj, ?_⟩, fun hq => ⟨j, hj, ?_⟩⟩
  · rw [← Real.mul_rpow hb0 hεj.1.le]
    exact Optimization.rpow_one_div_le_of_le_pow (by omega) (mul_nonneg hb0 hεj.1.le)
      (norm_nonneg _) (hq2 hq)
  · have hp0 : P.p ≠ 0 := by have := P.one_le_p; omega
    have he : ε j ^ ((j : ℝ) / P.p) = (ε j ^ j) ^ (1 / (P.p : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hεj.1.le, mul_one_div]
    rw [he, ← Real.mul_rpow hB0 (pow_nonneg hεj.1.le _)]
    refine Optimization.rpow_one_div_le_of_le_pow hp0 (mul_nonneg hB0 (pow_nonneg hεj.1.le _))
      (norm_nonneg _) ?_
    calc (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) * ε j ^ j =
          (1 - P.θ) / (2 * j ! * A) * κh ^ (j - 1) * ε j ^ j := by ring
      _ ≤ ‖s k‖ ^ P.p := hq3 hq

/-- Sufficient decrease. Assume the smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at iteration $k$. Let
iteration $k$ be a successful trial iteration, and let $x_{k+1}$ not be approximately optimal on
$X$ for any radii in $(0, 1]^q$. Then (13.1.82) and (13.1.83)
$$\overline{\Delta T}_{f,p}(x_k, s_k) \ge \kappa_{\Delta m}\min_{j \in [1, q]}
  \varepsilon_j^{\pi_j}, \qquad f(x_k) - f(x_{k+1}) \ge \tfrac{1}{2}\eta_1\kappa_{\Delta
  m}\min_{j \in [1, q]} \varepsilon_j^{\pi_j},$$
with $\pi_j$ the exponent `Optimization.arPiOf u p j` and $\kappa_{\Delta m}$ equal to
$\sigma_{\min}/(p+1)!$ times the step-length constant of `Optimization.arStepConstOf` for
$a = 1 - \theta$, $A = A_{\mathrm{c}}$ and $\kappa = \kappa_{\delta,\min}$. This is Lemma
13.1.18 of [cartis2022evaluation].

With unit radii ($u$), $\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!}\big(\frac{1 -
\theta}{2\,q!\,A_{\mathrm{c}}}\big)^{(p+1)/(p-q+1)}$ and $\pi_j = (p+1)/(p-j+1)$. With radii
bounded below (not $u$), $\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!}\big(\frac{(1 -
\theta)\hat\kappa^{q-1}}{2\,q!\,A_{\mathrm{c}}}\big)^{q(p+1)/p}$ and $\pi_j = j(p+1)/p$, with
$\hat\kappa$ as in `Optimization.IsARqpIDARun.norm_step_ge`. The source states the two cases for
$q \le 2$ and $q > 2$. -/
theorem IsARqpIDARun.decrease_ge (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    [Decidable u]
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arqpIDATest f X P ε x (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) := by
  have hnot' : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1)) :=
    fun hc => hnot ⟨δ (k + 1), fun j hj => (hrun.invariants (k + 1)).2.1 j hj, hc⟩
  obtain ⟨j, hj, hb⟩ := IsARqpIDARun.step_bound hf hL hXC hAX hrun hrc hk hρ hnot'
  have hs := hrun.step k
  obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos k).le
  have hLb := hrun.one_le_Lbar hL
  set A := arConstA P L (ordMax P.p κg)
  have hA : 1 ≤ A := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg
  have ht : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hεj := hrun.eps_mem j hj
  have hC := arqp_pow_succ_ge (sub_pos.2 P.θ_lt_one) (by linarith [P.θ_pos]) hA hεj.1 hεj.2 ht
    (arKappaDelta1_pos (by linarith)) (arKappaDelta1_le_one hLb) hj P.q_le_p hb
  set C := arStepConstOf u P.q P.p (1 - P.θ) A
    (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg (by linarith [P.θ_lt_one]) (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ ε j ^ arPiOf u P.p j := epsMin_le hj
  have hmin0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    (Optimization.epsMin_pos P.one_le_q fun j hj =>
      Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _).le
  have hσ := (hrun.invariants k).1
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
  have h2 := (hs.accept hk).sub_ge (w := f) rfl hpos hρ
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
      = P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) /
          2 := by ring
    _ ≤ P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) := by
        have := mul_nonneg hη.le h0; linarith
    _ ≤ P.η₁ * (D k).taylorDecrement P.p (s k) := mul_le_mul_of_nonneg_left h1 hη.le
    _ ≤ f (x k) - f (x (k + 1)) := h2

/-! ### Complexity -/

/-- The constant $\kappa_{\mathrm{acc}}$ of the proof of Theorem 13.1.19 of [cartis2022evaluation]:
$$\kappa_{\mathrm{acc}} = \min\Big\{\frac{\varsigma\kappa^q}{4\,q!\,\kappa_{\nabla,\max}},
  \kappa_s\Big(\frac{\varsigma\kappa^q}{12\,q!\,\max\{\overline{L}_f,
  \sigma_{\max}\}}\Big)^p\Big\}, \qquad \kappa = \kappa^{(1)}_\delta(\sigma_{\max}),$$
where the first term is omitted when $\kappa_{\nabla,\max} = 0$. -/
noncomputable def arKappaAcc (P : ARqpIDAParams) (κ Lb σmax κm : ℝ) : ℝ :=
  if κm = 0 then P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p
  else min (P.ς * κ ^ P.q / (4 * P.q ! * κm))
    (P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p)

/-- If $\kappa > 0$, $\overline{L} > 0$ and $\kappa_{\nabla,\max} \ge 0$, then
$\kappa_{\mathrm{acc}} > 0$. -/
theorem arKappaAcc_pos {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} (hκ : 0 < κ) (hLb : 0 < Lb)
    (hκm : 0 ≤ κm) : 0 < arKappaAcc P κ Lb σmax κm := by
  have := P.ς_pos; have := P.κs_pos
  have hM : 0 < max Lb σmax := lt_max_of_lt_left hLb
  unfold arKappaAcc
  split_ifs with h0
  · positivity
  · exact lt_min (by have := lt_of_le_of_ne hκm (Ne.symm h0); positivity) (by positivity)

/-- The constant $\kappa_{\mathrm{acc}}$ is at most its second term,
$\kappa_s(\varsigma\kappa^q/(12\,q!\,\max\{\overline{L}, \sigma_{\max}\}))^p$. -/
theorem arKappaAcc_le {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} :
    arKappaAcc P κ Lb σmax κm ≤ P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p := by
  unfold arKappaAcc
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

/-- If $\kappa \ge 0$ and $\kappa_{\nabla,\max} \ge 0$, then
$\kappa_{\nabla,\max}\kappa_{\mathrm{acc}} \le \varsigma\kappa^q/(4\,q!)$. -/
theorem mul_arKappaAcc_le {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} (hκ : 0 ≤ κ) (hκm : 0 ≤ κm) :
    κm * arKappaAcc P κ Lb σmax κm ≤ P.ς * κ ^ P.q / (4 * P.q !) := by
  have := P.ς_pos
  unfold arKappaAcc
  split_ifs with h0
  · rw [h0, zero_mul]; positivity
  · have hκm' : 0 < κm := lt_of_le_of_ne hκm (Ne.symm h0)
    calc κm * min (P.ς * κ ^ P.q / (4 * P.q ! * κm)) _
        ≤ κm * (P.ς * κ ^ P.q / (4 * P.q ! * κm)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hκm
      _ = P.ς * κ ^ P.q / (4 * P.q !) := by field_simp

/-- The accuracy-improving iterations of ARqpIDA on a feasible set, in the proof of Theorem 13.1.19
of [cartis2022evaluation]. Assume the smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$
and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at every iteration, in
either mode. If no iterate $x_j$ with $j \le k$ is approximately optimal on $X$, then
$$|\mathcal{A}_k| \le \frac{p(q+1)}{|\log\gamma_h|}|\log\varepsilon_{\min}| +
  \frac{|\log(\kappa_{\mathrm{acc}}/\kappa_h)|}{|\log\gamma_h|} + 1.$$

The set $\mathcal{A}_k$ is `Optimization.successSet` of the accuracy-improving flags. -/
theorem IsARqpIDARun.card_acc_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arqpIDATest f X P ε x j) :
    ((successSet acc k).card : ℝ) ≤
      P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
          |Real.log P.γh| + 1 := by
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set κm := ordMax P.p κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar hL
  set σmax := arqpIDASigmaMax P (L P.p) κm
  have hσk : ∀ k, σ k ≤ σmax := fun k => IsARqpIDARun.sigma_le hf hL hXC hAX hrun k
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  set κacc := arKappaAcc P κ Lb σmax κm
  have hκacc : 0 < κacc := arKappaAcc_pos hκ0 (by linarith) hκm
  have hlogh : 0 < |Real.log P.γh| := abs_pos.2 (Real.log_neg P.γh_pos P.γh_lt_one).ne
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hpowq : em ^ (P.p * (P.q + 1)) ≤ em ^ (P.q + 1) :=
    pow_le_pow_of_le_one hεmin.le hεmin1 (by nlinarith [P.one_le_p])
  have hp := P.one_le_p
  have h := card_accuracyImproving_le_of_pow_of_nonneg (acc := acc)
    (hmax := fun j => ordMax P.p (h j))
    (N := P.p * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.κh_nonneg hκacc hεmin
    ((ordMax_le_iff hp).2 fun i hi => by rw [hrun.h_zero]; exact P.h₀_le i hi)
    (fun j _ => (ordMax_le_iff hp).2 fun i hi => ((hrun.invariants j).2.2 i hi).2)
    (fun j _ ha => by
      rw [show h (j + 1) = fun i => P.γh * h j i from funext ((hrun.step j).h_acc ha),
        ordMax_mul hp P.γh_pos.le])
    (fun j _ ha => by rw [(hrun.step j).h_trial ha])
    (fun j hj ha => by
      by_contra hcon
      push Not at hcon
      have hhi : ∀ i ∈ Finset.Icc 1 P.p, h j i ≤ κacc * em ^ (P.p * (P.q + 1)) :=
        fun i hi => (le_ordMax hi).trans hcon
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd j i
      · refine (IsARqpIDARun.not_acc_of_le hf hL hAX hrun (fun i _ => hrc i) (k := j)
          (fun i _ => hσk i)).2.2 hfail
          (fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right arKappaAcc_le (by positivity)
      · push Not at hfail
        refine hk j hj
          (IsARqpIDARun.arqpIDATest_of_pass hf hL hXC hAX hrun (fun i _ => hrc i) hfail fun i
            hi => ?_).2.2
        calc κm * h j i ≤ κm * (κacc * em ^ (P.p * (P.q + 1))) :=
              mul_le_mul_of_nonneg_left (hhi i hi) hκm
          _ = κm * κacc * em ^ (P.p * (P.q + 1)) := by ring
          _ ≤ P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_arKappaAcc_le hκ0.le hκm) hpowq (by positivity)
                (by have := P.ς_pos; positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.p * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- The complexity argument of Theorem 13.1.19 of [cartis2022evaluation], for any decrease constant.
Assume $f \ge f_{\mathrm{low}}$ on $X$, the smoothness hypothesis with $L_j \ge 1$,
$X \subseteq C$ and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at every iteration. Let
$c > 0$, and suppose that every successful trial iteration $k$ such that $x_{k+1}$ is not
approximately optimal decreases $f$ by at least $c$. Then there is a first approximately optimal
iterate $x_{k_\varepsilon}$. Before it, with $N = (f(x_0) - f_{\mathrm{low}})/c$, at most
$$\Big(1 + \frac{|\log\gamma_1|}{\log\gamma_2}\Big)N +
  \frac{\log(\sigma_{\max}/\sigma_0)}{\log\gamma_2} + 2 + \frac{|\log\gamma_1|}{\log\gamma_2}$$
function evaluations and at most
$$N + \frac{p(q+1)}{|\log\gamma_h|}|\log\varepsilon_{\min}| +
  \frac{|\log(\kappa_{\mathrm{acc}}/\kappa_h)|}{|\log\gamma_h|} + 3$$
derivative estimates are made.

The function evaluations are counted as $1$ plus the number of trial iterations before
$k_\varepsilon$, and the derivative estimates as $1$ plus the number of iterations before
$k_\varepsilon$ that are accuracy-improving or successful (`Optimization.derivEvalCount`). The
first approximately optimal iterate is `Optimization.IsFirstHit` of `Optimization.arqpIDATest`. -/
theorem IsARqpIDARun.complexity (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {c : ℝ} (hc : 0 < c)
    (hdec : ∀ k, ¬ acc k → P.η₁ ≤ arqpIDARatio f P D x s k → ¬ arqpIDATest f X P ε x (k + 1) →
      c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (arqpIDATest f X P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) / c) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) / c + P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hq := P.one_le_q
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set κm := ordMax P.p κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar hL
  set σmax := arqpIDASigmaMax P (L P.p) κm
  have hσk : ∀ k, σ k ≤ σmax := fun k => IsARqpIDARun.sigma_le hf hL hXC hAX hrun k
  have hσ₀ : P.σ₀ ≤ σmax := le_max_left _ _
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hf0 : 0 ≤ f x₀ - flow := sub_nonneg.2 (hb x₀ hrun.x₀_mem)
  set N := (f x₀ - flow) / c with hN_def
  have hN0 : 0 ≤ N := by positivity
  -- successful iterations before termination
  have hS : ∀ k, (∀ j ≤ k, ¬ arqpIDATest f X P ε x j) →
      ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card : ℝ) ≤ N + 1 := by
    refine card_successSet_le_add_one_of_forall hN0 fun k hk => ?_
    rw [hN_def, ← hrun.x_zero]
    exact card_successSet_le_div_of_decrease («φ» := fun i => f (x i)) hc
      (fun j _ hj => by rw [(hrun.step j).iterate_succ_eq hj])
      (fun j hj hs => hdec j hs.1 hs.2 (hk (j + 1) (by omega))) (hb _ (hrun.mem _))
  -- trial iterations
  have hlog2 : 0 < Real.log P.γ₂ := P.log_γ₂_pos
  set cT := 1 + |Real.log P.γ₁| / Real.log P.γ₂ with hcT
  have hcT0 : 0 ≤ cT := by positivity
  set NT := (N + 1) * cT + Real.log (σmax / P.σ₀) / Real.log P.γ₂ with hNT_def
  have hNT0 : 0 ≤ NT := by
    have : 0 ≤ Real.log (σmax / P.σ₀) :=
      Real.log_nonneg ((one_le_div P.σ₀_pos).2 hσ₀)
    positivity
  have hT : ∀ k, (∀ j ≤ k, ¬ arqpIDATest f X P ε x j) →
      ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤ NT := by
    intro k hk
    have h1 := arqpDA_card_trial_le (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero
      (hσk (k + 1))
    have h2 := mul_le_mul_of_nonneg_right (hS k hk) hcT0
    linarith
  -- accuracy-improving iterations
  set κacc := arKappaAcc P κ Lb σmax κm
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hp := P.one_le_p
  have hA : ∀ k, (∀ j ≤ k, ¬ arqpIDATest f X P ε x j) → ((successSet acc k).card : ℝ) ≤ NA :=
    fun k hk => IsARqpIDARun.card_acc_le hf hL hXC hAX hrun hrc hk
  -- conclusion
  obtain ⟨kε, hkε, -, hTk, hAk⟩ := exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 hT hA
  have hSk := derivEvalCount_le_of_isFirstHit (by linarith) hkε hS
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε :
      ℝ) + 1 ≤ derivEvalCount acc kε +
        derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  refine ⟨kε, hkε, ?_, ?_⟩
  · calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤ NT + 1 := hTk
      _ = _ := by rw [hNT_def, hcT]; ring
  · calc _ ≤ (NA + 1) + (N + 1 + 1) - 1 := by linarith
      _ = _ := by rw [hNA_def]; ring

/-- Radius one suffices for the orders $q \le 2$, without constraints. Let $q \le 2$, and let $x$ be
an $(\varepsilon, \delta)$-approximate $q$-th order minimizer for the derivative data $D$ and
some radii $\delta \in (0, 1]^q$, with all of $E$ as feasible displacements. Then $x$ is also an
$(\varepsilon, 1)$-approximate minimizer: $\phi^1_j \le \varepsilon_j/j!$ for $j \in [1, q]$.
This is used for Theorem 13.1.19 (1) of [cartis2022evaluation].

The proof uses that $\delta \mapsto \phi^\delta_j/\delta^j$ is non-increasing for $j \le 2$
(`Optimization.pow_div_mul_taylorMeasure_le`). -/
theorem isEpsDeltaApprox_one_of_le_two {D : FormalMultilinearSeries ℝ E ℝ} {q : ℕ}
    (hq : q ≤ 2) {ε δ : ℕ → ℝ} (hδ : ∀ j ∈ Finset.Icc 1 q, δ j ∈ Set.Ioc 0 1)
    (h : IsEpsDeltaApprox D univ q ε δ) : IsEpsDeltaApprox D univ q ε (fun _ => 1) := by
  intro j hj
  have hj2 : j ≤ 2 := (Finset.mem_Icc.1 hj).2.trans hq
  have h1 := pow_div_mul_taylorMeasure_le D hj2 (hδ j hj).1 (hδ j hj).2
  have h2 := h j hj
  have hpos : 0 < δ j ^ j := pow_pos (hδ j hj).1 j
  have hf : (0 : ℝ) < j ! := by positivity
  rw [div_one] at h1
  simp only [one_pow, mul_one]
  have : δ j ^ j * taylorMeasure D j 1 univ ≤ δ j ^ j * (ε j / j !) := by
    calc δ j ^ j * taylorMeasure D j 1 univ ≤ ε j * δ j ^ j / j ! := h1.trans h2
      _ = δ j ^ j * (ε j / j !) := by ring
  exact le_of_mul_le_mul_left this hpos

/-- The radius inequality at unit radii. Let $X = C = A = E$ in the smoothness hypothesis, with
$L_j \ge 1$, and let $q \le 2$. Let iteration $k$ of an ARqpIDA run on $E$ be a successful trial
iteration with $\|s_k\| < 1$, and let $x_{k+1}$ not be an $(\varepsilon, 1)$-approximate $q$-th
order minimizer. Then for some $j \in [1, q]$ the inequality (13.1.79) holds with $\delta = 1$:
$$(1 - \theta)\frac{\varepsilon_j}{j!} \le (L_{f,p} + \sigma_{\max} +
  3\kappa_{\nabla,\max}\kappa_s)\sum_{\ell=1}^{j} \frac{1}{\ell!}\|s_k\|^{p-\ell+1},$$
whatever the radii $\delta_{s_k}$ of Step 2.

Since $\delta \mapsto \phi^\delta_\ell/\delta^\ell$ is non-increasing for $\ell \le 2$
(`Optimization.pow_div_mul_taylorMeasure_le`), the bound (13.1.57) on the model at the radii
$\delta_{s_k}$ gives the same bound at radius $1$. -/
theorem IsARqpIDARun.measure_ineq_unit (hf : LipschitzDerivsAnchored f univ univ 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hq2 : P.q ≤ 2)
    (hrun : IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * 1 ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, 1 ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hx : x (k + 1) = x k + s k := hs.iterate_succ_eq_add hk hρ
  unfold IsEpsDeltaApprox at hnot
  push Not at hnot
  obtain ⟨j, hj, hlt⟩ := hnot
  refine ⟨j, hj, ?_⟩
  obtain ⟨hδmem, dm, hdm, hdmle⟩ := h2.radii_of_lt hs1 j hj
  rw [hx] at hlt
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have hj2 : j ≤ 2 := (Finset.mem_Icc.1 hj).2.trans hq2
  have hfj : (0 : ℝ) < j ! := by positivity
  have h₂δ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j (δs k j)
      univ ≤ P.θ * ε j * δs k j ^ j / j ! := by
    have hw := hdm.2
    have := hw.trans hdmle
    have hς := P.ς_pos
    rw [show P.ς * P.θ * ε j * δs k j ^ j / j ! = P.ς * (P.θ * ε j * δs k j ^ j / j !) by ring,
      Set.setOf_add_mem_univ] at this
    exact le_of_mul_le_mul_left this hς
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j 1
      univ ≤ P.θ * ε j * 1 ^ j / j ! := by
    have hmono := pow_div_mul_taylorMeasure_le
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) hj2 hδmem.1 hδmem.2
    rw [div_one] at hmono
    have hpos : 0 < δs k j ^ j := pow_pos hδmem.1 j
    rw [one_pow, mul_one]
    have : δs k j ^ j * taylorMeasure
        (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j 1 univ ≤
        δs k j ^ j * (P.θ * ε j / j !) := by
      calc _ ≤ P.θ * ε j * δs k j ^ j / j ! := hmono.trans h₂δ
        _ = δs k j ^ j * (P.θ * ε j / j !) := by ring
    exact le_of_mul_le_mul_left this hpos
  have := radius_inequality_of_measure_gt hf.convex (fun y hy => hf.contDiffAt_of_le le_rfl hy)
    (hf.lipschitzOn_of_le le_rfl) (zero_le_one.trans (hL _ le_rfl)) (mem_univ _) (mem_univ _)
    (hrun.oracle k) hrun.kappaMax_nonneg P.κs_pos.le
    (fun i hi => by
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) (h2.accuracy_le_of_not_acc hk hs1 i hi)
        ((hrun.invariants k).2.2 i hi).1 hrun.kappaMax_nonneg)
    (hrun.sigma_pos k).le
        (IsARqpIDARun.sigma_le hf hL subset_rfl (fun _ _ _ => mem_univ _) hrun k) hjp (mem_univ 0)
    zero_le_one (a := 1) (e₀ := 0) (by rw [one_mul, sub_zero]; exact hlt) h₂
  rw [add_zero] at this
  exact this.le

/-- The step bound at unit radii. Let $X = C = A = E$ in the smoothness hypothesis, with
$L_j \ge 1$, and let $q \le 2$. Let iteration $k$ of an ARqpIDA run on $E$ be a successful trial
iteration, and let $x_{k+1}$ not be an $(\varepsilon, 1)$-approximate $q$-th order minimizer.
Then for some $j \in [1, q]$, either $\|s_k\| \ge 1$ or
$$\frac{1 - \theta}{2\,j!\,A_{\mathrm{c}}}\varepsilon_j \le \|s_k\|^{p-j+1},$$
whatever the radii of the run.

The conclusion is stated as the conclusion of `Optimization.IsARqpIDARun.step_bound` in the mode
$u = $ `True`, where the second alternative is empty. -/
theorem IsARqpIDARun.step_bound_unit (hf : LipschitzDerivsAnchored f univ univ 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hq2 : P.q ≤ 2)
    (hrun : IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((True → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ True → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) *
          arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
            (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  obtain ⟨j, hj, hineq⟩ := IsARqpIDARun.measure_ineq_unit hf hL hq2 hrun hk hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step k
  have hLb := hrun.one_le_Lbar hL
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  set κ := arKappaDelta1 P Lb (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hεj := hrun.eps_mem j hj
  have hκε : κ * ε j ≤ 1 := (mul_le_of_le_one_left hεj.1.le hκ1).trans hεj.2
  have ht : 0 < ‖s k‖ := by
    have hpos := (ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arConstA P L (ordMax P.p κg) := by
    have := hL _ le_rfl
    have : 0 ≤ arqpIDASigmaMax P (L P.p) (ordMax P.p κg) := (P.σ₀_pos.le).trans (le_max_left _ _)
    have := hrun.kappaMax_nonneg; have := P.κs_pos
    unfold arConstA; positivity
  exact arqp_pow_ge_of_radius_ineq (u := True) (sub_pos.2 P.θ_lt_one) hA hεj.1 ht hs1 one_pos
    hj P.q_le_p hκ0 hκε (fun _ => rfl) hineq

/-- Sufficient decrease at unit radii. Let $X = C = A = E$ in the smoothness hypothesis, with
$L_j \ge 1$, and let $q \le 2$. Let iteration $k$ of an ARqpIDA run on $E$ be a successful trial
iteration, and let $x_{k+1}$ not be approximately optimal for any radii in $(0, 1]^q$. Then
$$f(x_k) - f(x_{k+1}) \ge \tfrac{1}{2}\eta_1\kappa_{\Delta m}\min_{j \in [1, q]}
  \varepsilon_j^{(p+1)/(p-j+1)}, \qquad \kappa_{\Delta m} =
  \frac{\sigma_{\min}}{(p+1)!}\Big(\frac{1 -
  \theta}{2\,q!\,A_{\mathrm{c}}}\Big)^{(p+1)/(p-q+1)},$$
which is the decrease of the mode with unit radii, whatever the radii control of the run.

The constants are `Optimization.arStepConstOf` and `Optimization.arPiOf` in the mode `True`. -/
theorem IsARqpIDARun.decrease_ge_unit (hf : LipschitzDerivsAnchored f univ univ 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hq2 : P.q ≤ 2)
    (hrun : IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ arqpIDATest f univ P ε x (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤ f (x k) - f (x (k + 1)) := by
  have hnot' : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1) :=
    fun hc => hnot ⟨fun _ => 1, fun _ _ => ⟨one_pos, le_rfl⟩, by rwa [Set.setOf_add_mem_univ]⟩
  obtain ⟨j, hj, hb⟩ := IsARqpIDARun.step_bound_unit hf hL hq2 hrun hk hρ hnot'
  have hs := hrun.step k
  obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos k).le
  have hLb := hrun.one_le_Lbar hL
  set A := arConstA P L (ordMax P.p κg)
  have hA : 1 ≤ A := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg
  have ht : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hεj := hrun.eps_mem j hj
  have hC := arqp_pow_succ_ge (u := True) (sub_pos.2 P.θ_lt_one) (by linarith [P.θ_pos]) hA
    hεj.1 hεj.2 ht (arKappaDelta1_pos (by linarith)) (arKappaDelta1_le_one hLb) hj P.q_le_p hb
  set C := arStepConstOf True P.q P.p (1 - P.θ) A
    (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg (by linarith [P.θ_lt_one]) (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤ ε j ^ arPiOf True P.p j :=
    epsMin_le hj
  have hσ := (hrun.invariants k).1
  have h1 : P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤
      (D k).taylorDecrement P.p (s k) := by
    calc P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf True P.p j)
        ≤ P.σmin / ((P.p + 1)! : ℝ) * (C * ε j ^ arPiOf True P.p j) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hC0)
            (div_nonneg P.σmin_pos.le hfp.le)
      _ ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) :=
          mul_le_mul (div_le_div_of_nonneg_right hσ hfp.le) hC
            (mul_nonneg hC0 (Real.rpow_nonneg hεj.1.le _))
            (div_nonneg (P.σmin_pos.le.trans hσ) hfp.le)
      _ ≤ _ := hlow
  have h2 := (hs.accept hk).sub_ge (w := f) rfl hpos hρ
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C *
      epsMin P.q (fun j => ε j ^ arPiOf True P.p j) := by
    have hm0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf True P.p j) :=
      (Optimization.epsMin_pos P.one_le_q fun j hj =>
        Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _).le
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf True P.p j)
      = P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf True P.p j)) / 2 := by ring
    _ ≤ P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf True P.p j)) := by
        have := mul_nonneg hη.le h0; linarith
    _ ≤ P.η₁ * (D k).taylorDecrement P.p (s k) := mul_le_mul_of_nonneg_left h1 hη.le
    _ ≤ f (x k) - f (x (k + 1)) := h2

end ARqpIDA

section Iterations

variable {f : E → ℝ} {X C A X₀ : Set E} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop} {L B : ℕ → ℝ} {u : Prop}

/-- Counting the iterations of a run. Assume the smoothness hypothesis with $L_j \ge 1$,
$X \subseteq C$ and $A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at every iteration, in
either mode. Then every iteration $k$ up to the first iterate that is approximately optimal on
$X$ satisfies (14.2.13)
$$k \le \kappa_{\mathrm{uns}}|\mathcal{S}_k| + \kappa_{\mathrm{unc}}, \qquad
  \kappa_{\mathrm{uns}} = 1 + \frac{|\log\gamma_1|}{\log\gamma_2}, \qquad
  \kappa_{\mathrm{unc}} = \frac{\log(\sigma_{\max}/\sigma_0)}{\log\gamma_2} + N_{\mathcal{A}},$$
where $N_{\mathcal{A}} = \frac{p(q+1)}{|\log\gamma_h|}|\log\varepsilon_{\min}| +
\frac{|\log(\kappa_{\mathrm{acc}}/\kappa_h)|}{|\log\gamma_h|} + 1$. This is Lemma 14.2.3 of
[cartis2022evaluation] for ARqpIDA. -/
theorem IsARqpIDARun.le_card_succ (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ arqpIDATest f X P ε x j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) P.log_γ₂_pos.le)
  have hσ : 0 ≤ Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 (le_max_left _ _))) P.log_γ₂_pos.le
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ arqpIDATest f X P ε x j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hT := arqpDA_card_trial_le (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero
    (IsARqpIDARun.sigma_le hf hL hXC hAX hrun (k + 1))
  have hA := IsARqpIDARun.card_acc_le hf hL hXC hAX hrun hrc hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

/-- Evaluation complexity under the radii control. Assume $f \ge f_{\mathrm{low}}$ on $X$, the
smoothness hypothesis with $L_j \ge 1$, $X \subseteq C$ and
$A \supseteq \{y \in X \mid f(y) \le f(x_0)\}$, and the radii control
`Optimization.ARqpDARadiiControl u` with $\overline{L} = \overline{L}_f$ at every iteration.
Then every ARqpIDA run on $X$ reaches a first iterate $x_{k_\varepsilon} \in X$ that is an
$(\varepsilon, \delta_\varepsilon)$-approximate $q$-th order minimizer on $X$ for some radii
$\delta_\varepsilon \in (0, 1]^q$. Before it, with $c = \frac{1}{2}\eta_1\kappa_{\Delta m}\min_j
\varepsilon_j^{\pi_j}$ the decrease of `Optimization.IsARqpIDARun.decrease_ge` (Lemma 14.2.2)
and $N = (f(x_0) - f_{\mathrm{low}})/c$, at most
$$\Big(1 + \frac{|\log\gamma_1|}{\log\gamma_2}\Big)N +
  \frac{\log(\sigma_{\max}/\sigma_0)}{\log\gamma_2} + 2 + \frac{|\log\gamma_1|}{\log\gamma_2}$$
function evaluations and at most
$$N + \frac{p(q+1)}{|\log\gamma_h|}|\log\varepsilon_{\min}| +
  \frac{|\log(\kappa_{\mathrm{acc}}/\kappa_h)|}{|\log\gamma_h|} + 3$$
derivative estimates are made. This is Theorem 14.2.4 of [cartis2022evaluation] for ARqpIDA.

The radii control may be in either mode $u$: unit radii $\delta_{s_k} = 1$, which Step 2
guarantees for $X = E$ with $q \le 2$ or for $q = 1$ with $X$ convex, with
$\pi_j = (p+1)/(p-j+1)$; or the lower bounds of the type (12.2.51) at every order, available for
every $q$ and $X$, with $\pi_j = j(p+1)/p$. Here $\pi_j$ is `Optimization.arPiOf u p j`. The
radii control of Theorem 13.1.19, `Optimization.RadiiControl`, is the mode $u = (q \le 2)$. The
counts are as in `Optimization.IsARqpIDARun.complexity`. -/
theorem IsARqpIDARun.complexity_of_radiiControl (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    [Decidable u]
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arqpIDATest f X P ε x) kε ∧ x kε ∈ X ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j))) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hLb := hrun.one_le_Lbar hL
  have hA := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hC := arStepConstOf_pos (u := u) (q := P.q) (p := P.p) (sub_pos.2 P.θ_lt_one)
    (zero_lt_one.trans_le hA) (arKappaDelta1_pos (Lb := lipMax L P.p + ordMax P.p κg * P.κh)
      (σ := arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (P := P) (by linarith))
  have hm : 0 < epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    Optimization.epsMin_pos P.one_le_q fun j hj => Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
      epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := IsARqpIDARun.complexity hf hL hXC hAX hb hrun hrc hc
    fun k hk hρ hnot => (IsARqpIDARun.decrease_ge hf hL hXC hAX hrun (hrc k) hk hρ hnot).2
  exact ⟨kε, hk, hrun.mem kε, h1, h2⟩

end Iterations

section Splice

variable {X : Set E} {P : ARqpIDAParams} {ε : ℕ → ℝ} {f : E → ℝ} {κ : ℕ} {x x' : ℕ → E}
  {σ σ' : ℕ → ℝ} {δ δ' δ₁ δ₁' δs δs' h h' : ℕ → ℕ → ℝ} {dd dd' : ℕ → ℕ → E} {jk jk' : ℕ → ℕ}
  {s s' : ℕ → E} {acc acc' : ℕ → Prop}

/-- Splicing ARqpIDA iterations with exact Taylor data. Let the derivative data be the Taylor series
of $f$ at the iterates, and the ratio be (13.1.58). Suppose that the first sequences satisfy
`Optimization.ARqpDAStep` at every iteration $k < \kappa$, and that other sequences, whose
iterate, weight, radii $\delta^{(0)}$ and accuracies at $0$ are those of the first sequences at
$\kappa$, satisfy it at every iteration. Then the sequences equal to the first ones before
$\kappa$ and to the second ones, shifted by $\kappa$, from $\kappa$ on (`Nat.seqAppend`) satisfy
`Optimization.ARqpDAStep` at every iteration. -/
theorem ARqpDAStep.seqAppend
    (hpre : ∀ k < κ, ARqpDAStep X P ε x σ δ δ₁ δs h (fun i => ftaylorSeries ℝ f (x i)) dd jk s acc
      (arqpIDARatio f P (fun i => ftaylorSeries ℝ f (x i)) x s) k)
    (hpost : ∀ k, ARqpDAStep X P ε x' σ' δ' δ₁' δs' h' (fun i => ftaylorSeries ℝ f (x' i)) dd' jk'
      s' acc' (arqpIDARatio f P (fun i => ftaylorSeries ℝ f (x' i)) x' s') k)
    (hx : x' 0 = x κ) (hσ : σ' 0 = σ κ) (hδ : δ' 0 = δ κ) (hh : h' 0 = h κ) (k : ℕ) :
    ARqpDAStep X P ε (Nat.seqAppend κ x x') (Nat.seqAppend κ σ σ') (Nat.seqAppend κ δ δ')
      (Nat.seqAppend κ δ₁ δ₁') (Nat.seqAppend κ δs δs') (Nat.seqAppend κ h h')
      (fun i => ftaylorSeries ℝ f (Nat.seqAppend κ x x' i)) (Nat.seqAppend κ dd dd')
      (Nat.seqAppend κ jk jk') (Nat.seqAppend κ s s') (Nat.seqAppend κ acc acc')
      (arqpIDARatio f P (fun i => ftaylorSeries ℝ f (Nat.seqAppend κ x x' i))
        (Nat.seqAppend κ x x') (Nat.seqAppend κ s s')) k := by
  rcases lt_or_ge k κ with hk | hk
  · have hk1 : k + 1 ≤ κ := hk
    refine (hpre k hk).congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [arqpIDARatio, Nat.seqAppend_of_lt hk, Nat.seqAppend_eq_of_le hx hk1,
        Nat.seqAppend_eq_of_le hσ hk1, Nat.seqAppend_eq_of_le hδ hk1, Nat.seqAppend_eq_of_le hh hk1]
  · refine (hpost (k - κ)).congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [arqpIDARatio, Nat.seqAppend_of_le hk, Nat.seqAppend_succ_of_le hk]

/-- The ARqpIDA test at a spike of order $q$. Let $\varepsilon > 0$, and suppose that the Taylor
measures of $f$ at $x_k$, without constraints, satisfy $\phi^t_{f,j}(x_k) = 0$ for
$j \in [1, q - 1]$ and $\phi^t_{f,q}(x_k) = (c/q!)t^q$ for every radius $t \ge 0$. Then $x_k$ is
$(\varepsilon, \delta)$-approximately optimal for some radii $\delta \in (0, 1]^q$, with all
tolerances equal to $\varepsilon$ (`Optimization.arqpIDATest` on $E$), if and only if
$c \le \varepsilon$. -/
theorem arqpIDATest_univ_iff_of_taylorMeasure_eq {ε c : ℝ} {k : ℕ} (hε : 0 < ε)
    (hmeas : ∀ j ∈ Finset.Icc 1 P.q, ∀ t : ℝ, 0 ≤ t →
      taylorMeasure (ftaylorSeries ℝ f (x k)) j t univ =
        (if j = P.q then c / P.q ! else 0) * t ^ P.q) :
    arqpIDATest f univ P (fun _ => ε) x k ↔ c ≤ ε := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hqf : (0 : ℝ) < P.q ! := by positivity
  rw [arqpIDATest, Set.setOf_add_mem_univ]
  constructor
  · rintro ⟨δ', hδ', ht⟩
    have h1 := ht P.q hqm
    have hδq := (hδ' P.q hqm).1
    rw [hmeas P.q hqm _ hδq.le, ite_eq_left rfl, div_mul_eq_mul_div] at h1
    have h3 : 0 < δ' P.q ^ P.q := by positivity
    have := (div_le_div_iff_of_pos_right hqf).1 h1
    exact le_of_mul_le_mul_right this h3
  · intro hc
    refine ⟨fun _ => 1, fun _ _ => ⟨one_pos, le_rfl⟩, fun j hj => ?_⟩
    rw [hmeas j hj 1 zero_le_one, one_pow, mul_one, one_pow, mul_one]
    split_ifs with hjq
    · subst hjq; exact div_le_div_of_nonneg_right hc hqf.le
    · positivity

end Splice

end Optimization
