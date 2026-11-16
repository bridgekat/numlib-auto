/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.DynamicAccuracy
import Numlib.Optimization.Complexity.Telescoping
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.Basic
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.ModelBased.InexactRatio

/-!
# One iteration of ARqpIDA and ARqpEDA, and the step-length algebra

This file states one iteration of the adaptive-regularization methods with inexact derivatives and
dynamic accuracy ARqpIDA and ARqpEDA (Algorithms 13.1.2 and 13.3.2 of [cartis2022evaluation]) on a
feasible set $X$ (§14.2), and proves the facts about one iteration that the analyses of both methods
use. At iteration $k$ the method has an iterate $x_k$, a weight $\sigma_k$, radii $\delta^{(0)}_k$,
accuracies $h_{k,i}$ and inexact derivatives $\overline{\nabla}^i f(x_k)$, which form the derivative
data $D_k$. Write $\overline{\Delta T}_{f,j}(x_k, d)$ for the decrease along $d$ of the inexact
Taylor polynomial $\overline{T}_{f,j}(x_k, \cdot)$ of order $j$, and
$$\overline{m}_k(v) = \overline{T}_{f,p}(x_k, v) + \frac{\sigma_k}{(p+1)!} \|v\|^{p+1}, \qquad
  \Delta\overline{m}_k(v) = \overline{m}_k(0) - \overline{m}_k(v),$$
for the regularized inexact model (13.1.45) and its decrease.

Step 1 halves the optimality radii from $\delta^{(0)}_k$ to $\delta^{(1)}_k$. Step 2 computes a step
$s_k$ with radii $\delta_{s_k}$ for the model. Steps 3–4 accept or reject the step and update
$\sigma_k$. Step 5, the accuracy-improving branch, multiplies the accuracies by $\gamma_h$. The file
also gives the radii control (13.1.69)–(13.1.70), and the step-length algebra that turns the radius
inequalities of Lemmas 13.1.16 and 13.1.17 into lower bounds on $\|s_k\|^{p+1}$.

## Main definitions

* `Optimization.ARqpIDAParams`: the constants of ARqpIDA and ARqpEDA.
* `Optimization.ARqpStep1`, `Optimization.ARqpStep2`: Steps 1 and 2 at one iteration.
* `Optimization.ARqpDAStep`: one iteration, given the ratio $\rho_k$.
* `Optimization.ARqpDARadiiControl`: the radii control, with unit radii (mode $u$) or with lower
  bounds of the type (12.2.51) at every order (mode not $u$).
* `Optimization.RadiiControl`: the radii control in the mode $u = (q \le 2)$.
* `Optimization.arKappaDelta1`: the constant $\kappa^{(1)}_\delta(\sigma) =
  \varsigma\theta/(24\max\{\overline{L}, \sigma\})$ of (13.1.72).
* `Optimization.arPiOf`, `Optimization.arStepConstOf`: the exponents $\pi_j$ and the constants of
  the step-length bounds of Lemma 13.1.18.

## Main results

* `Optimization.arqpDA_card_trial_le`: the number of trial iterations is bounded by the number of
  successful ones (Lemma 13.1.9).
* `Optimization.ARqpStep1.radius_bounds`: the radii after Step 1 are bounded below (Lemma 13.1.11).
* `Optimization.arqpDA_radius_ge`: the radius bound $\delta^{(1)}_{k,j} \ge
  \kappa^{(1)}_\delta(\bar\sigma)\varepsilon_j$ (13.1.71) of Lemma 13.1.12.
* `Optimization.ARqpStep2.not_acc_of_le`: small accuracies give a trial iteration, the accuracy
  bound (13.1.73) of Lemma 13.1.12.
* `Optimization.ARqpDAStep.taylorDecrement_ge`: the predicted decrease of a trial iteration is
  positive (Lemma 13.1.13).
* `Optimization.arqp_pow_ge_of_radius_ineq`, `Optimization.arqp_pow_succ_ge`: lower bounds on the
  step length from a radius inequality.

## Implementation notes

* An iteration is a predicate `Optimization.ARqpDAStep` on whole sequences at an index $k$. Its
  arguments `δ k`, `δ₁ k` and `δs k` are the radii $\delta^{(0)}_k$, $\delta^{(1)}_k$ and
  $\delta_{s_k}$. The Step-1 displacement $d_{k,j}$ is `dd k j`. The order $j_k$ at which Step 2
  is entered is `jk k`. The flag `acc k` says that iteration $k$ is accuracy-improving.
* The halving loop of Step 1 is recorded by its effect, not by its single steps (see
  `Optimization.ARqpStep1`).
* The requirement $\varepsilon_j \le \delta_{0,j}$ is part of the run predicates, not of
  `Optimization.ARqpIDAParams`.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### ARqpIDA: constants and one iteration -/

/-- The constants of ARqpIDA (Step 0 of Algorithm 13.1.2 of [cartis2022evaluation], (13.1.51)), also
used by ARqpEDA. An element consists of the ARqp constants of `Optimization.ARqpParams`
($\sigma_0 > 0$, $0 \le \sigma_{\min} \le \sigma_0$, $0 < \eta_1 \le \eta_2 < 1$,
$0 < \gamma_1 < 1 < \gamma_2 \le \gamma_3$, $\theta \in (0, 1)$ and $\varsigma \in (0, 1]$)
together with $\sigma_{\min} > 0$, orders $1 \le q \le p$, an accuracy reduction factor
$\gamma_h \in (0, 1)$, constants $\kappa_s > 0$ and $\kappa_h \ge 0$, initial radii
$\delta_{0,j} \in (0, 1]$ for $j \in [1, q]$, and initial accuracies
$0 \le h_{0,i} \le \kappa_h$ for $i \in [1, p]$.

The requirement $\varepsilon_j \le \delta_{0,j}$ of (13.1.51) is part of the run predicates
`Optimization.IsARqpIDARun` and `Optimization.IsARqpEDARun`. -/
structure ARqpIDAParams extends ARqpParams where
  /-- The criticality order $q$. -/
  q : ℕ
  /-- The degree $p$ of the model. -/
  p : ℕ
  /-- The accuracy reduction factor $\gamma_h$ of Step 5. -/
  γh : ℝ
  /-- The constant $\kappa_s$ of the accuracy test (13.1.46). -/
  κs : ℝ
  /-- The bound $\kappa_h$ on the initial accuracies. -/
  κh : ℝ
  /-- The initial optimality radii $\delta_{0,j}$. -/
  δ₀ : ℕ → ℝ
  /-- The initial requested accuracies $h_{0,i}$. -/
  h₀ : ℕ → ℝ
  /-- The criticality order satisfies $q \ge 1$. -/
  one_le_q : 1 ≤ q
  /-- The orders satisfy $q \le p$. -/
  q_le_p : q ≤ p
  /-- The lower bound on the weights is positive: $\sigma_{\min} > 0$. -/
  σmin_pos : 0 < σmin
  /-- The accuracy reduction factor satisfies $\gamma_h > 0$. -/
  γh_pos : 0 < γh
  /-- The accuracy reduction factor satisfies $\gamma_h < 1$. -/
  γh_lt_one : γh < 1
  /-- The constant of the accuracy test satisfies $\kappa_s > 0$. -/
  κs_pos : 0 < κs
  /-- The bound on the initial accuracies satisfies $\kappa_h \ge 0$. -/
  κh_nonneg : 0 ≤ κh
  /-- The initial radii satisfy $\delta_{0,j} \in (0, 1]$ for $j \in [1, q]$. -/
  δ₀_mem : ∀ j ∈ Finset.Icc 1 q, δ₀ j ∈ Set.Ioc 0 1
  /-- The initial accuracies satisfy $h_{0,i} \ge 0$ for $i \in [1, p]$. -/
  h₀_nonneg : ∀ i ∈ Finset.Icc 1 p, 0 ≤ h₀ i
  /-- The initial accuracies satisfy $h_{0,i} \le \kappa_h$ for $i \in [1, p]$. -/
  h₀_le : ∀ i ∈ Finset.Icc 1 p, h₀ i ≤ κh

namespace ARqpIDAParams

variable (P : ARqpIDAParams)

/-- The degree satisfies $p \ge 1$. -/
theorem one_le_p : 1 ≤ P.p := P.one_le_q.trans P.q_le_p

/-- The order $1$ lies in $[1, q]$. -/
theorem one_mem_Icc : 1 ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩

/-- The orders satisfy $[1, q] \subseteq [1, p]$. -/
theorem Icc_q_subset : Finset.Icc 1 P.q ⊆ Finset.Icc 1 P.p :=
  Finset.Icc_subset_Icc le_rfl P.q_le_p

end ARqpIDAParams

section ARStep

variable {X : Set E} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x : ℕ → E} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The decrease $\Delta\overline{m}_k(v) = \overline{m}_k(0) - \overline{m}_k(v)$ of the
regularized inexact model $\overline{m}_k(v) = \overline{T}_{f,p}(x_k, v) + \sigma_k
\|v\|^{p+1}/(p+1)!$ of (13.1.45) of [cartis2022evaluation], where
$\overline{T}_{f,p}(x_k, \cdot)$ is the Taylor sum of degree $p$ of the derivative data $D_k$. -/
noncomputable abbrev arModelDec (P : ARqpIDAParams) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (σ : ℕ → ℝ) (k : ℕ) (v : E) : ℝ :=
  regularizedModel (D k) P.p (σ k) 0 - regularizedModel (D k) P.p (σ k) v

/-- The model decrease is $\Delta\overline{m}_k(v) = \overline{\Delta T}_{f,p}(x_k, v) - \sigma_k
\|v\|^{p+1}/(p+1)!$. -/
theorem arModelDec_eq (k : ℕ) (v : E) :
    arModelDec P D σ k v =
      (D k).taylorDecrement P.p v - σ k / ((P.p + 1)! : ℝ) * ‖v‖ ^ (P.p + 1) := by
  rw [arModelDec, regularizedModel_zero_right, regularizedModel_def,
    FormalMultilinearSeries.taylorDecrement]
  ring

/-- The test (13.1.53) of Step 1.2 of [cartis2022evaluation] at order $j$ of iteration $k$, with the
radius $\delta^{(1)}_{k,j}$:
$$\overline{\Delta T}_{f,j}(x_k, d_{k,j}) \le \frac{\varsigma\varepsilon_j
  (\delta^{(1)}_{k,j})^j}{2\,j!}.$$
-/
def arqpDAPass (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (δ₁ : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E) (k j : ℕ) : Prop :=
  (D k).taylorDecrement j (dd k j) ≤ P.ς * ε j * δ₁ k j ^ j / j ! / 2

/-- Step 2 of ARqpIDA at iteration $k$ on the feasible set $X$ (Algorithm 13.1.2 of
[cartis2022evaluation]). It is entered at the least order $j_k \in [1, q]$ at which the test
(13.1.53) fails, and the condition (13.1.54) holds at $j_k$. The trial point $x_k + s_k$ lies in
$X$, and $s_k$ decreases the model at least as much as $d_{k,j_k}$ (13.1.55). Either
$\|s_k\| \ge 1$ and $\delta_{s_k} = \delta^{(1)}_k$ (13.1.56), or the radii
$\delta_{s_k,\ell} \in (0, 1]$ and some model displacements satisfy (13.1.57) for every
$\ell \in [1, q]$. The iteration is accuracy-improving if and only if $\|s_k\| < 1$ and the
accuracy test (13.1.46) fails for some $i \in [1, p]$. -/
structure ARqpStep2 (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → E) (σ : ℕ → ℝ)
    (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E) (acc : ℕ → Prop) (k : ℕ) : Prop where
  /-- The order $j_k$ lies in $[1, q]$. -/
  jk_mem : jk k ∈ Finset.Icc 1 P.q
  /-- The test (13.1.53) fails at the order $j_k$. -/
  not_pass : ¬ arqpDAPass P ε D δ₁ dd k (jk k)
  /-- The test (13.1.53) holds at every order $j \in [1, q]$ with $j < j_k$. -/
  pass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < jk k → arqpDAPass P ε D δ₁ dd k j
  /-- The radii above $j_k$ are not examined in Step 1: $\delta^{(1)}_{k,j} = \delta^{(0)}_{k,j}$
  for every $j \in [1, q]$ with $j > j_k$. -/
  radius_gt : ∀ j ∈ Finset.Icc 1 P.q, jk k < j → δ₁ k j = δ k j
  /-- The condition (13.1.54) at $j_k$: $\Delta\overline{m}_k(d_{k,j_k}) \ge
  \varsigma\varepsilon_{j_k}(\delta^{(1)}_{k,j_k})^{j_k}/(4\,j_k!)$. -/
  model_dec : P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (dd k (jk k))
  /-- The trial point $x_k + s_k$ lies in $X$. -/
  mem : x k + s k ∈ X
  /-- The condition (13.1.55): $\Delta\overline{m}_k(d_{k,j_k}) \le \Delta\overline{m}_k(s_k)$. -/
  dec_le : arModelDec P D σ k (dd k (jk k)) ≤ arModelDec P D σ k (s k)
  /-- Either $\|s_k\| \ge 1$ and $\delta_{s_k} = \delta^{(1)}_k$ (13.1.56), or (13.1.57) holds: for
  every $\ell \in [1, q]$, $\delta_{s_k,\ell} \in (0, 1]$, and some $\varsigma$-approximate
  optimality displacement of the order-$\ell$ Taylor decrement of $\overline{m}_k$ at $s_k$, for
  the radius $\delta_{s_k,\ell}$ and the displacements $e$ with $x_k + s_k + e \in X$, has
  decrease at most $\varsigma\theta\varepsilon_\ell\delta_{s_k,\ell}^\ell/\ell!$. -/
  radii : (1 ≤ ‖s k‖ ∧ δs k = δ₁ k) ∨ ∀ ℓ ∈ Finset.Icc 1 P.q, δs k ℓ ∈ Set.Ioc 0 1 ∧
    ∃ dm, IsApproxMeasureStep
        ((ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ)
        (δs k ℓ) {e | x k + s k + e ∈ X} P.ς dm ∧
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ dm ≤
        P.ς * P.θ * ε ℓ * δs k ℓ ^ ℓ / ℓ !
  /-- The iteration branches to Step 5 if and only if $\|s_k\| < 1$ and the accuracy test (13.1.46)
  fails for some $i \in [1, p]$, that is $\kappa_s \|s_k\|^{p-i+1} < h_{k,i}$. -/
  acc_iff : acc k ↔ ‖s k‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖s k‖ ^ (P.p - i + 1) < h k i

/-- Step 1 of ARqpIDA and ARqpEDA (Steps 1.1–1.4 of Algorithm 13.1.2 of [cartis2022evaluation]) at
iteration $k$ on the feasible set $X$, with the radii $\delta^{(0)}_k$ at the start of Step 1
(13.1.60) and $\delta^{(1)}_k$ at its end (13.1.61). The halving loop halves $\delta_{k,j}$
while (13.1.53) and (13.1.54) both fail, and it is recorded by its effect. For every
$j \in [1, q]$: $0 < \delta^{(1)}_{k,j} \le \delta^{(0)}_{k,j}$ and
$\delta^{(1)}_{k,j} = \delta^{(0)}_{k,j}/2^m$ for some $m \in \mathbb{N}$; if
$\delta^{(1)}_{k,j} < \delta^{(0)}_{k,j}$, then $2\delta^{(1)}_{k,j} \le \delta^{(0)}_{k,j}$,
both tests failed at the radius $2\delta^{(1)}_{k,j}$ of the last halving, and (13.1.53) failed
at the radius $\delta^{(0)}_{k,j}$ of the first halving; and the final displacement $d_{k,j}$
satisfies (13.1.52). -/
structure ARqpStep1 (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → E) (σ : ℕ → ℝ)
    (δ δ₁ : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (k : ℕ) :
    Prop where
  /-- The final radii are positive: $\delta^{(1)}_{k,j} > 0$ for $j \in [1, q]$. -/
  radius_pos : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ₁ k j
  /-- The radii do not increase: $\delta^{(1)}_{k,j} \le \delta^{(0)}_{k,j}$ for $j \in [1, q]$. -/
  radius_le : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ≤ δ k j
  /-- The halving loop of Steps 1.1–1.4: if $\delta^{(1)}_{k,j} < \delta^{(0)}_{k,j}$ for some
  $j \in [1, q]$, then $2\delta^{(1)}_{k,j} \le \delta^{(0)}_{k,j}$, some $d'$ with
  $\|d'\| \le 2\delta^{(1)}_{k,j}$ and $x_k + d' \in X$ has $\overline{\Delta T}_{f,j}(x_k,
  d') > \varsigma\varepsilon_j(2\delta^{(1)}_{k,j})^j/(2\,j!)$ and $\Delta\overline{m}_k(d') <
  \varsigma\varepsilon_j(2\delta^{(1)}_{k,j})^j/(4\,j!)$, and some $d_0$ with
  $\|d_0\| \le \delta^{(0)}_{k,j}$ and $x_k + d_0 \in X$ has $\overline{\Delta T}_{f,j}(x_k,
  d_0) > \varsigma\varepsilon_j(\delta^{(0)}_{k,j})^j/(2\,j!)$. -/
  halving : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j < δ k j → 2 * δ₁ k j ≤ δ k j ∧
    (∃ d', ‖d'‖ ≤ 2 * δ₁ k j ∧ x k + d' ∈ X ∧
      P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 2 < (D k).taylorDecrement j d' ∧
      arModelDec P D σ k d' < P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 4) ∧
    ∃ d₀, ‖d₀‖ ≤ δ k j ∧ x k + d₀ ∈ X ∧
      P.ς * ε j * δ k j ^ j / j ! / 2 < (D k).taylorDecrement j d₀
  /-- The final radii come from halving: $\delta^{(1)}_{k,j} = \delta^{(0)}_{k,j}/2^m$ for some
  $m \in \mathbb{N}$, for every $j \in [1, q]$. -/
  dyadic : ∀ j ∈ Finset.Icc 1 P.q, ∃ m : ℕ, δ₁ k j = δ k j / 2 ^ m
  /-- The condition (13.1.52): for $j \in [1, q]$, $d_{k,j}$ is a $\varsigma$-approximate optimality
  displacement of $\overline{\Delta T}_{f,j}(x_k, \cdot)$ for the radius $\delta^{(1)}_{k,j}$
  and the displacements $e$ with $x_k + e \in X$. -/
  witness : ∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((D k).taylorDecrement j) (δ₁ k j)
    {e | x k + e ∈ X} P.ς (dd k j)

/-- One iteration $k$ of ARqpIDA and ARqpEDA (Steps 1, 2, 4 and 5 of Algorithm 13.1.2 of
[cartis2022evaluation]) on the feasible set $X$, given the ratio $\rho_k$. Step 1
(`Optimization.ARqpStep1`) holds. If the test (13.1.53) holds at every order $j \in [1, q]$, the
iteration is accuracy-improving; if the test fails at some order, Step 2
(`Optimization.ARqpStep2`) holds. A trial iteration, that is an iteration that is not
accuracy-improving, accepts or rejects the step and updates $\sigma$ by (13.1.59)
(`Optimization.ARAcceptance`); it passes the radii $\delta^{(0)}_{k+1} = \delta_{s_k}$ to the
next iteration if $\rho_k \ge \eta_1$ and $\|s_k\| < 1$, and
$\delta^{(0)}_{k+1} = \delta^{(1)}_k$ otherwise; it keeps the accuracies; and it keeps the
derivative estimates, $D_{k+1} = D_k$, if $\rho_k < \eta_1$. An accuracy-improving iteration
keeps $x_k$, $\sigma_k$ and $\delta^{(0)}_k$, and sets $h_{k+1,i} = \gamma_h h_{k,i}$ for every
$i$.

The ratio $\rho_k$ is a parameter: it is the ratio (13.1.58) with exact function values for
ARqpIDA and the ratio (13.3.19) with inexact function values for ARqpEDA. Step 3 of ARqpEDA,
which computes the inexact function values, is stated separately. -/
structure ARqpDAStep (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → E) (σ : ℕ → ℝ)
    (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E) (acc : ℕ → Prop) (ρ : ℕ → ℝ) (k : ℕ) :
    Prop extends ARqpStep1 X P ε x σ δ δ₁ D dd k where
  /-- If the test (13.1.53) holds at every order $j \in [1, q]$, Step 1 branches to Step 5: the
  iteration is accuracy-improving. -/
  acc_of_pass : (∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j) → acc k
  /-- If the test (13.1.53) fails at some order $j \in [1, q]$, Step 2 holds. -/
  step2 : (∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
    ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k
  /-- On a trial iteration, Steps 3–4 hold: the step is accepted or rejected and $\sigma$ is updated
  for the ratio $\rho_k$. -/
  accept : ¬ acc k → ARAcceptance P.toARParams (ρ k) (x k) (s k) (x (k + 1)) (σ k) (σ (k + 1))
  /-- On a trial iteration, the next radii are $\delta^{(0)}_{k+1} = \delta_{s_k}$ if
  $\eta_1 \le \rho_k$ and $\|s_k\| < 1$, and $\delta^{(0)}_{k+1} = \delta^{(1)}_k$ otherwise
  (Step 3). -/
  radii_trial : ¬ acc k →
    δ (k + 1) = if P.η₁ ≤ ρ k ∧ ‖s k‖ < 1 then δs k else δ₁ k
  /-- On a trial iteration, the accuracies are kept: $h_{k+1} = h_k$. -/
  h_trial : ¬ acc k → h (k + 1) = h k
  /-- On an unsuccessful trial iteration ($\rho_k < \eta_1$), no new derivative estimates are made
  at the unchanged iterate: $D_{k+1} = D_k$. -/
  D_unsucc : ¬ acc k → ρ k < P.η₁ → D (k + 1) = D k
  /-- Step 5 keeps the iterate: $x_{k+1} = x_k$. -/
  x_acc : acc k → x (k + 1) = x k
  /-- Step 5 keeps the radii: $\delta^{(0)}_{k+1} = \delta^{(0)}_k$. -/
  δ_acc : acc k → δ (k + 1) = δ k
  /-- Step 5 keeps the weight: $\sigma_{k+1} = \sigma_k$. -/
  σ_acc : acc k → σ (k + 1) = σ k
  /-- Step 5 multiplies the accuracies by $\gamma_h$: $h_{k+1,i} = \gamma_h h_{k,i}$ for every $i$.
  -/
  h_acc : acc k → ∀ i, h (k + 1) i = P.γh * h k i

/-- The radii control of ARqpIDA and ARqpEDA at iteration $k$ ((13.1.69)–(13.1.70) and §14.2 of
[cartis2022evaluation]), in one of two modes selected by the proposition $u$. After a trial
iteration $k$ with a short step $\|s_k\| < 1$: if $u$ holds, then $\delta_{s_k,j} = 1$ for all
$j \in [1, q]$ (unit radii); if $u$ fails, then
$$\delta_{s_k,j} \ge \frac{\varsigma\theta\varepsilon_j}{24\max\{\overline{L}, \sigma_k\}}
  \qquad \text{for all } j \in [1, q],$$
the lower bound of the type (12.2.51) at every order.

Algorithm 12.2.3 delivers unit radii for $q \le 2$ without constraints, and for $q = 1$ on a
convex feasible set. The lower bound is available in every case, in particular for $q > 2$ or
with a general feasible set. The complexity orders depend on the mode through the exponents of
`Optimization.arPiOf`. The argument `Lb` is the constant $\overline{L}$. -/
def ARqpDARadiiControl (u : Prop) (P : ARqpIDAParams) (ε : ℕ → ℝ) (Lb : ℝ) (σ : ℕ → ℝ)
    (δs : ℕ → ℕ → ℝ) (s : ℕ → E) (acc : ℕ → Prop) (k : ℕ) : Prop :=
  ¬ acc k → ‖s k‖ < 1 → (u → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) ∧
    (¬ u → ∀ j ∈ Finset.Icc 1 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j)

/-- The radii control of [cartis2022evaluation], (13.1.69)–(13.1.70), in the mode fixed by the
order: `Optimization.ARqpDARadiiControl` with unit radii exactly when $q \le 2$. After a trial
iteration $k$ with $\|s_k\| < 1$, $\delta_{s_k,j} = 1$ for all $j \in [1, q]$ if $q \le 2$, and
$\delta_{s_k,j} \ge \varsigma\theta\varepsilon_j/(24\max\{\overline{L}, \sigma_k\})$ for all
$j \in [1, q]$ if $q > 2$.

Unit radii at the orders $j \le 2$ together with the lower bound at the orders $j \ge 3$ imply
it (`Optimization.RadiiControl.of_unit_le_two`). -/
def RadiiControl (P : ARqpIDAParams) (ε : ℕ → ℝ) (Lb : ℝ) (σ : ℕ → ℝ) (δs : ℕ → ℕ → ℝ)
    (s : ℕ → E) (acc : ℕ → Prop) (k : ℕ) : Prop :=
  ARqpDARadiiControl (P.q ≤ 2) P ε Lb σ δs s acc k

omit [InnerProductSpace ℝ E] in
/-- The radii control `Optimization.RadiiControl` unfolded: after a trial iteration $k$ with
$\|s_k\| < 1$, $\delta_{s_k,j} = 1$ for $j \in [1, q]$ if $q \le 2$, and $\delta_{s_k,j} \ge
\varsigma\theta\varepsilon_j/(24\max\{\overline{L}, \sigma_k\})$ for $j \in [1, q]$ if $2 < q$. -/
theorem radiiControl_iff {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → E} {acc : ℕ → Prop} {k : ℕ} :
    RadiiControl P ε Lb σ δs s acc k ↔
      (¬ acc k → ‖s k‖ < 1 → (P.q ≤ 2 → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) ∧
        (2 < P.q → ∀ j ∈ Finset.Icc 1 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j)) := by
  simp only [RadiiControl, ARqpDARadiiControl, not_le]

omit [InnerProductSpace ℝ E] in
/-- Unit radii give the radii control in either mode. Let $\overline{L} \ge 1$ and
$\varepsilon_j \le 1$ for $j \in [1, q]$. If $\delta_{s_k,j} = 1$ for all $j \in [1, q]$
whenever iteration $k$ is a trial iteration with $\|s_k\| < 1$, then
`Optimization.ARqpDARadiiControl u` holds at $k$ for every proposition $u$.

The lower bound $\varsigma\theta\varepsilon_j/(24\max\{\overline{L}, \sigma_k\}) \le 1$ of the
second mode is automatic. -/
theorem ARqpDARadiiControl.of_unit {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → E} {acc : ℕ → Prop} {k : ℕ} {u : Prop} (hLb : 1 ≤ Lb)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ 1)
    (h1 : ¬ acc k → ‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) :
    ARqpDARadiiControl u P ε Lb σ δs s acc k := by
  intro hk hs1
  refine ⟨fun _ => h1 hk hs1, fun _ j hj => ?_⟩
  rw [h1 hk hs1 j hj]
  have hM : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  rw [div_le_one (by positivity)]
  have h0 : P.ς * P.θ ≤ 1 := (mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le
  rcases le_or_gt (ε j) 0 with hε0 | hε0
  · have : P.ς * P.θ * ε j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hε0
    linarith
  · have : P.ς * P.θ * ε j ≤ 1 := by nlinarith [hε j hj]
    linarith

omit [InnerProductSpace ℝ E] in
/-- Let $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$ and $\overline{L} \ge 1$. Suppose that after a
trial iteration $k$ with $\|s_k\| < 1$, $\delta_{s_k,j} = 1$ for $j \in [1, \min\{2, q\}]$ and
$\delta_{s_k,j} \ge \varsigma\theta\varepsilon_j/(24\max\{\overline{L}, \sigma_k\})$ for
$j \in [3, q]$. Then the radii control `Optimization.RadiiControl` of [cartis2022evaluation],
(13.1.69)–(13.1.70), holds at $k$. -/
theorem RadiiControl.of_unit_le_two {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → E} {acc : ℕ → Prop} {k : ℕ}
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hLb : 1 ≤ Lb)
    (h : ¬ acc k → ‖s k‖ < 1 → (∀ j ∈ Finset.Icc 1 (min 2 P.q), δs k j = 1) ∧
      ∀ j ∈ Finset.Icc 3 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j) :
    RadiiControl P ε Lb σ δs s acc k := by
  intro hk hs1
  obtain ⟨h1, h2⟩ := h hk hs1
  refine ⟨fun hq j hj => h1 j ?_, fun _ j hj => ?_⟩
  · obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
    exact Finset.mem_Icc.2 ⟨hj1, le_min (hjq.trans hq) hjq⟩
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  rcases le_or_gt j 2 with hj2 | hj2
  · rw [h1 j (Finset.mem_Icc.2 ⟨hj1, le_min hj2 hjq⟩)]
    have hM : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
    have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
    have hεj := hε j hj
    rw [div_le_one (by positivity)]
    have : P.ς * P.θ * ε j ≤ 1 :=
      (mul_le_of_le_one_left hεj.1.le
        ((mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le)).trans hεj.2
    linarith
  · exact h2 j (Finset.mem_Icc.2 ⟨hj2, hjq⟩)

namespace ARqpDAStep

variable (hs : ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ k)
include hs

/-- A trial iteration went through Step 2: if iteration $k$ is not accuracy-improving, then
`Optimization.ARqpStep2` holds at $k$. -/
theorem step2_of_not_acc (hk : ¬ acc k) : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k := by
  refine hs.step2 ?_
  by_contra hc
  push Not at hc
  exact hk (hs.acc_of_pass hc)

/-- On a trial iteration, $\sigma_{k+1}$ is obtained from $\sigma_k$ by the update rule (2.4.4) for
the ratio $\rho_k$. -/
theorem update (hk : ¬ acc k) :
    ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin (ρ k) (σ k) (σ (k + 1)) :=
  (hs.accept hk).2

/-- The iterate is kept, $x_{k+1} = x_k$, unless iteration $k$ is a successful trial iteration
($\rho_k \ge \eta_1$). -/
theorem iterate_succ_eq (hk : ¬ (¬ acc k ∧ P.η₁ ≤ ρ k)) : x (k + 1) = x k := by
  by_cases ha : acc k
  · exact hs.x_acc ha
  · exact (hs.accept ha).eq_self (not_le.1 fun h' => hk ⟨ha, h'⟩)

/-- A successful trial iteration moves to the trial point: $x_{k+1} = x_k + s_k$. -/
theorem iterate_succ_eq_add (hk : ¬ acc k) (hρ : P.η₁ ≤ ρ k) : x (k + 1) = x k + s k :=
  (hs.accept hk).eq_add hρ

/-- The iterates stay feasible: if $x_k \in X$, then $x_{k+1} \in X$. -/
theorem mem_succ (hx : x k ∈ X) : x (k + 1) ∈ X := by
  by_cases hc : ¬ acc k ∧ P.η₁ ≤ ρ k
  · rw [hs.iterate_succ_eq_add hc.1 hc.2]; exact (hs.step2_of_not_acc hc.1).mem
  · rw [hs.iterate_succ_eq hc]; exact hx

/-- One iteration involves only the data at the indices $k$ and $k + 1$. Suppose that the step
predicate `Optimization.ARqpDAStep` holds at $k$ for some sequences, and consider other
sequences such that: the iterates, weights, radii $\delta^{(0)}$, accuracies and derivative
estimates at $k'$ and $k' + 1$ equal those of the first sequences at $k$ and $k + 1$; and the
radii $\delta^{(1)}$ and $\delta_s$, the Step-1 displacements, the order $j_k$, the step and the
ratio at $k'$ equal those at $k$, and the flag at $k'$ holds if and only if the flag at $k$
holds. Then the step predicate holds for the other sequences at $k'$.

This is used to splice runs. -/
theorem congr {x' : ℕ → E} {σ' : ℕ → ℝ} {δ' δ₁' δs' : ℕ → ℕ → ℝ} {h' : ℕ → ℕ → ℝ}
    {D' : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd' : ℕ → ℕ → E} {jk' : ℕ → ℕ} {s' : ℕ → E}
    {acc' : ℕ → Prop} {ρ' : ℕ → ℝ} {k' : ℕ} (hx : x' k' = x k) (hx1 : x' (k' + 1) = x (k + 1))
    (hσ : σ' k' = σ k) (hσ1 : σ' (k' + 1) = σ (k + 1)) (hδ : δ' k' = δ k)
    (hδ1 : δ' (k' + 1) = δ (k + 1)) (hδ₁ : δ₁' k' = δ₁ k) (hδs : δs' k' = δs k)
    (hh : h' k' = h k) (hh1 : h' (k' + 1) = h (k + 1)) (hD : D' k' = D k)
    (hD1 : D' (k' + 1) = D (k + 1)) (hdd : dd' k' = dd k) (hjk : jk' k' = jk k)
    (hs' : s' k' = s k) (hacc : acc' k' ↔ acc k) (hρ : ρ' k' = ρ k) :
    ARqpDAStep X P ε x' σ' δ' δ₁' δs' h' D' dd' jk' s' acc' ρ' k' := by
  obtain ⟨⟨hpos, hle, hhalf, hdy, hw⟩, hap, hst, hac, hrt, hht, hdu, hxa, hδa, hσa, hha⟩ := hs
  have hP : ∀ j, arqpDAPass P ε D' δ₁' dd' k' j ↔ arqpDAPass P ε D δ₁ dd k j := fun j => by
    simp only [arqpDAPass, hD, hδ₁, hdd]
  have hM : ∀ v, arModelDec P D' σ' k' v = arModelDec P D σ k v := fun v => by
    simp only [arModelDec, hD, hσ]
  refine ⟨⟨fun j hj => ?_, fun j hj => ?_, fun j hj hlt => ?_, fun j hj => ?_, fun j hj => ?_⟩,
    fun hp => hacc.2 (hap fun j hj => (hP j).1 (hp j hj)), fun ⟨j, hj, hf⟩ => ?_,
    fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha hr => ?_, fun ha => ?_, fun ha => ?_,
    fun ha => ?_, fun ha => ?_⟩
  · rw [hδ₁]; exact hpos j hj
  · rw [hδ₁, hδ]; exact hle j hj
  · rw [hδ₁, hδ] at hlt ⊢
    simp only [hx, hM, hD]
    exact hhalf j hj hlt
  · rw [hδ₁, hδ]; exact hdy j hj
  · rw [hδ₁, hD, hx, hdd]; exact hw j hj
  · obtain ⟨hjm, hnp, hpl, hrg, hmd, hmem, hdl, hrad, hai⟩ :=
      hst ⟨j, hj, fun h' => hf ((hP j).2 h')⟩
    refine ⟨hjk ▸ hjm, fun h' => hnp ((hP _).1 (hjk ▸ h')), fun i hi hlt => (hP i).2
      (hpl i hi (hjk ▸ hlt)), fun i hi hlt => by rw [hδ₁, hδ]; exact hrg i hi (hjk ▸ hlt),
      by rw [hM, hjk, hdd, hδ₁]; exact hmd, by rw [hx, hs']; exact hmem,
      by rw [hM, hM, hjk, hdd, hs']; exact hdl, ?_, by rw [hacc, hs', hh]; exact hai⟩
    rw [hs', hδs, hD, hσ, hx, hδ₁]; exact hrad
  · rw [hρ, hx, hs', hx1, hσ, hσ1]; exact hac (fun h => ha (hacc.2 h))
  · rw [hδ1, hρ, hs', hδs, hδ₁]; exact hrt (fun h => ha (hacc.2 h))
  · rw [hh1, hh]; exact hht (fun h => ha (hacc.2 h))
  · rw [hD1, hD]; exact hdu (fun h => ha (hacc.2 h)) (hρ ▸ hr)
  · rw [hx1, hx]; exact hxa (hacc.1 ha)
  · rw [hδ1, hδ]; exact hδa (hacc.1 ha)
  · rw [hσ1, hσ]; exact hσa (hacc.1 ha)
  · rw [hh1, hh]; exact hha (hacc.1 ha)

end ARqpDAStep

/-- If the step predicate `Optimization.ARqpDAStep` holds at every iteration $i < k$ and
$x_0 \in X$, then $x_k \in X$. -/
theorem arqpDA_mem (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hx0 : x 0 ∈ X) : x k ∈ X := by
  induction k with
  | zero => exact hx0
  | succ k ih => exact (hstep k k.lt_succ_self).mem_succ (ih fun i hi => hstep i (by omega))

/-- If Step 2 holds at iteration $k$ and $\|s_k\| < 1$, then (13.1.57) holds: for every
$\ell \in [1, q]$, $\delta_{s_k,\ell} \in (0, 1]$, and some $\varsigma$-approximate optimality
displacement of the order-$\ell$ Taylor decrement of $\overline{m}_k$ at $s_k$, for the radius
$\delta_{s_k,\ell}$ and the displacements $e$ with $x_k + s_k + e \in X$, has decrease at most
$\varsigma\theta\varepsilon_\ell\delta_{s_k,\ell}^\ell/\ell!$. -/
theorem ARqpStep2.radii_of_lt (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hs1 : ‖s k‖ < 1) :
    ∀ ℓ ∈ Finset.Icc 1 P.q, δs k ℓ ∈ Set.Ioc 0 1 ∧
      ∃ dm, IsApproxMeasureStep
          ((ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ)
          (δs k ℓ) {e | x k + s k + e ∈ X} P.ς dm ∧
        (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ dm ≤
          P.ς * P.θ * ε ℓ * δs k ℓ ^ ℓ / ℓ ! :=
  h2.radii.resolve_left fun h' => absurd h'.1 (not_le.2 hs1)

/-- If Step 2 holds at iteration $k$, the iteration is not accuracy-improving and $\|s_k\| < 1$,
then the accuracy test (13.1.46) holds: $h_{k,i} \le \kappa_s \|s_k\|^{p-i+1}$ for every
$i \in [1, p]$. -/
theorem ARqpStep2.accuracy_le_of_not_acc (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hk : ¬ acc k) (hs1 : ‖s k‖ < 1) :
    ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1) := by
  intro i hi
  by_contra hc
  exact hk (h2.acc_iff.2 ⟨hs1, i, hi, not_le.1 hc⟩)

/-- Invariants of ARqpIDA and ARqpEDA sequences. If the step predicate `Optimization.ARqpDAStep`
holds at every iteration $i < k$ and the initial weight, radii and accuracies are $\sigma_0$,
$\delta_0$ and $h_0$ of $P$, then $\sigma_k \ge \sigma_{\min}$, $\delta^{(0)}_{k,j} \in (0, 1]$
for $j \in [1, q]$, and $0 \le h_{k,i} \le \kappa_h$ for $i \in [1, p]$. -/
theorem arqpDA_invariants (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) :
    P.σmin ≤ σ k ∧ (∀ j ∈ Finset.Icc 1 P.q, 0 < δ k j ∧ δ k j ≤ 1) ∧
      ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ h k i ∧ h k i ≤ P.κh := by
  induction k with
  | zero =>
    rw [hσ0, hδ0, hh0]
    exact ⟨P.σmin_le_σ₀, fun j hj => P.δ₀_mem j hj, fun i hi => ⟨P.h₀_nonneg i hi, P.h₀_le i hi⟩⟩
  | succ k ih =>
    obtain ⟨hσ, hδ, hh⟩ := ih fun i hi => hstep i (hi.trans k.lt_succ_self)
    have hk := hstep k k.lt_succ_self
    by_cases ha : acc k
    · refine ⟨by rw [hk.σ_acc ha]; exact hσ, by rw [hk.δ_acc ha]; exact hδ, fun i hi => ?_⟩
      rw [hk.h_acc ha i]
      obtain ⟨h1, h2⟩ := hh i hi
      exact ⟨mul_nonneg P.γh_pos.le h1, (mul_le_of_le_one_left h1 P.γh_lt_one.le).trans h2⟩
    refine ⟨(hk.update ha).sigmaMin_le P.σmin_nonneg P.one_le_γ₂ hσ, ?_,
      by rw [hk.h_trial ha]; exact hh⟩
    intro j hj
    rw [hk.radii_trial ha]
    split_ifs with hc
    · exact ((hk.step2_of_not_acc ha).radii_of_lt hc.2 j hj).1
    · exact ⟨hk.radius_pos j hj, (hk.radius_le j hj).trans (hδ j hj).2⟩

/-- Under the hypotheses of `Optimization.arqpDA_invariants`, the weight is positive:
$\sigma_k > 0$. -/
theorem arqpDA_sigma_pos (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) : 0 < σ k :=
  P.σmin_pos.trans_le (arqpDA_invariants hstep hσ0 hδ0 hh0).1

/-! ### Counting the trial iterations -/

/-- Let the step predicate `Optimization.ARqpDAStep` hold at every iteration $i \le k$, let the
initial weight, radii and accuracies be those of $P$, and let $\sigma_{k+1} \le \sigma_{\max}$.
Then (13.1.62)
$$|\mathcal{T}_k| \le |\mathcal{S}_k| \Big(1 + \frac{|\log\gamma_1|}{\log\gamma_2}\Big) +
  \frac{\log(\sigma_{\max}/\sigma_0)}{\log\gamma_2},$$
where $\mathcal{T}_k$ is the set of trial iterations $i \in [0, k]$ and $\mathcal{S}_k$ is the
set of successful trial iterations $i \in [0, k]$, those with $\rho_i \ge \eta_1$. This is Lemma
13.1.9 of [cartis2022evaluation].

The two sets are `Optimization.successSet` of the predicates "not accuracy-improving" and "not
accuracy-improving and $\eta_1 \le \rho_i$". -/
theorem arqpDA_card_trial_le (hstep : ∀ i ≤ k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) {σmax : ℝ}
    (hσmax : σ (k + 1) ≤ σmax) :
    ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ := by
  have hpos : ∀ i ≤ k, 0 < σ i := fun i hi =>
    arqpDA_sigma_pos (fun j hj => hstep j (by omega)) hσ0 hδ0 hh0
  have h := card_successSet_or_le_of_lower_ratio (σ := σ) (k := k)
    (succ := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) (fail := fun i => ¬ acc i ∧ ρ i < P.η₁)
    (hσ0 ▸ P.σ₀_pos) P.γ₁_pos P.γ₁_le_one P.one_lt_γ₂
    (fun i _ hi hf => not_le.2 hf.2 hi.2)
    (fun i hi hs => ((hstep i hi).update hs.1).mul_le_of_le hs.2 P.γ₁_le_one (hpos i hi).le)
    (fun i hi hf => ((hstep i hi).update hf.1).mul_le_of_lt hf.2)
    (fun i hi hs hf => by
      have ha : acc i := by
        by_contra ha
        rcases le_or_gt P.η₁ (ρ i) with hρ | hρ
        · exact hs ⟨ha, hρ⟩
        · exact hf ⟨ha, hρ⟩
      rw [(hstep i hi).σ_acc ha])
    hσmax
  rw [hσ0] at h
  have hset : successSet (fun i => (¬ acc i ∧ P.η₁ ≤ ρ i) ∨ (¬ acc i ∧ ρ i < P.η₁)) k =
      successSet (fun i => ¬ acc i) k := by
    ext i
    simp only [mem_successSet]
    constructor
    · rintro ⟨hi, (h1 | h1)⟩ <;> exact ⟨hi, h1.1⟩
    · rintro ⟨hi, h1⟩
      exact ⟨hi, (le_or_gt P.η₁ (ρ i)).imp (fun h2 => ⟨h1, h2⟩) fun h2 => ⟨h1, h2⟩⟩
  rwa [hset] at h

/-! ### Radii, accuracy and decrease at one iteration -/

/-- Let Step 1 hold at iteration $k$. Let $\overline{L} > 0$ with $\|\overline{\nabla}^i f(x_k)\|
\le \overline{L}$ for $i \in [1, p]$ (for ARqpIDA this is (13.1.63)), let $\sigma_k \ge 0$, and
let $\delta^{(0)}_{k,j} \le 1$ for $j \in [1, q]$. Then for every $j \in [1, q]$ (13.1.66)
$$\delta^{(0)}_{k,j} \ge \delta^{(1)}_{k,j} \ge
  \min\Big\{\frac{\varsigma\varepsilon_j}{16\max\{\overline{L}, \sigma_k\}},
  \delta^{(0)}_{k,j}\Big\}.$$
This is Lemma 13.1.11 of [cartis2022evaluation].

The inexact derivative $\overline{\nabla}^i f(x_k)$ is the term `D k i` of the derivative data.
That the halving loop stops is `Optimization.exists_arqpDA_halving`. -/
theorem ARqpStep1.radius_bounds (hs : ARqpStep1 X P ε x σ δ δ₁ D dd k) {Lb : ℝ}
    (hLb : 0 < Lb) (hD : ∀ i ∈ Finset.Icc 1 P.p, ‖D k i‖ ≤ Lb) (hσ : 0 ≤ σ k)
    (hδ1 : ∀ j ∈ Finset.Icc 1 P.q, δ k j ≤ 1) {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    δ₁ k j ≤ δ k j ∧ min (P.ς * ε j / (16 * max Lb (σ k))) (δ k j) ≤ δ₁ k j := by
  refine ⟨hs.radius_le j hj, ?_⟩
  rcases (hs.radius_le j hj).lt_or_eq with hlt | heq
  swap
  · rw [heq]; exact min_le_right _ _
  obtain ⟨h2δ, ⟨d', hd'n, -, hd'T, hd'm⟩, -⟩ := hs.halving j hj hlt
  refine (min_le_left _ _).trans ?_
  by_contra hcon
  push Not at hcon
  have hM : 0 < max Lb (σ k) := lt_max_of_lt_left hLb
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have hpos := hs.radius_pos j hj
  have hε : 0 < ε j := by
    by_contra hε
    push Not at hε
    have : P.ς * ε j / (16 * max Lb (σ k)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos P.ς_pos.le hε) (by positivity)
    linarith
  have key := regularizedModel_decrease_ge_of_taylorDecrement_ge (D := D k) (p := P.p)
    (σ := σ k) (L := Lb) hjp hσ
    (fun ℓ hℓ => hD ℓ (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hℓ).1; omega,
      (Finset.mem_Icc.1 hℓ).2⟩))
    (α := P.ς * ε j / 2) (δ := 2 * δ₁ k j) (by positivity) (h2δ.trans (hδ1 j hj)) ?_ hd'n
    (by
      have : P.ς * ε j / 2 * (2 * δ₁ k j) ^ j / j ! = P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 2 := by
        ring
      linarith)
  · have : P.ς * ε j / 2 / 2 * (2 * δ₁ k j) ^ j / j ! =
        P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 4 := by ring
    rw [this] at key
    exact absurd key (not_le.2 hd'm)
  · rw [lt_div_iff₀ (by positivity)] at hcon
    nlinarith

/-- The constant $\kappa^{(1)}_\delta(\sigma) = \varsigma\theta/(24\max\{\overline{L}, \sigma\})$ of
(13.1.72) of [cartis2022evaluation]. -/
noncomputable def arKappaDelta1 (P : ARqpIDAParams) (Lb σ : ℝ) : ℝ :=
  P.ς * P.θ / (24 * max Lb σ)

/-- If $\overline{L} > 0$, then $\kappa^{(1)}_\delta(\sigma) > 0$. -/
theorem arKappaDelta1_pos {P : ARqpIDAParams} {Lb σ : ℝ} (hLb : 0 < Lb) :
    0 < arKappaDelta1 P Lb σ := by
  have := P.ς_pos; have := P.θ_pos
  exact div_pos (by positivity) (by have : 0 < max Lb σ := lt_max_of_lt_left hLb; positivity)

/-- If $\overline{L} \ge 1$, then $\kappa^{(1)}_\delta(\sigma) \le 1$. -/
theorem arKappaDelta1_le_one {P : ARqpIDAParams} {Lb σ : ℝ} (hLb : 1 ≤ Lb) :
    arKappaDelta1 P Lb σ ≤ 1 := by
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  have hM : 1 ≤ max Lb σ := hLb.trans (le_max_left _ _)
  rw [arKappaDelta1, div_le_one (by positivity)]
  nlinarith

omit [InnerProductSpace ℝ E] in
/-- Either mode of the radii control gives a lower bound on the radii of Step 2. Let
`Optimization.ARqpDARadiiControl u` hold at iteration $k$, let $k$ be a trial iteration with
$\|s_k\| < 1$, let $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$, let $\overline{L} \ge 1$, and
let $\sigma_k \le \bar\sigma$. Then $\kappa^{(1)}_\delta(\bar\sigma)\varepsilon_j \le
\delta_{s_k,j}$ for every $j \in [1, q]$. -/
theorem ARqpDARadiiControl.kappa_mul_le {u : Prop} {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ}
    {σ : ℕ → ℝ} {δs : ℕ → ℕ → ℝ} {s : ℕ → E} {acc : ℕ → Prop} {k : ℕ}
    (hrc : ARqpDARadiiControl u P ε Lb σ δs s acc k) (hk : ¬ acc k) (hs : ‖s k‖ < 1)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hLb : 1 ≤ Lb) {σbar : ℝ}
    (hσ : σ k ≤ σbar) {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    arKappaDelta1 P Lb σbar * ε j ≤ δs k j := by
  obtain ⟨h1, h2⟩ := hrc hk hs
  have hεj := hε j hj
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  have hM : 1 ≤ max Lb σbar := hLb.trans (le_max_left _ _)
  have hM' : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
  by_cases hu : u
  · rw [h1 hu j hj, arKappaDelta1, div_mul_eq_mul_div, div_le_one (by positivity)]
    have : P.ς * P.θ * ε j ≤ 1 :=
      (mul_le_of_le_one_left hεj.1.le
        ((mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le)).trans hεj.2
    nlinarith
  · refine le_trans ?_ (h2 hu j hj)
    rw [arKappaDelta1, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by have := hεj.1; positivity) (by positivity)
      (by have := max_le_max (le_refl Lb) hσ; linarith)

/-- Let the step predicate `Optimization.ARqpDAStep` hold at every iteration $i < k$ and Step 1 at
iteration $k$, with the initial weight, radii and accuracies of $P$. Let
$\varepsilon_j \in (0, 1]$ and $\varepsilon_j \le \delta_{0,j}$ for $j \in [1, q]$, let
$\overline{L} \ge 1$ with $\|\overline{\nabla}^\ell f(x_i)\| \le \overline{L}$ for $i \le k$ and
$\ell \in [1, p]$, let $\sigma_i \le \bar\sigma$ for $i \le k$, and let the radii control
`Optimization.ARqpDARadiiControl u`, in either mode, hold at every iteration $i < k$. Then
$$\delta^{(0)}_{k,j} \ge \delta^{(1)}_{k,j} \ge \kappa^{(1)}_\delta(\bar\sigma)\varepsilon_j,
  \qquad j \in [1, q].$$
This is the radius bound (13.1.71) of Lemma 13.1.12 of [cartis2022evaluation]. -/
theorem arqpDA_radius_ge (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hstep1 : ARqpStep1 X P ε x σ δ δ₁ D dd k) (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀)
    (hh0 : h 0 = P.h₀)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j)
    {Lb σbar : ℝ} (hLb : 1 ≤ Lb) (hD : ∀ i ≤ k, ∀ ℓ ∈ Finset.Icc 1 P.p, ‖D i ℓ‖ ≤ Lb)
    (hσ : ∀ i ≤ k, σ i ≤ σbar) {u : Prop}
    (hrc : ∀ i < k, ARqpDARadiiControl u P ε Lb σ δs s acc i) :
    ∀ j ∈ Finset.Icc 1 P.q, arKappaDelta1 P Lb σbar * ε j ≤ δ₁ k j ∧ δ₁ k j ≤ δ k j := by
  have hLb0 : 0 < Lb := zero_lt_one.trans_le hLb
  set κ := arKappaDelta1 P Lb σbar with hκdef
  have hκ0 : 0 < κ := arKappaDelta1_pos hLb0
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hς := P.ς_pos
  have hθ := P.θ_pos
  have hθ1 := P.θ_lt_one.le
  have hσpos : ∀ i ≤ k, 0 < σ i := fun i hi =>
    arqpDA_sigma_pos (fun j hj => hstep j (by omega)) hσ0 hδ0 hh0
  have hMle : ∀ i ≤ k, max Lb (σ i) ≤ max Lb σbar := fun i hi => max_le_max le_rfl (hσ i hi)
  -- (a) the halving lower bound dominates `κ ε`
  have ha : ∀ i ≤ k, ∀ j ∈ Finset.Icc 1 P.q,
      κ * ε j ≤ P.ς * ε j / (16 * max Lb (σ i)) := by
    intro i hi j hj
    have hεj := (hε j hj).1
    have hM : 0 < max Lb (σ i) := lt_max_of_lt_left hLb0
    rw [le_div_iff₀ (by positivity), hκdef, arKappaDelta1, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_iff₀ (by have : 0 < max Lb σbar := lt_max_of_lt_left hLb0; positivity)]
    have := hMle i hi
    have h1 : P.ς * P.θ * ε j * (16 * max Lb (σ i)) ≤ P.ς * 1 * ε j * (16 * max Lb σbar) := by
      gcongr
    have : 0 ≤ P.ς * ε j * max Lb σbar := by
      have : 0 < max Lb σbar := lt_max_of_lt_left hLb0
      positivity
    linarith
  -- the radii at the start of Step 1
  have hδk : ∀ i ≤ k, ∀ j ∈ Finset.Icc 1 P.q, κ * ε j ≤ δ i j := by
    intro i
    induction i with
    | zero =>
      intro _ j hj
      rw [hδ0]
      exact (mul_le_of_le_one_left (hε j hj).1.le hκ1).trans (hεδ j hj)
    | succ i ih =>
      intro hi j hj
      have hik : i ≤ k := by omega
      have hsi := hstep i (by omega)
      have hδ1i : ∀ j ∈ Finset.Icc 1 P.q, δ i j ≤ 1 := fun j hj =>
        ((arqpDA_invariants (fun l hl => hstep l (by omega)) hσ0 hδ0 hh0).2.1 j hj).2
      have h11 :=
          (ARqpStep1.radius_bounds hsi.toARqpStep1 hLb0 (hD i hik) (hσpos i hik).le hδ1i hj).2
      have hδ₁ : κ * ε j ≤ δ₁ i j := (le_min (ha i hik j hj) (ih hik j hj)).trans h11
      by_cases hacc : acc i
      · rw [hsi.δ_acc hacc]; exact ih hik j hj
      rw [hsi.radii_trial hacc]
      split_ifs with hc
      · exact (hrc i (by omega)).kappa_mul_le hacc hc.2 hε hLb (hσ i hik) hj
      · exact hδ₁
  intro j hj
  have hδ1k : ∀ j ∈ Finset.Icc 1 P.q, δ k j ≤ 1 := fun j hj =>
    ((arqpDA_invariants (fun l hl => hstep l (by omega)) hσ0 hδ0 hh0).2.1 j hj).2
  have h11 := ARqpStep1.radius_bounds hstep1 hLb0 (hD k le_rfl) (hσpos k le_rfl).le hδ1k hj
  exact ⟨(le_min (ha k le_rfl j hj) (hδk k le_rfl j hj)).trans h11.2, h11.1⟩

/-- Let iteration $k$ of ARqpIDA or ARqpEDA be a trial iteration, let $\varepsilon_j > 0$ for
$j \in [1, q]$, and let $\sigma_k \ge 0$. Then (13.1.76)
$$\overline{\Delta T}_{f,p}(x_k, s_k) \ge \frac{\sigma_k}{(p+1)!} \|s_k\|^{p+1},$$
and $\overline{\Delta T}_{f,p}(x_k, s_k) > 0$, so that the ratio (13.1.58) is well defined. This
is Lemma 13.1.13 of [cartis2022evaluation]. -/
theorem ARqpDAStep.taylorDecrement_ge (hs : ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ k)
    (hk : ¬ acc k)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, 0 < ε j) (hσ : 0 ≤ σ k) :
    σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) ≤ (D k).taylorDecrement P.p (s k) ∧
      0 < (D k).taylorDecrement P.p (s k) := by
  have h2 := hs.step2_of_not_acc hk
  have hpos : 0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 := by
    have := P.ς_pos; have := hε _ h2.jk_mem; have := hs.radius_pos _ h2.jk_mem; positivity
  have hm := hpos.trans_le (h2.model_dec.trans h2.dec_le)
  rw [arModelDec_eq] at hm
  have : 0 ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) := by positivity
  constructor <;> linarith

/-- Let Step 2 hold at iteration $k$ with $\delta^{(1)}_{k,j} > 0$ for $j \in [1, q]$. Let
$\overline{L} \ge 1$ with $\|\overline{\nabla}^i f(x_k)\| \le \overline{L}$ for $i \in [1, p]$,
let $\sigma_k \ge 0$, let $\bar\sigma$ be any real number, let $\varepsilon_j \in (0, 1]$ for
$j \in [1, q]$, and let $0 \le \kappa \le 1$ with $\delta^{(1)}_{k,j} \ge \kappa\varepsilon_j$
for $j \in [1, q]$. If
$$h_{k,i} \le \kappa_s \Big(\frac{\varsigma\kappa^q}{12\,q!\,\max\{\overline{L},
  \bar\sigma\}}\Big)^p \varepsilon_{\min}^{p(q+1)}, \qquad i \in [1, p],$$
with $\varepsilon_{\min} = \min_{j \in [1, q]} \varepsilon_j$, then iteration $k$ is not
accuracy-improving. This is the accuracy bound (13.1.73) of Lemma 13.1.12 of
[cartis2022evaluation]. -/
theorem ARqpStep2.not_acc_of_le (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hpos : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ₁ k j) {Lb σbar κ : ℝ} (hLb : 1 ≤ Lb)
    (hD : ∀ i ∈ Finset.Icc 1 P.p, ‖D k i‖ ≤ Lb) (hσ : 0 ≤ σ k)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hδ₁ : ∀ j ∈ Finset.Icc 1 P.q, κ * ε j ≤ δ₁ k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤
      P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σbar)) ^ P.p *
        epsMin P.q ε ^ (P.p * (P.q + 1))) :
    ¬ acc k := by
  have hq := P.one_le_q
  have hεmin : 0 < epsMin P.q ε := epsMin_pos hq fun j hj => (hε j hj).1
  have hεmin1 : epsMin P.q ε ≤ 1 := epsMin_le_one hq fun j hj => (hε j hj).2
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  set j := jk k
  set em := epsMin P.q ε
  set M := max Lb σbar
  have hM : 1 ≤ M := hLb.trans (le_max_left _ _)
  set c := P.ς * κ ^ P.q / (12 * P.q ! * M) * em ^ (P.q + 1) with hc
  have hfq : (1 : ℝ) ≤ P.q ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_mul_eq_mul_div, div_le_one (by positivity)]
    calc P.ς * κ ^ P.q * em ^ (P.q + 1) ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul hς1 (pow_le_one₀ hκ0 hκ1) (by positivity) zero_le_one)
            (pow_le_one₀ hεmin.le hεmin1) (by positivity) (by norm_num)
      _ ≤ 12 * P.q ! * M := by nlinarith
  rw [h2.acc_iff]
  rintro ⟨hs1, i, hi, hlt⟩
  refine absurd hlt (not_lt.2 ?_)
  -- the step is not too short
  have hsc : c ≤ ‖s k‖ := by
    have hup := taylorDecrement_le_two_mul (D := D k) (j := P.p) (zero_le_one.trans hLb) hD hs1.le
    have hm := h2.model_dec.trans h2.dec_le
    rw [arModelDec_eq] at hm
    have hσs : 0 ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) := by positivity
    have hlow : P.ς * ε j * δ₁ k j ^ j / j ! / 4 ≤ 2 * Lb * ‖s k‖ := by linarith
    have hm0 : 0 ≤ κ * em := by positivity
    have hm1 : κ * em ≤ 1 := (mul_le_of_le_one_left hεmin.le hκ1).trans hεmin1
    have hδj : (κ * em) ^ P.q ≤ δ₁ k j ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0
        ((mul_le_mul_of_nonneg_left (epsMin_le h2.jk_mem) hκ0).trans (hδ₁ j h2.jk_mem)) j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : em ≤ ε j := epsMin_le h2.jk_mem
    have hLbM : 2 * Lb ≤ 3 * M := by have := le_max_left Lb σbar; linarith
    have hnum : P.ς * em * (κ * em) ^ P.q ≤ P.ς * ε j * δ₁ k j ^ j :=
      mul_le_mul (mul_le_mul_of_nonneg_left hεj hς.le) hδj (by positivity)
        (mul_nonneg hς.le (hεmin.le.trans hεj))
    have hN : 0 ≤ P.ς * ε j * δ₁ k j ^ j :=
      mul_nonneg (mul_nonneg hς.le (hεmin.le.trans hεj)) (pow_nonneg (hpos j h2.jk_mem).le _)
    calc c = P.ς * em * (κ * em) ^ P.q / (12 * P.q ! * M) := by rw [hc]; ring
      _ ≤ P.ς * ε j * δ₁ k j ^ j / (12 * P.q ! * M) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ P.ς * ε j * δ₁ k j ^ j / (12 * j ! * M) :=
          div_le_div_of_nonneg_left hN (by positivity) (by gcongr)
      _ = P.ς * ε j * δ₁ k j ^ j / j ! / 4 / (3 * M) := by field_simp; ring
      _ ≤ 2 * Lb * ‖s k‖ / (3 * M) := div_le_div_of_nonneg_right hlow (by positivity)
      _ ≤ 3 * M * ‖s k‖ / (3 * M) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLbM (norm_nonneg _))
            (by positivity)
      _ = ‖s k‖ := by field_simp
  obtain ⟨hi1, hip⟩ := Finset.mem_Icc.1 hi
  have hcp : c ^ P.p ≤ ‖s k‖ ^ (P.p - i + 1) :=
    (pow_le_pow_of_le_one hc0 hc1 (by omega)).trans (pow_le_pow_left₀ hc0 hsc _)
  calc h k i ≤ P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * M)) ^ P.p * em ^ (P.p * (P.q + 1)) :=
        hh i hi
    _ = P.κs * c ^ P.p := by rw [hc, mul_pow, ← pow_mul, mul_assoc, mul_comm (P.q + 1) P.p]
    _ ≤ P.κs * ‖s k‖ ^ (P.p - i + 1) := mul_le_mul_of_nonneg_left hcp P.κs_pos.le

end ARStep

/-! ### Step-length algebra for ARqpIDA and ARqpEDA -/

section StepLength

/-- The constant $\hat\kappa = \min\{\kappa, a/(2\,q!\,A)\}$, which replaces $\kappa_{\delta,\min}$
in the step-length bounds for $q > 2$ (Lemmas 13.1.17 and 13.1.18 of [cartis2022evaluation]). -/
noncomputable def arKappaHat (q : ℕ) (a A κ : ℝ) : ℝ := min κ (a / (2 * q ! * A))

/-- Let $a > 0$, $A > 0$, $\varepsilon > 0$, $t \in (0, 1)$, $\delta > 0$, $j \in [1, q]$ and
$q \le p$, let $\kappa > 0$ with $\kappa\varepsilon \le \delta$, and let $u$ be a proposition
such that $\delta = 1$ if $u$ holds. If the radius inequality (13.1.79)
$$\frac{a\varepsilon\delta^j}{j!} \le A \sum_{\ell=1}^{j} \frac{\delta^\ell}{\ell!}
  t^{p-\ell+1}$$
holds, then $\frac{a}{2\,j!\,A}\varepsilon \le t^{p-j+1}$ if $u$ holds, and
$\frac{a}{2\,j!\,A}\hat\kappa^{j-1}\varepsilon^j \le t^p$ with
$\hat\kappa = \min\{\kappa, a/(2\,q!\,A)\}$ if $u$ fails. This is the step-length bound of Lemma
13.1.17 of [cartis2022evaluation], obtained as in Lemma 12.2.12.

The proposition $u$ is the mode of the radii control: unit radii if $u$ holds, and radii bounded
below by $\kappa\varepsilon$ otherwise. The constant $\hat\kappa$ is
`Optimization.arKappaHat q a A κ`. -/
theorem arqp_pow_ge_of_radius_ineq {a A t ε δ κ : ℝ} {j p q : ℕ} {u : Prop} (ha : 0 < a)
    (hA : 0 < A) (hε : 0 < ε) (ht : 0 < t) (ht1 : t < 1) (hδ : 0 < δ) (hj : j ∈ Finset.Icc 1 q)
    (hqp : q ≤ p) (hκ : 0 < κ) (hκε : κ * ε ≤ δ) (hu : u → δ = 1)
    (hineq : a * ε * δ ^ j / j ! ≤ A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1)) :
    (u → a / (2 * j ! * A) * ε ≤ t ^ (p - j + 1)) ∧
      (¬ u → a / (2 * j ! * A) * arKappaHat q a A κ ^ (j - 1) * ε ^ j ≤ t ^ p) := by
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hjp : j ≤ p := hjq.trans hqp
  have hM : MeasureIneq A 0 a ε δ t j p := by
    rw [measureIneq_iff, zero_mul, add_zero]; exact hineq
  have hfj : (0 : ℝ) < j ! := by positivity
  refine ⟨fun hq => ?_, fun _ => ?_⟩
  · have h1 := hM.div_le_of_le hA.le le_rfl ht (by rw [hu hq]; exact ht1.le) hjp
    rw [add_zero] at h1
    calc a / (2 * j ! * A) * ε = a * ε / j ! / (2 * A) := by field_simp
      _ ≤ t ^ (p - j + 1) := by rw [div_le_iff₀ (by positivity)]; linarith
  · have h1 := pow_ge_of_measure_ineq hM hA ha hε ht ht1.le hδ hj1 hjp hκ hκε
    refine le_trans ?_ h1
    have hfq : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq
    have hk1 : arKappaHat q a A κ ≤ min κ (a / (A * j !) / 2) := by
      refine min_le_min le_rfl ?_
      rw [div_div, mul_comm (A * j !) 2, ← mul_assoc, mul_right_comm 2 A]
      exact div_le_div_of_nonneg_left ha.le (by positivity) (by gcongr)
    have hk0 : 0 ≤ arKappaHat q a A κ := le_min hκ.le (by positivity)
    have : a / (2 * j ! * A) = a / (A * j !) / 2 := by field_simp
    rw [this]
    gcongr

/-- The exponent $\pi_j$ of Lemma 13.1.18 of [cartis2022evaluation] in the mode $u$ of the radii
control:
$$\pi_j = \begin{cases} \dfrac{p+1}{p-j+1} & \text{if } u \text{ holds (unit radii)}, \\
  \dfrac{j(p+1)}{p} & \text{otherwise (radii bounded below)}. \end{cases}$$

The difference $p - j$ is taken in $\mathbb{N}$, so $p - j + 1 = 1$ for $j > p$. For $p = 0$ the
second case is $0$, by the Lean convention for division by zero. -/
noncomputable def arPiOf (u : Prop) [Decidable u] (p j : ℕ) : ℝ :=
  if u then ((p : ℝ) + 1) / ((p - j + 1 : ℕ) : ℝ) else (j : ℝ) * ((p : ℝ) + 1) / p

/-- The exponent $\pi_j$ of Lemma 13.1.18 of [cartis2022evaluation] in the mode fixed by the order:
$\pi_j = (p+1)/(p-j+1)$ if $q \le 2$ and $\pi_j = j(p+1)/p$ if $q > 2$. -/
noncomputable def arPi (q p j : ℕ) : ℝ := arPiOf (q ≤ 2) p j

/-- The step-length constant of Lemma 13.1.18 of [cartis2022evaluation] in the mode $u$ of the radii
control:
$$\begin{cases} \Big(\dfrac{a}{2\,q!\,A}\Big)^{(p+1)/(p-q+1)} & \text{if } u \text{ holds (unit
  radii)}, \\ \Big(\dfrac{a\hat\kappa^{q-1}}{2\,q!\,A}\Big)^{q(p+1)/p} & \text{otherwise (radii
  bounded below)}, \end{cases}$$
with $\hat\kappa = \min\{\kappa, a/(2\,q!\,A)\}$ (`Optimization.arKappaHat`).

The powers are real powers. The exponents follow the same conventions as `Optimization.arPiOf`. -/
noncomputable def arStepConstOf (u : Prop) [Decidable u] (q p : ℕ) (a A κ : ℝ) : ℝ :=
  if u then (a / (2 * q ! * A)) ^ (((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ))
  else (a * arKappaHat q a A κ ^ (q - 1) / (2 * q ! * A)) ^ ((q : ℝ) * ((p : ℝ) + 1) / p)

/-- The step-length constant of Lemma 13.1.18 of [cartis2022evaluation] in the mode fixed by the
order: $(a/(2\,q!\,A))^{(p+1)/(p-q+1)}$ if $q \le 2$, and
$(a\hat\kappa^{q-1}/(2\,q!\,A))^{q(p+1)/p}$ with $\hat\kappa = \min\{\kappa, a/(2\,q!\,A)\}$ if
$q > 2$. -/
noncomputable def arStepConst (q p : ℕ) (a A κ : ℝ) : ℝ := arStepConstOf (q ≤ 2) q p a A κ

/-- If $a, A, \kappa \ge 0$, the step-length constant `Optimization.arStepConstOf u q p a A κ` is
nonnegative. -/
theorem arStepConstOf_nonneg {u : Prop} [Decidable u] {q p : ℕ} {a A κ : ℝ} (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hκ : 0 ≤ κ) : 0 ≤ arStepConstOf u q p a A κ := by
  unfold arStepConstOf
  have : 0 ≤ arKappaHat q a A κ := le_min hκ (by positivity)
  split_ifs <;> positivity

/-- If $a, A, \kappa > 0$, the step-length constant `Optimization.arStepConstOf u q p a A κ` is
positive. -/
theorem arStepConstOf_pos {u : Prop} [Decidable u] {q p : ℕ} {a A κ : ℝ} (ha : 0 < a)
    (hA : 0 < A) (hκ : 0 < κ) : 0 < arStepConstOf u q p a A κ := by
  unfold arStepConstOf
  have : 0 < arKappaHat q a A κ := lt_min hκ (by positivity)
  split_ifs <;> positivity

/-- The exponent `Optimization.arPiOf u p j` is nonnegative. -/
theorem arPiOf_nonneg {u : Prop} [Decidable u] {p j : ℕ} : 0 ≤ arPiOf u p j := by
  unfold arPiOf; split_ifs <;> positivity

/-- If $a, A, \kappa \ge 0$, the step-length constant `Optimization.arStepConst q p a A κ` is
nonnegative. -/
theorem arStepConst_nonneg {q p : ℕ} {a A κ : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hκ : 0 ≤ κ) :
    0 ≤ arStepConst q p a A κ :=
  arStepConstOf_nonneg ha hA hκ

/-- If $a, A, \kappa > 0$, the step-length constant `Optimization.arStepConst q p a A κ` is
positive. -/
theorem arStepConst_pos {q p : ℕ} {a A κ : ℝ} (ha : 0 < a) (hA : 0 < A) (hκ : 0 < κ) :
    0 < arStepConst q p a A κ :=
  arStepConstOf_pos ha hA hκ

/-- The exponent `Optimization.arPi q p j` is nonnegative. -/
theorem arPi_nonneg {q p j : ℕ} : 0 ≤ arPi q p j := arPiOf_nonneg

/-- Let $0 < a \le 1$, $A \ge 1$, $\varepsilon \in (0, 1]$, $t > 0$, $0 < \kappa \le 1$,
$j \in [1, q]$ and $q \le p$, and let $u$ be a decidable proposition. Suppose that $t \ge 1$, or
that the conclusions of `Optimization.arqp_pow_ge_of_radius_ineq` hold:
$\frac{a}{2\,j!\,A}\varepsilon \le t^{p-j+1}$ if $u$ holds, and
$\frac{a}{2\,j!\,A}\hat\kappa^{j-1}\varepsilon^j \le t^p$ if $u$ fails, with
$\hat\kappa = \min\{\kappa, a/(2\,q!\,A)\}$. Then
$$c\,\varepsilon^{\pi_j} \le t^{p+1},$$
where $c$ is the step-length constant `Optimization.arStepConstOf u q p a A κ` and $\pi_j$ is
the exponent `Optimization.arPiOf u p j`. This step turns step lengths into decrements in the
proof of Lemma 13.1.18 of [cartis2022evaluation]. -/
theorem arqp_pow_succ_ge {a A t ε κ : ℝ} {j p q : ℕ} {u : Prop} [Decidable u] (ha : 0 < a)
    (ha1 : a ≤ 1) (hA : 1 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hj : j ∈ Finset.Icc 1 q) (hqp : q ≤ p)
    (hb : 1 ≤ t ∨ ((u → a / (2 * j ! * A) * ε ≤ t ^ (p - j + 1)) ∧
      (¬ u → a / (2 * j ! * A) * arKappaHat q a A κ ^ (j - 1) * ε ^ j ≤ t ^ p))) :
    arStepConstOf u q p a A κ * ε ^ arPiOf u p j ≤ t ^ (p + 1) := by
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hfj : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfq : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq
  set κh := arKappaHat q a A κ
  have hκh0 : 0 < κh := lt_min hκ (by positivity)
  have hκh1 : κh ≤ 1 := (min_le_left _ _).trans hκ1
  have hbq0 : 0 < a / (2 * q ! * A) := by positivity
  have hbqj : a / (2 * q ! * A) ≤ a / (2 * j ! * A) :=
    div_le_div_of_nonneg_left ha.le (by positivity) (by gcongr)
  have hbj1 : a / (2 * j ! * A) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hbq1 : a / (2 * q ! * A) ≤ 1 := hbqj.trans hbj1
  have hπ := arPiOf_nonneg (u := u) (p := p) (j := j)
  have hC0 := arStepConstOf_nonneg (u := u) (q := q) (p := p) ha.le hA0.le hκ.le
  have hepi : ε ^ arPiOf u p j ≤ 1 := Real.rpow_le_one hε.le hε1 hπ
  have hC1 : arStepConstOf u q p a A κ ≤ 1 := by
    unfold arStepConstOf
    split_ifs
    · exact Real.rpow_le_one hbq0.le hbq1 (by positivity)
    · refine Real.rpow_le_one (by positivity) ?_ (by positivity)
      rw [mul_div_right_comm]
      exact (mul_le_of_le_one_left (by positivity) hbq1).trans (pow_le_one₀ hκh0.le hκh1)
  rcases hb with ht1 | ⟨hq2, hq3⟩
  · exact ((mul_le_of_le_one_left (by positivity) hC1).trans hepi).trans (one_le_pow₀ ht1)
  by_cases hq : u
  · have hX := hq2 hq
    simp only [arStepConstOf, arPiOf, hq, ↓reduceIte]
    set m := p - j + 1 with hm
    have hm0 : m ≠ 0 := by omega
    set π := ((p : ℝ) + 1) / (m : ℝ)
    have hππ : π ≤ ((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ) := by
      refine div_le_div_of_nonneg_left (by positivity) (by
        have : 0 < p - q + 1 := by omega
        exact_mod_cast this) ?_
      exact_mod_cast (show p - q + 1 ≤ m by omega)
    have hπ0 : 0 ≤ π := by positivity
    calc (a / (2 * q ! * A)) ^ (((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ)) * ε ^ π
        ≤ (a / (2 * q ! * A)) ^ π * ε ^ π :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hbq0 hbq1 hππ)
            (by positivity)
      _ ≤ (a / (2 * j ! * A)) ^ π * ε ^ π := by
          gcongr
      _ = (a / (2 * j ! * A) * ε) ^ π := (Real.mul_rpow (by positivity) hε.le).symm
      _ ≤ (t ^ m) ^ π := Real.rpow_le_rpow (by positivity) hX hπ0
      _ = t ^ ((p : ℝ) + 1) := pow_rpow_div hm0 ht.le _
      _ = t ^ (p + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf
  · have hX := hq3 hq
    simp only [arStepConstOf, arPiOf, hq, ↓reduceIte]
    have hp0 : p ≠ 0 := by omega
    have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp0
    set B := a / (2 * j ! * A) * κh ^ (j - 1)
    set Bq := a * κh ^ (q - 1) / (2 * q ! * A)
    have hBq0 : 0 < Bq := by positivity
    have hBqB : Bq ≤ B := by
      rw [show Bq = a / (2 * q ! * A) * κh ^ (q - 1) by ring]
      exact mul_le_mul hbqj (pow_le_pow_of_le_one hκh0.le hκh1 (by omega)) (by positivity)
        (by positivity)
    have hBq1 : Bq ≤ 1 := by
      rw [show Bq = a / (2 * q ! * A) * κh ^ (q - 1) by ring]
      exact (mul_le_of_le_one_left (by positivity) hbq1).trans (pow_le_one₀ hκh0.le hκh1)
    have he : ((p : ℝ) + 1) / p ≤ (q : ℝ) * ((p : ℝ) + 1) / p := by
      rw [mul_div_assoc]
      exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast (by omega : 1 ≤ q))
    have hεpow : (ε ^ j) ^ (((p : ℝ) + 1) / p) = ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, mul_div_assoc]
    calc Bq ^ ((q : ℝ) * ((p : ℝ) + 1) / p) * ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p)
        ≤ Bq ^ (((p : ℝ) + 1) / p) * ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hBq0 hBq1 he)
            (by positivity)
      _ ≤ B ^ (((p : ℝ) + 1) / p) * (ε ^ j) ^ (((p : ℝ) + 1) / p) := by
          rw [hεpow]; gcongr
      _ = (B * ε ^ j) ^ (((p : ℝ) + 1) / p) :=
          (Real.mul_rpow (by positivity) (by positivity)).symm
      _ ≤ (t ^ p) ^ (((p : ℝ) + 1) / p) := Real.rpow_le_rpow (by positivity) hX (by positivity)
      _ = t ^ ((p : ℝ) + 1) := pow_rpow_div hp0 ht.le _
      _ = t ^ (p + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf

end StepLength

end Optimization
