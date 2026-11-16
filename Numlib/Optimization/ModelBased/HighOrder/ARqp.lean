/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.ARRun
import Numlib.Optimization.ModelBased.HighOrderModel

/-!
# The high-order adaptive-regularization method ARqp

The method ARqp of [cartis2022evaluation] (Algorithm 12.2.2) looks for
$(\varepsilon, \delta)$-approximate $q$-th order minimizers of an objective by approximately
minimizing the regularized model of order $p \ge q$. It is an adaptive-regularization method
(`Optimization.IsARRun`) whose Step-1 test and Step-2 conditions use decrement measures. For a
decrement $\Delta$, a radius $\delta$ and a set $S$ of displacements, the decrement measure is
$\phi = \sup \{\Delta(d) \mid \|d\| \le \delta, \ d \in S\}$, and a $\varsigma$-**approximate
optimality displacement** is a $d$ with $\|d\| \le \delta$, $d \in S$ and
$\Delta(d) \ge \varsigma \phi$. At the iterate $x_k$ the decrement of order $j$ is
$\Delta T_j(x_k, d) = T_j(x_k, 0) - T_j(x_k, d)$. Step 1 stops when, for $j = 1, \ldots, q$, the
decrease along an approximate optimality displacement $d_{k,j}$ of radius $\delta_{k,j}$ satisfies
$$\Delta T_j(x_k, d_{k,j}) \le \varsigma \varepsilon_j \frac{\delta_{k,j}^j}{j!},$$
as in the test (12.2.2) of TRq.

The run predicate `Optimization.IsARqpRun` is generic in two ingredients. The first is the model
data of each iteration, bundled in `Optimization.ARqpData`: the Step-1 decrements of the objective's
model at $x_k$, the regularized model $m_k$, its decrements at a trial step, and the predicted
decrease of the ratio. Exact ARqp uses `Optimization.ARqpData.ofTaylor` with the Taylor series of
$f$ at $x_k$, inexact derivatives (Chapter 13) use it with other derivative data, and the composite
method ARqpC (Algorithm 14.1.1) uses `Optimization.ARqpData.ofComposite` with the objective
$w = f + h \circ c$. The second is the feasible set $X$ of §14.2. Step-1 measures are taken over
$\{e \mid x_k + e \in X\}$, steps satisfy $x_k + s_k \in X$, and model measures are taken over
$\{e \mid x_k + s_k + e \in X\}$. Unconstrained ARqp is the case $X = E$.

## Main definitions

* `Optimization.ARqpParams`: the AR constants and the factors $\theta \in (0, 1)$ and
  $\varsigma \in (0, 1]$.
* `Optimization.ARqpData`, `Optimization.ARqpData.ofTaylor`, `Optimization.ARqpData.ofComposite`:
  the model data of one iteration.
* `Optimization.ARqpStep`: the Step-2 conditions (12.2.27)–(12.2.29).
* `Optimization.IsARqpRun`: a run of ARqp.

## Main results

* `Optimization.IsARqpRun.mem`: the iterates stay feasible.
* `Optimization.IsARqpRun.model_lt`: the model decreases strictly before termination.
* `Optimization.IsARqpRun.delta_mem`: the radii stay in $(0, 1]$.
* `Optimization.IsARqpRun.of_univ`: an unconstrained run whose points stay in $X$ is a run on $X$.
* `Optimization.exists_arqpStep_ofTaylor`: Lemma 12.2.9, existence of a step with explicit radii.
* `Optimization.exists_isARqpRun`: in finite dimension runs of exact ARqp exist, with the radii of
  Lemma 12.2.9.

## Implementation notes

* The Step-1 test is `Optimization.MeasureTestPasses`, and approximate optimality displacements are
  `Optimization.IsApproxMeasureStep`. The decrement measure is `Optimization.decrementMeasure`.
* Step 2 asks the model decrease (12.2.27) and then either the long-step branch $\|s_k\| \ge 1$,
  with radii arbitrary in $(0, 1]$, or the approximate model optimality (12.2.29) with witnesses
  $d^m_{k,j}$. The long-step branch covers (12.2.28) and Algorithm 12.2.3.
* Termination in Step 2 ($m_k(s_k) = m_k(0)$) is allowed only if $0$ then minimizes the model
  globally over the feasible steps, as Algorithm 12.2.3 guarantees (12.2.34). Without this
  condition, termination in Step 2 would certify nothing (Lemma 12.2.10).
* Step 1 is skipped after an unsuccessful iteration: the run keeps $x_k$, the radii $\delta_k$ and
  the Step-1 witnesses. For Taylor data (`Optimization.ARqpData.ofTaylor`), whose decrements do not
  depend on $\sigma$, the outcome of the test is then unchanged. For model data that change with the
  iteration in other ways, such as re-evaluated inexact derivatives, the Step-1 test is evaluated
  again with the kept witnesses, which must still be approximate optimality displacements.
* Long steps ($\|s_k\| \ge 1$) only constrain the radii to $(0, 1]$. Lower bounds on the radii such
  as (12.2.45) and (12.2.50) are not part of the run; they are stated separately, as in
  `Optimization.exists_isARqpRun`.
* `Optimization.ARqpParams` asks $\theta \in (0, 1)$. The complexity analysis with $\varsigma < 1$
  needs $\theta < \varsigma$, which is assumed where it is used.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

/-- The constants of ARqp and ARqpC, Step 0 of Algorithms 12.2.2 and 14.1.1 of
[cartis2022evaluation]. They consist of the AR constants (`Optimization.ARParams`), the
model-optimality factor $\theta \in (0, 1)$ and the accuracy factor $\varsigma \in (0, 1]$.

The complexity analysis also needs $\theta < \varsigma$, which is assumed where it is used. For
$\varsigma = 1$ it is $\theta < 1$. -/
structure ARqpParams extends ARParams where
  /-- The model-optimality tolerance factor $\theta$ of (12.2.29). -/
  θ : ℝ
  /-- The accuracy factor $\varsigma$ of approximate measure evaluations, as in (12.2.26) and
  (12.2.29). -/
  ς : ℝ
  /-- The tolerance factor is positive: $\theta > 0$. -/
  θ_pos : 0 < θ
  /-- The tolerance factor is less than one: $\theta < 1$. -/
  θ_lt_one : θ < 1
  /-- The accuracy factor is positive: $\varsigma > 0$. -/
  ς_pos : 0 < ς
  /-- The accuracy factor is at most one: $\varsigma \le 1$. -/
  ς_le_one : ς ≤ 1

/-- The **model data** of one iteration of a high-order adaptive-regularization method, as in
(12.2.23), (12.2.26)–(12.2.30) and (14.1.10)–(14.1.15) of [cartis2022evaluation]. An element
consists of

* the decrement $\Delta T_j(x_k, \cdot)$ of order $j$ of the objective's model at the iterate,
  used in Step 1;
* the regularized model $m_k$;
* the decrement $\Delta T_{m_k, j}(s, \cdot)$ of order $j$ of the model at a trial step $s$,
  used in Step 2;
* the predicted decrease $\Delta T_p(x_k, s)$ used in the ratio. -/
structure ARqpData (E : Type*) where
  /-- The decrement of order $j$ of the objective's model at the iterate. -/
  dec : ℕ → E → ℝ
  /-- The regularized model $m_k$. -/
  model : E → ℝ
  /-- The decrement of order $j$ of the model at a trial step $s$. -/
  modelDec : ℕ → E → E → ℝ
  /-- The predicted decrease at a trial step $s$, used in the ratio. -/
  pred : E → ℝ

section Data

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The model data of ARqp for exact or inexact derivative data $D$, as in (12.2.23),
(12.2.26)–(12.2.30) of [cartis2022evaluation] and (13.1.45) for inexact data. With
$T_j(s) = \sum_{i \le j} D_i[s]^i / i!$ and $m(s) = T_p(s) + \sigma \|s\|^{p+1} / (p+1)!$, the
data are

* the decrements $\Delta T_j(d) = T_j(0) - T_j(d)$;
* the model $m$;
* the decrements $\Delta T_{m,j}(s, d) = T_{m,j}(s, 0) - T_{m,j}(s, d)$, where
  $T_{m,j}(s, \cdot)$ is the Taylor polynomial of degree $j$ of $m$ at $s$;
* the predicted decrease $\Delta T_p(s) = T_p(0) - T_p(s)$.

The model is `Optimization.regularizedModel D p σ`, and the decrements are
`FormalMultilinearSeries.taylorDecrement`. -/
@[simps]
noncomputable def ARqpData.ofTaylor (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) :
    ARqpData E where
  dec j := D.taylorDecrement j
  model := regularizedModel D p σ
  modelDec j s := (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j
  pred := D.taylorDecrement p

/-- The model data of ARqpC, as in (14.1.10)–(14.1.15) of [cartis2022evaluation], for derivative
data $D_f$ of $f$ and $D_c$ of $c$ and a function $h$. With
$T_{w,j}(d) = T_{f,j}(d) + h(T_{c,j}(d))$, the data are

* the composite decrements $\Delta T_{w,j}(d) = T_{w,j}(0) - T_{w,j}(d)$;
* the composite model $\hat m(s) = T_{f,p}(s) + h(T_{c,p}(s)) + \sigma \|s\|^{p+1} / (p+1)!$ of
  (14.1.11);
* the model decrements (14.1.14);
* the predicted decrease $\Delta T_{w,p}$.

The model is `Optimization.compositeRegularizedModel`, the decrements are
`Optimization.compositeTaylorDecrement`, and the model decrements are
`Optimization.compositeModelDecrement`. -/
@[simps]
noncomputable def ARqpData.ofComposite (Df : FormalMultilinearSeries ℝ E ℝ)
    (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ) (p : ℕ) (σ : ℝ) : ARqpData E where
  dec j := compositeTaylorDecrement Df Dc h j
  model := compositeRegularizedModel Df Dc h p σ
  modelDec j s := compositeModelDecrement Df Dc h p σ j s
  pred := compositeTaylorDecrement Df Dc h p

/-- For $h = 0$ the composite model data are the Taylor model data:
`Optimization.ARqpData.ofComposite Df Dc 0 p σ = Optimization.ARqpData.ofTaylor Df p σ`. -/
theorem ARqpData.ofComposite_zero_fun (Df : FormalMultilinearSeries ℝ E ℝ)
    (Dc : FormalMultilinearSeries ℝ E F) (p : ℕ) (σ : ℝ) :
    ARqpData.ofComposite Df Dc (0 : F → ℝ) p σ = ARqpData.ofTaylor Df p σ := by
  simp only [ARqpData.ofComposite, ARqpData.ofTaylor, compositeTaylorDecrement_zero_fun,
    compositeRegularizedModel_zero_fun, compositeModelDecrement_zero_fun]

end Data

variable {E : Type*} [NormedAddCommGroup E]

/-- **The Step-2 conditions of ARqp**, (12.2.27)–(12.2.29) and (14.1.12)–(14.1.13) of
[cartis2022evaluation]. Let $X \subseteq E$, let $M$ be model data at the iterate $x$, and let
$q$ and $\varepsilon_1, \ldots, \varepsilon_q$ be given. A step $s$ with radii $\delta^s_j$ and
witnesses $d^m_j$ satisfies the conditions if

* the trial point is feasible: $x + s \in X$;
* the model does not increase (12.2.27): $m(s) \le m(0)$;
* if $m(s) = m(0)$, then $0$ minimizes $m$ over the feasible steps $\{e \mid x + e \in X\}$;
* $0 < \delta^s_j \le 1$ for $j = 1, \ldots, q$;
* either $\|s\| \ge 1$, or for every $j = 1, \ldots, q$ the witness $d^m_j$ is a
  $\varsigma$-approximate optimality displacement of the model decrement
  $\Delta T_{m,j}(s, \cdot)$ with radius $\delta^s_j$ over $\{e \mid x + s + e \in X\}$, and
  (12.2.29)
$$\Delta T_{m,j}(s, d^m_j) \le \varsigma \theta \varepsilon_j \frac{(\delta^s_j)^j}{j!}.$$

Approximate optimality displacements are `Optimization.IsApproxMeasureStep`. -/
structure ARqpStep (X : Set E) (P : ARqpParams) (q : ℕ) (ε : ℕ → ℝ) (M : ARqpData E)
    (x s : E) (δs : ℕ → ℝ) (dm : ℕ → E) : Prop where
  /-- The trial point $x + s$ lies in $X$. -/
  mem : x + s ∈ X
  /-- The model does not increase, (12.2.27): $m(s) \le m(0)$. -/
  model_le : M.model s ≤ M.model 0
  /-- If $m(s) = m(0)$, so that the method terminates in Step 2, then $0$ minimizes the model over
  the feasible steps. -/
  isMinOn_of_eq : M.model s = M.model 0 → IsMinOn M.model {e | x + e ∈ X} 0
  /-- The radii are positive: $\delta^s_j > 0$ for $j = 1, \ldots, q$. -/
  radius_pos : ∀ j ∈ Finset.Icc 1 q, 0 < δs j
  /-- The radii are at most one: $\delta^s_j \le 1$ for $j = 1, \ldots, q$. -/
  radius_le_one : ∀ j ∈ Finset.Icc 1 q, δs j ≤ 1
  /-- Either the step is long, $\|s\| \ge 1$, or the approximate model optimality (12.2.29) holds
  with the witnesses $d^m_j$. -/
  branch : 1 ≤ ‖s‖ ∨ ∀ j ∈ Finset.Icc 1 q,
    IsApproxMeasureStep (M.modelDec j s) (δs j) {e | x + s + e ∈ X} P.ς (dm j) ∧
      M.modelDec j s (dm j) ≤ P.ς * P.θ * ε j * δs j ^ j / j !

/-- The Step-1 test of ARqp at iteration $k$, Step 1 of Algorithm 12.2.2 of [cartis2022evaluation]
in normalized form: for every $j = 1, \ldots, q$, the decrease of order $j$ along the witness
$d_{k,j}$ is at most $\varsigma \varepsilon_j \delta_{k,j}^j / j!$. -/
abbrev arqpStop₁ (P : ARqpParams) (q : ℕ) (ε : ℕ → ℝ) (M : ℕ → ARqpData E)
    (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  MeasureTestPasses (M k).dec q P.ς ε (δ k) (d k)

/-- The Step-2 termination test of ARqp at iteration $k$: $m_k(s_k) = m_k(0)$. -/
abbrev arqpStop₂ (M : ℕ → ARqpData E) (s : ℕ → E) (k : ℕ) : Prop :=
  (M k).model (s k) = (M k).model 0

/-- The ratio (12.2.30), (14.1.15) of ARqp at iteration $k$ for the objective $w$: $\rho_k =
(w(x_k) - w(x_k + s_k)) / \mathrm{pred}_k(s_k)$, with the predicted decrease of the model data. -/
noncomputable abbrev arqpRatio (w : E → ℝ) (M : ℕ → ARqpData E) (x s : ℕ → E) (k : ℕ) : ℝ :=
  reductionRatio w (x k) (s k) ((M k).pred (s k))

omit [NormedAddCommGroup E] in
/-- The Step-1 test of ARqp holds at iteration $k$ if and only if $\Delta T_j(x_k, d_{k,j}) \le
\varsigma \varepsilon_j \delta_{k,j}^j / j!$ for every $j = 1, \ldots, q$. -/
theorem arqpStop₁_iff {P : ARqpParams} {q : ℕ} {ε : ℕ → ℝ} {M : ℕ → ARqpData E}
    {δ : ℕ → ℕ → ℝ} {d : ℕ → ℕ → E} {k : ℕ} :
    arqpStop₁ P q ε M δ d k ↔
      ∀ j ∈ Finset.Icc 1 q, (M k).dec j (d k j) ≤ P.ς * ε j * δ k j ^ j / j ! :=
  Iff.rfl

/-- The Step-2 test of ARqp holds at iteration $k$ if and only if $m_k(s_k) = m_k(0)$. -/
theorem arqpStop₂_iff {M : ℕ → ARqpData E} {s : ℕ → E} {k : ℕ} :
    arqpStop₂ M s k ↔ (M k).model (s k) = (M k).model 0 :=
  Iff.rfl

/-- The ratio of ARqp at iteration $k$ is the reduction ratio of $w$ at $x_k$ and $s_k$ with the
predicted decrease of the model data. -/
theorem arqpRatio_eq (w : E → ℝ) (M : ℕ → ARqpData E) (x s : ℕ → E) (k : ℕ) :
    arqpRatio w M x s k = reductionRatio w (x k) (s k) ((M k).pred (s k)) :=
  rfl

/-- **A run of ARqp**, Algorithm 12.2.2 of [cartis2022evaluation]; with composite data it is
Algorithm 14.1.1, and with a general feasible set it is the variant of §14.2. The data are the
objective $w$, the feasible set $X$, the constants $P$, the order $q$, the accuracies
$\varepsilon_j$, the initial radii $\delta_{0,j}$, and the model data $M_k$ of each iteration.
The sequences are the iterates $x_k$, the steps $s_k$, the weights $\sigma_k$, the Step-1 radii
$\delta_{k,j}$ and witnesses $d_{k,j}$, and the Step-2 radii $\delta^s_{k,j}$ and witnesses
$d^m_{k,j}$. They form a **run** if

* they form a generic AR run (`Optimization.IsARRun`) with the Step-1 test
  `Optimization.arqpStop₁`, the Step-2 conditions `Optimization.ARqpStep`, the post-step test
  $m_k(s_k) = m_k(0)$ and the ratio `Optimization.arqpRatio`;
* $x_0 \in X$ and $\delta_0$ is the given initial radii;
* at every reached iteration $k$ and every $j = 1, \ldots, q$, the witness $d_{k,j}$ is a
  $\varsigma$-approximate optimality displacement of $\Delta T_j(x_k, \cdot)$ with radius
  $\delta_{k,j}$ over $\{e \mid x_k + e \in X\}$ ((12.2.26), (14.1.10));
* at every iteration $k$ before termination, a successful iteration sets
  $\delta_{k+1} = \delta^s_k$, and an unsuccessful one keeps $\delta_{k+1} = \delta_k$ and
  $d_{k+1} = d_k$.

The run terminates at the first $k$ at which the Step-1 test or the Step-2 test holds. -/
structure IsARqpRun (w : E → ℝ) (X : Set E) (P : ARqpParams) (q : ℕ) (ε δ₀ : ℕ → ℝ)
    (M : ℕ → ARqpData E) (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) :
    Prop where
  /-- Steps 2–4: the sequences form a generic adaptive-regularization run. -/
  toIsARRun : IsARRun P.toARParams (arqpStop₁ P q ε M δ d)
    (fun k => ARqpStep X P q ε (M k) (x k) (s k) (δs k) (dm k)) (arqpStop₂ M s)
    (arqpRatio w M x s) x s σ
  /-- The initial point is feasible: $x_0 \in X$. -/
  mem_zero : x 0 ∈ X
  /-- The initial radii are the given ones. -/
  delta_zero : δ 0 = δ₀
  /-- Step 1, (12.2.26) and (14.1.10): at every reached iteration, including the last one, the
  witnesses are $\varsigma$-approximate optimality displacements over the feasible
  displacements. -/
  witness : ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) →
    ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep ((M k).dec j) (δ k j) {e | x k + e ∈ X} P.ς (d k j)
  /-- Step 3: successful iterations take the Step-2 radii, and unsuccessful ones keep the radii and
  the Step-1 witnesses. -/
  radii : UntilHit (IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s)) fun k =>
    (P.η₁ ≤ arqpRatio w M x s k → δ (k + 1) = δs k) ∧
      (¬ P.η₁ ≤ arqpRatio w M x s k → δ (k + 1) = δ k ∧ d (k + 1) = d k)

namespace IsARqpRun

variable {w : E → ℝ} {X : Set E} {P : ARqpParams} {q : ℕ} {ε δ₀ : ℕ → ℝ}
  {M : ℕ → ARqpData E} {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E}

/-- In a run of ARqp, the Step-2 conditions hold at every reached iteration at which the Step-1 test
fails. -/
theorem step (h : IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i)
    (h1 : ¬ arqpStop₁ P q ε M δ d k) : ARqpStep X P q ε (M k) (x k) (s k) (δs k) (dm k) :=
  h.toIsARRun.step k hk h1

/-- **The iterates stay feasible.** In a run of ARqp, $x_k \in X$ for every reached iteration $k$.
-/
theorem mem (h : IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm) :
    ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) → x k ∈ X := by
  intro k
  induction k with
  | zero => exact fun _ => h.mem_zero
  | succ k ih =>
    intro hk
    have hk' : ∀ i ≤ k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i :=
      fun i hi => hk i (Nat.lt_succ_of_le hi)
    have hacc := h.toIsARRun.accept k hk'
    rcases hacc.eq_add_or_eq_self with h' | h'
    · rw [h']
      exact (h.step (fun i hi => hk' i hi.le) fun h1 => hk' k le_rfl (Or.inl h1)).mem
    · rw [h']
      exact ih fun i hi => hk' i hi.le

/-- **Strict model decrease before termination.** In a run of ARqp, every iteration $k$ before
termination satisfies $m_k(s_k) < m_k(0)$.

This follows from (12.2.27) and the failed Step-2 test. It is the model-decrease hypothesis of
`Optimization.IsARRun.sigma_le`. -/
theorem model_lt (h : IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) :
    (M k).model (s k) < (M k).model 0 := by
  have hstep := h.step (fun i hi => hk i hi.le) fun h1 => hk k le_rfl (Or.inl h1)
  exact lt_of_le_of_ne hstep.model_le fun h2 => hk k le_rfl (Or.inr h2)

/-- **The radii stay in $(0, 1]$.** In a run of ARqp, let $0 < \delta_{0,j} \le 1$ for
$j = 1, \ldots, q$. Then $0 < \delta_{k,j} \le 1$ for every reached iteration $k$ and every
$j = 1, \ldots, q$. -/
theorem delta_mem (h : IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) :
    ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) →
      ∀ j ∈ Finset.Icc 1 q, 0 < δ k j ∧ δ k j ≤ 1 := by
  intro k
  induction k with
  | zero => exact fun _ => by rw [h.delta_zero]; exact hδ₀
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i :=
      fun i hi => hk i (Nat.lt_succ_of_le hi)
    obtain ⟨hs, hu⟩ := h.radii k hk'
    by_cases hρ : P.η₁ ≤ arqpRatio w M x s k
    · have hstep := h.step (fun i hi => hk' i hi.le) fun h1 => hk' k le_rfl (Or.inl h1)
      rw [hs hρ]
      exact ⟨hstep.radius_pos j hj, hstep.radius_le_one j hj⟩
    · rw [(hu hρ).1]
      exact ih (fun i hi => hk' i hi.le) j hj

/-- **Restricting an unconstrained run to a feasible set.** Consider a run of ARqp with the feasible
set $E$, and let $X \subseteq E$. Assume that the decrements $\Delta T_j(x_k, \cdot)$ and
$\Delta T_{m_k, j}(s_k, \cdot)$ are bounded above on every ball, as they are for Taylor data.
Assume also that for every reached iteration $k$ and every $j = 1, \ldots, q$
$$x_k \in X, \qquad x_k + d_{k,j} \in X, \qquad x_k + s_k \in X,$$
and $x_k + s_k + d^m_{k,j} \in X$ if $\|s_k\| < 1$. Then the same sequences form a run of ARqp
on $X$. -/
theorem of_univ (h : IsARqpRun w univ P q ε δ₀ M x s σ δ δs d dm) {X : Set E}
    (hdec : ∀ k j r, BddAbove ((M k).dec j '' (closedBall 0 r ∩ {e | x k + e ∈ univ})))
    (hmdec : ∀ k j r, BddAbove
      ((M k).modelDec j (s k) '' (closedBall 0 r ∩ {e | x k + s k + e ∈ univ})))
    (hX : ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) →
      x k ∈ X ∧ (∀ j ∈ Finset.Icc 1 q, x k + d k j ∈ X) ∧ x k + s k ∈ X ∧
        (‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q, x k + s k + dm k j ∈ X)) :
    IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm := by
  have hς := P.ς_pos.le
  refine ⟨⟨h.toIsARRun.sigma_zero, fun k hk h1 => ?_, h.toIsARRun.accept⟩,
    (hX 0 fun _ h => absurd h (Nat.not_lt_zero _)).1, h.delta_zero, fun k hk j hj => ?_, h.radii⟩
  · have hst := h.toIsARRun.step k hk h1
    obtain ⟨-, -, hs, hdm⟩ := hX k hk
    refine ⟨hs, hst.model_le, fun he => (hst.isMinOn_of_eq he).of_subset (subset_univ _),
      hst.radius_pos, hst.radius_le_one, ?_⟩
    rcases hst.branch with hl | hb
    · exact Or.inl hl
    rcases le_or_gt 1 ‖s k‖ with hl | hl
    · exact Or.inl hl
    · exact Or.inr fun j hj => ⟨(hb j hj).1.mono_set hς (hmdec k j _) (fun _ _ => mem_univ _)
        (hdm hl j hj), (hb j hj).2⟩
  · exact (h.witness k hk j hj).mono_set hς (hdec k j _) (fun _ _ => mem_univ _)
      ((hX k hk).2.1 j hj)

end IsARqpRun

/-! ### Existence of runs -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Lemma 12.2.9** of [cartis2022evaluation], existence of an ARqp step without constraints. Let
$E$ be finite-dimensional, let $1 \le p$ and $q \le p$, and let $\varepsilon_j > 0$ for
$j = 1, \ldots, q$. Let $D$ be derivative data with $\|D_i\| \le L$ for $i = 2, \ldots, p$,
where $L \ge 0$, and let $\sigma > 0$ and $x \in E$. Then there are a step $s$, radii $\delta^s$
and witnesses $d^m$ that satisfy the Step-2 conditions `Optimization.ARqpStep` with $X = E$ and
the model data `Optimization.ARqpData.ofTaylor D p σ`, with
$$\delta^s_j = 1 \quad (j \le 2), \qquad \delta^s_j = \min\Bigl(1, \frac{\varsigma \theta
  \varepsilon_j}{4 (3L + \sigma)}\Bigr) \quad (3 \le j \le q),$$
as in (12.2.44) and (12.2.45). -/
theorem exists_arqpStep_ofTaylor [FiniteDimensional ℝ E] (P : ARqpParams) {p q : ℕ}
    (hp : 1 ≤ p) (hq : q ≤ p) {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    {D : FormalMultilinearSeries ℝ E ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) {σ : ℝ} (hσ : 0 < σ) (x : E) :
    ∃ s : E, ∃ δs : ℕ → ℝ, ∃ dm : ℕ → E,
      ARqpStep univ P q ε (ARqpData.ofTaylor D p σ) x s δs dm ∧
      (∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs j = 1) ∧
      ∀ j ∈ Finset.Icc 3 q, δs j = min 1 (P.ς * P.θ * ε j / (4 * (3 * L + σ))) := by
  obtain ⟨s, δs, dm, hmin, hrad, h12, h3, hbranch⟩ :=
    exists_highOrderStep (D := D) (σ := σ) hp hq hσ hL hD P.θ_pos P.ς_pos P.ς_le_one hε
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  refine ⟨s, δs, dm, ⟨mem_univ _, hmin (mem_univ 0), fun heq => ?_,
    fun j hj => (hrad j hj).1, fun j hj => (hrad j hj).2, ?_⟩, h12, h3⟩
  · refine isMinOn_iff.2 fun e _ => ?_
    change regularizedModel D p σ 0 ≤ regularizedModel D p σ e
    change regularizedModel D p σ s = regularizedModel D p σ 0 at heq
    rw [← heq]
    exact hmin (mem_univ e)
  · rw [hU]
    exact hbranch

/-- One ARqp iteration's state in the existence proof: iterate, weight, Step-1 radii and
witnesses, and the Step-2 step, radii and witnesses. -/
private structure ARqpState (E : Type*) where
  x : E
  σ : ℝ
  δ : ℕ → ℝ
  d : ℕ → E
  s : E
  δs : ℕ → ℝ
  dm : ℕ → E

omit [InnerProductSpace ℝ E] in
/-- **Existence of ARqp runs from the existence of steps**: the method is well defined as soon as
its steps exist. Let $M(y, \sigma)$ be model data at the point $y$ with weight $\sigma$, let
$0 < \delta_{0,j} \le 1$ for $j = 1, \ldots, q$, and let $Q(y, \sigma, s, \delta^s, d^m)$ be a
property. Assume that

* for every $y \in X$ and all radii $\delta \in (0, 1]^q$ there are Step-1 witnesses $d_j$ that,
  for every weight $\sigma$, are $\varsigma$-approximate optimality displacements of the
  decrements of $M(y, \sigma)$ with radius $\delta_j$ over $\{e \mid y + e \in X\}$;
* for every $y \in X$ and $\sigma > 0$ there is a triple $(s, \delta^s, d^m)$ that satisfies the
  Step-2 conditions `Optimization.ARqpStep` for $M(y, \sigma)$ and the property
  $Q(y, \sigma, s, \delta^s, d^m)$.

Then for every $x_0 \in X$ there is a run of ARqp from $x_0$ with the model data
$M(x_k, \sigma_k)$, whose Step-2 triples satisfy $Q$ at every reached iteration. -/
theorem exists_isARqpRun_of_forall (w : E → ℝ) (X : Set E) (P : ARqpParams) {q : ℕ}
    {ε δ₀ : ℕ → ℝ} (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (M : E → ℝ → ARqpData E)
    (Q : E → ℝ → E → (ℕ → ℝ) → (ℕ → E) → Prop)
    (hwit : ∀ y ∈ X, ∀ δ : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) →
      ∃ d : ℕ → E, ∀ σ, ∀ j ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((M y σ).dec j) (δ j) {e | y + e ∈ X} P.ς (d j))
    (hstep : ∀ y ∈ X, ∀ σ, 0 < σ → ∃ (s : E) (δs : ℕ → ℝ) (dm : ℕ → E),
      ARqpStep X P q ε (M y σ) y s δs dm ∧ Q y σ s δs dm)
    {x₀ : E} (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      IsARqpRun w X P q ε δ₀ (fun k => M (x k) (σ k)) x s σ δ δs d dm ∧
      ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε (fun k => M (x k) (σ k)) δ d)
          (arqpStop₂ (fun k => M (x k) (σ k)) s) i) →
        Q (x k) (σ k) (s k) (δs k) (dm k) := by
  classical
  -- Step-1 witnesses
  have hwit' : ∀ (y : E) (δ : ℕ → ℝ), ∃ d : ℕ → E, y ∈ X →
      (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) → ∀ σ, ∀ j ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((M y σ).dec j) (δ j) {e | y + e ∈ X} P.ς (d j) := by
    intro y δ
    by_cases h : y ∈ X ∧ ∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1
    · obtain ⟨d, hd⟩ := hwit y h.1 δ h.2
      exact ⟨d, fun _ _ => hd⟩
    · exact ⟨0, fun hy hδ => absurd ⟨hy, hδ⟩ h⟩
  choose wit hwit using hwit'
  -- Step-2 steps
  have hstp : ∀ (y : E) (σ : ℝ), ∃ t : E × (ℕ → ℝ) × (ℕ → E), y ∈ X → 0 < σ →
      ARqpStep X P q ε (M y σ) y t.1 t.2.1 t.2.2 ∧ Q y σ t.1 t.2.1 t.2.2 := by
    intro y σ
    by_cases h : y ∈ X ∧ 0 < σ
    · obtain ⟨s, δs, dm, h'⟩ := hstep y h.1 σ h.2
      exact ⟨(s, δs, dm), fun _ _ => h'⟩
    · exact ⟨(0, 0, 0), fun hy hσ => absurd ⟨hy, hσ⟩ h⟩
  choose stp hstp using hstp
  -- the states and their invariant
  let mk : E → ℝ → (ℕ → ℝ) → (ℕ → E) → ARqpState E := fun y σ δ d =>
    ⟨y, σ, δ, d, (stp y σ).1, (stp y σ).2.1, (stp y σ).2.2⟩
  let Good : ARqpState E → Prop := fun a =>
    a.x ∈ X ∧ P.σmin ≤ a.σ ∧ 0 < a.σ ∧ (∀ j ∈ Finset.Icc 1 q, 0 < a.δ j ∧ a.δ j ≤ 1) ∧
      (∀ σ, ∀ j ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((M a.x σ).dec j) (a.δ j) {e | a.x + e ∈ X} P.ς (a.d j)) ∧
      ARqpStep X P q ε (M a.x a.σ) a.x a.s a.δs a.dm ∧ Q a.x a.σ a.s a.δs a.dm
  have hmk : ∀ y σ δ d, y ∈ X → P.σmin ≤ σ → 0 < σ →
      (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) →
      (∀ σ, ∀ j ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((M y σ).dec j) (δ j) {e | y + e ∈ X} P.ς (d j)) →
      Good (mk y σ δ d) := fun y σ δ d hy h1 h2 h3 h4 => ⟨hy, h1, h2, h3, h4, hstp y σ hy h2⟩
  let stopS : ARqpState E → Prop := fun a =>
    MeasureTestPasses (M a.x a.σ).dec q P.ς ε a.δ a.d ∨ (M a.x a.σ).model a.s = (M a.x a.σ).model 0
  let ratio : ARqpState E → ℝ := fun a => reductionRatio w a.x a.s ((M a.x a.σ).pred a.s)
  let Trans : ARqpState E → ARqpState E → Prop := fun a b =>
    ARAcceptance P.toARParams (ratio a) a.x a.s b.x a.σ b.σ ∧
      (P.η₁ ≤ ratio a → b.δ = a.δs) ∧ (¬ P.η₁ ≤ ratio a → b.δ = a.δ ∧ b.d = a.d)
  have hnext : ∀ a, Good a → ∃ b, Good b ∧ Trans a b := by
    rintro a ⟨hx, hmin, hpos, hδ, hw, hst, -⟩
    obtain ⟨σ', hacc, hmin', hpos'⟩ := exists_arAcceptance P.toARParams (ratio a) a.x a.s hmin
    by_cases hρ : P.η₁ ≤ ratio a
    · simp only [hρ, ↓reduceIte] at hacc
      have hδs : ∀ j ∈ Finset.Icc 1 q, 0 < a.δs j ∧ a.δs j ≤ 1 :=
        fun j hj => ⟨hst.radius_pos j hj, hst.radius_le_one j hj⟩
      refine ⟨mk (a.x + a.s) σ' a.δs (wit (a.x + a.s) a.δs), hmk _ _ _ _ hst.mem hmin'
        (hpos' hpos) hδs (hwit _ _ hst.mem hδs), hacc, fun _ => rfl,
        fun h => absurd hρ h⟩
    · simp only [hρ, ↓reduceIte] at hacc
      exact ⟨mk a.x σ' a.δ a.d, hmk _ _ _ _ hx hmin' (hpos' hpos) hδ hw, hacc,
        fun h => absurd h hρ, fun _ => ⟨rfl, rfl⟩⟩
  -- the initial state
  set a₀ := mk x₀ P.σ₀ δ₀ (wit x₀ δ₀) with ha₀
  have hgood₀ : Good a₀ := hmk _ _ _ _ hx₀ P.σmin_le_σ₀ P.σ₀_pos hδ₀ (hwit _ _ hx₀ hδ₀)
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant
    (init := fun a => a = a₀) (inv := fun _ a => Good a) (stop := fun _ a => stopS a)
    (step := fun _ a b => Trans a b ∧ Good b) ⟨a₀, rfl⟩ (fun a ha => ha ▸ hgood₀)
    (fun _ a ha _ => by
      obtain ⟨b, hb, hab⟩ := hnext a ha
      exact ⟨b, hb, hab, hb⟩)
  have hgood : ∀ k, (∀ i < k, ¬ stopS (r i)) → Good (r k) := by
    intro k hk
    cases k with
    | zero => rw [hr0]; exact hgood₀
    | succ k => exact (hr k fun j hj => hk j (Nat.lt_succ_of_le hj)).2.2
  refine ⟨fun k => (r k).x, fun k => (r k).s, fun k => (r k).σ, fun k => (r k).δ,
    fun k => (r k).δs, fun k => (r k).d, fun k => (r k).dm, by simp [hr0, ha₀, mk], ?_,
    fun k hk => (hgood k hk).2.2.2.2.2.2⟩
  exact ⟨⟨by simp [hr0, ha₀, mk], fun k hk _ => (hgood k hk).2.2.2.2.2.1,
    fun k hk => (hr k hk).2.1.1⟩, (hgood 0 fun _ h => absurd h (Nat.not_lt_zero _)).1,
    by simp [hr0, ha₀, mk], fun k hk => (hgood k hk).2.2.2.2.1 (r k).σ,
    fun k hk => (hr k hk).2.1.2⟩

/-- **Existence of ARqp runs**, Lemmas 12.2.9–12.2.10 of [cartis2022evaluation]: the conceptual ARqp
algorithm is well defined. Let $E$ be finite-dimensional and $f : E \to \mathbb{R}$, let
$1 \le p$ and $q \le p$, and let $\varepsilon_j > 0$ and $0 < \delta_{0,j} \le 1$ for
$j = 1, \ldots, q$. Let $L : E \to \mathbb{R}$ be nonnegative with $\|\nabla^i f(y)\| \le L(y)$
for all $y$ and $i = 2, \ldots, p$. Then for every $x_0$ there is a run of exact ARqp from
$x_0$, with $X = E$ and the model data `Optimization.ARqpData.ofTaylor (ftaylorSeries ℝ f (x k))
p (σ k)`, whose Step-2 radii satisfy at every reached iteration $k$
$$\delta^s_{k,j} = 1 \quad (j \le 2), \qquad \delta^s_{k,j} = \min\Bigl(1, \frac{\varsigma
  \theta \varepsilon_j}{4 (3 L(x_k) + \sigma_k)}\Bigr) \quad (3 \le j \le q),$$
as in (12.2.44)–(12.2.45).

Under assumption f.D1pL (12.2.24) the bound $L$ is a constant. Every $f$ has such a bound, for
example $L(y) = \sum_{i=2}^p \|\nabla^i f(y)\|$. -/
theorem exists_isARqpRun [FiniteDimensional ℝ E] (f : E → ℝ) (P : ARqpParams) {p q : ℕ}
    (hp : 1 ≤ p) (hq : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (L : E → ℝ) (hL0 : ∀ y, 0 ≤ L y)
    (hL : ∀ y, ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤ L y) (x₀ : E) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      IsARqpRun f univ P q ε δ₀ (fun k => ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k))
        x s σ δ δs d dm ∧
      ∀ k, (∀ i < k, ¬ IsARRun.Stop
          (arqpStop₁ P q ε (fun k => ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)) δ d)
          (arqpStop₂ (fun k => ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)) s) i) →
        (∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs k j = 1) ∧
        ∀ j ∈ Finset.Icc 3 q, δs k j = min 1 (P.ς * P.θ * ε j / (4 * (3 * L (x k) + σ k))) := by
  refine exists_isARqpRun_of_forall f univ P hδ₀
    (fun y σ => ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σ)
    (fun y σ _ δs _ => (∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs j = 1) ∧
      ∀ j ∈ Finset.Icc 3 q, δs j = min 1 (P.ς * P.θ * ε j / (4 * (3 * L y + σ))))
    (fun y _ δ hδ => ?_) (fun y _ σ hσ => ?_) (mem_univ x₀)
  · have h : ∀ j, ∃ dj : E, j ∈ Finset.Icc 1 q → IsApproxMeasureStep
        ((ftaylorSeries ℝ f y).taylorDecrement j) (δ j) {e | y + e ∈ (univ : Set E)} P.ς dj := by
      intro j
      by_cases hj : j ∈ Finset.Icc 1 q
      · obtain ⟨dj, hdj⟩ := exists_isApproxMeasureStep_taylorDecrement (ftaylorSeries ℝ f y) j
          (S := {e | y + e ∈ (univ : Set E)}) (by simp) (by simp) (hδ j hj).1.le P.ς_le_one
        exact ⟨dj, fun _ => hdj⟩
      · exact ⟨0, fun h' => absurd h' hj⟩
    choose d hd using h
    exact ⟨d, fun _ j hj => hd j hj⟩
  · obtain ⟨s, δs, dm, h⟩ := exists_arqpStep_ofTaylor P hp hq hε (hL0 y) (hL y) hσ y
      (D := ftaylorSeries ℝ f y)
    exact ⟨s, δs, dm, h⟩

end Existence

end Optimization
