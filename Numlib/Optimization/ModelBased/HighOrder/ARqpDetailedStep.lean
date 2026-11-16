/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.Optimality.HighOrder

/-!
# The detailed step computation of ARqp

Algorithm 12.2.3 of [cartis2022evaluation] computes the step of the high-order
adaptive-regularization method ARqp. Without constraints, it works on the regularized model
$$m(s) = T_p(s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1}, \qquad T_p(s) = \sum_{i=0}^{p} \frac{1}{i!}
  D_i[s]^i,$$
for derivative data $D_0, D_1, \dots$ (a `FormalMultilinearSeries`) and a weight $\sigma > 0$. The
algorithm is the instance of the abstract transition system `Optimization.DetailedStepTrans` of
`Numlib.Optimization.ModelBased.HighOrderStep` in which the feasible steps and displacements are all
of $E$ and a radius $\delta_j$ can be halved only at the orders $j \ge 3$. Below,
$\Delta T_{m,j}(s, d)$ is the decrease of the order-$j$ Taylor polynomial of $m$ at $s$ along $d$,
$m^* = \inf_E m$, and $L \ge 0$ bounds $\|D_i\|$ for $i \in [2, p]$.

The file shows that every output of the algorithm is an admissible ARqp step with unit radii at the
orders $j \le 2$, that the radii stay above $\min\{1, \varsigma\theta\varepsilon_j/(8(3L +
\sigma))\}$ (12.2.45), and that in finite dimension every execution is finite and can always proceed
(Lemma 12.2.9).

## Main definitions

* `Optimization.ARqpDetailedTrans`: the transitions of Algorithm 12.2.3 for the model $m$.
* `Optimization.arqpRadiusLB`: the lower bound $\underline{\delta}_j$ on the radius of order $j$,
  which is $\min\{1, \varsigma\theta\varepsilon_j/(8(3L + \sigma))\}$ for $j \in [3, q]$ and $1$
  otherwise.

## Main results

* `Optimization.IsDetailedStepOutput.exists_arqpStep`: every output satisfies the Step-2 conditions
  (12.2.27)–(12.2.29) of ARqp and has $\delta_{s,j} = 1$ for $j \le 2$.
* `Optimization.arqpDetailedStep_radius_ge`: every state reached has radii $\delta_j \ge \min\{1,
  \varsigma\theta\varepsilon_j/(8(3L + \sigma))\}$ for $j \in [1, q]$.
* `Optimization.detailedHalvingBound_regularizedModel`: a halving at order $j \in [3, q]$ only
  happens when $\delta_j \ge 2\underline{\delta}_j$.
* `Optimization.detailedRestartGap_regularizedModel`: in finite dimension, a restart at a short
  trial step $s$ only happens when $m(s) - m^* \ge \eta$ for a fixed $\eta > 0$.
* `Optimization.arqpDetailedStep_terminates`: in finite dimension, there is no infinite execution.
* `Optimization.arqpDetailedStep_exists_trans`: in finite dimension, every state reached that is not
  final has a successor.

## Proof outline

A halving at order $j$ happens only while $\delta_j > \varsigma\theta\varepsilon_j/(4(3L + \sigma))$
(Lemma 12.2.8 of [cartis2022evaluation]), so the radii stay above $\underline{\delta}_j$. A restart
(Step 2.4.4) at a short trial step $s$ needs $m(s) - m^* \ge \eta$: at the orders $j \ge 3$ because
of the model decrease (12.2.37) with radii bounded below, and at the orders $j \le 2$ by
compactness, because the order-$j$ measure of $m$ vanishes at the global minimizers of $m$. The
abstract theorem `Optimization.detailedStep_terminates` turns these two bounds into termination.
-/

open Set Metric
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The order-$j$ decrement of the model $m = $ `Optimization.regularizedModel D p σ` at a trial
step $s$: the value at $d$ is $\Delta T_{m,j}(s, d) = T_{m,j}(s, 0) - T_{m,j}(s, d)$, where
$T_{m,j}(s, \cdot)$ is the Taylor polynomial of order $j$ of $m$ at $s$. -/
noncomputable abbrev arqpDetailedModelDec (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) :
    ℕ → E → E → ℝ :=
  fun j s d => (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d

/-- The transition relation of the detailed Step 2 of ARqp (Algorithm 12.2.3 of
[cartis2022evaluation]) for the model $m(s) = T_p(s) + \sigma \|s\|^{p+1}/(p+1)!$ of the
derivative data $D$. It is `Optimization.DetailedStepTrans` with the model $m$, all of $E$ as
the set of feasible steps and as the set of feasible displacements at every trial step, the
decrements $\Delta T_{m,j}(s, \cdot)$ of `Optimization.arqpDetailedModelDec`, the order $q$, the
constants $\varsigma$ and $\theta$, the tolerances $\varepsilon_j$, and the set of halved orders
$J = \{j \mid j \ge 3\}$.

Thus a radius $\delta_j$ is halved (Step 2.4.3) only at an order $j \ge 3$. At an order
$j \le 2$ a failed check always leads to a restart (Step 2.4.4). -/
abbrev ARqpDetailedTrans (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) (q : ℕ) (ς θ : ℝ)
    (ε : ℕ → ℝ) : DetailedStepState E → DetailedStepState E → Prop :=
  DetailedStepTrans (regularizedModel D p σ) univ (fun _ => univ) (arqpDetailedModelDec D p σ) q ς θ
    ε {j | 3 ≤ j}

/-- The lower bound on the radius of order $j$ in Algorithm 12.2.3 of [cartis2022evaluation]:
$$\underline{\delta}_j = \begin{cases} \min\Big\{1, \dfrac{\varsigma\theta\varepsilon_j}{8(3L +
  \sigma)}\Big\} & \text{if } 3 \le j \le q, \\ 1 & \text{otherwise}. \end{cases}$$

At the orders $j \in [3, q]$ this is the bound (12.2.45). The other orders are never halved, so
their radii stay $1$. If $3L + \sigma = 0$, the quotient is $0$ by the Lean convention for
division by zero. -/
noncomputable def arqpRadiusLB (q : ℕ) (ς θ L σ : ℝ) (ε : ℕ → ℝ) (j : ℕ) : ℝ :=
  if 3 ≤ j ∧ j ≤ q then min 1 (ς * θ * ε j / (8 * (3 * L + σ))) else 1

section

variable {q : ℕ} {ς θ L σ : ℝ} {ε : ℕ → ℝ}

/-- For every order $j$, $\min\{1, \varsigma\theta\varepsilon_j/(8(3L + \sigma))\} \le
\underline{\delta}_j$, where $\underline{\delta}_j$ is
`Optimization.arqpRadiusLB q ς θ L σ ε j`. -/
theorem min_le_arqpRadiusLB (j : ℕ) :
    min 1 (ς * θ * ε j / (8 * (3 * L + σ))) ≤ arqpRadiusLB q ς θ L σ ε j := by
  unfold arqpRadiusLB; split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- If $\sigma > 0$, $L \ge 0$, $\varsigma > 0$, $\theta > 0$ and $\varepsilon_j > 0$ for
$j \in [1, q]$, then the radius bound $\underline{\delta}_j$ of `Optimization.arqpRadiusLB` is
positive for every $j$. -/
theorem arqpRadiusLB_pos (hσ : 0 < σ) (hL : 0 ≤ L) (hς : 0 < ς) (hθ : 0 < θ)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) (j : ℕ) : 0 < arqpRadiusLB q ς θ L σ ε j := by
  unfold arqpRadiusLB; split_ifs with h
  · have := hε j (Finset.mem_Icc.2 ⟨by omega, h.2⟩)
    exact lt_min one_pos (by positivity)
  · exact one_pos

/-- The radius bound $\underline{\delta}_j$ of `Optimization.arqpRadiusLB` is at most $1$ for every
$j$. -/
theorem arqpRadiusLB_le_one (j : ℕ) : arqpRadiusLB q ς θ L σ ε j ≤ 1 := by
  unfold arqpRadiusLB; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- The radius bound $\underline{\delta}_j$ of `Optimization.arqpRadiusLB` equals $1$ for $j < 3$.
-/
theorem arqpRadiusLB_eq_one {j : ℕ} (hj : j < 3) : arqpRadiusLB q ς θ L σ ε j = 1 := by
  unfold arqpRadiusLB; rw [ite_eq_right (by omega)]

end

section Termination

variable {D : FormalMultilinearSeries ℝ E ℝ} {p q : ℕ} {σ L ς θ : ℝ} {ε : ℕ → ℝ}

/-- Let $\sigma > 0$, $L \ge 0$ with $\|D_i\| \le L$ for $i \in [2, p]$, $j \in [1, p]$,
$\|s\| < 1$, $0 \le \delta_j \le 1$ and $\|d\| \le \delta_j$; if $\Delta T_{m,j}(s, d) >
\varsigma\theta\varepsilon_j\delta_j^j/j!$ and $m(s) - m(s + d) <
\varsigma\theta\varepsilon_j\delta_j^j/(2\,j!)$, then $\delta_j >
\varsigma\theta\varepsilon_j/(4(3L + \sigma))$ (the argument of Lemma 12.2.8 of
[cartis2022evaluation]). -/
private theorem lt_radius_of_halve (hσ : 0 < σ) (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {s d : E}
    (hs : ‖s‖ < 1) {δj : ℝ} (hδ0 : 0 ≤ δj) (hδ1 : δj ≤ 1) (hd : ‖d‖ ≤ δj)
    (hlarge : ς * θ * ε j * δj ^ j / j ! < arqpDetailedModelDec D p σ j s d)
    (hmodel : regularizedModel D p σ s - regularizedModel D p σ (s + d) <
      ς * θ * ε j * δj ^ j / (2 * j !)) :
    ς * θ * ε j / (4 * (3 * L + σ)) < δj := by
  by_contra hle
  push Not at hle
  have hK : 0 < 3 * L + σ := by positivity
  have hδα : 4 * (3 * L + σ) * δj ≤ ς * θ * ε j := by
    rw [le_div_iff₀ (by positivity)] at hle; linarith
  have := sub_regularizedModel_ge_of_taylorDecrement_ge hL hD hσ.le hj hs.le hδ0 hδ1 hδα hd
    hlarge.le
  have e : ς * θ * ε j / 2 * δj ^ j / j ! = ς * θ * ε j * δj ^ j / (2 * j !) := by ring
  linarith

/-- Let $\sigma > 0$, let $L \ge 0$ with $\|D_i\| \le L$ for $i \in [2, p]$, let $q \le p$,
$\varsigma > 0$ and $\theta > 0$, and let $\varepsilon_j > 0$ for $j \in [1, q]$. Then the model
$m$ of Algorithm 12.2.3 satisfies the halving hypothesis `Optimization.DetailedHalvingBound`
with the bounds $\underline{\delta}$ of `Optimization.arqpRadiusLB`. That is, let $s$ be a trial
step with $\|s\| < 1$, let $j \in [3, q]$, let the radii satisfy
$\underline{\delta}_j \le \delta_j \le 1$, and let $\|d\| \le \delta_j$. If
$$\Delta T_{m,j}(s, d) > \frac{\varsigma\theta\varepsilon_j\delta_j^j}{j!}
  \qquad\text{and}\qquad m(s) - m(s + d) <
  \frac{\varsigma\theta\varepsilon_j\delta_j^j}{2\,j!},$$
which are the conditions of a halving (Step 2.4.3), then $\delta_j \ge 2\underline{\delta}_j$.

The proof shows $\delta_j > \varsigma\theta\varepsilon_j/(4(3L + \sigma))$, as in Lemma 12.2.8
of [cartis2022evaluation], and this number is at least $2\underline{\delta}_j$. The result is a
step of the proof of Lemma 12.2.9. -/
theorem detailedHalvingBound_regularizedModel (hσ : 0 < σ) (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hqp : q ≤ p) (hς : 0 < ς) (hθ : 0 < θ)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) :
    DetailedHalvingBound (regularizedModel D p σ) univ (fun _ => univ)
      (arqpDetailedModelDec D p σ) q ς θ ε {j | 3 ≤ j} (arqpRadiusLB q ς θ L σ ε) := by
  intro s δ j d _ hs hj1 hjq hJ hlb hle1 hd hlarge hmodel
  have hlt := lt_radius_of_halve (ς := ς) (θ := θ) (ε := ε) hσ hL hD
    (Finset.mem_Icc.2 ⟨hj1, hjq.trans hqp⟩) hs
    ((arqpRadiusLB_pos hσ hL hς hθ hε j).le.trans hlb) hle1
    (mem_closedBall_zero_iff.1 hd.1) hlarge hmodel
  have h3 : 3 ≤ j := hJ
  have hK : 0 < 3 * L + σ := by positivity
  unfold arqpRadiusLB
  rw [ite_eq_left ⟨h3, hjq⟩]
  have e : ς * θ * ε j / (8 * (3 * L + σ)) = ς * θ * ε j / (4 * (3 * L + σ)) / 2 := by
    field_simp; ring
  have := min_le_right 1 (ς * θ * ε j / (8 * (3 * L + σ)))
  rw [e] at this ⊢
  linarith

/-- Let $\sigma > 0$, let $L \ge 0$ with $\|D_i\| \le L$ for $i \in [2, p]$, let $1 \le q \le p$,
$\varsigma > 0$ and $\theta > 0$, let $\varepsilon_j > 0$ for $j \in [1, q]$, and let
$\mu_0 \in (0, 1]$. Then every state $b$ that Algorithm 12.2.3 reaches from the initial state
with parameter $\mu_0$ and all radii $1$ has radii
$$\delta_j \ge \min\Big\{1, \frac{\varsigma\theta\varepsilon_j}{8(3L + \sigma)}\Big\}, \qquad j
  \in [1, q].$$
This is the bound (12.2.45) in the proof of Lemma 12.2.9 of [cartis2022evaluation].

A state reached is a state related to `findStep μ₀ (fun _ => 1)` by the reflexive transitive
closure of `Optimization.ARqpDetailedTrans`, and its radii are
`Optimization.DetailedStepState.radii`. The bound holds because a halving at order $j$ only
happens while $\delta_j > \varsigma\theta\varepsilon_j/(4(3L + \sigma))$ (Lemma 12.2.8). -/
theorem arqpDetailedStep_radius_ge (hσ : 0 < σ) (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hq : 1 ≤ q) (hqp : q ≤ p) (hς : 0 < ς)
    (hθ : 0 < θ) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Ioc (0 : ℝ) 1) {b : DetailedStepState E}
    (h : Relation.ReflTransGen (ARqpDetailedTrans D p σ q ς θ ε) (.findStep μ₀ fun _ => 1) b) :
    ∀ j ∈ Finset.Icc 1 q, min 1 (ς * θ * ε j / (8 * (3 * L + σ))) ≤ b.radii j :=
  fun j _ => (min_le_arqpRadiusLB (q := q) j).trans
    ((DetailedStepState.lb_le_radii hq (fun _ => arqpRadiusLB_le_one _)
      (detailedHalvingBound_regularizedModel hσ hL hD hqp hς hθ hε) hμ₀ h j).1)

/-- In finite dimension, with $\sigma > 0$ and $p \ge 1$, the model $m$ has a global minimizer
$s_0$, and $m^* = \inf_E m = m(s_0)$. -/
private theorem exists_eq_sInf [FiniteDimensional ℝ E] (hσ : 0 < σ) (hp : 1 ≤ p) :
    ∃ s₀, IsMinOn (regularizedModel D p σ) univ s₀ ∧
      sInf (regularizedModel D p σ '' univ) = regularizedModel D p σ s₀ := by
  obtain ⟨s₀, hmin, -⟩ := exists_isMinOn_regularizedModel (D := D) hσ hp
  exact ⟨s₀, hmin, IsLeast.csInf_eq ⟨⟨s₀, mem_univ _, rfl⟩,
    by rintro _ ⟨t, _, rfl⟩; exact hmin (mem_univ t)⟩⟩

/-- In finite dimension, with $\sigma > 0$, $1 \le p$, $j \in \{1, 2\}$, $j \le p$ and $\tau > 0$,
there is $\eta > 0$ such that $m(s) - m^* \ge \eta$ for every $s$ with $\|s\| \le 1$ and
$\phi^1_{m,j}(s) > \tau$, because these $s$ lie in a compact set on which $m > m^*$ (the measure
$\phi^1_{m,j}$ vanishes at the global minimizers, Theorem 12.1.4 of [cartis2022evaluation]). -/
private theorem exists_gap_low [FiniteDimensional ℝ E] (hσ : 0 < σ) (hp : 1 ≤ p) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 2) (hjp : j ≤ p) {τ : ℝ} (hτ : 0 < τ) :
    ∃ η > 0, ∀ s : E, ‖s‖ ≤ 1 →
      τ < taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j 1 univ →
      η ≤ regularizedModel D p σ s - sInf (regularizedModel D p σ '' univ) := by
  obtain ⟨s₀, hmin, hinf⟩ := exists_eq_sInf (D := D) hσ hp
  rw [hinf]
  set m := regularizedModel D p σ
  have hmc : ContDiff ℝ p m := contDiff_regularizedModel
  have hφ := Optimization.continuous_taylorMeasure_ftaylorSeries hmc hjp zero_le_one
  set K := closedBall (0 : E) 1 ∩ {s | τ ≤ taylorMeasure (ftaylorSeries ℝ m s) j 1 univ}
  have hK : IsCompact K :=
    (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const hφ)
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun s hs hτs => ?_⟩
    have : s ∈ K := ⟨mem_closedBall_zero_iff.2 hs, hτs.le⟩
    rw [hK0] at this
    exact absurd this (notMem_empty s)
  obtain ⟨s₁, hs₁, hmin₁⟩ := hK.exists_isMinOn hKne hmc.continuous.continuousOn
  refine ⟨m s₁ - m s₀, sub_pos.2 (lt_of_le_of_ne (hmin (mem_univ s₁)) fun heq => ?_),
    fun s hs hτs => ?_⟩
  · have hmin' : IsMinOn m univ s₁ := isMinOn_iff.2 fun t _ => by
      rw [← heq]; exact hmin (mem_univ t)
    have h0 := taylorMeasure_eq_zero_of_isLocalMin
      (hmc.contDiffAt.of_le (by exact_mod_cast hjp))
        (hmin'.isLocalMin Filter.univ_mem) hj zero_le_one
    have h1 : τ ≤ taylorMeasure (ftaylorSeries ℝ m s₁) j 1 univ := hs₁.2
    linarith
  · have := isMinOn_iff.1 hmin₁ s ⟨mem_closedBall_zero_iff.2 hs, hτs.le⟩
    linarith

/-- Let $E$ be finite-dimensional, let $\sigma > 0$, $L \ge 0$, $1 \le q \le p$, $\varsigma > 0$ and
$\theta > 0$, and let $\varepsilon_j > 0$ for $j \in [1, q]$. Then the model $m$ of Algorithm
12.2.3 satisfies the restart-gap hypothesis `Optimization.DetailedRestartGap` with the bounds
$\underline{\delta}$ of `Optimization.arqpRadiusLB`. That is, there is $\eta > 0$ with the
following property. Let $s$ be a trial step with $\|s\| < 1$, let $j \in [1, q]$, let the radii
satisfy $\underline{\delta}_i \le \delta_i \le 1$ for every $i$ and $\delta_i = 1$ for
$i \le 2$, and let $\|d\| \le \delta_j$ with $\Delta T_{m,j}(s, d) >
\varsigma\theta\varepsilon_j\delta_j^j/j!$. If $j \le 2$ or $m(s) - m(s + d) \ge
\varsigma\theta\varepsilon_j\delta_j^j/(2\,j!)$, which are the conditions of a restart (Step
2.4.4), then $m(s) - m^* \ge \eta$, where $m^* = \inf_E m$.

No bound on the derivative data $D$ is needed. At an order $j \ge 3$ the gap comes from the
model decrease (12.2.37) with radii bounded below. At an order $j \le 2$ it comes from
compactness, because the measure $\phi^1_{m,j}$ vanishes at the global minimizers of $m$. The
result is a step of the proof of Lemma 12.2.9 of [cartis2022evaluation]. -/
theorem detailedRestartGap_regularizedModel [FiniteDimensional ℝ E] (hσ : 0 < σ) (hL : 0 ≤ L)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hς : 0 < ς) (hθ : 0 < θ)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) :
    DetailedRestartGap (regularizedModel D p σ) univ (fun _ => univ)
      (arqpDetailedModelDec D p σ) q ς θ ε {j | 3 ≤ j} (arqpRadiusLB q ς θ L σ ε) := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨s₀, hmin, hinf⟩ := exists_eq_sInf (D := D) hσ hp
  have hlow : ∀ t, sInf (regularizedModel D p σ '' univ) ≤ regularizedModel D p σ t :=
    fun t => hinf ▸ hmin (mem_univ t)
  have hex : ∀ j ∈ Finset.Icc 1 q, ∃ η > 0, ∀ (s : E) (δ : ℕ → ℝ) (d : E), ‖s‖ < 1 →
      (∀ i, arqpRadiusLB q ς θ L σ ε i ≤ δ i ∧ δ i ≤ 1 ∧ (i ∉ {j : ℕ | 3 ≤ j} → δ i = 1)) →
      d ∈ closedBall 0 (δ j) →
      ς * θ * ε j * δ j ^ j / j ! < arqpDetailedModelDec D p σ j s d →
      (j ∉ {j : ℕ | 3 ≤ j} ∨ ς * θ * ε j * δ j ^ j / (2 * j !) ≤
        regularizedModel D p σ s - regularizedModel D p σ (s + d)) →
      η ≤ regularizedModel D p σ s - sInf (regularizedModel D p σ '' univ) := by
    intro j hj
    have hεj := hε j hj
    have hlb := arqpRadiusLB_pos (q := q) hσ hL hς hθ hε j
    by_cases h3 : 3 ≤ j
    · refine ⟨ς * θ * ε j * arqpRadiusLB q ς θ L σ ε j ^ j / (2 * j !), by positivity,
        fun s δ d _ hR _ _ hJ => ?_⟩
      have hdec := hJ.resolve_left (not_not.2 h3)
      have hδ := (hR j).1
      have : ς * θ * ε j * arqpRadiusLB q ς θ L σ ε j ^ j / (2 * j !) ≤
          ς * θ * ε j * δ j ^ j / (2 * j !) := by gcongr
      linarith [hlow (s + d)]
    · have hj2 : j ∈ Finset.Icc 1 2 := Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, by omega⟩
      obtain ⟨η, hη, H⟩ := exists_gap_low (D := D) hσ hp hj2 ((Finset.mem_Icc.1 hj).2.trans hqp)
        (τ := ς * θ * ε j / j !) (by positivity)
      refine ⟨η, hη, fun s δ d hs hR hd hlarge _ => ?_⟩
      have hδ1 : δ j = 1 := (hR j).2.2 h3
      rw [hδ1, one_pow, mul_one] at hlarge
      rw [hδ1] at hd
      refine H s hs.le (hlarge.trans_le ?_)
      exact taylorDecrement_le_taylorMeasure _ j ⟨hd, mem_univ _⟩
  choose! ηf hηf H using hex
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  refine ⟨(Finset.Icc 1 q).inf' hne ηf, (Finset.lt_inf'_iff _).2 hηf,
    fun s δ j d _ hs hj1 hjq hR hd hlarge hJ => ?_⟩
  have hj : j ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨hj1, hjq⟩
  exact (Finset.inf'_le _ hj).trans (H j hj s δ d hs hR hd.1 hlarge hJ)

/-- Let $E$ be finite-dimensional, let $\sigma > 0$, let $L \ge 0$ with $\|D_i\| \le L$ for
$i \in [2, p]$, let $1 \le q \le p$, $\varsigma > 0$ and $\theta > 0$, let $\varepsilon_j > 0$
for $j \in [1, q]$, and let $\mu_0 \in (0, 1]$. Then the detailed Step 2 for the model $m$ has
no infinite execution from the initial state (Step 2.1) with parameter $\mu_0$ and all radii
$1$: there is no sequence of states $c_0, c_1, \dots$ such that $c_0$ is this initial state and
$c_n \to c_{n+1}$ is a transition of `Optimization.ARqpDetailedTrans` for every $n$. This is
Lemma 12.2.9 of [cartis2022evaluation].

The proof applies the abstract `Optimization.detailedStep_terminates` with
`Optimization.detailedHalvingBound_regularizedModel` and
`Optimization.detailedRestartGap_regularizedModel`. -/
theorem arqpDetailedStep_terminates [FiniteDimensional ℝ E] (hσ : 0 < σ) (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hς : 0 < ς) (hθ : 0 < θ) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Ioc (0 : ℝ) 1) :
    ¬ ∃ c : ℕ → DetailedStepState E, c 0 = .findStep μ₀ (fun _ => 1) ∧
      ∀ n, ARqpDetailedTrans D p σ q ς θ ε (c n) (c (n + 1)) := by
  obtain ⟨s₀, hmin, -⟩ := exists_eq_sInf (D := D) hσ (hq.trans hqp)
  exact Optimization.detailedStep_terminates hq (mem_univ 0)
    ⟨_, by rintro _ ⟨t, -, rfl⟩; exact hmin (mem_univ t)⟩
    (fun j => ⟨arqpRadiusLB_pos hσ hL hς hθ hε j, arqpRadiusLB_le_one j⟩)
    (detailedHalvingBound_regularizedModel hσ hL hD hqp hς hθ hε)
    (detailedRestartGap_regularizedModel hσ hL hq hqp hς hθ hε) hμ₀

/-- Let $E$ be finite-dimensional, let $\sigma > 0$, $p \ge 1$ and $\varsigma \le 1$, and let
$\mu_0 \in (0, 1]$. Then every state $b$ that Algorithm 12.2.3 of [cartis2022evaluation] reaches
from the initial state with parameter $\mu_0$ and all radii $1$, and that is not a final state
`done s δ`, has a successor under `Optimization.ARqpDetailedTrans`. Thus Algorithm 12.2.3 is
well defined.

Step 2.2 can use a global minimizer of the model, and Step 2.4.1 can use an exact maximizer of
the decrement on the compact ball. The proof applies
`Optimization.DetailedStepState.exists_trans`. -/
theorem arqpDetailedStep_exists_trans [FiniteDimensional ℝ E] (hσ : 0 < σ) (hp : 1 ≤ p)
    (hς1 : ς ≤ 1) {μ₀ : ℝ} (hμ₀ : μ₀ ∈ Ioc (0 : ℝ) 1) {b : DetailedStepState E}
    (h : Relation.ReflTransGen (ARqpDetailedTrans D p σ q ς θ ε) (.findStep μ₀ fun _ => 1) b)
    (hb : ∀ s δ, b ≠ .done s δ) : ∃ b', ARqpDetailedTrans D p σ q ς θ ε b b' := by
  obtain ⟨s₀, hmin, hinf⟩ := exists_eq_sInf (D := D) hσ hp
  refine DetailedStepState.exists_trans (fun μ hμ => ⟨s₀, mem_univ _, ?_⟩)
    (fun s _ j r hr _ => ?_) hμ₀ h hb
  · rw [hinf]
    have : 0 ≤ regularizedModel D p σ 0 - regularizedModel D p σ s₀ :=
      sub_nonneg.2 (hmin (mem_univ 0))
    nlinarith [hμ.2]
  · obtain ⟨d, hd⟩ := exists_isApproxMeasureStep_taylorDecrement
      (ftaylorSeries ℝ (regularizedModel D p σ) s) j isClosed_univ (mem_univ 0) hr.le hς1
    exact ⟨d, hd.1, hd.2⟩

end Termination

/-- Let $E$ be finite-dimensional, let $P$ be the constants of ARqp, and let $p \ge 1$, $\sigma > 0$
and $x \in E$. If $(s, \delta_s)$ is an output of Algorithm 12.2.3 for the model $m$, that is
`Optimization.IsDetailedStepOutput` with the constants $\varsigma$ and $\theta$ of $P$ and the
halved orders $J = \{j \mid j \ge 3\}$, then:
* there are displacements $d^m_j$ such that $(s, \delta_s, d^m)$ satisfies the Step-2 conditions
  (12.2.27)–(12.2.29) of ARqp at the iterate $x$, which is `Optimization.ARqpStep` on the
  feasible set $E$ with the model data `Optimization.ARqpData.ofTaylor D p σ`;
* $\delta_{s,j} = 1$ for every $j \le 2$.

The iterate $x$ plays no role, because the feasible set is all of $E$. -/
theorem IsDetailedStepOutput.exists_arqpStep [FiniteDimensional ℝ E] (P : ARqpParams) {p q : ℕ}
    (hp : 1 ≤ p) {ε : ℕ → ℝ} {D : FormalMultilinearSeries ℝ E ℝ} {σ : ℝ} (hσ : 0 < σ) (x : E)
    {s : E} {δs : ℕ → ℝ}
    (h : IsDetailedStepOutput (regularizedModel D p σ) univ (fun _ => univ)
      (arqpDetailedModelDec D p σ) q P.ς P.θ ε {j | 3 ≤ j} s δs) :
    (∃ dm : ℕ → E, ARqpStep univ P q ε (ARqpData.ofTaylor D p σ) x s δs dm) ∧
      ∀ j ≤ 2, δs j = 1 := by
  obtain ⟨smin, hmin, -⟩ := exists_isMinOn_regularizedModel (D := D) (σ := σ) hσ hp
  have hb : BddBelow (regularizedModel D p σ '' univ) :=
    ⟨regularizedModel D p σ smin, by rintro _ ⟨t, -, rfl⟩; exact hmin (mem_univ t)⟩
  obtain ⟨-, -, hrad, hJ, hbranch⟩ := h.spec
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  refine ⟨?_, fun j hj => hJ j fun h3 => by have : 3 ≤ j := h3; omega⟩
  have hdm : ∀ j, ∃ d : E, (j ∈ Finset.Icc 1 q ∧ ¬ 1 ≤ ‖s‖) →
      IsApproxMeasureStep ((ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j)
        (δs j) univ P.ς d ∧
      (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d ≤
        P.ς * P.θ * ε j * δs j ^ j / j ! := fun j => by
    by_cases hj : j ∈ Finset.Icc 1 q ∧ ¬ 1 ≤ ‖s‖
    · obtain ⟨d, hd, h1, h2⟩ := (hbranch.resolve_left hj.2) j hj.1
      exact ⟨d, fun _ => ⟨⟨hd, h1⟩, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose dm hdm using hdm
  refine ⟨dm, mem_univ _, h.le_of_bddBelow (mem_univ 0) hb, fun heq => ?_,
    fun j _ => (hrad j).1, fun j _ => (hrad j).2, ?_⟩
  · rw [hU]
    exact h.isMinOn_of_eq hb heq
  · by_cases hs : 1 ≤ ‖s‖
    · exact Or.inl hs
    · refine Or.inr fun j hj => ?_
      rw [hU]
      exact hdm j ⟨hj, hs⟩

end Optimization
