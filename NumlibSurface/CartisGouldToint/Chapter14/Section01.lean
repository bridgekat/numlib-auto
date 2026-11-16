/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.LinearComp
import Numlib.Analysis.Calculus.MultivariateTaylor.VectorRemainder
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.Complexity.SlowExample.ARp
import Numlib.Optimization.Optimality.CurveConditions
import NumlibSurface.CartisGouldToint.Chapter03.Section02
import NumlibSurface.CartisGouldToint.Chapter12.Section02
import Numlib.Analysis.Calculus.AnchoredLipschitz

/-!
# Cartis, Gould and Toint, Section 14.1: Composite optimization problems

This module formalizes Section 14.1 of [cartis2022evaluation]: the composite problem
$$\min_x \; w(x) = f(x) + h(c(x)) \quad \text{(14.1.1)}$$
with smooth $f : \mathbb{R}^n \to \mathbb{R}$ and $c : \mathbb{R}^n \to \mathbb{R}^m$ and a
Lipschitz continuous, subadditive, possibly nonsmooth $h : \mathbb{R}^m \to \mathbb{R}$. The
optimality measures of the section use the generalized Taylor model $T_{w,j}(x, s) = T_{f,j}(x, s) +
h(T_{c,j}(x, s))$ of (14.1.5), its decrement $\Delta T_{w,j}(x, d) = T_{w,j}(x, 0) - T_{w,j}(x, d)$,
and the measure $\phi^\delta_{w,j}(x) = \sup_{\|d\| \le \delta} \Delta T_{w,j}(x, d)$ of (14.1.6). A
point $x$ is an $(\epsilon, \delta)$-approximate $q$-th order minimizer (14.1.9) if
$\phi^{\delta_j}_{w,j}(x) \le \epsilon_j \delta_j^j / j!$ for every $j \in [1 : q]$. Lemma 14.1.1
shows that $\phi^\delta_{w,1}$ vanishes at a minimizer when $h$ is convex, and Example 14.1.1 shows
that $\phi^1_{w,2}$ need not vanish there.

The adaptive-regularization algorithm ARqpC (Algorithm 14.1.1, with the detailed Step 2 of Algorithm
14.1.2) computes steps from the model $\hat m_k(s) = T_{f,p}(x_k, s) + h(T_{c,p}(x_k, s)) + \sigma_k
\|s\|^{p+1} / (p+1)!$ of (14.1.11). Lemmas 14.1.2–14.1.9 bound its radii, regularization weights,
steps and decreases. Theorem 14.1.10 shows that ARqpC finds an approximate minimizer after
$O(\epsilon_1^{-(p+1)/p})$ evaluations if $q = 1$ and $h$ is convex, and after
$O(\max_j \epsilon_j^{-(j+1)})$ evaluations in general. Corollary 14.1.11 shows that the first bound
is sharp. The proofs specialize the backbone modules
`Numlib.Optimization.ModelBased.HighOrder.ARqpC` and
`Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity`.

## Main definitions

* Assumption c.D1pL, `CartisGouldToint.Chapter14.AssumptionCD1pL`: every component of $c$ is $p$
  times continuously differentiable with Lipschitz continuous derivatives of orders $1$ to $p$.
* Assumption h.L, `CartisGouldToint.Chapter14.AssumptionHLip`: $h$ is Lipschitz continuous with
  constant $L_{h,0}$.
* Assumption h.S0, `CartisGouldToint.Chapter14.AssumptionHS0`: $h$ is subadditive and $h(0) = 0$.
* Assumption w.Bb, `CartisGouldToint.Chapter14.AssumptionWBb`: $w$ is bounded below on the feasible
  set.
* Equations (14.1.3) and (14.1.27), `CartisGouldToint.Chapter14.compositeLipschitzW`,
  `CartisGouldToint.Chapter14.compositeLipschitzWp`: the constants $L_w$ and $L_{w,p}$.
* Equation (14.2.8), `CartisGouldToint.Chapter14.compositeSublevel`: the sublevel set of $w$ at
  $x_0$ in the feasible set.
* Assumption f.D1pLaB.X of Section 14.2.1, `CartisGouldToint.Chapter14.AnchoredCompositeBounds`: the
  anchored smoothness of the data $f$ and $c$ that the analysis uses.
* Algorithm 14.1.1, Step 0, `CartisGouldToint.Chapter14.ARqpCParams`: the constants of ARqpC.
* Algorithm 14.1.2, `CartisGouldToint.Chapter14.algorithm_14_1_2`: the outputs of the detailed
  Step 2.
* Algorithm 14.1.1, `CartisGouldToint.Chapter14.algorithm_14_1_1`: a run of ARqpC.

## Main results

* Lemma 14.1.1, `CartisGouldToint.Chapter14.lemma_14_1_1`: for convex $h$,
  $\phi^\delta_{w,1}(x_\star) = 0$ at a global minimizer $x_\star$ of $w$.
* Example 14.1.1, `CartisGouldToint.Chapter14.example_14_1_1`: a global minimizer with
  $\phi^1_{w,2}(x_\star) > 0$.
* Lemma 14.1.2, `CartisGouldToint.Chapter14.lemma_14_1_2`,
  `CartisGouldToint.Chapter14.lemma_14_1_2_of_jet`: a large model decrement along a short
  displacement gives a decrease of the model.
* Lemma 14.1.3, `CartisGouldToint.Chapter14.lemma_14_1_3`,
  `CartisGouldToint.Chapter14.lemma_14_1_3_of_jet`: Algorithm 14.1.2 has an output whose radii are
  bounded below.
* Algorithm 14.1.1, `CartisGouldToint.Chapter14.exists_algorithm_14_1_1`,
  `CartisGouldToint.Chapter14.exists_algorithm_14_1_1_of_hLip`: runs of ARqpC exist from every
  feasible starting point.
* Lemma 14.1.4, `CartisGouldToint.Chapter14.lemma_14_1_4`,
  `CartisGouldToint.Chapter14.lemma_14_1_4_ii`: termination in Step 2 gives an approximate
  minimizer, and does not occur if $q = 1$ and $h$ and $X$ are convex.
* Lemma 14.1.5, `CartisGouldToint.Chapter14.lemma_14_1_5`: the Taylor decrease of a step is at least
  $\sigma_k \|s_k\|^{p+1} / (p+1)!$.
* Lemma 14.1.6, `CartisGouldToint.Chapter14.lemma_14_1_6`,
  `CartisGouldToint.Chapter14.lemma_14_1_6_anchored`,
  `CartisGouldToint.Chapter14.sigma_le_arqpcSigmaMax_anchored`: the regularization weights are
  bounded by $\sigma_{\max}$.
* Lemma 14.1.7, `CartisGouldToint.Chapter14.lemma_14_1_7`,
  `CartisGouldToint.Chapter14.lemma_14_1_7_anchored`: an inequality between the radii and the step
  after a successful iteration.
* Lemma 14.1.8, `CartisGouldToint.Chapter14.lemma_14_1_8`,
  `CartisGouldToint.Chapter14.lemma_14_1_8_anchored`: a lower bound on the step after a successful
  iteration.
* Lemma 14.1.3 for every step of a run,
  `CartisGouldToint.Chapter14.algorithm_14_1_1.kappaDeltaMin_mul_le_radius`,
  `CartisGouldToint.Chapter14.algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`: the Step-2
  radii of every run are at least $\kappa_{\delta,\min} \epsilon_j$, so the radius policy (14.1.28)
  holds.
* Lemma 14.1.9, `CartisGouldToint.Chapter14.lemma_14_1_9`,
  `CartisGouldToint.Chapter14.lemma_14_1_9_anchored`: lower bounds on the decreases of the model and
  of $w$.
* Theorem 14.1.10(1), `CartisGouldToint.Chapter14.theorem_14_1_10_i`: for $q = 1$ and convex $h$,
  ARqpC needs $O(\epsilon_1^{-(p+1)/p})$ evaluations.
* Theorem 14.1.10(2), `CartisGouldToint.Chapter14.theorem_14_1_10_ii`,
  `CartisGouldToint.Chapter14.theorem_14_1_10_ii_anchored`: ARqpC needs
  $O(\max_j \epsilon_j^{-(j+1)})$ evaluations.
* Corollary 14.1.11, `CartisGouldToint.Chapter14.corollary_14_1_11`: the bound of Theorem 14.1.10(1)
  is sharp in order.

## Proof outline

Lemma 14.1.2 compares the model decrements with the decrease of the model, with the bounds (14.1.2)
on the derivatives. With it, Lemma 14.1.3 shows that Algorithm 14.1.2 stops halving a radius before
it falls below $\kappa_\delta(\sigma) \epsilon_j$. The anchored Lipschitz condition at the top order
bounds the regularization weights (Lemma 14.1.6). After a successful iteration at which the next
Step-1 test fails, the model test (14.1.13) gives a lower bound on the step (Lemmas 14.1.7 and
14.1.8), and Lemma 14.1.5 turns it into a lower bound on the decrease of $w$ (Lemma 14.1.9). Theorem
14.1.10 bounds the number of successful iterations with $w_{\mathrm{low}}$, and the number of
unsuccessful iterations with the bound on $\sigma_k$. Corollary 14.1.11 lifts the slow example of
Theorem 12.2.15 to $w = |c|$.

## Conventions

* The space $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`.
* The space $\mathbb{R}^m$ is `EuclideanSpace ℝ (Fin m)`.
* The index set $[1 : p]$ is `Finset.Icc 1 p`.
* Assumption f.D1pL is `CartisGouldToint.Chapter12.AssumptionD1pL f p Lf`, with constants
  $L_{f,j} \ge 1$. The constants $L_{c,j}$ of c.D1pL are `Lc j`, and the constant $L_{h,0}$ of h.L
  is `Lh`.
* The maxima $L_f$ and $L_c$ of (14.1.3) are `Optimization.finMax 1 Lf p` and
  `Optimization.finMax 0 Lc p`: the maxima of the constants of orders $1$ to $p$ together with $1$
  and with $0$. Under f.D1pL and c.D1pL they are the maxima of the source.
* The Taylor models are built from the jets `ftaylorSeries ℝ f x` and `ftaylorSeries ℝ c x`. The
  decrement $\Delta T_{w,j}$ and the measure $\phi^\delta_{w,j}$ are
  `Optimization.compositeTaylorDecrement` and `Optimization.compositeTaylorMeasure`. The model
  $\hat m_k$ and its decrements (14.1.14) are `Optimization.compositeRegularizedModel` and
  `Optimization.compositeModelDecrement`, and (14.1.9) is `Optimization.IsEpsDeltaApproxComposite`.

## Implementation notes

* A closed feasible set $X$ with $x_0 \in X$ is carried throughout, and the measures are taken over
  the feasible displacements $\{d : x + d \in X\}$. With $X = \mathbb{R}^n$ the algorithm is ARqpC;
  with a general $X$ it is the variant ARqpC-SC of Section 14.2.
* A run of ARqpC is the backbone run `Optimization.IsARqpCRun`: the ARqp run
  `Optimization.IsARqpRun` for $w$ with the composite model data `Optimization.arqpcData`, whose
  Step 2 is the detailed Step 2 `Optimization.IsARqpCDetailedStep`.
* The analysis (Lemmas 14.1.3–14.1.9, Theorem 14.1.10) is the backbone
  `Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity`, in normed spaces and under the
  anchored condition `LipschitzDerivsAnchored` on $f$ and $c$ at the top order. The results with the
  suffix `_anchored` state it under `CartisGouldToint.Chapter14.AnchoredCompositeBounds` with the
  sublevel set `CartisGouldToint.Chapter14.compositeSublevel f c h X x₀` as anchor set; this set
  contains every iterate (`CartisGouldToint.Chapter14.algorithm_14_1_1.mem_compositeSublevel`). The
  global versions are their instances with $X_0 = \mathbb{R}^n$. This is the remark of the source
  after (14.2.10) that the analysis uses only f.D1pLaB.X.
* Trial points need only lie in $X \subseteq X_0$, because Taylor's theorem is applied with the
  Lipschitz condition anchored at the iterate
  (`Optimization.abs_sub_compositeTaylor_le_of_lipschitzAnchored`,
  `Optimization.radius_inequality_of_compositeTaylorMeasure_gt_anchored`).
* The componentwise constants of c.D1pL give the operator-norm constants $\sqrt{m} L_{c,j}$ of the
  derivatives of $c$ (`CartisGouldToint.Chapter14.AssumptionCD1pL.lipschitz`,
  `CartisGouldToint.Chapter14.compositeLipschitzWp_eq`,
  `CartisGouldToint.Chapter14.compositeLipschitzW_eq`). The constants of the source are those of the
  backbone (`CartisGouldToint.Chapter14.kappaDeltaMin_eq`,
  `CartisGouldToint.Chapter14.stepBound1_eq`, `CartisGouldToint.Chapter14.stepBound2_eq`,
  `CartisGouldToint.Chapter14.kappaDm1_eq`, `CartisGouldToint.Chapter14.kappaDm2_eq`).
* Lemmas 14.1.2 and 14.1.3 are also stated at a point with given bounds on the derivatives
  (`CartisGouldToint.Chapter14.lemma_14_1_2_of_jet`,
  `CartisGouldToint.Chapter14.lemma_14_1_3_of_jet`). With them, runs exist for all $f$ and $c$ under
  h.L and h.S0 (`CartisGouldToint.Chapter14.exists_algorithm_14_1_1_of_hLip`).
* For $q = 1$ and convex $h$ and $X$, every global minimizer of the model is an output of Algorithm
  14.1.2 (`CartisGouldToint.Chapter14.algorithm_14_1_2_of_isMinOn`). The proof of Corollary 14.1.11
  uses this.

## Deviations from the source

* **Assumption h.S0** (typo). The source says that $h$ is subadditive "in $\mathbb{R}$"; the space
  is $\mathbb{R}^m$. See `CartisGouldToint.Chapter14.AssumptionHS0`.
* **Equation (14.1.2)** (correction). With the componentwise constants of c.D1pL as printed, the
  bound is $\|\nabla^j c(x)\| \le \sqrt{m} L_{c,j-1}$; the source omits the factor $\sqrt{m}$. See
  `CartisGouldToint.Chapter14.AssumptionCD1pL.norm_iteratedFDeriv_le`.
* **Lemma 14.1.1** (generalization). The hypothesis h.S0 is not used. See
  `CartisGouldToint.Chapter14.lemma_14_1_1`.
* **Example 14.1.1** (generalization). The measure $\phi^\delta_{w,2}(0)$ vanishes for every
  $\delta \in (0, 3/5]$, where the source says "smaller than $\frac12$, say". See
  `CartisGouldToint.Chapter14.example_14_1_1`.
* **Lemma 14.1.3** (generalization). The lower bound on the radii also holds for $j = 1$ when $h$ or
  $X$ is not convex, and the analysis needs this case; the source states it for $j \in [2 : q]$. See
  `CartisGouldToint.Chapter14.lemma_14_1_3`.
* **Lemmas 14.1.4 and 14.1.6** (generalization). Only the smoothness and Lipschitz properties that
  the proofs use are assumed. See `CartisGouldToint.Chapter14.lemma_14_1_4`,
  `CartisGouldToint.Chapter14.lemma_14_1_6`.
* **Lemma 14.1.7** (correction). The factor $(1 - \theta)$ is $(\varsigma - \theta)$, the term in
  $\|s_k\|^{p+1}$ has a factor $2$, and the inequality is strict. See
  `CartisGouldToint.Chapter14.lemma_14_1_7`.
* **Proof of Lemma 14.1.7, (B.14.6)** (typo). Inside the sum over $\ell$, the printed $(p - j + 1)!$
  and $\|s_k\|^{p-j+1}$ are $(p - \ell + 1)!$ and $\|s_k\|^{p-\ell+1}$. See
  `CartisGouldToint.Chapter14.lemma_14_1_7`.
* **Lemma 14.1.7 and Theorem 14.1.10(1)** (generalization). The hypothesis h.S0 is not used. See
  `CartisGouldToint.Chapter14.lemma_14_1_7`, `CartisGouldToint.Chapter14.theorem_14_1_10_i`.
* **Lemma 14.1.8** (correction). The second case of (14.1.31) needs the factor
  $\epsilon_j^{(j+1)/(p+1)}$, and $(1 - \theta)$ is $(\varsigma - \theta)$ with
  $\theta < \varsigma$. See `CartisGouldToint.Chapter14.lemma_14_1_8`.
* **Lemma 14.1.9** (correction). The decreases hold at successful iterations that are not followed
  by termination, under f.D1pL, c.D1pL and h.L, with $(\varsigma - \theta)$ for $(1 - \theta)$. See
  `CartisGouldToint.Chapter14.lemma_14_1_9`.
* **Lemma 14.1.9** (typo). The source writes $f$ and $L_{f,p}$ for $w$ and $L_{w,p}$. See
  `CartisGouldToint.Chapter14.lemma_14_1_9`.
* **Lemma 14.1.9 and Theorem 14.1.10(2)** (generalization). The decrease is bounded with
  $\epsilon_j^{j+1}$ for the order $j$ that Lemma 14.1.8 gives, and $\min_j \epsilon_j^{j+1}$ can be
  any positive lower bound $m_\epsilon$. Theorem 14.1.10(2) also holds when $h$ is convex and
  $q = 1$. See `CartisGouldToint.Chapter14.lemma_14_1_9`,
  `CartisGouldToint.Chapter14.theorem_14_1_10_ii`.
* **Theorem 14.1.10** (correction). In the constants, $(1 - \theta)$ is $(\varsigma - \theta)$ with
  $\theta < \varsigma$. See `CartisGouldToint.Chapter14.theorem_14_1_10_i`,
  `CartisGouldToint.Chapter14.theorem_14_1_10_ii`.
* **Theorem 14.1.10(2)** (typo). The factor $3j!$ in the constant is $3q!$. See
  `CartisGouldToint.Chapter14.theorem_14_1_10_ii`.
* **Theorem 14.1.10** (reading). The radius policies that the source assumes are proved for every
  run; for part (1) this needs the initial radius $\delta_{0,1} = 1$. See
  `CartisGouldToint.Chapter14.theorem_14_1_10_i`,
  `CartisGouldToint.Chapter14.algorithm_14_1_1.radius_policy`.
* **Corollary 14.1.11** (generalization). The statement holds for every $\sigma_0$ and every
  $\epsilon \in (0, 1]$; the source fixes $\sigma_0 = p!$ and takes $\epsilon \le \frac12$. See
  `CartisGouldToint.Chapter14.corollary_14_1_11`.

## Not formalized

All numbered items of Section 14.1 are formalized.
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### Assumptions and constants -/

/-- **Assumption c.D1pL** of [cartis2022evaluation], Section 14.1.1. Let
$c : \mathbb{R}^n \to \mathbb{R}^m$, $p \in \mathbb{N}$ and $L_{c,j} \in \mathbb{R}$. The
assumption holds if every component $c_i$ of $c$ is $p$ times continuously differentiable,
$L_{c,j} \ge 0$ for $j \in [1 : p]$, and for every component $c_i$, every $j \in [1 : p]$ and
all $x, y \in \mathbb{R}^n$
$$\|\nabla^j c_i(x) - \nabla^j c_i(y)\| \le L_{c,j} \|x - y\|.$$

The condition on each component is the anchored assumption `LipschitzDerivsAnchored` of orders
$[1 : p]$ with $C = A = \mathbb{R}^n$. The form of the source is
`CartisGouldToint.Chapter14.AssumptionCD1pL.contDiff`,
`CartisGouldToint.Chapter14.AssumptionCD1pL.lipschitz_component` and
`CartisGouldToint.Chapter14.AssumptionCD1pL.of_lipschitz_component`. The constants are
componentwise, as printed; the derivatives of the vector function $c$ then have the Lipschitz
constants $\sqrt{m} L_{c,j}$ (`CartisGouldToint.Chapter14.AssumptionCD1pL.lipschitz`). -/
abbrev AssumptionCD1pL (c : ℝⁿ → ℝᵐ) (p : ℕ) (Lc : ℕ → ℝ) : Prop :=
  (∀ i, LipschitzDerivsAnchored (fun x => c x i) univ univ 1 p Lc) ∧
    ∀ j ∈ Finset.Icc 1 p, 0 ≤ Lc j

namespace AssumptionCD1pL

variable {c : ℝⁿ → ℝᵐ} {p : ℕ} {Lc : ℕ → ℝ}

/-- Under c.D1pL, the map $c$ is $p$ times continuously differentiable. -/
theorem contDiff (hc : AssumptionCD1pL c p Lc) : ContDiff ℝ p c :=
  contDiff_piLp' 2 fun i => (hc.1 i).contDiff

/-- The constants of c.D1pL satisfy $L_{c,j} \ge 0$ for $j \in [1 : p]$. -/
theorem nonneg (hc : AssumptionCD1pL c p Lc) : ∀ j ∈ Finset.Icc 1 p, 0 ≤ Lc j :=
  hc.2

/-- Under c.D1pL, for every component $c_i$ and every $j \in [1 : p]$, the $j$-th derivative of
$c_i$ is Lipschitz continuous on $\mathbb{R}^n$ with constant $L_{c,j}$. -/
theorem lipschitz_component (hc : AssumptionCD1pL c p Lc) :
    ∀ i, ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzOn (fun x => c x i) j (Lc j) univ :=
  fun i _ hj => (hc.1 i).lipschitzOn hj

/-- If $c$ is $p$ times continuously differentiable, $L_{c,j} \ge 0$ for $j \in [1 : p]$, and the
$j$-th derivative of every component $c_i$ is Lipschitz continuous on $\mathbb{R}^n$ with
constant $L_{c,j}$ for every $j \in [1 : p]$, then c.D1pL holds. -/
theorem of_lipschitz_component (hc : ContDiff ℝ p c) (h0 : ∀ j ∈ Finset.Icc 1 p, 0 ≤ Lc j)
    (hL : ∀ i, ∀ j ∈ Finset.Icc 1 p,
      IteratedFDerivLipschitzOn (fun x => c x i) j (Lc j) univ) :
    AssumptionCD1pL c p Lc :=
  ⟨fun i => .of_contDiff ((contDiff_piLp 2).1 hc i) (hL i) univ, h0⟩

end AssumptionCD1pL

/-- **Assumption h.L** of [cartis2022evaluation], Section 14.1.1. The function
$h : \mathbb{R}^m \to \mathbb{R}$ is Lipschitz continuous with a constant $L_{h,0} \ge 0$:
$$|h(a) - h(b)| \le L_{h,0} \|a - b\| \quad \text{for all } a, b \in \mathbb{R}^m.$$

The assumption is the backbone `Optimization.HasLipschitzConst h Lh`, with the real constant
$L_{h,0}$ = `Lh`. -/
abbrev AssumptionHLip (h : ℝᵐ → ℝ) (Lh : ℝ) : Prop := Optimization.HasLipschitzConst h Lh

/-- Assumption h.L holds if and only if $L_{h,0} \ge 0$ and $|h(a) - h(b)| \le L_{h,0} \|a - b\|$
for all $a, b \in \mathbb{R}^m$. -/
theorem assumptionHLip_iff {h : ℝᵐ → ℝ} {Lh : ℝ} :
    AssumptionHLip h Lh ↔ 0 ≤ Lh ∧ ∀ a b, |h a - h b| ≤ Lh * ‖a - b‖ :=
  ⟨fun hh => ⟨hh.nonneg, hh.abs_sub_le⟩, fun hh => ⟨hh.1, hh.2⟩⟩

/-- **Assumption h.S0** of [cartis2022evaluation], Section 14.1.1. The function
$h : \mathbb{R}^m \to \mathbb{R}$ is subadditive, $h(a + b) \le h(a) + h(b)$ for all
$a, b \in \mathbb{R}^m$, and $h(0) = 0$.

**Typo.** The source says that $h$ is subadditive "in $\mathbb{R}$". The space is
$\mathbb{R}^m$, the domain of $h$.

Subadditivity is `Optimization.IsSubadditive`. -/
def AssumptionHS0 (h : ℝᵐ → ℝ) : Prop := Optimization.IsSubadditive h ∧ h 0 = 0

/-- **Assumption w.Bb** of [cartis2022evaluation], Section 14.1.1. Let $X \subseteq \mathbb{R}^n$
and $w_{\mathrm{low}} \in \mathbb{R}$. The composite objective $w = f + h \circ c$ is bounded
below by $w_{\mathrm{low}}$ on $X$: $w(x) \ge w_{\mathrm{low}}$ for every $x \in X$.

In Section 14.1 the feasible set is $X = \mathbb{R}^n$. The form with a general $X$ is the one
that Section 14.2 uses. -/
def AssumptionWBb (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (wlow : ℝ) : Prop :=
  ∀ x ∈ X, wlow ≤ f x + h (c x)

/-- Under h.L, the function $h$ has the Lipschitz constant $L_{h,0}$ in the sense of
`Optimization.HasLipschitzConst`. -/
theorem AssumptionHLip.hasLipschitzConst {h : ℝᵐ → ℝ} {Lh : ℝ} (hh : AssumptionHLip h Lh) :
    Optimization.HasLipschitzConst h Lh := hh

/-- Under h.L and h.S0, $|h(a)| \le L_{h,0} \|a\|$ for every $a \in \mathbb{R}^m$. This is (14.1.4)
of [cartis2022evaluation]. -/
theorem AssumptionHS0.abs_le {h : ℝᵐ → ℝ} {Lh : ℝ} (hS : AssumptionHS0 h)
    (hL : AssumptionHLip h Lh) (a : ℝᵐ) : |h a| ≤ Lh * ‖a‖ := by
  simpa [hS.2] using hL.abs_sub_le a 0

/-- Under c.D1pL, for every $j \in [1 : p]$ the $j$-th derivative of $c$ is Lipschitz continuous on
$\mathbb{R}^n$ with constant $\sqrt{m} L_{c,j}$, in the operator norm. -/
theorem AssumptionCD1pL.lipschitz {c : ℝⁿ → ℝᵐ} {p : ℕ} {Lc : ℕ → ℝ}
    (hc : AssumptionCD1pL c p Lc) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) :
    IteratedFDerivLipschitzOn c j (Real.sqrt m * Lc j) univ :=
  iteratedFDerivLipschitzOn_of_forall_component
    (fun _ _ => hc.contDiff.contDiffAt.of_le (by exact_mod_cast (Finset.mem_Icc.1 hj).2))
    fun i => hc.lipschitz_component i j hj

/-- **Equation (14.1.2)** of [cartis2022evaluation]. Under c.D1pL, for every $x \in \mathbb{R}^n$
and every $j \in [2 : p]$,
$$\|\nabla^j c(x)\| \le \sqrt{m} \, L_{c,j-1}.$$

**Correction.** The source prints the bound $L_{c,j-1}$, without the factor $\sqrt{m}$. With the
componentwise constants of c.D1pL as printed, this bound fails: if all $m$ components of $c$ are
$x_1^2$, then $L_{c,1} = 2$ but $\|\nabla^2 c(x)\| = 2\sqrt{m}$. -/
theorem AssumptionCD1pL.norm_iteratedFDeriv_le {c : ℝⁿ → ℝᵐ} {p : ℕ} {Lc : ℕ → ℝ}
    (hc : AssumptionCD1pL c p Lc) {j : ℕ} (hj : j ∈ Finset.Icc 2 p) (x : ℝⁿ) :
    ‖iteratedFDeriv ℝ j c x‖ ≤ Real.sqrt m * Lc (j - 1) := by
  obtain ⟨hj2, hjp⟩ := Finset.mem_Icc.1 hj
  have hj' : j - 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have h0 : 0 ≤ Real.sqrt m * Lc (j - 1) := by
    have := hc.nonneg (j - 1) hj'
    positivity
  have := norm_iteratedFDeriv_succ_le_of_lipschitzOn isOpen_univ h0 (hc.lipschitz hj')
    (mem_univ x)
  rwa [show j - 1 + 1 = j by omega] at this

/-- **Equation (14.1.3)** of [cartis2022evaluation]. The constant
$$L_w = L_f + \sqrt{m} \, L_{h,0} L_c,$$
where $L_f = \max(1, \max_{j \in [1 : p]} L_{f,j})$ and
$L_c = \max(0, \max_{j \in [1 : p]} L_{c,j})$.

The factor $\sqrt{m}$ is the one of (14.1.2) for the componentwise constants of c.D1pL. Under
f.D1pL and c.D1pL, $L_f$ and $L_c$ are the maxima $\max_j L_{f,j}$ and $\max_j L_{c,j}$ of the
source. They are `Optimization.finMax 1 Lf p` and `Optimization.finMax 0 Lc p`. -/
noncomputable def compositeLipschitzW (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  Optimization.finMax 1 Lf p + Real.sqrt m * Lh * Optimization.finMax 0 Lc p

/-- The constant $L_{w,p} = L_{f,p} + \sqrt{m} \, L_{h,0} L_{c,p}$ of (14.1.27) of
[cartis2022evaluation]. -/
noncomputable def compositeLipschitzWp (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  Lf p + Real.sqrt m * Lh * Lc p

/-- The constant $L_{w,p}$ equals $L_{f,p} + L_{h,0} (\sqrt{m} L_{c,p})$. This is the form that the
backbone analysis (`Optimization.IsARqpRun.sigma_le_of_compositeAnchored`) uses, with the
operator-norm Lipschitz constant $\sqrt{m} L_{c,p}$ of $\nabla^p c$. -/
theorem compositeLipschitzWp_eq {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} :
    compositeLipschitzWp Lf Lc Lh p m = Lf p + Lh * (Real.sqrt m * Lc p) := by
  unfold compositeLipschitzWp; ring

/-- The constant $L_w$ equals $L_f + L_{h,0} (\sqrt{m} L_c)$, the form of the constant in the
backbone analysis. -/
theorem compositeLipschitzW_eq {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} :
    compositeLipschitzW Lf Lc Lh p m =
      Optimization.finMax 1 Lf p + Lh * (Real.sqrt m * Optimization.finMax 0 Lc p) := by
  unfold compositeLipschitzW; ring

/-- If $p \ge 1$ and $L_{h,0} \ge 0$, then $L_{w,p} \le L_w$. -/
theorem compositeLipschitzWp_le {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} (hp : 1 ≤ p) (hLh : 0 ≤ Lh) :
    compositeLipschitzWp Lf Lc Lh p m ≤ compositeLipschitzW Lf Lc Lh p m := by
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hp, le_rfl⟩
  unfold compositeLipschitzWp compositeLipschitzW
  have := Optimization.le_finMax (b := 0) (u := Lc) hp'
  gcongr
  exact Optimization.le_finMax hp'

/-- If $L_{h,0} \ge 0$, then the constant $L_w$ of (14.1.3) of [cartis2022evaluation] satisfies
$L_w \ge 1$.

This holds for all constants $L_{f,j}$ and $L_{c,j}$, because the maxima $L_f$ and $L_c$ include
$1$ and $0$. -/
theorem one_le_compositeLipschitzW_of {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} (hLh : 0 ≤ Lh) :
    1 ≤ compositeLipschitzW Lf Lc Lh p m := by
  unfold compositeLipschitzW
  have h1 : (1 : ℝ) ≤ Optimization.finMax 1 Lf p := Optimization.le_finMax_left
  have h2 : (0 : ℝ) ≤ Optimization.finMax 0 Lc p := Optimization.le_finMax_left
  have : 0 ≤ Real.sqrt m * Lh * Optimization.finMax 0 Lc p := by positivity
  linarith

/-! ### Anchored assumptions -/

/-- **Equation (14.2.8)** of [cartis2022evaluation], for the composite objective. Let
$X \subseteq \mathbb{R}^n$ and $x_0 \in \mathbb{R}^n$. The **sublevel set** of
$w = f + h \circ c$ at $x_0$ in $X$ is
$$\{y \in X : w(y) \le w(x_0)\}.$$

The source writes $\mathcal{L}_f(x_0)$ for the objective $f$ of Section 14.2. Here the set is
used for $w$. -/
def compositeSublevel (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (x₀ : ℝⁿ) :
    Set ℝⁿ :=
  {y ∈ X | f y + h (c y) ≤ f x₀ + h (c x₀)}

/-- A point $y$ lies in the sublevel set of $w$ at $x_0$ in $X$ if and only if $y \in X$ and
$f(y) + h(c(y)) \le f(x_0) + h(c(x_0))$. -/
theorem mem_compositeSublevel {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ}
    {x₀ y : ℝⁿ} :
    y ∈ compositeSublevel f c h X x₀ ↔ y ∈ X ∧ f y + h (c y) ≤ f x₀ + h (c x₀) := Iff.rfl

/-- **Assumption f.D1pLaB.X** of [cartis2022evaluation], Section 14.2.1, in the form that the
analysis of ARqpC uses. Let $X_0, A \subseteq \mathbb{R}^n$, $p \in \mathbb{N}$ and constants
$L_{f,j}, L_{c,j} \in \mathbb{R}$. The data $f$ and $c$ satisfy the **anchored composite
bounds** if $X_0$ is open and convex, $A \subseteq X_0$, $f$ and $c$ are $p$ times continuously
differentiable on $X_0$, $L_{f,p} \ge 1$, $L_{c,p} \ge 0$, and for all $x \in A$, $y \in X_0$
and $i \in [2 : p]$
$$\|\nabla^p f(x) - \nabla^p f(y)\| \le L_{f,p} \|x - y\|, \qquad
  \|\nabla^p c(x) - \nabla^p c(y)\| \le \sqrt{m} \, L_{c,p} \|x - y\|,$$
$$\|\nabla^i f(x)\| \le L_{f,i-1}, \qquad \|\nabla^i c(x)\| \le \sqrt{m} \, L_{c,i-1}.$$
The first line is the anchored Lipschitz condition (14.2.9) at the top order. The second line is
the bound (14.1.2) on the derivatives at the anchors, that is, (14.2.10).

In applications, $A$ is the sublevel set `CartisGouldToint.Chapter14.compositeSublevel f c h X
x₀`, which contains every iterate. Under the global assumptions f.D1pL and c.D1pL, the bounds
hold with $X_0 = \mathbb{R}^n$ and every anchor set
(`CartisGouldToint.Chapter14.AnchoredCompositeBounds.of_global`). The assumption f.D1pLaB.X of
the source, with anchored Lipschitz constants $L_{f,j}$ in (14.2.9) and bounds $B_{f,j}$ in
(14.2.10) on $A = \mathcal{L}_f(x_0)$, gives the bounds with the constants
$\max(L_{f,i}, B_{f,i+1})$: the bound of order $i$ enters as the constant of order $i - 1$. -/
structure AnchoredCompositeBounds (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X₀ A : Set ℝⁿ) (p : ℕ)
    (Lf Lc : ℕ → ℝ) : Prop where
  /-- The set $X_0$ is open. -/
  isOpen : IsOpen X₀
  /-- The set $X_0$ is convex. -/
  convex : Convex ℝ X₀
  /-- The anchor set satisfies $A \subseteq X_0$. -/
  subset : A ⊆ X₀
  /-- The function $f$ is $p$ times continuously differentiable on $X_0$. -/
  contDiffOn_f : ContDiffOn ℝ p f X₀
  /-- The map $c$ is $p$ times continuously differentiable on $X_0$. -/
  contDiffOn_c : ContDiffOn ℝ p c X₀
  /-- The top-order constant of $f$ satisfies $L_{f,p} \ge 1$. -/
  one_le : 1 ≤ Lf p
  /-- The top-order constant of $c$ satisfies $L_{c,p} \ge 0$. -/
  nonneg : 0 ≤ Lc p
  /-- The $p$-th derivative of $f$ satisfies $\|\nabla^p f(x) - \nabla^p f(y)\| \le L_{f,p} \|x -
  y\|$ for all $x \in A$ and $y \in X_0$. -/
  lipschitz_f : IteratedFDerivLipschitzAnchored f p (Lf p) A X₀
  /-- The $p$-th derivative of $c$ satisfies $\|\nabla^p c(x) - \nabla^p c(y)\| \le \sqrt{m} \,
  L_{c,p} \|x - y\|$ for all $x \in A$ and $y \in X_0$. -/
  lipschitz_c : IteratedFDerivLipschitzAnchored c p (Real.sqrt m * Lc p) A X₀
  /-- The derivatives of $f$ satisfy $\|\nabla^i f(x)\| \le L_{f,i-1}$ for all $i \in [2 : p]$ and
  $x \in A$. -/
  norm_f : ∀ i ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ i f x‖ ≤ Lf (i - 1)
  /-- The derivatives of $c$ satisfy $\|\nabla^i c(x)\| \le \sqrt{m} \, L_{c,i-1}$ for all
  $i \in [2 : p]$ and $x \in A$. -/
  norm_c : ∀ i ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ i c x‖ ≤ Real.sqrt m * Lc (i - 1)

namespace AnchoredCompositeBounds

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X₀ A : Set ℝⁿ} {p : ℕ} {Lf Lc : ℕ → ℝ}

/-- **Remark after (14.2.10)** of [cartis2022evaluation]. Let $p \ge 1$. If $f$ satisfies f.D1pL
with constants $L_{f,j}$ and $c$ satisfies c.D1pL with constants $L_{c,j}$, then the anchored
composite bounds hold with $X_0 = \mathbb{R}^n$ and every anchor set $A \subseteq \mathbb{R}^n$. -/
theorem of_global (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hp : 1 ≤ p) (A : Set ℝⁿ) : AnchoredCompositeBounds f c univ A p Lf Lc where
  isOpen := isOpen_univ
  convex := convex_univ
  subset := subset_univ A
  contDiffOn_f := hf.contDiff.contDiffOn
  contDiffOn_c := hc.contDiff.contDiffOn
  one_le := hf.one_le p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)
  nonneg := hc.nonneg p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)
  lipschitz_f := (hf.lipschitz p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)).anchored (subset_univ A)
  lipschitz_c := (hc.lipschitz (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)).anchored (subset_univ A)
  norm_f _ hi x _ := hf.norm_iteratedFDeriv_le hi x
  norm_c _ hi x _ := hc.norm_iteratedFDeriv_le hi x

/-- If the anchored composite bounds hold for an anchor set $A$, then they hold for every anchor set
$A' \subseteq A$. -/
theorem mono (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) {A' : Set ℝⁿ} (h : A' ⊆ A) :
    AnchoredCompositeBounds f c X₀ A' p Lf Lc where
  isOpen := hA.isOpen
  convex := hA.convex
  subset := h.trans hA.subset
  contDiffOn_f := hA.contDiffOn_f
  contDiffOn_c := hA.contDiffOn_c
  one_le := hA.one_le
  nonneg := hA.nonneg
  lipschitz_f := hA.lipschitz_f.mono_left h
  lipschitz_c := hA.lipschitz_c.mono_left h
  norm_f i hi x hx := hA.norm_f i hi x (h hx)
  norm_c i hi x hx := hA.norm_c i hi x (h hx)

/-- Under the anchored composite bounds, $f$ is $p$ times continuously differentiable at every point
of $X_0$. -/
theorem contDiffAt_f (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) {y : ℝⁿ} (hy : y ∈ X₀) :
    ContDiffAt ℝ p f y :=
  hA.contDiffOn_f.contDiffAt (hA.isOpen.mem_nhds hy)

/-- Under the anchored composite bounds, $c$ is $p$ times continuously differentiable at every point
of $X_0$. -/
theorem contDiffAt_c (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) {y : ℝⁿ} (hy : y ∈ X₀) :
    ContDiffAt ℝ p c y :=
  hA.contDiffOn_c.contDiffAt (hA.isOpen.mem_nhds hy)

/-- Under the anchored composite bounds, at every anchor $x \in A$ and for every $i \in [2 : p]$,
$\|\nabla^i f(x)\| \le L_f$ and $\|\nabla^i c(x)\| \le \sqrt{m} L_c$, with the maxima $L_f$ and
$L_c$ of (14.1.3). -/
theorem jet_bounds (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) {x : ℝⁿ} (hx : x ∈ A) :
    (∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ Optimization.finMax 1 Lf p) ∧
    (∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ c x i‖ ≤ Real.sqrt m * Optimization.finMax 0 Lc p) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hi' : i - 1 ∈ Finset.Icc 1 p := by
      have := Finset.mem_Icc.1 hi; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    exact (hA.norm_f i hi x hx).trans (Optimization.le_finMax hi')
  · have hi' : i - 1 ∈ Finset.Icc 1 p := by
      have := Finset.mem_Icc.1 hi; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    exact (hA.norm_c i hi x hx).trans
      (mul_le_mul_of_nonneg_left (Optimization.le_finMax hi') (Real.sqrt_nonneg _))

/-- Under the anchored composite bounds, $\|\nabla^i f(y)\| \le L_f$ for every $i \in [2 : p]$ and
every $y \in A$. This is the form of the bound in the backbone analyses. -/
theorem jet_f (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) :
    ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ Optimization.finMax 1 Lf p :=
  fun i hi _ hy => (hA.jet_bounds hy).1 i hi

/-- Under the anchored composite bounds, $f$ satisfies the backbone anchored assumption
`LipschitzDerivsAnchored` on $X_0$ with anchors in $A$, for the single order $p$ and the
constant $L_{f,p}$. -/
theorem lipschitzDerivsAnchored_f (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) :
    LipschitzDerivsAnchored f X₀ A p p Lf :=
  ⟨hA.isOpen, hA.convex, hA.subset, fun _ hy => hA.contDiffAt_f hy, fun j hj => by
    obtain rfl : j = p := le_antisymm (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj).1
    exact hA.lipschitz_f⟩

/-- Under the anchored composite bounds, $c$ satisfies the backbone anchored assumption
`LipschitzDerivsAnchored` on $X_0$ with anchors in $A$, for the single order $p$ and the
operator-norm constant $\sqrt{m} L_{c,p}$. -/
theorem lipschitzDerivsAnchored_c (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) :
    LipschitzDerivsAnchored c X₀ A p p (fun j => Real.sqrt m * Lc j) :=
  ⟨hA.isOpen, hA.convex, hA.subset, fun _ hy => hA.contDiffAt_c hy, fun j hj => by
    obtain rfl : j = p := le_antisymm (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj).1
    exact hA.lipschitz_c⟩

/-- Under the anchored composite bounds, $\sqrt{m} L_{c,p} \ge 0$. -/
theorem sqrt_mul_nonneg (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) :
    0 ≤ Real.sqrt m * Lc p :=
  mul_nonneg (Real.sqrt_nonneg _) hA.nonneg

/-- **Equations (14.2.9)–(14.2.10)** of [cartis2022evaluation], for the data of ARqpC. The anchored
composite bounds hold if and only if all of the following hold:
* $f$ satisfies the backbone anchored assumption `LipschitzDerivsAnchored` on $X_0$ with anchors
  in $A$, for the order $p$ and the constant $L_{f,p}$;
* $c$ satisfies the same assumption with the constant $\sqrt{m} L_{c,p}$;
* $L_{f,p} \ge 1$ and $L_{c,p} \ge 0$;
* $\|\nabla^i f(x)\| \le L_{f,i-1}$ and $\|\nabla^i c(x)\| \le \sqrt{m} L_{c,i-1}$ for all
  $i \in [2 : p]$ and $x \in A$. -/
theorem _root_.CartisGouldToint.Chapter14.anchoredCompositeBounds_iff :
    AnchoredCompositeBounds f c X₀ A p Lf Lc ↔
      LipschitzDerivsAnchored f X₀ A p p Lf ∧
      LipschitzDerivsAnchored c X₀ A p p (fun j => Real.sqrt m * Lc j) ∧ 1 ≤ Lf p ∧
      0 ≤ Lc p ∧ (∀ i ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ i f x‖ ≤ Lf (i - 1)) ∧
      ∀ i ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ i c x‖ ≤ Real.sqrt m * Lc (i - 1) := by
  refine ⟨fun hA => ⟨hA.lipschitzDerivsAnchored_f, hA.lipschitzDerivsAnchored_c, hA.one_le,
    hA.nonneg, hA.norm_f, hA.norm_c⟩, fun ⟨hf, hc, h1, h0, hnf, hnc⟩ => ?_⟩
  have hpp : p ∈ Finset.Icc p p := Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩
  exact ⟨hf.isOpen, hf.convex, hf.subset, fun y hy => (hf.contDiffAt y hy).contDiffWithinAt,
    fun y hy => (hc.contDiffAt y hy).contDiffWithinAt, h1, h0, hf.lipschitzAnchored p hpp,
    hc.lipschitzAnchored p hpp, hnf, hnc⟩

end AnchoredCompositeBounds

/-! ### Lemma 14.1.1 and Example 14.1.1 -/

/-- **Lemma 14.1.1** of [cartis2022evaluation] (first-order necessary optimality condition for
composite problems). Let $f : \mathbb{R}^n \to \mathbb{R}$ and
$c : \mathbb{R}^n \to \mathbb{R}^m$ be continuously differentiable, and let
$h : \mathbb{R}^m \to \mathbb{R}$ be convex and satisfy h.L. If $x_\star$ is a global minimizer
of $w = f + h \circ c$, then $s = 0$ is a global minimizer of the first-order model
$$s \mapsto T_{w,1}(x_\star, s) = T_{f,1}(x_\star, s) + h(T_{c,1}(x_\star, s)),$$
and $\phi^\delta_{w,1}(x_\star) = 0$ for every $\delta > 0$.

**Generalization.** The source also assumes h.S0, which the proof does not use.

The measure is taken over all displacements. The backbone version
`Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn` needs only a local minimizer
on a convex set and the differentiability of $f$ and $c$ at $x_\star$. -/
theorem lemma_14_1_1 {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {Lh : ℝ} {xs : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hc : ContDiff ℝ 1 c) (hL : AssumptionHLip h Lh)
    (hconv : ConvexOn ℝ univ h) (hmin : ∀ x, f xs + h (c xs) ≤ f x + h (c x)) :
    (∀ s, (ftaylorSeries ℝ f xs).taylorSum 1 0 + h ((ftaylorSeries ℝ c xs).taylorSum 1 0) ≤
      (ftaylorSeries ℝ f xs).taylorSum 1 s + h ((ftaylorSeries ℝ c xs).taylorSum 1 s)) ∧
    ∀ δ > 0, Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f xs) (ftaylorSeries ℝ c xs)
      h 1 δ univ = 0 := by
  have hmin' : IsLocalMinOn (fun z => f z + h (c z)) univ xs :=
    (isMinOn_univ_iff.2 hmin).isLocalMinOn
  have hfd := hf.contDiffAt.differentiableAt one_ne_zero (x := xs)
  have hcd := hc.contDiffAt.differentiableAt one_ne_zero (x := xs)
  have hU : {d | xs + d ∈ (univ : Set ℝⁿ)} = univ := by ext; simp
  refine ⟨fun s => ?_, fun δ hδ => ?_⟩
  · have := Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn convex_univ
      (mem_univ xs) hfd hcd hconv hL.hasLipschitzConst hmin' (s := s) (mem_univ _)
    rw [Optimization.compositeTaylorDecrement] at this
    linarith
  · have := Optimization.compositeTaylorMeasure_one_eq_zero_of_isLocalMinOn convex_univ
      (mem_univ xs) hfd hcd hconv hL.hasLipschitzConst hmin' hδ.le
    rwa [hU] at this

section Example

/-- The objective $f(x) = -\frac{2}{5} x$ of Example 14.1.1, on $\mathbb{R}$. -/
noncomputable def example1411F : ℝ → ℝ := fun x => -(2 / 5) * x

/-- The inner function $c(x) = x - x^2 + 2x^3$ of Example 14.1.1, on $\mathbb{R}$. -/
noncomputable def example1411C : ℝ → ℝ := fun x => x - x ^ 2 + 2 * x ^ 3

private theorem icc_one_three : (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} := by decide

private theorem icc_one_two : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide

private theorem example1411F_taylor (s : ℝ) :
    (ftaylorSeries ℝ example1411F 0).taylorSum 2 s = -(2 / 5) * s := by
  have hcd : ContDiffAt ℝ (3 : ℕ) example1411F 0 := by unfold example1411F; fun_prop
  have := Optimization.taylorPolynomial_eq_of_poly (N := 3) (x := 0) (d := s)
    (a := fun i => if i = 1 then -(2 / 5) * s else 0) hcd
    (Filter.Eventually.of_forall fun t => by
      rw [icc_one_three]; simp [example1411F]; ring) (p := 2) (by norm_num)
  rw [← taylorPolynomial_eq_taylorSum, this, icc_one_two]
  simp [example1411F]

private theorem example1411C_taylor (s : ℝ) :
    (ftaylorSeries ℝ example1411C 0).taylorSum 2 s = s - s ^ 2 := by
  have hcd : ContDiffAt ℝ (3 : ℕ) example1411C 0 := by unfold example1411C; fun_prop
  have := Optimization.taylorPolynomial_eq_of_poly (N := 3) (x := 0) (d := s)
    (a := fun i => if i = 1 then s else if i = 2 then -s ^ 2 else 2 * s ^ 3) hcd
    (Filter.Eventually.of_forall fun t => by
      rw [icc_one_three]; simp [example1411C]; ring) (p := 2) (by norm_num)
  rw [← taylorPolynomial_eq_taylorSum, this, icc_one_two]
  simp [example1411C]
  ring

/-- In Example 14.1.1, the second-order composite decrement at $0$ is $\Delta T_{w,2}(0, d) =
\frac{2}{5} d - |d - d^2|$. -/
private theorem example1411_decrement (d : ℝ) :
    Optimization.compositeTaylorDecrement (ftaylorSeries ℝ example1411F 0)
      (ftaylorSeries ℝ example1411C 0) (fun a => |a|) 2 d = 2 / 5 * d - |d - d ^ 2| := by
  rw [Optimization.compositeTaylorDecrement, example1411F_taylor, example1411C_taylor,
    example1411F_taylor, example1411C_taylor]
  simp
  ring

/-- **Example 14.1.1** of [cartis2022evaluation]. Let $n = m = 1$, $f(x) = -\frac{2}{5} x$,
$c(x) = x - x^2 + 2x^3$ and $h = |\cdot|$, which is convex and satisfies h.L with $L_{h,0} = 1$
and h.S0. Then:
* $x_\star = 0$ is a global minimizer of $w(x) = -\frac{2}{5} x + |x - x^2 + 2x^3|$, with
  $w(0) = 0$;
* the second-order model is $T_{w,2}(0, s) = -\frac{2}{5} s + |s - s^2|$ for every
  $s \in \mathbb{R}$;
* $T_{w,2}(0, s) \ge -\frac{2}{5}$ for every $s$, with equality at $s = 1$;
* $\phi^1_{w,2}(0) = \frac{2}{5} > 0$;
* $\phi^\delta_{w,2}(0) = 0$ for every $\delta \in (0, \frac{3}{5}]$.

So Lemma 14.1.1 does not extend to $q = 2$: at a global minimizer, the second-order measure with
radius $1$ is positive.

**Generalization.** The source shows $\phi^\delta_{w,2}(0) = 0$ for $\delta$ "smaller than
$\frac12$, say". The statement gives every $\delta \in (0, \frac{3}{5}]$.

The functions are `CartisGouldToint.Chapter14.example1411F` and
`CartisGouldToint.Chapter14.example1411C` on $\mathbb{R}$, and the measures are taken over all
displacements. -/
theorem example_14_1_1 :
    (∀ x, example1411F 0 + |example1411C 0| ≤ example1411F x + |example1411C x|) ∧
    (∀ s, (ftaylorSeries ℝ example1411F 0).taylorSum 2 s +
        |(ftaylorSeries ℝ example1411C 0).taylorSum 2 s| = -(2 / 5) * s + |s - s ^ 2|) ∧
    (∀ s : ℝ, -(2 / 5) ≤ -(2 / 5) * s + |s - s ^ 2|) ∧ -(2 / 5) * 1 + |(1 : ℝ) - 1 ^ 2| = -(2 / 5) ∧
    Optimization.compositeTaylorMeasure (ftaylorSeries ℝ example1411F 0)
      (ftaylorSeries ℝ example1411C 0) (fun a => |a|) 2 1 univ = 2 / 5 ∧
    ∀ δ ∈ Ioc (0 : ℝ) (3 / 5), Optimization.compositeTaylorMeasure
      (ftaylorSeries ℝ example1411F 0) (ftaylorSeries ℝ example1411C 0) (fun a => |a|) 2 δ
      univ = 0 := by
  refine ⟨fun x => ?_, fun s => by rw [example1411F_taylor, example1411C_taylor],
    fun s => ?_, by norm_num, ?_, fun δ hδ => ?_⟩
  · simp only [example1411F, example1411C]
    norm_num
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg (by nlinarith [sq_nonneg (x - 1 / 4)])]
      nlinarith [sq_nonneg (x - 1 / 4), mul_nonneg hx (sq_nonneg (x - 1 / 4))]
    · rw [abs_of_neg (by nlinarith [sq_nonneg (x - 1 / 4)])]
      nlinarith [sq_nonneg (x - 1 / 4), mul_nonneg (neg_nonneg.2 hx.le) (sq_nonneg (x - 1 / 4))]
  · rcases le_or_gt s 0 with hs | hs
    · nlinarith [abs_nonneg (s - s ^ 2)]
    · rcases le_or_gt s 1 with hs1 | hs1
      · rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [abs_of_neg (by nlinarith)]; nlinarith
  · rw [Optimization.compositeTaylorMeasure_eq_sSup]
    refine IsGreatest.csSup_eq ⟨⟨1, ⟨by simp, mem_univ _⟩, by
      rw [example1411_decrement]; norm_num⟩, ?_⟩
    rintro _ ⟨d, ⟨hd, -⟩, rfl⟩
    rw [example1411_decrement]
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at hd
    rcases le_or_gt d 0 with hd0 | hd0
    · nlinarith [abs_nonneg (d - d ^ 2)]
    · rw [abs_of_nonneg (by nlinarith)]; nlinarith
  · rw [Optimization.compositeTaylorMeasure_eq_sSup]
    refine IsGreatest.csSup_eq ⟨⟨0, ⟨mem_closedBall_self hδ.1.le, mem_univ _⟩, by
      rw [example1411_decrement]; norm_num⟩, ?_⟩
    rintro _ ⟨d, ⟨hd, -⟩, rfl⟩
    rw [example1411_decrement]
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at hd
    rcases le_or_gt d 0 with hd0 | hd0
    · nlinarith [abs_nonneg (d - d ^ 2)]
    · rw [abs_of_nonneg (by nlinarith [hδ.2])]; nlinarith [hδ.2]

end Example


/-! ### The ARqpC algorithm (Algorithms 14.1.1 and 14.1.2) -/

/-- **Algorithm 14.1.1** of [cartis2022evaluation], Step 0. A set of **ARqpC constants** consists of
the constants of ARqp (`Optimization.ARqpParams`) with a positive lower bound on the
regularization weights: $\sigma_0 > 0$, $0 < \eta_1 \le \eta_2 < 1$,
$0 < \gamma_1 < 1 < \gamma_2 \le \gamma_3$, $\theta \in (0, 1)$, $\varsigma \in (0, 1]$, and
$0 < \sigma_{\min} \le \sigma_0$.

The complexity analysis also needs $\theta < \varsigma$. This is a hypothesis of the results
that use it. -/
structure ARqpCParams extends Optimization.ARqpParams where
  /-- The lower bound on the regularization weights is positive, $\sigma_{\min} > 0$. -/
  σmin_pos : 0 < σmin

/-- The model data of ARqpC at the iterate $y$ with the weight $\sigma$: the decrements
$\Delta T_{w,j}(y, \cdot)$ of the generalized Taylor models of $w$, the model $\hat m$ of
(14.1.11) and its decrements (14.1.14), and the predicted decrease $\Delta T_{w,p}(y, \cdot)$.
It is `Optimization.ARqpData.ofComposite` for the jets of $f$ and $c$ at $y$. -/
noncomputable abbrev arqpcData (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (p : ℕ) (y : ℝⁿ)
    (σ : ℝ) : Optimization.ARqpData ℝⁿ :=
  Optimization.ARqpData.ofComposite (ftaylorSeries ℝ f y) (ftaylorSeries ℝ c y) h p σ

/-- The orders at which Step 2.4.3 of Algorithm 14.1.2 can halve the radius: every $j \ge 2$, and
every order if $h$ is not convex or the feasible set $X$ is not convex
(`Optimization.compositeHalvingSet`).

The algorithm of the source uses the known convexity of $h$ and $X$. If the convexity is not
known, the algorithm also halves at order $1$. This is the nonconvex case of the analysis, so
every statement below holds for that variant with the conclusions of the nonconvex case. -/
noncomputable abbrev halvingSet (h : ℝᵐ → ℝ) (X : Set ℝⁿ) : Set ℕ :=
  Optimization.compositeHalvingSet h X

/-- **Algorithm 14.1.2** of [cartis2022evaluation] (the detailed Step 2 of ARqpC), as a predicate on
its outputs. Let $x \in \mathbb{R}^n$, $\sigma \in \mathbb{R}$, $q \in \mathbb{N}$ and
$\epsilon_j \in \mathbb{R}$, and let $\hat m(s) = T_{f,p}(x, s) + h(T_{c,p}(x, s)) + \sigma
\|s\|^{p+1} / (p+1)!$ be the model (14.1.11) over the feasible steps $\{s : x + s \in X\}$, with
infimum $\hat m_*$. A step $s$ with radii $\delta_s$ is an **output** if some execution of the
following procedure, started with some $\mu \in (0, 1]$ and all radii $\delta_j = 1$, returns
$(s, \delta_s)$:
* compute a feasible step $s$ with $\mu (\hat m(0) - \hat m_*) \le \hat m(0) - \hat m(s)$;
  return $(s, \delta)$ if $\|s\| \ge 1$, and otherwise check $s$ at the orders
  $j = 1, \dots, q$;
* at order $j$, compute a feasible displacement $d$ with $\|d\| \le \delta_j$ and $\Delta
  T_{\hat m,j}(s, d) \ge \varsigma \phi^{\delta_j}_{\hat m,j}(s)$, where the displacements are
  $\{d : x + s + d \in X\}$ and the decrements are those of (14.1.14);
* if $\Delta T_{\hat m,j}(s, d) \le \varsigma \theta \epsilon_j \delta_j^j / j!$, the order
  passes, and $(s, \delta)$ is returned after order $q$;
* otherwise, if $j$ is in the halving set `CartisGouldToint.Chapter14.halvingSet h X` and $\hat
  m(s) - \hat m(s + d) < \varsigma \theta \epsilon_j \delta_j^j / (2 \, j!)$, the radius
  $\delta_j$ is halved and order $j$ is checked again;
* otherwise $\mu$ is replaced by $(1 + \mu) / 2$ and a new step is computed.

The predicate is the backbone transition system `Optimization.DetailedStepTrans`, through
`Optimization.IsARqpCDetailedStep`. It does not require $x \in X$ or $q \ge 1$; a run of ARqpC
(`CartisGouldToint.Chapter14.algorithm_14_1_1`) supplies both. Its instance with $h = 0$ and
halving at the orders $j \ge 3$ is Algorithm 12.2.3. -/
abbrev algorithm_14_1_2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (p q : ℕ)
    (P : ARqpCParams) (ε : ℕ → ℝ) (σ : ℝ) (x s : ℝⁿ) (δs : ℕ → ℝ) : Prop :=
  Optimization.IsARqpCDetailedStep f c h X p q P.toARqpParams ε (halvingSet h X) σ x s δs

/-- The termination test of ARqpC at iteration $k$: the Step-1 test passes at $k$, or Step 2
terminates with $\hat m_k(s_k) = \hat m_k(0)$ (`Optimization.arqpcStop_iff`). -/
abbrev arqpcStop (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (p q : ℕ) (P : ARqpCParams)
    (ε : ℕ → ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℝⁿ) (k : ℕ) : Prop :=
  Optimization.arqpcStop f c h P.toARqpParams p q ε x s σ δ d k

/-- **Algorithm 14.1.1** of [cartis2022evaluation] (ARqpC), as a run predicate. Let
$X \subseteq \mathbb{R}^n$, $1 \le q \le p$, $\epsilon \in (0, 1]^q$ and initial radii
$\delta_0 \in (0, 1]^q$, and let ARqpC constants be given. Sequences of iterates $x_k$, steps
$s_k$, weights $\sigma_k$, Step-1 radii $\delta_k$ and optimality displacements $d_k$, and
Step-2 radii $\delta_{s_k}$ and model displacements $d^m_k$ form a **run of ARqpC** if
$x_0 \in X$, $\sigma_0$ is the initial weight, the initial radii are $\delta_0$, and at every
iteration $k$ that the run reaches, that is, up to and including the first iteration at which
the termination test holds:
* Step 1 (14.1.10): each $d_{k,j}$ is a feasible displacement with
  $\|d_{k,j}\| \le \delta_{k,j}$ and $\Delta T_{w,j}(x_k, d_{k,j}) \ge \varsigma
  \phi^{\delta_{k,j}}_{w,j}(x_k)$, and the algorithm terminates if $\Delta T_{w,j}(x_k, d_{k,j})
  \le \varsigma \epsilon_j \delta_{k,j}^j / j!$ for every $j \in [1 : q]$;
* Step 2 (14.1.12)–(14.1.13): if Step 1 does not terminate, the pair $(s_k, \delta_{s_k})$ is an
  output of Algorithm 14.1.2 at $x_k$ with the weight $\sigma_k$, it satisfies the Step-2
  conditions of ARqp, and the algorithm terminates if $\hat m_k(s_k) = \hat m_k(0)$;
* Steps 3–4 (14.1.15)–(14.1.16): if the iteration does not terminate, then with the ratio
  $\rho_k = (w(x_k) - w(x_k + s_k)) / \Delta T_{w,p}(x_k, s_k)$, a successful iteration
  ($\rho_k \ge \eta_1$) sets $x_{k+1} = x_k + s_k$ and $\delta_{k+1} = \delta_{s_k}$, an
  unsuccessful one keeps the iterate, the radii and the displacements, and $\sigma_{k+1}$
  follows the update rule of adaptive regularization.

With $X = \mathbb{R}^n$ this is ARqpC. With a closed $X$ it is the variant ARqpC-SC of Section
14.2.

The predicate is the backbone run `Optimization.IsARqpCRun` with the halving set
`CartisGouldToint.Chapter14.halvingSet h X`: the ARqp run `Optimization.IsARqpRun` for $w$ with
composite model data, together with the condition that Step 2 is an output of Algorithm 14.1.2
at every iteration that reaches Step 2. The closedness of $X$ is not part of the predicate. It
is needed only for the existence of runs (`CartisGouldToint.Chapter14.exists_algorithm_14_1_1`). -/
abbrev algorithm_14_1_1 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (p q : ℕ)
    (P : ARqpCParams) (ε δ₀ : ℕ → ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ)
    (d dm : ℕ → ℕ → ℝⁿ) : Prop :=
  Optimization.IsARqpCRun f c h X p q P.toARqpParams (halvingSet h X) ε δ₀ x s σ δ δs d dm

/-! ### Lemmas 14.1.2 and 14.1.3: model decrease and existence of a step -/

section Step

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {p : ℕ} {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- Let $p \ge 1$. Under f.D1pL, c.D1pL and h.L, the constant $L_w$ of (14.1.3) of
[cartis2022evaluation] satisfies $L_w \ge 1$. -/
theorem one_le_compositeLipschitzW
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hp : 1 ≤ p) :
    1 ≤ compositeLipschitzW Lf Lc Lh p m := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨le_rfl, hp⟩
  have hf1 := (hf.one_le 1 h1).trans (Optimization.le_finMax (b := 1) (u := Lf) h1)
  have hc1 := (hc.nonneg 1 h1).trans (Optimization.le_finMax (b := 0) (u := Lc) h1)
  have := hL.nonneg
  unfold compositeLipschitzW
  have : 0 ≤ Real.sqrt m * Lh * Optimization.finMax 0 Lc p := by positivity
  linarith

/-- **Lemma 14.1.2** of [cartis2022evaluation], at a point with given bounds on the derivatives.
Assume h.L and h.S0. Let $x \in \mathbb{R}^n$, and let $K_f \ge 1$ and $K_c \ge 0$ satisfy
$\|\nabla^i f(x)\| \le K_f$ and $\|\nabla^i c(x)\| \le K_c$ for every $i \in [2 : p]$. Let
$\sigma \ge 0$, let $s \in \mathbb{R}^n$ with $\|s\| \le 1$, let $j \in [1 : p]$ and
$\alpha \in \mathbb{R}$, and let
$$0 < \delta \le \min\left(1, \frac{\alpha}{4(3(K_f + L_{h,0} K_c) + \sigma)}\right).$$
If $\|d\| \le \delta$ and $\Delta T_{\hat m,j}(s, d) \ge \alpha \delta^j / j!$, then
$$\hat m(s) - \hat m(s + d) \ge \frac{\alpha}{2} \frac{\delta^j}{j!},$$
where $\hat m$ is the model (14.1.11) at $x$ with the weight $\sigma$.

The bound on $\delta$ implies $\alpha > 0$. The derivative $\nabla^i f(x)$ is the term of order
$i$ of the jet `ftaylorSeries ℝ f x`. -/
theorem lemma_14_1_2_of_jet (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {x : ℝⁿ}
    {Kf Kc : ℝ} (hKf : 1 ≤ Kf) (hKc : 0 ≤ Kc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ Kf)
    (hDc : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ c x i‖ ≤ Kc)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝⁿ} (hs : ‖s‖ ≤ 1) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {α δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ min 1 (α / (4 * (3 * (Kf + Lh * Kc) + σ)))) {d : ℝⁿ}
    (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ Optimization.compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ j s d) :
    α / 2 * δ ^ j / j ! ≤
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ s -
        Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ
          (s + d) := by
  have hLh := hL.nonneg
  have hK : 0 < 3 * (Kf + Lh * Kc) + σ := by
    have : 0 ≤ Lh * Kc := mul_nonneg hLh hKc
    linarith
  have hδα : 4 * (3 * (Kf + Lh * Kc) + σ) * δ ≤ α := by
    have := hδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  exact Optimization.compositeRegularizedModel_sub_ge_of_decrement_ge hL.hasLipschitzConst hS.1
    hS.2 (zero_le_one.trans hKf) hKc hDf hDc hσ hj hs hδ0.le (hδ.trans (min_le_left _ _)) hδα hd
    hdec

/-- **Lemma 14.1.2** of [cartis2022evaluation] (relationship between the composite model and its
generalized Taylor decrements). Assume f.D1pL, c.D1pL, h.L and h.S0. Let $x \in \mathbb{R}^n$,
$\sigma \ge 0$, $s \in \mathbb{R}^n$ with $\|s\| \le 1$, $j \in [1 : p]$ and
$\alpha \in \mathbb{R}$, and let
$$0 < \delta \le \min\left(1, \frac{\alpha}{4(3L_w + \sigma)}\right) \quad \text{(14.1.17)}.$$
If $\|d\| \le \delta$ and
$$\Delta T_{\hat m,j}(s, d) \ge \alpha \frac{\delta^j}{j!} \quad \text{(14.1.18)},$$
then
$$\hat m(s) - \hat m(s + d) \ge \frac{\alpha}{2} \frac{\delta^j}{j!} \quad \text{(14.1.19)},$$
where $\hat m$ is the model (14.1.11) at $x$ with the weight $\sigma$.

The bound (14.1.17) implies $\alpha > 0$. The proof applies
`CartisGouldToint.Chapter14.lemma_14_1_2_of_jet` with the bounds (14.1.2). -/
theorem lemma_14_1_2 (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) (x : ℝⁿ)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝⁿ} (hs : ‖s‖ ≤ 1) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {α δ : ℝ}
    (hδ0 : 0 < δ)
    (hδ : δ ≤ min 1 (α / (4 * (3 * compositeLipschitzW Lf Lc Lh p m + σ)))) {d : ℝⁿ}
    (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ Optimization.compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ j s d) :
    α / 2 * δ ^ j / j ! ≤
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ s -
        Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ
          (s + d) := by
  have hp : 1 ≤ p := (Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2
  obtain ⟨hDf, hDc⟩ := (AnchoredCompositeBounds.of_global hf hc hp univ).jet_bounds (mem_univ x)
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨le_rfl, hp⟩
  have hLc0 : 0 ≤ Real.sqrt m * Optimization.finMax 0 Lc p :=
    mul_nonneg (Real.sqrt_nonneg _) Optimization.le_finMax_left
  have e : Optimization.finMax 1 Lf p + Lh * (Real.sqrt m * Optimization.finMax 0 Lc p) =
      compositeLipschitzW Lf Lc Lh p m := by
    unfold compositeLipschitzW; ring
  exact lemma_14_1_2_of_jet hL hS Optimization.le_finMax_left hLc0 hDf hDc hσ hs hj hδ0
    (by rwa [e]) hd hdec

/-- **Lemma 14.1.3** of [cartis2022evaluation], at a point with given bounds on the derivatives.
Assume h.L and h.S0. Let $X \subseteq \mathbb{R}^n$ be closed, $x \in X$, and let $K_f \ge 1$
and $K_c \ge 0$ satisfy $\|\nabla^i f(x)\| \le K_f$ and $\|\nabla^i c(x)\| \le K_c$ for every
$i \in [2 : p]$. Let $\sigma > 0$, $1 \le q \le p$ and $\epsilon \in (0, 1]^q$. Then Algorithm
14.1.2 has an output $(s, \delta_s)$ such that $\delta_{s,j} = 1$ at every order $j$ outside the
halving set and, if $\|s\| < 1$,
$$\delta_{s,j} \ge \frac{\varsigma \theta}{8(3(K_f + L_{h,0} K_c) + \sigma)} \epsilon_j$$
for every $j \in [1 : q]$ in the halving set. -/
theorem lemma_14_1_3_of_jet (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h)
    (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x : ℝⁿ}
    (hx : x ∈ X) {Kf Kc : ℝ} (hKf : 1 ≤ Kf) (hKc : 0 ≤ Kc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ Kf)
    (hDc : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ c x i‖ ≤ Kc) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s δs, algorithm_14_1_2 f c h X p q P ε σ x s δs ∧ (∀ j ∉ halvingSet h X, δs j = 1) ∧
      (‖s‖ < 1 → ∀ j ∈ Finset.Icc 1 q, j ∈ halvingSet h X →
        P.ς * P.θ / (8 * (3 * (Kf + Lh * Kc) + σ)) * ε j ≤ δs j) :=
  Optimization.exists_isARqpCDetailedStep hL hS.1 hS.2 P.toARqpParams hq hqp hε hX hx hKf hKc
    hDf hDc hσ fun _ hj hjJ => Optimization.eq_one_of_notMem_compositeHalvingSet hj hjJ

/-- **Lemma 14.1.3** of [cartis2022evaluation] (existence of a step for ARqpC). Assume f.D1pL,
c.D1pL, h.L and h.S0. Let $X \subseteq \mathbb{R}^n$ be closed, $x \in X$, $\sigma > 0$,
$1 \le q \le p$ and $\epsilon \in (0, 1]^q$. Then Algorithm 14.1.2 has an output $(s, \delta_s)$
such that $\delta_{s,j} = 1$ at every order $j$ that is never halved (this includes $j = 1$ when
$h$ and $X$ are convex) and, if $\|s\| < 1$,
$$\delta_{s,j} \ge \kappa_\delta(\sigma) \epsilon_j, \qquad \kappa_\delta(\sigma) =
  \frac{\varsigma \theta}{8(3L_w + \sigma)} \quad \text{(14.1.24)},$$
for every order $j \in [1 : q]$ that can be halved.

**Generalization.** The source states the lower bound only for $j \in [2 : q]$. When $h$ or $X$
is not convex, Algorithm 14.1.2 also halves the radius of order $1$, and the later analysis
needs the bound for $j = 1$. The bound holds there too.

An output satisfies (14.1.12), and either $\|s\| \ge 1$ or (14.1.13), by
`Optimization.IsDetailedStepOutput.spec`. -/
theorem lemma_14_1_3 (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h)
    (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x : ℝⁿ}
    (hx : x ∈ X) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s δs, algorithm_14_1_2 f c h X p q P ε σ x s δs ∧ (∀ j ∉ halvingSet h X, δs j = 1) ∧
      (‖s‖ < 1 → ∀ j ∈ Finset.Icc 1 q, j ∈ halvingSet h X →
        P.ς * P.θ / (8 * (3 * compositeLipschitzW Lf Lc Lh p m + σ)) * ε j ≤ δs j) := by
  obtain ⟨hDf, hDc⟩ :=
    (AnchoredCompositeBounds.of_global hf hc (hq.trans hqp) univ).jet_bounds (mem_univ x)
  have hLc0 : 0 ≤ Real.sqrt m * Optimization.finMax 0 Lc p :=
    mul_nonneg (Real.sqrt_nonneg _) Optimization.le_finMax_left
  have e : Optimization.finMax 1 Lf p + Lh * (Real.sqrt m * Optimization.finMax 0 Lc p) =
      compositeLipschitzW Lf Lc Lh p m := by
    unfold compositeLipschitzW; ring
  obtain ⟨s, δs, h1, h2, h3⟩ := lemma_14_1_3_of_jet hL hS P hq hqp hε hX hx
    Optimization.le_finMax_left hLc0 hDf hDc hσ
  rw [e] at h3
  exact ⟨s, δs, h1, h2, h3⟩

/-- Assume h.L, and let $X$ be closed, $x \in X$ and $\sigma > 0$. Every output $(s, \delta_s)$ of
Algorithm 14.1.2 satisfies the Step-2 conditions of the ARqp run (`Optimization.ARqpStep`) for
some model displacements $d^m$. -/
theorem algorithm_14_1_2.exists_arqpStep (hL : AssumptionHLip h Lh) {X : Set ℝⁿ}
    (hX : IsClosed X) {P : ARqpCParams} {q : ℕ} {ε : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ) {x s : ℝⁿ}
    (hx : x ∈ X) {δs : ℕ → ℝ} (hout : algorithm_14_1_2 f c h X p q P ε σ x s δs) :
    ∃ dm : ℕ → ℝⁿ,
      Optimization.ARqpStep X P.toARqpParams q ε (arqpcData f c h p x σ) x s δs dm :=
  Optimization.IsARqpCDetailedStep.exists_arqpStep hL hX hσ hx hout

/-- **Algorithms 14.1.1 and 14.1.2** of [cartis2022evaluation], existence of runs without
smoothness. Assume h.L and h.S0, and let $f$ and $c$ be arbitrary. Let
$X \subseteq \mathbb{R}^n$ be closed, $x_0 \in X$, $1 \le q \le p$, $\epsilon \in (0, 1]^q$ and
$\delta_0 \in (0, 1]^q$. Then there is a run of ARqpC that starts at $x_0$.

In the run, Step 2 is the output of `CartisGouldToint.Chapter14.lemma_14_1_3_of_jet` with the
bounds on the derivatives at the current iterate. -/
theorem exists_algorithm_14_1_1_of_hLip (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h)
    (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q)
    (hqp : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x₀ : ℝⁿ}
    (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ), x 0 = x₀ ∧
      algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm :=
  Optimization.exists_isARqpCRun_compositeHalvingSet hL hS.1 hS.2 P.toARqpParams hq hqp hε hδ₀
    hX hx₀

/-- **Algorithm 14.1.1** of [cartis2022evaluation], existence of runs. Assume f.D1pL, c.D1pL, h.L
and h.S0. Let $X \subseteq \mathbb{R}^n$ be closed, $x_0 \in X$, $1 \le q \le p$,
$\epsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$. Then there is a run of ARqpC that starts at
$x_0$.

In the run, the Step-1 displacements are exact maximizers, Step 2 is an output of Lemma 14.1.3,
and the regularization weights are any admissible updates. The smoothness assumptions are not
used (`CartisGouldToint.Chapter14.exists_algorithm_14_1_1_of_hLip`). -/
theorem exists_algorithm_14_1_1 (_hf : Chapter12.AssumptionD1pL f p Lf)
    (_hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q)
    (hqp : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x₀ : ℝⁿ}
    (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ), x 0 = x₀ ∧
      algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm :=
  exists_algorithm_14_1_1_of_hLip hL hS P hq hqp hε hδ₀ hX hx₀

end Step


/-! ### Lemmas 14.1.4–14.1.6 -/

namespace algorithm_14_1_1

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}

/-- The Step-1 test (14.1.10) of ARqpC at iteration $k$, in terms of the optimality displacements
$d_{k,j}$ of the run: $\Delta T_{w,j}(x_k, d_{k,j}) \le \varsigma \epsilon_j \delta_{k,j}^j /
j!$ for every $j \in [1 : q]$. -/
abbrev Stop₁ (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (p q : ℕ) (P : ARqpCParams)
    (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℝⁿ) (k : ℕ) : Prop :=
  Optimization.arqpStop₁ P.toARqpParams q ε (Optimization.arqpcData f c h p x σ) δ d k

end algorithm_14_1_1

section Analysis

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Lemma 14.1.4(ii)** of [cartis2022evaluation], without smoothness. Assume h.L and h.S0, and
consider a run of ARqpC. Let $k$ be an iteration such that the run has not terminated before
$k$, the Step-1 test fails at $k$, and Step 2 terminates, $\hat m_k(s_k) = \hat m_k(0)$. Then
there is $\delta \in (0, 1]^q$ such that $x_k$ is an $(\epsilon, \delta)$-approximate $q$-th
order minimizer (14.1.9) of $w$ over $X$:
$$\phi^{\delta_j}_{w,j}(x_k) \le \epsilon_j \frac{\delta_j^j}{j!} \quad \text{for every } j \in
  [1 : q].$$

The measures are taken over the feasible displacements $\{e : x_k + e \in X\}$, and (14.1.9) is
`Optimization.IsEpsDeltaApproxComposite`. -/
theorem lemma_14_1_4_ii (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k)
    (heq : Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (σ k) (s k) =
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (σ k) 0) :
    ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
      Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h {e | x k + e ∈ X} q ε δ' :=
  hr.run.exists_isEpsDeltaApproxComposite_of_stop₂ hL hS.1 hS.2 hr.q_le_p
    (fun j hj => (hr.ε_mem j hj).1) hk h1 heq

/-- **Lemma 14.1.4** of [cartis2022evaluation] (termination in Step 2 of ARqpC). Consider a run of
ARqpC, where $f$ and $c$ are $p$ times continuously differentiable and $h$ satisfies h.L and
h.S0. Let $k$ be an iteration such that the run has not terminated before $k$ and the Step-1
test fails at $k$.
* (i) If $q = 1$ and $h$ and $X$ are convex, Step 2 does not terminate:
  $\hat m_k(s_k) < \hat m_k(0)$.
* (ii) If Step 2 terminates, $\hat m_k(s_k) = \hat m_k(0)$, then $x_k$ is an
  $(\epsilon, \delta)$-approximate $q$-th order minimizer (14.1.9) of $w$ over $X$ for some
  $\delta \in (0, 1]^q$.

**Generalization.** Only the smoothness that the proof uses is assumed: $f$ and $c$ are $p$
times continuously differentiable. Part (ii) holds without smoothness
(`CartisGouldToint.Chapter14.lemma_14_1_4_ii`). -/
theorem lemma_14_1_4 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hfC : ContDiff ℝ p f) (hcC : ContDiff ℝ p c) (hL : AssumptionHLip h Lh)
    (hS : AssumptionHS0 h) :
    (q = 1 → ConvexOn ℝ univ h → Convex ℝ X → ∀ k,
      (∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) →
      ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k →
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
          h p (σ k) (s k) <
        Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h p (σ k) 0) ∧
    (∀ k, (∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) →
      ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k →
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
          h p (σ k) (s k) =
        Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h p (σ k) 0 →
      ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h {e | x k + e ∈ X} q ε δ') :=
  ⟨fun hq hconv hX _ hk h1 => hr.run.compositeModel_lt_of_convex hL hconv hX
    (fun _ _ => hfC.contDiffAt) (fun _ _ => hcC.contDiffAt) hq (hr.one_le_q.trans hr.q_le_p)
    (fun j hj => (hr.ε_mem j hj).1) hr.δ₀_mem hk h1,
    fun _ hk h1 heq => lemma_14_1_4_ii hr hL hS hk h1 heq⟩

/-- **Lemma 14.1.5** of [cartis2022evaluation] (Taylor decrease for ARqpC). Consider a run of ARqpC,
and let $k$ be an iteration such that the run has not terminated before $k$ and the Step-1 test
fails at $k$, so that Step 2 is executed. Then
$$\Delta T_{w,p}(x_k, s_k) \ge \frac{\sigma_k}{(p+1)!} \|s_k\|^{p+1} \quad \text{(14.1.25)},$$
and $\Delta T_{w,p}(x_k, s_k) > 0$ unless Step 2 terminates, that is, unless
$\hat m_k(s_k) = \hat m_k(0)$.

The statement needs no assumption on $f$, $c$ or $h$. -/
theorem lemma_14_1_5 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤
      Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
        h p (s k) ∧
    (¬ Optimization.arqpStop₂ (fun k => arqpcData f c h p (x k) (σ k)) s k →
      0 < Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (s k)) :=
  hr.run.compositeTaylorDecrement_ge hk h1

/-- **Algorithm 14.1.1** of [cartis2022evaluation], monotonicity of the objective. Along a run of
ARqpC, $w(x_{k+1}) \le w(x_k)$ for every $k$ such that the run has not terminated at any
iteration $i \le k$. -/
theorem algorithm_14_1_1.w_succ_le (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    f (x (k + 1)) + h (c (x (k + 1))) ≤ f (x k) + h (c (x k)) :=
  hr.run.composite_objective_succ_le hk

/-- **Algorithm 14.1.1** of [cartis2022evaluation], the iterates stay in the sublevel set (14.2.8).
Along a run of ARqpC, $x_k \in \{y \in X : w(y) \le w(x_0)\}$ for every $k$ such that the run
has not terminated before $k$, that is, up to and including the first termination index. -/
theorem algorithm_14_1_1.mem_compositeSublevel
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    x k ∈ compositeSublevel f c h X (x 0) :=
  hr.run.mem_compositeSublevel hk

/-- **Lemma 14.1.6** of [cartis2022evaluation] (upper bound on the regularization parameter for
ARqpC). Consider a run of ARqpC. Assume that $f$ and $c$ are $p$ times continuously
differentiable, that $\nabla^p f$ is Lipschitz continuous on $\mathbb{R}^n$ with constant
$L_{f,p}$ (f.DpL), that $\nabla^p c_i$ is Lipschitz continuous on $\mathbb{R}^n$ with constant
$L_{c,p}$ for every component $c_i$ (c.DpL), and that $h$ satisfies h.L. If the run has not
terminated before iteration $K$, then for every $k \le K$
$$\sigma_k \le \sigma_{\max} = \max\left(\sigma_0, \frac{\gamma_3 L_{w,p}}{1 - \eta_2}\right)
  \quad \text{(14.1.26)},$$
with $L_{w,p} = L_{f,p} + \sqrt{m} L_{h,0} L_{c,p}$ of (14.1.27).

**Generalization.** Only the smoothness and Lipschitz properties that the proof uses are
assumed.

The bound $\sigma_{\max}$ is `Optimization.arSigmaMax`. The proof specializes
`Optimization.IsARqpRun.sigma_le_of_compositeAnchored` with anchors in $\mathbb{R}^n$. -/
theorem lemma_14_1_6 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hfC : ContDiff ℝ p f) (hLfp : IteratedFDerivLipschitzOn f p (Lf p) univ)
    (hcC : ContDiff ℝ p c)
    (hLcp : ∀ i, IteratedFDerivLipschitzOn (fun y => c y i) p (Lc p) univ)
    (hL : AssumptionHLip h Lh) {K : ℕ} (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ Optimization.arSigmaMax P.toARParams (compositeLipschitzWp Lf Lc Lh p m) := by
  have hpp : ∀ j ∈ Finset.Icc p p, j = p := fun j hj =>
    le_antisymm (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj).1
  exact hr.run.sigma_le_of_compositeAnchored (A := univ)
    (LipschitzDerivsAnchored.of_contDiff hfC (fun j hj => hpp j hj ▸ hLfp) univ)
    (LipschitzDerivsAnchored.of_contDiff hcC (L := fun j => Real.sqrt m * Lc j) (fun j hj =>
      hpp j hj ▸ iteratedFDerivLipschitzOn_of_forall_component (fun _ _ => hcC.contDiffAt) hLcp)
      univ)
    hL compositeLipschitzWp_eq.ge (subset_univ X) (fun _ _ _ => mem_univ _) hK

/-- **Lemma 14.1.6** of [cartis2022evaluation], under the anchored assumptions. Consider a run of
ARqpC, and let $X_0 \supseteq X$ be a set on which the anchored composite bounds hold with the
anchor set $\{y \in X : w(y) \le w(x_0)\}$. Assume h.L. If the run has not terminated before
iteration $K$, then $\sigma_k \le \sigma_{\max} = \max(\sigma_0, \gamma_3 L_{w,p} / (1 -
\eta_2))$ for every $k \le K$. -/
theorem lemma_14_1_6_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {X₀ : Set ℝⁿ} (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {K : ℕ}
    (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ Optimization.arSigmaMax P.toARParams (compositeLipschitzWp Lf Lc Lh p m) :=
  hr.run.sigma_le_of_compositeAnchored hA.lipschitzDerivsAnchored_f hA.lipschitzDerivsAnchored_c hL
    compositeLipschitzWp_eq.ge hX
    (fun _ hy hw => ⟨hy, hw⟩) hK

end Analysis

/-! ### Lemmas 14.1.7 and 14.1.8 -/

section StepLength

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- The bound $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_{w,p} / (1 - \eta_2))$ of Lemma 14.1.6,
(14.1.26). -/
noncomputable abbrev arqpcSigmaMax (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  Optimization.arSigmaMax P.toARParams (compositeLipschitzWp Lf Lc Lh p m)

/-- The constant $\kappa_{\delta,\min} = \varsigma \theta / (8(3L_w + \sigma_{\max}))$ of (14.1.29).
-/
noncomputable def kappaDeltaMin (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  P.ς * P.θ / (8 * (3 * compositeLipschitzW Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m))

/-- The constant $\kappa_{\delta,\min}$ is the backbone radius constant
$\kappa_\delta(\sigma_{\max})$ (`Optimization.arqpKappaDelta`) for the composite constant $L_w$. -/
theorem kappaDeltaMin_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) :
    kappaDeltaMin P Lf Lc Lh p m = Optimization.arqpKappaDelta P.toARqpParams
      (compositeLipschitzW Lf Lc Lh p m) (arqpcSigmaMax P Lf Lc Lh p m) := rfl

/-- Lemma 14.1.6 under f.D1pL, c.D1pL and h.L: if a run of ARqpC has not terminated before iteration
$K$, then $\sigma_k \le \sigma_{\max}$ for every $k \le K$. -/
theorem sigma_le_arqpcSigmaMax (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {K : ℕ}
    (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ arqpcSigmaMax P Lf Lc Lh p m := by
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hr.one_le_q.trans hr.q_le_p, le_rfl⟩
  exact lemma_14_1_6 hr hf.contDiff (hf.lipschitz p hp') hc.contDiff
    (fun i => hc.lipschitz_component i p hp') hL hK

/-- **Lemma 14.1.6** of [cartis2022evaluation], under the anchored assumptions, with the bound
`CartisGouldToint.Chapter14.arqpcSigmaMax`. Consider a run of ARqpC, let $X_0 \supseteq X$ be a
set on which the anchored composite bounds hold with the anchor set
$\{y \in X : w(y) \le w(x_0)\}$, and assume h.L. If the run has not terminated before iteration
$K$, then $\sigma_k \le \sigma_{\max}$ for every $k \le K$. -/
theorem sigma_le_arqpcSigmaMax_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {X₀ : Set ℝⁿ} (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {K : ℕ}
    (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ arqpcSigmaMax P Lf Lc Lh p m :=
  lemma_14_1_6_anchored hr hA hX hL hK

/-- **Lemma 14.1.7** of [cartis2022evaluation] (a useful inequality for ARqpC), under the anchored
assumptions. Consider a run of ARqpC, let $X_0 \supseteq X$ be a set on which the anchored
composite bounds hold with the anchor set $\{y \in X : w(y) \le w(x_0)\}$, and assume h.L. Let
$k$ be a successful iteration ($\rho_k \ge \eta_1$) such that the run has not terminated at any
iteration $i \le k$ and the Step-1 test fails at $k + 1$. Then there is $j \in [1 : q]$ with
$$(\varsigma - \theta) \epsilon_j \frac{\delta_{k+1,j}^j}{j!} < (L_{w,p} + \sigma_{\max})
  \sum_{\ell=1}^{j} \frac{\delta_{k+1,j}^\ell}{\ell!} \|s_k\|^{p-\ell+1} + \frac{2\sqrt{m} \,
  L_{h,0} L_{c,p}}{(p+1)!} \|s_k\|^{p+1} \quad \text{(14.1.30)}.$$

**Correction.** The source prints the factor $(1 - \theta)$ and omits the factor $2$ of the last
term. See `CartisGouldToint.Chapter14.lemma_14_1_7`. -/
theorem lemma_14_1_7_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {X₀ : Set ℝⁿ} (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δ (k + 1) j ^ j / j ! <
      (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) +
      2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
  obtain ⟨j, hj, hlt⟩ := hr.run.exists_composite_radius_ineq hA.lipschitzDerivsAnchored_f
    hA.lipschitzDerivsAnchored_c hL hA.one_le
    hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge hX (fun _ hy hw => ⟨hy, hw⟩) hr.one_le_q
    hr.q_le_p hr.ε_mem hr.δ₀_mem hk hsucc h1
  exact ⟨j, hj, hlt.trans_eq (by ring)⟩

/-- **Lemma 14.1.7** of [cartis2022evaluation] (a useful inequality for ARqpC). Assume f.D1pL,
c.D1pL and h.L, and consider a run of ARqpC. Let $k$ be a successful iteration
($\rho_k \ge \eta_1$) such that the run has not terminated at any iteration $i \le k$ and the
Step-1 test fails at $k + 1$. Then there is $j \in [1 : q]$ with
$$(\varsigma - \theta) \epsilon_j \frac{\delta_{k+1,j}^j}{j!} < (L_{w,p} + \sigma_{\max})
  \sum_{\ell=1}^{j} \frac{\delta_{k+1,j}^\ell}{\ell!} \|s_k\|^{p-\ell+1} + \frac{2\sqrt{m} \,
  L_{h,0} L_{c,p}}{(p+1)!} \|s_k\|^{p+1} \quad \text{(14.1.30)}.$$

**Correction.** The source prints the factor $(1 - \theta)$ on the left, which presumes
$\varsigma = 1$. When the Step-1 test fails, it only certifies $\phi^{\delta}_{w,j}(x_{k+1}) >
\varsigma \epsilon_j \delta^j / j!$ for some $j$, so the factor is $(\varsigma - \theta)$. The
last term of the source lacks the factor $2$. The inequality is strict.

**Typo.** In the proof, (B.14.6) prints $(p - j + 1)!$ and $\|s_k\|^{p-j+1}$ inside the sum over
$\ell$. They are $(p - \ell + 1)!$ and $\|s_k\|^{p-\ell+1}$, as in (B.14.2), (B.14.4) and
(14.1.30), and the proof here uses the corrected bound.

**Generalization.** The source also assumes h.S0, which the proof does not use.

For short steps the inequality comes from the model test (14.1.13); for long steps,
$\|s_k\| \ge 1$, it holds trivially. The statement does not assume $\theta < \varsigma$. The
proof specializes `CartisGouldToint.Chapter14.lemma_14_1_7_anchored` with $X_0 = \mathbb{R}^n$. -/
theorem lemma_14_1_7 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δ (k + 1) j ^ j / j ! <
      (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) +
      2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
  exact lemma_14_1_7_anchored hr (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hk hsucc h1

end StepLength

section StepLength2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- The step-length bound of the first case of (14.1.31):
$$\left(\frac{\varsigma - \theta}{j! \, A} \cdot \frac{\epsilon_j}{3}\right)^{1/(p-j+1)}, \qquad
  A = L_{w,p} + \sigma_{\max}.$$
For $j = 1$ it is the bound $((\varsigma - \theta) \epsilon_j / (3 j! A))^{1/p}$ of the source. -/
noncomputable def stepBound1 (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m j : ℕ) (εj : ℝ) :
    ℝ :=
  ((P.ς - P.θ) / ((j ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
    arqpcSigmaMax P Lf Lc Lh p m)) * εj / 3) ^ (1 / ((p : ℝ) - j + 1))

/-- The step-length bound of the second case of (14.1.31), with the factor
$\epsilon_j^{(j+1)/(p+1)}$:
$$\left(\frac{(\varsigma - \theta) \kappa_{\delta,\min}^j}{3 j! \, A}\right)^{1/(p-j+1)}
  \epsilon_j^{(j+1)/(p+1)}, \qquad A = L_{w,p} + \sigma_{\max}.$$
-/
noncomputable def stepBound2 (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m j : ℕ) (εj : ℝ) :
    ℝ :=
  ((P.ς - P.θ) / ((j ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
    arqpcSigmaMax P Lf Lc Lh p m)) * kappaDeltaMin P Lf Lc Lh p m ^ j / 3) ^
      (1 / ((p : ℝ) - j + 1)) * εj ^ (((j : ℝ) + 1) / ((p : ℝ) + 1))

/-- The first bound of (14.1.31) is the backbone bound `Optimization.arqpcStepBoundUnit` for the
constant $L_{w,p}$. -/
theorem stepBound1_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m j : ℕ) (εj : ℝ) :
    stepBound1 P Lf Lc Lh p m j εj = Optimization.arqpcStepBoundUnit P.toARqpParams
      (compositeLipschitzWp Lf Lc Lh p m) p j εj := rfl

/-- The second bound of (14.1.31) is the backbone bound `Optimization.arqpcStepBound` for the
constants $L_{w,p}$ and $L_w$. -/
theorem stepBound2_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m j : ℕ) (εj : ℝ) :
    stepBound2 P Lf Lc Lh p m j εj = Optimization.arqpcStepBound P.toARqpParams
      (compositeLipschitzWp Lf Lc Lh p m) (compositeLipschitzW Lf Lc Lh p m) p j εj := rfl

/-- **Lemma 14.1.8** of [cartis2022evaluation] (lower bound on the step for ARqpC), under the
anchored assumptions. Consider a run of ARqpC, let $X_0 \supseteq X$ be a set on which the
anchored composite bounds hold with the anchor set $\{y \in X : w(y) \le w(x_0)\}$, and assume
h.L and $\theta < \varsigma$. Let $k$ be a successful iteration such that the run has not
terminated at any iteration $i \le k$ and the Step-1 test fails at $k + 1$. Then there is
$j \in [1 : q]$ such that, with $A = L_{w,p} + \sigma_{\max}$:
* if $\delta_{k+1,j} = 1$, then $\|s_k\| \ge ((\varsigma - \theta) \epsilon_j / (3 j!
  A))^{1/(p-j+1)}$, the first case of (14.1.31);
* if $\delta_{k+1,j} \ge \kappa_{\delta,\min} \epsilon_j$, then $\|s_k\| \ge ((\varsigma -
  \theta) \kappa_{\delta,\min}^j / (3 j! A))^{1/(p-j+1)} \epsilon_j^{(j+1)/(p+1)}$, the second
  case of (14.1.31).

**Correction.** The source prints the second case without the factor $\epsilon_j^{(j+1)/(p+1)}$,
and with $(1 - \theta)$ for $(\varsigma - \theta)$. See
`CartisGouldToint.Chapter14.lemma_14_1_8`. -/
theorem lemma_14_1_8_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) {X₀ : Set ℝⁿ}
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q,
      (δ (k + 1) j = 1 → stepBound1 P Lf Lc Lh p m j (ε j) ≤ ‖s k‖) ∧
      (kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δ (k + 1) j →
        stepBound2 P Lf Lc Lh p m j (ε j) ≤ ‖s k‖) :=
  hr.run.composite_norm_step_ge (Kw := compositeLipschitzW Lf Lc Lh p m)
    hA.lipschitzDerivsAnchored_f hA.lipschitzDerivsAnchored_c hL hA.one_le
    hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge (one_le_compositeLipschitzW_of hL.nonneg) hX
    (fun _ hy hw => ⟨hy, hw⟩) hr.one_le_q hr.q_le_p hθς hr.ε_mem hr.δ₀_mem hk hsucc h1

/-- **Lemma 14.1.8** of [cartis2022evaluation] (lower bound on the step for ARqpC). Assume f.D1pL,
c.D1pL, h.L and $\theta < \varsigma$, and consider a run of ARqpC. Let $k$ be a successful
iteration such that the run has not terminated at any iteration $i \le k$ and the Step-1 test
fails at $k + 1$. Then there is $j \in [1 : q]$ such that, with $A = L_{w,p} + \sigma_{\max}$:
* if $\delta_{k+1,j} = 1$ (the radius policy for $q = 1$ and convex $h$), then $\|s_k\| \ge
  ((\varsigma - \theta) \epsilon_j / (3 j! A))^{1/(p-j+1)}$, the first case of (14.1.31);
* if $\delta_{k+1,j} \ge \kappa_{\delta,\min} \epsilon_j$ (the radius policy (14.1.28)), then
  $\|s_k\| \ge ((\varsigma - \theta) \kappa_{\delta,\min}^j / (3 j! A))^{1/(p-j+1)}
  \epsilon_j^{(j+1)/(p+1)}$, the second case of (14.1.31).

Long steps, $\|s_k\| \ge 1$, satisfy both bounds.

**Correction.** The source prints the second case without the factor $\epsilon_j^{(j+1)/(p+1)}$,
which its proof in Appendix B derives. As in Lemma 14.1.7, the source writes $(1 - \theta)$ for
$(\varsigma - \theta)$.

The bounds are `CartisGouldToint.Chapter14.stepBound1` and
`CartisGouldToint.Chapter14.stepBound2`. The proof specializes
`CartisGouldToint.Chapter14.lemma_14_1_8_anchored` with $X_0 = \mathbb{R}^n$. -/
theorem lemma_14_1_8 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q,
      (δ (k + 1) j = 1 → stepBound1 P Lf Lc Lh p m j (ε j) ≤ ‖s k‖) ∧
      (kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δ (k + 1) j →
        stepBound2 P Lf Lc Lh p m j (ε j) ≤ ‖s k‖) := by
  exact lemma_14_1_8_anchored hr hθς (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hk hsucc h1

end StepLength2

/-! ### The radius policies -/

section RadiusPolicy

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Lemma 14.1.3** of [cartis2022evaluation], for every step of a run, under the anchored
assumptions. Consider a run of ARqpC, let $X_0 \supseteq X$ be a set on which the anchored
composite bounds hold with the anchor set $\{y \in X : w(y) \le w(x_0)\}$, and assume h.L and
h.S0. Let $k$ be an iteration such that the run has not terminated before $k$ and the Step-1
test fails at $k$. Then $\delta_{s_k,j} \ge \kappa_{\delta,\min} \epsilon_j$ for every
$j \in [1 : q]$, whatever the length of the step.

Radii are halved only while short trial steps are checked, so the bound also holds after long
steps. -/
theorem algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {X₀ : Set ℝⁿ} (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δs k j :=
  hr.arqpKappaDelta_mul_le_radius (Kf := Optimization.finMax 1 Lf p)
    (Kc := Real.sqrt m * Optimization.finMax 0 Lc p) hA.lipschitzDerivsAnchored_f
    hA.lipschitzDerivsAnchored_c hL hS.1 hS.2
    compositeLipschitzWp_eq.ge (zero_le_one.trans Optimization.le_finMax_left)
    (mul_nonneg (Real.sqrt_nonneg _) Optimization.le_finMax_left) compositeLipschitzW_eq.ge
    (one_le_compositeLipschitzW_of hL.nonneg) (fun i hi _ hy => (hA.jet_bounds hy).1 i hi)
    (fun i hi _ hy => (hA.jet_bounds hy).2 i hi) hX (fun _ hy hw => ⟨hy, hw⟩) hk h1

/-- **Lemma 14.1.3** of [cartis2022evaluation], for every step of a run. Assume f.D1pL, c.D1pL, h.L
and h.S0, and consider a run of ARqpC. Let $k$ be an iteration such that the run has not
terminated before $k$ and the Step-1 test fails at $k$. Then $\delta_{s_k,j} \ge
\kappa_{\delta,\min} \epsilon_j$ for every $j \in [1 : q]$, whatever the length of the step.

Radii are halved only while short trial steps are checked, so the bound also holds after long
steps. -/
theorem algorithm_14_1_1.kappaDeltaMin_mul_le_radius
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δs k j := by
  exact hr.kappaDeltaMin_mul_le_radius_anchored (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hS hk h1

/-- The radius policy (14.1.28) holds for every run of ARqpC. Under f.D1pL, c.D1pL, h.L and h.S0, at
every iteration $k$ before termination at which the Step-1 test fails, $\|s_k\| \ge 1$ or
$\delta_{s_k,j} \ge \kappa_{\delta,\min} \epsilon_j$ for every $j \in [1 : q]$; the second
alternative always holds
(`CartisGouldToint.Chapter14.algorithm_14_1_1.kappaDeltaMin_mul_le_radius`). -/
theorem algorithm_14_1_1.radius_policy
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δs k j :=
  Or.inr (hr.kappaDeltaMin_mul_le_radius hf hc hL hS hk h1)

end RadiusPolicy

/-! ### Lemma 14.1.9 and Theorem 14.1.10 -/

section Complexity

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- The constant $\kappa_{\Delta m}$ of Lemma 14.1.9 in the case $q = 1$ with convex $h$:
$$\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!} \left(\frac{\varsigma - \theta}{3(L_{w,p} +
  \sigma_{\max})}\right)^{(p+1)/p}.$$
-/
noncomputable def kappaDm1 (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) /
    (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) / 3) ^
      (((p : ℝ) + 1) / p)

/-- The constant $\kappa_{\Delta m}$ of Lemma 14.1.9 in the general case:
$$\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!} \left(\frac{(\varsigma - \theta)
  \kappa_{\delta,\min}^q}{3 q! (L_{w,p} + \sigma_{\max})}\right)^{(p+1)/(p-q+1)}.$$
-/
noncomputable def kappaDm2 (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p q m : ℕ) : ℝ :=
  P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) /
    ((q ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m)) *
      kappaDeltaMin P Lf Lc Lh p m ^ q / 3) ^ (((p : ℝ) + 1) / ((p : ℝ) - q + 1))

/-- The first constant of Lemma 14.1.9 is the backbone constant `Optimization.arqpcKappaDmUnit` for
the constant $L_{w,p}$. -/
theorem kappaDm1_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) :
    kappaDm1 P Lf Lc Lh p m = Optimization.arqpcKappaDmUnit P.toARqpParams
      (compositeLipschitzWp Lf Lc Lh p m) p := rfl

/-- The second constant of Lemma 14.1.9 is the backbone constant `Optimization.arqpcKappaDm` for the
constants $L_{w,p}$ and $L_w$. -/
theorem kappaDm2_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p q m : ℕ) :
    kappaDm2 P Lf Lc Lh p q m = Optimization.arqpcKappaDm P.toARqpParams
      (compositeLipschitzWp Lf Lc Lh p m) (compositeLipschitzW Lf Lc Lh p m) p q := rfl

/-- **Lemma 14.1.9** of [cartis2022evaluation] (model and function decreases for ARqpC), under the
anchored assumptions. Consider a run of ARqpC, let $X_0 \supseteq X$ be a set on which the
anchored composite bounds hold with the anchor set $\{y \in X : w(y) \le w(x_0)\}$, and assume
h.L and $\theta < \varsigma$. Let $k$ be a successful iteration such that the run has not
terminated at any iteration $i \le k$ and the Step-1 test fails at $k + 1$.
* If $q = 1$ and $\delta_{k+1,1} = 1$, then $\Delta T_{w,p}(x_k, s_k) \ge \kappa_{\Delta m}
  \epsilon_1^{(p+1)/p}$ (14.1.32) and $w(x_k) - w(x_{k+1}) \ge \eta_1 \kappa_{\Delta m}
  \epsilon_1^{(p+1)/p}$ (14.1.33), with $\kappa_{\Delta m}$ =
  `CartisGouldToint.Chapter14.kappaDm1`.
* If $\|s_k\| \ge 1$ or $\delta_{k+1,j} \ge \kappa_{\delta,\min} \epsilon_j$ for every
  $j \in [1 : q]$ (the radius policy (14.1.28)), then there is $j \in [1 : q]$ with $\Delta
  T_{w,p}(x_k, s_k) \ge \kappa_{\Delta m} \epsilon_j^{j+1}$ and $w(x_k) - w(x_{k+1}) \ge \eta_1
  \kappa_{\Delta m} \epsilon_j^{j+1}$, with $\kappa_{\Delta m}$ =
  `CartisGouldToint.Chapter14.kappaDm2`.

**Correction.** The source claims (14.1.32) at every iteration before termination, under f.D1qL
only, with $(1 - \theta)$ for $(\varsigma - \theta)$. See
`CartisGouldToint.Chapter14.lemma_14_1_9`. -/
theorem lemma_14_1_9_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) {X₀ : Set ℝⁿ}
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    (q = 1 → δ (k + 1) 1 = 1 →
      kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p) ≤
        Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h p (s k) ∧
      P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p)) ≤
        (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1))))) ∧
    ((1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δ (k + 1) j) →
      ∃ j ∈ Finset.Icc 1 q,
        kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1) ≤
          Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
            (ftaylorSeries ℝ c (x k)) h p (s k) ∧
        P.η₁ * (kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1)) ≤
          (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1))))) :=
  ⟨fun hq hδ1 => hr.run.composite_decrease_unit hA.lipschitzDerivsAnchored_f
    hA.lipschitzDerivsAnchored_c hL hA.one_le hA.sqrt_mul_nonneg
    compositeLipschitzWp_eq.ge hX (fun _ hy hw => ⟨hy, hw⟩) hq hr.q_le_p hθς hr.ε_mem hr.δ₀_mem hk
    hsucc h1 hδ1,
    fun hpol => hr.run.composite_decrease (Kw := compositeLipschitzW Lf Lc Lh p m)
    hA.lipschitzDerivsAnchored_f hA.lipschitzDerivsAnchored_c hL
      hA.one_le hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge
      (one_le_compositeLipschitzW_of hL.nonneg) hX (fun _ hy hw => ⟨hy, hw⟩) hr.one_le_q hr.q_le_p
      hθς hr.ε_mem hr.δ₀_mem hk hsucc h1 hpol⟩

/-- **Lemma 14.1.9** of [cartis2022evaluation] (model and function decreases for ARqpC). Assume
f.D1pL, c.D1pL, h.L and $\theta < \varsigma$, and consider a run of ARqpC. Let $k$ be a
successful iteration such that the run has not terminated at any iteration $i \le k$ and the
Step-1 test fails at $k + 1$.
* If $q = 1$ and $\delta_{k+1,1} = 1$, then $\Delta T_{w,p}(x_k, s_k) \ge \kappa_{\Delta m}
  \epsilon_1^{(p+1)/p}$ (14.1.32) and $w(x_k) - w(x_{k+1}) \ge \eta_1 \kappa_{\Delta m}
  \epsilon_1^{(p+1)/p}$ (14.1.33), with $\kappa_{\Delta m}$ =
  `CartisGouldToint.Chapter14.kappaDm1`.
* If $\|s_k\| \ge 1$ or $\delta_{k+1,j} \ge \kappa_{\delta,\min} \epsilon_j$ for every
  $j \in [1 : q]$ (the radius policy (14.1.28)), then there is $j \in [1 : q]$ with $\Delta
  T_{w,p}(x_k, s_k) \ge \kappa_{\Delta m} \epsilon_j^{j+1}$ and $w(x_k) - w(x_{k+1}) \ge \eta_1
  \kappa_{\Delta m} \epsilon_j^{j+1}$, with $\kappa_{\Delta m}$ =
  `CartisGouldToint.Chapter14.kappaDm2`.

**Correction.** The source assumes only f.D1qL and claims (14.1.32) at every iteration before
termination. The statement assumes f.D1pL, c.D1pL and h.L, and holds at successful iterations
that are not followed by termination. As in Lemmas 14.1.7 and 14.1.8, $(1 - \theta)$ is replaced
by $(\varsigma - \theta)$.

**Typo.** The source writes $f$ and $L_{f,p}$ for $w$ and $L_{w,p}$.

**Generalization.** In the second case the source bounds the decreases with
$\min_j \epsilon_j^{j+1}$. The statement gives the bounds with $\epsilon_j^{j+1}$ for the order
$j$ of Lemma 14.1.8, which implies the bounds of the source.

The ratio $\rho_k$ is `Optimization.arqpRatio`. The proof specializes
`CartisGouldToint.Chapter14.lemma_14_1_9_anchored` with $X_0 = \mathbb{R}^n$. -/
theorem lemma_14_1_9 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    (q = 1 → δ (k + 1) 1 = 1 →
      kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p) ≤
        Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h p (s k) ∧
      P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p)) ≤
        (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1))))) ∧
    ((1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δ (k + 1) j) →
      ∃ j ∈ Finset.Icc 1 q,
        kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1) ≤
          Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
            (ftaylorSeries ℝ c (x k)) h p (s k) ∧
        P.η₁ * (kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1)) ≤
          (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1))))) := by
  exact lemma_14_1_9_anchored hr hθς (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hk hsucc h1

end Complexity

section Theorem

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Theorem 14.1.10(1)** of [cartis2022evaluation]. Let $q = 1$, and let $h$ and the feasible set
$X$ be convex. Assume f.D1pL, c.D1pL, h.L, w.Bb on $X$ with the bound $w_{\mathrm{low}}$, and
$\theta < \varsigma$. Consider a run of ARqpC with the initial radius $\delta_{0,1} = 1$. Then
the run terminates at a first iteration $k_\epsilon$, at which
$\phi^1_{w,1}(x_{k_\epsilon}) \le \epsilon_1$, and
$$\#_f \le \kappa_A \frac{w(x_0) - w_{\mathrm{low}}}{\Delta} + \kappa_C \quad \text{(14.1.34)},
  \qquad \#_D \le \frac{w(x_0) - w_{\mathrm{low}}}{\Delta} + 2 \quad \text{(14.1.35)}.$$
Here $\#_f = k_\epsilon + 1$ is the number of evaluations of $f$ and $c$, $\#_D$ is one plus the
number of successful iterations before $k_\epsilon$, which is the number of evaluations of their
derivatives, $\Delta = \eta_1 \kappa_{\Delta m} \epsilon_1^{(p+1)/p}$ with $\kappa_{\Delta m}$ =
`CartisGouldToint.Chapter14.kappaDm1`, $\kappa_A = 1 + |\log \gamma_1| / \log \gamma_2$ and
$\kappa_C = (|\log \gamma_1| + \log(\sigma_{\max} / \sigma_0)) / \log \gamma_2 + 2$. This is
$O(\epsilon_1^{-(p+1)/p})$.

**Correction.** The constant $\kappa^{s,1}$ of the source contains $(1 - \theta)$, which is
$(\varsigma - \theta)$ here, with $\theta < \varsigma$. With this change
$1 / (\eta_1 \kappa_{\Delta m}) = \kappa^{s,1}$ and $\kappa^{a,1} = \kappa^{s,1} \kappa_A$.

**Reading.** The source assumes that the algorithm keeps the first-order radius equal to $1$.
Here this follows from $\delta_{0,1} = 1$, because Algorithm 14.1.2 never halves the first-order
radius when $h$ and $X$ are convex.

**Generalization.** The hypothesis h.S0 is not used.

Termination is `Optimization.IsFirstHit` of the test `CartisGouldToint.Chapter14.arqpcStop`. The
counts are `Optimization.funEvalCount` and `Optimization.derivEvalCount` of the successful
iterations, and the measure is taken over the feasible displacements. -/
theorem theorem_14_1_10_i (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) (hq : q = 1) (hconv : ConvexOn ℝ univ h)
    (hXc : Convex ℝ X) (hδ₀ : δ₀ 1 = 1) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧
      Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f (x kε)) (ftaylorSeries ℝ c (x kε))
        h 1 1 {e | x kε + e ∈ X} ≤ ε 1 ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) /
            (P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p)))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) /
          (P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p))) + 2 := by
  have hA := AnchoredCompositeBounds.of_global hf hc (hr.one_le_q.trans hr.q_le_p)
    (compositeSublevel f c h X (x 0))
  exact hr.complexity_unit hA.lipschitzDerivsAnchored_f hA.lipschitzDerivsAnchored_c hL hconv hXc
    hA.one_le hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge (subset_univ X)
    (fun _ hy hw => ⟨hy, hw⟩) hq hθς P.σmin_pos hδ₀
    (Optimization.one_notMem_compositeHalvingSet hconv hXc) hw

/-- **Theorem 14.1.10(2)** of [cartis2022evaluation], under the anchored assumptions. Let
$X_0 \supseteq X$ be a set on which the anchored composite bounds hold with the anchor set
$\{y \in X : w(y) \le w(x_0)\}$; this is f.D1pLaB.X of the source. Assume h.L, h.S0, w.Bb on $X$
with the bound $w_{\mathrm{low}}$, and $\theta < \varsigma$. Let $m_\epsilon > 0$ with
$m_\epsilon \le \epsilon_j^{j+1}$ for every $j \in [1 : q]$, for example
$m_\epsilon = \min_j \epsilon_j^{j+1}$. Then every run of ARqpC terminates at a first iteration
$k_\epsilon$ at which $x_{k_\epsilon}$ is an $(\epsilon, \delta_\epsilon)$-approximate $q$-th
order minimizer (14.1.9) over $X$ for some $\delta_\epsilon \in (0, 1]^q$, and
$$\#_f \le \kappa_A \frac{w(x_0) - w_{\mathrm{low}}}{\Delta} + \kappa_C \quad \text{(14.1.36)},
  \qquad \#_D \le \frac{w(x_0) - w_{\mathrm{low}}}{\Delta} + 2 \quad \text{(14.1.37)},$$
with $\#_f$, $\#_D$, $\kappa_A$ and $\kappa_C$ as in
`CartisGouldToint.Chapter14.theorem_14_1_10_i`, and
$\Delta = \eta_1 \kappa_{\Delta m} m_\epsilon$ with $\kappa_{\Delta m}$ =
`CartisGouldToint.Chapter14.kappaDm2`. This is $O(\max_j \epsilon_j^{-(j+1)})$.

**Correction.** The source writes $(1 - \theta)$ for $(\varsigma - \theta)$ in the constant
$\kappa^{s,2}$. See `CartisGouldToint.Chapter14.theorem_14_1_10_ii`.

**Typo.** The factor $3j!$ in the constant $\kappa^{s,2}$ is $3q!$.

The radius policy (14.1.28) holds for every run
(`CartisGouldToint.Chapter14.algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`). -/
theorem theorem_14_1_10_ii_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) {X₀ : Set ℝⁿ}
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) {mε : ℝ} (hmε0 : 0 < mε)
    (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε))
          (ftaylorSeries ℝ c (x kε)) h {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε)) + 2 :=
  hr.complexity (Kf := Optimization.finMax 1 Lf p)
    (Kc := Real.sqrt m * Optimization.finMax 0 Lc p) hA.lipschitzDerivsAnchored_f
    hA.lipschitzDerivsAnchored_c hL hS.1 hS.2 hA.one_le
    hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge (zero_le_one.trans Optimization.le_finMax_left)
    (mul_nonneg (Real.sqrt_nonneg _) Optimization.le_finMax_left) compositeLipschitzW_eq.ge
    (one_le_compositeLipschitzW_of hL.nonneg) (fun i hi _ hy => (hA.jet_bounds hy).1 i hi)
    (fun i hi _ hy => (hA.jet_bounds hy).2 i hi) hX (fun _ hy hw => ⟨hy, hw⟩) hθς P.σmin_pos hw
    hmε0 hmε

/-- **Theorem 14.1.10(2)** of [cartis2022evaluation]. Assume f.D1pL, c.D1pL, h.L, h.S0, w.Bb on $X$
with the bound $w_{\mathrm{low}}$, and $\theta < \varsigma$. Let $m_\epsilon > 0$ with
$m_\epsilon \le \epsilon_j^{j+1}$ for every $j \in [1 : q]$, for example
$m_\epsilon = \min_j \epsilon_j^{j+1}$. Then every run of ARqpC terminates at a first iteration
$k_\epsilon$ at which $x_{k_\epsilon}$ is an $(\epsilon, \delta_\epsilon)$-approximate $q$-th
order minimizer (14.1.9) over $X$ for some $\delta_\epsilon \in (0, 1]^q$, and
$$\#_f \le \kappa_A \frac{w(x_0) - w_{\mathrm{low}}}{\Delta} + \kappa_C \quad \text{(14.1.36)},
  \qquad \#_D \le \frac{w(x_0) - w_{\mathrm{low}}}{\Delta} + 2 \quad \text{(14.1.37)},$$
with $\#_f$, $\#_D$, $\kappa_A$ and $\kappa_C$ as in
`CartisGouldToint.Chapter14.theorem_14_1_10_i`, and
$\Delta = \eta_1 \kappa_{\Delta m} m_\epsilon$ with $\kappa_{\Delta m}$ =
`CartisGouldToint.Chapter14.kappaDm2`. This is $O(\max_j \epsilon_j^{-(j+1)})$.

**Correction.** The constant $\kappa^{s,2}$ of the source contains $(1 - \theta)$, which is
$(\varsigma - \theta)$ here, with $\theta < \varsigma$. With this change
$1 / (\eta_1 \kappa_{\Delta m}) = \kappa^{s,2}$.

**Typo.** The factor $3j!$ in the constant $\kappa^{s,2}$ is $3q!$.

**Reading.** The source assumes the radius policy (14.1.28). Here it is proved for every run
(`CartisGouldToint.Chapter14.algorithm_14_1_1.radius_policy`).

**Generalization.** The source states this part for nonconvex $h$ or $q > 1$, with
$\min_j \epsilon_j^{j+1}$. The statement holds for all $h$, $X$ and $q$, with any positive lower
bound $m_\epsilon$.

The proof specializes `CartisGouldToint.Chapter14.theorem_14_1_10_ii_anchored` with
$X_0 = \mathbb{R}^n$. -/
theorem theorem_14_1_10_ii (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) {mε : ℝ} (hmε0 : 0 < mε)
    (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε))
          (ftaylorSeries ℝ c (x kε)) h {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε)) + 2 := by
  exact theorem_14_1_10_ii_anchored hr hθς (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hS hw hmε0 hmε

end Theorem

/-! ### Corollary 14.1.11: sharpness for $q = 1$ and convex $h$ -/

/-- For $q = 1$, global minimizers of the model are outputs of Algorithm 14.1.2. Let $p \ge 1$, let
$h$ be convex with h.L, let $X$ be convex and $\epsilon_1 \ge 0$. If $x + s \in X$ and $s$
minimizes the model $\hat m$ at $x$ over the feasible steps $\{t : x + t \in X\}$, then $(s, 1)$
is an output of Algorithm 14.1.2 with $q = 1$: a long step is returned at once, and for a short
step the displacement $0$ passes the first-order test with radius $1$, by Lemma 14.1.1 for
$\hat m$. -/
theorem algorithm_14_1_2_of_isMinOn {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {Lh : ℝ}
    {X : Set ℝⁿ} {p : ℕ} (hp : 1 ≤ p) (hL : AssumptionHLip h Lh) (hconv : ConvexOn ℝ univ h)
    (hX : Convex ℝ X) (P : ARqpCParams) {ε : ℕ → ℝ} (hε : 0 ≤ ε 1) {σ : ℝ} {x s : ℝⁿ}
    (hs : x + s ∈ X)
    (hmin : IsMinOn (Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ) {t | x + t ∈ X} s) :
    algorithm_14_1_2 f c h X p 1 P ε σ x s (fun _ => 1) :=
  Optimization.isARqpCDetailedStep_of_isMinOn hp hL hconv hX P.toARqpParams (halvingSet h X) hε hs
    hmin

section Corollary

open scoped RealInnerProductSpace
open Chapter02 (e₀ norm_e₀ norm_smul_e₀ inner_e₀_smul)
open Chapter03 (norm_eq_abs_inner_e₀)

private theorem smul_e₀_apply (r : ℝ) (i : Fin 1) : (r • e₀) i = r := by
  fin_cases i
  simp [e₀]

/-- The vector function $c(y) = g(y_0) e_0$ on $\mathbb{R}^1$ that lifts a function $g$ of one
variable. -/
private noncomputable def liftC (g : ℝ → ℝ) (y : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) :=
  Optimization.ridge g e₀ y • e₀

private theorem taylorSum_liftC {g : ℝ → ℝ} {p j : ℕ} (hg : ContDiff ℝ p g) (hj1 : 1 ≤ j)
    (hjp : j ≤ p) {y : EuclideanSpace ℝ (Fin 1)} {α : ℝ}
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α) (t : EuclideanSpace ℝ (Fin 1)) :
    (ftaylorSeries ℝ (liftC g) y).taylorSum j t = (g ⟪e₀, y⟫ - α * ⟪e₀, t⟫) • e₀ := by
  have hgj : ContDiff ℝ j g := hg.of_le (by exact_mod_cast hjp)
  have hd' : Optimization.IsSpikeJetOf j g 1 ⟪e₀, y⟫ α :=
    ⟨hd.1, fun i hi1 hij hi => hd.2 i hi1 (hij.trans hjp) hi⟩
  rw [← taylorPolynomial_eq_taylorSum, show liftC g = fun y => Optimization.ridge g e₀ y • e₀ from
    rfl, taylorPolynomial_smul_const (Optimization.contDiff_ridge hgj).contDiffAt,
    Optimization.taylorPolynomial_ridge_spike hgj le_rfl hj1 hd']
  simp


/-- The norm of $\mathbb{R}^1$ satisfies h.L with $L_{h,0} = 1$. -/
private theorem assumptionHLip_norm : AssumptionHLip (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) 1 :=
  ⟨zero_le_one, fun a b => by rw [one_mul]; exact abs_norm_sub_norm_le a b⟩

section LiftC

variable {g : ℝ → ℝ} {p : ℕ} {y : EuclideanSpace ℝ (Fin 1)} {α : ℝ}

private theorem compositeTaylorDecrement_liftC (hg : ContDiff ℝ p g) {j : ℕ} (hj1 : 1 ≤ j)
    (hjp : j ≤ p) (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α)
    (t : EuclideanSpace ℝ (Fin 1)) :
    Optimization.compositeTaylorDecrement (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) j t =
      |g ⟪e₀, y⟫| - |g ⟪e₀, y⟫ - α * ⟪e₀, t⟫| := by
  rw [Optimization.compositeTaylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_fun, taylorPolynomial_zero_fun,
    taylorSum_liftC hg hj1 hjp hd, taylorSum_liftC hg hj1 hjp hd, norm_smul_e₀, norm_smul_e₀,
    inner_zero_right]
  ring_nf

private theorem compositeRegularizedModel_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α) (σ : ℝ) (t : EuclideanSpace ℝ (Fin 1)) :
    Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ t =
      g ⟪e₀, y⟫ + Optimization.negMonomialRegModel p 1 σ α ⟪e₀, t⟫ +
        (|g ⟪e₀, y⟫ - α * ⟪e₀, t⟫| - (g ⟪e₀, y⟫ - α * ⟪e₀, t⟫)) := by
  rw [Optimization.compositeRegularizedModel_def, Optimization.regularizedModel_def,
    ← taylorPolynomial_eq_taylorSum, taylorPolynomial_zero_fun, taylorSum_liftC hg hp le_rfl hd,
    norm_smul_e₀,
    Optimization.negMonomialRegModel, norm_eq_abs_inner_e₀ t]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

/-- If the derivative of $g$ at $y_0$ is $-\alpha$, its derivatives of orders $2$ to $p$ there
vanish, and $g(y_0) \ge 2 \ge \alpha \ge 0$, then the first-order measure of $w = |c|$ for the
lifted $c$ is $\phi^1_{w,1}(y) = \alpha$. -/
private theorem compositeTaylorMeasure_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α) (hg2 : 2 ≤ g ⟪e₀, y⟫) (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2) :
    Optimization.compositeTaylorMeasure (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) 1 1 univ = α := by
  rw [Optimization.compositeTaylorMeasure_eq_sSup]
  have hdec := compositeTaylorDecrement_liftC hg le_rfl hp hd
  refine IsGreatest.csSup_eq ⟨⟨e₀, ⟨by simp, mem_univ _⟩, ?_⟩, ?_⟩
  · rw [hdec, real_inner_self_eq_norm_sq, norm_e₀, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    ring
  · rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
    have ht1 : |⟪e₀, t⟫| ≤ 1 := by
      rw [← norm_eq_abs_inner_e₀]; simpa using ht
    have h1 := (abs_le.1 ht1).1
    have h2 := (abs_le.1 ht1).2
    have hat : α * ⟪e₀, t⟫ ≤ α := by nlinarith
    have hat' : -α ≤ α * ⟪e₀, t⟫ := by nlinarith
    rw [hdec, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- For such a jet of $g$ with $\sigma > 0$ and $\alpha > 0$, if the Taylor model of $g$ stays
nonnegative at the minimizer of the one-dimensional monomial model, then that minimizer is a
global minimizer of the composite model of $|c|$, with a model value less than at $0$. -/
private theorem isMinOn_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α) {σ : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    (hpos : 0 ≤ g ⟪e₀, y⟫ - α * Optimization.monomialMinimizer p 1 σ α) :
    IsMinOn (Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ) univ
        (Optimization.monomialMinimizer p 1 σ α • e₀) ∧
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
        (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ
          (Optimization.monomialMinimizer p 1 σ α • e₀) <
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
        (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ 0 := by
  obtain ⟨hm, hv, -⟩ := Optimization.isMinOn_neg_monomial_add_regularization le_rfl hp hσ hα
  rw [← Optimization.monomialMinimizer] at hm hv
  set τ := Optimization.monomialMinimizer p 1 σ α
  have hτ : 0 < τ := Optimization.monomialMinimizer_pos hσ hα
  have hmod := compositeRegularizedModel_liftC hg hp hd σ
  have hval : Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ (τ • e₀) =
      g ⟪e₀, y⟫ + Optimization.negMonomialRegModel p 1 σ α τ := by
    rw [hmod, inner_e₀_smul, abs_of_nonneg hpos, sub_self, add_zero]
  refine ⟨isMinOn_iff.2 fun t _ => ?_, ?_⟩
  · rw [hval, hmod]
    have := isMinOn_iff.1 hm ⟪e₀, t⟫ (mem_univ _)
    have := le_abs_self (g ⟪e₀, y⟫ - α * ⟪e₀, t⟫)
    linarith
  · rw [hval, hmod, inner_zero_right, mul_zero, sub_zero, hv]
    have := le_abs_self (g ⟪e₀, y⟫)
    have h0 : Optimization.negMonomialRegModel p 1 σ α 0 = 0 := by
      simp [Optimization.negMonomialRegModel]
    rw [h0]
    have : 0 < (((p - 1 + 1 : ℕ) : ℝ) / ((p + 1) * (1 ! : ℕ))) * α * τ ^ 1 := by positivity
    linarith

end LiftC

/-- **Corollary 14.1.11** of [cartis2022evaluation] (slow convergence of ARqpC for $q = 1$ and
convex $h$). Let $p \ge 1$ and fix ARqpC constants. Let $n = m = 1$, $f = 0$, which satisfies
f.D1pL with constants $1$, and $h = \|\cdot\|$, which is convex and satisfies h.L with
$L_{h,0} = 1$ and h.S0. There is $L \ge 1$, which depends only on $p$ and the constants, such
that for every $\epsilon \in (0, 1]$ there is $c : \mathbb{R}^1 \to \mathbb{R}^1$ with the
following properties:
* $c$ satisfies c.D1pL with all constants equal to $L$, $\|c(0)\| \le L$, and $c(y)_0 \ge 2$ for
  every $y$, so that w.Bb holds with $w_{\mathrm{low}} = 0$ and
  $w(x_0) - w_{\mathrm{low}} \le L$ for every $\epsilon$;
* there is a run of ARqpC with $q = 1$, $\epsilon_1 = \epsilon$, $\delta_0 = 1$ and $x_0 = 0$
  that terminates first at $k_\epsilon = \lceil \epsilon^{-(p+1)/p} \rceil$, with $\rho_k = 1$
  for every $k < k_\epsilon$;
* $\phi^1_{w,1}(x_{k_\epsilon}) \le \epsilon$, and $\phi^1_{w,1}(x_k) > \epsilon$ for every
  $k < k_\epsilon$;
* the run evaluates $c$ at least $\epsilon^{-(p+1)/p} + 1$ times, and its derivatives at least
  $\epsilon^{-(p+1)/p} + 1$ times.

So the bounds of Theorem 14.1.10(1) are sharp in order.

**Generalization.** The source fixes $\sigma_0 = p!$ and takes $\epsilon \le \frac12$. The
statement holds for all ARqpC constants and every $\epsilon \in (0, 1]$.

The function is $c(y) = g(y_0) e_0$, where $g$ is the interpolant of the slow example of Theorem
12.2.15 (`Optimization.exists_slowTaylorOrder_interpolant` with $q = 1$, for any $\sigma_0$),
shifted so that $g \ge 2$. The one-line proof of the source takes $w = |c|$ and does not check
that the slow steps of that example are admissible steps of ARqpC for $|c|$. They are: since
$|t| \ge t$, the composite model $|T_{c,p}(x_k, s)| + \sigma_0 \|s\|^{p+1} / (p+1)!$ lies above
the smooth model $T_{c,p}(x_k, s) + \sigma_0 \|s\|^{p+1} / (p+1)!$ and agrees with it at the
global minimizer $s_k$ of the smooth model, where $T_{c,p}(x_k, s_k) = c(x_{k+1}) > 0$. So $s_k$
is a global minimizer of the composite model and an output of Algorithm 14.1.2
(`CartisGouldToint.Chapter14.algorithm_14_1_2_of_isMinOn`). Since $c(x_k) \ge 2 \ge |c'(x_k)|$,
the measure is $\phi^1_{w,1}(x_k) = |c'(x_k)| = \epsilon + \omega_k$, as in the smooth case. -/
theorem corollary_14_1_11 {p : ℕ} (hp : 1 ≤ p) (P : ARqpCParams) :
    Chapter12.AssumptionD1pL (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ)) p (fun _ => 1) ∧
    AssumptionHLip (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) 1 ∧
    AssumptionHS0 (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) ∧
    ConvexOn ℝ univ (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) ∧
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1),
        AssumptionCD1pL c p (fun _ => L) ∧ ‖c 0‖ ≤ L ∧ (∀ y, 2 ≤ c y 0) ∧
        AssumptionWBb (fun _ => 0) c (fun v => ‖v‖) univ 0 ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ)
          (d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)),
          algorithm_14_1_1 (fun _ => 0) c (fun v => ‖v‖) univ p 1 P (fun _ => ε) (fun _ => 1)
            x s σ δ δs d dm ∧ x 0 = 0 ∧
          Optimization.IsFirstHit
            (arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε) x s σ δ d)
            ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊, Optimization.arqpRatio (fun y => 0 + ‖c y‖)
            (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σ k)) x s k = 1) ∧
          ε ^ (-((p + 1 : ℝ) / p)) + 1 ≤
            (Optimization.funEvalCount ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ : ℝ) ∧
          ε ^ (-((p + 1 : ℝ) / p)) + 1 ≤ (Optimization.derivEvalCount (fun k => P.η₁ ≤
            Optimization.arqpRatio (fun y => 0 + ‖c y‖)
              (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σ k)) x s k)
            ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ : ℝ) ∧
          Optimization.compositeTaylorMeasure
            (ftaylorSeries ℝ (fun _ => (0 : ℝ)) (x ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊))
            (ftaylorSeries ℝ c (x ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊)) (fun v => ‖v‖) 1 1 univ ≤ ε ∧
          ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊, ε < Optimization.compositeTaylorMeasure
            (ftaylorSeries ℝ (fun _ => (0 : ℝ)) (x k)) (ftaylorSeries ℝ c (x k))
            (fun v => ‖v‖) 1 1 univ := by
  have hf0 : Chapter12.AssumptionD1pL (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ)) p
      (fun _ => 1) :=
    .of_iteratedFDerivLipschitzOn contDiff_const (fun _ _ => le_rfl) fun j _ =>
      iteratedFDerivLipschitzOn_iff.2 fun a _ b _ => by simp
  refine ⟨hf0, assumptionHLip_norm, ⟨Optimization.isSubadditive_norm, norm_zero⟩,
    convexOn_norm convex_univ, ?_⟩
  have hσ₀ := P.σ₀_pos
  obtain ⟨L₀, B, hL₀, hB, hG⟩ := Optimization.exists_slowTaylorOrder_interpolant (q := 1) le_rfl
    hp (c := (p ! : ℝ) / P.σ₀) (by positivity)
  set L : ℝ := max 1 (max L₀ (B + (B + 2))) with hLdef
  refine ⟨L, le_max_left _ _, fun ε hε hε1 => ?_⟩
  have hR : ((p - 1 + 1 : ℕ) : ℝ) = p := by rw [Nat.sub_add_cancel hp]
  set kε : ℕ := ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ with hkε
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (by
    rw [hkε]; exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne')
  have hkεpos : (0 : ℝ) < kε := by exact_mod_cast hkε1
  set a : ℕ → ℝ := fun k => ε + ε * ((kε : ℝ) - k) / kε with ha
  set st : ℕ → ℝ := fun k => Optimization.monomialMinimizer p 1 P.σ₀ (a k) with hst
  set xr : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, st i with hxr
  have hxs : ∀ k, xr (k + 1) = xr k + st k := fun k => by
    simp only [hxr, Finset.sum_range_succ]
  have hstc : ∀ k, st k = ((p ! : ℝ) / P.σ₀ * a k) ^ (1 / ((p - 1 + 1 : ℕ) : ℝ)) := fun k => by
    simp only [hst, Optimization.monomialMinimizer, Nat.sub_self, Nat.factorial_zero,
      Nat.cast_one, mul_one]
    congr 1
    field_simp
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε kε xr hε hε1 (by rw [hkε, hR])
    fun k _ => by rw [hxs k, hstc k]
  clear_value kε
  -- the sequence `a_k = ε + ω_k`
  have ha_ge : ∀ k ≤ kε, ε ≤ a k := fun k hk => by
    simp only [ha]
    have : (0 : ℝ) ≤ ε * ((kε : ℝ) - k) / kε := by
      have : (k : ℝ) ≤ kε := by exact_mod_cast hk
      have : 0 ≤ (kε : ℝ) - k := by linarith
      positivity
    linarith
  have ha_gt : ∀ k < kε, ε < a k := fun k hk => by
    simp only [ha]
    have : (0 : ℝ) < ε * ((kε : ℝ) - k) / kε := by
      have : (k : ℝ) < kε := by exact_mod_cast hk
      have : 0 < (kε : ℝ) - k := by linarith
      positivity
    linarith
  have ha_le : ∀ k, a k ≤ 2 := fun k => by
    simp only [ha]
    have : ε * ((kε : ℝ) - k) / kε ≤ ε := by
      rw [div_le_iff₀ hkεpos]
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      nlinarith
    linarith
  have ha_eq : a kε = ε := by simp only [ha]; rw [sub_self, mul_zero, zero_div, add_zero]
  -- the shifted interpolant `g = (B + 2) + G ≥ 2`
  set g : ℝ → ℝ := fun t => (B + 2) + G t with hgdef
  have hg : ContDiff ℝ p g := contDiff_const.add hGc
  have hgder : ∀ j, 1 ≤ j → ∀ t, iteratedDeriv j g t = iteratedDeriv j G t := fun j hj t =>
    iteratedDeriv_const_add (by omega) _
  have hg2 : ∀ t, 2 ≤ g t := fun t => by
    have := hGB 0 (Nat.zero_le p) t
    rw [iteratedDeriv_zero] at this
    simp only [hgdef]
    linarith [(abs_le.1 this).1]
  have hgD : Chapter12.AssumptionD1pL g p (fun _ => L) := by
    refine Chapter12.assumptionD1pL_real hg (fun s t => ?_) (fun j hj t => ?_)
    · rw [hgder p hp, hgder p hp]; exact hGL s t
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [iteratedDeriv_zero]
        have := hGB 0 (Nat.zero_le p) t
        rw [iteratedDeriv_zero] at this
        simp only [hgdef]
        calc |B + 2 + G t| ≤ |B + 2| + |G t| := abs_add_le _ _
          _ ≤ B + (B + 2) := by rw [abs_of_nonneg (by linarith)]; linarith
      · rw [hgder j hj0 t]
        linarith [hGB j hj t]
  have hspike : ∀ k ≤ kε, Optimization.IsSpikeJetOf p g 1 (xr k) (a k) := fun k hk =>
    ⟨by rw [hgder 1 le_rfl, (hGd k hk).1], fun j hj1 hjp hj => by
      rw [hgder j hj1, (hGd k hk).2 j hj1 hjp hj]⟩
  have hgval : ∀ k < kε, g (xr (k + 1)) = g (xr k) - a k * st k := fun k hk => by
    simp only [hgdef]
    rw [hGf k hk, hxs k]
    simp
    ring
  -- the problem
  set c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := liftC g with hcdef
  have hcD : AssumptionCD1pL c p (fun _ => L) := by
    refine .of_lipschitz_component ((Optimization.contDiff_ridge hg).smul contDiff_const)
      (fun _ _ => zero_le_one.trans (le_max_left _ _)) fun i j hj => ?_
    have hci : (fun y => c y i) = Optimization.ridge g e₀ := funext fun y => smul_e₀_apply _ i
    rw [hci]
    exact Optimization.iteratedFDerivLipschitzOn_ridge hg
      (by exact_mod_cast (Finset.mem_Icc.1 hj).2) norm_e₀.le
      (zero_le_one.trans (le_max_left _ _))
      (fun a b => (hgD.lipschitz j hj).abs_iteratedDeriv_sub_le (mem_univ a) (mem_univ b))
  have hc0 : ∀ y, c y 0 = g ⟪e₀, y⟫ := fun y => smul_e₀_apply _ 0
  have hnc : ∀ y, ‖c y‖ = g ⟪e₀, y⟫ := fun y => by
    rw [hcdef, liftC, norm_smul_e₀, Optimization.ridge_apply,
      abs_of_nonneg (by linarith [hg2 ⟪e₀, y⟫])]
  -- the iterates
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • e₀ with hxdef
  set sv : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => st k • e₀ with hsvdef
  set σs : ℕ → ℝ := fun _ => P.σ₀ with hσs
  have hxe : ∀ k, ⟪e₀, x k⟫ = xr k := fun k => inner_e₀_smul _
  have hxsv : ∀ k, x (k + 1) = x k + sv k := fun k => by
    simp only [hxdef, hsvdef, hxs k, add_smul]
  have hspk : ∀ k ≤ kε, Optimization.IsSpikeJetOf p g 1 ⟪e₀, x k⟫ (a k) := fun k hk => by
    rw [hxe]; exact hspike k hk
  have hapos : ∀ k ≤ kε, 0 < a k := fun k hk => hε.trans_le (ha_ge k hk)
  have hstpos : ∀ k ≤ kε, 0 < st k := fun k hk =>
    Optimization.monomialMinimizer_pos hσ₀ (hapos k hk)
  have hnext : ∀ k < kε, 0 ≤ g ⟪e₀, x k⟫ - a k * Optimization.monomialMinimizer p 1 P.σ₀ (a k) :=
    fun k hk => by
      rw [hxe, show Optimization.monomialMinimizer p 1 P.σ₀ (a k) = st k from rfl, ← hgval k hk]
      linarith [hg2 (xr (k + 1))]
  have hmin : ∀ k < kε, _ := fun k hk => isMinOn_liftC hg hp (hspk k hk.le) hσ₀
    (hapos k hk.le) (hnext k hk)
  -- the measures
  have hmeas : ∀ k ≤ kε, Optimization.compositeTaylorMeasure
      (ftaylorSeries ℝ (fun _ => (0 : ℝ)) (x k)) (ftaylorSeries ℝ c (x k))
      (fun v => ‖v‖) 1 1 univ = a k := fun k hk =>
    compositeTaylorMeasure_liftC hg hp (hspk k hk) (hg2 _) (hapos k hk).le (ha_le k)
  have hU : ∀ y : EuclideanSpace ℝ (Fin 1), {e : EuclideanSpace ℝ (Fin 1) | y + e ∈ univ} = univ :=
    fun y => by ext; simp
  -- Step-1 witnesses
  have hw : ∀ k j, ∃ e : EuclideanSpace ℝ (Fin 1),
      Optimization.IsApproxMeasureStep
        ((arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)).dec j) 1 univ P.ς e ∧
      (arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)).dec j e =
        P.ς * Optimization.decrementMeasure
          ((arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)).dec j) 1 univ := fun k j =>
    Optimization.exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0)
      zero_le_one (Optimization.continuous_compositeTaylorDecrement _ _ _ j
        assumptionHLip_norm.continuous).continuousOn
      (Optimization.compositeTaylorDecrement_zero_right _ _ _ j) ⟨P.ς_pos.le, P.ς_le_one⟩
  choose d hd hdeq using hw
  set δ : ℕ → ℕ → ℝ := fun _ _ => 1 with hδ
  have hstop₁ : ∀ k ≤ kε, (Optimization.arqpStop₁ P.toARqpParams 1 (fun _ => ε)
      (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) δ d k ↔ k = kε) := by
    intro k hk
    have hd1 : (arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)).dec 1 (d k 1) =
        P.ς * a k := by
      rw [hdeq, ← hmeas k hk]; rfl
    simp only [Optimization.arqpStop₁_iff, Finset.Icc_self,
      Finset.mem_singleton, forall_eq, hd1, hδ, one_pow, mul_one, Nat.factorial_one,
      Nat.cast_one, div_one]
    constructor
    · intro h
      by_contra hne
      have := ha_gt k (lt_of_le_of_ne hk hne)
      nlinarith [P.ς_pos]
    · rintro rfl
      rw [ha_eq]
  -- Step 2: global model minimizers, outputs of Algorithm 14.1.2
  have halg : ∀ k < kε, algorithm_14_1_2 (fun _ => 0) c (fun v => ‖v‖) univ p 1 P (fun _ => ε)
      (σs k) (x k) (sv k) (fun _ => 1) := fun k hk =>
    algorithm_14_1_2_of_isMinOn hp assumptionHLip_norm (convexOn_norm convex_univ) convex_univ P
      (ε := fun _ => ε) hε.le (mem_univ _) (by rw [hU]; exact (hmin k hk).1)
  have hdm : ∀ k, ∃ e : ℕ → EuclideanSpace ℝ (Fin 1), k < kε →
      Optimization.ARqpStep univ P.toARqpParams 1 (fun _ => ε)
        (arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) (x k) (sv k) (fun _ => 1) e := by
    intro k
    by_cases hk : k < kε
    · obtain ⟨e, he⟩ := (halg k hk).exists_arqpStep assumptionHLip_norm isClosed_univ hσ₀
        (mem_univ _)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose dm hdm using hdm
  -- the ratio
  have hratio : ∀ k < kε, Optimization.arqpRatio (fun y => 0 + ‖c y‖)
      (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) x sv k = 1 := by
    intro k hk
    have hpred : Optimization.compositeTaylorDecrement (ftaylorSeries ℝ (fun _ => (0 : ℝ)) (x k))
        (ftaylorSeries ℝ c (x k)) (fun v => ‖v‖) p (sv k) = a k * st k := by
      rw [compositeTaylorDecrement_liftC hg hp le_rfl (hspk k hk.le), hxe,
        show ⟪e₀, sv k⟫ = st k from inner_e₀_smul _,
        ← hgval k hk, abs_of_nonneg (by linarith [hg2 (xr k)]),
        abs_of_nonneg (by linarith [hg2 (xr (k + 1))])]
      rw [hgval k hk]
      ring
    have hpos : 0 < a k * st k := mul_pos (hapos k hk.le) (hstpos k hk.le)
    change Optimization.reductionRatio _ (x k) (sv k)
      (Optimization.compositeTaylorDecrement _ _ _ p (sv k)) = 1
    rw [Optimization.reductionRatio_def, hpred, ← hxsv, hnc, hnc, hxe, hxe, hgval k hk,
      div_eq_one_iff_eq hpos.ne']
    ring
  have hη1 : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  -- termination
  have hstop₂ : ∀ k < kε, ¬ Optimization.arqpStop₂
      (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) sv k :=
    fun k hk h2 => (hmin k hk).2.ne h2
  have hfirst : Optimization.IsFirstHit
      (arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε) x sv σs δ d) kε :=
    ⟨Or.inl ((hstop₁ kε le_rfl).2 rfl), fun i hi h' => h'.elim
      (fun h1 => hi.ne ((hstop₁ i hi.le).1 h1)) (hstop₂ i hi)⟩
  have hbefore : ∀ k, (∀ i ≤ k, ¬ arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε)
      x sv σs δ d i) → k < kε := fun k hk => by
    by_contra hge
    exact hk kε (not_lt.1 hge) hfirst.1
  have hbefore' : ∀ k, (∀ i < k, ¬ arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε)
      x sv σs δ d i) → ¬ Optimization.arqpStop₁ P.toARqpParams 1 (fun _ => ε)
        (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) δ d k → k < kε :=
    fun k hk h1 => by
      have hle : k ≤ kε := by
        by_contra hge
        exact hk kε (not_le.1 hge) hfirst.1
      exact lt_of_le_of_ne hle fun heq => h1 ((hstop₁ k hle).2 heq)
  have hkge : ε ^ (-((p + 1 : ℝ) / p)) ≤ kε := hkε ▸ Nat.le_ceil _
  have hderiv : Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
      (fun y => 0 + ‖c y‖) (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k))
        x sv k) kε = kε + 1 := by
    classical
    rw [Optimization.derivEvalCount, Finset.filter_true_of_mem fun k hk => by
      rw [hratio k (Finset.mem_range.1 hk)]; exact hη1, Finset.card_range]
  have hc0L : ‖c 0‖ ≤ L := by
    rw [hnc, inner_zero_right]
    have := hGB 0 (Nat.zero_le p) 0
    rw [iteratedDeriv_zero] at this
    simp only [hgdef]
    linarith [(abs_le.1 this).2, le_max_right L₀ (B + (B + 2)),
      le_max_right 1 (max L₀ (B + (B + 2)))]
  refine ⟨c, hcD, hc0L, fun y => by rw [hc0]; exact hg2 _, fun y _ => by positivity, x, sv, σs, δ,
    fun _ _ => 1, d, dm, ⟨le_rfl, hp, fun _ _ => ⟨hε, hε1⟩, fun _ _ => ⟨one_pos, le_rfl⟩,
    ⟨⟨rfl, fun k hk h1 => hdm k (hbefore' k hk h1), fun k hk => ?_⟩, mem_univ _, rfl,
      fun k _ j _ => by rw [hU]; exact hd k j, fun k hk => ⟨fun _ => rfl, fun hρ =>
        (hρ (le_of_le_of_eq hη1 (hratio k (hbefore k hk)).symm)).elim⟩⟩,
    fun k hk h1 => halg k (hbefore' k hk h1)⟩, by simp [hxdef, hxr], hfirst, hratio,
    by rw [Optimization.funEvalCount_eq]; push_cast; linarith,
    by rw [hderiv]; push_cast; linarith, ?_, fun k hk => ?_⟩
  · beta_reduce
    rw [hxsv]
    exact Optimization.arAcceptance_of_one_le P.toARParams (hratio k (hbefore k hk)).ge (x k)
      (sv k) P.σmin_le_σ₀ hσ₀.le
  · rw [hmeas kε le_rfl, ha_eq]
  · rw [hmeas k hk.le]
    exact ha_gt k hk

end Corollary

end CartisGouldToint.Chapter14
