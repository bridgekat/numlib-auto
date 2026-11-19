/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.EpigraphPenalty
import NumlibSurface.ConnGouldToint.Chapter11.Section03
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Conn, Gould and Toint, Section 16.2: Composite nonsmooth equations

Section 16.2 of [conn2000trust] treats the composite problem of minimizing $h(c(x))$, where
$c : E \to Y$ is smooth and $h(y) = \max_i (p_i(y) + b_i)$ is a maximum of finitely many affine
functions. The problem is equivalent to the smooth epigraph problem of minimizing $t$ subject to
$p_i(c(x)) + b_i \le t$ for all $i$. The trust-region model replaces $c$ by its linearization and
adds a quadratic term. This module formalizes the polyhedral objective and its model, the epigraph
problem and its multipliers, the equivalence of the second-order conditions in Theorem 16.2.2, the
convergence result of Theorem 16.2.1 for the monotone nonsmooth algorithm, and the exact merit
function of Lemma 16.2.3. The penalty is `Numlib.Optimization.epigraphPenalty`, and the nonsmooth
algorithms come from `NumlibSurface.ConnGouldToint.Chapter11.Section01` and
`NumlibSurface.ConnGouldToint.Chapter11.Section03`.

## Main definitions

* Equation (16.2.1), `ConnGouldToint.Chapter16.polyhedralAffineMaximum`: the maximum
  $h(y) = \max_i (p_i(y) + b_i)$.
* Equation (16.2.2), `ConnGouldToint.Chapter16.affineResidualBranch`: one affine branch
  $p_i(y) + b_i$.
* Equation (16.2.3), `ConnGouldToint.Chapter16.polyhedralResidualValue`: the objective $h(c(x))$.
* Equation (16.2.4), `ConnGouldToint.Chapter16.polyhedralResidualModel`: the model
  $\frac{1}{2} H(s, s) + h(c(x) + J(x) s)$.
* Algorithm 16.2.1, `ConnGouldToint.Chapter16.polyhedralResidualCorrectionModel` and
  `ConnGouldToint.Chapter16.algorithm_16_2_1`: the correction model and the correction step.
* Equation (16.2.5), `ConnGouldToint.Chapter16.IsPolyhedralModelSolution`: a solution of the
  trust-region model problem.
* Equation (16.2.9), `ConnGouldToint.Chapter16.polyhedralEpigraphFeasible`: the feasible set of the
  epigraph problem.
* Equations (16.2.11)–(16.2.14), `ConnGouldToint.Chapter16.EpigraphMultiplier`: the first-order
  conditions of the epigraph problem.
* Theorem 16.2.2, `ConnGouldToint.Chapter16.epigraphCriticalCone`: the critical cone of the epigraph
  problem.
* Equations (16.2.16)–(16.2.18), `ConnGouldToint.Chapter16.IsActiveBranchCombination`: a convex
  combination of the active slopes.
* Equation (16.2.15), `ConnGouldToint.Chapter16.polyhedralEpigraphLagrangian`: the Lagrangian of the
  epigraph problem.
* Equation (16.2.23), `ConnGouldToint.Chapter16.epigraphMerit`: the exact merit function in the
  epigraph variable.

## Main results

* Equations (16.2.9)–(16.2.10), `ConnGouldToint.Chapter16.isMinOn_polyhedralEpigraph_iff`: the
  epigraph problem and the composite problem have the same minimizers.
* `ConnGouldToint.Chapter16.mem_epigraphCriticalCone_iff`: at a multiplier, the critical cone
  consists of the directions with nonpositive active derivatives and height $0$.
* `ConnGouldToint.Chapter16.isActiveBranchCombination_iff_mem_convexHull`: the active combinations
  are the convex hull of the active slopes.
* Equation (16.2.15), `ConnGouldToint.Chapter16.fderiv_fderiv_polyhedralEpigraphLagrangian`: the
  second derivative of the Lagrangian.
* Theorem 16.2.2, `ConnGouldToint.Chapter16.theorem_16_2_2`: the second-order sufficient condition
  of the epigraph problem is equivalent to the composite second-order condition.
* `ConnGouldToint.Chapter16.lipschitzWith_polyhedralAffineMaximum`: $h$ is Lipschitz with constant
  $\sum_i \|p_i\|$.
* `ConnGouldToint.Chapter16.polyhedralResidualModel_uniformAgreement`: the models agree uniformly
  with the objective after normalization.
* Theorem 16.2.1, `ConnGouldToint.Chapter16.theorem_16_2_1_monotone`: every limit point of a run of
  Algorithm 11.1.1 is Clarke stationary.
* Lemma 16.2.3, `ConnGouldToint.Chapter16.lemma_16_2_3`: for $\sigma > 1$ the merit function has the
  minimum value $h(c(x))$, attained only at $t = h(c(x))$.

## Conventions

* The Jacobian $J(x)$ is `fderiv ℝ c x`, and the second derivative $\nabla^2 c(x)$ is
  `fderiv ℝ (fderiv ℝ c) x`, applied to two directions.
* Quadratic terms $H$ are continuous bilinear forms `E →L[ℝ] E →L[ℝ] ℝ`, and $H(s, s)$ is `H s s`.
* A branch $i$ is **active** at the height $t$ if its value $a_i$ equals $t$.

## Deviations from the source

* **Correction.** Lemma 16.2.3 distinguishes the real minimum from the singleton set of minimizers.
  See `ConnGouldToint.Chapter16.lemma_16_2_3`.
* **Relational step selection.** Algorithm 16.2.1 uses an optional-correction relation with the
  derivative shift and admissibility conditions explicit. See
  `ConnGouldToint.Chapter16.polyhedralResidualCorrectionModel`,
  `ConnGouldToint.Chapter16.algorithm_16_2_1`.
* **Correction.** Theorem 16.2.2 corrects the curvature contraction in (16.2.15), distinguishing
  residual components from affine branches. See
  `ConnGouldToint.Chapter16.fderiv_fderiv_affineResidualBranch`,
  `ConnGouldToint.Chapter16.fderiv_fderiv_polyhedralEpigraphLagrangian`,
  `ConnGouldToint.Chapter16.theorem_16_2_2`.
* **Explicit Lipschitz bound.** The polyhedral maximum uses an explicit Lipschitz constant given by
  the sum of slope norms. See `ConnGouldToint.Chapter16.lipschitzWith_polyhedralAffineMaximum`.
* **Restricted algorithm and explicit bounds.** Theorem 16.2.1 treats the monotone run, with
  explicit curvature and local sufficient-decrease bounds. See
  `ConnGouldToint.Chapter16.polyhedralResidualModel_uniformAgreement`,
  `ConnGouldToint.Chapter16.theorem_16_2_1_monotone`.
* **Equation (16.2.15)** (reading). The Hessian of the epigraph Lagrangian sums the residual
  Hessians over the residual components, weighted by the convex combination of the slopes;
  equivalently it weights the Hessians of the affine branches. See
  `ConnGouldToint.Chapter16.fderiv_fderiv_polyhedralEpigraphLagrangian`.
* **Equation (16.2.24)** (reading). The minimum of the merit function is the real number $h(c(x))$,
  and the set of minimizers is the singleton $\{h(c(x))\}$. See
  `ConnGouldToint.Chapter16.lemma_16_2_3`.
-/

open Filter Topology

namespace ConnGouldToint.Chapter16

/-- **Equation (16.2.23)** of [conn2000trust]. Let $c : X \to Y$, $h : Y \to \mathbb{R}$, $x \in X$
and $\sigma, t \in \mathbb{R}$. The **exact merit function** in the epigraph variable $t$ is
$$\phi(x, \sigma, t) = (1 - \sigma) t + \sigma \max\{t, h(c(x))\} = t + \sigma \max\{0,
  h(c(x)) - t\}.$$

The definition is `Numlib.Optimization.epigraphPenalty` at the value $h(c(x))$. -/
def epigraphMerit {X Y : Type*} (c : X → Y) (h : Y → ℝ)
    (x : X) (σ t : ℝ) : ℝ :=
  Numlib.Optimization.epigraphPenalty (h (c x)) σ t

/-- **Lemma 16.2.3** of [conn2000trust]. Let $c : X \to Y$, $h : Y \to \mathbb{R}$, $x \in X$ and
$\sigma > 1$. Then $h(c(x))$ is the least value of $t \mapsto \phi(x, \sigma, t)$, and the set
of its global minimizers is $\{h(c(x))\}$.

**Reading.** Equation (16.2.24) gives the minimum value $h(c(x))$, a real number. The set of
minimizers is the singleton that contains this value.

**Correction.** The optimum is a real number and the argmin is a singleton. The theorem
distinguishes the value from the minimizer set in the printed chain of equalities.
-/
theorem lemma_16_2_3 {X Y : Type*} (c : X → Y) (h : Y → ℝ)
    (x : X) {σ : ℝ} (hσ : 1 < σ) :
    IsLeast (Set.range (epigraphMerit c h x σ)) (h (c x)) ∧
      {t | IsMinOn (epigraphMerit c h x σ) Set.univ t} = {h (c x)} := by
  have htight : epigraphMerit c h x σ (h (c x)) = h (c x) :=
    (Numlib.Optimization.epigraphPenalty_eq_iff hσ).2 rfl
  have hbound (t : ℝ) : h (c x) ≤ epigraphMerit c h x σ t :=
    Numlib.Optimization.le_epigraphPenalty hσ.le
  refine ⟨⟨⟨h (c x), htight⟩, ?_⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hbound t
  · ext t
    change IsMinOn (epigraphMerit c h x σ) Set.univ t ↔ t = h (c x)
    constructor
    · intro hmin
      have hle := isMinOn_univ_iff.mp hmin (h (c x))
      rw [htight] at hle
      exact (Numlib.Optimization.epigraphPenalty_eq_iff hσ).1 (le_antisymm hle (hbound t))
    · rintro rfl
      apply isMinOn_univ_iff.mpr
      intro y
      rw [htight]
      exact hbound y

section EpigraphConditions

variable {E Y ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]

/-- **Equation (16.2.2)** of [conn2000trust]. For a continuous linear functional $p$ on $Y$ and
$b \in \mathbb{R}$, the **affine branch** is $y \mapsto p(y) + b$. -/
def affineResidualBranch (p : Y →L[ℝ] ℝ) (b : ℝ) (y : Y) : ℝ := p y + b

/-- **Equation (16.2.1)** of [conn2000trust]. Let $\iota$ be a nonempty finite index type, and let
$p_i$ be continuous linear functionals on $Y$ and $b_i \in \mathbb{R}$. The **polyhedral
maximum** is
$$h(y) = \max_i \bigl(p_i(y) + b_i\bigr).$$
-/
noncomputable def polyhedralAffineMaximum [Nonempty ι]
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (y : Y) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ affineResidualBranch (p i) (b i) y)

/-- **Equation (16.2.3)** of [conn2000trust]. For $c : E \to Y$ and the polyhedral maximum $h$, the
**polyhedral residual objective** is $x \mapsto h(c(x))$. -/
noncomputable def polyhedralResidualValue [Nonempty ι] (c : E → Y)
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (x : E) : ℝ :=
  polyhedralAffineMaximum p b (c x)

/-- **Equation (16.2.4)** of [conn2000trust]. For $c : E \to Y$, the polyhedral maximum $h$, a
continuous bilinear form $H$ on $E$ and $x \in E$, the **composite model** is
$$m(s) = \tfrac{1}{2} H(s, s) + h\bigl(c(x) + J(x) s\bigr).$$
-/
noncomputable def polyhedralResidualModel [Nonempty ι] (c : E → Y)
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ) (x s : E) : ℝ :=
  H s s / 2 + polyhedralAffineMaximum p b (c x + fderiv ℝ c x s)

/-- **Algorithm 16.2.1** of [conn2000trust], correction model. Let $x, s, z \in E$ and let $H_{CS}$
be a continuous bilinear form on $E$. The **correction model** is
$$m_{CS}(d) = \tfrac{1}{2} H_{CS}(d, d) + h\bigl(c(x + s) + J(x + z) d\bigr),$$
the polyhedral maximum of the residual at the original trial point $x + s$, linearized with the
Jacobian at the shifted point $x + z$.

The shift $z$ is the argument `shift`.

**Reading.** The correction model is parameterized by the derivative evaluation shift and the
algorithm is an optional one-step relation with explicit radius, size and decrease tests inherited
from Chapter 11.
-/
noncomputable def polyhedralResidualCorrectionModel [Nonempty ι] (c : E → Y)
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (HCS : E →L[ℝ] E →L[ℝ] ℝ)
    (x s shift d : E) : ℝ :=
  HCS d d / 2 + polyhedralAffineMaximum p b (c (x + s) + fderiv ℝ c (x + shift) d)

/-- **Algorithm 16.2.1** of [conn2000trust]. It is Step 2 of Algorithm 11.3.1 for the polyhedral
residual objective $h \circ c$, the composite model $m$ of (16.2.4) at $x$, and the correction
model $m_{CS}$. The step $s$ and the correction form a valid step if $\Delta \ge 0$, $\tau > 1$,
$\|s\| \le \Delta$ in the trust-region seminorm, the required decrease $r$ satisfies
$0 \le r \le m(0) - m(s)$, each proposed correction $d$ satisfies $m_{CS}(d) \le m_{CS}(0)$ and
$\|s + d\| \le \tau \Delta$, and the correction is the proposal if it does not increase
$h \circ c$ at the trial point, and $0$ otherwise.

The step is `ConnGouldToint.Chapter11.OptionalCorrectionStep`.

**Reading.** The correction model is parameterized by the derivative evaluation shift and the
algorithm is an optional one-step relation with explicit radius, size and decrease tests inherited
from Chapter 11.
-/
def algorithm_16_2_1 [Nonempty ι] (c : E → Y) (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ)
    (H HCS : E →L[ℝ] E →L[ℝ] ℝ) (normK : Seminorm ℝ E) (x s shift : E)
    (Δ τ required : ℝ) (proposal : Option E) (correction : E) : Prop :=
  Chapter11.OptionalCorrectionStep (polyhedralResidualValue c p b)
    (polyhedralResidualModel c p b H x) (polyhedralResidualCorrectionModel c p b HCS x s shift)
    normK x s Δ τ required proposal correction

/-- **Equation (16.2.5)** of [conn2000trust]. A step $s$ **solves the trust-region model problem**
if $\|s\| \le \Delta$ and $s$ minimizes the composite model $m$ of (16.2.4) over the closed ball
$\{s : \|s\| \le \Delta\}$. -/
def IsPolyhedralModelSolution [Nonempty ι] (c : E → Y)
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (x : E) (Δ : ℝ) (s : E) : Prop :=
  s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (polyhedralResidualModel c p b H x) (Metric.closedBall 0 Δ) s

/-- **Equation (16.2.9)** of [conn2000trust]. The feasible set of the **epigraph problem** is the
set of pairs $(x, t) \in E \times \mathbb{R}$ with
$$p_i(c(x)) + b_i \le t \quad \text{for all } i.$$
-/
def polyhedralEpigraphFeasible (c : E → Y) (p : ι → Y →L[ℝ] ℝ)
    (b : ι → ℝ) : Set (E × ℝ) :=
  {w | ∀ i, affineResidualBranch (p i) (b i) (c w.1) ≤ w.2}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A pair $(x, t)$ lies in the feasible set (16.2.9) of the epigraph problem if and only if
$h(c(x)) \le t$. -/
theorem mem_polyhedralEpigraphFeasible [Nonempty ι] {c : E → Y}
    {p : ι → Y →L[ℝ] ℝ} {b : ι → ℝ} {w : E × ℝ} :
    w ∈ polyhedralEpigraphFeasible c p b ↔ polyhedralResidualValue c p b w.1 ≤ w.2 := by
  change (∀ i, affineResidualBranch (p i) (b i) (c w.1) ≤ w.2) ↔
    Finset.univ.sup' Finset.univ_nonempty
      (fun i ↦ affineResidualBranch (p i) (b i) (c w.1)) ≤ w.2
  simp only [Finset.sup'_le_iff, Finset.mem_univ, true_implies]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **Equations (16.2.9)–(16.2.10)** of [conn2000trust]. A pair $(x, t)$ is feasible for the
epigraph problem and minimizes $t$ over its feasible set if and only if $t = h(c(x))$ and $x$ is
a global minimizer of $h \circ c$. -/
theorem isMinOn_polyhedralEpigraph_iff [Nonempty ι] {c : E → Y}
    {p : ι → Y →L[ℝ] ℝ} {b : ι → ℝ} {x : E} {t : ℝ} :
    ((x, t) ∈ polyhedralEpigraphFeasible c p b ∧
      IsMinOn Prod.snd (polyhedralEpigraphFeasible c p b) (x, t)) ↔
    t = polyhedralResidualValue c p b x ∧
      IsMinOn (polyhedralResidualValue c p b) Set.univ x := by
  have hfeas (y : E) :
      (y, polyhedralResidualValue c p b y) ∈ polyhedralEpigraphFeasible c p b :=
    mem_polyhedralEpigraphFeasible.2 le_rfl
  constructor
  · rintro ⟨hf, hm⟩
    have ht : t = polyhedralResidualValue c p b x := le_antisymm ((isMinOn_iff.1 hm) _ (hfeas x))
      (mem_polyhedralEpigraphFeasible.1 hf)
    refine ⟨ht, isMinOn_univ_iff.2 fun y ↦ ?_⟩
    simpa only [ht] using ((isMinOn_iff.1 hm) _ (hfeas y) : t ≤ polyhedralResidualValue c p b y)
  · rintro ⟨rfl, hm⟩
    exact ⟨hfeas x, isMinOn_iff.2 fun w hw ↦
      ((isMinOn_univ_iff.1 hm) w.1).trans (mem_polyhedralEpigraphFeasible.1 hw)⟩

/-- **Equations (16.2.11)–(16.2.14)** of [conn2000trust]. Let $a_i \in \mathbb{R}$ be the branch
values, $A_i$ continuous linear functionals on $E$ the branch derivatives, $t$ the epigraph
height and $\theta_i \in \mathbb{R}$. Then $\theta$ is an **epigraph multiplier** if
$$a_i \le t, \quad \theta_i \ge 0, \quad \theta_i (t - a_i) = 0 \quad \text{for all } i, \qquad
  \sum_i \theta_i = 1, \qquad \sum_i \theta_i A_i = 0.$$

At $a_i = p_i(c(x)) + b_i$ and $A_i = p_i \circ J(x)$, these are the first-order conditions of
the epigraph problem. -/
structure EpigraphMultiplier (a : ι → ℝ) (A : ι → E →L[ℝ] ℝ)
    (t : ℝ) (θ : ι → ℝ) : Prop where
  /-- Feasibility: $a_i \le t$ for every $i$. -/
  feasible : ∀ i, a i ≤ t
  /-- Nonnegativity: $\theta_i \ge 0$ for every $i$. -/
  nonneg : ∀ i, 0 ≤ θ i
  /-- Complementarity: $\theta_i (t - a_i) = 0$ for every $i$. -/
  complementary : ∀ i, θ i * (t - a i) = 0
  /-- Stationarity in the height: $\sum_i \theta_i = 1$. -/
  sum_eq_one : ∑ i, θ i = 1
  /-- Stationarity in $x$: $\sum_i \theta_i A_i = 0$. -/
  stationary : ∑ i, θ i • A i = 0

/-- **Theorem 16.2.2** of [conn2000trust], critical cone of the epigraph problem, from its proof.
For branch values $a_i$, derivatives $A_i$, height $t$ and multipliers $\theta_i$, the
**critical cone** is the set of $(d, u) \in E \times \mathbb{R}$ with $A_i d \le u$ for every
active $i$, and $A_i d = u$ for every active $i$ with $\theta_i > 0$. -/
def epigraphCriticalCone (a : ι → ℝ) (A : ι → E →L[ℝ] ℝ)
    (t : ℝ) (θ : ι → ℝ) : Set (E × ℝ) :=
  {v | (∀ i, a i = t → A i v.1 ≤ v.2) ∧
    ∀ i, a i = t → 0 < θ i → A i v.1 = v.2}

private theorem EpigraphMultiplier.eq_height_of_pos {a : ι → ℝ} {A : ι → E →L[ℝ] ℝ}
    {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ) {i : ι} (hi : 0 < θ i) :
    a i = t := by
  have hz := (mul_eq_zero.1 (h.complementary i)).resolve_left hi.ne'
  exact (sub_eq_zero.1 hz).symm

private theorem EpigraphMultiplier.sum_apply_eq_zero {a : ι → ℝ} {A : ι → E →L[ℝ] ℝ}
    {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ) (d : E) :
    ∑ i, θ i * A i d = 0 := by
  have hs := congrArg (fun f : E →L[ℝ] ℝ ↦ f d) h.stationary
  simpa only [sum_apply, smul_apply, smul_eq_mul, zero_apply] using hs

/-- Let $\theta$ be an epigraph multiplier for $(a, A, t)$. Then $(d, u)$ lies in the critical cone
if and only if $u = 0$ and $A_i d \le 0$ for every active $i$. -/
theorem mem_epigraphCriticalCone_iff {a : ι → ℝ} {A : ι → E →L[ℝ] ℝ}
    {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ) {d : E} {u : ℝ} :
    (d, u) ∈ epigraphCriticalCone a A t θ ↔ u = 0 ∧ ∀ i, a i = t → A i d ≤ 0 := by
  have hstat := h.sum_apply_eq_zero d
  constructor
  · rintro ⟨hactive, hpos⟩
    have heq : ∑ i, θ i * A i d = ∑ i, θ i * u := by
      apply Finset.sum_congr rfl
      intro i _
      rcases eq_or_lt_of_le (h.nonneg i) with hi | hi
      · simp [← hi]
      · rw [hpos i (h.eq_height_of_pos hi) hi]
    rw [← Finset.sum_mul, h.sum_eq_one, one_mul, hstat] at heq
    exact ⟨heq.symm, fun i hi ↦ heq ▸ hactive i hi⟩
  · rintro ⟨rfl, hactive⟩
    have hnonpos (i : ι) (_ : i ∈ Finset.univ) : θ i * A i d ≤ 0 := by
      rcases eq_or_lt_of_le (h.nonneg i) with hi | hi
      · simp [← hi]
      · exact mul_nonpos_of_nonneg_of_nonpos hi.le (hactive i (h.eq_height_of_pos hi))
    refine ⟨hactive, fun i _ hi ↦ ?_⟩
    exact (mul_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hstat i
      (Finset.mem_univ i))).resolve_left hi.ne'

/-- **Theorem 16.2.2** of [conn2000trust], in active-branch coordinates. Let $\theta$ be an epigraph
multiplier for $(a, A, t)$, and let $H_i$ be continuous bilinear forms on $E$. Then
$$\sum_i \theta_i H_i(d, d) > 0 \text{ for all nonzero } (d, u) \text{ in the critical cone}$$
if and only if $\sum_i \theta_i H_i(d, d) > 0$ for all $d$ with $\|d\| = 1$ and $A_i d \le 0$
for every active $i$.

The epigraph Lagrangian and the composite condition have the same weighted branch Hessian. A
stationary convex combination of the active branches has directional derivative $0$, so the
maximum of the active derivatives in a direction is $0$ exactly when all of them are
nonpositive. -/
theorem epigraphSecondOrder_iff_activeBranch {a : ι → ℝ} {A : ι → E →L[ℝ] ℝ}
    {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ)
    (H : ι → E →L[ℝ] E →L[ℝ] ℝ) :
    (∀ v ∈ epigraphCriticalCone a A t θ, v ≠ 0 →
      0 < ∑ i, θ i * H i v.1 v.1) ↔
    (∀ d : E, ‖d‖ = 1 → (∀ i, a i = t → A i d ≤ 0) →
      0 < ∑ i, θ i * H i d d) := by
  constructor
  · intro hpos d hd hactive
    apply hpos (d, 0) ((mem_epigraphCriticalCone_iff h).2 ⟨rfl, hactive⟩)
    intro hz
    have hdz : d = 0 := congrArg Prod.fst hz
    simp [hdz] at hd
  · intro hpos v hv hn
    obtain ⟨d, u⟩ := v
    obtain ⟨rfl, hactive⟩ := (mem_epigraphCriticalCone_iff h).1 hv
    have hd : d ≠ 0 := by
      intro hz
      exact hn (by simp [hz])
    let r := ‖d‖⁻¹
    have hr : 0 < r := inv_pos.2 (norm_pos_iff.2 hd)
    have hunit : ‖r • d‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hd)
    have hact i (hi : a i = t) : A i (r • d) ≤ 0 := by
      simpa only [map_smul, smul_eq_mul] using
        mul_nonpos_of_nonneg_of_nonpos hr.le (hactive i hi)
    have hscale (i : ι) : θ i * H i (r • d) (r • d) = r ^ 2 * (θ i * H i d d) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hp := hpos (r • d) hunit hact
    simp only [hscale, ← Finset.mul_sum] at hp
    exact pos_of_mul_pos_right hp (sq_nonneg r)

/-- **Equations (16.2.16)–(16.2.18)** of [conn2000trust]. Let $a_i$ be branch values, $p_i$
continuous linear functionals on $Y$ and $t \in \mathbb{R}$. A functional $y$ is an **active
branch combination** if there are $\theta_i \ge 0$ with $\sum_i \theta_i = 1$, $\theta_i = 0$
whenever $a_i \neq t$, and $y = \sum_i \theta_i p_i$.

At $t = h(c(x))$, these functionals are the elements of the subdifferential of the polyhedral
maximum at $c(x)$. -/
def IsActiveBranchCombination (a : ι → ℝ) (p : ι → Y →L[ℝ] ℝ)
    (t : ℝ) (y : Y →L[ℝ] ℝ) : Prop :=
  ∃ θ : ι → ℝ, (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1 ∧
    (∀ i, a i ≠ t → θ i = 0) ∧ y = ∑ i, θ i • p i

private theorem activeBranchCombination_self {a : ι → ℝ} {p : ι → Y →L[ℝ] ℝ}
    {t : ℝ} {i : ι} (hi : a i = t) : IsActiveBranchCombination a p t (p i) := by
  classical
  refine ⟨fun j ↦ if j = i then 1 else 0, ?_, by simp, ?_, ?_⟩
  · intro j
    by_cases hji : j = i <;> simp [hji]
  · intro j hj
    have hji : j ≠ i := fun e ↦ hj (e ▸ hi)
    simp [hji]
  · simp [ite_smul]

/-- **Equations (16.2.16)–(16.2.18)** of [conn2000trust], convex hull form. A functional $y$ is an
active branch combination if and only if $y$ lies in the convex hull of the active slopes
$\{p_i : a_i = t\}$. -/
theorem isActiveBranchCombination_iff_mem_convexHull {a : ι → ℝ}
    {p : ι → Y →L[ℝ] ℝ} {t : ℝ} {y : Y →L[ℝ] ℝ} :
    IsActiveBranchCombination a p t y ↔
      y ∈ convexHull ℝ {q | ∃ i, a i = t ∧ p i = q} := by
  classical
  let S : Set (Y →L[ℝ] ℝ) := {q | ∃ i, a i = t ∧ p i = q}
  constructor
  · rintro ⟨θ, hn, hs, hzero, rfl⟩
    have hfilter (w : ι → ℝ) (hz : ∀ i, a i ≠ t → w i = 0) :
        ∑ i ∈ Finset.univ.filter (fun i ↦ a i = t), w i = ∑ i, w i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : a i = t <;> simp [hi, hz]
    have hf : ∑ i ∈ Finset.univ.filter (fun i ↦ a i = t), θ i • p i =
        ∑ i, θ i • p i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : a i = t <;> simp [hi, hzero]
    rw [← hf]
    exact (convex_convexHull ℝ S).sum_mem (fun i _ ↦ hn i)
      ((hfilter θ hzero).trans hs) (fun i hi ↦
        subset_convexHull ℝ S ⟨i, (Finset.mem_filter.1 hi).2, rfl⟩)
  · have hsub : S ⊆ {q | IsActiveBranchCombination a p t q} := by
      rintro _ ⟨i, hi, rfl⟩
      exact activeBranchCombination_self hi
    apply convexHull_min hsub _ (a := y)
    intro u hu v hv α β hα hβ hsum
    rcases hu with ⟨θ, hn, hs, hz, rfl⟩
    rcases hv with ⟨η, en, es, ez, rfl⟩
    refine ⟨fun i ↦ α * θ i + β * η i,
      fun i ↦ add_nonneg (mul_nonneg hα (hn i)) (mul_nonneg hβ (en i)), ?_, ?_, ?_⟩
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs, es, mul_one, hsum]
    · intro i hi
      simp [hz i hi, ez i hi]
    · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

private theorem activeBranchCombination_le_iff {a : ι → ℝ} {p : ι → Y →L[ℝ] ℝ}
    {t : ℝ} {v : Y} :
    (∀ y : Y →L[ℝ] ℝ, IsActiveBranchCombination a p t y → y v ≤ 0) ↔
      ∀ i, a i = t → p i v ≤ 0 := by
  classical
  constructor
  · intro h i hi
    exact h (p i) (activeBranchCombination_self hi)
  · rintro h y ⟨θ, hn, _, hs, rfl⟩
    simp only [sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : a i = t
    · exact mul_nonpos_of_nonneg_of_nonpos (hn i) (h i hi)
    · rw [hs i hi, zero_mul]

private theorem EpigraphMultiplier.height_eq_sup [Nonempty ι] {a : ι → ℝ}
    {A : ι → E →L[ℝ] ℝ} {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ) :
    t = Finset.univ.sup' Finset.univ_nonempty a := by
  apply le_antisymm _ (Finset.sup'_le _ _ fun i _ ↦ h.feasible i)
  obtain ⟨i, hi, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.sum_eq_one.trans_ne one_ne_zero)
  rw [← h.eq_height_of_pos (lt_of_le_of_ne (h.nonneg i) hn.symm)]
  exact Finset.le_sup' _ hi

/-- Let $c : E \to Y$ be differentiable at $x$, $p$ a continuous linear functional on $Y$ and
$b \in \mathbb{R}$. The derivative of the branch $z \mapsto p(c(z)) + b$ at $x$ is
$p \circ J(x)$. -/
theorem fderiv_affineResidualBranch {c : E → Y} {x : E}
    (hc : DifferentiableAt ℝ c x) (p : Y →L[ℝ] ℝ) (b : ℝ) :
    fderiv ℝ (fun z ↦ p (c z) + b) x = p.comp (fderiv ℝ c x) :=
  ((p.hasFDerivAt.comp x hc.hasFDerivAt).add_const b).fderiv

/-- Let $c : E \to Y$ be twice continuously differentiable at $x$, $p$ a continuous linear
functional on $Y$ and $b \in \mathbb{R}$. For all $d, e \in E$, the second derivative of the
branch $z \mapsto p(c(z)) + b$ at $x$ in the directions $d, e$ is $p(\nabla^2 c(x)(d, e))$.

**Correction.** The curvature is the Hessian of the residual paired with the weighted branch slopes.
Its component expression ranges over residual components, which can differ in number from the affine
branches. The theorem states the algebraic criterion equivalence explicitly.
-/
theorem fderiv_fderiv_affineResidualBranch {c : E → Y} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (p : Y →L[ℝ] ℝ) (b : ℝ) (d e : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ p (c z) + b)) x d e =
      p (fderiv ℝ (fderiv ℝ c) x d e) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun z ↦ p (c z) + b) =ᶠ[𝓝 x]
      fun z ↦ p.comp (fderiv ℝ c z) :=
    (hc.eventually (by norm_num)).mono fun _ hy ↦
      fderiv_affineResidualBranch (hy.differentiableAt (by norm_num)) p b
  rw [heq.fderiv_eq]
  change fderiv ℝ (((ContinuousLinearMap.compL ℝ E Y ℝ) p) ∘ fderiv ℝ c) x d e = _
  rw [(((ContinuousLinearMap.compL ℝ E Y ℝ) p).hasFDerivAt.comp x hd.hasFDerivAt).fderiv]
  rfl

/-- **Equation (16.2.15)** of [conn2000trust], the Lagrangian. For multipliers $\theta_i$ of the
constraints $p_i(c(x)) + b_i - t \le 0$, the **epigraph Lagrangian** is
$$L(x, t) = t + \sum_i \theta_i \bigl(p_i(c(x)) + b_i - t\bigr).$$
-/
def polyhedralEpigraphLagrangian (c : E → Y) (p : ι → Y →L[ℝ] ℝ)
    (b θ : ι → ℝ) (w : E × ℝ) : ℝ :=
  w.2 + ∑ i, θ i * (affineResidualBranch (p i) (b i) (c w.1) - w.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem polyhedralEpigraphLagrangian_eq_of_sum_eq_one
    (c : E → Y) (p : ι → Y →L[ℝ] ℝ) (b θ : ι → ℝ) (hθ : ∑ i, θ i = 1) :
    polyhedralEpigraphLagrangian c p b θ =
      fun w ↦ (∑ i, θ i • p i) (c w.1) + ∑ i, θ i * b i := by
  funext w
  simp only [polyhedralEpigraphLagrangian, affineResidualBranch, sum_apply, smul_apply,
    smul_eq_mul, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, hθ, one_mul]
  ring

/-- **Equation (16.2.15)** of [conn2000trust]. Let $c : E \to Y$ be twice continuously
differentiable at $x$, and let $\theta_i$ satisfy $\sum_i \theta_i = 1$. For all
$t \in \mathbb{R}$ and all $v, w \in E \times \mathbb{R}$ with first components $v_1, w_1$,
$$\nabla^2 L(x, t)(v, w) = \sum_i \theta_i \, p_i\bigl(\nabla^2 c(x)(v_1, w_1)\bigr).$$

**Reading.** The residual Hessian is evaluated against the convex combination
$\sum_i \theta_i p_i$ of the slopes, that is, the Hessians of the residual components are
summed. Equivalently, the formula weights the Hessians of the affine branches. It does not
depend on the number of branches.

**Correction.** The curvature is the Hessian of the residual paired with the weighted branch slopes.
Its component expression ranges over residual components, which can differ in number from the affine
branches. The theorem states the algebraic criterion equivalence explicitly.
-/
theorem fderiv_fderiv_polyhedralEpigraphLagrangian
    {c : E → Y} {x : E} (hc : ContDiffAt ℝ 2 c x) (p : ι → Y →L[ℝ] ℝ)
    (b θ : ι → ℝ) (hθ : ∑ i, θ i = 1) (t : ℝ) (v w : E × ℝ) :
    fderiv ℝ (fderiv ℝ (polyhedralEpigraphLagrangian c p b θ)) (x, t) v w =
      ∑ i, θ i * p i (fderiv ℝ (fderiv ℝ c) x v.1 w.1) := by
  rw [polyhedralEpigraphLagrangian_eq_of_sum_eq_one c p b θ hθ]
  let F : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  have hc' : ContDiffAt ℝ 2 (fun z : E × ℝ ↦ c z.1) (x, t) :=
    hc.comp (x, t) F.contDiff.contDiffAt
  rw [fderiv_fderiv_affineResidualBranch hc']
  suffices h : fderiv ℝ (fderiv ℝ (fun z : E × ℝ ↦ c z.1)) (x, t) v w =
      fderiv ℝ (fderiv ℝ c) x v.1 w.1 by
    simp only [h, sum_apply, smul_apply, smul_eq_mul]
  let L := (ContinuousLinearMap.compL ℝ (E × ℝ) E Y).flip F
  have hd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun z : E × ℝ ↦ c z.1) =ᶠ[𝓝 (x, t)]
      fun z ↦ L (fderiv ℝ c z.1) := by
    have he := (F.continuous.tendsto (x, t)).eventually (hc.eventually (by norm_num))
    filter_upwards [he] with z hz
    exact (hz.differentiableAt (by norm_num)).hasFDerivAt.comp z F.hasFDerivAt |>.fderiv
  rw [heq.fderiv_eq]
  exact congrArg (fun f : (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] Y ↦ f v w)
    (L.hasFDerivAt.comp (x, t) (hd.hasFDerivAt.comp (x, t) F.hasFDerivAt)).fderiv

/-- **Theorem 16.2.2** of [conn2000trust]. Let $\iota$ be nonempty and finite, $c : E \to Y$, $p_i$
continuous linear functionals on $Y$, $b_i \in \mathbb{R}$ and $x \in E$. Let
$a_i = p_i(c(x)) + b_i$, $A_i = p_i \circ J(x)$, $H = \nabla^2 c(x)$ and $t_0 = h(c(x))$. The
following are equivalent.

* There are a height $t$ and an epigraph multiplier $\theta$ for $(a, A, t)$ such that
  $\sum_i \theta_i p_i(H(d, d)) > 0$ for every nonzero $(d, u)$ in the critical cone.
* There is an active branch combination $y$ at the height $t_0$ with $y \circ J(x) = 0$ and
  $y(H(d, d)) > 0$ for every $d$ with $\|d\| = 1$ such that $z(J(x) d) \le 0$ for all active
  branch combinations $z$ at $t_0$.

The first condition uses the epigraph height and its first-order multipliers. The second uses a
subgradient of $h$ at $c(x)$, represented by the active slopes, and restricts the residual
Hessian to the unit directions with support value $0$. Stationarity supplies a subgradient that
is $0$ on every direction of this test.

**Correction.** The curvature is the Hessian of the residual paired with the weighted branch slopes.
Its component expression ranges over residual components, which can differ in number from the affine
branches. The theorem states the algebraic criterion equivalence explicitly.
-/
theorem theorem_16_2_2 [Nonempty ι] (c : E → Y) (p : ι → Y →L[ℝ] ℝ)
    (b : ι → ℝ) (x : E) :
    let a i := p i (c x) + b i
    let A i := (p i).comp (fderiv ℝ c x)
    let H := fderiv ℝ (fderiv ℝ c) x
    let height := polyhedralResidualValue c p b x
    (∃ t θ, EpigraphMultiplier a A t θ ∧
      ∀ v ∈ epigraphCriticalCone a A t θ, v ≠ 0 →
        0 < ∑ i, θ i * p i (H v.1 v.1)) ↔
    (∃ y : Y →L[ℝ] ℝ, IsActiveBranchCombination a p height y ∧
      y.comp (fderiv ℝ c x) = 0 ∧ ∀ d : E, ‖d‖ = 1 →
        (∀ z : Y →L[ℝ] ℝ, IsActiveBranchCombination a p height z →
          z (fderiv ℝ c x d) ≤ 0) → 0 < y (H d d)) := by
  dsimp only
  let a (i : ι) := p i (c x) + b i
  let A (i : ι) := (p i).comp (fderiv ℝ c x)
  let H := fderiv ℝ (fderiv ℝ c) x
  let height := polyhedralResidualValue c p b x
  let Q (i : ι) := (ContinuousLinearMap.compL ℝ E Y ℝ (p i)).comp H
  have hsum (θ : ι → ℝ) :
      (∑ i, θ i • p i).comp (fderiv ℝ c x) = ∑ i, θ i • A i := by
    ext d
    simp only [A, ContinuousLinearMap.comp_apply, sum_apply, smul_apply]
  have hquad (θ : ι → ℝ) (d : E) :
      (∑ i, θ i • p i) (H d d) = ∑ i, θ i * Q i d d := by
    simp only [Q, sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply]
  constructor
  · rintro ⟨t, θ, hθ, hpos⟩
    have ht : t = height := hθ.height_eq_sup
    subst t
    refine ⟨∑ i, θ i • p i, ⟨θ, hθ.nonneg, hθ.sum_eq_one, ?_, rfl⟩, ?_, ?_⟩
    · intro i hi
      exact (mul_eq_zero.1 (hθ.complementary i)).resolve_right (sub_ne_zero.2 hi.symm)
    · rw [hsum]
      exact hθ.stationary
    · intro d hd hz
      rw [hquad]
      exact (epigraphSecondOrder_iff_activeBranch hθ Q).1 hpos d hd
        (activeBranchCombination_le_iff (p := p) (v := fderiv ℝ c x d) |>.1 hz)
  · rintro ⟨_, ⟨θ, hn, hs, hzero, rfl⟩, hstat, hpos⟩
    have hθ : EpigraphMultiplier a A height θ := by
      refine ⟨fun i ↦ Finset.le_sup' a (Finset.mem_univ i), hn, ?_, hs, ?_⟩
      · intro i
        by_cases hi : a i = height
        · rw [hi, sub_self, mul_zero]
        · rw [hzero i hi, zero_mul]
      · rw [← hsum]
        exact hstat
    refine ⟨height, θ, hθ, (epigraphSecondOrder_iff_activeBranch hθ Q).2 ?_⟩
    intro d hd hactive
    rw [← hquad]
    exact hpos d hd (activeBranchCombination_le_iff (p := p) (v := fderiv ℝ c x d) |>.2 hactive)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Let $\iota$ be nonempty and finite. The polyhedral maximum $h(y) = \max_i (p_i(y) + b_i)$ is
Lipschitz with constant $\sum_i \|p_i\|$.

**Reading.** The sum of the slope norms is used as a uniform Lipschitz constant for the finite
maximum.
-/
theorem lipschitzWith_polyhedralAffineMaximum [Nonempty ι]
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) :
    LipschitzWith (∑ i, ‖p i‖₊) (polyhedralAffineMaximum p b) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  let K : ℝ := ((∑ i, ‖p i‖₊ : NNReal) : ℝ)
  have hK (i : ι) : ‖p i‖ ≤ K := by
    exact_mod_cast (Finset.single_le_sum (f := fun j ↦ ‖p j‖₊)
      (fun _ _ ↦ zero_le) (Finset.mem_univ i))
  have h (u v : Y) : polyhedralAffineMaximum p b u ≤
      polyhedralAffineMaximum p b v + K * dist u v := by
    apply Finset.sup'_le
    intro i hi
    have hv : affineResidualBranch (p i) (b i) v ≤ polyhedralAffineMaximum p b v :=
      Finset.le_sup' (fun j ↦ affineResidualBranch (p j) (b j) v) hi
    have hdiff : p i u - p i v ≤ K * dist u v := by
      rw [← map_sub, dist_eq_norm]
      have hnorm := (p i).le_opNorm (u - v)
      rw [Real.norm_eq_abs] at hnorm
      exact ((le_abs_self _).trans hnorm).trans
        (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))
    dsimp [affineResidualBranch] at hv ⊢
    linarith only [hv, hdiff]
  have hzy := h z y
  rw [dist_comm z y] at hzy
  rw [Real.dist_eq]
  change _ ≤ K * dist y z
  exact abs_le.2 ⟨by linarith only [hzy], by linarith only [h y z]⟩

private theorem exists_uniform_firstOrder_of_contDiff {c : E → Y}
    (hc : ContDiff ℝ 1 c) (x : E) {a : ℝ} (ha : 0 < a) :
    ∃ r > 0, ∀ y ∈ Metric.ball x r, ∀ s : E, ‖s‖ ≤ r →
      ‖c (y + s) - c y - fderiv ℝ c y s‖ ≤ a * ‖s‖ := by
  obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.1
    (show ContinuousAt (fderiv ℝ c) x from (hc.continuous_fderiv one_ne_zero).continuousAt)
    (a / 2) (half_pos ha)
  refine ⟨r / 3, by positivity, ?_⟩
  intro y hy s hs
  have hy' : y ∈ Metric.ball x r := Metric.ball_subset_ball (by linarith) hy
  have hys : y + s ∈ Metric.ball x r := by
    have hdy := Metric.mem_ball.1 hy
    rw [Metric.mem_ball]
    have ht := dist_triangle (y + s) y x
    rw [dist_eq_norm (y + s) y, add_sub_cancel_left] at ht
    linarith
  let g : E → Y := fun z ↦ c z - fderiv ℝ c y z
  have hdiff (z : E) : DifferentiableAt ℝ g z :=
    (hc.differentiable one_ne_zero z).sub (ContinuousLinearMap.differentiableAt _)
  have hbound (z : E) (hz : z ∈ Metric.ball x r) : ‖fderiv ℝ g z‖ ≤ a := by
    rw [show g = fun z ↦ c z - fderiv ℝ c y z from rfl,
      fderiv_fun_sub (hc.differentiable one_ne_zero z) (ContinuousLinearMap.differentiableAt _),
      ContinuousLinearMap.fderiv]
    rw [← dist_eq_norm]
    have ht := dist_triangle (fderiv ℝ c z) (fderiv ℝ c x) (fderiv ℝ c y)
    rw [dist_comm (fderiv ℝ c x)] at ht
    linarith only [ht, hclose hz, hclose hy']
  have he := (convex_ball x r).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hdiff z) hbound hy' hys
  have hcalc : g (y + s) - g y = c (y + s) - c y - fderiv ℝ c y s := by
    dsimp [g]
    rw [map_add]
    abel
  rwa [hcalc, add_sub_cancel_left] at he

end EpigraphConditions

section PolyhedralConvergence

variable {E Y ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]

open Chapter11 in
/-- Let $E$ be a real inner product space, let $c : E \to Y$ be continuously differentiable, and let
$(B_j)_{j \in I}$ be continuous bilinear forms on $E$ with $\|B_j\| \le M$ for some $M \ge 0$.
Then at every $x \in E$ the composite models (16.2.4) with quadratic terms $B_j$ agree uniformly
with $h \circ c$ after normalization by the step length, uniformly in the base point near $x$
and in $j$.

The agreement is `ConnGouldToint.Chapter11.UniformNormalizedModelAgreementAt`. The proof uses
the Lipschitz bound `ConnGouldToint.Chapter16.lipschitzWith_polyhedralAffineMaximum`.

**Reading.** The result covers the monotone Algorithm 11.1.1. It assumes a uniform bilinear-model
bound and the local sufficient-decrease property, and proves Clarke stationarity of every
subsequential limit using first-order uniform agreement.
-/
theorem polyhedralResidualModel_uniformAgreement
    [Nonempty ι] {I : Type*} {c : E → Y}
    (hc : ContDiff ℝ 1 c) (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ)
    (B : I → E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ i, ‖B i‖ ≤ M) (x : E) :
    UniformNormalizedModelAgreementAt (polyhedralResidualValue c p b)
      (fun y i s ↦ polyhedralResidualModel c p b (B i) y s) x := by
  intro a ha
  let K : ℝ := ((∑ i, ‖p i‖₊ : NNReal) : ℝ)
  have hK : 0 ≤ K := by positivity
  have hK₁ : 0 < K + 1 := by positivity
  have hM₁ : 0 < M + 1 := by positivity
  obtain ⟨r, hr, hrem⟩ := exists_uniform_firstOrder_of_contDiff hc x
    (div_pos (half_pos ha) hK₁)
  let t := min r (a / (M + 1))
  have ht : 0 < t := lt_min hr (div_pos ha hM₁)
  refine ⟨t, t, ht, ht, ?_⟩
  intro y hy i s hs
  by_cases hzero : s = 0
  · simp [normalizedModelError, hzero, ha.le]
  have hn := norm_pos_iff.2 hzero
  have hres : ‖c (y + s) - (c y + fderiv ℝ c y s)‖ ≤ (a / 2 / (K + 1)) * ‖s‖ := by
    rw [← sub_sub]
    exact hrem y (Metric.ball_subset_ball (min_le_left _ _) hy) s (hs.trans (min_le_left _ _))
  have hlip := (lipschitzWith_polyhedralAffineMaximum p b).dist_le_mul
    (c (y + s)) (c y + fderiv ℝ c y s)
  rw [Real.dist_eq, dist_eq_norm] at hlip
  have hpoly : |polyhedralResidualValue c p b (y + s) -
        polyhedralAffineMaximum p b (c y + fderiv ℝ c y s)| ≤ a / 2 * ‖s‖ := by
    apply hlip.trans
    calc
      K * ‖c (y + s) - (c y + fderiv ℝ c y s)‖ ≤ K * ((a / 2 / (K + 1)) * ‖s‖) :=
        mul_le_mul_of_nonneg_left hres hK
      _ = (K / (K + 1)) * (a / 2 * ‖s‖) := by ring
      _ ≤ a / 2 * ‖s‖ := mul_le_of_le_one_left (by positivity)
        ((div_le_one hK₁).2 (by linarith))
  have hcurv : |B i s s| ≤ M * ‖s‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖B i s‖ * ‖s‖ := (B i s).le_opNorm s
      _ ≤ (‖B i‖ * ‖s‖) * ‖s‖ :=
        mul_le_mul_of_nonneg_right ((B i).le_opNorm s) (norm_nonneg _)
      _ = ‖B i‖ * ‖s‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hB i) (sq_nonneg _)
  have hsn := (le_div_iff₀ hM₁).1 (hs.trans (min_le_right _ _))
  have hmul : M * ‖s‖ ≤ a := by nlinarith only [hsn, norm_nonneg s]
  have hquad : |B i s s / 2| ≤ a / 2 * ‖s‖ := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact hcurv.trans (by nlinarith only [mul_le_mul_of_nonneg_right hmul (norm_nonneg s)])
  rw [normalizedModelError, abs_div, abs_of_nonneg hn.le]
  apply (div_le_iff₀ hn).2
  rw [polyhedralResidualModel, add_comm (B i s s / 2), ← sub_sub]
  exact (abs_sub _ _).trans (by linarith only [hpoly, hquad])

open Chapter11 in
/-- **Theorem 16.2.1** of [conn2000trust], for Algorithm 11.1.1. Let $E$ be a real Hilbert space,
let $c : E \to Y$ be continuously differentiable, and let $(B_j)_{j \in I}$ be continuous
bilinear forms on $E$ with $\|B_j\| \le M$ for some $M \ge 0$. Consider a run of Algorithm
11.1.1 for the objective $h \circ c$ with the composite models (16.2.4), with quadratic terms
$B_j$, and suppose that the local sufficient decrease condition AA.1n holds at every point. If a
subsequence of the iterates converges to $x$, then $0$ lies in the Clarke subdifferential of
$h \circ c$ at $x$.

The run is `ConnGouldToint.Chapter11.NonsmoothTRRun`, AA.1n is
`ConnGouldToint.Chapter11.NonsmoothTRRun.HasLocalSufficientDecrease`, and the subdifferential is
`Optimization.clarkeSubgradient`.

**Reading.** The result covers the monotone Algorithm 11.1.1. It assumes a uniform bilinear-model
bound and the local sufficient-decrease property, and proves Clarke stationarity of every
subsequential limit using first-order uniform agreement.
-/
theorem theorem_16_2_1_monotone
    [CompleteSpace E] [Nonempty ι] {I : Type*} {c : E → Y}
    (hc : ContDiff ℝ 1 c) (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ)
    (B : I → E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M) (hB : ∀ i, ‖B i‖ ≤ M)
    {Q : NonsmoothTRParams}
    (R : NonsmoothTRRun Q (polyhedralResidualValue c p b)
      (fun y i s ↦ polyhedralResidualModel c p b (B i) y s))
    (hAA : ∀ y, R.HasLocalSufficientDecrease y)
    {x : E} {j : ℕ → ℕ} (hj : StrictMono j) (hx : Tendsto (R.x ∘ j) atTop (𝓝 x)) :
    (0 : E) ∈ Optimization.clarkeSubgradient (polyhedralResidualValue c p b) x := by
  have hloc := (lipschitzWith_polyhedralAffineMaximum p b).locallyLipschitz.comp hc.locallyLipschitz
  obtain ⟨L, U, hU, hL⟩ := hloc x
  have hmatch : modelValueMatches (polyhedralResidualValue c p b)
      (fun y i s ↦ polyhedralResidualModel c p b (B i) y s) := by
    intro y i
    simp [polyhedralResidualModel, polyhedralResidualValue]
  exact theorem_11_2_5 R hU hL hmatch (polyhedralResidualModel_uniformAgreement hc p b B hM hB x)
    hAA hj hx

end PolyhedralConvergence

end ConnGouldToint.Chapter16
