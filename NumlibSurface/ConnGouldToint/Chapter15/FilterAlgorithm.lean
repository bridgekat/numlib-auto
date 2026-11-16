/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import NumlibSurface.ConnGouldToint.Chapter15.Section05

/-!
# Conn, Gould and Toint, Section 15.5: The filter SQP algorithms

This module formalizes one iteration of the two filter SQP algorithms of Section 15.5 of
[conn2000trust]: the composite-step Algorithm 15.5.1 and the single-step Algorithm 15.5.2. The
problem has constraints $c_j(x) = 0$ for the equality indices and $c_j(x) \ge 0$ for the other
indices. Each point $x$ has the pair $(\theta(x), f(x))$ of its constraint violation and its
objective value. The filter is a set of such pairs. A trial pair is acceptable to the filter if, for
every entry $(\theta', f')$, it satisfies $\theta < (1 - \gamma)\theta'$ or $f < f' - \gamma\theta$.
At an iterate where the trust-region subproblem TRQP$(x, \Delta)$ is not compatible, a restoration
phase inserts the current pair into the filter and supplies a new acceptable iterate. Otherwise the
algorithm computes a trial step, tests it against the filter, the current pair and, when the
switching test holds, the ratio of actual to predicted decrease, and updates the radius. The filter,
the margin test and the radius rule are those of `NumlibSurface.ConnGouldToint.Chapter15.Section05`.

## Main definitions

* Algorithm 15.5.1, `ConnGouldToint.Chapter15.FilterSQPParams`: the radius factors, the ratio
  thresholds, the filter margin and the switching factor.
* Algorithms 15.5.1 and 15.5.2, `ConnGouldToint.Chapter15.FilterSQPState`: the iterate, the radius,
  the multipliers, the Hessian data and the filter.
* Algorithm 15.5.1, Step 0, `ConnGouldToint.Chapter15.FilterSQPState.initial`: the initial state
  with an empty filter.
* Section 15.5.1, `ConnGouldToint.Chapter15.filterSQPModel`: the quadratic model of
  TRQP$(x, \Delta)$.
* Section 15.5.1, `ConnGouldToint.Chapter15.filterSQPFeasible`: the trust-region and
  linearized-constraint conditions of TRQP$(x, \Delta)$.
* Equations (15.5.7)–(15.5.9), `ConnGouldToint.Chapter15.filterSQPAccepted`: the acceptance test of
  a trial.
* Algorithm 15.5.1, Steps 1 and 3–6, `ConnGouldToint.Chapter15.FilterSQPStep`: the restoration,
  rejection and acceptance transitions shared by the two algorithms.
* Algorithm 15.5.1, `ConnGouldToint.Chapter15.compositeFilterSQPStep`: one iteration with a
  compatible normal step and the tangential decrease condition AA.1m.
* Algorithm 15.5.2 and equation (15.5.45), `ConnGouldToint.Chapter15.singleFilterSQPStep`: one
  iteration with a single trial step.

## Main results

* Algorithms 15.5.1 and 15.5.2, `ConnGouldToint.Chapter15.FilterSQPStep.accepts_next`: every iterate
  that continues the run is acceptable to the filter at the start of its iteration.
* Algorithms 15.5.1 and 15.5.2, `ConnGouldToint.Chapter15.FilterSQPStep.compatible_of_restored`: a
  transition from an incompatible iterate is a restoration, and the restored iterate is compatible.

## Conventions

* The model Hessian is $B + \sum_i y_i W_i$, with a plus sign in front of the multipliers.

## Implementation notes

* An iteration is a relation between a state and an optional next state. The value `none` means that
  the restoration phase failed and the algorithm stops.
* The ratio of actual to predicted decrease is $0$ when the predicted decrease is not positive.

## Deviations from the source

* **Algorithm 15.5.1, filter update** (correction). A new entry deletes only the entries that it
  Pareto-dominates. The printed margin-based deletion admits a bounded insertion stream with
  violations bounded away from zero. See `ConnGouldToint.Chapter15.FilterSQPStep` and
  `ConnGouldToint.Chapter15.sqpFilter_margin_deletion_counterexample`.
* **Algorithm 15.5.1, rejected trials** (correction). The radius after a rejection is at most
  $\gamma_1 \Delta$ with $\gamma_1 < 1$. The printed parameter range allows $\gamma_1 = 1$, which
  permits a smooth nonstationary run that rejects the same trial forever. See
  `ConnGouldToint.Chapter15.FilterSQPParams` and
  `ConnGouldToint.Chapter15.sqpFilter_unchanged_rejected_radius_counterexample`.
* **Algorithm 15.5.1, radius update** (reading). An accepted trial with ratio below $\eta_1$, which
  can occur when the switching test fails, takes a radius in the shrink interval
  $[\gamma_0 \Delta, \gamma_1 \Delta]$. The printed radius update does not cover this case. See
  `ConnGouldToint.Chapter15.FilterSQPStep`.
* **Equations (15.5.7)–(15.5.9)** (reading). When the switching test holds, an accepted trial must
  have a positive predicted decrease. A zero or negative prediction does not certify an objective
  step. See `ConnGouldToint.Chapter15.filterSQPAccepted`.
-/

open ConnGouldToint.Chapter06 Optimization
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm 15.5.1** of [conn2000trust], parameters. The parameters of the composite-step and
single-step filter algorithms are radius factors $0 < \gamma_0 < \gamma_1 < 1 \le \gamma_2$,
ratio thresholds $0 < \eta_1 \le \eta_2 < 1$, a filter margin $\gamma \in (0, 1)$ and a
switching factor $\kappa \in (0, 1)$.

**Correction.** The source allows $\gamma_1 = 1$. Then a rejected trial need not shrink the
radius, and `ConnGouldToint.Chapter15.sqpFilter_unchanged_rejected_radius_counterexample` gives
a smooth run that rejects the same trial at a nonstationary point forever. The strict bound
$\gamma_1 < 1$ excludes this. -/
structure FilterSQPParams where
  /-- The smallest radius factor $\gamma_0$, the lower end of the shrink interval. -/
  γ₀ : ℝ
  /-- The radius factor $\gamma_1$, the upper end of the shrink interval. -/
  γ₁ : ℝ
  /-- The expansion factor $\gamma_2$, the upper end of the interval after a very successful
  trial. -/
  γ₂ : ℝ
  /-- The ratio threshold $\eta_1$ for a successful trial. -/
  η₁ : ℝ
  /-- The ratio threshold $\eta_2$ for a very successful trial. -/
  η₂ : ℝ
  /-- The filter margin $\gamma$ of the acceptance test (15.5.7). -/
  margin : ℝ
  /-- The switching factor $\kappa$ of the switching test $\kappa\theta^2 \le \mathrm{pred}$ in
  (15.5.8). -/
  switchFactor : ℝ
  /-- The lower radius factor is positive: $0 < \gamma_0$. -/
  lower_pos : 0 < γ₀
  /-- The radius factors are ordered: $\gamma_0 < \gamma_1$. -/
  lower_lt_upper : γ₀ < γ₁
  /-- A rejection contracts the radius: $\gamma_1 < 1$. -/
  rejection_contracts : γ₁ < 1
  /-- The expansion factor is at least one: $1 \le \gamma_2$. -/
  expansion : 1 ≤ γ₂
  /-- The first ratio threshold is positive: $0 < \eta_1$. -/
  acceptance_pos : 0 < η₁
  /-- The ratio thresholds are ordered: $\eta_1 \le \eta_2$. -/
  acceptance_order : η₁ ≤ η₂
  /-- The second ratio threshold is below one: $\eta_2 < 1$. -/
  acceptance_lt_one : η₂ < 1
  /-- The filter margin lies in $(0, 1)$. -/
  margin_range : margin ∈ Set.Ioo 0 1
  /-- The switching factor lies in $(0, 1)$. -/
  switch_range : switchFactor ∈ Set.Ioo 0 1

/-- **Algorithms 15.5.1 and 15.5.2** of [conn2000trust], state. A state of a filter SQP algorithm
consists of an iterate $x \in E$, a trust-region radius $\Delta$, multipliers $y_i$ for the
constraints, a Hessian approximation $B$ of the objective, Hessian approximations $W_i$ of the
constraints, and the filter, a set of pairs (violation, objective value). -/
structure FilterSQPState (E ι : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The current iterate $x$. -/
  x : E
  /-- The trust-region radius $\Delta$. -/
  radius : ℝ
  /-- The multiplier estimates $y_i$, one for each constraint. -/
  multiplier : ι → ℝ
  /-- The Hessian approximation $B$ of the objective. -/
  B : E →L[ℝ] E
  /-- The Hessian approximations $W_i$ of the constraints. -/
  W : ι → E →L[ℝ] E
  /-- The filter: the set of stored pairs $(\theta, f)$ of constraint violation and objective value.
  -/
  entries : Set (ℝ × ℝ)

/-- **Algorithm 15.5.1** of [conn2000trust], Step 0. The initial state has iterate $x$, radius
$\Delta$, multipliers $y$, Hessian data $B$ and $W_i$, and the empty filter. -/
def FilterSQPState.initial (x : E) (Δ : ℝ) (y : ι → ℝ)
    (B : E →L[ℝ] E) (W : ι → E →L[ℝ] E) : FilterSQPState E ι :=
  ⟨x, Δ, y, B, W, ∅⟩

/-- **Section 15.5.1** of [conn2000trust], the model of TRQP$(x, \Delta)$. For a state with iterate
$x$, multipliers $y_i$ and Hessian data $B$ and $W_i$, the model of a step $s$ is
$$m(s) = f(x) + \langle \nabla f(x), s\rangle + \tfrac12 \langle s, H s\rangle, \qquad H = B +
  \sum_i y_i W_i.$$

The Lagrangian Hessian uses the plus sign in front of the multipliers. -/
noncomputable def filterSQPModel [Fintype ι] [CompleteSpace E] (f : E → ℝ)
    (state : FilterSQPState E ι) (s : E) : ℝ :=
  let H := state.B + ∑ i, state.multiplier i • state.W i
  quadraticModel (f state.x) (gradient f state.x) H.toLinearMap s

/-- **Section 15.5.1** of [conn2000trust], the constraints of TRQP$(x, \Delta)$. A step $s$ is
**feasible** for the subproblem if $\|s\| \le \Delta$ and $s$ satisfies the linearized
constraints at $x$: $c_j(x) + \langle \nabla c_j(x), s\rangle = 0$ for each equality index $j$
and $c_j(x) + \langle \nabla c_j(x), s\rangle \ge 0$ for each other index $j$.

The Boolean function `eq` marks the equality indices. -/
def filterSQPFeasible [CompleteSpace E] (eq : ι → Bool) (c : ι → E → ℝ)
    (state : FilterSQPState E ι) (s : E) : Prop :=
  ‖s‖ ≤ state.radius ∧
    sqpFilterLinearFeasible eq (fun i ↦ c i state.x) (fun i ↦ gradient (c i) state.x) s

/-- **Equations (15.5.7)–(15.5.9)** of [conn2000trust]. A trial pair $(\theta^+, f^+)$ is
**accepted** against a filter $\mathcal{F}$, a current pair $(\theta, f)$, a predicted decrease
$\mathrm{pred}$ and a ratio $\rho$ if it is acceptable to every entry of $\mathcal{F}$ and to
the current pair in the margin test (15.5.7), and if, when the switching test
$\kappa \theta^2 \le \mathrm{pred}$ of (15.5.8) holds, also $\mathrm{pred} > 0$ and
$\rho \ge \eta_1$.

**Reading.** The condition $\mathrm{pred} > 0$ is explicit. A zero or negative prediction does
not certify an objective step. -/
def filterSQPAccepted (P : FilterSQPParams) (F : Set (ℝ × ℝ))
    (current trial : ℝ × ℝ) (pred ratio : ℝ) : Prop :=
  sqpFilterAccepts P.margin F trial ∧ sqpFilterAcceptsPair P.margin trial current ∧
    (sqpFilterSwitching P.switchFactor current.1 pred → 0 < pred ∧ P.η₁ ≤ ratio)

private noncomputable def filterSQPRatio (pair : E → ℝ × ℝ) (x s : E) (pred : ℝ) : ℝ :=
  if 0 < pred then ((pair x).2 - (pair (x + s)).2) / pred else 0

private def filterSQPModelDataValid (state : FilterSQPState E ι) : Prop :=
  state.B.toLinearMap.IsSymmetric ∧ ∀ i, (state.W i).toLinearMap.IsSymmetric

/-- **Algorithm 15.5.1** of [conn2000trust], Steps 1 and 3–6, shared with Algorithm 15.5.2. The
transition relation of a filter SQP iteration, for a map $x \mapsto (\theta(x), f(x))$, a
compatibility test, a trial condition and a predicted decrease. With the ratio
$\rho = (f(x) - f(x + s)) / \mathrm{pred}$, set to $0$ when $\mathrm{pred} \le 0$, a state goes
to:

* a restored state, if the current iterate is incompatible: the current pair is inserted into
  the filter, and the new iterate is acceptable to the new filter, compatible, with positive
  radius and symmetric Hessian data;
* no state, if the current iterate is incompatible and no such restored state exists;
* the same state with a new radius $\Delta' \in [\gamma_0\Delta, \gamma_1\Delta]$, if the
  iterate is compatible and the trial $s$ is not accepted;
* a state with iterate $x + s$, if the iterate is compatible and the trial is accepted. The
  filter is unchanged when the switching test holds, and otherwise the current pair is inserted.
  The new radius follows `ConnGouldToint.Chapter15.sqpFilterRadiusUpdate`, and the new Hessian
  data are symmetric.

**Correction.** The insertion deletes only the entries that the new pair Pareto-dominates, so
that every region excluded earlier stays excluded. The printed margin-based deletion admits a
bounded insertion stream with violations bounded away from zero; see
`ConnGouldToint.Chapter15.sqpFilter_margin_deletion_counterexample`.

**Reading.** An accepted trial with $\rho < \eta_1$ can occur when the switching test fails. Its
new radius lies in the shrink interval $[\gamma_0\Delta, \gamma_1\Delta]$, a case that the
printed radius update does not cover. -/
inductive FilterSQPStep (P : FilterSQPParams) (pair : E → ℝ × ℝ)
    (compatible : FilterSQPState E ι → Prop)
    (trial : FilterSQPState E ι → E → Prop) (prediction : FilterSQPState E ι → E → ℝ)
    (state : FilterSQPState E ι) : Option (FilterSQPState E ι) → Prop
  /-- Restoration: an incompatible iterate is replaced by a compatible state whose pair is
  acceptable to the filter with the current pair inserted. -/
  | restored (next : FilterSQPState E ι)
      (incompatible : ¬ compatible state)
      (entries : next.entries = sqpFilterInsert state.entries (pair state.x))
      (acceptable : sqpFilterAccepts P.margin next.entries (pair next.x))
      (radius_pos : 0 < next.radius) (ready : compatible next)
      (model_data : filterSQPModelDataValid next) :
      FilterSQPStep P pair compatible trial prediction state (some next)
  /-- Failed restoration: an incompatible iterate admits no restored state, and the algorithm stops.
  -/
  | restoration_failed
      (incompatible : ¬ compatible state)
      (impossible : ¬ ∃ next, next.entries = sqpFilterInsert state.entries (pair state.x) ∧
        sqpFilterAccepts P.margin next.entries (pair next.x) ∧
        0 < next.radius ∧ compatible next ∧ filterSQPModelDataValid next) :
      FilterSQPStep P pair compatible trial prediction state none
  /-- Rejection: a compatible iterate keeps its point and filter, and the radius shrinks to
  $\Delta' \in [\gamma_0 \Delta, \gamma_1 \Delta]$ after a trial that is not accepted. -/
  | rejected (s : E) (Δ' : ℝ)
      (ready : compatible state) (feasible_trial : trial state s)
      (rejected : ¬ filterSQPAccepted P state.entries (pair state.x) (pair (state.x + s))
        (prediction state s) (filterSQPRatio pair state.x s (prediction state s)))
      (radius_update : sqpFilterRadiusUpdate P.γ₀ P.γ₁ P.γ₂ P.η₁ P.η₂
        (filterSQPRatio pair state.x s (prediction state s)) state.radius Δ' false) :
      FilterSQPStep P pair compatible trial prediction state (some { state with radius := Δ' })
  /-- Acceptance: a compatible iterate moves to $x + s$ after an accepted trial, with the filter
  update of the switching test and the radius update for accepted trials. -/
  | accepted (s : E) (next : FilterSQPState E ι)
      (ready : compatible state) (feasible_trial : trial state s)
      (accepted : filterSQPAccepted P state.entries (pair state.x) (pair (state.x + s))
        (prediction state s) (filterSQPRatio pair state.x s (prediction state s)))
      (iterate_update : next.x = state.x + s)
      (entries : next.entries =
        open Classical in
        if sqpFilterSwitching P.switchFactor (pair state.x).1 (prediction state s) then
          state.entries else sqpFilterInsert state.entries (pair state.x))
      (radius_update : sqpFilterRadiusUpdate P.γ₀ P.γ₁ P.γ₂ P.η₁ P.η₂
        (filterSQPRatio pair state.x s (prediction state s)) state.radius next.radius true)
      (model_data : filterSQPModelDataValid next) :
      FilterSQPStep P pair compatible trial prediction state (some next)

private noncomputable def filterSQPPair [Fintype ι] (f : E → ℝ) (c : ι → E → ℝ)
    (eq : ι → Bool) (x : E) : ℝ × ℝ :=
  (sqpFilterViolation eq (fun i ↦ c i x), f x)

private def filterSQPNormal [CompleteSpace E] (eq : ι → Bool) (c : ι → E → ℝ)
    (κΔ κμ μ : ℝ) (state : FilterSQPState E ι) (n : E) : Prop :=
  sqpFilterCompatible eq (fun i ↦ c i state.x) (fun i ↦ gradient (c i) state.x)
    n κΔ κμ state.radius μ

/-- **Algorithm 15.5.1** of [conn2000trust]. One iteration of the composite-step filter algorithm.
The pair of a point is $(\theta(x), f(x))$, where $\theta$ is the maximum constraint violation
(15.5.3). The iterate is compatible if there is a normal step $n$ that satisfies the linearized
constraints and $\|n\| \le \kappa_\Delta \Delta \min\{1, \kappa_\mu \Delta^\mu\}$ (15.5.5). A
trial $s$ is feasible for TRQP$(x, \Delta)$, and for some such normal step $n$ it satisfies the
tangential decrease condition AA.1m,
$$m(n) - m(s) \ge \kappa_T \chi \min\Big\{\frac{\chi}{1 + \|H\|}, \Delta\Big\},$$
where $\chi$ is the tangential criticality measure at $x + n$ and $H = B + \sum_i y_i W_i$. The
predicted decrease is $m(0) - m(s)$.

The criticality measure is `ConnGouldToint.Chapter15.sqpFilterCriticality`, evaluated with the
gradient $\nabla f(x + n)$. -/
def compositeFilterSQPStep [Fintype ι] [CompleteSpace E]
    (P : FilterSQPParams) (f : E → ℝ) (c : ι → E → ℝ) (eq : ι → Bool)
    (κΔ κμ μ κT : ℝ) (state : FilterSQPState E ι) (next : Option (FilterSQPState E ι)) : Prop :=
  FilterSQPStep P (filterSQPPair f c eq)
    (fun a ↦ ∃ n, filterSQPNormal eq c κΔ κμ μ a n)
    (fun a s ↦ filterSQPFeasible eq c a s ∧ ∃ n, filterSQPNormal eq c κΔ κμ μ a n ∧
      let χ := sqpFilterCriticality eq (fun i ↦ c i a.x) (fun i ↦ gradient (c i) a.x)
        (gradient f (a.x + n)) n
      let H := a.B + ∑ i, a.multiplier i • a.W i
      κT * χ * min (χ / (1 + ‖H‖)) a.radius ≤ filterSQPModel f a n - filterSQPModel f a s)
    (fun a s ↦ filterSQPModel f a 0 - filterSQPModel f a s) state next

/-- **Algorithm 15.5.2** of [conn2000trust] and equation (15.5.45). One iteration of the single-step
filter algorithm. It has the same pair and the same transitions as Algorithm 15.5.1, but the
iterate is compatible if TRQP$(x, \Delta)$ has a feasible step. A trial $s$ is feasible for
TRQP$(x, \Delta)$ and satisfies (15.5.45),
$$m(0) - m(s) \ge \varepsilon \min\{\pi(x), \Delta\},$$
for a supplied criticality measure $\pi$. The predicted decrease is $m(0) - m(s)$. -/
def singleFilterSQPStep [Fintype ι] [CompleteSpace E]
    (P : FilterSQPParams) (f : E → ℝ) (c : ι → E → ℝ) (eq : ι → Bool)
    (π : E → ℝ) (ε : ℝ) (state : FilterSQPState E ι) (next : Option (FilterSQPState E ι)) : Prop :=
  FilterSQPStep P (filterSQPPair f c eq)
    (fun a ↦ ∃ s, filterSQPFeasible eq c a s)
    (fun a s ↦ filterSQPFeasible eq c a s ∧
      ε * min (π a.x) a.radius ≤ filterSQPModel f a 0 - filterSQPModel f a s)
    (fun a s ↦ filterSQPModel f a 0 - filterSQPModel f a s) state next

/-- **Algorithms 15.5.1 and 15.5.2** of [conn2000trust]. If a transition goes from a state to a next
state, and the pair of the current iterate is acceptable to the current filter, then the pair of
the next iterate is acceptable to the next filter. Thus every iterate that continues the run is
acceptable at the start of its iteration. -/
theorem FilterSQPStep.accepts_next {P : FilterSQPParams} {pair : E → ℝ × ℝ}
    {compatible : FilterSQPState E ι → Prop} {trial : FilterSQPState E ι → E → Prop}
    {prediction : FilterSQPState E ι → E → ℝ} {state next : FilterSQPState E ι}
    (hstep : FilterSQPStep P pair compatible trial prediction state (some next))
    (hstate : sqpFilterAccepts P.margin state.entries (pair state.x)) :
    sqpFilterAccepts P.margin next.entries (pair next.x) := by
  cases hstep with
  | restored next _ _ h _ _ _ => exact h
  | rejected => exact hstate
  | accepted s next _ _ ha hx hF _ _ =>
    rw [hx, hF]
    split
    · exact ha.1
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with he | hz
      · exact he.symm ▸ ha.2.1
      · exact ha.1 z hz.1

/-- **Algorithms 15.5.1 and 15.5.2** of [conn2000trust]. If a transition goes from an incompatible
state to a next state, then the next state is compatible. Thus the transition is a restoration,
and a restoration is not followed directly by another restoration. -/
theorem FilterSQPStep.compatible_of_restored {P : FilterSQPParams} {pair : E → ℝ × ℝ}
    {compatible : FilterSQPState E ι → Prop} {trial : FilterSQPState E ι → E → Prop}
    {prediction : FilterSQPState E ι → E → ℝ} {state next : FilterSQPState E ι}
    (hstep : FilterSQPStep P pair compatible trial prediction state (some next))
    (h : ¬ compatible state) : compatible next := by
  cases hstep with
  | restored next _ _ _ _ hr _ => exact hr
  | rejected _ _ hr => exact (h hr).elim
  | accepted _ _ hr => exact (h hr).elim

end ConnGouldToint.Chapter15
