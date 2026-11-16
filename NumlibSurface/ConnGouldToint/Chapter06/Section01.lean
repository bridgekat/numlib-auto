/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum
import Numlib.Optimization.ModelBased.RatioTest

/-!
# Conn, Gould and Toint, Section 6.1: The basic trust-region algorithm

This module formalizes the basic trust-region algorithm (BTR), Algorithm 6.1.1 of [conn2000trust],
on a real vector space $E$. At iteration $k$ the algorithm has an iterate $x_k$, a radius
$\Delta_k > 0$, a norm $\|\cdot\|_k$ and a model $m_k$ of the objective $f$. It computes a step
$s_k$ in the trust region $\|s_k\|_k \le \Delta_k$ (6.1.2) with sufficient model decrease, and it
evaluates the ratio
$$\rho_k = \frac{f(x_k) - f(x_k + s_k)}{m_k(x_k) - m_k(x_k + s_k)}$$
of (6.1.4). The step is accepted if $\rho_k \ge \eta_1$, and the radius is updated by the rule
(6.1.5), with parameters restricted by (6.1.3) and example values (6.1.6). The module also defines
the quadratic model (6.1.7) and proves the basic facts about a run: the radii stay positive, the
objective is nonincreasing, and a radius lower bound used in Theorem 6.4.3 and in Section 6.6.

The proofs use the backbone module `Numlib.Optimization.ModelBased.RatioTest`.

## Main definitions

* Equation (6.1.2), `ConnGouldToint.Chapter06.trustRegion`: the trust region
  $\{y : \|y - x\| \le \Delta\}$.
* Equation (6.1.3), `ConnGouldToint.Chapter06.BTRParams`: the parameters $0 < \eta_1 \le \eta_2 < 1$
  and $0 < \gamma_1 \le \gamma_2 < 1$.
* Equation (6.1.4), `ConnGouldToint.Chapter06.btrRatio`: the ratio of the actual reduction to the
  model reduction.
* Equation (6.1.5), `ConnGouldToint.Chapter06.BTRRadiusUpdate`: the radius update rule.
* Equation (6.1.6), `ConnGouldToint.Chapter06.defaultBTRParams`: the example values $\eta_1 = 0.01$,
  $\eta_2 = 0.9$, $\gamma_1 = \gamma_2 = 1/2$.
* Equation (6.1.7), `ConnGouldToint.Chapter06.quadraticModel`: the quadratic model $c + \langle g, s
  \rangle + \frac{1}{2} \langle s, Hs \rangle$.
* Algorithm 6.1.1, `ConnGouldToint.Chapter06.BTRRun`: an infinite run of the basic trust-region
  algorithm.

## Main results

* Theorem 6.4.3, `ConnGouldToint.Chapter06.BTRRun.delta_lower_bound`: if small radii force very
  successful iterations, the radii are bounded below.
* Equations (6.6.22) and (6.6.40), `ConnGouldToint.Chapter06.BTRRun.delta_lower_bound_from`: the
  same bound from a given iteration on.

## Implementation notes

* Algorithm 6.1.1 leaves the sufficient model decrease test unspecified. A run is parametrized by
  that test, a predicate on the index, the model, the iterate and the step.
* A run requires the predicted decrease $m_k(x_k) - m_k(x_k + s_k)$ to be positive at every
  iteration, so that the ratio $\rho_k$ is defined.
* The norms $\|\cdot\|_k$ are seminorms that vanish only at $0$, that is, norms. The rule (6.1.5)
  puts no upper bound on the expansion of the radius.
-/

namespace ConnGouldToint.Chapter06

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Equation (6.1.2)** of [conn2000trust]. For a seminorm $\|\cdot\|$ on $E$, a center $x \in E$
and a radius $\Delta \in \mathbb{R}$, the **trust region** is
$$\mathcal{B} = \{y \in E : \|y - x\| \le \Delta\}.$$
-/
def trustRegion (p : Seminorm ℝ E) (x : E) (Δ : ℝ) : Set E :=
  {y | p (y - x) ≤ Δ}

/-- A point $y$ lies in the trust region about $x$ of radius $\Delta$ if and only if
$\|y - x\| \le \Delta$. -/
@[simp]
theorem mem_trustRegion {p : Seminorm ℝ E} {x y : E} {Δ : ℝ} :
    y ∈ trustRegion p x Δ ↔ p (y - x) ≤ Δ :=
  Iff.rfl

/-- **Equation (6.1.3)** of [conn2000trust]. The **parameters of the basic trust-region algorithm**
are real numbers $\eta_1, \eta_2, \gamma_1, \gamma_2$ with
$$0 < \eta_1 \le \eta_2 < 1 \quad \text{and} \quad 0 < \gamma_1 \le \gamma_2 < 1.$$
-/
structure BTRParams where
  /-- The acceptance threshold $\eta_1$ for a successful iteration. -/
  η₁ : ℝ
  /-- The threshold $\eta_2$ for a very successful iteration. -/
  η₂ : ℝ
  /-- The smallest contraction factor $\gamma_1$ of the radius. -/
  γ₁ : ℝ
  /-- The largest contraction factor $\gamma_2$ of the radius. -/
  γ₂ : ℝ
  /-- The threshold $\eta_1$ is positive. -/
  eta₁_pos : 0 < η₁
  /-- The thresholds satisfy $\eta_1 \le \eta_2$. -/
  eta₁_le_eta₂ : η₁ ≤ η₂
  /-- The threshold $\eta_2$ is less than one. -/
  eta₂_lt_one : η₂ < 1
  /-- The factor $\gamma_1$ is positive. -/
  gamma₁_pos : 0 < γ₁
  /-- The factors satisfy $\gamma_1 \le \gamma_2$. -/
  gamma₁_le_gamma₂ : γ₁ ≤ γ₂
  /-- The factor $\gamma_2$ is less than one. -/
  gamma₂_lt_one : γ₂ < 1

/-- **Equation (6.1.4)** of [conn2000trust]. For an objective $f$, a model $m$, an iterate $x$ and a
step $s$, the **reduction ratio** is
$$\rho = \frac{f(x) - f(x + s)}{m(x) - m(x + s)}.$$

It is `Optimization.reductionRatio` with the predicted decrease $m(x) - m(x + s)$. Division by a
zero predicted decrease gives $0$ by Lean's convention. -/
noncomputable def btrRatio (f m : E → ℝ) (x s : E) : ℝ :=
  Optimization.reductionRatio f x s (m x - m (x + s))

/-- **Equation (6.1.5)** of [conn2000trust]. For parameters $\eta_1, \eta_2, \gamma_1, \gamma_2$, a
ratio $\rho$ and radii $\Delta$, $\Delta'$, the new radius $\Delta'$ **follows the radius
update** if
$$\Delta' \in \begin{cases}
  [\Delta, \infty) & \text{if } \rho \ge \eta_2, \\
  [\gamma_2 \Delta, \Delta] & \text{if } \eta_1 \le \rho < \eta_2, \\
  [\gamma_1 \Delta, \gamma_2 \Delta] & \text{if } \rho < \eta_1.
\end{cases}$$
-/
structure BTRRadiusUpdate (P : BTRParams) (ρ Δ Δ' : ℝ) : Prop where
  /-- A very successful iteration, $\rho \ge \eta_2$, does not decrease the radius. -/
  very_successful : P.η₂ ≤ ρ → Δ ≤ Δ'
  /-- A successful iteration, $\eta_1 \le \rho < \eta_2$, gives
  $\gamma_2 \Delta \le \Delta' \le \Delta$. -/
  successful : P.η₁ ≤ ρ → ρ < P.η₂ → P.γ₂ * Δ ≤ Δ' ∧ Δ' ≤ Δ
  /-- An unsuccessful iteration, $\rho < \eta_1$, gives $\gamma_1 \Delta \le \Delta' \le \gamma_2
  \Delta$. -/
  unsuccessful : ρ < P.η₁ → P.γ₁ * Δ ≤ Δ' ∧ Δ' ≤ P.γ₂ * Δ

/-- If $\Delta > 0$ and $\Delta'$ follows the radius update (6.1.5), then $\Delta' > 0$. -/
theorem BTRRadiusUpdate.pos {P : BTRParams} {ρ Δ Δ' : ℝ}
    (h : BTRRadiusUpdate P ρ Δ Δ') (hΔ : 0 < Δ) : 0 < Δ' := by
  by_cases h₂ : P.η₂ ≤ ρ
  · exact hΔ.trans_le (h.very_successful h₂)
  by_cases h₁ : P.η₁ ≤ ρ
  · exact (mul_pos (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂) hΔ).trans_le
      (h.successful h₁ (lt_of_not_ge h₂)).1
  · exact (mul_pos P.gamma₁_pos hΔ).trans_le (h.unsuccessful (lt_of_not_ge h₁)).1

/-- **Equation (6.1.6)** of [conn2000trust]. These parameters have the example values
$$\eta_1 = 0.01, \qquad \eta_2 = 0.9, \qquad \gamma_1 = \gamma_2 = \tfrac{1}{2}.$$
-/
noncomputable def defaultBTRParams : BTRParams where
  η₁ := 0.01
  η₂ := 0.9
  γ₁ := 1 / 2
  γ₂ := 1 / 2
  eta₁_pos := by norm_num
  eta₁_le_eta₂ := by norm_num
  eta₂_lt_one := by norm_num
  gamma₁_pos := by norm_num
  gamma₁_le_gamma₂ := le_rfl
  gamma₂_lt_one := by norm_num

/-- **Equation (6.1.7)** of [conn2000trust]. Let $F$ be a real inner product space. For
$c \in \mathbb{R}$, $g \in F$ and a linear operator $H$ on $F$, the **quadratic model** at the
step $s \in F$ from its center is
$$m(s) = c + \langle g, s \rangle + \tfrac{1}{2} \langle s, Hs \rangle.$$
-/
noncomputable def quadraticModel {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (c : ℝ) (g : F) (H : F →ₗ[ℝ] F) (s : F) : ℝ :=
  c + inner ℝ g s + (1 / 2) * inner ℝ s (H s)

/-- **Algorithm 6.1.1** of [conn2000trust] (basic trust-region algorithm). Let
$f : E \to \mathbb{R}$, let $P$ be parameters as in (6.1.3), and let `sufficient` be a predicate
that specifies the sufficient model decrease. A **run** of the algorithm consists of iterates
$x_k$, steps $s_k$, radii $\Delta_k$, norms $\|\cdot\|_k$ and models $m_k$ for
$k \in \mathbb{N}$ such that

* $\Delta_0 > 0$, and $\|s_k\|_k \le \Delta_k$,
* $s_k$ satisfies the sufficient decrease predicate for $m_k$ at $x_k$, and
  $m_k(x_k) - m_k(x_k + s_k) > 0$,
* $x_{k+1} = x_k + s_k$ if $\rho_k \ge \eta_1$, and $x_{k+1} = x_k$ otherwise, and
* $\Delta_{k+1}$ follows the radius update (6.1.5) for $\rho_k$ and $\Delta_k$.

The positivity of the predicted decrease makes the ratio $\rho_k$ defined. The source leaves the
sufficient decrease test unspecified. -/
structure BTRRun (f : E → ℝ) (P : BTRParams)
    (sufficient : ℕ → (E → ℝ) → E → E → Prop) where
  /-- The iterates $x_k$. -/
  x : ℕ → E
  /-- The steps $s_k$. -/
  s : ℕ → E
  /-- The trust-region radii $\Delta_k$. -/
  Δ : ℕ → ℝ
  /-- The trust-region norms $\|\cdot\|_k$, given as seminorms. -/
  p : ℕ → Seminorm ℝ E
  /-- Each seminorm $\|\cdot\|_k$ vanishes only at $0$, so it is a norm. -/
  norm_separates : ∀ k v, p k v = 0 → v = 0
  /-- The models $m_k$ of the objective, evaluated at points of $E$. -/
  model : ℕ → E → ℝ
  /-- The initial radius is positive: $\Delta_0 > 0$. -/
  delta_initial_pos : 0 < Δ 0
  /-- Each trial point lies in the trust region: $\|s_k\|_k \le \Delta_k$. -/
  feasible : ∀ k, x k + s k ∈ trustRegion (p k) (x k) (Δ k)
  /-- Each step satisfies the sufficient model decrease predicate. -/
  sufficient_decrease : ∀ k, sufficient k (model k) (x k) (s k)
  /-- Each predicted decrease is positive: $m_k(x_k) - m_k(x_k + s_k) > 0$. -/
  predicted_pos : ∀ k, 0 < model k (x k) - model k (x k + s k)
  /-- The next iterate is $x_k + s_k$ if $\rho_k \ge \eta_1$ and $x_k$ otherwise. -/
  iterate_update : ∀ k, x (k + 1) =
    Optimization.acceptStep P.η₁ f (x k) (s k) (model k (x k) - model k (x k + s k))
  /-- Each new radius $\Delta_{k+1}$ follows the radius update (6.1.5) for $\rho_k$ and $\Delta_k$.
  -/
  radius_update : ∀ k, BTRRadiusUpdate P (btrRatio f (model k) (x k) (s k)) (Δ k) (Δ (k + 1))

namespace BTRRun

variable {f : E → ℝ} {P : BTRParams} {sufficient : ℕ → (E → ℝ) → E → E → Prop}

/-- The **successful iterations** of a run are the indices $k$ with $\rho_k \ge \eta_1$. -/
def successful (run : BTRRun f P sufficient) : Set ℕ :=
  {k | P.η₁ ≤ btrRatio f (run.model k) (run.x k) (run.s k)}

/-- The **very successful iterations** of a run are the indices $k$ with $\rho_k \ge \eta_2$. -/
def verySuccessful (run : BTRRun f P sufficient) : Set ℕ :=
  {k | P.η₂ ≤ btrRatio f (run.model k) (run.x k) (run.s k)}

/-- Every very successful iteration of a run is successful. -/
theorem verySuccessful_subset_successful (run : BTRRun f P sufficient) :
    run.verySuccessful ⊆ run.successful :=
  fun _ hk ↦ P.eta₁_le_eta₂.trans hk

/-- Every radius of a run is positive: $\Delta_k > 0$ for all $k$. -/
theorem delta_pos (run : BTRRun f P sufficient) (k : ℕ) : 0 < run.Δ k := by
  induction k with
  | zero => exact run.delta_initial_pos
  | succ k ih => exact (run.radius_update k).pos ih

/-- **Theorem 6.4.3** of [conn2000trust], the radius bound in its proof. Let
$\theta \in \mathbb{R}$, and suppose that every iteration $k$ of a run with
$\Delta_k \le \theta$ is very successful. Then
$$\Delta_k \ge \min\{\Delta_0, \gamma_1 \theta\} \quad \text{for all } k.$$

The minimum includes the initial radius $\Delta_0$, which can be smaller than the constant
displayed in the proof of the source. -/
theorem delta_lower_bound (run : BTRRun f P sufficient) {θ : ℝ}
    (hforce : ∀ k, run.Δ k ≤ θ → k ∈ run.verySuccessful) (k : ℕ) :
    min (run.Δ 0) (P.γ₁ * θ) ≤ run.Δ k := by
  induction k with
  | zero => exact min_le_left _ _
  | succ k ih =>
    have h := run.radius_update k
    by_cases hρ : k ∈ run.verySuccessful
    · exact ih.trans (h.very_successful hρ)
    · have hθ : θ < run.Δ k := lt_of_not_ge (fun hk ↦ hρ (hforce k hk))
      have hmul := mul_le_mul_of_nonneg_left hθ.le P.gamma₁_pos.le
      have hstep : P.γ₁ * run.Δ k ≤ run.Δ (k + 1) := by
        by_cases h₁ : k ∈ run.successful
        · exact (mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (run.delta_pos k).le).trans
            (h.successful h₁ (lt_of_not_ge hρ)).1
        · exact (h.unsuccessful (lt_of_not_ge h₁)).1
      exact (min_le_right _ _).trans (hmul.trans hstep)

/-- For Algorithm 6.1.1: at a successful iteration $k$ of a run, the objective decreases by at least
$\eta_1$ times the model decrease:
$$f(x_k) - f(x_{k+1}) \ge \eta_1 (m_k(x_k) - m_k(x_k + s_k)).$$
-/
theorem objective_drop_of_successful (run : BTRRun f P sufficient) {k : ℕ}
    (hk : k ∈ run.successful) :
    P.η₁ * (run.model k (run.x k) - run.model k (run.x k + run.s k)) ≤
      f (run.x k) - f (run.x (k + 1)) := by
  have hr : P.η₁ ≤ Optimization.reductionRatio f (run.x k) (run.s k)
      (run.model k (run.x k) - run.model k (run.x k + run.s k)) := hk
  rw [run.iterate_update, Optimization.acceptStep_of_le hr]
  exact (Optimization.le_reductionRatio_iff (run.predicted_pos k)).mp hr

/-- For Algorithm 6.1.1: at an iteration $k$ of a run that is not successful, the iterate does not
change, $x_{k+1} = x_k$. -/
theorem iterate_eq_of_unsuccessful (run : BTRRun f P sufficient) {k : ℕ}
    (hk : k ∉ run.successful) : run.x (k + 1) = run.x k := by
  have hr : Optimization.reductionRatio f (run.x k) (run.s k)
      (run.model k (run.x k) - run.model k (run.x k + run.s k)) < P.η₁ := lt_of_not_ge hk
  rw [run.iterate_update, Optimization.acceptStep_of_lt hr]

/-- For Algorithm 6.1.1: the objective values $f(x_k)$ along a run are nonincreasing in $k$. -/
theorem objective_antitone (run : BTRRun f P sufficient) : Antitone (fun k ↦ f (run.x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hk : k ∈ run.successful
  · exact sub_nonneg.mp ((mul_pos P.eta₁_pos (run.predicted_pos k)).le.trans
      (run.objective_drop_of_successful hk))
  · rw [run.iterate_eq_of_unsuccessful hk]

/-- For Algorithm 6.1.1: the run restarted at iteration $n$, with $x'_k = x_{n+k}$ and the same
shift for the steps, radii, norms, models and the sufficient decrease predicate. -/
def tail (run : BTRRun f P sufficient) (n : ℕ) :
    BTRRun f P (fun k ↦ sufficient (n + k)) where
  x k := run.x (n + k)
  s k := run.s (n + k)
  Δ k := run.Δ (n + k)
  p k := run.p (n + k)
  norm_separates k := run.norm_separates (n + k)
  model k := run.model (n + k)
  delta_initial_pos := run.delta_pos n
  feasible k := run.feasible (n + k)
  sufficient_decrease k := run.sufficient_decrease (n + k)
  predicted_pos k := run.predicted_pos (n + k)
  iterate_update k := run.iterate_update (n + k)
  radius_update k := run.radius_update (n + k)

/-- **Equations (6.6.22) and (6.6.40)** of [conn2000trust], the radius bound from a given iteration.
Let $n \in \mathbb{N}$ and $\theta \in \mathbb{R}$, and suppose that every iteration $k \ge n$
of a run with $\Delta_k \le \theta$ is very successful. Then
$$\Delta_{n+j} \ge \min\{\gamma_1 \theta, \Delta_n\} \quad \text{for all } j.$$
-/
theorem delta_lower_bound_from (run : BTRRun f P sufficient) (n : ℕ) {θ : ℝ}
    (hforce : ∀ k ≥ n, run.Δ k ≤ θ → k ∈ run.verySuccessful) (j : ℕ) :
    min (P.γ₁ * θ) (run.Δ n) ≤ run.Δ (n + j) := by
  simpa only [tail, Nat.add_zero, min_comm] using (run.tail n).delta_lower_bound (θ := θ)
    (fun k hk ↦ hforce (n + k) (Nat.le_add_right _ _) hk) j

end BTRRun
end ConnGouldToint.Chapter06
