/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter17.Section03
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Conn, Gould and Toint, Section 17.4: Model decrease and stopping residuals

Section 17.4 of [conn2000trust] treats the computation of the model decrease and the stopping rules.
For a conjugate-gradient line step, the model change has a closed form (17.4.1). An unconstrained
run stops when $\|\nabla f(x)\| \le \epsilon$. For constraints, the violation vector takes the
negative part of each inequality constraint. For a closed convex set $C$, the projected residual
$P_C(x - g) - x$ vanishes exactly when $x$ satisfies the first-order condition
$\langle g, y - x \rangle \ge 0$ for all $y \in C$. This module formalizes these quantities and a
corrected projected Lagrangian residual (17.4.9). The projection is `bestApprox` from
`Numlib.Analysis.Normed.Module.BestApprox`.

## Main definitions

* Equation (17.4.2), `ConnGouldToint.Chapter17.gradientSmall`: the test
  $\|\nabla f(x)\| \le \epsilon$.
* Equation (17.4.4), `ConnGouldToint.Chapter17.constraintViolation`: the constraint violation
  vector.
* Equation (17.4.7), `ConnGouldToint.Chapter17.projectedStationarityResidual`: the residual
  $P_C(x - g) - x$.
* Equation (17.4.9), `ConnGouldToint.Chapter17.projectedLagrangianResidual`: the corrected residual
  $P_C(x - (g - a)) - x$.

## Main results

* Equation (17.4.1), `ConnGouldToint.Chapter17.cgModelChange`: the model change
  $-\frac{1}{2} \alpha \langle g, v \rangle$ of a line step.
* Equation (17.4.7), `ConnGouldToint.Chapter17.projectedStationarityResidual_eq_zero_iff`: the
  residual vanishes if and only if the first-order inequality holds.
* Equation (17.4.9), `ConnGouldToint.Chapter17.projectedLagrangianResidual_eq_zero_iff`: the
  corrected residual vanishes if and only if the Lagrangian first-order inequality holds.
* `ConnGouldToint.Chapter17.printedProjectionSign_counterexample`: the printed sign gives a nonzero
  residual at a stationary point.

## Deviations from the source

* **Correction.** Equation (17.4.9) corrects the multiplier sign in the projected trial point and
  supplies a counterexample to the printed sign. See
  `ConnGouldToint.Chapter17.projectedLagrangianResidual`,
  `ConnGouldToint.Chapter17.projectedLagrangianResidual_eq_zero_iff`,
  `ConnGouldToint.Chapter17.printedProjectionSign_counterexample`.
* **Equation (17.4.9)** (correction). The trial point subtracts the Lagrangian gradient $g - a$; the
  printed sign of the multiplier term subtracts $g + a$. See
  `ConnGouldToint.Chapter17.printedProjectionSign_counterexample`.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter17

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (17.4.1)** of [conn2000trust]. Let $g, v, p \in E$, let $H : E \to E$ be a continuous
linear map and $\alpha \in \mathbb{R}$. If $\langle g, p \rangle = -\langle g, v \rangle$ and
$\alpha \langle p, H p \rangle = \langle g, v \rangle$, then
$$q(\alpha p) = -\tfrac{1}{2} \alpha \langle g, v \rangle,$$
where $q(s) = \langle g, s \rangle + \frac{1}{2} \langle s, H s \rangle$.

The model $q$ is `Subproblem.quadModel`. -/
theorem cgModelChange (g v p : E) (H : E →L[ℝ] E) (α : ℝ)
    (hpair : ⟪g, p⟫ = -⟪g, v⟫) (hline : α * ⟪p, H p⟫ = ⟪g, v⟫) :
    Subproblem.quadModel g H (α • p) = -(1 / 2 : ℝ) * α * ⟪g, v⟫ := by
  rw [Subproblem.quadModel_def, map_smul, inner_smul_right,
    real_inner_smul_left, inner_smul_right, hpair]
  nlinarith only [congrArg (α * ·) hline]

/-- **Equation (17.4.2)** of [conn2000trust]. For $f : E \to \mathbb{R}$ on a real Hilbert space
$E$, a point $x$ and $\epsilon \in \mathbb{R}$, the **absolute stopping test** is
$\|\nabla f(x)\| \le \epsilon$.

The gradient is Mathlib's `gradient`, which is $0$ where $f$ is not differentiable. -/
def gradientSmall [CompleteSpace E] (f : E → ℝ) (x : E) (ε : ℝ) : Prop :=
  ‖gradient f x‖ ≤ ε

/-- **Equation (17.4.4)** of [conn2000trust]. Let $c \in \mathbb{R}^\iota$ be the constraint values,
where each index is an inequality constraint $c_i \ge 0$ or an equality constraint $c_i = 0$.
The **constraint violation** has the entries $\min\{c_i, 0\}$ for an inequality constraint and
$c_i$ for an equality constraint.

The predicate `ineq i` is true for an inequality constraint. -/
def constraintViolation {ι : Type*} (ineq : ι → Bool) (c : ι → ℝ) : ι → ℝ :=
  fun i ↦ if ineq i then min (c i) 0 else c i

/-- **Equation (17.4.7)** of [conn2000trust]. For a set $C \subseteq E$ and $x, g \in E$, the
**projected stationarity residual** is $P_C(x - g) - x$, where $P_C$ is the projection onto $C$
and $g$ is a supplied gradient.

The projection is `bestApprox`. -/
noncomputable def projectedStationarityResidual (C : Set E) (x g : E) : E :=
  bestApprox C (x - g) - x

variable [CompleteSpace E]

/-- **Equation (17.4.7)** of [conn2000trust], characterization. Let $E$ be a real Hilbert space, let
$C \subseteq E$ be closed and convex, and let $x \in C$ and $g \in E$. Then $P_C(x - g) - x = 0$
if and only if
$$\langle g, y - x \rangle \ge 0 \quad \text{for all } y \in C.$$
-/
theorem projectedStationarityResidual_eq_zero_iff {C : Set E} (hc : IsClosed C)
    (hconv : Convex ℝ C) {x g : E} (hx : x ∈ C) :
    projectedStationarityResidual C x g = 0 ↔ ∀ y ∈ C, 0 ≤ ⟪g, y - x⟫ := by
  rw [projectedStationarityResidual, sub_eq_zero, bestApprox_eq_iff ⟨x, hx⟩ hc hconv]
  simp [hx, sub_sub_cancel_left, inner_neg_left]

/-- **Equation (17.4.9)** of [conn2000trust], corrected. For a set $C \subseteq E$ and
$x, g, a \in E$, where $a$ is the multiplier-weighted sum of the equality constraint gradients,
the **projected Lagrangian residual** is
$$P_C\bigl(x - (g - a)\bigr) - x.$$

**Correction.** The printed sign of the multiplier term gives the trial point $x - g - a$, which
subtracts the term $a$ twice relative to stationarity of the Lagrangian gradient $g - a$. At a
stationary point the printed residual can be nonzero; see
`ConnGouldToint.Chapter17.printedProjectionSign_counterexample`.

**Correction.** The projection uses the trial point obtained by subtracting the Lagrangian gradient.
With the source convention that this gradient is the objective gradient minus the
multiplier-weighted constraint gradients, the multiplier term has a plus sign in the trial point.
The counterexample separates the two signs.
-/
noncomputable def projectedLagrangianResidual (C : Set E) (x g a : E) : E :=
  projectedStationarityResidual C x (g - a)

/-- **Equation (17.4.9)** of [conn2000trust], characterization. Let $E$ be a real Hilbert space, let
$C \subseteq E$ be closed and convex, and let $x \in C$ and $g, a \in E$. Then the corrected
projected Lagrangian residual is $0$ if and only if
$$\langle g - a, y - x \rangle \ge 0 \quad \text{for all } y \in C.$$

**Correction.** The projection uses the trial point obtained by subtracting the Lagrangian gradient.
With the source convention that this gradient is the objective gradient minus the
multiplier-weighted constraint gradients, the multiplier term has a plus sign in the trial point.
The counterexample separates the two signs.
-/
theorem projectedLagrangianResidual_eq_zero_iff {C : Set E} (hc : IsClosed C)
    (hconv : Convex ℝ C) {x g a : E} (hx : x ∈ C) :
    projectedLagrangianResidual C x g a = 0 ↔ ∀ y ∈ C, 0 ≤ ⟪g - a, y - x⟫ :=
  projectedStationarityResidual_eq_zero_iff hc hconv hx

/-- The printed sign in equation (17.4.9) of [conn2000trust] is wrong. On $C = \mathbb{R}$ at
$x = 0$, with $g = a = 1$, the Lagrangian gradient $g - a$ vanishes and the corrected residual
is $0$, but the printed residual $P_C(x - g - a) - x = -2$ is nonzero.

**Correction.** The projection uses the trial point obtained by subtracting the Lagrangian gradient.
With the source convention that this gradient is the objective gradient minus the
multiplier-weighted constraint gradients, the multiplier term has a plus sign in the trial point.
The counterexample separates the two signs.
-/
theorem printedProjectionSign_counterexample :
    projectedLagrangianResidual Set.univ (0 : ℝ) 1 1 = 0 ∧
      bestApprox Set.univ ((0 : ℝ) - 1 - 1) - 0 ≠ 0 := by
  have hproj (z : ℝ) : bestApprox Set.univ z = z :=
    (bestApprox_eq_iff Set.univ_nonempty isClosed_univ convex_univ).mpr
      ⟨Set.mem_univ z, by simp⟩
  norm_num [projectedLagrangianResidual, projectedStationarityResidual, hproj]

end ConnGouldToint.Chapter17
