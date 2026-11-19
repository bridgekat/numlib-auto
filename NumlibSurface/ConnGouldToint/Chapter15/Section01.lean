/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Conn, Gould and Toint, Section 15.1: The nonlinear programs of SQP

This module states the two nonlinear programs that the sequential quadratic programming (SQP)
methods of Chapter 15 of [conn2000trust] solve. The mixed program (15.1.1) is
$$\min_{x \in E} f(x) \quad \text{subject to} \quad c_i(x) = 0 \ (i \in \mathcal{E}), \qquad c_j(x)
  \ge 0 \ (j \in \mathcal{I}),$$
and the equality program (15.1.2) has only the equality constraints. A solution is a global
minimizer of $f$ on the feasible set. The equality program is the mixed program with no inequality
constraints, and continuous constraints give a closed feasible set.

## Main definitions

* Equation (15.1.1), `ConnGouldToint.Chapter15.nonlinearFeasibleSet`: the feasible set of the mixed
  program.
* Equation (15.1.1), `ConnGouldToint.Chapter15.IsMixedNonlinearSolution`: a feasible point that
  minimizes $f$ on the feasible set.
* Equation (15.1.2), `ConnGouldToint.Chapter15.IsEqualityNonlinearSolution`: a solution of the
  equality program.

## Main results

* Equations (15.1.1)–(15.1.2),
  `ConnGouldToint.Chapter15.isMixedNonlinearSolution_iff_isEqualityNonlinearSolution`: with no
  inequality constraints, the two solution notions agree.
* `ConnGouldToint.Chapter15.isClosed_nonlinearFeasibleSet`: continuous constraints give a closed
  feasible set.

## Implementation notes

* The equality and inequality constraints are two families `cEq : ι → E → ℝ` and `cIneq : κ → E → ℝ`
  with separate index types. The index sets $\mathcal{E}$ and $\mathcal{I}$ of the source are `ι`
  and `κ`.

## Deviations from the source

* **Generalization.** The mixed and equality problems use arbitrary index types and an explicit
  global feasibility condition. See `ConnGouldToint.Chapter15.nonlinearFeasibleSet`,
  `ConnGouldToint.Chapter15.IsMixedNonlinearSolution`,
  `ConnGouldToint.Chapter15.IsEqualityNonlinearSolution`,
  `ConnGouldToint.Chapter15.isMixedNonlinearSolution_iff_isEqualityNonlinearSolution`.
-/

namespace ConnGouldToint.Chapter15

variable {E ι κ : Type*}

/-- **Equation (15.1.1)** of [conn2000trust]. For constraint functions $c_i : E \to \mathbb{R}$,
$i \in \mathcal{E}$, and $c_j : E \to \mathbb{R}$, $j \in \mathcal{I}$, the **feasible set** of
the mixed program is
$$\{x \in E : c_i(x) = 0 \text{ for all } i \in \mathcal{E}, \ c_j(x) \ge 0 \text{ for all } j
  \in \mathcal{I}\}.$$

The two constraint families are indexed by separate types `ι` and `κ`.

**Generalization.** These definitions use arbitrary index types and objective domain. They express
global minimization with feasibility separately. The equality restriction is proved by making the
inequality index type empty.
-/
def nonlinearFeasibleSet (cEq : ι → E → ℝ) (cIneq : κ → E → ℝ) : Set E :=
  {x | (∀ i, cEq i x = 0) ∧ ∀ j, 0 ≤ cIneq j x}

/-- **Equation (15.1.1)** of [conn2000trust]. A point $x \in E$ **solves the mixed program** if $x$
lies in the feasible set of `ConnGouldToint.Chapter15.nonlinearFeasibleSet` and $f(x) \le f(y)$
for every feasible $y$.

**Generalization.** These definitions use arbitrary index types and objective domain. They express
global minimization with feasibility separately. The equality restriction is proved by making the
inequality index type empty.
-/
def IsMixedNonlinearSolution (f : E → ℝ) (cEq : ι → E → ℝ)
    (cIneq : κ → E → ℝ) (x : E) : Prop :=
  x ∈ nonlinearFeasibleSet cEq cIneq ∧ IsMinOn f (nonlinearFeasibleSet cEq cIneq) x

/-- **Equation (15.1.2)** of [conn2000trust]. A point $x \in E$ **solves the equality program** if
$c_i(x) = 0$ for all $i \in \mathcal{E}$ and $f(x) \le f(y)$ for every $y$ with $c_i(y) = 0$ for
all $i \in \mathcal{E}$.

**Generalization.** These definitions use arbitrary index types and objective domain. They express
global minimization with feasibility separately. The equality restriction is proved by making the
inequality index type empty.
-/
def IsEqualityNonlinearSolution (f : E → ℝ) (cEq : ι → E → ℝ) (x : E) : Prop :=
  (∀ i, cEq i x = 0) ∧ IsMinOn f {y | ∀ i, cEq i y = 0} x

/-- **Equations (15.1.1)–(15.1.2)** of [conn2000trust]. If the inequality index set $\mathcal{I}$ is
empty, then $x$ solves the mixed program (15.1.1) if and only if $x$ solves the equality program
(15.1.2).

The empty index set is the hypothesis `[IsEmpty κ]`; the inequality functions `cIneq` are then
arbitrary.

**Generalization.** These definitions use arbitrary index types and objective domain. They express
global minimization with feasibility separately. The equality restriction is proved by making the
inequality index type empty.
-/
theorem isMixedNonlinearSolution_iff_isEqualityNonlinearSolution [IsEmpty κ]
    (f : E → ℝ) (cEq : ι → E → ℝ) (cIneq : κ → E → ℝ) (x : E) :
    IsMixedNonlinearSolution f cEq cIneq x ↔ IsEqualityNonlinearSolution f cEq x := by
  have h : nonlinearFeasibleSet cEq cIneq = {y | ∀ i, cEq i y = 0} := by
    ext y
    simp [nonlinearFeasibleSet]
  simp [IsMixedNonlinearSolution, IsEqualityNonlinearSolution, h]

/-- Let $E$ be a topological space. If every equality constraint $c_i$ and every inequality
constraint $c_j$ is continuous, then the feasible set of the mixed program (15.1.1) is closed. -/
theorem isClosed_nonlinearFeasibleSet [TopologicalSpace E]
    {cEq : ι → E → ℝ} {cIneq : κ → E → ℝ}
    (hEq : ∀ i, Continuous (cEq i)) (hIneq : ∀ j, Continuous (cIneq j)) :
    IsClosed (nonlinearFeasibleSet cEq cIneq) := by
  have h : nonlinearFeasibleSet cEq cIneq =
      (⋂ i, {x | cEq i x = 0}) ∩ (⋂ j, {x | 0 ≤ cIneq j x}) := by
    ext x
    simp [nonlinearFeasibleSet]
  rw [h]
  exact (isClosed_iInter fun i ↦ isClosed_eq (hEq i) continuous_const).inter
    (isClosed_iInter fun j ↦ isClosed_le continuous_const (hIneq j))

end ConnGouldToint.Chapter15
