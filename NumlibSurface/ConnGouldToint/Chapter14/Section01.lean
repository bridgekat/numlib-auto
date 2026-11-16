/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Conn, Gould and Toint, Section 14.1: Motivation and basic notation for penalty methods

This module fixes the setting of Chapter 14 of [conn2000trust]: the equality-constrained problem of
minimizing $f(x)$ subject to $c(x) = 0$, where $f : E \to \mathbb{R}$ is defined on a real normed
space $E$ and $c : E \to F$ takes values in a real inner product space $F$. It defines the standing
smoothness assumption AW.1 and the Lagrangian (14.1.4).

## Main definitions

* Assumption AW.1, `ConnGouldToint.Chapter14.AW1`: $f$ and $c$ are twice continuously
  differentiable.
* Equation (14.1.4), `ConnGouldToint.Chapter14.lagrangian`: the Lagrangian
  $\ell(x, y) = f(x) - \langle y, c(x) \rangle$.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter14

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Assumption AW.1** of [conn2000trust]. The objective $f : E \to \mathbb{R}$ and the constraint
map $c : E \to F$ are twice continuously differentiable. -/
def AW1 (f : E → ℝ) (c : E → F) : Prop :=
  ContDiff ℝ 2 f ∧ ContDiff ℝ 2 c

/-- **Equation (14.1.4)** of [conn2000trust]. The **Lagrangian** of the equality-constrained problem
is
$$\ell(x, y) = f(x) - \langle y, c(x) \rangle$$
for $x \in E$ and a multiplier $y \in F$.

The Lean argument order is `lagrangian f c y x`, with the multiplier before the point. -/
def lagrangian (f : E → ℝ) (c : E → F) (y : F) (x : E) : ℝ :=
  f x - ⟪y, c x⟫

end ConnGouldToint.Chapter14
