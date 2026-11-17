/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Liesen and Strakoš, §5.4: Particular computations and complexity

A tolerance determines the number of steps needed to approximate a solution. Strong optimality
compares this number across methods and requires minimality for each problem separately.
-/

namespace LiesenStrakos.Chapter05

/-- **Section 5.4** of [liesen2013krylov]. An approximation $y$ to $x$ **meets the tolerance**
$\varepsilon$ if $\|x-y\|<\varepsilon$. -/
def meetsTolerance {E : Type*} [SeminormedAddCommGroup E] (ε : ℝ) (x y : E) : Prop :=
  ‖x - y‖ < ε

/-- **Section 5.4** of [liesen2013krylov]. Let $P$ be a class of problems including their
right-hand sides, with exact solution $x(p)$ for problem $p$, and let $x_{i,k}(p)$ be
method $i$'s approximation after $k$ steps. An iteration $i$ is **strongly optimal** at tolerance
$\varepsilon$ if, for every $p$ in the class, it reaches tolerance at some step $n$ such that any
competing method that reaches tolerance does so at a step $m \ge n$. -/
def isStronglyOptimalIteration {P I E : Type*} [SeminormedAddCommGroup E]
    (ε : ℝ) (problems : Set P) (solution : P → E) (iterates : I → P → ℕ → E) (i : I) : Prop :=
  ∀ p ∈ problems, ∃ n, meetsTolerance ε (solution p) (iterates i p n) ∧
    ∀ j m, meetsTolerance ε (solution p) (iterates j p m) → n ≤ m

end LiesenStrakos.Chapter05
