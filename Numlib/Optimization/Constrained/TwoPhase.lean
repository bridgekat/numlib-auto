/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.Basic
import Numlib.Optimization.Constrained.TwoPhase.Run
import Numlib.Optimization.Constrained.TwoPhase.Complexity
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Basic
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.ARqpCalls
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.TRqCalls
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.OneStep
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.OrderBounds

/-!
# Two-phase target-following methods

This module imports the analysis of the two-phase target-following methods of [cartis2022evaluation]
for the problem of minimizing $f(x)$ subject to $x \in \mathcal{X}$ and $c(x) = 0$: TPp-GC
(Algorithm 7.2.1) and its high-order form TPqp-GC (Algorithm 14.3.2). Phase 1 finds an approximately
feasible point. Phase 2 follows a decreasing sequence of targets $t_k$ for the objective value and,
for each target, calls an inner method that decreases the norm of the target residual
$r(x, t_k) = (c(x), f(x) - t_k)$, or equivalently the merit function
$\mu(x, t_k) = \tfrac12 \|r(x, t_k)\|^2$. The modules define the targets and the outer loop, state
the contracts that an inner method must satisfy, and bound the number of evaluations of $f$, $c$ and
their derivatives. This module adds no declaration.

## Contents

| Module | Subject |
|---|---|
| `Basic` | targets, Lemmas 7.2.3–7.2.4, counting lemmas |
| `Run` | the outer loop of Phase 2 and its output |
| `Complexity` | inner contract, complexity of Phase 2 |
| `HighOrder.Basic` | high-order runs of TPqp-GC |
| `HighOrder.Complexity` | Lemma 14.3.8, Theorem 14.3.9 |
| `HighOrder.ARqpCalls` | inner calls that are ARqp runs |
| `HighOrder.TRqCalls` | inner calls that are TRq runs |
| `HighOrder.OneStep` | inner calls of one successful step |
| `HighOrder.OrderBounds` | inequalities between complexity orders |

The module names are relative to `Numlib.Optimization.Constrained.TwoPhase`.

## Implementation notes

* `Numlib.Optimization.Constrained.TwoPhase.Basic` defines the targets,
  `Constrained.IsTargetSequence`. `Numlib.Optimization.Constrained.TwoPhase.Run` defines the outer
  loop of Phase 2, `Constrained.TargetFollowingSeq` and `Constrained.IsTargetFollowingRun`.
  `Numlib.Optimization.Constrained.TwoPhase.Complexity` states the contract of the inner method,
  `Constrained.TargetFollowingSeq.IsInnerContract`.
* `Numlib.Optimization.Constrained.TwoPhase.HighOrder.Basic` defines the high-order run,
  `Constrained.HighOrderTargetSeq` and `Constrained.IsHighOrderTargetRun`, with the criticality test
  `Constrained.targetCrit`, and constructs runs from an inner oracle.
  `Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity` states the merit-decrease
  contracts of the inner method. The modules `ARqpCalls` and `TRqCalls` make the inner calls runs of
  the regularization method ARqp or of the trust-region method TRq and prove the contracts for them,
  and `OneStep` treats Phase-2 data whose inner calls make one successful iteration each.
* The examples of runs, the modules under
  `Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples`, are not imported here.
-/
