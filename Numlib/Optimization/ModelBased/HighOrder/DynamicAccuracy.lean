/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.Basic
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqIDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpDAStep
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDAExistence
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqEDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpEDA

/-!
# High-order methods with dynamic accuracy

This module imports the high-order methods of Chapter 13 of [cartis2022evaluation] and the
corresponding rows of §14.2, and adds no declaration. These methods use inexact derivatives, and the
methods with explicit dynamic accuracy also use inexact function values; the algorithm itself
controls the accuracy. The methods are the trust-region methods TRqIDA and TRqEDA and the
adaptive-regularization methods ARqpIDA and ARqpEDA, where IDA stands for implicit and EDA for
explicit dynamic accuracy. The modules define the runs of each method, bound the number of
evaluations that the run needs, and prove that runs exist.

## Contents

| Module | Subject |
|---|---|
| `Basic` | Taylor's theorem and derivative bounds at anchors, inexact jets |
| `TRqIDA` | TRqIDA: Lemmas 13.1.1–13.1.7, Theorem 13.1.8, existence of runs |
| `ARqpDAStep` | one iteration of ARqpIDA and ARqpEDA: Lemmas 13.1.9–13.1.13 |
| `ARqpIDA` | ARqpIDA: Lemmas 13.1.14–13.1.18, Theorem 13.1.19 |
| `ARqpIDAExistence` | existence of ARqpIDA runs |
| `TRqEDA` | TRqEDA, with inexact function values |
| `ARqpEDA` | ARqpEDA, with inexact function values |

The module names are relative to `Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy`.

## Implementation notes

* `Basic` proves the consequences of `LipschitzDerivsAnchored` of order $0$: Taylor's theorem,
  bounds on the derivatives at the anchors, and bounds on inexact jets.
* `TRqIDA` defines the step predicate of TRqIDA, which TRqEDA shares, and the runs
  `Optimization.IsTRqIDARun` on a feasible set. `ARqpDAStep` defines the step predicates of ARqpIDA,
  which ARqpEDA shares, the control of the radii and the step-length algebra. `ARqpIDA` defines the
  runs `Optimization.IsARqpIDARun`.
* `TRqEDA` and `ARqpEDA` together contain Lemmas 13.3.1–13.3.7 and Theorems 13.3.4 and 13.3.8.
* All analyses are stated on a feasible set $X \subseteq C$ under
  `LipschitzDerivsAnchored f C A 0 p L`, with an anchor set $A$ that contains the sublevel set of
  the starting point. The unconstrained methods are the case $X = C = A = E$, the whole space.
-/
