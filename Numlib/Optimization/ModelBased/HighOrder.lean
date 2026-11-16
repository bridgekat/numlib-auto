/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.MeasureTest
import Numlib.Optimization.ModelBased.HighOrder.Orders
import Numlib.Optimization.ModelBased.HighOrder.TRq
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrder.TRqComplexity
import Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity
import Numlib.Optimization.ModelBased.HighOrder.ARqpDetailedStep
import Numlib.Optimization.ModelBased.HighOrder.ARqpC
import Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity
import Numlib.Optimization.ModelBased.HighOrder.ARqpCCall
import Numlib.Optimization.ModelBased.HighOrder.TRqCall
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy

/-!
# High-order model-based methods

This module imports the high-order model-based methods of Chapter 12 of [cartis2022evaluation],
which Chapters 13 and 14 reuse, and adds no declaration. These methods find approximate $q$-th order
critical points of a smooth function $f$, possibly on a feasible set $X$. Their termination tests
and step conditions use Taylor-decrement measures $\phi^{\delta}_{f,j}(x)$, the largest decrease of
the Taylor expansion of order $j$ of $f$ at $x$ over the feasible displacements of norm at most
$\delta$, instead of tests on the gradient and on the eigenvalues of the Hessian. The modules define
the trust-region method TRq (Algorithm 12.2.1), the adaptive-regularization method ARqp (Algorithm
12.2.2) and its composite form ARqpC (Algorithm 14.1.1), and bound the number of evaluations that
each needs.

## Contents

| Module | Subject |
|---|---|
| `MeasureTest` | approximate decrement measures and the termination test |
| `Orders` | extrema of order-indexed constants over $[1, q]$ |
| `TRq` | the trust-region method TRq, Algorithm 12.2.1 |
| `ARqp` | the adaptive-regularization method ARqp, Algorithm 12.2.2 |
| `TRqComplexity` | evaluation complexity of TRq with exact derivatives |
| `ARqpComplexity` | evaluation complexity of ARqp with exact derivatives |
| `ARqpDetailedStep` | the detailed Step 2 of ARqp, Algorithm 12.2.3 |
| `ARqpC` | the composite method ARqpC, Algorithm 14.1.1 |
| `ARqpCComplexity` | evaluation complexity of ARqpC |
| `ARqpCCall` | ARqpC runs as inner solvers of the two-phase methods |
| `TRqCall` | TRq runs as inner solvers of the two-phase methods |
| `DynamicAccuracy` | the methods with dynamic accuracy of Chapter 13 |

The module names are relative to `Numlib.Optimization.ModelBased.HighOrder`.

## Implementation notes

* The decrement measures are `Optimization.decrementMeasure` and `Optimization.taylorMeasure`.
  `MeasureTest` evaluates a decrement measure approximately by a displacement $d$ with
  $\varsigma \phi \le \Delta(d)$, as in (12.1.32), (12.2.1), (12.2.26) and (12.2.35), and derives
  the termination test, for an arbitrary decrement function.
* `TRq` builds on the generic trust-region run and is generic in the derivative data and in the sets
  of feasible displacements, so that it also covers TRq-SC of §14.2. `ARqp` builds on the generic
  adaptive-regularization run and is generic in the model data (exact, inexact or composite) and in
  the feasible set $X$.
* `TRqComplexity` and `ARqpComplexity` contain Lemmas 12.2.3–12.2.13, Theorems 12.2.5 and 12.2.14,
  and the rows TRq-SC and ARqp-SC of §14.2. They are stated on a feasible set under the anchored
  smoothness assumption `LipschitzDerivsAnchored`. `ARqpDetailedStep` proves that the detailed Step
  2 terminates for the regularized model and that its outputs are admissible.
* The model lemmas are in other modules: the error budgets in
  `Numlib.Optimization.ModelBased.HighOrderModel`, the detailed Step 2 and the step-length algebra
  in `Numlib.Optimization.ModelBased.HighOrderStep`, and the composite models in
  `Numlib.Optimization.Composite.RegularizedModel`.
-/
