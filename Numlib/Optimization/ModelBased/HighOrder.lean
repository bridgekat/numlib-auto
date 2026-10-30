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

Umbrella module for the high-order model-based methods of [cartis2022evaluation] (Chapter 12, reused
in Chapters 13–14), whose termination tests and step conditions are expressed with Taylor-decrement
measures (`Optimization.decrementMeasure`, `Optimization.taylorMeasure`: `φ^δ_{f,j}`) rather than
gradient and eigenvalue tests. Its modules, under `Numlib.Optimization.ModelBased.HighOrder`,
are:

* `MeasureTest`: approximate evaluation of a decrement measure by a displacement `d` with
  `ς φ ≤ Δ(d)` ((12.1.32), (12.2.1), (12.2.26), (12.2.35)) and the resulting termination test,
  for an arbitrary decrement function;
* `Orders`: extrema of order-indexed constants over `[1, q]`;
* `TRq`: TRq (Algorithm 12.2.1) on top of the generic trust-region run, generic in the derivative
  data and the feasible displacement sets (TRq-SC of §14.2);
* `ARqp`: ARqp (Algorithm 12.2.2) on top of the generic adaptive-regularization run, generic in the
  model data (exact, inexact, composite) and in a feasible set `X`;
* `TRqComplexity`, `ARqpComplexity`: the evaluation-complexity analyses of TRq and ARqp with exact
  derivatives (Lemmas 12.2.3–12.2.13, Theorems 12.2.5 and 12.2.14, and the TRq-SC and ARqp-SC rows
  of §14.2), stated on a feasible set under the anchored smoothness assumption
  `LipschitzDerivsAnchored`;
* `ARqpDetailedStep`: termination of the detailed Step 2 (Algorithm 12.2.3) for the regularized
  model and admissibility of its outputs;
* `ARqpC`, `ARqpCComplexity`: the composite method ARqpC (Algorithm 14.1.1) and its evaluation
  complexity;
* `ARqpCCall`, `TRqCall`: ARqpC and TRq runs as inner solvers of the two-phase methods;
* `DynamicAccuracy`: the methods with dynamic accuracy of Chapter 13.

The model lemmas are in `Numlib.Optimization.ModelBased.HighOrderModel` (error budgets),
`Numlib.Optimization.ModelBased.HighOrderStep` (the detailed Step 2, step-length algebra) and
`Numlib.Optimization.Composite.RegularizedModel` (composite models). -/
