import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.Basic
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqIDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpDAStep
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDAExistence
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqEDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpEDA

/-!
# High-order methods with dynamic accuracy

Umbrella module for the high-order methods with inexact derivatives (and, for explicit dynamic
accuracy, inexact function values) whose accuracy the algorithm controls: TRqIDA, ARqpIDA, TRqEDA
and ARqpEDA ([cartis2022evaluation], Chapter 13, and the corresponding rows of §14.2). Its
modules, under `Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy`, are:

* `Basic`: order-`0` consequences of `LipschitzDerivsAnchored` (Taylor's theorem, derivative bounds
  at anchors, bounds on inexact jets);
* `TRqIDA`: the TRqIDA step predicate (shared with TRqEDA), runs on a feasible set
  `Optimization.IsTRqIDARun`, their analysis (Lemmas 13.1.1–13.1.7, Theorem 13.1.8) and the
  existence of runs;
* `ARqpDAStep`: the ARqpIDA step predicates (shared with ARqpEDA), the radii control, the
  one-iteration lemmas (Lemmas 13.1.9–13.1.13) and the step-length algebra;
* `ARqpIDA`, `ARqpIDAExistence`: runs `Optimization.IsARqpIDARun`, their analysis (Lemmas
  13.1.14–13.1.18, Theorem 13.1.19) and the existence of runs;
* `TRqEDA`, `ARqpEDA`: the explicit-dynamic-accuracy runs with inexact function values and their
  analyses (Lemmas 13.3.1–13.3.7, Theorems 13.3.4 and 13.3.8).

All analyses are stated on a feasible set `X ⊆ C` under `LipschitzDerivsAnchored f C A 0 p L` with
an anchor set `A` containing the sublevel set of the starting point; the unconstrained methods are
the case `X = C = A = univ`. -/
