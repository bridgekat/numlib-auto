import Numlib.Optimization.Constrained.TwoPhase.Basic
import Numlib.Optimization.Constrained.TwoPhase.Run
import Numlib.Optimization.Constrained.TwoPhase.Complexity
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Basic
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity

/-!
# Two-phase target-following methods

Umbrella module for the analysis of the two-phase target-following methods of
[cartis2022evaluation] (TPp-GC, Algorithm 7.2.1, and TPqp-GC, Algorithm 14.3.2) for
`min f(x)` subject to `x ∈ 𝒳`, `c(x) = 0`:

* `Numlib.Optimization.Constrained.TwoPhase.Basic`: the targets (`Constrained.IsTargetSequence`,
  Lemmas 7.2.3–7.2.4) and the counting lemmas;
* `Numlib.Optimization.Constrained.TwoPhase.Run`: the outer loop of Phase 2
  (`Constrained.TargetFollowingSeq`, `Constrained.IsTargetFollowingRun`) and its output;
* `Numlib.Optimization.Constrained.TwoPhase.Complexity`: the inner-method contract
  (`Constrained.TargetFollowingSeq.IsInnerContract`) and the evaluation complexity of Phase 2;
* `Numlib.Optimization.Constrained.TwoPhase.HighOrder.Basic`: the high-order run of TPqp-GC
  (`Constrained.HighOrderTargetSeq`, `Constrained.IsHighOrderTargetRun`, the criticality test
  `Constrained.targetCrit`) and the construction of runs from an inner oracle;
* `Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity`: the merit-decrease contracts of
  the inner method and the evaluation complexity of the high-order run (Lemma 14.3.8 and
  Theorem 14.3.9, corrected).
-/
