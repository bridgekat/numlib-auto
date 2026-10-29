import Numlib.Optimization.Constrained.TwoPhase.Basic
import Numlib.Optimization.Constrained.TwoPhase.Run
import Numlib.Optimization.Constrained.TwoPhase.Complexity

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
  (`Constrained.TargetFollowingSeq.IsInnerContract`) and the evaluation complexity of Phase 2.
-/
