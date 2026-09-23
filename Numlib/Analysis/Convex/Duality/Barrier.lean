import Numlib.Analysis.Convex.Recession.Conjugate

/-!
# The barrier cone and the recession cone

The **barrier cone** of a set `C` is `dom (δ*(· ∣ C))`, the set of directions in which the pairing
is bounded above on `C`. For a nonempty closed convex set it is polar to the recession cone.

## Main results

* `polarCone_convexDom_supportFn` — the polar of the barrier cone of a nonempty closed convex set is
  its recession cone ([rockafellar1970convex] Corollary 14.2.1).

## References

* [rockafellar1970convex] §14.
-/

open Set

namespace ConvexAnalysis

section Barrier

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

/-- The polar of the barrier cone of a nonempty closed convex set is its recession cone: the
function-level `recessionConeFn_eq_polarCone_convexDom_convexConj` for the indicator function of
`C`.

Nonemptiness matters: for `C = ∅` the barrier cone is all of `F` and its polar is the kernel of the
pairing, while `0⁺∅` is everything. -/
theorem polarCone_convexDom_supportFn [IsCompatiblePairing B] (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty) :
    polarCone B.flip (convexDom (supportFn B C)) = recessionCone C := by
  rw [supportFn_eq_convexConj_indicatorFn, ← recessionConeFn_indicatorFn hCne,
    recessionConeFn_eq_polarCone_convexDom_convexConj (B := B)
      ⟨convexFn_indicatorFn.2 hC, closedConvex_indicatorFn hCcl, properConvex_indicatorFn.2 hCne⟩]

end Barrier

end ConvexAnalysis
