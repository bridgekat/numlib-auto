/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Recession.Conjugate

/-!
# The barrier cone and the recession cone

Let $\langle \cdot, \cdot \rangle$ be a bilinear pairing of real vector spaces $E$ and $F$. The
**barrier cone** of a set $C \subseteq E$ is the effective domain of its support function
$\delta^*(\cdot \mid C)$, that is, the set of $y \in F$ for which
$\sup_{x \in C} \langle x, y \rangle < +\infty$. For a nonempty closed convex set $C$, the polar of
the barrier cone is the recession cone $0^+ C$. This is Corollary 14.2.1 of [rockafellar1970convex].

## Main results

* `ConvexAnalysis.polarCone_convexDom_supportFn`: the polar of the barrier cone of a nonempty closed
  convex set is its recession cone.
-/

open Set

namespace ConvexAnalysis

section Barrier

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

/-- **The polar of the barrier cone is the recession cone.** Let $E$ be a real locally convex
topological vector space, let $\langle \cdot, \cdot \rangle$ be a pairing of $E$ with a real
vector space $F$ such that every map $x \mapsto \langle x, y \rangle$ is continuous and every
continuous linear functional on $E$ is $\langle \cdot, y \rangle$ for some $y \in F$, and let
$C \subseteq E$ be nonempty, closed and convex. Then $$\{x \in E \mid \langle x, y \rangle \le 0
\text{ for all } y \in \operatorname{dom} \delta^*(\cdot \mid C)\} = 0^+ C.$$ This is Corollary
14.2.1 of [rockafellar1970convex].

The hypothesis $C \neq \emptyset$ is necessary: for $C = \emptyset$ the barrier cone is all of
$F$ and its polar is the kernel $\{x \mid \langle x, y \rangle = 0 \text{ for all } y\}$ of the
pairing, but $0^+ \emptyset$ is all of $E$.

The pairing condition is `ConvexAnalysis.IsCompatiblePairing B`, the support function is
`ConvexAnalysis.supportFn B C`, the polar is `ConvexAnalysis.polarCone B.flip`, and the
recession cone is `ConvexAnalysis.recessionCone C`. The result is
`ConvexAnalysis.recessionConeFn_eq_polarCone_convexDom_convexConj`, the statement for functions,
applied to the indicator function of $C$. -/
theorem polarCone_convexDom_supportFn [IsCompatiblePairing B] (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty) :
    polarCone B.flip (convexDom (supportFn B C)) = recessionCone C := by
  rw [supportFn_eq_convexConj_indicatorFn, ← recessionConeFn_indicatorFn hCne,
    recessionConeFn_eq_polarCone_convexDom_convexConj (B := B)
      ⟨convexFn_indicatorFn.2 hC, closedConvex_indicatorFn hCcl, properConvex_indicatorFn.2 hCne⟩]

end Barrier

end ConvexAnalysis
