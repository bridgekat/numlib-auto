/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Operations.Image

/-!
# Closedness of inverse images under linear maps

Let $A : E \to G$ be a continuous linear map between real topological vector spaces, and let
$g : G \to [-\infty, +\infty]$. The inverse image $gA : x \mapsto g(Ax)$ of a closed function $g$ is
closed. This is the closedness counterpart of `ConvexAnalysis.convexFn_compLin`, which states that
$gA$ is convex when $g$ is. The presentation follows [rockafellar1970convex], §5 and §7.

A closed function is not the same as a lower semicontinuous one. A function is closed if and only if
it is the constant $-\infty$, or it is lower semicontinuous and never takes the value $-\infty$.
Both cases survive precomposition with $A$: the constant $-\infty$ composed with $A$ is again
constant.

## Main results

* `ConvexAnalysis.lowerSemicontinuous_comp`: a lower semicontinuous function composed with a
  continuous map is lower semicontinuous.
* `ConvexAnalysis.lowerSemicontinuous_compLin`: the inverse image of a lower semicontinuous function
  under a continuous linear map is lower semicontinuous.
* `ConvexAnalysis.closedConvex_compLin`: the inverse image of a closed function under a continuous
  linear map is closed.

## Implementation notes

* `ConvexAnalysis.lowerSemicontinuous_comp` composes $g$ with a continuous map on the right.
  Mathlib's `Continuous.comp_lowerSemicontinuous` composes on the left.
-/

namespace ConvexAnalysis

section Comp

variable {E G : Type*} [TopologicalSpace E] [TopologicalSpace G] {g : G → EReal}

/-- Let $E, G$ be topological spaces, let $g : G \to [-\infty, +\infty]$ be lower semicontinuous,
and let $\varphi : E \to G$ be continuous. Then $g \circ \varphi$ is lower semicontinuous. -/
theorem lowerSemicontinuous_comp (hg : LowerSemicontinuous g) {φ : E → G} (hφ : Continuous φ) :
    LowerSemicontinuous (g ∘ φ) :=
  hg.comp hφ

end Comp

section CompLin

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace G] [IsTopologicalAddGroup G]
  {A : E →ₗ[ℝ] G} {g : G → EReal}

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup G] in
/-- Let $A : E \to G$ be a continuous linear map between real vector spaces with topologies, and let
$g : G \to [-\infty, +\infty]$ be lower semicontinuous. Then the inverse image
$gA : x \mapsto g(Ax)$ is lower semicontinuous.

The inverse image is `ConvexAnalysis.compLin g A`. This is
`ConvexAnalysis.lowerSemicontinuous_comp` for $\varphi = A$. -/
theorem lowerSemicontinuous_compLin (hg : LowerSemicontinuous g) (hA : Continuous A) :
    LowerSemicontinuous (compLin g A) :=
  lowerSemicontinuous_comp hg hA

/-- Let $E, G$ be real vector spaces with topologies that make them topological additive groups. Let
$A : E \to G$ be a continuous linear map, and let $g : G \to [-\infty, +\infty]$ be closed, that
is, equal to its closure (`ConvexAnalysis.ClosedConvex`). Then the inverse image
$gA : x \mapsto g(Ax)$ is closed.

No convexity of $g$ is assumed. The proof uses `ConvexAnalysis.closedConvex_iff`: a closed
function is either the constant $-\infty$, or lower semicontinuous and never $-\infty$, and both
properties pass to $gA$. -/
theorem closedConvex_compLin (hg : ClosedConvex g)
    (hA : Continuous A) : ClosedConvex (compLin g A) := by
  rcases closedConvex_iff.1 hg with rfl | ⟨hlsc, hne⟩
  · exact closedConvex_iff.2 (Or.inl rfl)
  · exact closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_compLin hlsc hA, fun x => hne (A x)⟩)

omit [TopologicalSpace G] [IsTopologicalAddGroup G] in
/-- Let $E$ be a real vector space with a topology that makes it a topological additive group, and
let $f : E \to [-\infty, +\infty]$ be closed, proper and convex. Then the reflection
$x \mapsto f(-x)$ is closed, proper and convex. -/
theorem ClosedProperConvexFn.comp_neg {f : E → EReal} (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn fun x => f (-x) :=
  ⟨hf.convex.comp_neg, closedConvex_compLin (A := -LinearMap.id) hf.closed continuous_neg,
    hf.proper.comp_neg⟩

end CompLin

end ConvexAnalysis
