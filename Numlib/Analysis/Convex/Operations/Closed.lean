import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Operations.Image

/-!
# Closedness of the functional operations

The inverse image of a closed function under a continuous linear map is closed — the closedness
counterpart of `convexFn_compLin`, which is the convexity statement. The supporting
`lowerSemicontinuous_comp` precomposes a lower semicontinuous `g` with a continuous `φ`; Mathlib's
`Continuous.comp_lowerSemicontinuous` composes on the other side.

Closedness is not lower semicontinuity — `ClosedConvex` also admits the constant `⊥` — and that
branch survives precomposition because `(fun _ => ⊥) ∘ A` is again constant.

## References

* [rockafellar1970convex] §5, §7.
-/

namespace ConvexAnalysis

section Comp

variable {E G : Type*} [TopologicalSpace E] [TopologicalSpace G] {g : G → EReal}

/-- Lower semicontinuity is preserved by precomposition with a continuous map. -/
theorem lowerSemicontinuous_comp (hg : LowerSemicontinuous g) {φ : E → G} (hφ : Continuous φ) :
    LowerSemicontinuous (g ∘ φ) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  exact (hg.isOpen_preimage y).preimage hφ

end Comp

section CompLin

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace G] [IsTopologicalAddGroup G]
  {A : E →ₗ[ℝ] G} {g : G → EReal}

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup G] in
theorem lowerSemicontinuous_compLin (hg : LowerSemicontinuous g) (hA : Continuous A) :
    LowerSemicontinuous (compLin g A) :=
  lowerSemicontinuous_comp hg hA

/-- The inverse image of a closed function under a continuous linear map is closed. -/
theorem closedConvex_compLin (hg : ClosedConvex g)
    (hA : Continuous A) : ClosedConvex (compLin g A) := by
  rcases closedConvex_iff.1 hg with rfl | ⟨hlsc, hne⟩
  · exact closedConvex_iff.2 (Or.inl rfl)
  · exact closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_compLin hlsc hA, fun x => hne (A x)⟩)

omit [TopologicalSpace G] [IsTopologicalAddGroup G] in
/-- The reflection `x ↦ f (-x)` of a closed proper convex function is closed proper convex. -/
theorem ClosedProperConvexFn.comp_neg {f : E → EReal} (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn fun x => f (-x) :=
  ⟨hf.convex.comp_neg, closedConvex_compLin (A := -LinearMap.id) hf.closed continuous_neg,
    hf.proper.comp_neg⟩

end CompLin

end ConvexAnalysis
