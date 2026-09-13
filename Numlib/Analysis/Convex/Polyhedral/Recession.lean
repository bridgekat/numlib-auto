import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Recession.Closedness

/-!
# The recession cone of a polyhedral set, read off its generators

The recession cone of a nonempty finitely generated convex set `conv P + cone D` is `cone D`
itself — the *generator* side of the description `Polyhedral/Ops.lean` proves on the inequality
side. The consequence, `Polyhedral.recessionCone_image`, is that a linear map commutes with `0⁺`
on polyhedral sets with no hypothesis on the map. The general recession calculus cannot supply
that: it computes `0⁺(A '' C)` only when `A` kills no direction of recession of `C`.

## References

* [rockafellar1970convex] §19.
-/

open Set Pointwise

namespace ConvexAnalysis

section Generators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The recession cone of a nonempty finitely generated convex set `conv P + cone D` is `cone D`
itself. The inclusion `⊇` needs nothing; `⊆` is the recession cone of a sum, whose hypothesis is
vacuous because `conv P` is compact. -/
theorem recessionCone_of_finitelyGenerated {C : Set E} {P D : Finset E}
    (hPD : C = convexHull ℝ (P : Set E) + (PointedCone.hull ℝ (D : Set E) : Set E))
    (hne : C.Nonempty) :
    recessionCone C = (PointedCone.hull ℝ (D : Set E) : Set E) := by
  obtain ⟨x, hx⟩ := hne
  rw [hPD] at hx
  obtain ⟨u, hu, v, -, -⟩ := hx
  have hPne : (convexHull ℝ (P : Set E)).Nonempty := ⟨u, hu⟩
  have hDne : ((PointedCone.hull ℝ (D : Set E) : Set E)).Nonempty :=
    ⟨0, (PointedCone.hull ℝ (D : Set E)).zero_mem⟩
  have hPcomp : IsCompact (convexHull ℝ (P : Set E)) :=
    P.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hPrec : recessionCone (convexHull ℝ (P : Set E)) = {0} :=
    (isCompact_iff_recessionCone_eq_zero (convex_convexHull ℝ _) hPcomp.isClosed hPne).1 hPcomp
  have hDcl : IsClosed ((PointedCone.hull ℝ (D : Set E) : Set E)) :=
    FinitelyGeneratedCone.isClosed ⟨D, rfl⟩
  have hDconv : Convex ℝ ((PointedCone.hull ℝ (D : Set E) : Set E)) :=
    ((PointedCone.hull ℝ (D : Set E) : ConvexCone ℝ E)).convex
  rw [hPD, Convex.recessionCone_add_of_neg_notMem_recessionCone (convex_convexHull ℝ _)
      hPcomp.isClosed hPne hDconv hDcl hDne
      (fun z hz _ => by rw [hPrec] at hz; exact hz),
    hPrec, recessionCone_coe_pointedCone]
  ext y
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simpa using hb
  · exact fun hy => ⟨0, rfl, y, hy, zero_add y⟩

/-- **A linear map commutes with `0⁺` on polyhedral sets**: `0⁺(A '' C) = A '' 0⁺C`, with no
hypothesis whatever on `A`. For a general closed convex `C` this fails — the image need not even
be closed — and the general criterion repairs it only under `0⁺C ∩ ker A = {0}`. -/
theorem Polyhedral.recessionCone_image {C : Set E} (hC : Polyhedral C) (hne : C.Nonempty)
    (A : E →ₗ[ℝ] F) : recessionCone (A '' C) = A '' recessionCone C := by
  classical
  obtain ⟨P, D, hPD⟩ := hC.finitelyGenerated
  have himg : A '' C = convexHull ℝ ((P.image A : Finset F) : Set F)
      + (PointedCone.hull ℝ ((D.image A : Finset F) : Set F) : Set F) := by
    rw [hPD, Set.image_add A, LinearMap.image_convexHull, image_coe_hull, Finset.coe_image,
      Finset.coe_image]
  rw [recessionCone_of_finitelyGenerated himg (hne.image A),
    recessionCone_of_finitelyGenerated hPD hne, Finset.coe_image, ← image_coe_hull]

end Generators

end ConvexAnalysis
