/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convex.Segment`, beside `segment_eq_image_lineMap`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Affine

/-!
# Segments of the plane: topology, measurability, and the affine parametrization

Small facts about `segment ℝ P Q` and `openSegment ℝ P Q` in the Euclidean plane that the
polygon modules of `Numlib/Analysis/Sobolev/Boundary/` use:

* `EuclideanSpace.lineMap_eq`: `AffineMap.lineMap P Q t = P + t (Q − P)`;
* `EuclideanSpace.mem_segment_iff'`, `EuclideanSpace.mem_openSegment_iff'`: membership in that
  form;
* `EuclideanSpace.isCompact_segment`, `EuclideanSpace.measurableSet_segment`,
  `EuclideanSpace.measurableSet_openSegment`: a segment is compact, hence measurable; an open
  segment is a segment minus its two endpoints.

Mathlib has `segment_eq_image_lineMap` and `Convex.isCompact_convexHull`, but no
`isCompact_segment`.
-/

open Set

/-- The plane, locally. -/
local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanSpace

/-- `lineMap P Q t = P + t (Q − P)`. -/
theorem lineMap_eq (P Q : 𝔼₂) (t : ℝ) : AffineMap.lineMap P Q t = P + t • (Q - P) := by
  rw [AffineMap.lineMap_apply_module']; abel

/-- The parametrization of a segment is continuous. -/
theorem continuous_lineMap (P Q : 𝔼₂) : Continuous (AffineMap.lineMap P Q : ℝ → 𝔼₂) :=
  AffineMap.lineMap_continuous

/-- A segment of the plane is compact. -/
theorem isCompact_segment (P Q : 𝔼₂) : IsCompact (segment ℝ P Q) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image (continuous_lineMap P Q)

/-- A segment of the plane is measurable. -/
theorem measurableSet_segment (P Q : 𝔼₂) : MeasurableSet (segment ℝ P Q) :=
  (isCompact_segment P Q).isClosed.measurableSet

/-- An open segment of the plane is measurable: it is the segment minus its endpoints. -/
theorem measurableSet_openSegment (P Q : 𝔼₂) : MeasurableSet (openSegment ℝ P Q) := by
  by_cases hPQ : P = Q
  · subst hPQ
    rw [openSegment_same]
    exact measurableSet_singleton P
  · have : openSegment ℝ P Q = segment ℝ P Q \ {P, Q} := by
      ext x
      simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro hx
        refine ⟨openSegment_subset_segment ℝ _ _ hx, ?_, ?_⟩
        · rintro rfl
          exact hPQ (left_mem_openSegment_iff.1 hx)
        · rintro rfl
          exact hPQ (right_mem_openSegment_iff.1 hx)
      · rintro ⟨hx, hxP, hxQ⟩
        rw [← insert_endpoints_openSegment] at hx
        rcases hx with rfl | rfl | hx
        · exact absurd rfl hxP
        · exact absurd rfl hxQ
        · exact hx
    rw [this]
    exact (measurableSet_segment P Q).diff (by simp)

/-- Membership of the open segment, as `x = P + s (Q − P)` with `0 < s < 1`. -/
theorem mem_openSegment_iff' {P Q x : 𝔼₂} :
    x ∈ openSegment ℝ P Q ↔ ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x = P + s • (Q - P) := by
  rw [openSegment_eq_image']
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs.1, hs.2, rfl⟩
  · rintro ⟨s, h1, h2, rfl⟩; exact ⟨s, ⟨h1, h2⟩, rfl⟩

/-- Membership of the segment, as `x = P + s (Q − P)` with `0 ≤ s ≤ 1`. -/
theorem mem_segment_iff' {P Q x : 𝔼₂} :
    x ∈ segment ℝ P Q ↔ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = P + s • (Q - P) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs.1, hs.2, rfl⟩
  · rintro ⟨s, h1, h2, rfl⟩; exact ⟨s, ⟨h1, h2⟩, rfl⟩

end EuclideanSpace
