/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

For points $P, Q$ of the Euclidean plane $\mathbb{R}^2$, the segment $[P, Q]$ is the set of points
$P + s(Q - P)$ with $0 \le s \le 1$, and the open segment $(P, Q)$ is the set of these points with
$0 < s < 1$. This module proves the small facts about `segment ℝ P Q` and `openSegment ℝ P Q` that
the polygon module `Numlib.Analysis.Sobolev.Boundary.Polygon` uses: the affine parametrization is
continuous, a segment is compact and hence measurable, and an open segment is measurable because,
for $P \neq Q$, it is the segment without its two endpoints.

## Main results

* `EuclideanSpace.lineMap_eq`: $\operatorname{lineMap}(P, Q)(t) = P + t(Q - P)$.
* `EuclideanSpace.mem_segment_iff'`, `EuclideanSpace.mem_openSegment_iff'`: membership in the
  segment and in the open segment, in this form.
* `EuclideanSpace.isCompact_segment`, `EuclideanSpace.measurableSet_segment`,
  `EuclideanSpace.measurableSet_openSegment`: a segment is compact and measurable, and an open
  segment is measurable.

## Implementation notes

* Mathlib has `segment_eq_image_lineMap` and `Convex.isCompact_convexHull`, but no
  `isCompact_segment`.
-/

open Set

/-- The Euclidean plane $\mathbb{R}^2$, as a local notation. -/
local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanSpace

/-- For points $P, Q \in \mathbb{R}^2$ and $t \in \mathbb{R}$, the affine map from $P$ to $Q$ takes
at $t$ the value
$$\operatorname{lineMap}(P, Q)(t) = P + t(Q - P).$$
-/
theorem lineMap_eq (P Q : 𝔼₂) (t : ℝ) : AffineMap.lineMap P Q t = P + t • (Q - P) := by
  rw [AffineMap.lineMap_apply_module']; abel

/-- For points $P, Q \in \mathbb{R}^2$, the parametrization $t \mapsto P + t(Q - P)$ of the line
through $P$ and $Q$ is continuous. -/
theorem continuous_lineMap (P Q : 𝔼₂) : Continuous (AffineMap.lineMap P Q : ℝ → 𝔼₂) :=
  AffineMap.lineMap_continuous

/-- For points $P, Q \in \mathbb{R}^2$, the segment $[P, Q]$ is compact. -/
theorem isCompact_segment (P Q : 𝔼₂) : IsCompact (segment ℝ P Q) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image (continuous_lineMap P Q)

/-- For points $P, Q \in \mathbb{R}^2$, the segment $[P, Q]$ is a measurable set. -/
theorem measurableSet_segment (P Q : 𝔼₂) : MeasurableSet (segment ℝ P Q) :=
  (isCompact_segment P Q).isClosed.measurableSet

/-- For points $P, Q \in \mathbb{R}^2$, the open segment $(P, Q)$ is a measurable set. For
$P \neq Q$ it is the segment $[P, Q]$ without its endpoints, and for $P = Q$ it is the single
point $P$. -/
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

/-- For points $P, Q, x \in \mathbb{R}^2$, $x$ lies in the open segment $(P, Q)$ if and only if
$x = P + s(Q - P)$ for some $s$ with $0 < s < 1$. -/
theorem mem_openSegment_iff' {P Q x : 𝔼₂} :
    x ∈ openSegment ℝ P Q ↔ ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x = P + s • (Q - P) := by
  rw [openSegment_eq_image']
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs.1, hs.2, rfl⟩
  · rintro ⟨s, h1, h2, rfl⟩; exact ⟨s, ⟨h1, h2⟩, rfl⟩

/-- For points $P, Q, x \in \mathbb{R}^2$, $x$ lies in the segment $[P, Q]$ if and only if
$x = P + s(Q - P)$ for some $s$ with $0 \le s \le 1$. -/
theorem mem_segment_iff' {P Q x : 𝔼₂} :
    x ∈ segment ℝ P Q ↔ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = P + s • (Q - P) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs.1, hs.2, rfl⟩
  · rintro ⟨s, h1, h2, rfl⟩; exact ⟨s, ⟨h1, h2⟩, rfl⟩

end EuclideanSpace
