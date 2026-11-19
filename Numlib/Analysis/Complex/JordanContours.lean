/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Complex.ContourIntegral
import Numlib.ThirdParty.Jordan

/-!
# Rectifiable Jordan contours

The analytic winding index agrees with continuous-angle winding on closed
Lipschitz paths. Jordan separation then determines the index from the
geometric interior and orientation. For a finite boundary, clockwise
hole contours cancel their outer contours on the corresponding holes.
-/

noncomputable section

open Set Function
open scoped unitInterval

attribute [local instance] Classical.propDecidable

namespace Path

/-- A rectifiable Jordan contour is a closed path with no repetitions after
omitting the terminal parameter, and with finite variation. -/
structure IsRectifiableJordan {a : ℂ} (γ : Path a a) : Prop where
  injectiveOn : Set.InjOn γ.extend (Ico 0 1)
  boundedVariationOn : BoundedVariationOn γ.extend unitInterval

/-- The geometric Jordan interior is the bounded component of the trace complement. -/
def jordanInterior {a : ℂ} (γ : Path a a) : Set ℂ :=
  {w | w ∉ range γ ∧ Bornology.IsBounded (connectedComponentIn (range γ)ᶜ w)}

/-- Continuous-angle winding, independent of the contour integral and defined
also for parametrizations which are not absolutely continuous. -/
def topologicalWinding {a : ℂ} (γ : Path a a) (w : ℂ) : ℝ :=
  MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1)
    (fun t : I => Isoperimetric.planeComplex.symm (γ t)) (Isoperimetric.planeComplex.symm w)

/-- Standard orientation of a Jordan contour, detected by the continuous
argument of the direction from one point in the bounded component.
The signs indicate counterclockwise and clockwise orientation, respectively. -/
def HasJordanOrientation {a : ℂ} (γ : Path a a) (ccw : Bool) : Prop :=
  ∃ w ∈ γ.jordanInterior, γ.topologicalWinding w = if ccw then 1 else -1

private abbrev planeToEuclidean := Isoperimetric.planeComplex.symm

private theorem range_extend_apply_plane {a : ℂ} (γ : Path a a) :
    Isoperimetric.trace (fun t => planeToEuclidean (γ.extend t)) =
      range (fun t : I => planeToEuclidean (γ t)) := by
  ext w
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨⟨t, ht⟩, by simpa only [Path.extend_apply γ ht] using h⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, congrArg planeToEuclidean (Path.extend_apply γ t.property)⟩

private theorem rectifiableJordan_plane {a : ℂ} {γ : Path a a} (h : γ.IsRectifiableJordan) :
    Isoperimetric.RectifiableJordan (fun t => planeToEuclidean (γ.extend t)) where
  continuousOn := (planeToEuclidean.continuous.comp γ.continuous_extend).continuousOn
  closed := congrArg planeToEuclidean (γ.extend_zero.trans γ.extend_one.symm)
  injectiveOn := fun _ hu _ hv hxy => h.injectiveOn hu hv (planeToEuclidean.injective hxy)
  boundedVariationOn := planeToEuclidean.lipschitzWith.comp_boundedVariationOn h.boundedVariationOn

private theorem mem_jordanInterior_plane_iff {a w : ℂ} (γ : Path a a) :
    planeToEuclidean w ∈ MovingSofa.jordanInterior
      (Isoperimetric.trace (fun t => planeToEuclidean (γ.extend t))) ↔ w ∈ γ.jordanInterior := by
  have hrange : range (fun t : I => planeToEuclidean (γ t)) = planeToEuclidean '' range γ :=
    range_comp planeToEuclidean γ
  have hcompl : planeToEuclidean '' (range γ)ᶜ = (planeToEuclidean '' range γ)ᶜ := by
    ext v
    simp only [mem_compl_iff, mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩ ⟨z, hz, he⟩
      exact hu (planeToEuclidean.injective he ▸ hz)
    · intro hv
      refine ⟨planeToEuclidean.symm v, ?_, planeToEuclidean.apply_symm_apply v⟩
      exact fun h => hv ⟨_, h, planeToEuclidean.apply_symm_apply v⟩
  have htrace : planeToEuclidean w ∉ planeToEuclidean '' range γ ↔ w ∉ range γ := by
    simp only [mem_image, planeToEuclidean.injective.eq_iff, exists_eq_right]
  rw [range_extend_apply_plane, hrange]
  change (planeToEuclidean w ∉ planeToEuclidean '' range γ ∧
    Bornology.IsBounded
      (connectedComponentIn (planeToEuclidean '' range γ)ᶜ (planeToEuclidean w))) ↔
    (w ∉ range γ ∧ Bornology.IsBounded (connectedComponentIn (range γ)ᶜ w))
  rw [htrace]
  apply and_congr_right
  intro hw
  have himage := planeToEuclidean.toHomeomorph.image_connectedComponentIn
    (show w ∈ (range γ)ᶜ from hw)
  change planeToEuclidean '' connectedComponentIn (range γ)ᶜ w =
    connectedComponentIn (planeToEuclidean '' (range γ)ᶜ) (planeToEuclidean w) at himage
  rw [hcompl] at himage
  rw [← himage]
  constructor
  · intro hb
    simpa only [image_image, Function.comp_def, planeToEuclidean.symm_apply_apply, image_id'] using
      planeToEuclidean.symm.lipschitzWith.isBounded_image hb
  · exact planeToEuclidean.lipschitzWith.isBounded_image

private theorem exists_topologicalAngleLift_of_avoids {a w : ℂ} {γ : Path a a}
    (hw : w ∉ range γ) : ∃ θ : I → ℝ,
      MovingSofa.IsCurveAngleLift (fun t : I => planeToEuclidean (γ t)) (planeToEuclidean w) θ := by
  apply MovingSofa.exists_curveAngleLift_of_avoids (by norm_num)
    (planeToEuclidean.continuous.comp γ.continuous)
  rintro ⟨t, ht⟩
  exact hw ⟨t, planeToEuclidean.injective ht⟩

/-- The analytic contour index agrees with continuous-angle winding on a
Lipschitz representative. -/
theorem complexPathIndex_eq_topologicalWinding {a w : ℂ} {γ : Path a a}
    (hγ : γ.IsLipschitz) (hw : w ∉ range γ) :
    complexPathIndex γ w = (γ.topologicalWinding w : ℂ) := by
  obtain ⟨θ, hθc, hθ, hIndex⟩ := exists_complexPathIndex_argumentLift hγ hw
  have hlift : MovingSofa.IsCurveAngleLift
      (fun t : I => planeToEuclidean (γ t)) (planeToEuclidean w) θ := by
    refine ⟨hθc, fun t => ?_⟩
    have hDiff :
        Isoperimetric.planeComplex (planeToEuclidean (γ t) - planeToEuclidean w) = γ t - w := by
      simp only [map_sub, LinearIsometryEquiv.apply_symm_apply]
    have hNorm : ‖planeToEuclidean (γ t) - planeToEuclidean w‖ = ‖γ t - w‖ := by
      rw [← map_sub, LinearIsometryEquiv.norm_map]
    rw [← Isoperimetric.planeComplex_re, ← Isoperimetric.planeComplex_im, hDiff, hNorm]
    exact hθ t
  rw [topologicalWinding, hlift.curveWinding_eq (by norm_num), hIndex]
  rfl

/-- Continuous-angle winding is unchanged along an increasing time change. -/
theorem LipschitzReparametrization.topologicalWinding_eq {a w : ℂ} {γ : Path a a}
    (η : γ.LipschitzReparametrization) (hw : w ∉ range γ) :
    η.path.topologicalWinding w = γ.topologicalWinding w := by
  have hE : (fun t : I => planeToEuclidean (γ t)) =
      (fun t : I => planeToEuclidean (η.path t)) ∘ η.orderIso := by
    funext t
    rw [Function.comp_apply, η.apply_orderIso]
  rw [topologicalWinding, topologicalWinding, hE]
  have h0 : η.orderIso (0 : I) = 0 := η.orderIso.map_bot
  have h1 : η.orderIso (1 : I) = 1 := η.orderIso.map_top
  rw [MovingSofa.curveWinding_comp_of_endpoints (by norm_num) (by norm_num)
    (exists_topologicalAngleLift_of_avoids (η.range_eq.symm ▸ hw))
    η.orderIso.continuous h0 h1]

/-- Geometric rectifiability and simplicity imply a uniform winding sign on
the interior. The sign agrees with continuous-angle orientation. -/
theorem IsRectifiableJordan.exists_uniform_topologicalWinding {a : ℂ} {γ : Path a a}
    (h : γ.IsRectifiableJordan) :
    ∃ b : Bool, γ.HasJordanOrientation b ∧
      ∀ w ∈ γ.jordanInterior, γ.topologicalWinding w = if b then 1 else -1 := by
  let hplane := rectifiableJordan_plane h
  obtain ⟨b, _, _, _, _, _, _, hSign⟩ := hplane.exists_orientation
  have hMap : hplane.intervalMap = fun t : I => planeToEuclidean (γ t) := by
    funext t
    exact congrArg planeToEuclidean (Path.extend_apply γ t.property)
  have hW (w : ℂ) (hw : w ∈ γ.jordanInterior) :
      γ.topologicalWinding w = if b then 1 else -1 := by
    rw [topologicalWinding, ← hMap]
    exact hSign (planeToEuclidean w) ((mem_jordanInterior_plane_iff γ).mpr hw)
  obtain ⟨v, hv⟩ := hplane.isConnected_enclosed.nonempty
  let w := planeToEuclidean.symm v
  have hw : w ∈ γ.jordanInterior := (mem_jordanInterior_plane_iff γ).mp
    ((planeToEuclidean.apply_symm_apply v).symm ▸ hv)
  exact ⟨b, ⟨w, hw, hW w hw⟩, hW⟩

/-- The continuous-angle orientation determines the analytic index on any
Lipschitz representative of a rectifiable Jordan contour. -/
theorem IsRectifiableJordan.complexPathIndex_eq_of_orientation {a w : ℂ} {γ : Path a a}
    (h : γ.IsRectifiableJordan) (η : γ.LipschitzReparametrization)
    {b : Bool} (hb : γ.HasJordanOrientation b) (hw : w ∉ range γ) :
    complexPathIndex η.path w =
      if w ∈ γ.jordanInterior then (if b then (1 : ℂ) else -1) else 0 := by
  classical
  by_cases hi : w ∈ γ.jordanInterior
  · obtain ⟨c, _, hC⟩ := h.exists_uniform_topologicalWinding
    obtain ⟨u, hu, hU⟩ := hb
    have hsign : (if c then (1 : ℝ) else -1) = if b then 1 else -1 :=
      (hC u hu).symm.trans hU
    rw [ite_eq_left hi, complexPathIndex_eq_topologicalWinding η.isLipschitz (η.range_eq.symm ▸ hw),
      η.topologicalWinding_eq hw, hC w hi, hsign]
    cases b <;> norm_num
  · rw [ite_eq_right hi]
    apply complexPathIndex_eq_zero_of_unbounded_connectedComponentIn η.isLipschitz
      (η.range_eq.symm ▸ hw)
    rw [η.range_eq]
    exact fun hBound => hi ⟨hw, hBound⟩

end Path

section JordanDomains

variable {outer hole : Type*} [Fintype outer] [Fintype hole] {p : outer ⊕ hole → ℂ}

/-- A geometric region specified by one outer contour, with the interiors
and traces of its assigned holes removed. -/
def jordanRegionPiece (γ : (i : outer ⊕ hole) → Path (p i) (p i))
    (owner : hole → outer) (i : outer) : Set ℂ :=
  {w | w ∈ (γ (.inl i)).jordanInterior ∧
    ∀ j, owner j = i → w ∉ (γ (.inr j)).jordanInterior ∪ range (γ (.inr j))}

/-- The geometric Jordan enclosure is the union of its region pieces, with
the boundary traces omitted. Nested islands can be separate region pieces. -/
def jordanBoundaryEnclosure (γ : (i : outer ⊕ hole) → Path (p i) (p i))
    (owner : hole → outer) : Set ℂ :=
  (⋃ i, jordanRegionPiece γ owner i) \ ⋃ i, range (γ i)

/-- The geometric conditions for customary orientation of a finite
rectifiable Jordan boundary. Outer boundaries are counterclockwise, holes
are clockwise, and each hole belongs to a specified outer boundary. -/
structure IsCustomaryJordanBoundary (γ : (i : outer ⊕ hole) → Path (p i) (p i))
    (owner : hole → outer) : Prop where
  rectifiableJordan : ∀ i, (γ i).IsRectifiableJordan
  outer_counterclockwise : ∀ i, (γ (.inl i)).HasJordanOrientation true
  hole_clockwise : ∀ j, (γ (.inr j)).HasJordanOrientation false
  hole_inside : ∀ j, (γ (.inr j)).jordanInterior ⊆ (γ (.inl (owner j))).jordanInterior
  holes_disjoint : ∀ ⦃j k⦄, j ≠ k → owner j = owner k →
    Disjoint (γ (.inr j)).jordanInterior (γ (.inr k)).jordanInterior
  regions_disjoint : Pairwise (Disjoint on jordanRegionPiece γ owner)

omit [Fintype outer] in
/-- The locally positive contribution of one outer contour is cancelled
exactly in the interiors of its clockwise holes. -/
private theorem regional_signed_sum {γ : (i : outer ⊕ hole) → Path (p i) (p i)}
    {owner : hole → outer} (h : IsCustomaryJordanBoundary γ owner)
    {w : ℂ} (hw : ∀ i, w ∉ range (γ i)) (i : outer) :
    (if w ∈ (γ (.inl i)).jordanInterior then (1 : ℂ) else 0) -
      (∑ j : hole, if owner j = i ∧ w ∈ (γ (.inr j)).jordanInterior then (1 : ℂ) else 0) =
      if w ∈ jordanRegionPiece γ owner i then (1 : ℂ) else 0 := by
  classical
  by_cases hH : ∃ j, owner j = i ∧ w ∈ (γ (.inr j)).jordanInterior
  · obtain ⟨j, hj, hW⟩ := hH
    have hO : w ∈ (γ (.inl i)).jordanInterior := hj ▸ h.hole_inside j hW
    have hR : w ∉ jordanRegionPiece γ owner i := fun hR => hR.2 j hj (Or.inl hW)
    have hsum : (∑ k : hole, if owner k = i ∧ w ∈ (γ (.inr k)).jordanInterior then
        (1 : ℂ) else 0) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp [hj, hW]
      · intro k _ hkj
        apply ite_eq_right
        rintro ⟨hk, hwk⟩
        exact Set.disjoint_left.mp (h.holes_disjoint hkj (hk.trans hj.symm)) hwk hW
      · simp
    simp [hO, hR, hsum]
  · have hsum : (∑ j : hole, if owner j = i ∧ w ∈ (γ (.inr j)).jordanInterior then
        (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      exact fun j _ => ite_eq_right (fun hj => hH ⟨j, hj⟩)
    have he : w ∈ jordanRegionPiece γ owner i ↔ w ∈ (γ (.inl i)).jordanInterior := by
      refine ⟨fun h => h.1, fun ho => ⟨ho, ?_⟩⟩
      intro j hj hw'
      exact hw'.elim (fun hm => hH ⟨j, hj, hm⟩) (hw (.inr j))
    rw [he, hsum, sub_zero]

/-- A customarily oriented finite Jordan boundary winds once about the
geometric enclosure and zero times about every other point off its traces. -/
theorem IsCustomaryJordanBoundary.totalIndex_eq {γ : (i : outer ⊕ hole) → Path (p i) (p i)}
    {owner : hole → outer} (h : IsCustomaryJordanBoundary γ owner)
    (η : ∀ i, (γ i).LipschitzReparametrization) {w : ℂ} (hw : ∀ i, w ∉ range (γ i)) :
    complexTotalPathIndex (fun i => (η i).path) w =
      if w ∈ jordanBoundaryEnclosure γ owner then (1 : ℂ) else 0 := by
  classical
  have hp (i : outer) : complexPathIndex (η (.inl i)).path w =
      if w ∈ (γ (.inl i)).jordanInterior then (1 : ℂ) else 0 := by
    simpa only [ite_true] using (h.rectifiableJordan (.inl i)).complexPathIndex_eq_of_orientation
      (η (.inl i)) (h.outer_counterclockwise i) (hw (.inl i))
  have hm (j : hole) : complexPathIndex (η (.inr j)).path w =
      -(if w ∈ (γ (.inr j)).jordanInterior then (1 : ℂ) else 0) := by
    rw [(h.rectifiableJordan (.inr j)).complexPathIndex_eq_of_orientation
      (η (.inr j)) (h.hole_clockwise j) (hw (.inr j))]
    split <;> simp
  have hgroup :
      (∑ i : outer, ∑ j : hole, if owner j = i ∧ w ∈ (γ (.inr j)).jordanInterior
        then (1 : ℂ) else 0) =
      ∑ j : hole, if w ∈ (γ (.inr j)).jordanInterior then (1 : ℂ) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : w ∈ (γ (.inr j)).jordanInterior
    · simp [hj]
    · simp [hj]
  rw [complexTotalPathIndex, Fintype.sum_sum_type]
  simp_rw [hp, hm]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← hgroup, ← Finset.sum_sub_distrib]
  simp_rw [regional_signed_sum h hw]
  have htraces : w ∉ ⋃ i, range (γ i) := fun hW => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hW
    exact hw i hi
  by_cases hR : w ∈ ⋃ i, jordanRegionPiece γ owner i
  · have hE : w ∈ jordanBoundaryEnclosure γ owner := ⟨hR, htraces⟩
    rw [ite_eq_left hE]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hR
    rw [Finset.sum_eq_single i]
    · exact ite_eq_left hi
    · intro j _ hji
      apply ite_eq_right
      exact fun hj => Set.disjoint_left.mp (h.regions_disjoint hji) hj hi
    · simp
  · have hnot : w ∉ jordanBoundaryEnclosure γ owner := fun hW => hR hW.1
    rw [ite_eq_right hnot]
    apply Finset.sum_eq_zero
    exact fun i _ => ite_eq_right fun hi => hR (mem_iUnion.mpr ⟨i, hi⟩)

/-- The analytic and geometric enclosures of a customarily oriented
rectifiable Jordan boundary are equal. -/
theorem IsCustomaryJordanBoundary.indexEnclosure_eq
    {γ : (i : outer ⊕ hole) → Path (p i) (p i)}
    {owner : hole → outer} (h : IsCustomaryJordanBoundary γ owner)
    (η : ∀ i, (γ i).LipschitzReparametrization) :
    complexCycleEnclosure (fun i => (η i).path) = jordanBoundaryEnclosure γ owner := by
  ext w
  have hAvoid : (∀ i, w ∉ range (η i).path) ↔ ∀ i, w ∉ range (γ i) := by
    simp_rw [Path.LipschitzReparametrization.range_eq]
  constructor
  · rintro ⟨hw, hIndex⟩
    rw [h.totalIndex_eq η (hAvoid.mp hw)] at hIndex
    split at hIndex
    · assumption
    · exact (zero_ne_one hIndex).elim
  · intro hw
    have hn (i : outer ⊕ hole) : w ∉ range (γ i) :=
      fun hi => hw.2 (mem_iUnion.mpr ⟨i, hi⟩)
    refine ⟨hAvoid.mpr hn, ?_⟩
    exact (h.totalIndex_eq η hn).trans (ite_eq_left hw)

/-- Customary geometric orientation implies positive winding orientation. -/
theorem IsCustomaryJordanBoundary.hasPositiveCycleIndex
    {γ : (i : outer ⊕ hole) → Path (p i) (p i)}
    {owner : hole → outer} (h : IsCustomaryJordanBoundary γ owner)
    (η : ∀ i, (γ i).LipschitzReparametrization) :
    HasPositiveCycleIndex (fun i => (η i).path) := by
  classical
  intro w hw
  have hn (i : outer ⊕ hole) : w ∉ range (γ i) := (η i).range_eq ▸ hw i
  rw [h.totalIndex_eq η hn]
  split <;> simp

end JordanDomains
