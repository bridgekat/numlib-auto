import Numlib.Analysis.Sobolev.Boundary.Data
import Numlib.Geometry.Triangulation

/-!
# The boundary of a plane polygon through its triangles

The polygonal instance of the boundary interface `BoundaryData` of
`Numlib/Analysis/Sobolev/Boundary/Data.lean` (decision B6 of `notes/boundary/planning-brief.md`):
the **arclength measure** of a segment (`EuclideanSpace.edgeMeasure`, one-dimensional Lebesgue
measure transported to the segment by `AffineMap.lineMap` and scaled by the length), the
**outward edge normal** of a triangle (`EuclideanSpace.edgeNormal`, the unit normal of the edge
pointing away from the third vertex), the **divergence theorem on a triangle** — first on the
reference triangle `{x, y > 0, x + y < 1}` by Fubini and the one-dimensional fundamental theorem
of calculus in each coordinate (`EuclideanSpace.integral_div_referenceTriangle`), then on every
nondegenerate triangle by the affine transport of `Numlib/Analysis/Sobolev/Simplex.lean` and the
linear Piola identity `EuclideanSpace.div_comp_continuousLinearEquiv`
(`EuclideanSpace.integral_div_openTriangle`) — and, for a triangulation `𝒯 : Triangulation Ω` of
`Numlib/Geometry/Triangulation.lean`, the **divergence theorem on a triangulated domain**
(`Triangulation.integral_div_eq`): the sum of the triangles' theorems, in which the terms of the
interior edges cancel in pairs because a shared edge is the same segment with opposite normals
(`Triangulation.partner_unique`, `Finset.sum_involution`), and the terms of the boundary edges are
the boundary integral against the surface measure `Triangulation.boundaryMeasure` and the outward
normal `Triangulation.outwardNormal`. Hence `Triangulation.boundaryData : BoundaryData Ω` for
*every* triangulation: no polygonal-domain hypothesis is needed for the divergence theorem, a slit
along an interior edge being invisible to a field continuous across it.

The regularity of the field is that of `BoundaryData`: `F ∈ C¹(Ω̄)`, i.e.
`ContinuousOn F (closure Ω)` and `ContDiffOnClosure ℝ 1 F Ω` (the fundamental theorem of calculus
needs continuity on the closed slice and the derivative on the open one, and the derivative is
bounded because it extends continuously to the compact closure).

## Main definitions

* `EuclideanSpace.perp v = !₂[v 1, -v 0]`, the clockwise rotation by a right angle, with the
  transformation rule `inner_perp_map : ⟪perp (M v), M w⟫ = det M * ⟪perp v, w⟫`;
* `EuclideanSpace.edgeMeasure P Q`, the arclength measure of `[P, Q]`;
* `EuclideanSpace.edgeNormal P Q R`, the unit normal of `[P, Q]` pointing away from `R`;
* `EuclideanSpace.triangleBoundaryMeasure A B C`, `EuclideanSpace.triangleNormal A B C`, the
  boundary data of a triangle, packaged as `EuclideanSpace.triangleBoundaryData`;
* `Triangulation.IsBoundaryEdge`, `Triangulation.IsPartner`, `Triangulation.boundaryEdges`: the
  edges of the elements that no other element has, and the partner of a shared edge;
* `Triangulation.boundaryMeasure`, `Triangulation.outwardNormal`, `Triangulation.boundaryData`;
* `Triangulation.InteriorEdgesSubset`, the no-slit hypothesis the *trace* theory on a polygon needs.

## Main statements

* `EuclideanSpace.integral_div_referenceTriangle`,
  `EuclideanSpace.integral_div_referenceTriangle_eq_integral_inner`: the divergence theorem on the
  reference triangle, in parametrized and in measure form;
* `EuclideanSpace.integral_div_openTriangle`: the divergence theorem on a triangle;
* `Triangulation.segment_subset_frontier_of_isBoundaryEdge`: a boundary edge lies in `∂Ω`, from the
  four axioms of `Triangulation` alone;
* `Triangulation.partner_unique`: the partner of an interior edge is unique and lies on the other
  side of it (two triangles on the same side of a common edge overlap);
* `Triangulation.integral_div_eq`: the divergence theorem on a triangulated domain.

## Implementation notes

The edge `a : Fin 3` of an element `T` is the segment from `T.1 a` to `T.1 (a + 1)` (the indexing
of `Triangulation.skeleton_subset_iUnion_segment`), its third vertex is `T.1 (a + 2)`, and the
element is `openTriangle (T.1 a) (T.1 (a + 1)) (T.1 (a + 2))` whatever `a`
(`Triangulation.K_eq_rot`): every statement about "the edge `a` of `T`" is proved for the first
edge `[P, Q]` of a triangle `P Q R` and rotated. The sign of `edgeNormal` is fixed by
`⟪edgeNormal P Q R, R - P⟫ < 0`, a condition transported by `inner_perp_map`, which is how the
non-isometric affine change of variables of `integral_div_openTriangle` combines `|det M|`, the
edge lengths and the normals into exactly the target edge terms
(`integral_inner_edgeNormal_affine`).

What "polygonal domain" must mean for the trace is recorded as `Triangulation.InteriorEdgesSubset`:
the existing `Triangulation.FrontierSubsetEdges` does not exclude a slit along a full interior edge,
and neither hypothesis implies the other (see the doc comment of `InteriorEdgesSubset`).

## References

[han2009theoretical] §10.2 (triangulations), §7.6 (Green's formulas); Grisvard, *Elliptic Problems
in Nonsmooth Domains*, §1.5.2 (polygons); `notes/boundary/planning-brief.md` B6 and
`notes/boundary/plan-report.md` E5.
-/

open Filter MeasureTheory Set Function TopologicalSpace
open scoped InnerProductSpace

noncomputable section

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanSpace

/-! ### The rotation by a right angle -/

/-- **The clockwise rotation of `v` by a right angle**, `perp v = (v₁, −v₀)`: the normal direction
of a segment with direction `v`. -/
def perp (v : 𝔼₂) : 𝔼₂ := !₂[v 1, -v 0]

@[simp] theorem perp_apply_zero (v : 𝔼₂) : perp v 0 = v 1 := rfl

@[simp] theorem perp_apply_one (v : 𝔼₂) : perp v 1 = -v 0 := rfl

/-- `⟪perp v, w⟫ = v₁ w₀ − v₀ w₁`, the negative of the determinant of `[v, w]`. -/
theorem inner_perp_eq (v w : 𝔼₂) : ⟪perp v, w⟫_ℝ = v 1 * w 0 - v 0 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, perp]
  ring

/-- `perp v` is orthogonal to `v`. -/
theorem inner_perp_self (v : 𝔼₂) : ⟪perp v, v⟫_ℝ = 0 := by
  rw [inner_perp_eq]; ring

/-- `perp` is an isometry. -/
theorem norm_perp (v : 𝔼₂) : ‖perp v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, perp, add_comm]

@[simp] theorem perp_neg (v : 𝔼₂) : perp (-v) = -perp v := by
  ext i; fin_cases i <;> simp [perp]

theorem perp_sub (v w : 𝔼₂) : perp (v - w) = perp v - perp w := by
  ext i; fin_cases i
  · simp [perp]
  · simp [perp]; ring

@[simp] theorem perp_smul (c : ℝ) (v : 𝔼₂) : perp (c • v) = c • perp v := by
  ext i; fin_cases i <;> simp [perp]

/-- A vector of the plane is the combination of the standard basis with its coordinates. -/
theorem eq_smul_single_add_smul_single (v : 𝔼₂) :
    v = v 0 • EuclideanSpace.single 0 1 + v 1 • EuclideanSpace.single 1 1 := by
  ext i; fin_cases i <;> simp

/-- **The transformation rule of `perp`**: `⟪perp (M v), M w⟫ = det M * ⟪perp v, w⟫` for a linear
map `M` of the plane (`det` of the `2 × 2` matrix of `M` in the standard basis). -/
theorem inner_perp_map (M : 𝔼₂ →L[ℝ] 𝔼₂) (v w : 𝔼₂) :
    ⟪perp (M v), M w⟫_ℝ = LinearMap.det (M : 𝔼₂ →ₗ[ℝ] 𝔼₂) * ⟪perp v, w⟫_ℝ := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  have hv : M v = v 0 • M (EuclideanSpace.single 0 1) + v 1 • M (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [eq_smul_single_add_smul_single v]
    simp only [map_add, map_smul]
  have hw : M w = w 0 • M (EuclideanSpace.single 0 1) + w 1 • M (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [eq_smul_single_add_smul_single w]
    simp only [map_add, map_smul]
  rw [inner_perp_eq, inner_perp_eq, hv, hw]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Two vectors of the plane are linearly independent iff `⟪perp v, w⟫ ≠ 0`. -/
theorem linearIndependent_pair_iff_inner_perp_ne_zero (v w : 𝔼₂) :
    LinearIndependent ℝ ![v, w] ↔ ⟪perp v, w⟫_ℝ ≠ 0 := by
  rw [LinearIndependent.pair_iff, inner_perp_eq]
  constructor
  · intro h hvw
    have h1 := h (w 0) (-v 0) (by ext i; fin_cases i <;> simp <;> linarith [hvw])
    have h2 := h (w 1) (-v 1) (by ext i; fin_cases i <;> simp <;> linarith [hvw])
    have hv0 : v 0 = 0 := neg_eq_zero.1 h1.2
    have hv1 : v 1 = 0 := neg_eq_zero.1 h2.2
    have h3 := h 1 0 (by ext i; fin_cases i <;> simp [hv0, hv1])
    exact one_ne_zero h3.1
  · intro h s t hst
    have h0 := congrArg (fun z : 𝔼₂ ↦ z 0) hst
    have h1 := congrArg (fun z : 𝔼₂ ↦ z 1) hst
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at h0 h1
    have ht : t = 0 := by
      by_contra ht
      apply h
      have : t * (v 1 * w 0 - v 0 * w 1) = 0 := by linear_combination v 1 * h0 - v 0 * h1
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' ht
      · exact h'
    subst ht
    refine ⟨?_, rfl⟩
    by_contra hs
    apply h
    simp only [zero_mul, add_zero] at h0 h1
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact absurd h' hs
    rcases mul_eq_zero.1 h1 with h'' | h''
    · exact absurd h'' hs
    rw [h', h'']; ring

/-- The signed area `⟪perp (B − A), C − A⟫` of a triangle is invariant under cyclic rotation of
the vertices. -/
theorem inner_perp_rotate (A B C : 𝔼₂) :
    ⟪perp (C - B), A - B⟫_ℝ = ⟪perp (B - A), C - A⟫_ℝ := by
  rw [inner_perp_eq, inner_perp_eq]
  simp only [PiLp.sub_apply]
  ring

/-- The signed area changes sign under a transposition of the vertices. -/
theorem inner_perp_swap (A B C : 𝔼₂) :
    ⟪perp (A - B), C - B⟫_ℝ = -⟪perp (B - A), C - A⟫_ℝ := by
  rw [inner_perp_eq, inner_perp_eq]
  simp only [PiLp.sub_apply]
  ring

/-! ### Plane triangles: rotations of the vertices and barycentric coordinates -/

/-- Non-collinearity is invariant under cyclic rotation of the vertices. -/
theorem linearIndependent_rotate {A B C : 𝔼₂} (h : LinearIndependent ℝ ![B - A, C - A]) :
    LinearIndependent ℝ ![C - B, A - B] := by
  rw [linearIndependent_pair_iff_inner_perp_ne_zero] at h ⊢
  rwa [inner_perp_rotate]

/-- Non-collinearity is invariant under a transposition of the vertices. -/
theorem linearIndependent_swap {A B C : 𝔼₂} (h : LinearIndependent ℝ ![B - A, C - A]) :
    LinearIndependent ℝ ![A - B, C - B] := by
  rw [linearIndependent_pair_iff_inner_perp_ne_zero] at h ⊢
  rwa [inner_perp_swap, neg_ne_zero]

/-- The open triangle is invariant under cyclic rotation of the vertices. -/
theorem openTriangle_rotate (A B C : 𝔼₂) : openTriangle B C A = openTriangle A B C := by
  ext x
  simp only [mem_openTriangle]
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨1 - s - t, s, by linarith, hs, by linarith, by module⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨t, 1 - s - t, ht, by linarith, by linarith, by module⟩

/-- The open triangle is invariant under a transposition of the vertices. -/
theorem openTriangle_swap (A B C : 𝔼₂) : openTriangle B A C = openTriangle A B C := by
  ext x
  simp only [mem_openTriangle]
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨1 - s - t, t, by linarith, ht, by linarith, by module⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨1 - s - t, t, by linarith, ht, by linarith, by module⟩

/-- The closed triangle is invariant under cyclic rotation of the vertices. -/
theorem closedTriangle_rotate (A B C : 𝔼₂) : closedTriangle B C A = closedTriangle A B C := by
  ext x
  simp only [mem_closedTriangle]
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨1 - s - t, s, by linarith, hs, by linarith, by module⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨t, 1 - s - t, ht, by linarith, by linarith, by module⟩

/-- The closed triangle is convex. -/
theorem convex_closedTriangle (A B C : 𝔼₂) : Convex ℝ (closedTriangle A B C) := by
  rw [← closure_openTriangle]
  exact (convex_openTriangle A B C).closure

/-- The edges of a triangle lie in the closed triangle. -/
theorem segment_subset_closedTriangle (A B C : 𝔼₂) (a b : Fin 3) :
    segment ℝ (![A, B, C] a) (![A, B, C] b) ⊆ closedTriangle A B C :=
  (convex_closedTriangle A B C).segment_subset (vertex_mem_closedTriangle A B C a)
    (vertex_mem_closedTriangle A B C b)

/-- **Uniqueness of the barycentric coordinates** with respect to non-collinear vertices. -/
theorem eq_of_affine_eq {A B C : 𝔼₂} (h : LinearIndependent ℝ ![B - A, C - A]) {s t s' t' : ℝ}
    (e : A + s • (B - A) + t • (C - A) = A + s' • (B - A) + t' • (C - A)) : s = s' ∧ t = t' := by
  have e' : (s - s') • (B - A) + (t - t') • (C - A) = 0 := by
    calc (s - s') • (B - A) + (t - t') • (C - A)
        = (A + s • (B - A) + t • (C - A)) - (A + s' • (B - A) + t' • (C - A)) := by module
      _ = 0 := sub_eq_zero.2 e
  have := LinearIndependent.pair_iff.1 h _ _ e'
  exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩

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

section EdgeGeometry

variable {P Q R x : 𝔼₂} (h : LinearIndependent ℝ ![Q - P, R - P])
include h

/-- A point of the edge `[P, Q]` is not in the open triangle. -/
theorem notMem_openTriangle_of_mem_segment (hx : x ∈ segment ℝ P Q) :
    x ∉ openTriangle P Q R := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_segment_iff'.1 hx
  rintro hx'
  obtain ⟨s', t', hs', ht', hst', e⟩ := mem_openTriangle.1 hx'
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := s') (t' := t')
    (by rw [zero_smul, add_zero]; exact e)
  linarith [this.2]

/-- A point of the open edge `[P, Q]` is not in the open triangle. -/
theorem notMem_openTriangle_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) :
    x ∉ openTriangle P Q R :=
  notMem_openTriangle_of_mem_segment h (openSegment_subset_segment ℝ _ _ hx)

/-- A point of the open edge `[P, Q]` is not the vertex `P`. -/
theorem ne_left_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) : x ≠ P := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro e
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 0) (t' := 0)
    (by simp only [zero_smul, add_zero]; exact e)
  linarith [this.1]

/-- A point of the open edge `[P, Q]` is not the vertex `Q`. -/
theorem ne_right_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) : x ≠ Q := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro e
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 1) (t' := 0)
    (by simp only [zero_smul, add_zero, one_smul]; rw [e]; abel)
  linarith [this.1]

/-- A point of the open edge `[P, Q]` is not the third vertex `R`. -/
theorem ne_third_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) : x ≠ R := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro e
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 0) (t' := 1)
    (by simp only [zero_smul, add_zero, one_smul]; rw [e]; abel)
  linarith [this.1]

/-- A point of the open edge `[P, Q]` is not a vertex. -/
theorem ne_vertex_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) (i : Fin 3) :
    x ≠ ![P, Q, R] i := by
  fin_cases i
  · exact ne_left_of_mem_openSegment h hx
  · exact ne_right_of_mem_openSegment h hx
  · exact ne_third_of_mem_openSegment h hx

/-- A point of the open edge `[P, Q]` is not on the closed edge `[Q, R]`. -/
theorem notMem_segment_right_third_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) :
    x ∉ segment ℝ Q R := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro hx'
  obtain ⟨u, hu0, hu1, e⟩ := mem_segment_iff'.1 hx'
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 1 - u) (t' := u)
    (by rw [zero_smul, add_zero]; rw [e]; module)
  linarith [this.1, this.2]

/-- A point of the open edge `[P, Q]` is not on the closed edge `[R, P]`. -/
theorem notMem_segment_third_left_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) :
    x ∉ segment ℝ R P := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro hx'
  obtain ⟨u, hu0, hu1, e⟩ := mem_segment_iff'.1 hx'
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 0) (t' := 1 - u)
    (by rw [zero_smul, add_zero]; rw [e]; module)
  linarith [this.1]

/-- **A point of the open edge `[P, Q]` lies on no other closed edge of the triangle**: if it lies
on the edge between the vertices `c ≠ d`, then `{c, d} = {0, 1}`. -/
theorem eq_edge_of_mem_openSegment_of_mem_segment (hx : x ∈ openSegment ℝ P Q) {c d : Fin 3}
    (hcd : c ≠ d) (hs : x ∈ segment ℝ (![P, Q, R] c) (![P, Q, R] d)) :
    (c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0) := by
  have hQR := notMem_segment_right_third_of_mem_openSegment h hx
  have hRP := notMem_segment_third_left_of_mem_openSegment h hx
  have hRQ : x ∉ segment ℝ R Q := by rwa [segment_symm]
  have hPR : x ∉ segment ℝ P R := by rwa [segment_symm]
  fin_cases c <;> fin_cases d
  · exact absurd rfl hcd
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd hs hPR
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hcd
  · exact absurd hs hQR
  · exact absurd hs hRP
  · exact absurd hs hRQ
  · exact absurd rfl hcd

/-- The edge `[P, Q]` lies in the frontier of the open triangle. -/
theorem segment_subset_frontier_openTriangle :
    segment ℝ P Q ⊆ frontier (openTriangle P Q R) := by
  rw [(isOpen_openTriangle P Q R h).frontier_eq, closure_openTriangle]
  exact fun x hx ↦ ⟨segment_subset_closedTriangle P Q R 0 1 hx,
    notMem_openTriangle_of_mem_segment h hx⟩

end EdgeGeometry

/-- The open triangle with vertices `T 0, T 1, T 2`, read from the vertex `a`. -/
theorem openTriangle_eq_rot (T : Fin 3 → 𝔼₂) (a : Fin 3) :
    openTriangle (T 0) (T 1) (T 2) = openTriangle (T a) (T (a + 1)) (T (a + 2)) := by
  fin_cases a
  · rfl
  · exact (openTriangle_rotate (T 0) (T 1) (T 2)).symm
  · exact openTriangle_rotate (T 2) (T 0) (T 1)

/-- The closed triangle with vertices `T 0, T 1, T 2`, read from the vertex `a`. -/
theorem closedTriangle_eq_rot (T : Fin 3 → 𝔼₂) (a : Fin 3) :
    closedTriangle (T 0) (T 1) (T 2) = closedTriangle (T a) (T (a + 1)) (T (a + 2)) := by
  fin_cases a
  · rfl
  · exact (closedTriangle_rotate (T 0) (T 1) (T 2)).symm
  · exact closedTriangle_rotate (T 2) (T 0) (T 1)

/-- Non-collinearity of the vertices `T 0, T 1, T 2`, read from the vertex `a`. -/
theorem linearIndependent_rot {T : Fin 3 → 𝔼₂} (h : LinearIndependent ℝ ![T 1 - T 0, T 2 - T 0])
    (a : Fin 3) : LinearIndependent ℝ ![T (a + 1) - T a, T (a + 2) - T a] := by
  fin_cases a
  · exact h
  · exact linearIndependent_rotate h
  · exact linearIndependent_rotate (linearIndependent_rotate h)

/-- The vertex triple read from the vertex `a`, at the index `i`. -/
theorem vecCons_rot (T : Fin 3 → 𝔼₂) (a i : Fin 3) :
    ![T a, T (a + 1), T (a + 2)] i = T (a + i) := by
  fin_cases i <;> simp

/-- The vertices of a nondegenerate triangle are distinct. -/
theorem vertex_injective {T : Fin 3 → 𝔼₂} (h : LinearIndependent ℝ ![T 1 - T 0, T 2 - T 0]) :
    Function.Injective T := by
  rw [linearIndependent_pair_iff_inner_perp_ne_zero] at h
  intro i j hij
  by_contra hne
  apply h
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · have e : T 0 = T 1 := hij
    rw [e, inner_perp_eq]; simp
  · have e : T 0 = T 2 := hij
    rw [e, inner_perp_eq]; simp
  · have e : T 1 = T 0 := hij
    rw [e, inner_perp_eq]; simp
  · exact absurd rfl hne
  · have e : T 1 = T 2 := hij
    rw [e, inner_perp_self]
  · have e : T 2 = T 0 := hij
    rw [e, inner_perp_eq]; simp
  · have e : T 2 = T 1 := hij
    rw [e, inner_perp_self]
  · exact absurd rfl hne

/-- In `Fin 3`, `a ≠ a + 1`. -/
theorem fin3_ne_add_one (a : Fin 3) : a ≠ a + 1 := by revert a; decide

/-- Two distinct indices of `Fin 3` are consecutive, in one order or the other. -/
theorem exists_fin3_of_ne {i j : Fin 3} (hij : i ≠ j) :
    ∃ a : Fin 3, (i = a ∧ j = a + 1) ∨ (i = a + 1 ∧ j = a) := by
  revert i j; decide

/-! ### Segments and the edge measure -/

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

/-- The parametrization maps `[0, 1]` into the segment. -/
theorem lineMap_mem_segment' (P Q : 𝔼₂) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap P Q t ∈ segment ℝ P Q := by
  rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩

/-- `x ↦ M x + b` maps `lineMap P Q t` to `lineMap (M P + b) (M Q + b) t`. -/
theorem lineMap_affine (M : 𝔼₂ ≃L[ℝ] 𝔼₂) (b P Q : 𝔼₂) (t : ℝ) :
    M (AffineMap.lineMap P Q t) + b = AffineMap.lineMap (M P + b) (M Q + b) t := by
  rw [lineMap_eq, lineMap_eq, map_add, map_smul, map_sub]
  module

/-- The image of a segment under `x ↦ M x + b`. -/
theorem image_segment_affine (M : 𝔼₂ ≃L[ℝ] 𝔼₂) (b P Q : 𝔼₂) :
    (fun x ↦ M x + b) '' segment ℝ P Q = segment ℝ (M P + b) (M Q + b) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap, image_image]
  congr 1
  funext t
  exact lineMap_affine M b P Q t

/-- **The arclength measure of the segment `[P, Q]`**: one-dimensional Lebesgue measure on
`[0, 1]` transported by the parametrization `t ↦ P + t (Q − P)` and scaled by the length
`‖Q − P‖`. -/
def edgeMeasure (P Q : 𝔼₂) : Measure 𝔼₂ :=
  (‖Q - P‖).toNNReal • Measure.map (AffineMap.lineMap P Q) (volume.restrict (Icc (0 : ℝ) 1))

/-- The arclength measure of a segment is finite. -/
instance isFiniteMeasure_edgeMeasure (P Q : 𝔼₂) : IsFiniteMeasure (edgeMeasure P Q) := by
  unfold edgeMeasure
  infer_instance

/-- The arclength measure of a measurable set, through the parametrization. -/
theorem edgeMeasure_apply (P Q : 𝔼₂) {s : Set 𝔼₂} (hs : MeasurableSet s) :
    edgeMeasure P Q s
      = ENNReal.ofReal ‖Q - P‖ * volume ((AffineMap.lineMap P Q : ℝ → 𝔼₂) ⁻¹' s ∩ Icc 0 1) := by
  rw [edgeMeasure, Measure.smul_apply, Measure.map_apply (continuous_lineMap P Q).measurable hs,
    Measure.restrict_apply' measurableSet_Icc, ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal]

/-- The arclength measure is carried by the segment. -/
theorem edgeMeasure_compl_segment (P Q : 𝔼₂) : edgeMeasure P Q (segment ℝ P Q)ᶜ = 0 := by
  rw [edgeMeasure_apply P Q (measurableSet_segment P Q).compl]
  have : (AffineMap.lineMap P Q : ℝ → 𝔼₂) ⁻¹' (segment ℝ P Q)ᶜ ∩ Icc 0 1 = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    exact fun h ht ↦ h (lineMap_mem_segment' P Q ht)
  rw [this, measure_empty, mul_zero]

/-- Almost every point for the arclength measure lies on the segment. -/
theorem ae_mem_segment (P Q : 𝔼₂) : ∀ᵐ x ∂edgeMeasure P Q, x ∈ segment ℝ P Q :=
  ae_iff.2 (edgeMeasure_compl_segment P Q)

/-- Points are null for the arclength measure of a nondegenerate segment. -/
theorem edgeMeasure_singleton {P Q : 𝔼₂} (h : P ≠ Q) (x : 𝔼₂) : edgeMeasure P Q {x} = 0 := by
  rw [edgeMeasure_apply P Q (measurableSet_singleton x)]
  refine mul_eq_zero_of_right _ (measure_mono_null inter_subset_left ?_)
  refine Set.Subsingleton.measure_zero (fun s hs t ht ↦ ?_) _
  exact AffineMap.lineMap_injective ℝ h (hs.trans ht.symm)

/-- The complement of the open segment lies in the complement of the segment plus the
endpoints. -/
theorem compl_openSegment_subset (P Q : 𝔼₂) :
    (openSegment ℝ P Q)ᶜ ⊆ (segment ℝ P Q)ᶜ ∪ {P} ∪ {Q} := by
  intro x hx
  by_cases hs : x ∈ segment ℝ P Q
  · rw [← insert_endpoints_openSegment] at hs
    rcases hs with rfl | rfl | hs
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl
    · exact absurd hs hx
  · exact Or.inl (Or.inl hs)

/-- The arclength measure of a nondegenerate segment is carried by the open segment. -/
theorem edgeMeasure_compl_openSegment {P Q : 𝔼₂} (h : P ≠ Q) :
    edgeMeasure P Q (openSegment ℝ P Q)ᶜ = 0 :=
  measure_mono_null (compl_openSegment_subset P Q)
    (measure_union_null (measure_union_null (edgeMeasure_compl_segment P Q)
      (edgeMeasure_singleton h P)) (edgeMeasure_singleton h Q))

/-- Almost every point for the arclength measure of a nondegenerate segment lies on the open
segment. -/
theorem ae_mem_openSegment {P Q : 𝔼₂} (h : P ≠ Q) :
    ∀ᵐ x ∂edgeMeasure P Q, x ∈ openSegment ℝ P Q :=
  ae_iff.2 (edgeMeasure_compl_openSegment h)

/-- The arclength measure of a degenerate segment vanishes. -/
theorem edgeMeasure_self (P : 𝔼₂) : edgeMeasure P P = 0 := by
  rw [edgeMeasure, sub_self, norm_zero, Real.toNNReal_zero, zero_smul]

/-- The arclength measure does not depend on the orientation of the segment. -/
theorem edgeMeasure_symm (P Q : 𝔼₂) : edgeMeasure Q P = edgeMeasure P Q := by
  unfold edgeMeasure
  rw [norm_sub_rev]
  congr 1
  have h1 : (AffineMap.lineMap Q P : ℝ → 𝔼₂)
      = (AffineMap.lineMap P Q : ℝ → 𝔼₂) ∘ fun t ↦ 1 - t := by
    funext t; simp [AffineMap.lineMap_apply_one_sub]
  have hm : Measurable fun t : ℝ ↦ 1 - t := measurable_const.sub measurable_id
  have h2 : Measure.map (fun t : ℝ ↦ 1 - t) (volume.restrict (Icc (0 : ℝ) 1))
      = volume.restrict (Icc 0 1) := by
    conv_lhs => rw [show Icc (0 : ℝ) 1 = (fun t : ℝ ↦ 1 - t) ⁻¹' Icc 0 1 by
      rw [preimage_const_sub_Icc]; norm_num]
    rw [← Measure.restrict_map hm measurableSet_Icc, Measure.map_sub_left_eq_self]
  rw [h1, ← Measure.map_map (continuous_lineMap P Q).measurable hm, h2]

/-- A function continuous on the segment is measurable for its arclength measure. -/
theorem aestronglyMeasurable_edgeMeasure_of_continuousOn {f : 𝔼₂ → ℝ} {P Q : 𝔼₂}
    (hf : ContinuousOn f (segment ℝ P Q)) : AEStronglyMeasurable f (edgeMeasure P Q) := by
  have := hf.aestronglyMeasurable (μ := edgeMeasure P Q) (measurableSet_segment P Q)
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_segment P Q)] at this

/-- A function continuous on the segment is integrable for its arclength measure. -/
theorem integrable_edgeMeasure_of_continuousOn {f : 𝔼₂ → ℝ} {P Q : 𝔼₂}
    (hf : ContinuousOn f (segment ℝ P Q)) : Integrable f (edgeMeasure P Q) := by
  have : IsFiniteMeasureOnCompacts (edgeMeasure P Q) := ⟨fun _ _ ↦ measure_lt_top _ _⟩
  have := hf.integrableOn_compact (μ := edgeMeasure P Q) (isCompact_segment P Q)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_segment P Q)] at this

/-- Almost every point for the transported Lebesgue measure lies on the segment. -/
theorem ae_map_lineMap_mem_segment (P Q : 𝔼₂) :
    ∀ᵐ x ∂(Measure.map (AffineMap.lineMap P Q) (volume.restrict (Icc (0 : ℝ) 1))),
      x ∈ segment ℝ P Q := by
  refine (ae_map_iff (continuous_lineMap P Q).measurable.aemeasurable
    (measurableSet_segment P Q)).2 ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall fun t ht ↦ lineMap_mem_segment' P Q ht

/-- **The integral against the arclength measure** is the length times the integral along the
parametrization, for a function continuous on the segment. -/
theorem integral_edgeMeasure {f : 𝔼₂ → ℝ} {P Q : 𝔼₂} (hf : ContinuousOn f (segment ℝ P Q)) :
    ∫ x, f x ∂edgeMeasure P Q = ‖Q - P‖ * ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap P Q t) := by
  have hf' : AEStronglyMeasurable f
      (Measure.map (AffineMap.lineMap P Q) (volume.restrict (Icc (0 : ℝ) 1))) := by
    have := hf.aestronglyMeasurable (μ := Measure.map (AffineMap.lineMap P Q)
      (volume.restrict (Icc (0 : ℝ) 1))) (measurableSet_segment P Q)
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_map_lineMap_mem_segment P Q)] at this
  rw [edgeMeasure, integral_smul_nnreal_measure, NNReal.smul_def,
    Real.coe_toNNReal _ (norm_nonneg _), smul_eq_mul,
    integral_map (continuous_lineMap P Q).measurable.aemeasurable hf',
    intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-- An open set meeting the open segment has positive arclength measure. -/
theorem edgeMeasure_pos_of_isOpen {P Q : 𝔼₂} (h : P ≠ Q) {U : Set 𝔼₂} (hU : IsOpen U)
    (hne : (U ∩ openSegment ℝ P Q).Nonempty) : 0 < edgeMeasure P Q U := by
  rw [edgeMeasure_apply P Q hU.measurableSet]
  refine ENNReal.mul_pos ?_ ?_
  · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact norm_pos_iff.2 (sub_ne_zero.2 h.symm)
  · obtain ⟨x, hxU, hxs⟩ := hne
    rw [openSegment_eq_image_lineMap] at hxs
    obtain ⟨t, ht, rfl⟩ := hxs
    refine ne_of_gt (lt_of_lt_of_le ?_
      (measure_mono (inter_subset_inter_right _ Ioo_subset_Icc_self)))
    exact ((hU.preimage (continuous_lineMap P Q)).inter isOpen_Ioo).measure_pos volume
      ⟨t, hxU, ht⟩

/-! ### The edge normal -/

/-- **The unit normal of the edge `[P, Q]` pointing away from the third vertex `R`**: the outward
normal of the triangle `P Q R` on that edge. The sign is fixed by `⟪edgeNormal P Q R, R − P⟫ < 0`
(`inner_edgeNormal_third_neg`), an affine-invariant condition. -/
def edgeNormal (P Q R : 𝔼₂) : 𝔼₂ :=
  if ⟪perp (Q - P), R - P⟫_ℝ < 0 then ‖Q - P‖⁻¹ • perp (Q - P)
  else -(‖Q - P‖⁻¹ • perp (Q - P))

/-- A nondegenerate triangle has distinct vertices `P ≠ Q`. -/
theorem ne_of_inner_perp_ne_zero {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) : P ≠ Q := by
  rintro rfl
  apply h
  rw [sub_self, inner_perp_eq]
  simp

/-- The edge normal of a nondegenerate triangle is a unit vector. -/
theorem norm_edgeNormal {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) :
    ‖edgeNormal P Q R‖ = 1 := by
  have hQP : ‖Q - P‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (ne_of_inner_perp_ne_zero h).symm)
  unfold edgeNormal
  split_ifs <;> simp [norm_smul, norm_perp, hQP]

/-- The edge normal is orthogonal to the edge. -/
theorem inner_edgeNormal_sub (P Q R : 𝔼₂) : ⟪edgeNormal P Q R, Q - P⟫_ℝ = 0 := by
  unfold edgeNormal
  split_ifs <;> simp [inner_smul_left, inner_perp_self]

/-- `⟪edgeNormal P Q R, y − x₀⟫` is constant along the edge: the fact behind the transversal
field `x − x₀` on a convex polygon. -/
theorem inner_edgeNormal_lineMap_sub (P Q R x₀ : 𝔼₂) (t : ℝ) :
    ⟪edgeNormal P Q R, AffineMap.lineMap P Q t - x₀⟫_ℝ = ⟪edgeNormal P Q R, P - x₀⟫_ℝ := by
  rw [lineMap_eq, show P + t • (Q - P) - x₀ = (P - x₀) + t • (Q - P) by module, inner_add_right,
    inner_smul_right, inner_edgeNormal_sub, mul_zero, add_zero]

/-- The edge normal points away from the third vertex. -/
theorem inner_edgeNormal_third_neg {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) :
    ⟪edgeNormal P Q R, R - P⟫_ℝ < 0 := by
  have hQP : 0 < ‖Q - P‖ := norm_pos_iff.2 (sub_ne_zero.2 (ne_of_inner_perp_ne_zero h).symm)
  unfold edgeNormal
  split_ifs with hx
  · rw [inner_smul_left]
    simpa using mul_neg_of_pos_of_neg (inv_pos.2 hQP) hx
  · rw [inner_neg_left, inner_smul_left, neg_lt_zero]
    simpa using mul_pos (inv_pos.2 hQP) (lt_of_le_of_ne (not_lt.1 hx) (Ne.symm h))

/-- The edge normal does not depend on the orientation of the edge. -/
theorem edgeNormal_symm {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) :
    edgeNormal Q P R = edgeNormal P Q R := by
  unfold edgeNormal
  rw [inner_perp_swap, norm_sub_rev, ← neg_sub Q P, perp_neg, smul_neg]
  split_ifs with h1 h2 h2
  · exfalso; linarith
  · rfl
  · rw [neg_neg]
  · exfalso; exact h (by linarith)

/-- Third vertices on opposite sides of the edge give opposite edge normals. -/
theorem edgeNormal_eq_neg_of_mul_neg {P Q R R' : 𝔼₂}
    (h : ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), R' - P⟫_ℝ < 0) :
    edgeNormal P Q R' = -edgeNormal P Q R := by
  unfold edgeNormal
  rcases mul_neg_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ite_eq_left h2, ite_eq_right (not_lt.2 h1.le), neg_neg]
  · rw [ite_eq_right (not_lt.2 h2.le), ite_eq_left h1]

/-- Third vertices on the same side of the edge give the same edge normal. -/
theorem edgeNormal_eq_of_mul_pos {P Q R R' : 𝔼₂}
    (h : 0 < ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), R' - P⟫_ℝ) :
    edgeNormal P Q R' = edgeNormal P Q R := by
  unfold edgeNormal
  rcases mul_pos_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ite_eq_right (not_lt.2 h2.le), ite_eq_right (not_lt.2 h1.le)]
  · rw [ite_eq_left h2, ite_eq_left h1]

/-- **The edge term of a positively oriented edge**: for `⟪perp (Q − P), R − P⟫ < 0`,
`∫ ⟪F, edgeNormal P Q R⟫ d(edgeMeasure P Q) = ∫_0^1 ⟪perp (Q − P), F (lineMap P Q t)⟫ dt` — the
length of the edge cancels the normalization of the normal. -/
theorem integral_inner_edgeNormal_of_neg {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ < 0)
    {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F (segment ℝ P Q)) :
    ∫ x, ⟪F x, edgeNormal P Q R⟫_ℝ ∂edgeMeasure P Q
      = ∫ t in (0 : ℝ)..1, ⟪perp (Q - P), F (AffineMap.lineMap P Q t)⟫_ℝ := by
  have hn : ‖Q - P‖ ≠ 0 :=
    norm_ne_zero_iff.2 (sub_ne_zero.2 (ne_of_inner_perp_ne_zero h.ne).symm)
  rw [integral_edgeMeasure (hF.inner continuousOn_const), edgeNormal, ite_eq_left h]
  simp_rw [inner_smul_right, real_inner_comm (perp (Q - P))]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

/-! ### Transport of an edge term by an affine map -/

/-- `⟪M⁻¹ y, perp v⟫ = (det M)⁻¹ ⟪y, perp (M v)⟫`. -/
theorem inner_symm_perp (M : 𝔼₂ ≃L[ℝ] 𝔼₂) (v y : 𝔼₂) :
    ⟪M.symm y, perp v⟫_ℝ
      = (LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂))⁻¹ * ⟪y, perp (M v)⟫_ℝ := by
  have hd : LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂) ≠ 0 :=
    (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  have := inner_perp_map (M : 𝔼₂ →L[ℝ] 𝔼₂) v (M.symm y)
  rw [ContinuousLinearEquiv.coe_coe, M.apply_symm_apply] at this
  rw [eq_inv_mul_iff_mul_eq₀ hd, real_inner_comm (perp (M v)) y, this,
    real_inner_comm (M.symm y) (perp v)]

/-- **The edge normal transported by `x ↦ M x + b`**: `⟪M⁻¹ y, edgeNormal P Q R⟫` is
`|det M|⁻¹ ‖M (Q − P)‖ ‖Q − P‖⁻¹ ⟪y, edgeNormal (M P + b) (M Q + b) (M R + b)⟫`; the sign
condition of `edgeNormal` transports by `inner_perp_map`. -/
theorem inner_symm_edgeNormal (M : 𝔼₂ ≃L[ℝ] 𝔼₂) (b : 𝔼₂) {P Q R : 𝔼₂}
    (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) (y : 𝔼₂) :
    ⟪M.symm y, edgeNormal P Q R⟫_ℝ
      = |LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂)|⁻¹ * ‖(M Q + b) - (M P + b)‖
        * ‖Q - P‖⁻¹ * ⟪y, edgeNormal (M P + b) (M Q + b) (M R + b)⟫_ℝ := by
  set d := LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂) with hd_def
  have hd : d ≠ 0 := (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  have hQP : (M Q + b) - (M P + b) = M (Q - P) := by rw [map_sub]; abel
  have hRP : (M R + b) - (M P + b) = M (R - P) := by rw [map_sub]; abel
  have hx' : ⟪perp ((M Q + b) - (M P + b)), (M R + b) - (M P + b)⟫_ℝ
      = d * ⟪perp (Q - P), R - P⟫_ℝ := by
    rw [hQP, hRP]
    exact inner_perp_map (M : 𝔼₂ →L[ℝ] 𝔼₂) _ _
  have hn : ‖Q - P‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (ne_of_inner_perp_ne_zero h).symm)
  have hn' : ‖(M Q + b) - (M P + b)‖ ≠ 0 := by
    rw [hQP]
    exact norm_ne_zero_iff.2 (M.injective.ne_iff' (map_zero M) |>.2 (sub_ne_zero.2
      (ne_of_inner_perp_ne_zero h).symm))
  have key : ⟪M.symm y, perp (Q - P)⟫_ℝ = d⁻¹ * ⟪y, perp ((M Q + b) - (M P + b))⟫_ℝ := by
    rw [hQP]; exact inner_symm_perp M _ _
  unfold edgeNormal
  rw [hx']
  rcases lt_or_gt_of_ne h with hx | hx <;> rcases lt_or_gt_of_ne hd with hdn | hdp
  · rw [ite_eq_left hx, ite_eq_right (not_lt.2 (mul_nonneg_of_nonpos_of_nonpos hdn.le hx.le)),
      abs_of_neg hdn, inner_smul_right, inner_neg_right, inner_smul_right, key]
    field_simp
  · rw [ite_eq_left hx, ite_eq_left (mul_neg_of_pos_of_neg hdp hx), abs_of_pos hdp,
      inner_smul_right, inner_smul_right, key]
    field_simp
  · rw [ite_eq_right (not_lt.2 hx.le), ite_eq_left (mul_neg_of_neg_of_pos hdn hx), abs_of_neg hdn,
      inner_neg_right, inner_smul_right, inner_smul_right, key]
    field_simp
  · rw [ite_eq_right (not_lt.2 hx.le), ite_eq_right (not_lt.2 (mul_pos hdp hx).le), abs_of_pos hdp,
      inner_neg_right, inner_smul_right, inner_neg_right, inner_smul_right, key]
    field_simp

/-- **Transport of an edge term by the affine map `x ↦ M x + b`**: `|det M|` times the edge term
of the conjugate field `M⁻¹ ∘ F ∘ (M · + b)` on the edge `[P, Q]` of the triangle `P Q R` is the
edge term of `F` on the image edge, with the image triangle's outward normal. -/
theorem integral_inner_edgeNormal_affine (M : 𝔼₂ ≃L[ℝ] 𝔼₂) (b : 𝔼₂) {P Q R : 𝔼₂}
    (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) {F : 𝔼₂ → 𝔼₂}
    (hF : ContinuousOn F (segment ℝ (M P + b) (M Q + b))) :
    |LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂)|
        * ∫ x, ⟪M.symm (F (M x + b)), edgeNormal P Q R⟫_ℝ ∂edgeMeasure P Q
      = ∫ y, ⟪F y, edgeNormal (M P + b) (M Q + b) (M R + b)⟫_ℝ
          ∂edgeMeasure (M P + b) (M Q + b) := by
  have hd : |LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂)| ≠ 0 :=
    abs_ne_zero.2 (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  have hn : ‖Q - P‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (ne_of_inner_perp_ne_zero h).symm)
  have hΦ : Continuous fun x ↦ M x + b := M.continuous.add continuous_const
  have hF₁ : ContinuousOn (fun x ↦ ⟪M.symm (F (M x + b)), edgeNormal P Q R⟫_ℝ)
      (segment ℝ P Q) := by
    refine ContinuousOn.inner (M.symm.continuous.comp_continuousOn (hF.comp hΦ.continuousOn ?_))
      continuousOn_const
    rw [← image_segment_affine M b P Q]; exact mapsTo_image _ _
  have hF₂ : ContinuousOn (fun y ↦ ⟪F y, edgeNormal (M P + b) (M Q + b) (M R + b)⟫_ℝ)
      (segment ℝ (M P + b) (M Q + b)) :=
    hF.inner continuousOn_const
  rw [integral_edgeMeasure hF₁, integral_edgeMeasure hF₂]
  simp_rw [inner_symm_edgeNormal M b h, lineMap_affine M b P Q]
  rw [intervalIntegral.integral_const_mul]
  field_simp

/-! ### The half-disc lemma -/

/-- **A triangle contains a half-disc around the midpoint of each edge, on its own side**: for
`‖v‖` small and `v` pointing to the side of the third vertex `R` (`0 < s ⟪perp (Q − P), v⟫` with
`s := ⟪perp (Q − P), R − P⟫`), the point `midpoint P Q + v` lies in the open triangle. -/
theorem exists_ball_inter_subset_openTriangle {P Q R : 𝔼₂}
    (h : LinearIndependent ℝ ![Q - P, R - P]) :
    ∃ δ > 0, ∀ v : 𝔼₂, ‖v‖ < δ → 0 < ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), v⟫_ℝ →
      midpoint ℝ P Q + v ∈ openTriangle P Q R := by
  set M := triangleEquiv P Q R h with hM
  set C := ‖(M.symm : 𝔼₂ →L[ℝ] 𝔼₂)‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  refine ⟨1 / (4 * (C + 1)), by positivity, fun v hv hpos ↦ ?_⟩
  set w := M.symm v with hw
  have hvw : v = w 0 • (Q - P) + w 1 • (R - P) := by
    rw [← triangleEquiv_apply P Q R h, ← hM, hw, M.apply_symm_apply]
  have hwle : ∀ i, |w i| ≤ C * ‖v‖ := fun i ↦ by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le w i).trans ((M.symm : 𝔼₂ →L[ℝ] 𝔼₂).le_opNorm v)
  have hCv : C * ‖v‖ < 1 / 4 := by
    calc C * ‖v‖ ≤ C * (1 / (4 * (C + 1))) := by gcongr
      _ < 1 / 4 := by
        rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  have hw0 := abs_lt.1 ((hwle 0).trans_lt hCv)
  have hw1 := abs_lt.1 ((hwle 1).trans_lt hCv)
  have hinner : ⟪perp (Q - P), v⟫_ℝ = w 1 * ⟪perp (Q - P), R - P⟫_ℝ := by
    rw [hvw, inner_add_right, inner_smul_right, inner_smul_right, inner_perp_self, mul_zero,
      zero_add]
  have hw1pos : 0 < w 1 := by
    rw [hinner] at hpos
    have hs : 0 < ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), R - P⟫_ℝ :=
      mul_self_pos.2 ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 h)
    nlinarith
  rw [mem_openTriangle]
  refine ⟨1 / 2 + w 0, w 1, by linarith, hw1pos, by linarith, ?_⟩
  rw [hvw, midpoint_eq_smul_add, invOf_eq_inv, one_div]
  module

/-- **Two triangles on the same side of a common edge overlap**: if the third vertices `R, R'`
of the triangles `P Q R` and `P Q R'` lie strictly on the same side of the line `P Q`, the open
triangles meet. -/
theorem openTriangle_inter_nonempty_of_same_side {P Q R R' : 𝔼₂}
    (hs : 0 < ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), R' - P⟫_ℝ) :
    (openTriangle P Q R ∩ openTriangle P Q R').Nonempty := by
  obtain ⟨hs0, hs0'⟩ := mul_ne_zero_iff.1 hs.ne'
  have h : LinearIndependent ℝ ![Q - P, R - P] :=
    (linearIndependent_pair_iff_inner_perp_ne_zero _ _).2 hs0
  have h' : LinearIndependent ℝ ![Q - P, R' - P] :=
    (linearIndependent_pair_iff_inner_perp_ne_zero _ _).2 hs0'
  obtain ⟨δ, hδ, hδ'⟩ := exists_ball_inter_subset_openTriangle h
  obtain ⟨δ', hδ'0, hδ''⟩ := exists_ball_inter_subset_openTriangle h'
  set ε := min δ δ' / (2 * (‖R - P‖ + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hnorm : ‖ε • (R - P)‖ < min δ δ' := by
    rw [norm_smul, Real.norm_of_nonneg hε0.le, hε, div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity)]
    nlinarith [lt_min hδ hδ'0, norm_nonneg (R - P)]
  have hin : ⟪perp (Q - P), ε • (R - P)⟫_ℝ = ε * ⟪perp (Q - P), R - P⟫_ℝ :=
    inner_smul_right _ _ _
  refine ⟨midpoint ℝ P Q + ε • (R - P), hδ' _ (hnorm.trans_le (min_le_left _ _)) ?_,
    hδ'' _ (hnorm.trans_le (min_le_right _ _)) ?_⟩
  · rw [hin]
    have : 0 < ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), R - P⟫_ℝ := mul_self_pos.2 hs0
    nlinarith
  · rw [hin]
    nlinarith

/-! ### The boundary measure and the outward normal of a triangle -/

/-- **The arclength measure of the boundary of the triangle `A B C`**: the sum of the arclength
measures of its three edges. -/
def triangleBoundaryMeasure (A B C : 𝔼₂) : Measure 𝔼₂ :=
  edgeMeasure A B + edgeMeasure B C + edgeMeasure C A

open Classical in
/-- **The outward unit normal of the triangle `A B C`**, defined on the relative interiors of the
three edges (the vertices are null for the boundary measure) and `0` elsewhere. -/
def triangleNormal (A B C : 𝔼₂) : 𝔼₂ → 𝔼₂ := fun x ↦
  if x ∈ openSegment ℝ A B then edgeNormal A B C
  else if x ∈ openSegment ℝ B C then edgeNormal B C A
  else if x ∈ openSegment ℝ C A then edgeNormal C A B else 0

/-- The boundary measure of a triangle is finite. -/
instance isFiniteMeasure_triangleBoundaryMeasure (A B C : 𝔼₂) :
    IsFiniteMeasure (triangleBoundaryMeasure A B C) := by
  unfold triangleBoundaryMeasure
  infer_instance

section TriangleNormal

variable {A B C : 𝔼₂} (h : LinearIndependent ℝ ![B - A, C - A])
include h

omit h in
/-- On the open edge `[A, B]`, the normal of the triangle is the edge normal. -/
theorem triangleNormal_eq_of_mem_openSegment₀₁ {x : 𝔼₂} (hx : x ∈ openSegment ℝ A B) :
    triangleNormal A B C x = edgeNormal A B C := by
  rw [triangleNormal, ite_eq_left hx]

/-- On the open edge `[B, C]`, the normal of the triangle is the edge normal. -/
theorem triangleNormal_eq_of_mem_openSegment₁₂ {x : 𝔼₂} (hx : x ∈ openSegment ℝ B C) :
    triangleNormal A B C x = edgeNormal B C A := by
  have h1 : x ∉ openSegment ℝ A B := fun hx' ↦
    notMem_segment_right_third_of_mem_openSegment h hx' (openSegment_subset_segment ℝ _ _ hx)
  rw [triangleNormal, ite_eq_right h1, ite_eq_left hx]

/-- On the open edge `[C, A]`, the normal of the triangle is the edge normal. -/
theorem triangleNormal_eq_of_mem_openSegment₂₀ {x : 𝔼₂} (hx : x ∈ openSegment ℝ C A) :
    triangleNormal A B C x = edgeNormal C A B := by
  have h1 : x ∉ openSegment ℝ A B := fun hx' ↦
    notMem_segment_third_left_of_mem_openSegment h hx' (openSegment_subset_segment ℝ _ _ hx)
  have h2 : x ∉ openSegment ℝ B C := fun hx' ↦
    notMem_segment_right_third_of_mem_openSegment (linearIndependent_rotate h) hx'
      (openSegment_subset_segment ℝ _ _ hx)
  rw [triangleNormal, ite_eq_right h1, ite_eq_right h2, ite_eq_left hx]

/-- The vertices of a nondegenerate triangle are distinct: `A ≠ B`. -/
theorem ne₀₁ : A ≠ B :=
  ne_of_inner_perp_ne_zero ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 h)

/-- The vertices of a nondegenerate triangle are distinct: `B ≠ C`. -/
theorem ne₁₂ : B ≠ C :=
  ne_of_inner_perp_ne_zero
    ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (linearIndependent_rotate h))

/-- The vertices of a nondegenerate triangle are distinct: `C ≠ A`. -/
theorem ne₂₀ : C ≠ A :=
  ne_of_inner_perp_ne_zero ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1
    (linearIndependent_rotate (linearIndependent_rotate h)))

/-- The normal of a triangle is a unit vector almost everywhere for its boundary measure. -/
theorem ae_norm_triangleNormal :
    ∀ᵐ x ∂triangleBoundaryMeasure A B C, ‖triangleNormal A B C x‖ = 1 := by
  have h1 := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 h
  have h2 := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (linearIndependent_rotate h)
  have h3 := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1
    (linearIndependent_rotate (linearIndependent_rotate h))
  unfold triangleBoundaryMeasure
  rw [ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨(ae_mem_openSegment (ne₀₁ h)).mono fun x hx ↦ ?_,
    (ae_mem_openSegment (ne₁₂ h)).mono fun x hx ↦ ?_⟩,
    (ae_mem_openSegment (ne₂₀ h)).mono fun x hx ↦ ?_⟩
  · rw [triangleNormal_eq_of_mem_openSegment₀₁ hx]; exact norm_edgeNormal h1
  · rw [triangleNormal_eq_of_mem_openSegment₁₂ h hx]; exact norm_edgeNormal h2
  · rw [triangleNormal_eq_of_mem_openSegment₂₀ h hx]; exact norm_edgeNormal h3

/-- The normal of a triangle is measurable for its boundary measure. -/
theorem aestronglyMeasurable_triangleNormal :
    AEStronglyMeasurable (triangleNormal A B C) (triangleBoundaryMeasure A B C) := by
  unfold triangleBoundaryMeasure
  refine (AEStronglyMeasurable.add_measure
    ((aestronglyMeasurable_const (b := edgeNormal A B C)).congr ?_)
    ((aestronglyMeasurable_const (b := edgeNormal B C A)).congr ?_)).add_measure
    ((aestronglyMeasurable_const (b := edgeNormal C A B)).congr ?_)
  · exact (ae_mem_openSegment (ne₀₁ h)).mono fun x hx ↦
      (triangleNormal_eq_of_mem_openSegment₀₁ hx).symm
  · exact (ae_mem_openSegment (ne₁₂ h)).mono fun x hx ↦
      (triangleNormal_eq_of_mem_openSegment₁₂ h hx).symm
  · exact (ae_mem_openSegment (ne₂₀ h)).mono fun x hx ↦
      (triangleNormal_eq_of_mem_openSegment₂₀ h hx).symm

/-- The boundary measure of a triangle is carried by the frontier of the open triangle. -/
theorem triangleBoundaryMeasure_compl_frontier :
    triangleBoundaryMeasure A B C (frontier (openTriangle A B C))ᶜ = 0 := by
  have e1 := segment_subset_frontier_openTriangle h
  have e2 := segment_subset_frontier_openTriangle (linearIndependent_rotate h)
  have e3 := segment_subset_frontier_openTriangle
    (linearIndependent_rotate (linearIndependent_rotate h))
  rw [openTriangle_rotate] at e2
  rw [openTriangle_rotate, openTriangle_rotate] at e3
  unfold triangleBoundaryMeasure
  rw [Measure.add_apply, Measure.add_apply]
  refine add_eq_zero.2 ⟨add_eq_zero.2 ⟨?_, ?_⟩, ?_⟩
  · exact measure_mono_null (compl_subset_compl.2 e1) (edgeMeasure_compl_segment A B)
  · exact measure_mono_null (compl_subset_compl.2 e2) (edgeMeasure_compl_segment B C)
  · exact measure_mono_null (compl_subset_compl.2 e3) (edgeMeasure_compl_segment C A)

omit h in
/-- The integral against the boundary measure of a triangle is the sum of the three edge
integrals. -/
theorem integral_triangleBoundaryMeasure {f : 𝔼₂ → ℝ} (h₁ : Integrable f (edgeMeasure A B))
    (h₂ : Integrable f (edgeMeasure B C)) (h₃ : Integrable f (edgeMeasure C A)) :
    ∫ x, f x ∂triangleBoundaryMeasure A B C
      = ∫ x, f x ∂edgeMeasure A B + ∫ x, f x ∂edgeMeasure B C + ∫ x, f x ∂edgeMeasure C A := by
  unfold triangleBoundaryMeasure
  rw [integral_add_measure (h₁.add_measure h₂) h₃, integral_add_measure h₁ h₂]

/-- **The boundary integral of `⟪F, ν⟫` on a triangle is the sum of the three edge terms**, each
with the constant outward edge normal, for `F` continuous on the closed triangle. -/
theorem integral_inner_triangleNormal {F : 𝔼₂ → 𝔼₂}
    (hF : ContinuousOn F (closedTriangle A B C)) :
    ∫ x, ⟪F x, triangleNormal A B C x⟫_ℝ ∂triangleBoundaryMeasure A B C
      = ∫ x, ⟪F x, edgeNormal A B C⟫_ℝ ∂edgeMeasure A B
        + ∫ x, ⟪F x, edgeNormal B C A⟫_ℝ ∂edgeMeasure B C
        + ∫ x, ⟪F x, edgeNormal C A B⟫_ℝ ∂edgeMeasure C A := by
  have a1 : (fun x ↦ ⟪F x, triangleNormal A B C x⟫_ℝ) =ᵐ[edgeMeasure A B]
      fun x ↦ ⟪F x, edgeNormal A B C⟫_ℝ :=
    (ae_mem_openSegment (ne₀₁ h)).mono fun x hx ↦ by
      dsimp only; rw [triangleNormal_eq_of_mem_openSegment₀₁ hx]
  have a2 : (fun x ↦ ⟪F x, triangleNormal A B C x⟫_ℝ) =ᵐ[edgeMeasure B C]
      fun x ↦ ⟪F x, edgeNormal B C A⟫_ℝ :=
    (ae_mem_openSegment (ne₁₂ h)).mono fun x hx ↦ by
      dsimp only; rw [triangleNormal_eq_of_mem_openSegment₁₂ h hx]
  have a3 : (fun x ↦ ⟪F x, triangleNormal A B C x⟫_ℝ) =ᵐ[edgeMeasure C A]
      fun x ↦ ⟪F x, edgeNormal C A B⟫_ℝ :=
    (ae_mem_openSegment (ne₂₀ h)).mono fun x hx ↦ by
      dsimp only; rw [triangleNormal_eq_of_mem_openSegment₂₀ h hx]
  have i1 : Integrable (fun x ↦ ⟪F x, edgeNormal A B C⟫_ℝ) (edgeMeasure A B) :=
    integrable_edgeMeasure_of_continuousOn
      ((hF.mono (segment_subset_closedTriangle A B C 0 1)).inner continuousOn_const)
  have i2 : Integrable (fun x ↦ ⟪F x, edgeNormal B C A⟫_ℝ) (edgeMeasure B C) :=
    integrable_edgeMeasure_of_continuousOn
      ((hF.mono (segment_subset_closedTriangle A B C 1 2)).inner continuousOn_const)
  have i3 : Integrable (fun x ↦ ⟪F x, edgeNormal C A B⟫_ℝ) (edgeMeasure C A) :=
    integrable_edgeMeasure_of_continuousOn
      ((hF.mono (segment_subset_closedTriangle A B C 2 0)).inner continuousOn_const)
  rw [integral_triangleBoundaryMeasure (i1.congr a1.symm) (i2.congr a2.symm) (i3.congr a3.symm),
    integral_congr_ae a1, integral_congr_ae a2, integral_congr_ae a3]

end TriangleNormal

/-! ### Fubini on the reference triangle -/

/-- The measurable equivalence `𝔼₂ ≃ᵐ ℝ × ℝ`, `x ↦ (x 0, x 1)`. -/
def planeMeasurableEquiv : 𝔼₂ ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

/-- The coordinate equivalence `𝔼₂ ≃ᵐ ℝ × ℝ` preserves Lebesgue measure. -/
theorem measurePreserving_planeMeasurableEquiv :
    MeasurePreserving planeMeasurableEquiv volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

@[simp] theorem planeMeasurableEquiv_apply (x : 𝔼₂) : planeMeasurableEquiv x = (x 0, x 1) := rfl

@[simp] theorem planeMeasurableEquiv_symm_apply (p : ℝ × ℝ) :
    planeMeasurableEquiv.symm p = !₂[p.1, p.2] := by
  ext i; fin_cases i <;> rfl

/-- The reference triangle in the coordinates of `ℝ × ℝ`. -/
def planeTriangle : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

/-- The plane triangle is measurable. -/
theorem measurableSet_planeTriangle : MeasurableSet planeTriangle :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const))

/-- The reference triangle is the preimage of the plane triangle. -/
theorem preimage_referenceTriangle :
    planeMeasurableEquiv.symm ⁻¹' (referenceTriangle : Set 𝔼₂) = planeTriangle := by
  ext p
  exact Iff.rfl

/-- The slice integral of the indicator of a triangle `{0 < x, 0 < y, x + y < 1}` in `y`. -/
theorem integral_indicator_slice (x : ℝ) (k : ℝ → ℝ) :
    ∫ y, {y : ℝ | 0 < x ∧ 0 < y ∧ x + y < 1}.indicator k y
      = (Ioo (0 : ℝ) 1).indicator (fun x ↦ ∫ y in (0 : ℝ)..(1 - x), k y) x := by
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hx, intervalIntegral.integral_of_le (by linarith [hx.2]),
      integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
    congr 1
    funext y
    simp only [Set.indicator_apply, mem_Ioo, mem_ofPred_eq]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨h1.2.1, by linarith [h1.2.2]⟩ h2
    · exact absurd ⟨hx.1, h2.1, by linarith [h2.2]⟩ h1
    · rfl
  · rw [indicator_of_notMem hx]
    have : ∀ y, {y : ℝ | 0 < x ∧ 0 < y ∧ x + y < 1}.indicator k y = 0 := fun y ↦
      indicator_of_notMem (by rintro ⟨h1, h2, h3⟩; exact hx ⟨h1, by linarith⟩) _
    simp only [this, integral_zero]

/-- The indicator of the plane triangle at `(x, y)`, as an indicator in `y`. -/
theorem indicator_planeTriangle (g : ℝ × ℝ → ℝ) (x y : ℝ) :
    planeTriangle.indicator g (x, y)
      = {y : ℝ | 0 < x ∧ 0 < y ∧ x + y < 1}.indicator (fun y ↦ g (x, y)) y := rfl

/-- The indicator of the plane triangle at `(x, y)`, as an indicator in `x`. -/
theorem indicator_planeTriangle' (g : ℝ × ℝ → ℝ) (x y : ℝ) :
    planeTriangle.indicator g (x, y)
      = {x : ℝ | 0 < y ∧ 0 < x ∧ y + x < 1}.indicator (fun x ↦ g (x, y)) x := by
  by_cases h : (x, y) ∈ planeTriangle
  · rw [indicator_of_mem h, indicator_of_mem (show x ∈ {x : ℝ | 0 < y ∧ 0 < x ∧ y + x < 1} from
      ⟨h.2.1, h.1, by linarith [h.2.2]⟩)]
  · rw [indicator_of_notMem h,
      indicator_of_notMem (fun h' ↦ h ⟨h'.2.1, h'.1, by linarith [h'.2.2]⟩)]

/-- **Fubini on the plane triangle**, `x` outside. -/
theorem integral_planeTriangle_eq {g : ℝ × ℝ → ℝ} (hg : IntegrableOn g planeTriangle) :
    ∫ p in planeTriangle, g p = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), g (x, y) := by
  rw [← integral_indicator measurableSet_planeTriangle, Measure.volume_eq_prod,
    integral_prod _ ((integrable_indicator_iff measurableSet_planeTriangle).2 hg)]
  have : ∀ x, ∫ y, planeTriangle.indicator g (x, y)
      = (Ioo (0 : ℝ) 1).indicator (fun x ↦ ∫ y in (0 : ℝ)..(1 - x), g (x, y)) x := fun x ↦ by
    simp only [indicator_planeTriangle]
    rw [integral_indicator_slice]
    by_cases hx : x ∈ Ioo (0 : ℝ) 1 <;> simp [hx]
  simp only [this]
  rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

/-- **Fubini on the plane triangle**, `y` outside. -/
theorem integral_planeTriangle_eq' {g : ℝ × ℝ → ℝ} (hg : IntegrableOn g planeTriangle) :
    ∫ p in planeTriangle, g p = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..(1 - y), g (x, y) := by
  rw [← integral_indicator measurableSet_planeTriangle, Measure.volume_eq_prod,
    integral_prod_symm _ ((integrable_indicator_iff measurableSet_planeTriangle).2 hg)]
  have : ∀ y, ∫ x, planeTriangle.indicator g (x, y)
      = (Ioo (0 : ℝ) 1).indicator (fun y ↦ ∫ x in (0 : ℝ)..(1 - y), g (x, y)) y := fun y ↦ by
    simp only [indicator_planeTriangle']
    rw [integral_indicator_slice]
    by_cases hy : y ∈ Ioo (0 : ℝ) 1 <;> simp [hy]
  simp only [this]
  rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

/-- **Fubini on the reference triangle**, `x` outside:
`∫_T̂ h = ∫_0^1 ∫_0^{1−x} h(x, y) dy dx`. -/
theorem integral_referenceTriangle_eq {h : 𝔼₂ → ℝ}
    (hh : IntegrableOn h (referenceTriangle : Set 𝔼₂)) :
    ∫ x in (referenceTriangle : Set 𝔼₂), h x
      = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), h !₂[x, y] := by
  rw [← measurePreserving_planeMeasurableEquiv.symm.setIntegral_preimage_emb
    planeMeasurableEquiv.symm.measurableEmbedding, preimage_referenceTriangle,
    integral_planeTriangle_eq]
  · simp only [planeMeasurableEquiv_symm_apply]
  · rw [← preimage_referenceTriangle]
    exact (measurePreserving_planeMeasurableEquiv.symm.integrableOn_comp_preimage
      planeMeasurableEquiv.symm.measurableEmbedding).2 hh

/-- **Fubini on the reference triangle**, `y` outside:
`∫_T̂ h = ∫_0^1 ∫_0^{1−y} h(x, y) dx dy`. -/
theorem integral_referenceTriangle_eq' {h : 𝔼₂ → ℝ}
    (hh : IntegrableOn h (referenceTriangle : Set 𝔼₂)) :
    ∫ x in (referenceTriangle : Set 𝔼₂), h x
      = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..(1 - y), h !₂[x, y] := by
  rw [← measurePreserving_planeMeasurableEquiv.symm.setIntegral_preimage_emb
    planeMeasurableEquiv.symm.measurableEmbedding, preimage_referenceTriangle,
    integral_planeTriangle_eq']
  · simp only [planeMeasurableEquiv_symm_apply]
  · rw [← preimage_referenceTriangle]
    exact (measurePreserving_planeMeasurableEquiv.symm.integrableOn_comp_preimage
      planeMeasurableEquiv.symm.measurableEmbedding).2 hh

/-! ### The divergence theorem on the reference triangle -/

/-- `y ↦ !₂[f y, g y]` is continuous for continuous `f, g`. -/
theorem continuous_toLp₂ {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y ↦ (!₂[f y, g y] : 𝔼₂) := by
  have : (fun y ↦ (!₂[f y, g y] : 𝔼₂))
      = (WithLp.toLp 2 : (Fin 2 → ℝ) → 𝔼₂) ∘ fun y ↦ ![f y, g y] := rfl
  rw [this]
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 ↦ ℝ)).comp (continuous_pi fun i ↦ ?_)
  fin_cases i <;> simpa

/-- The vertical line `y ↦ !₂[x, y]` has derivative `e₁`. -/
theorem hasDerivAt_toLp_snd (x y : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (!₂[x, y] : 𝔼₂)) (EuclideanSpace.single 1 1) y := by
  have : (fun y : ℝ ↦ (!₂[x, y] : 𝔼₂)) = fun y ↦ !₂[x, 0] + y • EuclideanSpace.single 1 1 := by
    funext y; ext i; fin_cases i <;> simp
  rw [this]
  simpa using ((hasDerivAt_id y).smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))).const_add
    (!₂[x, 0] : 𝔼₂)

/-- The horizontal line `x ↦ !₂[x, y]` has derivative `e₀`. -/
theorem hasDerivAt_toLp_fst (x y : ℝ) :
    HasDerivAt (fun x : ℝ ↦ (!₂[x, y] : 𝔼₂)) (EuclideanSpace.single 0 1) x := by
  have : (fun x : ℝ ↦ (!₂[x, y] : 𝔼₂)) = fun x ↦ !₂[0, y] + x • EuclideanSpace.single 0 1 := by
    funext x; ext i; fin_cases i <;> simp
  rw [this]
  simpa using ((hasDerivAt_id x).smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).const_add
    (!₂[0, y] : 𝔼₂)

/-- The derivative of a function of class `C¹(s̄)` is bounded on a bounded set `s` (it extends
continuously to the compact closure). General lemma; belongs in
`Numlib/Analysis/Calculus/ContDiffOnClosure.lean`. -/
theorem _root_.ContDiffOnClosure.exists_norm_fderiv_le {𝕜 X F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [ProperSpace X] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : X → F} {s : Set X}
    (hf : ContDiffOnClosure 𝕜 1 f s) (hs : Bornology.IsBounded s) :
    ∃ C, ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ C := by
  obtain ⟨-, -, g', hg'c, hg'e⟩ := contDiffOnClosure_one_iff.1 hf
  obtain ⟨C, hC⟩ := hs.isCompact_closure.exists_bound_of_continuousOn hg'c
  exact ⟨C, fun x hx ↦ by rw [← hg'e hx]; exact hC x (subset_closure hx)⟩

/-- The partial derivatives `z ↦ ∂ⱼFᵢ(z)` are measurable (no differentiability assumed). -/
theorem measurable_fderiv_apply_apply {N : ℕ}
    (F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    Measurable fun z ↦ fderiv ℝ F z v i :=
  (EuclideanSpace.proj i).continuous.measurable.comp
    ((measurable_fderiv ℝ F).apply_continuousLinearMap v)

/-- A partial derivative is bounded by the operator norm of the derivative. -/
theorem norm_fderiv_apply_apply_le {N : ℕ}
    {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {z : EuclideanSpace ℝ (Fin N)} {C : ℝ} (hC : ‖fderiv ℝ F z‖ ≤ C) (i j : Fin N) :
    ‖fderiv ℝ F z (EuclideanSpace.single i 1) j‖ ≤ C :=
  calc ‖fderiv ℝ F z (EuclideanSpace.single i 1) j‖
      ≤ ‖fderiv ℝ F z (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖fderiv ℝ F z‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C := by simpa using hC

/-- The partial derivatives of a `C¹(s̄)` field are integrable on a bounded measurable `s`. -/
theorem integrableOn_fderiv_apply_apply {N : ℕ}
    {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {s : Set (EuclideanSpace ℝ (Fin N))}
    (hF : ContDiffOnClosure ℝ 1 F s) (hs : Bornology.IsBounded s) (hsm : MeasurableSet s)
    (i j : Fin N) : IntegrableOn (fun z ↦ fderiv ℝ F z (EuclideanSpace.single i 1) j) s := by
  obtain ⟨C, hC⟩ := hF.exists_norm_fderiv_le hs
  refine Measure.integrableOn_of_bounded (M := C) hs.measure_lt_top.ne
    (measurable_fderiv_apply_apply F _ j).aestronglyMeasurable ?_
  rw [ae_restrict_iff' hsm]
  exact Filter.Eventually.of_forall fun z hz ↦ norm_fderiv_apply_apply_le (hC z hz) i j

/-- The divergence of a `C¹(s̄)` field is integrable on a bounded measurable `s`. -/
theorem integrableOn_div {N : ℕ}
    {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {s : Set (EuclideanSpace ℝ (Fin N))}
    (hF : ContDiffOnClosure ℝ 1 F s) (hs : Bornology.IsBounded s) (hsm : MeasurableSet s) :
    IntegrableOn (div F) s := by
  have : div F = fun z ↦ ∑ i, fderiv ℝ F z (EuclideanSpace.single i 1) i := rfl
  rw [this]
  exact integrable_finsetSum _ fun i _ ↦ integrableOn_fderiv_apply_apply hF hs hsm i i

/-- The divergence in the plane: `div F = ∂₀F₀ + ∂₁F₁`. -/
theorem div_eq_two (F : 𝔼₂ → 𝔼₂) (z : 𝔼₂) :
    div F z = fderiv ℝ F z (EuclideanSpace.single 0 1) 0
      + fderiv ℝ F z (EuclideanSpace.single 1 1) 1 := by
  simp [div, Fin.sum_univ_two]

/-- Membership of the reference triangle, in coordinates. -/
theorem mem_referenceTriangle_toLp {x y : ℝ} :
    (!₂[x, y] : 𝔼₂) ∈ (referenceTriangle : Set 𝔼₂) ↔ 0 < x ∧ 0 < y ∧ x + y < 1 := Iff.rfl

/-- Membership of the closed reference triangle, in coordinates. -/
theorem mem_closedReferenceTriangle_toLp {x y : ℝ} :
    (!₂[x, y] : 𝔼₂) ∈ closedReferenceTriangle ↔ 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 := Iff.rfl

/-- **The fundamental theorem of calculus on a vertical slice of the reference triangle**:
`∫_0^{1−x} ∂₁F₁(x, y) dy = F₁(x, 1 − x) − F₁(x, 0)` for `0 < x < 1`. -/
theorem integral_fderiv_snd {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F closedReferenceTriangle)
    (hF' : ContDiffOnClosure ℝ 1 F referenceTriangle) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ y in (0 : ℝ)..(1 - x), fderiv ℝ F !₂[x, y] (EuclideanSpace.single 1 1) 1
      = F !₂[x, 1 - x] 1 - F !₂[x, 0] 1 := by
  obtain ⟨C, hC⟩ := hF'.exists_norm_fderiv_le isBounded_referenceTriangle
  have hcont : Continuous fun y : ℝ ↦ (!₂[x, y] : 𝔼₂) :=
    continuous_toLp₂ continuous_const continuous_id
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun y ↦ F !₂[x, y] 1)
    (by linarith [hx.2]) ?_ ?_ ?_
  · refine (EuclideanSpace.proj (1 : Fin 2)).continuous.comp_continuousOn
      (hF.comp hcont.continuousOn fun y hy ↦ ?_)
    exact mem_closedReferenceTriangle_toLp.2 ⟨hx.1.le, hy.1, by linarith [hy.2]⟩
  · intro y hy
    have hmem : (!₂[x, y] : 𝔼₂) ∈ (referenceTriangle : Set 𝔼₂) :=
      mem_referenceTriangle_toLp.2 ⟨hx.1, hy.1, by linarith [hy.2]⟩
    have hd : DifferentiableAt ℝ F !₂[x, y] :=
      (hF'.contDiffOn.differentiableOn one_ne_zero).differentiableAt
        (referenceTriangle.isOpen.mem_nhds hmem)
    exact (EuclideanSpace.proj (1 : Fin 2)).hasFDerivAt.comp_hasDerivAt y
      (hd.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_toLp_snd x y))
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [hx.2])]
    refine Measure.integrableOn_of_bounded (M := C) (by simp)
      ((measurable_fderiv_apply_apply F _ 1).comp hcont.measurable).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun y hy ↦ ?_
    exact norm_fderiv_apply_apply_le
      (hC _ (mem_referenceTriangle_toLp.2 ⟨hx.1, hy.1, by linarith [hy.2]⟩)) 1 1

/-- **The fundamental theorem of calculus on a horizontal slice of the reference triangle**:
`∫_0^{1−y} ∂₀F₀(x, y) dx = F₀(1 − y, y) − F₀(0, y)` for `0 < y < 1`. -/
theorem integral_fderiv_fst {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F closedReferenceTriangle)
    (hF' : ContDiffOnClosure ℝ 1 F referenceTriangle) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..(1 - y), fderiv ℝ F !₂[x, y] (EuclideanSpace.single 0 1) 0
      = F !₂[1 - y, y] 0 - F !₂[0, y] 0 := by
  obtain ⟨C, hC⟩ := hF'.exists_norm_fderiv_le isBounded_referenceTriangle
  have hcont : Continuous fun x : ℝ ↦ (!₂[x, y] : 𝔼₂) :=
    continuous_toLp₂ continuous_id continuous_const
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun x ↦ F !₂[x, y] 0)
    (by linarith [hy.2]) ?_ ?_ ?_
  · refine (EuclideanSpace.proj (0 : Fin 2)).continuous.comp_continuousOn
      (hF.comp hcont.continuousOn fun x hx ↦ ?_)
    exact mem_closedReferenceTriangle_toLp.2 ⟨hx.1, hy.1.le, by linarith [hx.2]⟩
  · intro x hx
    have hmem : (!₂[x, y] : 𝔼₂) ∈ (referenceTriangle : Set 𝔼₂) :=
      mem_referenceTriangle_toLp.2 ⟨hx.1, hy.1, by linarith [hx.2]⟩
    have hd : DifferentiableAt ℝ F !₂[x, y] :=
      (hF'.contDiffOn.differentiableOn one_ne_zero).differentiableAt
        (referenceTriangle.isOpen.mem_nhds hmem)
    exact (EuclideanSpace.proj (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt x
      (hd.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_toLp_fst x y))
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [hy.2])]
    refine Measure.integrableOn_of_bounded (M := C) (by simp)
      ((measurable_fderiv_apply_apply F _ 0).comp hcont.measurable).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun x hx ↦ ?_
    exact norm_fderiv_apply_apply_le
      (hC _ (mem_referenceTriangle_toLp.2 ⟨hx.1, hy.1, by linarith [hx.2]⟩)) 0 0

/-- A coordinate of `F` along a continuous curve in the closed reference triangle is interval
integrable on `[0, 1]`. -/
theorem intervalIntegrable_comp_toLp {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F closedReferenceTriangle)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t ∧ 0 ≤ g t ∧ f t + g t ≤ 1) (i : Fin 2) :
    IntervalIntegrable (fun t ↦ F !₂[f t, g t] i) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  exact (EuclideanSpace.proj i).continuous.comp_continuousOn
    (hF.comp (continuous_toLp₂ hf hg).continuousOn fun t ht ↦
      mem_closedReferenceTriangle_toLp.2 (h t ht))

/-- The reparametrization `t ↦ 1 − t` of `[0, 1]`. -/
theorem integral_comp_one_sub (g : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1, g (1 - t) = ∫ t in (0 : ℝ)..1, g t := by
  have := intervalIntegral.integral_comp_sub_left g (a := 0) (b := 1) 1
  simp only [sub_zero, sub_self] at this
  exact this

/-- **The divergence theorem on the reference triangle, in parametrized form**: for `F` continuous
on the closed reference triangle and of class `C¹` up to the boundary inside,
`∫_T̂ div F = ∫_0^1 (F₀ + F₁)(t, 1 − t) dt − ∫_0^1 F₁(t, 0) dt − ∫_0^1 F₀(0, t) dt` — the edge
terms `∫_e ⟪F, ν⟫ ds` of the hypotenuse (`ν = (1, 1)/√2`, `ds = √2 dt`), the bottom (`ν = (0, −1)`)
and the left side (`ν = (−1, 0)`). Fubini on the triangle and the one-dimensional fundamental
theorem of calculus on each slice. -/
theorem integral_div_referenceTriangle {F : 𝔼₂ → 𝔼₂}
    (hF : ContinuousOn F closedReferenceTriangle)
    (hF' : ContDiffOnClosure ℝ 1 F referenceTriangle) :
    ∫ x in (referenceTriangle : Set 𝔼₂), div F x
      = (∫ t in (0 : ℝ)..1, (F !₂[t, 1 - t] 0 + F !₂[t, 1 - t] 1))
        - (∫ t in (0 : ℝ)..1, F !₂[t, 0] 1) - ∫ t in (0 : ℝ)..1, F !₂[0, t] 0 := by
  have hsm : MeasurableSet (referenceTriangle : Set 𝔼₂) := referenceTriangle.isOpen.measurableSet
  have h0 := integrableOn_fderiv_apply_apply hF' isBounded_referenceTriangle hsm 0 0
  have h1 := integrableOn_fderiv_apply_apply hF' isBounded_referenceTriangle hsm 1 1
  simp_rw [div_eq_two]
  rw [integral_add h0 h1, integral_referenceTriangle_eq' h0, integral_referenceTriangle_eq h1]
  have e0 : ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..(1 - y),
      fderiv ℝ F !₂[x, y] (EuclideanSpace.single 0 1) 0
      = ∫ y in (0 : ℝ)..1, (F !₂[1 - y, y] 0 - F !₂[0, y] 0) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun y hy ↦ integral_fderiv_fst hF hF' hy
  have e1 : ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x),
      fderiv ℝ F !₂[x, y] (EuclideanSpace.single 1 1) 1
      = ∫ x in (0 : ℝ)..1, (F !₂[x, 1 - x] 1 - F !₂[x, 0] 1) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ integral_fderiv_snd hF hF' hx
  have c1 : IntervalIntegrable (fun y ↦ F !₂[1 - y, y] 0) volume 0 1 :=
    intervalIntegrable_comp_toLp hF (by fun_prop) continuous_id
      (fun t ht ↦ ⟨by linarith [ht.2], ht.1, by simp⟩) 0
  have c2 : IntervalIntegrable (fun y ↦ F !₂[0, y] 0) volume 0 1 :=
    intervalIntegrable_comp_toLp hF continuous_const continuous_id
      (fun t ht ↦ ⟨le_rfl, ht.1, by simp [ht.2]⟩) 0
  have c3 : IntervalIntegrable (fun x ↦ F !₂[x, 1 - x] 1) volume 0 1 :=
    intervalIntegrable_comp_toLp hF continuous_id (by fun_prop)
      (fun t ht ↦ ⟨ht.1, by linarith [ht.2], by simp⟩) 1
  have c4 : IntervalIntegrable (fun x ↦ F !₂[x, 0] 1) volume 0 1 :=
    intervalIntegrable_comp_toLp hF continuous_id continuous_const
      (fun t ht ↦ ⟨ht.1, le_rfl, by simp [ht.2]⟩) 1
  have c5 : IntervalIntegrable (fun x ↦ F !₂[x, 1 - x] 0) volume 0 1 :=
    intervalIntegrable_comp_toLp hF continuous_id (by fun_prop)
      (fun t ht ↦ ⟨ht.1, by linarith [ht.2], by simp⟩) 0
  have e2 : ∫ y in (0 : ℝ)..1, F !₂[1 - y, y] 0 = ∫ t in (0 : ℝ)..1, F !₂[t, 1 - t] 0 := by
    rw [← integral_comp_one_sub (fun t ↦ F !₂[t, 1 - t] 0)]
    simp only [sub_sub_cancel]
  rw [e0, e1, intervalIntegral.integral_sub c1 c2, intervalIntegral.integral_sub c3 c4, e2,
    intervalIntegral.integral_add c5 c3]
  ring

/-- The vertices of the reference triangle are not collinear. -/
theorem linearIndependent_referenceTriangleVertex :
    LinearIndependent ℝ ![referenceTriangleVertex 1 - referenceTriangleVertex 0,
      referenceTriangleVertex 2 - referenceTriangleVertex 0] := by
  rw [linearIndependent_pair_iff_inner_perp_ne_zero, inner_perp_eq]
  simp [referenceTriangleVertex]

/-- The affine map of the reference vertices is the identity. -/
theorem triangleAffine_referenceTriangleVertex_eq_id :
    triangleAffine (referenceTriangleVertex 0) (referenceTriangleVertex 1)
      (referenceTriangleVertex 2) = id := by
  funext x
  ext i
  fin_cases i <;> simp [triangleAffine, referenceTriangleVertex]

/-- The closed triangle of the reference vertices is the closed reference triangle. -/
theorem closedTriangle_referenceTriangleVertex :
    closedTriangle (referenceTriangleVertex 0) (referenceTriangleVertex 1)
      (referenceTriangleVertex 2) = closedReferenceTriangle := by
  rw [closedTriangle, triangleAffine_referenceTriangleVertex_eq_id, image_id]

/-- The open triangle of the reference vertices is the reference triangle. -/
theorem openTriangle_referenceTriangleVertex :
    openTriangle (referenceTriangleVertex 0) (referenceTriangleVertex 1)
      (referenceTriangleVertex 2) = referenceTriangle := by
  rw [openTriangle_eq_image_triangleAffine, triangleAffine_referenceTriangleVertex_eq_id, image_id]

/-- The bottom edge of the reference triangle, parametrized. -/
theorem lineMap_referenceTriangleVertex₀₁ (t : ℝ) :
    AffineMap.lineMap (referenceTriangleVertex 0) (referenceTriangleVertex 1) t = !₂[t, 0] := by
  ext i; fin_cases i <;> simp [lineMap_eq, referenceTriangleVertex]

/-- The hypotenuse of the reference triangle, parametrized. -/
theorem lineMap_referenceTriangleVertex₁₂ (t : ℝ) :
    AffineMap.lineMap (referenceTriangleVertex 1) (referenceTriangleVertex 2) t
      = !₂[1 - t, t] := by
  ext i; fin_cases i
  · simp [lineMap_eq, referenceTriangleVertex]; ring
  · simp [lineMap_eq, referenceTriangleVertex]

/-- The left edge of the reference triangle, parametrized. -/
theorem lineMap_referenceTriangleVertex₂₀ (t : ℝ) :
    AffineMap.lineMap (referenceTriangleVertex 2) (referenceTriangleVertex 0) t
      = !₂[0, 1 - t] := by
  ext i; fin_cases i
  · simp [lineMap_eq, referenceTriangleVertex]
  · simp [lineMap_eq, referenceTriangleVertex]; ring

/-- **The divergence theorem on the reference triangle, in measure form**: with the vertices
`v₀ = (0, 0)`, `v₁ = (1, 0)`, `v₂ = (0, 1)`,
`∫_T̂ div F = ∫ ⟪F, triangleNormal v₀ v₁ v₂⟫ d(triangleBoundaryMeasure v₀ v₁ v₂)`. -/
theorem integral_div_referenceTriangle_eq_integral_inner {F : 𝔼₂ → 𝔼₂}
    (hF : ContinuousOn F closedReferenceTriangle)
    (hF' : ContDiffOnClosure ℝ 1 F referenceTriangle) :
    ∫ x in (referenceTriangle : Set 𝔼₂), div F x
      = ∫ x, ⟪F x, triangleNormal (referenceTriangleVertex 0) (referenceTriangleVertex 1)
          (referenceTriangleVertex 2) x⟫_ℝ
        ∂triangleBoundaryMeasure (referenceTriangleVertex 0) (referenceTriangleVertex 1)
          (referenceTriangleVertex 2) := by
  have hli := linearIndependent_referenceTriangleVertex
  have hF₀ : ContinuousOn F (closedTriangle (referenceTriangleVertex 0)
      (referenceTriangleVertex 1) (referenceTriangleVertex 2)) := by
    rwa [closedTriangle_referenceTriangleVertex]
  have h01 : ⟪perp (referenceTriangleVertex 1 - referenceTriangleVertex 0),
      referenceTriangleVertex 2 - referenceTriangleVertex 0⟫_ℝ < 0 := by
    rw [inner_perp_eq]; simp [referenceTriangleVertex]
  have h12 : ⟪perp (referenceTriangleVertex 2 - referenceTriangleVertex 1),
      referenceTriangleVertex 0 - referenceTriangleVertex 1⟫_ℝ < 0 := by
    rw [inner_perp_eq]; simp [referenceTriangleVertex]
  have h20 : ⟪perp (referenceTriangleVertex 0 - referenceTriangleVertex 2),
      referenceTriangleVertex 1 - referenceTriangleVertex 2⟫_ℝ < 0 := by
    rw [inner_perp_eq]; simp [referenceTriangleVertex]
  rw [integral_inner_triangleNormal hli hF₀, integral_div_referenceTriangle hF hF',
    integral_inner_edgeNormal_of_neg h01 (hF₀.mono (segment_subset_closedTriangle _ _ _ 0 1)),
    integral_inner_edgeNormal_of_neg h12 (hF₀.mono (segment_subset_closedTriangle _ _ _ 1 2)),
    integral_inner_edgeNormal_of_neg h20 (hF₀.mono (segment_subset_closedTriangle _ _ _ 2 0))]
  simp only [lineMap_referenceTriangleVertex₀₁, lineMap_referenceTriangleVertex₁₂,
    lineMap_referenceTriangleVertex₂₀, inner_perp_eq]
  simp only [referenceTriangleVertex, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.sub_apply, sub_zero, zero_sub,
    zero_mul, one_mul, neg_mul, sub_neg_eq_add, sub_self]
  have e1 : ∫ t in (0 : ℝ)..1, (F !₂[1 - t, t] 0 + F !₂[1 - t, t] 1)
      = ∫ t in (0 : ℝ)..1, (F !₂[t, 1 - t] 0 + F !₂[t, 1 - t] 1) := by
    rw [← integral_comp_one_sub (fun t ↦ F !₂[t, 1 - t] 0 + F !₂[t, 1 - t] 1)]
    simp only [sub_sub_cancel]
  have e2 : ∫ t in (0 : ℝ)..1, -F !₂[0, 1 - t] 0 = -∫ t in (0 : ℝ)..1, F !₂[0, t] 0 := by
    rw [intervalIntegral.integral_neg, ← integral_comp_one_sub (fun t ↦ F !₂[0, t] 0)]
  rw [e1, e2, intervalIntegral.integral_neg]
  ring

/-! ### The divergence theorem on a triangle -/

/-- **`C¹(s̄)` is stable under conjugation by an affine bijection and a linear map**: for `s` open
and `f ∈ C¹(s̄)`, the field `x ↦ L (f (M x + b))` is of class `C¹` up to the boundary on the
preimage of `s` under `x ↦ M x + b`. General lemma; belongs in
`Numlib/Analysis/Calculus/ContDiffOnClosure.lean`. -/
theorem _root_.ContDiffOnClosure.clm_comp_comp_affine {𝕜 X Y F G : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {f : X → F} {s : Set X} (hs : IsOpen s) (hf : ContDiffOnClosure 𝕜 1 f s)
    (L : F →L[𝕜] G) (M : Y ≃L[𝕜] X) (b : X) :
    ContDiffOnClosure 𝕜 1 (fun y ↦ L (f (M y + b))) ((fun y ↦ M y + b) ⁻¹' s) := by
  obtain ⟨hcd, ⟨g, hgc, hge⟩, ⟨g', hg'c, hg'e⟩⟩ := contDiffOnClosure_one_iff.1 hf
  have hΦ : Continuous fun y ↦ M y + b := M.continuous.add continuous_const
  have hΦh : (fun y ↦ M y + b) = M.toHomeomorph.trans (Homeomorph.addRight b) := by
    funext y; rfl
  have hcl : closure ((fun y ↦ M y + b) ⁻¹' s) = (fun y ↦ M y + b) ⁻¹' closure s := by
    rw [hΦh, Homeomorph.preimage_closure]
  refine contDiffOnClosure_one_iff.2 ⟨?_, ⟨fun y ↦ L (g (M y + b)), ?_, fun y hy ↦ ?_⟩,
    ⟨fun y ↦ (L.comp (g' (M y + b))).comp (M : Y →L[𝕜] X), ?_, fun y hy ↦ ?_⟩⟩
  · exact L.contDiff.comp_contDiffOn
      (hcd.comp (M.contDiff.add contDiff_const).contDiffOn (mapsTo_preimage _ _))
  · rw [hcl]
    exact L.continuous.comp_continuousOn (hgc.comp hΦ.continuousOn (mapsTo_preimage _ _))
  · simp only [hge hy]
  · rw [hcl]
    exact (continuousOn_const.clm_comp (hg'c.comp hΦ.continuousOn
      (mapsTo_preimage _ _))).clm_comp continuousOn_const
  · have hd : DifferentiableAt 𝕜 f (M y + b) :=
      (hcd.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hy)
    simp only [hg'e hy]
    exact (L.hasFDerivAt.comp y (hd.hasFDerivAt.comp y (M.hasFDerivAt.add_const b))).fderiv.symm

/-- **The divergence theorem on a triangle**: for non-collinear `A, B, C` and a field `F`
continuous on the closed triangle and of class `C¹` up to the boundary on the open one,
`∫_{ABC} div F = ∫ ⟪F, triangleNormal A B C⟫ d(triangleBoundaryMeasure A B C)`. Affine transport
from the reference triangle: with `M := triangleEquiv A B C h` and `Φ x̂ = M x̂ + A`, the change of
variables gives `|det M| ∫_T̂ div F ∘ Φ`, the Piola identity `div_comp_continuousLinearEquiv`
turns the integrand into `div (M⁻¹ ∘ F ∘ Φ)`, the reference theorem applies to this field, and
`integral_inner_edgeNormal_affine` carries each edge term back. -/
theorem integral_div_openTriangle {A B C : 𝔼₂} (h : LinearIndependent ℝ ![B - A, C - A])
    {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F (closedTriangle A B C))
    (hF' : ContDiffOnClosure ℝ 1 F (openTriangle A B C)) :
    ∫ x in openTriangle A B C, div F x
      = ∫ x, ⟪F x, triangleNormal A B C x⟫_ℝ ∂triangleBoundaryMeasure A B C := by
  set M := triangleEquiv A B C h with hM
  have hΦinj : Injective fun x ↦ M x + A := fun x y hxy ↦ M.injective (add_right_cancel hxy)
  have hopen : openTriangle A B C = (fun x ↦ M x + A) '' referenceTriangle :=
    openTriangle_eq_image A B C h
  have hclosed : closedTriangle A B C = (fun x ↦ M x + A) '' closedReferenceTriangle := by
    rw [closedTriangle, triangleAffine_eq A B C h]
  have hpre : (fun x ↦ M x + A) ⁻¹' openTriangle A B C = referenceTriangle := by
    rw [hopen, preimage_image_eq _ hΦinj]
  have hv : ∀ a : Fin 3, M (referenceTriangleVertex a) + A = ![A, B, C] a := fun a ↦ by
    rw [← triangleAffine_referenceTriangleVertex, triangleAffine_eq A B C h]
  have hv0 : M (referenceTriangleVertex 0) + A = A := hv 0
  have hv1 : M (referenceTriangleVertex 1) + A = B := hv 1
  have hv2 : M (referenceTriangleVertex 2) + A = C := hv 2
  have hG : ContinuousOn (fun x ↦ M.symm (F (M x + A))) closedReferenceTriangle := by
    refine M.symm.continuous.comp_continuousOn
      (hF.comp (M.continuous.add continuous_const).continuousOn ?_)
    rw [hclosed]; exact mapsTo_image _ _
  have hG' : ContDiffOnClosure ℝ 1 (fun x ↦ M.symm (F (M x + A))) referenceTriangle := by
    rw [← hpre]
    exact hF'.clm_comp_comp_affine (isOpen_openTriangle A B C h) (M.symm : 𝔼₂ →L[ℝ] 𝔼₂) M A
  have hli := linearIndependent_referenceTriangleVertex
  have hs := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 hli
  have hs' := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (linearIndependent_rotate hli)
  have hs'' := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1
    (linearIndependent_rotate (linearIndependent_rotate hli))
  have h1 : ∫ x in openTriangle A B C, div F x
      = ∫ x in (referenceTriangle : Set 𝔼₂),
          |LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂)| • div F (M x + A) := by
    rw [hopen]
    exact integral_image_eq_integral_abs_det_fderiv_smul volume
      referenceTriangle.isOpen.measurableSet
      (fun x _ ↦ (M.hasFDerivAt.add_const A).hasFDerivWithinAt) hΦinj.injOn _
  have h2 : ∀ x ∈ (referenceTriangle : Set 𝔼₂),
      |LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂)| • div F (M x + A)
        = |LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂)|
          • div (fun z ↦ M.symm (F (M z + A))) x := fun x hx ↦ by
    have hd : DifferentiableAt ℝ F (M x + A) :=
      (hF'.contDiffOn.differentiableOn one_ne_zero).differentiableAt
        ((isOpen_openTriangle A B C h).mem_nhds (by rw [hopen]; exact ⟨x, hx, rfl⟩))
    rw [div_comp_continuousLinearEquiv M A hd]
  have hF01 : ContinuousOn F (segment ℝ (M (referenceTriangleVertex 0) + A)
      (M (referenceTriangleVertex 1) + A)) := by
    rw [hv0, hv1]; exact hF.mono (segment_subset_closedTriangle A B C 0 1)
  have hF12 : ContinuousOn F (segment ℝ (M (referenceTriangleVertex 1) + A)
      (M (referenceTriangleVertex 2) + A)) := by
    rw [hv1, hv2]; exact hF.mono (segment_subset_closedTriangle A B C 1 2)
  have hF20 : ContinuousOn F (segment ℝ (M (referenceTriangleVertex 2) + A)
      (M (referenceTriangleVertex 0) + A)) := by
    rw [hv2, hv0]; exact hF.mono (segment_subset_closedTriangle A B C 2 0)
  rw [h1, setIntegral_congr_fun referenceTriangle.isOpen.measurableSet h2, integral_smul,
    smul_eq_mul, integral_div_referenceTriangle_eq_integral_inner hG hG',
    integral_inner_triangleNormal hli (by rwa [closedTriangle_referenceTriangleVertex]),
    integral_inner_triangleNormal h hF, mul_add, mul_add,
    integral_inner_edgeNormal_affine M A hs hF01, integral_inner_edgeNormal_affine M A hs' hF12,
    integral_inner_edgeNormal_affine M A hs'' hF20, hv0, hv1, hv2]

/-- **A triangle is a `BoundaryData`**: the open triangle with non-collinear vertices `A, B, C`,
with the boundary measure `triangleBoundaryMeasure A B C` and the normal `triangleNormal A B C`.
-/
def triangleBoundaryData (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    BoundaryData (openTriangleOpens A B C h) where
  σ := triangleBoundaryMeasure A B C
  ν := triangleNormal A B C
  isBounded := isBounded_openTriangle A B C
  isFiniteMeasure := inferInstance
  measure_compl_frontier := triangleBoundaryMeasure_compl_frontier h
  aestronglyMeasurable_ν := aestronglyMeasurable_triangleNormal h
  ae_norm_ν := ae_norm_triangleNormal h
  integral_div_eq F hF hF' := integral_div_openTriangle h
    (by rwa [coe_openTriangleOpens, closure_openTriangle] at hF) hF'

@[simp] theorem triangleBoundaryData_σ (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    (triangleBoundaryData A B C h).σ = triangleBoundaryMeasure A B C := rfl

@[simp] theorem triangleBoundaryData_ν (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    (triangleBoundaryData A B C h).ν = triangleNormal A B C := rfl

end EuclideanSpace

/-! ### Triangulations: boundary edges and partners -/

namespace Triangulation

open EuclideanSpace

variable {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)

/-- **A boundary edge of a triangulation**: the edge `[T a, T (a + 1)]` of the element `T` is a
boundary edge when no other element has both its endpoints as vertices. -/
def IsBoundaryEdge (T : 𝒯.elems) (a : Fin 3) : Prop :=
  ∀ T' : 𝒯.elems, T' ≠ T → ∀ i j : Fin 3, ¬ (T.1 a = T'.1 i ∧ T.1 (a + 1) = T'.1 j)

/-- **The partner of an edge**: the edge `a'` of another element `T'` is the same segment as the
edge `a` of `T`, in the same or in the reversed orientation. -/
def IsPartner (T : 𝒯.elems) (a : Fin 3) (T' : 𝒯.elems) (a' : Fin 3) : Prop :=
  T' ≠ T ∧ ((T.1 a = T'.1 a' ∧ T.1 (a + 1) = T'.1 (a' + 1)) ∨
    (T.1 a = T'.1 (a' + 1) ∧ T.1 (a + 1) = T'.1 a'))

open Classical in
/-- The boundary edges of the triangulation, as pairs `(T, a)`. -/
def boundaryEdges : Finset (𝒯.elems × Fin 3) :=
  Finset.univ.filter fun e ↦ 𝒯.IsBoundaryEdge e.1 e.2

variable {𝒯}

/-- Membership of `boundaryEdges`. -/
theorem mem_boundaryEdges {e : 𝒯.elems × Fin 3} :
    e ∈ 𝒯.boundaryEdges ↔ 𝒯.IsBoundaryEdge e.1 e.2 := by
  classical
  simp [boundaryEdges]

/-- The vertices of an element are distinct. -/
theorem vertex_injective (T : 𝒯.elems) : Function.Injective T.1 :=
  EuclideanSpace.vertex_injective (𝒯.li T)

/-- Non-collinearity of the vertices of an element, read from the vertex `a`. -/
theorem li_rot (T : 𝒯.elems) (a : Fin 3) :
    LinearIndependent ℝ ![T.1 (a + 1) - T.1 a, T.1 (a + 2) - T.1 a] :=
  linearIndependent_rot (𝒯.li T) a

/-- The open element, read from the vertex `a`. -/
theorem K_eq_rot (T : 𝒯.elems) (a : Fin 3) :
    𝒯.K T = openTriangle (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) :=
  openTriangle_eq_rot T.1 a

/-- The closed element, read from the vertex `a`. -/
theorem closedK_eq_rot (T : 𝒯.elems) (a : Fin 3) :
    𝒯.closedK T = closedTriangle (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) :=
  closedTriangle_eq_rot T.1 a

/-- The endpoints of an edge are distinct. -/
theorem vertex_ne_vertex_add_one (T : 𝒯.elems) (a : Fin 3) : T.1 a ≠ T.1 (a + 1) :=
  fun e ↦ fin3_ne_add_one a (vertex_injective T e)

/-- The vertex `T c`, read in the triple starting at the vertex `a`. -/
theorem vertex_eq_vecCons_rot (T : 𝒯.elems) (a c : Fin 3) :
    T.1 c = ![T.1 a, T.1 (a + 1), T.1 (a + 2)] (c - a) := by
  rw [vecCons_rot, add_sub_cancel]

/-- The partner relation is symmetric. -/
theorem IsPartner.symm {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    𝒯.IsPartner T' a' T a := by
  obtain ⟨hne, h | h⟩ := h
  · exact ⟨hne.symm, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
  · exact ⟨hne.symm, Or.inr ⟨h.2.symm, h.1.symm⟩⟩

/-- An edge is not a boundary edge iff it has a partner. -/
theorem not_isBoundaryEdge_iff_exists_partner (T : 𝒯.elems) (a : Fin 3) :
    ¬ 𝒯.IsBoundaryEdge T a ↔ ∃ T' a', 𝒯.IsPartner T a T' a' := by
  constructor
  · intro h
    simp only [IsBoundaryEdge, not_forall, not_not] at h
    obtain ⟨T', hT', i, j, hi, hj⟩ := h
    have hij : i ≠ j := by
      rintro rfl
      exact fin3_ne_add_one a (vertex_injective T (hi.trans hj.symm))
    obtain ⟨a', h | h⟩ := exists_fin3_of_ne hij
    · exact ⟨T', a', hT', Or.inl ⟨h.1 ▸ hi, h.2 ▸ hj⟩⟩
    · exact ⟨T', a', hT', Or.inr ⟨h.1 ▸ hi, h.2 ▸ hj⟩⟩
  · rintro ⟨T', a', hne, h | h⟩ hb
    · exact hb T' hne a' (a' + 1) h
    · exact hb T' hne (a' + 1) a' h

/-- An edge with a partner is not a boundary edge. -/
theorem IsPartner.not_isBoundaryEdge {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') : ¬ 𝒯.IsBoundaryEdge T a :=
  (not_isBoundaryEdge_iff_exists_partner T a).2 ⟨T', a', h⟩

/-- The triangle of the partner, on the edge of `T`, is nondegenerate. -/
theorem IsPartner.li {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    LinearIndependent ℝ ![T.1 (a + 1) - T.1 a, T'.1 (a' + 2) - T.1 a] := by
  have hli' := 𝒯.li_rot T' a'
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rwa [← h1, ← h2] at hli'
  · rw [← h1, ← h2] at hli'
    exact linearIndependent_swap hli'

/-- The open element of the partner, as the triangle on the edge of `T` with the partner's
third vertex. -/
theorem IsPartner.K_eq {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    𝒯.K T' = openTriangle (T.1 a) (T.1 (a + 1)) (T'.1 (a' + 2)) := by
  rw [K_eq_rot T' a']
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [h1, h2]
  · rw [h1, h2, openTriangle_swap]

/-- **The partner lies on the other side of the edge**: the third vertices of an edge and of its
partner lie strictly on opposite sides of the line through the edge (two triangles on the same
side would overlap, against the disjointness of the open elements). -/
theorem IsPartner.inner_perp_mul_neg {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') :
    ⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ
      * ⟪perp (T.1 (a + 1) - T.1 a), T'.1 (a' + 2) - T.1 a⟫_ℝ < 0 := by
  have hdisj := 𝒯.pairwise_disjoint_K h.1.symm
  rw [onFun, K_eq_rot T a, h.K_eq] at hdisj
  have hs := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (𝒯.li_rot T a)
  have hs' := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 h.li
  by_contra hcon
  have hpos := lt_of_le_of_ne (not_lt.1 hcon) (mul_ne_zero hs hs').symm
  obtain ⟨x, hx, hx'⟩ := openTriangle_inter_nonempty_of_same_side hpos
  exact Set.disjoint_left.1 hdisj hx hx'

/-- **The partner of an interior edge is unique.** Two partners lie on the far side of the edge
from `T`, hence on the same side of it, hence coincide; the edge index is then determined by the
injectivity of the vertex triple. -/
theorem partner_unique {T T' T'' : 𝒯.elems} {a a' a'' : Fin 3} (h : 𝒯.IsPartner T a T' a')
    (h' : 𝒯.IsPartner T a T'' a'') : T'' = T' ∧ a'' = a' := by
  have hTT : T'' = T' := by
    by_contra hne
    have hdisj := 𝒯.pairwise_disjoint_K hne
    rw [onFun, h'.K_eq, h.K_eq] at hdisj
    have h1 := h.inner_perp_mul_neg
    have h2 := h'.inner_perp_mul_neg
    have hs : 0 < ⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ
        * ⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ :=
      mul_self_pos.2 ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (𝒯.li_rot T a))
    have h12 := mul_pos_of_neg_of_neg h2 h1
    have e : ⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ
        * ⟪perp (T.1 (a + 1) - T.1 a), T''.1 (a'' + 2) - T.1 a⟫_ℝ
        * (⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ
        * ⟪perp (T.1 (a + 1) - T.1 a), T'.1 (a' + 2) - T.1 a⟫_ℝ)
        = (⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ
        * ⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ)
        * (⟪perp (T.1 (a + 1) - T.1 a), T''.1 (a'' + 2) - T.1 a⟫_ℝ
        * ⟪perp (T.1 (a + 1) - T.1 a), T'.1 (a' + 2) - T.1 a⟫_ℝ) := by ring
    rw [e] at h12
    have hpos := (pos_iff_pos_of_mul_pos h12).1 hs
    obtain ⟨x, hx, hx'⟩ := openTriangle_inter_nonempty_of_same_side hpos
    exact Set.disjoint_left.1 hdisj hx hx'
  subst hTT
  refine ⟨rfl, ?_⟩
  have hinj := vertex_injective T''
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h <;> obtain ⟨-, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ := h'
  · exact hinj (h3.symm.trans h1)
  · have e1 := hinj (h3.symm.trans h1)
    have e2 := hinj (h4.symm.trans h2)
    clear h1 h2 h3 h4 hinj
    revert e1 e2; revert a' a''; decide
  · have e1 := hinj (h3.symm.trans h1)
    have e2 := hinj (h4.symm.trans h2)
    clear h1 h2 h3 h4 hinj
    revert e1 e2; revert a' a''; decide
  · have e1 := hinj (h3.symm.trans h1)
    clear h1 h2 h3 h4 hinj
    revert e1; revert a' a''; decide

/-- The partner edge carries the same arclength measure. -/
theorem IsPartner.edgeMeasure_eq {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    edgeMeasure (T'.1 a') (T'.1 (a' + 1)) = edgeMeasure (T.1 a) (T.1 (a + 1)) := by
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [← h1, ← h2]
  · rw [← h1, ← h2, edgeMeasure_symm]

/-- The partner edge carries the opposite outward normal. -/
theorem IsPartner.edgeNormal_eq {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    edgeNormal (T'.1 a') (T'.1 (a' + 1)) (T'.1 (a' + 2))
      = -edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) := by
  have hneg := h.inner_perp_mul_neg
  have hs' := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 h.li
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [← h1, ← h2]
    exact edgeNormal_eq_neg_of_mul_neg hneg
  · rw [← h1, ← h2, edgeNormal_symm hs']
    exact edgeNormal_eq_neg_of_mul_neg hneg

/-- The partner of an interior edge, chosen. -/
def partner (T : 𝒯.elems) (a : Fin 3) (h : ¬ 𝒯.IsBoundaryEdge T a) : 𝒯.elems × Fin 3 :=
  (((not_isBoundaryEdge_iff_exists_partner T a).1 h).choose,
    ((not_isBoundaryEdge_iff_exists_partner T a).1 h).choose_spec.choose)

/-- The chosen partner is a partner. -/
theorem isPartner_partner (T : 𝒯.elems) (a : Fin 3) (h : ¬ 𝒯.IsBoundaryEdge T a) :
    𝒯.IsPartner T a (partner T a h).1 (partner T a h).2 :=
  ((not_isBoundaryEdge_iff_exists_partner T a).1 h).choose_spec.choose_spec

/-! ### Boundary edges lie in the frontier -/

/-- A point of an open edge of `T` lying in another closed element makes both endpoints of the
edge vertices of that element. -/
theorem exists_eq_vertex_of_mem_closedK {T T' : 𝒯.elems} (hne : T' ≠ T) {a : Fin 3} {x : 𝔼₂}
    (hx : x ∈ openSegment ℝ (T.1 a) (T.1 (a + 1))) (hx' : x ∈ 𝒯.closedK T') :
    ∃ i j : Fin 3, T.1 a = T'.1 i ∧ T.1 (a + 1) = T'.1 j := by
  have hli := 𝒯.li_rot T a
  have hxT : x ∈ 𝒯.closedK T :=
    𝒯.segment_subset_closedK T a (a + 1) (openSegment_subset_segment ℝ _ _ hx)
  rcases 𝒯.conforming' hne.symm hxT hx' with ⟨c, d, hxc, -⟩ | ⟨c, d, c', d', hcd, hc, hd, hs⟩
  · exfalso
    rw [vertex_eq_vecCons_rot T a c] at hxc
    exact ne_vertex_of_mem_openSegment hli hx (c - a) hxc
  · rw [vertex_eq_vecCons_rot T a c, vertex_eq_vecCons_rot T a d] at hs
    have hcd' : c - a ≠ d - a := fun e ↦ hcd (sub_left_injective e)
    rcases eq_edge_of_mem_openSegment_of_mem_segment hli hx hcd' hs with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hc' : c = a := by rw [sub_eq_zero] at e1; exact e1
      have hd' : d = a + 1 := by rw [sub_eq_iff_eq_add] at e2; rw [e2, add_comm]
      subst hc' hd'
      exact ⟨c', d', hc, hd⟩
    · have hc' : c = a + 1 := by rw [sub_eq_iff_eq_add] at e1; rw [e1, add_comm]
      have hd' : d = a := by rw [sub_eq_zero] at e2; exact e2
      subst hc' hd'
      exact ⟨d', c', hd, hc⟩

/-- **A boundary edge lies in `∂Ω`** — from the four axioms of `Triangulation` alone. A point
`x` of the open edge in `Ω` would either lie in another closed element, which then shares the
edge (`conforming'`), or have a neighbourhood in `Ω` missing every other element, hence contained
in the closed element of `T`, which the point `x − ε (R − P)` beyond the edge contradicts. -/
theorem segment_subset_frontier_of_isBoundaryEdge {T : 𝒯.elems} {a : Fin 3}
    (h : 𝒯.IsBoundaryEdge T a) :
    segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ frontier (Ω : Set 𝔼₂) := by
  rw [← closure_openSegment]
  refine closure_minimal (fun x hx ↦ ?_) isClosed_frontier
  rw [Ω.isOpen.frontier_eq]
  refine ⟨𝒯.closedK_subset_closure T
    (𝒯.segment_subset_closedK T a (a + 1) (openSegment_subset_segment ℝ _ _ hx)), fun hxΩ ↦ ?_⟩
  by_cases hC : ∃ T' : 𝒯.elems, T' ≠ T ∧ x ∈ 𝒯.closedK T'
  · obtain ⟨T', hne, hx'⟩ := hC
    obtain ⟨i, j, hi, hj⟩ := exists_eq_vertex_of_mem_closedK hne hx hx'
    exact h T' hne i j ⟨hi, hj⟩
  · simp only [not_exists, not_and] at hC
    have hCclosed : IsClosed (⋃ T' : {T' : 𝒯.elems // T' ≠ T}, 𝒯.closedK T'.1) :=
      isClosed_iUnion_of_finite fun T' ↦ 𝒯.isClosed_closedK T'.1
    have hxC : x ∉ ⋃ T' : {T' : 𝒯.elems // T' ≠ T}, 𝒯.closedK T'.1 := by
      rw [mem_iUnion, not_exists]
      exact fun T' ↦ hC T'.1 T'.2
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
      ((Ω.isOpen.inter hCclosed.isOpen_compl).mem_nhds ⟨hxΩ, hxC⟩)
    set ε := r / (2 * (‖T.1 (a + 2) - T.1 a‖ + 1)) with hε
    have hε0 : 0 < ε := by positivity
    have hy : x - ε • (T.1 (a + 2) - T.1 a) ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg hε0.le, hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (T.1 (a + 2) - T.1 a)]
    obtain ⟨hyΩ, hyC⟩ := hball hy
    obtain ⟨T'', hT''⟩ := mem_iUnion.1 (𝒯.subset_iUnion_closedK hyΩ)
    have hTT : T'' = T := by
      by_contra hne
      exact hyC (mem_iUnion.2 ⟨⟨T'', hne⟩, hT''⟩)
    subst hTT
    rw [closedK_eq_rot T'' a] at hT''
    obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
    obtain ⟨s', t', hs', ht', hst', e⟩ := mem_closedTriangle.1 hT''
    have := eq_of_affine_eq (𝒯.li_rot T'' a) (s := s) (t := -ε) (s' := s') (t' := t')
      (by rw [← e]; module)
    linarith [this.2]

/-- **Distinct boundary edges have disjoint relative interiors**: two open edges of one element
are disjoint by the barycentric coordinates, and a point of an open edge of `T` in another
element makes the edge shared. -/
theorem openSegment_disjoint_of_isBoundaryEdge {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsBoundaryEdge T a) (h' : 𝒯.IsBoundaryEdge T' a') (hne : (T, a) ≠ (T', a')) :
    Disjoint (openSegment ℝ (T.1 a) (T.1 (a + 1))) (openSegment ℝ (T'.1 a') (T'.1 (a' + 1))) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  by_cases hT : T = T'
  · subst hT
    have haa : a ≠ a' := fun e ↦ hne (by rw [e])
    have hli := 𝒯.li_rot T a
    have hs : x ∈ segment ℝ (![T.1 a, T.1 (a + 1), T.1 (a + 2)] (a' - a))
        (![T.1 a, T.1 (a + 1), T.1 (a + 2)] (a' + 1 - a)) := by
      rw [← vertex_eq_vecCons_rot, ← vertex_eq_vecCons_rot]
      exact openSegment_subset_segment ℝ _ _ hx'
    have hne' : a' - a ≠ a' + 1 - a := fun e ↦ fin3_ne_add_one a' (sub_left_injective e)
    rcases eq_edge_of_mem_openSegment_of_mem_segment hli hx hne' hs with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact haa (sub_eq_zero.1 e1).symm
    · clear hs hx hx' h h' hne hli hne' haa
      revert e1 e2; revert a a'; decide
  · have hx'' : x ∈ 𝒯.closedK T' :=
      𝒯.segment_subset_closedK T' a' (a' + 1) (openSegment_subset_segment ℝ _ _ hx')
    obtain ⟨i, j, hi, hj⟩ := exists_eq_vertex_of_mem_closedK (Ne.symm hT) hx hx''
    exact h T' (Ne.symm hT) i j ⟨hi, hj⟩

/-! ### The boundary measure and the outward normal of a triangulated domain -/

variable (𝒯)

/-- **The surface (arclength) measure of a triangulated domain**: the sum of the arclength
measures of the boundary edges. -/
def boundaryMeasure : Measure 𝔼₂ :=
  ∑ e ∈ 𝒯.boundaryEdges, edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1))

/-- The surface measure of a triangulated domain is finite. -/
instance isFiniteMeasure_boundaryMeasure : IsFiniteMeasure 𝒯.boundaryMeasure :=
  ⟨by
    rw [boundaryMeasure, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.2 fun e _ ↦ measure_lt_top _ _⟩

/-- The surface measure is carried by `∂Ω`. -/
theorem boundaryMeasure_compl_frontier : 𝒯.boundaryMeasure (frontier (Ω : Set 𝔼₂))ᶜ = 0 := by
  rw [boundaryMeasure, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun e he ↦ measure_mono_null (compl_subset_compl.2 ?_)
    (edgeMeasure_compl_segment _ _)
  exact segment_subset_frontier_of_isBoundaryEdge (mem_boundaryEdges.1 he)

/-- The integral against the surface measure is the sum of the boundary edge integrals. -/
theorem integral_boundaryMeasure {f : 𝔼₂ → ℝ}
    (hf : ∀ e ∈ 𝒯.boundaryEdges, Integrable f (edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1)))) :
    ∫ x, f x ∂𝒯.boundaryMeasure
      = ∑ e ∈ 𝒯.boundaryEdges, ∫ x, f x ∂edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1)) :=
  integral_finsetSum_measure hf

/-- An open set meeting the relative interior of a boundary edge has positive surface measure.
Unlike the `C¹` case, an open set meeting `∂Ω` only at a vertex may have surface measure zero,
so the hypothesis names an edge. -/
theorem boundaryMeasure_pos_of_isOpen {U : Set 𝔼₂} (hU : IsOpen U)
    (hne : ∃ e ∈ 𝒯.boundaryEdges, (U ∩ openSegment ℝ (e.1.1 e.2) (e.1.1 (e.2 + 1))).Nonempty) :
    0 < 𝒯.boundaryMeasure U := by
  obtain ⟨e, he, hne⟩ := hne
  have h1 : 0 < edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1)) U :=
    edgeMeasure_pos_of_isOpen (vertex_ne_vertex_add_one e.1 e.2) hU hne
  have h2 := Finset.single_le_sum_of_canonicallyOrdered
    (f := fun i ↦ edgeMeasure (i.1.1 i.2) (i.1.1 (i.2 + 1)) U) he
  rw [boundaryMeasure, Measure.finsetSum_apply]
  exact h1.trans_le h2

open Classical in
/-- **The outward unit normal of a triangulated domain**: on the relative interior of a boundary
edge, the outward edge normal of its element; `0` elsewhere (at the vertices and off `∂Ω`). -/
def outwardNormal : 𝔼₂ → 𝔼₂ := fun x ↦
  if h : ∃ e ∈ 𝒯.boundaryEdges, x ∈ openSegment ℝ (e.1.1 e.2) (e.1.1 (e.2 + 1)) then
    edgeNormal (h.choose.1.1 h.choose.2) (h.choose.1.1 (h.choose.2 + 1))
      (h.choose.1.1 (h.choose.2 + 2))
  else 0

variable {𝒯}

/-- On the relative interior of a boundary edge, the outward normal is the edge normal of its
element (the edge is determined by `openSegment_disjoint_of_isBoundaryEdge`). -/
theorem outwardNormal_eq_edgeNormal {T : 𝒯.elems} {a : Fin 3} (h : 𝒯.IsBoundaryEdge T a)
    {x : 𝔼₂} (hx : x ∈ openSegment ℝ (T.1 a) (T.1 (a + 1))) :
    𝒯.outwardNormal x = edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) := by
  classical
  have hex : ∃ e ∈ 𝒯.boundaryEdges, x ∈ openSegment ℝ (e.1.1 e.2) (e.1.1 (e.2 + 1)) :=
    ⟨(T, a), mem_boundaryEdges.2 h, hx⟩
  rw [outwardNormal, dite_eq_left hex]
  have hspec := hex.choose_spec
  have heq : hex.choose = (T, a) := by
    by_contra hne
    exact Set.disjoint_left.1 (openSegment_disjoint_of_isBoundaryEdge
      (mem_boundaryEdges.1 hspec.1) h hne) hspec.2 hx
  rw [heq]

/-- The outward normal is a unit vector almost everywhere for the surface measure. -/
theorem ae_norm_outwardNormal : ∀ᵐ x ∂𝒯.boundaryMeasure, ‖𝒯.outwardNormal x‖ = 1 := by
  rw [boundaryMeasure, ae_finsetSum_measure_iff]
  intro e he
  refine (ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)).mono fun x hx ↦ ?_
  rw [outwardNormal_eq_edgeNormal (mem_boundaryEdges.1 he) hx]
  exact norm_edgeNormal ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (𝒯.li_rot e.1 e.2))

/-- A function almost everywhere equal to a constant for each of finitely many measures is
measurable for their sum. -/
theorem _root_.MeasureTheory.aestronglyMeasurable_finsetSum_measure {α β ι : Type*}
    [MeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α → β}
    {s : Finset ι} {μ : ι → Measure α} (h : ∀ i ∈ s, AEStronglyMeasurable f (μ i)) :
    AEStronglyMeasurable f (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add_measure
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- The outward normal is measurable for the surface measure. -/
theorem aestronglyMeasurable_outwardNormal :
    AEStronglyMeasurable 𝒯.outwardNormal 𝒯.boundaryMeasure := by
  rw [boundaryMeasure]
  refine aestronglyMeasurable_finsetSum_measure fun e he ↦
    (aestronglyMeasurable_const
      (b := edgeNormal (e.1.1 e.2) (e.1.1 (e.2 + 1)) (e.1.1 (e.2 + 2)))).congr ?_
  exact (ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)).mono fun x hx ↦
    (outwardNormal_eq_edgeNormal (mem_boundaryEdges.1 he) hx).symm

/-! ### The divergence theorem on a triangulated domain -/

/-- The edge term of the divergence theorem: the flux of `F` through the edge `a` of `T`. -/
def edgeTerm (F : 𝔼₂ → 𝔼₂) (T : 𝒯.elems) (a : Fin 3) : ℝ :=
  ∫ x, ⟪F x, edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2))⟫_ℝ ∂edgeMeasure (T.1 a) (T.1 (a + 1))

/-- The edge of an element lies in the closure of the domain. -/
theorem segment_subset_closure (T : 𝒯.elems) (a b : Fin 3) :
    segment ℝ (T.1 a) (T.1 b) ⊆ closure (Ω : Set 𝔼₂) :=
  (𝒯.segment_subset_closedK T a b).trans (𝒯.closedK_subset_closure T)

/-- The flux through an edge and through its partner cancel. -/
theorem edgeTerm_add_edgeTerm_partner {F : 𝔼₂ → 𝔼₂} {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') : 𝒯.edgeTerm F T a + 𝒯.edgeTerm F T' a' = 0 := by
  unfold edgeTerm
  rw [h.edgeMeasure_eq, h.edgeNormal_eq]
  simp only [inner_neg_right, integral_neg, add_neg_cancel]

/-- **The divergence theorem on a triangle, in edge terms.** -/
theorem integral_div_K_eq_sum_edgeTerm {F : 𝔼₂ → 𝔼₂}
    (hF : ContinuousOn F (closure (Ω : Set 𝔼₂))) (hF' : ContDiffOnClosure ℝ 1 F (Ω : Set 𝔼₂))
    (T : 𝒯.elems) : ∫ x in 𝒯.K T, div F x = ∑ a : Fin 3, 𝒯.edgeTerm F T a := by
  have hFT : ContinuousOn F (closedTriangle (T.1 0) (T.1 1) (T.1 2)) :=
    hF.mono (𝒯.closedK_subset_closure T)
  rw [K, integral_div_openTriangle (𝒯.li T) hFT (hF'.mono (𝒯.K_subset T)),
    integral_inner_triangleNormal (𝒯.li T) hFT, Fin.sum_univ_three]
  rfl

open Classical in
/-- **The sum of the interior edge terms vanishes**: the map `partner` is a fixed-point-free
involution of the interior edges under which the edge term changes sign. -/
theorem sum_edgeTerm_interior_eq_zero (F : 𝔼₂ → 𝔼₂) :
    ∑ e ∈ Finset.univ.filter (fun e : 𝒯.elems × Fin 3 ↦ ¬ 𝒯.IsBoundaryEdge e.1 e.2),
      𝒯.edgeTerm F e.1 e.2 = 0 := by
  classical
  refine Finset.sum_involution (fun e he ↦ partner e.1 e.2 (Finset.mem_filter.1 he).2)
    (fun e he ↦ ?_) (fun e he _ ↦ ?_) (fun e he ↦ ?_) (fun e he ↦ ?_)
  · exact edgeTerm_add_edgeTerm_partner (isPartner_partner e.1 e.2 _)
  · intro heq
    exact (isPartner_partner e.1 e.2 (Finset.mem_filter.1 he).2).1 (congrArg Prod.fst heq)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (isPartner_partner e.1 e.2 (Finset.mem_filter.1 he).2).symm.not_isBoundaryEdge⟩
  · have he' := (Finset.mem_filter.1 he).2
    have h1 := isPartner_partner e.1 e.2 he'
    have h2 := isPartner_partner (partner e.1 e.2 he').1 (partner e.1 e.2 he').2
      h1.symm.not_isBoundaryEdge
    obtain ⟨e1, e2⟩ := partner_unique h1.symm h2
    exact Prod.ext e1 e2

/-- **The divergence theorem on a triangulated domain** (decision B6): for `F ∈ C¹(Ω̄)`,
`∫_Ω div F = ∫ ⟪F, ν⟫ dσ` with the surface measure `𝒯.boundaryMeasure` and the outward normal
`𝒯.outwardNormal`. The integral over `Ω` is the sum over the open elements (they partition `Ω` up
to a null set), each is the sum of its three edge terms (`integral_div_openTriangle`), the terms of
the interior edges cancel in pairs (`sum_edgeTerm_interior_eq_zero`), and the boundary edges make
up the surface integral. No hypothesis beyond the four axioms of `Triangulation` is needed: a slit
along an interior edge is invisible to a field continuous across it. -/
theorem integral_div_eq {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F (closure (Ω : Set 𝔼₂)))
    (hF' : ContDiffOnClosure ℝ 1 F (Ω : Set 𝔼₂)) :
    ∫ x in (Ω : Set 𝔼₂), div F x = ∫ x, ⟪F x, 𝒯.outwardNormal x⟫_ℝ ∂𝒯.boundaryMeasure := by
  classical
  have h1 : ∫ x in (Ω : Set 𝔼₂), div F x = ∑ T, ∫ x in 𝒯.K T, div F x := by
    rw [← setIntegral_congr_set 𝒯.ae_eq_iUnion_K]
    exact integral_iUnion_fintype (fun T ↦ (𝒯.isOpen_K T).measurableSet) 𝒯.pairwise_disjoint_K
      fun T ↦ (integrableOn_div hF' 𝒯.isBounded Ω.isOpen.measurableSet).mono_set (𝒯.K_subset T)
  have hint : ∀ e ∈ 𝒯.boundaryEdges, Integrable (fun x ↦ ⟪F x, 𝒯.outwardNormal x⟫_ℝ)
      (edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1))) := fun e he ↦ by
    have hc : ContinuousOn
        (fun x ↦ ⟪F x, edgeNormal (e.1.1 e.2) (e.1.1 (e.2 + 1)) (e.1.1 (e.2 + 2))⟫_ℝ)
        (segment ℝ (e.1.1 e.2) (e.1.1 (e.2 + 1))) :=
      (hF.mono (𝒯.segment_subset_closure e.1 e.2 (e.2 + 1))).inner continuousOn_const
    refine (integrable_edgeMeasure_of_continuousOn hc).congr
      ((ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)).mono fun x hx ↦ ?_)
    dsimp only
    rw [outwardNormal_eq_edgeNormal (mem_boundaryEdges.1 he) hx]
  rw [h1, Finset.sum_congr rfl fun T _ ↦ 𝒯.integral_div_K_eq_sum_edgeTerm hF hF' T,
    ← Fintype.sum_prod_type' fun T a ↦ 𝒯.edgeTerm F T a,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun e : 𝒯.elems × Fin 3 ↦ 𝒯.IsBoundaryEdge e.1 e.2),
    sum_edgeTerm_interior_eq_zero, add_zero, 𝒯.integral_boundaryMeasure hint]
  refine Finset.sum_congr (by ext e; simp [boundaryEdges]) fun e he ↦ ?_
  unfold edgeTerm
  refine integral_congr_ae
    ((ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)).mono fun x hx ↦ ?_)
  dsimp only
  rw [outwardNormal_eq_edgeNormal (Finset.mem_filter.1 he).2 hx]

variable (𝒯)

/-- **A triangulated domain is a `BoundaryData`**, with the surface measure `𝒯.boundaryMeasure`
and the outward normal `𝒯.outwardNormal` — the instance the polygon consumers of Atkinson–Han
§11.4 and §13.1 and QSS (12.95) take; its trace family is `Triangulation.traceFamily` of
`Boundary/PolygonTrace.lean`. -/
def boundaryData : BoundaryData Ω where
  σ := 𝒯.boundaryMeasure
  ν := 𝒯.outwardNormal
  isBounded := 𝒯.isBounded
  isFiniteMeasure := inferInstance
  measure_compl_frontier := 𝒯.boundaryMeasure_compl_frontier
  aestronglyMeasurable_ν := aestronglyMeasurable_outwardNormal
  ae_norm_ν := ae_norm_outwardNormal
  integral_div_eq _ hF hF' := integral_div_eq hF hF'

@[simp] theorem boundaryData_σ : 𝒯.boundaryData.σ = 𝒯.boundaryMeasure := rfl

@[simp] theorem boundaryData_ν : 𝒯.boundaryData.ν = 𝒯.outwardNormal := rfl

/-! ### The no-slit hypothesis of a polygonal domain -/

/-- **The no-slit hypothesis of a polygonal domain**: the relative interior of every interior
edge lies in `Ω`. It is what the trace theory on a polygon needs (the one-sided traces of a
`W^{1,p}(Ω)` function agree across an interior edge only when `Ω` is on both sides of it) and
what `FrontierSubsetEdges` does not give: the open square minus a closed interior edge of its
triangulation satisfies the four axioms and `FrontierSubsetEdges` but not this; conversely a disc
punctured at a vertex satisfies this and not `FrontierSubsetEdges`. Both hold for a polygon in the
book's sense, and the polygon consumers carry both. -/
def InteriorEdgesSubset : Prop :=
  ∀ (T : 𝒯.elems) (a : Fin 3), ¬ 𝒯.IsBoundaryEdge T a →
    openSegment ℝ (T.1 a) (T.1 (a + 1)) ⊆ Ω

variable {𝒯}

/-- **Without slits, the boundary is the vertices and the open boundary edges**: a point of `∂Ω`
is a vertex or lies on the relative interior of a boundary edge, so that the surface measure sees
all of `∂Ω` but finitely many points. -/
theorem mem_vertices_or_exists_isBoundaryEdge_of_mem_frontier (h : 𝒯.InteriorEdgesSubset)
    {x : 𝔼₂} (hx : x ∈ frontier (Ω : Set 𝔼₂)) :
    x ∈ 𝒯.vertices ∨ ∃ T a, 𝒯.IsBoundaryEdge T a ∧ x ∈ openSegment ℝ (T.1 a) (T.1 (a + 1)) := by
  rw [Ω.isOpen.frontier_eq] at hx
  obtain ⟨hxc, hxΩ⟩ := hx
  rw [𝒯.closure_eq_iUnion_closedK, mem_iUnion] at hxc
  obtain ⟨T, hT⟩ := hxc
  have hxK : x ∉ 𝒯.K T := fun h' ↦ hxΩ (𝒯.K_subset T h')
  have hfr : x ∈ frontier (𝒯.K T) := by
    rw [(𝒯.isOpen_K T).frontier_eq, closure_K]; exact ⟨hT, hxK⟩
  have hedge := frontier_openTriangle_subset _ _ _ (𝒯.li T) hfr
  obtain ⟨a, ha⟩ : ∃ a : Fin 3, x ∈ segment ℝ (T.1 a) (T.1 (a + 1)) := by
    rcases hedge with (h | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  rw [← insert_endpoints_openSegment] at ha
  rcases ha with rfl | rfl | ha
  · exact Or.inl (𝒯.vertex_mem_vertices T a)
  · exact Or.inl (𝒯.vertex_mem_vertices T (a + 1))
  · by_cases hb : 𝒯.IsBoundaryEdge T a
    · exact Or.inr ⟨T, a, hb, ha⟩
    · exact absurd (h T a hb ha) hxΩ

end Triangulation

end
