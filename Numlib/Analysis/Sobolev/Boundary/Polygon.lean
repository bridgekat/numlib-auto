/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Segment
import Numlib.Analysis.Sobolev.Boundary.Data
import Numlib.Geometry.Triangulation
import Numlib.MeasureTheory.Function.LpSeminorm.Basic
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# The divergence theorem on a triangulated plane domain

This module gives every triangulated plane domain $\Omega \subseteq \mathbb{R}^2$ the structure
`BoundaryData` of `Numlib.Analysis.Sobolev.Boundary.Data`: a surface measure $\sigma$ on
$\partial\Omega$, an outward unit normal $\nu$, and the divergence theorem $$\int_\Omega
\operatorname{div} F \, dx = \int_{\partial\Omega} F \cdot \nu \, d\sigma$$ for every vector field
$F \in C^1(\bar\Omega)$. The surface measure is the sum of the arclength measures of the boundary
edges, the edges that belong to only one element. On the relative interior of a boundary edge, the
normal $\nu$ is the unit normal of the edge that points away from the third vertex of its element.
Triangulations are those of `Numlib.Geometry.Triangulation`, in the sense of [han2009theoretical]
§10.2; for polygonal domains see also [grisvard2011elliptic] §1.5.2. For Green's formulas, see
[han2009theoretical] §7.6.

The divergence theorem is proved in three steps. On the reference triangle
$\hat T = \{(x, y) : x > 0, y > 0, x + y < 1\}$, it follows from Fubini's theorem and the
fundamental theorem of calculus in each coordinate. On a nondegenerate triangle, it follows by an
affine change of variables from the reference triangle, with the affine maps of
`Numlib.Analysis.Sobolev.Simplex`. On a triangulated domain, it is the sum of the theorems for the
elements: the terms of an interior edge cancel, because the two elements that share the edge give it
the same arclength measure and opposite normals. No hypothesis on $\Omega$ beyond the axioms of a
triangulation is needed. In particular, a slit along an interior edge does not change the integrals
of a field that is continuous across it.

## Main definitions

* `EuclideanSpace.perp`: the clockwise rotation $v^\perp = (v_1, -v_0)$ of $v \in \mathbb{R}^2$ by a
  right angle.
* `EuclideanSpace.edgeMeasure`: the arclength measure $\sigma_{PQ}$ of the segment $[P, Q]$.
* `EuclideanSpace.edgeNormal`: the unit normal $n_{PQR}$ of $[P, Q]$ that points away from $R$.
* `EuclideanSpace.triangleBoundaryMeasure`, `EuclideanSpace.triangleNormal`: the arclength measure
  of the boundary of a triangle and its outward unit normal, which form the boundary data
  `EuclideanSpace.triangleBoundaryData` of the triangle.
* `Triangulation.IsBoundaryEdge`, `Triangulation.IsPartner`, `Triangulation.boundaryEdges`: the
  edges of the elements that no other element has, and the partner of a shared edge in the other
  element.
* `Triangulation.boundaryMeasure`, `Triangulation.outwardNormal`, `Triangulation.boundaryData`: the
  surface measure, the outward unit normal and the boundary data of a triangulated domain.
* `Triangulation.InteriorEdgesSubset`: the hypothesis that the relative interior of every interior
  edge lies in $\Omega$, which the trace theory on a polygonal domain needs.

## Main results

* `EuclideanSpace.inner_perp_map`: $\langle (Mv)^\perp, Mw \rangle = \det M \, \langle v^\perp, w
  \rangle$ for a linear map $M$ of $\mathbb{R}^2$.
* `EuclideanSpace.integral_div_referenceTriangle`,
  `EuclideanSpace.integral_div_referenceTriangle_eq_integral_inner`: the divergence theorem on the
  reference triangle, with parametrized edges and with the boundary measure.
* `EuclideanSpace.integral_div_openTriangle`: the divergence theorem on a nondegenerate triangle.
* `Triangulation.segment_subset_frontier_of_isBoundaryEdge`: a boundary edge lies in
  $\partial\Omega$.
* `Triangulation.IsPartner.inner_perp_mul_neg`: the partner of an edge lies on the other side of the
  edge.
* `Triangulation.partner_unique`: the partner of an interior edge is unique.
* `Triangulation.integral_div_eq`: the divergence theorem on a triangulated domain.
* `Triangulation.mem_vertices_or_exists_isBoundaryEdge_of_mem_frontier`: if no interior edge is a
  slit, every point of $\partial\Omega$ is a vertex or lies in the relative interior of a boundary
  edge.

## Notation

* $v^\perp = (v_1, -v_0)$ for $v = (v_0, v_1) \in \mathbb{R}^2$; the coordinates are indexed by
  `Fin 2`, from $0$.
* $[P, Q]$ is the closed segment and $(P, Q)$ the open segment from $P$ to $Q$.
* $s(P, Q, R) = \langle (Q - P)^\perp, R - P \rangle$, minus twice the signed area of the triangle
  $PQR$. It is nonzero exactly when $P, Q, R$ are not collinear.
* $\sigma_{PQ}$ is the arclength measure of $[P, Q]$, and $n_{PQR}$ the unit normal of $[P, Q]$ that
  points away from $R$.

## Implementation notes

* An element $T$ of a triangulation is a vertex triple $T_0, T_1, T_2$ with indices in `Fin 3`, so
  that the arithmetic of the indices is modulo $3$. The edge $a$ of $T$ is the segment
  $[T_a, T_{a+1}]$, as in `Triangulation.skeleton_subset_iUnion_segment`, and its third vertex is
  $T_{a+2}$. The open element is the open triangle $T_a T_{a+1} T_{a+2}$ for every $a$
  (`Triangulation.K_eq_rot`). Each statement about the edge $a$ of $T$ is therefore proved for the
  first edge $[P, Q]$ of a triangle $PQR$ and then rotated.
* The sign of $n_{PQR}$ is fixed by the condition $\langle n_{PQR}, R - P \rangle < 0$. By
  `EuclideanSpace.inner_perp_map`, an affine map carries this condition to the image triangle. This
  is how the change of variables in `EuclideanSpace.integral_div_openTriangle`, by a map that need
  not be an isometry, combines $|\det M|$, the edge lengths and the normals into the edge terms of
  the image triangle (`EuclideanSpace.integral_inner_edgeNormal_affine`).
* The regularity of the field is that of `BoundaryData`: $F$ is continuous on $\bar\Omega$ and
  `ContDiffOnClosure ℝ 1 F Ω`. The fundamental theorem of calculus needs continuity on the closed
  slice and the derivative on the open slice. The derivative is bounded, because it extends
  continuously to the compact closure.
* The hypothesis that a triangulated domain is polygonal, as the trace theory needs it, is
  `Triangulation.InteriorEdgesSubset`. The hypothesis `Triangulation.FrontierSubsetEdges` does not
  exclude a slit along a whole interior edge, and neither hypothesis implies the other (see
  `Triangulation.InteriorEdgesSubset`).
-/

open Filter MeasureTheory Set Function TopologicalSpace
open scoped ENNReal InnerProductSpace

noncomputable section

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanSpace

/-! ### The rotation by a right angle -/

/-- The **clockwise rotation by a right angle** of $v = (v_0, v_1) \in \mathbb{R}^2$: $$v^\perp =
(v_1, -v_0).$$ For a segment with direction $v$, the vector $v^\perp$ is a normal direction. -/
def perp (v : 𝔼₂) : 𝔼₂ := !₂[v 1, -v 0]

/-- The first coordinate of $v^\perp$ is $v_1$. -/
@[simp] theorem perp_apply_zero (v : 𝔼₂) : perp v 0 = v 1 := rfl

/-- The second coordinate of $v^\perp$ is $-v_0$. -/
@[simp] theorem perp_apply_one (v : 𝔼₂) : perp v 1 = -v 0 := rfl

/-- For $v, w \in \mathbb{R}^2$, $\langle v^\perp, w \rangle = v_1 w_0 - v_0 w_1$, the negative of
the determinant of the matrix with columns $v$ and $w$. -/
theorem inner_perp_eq (v w : 𝔼₂) : ⟪perp v, w⟫_ℝ = v 1 * w 0 - v 0 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, perp]
  ring

/-- The vector $v^\perp$ is orthogonal to $v$. -/
theorem inner_perp_self (v : 𝔼₂) : ⟪perp v, v⟫_ℝ = 0 := by
  rw [inner_perp_eq]; ring

/-- The rotation preserves the norm: $\|v^\perp\| = \|v\|$. -/
theorem norm_perp (v : 𝔼₂) : ‖perp v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, perp, add_comm]

/-- The rotation commutes with negation: $(-v)^\perp = -v^\perp$. -/
@[simp] theorem perp_neg (v : 𝔼₂) : perp (-v) = -perp v := by
  ext i; fin_cases i <;> simp [perp]

/-- The rotation is additive: $(v - w)^\perp = v^\perp - w^\perp$. -/
theorem perp_sub (v w : 𝔼₂) : perp (v - w) = perp v - perp w := by
  ext i; fin_cases i
  · simp [perp]
  · simp [perp]; ring

/-- The rotation commutes with scalar multiplication: $(cv)^\perp = c \, v^\perp$. -/
@[simp] theorem perp_smul (c : ℝ) (v : 𝔼₂) : perp (c • v) = c • perp v := by
  ext i; fin_cases i <;> simp [perp]

/-- A vector $v \in \mathbb{R}^2$ is $v = v_0 e_0 + v_1 e_1$, where $e_0, e_1$ is the standard
basis. -/
theorem eq_smul_single_add_smul_single (v : 𝔼₂) :
    v = v 0 • EuclideanSpace.single 0 1 + v 1 • EuclideanSpace.single 1 1 := by
  ext i; fin_cases i <;> simp

/-- The transformation rule of the rotation. Let $M : \mathbb{R}^2 \to \mathbb{R}^2$ be linear. Then
for all $v, w \in \mathbb{R}^2$, $$\langle (Mv)^\perp, Mw \rangle = \det M \, \langle v^\perp, w
\rangle.$$

The determinant is `LinearMap.det` of $M$. -/
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

/-- Two vectors $v, w \in \mathbb{R}^2$ are linearly independent if and only if
$\langle v^\perp, w \rangle \neq 0$. -/
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

/-- The quantity $s(A, B, C) = \langle (B - A)^\perp, C - A \rangle$ does not change under a cyclic
rotation of the vertices: $s(B, C, A) = s(A, B, C)$. -/
theorem inner_perp_rotate (A B C : 𝔼₂) :
    ⟪perp (C - B), A - B⟫_ℝ = ⟪perp (B - A), C - A⟫_ℝ := by
  rw [inner_perp_eq, inner_perp_eq]
  simp only [PiLp.sub_apply]
  ring

/-- The quantity $s(A, B, C) = \langle (B - A)^\perp, C - A \rangle$ changes sign when the first two
vertices are exchanged: $s(B, A, C) = -s(A, B, C)$. -/
theorem inner_perp_swap (A B C : 𝔼₂) :
    ⟪perp (A - B), C - B⟫_ℝ = -⟪perp (B - A), C - A⟫_ℝ := by
  rw [inner_perp_eq, inner_perp_eq]
  simp only [PiLp.sub_apply]
  ring

/-! ### Plane triangles: rotations of the vertices and barycentric coordinates -/

/-- If $B - A$ and $C - A$ are linearly independent, then so are $C - B$ and $A - B$:
noncollinearity is invariant under a cyclic rotation of the vertices. -/
theorem linearIndependent_rotate {A B C : 𝔼₂} (h : LinearIndependent ℝ ![B - A, C - A]) :
    LinearIndependent ℝ ![C - B, A - B] := by
  rw [linearIndependent_pair_iff_inner_perp_ne_zero] at h ⊢
  rwa [inner_perp_rotate]

/-- If $B - A$ and $C - A$ are linearly independent, then so are $A - B$ and $C - B$:
noncollinearity is invariant under an exchange of the first two vertices. -/
theorem linearIndependent_swap {A B C : 𝔼₂} (h : LinearIndependent ℝ ![B - A, C - A]) :
    LinearIndependent ℝ ![A - B, C - B] := by
  rw [linearIndependent_pair_iff_inner_perp_ne_zero] at h ⊢
  rwa [inner_perp_swap, neg_ne_zero]

/-- The open triangle does not change under a cyclic rotation of its vertices: the open triangle
with vertices $B, C, A$ is the open triangle with vertices $A, B, C$.

The open triangle is `EuclideanSpace.openTriangle`, the set of the points
$A + s(B - A) + t(C - A)$ with $s, t > 0$ and $s + t < 1$. -/
theorem openTriangle_rotate (A B C : 𝔼₂) : openTriangle B C A = openTriangle A B C := by
  ext x
  simp only [mem_openTriangle]
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨1 - s - t, s, by linarith, hs, by linarith, by module⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨t, 1 - s - t, ht, by linarith, by linarith, by module⟩

/-- The open triangle does not change when its first two vertices are exchanged. -/
theorem openTriangle_swap (A B C : 𝔼₂) : openTriangle B A C = openTriangle A B C := by
  ext x
  simp only [mem_openTriangle]
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨1 - s - t, t, by linarith, ht, by linarith, by module⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨1 - s - t, t, by linarith, ht, by linarith, by module⟩

/-- The closed triangle does not change under a cyclic rotation of its vertices. -/
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

/-- Each segment between two vertices of a triangle lies in the closed triangle. -/
theorem segment_subset_closedTriangle (A B C : 𝔼₂) (a b : Fin 3) :
    segment ℝ (![A, B, C] a) (![A, B, C] b) ⊆ closedTriangle A B C :=
  (convex_closedTriangle A B C).segment_subset (vertex_mem_closedTriangle A B C a)
    (vertex_mem_closedTriangle A B C b)

/-- **Uniqueness of barycentric coordinates.** Let $A, B, C \in \mathbb{R}^2$ with $B - A$ and
$C - A$ linearly independent. If $A + s(B - A) + t(C - A) = A + s'(B - A) + t'(C - A)$, then
$s = s'$ and $t = t'$. -/
theorem eq_of_affine_eq {A B C : 𝔼₂} (h : LinearIndependent ℝ ![B - A, C - A]) {s t s' t' : ℝ}
    (e : A + s • (B - A) + t • (C - A) = A + s' • (B - A) + t' • (C - A)) : s = s' ∧ t = t' := by
  have e' : (s - s') • (B - A) + (t - t') • (C - A) = 0 := by
    calc (s - s') • (B - A) + (t - t') • (C - A)
        = (A + s • (B - A) + t • (C - A)) - (A + s' • (B - A) + t' • (C - A)) := by module
      _ = 0 := sub_eq_zero.2 e
  have := LinearIndependent.pair_iff.1 h _ _ e'
  exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩

section EdgeGeometry

variable {P Q R x : 𝔼₂} (h : LinearIndependent ℝ ![Q - P, R - P])
include h

/-- Let $P, Q, R$ be noncollinear. A point of the edge $[P, Q]$ is not in the open triangle $PQR$.
-/
theorem notMem_openTriangle_of_mem_segment (hx : x ∈ segment ℝ P Q) :
    x ∉ openTriangle P Q R := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_segment_iff'.1 hx
  rintro hx'
  obtain ⟨s', t', hs', ht', hst', e⟩ := mem_openTriangle.1 hx'
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := s') (t' := t')
    (by rw [zero_smul, add_zero]; exact e)
  linarith [this.2]

/-- Let $P, Q, R$ be noncollinear. A point of the open edge $(P, Q)$ is not in the open triangle
$PQR$. -/
theorem notMem_openTriangle_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) :
    x ∉ openTriangle P Q R :=
  notMem_openTriangle_of_mem_segment h (openSegment_subset_segment ℝ _ _ hx)

/-- Let $P, Q, R$ be noncollinear. A point of the open edge $(P, Q)$ is not the vertex $P$. -/
theorem ne_left_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) : x ≠ P := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro e
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 0) (t' := 0)
    (by simp only [zero_smul, add_zero]; exact e)
  linarith [this.1]

/-- Let $P, Q, R$ be noncollinear. A point of the open edge $(P, Q)$ is not the vertex $Q$. -/
theorem ne_right_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) : x ≠ Q := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro e
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 1) (t' := 0)
    (by simp only [zero_smul, add_zero, one_smul]; rw [e]; abel)
  linarith [this.1]

/-- Let $P, Q, R$ be noncollinear. A point of the open edge $(P, Q)$ is not the third vertex $R$. -/
theorem ne_third_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) : x ≠ R := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro e
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 0) (t' := 1)
    (by simp only [zero_smul, add_zero, one_smul]; rw [e]; abel)
  linarith [this.1]

/-- Let $P, Q, R$ be noncollinear. A point of the open edge $(P, Q)$ is none of the three vertices.
-/
theorem ne_vertex_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) (i : Fin 3) :
    x ≠ ![P, Q, R] i := by
  fin_cases i
  · exact ne_left_of_mem_openSegment h hx
  · exact ne_right_of_mem_openSegment h hx
  · exact ne_third_of_mem_openSegment h hx

/-- Let $P, Q, R$ be noncollinear. A point of the open edge $(P, Q)$ is not on the closed edge
$[Q, R]$. -/
theorem notMem_segment_right_third_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) :
    x ∉ segment ℝ Q R := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro hx'
  obtain ⟨u, hu0, hu1, e⟩ := mem_segment_iff'.1 hx'
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 1 - u) (t' := u)
    (by rw [zero_smul, add_zero]; rw [e]; module)
  linarith [this.1, this.2]

/-- Let $P, Q, R$ be noncollinear. A point of the open edge $(P, Q)$ is not on the closed edge
$[R, P]$. -/
theorem notMem_segment_third_left_of_mem_openSegment (hx : x ∈ openSegment ℝ P Q) :
    x ∉ segment ℝ R P := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_openSegment_iff'.1 hx
  intro hx'
  obtain ⟨u, hu0, hu1, e⟩ := mem_segment_iff'.1 hx'
  have := eq_of_affine_eq h (s := s) (t := 0) (s' := 0) (t' := 1 - u)
    (by rw [zero_smul, add_zero]; rw [e]; module)
  linarith [this.1]

/-- A point of an open edge lies on no other closed edge of the triangle. Let $P, Q, R$ be
noncollinear, write $V_0 = P$, $V_1 = Q$, $V_2 = R$, and let $x \in (P, Q)$. If $c \neq d$ in
$\{0, 1, 2\}$ and $x \in [V_c, V_d]$, then $\{c, d\} = \{0, 1\}$. -/
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

/-- Let $P, Q, R$ be noncollinear. The edge $[P, Q]$ lies in the frontier of the open triangle
$PQR$. -/
theorem segment_subset_frontier_openTriangle :
    segment ℝ P Q ⊆ frontier (openTriangle P Q R) := by
  rw [(isOpen_openTriangle P Q R h).frontier_eq, closure_openTriangle]
  exact fun x hx ↦ ⟨segment_subset_closedTriangle P Q R 0 1 hx,
    notMem_openTriangle_of_mem_segment h hx⟩

end EdgeGeometry

/-- For a vertex triple $T_0, T_1, T_2$ and every $a$ modulo $3$, the open triangle $T_0 T_1 T_2$ is
the open triangle $T_a T_{a+1} T_{a+2}$. -/
theorem openTriangle_eq_rot (T : Fin 3 → 𝔼₂) (a : Fin 3) :
    openTriangle (T 0) (T 1) (T 2) = openTriangle (T a) (T (a + 1)) (T (a + 2)) := by
  fin_cases a
  · rfl
  · exact (openTriangle_rotate (T 0) (T 1) (T 2)).symm
  · exact openTriangle_rotate (T 2) (T 0) (T 1)

/-- For a vertex triple $T_0, T_1, T_2$ and every $a$ modulo $3$, the closed triangle $T_0 T_1 T_2$
is the closed triangle $T_a T_{a+1} T_{a+2}$. -/
theorem closedTriangle_eq_rot (T : Fin 3 → 𝔼₂) (a : Fin 3) :
    closedTriangle (T 0) (T 1) (T 2) = closedTriangle (T a) (T (a + 1)) (T (a + 2)) := by
  fin_cases a
  · rfl
  · exact (closedTriangle_rotate (T 0) (T 1) (T 2)).symm
  · exact closedTriangle_rotate (T 2) (T 0) (T 1)

/-- If $T_1 - T_0$ and $T_2 - T_0$ are linearly independent, then for every $a$ modulo $3$, so are
$T_{a+1} - T_a$ and $T_{a+2} - T_a$. -/
theorem linearIndependent_rot {T : Fin 3 → 𝔼₂} (h : LinearIndependent ℝ ![T 1 - T 0, T 2 - T 0])
    (a : Fin 3) : LinearIndependent ℝ ![T (a + 1) - T a, T (a + 2) - T a] := by
  fin_cases a
  · exact h
  · exact linearIndependent_rotate h
  · exact linearIndependent_rotate (linearIndependent_rotate h)

/-- The vertex triple $(T_a, T_{a+1}, T_{a+2})$, at the index $i$, is $T_{a+i}$, with indices modulo
$3$. -/
theorem vecCons_rot (T : Fin 3 → 𝔼₂) (a i : Fin 3) :
    ![T a, T (a + 1), T (a + 2)] i = T (a + i) := by
  fin_cases i <;> simp

/-- If $T_1 - T_0$ and $T_2 - T_0$ are linearly independent, then the vertices $T_0, T_1, T_2$ are
distinct. -/
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

/-- In `Fin 3`, $a \neq a + 1$. -/
theorem fin3_ne_add_one (a : Fin 3) : a ≠ a + 1 := by revert a; decide

/-- Two distinct indices $i \neq j$ in `Fin 3` are consecutive: there is an $a$ with
$(i, j) = (a, a + 1)$ or $(i, j) = (a + 1, a)$. -/
theorem exists_fin3_of_ne {i j : Fin 3} (hij : i ≠ j) :
    ∃ a : Fin 3, (i = a ∧ j = a + 1) ∨ (i = a + 1 ∧ j = a) := by
  revert i j; decide

/-! ### Segments and the edge measure -/

/-- For $t \in [0, 1]$, the point $P + t(Q - P)$ lies on the segment $[P, Q]$. -/
theorem lineMap_mem_segment' (P Q : 𝔼₂) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap P Q t ∈ segment ℝ P Q := by
  rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩

/-- The map $x \mapsto Mx + b$, for a linear equivalence $M$ of $\mathbb{R}^2$, maps the point
$P + t(Q - P)$ to the point $P' + t(Q' - P')$, where $P' = MP + b$ and $Q' = MQ + b$. -/
theorem lineMap_affine (M : 𝔼₂ ≃L[ℝ] 𝔼₂) (b P Q : 𝔼₂) (t : ℝ) :
    M (AffineMap.lineMap P Q t) + b = AffineMap.lineMap (M P + b) (M Q + b) t := by
  rw [lineMap_eq, lineMap_eq, map_add, map_smul, map_sub]
  module

/-- The map $x \mapsto Mx + b$, for a linear equivalence $M$ of $\mathbb{R}^2$, maps the segment
$[P, Q]$ onto the segment $[MP + b, MQ + b]$. -/
theorem image_segment_affine (M : 𝔼₂ ≃L[ℝ] 𝔼₂) (b P Q : 𝔼₂) :
    (fun x ↦ M x + b) '' segment ℝ P Q = segment ℝ (M P + b) (M Q + b) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap, image_image]
  congr 1
  funext t
  exact lineMap_affine M b P Q t

/-- The **arclength measure** $\sigma_{PQ}$ of the segment $[P, Q]$ in $\mathbb{R}^2$: the image of
Lebesgue measure on $[0, 1]$ under the parametrization $t \mapsto P + t(Q - P)$, multiplied by
the length $\|Q - P\|$.

The parametrization is `AffineMap.lineMap P Q`. For $P = Q$ the measure is zero
(`EuclideanSpace.edgeMeasure_self`). -/
def edgeMeasure (P Q : 𝔼₂) : Measure 𝔼₂ :=
  (‖Q - P‖).toNNReal • Measure.map (AffineMap.lineMap P Q) (volume.restrict (Icc (0 : ℝ) 1))

/-- The arclength measure of a segment is finite. -/
instance isFiniteMeasure_edgeMeasure (P Q : 𝔼₂) : IsFiniteMeasure (edgeMeasure P Q) := by
  unfold edgeMeasure
  infer_instance

/-- For a measurable set $s$, $\sigma_{PQ}(s) = \|Q - P\| \, \lambda(\{t \in [0, 1] : P + t(Q - P)
\in s\})$, where $\lambda$ is Lebesgue measure. -/
theorem edgeMeasure_apply (P Q : 𝔼₂) {s : Set 𝔼₂} (hs : MeasurableSet s) :
    edgeMeasure P Q s
      = ENNReal.ofReal ‖Q - P‖ * volume ((AffineMap.lineMap P Q : ℝ → 𝔼₂) ⁻¹' s ∩ Icc 0 1) := by
  rw [edgeMeasure, Measure.smul_apply, Measure.map_apply (continuous_lineMap P Q).measurable hs,
    Measure.restrict_apply' measurableSet_Icc, ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal]

/-- The arclength measure $\sigma_{PQ}$ is carried by the segment $[P, Q]$: the complement of the
segment has measure zero. -/
theorem edgeMeasure_compl_segment (P Q : 𝔼₂) : edgeMeasure P Q (segment ℝ P Q)ᶜ = 0 := by
  rw [edgeMeasure_apply P Q (measurableSet_segment P Q).compl]
  have : (AffineMap.lineMap P Q : ℝ → 𝔼₂) ⁻¹' (segment ℝ P Q)ᶜ ∩ Icc 0 1 = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    exact fun h ht ↦ h (lineMap_mem_segment' P Q ht)
  rw [this, measure_empty, mul_zero]

/-- Almost every point for $\sigma_{PQ}$ lies on the segment $[P, Q]$. -/
theorem ae_mem_segment (P Q : 𝔼₂) : ∀ᵐ x ∂edgeMeasure P Q, x ∈ segment ℝ P Q :=
  ae_iff.2 (edgeMeasure_compl_segment P Q)

/-- If $P \neq Q$, every point has measure zero for $\sigma_{PQ}$. -/
theorem edgeMeasure_singleton {P Q : 𝔼₂} (h : P ≠ Q) (x : 𝔼₂) : edgeMeasure P Q {x} = 0 := by
  rw [edgeMeasure_apply P Q (measurableSet_singleton x)]
  refine mul_eq_zero_of_right _ (measure_mono_null inter_subset_left ?_)
  refine Set.Subsingleton.measure_zero (fun s hs t ht ↦ ?_) _
  exact AffineMap.lineMap_injective ℝ h (hs.trans ht.symm)

/-- The complement of the open segment $(P, Q)$ lies in the union of the complement of $[P, Q]$ and
the two endpoints. -/
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

/-- If $P \neq Q$, the arclength measure $\sigma_{PQ}$ is carried by the open segment $(P, Q)$. -/
theorem edgeMeasure_compl_openSegment {P Q : 𝔼₂} (h : P ≠ Q) :
    edgeMeasure P Q (openSegment ℝ P Q)ᶜ = 0 :=
  measure_mono_null (compl_openSegment_subset P Q)
    (measure_union_null (measure_union_null (edgeMeasure_compl_segment P Q)
      (edgeMeasure_singleton h P)) (edgeMeasure_singleton h Q))

/-- If $P \neq Q$, almost every point for $\sigma_{PQ}$ lies on the open segment $(P, Q)$. -/
theorem ae_mem_openSegment {P Q : 𝔼₂} (h : P ≠ Q) :
    ∀ᵐ x ∂edgeMeasure P Q, x ∈ openSegment ℝ P Q :=
  ae_iff.2 (edgeMeasure_compl_openSegment h)

/-- The arclength measure of a degenerate segment is zero: $\sigma_{PP} = 0$. -/
theorem edgeMeasure_self (P : 𝔼₂) : edgeMeasure P P = 0 := by
  rw [edgeMeasure, sub_self, norm_zero, Real.toNNReal_zero, zero_smul]

/-- The arclength measure does not depend on the orientation of the segment:
$\sigma_{QP} = \sigma_{PQ}$. -/
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

/-- A real function that is continuous on the segment $[P, Q]$ is almost everywhere strongly
measurable for $\sigma_{PQ}$. -/
theorem aestronglyMeasurable_edgeMeasure_of_continuousOn {f : 𝔼₂ → ℝ} {P Q : 𝔼₂}
    (hf : ContinuousOn f (segment ℝ P Q)) : AEStronglyMeasurable f (edgeMeasure P Q) := by
  have := hf.aestronglyMeasurable (μ := edgeMeasure P Q) (measurableSet_segment P Q)
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_segment P Q)] at this

/-- A real function that is continuous on the segment $[P, Q]$ is integrable for $\sigma_{PQ}$. -/
theorem integrable_edgeMeasure_of_continuousOn {f : 𝔼₂ → ℝ} {P Q : 𝔼₂}
    (hf : ContinuousOn f (segment ℝ P Q)) : Integrable f (edgeMeasure P Q) := by
  have : IsFiniteMeasureOnCompacts (edgeMeasure P Q) := ⟨fun _ _ ↦ measure_lt_top _ _⟩
  have := hf.integrableOn_compact (μ := edgeMeasure P Q) (isCompact_segment P Q)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_segment P Q)] at this

/-- Almost every point for the image of Lebesgue measure on $[0, 1]$ under $t \mapsto P + t(Q - P)$
lies on the segment $[P, Q]$. -/
theorem ae_map_lineMap_mem_segment (P Q : 𝔼₂) :
    ∀ᵐ x ∂(Measure.map (AffineMap.lineMap P Q) (volume.restrict (Icc (0 : ℝ) 1))),
      x ∈ segment ℝ P Q := by
  refine (ae_map_iff (continuous_lineMap P Q).measurable.aemeasurable
    (measurableSet_segment P Q)).2 ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall fun t ht ↦ lineMap_mem_segment' P Q ht

/-- Let $f : \mathbb{R}^2 \to \mathbb{R}$ be continuous on the segment $[P, Q]$. Then $$\int f \,
d\sigma_{PQ} = \|Q - P\| \int_0^1 f(P + t(Q - P)) \, dt.$$
-/
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

/-- Let $P \neq Q$ and let $U \subseteq \mathbb{R}^2$ be an open set that meets the open segment
$(P, Q)$. Then $\sigma_{PQ}(U) > 0$. -/
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

/-- The **edge normal** $n_{PQR}$: the unit normal of the segment $[P, Q]$ that points away from the
point $R$,
$$n_{PQR} = \begin{cases}
  (Q - P)^\perp / \|Q - P\| & \text{if } s(P, Q, R) < 0, \\
  -(Q - P)^\perp / \|Q - P\| & \text{otherwise},
\end{cases}$$
where $s(P, Q, R) = \langle (Q - P)^\perp, R - P \rangle$. For a nondegenerate triangle $PQR$, it
is the outward unit normal of the triangle on the edge $[P, Q]$.

The sign is fixed by the condition $\langle n_{PQR}, R - P \rangle < 0$
(`EuclideanSpace.inner_edgeNormal_third_neg`), which affine maps preserve. For $P = Q$ the value
is $0$, because $\|Q - P\|^{-1}$ is read as $0$. If $P, Q, R$ are collinear and $P \neq Q$, the
value is $-(Q - P)^\perp / \|Q - P\|$. -/
def edgeNormal (P Q R : 𝔼₂) : 𝔼₂ :=
  if ⟪perp (Q - P), R - P⟫_ℝ < 0 then ‖Q - P‖⁻¹ • perp (Q - P)
  else -(‖Q - P‖⁻¹ • perp (Q - P))

/-- If $s(P, Q, R) = \langle (Q - P)^\perp, R - P \rangle \neq 0$, then $P \neq Q$. -/
theorem ne_of_inner_perp_ne_zero {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) : P ≠ Q := by
  rintro rfl
  apply h
  rw [sub_self, inner_perp_eq]
  simp

/-- If $s(P, Q, R) \neq 0$, the edge normal $n_{PQR}$ is a unit vector. -/
theorem norm_edgeNormal {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) :
    ‖edgeNormal P Q R‖ = 1 := by
  have hQP : ‖Q - P‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (ne_of_inner_perp_ne_zero h).symm)
  unfold edgeNormal
  split_ifs <;> simp [norm_smul, norm_perp, hQP]

/-- The edge normal is orthogonal to the edge: $\langle n_{PQR}, Q - P \rangle = 0$. -/
theorem inner_edgeNormal_sub (P Q R : 𝔼₂) : ⟪edgeNormal P Q R, Q - P⟫_ℝ = 0 := by
  unfold edgeNormal
  split_ifs <;> simp [inner_smul_left, inner_perp_self]

/-- The quantity $\langle n_{PQR}, y - x_0 \rangle$ is constant for $y$ on the line through $P$ and
$Q$: $\langle n_{PQR}, P + t(Q - P) - x_0 \rangle = \langle n_{PQR}, P - x_0 \rangle$ for every
$t$. This is the fact behind the transversal field $x - x_0$ on a convex polygon. -/
theorem inner_edgeNormal_lineMap_sub (P Q R x₀ : 𝔼₂) (t : ℝ) :
    ⟪edgeNormal P Q R, AffineMap.lineMap P Q t - x₀⟫_ℝ = ⟪edgeNormal P Q R, P - x₀⟫_ℝ := by
  rw [lineMap_eq, show P + t • (Q - P) - x₀ = (P - x₀) + t • (Q - P) by module, inner_add_right,
    inner_smul_right, inner_edgeNormal_sub, mul_zero, add_zero]

/-- If $s(P, Q, R) \neq 0$, the edge normal points away from the third vertex:
$\langle n_{PQR}, R - P \rangle < 0$. -/
theorem inner_edgeNormal_third_neg {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) :
    ⟪edgeNormal P Q R, R - P⟫_ℝ < 0 := by
  have hQP : 0 < ‖Q - P‖ := norm_pos_iff.2 (sub_ne_zero.2 (ne_of_inner_perp_ne_zero h).symm)
  unfold edgeNormal
  split_ifs with hx
  · rw [inner_smul_left]
    simpa using mul_neg_of_pos_of_neg (inv_pos.2 hQP) hx
  · rw [inner_neg_left, inner_smul_left, neg_lt_zero]
    simpa using mul_pos (inv_pos.2 hQP) (lt_of_le_of_ne (not_lt.1 hx) (Ne.symm h))

/-- If $s(P, Q, R) \neq 0$, the edge normal does not depend on the orientation of the edge:
$n_{QPR} = n_{PQR}$. -/
theorem edgeNormal_symm {P Q R : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0) :
    edgeNormal Q P R = edgeNormal P Q R := by
  unfold edgeNormal
  rw [inner_perp_swap, norm_sub_rev, ← neg_sub Q P, perp_neg, smul_neg]
  split_ifs with h1 h2 h2
  · exfalso; linarith
  · rfl
  · rw [neg_neg]
  · exfalso; exact h (by linarith)

/-- If $R$ and $R'$ lie strictly on opposite sides of the line through $P$ and $Q$, that is,
$s(P, Q, R) \, s(P, Q, R') < 0$, then $n_{PQR'} = -n_{PQR}$. -/
theorem edgeNormal_eq_neg_of_mul_neg {P Q R R' : 𝔼₂}
    (h : ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), R' - P⟫_ℝ < 0) :
    edgeNormal P Q R' = -edgeNormal P Q R := by
  unfold edgeNormal
  rcases mul_neg_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ite_eq_left h2, ite_eq_right (not_lt.2 h1.le), neg_neg]
  · rw [ite_eq_right (not_lt.2 h2.le), ite_eq_left h1]

/-- If $R$ and $R'$ lie strictly on the same side of the line through $P$ and $Q$, that is,
$s(P, Q, R) \, s(P, Q, R') > 0$, then $n_{PQR'} = n_{PQR}$. -/
theorem edgeNormal_eq_of_mul_pos {P Q R R' : 𝔼₂}
    (h : 0 < ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), R' - P⟫_ℝ) :
    edgeNormal P Q R' = edgeNormal P Q R := by
  unfold edgeNormal
  rcases mul_pos_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ite_eq_right (not_lt.2 h2.le), ite_eq_right (not_lt.2 h1.le)]
  · rw [ite_eq_left h2, ite_eq_left h1]

/-- The edge term of a positively oriented edge. Let $s(P, Q, R) < 0$, and let
$F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on $[P, Q]$. Then $$\int \langle F, n_{PQR}
\rangle \, d\sigma_{PQ} = \int_0^1 \langle (Q - P)^\perp, F(P + t(Q - P)) \rangle \, dt.$$ The
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

/-- For a linear equivalence $M$ of $\mathbb{R}^2$ and $v, y \in \mathbb{R}^2$, $\langle M^{-1} y,
v^\perp \rangle = (\det M)^{-1} \langle y, (Mv)^\perp \rangle$. -/
theorem inner_symm_perp (M : 𝔼₂ ≃L[ℝ] 𝔼₂) (v y : 𝔼₂) :
    ⟪M.symm y, perp v⟫_ℝ
      = (LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂))⁻¹ * ⟪y, perp (M v)⟫_ℝ := by
  have hd : LinearMap.det ((M : 𝔼₂ →L[ℝ] 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂) ≠ 0 :=
    (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  have := inner_perp_map (M : 𝔼₂ →L[ℝ] 𝔼₂) v (M.symm y)
  rw [ContinuousLinearEquiv.coe_coe, M.apply_symm_apply] at this
  rw [eq_inv_mul_iff_mul_eq₀ hd, real_inner_comm (perp (M v)) y, this,
    real_inner_comm (M.symm y) (perp v)]

/-- The edge normal under the affine map $\Phi(x) = Mx + b$. Let $M$ be a linear equivalence of
$\mathbb{R}^2$, let $b \in \mathbb{R}^2$, and let $s(P, Q, R) \neq 0$. Write $P' = \Phi(P)$,
$Q' = \Phi(Q)$, $R' = \Phi(R)$. Then for every $y \in \mathbb{R}^2$, $$\langle M^{-1} y, n_{PQR}
\rangle = |\det M|^{-1} \, \frac{\|Q' - P'\|}{\|Q - P\|} \, \langle y, n_{P'Q'R'} \rangle.$$

The sign condition in the definition of the edge normal is carried to the image triangle by
`EuclideanSpace.inner_perp_map`. -/
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

/-- The edge term under the affine map $\Phi(x) = Mx + b$. Let $M$ be a linear equivalence of
$\mathbb{R}^2$, let $b \in \mathbb{R}^2$, and let $s(P, Q, R) \neq 0$. Write $P' = \Phi(P)$,
$Q' = \Phi(Q)$, $R' = \Phi(R)$, and let $F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on
$[P', Q']$. Then $$|\det M| \int \langle M^{-1} F(\Phi(x)), n_{PQR} \rangle \, d\sigma_{PQ}(x) =
\int \langle F, n_{P'Q'R'} \rangle \, d\sigma_{P'Q'}.$$ That is, $|\det M|$ times the edge term
of the field $M^{-1} \circ F \circ \Phi$ on $[P, Q]$ is the edge term of $F$ on the image edge,
with the outward normal of the image triangle. -/
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

/-- A triangle contains a half-disc around the midpoint of each edge, on its own side of the edge.
Let $P, Q, R$ be noncollinear. Then there is a $\delta > 0$ such that for every
$v \in \mathbb{R}^2$ with $\|v\| < \delta$ and $s(P, Q, R) \, \langle (Q - P)^\perp, v \rangle >
0$, the point $\frac{1}{2}(P + Q) + v$ lies in the open triangle $PQR$. -/
theorem exists_ball_inter_subset_openTriangle {P Q R : 𝔼₂}
    (h : LinearIndependent ℝ ![Q - P, R - P]) :
    ∃ δ > 0, ∀ v : 𝔼₂, ‖v‖ < δ → 0 < ⟪perp (Q - P), R - P⟫_ℝ * ⟪perp (Q - P), v⟫_ℝ →
      midpoint ℝ P Q + v ∈ openTriangle P Q R := by
  set M := triangleEquiv P Q R h with hM
  set C := ‖(M.symm : 𝔼₂ →L[ℝ] 𝔼₂)‖ with hC
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

/-- Two triangles on the same side of a common edge overlap. If $R$ and $R'$ lie strictly on the
same side of the line through $P$ and $Q$, that is, $s(P, Q, R) \, s(P, Q, R') > 0$, then the
open triangles $PQR$ and $PQR'$ meet. -/
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

/-- The **boundary measure of the triangle** $ABC$: the sum
$\sigma_{AB} + \sigma_{BC} + \sigma_{CA}$ of the arclength measures of its three edges. -/
def triangleBoundaryMeasure (A B C : 𝔼₂) : Measure 𝔼₂ :=
  edgeMeasure A B + edgeMeasure B C + edgeMeasure C A

open Classical in
/-- The **outward unit normal of the triangle** $ABC$: $n_{ABC}$ on the open edge $(A, B)$,
$n_{BCA}$ on $(B, C)$, $n_{CAB}$ on $(C, A)$, and $0$ at every other point.

The open edges are tested in this order. The vertices have measure zero for the boundary measure
of a nondegenerate triangle, so the value there does not matter. -/
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
/-- On the open edge $(A, B)$, the normal of the triangle $ABC$ is the edge normal $n_{ABC}$. -/
theorem triangleNormal_eq_of_mem_openSegment₀₁ {x : 𝔼₂} (hx : x ∈ openSegment ℝ A B) :
    triangleNormal A B C x = edgeNormal A B C := by
  rw [triangleNormal, ite_eq_left hx]

/-- Let $A, B, C$ be noncollinear. On the open edge $(B, C)$, the normal of the triangle $ABC$ is
the edge normal $n_{BCA}$. -/
theorem triangleNormal_eq_of_mem_openSegment₁₂ {x : 𝔼₂} (hx : x ∈ openSegment ℝ B C) :
    triangleNormal A B C x = edgeNormal B C A := by
  have h1 : x ∉ openSegment ℝ A B := fun hx' ↦
    notMem_segment_right_third_of_mem_openSegment h hx' (openSegment_subset_segment ℝ _ _ hx)
  rw [triangleNormal, ite_eq_right h1, ite_eq_left hx]

/-- Let $A, B, C$ be noncollinear. On the open edge $(C, A)$, the normal of the triangle $ABC$ is
the edge normal $n_{CAB}$. -/
theorem triangleNormal_eq_of_mem_openSegment₂₀ {x : 𝔼₂} (hx : x ∈ openSegment ℝ C A) :
    triangleNormal A B C x = edgeNormal C A B := by
  have h1 : x ∉ openSegment ℝ A B := fun hx' ↦
    notMem_segment_third_left_of_mem_openSegment h hx' (openSegment_subset_segment ℝ _ _ hx)
  have h2 : x ∉ openSegment ℝ B C := fun hx' ↦
    notMem_segment_right_third_of_mem_openSegment (linearIndependent_rotate h) hx'
      (openSegment_subset_segment ℝ _ _ hx)
  rw [triangleNormal, ite_eq_right h1, ite_eq_right h2, ite_eq_left hx]

/-- The vertices of a nondegenerate triangle $ABC$ are distinct: $A \neq B$. -/
theorem ne₀₁ : A ≠ B :=
  ne_of_inner_perp_ne_zero ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 h)

/-- The vertices of a nondegenerate triangle $ABC$ are distinct: $B \neq C$. -/
theorem ne₁₂ : B ≠ C :=
  ne_of_inner_perp_ne_zero
    ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (linearIndependent_rotate h))

/-- The vertices of a nondegenerate triangle $ABC$ are distinct: $C \neq A$. -/
theorem ne₂₀ : C ≠ A :=
  ne_of_inner_perp_ne_zero ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1
    (linearIndependent_rotate (linearIndependent_rotate h)))

/-- Let $A, B, C$ be noncollinear. The outward normal of the triangle $ABC$ has norm $1$ almost
everywhere for the boundary measure of the triangle. -/
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

/-- Let $A, B, C$ be noncollinear. The outward normal of the triangle $ABC$ is almost everywhere
strongly measurable for the boundary measure of the triangle. -/
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

/-- Let $A, B, C$ be noncollinear. The boundary measure of the triangle $ABC$ is carried by the
frontier of the open triangle: the complement of the frontier has measure zero. -/
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
/-- Let $f : \mathbb{R}^2 \to \mathbb{R}$ be integrable for each of $\sigma_{AB}$, $\sigma_{BC}$ and
$\sigma_{CA}$. Then the integral of $f$ for the boundary measure of the triangle $ABC$ is $\int
f \, d\sigma_{AB} + \int f \, d\sigma_{BC} + \int f \, d\sigma_{CA}$. -/
theorem integral_triangleBoundaryMeasure {f : 𝔼₂ → ℝ} (h₁ : Integrable f (edgeMeasure A B))
    (h₂ : Integrable f (edgeMeasure B C)) (h₃ : Integrable f (edgeMeasure C A)) :
    ∫ x, f x ∂triangleBoundaryMeasure A B C
      = ∫ x, f x ∂edgeMeasure A B + ∫ x, f x ∂edgeMeasure B C + ∫ x, f x ∂edgeMeasure C A := by
  unfold triangleBoundaryMeasure
  rw [integral_add_measure (h₁.add_measure h₂) h₃, integral_add_measure h₁ h₂]

/-- The boundary integral of $\langle F, \nu \rangle$ on a triangle is the sum of three edge terms.
Let $A, B, C$ be noncollinear, let $\sigma$ and $\nu$ be the boundary measure and the outward
normal of the triangle $ABC$, and let $F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on the
closed triangle. Then $$\int \langle F, \nu \rangle \, d\sigma = \int \langle F, n_{ABC} \rangle
\, d\sigma_{AB} + \int \langle F, n_{BCA} \rangle \, d\sigma_{BC} + \int \langle F, n_{CAB}
\rangle \, d\sigma_{CA}.$$ In each edge term the normal is constant. -/
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

/-- The measurable equivalence $\mathbb{R}^2 \to \mathbb{R} \times \mathbb{R}$,
$x \mapsto (x_0, x_1)$, from the Euclidean plane to the product of two lines. -/
def planeMeasurableEquiv : 𝔼₂ ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

/-- The equivalence $x \mapsto (x_0, x_1)$ maps Lebesgue measure on $\mathbb{R}^2$ to Lebesgue
measure on $\mathbb{R} \times \mathbb{R}$. -/
theorem measurePreserving_planeMeasurableEquiv :
    MeasurePreserving planeMeasurableEquiv volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

/-- The equivalence `EuclideanSpace.planeMeasurableEquiv` maps $x$ to $(x_0, x_1)$. -/
@[simp] theorem planeMeasurableEquiv_apply (x : 𝔼₂) : planeMeasurableEquiv x = (x 0, x 1) := rfl

/-- The inverse of `EuclideanSpace.planeMeasurableEquiv` maps $(p_1, p_2)$ to the vector with
coordinates $p_1$ and $p_2$. -/
@[simp] theorem planeMeasurableEquiv_symm_apply (p : ℝ × ℝ) :
    planeMeasurableEquiv.symm p = !₂[p.1, p.2] := by
  ext i; fin_cases i <;> rfl

/-- The reference triangle in $\mathbb{R} \times \mathbb{R}$: the set of the pairs $(x, y)$ with
$x > 0$, $y > 0$ and $x + y < 1$. -/
def planeTriangle : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

/-- The reference triangle in $\mathbb{R} \times \mathbb{R}$ is measurable. -/
theorem measurableSet_planeTriangle : MeasurableSet planeTriangle :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const))

/-- The reference triangle of $\mathbb{R}^2$ corresponds to the reference triangle of
$\mathbb{R} \times \mathbb{R}$ under the equivalence `EuclideanSpace.planeMeasurableEquiv`. -/
theorem preimage_referenceTriangle :
    planeMeasurableEquiv.symm ⁻¹' (referenceTriangle : Set 𝔼₂) = planeTriangle := by
  ext p
  exact Iff.rfl

/-- For $x \in \mathbb{R}$ and $k : \mathbb{R} \to \mathbb{R}$, the integral over $y$ of $k$ times
the indicator of $\{y : x > 0, y > 0, x + y < 1\}$ is $\int_0^{1-x} k(y) \, dy$ if $0 < x < 1$,
and $0$ otherwise. -/
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

/-- The indicator of the reference triangle of $\mathbb{R} \times \mathbb{R}$ at $(x, y)$, written
as an indicator in $y$ for fixed $x$. -/
theorem indicator_planeTriangle (g : ℝ × ℝ → ℝ) (x y : ℝ) :
    planeTriangle.indicator g (x, y)
      = {y : ℝ | 0 < x ∧ 0 < y ∧ x + y < 1}.indicator (fun y ↦ g (x, y)) y := rfl

/-- The indicator of the reference triangle of $\mathbb{R} \times \mathbb{R}$ at $(x, y)$, written
as an indicator in $x$ for fixed $y$. -/
theorem indicator_planeTriangle' (g : ℝ × ℝ → ℝ) (x y : ℝ) :
    planeTriangle.indicator g (x, y)
      = {x : ℝ | 0 < y ∧ 0 < x ∧ y + x < 1}.indicator (fun x ↦ g (x, y)) x := by
  by_cases h : (x, y) ∈ planeTriangle
  · rw [indicator_of_mem h, indicator_of_mem (show x ∈ {x : ℝ | 0 < y ∧ 0 < x ∧ y + x < 1} from
      ⟨h.2.1, h.1, by linarith [h.2.2]⟩)]
  · rw [indicator_of_notMem h,
      indicator_of_notMem
        (fun (h' : x ∈ {x : ℝ | 0 < y ∧ 0 < x ∧ y + x < 1}) ↦
          h ⟨h'.2.1, h'.1, by linarith [h'.2.2]⟩)]

/-- Fubini's theorem on the reference triangle of $\mathbb{R} \times \mathbb{R}$, with $x$ outside:
for $g$ integrable on the triangle, its integral over the triangle is
$\int_0^1 \int_0^{1-x} g(x, y) \, dy \, dx$. -/
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

/-- Fubini's theorem on the reference triangle of $\mathbb{R} \times \mathbb{R}$, with $y$ outside:
for $g$ integrable on the triangle, its integral over the triangle is
$\int_0^1 \int_0^{1-y} g(x, y) \, dx \, dy$. -/
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

/-- Fubini's theorem on the reference triangle $\hat T = \{(x, y) : x > 0, y > 0, x + y < 1\}$ of
$\mathbb{R}^2$, with $x$ outside. Let $h : \mathbb{R}^2 \to \mathbb{R}$ be integrable on
$\hat T$. Then $$\int_{\hat T} h = \int_0^1 \int_0^{1-x} h(x, y) \, dy \, dx.$$
-/
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

/-- Fubini's theorem on the reference triangle $\hat T$ of $\mathbb{R}^2$, with $y$ outside: for $h$
integrable on $\hat T$, $\int_{\hat T} h = \int_0^1 \int_0^{1-y} h(x, y) \, dx \, dy$. -/
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

/-- If $f, g : \mathbb{R} \to \mathbb{R}$ are continuous, then
$y \mapsto (f(y), g(y)) \in \mathbb{R}^2$ is continuous. -/
theorem continuous_toLp₂ {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y ↦ (!₂[f y, g y] : 𝔼₂) := by
  have : (fun y ↦ (!₂[f y, g y] : 𝔼₂))
      = (WithLp.toLp 2 : (Fin 2 → ℝ) → 𝔼₂) ∘ fun y ↦ ![f y, g y] := rfl
  rw [this]
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 ↦ ℝ)).comp (continuous_pi fun i ↦ ?_)
  fin_cases i <;> simpa

/-- The vertical line $y \mapsto (x, y)$ has derivative $e_1$ at every point. -/
theorem hasDerivAt_toLp_snd (x y : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (!₂[x, y] : 𝔼₂)) (EuclideanSpace.single 1 1) y := by
  have : (fun y : ℝ ↦ (!₂[x, y] : 𝔼₂)) = fun y ↦ !₂[x, 0] + y • EuclideanSpace.single 1 1 := by
    funext y; ext i; fin_cases i <;> simp
  rw [this]
  simpa using ((hasDerivAt_id y).smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))).const_add
    (!₂[x, 0] : 𝔼₂)

/-- The horizontal line $x \mapsto (x, y)$ has derivative $e_0$ at every point. -/
theorem hasDerivAt_toLp_fst (x y : ℝ) :
    HasDerivAt (fun x : ℝ ↦ (!₂[x, y] : 𝔼₂)) (EuclideanSpace.single 0 1) x := by
  have : (fun x : ℝ ↦ (!₂[x, y] : 𝔼₂)) = fun x ↦ !₂[0, y] + x • EuclideanSpace.single 0 1 := by
    funext x; ext i; fin_cases i <;> simp
  rw [this]
  simpa using ((hasDerivAt_id x).smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).const_add
    (!₂[0, y] : 𝔼₂)

/-- The divergence of a plane vector field $F = (F_0, F_1)$ is $\operatorname{div} F = \partial_0
F_0 + \partial_1 F_1$. -/
theorem div_eq_two (F : 𝔼₂ → 𝔼₂) (z : 𝔼₂) :
    div F z = fderiv ℝ F z (EuclideanSpace.single 0 1) 0
      + fderiv ℝ F z (EuclideanSpace.single 1 1) 1 := by
  simp [div, Fin.sum_univ_two]

/-- The point $(x, y)$ lies in the reference triangle if and only if $x > 0$, $y > 0$ and
$x + y < 1$. -/
theorem mem_referenceTriangle_toLp {x y : ℝ} :
    (!₂[x, y] : 𝔼₂) ∈ (referenceTriangle : Set 𝔼₂) ↔ 0 < x ∧ 0 < y ∧ x + y < 1 := Iff.rfl

/-- The point $(x, y)$ lies in the closed reference triangle if and only if $x \ge 0$, $y \ge 0$ and
$x + y \le 1$. -/
theorem mem_closedReferenceTriangle_toLp {x y : ℝ} :
    (!₂[x, y] : 𝔼₂) ∈ closedReferenceTriangle ↔ 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 := Iff.rfl

/-- The fundamental theorem of calculus along a coordinate line of the reference triangle. Let
$F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on the closed reference triangle and of class
$C^1$ up to the boundary on the open reference triangle $\hat T$, and let $i \in \{0, 1\}$. Let
$\gamma : \mathbb{R} \to \mathbb{R}^2$ be continuous with $\gamma'(t) = e_i$ for every $t$, and
let $L \ge 0$. Suppose that $\gamma(t) \in \hat T$ for $0 < t < L$ and that $\gamma(t)$ lies in
the closed reference triangle for $0 \le t \le L$. Then $$\int_0^L \partial_i F_i(\gamma(t)) \,
dt = F_i(\gamma(L)) - F_i(\gamma(0)).$$

"Of class $C^1$ up to the boundary" is `ContDiffOnClosure ℝ 1 F referenceTriangle`. The partial
derivative $\partial_i F_i(z)$ is the $i$-th coordinate of `fderiv ℝ F z` applied to $e_i$. -/
theorem integral_fderiv_comp_line {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F closedReferenceTriangle)
    (hF' : ContDiffOnClosure ℝ 1 F referenceTriangle) (i : Fin 2) {γ : ℝ → 𝔼₂}
    (hγc : Continuous γ) (hγ : ∀ t, HasDerivAt γ (EuclideanSpace.single i 1) t) {L : ℝ}
    (hL : 0 ≤ L) (hmem : ∀ t ∈ Ioo 0 L, γ t ∈ (referenceTriangle : Set 𝔼₂))
    (hmemc : ∀ t ∈ Icc 0 L, γ t ∈ closedReferenceTriangle) :
    ∫ t in (0 : ℝ)..L, fderiv ℝ F (γ t) (EuclideanSpace.single i 1) i = F (γ L) i - F (γ 0) i := by
  obtain ⟨C, hC⟩ := hF'.exists_norm_fderiv_le isBounded_referenceTriangle
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun t ↦ F (γ t) i) hL ?_ ?_ ?_
  · exact (EuclideanSpace.proj i).continuous.comp_continuousOn
      (hF.comp hγc.continuousOn fun t ht ↦ hmemc t ht)
  · intro t ht
    have hd : DifferentiableAt ℝ F (γ t) :=
      (hF'.contDiffOn.differentiableOn one_ne_zero).differentiableAt
        (referenceTriangle.isOpen.mem_nhds (hmem t ht))
    exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t
      (hd.hasFDerivAt.comp_hasDerivAt t (hγ t))
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL]
    refine Measure.integrableOn_of_bounded (M := C) (by simp)
      ((measurable_fderiv_apply_apply F _ i).comp hγc.measurable).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun t ht ↦ norm_fderiv_apply_apply_le (hC _ (hmem t ht)) i i

/-- The fundamental theorem of calculus on a vertical slice of the reference triangle. Let
$F = (F_0, F_1)$ be continuous on the closed reference triangle and of class $C^1$ up to the
boundary on the open one, and let $0 < x < 1$. Then $$\int_0^{1-x} \partial_1 F_1(x, y) \, dy =
F_1(x, 1 - x) - F_1(x, 0).$$
-/
theorem integral_fderiv_snd {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F closedReferenceTriangle)
    (hF' : ContDiffOnClosure ℝ 1 F referenceTriangle) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ y in (0 : ℝ)..(1 - x), fderiv ℝ F !₂[x, y] (EuclideanSpace.single 1 1) 1
      = F !₂[x, 1 - x] 1 - F !₂[x, 0] 1 :=
  integral_fderiv_comp_line hF hF' 1 (γ := fun y ↦ !₂[x, y])
    (continuous_toLp₂ continuous_const continuous_id)
    (hasDerivAt_toLp_snd x) (by linarith [hx.2])
    (fun y hy ↦ mem_referenceTriangle_toLp.2 ⟨hx.1, hy.1, by linarith [hy.2]⟩)
    (fun y hy ↦ mem_closedReferenceTriangle_toLp.2 ⟨hx.1.le, hy.1, by linarith [hy.2]⟩)

/-- The fundamental theorem of calculus on a horizontal slice of the reference triangle: under the
hypotheses of `EuclideanSpace.integral_fderiv_snd` and for $0 < y < 1$, $\int_0^{1-y} \partial_0
F_0(x, y) \, dx = F_0(1 - y, y) - F_0(0, y)$. -/
theorem integral_fderiv_fst {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F closedReferenceTriangle)
    (hF' : ContDiffOnClosure ℝ 1 F referenceTriangle) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..(1 - y), fderiv ℝ F !₂[x, y] (EuclideanSpace.single 0 1) 0
      = F !₂[1 - y, y] 0 - F !₂[0, y] 0 :=
  integral_fderiv_comp_line hF hF' 0 (γ := fun x ↦ !₂[x, y])
    (continuous_toLp₂ continuous_id continuous_const)
    (fun x ↦ hasDerivAt_toLp_fst x y) (by linarith [hy.2])
    (fun x hx ↦ mem_referenceTriangle_toLp.2 ⟨hx.1, hy.1, by linarith [hx.2]⟩)
    (fun x hx ↦ mem_closedReferenceTriangle_toLp.2 ⟨hx.1, hy.1.le, by linarith [hx.2]⟩)

/-- Let $F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on the closed reference triangle, and let
$f, g : \mathbb{R} \to \mathbb{R}$ be continuous with $(f(t), g(t))$ in the closed reference
triangle for $t \in [0, 1]$. Then each coordinate of $t \mapsto F(f(t), g(t))$ is interval
integrable on $[0, 1]$. -/
theorem intervalIntegrable_comp_toLp {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F closedReferenceTriangle)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t ∧ 0 ≤ g t ∧ f t + g t ≤ 1) (i : Fin 2) :
    IntervalIntegrable (fun t ↦ F !₂[f t, g t] i) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  exact (EuclideanSpace.proj i).continuous.comp_continuousOn
    (hF.comp (continuous_toLp₂ hf hg).continuousOn fun t ht ↦
      mem_closedReferenceTriangle_toLp.2 (h t ht))

/-- The divergence theorem on the reference triangle, with parametrized edges. Let
$F = (F_0, F_1) : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on the closed reference triangle
and of class $C^1$ up to the boundary on the open reference triangle $\hat T$. Then $$\int_{\hat
T} \operatorname{div} F = \int_0^1 \bigl(F_0 + F_1\bigr)(t, 1 - t) \, dt - \int_0^1 F_1(t, 0) \,
dt - \int_0^1 F_0(0, t) \, dt.$$

The three terms on the right are the edge terms $\int_e \langle F, \nu \rangle \, ds$ of the
hypotenuse, where $\nu = (1, 1)/\sqrt 2$ and $ds = \sqrt 2 \, dt$, of the bottom edge, where
$\nu = (0, -1)$, and of the left edge, where $\nu = (-1, 0)$. The proof applies Fubini's theorem
on the triangle and the fundamental theorem of calculus on each slice. -/
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
    rw [← intervalIntegral.integral_comp_one_sub (fun t ↦ F !₂[t, 1 - t] 0)]
    simp only [sub_sub_cancel]
  rw [e0, e1, intervalIntegral.integral_sub c1 c2, intervalIntegral.integral_sub c3 c4, e2,
    intervalIntegral.integral_add c5 c3]
  ring

/-- The vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ of the reference triangle are not collinear. -/
theorem linearIndependent_referenceTriangleVertex :
    LinearIndependent ℝ ![referenceTriangleVertex 1 - referenceTriangleVertex 0,
      referenceTriangleVertex 2 - referenceTriangleVertex 0] := by
  rw [linearIndependent_pair_iff_inner_perp_ne_zero, inner_perp_eq]
  simp [referenceTriangleVertex]

/-- The affine map `EuclideanSpace.triangleAffine` for the vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ of
the reference triangle is the identity. -/
theorem triangleAffine_referenceTriangleVertex_eq_id :
    triangleAffine (referenceTriangleVertex 0) (referenceTriangleVertex 1)
      (referenceTriangleVertex 2) = id := by
  funext x
  ext i
  fin_cases i <;> simp [triangleAffine, referenceTriangleVertex]

/-- The closed triangle with the vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ is the closed reference
triangle. -/
theorem closedTriangle_referenceTriangleVertex :
    closedTriangle (referenceTriangleVertex 0) (referenceTriangleVertex 1)
      (referenceTriangleVertex 2) = closedReferenceTriangle := by
  rw [closedTriangle, triangleAffine_referenceTriangleVertex_eq_id, image_id]

/-- The open triangle with the vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ is the reference triangle. -/
theorem openTriangle_referenceTriangleVertex :
    openTriangle (referenceTriangleVertex 0) (referenceTriangleVertex 1)
      (referenceTriangleVertex 2) = referenceTriangle := by
  rw [openTriangle_eq_image_triangleAffine, triangleAffine_referenceTriangleVertex_eq_id, image_id]

/-- The bottom edge of the reference triangle, from $(0, 0)$ to $(1, 0)$, is parametrized by
$t \mapsto (t, 0)$. -/
theorem lineMap_referenceTriangleVertex₀₁ (t : ℝ) :
    AffineMap.lineMap (referenceTriangleVertex 0) (referenceTriangleVertex 1) t = !₂[t, 0] := by
  ext i; fin_cases i <;> simp [lineMap_eq, referenceTriangleVertex]

/-- The hypotenuse of the reference triangle, from $(1, 0)$ to $(0, 1)$, is parametrized by
$t \mapsto (1 - t, t)$. -/
theorem lineMap_referenceTriangleVertex₁₂ (t : ℝ) :
    AffineMap.lineMap (referenceTriangleVertex 1) (referenceTriangleVertex 2) t
      = !₂[1 - t, t] := by
  ext i; fin_cases i
  · simp [lineMap_eq, referenceTriangleVertex]; ring
  · simp [lineMap_eq, referenceTriangleVertex]

/-- The left edge of the reference triangle, from $(0, 1)$ to $(0, 0)$, is parametrized by
$t \mapsto (0, 1 - t)$. -/
theorem lineMap_referenceTriangleVertex₂₀ (t : ℝ) :
    AffineMap.lineMap (referenceTriangleVertex 2) (referenceTriangleVertex 0) t
      = !₂[0, 1 - t] := by
  ext i; fin_cases i
  · simp [lineMap_eq, referenceTriangleVertex]
  · simp [lineMap_eq, referenceTriangleVertex]; ring

/-- The divergence theorem on the reference triangle, with the boundary measure. Let $v_0 = (0, 0)$,
$v_1 = (1, 0)$, $v_2 = (0, 1)$, and let $\sigma$ and $\nu$ be the boundary measure and the
outward normal of the triangle $v_0 v_1 v_2$. Let $F : \mathbb{R}^2 \to \mathbb{R}^2$ be
continuous on the closed reference triangle and of class $C^1$ up to the boundary on the open
reference triangle $\hat T$. Then $$\int_{\hat T} \operatorname{div} F = \int \langle F, \nu
\rangle \, d\sigma.$$

The vertices are `EuclideanSpace.referenceTriangleVertex`. The measure $\sigma$ is
`EuclideanSpace.triangleBoundaryMeasure`.
The normal $\nu$ is `EuclideanSpace.triangleNormal`. -/
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
    rw [← intervalIntegral.integral_comp_one_sub (fun t ↦ F !₂[t, 1 - t] 0 + F !₂[t, 1 - t] 1)]
    simp only [sub_sub_cancel]
  have e2 : ∫ t in (0 : ℝ)..1, -F !₂[0, 1 - t] 0 = -∫ t in (0 : ℝ)..1, F !₂[0, t] 0 := by
    rw [intervalIntegral.integral_neg,
      ← intervalIntegral.integral_comp_one_sub (fun t ↦ F !₂[0, t] 0)]
  rw [e1, e2, intervalIntegral.integral_neg]
  ring

/-! ### The divergence theorem on a triangle -/

/-- The **divergence theorem on a triangle**. Let $A, B, C \in \mathbb{R}^2$ be noncollinear, let
$K$ be the open triangle $ABC$, and let $\sigma$ and $\nu$ be its boundary measure and its
outward normal. Let $F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on the closed triangle and
of class $C^1$ up to the boundary on $K$. Then $$\int_K \operatorname{div} F = \int \langle F,
\nu \rangle \, d\sigma.$$

The proof is an affine change of variables from the reference triangle. Let $M$ be
`EuclideanSpace.triangleEquiv A B C h` and $\Phi(\hat x) = M \hat x + A$. The change of
variables gives $|\det M| \int_{\hat T} (\operatorname{div} F) \circ \Phi$. The Piola identity
`EuclideanSpace.div_comp_continuousLinearEquiv` turns the integrand into
$\operatorname{div}(M^{-1} \circ F \circ \Phi)$, the theorem on the reference triangle applies
to this field, and `EuclideanSpace.integral_inner_edgeNormal_affine` carries each edge term back
to $K$. -/
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

/-- The **boundary data of a triangle**. For noncollinear $A, B, C \in \mathbb{R}^2$, the open
triangle $ABC$ is a `BoundaryData`, with the boundary measure
`EuclideanSpace.triangleBoundaryMeasure A B C` as surface measure and
`EuclideanSpace.triangleNormal A B C` as outward unit normal.

The divergence theorem of the structure is `EuclideanSpace.integral_div_openTriangle`. -/
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

/-- The surface measure of the boundary data of a triangle is its boundary measure. -/
@[simp] theorem triangleBoundaryData_σ (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    (triangleBoundaryData A B C h).σ = triangleBoundaryMeasure A B C := rfl

/-- The normal of the boundary data of a triangle is its outward normal. -/
@[simp] theorem triangleBoundaryData_ν (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    (triangleBoundaryData A B C h).ν = triangleNormal A B C := rfl

/-! ### Segments and edges of a triangle, rotated -/

/-- For a vertex triple $T_0, T_1, T_2$ and every $a$ modulo $3$, the arclength measure
$\sigma_{T_a T_{a+1}}$ of the edge $a$ is at most the boundary measure of the triangle
$T_0 T_1 T_2$. -/
theorem edgeMeasure_le_triangleBoundaryMeasure (T : Fin 3 → 𝔼₂) (a : Fin 3) :
    edgeMeasure (T a) (T (a + 1)) ≤ triangleBoundaryMeasure (T 0) (T 1) (T 2) := by
  unfold triangleBoundaryMeasure
  fin_cases a
  · exact Measure.le_add_right (Measure.le_add_right le_rfl)
  · exact Measure.le_add_right (Measure.le_add_left le_rfl)
  · exact Measure.le_add_left le_rfl

/-- Let $T_0, T_1, T_2$ be noncollinear and let $a$ be an index modulo $3$. On the open edge
$(T_a, T_{a+1})$, the outward normal of the triangle $T_0 T_1 T_2$ is the edge normal
$n_{T_a T_{a+1} T_{a+2}}$. -/
theorem triangleNormal_eq_of_mem_openSegment_rot {T : Fin 3 → 𝔼₂}
    (h : LinearIndependent ℝ ![T 1 - T 0, T 2 - T 0]) (a : Fin 3) {x : 𝔼₂}
    (hx : x ∈ openSegment ℝ (T a) (T (a + 1))) :
    triangleNormal (T 0) (T 1) (T 2) x = edgeNormal (T a) (T (a + 1)) (T (a + 2)) := by
  fin_cases a
  · exact triangleNormal_eq_of_mem_openSegment₀₁ hx
  · exact triangleNormal_eq_of_mem_openSegment₁₂ h hx
  · exact triangleNormal_eq_of_mem_openSegment₂₀ h hx

/-- For a vertex triple $T_0, T_1, T_2$ and every $a$ modulo $3$, the edge $[T_a, T_{a+1}]$ lies in
the closed triangle $T_0 T_1 T_2$. -/
theorem segment_subset_closedTriangle_rot (T : Fin 3 → 𝔼₂) (a : Fin 3) :
    segment ℝ (T a) (T (a + 1)) ⊆ closedTriangle (T 0) (T 1) (T 2) := by
  fin_cases a
  · exact segment_subset_closedTriangle (T 0) (T 1) (T 2) 0 1
  · exact segment_subset_closedTriangle (T 0) (T 1) (T 2) 1 2
  · exact segment_subset_closedTriangle (T 0) (T 1) (T 2) 2 0

/-- The boundary integral of $f \nu_i$ on a triangle is the sum of three edge integrals. Let
$T_0, T_1, T_2$ be noncollinear, let $\sigma$ and $\nu$ be the boundary measure and the outward
normal of the triangle $T_0 T_1 T_2$, let $f : \mathbb{R}^2 \to \mathbb{R}$ be integrable for
$\sigma$, and let $i \in \{0, 1\}$. Then $$\int f \, \nu_i \, d\sigma = \sum_{a=0}^{2} \int f \,
(n_{T_a T_{a+1} T_{a+2}})_i \, d\sigma_{T_a T_{a+1}},$$ with indices modulo $3$. In each edge
integral the normal is constant. -/
theorem integral_mul_triangleNormal_apply {T : Fin 3 → 𝔼₂}
    (h : LinearIndependent ℝ ![T 1 - T 0, T 2 - T 0]) {f : 𝔼₂ → ℝ}
    (hf : Integrable f (triangleBoundaryMeasure (T 0) (T 1) (T 2))) (i : Fin 2) :
    ∫ x, f x * triangleNormal (T 0) (T 1) (T 2) x i ∂triangleBoundaryMeasure (T 0) (T 1) (T 2)
      = ∑ a : Fin 3, ∫ x, f x * edgeNormal (T a) (T (a + 1)) (T (a + 2)) i
          ∂edgeMeasure (T a) (T (a + 1)) := by
  have hfν := (triangleBoundaryData (T 0) (T 1) (T 2) h).integrable_mul_ν_apply hf i
  have key : ∀ a : Fin 3, ∫ x, f x * triangleNormal (T 0) (T 1) (T 2) x i
      ∂edgeMeasure (T a) (T (a + 1))
      = ∫ x, f x * edgeNormal (T a) (T (a + 1)) (T (a + 2)) i ∂edgeMeasure (T a) (T (a + 1)) :=
    fun a ↦ integral_congr_ae ((ae_mem_openSegment
      ((EuclideanSpace.vertex_injective h).ne (fin3_ne_add_one a))).mono fun x hx ↦ by
        dsimp only; rw [triangleNormal_eq_of_mem_openSegment_rot h a hx])
  rw [Fin.sum_univ_three, ← key 0, ← key 1, ← key 2]
  exact integral_triangleBoundaryMeasure
    (hfν.mono_measure (edgeMeasure_le_triangleBoundaryMeasure T 0))
    (hfν.mono_measure (edgeMeasure_le_triangleBoundaryMeasure T 1))
    (hfν.mono_measure (edgeMeasure_le_triangleBoundaryMeasure T 2))

end EuclideanSpace

/-! ### Triangulations: boundary edges and partners -/

namespace Triangulation

open EuclideanSpace

variable {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)

/-- A **boundary edge** of a triangulation $\mathcal{T}$. The edge $a$ of the element $T$, the
segment $[T_a, T_{a+1}]$, is a boundary edge if no other element $T' \neq T$ has both $T_a$ and
$T_{a+1}$ among its vertices. -/
def IsBoundaryEdge (T : 𝒯.elems) (a : Fin 3) : Prop :=
  ∀ T' : 𝒯.elems, T' ≠ T → ∀ i j : Fin 3, ¬ (T.1 a = T'.1 i ∧ T.1 (a + 1) = T'.1 j)

/-- A **partner** of an edge. The edge $a'$ of the element $T'$ is a partner of the edge $a$ of the
element $T$ if $T' \neq T$ and the two edges have the same endpoints, in the same or in the
opposite order: $(T_a, T_{a+1}) = (T'_{a'}, T'_{a'+1})$ or
$(T_a, T_{a+1}) = (T'_{a'+1}, T'_{a'})$. -/
def IsPartner (T : 𝒯.elems) (a : Fin 3) (T' : 𝒯.elems) (a' : Fin 3) : Prop :=
  T' ≠ T ∧ ((T.1 a = T'.1 a' ∧ T.1 (a + 1) = T'.1 (a' + 1)) ∨
    (T.1 a = T'.1 (a' + 1) ∧ T.1 (a + 1) = T'.1 a'))

open Classical in
/-- The finite set of the boundary edges of the triangulation, as pairs $(T, a)$ of an element and
an edge index. -/
def boundaryEdges : Finset (𝒯.elems × Fin 3) :=
  Finset.univ.filter fun e ↦ 𝒯.IsBoundaryEdge e.1 e.2

variable {𝒯}

/-- A pair $(T, a)$ lies in `Triangulation.boundaryEdges` if and only if the edge $a$ of $T$ is a
boundary edge. -/
theorem mem_boundaryEdges {e : 𝒯.elems × Fin 3} :
    e ∈ 𝒯.boundaryEdges ↔ 𝒯.IsBoundaryEdge e.1 e.2 := by
  classical
  simp [boundaryEdges]

/-- The three vertices of an element of a triangulation are distinct. -/
theorem vertex_injective (T : 𝒯.elems) : Function.Injective T.1 :=
  EuclideanSpace.vertex_injective (𝒯.li T)

/-- For an element $T$ of a triangulation and every $a$ modulo $3$, the vectors $T_{a+1} - T_a$ and
$T_{a+2} - T_a$ are linearly independent. -/
theorem li_rot (T : 𝒯.elems) (a : Fin 3) :
    LinearIndependent ℝ ![T.1 (a + 1) - T.1 a, T.1 (a + 2) - T.1 a] :=
  linearIndependent_rot (𝒯.li T) a

/-- For an element $T$ of a triangulation and every $a$ modulo $3$, the open element of $T$ is the
open triangle $T_a T_{a+1} T_{a+2}$. -/
theorem K_eq_rot (T : 𝒯.elems) (a : Fin 3) :
    𝒯.K T = openTriangle (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) :=
  openTriangle_eq_rot T.1 a

/-- For an element $T$ of a triangulation and every $a$ modulo $3$, the closed element of $T$ is the
closed triangle $T_a T_{a+1} T_{a+2}$. -/
theorem closedK_eq_rot (T : 𝒯.elems) (a : Fin 3) :
    𝒯.closedK T = closedTriangle (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) :=
  closedTriangle_eq_rot T.1 a

/-- The endpoints $T_a$ and $T_{a+1}$ of an edge of an element are distinct. -/
theorem vertex_ne_vertex_add_one (T : 𝒯.elems) (a : Fin 3) : T.1 a ≠ T.1 (a + 1) :=
  fun e ↦ fin3_ne_add_one a (vertex_injective T e)

/-- The vertex $T_c$ of an element is the entry at the index $c - a$ of the vertex triple
$(T_a, T_{a+1}, T_{a+2})$, with indices modulo $3$. -/
theorem vertex_eq_vecCons_rot (T : 𝒯.elems) (a c : Fin 3) :
    T.1 c = ![T.1 a, T.1 (a + 1), T.1 (a + 2)] (c - a) := by
  rw [vecCons_rot, add_sub_cancel]

/-- The partner relation is symmetric: if the edge $a'$ of $T'$ is a partner of the edge $a$ of $T$,
then the edge $a$ of $T$ is a partner of the edge $a'$ of $T'$. -/
theorem IsPartner.symm {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    𝒯.IsPartner T' a' T a := by
  obtain ⟨hne, h | h⟩ := h
  · exact ⟨hne.symm, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
  · exact ⟨hne.symm, Or.inr ⟨h.2.symm, h.1.symm⟩⟩

/-- The edge $a$ of an element $T$ is not a boundary edge if and only if it has a partner, that is,
an element $T'$ and an index $a'$ such that the edge $a'$ of $T'$ is a partner of the edge $a$
of $T$. -/
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

/-- An edge that has a partner is not a boundary edge. -/
theorem IsPartner.not_isBoundaryEdge {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') : ¬ 𝒯.IsBoundaryEdge T a :=
  (not_isBoundaryEdge_iff_exists_partner T a).2 ⟨T', a', h⟩

/-- If the edge $a'$ of $T'$ is a partner of the edge $a$ of $T$, then $T_{a+1} - T_a$ and
$T'_{a'+2} - T_a$ are linearly independent: the triangle formed by the edge of $T$ and the third
vertex of $T'$ is nondegenerate. -/
theorem IsPartner.li {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    LinearIndependent ℝ ![T.1 (a + 1) - T.1 a, T'.1 (a' + 2) - T.1 a] := by
  have hli' := 𝒯.li_rot T' a'
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rwa [← h1, ← h2] at hli'
  · rw [← h1, ← h2] at hli'
    exact linearIndependent_swap hli'

/-- If the edge $a'$ of $T'$ is a partner of the edge $a$ of $T$, then the open element of $T'$ is
the open triangle $T_a T_{a+1} T'_{a'+2}$, formed by the edge of $T$ and the third vertex of
$T'$. -/
theorem IsPartner.K_eq {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    𝒯.K T' = openTriangle (T.1 a) (T.1 (a + 1)) (T'.1 (a' + 2)) := by
  rw [K_eq_rot T' a']
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [h1, h2]
  · rw [h1, h2, openTriangle_swap]

/-- The partner lies on the other side of the edge. If the edge $a'$ of $T'$ is a partner of the
edge $a$ of $T$, then the third vertices $T_{a+2}$ and $T'_{a'+2}$ lie strictly on opposite
sides of the line through the edge: $$s(T_a, T_{a+1}, T_{a+2}) \, s(T_a, T_{a+1}, T'_{a'+2}) <
0.$$

If they were on the same side, the two open elements would meet
(`EuclideanSpace.openTriangle_inter_nonempty_of_same_side`), against the disjointness of
distinct open elements. -/
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

/-- The **partner of an interior edge is unique**. If the edge $a'$ of $T'$ and the edge $a''$ of
$T''$ are both partners of the edge $a$ of $T$, then $T'' = T'$ and $a'' = a'$.

Both partners lie on the far side of the edge from $T$
(`Triangulation.IsPartner.inner_perp_mul_neg`), hence on the same side of it, hence their open
elements meet and the elements coincide. The edge index is then determined because the vertices
of an element are distinct. -/
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

/-- A partner edge has the same arclength measure: if the edge $a'$ of $T'$ is a partner of the edge
$a$ of $T$, then $\sigma_{T'_{a'} T'_{a'+1}} = \sigma_{T_a T_{a+1}}$. -/
theorem IsPartner.edgeMeasure_eq {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    edgeMeasure (T'.1 a') (T'.1 (a' + 1)) = edgeMeasure (T.1 a) (T.1 (a + 1)) := by
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [← h1, ← h2]
  · rw [← h1, ← h2, edgeMeasure_symm]

/-- A partner edge has the opposite outward normal: if the edge $a'$ of $T'$ is a partner of the
edge $a$ of $T$, then $n_{T'_{a'} T'_{a'+1} T'_{a'+2}} = -n_{T_a T_{a+1} T_{a+2}}$. -/
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

/-- A partner of an edge that is not a boundary edge, chosen by the axiom of choice. -/
def partner (T : 𝒯.elems) (a : Fin 3) (h : ¬ 𝒯.IsBoundaryEdge T a) : 𝒯.elems × Fin 3 :=
  (((not_isBoundaryEdge_iff_exists_partner T a).1 h).choose,
    ((not_isBoundaryEdge_iff_exists_partner T a).1 h).choose_spec.choose)

/-- The chosen partner `Triangulation.partner T a h` is a partner of the edge $a$ of $T$. -/
theorem isPartner_partner (T : 𝒯.elems) (a : Fin 3) (h : ¬ 𝒯.IsBoundaryEdge T a) :
    𝒯.IsPartner T a (partner T a h).1 (partner T a h).2 :=
  ((not_isBoundaryEdge_iff_exists_partner T a).1 h).choose_spec.choose_spec

/-! ### Boundary edges lie in the frontier -/

/-- Let $T' \neq T$ be elements of a triangulation, and let $x$ be a point of the open edge
$(T_a, T_{a+1})$ that lies in the closed element of $T'$. Then both endpoints $T_a$ and
$T_{a+1}$ are vertices of $T'$.

This follows from the conformity axiom of `Triangulation`. -/
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

/-- A **boundary edge lies in** $\partial\Omega$. If the edge $a$ of the element $T$ is a boundary
edge of a triangulation of $\Omega$, then the segment $[T_a, T_{a+1}]$ lies in the frontier of
$\Omega$.

The proof uses only the axioms of `Triangulation`. Suppose a point $x$ of the open edge lies in
$\Omega$. If $x$ lies in another closed element, that element shares the edge by conformity,
against the hypothesis. Otherwise $x$ has a neighbourhood in $\Omega$ that misses every other
closed element, so the neighbourhood lies in the closed element of $T$; the point
$x - \varepsilon(T_{a+2} - T_a)$ beyond the edge contradicts this. -/
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

/-- Distinct boundary edges have disjoint relative interiors. If the edge $a$ of $T$ and the edge
$a'$ of $T'$ are boundary edges and $(T, a) \neq (T', a')$, then the open segments
$(T_a, T_{a+1})$ and $(T'_{a'}, T'_{a'+1})$ are disjoint.

Two open edges of one element are disjoint by the uniqueness of barycentric coordinates. A point
of an open edge of $T$ in another closed element makes that edge shared
(`Triangulation.exists_eq_vertex_of_mem_closedK`). -/
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

/-- The **surface measure of a triangulated domain**: the sum $$\sigma = \sum_{(T, a)} \sigma_{T_a
T_{a+1}}$$ of the arclength measures of all boundary edges $(T, a)$ of the triangulation. -/
def boundaryMeasure : Measure 𝔼₂ :=
  ∑ e ∈ 𝒯.boundaryEdges, edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1))

/-- The surface measure of a triangulated domain is finite. -/
instance isFiniteMeasure_boundaryMeasure : IsFiniteMeasure 𝒯.boundaryMeasure :=
  ⟨by
    rw [boundaryMeasure, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.2 fun e _ ↦ measure_lt_top _ _⟩

/-- The surface measure of a triangulated domain is carried by $\partial\Omega$: the complement of
$\partial\Omega$ has measure zero. -/
theorem boundaryMeasure_compl_frontier : 𝒯.boundaryMeasure (frontier (Ω : Set 𝔼₂))ᶜ = 0 := by
  rw [boundaryMeasure, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun e he ↦ measure_mono_null (compl_subset_compl.2 ?_)
    (edgeMeasure_compl_segment _ _)
  exact segment_subset_frontier_of_isBoundaryEdge (mem_boundaryEdges.1 he)

/-- Let $f : \mathbb{R}^2 \to \mathbb{R}$ be integrable for the arclength measure of every boundary
edge. Then the integral of $f$ for the surface measure is the sum over the boundary edges
$(T, a)$ of $\int f \, d\sigma_{T_a T_{a+1}}$. -/
theorem integral_boundaryMeasure {f : 𝔼₂ → ℝ}
    (hf : ∀ e ∈ 𝒯.boundaryEdges, Integrable f (edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1)))) :
    ∫ x, f x ∂𝒯.boundaryMeasure
      = ∑ e ∈ 𝒯.boundaryEdges, ∫ x, f x ∂edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1)) :=
  integral_finsetSum_measure hf

/-- Let $U \subseteq \mathbb{R}^2$ be open, and suppose that $U$ meets the open segment
$(T_a, T_{a+1})$ of some boundary edge $(T, a)$. Then $U$ has positive surface measure.

The hypothesis names an edge because, unlike on a $C^1$ domain, an open set that meets
$\partial\Omega$ only at a vertex can have surface measure zero. -/
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
/-- The **outward unit normal of a triangulated domain**. At a point $x$ of the open segment
$(T_a, T_{a+1})$ of a boundary edge $(T, a)$, its value is the edge normal
$n_{T_a T_{a+1} T_{a+2}}$ of that edge in its element. At every other point, including the
vertices and the points off $\partial\Omega$, its value is $0$.

The boundary edge is chosen by the axiom of choice. By
`Triangulation.openSegment_disjoint_of_isBoundaryEdge` it is unique, see
`Triangulation.outwardNormal_eq_edgeNormal`. -/
def outwardNormal : 𝔼₂ → 𝔼₂ := fun x ↦
  if h : ∃ e ∈ 𝒯.boundaryEdges, x ∈ openSegment ℝ (e.1.1 e.2) (e.1.1 (e.2 + 1)) then
    edgeNormal (h.choose.1.1 h.choose.2) (h.choose.1.1 (h.choose.2 + 1))
      (h.choose.1.1 (h.choose.2 + 2))
  else 0

variable {𝒯}

/-- If $(T, a)$ is a boundary edge and $x$ lies on the open segment $(T_a, T_{a+1})$, then the
outward normal at $x$ is the edge normal $n_{T_a T_{a+1} T_{a+2}}$.

The boundary edge through $x$ is unique by
`Triangulation.openSegment_disjoint_of_isBoundaryEdge`. -/
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

/-- The outward normal of a triangulated domain has norm $1$ almost everywhere for the surface
measure. -/
theorem ae_norm_outwardNormal : ∀ᵐ x ∂𝒯.boundaryMeasure, ‖𝒯.outwardNormal x‖ = 1 := by
  rw [boundaryMeasure, ae_finsetSum_measure_iff]
  intro e he
  refine (ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)).mono fun x hx ↦ ?_
  rw [outwardNormal_eq_edgeNormal (mem_boundaryEdges.1 he) hx]
  exact norm_edgeNormal ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (𝒯.li_rot e.1 e.2))

/-- The outward normal of a triangulated domain is almost everywhere strongly measurable for the
surface measure. -/
theorem aestronglyMeasurable_outwardNormal :
    AEStronglyMeasurable 𝒯.outwardNormal 𝒯.boundaryMeasure := by
  rw [boundaryMeasure]
  refine aestronglyMeasurable_finsetSum_measure fun e he ↦
    (aestronglyMeasurable_const
      (b := edgeNormal (e.1.1 e.2) (e.1.1 (e.2 + 1)) (e.1.1 (e.2 + 2)))).congr ?_
  exact (ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)).mono fun x hx ↦
    (outwardNormal_eq_edgeNormal (mem_boundaryEdges.1 he) hx).symm

/-! ### The divergence theorem on a triangulated domain -/

/-- The **edge term** of the divergence theorem: the flux $\int \langle F, n_{T_a T_{a+1} T_{a+2}}
\rangle \, d\sigma_{T_a T_{a+1}}$ of the field $F$ through the edge $a$ of the element $T$. -/
def edgeTerm (F : 𝔼₂ → 𝔼₂) (T : 𝒯.elems) (a : Fin 3) : ℝ :=
  ∫ x, ⟪F x, edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2))⟫_ℝ ∂edgeMeasure (T.1 a) (T.1 (a + 1))

/-- For an element $T$ and indices $a, b$, the segment $[T_a, T_b]$ lies in the closure of $\Omega$.
-/
theorem segment_subset_closure (T : 𝒯.elems) (a b : Fin 3) :
    segment ℝ (T.1 a) (T.1 b) ⊆ closure (Ω : Set 𝔼₂) :=
  (𝒯.segment_subset_closedK T a b).trans (𝒯.closedK_subset_closure T)

/-- The edge terms of an edge and of its partner cancel: if the edge $a'$ of $T'$ is a partner of
the edge $a$ of $T$, then the sum of their edge terms for $F$ is $0$, for every field $F$. -/
theorem edgeTerm_add_edgeTerm_partner {F : 𝔼₂ → 𝔼₂} {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') : 𝒯.edgeTerm F T a + 𝒯.edgeTerm F T' a' = 0 := by
  unfold edgeTerm
  rw [h.edgeMeasure_eq, h.edgeNormal_eq]
  simp only [inner_neg_right, integral_neg, add_neg_cancel]

/-- The divergence theorem on one element, in edge terms. Let $F$ be continuous on $\bar\Omega$ and
of class $C^1$ up to the boundary on $\Omega$. Then for every element $T$, the integral of
$\operatorname{div} F$ over the open element of $T$ is the sum of the three edge terms of $F$ on
$T$. -/
theorem integral_div_K_eq_sum_edgeTerm {F : 𝔼₂ → 𝔼₂}
    (hF : ContinuousOn F (closure (Ω : Set 𝔼₂))) (hF' : ContDiffOnClosure ℝ 1 F (Ω : Set 𝔼₂))
    (T : 𝒯.elems) : ∫ x in 𝒯.K T, div F x = ∑ a : Fin 3, 𝒯.edgeTerm F T a := by
  have hFT : ContinuousOn F (closedTriangle (T.1 0) (T.1 1) (T.1 2)) :=
    hF.mono (𝒯.closedK_subset_closure T)
  rw [K, integral_div_openTriangle (𝒯.li T) hFT (hF'.mono (𝒯.K_subset T)),
    integral_inner_triangleNormal (𝒯.li T) hFT, Fin.sum_univ_three]
  rfl

open Classical in
/-- A sum over the interior edges vanishes when the terms of partner edges cancel. Let $M$ be an
additive commutative monoid and let $g$ assign an element $g(T, a) \in M$ to each edge $a$ of
each element $T$. If $g(T, a) + g(T', a') = 0$ whenever the edge $a'$ of $T'$ is a partner of
the edge $a$ of $T$, then the sum of $g(T, a)$ over all edges $(T, a)$ that are not boundary
edges is $0$.

The map `Triangulation.partner` is an involution without fixed points on the interior edges. -/
theorem sum_interior_eq_zero_of_add_partner {M : Type*} [AddCommMonoid M]
    (g : 𝒯.elems → Fin 3 → M)
    (hg : ∀ T a T' a', 𝒯.IsPartner T a T' a' → g T a + g T' a' = 0) :
    ∑ e ∈ Finset.univ.filter (fun e : 𝒯.elems × Fin 3 ↦ ¬ 𝒯.IsBoundaryEdge e.1 e.2),
      g e.1 e.2 = 0 := by
  classical
  refine Finset.sum_involution (fun e he ↦ partner e.1 e.2 (Finset.mem_filter.1 he).2)
    (fun e he ↦ ?_) (fun e he _ ↦ ?_) (fun e he ↦ ?_) (fun e he ↦ ?_)
  · exact hg _ _ _ _ (isPartner_partner e.1 e.2 (Finset.mem_filter.1 he).2)
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

open Classical in
/-- The sum of the edge terms of a field $F$ over all interior edges is $0$, for every field $F$.
The map `Triangulation.partner` is an involution without fixed points on the interior edges, and
it changes the sign of the edge term. -/
theorem sum_edgeTerm_interior_eq_zero (F : 𝔼₂ → 𝔼₂) :
    ∑ e ∈ Finset.univ.filter (fun e : 𝒯.elems × Fin 3 ↦ ¬ 𝒯.IsBoundaryEdge e.1 e.2),
      𝒯.edgeTerm F e.1 e.2 = 0 :=
  sum_interior_eq_zero_of_add_partner _ fun _ _ _ _ h ↦ edgeTerm_add_edgeTerm_partner h

variable (𝒯) in
/-- Let $\mathcal{T}$ be a triangulation of $\Omega$ and let $A : \mathbb{R}^2 \to \mathbb{R}$ be
integrable on $\Omega$. Then the integral of $A$ over $\Omega$ is the sum over the elements $T$
of the integrals of $A$ over the open elements of $T$. -/
theorem setIntegral_eq_sum_K {A : 𝔼₂ → ℝ} (hA : IntegrableOn A (Ω : Set 𝔼₂)) :
    ∫ x in (Ω : Set 𝔼₂), A x = ∑ T, ∫ x in 𝒯.K T, A x := by
  rw [← setIntegral_congr_set 𝒯.ae_eq_iUnion_K]
  exact integral_iUnion_fintype (fun T ↦ (𝒯.isOpen_K T).measurableSet) 𝒯.pairwise_disjoint_K
    fun T ↦ hA.mono_set (𝒯.K_subset T)

/-- The **divergence theorem on a triangulated domain**. Let $\mathcal{T}$ be a triangulation of the
open set $\Omega \subseteq \mathbb{R}^2$, with surface measure $\sigma$ and outward unit normal
$\nu$. Let $F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on $\bar\Omega$ and of class $C^1$
up to the boundary on $\Omega$. Then $$\int_\Omega \operatorname{div} F \, dx = \int \langle F,
\nu \rangle \, d\sigma.$$

No hypothesis beyond the axioms of `Triangulation` is needed: a slit along an interior edge does
not change the integrals of a field that is continuous across it. The integral over $\Omega$ is
the sum of the integrals over the open elements, which partition $\Omega$ up to a null set. Each
of these is the sum of three edge terms (`EuclideanSpace.integral_div_openTriangle`), the terms
of the interior edges cancel in pairs (`Triangulation.sum_edgeTerm_interior_eq_zero`), and the
terms of the boundary edges make up the surface integral. The measure $\sigma$ is
`Triangulation.boundaryMeasure`.
The normal $\nu$ is `Triangulation.outwardNormal`. -/
theorem integral_div_eq {F : 𝔼₂ → 𝔼₂} (hF : ContinuousOn F (closure (Ω : Set 𝔼₂)))
    (hF' : ContDiffOnClosure ℝ 1 F (Ω : Set 𝔼₂)) :
    ∫ x in (Ω : Set 𝔼₂), div F x = ∫ x, ⟪F x, 𝒯.outwardNormal x⟫_ℝ ∂𝒯.boundaryMeasure := by
  classical
  have h1 : ∫ x in (Ω : Set 𝔼₂), div F x = ∑ T, ∫ x in 𝒯.K T, div F x :=
    𝒯.setIntegral_eq_sum_K (integrableOn_div hF' 𝒯.isBounded Ω.isOpen.measurableSet)
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

/-- The **boundary data of a triangulated domain**: $\Omega$ with the surface measure
`Triangulation.boundaryMeasure` and the outward unit normal `Triangulation.outwardNormal` is a
`BoundaryData`, whose divergence theorem is `Triangulation.integral_div_eq`.

This is the boundary data that the polygonal domains of [han2009theoretical] §11.4 and §13.1 and
of equation (12.95) of [quarteroni2000numerical] use. Its trace family is
`Triangulation.traceFamily` of `Numlib.Analysis.Sobolev.Boundary.PolygonTrace`. -/
def boundaryData : BoundaryData Ω where
  σ := 𝒯.boundaryMeasure
  ν := 𝒯.outwardNormal
  isBounded := 𝒯.isBounded
  isFiniteMeasure := inferInstance
  measure_compl_frontier := 𝒯.boundaryMeasure_compl_frontier
  aestronglyMeasurable_ν := aestronglyMeasurable_outwardNormal
  ae_norm_ν := ae_norm_outwardNormal
  integral_div_eq _ hF hF' := integral_div_eq hF hF'

/-- The surface measure of the boundary data of a triangulated domain is
`Triangulation.boundaryMeasure`. -/
@[simp] theorem boundaryData_σ : 𝒯.boundaryData.σ = 𝒯.boundaryMeasure := rfl

/-- The normal of the boundary data of a triangulated domain is `Triangulation.outwardNormal`. -/
@[simp] theorem boundaryData_ν : 𝒯.boundaryData.ν = 𝒯.outwardNormal := rfl

/-! ### The no-slit hypothesis of a polygonal domain -/

/-- The **no-slit hypothesis** of a polygonal domain: for every edge $(T, a)$ that is not a boundary
edge, the open segment $(T_a, T_{a+1})$ lies in $\Omega$.

The trace theory on a polygonal domain needs this hypothesis: the one-sided traces of a function
in $W^{1,p}(\Omega)$ agree across an interior edge only when $\Omega$ lies on both sides of the
edge. The hypothesis `Triangulation.FrontierSubsetEdges` does not give it. The open square minus
a closed interior edge of a triangulation of the square satisfies the axioms of `Triangulation`
and `Triangulation.FrontierSubsetEdges`, but not this hypothesis. Conversely, a triangulated
polygonal domain with one interior vertex removed satisfies this hypothesis but not
`Triangulation.FrontierSubsetEdges`. A polygonal domain in the sense of [han2009theoretical]
§10.2 satisfies both, and the results on polygonal domains assume both. -/
def InteriorEdgesSubset : Prop :=
  ∀ (T : 𝒯.elems) (a : Fin 3), ¬ 𝒯.IsBoundaryEdge T a →
    openSegment ℝ (T.1 a) (T.1 (a + 1)) ⊆ Ω

variable {𝒯}

/-- Without slits, the boundary consists of the vertices and the open boundary edges. Suppose that
$\mathcal{T}$ satisfies `Triangulation.InteriorEdgesSubset`, and let $x \in \partial\Omega$.
Then $x$ is a vertex of the triangulation, or $x$ lies on the open segment $(T_a, T_{a+1})$ of a
boundary edge $(T, a)$. So the surface measure sees all of $\partial\Omega$ except finitely many
points. -/
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

/-! ### Integrals over the boundary edges -/

section Integrals

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A property holds almost everywhere for the surface measure of a triangulated domain if and only
if it holds almost everywhere for the arclength measure of every boundary edge. -/
theorem ae_boundaryMeasure_iff {P : 𝔼₂ → Prop} :
    (∀ᵐ x ∂𝒯.boundaryMeasure, P x) ↔
      ∀ e ∈ 𝒯.boundaryEdges, ∀ᵐ x ∂edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1)), P x := by
  rw [boundaryMeasure, ae_finsetSum_measure_iff]

/-- If $(T, a)$ is a boundary edge, the arclength measure $\sigma_{T_a T_{a+1}}$ is at most the
surface measure of the triangulated domain. -/
theorem edgeMeasure_le_boundaryMeasure {T : 𝒯.elems} {a : Fin 3} (h : 𝒯.IsBoundaryEdge T a) :
    edgeMeasure (T.1 a) (T.1 (a + 1)) ≤ 𝒯.boundaryMeasure := by
  have h2 := Finset.single_le_sum
    (f := fun e : 𝒯.elems × Fin 3 ↦ edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1)))
    (fun _ _ ↦ Measure.zero_le _) ((mem_boundaryEdges (e := (T, a))).2 h)
  rw [boundaryMeasure]
  exact h2

/-! ### The interior integrals over the elements -/

include 𝒯 in
/-- Let $\Omega \subseteq \mathbb{R}^2$ be an open set that has a triangulation, and let
$f : \mathbb{R}^2 \to \mathbb{R}$ be continuous on $\bar\Omega$. Then $f \in L^q(\Omega)$ for
every $q \in [0, \infty]$.

The triangulation makes $\Omega$ bounded, so $\bar\Omega$ is compact. -/
theorem memLp_restrict_of_continuousOn {f : 𝔼₂ → ℝ} (hf : ContinuousOn f (closure (Ω : Set 𝔼₂)))
    (q : ℝ≥0∞) : MemLp f q (volume.restrict (Ω : Set 𝔼₂)) := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set 𝔼₂)) :=
    isFiniteMeasure_restrict.2 𝒯.isBounded.measure_lt_top.ne
  obtain ⟨C, hC⟩ := 𝒯.isCompact_closure.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable Ω.isOpen.measurableSet) C ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hC x (subset_closure hx)

include 𝒯 in
/-- Let $\Omega \subseteq \mathbb{R}^2$ be an open set that has a triangulation, let
$1 \le p \le \infty$, let $f \in L^p(\Omega)$, and let $g$ be continuous on $\bar\Omega$. Then
$fg$ is integrable on $\Omega$. -/
theorem integrableOn_mul_of_memLp_of_continuousOn {f g : 𝔼₂ → ℝ}
    (hf : MemLp f p (volume.restrict (Ω : Set 𝔼₂))) (hg : ContinuousOn g (closure (Ω : Set 𝔼₂))) :
    IntegrableOn (fun x ↦ f x * g x) (Ω : Set 𝔼₂) := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set 𝔼₂)) :=
    isFiniteMeasure_restrict.2 𝒯.isBounded.measure_lt_top.ne
  exact (hf.integrable Fact.out).mul_of_top_left (𝒯.memLp_restrict_of_continuousOn hg ⊤)

end Integrals

end Triangulation

end
