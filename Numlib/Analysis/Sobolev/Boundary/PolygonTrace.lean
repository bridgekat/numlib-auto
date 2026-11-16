/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Sobolev.Boundary.Polygon
import Numlib.Analysis.Sobolev.Boundary.Trace
import Numlib.Analysis.Sobolev.Compactness

/-!
# The trace on a triangulated plane domain

Let $\Omega \subseteq \mathbb{R}^2$ be an open set with a triangulation (`Triangulation`). Each
element $T$ is an open triangle $K_T$ with vertices $T_0, T_1, T_2$. The edge $(T, a)$, for
$a \in \{0, 1, 2\}$, is the segment $[T_a, T_{a+1}]$ with indices modulo $3$, and $T_{a+2}$ is its
third vertex. An edge is a boundary edge if no other element has both of its endpoints as vertices;
otherwise it has a partner $(T', a')$, the same segment as an edge of another element. Let $\sigma$
be the sum of the arclength measures of the boundary edges, $\nu$ the outward unit normal on the
boundary edges, and $\sigma_T$, $\nu_T$ the arclength measure and the outward normal of
$\partial K_T$. This module constructs the trace operator $\gamma : W^{1,p}(\Omega) \to L^p(\sigma)$
for $1 \le p < \infty$ and proves Green's formula on $\Omega$, as the trace family
`Triangulation.traceFamily` of the boundary data `Triangulation.boundaryData`. These are the trace
results that [han2009theoretical] uses on polygons in §11.4 and §13; see also [grisvard2011elliptic]
§1.5.2 (Theorem 1.5.2.1) and Nečas, *Direct Methods in the Theory of Elliptic Equations*, Chapter 2.

A polygon is not known to be a Sobolev extension domain, and a triangulated domain pinched at a
vertex has no transversal field. Therefore the construction of
`Numlib.Analysis.Sobolev.Boundary.Trace` is applied to each element. A triangle is a bounded convex
open set, so smooth functions are dense in $W^{1,p}$ up to its boundary, and the field
$x \mapsto x - G$ from its centroid $G$, cut off by a bump, is transversal. This gives the trace
family of a triangle, `EuclideanSpace.triangleTraceFamily`, whose trace is compact for
$1 < p < \infty$. For $u \in W^{1,p}(\Omega)$ let $\gamma_T u \in L^p(\sigma_T)$ be the trace of the
restriction $u|_{K_T}$. The glued trace is $\gamma u = \sum (\gamma_T u) \mathbf{1}_e$, the sum over
the boundary edges $(T, a)$, with $\mathbf{1}_e$ the indicator of the open edge
$e = (T_a, T_{a+1})$. The trace of a function continuous up to the boundary is its restriction, and
$\gamma$ is compact for $1 < p < \infty$. If $\Omega$ has no slits
(`Triangulation.InteriorEdgesSubset`: the relative interior of every interior edge lies in
$\Omega$), the one-sided traces $\gamma_T u$ and $\gamma_{T'} u$ agree on every interior edge, and
Green's formula holds on $\Omega$. The same tools prove two results of [han2009theoretical] §7.2 on
a triangulation: Example 7.2.7, a function continuous on $\overline{\Omega}$ and in $W^{1,p}$ on
every element is in $W^{1,p}(\Omega)$, and Example 7.2.8, a function in $W^{1,p}(\Omega)$ that is
continuous on each closed element takes the same values on both sides of every interior edge.

## Main definitions

* `EuclideanSpace.triangleTraceFamily`: the trace family of a triangle.
* `Triangulation.elemTraceL`: the element trace $u \mapsto \gamma_T u$,
  $W^{1,p}(\Omega) \to L^p(\sigma_T)$.
* `Triangulation.edgeEmbedL`: extension by zero from a boundary edge,
  $L^p(\sigma_T) \to L^p(\sigma)$.
* `Triangulation.traceL`: the glued trace operator $\gamma : W^{1,p}(\Omega) \to L^p(\sigma)$.
* `Triangulation.traceFun`: the glued trace as a function.
* `Triangulation.traceFamily`: the trace family of a triangulated domain without slits.

## Main results

* `EuclideanSpace.triangle_hasTransversalField`: a triangle has a transversal field.
* `EuclideanSpace.isCompactOperator_triangleTraceL`: the trace on a triangle is compact for
  $1 < p < \infty$.
* `Triangulation.traceL_ae_eq_of_continuousOn`: the glued trace of a function continuous on
  $\overline{\Omega}$ is its restriction.
* `Triangulation.isCompactOperator_traceL`: the glued trace is compact for $1 < p < \infty$.
* `Triangulation.traceL_partner_ae_eq`: without slits, $\gamma_T u = \gamma_{T'} u$ on every
  interior edge.
* `Triangulation.green_contDiff`: Green's formula without slits, against a compactly supported $C^1$
  test function.
* `Triangulation.green`: Green's formula without slits, at finite conjugate exponents.
* `Triangulation.memSobolevMultiIndex_of_continuousOn_of_forall`: a function continuous on
  $\overline{\Omega}$ and in $W^{1,p}$ on every element is in $W^{1,p}(\Omega)$.
* `Triangulation.eqOn_partner_of_memSobolev_of_continuousOn`: a function in $W^{1,p}(\Omega)$ that
  is continuous on each closed element has equal values from both sides of every interior edge.
* `Triangulation.traceFamily_of_convex_traceL`: on a convex domain, the construction of
  `Numlib.Analysis.Sobolev.Boundary.Trace` on $\Omega$ itself gives the glued trace.
* `Triangulation.interiorEdgesSubset_of_convex`: a convex triangulated domain has no slits.

## Proof outline

For the agreement of the one-sided traces on an interior edge $e$, take a smooth test function $g$
supported near $e$. The sum of the Green formulas of the elements against $g$ is the defining
identity of the weak derivative on $\Omega$, so it vanishes, and all edge integrals except those on
$e$ vanish. The two elements give $e$ the same arclength measure and opposite normals, so $\int_e g
\, (\gamma_T u - \gamma_{T'} u) \, \nu_i = 0$ for every such $g$. Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` on the arclength measure then gives
$\gamma_T u = \gamma_{T'} u$ on $e$. Green's formula on $\Omega$ is the sum of the Green formulas of
the elements. The interior edges cancel in partner pairs (same measure, opposite normals, equal
traces), exactly as in the divergence theorem `Triangulation.integral_div_eq`.

## Notation

* `𝔼₂`: the plane `EuclideanSpace ℝ (Fin 2)`.

## Implementation notes

* The glued operator is a sum of bounded operators `Triangulation.edgeEmbedL` ∘
  `Triangulation.elemTraceL` over the boundary edges, and not `MemLp.toLp` of the glued function.
  Linearity, boundedness and compactness then come from the pieces. The only computation is the
  identification of the sum on each boundary edge (`Triangulation.traceL_ae_eq_triangle`), where all
  indicators but one vanish almost everywhere
  (`Triangulation.openSegment_disjoint_of_isBoundaryEdge`).
* The edge-by-edge bookkeeping of the boundary integrals (`Triangulation.edgeIntegral`,
  `Triangulation.sum_integral_mul_triangleNormal_eq`) is shared by Green's formula, the agreement of
  the one-sided traces, and the piecewise membership theorem.
* For `T : 𝒯.elems`, the vertex $T_a$ is `T.1 a` with `a : Fin 3`. The open element $K_T$ is
  `𝒯.K T`, and as an open set `𝒯.Kopens T`. Its boundary data are `Triangulation.elemBoundaryData`,
  and $u|_{K_T}$ is `SobolevMultiIndex.restrictL … (𝒯.Kopens_le T) u`.
* The membership theorem `Triangulation.memSobolevMultiIndex_of_continuousOn_of_forall` needs no
  slit hypothesis. The agreement of the one-sided traces, Green's formula and the trace family need
  `Triangulation.InteriorEdgesSubset`.
* Example 7.2.8 of [han2009theoretical] also concludes that the function is continuous on
  $\overline{\Omega}$. This needs, in addition, that the elements around each vertex are connected
  through shared edges, and it can fail at a pinch vertex.
  `Triangulation.eqOn_partner_of_memSobolev_of_continuousOn` states the agreement across the edges
  only.
-/

open Filter MeasureTheory Set Function TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal

noncomputable section

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

section General

variable {α : Type*} [MeasurableSpace α] {ι : Type*} {s : Finset ι} {μ : ι → Measure α}
  {p : ℝ≥0∞} {f : α → ℝ}

end General

namespace EuclideanSpace

/-! ### The transversal field of a triangle -/

/-- Let $P, Q, R \in \mathbb{R}^2$ be the vertices of a nondegenerate triangle,
$\langle (Q - P)^\perp, R - P \rangle \neq 0$, where $(Q - P)^\perp$ is the rotation
`EuclideanSpace.perp (Q - P)`, and let $G$ be its centroid, $3G = P + Q + R$. Then $$\langle
\nu, P - G \rangle > 0,$$ where $\nu$ is the outward unit normal
`EuclideanSpace.edgeNormal P Q R` of the edge $[P, Q]$. The number $\langle \nu, P - G \rangle$
is the distance from $G$ to the line through the edge, so the centroid lies strictly on the
inner side of this line. -/
theorem inner_edgeNormal_sub_centroid_pos {P Q R G : 𝔼₂} (h : ⟪perp (Q - P), R - P⟫_ℝ ≠ 0)
    (hG : (3 : ℝ) • G = P + Q + R) : 0 < ⟪edgeNormal P Q R, P - G⟫_ℝ := by
  have h1 := inner_edgeNormal_sub P Q R
  have h2 := inner_edgeNormal_third_neg h
  have hG' : G = (1 / 3 : ℝ) • (P + Q + R) := by
    rw [← hG, smul_smul]; norm_num
  have : P - G = (-(1 / 3) : ℝ) • (Q - P) + (-(1 / 3) : ℝ) • (R - P) := by
    rw [hG']; module
  rw [this, inner_add_right, inner_smul_right, inner_smul_right, h1]
  linarith

/-- **A triangle has a transversal field.** Let $A, B, C \in \mathbb{R}^2$ with $B - A$ and $C - A$
linearly independent. Then the boundary data `EuclideanSpace.triangleBoundaryData A B C h` of
the open triangle $ABC$ have a transversal field (`BoundaryData.HasTransversalField`).

With $G$ the centroid and $\delta$ the least of the three distances from $G$ to the lines
through the edges, the field is $w(x) = \chi(x) \, \delta^{-1} (x - G)$ for a bump function
$\chi$ equal to $1$ on the closed triangle. It satisfies $\langle w, \nu \rangle \ge 1$ on the
relative interior of every edge, because $\langle x - G, \nu \rangle$ is constant along an edge
(`EuclideanSpace.inner_edgeNormal_lineMap_sub`) and equals that distance. -/
theorem triangle_hasTransversalField (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    (triangleBoundaryData A B C h).HasTransversalField := by
  have h1 := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 h
  have h2 := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (linearIndependent_rotate h)
  have h3 := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1
    (linearIndependent_rotate (linearIndependent_rotate h))
  obtain ⟨G, hG⟩ : ∃ G : 𝔼₂, G = (1 / 3 : ℝ) • (A + B + C) := ⟨_, rfl⟩
  have hG3 : (3 : ℝ) • G = A + B + C := by rw [hG, smul_smul]; norm_num
  have hd₁ := inner_edgeNormal_sub_centroid_pos h1 hG3
  have hd₂ := inner_edgeNormal_sub_centroid_pos h2 (by rw [hG3]; abel)
  have hd₃ := inner_edgeNormal_sub_centroid_pos h3 (by rw [hG3]; abel)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min ⟪edgeNormal A B C, A - G⟫_ℝ
      (min ⟪edgeNormal B C A, B - G⟫_ℝ ⟪edgeNormal C A B, C - G⟫_ℝ) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min hd₁ (lt_min hd₂ hd₃)
  have hδ₁ : δ ≤ ⟪edgeNormal A B C, A - G⟫_ℝ := hδ ▸ min_le_left _ _
  have hδ₂ : δ ≤ ⟪edgeNormal B C A, B - G⟫_ℝ := hδ ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hδ₃ : δ ≤ ⟪edgeNormal C A B, C - G⟫_ℝ := hδ ▸ (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨r, hr⟩ := (isBounded_closedTriangle A B C).subset_closedBall G
  let χ : ContDiffBump G := ⟨max r 0 + 1, max r 0 + 2, by positivity, by linarith⟩
  have hχ : ∀ x ∈ closedTriangle A B C, χ x = 1 := fun x hx ↦
    χ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall
      (by linarith [le_max_left r 0]) (hr hx))
  refine ⟨fun x ↦ χ x • (δ⁻¹ • (x - G)), ?_, ?_, ?_⟩
  · exact χ.contDiff.smul ((contDiff_id.sub contDiff_const).const_smul δ⁻¹)
  · exact χ.hasCompactSupport.smul_right (f' := fun x ↦ δ⁻¹ • (x - G))
  · -- on the open edge `[P, Q]` with normal `n`: `⟪w x, n⟫ = δ⁻¹ ⟪n, P − G⟫ ≥ 1`
    have key : ∀ (P Q R : 𝔼₂), segment ℝ P Q ⊆ closedTriangle A B C →
        δ ≤ ⟪edgeNormal P Q R, P - G⟫_ℝ → ∀ x ∈ openSegment ℝ P Q,
          1 ≤ ⟪χ x • (δ⁻¹ • (x - G)), edgeNormal P Q R⟫_ℝ := by
      intro P Q R hs hδP x hx
      have hxs : x ∈ closedTriangle A B C := hs (openSegment_subset_segment ℝ _ _ hx)
      rw [openSegment_eq_image_lineMap] at hx
      obtain ⟨t, -, rfl⟩ := hx
      rw [hχ _ hxs, one_smul, real_inner_smul_left, real_inner_comm,
        inner_edgeNormal_lineMap_sub, le_inv_mul_iff₀ hδ0, mul_one]
      exact hδP
    change ∀ᵐ x ∂triangleBoundaryMeasure A B C, 1 ≤ ⟪_, triangleNormal A B C x⟫_ℝ
    unfold triangleBoundaryMeasure
    rw [ae_add_measure_iff, ae_add_measure_iff]
    refine ⟨⟨(ae_mem_openSegment (ne₀₁ h)).mono fun x hx ↦ ?_,
      (ae_mem_openSegment (ne₁₂ h)).mono fun x hx ↦ ?_⟩,
      (ae_mem_openSegment (ne₂₀ h)).mono fun x hx ↦ ?_⟩
    · rw [triangleNormal_eq_of_mem_openSegment₀₁ hx]
      exact key A B C (segment_subset_closedTriangle A B C 0 1) hδ₁ x hx
    · rw [triangleNormal_eq_of_mem_openSegment₁₂ h hx]
      exact key B C A (segment_subset_closedTriangle A B C 1 2) hδ₂ x hx
    · rw [triangleNormal_eq_of_mem_openSegment₂₀ h hx]
      exact key C A B (segment_subset_closedTriangle A B C 2 0) hδ₃ x hx

/-! ### The trace family of a triangle -/

/-- **The trace theorem on a triangle**: for $A, B, C \in \mathbb{R}^2$ with $B - A$ and $C - A$
linearly independent, the trace family (`BoundaryData.TraceFamily`) of the open triangle $K$
with these vertices. It gives, for each $1 \le p < \infty$, the trace operator
$W^{1,p}(K) \to L^p$ of the arclength measure of $\partial K$, the restriction property, and
Green's formulas.

It is `BoundaryData.traceFamily` with the transversal field
`EuclideanSpace.triangle_hasTransversalField` and the density theorems for bounded convex open
sets (`EuclideanSpace.hasSmoothDensity_openTriangleOpens`,
`EuclideanSpace.hasUniformSmoothDensity_openTriangleOpens`). -/
def triangleTraceFamily (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    (triangleBoundaryData A B C h).TraceFamily :=
  BoundaryData.traceFamily _ (triangle_hasTransversalField A B C h)
    (fun _ _ hq ↦ hasSmoothDensity_openTriangleOpens A B C h hq)
    (fun _ _ hq ↦ hasUniformSmoothDensity_openTriangleOpens A B C h hq)

/-- The trace operator of `EuclideanSpace.triangleTraceFamily` at an exponent $1 \le p < \infty$ is
`BoundaryData.traceL` for the transversal field `EuclideanSpace.triangle_hasTransversalField`. -/
theorem triangleTraceFamily_traceL (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A])
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (triangleTraceFamily A B C h).traceL p hp
      = (triangleBoundaryData A B C h).traceL (triangle_hasTransversalField A B C h) p hp :=
  rfl

/-- **Compactness of the trace on a triangle.** Let $A, B, C \in \mathbb{R}^2$ with $B - A$ and
$C - A$ linearly independent, and let $1 < p < \infty$. Then the trace operator of
`EuclideanSpace.triangleTraceFamily A B C h` at $p$ is a compact operator. This is
[han2009theoretical] Theorem 7.3.10(c) on a triangle.

It is `BoundaryData.isCompactOperator_traceL` with Rellich's theorem on the triangle, which is a
Sobolev extension domain (`EuclideanSpace.isSobolevExtensionDomainAll_openTriangleOpens`). -/
theorem isCompactOperator_triangleTraceL (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A])
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsCompactOperator ((triangleTraceFamily A B C h).traceL p hp) := by
  rw [triangleTraceFamily_traceL]
  refine BoundaryData.isCompactOperator_traceL _ _ p hp hp1
    (hasSmoothDensity_openTriangleOpens A B C h hp) ?_
  obtain ⟨q, rfl⟩ : ∃ q : ℝ≥0, p = q := ⟨p.toNNReal, (ENNReal.coe_toNNReal hp).symm⟩
  rw [← SobolevMultiIndex.toLpₗ_self]
  exact SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain
    (isSobolevExtensionDomainAll_openTriangleOpens A B C h q)
    (isBounded_openTriangle A B C).measure_lt_top.ne

end EuclideanSpace

/-! ### The element traces and the glued trace of a triangulation -/

namespace Triangulation

open EuclideanSpace SobolevMultiIndex

variable {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The boundary data of the element $K_T$, as a triangle: `EuclideanSpace.triangleBoundaryData` of
its vertices, with the measure $\sigma_T$ and the normal $\nu_T$. -/
abbrev elemBoundaryData (T : 𝒯.elems) : BoundaryData (𝒯.Kopens T) :=
  triangleBoundaryData (T.1 0) (T.1 1) (T.1 2) (𝒯.li T)

/-- The trace family of the element $K_T$, as a triangle: `EuclideanSpace.triangleTraceFamily` of
its vertices. -/
abbrev elemTraceFamily (T : 𝒯.elems) : (𝒯.elemBoundaryData T).TraceFamily :=
  triangleTraceFamily (T.1 0) (T.1 1) (T.1 2) (𝒯.li T)

/-- **The trace on the boundary of an element**: for $1 \le p < \infty$ and an element $T$, the
bounded operator $W^{1,p}(\Omega) \to L^p(\sigma_T)$, $u \mapsto \gamma_T u$, that maps $u$ to
the trace on $\partial K_T$ of its restriction $u|_{K_T} \in W^{1,p}(K_T)$. The measure
$\sigma_T$ is `EuclideanSpace.triangleBoundaryMeasure` of the vertices of $T$. -/
def elemTraceL (hp : p ≠ ⊤) (T : 𝒯.elems) :
    SobolevEuclidean 2 1 p Ω →L[ℝ] Lp ℝ p (triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2)) :=
  (𝒯.elemTraceFamily T).traceL p hp ∘L
    restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p volume (𝒯.Kopens_le T)

variable {𝒯 p}

/-- The element trace $\gamma_T u$ is the trace operator of `Triangulation.elemTraceFamily` applied
to the restriction $u|_{K_T}$ (`SobolevMultiIndex.restrictL`). -/
theorem elemTraceL_apply (hp : p ≠ ⊤) (T : 𝒯.elems) (u : SobolevEuclidean 2 1 p Ω) :
    𝒯.elemTraceL p hp T u = (𝒯.elemTraceFamily T).traceL p hp
      (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p volume (𝒯.Kopens_le T) u) :=
  rfl

/-- For $u \in W^{1,p}(\Omega)$ and an element $T$, the function of the restriction $u|_{K_T}$
equals the function of $u$ almost everywhere on $K_T$. -/
theorem fn_restrictL_ae_eq (T : 𝒯.elems) (u : SobolevEuclidean 2 1 p Ω) :
    fn (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p volume (𝒯.Kopens_le T) u)
      =ᵐ[volume.restrict (𝒯.K T)] fn u :=
  fn_restrictL _ u

/-- **The element trace of a function continuous up to the boundary is its restriction.** Let
$1 \le p < \infty$ and $u \in W^{1,p}(\Omega)$, and let $\tilde u : \mathbb{R}^2 \to \mathbb{R}$
be continuous on $\overline{\Omega}$ and equal to $u$ almost everywhere on $\Omega$. Then for
every element $T$, $\gamma_T u = \tilde u$ $\sigma_T$-almost everywhere. -/
theorem elemTraceL_ae_eq_of_continuousOn (hp : p ≠ ⊤) (T : 𝒯.elems) (u : SobolevEuclidean 2 1 p Ω)
    {ũ : 𝔼₂ → ℝ} (hu : fn u =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) :
    (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) =ᵐ[triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2)] ũ := by
  refine (𝒯.elemTraceFamily T).traceL_ae_eq p hp _ ũ ?_ ?_
  · exact (fn_restrictL_ae_eq T u).trans
      (hu.filter_mono (ae_mono (Measure.restrict_mono (𝒯.K_subset T) le_rfl)))
  · rw [coe_Kopens, 𝒯.closure_K]
    exact hc.mono (𝒯.closedK_subset_closure T)

/-! ### Extension by zero from a boundary edge -/

/-- Let $(T, a)$ and $(T', a')$ be distinct boundary edges, and let $e$ be the open edge
$(T_a, T_{a+1})$. For every $f : \mathbb{R}^2 \to \mathbb{R}$, the function $f \mathbf{1}_e$
vanishes almost everywhere for the arclength measure of the edge $(T', a')$. -/
theorem indicator_ae_eq_zero_of_ne {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsBoundaryEdge T a)
    (h' : 𝒯.IsBoundaryEdge T' a') (hne : (T, a) ≠ (T', a')) (f : 𝔼₂ → ℝ) :
    (openSegment ℝ (T.1 a) (T.1 (a + 1))).indicator f
      =ᵐ[edgeMeasure (T'.1 a') (T'.1 (a' + 1))] 0 :=
  (ae_mem_openSegment (vertex_ne_vertex_add_one T' a')).mono fun x hx ↦ by
    rw [Pi.zero_apply, indicator_of_notMem]
    exact fun hx' ↦ Set.disjoint_left.1 (openSegment_disjoint_of_isBoundaryEdge h h' hne) hx' hx

/-- Let $(T, a)$ be a boundary edge with open edge $e$, and let $f, g : \mathbb{R}^2 \to \mathbb{R}$
be equal almost everywhere for the arclength measure of this edge. Then
$f \mathbf{1}_e = g \mathbf{1}_e$ $\sigma$-almost everywhere. -/
theorem indicator_ae_eq_boundaryMeasure {T : 𝒯.elems} {a : Fin 3} (h : 𝒯.IsBoundaryEdge T a)
    {f g : 𝔼₂ → ℝ} (hfg : f =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] g) :
    (openSegment ℝ (T.1 a) (T.1 (a + 1))).indicator f
      =ᵐ[𝒯.boundaryMeasure] (openSegment ℝ (T.1 a) (T.1 (a + 1))).indicator g := by
  refine ae_boundaryMeasure_iff.2 fun e he ↦ ?_
  by_cases hea : e = (T, a)
  · subst hea
    exact hfg.mono fun x hx ↦ by simp only [indicator, hx]
  · exact (indicator_ae_eq_zero_of_ne h (mem_boundaryEdges.1 he) (Ne.symm hea) f).trans
      (indicator_ae_eq_zero_of_ne h (mem_boundaryEdges.1 he) (Ne.symm hea) g).symm

/-- Let $1 \le p < \infty$, and let $(T, a)$ be a boundary edge with open edge $e$. If $f$ lies in
$L^p$ of the arclength measure of the edge, then $f \mathbf{1}_e$ lies in $L^p(\sigma)$. -/
theorem memLp_indicator_boundaryMeasure (hp : p ≠ ⊤) {T : 𝒯.elems} {a : Fin 3}
    (h : 𝒯.IsBoundaryEdge T a)
    {f : 𝔼₂ → ℝ} (hf : MemLp f p (edgeMeasure (T.1 a) (T.1 (a + 1)))) :
    MemLp ((openSegment ℝ (T.1 a) (T.1 (a + 1))).indicator f) p 𝒯.boundaryMeasure := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  rw [boundaryMeasure]
  refine memLp_finsetSum_measure hp0 hp fun e he ↦ ?_
  by_cases hea : e = (T, a)
  · subst hea
    exact hf.indicator (measurableSet_openSegment _ _).nullMeasurableSet
  · exact (MemLp.zero (p := p)).ae_eq
      (indicator_ae_eq_zero_of_ne h (mem_boundaryEdges.1 he) (Ne.symm hea) f).symm

/-- Let $1 \le p < \infty$, and let $(T, a)$ be a boundary edge with open edge $e$ and arclength
measure $\lambda$. For $f$ almost everywhere strongly measurable for $\lambda$, $$\|f
\mathbf{1}_e\|_{L^p(\sigma)} \le \|f\|_{L^p(\lambda)},$$ for the extended-real seminorms
`MeasureTheory.eLpNorm`. -/
theorem eLpNorm_indicator_boundaryMeasure_le (hp : p ≠ ⊤) {T : 𝒯.elems} {a : Fin 3}
    (h : 𝒯.IsBoundaryEdge T a) {f : 𝔼₂ → ℝ}
    (hf : AEStronglyMeasurable f (edgeMeasure (T.1 a) (T.1 (a + 1)))) :
    eLpNorm ((openSegment ℝ (T.1 a) (T.1 (a + 1))).indicator f) p 𝒯.boundaryMeasure
      ≤ eLpNorm f p (edgeMeasure (T.1 a) (T.1 (a + 1))) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  rw [boundaryMeasure, eLpNorm_finsetSum_measure_of_ae_eq_zero hp0 hp (mem_boundaryEdges.2 h)
    (hf.indicator (measurableSet_openSegment _ _))
    (fun e he hne ↦ indicator_ae_eq_zero_of_ne h (mem_boundaryEdges.1 he) (Ne.symm hne) f)]
  exact eLpNorm_indicator_le f (measurableSet_openSegment _ _).nullMeasurableSet

variable (p) in
/-- **Extension by zero from a boundary edge**: for $1 \le p < \infty$ and a boundary edge $(T, a)$
with open edge $e$, the bounded operator $L^p(\sigma_T) \to L^p(\sigma)$,
$g \mapsto g \mathbf{1}_e$, of norm at most $1$. -/
def edgeEmbedL (hp : p ≠ ⊤) {T : 𝒯.elems} {a : Fin 3} (h : 𝒯.IsBoundaryEdge T a) :
    Lp ℝ p (triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2)) →L[ℝ] Lp ℝ p 𝒯.boundaryMeasure :=
  have hle := edgeMeasure_le_triangleBoundaryMeasure T.1 a
  LinearMap.mkContinuous
    { toFun := fun g ↦ (memLp_indicator_boundaryMeasure hp h
        ((Lp.memLp g).mono_measure hle)).toLp _
      map_add' := fun g g' ↦ by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _
          ((indicator_ae_eq_boundaryMeasure h ((Lp.coeFn_add g g').filter_mono
            (ae_mono hle))).trans ?_)
        exact Filter.EventuallyEq.of_eq (Set.indicator_add' _ _ _)
      map_smul' := fun c g ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _
          ((indicator_ae_eq_boundaryMeasure h ((Lp.coeFn_smul c g).filter_mono
            (ae_mono hle))).trans ?_)
        refine Filter.EventuallyEq.of_eq (funext fun x ↦ ?_)
        by_cases hx : x ∈ openSegment ℝ (T.1 a) (T.1 (a + 1))
        · simp only [indicator_of_mem hx, Pi.smul_apply]
        · simp only [indicator_of_notMem hx, Pi.smul_apply, smul_zero] }
    1 fun g ↦ by
      rw [one_mul, LinearMap.coe_mk, AddHom.coe_mk,
        Lp.norm_toLp _ (memLp_indicator_boundaryMeasure hp h ((Lp.memLp g).mono_measure hle)),
        Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) ?_
      exact (eLpNorm_indicator_boundaryMeasure_le hp h
        ((Lp.aestronglyMeasurable g).mono_measure hle)).trans (eLpNorm_mono_measure _ hle)

/-- For $g \in L^p(\sigma_T)$ and a boundary edge $(T, a)$ with open edge $e$, the function of the
extension by zero `Triangulation.edgeEmbedL` of $g$ is $g \mathbf{1}_e$ $\sigma$-almost
everywhere. -/
theorem coeFn_edgeEmbedL (hp : p ≠ ⊤) {T : 𝒯.elems} {a : Fin 3} (h : 𝒯.IsBoundaryEdge T a)
    (g : Lp ℝ p (triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2))) :
    (𝒯.edgeEmbedL p hp h g : 𝔼₂ → ℝ) =ᵐ[𝒯.boundaryMeasure]
      (openSegment ℝ (T.1 a) (T.1 (a + 1))).indicator g :=
  MemLp.coeFn_toLp (memLp_indicator_boundaryMeasure hp h
    ((Lp.memLp g).mono_measure (edgeMeasure_le_triangleBoundaryMeasure T.1 a)))

/-! ### The glued trace -/

variable (𝒯 p) in
/-- The contribution of a boundary edge $(T, a)$, with open edge $e$, to the glued trace: the
bounded operator $W^{1,p}(\Omega) \to L^p(\sigma)$, $u \mapsto (\gamma_T u) \mathbf{1}_e$, the
element trace extended by zero off the open edge. -/
def edgeTraceL (hp : p ≠ ⊤) (e : 𝒯.boundaryEdges) :
    SobolevEuclidean 2 1 p Ω →L[ℝ] Lp ℝ p 𝒯.boundaryMeasure :=
  (𝒯.edgeEmbedL p hp (mem_boundaryEdges.1 e.2)).comp (𝒯.elemTraceL p hp e.1.1)

variable (𝒯 p) in
/-- **The trace operator of a triangulated domain**: for $1 \le p < \infty$, the bounded operator
$\gamma : W^{1,p}(\Omega) \to L^p(\sigma)$, $$\gamma u = \sum_{(T, a)} (\gamma_T u) \,
\mathbf{1}_{(T_a, T_{a+1})},$$ where the sum is over the boundary edges, and each element trace
is extended by zero off its open edge.

It is defined on every triangulation. The no-slit hypothesis `Triangulation.InteriorEdgesSubset`
is needed only for the agreement of the one-sided traces and for Green's formula. -/
def traceL (hp : p ≠ ⊤) : SobolevEuclidean 2 1 p Ω →L[ℝ] Lp ℝ p 𝒯.boundaryMeasure :=
  ∑ e : 𝒯.boundaryEdges, 𝒯.edgeTraceL p hp e

variable (𝒯 p) in
/-- **The glued boundary values of $u \in W^{1,p}(\Omega)$, as a function**: $$x \mapsto \sum_{(T,
a)} \mathbf{1}_{(T_a, T_{a+1})}(x) \, (\gamma_T u)(x),$$ with the sum over the boundary edges
and $\gamma_T u$ evaluated through a representative. On the relative interior of each boundary
edge, it is the trace of the restriction of $u$ to the element that owns the edge. -/
def traceFun (hp : p ≠ ⊤) (u : SobolevEuclidean 2 1 p Ω) : 𝔼₂ → ℝ := fun x ↦
  ∑ e ∈ 𝒯.boundaryEdges, (openSegment ℝ (e.1.1 e.2) (e.1.1 (e.2 + 1))).indicator
    (fun y ↦ (𝒯.elemTraceL p hp e.1 u : 𝔼₂ → ℝ) y) x

/-- For a boundary edge $(T, a)$ with open edge $e$, the function of the contribution
`Triangulation.edgeTraceL` is $(\gamma_T u) \mathbf{1}_e$ $\sigma$-almost everywhere. -/
theorem coeFn_edgeTraceL (hp : p ≠ ⊤) (e : 𝒯.boundaryEdges) (u : SobolevEuclidean 2 1 p Ω) :
    (𝒯.edgeTraceL p hp e u : 𝔼₂ → ℝ) =ᵐ[𝒯.boundaryMeasure]
      (openSegment ℝ (e.1.1.1 e.1.2) (e.1.1.1 (e.1.2 + 1))).indicator
        (𝒯.elemTraceL p hp e.1.1 u) :=
  coeFn_edgeEmbedL hp (mem_boundaryEdges.1 e.2) _

/-- **On a boundary edge, the glued trace is the element trace.** For a boundary edge $(T, a)$ and
$u \in W^{1,p}(\Omega)$, $\gamma u = \gamma_T u$ almost everywhere for the arclength measure of
the edge. -/
theorem traceL_ae_eq_triangle (hp : p ≠ ⊤) {T : 𝒯.elems} {a : Fin 3} (h : 𝒯.IsBoundaryEdge T a)
    (u : SobolevEuclidean 2 1 p Ω) :
    (𝒯.traceL p hp u : 𝔼₂ → ℝ) =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))]
      (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) := by
  have hle := edgeMeasure_le_boundaryMeasure h
  have h1 := (Lp.coeFn_finsetSum Finset.univ
    (fun e : 𝒯.boundaryEdges ↦ 𝒯.edgeTraceL p hp e u)).filter_mono (ae_mono hle)
  have h2 := ae_all_iff.2 fun e : 𝒯.boundaryEdges ↦
    (coeFn_edgeTraceL hp e u).filter_mono (ae_mono hle)
  rw [traceL, FunLike.coe_sum, Finset.sum_apply]
  filter_upwards [h1, h2, ae_mem_openSegment (vertex_ne_vertex_add_one T a)] with x hx1 hx2 hxs
  rw [hx1, Finset.sum_apply, Finset.sum_eq_single ⟨(T, a), mem_boundaryEdges.2 h⟩]
  · rw [hx2, indicator_of_mem hxs]
  · intro e _ hne
    rw [hx2, indicator_of_notMem]
    intro hx'
    refine Set.disjoint_left.1 (openSegment_disjoint_of_isBoundaryEdge (mem_boundaryEdges.1 e.2)
      h ?_) hx' hxs
    exact fun heq ↦ hne (Subtype.ext heq)
  · exact fun habs ↦ absurd (Finset.mem_univ _) habs

/-- The function of the glued trace $\gamma u$ equals the glued function `Triangulation.traceFun`
$\sigma$-almost everywhere. -/
theorem coeFn_traceL (hp : p ≠ ⊤) (u : SobolevEuclidean 2 1 p Ω) :
    (𝒯.traceL p hp u : 𝔼₂ → ℝ) =ᵐ[𝒯.boundaryMeasure] 𝒯.traceFun p hp u := by
  refine ae_boundaryMeasure_iff.2 fun e he ↦ ?_
  refine (traceL_ae_eq_triangle hp (mem_boundaryEdges.1 he) u).trans ?_
  refine (ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)).mono fun x hx ↦ ?_
  rw [traceFun, Finset.sum_eq_single_of_mem e he]
  · rw [indicator_of_mem hx]
  · intro e' he' hne
    rw [indicator_of_notMem]
    intro hx'
    exact Set.disjoint_left.1 (openSegment_disjoint_of_isBoundaryEdge (mem_boundaryEdges.1 he')
      (mem_boundaryEdges.1 he) hne) hx' hx

/-- The glued function `Triangulation.traceFun` of $u \in W^{1,p}(\Omega)$ lies in $L^p(\sigma)$. -/
theorem memLp_traceFun (hp : p ≠ ⊤) (u : SobolevEuclidean 2 1 p Ω) :
    MemLp (𝒯.traceFun p hp u) p 𝒯.boundaryMeasure :=
  (Lp.memLp _).ae_eq (coeFn_traceL hp u)

/-- The glued trace $\gamma u$ is the class in $L^p(\sigma)$ of the glued function
`Triangulation.traceFun`. -/
theorem traceL_eq_toLp (hp : p ≠ ⊤) (u : SobolevEuclidean 2 1 p Ω) :
    𝒯.traceL p hp u = (memLp_traceFun hp u).toLp _ :=
  Lp.ext ((coeFn_traceL hp u).trans (MemLp.coeFn_toLp _).symm)

/-- **The trace of a function continuous up to the boundary is its restriction**, on a triangulated
domain. Let $1 \le p < \infty$ and $u \in W^{1,p}(\Omega)$, and let
$\tilde u : \mathbb{R}^2 \to \mathbb{R}$ be continuous on $\overline{\Omega}$ and equal to $u$
almost everywhere on $\Omega$. Then $\gamma u = \tilde u$ $\sigma$-almost everywhere. This is
[han2009theoretical] Theorem 7.3.10(a) on a polygon.

On each boundary edge, it is the restriction property of the trace on the element that owns the
edge. -/
theorem traceL_ae_eq_of_continuousOn (hp : p ≠ ⊤) (u : SobolevEuclidean 2 1 p Ω) {ũ : 𝔼₂ → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) :
    (𝒯.traceL p hp u : 𝔼₂ → ℝ) =ᵐ[𝒯.boundaryMeasure] ũ := by
  refine ae_boundaryMeasure_iff.2 fun e he ↦ ?_
  refine (traceL_ae_eq_triangle hp (mem_boundaryEdges.1 he) u).trans ?_
  exact (elemTraceL_ae_eq_of_continuousOn hp e.1 u hu hc).filter_mono
    (ae_mono (edgeMeasure_le_triangleBoundaryMeasure e.1.1 e.2))

/-- **Compactness of the glued trace.** For $1 < p < \infty$, the trace
$\gamma : W^{1,p}(\Omega) \to L^p(\sigma)$ is a compact operator. This is [han2009theoretical]
Theorem 7.3.10(c) on a polygon.

Each contribution `Triangulation.edgeTraceL` is compact because the trace on a triangle is
compact (`EuclideanSpace.isCompactOperator_triangleTraceL`), and a finite sum of compact
operators is compact. -/
theorem isCompactOperator_traceL (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsCompactOperator (𝒯.traceL p hp) := by
  have key : ∀ e : 𝒯.boundaryEdges, IsCompactOperator (𝒯.edgeTraceL p hp e) := fun e ↦ by
    have h1 := isCompactOperator_triangleTraceL (e.1.1.1 0) (e.1.1.1 1) (e.1.1.1 2)
      (𝒯.li e.1.1) p hp hp1
    have h2 : IsCompactOperator (𝒯.elemTraceL p hp e.1.1) :=
      h1.comp_clm (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p volume
        (𝒯.Kopens_le e.1.1))
    exact h2.clm_comp (𝒯.edgeEmbedL p hp (mem_boundaryEdges.1 e.2))
  rw [traceL, FunLike.coe_sum]
  exact Finset.sum_induction _ IsCompactOperator (fun _ _ hf hg ↦ hf.add hg) isCompactOperator_zero
    fun e _ ↦ key e

variable (𝒯) in
/-- **The edge integral**: for a family $(f_T)$ of functions $\mathbb{R}^2 \to \mathbb{R}$ indexed
by the elements, a coordinate index $i$, an element $T$ and an edge $a$ of $T$, the number
$$\int f_T \, n_i \, d\lambda,$$ where $\lambda$ is the arclength measure of the edge
$[T_a, T_{a+1}]$ and $n$ is its constant outward normal `EuclideanSpace.edgeNormal (T.1 a) (T.1
(a + 1)) (T.1 (a + 2))`. -/
def edgeIntegral (f : 𝒯.elems → 𝔼₂ → ℝ) (i : Fin 2) (T : 𝒯.elems) (a : Fin 3) : ℝ :=
  ∫ x, f T x * edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) i ∂edgeMeasure (T.1 a) (T.1 (a + 1))

/-- Let $T$ be an element and let $f_T$ be integrable for $\sigma_T$. Then the boundary integral
$\int f_T \, (\nu_T)_i \, d\sigma_T$ is the sum of the three edge integrals
`Triangulation.edgeIntegral f i T a`, $a = 0, 1, 2$. -/
theorem integral_mul_triangleNormal_eq_sum_edgeIntegral {f : 𝒯.elems → 𝔼₂ → ℝ} {T : 𝒯.elems}
    (hf : Integrable (f T) (triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2))) (i : Fin 2) :
    ∫ x, f T x * triangleNormal (T.1 0) (T.1 1) (T.1 2) x i
        ∂triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2)
      = ∑ a : Fin 3, 𝒯.edgeIntegral f i T a :=
  integral_mul_triangleNormal_apply (𝒯.li T) hf i

/-- Let $(T', a')$ be the partner of the edge $(T, a)$, and suppose that $f_T = f_{T'}$ almost
everywhere for the arclength measure of the edge. Then the edge integrals of $f$ over $(T, a)$
and over $(T', a')$ have sum zero. -/
theorem edgeIntegral_add_partner {f : 𝒯.elems → 𝔼₂ → ℝ} {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') (hf : f T =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] f T')
    (i : Fin 2) : 𝒯.edgeIntegral f i T a + 𝒯.edgeIntegral f i T' a' = 0 := by
  unfold edgeIntegral
  rw [h.edgeMeasure_eq, h.edgeNormal_eq, PiLp.neg_apply]
  simp only [mul_neg, integral_neg]
  have e : ∫ x, f T' x * edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) i
        ∂edgeMeasure (T.1 a) (T.1 (a + 1))
      = ∫ x, f T x * edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) i
        ∂edgeMeasure (T.1 a) (T.1 (a + 1)) :=
    integral_congr_ae (hf.mono fun x hx ↦ by dsimp only; rw [hx])
  rw [e, add_neg_cancel]

open Classical in
/-- **The interior edge integrals cancel.** Suppose that $f_T = f_{T'}$ almost everywhere for the
arclength measure of the common edge whenever $(T', a')$ is the partner of $(T, a)$. Then the
sum of the edge integrals of $f$ over all edges $(T, a)$ that are not boundary edges is zero.

Partnership is an involution without fixed points on the interior edges, and the edge integral
changes sign under it. -/
theorem sum_edgeIntegral_interior_eq_zero (f : 𝒯.elems → 𝔼₂ → ℝ) (i : Fin 2)
    (hf : ∀ (T : 𝒯.elems) (a : Fin 3) (T' : 𝒯.elems) (a' : Fin 3), 𝒯.IsPartner T a T' a' →
      f T =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] f T') :
    ∑ e ∈ Finset.univ.filter (fun e : 𝒯.elems × Fin 3 ↦ ¬ 𝒯.IsBoundaryEdge e.1 e.2),
      𝒯.edgeIntegral f i e.1 e.2 = 0 :=
  sum_interior_eq_zero_of_add_partner _ fun _ _ _ _ h ↦ edgeIntegral_add_partner h (hf _ _ _ _ h) i

/-- Suppose that $f_T = f_{T'}$ almost everywhere for the arclength measure of the common edge
whenever $(T', a')$ is the partner of $(T, a)$. Then the sum of the edge integrals of $f$ over
all elements $T$ and all edges $a$ of $T$ equals the sum over the boundary edges. -/
theorem sum_sum_edgeIntegral_eq_sum_boundaryEdges (f : 𝒯.elems → 𝔼₂ → ℝ) (i : Fin 2)
    (hf : ∀ (T : 𝒯.elems) (a : Fin 3) (T' : 𝒯.elems) (a' : Fin 3), 𝒯.IsPartner T a T' a' →
      f T =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] f T') :
    ∑ T, ∑ a : Fin 3, 𝒯.edgeIntegral f i T a
      = ∑ e ∈ 𝒯.boundaryEdges, 𝒯.edgeIntegral f i e.1 e.2 := by
  classical
  rw [← Fintype.sum_prod_type' fun T a ↦ 𝒯.edgeIntegral f i T a,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun e : 𝒯.elems × Fin 3 ↦ 𝒯.IsBoundaryEdge e.1 e.2),
    sum_edgeIntegral_interior_eq_zero f i hf, add_zero]
  exact Finset.sum_congr (by ext e; simp [boundaryEdges]) fun _ _ ↦ rfl

/-- Let $g : \mathbb{R}^2 \to \mathbb{R}$ be integrable for $\sigma$, and suppose that $f_T = g$
almost everywhere for the arclength measure of every boundary edge $(T, a)$. Then the sum of the
edge integrals of $f$ over the boundary edges is $$\int g \, \nu_i \, d\sigma,$$ with $\nu$ the
outward normal `Triangulation.outwardNormal`. -/
theorem sum_boundaryEdges_edgeIntegral_eq {f : 𝒯.elems → 𝔼₂ → ℝ} {g : 𝔼₂ → ℝ}
    (hg : ∀ (T : 𝒯.elems) (a : Fin 3), 𝒯.IsBoundaryEdge T a →
      f T =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] g)
    (hgi : Integrable g 𝒯.boundaryMeasure) (i : Fin 2) :
    ∑ e ∈ 𝒯.boundaryEdges, 𝒯.edgeIntegral f i e.1 e.2
      = ∫ x, g x * 𝒯.outwardNormal x i ∂𝒯.boundaryMeasure := by
  have hgν : Integrable (fun x ↦ g x * 𝒯.outwardNormal x i) 𝒯.boundaryMeasure :=
    𝒯.boundaryData.integrable_mul_ν_apply hgi i
  rw [𝒯.integral_boundaryMeasure fun e he ↦
    hgν.mono_measure (edgeMeasure_le_boundaryMeasure (mem_boundaryEdges.1 he))]
  refine Finset.sum_congr rfl fun e he ↦ integral_congr_ae ?_
  filter_upwards [hg e.1 e.2 (mem_boundaryEdges.1 he),
    ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)] with x hx hxs
  rw [hx, outwardNormal_eq_edgeNormal (mem_boundaryEdges.1 he) hxs]

/-- **Assembly of the boundary integrals of the elements.** For each element $T$, let $f_T$ be
integrable for $\sigma_T$, and suppose that $f_T = f_{T'}$ almost everywhere for the arclength
measure of the common edge whenever $(T', a')$ is the partner of $(T, a)$. Let $g$ be integrable
for $\sigma$, with $f_T = g$ almost everywhere for the arclength measure of every boundary edge
$(T, a)$. Then $$\sum_T \int f_T \, (\nu_T)_i \, d\sigma_T = \int g \, \nu_i \, d\sigma.$$
-/
theorem sum_integral_mul_triangleNormal_eq {f : 𝒯.elems → 𝔼₂ → ℝ}
    (hf : ∀ T, Integrable (f T) (triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2)))
    (hpart : ∀ (T : 𝒯.elems) (a : Fin 3) (T' : 𝒯.elems) (a' : Fin 3), 𝒯.IsPartner T a T' a' →
      f T =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] f T')
    {g : 𝔼₂ → ℝ} (hg : ∀ (T : 𝒯.elems) (a : Fin 3), 𝒯.IsBoundaryEdge T a →
      f T =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] g)
    (hgi : Integrable g 𝒯.boundaryMeasure) (i : Fin 2) :
    ∑ T, ∫ x, f T x * triangleNormal (T.1 0) (T.1 1) (T.1 2) x i
        ∂triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2)
      = ∫ x, g x * 𝒯.outwardNormal x i ∂𝒯.boundaryMeasure := by
  rw [Finset.sum_congr rfl fun T _ ↦ integral_mul_triangleNormal_eq_sum_edgeIntegral (hf T) i,
    sum_sum_edgeIntegral_eq_sum_boundaryEdges f i hpart, sum_boundaryEdges_edgeIntegral_eq hg hgi i]

/-- **The Green formulas of the elements, summed.** Let $1 \le p < \infty$ and
$u \in W^{1,p}(\Omega)$, let $\varphi : \mathbb{R}^2 \to \mathbb{R}$ be of class $C^1$ with
compact support, and let $i$ be a coordinate index. Then $$\int_\Omega \partial_i u \, \varphi
\, dx + \int_\Omega u \, \partial_i \varphi \, dx = \sum_T \int \gamma_T u \, \varphi \,
(\nu_T)_i \, d\sigma_T.$$

Each element contributes its Green formula against $\varphi$
(`BoundaryData.TraceFamily.green_contDiff`), because the weak derivatives of $u$ restrict to the
elements. -/
theorem integral_add_integral_eq_sum_elem (hp : p ≠ ⊤) (u : SobolevEuclidean 2 1 p Ω)
    {φ : 𝔼₂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (i : Fin 2) :
    (∫ x in (Ω : Set 𝔼₂), (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * φ x)
      + ∫ x in (Ω : Set 𝔼₂), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∑ T, ∫ x, (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) x * φ x
          * triangleNormal (T.1 0) (T.1 1) (T.1 2) x i
          ∂triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2) := by
  have hdφ : ContinuousOn (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
      (closure (Ω : Set 𝔼₂)) :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
  rw [𝒯.setIntegral_eq_sum_K (𝒯.integrableOn_mul_of_memLp_of_continuousOn (Lp.memLp _)
      hφ.continuous.continuousOn),
    𝒯.setIntegral_eq_sum_K (𝒯.integrableOn_mul_of_memLp_of_continuousOn (memLp u) hdφ),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  have hG := (𝒯.elemTraceFamily T).green_contDiff p hp
    (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p volume (𝒯.Kopens_le T) u) φ hφ
    hφc i
  have e1 : ∫ x in 𝒯.K T, (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * φ x
      = ∫ x in 𝒯.K T, (weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p
          volume (𝒯.Kopens_le T) u) (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * φ x :=
    integral_congr_ae ((weakDeriv_restrictL (𝒯.Kopens_le T) u _).mono fun x hx ↦ by
      dsimp only; rw [hx])
  have e2 : ∫ x in 𝒯.K T, fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in 𝒯.K T, fn (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p
          volume (𝒯.Kopens_le T) u) x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    integral_congr_ae ((fn_restrictL (𝒯.Kopens_le T) u).mono fun x hx ↦ by
      dsimp only; rw [hx])
  rw [e1, e2]
  exact hG

/-! ### The one-sided traces agree across an interior edge -/

/-- If $(T', a')$ is the partner of $(T, a)$, the open edges $(T'_{a'}, T'_{a'+1})$ and
$(T_a, T_{a+1})$ are the same set. -/
theorem IsPartner.openSegment_eq {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    openSegment ℝ (T'.1 a') (T'.1 (a' + 1)) = openSegment ℝ (T.1 a) (T.1 (a + 1)) := by
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [h1, h2]
  · rw [h1, h2, openSegment_symm]

/-- A point of the open edge $a$ of an element $T$ lies on no other closed edge $b \neq a$ of $T$.
-/
theorem notMem_segment_of_ne (T : 𝒯.elems) {a b : Fin 3} (hab : b ≠ a) {x : 𝔼₂}
    (hx : x ∈ openSegment ℝ (T.1 a) (T.1 (a + 1))) : x ∉ segment ℝ (T.1 b) (T.1 (b + 1)) := by
  intro hs
  have hli := 𝒯.li_rot T a
  have hs' : x ∈ segment ℝ (![T.1 a, T.1 (a + 1), T.1 (a + 2)] (b - a))
      (![T.1 a, T.1 (a + 1), T.1 (a + 2)] (b + 1 - a)) := by
    rw [← vertex_eq_vecCons_rot, ← vertex_eq_vecCons_rot]
    exact hs
  have hne' : b - a ≠ b + 1 - a := fun e ↦ fin3_ne_add_one b (sub_left_injective e)
  rcases eq_edge_of_mem_openSegment_of_mem_segment hli hx hne' hs' with ⟨e1, -⟩ | ⟨e1, e2⟩
  · exact hab (sub_eq_zero.1 e1)
  · clear hs hs' hx hli hne' hab
    revert e1 e2; revert a b; decide

/-- **Only the partner meets the open edge.** If $(T', a')$ is the partner of $(T, a)$, then a point
of the open edge $(T_a, T_{a+1})$ lies in no closed element other than those of $T$ and $T'$. -/
theorem notMem_closedK_of_isPartner {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a')
    {T'' : 𝒯.elems} (h1 : T'' ≠ T) (h2 : T'' ≠ T') {x : 𝔼₂}
    (hx : x ∈ openSegment ℝ (T.1 a) (T.1 (a + 1))) : x ∉ 𝒯.closedK T'' := by
  intro hx'
  obtain ⟨i, j, hi, hj⟩ := exists_eq_vertex_of_mem_closedK h1 hx hx'
  have hij : i ≠ j := by
    rintro rfl
    exact fin3_ne_add_one a (vertex_injective T (hi.trans hj.symm))
  obtain ⟨a'', h'' | h''⟩ := exists_fin3_of_ne hij
  · exact h2 (partner_unique h ⟨h1, Or.inl ⟨h''.1 ▸ hi, h''.2 ▸ hj⟩⟩).1
  · exact h2 (partner_unique h ⟨h1, Or.inr ⟨h''.1 ▸ hi, h''.2 ▸ hj⟩⟩).1

variable (𝒯) in
/-- **The neighbourhood of an interior edge** that sees only its two elements: for edges $(T, a)$
and $(T', a')$, the set of the points of $\Omega$ that lie in no closed element other than those
of $T$ and $T'$, on no closed edge $b \neq a$ of $T$, and on no closed edge $b \neq a'$ of $T'$.

A test function supported in this set contributes to Green's formula only through the common
edge. -/
def edgeNhd (T : 𝒯.elems) (a : Fin 3) (T' : 𝒯.elems) (a' : Fin 3) : Set 𝔼₂ :=
  (Ω : Set 𝔼₂) ∩ (⋃ T'' : {T'' : 𝒯.elems // T'' ≠ T ∧ T'' ≠ T'}, 𝒯.closedK T''.1)ᶜ
    ∩ (⋃ b : {b : Fin 3 // b ≠ a}, segment ℝ (T.1 b) (T.1 (b + 1)))ᶜ
    ∩ (⋃ b : {b : Fin 3 // b ≠ a'}, segment ℝ (T'.1 b) (T'.1 (b + 1)))ᶜ

/-- For elements $T$ and $T'$, the union of the closed elements other than those of $T$ and $T'$ is
closed. -/
theorem isClosed_iUnion_closedK_of_ne (T T' : 𝒯.elems) :
    IsClosed (⋃ T'' : {T'' : 𝒯.elems // T'' ≠ T ∧ T'' ≠ T'}, 𝒯.closedK T''.1) :=
  isClosed_iUnion_of_finite fun T'' ↦ 𝒯.isClosed_closedK T''.1

/-- For an element $T$ and an edge $a$ of $T$, the union of the closed edges $b \neq a$ of $T$ is
closed. -/
theorem isClosed_iUnion_segment_of_ne (T : 𝒯.elems) (a : Fin 3) :
    IsClosed (⋃ b : {b : Fin 3 // b ≠ a}, segment ℝ (T.1 b) (T.1 (b + 1))) :=
  isClosed_iUnion_of_finite fun _ ↦ (isCompact_segment _ _).isClosed

/-- The neighbourhood `Triangulation.edgeNhd T a T' a'` of an interior edge is open. -/
theorem isOpen_edgeNhd (T : 𝒯.elems) (a : Fin 3) (T' : 𝒯.elems) (a' : Fin 3) :
    IsOpen (𝒯.edgeNhd T a T' a') := by
  unfold edgeNhd
  refine IsOpen.inter (IsOpen.inter (IsOpen.inter Ω.isOpen ?_) ?_) ?_
  · exact (𝒯.isClosed_iUnion_closedK_of_ne T T').isOpen_compl
  · exact (𝒯.isClosed_iUnion_segment_of_ne T a).isOpen_compl
  · exact (𝒯.isClosed_iUnion_segment_of_ne T' a').isOpen_compl

/-- The neighbourhood `Triangulation.edgeNhd T a T' a'` of an interior edge is contained in
$\Omega$. -/
theorem edgeNhd_subset (T : 𝒯.elems) (a : Fin 3) (T' : 𝒯.elems) (a' : Fin 3) :
    𝒯.edgeNhd T a T' a' ⊆ Ω := fun _ hx ↦ hx.1.1.1

/-- **Without slits, the open interior edge lies in its neighbourhood.** If the triangulation
satisfies `Triangulation.InteriorEdgesSubset` and $(T', a')$ is the partner of $(T, a)$, then
the open edge $(T_a, T_{a+1})$ is contained in `Triangulation.edgeNhd T a T' a'`. -/
theorem openSegment_subset_edgeNhd (hI : 𝒯.InteriorEdgesSubset) {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') :
    openSegment ℝ (T.1 a) (T.1 (a + 1)) ⊆ 𝒯.edgeNhd T a T' a' := fun x hx ↦ by
  have hx' : x ∈ openSegment ℝ (T'.1 a') (T'.1 (a' + 1)) := by
    rw [h.openSegment_eq]; exact hx
  have h1 : x ∈ (Ω : Set 𝔼₂) := hI T a h.not_isBoundaryEdge hx
  have h2 : x ∉ ⋃ T'' : {T'' : 𝒯.elems // T'' ≠ T ∧ T'' ≠ T'}, 𝒯.closedK T''.1 := by
    rw [mem_iUnion, not_exists]
    exact fun T'' ↦ notMem_closedK_of_isPartner h T''.2.1 T''.2.2 hx
  have h3 : x ∉ ⋃ b : {b : Fin 3 // b ≠ a}, segment ℝ (T.1 b) (T.1 (b + 1)) := by
    rw [mem_iUnion, not_exists]
    exact fun b ↦ notMem_segment_of_ne T b.2 hx
  have h4 : x ∉ ⋃ b : {b : Fin 3 // b ≠ a'}, segment ℝ (T'.1 b) (T'.1 (b + 1)) := by
    rw [mem_iUnion, not_exists]
    exact fun b ↦ notMem_segment_of_ne T' b.2 hx'
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- Let $g : \mathbb{R}^2 \to \mathbb{R}$ have its closed support in
`Triangulation.edgeNhd T a T' a'`. Then $g = 0$ on every closed edge of every element other than
$T$ and $T'$, on every closed edge $b \neq a$ of $T$, and on every closed edge $b \neq a'$ of
$T'$. -/
theorem eqOn_zero_of_tsupport_subset_edgeNhd {T T' : 𝒯.elems} {a a' : Fin 3} {g : 𝔼₂ → ℝ}
    (hg : tsupport g ⊆ 𝒯.edgeNhd T a T' a') :
    (∀ T'' : 𝒯.elems, T'' ≠ T → T'' ≠ T' → ∀ b : Fin 3,
        EqOn g 0 (segment ℝ (T''.1 b) (T''.1 (b + 1)))) ∧
      (∀ b : Fin 3, b ≠ a → EqOn g 0 (segment ℝ (T.1 b) (T.1 (b + 1)))) ∧
      (∀ b : Fin 3, b ≠ a' → EqOn g 0 (segment ℝ (T'.1 b) (T'.1 (b + 1)))) := by
  refine ⟨fun T'' h1 h2 b x hx ↦ ?_, fun b hb x hx ↦ ?_, fun b hb x hx ↦ ?_⟩
  · refine image_eq_zero_of_notMem_tsupport fun hxs ↦ (hg hxs).1.1.2 ?_
    exact mem_iUnion.2 ⟨⟨T'', h1, h2⟩, 𝒯.segment_subset_closedK T'' b (b + 1) hx⟩
  · exact image_eq_zero_of_notMem_tsupport fun hxs ↦ (hg hxs).1.2 (mem_iUnion.2 ⟨⟨b, hb⟩, hx⟩)
  · exact image_eq_zero_of_notMem_tsupport fun hxs ↦ (hg hxs).2 (mem_iUnion.2 ⟨⟨b, hb⟩, hx⟩)

/-- If $f_T = 0$ on the closed edge $[T_a, T_{a+1}]$, then the edge integral of $f$ over $(T, a)$ is
zero for every coordinate index $i$. -/
theorem edgeIntegral_eq_zero_of_eqOn_zero {f : 𝒯.elems → 𝔼₂ → ℝ} {T : 𝒯.elems} {a : Fin 3}
    (hf : EqOn (f T) 0 (segment ℝ (T.1 a) (T.1 (a + 1)))) (i : Fin 2) :
    𝒯.edgeIntegral f i T a = 0 := by
  unfold edgeIntegral
  rw [integral_congr_ae ((ae_mem_segment _ _).mono fun x hx ↦ ?_), integral_zero]
  dsimp only
  rw [hf hx, Pi.zero_apply, zero_mul]

/-- **The one-sided traces agree across an interior edge.** Suppose that the triangulation has no
slits (`Triangulation.InteriorEdgesSubset`), let $1 \le p < \infty$, and let $(T', a')$ be the
partner of $(T, a)$. Then for every $u \in W^{1,p}(\Omega)$, $$\gamma_T u = \gamma_{T'} u$$
almost everywhere for the arclength measure of the common edge.

The result characterizes the trace by Green's formula. For a smooth $g$ supported in
`Triangulation.edgeNhd T a T' a'`, the sum of the Green formulas of the elements against $g$ is
the defining identity of the weak derivative on $\Omega$, so it vanishes, and all edge integrals
except those on the common edge vanish. The common edge carries the same arclength measure with
opposite normals, so $\nu_i \int_e g \, (\gamma_T u - \gamma_{T'} u) = 0$ for a coordinate with
$\nu_i \neq 0$, and Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` on the
arclength measure concludes. -/
theorem traceL_partner_ae_eq (hI : 𝒯.InteriorEdgesSubset) (hp : p ≠ ⊤) {T T' : 𝒯.elems}
    {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') (u : SobolevEuclidean 2 1 p Ω) :
    (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))]
      (𝒯.elemTraceL p hp T' u : 𝔼₂ → ℝ) := by
  have hn : ‖edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2))‖ = 1 :=
    norm_edgeNormal ((linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 (𝒯.li_rot T a))
  obtain ⟨i, hi⟩ := exists_apply_ne_zero_of_norm_eq_one hn
  obtain ⟨D, hD⟩ : ∃ D : 𝔼₂ → ℝ, ∀ x,
      D x = (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) x - (𝒯.elemTraceL p hp T' u : 𝔼₂ → ℝ) x :=
    ⟨_, fun _ ↦ rfl⟩
  -- integrability of the difference on the common edge
  have hD1 : Integrable (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) (edgeMeasure (T.1 a) (T.1 (a + 1))) :=
    ((Lp.memLp _).integrable Fact.out).mono_measure (edgeMeasure_le_triangleBoundaryMeasure T.1 a)
  have hD2 : Integrable (𝒯.elemTraceL p hp T' u : 𝔼₂ → ℝ)
      (edgeMeasure (T.1 a) (T.1 (a + 1))) := by
    rw [← h.edgeMeasure_eq]
    exact ((Lp.memLp _).integrable Fact.out).mono_measure
      (edgeMeasure_le_triangleBoundaryMeasure T'.1 a')
  have hDi : Integrable D (edgeMeasure (T.1 a) (T.1 (a + 1))) :=
    (hD1.sub hD2).congr (Eventually.of_forall fun x ↦ (hD x).symm)
  -- the key identity for every test function supported near the edge
  have key : ∀ g : 𝔼₂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ 𝒯.edgeNhd T a T' a' →
      ∫ x, g x • D x ∂edgeMeasure (T.1 a) (T.1 (a + 1)) = 0 := by
    intro g hg hgc hgs
    obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(Ω, ℝ), (ψ : 𝔼₂ → ℝ) = g :=
      ⟨⟨g, hg, hgc, hgs.trans (𝒯.edgeNhd_subset T a T' a')⟩, rfl⟩
    -- the defining identity of the weak derivative on `Ω`
    have hw := (SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single u i).integral_smul_eq ψ
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one,
      neg_one_mul, hψ] at hw
    have h0 : (∫ x in (Ω : Set 𝔼₂), (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * g x)
        + ∫ x in (Ω : Set 𝔼₂), fn u x * fderiv ℝ g x (EuclideanSpace.single i 1) = 0 := by
      have e1 : ∫ x in (Ω : Set 𝔼₂), fn u x * fderiv ℝ g x (EuclideanSpace.single i 1)
          = ∫ x in (Ω : Set 𝔼₂), fderiv ℝ g x (EuclideanSpace.single i 1) * fn u x :=
        integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
      have e2 : ∫ x in (Ω : Set 𝔼₂), (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * g x
          = ∫ x in (Ω : Set 𝔼₂), g x * (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x :=
        integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
      rw [e1, e2, hw, add_neg_cancel]
    -- the sum over the elements reduces to the two edge integrals of the common edge
    rw [𝒯.integral_add_integral_eq_sum_elem hp u (hg.of_le (by simp)) hgc i] at h0
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hf : ∀ T'' : 𝒯.elems, Integrable (fun x ↦ (𝒯.elemTraceL p hp T'' u : 𝔼₂ → ℝ) x * g x)
        (triangleBoundaryMeasure (T''.1 0) (T''.1 1) (T''.1 2)) := fun T'' ↦
      ((Lp.memLp _).integrable Fact.out).mul_bdd hg.continuous.aestronglyMeasurable
        (Eventually.of_forall hC)
    rw [Finset.sum_congr rfl fun T'' _ ↦ integral_mul_triangleNormal_eq_sum_edgeIntegral
        (f := fun T'' x ↦ (𝒯.elemTraceL p hp T'' u : 𝔼₂ → ℝ) x * g x) (hf T'') i,
      ← Fintype.sum_prod_type' fun T'' b ↦ 𝒯.edgeIntegral
        (fun T'' x ↦ (𝒯.elemTraceL p hp T'' u : 𝔼₂ → ℝ) x * g x) i T'' b] at h0
    obtain ⟨hz1, hz2, hz3⟩ := eqOn_zero_of_tsupport_subset_edgeNhd hgs
    rw [Finset.sum_eq_add_of_mem (T, a) (T', a') (Finset.mem_univ _) (Finset.mem_univ _)
      (fun e ↦ h.1 (congrArg Prod.fst e).symm) (fun c _ hc ↦ ?_)] at h0
    · -- the two remaining edge integrals combine into `νᵢ ∫ g D`
      unfold edgeIntegral at h0
      rw [h.edgeMeasure_eq, h.edgeNormal_eq, PiLp.neg_apply] at h0
      have h0' : ∫ x, (g x • D x) * edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) i
          ∂edgeMeasure (T.1 a) (T.1 (a + 1)) = 0 := by
        refine Eq.trans ?_ h0
        rw [← integral_add]
        · refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          dsimp only
          rw [hD x, smul_eq_mul]; ring
        · exact (hD1.mul_bdd (c := C) hg.continuous.aestronglyMeasurable
            (Eventually.of_forall hC)).mul_const _
        · exact (hD2.mul_bdd (c := C) hg.continuous.aestronglyMeasurable
            (Eventually.of_forall hC)).mul_const _
      rw [integral_mul_const] at h0'
      exact (mul_eq_zero.1 h0').resolve_right hi
    · -- every other edge integral vanishes
      by_cases hcT : c.1 = T
      · have hb : c.2 ≠ a := fun e ↦ hc.1 (Prod.ext hcT e)
        refine edgeIntegral_eq_zero_of_eqOn_zero (fun x hx ↦ ?_) i
        rw [hcT] at hx ⊢
        rw [hz2 c.2 hb hx]; simp
      · by_cases hcT' : c.1 = T'
        · have hb : c.2 ≠ a' := fun e ↦ hc.2 (Prod.ext hcT' e)
          refine edgeIntegral_eq_zero_of_eqOn_zero (fun x hx ↦ ?_) i
          rw [hcT'] at hx ⊢
          rw [hz3 c.2 hb hx]; simp
        · refine edgeIntegral_eq_zero_of_eqOn_zero (fun x hx ↦ ?_) i
          rw [hz1 c.1 hcT hcT' c.2 hx]; simp
  have hD0 : ∀ᵐ x ∂edgeMeasure (T.1 a) (T.1 (a + 1)), x ∈ 𝒯.edgeNhd T a T' a' → D x = 0 :=
    (𝒯.isOpen_edgeNhd T a T' a').ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hDi.locallyIntegrable.locallyIntegrableOn _) key
  filter_upwards [hD0, ae_mem_openSegment (vertex_ne_vertex_add_one T a)] with x hx hxs
  have := hx (openSegment_subset_edgeNhd hI h hxs)
  rw [hD x, sub_eq_zero] at this
  exact this

/-! ### Green's formula on a triangulated domain -/

/-- **Green's formula on a triangulated domain against a $C^1$ test function.** Suppose that the
triangulation has no slits, and let $1 \le p < \infty$. Let $u \in W^{1,p}(\Omega)$, let
$\varphi : \mathbb{R}^2 \to \mathbb{R}$ be of class $C^1$ with compact support, and let $i$ be a
coordinate index. Then $$\int_\Omega \partial_i u \, \varphi \, dx + \int_\Omega u \, \partial_i
\varphi \, dx = \int \gamma u \, \varphi \, \nu_i \, d\sigma.$$

The proof sums the Green formulas of the elements
(`Triangulation.integral_add_integral_eq_sum_elem`) and assembles them with
`Triangulation.sum_integral_mul_triangleNormal_eq`: the interior edges cancel by
`Triangulation.traceL_partner_ae_eq`, and the boundary edges carry the glued trace. -/
theorem green_contDiff (hI : 𝒯.InteriorEdgesSubset) (hp : p ≠ ⊤) (u : SobolevEuclidean 2 1 p Ω)
    {φ : 𝔼₂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (i : Fin 2) :
    (∫ x in (Ω : Set 𝔼₂), (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * φ x)
      + ∫ x in (Ω : Set 𝔼₂), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (𝒯.traceL p hp u : 𝔼₂ → ℝ) x * φ x * 𝒯.outwardNormal x i ∂𝒯.boundaryMeasure := by
  rw [𝒯.integral_add_integral_eq_sum_elem hp u hφ hφc i]
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  refine 𝒯.sum_integral_mul_triangleNormal_eq
    (f := fun T x ↦ (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) x * φ x) (fun T ↦ ?_)
    (fun T a T' a' h ↦ ?_) (g := fun x ↦ (𝒯.traceL p hp u : 𝔼₂ → ℝ) x * φ x)
    (fun T a h ↦ ?_) ?_ i
  · exact ((Lp.memLp _).integrable Fact.out).mul_bdd (c := C) hφ.continuous.aestronglyMeasurable
      (Eventually.of_forall hC)
  · exact (traceL_partner_ae_eq hI hp h u).mono fun x hx ↦ by dsimp only; rw [hx]
  · exact (traceL_ae_eq_triangle hp h u).mono fun x hx ↦ by dsimp only; rw [hx]
  · exact ((Lp.memLp _).integrable Fact.out).mul_bdd (c := C) hφ.continuous.aestronglyMeasurable
      (Eventually.of_forall hC)

/-- **Green's formula on a triangulated domain.** Suppose that the triangulation has no slits, and
let $p$ and $q$ be finite conjugate exponents, $1/p + 1/q = 1$. Then for
$u \in W^{1,p}(\Omega)$, $v \in W^{1,q}(\Omega)$ and each coordinate index $i$, $$\int_\Omega
\partial_i u \, v \, dx + \int_\Omega u \, \partial_i v \, dx = \int \gamma u \, \gamma v \,
\nu_i \, d\sigma.$$ This is [han2009theoretical] (7.6.3) on a polygon, and
[grisvard2011elliptic] Theorem 1.5.3.1 for polygons.

The formula is the sum of the Green formulas of the elements, and the interior edges cancel by
`Triangulation.traceL_partner_ae_eq`. -/
theorem green (hI : 𝒯.InteriorEdgesSubset) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤) (hq : q ≠ ⊤) (u : SobolevEuclidean 2 1 p Ω)
    (v : SobolevEuclidean 2 1 q Ω) (i : Fin 2) :
    (∫ x in (Ω : Set 𝔼₂), (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * fn v x)
      + ∫ x in (Ω : Set 𝔼₂), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼₂ → ℝ) x
      = ∫ x, (𝒯.traceL p hp u : 𝔼₂ → ℝ) x * (𝒯.traceL q hq v : 𝔼₂ → ℝ) x
          * 𝒯.outwardNormal x i ∂𝒯.boundaryMeasure := by
  have hint1 : IntegrableOn
      (fun x ↦ (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * fn v x) (Ω : Set 𝔼₂) := by
    have := (Lp.memLp (weakDeriv u (MultiIndexLE.single i))).integrable_mul (memLp v)
    exact this
  have hint2 : IntegrableOn
      (fun x ↦ fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼₂ → ℝ) x) (Ω : Set 𝔼₂) := by
    have := (memLp u).integrable_mul (Lp.memLp (weakDeriv v (MultiIndexLE.single i)))
    exact this
  rw [𝒯.setIntegral_eq_sum_K hint1, 𝒯.setIntegral_eq_sum_K hint2, ← Finset.sum_add_distrib]
  have hT : ∀ T : 𝒯.elems,
      (∫ x in 𝒯.K T, (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * fn v x)
        + ∫ x in 𝒯.K T, fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼₂ → ℝ) x
        = ∫ x, (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) x * (𝒯.elemTraceL q hq T v : 𝔼₂ → ℝ) x
            * triangleNormal (T.1 0) (T.1 1) (T.1 2) x i
            ∂triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2) := fun T ↦ by
    have hG := (𝒯.elemTraceFamily T).green p q hp hq
      (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p volume (𝒯.Kopens_le T) u)
      (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 q volume (𝒯.Kopens_le T) v) i
    have e1 : ∫ x in 𝒯.K T, (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * fn v x
        = ∫ x in 𝒯.K T, (weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p
            volume (𝒯.Kopens_le T) u) (MultiIndexLE.single i) : 𝔼₂ → ℝ) x
          * fn (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 q volume
            (𝒯.Kopens_le T) v) x := by
      refine integral_congr_ae ?_
      filter_upwards [weakDeriv_restrictL (𝒯.Kopens_le T) u (MultiIndexLE.single i),
        fn_restrictL (𝒯.Kopens_le T) v] with x hx hx'
      rw [hx, hx']
    have e2 : ∫ x in 𝒯.K T, fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼₂ → ℝ) x
        = ∫ x in 𝒯.K T, fn (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 p volume
            (𝒯.Kopens_le T) u) x
          * (weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 q
            volume (𝒯.Kopens_le T) v) (MultiIndexLE.single i) : 𝔼₂ → ℝ) x := by
      refine integral_congr_ae ?_
      filter_upwards [fn_restrictL (𝒯.Kopens_le T) u,
        weakDeriv_restrictL (𝒯.Kopens_le T) v (MultiIndexLE.single i)] with x hx hx'
      rw [hx, hx']
    rw [e1, e2]
    exact hG
  rw [Finset.sum_congr rfl fun T _ ↦ hT T]
  refine 𝒯.sum_integral_mul_triangleNormal_eq
    (f := fun T x ↦ (𝒯.elemTraceL p hp T u : 𝔼₂ → ℝ) x * (𝒯.elemTraceL q hq T v : 𝔼₂ → ℝ) x)
    (fun T ↦ ?_) (fun T a T' a' h ↦ ?_)
    (g := fun x ↦ (𝒯.traceL p hp u : 𝔼₂ → ℝ) x * (𝒯.traceL q hq v : 𝔼₂ → ℝ) x)
    (fun T a h ↦ ?_) ?_ i
  · have := (Lp.memLp (𝒯.elemTraceL p hp T u)).integrable_mul (Lp.memLp (𝒯.elemTraceL q hq T v))
    exact this
  · filter_upwards [traceL_partner_ae_eq hI hp h u, traceL_partner_ae_eq hI hq h v] with x hx hx'
    exact congrArg₂ (fun a b : ℝ ↦ a * b) hx hx'
  · filter_upwards [traceL_ae_eq_triangle hp h u, traceL_ae_eq_triangle hq h v] with x hx hx'
    exact congrArg₂ (fun a b : ℝ ↦ a * b) hx.symm hx'.symm
  · have := (Lp.memLp (𝒯.traceL p hp u)).integrable_mul (Lp.memLp (𝒯.traceL q hq v))
    exact this

variable (𝒯) in
/-- **The trace family of a triangulated domain without slits**: given
`Triangulation.InteriorEdgesSubset`, the trace family (`BoundaryData.TraceFamily`) of the
boundary data `Triangulation.boundaryData`, with the glued trace `Triangulation.traceL` at every
exponent $1 \le p < \infty$, the restriction property
`Triangulation.traceL_ae_eq_of_continuousOn`, and the Green formulas `Triangulation.green` and
`Triangulation.green_contDiff`.

This is the object that the results on polygons take: [han2009theoretical] Examples 11.1.2,
11.2.4, 11.3.11 and 11.4.4 and Proposition 7.6.1 on a polygon, and Theorem 11.4.5. -/
def traceFamily (hI : 𝒯.InteriorEdgesSubset) : 𝒯.boundaryData.TraceFamily where
  traceL p _ hp := 𝒯.traceL p hp
  traceL_ae_eq _ _ hp u _ hu hc := traceL_ae_eq_of_continuousOn hp u hu hc
  green _ q _ _ _ hp hq u v i := 𝒯.green hI q hp hq u v i
  green_contDiff _ _ hp u _ hφ hφc i := 𝒯.green_contDiff hI hp u hφ hφc i

/-- The trace operator of `Triangulation.traceFamily` at an exponent $1 \le p < \infty$ is the glued
trace `Triangulation.traceL`. -/
@[simp]
theorem traceFamily_traceL (hI : 𝒯.InteriorEdgesSubset) (hp : p ≠ ⊤) :
    (𝒯.traceFamily hI).traceL p hp = 𝒯.traceL p hp :=
  rfl

/-! ### Piecewise Sobolev functions: [han2009theoretical] Examples 7.2.7 and 7.2.8 -/

variable (𝒯) in
/-- **The glued derivative**: for $v_T \in W^{1,1}(K_T)$ on each element $T$ and a coordinate index
$i$, the function $$x \mapsto \sum_T \mathbf{1}_{K_T}(x) \, \partial_i v_T(x),$$ equal to
$\partial_i v_T$ on each open element $K_T$ and to $0$ off the open elements.

It is the weak derivative on $\Omega$ of a function continuous on $\overline{\Omega}$ whose
restrictions are the $v_T$ (`Triangulation.hasWeakIteratedLineDerivOn_glueDeriv`). -/
def glueDeriv (v : ∀ T : 𝒯.elems, SobolevEuclidean 2 1 1 (𝒯.Kopens T)) (i : Fin 2) : 𝔼₂ → ℝ :=
  fun x ↦ ∑ T, (𝒯.K T).indicator
    (fun y ↦ (weakDeriv (v T) (MultiIndexLE.single i) : 𝔼₂ → ℝ) y) x

/-- On an open element $K_T$, the glued derivative equals the function of $\partial_i v_T$ at every
point. -/
theorem glueDeriv_eq_of_mem (v : ∀ T : 𝒯.elems, SobolevEuclidean 2 1 1 (𝒯.Kopens T)) (i : Fin 2)
    (T : 𝒯.elems) {x : 𝔼₂} (hx : x ∈ 𝒯.K T) :
    𝒯.glueDeriv v i x = (weakDeriv (v T) (MultiIndexLE.single i) : 𝔼₂ → ℝ) x := by
  unfold glueDeriv
  rw [Finset.sum_eq_single T]
  · rw [indicator_of_mem hx]
  · intro T' _ hT'
    refine indicator_of_notMem (fun hx' ↦ ?_) _
    exact Set.disjoint_left.1 (𝒯.pairwise_disjoint_K hT') hx' hx
  · exact fun h ↦ absurd (Finset.mem_univ T) h

/-- The glued derivative equals $\partial_i v_T$ almost everywhere on the open element $K_T$. -/
theorem glueDeriv_ae_eq (v : ∀ T : 𝒯.elems, SobolevEuclidean 2 1 1 (𝒯.Kopens T)) (i : Fin 2)
    (T : 𝒯.elems) :
    𝒯.glueDeriv v i =ᵐ[volume.restrict (𝒯.K T)] weakDeriv (v T) (MultiIndexLE.single i) :=
  (ae_restrict_iff' (𝒯.isOpen_K T).measurableSet).2
    (Eventually.of_forall fun _ hx ↦ 𝒯.glueDeriv_eq_of_mem v i T hx)

omit [Fact (1 ≤ p)] in
/-- Let $p \in [0, \infty]$. If $\partial_i v_T$ lies in $L^p(K_T)$ for every element $T$, then the
glued derivative lies in $L^p(\Omega)$. -/
theorem memLp_glueDeriv (v : ∀ T : 𝒯.elems, SobolevEuclidean 2 1 1 (𝒯.Kopens T)) (i : Fin 2)
    (hv : ∀ T, MemLp (weakDeriv (v T) (MultiIndexLE.single i) : 𝔼₂ → ℝ) p
      (volume.restrict (𝒯.K T))) :
    MemLp (𝒯.glueDeriv v i) p (volume.restrict (Ω : Set 𝔼₂)) := by
  refine memLp_finsetSum Finset.univ fun T _ ↦ ?_
  rw [memLp_indicator_iff_restrict (𝒯.isOpen_K T).measurableSet.nullMeasurableSet,
    Measure.restrict_restrict (𝒯.isOpen_K T).measurableSet, inter_eq_left.2 (𝒯.K_subset T)]
  exact hv T

/-- **The glued derivative is a weak derivative on $\Omega$.** Let $u : \mathbb{R}^2 \to \mathbb{R}$
be continuous on $\overline{\Omega}$, and for each element $T$ let $v_T \in W^{1,1}(K_T)$ with
$v_T = u$ almost everywhere on $K_T$. Let $i$ be a coordinate index and $g$ the glued derivative
`Triangulation.glueDeriv v i`. Then $u$ and $g$ are locally integrable on $\Omega$, and
$$\int_\Omega \partial_i \varphi \, u \, dx = -\int_\Omega \varphi \, g \, dx$$ for every test
function $\varphi$ on $\Omega$, so $g$ is the weak derivative of $u$ in the direction $e_i$. No
slit hypothesis is needed.

The Green formulas of the elements against $\varphi$ sum to this identity. The boundary terms
vanish because $\varphi = 0$ on $\partial\Omega$, and the interior edges cancel because the
trace of each $v_T$ on $\partial K_T$ is $u$ itself (`BoundaryData.TraceFamily.traceL_ae_eq`),
the same function on both sides. -/
theorem hasWeakIteratedLineDerivOn_glueDeriv {u : 𝔼₂ → ℝ}
    (hu : ContinuousOn u (closure (Ω : Set 𝔼₂)))
    (v : ∀ T : 𝒯.elems, SobolevEuclidean 2 1 1 (𝒯.Kopens T))
    (hv : ∀ T, fn (v T) =ᵐ[volume.restrict (𝒯.K T)] u) (i : Fin 2) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single i (1 : ℝ)] u (𝒯.glueDeriv v i) Ω
      volume where
  locallyIntegrableOn := (𝒯.memLp_restrict_of_continuousOn hu 1).locallyIntegrableOn le_rfl
  locallyIntegrableOn_weakDeriv :=
    (𝒯.memLp_glueDeriv v i fun T ↦ Lp.memLp _).locallyIntegrableOn le_rfl
  integral_smul_eq φ := by
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one, neg_one_mul]
    have hφ : ContDiff ℝ 1 (φ : 𝔼₂ → ℝ) := φ.contDiff.of_le (by simp)
    have hdφ : ContinuousOn (fun x ↦ fderiv ℝ (φ : 𝔼₂ → ℝ) x (EuclideanSpace.single i 1))
        (closure (Ω : Set 𝔼₂)) :=
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
    obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
    -- the two integrals over `Ω` split over the elements
    have h1 : ∫ x in (Ω : Set 𝔼₂), fderiv ℝ (φ : 𝔼₂ → ℝ) x (EuclideanSpace.single i 1) * u x
        = ∑ T, ∫ x in 𝒯.K T, u x * fderiv ℝ (φ : 𝔼₂ → ℝ) x (EuclideanSpace.single i 1) := by
      rw [← 𝒯.setIntegral_eq_sum_K (𝒯.integrableOn_mul_of_memLp_of_continuousOn
        (𝒯.memLp_restrict_of_continuousOn hu 1) hdφ)]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    have h2 : ∫ x in (Ω : Set 𝔼₂), φ x * 𝒯.glueDeriv v i x
        = ∑ T, ∫ x in 𝒯.K T, (weakDeriv (v T) (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * φ x := by
      have e0 : ∫ x in (Ω : Set 𝔼₂), φ x * 𝒯.glueDeriv v i x
          = ∫ x in (Ω : Set 𝔼₂), 𝒯.glueDeriv v i x * φ x :=
        integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
      rw [e0, 𝒯.setIntegral_eq_sum_K (𝒯.integrableOn_mul_of_memLp_of_continuousOn
        (𝒯.memLp_glueDeriv v i fun T ↦ Lp.memLp _) φ.continuous.continuousOn)]
      refine Finset.sum_congr rfl fun T _ ↦ integral_congr_ae ?_
      filter_upwards [𝒯.glueDeriv_ae_eq v i T] with x hx
      rw [hx]
    -- on each element, the triangle's Green formula with `T v_T = u` on `∂K_T`
    have hT : ∀ T : 𝒯.elems,
        (∫ x in 𝒯.K T, (weakDeriv (v T) (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * φ x)
          + ∫ x in 𝒯.K T, u x * fderiv ℝ (φ : 𝔼₂ → ℝ) x (EuclideanSpace.single i 1)
          = ∫ x, u x * φ x * triangleNormal (T.1 0) (T.1 1) (T.1 2) x i
              ∂triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2) := fun T ↦ by
      have hG := (𝒯.elemTraceFamily T).green_contDiff 1 (by simp) (v T) φ hφ φ.hasCompactSupport i
      have htr := (𝒯.elemTraceFamily T).traceL_ae_eq 1 (by simp) (v T) u (hv T)
        (by rw [coe_Kopens, 𝒯.closure_K]; exact hu.mono (𝒯.closedK_subset_closure T))
      have e2 : ∫ x in 𝒯.K T, u x * fderiv ℝ (φ : 𝔼₂ → ℝ) x (EuclideanSpace.single i 1)
          = ∫ x in 𝒯.K T, fn (v T) x * fderiv ℝ (φ : 𝔼₂ → ℝ) x (EuclideanSpace.single i 1) :=
        integral_congr_ae ((hv T).mono fun x hx ↦ by dsimp only; rw [hx])
      have e3 : ∫ x, u x * φ x * triangleNormal (T.1 0) (T.1 1) (T.1 2) x i
            ∂triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2)
          = ∫ x, ((𝒯.elemTraceFamily T).traceL 1 (by simp) (v T) : 𝔼₂ → ℝ) x * φ x
            * triangleNormal (T.1 0) (T.1 1) (T.1 2) x i
            ∂triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2) :=
        integral_congr_ae (htr.mono fun x hx ↦ by dsimp only; rw [hx])
      rw [e2, e3]
      exact hG
    -- the boundary terms: the same function `u φ` on both sides of every interior edge, and
    -- `φ = 0` on the boundary edges
    have hb : ∑ T : 𝒯.elems, ∫ x, u x * φ x * triangleNormal (T.1 0) (T.1 1) (T.1 2) x i
        ∂triangleBoundaryMeasure (T.1 0) (T.1 1) (T.1 2) = 0 := by
      have huφ : ContinuousOn (fun x ↦ u x * φ x) (closure (Ω : Set 𝔼₂)) :=
        hu.mul φ.continuous.continuousOn
      rw [𝒯.sum_integral_mul_triangleNormal_eq (f := fun _ x ↦ u x * φ x)
        (fun T ↦ memLp_one_iff_integrable.1
          ((𝒯.elemBoundaryData T).memLp_of_continuousOn (huφ.mono (by
            rw [coe_Kopens, 𝒯.closure_K]; exact 𝒯.closedK_subset_closure T)) 1))
        (fun _ _ _ _ _ ↦ EventuallyEq.rfl) (g := fun x ↦ u x * φ x) (fun _ _ _ ↦ EventuallyEq.rfl)
        (memLp_one_iff_integrable.1 (𝒯.boundaryData.memLp_of_continuousOn huφ 1)) i]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [𝒯.boundaryData.ae_mem_frontier] with x hx
      rw [Ω.isOpen.frontier_eq] at hx
      rw [φ.zero_on_compl hx.2, Pi.zero_apply, mul_zero, zero_mul]
    rw [h1, h2, eq_neg_iff_add_eq_zero, add_comm, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun T _ ↦ hT T, hb]

/-- **A function continuous on $\overline{\Omega}$ and in $W^{1,p}$ on each element is in
$W^{1,p}(\Omega)$.** Let $1 \le p \le \infty$, and let $u : \mathbb{R}^2 \to \mathbb{R}$ be
continuous on $\overline{\Omega}$ with $u \in W^{1,p}(K_T)$ for every element $T$. Then
$u \in W^{1,p}(\Omega)$. This is [han2009theoretical] Example 7.2.7 on a triangulation, and it
needs no slit hypothesis.

Membership in $W^{1,p}$ is `MemSobolevMultiIndex` for the standard basis. The piecewise $C^1$
case is `Triangulation.memSobolev_of_piecewise`, proved through lines. Here each element gives
$v_T \in W^{1,1}(K_T)$ with function $u$. The glued derivative is the weak derivative on
$\Omega$ (`Triangulation.hasWeakIteratedLineDerivOn_glueDeriv`), and it lies in $L^p(\Omega)$
because on each element it agrees with the derivative there, which lies in $L^p$. -/
theorem memSobolevMultiIndex_of_continuousOn_of_forall {u : 𝔼₂ → ℝ}
    (hu : ContinuousOn u (closure (Ω : Set 𝔼₂)))
    (hT : ∀ T : 𝒯.elems, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis u 1 p
      (𝒯.Kopens T) volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis u 1 p Ω volume := by
  have hfinK : ∀ T : 𝒯.elems, IsFiniteMeasure (volume.restrict (𝒯.Kopens T : Set 𝔼₂)) :=
    fun T ↦ isFiniteMeasure_restrict.2 (𝒯.isBounded_K T).measure_lt_top.ne
  have hT1 : ∀ T : 𝒯.elems, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis u 1 1
      (𝒯.Kopens T) volume := fun T ↦
    ⟨(hT T).1.mono_exponent Fact.out, fun α hα ↦
      let ⟨w, hw, hwp⟩ := (hT T).2 α hα
      ⟨w, hw, hwp.mono_exponent Fact.out⟩⟩
  choose v hv using fun T ↦ (hT1 T).exists_sobolevMultiIndex
  refine SobolevEuclidean.memSobolevMultiIndex_one_of_forall (𝒯.memLp_restrict_of_continuousOn hu p)
    (G := fun i ↦ 𝒯.glueDeriv v i) (fun i ↦ ?_)
    (fun i ↦ 𝒯.hasWeakIteratedLineDerivOn_glueDeriv hu v hv i)
  refine 𝒯.memLp_glueDeriv v i fun T ↦ ?_
  obtain ⟨w, hw, hwp⟩ := (hT T).exists_hasWeakIteratedLineDerivOn_single i
  exact hwp.ae_eq (SobolevEuclidean.weakDeriv_single_ae_eq (v T) (hv T) hw).symm

/-- If $(T', a')$ is the partner of $(T, a)$, the closed edges $[T'_{a'}, T'_{a'+1}]$ and
$[T_a, T_{a+1}]$ are the same set. -/
theorem IsPartner.segment_eq {T T' : 𝒯.elems} {a a' : Fin 3} (h : 𝒯.IsPartner T a T' a') :
    segment ℝ (T'.1 a') (T'.1 (a' + 1)) = segment ℝ (T.1 a) (T.1 (a + 1)) := by
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [h1, h2]
  · rw [h1, h2, segment_symm]

/-- Let $P \neq Q$ in $\mathbb{R}^2$, and let $f, g : \mathbb{R}^2 \to \mathbb{R}$ be continuous on
the segment $[P, Q]$ and equal almost everywhere for its arclength measure. Then $f = g$ on
$[P, Q]$.

The arclength measure charges every relatively open piece of the open segment
(`EuclideanSpace.edgeMeasure_pos_of_isOpen`). -/
theorem _root_.EuclideanSpace.eqOn_segment_of_ae_eq {P Q : 𝔼₂} (hPQ : P ≠ Q) {f g : 𝔼₂ → ℝ}
    (hf : ContinuousOn f (segment ℝ P Q)) (hg : ContinuousOn g (segment ℝ P Q))
    (hfg : f =ᵐ[edgeMeasure P Q] g) : EqOn f g (segment ℝ P Q) := by
  have hc : ContinuousOn (fun x ↦ f x - g x) (segment ℝ P Q) := hf.sub hg
  have hopen : EqOn f g (openSegment ℝ P Q) := by
    intro x hx
    by_contra hne
    obtain ⟨U, hU, hUeq⟩ := (continuousOn_iff'.1 hc) {0}ᶜ isClosed_singleton.isOpen_compl
    have hxU : x ∈ U := by
      have : x ∈ (fun x ↦ f x - g x) ⁻¹' {0}ᶜ ∩ segment ℝ P Q :=
        ⟨fun h0 ↦ hne (sub_eq_zero.1 h0), openSegment_subset_segment ℝ _ _ hx⟩
      rw [hUeq] at this
      exact this.1
    have hpos : 0 < edgeMeasure P Q U := edgeMeasure_pos_of_isOpen hPQ hU ⟨x, hxU, hx⟩
    have hzero : Uᶜ ∈ ae (edgeMeasure P Q) := by
      filter_upwards [hfg, ae_mem_segment P Q] with y hy hys hyU
      have : y ∈ U ∩ segment ℝ P Q := ⟨hyU, hys⟩
      rw [← hUeq] at this
      exact this.1 (sub_eq_zero.2 hy)
    exact hpos.ne' (compl_mem_ae_iff.1 hzero)
  exact hopen.of_subset_closure hf hg (openSegment_subset_segment ℝ _ _)
    (by rw [closure_openSegment])

/-- **A function in $W^{1,p}(\Omega)$ that is continuous on each closed element takes the same
values on both sides of every interior edge.** Suppose that the triangulation has no slits, and
let $1 \le p < \infty$. Let $u \in W^{1,p}(\Omega)$, and for each element $T$ let
$v_T : \mathbb{R}^2 \to \mathbb{R}$ be continuous on the closed element $\overline{K_T}$ and
equal to $u$ almost everywhere on $K_T$. If $(T', a')$ is the partner of $(T, a)$, then
$v_T = v_{T'}$ on the closed common edge $[T_a, T_{a+1}]$. This is [han2009theoretical] Example
7.2.8 on a triangulation without slits.

The traces of $u|_{K_T}$ and $u|_{K_{T'}}$ are $v_T$ and $v_{T'}$ on the edge, and they agree by
`Triangulation.traceL_partner_ae_eq`. Two continuous functions that are equal almost everywhere
for the arclength measure agree on the segment. The book also concludes that the function is
continuous on $\overline{\Omega}$. This needs, in addition, that the elements around each vertex
are connected through shared edges, and it fails at a pinch vertex. -/
theorem eqOn_partner_of_memSobolev_of_continuousOn (hI : 𝒯.InteriorEdgesSubset) (hp : p ≠ ⊤)
    (u : SobolevEuclidean 2 1 p Ω) {v : 𝒯.elems → 𝔼₂ → ℝ}
    (hvc : ∀ T, ContinuousOn (v T) (𝒯.closedK T))
    (hv : ∀ T, fn u =ᵐ[volume.restrict (𝒯.K T)] v T) {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') : EqOn (v T) (v T') (segment ℝ (T.1 a) (T.1 (a + 1))) := by
  have htr : ∀ T'' : 𝒯.elems, (𝒯.elemTraceL p hp T'' u : 𝔼₂ → ℝ)
      =ᵐ[triangleBoundaryMeasure (T''.1 0) (T''.1 1) (T''.1 2)] v T'' := fun T'' ↦
    (𝒯.elemTraceFamily T'').traceL_ae_eq p hp _ (v T'') ((fn_restrictL_ae_eq T'' u).trans (hv T''))
      (by rw [coe_Kopens, 𝒯.closure_K]; exact hvc T'')
  have h2 : (𝒯.elemTraceL p hp T' u : 𝔼₂ → ℝ) =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] v T' := by
    rw [← h.edgeMeasure_eq]
    exact (htr T').filter_mono (ae_mono (edgeMeasure_le_triangleBoundaryMeasure T'.1 a'))
  have hae : v T =ᵐ[edgeMeasure (T.1 a) (T.1 (a + 1))] v T' :=
    (((htr T).filter_mono (ae_mono (edgeMeasure_le_triangleBoundaryMeasure T.1 a))).symm.trans
      (traceL_partner_ae_eq hI hp h u)).trans h2
  have hs : segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ 𝒯.closedK T := 𝒯.segment_subset_closedK T a (a + 1)
  have hs' : segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ 𝒯.closedK T' := by
    rw [← h.segment_eq]
    exact 𝒯.segment_subset_closedK T' a' (a' + 1)
  exact eqOn_segment_of_ae_eq (vertex_ne_vertex_add_one T a) ((hvc T).mono hs) ((hvc T').mono hs')
    hae

/-! ### The direct route for a convex polygon -/

/-- For $P \neq Q$ and any $R$ in $\mathbb{R}^2$, the edge normal `EuclideanSpace.edgeNormal P Q R`
is $c \, (Q - P)^\perp$ for some real $c \neq 0$, where $(Q - P)^\perp$ is
`EuclideanSpace.perp (Q - P)`. -/
theorem _root_.EuclideanSpace.exists_edgeNormal_eq_smul_perp {P Q : 𝔼₂} (hPQ : P ≠ Q) (R : 𝔼₂) :
    ∃ c : ℝ, c ≠ 0 ∧ edgeNormal P Q R = c • perp (Q - P) := by
  have hn : ‖Q - P‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hPQ.symm)
  unfold edgeNormal
  split_ifs
  · exact ⟨‖Q - P‖⁻¹, inv_ne_zero hn, rfl⟩
  · exact ⟨-‖Q - P‖⁻¹, neg_ne_zero.2 (inv_ne_zero hn), by rw [neg_smul]⟩

/-- **The supporting-line property of a convex triangulated domain.** Let $\Omega$ be convex, let
$(T, a)$ be a boundary edge with outward normal $n$ = `EuclideanSpace.edgeNormal (T.1 a) (T.1
(a + 1)) (T.1 (a + 2))`, and let $y \in \Omega$. Then $$\langle n, y - T_a \rangle < 0,$$ that
is, $\Omega$ lies strictly on the inner side of the line through the edge.

If $y$ were on the outer side, the midpoint $m$ of the edge, which lies on $\partial\Omega$,
would lie in the open segment between $y$ and a point of the element beyond $m$
(`EuclideanSpace.exists_ball_inter_subset_openTriangle`), hence in $\Omega$. A point $y$ on the
line is pushed outward along the normal, since $\Omega$ is open. -/
theorem inner_edgeNormal_sub_neg_of_convex (hc : Convex ℝ (Ω : Set 𝔼₂)) {T : 𝒯.elems}
    {a : Fin 3} (h : 𝒯.IsBoundaryEdge T a) {y : 𝔼₂} (hy : y ∈ Ω) :
    ⟪edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)), y - T.1 a⟫_ℝ < 0 := by
  have hli := 𝒯.li_rot T a
  have hs := (linearIndependent_pair_iff_inner_perp_ne_zero _ _).1 hli
  have hn1 : ‖edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2))‖ = 1 := norm_edgeNormal hs
  obtain ⟨c, hc0, hnc⟩ := exists_edgeNormal_eq_smul_perp (vertex_ne_vertex_add_one T a)
    (T.1 (a + 2))
  have hR := inner_edgeNormal_third_neg hs
  -- the midpoint of the edge lies on `∂Ω`, hence off `Ω`
  have hm : midpoint ℝ (T.1 a) (T.1 (a + 1)) ∉ (Ω : Set 𝔼₂) := by
    have := segment_subset_frontier_of_isBoundaryEdge h (midpoint_mem_segment _ _)
    rw [Ω.isOpen.frontier_eq] at this
    exact this.2
  have hmP : midpoint ℝ (T.1 a) (T.1 (a + 1)) - T.1 a = (1 / 2 : ℝ) • (T.1 (a + 1) - T.1 a) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]; module
  -- no point of `Ω` lies strictly on the outer side
  have key : ∀ y ∈ (Ω : Set 𝔼₂),
      ¬ 0 < ⟪edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)), y - T.1 a⟫_ℝ := by
    intro y hy hpos
    obtain ⟨δ, hδ, hball⟩ := exists_ball_inter_subset_openTriangle hli
    rw [hnc, real_inner_smul_left] at hpos hR
    have hprod : ⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ
        * ⟪perp (T.1 (a + 1) - T.1 a), y - T.1 a⟫_ℝ < 0 := by
      have := mul_neg_of_neg_of_pos hR hpos
      have hc2 : 0 < c * c := mul_self_pos.2 hc0
      nlinarith
    -- the point of the element beyond the midpoint, away from `y`
    obtain ⟨s, hs0, hs1⟩ : ∃ s : ℝ, 0 < s ∧
        s * ‖y - midpoint ℝ (T.1 a) (T.1 (a + 1))‖ < δ :=
      ⟨δ / (2 * (‖y - midpoint ℝ (T.1 a) (T.1 (a + 1))‖ + 1)), by positivity, by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (y - midpoint ℝ (T.1 a) (T.1 (a + 1)))]⟩
    have hym : ⟪perp (T.1 (a + 1) - T.1 a), y - midpoint ℝ (T.1 a) (T.1 (a + 1))⟫_ℝ
        = ⟪perp (T.1 (a + 1) - T.1 a), y - T.1 a⟫_ℝ := by
      rw [show y - midpoint ℝ (T.1 a) (T.1 (a + 1))
          = (y - T.1 a) - (midpoint ℝ (T.1 a) (T.1 (a + 1)) - T.1 a) by abel, inner_sub_right,
        hmP, inner_smul_right, inner_perp_self, mul_zero, sub_zero]
    have hz : midpoint ℝ (T.1 a) (T.1 (a + 1)) + (-s) • (y - midpoint ℝ (T.1 a) (T.1 (a + 1)))
        ∈ (Ω : Set 𝔼₂) := by
      refine 𝒯.K_subset T ?_
      rw [K_eq_rot T a]
      refine hball _ ?_ ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hs0]; exact hs1
      · rw [inner_smul_right, hym]; nlinarith
    -- the midpoint lies between `y` and that point
    refine hm (hc.openSegment_subset hy hz ?_)
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 / (1 + s), ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩, ?_⟩
    rw [lineMap_eq, show midpoint ℝ (T.1 a) (T.1 (a + 1))
        + (-s) • (y - midpoint ℝ (T.1 a) (T.1 (a + 1))) - y
        = (1 + s) • (midpoint ℝ (T.1 a) (T.1 (a + 1)) - y) by module, smul_smul, one_div,
      inv_mul_cancel₀ (by positivity : (1 + s : ℝ) ≠ 0), one_smul, add_sub_cancel]
  -- push `y` outward along the normal
  by_contra hcon
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen y hy
  have hy' : y + (ε / 2) • edgeNormal (T.1 a) (T.1 (a + 1)) (T.1 (a + 2)) ∈ (Ω : Set 𝔼₂) := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hn1, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  refine key _ hy' ?_
  rw [add_sub_right_comm, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hn1,
    not_lt] at *
  nlinarith

/-- **A convex triangulated domain has a transversal field.** If $\Omega$ is convex and nonempty,
the boundary data `Triangulation.boundaryData` have a transversal field
(`BoundaryData.HasTransversalField`).

The field is $w(x) = \chi(x) \, \delta^{-1} (x - x_0)$ for an interior point $x_0$, a bump
function $\chi$ equal to $1$ on $\overline{\Omega}$, and $\delta > 0$ the least of the distances
$\langle n_e, P_e - x_0 \rangle$ from $x_0$ to the lines through the boundary edges $e$
(`Triangulation.inner_edgeNormal_sub_neg_of_convex`). Along a boundary edge,
$\langle x - x_0, n_e \rangle$ is constant (`EuclideanSpace.inner_edgeNormal_lineMap_sub`). -/
theorem hasTransversalField_of_convex (hc : Convex ℝ (Ω : Set 𝔼₂))
    (hne : (Ω : Set 𝔼₂).Nonempty) : 𝒯.boundaryData.HasTransversalField := by
  obtain ⟨x₀, hx₀⟩ := hne
  by_cases hE : 𝒯.boundaryEdges.Nonempty
  · -- the least distance from `x₀` to the lines through the boundary edges
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 𝒯.boundaryEdges.inf' hE fun e ↦
        ⟪edgeNormal (e.1.1 e.2) (e.1.1 (e.2 + 1)) (e.1.1 (e.2 + 2)), e.1.1 e.2 - x₀⟫_ℝ :=
      ⟨_, rfl⟩
    have hδ0 : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]
      intro e he
      have := inner_edgeNormal_sub_neg_of_convex hc (mem_boundaryEdges.1 he) hx₀
      rw [← neg_sub, inner_neg_right] at this
      linarith
    have hδe : ∀ e ∈ 𝒯.boundaryEdges,
        δ ≤ ⟪edgeNormal (e.1.1 e.2) (e.1.1 (e.2 + 1)) (e.1.1 (e.2 + 2)), e.1.1 e.2 - x₀⟫_ℝ :=
      fun e he ↦ hδ ▸ Finset.inf'_le _ he
    -- the bump equal to `1` on the closure of the domain
    obtain ⟨r, hr⟩ := 𝒯.isCompact_closure.isBounded.subset_closedBall x₀
    let χ : ContDiffBump x₀ := ⟨max r 0 + 1, max r 0 + 2, by positivity, by linarith⟩
    have hχ : ∀ x ∈ closure (Ω : Set 𝔼₂), χ x = 1 := fun x hx ↦
      χ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall
        (by linarith [le_max_left r 0]) (hr hx))
    refine ⟨fun x ↦ χ x • (δ⁻¹ • (x - x₀)), ?_, ?_, ?_⟩
    · exact χ.contDiff.smul ((contDiff_id.sub contDiff_const).const_smul δ⁻¹)
    · exact χ.hasCompactSupport.smul_right (f' := fun x ↦ δ⁻¹ • (x - x₀))
    · change ∀ᵐ x ∂𝒯.boundaryMeasure, 1 ≤ ⟪_, 𝒯.outwardNormal x⟫_ℝ
      refine ae_boundaryMeasure_iff.2 fun e he ↦ ?_
      refine (ae_mem_openSegment (vertex_ne_vertex_add_one e.1 e.2)).mono fun x hx ↦ ?_
      have hxc : x ∈ closure (Ω : Set 𝔼₂) :=
        𝒯.segment_subset_closure e.1 e.2 (e.2 + 1) (openSegment_subset_segment ℝ _ _ hx)
      rw [outwardNormal_eq_edgeNormal (mem_boundaryEdges.1 he) hx, hχ x hxc, one_smul,
        real_inner_smul_left, real_inner_comm, le_inv_mul_iff₀ hδ0, mul_one]
      rw [openSegment_eq_image_lineMap] at hx
      obtain ⟨t, -, rfl⟩ := hx
      rw [inner_edgeNormal_lineMap_sub]
      exact hδe e he
  · -- no boundary edge: the surface measure vanishes
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    change ∀ᵐ x ∂𝒯.boundaryMeasure, _
    rw [boundaryMeasure, Finset.not_nonempty_iff_eq_empty.1 hE, Finset.sum_empty, ae_zero]
    exact Filter.eventually_bot

variable (𝒯) in
/-- **The direct construction of the trace family of a convex polygon**: for a convex nonempty
triangulated domain, the construction `BoundaryData.traceFamily` on $\Omega$ itself, with the
transversal field `Triangulation.hasTransversalField_of_convex` and the density theorems for
bounded convex open sets (`Convex.hasSmoothDensity`, `Convex.hasUniformSmoothDensity`).

Its trace operator is the glued trace (`Triangulation.traceFamily_of_convex_traceL`). -/
def traceFamily_of_convex (hc : Convex ℝ (Ω : Set 𝔼₂)) (hne : (Ω : Set 𝔼₂).Nonempty) :
    𝒯.boundaryData.TraceFamily :=
  BoundaryData.traceFamily _ (𝒯.hasTransversalField_of_convex hc hne)
    (fun _ _ hq ↦ Convex.hasSmoothDensity 𝒯.isBounded hc hne hq)
    (fun _ _ hq ↦ Convex.hasUniformSmoothDensity 𝒯.isBounded hc hne hq)

/-- **The two constructions of the trace of a convex polygon agree.** Let $\Omega$ be convex and
nonempty, suppose that the triangulation has no slits, and let $1 \le p < \infty$. Then the
trace operator of `Triangulation.traceFamily_of_convex` at $p$ is the glued trace
`Triangulation.traceL`.

This is the uniqueness of the trace, `BoundaryData.TraceFamily.traceL_eq_of_hasSmoothDensity`.
The no-slit hypothesis also follows from convexity
(`Triangulation.interiorEdgesSubset_of_convex`). -/
theorem traceFamily_of_convex_traceL (hc : Convex ℝ (Ω : Set 𝔼₂)) (hne : (Ω : Set 𝔼₂).Nonempty)
    (hI : 𝒯.InteriorEdgesSubset) (hp : p ≠ ⊤) :
    (𝒯.traceFamily_of_convex hc hne).traceL p hp = 𝒯.traceL p hp :=
  BoundaryData.TraceFamily.traceL_eq_of_hasSmoothDensity 𝒯.boundaryData
    (𝒯.traceFamily_of_convex hc hne) (𝒯.traceFamily hI) hp
    (Convex.hasSmoothDensity 𝒯.isBounded hc hne hp)

/-- **A convex triangulated domain has no slits**: if $\Omega$ is convex, the relative interior of
every interior edge lies in $\Omega$ (`Triangulation.InteriorEdgesSubset`).

A point $x$ of the open edge outside $\Omega$ is separated from the convex open set $\Omega$ by
a linear functional $f$ with $f < f(x)$ on $\Omega$ (`geometric_hahn_banach_open_point`). Then
$f$ vanishes on the direction of the edge, because both directions from $x$ along the edge stay
in $\overline{\Omega}$, and $f$ is negative on $R - P$ and on $R' - P$ for the third vertices
$R$, $R'$ of the two elements. These vertices lie on opposite sides of the edge, a
contradiction. -/
theorem interiorEdgesSubset_of_convex (hc : Convex ℝ (Ω : Set 𝔼₂)) : 𝒯.InteriorEdgesSubset := by
  intro T a hb x hx
  obtain ⟨T', a', h⟩ := (not_isBoundaryEdge_iff_exists_partner T a).1 hb
  by_contra hxΩ
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hc Ω.isOpen hxΩ
  have hfc : ∀ y ∈ closure (Ω : Set 𝔼₂), f y ≤ f x :=
    closure_minimal (fun y hy ↦ (hf y hy).le) (isClosed_le f.continuous continuous_const)
  have hli := 𝒯.li_rot T a
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_openSegment_iff'.1 hx
  -- `f` vanishes along the edge
  have hfQ : f (T.1 (a + 1) - T.1 a) = 0 := by
    obtain ⟨s, hs0, hs1, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s < t ∧ t + s < 1 :=
      ⟨min t (1 - t) / 2, by positivity, by linarith [min_le_left t (1 - t)],
        by linarith [min_le_right t (1 - t)]⟩
    have h1 := hfc _ (𝒯.segment_subset_closure T a (a + 1) (openSegment_subset_segment ℝ _ _
      (mem_openSegment_iff'.2 ⟨t + s, by linarith, hs2, rfl⟩)))
    have h2 := hfc _ (𝒯.segment_subset_closure T a (a + 1) (openSegment_subset_segment ℝ _ _
      (mem_openSegment_iff'.2 ⟨t - s, by linarith, by linarith, rfl⟩)))
    simp only [map_add, map_smul, smul_eq_mul] at h1 h2
    nlinarith
  -- `f` is negative on the third vertices, from the two elements
  have hfR : ∀ R : 𝔼₂, openTriangle (T.1 a) (T.1 (a + 1)) R ⊆ Ω → f (R - T.1 a) < 0 := by
    intro R hR
    have hz : T.1 a + (t / 2) • (T.1 (a + 1) - T.1 a) + (1 / 2 : ℝ) • (R - T.1 a)
        ∈ openTriangle (T.1 a) (T.1 (a + 1)) R :=
      mem_openTriangle.2 ⟨t / 2, 1 / 2, by positivity, by norm_num, by linarith, rfl⟩
    have := hf _ (hR hz)
    simp only [map_add, map_smul, smul_eq_mul, hfQ, mul_zero, add_zero] at this
    linarith
  have hR := hfR (T.1 (a + 2)) (by rw [← K_eq_rot T a]; exact 𝒯.K_subset T)
  have hR' := hfR (T'.1 (a' + 2)) (by rw [← h.K_eq]; exact 𝒯.K_subset T')
  -- the third vertices lie on opposite sides of the edge
  obtain ⟨w, hw⟩ : ∃ w : 𝔼₂, T'.1 (a' + 2) - T.1 a
      = w 0 • (T.1 (a + 1) - T.1 a) + w 1 • (T.1 (a + 2) - T.1 a) :=
    ⟨(triangleEquiv _ _ _ hli).symm (T'.1 (a' + 2) - T.1 a), by
      rw [← triangleEquiv_apply _ _ _ hli, ContinuousLinearEquiv.apply_symm_apply]⟩
  have hw1 : w 1 < 0 := by
    have hneg := h.inner_perp_mul_neg
    rw [hw, inner_add_right, inner_smul_right, inner_smul_right, inner_perp_self, mul_zero,
      zero_add] at hneg
    nlinarith [mul_self_nonneg ⟪perp (T.1 (a + 1) - T.1 a), T.1 (a + 2) - T.1 a⟫_ℝ]
  rw [hw, map_add, map_smul, map_smul, hfQ, smul_zero, zero_add, smul_eq_mul] at hR'
  nlinarith

end Triangulation

end
