/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Boundary.PolygonTrace
import Numlib.Approximation.SobolevInterpolation
import Numlib.MeasureTheory.Integral.Bochner.Set

/-!
# Linear interpolation error on the boundary of a polygon

Let $\Omega \subseteq \mathbb{R}^2$ be an open set with a triangulation $\mathcal{T}$ of mesh size
$h$, and let $\Pi_h$ be the continuous piecewise linear interpolant on $\mathcal{T}$. A boundary
edge of $\mathcal{T}$ is an edge $[T_a, T_{a+1}]$ of an element $T$ whose two ends are not both
vertices of another element. Suppose that every boundary edge lies on one of finitely many sides
$[P_k, Q_k]$ with $P_k \ne Q_k$. Let $\tilde u$ be continuous on $\overline\Omega$, and suppose that
for each $k$ the restriction $r \mapsto \tilde u(P_k + r(Q_k - P_k))$ agrees almost everywhere on
$(0, 1)$ with an element $U_k$ of $H^2(0, 1)$. This module proves
$$\int_{\partial\Omega} (\tilde u - \Pi_h \tilde u)^2 \, ds \le h^4 \sum_k \|Q_k - P_k\|^{-3}
  |U_k|_{H^2(0, 1)}^2,$$
where $ds$ is the arclength measure of the boundary edges. The term
$\|Q_k - P_k\|^{-3} |U_k|_{H^2(0, 1)}^2$ is the squared $H^2$ seminorm of $\tilde u$ along side $k$
in the arclength variable. The same bound, after a square root, holds for the $L^2(\partial\Omega)$
norm of the trace of an element of $H^1(\Omega)$ whose function is $\Pi_h \tilde u - \tilde u$.

This is the boundary term of the error estimate in Example 11.4.4 of [han2009theoretical], for the
friction problem discretized by linear elements on a polygon.

## Main results

* `integral_sq_sub_affine_le`: on a panel $[s, t] \subseteq [0, 1]$, the affine interpolant $G$ of a
  function $f$ with $f'' = U''$ satisfies $\int_s^t (f - G)^2 \le (t - s)^4 \int_s^t |U''|^2$.
* `Triangulation.globalInterp_linear_lineMap`: along an edge, $\Pi_h v$ is the affine interpolant of
  $v$ at the two ends of the edge.
* `Triangulation.integral_sq_sub_globalInterp_edge_le`: the $L^2$ error of $\Pi_h \tilde u$ on one
  boundary edge $[A + s(B - A), A + t(B - A)]$ is at most $\|B - A\| (t - s)^4 \int_s^t |U''|^2$.
* `Triangulation.integral_sq_sub_globalInterp_boundaryMeasure_le`: the estimate of
  $\int_{\partial\Omega} (\tilde u - \Pi_h \tilde u)^2 \, ds$ above.
* `Triangulation.norm_traceL_sub_globalInterp_le`: the same estimate for the $L^2(\partial\Omega)$
  norm of the trace of $\Pi_h \tilde u - \tilde u$.

## Proof outline

Along a side, the linear interpolant is the one-dimensional affine interpolant of the restriction of
$\tilde u$ at the ends of the edge. So the one-panel case of the one-dimensional estimate
`integral_sq_sub_piecewiseLinearInterpCLM_le` of `Numlib.Approximation.SobolevInterpolation` bounds
the error on each boundary edge. An edge has length $(t - s)\|B - A\| \le h$, which turns
$(t - s)^4$ into $h^4 \|B - A\|^{-4}$. The open boundary edges are pairwise disjoint, so the
parameter intervals of the edges on one side are pairwise disjoint, and the estimates of the single
edges add up to the seminorm over the whole side.

## Implementation notes

* The linear interpolant is `Triangulation.globalInterp` with the vertices
  `EuclideanSpace.referenceTriangleVertex` of the reference triangle as nodes and the barycentric
  coordinates `EuclideanSpace.baryCoord` as shape functions.
* The arclength measure of $\partial\Omega$ is `Triangulation.boundaryMeasure`, the sum of the
  arclength measures `EuclideanSpace.edgeMeasure` of the boundary edges. Side $k$ is parametrized by
  `AffineMap.lineMap (P k) (Q k)`, that is, $r \mapsto P_k + r(Q_k - P_k)$.
* The restriction of $\tilde u$ to side $k$ enters as an element `Us k : SobolevInterval 2 0 1`
  whose function agrees almost everywhere on $(0, 1)$ with the pulled-back function. Its seminorm
  `SobolevInterval.seminorm 2 0 1` is the $L^2(0, 1)$ norm of the weak second derivative.
* The trace estimate uses the trace family `Triangulation.traceFamily`, which needs the hypothesis
  `Triangulation.InteriorEdgesSubset` that the relative interior of every interior edge lies in
  $\Omega$.
-/

open Filter MeasureTheory Set TopologicalSpace Topology EuclideanSpace SobolevMultiIndex
  intervalIntegral

noncomputable section

/-- Local notation for the Euclidean plane $\mathbb{R}^2$, the type `EuclideanSpace ℝ (Fin 2)`. -/
local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- Let $U \in H^2(0, 1)$ have the weak second derivative $U''$, and let
$f : \mathbb{R} \to \mathbb{R}$ be continuously differentiable with
$$f'(r') - f'(r) = \int_r^{r'} U''(x) \, dx \quad \text{for all } r, r' \in [0, 1].$$
Let $0 \le s < t \le 1$, and let $G$ agree on $[s, t]$ with the affine interpolant of $f$ at $s$
and $t$, that is, $G(r) = f(s) + (f(t) - f(s)) (r - s) / (t - s)$. Then
$$\int_s^t (f - G)^2 \le (t - s)^4 \int_s^t |U''|^2.$$

The hypothesis on $f$ holds for the continuously differentiable representative of $U$, but the
statement links only $f'$ to $U''$. The function $U''$ is
`SobolevInterval.deriv U (Fin.last 2)`. The proof applies
`integral_sq_sub_piecewiseLinearInterpCLM_le` to the partition $\{s, t\}$ with one panel. -/
theorem integral_sq_sub_affine_le (U : SobolevInterval 2 0 1) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfU : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      deriv f r' - deriv f r = ∫ x in r..r', SobolevInterval.deriv U (Fin.last 2) x)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) {G : ℝ → ℝ}
    (hG : ∀ r ∈ Icc s t, G r = f s + (f t - f s) * ((r - s) / (t - s))) :
    ∫ r in s..t, (f r - G r) ^ 2
      ≤ (t - s) ^ 4 * ∫ r in s..t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 := by
  let x : ℕ → Icc s t := fun j ↦
    if j = 0 then ⟨s, left_mem_Icc.2 hst.le⟩ else ⟨t, right_mem_Icc.2 hst.le⟩
  have hx0 : (x 0 : ℝ) = s := by simp [x]
  have hx1 : (x 1 : ℝ) = t := by simp [x]
  have hstep : ∀ i ≤ 0, (x i : ℝ) < (x (i + 1) : ℝ) := by
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [hx0, hx1]
    exact hst
  have hmesh : ∀ j ≤ 0, (x (j + 1) : ℝ) - (x j : ℝ) ≤ t - s := by
    intro j hj
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    rw [hx0, hx1]
  have hsub : uIcc s t ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hst.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hs ht
  let F : C(Icc s t, ℝ) := ⟨fun r ↦ f r, hf.continuous.comp continuous_subtype_val⟩
  refine integral_sq_sub_piecewiseLinearInterpCLM_le ⟨fun i hi ↦ hstep i (by omega), hx0, hx1⟩
    hmesh hf
    ((SobolevInterval.intervalIntegrable_deriv zero_le_one U _).mono_set hsub)
    ((SobolevInterval.intervalIntegrable_deriv_sq zero_le_one U _).mono_set hsub)
    (fun r hr r' hr' ↦ hfU r ⟨hs.trans hr.1, hr.2.trans ht⟩ r' ⟨hs.trans hr'.1, hr'.2.trans ht⟩)
    (F := F) (fun r ↦ rfl) (fun r ↦ ?_)
  rw [piecewiseLinearInterpCLM_apply_of_mem hstep F le_rfl (by rw [hx0]; exact r.2.1)
    (by rw [hx1]; exact r.2.2), hG r r.2]
  simp only [F, ContinuousMap.coe_mk, hx0, hx1]

/-- Let $A, B \in \mathbb{R}^2$ and $s < t$, write $x(r) = A + r(B - A)$, and let
$F : \mathbb{R}^2 \to \mathbb{R}$ be continuous on the segment $[x(s), x(t)]$. Then the integral
of $F$ with respect to the arclength measure of this segment is
$$\int_{[x(s), x(t)]} F \, ds = \|B - A\| \int_s^t F(x(r)) \, dr.$$

The arclength measure of the segment $[P, Q]$ is `EuclideanSpace.edgeMeasure P Q`, and $x(r)$ is
`AffineMap.lineMap A B r`. -/
theorem integral_edgeMeasure_lineMap {A B : 𝔼₂} {s t : ℝ} (hst : s < t) {F : 𝔼₂ → ℝ}
    (hF : ContinuousOn F (segment ℝ (AffineMap.lineMap A B s) (AffineMap.lineMap A B t))) :
    ∫ x, F x ∂edgeMeasure (AffineMap.lineMap A B s) (AffineMap.lineMap A B t)
      = ‖B - A‖ * ∫ r in s..t, F (AffineMap.lineMap A B r) := by
  rw [integral_edgeMeasure hF]
  have hQP : AffineMap.lineMap A B t - AffineMap.lineMap A B s = (t - s) • (B - A) := by
    simp only [lineMap_eq]
    module
  have hcomp : ∀ r : ℝ, AffineMap.lineMap (AffineMap.lineMap A B s) (AffineMap.lineMap A B t) r
      = AffineMap.lineMap A B ((t - s) * r + s) := by
    intro r
    simp only [lineMap_eq]
    module
  simp_rw [hcomp]
  rw [integral_comp_mul_add (fun r ↦ F (AffineMap.lineMap A B r)) (sub_ne_zero.2 hst.ne') s,
    hQP, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.2 hst)]
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul]
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  field_simp

namespace Triangulation

variable {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)

/-- Every edge of an element of $\mathcal{T}$ has length at most the mesh size: for an element with
vertices $T_0, T_1, T_2$ and any indices $a, b$, $\|T_b - T_a\| \le h$.

The mesh size $h$ is `Triangulation.meshSize`, the supremum of the diameters of the open
elements. -/
theorem norm_vertex_sub_le_meshSize (T : 𝒯.elems) (a b : Fin 3) :
    ‖T.1 b - T.1 a‖ ≤ 𝒯.meshSize := by
  rw [← dist_eq_norm]
  refine (Metric.dist_le_diam_of_mem (𝒯.isCompact_closedK T).isBounded (𝒯.vertex_mem_closedK T b)
    (𝒯.vertex_mem_closedK T a)).trans ?_
  rw [← 𝒯.closure_K, Metric.diam_closure]
  exact 𝒯.diam_le_meshSize T

/-- Let $T$ be an element of $\mathcal{T}$ with vertices $T_0, T_1, T_2$, with indices taken modulo
$3$, and let $A, B \in \mathbb{R}^2$. If the edge $[T_a, T_{a+1}]$ lies in the segment $[A, B]$,
then there are $0 \le s < t \le 1$ such that either $T_a = A + s(B - A)$ and
$T_{a+1} = A + t(B - A)$, or $T_a = A + t(B - A)$ and $T_{a+1} = A + s(B - A)$. -/
theorem exists_param_of_segment_subset {A B : 𝔼₂} (T : 𝒯.elems) (a : Fin 3)
    (h : segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ A B) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
      ((T.1 a = AffineMap.lineMap A B s ∧ T.1 (a + 1) = AffineMap.lineMap A B t) ∨
        (T.1 a = AffineMap.lineMap A B t ∧ T.1 (a + 1) = AffineMap.lineMap A B s)) := by
  obtain ⟨s₀, hs₀0, hs₀1, hs₀⟩ := mem_segment_iff'.1 (h (left_mem_segment ℝ _ _))
  obtain ⟨t₀, ht₀0, ht₀1, ht₀⟩ := mem_segment_iff'.1 (h (right_mem_segment ℝ _ _))
  rw [← lineMap_eq] at hs₀ ht₀
  have hne : s₀ ≠ t₀ := fun e ↦ 𝒯.vertex_ne_vertex_add_one T a (by rw [hs₀, ht₀, e])
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨s₀, t₀, hs₀0, hlt, ht₀1, Or.inl ⟨hs₀, ht₀⟩⟩
  · exact ⟨t₀, s₀, ht₀0, hlt, hs₀1, Or.inr ⟨hs₀, ht₀⟩⟩

/-- For $s < t$ and $r \in (s, t)$, the point $A + r(B - A)$ lies in the open segment between
$A + s(B - A)$ and $A + t(B - A)$. -/
private theorem lineMap_mem_openSegment_of_mem_Ioo {A B : 𝔼₂} {s t : ℝ} (hst : s < t) {r : ℝ}
    (hr : r ∈ Ioo s t) :
    AffineMap.lineMap A B r
      ∈ openSegment ℝ (AffineMap.lineMap A B s) (AffineMap.lineMap A B t) := by
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  rw [mem_openSegment_iff']
  refine ⟨(r - s) / (t - s), div_pos (sub_pos.2 hr.1) (sub_pos.2 hst),
    (div_lt_one (sub_pos.2 hst)).2 (sub_lt_sub_right hr.2 s), ?_⟩
  simp only [lineMap_eq]
  rw [show A + t • (B - A) - (A + s • (B - A)) = (t - s) • (B - A) by module, smul_smul,
    div_mul_cancel₀ _ hts]
  module

/-- For $s \le t$, the points $A + s(B - A)$ and $A + t(B - A)$ are at distance $(t - s)\|B - A\|$.
-/
private theorem norm_lineMap_sub_lineMap (A B : 𝔼₂) {s t : ℝ} (hst : s ≤ t) :
    ‖AffineMap.lineMap A B t - AffineMap.lineMap A B s‖ = (t - s) * ‖B - A‖ := by
  rw [show AffineMap.lineMap A B t - AffineMap.lineMap A B s = (t - s) • (B - A) by
    simp only [lineMap_eq]; module, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)]

/-- Let $A, B \in \mathbb{R}^2$ and $s < t$, and let $T$ be an element of $\mathcal{T}$ with two
vertices $T_b = A + s(B - A)$ and $T_c = A + t(B - A)$. Then for every function
$v : \mathbb{R}^2 \to \mathbb{R}$ and every $r \in [s, t]$, the continuous piecewise linear
interpolant satisfies
$$\Pi_h v(A + r(B - A)) = v(T_b) + (v(T_c) - v(T_b)) \frac{r - s}{t - s}.$$
So along an edge, $\Pi_h v$ is the affine interpolant of $v$ at the two ends of the edge.

The interpolant $\Pi_h$ is `Triangulation.globalInterp` with the nodes
`EuclideanSpace.referenceTriangleVertex` and the shape functions `EuclideanSpace.baryCoord`. The
proof uses `Triangulation.localInterp_lineMap` for these affine shape functions. -/
theorem globalInterp_linear_lineMap {A B : 𝔼₂} {s t : ℝ} (hst : s < t) (T : 𝒯.elems) (b c : Fin 3)
    (hb : T.1 b = AffineMap.lineMap A B s) (hc : T.1 c = AffineMap.lineMap A B t) (v : 𝔼₂ → ℝ)
    {r : ℝ} (hr : r ∈ Icc s t) :
    𝒯.globalInterp referenceTriangleVertex baryCoord v (AffineMap.lineMap A B r)
      = v (T.1 b) + (v (T.1 c) - v (T.1 b)) * ((r - s) / (t - s)) := by
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  have hpt : AffineMap.lineMap A B r = T.1 b + ((r - s) / (t - s)) • (T.1 c - T.1 b) := by
    rw [hb, hc]
    simp only [lineMap_eq]
    rw [show A + t • (B - A) - (A + s • (B - A)) = (t - s) • (B - A) by module, smul_smul,
      div_mul_cancel₀ _ hts]
    module
  have hmem : AffineMap.lineMap A B r ∈ 𝒯.closedK T := by
    refine 𝒯.segment_subset_closedK T b c ?_
    rw [hpt, mem_segment_iff']
    exact ⟨_, div_nonneg (sub_nonneg.2 hr.1) (sub_nonneg.2 hst.le),
      div_le_one_of_le₀ (sub_le_sub_right hr.2 s) (sub_nonneg.2 hst.le), rfl⟩
  rw [𝒯.globalInterp_eq_of_mem_closedK _ _ 𝒯.isConformingElement_linear T v hmem, hpt,
    𝒯.localInterp_lineMap _ _ baryCoord_lineMap, 𝒯.localInterp_linear_vertex,
    𝒯.localInterp_linear_vertex]
  ring

/-- Let $A, B \in \mathbb{R}^2$, let $\tilde u : \mathbb{R}^2 \to \mathbb{R}$ be continuous on
$\overline\Omega$, and let $U \in H^2(0, 1)$ agree almost everywhere on $(0, 1)$ with
$r \mapsto \tilde u(A + r(B - A))$. Let $0 \le s < t \le 1$, and let $T$ be an element of
$\mathcal{T}$ with two vertices $T_b = A + s(B - A)$ and $T_c = A + t(B - A)$. Then the linear
interpolant satisfies
$$\int_{[T_b, T_c]} (\tilde u - \Pi_h \tilde u)^2 \, ds \le \|B - A\| (t - s)^4 \int_s^t
  |U''|^2,$$
where $ds$ is the arclength measure of the segment $[T_b, T_c]$.

The measure is `EuclideanSpace.edgeMeasure (T b) (T c)`, and $U''$ is
`SobolevInterval.deriv U (Fin.last 2)`. The proof combines
`Triangulation.globalInterp_linear_lineMap`, `integral_edgeMeasure_lineMap` and
`integral_sq_sub_affine_le`. -/
theorem integral_sq_sub_globalInterp_edge_le {A B : 𝔼₂} {ũ : 𝔼₂ → ℝ}
    (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (U : SobolevInterval 2 0 1)
    (hU : SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap A B r))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) (T : 𝒯.elems) (b c : Fin 3)
    (hb : T.1 b = AffineMap.lineMap A B s) (hc : T.1 c = AffineMap.lineMap A B t) :
    ∫ x, (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2
        ∂edgeMeasure (T.1 b) (T.1 c)
      ≤ ‖B - A‖ * (t - s) ^ 4 * ∫ r in s..t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 := by
  obtain ⟨f, hf, hae, hftc⟩ := SobolevInterval.exists_contDiff_ae_eq zero_lt_one U
  have hf0 : SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f := by
    rw [← SobolevInterval.deriv_zero U]
    simpa using hae 0
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  -- the parametrization maps `[s, t]` onto the edge, which lies in `Ω̄`
  have hseg : ∀ r ∈ Icc s t, AffineMap.lineMap A B r ∈ segment ℝ (T.1 b) (T.1 c) := by
    intro r hr
    rw [hb, hc, mem_segment_iff']
    refine ⟨(r - s) / (t - s), div_nonneg (sub_nonneg.2 hr.1) (sub_nonneg.2 hst.le),
      div_le_one_of_le₀ (sub_le_sub_right hr.2 s) (sub_nonneg.2 hst.le), ?_⟩
    simp only [lineMap_eq]
    rw [show A + t • (B - A) - (A + s • (B - A)) = (t - s) • (B - A) by module, smul_smul,
      div_mul_cancel₀ _ hts]
    module
  have hcl : ∀ r ∈ Icc s t, AffineMap.lineMap A B r ∈ closure (Ω : Set 𝔼₂) := fun r hr ↦
    𝒯.segment_subset_closure T b c (hseg r hr)
  have hcont : ContinuousOn (fun r ↦ ũ (AffineMap.lineMap A B r)) (Icc s t) :=
    hũc.comp (continuous_lineMap A B).continuousOn hcl
  have hfeq : EqOn f (fun r ↦ ũ (AffineMap.lineMap A B r)) (Icc s t) :=
    eqOn_Icc_of_ae_eq hst hf.continuous.continuousOn hcont
      ((hf0.symm.trans hU).filter_mono (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo hs ht)
        le_rfl)))
  -- the interpolant along the edge
  have hG : ∀ r ∈ Icc s t, 𝒯.globalInterp referenceTriangleVertex baryCoord ũ
      (AffineMap.lineMap A B r) = f s + (f t - f s) * ((r - s) / (t - s)) := by
    intro r hr
    rw [globalInterp_linear_lineMap 𝒯 hst T b c hb hc ũ hr, hfeq (left_mem_Icc.2 hst.le),
      hfeq (right_mem_Icc.2 hst.le), hb, hc]
  -- the arclength integral as an interval integral
  have hcP : ContinuousOn (fun x ↦ (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2)
      (segment ℝ (T.1 b) (T.1 c)) :=
    ((hũc.sub (𝒯.continuousOn_globalInterp referenceTriangleVertex baryCoord
      𝒯.isConformingElement_linear (fun i ↦ (contDiff_baryCoord i).continuous) ũ)).pow 2).mono
      (𝒯.segment_subset_closure T b c)
  rw [hb, hc] at hcP ⊢
  rw [integral_edgeMeasure_lineMap hst hcP]
  have hcongr : ∫ r in s..t, (ũ (AffineMap.lineMap A B r)
      - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ (AffineMap.lineMap A B r)) ^ 2
      = ∫ r in s..t, (f r - (f s + (f t - f s) * ((r - s) / (t - s)))) ^ 2 := by
    refine integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le hst.le] at hr
    rw [hfeq hr, hG r hr]
  rw [hcongr, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine integral_sq_sub_affine_le U (by simpa using hf) (fun r hr r' hr' ↦ ?_) hs hst ht
    (G := fun r ↦ f s + (f t - f s) * ((r - s) / (t - s))) (fun r _ ↦ rfl)
  have := hftc r hr r' hr'
  simpa only [iteratedDeriv_one] using this

/-- If the edge $e = [T_a, T_{a+1}]$ lies on the side $[A, B]$ with $A \ne B$, then it has
parameters $0 \le s < t \le 1$ on the side such that $A + r(B - A)$ lies in the open edge for
$r \in (s, t)$, the edge has length $(t - s)\|B - A\|$, and $\int_e (\tilde u - \Pi_h \tilde
u)^2 \, ds \le h^4 \|B - A\|^{-3} \int_s^t |U''|^2$. -/
private theorem exists_param_integral_sq_sub_globalInterp_le {A B : 𝔼₂} (hAB : A ≠ B) {ũ : 𝔼₂ → ℝ}
    (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (U : SobolevInterval 2 0 1)
    (hU : SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap A B r))
    (T : 𝒯.elems) (a : Fin 3) (h : segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ A B) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
      (∀ r ∈ Ioo s t, AffineMap.lineMap A B r ∈ openSegment ℝ (T.1 a) (T.1 (a + 1))) ∧
      ‖T.1 (a + 1) - T.1 a‖ = (t - s) * ‖B - A‖ ∧
      ∫ x, (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2
          ∂edgeMeasure (T.1 a) (T.1 (a + 1))
        ≤ 𝒯.meshSize ^ 4 * ‖B - A‖⁻¹ ^ 3
          * ∫ r in Ioo s t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 := by
  have hBA : 0 < ‖B - A‖ := norm_pos_iff.2 (sub_ne_zero.2 hAB.symm)
  obtain ⟨s, t, hs, hst, ht, hor⟩ := exists_param_of_segment_subset 𝒯 T a h
  refine ⟨s, t, hs, hst, ht, ?_, ?_, ?_⟩
  · intro r hr
    rcases hor with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · rw [hb, hc]
      exact lineMap_mem_openSegment_of_mem_Ioo hst hr
    · rw [hb, hc, openSegment_symm]
      exact lineMap_mem_openSegment_of_mem_Ioo hst hr
  · rcases hor with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · rw [hb, hc, norm_lineMap_sub_lineMap A B hst.le]
    · rw [hb, hc, norm_sub_rev, norm_lineMap_sub_lineMap A B hst.le]
  · have hlen : (t - s) * ‖B - A‖ ≤ 𝒯.meshSize := by
      rcases hor with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · rw [← norm_lineMap_sub_lineMap A B hst.le, ← hb, ← hc]
        exact norm_vertex_sub_le_meshSize 𝒯 T a (a + 1)
      · rw [← norm_lineMap_sub_lineMap A B hst.le, ← hb, ← hc]
        exact norm_vertex_sub_le_meshSize 𝒯 T (a + 1) a
    have hI : ∫ r in Ioo s t, SobolevInterval.deriv U (Fin.last 2) r ^ 2
        = ∫ r in s..t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 := by
      rw [integral_of_le hst.le, integral_Ioc_eq_integral_Ioo]
    have hI0 : 0 ≤ ∫ r in s..t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 :=
      integral_nonneg hst.le fun r _ ↦ sq_nonneg _
    have hcoef : ‖B - A‖ * (t - s) ^ 4 ≤ 𝒯.meshSize ^ 4 * ‖B - A‖⁻¹ ^ 3 := by
      have h4 : ((t - s) * ‖B - A‖) ^ 4 ≤ 𝒯.meshSize ^ 4 :=
        pow_le_pow_left₀ (mul_nonneg (sub_nonneg.2 hst.le) hBA.le) hlen 4
      have e : ‖B - A‖ * (t - s) ^ 4 = ((t - s) * ‖B - A‖) ^ 4 * ‖B - A‖⁻¹ ^ 3 := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
    rw [hI]
    rcases hor with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact (integral_sq_sub_globalInterp_edge_le 𝒯 hũc U hU hs hst ht T a (a + 1) hb hc).trans
        (mul_le_mul_of_nonneg_right hcoef hI0)
    · rw [edgeMeasure_symm]
      exact (integral_sq_sub_globalInterp_edge_le 𝒯 hũc U hU hs hst ht T (a + 1) a hc hb).trans
        (mul_le_mul_of_nonneg_right hcoef hI0)

/-- Let $(P_k, Q_k)_{k \in \kappa}$ be a finite family of pairs of points of $\mathbb{R}^2$ with
$P_k \ne Q_k$, and suppose that every boundary edge $[T_a, T_{a+1}]$ of $\mathcal{T}$ lies in
some side $[P_k, Q_k]$. Let $\tilde u : \mathbb{R}^2 \to \mathbb{R}$ be continuous on
$\overline\Omega$, and for each $k$ let $U_k \in H^2(0, 1)$ agree almost everywhere on $(0, 1)$
with $r \mapsto \tilde u(P_k + r(Q_k - P_k))$. Then the linear interpolant satisfies
$$\int_{\partial\Omega} (\tilde u - \Pi_h \tilde u)^2 \, ds \le h^4 \sum_k \|Q_k - P_k\|^{-3}
  |U_k|_{H^2(0, 1)}^2,$$
where $h$ is the mesh size and $ds$ is the arclength measure of the boundary edges. This is the
boundary term of the error estimate in Example 11.4.4 of [han2009theoretical].

The measure $ds$ is `Triangulation.boundaryMeasure`, and $|U_k|_{H^2(0, 1)}$ is
`SobolevInterval.seminorm 2 0 1 (Us k)`, the $L^2(0, 1)$ norm of $U_k''$. The proof groups the
boundary edges by the sides. On one side the parameter intervals of the edges are pairwise
disjoint, because their open segments are
(`Triangulation.openSegment_disjoint_of_isBoundaryEdge`), so the estimates of the single edges
add up to the integral over $(0, 1)$. -/
theorem integral_sq_sub_globalInterp_boundaryMeasure_le {κ : Type*} [Fintype κ]
    {P Q : κ → 𝔼₂} (hPQ : ∀ k, P k ≠ Q k)
    (hside : ∀ (T : 𝒯.elems) (a : Fin 3), 𝒯.IsBoundaryEdge T a →
      ∃ k, segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ (P k) (Q k))
    {ũ : 𝔼₂ → ℝ} (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (Us : κ → SobolevInterval 2 0 1)
    (hUs : ∀ k, SobolevInterval.fn (Us k) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap (P k) (Q k) r)) :
    ∫ x, (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2 ∂𝒯.boundaryMeasure
      ≤ 𝒯.meshSize ^ 4
        * ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2 := by
  classical
  choose k hk using hside
  let ke : 𝒯.boundaryEdges → κ := fun e ↦ k e.1.1 e.1.2 (Triangulation.mem_boundaryEdges.1 e.2)
  have hedge := fun e : 𝒯.boundaryEdges ↦
    exists_param_integral_sq_sub_globalInterp_le 𝒯 (hPQ (ke e)) hũc (Us (ke e)) (hUs (ke e))
      e.1.1 e.1.2 (hk e.1.1 e.1.2 (Triangulation.mem_boundaryEdges.1 e.2))
  choose s t hs hst ht hopen _ hbound using hedge
  have hcont2 : ContinuousOn
      (fun x ↦ (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2)
      (closure (Ω : Set 𝔼₂)) :=
    (hũc.sub (𝒯.continuousOn_globalInterp referenceTriangleVertex baryCoord
      𝒯.isConformingElement_linear (fun i ↦ (contDiff_baryCoord i).continuous) ũ)).pow 2
  have hint : ∀ e ∈ 𝒯.boundaryEdges, Integrable
      (fun x ↦ (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2)
      (edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1))) := fun e he ↦
    ((𝒯.boundaryData.memLp_of_continuousOn hcont2 1).integrable le_rfl).mono_measure
      (Triangulation.edgeMeasure_le_boundaryMeasure (Triangulation.mem_boundaryEdges.1 he))
  rw [Triangulation.boundaryMeasure, integral_finsetSum_measure hint, ← Finset.sum_coe_sort]
  refine le_trans (Finset.sum_le_sum fun e _ ↦ hbound e) ?_
  calc ∑ e : 𝒯.boundaryEdges, 𝒯.meshSize ^ 4 * ‖Q (ke e) - P (ke e)‖⁻¹ ^ 3
          * ∫ r in Ioo (s e) (t e), SobolevInterval.deriv (Us (ke e)) (Fin.last 2) r ^ 2
      = ∑ j, ∑ e ∈ Finset.univ.filter (fun e ↦ ke e = j), 𝒯.meshSize ^ 4
          * ‖Q (ke e) - P (ke e)‖⁻¹ ^ 3
          * ∫ r in Ioo (s e) (t e), SobolevInterval.deriv (Us (ke e)) (Fin.last 2) r ^ 2 :=
        (Finset.sum_fiberwise _ ke _).symm
    _ = ∑ j, 𝒯.meshSize ^ 4 * ‖Q j - P j‖⁻¹ ^ 3 * ∑ e ∈ Finset.univ.filter (fun e ↦ ke e = j),
          ∫ r in Ioo (s e) (t e), SobolevInterval.deriv (Us j) (Fin.last 2) r ^ 2 := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e he ↦ ?_
        rw [(Finset.mem_filter.1 he).2]
    _ ≤ ∑ j, 𝒯.meshSize ^ 4 * ‖Q j - P j‖⁻¹ ^ 3
          * ∫ r in Ioo (0 : ℝ) 1, SobolevInterval.deriv (Us j) (Fin.last 2) r ^ 2 := by
        refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine sum_setIntegral_le_setIntegral_of_pairwiseDisjoint _ (fun e _ ↦ measurableSet_Ioo)
          (fun e _ ↦ Ioo_subset_Ioo (hs e) (ht e)) ?_
          ((memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable _)).1 (Lp.memLp _))
          (fun x ↦ sq_nonneg _)
        intro e he e' he' hne
        rw [Finset.mem_coe, Finset.mem_filter] at he he'
        refine Set.disjoint_left.2 fun r hr hr' ↦ ?_
        have h1 := hopen e r hr
        have h2 := hopen e' r hr'
        rw [he.2] at h1
        rw [he'.2] at h2
        exact Set.disjoint_left.1 (Triangulation.openSegment_disjoint_of_isBoundaryEdge
          (Triangulation.mem_boundaryEdges.1 e.2) (Triangulation.mem_boundaryEdges.1 e'.2)
          fun h ↦ hne (Subtype.ext h)) h1 h2
    _ = 𝒯.meshSize ^ 4
          * ∑ j, ‖Q j - P j‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us j) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [SobolevInterval.seminorm_sq_eq_integral zero_le_one, integral_of_le zero_le_one,
          integral_Ioc_eq_integral_Ioo]
        ring

/-- Suppose that the relative interior of every interior edge of $\mathcal{T}$ lies in $\Omega$. Let
$(P_k, Q_k)_{k \in \kappa}$ be a finite family of pairs of points of $\mathbb{R}^2$ with
$P_k \ne Q_k$, and suppose that every boundary edge of $\mathcal{T}$ lies in some side
$[P_k, Q_k]$. Let $\tilde u : \mathbb{R}^2 \to \mathbb{R}$ be continuous on $\overline\Omega$,
and for each $k$ let $U_k \in H^2(0, 1)$ agree almost everywhere on $(0, 1)$ with
$r \mapsto \tilde u(P_k + r(Q_k - P_k))$. Let $w \in H^1(\Omega)$ have the function
$\Pi_h \tilde u - \tilde u$ almost everywhere on $\Omega$. Then the trace $\gamma w$ satisfies
$$\|\gamma w\|_{L^2(\partial\Omega)} \le h^2 \Big( \sum_k \|Q_k - P_k\|^{-3} |U_k|_{H^2(0, 1)}^2
  \Big)^{1/2}.$$
This is the boundary term of the error estimate in Example 11.4.4 of [han2009theoretical],
stated for the trace.

The hypothesis on the interior edges is `Triangulation.InteriorEdgesSubset`, which the trace
family `Triangulation.traceFamily` needs. The trace is the glued trace `Triangulation.traceL` at
$p = 2$, with values in $L^2$ of `Triangulation.boundaryMeasure`. -/
theorem norm_traceL_sub_globalInterp_le (hI : 𝒯.InteriorEdgesSubset) {κ : Type*} [Fintype κ]
    {P Q : κ → 𝔼₂} (hPQ : ∀ k, P k ≠ Q k)
    (hside : ∀ (T : 𝒯.elems) (a : Fin 3), 𝒯.IsBoundaryEdge T a →
      ∃ k, segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ (P k) (Q k))
    {ũ : 𝔼₂ → ℝ} (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (Us : κ → SobolevInterval 2 0 1)
    (hUs : ∀ k, SobolevInterval.fn (Us k) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap (P k) (Q k) r))
    {w : SobolevEuclidean 2 1 2 Ω}
    (hw : fn w =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
      𝒯.globalInterp referenceTriangleVertex baryCoord ũ - ũ) :
    ‖(𝒯.traceFamily hI).traceL 2 ENNReal.ofNat_ne_top w‖
      ≤ 𝒯.meshSize ^ 2
        * Real.sqrt (∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2) := by
  have hcont := 𝒯.continuousOn_globalInterp referenceTriangleVertex baryCoord
    𝒯.isConformingElement_linear (fun j ↦ (contDiff_baryCoord j).continuous) ũ
  have hγ := (𝒯.traceFamily hI).traceL_ae_eq 2 ENNReal.ofNat_ne_top w
    (𝒯.globalInterp referenceTriangleVertex baryCoord ũ - ũ) hw (hcont.sub hũc)
  have hkey := integral_sq_sub_globalInterp_boundaryMeasure_le 𝒯 hPQ hside hũc Us hUs
  have hsq : ‖(𝒯.traceFamily hI).traceL 2 ENNReal.ofNat_ne_top w‖ ^ 2
      ≤ 𝒯.meshSize ^ 4
        * ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_eq_integral_mul]
    refine le_trans (le_of_eq ?_) hkey
    refine integral_congr_ae ?_
    filter_upwards [hγ] with x hx
    rw [hx, Pi.sub_apply]
    ring
  calc ‖(𝒯.traceFamily hI).traceL 2 ENNReal.ofNat_ne_top w‖
      = Real.sqrt (‖(𝒯.traceFamily hI).traceL 2 ENNReal.ofNat_ne_top w‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (𝒯.meshSize ^ 4
          * ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = _ := by
        rw [Real.sqrt_mul (by positivity),
          show 𝒯.meshSize ^ 4 = (𝒯.meshSize ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

end Triangulation
