import Numlib.Analysis.Sobolev.Boundary.PolygonTrace
import Numlib.Approximation.SobolevInterpolation

/-!
# The `L²(∂Ω)` error of the linear interpolant on a polygon

For a triangulation `𝒯` of a polygon `Ω ⊆ ℝ²` whose boundary edges lie on finitely many sides
`[P k, Q k]`, and a function `ũ` continuous on `Ω̄` whose restriction to each side is in
`H²(0, 1)`, the linear (`ℙ₁`) interpolant `Π_h ũ` satisfies

  `∫_{∂Ω} (ũ − Π_h ũ)² ds ≤ h⁴ ∑ₖ ‖Q k − P k‖⁻³ |ũ|²_{H²(side k)}`

(`Triangulation.integral_sq_sub_globalInterp_boundaryMeasure_le`), and the same bound, square
rooted, for the `L²(∂Ω)` norm of the trace of an `H¹(Ω)` element whose function is
`Π_h ũ − ũ` (`Triangulation.norm_traceL_sub_globalInterp_le`).

Along a side the linear interpolant is the one-dimensional affine interpolant of the restriction
of `ũ` at the ends of the edge (`Triangulation.globalInterp_linear_lineMap`), so the panel
estimate `integral_sq_sub_piecewiseLinearInterpCLM_le` of
`Numlib/Approximation/SobolevInterpolation.lean` applies on each boundary edge
(`Triangulation.integral_sq_sub_globalInterp_edge_le`), and the parameter intervals of the edges
of one side are pairwise disjoint (`Triangulation.openSegment_disjoint_of_isBoundaryEdge`), so the
panel estimates add up to the seminorm over the whole side.

## References

[han2009theoretical], Example 11.4.4 (the boundary term of the error estimate for the friction
problem discretized by linear elements on a polygon).
-/

open Filter MeasureTheory Set TopologicalSpace Topology EuclideanSpace SobolevMultiIndex
  intervalIntegral

noncomputable section

/-- `ℝ²`, locally. -/
local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- A finite sum of integrals of a nonnegative function over pairwise disjoint measurable subsets
of `J` is at most the integral over `J`. -/
private theorem sum_setIntegral_le_of_pairwiseDisjoint {ι : Type*} (S : Finset ι) {I : ι → Set ℝ}
    {J : Set ℝ} {F : ℝ → ℝ} (hI : ∀ e ∈ S, MeasurableSet (I e)) (hIJ : ∀ e ∈ S, I e ⊆ J)
    (hdisj : (S : Set ι).PairwiseDisjoint I) (hF : IntegrableOn F J) (hF0 : ∀ x, 0 ≤ F x) :
    ∑ e ∈ S, ∫ x in I e, F x ≤ ∫ x in J, F x := by
  rw [← integral_biUnion_finset S hI hdisj fun e he ↦ hF.mono_set (hIJ e he)]
  exact setIntegral_mono_set hF (Eventually.of_forall hF0)
    (LE.le.eventuallySubset (iUnion₂_subset hIJ))

/-- **The one-panel affine interpolation estimate** on a sub-interval `[s, t] ⊆ [0, 1]` for the
`C¹` representative `f` of an element `U ∈ H²(0, 1)`: `∫_s^t (f − G)² ≤ (t − s)⁴ ∫_s^t |U''|²`
when `G` is the affine interpolant of `f` at `s` and `t`
(`integral_sq_sub_piecewiseLinearInterpCLM_le` with the one-panel partition `{s, t}`). -/
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
  refine integral_sq_sub_piecewiseLinearInterpCLM_le hstep hx0 hx1 hmesh hf
    ((SobolevInterval.intervalIntegrable_deriv zero_le_one U _).mono_set hsub)
    ((SobolevInterval.intervalIntegrable_deriv_sq zero_le_one U _).mono_set hsub)
    (fun r hr r' hr' ↦ hfU r ⟨hs.trans hr.1, hr.2.trans ht⟩ r' ⟨hs.trans hr'.1, hr'.2.trans ht⟩)
    (F := F) (fun r ↦ rfl) (fun r ↦ ?_)
  rw [piecewiseLinearInterpCLM_apply_of_mem hstep F le_rfl (by rw [hx0]; exact r.2.1)
    (by rw [hx1]; exact r.2.2), hG r r.2]
  simp only [F, ContinuousMap.coe_mk, hx0, hx1]

/-- **The arclength integral over a sub-segment of a side**, as an interval integral of the
pulled-back function: `∫ F d(edgeMeasure (A + s(B−A)) (A + t(B−A))) = ‖B − A‖ ∫_s^t F(A + r(B−A))`.
-/
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

/-- The length of an edge of an element is at most the mesh size. -/
theorem norm_vertex_sub_le_meshSize (T : 𝒯.elems) (a b : Fin 3) :
    ‖T.1 b - T.1 a‖ ≤ 𝒯.meshSize := by
  rw [← dist_eq_norm]
  refine (Metric.dist_le_diam_of_mem (𝒯.isCompact_closedK T).isBounded (𝒯.vertex_mem_closedK T b)
    (𝒯.vertex_mem_closedK T a)).trans ?_
  rw [← 𝒯.closure_K, Metric.diam_closure]
  exact 𝒯.diam_le_meshSize T

/-- **A boundary edge on a side, parametrized**: if the edge `[T a, T (a+1)]` lies on the segment
`[A, B]` then its ends are `A + s(B − A)` and `A + t(B − A)` with `0 ≤ s < t ≤ 1`, in one of the
two orientations. -/
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

/-- The open parameter interval of a sub-segment maps into its open segment. -/
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

/-- The length of a sub-segment of a side. -/
private theorem norm_lineMap_sub_lineMap (A B : 𝔼₂) {s t : ℝ} (hst : s ≤ t) :
    ‖AffineMap.lineMap A B t - AffineMap.lineMap A B s‖ = (t - s) * ‖B - A‖ := by
  rw [show AffineMap.lineMap A B t - AffineMap.lineMap A B s = (t - s) • (B - A) by
    simp only [lineMap_eq]; module, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)]

/-- **The linear interpolant along an edge is the affine interpolant of the edge restriction**:
for two vertices `T b = A + s(B − A)`, `T c = A + t(B − A)` of the element `T` on the side
`[A, B]`, `Π_h v (A + r(B − A)) = v(T b) + (v(T c) − v(T b)) (r − s)/(t − s)` for `r ∈ [s, t]`
(`Triangulation.localInterp_lineMap` for the affine barycentric shape functions). -/
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

/-- **The `L²` error of the linear interpolant on a boundary edge lying on a side**: for
`T b = A + s(B − A)`, `T c = A + t(B − A)` and an edge restriction
`r ↦ ũ (A + r(B − A)) ∈ H²(0, 1)` (represented by `U`),
`∫_{[T b, T c]} (ũ − Π_h ũ)² ds ≤ ‖B − A‖ (t − s)⁴ ∫_s^t |U''|²`. -/
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

/-- **The per-edge estimate with the mesh size**: a boundary edge `(T, a)` lying on the side
`[A, B]` has parameters `0 ≤ s < t ≤ 1` on the side, its open parameter interval maps into its
open segment, its length is `(t − s) ‖B − A‖`, and
`∫_e (ũ − Π_h ũ)² ds ≤ h⁴ ‖B − A‖⁻³ ∫_s^t |U''|²` with `h` the mesh size. -/
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

/-- **The `L²(Γ)` error of the linear interpolant on a polygon**: if every boundary edge of `𝒯`
lies on one of the sides `[P k, Q k]` and the restriction of `ũ` to each side is in `H²(0, 1)`
(represented by `Us k`), then

  `∫_Γ (ũ − Π_h ũ)² ds ≤ h⁴ ∑ₖ ‖Q k − P k‖⁻³ |Us k|²_{H²(0,1)}`.

The sum over the boundary edges is grouped by the sides; on one side the parameter intervals of
the edges are pairwise disjoint (their open segments are, by
`Triangulation.openSegment_disjoint_of_isBoundaryEdge`), so the panel estimates add up to the
integral over `(0, 1)`. -/
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
        refine sum_setIntegral_le_of_pairwiseDisjoint _ (fun e _ ↦ measurableSet_Ioo)
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

/-- **The `L²(Γ)` error of the linear interpolant, as the norm of a trace**: for `w ∈ H¹(Ω)` whose
function is `Π_h ũ − ũ`,
`‖γ w‖_{L²(Γ)} ≤ h² √(∑ₖ ‖Q k − P k‖⁻³ |u|²_{H²(Γₖ)})`. -/
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
  have hS0 : 0 ≤ ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2 :=
    Finset.sum_nonneg fun k _ ↦ by positivity
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
