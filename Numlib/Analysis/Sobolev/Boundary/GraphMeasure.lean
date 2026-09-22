import Mathlib.MeasureTheory.Function.Jacobian
import Numlib.Analysis.Calculus.Deriv.Slope
import Numlib.Analysis.Sobolev.Boundary.Data
import Numlib.Analysis.Sobolev.Boundary.Gram
import Numlib.Topology.MetricSpace.Bounded

/-!
# The surface measure and the outward normal of a bounded `C¹` domain

The surface measure `σ` and the outward unit normal `ν` of a bounded `C¹` domain in the graph
form `IsContDiffDomain 1 Ω` of `Numlib/Analysis/Sobolev/Domain.lean` (decisions B2, B3 of
`notes/boundary/planning-brief.md`), built from graph charts and a partition of unity and
characterized chart by chart.

**Local objects.** A graph chart is a rigid motion `T : ℝ^{d+1} ≃ᵃⁱ ℝ^{d+1}` and a `C¹` function
`g : ℝ^d → ℝ` with `Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' epigraph g`. Its parametrization of the
boundary is `graphParam T g x' = T⁻¹ (x', g x')`, defined on the open bounded
`graphDomain T g x₀ r = graphParam T g ⁻¹' B(x₀, r)` and mapping it onto `∂Ω ∩ B(x₀, r)`; the
local surface measure is the pushforward `graphMeasure T g s` of `√(1 + |∇g|²) dx'` on `s ⊆ ℝ^d`
(`graphDensity g`), and the local outward normal is
`graphNormal T g x = T.linear⁻¹ (∇g x', −1) / √(1 + |∇g x'|²)`, `x' = (T x)'` — the sign is the
one pointing *out of* the region above the graph (`(∇g, −1)` is the gradient of
`y ↦ g y' − y_N`, which is negative on `Ω`); Grisvard's `(−∇φ, 1)` (§1.5.1) is for a region
*below* the graph. `graphNormal_outward` proves the sign: `x + tν ∉ Ω` and `x − tν ∈ Ω` for
small `t > 0`.

**Chart independence.** On the overlap of two charts the transition
`ψ = (T₂ ·)' ∘ graphParam T₁ g₁` is a `C¹` injection between open subsets of `ℝ^d` with
`graphParam T₁ g₁ = graphParam T₂ g₂ ∘ ψ`, the densities transform by `|det Dψ|` (the Gram
identity `gram (L ∘ A) = gram L · |det A|` of `Boundary/Gram.lean` with
`graphDensity g x' = gram (D graphParam x')`), and Mathlib's change of variables
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` gives
`graphMeasure T₁ g₁ = graphMeasure T₂ g₂` on the overlap (`graphMeasure_eq_of_eq`). The normals
agree pointwise (`graphNormal_eq_of_eq`): both are unit vectors orthogonal to the common tangent
space, so `ν₂ = ±ν₁` (a direct computation in the frame of the first chart, no dimension count),
and both point outward, which excludes the minus sign.

**Global objects.** A `GraphAtlas Ω` is a finite family of graph charts covering `∂Ω` with a
smooth partition of unity `θ₀ + ∑ θᵢ = 1` subordinate to the balls (`θ₀` vanishing near `∂Ω`, as
in [brezis2011functional] Lemma 9.3); its measure is `∑ᵢ θᵢ · σᵢ` and its normal is `νᵢ` on the
`i`-th ball. The chart characterization `GraphAtlas.measure_restrict_ball` — the atlas measure
restricted to *any* graph chart ball of `Ω` is that chart's `graphMeasure` — makes the measure
independent of the atlas (`GraphAtlas.measure_eq`), and likewise for the normal
(`GraphAtlas.normal_eq_graphNormal_of_inter_eq`). For `hΩ : IsContDiffDomain 1 Ω` bounded, an
atlas exists (`IsContDiffDomain.exists_graphAtlas`, from `IsBoundaryOfClass.exists_finite_cover`
and `IsCompact.exists_contDiff_partitionOfUnity`), and `IsContDiffDomain.boundaryMeasure hΩ hb`,
`IsContDiffDomain.outwardNormal hΩ hb` are the measure and normal of a chosen one. No Hausdorff
measure enters; the identity `σ = μH[d]⌊∂Ω` is a future node (area formula).

## Main definitions

* `EuclideanSpace.graphParam`, `graphDomain`, `graphDensity`, `graphMeasure`, `graphNormal`,
  `graphTransition`: the local objects of a graph chart;
* `GraphAtlas Ω`, `GraphAtlas.measure`, `GraphAtlas.normal`: the glued objects of an atlas;
* `IsContDiffDomain.graphAtlas`, `IsContDiffDomain.boundaryMeasure`,
  `IsContDiffDomain.outwardNormal`: the surface measure and outward normal of a bounded `C¹`
  domain.

## Main statements

* `EuclideanSpace.integral_graphMeasure`: `∫ f dσ_loc = ∫_s √(1 + |∇g|²) f (graphParam x') dx'`;
* `EuclideanSpace.graphNormal_outward`: the normal points out of the region above the graph;
* `EuclideanSpace.graphDensity_graphTransition`: the Gram identity between two charts;
* `EuclideanSpace.graphMeasure_eq_of_eq`, `EuclideanSpace.graphNormal_eq_of_eq`: chart
  independence of the local measure and normal;
* `GraphAtlas.measure_restrict_ball`, `IsContDiffDomain.boundaryMeasure_restrict_ball`: the
  surface measure restricted to any chart ball is the chart's graph measure;
* `IsContDiffDomain.boundaryMeasure_pos_of_isOpen`: `σ` has full support on `∂Ω`;
* `IsContDiffDomain.outwardNormal_eq_graphNormal`: the normal in any chart.

## References

Grisvard, *Elliptic Problems in Nonsmooth Domains*, §1.5.1; [brezis2011functional] §9.2
(Lemma 9.3); Atkinson–Han, Definition 7.2.1.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace Topology

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

namespace EuclideanSpace

/-! ### The graph parametrization -/

variable (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  (g : EuclideanSpace ℝ (Fin d) → ℝ)

/-- **The parametrization of the graph of `g` seen through the rigid motion `T`**:
`graphParam T g x' = T⁻¹ (x', g x')`. It maps `ℝ^d` onto `frontier (T ⁻¹' epigraph g)`, the
boundary of the region above the graph in the frame `T`. -/
def graphParam (x' : 𝔼') : 𝔼 := T.symm (snocLast x' (g x'))

variable {T g}

@[simp]
theorem init_apply_graphParam (x' : 𝔼') : init (T (graphParam T g x')) = x' := by
  simp [graphParam]

@[simp]
theorem apply_graphParam_last (x' : 𝔼') : T (graphParam T g x') (Fin.last d) = g x' := by
  simp [graphParam]

theorem graphParam_injective : Function.Injective (graphParam T g) := fun x y h ↦ by
  have := congrArg (fun z ↦ init (T z)) h
  simpa using this

/-- Every point of the parametrized graph lies on the frontier of the rotated epigraph. -/
theorem graphParam_mem_frontier_epigraph (hg : Continuous g) (x' : 𝔼') :
    graphParam T g x' ∈ frontier (T ⁻¹' epigraph g) := by
  rw [frontier_preimage_epigraph hg]
  simp

/-- A point of the frontier of the rotated epigraph is the parametrization of its first
coordinates: `graphParam T g (init (T x)) = x`. -/
theorem graphParam_eq_of_mem_frontier (hg : Continuous g) {x : 𝔼}
    (hx : x ∈ frontier (T ⁻¹' epigraph g)) : graphParam T g (init (T x)) = x := by
  rw [frontier_preimage_epigraph hg] at hx
  have hx' : T x (Fin.last d) = g (init (T x)) := hx
  rw [graphParam, ← hx', snocLast_init_last, AffineIsometryEquiv.symm_apply_apply]

theorem continuous_graphParam (hg : Continuous g) : Continuous (graphParam T g) := by
  unfold graphParam
  exact T.symm.continuous.comp (continuous_snocLast.comp (continuous_id.prodMk hg))

theorem contDiff_graphParam {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (graphParam T g) := by
  unfold graphParam
  refine (contDiff_affineIsometryEquiv T.symm).comp ?_
  change ContDiff ℝ n fun x' ↦ (lastInitL d).symm (g x', x')
  exact (lastInitL d).symm.contDiff.comp (hg.prodMk contDiff_id)

/-- The graph parametrization is a measurable embedding (continuous and injective on a Polish
space). -/
theorem measurableEmbedding_graphParam (hg : Continuous g) :
    MeasurableEmbedding (graphParam T g) :=
  (continuous_graphParam hg).measurableEmbedding graphParam_injective

/-- **The derivative of the graph parametrization**: if `g` has derivative `ℓ` at `x'`, then
`graphParam T g` has derivative `T.linear⁻¹ ∘L snocLastL ℓ`, `v ↦ T.linear⁻¹ (v, ℓ v)`. -/
theorem hasFDerivAt_graphParam {x' : 𝔼'} {ℓ : 𝔼' →L[ℝ] ℝ} (hg : HasFDerivAt g ℓ x') :
    HasFDerivAt (graphParam T g)
      ((T.linearIsometryEquiv.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) ∘L snocLastL ℓ) x' := by
  have h1 : HasFDerivAt (fun x' : 𝔼' ↦ snocLast x' (g x')) (snocLastL ℓ) x' := by
    change HasFDerivAt (fun x' : 𝔼' ↦ (lastInitL d).symm (g x', x')) _ x'
    exact (lastInitL d).symm.hasFDerivAt.comp x' (hg.prodMk (hasFDerivAt_id x'))
  have h2 := (T.symm.hasFDerivAt (snocLast x' (g x'))).comp x' h1
  rwa [AffineIsometryEquiv.linearIsometryEquiv_symm] at h2

theorem fderiv_graphParam {x' : 𝔼'} (hg : DifferentiableAt ℝ g x') :
    fderiv ℝ (graphParam T g) x'
      = (T.linearIsometryEquiv.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) ∘L
        snocLastL (fderiv ℝ g x') :=
  (hasFDerivAt_graphParam hg.hasFDerivAt).fderiv

/-- The derivative of the graph parametrization is injective (its composite with
`init ∘ T.linear` is the identity). -/
theorem injective_fderiv_graphParam {x' : 𝔼'} (hg : DifferentiableAt ℝ g x') :
    Function.Injective (fderiv ℝ (graphParam T g) x') := by
  rw [fderiv_graphParam hg]
  intro v w h
  have := congrArg (fun z ↦ init (T.linearIsometryEquiv z)) h
  simpa using this

/-! ### The chart domain -/

variable (T g) in
/-- **The parameter domain of a graph chart**: the part `graphParam T g ⁻¹' B(x₀, r)` of `ℝ^d`
that the chart ball sees. -/
def graphDomain (x₀ : 𝔼) (r : ℝ) : Set 𝔼' := graphParam T g ⁻¹' Metric.ball x₀ r

theorem isOpen_graphDomain (hg : Continuous g) (x₀ : 𝔼) (r : ℝ) :
    IsOpen (graphDomain T g x₀ r) :=
  Metric.isOpen_ball.preimage (continuous_graphParam hg)

theorem measurableSet_graphDomain (hg : Continuous g) (x₀ : 𝔼) (r : ℝ) :
    MeasurableSet (graphDomain T g x₀ r) :=
  (isOpen_graphDomain hg x₀ r).measurableSet

/-- The parameter domain is bounded: `‖x'‖ ≤ ‖T (graphParam x')‖ < ‖T x₀‖ + r` on it. -/
theorem isBounded_graphDomain (x₀ : 𝔼) (r : ℝ) : Bornology.IsBounded (graphDomain T g x₀ r) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖T x₀‖ + r, fun x' hx' ↦ ?_⟩
  have h1 : dist (T (graphParam T g x')) (T x₀) < r := by
    rw [T.dist_map]; exact hx'
  calc ‖x'‖ = ‖init (T (graphParam T g x'))‖ := by rw [init_apply_graphParam]
    _ ≤ ‖T (graphParam T g x')‖ := norm_init_le _
    _ ≤ ‖T x₀‖ + ‖T (graphParam T g x') - T x₀‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖T x₀‖ + r := by rw [← dist_eq_norm]; linarith

/-- The parametrization maps the parameter domain onto the part of the rotated graph inside the
ball. -/
theorem graphParam_image_graphDomain (hg : Continuous g) (x₀ : 𝔼) (r : ℝ) :
    graphParam T g '' graphDomain T g x₀ r = frontier (T ⁻¹' epigraph g) ∩ Metric.ball x₀ r := by
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨graphParam_mem_frontier_epigraph hg x', hx'⟩
  · rintro ⟨hx, hxB⟩
    refine ⟨init (T x), ?_, graphParam_eq_of_mem_frontier hg hx⟩
    change graphParam T g (init (T x)) ∈ Metric.ball x₀ r
    rwa [graphParam_eq_of_mem_frontier hg hx]

end EuclideanSpace

/-- **The parametrization of a graph chart of `Ω` covers `∂Ω ∩ B(x₀, r)`**: if
`Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' epigraph g` with `g` continuous, then
`graphParam T g '' graphDomain T g x₀ r = frontier Ω ∩ B(x₀, r)`. -/
theorem IsBoundaryGraphAt.graphParam_image_graphDomain {g : 𝔼' → ℝ} (hg : Continuous g)
    {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {Ω : Set 𝔼} {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    EuclideanSpace.graphParam T g '' EuclideanSpace.graphDomain T g x₀ r
      = frontier Ω ∩ Metric.ball x₀ r := by
  rw [EuclideanSpace.graphParam_image_graphDomain hg, IsBoundaryGraphAt.frontier_inter_ball hg h,
    EuclideanSpace.frontier_preimage_epigraph hg, inter_comm]


namespace EuclideanSpace

variable {T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
  {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### The surface element `√(1 + |∇g|²)` -/

variable (g) in
/-- **The surface element of the graph of `g`**: `graphDensity g x' = √(1 + ‖∇g x'‖²)`, the
density with which the parametrization `graphParam T g` transports Lebesgue measure of `ℝ^d` to
the graph (`graphDensity_eq_gram`: it is the Gram factor of `D graphParam`, for every frame `T`). -/
def graphDensity (x' : 𝔼') : ℝ := Real.sqrt (1 + ‖gradient g x'‖ ^ 2)

theorem one_le_graphDensity (x' : 𝔼') : 1 ≤ graphDensity g x' := by
  rw [graphDensity, Real.le_sqrt zero_le_one (by positivity)]
  nlinarith [sq_nonneg ‖gradient g x'‖]

theorem graphDensity_pos (x' : 𝔼') : 0 < graphDensity g x' :=
  zero_lt_one.trans_le (one_le_graphDensity x')

theorem graphDensity_ne_zero (x' : 𝔼') : graphDensity g x' ≠ 0 :=
  (graphDensity_pos x').ne'

theorem continuous_graphDensity (hg : ContDiff ℝ 1 g) : Continuous (graphDensity g) := by
  have h := continuous_gradient hg
  unfold graphDensity
  fun_prop

/-- **The surface element is intrinsic**: `graphDensity g x' = gram (D (graphParam T g) x')`
for every frame `T`, by `gram_isometry_comp` and `gram_snocLastL`. -/
theorem graphDensity_eq_gram (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {x' : 𝔼'} (hg : DifferentiableAt ℝ g x') :
    graphDensity g x' = gram (fderiv ℝ (graphParam T g) x') := by
  rw [fderiv_graphParam hg, gram_isometry_comp, gram_snocLastL, graphDensity, norm_gradient_eq]

/-! ### The local surface measure -/

variable (T g) in
/-- **The local surface measure of a graph piece**: the pushforward under `graphParam T g` of
`√(1 + |∇g|²) dx'` on `s ⊆ ℝ^d` (decision B2 of `notes/boundary/planning-brief.md`). -/
def graphMeasure (s : Set 𝔼') : Measure 𝔼 :=
  Measure.map (graphParam T g)
    ((volume.restrict s).withDensity fun x' ↦ ENNReal.ofReal (graphDensity g x'))

theorem measurable_ofReal_graphDensity (hg : ContDiff ℝ 1 g) :
    Measurable fun x' ↦ ENNReal.ofReal (graphDensity g x') :=
  ENNReal.measurable_ofReal.comp (continuous_graphDensity hg).measurable

/-- The local surface measure of a measurable set `A` is the weighted Lebesgue measure of its
preimage in the parameter domain. -/
theorem graphMeasure_apply (hg : Continuous g) (s : Set 𝔼') {A : Set 𝔼} (hA : MeasurableSet A) :
    graphMeasure T g s A
      = ∫⁻ x' in s ∩ graphParam T g ⁻¹' A, ENNReal.ofReal (graphDensity g x') := by
  rw [graphMeasure, Measure.map_apply (continuous_graphParam hg).measurable hA,
    withDensity_apply _ (hA.preimage (continuous_graphParam hg).measurable),
    Measure.restrict_restrict (hA.preimage (continuous_graphParam hg).measurable), inter_comm]

/-- Restricting the local surface measure to a measurable set is the local surface measure over
the preimage. -/
theorem graphMeasure_restrict (hg : Continuous g) (s : Set 𝔼') {A : Set 𝔼} (hA : MeasurableSet A) :
    (graphMeasure T g s).restrict A = graphMeasure T g (s ∩ graphParam T g ⁻¹' A) := by
  rw [graphMeasure, graphMeasure, Measure.restrict_map (continuous_graphParam hg).measurable hA,
    restrict_withDensity (hA.preimage (continuous_graphParam hg).measurable),
    Measure.restrict_restrict (hA.preimage (continuous_graphParam hg).measurable), inter_comm]

theorem graphMeasure_restrict_image (hg : Continuous g) (s : Set 𝔼') {t : Set 𝔼'}
    (ht : MeasurableSet t) :
    (graphMeasure T g s).restrict (graphParam T g '' t) = graphMeasure T g (s ∩ t) := by
  rw [graphMeasure_restrict hg s ((measurableEmbedding_graphParam hg).measurableSet_image.2 ht),
    preimage_image_eq _ graphParam_injective]

/-- The local surface measure is carried by the parametrized piece. -/
theorem graphMeasure_compl_image (hg : Continuous g) {s : Set 𝔼'} (hs : MeasurableSet s) :
    graphMeasure T g s (graphParam T g '' s)ᶜ = 0 := by
  rw [graphMeasure_apply hg s ((measurableEmbedding_graphParam hg).measurableSet_image.2 hs).compl,
    preimage_compl, preimage_image_eq _ graphParam_injective, inter_compl_self,
    Measure.restrict_empty, lintegral_zero_measure]

theorem ae_mem_image_graphMeasure (hg : Continuous g) {s : Set 𝔼'} (hs : MeasurableSet s) :
    ∀ᵐ x ∂(graphMeasure T g s), x ∈ graphParam T g '' s :=
  (measure_eq_zero_iff_ae_notMem.1 (graphMeasure_compl_image hg hs)).mono fun _ h ↦ not_not.1 h

theorem graphMeasure_mono_set (hg : Continuous g) {s t : Set 𝔼'} (hst : s ⊆ t) :
    graphMeasure T g s ≤ graphMeasure T g t := by
  refine Measure.map_mono ?_ (continuous_graphParam hg).measurable
  refine Measure.le_iff.2 fun A hA ↦ ?_
  rw [withDensity_apply _ hA, withDensity_apply _ hA]
  exact lintegral_mono' (Measure.restrict_mono le_rfl (Measure.restrict_mono hst le_rfl)) le_rfl

/-- The surface element is integrable over a bounded parameter set. -/
theorem lintegral_ofReal_graphDensity_lt_top (hg : ContDiff ℝ 1 g) {s : Set 𝔼'}
    (hs : Bornology.IsBounded s) :
    ∫⁻ x' in s, ENNReal.ofReal (graphDensity g x') < ⊤ := by
  obtain ⟨C, hC⟩ := hs.isCompact_closure.exists_bound_of_continuousOn
    (continuous_graphDensity hg).continuousOn
  calc ∫⁻ x' in s, ENNReal.ofReal (graphDensity g x')
      ≤ ∫⁻ x' in closure s, ENNReal.ofReal (graphDensity g x') :=
        lintegral_mono_set subset_closure
    _ ≤ ∫⁻ _ in closure s, ENNReal.ofReal C := by
        refine setLIntegral_mono' isClosed_closure.measurableSet fun x' hx' ↦ ?_
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC x' hx'))
    _ = ENNReal.ofReal C * volume (closure s) := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.isCompact_closure.measure_lt_top

/-- The local surface measure over a bounded parameter set is finite. -/
theorem isFiniteMeasure_graphMeasure (hg : ContDiff ℝ 1 g) {s : Set 𝔼'}
    (hs : Bornology.IsBounded s) : IsFiniteMeasure (graphMeasure T g s) := by
  rw [graphMeasure]
  have : IsFiniteMeasure
      ((volume.restrict s).withDensity fun x' ↦ ENNReal.ofReal (graphDensity g x')) :=
    isFiniteMeasure_withDensity (lintegral_ofReal_graphDensity_lt_top hg hs).ne
  infer_instance

/-- **The Lebesgue integral against the local surface measure** is the weighted integral over
the parameter domain. -/
theorem lintegral_graphMeasure (hg : ContDiff ℝ 1 g) (s : Set 𝔼') (f : 𝔼 → ℝ≥0∞) :
    ∫⁻ x, f x ∂(graphMeasure T g s)
      = ∫⁻ x' in s, ENNReal.ofReal (graphDensity g x') * f (graphParam T g x') := by
  rw [graphMeasure, (measurableEmbedding_graphParam hg.continuous).lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_ofReal_graphDensity hg)
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  rfl

/-- **The integral against the local surface measure** is the weighted integral over the
parameter domain: `∫ f dσ_loc = ∫ x' in s, √(1 + |∇g x'|²) • f (graphParam T g x')`. -/
theorem integral_graphMeasure (hg : ContDiff ℝ 1 g) (s : Set 𝔼') {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : AEStronglyMeasurable f (graphMeasure T g s)) :
    ∫ x, f x ∂(graphMeasure T g s)
      = ∫ x' in s, graphDensity g x' • f (graphParam T g x') := by
  rw [graphMeasure, integral_map (continuous_graphParam hg.continuous).aemeasurable hf]
  have hm : Measurable fun x' ↦ (graphDensity g x').toNNReal :=
    (continuous_graphDensity hg).measurable.real_toNNReal
  have h := integral_withDensity_eq_integral_smul (μ := volume.restrict s) hm
    (fun x' ↦ f (graphParam T g x'))
  simp only [ENNReal.ofReal] at h ⊢
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun x' ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (graphDensity_pos x').le]

/-! ### The outward normal of a graph chart -/

variable (T g) in
/-- **The outward unit normal of the region above the graph of `g` in the frame `T`**, at a point
`x` read as lying on the graph:
`graphNormal T g x = T.linear⁻¹ (∇g x', −1) / √(1 + |∇g x'|²)` with `x' = (T x)'` (decision B3
of `notes/boundary/planning-brief.md`). The sign: `Ω` is `{(T x)_N > g ((T x)')}`, the function
`φ(y) = g y' − y_N` is negative on it, and its gradient `(∇g, −1)` points where `φ` grows, that is
out of `Ω` (`graphNormal_outward`). Grisvard's `(−∇φ, 1)` (§1.5.1) is for the region *below* the
graph. -/
def graphNormal (x : 𝔼) : 𝔼 :=
  (graphDensity g (init (T x)))⁻¹ •
    T.linearIsometryEquiv.symm (snocLast (gradient g (init (T x))) (-1))

/-- The normal is a unit vector. -/
theorem norm_graphNormal (x : 𝔼) : ‖graphNormal T g x‖ = 1 := by
  rw [graphNormal, norm_smul, norm_inv, LinearIsometryEquiv.norm_map, norm_snocLast_neg_one,
    Real.norm_eq_abs, abs_of_pos (graphDensity_pos _)]
  exact inv_mul_cancel₀ (graphDensity_ne_zero _)

theorem continuous_graphNormal (hg : ContDiff ℝ 1 g) : Continuous (graphNormal T g) := by
  have h1 := continuous_graphDensity hg
  have h2 := continuous_gradient hg
  have h3 : Continuous (init : 𝔼 → 𝔼') := continuous_init
  have h4 : Continuous T := T.continuous
  have h5 := (continuous_snocLast (d := d))
  have h6 := T.linearIsometryEquiv.symm.continuous
  unfold graphNormal
  refine Continuous.smul (Continuous.inv₀ (h1.comp (h3.comp h4)) fun x ↦ graphDensity_ne_zero _) ?_
  exact h6.comp (h5.comp ((h2.comp (h3.comp h4)).prodMk continuous_const))

/-- The normal depends on `x` only through the first coordinates `(T x)'`. -/
theorem graphNormal_eq_of_init_eq {x y : 𝔼} (h : init (T x) = init (T y)) :
    graphNormal T g x = graphNormal T g y := by
  simp only [graphNormal, h]

/-- **Tangency**: the normal is orthogonal to the range of the derivative of the parametrization,
`⟪T⁻¹(∇g, −1), T⁻¹(v, Dg v)⟫ = ⟪∇g, v⟫ − Dg v = 0`. -/
theorem inner_graphNormal_fderiv_graphParam {x' : 𝔼'} (hg : DifferentiableAt ℝ g x') (v : 𝔼') :
    ⟪graphNormal T g (graphParam T g x'), fderiv ℝ (graphParam T g) x' v⟫_ℝ = 0 := by
  rw [fderiv_graphParam hg, graphNormal, init_apply_graphParam, inner_smul_left]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.inner_map_map,
    snocLastL_apply, inner_snocLast, inner_gradient_eq_fderiv]
  ring

/-- The point `x + t ν` in the frame `T`, for `x = graphParam T g x'` and `ν` the normal at `x`:
its coordinates are `(x' + (t/c) ∇g x', g x' − t/c)` with `c = √(1 + |∇g x'|²)`. -/
theorem apply_graphParam_add_smul_graphNormal (x' : 𝔼') (t : ℝ) :
    T (graphParam T g x' + t • graphNormal T g (graphParam T g x'))
      = snocLast (x' + (t * (graphDensity g x')⁻¹) • gradient g x')
          (g x' - t * (graphDensity g x')⁻¹) := by
  have h1 : ∀ (p w : 𝔼), T (p + w) = T.linearIsometryEquiv w + T p := fun p w ↦ by
    have := T.map_vadd p w
    rwa [vadd_eq_add, vadd_eq_add, add_comm w p] at this
  rw [h1, graphNormal, init_apply_graphParam, map_smul, map_smul,
    LinearIsometryEquiv.apply_symm_apply, graphParam, AffineIsometryEquiv.apply_symm_apply]
  ext i
  induction i using Fin.lastCases
  · simp only [PiLp.add_apply, PiLp.smul_apply, snocLast_apply_last, smul_eq_mul]
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, snocLast_apply_castSucc, smul_eq_mul]
    ring

/-- **The normal points out of the region above the graph**: for `x = graphParam T g x'` on the
graph and all small `t > 0`, `x + t ν ∉ T ⁻¹' epigraph g` and `x − t ν ∈ T ⁻¹' epigraph g`. In
the frame `T` the point `x + tν` lies in the epigraph iff
`h(t) := g (x' + (t/c) ∇g x') − g x' + t/c < 0`, and `h(0) = 0`, `h'(0) = (‖∇g x'‖² + 1)/c > 0`. -/
theorem graphNormal_outward (hg : ContDiff ℝ 1 g) (x' : 𝔼') :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      graphParam T g x' + t • graphNormal T g (graphParam T g x') ∉ T ⁻¹' epigraph g ∧
      graphParam T g x' - t • graphNormal T g (graphParam T g x') ∈ T ⁻¹' epigraph g := by
  set c := graphDensity g x' with hcdef
  set a := gradient g x' with hadef
  have hc : 0 < c := graphDensity_pos x'
  let h : ℝ → ℝ := fun t ↦ g (x' + (t * c⁻¹) • a) - g x' + t * c⁻¹
  have hmem : ∀ t : ℝ, graphParam T g x' + t • graphNormal T g (graphParam T g x')
      ∈ T ⁻¹' epigraph g ↔ h t < 0 := fun t ↦ by
    rw [mem_preimage, apply_graphParam_add_smul_graphNormal, snocLast_mem_epigraph]
    simp only [h]
    constructor <;> intro h <;> linarith
  have hline : HasDerivAt (fun t : ℝ ↦ x' + (t * c⁻¹) • a) (c⁻¹ • a) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const c⁻¹).smul_const a).const_add x'
    simpa using this
  have hg1 : HasDerivAt (fun t : ℝ ↦ g (x' + (t * c⁻¹) • a)) (fderiv ℝ g x' (c⁻¹ • a)) 0 := by
    have hgd : HasFDerivAt g (fderiv ℝ g x') (x' + ((0 : ℝ) * c⁻¹) • a) := by
      simpa using (hg.differentiable one_ne_zero x').hasFDerivAt
    exact hgd.comp_hasDerivAt 0 hline
  have hh : HasDerivAt h (c⁻¹ * ‖a‖ ^ 2 + c⁻¹) 0 := by
    have := (hg1.sub_const (g x')).add ((hasDerivAt_id (0 : ℝ)).mul_const c⁻¹)
    refine this.congr_deriv ?_
    rw [map_smul, smul_eq_mul, ← inner_gradient_eq_fderiv, ← hadef, real_inner_self_eq_norm_sq,
      one_mul]
  have hpos : 0 < c⁻¹ * ‖a‖ ^ 2 + c⁻¹ := by positivity
  have h0 : h 0 = 0 := by simp [h]
  filter_upwards [eventually_pos_and_neg_of_hasDerivAt_pos hh hpos h0] with t ⟨ht1, ht2⟩
  refine ⟨fun hmem' ↦ ?_, ?_⟩
  · rw [hmem] at hmem'
    linarith
  · rw [sub_eq_add_neg, ← neg_smul, hmem]
    exact ht2

end EuclideanSpace


namespace EuclideanSpace

/-! ### The transition between two graph charts -/

variable (T₁ : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  (g₁ : EuclideanSpace ℝ (Fin d) → ℝ)
  (T₂ : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))

/-- **The transition between two graph charts**: `x' ↦ (T₂ (graphParam T₁ g₁ x'))'`, the
parameters of the second chart of the point with parameters `x'` in the first. Where both charts
describe the same set (an open `V` with `V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂`) it
is a `C¹` bijection `graphParam T₁ g₁ ⁻¹' V → graphParam T₂ g₂ ⁻¹' V` with
`graphParam T₂ g₂ ∘ graphTransition = graphParam T₁ g₁` (`graphParam_graphTransition`). -/
def graphTransition (x' : 𝔼') : 𝔼' := init (T₂ (graphParam T₁ g₁ x'))

variable {T₁ g₁ T₂} {g₂ : EuclideanSpace ℝ (Fin d) → ℝ} {V : Set (EuclideanSpace ℝ (Fin (d + 1)))}

theorem contDiff_graphTransition {n : WithTop ℕ∞} (hg₁ : ContDiff ℝ n g₁) :
    ContDiff ℝ n (graphTransition T₁ g₁ T₂) :=
  contDiff_init.comp ((contDiff_affineIsometryEquiv T₂).comp (contDiff_graphParam hg₁))

theorem continuous_graphTransition (hg₁ : Continuous g₁) :
    Continuous (graphTransition T₁ g₁ T₂) :=
  continuous_init.comp (T₂.continuous.comp (continuous_graphParam hg₁))

/-- Two charts describing the same set on an open `V` have the same frontier in `V`. -/
theorem frontier_inter_eq_of_inter_eq (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    frontier (T₁ ⁻¹' epigraph g₁) ∩ V = frontier (T₂ ⁻¹' epigraph g₂) ∩ V := by
  have h1 : frontier (T₁ ⁻¹' epigraph g₁) ∩ V = frontier (V ∩ T₁ ⁻¹' epigraph g₁) ∩ V := by
    rw [inter_comm V, frontier_inter_open_inter hV]
  have h2 : frontier (T₂ ⁻¹' epigraph g₂) ∩ V = frontier (V ∩ T₂ ⁻¹' epigraph g₂) ∩ V := by
    rw [inter_comm V, frontier_inter_open_inter hV]
  rw [h1, h2, hΩ]

/-- **The transition reparametrizes**:
`graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x') = graphParam T₁ g₁ x'` for `x'` in the first
chart's preimage of `V`. -/
theorem graphParam_graphTransition (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {x' : 𝔼'}
    (hx' : x' ∈ graphParam T₁ g₁ ⁻¹' V) :
    graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x') = graphParam T₁ g₁ x' := by
  have h : graphParam T₁ g₁ x' ∈ frontier (T₂ ⁻¹' epigraph g₂) ∩ V := by
    rw [← frontier_inter_eq_of_inter_eq hV hΩ]
    exact ⟨graphParam_mem_frontier_epigraph hg₁ x', hx'⟩
  exact graphParam_eq_of_mem_frontier hg₂ h.1

theorem graphTransition_mapsTo (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    MapsTo (graphTransition T₁ g₁ T₂) (graphParam T₁ g₁ ⁻¹' V) (graphParam T₂ g₂ ⁻¹' V) :=
  fun x' hx' ↦ by
    change graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x') ∈ V
    rw [graphParam_graphTransition hg₁ hg₂ hV hΩ hx']
    exact hx'

theorem graphTransition_injOn (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    InjOn (graphTransition T₁ g₁ T₂) (graphParam T₁ g₁ ⁻¹' V) := fun x' hx' y' hy' h ↦ by
  apply graphParam_injective (T := T₁) (g := g₁)
  rw [← graphParam_graphTransition hg₁ hg₂ hV hΩ hx', h,
    graphParam_graphTransition hg₁ hg₂ hV hΩ hy']

/-- The transition in the other direction is the inverse. -/
theorem graphTransition_graphTransition (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {y' : 𝔼'}
    (hy' : y' ∈ graphParam T₂ g₂ ⁻¹' V) :
    graphTransition T₁ g₁ T₂ (graphTransition T₂ g₂ T₁ y') = y' := by
  rw [graphTransition, graphParam_graphTransition hg₂ hg₁ hV hΩ.symm hy', init_apply_graphParam]

theorem graphTransition_image (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    graphTransition T₁ g₁ T₂ '' (graphParam T₁ g₁ ⁻¹' V) = graphParam T₂ g₂ ⁻¹' V := by
  refine Subset.antisymm (graphTransition_mapsTo hg₁ hg₂ hV hΩ).image_subset fun y' hy' ↦ ?_
  exact ⟨graphTransition T₂ g₂ T₁ y', graphTransition_mapsTo hg₂ hg₁ hV hΩ.symm hy',
    graphTransition_graphTransition hg₁ hg₂ hV hΩ hy'⟩

/-- **The chain rule across the transition**: on the first chart's preimage of `V`,
`D (graphParam T₁ g₁) = D (graphParam T₂ g₂) ∘ D graphTransition`. -/
theorem fderiv_graphParam_comp (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {x' : 𝔼'}
    (hx' : x' ∈ graphParam T₁ g₁ ⁻¹' V) :
    fderiv ℝ (graphParam T₁ g₁) x'
      = fderiv ℝ (graphParam T₂ g₂) (graphTransition T₁ g₁ T₂ x') ∘L
        fderiv ℝ (graphTransition T₁ g₁ T₂) x' := by
  have hD : graphParam T₁ g₁ ⁻¹' V ∈ 𝓝 x' :=
    (hV.preimage (continuous_graphParam hg₁.continuous)).mem_nhds hx'
  have heq : graphParam T₁ g₁ =ᶠ[𝓝 x'] graphParam T₂ g₂ ∘ graphTransition T₁ g₁ T₂ := by
    filter_upwards [hD] with y' hy'
    exact (graphParam_graphTransition hg₁.continuous hg₂.continuous hV hΩ hy').symm
  rw [heq.fderiv_eq]
  exact fderiv_comp x' ((contDiff_graphParam hg₂).differentiable one_ne_zero _)
    ((contDiff_graphTransition hg₁).differentiable one_ne_zero _)

/-- **The Gram identity between two charts** (decision B2 of `notes/boundary/planning-brief.md`):
`graphDensity g₁ x' = graphDensity g₂ (ψ x') · |det Dψ x'|` for the transition `ψ`, on the first
chart's preimage of `V`. -/
theorem graphDensity_graphTransition (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {x' : 𝔼'}
    (hx' : x' ∈ graphParam T₁ g₁ ⁻¹' V) :
    graphDensity g₁ x' = graphDensity g₂ (graphTransition T₁ g₁ T₂ x') *
      |LinearMap.det (fderiv ℝ (graphTransition T₁ g₁ T₂) x' : 𝔼' →ₗ[ℝ] 𝔼')| := by
  rw [graphDensity_eq_gram T₁ (hg₁.differentiable one_ne_zero _),
    graphDensity_eq_gram T₂ (hg₂.differentiable one_ne_zero _),
    fderiv_graphParam_comp hg₁ hg₂ hV hΩ hx', gram_comp]

/-! ### Chart independence of the local measure -/

/-- **Chart independence of the local surface measure**: two `C¹` graph charts describing the
same set on an open `V` induce the same measure on `V`,
`graphMeasure T₁ g₁ (graphParam T₁ g₁ ⁻¹' V) = graphMeasure T₂ g₂ (graphParam T₂ g₂ ⁻¹' V)`. The
change of variables `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` along the
transition and the Gram identity `graphDensity_graphTransition`. -/
theorem graphMeasure_eq_of_eq (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    graphMeasure T₁ g₁ (graphParam T₁ g₁ ⁻¹' V) = graphMeasure T₂ g₂ (graphParam T₂ g₂ ⁻¹' V) := by
  have hc₁ := hg₁.continuous
  have hc₂ := hg₂.continuous
  have hψ := contDiff_graphTransition (T₁ := T₁) (T₂ := T₂) hg₁
  ext A hA
  rw [graphMeasure_apply hc₁ _ hA, graphMeasure_apply hc₂ _ hA]
  set s := graphParam T₁ g₁ ⁻¹' V ∩ graphParam T₁ g₁ ⁻¹' A with hsdef
  have hs : MeasurableSet s :=
    (hV.preimage (continuous_graphParam hc₁)).measurableSet.inter
      (hA.preimage (continuous_graphParam hc₁).measurable)
  have himage : graphParam T₂ g₂ ⁻¹' V ∩ graphParam T₂ g₂ ⁻¹' A
      = graphTransition T₁ g₁ T₂ '' s := by
    ext y'
    constructor
    · rintro ⟨hy'V, hy'A⟩
      refine ⟨graphTransition T₂ g₂ T₁ y', ⟨graphTransition_mapsTo hc₂ hc₁ hV hΩ.symm hy'V, ?_⟩,
        graphTransition_graphTransition hc₁ hc₂ hV hΩ hy'V⟩
      change graphParam T₁ g₁ (graphTransition T₂ g₂ T₁ y') ∈ A
      rwa [graphParam_graphTransition hc₂ hc₁ hV hΩ.symm hy'V]
    · rintro ⟨x', ⟨hx'V, hx'A⟩, rfl⟩
      refine ⟨graphTransition_mapsTo hc₁ hc₂ hV hΩ hx'V, ?_⟩
      change graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x') ∈ A
      rwa [graphParam_graphTransition hc₁ hc₂ hV hΩ hx'V]
  rw [himage, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x' _ ↦ (hψ.differentiable one_ne_zero x').hasFDerivAt.hasFDerivWithinAt)
    ((graphTransition_injOn hc₁ hc₂ hV hΩ).mono inter_subset_left)]
  refine setLIntegral_congr_fun hs fun x' hx' ↦ ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm,
    ← graphDensity_graphTransition hg₁ hg₂ hV hΩ hx'.1]

/-! ### Chart independence of the normal -/

/-- A vector of `ℝ^{d+1}` orthogonal to the graph directions `(v, ⟪a, v⟫)` of a linear form and to
the normal direction `(a, −1)` is zero. -/
theorem eq_zero_of_inner_snocLast_eq_zero {a : 𝔼'} {z : 𝔼}
    (h1 : ∀ v, ⟪z, snocLast v ⟪a, v⟫_ℝ⟫_ℝ = 0) (h2 : ⟪z, snocLast a (-1)⟫_ℝ = 0) : z = 0 := by
  have hz : z = snocLast (init z) (z (Fin.last d)) := (snocLast_init_last z).symm
  set w := init z
  set s := z (Fin.last d)
  rw [hz] at h1 h2
  simp only [inner_snocLast] at h1 h2
  have h3 : w + s • a = 0 := by
    have := h1 (w + s • a)
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial]
      at this ⊢
    linear_combination this
  have h4 : w = -(s • a) := eq_neg_of_add_eq_zero_left h3
  rw [h4, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq] at h2
  simp only [conj_trivial] at h2
  have h5 : s * (‖a‖ ^ 2 + 1) = 0 := by linarith
  have hs : s = 0 := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact h
    · nlinarith [sq_nonneg ‖a‖]
  rw [hz, hs, h4, hs, zero_smul, neg_zero]
  ext i
  induction i using Fin.lastCases <;> simp

/-- **Chart independence of the normal**: two `C¹` graph charts describing the same set on an
open `V` have the same outward normal at every point of the graph inside `V`. Both normals are
unit vectors orthogonal to the tangent space of the first chart
(`inner_graphNormal_fderiv_graphParam`, `fderiv_graphParam_comp`), so `ν₂ = ⟪ν₂, ν₁⟫ ν₁`
(`eq_zero_of_inner_snocLast_eq_zero` in the first frame) with `⟪ν₂, ν₁⟫ = ±1`; the sign `−1`
would put `x + tν₁ = x − tν₂` both inside and outside the set for small `t > 0`
(`graphNormal_outward` for each chart). -/
theorem graphNormal_eq_of_eq (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {x : 𝔼}
    (hx : x ∈ frontier (T₁ ⁻¹' epigraph g₁) ∩ V) :
    graphNormal T₁ g₁ x = graphNormal T₂ g₂ x := by
  have hc₁ := hg₁.continuous
  have hc₂ := hg₂.continuous
  set x₁ := init (T₁ x) with hx₁def
  have hxeq : graphParam T₁ g₁ x₁ = x := graphParam_eq_of_mem_frontier hc₁ hx.1
  have hx₁ : x₁ ∈ graphParam T₁ g₁ ⁻¹' V := by
    change graphParam T₁ g₁ x₁ ∈ V
    rw [hxeq]; exact hx.2
  have hxeq₂ : graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x₁) = x := by
    rw [graphParam_graphTransition hc₁ hc₂ hV hΩ hx₁, hxeq]
  set ν₁ := graphNormal T₁ g₁ x with hν₁
  set ν₂ := graphNormal T₂ g₂ x with hν₂
  -- both normals are orthogonal to the tangent space of chart 1
  have horth₁ : ∀ v, ⟪ν₁, fderiv ℝ (graphParam T₁ g₁) x₁ v⟫_ℝ = 0 := fun v ↦ by
    rw [hν₁, ← hxeq]
    exact inner_graphNormal_fderiv_graphParam (hg₁.differentiable one_ne_zero _) v
  have horth₂ : ∀ v, ⟪ν₂, fderiv ℝ (graphParam T₁ g₁) x₁ v⟫_ℝ = 0 := fun v ↦ by
    rw [hν₂, ← hxeq₂, fderiv_graphParam_comp hg₁ hg₂ hV hΩ hx₁, ContinuousLinearMap.comp_apply]
    exact inner_graphNormal_fderiv_graphParam (hg₂.differentiable one_ne_zero _) _
  -- hence `ν₂ = ⟪ν₂, ν₁⟫ ν₁`
  set c := ⟪ν₂, ν₁⟫_ℝ with hcdef
  have hν₁' : T₁.linearIsometryEquiv.symm (snocLast (gradient g₁ x₁) (-1))
      = graphDensity g₁ x₁ • ν₁ := by
    rw [hν₁, graphNormal, ← hx₁def, smul_smul, mul_inv_cancel₀ (graphDensity_ne_zero _), one_smul]
  have hz : T₁.linearIsometryEquiv (ν₂ - c • ν₁) = 0 := by
    refine eq_zero_of_inner_snocLast_eq_zero (a := gradient g₁ x₁) (fun v ↦ ?_) ?_
    · have hD : fderiv ℝ (graphParam T₁ g₁) x₁ v
          = T₁.linearIsometryEquiv.symm (snocLast v ⟪gradient g₁ x₁, v⟫_ℝ) := by
        rw [fderiv_graphParam (hg₁.differentiable one_ne_zero _), inner_gradient_eq_fderiv]
        rfl
      rw [← LinearIsometryEquiv.inner_map_map T₁.linearIsometryEquiv.symm,
        LinearIsometryEquiv.symm_apply_apply, ← hD, inner_sub_left, inner_smul_left, horth₁,
        horth₂]
      simp
    · rw [← LinearIsometryEquiv.inner_map_map T₁.linearIsometryEquiv.symm,
        LinearIsometryEquiv.symm_apply_apply, hν₁', inner_smul_right, inner_sub_left,
        inner_smul_left, real_inner_self_eq_norm_sq, norm_graphNormal, ← hcdef]
      simp
  have hν₂c : ν₂ = c • ν₁ := by
    have := (LinearIsometryEquiv.map_eq_zero_iff _).1 hz
    exact sub_eq_zero.1 this
  -- `|c| = 1`
  have hc1 : |c| = 1 := by
    have := norm_graphNormal (T := T₂) (g := g₂) x
    rw [← hν₂, hν₂c, norm_smul, norm_graphNormal, mul_one, Real.norm_eq_abs] at this
    exact this
  rcases abs_eq (zero_le_one) |>.1 hc1 with hc | hc
  · rw [hν₂c, hc, one_smul]
  -- the case `c = -1` contradicts the outward orientation of both normals
  exfalso
  have hout₁ := graphNormal_outward (T := T₁) hg₁ x₁
  have hout₂ := graphNormal_outward (T := T₂) hg₂ (graphTransition T₁ g₁ T₂ x₁)
  rw [hxeq] at hout₁
  rw [hxeq₂] at hout₂
  have hV' : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • ν₁ ∈ V := by
    have ht : Tendsto (fun t : ℝ ↦ x + t • ν₁) (𝓝[>] 0) (𝓝 x) := by
      have : Tendsto (fun t : ℝ ↦ x + t • ν₁) (𝓝 0) (𝓝 (x + (0 : ℝ) • ν₁)) :=
        tendsto_const_nhds.add (tendsto_id.smul_const ν₁)
      rw [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact ht.eventually (hV.mem_nhds hx.2)
  obtain ⟨t, ⟨h1, _⟩, ⟨_, h2⟩, h3⟩ := (hout₁.and (hout₂.and hV')).exists
  apply h1
  have h4 : x - t • ν₂ = x + t • ν₁ := by
    rw [hν₂c, hc, neg_one_smul, smul_neg, sub_neg_eq_add]
  rw [h4] at h2
  have h5 : x + t • ν₁ ∈ V ∩ T₂ ⁻¹' epigraph g₂ := ⟨h3, h2⟩
  rw [← hΩ] at h5
  exact h5.2

end EuclideanSpace


/-! ### Atlases: finitely many graph charts with a partition of unity -/

/-- **A finite graph atlas of `Ω ⊆ ℝ^{d+1}` with a subordinate partition of unity** — the data
from which the surface measure and the outward normal are built: `k` balls `B(x i, r i)` covering
`∂Ω`, in each of which `Ω` is the region above the graph of a `C¹` function `g i` in the frame
`T i`, and smooth `θ₀, θ i` with values in `[0, 1]`, `θ₀ + ∑ i, θ i = 1`, each `θ i` compactly
supported in its ball and `θ₀` vanishing on a neighbourhood of `∂Ω` (the partition of unity of
[brezis2011functional] Lemma 9.3; `θ₀` is what the assembly of the divergence theorem needs, so
that `θ₀ F` has compact support inside `Ω`). -/
structure GraphAtlas (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) where
  /-- The number of charts. -/
  k : ℕ
  /-- The centres of the chart balls. -/
  x : Fin k → EuclideanSpace ℝ (Fin (d + 1))
  /-- The radii of the chart balls. -/
  r : Fin k → ℝ
  /-- The rigid motions of the charts. -/
  T : Fin k → (EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  /-- The graph functions of the charts. -/
  g : Fin k → (EuclideanSpace ℝ (Fin d) → ℝ)
  /-- The interior piece of the partition of unity. -/
  θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ
  /-- The pieces of the partition of unity subordinate to the balls. -/
  θ : Fin k → EuclideanSpace ℝ (Fin (d + 1)) → ℝ
  x_mem_frontier : ∀ i, x i ∈ frontier Ω
  r_pos : ∀ i, 0 < r i
  contDiff_g : ∀ i, ContDiff ℝ 1 (g i)
  inter_ball_eq : ∀ i, Ω ∩ Metric.ball (x i) (r i)
    = Metric.ball (x i) (r i) ∩ T i ⁻¹' EuclideanSpace.epigraph (g i)
  frontier_subset : frontier Ω ⊆ ⋃ i, Metric.ball (x i) (r i)
  contDiff_θ₀ : ContDiff ℝ ∞ θ₀
  contDiff_θ : ∀ i, ContDiff ℝ ∞ (θ i)
  θ₀_mem_Icc : ∀ y, θ₀ y ∈ Icc (0 : ℝ) 1
  θ_mem_Icc : ∀ i y, θ i y ∈ Icc (0 : ℝ) 1
  θ₀_add_sum_θ : ∀ y, θ₀ y + ∑ i, θ i y = 1
  hasCompactSupport_θ : ∀ i, HasCompactSupport (θ i)
  tsupport_θ_subset : ∀ i, tsupport (θ i) ⊆ Metric.ball (x i) (r i)
  disjoint_tsupport_θ₀ : Disjoint (tsupport θ₀) (frontier Ω)

namespace GraphAtlas

variable {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} (a : GraphAtlas Ω)

theorem θ₀_eq_zero {y : 𝔼} (hy : y ∈ frontier Ω) : a.θ₀ y = 0 :=
  image_eq_zero_of_notMem_tsupport (disjoint_right.1 a.disjoint_tsupport_θ₀ hy)

/-- On `∂Ω` the pieces subordinate to the balls sum to one. -/
theorem sum_θ {y : 𝔼} (hy : y ∈ frontier Ω) : ∑ i, a.θ i y = 1 := by
  have := a.θ₀_add_sum_θ y
  rwa [a.θ₀_eq_zero hy, zero_add] at this

theorem θ_eq_zero (i : Fin a.k) {y : 𝔼} (hy : y ∉ Metric.ball (a.x i) (a.r i)) : a.θ i y = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hy (a.tsupport_θ_subset i h)

theorem θ_nonneg (i : Fin a.k) (y : 𝔼) : 0 ≤ a.θ i y := (a.θ_mem_Icc i y).1

theorem θ_le_one (i : Fin a.k) (y : 𝔼) : a.θ i y ≤ 1 := (a.θ_mem_Icc i y).2

theorem measurable_ofReal_θ (i : Fin a.k) : Measurable fun y ↦ ENNReal.ofReal (a.θ i y) :=
  ENNReal.measurable_ofReal.comp (a.contDiff_θ i).continuous.measurable

theorem exists_mem_ball {y : 𝔼} (hy : y ∈ frontier Ω) : ∃ i, y ∈ Metric.ball (a.x i) (a.r i) :=
  mem_iUnion.1 (a.frontier_subset hy)

/-- The boundary of a set with an atlas is compact (closed and covered by finitely many balls). -/
theorem isCompact_frontier (a : GraphAtlas Ω) : IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    ((Bornology.isBounded_iUnion.2 fun _ ↦ Metric.isBounded_ball).subset a.frontier_subset)

/-- The parameter domain of the `i`-th chart. -/
def graphDomain (i : Fin a.k) : Set 𝔼' :=
  EuclideanSpace.graphDomain (a.T i) (a.g i) (a.x i) (a.r i)

theorem graphDomain_eq (i : Fin a.k) :
    a.graphDomain i = EuclideanSpace.graphParam (a.T i) (a.g i) ⁻¹' Metric.ball (a.x i) (a.r i) :=
  rfl

/-- The local surface measure of the `i`-th chart, over its parameter domain. -/
def localMeasure (i : Fin a.k) : Measure 𝔼 :=
  EuclideanSpace.graphMeasure (a.T i) (a.g i) (a.graphDomain i)

theorem localMeasure_eq (i : Fin a.k) :
    a.localMeasure i = EuclideanSpace.graphMeasure (a.T i) (a.g i) (a.graphDomain i) :=
  rfl

/-- **The surface measure of the atlas**: the local graph measures glued by the partition of
unity, `∑ i, θ i · σ i`. -/
def measure : Measure 𝔼 :=
  ∑ i, (a.localMeasure i).withDensity fun y ↦ ENNReal.ofReal (a.θ i y)

theorem measure_eq_sum :
    a.measure = ∑ i, (a.localMeasure i).withDensity fun y ↦ ENNReal.ofReal (a.θ i y) :=
  rfl

/-- The `i`-th local measure is carried by `∂Ω ∩ B(x i, r i)`. -/
theorem localMeasure_compl_frontier (i : Fin a.k) : a.localMeasure i (frontier Ω)ᶜ = 0 := by
  refine measure_mono_null (compl_subset_compl.2 ?_)
    (EuclideanSpace.graphMeasure_compl_image (a.contDiff_g i).continuous
      (EuclideanSpace.measurableSet_graphDomain (a.contDiff_g i).continuous _ _))
  rw [graphDomain, IsBoundaryGraphAt.graphParam_image_graphDomain (a.contDiff_g i).continuous
    (a.inter_ball_eq i)]
  exact inter_subset_left

instance isFiniteMeasure_localMeasure (i : Fin a.k) : IsFiniteMeasure (a.localMeasure i) :=
  EuclideanSpace.isFiniteMeasure_graphMeasure (a.contDiff_g i)
    (EuclideanSpace.isBounded_graphDomain _ _)

instance isFiniteMeasure_measure : IsFiniteMeasure a.measure := by
  unfold measure
  have : ∀ i : Fin a.k, IsFiniteMeasure ((a.localMeasure i).withDensity
      fun y ↦ ENNReal.ofReal (a.θ i y)) := fun i ↦ by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ y, ENNReal.ofReal (a.θ i y) ∂(a.localMeasure i)
        ≤ ∫⁻ _, 1 ∂(a.localMeasure i) :=
          lintegral_mono fun y ↦ by
            simpa using ENNReal.ofReal_le_ofReal (a.θ_le_one i y)
      _ < ⊤ := by simp [measure_lt_top]
  infer_instance

/-- The surface measure of the atlas is carried by `∂Ω`. -/
theorem measure_compl_frontier : a.measure (frontier Ω)ᶜ = 0 := by
  rw [measure, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  exact withDensity_absolutelyContinuous _ _ (a.localMeasure_compl_frontier i)

theorem ae_mem_frontier : ∀ᵐ y ∂a.measure, y ∈ frontier Ω :=
  (measure_eq_zero_iff_ae_notMem.1 a.measure_compl_frontier).mono fun _ h ↦ not_not.1 h

/-- A function continuous on `∂Ω` is integrable for the surface measure of the atlas. -/
theorem integrable_of_continuousOn {G : Type*} [NormedAddCommGroup G] {f : 𝔼 → G}
    (hf : ContinuousOn f (frontier Ω)) : Integrable f a.measure := by
  have := hf.integrableOn_compact (μ := a.measure) a.isCompact_frontier
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem a.ae_mem_frontier] at this

theorem withDensity_localMeasure_le (i : Fin a.k) :
    (a.localMeasure i).withDensity (fun y ↦ ENNReal.ofReal (a.θ i y)) ≤ a.measure :=
  Finset.single_le_sum (f := fun j ↦ (a.localMeasure j).withDensity
    fun y ↦ ENNReal.ofReal (a.θ j y)) (fun _ _ ↦ bot_le) (Finset.mem_univ i)

/-- The integral against the atlas measure is the sum over the charts of the integrals against
the local measures weighted by the partition of unity. -/
theorem integral_measure_eq_sum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : Integrable f a.measure) :
    ∫ y, f y ∂a.measure = ∑ i, ∫ y, a.θ i y • f y ∂(a.localMeasure i) := by
  rw [measure,
    integral_finsetSum_measure fun i _ ↦ hf.mono_measure (a.withDensity_localMeasure_le i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hm : Measurable fun y ↦ (a.θ i y).toNNReal :=
    (a.contDiff_θ i).continuous.measurable.real_toNNReal
  have h1 := integral_withDensity_eq_integral_smul (μ := a.localMeasure i) hm f
  simp only [ENNReal.ofReal] at h1 ⊢
  rw [h1]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (a.θ_nonneg i _)]

/-- **The integral against the atlas measure, in the parameters of the charts**:
`∫ f dσ = ∑ i, ∫ x' in Dᵢ, √(1 + |∇gᵢ|²) θᵢ(Φᵢ x') • f (Φᵢ x')`. -/
theorem integral_measure {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : Integrable f a.measure) :
    ∫ y, f y ∂a.measure = ∑ i, ∫ x' in a.graphDomain i,
      (EuclideanSpace.graphDensity (a.g i) x' *
        a.θ i (EuclideanSpace.graphParam (a.T i) (a.g i) x')) •
          f (EuclideanSpace.graphParam (a.T i) (a.g i) x') := by
  rw [a.integral_measure_eq_sum hf]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hm : Measurable fun y ↦ (a.θ i y).toNNReal :=
    (a.contDiff_θ i).continuous.measurable.real_toNNReal
  have h2 : AEStronglyMeasurable (fun y ↦ a.θ i y • f y) (a.localMeasure i) := by
    have := (hf.mono_measure (a.withDensity_localMeasure_le i)).aestronglyMeasurable
    simp only [ENNReal.ofReal] at this
    have h3 := (aestronglyMeasurable_withDensity_iff hm).1 this
    simpa only [NNReal.smul_def, Real.coe_toNNReal _ (a.θ_nonneg i _)] using h3
  rw [localMeasure, EuclideanSpace.integral_graphMeasure (a.contDiff_g i) _ h2]
  refine setIntegral_congr_fun (EuclideanSpace.measurableSet_graphDomain (a.contDiff_g i).continuous
    _ _) fun x' _ ↦ ?_
  simp only [smul_smul]

/-- **The partition of unity glues a measure carried by `∂Ω` back to itself**:
`∑ i, θ i · μ⌊B(x i, r i) = μ` whenever `μ (∂Ω)ᶜ = 0`. This is the mechanism behind the chart
characterization of the atlas measure and its independence of the atlas. -/
theorem sum_withDensity_restrict_eq {μ : Measure 𝔼} (hμ : μ (frontier Ω)ᶜ = 0) :
    ∑ i, (μ.restrict (Metric.ball (a.x i) (a.r i))).withDensity (fun y ↦ ENNReal.ofReal (a.θ i y))
      = μ := by
  have h1 : ∀ i, (μ.restrict (Metric.ball (a.x i) (a.r i))).withDensity
      (fun y ↦ ENNReal.ofReal (a.θ i y)) = μ.withDensity fun y ↦ ENNReal.ofReal (a.θ i y) := by
    intro i
    rw [← restrict_withDensity measurableSet_ball]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have h0 : (μ.withDensity fun y ↦ ENNReal.ofReal (a.θ i y)) (Metric.ball (a.x i) (a.r i))ᶜ
        = 0 := by
      rw [withDensity_apply _ measurableSet_ball.compl]
      exact setLIntegral_eq_zero measurableSet_ball.compl fun y hy ↦ by simp [a.θ_eq_zero i hy]
    exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun _ h ↦ not_not.1 h
  simp_rw [h1]
  have h2 : (∑ i, μ.withDensity fun y ↦ ENNReal.ofReal (a.θ i y))
      = μ.withDensity fun y ↦ ∑ i, ENNReal.ofReal (a.θ i y) := by
    ext A hA
    rw [Measure.finsetSum_apply, withDensity_apply _ hA,
      lintegral_finsetSum _ fun i _ ↦ a.measurable_ofReal_θ i]
    exact Finset.sum_congr rfl fun i _ ↦ withDensity_apply _ hA
  rw [h2]
  have h3 : (fun y ↦ ∑ i, ENNReal.ofReal (a.θ i y)) =ᵐ[μ] 1 := by
    have hμ' : ∀ᵐ y ∂μ, y ∈ frontier Ω :=
      (measure_eq_zero_iff_ae_notMem.1 hμ).mono fun _ h ↦ not_not.1 h
    filter_upwards [hμ'] with y hy
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ a.θ_nonneg i y, a.sum_θ hy]
    simp
  rw [withDensity_congr_ae h3, withDensity_one]

/-- **The chart characterization of the atlas measure**: restricted to the ball of *any* `C¹`
graph chart `(T, g)` of `Ω` at `(x₀, r)`, the atlas measure is that chart's graph measure. Each
local measure restricted to `B(x₀, r)` is the chart's measure restricted to the local ball
(`graphMeasure_eq_of_eq` on the intersection of the balls), and the partition of unity glues
(`sum_withDensity_restrict_eq`). -/
theorem measure_restrict_ball {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g) {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    a.measure.restrict (Metric.ball x₀ r)
      = EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r) := by
  set ν := EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r) with hνdef
  have hν : ν (frontier Ω)ᶜ = 0 := by
    refine measure_mono_null (compl_subset_compl.2 ?_)
      (EuclideanSpace.graphMeasure_compl_image hg.continuous
        (EuclideanSpace.measurableSet_graphDomain hg.continuous _ _))
    rw [IsBoundaryGraphAt.graphParam_image_graphDomain hg.continuous h]
    exact inter_subset_left
  have hkey : ∀ i, (a.localMeasure i).restrict (Metric.ball x₀ r)
      = ν.restrict (Metric.ball (a.x i) (a.r i)) := by
    intro i
    rw [localMeasure, hνdef,
      EuclideanSpace.graphMeasure_restrict (a.contDiff_g i).continuous _ measurableSet_ball,
      EuclideanSpace.graphMeasure_restrict hg.continuous _ measurableSet_ball,
      graphDomain_eq, EuclideanSpace.graphDomain, ← preimage_inter, ← preimage_inter,
      inter_comm (Metric.ball x₀ r)]
    exact EuclideanSpace.graphMeasure_eq_of_eq (a.contDiff_g i) hg
      (Metric.isOpen_ball.inter Metric.isOpen_ball)
      (EuclideanSpace.inter_inter_preimage_epigraph_eq (a.inter_ball_eq i) h)
  calc a.measure.restrict (Metric.ball x₀ r)
      = ∑ i, ((a.localMeasure i).withDensity fun y ↦ ENNReal.ofReal (a.θ i y)).restrict
          (Metric.ball x₀ r) := by
        rw [measure]
        ext A hA
        simp only [Measure.restrict_apply hA, Measure.finsetSum_apply]
    _ = ∑ i, ((a.localMeasure i).restrict (Metric.ball x₀ r)).withDensity
          fun y ↦ ENNReal.ofReal (a.θ i y) := by
        simp_rw [restrict_withDensity measurableSet_ball]
    _ = ∑ i, (ν.restrict (Metric.ball (a.x i) (a.r i))).withDensity
          fun y ↦ ENNReal.ofReal (a.θ i y) := by
        simp_rw [hkey]
    _ = ν := a.sum_withDensity_restrict_eq hν

/-- **A measure carried by `∂Ω` that agrees with the chart measures on the atlas balls is the
atlas measure.** -/
theorem measure_eq_of_forall_restrict_ball {μ : Measure 𝔼} (hμ : μ (frontier Ω)ᶜ = 0)
    (h : ∀ i, μ.restrict (Metric.ball (a.x i) (a.r i)) = a.localMeasure i) : μ = a.measure := by
  rw [measure_eq_sum]
  simp_rw [← h]
  exact (a.sum_withDensity_restrict_eq hμ).symm

/-- **The atlas measure does not depend on the atlas.** -/
theorem measure_eq (a a' : GraphAtlas Ω) : a.measure = a'.measure :=
  a'.measure_eq_of_forall_restrict_ball a.measure_compl_frontier fun i ↦
    a.measure_restrict_ball (a'.contDiff_g i) (a'.inter_ball_eq i)

/-! ### The normal of an atlas -/

open Classical in
/-- **The outward normal of the atlas**: on each chart ball the chart's `graphNormal`, and `0` off
the atlas. -/
def normal (y : 𝔼) : 𝔼 :=
  if h : ∃ i, y ∈ Metric.ball (a.x i) (a.r i) then
    EuclideanSpace.graphNormal (a.T (Classical.choose h)) (a.g (Classical.choose h)) y
  else 0

/-- On `∂Ω ∩ B(x i, r i)` the atlas normal is the `i`-th chart's normal, whichever chart the
definition picked (`graphNormal_eq_of_eq`). -/
theorem normal_eq_graphNormal {y : 𝔼} (hy : y ∈ frontier Ω) {i : Fin a.k}
    (hi : y ∈ Metric.ball (a.x i) (a.r i)) :
    a.normal y = EuclideanSpace.graphNormal (a.T i) (a.g i) y := by
  have h : ∃ i, y ∈ Metric.ball (a.x i) (a.r i) := ⟨i, hi⟩
  rw [normal, dite_eq_left h]
  set j := Classical.choose h
  have hj : y ∈ Metric.ball (a.x j) (a.r j) := Classical.choose_spec h
  refine EuclideanSpace.graphNormal_eq_of_eq (a.contDiff_g j) (a.contDiff_g i)
    (Metric.isOpen_ball.inter Metric.isOpen_ball)
    (EuclideanSpace.inter_inter_preimage_epigraph_eq (a.inter_ball_eq j) (a.inter_ball_eq i))
    ⟨?_, hj, hi⟩
  exact EuclideanSpace.mem_frontier_preimage_epigraph_of_mem_frontier (a.contDiff_g j).continuous
    (a.inter_ball_eq j) hy hj

/-- **The chart characterization of the atlas normal**: at a boundary point inside the ball of
*any* `C¹` graph chart of `Ω`, the atlas normal is that chart's normal. -/
theorem normal_eq_graphNormal_of_inter_eq {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g)
    {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    {y : 𝔼} (hy : y ∈ frontier Ω) (hyB : y ∈ Metric.ball x₀ r) :
    a.normal y = EuclideanSpace.graphNormal T g y := by
  obtain ⟨i, hi⟩ := a.exists_mem_ball hy
  rw [a.normal_eq_graphNormal hy hi]
  refine EuclideanSpace.graphNormal_eq_of_eq (a.contDiff_g i) hg
    (Metric.isOpen_ball.inter Metric.isOpen_ball)
    (EuclideanSpace.inter_inter_preimage_epigraph_eq (a.inter_ball_eq i) h) ⟨?_, hi, hyB⟩
  exact EuclideanSpace.mem_frontier_preimage_epigraph_of_mem_frontier (a.contDiff_g i).continuous
    (a.inter_ball_eq i) hy hi

/-- **The atlas normal does not depend on the atlas** on `∂Ω`. -/
theorem normal_eq_of_mem_frontier (a a' : GraphAtlas Ω) {y : 𝔼} (hy : y ∈ frontier Ω) :
    a.normal y = a'.normal y := by
  obtain ⟨i, hi⟩ := a'.exists_mem_ball hy
  rw [a'.normal_eq_graphNormal hy hi]
  exact a.normal_eq_graphNormal_of_inter_eq (a'.contDiff_g i) (a'.inter_ball_eq i) hy hi

theorem norm_normal {y : 𝔼} (hy : y ∈ frontier Ω) : ‖a.normal y‖ = 1 := by
  obtain ⟨i, hi⟩ := a.exists_mem_ball hy
  rw [a.normal_eq_graphNormal hy hi, EuclideanSpace.norm_graphNormal]

/-- The atlas normal is continuous on `∂Ω` (locally it is a chart normal). -/
theorem continuousOn_normal : ContinuousOn a.normal (frontier Ω) := by
  intro y hy
  obtain ⟨i, hi⟩ := a.exists_mem_ball hy
  refine (EuclideanSpace.continuous_graphNormal
    (a.contDiff_g i)).continuousWithinAt.congr_of_eventuallyEq ?_ (a.normal_eq_graphNormal hy hi)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.isOpen_ball.mem_nhds hi),
    eventually_mem_nhdsWithin] with z hz1 hz2
  exact a.normal_eq_graphNormal hz2 hz1

theorem ae_norm_normal : ∀ᵐ y ∂a.measure, ‖a.normal y‖ = 1 :=
  a.ae_mem_frontier.mono fun _ hy ↦ a.norm_normal hy

theorem aestronglyMeasurable_normal : AEStronglyMeasurable a.normal a.measure := by
  have := a.continuousOn_normal.aestronglyMeasurable (μ := a.measure)
    isClosed_frontier.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem a.ae_mem_frontier] at this

end GraphAtlas

/-! ### The surface measure and the outward normal of a bounded `C¹` domain -/

namespace IsContDiffDomain

variable {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **A bounded `C¹` domain has a graph atlas**: the finite cover of
`IsBoundaryOfClass.exists_finite_cover` with the partition of unity of
`IsCompact.exists_contDiff_partitionOfUnity` on the compact `∂Ω`. -/
theorem exists_graphAtlas (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω) :
    Nonempty (GraphAtlas Ω) := by
  obtain ⟨s, hs, hcov⟩ := hΩ.isBoundaryOfClass.exists_finite_cover hb
  let e := s.equivFin
  have hq : ∀ i : Fin s.card, ∃ (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) (g : 𝔼' → ℝ), ContDiff ℝ 1 g ∧
      Ω ∩ Metric.ball (e.symm i).1.1 (e.symm i).1.2
        = Metric.ball (e.symm i).1.1 (e.symm i).1.2 ∩ T ⁻¹' EuclideanSpace.epigraph g :=
    fun i ↦ (hs _ (e.symm i).2).2.2
  choose T g hg hTg using hq
  have hcov' : frontier Ω ⊆ ⋃ i : Fin s.card, Metric.ball (e.symm i).1.1 (e.symm i).1.2 := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.1 (hcov hy)
    refine mem_iUnion.2 ⟨e ⟨q, hq⟩, ?_⟩
    simpa using hyq
  have hK : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hb.closure.subset frontier_subset_closure)
  obtain ⟨θ₀, θ, hθ₀, hθ, hθ₀I, hθI, hsum, hθc, hθs, hθ₀d⟩ :=
    hK.exists_contDiff_partitionOfUnity (fun i ↦ Metric.isOpen_ball) hcov'
  refine ⟨{ k := s.card
            x := fun i ↦ (e.symm i).1.1
            r := fun i ↦ (e.symm i).1.2
            T := T
            g := g
            θ₀ := θ₀
            θ := θ
            x_mem_frontier := fun i ↦ (hs _ (e.symm i).2).1
            r_pos := fun i ↦ (hs _ (e.symm i).2).2.1
            contDiff_g := hg
            inter_ball_eq := hTg
            frontier_subset := hcov'
            contDiff_θ₀ := hθ₀
            contDiff_θ := hθ
            θ₀_mem_Icc := hθ₀I
            θ_mem_Icc := hθI
            θ₀_add_sum_θ := hsum
            hasCompactSupport_θ := hθc
            tsupport_θ_subset := hθs
            disjoint_tsupport_θ₀ := hθ₀d }⟩

/-- **The chosen graph atlas** of a bounded `C¹` domain. Everything defined from it is
characterized chart-independently (`boundaryMeasure_restrict_ball`,
`outwardNormal_eq_graphNormal`), so the choice never leaks. -/
def graphAtlas (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω) : GraphAtlas Ω :=
  Classical.choice (hΩ.exists_graphAtlas hb)

/-- **The surface measure of a bounded `C¹` domain**: the measure of the chosen atlas,
`∑ i, θ i · σ i` (decision B2 of `notes/boundary/planning-brief.md`); by `GraphAtlas.measure_eq`
it is the measure of every atlas, and by `boundaryMeasure_restrict_ball` it is, on every chart
ball, the pushforward of `√(1 + |∇g|²) dx'` under the chart's parametrization. -/
def boundaryMeasure (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω) : Measure 𝔼 :=
  (hΩ.graphAtlas hb).measure

/-- **The outward unit normal of a bounded `C¹` domain**, as a function on the ambient space: on
each chart ball of the chosen atlas the chart's `graphNormal`, and `0` off the atlas (decision
B3 of `notes/boundary/planning-brief.md`); by `outwardNormal_eq_graphNormal` it is the normal of
every chart at every boundary point. -/
def outwardNormal (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω) : 𝔼 → 𝔼 :=
  (hΩ.graphAtlas hb).normal

variable (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω)

theorem boundaryMeasure_eq_graphAtlas_measure :
    hΩ.boundaryMeasure hb = (hΩ.graphAtlas hb).measure :=
  rfl

/-- The surface measure is the measure of every graph atlas of `Ω`. -/
theorem boundaryMeasure_eq_measure (a : GraphAtlas Ω) : hΩ.boundaryMeasure hb = a.measure :=
  GraphAtlas.measure_eq _ a

theorem outwardNormal_eq_graphAtlas_normal : hΩ.outwardNormal hb = (hΩ.graphAtlas hb).normal :=
  rfl

instance isFiniteMeasure_boundaryMeasure : IsFiniteMeasure (hΩ.boundaryMeasure hb) :=
  GraphAtlas.isFiniteMeasure_measure _

/-- The surface measure is carried by `∂Ω`. -/
theorem boundaryMeasure_compl_frontier : hΩ.boundaryMeasure hb (frontier Ω)ᶜ = 0 :=
  GraphAtlas.measure_compl_frontier _

theorem ae_mem_frontier_boundaryMeasure : ∀ᵐ y ∂(hΩ.boundaryMeasure hb), y ∈ frontier Ω :=
  GraphAtlas.ae_mem_frontier _

/-- A function continuous on `∂Ω` is integrable for the surface measure. -/
theorem integrable_boundaryMeasure_of_continuousOn {G : Type*} [NormedAddCommGroup G]
    {f : 𝔼 → G} (hf : ContinuousOn f (frontier Ω)) : Integrable f (hΩ.boundaryMeasure hb) :=
  GraphAtlas.integrable_of_continuousOn _ hf

/-- **The integral against the surface measure, in the charts of the chosen atlas**
`a := hΩ.graphAtlas hb`:
`∫ f dσ = ∑ i, ∫ x' in a.graphDomain i, √(1 + |∇(a.g i)|²) · θᵢ(Φᵢ x') • f (Φᵢ x')` with
`Φᵢ := graphParam (a.T i) (a.g i)`. -/
theorem integral_boundaryMeasure {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : Integrable f (hΩ.boundaryMeasure hb)) :
    ∫ y, f y ∂(hΩ.boundaryMeasure hb) = ∑ i, ∫ x' in (hΩ.graphAtlas hb).graphDomain i,
      (EuclideanSpace.graphDensity ((hΩ.graphAtlas hb).g i) x' *
        (hΩ.graphAtlas hb).θ i
          (EuclideanSpace.graphParam ((hΩ.graphAtlas hb).T i) ((hΩ.graphAtlas hb).g i) x')) •
          f (EuclideanSpace.graphParam ((hΩ.graphAtlas hb).T i) ((hΩ.graphAtlas hb).g i) x') :=
  GraphAtlas.integral_measure _ hf

/-- The integral against the surface measure as the sum over the chosen atlas of the integrals
against the local measures weighted by the partition of unity. -/
theorem integral_boundaryMeasure_eq_sum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : 𝔼 → G} (hf : Integrable f (hΩ.boundaryMeasure hb)) :
    ∫ y, f y ∂(hΩ.boundaryMeasure hb)
      = ∑ i, ∫ y, (hΩ.graphAtlas hb).θ i y • f y ∂((hΩ.graphAtlas hb).localMeasure i) :=
  GraphAtlas.integral_measure_eq_sum _ hf

/-- **The chart characterization of the surface measure**: for *any* `C¹` graph chart `(T, g)` of
`Ω` at `(x₀, r)`, the surface measure restricted to `B(x₀, r)` is the chart's graph measure
`graphMeasure T g (graphDomain T g x₀ r)`, the pushforward of `√(1 + |∇g|²) dx'`. This is the
theorem that makes `boundaryMeasure` canonical and what consumers compute with. -/
theorem boundaryMeasure_restrict_ball {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g)
    {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    (hΩ.boundaryMeasure hb).restrict (Metric.ball x₀ r)
      = EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r) :=
  GraphAtlas.measure_restrict_ball _ hg h

/-- **Composition with a patch respects equality almost everywhere on `∂Ω`**: two functions equal
`σ`-almost everywhere on `∂Ω` pull back to functions equal almost everywhere on the parameter
domain `Dᵢ` of a chart, since on the chart ball `σ` is the pushforward under `Φᵢ` of a measure
with a positive density with respect to Lebesgue measure on `Dᵢ`
(`boundaryMeasure_restrict_ball`, `EuclideanSpace.graphDensity_pos`). This is what makes a
condition on `v ∘ Φᵢ` a condition on the class of `v` in `L^p(∂Ω)`
([han2009theoretical] Definition 7.2.13). -/
theorem ae_eq_comp_graphParam (a : GraphAtlas Ω) (i : Fin a.k) {f g : 𝔼 → ℝ}
    (h : f =ᵐ[hΩ.boundaryMeasure hb] g) :
    f ∘ EuclideanSpace.graphParam (a.T i) (a.g i)
      =ᵐ[volume.restrict (a.graphDomain i)] g ∘ EuclideanSpace.graphParam (a.T i) (a.g i) := by
  have h1 : f =ᵐ[(hΩ.boundaryMeasure hb).restrict (Metric.ball (a.x i) (a.r i))] g :=
    ae_restrict_of_ae h
  rw [hΩ.boundaryMeasure_restrict_ball hb (a.contDiff_g i) (a.inter_ball_eq i),
    EuclideanSpace.graphMeasure] at h1
  have h2 := h1.comp_tendsto (Measure.tendsto_ae_map
    (EuclideanSpace.continuous_graphParam (a.contDiff_g i).continuous).aemeasurable)
  rw [Filter.EventuallyEq, ae_withDensity_iff
    (EuclideanSpace.measurable_ofReal_graphDensity (a.contDiff_g i))] at h2
  exact h2.mono fun x hx ↦ hx (ENNReal.ofReal_pos.2 (EuclideanSpace.graphDensity_pos _)).ne'

/-- The surface measure of a chart ball is the weighted Lebesgue measure of the parameter
domain. -/
theorem boundaryMeasure_ball_eq_lintegral {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g)
    {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    hΩ.boundaryMeasure hb (Metric.ball x₀ r)
      = ∫⁻ x' in EuclideanSpace.graphDomain T g x₀ r,
          ENNReal.ofReal (EuclideanSpace.graphDensity g x') := by
  rw [← Measure.restrict_apply_univ, boundaryMeasure_restrict_ball hΩ hb hg h,
    EuclideanSpace.graphMeasure_apply hg.continuous _ MeasurableSet.univ, preimage_univ, inter_univ]

/-- **The surface measure has full support on `∂Ω`**: every open set meeting `∂Ω` has positive
surface measure. In a chart at a common point, a small ball has measure at least the Lebesgue
measure of its nonempty open parameter domain (the density is `≥ 1`). -/
theorem boundaryMeasure_pos_of_isOpen {U : Set 𝔼} (hU : IsOpen U)
    (hne : (U ∩ frontier Ω).Nonempty) : 0 < hΩ.boundaryMeasure hb U := by
  obtain ⟨x, hxU, hxF⟩ := hne
  obtain ⟨r, hr, T, g, hg, h⟩ := hΩ.isBoundaryOfClass x hxF
  replace hg : ContDiff ℝ 1 g := hg
  replace h : Ω ∩ Metric.ball x r = Metric.ball x r ∩ T ⁻¹' EuclideanSpace.epigraph g := h
  obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.1 hU x hxU
  set ρ := min r r' with hρdef
  have hρ : 0 < ρ := lt_min hr hr'
  have hρr : Metric.ball x ρ ⊆ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _)
  have hρU : Metric.ball x ρ ⊆ U := (Metric.ball_subset_ball (min_le_right _ _)).trans hr'U
  have h' : Ω ∩ Metric.ball x ρ = Metric.ball x ρ ∩ T ⁻¹' EuclideanSpace.epigraph g := by
    ext y
    have e := Set.ext_iff.1 h y
    simp only [mem_inter_iff] at e ⊢
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (e.1 ⟨h1, hρr h2⟩).2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(e.2 ⟨hρr h1, h2⟩).1, h1⟩
  have hne' : (EuclideanSpace.graphDomain T g x ρ).Nonempty := by
    refine ⟨EuclideanSpace.init (T x), ?_⟩
    change EuclideanSpace.graphParam T g (EuclideanSpace.init (T x)) ∈ Metric.ball x ρ
    rw [EuclideanSpace.graphParam_eq_of_mem_frontier hg.continuous
      (EuclideanSpace.mem_frontier_preimage_epigraph_of_mem_frontier hg.continuous h' hxF
        (Metric.mem_ball_self hρ))]
    exact Metric.mem_ball_self hρ
  calc 0 < volume (EuclideanSpace.graphDomain T g x ρ) :=
        (EuclideanSpace.isOpen_graphDomain hg.continuous x ρ).measure_pos volume hne'
    _ ≤ ∫⁻ x' in EuclideanSpace.graphDomain T g x ρ,
          ENNReal.ofReal (EuclideanSpace.graphDensity g x') := by
        rw [← setLIntegral_one]
        refine setLIntegral_mono' (EuclideanSpace.measurableSet_graphDomain hg.continuous x ρ)
          fun x' _ ↦ ?_
        simpa using ENNReal.ofReal_le_ofReal (EuclideanSpace.one_le_graphDensity (g := g) x')
    _ = hΩ.boundaryMeasure hb (Metric.ball x ρ) :=
        (boundaryMeasure_ball_eq_lintegral hΩ hb hg h').symm
    _ ≤ hΩ.boundaryMeasure hb U := measure_mono hρU

/-- The surface measure of a nonempty bounded `C¹` domain is positive. -/
theorem boundaryMeasure_univ_pos (hne : Ω.Nonempty) : 0 < hΩ.boundaryMeasure hb univ :=
  hΩ.boundaryMeasure_pos_of_isOpen hb isOpen_univ
    (by rw [univ_inter]; exact hb.frontier_nonempty hne)

/-- On `∂Ω ∩ B(a.x i, a.r i)` the outward normal is the `i`-th chart normal of the chosen atlas
`a := hΩ.graphAtlas hb`. -/
theorem outwardNormal_eq_graphNormal_atlas {y : 𝔼} (hy : y ∈ frontier Ω)
    {i : Fin (hΩ.graphAtlas hb).k}
    (hi : y ∈ Metric.ball ((hΩ.graphAtlas hb).x i) ((hΩ.graphAtlas hb).r i)) :
    hΩ.outwardNormal hb y
      = EuclideanSpace.graphNormal ((hΩ.graphAtlas hb).T i) ((hΩ.graphAtlas hb).g i) y :=
  GraphAtlas.normal_eq_graphNormal _ hy hi

/-- **The chart characterization of the outward normal**: for *any* `C¹` graph chart `(T, g)` of
`Ω` at `(x₀, r)` and every `y ∈ ∂Ω ∩ B(x₀, r)`, `outwardNormal hΩ hb y = graphNormal T g y`,
that is `T.linear⁻¹ (∇g y', −1) / √(1 + |∇g y'|²)` with `y' = (T y)'`. -/
theorem outwardNormal_eq_graphNormal {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g)
    {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    {y : 𝔼} (hy : y ∈ frontier Ω) (hyB : y ∈ Metric.ball x₀ r) :
    hΩ.outwardNormal hb y = EuclideanSpace.graphNormal T g y :=
  GraphAtlas.normal_eq_graphNormal_of_inter_eq _ hg h hy hyB

/-- The outward normal is the normal of every graph atlas of `Ω`, on `∂Ω`. -/
theorem outwardNormal_eq_normal (a : GraphAtlas Ω) {y : 𝔼} (hy : y ∈ frontier Ω) :
    hΩ.outwardNormal hb y = a.normal y :=
  GraphAtlas.normal_eq_of_mem_frontier _ a hy

theorem norm_outwardNormal {y : 𝔼} (hy : y ∈ frontier Ω) : ‖hΩ.outwardNormal hb y‖ = 1 :=
  GraphAtlas.norm_normal _ hy

theorem continuousOn_outwardNormal : ContinuousOn (hΩ.outwardNormal hb) (frontier Ω) :=
  GraphAtlas.continuousOn_normal _

theorem ae_norm_outwardNormal : ∀ᵐ y ∂(hΩ.boundaryMeasure hb), ‖hΩ.outwardNormal hb y‖ = 1 :=
  GraphAtlas.ae_norm_normal _

theorem aestronglyMeasurable_outwardNormal :
    AEStronglyMeasurable (hΩ.outwardNormal hb) (hΩ.boundaryMeasure hb) :=
  GraphAtlas.aestronglyMeasurable_normal _

end IsContDiffDomain

end
