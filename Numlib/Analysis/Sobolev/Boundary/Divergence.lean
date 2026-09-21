import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Numlib.Analysis.Sobolev.Boundary.ChartGraph
import Numlib.Analysis.Sobolev.Boundary.Data

/-!
# The divergence theorem on the region above a graph

The analytic heart of the boundary round (decision B4 of `notes/boundary/planning-brief.md`): for
a field `F : ℝ^{d+1} → ℝ^{d+1}` of class `C¹(Ω̄)` with compact support, on the epigraph
`Ω = {y : y_N > g y'}` of a `C¹` function `g : ℝ^d → ℝ`,

  `∫_Ω div F = ∫ ⟪F (x', g x'), (∇g x', −1)⟫ dx'`  (`EuclideanSpace.integral_div_epigraph`),

which is `∫_{∂Ω} ⟪F, ν⟫ dσ` for the surface measure with density `√(1 + |∇g|²)` and the outward
normal `ν = (∇g, −1)/√(1 + |∇g|²)` of `Boundary/GraphMeasure.lean`: the two square roots cancel,
and this module states its conclusions as the explicit integrals over `ℝ^d` so that it is
independent of that module. The transport to a rotated epigraph `T ⁻¹' epigraph g`
(`integral_div_graphEpigraph`) and to a graph chart `(T, g)` of a domain, for a field supported in
the chart ball (`IsBoundaryGraphAt.integral_div_eq_of_tsupport_subset`), are the inputs of the
assembly `IsContDiffDomain.integral_div_eq` in `Boundary/ContDiffDomain.lean`.

No Piola identity, no area formula, no Hausdorff measure. The proof is Fubini along the last
coordinate (`EuclideanSpace.integral_lastInit`), the fundamental theorem of calculus on the
vertical lines for the last component (`integral_fderiv_last_epigraph`), and, for a horizontal
component `∂ᵢ`, **Leibniz's rule with the moving lower limit**
(`integral_fderiv_castSucc_epigraph`): the function `H(x') = ∫_0^∞ f(x', g x' + s) ds` is
differentiable with compact support by Mathlib's dominated differentiation
`hasFDerivAt_integral_of_dominated_of_fderiv_le` — the substitution `t = g x' + s` straightens
the lower limit — so `∫ ∂ᵢH = 0`
(`integral_fderiv_apply_eq_zero_of_hasCompactSupport`), and
`∂ᵢH = ∫_{t > g x'} ∂ᵢf(x', t) dt + ∂ᵢg(x') ∫_{t > g x'} ∂_N f(x', t) dt`, the second integral
being `−f(x', g x')` by the fundamental theorem of calculus.

Regularity: the hypotheses are `HasCompactSupport f`, `ContinuousOn f (closure (epigraph g))` and
`ContDiffOnClosure ℝ 1 f (epigraph g)` — "`f ∈ C¹(Ω̄)`" in the library's sense — which the
one-dimensional FTC (`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`: continuity on
`Icc`, derivative on `Ioo`) and the dominated differentiation (derivative bounded on the support,
`ContDiffOnClosure.exists_norm_fderiv_le_of_hasCompactSupport`) absorb at no cost. This is why the
books' `C¹(Ω̄)` Green formulas are reachable without a `C¹(Ω̄) → C¹(ℝ^N)` extension theorem. The
class is local on the support (`ContDiffOnClosure.congr_set_of_tsupport_subset`), which moves a
field supported in a chart ball from `Ω` to the global rotated epigraph.

## Main statements

* `integral_fderiv_apply_eq_zero_of_hasCompactSupport`: `∫ ∂_v f = 0` for a differentiable `f`
  with compact support and integrable `∂_v f` (and
  `EuclideanSpace.integral_div_eq_zero_of_hasCompactSupport` for the divergence);
* `EuclideanSpace.integral_epigraph_eq`: Fubini on the epigraph;
* `EuclideanSpace.integral_fderiv_last_epigraph`,
  `EuclideanSpace.integral_fderiv_castSucc_epigraph`: the vertical and the horizontal components;
* `EuclideanSpace.integral_div_epigraph`, `EuclideanSpace.integral_div_graphEpigraph`,
  `IsBoundaryGraphAt.integral_div_eq_of_tsupport_subset`: the divergence theorem on an epigraph,
  a rotated epigraph, and a graph chart of a domain.

Conventions: `E := EuclideanSpace ℝ (Fin (d + 1))`, `E' := EuclideanSpace ℝ (Fin d)`,
`snocLast x' t = (x', t)`, `eN := EuclideanSpace.single (Fin.last d) 1`,
`e i := EuclideanSpace.single i.castSucc 1` for `i : Fin d`. The sign of the normal: `Ω` is
*above* the graph, so the outward normal is `(∇g, −1)/√(1 + |∇g|²)` (erratum E1 of
`notes/boundary/plan-report.md`).

## References

Grisvard, *Elliptic Problems in Nonsmooth Domains*, §1.5.3 (Theorem 1.5.3.1); Evans, *Partial
Differential Equations*, Appendix C.2; Atkinson–Han §7.6; [brezis2011functional] §9.5 Example 4.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProductSpace

noncomputable section

/-! ### Integrability helpers -/

section Integrability

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [NormedAddCommGroup G]

/-- A function bounded on a measurable set `s`, strongly measurable there, and vanishing on `s`
outside a set `K` of finite measure is integrable on `s`. -/
theorem integrableOn_of_forall_norm_le_of_eq_zero {φ : X → G} {s K : Set X}
    (hs : MeasurableSet s) (hK : μ K ≠ ⊤) (hφ : AEStronglyMeasurable φ (μ.restrict s)) {M : ℝ}
    (hM : ∀ y ∈ s, ‖φ y‖ ≤ M) (h0 : ∀ y ∈ s, y ∉ K → φ y = 0) : IntegrableOn φ s μ := by
  have h1 : IntegrableOn φ (s ∩ K) μ := by
    refine IntegrableOn.of_bound ((measure_mono inter_subset_right).trans_lt hK.lt_top)
      (hφ.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) M ?_
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left (ae_restrict_of_forall_mem hs hM)
  exact h1.of_forall_sdiff_eq_zero hs fun y hy ↦ h0 y hy.1 fun hK' ↦ hy.2 ⟨hy.1, hK'⟩

/-- Translation of a half-line integral: `∫_0^∞ φ(a + s) ds = ∫_a^∞ φ(t) dt`. -/
theorem integral_Ioi_comp_add_left {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : ℝ → G) (a : ℝ) : ∫ s in Ioi (0 : ℝ), φ (a + s) = ∫ t in Ioi a, φ t := by
  have h := integral_add_left_eq_self (μ := volume) (fun t ↦ (Ioi a).indicator φ t) a
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi, ← h]
  congr 1
  funext s
  rw [← Set.indicator_comp_right (fun s ↦ a + s) (g := φ) (s := Ioi a),
    Set.preimage_const_add_Ioi, sub_self]
  rfl

end Integrability

/-! ### The integral of a derivative of a compactly supported function vanishes -/

section IntegralFDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The integral of a derivative of a compactly supported function vanishes**: for `f : E → ℝ`
differentiable with compact support and `∂_v f` integrable, `∫ ∂_v f dμ = 0` for every additive
Haar measure `μ`. Mathlib's integration by parts
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` against the constant `1`. Continuity of
`fderiv ℝ f` is not needed, only its integrability — which is what the Leibniz step
`EuclideanSpace.integral_fderiv_castSucc_epigraph` has. -/
theorem integral_fderiv_apply_eq_zero_of_hasCompactSupport {f : E → ℝ} (hf : Differentiable ℝ f)
    (hfc : HasCompactSupport f) {v : E} (hf' : Integrable (fun x ↦ fderiv ℝ f x v) μ) :
    ∫ x, fderiv ℝ f x v ∂μ = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := fun _ ↦ (1 : ℝ))
    (g := f) (v := v) (by simp) (by simpa using hf')
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hfc)
    (fun x _ ↦ differentiableAt_const _) (fun x _ ↦ hf x)
  simpa using h

/-- The integral of a derivative of a compactly supported `C¹` function vanishes. -/
theorem integral_fderiv_apply_eq_zero_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (v : E) : ∫ x, fderiv ℝ f x v ∂μ = 0 :=
  integral_fderiv_apply_eq_zero_of_hasCompactSupport (hf.differentiable one_ne_zero) hfc
    (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.fderiv_apply ℝ hfc v))

end IntegralFDeriv

/-- **The integral of the divergence of a compactly supported field vanishes**: for
`F : ℝ^N → ℝ^N` differentiable with compact support and integrable derivative, `∫ div F = 0`. -/
theorem EuclideanSpace.integral_div_eq_zero_of_hasCompactSupport {N : ℕ}
    {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} (hF : Differentiable ℝ F)
    (hFc : HasCompactSupport F) (hF' : Integrable (fderiv ℝ F)) : ∫ x, div F x = 0 := by
  have hcoord : ∀ i : Fin N, ∀ x,
      fderiv ℝ F x (EuclideanSpace.single i 1) i
        = fderiv ℝ (fun y ↦ F y i) x (EuclideanSpace.single i 1) := fun i x ↦ by
    have h := ((EuclideanSpace.proj i).hasFDerivAt.comp x (hF x).hasFDerivAt).fderiv
    rw [show (fun y ↦ F y i) = (EuclideanSpace.proj i) ∘ F from rfl, h]
    rfl
  have hint : ∀ i : Fin N,
      Integrable fun x ↦ fderiv ℝ (fun y ↦ F y i) x (EuclideanSpace.single i 1) := fun i ↦ by
    refine hF'.norm.mono' (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [← hcoord]
    refine (PiLp.norm_apply_le _ _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    rw [PiLp.norm_single, norm_one, mul_one]
  simp only [div, hcoord]
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  exact integral_fderiv_apply_eq_zero_of_hasCompactSupport
    (fun x ↦ (EuclideanSpace.proj i).differentiableAt.comp x (hF x))
    (hFc.comp_left (g := fun v ↦ v i) rfl) (hint i)

/-! ### The class `C¹(s̄)`: bounded derivatives, compositions, locality on the support -/

section ContDiffOnClosure

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X F G : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {f : X → F} {s : Set X}

/-- The derivative of a function vanishes off its closed support. -/
theorem fderiv_eq_zero_of_notMem_tsupport {x : X} (hx : x ∉ tsupport f) : fderiv 𝕜 f x = 0 :=
  Function.notMem_support.1 fun h ↦ hx (support_fderiv_subset 𝕜 h)

/-- **A function of class `C¹(s̄)` with compact support has a bounded derivative on `s`**: the
continuous extension of `fderiv 𝕜 f` is bounded on the compact `closure s ∩ tsupport f`, and
`fderiv 𝕜 f = 0` off `tsupport f`. Compare `ContDiffOn.exists_norm_fderiv_le_of_isCompact` of
`Chart.lean`, which bounds the derivative on the interior of a compact set. -/
theorem ContDiffOnClosure.exists_norm_fderiv_le_of_hasCompactSupport
    (hf : ContDiffOnClosure 𝕜 1 f s) (hfc : HasCompactSupport f) :
    ∃ M, ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ M := by
  obtain ⟨-, -, G, hGc, hGe⟩ := contDiffOnClosure_one_iff.1 hf
  obtain ⟨C, hC⟩ := (hfc.inter_left isClosed_closure).exists_bound_of_continuousOn
    (hGc.mono inter_subset_left)
  refine ⟨max C 0, fun x hx ↦ ?_⟩
  by_cases hxs : x ∈ tsupport f
  · rw [← hGe hx]
    exact (hC x ⟨subset_closure hx, hxs⟩).trans (le_max_left _ _)
  · rw [fderiv_eq_zero_of_notMem_tsupport hxs, norm_zero]
    exact le_max_right _ _

/-- **`C¹(s̄)` is stable under a continuous linear map on the left**, on an open set `s`: the
extensions of `f` and `Df` compose with `L`. -/
theorem ContDiffOnClosure.continuousLinearMap_comp (hs : IsOpen s)
    (hf : ContDiffOnClosure 𝕜 1 f s) (L : F →L[𝕜] G) :
    ContDiffOnClosure 𝕜 1 (fun x ↦ L (f x)) s := by
  rw [contDiffOnClosure_one_iff] at hf ⊢
  obtain ⟨hf, ⟨g₀, hg₀c, hg₀e⟩, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf
  refine ⟨hf.continuousLinearMap_comp L, ⟨fun x ↦ L (g₀ x), L.continuous.comp_continuousOn hg₀c,
    fun x hx ↦ by simp only [hg₀e hx]⟩, ⟨fun x ↦ L.comp (g₁ x), continuousOn_const.clm_comp hg₁c,
    fun x hx ↦ ?_⟩⟩
  have hx' : DifferentiableAt 𝕜 f x :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
  simp only [hg₁e hx]
  exact (L.hasFDerivAt.comp x hx'.hasFDerivAt).fderiv.symm

/-- A function continuous on `closure s` and vanishing on `s` outside a closed set `K` vanishes
on `closure s` outside `K`: `closure s \ K` lies in the closure of `s \ K`. -/
theorem ContinuousOn.eq_zero_of_notMem_of_forall {Y : Type*} [TopologicalSpace Y] {φ : Y → G}
    {s K : Set Y} (hφ : ContinuousOn φ (closure s)) (hK : IsClosed K)
    (h : ∀ y ∈ s, y ∉ K → φ y = 0) {y : Y} (hy : y ∈ closure s) (hyK : y ∉ K) : φ y = 0 := by
  have hsub : closure s ∩ Kᶜ ⊆ closure (s ∩ Kᶜ) := fun z hz ↦ by
    have := hK.isOpen_compl.inter_closure ⟨hz.2, hz.1⟩
    rwa [inter_comm] at this
  exact Set.EqOn.of_subset_closure (s := s ∩ Kᶜ) (t := closure s ∩ Kᶜ) (f := φ) (g := 0)
    (fun z hz ↦ h z hz.1 hz.2) (hφ.mono inter_subset_left) continuousOn_const
    (inter_subset_inter_left _ subset_closure) hsub ⟨hy, hyK⟩

/-- The indicator on `tsupport f` of a function `φ` continuous on `closure s` and vanishing on
`s \ tsupport f` is continuous on `closure s'`, when `s ∩ V = s' ∩ V` for an open `V ⊇ tsupport f`:
near a point of `V`, `closure s' ∩ V ⊆ closure s` and `φ` serves; away from `V` the indicator
vanishes on a neighbourhood. The continuity clauses of
`ContDiffOnClosure.congr_set_of_tsupport_subset`. -/
theorem ContinuousOn.indicator_tsupport_of_inter_eq {Y : Type*} [TopologicalSpace Y]
    {f : Y → F} {s s' V : Set Y} (hV : IsOpen V) (hsV : s ∩ V = s' ∩ V) (hsupp : tsupport f ⊆ V)
    {φ : Y → G} (hφ : ContinuousOn φ (closure s)) (hφ0 : ∀ x ∈ s, x ∉ tsupport f → φ x = 0) :
    ContinuousOn ((tsupport f).indicator φ) (closure s') := by
  -- `closure s' ∩ V ⊆ closure s`, and `closure s` is a neighbourhood within `closure s'` there
  have hcl : closure s' ∩ V ⊆ closure s := fun x hx ↦ by
    have h1 : x ∈ closure (s' ∩ V) := by
      have := hV.inter_closure ⟨hx.2, hx.1⟩
      rwa [inter_comm] at this
    rw [← hsV] at h1
    exact closure_mono inter_subset_left h1
  have hnhds : ∀ x ∈ closure s', x ∈ V → closure s ∈ 𝓝[closure s'] x := fun x hx hxV ↦
    mem_nhdsWithin.2 ⟨V, hV, hxV, fun z hz ↦ hcl ⟨hz.2, hz.1⟩⟩
  intro x hx
  have heq : ∀ z ∈ closure s, (tsupport f).indicator φ z = φ z := fun z hz ↦ by
    by_cases hzK : z ∈ tsupport f
    · exact indicator_of_mem hzK _
    · rw [indicator_of_notMem hzK,
        hφ.eq_zero_of_notMem_of_forall (isClosed_tsupport f) hφ0 hz hzK]
  by_cases hxV : x ∈ V
  · have h1 : ContinuousWithinAt φ (closure s') x :=
      (hφ x (hcl ⟨hx, hxV⟩)).mono_of_mem_nhdsWithin (hnhds x hx hxV)
    refine h1.congr_of_eventuallyEq ?_ (heq x (hcl ⟨hx, hxV⟩))
    filter_upwards [hnhds x hx hxV] with z hz using heq z hz
  · have hxs : x ∉ tsupport f := fun h ↦ hxV (hsupp h)
    have hev : (tsupport f).indicator φ =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxs] with z hz
      exact indicator_of_notMem hz _
    exact (continuousAt_const.congr hev.symm).continuousWithinAt

/-- **The class `C¹(Ω̄)` is local on the support**: for open sets `s`, `V` and a set `s'` with
`s ∩ V = s' ∩ V`, a function `f ∈ C¹(s̄)` with `tsupport f ⊆ V` is in `C¹(s̄')`. Near a point of
`V`, `closure s' ∩ V ⊆ closure (s ∩ V)` and the data of `f` on `closure s` serve; away from `V`
the function vanishes on a neighbourhood. The extension of `Df` to `closure s'` is
`(tsupport f).indicator` of the given extension, which vanishes on `closure s \ tsupport f`
(`ContinuousOn.eq_zero_of_notMem_of_forall`, `ContinuousOn.indicator_tsupport_of_inter_eq`).
Used to move a field supported in a chart ball from `Ω` to the global rotated epigraph. -/
theorem ContDiffOnClosure.congr_set_of_tsupport_subset {s' V : Set X} (hs : IsOpen s)
    (hV : IsOpen V) (hsV : s ∩ V = s' ∩ V) (hsupp : tsupport f ⊆ V)
    (hf₀ : ContinuousOn f (closure s)) (hf₁ : ContDiffOnClosure 𝕜 1 f s) :
    ContinuousOn f (closure s') ∧ ContDiffOnClosure 𝕜 1 f s' := by
  have hmem : ∀ x ∈ s', x ∈ V → x ∈ s := fun x hx hxV ↦ by
    have : x ∈ s' ∩ V := ⟨hx, hxV⟩
    rw [← hsV] at this
    exact this.1
  have hcontf : ContinuousOn f (closure s') := by
    have := hf₀.indicator_tsupport_of_inter_eq hV hsV hsupp
      fun x _ hx ↦ image_eq_zero_of_notMem_tsupport (f := f) hx
    rwa [Set.indicator_eq_self.2 (subset_tsupport f)] at this
  refine ⟨hcontf, ?_⟩
  rw [contDiffOnClosure_one_iff] at hf₁ ⊢
  obtain ⟨hf, -, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf₁
  refine ⟨fun x hx ↦ ?_, ⟨f, hcontf, fun _ _ ↦ rfl⟩, ⟨(tsupport f).indicator g₁,
    hg₁c.indicator_tsupport_of_inter_eq hV hsV hsupp fun x hx hxK ↦ ?_, fun x hx ↦ ?_⟩⟩
  · by_cases hxV : x ∈ V
    · exact (hf.contDiffAt (hs.mem_nhds (hmem x hx hxV))).contDiffWithinAt
    · have hxs : x ∉ tsupport f := fun h ↦ hxV (hsupp h)
      exact (contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hxs)).contDiffWithinAt
  · rw [hg₁e hx]
    exact fderiv_eq_zero_of_notMem_tsupport hxK
  · by_cases hxK : x ∈ tsupport f
    · rw [indicator_of_mem hxK, hg₁e (hmem x hx (hsupp hxK))]
    · rw [indicator_of_notMem hxK, fderiv_eq_zero_of_notMem_tsupport hxK]

end ContDiffOnClosure

section AffineIsometryEquiv

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A rigid motion `T x = T.linear x + T 0` has derivative its linear part. -/
theorem AffineIsometryEquiv.hasFDerivAt (T : E' ≃ᵃⁱ[ℝ] E) (z : E') :
    HasFDerivAt T (T.linearIsometryEquiv.toContinuousLinearEquiv : E' →L[ℝ] E) z := by
  have h : (T : E' → E) = fun z ↦ T.linearIsometryEquiv z + T 0 := by
    funext z
    have := T.map_vadd (0 : E') z
    rwa [vadd_eq_add, add_zero, vadd_eq_add] at this
  rw [h]
  exact T.linearIsometryEquiv.toContinuousLinearEquiv.hasFDerivAt.add_const (T 0)

/-- **`C¹(s̄)` is stable under a rigid motion on the right**: `f ∘ T ∈ C¹(T⁻¹(s)‾)` for
`f ∈ C¹(s̄)`, `s` open. The extensions compose with `T`, the derivative with `T`'s linear part. -/
theorem ContDiffOnClosure.comp_affineIsometryEquiv {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOnClosure ℝ 1 f s) (T : E' ≃ᵃⁱ[ℝ] E) :
    ContDiffOnClosure ℝ 1 (fun z ↦ f (T z)) (T ⁻¹' s) := by
  rw [contDiffOnClosure_one_iff] at hf ⊢
  obtain ⟨hf, ⟨g₀, hg₀c, hg₀e⟩, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf
  have hcl : closure (T ⁻¹' s) = T ⁻¹' closure s := by
    have := T.toHomeomorph.preimage_closure s
    rwa [AffineIsometryEquiv.coe_toHomeomorph, eq_comm] at this
  have hTc : ContinuousOn T (closure (T ⁻¹' s)) := T.continuous.continuousOn
  have hmaps : MapsTo T (closure (T ⁻¹' s)) (closure s) := fun z hz ↦ by rwa [hcl] at hz
  have hT : ContDiff ℝ 1 T := T.toAffineIsometry.toContinuousAffineMap.contDiff
  refine ⟨hf.comp hT.contDiffOn (mapsTo_preimage T s), ⟨fun z ↦ g₀ (T z), hg₀c.comp hTc hmaps,
    fun z hz ↦ hg₀e hz⟩, ⟨fun z ↦ (g₁ (T z)).comp
      (T.linearIsometryEquiv.toContinuousLinearEquiv : E' →L[ℝ] E),
    (hg₁c.comp hTc hmaps).clm_comp continuousOn_const, fun z hz ↦ ?_⟩⟩
  have hd : DifferentiableAt ℝ f (T z) :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hz)
  simp only [hg₁e hz]
  exact (hd.hasFDerivAt.comp z (T.hasFDerivAt z)).fderiv.symm

end AffineIsometryEquiv

namespace EuclideanSpace

variable {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### Fubini on the epigraph -/

/-- **Fubini on the epigraph**: `∫_{y_N > g y'} h = ∫ x' ∫_{t > g x'} h (x', t) dt dx'`. -/
theorem integral_epigraph_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hg : Continuous g) {h : EuclideanSpace ℝ (Fin (d + 1)) → G}
    (hh : IntegrableOn h (epigraph g)) :
    ∫ y in epigraph g, h y = ∫ x', ∫ t in Ioi (g x'), h (snocLast x' t) := by
  have hmeas := (isOpen_epigraph hg).measurableSet
  rw [← integral_indicator hmeas, integral_lastInit _ ((integrable_indicator_iff hmeas).2 hh)]
  refine integral_congr_ae (Eventually.of_forall fun x' ↦ ?_)
  simp only
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext t
  rw [← epigraph_preimage_snocLast x']
  exact (Set.indicator_comp_right (fun t ↦ snocLast x' t) (g := h)).symm

/-- Fubini on the epigraph, for the Lebesgue integral. -/
theorem lintegral_epigraph_eq (hg : Continuous g) {h : EuclideanSpace ℝ (Fin (d + 1)) → ℝ≥0∞}
    (hh : AEMeasurable h (volume.restrict (epigraph g))) :
    ∫⁻ y in epigraph g, h y = ∫⁻ x', ∫⁻ t in Ioi (g x'), h (snocLast x' t) := by
  have hmeas := (isOpen_epigraph hg).measurableSet
  rw [← lintegral_indicator hmeas, lintegral_lastInit _ ((aemeasurable_indicator_iff hmeas).2 hh)]
  refine lintegral_congr fun x' ↦ ?_
  rw [← lintegral_indicator measurableSet_Ioi]
  congr 1
  funext t
  rw [← epigraph_preimage_snocLast x']
  exact (Set.indicator_comp_right (fun t ↦ snocLast x' t) (g := h)).symm

/-- The point `(x', t)` lies in the closure of the epigraph iff `g x' ≤ t`. -/
theorem snocLast_mem_closure_epigraph (hg : Continuous g) (x' : EuclideanSpace ℝ (Fin d))
    (t : ℝ) : snocLast x' t ∈ closure (epigraph g) ↔ g x' ≤ t := by
  rw [closure_epigraph hg]
  simp

/-- `‖(x', t)‖ ≤ ‖x'‖ + |t|`. -/
theorem norm_snocLast_le (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖snocLast x' t‖ ≤ ‖x'‖ + |t| := by
  have h := norm_sq_eq_init_add_last (snocLast x' t)
  rw [init_snocLast, snocLast_apply_last] at h
  have h2 : ‖snocLast x' t‖ ^ 2 ≤ (‖x'‖ + |t|) ^ 2 := by
    rw [h]; nlinarith [norm_nonneg x', abs_nonneg t, sq_abs t]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- The coordinates of the gradient are the partial derivatives. -/
theorem gradient_apply (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin d) : gradient g x i = fderiv ℝ g x (EuclideanSpace.single i 1) := by
  have h : gradient g x i = ⟪gradient g x, EuclideanSpace.single i 1⟫_ℝ := by
    rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  rw [h, gradient, InnerProductSpace.toDual_symm_apply]

/-- The graph map `x' ↦ (x', g x')` is continuous. -/
theorem continuous_snocLast_graph (hg : Continuous g) :
    Continuous fun x' ↦ snocLast x' (g x') :=
  continuous_snocLast.comp (continuous_id.prodMk hg)

variable {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}

/-- A directional derivative of a compactly supported function of class `C¹(Ω̄)` is integrable on
the epigraph: bounded there (`ContDiffOnClosure.exists_norm_fderiv_le_of_hasCompactSupport`),
continuous on the open epigraph, and zero off the compact support. -/
theorem integrableOn_fderiv_apply_epigraph (hg : Continuous g) (hfc : HasCompactSupport f)
    (hf₁ : ContDiffOnClosure ℝ 1 f (epigraph g)) (w : EuclideanSpace ℝ (Fin (d + 1))) :
    IntegrableOn (fun y ↦ fderiv ℝ f y w) (epigraph g) := by
  obtain ⟨M, hM⟩ := hf₁.exists_norm_fderiv_le_of_hasCompactSupport hfc
  refine integrableOn_of_forall_norm_le_of_eq_zero (isOpen_epigraph hg).measurableSet
    hfc.measure_lt_top.ne ?_ (M := M * ‖w‖) (fun y hy ↦ ?_) (fun y _ hy ↦ ?_)
  · exact ((hf₁.1.continuousOn_fderiv_of_isOpen (isOpen_epigraph hg) le_rfl).clm_apply
      continuousOn_const).aestronglyMeasurable (isOpen_epigraph hg).measurableSet
  · exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hM y hy)
  · rw [fderiv_eq_zero_of_notMem_tsupport hy]; rfl

/-- The composition of a compactly supported function on `ℝ^{d+1}` with the graph map
`x' ↦ (x', g x')` has compact support. -/
theorem hasCompactSupport_comp_snocLast_graph {G : Type*} [NormedAddCommGroup G]
    {f : EuclideanSpace ℝ (Fin (d + 1)) → G} (hfc : HasCompactSupport f) :
    HasCompactSupport fun x' ↦ f (snocLast x' (g x')) := by
  obtain ⟨R₀, hR₀⟩ := hfc.isBounded.subset_closedBall 0
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R₀) fun x' hx' ↦ ?_
  have h1 : snocLast x' (g x') ∈ tsupport f := subset_tsupport _ hx'
  have h2 := hR₀ h1
  rw [Metric.mem_closedBall, dist_zero_right] at h2 ⊢
  have h3 := (norm_init_le (snocLast x' (g x'))).trans h2
  rwa [init_snocLast] at h3

/-! ### The vertical component: the fundamental theorem of calculus on the vertical lines -/

/-- **The fundamental theorem of calculus on a vertical line** through the epigraph: for `f` of
class `C¹(Ω̄)` with compact support, `∫_{t > g x'} ∂_N f (x', t) dt = −f (x', g x')`. The
integrand vanishes beyond the support, `t ↦ f (x', t)` is continuous on `[g x', R]` (the closed
half-line lies in the closure of the epigraph) and differentiable on `(g x', R)`, so
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` applies. -/
theorem integral_Ioi_fderiv_last_eq (hg : Continuous g) (hfc : HasCompactSupport f)
    (hf₀ : ContinuousOn f (closure (epigraph g))) (hf₁ : ContDiffOnClosure ℝ 1 f (epigraph g))
    {M : ℝ} (hM : ∀ y ∈ epigraph g, ‖fderiv ℝ f y‖ ≤ M) (x' : EuclideanSpace ℝ (Fin d)) :
    ∫ t in Ioi (g x'), fderiv ℝ f (snocLast x' t) (EuclideanSpace.single (Fin.last d) 1)
      = -f (snocLast x' (g x')) := by
  obtain ⟨R₀, hR₀⟩ := hfc.isBounded.subset_closedBall 0
  set R : ℝ := max (g x') R₀ + 1 with hR
  have hgR : g x' ≤ R := by linarith [le_max_left (g x') R₀]
  have hline : Continuous fun t ↦ snocLast x' t :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_snocLast x' t).continuousAt
  have hout : ∀ t, R ≤ t → snocLast x' t ∉ tsupport f := fun t ht hmem ↦ by
    have h1 := hR₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 := abs_apply_last_le (snocLast x' t)
    rw [snocLast_apply_last] at h2
    have h3 : R₀ < t := by linarith [le_max_right (g x') R₀]
    linarith [le_abs_self t]
  have hmeas : AEStronglyMeasurable
      (fun t ↦ fderiv ℝ f (snocLast x' t) (EuclideanSpace.single (Fin.last d) 1))
      (volume.restrict (Ioi (g x'))) := by
    have h1 : ContinuousOn (fderiv ℝ f) (epigraph g) :=
      hf₁.1.continuousOn_fderiv_of_isOpen (isOpen_epigraph hg) le_rfl
    exact ((h1.comp hline.continuousOn fun t ht ↦ (snocLast_mem_epigraph x' t).2 ht).clm_apply
      continuousOn_const).aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ t ∈ Ioi (g x'),
      ‖fderiv ℝ f (snocLast x' t) (EuclideanSpace.single (Fin.last d) 1)‖ ≤ M := fun t ht ↦ by
    have h1 := hM _ ((snocLast_mem_epigraph x' t).2 ht)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one]
    exact h1
  -- the integrand vanishes above `R`
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun t ht ↦ by
      have ht' : R ≤ t := by
        rcases ht with ⟨ht1, ht2⟩
        by_contra h
        exact ht2 ⟨ht1, (not_le.1 h).le⟩
      rw [fderiv_eq_zero_of_notMem_tsupport (hout t ht')]
      rfl),
    ← intervalIntegral.integral_of_le hgR]
  have hcont : ContinuousOn (fun t ↦ f (snocLast x' t)) (Icc (g x') R) :=
    hf₀.comp hline.continuousOn fun t ht ↦ (snocLast_mem_closure_epigraph hg x' t).2 ht.1
  have hderiv : ∀ t ∈ Ioo (g x') R, HasDerivWithinAt (fun t ↦ f (snocLast x' t))
      (fderiv ℝ f (snocLast x' t) (EuclideanSpace.single (Fin.last d) 1)) (Ioi t) t :=
    fun t ht ↦ by
      have hmem : snocLast x' t ∈ epigraph g := (snocLast_mem_epigraph x' t).2 ht.1
      have hdiff : DifferentiableAt ℝ f (snocLast x' t) :=
        (hf₁.1.differentiableOn one_ne_zero).differentiableAt
          ((isOpen_epigraph hg).mem_nhds hmem)
      exact (hdiff.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_snocLast x' t)).hasDerivWithinAt
  have hint : IntervalIntegrable
      (fun t ↦ fderiv ℝ f (snocLast x' t) (EuclideanSpace.single (Fin.last d) 1)) volume
      (g x') R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hgR]
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      (hmeas.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)) M ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hbound t ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hgR hcont hderiv hint,
    image_eq_zero_of_notMem_tsupport (hout R le_rfl), zero_sub]

/-- **The vertical component of the divergence theorem**: for `ContDiff ℝ 1 g` and `f` of class
`C¹(Ω̄)` with compact support on the epigraph,
`∫_{y_N > g y'} ∂_N f = −∫ f (x', g x') dx'`. Fubini (`integral_epigraph_eq`) and the fundamental
theorem of calculus on each vertical line (`integral_Ioi_fderiv_last_eq`). -/
theorem integral_fderiv_last_epigraph (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f)
    (hf₀ : ContinuousOn f (closure (epigraph g))) (hf₁ : ContDiffOnClosure ℝ 1 f (epigraph g)) :
    ∫ y in epigraph g, fderiv ℝ f y (EuclideanSpace.single (Fin.last d) 1)
      = -∫ x', f (snocLast x' (g x')) := by
  obtain ⟨M, hM⟩ := hf₁.exists_norm_fderiv_le_of_hasCompactSupport hfc
  rw [integral_epigraph_eq hg.continuous (integrableOn_fderiv_apply_epigraph hg.continuous hfc
    hf₁ _), ← integral_neg]
  exact integral_congr_ae (Eventually.of_forall fun x' ↦
    integral_Ioi_fderiv_last_eq hg.continuous hfc hf₀ hf₁ hM x')

/-! ### The horizontal components: Leibniz's rule with the moving lower limit -/

/-- The derivative of the map `x' ↦ (x', g x' + s)`. -/
theorem hasFDerivAt_snocLast_add (hg : ContDiff ℝ 1 g) (x' : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    HasFDerivAt (fun x' ↦ snocLast x' (g x' + s))
      (((initLastL d).symm : EuclideanSpace ℝ (Fin d) × ℝ →L[ℝ] _).comp
        ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x'))) x' := by
  have h1 : HasFDerivAt (fun x' ↦ (x', g x' + s))
      ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x')) x' :=
    (hasFDerivAt_id x').prodMk ((hg.differentiable one_ne_zero x').hasFDerivAt.add_const s)
  exact (initLastL d).symm.hasFDerivAt.comp x' h1

/-- The derivative of `x' ↦ (x', g x' + s)` in the direction `eᵢ` is `eᵢ + ∂ᵢg(x') e_N`. -/
theorem snocLast_add_fderiv_apply_single (x' : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    ((initLastL d).symm : EuclideanSpace ℝ (Fin d) × ℝ →L[ℝ] _).comp
        ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x')) (EuclideanSpace.single i 1)
      = EuclideanSpace.single i.castSucc 1
        + fderiv ℝ g x' (EuclideanSpace.single i 1)
          • EuclideanSpace.single (Fin.last d) (1 : ℝ) := by
  ext j
  induction j using Fin.lastCases <;> simp [Fin.castSucc_ne_last, Fin.castSucc_inj]

/-- **A horizontal component of the divergence theorem — Leibniz's rule with the moving lower
limit**: for `ContDiff ℝ 1 g`, `i : Fin d`, and `f` of class `C¹(Ω̄)` with compact support on the
epigraph, `∫_{y_N > g y'} ∂ᵢ f = ∫ f (x', g x') ∂ᵢg (x') dx'`.

Proof (decision B4): `H x' := ∫_0^∞ f (x', g x' + s) ds` — the substitution `t = g x' + s`
straightens the moving lower limit — is differentiable at every `x'` by Mathlib's dominated
differentiation `hasFDerivAt_integral_of_dominated_of_fderiv_le` (the derivative of the integrand
is bounded by `M (1 + ‖Dg‖)` on `[0, R]` and vanishes beyond, uniformly in `x'`), with
`∂ᵢH x' = ∫_0^∞ ∂ᵢf (x', g x' + s) + ∂ᵢg (x') ∂_N f (x', g x' + s) ds`; `H` has compact support,
so `∫ ∂ᵢH = 0` (`integral_fderiv_apply_eq_zero_of_hasCompactSupport`); the first summand
integrates over `x'` to `∫_{y_N > g y'} ∂ᵢf` (translation and Fubini) and the second is
`−∂ᵢg (x') f (x', g x')` by the fundamental theorem of calculus on the line
(`integral_Ioi_fderiv_last_eq`). -/
theorem integral_fderiv_castSucc_epigraph (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f)
    (hf₀ : ContinuousOn f (closure (epigraph g))) (hf₁ : ContDiffOnClosure ℝ 1 f (epigraph g))
    (i : Fin d) :
    ∫ y in epigraph g, fderiv ℝ f y (EuclideanSpace.single i.castSucc 1)
      = ∫ x', f (snocLast x' (g x')) * fderiv ℝ g x' (EuclideanSpace.single i 1) := by
  have hgc : Continuous g := hg.continuous
  have hopen : IsOpen (epigraph g) := isOpen_epigraph hgc
  -- the constants
  obtain ⟨M, hM⟩ := hf₁.exists_norm_fderiv_le_of_hasCompactSupport hfc
  obtain ⟨R₀, hR₀0, hR₀⟩ : ∃ R₀, 0 ≤ R₀ ∧ tsupport f ⊆ Metric.closedBall 0 R₀ := by
    obtain ⟨R, hR⟩ := hfc.isBounded.subset_closedBall 0
    exact ⟨max R 0, le_max_right _ _,
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨Cg, hCg⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R₀)
    (hg.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨Cg', hCg'⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R₀) hgc.continuousOn
  obtain ⟨Mf, hMf⟩ := (hfc.inter_left isClosed_closure).exists_bound_of_continuousOn
    (hf₀.mono inter_subset_left)
  set R : ℝ := R₀ + Cg' with hRdef
  -- the map `Φ x' s = (x', g x' + s)`, its derivative `DΦ`, the integrand `F` and its derivative
  set Φ : EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin (d + 1)) :=
    fun x' s ↦ snocLast x' (g x' + s) with hΦdef
  set DΦ : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    fun x' ↦ ((initLastL d).symm : EuclideanSpace ℝ (Fin d) × ℝ →L[ℝ] _).comp
      ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x')) with hDΦdef
  set F : EuclideanSpace ℝ (Fin d) → ℝ → ℝ := fun x' s ↦ f (Φ x' s) with hFdef
  set F' : EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fun x' s ↦ (fderiv ℝ f (Φ x' s)).comp (DΦ x') with hF'def
  set H : EuclideanSpace ℝ (Fin d) → ℝ := fun x' ↦ ∫ s in Ioi (0 : ℝ), F x' s with hHdef
  -- pointwise facts
  have hΦmem : ∀ x' s, 0 < s → Φ x' s ∈ epigraph g := fun x' s hs ↦ by
    rw [hΦdef, snocLast_mem_epigraph]; linarith
  have hΦsupp : ∀ x' s, Φ x' s ∈ tsupport f → ‖x'‖ ≤ R₀ ∧ s ≤ R := fun x' s h ↦ by
    have h1 := hR₀ h
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 := norm_init_le (Φ x' s)
    have h3 := abs_apply_last_le (Φ x' s)
    rw [hΦdef, init_snocLast] at h2
    rw [hΦdef, snocLast_apply_last] at h3
    have h4 : ‖x'‖ ≤ R₀ := h2.trans h1
    have h5 := hCg' x' (by rwa [Metric.mem_closedBall, dist_zero_right])
    rw [Real.norm_eq_abs] at h5
    refine ⟨h4, ?_⟩
    have := le_abs_self (g x' + s)
    have := neg_abs_le (g x')
    linarith
  have hΦcont : ∀ x', Continuous (Φ x') := fun x' ↦ by
    have : Continuous fun s : ℝ ↦ (x', g x' + s) := by fun_prop
    exact (initLastL d).symm.continuous.comp this
  have hfderiv_cont : ContinuousOn (fderiv ℝ f) (epigraph g) :=
    hf₁.1.continuousOn_fderiv_of_isOpen hopen le_rfl
  have hDΦ : ∀ x' s, HasFDerivAt (Φ · s) (DΦ x') x' := fun x' s ↦ hasFDerivAt_snocLast_add hg x' s
  have hF'deriv : ∀ x' s, 0 < s → HasFDerivAt (F · s) (F' x' s) x' := fun x' s hs ↦ by
    have hdiff : DifferentiableAt ℝ f (Φ x' s) :=
      (hf₁.1.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds (hΦmem x' s hs))
    exact hdiff.hasFDerivAt.comp x' (hDΦ x' s)
  have hDΦnorm : ∀ x', ‖x'‖ ≤ R₀ → ‖DΦ x'‖ ≤ 1 + Cg := fun x' hx' ↦ by
    have hCgx : ‖fderiv ℝ g x'‖ ≤ Cg := hCg x' (by rwa [Metric.mem_closedBall, dist_zero_right])
    refine ContinuousLinearMap.opNorm_le_bound _
      (by linarith [norm_nonneg (fderiv ℝ g x')]) fun v ↦ ?_
    have h1 : DΦ x' v = snocLast v (fderiv ℝ g x' v) := rfl
    rw [h1]
    refine (norm_snocLast_le _ _).trans ?_
    have h2 : |fderiv ℝ g x' v| ≤ Cg * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    nlinarith [norm_nonneg v]
  -- the bound on the derivative of `f` along `Φ`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (hΦmem 0 1 one_pos))
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0 (by simpa using hR₀0))
  set bound₀ : ℝ → ℝ := (Icc (0 : ℝ) R).indicator fun _ ↦ M with hbound₀def
  have hbound₀_int : Integrable bound₀ (volume.restrict (Ioi 0)) := by
    rw [hbound₀def]
    refine (integrable_indicator_iff measurableSet_Icc).2 ?_
    refine integrableOn_const (C := M) ?_
    rw [Measure.restrict_apply measurableSet_Icc]
    exact ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
  have hbound₀_nonneg : ∀ s, 0 ≤ bound₀ s := fun s ↦ indicator_nonneg (fun _ _ ↦ hM0) s
  have hbound₀ : ∀ x' s, 0 < s → ‖fderiv ℝ f (Φ x' s)‖ ≤ bound₀ s := fun x' s hs ↦ by
    by_cases hsupp : Φ x' s ∈ tsupport f
    · have hs' : s ∈ Icc (0 : ℝ) R := ⟨hs.le, (hΦsupp x' s hsupp).2⟩
      rw [hbound₀def, indicator_of_mem hs']
      exact hM _ (hΦmem x' s hs)
    · rw [fderiv_eq_zero_of_notMem_tsupport hsupp, norm_zero]
      exact hbound₀_nonneg s
  set bound : ℝ → ℝ := fun s ↦ bound₀ s * (1 + Cg) with hbounddef
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := hbound₀_int.mul_const _
  have hF'bound : ∀ x' s, 0 < s → ‖F' x' s‖ ≤ bound s := fun x' s hs ↦ by
    by_cases hsupp : Φ x' s ∈ tsupport f
    · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul (hbound₀ x' s hs) (hDΦnorm x' (hΦsupp x' s hsupp).1) (norm_nonneg _)
        (hbound₀_nonneg s)
    · have : F' x' s = 0 := by
        rw [hF'def]; simp only; rw [fderiv_eq_zero_of_notMem_tsupport hsupp]; rfl
      rw [this, norm_zero, hbounddef]
      exact mul_nonneg (hbound₀_nonneg s) (by linarith)
  -- measurability and integrability of the integrand and of its derivative
  have hFmeas : ∀ x', AEStronglyMeasurable (F x') (volume.restrict (Ioi 0)) := fun x' ↦ by
    refine (hf₀.comp (hΦcont x').continuousOn fun s hs ↦ ?_).aestronglyMeasurable
      measurableSet_Ioi
    exact subset_closure (hΦmem x' s hs)
  have hFint : ∀ x', Integrable (F x') (volume.restrict (Ioi 0)) := fun x' ↦ by
    refine integrableOn_of_forall_norm_le_of_eq_zero measurableSet_Ioi
      (K := Icc 0 R) measure_Icc_lt_top.ne (hFmeas x') (M := max Mf 0) (fun s hs ↦ ?_)
      (fun s hs hsR ↦ ?_)
    · by_cases hsupp : Φ x' s ∈ tsupport f
      · exact (hMf _ ⟨subset_closure (hΦmem x' s hs), hsupp⟩).trans (le_max_left _ _)
      · rw [hFdef]; simp only; rw [image_eq_zero_of_notMem_tsupport hsupp, norm_zero]
        exact le_max_right _ _
    · have hsupp : Φ x' s ∉ tsupport f := fun h ↦ hsR ⟨le_of_lt hs, (hΦsupp x' s h).2⟩
      rw [hFdef]; simp only; rw [image_eq_zero_of_notMem_tsupport hsupp]
  have hF'meas : ∀ x', AEStronglyMeasurable (F' x') (volume.restrict (Ioi 0)) := fun x' ↦
    ((hfderiv_cont.comp (hΦcont x').continuousOn fun s hs ↦ hΦmem x' s hs).clm_comp
      continuousOn_const).aestronglyMeasurable measurableSet_Ioi
  have hF'int : ∀ x', Integrable (F' x') (volume.restrict (Ioi 0)) := fun x' ↦
    hbound_int.mono' (hF'meas x')
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦ hF'bound x' s hs)
  -- differentiation under the integral sign
  have hHderiv : ∀ x', HasFDerivAt H (∫ s in Ioi (0 : ℝ), F' x' s) x' := fun x' ↦ by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (F := F) (F' := F')
      (bound := bound) (x₀ := x') univ_mem (Eventually.of_forall hFmeas) (hFint x') (hF'meas x')
      ?_ hbound_int ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun s hs x _ ↦ hF'bound x s hs
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun s hs x _ ↦ hF'deriv x s hs
  have hHfderiv : ∀ x', fderiv ℝ H x' = ∫ s in Ioi (0 : ℝ), F' x' s := fun x' ↦
    (hHderiv x').fderiv
  -- the support of `H`
  have hHsupp : ∀ x', R₀ < ‖x'‖ → H x' = 0 := fun x' hx' ↦ by
    have : F x' = 0 := funext fun s ↦
      image_eq_zero_of_notMem_tsupport (f := f) fun h ↦ (hΦsupp x' s h).1.not_gt hx'
    rw [hHdef]; simp only; rw [this]; simp
  have hHc : HasCompactSupport H := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R₀)
      fun x' hx' ↦ ?_
    by_contra h
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at h
    exact hx' (hHsupp x' h)
  -- the partial derivative of `H` and its integrability
  have hHderiv_apply : ∀ x', fderiv ℝ H x' (EuclideanSpace.single i 1)
      = ∫ s in Ioi (0 : ℝ), F' x' s (EuclideanSpace.single i 1) := fun x' ↦ by
    rw [hHfderiv, ContinuousLinearMap.integral_apply (hF'int x')]
  have hHderiv_bound : ∀ x', ‖fderiv ℝ H x' (EuclideanSpace.single i 1)‖
      ≤ ∫ s in Ioi (0 : ℝ), bound s := fun x' ↦ by
    rw [hHderiv_apply]
    refine norm_integral_le_of_norm_le hbound_int
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦ ?_)
    calc ‖F' x' s (EuclideanSpace.single i 1)‖
        ≤ ‖F' x' s‖ * ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin d))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ bound s := by rw [PiLp.norm_single, norm_one, mul_one]; exact hF'bound x' s hs
  have hHderiv_int : Integrable fun x' ↦ fderiv ℝ H x' (EuclideanSpace.single i 1) := by
    have hK : IsCompact (tsupport fun x' ↦ fderiv ℝ H x' (EuclideanSpace.single i 1)) :=
      HasCompactSupport.fderiv_apply ℝ hHc _
    refine (IntegrableOn.of_bound hK.measure_lt_top
      (measurable_fderiv_apply_const ℝ H _).aestronglyMeasurable _
      (ae_of_all _ hHderiv_bound)).integrable_of_forall_notMem_eq_zero fun x' hx' ↦
      image_eq_zero_of_notMem_tsupport (f := fun x' ↦ fderiv ℝ H x' (EuclideanSpace.single i 1))
        hx'
  have hHzero : ∫ x', fderiv ℝ H x' (EuclideanSpace.single i 1) = 0 :=
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (fun x' ↦ (hHderiv x').differentiableAt)
      hHc hHderiv_int
  -- the partial derivative of `H`, computed
  have hA_int : ∀ x' (w : EuclideanSpace ℝ (Fin (d + 1))),
      Integrable (fun s ↦ fderiv ℝ f (Φ x' s) w) (volume.restrict (Ioi 0)) := fun x' w ↦ by
    refine (hbound₀_int.mul_const ‖w‖).mono' ?_
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦ ?_)
    · exact ((hfderiv_cont.comp (hΦcont x').continuousOn fun s hs ↦ hΦmem x' s hs).clm_apply
        continuousOn_const).aestronglyMeasurable measurableSet_Ioi
    · exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hbound₀ x' s hs) (norm_nonneg w))
  have hsplit : ∀ x', fderiv ℝ H x' (EuclideanSpace.single i 1)
      = (∫ s in Ioi (0 : ℝ), fderiv ℝ f (Φ x' s) (EuclideanSpace.single i.castSucc 1))
        + fderiv ℝ g x' (EuclideanSpace.single i 1)
          * ∫ s in Ioi (0 : ℝ), fderiv ℝ f (Φ x' s) (EuclideanSpace.single (Fin.last d) 1) :=
    fun x' ↦ by
      rw [hHderiv_apply, ← integral_const_mul,
        ← integral_add (hA_int x' _) ((hA_int x' _).const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
      simp only
      rw [hF'def]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hDΦdef]
      simp only
      rw [snocLast_add_fderiv_apply_single, map_add, map_smul, smul_eq_mul]
  -- the two inner integrals, straightened back
  have hinner_i : ∀ x',
      ∫ s in Ioi (0 : ℝ), fderiv ℝ f (Φ x' s) (EuclideanSpace.single i.castSucc 1)
        = ∫ t in Ioi (g x'), fderiv ℝ f (snocLast x' t) (EuclideanSpace.single i.castSucc 1) :=
    fun x' ↦ integral_Ioi_comp_add_left
      (fun t ↦ fderiv ℝ f (snocLast x' t) (EuclideanSpace.single i.castSucc 1)) (g x')
  have hinner_N : ∀ x',
      ∫ s in Ioi (0 : ℝ), fderiv ℝ f (Φ x' s) (EuclideanSpace.single (Fin.last d) 1)
        = -f (snocLast x' (g x')) := fun x' ↦ by
    rw [integral_Ioi_comp_add_left
      (fun t ↦ fderiv ℝ f (snocLast x' t) (EuclideanSpace.single (Fin.last d) 1)) (g x')]
    exact integral_Ioi_fderiv_last_eq hgc hfc hf₀ hf₁ hM x'
  -- the boundary term is continuous with compact support
  have hD_cont : Continuous fun x' ↦
      fderiv ℝ g x' (EuclideanSpace.single i 1) * f (snocLast x' (g x')) := by
    refine ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      (hf₀.comp_continuous (continuous_snocLast_graph hgc) fun x' ↦ ?_)
    exact (snocLast_mem_closure_epigraph hgc x' _).2 le_rfl
  have hD_int : Integrable fun x' ↦
      fderiv ℝ g x' (EuclideanSpace.single i 1) * f (snocLast x' (g x')) :=
    hD_cont.integrable_of_hasCompactSupport
      (hasCompactSupport_comp_snocLast_graph hfc).mul_left
  -- assembling
  have key : ∀ x',
      (∫ t in Ioi (g x'), fderiv ℝ f (snocLast x' t) (EuclideanSpace.single i.castSucc 1))
        = fderiv ℝ H x' (EuclideanSpace.single i 1)
          + fderiv ℝ g x' (EuclideanSpace.single i 1) * f (snocLast x' (g x')) := fun x' ↦ by
    rw [hsplit, hinner_i, hinner_N]; ring
  rw [integral_epigraph_eq hgc (integrableOn_fderiv_apply_epigraph hgc hfc hf₁ _)]
  simp_rw [key]
  rw [integral_add hHderiv_int hD_int, hHzero, zero_add]
  exact integral_congr_ae (Eventually.of_forall fun x' ↦ mul_comm _ _)

/-! ### The divergence theorem on an epigraph -/

/-- The inner product with `(w, −1)`, in coordinates. -/
theorem inner_snocLast_neg_one (v : EuclideanSpace ℝ (Fin (d + 1)))
    (w : EuclideanSpace ℝ (Fin d)) :
    ⟪v, snocLast w (-1)⟫_ℝ = ∑ i : Fin d, v i.castSucc * w i + -v (Fin.last d) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_castSucc,
    snocLast_apply_castSucc, snocLast_apply_last, neg_mul, one_mul, mul_comm]

/-- **The divergence theorem on an epigraph**: for `ContDiff ℝ 1 g` and a field `F` of class
`C¹(Ω̄)` with compact support on `Ω = {y : y_N > g y'}`,
`∫_Ω div F = ∫ ⟪F (x', g x'), (∇g x', −1)⟫ dx'`. The right-hand side is `∫_{∂Ω} ⟪F, ν⟫ dσ` for
the graph measure with density `√(1 + |∇g|²)` and the outward normal `(∇g, −1)/√(1 + |∇g|²)`
of `Boundary/GraphMeasure.lean`: the two square roots cancel. Sum of
`integral_fderiv_castSucc_epigraph` over the first `d` coordinate functions and
`integral_fderiv_last_epigraph` for the last one. -/
theorem integral_div_epigraph (hg : ContDiff ℝ 1 g)
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hFc : HasCompactSupport F) (hF₀ : ContinuousOn F (closure (epigraph g)))
    (hF₁ : ContDiffOnClosure ℝ 1 F (epigraph g)) :
    ∫ y in epigraph g, div F y
      = ∫ x', ⟪F (snocLast x' (g x')), snocLast (gradient g x') (-1)⟫_ℝ := by
  have hgc : Continuous g := hg.continuous
  have hopen : IsOpen (epigraph g) := isOpen_epigraph hgc
  -- the coordinate functions are of class `C¹(Ω̄)` with compact support
  have hcoord : ∀ j : Fin (d + 1), HasCompactSupport (fun y ↦ F y j)
      ∧ ContinuousOn (fun y ↦ F y j) (closure (epigraph g))
      ∧ ContDiffOnClosure ℝ 1 (fun y ↦ F y j) (epigraph g) := fun j ↦ by
    refine ⟨?_, (EuclideanSpace.proj j).continuous.comp_continuousOn hF₀,
      hF₁.continuousLinearMap_comp hopen (EuclideanSpace.proj j)⟩
    exact hFc.comp_left (g := fun v : EuclideanSpace ℝ (Fin (d + 1)) ↦ v j) rfl
  have hdiv : ∀ y ∈ epigraph g,
      div F y = ∑ j, fderiv ℝ (fun y ↦ F y j) y (EuclideanSpace.single j 1) := fun y hy ↦ by
    have hdiff : DifferentiableAt ℝ F y :=
      (hF₁.1.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hy)
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h := ((EuclideanSpace.proj j).hasFDerivAt.comp y hdiff.hasFDerivAt).fderiv
    rw [show (fun y ↦ F y j) = (EuclideanSpace.proj j) ∘ F from rfl, h]
    rfl
  rw [setIntegral_congr_fun hopen.measurableSet hdiv,
    integral_finsetSum _ fun j _ ↦ integrableOn_fderiv_apply_epigraph hgc (hcoord j).1
      (hcoord j).2.2 _,
    Fin.sum_univ_castSucc]
  simp_rw [fun i : Fin d ↦ integral_fderiv_castSucc_epigraph hg (hcoord i.castSucc).1
    (hcoord i.castSucc).2.1 (hcoord i.castSucc).2.2 i,
    integral_fderiv_last_epigraph hg (hcoord _).1 (hcoord _).2.1 (hcoord _).2.2]
  -- the boundary terms are continuous with compact support
  have hgraph : ∀ j, Continuous fun x' ↦ F (snocLast x' (g x')) j := fun j ↦
    (EuclideanSpace.proj j).continuous.comp (hF₀.comp_continuous (continuous_snocLast_graph hgc)
      fun x' ↦ (snocLast_mem_closure_epigraph hgc x' _).2 le_rfl)
  have hgraphc : ∀ j, HasCompactSupport fun x' ↦ F (snocLast x' (g x')) j := fun j ↦
    (hasCompactSupport_comp_snocLast_graph hFc).comp_left
      (g := fun v : EuclideanSpace ℝ (Fin (d + 1)) ↦ v j) rfl
  have hint_i : ∀ i : Fin d, Integrable fun x' ↦
      F (snocLast x' (g x')) i.castSucc * fderiv ℝ g x' (EuclideanSpace.single i 1) := fun i ↦
    ((hgraph _).mul ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport (hgraphc _).mul_right
  have hint_N : Integrable fun x' ↦ F (snocLast x' (g x')) (Fin.last d) :=
    (hgraph _).integrable_of_hasCompactSupport (hgraphc _)
  have hrhs : ∫ x', ⟪F (snocLast x' (g x')), snocLast (gradient g x') (-1)⟫_ℝ
      = ∫ x', (∑ i : Fin d, F (snocLast x' (g x')) i.castSucc
          * fderiv ℝ g x' (EuclideanSpace.single i 1)) + -F (snocLast x' (g x')) (Fin.last d) :=
    integral_congr_ae (Eventually.of_forall fun x' ↦ by
      simp only [inner_snocLast_neg_one, gradient_apply])
  rw [hrhs, integral_add (integrable_finsetSum _ fun i _ ↦ hint_i i) hint_N.fun_neg,
    integral_finsetSum _ fun i _ ↦ hint_i i, integral_neg]

/-! ### The rotated epigraph, and a graph chart of a domain -/

/-- **The divergence theorem on a rotated epigraph**: for a rigid motion `T`, `ContDiff ℝ 1 g` and
a field `F` of class `C¹(Ω̄)` with compact support on `Ω = T ⁻¹' epigraph g`,
`∫_Ω div F = ∫ ⟪F (T⁻¹ (x', g x')), T.linear⁻¹ (∇g x', −1)⟫ dx'`. Conjugate by `T`: the field
`G = T.linear ∘ F ∘ T⁻¹` is of class `C¹` on the closure of the epigraph with compact support,
`div G ∘ T = div F` (`div_comp_affineIsometryEquiv`), `T` preserves Lebesgue measure, and
`integral_div_epigraph` applies to `G`. -/
theorem integral_div_graphEpigraph
    (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hg : ContDiff ℝ 1 g)
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hFc : HasCompactSupport F) (hF₀ : ContinuousOn F (closure (T ⁻¹' epigraph g)))
    (hF₁ : ContDiffOnClosure ℝ 1 F (T ⁻¹' epigraph g)) :
    ∫ y in T ⁻¹' epigraph g, div F y
      = ∫ x', ⟪F (T.symm (snocLast x' (g x'))),
          T.linearIsometryEquiv.symm (snocLast (gradient g x') (-1))⟫_ℝ := by
  have hgc : Continuous g := hg.continuous
  have hopen : IsOpen (T ⁻¹' epigraph g) := (isOpen_epigraph hgc).preimage T.continuous
  set G : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) :=
    fun z ↦ T.linearIsometryEquiv (F (T.symm z)) with hGdef
  have hcl : closure (T ⁻¹' epigraph g) = T ⁻¹' closure (epigraph g) := by
    have := T.toHomeomorph.preimage_closure (epigraph g)
    rwa [AffineIsometryEquiv.coe_toHomeomorph, eq_comm] at this
  have hmaps : MapsTo T.symm (closure (epigraph g)) (closure (T ⁻¹' epigraph g)) :=
    fun z hz ↦ by rw [hcl]; simpa using hz
  have hGc : HasCompactSupport G := by
    have h1 : HasCompactSupport fun y ↦ T.linearIsometryEquiv (F y) :=
      hFc.comp_left (map_zero _)
    exact h1.comp_isClosedEmbedding T.symm.toHomeomorph.isClosedEmbedding
  have hG₀ : ContinuousOn G (closure (epigraph g)) :=
    T.linearIsometryEquiv.continuous.comp_continuousOn
      (hF₀.comp T.symm.continuous.continuousOn hmaps)
  have hG₁ : ContDiffOnClosure ℝ 1 G (epigraph g) := by
    have h1 := hF₁.comp_affineIsometryEquiv hopen T.symm
    have h2 : T.symm ⁻¹' (T ⁻¹' epigraph g) = epigraph g := by ext z; simp
    rw [h2] at h1
    exact h1.continuousLinearMap_comp (isOpen_epigraph hgc)
      (T.linearIsometryEquiv.toContinuousLinearEquiv :
        EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  have hdiv : ∀ y ∈ T ⁻¹' epigraph g, div F y = div G (T y) := fun y hy ↦ by
    have hdiff : DifferentiableAt ℝ F y :=
      (hF₁.1.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hy)
    rw [hGdef, div_comp_affineIsometryEquiv T (by simpa using hdiff), T.symm_apply_apply]
  rw [setIntegral_congr_fun hopen.measurableSet hdiv, T.setIntegral_comp (fun z ↦ div G z),
    integral_div_epigraph hg hGc hG₀ hG₁]
  refine integral_congr_ae (Eventually.of_forall fun x' ↦ ?_)
  simp only [hGdef]
  rw [LinearIsometryEquiv.inner_map_eq_flip]

end EuclideanSpace

/-- **The divergence theorem on a graph chart of a domain**: for an open `Ω ⊆ ℝ^{d+1}`, a graph
chart `(T, g)` at `(x₀, r)` — `ContDiff ℝ 1 g` and
`Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' epigraph g`, the clause of `IsBoundaryGraphAt` — and a field
`F` of class `C¹(Ω̄)` with `tsupport F ⊆ B(x₀, r)`,
`∫_Ω div F = ∫ ⟪F (T⁻¹ (x', g x')), T.linear⁻¹ (∇g x', −1)⟫ dx'`. The right-hand side is read in
`Boundary/ContDiffDomain.lean` as
`∫ ⟪F, graphNormal T g⟫ d(graphMeasure T g (graphDomain T g x₀ r))`; it vanishes where `F` does,
so no localization appears here. `div F` vanishes off the ball, so
both `∫_Ω` and the integral over the global rotated epigraph reduce to `Ω ∩ B(x₀, r)`; `F` is of
class `C¹` on the closure of the rotated epigraph by
`ContDiffOnClosure.congr_set_of_tsupport_subset`, and `integral_div_graphEpigraph` applies. -/
theorem IsBoundaryGraphAt.integral_div_eq_of_tsupport_subset {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsOpen Ω) {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
    (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hg : ContDiff ℝ 1 g)
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hFs : tsupport F ⊆ Metric.ball x₀ r) (hF₀ : ContinuousOn F (closure Ω))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ y in Ω, EuclideanSpace.div F y
      = ∫ x', ⟪F (T.symm (EuclideanSpace.snocLast x' (g x'))),
          T.linearIsometryEquiv.symm (EuclideanSpace.snocLast (gradient g x') (-1))⟫_ℝ := by
  have hopen : IsOpen (T ⁻¹' EuclideanSpace.epigraph g) :=
    (EuclideanSpace.isOpen_epigraph hg.continuous).preimage T.continuous
  have hFc : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ r)
      ((subset_tsupport F).trans (hFs.trans Metric.ball_subset_closedBall))
  have hsV : Ω ∩ Metric.ball x₀ r = T ⁻¹' EuclideanSpace.epigraph g ∩ Metric.ball x₀ r := by
    rw [h, inter_comm]
  obtain ⟨hF₀', hF₁'⟩ := hF₁.congr_set_of_tsupport_subset hΩ Metric.isOpen_ball hsV hFs hF₀
  have hdiv0 : ∀ y, y ∉ Metric.ball x₀ r → EuclideanSpace.div F y = 0 := fun y hy ↦ by
    have : fderiv ℝ F y = 0 := fderiv_eq_zero_of_notMem_tsupport fun h ↦ hy (hFs h)
    simp [EuclideanSpace.div, this]
  have e1 : ∫ y in Ω, EuclideanSpace.div F y
      = ∫ y in Ω ∩ Metric.ball x₀ r, EuclideanSpace.div F y :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet inter_subset_left
      fun y hy ↦ hdiv0 y fun h' ↦ hy.2 ⟨hy.1, h'⟩
  have e2 : ∫ y in T ⁻¹' EuclideanSpace.epigraph g, EuclideanSpace.div F y
      = ∫ y in T ⁻¹' EuclideanSpace.epigraph g ∩ Metric.ball x₀ r, EuclideanSpace.div F y :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hopen.measurableSet inter_subset_left
      fun y hy ↦ hdiv0 y fun h' ↦ hy.2 ⟨hy.1, h'⟩
  rw [e1, hsV, ← e2]
  exact EuclideanSpace.integral_div_graphEpigraph T hg hFc hF₀' hF₁'

end
