import Numlib.Analysis.Sobolev.Boundary.Divergence
import Numlib.Analysis.Sobolev.Boundary.GraphMeasure
import Numlib.Analysis.Sobolev.Boundary.Trace
import Numlib.Analysis.Sobolev.Compactness

/-!
# The divergence theorem, the boundary data and the trace of a bounded `C¹` domain

The assembly on a bounded `C¹` domain (decisions B1–B4 and B7 of
`notes/boundary/planning-brief.md`): from the local divergence theorem on a graph chart
(`Boundary/Divergence.lean`), the surface measure and outward normal with their chart
characterizations (`Boundary/GraphMeasure.lean`) and the partition of unity of an atlas, the
divergence theorem

  `∫_Ω div F = ∫ ⟪F, ν⟫ dσ`  for `F ∈ C¹(Ω̄)`  (`IsContDiffDomain.integral_div_eq`),

hence the boundary data `IsContDiffDomain.boundaryData : BoundaryData Ω`; a transversal field
(`IsContDiffDomain.hasTransversalField`); with the density theorems of `Boundary/Density.lean`
the trace family `IsContDiffDomain.traceFamily` of `Boundary/Trace.lean`, and with Rellich's
theorem (`Numlib/Analysis/Sobolev/Compactness.lean`) the compactness of the trace for `1 < p`.
This is the module the `C¹`-domain consumers of the Atkinson–Han and Brezis surfaces import
(Theorem 7.3.10, Proposition 7.6.1, Examples 11.1.2–11.3.11 on a `C¹` domain, Brezis Example 4
of §9.5 and the Neumann boundary condition of Theorem 9.26).

**The assembly.** For a graph atlas `a` of `Ω` with its partition of unity `θ₀ + ∑ θᵢ = 1`,
`F = θ₀ F + ∑ θᵢ F` on `Ω` and the divergence is additive on differentiable fields
(`EuclideanSpace.div_finset_sum`). The interior piece `θ₀ F` vanishes near `∂Ω`; the compact set
`tsupport θ₀ ∩ closure Ω ⊆ Ω` carries a smooth cut-off `χ` supported in `Ω`, and
`H := (χ θ₀) F` is a `C¹` field on all of `ℝ^N` with compact support, equal to `θ₀ F` on `Ω`
and with `div H = 0` off `Ω`, so `∫_Ω div (θ₀ F) = ∫ div H = 0`
(`EuclideanSpace.integral_div_smul_eq_zero_of_disjoint_tsupport_frontier`). Each chart piece
`θᵢ F` is supported in its chart ball, so the local theorem
`IsBoundaryGraphAt.integral_div_eq_of_tsupport_subset` applies; read through
`EuclideanSpace.integral_graphMeasure` it is `∫_Ω div (θᵢ F) = ∫ ⟪θᵢ F, graphNormal⟫ dσᵢ`
(`IsBoundaryGraphAt.integral_div_eq_graphMeasure`: the density `√(1 + |∇g|²)` of the measure and
the normalization of the normal cancel), and the local measure `σᵢ` is carried by
`∂Ω ∩ B(xᵢ, rᵢ)`, where the chart normal is the normal of the atlas
(`GraphAtlas.integral_div_smul_θ_eq`). The atlas measure `σ = ∑ θᵢ σᵢ` recombines the pieces
(`GraphAtlas.integral_measure_eq_sum`). The theorem is proved for every atlas
(`GraphAtlas.integral_div_eq`) and specialized to the chosen one. Integrability of the pieces:
the derivative of a `C¹(Ω̄)` field is bounded on the bounded `Ω`
(`ContDiffOnClosure.exists_norm_fderiv_le_of_isBounded`), so its divergence is integrable there
(`ContDiffOnClosure.integrableOn_div`).

**The transversal field** is `w = c ∑ᵢ θᵢ Tᵢ⁻¹(−e_N)`, the partition of unity applied to the
downward directions of the charts: in the frame `Tᵢ` the outward normal is
`(∇gᵢ, −1)/√(1 + |∇gᵢ|²)`, so `⟪Tᵢ⁻¹(−e_N), ν⟫ = 1/√(1 + |∇gᵢ|²) ≥ 1/c` on `∂Ω ∩ B(xᵢ, rᵢ)` for
`c` bounding the densities over the (bounded) parameter domains, and `⟪w, ν⟫ ≥ ∑ θᵢ = 1` on
`∂Ω` (`IsContDiffDomain.exists_transversalField`).

**Regularity.** The divergence theorem is stated for `F ∈ C¹(Ω̄)` — `ContinuousOn F (closure Ω)`
and `ContDiffOnClosure ℝ 1 F Ω` (`Numlib/Analysis/Calculus/ContDiffOnClosure.lean`), the
regularity of the books' Green formulas; `ContDiff ℝ 1 F` is the corollary
`BoundaryData.integral_div_eq_of_contDiff`. No Piola identity, no area formula, no Hausdorff
measure enters (decision B4).

## Main statements

* `IsBoundaryGraphAt.integral_div_eq_graphMeasure`: the local divergence theorem in
  surface-measure form;
* `GraphAtlas.integral_div_eq`, `IsContDiffDomain.integral_div_eq`: the divergence theorem on a
  bounded `C¹` domain;
* `IsContDiffDomain.boundaryData`, `IsContDiffChartDomain.boundaryData`: the boundary data;
* `IsContDiffDomain.exists_transversalField`, `IsContDiffDomain.hasTransversalField`: the
  transversal field;
* `IsContDiffDomain.traceFamily`, `IsContDiffDomain.traceL`, `IsContDiffDomain.green`: the trace
  theorem and Green's formula on a bounded `C¹` domain;
* `IsContDiffDomain.isCompactOperator_traceL`: compactness of the trace for `1 < p < ∞`.

## Not formalized here

**Korn's second inequality and the mixed displacement–traction problem of linear elasticity**
(Nečas–Hlaváček; Duvaut–Lions; Atkinson–Han §8.5, the `V`-ellipticity remark after (8.5.15)).
This was planned as a module `Boundary/KornSecond.lean` of this directory and is recorded here
instead, the trace family above being everything it was waiting for. Three statements, in the
order they were planned: the first is a definition and is cheap, the second is the deep one, and
the third follows from it.

* `[H¹(Ω)]^N` as a Hilbert space, and the mixed space `V` of Atkinson–Han (8.5.13). The type is
  `PiLp 2 fun _ : Fin N ↦ SobolevEuclidean N 1 2 Ω`, the `ℓ²` product of `N` copies of `H¹(Ω)`
  with `‖v‖² = ∑ᵢ ‖vᵢ‖²`; over it the partial derivatives `v ↦ ∂ⱼvᵢ` and the linearized strain
  `ε(v)ᵢⱼ = ½ (∂ⱼvᵢ + ∂ᵢvⱼ)` as continuous linear maps into `L²(Ω)` — the analogues of
  `SobolevEuclideanZeroVec.partialL` and `.strainL` of `Numlib/Analysis/Sobolev/Korn.lean`, of
  which they are the extensions off the subspace `[H¹₀(Ω)]^N`; the trace taken componentwise,
  `v ↦ fun i ↦ 𝒯.traceL 2 _ (v i)` for `𝒯 := hΩ.traceFamily hb`; and the subspace
  `V = {v | ∀ i, 𝒯.traceL 2 _ (v i) = 0 σ-a.e. on Γ_D}` of the fields whose trace vanishes on a
  measurable `Γ_D ⊆ ∂Ω`, closed because the trace is continuous. Nothing in this first item is
  missing; it was never written because the two theorems below are.
* **Korn's second inequality**: on a bounded `C¹` domain `Ω` there is a `C` with
  `‖v‖²_{H¹} ≤ C (‖v‖²_{L²} + ‖ε(v)‖²_{L²})` for every `v ∈ [H¹(Ω)]^N`. On `[H¹₀(Ω)]^N` the
  sharper inequality without the `L²` term is `SobolevEuclideanZeroVec.korn_first` and needs no
  regularity of `Ω` at all; on `[H¹(Ω)]^N` the boundary terms of its two integrations by parts do
  not vanish, and the standard proof (Duvaut–Lions, Nečas) runs the other way. It writes
  `∂ⱼ∂ₖvᵢ = ∂ⱼ εᵢₖ + ∂ₖ εᵢⱼ − ∂ᵢ εⱼₖ` in `H^{−1}(Ω)` and invokes **Lions's lemma**: on a bounded
  Lipschitz (a fortiori `C¹`) domain, a distribution `f` with `f ∈ H^{−1}(Ω)` and
  `∇f ∈ H^{−1}(Ω)^N` lies in `L²(Ω)`, with `‖f‖_{L²} ≤ C (‖f‖_{H^{−1}} + ‖∇f‖_{H^{−1}})`.
  Lions's lemma is itself proved through a right inverse of the divergence (Bogovskiĭ) or through
  the Nečas inequality `‖f‖_{L²} ≤ C ‖∇f‖_{H^{−1}}` on `L²_0`, and neither is in Mathlib or in
  `Numlib/`; the alternatives — Kondratiev–Oleĭnik's integral representation for star-shaped
  domains, or the Fourier proof on `ℝ^N` combined with a `C¹` extension operator commuting with
  `ε`, which does not exist — are no cheaper. What exists towards it is `H^{−1}(Ω)` as the dual
  of `H¹₀(Ω)` with its norm (`SobolevEuclideanZero.exists_dual_repr` of
  `Numlib/Analysis/Sobolev/Zero.lean`). Research-scale, 2000+ lines. **The trace is not what is
  missing**: with `IsContDiffDomain.traceFamily` every statement of this section is statable, and
  the boundary round of 2026-09-21 confirmed it.
* **`V`-ellipticity of the elasticity form**: for `Ω` bounded, `C¹` and connected and a
  measurable `Γ_D ⊆ ∂Ω` with `σ(Γ_D) > 0`, there is a `C` with `‖v‖²_{H¹} ≤ C ‖ε(v)‖²_{L²}` for
  every `v ∈ V` — the missing step of Atkinson–Han Theorem 8.5.1. The route from Korn's second
  inequality is a contradiction argument: a sequence `vₙ ∈ V` with `‖vₙ‖ = 1` and `ε(vₙ) → 0`
  has, by Rellich on the extension domain (`SobolevEuclidean.isCompactEmbedding_fnL`), a
  subsequence converging in `L²`, hence by Korn's second inequality in `H¹`, to some `v ∈ V` with
  `‖v‖ = 1` and `ε(v) = 0`; and the kernel of `ε` on a connected domain is the infinitesimal
  rigid motions `x ↦ a + W x` with `W` skew, because the same identity
  `∂ⱼ∂ₖvᵢ = ∂ⱼ εᵢₖ + ∂ₖ εᵢⱼ − ∂ᵢ εⱼₖ` makes every second derivative vanish and
  `Numlib/Analysis/Sobolev/DenyLions.lean`'s "`|u|_{2,p} = 0` forces a polynomial of degree
  `≤ 1`" then makes `v` affine. **The last step is the non-obvious one, and is the part of this
  route worth keeping.** It is *not* enough to say "an affine map vanishing on a set of positive
  surface measure is zero": the zero set of a general affine map is a hyperplane, of dimension
  `N − 1`, and a `C¹` boundary may perfectly well contain a flat face of positive `σ`-measure
  inside one. What makes the step true is that `W` is **skew**. The zero set of a nonzero
  infinitesimal rigid motion `a + W x` is an affine subspace of *even codimension* `≥ 2` — for
  `N = 2` a point and for `N = 3` a line, which is the classical form of the argument — and an
  affine subspace of dimension `≤ N − 2` is `σ`-null on a `C¹` hypersurface. That nullity is the
  only piece of the step needing work: by `IsContDiffDomain.boundaryMeasure_restrict_ball` the
  surface measure is a graph measure in each chart, and the preimage of an affine subspace of
  dimension `≤ N − 2` under a graph parametrization over `ℝ^{N−1}` is Lebesgue-null — about 100
  lines. The whole of this third statement is about 400 lines once Korn's second inequality
  exists; it is blocked on that alone.

The consumer is `NumlibSurface/AtkinsonHan/Chapter08/Section05.lean`, whose module doc carries
the same record from the elasticity side.

## References

Atkinson–Han, *Theoretical Numerical Analysis*, §7.3 (Theorem 7.3.10) and §7.6; Grisvard,
*Elliptic Problems in Nonsmooth Domains*, Theorems 1.5.1.3 and 1.5.3.1; Nečas, *Direct Methods
in the Theory of Elliptic Equations*, Ch. 2 §4; [brezis2011functional] §9.5 Example 4 and
Comments on chapter 9.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace NNReal Topology

noncomputable section

/-! ### The divergence of a sum, its measurability and integrability -/

/-! ### The compactly supported piece: `∫_Ω div (θ F) = 0` for `θ` vanishing near `∂Ω` -/

/-- **The interior piece of the divergence theorem**: for `θ` of class `C¹` with
`Disjoint (tsupport θ) (frontier Ω)` and `F` of class `C¹` on the bounded open `Ω`,
`∫_Ω div (θ F) = 0`. The compact `K := tsupport θ ∩ closure Ω` lies in `Ω`
(`inter_closure_subset_of_disjoint_frontier`); with a smooth cut-off `χ` equal to `1` on `K` and
supported in `Ω` (`IsCompact.exists_contDiff_eqOn_one`), the field `H := (χ θ) F` is `C¹` on all
of `ℝ^N` with compact support, equals `θ F` on `Ω`, and has `div H = 0` off `Ω`, so
`∫_Ω div (θ F) = ∫ div H = 0` (`EuclideanSpace.integral_div_eq_zero_of_hasCompactSupport`). -/
theorem EuclideanSpace.integral_div_smul_eq_zero_of_disjoint_tsupport_frontier {N : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin N))} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {θ : EuclideanSpace ℝ (Fin N) → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hθΩ : Disjoint (tsupport θ) (frontier Ω))
    {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} (hF : ContDiffOn ℝ 1 F Ω) :
    ∫ y in Ω, EuclideanSpace.div (fun y ↦ θ y • F y) y = 0 := by
  have hK : IsCompact (tsupport θ ∩ closure Ω) :=
    (isClosed_tsupport θ).isCompact_inter_closure_of_isBounded hb
  have hKΩ : tsupport θ ∩ closure Ω ⊆ Ω := inter_closure_subset_of_disjoint_frontier hΩ hθΩ
  obtain ⟨χ, hχ, hχ1, hχs, -⟩ := hK.exists_contDiff_eqOn_one hΩ hKΩ
  set H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
    fun y ↦ (χ y * θ y) • F y with hHdef
  have hHeq : ∀ y ∈ Ω, H y = θ y • F y := fun y hy ↦ by
    by_cases hyθ : y ∈ tsupport θ
    · simp [hHdef, hχ1 ⟨hyθ, subset_closure hy⟩]
    · simp [hHdef, image_eq_zero_of_notMem_tsupport hyθ]
  have hHs : tsupport H ⊆ tsupport χ :=
    (tsupport_smul_subset_left _ _).trans tsupport_mul_subset_left
  have hHd : ContDiff ℝ 1 H := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Ω
    · exact ((hχ.of_le (by simp)).contDiffAt.mul hθ.contDiffAt).smul
        (hF.contDiffAt (hΩ.mem_nhds hy))
    · have hyχ : y ∉ tsupport χ := fun h ↦ hy (hχs h)
      have : H =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hyχ] with z hz
        simp [hHdef, image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq this
  have hHc : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact hb.isCompact_closure
      ((subset_tsupport H).trans (hHs.trans (hχs.trans subset_closure)))
  have hdiv0 : ∀ y, y ∉ Ω → EuclideanSpace.div H y = 0 := fun y hy ↦ by
    have : fderiv ℝ H y = 0 :=
      fderiv_of_notMem_tsupport ℝ fun h ↦ hy (hχs (hHs h))
    simp [EuclideanSpace.div, this]
  calc ∫ y in Ω, EuclideanSpace.div (fun y ↦ θ y • F y) y
      = ∫ y in Ω, EuclideanSpace.div H y := by
        refine setIntegral_congr_fun hΩ.measurableSet fun y hy ↦ ?_
        have : (fun y ↦ θ y • F y) =ᶠ[𝓝 y] H := by
          filter_upwards [hΩ.mem_nhds hy] with z hz
          exact (hHeq z hz).symm
        simp only [EuclideanSpace.div, this.fderiv_eq]
    _ = ∫ y, EuclideanSpace.div H y :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ hdiv0 y hy
    _ = 0 :=
        EuclideanSpace.integral_div_eq_zero_of_hasCompactSupport (hHd.differentiable one_ne_zero)
          hHc ((hHd.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport
            (hHc.fderiv (𝕜 := ℝ)))

/-! ### The local divergence theorem in surface-measure form -/

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-- **The divergence theorem on a graph chart, in surface-measure form**: for an open
`Ω ⊆ ℝ^{d+1}`, a graph chart `(T, g)` at `(x₀, r)` — `ContDiff ℝ 1 g` and
`Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' epigraph g` — and a field `F` of class `C¹(Ω̄)` with
`tsupport F ⊆ B(x₀, r)`,
`∫_Ω div F = ∫ ⟪F, graphNormal T g⟫ d(graphMeasure T g (graphDomain T g x₀ r))`.
The right-hand side of `IsBoundaryGraphAt.integral_div_eq_of_tsupport_subset` is
`∫ ⟪F (graphParam x'), T.linear⁻¹ (∇g x', −1)⟫ dx'`; under `integral_graphMeasure` the surface
integral is `∫_{graphDomain} √(1 + |∇g|²) ⟪F (graphParam x'), graphNormal (graphParam x')⟫ dx'`
and the density cancels the normalization of `graphNormal`; the integrand vanishes off the
parameter domain since `F` vanishes off the ball. -/
theorem IsBoundaryGraphAt.integral_div_eq_graphMeasure {g : 𝔼' → ℝ} {Ω : Set 𝔼} (hΩ : IsOpen Ω)
    {x₀ : 𝔼} {r : ℝ} (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) (hg : ContDiff ℝ 1 g)
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    {F : 𝔼 → 𝔼} (hFs : tsupport F ⊆ Metric.ball x₀ r) (hF₀ : ContinuousOn F (closure Ω))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ y in Ω, EuclideanSpace.div F y
      = ∫ x, ⟪F x, EuclideanSpace.graphNormal T g x⟫_ℝ
          ∂(EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r)) := by
  set μ := EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r) with hμdef
  -- the graph measure is carried by `∂Ω ∩ B ⊆ closure Ω`, where `F` is continuous
  have hμc : ∀ᵐ x ∂μ, x ∈ closure Ω := by
    filter_upwards [EuclideanSpace.ae_mem_image_graphMeasure (T := T) hg.continuous
      (EuclideanSpace.measurableSet_graphDomain hg.continuous x₀ r)] with x hx
    rw [IsBoundaryGraphAt.graphParam_image_graphDomain hg.continuous h] at hx
    exact frontier_subset_closure hx.1
  have hFm : AEStronglyMeasurable F μ := by
    have := hF₀.aestronglyMeasurable (μ := μ) isClosed_closure.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hμc] at this
  have hm : AEStronglyMeasurable (fun x ↦ ⟪F x, EuclideanSpace.graphNormal T g x⟫_ℝ) μ :=
    hFm.inner (EuclideanSpace.continuous_graphNormal hg).aestronglyMeasurable
  rw [hμdef, EuclideanSpace.integral_graphMeasure hg _ hm,
    IsBoundaryGraphAt.integral_div_eq_of_tsupport_subset hΩ T hg h hFs hF₀ hF₁]
  -- the integrand vanishes off the parameter domain
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x' hx' ↦ ?_]
  · refine integral_congr_ae (Eventually.of_forall fun x' ↦ ?_)
    simp only [EuclideanSpace.graphNormal, EuclideanSpace.init_apply_graphParam,
      real_inner_smul_right, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (EuclideanSpace.graphDensity_ne_zero x'), one_mul]
    rfl
  · have : F (EuclideanSpace.graphParam T g x') = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem ↦ hx' (hFs hmem)
    rw [this, inner_zero_left, smul_zero]

/-! ### The divergence theorem for an atlas -/

namespace GraphAtlas

variable {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} (a : GraphAtlas Ω)

/-- **The chart piece of the divergence theorem**: `∫_Ω div (θᵢ F) = ∫ θᵢ ⟪F, ν⟫ dσᵢ` for the
`i`-th chart of an atlas of the open `Ω` and `F ∈ C¹(Ω̄)`. The piece `θᵢ F` is supported in the
chart ball (`IsBoundaryGraphAt.integral_div_eq_graphMeasure`), and the local measure `σᵢ` is
carried by `∂Ω ∩ B(xᵢ, rᵢ)`, where the chart normal is the atlas normal
(`GraphAtlas.normal_eq_graphNormal`). -/
theorem integral_div_smul_θ_eq (hΩ : IsOpen Ω) {F : 𝔼 → 𝔼} (hF₀ : ContinuousOn F (closure Ω))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) (i : Fin a.k) :
    ∫ y in Ω, EuclideanSpace.div (fun y ↦ a.θ i y • F y) y
      = ∫ x, a.θ i x • ⟪F x, a.normal x⟫_ℝ ∂(a.localMeasure i) := by
  have hGs : tsupport (fun y ↦ a.θ i y • F y) ⊆ Metric.ball (a.x i) (a.r i) :=
    (tsupport_smul_subset_left _ _).trans (a.tsupport_θ_subset i)
  have hG₀ : ContinuousOn (fun y ↦ a.θ i y • F y) (closure Ω) :=
    (a.contDiff_θ i).continuous.continuousOn.smul hF₀
  have hG₁ : ContDiffOnClosure ℝ 1 (fun y ↦ a.θ i y • F y) Ω :=
    (((a.contDiff_θ i).of_le (by simp)).contDiffOn.contDiffOnClosure hΩ).smul hΩ hF₁
  rw [IsBoundaryGraphAt.integral_div_eq_graphMeasure hΩ (a.T i) (a.contDiff_g i)
    (a.inter_ball_eq i) hGs hG₀ hG₁, a.localMeasure_eq]
  refine integral_congr_ae ?_
  filter_upwards [EuclideanSpace.ae_mem_image_graphMeasure (T := a.T i) (a.contDiff_g i).continuous
    (EuclideanSpace.measurableSet_graphDomain (a.contDiff_g i).continuous (a.x i) (a.r i))]
    with x hx
  rw [IsBoundaryGraphAt.graphParam_image_graphDomain (a.contDiff_g i).continuous
    (a.inter_ball_eq i)] at hx
  rw [a.normal_eq_graphNormal hx.1 hx.2, real_inner_smul_left, smul_eq_mul]

/-- **The divergence theorem for a graph atlas** of a bounded open `Ω ⊆ ℝ^{d+1}`: for
`F ∈ C¹(Ω̄)`, `∫_Ω div F = ∫ ⟪F, a.normal⟫ ∂a.measure`. The partition of unity splits
`F = θ₀ F + ∑ θᵢ F` on `Ω`; the interior piece integrates to zero
(`EuclideanSpace.integral_div_smul_eq_zero_of_disjoint_tsupport_frontier`), each chart piece is
`∫ θᵢ ⟪F, ν⟫ dσᵢ` (`integral_div_smul_θ_eq`), and the atlas measure recombines them
(`integral_measure_eq_sum`). -/
theorem integral_div_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {F : 𝔼 → 𝔼}
    (hF₀ : ContinuousOn F (closure Ω)) (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ y in Ω, EuclideanSpace.div F y = ∫ x, ⟪F x, a.normal x⟫_ℝ ∂a.measure := by
  have hθ₁ : ∀ i, ContDiffOnClosure ℝ 1 (a.θ i) Ω := fun i ↦
    ((a.contDiff_θ i).of_le (by simp)).contDiffOn.contDiffOnClosure hΩ
  have hθ₀₁ : ContDiffOnClosure ℝ 1 a.θ₀ Ω :=
    (a.contDiff_θ₀.of_le (by simp)).contDiffOn.contDiffOnClosure hΩ
  obtain ⟨G, hGdef⟩ : ∃ G : Fin a.k → 𝔼 → 𝔼, G = fun i y ↦ a.θ i y • F y := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀def⟩ : ∃ G₀ : 𝔼 → 𝔼, G₀ = fun y ↦ a.θ₀ y • F y := ⟨_, rfl⟩
  have hG₁ : ∀ i, ContDiffOnClosure ℝ 1 (G i) Ω := fun i ↦ by
    rw [hGdef]; exact (hθ₁ i).smul hΩ hF₁
  have hG₀₁ : ContDiffOnClosure ℝ 1 G₀ Ω := by
    rw [hG₀def]; exact hθ₀₁.smul hΩ hF₁
  -- pointwise decomposition of `div F` on `Ω`
  have hdiv : ∀ y ∈ Ω, EuclideanSpace.div F y
      = EuclideanSpace.div G₀ y + ∑ i, EuclideanSpace.div (G i) y := fun y hy ↦ by
    have hF' : DifferentiableAt ℝ F y :=
      (hF₁.1.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hy)
    have hd : ∀ i, DifferentiableAt ℝ (G i) y := fun i ↦ by
      rw [hGdef]; exact ((a.contDiff_θ i).differentiable (by simp) y).smul hF'
    have hd₀ : DifferentiableAt ℝ G₀ y := by
      rw [hG₀def]; exact (a.contDiff_θ₀.differentiable (by simp) y).smul hF'
    have hFeq : F = G₀ + fun y ↦ ∑ i, G i y := by
      funext z
      simp only [hGdef, hG₀def, Pi.add_apply, ← Finset.sum_smul, ← add_smul, a.θ₀_add_sum_θ,
        one_smul]
    conv_lhs => rw [hFeq]
    rw [EuclideanSpace.div_add hd₀ (DifferentiableAt.fun_sum fun i _ ↦ hd i),
      EuclideanSpace.div_finset_sum _ fun i _ ↦ hd i]
  have hint₀ : IntegrableOn (EuclideanSpace.div G₀) Ω := hG₀₁.integrableOn_div hΩ hb
  have hint : ∀ i, IntegrableOn (EuclideanSpace.div (G i)) Ω := fun i ↦
    (hG₁ i).integrableOn_div hΩ hb
  rw [setIntegral_congr_fun hΩ.measurableSet hdiv,
    integral_add hint₀ (integrable_finsetSum _ fun i _ ↦ hint i),
    integral_finsetSum _ fun i _ ↦ hint i]
  -- the interior piece vanishes
  have h₀ : ∫ y in Ω, EuclideanSpace.div G₀ y = 0 := by
    rw [hG₀def]
    exact EuclideanSpace.integral_div_smul_eq_zero_of_disjoint_tsupport_frontier hΩ hb
      (a.contDiff_θ₀.of_le (by simp)) a.disjoint_tsupport_θ₀ hF₁.1
  -- the chart pieces
  have hpiece : ∀ i, ∫ y in Ω, EuclideanSpace.div (G i) y
      = ∫ x, a.θ i x • ⟪F x, a.normal x⟫_ℝ ∂(a.localMeasure i) := fun i ↦ by
    rw [hGdef]
    exact a.integral_div_smul_θ_eq hΩ hF₀ hF₁ i
  simp_rw [h₀, hpiece, zero_add]
  -- the atlas measure recombines
  have hint' : Integrable (fun x ↦ ⟪F x, a.normal x⟫_ℝ) a.measure :=
    a.integrable_of_continuousOn ((hF₀.mono frontier_subset_closure).inner a.continuousOn_normal)
  exact (a.integral_measure_eq_sum hint').symm

end GraphAtlas

/-! ### The divergence theorem, the boundary data and the transversal field of a `C¹` domain -/

namespace IsContDiffDomain

section Set

variable {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : IsContDiffDomain 1 Ω)
  (hb : Bornology.IsBounded Ω)

/-- **The divergence theorem on a bounded `C¹` domain** (Atkinson–Han §7.6 "Gauss's formula",
Grisvard Theorem 1.5.3.1 for classical fields, [brezis2011functional] §9.5 Example 4): for
`F ∈ C¹(Ω̄)` — `ContinuousOn F (closure Ω)` and `ContDiffOnClosure ℝ 1 F Ω` —
`∫_Ω div F = ∫ ⟪F, ν⟫ dσ` with the surface measure `σ = hΩ.boundaryMeasure hb` and the outward
normal `ν = hΩ.outwardNormal hb` of `Boundary/GraphMeasure.lean`. It is `GraphAtlas.integral_div_eq`
for the chosen atlas. -/
theorem integral_div_eq {F : 𝔼 → 𝔼} (hF₀ : ContinuousOn F (closure Ω))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ x in Ω, EuclideanSpace.div F x
      = ∫ x, ⟪F x, hΩ.outwardNormal hb x⟫_ℝ ∂(hΩ.boundaryMeasure hb) :=
  (hΩ.graphAtlas hb).integral_div_eq hΩ.isOpen hb hF₀ hF₁

/-- The pairing of a chart's downward direction `T.linear⁻¹ (−e_N)` with the chart normal is
`1/√(1 + |∇g|²)`: in the frame `T` the normal is `(∇g, −1)/√(1 + |∇g|²)`. -/
theorem inner_symm_neg_single_last_graphNormal (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) (g : 𝔼' → ℝ) (x : 𝔼) :
    ⟪T.linearIsometryEquiv.symm (-EuclideanSpace.single (Fin.last d) (1 : ℝ)),
        EuclideanSpace.graphNormal T g x⟫_ℝ
      = (EuclideanSpace.graphDensity g (EuclideanSpace.init (T x)))⁻¹ := by
  rw [EuclideanSpace.graphNormal, real_inner_smul_right, LinearIsometryEquiv.inner_map_map,
    inner_neg_left, EuclideanSpace.inner_single_left, EuclideanSpace.snocLast_apply_last]
  simp

/-- **A bounded `C¹` domain has a transversal field**: a `C¹` compactly supported `w` with
`⟪w, ν⟫ ≥ 1` `σ`-a.e. — the field `w = c ∑ᵢ θᵢ Tᵢ⁻¹(−e_N)` of the chosen atlas, `c ≥ 1` bounding
the densities `√(1 + |∇gᵢ|²)` over the bounded parameter domains: on `∂Ω ∩ B(xᵢ, rᵢ)` the
normal is the chart normal and `⟪Tᵢ⁻¹(−e_N), ν⟫ = 1/√(1 + |∇gᵢ|²) ≥ 1/c`
(`inner_symm_neg_single_last_graphNormal`), so `⟪w, ν⟫ ≥ ∑ θᵢ = 1` on `∂Ω`. -/
theorem exists_transversalField :
    ∃ w : 𝔼 → 𝔼, ContDiff ℝ 1 w ∧ HasCompactSupport w ∧
      ∀ᵐ x ∂(hΩ.boundaryMeasure hb), 1 ≤ ⟪w x, hΩ.outwardNormal hb x⟫_ℝ := by
  set a := hΩ.graphAtlas hb with ha
  -- a common bound `c ≥ 1` on the densities of the charts over their parameter domains
  have hbd : ∀ i : Fin a.k, ∃ M, ∀ x' ∈ a.graphDomain i,
      EuclideanSpace.graphDensity (a.g i) x' ≤ M := fun i ↦ by
    obtain ⟨M, hM⟩ := (EuclideanSpace.isBounded_graphDomain (T := a.T i) (g := a.g i) (a.x i)
      (a.r i)).isCompact_closure.exists_bound_of_continuousOn
      (EuclideanSpace.continuous_graphDensity (a.contDiff_g i)).continuousOn
    exact ⟨M, fun x' hx' ↦ (le_abs_self _).trans (hM x' (subset_closure hx'))⟩
  choose M hM using hbd
  obtain ⟨c₀, hc₀⟩ := (Set.finite_range M).bddAbove
  set c := max c₀ 1 with hcdef
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMc : ∀ i, M i ≤ c := fun i ↦ (hc₀ ⟨i, rfl⟩).trans (le_max_left _ _)
  -- the downward direction of each chart
  set v : Fin a.k → 𝔼 := fun i ↦
    (a.T i).linearIsometryEquiv.symm (-EuclideanSpace.single (Fin.last d) (1 : ℝ)) with hvdef
  refine ⟨fun x ↦ c • ∑ i, a.θ i x • v i, ?_, ?_, ?_⟩
  · have h1 : ∀ i, ContDiff ℝ 1 (a.θ i) := fun i ↦ (a.contDiff_θ i).of_le (by simp)
    have h2 : ContDiff ℝ 1 fun x ↦ ∑ i, a.θ i x • v i :=
      ContDiff.sum fun i _ ↦ (h1 i).smul_const (v i)
    exact h2.const_smul c
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_iUnion fun i ↦ a.hasCompactSupport_θ i) fun x hx ↦ ?_
    by_contra hnot
    simp only [mem_iUnion, not_exists] at hnot
    refine hx ?_
    simp only [Function.mem_support, ne_eq] at hx ⊢
    rw [Finset.sum_eq_zero fun i _ ↦ by rw [image_eq_zero_of_notMem_tsupport (hnot i), zero_smul],
      smul_zero]
  · filter_upwards [hΩ.ae_mem_frontier_boundaryMeasure hb] with x hx
    have key : ∀ i, a.θ i x * c⁻¹ ≤ a.θ i x * ⟪v i, hΩ.outwardNormal hb x⟫_ℝ := fun i ↦ by
      by_cases hθ : a.θ i x = 0
      · simp [hθ]
      · have hxB : x ∈ Metric.ball (a.x i) (a.r i) := by
          by_contra hB
          exact hθ (a.θ_eq_zero i hB)
        refine mul_le_mul_of_nonneg_left ?_ (a.θ_nonneg i x)
        rw [hΩ.outwardNormal_eq_graphNormal_atlas hb hx hxB, hvdef,
          inner_symm_neg_single_last_graphNormal]
        have hx' : EuclideanSpace.init (a.T i x) ∈ a.graphDomain i := by
          change EuclideanSpace.graphParam (a.T i) (a.g i) (EuclideanSpace.init (a.T i x))
            ∈ Metric.ball (a.x i) (a.r i)
          rw [EuclideanSpace.graphParam_eq_of_mem_frontier (a.contDiff_g i).continuous
            (EuclideanSpace.mem_frontier_preimage_epigraph_of_mem_frontier
              (a.contDiff_g i).continuous (a.inter_ball_eq i) hx hxB)]
          exact hxB
        exact inv_anti₀ (EuclideanSpace.graphDensity_pos _) ((hM i _ hx').trans (hMc i))
    calc (1 : ℝ) = c * ∑ i, a.θ i x * c⁻¹ := by
          rw [← Finset.sum_mul, a.sum_θ hx, one_mul, mul_inv_cancel₀ hc.ne']
      _ ≤ c * ∑ i, a.θ i x * ⟪v i, hΩ.outwardNormal hb x⟫_ℝ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ key i) hc.le
      _ = ⟪c • ∑ i, a.θ i x • v i, hΩ.outwardNormal hb x⟫_ℝ := by
          rw [real_inner_smul_left, sum_inner]
          simp_rw [real_inner_smul_left]

end Set

section Opens

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- **A bounded `C¹` domain is a `BoundaryData`**: the surface measure `hΩ.boundaryMeasure hb`,
the outward normal `hΩ.outwardNormal hb`, and the divergence theorem
`IsContDiffDomain.integral_div_eq` (decision B1 of `notes/boundary/planning-brief.md`). The
surface nodes on `C¹` domains take `hΩ.boundaryData hb`; they compute with the chart
characterizations `IsContDiffDomain.boundaryMeasure_restrict_ball` and
`IsContDiffDomain.outwardNormal_eq_graphNormal`. -/
def boundaryData : BoundaryData Ω where
  σ := hΩ.boundaryMeasure hb
  ν := hΩ.outwardNormal hb
  isBounded := hb
  isFiniteMeasure := hΩ.isFiniteMeasure_boundaryMeasure hb
  measure_compl_frontier := hΩ.boundaryMeasure_compl_frontier hb
  aestronglyMeasurable_ν := hΩ.aestronglyMeasurable_outwardNormal hb
  ae_norm_ν := hΩ.ae_norm_outwardNormal hb
  integral_div_eq := fun _ hF₀ hF₁ ↦ hΩ.integral_div_eq hb hF₀ hF₁

/-- The surface measure of the boundary data of a bounded `C¹` domain is `boundaryMeasure`. -/
@[simp]
theorem boundaryData_σ : (hΩ.boundaryData hb).σ = hΩ.boundaryMeasure hb := rfl

/-- The normal of the boundary data of a bounded `C¹` domain is `outwardNormal`. -/
@[simp]
theorem boundaryData_ν : (hΩ.boundaryData hb).ν = hΩ.outwardNormal hb := rfl

/-- **A bounded `C¹` domain has a transversal field** (`exists_transversalField`), the
hypothesis of Nečas's trace construction in `Boundary/Trace.lean`. -/
theorem hasTransversalField : (hΩ.boundaryData hb).HasTransversalField :=
  hΩ.exists_transversalField hb

/-! ### The trace theorem on a bounded `C¹` domain -/

/-- **The trace theorem on a bounded `C¹` domain** (Atkinson–Han Theorem 7.3.10 (a), (b) with
`Lipschitz` restated as `C¹`; Grisvard Theorem 1.5.1.3 into `L^p(Γ)`; [brezis2011functional]
Comments on chapter 9, 7): the trace family of `hΩ.boundaryData hb` — the trace
`W^{1,p}(Ω) →L L^p(σ)` at every `1 ≤ p < ∞`, the restriction of continuous representatives, and
Green's formula — from the transversal field (`hasTransversalField`) and the density theorems of
`Boundary/Density.lean` (a bounded `C¹` graph domain has the segment property), through the
constructor `BoundaryData.traceFamily` of `Boundary/Trace.lean`. -/
def traceFamily : (hΩ.boundaryData hb).TraceFamily :=
  BoundaryData.traceFamily _ (hΩ.hasTransversalField hb) (fun _ _ hp ↦ hΩ.hasSmoothDensity hp)
    fun _ _ hp ↦ hΩ.hasUniformSmoothDensity hb hp

/-- **The trace operator of a bounded `C¹` domain**, `W^{1,p}(Ω) →L L^p(σ)` for `1 ≤ p < ∞`:
the trace of `hΩ.traceFamily hb`. -/
abbrev traceL (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] Lp ℝ p (hΩ.boundaryMeasure hb) :=
  (hΩ.traceFamily hb).traceL p hp

/-- The trace of the trace family is `traceL` (and `BoundaryData.traceL` of the boundary data). -/
theorem traceFamily_traceL (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (hΩ.traceFamily hb).traceL p hp
      = (hΩ.boundaryData hb).traceL (hΩ.hasTransversalField hb) p hp :=
  rfl

/-- **The trace of a function continuous up to the boundary is its restriction**
(Atkinson–Han Theorem 7.3.10 (a)): for `u ∈ W^{1,p}(Ω)` with `fn u = ũ` a.e. on `Ω` and `ũ`
continuous on `closure Ω`, `traceL u = ũ` `σ`-a.e. -/
theorem traceL_ae_eq_of_continuousOn (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : SobolevEuclidean (d + 1) 1 p Ω) {ũ : 𝔼 → ℝ}
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) :
    (hΩ.traceL hb p hp u : 𝔼 → ℝ) =ᵐ[hΩ.boundaryMeasure hb] ũ :=
  (hΩ.traceFamily hb).traceL_ae_eq p hp u ũ hu hc

/-- **Green's formula on a bounded `C¹` domain** (Grisvard Theorem 1.5.3.1, Atkinson–Han (7.6.1)
and (7.6.3), [brezis2011functional] Comments on chapter 9, 7 (iii)): for `u ∈ W^{1,p}(Ω)`,
`v ∈ W^{1,q}(Ω)` at conjugate exponents `1 < p, q < ∞`,
`∫_Ω ∂ᵢu v + ∫_Ω u ∂ᵢv = ∫ (Tu)(Tv) νᵢ dσ`. -/
theorem green (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (u : SobolevEuclidean (d + 1) 1 p Ω)
    (v : SobolevEuclidean (d + 1) 1 q Ω) (i : Fin (d + 1)) :
    (∫ x in (Ω : Set 𝔼),
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x
          * SobolevMultiIndex.fn v x)
      + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x
          * (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x, (hΩ.traceL hb p hp u : 𝔼 → ℝ) x * (hΩ.traceL hb q hq v : 𝔼 → ℝ) x
          * hΩ.outwardNormal hb x i ∂(hΩ.boundaryMeasure hb) :=
  (hΩ.traceFamily hb).green p q hp hq u v i

/-- **Green's formula against a compactly supported `C¹` test function**, at every `1 ≤ p < ∞`:
`∫_Ω ∂ᵢu φ + ∫_Ω u ∂ᵢφ = ∫ (Tu) φ νᵢ dσ`. -/
theorem green_contDiff (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean (d + 1) 1 p Ω)
    {φ : 𝔼 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (i : Fin (d + 1)) :
    (∫ x in (Ω : Set 𝔼),
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x)
      + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x
          * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (hΩ.traceL hb p hp u : 𝔼 → ℝ) x * φ x * hΩ.outwardNormal hb x i
          ∂(hΩ.boundaryMeasure hb) :=
  (hΩ.traceFamily hb).green_contDiff p hp u φ hφ hφc i

/-- **`W_0^{1,p}(Ω) ⊆ ker T`** on a bounded `C¹` domain, `1 ≤ p < ∞` (the easy half of
[brezis2011functional] Comments on chapter 9, 7 (ii)). -/
theorem traceL_eq_zero_of_mem_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p Ω) :
    hΩ.traceL hb p hp u = 0 :=
  (hΩ.traceFamily hb).traceL_eq_zero_of_mem_zero hp hu

/-- **Compactness of the trace on a bounded `C¹` domain** (Atkinson–Han Theorem 7.3.10 (c)) for
`1 < p < ∞`: `traceL : W^{1,p}(Ω) →L L^p(σ)` is a compact operator, by Nečas's sharp inequality
(`BoundaryData.isCompactOperator_traceL`) and Rellich's theorem
`SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one`, which at `p ≠ 1` needs no restriction on
the dimension. The hypothesis `1 < p` is necessary: the trace `W^{1,1}(Ω) → L¹(∂Ω)` is onto
(Gagliardo), hence not compact; the book's `1 ≤ p` is an erratum. -/
theorem isCompactOperator_traceL (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsCompactOperator (hΩ.traceL hb p hp) := by
  refine BoundaryData.isCompactOperator_traceL _ (hΩ.hasTransversalField hb) p hp hp1
    (hΩ.hasSmoothDensity hp) ?_
  lift p to ℝ≥0 using hp
  refine SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one hΩ.isContDiffChartDomain hb
    (Or.inl fun h ↦ hp1.ne' ?_)
  rw [h]
  rfl

end Opens

end IsContDiffDomain

/-! ### Chart domains (Brezis's definition), through the chart ⇒ graph bridge -/

namespace IsContDiffChartDomain

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (h : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- **A bounded `C¹` chart domain** ([brezis2011functional] §9.2's definition) **is a
`BoundaryData`**: the boundary data of the graph domain it is by the implicit function theorem
(`IsContDiffChartDomain.isContDiffDomain`, `Boundary/ChartGraph.lean`). -/
def boundaryData : BoundaryData Ω :=
  (h.isContDiffDomain le_rfl WithTop.one_ne_top).boundaryData hb

/-- **The trace theorem on a bounded `C¹` chart domain**, through the chart ⇒ graph bridge. -/
def traceFamily : (h.boundaryData hb).TraceFamily :=
  (h.isContDiffDomain le_rfl WithTop.one_ne_top).traceFamily hb

end IsContDiffChartDomain

end
