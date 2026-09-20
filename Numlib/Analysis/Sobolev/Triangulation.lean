import Numlib.Analysis.Calculus.IntegrationByPartsOffSegments
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.Analysis.Sobolev.SeminormCompare
import Numlib.Geometry.Triangulation

/-!
# Sobolev functions on a triangulated domain

The two facts about Sobolev spaces that the finite element method needs from a triangulation
`𝒯` of a plane domain `Ω` ([han2009theoretical] §10.2–§10.3), and their general forms.

* **Additivity of the norm over the elements.** Since the open elements partition `Ω` up to a
  null set and the weak derivative restricts to each of them, `‖f‖_{k,p,Ω}^p = ∑_K ‖f‖_{k,p,K}^p`
  and `|f|_{k,p,Ω}^p = ∑_K |f|_{k,p,K}^p` for every `f ∈ W^{k,p}(Ω)`, `1 ≤ p < ∞`
  (`Triangulation.sobolevNorm_rpow_eq_sum`, `Triangulation.sobolevSeminorm_rpow_eq_sum`). The
  general statement, for any finite family of disjoint open subsets of `Ω` whose union is `Ω`
  up to a null set, is `sobolevNorm_rpow_eq_sum` and `sobolevSeminorm_rpow_eq_sum`.
* **Conformity: a continuous piecewise-`C¹` function is `W^{1,p}(Ω)`.** A function on `Ω`
  continuous up to the boundary which agrees on each open element `K` with a `C¹` function
  `g K` lies in `W^{1,p}(Ω)` for every `1 ≤ p ≤ ∞`, with weak derivative the elementwise
  derivative `Triangulation.pieceFDeriv g` (`Triangulation.hasWeakFDerivOn_of_piecewise`,
  `Triangulation.memSobolev_of_piecewise`). This is the direction of [han2009theoretical]
  Example 7.2.7 that the finite element method uses ("`v_h ∈ H¹(Ω)` if and only if
  `v_h ∈ C(Ω̄)`", §10.2.3), and it is proved **without Green's formula**: the weak-derivative
  identity `∫_Ω (∂_v φ) u = -∫_Ω φ (∂_v u)` is the integration by parts
  `integral_fderiv_smul_eq_neg_smul_fderiv_of_integrable_off_segments` of
  `Numlib/Analysis/Calculus/IntegrationByPartsOffSegments.lean`, whose exceptional set is the
  skeleton of the triangulation, a finite union of segments: on almost every line parallel to
  `v` the function `φ u` is continuous and differentiable off finitely many points, so the
  fundamental theorem of calculus holds on it, and Fubini does the rest.
* **The glued function.** The function `𝒯.glue g` equal to `g K` on each closed element, for a
  compatible family of `C¹` pieces, is therefore in `W^{1,p}(Ω)` (`Triangulation.memSobolev_glue`):
  this is how the global finite element interpolant `Π_h v` enters `H¹(Ω)`.
-/

open EuclideanSpace Function Set Topology MeasureTheory TopologicalSpace

open scoped ENNReal Distributions

noncomputable section

/-! ### Additivity of the Sobolev norm over an almost-everywhere partition -/

section Additivity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens E} {μ : Measure E} {p : ℝ≥0∞} {f : E → F}
  {ι : Type*} [Fintype ι] {U : ι → Opens E}

/-- **The `p`-th power of the Sobolev seminorm is additive over a finite family of disjoint
open subsets of `Ω` covering it up to a null set**, `1 ≤ p < ∞`: the weak derivative of order
`n` on `Ω` restricts to a weak derivative on each `U i`, and the `L^p(Ω)` integral splits. -/
theorem sobolevSeminorm_rpow_eq_sum [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hU : ∀ i, U i ≤ Ω)
    (hd : Pairwise (Disjoint on fun i ↦ (U i : Set E)))
    (hae : (⋃ i, (U i : Set E)) =ᵐ[μ] (Ω : Set E)) {n : ℕ} (hf : MemSobolev f n p Ω μ) :
    sobolevSeminorm f n p Ω μ ^ p.toReal = ∑ i, sobolevSeminorm f n p (U i) μ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpt : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hp0, hp⟩
  have key : ∀ (V : Opens E) (g : E → E [×n]→L[ℝ] F), MemLp g p (μ.restrict V) →
      eLpNorm g p (μ.restrict V) ^ p.toReal = ∫⁻ x in (V : Set E), ‖g x‖ₑ ^ p.toReal ∂μ := by
    intro V g hg
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable,
      ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpt, ENNReal.rpow_one]
  unfold sobolevSeminorm
  rw [key Ω _ (hf.memLp_weakIteratedFDeriv le_rfl), setLIntegral_congr hae.symm,
    lintegral_iUnion (fun i ↦ (U i).isOpen.measurableSet) hd, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [key (U i) _ ((hf.mono_set (hU i)).memLp_weakIteratedFDeriv le_rfl)]
  refine setLIntegral_congr_fun_ae (U i).isOpen.measurableSet ?_
  filter_upwards [((hf.hasWeakIteratedFDerivOn le_rfl).mono (hU i)).weakIteratedFDeriv_ae_eq]
    with x hx hxU
  rw [hx hxU]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- The `p`-th power of the Sobolev norm is the sum of the `p`-th powers of the seminorms of
all orders, `1 ≤ p < ∞`. -/
theorem sobolevNorm_rpow_eq_sum_sobolevSeminorm_rpow [Fact (1 ≤ p)] (hp : p ≠ ⊤) (k : ℕ)
    (V : Opens E) :
    sobolevNorm f k p V μ ^ p.toReal = ∑ n : Fin (k + 1), sobolevSeminorm f n p V μ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpt : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hp0, hp⟩
  simp only [sobolevNorm, hp, ↓reduceIte]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpt, ENNReal.rpow_one]
  rfl

/-- **The `p`-th power of the Sobolev norm is additive over a finite family of disjoint open
subsets of `Ω` covering it up to a null set**, `1 ≤ p < ∞`:
`‖f‖_{k,p,Ω}^p = ∑_i ‖f‖_{k,p,U i}^p` for `f ∈ W^{k,p}(Ω)`. -/
theorem sobolevNorm_rpow_eq_sum [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hU : ∀ i, U i ≤ Ω)
    (hd : Pairwise (Disjoint on fun i ↦ (U i : Set E)))
    (hae : (⋃ i, (U i : Set E)) =ᵐ[μ] (Ω : Set E)) {k : ℕ} (hf : MemSobolev f k p Ω μ) :
    sobolevNorm f k p Ω μ ^ p.toReal = ∑ i, sobolevNorm f k p (U i) μ ^ p.toReal := by
  simp_rw [sobolevNorm_rpow_eq_sum_sobolevSeminorm_rpow hp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  exact sobolevSeminorm_rpow_eq_sum hp hU hd hae
    (hf.mono_order (by exact_mod_cast Nat.lt_succ_iff.1 n.2))

end Additivity

/-! ### Sobolev functions on a triangulation -/

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

namespace Triangulation

variable {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {p : ℝ≥0∞}

/-- **The Sobolev seminorm is additive over the elements**: `|f|_{n,p,Ω}^p = ∑_K |f|_{n,p,K}^p`
for `f ∈ W^{n,p}(Ω)`, `1 ≤ p < ∞`. -/
theorem sobolevSeminorm_rpow_eq_sum [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : 𝔼₂ → ℝ} {n : ℕ}
    (hf : MemSobolev f n p Ω volume) :
    sobolevSeminorm f n p Ω volume ^ p.toReal
      = ∑ T, sobolevSeminorm f n p (𝒯.Kopens T) volume ^ p.toReal :=
  _root_.sobolevSeminorm_rpow_eq_sum hp 𝒯.Kopens_le 𝒯.pairwise_disjoint_K 𝒯.ae_eq_iUnion_K hf

/-- **The Sobolev norm is additive over the elements** ([han2009theoretical], the first line of
the proof of Theorem 10.3.9): `‖f‖_{k,p,Ω}^p = ∑_K ‖f‖_{k,p,K}^p` for `f ∈ W^{k,p}(Ω)`,
`1 ≤ p < ∞`. -/
theorem sobolevNorm_rpow_eq_sum [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : 𝔼₂ → ℝ} {k : ℕ}
    (hf : MemSobolev f k p Ω volume) :
    sobolevNorm f k p Ω volume ^ p.toReal
      = ∑ T, sobolevNorm f k p (𝒯.Kopens T) volume ^ p.toReal :=
  _root_.sobolevNorm_rpow_eq_sum hp 𝒯.Kopens_le 𝒯.pairwise_disjoint_K 𝒯.ae_eq_iUnion_K hf

/-! #### The elementwise derivative -/

/-- **The elementwise derivative** of a family `g` of functions, one per element: the derivative
of `g T` on the open element `K_T`, and `0` on the skeleton and outside the domain. It is the
weak derivative of the function equal to `g T` on each `K_T`
(`Triangulation.hasWeakFDerivOn_of_piecewise`). -/
def pieceFDeriv (g : 𝒯.elems → 𝔼₂ → ℝ) : 𝔼₂ → 𝔼₂ →L[ℝ] ℝ := fun x ↦
  ∑ T, (𝒯.K T).indicator (fderiv ℝ (g T)) x

/-- On an open element the elementwise derivative is the derivative of the piece there. -/
theorem pieceFDeriv_of_mem (g : 𝒯.elems → 𝔼₂ → ℝ) (T : 𝒯.elems) {x : 𝔼₂} (hx : x ∈ 𝒯.K T) :
    𝒯.pieceFDeriv g x = fderiv ℝ (g T) x := by
  unfold pieceFDeriv
  rw [Finset.sum_eq_single T]
  · rw [indicator_of_mem hx]
  · intro T' _ hT'
    refine indicator_of_notMem (fun hx' ↦ ?_) _
    exact Set.disjoint_left.1 (𝒯.pairwise_disjoint_K hT') hx' hx
  · exact fun h ↦ absurd (Finset.mem_univ T) h

/-- The elementwise derivative is measurable. -/
theorem measurable_pieceFDeriv (g : 𝒯.elems → 𝔼₂ → ℝ) : Measurable (𝒯.pieceFDeriv g) :=
  Finset.measurable_sum _ fun T _ ↦
    (measurable_fderiv ℝ (g T)).indicator (𝒯.isOpen_K T).measurableSet

/-- The elementwise derivative of a family of `C¹` pieces is bounded: each derivative is
continuous on the compact closed element. -/
theorem exists_norm_pieceFDeriv_le {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : ∀ T, ContDiff ℝ 1 (g T)) :
    ∃ M : ℝ, ∀ x, ‖𝒯.pieceFDeriv g x‖ ≤ M := by
  have hb : ∀ T : 𝒯.elems, ∃ C : ℝ, ∀ x ∈ 𝒯.K T, ‖fderiv ℝ (g T) x‖ ≤ C := fun T ↦ by
    obtain ⟨C, hC⟩ := (𝒯.isCompact_closedK T).exists_bound_of_continuousOn
      ((hg T).continuous_fderiv one_ne_zero).continuousOn
    exact ⟨C, fun x hx ↦ hC x (𝒯.K_subset_closedK T hx)⟩
  choose C hC using hb
  refine ⟨∑ T, max (C T) 0, fun x ↦ ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun T _ ↦ ?_)
  by_cases hx : x ∈ 𝒯.K T
  · rw [indicator_of_mem hx]
    exact (hC T x hx).trans (le_max_left _ _)
  · rw [indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

/-- The elementwise derivative of a family of `C¹` pieces lies in `L^∞(Ω)`. -/
theorem memLp_top_pieceFDeriv {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : ∀ T, ContDiff ℝ 1 (g T)) :
    MemLp (𝒯.pieceFDeriv g) ⊤ (volume.restrict (Ω : Set 𝔼₂)) := by
  obtain ⟨M, hM⟩ := 𝒯.exists_norm_pieceFDeriv_le hg
  exact memLp_top_of_bound (𝒯.measurable_pieceFDeriv g).aestronglyMeasurable M
    (Filter.Eventually.of_forall hM)

/-! #### Conformity: continuous piecewise-`C¹` functions are `W^{1,p}` -/

/-- **A continuous piecewise-`C¹` function has the elementwise derivative as weak derivative.**
Let `u` be continuous on `Ω` and equal on each open element `K_T` to a `C¹` function `g T`.
Then `𝒯.pieceFDeriv g` is a first-order weak derivative of `u` on `Ω`.

The integration by parts against a test function `φ` and a direction `v`,
`∫_Ω (∂_v φ) u = -∫_Ω φ (∂_v u)`, is
`integral_fderiv_smul_eq_neg_smul_fderiv_of_integrable_off_segments`: `u` is continuous on the
support of `φ` and differentiable, with derivative `fderiv (g T)`, at every point of it off the
skeleton `⋃_T ∂K_T`, which is a finite union of segments — a point of `Ω` off the skeleton lies
in some open `K_T`, where `u = g T`. No Green formula on the elements is used. -/
theorem hasWeakFDerivOn_of_piecewise {u : 𝔼₂ → ℝ} (hu : ContinuousOn u Ω)
    {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : ∀ T, ContDiff ℝ 1 (g T))
    (hug : ∀ T, ∀ x ∈ 𝒯.K T, u x = g T x) :
    HasWeakFDerivOn u (𝒯.pieceFDeriv g) Ω volume := by
  have hloc : LocallyIntegrableOn (𝒯.pieceFDeriv g) (Ω : Set 𝔼₂) volume :=
    (𝒯.memLp_top_pieceFDeriv hg).locallyIntegrableOn le_top
  have huloc : LocallyIntegrableOn u (Ω : Set 𝔼₂) volume :=
    hu.locallyIntegrableOn Ω.isOpen.measurableSet
  rw [hasWeakFDerivOn_iff]
  refine ⟨huloc, hloc, fun φ v ↦ ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      rw [show fderiv ℝ (φ : 𝔼₂ → ℝ) x v = 0 from (φ.fderivApply v).eq_zero_of_notMem hx,
        zero_smul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      rw [φ.eq_zero_of_notMem hx, zero_smul])]
  refine integral_fderiv_smul_eq_neg_smul_fderiv_of_integrable_off_segments (μ := volume)
    (by rw [finrank_euclideanSpace_fin]) v (P := fun q : 𝒯.elems × Fin 3 ↦ q.1.1 q.2)
    (Q := fun q ↦ q.1.1 (q.2 + 1)) ?_ ?_ ?_ ?_ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  · exact (hloc.comp_continuousLinearMap (ContinuousLinearMap.apply ℝ ℝ v))
      |>.integrable_smul_left_of_tsupport_subset φ.continuous φ.hasCompactSupport
        φ.tsupport_subset
  · exact huloc.integrable_smul_left_of_tsupport_subset (φ.fderivApply v).continuous
      (φ.fderivApply v).hasCompactSupport (φ.fderivApply v).tsupport_subset
  · exact fun x hx ↦ hu.continuousAt (Ω.isOpen.mem_nhds (φ.tsupport_subset hx))
  · intro x hx hS
    obtain ⟨T, hT⟩ := 𝒯.exists_mem_K_of_notMem_skeleton (φ.tsupport_subset hx)
      fun h ↦ hS (𝒯.skeleton_subset_iUnion_segment h)
    rw [𝒯.pieceFDeriv_of_mem g T hT]
    refine ((hg T).differentiable one_ne_zero x).hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [(𝒯.isOpen_K T).mem_nhds hT] with y hy
    exact hug T y hy

/-- **A continuous piecewise-`C¹` function lies in `W^{1,p}(Ω)`** for every `1 ≤ p ≤ ∞`
([han2009theoretical] Example 7.2.7 and §10.2.3, the direction used by the finite element
method): a function continuous on `Ω̄` and equal on each open element to a `C¹` function is in
`W^{1,p}(Ω)`, with weak derivative the elementwise derivative. -/
theorem memSobolev_of_piecewise {u : 𝔼₂ → ℝ} (hu : ContinuousOn u (closure (Ω : Set 𝔼₂)))
    {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : ∀ T, ContDiff ℝ 1 (g T))
    (hug : ∀ T, ∀ x ∈ 𝒯.K T, u x = g T x) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MemSobolev u 1 p Ω volume := by
  have hfin : IsFiniteMeasure (volume.restrict (Ω : Set 𝔼₂)) :=
    isFiniteMeasure_restrict.2 𝒯.isBounded.measure_lt_top.ne
  refine (𝒯.hasWeakFDerivOn_of_piecewise (hu.mono subset_closure) hg hug).memSobolev ?_ ?_
  · obtain ⟨C, hC⟩ := 𝒯.isCompact_closure.exists_bound_of_continuousOn hu
    exact MemLp.of_bound ((hu.mono subset_closure).aestronglyMeasurable Ω.isOpen.measurableSet) C
      ((ae_restrict_iff' Ω.isOpen.measurableSet).2
        (Filter.Eventually.of_forall fun x hx ↦ hC x (subset_closure hx)))
  · exact (𝒯.memLp_top_pieceFDeriv hg).mono_exponent le_top

/-! #### The glued function -/

/-- **The function glued from compatible `C¹` pieces lies in `W^{1,p}(Ω)`** for every
`1 ≤ p ≤ ∞`: it is continuous on `Ω̄` (`Triangulation.continuousOn_glue`) and equal to the
piece on each open element. This is how the global finite element interpolant, glued from the
elementwise polynomial interpolants, enters `H¹(Ω)`. -/
theorem memSobolev_glue {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g)
    (hgc : ∀ T, ContDiff ℝ 1 (g T)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MemSobolev (𝒯.glue g) 1 p Ω volume :=
  𝒯.memSobolev_of_piecewise (𝒯.continuousOn_glue hg fun T ↦ (hgc T).continuous.continuousOn)
    hgc (fun T _ hx ↦ 𝒯.glue_eq_of_mem_K hg T hx) p

/-- The weak derivative of the glued function is the elementwise derivative. -/
theorem hasWeakFDerivOn_glue {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g)
    (hgc : ∀ T, ContDiff ℝ 1 (g T)) :
    HasWeakFDerivOn (𝒯.glue g) (𝒯.pieceFDeriv g) Ω volume :=
  𝒯.hasWeakFDerivOn_of_piecewise
    ((𝒯.continuousOn_glue hg fun T ↦ (hgc T).continuous.continuousOn).mono subset_closure) hgc
    fun T _ hx ↦ 𝒯.glue_eq_of_mem_K hg T hx

/-- On an open element, a function of `W^{k,p}(Ω)` and its glued interpolant differ, in the
Sobolev norm of the element, by the same amount as the function and the piece there: the
Sobolev norm on `K_T` only sees the function up to a null set of `K_T`. -/
theorem sobolevNorm_sub_glue {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g) (T : 𝒯.elems)
    (f : 𝔼₂ → ℝ) (k : ℕ) :
    sobolevNorm (f - 𝒯.glue g) k p (𝒯.Kopens T) volume
      = sobolevNorm (f - g T) k p (𝒯.Kopens T) volume :=
  sobolevNorm_congr_ae ((ae_restrict_iff' (𝒯.isOpen_K T).measurableSet).2
    (Filter.Eventually.of_forall fun x hx ↦ by
      simp only [Pi.sub_apply, 𝒯.glue_eq_of_mem_K hg T hx]))

/-! #### The global interpolant -/

section Interpolant

variable {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)

/-- **The global interpolant of a conforming element with `C¹` shape functions lies in
`W^{1,p}(Ω)`** for every `1 ≤ p ≤ ∞` ([han2009theoretical] §10.2.3, `X_h ⊆ H¹(Ω)`). -/
theorem memSobolev_globalInterp (h : 𝒯.IsConformingElement xhat φhat)
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i)) (v : 𝔼₂ → ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MemSobolev (𝒯.globalInterp xhat φhat v) 1 p Ω volume :=
  𝒯.memSobolev_glue (h v) (fun T ↦ 𝒯.contDiff_localInterp xhat φhat hφ T v) p

/-- On an element, the interpolation error of the global interpolant is that of the local one:
`‖v − Π_h v‖_{k,p,K} = ‖v − Π_K v‖_{k,p,K}`. -/
theorem sobolevNorm_sub_globalInterp (h : 𝒯.IsConformingElement xhat φhat) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) (k : ℕ) :
    sobolevNorm (v - 𝒯.globalInterp xhat φhat v) k p (𝒯.Kopens T) volume
      = sobolevNorm (v - 𝒯.localInterp xhat φhat T v) k p (𝒯.Kopens T) volume :=
  𝒯.sobolevNorm_sub_glue (h v) T v k

end Interpolant

end Triangulation

/-! ### Smooth functions on a bounded open set -/

section ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℝ F]
  [μ.IsAddHaarMeasure] in
/-- A continuous function lies in `L^p` of a bounded open set, for every exponent, when the
measure is finite on bounded sets: it is bounded on the compact closure. -/
theorem Continuous.memLp_restrict_of_isBounded [ProperSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (hb : Bornology.IsBounded (Ω : Set E)) {g : E → F}
    (hg : Continuous g) (p : ℝ≥0∞) : MemLp g p (μ.restrict (Ω : Set E)) := by
  have hfin : IsFiniteMeasure (μ.restrict (Ω : Set E)) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C ((ae_restrict_iff' Ω.isOpen.measurableSet).2
    (Filter.Eventually.of_forall fun x hx ↦ hC x (subset_closure hx)))

/-- **A `C^k` function on a bounded open set lies in `W^{k,p}`** for every exponent: its
classical derivatives are its weak derivatives, and they are bounded on the compact closure. -/
theorem ContDiff.memSobolev_of_isBounded (hb : Bornology.IsBounded (Ω : Set E)) {k : ℕ}
    {f : E → F} (hf : ContDiff ℝ k f) (p : ℝ≥0∞) : MemSobolev f k p Ω μ := by
  refine ⟨hf.continuous.memLp_restrict_of_isBounded hb p,
    fun n hn ↦ ⟨iteratedFDeriv ℝ n f, ?_, ?_⟩⟩
  · exact hf.contDiffOn.hasWeakIteratedFDerivOn (by exact_mod_cast hn)
  · exact (hf.continuous_iteratedFDeriv (by exact_mod_cast hn)).memLp_restrict_of_isBounded hb p

end ContDiff

end
