import Numlib.Analysis.Calculus.IntegrationByPartsOffSegments
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.Analysis.Sobolev.SeminormCompare
import Numlib.Analysis.Sobolev.Zero
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
* **The finite element spaces.** `Triangulation.polySpace p k` is the space `X_h ⊆ W^{1,p}(Ω)`
  of continuous piecewise polynomials of degree at most `k` (`Triangulation.IsPiecewisePoly`),
  and `Triangulation.polySpaceZero p k` the space `V_h ⊆ W_0^{1,p}(Ω)` of those vanishing on
  `∂Ω` ([quarteroni2000numerical] (12.94), [han2009theoretical] §10.4). The boundary condition
  is read on the continuous representative and needs no trace: a continuous `W^{1,p}` function
  vanishing on `∂Ω` lies in `W_0^{1,p}(Ω)` on any open set ([brezis2011functional] Theorem 9.17,
  `Triangulation.exists_mem_polySpaceZero`). The interpolant of a boundary-vanishing function
  lies in `V_h` for an edge-unisolvent element on a polygon
  (`Triangulation.exists_mem_polySpaceZero_globalInterp`), and both spaces are
  finite-dimensional once a conforming element reproducing `ℙ_k` is fixed, an element of `X_h`
  being determined by its nodal values (`Triangulation.finiteDimensional_polySpace`).
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


/-! #### The elementwise derivative of order `n`, and the weak derivative of order `k + 1` -/

/-- **The elementwise derivative of order `n`** of a family `g` of functions, one per element:
`∂^n (g T)` on the open element `K_T`, and `0` on the skeleton and outside the domain. At `n = 1`
it is `pieceFDeriv` read as a multilinear map. -/
def pieceIteratedFDeriv (n : ℕ) (g : 𝒯.elems → 𝔼₂ → ℝ) : 𝔼₂ → 𝔼₂ [×n]→L[ℝ] ℝ := fun x ↦
  ∑ T, (𝒯.K T).indicator (iteratedFDeriv ℝ n (g T)) x

/-- On an open element the elementwise derivative of order `n` is the derivative of the piece
there. -/
theorem pieceIteratedFDeriv_of_mem {n : ℕ} (g : 𝒯.elems → 𝔼₂ → ℝ) (T : 𝒯.elems) {x : 𝔼₂}
    (hx : x ∈ 𝒯.K T) : 𝒯.pieceIteratedFDeriv n g x = iteratedFDeriv ℝ n (g T) x := by
  unfold pieceIteratedFDeriv
  rw [Finset.sum_eq_single T]
  · rw [indicator_of_mem hx]
  · intro T' _ hT'
    refine indicator_of_notMem (fun hx' ↦ ?_) _
    exact Set.disjoint_left.1 (𝒯.pairwise_disjoint_K hT') hx' hx
  · exact fun h ↦ absurd (Finset.mem_univ T) h

/-- Off the open elements the elementwise derivative of order `n` vanishes. -/
theorem pieceIteratedFDeriv_of_notMem {n : ℕ} (g : 𝒯.elems → 𝔼₂ → ℝ) {x : 𝔼₂}
    (hx : x ∉ ⋃ T, 𝒯.K T) : 𝒯.pieceIteratedFDeriv n g x = 0 :=
  Finset.sum_eq_zero fun T _ ↦ indicator_of_notMem (fun h ↦ hx (mem_iUnion.2 ⟨T, h⟩)) _

/-- On an open element, where `v` agrees with the piece `g T`, the classical derivatives of `v`
are those of the piece. -/
theorem iteratedFDeriv_eq_of_mem_K {v : 𝔼₂ → ℝ} {g : 𝒯.elems → 𝔼₂ → ℝ}
    (hvg : ∀ T, ∀ x ∈ 𝒯.K T, v x = g T x) (n : ℕ) (T : 𝒯.elems) {x : 𝔼₂} (hx : x ∈ 𝒯.K T) :
    iteratedFDeriv ℝ n v x = iteratedFDeriv ℝ n (g T) x := by
  have h : v =ᶠ[nhds x] g T := by
    filter_upwards [(𝒯.isOpen_K T).mem_nhds hx] with y hy
    exact hvg T y hy
  exact (h.iteratedFDeriv (𝕜 := ℝ) n).self_of_nhds

/-- The elementwise derivative of order `n` of `C^n` pieces is bounded: each `∂^n (g T)` is
continuous on the compact closed element. -/
theorem exists_norm_pieceIteratedFDeriv_le {n : ℕ} {g : 𝒯.elems → 𝔼₂ → ℝ}
    (hg : ∀ T, ContDiff ℝ n (g T)) : ∃ M : ℝ, ∀ x, ‖𝒯.pieceIteratedFDeriv n g x‖ ≤ M := by
  have hb : ∀ T : 𝒯.elems, ∃ C : ℝ, ∀ x ∈ 𝒯.K T, ‖iteratedFDeriv ℝ n (g T) x‖ ≤ C := fun T ↦ by
    obtain ⟨C, hC⟩ := (𝒯.isCompact_closedK T).exists_bound_of_continuousOn
      ((hg T).continuous_iteratedFDeriv le_rfl).continuousOn
    exact ⟨C, fun x hx ↦ hC x (𝒯.K_subset_closedK T hx)⟩
  choose C hC using hb
  refine ⟨∑ T, max (C T) 0, fun x ↦ ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun T _ ↦ ?_)
  by_cases hx : x ∈ 𝒯.K T
  · rw [indicator_of_mem hx]
    exact (hC T x hx).trans (le_max_left _ _)
  · rw [indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

/-- The elementwise derivative of order `n` of `C^n` pieces is strongly measurable. -/
theorem stronglyMeasurable_pieceIteratedFDeriv {n : ℕ} {g : 𝒯.elems → 𝔼₂ → ℝ}
    (hg : ∀ T, ContDiff ℝ n (g T)) : StronglyMeasurable (𝒯.pieceIteratedFDeriv n g) :=
  Finset.stronglyMeasurable_fun_sum _ fun T _ ↦
    ((hg T).continuous_iteratedFDeriv le_rfl).stronglyMeasurable.indicator
      (𝒯.isOpen_K T).measurableSet

/-- The elementwise derivative of order `n` of `C^n` pieces is locally integrable on `Ω`: it is
strongly measurable and bounded. -/
theorem locallyIntegrableOn_pieceIteratedFDeriv {n : ℕ} {g : 𝒯.elems → 𝔼₂ → ℝ}
    (hg : ∀ T, ContDiff ℝ n (g T)) :
    LocallyIntegrableOn (𝒯.pieceIteratedFDeriv n g) (Ω : Set 𝔼₂) volume := by
  obtain ⟨M, hM⟩ := 𝒯.exists_norm_pieceIteratedFDeriv_le hg
  exact (memLp_top_of_bound (𝒯.stronglyMeasurable_pieceIteratedFDeriv hg).aestronglyMeasurable M
    (Filter.Eventually.of_forall hM)).locallyIntegrableOn le_top

/-- **The weak derivative of order `k + 1` along a tuple of directions** of a `C^k` function that
is piecewise `C^{k+1}` on a triangulation: the elementwise classical derivative of order `k + 1`
evaluated at the tuple. This is the order-`k+1` form of `hasWeakFDerivOn_of_piecewise`.

The tuple `y` is `y 0 :: tail y`; the classical derivative of order `k` along `tail y` is a weak
one, it is continuous on `Ω` and piecewise `C¹`, so its first-order weak derivative in the
direction `y 0` is the elementwise one (`hasWeakFDerivOn_of_piecewise`), and
`HasWeakIteratedLineDerivOn.cons` composes the two ([han2009theoretical] Example 7.1.9). -/
theorem hasWeakIteratedLineDerivOn_of_piecewise {k : ℕ} {v : 𝔼₂ → ℝ} (hv : ContDiffOn ℝ k v Ω)
    {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : ∀ T, ContDiff ℝ (k + 1) (g T))
    (hvg : ∀ T, ∀ x ∈ 𝒯.K T, v x = g T x) (y : Fin (k + 1) → 𝔼₂) :
    HasWeakIteratedLineDerivOn y v (fun x ↦ 𝒯.pieceIteratedFDeriv (k + 1) g x y) Ω volume := by
  -- the classical derivative of order `k` along `tail y` is a weak derivative
  have h₁ : HasWeakIteratedLineDerivOn (Fin.tail y) v
      (fun x ↦ iteratedFDeriv ℝ k v x (Fin.tail y)) Ω volume :=
    (hv.hasWeakIteratedFDerivOn le_rfl).lineDeriv (Fin.tail y)
  -- it is continuous on `Ω` and piecewise `C¹`
  have hu : ContinuousOn (fun x ↦ iteratedFDeriv ℝ k v x (Fin.tail y)) Ω :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ 𝔼₂) ℝ
      (Fin.tail y)).continuous.comp_continuousOn (hv.continuousOn_iteratedFDeriv le_rfl)
  have hg' : ∀ T, ContDiff ℝ 1 fun x ↦ iteratedFDeriv ℝ k (g T) x (Fin.tail y) := fun T ↦
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ 𝔼₂) ℝ (Fin.tail y)).contDiff.comp
      ((hg T).iteratedFDeriv_right (m := 1) (by norm_cast; omega))
  have hug : ∀ T, ∀ x ∈ 𝒯.K T, iteratedFDeriv ℝ k v x (Fin.tail y)
      = iteratedFDeriv ℝ k (g T) x (Fin.tail y) := fun T x hx ↦ by
    rw [𝒯.iteratedFDeriv_eq_of_mem_K hvg k T hx]
  -- its first-order weak derivative in the direction `y 0` is the elementwise one
  have h₂ := (𝒯.hasWeakFDerivOn_of_piecewise hu hg' hug).lineDeriv ![y 0]
  simp only [continuousMultilinearCurryFin1_symm_apply, Matrix.cons_val_zero] at h₂
  have h₃ := h₁.cons h₂
  rw [Fin.cons_self_tail] at h₃
  -- the elementwise derivative of `∂^k (g T) (tail y)` in the direction `y 0` is `∂^{k+1}(g T) y`
  refine h₃.congr_ae (Filter.EventuallyEq.refl _ _) (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only
  by_cases hx : x ∈ ⋃ T, 𝒯.K T
  · obtain ⟨T, hT⟩ := mem_iUnion.1 hx
    rw [𝒯.pieceFDeriv_of_mem _ T hT, 𝒯.pieceIteratedFDeriv_of_mem g T hT,
      iteratedFDeriv_succ_apply_left, fderiv_continuousMultilinear_apply_const_apply
        ((hg T).differentiable_iteratedFDeriv (by norm_cast; omega) x)]
  · rw [𝒯.pieceIteratedFDeriv_of_notMem g hx]
    unfold Triangulation.pieceFDeriv
    rw [Finset.sum_eq_zero fun T _ ↦ indicator_of_notMem (fun h ↦ hx (mem_iUnion.2 ⟨T, h⟩)) _]
    simp
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

/-! #### Continuous piecewise polynomials: the finite element spaces -/

section PolySpace

open MvPolynomial

/-- **A piecewise polynomial of degree at most `k`** on the triangulation: on each closed element
`K` the function is a polynomial of total degree at most `k` in the reference coordinates
`F_K⁻¹ x`, that is, `v|_K ∈ ℙ_k(K)` ([han2009theoretical] §10.4, [quarteroni2000numerical]
(12.94), (8.35)). -/
def IsPiecewisePoly (k : ℕ) (v : 𝔼₂ → ℝ) : Prop :=
  ∀ T : 𝒯.elems, ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k ∧
    ∀ x ∈ 𝒯.closedK T, v x = eval (fun j ↦ (𝒯.linearPart T).symm (x - T.1 0) j) q

variable {𝒯}

/-- The zero function is piecewise polynomial. -/
theorem IsPiecewisePoly.zero (k : ℕ) : 𝒯.IsPiecewisePoly k 0 := fun _ ↦
  ⟨0, by simp, fun _ _ ↦ by simp⟩

/-- The sum of two piecewise polynomials of degree at most `k` is one. -/
theorem IsPiecewisePoly.add {k : ℕ} {v w : 𝔼₂ → ℝ} (hv : 𝒯.IsPiecewisePoly k v)
    (hw : 𝒯.IsPiecewisePoly k w) : 𝒯.IsPiecewisePoly k (v + w) := fun T ↦ by
  obtain ⟨q, hq, hvq⟩ := hv T
  obtain ⟨r, hr, hwr⟩ := hw T
  refine ⟨q + r, (totalDegree_add q r).trans (max_le hq hr), fun x hx ↦ ?_⟩
  rw [Pi.add_apply, hvq x hx, hwr x hx, map_add]

/-- A scalar multiple of a piecewise polynomial of degree at most `k` is one. -/
theorem IsPiecewisePoly.smul {k : ℕ} {v : 𝔼₂ → ℝ} (hv : 𝒯.IsPiecewisePoly k v) (c : ℝ) :
    𝒯.IsPiecewisePoly k (c • v) := fun T ↦ by
  obtain ⟨q, hq, hvq⟩ := hv T
  refine ⟨c • q, (totalDegree_smul_le c q).trans hq, fun x hx ↦ ?_⟩
  rw [Pi.smul_apply, hvq x hx, smul_eval, smul_eq_mul]

variable (𝒯)

/-- A polynomial in the reference coordinates of an element is smooth. -/
theorem contDiff_eval_symm (T : 𝒯.elems) (q : MvPolynomial (Fin 2) ℝ) :
    ContDiff ℝ 1 fun x ↦ eval (fun j ↦ (𝒯.linearPart T).symm (x - T.1 0) j) q := by
  have : (fun x ↦ eval (fun j ↦ (𝒯.linearPart T).symm (x - T.1 0) j) q)
      = evalBasis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis q
        ∘ fun x ↦ (𝒯.linearPart T).symm (x - T.1 0) := by
    funext x
    exact (evalBasis_basisFun q _).symm
  rw [this]
  exact ((contDiff_evalBasis _ q).of_le (by simp)).comp
    ((𝒯.linearPart T).symm.contDiff.comp (contDiff_id.sub contDiff_const))

variable {𝒯}

/-- **A continuous piecewise polynomial lies in `W^{1,p}(Ω)`** for every `1 ≤ p ≤ ∞`
([han2009theoretical] §10.2.3, the conformity `X_h ⊆ H¹(Ω)`): `memSobolev_of_piecewise` with
the polynomial pieces. -/
theorem IsPiecewisePoly.memSobolev {k : ℕ} {v : 𝔼₂ → ℝ}
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (h : 𝒯.IsPiecewisePoly k v) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : MemSobolev v 1 p Ω volume := by
  choose q hq hvq using h
  exact 𝒯.memSobolev_of_piecewise hv
    (g := fun T x ↦ eval (fun j ↦ (𝒯.linearPart T).symm (x - T.1 0) j) (q T))
    (fun T ↦ 𝒯.contDiff_eval_symm T (q T))
    (fun T x hx ↦ hvq T x (𝒯.K_subset_closedK T hx)) p

variable (𝒯)

/-- **The interpolant with polynomial shape functions is piecewise polynomial**: when every
shape function `φ̂ᵢ` is a polynomial of total degree at most `k`, so is every local
interpolant `Π_K v = ∑ᵢ v(F_K x̂ᵢ) φ̂ᵢ ∘ F_K⁻¹` in the reference coordinates, and hence the global
interpolant of a conforming element is piecewise polynomial. -/
theorem globalInterp_isPiecewisePoly {I : ℕ} {xhat : Fin I → 𝔼₂} {φhat : Fin I → 𝔼₂ → ℝ}
    (hconf : 𝒯.IsConformingElement xhat φhat) {k : ℕ}
    (hpoly : ∀ i, ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k ∧
      ∀ x, φhat i x = eval (fun j ↦ x j) q) (v : 𝔼₂ → ℝ) :
    𝒯.IsPiecewisePoly k (𝒯.globalInterp xhat φhat v) := by
  choose q hq hφq using hpoly
  intro T
  refine ⟨∑ i, C (v (𝒯.linearPart T (xhat i) + T.1 0)) * q i, ?_, fun x hx ↦ ?_⟩
  · rw [← mem_restrictTotalDegree]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [C_mul']
    exact Submodule.smul_mem _ _ ((mem_restrictTotalDegree _ _ _).2 (hq i))
  · rw [𝒯.globalInterp_eq_of_mem_closedK xhat φhat hconf T v hx, localInterp_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, eval_C, hφq i, mul_comm]

variable (p : ℝ≥0∞)

/-- **The finite element space `X_h ⊆ H¹(Ω)`** of continuous piecewise polynomials of degree at
most `k` on the triangulation, as a subspace of `W^{1,p}(Ω)`: the elements whose function is,
almost everywhere on `Ω`, a function continuous on `Ω̄` and piecewise polynomial of degree at
most `k` ([han2009theoretical] §10.2.3, §10.4, "affine-equivalent finite element spaces of
piecewise polynomials of degree less than or equal to `k`"). -/
def polySpace (k : ℕ) : Submodule ℝ (SobolevEuclidean 2 1 p Ω) where
  carrier := {w | ∃ v : 𝔼₂ → ℝ, ContinuousOn v (closure (Ω : Set 𝔼₂)) ∧
    𝒯.IsPiecewisePoly k v ∧ SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v}
  add_mem' := by
    rintro w w' ⟨v, hvc, hvp, hvw⟩ ⟨v', hvc', hvp', hvw'⟩
    refine ⟨v + v', hvc.add hvc', hvp.add hvp', (SobolevMultiIndex.fn_add w w').trans ?_⟩
    filter_upwards [hvw, hvw'] with x h1 h2
    simp only [Pi.add_apply, h1, h2]
  zero_mem' := ⟨0, continuousOn_const, IsPiecewisePoly.zero k, SobolevMultiIndex.fn_zero⟩
  smul_mem' := by
    rintro c w ⟨v, hvc, hvp, hvw⟩
    refine ⟨c • v, hvc.const_smul c, hvp.smul c, (SobolevMultiIndex.fn_smul c w).trans ?_⟩
    filter_upwards [hvw] with x h1
    simp only [Pi.smul_apply, h1]

/-- Membership of `X_h`, unfolded. -/
theorem mem_polySpace_iff {k : ℕ} {w : SobolevEuclidean 2 1 p Ω} :
    w ∈ 𝒯.polySpace p k ↔ ∃ v : 𝔼₂ → ℝ, ContinuousOn v (closure (Ω : Set 𝔼₂)) ∧
      𝒯.IsPiecewisePoly k v ∧ SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v :=
  Iff.rfl

/-- **Every continuous piecewise polynomial is the function of an element of `X_h`**: the
space `X_h` is the book's space of continuous piecewise polynomials. -/
theorem exists_mem_polySpace [Fact (1 ≤ p)] {k : ℕ} {v : 𝔼₂ → ℝ}
    (hvc : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hvp : 𝒯.IsPiecewisePoly k v) :
    ∃ w ∈ 𝒯.polySpace p k, SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v := by
  have h := ((hvp.memSobolev hvc p).memSobolevMultiIndex
    (b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)).exists_sobolevMultiIndex
  obtain ⟨u, hu⟩ := h
  exact ⟨u, ⟨v, hvc, hvp, hu⟩, hu⟩

/-! ##### Finite dimensionality

`X_h` is finite-dimensional because an element of `X_h` is determined by its nodal values, once
a conforming element reproducing `ℙ_k` is fixed: the continuous representative `v` of `w ∈ X_h`
is unique (two continuous functions agreeing almost everywhere on the open set `Ω` agree on
`Ω̄`), it satisfies `v = Π_h v` on `Ω̄` (`ℙ_k` reproduction on each element), and `Π_h v` depends
on the nodal values of `v` only. -/

omit 𝒯 in
/-- Two functions continuous on `Ω̄` that are almost everywhere equal on `Ω` agree on `Ω̄`. -/
theorem eqOn_closure_of_ae_eq {v v' : 𝔼₂ → ℝ} (h : v =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v')
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv' : ContinuousOn v' (closure (Ω : Set 𝔼₂))) :
    EqOn v v' (closure (Ω : Set 𝔼₂)) :=
  (Measure.eqOn_open_of_ae_eq h Ω.isOpen (hv.mono subset_closure)
    (hv'.mono subset_closure)).of_subset_closure hv hv' subset_closure subset_rfl

/-- **`ℙ_k` reproduction on the elements**: for a conforming element with nodes in the closed
reference triangle whose reference interpolant reproduces every polynomial of total degree at
most `k`, the global interpolant of a piecewise polynomial of degree at most `k` is that
function on `Ω̄`. -/
theorem globalInterp_eqOn_closure_of_isPiecewisePoly {I : ℕ} {xhat : Fin I → 𝔼₂}
    {φhat : Fin I → 𝔼₂ → ℝ} (hconf : 𝒯.IsConformingElement xhat φhat)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂)) {k : ℕ}
    (hrep : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k → ∀ x : 𝔼₂,
      Approximation.nodalInterp xhat φhat (fun y ↦ eval (fun j ↦ y j) q) x = eval (fun j ↦ x j) q)
    {v : 𝔼₂ → ℝ} (hv : 𝒯.IsPiecewisePoly k v) :
    EqOn (𝒯.globalInterp xhat φhat v) v (closure (Ω : Set 𝔼₂)) := by
  intro x hx'
  rw [𝒯.closure_eq_iUnion_closedK, mem_iUnion] at hx'
  obtain ⟨T, hxT⟩ := hx'
  obtain ⟨q, hq, hvq⟩ := hv T
  rw [𝒯.globalInterp_eq_of_mem_closedK xhat φhat hconf T v hxT, hvq x hxT,
    𝒯.localInterp_eq_nodalInterp_comp, ← hrep q hq]
  simp only [Approximation.nodalInterp_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hvq _ (𝒯.node_mem_closedK xhat hx T i), 𝒯.affine_symm]

/-- The continuous representative of an element of `X_h`. -/
noncomputable def polySpaceRep {k : ℕ} (w : 𝒯.polySpace p k) : 𝔼₂ → ℝ := w.2.choose

/-- The continuous representative is continuous on `Ω̄`. -/
theorem continuousOn_polySpaceRep {k : ℕ} (w : 𝒯.polySpace p k) :
    ContinuousOn (𝒯.polySpaceRep p w) (closure (Ω : Set 𝔼₂)) := w.2.choose_spec.1

/-- The continuous representative is piecewise polynomial. -/
theorem isPiecewisePoly_polySpaceRep {k : ℕ} (w : 𝒯.polySpace p k) :
    𝒯.IsPiecewisePoly k (𝒯.polySpaceRep p w) := w.2.choose_spec.2.1

/-- The continuous representative represents. -/
theorem fn_ae_eq_polySpaceRep {k : ℕ} (w : 𝒯.polySpace p k) :
    SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set 𝔼₂)] 𝒯.polySpaceRep p w := w.2.choose_spec.2.2

/-- The continuous representative is the unique one: any function continuous on `Ω̄`
representing `w` agrees with it on `Ω̄`. -/
theorem polySpaceRep_eqOn {k : ℕ} (w : 𝒯.polySpace p k) {v : 𝔼₂ → ℝ}
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂)))
    (hvw : SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v) :
    EqOn (𝒯.polySpaceRep p w) v (closure (Ω : Set 𝔼₂)) :=
  eqOn_closure_of_ae_eq ((𝒯.fn_ae_eq_polySpaceRep p w).symm.trans hvw)
    (𝒯.continuousOn_polySpaceRep p w) hv

/-- **The nodal values of an element of `X_h`**, as a linear map into `ℝ^{𝒯.elems × I}`: the
values of the continuous representative at the nodes `F_K x̂ᵢ` of the elements. -/
noncomputable def nodalValues {I : ℕ} (xhat : Fin I → 𝔼₂)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂)) (k : ℕ) :
    𝒯.polySpace p k →ₗ[ℝ] (𝒯.elems × Fin I → ℝ) where
  toFun w := fun q ↦ 𝒯.polySpaceRep p w (𝒯.linearPart q.1 (xhat q.2) + q.1.1 0)
  map_add' w w' := by
    funext q
    have hmem := 𝒯.closedK_subset_closure q.1 (𝒯.node_mem_closedK xhat hx q.1 q.2)
    have h := 𝒯.polySpaceRep_eqOn p (w + w') (v := 𝒯.polySpaceRep p w + 𝒯.polySpaceRep p w')
      ((𝒯.continuousOn_polySpaceRep p w).add (𝒯.continuousOn_polySpaceRep p w')) ?_
    · exact h hmem
    · refine (SobolevMultiIndex.fn_add (w : SobolevEuclidean 2 1 p Ω) w').trans ?_
      filter_upwards [𝒯.fn_ae_eq_polySpaceRep p w, 𝒯.fn_ae_eq_polySpaceRep p w'] with x h1 h2
      simp only [Pi.add_apply, h1, h2]
  map_smul' c w := by
    funext q
    have hmem := 𝒯.closedK_subset_closure q.1 (𝒯.node_mem_closedK xhat hx q.1 q.2)
    have h := 𝒯.polySpaceRep_eqOn p (c • w) (v := c • 𝒯.polySpaceRep p w)
      ((𝒯.continuousOn_polySpaceRep p w).const_smul c) ?_
    · exact h hmem
    · refine (SobolevMultiIndex.fn_smul c (w : SobolevEuclidean 2 1 p Ω)).trans ?_
      filter_upwards [𝒯.fn_ae_eq_polySpaceRep p w] with x h1
      simp only [Pi.smul_apply, h1]

/-- **An element of `X_h` is determined by its nodal values**, for a conforming element
reproducing `ℙ_k`: the nodal-value map is injective. -/
theorem nodalValues_injective {I : ℕ} {xhat : Fin I → 𝔼₂} {φhat : Fin I → 𝔼₂ → ℝ}
    (hconf : 𝒯.IsConformingElement xhat φhat)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂)) {k : ℕ}
    (hrep : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k → ∀ x : 𝔼₂,
      Approximation.nodalInterp xhat φhat (fun y ↦ eval (fun j ↦ y j) q) x
        = eval (fun j ↦ x j) q) :
    Function.Injective (𝒯.nodalValues p xhat hx k) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  -- the representative vanishes at every node, hence its interpolant vanishes
  have hint : 𝒯.globalInterp xhat φhat (𝒯.polySpaceRep p w) = 0 := by
    rw [← 𝒯.globalInterp_zero xhat φhat]
    refine 𝒯.globalInterp_congr xhat φhat fun T i ↦ ?_
    exact congrFun hw (T, i)
  -- so the representative vanishes on `Ω̄` by `ℙ_k` reproduction
  have hrep0 : EqOn (𝒯.polySpaceRep p w) 0 (closure (Ω : Set 𝔼₂)) := fun x hx' ↦ by
    rw [← 𝒯.globalInterp_eqOn_closure_of_isPiecewisePoly hconf hx hrep
      (𝒯.isPiecewisePoly_polySpaceRep p w) hx', hint]
  -- hence `w = 0`
  apply Subtype.ext
  refine SobolevMultiIndex.ext_of_fn_ae_eq ((𝒯.fn_ae_eq_polySpaceRep p w).trans ?_)
  refine Filter.EventuallyEq.trans ?_ (SobolevMultiIndex.fn_zero (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)).symm
  refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall fun x hx' ↦ ?_)
  exact hrep0 (subset_closure hx')

/-- **`X_h` is finite-dimensional** once a conforming element with nodes in the closed
reference triangle reproducing `ℙ_k` is given (the `ℙ_k` Lagrange element on the principal
lattice, for instance): its elements are determined by finitely many nodal values. -/
theorem finiteDimensional_polySpace {I : ℕ} {xhat : Fin I → 𝔼₂} {φhat : Fin I → 𝔼₂ → ℝ}
    (hconf : 𝒯.IsConformingElement xhat φhat)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂)) {k : ℕ}
    (hrep : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k → ∀ x : 𝔼₂,
      Approximation.nodalInterp xhat φhat (fun y ↦ eval (fun j ↦ y j) q) x
        = eval (fun j ↦ x j) q) :
    FiniteDimensional ℝ (𝒯.polySpace p k) :=
  FiniteDimensional.of_injective (𝒯.nodalValues p xhat hx k)
    (𝒯.nodalValues_injective p hconf hx hrep)

/-! ##### The space with the homogeneous Dirichlet condition -/

variable [Fact (1 ≤ p)]

/-- **The finite element space `V_h ⊆ H¹₀(Ω)`** of continuous piecewise polynomials of degree
at most `k` vanishing on the boundary, as a subspace of `W_0^{1,p}(Ω)`:

  `V_h = {v_h ∈ C(Ω̄) : v_h|_K ∈ ℙ_k(K) for every K ∈ 𝒯_h, v_h|_∂Ω = 0}`

([quarteroni2000numerical] (12.94), [han2009theoretical] Example 10.4.2). Its elements are the
elements of `W_0^{1,p}(Ω)` whose function is, almost everywhere on `Ω`, such a `v_h`; that every
such `v_h` *is* the function of an element of `W_0^{1,p}(Ω)` is `exists_mem_polySpaceZero`
(Brezis's Theorem 9.17, (i) ⇒ (ii), which needs no regularity of `Ω`). -/
def polySpaceZero (k : ℕ) : Submodule ℝ (SobolevEuclideanZero 2 1 p Ω) where
  carrier := {w | ∃ v : 𝔼₂ → ℝ, ContinuousOn v (closure (Ω : Set 𝔼₂)) ∧
    𝒯.IsPiecewisePoly k v ∧ EqOn v 0 (frontier (Ω : Set 𝔼₂)) ∧
    SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v}
  add_mem' := by
    rintro w w' ⟨v, hvc, hvp, hv0, hvw⟩ ⟨v', hvc', hvp', hv0', hvw'⟩
    refine ⟨v + v', hvc.add hvc', hvp.add hvp', fun x hx ↦ ?_,
      (SobolevMultiIndex.fn_add (w : SobolevEuclidean 2 1 p Ω) w').trans ?_⟩
    · simp only [Pi.add_apply, hv0 hx, hv0' hx, Pi.zero_apply, add_zero]
    · filter_upwards [hvw, hvw'] with x h1 h2
      simp only [Pi.add_apply, h1, h2]
  zero_mem' := ⟨0, continuousOn_const, IsPiecewisePoly.zero k, fun _ _ ↦ rfl,
    SobolevMultiIndex.fn_zero⟩
  smul_mem' := by
    rintro c w ⟨v, hvc, hvp, hv0, hvw⟩
    refine ⟨c • v, hvc.const_smul c, hvp.smul c, fun x hx ↦ ?_,
      (SobolevMultiIndex.fn_smul c (w : SobolevEuclidean 2 1 p Ω)).trans ?_⟩
    · simp only [Pi.smul_apply, hv0 hx, Pi.zero_apply, smul_zero]
    · filter_upwards [hvw] with x h1
      simp only [Pi.smul_apply, h1]

/-- Membership of `V_h`, unfolded. -/
theorem mem_polySpaceZero_iff {k : ℕ} {w : SobolevEuclideanZero 2 1 p Ω} :
    w ∈ 𝒯.polySpaceZero p k ↔ ∃ v : 𝔼₂ → ℝ, ContinuousOn v (closure (Ω : Set 𝔼₂)) ∧
      𝒯.IsPiecewisePoly k v ∧ EqOn v 0 (frontier (Ω : Set 𝔼₂)) ∧
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v :=
  Iff.rfl

/-- An element of `V_h` is, as an element of `W^{1,p}(Ω)`, an element of `X_h`. -/
theorem coe_mem_polySpace_of_mem_polySpaceZero {k : ℕ} {w : SobolevEuclideanZero 2 1 p Ω}
    (hw : w ∈ 𝒯.polySpaceZero p k) : (w : SobolevEuclidean 2 1 p Ω) ∈ 𝒯.polySpace p k := by
  obtain ⟨v, hvc, hvp, -, hvw⟩ := hw
  exact ⟨v, hvc, hvp, hvw⟩

/-- **Every continuous piecewise polynomial vanishing on `∂Ω` is the function of an element of
`V_h ⊆ W_0^{1,p}(Ω)`**, `1 ≤ p < ∞`: it lies in `W^{1,p}(Ω)` by `IsPiecewisePoly.memSobolev`
and in `W_0^{1,p}(Ω)` by [brezis2011functional] Theorem 9.17, (i) ⇒ (ii)
(`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`), with no regularity of
`Ω` — no trace theorem is needed to read the boundary condition `v_h|_∂Ω = 0`. -/
theorem exists_mem_polySpaceZero (hp' : p ≠ ⊤) {k : ℕ} {v : 𝔼₂ → ℝ}
    (hvc : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hvp : 𝒯.IsPiecewisePoly k v)
    (hv0 : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ w ∈ 𝒯.polySpaceZero p k,
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v := by
  have h := ((hvp.memSobolev hvc p).memSobolevMultiIndex
    (b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)).exists_sobolevMultiIndex
  obtain ⟨u, hu⟩ := h
  have hu0 : u ∈ SobolevEuclideanZero 2 1 p Ω :=
    SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier hp' u hu hvc hv0
  exact ⟨⟨u, hu0⟩, ⟨v, hvc, hvp, hv0, hu⟩, hu⟩

/-- **The interpolant of a boundary-vanishing function lies in `V_h`**: for a conforming,
edge-unisolvent element with polynomial shape functions of degree at most `k` on a
triangulation whose boundary is a union of edges, the global interpolant `Π_h v` of a function
`v` continuous on `Ω̄` and vanishing on `∂Ω` is the function of an element of `V_h`, `1 ≤ p < ∞`.
This is the `v_h = Π_h u` step of the finite element error analysis on `H¹₀(Ω)`
([han2009theoretical] Example 10.4.2, [quarteroni2000numerical] Property 12.2). -/
theorem exists_mem_polySpaceZero_globalInterp (hp' : p ≠ ⊤) {I : ℕ} {xhat : Fin I → 𝔼₂}
    {φhat : Fin I → 𝔼₂ → ℝ} (hconf : 𝒯.IsConformingElement xhat φhat)
    (hφ : ∀ i, Continuous (φhat i)) (hunis : IsEdgeUnisolvent xhat φhat) {k : ℕ}
    (hpoly : ∀ i, ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k ∧
      ∀ x, φhat i x = eval (fun j ↦ x j) q)
    (hedge : 𝒯.FrontierSubsetEdges) {v : 𝔼₂ → ℝ} (hv0 : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ w ∈ 𝒯.polySpaceZero p k, SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set 𝔼₂)] 𝒯.globalInterp xhat φhat v :=
  𝒯.exists_mem_polySpaceZero p hp' (𝒯.continuousOn_globalInterp xhat φhat hconf hφ v)
    (𝒯.globalInterp_isPiecewisePoly hconf hpoly v)
    (𝒯.globalInterp_eqOn_frontier xhat φhat hedge hconf hunis hv0)

/-- **`V_h` is finite-dimensional** under the hypotheses of `finiteDimensional_polySpace`: it
embeds in `X_h`. -/
theorem finiteDimensional_polySpaceZero {I : ℕ} {xhat : Fin I → 𝔼₂} {φhat : Fin I → 𝔼₂ → ℝ}
    (hconf : 𝒯.IsConformingElement xhat φhat)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂)) {k : ℕ}
    (hrep : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k → ∀ x : 𝔼₂,
      Approximation.nodalInterp xhat φhat (fun y ↦ eval (fun j ↦ y j) q) x
        = eval (fun j ↦ x j) q) :
    FiniteDimensional ℝ (𝒯.polySpaceZero p k) := by
  have := 𝒯.finiteDimensional_polySpace p hconf hx hrep
  refine FiniteDimensional.of_injective (LinearMap.codRestrict (𝒯.polySpace p k)
    ((SobolevEuclideanZero 2 1 p Ω).subtype.comp (𝒯.polySpaceZero p k).subtype)
    fun w ↦ 𝒯.coe_mem_polySpace_of_mem_polySpaceZero p w.2) fun w w' h ↦ ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

end PolySpace

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
