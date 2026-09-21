import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Zero

/-!
# The kernel of the trace is `W_0^{1,p}(Ω)`

On a bounded `C¹` domain `Ω ⊆ ℝ^{d+1}` and for `1 ≤ p < ∞`, the kernel of the trace operator
`T : W^{1,p}(Ω) →L L^p(∂Ω)` of `Boundary/ContDiffDomain.lean` is `W_0^{1,p}(Ω)`
([brezis2011functional] Comments on chapter 9, 7 (ii); Evans, *PDE*, §5.5, Theorem 2; the
identification `H^1_0(Ω) = {v ∈ H¹(Ω) : γ v = 0}` behind Atkinson–Han's Definition 7.2.9 and the
mixed problems of their §8.5 and §11.4). The inclusion `W_0^{1,p} ⊆ ker T` is
`BoundaryData.TraceFamily.traceL_eq_zero_of_mem_zero` (`Data.lean`, for any trace family); this
module proves the converse and, with it, Evans's strip estimate.

**The route to `ker T ⊆ W_0^{1,p}(Ω)`** is Brezis's, through Proposition 9.18 rather than
Evans's cut-offs: for `u ∈ W^{1,p}(Ω)` with `T u = 0`, Green's formula against a compactly
supported `C¹` test function `φ` on `ℝ^{d+1}` (`IsContDiffDomain.green_contDiff`)
reads `∫_Ω ∂ᵢu φ + ∫_Ω u ∂ᵢφ = ∫ (Tu) φ νᵢ dσ = 0`, i.e. the extension by zero `ū` of `u` has
the extension by zero of `∂ᵢu` as weak derivative on the whole space
(`IsContDiffDomain.hasWeakIteratedLineDerivOn_indicator_of_traceL_eq_zero`), so
`ū ∈ W^{1,p}(ℝ^{d+1})` and Proposition 9.18, (iii) ⇒ (i)
(`SobolevEuclideanZero.mem_of_indicator_memSobolev`, `Numlib/Analysis/Sobolev/Zero.lean`, proved
there on `C¹` chart domains by local charts and one-sided mollification) gives
`u ∈ W_0^{1,p}(Ω)` (`IsContDiffDomain.mem_zero_of_traceL_eq_zero`). No strip estimate, no
partition of unity and no cut-off sequence enter.

**The strip estimate** (Evans §5.5 Theorem 2, (17)) is then proved *for every* `u ∈ W_0^{1,p}(Ω)`
on an arbitrary open set with a graph chart `(T, g)` at `(x₀, r)` — `g` merely continuous — with
the sharp constant `1`: with `S_ρ(t) := Ω ∩ B(x₀, ρ) ∩ {(Tx)_N < g((Tx)') + t}` the strip of
height `t` inside `B(x₀, ρ)`, for `0 < t` and `ρ + t ≤ r`,

  `∫_{S_ρ(t)} |u|^p ≤ t^p ∫_{S_r(t)} |∇u|^p`

(`SobolevEuclideanZero.integral_strip_rpow_le`; the planned
`IsContDiffDomain.integral_strip_rpow_le_of_traceL_eq_zero` is its corollary through the kernel
theorem). For a test function `φ` on `Ω`, in the frame of the chart the function `ψ = φ ∘ T⁻¹`
vanishes on the graph inside `B(T x₀, r)`, so on each vertical line
`ψ(x', g x' + s) = ∫_0^s ∂_N ψ(x', g x' + τ) dτ`; Hölder in `τ` on an interval of length `≤ t`
(`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`) and integration in `s` over an interval of length
`≤ t` give `t^p` (`lintegral_enorm_rpow_le_of_hasDerivAt`, the one-variable core); Fubini in
the last coordinate (`EuclideanSpace.lintegral_lastInit`) and the rigid motion assemble the
estimate in `ℝ≥0∞` form (`EuclideanSpace.lintegral_graphStrip_le`,
`TestFunction.lintegral_strip_le`), where no integrability enters. Both sides are continuous in
`u` (the restricted function through `Lp.monoMeasureL ∘ fnL`, the restricted pointwise gradient
through the bounded map `SobolevEuclidean.gradFnL`), and the test functions are dense in
`W_0^{1,p}(Ω)`.

## Main statements

* `IsContDiffDomain.mem_zero_of_traceL_eq_zero`, `IsContDiffDomain.traceL_eq_zero_iff_mem_zero`:
  `ker T = W_0^{1,p}(Ω)` on a bounded `C¹` domain;
* `SobolevEuclideanZero.integral_strip_rpow_le`,
  `IsContDiffDomain.integral_strip_rpow_le_of_traceL_eq_zero`: the strip estimate;
* `SobolevEuclidean.gradFnL`: the restricted pointwise gradient as a bounded linear map
  `W^{1,p}(Ω) → L^p(S; ℝ^N)`.

## References

[brezis2011functional] Comments on chapter 9, 7 (ii), Proposition 9.18; Evans, *Partial
Differential Equations*, §5.5, Theorem 2; Atkinson–Han, *Theoretical Numerical Analysis*,
Definition 7.2.9 and Theorem 7.3.11.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal Topology
open SobolevMultiIndex

noncomputable section

/-! ### General lemmas

The lemmas of this section are general (Mathlib-facing or belonging to earlier modules); they are
listed for relocation in the report. -/

section General

/-- `∫ ‖f‖^P = (∫⁻ ‖f‖ₑ^P).toReal` for `0 ≤ P` and `f` almost everywhere strongly measurable. -/
theorem MeasureTheory.integral_norm_rpow_eq_toReal_lintegral {α G : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup G] {f : α → G} (hf : AEStronglyMeasurable f μ) {P : ℝ}
    (hP : 0 ≤ P) : ∫ x, ‖f x‖ ^ P ∂μ = (∫⁻ x, ‖f x‖ₑ ^ P ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x ↦ by positivity)
    (hf.norm.aemeasurable.pow_const P).aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP]

/-- **The one-variable core of the strip estimate**: for `f` with `f a = 0` and continuous
derivative `f'`, and sets `I`, `J` of the interval `(a, a + t)` with `(a, s] ⊆ J` for every
`s ∈ I`, `∫_I |f|^P ≤ t^P ∫_J |f'|^P` for `1 ≤ P`. On `I`, `f s = ∫_a^s f'` is bounded by
`∫_J |f'|`, which Hölder bounds by `(vol J)^{1 − 1/P} (∫_J |f'|^P)^{1/P}`
(`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`), and `vol I, vol J ≤ t`. -/
theorem lintegral_enorm_rpow_le_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {a t : ℝ} (ht : 0 < t) (hfa : f a = 0) {I J : Set ℝ}
    (hI : I ⊆ Ioo a (a + t)) (hJ : J ⊆ Ioo a (a + t)) (hIJ : ∀ s ∈ I, Ioc a s ⊆ J)
    {P : ℝ} (hP : 1 ≤ P) :
    ∫⁻ s in I, ‖f s‖ₑ ^ P ≤ ENNReal.ofReal t ^ P * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
  have hvol : volume (Ioo a (a + t)) = ENNReal.ofReal t := by
    rw [Real.volume_Ioo, add_sub_cancel_left]
  have hm : AEStronglyMeasurable f' (volume.restrict J) := hf'.aestronglyMeasurable
  -- Hölder on `J`
  have hH : ∫⁻ τ in J, ‖f' τ‖ₑ
      ≤ (∫⁻ τ in J, ‖f' τ‖ₑ ^ P) ^ (1 / P) * ENNReal.ofReal t ^ (1 - 1 / P) := by
    have h1P : (1 : ℝ≥0∞) ≤ ENNReal.ofReal P := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hP
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict J) (f := f')
      (p := 1) (q := ENNReal.ofReal P) h1P hm
    rw [eLpNorm_one_eq_lintegral_enorm hm, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by simpa using hP0) ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal hP0.le,
      ENNReal.toReal_one, div_one, Measure.restrict_apply_univ] at h
    refine h.trans ?_
    gcongr
    · rw [sub_nonneg, div_le_one hP0]
      exact hP
    · exact (measure_mono hJ).trans hvol.le
  -- the pointwise bound on `I`
  have hpt : ∀ s ∈ I, ‖f s‖ₑ ^ P
      ≤ ENNReal.ofReal t ^ (P - 1) * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P := by
    intro s hs
    have has : a ≤ s := (hI hs).1.le
    have e : f s = ∫ τ in a..s, f' τ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ ↦ hf τ)
        (hf'.intervalIntegrable _ _), hfa, sub_zero]
    have h1 : ‖f s‖ₑ ≤ ∫⁻ τ in J, ‖f' τ‖ₑ := by
      rw [e, intervalIntegral.integral_of_le has]
      exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set (hIJ s hs))
    calc ‖f s‖ₑ ^ P
        ≤ ((∫⁻ τ in J, ‖f' τ‖ₑ ^ P) ^ (1 / P) * ENNReal.ofReal t ^ (1 - 1 / P)) ^ P :=
          ENNReal.rpow_le_rpow (h1.trans hH) hP0.le
      _ = ENNReal.ofReal t ^ (P - 1) * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            one_div_mul_cancel hP0.ne', ENNReal.rpow_one, mul_comm]
          congr 2
          field_simp
  calc ∫⁻ s in I, ‖f s‖ₑ ^ P
      ≤ ∫⁻ _ in I, ENNReal.ofReal t ^ (P - 1) * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P :=
        setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal t ^ (P - 1) * (∫⁻ τ in J, ‖f' τ‖ₑ ^ P) * volume I :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal t ^ (P - 1) * (∫⁻ τ in J, ‖f' τ‖ₑ ^ P) * ENNReal.ofReal t := by
        gcongr
        exact (measure_mono hI).trans hvol.le
    _ = ENNReal.ofReal t ^ P * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P := by
        have e : ENNReal.ofReal t ^ P = ENNReal.ofReal t * ENNReal.ofReal t ^ (P - 1) := by
          conv_lhs => rw [show P = 1 + (P - 1) by ring]
          rw [ENNReal.rpow_add _ _ ht0 ENNReal.ofReal_ne_top, ENNReal.rpow_one]
        rw [e]
        ring

/-- Two points of a vertical line: `‖(x', s) − (x', t)‖ = |s − t|`. -/
theorem EuclideanSpace.norm_snocLast_sub_snocLast {d : ℕ} (x' : EuclideanSpace ℝ (Fin d))
    (s t : ℝ) : ‖EuclideanSpace.snocLast x' s - EuclideanSpace.snocLast x' t‖ = |s - t| := by
  have h := EuclideanSpace.norm_sq_eq_init_add_last
    (EuclideanSpace.snocLast x' s - EuclideanSpace.snocLast x' t)
  simp only [EuclideanSpace.init_sub, EuclideanSpace.init_snocLast, sub_self, norm_zero,
    PiLp.sub_apply, EuclideanSpace.snocLast_apply_last, zero_pow two_ne_zero, zero_add] at h
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq_eq_abs]

end General

/-! ### The restricted pointwise gradient as a bounded linear map -/

section GradFnL

variable {N : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-- **The pointwise gradient restricted to `S ⊆ Ω`, as a bounded linear map**
`W^{1,p}(Ω) → L^p(S; ℝ^N)`, `u ↦ ∇u|_S = (∂ᵢu|_S)ᵢ`: the sum over `i` of the partial
derivatives (`weakDerivL`), restricted to `S` (`Lp.monoMeasureL`) and placed on the `i`-th axis
(`ContinuousLinearMap.compLpL` with `toSpanSingleton`). Its function is `gradFn u` on `S`
(`SobolevEuclidean.coeFn_gradFnL`), so `∫_S |∇u|^p = ‖gradFnL u‖^p` is continuous in `u`. -/
def SobolevEuclidean.gradFnL {S : Set (EuclideanSpace ℝ (Fin N))} (hS : S ⊆ Ω) :
    SobolevEuclidean N 1 p Ω →L[ℝ] Lp (EuclideanSpace ℝ (Fin N)) p (volume.restrict S) :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).compLpL p
    (volume.restrict S) ∘L Lp.monoMeasureL (Measure.restrict_mono hS le_rfl) ∘L
      weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (MultiIndexLE.single i)

variable {p Ω}

/-- The function of `gradFnL u` is the pointwise gradient `gradFn u`, almost everywhere on `S`. -/
theorem SobolevEuclidean.coeFn_gradFnL {S : Set (EuclideanSpace ℝ (Fin N))} (hS : S ⊆ Ω)
    (u : SobolevEuclidean N 1 p Ω) :
    ⇑(SobolevEuclidean.gradFnL p Ω hS u) =ᵐ[volume.restrict S] gradFn u := by
  rw [SobolevEuclidean.gradFnL, sum_apply]
  have h1 := Lp.coeFn_finsetSum (μ := volume.restrict S) Finset.univ fun i ↦
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).compLpL p
      (volume.restrict S) (Lp.monoMeasureL (Measure.restrict_mono hS le_rfl)
        (weakDeriv u (MultiIndexLE.single i)))
  have h2 := ae_all_iff.2 fun i : Fin N ↦
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).coeFn_compLpL
      (p := p) (μ := volume.restrict S)
      (Lp.monoMeasureL (Measure.restrict_mono hS le_rfl) (weakDeriv u (MultiIndexLE.single i)))
  have h3 := ae_all_iff.2 fun i : Fin N ↦ Lp.coeFn_monoMeasureL
    (Measure.restrict_mono hS le_rfl) (weakDeriv u (MultiIndexLE.single i))
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  simp only [ContinuousLinearMap.comp_apply, weakDerivL_apply] at hx1 ⊢
  rw [hx1, Finset.sum_apply]
  simp only [hx2, hx3, ContinuousLinearMap.toSpanSingleton_apply]
  ext j
  simp [gradFn, Pi.single_apply]

/-- `∫_S |∇u|^p = ‖gradFnL u‖^p` for `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, `S ⊆ Ω`. -/
theorem SobolevEuclidean.integral_norm_gradFn_rpow_eq (hp : p ≠ ⊤)
    {S : Set (EuclideanSpace ℝ (Fin N))} (hS : S ⊆ Ω) (u : SobolevEuclidean N 1 p Ω) :
    ∫ x in S, ‖gradFn u x‖ ^ p.toReal = ‖SobolevEuclidean.gradFnL p Ω hS u‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  rw [Lp.norm_rpow_eq_integral hp0 hp]
  refine integral_congr_ae ?_
  filter_upwards [SobolevEuclidean.coeFn_gradFnL hS u] with x hx
  rw [hx]

end GradFnL

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-! ### The kernel of the trace -/

namespace IsContDiffDomain

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- **The extension by zero of a function with zero trace has the extension by zero of its
partial derivative as weak derivative on the whole space**: for `u ∈ W^{1,p}(Ω)` on a bounded
`C¹` domain with `T u = 0`, `1 ≤ p < ∞`, and every `i`,
`∂ᵢ(Ω.indicator u) = Ω.indicator (∂ᵢu)` weakly on `ℝ^{d+1}`. Green's formula against a test
function `φ` (`IsContDiffDomain.green_contDiff`) has a vanishing boundary term. -/
theorem hasWeakIteratedLineDerivOn_indicator_of_traceL_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : hΩ.traceL hb p hp u = 0)
    (i : Fin (d + 1)) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single i (1 : ℝ)]
      ((Ω : Set 𝔼).indicator (fn u))
      ((Ω : Set 𝔼).indicator (weakDeriv u (MultiIndexLE.single i))) ⊤ volume where
  locallyIntegrableOn :=
    ((SobolevMultiIndexZero.memLp_indicator_fn u).locallyIntegrable Fact.out).locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv :=
    ((SobolevMultiIndexZero.memLp_indicator_weakDeriv u _).locallyIntegrable
      Fact.out).locallyIntegrableOn _
  integral_smul_eq φ := by
    have hG := hΩ.green_contDiff hb p hp u (φ.contDiff.of_le (by simp)) φ.hasCompactSupport i
    have h0 : ∫ x, (hΩ.traceL hb p hp u : 𝔼 → ℝ) x * φ x * hΩ.outwardNormal hb x i
        ∂(hΩ.boundaryMeasure hb) = 0 := by
      rw [hu]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [Lp.coeFn_zero ℝ p (hΩ.boundaryMeasure hb)] with x hx
      rw [hx, Pi.zero_apply, zero_mul, zero_mul]
    rw [h0] at hG
    have hΩm := Ω.isOpen.measurableSet
    simp only [Opens.coe_top, Measure.restrict_univ, iteratedFDeriv_one_apply,
      Matrix.cons_val_zero, smul_eq_mul, pow_one]
    have e1 : (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) * (Ω : Set 𝔼).indicator (fn u) x)
        = (Ω : Set 𝔼).indicator fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) * fn u x := by
      funext x
      rw [Set.indicator_mul_right]
    have e2 : (fun x ↦ φ x * (Ω : Set 𝔼).indicator (weakDeriv u (MultiIndexLE.single i)) x)
        = (Ω : Set 𝔼).indicator fun x ↦ φ x * weakDeriv u (MultiIndexLE.single i) x := by
      funext x
      rw [Set.indicator_mul_right]
    rw [e1, e2, integral_indicator hΩm, integral_indicator hΩm]
    have e3 : ∫ x in (Ω : Set 𝔼), fderiv ℝ φ x (EuclideanSpace.single i 1) * fn u x
        = ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    have e4 : ∫ x in (Ω : Set 𝔼), φ x * weakDeriv u (MultiIndexLE.single i) x
        = ∫ x in (Ω : Set 𝔼), weakDeriv u (MultiIndexLE.single i) x * φ x :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    rw [e3, e4]
    linarith

/-- **The extension by zero of a function with zero trace lies in `W^{1,p}(ℝ^{d+1})`**
([brezis2011functional] Proposition 9.18 (iii) for `u ∈ ker T`): from
`hasWeakIteratedLineDerivOn_indicator_of_traceL_eq_zero` and the `L^p` memberships of the
extensions by zero. -/
theorem indicator_memSobolevMultiIndex_of_traceL_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : hΩ.traceL hb p hp u = 0) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set 𝔼).indicator (fn u)) 1 p ⊤ volume := by
  refine SobolevEuclidean.memSobolevMultiIndex_one_of_forall (Ω := ⊤) ?_
    (G := fun i ↦ (Ω : Set 𝔼).indicator (weakDeriv u (MultiIndexLE.single i))) (fun i ↦ ?_)
    fun i ↦ hΩ.hasWeakIteratedLineDerivOn_indicator_of_traceL_eq_zero hb p hp hu i
  · simpa only [Opens.coe_top, Measure.restrict_univ] using
      SobolevMultiIndexZero.memLp_indicator_fn u
  · simpa only [Opens.coe_top, Measure.restrict_univ] using
      SobolevMultiIndexZero.memLp_indicator_weakDeriv u (MultiIndexLE.single i)

/-- **`ker T ⊆ W_0^{1,p}(Ω)`** on a bounded `C¹` domain, `1 ≤ p < ∞` ([brezis2011functional]
Comments on chapter 9, 7 (ii); Evans §5.5 Theorem 2): a `W^{1,p}(Ω)` function with zero trace
lies in `W_0^{1,p}(Ω)`. Its extension by zero lies in `W^{1,p}(ℝ^{d+1})`
(`indicator_memSobolevMultiIndex_of_traceL_eq_zero`), so Proposition 9.18, (iii) ⇒ (i)
(`SobolevEuclideanZero.mem_of_indicator_memSobolev`, on the `C¹` chart domain
`hΩ.isContDiffChartDomain`) produces an element of `W_0^{1,p}(Ω)` with the same function, which
is `u` (`SobolevMultiIndex.ext_of_fn_ae_eq`). -/
theorem mem_zero_of_traceL_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : hΩ.traceL hb p hp u = 0) :
    u ∈ SobolevEuclideanZero (d + 1) 1 p Ω := by
  obtain ⟨v, hv, hvu⟩ := SobolevEuclideanZero.mem_of_indicator_memSobolev hp
    hΩ.isContDiffChartDomain (hΩ.indicator_memSobolevMultiIndex_of_traceL_eq_zero hb p hp hu)
  rwa [SobolevMultiIndex.ext_of_fn_ae_eq hvu] at hv

/-- **`ker T = W_0^{1,p}(Ω)`** on a bounded `C¹` domain, `1 ≤ p < ∞` ([brezis2011functional]
Comments on chapter 9, 7 (ii); Atkinson–Han's `H^1_0(Ω) = {v : γ v = 0}`):
`T u = 0 ↔ u ∈ W_0^{1,p}(Ω)`, from `mem_zero_of_traceL_eq_zero` and
`traceL_eq_zero_of_mem_zero`. -/
theorem traceL_eq_zero_iff_mem_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    hΩ.traceL hb p hp u = 0 ↔ u ∈ SobolevEuclideanZero (d + 1) 1 p Ω :=
  ⟨hΩ.mem_zero_of_traceL_eq_zero hb p hp, hΩ.traceL_eq_zero_of_mem_zero hb p hp⟩

end IsContDiffDomain

/-! ### The strip estimate in the frame of a graph -/

namespace EuclideanSpace

/-- **The strip of height `t` above the graph of `g`**, `{y | g y' < y_N < g y' + t}`, in the
frame of the graph. -/
def graphStrip (g : 𝔼' → ℝ) (t : ℝ) : Set 𝔼 :=
  {y | g (init y) < y (Fin.last d) ∧ y (Fin.last d) < g (init y) + t}

/-- The strip above the graph of a continuous function is open. -/
theorem isOpen_graphStrip {g : 𝔼' → ℝ} (hg : Continuous g) (t : ℝ) : IsOpen (graphStrip g t) :=
  (isOpen_lt (hg.comp continuous_init) continuous_apply_last).inter
    (isOpen_lt continuous_apply_last ((hg.comp continuous_init).add continuous_const))

/-- The point `(x', s)` lies in the strip iff `g x' < s < g x' + t`. -/
theorem snocLast_mem_graphStrip {g : 𝔼' → ℝ} {t : ℝ} (x' : 𝔼') (s : ℝ) :
    snocLast x' s ∈ graphStrip g t ↔ g x' < s ∧ s < g x' + t := by
  simp [graphStrip]

/-- **The strip estimate in the frame of the graph**, for a `C¹` function `ψ` vanishing on the
graph of the continuous `g` inside `B(c, r)`: for `0 < t` and `ρ + t ≤ r`,
`∫_{B(c,ρ) ∩ strip_t} |ψ|^P ≤ t^P ∫_{B(c,r) ∩ strip_t} |∂_N ψ|^P` (`1 ≤ P`). Fubini in the last
coordinate (`lintegral_lastInit`); on the vertical line through `x'`, if it meets the small
strip then its foot `(x', g x')` lies in `B(c, r)`, so `ψ(x', g x') = 0`, and the segments from
the foot to the points of the small strip lie in the large one, which is what the one-variable
core `lintegral_enorm_rpow_le_of_hasDerivAt` needs. -/
theorem lintegral_graphStrip_le {ψ : 𝔼 → ℝ} (hψ : ContDiff ℝ 1 ψ) {g : 𝔼' → ℝ}
    (hg : Continuous g) {c : 𝔼} {r ρ t : ℝ} (ht : 0 < t) (hρt : ρ + t ≤ r)
    (h0 : ∀ y ∈ Metric.ball c r, y (Fin.last d) = g (init y) → ψ y = 0) {P : ℝ} (hP : 1 ≤ P) :
    ∫⁻ y in Metric.ball c ρ ∩ graphStrip g t, ‖ψ y‖ₑ ^ P
      ≤ ENNReal.ofReal t ^ P * ∫⁻ y in Metric.ball c r ∩ graphStrip g t,
          ‖fderiv ℝ ψ y (single (Fin.last d) 1)‖ₑ ^ P := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hSρ : MeasurableSet (Metric.ball c ρ ∩ graphStrip g t) :=
    (Metric.isOpen_ball.inter (isOpen_graphStrip hg t)).measurableSet
  have hSr : MeasurableSet (Metric.ball c r ∩ graphStrip g t) :=
    (Metric.isOpen_ball.inter (isOpen_graphStrip hg t)).measurableSet
  have hF : Measurable fun y : 𝔼 ↦ ‖ψ y‖ₑ ^ P := hψ.continuous.measurable.enorm.pow_const _
  have hG : Measurable fun y : 𝔼 ↦ ‖fderiv ℝ ψ y (single (Fin.last d) 1)‖ₑ ^ P :=
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable.enorm.pow_const _
  rw [← lintegral_indicator hSρ, ← lintegral_indicator hSr,
    lintegral_lastInit _ (hF.indicator hSρ).aemeasurable,
    lintegral_lastInit _ (hG.indicator hSr).aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hP0.le ENNReal.ofReal_ne_top)]
  refine lintegral_mono fun x' ↦ ?_
  have hline : Continuous fun s : ℝ ↦ snocLast x' s :=
    continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_snocLast x' s).continuousAt
  have hIm : MeasurableSet ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c ρ ∩ graphStrip g t)) :=
    hSρ.preimage hline.measurable
  have hJm : MeasurableSet ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c r ∩ graphStrip g t)) :=
    hSr.preimage hline.measurable
  have e1 : (fun s : ℝ ↦ (Metric.ball c ρ ∩ graphStrip g t).indicator
      (fun y ↦ ‖ψ y‖ₑ ^ P) (snocLast x' s))
      = ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c ρ ∩ graphStrip g t)).indicator
          fun s ↦ ‖ψ (snocLast x' s)‖ₑ ^ P := by
    funext s
    exact (Set.indicator_comp_right (fun s : ℝ ↦ snocLast x' s)).symm
  have e2 : (fun s : ℝ ↦ (Metric.ball c r ∩ graphStrip g t).indicator
      (fun y ↦ ‖fderiv ℝ ψ y (single (Fin.last d) 1)‖ₑ ^ P) (snocLast x' s))
      = ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c r ∩ graphStrip g t)).indicator
          fun s ↦ ‖fderiv ℝ ψ (snocLast x' s) (single (Fin.last d) 1)‖ₑ ^ P := by
    funext s
    exact (Set.indicator_comp_right (fun s : ℝ ↦ snocLast x' s)).symm
  simp only
  rw [e1, e2, lintegral_indicator hIm, lintegral_indicator hJm]
  -- the vertical line may miss the small strip
  by_cases hne : ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c ρ ∩ graphStrip g t)).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  obtain ⟨s₀, hs₀⟩ := hne
  -- the foot `(x', g x')` of the line lies in `B(c, r)`
  have hfoot : snocLast x' (g x') ∈ Metric.ball c r := by
    simp only [Set.mem_preimage, Set.mem_inter_iff, snocLast_mem_graphStrip] at hs₀
    have h1 : dist (snocLast x' (g x')) (snocLast x' s₀) < t := by
      rw [dist_eq_norm, norm_snocLast_sub_snocLast, abs_sub_comm,
        abs_of_pos (by linarith [hs₀.2.1])]
      linarith [hs₀.2.2]
    have h2 := hs₀.1
    rw [Metric.mem_ball] at h2 ⊢
    linarith [dist_triangle (snocLast x' (g x')) (snocLast x' s₀) c]
  refine lintegral_enorm_rpow_le_of_hasDerivAt (f := fun s ↦ ψ (snocLast x' s))
    (f' := fun s ↦ fderiv ℝ ψ (snocLast x' s) (single (Fin.last d) 1)) (a := g x') (fun s ↦ ?_) ?_
    ht ?_ ?_ ?_ ?_ hP
  · exact (hψ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_snocLast x' s)
  · exact ((hψ.continuous_fderiv one_ne_zero).comp hline).clm_apply continuous_const
  · exact h0 _ hfoot (by simp)
  · intro s hs
    simp only [Set.mem_preimage, Set.mem_inter_iff, snocLast_mem_graphStrip] at hs
    exact hs.2
  · intro s hs
    simp only [Set.mem_preimage, Set.mem_inter_iff, snocLast_mem_graphStrip] at hs
    exact hs.2
  · intro s hs τ hτ
    simp only [Set.mem_preimage, Set.mem_inter_iff, snocLast_mem_graphStrip] at hs ⊢
    refine ⟨?_, hτ.1, by linarith [hτ.2, hs.2.2]⟩
    have h1 : dist (snocLast x' τ) (snocLast x' s) < t := by
      rw [dist_eq_norm, norm_snocLast_sub_snocLast, abs_sub_comm,
        abs_of_nonneg (by linarith [hτ.2])]
      linarith [hτ.1, hs.2.2]
    have h2 := hs.1
    rw [Metric.mem_ball] at h2 ⊢
    linarith [dist_triangle (snocLast x' τ) (snocLast x' s) c]

end EuclideanSpace

/-! ### The strip estimate on `W_0^{1,p}(Ω)` -/

/-- **The strip estimate for a test function on `Ω`**, in the original frame: for an open `Ω`
with a graph chart `(T, g)` at `(x₀, r)` (`Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' epigraph g`, `g`
continuous), `φ ∈ C_c^∞(Ω)`, `0 < t`, `ρ + t ≤ r` and `1 ≤ P`,
`∫_{S_ρ(t)} |φ|^P ≤ t^P ∫_{S_r(t)} |∂_e φ|^P`, with
`S_ρ(t) := Ω ∩ B(x₀, ρ) ∩ {(Tx)_N < g((Tx)') + t}` and `e = T.linear⁻¹ e_N` the upward direction
of the chart. The function `φ ∘ T⁻¹` vanishes
on the graph inside `B(T x₀, r)` (`IsBoundaryGraphAt.frontier_inter_ball`), the small strip
maps into `B(T x₀, ρ) ∩ strip_t` and `B(T x₀, r) ∩ strip_t` maps into the large strip
(`EuclideanSpace.lintegral_graphStrip_le`, the rigid motion preserving Lebesgue measure). -/
theorem TestFunction.lintegral_strip_le {Ω : Opens 𝔼} (φ : 𝓓(Ω, ℝ)) (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼)
    {g : 𝔼' → ℝ} (hg : Continuous g) {x₀ : 𝔼} {r ρ t : ℝ}
    (h : (Ω : Set 𝔼) ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    (ht : 0 < t) (hρt : ρ + t ≤ r) {P : ℝ} (hP : 1 ≤ P) :
    ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, ‖φ x‖ₑ ^ P
      ≤ ENNReal.ofReal t ^ P
        * ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
            ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖fderiv ℝ φ x (T.linearIsometryEquiv.symm (EuclideanSpace.single (Fin.last d) 1))‖ₑ
            ^ P := by
  have hψ : ContDiff ℝ 1 (φ ∘ T.symm) :=
    (φ.contDiff.of_le (by simp)).comp T.symm.toAffineIsometry.toContinuousAffineMap.contDiff
  have hTe := T.toHomeomorph.measurableEmbedding
  have hmp := T.measurePreserving
  -- the derivative of `φ ∘ T⁻¹` along `e_N`
  have hderiv : ∀ x, fderiv ℝ (φ ∘ T.symm) (T x) (EuclideanSpace.single (Fin.last d) 1)
      = fderiv ℝ φ x (T.linearIsometryEquiv.symm (EuclideanSpace.single (Fin.last d) 1)) := by
    intro x
    have h1 : HasFDerivAt φ (fderiv ℝ φ x) (T.symm (T x)) := by
      rw [T.symm_apply_apply]
      exact ((φ.contDiff.differentiable (by simp)) x).hasFDerivAt
    have h2 := h1.comp (T x) (T.symm.hasFDerivAt (T x))
    rw [h2.fderiv]
    rfl
  -- the two strips
  have hsub1 : (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
      ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}
      ⊆ T ⁻¹' (Metric.ball (T x₀) ρ ∩ EuclideanSpace.graphStrip g t) := by
    rintro x ⟨⟨hxΩ, hxρ⟩, hxt⟩
    have hxr : x ∈ Metric.ball x₀ r := Metric.ball_subset_ball (by linarith) hxρ
    have hx : x ∈ Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g := h ▸ ⟨hxΩ, hxr⟩
    refine ⟨?_, hx.2, hxt⟩
    rw [Metric.mem_ball, T.dist_map]
    exact hxρ
  have hsub2 : T ⁻¹' (Metric.ball (T x₀) r ∩ EuclideanSpace.graphStrip g t)
      ⊆ (Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t} := by
    rintro x ⟨hxr, hx1, hx2⟩
    have hxr' : x ∈ Metric.ball x₀ r := by
      rw [Metric.mem_ball, T.dist_map] at hxr
      exact hxr
    have hx : x ∈ (Ω : Set 𝔼) ∩ Metric.ball x₀ r := h.symm ▸ ⟨hxr', hx1⟩
    exact ⟨hx, hx2⟩
  -- `φ ∘ T⁻¹` vanishes on the graph inside the ball
  have h0 : ∀ y ∈ Metric.ball (T x₀) r, y (Fin.last d) = g (EuclideanSpace.init y) →
      (φ ∘ T.symm) y = 0 := by
    intro y hy hyg
    have hfr : T.symm y ∈ frontier (Ω : Set 𝔼) := by
      have h2 := IsBoundaryGraphAt.frontier_inter_ball hg h
      have h3 : T.symm y ∈ Metric.ball x₀ r
          ∩ T ⁻¹' {y | y (Fin.last d) = g (EuclideanSpace.init y)} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, ← T.dist_map, T.apply_symm_apply]
          exact hy
        · rw [Set.mem_preimage, T.apply_symm_apply]
          exact hyg
      rw [← h2] at h3
      exact h3.1
    exact φ.eq_zero_of_notMem fun hmem ↦ hfr.2 (by rwa [Ω.isOpen.interior_eq])
  have e1 : (fun x ↦ ‖φ x‖ₑ ^ P) = fun x ↦ ‖(φ ∘ T.symm) (T x)‖ₑ ^ P := by
    funext x
    simp
  calc ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, ‖φ x‖ₑ ^ P
      ≤ ∫⁻ x in T ⁻¹' (Metric.ball (T x₀) ρ ∩ EuclideanSpace.graphStrip g t),
          ‖(φ ∘ T.symm) (T x)‖ₑ ^ P := by
        rw [e1]
        exact lintegral_mono_set hsub1
    _ = ∫⁻ y in Metric.ball (T x₀) ρ ∩ EuclideanSpace.graphStrip g t, ‖(φ ∘ T.symm) y‖ₑ ^ P :=
        hmp.setLIntegral_comp_preimage_emb hTe (fun y ↦ ‖(φ ∘ T.symm) y‖ₑ ^ P) _
    _ ≤ ENNReal.ofReal t ^ P * ∫⁻ y in Metric.ball (T x₀) r ∩ EuclideanSpace.graphStrip g t,
          ‖fderiv ℝ (φ ∘ T.symm) y (EuclideanSpace.single (Fin.last d) 1)‖ₑ ^ P :=
        EuclideanSpace.lintegral_graphStrip_le hψ hg ht hρt h0 hP
    _ = ENNReal.ofReal t ^ P
        * ∫⁻ x in T ⁻¹' (Metric.ball (T x₀) r ∩ EuclideanSpace.graphStrip g t),
          ‖fderiv ℝ (φ ∘ T.symm) (T x) (EuclideanSpace.single (Fin.last d) 1)‖ₑ ^ P := by
        rw [hmp.setLIntegral_comp_preimage_emb hTe
          (fun y ↦ ‖fderiv ℝ (φ ∘ T.symm) y (EuclideanSpace.single (Fin.last d) 1)‖ₑ ^ P)]
    _ ≤ ENNReal.ofReal t ^ P
        * ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
            ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖fderiv ℝ φ x (T.linearIsometryEquiv.symm (EuclideanSpace.single (Fin.last d) 1))‖ₑ
            ^ P := by
        refine mul_le_mul' le_rfl ?_
        simp_rw [hderiv]
        exact lintegral_mono_set hsub2

/-- **The strip estimate on `W_0^{1,p}(Ω)`** (Evans §5.5 Theorem 2, (17), with constant `1`):
for an open `Ω ⊆ ℝ^{d+1}` with a graph chart `(T, g)` at `(x₀, r)` (`g` continuous),
`u ∈ W_0^{1,p}(Ω)`, `1 ≤ p < ∞`, `0 < t` and `ρ + t ≤ r`,
`∫_{S_ρ(t)} |u|^p ≤ t^p ∫_{S_r(t)} |∇u|^p` with `S_ρ(t) := Ω ∩ B(x₀, ρ) ∩ {(Tx)_N < g((Tx)') + t}`.
For the test functions `TestFunction.lintegral_strip_le` bounds the vertical derivative
`|∂_e φ| ≤ |∇φ|`; both sides are continuous in `u` (`Lp.monoMeasureL ∘ fnL`,
`SobolevEuclidean.gradFnL`) and the test functions are dense in `W_0^{1,p}(Ω)`
(`SobolevMultiIndexZero.exists_seq_testFunction_tendsto`). -/
theorem SobolevEuclideanZero.integral_strip_rpow_le {Ω : Opens 𝔼} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p Ω)
    (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {g : 𝔼' → ℝ} (hg : Continuous g) {x₀ : 𝔼} {r ρ t : ℝ}
    (h : (Ω : Set 𝔼) ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    (ht : 0 < t) (hρt : ρ + t ≤ r) :
    ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, |fn u x| ^ p.toReal
      ≤ t ^ p.toReal * ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
          ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖gradFn u x‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_ne_top hp
  have hP0 : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hSρ : (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
      ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t} ⊆ Ω :=
    fun x hx ↦ hx.1.1
  have hSr : (Ω : Set 𝔼) ∩ Metric.ball x₀ r
      ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t} ⊆ Ω :=
    fun x hx ↦ hx.1.1
  -- the two sides as continuous functions of `u`
  obtain ⟨L, hL⟩ : ∃ L : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] Lp ℝ p (volume.restrict
      ((Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t})),
      L = Lp.monoMeasureL (Measure.restrict_mono hSρ le_rfl) ∘L
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume := ⟨_, rfl⟩
  have hLeq : ∀ v : SobolevEuclidean (d + 1) 1 p Ω, ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
      ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, |fn v x| ^ p.toReal
      = ‖L v‖ ^ p.toReal := by
    intro v
    rw [Lp.norm_rpow_eq_integral hp0 hp, hL]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_monoMeasureL (Measure.restrict_mono hSρ le_rfl)
      (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume v)] with x hx
    rw [ContinuousLinearMap.comp_apply, hx, fnL_apply, Real.norm_eq_abs]
  have hΓeq := fun v ↦ SobolevEuclidean.integral_norm_gradFn_rpow_eq hp hSr v
  simp_rw [hLeq, hΓeq]
  -- the estimate on the test functions
  obtain ⟨w, φ, hφ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hu
  have key : ∀ n, ‖L (w n)‖ ^ p.toReal
      ≤ t ^ p.toReal * ‖SobolevEuclidean.gradFnL p Ω hSr (w n)‖ ^ p.toReal := by
    intro n
    rw [← hLeq, ← hΓeq]
    have h1 := TestFunction.lintegral_strip_le (φ n) T hg h ht hρt hP1
    have hφ1 : ContDiff ℝ 1 (φ n) := (φ n).contDiff.of_le (by simp)
    have hmS : AEStronglyMeasurable (fn (w n)) (volume.restrict ((Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t})) :=
      (memLp (w n)).aestronglyMeasurable.mono_measure (Measure.restrict_mono hSρ le_rfl)
    have hmG : AEStronglyMeasurable (gradFn (w n)) (volume.restrict ((Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t})) :=
      (aestronglyMeasurable_gradFn (w n)).mono_measure (Measure.restrict_mono hSr le_rfl)
    have hG : MemLp (gradFn (w n)) p (volume.restrict ((Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t})) :=
      (memLp_gradFn (w n)).mono_measure (Measure.restrict_mono hSr le_rfl)
    -- the function of the test function, and the vertical derivative against the gradient
    have e1 : ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, ‖(φ n) x‖ₑ ^ p.toReal
        = ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, ‖fn (w n) x‖ₑ ^ p.toReal := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hSρ (hφ n)] with x hx
      rw [hx]
    have e2 : ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖fderiv ℝ (φ n) x (T.linearIsometryEquiv.symm
            (EuclideanSpace.single (Fin.last d) 1))‖ₑ ^ p.toReal
        ≤ ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖gradFn (w n) x‖ₑ ^ p.toReal := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hSr
        (SobolevEuclidean.norm_fderiv_ae_eq_norm_gradFn (w n) hφ1 (hφ n))] with x hx
      refine ENNReal.rpow_le_rpow ?_ hP0.le
      rw [← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [LinearIsometryEquiv.norm_map, PiLp.norm_single, norm_one, mul_one]
      exact hx.le
    rw [e1] at h1
    have h2 := h1.trans (mul_le_mul' le_rfl e2)
    have e3 : ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, |fn (w n) x| ^ p.toReal
        = (∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖fn (w n) x‖ₑ ^ p.toReal).toReal := by
      rw [← MeasureTheory.integral_norm_rpow_eq_toReal_lintegral hmS hP0.le]
      simp only [Real.norm_eq_abs]
    rw [e3, MeasureTheory.integral_norm_rpow_eq_toReal_lintegral hmG hP0.le]
    calc (∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
          ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
            ‖fn (w n) x‖ₑ ^ p.toReal).toReal
        ≤ (ENNReal.ofReal t ^ p.toReal * ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
          ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
            ‖gradFn (w n) x‖ₑ ^ p.toReal).toReal := by
          refine ENNReal.toReal_mono (ENNReal.mul_ne_top
            (ENNReal.rpow_ne_top_of_nonneg hP0.le ENNReal.ofReal_ne_top)
            (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hG).ne) h2
      _ = _ := by
          rw [ENNReal.toReal_mul, ENNReal.ofReal_rpow_of_nonneg ht.le hP0.le,
            ENNReal.toReal_ofReal (by positivity)]
  -- pass to the limit
  refine le_of_tendsto_of_tendsto' (b := atTop) ?_ ?_ key
  · exact (((continuous_norm.comp L.continuous).rpow_const fun _ ↦ Or.inr hP0.le).tendsto u).comp
      hw
  · exact ((continuous_const.mul ((continuous_norm.comp
      (SobolevEuclidean.gradFnL p Ω hSr).continuous).rpow_const fun _ ↦ Or.inr hP0.le)).tendsto
        u).comp hw

/-- **The strip estimate for a function with zero trace** (Evans §5.5 Theorem 2, (17)): on a
bounded `C¹` domain `Ω ⊆ ℝ^{d+1}`, for `u ∈ W^{1,p}(Ω)` with `T u = 0`, `1 ≤ p < ∞`, a graph
chart `(T, g)` at `(x₀, r)` (`g` continuous), `0 < t` and `ρ + t ≤ r`,
`∫_{S_ρ(t)} |u|^p ≤ t^p ∫_{S_r(t)} |∇u|^p` with `S_ρ(t) := Ω ∩ B(x₀, ρ) ∩ {(Tx)_N < g((Tx)') + t}`
— the estimate of `SobolevEuclideanZero.integral_strip_rpow_le`, since `u ∈ W_0^{1,p}(Ω)`
(`IsContDiffDomain.mem_zero_of_traceL_eq_zero`). With `ρ = r/2` this is Evans's form. -/
theorem IsContDiffDomain.integral_strip_rpow_le_of_traceL_eq_zero
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) {u : SobolevEuclidean (d + 1) 1 p Ω}
    (hu : hΩ.traceL hb p hp u = 0) (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {g : 𝔼' → ℝ} (hg : Continuous g) {x₀ : 𝔼}
    {r ρ t : ℝ}
    (h : (Ω : Set 𝔼) ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    (ht : 0 < t) (hρt : ρ + t ≤ r) :
    ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, |fn u x| ^ p.toReal
      ≤ t ^ p.toReal * ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
          ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖gradFn u x‖ ^ p.toReal :=
  SobolevEuclideanZero.integral_strip_rpow_le hp (hΩ.mem_zero_of_traceL_eq_zero hb p hp hu) T hg
    h ht hρt

end
