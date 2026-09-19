/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Cutoff.lean` and `Numlib/Analysis/Sobolev/Calculus.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.Analysis.Sobolev.Calculus
import Numlib.Analysis.Sobolev.Extension
import Numlib.Analysis.Sobolev.Poincare
import Numlib.Analysis.Sobolev.RemovableSingularity
import Numlib.MeasureTheory.Function.LpSpace.Convergence

/-!
# The space `W_0^{1,p}(Ω)`

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.4: the
closure `W_0^{1,p}(Ω)` of the test functions in `W^{1,p}(Ω)` (`SobolevMultiIndexZero`,
`SobolevEuclideanZero` of `Numlib/Analysis/Sobolev/MultiIndex.lean`) and its characterizations.

## Main results

* `SobolevMultiIndexZero.indicator_memSobolevMultiIndex` and `SobolevEuclideanZero.extendZeroL`:
  **the extension by zero** `ū` of `u ∈ W_0^{1,p}(Ω)` lies in `W^{1,p}` of the whole space, with
  `∂_i ū = \overline{∂_i u}` (Proposition 9.18, (i) ⇒ (iii)), on an arbitrary open set and for
  every `1 ≤ p ≤ ∞` — the book's route through the Riesz representation is replaced by the
  closedness of the weak derivative under `L^p` limits, applied to the zero extensions of
  approximating test functions, which are test functions on the whole space;
* `SobolevEuclideanZero.hasSobolevExtensionOn`: **Remark 20**, the extension by zero is a
  bounded (indeed isometric) extension operator on `W_0^{1,p}(Ω)`, so that the embedding and
  compactness theorems stated under `HasSobolevExtensionOn` hold on `W_0^{1,p}(Ω)` with no
  regularity of `Ω`;
* `SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`: **Theorem 9.17,
  (i) ⇒ (ii)**, on any open set: a `W^{1,p}(Ω)` function with a representative continuous on
  `closure Ω` and vanishing on `∂Ω` lies in `W_0^{1,p}(Ω)`. The book's "`u_n → u` by dominated
  convergence" silently needs `∇u = 0` a.e. on `{u = 0}`; here the truncations `G(nu)/n` are
  shown to be Cauchy in `W^{1,p}(Ω)` instead, their gradients converging to
  `{u ≠ 0}.indicator ∇u`, and the limit is identified through the function alone;
* `SobolevEuclideanZero.abs_integral_fn_smul_fderiv_le` and
  `SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le`: Proposition 9.18,
  (i) ⇒ (ii) and (ii) ⇒ (iii);
* `SobolevEuclideanZero.eq_top` (Remark 17) and
  `SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport` (Remark 18);
* `SobolevMultiIndexZero.contDiff_comp_mem` and `SobolevEuclideanZero.posPart_mem`: the chain
  rule and the positive part preserve `W_0^{1,p}(Ω)`;
* `SobolevEuclideanZero.exists_dual_repr`: **Proposition 9.20**, every element of the dual
  `W^{-1,p'}(Ω)` is `v ↦ ∫ f_0 v + ∑ ∫ f_i ∂_i v` with `f_α ∈ L^{p'}(Ω)`, `‖f_α‖ ≤ ‖F‖`, and
  `SobolevEuclideanZero.exists_dual_repr_of_isBounded`, its form with `f_0 = 0` on a bounded `Ω`
  (Poincaré's inequality);
* `SobolevEuclideanZero.gelfandTriple`: **the inclusions `H^1_0(Ω) ⊂ L²(Ω) ⊂ H^{-1}(Ω)`** are
  injective with dense range (`SobolevEuclideanZero.toDualL2` is the second one).

## Design

Predicate-level statements are over a finite-dimensional real normed `E` with an additive Haar
measure `μ` and an arbitrary basis `b`; typed statements are on `SobolevEuclideanZero N 1 p Ω`.
The zero extension is built by the pattern of `Numlib/Analysis/Sobolev/Cutoff.lean`: membership
and the identities at the predicate level, then `MemSobolevMultiIndex.exists_sobolevMultiIndex`
and `SobolevMultiIndex.ext_of_fn_ae_eq`.

## References

[brezis2011functional], §9.4: Theorem 9.17, Proposition 9.18, Remarks 17–20, Proposition 9.20.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

/-! ### The weak derivative along a tuple is closed under `L^p` limits -/

section Closed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {μ : Measure E}
  {p : ℝ≥0∞} {n : ℕ} {y : Fin n → E} {f w : E → F}

/-- **The weak derivative along a tuple of directions is closed under `L^p(Ω)` limits**, for any
`1 ≤ p ≤ ∞`: if `u i` is a weak derivative of `g i` along `y` on `Ω` for every `i`, `g i → f` and
`u i → w` in `L^p(Ω)`, and `f`, `w` are locally integrable on `Ω`, then `w` is a weak derivative
of `f` along `y`. The tuple-by-tuple form of `hasWeakIteratedFDerivOn_of_tendsto_eLpNorm`
(the closedness clause of [brezis2011functional] Chapter 9, Remark 4 (i)), with the same proof:
the pairings against a fixed test function are continuous on `L^p(Ω)` by Hölder's inequality. -/
theorem hasWeakIteratedLineDerivOn_of_tendsto_eLpNorm
    (hμ : LocallyIntegrableOn (fun _ : E ↦ (1 : ℝ)) Ω μ) (hp : 1 ≤ p) {g u : ℕ → E → F}
    (hg : ∀ i, HasWeakIteratedLineDerivOn y (g i) (u i) Ω μ)
    (hfl : LocallyIntegrableOn f Ω μ) (hwl : LocallyIntegrableOn w Ω μ)
    (h1 : Tendsto (fun i ↦ eLpNorm (g i - f) p (μ.restrict (Ω : Set E))) atTop (𝓝 0))
    (h2 : Tendsto (fun i ↦ eLpNorm (u i - w) p (μ.restrict (Ω : Set E))) atTop (𝓝 0)) :
    HasWeakIteratedLineDerivOn y f w Ω μ where
  locallyIntegrableOn := hfl
  locallyIntegrableOn_weakDeriv := hwl
  integral_smul_eq φ := by
    have : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
      ENNReal.HolderConjugate.conjExponent hp
    set q := ENNReal.conjExponent p with hq
    set a : 𝓓(Ω, ℝ) := φ.iteratedFDerivApply n y with hadef
    have haq : eLpNorm a q (μ.restrict (Ω : Set E)) ≠ ⊤ :=
      (a.memLp_restrict_of_locallyIntegrableOn_one hμ q).eLpNorm_ne_top
    have hφq : eLpNorm φ q (μ.restrict (Ω : Set E)) ≠ ⊤ :=
      (φ.memLp_restrict_of_locallyIntegrableOn_one hμ q).eLpNorm_ne_top
    -- the left-hand sides converge
    have hIg : ∀ i, IntegrableOn (fun x ↦ a x • g i x) (Ω : Set E) μ := fun i ↦
      ((hg i).integrable_smul a).integrableOn
    have hIf : IntegrableOn (fun x ↦ a x • f x) (Ω : Set E) μ :=
      (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hfl a.contDiff.continuous
        a.hasCompactSupport a.tsupport_subset).integrableOn
    have hA : Tendsto (fun i ↦ ∫ x in (Ω : Set E), a x • g i x ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), a x • f x ∂μ)) := by
      rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_enorm_tendsto_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (?_ : Tendsto (fun i ↦ eLpNorm a q (μ.restrict (Ω : Set E)) *
          eLpNorm (g i - f) p (μ.restrict (Ω : Set E))) atTop (𝓝 0))
        (fun _ ↦ zero_le) (fun i ↦ ?_)
      · simpa using ENNReal.Tendsto.const_mul h1 (Or.inr haq)
      · rw [← integral_sub (hIg i) hIf]
        have heq : (fun x ↦ a x • g i x - a x • f x) = fun x ↦ a x • (g i - f) x :=
          funext fun x ↦ by simp [smul_sub]
        rw [heq]
        exact enorm_integral_smul_le_eLpNorm_mul_eLpNorm (p := q) (q := p)
    -- the right-hand sides converge
    have hIu : ∀ i, IntegrableOn (fun x ↦ φ x • u i x) (Ω : Set E) μ := fun i ↦
      ((hg i).integrable_smul_weakDeriv φ).integrableOn
    have hIw : IntegrableOn (fun x ↦ φ x • w x) (Ω : Set E) μ :=
      (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hwl φ.contDiff.continuous
        φ.hasCompactSupport φ.tsupport_subset).integrableOn
    have hB : Tendsto (fun i ↦ ∫ x in (Ω : Set E), φ x • u i x ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), φ x • w x ∂μ)) := by
      rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_enorm_tendsto_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (?_ : Tendsto (fun i ↦ eLpNorm φ q (μ.restrict (Ω : Set E)) *
          eLpNorm (u i - w) p (μ.restrict (Ω : Set E))) atTop (𝓝 0))
        (fun _ ↦ zero_le) (fun i ↦ ?_)
      · simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hφq)
      · rw [← integral_sub (hIu i) hIw]
        have heq : (fun x ↦ φ x • u i x - φ x • w x) = fun x ↦ φ x • (u i - w) x :=
          funext fun x ↦ by simp [smul_sub]
        rw [heq]
        exact enorm_integral_smul_le_eLpNorm_mul_eLpNorm (p := q) (q := p)
    have hAB : ∀ i, (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • g i x ∂μ)
        = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • u i x ∂μ := fun i ↦
      (hg i).integral_smul_eq φ
    have hax : ∀ x, a x = iteratedFDeriv ℝ n (φ : E → ℝ) x y := fun _ ↦ rfl
    have hA' : Tendsto (fun i ↦ (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • u i x ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x ∂μ)) := by
      simpa only [hax, hAB] using hA
    exact tendsto_nhds_unique hA' (hB.const_smul ((-1 : ℝ) ^ n))

end Closed

/-! ### Dominated convergence in `L^p`, and convergence in `W^{1,p}(Ω)` component by component -/

section Dominated

/-- **Dominated convergence in `L^p`**, `0 < p < ∞`: if `f n → g` almost everywhere and
`‖f n‖ ≤ bound` almost everywhere for a fixed `bound ∈ L^p`, then `f n → g` in `L^p`. The
dominated convergence theorem for the integrals `∫ ‖f n − g‖^p`, dominated by `(2 bound)^p`. -/
theorem MeasureTheory.tendsto_eLpNorm_sub_of_tendsto_ae {X G : Type*} [MeasurableSpace X]
    {ν : Measure X} [NormedAddCommGroup G] {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤)
    {f : ℕ → X → G} {g : X → G} {bound : X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) ν) (hg : AEStronglyMeasurable g ν)
    (hbound : MemLp bound p ν) (hfb : ∀ n, ∀ᵐ x ∂ν, ‖f n x‖ ≤ bound x)
    (hfg : ∀ᵐ x ∂ν, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p ν) atTop (𝓝 0) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have hgb : ∀ᵐ x ∂ν, ‖g x‖ ≤ bound x := by
    filter_upwards [ae_all_iff.2 hfb, hfg] with x hx hlim
    exact le_of_tendsto hlim.norm (Eventually.of_forall hx)
  have hle : ∀ {a : G} {b : ℝ}, ‖a‖ ≤ b → ‖a‖ₑ ≤ ‖b‖ₑ := fun {a b} h ↦ by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (h.trans (Real.le_norm_self _))
  have hB : ∫⁻ x, (2 * ‖bound x‖ₑ) ^ p.toReal ∂ν ≠ ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp hp' hbound.eLpNorm_lt_top
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le (by simp))]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (by simp)) this.ne
  have key : Tendsto (fun n ↦ ∫⁻ x, ‖(f n - g) x‖ₑ ^ p.toReal ∂ν) atTop
      (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence' _
      (fun n ↦ ((hf n).sub hg).enorm.pow_const _) (fun n ↦ ?_) hB ?_
    · filter_upwards [hfb n, hgb] with x hxn hxg
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      calc ‖(f n - g) x‖ₑ = ‖f n x - g x‖ₑ := rfl
        _ ≤ ‖f n x‖ₑ + ‖g x‖ₑ := enorm_sub_le
        _ ≤ ‖bound x‖ₑ + ‖bound x‖ₑ := add_le_add (hle hxn) (hle hxg)
        _ = 2 * ‖bound x‖ₑ := (two_mul _).symm
    · filter_upwards [hfg] with x hx
      have h0 : Tendsto (fun n ↦ ‖(f n - g) x‖ₑ) atTop (𝓝 0) := by
        rw [← tendsto_sub_nhds_zero_iff] at hx
        exact tendsto_zero_iff_enorm_tendsto_zero.1 hx
      have := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp h0
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp0] using this
  simp only [lintegral_zero] at key
  have := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp key
  simp only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.2 hp0)] at this
  refine this.congr fun n ↦ ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' ((hf n).sub hg)]

end Dominated

section Components

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- Convergence in `W^{k,p}(Ω)` gives the `L^p(Ω)` convergence of every weak derivative. -/
theorem tendsto_eLpNorm_weakDeriv_sub {w : ℕ → SobolevMultiIndex F b k p Ω μ}
    {u : SobolevMultiIndex F b k p Ω μ} (hw : Tendsto w atTop (𝓝 u)) (α : MultiIndexLE ι k) :
    Tendsto (fun n ↦ eLpNorm ((weakDeriv (w n) α : E → F) - (weakDeriv u α : E → F)) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
  have ht := ((weakDerivL F b k p Ω μ α).continuous.tendsto u).comp hw
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at ht
  simpa only [Function.comp_def, weakDerivL_apply] using ht

/-- Convergence in `W^{k,p}(Ω)` gives the `L^p(Ω)` convergence of the functions. -/
theorem tendsto_eLpNorm_fn_sub {w : ℕ → SobolevMultiIndex F b k p Ω μ}
    {u : SobolevMultiIndex F b k p Ω μ} (hw : Tendsto w atTop (𝓝 u)) :
    Tendsto (fun n ↦ eLpNorm (fn (w n) - fn u) p (μ.restrict (Ω : Set E))) atTop (𝓝 0) :=
  tendsto_eLpNorm_weakDeriv_sub hw 0

/-- **Convergence in `W^{k,p}(Ω)` from the convergence of the components**: if every weak
derivative of `w n − u` tends to `0` in `L^p(Ω)`, then `w n → u` in `W^{k,p}(Ω)`. -/
theorem tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub {w : ℕ → SobolevMultiIndex F b k p Ω μ}
    {u : SobolevMultiIndex F b k p Ω μ}
    (h : ∀ α : MultiIndexLE ι k, Tendsto (fun n ↦
      eLpNorm ((weakDeriv (w n) α : E → F) - (weakDeriv u α : E → F)) p (μ.restrict (Ω : Set E)))
        atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hα : ∀ α : MultiIndexLE ι k, Tendsto (fun n ↦ ‖weakDeriv (w n - u) α‖) atTop (𝓝 0) := by
    intro α
    have e : ∀ n, ‖weakDeriv (w n - u) α‖
        = (eLpNorm ((weakDeriv (w n) α : E → F) - (weakDeriv u α : E → F)) p
            (μ.restrict (Ω : Set E))).toReal := fun n ↦ by
      have e' : weakDeriv (w n - u) α = weakDeriv (w n) α - weakDeriv u α := rfl
      rw [Lp.norm_def, e']
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_sub _ _))
    simp_rw [e]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h α)
    simpa [Function.comp_def] using this
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_le_sum_norm_weakDeriv (w n - u)) ?_
  simpa using tendsto_finsetSum Finset.univ fun α _ ↦ hα α

end SobolevMultiIndex

end Components

/-! ### The extension by zero of a `W_0^{1,p}(Ω)` function -/

section ZeroExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndexZero

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- The zero extension of the function of an element of `W^{k,p}(Ω)` lies in `L^p` of the whole
space. -/
theorem memLp_indicator_fn {k : ℕ} (u : SobolevMultiIndex F b k p Ω μ) :
    MemLp ((Ω : Set E).indicator (SobolevMultiIndex.fn u)) p μ :=
  (memLp_indicator_iff_restrict Ω.isOpen.measurableSet).2 (SobolevMultiIndex.memLp u)

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- The zero extension of a weak derivative of an element of `W^{k,p}(Ω)` lies in `L^p` of the
whole space. -/
theorem memLp_indicator_weakDeriv {k : ℕ} (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k) :
    MemLp ((Ω : Set E).indicator (SobolevMultiIndex.weakDeriv u α)) p μ :=
  (memLp_indicator_iff_restrict Ω.isOpen.measurableSet).2 (Lp.memLp _)

omit [FiniteDimensional ℝ E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- An element of `W_0^{k,p}(Ω)` is the limit of a sequence of elements of `W^{k,p}(Ω)` whose
functions are test functions on `Ω`. -/
theorem exists_seq_testFunction_tendsto {k : ℕ} {u : SobolevMultiIndex F b k p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero F b k p Ω μ) :
    ∃ (w : ℕ → SobolevMultiIndex F b k p Ω μ) (φ : ℕ → 𝓓(Ω, F)),
      (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[μ.restrict (Ω : Set E)] φ n) ∧
        Tendsto w atTop (𝓝 u) := by
  have hmem : u ∈ closure (SobolevMultiIndex.testFunctions F b k p Ω μ : Set _) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hu
  obtain ⟨w, hwT, hw⟩ := mem_closure_iff_seq_limit.1 hmem
  choose φ hφ using hwT
  exact ⟨w, φ, hφ, hw⟩

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- The zero extension of the function of an element of `W^{k,p}(Ω)` whose function is a test
function on `Ω` is that test function, almost everywhere. -/
theorem indicator_fn_ae_eq_testFunction {k : ℕ} {w : SobolevMultiIndex F b k p Ω μ}
    {φ : 𝓓(Ω, F)} (hφ : SobolevMultiIndex.fn w =ᵐ[μ.restrict (Ω : Set E)] φ) :
    (Ω : Set E).indicator (SobolevMultiIndex.fn w) =ᵐ[μ] φ := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1 hφ
  refine h.trans (Eventually.of_forall fun x ↦ ?_)
  exact congrFun (Set.indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx ↦
    φ.eq_zero_of_notMem hx)) x

omit [Fact (1 ≤ p)] in
/-- The partial derivative `∂_i w` of an element of `W^{1,p}(Ω)` whose function is a test
function `φ` on `Ω` is the classical derivative `∂_i φ`, almost everywhere on `Ω`. -/
theorem weakDeriv_single_ae_eq_testFunction {w : SobolevMultiIndex F b 1 p Ω μ}
    {φ : 𝓓(Ω, F)} (hφ : SobolevMultiIndex.fn w =ᵐ[μ.restrict (Ω : Set E)] φ) (i : ι) :
    SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ fderiv ℝ φ x (b i) := by
  refine (SobolevMultiIndex.weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq w φ.contDiff hφ
    (MultiIndexLE.single i)).trans (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [MultiIndexLE.coe_single, φ.contDiff.iteratedFDeriv_congr_perm
    (multiIndexTuple_single_perm (b : ι → E) i) x, iteratedFDeriv_one_apply,
    Matrix.cons_val_zero]

omit [Fact (1 ≤ p)] in
/-- The zero extension of the partial derivative `∂_i w` of an element of `W^{1,p}(Ω)` whose
function is a test function `φ` on `Ω` is the classical derivative `∂_i φ`, almost everywhere. -/
theorem indicator_weakDeriv_single_ae_eq_testFunction {w : SobolevMultiIndex F b 1 p Ω μ}
    {φ : 𝓓(Ω, F)} (hφ : SobolevMultiIndex.fn w =ᵐ[μ.restrict (Ω : Set E)] φ) (i : ι) :
    (Ω : Set E).indicator (SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i))
      =ᵐ[μ] fun x ↦ fderiv ℝ φ x (b i) := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1
    (weakDeriv_single_ae_eq_testFunction hφ i)
  refine h.trans (Eventually.of_forall fun x ↦ ?_)
  exact congrFun (Set.indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx ↦
    (φ.fderivApply (b i)).eq_zero_of_notMem hx)) x

/-- **The zero extension of a `W_0^{1,p}(Ω)` function has the zero extension of its partial
derivative as weak derivative on the whole space**: for `u ∈ W_0^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, the
weak derivative of `ū = Ω.indicator u` along `b i` on `E` is `\overline{∂_i u}`. Test functions
`φ_n → u` in `W^{1,p}(Ω)` are test functions on `E` with `∂_i φ_n` as classical derivative,
`φ_n → ū` and `∂_i φ_n → \overline{∂_i u}` in `L^p(E)`, and the weak derivative is closed under
`L^p` limits (`hasWeakIteratedLineDerivOn_of_tendsto_eLpNorm`). This is the identity
"`∂ū/∂x_i = \overline{∂u/∂x_i}`" of [brezis2011functional] Proposition 9.18 (iii), proved for
every open `Ω` and without the Riesz representation of the book's route. -/
theorem hasWeakIteratedLineDerivOn_indicator {u : SobolevMultiIndex F b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero F b 1 p Ω μ) (i : ι) :
    HasWeakIteratedLineDerivOn ![b i] ((Ω : Set E).indicator (SobolevMultiIndex.fn u))
      ((Ω : Set E).indicator (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i))) ⊤ μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨w, φ, hφ, hw⟩ := exists_seq_testFunction_tendsto hu
  have hμ : LocallyIntegrableOn (fun _ : E ↦ (1 : ℝ)) (⊤ : Opens E) μ :=
    (locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _
  -- convergence of the components, in `L^p(E)`
  have hconv : ∀ α : MultiIndexLE ι 1, Tendsto (fun n ↦ eLpNorm
      ((Ω : Set E).indicator (SobolevMultiIndex.weakDeriv (w n) α)
        - (Ω : Set E).indicator (SobolevMultiIndex.weakDeriv u α)) p μ) atTop (𝓝 0) := by
    intro α
    refine (SobolevMultiIndex.tendsto_eLpNorm_weakDeriv_sub hw α).congr fun n ↦ ?_
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet, ← Set.indicator_sub']
  refine hasWeakIteratedLineDerivOn_of_tendsto_eLpNorm hμ hp (g := fun n ↦ (φ n : E → F))
    (u := fun n x ↦ fderiv ℝ (φ n) x (b i)) (fun n ↦ ?_) ?_ ?_ ?_ ?_
  · have h := (ContDiffOn.hasWeakIteratedFDerivOn (Ω := ⊤) (μ := μ) (φ n).contDiff.contDiffOn
      (m := 1) (by simp)).lineDeriv ![b i]
    exact h.congr_ae (Filter.EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ by
      simp [iteratedFDeriv_one_apply])
  · exact ((memLp_indicator_fn u).locallyIntegrable hp).locallyIntegrableOn _
  · exact ((memLp_indicator_weakDeriv u _).locallyIntegrable hp).locallyIntegrableOn _
  · refine (hconv 0).congr fun n ↦ ?_
    simp only [Measure.restrict_coe_top]
    exact eLpNorm_congr_ae ((indicator_fn_ae_eq_testFunction (hφ n)).sub
      (Filter.EventuallyEq.refl _ _))
  · refine (hconv (MultiIndexLE.single i)).congr fun n ↦ ?_
    simp only [Measure.restrict_coe_top]
    exact eLpNorm_congr_ae ((indicator_weakDeriv_single_ae_eq_testFunction (hφ n) i).sub
      (Filter.EventuallyEq.refl _ _))

/-- **Proposition 9.18, (i) ⇒ (iii), predicate form**: for `u ∈ W_0^{1,p}(Ω)` on an arbitrary
open `Ω`, `1 ≤ p ≤ ∞`, the extension by zero `ū = Ω.indicator u` lies in `W^{1,p}` of the whole
space, with `∂_i ū = \overline{∂_i u}`
(`SobolevMultiIndexZero.hasWeakIteratedLineDerivOn_indicator`); [brezis2011functional]
Proposition 9.18, (i) ⇒ (iii), and Remark 20 ("the canonical extension by 0 outside `Ω`, which
is valid for arbitrary domains"). -/
theorem indicator_memSobolevMultiIndex {u : SobolevMultiIndex F b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero F b 1 p Ω μ) :
    MemSobolevMultiIndex b ((Ω : Set E).indicator (SobolevMultiIndex.fn u)) 1 p ⊤ μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  refine ⟨by simpa only [Measure.restrict_coe_top] using memLp_indicator_fn u, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (((memLp_indicator_fn u).locallyIntegrable hp).locallyIntegrableOn _),
      by simpa only [Measure.restrict_coe_top] using memLp_indicator_fn u⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    exact ⟨_, (hasWeakIteratedLineDerivOn_indicator hu i).of_perm
      (multiIndexTuple_single_perm (b : ι → E) i).symm,
      by simpa only [Measure.restrict_coe_top] using memLp_indicator_weakDeriv u _⟩

end SobolevMultiIndexZero

end ZeroExtension


/-! ### The typed extension by zero `W_0^{1,p}(Ω) → W^{1,p}(ℝ^N)` -/

section Typed

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

namespace SobolevEuclideanZero

/-- The extension by zero of `u ∈ W_0^{1,p}(Ω)`, as an element of `W^{1,p}(ℝ^N)`: the element
whose function is `Ω.indicator (fn u)`, which exists by
`SobolevMultiIndexZero.indicator_memSobolevMultiIndex`. -/
def extendZero (u : SobolevEuclideanZero N 1 p Ω) : SobolevEuclidean N 1 p ⊤ :=
  (SobolevMultiIndexZero.indicator_memSobolevMultiIndex u.2).exists_sobolevMultiIndex.choose

/-- The function of the extension by zero is `Ω.indicator (fn u)`, almost everywhere. -/
theorem fn_extendZero (u : SobolevEuclideanZero N 1 p Ω) :
    SobolevMultiIndex.fn (extendZero u) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) := by
  have h : SobolevMultiIndex.fn (extendZero u)
      =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)]
        (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
          (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) :=
    (SobolevMultiIndexZero.indicator_memSobolevMultiIndex u.2).exists_sobolevMultiIndex.choose_spec
  simpa only [Measure.restrict_coe_top] using h

/-- On `Ω`, the function of the extension by zero is the function of `u`. -/
theorem fn_extendZero_restrict (u : SobolevEuclideanZero N 1 p Ω) :
    SobolevMultiIndex.fn (extendZero u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) :=
  Filter.EventuallyEq.trans (ae_restrict_of_ae (fn_extendZero u))
    (indicator_ae_eq_restrict Ω.isOpen.measurableSet)

/-- The partial derivative of the extension by zero is the extension by zero of the partial
derivative: `∂_i ū = \overline{∂_i u}` ([brezis2011functional] Proposition 9.18 (iii)). -/
theorem weakDeriv_extendZero_single (u : SobolevEuclideanZero N 1 p Ω) (i : Fin N) :
    (SobolevMultiIndex.weakDeriv (extendZero u) (MultiIndexLE.single i) :
      EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)) := by
  have h1 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn (extendZero u)
    (MultiIndexLE.single i)).of_perm (multiIndexTuple_single_perm
      ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → _) i)).congr_ae
    (by simpa only [Measure.restrict_coe_top] using fn_extendZero u)
    (Filter.EventuallyEq.refl _ _)
  have h2 := SobolevMultiIndexZero.hasWeakIteratedLineDerivOn_indicator u.2 i
  filter_upwards [h1.ae_eq h2] with x hx using hx (mem_univ x)

/-- The extension by zero of a sum is the sum of the extensions. -/
theorem extendZero_add (u v : SobolevEuclideanZero N 1 p Ω) :
    extendZero (u + v) = extendZero u + extendZero v := by
  refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
  have h1 : SobolevMultiIndex.fn (extendZero u + extendZero v) =ᵐ[volume]
      SobolevMultiIndex.fn (extendZero u) + SobolevMultiIndex.fn (extendZero v) := by
    simpa only [Measure.restrict_coe_top] using
      SobolevMultiIndex.fn_add (extendZero u) (extendZero v)
  have h2 : (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
      (SobolevMultiIndex.fn ((u : SobolevEuclidean N 1 p Ω) + (v : SobolevEuclidean N 1 p Ω)))
        =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)
          + SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω)) :=
    (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1
      (SobolevMultiIndex.fn_add (u : SobolevEuclidean N 1 p Ω) v)
  simp only [Measure.restrict_coe_top]
  refine (fn_extendZero (u + v)).trans (h2.trans (Filter.EventuallyEq.trans ?_ h1.symm))
  rw [Set.indicator_add']
  exact (fn_extendZero u).symm.add (fn_extendZero v).symm

/-- The extension by zero of a scalar multiple is the multiple of the extension. -/
theorem extendZero_smul (c : ℝ) (u : SobolevEuclideanZero N 1 p Ω) :
    extendZero (c • u) = c • extendZero u := by
  refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
  have h1 : SobolevMultiIndex.fn (c • extendZero u) =ᵐ[volume]
      c • SobolevMultiIndex.fn (extendZero u) := by
    simpa only [Measure.restrict_coe_top] using SobolevMultiIndex.fn_smul c (extendZero u)
  have h2 : (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
      (SobolevMultiIndex.fn (c • (u : SobolevEuclidean N 1 p Ω))) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (c • SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) :=
    (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1
      (SobolevMultiIndex.fn_smul c (u : SobolevEuclidean N 1 p Ω))
  simp only [Measure.restrict_coe_top]
  refine (fn_extendZero (c • u)).trans (h2.trans (Filter.EventuallyEq.trans ?_ h1.symm))
  have h3 : (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
      (c • SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω))
      = c • (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) := by
    funext x
    exact congrFun (Set.indicator_const_smul (Ω : Set (EuclideanSpace ℝ (Fin N))) c
      (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω))) x
  rw [h3]
  exact (fn_extendZero u).symm.const_smul c

/-- The `L^p` norms of the components of the extension by zero are those of `u`: the integrals
over `ℝ^N` of the zero extensions are the integrals over `Ω`. -/
theorem norm_weakDeriv_extendZero (u : SobolevEuclideanZero N 1 p Ω)
    (α : MultiIndexLE (Fin N) 1) :
    ‖SobolevMultiIndex.weakDeriv (extendZero u) α‖
      = ‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) α‖ := by
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
  · rw [Lp.norm_def, Lp.norm_def]
    simp only [Measure.restrict_coe_top]
    rw [eLpNorm_congr_ae (f := (SobolevMultiIndex.weakDeriv (extendZero u) 0 : _ → ℝ))
      (fn_extendZero u), eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet]
    rfl
  · rw [Lp.norm_def, Lp.norm_def]
    simp only [Measure.restrict_coe_top]
    rw [eLpNorm_congr_ae (weakDeriv_extendZero_single u i),
      eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet]

/-- **The extension by zero is an isometry** `W_0^{1,p}(Ω) → W^{1,p}(ℝ^N)`: the norm of the
type is the `ℓ^p` sum of the `L^p` norms of the components, each of which is unchanged. -/
theorem norm_extendZero (u : SobolevEuclideanZero N 1 p Ω) :
    ‖extendZero u‖ = ‖(u : SobolevEuclidean N 1 p Ω)‖ := by
  rcases eq_or_ne p ⊤ with rfl | hp'
  · rw [SobolevMultiIndex.norm_eq_ciSup, SobolevMultiIndex.norm_eq_ciSup]
    exact iSup_congr (norm_weakDeriv_extendZero u)
  · rw [SobolevMultiIndex.norm_eq_sum hp', SobolevMultiIndex.norm_eq_sum hp']
    congr 1
    exact Finset.sum_congr rfl fun α _ ↦ by rw [norm_weakDeriv_extendZero]

variable (N p Ω) in
/-- The extension by zero as a linear map `W_0^{1,p}(Ω) → W^{1,p}(ℝ^N)`. -/
def extendZeroₗ : SobolevEuclideanZero N 1 p Ω →ₗ[ℝ] SobolevEuclidean N 1 p ⊤ where
  toFun := extendZero
  map_add' := extendZero_add
  map_smul' := extendZero_smul

variable (N p Ω) in
/-- **Proposition 9.18, (i) ⇒ (iii): the extension by zero**, as a bounded linear map
`W_0^{1,p}(Ω) → W^{1,p}(ℝ^N)`, for every open `Ω` and `1 ≤ p ≤ ∞`: `ū = Ω.indicator u` lies in
`W^{1,p}(ℝ^N)` (`SobolevEuclideanZero.fn_extendZeroL`), with `∂_i ū = \overline{∂_i u}`
(`SobolevEuclideanZero.weakDeriv_extendZeroL_single`), and the map is an isometry
(`SobolevEuclideanZero.norm_extendZeroL_apply`). [brezis2011functional] Proposition 9.18,
(i) ⇒ (iii), and Remark 20 ("the canonical extension by 0 outside `Ω`, which is valid for
arbitrary domains"). -/
def extendZeroL : SobolevEuclideanZero N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤ :=
  (extendZeroₗ N p Ω).mkContinuous 1 fun u ↦ by
    rw [one_mul, ← Submodule.norm_coe]
    exact (norm_extendZero u).le

/-- `SobolevEuclideanZero.extendZeroL` is `SobolevEuclideanZero.extendZero`. -/
@[simp]
theorem extendZeroL_apply (u : SobolevEuclideanZero N 1 p Ω) :
    extendZeroL N p Ω u = extendZero u :=
  rfl

/-- The function of `extendZeroL u` is `Ω.indicator (fn u)`, almost everywhere on `ℝ^N`:
"`ū ∈ W^{1,p}(ℝ^N)`". -/
theorem fn_extendZeroL (u : SobolevEuclideanZero N 1 p Ω) :
    SobolevMultiIndex.fn (extendZeroL N p Ω u) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) :=
  fn_extendZero u

/-- On `Ω`, the function of `extendZeroL u` is the function of `u`. -/
theorem fn_extendZeroL_restrict (u : SobolevEuclideanZero N 1 p Ω) :
    SobolevMultiIndex.fn (extendZeroL N p Ω u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) :=
  fn_extendZero_restrict u

/-- The partial derivatives of `extendZeroL u` are the zero extensions of those of `u`:
"`∂ū/∂x_i = \overline{∂u/∂x_i}`". -/
theorem weakDeriv_extendZeroL_single (u : SobolevEuclideanZero N 1 p Ω) (i : Fin N) :
    (SobolevMultiIndex.weakDeriv (extendZeroL N p Ω u) (MultiIndexLE.single i) :
      EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)) :=
  weakDeriv_extendZero_single u i

/-- The extension by zero is an isometry: `‖ū‖_{W^{1,p}(ℝ^N)} = ‖u‖_{W^{1,p}(Ω)}`. -/
theorem norm_extendZeroL_apply (u : SobolevEuclideanZero N 1 p Ω) :
    ‖extendZeroL N p Ω u‖ = ‖u‖ := by
  rw [extendZeroL_apply, norm_extendZero, Submodule.norm_coe]

/-- The operator norm of the extension by zero is at most one. -/
theorem norm_extendZeroL_le : ‖extendZeroL N p Ω‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Remark 20**: on the subspace `W_0^{1,p}(Ω)` of an arbitrary open set, the extension by
zero is a bounded extension operator into `W^{1,p}(ℝ^N)`, `HasSobolevExtensionOn` of
`Numlib/Analysis/Sobolev/Cutoff.lean`; hence every consequence of that predicate — the
embeddings of Corollary 9.14 and the compactness of Theorem 9.16 — holds on `W_0^{1,p}(Ω)`
with no regularity of `Ω` ([brezis2011functional] Chapter 9, Remark 20). -/
theorem hasSobolevExtensionOn : HasSobolevExtensionOn (SobolevEuclideanZero N 1 p Ω) :=
  ⟨extendZeroL N p Ω, fun u ↦ fn_extendZeroL_restrict u⟩

end SobolevEuclideanZero

end Typed

/-! ### Remarks 17 and 18: `C_c^k(Ω) ⊆ W_0^{k,p}(Ω)`, and `W_0^{1,p}(ℝ^N) = W^{1,p}(ℝ^N)` -/

section Remarks

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Lemma 9.5 for a function with compact support in `Ω`**: an element of `W^{k,p}(Ω)`,
`1 ≤ p < ∞`, whose function agrees almost everywhere on `Ω` with a function whose support is a
compact subset of `Ω` lies in `W_0^{k,p}(Ω)`
(`SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact` with `K = tsupport v`). -/
theorem SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset (hp' : p ≠ ⊤)
    (u : SobolevMultiIndex F b k p Ω μ) {v : E → F} (hvc : HasCompactSupport v)
    (hvΩ : tsupport v ⊆ Ω) (hu : SobolevMultiIndex.fn u =ᵐ[μ.restrict (Ω : Set E)] v) :
    u ∈ SobolevMultiIndexZero F b k p Ω μ :=
  SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact hp' u hvc hvΩ
    (hu.mono fun x hx hxK ↦ by rw [hx]; exact image_eq_zero_of_notMem_tsupport hxK)

omit [μ.IsAddHaarMeasure] in
/-- A `C^k` function with compact support is the function of an element of `W^{k,p}(Ω)`: the
`C^∞` case is `ContDiff.exists_sobolevMultiIndex_of_hasCompactSupport`. -/
theorem ContDiff.exists_sobolevMultiIndex_of_hasCompactSupport' [μ.IsAddHaarMeasure] {v : E → F}
    (hv : ContDiff ℝ k v) (hvc : HasCompactSupport v) :
    ∃ u : SobolevMultiIndex F b k p Ω μ, SobolevMultiIndex.fn u =ᵐ[μ.restrict (Ω : Set E)] v := by
  refine MemSobolevMultiIndex.exists_sobolevMultiIndex (MemSobolev.memSobolevMultiIndex ?_)
  refine ⟨(hv.continuous.memLp_of_hasCompactSupport hvc).restrict _, fun n hn ↦ ⟨_,
    ContDiffOn.hasWeakIteratedFDerivOn hv.contDiffOn (by exact_mod_cast hn), ?_⟩⟩
  exact ((hv.continuous_iteratedFDeriv (m := n) (by exact_mod_cast hn)).memLp_of_hasCompactSupport
    (hvc.iteratedFDeriv n)).restrict _

/-- **Remark 18, and the book's definition of `W_0^{1,p}(Ω)` through `C_c^1(Ω)`**: a `C^k`
function with compact support in `Ω` is the function of an element of `W_0^{k,p}(Ω)`,
`1 ≤ p < ∞`. So the closure of `C_c^k(Ω)` in `W^{k,p}(Ω)` is contained in the closure
`SobolevEuclideanZero N k p Ω` of `C_c^∞(Ω)`, and the two closures agree: "`C_c^∞(Ω)` could
equally well have been used instead of `C_c^1(Ω)` in the definition of `W_0^{1,p}(Ω)`"
([brezis2011functional] §9.4, Definition, Remark 18, and Remark 22 for `k ≥ 2`). Immediate from
Lemma 9.5 and Remark 2. -/
theorem SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (hp' : p ≠ ⊤) {v : EuclideanSpace ℝ (Fin N) → ℝ}
    (hv : ContDiff ℝ k v) (hvc : HasCompactSupport v) (hvΩ : tsupport v ⊆ Ω) :
    ∃ u ∈ SobolevEuclideanZero N k p Ω,
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v :=
  let ⟨u, hu⟩ := hv.exists_sobolevMultiIndex_of_hasCompactSupport'
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (Ω := Ω) (μ := volume) hvc
  ⟨u, SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset hp' u hvc hvΩ hu, hu⟩

/-- **Remark 17**: `W_0^{1,p}(ℝ^N) = W^{1,p}(ℝ^N)` for `1 ≤ p < ∞`, since `C_c^∞(ℝ^N)` is dense in
`W^{1,p}(ℝ^N)` (Theorem 9.2 on the whole space, through the abstract density lemma
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn` with
the identity as extension operator): the approximants are test functions on `ℝ^N`
([brezis2011functional] Chapter 9, Remark 17, first sentence). -/
theorem SobolevEuclideanZero.eq_top {N : ℕ} (hp' : p ≠ ⊤) :
    SobolevEuclideanZero N 1 p ⊤ = ⊤ := by
  refine top_unique fun u _ ↦ ?_
  have hS : HasSobolevExtensionOn (⊤ : Submodule ℝ (SobolevEuclidean N 1 p ⊤)) :=
    ⟨(⊤ : Submodule ℝ (SobolevEuclidean N 1 p ⊤)).subtypeL, fun _ ↦ Filter.EventuallyEq.rfl⟩
  obtain ⟨v, hvs, hvc, w, hw, hwt⟩ :=
    SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp' hS
      ⟨u, trivial⟩
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hwt (Eventually.of_forall fun n ↦ ?_)
  exact SobolevMultiIndexZero.testFunctions_le ⟨⟨v n, hvs n, hvc n, subset_univ _⟩, hw n⟩

end Remarks

/-! ### Proposition 9.18: the extension by zero and the distributional derivative -/

section Characterization

variable {N : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The `i`-th vector of the standard basis of `ℝ^N` is `e_i`. -/
theorem EuclideanSpace.basisFun_toBasis_apply (i : Fin N) :
    ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) i
      = EuclideanSpace.single i 1 := by
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]

/-- **Integration by parts of a test function on `Ω` against a `C^1` function on `ℝ^N`**:
`∫_Ω φ ∂_v ψ = -∫_Ω (∂_v φ) ψ`, both integrals being over `Ω` because `φ` vanishes outside it. -/
theorem TestFunction.setIntegral_mul_fderiv_eq_neg {ψ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (φ : 𝓓(Ω, ℝ)) (v : EuclideanSpace ℝ (Fin N)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x * fderiv ℝ ψ x v
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), fderiv ℝ φ x v * ψ x := by
  have h : ∫ x, fderiv ℝ φ x v * ψ x = -∫ x, φ x * fderiv ℝ ψ x v := by
    have := integral_fderiv_smul_eq_neg_integral_smul_apply (Ω := ⊤) (μ := volume)
      (hψ.continuous.locallyIntegrable.locallyIntegrableOn _)
      ((hψ.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
      (fun x _ ↦ (hψ.differentiable one_ne_zero x).hasFDerivAt) v
    simp only [smul_eq_mul] at this
    exact this
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [φ.eq_zero_of_notMem hx, zero_mul],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [← φ.fderivApply_apply v x, (φ.fderivApply v).eq_zero_of_notMem hx, zero_mul],
    h, neg_neg]

namespace SobolevEuclideanZero

/-- **Proposition 9.18, (i) ⇒ (ii)**: for `u ∈ W_0^{1,p}(Ω)`, `p` and `q` Hölder conjugate,
every `C^1` function `φ` with compact support in `ℝ^N` (not in `Ω`) and every `i`,
`|∫_Ω u ∂_i φ| ≤ ‖∂_i u‖_{L^p(Ω)} ‖φ‖_{L^q(Ω)}`. For test functions `u_n → u` in `W^{1,p}(Ω)`,
`∫_Ω u_n ∂_i φ = -∫_Ω (∂_i u_n) φ` by integration by parts of the compactly supported product
(`TestFunction.setIntegral_mul_fderiv_eq_neg`), Hölder's inequality bounds it by
`‖∂_i u_n‖_p ‖φ‖_q`, and both sides pass to the limit ([brezis2011functional] Proposition 9.18,
(i) ⇒ (ii)). -/
theorem abs_integral_fn_smul_fderiv_le [p.HolderConjugate q] (u : SobolevEuclideanZero N 1 p Ω)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (i : Fin N) :
    |∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) x
          * fderiv ℝ φ x (EuclideanSpace.single i 1)|
      ≤ ‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
        * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
  obtain ⟨w, ψ, hψ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto u.2
  have hφq : MemLp φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict _
  have hdφ : MemLp (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφc.fderiv_apply ℝ _)).restrict _
  -- the inequality for each approximant
  have hn : ∀ n, |∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      SobolevMultiIndex.fn (w n) x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
      ≤ ‖SobolevMultiIndex.weakDeriv (w n) (MultiIndexLE.single i)‖
        * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
    intro n
    have e1 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        SobolevMultiIndex.fn (w n) x * fderiv ℝ φ x (EuclideanSpace.single i 1)
        = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) * φ x := by
      rw [← TestFunction.setIntegral_mul_fderiv_eq_neg hφ (ψ n)]
      exact integral_congr_ae ((hψ n).mono fun x hx ↦ by dsimp only; rw [hx])
    have e2 : eLpNorm (fun x ↦ fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)) p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        = eLpNorm (SobolevMultiIndex.weakDeriv (w n) (MultiIndexLE.single i)) p
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      refine (eLpNorm_congr_ae ?_).symm
      rw [← EuclideanSpace.basisFun_toBasis_apply i]
      exact SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction (hψ n) i
    have hH := enorm_integral_smul_le_eLpNorm_mul_eLpNorm
      (ν := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) (p := p) (q := q)
      (a := fun x ↦ fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)) (h := φ)
    simp only [smul_eq_mul] at hH
    rw [e2] at hH
    rw [e1, abs_neg, ← Real.norm_eq_abs, ← toReal_enorm, Lp.norm_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) hφq.eLpNorm_ne_top) hH
  -- the limit
  have hL : Tendsto (fun n ↦ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      SobolevMultiIndex.fn (w n) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) atTop
      (𝓝 (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) x
          * fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    have ht := ((SobolevMultiIndex.fnL ℝ _ 1 p Ω volume).continuous.tendsto _).comp hw
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at ht
    have := tendsto_integral_mul_of_tendsto_eLpNorm (p := p) (q := q)
      (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      (a := fun n ↦ SobolevMultiIndex.fn (w n))
      (a₀ := SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω))
      (b := fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
      (fun n ↦ SobolevMultiIndex.memLp (w n)) (SobolevMultiIndex.memLp _) hdφ ht
    simp only [mul_comm] at this
    exact this
  have hR : Tendsto (fun n ↦ ‖SobolevMultiIndex.weakDeriv (w n) (MultiIndexLE.single i)‖
      * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) atTop
      (𝓝 (‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
        * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) :=
    ((((SobolevMultiIndex.weakDerivL ℝ _ 1 p Ω volume (MultiIndexLE.single i)).continuous.tendsto
      _).comp hw).norm).mul_const _
  exact le_of_tendsto_of_tendsto' hL.abs hR hn

end SobolevEuclideanZero

omit [Fact (1 ≤ p)] in
/-- **Proposition 9.18, (ii) ⇒ (iii)**: for `1 < p < ∞` (`q` the conjugate exponent, `q ≠ ∞`),
if `u ∈ L^p(Ω)` satisfies `|∫_Ω u ∂_i φ| ≤ C ‖φ‖_{L^q(Ω)}` for every `C^1` function `φ` with
compact support in `ℝ^N` and every `i`, then the extension by zero `ū = Ω.indicator u` lies in
`W^{1,p}(ℝ^N)`. Since `∫_{ℝ^N} ū ∂_i φ = ∫_Ω u ∂_i φ` and `‖φ‖_{L^q(Ω)} ≤ ‖φ‖_{L^q(ℝ^N)}`, this is
Proposition 9.3, (ii) ⇒ (i), on `ℝ^N` (`MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le`)
([brezis2011functional] Proposition 9.18, (ii) ⇒ (iii)). -/
theorem SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le [p.HolderConjugate q]
    (hq : q ≠ ⊤) {u : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : MemLp u p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) {C : ℝ}
    (h : ∀ φ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin N,
      |∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
        ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator u) 1 p ⊤ volume := by
  have hΩm := Ω.isOpen.measurableSet
  refine MemSobolev.memSobolevMultiIndex (MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le
    hq ?_ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (C := fun _ ↦ ENNReal.ofReal (max C 0))
    (fun _ ↦ ENNReal.ofReal_ne_top) fun φ i ↦ ?_)
  · simpa only [Measure.restrict_coe_top] using (memLp_indicator_iff_restrict hΩm).2 hu
  · have hφq : eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≠ ⊤ :=
      ((φ.memLp q volume).restrict _).eLpNorm_ne_top
    have hint : ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _),
        fderiv ℝ φ x ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis i)
          • (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator u x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      simp only [Opens.coe_top, Measure.restrict_univ, EuclideanSpace.basisFun_toBasis_apply,
        smul_eq_mul]
      rw [← integral_indicator hΩm]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
      · simp [hx, mul_comm]
      · simp [hx]
    rw [hint, Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
        ≤ ENNReal.ofReal (max C 0 *
            (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) := by
          refine ENNReal.ofReal_le_ofReal
            ((h φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport i).trans ?_)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg
      _ = ENNReal.ofReal (max C 0)
            * eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_toReal hφq]
      _ ≤ ENNReal.ofReal (max C 0)
            * eLpNorm φ q (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)) := by
          simp only [Opens.coe_top, Measure.restrict_univ]
          exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)

end Characterization

/-! ### The chain rule and the positive part preserve `W_0^{1,p}(Ω)` -/

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndexZero

omit [Fact (1 ≤ p)] in
/-- The partial derivative `∂_i v` of an element `v` of `W^{1,p}(Ω)` whose function is `G ∘ u`,
for `G ∈ C^1(ℝ)` with bounded derivative and `u ∈ W^{1,p}(Ω)`, is `G'(u) ∂_i u` almost
everywhere on `Ω`: the chain rule `HasWeakIteratedLineDerivOn.contDiff_comp'` and the
uniqueness of the weak derivative. -/
theorem _root_.SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp
    {u v : SobolevMultiIndex ℝ b 1 p Ω μ} {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ}
    (hM : ∀ t, |deriv G t| ≤ M)
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ G (SobolevMultiIndex.fn u x))
    (i : ι) :
    (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ deriv G (SobolevMultiIndex.fn u x)
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x := by
  have h1 := (SobolevMultiIndex.hasWeakIteratedLineDerivOn v (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).contDiff_comp' hG hM
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2
    ((h1.congr_ae hv (Filter.EventuallyEq.refl _ _)).ae_eq h2)

/-- **The chain rule preserves `W_0^{1,p}(Ω)`**, `1 ≤ p < ∞`: for `G ∈ C^1(ℝ)` with `G 0 = 0`
and `|G'| ≤ M`, and `u ∈ W_0^{1,p}(Ω)`, every element `v` of `W^{1,p}(Ω)` whose function is
`G ∘ u` (one exists by Proposition 9.5, `MemSobolevMultiIndex.contDiff_comp`) lies in
`W_0^{1,p}(Ω)`. This is the content of footnotes 35, 37 and 38 of [brezis2011functional] §9.7
("if `u ∈ H^1_0(Ω)` the assumption `u ∈ C(Ω̄)` can be removed").

Proof: for test functions `u_n → u` in `W^{1,p}(Ω)`, `G ∘ u_n` is `C^1` with compact support in
`Ω`, hence in `W_0^{1,p}(Ω)` by Lemma 9.5; `G ∘ u_n → G ∘ u` in `L^p(Ω)` because
`|G(a) − G(b)| ≤ M |a − b|`, and `∇(G ∘ u_n) = G'(u_n) ∇u_n → G'(u) ∇u` in `L^p(Ω)` along a
subsequence on which `u_n → u` almost everywhere, by splitting
`G'(u_n)(∇u_n − ∇u) + (G'(u_n) − G'(u)) ∇u` — the first term is bounded by `M ‖∇u_n − ∇u‖_p`, the
second tends to `0` by dominated convergence. The closed subspace `W_0^{1,p}(Ω)` contains the
limit. -/
theorem contDiff_comp_mem (hp' : p ≠ ⊤) {u : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (hG0 : G 0 = 0) {M : ℝ} (hM : ∀ t, |deriv G t| ≤ M) {v : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ G (SobolevMultiIndex.fn u x)) :
    v ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hΩm := Ω.isOpen.measurableSet
  have hG' : Continuous (deriv G) := hG.continuous_deriv le_rfl
  obtain ⟨w, φ, hφ, hw⟩ := exists_seq_testFunction_tendsto hu
  -- the test functions converge to `u` in `L^p(Ω)`, and almost everywhere along a subsequence
  have hφu : Tendsto (fun n ↦ eLpNorm ((φ n : E → ℝ) - SobolevMultiIndex.fn u) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) :=
    (SobolevMultiIndex.tendsto_eLpNorm_fn_sub hw).congr fun n ↦
      eLpNorm_congr_ae ((hφ n).sub (Filter.EventuallyEq.refl _ _))
  obtain ⟨ns, hns, -, -, hae, -⟩ := exists_subseq_tendsto_ae_ae_le_of_tendsto_eLpNorm
    (fun n ↦ ((φ n).memLp p μ).restrict _) (SobolevMultiIndex.memLp u) hφu
  -- `G ∘ φ n` lies in `W_0^{1,p}(Ω)`
  have hGφ : ∀ n, ContDiff ℝ 1 fun x ↦ G (φ n x) := fun n ↦
    hG.comp ((φ n).contDiff.of_le (by simp))
  have hGφc : ∀ n, HasCompactSupport fun x ↦ G (φ n x) := fun n ↦
    (φ n).hasCompactSupport.comp_left hG0
  have hGφΩ : ∀ n, tsupport (fun x ↦ G (φ n x)) ⊆ Ω := fun n ↦
    (tsupport_comp_subset hG0 (φ n : E → ℝ)).trans (φ n).tsupport_subset
  choose V hV using fun n ↦ (hGφ n).exists_sobolevMultiIndex_of_hasCompactSupport'
    (b := b) (p := p) (Ω := Ω) (μ := μ) (hGφc n)
  have hVmem : ∀ n, V n ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := fun n ↦
    SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset hp' (V n) (hGφc n) (hGφΩ n) (hV n)
  -- `V (ns k) → v` in `W^{1,p}(Ω)`
  refine isClosed.mem_of_tendsto (f := fun k ↦ V (ns k)) (b := atTop) ?_
    (Eventually.of_forall fun k ↦ hVmem _)
  refine SobolevMultiIndex.tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun α ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
  · -- the functions: `|G(φ_n) − G(u)| ≤ M |φ_n − u|`
    have hbd : ∀ k, eLpNorm ((SobolevMultiIndex.weakDeriv (V (ns k)) 0 : E → ℝ)
        - (SobolevMultiIndex.weakDeriv v 0 : E → ℝ)) p (μ.restrict (Ω : Set E))
        ≤ ENNReal.ofReal M * eLpNorm ((φ (ns k) : E → ℝ) - SobolevMultiIndex.fn u) p
          (μ.restrict (Ω : Set E)) := by
      intro k
      have heq : ((SobolevMultiIndex.weakDeriv (V (ns k)) 0 : E → ℝ)
          - (SobolevMultiIndex.weakDeriv v 0 : E → ℝ)) =ᵐ[μ.restrict (Ω : Set E)]
          fun x ↦ G (φ (ns k) x) - G (SobolevMultiIndex.fn u x) := (hV (ns k)).sub hv
      rw [eLpNorm_congr_ae heq]
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x ↦ ?_) p
      · exact (hGφ _).continuous.aestronglyMeasurable.sub
          (hG.continuous.comp_aestronglyMeasurable (SobolevMultiIndex.memLp u).aestronglyMeasurable)
      · simp only [Real.norm_eq_abs, Pi.sub_apply]
        exact abs_sub_le_mul_of_abs_deriv_le hG hM _ _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
    simpa using ENNReal.Tendsto.const_mul (hφu.comp hns.tendsto_atTop)
      (Or.inr ENNReal.ofReal_ne_top)
  · -- the derivatives: `G'(φ_n) ∂_i φ_n → G'(u) ∂_i u`
    have hdV : ∀ k, (SobolevMultiIndex.weakDeriv (V k) (MultiIndexLE.single i) : E → ℝ)
        =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ deriv G (φ k x)
          * SobolevMultiIndex.weakDeriv (w k) (MultiIndexLE.single i) x := fun k ↦ by
      refine (SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp (u := w k) hG hM
        ((hV k).trans ((hφ k).mono fun x hx ↦ by dsimp only; rw [hx])) i).trans ?_
      filter_upwards [hφ k] with x hx
      rw [hx]
    have hdv := SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp hG hM hv i
    have hsplit : ∀ k, ((SobolevMultiIndex.weakDeriv (V (ns k)) (MultiIndexLE.single i) : E → ℝ)
        - (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ))
        =ᵐ[μ.restrict (Ω : Set E)]
          (fun x ↦ deriv G (φ (ns k) x)
            * (SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) x
              - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x))
          + fun x ↦ (deriv G (φ (ns k) x) - deriv G (SobolevMultiIndex.fn u x))
            * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x := by
      intro k
      filter_upwards [hdV (ns k), hdv] with x h1 h2
      simp only [Pi.sub_apply, Pi.add_apply, h1, h2]
      ring
    have hA : Tendsto (fun k ↦ eLpNorm (fun x ↦ deriv G (φ (ns k) x)
        * (SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) x
          - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)) p
        (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
      have hbd : ∀ k, eLpNorm (fun x ↦ deriv G (φ (ns k) x)
          * (SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) x
            - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)) p
          (μ.restrict (Ω : Set E))
          ≤ ENNReal.ofReal M * eLpNorm
            ((SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) : E → ℝ)
              - (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : E → ℝ)) p
            (μ.restrict (Ω : Set E)) := fun k ↦ by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x ↦ ?_) p
        · exact (hG'.comp_aestronglyMeasurable (φ _).contDiff.continuous.aestronglyMeasurable).mul
            ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
        · simp only [norm_mul, Real.norm_eq_abs, Pi.sub_apply]
          exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le)
        hbd
      simpa using ENNReal.Tendsto.const_mul
        ((SobolevMultiIndex.tendsto_eLpNorm_weakDeriv_sub hw (MultiIndexLE.single i)).comp
          hns.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
    have hB : Tendsto (fun k ↦ eLpNorm ((fun x ↦
        (deriv G (φ (ns k) x) - deriv G (SobolevMultiIndex.fn u x))
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x) - (0 : E → ℝ)) p
        (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp' (g := 0)
        (bound := fun x ↦ 2 * M * ‖SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x‖)
        (fun k ↦ ?_) aestronglyMeasurable_zero ((Lp.memLp _).norm.const_mul _)
        (fun k ↦ Eventually.of_forall fun x ↦ ?_) ?_
      · exact ((hG'.comp_aestronglyMeasurable (φ _).contDiff.continuous.aestronglyMeasurable).sub
          (hG'.comp_aestronglyMeasurable (SobolevMultiIndex.memLp u).aestronglyMeasurable)).mul
          (Lp.aestronglyMeasurable _)
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Real.norm_eq_abs, two_mul]
        exact (abs_sub _ _).trans (add_le_add (hM _) (hM _))
      · filter_upwards [hae] with x hx
        have := (((hG'.tendsto _).comp hx).sub
          (tendsto_const_nhds (x := deriv G (SobolevMultiIndex.fn u x)))).mul_const
          (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)
        simpa [Function.comp_def] using this
    have hbd : ∀ k, eLpNorm ((SobolevMultiIndex.weakDeriv (V (ns k)) (MultiIndexLE.single i) :
        E → ℝ) - (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ)) p
        (μ.restrict (Ω : Set E))
        ≤ eLpNorm (fun x ↦ deriv G (φ (ns k) x)
            * (SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) x
              - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)) p
            (μ.restrict (Ω : Set E))
          + eLpNorm ((fun x ↦ (deriv G (φ (ns k) x) - deriv G (SobolevMultiIndex.fn u x))
            * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x) - (0 : E → ℝ)) p
            (μ.restrict (Ω : Set E)) := fun k ↦ by
      rw [eLpNorm_congr_ae (hsplit k), sub_zero]
      exact eLpNorm_add_le hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
    simpa using hA.add hB

end SobolevMultiIndexZero

end ChainRule

section PosPart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndexZero

omit [Fact (1 ≤ p)] in
/-- The partial derivative of an element `v` of `W^{1,p}(Ω)` whose function is `u⁺ = max u 0`,
for `u ∈ W^{1,p}(Ω)`, is `{u > 0}.indicator (∂_i u)` almost everywhere on `Ω`
(`HasWeakIteratedLineDerivOn.posPart` and the uniqueness of the weak derivative). -/
theorem _root_.SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart
    {u v : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ max (SobolevMultiIndex.fn u x) 0) (i : ι) :
    (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
      {x | 0 < SobolevMultiIndex.fn u x}.indicator
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)) := by
  have h1 := (SobolevMultiIndex.hasWeakIteratedLineDerivOn v (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).posPart
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2
    ((h1.congr_ae hv (Filter.EventuallyEq.refl _ _)).ae_eq h2)

/-- **The positive part preserves `W_0^{1,p}(Ω)`**, `1 ≤ p < ∞`: for `u ∈ W_0^{1,p}(Ω)`, every
element `v` of `W^{1,p}(Ω)` whose function is `u⁺ = max u 0` (one exists by
`MemSobolevMultiIndex.posPart`) lies in `W_0^{1,p}(Ω)`. The `C^1` approximations
`G_ε(s) = √((max s 0)² + ε²) − ε` of the positive part have `G_ε(u) ∈ W_0^{1,p}(Ω)` by the
chain rule (`SobolevMultiIndexZero.contDiff_comp_mem`), and `G_ε(u) → u⁺` in `W^{1,p}(Ω)` as
`ε → 0` by dominated convergence, with `|G_ε(u)| ≤ |u|` and `|G_ε'(u) ∂_i u| ≤ |∂_i u|`
(Kinderlehrer and Stampacchia, *An Introduction to Variational Inequalities and Their
Applications*, Theorem II.A.1; the obstacle set `{v ∈ H^1_0(Ω) : v ≥ ψ}` is nonempty because of
it). -/
theorem posPart_mem (hp' : p ≠ ⊤) {u : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ) {v : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ max (SobolevMultiIndex.fn u x) 0) :
    v ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hum : AEStronglyMeasurable (SobolevMultiIndex.fn u) (μ.restrict (Ω : Set E)) :=
    (SobolevMultiIndex.memLp u).aestronglyMeasurable
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by rw [hεdef]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := hεdef ▸ tendsto_one_div_add_atTop_nhds_zero_nat
  -- the approximants `G_{ε n}(u)`, in `W_0^{1,p}(Ω)`
  have hGn : ∀ n, MemSobolevMultiIndex b (fun x ↦ posPartApprox (ε n) (SobolevMultiIndex.fn u x))
      1 p Ω μ := fun n ↦ (SobolevMultiIndex.memSobolevMultiIndex u).contDiff_comp hp
    (contDiff_posPartApprox (hεpos n)) (posPartApprox_zero (hεpos n).le)
    (abs_deriv_posPartApprox_le (hεpos n))
  choose V hV using fun n ↦ (hGn n).exists_sobolevMultiIndex
  have hVmem : ∀ n, V n ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := fun n ↦
    contDiff_comp_mem hp' hu (contDiff_posPartApprox (hεpos n)) (posPartApprox_zero (hεpos n).le)
      (abs_deriv_posPartApprox_le (hεpos n)) (hV n)
  -- `V n → v` in `W^{1,p}(Ω)`
  refine isClosed.mem_of_tendsto (f := V) (b := atTop) ?_ (Eventually.of_forall hVmem)
  refine SobolevMultiIndex.tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun α ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
  · -- the functions: `G_ε(u) → u⁺`, dominated by `|u|`
    have heq : ∀ n, ((SobolevMultiIndex.weakDeriv (V n) 0 : E → ℝ)
        - (SobolevMultiIndex.weakDeriv v 0 : E → ℝ)) =ᵐ[μ.restrict (Ω : Set E)]
        (fun x ↦ posPartApprox (ε n) (SobolevMultiIndex.fn u x))
          - fun x ↦ max (SobolevMultiIndex.fn u x) 0 := fun n ↦ (hV n).sub hv
    refine (tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp'
      (bound := fun x ↦ ‖SobolevMultiIndex.fn u x‖) (fun n ↦ ?_) ?_ (SobolevMultiIndex.memLp u).norm
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)).congr
      fun n ↦ (eLpNorm_congr_ae (heq n)).symm
    · exact (contDiff_posPartApprox (hεpos n)).continuous.comp_aestronglyMeasurable hum
    · exact (continuous_id.max continuous_const).comp_aestronglyMeasurable hum
    · exact (abs_posPartApprox_le (hεpos n).le _).trans (Real.norm_eq_abs _).symm.le
    · exact (tendsto_posPartApprox _).comp hεt
  · -- the derivatives: `G_ε'(u) ∂_i u → {u > 0}.indicator (∂_i u)`, dominated by `|∂_i u|`
    have hdV : ∀ n, (SobolevMultiIndex.weakDeriv (V n) (MultiIndexLE.single i) : E → ℝ)
        =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ deriv (posPartApprox (ε n)) (SobolevMultiIndex.fn u x)
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x := fun n ↦
      SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp (contDiff_posPartApprox (hεpos n))
        (abs_deriv_posPartApprox_le (hεpos n)) (hV n) i
    have hdv := SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart hv i
    have heq : ∀ n, ((SobolevMultiIndex.weakDeriv (V n) (MultiIndexLE.single i) : E → ℝ)
        - (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ))
        =ᵐ[μ.restrict (Ω : Set E)]
        (fun x ↦ deriv (posPartApprox (ε n)) (SobolevMultiIndex.fn u x)
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)
          - {x | 0 < SobolevMultiIndex.fn u x}.indicator
            (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)) := fun n ↦ (hdV n).sub hdv
    have hind : ∀ x, {x | 0 < SobolevMultiIndex.fn u x}.indicator
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)) x
        = (if 0 < SobolevMultiIndex.fn u x then 1 else 0)
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x := fun x ↦ by
      by_cases hx : 0 < SobolevMultiIndex.fn u x <;> simp [Set.indicator, hx]
    refine (tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp'
      (bound := fun x ↦ ‖SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x‖) (fun n ↦ ?_) ?_
      (Lp.memLp _).norm (fun n ↦ Eventually.of_forall fun x ↦ ?_)
      (Eventually.of_forall fun x ↦ ?_)).congr fun n ↦ (eLpNorm_congr_ae (heq n)).symm
    · exact (((contDiff_posPartApprox (hεpos n)).continuous_deriv le_rfl).comp_aestronglyMeasurable
        hum).mul (Lp.aestronglyMeasurable _)
    · exact aestronglyMeasurable_indicator_pos hum (Lp.aestronglyMeasurable _)
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_deriv_posPartApprox_le (hεpos n) _)
    · have e : ∀ n, deriv (posPartApprox (ε n)) (SobolevMultiIndex.fn u x)
          = max (SobolevMultiIndex.fn u x) 0 / √(posSq (SobolevMultiIndex.fn u x) + ε n ^ 2) :=
        fun n ↦ deriv_posPartApprox (hεpos n) _
      simp_rw [e, hind x]
      exact ((tendsto_deriv_posPartApprox _).comp hεt).mul_const _

end SobolevMultiIndexZero

/-- **The positive part preserves `W_0^{1,p}(Ω)`** on an open `Ω ⊆ ℝ^N`, `1 ≤ p < ∞`: for
`u ∈ W_0^{1,p}(Ω)` and `v ∈ W^{1,p}(Ω)` with `v = u⁺ = max u 0`, `v ∈ W_0^{1,p}(Ω)`; the
instance of `SobolevMultiIndexZero.posPart_mem` on `SobolevEuclideanZero`. Together with
`MemSobolevMultiIndex.posPart` (existence of `v`), this is what makes the obstacle set
`{v ∈ H^1_0(Ω) : v ≥ ψ a.e.}` nonempty when `ψ ∈ H^1(Ω)` has `ψ⁺ ∈ H^1_0(Ω)` (Kinderlehrer and
Stampacchia, *An Introduction to Variational Inequalities and Their Applications*,
Theorem II.A.1). -/
theorem SobolevEuclideanZero.posPart_mem {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (hp' : p ≠ ⊤) (u : SobolevEuclideanZero N 1 p Ω) {v : SobolevEuclidean N 1 p Ω}
    (hv : SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ max (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) x) 0) :
    v ∈ SobolevEuclideanZero N 1 p Ω :=
  SobolevMultiIndexZero.posPart_mem hp' u.2 hv

end PosPart

/-! ### Theorem 9.17, (i) ⇒ (ii): a continuous function vanishing on the boundary is in `W_0^{1,p}`

The truncation `G(t) = t · smoothTransition(t² − 1)` of the book's proof: smooth, `G(t) = 0` for
`|t| ≤ 1`, `G(t) = t` for `|t| ≥ 2` (in fact for `|t| ≥ √2`), with bounded derivative. -/

section StepTruncation

/-- The truncation `G(t) = t · smoothTransition(t² − 1)` of the proof of
[brezis2011functional] Theorem 9.17: smooth, `G(t) = 0` for `|t| ≤ 1`, `G(t) = t` for
`|t| ≥ 2`, `|G(t)| ≤ |t|`, with bounded derivative. -/
def stepTruncation (t : ℝ) : ℝ := t * Real.smoothTransition (t ^ 2 - 1)

/-- The truncation is smooth. -/
theorem contDiff_stepTruncation : ContDiff ℝ ∞ stepTruncation :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp ((contDiff_id.pow 2).sub contDiff_const))

/-- `G(0) = 0`. -/
theorem stepTruncation_zero : stepTruncation 0 = 0 := by simp [stepTruncation]

/-- `G(t) = 0` for `|t| ≤ 1`. -/
theorem stepTruncation_of_abs_le {t : ℝ} (ht : |t| ≤ 1) : stepTruncation t = 0 := by
  have h : t ^ 2 - 1 ≤ 0 := by nlinarith [abs_nonneg t, sq_abs t]
  simp [stepTruncation, Real.smoothTransition.zero_of_nonpos h]

/-- `G(t) = t` for `|t| ≥ 2`. -/
theorem stepTruncation_of_two_le {t : ℝ} (ht : 2 ≤ |t|) : stepTruncation t = t := by
  have h : 1 ≤ t ^ 2 - 1 := by nlinarith [sq_abs t]
  simp [stepTruncation, Real.smoothTransition.one_of_one_le h]

/-- `|G(t)| ≤ |t|`. -/
theorem abs_stepTruncation_le (t : ℝ) : |stepTruncation t| ≤ |t| := by
  rw [stepTruncation, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.le_one _)

/-- `G' = 0` where `|t| < 1`. -/
theorem deriv_stepTruncation_of_abs_lt {t : ℝ} (ht : |t| < 1) : deriv stepTruncation t = 0 := by
  have hev : stepTruncation =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds ht)
      fun s hs ↦ stepTruncation_of_abs_le hs.le
  rw [hev.deriv_eq, deriv_const]

/-- `G' = 1` where `|t| > 2`. -/
theorem deriv_stepTruncation_of_two_lt {t : ℝ} (ht : 2 < |t|) : deriv stepTruncation t = 1 := by
  have hev : stepTruncation =ᶠ[𝓝 t] id :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_abs).mem_nhds ht)
      fun s hs ↦ stepTruncation_of_two_le hs.le
  rw [hev.deriv_eq, deriv_id]

/-- `G'` is bounded: it is continuous, and equal to `1` outside `[-2, 2]`. -/
theorem exists_abs_deriv_stepTruncation_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv stepTruncation t| ≤ M := by
  have hc : Continuous (deriv stepTruncation) := contDiff_stepTruncation.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, zero_le_one.trans (le_max_right _ _), fun t ↦ ?_⟩
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · exact (Real.norm_eq_abs _).symm.le.trans ((hC t ht).trans (le_max_left _ _))
  · have h2 : 2 < |t| := by
      rw [lt_abs]
      rcases not_and_or.1 ht with h | h
      · right; linarith [not_le.1 h]
      · left; exact not_le.1 h
    rw [deriv_stepTruncation_of_two_lt h2, abs_one]
    exact le_max_right _ _

/-- The scaled truncation `G_c(t) = c⁻¹ G(c t)`, `c > 0`: it vanishes for `|t| ≤ 1/c`, is the
identity for `|t| ≥ 2/c`, and has the derivative `G'(c t)`. -/
theorem hasDerivAt_scaled_stepTruncation {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (fun s ↦ c⁻¹ * stepTruncation (s * c)) (deriv stepTruncation (t * c)) t := by
  have h := ((contDiff_stepTruncation.differentiable (by simp)) (t * c)).hasDerivAt.comp t
    (hasDerivAt_mul_const c)
  have := h.const_mul c⁻¹
  convert this using 1
  · rfl
  · field_simp

end StepTruncation

section ContinuousBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndex

/-- **Theorem 9.17, (i) ⇒ (ii), for a function with bounded support**: on any open `Ω`,
`1 ≤ p < ∞`, an element `u` of `W^{1,p}(Ω)` with a representative `ũ` continuous on `closure Ω`,
vanishing on `∂Ω` and outside a ball, lies in `W_0^{1,p}(Ω)`.

Proof ([brezis2011functional] Theorem 9.17, (i) ⇒ (ii), with one change): with the truncations
`G_n(t) = G(nt)/n` of `stepTruncation`, `u_n = G_n ∘ u ∈ W^{1,p}(Ω)` by Proposition 9.5, and
`supp u_n ⊆ {|ũ| ≥ 1/n}` is a compact subset of `Ω` (closed and bounded in `closure Ω`, missing
`∂Ω` where `ũ = 0`), so `u_n ∈ W_0^{1,p}(Ω)` by Lemma 9.5. The book's "`u_n → u` in `W^{1,p}` by
dominated convergence" silently uses `∇u = 0` a.e. on `{u = 0}`; instead, `u_n → ũ` and
`∇u_n = G_n'(ũ) ∇u → {ũ ≠ 0}.indicator ∇u` in `L^p(Ω)` by dominated convergence (`G_n'(0) = 0`
and `G_n'(t) = 1` for `n |t| > 2`), so `(u_n)` is Cauchy in `W^{1,p}(Ω)`; its limit lies in the
closed subspace `W_0^{1,p}(Ω)` and has function `ũ`, so it is `u`. -/
theorem mem_zero_of_continuousOn_closure_of_eqOn_frontier_of_forall_eq_zero (hp' : p ≠ ⊤)
    (u : SobolevMultiIndex ℝ b 1 p Ω μ) {ũ : E → ℝ} (hu : fn u =ᵐ[μ.restrict (Ω : Set E)] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (h0 : EqOn ũ 0 (frontier Ω)) {R : ℝ}
    (hR : ∀ x, R < ‖x‖ → ũ x = 0) : u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hΩm := Ω.isOpen.measurableSet
  have hum : AEStronglyMeasurable ũ (μ.restrict (Ω : Set E)) :=
    (memLp u).aestronglyMeasurable.congr hu
  have hũp : MemLp ũ p (μ.restrict (Ω : Set E)) := (memLp u).ae_eq hu
  obtain ⟨M, -, hM⟩ := exists_abs_deriv_stepTruncation_le
  -- the scaled truncations `G_n(t) = G((n+1) t)/(n+1)`
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℝ → ℝ,
      G = fun (n : ℕ) (t : ℝ) ↦ ((n : ℝ) + 1)⁻¹ * stepTruncation (t * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hcpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n ↦ by positivity
  have hGd : ∀ n t, HasDerivAt (G n) (deriv stepTruncation (t * ((n : ℝ) + 1))) t := fun n t ↦ by
    rw [hGdef]
    exact hasDerivAt_scaled_stepTruncation (hcpos n).ne' t
  have hGc : ∀ n, ContDiff ℝ 1 (G n) := fun n ↦ by
    rw [hGdef]
    exact contDiff_const.mul
      ((contDiff_stepTruncation.of_le (by simp)).comp (contDiff_id.mul contDiff_const))
  have hG0 : ∀ n, G n 0 = 0 := fun n ↦ by simp [hGdef, stepTruncation_zero]
  have hGderiv : ∀ n t, deriv (G n) t = deriv stepTruncation (t * ((n : ℝ) + 1)) :=
    fun n t ↦ (hGd n t).deriv
  have hGM : ∀ n t, |deriv (G n) t| ≤ M := fun n t ↦ by rw [hGderiv]; exact hM _
  have hGle : ∀ n t, |G n t| ≤ M * |t| := fun n t ↦ by
    simpa [hG0 n] using abs_sub_le_mul_of_abs_deriv_le (hGc n) (hGM n) t 0
  have hGzero : ∀ (n : ℕ) (t : ℝ), |t| * ((n : ℝ) + 1) ≤ 1 → G n t = 0 := fun n t ht ↦ by
    simp only [hGdef]
    rw [stepTruncation_of_abs_le (by rwa [abs_mul, abs_of_pos (hcpos n)]), mul_zero]
  have hGid : ∀ (n : ℕ) (t : ℝ), 2 ≤ |t| * ((n : ℝ) + 1) → G n t = t := fun n t ht ↦ by
    simp only [hGdef]
    rw [stepTruncation_of_two_le (by rwa [abs_mul, abs_of_pos (hcpos n)])]
    field_simp
  have hGd0 : ∀ n, deriv (G n) 0 = 0 := fun n ↦ by
    rw [hGderiv, zero_mul]
    exact deriv_stepTruncation_of_abs_lt (by simp)
  have hGd1 : ∀ (n : ℕ) (t : ℝ), 2 < |t| * ((n : ℝ) + 1) → deriv (G n) t = 1 := fun n t ht ↦ by
    rw [hGderiv]
    exact deriv_stepTruncation_of_two_lt (by rwa [abs_mul, abs_of_pos (hcpos n)])
  have hev : ∀ t : ℝ, t ≠ 0 → ∀ n ≥ ⌈2 / |t|⌉₊, 2 < |t| * ((n : ℝ) + 1) := fun t ht n hn ↦ by
    have hpos : 0 < |t| := abs_pos.2 ht
    have h1 : 2 / |t| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [div_le_iff₀ hpos] at h1
    nlinarith
  -- the truncated functions `u_n = G_n ∘ u`, as elements of `W^{1,p}(Ω)`
  choose U hU using fun n ↦
    ((memSobolevMultiIndex u).contDiff_comp hp (hGc n) (hG0 n) (hGM n)).exists_sobolevMultiIndex
  have hUũ : ∀ n, fn (U n) =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ G n (ũ x) := fun n ↦
    (hU n).trans (hu.mono fun x hx ↦ by dsimp only; rw [hx])
  -- (a) each `u_n` has compact support in `Ω`, hence lies in `W_0^{1,p}(Ω)`
  have hUmem : ∀ n, U n ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
    intro n
    have hK1 : IsClosed (closure (Ω : Set E) ∩ (fun x ↦ |ũ x|) ⁻¹' Ici (((n : ℝ) + 1)⁻¹)) :=
      (continuous_abs.comp_continuousOn hc).preimage_isClosed_of_isClosed isClosed_closure
        isClosed_Ici
    have hK : IsCompact (closure (Ω : Set E) ∩ (fun x ↦ |ũ x|) ⁻¹' Ici (((n : ℝ) + 1)⁻¹)
        ∩ closedBall 0 R) :=
      (isCompact_closedBall (0 : E) R).inter_left hK1
    refine mem_zero_of_ae_eq_zero_compl_isCompact hp' (U n) hK ?_ ?_
    · rintro x ⟨⟨hxc, hx⟩, -⟩
      rw [closure_eq_interior_union_frontier, Ω.isOpen.interior_eq] at hxc
      rcases hxc with hxΩ | hxf
      · exact hxΩ
      · exfalso
        have h1 : ((n : ℝ) + 1)⁻¹ ≤ |ũ x| := hx
        rw [h0 hxf, Pi.zero_apply, abs_zero] at h1
        exact absurd h1 (not_le.2 (inv_pos.2 (hcpos n)))
    · filter_upwards [hUũ n, ae_restrict_mem hΩm] with x hx hxΩ hxK
      rw [hx]
      by_cases hxR : R < ‖x‖
      · rw [hR x hxR, hG0]
      · have hxb : x ∈ closedBall (0 : E) R := by
          rw [mem_closedBall_zero_iff]
          exact not_lt.1 hxR
        have hlt : ¬ ((n : ℝ) + 1)⁻¹ ≤ |ũ x| := fun h ↦ hxK ⟨⟨subset_closure hxΩ, h⟩, hxb⟩
        have h1 : |ũ x| ≤ 1 / ((n : ℝ) + 1) := by rw [one_div]; exact (not_le.1 hlt).le
        exact hGzero n _ ((le_div_iff₀ (hcpos n)).1 h1)
  -- (b) `u_n → ũ` in `L^p(Ω)`
  have hL0 : Tendsto (fun n ↦ eLpNorm ((fun x ↦ G n (ũ x)) - ũ) p (μ.restrict (Ω : Set E)))
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp' (bound := fun x ↦ M * ‖ũ x‖)
      (fun n ↦ (hGc n).continuous.comp_aestronglyMeasurable hum) hum (hũp.norm.const_mul M)
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · simpa [Real.norm_eq_abs] using hGle n (ũ x)
    · by_cases hx : ũ x = 0
      · simp [hx, hG0]
      · exact tendsto_atTop_of_eventually_const (i₀ := ⌈2 / |ũ x|⌉₊) fun n hn ↦
          hGid n _ (hev _ hx n hn).le
  -- (b') `∇u_n = G_n'(ũ) ∇u → {ũ ≠ 0}.indicator ∇u` in `L^p(Ω)`
  have hdU : ∀ n i, (weakDeriv (U n) (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ deriv (G n) (ũ x) * weakDeriv u (MultiIndexLE.single i) x := fun n i ↦
    (weakDeriv_single_ae_eq_of_fn_ae_eq_comp (hGc n) (hGM n) (hU n) i).trans
      (hu.mono fun x hx ↦ by dsimp only; rw [hx])
  have hind : AEStronglyMeasurable (fun x ↦ if ũ x = 0 then (0 : ℝ) else 1)
      (μ.restrict (Ω : Set E)) := by
    have hm : Measurable fun t : ℝ ↦ if t = 0 then (0 : ℝ) else 1 :=
      Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const
    exact (hm.comp_aemeasurable hum.aemeasurable).aestronglyMeasurable
  have hLi : ∀ i, Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ deriv (G n) (ũ x) * weakDeriv u (MultiIndexLE.single i) x)
        - fun x ↦ (if ũ x = 0 then (0 : ℝ) else 1) * weakDeriv u (MultiIndexLE.single i) x) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
    intro i
    refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp'
      (bound := fun x ↦ M * ‖weakDeriv u (MultiIndexLE.single i) x‖)
      (fun n ↦ (((hGc n).continuous_deriv le_rfl).comp_aestronglyMeasurable hum).mul
        (Lp.aestronglyMeasurable _))
      (hind.mul (Lp.aestronglyMeasurable _)) ((Lp.memLp _).norm.const_mul M)
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hGM n _) (norm_nonneg _)
    · by_cases hx : ũ x = 0
      · simp [hx, hGd0]
      · simp only [hx, ite_false]
        exact tendsto_atTop_of_eventually_const (i₀ := ⌈2 / |ũ x|⌉₊) fun n hn ↦ by
          rw [hGd1 n _ (hev _ hx n hn)]
  -- the limits, as elements of `L^p(Ω)`
  have hHp : ∀ i, MemLp (fun x ↦ (if ũ x = 0 then (0 : ℝ) else 1)
      * weakDeriv u (MultiIndexLE.single i) x) p (μ.restrict (Ω : Set E)) := fun i ↦
    (Lp.memLp (weakDeriv u (MultiIndexLE.single i))).of_le (hind.mul (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun x ↦ by
        rw [norm_mul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        split_ifs <;> simp)
  have hT0 : Tendsto (fun n ↦ weakDeriv (U n) 0) atTop (𝓝 (hũp.toLp ũ)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    exact hL0.congr fun n ↦ (eLpNorm_congr_ae ((hUũ n).sub (Filter.EventuallyEq.refl _ _))).symm
  have hTi : ∀ i, Tendsto (fun n ↦ weakDeriv (U n) (MultiIndexLE.single i)) atTop
      (𝓝 ((hHp i).toLp _)) := fun i ↦ by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    exact (hLi i).congr fun n ↦
      (eLpNorm_congr_ae ((hdU n i).sub (Filter.EventuallyEq.refl _ _))).symm
  -- (c) `(u_n)` is Cauchy in `W^{1,p}(Ω)`
  have hnorm : ∀ n m, ‖U n - U m‖
      ≤ (‖weakDeriv (U n) 0 - hũp.toLp ũ‖
          + ∑ i, ‖weakDeriv (U n) (MultiIndexLE.single i) - (hHp i).toLp _‖)
        + (‖weakDeriv (U m) 0 - hũp.toLp ũ‖
          + ∑ i, ‖weakDeriv (U m) (MultiIndexLE.single i) - (hHp i).toLp _‖) := by
    intro n m
    refine (norm_le_sum_norm_weakDeriv (U n - U m)).trans ?_
    rw [MultiIndexLE.sum_univ_one]
    have e : ∀ α, weakDeriv (U n - U m) α = weakDeriv (U n) α - weakDeriv (U m) α := fun _ ↦ rfl
    simp only [e]
    have key : ∀ (a c z : Lp ℝ p (μ.restrict (Ω : Set E))), ‖a - c‖ ≤ ‖a - z‖ + ‖c - z‖ :=
      fun a c z ↦ by rw [← sub_sub_sub_cancel_right a c z]; exact norm_sub_le _ _
    calc ‖weakDeriv (U n) 0 - weakDeriv (U m) 0‖
          + ∑ i, ‖weakDeriv (U n) (MultiIndexLE.single i) - weakDeriv (U m) (MultiIndexLE.single i)‖
        ≤ (‖weakDeriv (U n) 0 - hũp.toLp ũ‖ + ‖weakDeriv (U m) 0 - hũp.toLp ũ‖)
          + ∑ i, (‖weakDeriv (U n) (MultiIndexLE.single i) - (hHp i).toLp _‖
            + ‖weakDeriv (U m) (MultiIndexLE.single i) - (hHp i).toLp _‖) :=
          add_le_add (key _ _ _) (Finset.sum_le_sum fun i _ ↦ key _ _ _)
      _ = _ := by rw [Finset.sum_add_distrib]; ring
  have he : Tendsto (fun n ↦ ‖weakDeriv (U n) 0 - hũp.toLp ũ‖
      + ∑ i, ‖weakDeriv (U n) (MultiIndexLE.single i) - (hHp i).toLp _‖) atTop (𝓝 0) := by
    have h1 := tendsto_iff_norm_sub_tendsto_zero.1 hT0
    have h2 : ∀ i, Tendsto (fun n ↦ ‖weakDeriv (U n) (MultiIndexLE.single i) - (hHp i).toLp _‖)
        atTop (𝓝 0) := fun i ↦ tendsto_iff_norm_sub_tendsto_zero.1 (hTi i)
    simpa using h1.add (tendsto_finsetSum Finset.univ fun i _ ↦ h2 i)
  have hcauchy : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 he) (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1 h2
    rw [dist_eq_norm]
    linarith [hnorm m n]
  -- (d) the limit lies in `W_0^{1,p}(Ω)` and is `u`
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hVmem : V ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ :=
    SobolevMultiIndexZero.isClosed.mem_of_tendsto hV (Eventually.of_forall hUmem)
  have hV0 : weakDeriv V 0 = hũp.toLp ũ :=
    tendsto_nhds_unique (((weakDerivL ℝ b 1 p Ω μ 0).continuous.tendsto V).comp hV) hT0
  have hVu : V = u := by
    refine ext_of_fn_ae_eq ?_
    have h1 : (weakDeriv V 0 : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)] ũ := by
      rw [hV0]
      exact hũp.coeFn_toLp
    exact h1.trans hu.symm
  rw [← hVu]
  exact hVmem

/-- **Theorem 9.17, (i) ⇒ (ii), on any open set** (Remark 19: this direction needs no
smoothness of `Ω`), `1 ≤ p < ∞`: an element `u` of `W^{1,p}(Ω)` with a representative `ũ`
continuous on `closure Ω` and vanishing on `∂Ω` lies in `W_0^{1,p}(Ω)`. The case of bounded
support is `SobolevMultiIndex.mem_zero_of_continuousOn_closure_of_eqOn_frontier_of_forall_eq_zero`;
in general, `ζ_n u → u` in `W^{1,p}(Ω)` for the cut-off sequence `ζ_n`
(`SobolevMultiIndex.tendsto_cutoff_smul`), each `ζ_n u` has the representative `ζ_n ũ` of bounded
support, and `W_0^{1,p}(Ω)` is closed ([brezis2011functional] Theorem 9.17, (i) ⇒ (ii), and
Remark 19). -/
theorem mem_zero_of_continuousOn_closure_of_eqOn_frontier (hp' : p ≠ ⊤)
    (u : SobolevMultiIndex ℝ b 1 p Ω μ) {ũ : E → ℝ} (hu : fn u =ᵐ[μ.restrict (Ω : Set E)] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (h0 : EqOn ũ 0 (frontier Ω)) :
    u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  obtain ⟨ζ, hζ, hζ1, hζs, hζ01⟩ := exists_contDiff_eqOn_one_closedBall_one E
  obtain ⟨v, hv, -, hvt⟩ :=
    tendsto_cutoff_smul hp' hζ hζ01 hζ1 (hζs.trans ball_subset_closedBall) u
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hvt (Eventually.of_forall fun n ↦ ?_)
  refine mem_zero_of_continuousOn_closure_of_eqOn_frontier_of_forall_eq_zero hp' (v n)
    (ũ := fun x ↦ ζ (((n : ℝ) + 1)⁻¹ • x) * ũ x) ?_ ?_ ?_ (R := 2 * ((n : ℝ) + 1)) ?_
  · exact (hv n).trans (hu.mono fun x hx ↦ by dsimp only; rw [hx])
  · exact (hζ.continuous.comp (continuous_const.smul continuous_id)).continuousOn.mul hc
  · intro x hx
    simp [h0 hx]
  · intro x hx
    have hζx : ζ (((n : ℝ) + 1)⁻¹ • x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
      have h2 : ‖((n : ℝ) + 1)⁻¹ • x‖ < 2 := by simpa using hζs h
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity),
        inv_mul_lt_iff₀ (by positivity)] at h2
      linarith
    simp [hζx]

end SobolevMultiIndex

/-- **Theorem 9.17, (i) ⇒ (ii)** on an open `Ω ⊆ ℝ^N`, `1 ≤ p < ∞`: if `u ∈ W^{1,p}(Ω)` has a
representative `ũ` continuous on `closure Ω` with `ũ = 0` on `∂Ω`, then `u ∈ W_0^{1,p}(Ω)`. No
smoothness of `Ω` is needed ([brezis2011functional] Theorem 9.17, (i) ⇒ (ii), and Remark 19);
the instance of `SobolevMultiIndex.mem_zero_of_continuousOn_closure_of_eqOn_frontier`. This is
what places a classical solution of the Dirichlet problem in `H^1_0(Ω)` (§9.5, Example 1,
Step A). -/
theorem SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (hp' : p ≠ ⊤) (u : SobolevEuclidean N 1 p Ω)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (h0 : EqOn ũ 0 (frontier Ω)) :
    u ∈ SobolevEuclideanZero N 1 p Ω :=
  SobolevMultiIndex.mem_zero_of_continuousOn_closure_of_eqOn_frontier hp' u hu hc h0

end ContinuousBoundary








/-! ### Proposition 9.20: the dual `W^{-1,p'}(Ω)` -/

section Dual

/-! #### Functionals on a finite `ℓ^p` product -/

namespace PiLp

variable {κ : Type*} [DecidableEq κ] {X : κ → Type*} [∀ i, NormedAddCommGroup (X i)]
  [∀ i, NormedSpace ℝ (X i)] {p : ℝ≥0∞}

variable (p) in
/-- The inclusion of the `i`-th factor into the `ℓ^p` product, as a continuous linear map. -/
def singleCLM (i : κ) : X i →L[ℝ] PiLp p X :=
  (continuousLinearEquiv p ℝ X).symm.toContinuousLinearMap.comp (ContinuousLinearMap.single ℝ X i)

/-- `singleCLM p i b` is `PiLp.single p i b`. -/
theorem singleCLM_apply (i : κ) (b : X i) : singleCLM p i b = single p i b := rfl

variable [Fintype κ] [Fact (1 ≤ p)]

/-- The inclusion of a factor is isometric. -/
theorem norm_singleCLM_apply (i : κ) (b : X i) : ‖singleCLM p i b‖ = ‖b‖ := by
  rw [singleCLM_apply, norm_single]

omit [Fact (1 ≤ p)] in
/-- Every element of the product is the sum of its coordinates. -/
theorem sum_singleCLM_apply (x : PiLp p X) : ∑ i, singleCLM p i (x i) = x := by
  refine (continuousLinearEquiv p ℝ X).injective ?_
  rw [map_sum]
  simp only [singleCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.single_apply]
  exact Finset.univ_sum_single _

omit [Fact (1 ≤ p)] in
/-- A functional on the product is the sum of its restrictions to the factors. -/
theorem strongDual_apply_eq_sum_singleCLM (Φ : StrongDual ℝ (PiLp p X)) (x : PiLp p X) :
    Φ x = ∑ i, Φ.comp (singleCLM p i) (x i) := by
  conv_lhs => rw [← sum_singleCLM_apply x]
  rw [map_sum]
  rfl

/-- The restriction of a functional to a factor has norm at most that of the functional. -/
theorem norm_strongDual_comp_singleCLM_le (Φ : StrongDual ℝ (PiLp p X)) (i : κ) :
    ‖Φ.comp (singleCLM p i)‖ ≤ ‖Φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun b ↦ by
    rw [ContinuousLinearMap.comp_apply]
    exact (Φ.le_opNorm _).trans_eq (by rw [norm_singleCLM_apply])

end PiLp

/-! #### Hahn–Banach along a bounded-below linear map, and the Riesz representation on `(L^p)^κ` -/

/-- **Hahn–Banach along a linear map with bounded inverse**: if `g : V →ₗ W` satisfies
`‖v‖ ≤ C ‖g v‖`, every continuous linear functional `F` on `V` is `Φ ∘ g` for a continuous
linear functional `Φ` on `W` with `‖Φ‖ ≤ C ‖F‖`: `g` is injective, `F ∘ g⁻¹` is a functional of
norm at most `C ‖F‖` on the range of `g`, and `exists_extension_norm_eq` extends it. -/
theorem exists_strongDual_comp_eq_of_norm_le {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (g : V →ₗ[ℝ] W) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ v, ‖v‖ ≤ C * ‖g v‖) (F : StrongDual ℝ V) :
    ∃ Φ : StrongDual ℝ W, (∀ v, Φ (g v) = F v) ∧ ‖Φ‖ ≤ C * ‖F‖ := by
  have hinj : Function.Injective g := by
    intro u v huv
    have h := hg (u - v)
    rw [map_sub, huv, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
  obtain ⟨e, he⟩ : ∃ e : V ≃ₗ[ℝ] LinearMap.range g,
      ∀ v, e v = ⟨g v, LinearMap.mem_range_self _ v⟩ :=
    ⟨LinearEquiv.ofInjective g hinj, fun _ ↦ rfl⟩
  have hbound : ∀ w : LinearMap.range g,
      ‖(F.toLinearMap ∘ₗ e.symm.toLinearMap) w‖ ≤ (C * ‖F‖) * ‖w‖ := by
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe, he]
    change ‖F v‖ ≤ (C * ‖F‖) * ‖g v‖
    calc ‖F v‖ ≤ ‖F‖ * ‖v‖ := F.le_opNorm v
      _ ≤ ‖F‖ * (C * ‖g v‖) := mul_le_mul_of_nonneg_left (hg v) (norm_nonneg _)
      _ = (C * ‖F‖) * ‖g v‖ := by ring
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_extension_norm_eq (LinearMap.range g)
    ((F.toLinearMap ∘ₗ e.symm.toLinearMap).mkContinuous (C * ‖F‖) hbound)
  refine ⟨Φ, fun v ↦ ?_, hΦn.trans_le (LinearMap.mkContinuous_norm_le _
    (mul_nonneg hC (norm_nonneg _)) hbound)⟩
  have h2 : ((F.toLinearMap ∘ₗ e.symm.toLinearMap).mkContinuous (C * ‖F‖) hbound)
      ⟨g v, LinearMap.mem_range_self _ v⟩ = F v := by
    rw [LinearMap.mkContinuous_apply, ← he, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl
  exact (hΦ ⟨g v, LinearMap.mem_range_self _ v⟩).trans h2

/-- **A functional on a finite `ℓ^p` product of copies of `L^p(ν)`, `1 ≤ p < ∞`, is a sum of
integrals against `L^{p'}(ν)` functions of norm at most that of the functional**: restricted to
each factor it is a functional on `L^p(ν)` of no larger norm, which the Riesz representation
theorem (`MeasureTheory.Lp.dualEquiv`, [brezis2011functional] Theorems 4.11 and 4.14)
represents isometrically by a function of `L^{p'}(ν)`. With
`exists_strongDual_comp_eq_of_norm_le` this is the common core of the proofs of
[brezis2011functional] Propositions 8.14 and 9.20. -/
theorem MeasureTheory.Lp.strongDual_piLp_exists_forall_eq_sum_integral {α : Type*}
    [MeasurableSpace α] {ν : Measure α} [SigmaFinite ν] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] [p.HolderConjugate q] (hp : p ≠ ⊤) {κ : Type*} [Fintype κ]
    (Φ : StrongDual ℝ (PiLp p fun _ : κ ↦ Lp ℝ p ν)) :
    ∃ f : κ → Lp ℝ q ν, (∀ x : PiLp p fun _ : κ ↦ Lp ℝ p ν, Φ x = ∑ i, ∫ t, f i t * x i t ∂ν) ∧
      ∀ i, ‖f i‖ ≤ ‖Φ‖ := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Lp ℝ q ν ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p ν),
      ∀ (u : Lp ℝ q ν) (f : Lp ℝ p ν), e u f = ∫ x, u x * f x ∂ν :=
    ⟨Lp.dualEquiv ℝ p q ν hp, fun u f ↦ Lp.dualEquiv_apply hp u f⟩
  refine ⟨fun i ↦ e.symm (Φ.comp (PiLp.singleCLM p (X := fun _ : κ ↦ Lp ℝ p ν) i)),
    fun x ↦ ?_, fun i ↦ ?_⟩
  · rw [PiLp.strongDual_apply_eq_sum_singleCLM Φ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← he, LinearIsometryEquiv.apply_symm_apply]
  · rw [LinearIsometryEquiv.norm_map]
    exact PiLp.norm_strongDual_comp_singleCLM_le Φ i

/-! #### The dual of `W_0^{1,p}(Ω)` -/

namespace SobolevEuclideanZero

variable {N : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Proposition 9.20 (the dual `W^{-1,p'}(Ω)` of `W_0^{1,p}(Ω)`)**: for `1 ≤ p < ∞`, `p'` the
conjugate exponent and `F` a continuous linear functional on `W_0^{1,p}(Ω)`, there are
`f_0, f_1, …, f_N ∈ L^{p'}(Ω)` — indexed by the multi-indices `α` of length at most `1` — with
`F v = ∫_Ω f_0 v + ∑ᵢ ∫_Ω f_i ∂_i v` for all `v ∈ W_0^{1,p}(Ω)` and `‖f_α‖_{p'} ≤ ‖F‖`.

Proof ([brezis2011functional] Proposition 9.20, "adapt the proof of Proposition 8.14"):
`W_0^{1,p}(Ω)` is isometrically a subspace of the `ℓ^p` product of `N + 1` copies of `L^p(Ω)`,
through `v ↦ (∂^α v)_α`, so `F` extends by Hahn–Banach to a functional of the same norm on the
product (`exists_strongDual_comp_eq_of_norm_le`), which the Riesz representation theorem on
each factor represents (`MeasureTheory.Lp.strongDual_piLp_exists_forall_eq_sum_integral`). The
book's norm identity `‖F‖ = max_α ‖f_α‖_{p'}` refers to its norm `∑_α ‖h_α‖_p` on the product;
for the `ℓ^p`-sum norm of `SobolevMultiIndexTuple` the one-sided bound is what is stated. -/
theorem exists_dual_repr [p.HolderConjugate q] (hp : p ≠ ⊤)
    (F : StrongDual ℝ (SobolevEuclideanZero N 1 p Ω)) :
    ∃ f : MultiIndexLE (Fin N) 1 → Lp ℝ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      (∀ v : SobolevEuclideanZero N 1 p Ω,
        F v = ∑ α, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          f α x * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean N 1 p Ω) α x) ∧
        ∀ α, ‖f α‖ ≤ ‖F‖ := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  -- the isometric inclusion of `W_0^{1,p}(Ω)` into the ambient `ℓ^p` product
  obtain ⟨ι, hι⟩ : ∃ ι : SobolevEuclideanZero N 1 p Ω →ₗᵢ[ℝ]
      SobolevMultiIndexTuple ℝ (Fin N) 1 p Ω volume, ∀ v : SobolevEuclideanZero N 1 p Ω,
        ι v = ((v : SobolevEuclidean N 1 p Ω) : SobolevMultiIndexTuple ℝ (Fin N) 1 p Ω volume) :=
    ⟨(SobolevMultiIndex ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).subtypeₗᵢ.comp
      (SobolevEuclideanZero N 1 p Ω).subtypeₗᵢ, fun _ ↦ rfl⟩
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_strongDual_comp_eq_of_norm_le ι.toLinearMap zero_le_one
    (fun v ↦ by rw [one_mul, LinearIsometry.coe_toLinearMap, ι.norm_map]) F
  rw [one_mul] at hΦn
  obtain ⟨f, hf, hfn⟩ := Lp.strongDual_piLp_exists_forall_eq_sum_integral (q := q) hp Φ
  refine ⟨f, fun v ↦ ?_, fun α ↦ (hfn α).trans hΦn⟩
  rw [← hΦ v, hf, LinearIsometry.coe_toLinearMap, hι]
  rfl

variable (N p Ω) in
/-- **The gradient `v ↦ ∇v` on `W_0^{1,p}(Ω)`**, as a linear map into the `ℓ^p` product of `N`
copies of `L^p(Ω)`. -/
noncomputable def gradₗ : SobolevEuclideanZero N 1 p Ω →ₗ[ℝ]
    PiLp p fun _ : Fin N ↦ Lp ℝ p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) where
  toFun v := SobolevMultiIndex.grad (v : SobolevEuclidean N 1 p Ω)
  map_add' _ _ := SobolevMultiIndex.grad_add _ _
  map_smul' _ _ := SobolevMultiIndex.grad_smul _ _

/-- `gradₗ v` is the gradient tuple of `v`. -/
theorem gradₗ_apply (v : SobolevEuclideanZero N 1 p Ω) :
    gradₗ N p Ω v = SobolevMultiIndex.grad (v : SobolevEuclidean N 1 p Ω) :=
  rfl

/-- **Poincaré's inequality on the gradient map**: for `Ω ⊆ B(0, R)` and `1 ≤ p < ∞`,
`‖v‖ ≤ (1 + (2R)^p)^{1/p} ‖∇v‖_p` on `W_0^{1,p}(Ω)` (`SobolevEuclideanZero.norm_le_gradNorm`). -/
theorem norm_le_mul_norm_gradₗ {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hp : p ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    ‖v‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal) * ‖gradₗ (d + 1) p Ω v‖ :=
  norm_le_gradNorm hp hR hΩ v

/-- **Proposition 9.20 on a bounded open set: `f_0 = 0`**. For `Ω ⊆ B(0, R)` in `ℝ^{d+1}`,
`1 ≤ p < ∞`, `p'` the conjugate exponent and `F` a continuous linear functional on
`W_0^{1,p}(Ω)`, there are `f_1, …, f_N ∈ L^{p'}(Ω)` with `F v = ∑ᵢ ∫_Ω f_i ∂_i v` for all `v` and
`‖f_i‖_{p'} ≤ (1 + (2R)^p)^{1/p} ‖F‖`: by Poincaré's inequality
(`SobolevEuclideanZero.norm_le_mul_norm_gradₗ`) the gradient `v ↦ ∇v` is injective on
`W_0^{1,p}(Ω)` with bounded inverse, so `F` extends along it to a functional on the `ℓ^p` product
of `N` copies of `L^p(Ω)` (`exists_strongDual_comp_eq_of_norm_le`), represented by
`MeasureTheory.Lp.strongDual_piLp_exists_forall_eq_sum_integral` ([brezis2011functional]
Proposition 9.20, last sentence, and the proof of Proposition 8.14). -/
theorem exists_dual_repr_of_isBounded {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    [p.HolderConjugate q] (hp : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (F : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    ∃ f : Fin (d + 1) → Lp ℝ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      (∀ v : SobolevEuclideanZero (d + 1) 1 p Ω,
        F v = ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          f i x * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 p Ω)
            (MultiIndexLE.single i) x) ∧
        ∀ i, ‖f i‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal) * ‖F‖ := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_strongDual_comp_eq_of_norm_le (gradₗ (d + 1) p Ω)
    (by positivity) (norm_le_mul_norm_gradₗ hp hR hΩ) F
  obtain ⟨f, hf, hfn⟩ := Lp.strongDual_piLp_exists_forall_eq_sum_integral (q := q) hp Φ
  refine ⟨f, fun v ↦ ?_, fun i ↦ (hfn i).trans hΦn⟩
  rw [← hΦ v, hf]
  simp only [gradₗ_apply, SobolevMultiIndex.grad_apply]

end SobolevEuclideanZero

end Dual


/-! ### The Gelfand triple `H^1_0(Ω) ⊂ L²(Ω) ⊂ H^{-1}(Ω)` -/

section GelfandTriple

open scoped InnerProductSpace

namespace SobolevEuclideanZero

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The `L²(Ω)` inner product of two `L²` functions is the integral of their product. -/
theorem _root_.MeasureTheory.L2.inner_eq_integral_mul
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⟪f, g⟫_ℝ = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * g x := by
  rw [L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])

variable (N Ω) in
/-- **The inclusion `L²(Ω) ⊂ H^{-1}(Ω)`**: `f ↦ (v ↦ ∫_Ω f v)`, the transpose of the inclusion
`H^1_0(Ω) ⊂ L²(Ω)` (`SobolevMultiIndexZero.fnL`) composed with the self-duality of `L²(Ω)`
([brezis2011functional] §9.4, "The Dual Space of `W_0^{1,p}(Ω)`", Notation). -/
def toDualL2 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
    StrongDual ℝ (SobolevEuclideanZero N 1 2 Ω) :=
  ((ContinuousLinearMap.compL ℝ (SobolevEuclideanZero N 1 2 Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ℝ).flip
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)).comp
    (innerSL ℝ)

/-- `toDualL2 N Ω f v = ⟪f, v⟫_{L²(Ω)}`. -/
theorem toDualL2_apply_inner (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 2 Ω) :
    toDualL2 N Ω f v
      = ⟪f, SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume v⟫_ℝ :=
  rfl

/-- `toDualL2 N Ω f v = ∫_Ω f v`. -/
theorem toDualL2_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 2 Ω) :
    toDualL2 N Ω f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      f x * SobolevMultiIndex.fn (v : SobolevEuclidean N 1 2 Ω) x := by
  rw [toDualL2_apply_inner, L2.inner_eq_integral_mul]
  rfl

/-- **`H^1_0(Ω) ⊂ L²(Ω)` has dense range**: its range contains the test functions, which are
dense in `L²(Ω)` (`MeasureTheory.Lp.dense_contDiff_tsupport_subset`). -/
theorem denseRange_fnL :
    DenseRange (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume) := by
  refine (Lp.dense_contDiff_tsupport_subset (F := ℝ) (μ := volume) (p := 2) Ω.isOpen
    ENNReal.ofNat_ne_top).mono ?_
  rintro f ⟨g, hfg, hgc, hgs, hgΩ⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(Ω, ℝ), (φ : EuclideanSpace ℝ (Fin N) → ℝ) = g :=
    ⟨⟨g, hgs, hgc, hgΩ⟩, rfl⟩
  obtain ⟨u, hu, hφu⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  refine ⟨⟨u, SobolevMultiIndexZero.testFunctions_le hu⟩, Lp.ext ?_⟩
  rw [SobolevMultiIndexZero.fnL_apply]
  refine hφu.trans ?_
  rw [hφ]
  exact hfg.symm

/-- **`L²(Ω) ⊂ H^{-1}(Ω)` is injective**: a function of `L²(Ω)` whose integral against every
test function vanishes is zero (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem toDualL2_injective : Function.Injective (toDualL2 N Ω) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf ↦ ?_
  have hΩm := Ω.isOpen.measurableSet
  have hloc : LocallyIntegrableOn (⇑f) Ω (volume : Measure (EuclideanSpace ℝ (Fin N))) :=
    (Lp.memLp f).locallyIntegrableOn one_le_two
  have key := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc
    fun g hgs hgc hgΩ ↦ ?_
  · refine Lp.ext ?_
    filter_upwards [(ae_restrict_iff' hΩm).2 key, Lp.coeFn_zero ℝ 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))] with x hx hx0
    rw [hx, hx0]
    rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(Ω, ℝ), (φ : EuclideanSpace ℝ (Fin N) → ℝ) = g :=
      ⟨⟨g, hgs, hgc, hgΩ⟩, rfl⟩
    obtain ⟨u, hu, hφu⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
      (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
    have h1 := DFunLike.congr_fun hf ⟨u, SobolevMultiIndexZero.testFunctions_le hu⟩
    rw [toDualL2_apply, zero_apply] at h1
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgΩ h), zero_smul], ← h1, ← hφ]
    refine integral_congr_ae (hφu.mono fun x hx ↦ ?_)
    simp only [smul_eq_mul, mul_comm, hx]

/-- **A bounded linear map into the dual of a reflexive space whose range separates the points
has dense range**: a functional on the dual vanishing on the range is, by reflexivity, evaluation
at some `v`, which the range separates from `0` only if `v = 0`; a closed proper subspace would
be separated from a point by a nonzero functional (`Submodule.exists_dual_eq_zero_of_notMem`). -/
theorem _root_.denseRange_of_forall_apply_eq_zero {X L : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedSpace.IsReflexive ℝ X] [NormedAddCommGroup L] [NormedSpace ℝ L]
    (j : L →L[ℝ] StrongDual ℝ X) (h : ∀ v : X, (∀ f, j f v = 0) → v = 0) : DenseRange j := by
  obtain ⟨M, hM⟩ : ∃ M : Submodule ℝ (StrongDual ℝ X),
      M = (LinearMap.range (j : L →ₗ[ℝ] StrongDual ℝ X)).topologicalClosure := ⟨_, rfl⟩
  have hMtop : M = ⊤ := by
    by_contra hne
    obtain ⟨z, hz⟩ : ∃ z, z ∉ M := by
      by_contra h'
      push Not at h'
      exact hne (Submodule.eq_top_iff'.2 h')
    obtain ⟨Λ, -, hΛ0, hΛz⟩ :=
      M.exists_dual_eq_zero_of_notMem (hM ▸ Submodule.isClosed_topologicalClosure _) hz
    obtain ⟨v, rfl⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := ℝ) Λ
    have hv : v = 0 := h v fun f ↦ by
      have := hΛ0 (j f) (hM ▸ Submodule.le_topologicalClosure _ ⟨f, rfl⟩)
      rwa [NormedSpace.dual_def] at this
    apply hΛz
    rw [hv, map_zero]
    rfl
  have hrange : Set.range j = ((LinearMap.range (j : L →ₗ[ℝ] StrongDual ℝ X)) : Set _) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  rw [DenseRange, hrange, Submodule.dense_iff_topologicalClosure_eq_top, ← hM, hMtop]

/-- **`L²(Ω) ⊂ H^{-1}(Ω)` has dense range**: `H^1_0(Ω)` is a Hilbert space, hence reflexive,
and the range separates the points, since `∫_Ω f v = 0` for all `f ∈ L²(Ω)` gives, at `f = v`,
`‖v‖_2 = 0` (`denseRange_of_forall_apply_eq_zero`). -/
theorem denseRange_toDualL2 : DenseRange (toDualL2 N Ω) :=
  denseRange_of_forall_apply_eq_zero _ fun v hv ↦ by
    have h := hv (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume v)
    rw [toDualL2_apply_inner, real_inner_self_eq_norm_sq] at h
    exact SobolevMultiIndexZero.fnL_injective
      ((norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)).trans (map_zero _).symm)

/-- **The Gelfand triple `H^1_0(Ω) ⊂ L²(Ω) ⊂ H^{-1}(Ω)`** ([brezis2011functional] §9.4, "The Dual
Space of `W_0^{1,p}(Ω)`", Notation): the inclusion `H^1_0(Ω) → L²(Ω)`
(`SobolevMultiIndexZero.fnL`) and the inclusion `L²(Ω) → H^{-1}(Ω)`
(`SobolevEuclideanZero.toDualL2`, `f ↦ (v ↦ ∫_Ω f v)`) are both injective with dense range —
"these injections are continuous and dense". -/
theorem gelfandTriple :
    Function.Injective (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        1 2 Ω volume) ∧
      DenseRange (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
        volume) ∧
      Function.Injective (toDualL2 N Ω) ∧ DenseRange (toDualL2 N Ω) :=
  ⟨SobolevMultiIndexZero.fnL_injective, denseRange_fnL, toDualL2_injective, denseRange_toDualL2⟩

end SobolevEuclideanZero

end GelfandTriple
