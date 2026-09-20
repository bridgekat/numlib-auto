/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Cutoff.lean` and `Numlib/Analysis/Sobolev/Calculus.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Lp.PiLpDual
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.Analysis.Sobolev.Calculus
import Numlib.Analysis.Sobolev.Embedding
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
  regularity of `Ω`; `SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_eq` is the Sobolev
  inequality `‖u‖_{p*} ≤ C ‖∇u‖_p` on `W_0^{1,p}(Ω)` of an arbitrary open set (Remark 20, last
  sentence) and `SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_measure_ne_top` Poincaré's
  inequality on an open set of finite measure (**Remark 21**, first clause, for `N ≥ 2`);
* `SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`: **Theorem 9.17,
  (i) ⇒ (ii)**, on any open set: a `W^{1,p}(Ω)` function with a representative continuous on
  `closure Ω` and vanishing on `∂Ω` lies in `W_0^{1,p}(Ω)`. The book's "`u_n → u` by dominated
  convergence" silently needs `∇u = 0` a.e. on `{u = 0}`; here the truncations `G(nu)/n` are
  shown to be Cauchy in `W^{1,p}(Ω)` instead, their gradients converging to
  `{u ≠ 0}.indicator ∇u`, and the limit is identified through the function alone;
  `SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure` is **Theorem 9.17, (ii) ⇒ (i)**
  on a `C^1` chart domain: a `W_0^{1,p}(Ω)` function with a representative continuous on
  `closure Ω` vanishes on `∂Ω`, by local charts from the `Q_+` computation
  `SobolevEuclideanZero.eqOn_unitChartCubeZero_of_continuousOn_closure` (the strip inequality
  `∫_{x_N < ε} |u| ≤ ε ∫_{x_N < ε} |∂_N u|` on `W_0^{1,p}(Q_+)`);
* `SobolevEuclideanZero.abs_integral_fn_smul_fderiv_le` and
  `SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le`: Proposition 9.18,
  (i) ⇒ (ii) and (ii) ⇒ (iii); `SobolevEuclidean.mem_zero_of_indicator_memSobolev_unitChartCubePos`
  is the `Q_+` computation of (iii) ⇒ (i), by one-sided mollifiers, and
  `SobolevEuclideanZero.mem_of_indicator_memSobolev` is **Proposition 9.18, (iii) ⇒ (i)** on a
  `C^1` chart domain, by local charts and a partition of unity;
* `SobolevMultiIndexZero.mem_of_mem_restrict`, `SobolevMultiIndexZero.mul_contDiff_mem` and
  `SobolevMultiIndexZero.compDiffeoL_mem`: the transfer of membership in `W_0^{1,p}` from an open
  subset, under a smooth compactly supported factor, and along a change of variables — the steps
  of the chart reductions of Theorem 9.17 and Proposition 9.18;
* `SobolevEuclideanZero.eq_top` (Remark 17) and
  `SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport` (Remark 18);
  `SobolevEuclideanZero.eq_top_of_compl_singleton`: **Remark 17, the punctured space**,
  `W_0^{1,p}(ℝ^N ∖ {0}) = W^{1,p}(ℝ^N ∖ {0})` for `N ≥ 2` and `1 ≤ p ≤ N` — a point has zero
  capacity, by the averaged cut-offs `pointCutoff` whose gradients tend to `0` in `L^p`
  (`tendsto_eLpNorm_fderiv_pointCutoff`), after the density of bounded functions
  (`SobolevMultiIndex.exists_seq_tendsto_ae_abs_le`) and Lemma 9.5 without compactness at
  infinity (`SobolevMultiIndex.mem_zero_of_ae_eq_zero_of_compl_subset`);
* `SobolevMultiIndexZero.contDiff_comp_mem` and `SobolevEuclideanZero.posPart_mem`: the chain
  rule and the positive part preserve `W_0^{1,p}(Ω)`;
* `SobolevEuclideanZero.exists_dual_repr`: **Proposition 9.20**, every element of the dual
  `W^{-1,p'}(Ω)` is `v ↦ ∫ f_0 v + ∑ ∫ f_i ∂_i v` with `f_α ∈ L^{p'}(Ω)`, `‖f_α‖ ≤ ‖F‖`, and
  `SobolevEuclideanZero.exists_dual_repr_of_isBounded`, its form with `f_0 = 0` on a bounded `Ω`
  (Poincaré's inequality);
* `SobolevEuclideanZero.gelfandTriple`: **the inclusions `H^1_0(Ω) ⊂ L²(Ω) ⊂ H^{-1}(Ω)`** are
  injective with dense range (`SobolevEuclideanZero.toDualL2` is the second one);
  `SobolevEuclideanZero.gelfandTriple_of_forall_ae_eq`: the same for
  `W_0^{1,p}(Ω) ⊂ L²(Ω) ⊂ W^{-1,p'}(Ω)`, `1 < p < ∞`, along any bounded inclusion
  `W_0^{1,p}(Ω) → L²(Ω)` sending each element to its function (`SobolevEuclideanZero.toDualOfL2`
  is the second one) — the inclusion itself is Remark 20's, in
  `Numlib/Analysis/Sobolev/EmbeddingDomain.lean`, which imports this file.

## Design

Predicate-level statements are over a finite-dimensional real normed `E` with an additive Haar
measure `μ` and an arbitrary basis `b`; typed statements are on `SobolevEuclideanZero N 1 p Ω`.
The zero extension is built by the pattern of `Numlib/Analysis/Sobolev/Cutoff.lean`: membership
and the identities at the predicate level, then `MemSobolevMultiIndex.exists_sobolevMultiIndex`
and `SobolevMultiIndex.ext_of_fn_ae_eq`.

## References

[brezis2011functional], §9.4: Theorem 9.17, Proposition 9.18, Remarks 17–21, Proposition 9.20.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal NNReal Pointwise Topology

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

/-! ### Remarks 20 and 21: the Sobolev and Poincaré inequalities on `W_0^{1,p}(Ω)` -/

section Remark20

variable {N : ℕ} {p p' : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

namespace SobolevEuclideanZero

/-- **Remark 20, the Sobolev inequality on `W_0^{1,p}(Ω)` for an arbitrary open `Ω`**, in the
form of Theorem 9.9: for `1 ≤ p < N`, `1/p* = 1/p − 1/N` and `u ∈ W_0^{1,p}(Ω)`,
`‖u‖_{L^{p*}(Ω)} ≤ C(p, N) ∑_i ‖∂_i u‖_{L^p(Ω)}`, with Mathlib's constant
`SobolevEuclidean.gnsConst`. Theorem 9.9 (`SobolevEuclidean.eLpNorm_fn_le_of_eq`) applied to the
extension by zero `SobolevEuclideanZero.extendZeroL u ∈ W^{1,p}(ℝ^N)`, whose partial derivatives
have the `L^p` norms of those of `u` ([brezis2011functional] Chapter 9, Remark 20, "it can also
be deduced from Theorem 9.9 that …"). -/
theorem eLpNorm_fn_le_sum_of_eq (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclideanZero N 1 p Ω) :
    eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) (p' : ℝ≥0∞)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ SobolevEuclidean.gnsConst N p
        * ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
          (MultiIndexLE.single i)‖ := by
  have h := SobolevEuclidean.eLpNorm_fn_le_of_eq hpN hp' (extendZeroL N p Ω u)
  rw [eLpNorm_congr_ae (fn_extendZeroL u),
    eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet] at h
  simp only [extendZeroL_apply, norm_weakDeriv_extendZero] at h
  exact h

/-- **Remark 20, the Sobolev inequality on `W_0^{1,p}(Ω)` for an arbitrary open `Ω`**: for
`1 ≤ p < N`, `1/p* = 1/p − 1/N` and `u ∈ W_0^{1,p}(Ω)`,
`‖u‖_{L^{p*}(Ω)} ≤ C(p, N) ‖∇u‖_{L^p(Ω)}` with `C(p, N) = N · SobolevEuclidean.gnsConst N p`
([brezis2011functional] Chapter 9, Remark 20): no regularity of `Ω` is needed, the extension by
zero being an extension operator on `W_0^{1,p}(Ω)`. The sum form is
`SobolevEuclideanZero.eLpNorm_fn_le_sum_of_eq`. -/
theorem eLpNorm_fn_le_gradNorm_of_eq (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclideanZero N 1 p Ω) :
    eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) (p' : ℝ≥0∞)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N
          * gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
  refine (eLpNorm_fn_le_sum_of_eq hpN hp' u).trans ?_
  have hsum : ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
      ≤ N * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
    calc ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
        ≤ ∑ _i : Fin N, ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) :=
          Finset.sum_le_sum fun i _ ↦
            ENNReal.ofReal_le_ofReal (norm_weakDeriv_single_le_gradNorm _ i)
      _ = N * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc SobolevEuclidean.gnsConst N p
        * ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
      ≤ SobolevEuclidean.gnsConst N p
          * (N * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω))) :=
        mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N
          * gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal, mul_assoc]

/-- **`W_0^{1,p}(Ω) ⊆ L^{p*}(Ω)`** for `1 ≤ p < N` and an arbitrary open `Ω`
([brezis2011functional] Chapter 9, Remark 20); the general `L^q` memberships are
`SobolevEuclideanZero.memLp_fn_of_le` / `memLp_fn_of_lt` / `memLp_fn_of_eq` in
`EmbeddingDomain.lean`. -/
theorem memLp_fn_sobolevConj (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclideanZero N 1 p Ω) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) (p' : ℝ≥0∞)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  memLp_iff.2 ((eLpNorm_fn_le_gradNorm_of_eq hpN hp' u).trans_lt ENNReal.ofReal_lt_top)

end SobolevEuclideanZero

end Remark20

section Remark21

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

namespace SobolevEuclideanZero

/-- The tensor weak gradient of the extension by zero of `u ∈ W_0^{1,p}(Ω)` may be taken to vanish
outside `Ω`: it is `Ω.indicator w` for the tensor gradient `w` of `ū`, which vanishes almost
everywhere off `Ω` because its values on the basis vectors are the zero extensions of the partial
derivatives of `u`. -/
theorem exists_hasWeakFDerivOn_indicator (u : SobolevEuclideanZero N 1 p Ω) :
    ∃ w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
      HasWeakFDerivOn ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (fn (u : SobolevEuclidean N 1 p Ω))) w ⊤ volume ∧
      (∀ x, x ∉ (Ω : Set (EuclideanSpace ℝ (Fin N))) → w x = 0) ∧
      MemLp w p volume ∧
      eLpNorm w p volume ≤ ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
        (MultiIndexLE.single i)‖ := by
  classical
  have hΩm := Ω.isOpen.measurableSet
  obtain ⟨w, hw, hwp, hwi, -⟩ := exists_hasWeakFDerivOn_fn (extendZeroL N p Ω u)
  simp only [Opens.coe_top, Measure.restrict_univ] at hwp hwi
  -- `w` vanishes almost everywhere off `Ω`
  have hzero : ∀ᵐ x ∂volume, x ∉ (Ω : Set (EuclideanSpace ℝ (Fin N))) → w x = 0 := by
    have hall : ∀ᵐ x ∂volume, ∀ i, w x ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis i)
        = (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
          (weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)) x :=
      ae_all_iff.2 fun i ↦ (hwi i).trans (weakDeriv_extendZeroL_single u i)
    filter_upwards [hall] with x hx hxΩ
    refine ContinuousLinearMap.ext fun ξ ↦ ?_
    rw [← (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.sum_repr ξ, map_sum]
    simp only [map_smul, hx, Set.indicator_of_notMem hxΩ, smul_zero, Finset.sum_const_zero,
      zero_apply]
  have hae : w =ᵐ[volume] (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator w := by
    filter_upwards [hzero] with x hx
    by_cases hxΩ : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
    · rw [Set.indicator_of_mem hxΩ]
    · rw [Set.indicator_of_notMem hxΩ, hx hxΩ]
  refine ⟨(Ω : Set (EuclideanSpace ℝ (Fin N))).indicator w, ?_,
    fun x hx ↦ Set.indicator_of_notMem hx _, hwp.ae_eq hae, ?_⟩
  · unfold HasWeakFDerivOn
    refine HasWeakIteratedFDerivOn.congr_ae hw ?_ ?_
    · simpa only [Opens.coe_top, Measure.restrict_univ] using fn_extendZeroL u
    · simp only [Opens.coe_top, Measure.restrict_univ]
      filter_upwards [hae] with x hx
      rw [hx]
  · rw [← eLpNorm_congr_ae hae]
    exact (SobolevEuclidean.eLpNorm_le_sum_of_hasWeakFDerivOn (extendZeroL N p Ω u) hw).trans
      (le_of_eq (Finset.sum_congr rfl fun i _ ↦ by
        rw [extendZeroL_apply, norm_weakDeriv_extendZero]))

/-- The exponent bookkeeping of Remark 21: for `0 < a ≤ 1` and `0 < b < 1` there is `c` with
`a ≤ c ≤ a + b` and `b < c ≤ 1`. -/
theorem exists_exponent_aux {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b < 1) :
    ∃ c : ℝ, a ≤ c ∧ c ≤ a + b ∧ b < c ∧ c ≤ 1 :=
  ⟨min 1 (max a (b + a / 2)), le_min ha1 (le_max_left _ _),
    (min_le_right _ _).trans (max_le (by linarith) (by linarith)),
    lt_min hb1 ((lt_max_of_lt_right (by linarith))), min_le_left _ _⟩

/-- **Remark 21, first clause: Poincaré's inequality on an open set of finite measure**, sum
form: for `N ≥ 2`, `1 ≤ p < ∞` and `Ω` of finite measure there is `C < ∞` with
`‖u‖_{L^p(Ω)} ≤ C ∑_i ‖∂_i u‖_{L^p(Ω)}` for every `u ∈ W_0^{1,p}(Ω)`.

Proof: choose an exponent `1 ≤ q ≤ p` with `q < N` and `p ≤ q*` (`1/q* = 1/q − 1/N`), which is
possible for `N ≥ 2`. On the finite-measure `Ω`, `L^p(Ω) ⊆ L^q(Ω)`, so the extension by zero `ū`
and its (tensor) weak gradient `w`, which vanishes off `Ω`, lie in `L^q(ℝ^N)`, and Theorem 9.9
(`HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq`) at the exponent `q` gives
`‖u‖_{q*} ≤ C ‖w‖_q`; Hölder's inequality `‖u‖_p ≤ |Ω|^{1/p − 1/q*} ‖u‖_{q*}` and
`‖w‖_q ≤ |Ω|^{1/q − 1/p} ‖w‖_p ≤ |Ω|^{1/q − 1/p} ∑_i ‖∂_i u‖_p` finish
([brezis2011functional] Chapter 9, Remark 21, "Poincaré's inequality remains true if `Ω` has
finite measure"). For `N = 1` the statement is false on unbounded sets of finite measure
(`notes/book-errata.md`). -/
theorem exists_eLpNorm_fn_le_sum_of_measure_ne_top (hp' : p ≠ ⊤) (hN : 2 ≤ N)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : SobolevEuclideanZero N 1 p Ω,
      eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) p (volume.restrict (Ω : Set _))
        ≤ C * ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
          (MultiIndexLE.single i)‖ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hΩm := Ω.isOpen.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    isFiniteMeasure_restrict.2 hΩ
  have hP1 : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hP0 : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (zero_lt_two.trans_le hN)
  have hN1 : (N : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact_mod_cast (one_lt_two.trans_le hN)
  obtain ⟨c, hac, hcab, hbc, hc1⟩ := exists_exponent_aux (inv_pos.2 hP0) (inv_le_one_of_one_le₀ hP1)
    (inv_pos.2 hN0) hN1
  have hc0 : 0 < c := (inv_pos.2 hN0).trans hbc
  have hcb0 : 0 < c - (N : ℝ)⁻¹ := sub_pos.2 hbc
  -- the exponents `q = 1/c` and `q* = 1/(c - 1/N)`
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = c⁻¹ :=
    ⟨Real.toNNReal c⁻¹, Real.coe_toNNReal _ (inv_pos.2 hc0).le⟩
  obtain ⟨q', hq'⟩ : ∃ q' : ℝ≥0, (q' : ℝ) = (c - (N : ℝ)⁻¹)⁻¹ :=
    ⟨Real.toNNReal _, Real.coe_toNNReal _ (inv_pos.2 hcb0).le⟩
  have hq1 : 1 ≤ q := by
    rw [← NNReal.coe_le_coe, hq, NNReal.coe_one]
    exact one_le_inv₀ hc0 |>.2 hc1
  have hqN : q < N := by
    rw [← NNReal.coe_lt_coe, hq, NNReal.coe_natCast]
    rw [inv_lt_comm₀ hc0 hN0]
    exact hbc
  have hqq' : (q' : ℝ)⁻¹ = q⁻¹ - (N : ℝ)⁻¹ := by
    rw [hq', NNReal.coe_inv, hq, inv_inv, inv_inv]
  have hqp : (q : ℝ≥0∞) ≤ p := by
    rw [← ENNReal.ofReal_toReal hp', ← ENNReal.ofReal_coe_nnreal, hq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_le_comm₀ hc0 hP0]
    exact hac
  have hpq' : p ≤ (q' : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hp', ← ENNReal.ofReal_coe_nnreal, hq']
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_inv_comm₀ hP0 hcb0]
    linarith
  have hqtop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hq'top : (q' : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  -- the two powers of the measure of `Ω`
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
    ^ (1 / p.toReal - 1 / (q' : ℝ≥0∞).toReal) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
    ^ (1 / (q : ℝ≥0∞).toReal - 1 / p.toReal) := ⟨_, rfl⟩
  have hA' : A ≠ ⊤ := by
    rw [hA]
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hΩ
    rw [ENNReal.coe_toReal, hq', one_div, one_div, inv_inv, sub_nonneg]
    linarith
  have hB' : B ≠ ⊤ := by
    rw [hB]
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hΩ
    rw [ENNReal.coe_toReal, hq, one_div, one_div, inv_inv, sub_nonneg]
    exact hac
  refine ⟨SobolevEuclidean.gnsConst N q * B * A,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hB') hA', fun u ↦ ?_⟩
  obtain ⟨w, hw, hw0, hwp, hwle⟩ := exists_hasWeakFDerivOn_indicator u
  have hwae : w =ᵐ[volume] (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator w :=
    Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hw0 x hx]
  have hum : AEStronglyMeasurable (fn (u : SobolevEuclidean N 1 p Ω))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := (memLp _).aestronglyMeasurable
  -- memberships at the exponent `q`
  have hūq : MemLp ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
      (fn (u : SobolevEuclidean N 1 p Ω))) q volume :=
    (memLp_indicator_iff_restrict hΩm).2 ((memLp _).mono_exponent hqp)
  have hwq : MemLp w q volume := by
    refine ((memLp_indicator_iff_restrict hΩm).2 ?_).ae_eq hwae.symm
    exact (hwp.restrict _).mono_exponent hqp
  -- Theorem 9.9 at the exponent `q`
  have hN' : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  have hGNS := hw.eLpNorm_le_eLpNorm_weakFDeriv_of_eq hq1 (by rw [hN']; exact_mod_cast hqN)
    (by rw [hN']; exact hqq') hūq hwq
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hΩm] at hGNS
  -- the two Hölder steps on the finite-measure set `Ω`
  have hH1 : eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) p (volume.restrict (Ω : Set _))
      ≤ eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) (q' : ℝ≥0∞) (volume.restrict (Ω : Set _))
        * A := by
    rw [hA, ← Measure.restrict_apply_univ (μ := volume) (Ω : Set (EuclideanSpace ℝ (Fin N)))]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq' hum
  have hH2 : eLpNorm w (q : ℝ≥0∞) volume
      ≤ eLpNorm w p volume * B := by
    have e1 : eLpNorm w (q : ℝ≥0∞) volume
        = eLpNorm w q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      rw [eLpNorm_congr_ae hwae, eLpNorm_indicator_eq_eLpNorm_restrict hΩm]
    have e2 : eLpNorm w p volume
        = eLpNorm w p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      rw [eLpNorm_congr_ae hwae, eLpNorm_indicator_eq_eLpNorm_restrict hΩm]
    rw [e1, e2, hB,
      ← Measure.restrict_apply_univ (μ := volume) (Ω : Set (EuclideanSpace ℝ (Fin N)))]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp (hwp.restrict _).aestronglyMeasurable
  calc eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) p (volume.restrict (Ω : Set _))
      ≤ eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) (q' : ℝ≥0∞) (volume.restrict (Ω : Set _)) * A :=
        hH1
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ volume q * eLpNorm w (q : ℝ≥0∞) volume) * A :=
        mul_le_mul' hGNS le_rfl
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ volume q * (eLpNorm w p volume * B)) * A :=
        mul_le_mul' (mul_le_mul' le_rfl hH2) le_rfl
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ volume q
          * ((∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
            (MultiIndexLE.single i)‖) * B)) * A :=
        mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul' hwle le_rfl)) le_rfl
    _ = SobolevEuclidean.gnsConst N q * B * A
          * ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
            (MultiIndexLE.single i)‖ := by
        rw [SobolevEuclidean.gnsConst]; ring

/-- **Remark 21, first clause: Poincaré's inequality on an open set of finite measure**: for
`N ≥ 2`, `1 ≤ p < ∞` and an open `Ω ⊆ ℝ^N` of finite measure there is `C < ∞` with
`‖u‖_{L^p(Ω)} ≤ C ‖∇u‖_{L^p(Ω)}` for every `u ∈ W_0^{1,p}(Ω)`
([brezis2011functional] Chapter 9, Remark 21; the bounded-projection clause is
`SobolevEuclideanZero.eLpNorm_fn_le_of_subset_slab` of `Numlib/Analysis/Sobolev/Poincare.lean`).
The sum form is `SobolevEuclideanZero.exists_eLpNorm_fn_le_sum_of_measure_ne_top`; for `N = 1`
the statement is false on unbounded sets of finite measure. -/
theorem eLpNorm_fn_le_gradNorm_of_measure_ne_top (hp' : p ≠ ⊤) (hN : 2 ≤ N)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : SobolevEuclideanZero N 1 p Ω,
      eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) p (volume.restrict (Ω : Set _))
        ≤ C * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
  obtain ⟨C, hC, h⟩ := exists_eLpNorm_fn_le_sum_of_measure_ne_top (Ω := Ω) hp' hN hΩ
  refine ⟨C * N, ENNReal.mul_ne_top hC (ENNReal.natCast_ne_top N), fun u ↦ ?_⟩
  refine (h u).trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  calc ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
      ≤ ∑ _i : Fin N, ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) :=
        Finset.sum_le_sum fun i _ ↦
          ENNReal.ofReal_le_ofReal (norm_weakDeriv_single_le_gradNorm _ i)
    _ = N * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end SobolevEuclideanZero

end Remark21

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








/-! ### Transfer of membership in `W_0^{1,p}`: open subsets and changes of variables -/

section Transfer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω Ω' : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndex

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ p)]
  [μ.IsAddHaarMeasure] in
/-- The `L^p(Ω)` norm of `g − f` reduces to the `L^p(Ω')` norm, `Ω' ⊆ Ω`, when `g` vanishes off
`Ω'` and `f` vanishes almost everywhere on `Ω ∖ Ω'`. -/
theorem _root_.MeasureTheory.eLpNorm_sub_restrict_eq_of_eq_zero_compl {g f : E → F} (h : Ω' ≤ Ω)
    (hg : ∀ x ∉ (Ω' : Set E), g x = 0)
    (hf : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ (Ω' : Set E) → f x = 0) :
    eLpNorm (g - f) p (μ.restrict (Ω : Set E)) = eLpNorm (g - f) p (μ.restrict (Ω' : Set E)) := by
  have e : (g - f) =ᵐ[μ.restrict (Ω : Set E)] (Ω' : Set E).indicator (g - f) := by
    filter_upwards [hf] with x hx
    by_cases hxΩ' : x ∈ (Ω' : Set E)
    · rw [Set.indicator_of_mem hxΩ']
    · rw [Set.indicator_of_notMem hxΩ', Pi.sub_apply, hg x hxΩ', hx hxΩ', sub_zero]
  rw [eLpNorm_congr_ae e, eLpNorm_indicator_eq_eLpNorm_restrict Ω'.isOpen.measurableSet,
    Measure.restrict_restrict Ω'.isOpen.measurableSet, inter_eq_left.2 h]

omit [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- **The weak derivatives of `u ∈ W^{k,p}(Ω)` vanish almost everywhere on an open subset of `Ω`
where `u` does**: on such an open `V`, `0` is a weak derivative of `fn u =ᵐ 0`, and the weak
derivative is unique. -/
theorem weakDeriv_ae_eq_zero_of_fn_ae_eq_zero {k : ℕ} (u : SobolevMultiIndex F b k p Ω μ)
    {V : Opens E} (hV : V ≤ Ω) (hu : fn u =ᵐ[μ.restrict (V : Set E)] 0) (α : MultiIndexLE ι k) :
    (weakDeriv u α : E → F) =ᵐ[μ.restrict (V : Set E)] 0 := by
  have h1 := ((hasWeakIteratedLineDerivOn u α).mono hV).congr_ae hu (EventuallyEq.refl _ _)
  have h2 : HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) (0 : E → F) 0 V μ :=
    HasWeakIteratedLineDerivOn.zero
  exact (ae_restrict_iff' V.isOpen.measurableSet).2 (h1.ae_eq h2)

omit [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- The weak derivatives of `u ∈ W^{k,p}(Ω)` vanish almost everywhere off a closed set `K`
outside of which `u` vanishes almost everywhere. -/
theorem weakDeriv_ae_eq_zero_of_fn_ae_eq_zero_compl {k : ℕ} (u : SobolevMultiIndex F b k p Ω μ)
    {K : Set E} (hK : IsClosed K) (hu : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ K → fn u x = 0)
    (α : MultiIndexLE ι k) :
    ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ K → weakDeriv u α x = 0 := by
  obtain ⟨V, hVdef⟩ : ∃ V : Opens E, V = ⟨(Ω : Set E) ∩ Kᶜ, Ω.isOpen.inter hK.isOpen_compl⟩ :=
    ⟨_, rfl⟩
  have hVs : (V : Set E) = (Ω : Set E) ∩ Kᶜ := by rw [hVdef]; rfl
  have hVΩ : V ≤ Ω := by rw [← SetLike.coe_subset_coe, hVs]; exact inter_subset_left
  have hu' : fn u =ᵐ[μ.restrict (V : Set E)] 0 := by
    rw [hVs, inter_comm, ← Measure.restrict_restrict hK.isOpen_compl.measurableSet]
    refine (ae_restrict_iff' hK.isOpen_compl.measurableSet).2 ?_
    filter_upwards [hu] with x hx hxK
    simpa using hx hxK
  have h := weakDeriv_ae_eq_zero_of_fn_ae_eq_zero u hVΩ hu' α
  rw [hVs, inter_comm, ← Measure.restrict_restrict hK.isOpen_compl.measurableSet] at h
  filter_upwards [(ae_restrict_iff' hK.isOpen_compl.measurableSet).1 h] with x hx hxK
  simpa using hx hxK

end SobolevMultiIndex

namespace SobolevMultiIndexZero

open SobolevMultiIndex

/-- **Transfer of membership in `W_0^{1,p}` from an open subset**: if `Ω' ⊆ Ω`, the restriction
of `u ∈ W^{1,p}(Ω)` to `Ω'` lies in `W_0^{1,p}(Ω')`, and `u` vanishes almost everywhere on `Ω`
outside a closed set `K` with `K ∩ Ω ⊆ Ω'`, then `u ∈ W_0^{1,p}(Ω)`. Test functions on `Ω'`
converging to `u|_{Ω'}` are test functions on `Ω`, and they converge to `u` in `W^{1,p}(Ω)`
because every component of the difference vanishes almost everywhere on `Ω ∖ Ω'` — the weak
derivatives of `u` vanish there by uniqueness of the weak derivative on the open set `Ω ∖ K`
(`SobolevMultiIndex.weakDeriv_ae_eq_zero_of_fn_ae_eq_zero_compl`). This is the step "extend by
zero to `Ω`" of the chart reductions of [brezis2011functional] Theorem 9.17 and Proposition
9.18. -/
theorem mem_of_mem_restrict (h : Ω' ≤ Ω) {u : SobolevMultiIndex F b 1 p Ω μ}
    (hu : restrictL F b 1 p μ h u ∈ SobolevMultiIndexZero F b 1 p Ω' μ) {K : Set E}
    (hK : IsClosed K) (hKΩ : K ∩ Ω ⊆ Ω')
    (hu0 : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ K → fn u x = 0) :
    u ∈ SobolevMultiIndexZero F b 1 p Ω μ := by
  obtain ⟨w, φ, hφ, hw⟩ := exists_seq_testFunction_tendsto hu
  -- the test functions on `Ω'`, read as test functions on `Ω`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → 𝓓(Ω, F), ∀ n, (ψ n : E → F) = φ n :=
    ⟨fun n ↦ ⟨φ n, (φ n).contDiff, (φ n).hasCompactSupport, (φ n).tsupport_subset.trans h⟩,
      fun _ ↦ rfl⟩
  choose W hWT hW using fun n ↦ (ψ n).exists_mem_sobolevMultiIndex_testFunctions (b := b) (k := 1)
    (p := p) (μ := μ)
  -- `u` and its derivatives vanish almost everywhere on `Ω ∖ Ω'`
  have hu0' : ∀ α : MultiIndexLE ι 1, ∀ᵐ x ∂μ.restrict (Ω : Set E),
      x ∉ (Ω' : Set E) → weakDeriv u α x = 0 := fun α ↦ by
    filter_upwards [weakDeriv_ae_eq_zero_of_fn_ae_eq_zero_compl u hK hu0 α, ae_restrict_mem
      Ω.isOpen.measurableSet] with x hx hxΩ hxΩ'
    exact hx fun hxK ↦ hxΩ' (hKΩ ⟨hxK, hxΩ⟩)
  refine isClosed.mem_of_tendsto (f := W) (b := atTop) ?_
    (Eventually.of_forall fun n ↦ testFunctions_le (hWT n))
  refine tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun α ↦ ?_
  -- the classical function `c n` carrying the component `α` of `W n` and of `w n`
  have hc : ∀ n, ∃ c : E → F, (∀ x ∉ (Ω' : Set E), c x = 0) ∧
      (weakDeriv (W n) α : E → F) =ᵐ[μ.restrict (Ω : Set E)] c ∧
      (weakDeriv (w n) α : E → F) =ᵐ[μ.restrict (Ω' : Set E)] c := by
    intro n
    rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
    · refine ⟨φ n, fun x hx ↦ (φ n).eq_zero_of_notMem hx, ?_, hφ n⟩
      rw [weakDeriv_zero, ← hψ n]
      exact hW n
    · refine ⟨fun x ↦ fderiv ℝ (φ n) x (b i), fun x hx ↦ ?_, ?_, ?_⟩
      · dsimp only
        rw [← (φ n).fderivApply_apply (b i) x]
        exact ((φ n).fderivApply (b i)).eq_zero_of_notMem hx
      · have := weakDeriv_single_ae_eq_testFunction (hW n) i
        rwa [hψ n] at this
      · exact weakDeriv_single_ae_eq_testFunction (hφ n) i
  choose c hc0 hcW hcw using hc
  have key : ∀ n, eLpNorm ((weakDeriv (W n) α : E → F) - (weakDeriv u α : E → F)) p
        (μ.restrict (Ω : Set E))
      = eLpNorm ((weakDeriv (w n) α : E → F) - (weakDeriv (restrictL F b 1 p μ h u) α : E → F)) p
        (μ.restrict (Ω' : Set E)) := by
    intro n
    rw [eLpNorm_congr_ae ((hcW n).sub (EventuallyEq.refl _ _)),
      eLpNorm_sub_restrict_eq_of_eq_zero_compl h (hc0 n) (hu0' α)]
    exact eLpNorm_congr_ae ((hcw n).symm.sub (weakDeriv_restrictL h u α).symm)
  simp_rw [key]
  exact tendsto_eLpNorm_weakDeriv_sub hw α

/-- **Change of variables preserves `W_0^{1,p}`**: for a `C^1` diffeomorphism `H : Ω' → Ω` with
bounded Jacobians and `u ∈ W_0^{1,p}(Ω)`, `1 ≤ p < ∞`, the transfer `u ∘ H` lies in
`W_0^{1,p}(Ω')`. The test functions `φ_n → u` transfer to `φ_n ∘ H`, which vanish on `Ω'` outside
the compact `H⁻¹(supp φ_n)`, hence lie in `W_0^{1,p}(Ω')` by Lemma 9.5
(`SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact`), and `compDiffeoL` is continuous.
This is the "transfer along the chart" step of the chart reductions of [brezis2011functional]
Theorem 9.17 and Proposition 9.18. -/
theorem compDiffeoL_mem (hp' : p ≠ ⊤) {H Hinv : E → E} {M : ℝ}
    (hH : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) {u : SobolevMultiIndex F b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero F b 1 p Ω μ) :
    compDiffeoL F b p μ hH u ∈ SobolevMultiIndexZero F b 1 p Ω' μ := by
  obtain ⟨w, φ, hφ, hw⟩ := exists_seq_testFunction_tendsto hu
  have ht : Tendsto (fun n ↦ compDiffeoL F b p μ hH (w n)) atTop
      (𝓝 (compDiffeoL F b p μ hH u)) :=
    ((compDiffeoL F b p μ hH).continuous.tendsto u).comp hw
  refine isClosed.mem_of_tendsto ht (Eventually.of_forall fun n ↦ ?_)
  have hmaps : MapsTo Hinv Ω Ω' := hH.invOn.1.mapsTo hH.bijOn.surjOn
  have hK : IsCompact (Hinv '' tsupport (φ n)) :=
    (φ n).hasCompactSupport.image_of_continuousOn
      (hH.contDiffOn_invFun.continuousOn.mono (φ n).tsupport_subset)
  have hKΩ' : Hinv '' tsupport (φ n) ⊆ Ω' :=
    (image_mono (φ n).tsupport_subset).trans hmaps.image_subset
  refine mem_zero_of_ae_eq_zero_compl_isCompact hp' _ hK hKΩ' ?_
  filter_upwards [fn_compDiffeoL hH (w n), ae_restrict_mem Ω'.isOpen.measurableSet,
    hH.ae_comp_restrict (P := fun x ↦ fn (w n) x = φ n x) (hφ n)] with y hy hyΩ' hyφ hyK
  rw [hy, hyφ]
  by_contra hne
  apply hyK
  refine ⟨H y, subset_tsupport _ hne, hH.invOn.1 hyΩ'⟩

end SobolevMultiIndexZero

end Transfer

/-! ### A smooth compactly supported factor preserves `W_0^{1,p}` -/

section LpAux

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- `L^p` convergence to `0` is preserved by a bounded factor: `‖f_n a‖_p ≤ M ‖f_n‖_p`. -/
theorem MeasureTheory.tendsto_eLpNorm_mul_of_tendsto {f : ℕ → X → ℝ} {a : X → ℝ}
    (ha : AEStronglyMeasurable a ν) {M : ℝ} (hM : ∀ x, |a x| ≤ M)
    (hfm : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf : Tendsto (fun n ↦ eLpNorm (f n) p ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ f n x * a x) p ν) atTop (𝓝 0) := by
  have hbd : ∀ n, eLpNorm (fun x ↦ f n x * a x) p ν ≤ ENNReal.ofReal M * eLpNorm (f n) p ν := by
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := fun x ↦ f n x * a x) (g := f n) (c := M)
      ((hfm n).mul ha) (Eventually.of_forall fun x ↦ ?_) p
    change ‖f n x * a x‖ ≤ M * ‖f n x‖
    rw [norm_mul, mul_comm, Real.norm_eq_abs (a x)]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
  simpa using ENNReal.Tendsto.const_mul hf (Or.inr ENNReal.ofReal_ne_top)

/-- `L^p` convergence to `0` of `f_n a + g_n c` for bounded factors `a`, `c`. -/
theorem MeasureTheory.tendsto_eLpNorm_mul_add_mul_of_tendsto {f g : ℕ → X → ℝ}
    {a c : X → ℝ} (ha : AEStronglyMeasurable a ν) (hc : AEStronglyMeasurable c ν) {M : ℝ}
    (hMa : ∀ x, |a x| ≤ M) (hMc : ∀ x, |c x| ≤ M) (hfm : ∀ n, AEStronglyMeasurable (f n) ν)
    (hgm : ∀ n, AEStronglyMeasurable (g n) ν)
    (hf : Tendsto (fun n ↦ eLpNorm (f n) p ν) atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ eLpNorm (g n) p ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ f n x * a x + g n x * c x) p ν) atTop (𝓝 0) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hbd : ∀ n, eLpNorm (fun x ↦ f n x * a x + g n x * c x) p ν
      ≤ eLpNorm (fun x ↦ f n x * a x) p ν + eLpNorm (fun x ↦ g n x * c x) p ν := fun n ↦
    eLpNorm_add_le (f := fun x ↦ f n x * a x) (g := fun x ↦ g n x * c x) hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
  simpa using (tendsto_eLpNorm_mul_of_tendsto ha hMa hfm hf).add
    (tendsto_eLpNorm_mul_of_tendsto hc hMc hgm hg)

end LpAux

section SmulContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω Ω' : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

open SobolevMultiIndex

omit [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- **The Leibniz rule for a smooth factor on `W^{1,p}(Ω)`**: if `v ∈ W^{1,p}(Ω)` has function
`u α` for `u ∈ W^{1,p}(Ω)` and `α` smooth, then `∂_i v = (∂_i u) α + u ∂_i α` almost everywhere
on `Ω` — the weak derivative `HasWeakIteratedLineDerivOn.mul_contDiff` provides, by uniqueness. -/
theorem SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_mul_contDiff {α : E → ℝ}
    (hα : ContDiff ℝ ∞ α) {u v : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hv : fn v =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ fn u x * α x) (i : ι) :
    (weakDeriv v (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ weakDeriv u (MultiIndexLE.single i) x * α x + fn u x * fderiv ℝ α x (b i) := by
  have h1 : HasWeakIteratedLineDerivOn ![b i] (fn v) (weakDeriv v (MultiIndexLE.single i)) Ω μ :=
    (hasWeakIteratedLineDerivOn v (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 := ((hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).mul_contDiff rfl hα
  have h3 : HasWeakIteratedLineDerivOn ![b i] (fn v)
      (fun x ↦ weakDeriv u (MultiIndexLE.single i) x * α x + fn u x * fderiv ℝ α x (b i)) Ω μ := by
    refine h2.congr_ae hv.symm (Eventually.of_forall fun x ↦ ?_)
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h3)

omit [FiniteDimensional ℝ E] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- The functions, in the proof of `SobolevMultiIndexZero.mul_contDiff_mem`:
`z_n − v = (w_n − u) α` almost everywhere on `Ω'`. -/
theorem SobolevMultiIndexZero.fn_sub_ae_eq_mul_aux (h : Ω' ≤ Ω) {α : E → ℝ}
    {u w : SobolevMultiIndex ℝ b 1 p Ω μ} {v z : SobolevMultiIndex ℝ b 1 p Ω' μ} {φ : 𝓓(Ω, ℝ)}
    {ψ : 𝓓(Ω', ℝ)} (hφ : fn w =ᵐ[μ.restrict (Ω : Set E)] φ)
    (hψ : (ψ : E → ℝ) = fun x ↦ φ x * α x) (hz : fn z =ᵐ[μ.restrict (Ω' : Set E)] ψ)
    (hv : fn v =ᵐ[μ.restrict (Ω' : Set E)] fun x ↦ fn u x * α x) :
    (weakDeriv z 0 : E → ℝ) - (weakDeriv v 0 : E → ℝ) =ᵐ[μ.restrict (Ω' : Set E)]
      fun x ↦ (fn w x - fn u x) * α x := by
  have hle : μ.restrict (Ω' : Set E) ≤ μ.restrict (Ω : Set E) := Measure.restrict_mono h le_rfl
  filter_upwards [hz, hv, hφ.filter_mono (ae_mono hle)] with x h1 h2 h3
  rw [hψ] at h1
  simp only [Pi.sub_apply, weakDeriv_zero, h1, h2, h3]
  ring

/-- The derivatives, in the proof of `SobolevMultiIndexZero.mul_contDiff_mem`:
`∂_i z_n − ∂_i v = (∂_i w_n − ∂_i u) α + (w_n − u) ∂_i α` almost everywhere on `Ω'`. -/
theorem SobolevMultiIndexZero.weakDeriv_single_sub_ae_eq_mul_aux (h : Ω' ≤ Ω) {α : E → ℝ}
    (hα : ContDiff ℝ ∞ α) {u w : SobolevMultiIndex ℝ b 1 p Ω μ}
    {v z : SobolevMultiIndex ℝ b 1 p Ω' μ} {φ : 𝓓(Ω, ℝ)} {ψ : 𝓓(Ω', ℝ)}
    (hφ : fn w =ᵐ[μ.restrict (Ω : Set E)] φ) (hψ : (ψ : E → ℝ) = fun x ↦ φ x * α x)
    (hz : fn z =ᵐ[μ.restrict (Ω' : Set E)] ψ)
    (hv : fn v =ᵐ[μ.restrict (Ω' : Set E)] fun x ↦ fn u x * α x) (i : ι) :
    (weakDeriv z (MultiIndexLE.single i) : E → ℝ) - (weakDeriv v (MultiIndexLE.single i) : E → ℝ)
      =ᵐ[μ.restrict (Ω' : Set E)] fun x ↦
        (weakDeriv w (MultiIndexLE.single i) x - weakDeriv u (MultiIndexLE.single i) x) * α x
          + (fn w x - fn u x) * fderiv ℝ α x (b i) := by
  have hle : μ.restrict (Ω' : Set E) ≤ μ.restrict (Ω : Set E) := Measure.restrict_mono h le_rfl
  have hu' : fn v =ᵐ[μ.restrict (Ω' : Set E)]
      fun x ↦ fn (restrictL ℝ b 1 p μ h u) x * α x := by
    filter_upwards [hv, fn_restrictL h u] with x h1 h2
    rw [h1, h2]
  have hvD := weakDeriv_single_ae_eq_of_fn_ae_eq_mul_contDiff hα hu' i
  have hzD := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hz i
  have hwD := (SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hφ i).filter_mono
    (ae_mono hle)
  have hprod : ∀ x, fderiv ℝ (ψ : E → ℝ) x (b i)
      = fderiv ℝ (φ : E → ℝ) x (b i) * α x + φ x * fderiv ℝ α x (b i) := fun x ↦ by
    rw [hψ, fderiv_fun_mul (φ.contDiff.differentiable (by simp) x) (hα.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  filter_upwards [hzD, hvD, hwD, hφ.filter_mono (ae_mono hle), weakDeriv_restrictL h u
    (MultiIndexLE.single i), fn_restrictL h u] with x h1 h2 h3 h4 h5 h6
  simp only [Pi.sub_apply, h1, h2, hprod x, h5, h6, ← h3, ← h4]
  ring

/-- **A smooth compactly supported factor preserves `W_0^{1,p}`, with restriction to an open
subset**: for `Ω' ≤ Ω`, `α` smooth with compact support and `tsupport α ∩ Ω ⊆ Ω'`,
`u ∈ W_0^{1,p}(Ω)` and `v ∈ W^{1,p}(Ω')` with `v = u α` almost everywhere on `Ω'`, one has
`v ∈ W_0^{1,p}(Ω')`. The test functions `φ_n α`, supported in `Ω'`, converge to `v` in
`W^{1,p}(Ω')`: `(φ_n − u) α` is bounded by `M |φ_n − u|`, and
`∂_i(φ_n α) − ∂_i v = (∂_i φ_n − ∂_i u) α + (φ_n − u) ∂_i α` by the Leibniz rule
(`SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_mul_contDiff`). This is the step
"`θ u ∈ W_0^{1,p}(U ∩ Ω)`" of the chart reduction of Theorem 9.17 (ii) ⇒ (i). -/
theorem SobolevMultiIndexZero.mul_contDiff_mem (h : Ω' ≤ Ω) {α : E → ℝ} (hα : ContDiff ℝ ∞ α)
    (hαc : HasCompactSupport α) (hαΩ : tsupport α ∩ Ω ⊆ Ω') {u : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ) {v : SobolevMultiIndex ℝ b 1 p Ω' μ}
    (hv : fn v =ᵐ[μ.restrict (Ω' : Set E)] fun x ↦ fn u x * α x) :
    v ∈ SobolevMultiIndexZero ℝ b 1 p Ω' μ := by
  have hle : μ.restrict (Ω' : Set E) ≤ μ.restrict (Ω : Set E) := Measure.restrict_mono h le_rfl
  -- the bounds on `α` and `∂_i α`
  obtain ⟨M₀, hM₀⟩ := hαc.exists_bound_of_continuous hα.continuous
  obtain ⟨M₁, hM₁⟩ := (hαc.fderiv ℝ).exists_bound_of_continuous (hα.continuous_fderiv (by simp))
  have hMa : ∀ x, |α x| ≤ M₀ + M₁ * ∑ i, ‖b i‖ := fun x ↦ by
    have := hM₀ x
    rw [Real.norm_eq_abs] at this
    have h2 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
    have h3 : 0 ≤ ∑ i, ‖b i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    nlinarith
  have hMd : ∀ i x, |fderiv ℝ α x (b i)| ≤ M₀ + M₁ * ∑ i, ‖b i‖ := fun i x ↦ by
    have h1 : ‖fderiv ℝ α x (b i)‖ ≤ M₁ * ‖b i‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hM₁ x) (norm_nonneg _))
    have h2 : ‖b i‖ ≤ ∑ j, ‖b j‖ :=
      Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun j _ ↦ norm_nonneg _) (Finset.mem_univ i)
    have h3 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
    have h4 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
    rw [← Real.norm_eq_abs]
    nlinarith
  -- the approximating test functions `φ_n α` on `Ω'`
  obtain ⟨w, φ, hφ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hu
  have hψ : ∀ n, ∃ ψ : 𝓓(Ω', ℝ), (ψ : E → ℝ) = fun x ↦ φ n x * α x := fun n ↦
    ⟨⟨fun x ↦ φ n x * α x, (φ n).contDiff.mul hα, (φ n).hasCompactSupport.mul_right,
      fun x hx ↦ hαΩ ⟨tsupport_mul_subset_right hx, (φ n).tsupport_subset
        (tsupport_mul_subset_left hx)⟩⟩, rfl⟩
  choose ψ hψ using hψ
  choose z hzT hz using fun n ↦ (ψ n).exists_mem_sobolevMultiIndex_testFunctions (b := b) (p := p)
    (μ := μ)
  -- `z_n → v` in `W^{1,p}(Ω')`
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto (f := z) (b := atTop) ?_
    (Eventually.of_forall fun n ↦ SobolevMultiIndexZero.testFunctions_le (hzT n))
  refine SobolevMultiIndex.tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun β ↦ ?_
  have hf : Tendsto (fun n ↦ eLpNorm (fun x ↦ fn (w n) x - fn u x) p (μ.restrict (Ω' : Set E)))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_eLpNorm_fn_sub hw)
      (fun _ ↦ zero_le) fun n ↦ eLpNorm_mono_measure _ hle
  have hfm : ∀ n, AEStronglyMeasurable (fun x ↦ fn (w n) x - fn u x) (μ.restrict (Ω' : Set E)) :=
    fun n ↦ ((memLp (w n)).aestronglyMeasurable.sub (memLp u).aestronglyMeasurable).mono_measure
      hle
  rcases MultiIndexLE.eq_zero_or_exists_eq_single β with rfl | ⟨i, rfl⟩
  · refine (tendsto_eLpNorm_mul_of_tendsto hα.continuous.aestronglyMeasurable hMa hfm hf).congr
      fun n ↦ ?_
    exact (eLpNorm_congr_ae (SobolevMultiIndexZero.fn_sub_ae_eq_mul_aux h (hφ n) (hψ n) (hz n)
      hv)).symm
  · have hg : Tendsto (fun n ↦ eLpNorm (fun x ↦ weakDeriv (w n) (MultiIndexLE.single i) x
        - weakDeriv u (MultiIndexLE.single i) x) p (μ.restrict (Ω' : Set E))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_eLpNorm_weakDeriv_sub hw (MultiIndexLE.single i)) (fun _ ↦ zero_le)
        fun n ↦ eLpNorm_mono_measure _ hle
    have hgm : ∀ n, AEStronglyMeasurable (fun x ↦ weakDeriv (w n) (MultiIndexLE.single i) x
        - weakDeriv u (MultiIndexLE.single i) x) (μ.restrict (Ω' : Set E)) := fun n ↦
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).mono_measure hle
    refine (tendsto_eLpNorm_mul_add_mul_of_tendsto hα.continuous.aestronglyMeasurable
      (((hα.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable) hMa
      (hMd i) hgm hfm hg hf).congr fun n ↦ ?_
    exact (eLpNorm_congr_ae (SobolevMultiIndexZero.weakDeriv_single_sub_ae_eq_mul_aux h hα (hφ n)
      (hψ n) (hz n) hv i)).symm

end SmulContDiff

/-! ### Proposition 9.18, (iii) ⇒ (i): the `Q_+` computation -/

section CubePos

variable {d : ℕ}

/-- The upper half cylinder `Q₊` as an `Opens`, the shape the Sobolev spaces on it take. -/
def unitChartCubePosOpens (d : ℕ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨unitChartCubePos d, isOpen_unitChartCubePos⟩

/-- The underlying set of `unitChartCubePosOpens d` is `unitChartCubePos d`. -/
@[simp]
theorem coe_unitChartCubePosOpens : (unitChartCubePosOpens d : Set _) = unitChartCubePos d := rfl

/-- `Q₊ ≤ Q`. -/
theorem unitChartCubePosOpens_le : unitChartCubePosOpens d ≤ unitChartCubeOpens d :=
  unitChartCubePos_subset

/-- The closure of `Q₊` lies in `{x_N ≥ 0}`. -/
theorem closure_unitChartCubePos_subset :
    closure (unitChartCubePos d) ⊆ {x | 0 ≤ x (Fin.last d)} :=
  closure_minimal (fun _ hx ↦ hx.2.le) (isClosed_le continuous_const continuous_apply_last)

/-- **The one-sided mollifiers of the proof of Proposition 9.18**: normalized bumps `ρ_n`,
nonnegative, smooth, of integral one, supported in the ball of radius `1/(4(n+1))` around
`(3/(4(n+1))) e_N`, hence in `{1/(2(n+1)) ≤ x_N} ∩ closedBall 0 (1/(n+1))`
([brezis2011functional] §9.4, proof of Proposition 9.18, (iii) ⇒ (i),
"`supp ρ_n ⊂ {1/(2n) < x_N < 1/n}`"). -/
theorem exists_oneSided_mollifiers :
    ∃ ρ : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      (∀ n, ContDiff ℝ ∞ (ρ n)) ∧ (∀ n x, 0 ≤ ρ n x) ∧ (∀ n, HasCompactSupport (ρ n)) ∧
      (∀ n, Integrable (ρ n) volume) ∧ (∀ n, ∫ x, ρ n x = 1) ∧
      (∀ n, tsupport (ρ n) ⊆ closedBall 0 (1 / ((n : ℝ) + 1))) ∧
      (∀ n x, x ∈ tsupport (ρ n) → 1 / (2 * ((n : ℝ) + 1)) ≤ x (Fin.last d)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n ↦ by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℕ → EuclideanSpace ℝ (Fin (d + 1)),
      c = fun n : ℕ ↦ (3 / (4 * ((n : ℝ) + 1))) • EuclideanSpace.single (Fin.last d) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hcnorm : ∀ n, ‖c n‖ = 3 / (4 * ((n : ℝ) + 1)) := fun n ↦ by
    rw [hc]
    simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hclast : ∀ n, c n (Fin.last d) = 3 / (4 * ((n : ℝ) + 1)) := fun n ↦ by
    rw [hc]
    simp
  obtain ⟨φ, hφ⟩ : ∃ φ : (n : ℕ) → ContDiffBump (c n), ∀ n,
      (φ n).rOut = 1 / (4 * ((n : ℝ) + 1)) :=
    ⟨fun n ↦ ⟨1 / (8 * ((n : ℝ) + 1)), 1 / (4 * ((n : ℝ) + 1)), by positivity, by
      rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
      linarith [hpos n]⟩, fun n ↦ rfl⟩
  have htsupp : ∀ n, tsupport ((φ n).normed volume) = closedBall (c n) (1 / (4 * ((n : ℝ) + 1))) :=
    fun n ↦ by rw [(φ n).tsupport_normed_eq, hφ n]
  refine ⟨fun n ↦ (φ n).normed volume, fun n ↦ (φ n).contDiff_normed,
    fun n x ↦ (φ n).nonneg_normed x, fun n ↦ (φ n).hasCompactSupport_normed,
    fun n ↦ (φ n).integrable_normed, fun n ↦ (φ n).integral_normed, fun n ↦ ?_, fun n x hx ↦ ?_⟩
  · rw [htsupp n]
    intro x hx
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖c n + (x - c n)‖ := by rw [add_sub_cancel]
      _ ≤ ‖c n‖ + ‖x - c n‖ := norm_add_le _ _
      _ ≤ 3 / (4 * ((n : ℝ) + 1)) + 1 / (4 * ((n : ℝ) + 1)) := by
          rw [hcnorm n]
          exact add_le_add le_rfl (mem_closedBall_iff_norm.1 hx)
      _ = 1 / ((n : ℝ) + 1) := by field_simp; ring
  · rw [htsupp n] at hx
    have h1 : |(x - c n) (Fin.last d)| ≤ 1 / (4 * ((n : ℝ) + 1)) :=
      (EuclideanSpace.abs_apply_last_le _).trans (mem_closedBall_iff_norm.1 hx)
    rw [PiLp.sub_apply, hclast n] at h1
    have h2 := (abs_le.1 h1).1
    have e : 1 / (2 * ((n : ℝ) + 1)) = 3 / (4 * ((n : ℝ) + 1)) - 1 / (4 * ((n : ℝ) + 1)) := by
      field_simp; ring
    rw [e]
    linarith

end CubePos

section Prop918

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open SobolevMultiIndex

/-- **Proposition 9.18, (iii) ⇒ (i), the `Q_+` computation**: let `u ∈ L^p(Q_+)`, `1 ≤ p < ∞`,
be such that its extension by zero to `Q` lies in `W^{1,p}(Q)`; then for every smooth `α` with
compact support in `Q`, the element `v` of `W^{1,p}(Q_+)` with function `α u` lies in
`W_0^{1,p}(Q_+)`.

Proof ([brezis2011functional] §9.4, proof of Proposition 9.18, (iii) ⇒ (i)): `g = α ū` extended
by zero outside `Q` is in `W^{1,p}(ℝ^N)` (`MemSobolevMultiIndex.indicator_mul`); with the
one-sided mollifiers `ρ_n` of `exists_oneSided_mollifiers`, `ρ_n ⋆ g → g` in `L^p(ℝ^N)` and
`∂_i (ρ_n ⋆ g) = ρ_n ⋆ ∂_i g → ∂_i g` (Lemma 9.1,
`HasWeakIteratedLineDerivOn.convolution_of_integrable`, and
`MeasureTheory.tendsto_eLpNorm_convolution_sub_of_tendsto_support`), while
`supp (ρ_n ⋆ g) ⊆ supp ρ_n + supp g ⊆ Q_+` for `n` large: adding a vector with
`x_N ≥ 1/(2(n+1))` and norm at most `1/(n+1)` pushes the support of `g`, which lies in
`supp α ∩ closure Q_+`, into `{x_N > 0}` and keeps it in `Q`. So the `ρ_n ⋆ g` are smooth with
compact support in `Q_+`, hence lie in `W_0^{1,p}(Q_+)` (Lemma 9.5), and `v` is their limit in
`W^{1,p}(Q_+)`, in the closed subspace `W_0^{1,p}(Q_+)`. -/
theorem SobolevEuclidean.mem_zero_of_indicator_memSobolev_unitChartCubePos (hp' : p ≠ ⊤)
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((unitChartCubePos d).indicator u) 1 p (unitChartCubeOpens d) volume)
    {α : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (hαQ : tsupport α ⊆ unitChartCube d)
    {v : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hv : fn v =ᵐ[volume.restrict (unitChartCubePos d)] fun x ↦ α x * u x) :
    v ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d) := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hQm : MeasurableSet (unitChartCubePos d) := isOpen_unitChartCubePos.measurableSet
  -- the function `g = α ū` on the whole space, in `W^{1,p}(ℝ^N)`
  obtain ⟨g, hgdef⟩ : ∃ g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      g = fun x ↦ α x * (unitChartCubePos d).indicator u x := ⟨_, rfl⟩
  have hcut : IsSobolevCutoff (unitChartCubeOpens d) α :=
    IsSobolevCutoff.of_hasCompactSupport hα hαc hαQ
  have hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis g 1 p ⊤
      volume := by
    refine (hu.indicator_mul hp hcut).congr_ae (Eventually.of_forall fun x ↦ ?_)
    change (unitChartCube d).indicator (fun x ↦ α x • (unitChartCubePos d).indicator u x) x = g x
    by_cases hx : x ∈ unitChartCube d
    · simp only [hgdef, Set.indicator_of_mem hx, smul_eq_mul]
    · have : α x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hαQ h)
      simp [hgdef, Set.indicator_of_notMem hx, this]
  have hgp : MemLp g p volume := by simpa [Measure.restrict_coe_top] using hg.memLp
  have hgc : HasCompactSupport g := by rw [hgdef]; exact hαc.mul_right
  have hgv : g =ᵐ[volume.restrict (unitChartCubePos d)] fn v := by
    filter_upwards [hv, ae_restrict_mem hQm] with x hx hxQ
    simp only [hgdef, hx, Set.indicator_of_mem hxQ]
  have hgsupp : Function.support g ⊆ tsupport α ∩ closure (unitChartCubePos d) := by
    intro x hx
    rw [Function.mem_support, hgdef] at hx
    refine ⟨subset_tsupport _ (left_ne_zero_of_mul hx), subset_closure ?_⟩
    by_contra h
    exact hx (by simp [Set.indicator_of_notMem h])
  -- the weak partial derivatives of `g` on the whole space
  have hw : ∀ i : Fin (d + 1), ∃ w : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] g w ⊤ volume ∧ MemLp w p volume := by
    intro i
    obtain ⟨w, hw, hwp⟩ := hg.2 (Pi.single i 1) (by simp)
    refine ⟨w, ?_, by simpa [Measure.restrict_coe_top] using hwp⟩
    have := hw.of_perm (multiIndexTuple_single_perm
      ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis : Fin (d + 1) → _) i)
    rwa [EuclideanSpace.basisFun_toBasis_apply] at this
  choose w hw hwp using hw
  -- the margin between the support of `α` and the boundary of `Q`
  obtain ⟨V, ε, -, hαV, hε, -, -, hV⟩ :=
    hαc.exists_pos_forall_closedBall_subset isOpen_unitChartCube hαQ
  -- the one-sided mollifiers
  obtain ⟨ρ, hρs, hρ0, hρc, hρi, hρ1, hρt, hρN⟩ := exists_oneSided_mollifiers (d := d)
  have hr : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hρsupp : ∀ n, Function.support (ρ n) ⊆ closedBall 0 (1 / ((n : ℝ) + 1)) :=
    fun n ↦ (subset_tsupport _).trans (hρt n)
  -- the convolutions converge in `L^p(ℝ^N)`, together with their derivatives
  have hL0 : Tendsto (fun n ↦ eLpNorm (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g - g) p volume)
      atTop (𝓝 0) :=
    tendsto_eLpNorm_convolution_sub_of_tendsto_support hρ0 hρi hρ1 hρsupp hr hp hp' hgp
  have hLi : ∀ i, Tendsto (fun n ↦ eLpNorm (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w i - w i)
      p volume) atTop (𝓝 0) := fun i ↦
    tendsto_eLpNorm_convolution_sub_of_tendsto_support hρ0 hρi hρ1 hρsupp hr hp hp' (hwp i)
  -- the convolutions are smooth with compact support, and supported in `Q₊` for `n` large
  have hsm : ∀ n, ContDiff ℝ ∞ (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := fun n ↦
    (hρc n).contDiff_convolution_left _ (hρs n) (hgp.locallyIntegrable hp)
  have hcs : ∀ n, HasCompactSupport (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := fun n ↦
    (hρc n).convolution _ hgc
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 1 / ((n₀ : ℝ) + 1) ≤ ε := by
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
    exact ⟨n₀, hn₀.le⟩
  have hsupp : ∀ n ≥ n₀, tsupport (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
      ⊆ unitChartCubePos d := by
    intro n hn
    have hnε : 1 / ((n : ℝ) + 1) ≤ ε := by
      refine le_trans ?_ hn₀
      gcongr
    have hS : IsCompact (tsupport (ρ n) + (tsupport α ∩ closure (unitChartCubePos d))) :=
      IsCompact.add (hρc n) (hαc.inter_right isClosed_closure)
    refine (closure_minimal ((support_convolution_subset _).trans
      (add_subset_add (subset_tsupport _) hgsupp)) hS.isClosed).trans ?_
    rintro z ⟨y, hy, x, ⟨hxα, hxQ⟩, rfl⟩
    have hyN := hρN n y hy
    have hxN := closure_unitChartCubePos_subset hxQ
    have hyn : ‖y‖ ≤ 1 / ((n : ℝ) + 1) := mem_closedBall_zero_iff.1 (hρt n hy)
    refine ⟨hV x (hαV hxα) ?_, ?_⟩
    · rw [mem_closedBall_iff_norm, add_sub_cancel_right]
      exact hyn.trans hnε
    · rw [PiLp.add_apply]
      have : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
      exact add_pos_of_pos_of_nonneg (this.trans_le hyN) hxN
  -- the elements of `W^{1,p}(Q₊)` with the convolutions as functions lie in `W_0^{1,p}(Q₊)`
  choose T hT using fun n ↦ (hsm n).exists_sobolevMultiIndex_of_hasCompactSupport
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (p := p)
    (Ω := unitChartCubePosOpens d) (μ := volume) (hcs n)
  simp only [coe_unitChartCubePosOpens] at hT
  have hTmem : ∀ n ≥ n₀, T n ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d) :=
    fun n hn ↦ mem_zero_of_fn_ae_eq_of_tsupport_subset hp' (T n) (hcs n) (hsupp n hn) (hT n)
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto (f := T) (b := atTop) ?_
    ((eventually_ge_atTop n₀).mono hTmem)
  refine tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun β ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single β with rfl | ⟨i, rfl⟩
  · -- the functions
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL0 (fun _ ↦ zero_le)
      fun n ↦ ?_
    rw [weakDeriv_zero, weakDeriv_zero, coe_unitChartCubePosOpens,
      eLpNorm_congr_ae ((hT n).sub hgv.symm)]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · -- the derivatives: `∂_i (T n) = ρ n ⋆ w i` and `∂_i v = w i` on `Q₊`
    have hTi : ∀ n, (weakDeriv (T n) (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (unitChartCubePos d)]
          ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w i := by
      intro n
      have h1 := (hasWeakIteratedLineDerivOn (T n) (MultiIndexLE.single i)).of_perm
        (multiIndexTuple_single_perm
          ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis : Fin (d + 1) → _) i)
      rw [EuclideanSpace.basisFun_toBasis_apply] at h1
      have h2 := (((hw i).convolution_of_integrable (hρi n) hp hgp (hwp i)).mono
        (le_top : unitChartCubePosOpens d ≤ ⊤)).congr_ae (hT n).symm (EventuallyEq.refl _ _)
      exact (ae_restrict_iff' hQm).2 (h1.ae_eq h2)
    have hvi : (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (unitChartCubePos d)] w i := by
      have h1 := (hasWeakIteratedLineDerivOn v (MultiIndexLE.single i)).of_perm
        (multiIndexTuple_single_perm
          ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis : Fin (d + 1) → _) i)
      rw [EuclideanSpace.basisFun_toBasis_apply] at h1
      have h2 := ((hw i).mono (le_top : unitChartCubePosOpens d ≤ ⊤)).congr_ae hgv
        (EventuallyEq.refl _ _)
      exact (ae_restrict_iff' hQm).2 (h1.ae_eq h2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hLi i) (fun _ ↦ zero_le)
      fun n ↦ ?_
    exact (eLpNorm_congr_ae ((hTi n).sub hvi)).trans_le
      (eLpNorm_mono_measure _ Measure.restrict_le_self)

end Prop918

/-! ### Proposition 9.18, (iii) ⇒ (i): the chart reduction -/

section Prop918Chart

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

namespace ContDiffChart

variable (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- **The chart transfer of `θ ū`**: for a chart `c` of `Ω`, a smooth compactly supported `θ`
with `tsupport θ ⊆ c.U`, and `u` whose extension by zero `ū` lies in `W^{1,p}(ℝ^N)`, the
function `(θ u) ∘ H` on `Q_+`, extended by zero to `Q`, lies in `W^{1,p}(Q)`: it is
`(θ ū) ∘ H`, the transfer along the chart (Proposition 9.6) of `θ ū ∈ W^{1,p}(U)`, because
`H` sends `Q ∖ Q_+` outside `Ω`. -/
theorem indicator_comp_toFun_memSobolevMultiIndex {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((unitChartCubePos d).indicator fun y ↦ θ (c.toFun y) * u (c.toFun y)) 1 p
      (unitChartCubeOpens d) volume := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨M, hM⟩ := (IsSobolevCutoff.of_hasCompactSupport (Ω := ⊤) hθ hθc
    (subset_univ _)).exists_bound
  have hw : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ x * (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u x) 1 p ⊤ volume :=
    hu.contDiff_mul hp hθ hM
  obtain ⟨M', hH⟩ := c.isDiffeoOnWithBoundedJacobian le_rfl
  have hH' : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCubeOpens d : Set _)
    (c.opensU : Set _) M' := hH
  have hwQ := (hw.mono_set (le_top : c.opensU ≤ ⊤)).comp_diffeoOn hH'
  refine hwQ.congr_ae ?_
  filter_upwards [ae_restrict_mem isOpen_unitChartCube.measurableSet] with y hy
  by_cases hyQ : y ∈ unitChartCubePos d
  · have hyΩ : c.toFun y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := (c.toFun_mem_iff hy).2 hyQ
    simp only [Set.indicator_of_mem hyΩ, Set.indicator_of_mem hyQ]
  · have hyΩ : c.toFun y ∉ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := fun h ↦
      hyQ ((c.toFun_mem_iff hy).1 h)
    simp only [Set.indicator_of_notMem hyΩ, Set.indicator_of_notMem hyQ, mul_zero]

/-- **The chart piece of Proposition 9.18, (iii) ⇒ (i), on `Q_+`**: with `c`, `θ`, `u` as in
`ContDiffChart.indicator_comp_toFun_memSobolevMultiIndex`, an element `Z` of `W^{1,p}(Q_+)`
with function `(θ u) ∘ H` lies in `W_0^{1,p}(Q_+)`: the `Q_+` computation
`SobolevEuclidean.mem_zero_of_indicator_memSobolev_unitChartCubePos` with a smooth `α` equal to
`1` on the compact `H⁻¹(supp θ) ⊆ Q`, where `α (θ u) ∘ H = (θ u) ∘ H`. -/
theorem mem_zero_unitChartCubePos_of_indicator_memSobolev (hp' : p ≠ ⊤)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume)
    {Z : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hZ : fn Z =ᵐ[volume.restrict (unitChartCubePos d)] fun y ↦ θ (c.toFun y) * u (c.toFun y)) :
    Z ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d) := by
  have hQm : MeasurableSet (unitChartCubePos d) := isOpen_unitChartCubePos.measurableSet
  -- a smooth `α`, compactly supported in `Q`, equal to `1` on `H⁻¹(supp θ)`
  have hK : IsCompact (c.invFun '' tsupport θ) :=
    hθc.image_of_continuousOn (c.continuousOn_invFun.mono (hθU.trans subset_closure))
  have hKQ : c.invFun '' tsupport θ ⊆ unitChartCube d :=
    (image_mono hθU).trans c.mapsTo_invFun.image_subset
  obtain ⟨V, -, hVo, hKV, -, hVc, hVQ, -⟩ :=
    hK.exists_pos_forall_closedBall_subset isOpen_unitChartCube hKQ
  obtain ⟨α, hαs, hα1, hαV, -⟩ := hK.exists_contDiff_eqOn_one hVo hKV
  have hαc : HasCompactSupport α :=
    hVc.of_isClosed_subset isClosed_closure (hαV.trans subset_closure)
  have hαQ : tsupport α ⊆ unitChartCube d := hαV.trans (subset_closure.trans hVQ)
  refine SobolevEuclidean.mem_zero_of_indicator_memSobolev_unitChartCubePos hp'
    (c.indicator_comp_toFun_memSobolevMultiIndex hθ hθc hu) hαs hαc hαQ ?_
  filter_upwards [hZ, ae_restrict_mem hQm] with y hy hyQ
  rw [hy]
  by_cases hθy : θ (c.toFun y) = 0
  · simp [hθy]
  · have hyK : y ∈ c.invFun '' tsupport θ :=
      ⟨c.toFun y, subset_tsupport _ hθy, c.invFun_toFun (unitChartCubePos_subset hyQ)⟩
    rw [hα1 hyK, Pi.one_apply, one_mul]

/-- **The chart piece of Proposition 9.18, (iii) ⇒ (i), on `Q_+`, existence form**: with `c`,
`θ`, `u` as in `ContDiffChart.indicator_comp_toFun_memSobolevMultiIndex`, there is an element of
`W_0^{1,p}(Q_+)` with function `(θ u) ∘ H`. -/
theorem exists_mem_zero_unitChartCubePos_of_indicator_memSobolev (hp' : p ≠ ⊤)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume) :
    ∃ Z ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d),
      fn Z =ᵐ[volume.restrict (unitChartCubePos d)] fun y ↦ θ (c.toFun y) * u (c.toFun y) := by
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun y ↦ θ (c.toFun y) * u (c.toFun y)) 1 p (unitChartCubePosOpens d) volume :=
    ((c.indicator_comp_toFun_memSobolevMultiIndex hθ hθc hu).mono_set
      unitChartCubePosOpens_le).congr_ae
      (indicator_ae_eq_restrict isOpen_unitChartCubePos.measurableSet)
  obtain ⟨Z, hZ⟩ := hmem.exists_sobolevMultiIndex
  exact ⟨Z, c.mem_zero_unitChartCubePos_of_indicator_memSobolev hp' hθ hθc hθU hu hZ, hZ⟩

/-- An element `V` of `W^{1,p}(Ω'')` whose function is that of the image under a map
`T : W^{1,p}(Ω') → W^{1,p}(Ω'')` preserving `W_0^{1,p}` of an element of `W_0^{1,p}(Ω')` lies in
`W_0^{1,p}(Ω'')`. -/
theorem _root_.SobolevMultiIndexZero.mem_of_fn_ae_eq_map {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {ι : Type*} [Fintype ι]
    [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω' Ω'' : Opens E}
    {μ : Measure E} (T : SobolevMultiIndex F b 1 p Ω' μ →L[ℝ] SobolevMultiIndex F b 1 p Ω'' μ)
    (hT : ∀ z ∈ SobolevMultiIndexZero F b 1 p Ω' μ, T z ∈ SobolevMultiIndexZero F b 1 p Ω'' μ)
    {Z : SobolevMultiIndex F b 1 p Ω' μ} (hZ : Z ∈ SobolevMultiIndexZero F b 1 p Ω' μ)
    {V : SobolevMultiIndex F b 1 p Ω'' μ} (heq : fn (T Z) =ᵐ[μ.restrict (Ω'' : Set E)] fn V) :
    V ∈ SobolevMultiIndexZero F b 1 p Ω'' μ :=
  ext_of_fn_ae_eq heq ▸ hT Z hZ

/-- **The chart piece of Proposition 9.18, (iii) ⇒ (i), on `U ∩ Ω`**: with `c`, `θ`, `u` as in
`ContDiffChart.indicator_comp_toFun_memSobolevMultiIndex`, an element `V` of `W^{1,p}(Ω)` with
function `θ u` restricts to an element of `W_0^{1,p}(U ∩ Ω)`: its restriction is the transfer
back along `H⁻¹` (`SobolevMultiIndexZero.compDiffeoL_mem`) of an element `Z` of `W_0^{1,p}(Q_+)`
with function `(θ u) ∘ H`
(`ContDiffChart.exists_mem_zero_unitChartCubePos_of_indicator_memSobolev`). The chart's Jacobian
bundle and `Z` are arguments, so that each of the three elaborations stays
within its own heartbeat budget. -/
theorem restrictL_mem_zero_of_indicator_memSobolev_aux (hp' : p ≠ ⊤) {M : ℝ}
    (hH : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCubePosOpens d : Set _)
      (c.opensInter : Set _) M)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {Z : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hZ0 : Z ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d))
    (hZ : fn Z =ᵐ[volume.restrict (unitChartCubePos d)] fun y ↦ θ (c.toFun y) * u (c.toFun y))
    {V : SobolevEuclidean (d + 1) 1 p Ω}
    (hV : fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ θ x * u x) :
    restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume c.opensInter_le V
      ∈ SobolevEuclideanZero (d + 1) 1 p c.opensInter := by
  refine SobolevMultiIndexZero.mem_of_fn_ae_eq_map
    (compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume hH.symm)
    (fun z hz ↦ SobolevMultiIndexZero.compDiffeoL_mem hp' hH.symm hz) hZ0 ?_
  have h1 := hH.symm.ae_comp_restrict (P := fun y ↦ fn Z y = θ (c.toFun y) * u (c.toFun y)) hZ
  have h2 : fn V =ᵐ[volume.restrict (c.opensInter : Set _)] fun x ↦ θ x * u x :=
    hV.filter_mono (ae_mono (Measure.restrict_mono c.opensInter_le le_rfl))
  filter_upwards [fn_compDiffeoL hH.symm Z, h1, fn_restrictL c.opensInter_le V, h2,
    ae_restrict_mem c.opensInter.isOpen.measurableSet] with x hx1 hx2 hx3 hx4 hx5
  refine hx1.trans (hx2.trans ?_)
  rw [c.toFun_invFun hx5.1]
  exact (hx3.trans hx4).symm

/-- **The chart piece of Proposition 9.18, (iii) ⇒ (i), on `U ∩ Ω`**: with `c`, `θ`, `u` as in
`ContDiffChart.indicator_comp_toFun_memSobolevMultiIndex`, an element `V` of `W^{1,p}(Ω)` with
function `θ u` restricts to an element of `W_0^{1,p}(U ∩ Ω)`. -/
theorem restrictL_mem_zero_of_indicator_memSobolev (hp' : p ≠ ⊤)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume)
    {V : SobolevEuclidean (d + 1) 1 p Ω}
    (hV : fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ θ x * u x) :
    restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume c.opensInter_le V
      ∈ SobolevEuclideanZero (d + 1) 1 p c.opensInter := by
  obtain ⟨M, hH⟩ := c.isDiffeoOnWithBoundedJacobian_pos le_rfl Ω.isOpen
  obtain ⟨Z, hZ0, hZ⟩ :=
    c.exists_mem_zero_unitChartCubePos_of_indicator_memSobolev hp' hθ hθc hθU hu
  exact c.restrictL_mem_zero_of_indicator_memSobolev_aux hp' hH hZ0 hZ hV

/-- **The chart piece of Proposition 9.18, (iii) ⇒ (i)**: with `c`, `θ`, `u` as in
`ContDiffChart.indicator_comp_toFun_memSobolevMultiIndex`, an element `V` of `W^{1,p}(Ω)` with
function `θ u` lies in `W_0^{1,p}(Ω)`: it restricts to an element of `W_0^{1,p}(U ∩ Ω)`
(`ContDiffChart.restrictL_mem_zero_of_indicator_memSobolev`) and vanishes on `Ω` outside the
closed `tsupport θ`, whose trace on `Ω` lies in `U ∩ Ω`
(`SobolevMultiIndexZero.mem_of_mem_restrict`). -/
theorem mem_zero_of_indicator_memSobolev (hp' : p ≠ ⊤)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume)
    {V : SobolevEuclidean (d + 1) 1 p Ω}
    (hV : fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ θ x * u x) :
    V ∈ SobolevEuclideanZero (d + 1) 1 p Ω := by
  refine SobolevMultiIndexZero.mem_of_mem_restrict c.opensInter_le
    (c.restrictL_mem_zero_of_indicator_memSobolev hp' hθ hθc hθU hu hV) (isClosed_tsupport θ)
    (fun x hx ↦ ⟨hθU hx.1, hx.2⟩) ?_
  filter_upwards [hV] with x hx hxθ
  rw [hx, image_eq_zero_of_notMem_tsupport hxθ, zero_mul]

end ContDiffChart

namespace SobolevEuclideanZero

/-- **Proposition 9.18, (iii) ⇒ (i), for `u` vanishing outside a ball**: on a `C^1` chart domain
`Ω`, `1 ≤ p < ∞`, if `u` vanishes for `‖x‖ > R` and its extension by zero lies in
`W^{1,p}(ℝ^N)`, then the element `v` of `W^{1,p}(Ω)` with function `u` lies in `W_0^{1,p}(Ω)`.

Proof ([brezis2011functional] Proposition 9.18, (iii) ⇒ (i), "by local charts and partition of
unity"): cover the compact `∂Ω ∩ closedBall 0 R` by finitely many charts `c_i` and take Lemma
9.3's partition `θ₀ + ∑ θ_i = 1` (`IsCompact.exists_contDiff_partitionOfUnity`) with
`tsupport θ_i ⊆ U_i` and `θ₀` vanishing near that piece of the boundary. Each `θ_i u` is the
function of an element of `W_0^{1,p}(Ω)` by the chart piece
`ContDiffChart.mem_zero_of_indicator_memSobolev`, and `θ₀ u = u − ∑ θ_i u` vanishes on `Ω`
outside the compact `tsupport θ₀ ∩ closure Ω ∩ closedBall 0 R ⊆ Ω`, hence is in `W_0^{1,p}(Ω)` by
Lemma 9.5; `v` is the sum. -/
theorem mem_of_indicator_memSobolev_of_forall_eq_zero (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume)
    {R : ℝ} (huR : ∀ x, R < ‖x‖ → u x = 0) {v : SobolevEuclidean (d + 1) 1 p Ω}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u) :
    v ∈ SobolevEuclideanZero (d + 1) 1 p Ω := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hΩm := Ω.isOpen.measurableSet
  -- the compact piece of the boundary inside the ball, its finite atlas and partition of unity
  have hΓ : IsCompact (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ closedBall 0 R) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_frontier.inter isClosed_closedBall)
      (isBounded_closedBall.subset inter_subset_right)
  obtain ⟨k, c, hc⟩ := hΩ.exists_finite_atlas_of_isCompact hΓ inter_subset_left
  obtain ⟨θ₀, θ, -, hθs, -, -, hsum, hθc, hθU, hθ₀Γ⟩ :=
    hΓ.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hc
  -- `u ∈ W^{1,p}(Ω)`, and the elements `θ_i u`
  have huΩ : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u 1 p Ω
      volume :=
    (hu.mono_set le_top).congr_ae (indicator_ae_eq_restrict hΩm)
  have hθu : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ i x * u x) 1 p Ω volume := fun i ↦ by
    obtain ⟨M, hM⟩ := (IsSobolevCutoff.of_hasCompactSupport (Ω := ⊤) (hθs i) (hθc i)
      (subset_univ _)).exists_bound
    exact huΩ.contDiff_mul hp (hθs i) hM
  choose V hV using fun i ↦ (hθu i).exists_sobolevMultiIndex
  have hVmem : ∀ i, V i ∈ SobolevEuclideanZero (d + 1) 1 p Ω := fun i ↦
    (c i).mem_zero_of_indicator_memSobolev hp' (hθs i) (hθc i) (hθU i) hu (hV i)
  -- the remaining piece `θ₀ u = u − ∑ θ_i u` has compact support in `Ω`
  have hV₀ : fn (v - ∑ i, V i) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ θ₀ x * u x := by
    filter_upwards [fn_sub v (∑ i, V i), fn_finset_sum Finset.univ V, ae_all_iff.2 hV, hv]
      with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Finset.sum_apply, h4]
    simp only [h3]
    have := hsum x
    rw [← Finset.sum_mul]
    have e : ∑ i, θ i x = 1 - θ₀ x := by linarith
    rw [e]
    ring
  have hK : IsCompact (tsupport θ₀ ∩ closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ∩ closedBall 0 R) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) R).inter_left
      ((isClosed_tsupport θ₀).inter isClosed_closure)
  have hKΩ : tsupport θ₀ ∩ closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ closedBall 0 R
      ⊆ Ω := by
    rintro x ⟨⟨hxθ, hxc⟩, hxR⟩
    rw [closure_eq_interior_union_frontier, Ω.isOpen.interior_eq] at hxc
    rcases hxc with hxΩ | hxf
    · exact hxΩ
    · exact absurd ⟨hxf, hxR⟩ (disjoint_left.1 hθ₀Γ hxθ)
  have hV₀mem : v - ∑ i, V i ∈ SobolevEuclideanZero (d + 1) 1 p Ω := by
    refine mem_zero_of_ae_eq_zero_compl_isCompact hp' _ hK hKΩ ?_
    filter_upwards [hV₀, ae_restrict_mem hΩm] with x hx hxΩ hxK
    rw [hx]
    by_cases hxθ : x ∈ tsupport θ₀
    · by_cases hxR : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) R
      · exact absurd ⟨⟨hxθ, subset_closure hxΩ⟩, hxR⟩ hxK
      · rw [huR x (not_le.1 fun h ↦ hxR (mem_closedBall_zero_iff.2 h)), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul]
  have e : v = (v - ∑ i, V i) + ∑ i, V i := by abel
  rw [e]
  exact add_mem hV₀mem (Submodule.sum_mem _ fun i _ ↦ hVmem i)

/-- **Proposition 9.18, (iii) ⇒ (i)**: on a `C^1` chart domain `Ω ⊆ ℝ^N`, `1 ≤ p < ∞`, a function
`u` whose extension by zero `ū = Ω.indicator u` lies in `W^{1,p}(ℝ^N)` is the function of an
element of `W_0^{1,p}(Ω)` ([brezis2011functional] Proposition 9.18, (iii) ⇒ (i); the converse
(i) ⇒ (iii) is `SobolevMultiIndexZero.indicator_memSobolevMultiIndex`, valid on every open set).
The case of `u` vanishing outside a ball is
`SobolevEuclideanZero.mem_of_indicator_memSobolev_of_forall_eq_zero`; in general, with the
cut-off sequence `ζ_n` (`SobolevMultiIndex.tendsto_cutoff_smul`), `ζ_n u` has bounded support and
its extension by zero `ζ_n ū` lies in `W^{1,p}(ℝ^N)`, so the elements `ζ_n u` lie in
`W_0^{1,p}(Ω)` and converge to `u` in `W^{1,p}(Ω)`, which is closed. -/
theorem mem_of_indicator_memSobolev (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume) :
    ∃ v ∈ SobolevEuclideanZero (d + 1) 1 p Ω,
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hΩm := Ω.isOpen.measurableSet
  have huΩ : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u 1 p Ω
      volume :=
    (hu.mono_set le_top).congr_ae (indicator_ae_eq_restrict hΩm)
  obtain ⟨U, hU⟩ := huΩ.exists_sobolevMultiIndex
  refine ⟨U, ?_, hU⟩
  -- the cut-off sequence `ζ_n U → U`
  obtain ⟨ζ, hζ, hζ1, hζs, hζ01⟩ := exists_contDiff_eqOn_one_closedBall_one
    (EuclideanSpace ℝ (Fin (d + 1)))
  obtain ⟨w, hw, -, hwt⟩ :=
    tendsto_cutoff_smul hp' hζ hζ01 hζ1 (hζs.trans ball_subset_closedBall) U
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hwt (Eventually.of_forall fun n ↦ ?_)
  have hcpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hζc : HasCompactSupport ζ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) 2).of_isClosed_subset
      (isClosed_tsupport ζ) (hζs.trans ball_subset_closedBall)
  -- the cut-off `ζ_n`: smooth, compactly supported, vanishing for `‖x‖ > 2 (n + 1)`
  have hζn : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ ζ (((n : ℝ) + 1)⁻¹ • x) :=
    hζ.comp (contDiff_id.const_smul _)
  have hζnc : HasCompactSupport fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ ζ (((n : ℝ) + 1)⁻¹ • x) :=
    hζc.comp_homeomorph (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (inv_ne_zero hcpos.ne'))
  have hζn0 : ∀ x : EuclideanSpace ℝ (Fin (d + 1)), 2 * ((n : ℝ) + 1) < ‖x‖ →
      ζ (((n : ℝ) + 1)⁻¹ • x) = 0 := fun x hx ↦ by
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have h2 : ‖((n : ℝ) + 1)⁻¹ • x‖ < 2 := by simpa using hζs h
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos, inv_mul_lt_iff₀ hcpos] at h2
    linarith
  obtain ⟨M, hM⟩ := (IsSobolevCutoff.of_hasCompactSupport (Ω := ⊤) hζn hζnc
    (subset_univ _)).exists_bound
  have hun : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
        fun x ↦ ζ (((n : ℝ) + 1)⁻¹ • x) * u x) 1 p ⊤ volume := by
    refine (hu.contDiff_mul hp hζn hM).congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  refine mem_of_indicator_memSobolev_of_forall_eq_zero hp' hΩ hun (R := 2 * ((n : ℝ) + 1))
    (fun x hx ↦ by rw [hζn0 x hx, zero_mul]) ?_
  filter_upwards [hw n, hU] with x hx1 hx2
  rw [hx1, hx2]

end SobolevEuclideanZero

end Prop918Chart

/-! ### Theorem 9.17, (ii) ⇒ (i): the `Q_+` computation -/

section Strip

variable {d : ℕ}

/-- The strip `{x ∈ Q_+ : x_N < ε}` at the bottom of the upper half cylinder. -/
def unitChartCubeStrip (d : ℕ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x ∈ unitChartCubePos d | x (Fin.last d) < ε}

/-- The strip lies in `Q_+`. -/
theorem unitChartCubeStrip_subset {ε : ℝ} : unitChartCubeStrip d ε ⊆ unitChartCubePos d :=
  fun _ hx ↦ hx.1

/-- The strip is open. -/
theorem isOpen_unitChartCubeStrip {ε : ℝ} : IsOpen (unitChartCubeStrip d ε) :=
  isOpen_unitChartCubePos.inter (isOpen_lt continuous_apply_last continuous_const)

/-- The strip is measurable. -/
theorem measurableSet_unitChartCubeStrip {ε : ℝ} : MeasurableSet (unitChartCubeStrip d ε) :=
  isOpen_unitChartCubeStrip.measurableSet

/-- The strip, through the last-coordinate splitting: for `0 < ε ≤ 1`,
`(x', t) ∈ {x ∈ Q_+ : x_N < ε}` iff `‖x'‖ < 1` and `0 < t < ε`. -/
theorem snocLast_mem_unitChartCubeStrip_iff {ε : ℝ} (hε : ε ≤ 1) {x' : EuclideanSpace ℝ (Fin d)}
    {t : ℝ} :
    EuclideanSpace.snocLast x' t ∈ unitChartCubeStrip d ε ↔ ‖x'‖ < 1 ∧ 0 < t ∧ t < ε := by
  simp only [unitChartCubeStrip, unitChartCubePos, unitChartCube, mem_ofPred_eq,
    EuclideanSpace.init_snocLast, EuclideanSpace.snocLast_apply_last]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨h1, ?_⟩, h2⟩, h3⟩
    rw [abs_of_pos h2]
    exact h3.trans_le hε

/-- **Fubini on the strip**: for `0 < ε ≤ 1` and an almost everywhere measurable `F`,
`∫⁻_{x ∈ Q_+, x_N < ε} F = ∫⁻_{‖x'‖ < 1} ∫⁻_{0 < t < ε} F (x', t)`. -/
theorem lintegral_unitChartCubeStrip {ε : ℝ} (hε : ε ≤ 1)
    {F : EuclideanSpace ℝ (Fin (d + 1)) → ℝ≥0∞} (hF : AEMeasurable F) :
    ∫⁻ x in unitChartCubeStrip d ε, F x
      = ∫⁻ x' in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ t in Ioo 0 ε,
        F (EuclideanSpace.snocLast x' t) := by
  rw [← lintegral_indicator measurableSet_unitChartCubeStrip,
    EuclideanSpace.lintegral_lastInit _ (hF.indicator measurableSet_unitChartCubeStrip),
    ← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun x' ↦ ?_
  by_cases hx' : x' ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1
  · rw [Set.indicator_of_mem hx', ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t ↦ ?_
    by_cases ht : t ∈ Ioo 0 ε
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem]
      exact (snocLast_mem_unitChartCubeStrip_iff hε).2 ⟨mem_ball_zero_iff.1 hx', ht.1, ht.2⟩
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem]
      exact fun h ↦ ht ⟨((snocLast_mem_unitChartCubeStrip_iff hε).1 h).2.1,
        ((snocLast_mem_unitChartCubeStrip_iff hε).1 h).2.2⟩
  · rw [Set.indicator_of_notMem hx']
    have h0 : ∀ t, (unitChartCubeStrip d ε).indicator F (EuclideanSpace.snocLast x' t) = 0 :=
      fun t ↦ Set.indicator_of_notMem (fun h ↦
        hx' (mem_ball_zero_iff.2 ((snocLast_mem_unitChartCubeStrip_iff hε).1 h).1)) F
    simp [h0]

/-- **The strip inequality for a `C¹` function supported in `Q_+`**: for `0 < ε ≤ 1`,
`∫_{x ∈ Q_+, x_N < ε} |g| ≤ ε ∫_{x ∈ Q_+, x_N < ε} |∂_N g|`. The fundamental theorem of calculus
along the last coordinate from `x_N = 0`, where `g` vanishes: `|g(x', t)| ≤ ∫₀^ε |∂_N g(x', s)| ds`
for `0 < t < ε`, integrated over `t ∈ (0, ε)` and `‖x'‖ < 1` (`lintegral_unitChartCubeStrip`). -/
theorem lintegral_unitChartCubeStrip_le_of_contDiff {ε : ℝ} (hε : ε ≤ 1)
    {g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hg : ContDiff ℝ 1 g)
    (hgs : tsupport g ⊆ unitChartCubePos d) :
    ∫⁻ x in unitChartCubeStrip d ε, ‖g x‖ₑ
      ≤ ENNReal.ofReal ε * ∫⁻ x in unitChartCubeStrip d ε,
        ‖fderiv ℝ g x (EuclideanSpace.single (Fin.last d) 1)‖ₑ := by
  obtain ⟨D, hDdef⟩ : ∃ D : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
    D = fun x ↦ fderiv ℝ g x (EuclideanSpace.single (Fin.last d) 1) := ⟨_, rfl⟩
  have hgc : Continuous g := hg.continuous
  have hDc : Continuous D := by
    rw [hDdef]; exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hzero : ∀ x, x ∉ unitChartCubePos d → g x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs h)
  -- the derivative of `g` along the last coordinate
  have hderiv : ∀ (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ),
      HasDerivAt (fun s ↦ g (EuclideanSpace.snocLast x' s))
        (D (EuclideanSpace.snocLast x' t)) t := by
    intro x' t
    have h1 : HasDerivAt (fun s : ℝ ↦ EuclideanSpace.snocLast x' s)
        (EuclideanSpace.single (Fin.last d) 1) t := by
      have heq : (fun s : ℝ ↦ EuclideanSpace.snocLast x' s)
          = fun s ↦ EuclideanSpace.snocLast x' 0 + s • EuclideanSpace.single (Fin.last d) 1 := by
        funext s
        exact EuclideanSpace.snocLast_eq_add_smul_single x' s
      rw [heq]
      exact (((hasDerivAt_id' t).smul_const _).const_add (EuclideanSpace.snocLast x' 0)).congr_deriv
        (one_smul ℝ _)
    have h2 := (hg.differentiable one_ne_zero (EuclideanSpace.snocLast x' t)).hasFDerivAt
    rw [hDdef]
    exact h2.comp_hasDerivAt t h1
  -- the pointwise bound on the strip
  have hpt : ∀ (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ), 0 < t → t < ε →
      ‖g (EuclideanSpace.snocLast x' t)‖ₑ
        ≤ ∫⁻ s in Ioo 0 ε, ‖D (EuclideanSpace.snocLast x' s)‖ₑ := by
    intro x' t ht0 htε
    have hint : IntervalIntegrable (fun s ↦ D (EuclideanSpace.snocLast x' s)) volume 0 t :=
      (hDc.comp (EuclideanSpace.continuous_snocLast.comp (Continuous.prodMk_right x')))
        |>.intervalIntegrable _ _
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s ↦ g (EuclideanSpace.snocLast x' s)) (fun s _ ↦ hderiv x' s) hint
    have hg0 : g (EuclideanSpace.snocLast x' 0) = 0 :=
      hzero _ (by simp [unitChartCubePos, EuclideanSpace.snocLast_apply_last])
    rw [hg0, sub_zero] at hfund
    rw [← hfund, intervalIntegral.integral_of_le ht0.le]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine (lintegral_mono_set (Ioc_subset_Ioc_right htε.le)).trans ?_
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  -- Fubini on both sides
  have hgm : AEMeasurable fun x ↦ ‖g x‖ₑ := hgc.measurable.enorm.aemeasurable
  have hDm : AEMeasurable fun x ↦ ‖D x‖ₑ := hDc.measurable.enorm.aemeasurable
  have hD : ∀ x, fderiv ℝ g x (EuclideanSpace.single (Fin.last d) 1) = D x := fun x ↦ by
    rw [hDdef]
  simp only [hD]
  rw [lintegral_unitChartCubeStrip hε hgm, lintegral_unitChartCubeStrip hε hDm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x' _
  calc ∫⁻ t in Ioo 0 ε, ‖g (EuclideanSpace.snocLast x' t)‖ₑ
      ≤ ∫⁻ _ in Ioo 0 ε, ∫⁻ s in Ioo 0 ε, ‖D (EuclideanSpace.snocLast x' s)‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hpt x' t ht.1 ht.2
    _ = ENNReal.ofReal ε * ∫⁻ s in Ioo 0 ε, ‖D (EuclideanSpace.snocLast x' s)‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]

end Strip

section Limit

/-- `L^p(ν) ⊆ L^1(ν)` for a finite measure `ν ≤ μ`, quantitatively:
`∫⁻ ‖h‖ₑ ∂ν ≤ ‖h‖_{L^p(μ)} ν(univ)^(1 − 1/p)`. -/
theorem MeasureTheory.lintegral_enorm_le_eLpNorm_mul_of_le {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hν : ν ≤ μ) {p : ℝ≥0∞} (hp : 1 ≤ p) {h : X → ℝ}
    (hh : AEStronglyMeasurable h μ) :
    ∫⁻ x, ‖h x‖ₑ ∂ν ≤ eLpNorm h p μ * ν univ ^ (1 - 1 / p.toReal) := by
  have hh' := hh.mono_measure hν
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (p := 1) hp hh'
  rw [eLpNorm_one_eq_lintegral_enorm hh', ENNReal.toReal_one, div_one] at this
  exact this.trans (mul_le_mul' (eLpNorm_mono_measure _ hν) le_rfl)

/-- The triangle inequality `∫⁻ ‖h₁‖ₑ ≤ ∫⁻ ‖h₁ − h₂‖ₑ + ∫⁻ ‖h₂‖ₑ`. -/
theorem MeasureTheory.lintegral_enorm_le_lintegral_enorm_sub_add {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {h₁ h₂ : X → ℝ} (hm : AEStronglyMeasurable (h₁ - h₂) ν) :
    ∫⁻ x, ‖h₁ x‖ₑ ∂ν ≤ ∫⁻ x, ‖(h₁ - h₂) x‖ₑ ∂ν + ∫⁻ x, ‖h₂ x‖ₑ ∂ν := by
  rw [← lintegral_add_left' hm.enorm]
  refine lintegral_mono fun x ↦ ?_
  calc ‖h₁ x‖ₑ = ‖(h₁ x - h₂ x) + h₂ x‖ₑ := by rw [sub_add_cancel]
    _ ≤ ‖h₁ x - h₂ x‖ₑ + ‖h₂ x‖ₑ := enorm_add_le _ _

/-- **Passing an integral inequality to the limit**: if `∫ |fₙ| ∂ν ≤ c ∫ |gₙ| ∂ν` for every `n`,
`ν ≤ μ` is finite, `1 ≤ p < ∞`, and `fₙ → f`, `gₙ → g` in `L^p(μ)`, then
`∫ |f| ∂ν ≤ c ∫ |g| ∂ν`. -/
theorem MeasureTheory.lintegral_enorm_le_mul_of_tendsto {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hν : ν ≤ μ) [IsFiniteMeasure ν] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {f g : X → ℝ} {fs gs : ℕ → X → ℝ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfs : ∀ n, AEStronglyMeasurable (fs n) μ) (hgs : ∀ n, AEStronglyMeasurable (gs n) μ)
    (hn : ∀ n, ∫⁻ x, ‖fs n x‖ₑ ∂ν ≤ c * ∫⁻ x, ‖gs n x‖ₑ ∂ν)
    (hft : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0))
    (hgt : Tendsto (fun n ↦ eLpNorm (gs n - g) p μ) atTop (𝓝 0)) :
    ∫⁻ x, ‖f x‖ₑ ∂ν ≤ c * ∫⁻ x, ‖g x‖ₑ ∂ν := by
  have hV : ν univ ^ (1 - 1 / p.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by
      have : 1 / p.toReal ≤ 1 := by
        rw [div_le_one (ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp'),
          ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono hp' hp
      linarith) (measure_ne_top ν _)
  have hbound : ∀ n, ∫⁻ x, ‖f x‖ₑ ∂ν
      ≤ eLpNorm (fs n - f) p μ * ν univ ^ (1 - 1 / p.toReal)
        + c * (eLpNorm (gs n - g) p μ * ν univ ^ (1 - 1 / p.toReal) + ∫⁻ x, ‖g x‖ₑ ∂ν) := by
    intro n
    calc ∫⁻ x, ‖f x‖ₑ ∂ν
        ≤ ∫⁻ x, ‖(f - fs n) x‖ₑ ∂ν + ∫⁻ x, ‖fs n x‖ₑ ∂ν :=
          lintegral_enorm_le_lintegral_enorm_sub_add ((hf.sub (hfs n)).mono_measure hν)
      _ ≤ ∫⁻ x, ‖(f - fs n) x‖ₑ ∂ν + c * ∫⁻ x, ‖gs n x‖ₑ ∂ν := add_le_add le_rfl (hn n)
      _ ≤ ∫⁻ x, ‖(f - fs n) x‖ₑ ∂ν
          + c * (∫⁻ x, ‖(gs n - g) x‖ₑ ∂ν + ∫⁻ x, ‖g x‖ₑ ∂ν) :=
          add_le_add le_rfl (mul_le_mul' le_rfl (lintegral_enorm_le_lintegral_enorm_sub_add
            (((hgs n).sub hg).mono_measure hν)))
      _ ≤ eLpNorm (f - fs n) p μ * ν univ ^ (1 - 1 / p.toReal)
          + c * (eLpNorm (gs n - g) p μ * ν univ ^ (1 - 1 / p.toReal) + ∫⁻ x, ‖g x‖ₑ ∂ν) :=
          add_le_add (lintegral_enorm_le_eLpNorm_mul_of_le hν hp (hf.sub (hfs n)))
            (mul_le_mul' le_rfl (add_le_add
              (lintegral_enorm_le_eLpNorm_mul_of_le hν hp ((hgs n).sub hg)) le_rfl))
      _ = _ := by rw [eLpNorm_sub_comm]
  have h1 := ENNReal.Tendsto.mul_const hft (Or.inr hV)
  have h2 := ENNReal.Tendsto.mul_const hgt (Or.inr hV)
  have h3 := h1.add (ENNReal.Tendsto.const_mul (h2.add (tendsto_const_nhds
    (x := ∫⁻ x, ‖g x‖ₑ ∂ν))) (Or.inr hc))
  simp only [zero_mul, zero_add] at h3
  exact ge_of_tendsto h3 (Eventually.of_forall hbound)

end Limit

section StripTyped

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open SobolevMultiIndex

/-- The strip has finite measure. -/
theorem volume_unitChartCubeStrip_ne_top {ε : ℝ} :
    volume (unitChartCubeStrip d ε) ≠ ⊤ :=
  (measure_mono (unitChartCubeStrip_subset.trans (unitChartCubePos_subset.trans
    unitChartCube_subset_ball))).trans_lt measure_ball_lt_top |>.ne

omit [Fact (1 ≤ p)] in
/-- The strip inequality for an element of `W^{1,p}(Q_+)` whose function is a test function. -/
theorem SobolevEuclidean.lintegral_unitChartCubeStrip_le_of_fn_ae_eq_testFunction {ε : ℝ}
    (hε : ε ≤ 1) {w : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    {φ : 𝓓(unitChartCubePosOpens d, ℝ)} (hφ : fn w =ᵐ[volume.restrict (unitChartCubePos d)] φ) :
    ∫⁻ x in unitChartCubeStrip d ε, ‖fn w x‖ₑ
      ≤ ENNReal.ofReal ε * ∫⁻ x in unitChartCubeStrip d ε,
        ‖weakDeriv w (MultiIndexLE.single (Fin.last d)) x‖ₑ := by
  have hSQ : volume.restrict (unitChartCubeStrip d ε)
      ≤ volume.restrict (unitChartCubePos d) :=
    Measure.restrict_mono unitChartCubeStrip_subset le_rfl
  have h1 : ∫⁻ x in unitChartCubeStrip d ε, ‖fn w x‖ₑ = ∫⁻ x in unitChartCubeStrip d ε, ‖φ x‖ₑ :=
    lintegral_congr_ae ((hφ.filter_mono (ae_mono hSQ)).mono fun x hx ↦ by simp only [hx])
  have h2 : ∫⁻ x in unitChartCubeStrip d ε, ‖weakDeriv w (MultiIndexLE.single (Fin.last d)) x‖ₑ
      = ∫⁻ x in unitChartCubeStrip d ε, ‖fderiv ℝ φ x (EuclideanSpace.single (Fin.last d) 1)‖ₑ := by
    have := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hφ (Fin.last d)
    rw [EuclideanSpace.basisFun_toBasis_last] at this
    exact lintegral_congr_ae ((this.filter_mono (ae_mono hSQ)).mono fun x hx ↦ by simp only [hx])
  rw [h1, h2]
  exact lintegral_unitChartCubeStrip_le_of_contDiff hε (φ.contDiff.of_le (by simp))
    φ.tsupport_subset

/-- **The strip inequality on `W_0^{1,p}(Q_+)`**: for `u ∈ W_0^{1,p}(Q_+)`, `1 ≤ p < ∞`, and
`ε ≤ 1`, `∫_{x ∈ Q_+, x_N < ε} |u| ≤ ε ∫_{x ∈ Q_+, x_N < ε} |∂_N u|`. The inequality for test
functions (`lintegral_unitChartCubeStrip_le_of_contDiff`) passes to the limit in `W^{1,p}(Q_+)`,
both sides being continuous for the `L^p` convergence on the strip, which has finite measure. -/
theorem SobolevEuclideanZero.lintegral_unitChartCubeStrip_le (hp' : p ≠ ⊤) {ε : ℝ} (hε : ε ≤ 1)
    {u : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d)) :
    ∫⁻ x in unitChartCubeStrip d ε, ‖fn u x‖ₑ
      ≤ ENNReal.ofReal ε * ∫⁻ x in unitChartCubeStrip d ε,
        ‖weakDeriv u (MultiIndexLE.single (Fin.last d)) x‖ₑ := by
  obtain ⟨w, φ, hφ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hu
  have hSQ : volume.restrict (unitChartCubeStrip d ε)
      ≤ volume.restrict (unitChartCubePos d) :=
    Measure.restrict_mono unitChartCubeStrip_subset le_rfl
  have : IsFiniteMeasure (volume.restrict (unitChartCubeStrip d ε)) :=
    isFiniteMeasure_restrict.2 volume_unitChartCubeStrip_ne_top
  exact lintegral_enorm_le_mul_of_tendsto hSQ Fact.out hp' ENNReal.ofReal_ne_top
    (memLp u).aestronglyMeasurable (Lp.aestronglyMeasurable _)
    (fun n ↦ (memLp (w n)).aestronglyMeasurable) (fun n ↦ Lp.aestronglyMeasurable _)
    (fun n ↦ SobolevEuclidean.lintegral_unitChartCubeStrip_le_of_fn_ae_eq_testFunction hε (hφ n))
    (tendsto_eLpNorm_fn_sub hw) (tendsto_eLpNorm_weakDeriv_sub hw _)

end StripTyped

section StripLimit

variable {d : ℕ}

open EuclideanSpace

/-- The measure of the strip: `|{x ∈ Q_+ : x_N < ε}| = |B'(0, 1)| ε` for `ε ≤ 1`. -/
theorem volume_unitChartCubeStrip {ε : ℝ} (hε : ε ≤ 1) :
    volume (unitChartCubeStrip d ε)
      = volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ENNReal.ofReal ε := by
  rw [← setLIntegral_one, lintegral_unitChartCubeStrip hε aemeasurable_const]
  simp only [setLIntegral_const, one_mul, Real.volume_Ioo, sub_zero]
  rw [mul_comm]

/-- **The strip integrals of an `L^1(Q_+)` function tend to `0`** along `ε_n → 0`. -/
theorem tendsto_lintegral_unitChartCubeStrip {g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hg : ∫⁻ x in unitChartCubePos d, ‖g x‖ₑ ≠ ⊤) {ε : ℕ → ℝ} (hε : ∀ n, ε n ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫⁻ x in unitChartCubeStrip d (ε n), ‖g x‖ₑ) atTop (𝓝 0) := by
  have heq : ∀ n, ∫⁻ x in unitChartCubeStrip d (ε n), ‖g x‖ₑ
      = ∫⁻ x in unitChartCubeStrip d (ε n), ‖g x‖ₑ ∂(volume.restrict (unitChartCubePos d)) := by
    intro n
    rw [Measure.restrict_restrict measurableSet_unitChartCubeStrip,
      inter_eq_self_of_subset_left unitChartCubeStrip_subset]
  refine (tendsto_congr heq).2 (tendsto_setLIntegral_zero hg ?_)
  have h : ∀ n, (volume.restrict (unitChartCubePos d) ∘ fun n ↦ unitChartCubeStrip d (ε n)) n
      = volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ENNReal.ofReal (ε n) := fun n ↦ by
    simp only [Function.comp_apply]
    rw [Measure.restrict_apply measurableSet_unitChartCubeStrip,
      inter_eq_self_of_subset_left unitChartCubeStrip_subset, volume_unitChartCubeStrip (hε n)]
  refine (tendsto_congr h).2 ?_
  have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hε0)
    (a := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) (Or.inr measure_ball_lt_top.ne)
  simpa using this

/-- **A lower bound for the strip integral** near a point of the equator: if `c ≤ |v|` on the
cylinder `B'(x₀', r) × (0, ε)`, contained in the strip when `r + ‖x₀'‖ ≤ 1` and `ε ≤ 1`, then
`c ε |B'(x₀', r)| ≤ ∫_{x ∈ Q_+, x_N < ε} |v|`. -/
theorem le_lintegral_unitChartCubeStrip {ε : ℝ} (hε : ε ≤ 1)
    {v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hv : AEMeasurable v)
    {x₀' : EuclideanSpace ℝ (Fin d)} {r c : ℝ} (hr1 : r + ‖x₀'‖ ≤ 1)
    (hlow : ∀ x' ∈ ball x₀' r, ∀ t ∈ Ioo 0 ε, c ≤ |v (snocLast x' t)|) :
    ENNReal.ofReal c * (ENNReal.ofReal ε * volume (ball x₀' r))
      ≤ ∫⁻ x in unitChartCubeStrip d ε, ‖v x‖ₑ := by
  rw [lintegral_unitChartCubeStrip hε hv.enorm]
  calc ENNReal.ofReal c * (ENNReal.ofReal ε * volume (ball x₀' r))
      = ∫⁻ _ in ball x₀' r, ENNReal.ofReal c * ENNReal.ofReal ε := by
        rw [setLIntegral_const, mul_assoc]
    _ ≤ ∫⁻ x' in ball x₀' r, ∫⁻ t in Ioo 0 ε, ‖v (snocLast x' t)‖ₑ := by
        refine setLIntegral_mono' measurableSet_ball fun x' hx' ↦ ?_
        calc ENNReal.ofReal c * ENNReal.ofReal ε
            = ∫⁻ _ in Ioo 0 ε, ENNReal.ofReal c := by
              rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
          _ ≤ ∫⁻ t in Ioo 0 ε, ‖v (snocLast x' t)‖ₑ := by
              refine setLIntegral_mono' measurableSet_Ioo fun t ht ↦ ?_
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_ofReal (hlow x' hx' t ht)
    _ ≤ ∫⁻ x' in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ t in Ioo 0 ε,
          ‖v (snocLast x' t)‖ₑ :=
        lintegral_mono_set (ball_subset_ball' (by rwa [dist_zero_right]))

end StripLimit

section Thm917

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open EuclideanSpace SobolevMultiIndex

/-- **Theorem 9.17, (ii) ⇒ (i), the `Q_+` computation**: if `u ∈ W_0^{1,p}(Q_+)`, `1 ≤ p < ∞`,
has a representative `ũ` continuous on `closure Q_+`, then `ũ = 0` on the equator `Q_0`
([brezis2011functional] Theorem 9.17, (ii) ⇒ (i)). The strip inequality
`∫_{x_N < ε} |u| ≤ ε ∫_{x_N < ε} |∂_N u|` (`SobolevEuclideanZero.lintegral_unitChartCubeStrip_le`)
is tested against a point `x₀ ∈ Q_0` with `ũ x₀ ≠ 0`: by continuity `|ũ| ≥ |ũ x₀| / 2` on a
cylinder `B'(x₀', r) × (0, ε)`, so the left side is at least `(|ũ x₀| / 2) ε |B'(x₀', r)|`, while
`∫_{x_N < ε} |∂_N u| → 0` as `ε → 0` (`∂_N u ∈ L^1(Q_+)`), a contradiction. -/
theorem SobolevEuclideanZero.eqOn_unitChartCubeZero_of_continuousOn_closure (hp' : p ≠ ⊤)
    {u : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d))
    {ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hc : ContinuousOn ũ (closure (unitChartCubePos d)))
    (hũ : fn u =ᵐ[volume.restrict (unitChartCubePos d)] ũ) :
    EqOn ũ 0 (unitChartCubeZero d) := by
  intro x₀ hx₀
  by_contra hne
  rw [Pi.zero_apply] at hne
  -- the constant `c = |ũ x₀| / 2` and the radius `r`
  have hc0 : 0 < |ũ x₀| / 2 := by positivity
  have hx₀c : x₀ ∈ closure (unitChartCubePos d) :=
    frontier_subset_closure (unitChartCubeZero_subset_frontier_unitChartCubePos hx₀)
  have hx₀' : snocLast (init x₀) 0 = x₀ := by
    conv_rhs => rw [← snocLast_init_last x₀]
    rw [hx₀.2]
  have hG : ContinuousWithinAt (fun q : EuclideanSpace ℝ (Fin d) × ℝ ↦ ũ (snocLast q.1 q.2))
      ((fun q : EuclideanSpace ℝ (Fin d) × ℝ ↦ snocLast q.1 q.2) ⁻¹' closure (unitChartCubePos d))
      (init x₀, 0) := by
    refine ContinuousWithinAt.comp (f := fun q : EuclideanSpace ℝ (Fin d) × ℝ ↦ snocLast q.1 q.2)
      ?_ continuous_snocLast.continuousWithinAt (mapsTo_preimage _ _)
    simpa only [hx₀'] using hc x₀ hx₀c
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 hG _ hc0
  have hx₀1 : ‖init x₀‖ < 1 := hx₀.1.1
  obtain ⟨r, hrδ, hr1, hr⟩ : ∃ r : ℝ, r ≤ δ / 2 ∧ r + ‖init x₀‖ ≤ 1 ∧ 0 < r :=
    ⟨min (δ / 2) (1 - ‖init x₀‖), min_le_left _ _,
      by linarith [min_le_right (δ / 2) (1 - ‖init x₀‖)], lt_min (by positivity) (by linarith)⟩
  -- the lower bound on the cylinder
  have hlow : ∀ x' ∈ ball (init x₀) r, ∀ t ∈ Ioo 0 r,
      |ũ x₀| / 2 ≤ |ũ (snocLast x' t)| ∧ snocLast x' t ∈ unitChartCubePos d := by
    intro x' hx' t ht
    have hmem : snocLast x' t ∈ unitChartCubePos d := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [init_snocLast]
        calc ‖x'‖ = ‖x' - init x₀ + init x₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖x' - init x₀‖ + ‖init x₀‖ := norm_add_le _ _
          _ < r + ‖init x₀‖ := by
              have := mem_ball_iff_norm.1 hx'
              linarith
          _ ≤ 1 := hr1
      · rw [snocLast_apply_last, abs_of_pos ht.1]
        linarith [ht.2, norm_nonneg (init x₀)]
      · rw [snocLast_apply_last]; exact ht.1
    refine ⟨?_, hmem⟩
    have hdist : dist (x', t) (init x₀, 0) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨(mem_ball.1 hx').trans_le (by linarith), ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      linarith [ht.2]
    have := hδ' (x := (x', t)) (subset_closure hmem) hdist
    rw [hx₀', Real.dist_eq] at this
    have h2 := abs_sub_abs_le_abs_sub (ũ x₀) (ũ (snocLast x' t))
    rw [abs_sub_comm] at h2
    linarith
  -- the measurable representative `v`
  obtain ⟨v, hvdef⟩ : ∃ v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      v = (closure (unitChartCubePos d)).indicator ũ := ⟨_, rfl⟩
  have hvm : AEMeasurable v := by
    rw [hvdef]
    exact (aemeasurable_indicator_iff isClosed_closure.measurableSet).2
      (hc.aemeasurable isClosed_closure.measurableSet)
  have hveq : ∀ x ∈ unitChartCubePos d, v x = ũ x := fun x hx ↦ by
    rw [hvdef, Set.indicator_of_mem (subset_closure hx)]
  -- the strip inequality along `ε n = r / (n + 1)`
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun n : ℕ ↦ r / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hε1 : ∀ n, ε n ≤ 1 := fun n ↦ by
    rw [hεdef]
    exact (div_le_self hr.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])).trans
      (by linarith [norm_nonneg (init x₀)])
  have hεr : ∀ n, ε n ≤ r := fun n ↦ by
    rw [hεdef]
    exact div_le_self hr.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hε0 : ∀ n, 0 < ε n := fun n ↦ by
    rw [hεdef]
    positivity
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [hεdef]
    ring
  have hSQ : ∀ n, volume.restrict (unitChartCubeStrip d (ε n))
      ≤ volume.restrict (unitChartCubePos d) := fun n ↦
    Measure.restrict_mono unitChartCubeStrip_subset le_rfl
  have hstrip : ∀ n, ENNReal.ofReal (|ũ x₀| / 2) * volume (ball (init x₀) r)
      ≤ ∫⁻ x in unitChartCubeStrip d (ε n),
        ‖weakDeriv u (MultiIndexLE.single (Fin.last d)) x‖ₑ := by
    intro n
    have h1 : ∫⁻ x in unitChartCubeStrip d (ε n), ‖fn u x‖ₑ
        = ∫⁻ x in unitChartCubeStrip d (ε n), ‖v x‖ₑ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hũ.filter_mono (ae_mono (hSQ n)),
        ae_restrict_mem measurableSet_unitChartCubeStrip] with x hx hxS
      rw [hx, hveq x (unitChartCubeStrip_subset hxS)]
    have h2 := le_lintegral_unitChartCubeStrip (hε1 n) hvm hr1 (x₀' := init x₀) (c := |ũ x₀| / 2)
      (fun x' hx' t ht ↦ by
        have := hlow x' hx' t ⟨ht.1, ht.2.trans_le (hεr n)⟩
        rw [hveq _ this.2]
        exact this.1)
    have h3 := SobolevEuclideanZero.lintegral_unitChartCubeStrip_le hp' (hε1 n) hu
    rw [h1] at h3
    have h4 := h2.trans h3
    rw [mul_left_comm] at h4
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (hε0 n)).ne'
      ENNReal.ofReal_ne_top).1 h4
  -- the right side tends to `0`
  have hfin : IsFiniteMeasure (volume.restrict (unitChartCubePos d)) :=
    isFiniteMeasure_restrict.2 ((measure_mono (unitChartCubePos_subset.trans
      unitChartCube_subset_ball)).trans_lt measure_ball_lt_top).ne
  have hL1 : ∫⁻ x in unitChartCubePos d, ‖weakDeriv u (MultiIndexLE.single (Fin.last d)) x‖ₑ
      ≠ ⊤ :=
    (hasFiniteIntegral_iff_enorm.1 (memLp_one_iff_integrable.1
      ((Lp.memLp _).mono_exponent Fact.out)).hasFiniteIntegral).ne
  have hlim := tendsto_lintegral_unitChartCubeStrip hL1 hε1 hεt
  have h0 := ge_of_tendsto hlim (Eventually.of_forall hstrip)
  rw [nonpos_iff_eq_zero, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact (ENNReal.ofReal_pos.2 hc0).ne' h0
  · exact (Metric.measure_ball_pos volume (init x₀) hr).ne' h0

end Thm917

/-! ### Theorem 9.17, (ii) ⇒ (i): the chart reduction -/

section Thm917Chart

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

namespace ContDiffChart

variable (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- The chart sends `closure Q_+` into `closure Ω`. -/
theorem mapsTo_closure_unitChartCubePos :
    MapsTo c.toFun (closure (unitChartCubePos d)) (closure (Ω : Set _)) := by
  have h1 : c.toFun '' closure (unitChartCubePos d) ⊆ closure (c.toFun '' unitChartCubePos d) :=
    (c.continuousOn.mono (closure_mono unitChartCubePos_subset)).image_closure
  rw [c.image_pos] at h1
  exact fun y hy ↦ closure_mono inter_subset_right (h1 (mem_image_of_mem _ hy))

/-- **The chart piece of Theorem 9.17, (ii) ⇒ (i)**: for a chart `c` of `Ω`, `θ` smooth with
compact support in `c.U`, `u ∈ W_0^{1,p}(Ω)` with a representative `ũ` continuous on `closure Ω`,
and `V ∈ W^{1,p}(U ∩ Ω)` with function `u θ`, the transfer `V ∘ H` lies in `W_0^{1,p}(Q_+)`
(`SobolevMultiIndexZero.mul_contDiff_mem`, `SobolevMultiIndexZero.compDiffeoL_mem`) and has the
representative `(ũ θ) ∘ H`, continuous on `closure Q_+`; the `Q_+` computation
(`SobolevEuclideanZero.eqOn_unitChartCubeZero_of_continuousOn_closure`) gives `(ũ θ) ∘ H = 0` on
the equator `Q_0`. -/
theorem eqOn_unitChartCubeZero_aux (hp' : p ≠ ⊤) {M : ℝ}
    (hH : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCubePosOpens d : Set _)
      (c.opensInter : Set _) M)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : SobolevEuclidean (d + 1) 1 p Ω}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p Ω) {ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hũ : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {V : SobolevEuclidean (d + 1) 1 p c.opensInter}
    (hV : fn V =ᵐ[volume.restrict (c.opensInter : Set _)] fun x ↦ fn u x * θ x) :
    EqOn (fun y ↦ ũ (c.toFun y) * θ (c.toFun y)) 0 (unitChartCubeZero d) := by
  have hle : volume.restrict (c.opensInter : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    Measure.restrict_mono c.opensInter_le le_rfl
  -- `V ∈ W_0^{1,p}(U ∩ Ω)`
  have hVZ : V ∈ SobolevEuclideanZero (d + 1) 1 p c.opensInter :=
    SobolevMultiIndexZero.mul_contDiff_mem c.opensInter_le hθ hθc
      (fun x hx ↦ ⟨hθU hx.1, hx.2⟩) hu hV
  -- the transfer `V ∘ H ∈ W_0^{1,p}(Q_+)`
  have hWZ := SobolevMultiIndexZero.compDiffeoL_mem hp' hH hVZ
  -- its continuous representative `(ũ θ) ∘ H`
  have hH1 : ContinuousOn c.toFun (closure (unitChartCubePos d)) :=
    c.continuousOn.mono (closure_mono unitChartCubePos_subset)
  have hcont : ContinuousOn (fun y ↦ ũ (c.toFun y) * θ (c.toFun y))
      (closure (unitChartCubePos d)) :=
    (hc.comp hH1 c.mapsTo_closure_unitChartCubePos).mul (hθ.continuous.comp_continuousOn hH1)
  have hW : fn (compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume hH V)
      =ᵐ[volume.restrict (unitChartCubePos d)] fun y ↦ ũ (c.toFun y) * θ (c.toFun y) := by
    have h1 := fn_compDiffeoL hH V
    have h2 := hH.ae_comp_restrict (P := fun x ↦ fn V x = fn u x * θ x) hV
    have h3 := hH.ae_comp_restrict (P := fun x ↦ fn u x = ũ x) (hũ.filter_mono (ae_mono hle))
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    rw [hy1, hy2, hy3]
  exact SobolevEuclideanZero.eqOn_unitChartCubeZero_of_continuousOn_closure hp' hWZ hcont hW

end ContDiffChart

/-- **Theorem 9.17, (ii) ⇒ (i)** for a `C^1` chart domain, `1 ≤ p < ∞`: if
`IsContDiffChartDomain 1 Ω`, `u ∈ W_0^{1,p}(Ω)` and `ũ` is a representative of `u` continuous on
`closure Ω`, then `ũ = 0` on `frontier Ω` ([brezis2011functional] Theorem 9.17, (ii) ⇒ (i):
"using local charts this is reduced to" the `Q_+` computation). For `x₀ ∈ frontier Ω` with chart
`c` and `θ` smooth with compact support in `c.U`, `θ = 1` near `x₀`, the function `u θ` is in
`W_0^{1,p}(U ∩ Ω)` and transfers along the chart to `W_0^{1,p}(Q_+)` with the continuous
representative `(ũ θ) ∘ H` (`ContDiffChart.eqOn_unitChartCubeZero_aux`), which vanishes on the
equator; `x₀ = H(y₀)` with `y₀ ∈ Q_0`, so `ũ x₀ = ũ x₀ θ x₀ = 0`. Together with
`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`, this is Theorem 9.17. -/
theorem SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p Ω)
    {ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hũ : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    EqOn ũ 0 (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  intro x₀ hx₀
  obtain ⟨c, hx₀U⟩ := hΩ.exists_chart hx₀
  -- the cut-off `θ`, equal to `1` near `x₀`, with compact support in `c.U`
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 c.isOpen_U x₀ hx₀U
  obtain ⟨θ, hθ, hθ1, hθU, -⟩ := (isCompact_closedBall x₀ (r / 2)).exists_contDiff_eqOn_one
    c.isOpen_U ((closedBall_subset_ball (by linarith)).trans hrU)
  have hθc : HasCompactSupport θ :=
    c.isCompact_closure_U.of_isClosed_subset (isClosed_tsupport _) (hθU.trans subset_closure)
  obtain ⟨M₀, hM₀⟩ := hθc.exists_bound_of_continuous hθ.continuous
  obtain ⟨M₁, hM₁⟩ := (hθc.fderiv ℝ).exists_bound_of_continuous (hθ.continuous_fderiv (by simp))
  have hM : ∀ x, |θ x| ≤ M₀ + M₁ ∧ ‖fderiv ℝ θ x‖ ≤ M₀ + M₁ := fun x ↦ by
    have h0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ x)
    have h1 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ x)
    exact ⟨(Real.norm_eq_abs _).symm.trans_le ((hM₀ x).trans (by linarith)),
      (hM₁ x).trans (by linarith)⟩
  -- `V ∈ W^{1,p}(U ∩ Ω)` with function `u θ`
  obtain ⟨V, hV⟩ := ((memSobolevMultiIndex (restrictL ℝ
    (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume c.opensInter_le u)).contDiff_mul
    Fact.out hθ hM).exists_sobolevMultiIndex
  have hV' : fn V =ᵐ[volume.restrict (c.opensInter : Set _)] fun x ↦ fn u x * θ x := by
    filter_upwards [hV, fn_restrictL c.opensInter_le u] with x h1 h2
    rw [h1, h2, mul_comm]
  -- the chart piece
  obtain ⟨M, hH⟩ := c.isDiffeoOnWithBoundedJacobian_pos le_rfl Ω.isOpen
  have h0 := c.eqOn_unitChartCubeZero_aux hp' hH hθ hθc hθU hu hũ hc hV'
    ((c.invFun_mem_zero_iff hx₀U).2 hx₀)
  simp only [Pi.zero_apply, c.toFun_invFun hx₀U] at h0 ⊢
  rwa [hθ1 (mem_closedBall_self (by positivity)), Pi.one_apply, mul_one] at h0

end Thm917Chart

/-! ### Proposition 9.20: the dual `W^{-1,p'}(Ω)` -/

section Dual

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
  refine ⟨fun i ↦ e.symm (Φ.comp (PiLp.singleL p (X := fun _ : κ ↦ Lp ℝ p ν) i)),
    fun x ↦ ?_, fun i ↦ ?_⟩
  · rw [PiLp.strongDual_apply_eq_sum Φ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← he, LinearIsometryEquiv.apply_symm_apply]
  · rw [LinearIsometryEquiv.norm_map]
    exact PiLp.norm_strongDual_comp_singleL_le Φ i

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

/-! #### The triple `W_0^{1,p}(Ω) ⊂ L²(Ω) ⊂ W^{-1,p'}(Ω)` along a bounded inclusion into `L²` -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The inclusion `L²(Ω) ⊂ W^{-1,p'}(Ω)` along a bounded inclusion `ι : W_0^{1,p}(Ω) → L²(Ω)`**:
`f ↦ (v ↦ ⟪f, ι v⟫_{L²(Ω)})`, the transpose of `ι` composed with the self-duality of `L²(Ω)`. The
inclusion `ι` is a parameter: it is `SobolevMultiIndexZero.fnL` at `p = 2`
(`SobolevEuclideanZero.toDualL2_eq_toDualOfL2`) and, for `2N/(N+2) ≤ p`, the bounded inclusion of
Remark 20 (`SobolevEuclideanZero.isContinuousEmbedding_toLp` of
`Numlib/Analysis/Sobolev/EmbeddingDomain.lean`, which this file does not import). -/
def toDualOfL2 (ι : SobolevEuclideanZero N 1 p Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      StrongDual ℝ (SobolevEuclideanZero N 1 p Ω) :=
  ((ContinuousLinearMap.compL ℝ (SobolevEuclideanZero N 1 p Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ℝ).flip ι).comp (innerSL ℝ)

/-- `toDualOfL2 ι f v = ⟪f, ι v⟫_{L²(Ω)}`. -/
theorem toDualOfL2_apply_inner (ι : SobolevEuclideanZero N 1 p Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 p Ω) : toDualOfL2 ι f v = ⟪f, ι v⟫_ℝ :=
  rfl

/-- `SobolevEuclideanZero.toDualL2` is `toDualOfL2` along the inclusion `H^1_0(Ω) ⊂ L²(Ω)`. -/
theorem toDualL2_eq_toDualOfL2 :
    toDualL2 N Ω = toDualOfL2
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume) :=
  rfl

variable {ι : SobolevEuclideanZero N 1 p Ω →L[ℝ]
  Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- `toDualOfL2 ι f v = ∫_Ω f v` when `ι v` is the function of `v`. -/
theorem toDualOfL2_apply
    (hι : ∀ v : SobolevEuclideanZero N 1 p Ω, (ι v : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 p Ω) :
    toDualOfL2 ι f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      f x * SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω) x := by
  rw [toDualOfL2_apply_inner, L2.inner_eq_integral_mul]
  exact integral_congr_ae (Filter.EventuallyEq.rfl.mul (hι v))

/-- **A bounded map `W_0^{1,p}(Ω) → L²(Ω)` sending each element to its function is injective**:
the function determines the element (`SobolevMultiIndexZero.fnL_injective`). -/
theorem injective_of_forall_ae_eq
    (hι : ∀ v : SobolevEuclideanZero N 1 p Ω, (ι v : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω)) :
    Function.Injective ι := fun u v huv ↦ by
  refine SobolevMultiIndexZero.fnL_injective (Lp.ext ?_)
  rw [SobolevMultiIndexZero.fnL_apply, SobolevMultiIndexZero.fnL_apply]
  exact (hι u).symm.trans ((Lp.ext_iff.1 huv).trans (hι v))

/-- **A bounded map `W_0^{1,p}(Ω) → L²(Ω)` sending each element to its function has dense
range**: its range contains the test functions, which are dense in `L²(Ω)`
(`MeasureTheory.Lp.dense_contDiff_tsupport_subset`). -/
theorem denseRange_of_forall_ae_eq
    (hι : ∀ v : SobolevEuclideanZero N 1 p Ω, (ι v : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω)) :
    DenseRange ι := by
  refine (Lp.dense_contDiff_tsupport_subset (F := ℝ) (μ := volume) (p := 2) Ω.isOpen
    ENNReal.ofNat_ne_top).mono ?_
  rintro f ⟨g, hfg, hgc, hgs, hgΩ⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(Ω, ℝ), (φ : EuclideanSpace ℝ (Fin N) → ℝ) = g :=
    ⟨⟨g, hgs, hgc, hgΩ⟩, rfl⟩
  obtain ⟨u, hu, hφu⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := p) (μ := volume)
  refine ⟨⟨u, SobolevMultiIndexZero.testFunctions_le hu⟩, Lp.ext ((hι _).trans ?_)⟩
  refine hφu.trans ?_
  rw [hφ]
  exact hfg.symm

/-- **`L²(Ω) ⊂ W^{-1,p'}(Ω)` is injective**, along any bounded inclusion `ι` sending each element
of `W_0^{1,p}(Ω)` to its function: a function of `L²(Ω)` whose integral against every test
function vanishes is zero (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem toDualOfL2_injective
    (hι : ∀ v : SobolevEuclideanZero N 1 p Ω, (ι v : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω)) :
    Function.Injective (toDualOfL2 ι) := by
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
      (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := p) (μ := volume)
    have h1 := DFunLike.congr_fun hf ⟨u, SobolevMultiIndexZero.testFunctions_le hu⟩
    rw [toDualOfL2_apply hι, zero_apply] at h1
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgΩ h), zero_smul], ← h1, ← hφ]
    refine integral_congr_ae (hφu.mono fun x hx ↦ ?_)
    simp only [smul_eq_mul, mul_comm, hx]

/-- **`L²(Ω) ⊂ W^{-1,p'}(Ω)` has dense range when `W_0^{1,p}(Ω)` is reflexive** (`1 < p < ∞`),
along any bounded inclusion `ι` sending each element of `W_0^{1,p}(Ω)` to its function: the
range separates the points, since `⟪f, ι v⟫ = 0` for all `f ∈ L²(Ω)` gives, at `f = ι v`,
`ι v = 0`, hence `v = 0` (`denseRange_of_forall_apply_eq_zero`). -/
theorem denseRange_toDualOfL2 [NormedSpace.IsReflexive ℝ (SobolevEuclideanZero N 1 p Ω)]
    (hι : ∀ v : SobolevEuclideanZero N 1 p Ω, (ι v : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω)) :
    DenseRange (toDualOfL2 ι) :=
  denseRange_of_forall_apply_eq_zero _ fun v hv ↦ by
    have h := hv (ι v)
    rw [toDualOfL2_apply_inner, real_inner_self_eq_norm_sq] at h
    exact injective_of_forall_ae_eq hι
      ((norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)).trans (map_zero _).symm)

/-- **The Gelfand triple `W_0^{1,p}(Ω) ⊂ L²(Ω) ⊂ W^{-1,p'}(Ω)`, for `1 < p < ∞`, along a bounded
inclusion `ι : W_0^{1,p}(Ω) → L²(Ω)` sending each element to its function**
([brezis2011functional] §9.4, "The Dual Space of `W_0^{1,p}(Ω)`", Notation: "if `Ω` is bounded
then `W_0^{1,p}(Ω) ⊂ L²(Ω) ⊂ W^{-1,p'}(Ω)` if `2N/(N+2) ≤ p < ∞`, with continuous and dense
injections; if `Ω` is not bounded, the same holds for `2N/(N+2) ≤ p ≤ 2`"): `ι` and
`SobolevEuclideanZero.toDualOfL2 ι`, `f ↦ (v ↦ ∫_Ω f v)`, are injective with dense range. The
inclusion `ι` is supplied by Remark 20 (`SobolevEuclideanZero.isContinuousEmbedding_toLp` at
`q = 2`, which is where the condition `2N/(N+2) ≤ p` enters, together with `L^p(Ω) ⊂ L²(Ω)` on
a bounded `Ω` for `p > 2`); the density of the second inclusion uses the reflexivity of
`W_0^{1,p}(Ω)` and **fails at `p = 1`** (allowed by the book's range for `N ≤ 2`): `W_0^{1,1}(Ω)`
contains a complemented copy of `ℓ¹`, so its dual contains `ℓ^∞` and is not separable, while the
range of a bounded map from the separable `L²(Ω)` is. -/
theorem gelfandTriple_of_forall_ae_eq (hp : 1 < p) (hp' : p ≠ ⊤)
    (hι : ∀ v : SobolevEuclideanZero N 1 p Ω, (ι v : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω)) :
    Function.Injective ι ∧ DenseRange ι ∧
      Function.Injective (toDualOfL2 ι) ∧ DenseRange (toDualOfL2 ι) := by
  have : Fact (1 < p) := ⟨hp⟩
  have : Fact (p ≠ (⊤ : ℝ≥0∞)) := ⟨hp'⟩
  exact ⟨injective_of_forall_ae_eq hι, denseRange_of_forall_ae_eq hι, toDualOfL2_injective hι,
    denseRange_toDualOfL2 hι⟩

end SobolevEuclideanZero

end GelfandTriple

/-! ### Remark 17, the punctured space: the capacity of a point

For `N ≥ 2` and `1 ≤ p ≤ N`, `W_0^{1,p}(ℝ^N ∖ {0}) = W^{1,p}(ℝ^N ∖ {0})`. The cut-off near `0`
is the average `η_n x = (n+1)⁻¹ ∑_{k ≤ n} η (3^k x)` of contractions of one cut-off `η`: the
gradients of the summands live on disjoint shells, so `‖∇η_n‖_{L^N}^N ≤ C (n+1)^{1−N} → 0`, and
Hölder's inequality gives `‖∇η_n‖_{L^p} → 0` for every `p ≤ N` — one construction for `p < N`
and for the endpoint `p = N`, with no radial integration. -/

section PointCutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The averaged cut-off at the origin**: for a cut-off `η` equal to `1` on `closedBall 0 1`
and supported in `ball 0 2`, the average `η_n x = (n + 1)⁻¹ ∑_{k ≤ n} η (3^k x)` of its
contractions. It is `1` on `closedBall 0 3^{-n}`, vanishes for `‖x‖ ≥ 2`, tends to `0` at every
`x ≠ 0`, and — the point of the construction — the gradients `∇η (3^k x)` of the summands have
disjoint supports (the shells `3^{-k} ≤ ‖x‖ < 2 · 3^{-k}`), so that `‖∇η_n‖_{L^d}^d ≤ C (n+1)^{1-d}`
in dimension `d`: the capacity of a point is zero in `W^{1,p}` for `p ≤ d`. -/
def pointCutoff (η : E → ℝ) (n : ℕ) (x : E) : ℝ :=
  ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), η ((3 : ℝ) ^ k • x)

variable {η : E → ℝ}

/-- The averaged cut-off is smooth. -/
theorem contDiff_pointCutoff (hη : ContDiff ℝ ∞ η) (n : ℕ) : ContDiff ℝ ∞ (pointCutoff η n) :=
  contDiff_const.mul (ContDiff.sum fun _ _ ↦ hη.comp (contDiff_id.const_smul _))

/-- The averaged cut-off takes its values in `[0, 1]`. -/
theorem pointCutoff_mem_Icc (hη01 : ∀ x, η x ∈ Icc (0 : ℝ) 1) (n : ℕ) (x : E) :
    pointCutoff η n x ∈ Icc (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨mul_nonneg (inv_pos.2 hpos).le (Finset.sum_nonneg fun k _ ↦ (hη01 _).1), ?_⟩
  rw [pointCutoff, inv_mul_le_iff₀ hpos, mul_one]
  calc ∑ k ∈ Finset.range (n + 1), η ((3 : ℝ) ^ k • x)
      ≤ ∑ k ∈ Finset.range (n + 1), (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ (hη01 _).2
    _ = (n : ℝ) + 1 := by simp

/-- The averaged cut-off `η_n` is `1` on `closedBall 0 3^{-n}`. -/
theorem pointCutoff_eq_one (hη1 : EqOn η 1 (closedBall 0 1)) (n : ℕ) {x : E}
    (hx : ‖x‖ ≤ ((3 : ℝ) ^ n)⁻¹) : pointCutoff η n x = 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [pointCutoff, Finset.sum_eq_card_nsmul (b := (1 : ℝ)) fun k hk ↦ ?_]
  · simp [hpos.ne']
  · refine hη1 (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    calc (3 : ℝ) ^ k * ‖x‖ ≤ 3 ^ k * (3 ^ n)⁻¹ := by gcongr
      _ ≤ 1 := by
        rw [mul_inv_le_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ (by norm_num) hk'

/-- The averaged cut-off vanishes for `‖x‖ ≥ 2`. -/
theorem pointCutoff_eq_zero (hηs : tsupport η ⊆ ball 0 2) (n : ℕ) {x : E} (hx : 2 ≤ ‖x‖) :
    pointCutoff η n x = 0 := by
  rw [pointCutoff, Finset.sum_eq_zero fun k _ ↦ ?_, mul_zero]
  refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
  have h2 := mem_ball_zero_iff.1 (hηs h)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
  have : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

/-- The averaged cut-offs tend to `0` at every `x ≠ 0`: at most `log₃(2/‖x‖) + 1` of the
`n + 1` summands are nonzero. -/
theorem tendsto_pointCutoff (hηs : tsupport η ⊆ ball 0 2) (hη01 : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    {x : E} (hx : x ≠ 0) : Tendsto (fun n ↦ pointCutoff η n x) atTop (𝓝 0) := by
  classical
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 / ‖x‖ < 3 ^ K := pow_unbounded_of_one_lt _ (by norm_num)
  have hzero : ∀ k, K ≤ k → η ((3 : ℝ) ^ k • x) = 0 := fun k hk ↦ by
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have h2 := mem_ball_zero_iff.1 (hηs h)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
    have h3 : (3 : ℝ) ^ K ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hk
    rw [div_lt_iff₀ hxpos] at hK
    nlinarith
  have hle : ∀ n, pointCutoff η n x ≤ ((n : ℝ) + 1)⁻¹ * K := fun n ↦ by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [pointCutoff]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hpos).le
    rw [← Finset.sum_filter_of_ne (p := fun k ↦ k < K) fun k _ hk ↦ ?_]
    · calc ∑ k ∈ (Finset.range (n + 1)).filter (fun k ↦ k < K), η ((3 : ℝ) ^ k • x)
          ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k ↦ k < K), (1 : ℝ) :=
            Finset.sum_le_sum fun k _ ↦ (hη01 _).2
        _ ≤ ∑ k ∈ Finset.range K, (1 : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ zero_le_one
            intro k hk
            exact Finset.mem_range.2 (Finset.mem_filter.1 hk).2
        _ = K := by simp
    · by_contra h
      exact hk (hzero k (not_lt.1 h))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ (pointCutoff_mem_Icc hη01 n x).1) hle
  simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (K : ℝ)

/-- The derivative of the averaged cut-off: `∇η_n x = (n + 1)⁻¹ ∑_{k ≤ n} 3^k ∇η (3^k x)`. -/
theorem hasFDerivAt_pointCutoff (hη : ContDiff ℝ ∞ η) (n : ℕ) (x : E) :
    HasFDerivAt (pointCutoff η n) (((n : ℝ) + 1)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x)) x := by
  refine HasFDerivAt.const_mul (HasFDerivAt.fun_sum fun k _ ↦ ?_) _
  have h := ((hη.differentiable (by simp)) _).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul ((3 : ℝ) ^ k))
  rwa [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] at h

/-- The derivative of the averaged cut-off, as `fderiv`. -/
theorem fderiv_pointCutoff (hη : ContDiff ℝ ∞ η) (n : ℕ) (x : E) :
    fderiv ℝ (pointCutoff η n) x = ((n : ℝ) + 1)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x) :=
  (hasFDerivAt_pointCutoff hη n x).fderiv

/-- The gradient of `η` vanishes on the open unit ball, where `η = 1`. -/
theorem fderiv_eq_zero_of_eqOn_one_closedBall_one (hη1 : EqOn η 1 (closedBall 0 1)) {y : E}
    (hy : ‖y‖ < 1) : fderiv ℝ η y = 0 := by
  have hev : η =ᶠ[𝓝 y] fun _ ↦ (1 : ℝ) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)) fun z hz ↦
      hη1 (ball_subset_closedBall hz)
  rw [hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply]

end PointCutoff

section PointCutoffNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {η : E → ℝ}

/-- The summand `3^k ∇η (3^k x)` of `∇η_n` vanishes off the shell `3^{-k} ≤ ‖x‖ < 2 · 3^{-k}`. -/
theorem norm_mem_Ico_of_pow_smul_fderiv_ne_zero (hη1 : EqOn η 1 (closedBall 0 1))
    (hηs : tsupport η ⊆ ball 0 2) {k : ℕ} {x : E}
    (h : (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x) ≠ 0) :
    ((3 : ℝ) ^ k)⁻¹ ≤ ‖x‖ ∧ ‖x‖ < 2 * ((3 : ℝ) ^ k)⁻¹ := by
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hne : fderiv ℝ η ((3 : ℝ) ^ k • x) ≠ 0 := fun h0 ↦ h (by rw [h0, smul_zero])
  have h2 := mem_ball_zero_iff.1 (hηs (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 hne)))
  have h1 : ¬ ‖(3 : ℝ) ^ k • x‖ < 1 := fun hlt ↦
    hne (fderiv_eq_zero_of_eqOn_one_closedBall_one hη1 hlt)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3] at h1 h2
  rw [not_lt] at h1
  constructor
  · rw [inv_le_iff_one_le_mul₀ h3, mul_comm]
    exact h1
  · rwa [lt_mul_inv_iff₀ h3, mul_comm]

/-- The shells of two distinct summands of `∇η_n` are disjoint. -/
theorem eq_of_pow_smul_fderiv_ne_zero (hη1 : EqOn η 1 (closedBall 0 1))
    (hηs : tsupport η ⊆ ball 0 2) {k k' : ℕ} {x : E}
    (h : (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x) ≠ 0)
    (h' : (3 : ℝ) ^ k' • fderiv ℝ η ((3 : ℝ) ^ k' • x) ≠ 0) : k = k' := by
  have key : ∀ {k k' : ℕ}, k < k' → ((3 : ℝ) ^ k)⁻¹ ≤ ‖x‖ → ‖x‖ < 2 * ((3 : ℝ) ^ k')⁻¹ → False :=
    fun {k k'} hkk' h1 h2 ↦ by
    have h3 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ k' := pow_le_pow_right₀ (by norm_num) hkk'
    have h4 : 2 * ((3 : ℝ) ^ k')⁻¹ ≤ 2 * ((3 : ℝ) ^ (k + 1))⁻¹ := by gcongr
    have h5 : 2 * ((3 : ℝ) ^ (k + 1))⁻¹ < ((3 : ℝ) ^ k)⁻¹ := by
      rw [pow_succ, mul_inv, ← mul_assoc, mul_comm 2, mul_assoc]
      have : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹ := by positivity
      nlinarith
    linarith
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact key hlt (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs h).1
      (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs h').2
  · exact key hlt (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs h').1
      (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs h).2

/-- For a finite family with at most one nonzero member, `‖∑ aᵢ‖ₑ^q ≤ ∑ ‖aᵢ‖ₑ^q`, `q > 0`. -/
theorem enorm_sum_rpow_le_sum_of_forall_eq {ι G : Type*} [NormedAddCommGroup G] {s : Finset ι}
    {a : ι → G} (h : ∀ i ∈ s, ∀ j ∈ s, a i ≠ 0 → a j ≠ 0 → i = j) {q : ℝ} (hq : 0 < q) :
    ‖∑ i ∈ s, a i‖ₑ ^ q ≤ ∑ i ∈ s, ‖a i‖ₑ ^ q := by
  classical
  by_cases h0 : ∃ i ∈ s, a i ≠ 0
  · obtain ⟨i, hi, hai⟩ := h0
    rw [Finset.sum_eq_single i (fun j hj hji ↦ by_contra fun haj ↦ hji (h j hj i hi haj hai))
      (fun hi' ↦ absurd hi hi')]
    exact Finset.single_le_sum (f := fun j ↦ ‖a j‖ₑ ^ q) (fun _ _ ↦ zero_le) hi
  · push Not at h0
    rw [Finset.sum_eq_zero h0, enorm_zero, ENNReal.zero_rpow_of_pos hq]
    exact zero_le

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- **The `L^d` norm of the gradient of the averaged cut-off, `d = dim E`**:
`∫ ‖∇η_n‖^d ≤ (n + 1) ((2 M)/(n + 1))^d |B(0, 1)|` when `‖∇η‖ ≤ M`, since the summands
`3^k ∇η (3^k x)` of `(n + 1) ∇η_n` are bounded by `3^k M` and supported in the disjoint balls
`B(0, 2 · 3^{-k})` of measure `(2 · 3^{-k})^d |B(0, 1)|`. -/
theorem lintegral_enorm_fderiv_pointCutoff_pow_le [Nontrivial E] (hη : ContDiff ℝ ∞ η)
    (hη1 : EqOn η 1 (closedBall 0 1)) (hηs : tsupport η ⊆ ball 0 2) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (n : ℕ) :
    ∫⁻ x, ‖fderiv ℝ (pointCutoff η n) x‖ₑ ^ (finrank ℝ E : ℝ) ∂μ
      ≤ ((n : ℝ≥0∞) + 1) * ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (2 * M)) ^ finrank ℝ E)
        * μ (ball 0 1) := by
  classical
  have hd : 0 < finrank ℝ E := finrank_pos
  have hd' : (0 : ℝ) < finrank ℝ E := by exact_mod_cast hd
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set d := finrank ℝ E with hddef
  -- the pointwise bound
  have hpt : ∀ x, ‖fderiv ℝ (pointCutoff η n) x‖ₑ ^ (d : ℝ) ≤ ∑ k ∈ Finset.range (n + 1),
      (ball (0 : E) (2 * ((3 : ℝ) ^ k)⁻¹)).indicator
        (fun _ ↦ ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (3 ^ k * M)) ^ d)) x := by
    intro x
    rw [fderiv_pointCutoff hη, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hd'.le]
    calc ‖((n : ℝ) + 1)⁻¹‖ₑ ^ (d : ℝ)
          * ‖∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x)‖ₑ ^ (d : ℝ)
        ≤ ‖((n : ℝ) + 1)⁻¹‖ₑ ^ (d : ℝ) * ∑ k ∈ Finset.range (n + 1),
            ‖(3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x)‖ₑ ^ (d : ℝ) := by
          gcongr
          exact enorm_sum_rpow_le_sum_of_forall_eq
            (fun k _ k' _ hk hk' ↦ eq_of_pow_smul_fderiv_ne_zero hη1 hηs hk hk') hd'
      _ = ∑ k ∈ Finset.range (n + 1), ‖((n : ℝ) + 1)⁻¹‖ₑ ^ (d : ℝ)
          * ‖(3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x)‖ₑ ^ (d : ℝ) := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum fun k _ ↦ ?_
    have h3 : (0 : ℝ) < 3 ^ k := by positivity
    by_cases hx : x ∈ ball (0 : E) (2 * ((3 : ℝ) ^ k)⁻¹)
    · rw [Set.indicator_of_mem hx, Real.enorm_of_nonneg (inv_pos.2 hpos).le, mul_pow,
        ENNReal.ofReal_mul (by positivity), ← Real.rpow_natCast (((n : ℝ) + 1)⁻¹),
        ← Real.rpow_natCast ((3 : ℝ) ^ k * M),
        ← ENNReal.ofReal_rpow_of_nonneg (inv_pos.2 hpos).le hd'.le,
        ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hd'.le]
      gcongr
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3]
      exact mul_le_mul_of_nonneg_left (hM _) h3.le
    · have h0 : (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x) = 0 := by
        by_contra hne
        exact hx (mem_ball_zero_iff.2 (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs hne).2)
      rw [h0, enorm_zero, ENNReal.zero_rpow_of_pos hd', mul_zero]
      exact zero_le
  -- integration
  calc ∫⁻ x, ‖fderiv ℝ (pointCutoff η n) x‖ₑ ^ (d : ℝ) ∂μ
      ≤ ∫⁻ x, ∑ k ∈ Finset.range (n + 1), (ball (0 : E) (2 * ((3 : ℝ) ^ k)⁻¹)).indicator
          (fun _ ↦ ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (3 ^ k * M)) ^ d)) x ∂μ :=
        lintegral_mono hpt
    _ = ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (3 ^ k * M)) ^ d)
          * μ (ball (0 : E) (2 * ((3 : ℝ) ^ k)⁻¹)) := by
        rw [lintegral_finsetSum _ fun k _ ↦ measurable_const.indicator measurableSet_ball]
        exact Finset.sum_congr rfl fun k _ ↦ lintegral_indicator_const measurableSet_ball _
    _ = ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (2 * M)) ^ d) * μ (ball (0 : E) 1) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        have h3 : (0 : ℝ) < 3 ^ k := by positivity
        rw [Measure.addHaar_ball μ _ (by positivity), ← mul_assoc, ← ENNReal.ofReal_mul
          (by positivity), ← mul_pow]
        congr 3
        field_simp
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- `‖∇η_n‖_{L^d} → 0` in dimension `d ≥ 2`. -/
theorem tendsto_lintegral_enorm_fderiv_pointCutoff_pow (hη : ContDiff ℝ ∞ η)
    (hη1 : EqOn η 1 (closedBall 0 1)) (hηs : tsupport η ⊆ ball 0 2) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (hd : 2 ≤ finrank ℝ E) :
    Tendsto (fun n ↦ ∫⁻ x, ‖fderiv ℝ (pointCutoff η n) x‖ₑ ^ (finrank ℝ E : ℝ) ∂μ) atTop
      (𝓝 0) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  set d := finrank ℝ E with hddef
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- the real bound `(n + 1) ((2M)/(n+1))^d = ((n+1)⁻¹)^(d-1) (2M)^d → 0`
  have hreal : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * (2 * M)) ^ d) atTop
      (𝓝 0) := by
    have he : ∀ n : ℕ, ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * (2 * M)) ^ d
        = (1 / ((n : ℝ) + 1)) ^ (d - 1) * (2 * M) ^ d := fun n ↦ by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rw [he, Nat.add_sub_cancel, mul_pow, pow_succ, one_div]
      field_simp
    simp_rw [he]
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat.pow (d - 1)).mul_const ((2 * M) ^ d)
    rwa [zero_pow (by omega), zero_mul] at h1
  have hB : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0∞) + 1)
      * ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (2 * M)) ^ d) * μ (ball (0 : E) 1)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hreal) (b := μ (ball (0 : E) 1))
      (Or.inr measure_ball_lt_top.ne)
    rw [ENNReal.ofReal_zero, zero_mul] at h1
    refine h1.congr fun n ↦ ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 2
    exact_mod_cast (ENNReal.ofReal_natCast (n + 1)).symm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun _ ↦ zero_le)
    fun n ↦ lintegral_enorm_fderiv_pointCutoff_pow_le hη hη1 hηs hM n

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The gradient of the averaged cut-off is supported in `closedBall 0 2`. -/
theorem support_fderiv_pointCutoff_subset (hηs : tsupport η ⊆ ball 0 2) (n : ℕ) :
    Function.support (fderiv ℝ (pointCutoff η n)) ⊆ closedBall 0 2 := by
  refine (support_fderiv_subset (𝕜 := ℝ)).trans ?_
  refine (closure_mono fun x hx ↦ ?_).trans closure_ball_subset_closedBall
  rw [mem_ball_zero_iff]
  by_contra h
  exact hx (pointCutoff_eq_zero hηs n (not_lt.1 h))

/-- **The `L^p` norm of the gradient of the averaged cut-off tends to `0`** for `1 ≤ p ≤ d`,
`d = dim E ≥ 2`: the case `p = d` from `lintegral_enorm_fderiv_pointCutoff_pow_le`, the others by
Hölder's inequality on `closedBall 0 2`, which carries the gradients. The capacity of a point is
zero in `W^{1,p}` for `p ≤ d`. -/
theorem tendsto_eLpNorm_fderiv_pointCutoff (hη : ContDiff ℝ ∞ η)
    (hη1 : EqOn η 1 (closedBall 0 1)) (hηs : tsupport η ⊆ ball 0 2) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (hd : 2 ≤ finrank ℝ E) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpd : p ≤ finrank ℝ E) :
    Tendsto (fun n ↦ eLpNorm (fderiv ℝ (pointCutoff η n)) p μ) atTop (𝓝 0) := by
  set d := finrank ℝ E with hddef
  have hdpos : (0 : ℝ) < d := by norm_cast; omega
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top hdt hpd
  have hm : ∀ n, AEStronglyMeasurable (fderiv ℝ (pointCutoff η n)) μ := fun n ↦
    ((contDiff_pointCutoff hη n).continuous_fderiv (by simp)).aestronglyMeasurable
  -- the case `p = d`
  have hLd : Tendsto (fun n ↦ eLpNorm (fderiv ℝ (pointCutoff η n)) d μ) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / (d : ℝ))).tendsto 0).comp
      (tendsto_lintegral_enorm_fderiv_pointCutoff_pow (μ := μ) hη hη1 hηs hM hd)
    simp only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.2 hdpos)] at h
    refine h.congr fun n ↦ ?_
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hd0 hdt (hm n), ENNReal.toReal_natCast]
  -- Hölder on `closedBall 0 2`
  have hC : μ (closedBall (0 : E) 2) ^ (1 / p.toReal - 1 / (d : ℝ)) ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg ?_ measure_closedBall_lt_top.ne
    rw [sub_nonneg]
    refine one_div_le_one_div_of_le (ENNReal.toReal_pos hp0 hpt) ?_
    have := ENNReal.toReal_mono hdt hpd
    rwa [ENNReal.toReal_natCast] at this
  have hle : ∀ n, eLpNorm (fderiv ℝ (pointCutoff η n)) p μ
      ≤ eLpNorm (fderiv ℝ (pointCutoff η n)) d μ
        * μ (closedBall (0 : E) 2) ^ (1 / p.toReal - 1 / (d : ℝ)) := fun n ↦ by
    rw [← eLpNorm_restrict_eq_of_support_subset (hm n) (support_fderiv_pointCutoff_subset hηs n),
      ← eLpNorm_restrict_eq_of_support_subset (p := d) (hm n)
        (support_fderiv_pointCutoff_subset hηs n)]
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpd
      (μ := μ.restrict (closedBall (0 : E) 2)) ((hm n).restrict)
    rwa [Measure.restrict_apply_univ, ENNReal.toReal_natCast] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hle
  simpa using ENNReal.Tendsto.mul_const hLd (Or.inr hC)

end PointCutoffNorm

section PointCapacity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndex

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Convergence in `W^{1,p}(Ω)` from the `L^p(Ω)` convergence of the functions and of the
first-order weak derivatives: `SobolevMultiIndex.tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub`
with the multi-indices of order at most one enumerated as `0` and the `e_i`. -/
theorem tendsto_of_tendsto_eLpNorm_fn_sub_of_forall_single {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {w : ℕ → SobolevMultiIndex F b 1 p Ω μ} {u : SobolevMultiIndex F b 1 p Ω μ}
    (h0 : Tendsto (fun n ↦ eLpNorm (fn (w n) - fn u) p (μ.restrict (Ω : Set E))) atTop (𝓝 0))
    (hi : ∀ i, Tendsto (fun n ↦ eLpNorm ((weakDeriv (w n) (MultiIndexLE.single i) : E → F)
      - (weakDeriv u (MultiIndexLE.single i) : E → F)) p (μ.restrict (Ω : Set E))) atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 u) := by
  refine tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun α ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
  · exact h0
  · exact hi i

/-- **Lemma 9.5 without compactness at infinity**: an element `u` of `W^{1,p}(Ω)`, `1 ≤ p < ∞`,
whose function vanishes almost everywhere on an open neighbourhood `U` of `Ωᶜ` lies in
`W_0^{1,p}(Ω)`. The cut-offs `ζ_n u → u` (`SobolevMultiIndex.tendsto_cutoff_smul`) vanish almost
everywhere outside the compact set `closedBall 0 (2(n+1)) ∖ U ⊆ Ω`, so lie in `W_0^{1,p}(Ω)` by
Lemma 9.5 (`SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact`), and `W_0^{1,p}(Ω)` is
closed ([brezis2011functional] Lemma 9.5 and footnote 5 of §9.1). -/
theorem mem_zero_of_ae_eq_zero_of_compl_subset (hp' : p ≠ ⊤) (u : SobolevMultiIndex ℝ b 1 p Ω μ)
    {U : Set E} (hU : IsOpen U) (hΩU : (Ω : Set E)ᶜ ⊆ U)
    (hu : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∈ U → fn u x = 0) :
    u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  obtain ⟨ζ, hζ, hζ1, hζs, hζ01⟩ := exists_contDiff_eqOn_one_closedBall_one E
  obtain ⟨v, hv, hv0, hvt⟩ :=
    tendsto_cutoff_smul hp' hζ hζ01 hζ1 (hζs.trans ball_subset_closedBall) u
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hvt (Eventually.of_forall fun n ↦ ?_)
  refine mem_zero_of_ae_eq_zero_compl_isCompact hp' (v n)
    (K := closedBall 0 (2 * ((n : ℝ) + 1)) ∩ Uᶜ)
    ((isCompact_closedBall _ _).inter_right hU.isClosed_compl)
    (fun x hx ↦ by_contra fun hxΩ ↦ hx.2 (hΩU hxΩ)) ?_
  filter_upwards [hv n, hv0 n, hu] with x hx hx0 hxU hxK
  by_cases hxb : 2 * ((n : ℝ) + 1) < ‖x‖
  · exact hx0 hxb
  · have hxU' : x ∈ U := by
      by_contra h
      exact hxK ⟨mem_closedBall_zero_iff.2 (not_lt.1 hxb), h⟩
    rw [hx, hxU hxU', mul_zero]

/-- **Bounded functions are dense in `W^{1,p}(Ω)`**, `1 ≤ p < ∞`: every `u ∈ W^{1,p}(Ω)` is the
limit of elements with bounded functions. With the truncations
`H_n(t) = t − (n+1) G(t/(n+1))` of `stepTruncation` — `C^1`, `H_n(t) = t` for `|t| ≤ n + 1`,
`H_n(t) = 0` for `|t| ≥ 2(n+1)`, `|H_n'| ≤ 1 + M` — the composites `H_n ∘ u` lie in `W^{1,p}(Ω)`
by Proposition 9.5 (`MemSobolevMultiIndex.contDiff_comp`), are bounded, and converge to `u` in
`W^{1,p}(Ω)` by dominated convergence, their weak derivatives being `H_n'(u) ∂_i u`
(`SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp`). -/
theorem exists_seq_tendsto_ae_abs_le (hp' : p ≠ ⊤) (u : SobolevMultiIndex ℝ b 1 p Ω μ) :
    ∃ v : ℕ → SobolevMultiIndex ℝ b 1 p Ω μ,
      (∀ n, ∃ M : ℝ, ∀ᵐ x ∂μ.restrict (Ω : Set E), |fn (v n) x| ≤ M) ∧
        Tendsto v atTop (𝓝 u) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hum : AEStronglyMeasurable (fn u) (μ.restrict (Ω : Set E)) := (memLp u).aestronglyMeasurable
  obtain ⟨M, hM0, hM⟩ := exists_abs_deriv_stepTruncation_le
  -- the truncations `H_n(t) = t − (n+1) G(t/(n+1))`
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ := ⟨_, rfl⟩
  have hcpos : ∀ n, 0 < c n := fun n ↦ by rw [hcdef]; positivity
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → ℝ → ℝ,
      H = fun (n : ℕ) (t : ℝ) ↦ t - (c n)⁻¹ * stepTruncation (t * c n) := ⟨_, rfl⟩
  have hHd : ∀ n t, HasDerivAt (H n) (1 - deriv stepTruncation (t * c n)) t := fun n t ↦ by
    rw [hHdef]
    exact (hasDerivAt_id t).sub (hasDerivAt_scaled_stepTruncation (hcpos n).ne' t)
  have hHc : ∀ n, ContDiff ℝ 1 (H n) := fun n ↦ by
    rw [hHdef]
    exact contDiff_id.sub (contDiff_const.mul
      ((contDiff_stepTruncation.of_le (by simp)).comp (contDiff_id.mul contDiff_const)))
  have hH0 : ∀ n, H n 0 = 0 := fun n ↦ by simp [hHdef, stepTruncation_zero]
  have hHderiv : ∀ n t, deriv (H n) t = 1 - deriv stepTruncation (t * c n) :=
    fun n t ↦ (hHd n t).deriv
  have hHM : ∀ n t, |deriv (H n) t| ≤ 1 + M := fun n t ↦ by
    rw [hHderiv]
    exact (abs_sub _ _).trans (by rw [abs_one]; linarith [hM (t * c n)])
  have hHle : ∀ n t, |H n t| ≤ (1 + M) * |t| := fun n t ↦ by
    simpa [hH0 n] using abs_sub_le_mul_of_abs_deriv_le (hHc n) (hHM n) t 0
  have hHzero : ∀ (n : ℕ) (t : ℝ), 2 ≤ |t| * c n → H n t = 0 := fun n t ht ↦ by
    simp only [hHdef]
    rw [stepTruncation_of_two_le (by rwa [abs_mul, abs_of_pos (hcpos n)]), mul_comm t,
      inv_mul_cancel_left₀ (hcpos n).ne', sub_self]
  have hHid : ∀ (n : ℕ) (t : ℝ), |t| * c n ≤ 1 → H n t = t := fun n t ht ↦ by
    simp only [hHdef]
    rw [stepTruncation_of_abs_le (by rwa [abs_mul, abs_of_pos (hcpos n)]), mul_zero, sub_zero]
  have hHd1 : ∀ (n : ℕ) (t : ℝ), |t| * c n < 1 → deriv (H n) t = 1 := fun n t ht ↦ by
    rw [hHderiv, deriv_stepTruncation_of_abs_lt (by rwa [abs_mul, abs_of_pos (hcpos n)]),
      sub_zero]
  have hHbdd : ∀ n t, |H n t| ≤ (1 + M) * (2 * (c n)⁻¹) := fun n t ↦ by
    by_cases ht : 2 ≤ |t| * c n
    · rw [hHzero n t ht, abs_zero]
      exact mul_nonneg (by linarith) (mul_nonneg zero_le_two (inv_pos.2 (hcpos n)).le)
    · refine (hHle n t).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      rw [not_le, ← lt_div_iff₀ (hcpos n), div_eq_mul_inv] at ht
      exact ht.le
  have hev : ∀ t : ℝ, ∀ n ≥ ⌈|t|⌉₊, |t| * c n < 1 := fun t n hn ↦ by
    rw [hcdef, mul_inv_lt_iff₀ (by positivity), one_mul]
    exact (Nat.le_ceil _).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hn)
  -- the truncated elements `H_n ∘ u`
  choose U hU using fun n ↦
    ((memSobolevMultiIndex u).contDiff_comp hp (hHc n) (hH0 n) (hHM n)).exists_sobolevMultiIndex
  refine ⟨U, fun n ↦ ⟨(1 + M) * (2 * (c n)⁻¹), ?_⟩,
    tendsto_of_tendsto_eLpNorm_fn_sub_of_forall_single ?_ fun i ↦ ?_⟩
  · filter_upwards [hU n] with x hx
    rw [hx]
    exact hHbdd n _
  -- `H_n ∘ u → u` in `L^p(Ω)`
  · have hL0 : Tendsto (fun n ↦ eLpNorm ((fun x ↦ H n (fn u x)) - fn u) p
        (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp' (bound := fun x ↦ (1 + M) * ‖fn u x‖)
        (fun n ↦ (hHc n).continuous.comp_aestronglyMeasurable hum) hum
        ((memLp u).norm.const_mul _) (fun n ↦ Eventually.of_forall fun x ↦ ?_)
        (Eventually.of_forall fun x ↦ ?_)
      · simpa [Real.norm_eq_abs] using hHle n (fn u x)
      · exact tendsto_atTop_of_eventually_const (i₀ := ⌈|fn u x|⌉₊) fun n hn ↦
          hHid n _ (hev _ n hn).le
    exact hL0.congr fun n ↦
      (eLpNorm_congr_ae ((hU n).sub (Filter.EventuallyEq.refl _ _))).symm
  -- `H_n'(u) ∂_i u → ∂_i u` in `L^p(Ω)`
  · have hdU : ∀ n, (weakDeriv (U n) (MultiIndexLE.single i) : E → ℝ)
        =ᵐ[μ.restrict (Ω : Set E)]
          fun x ↦ deriv (H n) (fn u x) * weakDeriv u (MultiIndexLE.single i) x := fun n ↦
      weakDeriv_single_ae_eq_of_fn_ae_eq_comp (hHc n) (hHM n) (hU n) i
    have hLi : Tendsto (fun n ↦ eLpNorm
        ((fun x ↦ deriv (H n) (fn u x) * weakDeriv u (MultiIndexLE.single i) x)
          - (weakDeriv u (MultiIndexLE.single i) : E → ℝ)) p (μ.restrict (Ω : Set E))) atTop
        (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp'
        (bound := fun x ↦ (1 + M) * ‖weakDeriv u (MultiIndexLE.single i) x‖)
        (fun n ↦ (((hHc n).continuous_deriv le_rfl).comp_aestronglyMeasurable hum).mul
          (Lp.aestronglyMeasurable _))
        (Lp.aestronglyMeasurable _) ((Lp.memLp _).norm.const_mul _)
        (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hHM n _) (norm_nonneg _)
      · exact tendsto_atTop_of_eventually_const (i₀ := ⌈|fn u x|⌉₊) fun n hn ↦ by
          rw [hHd1 n _ (hev _ n hn), one_mul]
    exact hLi.congr fun n ↦
      (eLpNorm_congr_ae ((hdU n).sub (Filter.EventuallyEq.refl _ _))).symm


/-- **The capacity of a point is zero in `W^{1,p}`, `p ≤ dim E`**: a bounded element `u` of
`W^{1,p}(Ω)`, `1 ≤ p ≤ d = dim E`, `d ≥ 2`, is the limit in `W^{1,p}(Ω)` of elements vanishing
almost everywhere on a ball around `0`. The approximants are `(1 − η_n) u` with the averaged
cut-offs `η_n = pointCutoff η n`, equal to `1` near `0`: `η_n u → 0` and `η_n ∂_i u → 0` in
`L^p(Ω)` by dominated convergence (`η_n → 0` off `0`, a null set), and
`‖u ∂_i η_n‖_p ≤ M ‖e_i‖ ‖∇η_n‖_p → 0` by `tendsto_eLpNorm_fderiv_pointCutoff` — this is where
`p ≤ d` enters, through `‖∇η_n‖_{L^d}^d ≤ C (n+1)^{1-d}`. -/
theorem exists_seq_tendsto_ae_eq_zero_ball (hp' : p ≠ ⊤) (hd : 2 ≤ finrank ℝ E)
    (hpd : p ≤ finrank ℝ E) (u : SobolevMultiIndex ℝ b 1 p Ω μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), |fn u x| ≤ M) :
    ∃ v : ℕ → SobolevMultiIndex ℝ b 1 p Ω μ,
      (∀ n, ∃ r > 0, ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∈ ball 0 r → fn (v n) x = 0) ∧
        Tendsto v atTop (𝓝 u) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hum : AEStronglyMeasurable (fn u) (μ.restrict (Ω : Set E)) := (memLp u).aestronglyMeasurable
  obtain ⟨η, hη, hη1, hηs, hη01⟩ := exists_contDiff_eqOn_one_closedBall_one E
  have hηc : HasCompactSupport η :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport η)
      (hηs.trans ball_subset_closedBall)
  obtain ⟨Mη, hMη⟩ := (hηc.fderiv ℝ).exists_bound_of_continuous (hη.continuous_fderiv (by simp))
  -- the factors `c n = 1 − η_n`
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → E → ℝ, c = fun n x ↦ 1 - pointCutoff η n x := ⟨_, rfl⟩
  have hcs : ∀ n, ContDiff ℝ ∞ (c n) := fun n ↦ by
    rw [hcdef]
    exact contDiff_const.sub (contDiff_pointCutoff hη n)
  have hcd : ∀ n x, fderiv ℝ (c n) x = -fderiv ℝ (pointCutoff η n) x := fun n x ↦ by
    have h : HasFDerivAt (c n) (0 - fderiv ℝ (pointCutoff η n) x) x := by
      rw [fderiv_pointCutoff hη, hcdef]
      exact (hasFDerivAt_const (1 : ℝ) x).fun_sub (hasFDerivAt_pointCutoff hη n x)
    rw [h.fderiv, zero_sub]
  have hc01 : ∀ n x, c n x ∈ Icc (0 : ℝ) 1 := fun n x ↦ by
    have := pointCutoff_mem_Icc hη01 n x
    rw [hcdef]
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have hcM : ∀ n, ∃ K : ℝ, ∀ x, |c n x| ≤ K ∧ ‖fderiv ℝ (c n) x‖ ≤ K := fun n ↦ by
    have hsupp : HasCompactSupport (pointCutoff η n) := by
      refine IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport _) ?_
      refine (closure_mono fun x hx ↦ ?_).trans closure_ball_subset_closedBall
      rw [mem_ball_zero_iff]
      by_contra h
      exact hx (pointCutoff_eq_zero hηs n (not_lt.1 h))
    obtain ⟨K, hK⟩ := (hsupp.fderiv ℝ).exists_bound_of_continuous
      ((contDiff_pointCutoff hη n).continuous_fderiv (by simp))
    refine ⟨max 1 K, fun x ↦ ⟨?_, ?_⟩⟩
    · exact (abs_le.2 ⟨by linarith [(hc01 n x).1], (hc01 n x).2⟩).trans (le_max_left _ _)
    · rw [hcd, norm_neg]
      exact (hK x).trans (le_max_right _ _)
  have hc1 : ∀ n, ∀ x ∈ ball (0 : E) ((3 : ℝ) ^ n)⁻¹, c n x = 0 := fun n x hx ↦ by
    rw [hcdef]
    dsimp only
    rw [pointCutoff_eq_one hη1 n (mem_ball_zero_iff.1 hx).le, sub_self]
  have hclim : ∀ x, x ≠ 0 → Tendsto (fun n ↦ c n x) atTop (𝓝 1) := fun x hx ↦ by
    have := (tendsto_pointCutoff hηs hη01 hx).const_sub 1
    rw [sub_zero] at this
    rw [hcdef]
    exact this
  have hae : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  -- the elements `v n`, with functions `c n * u`
  have hmem : ∀ n, MemSobolevMultiIndex b (fun x ↦ c n x * fn u x) 1 p Ω μ := fun n ↦
    (memSobolevMultiIndex u).contDiff_mul hp (hcs n) (hcM n).choose_spec
  choose v hv using fun n ↦ (hmem n).exists_sobolevMultiIndex
  refine ⟨v, fun n ↦ ⟨((3 : ℝ) ^ n)⁻¹, by positivity, ?_⟩, ?_⟩
  · filter_upwards [hv n] with x hx hxr
    rw [hx, hc1 n x hxr, zero_mul]
  -- the weak derivatives of `v n`
  have hperm := fun i ↦ multiIndexTuple_single_perm (b : ι → E) i
  have hwu : ∀ i, HasWeakIteratedLineDerivOn ![b i] (fn u) (weakDeriv u (MultiIndexLE.single i))
      Ω μ := fun i ↦ (hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm (hperm i)
  have hwv : ∀ n i, (weakDeriv (v n) (MultiIndexLE.single i) : E → ℝ)
      =ᵐ[μ.restrict (Ω : Set E)] fun x ↦
        c n x * weakDeriv u (MultiIndexLE.single i) x + fderiv ℝ (c n) x (b i) * fn u x := by
    intro n i
    have h1 : HasWeakIteratedLineDerivOn ![b i] (fun x ↦ c n x * fn u x)
        (weakDeriv (v n) (MultiIndexLE.single i)) Ω μ :=
      ((hasWeakIteratedLineDerivOn (v n) (MultiIndexLE.single i)).of_perm (hperm i)).congr_ae
        (hv n) (EventuallyEq.refl _ _)
    exact (ae_restrict_iff' hΩm).2 (h1.ae_eq ((hwu i).contDiff_mul (hcs n)))
  -- dominated convergence for a factor `c n` tending to `1`
  have hdom : ∀ {f : E → ℝ}, MemLp f p (μ.restrict (Ω : Set E)) →
      Tendsto (fun n ↦ eLpNorm ((fun x ↦ c n x * f x) - f) p (μ.restrict (Ω : Set E))) atTop
        (𝓝 0) := fun {f} hf ↦ by
    refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp' (bound := fun x ↦ ‖f x‖)
      (fun n ↦ (hcs n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
      hf.aestronglyMeasurable hf.norm (fun n ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs (c n x)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_le.2 ⟨by linarith [(hc01 n x).1], (hc01 n x).2⟩)
    · filter_upwards [hae] with x hx
      have := (hclim x hx).mul_const (f x)
      rw [one_mul] at this
      exact this
  -- the gradient term
  have hgrad : ∀ i, Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (c n) x (b i) * fn u x) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
    intro i
    have hT := ENNReal.Tendsto.mul_const
      (tendsto_eLpNorm_fderiv_pointCutoff (μ := μ) hη hη1 hηs hMη hd hp hpd)
      (b := ENNReal.ofReal (M * ‖b i‖)) (Or.inr ENNReal.ofReal_ne_top)
    rw [zero_mul] at hT
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ ↦ zero_le)
      fun n ↦ ?_
    rw [mul_comm]
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (f := fun x ↦ fderiv ℝ (c n) x (b i) * fn u x) (g := fderiv ℝ (pointCutoff η n))
      (c := M * ‖b i‖) ?_ ?_ p).trans ?_
    · exact (((hcs n).fderiv_right (m := ∞) le_rfl).clm_apply
        contDiff_const).continuous.aestronglyMeasurable.mul hum
    · filter_upwards [hM] with x hx
      rw [norm_mul, hcd, neg_apply, norm_neg, Real.norm_eq_abs (fn u x)]
      calc ‖fderiv ℝ (pointCutoff η n) x (b i)‖ * |fn u x|
          ≤ ‖fderiv ℝ (pointCutoff η n) x‖ * ‖b i‖ * M :=
            mul_le_mul ((fderiv ℝ (pointCutoff η n) x).le_opNorm (b i)) hx (abs_nonneg _)
              (by positivity)
        _ = M * ‖b i‖ * ‖fderiv ℝ (pointCutoff η n) x‖ := by ring
    · gcongr
      exact Measure.restrict_le_self
  -- the convergence
  refine tendsto_of_tendsto_eLpNorm_fn_sub_of_forall_single ?_ fun i ↦ ?_
  · refine (hdom (memLp u)).congr fun n ↦ ?_
    exact (eLpNorm_congr_ae ((hv n).sub (Filter.EventuallyEq.refl _ _))).symm
  · have hsum := (hdom (Lp.memLp (weakDeriv u (MultiIndexLE.single i)))).add (hgrad i)
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
      fun n ↦ ?_
    have h : (weakDeriv (v n) (MultiIndexLE.single i) : E → ℝ)
        - (weakDeriv u (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
          ((fun x ↦ c n x * weakDeriv u (MultiIndexLE.single i) x)
            - (weakDeriv u (MultiIndexLE.single i) : E → ℝ))
          + fun x ↦ fderiv ℝ (c n) x (b i) * fn u x := by
      filter_upwards [hwv n i] with x hx
      simp only [Pi.sub_apply, Pi.add_apply, hx]
      ring
    rw [eLpNorm_congr_ae h]
    exact eLpNorm_add_le hp

end SobolevMultiIndex

/-- **Remark 17, the punctured space, predicate form**: on a finite-dimensional space `E` of
dimension `d ≥ 2`, for `1 ≤ p ≤ d` and an open set `Ω` whose complement is contained in `{0}`
(`Ω = E` or `Ω = E ∖ {0}`), `W_0^{1,p}(Ω) = W^{1,p}(Ω)`: a point has zero capacity. Bounded
elements are dense (`SobolevMultiIndex.exists_seq_tendsto_ae_abs_le`), a bounded element is the
limit of elements vanishing near `0` (`SobolevMultiIndex.exists_seq_tendsto_ae_eq_zero_ball`),
those lie in `W_0^{1,p}(Ω)` by Lemma 9.5 in the form
`SobolevMultiIndex.mem_zero_of_ae_eq_zero_of_compl_subset`, and `W_0^{1,p}(Ω)` is closed
([brezis2011functional] Chapter 9, Remark 17: "if `Ω = ℝ^N ∖ {0}` and `N ≥ 2` one can show that
`H_0^1(Ω) = H^1(Ω)`"). -/
theorem SobolevMultiIndexZero.eq_top_of_compl_subset_singleton (hd : 2 ≤ finrank ℝ E)
    (hpd : p ≤ finrank ℝ E) (hΩ : (Ω : Set E)ᶜ ⊆ {0}) :
    SobolevMultiIndexZero ℝ b 1 p Ω μ = ⊤ := by
  have hp' : p ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) hpd
  refine top_unique fun u _ ↦ ?_
  obtain ⟨v, hvb, hvt⟩ := SobolevMultiIndex.exists_seq_tendsto_ae_abs_le hp' u
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hvt (Eventually.of_forall fun n ↦ ?_)
  obtain ⟨M, hM⟩ := hvb n
  obtain ⟨w, hw0, hwt⟩ := SobolevMultiIndex.exists_seq_tendsto_ae_eq_zero_ball hp' hd hpd (v n) hM
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hwt (Eventually.of_forall fun m ↦ ?_)
  obtain ⟨r, hr, hw⟩ := hw0 m
  exact SobolevMultiIndex.mem_zero_of_ae_eq_zero_of_compl_subset hp' (w m) isOpen_ball
    (hΩ.trans (singleton_subset_iff.2 (mem_ball_self hr))) hw

/-- **Remark 17, the punctured space**: for `N ≥ 2` and `1 ≤ p ≤ N`,
`W_0^{1,p}(ℝ^N ∖ {0}) = W^{1,p}(ℝ^N ∖ {0})` — in the book, `H_0^1(ℝ^N ∖ {0}) = H^1(ℝ^N ∖ {0})`
for `N ≥ 2` ([brezis2011functional] Chapter 9, Remark 17: "if `ℝ^N ∖ Ω` is sufficiently thin and
`p < N`… one can show"; the endpoint `p = N` is included). The instance of
`SobolevMultiIndexZero.eq_top_of_compl_subset_singleton`: a point has zero `W^{1,p}`-capacity for
`p ≤ N`, by the averaged cut-offs `pointCutoff`. -/
theorem SobolevEuclideanZero.eq_top_of_compl_singleton {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (hN : 2 ≤ N) (hp : p ≤ N)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin N))) = {0}ᶜ) : SobolevEuclideanZero N 1 p Ω = ⊤ :=
  SobolevMultiIndexZero.eq_top_of_compl_subset_singleton
    (by rw [finrank_euclideanSpace_fin]; exact hN) (by rw [finrank_euclideanSpace_fin]; exact hp)
    (by rw [hΩ, compl_compl])

end PointCapacity

/-! ### Density: identities checked on the test functions hold on `W_0^{k,p}(Ω)` -/

section EqOn

/-- **Two continuous maps on `W^{k,p}(Ω)` that agree on the test functions agree on
`W_0^{k,p}(Ω)`**, the closure of the test functions. This is the density step of every "classical
solution is a weak solution" argument: an identity between continuous functionals checked on
`C_c^∞(Ω)` holds on `W_0^{1,p}(Ω)`. -/
theorem SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}
    {X : Type*} [TopologicalSpace X] [T2Space X] {f g : SobolevMultiIndex F b k p Ω μ → X}
    (hf : Continuous f) (hg : Continuous g)
    (h : EqOn f g (SobolevMultiIndex.testFunctions F b k p Ω μ)) :
    EqOn f g (SobolevMultiIndexZero F b k p Ω μ) := by
  rw [SobolevMultiIndexZero, Submodule.topologicalClosure_coe]
  exact closure_minimal h (isClosed_eq hf hg)

end EqOn

/-! ### Footnote 39: a `W_0^{1,p}` function with vanishing gradient is zero -/

section Footnote39

open SobolevMultiIndex

/-- **Footnote 39 of [brezis2011functional] §9.7**: for `N ≥ 1`, `1 ≤ p < ∞` and any open
`Ω ⊆ ℝ^N`, an element of `W_0^{1,p}(Ω)` whose partial derivatives all vanish is zero. The
extension by zero `ū` lies in `W^{1,p}(ℝ^N)` with `∇ū = ext(∇u) = 0` (Proposition 9.18 (i) ⇒
(iii), `SobolevEuclideanZero.extendZeroL`), so `ū` is almost everywhere constant on the connected
`ℝ^N` (Remark 7, `HasWeakFDerivOn.ae_eq_const_of_isPreconnected`), and a constant in
`L^p(ℝ^N)`, `p < ∞`, is `0` (`MeasureTheory.memLp_const_iff`, the measure of `ℝ^N` being
infinite for `N ≥ 1`; for `N = 0` the statement is false). -/
theorem SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero {N : ℕ} (hN : N ≠ 0)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ⊤) {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (u : SobolevEuclideanZero N 1 p Ω)
    (h : ∀ i, weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i) = 0) : u = 0 := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hΩm := Ω.isOpen.measurableSet
  have : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
  -- the tensor gradient of the extension by zero vanishes almost everywhere
  obtain ⟨w, hw, -, hwi, -⟩ := exists_hasWeakFDerivOn_fn (SobolevEuclideanZero.extendZeroL N p Ω u)
  simp only [Opens.coe_top, Measure.restrict_univ] at hwi
  have hw0 : w =ᵐ[volume] 0 := by
    have hall : ∀ᵐ x ∂volume, ∀ i, w x ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis i) = 0 :=
      ae_all_iff.2 fun i ↦ by
        refine (hwi i).trans ((SobolevEuclideanZero.weakDeriv_extendZeroL_single u i).trans ?_)
        rw [h i]
        have := (ae_eq_restrict_iff_indicator_ae_eq hΩm).1
          (Lp.coeFn_zero ℝ p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        refine this.trans (Eventually.of_forall fun x ↦ ?_)
        simp
    filter_upwards [hall] with x hx
    simp only [EuclideanSpace.basisFun_toBasis_apply] at hx
    refine ContinuousLinearMap.ext fun ξ ↦ ?_
    rw [← (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.sum_repr ξ, map_sum]
    simp [hx]
  obtain ⟨c, hc⟩ := hw.ae_eq_const_of_isPreconnected
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hw0) isPreconnected_univ
  simp only [Opens.coe_top, Measure.restrict_univ] at hc
  -- the constant is zero, the measure of `ℝ^N` being infinite
  have hmem : MemLp (fun _ : EuclideanSpace ℝ (Fin N) ↦ c) p volume :=
    (SobolevEuclidean.memLp_fn (SobolevEuclideanZero.extendZeroL N p Ω u)).ae_eq hc
  have hc0 : c = 0 := by
    rcases (memLp_const_iff hp0 hp').1 hmem with h0 | hfin
    · exact h0
    · rw [measure_univ_of_isAddLeftInvariant] at hfin
      exact absurd hfin (lt_irrefl _)
  -- hence `u = 0`
  refine Subtype.ext (ext_of_fn_ae_eq ?_)
  refine ((SobolevEuclideanZero.fn_extendZeroL_restrict u).symm.trans ?_).trans fn_zero.symm
  refine ae_restrict_of_ae (hc.trans (Eventually.of_forall fun x ↦ ?_))
  simp [hc0]

end Footnote39
