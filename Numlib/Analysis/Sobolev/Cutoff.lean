/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/MultiIndex.lean` and `Numlib/Analysis/Sobolev/Density.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Calculus.ContDiffConstOffCompact
import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Sobolev.Density
import Numlib.Analysis.Sobolev.MultiIndex

/-!
# Cut-off functions and extension by zero in `W^{1,p}(Ω)`

The elementary tools that Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, chapter 9, uses in every proof of §9.2–§9.4, on an arbitrary open set `Ω` of a
finite-dimensional real normed space with an additive Haar measure:

* **locality of the weak derivative**: a weak derivative on every relatively compact open subset
  of `Ω` is a weak derivative on `Ω`
  (`HasWeakIteratedLineDerivOn.of_forall_isCompact_closure_subset`), the device by which the book
  reduces a `W^{1,∞}` statement to `W^{1,q}`, `q < ∞`, on relatively compact subsets;
* **`C_c^1` test functions** (Remark 1): the defining identity of a weak derivative holds for
  every `C^1` test function with compact support in `Ω`
  (`HasWeakIteratedLineDerivOn.integral_smul_eq_of_contDiff_one`), by mollifying the function
  rather than the test function;
* **the zero extension of `α u`** for a cut-off `α` (Remark 4 (ii)): `IsSobolevCutoff Ω α` says
  that `α` is smooth, bounded with bounded derivative, and supported away from `∂Ω`; for such `α`
  and `u ∈ W^{1,p}(Ω)`, the extension of `α u` by zero lies in `W^{1,p}` of the whole space with
  the derivative one expects (`HasWeakIteratedLineDerivOn.indicator_mul`,
  `MemSobolevMultiIndex.indicator_mul`), with the `L^p` estimates of step (a) of the proof of
  the extension theorem;
* **the typed operators**: restriction to an open subset `SobolevMultiIndex.restrictL`, the zero
  extension `u ↦ α u` as a bounded linear map `W^{1,p}(Ω) → W^{1,p}(E)`
  (`SobolevMultiIndex.extendZeroMulL`), the inclusion `W^{k,p}(Ω) → L^q(Ω)` given the
  membership (`SobolevMultiIndex.toLpₗ`), in the vocabulary of `IsContinuousEmbedding`, the
  inclusion `W^{k,p}(Ω) → W^{k,r}(Ω)` for `r ≤ p` on a set of finite measure
  (`SobolevMultiIndex.toLowerExponentL`, over `MeasureTheory.Lp.monoExponentL`), the inclusion
  `W^{k,p}(Ω) → W^{k',p}(Ω)` for `k' ≤ k` (`SobolevMultiIndex.toLowerOrderL`) and the partial
  derivative `∂_i : W^{k+1,p}(Ω) → W^{k,p}(Ω)` (`SobolevMultiIndex.partialDerivL`), the typed
  form of the inductive definition of `W^{m+1,p}`;
* **the cut-off sequence** `ζ_n x = ζ (x / (n + 1))` of footnote 5
  (`MemSobolev.tendsto_sobolevNorm_cutoff_mul_sub` in the tensor reading,
  `SobolevMultiIndex.tendsto_cutoff_smul` on the typed space): `ζ_n u → u` in `W^{1,p}(Ω)` for
  `1 ≤ p < ∞`, with the tensor Leibniz rule `HasWeakIteratedFDerivOn.contDiff_mul_one`;
* **Lemma 9.5**: a `W^{k,p}(Ω)` function vanishing outside a compact subset of `Ω` lies in
  `W_0^{k,p}(Ω)` (`SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact`), at every order;
* **the local space** `W^{k,p}_loc(Ω)` (`MemSobolevMultiIndexLoc`), with the cut-off lemma that
  places `θ u` in `W^{k,p}(E)` for a test function `θ` on `Ω`;
* **the abstract extension predicate** `HasSobolevExtensionOn S` / `IsSobolevExtensionDomain N p Ω`
  ("a bounded linear extension operator `W^{1,p}(Ω) → W^{1,p}(ℝ^N)` exists on `S`"), under which
  the embedding and compactness theorems on a domain are stated once, and the density of the
  restrictions of `C_c^∞(ℝ^N)` functions it gives (the abstract form of Corollary 9.8).

## Design

Predicate-level statements are over a finite-dimensional real normed `E` with an additive Haar
measure `μ`, in the `HasWeakIteratedLineDerivOn ![y] f w Ω μ` (single direction) or
`HasWeakFDerivOn` (tensor) reading, as in `Numlib/Analysis/Sobolev/Mollification.lean` and
`Numlib/Analysis/Sobolev/Density.lean`; typed statements are on `SobolevMultiIndex F b k p Ω μ`
and its abbreviation `SobolevEuclidean N k p Ω` of `Numlib/Analysis/Sobolev/MultiIndex.lean`.

A cut-off asks for smoothness `C^∞` rather than the book's `C^1` because the test functions are
`C_c^∞` and `α φ` has to be a test function again; the `C^1` form is not needed anywhere, the
partitions of unity of the extension theorem being smooth.

The typed operators are assembled by one fixed pattern: define the function, prove the
membership and the bound at the predicate level, bundle by
`MemSobolevMultiIndex.exists_sobolevMultiIndex` and `SobolevMultiIndex.ext_of_fn_ae_eq`, and
bound the `ℓ^p` norm of the tuple of derivatives coordinatewise
(`PiLp.norm_le_norm_of_forall_norm_le`).

## References

[brezis2011functional], §9.1 (Remarks 1 and 4 (ii), footnote 5), §9.2 (proof of Theorem 9.7,
step (a)), §9.3.B (the standing hypothesis), §9.4 (Lemma 9.5, Remark 25).
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

/-! ### Locality of the weak derivative -/

section Locality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {μ : Measure E}
  {n : ℕ} {y : Fin n → E} {f w : E → F}

/-- **Locality of the weak derivative**: if `f` and `w` are locally integrable on `Ω`, and `w` is a
weak derivative of `f` along `y` on every open `Ω'` with compact closure contained in `Ω`, then it
is one on `Ω`. A test function on `Ω` has compact support, hence lives in such an `Ω'`, and the
defining identity on `Ω'` is the identity on `Ω`. This is the step "fix an open set `Ω'` with
`supp φ ⊂ Ω' ⊂⊂ Ω`" by which [brezis2011functional] handles `p = ∞` in Propositions 9.5 and 9.6,
reducing a `W^{1,∞}` statement to `W^{1,q}`, `q < ∞`, on relatively compact subsets. -/
theorem HasWeakIteratedLineDerivOn.of_forall_isCompact_closure_subset
    (hf : LocallyIntegrableOn f Ω μ) (hw : LocallyIntegrableOn w Ω μ)
    (h : ∀ Ω' : Opens E, IsCompact (closure (Ω' : Set E)) → closure (Ω' : Set E) ⊆ Ω →
      HasWeakIteratedLineDerivOn y f w Ω' μ) :
    HasWeakIteratedLineDerivOn y f w Ω μ where
  locallyIntegrableOn := hf
  locallyIntegrableOn_weakDeriv := hw
  integral_smul_eq φ := by
    obtain ⟨V, -, hVo, hφV, -, hVc, hVΩ, -⟩ :=
      φ.hasCompactSupport.exists_pos_forall_closedBall_subset Ω.isOpen φ.tsupport_subset
    have key := (h ⟨V, hVo⟩ hVc hVΩ).integral_smul_eq'
      ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
        = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
          (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
    have e2 : ∫ x in (Ω : Set E), φ x • w x ∂μ = ∫ x, φ x • w x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]
    rw [e1, e2]
    exact key

end Locality

/-! ### Remark 1: `C_c^1` test functions -/

section TestFunctionOne

variable {X G : Type*} [MeasurableSpace X] {ν : Measure X} [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- **Passing to the limit against a bounded factor**: if `a j → a₀` in `L^1(ν)` and `b` is a
bounded measurable scalar function, then `∫ b • a j → ∫ b • a₀`. -/
theorem MeasureTheory.tendsto_integral_smul_of_tendsto_eLpNorm_one {b : X → ℝ} {M : ℝ}
    (hb : ∀ x, |b x| ≤ M) (hbm : AEStronglyMeasurable b ν) {a : ℕ → X → G} {a₀ : X → G}
    (ha : ∀ j, Integrable (a j) ν) (ha₀ : Integrable a₀ ν)
    (hlim : Tendsto (fun j ↦ eLpNorm (fun x ↦ a j x - a₀ x) 1 ν) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x, b x • a j x ∂ν) atTop (𝓝 (∫ x, b x • a₀ x ∂ν)) := by
  have hint : ∀ c : X → G, Integrable c ν → Integrable (fun x ↦ b x • c x) ν := fun c hc ↦
    hc.bdd_smul M hbm (Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hb x)
  have hup : Tendsto (fun j ↦ (ENNReal.ofReal M * eLpNorm (fun x ↦ a j x - a₀ x) 1 ν).toReal)
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = (0 : ℝ≥0∞).toReal by simp]
    refine (ENNReal.tendsto_toReal (by simp)).comp ?_
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun j ↦ norm_nonneg _) fun j ↦ ?_
  have hfin : ENNReal.ofReal M * eLpNorm (fun x ↦ a j x - a₀ x) 1 ν ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (memLp_one_iff_integrable.2 ((ha j).sub ha₀)).eLpNorm_ne_top
  have e : (∫ x, b x • a j x ∂ν) - ∫ x, b x • a₀ x ∂ν = ∫ x, b x • (a j x - a₀ x) ∂ν := by
    rw [← integral_sub (hint _ (ha j)) (hint _ ha₀)]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp [smul_sub])
  rw [e, ← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
  exact ENNReal.toReal_mono hfin (enorm_integral_smul_le_of_bound hb)

end TestFunctionOne

section ContDiffOne

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure] {f w : E → F}

/-- **Remark 1: `C_c^1` test functions.** If `w` is a weak derivative of `f` along `y` on `Ω`
(`HasWeakIteratedLineDerivOn ![y] f w Ω μ`) and `φ : E → ℝ` is `C^1` with compact support
contained in `Ω`, then the defining identity `∫_Ω (∂_y φ) f = −∫_Ω φ w` holds for `φ` as well:
the test functions of the definition of `W^{1,p}` may be taken in `C_c^1(Ω)` instead of
`C_c^∞(Ω)`. Proof by mollification of `f` rather than of `φ`: on a relatively compact open
`V ⊇ supp φ` the local approximation
`HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm` gives smooth `g_j` with
`g_j → f` and `∂_y g_j → w` in `L^1(V)`, the classical integration by parts
`∫ (∂_y φ) g_j = −∫ φ ∂_y g_j` (`integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`) holds
for each `j`, and both sides pass to the limit against the bounded factors `∂_y φ` and `φ`.
[brezis2011functional] §9.1, Remark 1 ("to show this, use a sequence of mollifiers"). -/
theorem HasWeakIteratedLineDerivOn.integral_smul_eq_of_contDiff_one {y : E}
    (h : HasWeakIteratedLineDerivOn ![y] f w Ω μ) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    ∫ x in (Ω : Set E), fderiv ℝ φ x y • f x ∂μ = -∫ x in (Ω : Set E), φ x • w x ∂μ := by
  -- a relatively compact open neighbourhood `V` of the support of `φ`
  obtain ⟨V, -, hVo, hφV, -, hVc, hVΩ, -⟩ :=
    hφc.exists_pos_forall_closedBall_subset Ω.isOpen hφΩ
  have hVΩ' : V ⊆ (Ω : Set E) := subset_closure.trans hVΩ
  -- the local approximation in `L^1(V)`
  obtain ⟨g, hgs, hg1, -, hgf, hgw⟩ := h.exists_seq_contDiff_tendsto_eLpNorm (p := 1)
    (locallyMemLpOn_one_iff.2 h.locallyIntegrableOn)
    (locallyMemLpOn_one_iff.2 h.locallyIntegrableOn_weakDeriv) le_rfl ENNReal.one_ne_top
    hVo hVc hVΩ
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_fin_one] at hgw
  -- the bounded factors
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous fun x ↦ fderiv ℝ φ x y :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨M, hM⟩ := (hφc.fderiv_apply ℝ y).exists_bound_of_continuous hφ'c
  obtain ⟨M', hM'⟩ := hφc.exists_bound_of_continuous hφ.continuous
  -- vanishing of the test factors off `V`
  have hφ0 : ∀ x, x ∉ V → φ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun hm ↦ hx (hφV hm)
  have hφ'0 : ∀ x, x ∉ V → fderiv ℝ φ x y = 0 := fun x hx ↦ by
    have : x ∉ tsupport (fderiv ℝ φ) := fun hm ↦ hx (hφV ((tsupport_fderiv_subset ℝ) hm))
    rw [image_eq_zero_of_notMem_tsupport this]
    rfl
  -- integrability on `V`
  have hfV : Integrable f (μ.restrict V) :=
    (h.locallyIntegrableOn.integrableOn_compact_subset hVΩ hVc).mono_set subset_closure
  have hwV : Integrable w (μ.restrict V) :=
    (h.locallyIntegrableOn_weakDeriv.integrableOn_compact_subset hVΩ hVc).mono_set
      subset_closure
  have hgV : ∀ j, Integrable (g j) (μ.restrict V) := fun j ↦ memLp_one_iff_integrable.1 (hg1 j)
  have hgdV : ∀ j, Integrable (fun x ↦ fderiv ℝ (g j) x y) (μ.restrict V) := fun j ↦ by
    have hc : Continuous fun x ↦ fderiv ℝ (g j) x y :=
      ((hgs j).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.continuousOn.integrableOn_compact hVc).mono_set subset_closure
  -- the classical identity for each `j`, on `V`
  have hclass : ∀ j, ∫ x in V, fderiv ℝ φ x y • g j x ∂μ
      = -∫ x in V, φ x • fderiv ℝ (g j) x y ∂μ := by
    intro j
    have hgd : Differentiable ℝ (g j) := (hgs j).differentiable (by simp)
    have hint : ∀ (b : E → ℝ) (c : E → F), Continuous b → (∀ x, x ∉ V → b x = 0) →
        Continuous c → Integrable (fun x ↦ b x • c x) μ := fun b c hb hb0 hc ↦ by
      refine (hb.smul hc).integrable_of_hasCompactSupport ?_
      refine hVc.of_isClosed_subset (isClosed_tsupport _) (closure_mono fun x hx ↦ ?_)
      by_contra hxV
      exact hx (by simp [hb0 x hxV])
    have key := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ) (f := φ)
      (g := g j) (v := y) (hint _ _ hφ'c hφ'0 (hgs j).continuous)
      (hint _ _ hφ.continuous hφ0 (((hgs j).continuous_fderiv (by simp)).clm_apply
        continuous_const)) (hint _ _ hφ.continuous hφ0 (hgs j).continuous)
      (fun x _ ↦ hφd.differentiableAt) (fun x _ ↦ hgd.differentiableAt)
    have e1 : ∫ x in V, fderiv ℝ φ x y • g j x ∂μ = ∫ x, fderiv ℝ φ x y • g j x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by rw [hφ'0 x hx, zero_smul]
    have e2 : ∫ x in V, φ x • fderiv ℝ (g j) x y ∂μ = ∫ x, φ x • fderiv ℝ (g j) x y ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by rw [hφ0 x hx, zero_smul]
    rw [e1, e2, key, neg_neg]
  -- the two limits
  have hlim1 : Tendsto (fun j ↦ ∫ x in V, fderiv ℝ φ x y • g j x ∂μ) atTop
      (𝓝 (∫ x in V, fderiv ℝ φ x y • f x ∂μ)) :=
    tendsto_integral_smul_of_tendsto_eLpNorm_one (fun x ↦ by simpa [Real.norm_eq_abs] using hM x)
      hφ'c.aestronglyMeasurable hgV hfV hgf
  have hlim2 : Tendsto (fun j ↦ ∫ x in V, φ x • fderiv ℝ (g j) x y ∂μ) atTop
      (𝓝 (∫ x in V, φ x • w x ∂μ)) :=
    tendsto_integral_smul_of_tendsto_eLpNorm_one (fun x ↦ by simpa [Real.norm_eq_abs] using hM' x)
      hφ.continuous.aestronglyMeasurable hgdV hwV hgw
  have hlim := tendsto_nhds_unique hlim1 (by simpa only [hclass] using hlim2.neg)
  -- back to `Ω`
  have e1 : ∫ x in (Ω : Set E), fderiv ℝ φ x y • f x ∂μ = ∫ x in V, fderiv ℝ φ x y • f x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [hφ'0 x fun hxV ↦ hx (hVΩ' hxV), zero_smul],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by rw [hφ'0 x hx, zero_smul]]
  have e2 : ∫ x in (Ω : Set E), φ x • w x ∂μ = ∫ x in V, φ x • w x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [hφ0 x fun hxV ↦ hx (hVΩ' hxV), zero_smul],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by rw [hφ0 x hx, zero_smul]]
  rw [e1, e2, hlim]

end ContDiffOne

/-! ### Cut-off functions and the zero extension of `α u` -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {α : E → ℝ}

/-- **A Sobolev cut-off for the open set `Ω`**: a smooth function `α : E → ℝ`, bounded together
with its derivative, whose support is disjoint from the frontier of `Ω`. This is the hypothesis of
the last sentence of [brezis2011functional] Chapter 9, Remark 4 (ii) — "`α ∈ C^1(ℝ^N) ∩ L^∞(ℝ^N)`
with `∇α ∈ L^∞` and `supp α ⊂ ℝ^N ∖ ∂Ω`" — with `C^∞` in place of `C^1`, and it is what the
function `θ_0` of the partition of unity satisfies in the proof of the extension theorem. It covers
the first form of that remark, `α ∈ C_c^1(Ω)`, through `IsSobolevCutoff.of_hasCompactSupport`. -/
structure IsSobolevCutoff (Ω : Opens E) (α : E → ℝ) : Prop where
  /-- A cut-off is smooth. -/
  contDiff : ContDiff ℝ ∞ α
  /-- A cut-off is bounded, together with its derivative. -/
  exists_bound : ∃ M : ℝ, ∀ x, |α x| ≤ M ∧ ‖fderiv ℝ α x‖ ≤ M
  /-- The support of a cut-off misses the frontier of `Ω`. -/
  disjoint_frontier : Disjoint (tsupport α) (frontier (Ω : Set E))

namespace IsSobolevCutoff

/-- A cut-off is continuous. -/
theorem continuous (hα : IsSobolevCutoff Ω α) : Continuous α := hα.contDiff.continuous

/-- The derivative of a cut-off in a fixed direction is smooth. -/
theorem contDiff_fderiv_apply (hα : IsSobolevCutoff Ω α) (y : E) :
    ContDiff ℝ ∞ fun x ↦ fderiv ℝ α x y :=
  (hα.contDiff.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- The bound of a cut-off may be taken nonnegative. -/
theorem exists_nonneg_bound (hα : IsSobolevCutoff Ω α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |α x| ≤ M ∧ ‖fderiv ℝ α x‖ ≤ M :=
  let ⟨M, hM⟩ := hα.exists_bound
  ⟨M, (abs_nonneg _).trans (hM 0).1, hM⟩

/-- The support of a cut-off meets the closure of `Ω` inside `Ω`. -/
theorem tsupport_inter_closure_subset (hα : IsSobolevCutoff Ω α) :
    tsupport α ∩ closure (Ω : Set E) ⊆ Ω := by
  rintro x ⟨hxα, hxc⟩
  by_contra hxΩ
  exact hα.disjoint_frontier.notMem_of_mem_left hxα ⟨hxc, fun h ↦ hxΩ (Ω.isOpen.interior_eq ▸ h)⟩

/-- A smooth function with compact support inside `Ω` is a cut-off for `Ω`: the first form of
[brezis2011functional] Chapter 9, Remark 4 (ii), `α ∈ C_c^1(Ω)`, used for the functions `θ_i`,
`i ≥ 1`, in the proof of the extension theorem. -/
theorem of_hasCompactSupport (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (hαΩ : tsupport α ⊆ Ω) : IsSobolevCutoff Ω α where
  contDiff := hα
  exists_bound := by
    obtain ⟨M₁, hM₁⟩ := hαc.exists_bound_of_continuous hα.continuous
    obtain ⟨M₂, hM₂⟩ := (hαc.fderiv ℝ).exists_bound_of_continuous (hα.continuous_fderiv (by simp))
    exact ⟨max M₁ M₂, fun x ↦ ⟨((Real.norm_eq_abs (α x)).symm.trans_le (hM₁ x)).trans
      (le_max_left _ _), (hM₂ x).trans (le_max_right _ _)⟩⟩
  disjoint_frontier := Set.disjoint_left.2 fun x hx hxf ↦
    hxf.2 (Ω.isOpen.interior_eq.symm ▸ hαΩ hx)

end IsSobolevCutoff

end Cutoff

section ZeroExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {α : E → ℝ}

/-- **The zero extension of `g u` is locally integrable on the whole space**, for `u` locally
integrable on `Ω` and a continuous `g` supported inside the support of a cut-off `α` of `Ω`: near
a point of `Ω` the function `g` is bounded and `u` integrable, near a frontier point of `Ω` the
function `g` vanishes, and outside the closure of `Ω` so does the indicator. -/
theorem IsSobolevCutoff.locallyIntegrable_indicator_smul (hα : IsSobolevCutoff Ω α) {g : E → ℝ}
    (hg : Continuous g) (hgα : tsupport g ⊆ tsupport α) {u : E → F}
    (hu : LocallyIntegrableOn u Ω μ) :
    LocallyIntegrable ((Ω : Set E).indicator fun x ↦ g x • u x) μ := by
  intro x
  by_cases hx : x ∈ (Ω : Set E)
  · obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
    have hball : closedBall x (ε / 2) ⊆ Ω :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεΩ
    refine ⟨closedBall x (ε / 2), closedBall_mem_nhds x (half_pos hε), ?_⟩
    obtain ⟨C, hC⟩ := (isCompact_closedBall x (ε / 2)).exists_bound_of_continuousOn
      hg.continuousOn
    have hint : IntegrableOn (fun z ↦ g z • u z) (closedBall x (ε / 2)) μ :=
      (hu.integrableOn_compact_subset hball (isCompact_closedBall _ _)).bdd_smul C
        hg.aestronglyMeasurable
        ((ae_restrict_mem measurableSet_closedBall).mono fun z hz ↦ hC z hz)
    exact hint.congr_fun (fun z hz ↦ (Set.indicator_of_mem (hball hz) fun x ↦ g x • u x).symm)
      measurableSet_closedBall
  · set V : Set E := (tsupport g)ᶜ ∪ (closure (Ω : Set E))ᶜ with hVdef
    have hVo : IsOpen V :=
      (isOpen_compl_iff.2 (isClosed_tsupport g)).union isClosed_closure.isOpen_compl
    refine ⟨V, hVo.mem_nhds ?_, ?_⟩
    · by_cases hxc : x ∈ closure (Ω : Set E)
      · exact Or.inl fun hxg ↦ hx (hα.tsupport_inter_closure_subset ⟨hgα hxg, hxc⟩)
      · exact Or.inr hxc
    · refine (integrable_zero _ _ _).congr ?_
      filter_upwards [self_mem_ae_restrict hVo.measurableSet] with z hzV
      by_cases hz : z ∈ (Ω : Set E)
      · rw [Set.indicator_of_mem hz]
        rcases hzV with hzg | hzc
        · rw [image_eq_zero_of_notMem_tsupport hzg, zero_smul]
          rfl
        · exact absurd (subset_closure hz) hzc
      · rw [Set.indicator_of_notMem hz]
        rfl

/-- **The zero extension of `α u` is locally integrable on the whole space** for a locally
integrable `u` on `Ω` and a cut-off `α`. -/
theorem IsSobolevCutoff.locallyIntegrable_indicator_mul (hα : IsSobolevCutoff Ω α) {u : E → F}
    (hu : LocallyIntegrableOn u Ω μ) :
    LocallyIntegrable ((Ω : Set E).indicator fun x ↦ α x • u x) μ :=
  hα.locallyIntegrable_indicator_smul hα.continuous le_rfl hu

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A cut-off times a compactly supported smooth function is a test function on `Ω`**, after a
correction off `Ω`: for a cut-off `α` of `Ω` and a smooth compactly supported `φ` there is a test
function `ψ` on `Ω` with `ψ = α φ` on `Ω`. The set `tsupport (α φ) ∩ closure Ω` is a compact subset
of `Ω`, the support of `α` missing the frontier; a smooth function `χ` equal to `1` there and
supported in `Ω` gives `ψ = χ α φ`. This is the one technical point of the zero-extension argument
of [brezis2011functional] Chapter 9, Remark 4 (ii), when `α` is merely supported off `∂Ω`. -/
theorem IsSobolevCutoff.exists_testFunction_mul_eqOn (hα : IsSobolevCutoff Ω α) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ ψ : 𝓓(Ω, ℝ), ∀ x ∈ (Ω : Set E), ψ x = α x * φ x := by
  set K : Set E := tsupport (fun x ↦ α x * φ x) ∩ closure (Ω : Set E) with hKdef
  have hK : IsCompact K :=
    (hφc.mul_left.of_isClosed_subset isClosed_closure le_rfl).inter_right isClosed_closure
  have hKΩ : K ⊆ Ω := fun x hx ↦
    hα.tsupport_inter_closure_subset ⟨tsupport_mul_subset_left hx.1, hx.2⟩
  obtain ⟨χ, hχ, hχ1, hχΩ, -⟩ := hK.exists_contDiff_eqOn_one Ω.isOpen hKΩ
  refine ⟨⟨fun x ↦ χ x * (α x * φ x), hχ.mul (hα.contDiff.mul hφ), ?_, ?_⟩, fun x hx ↦ ?_⟩
  · exact hφc.mul_left.mul_left
  · exact tsupport_mul_subset_left.trans hχΩ
  · change χ x * (α x * φ x) = α x * φ x
    by_cases hxK : x ∈ K
    · rw [hχ1 hxK, Pi.one_apply, one_mul]
    · have : α x * φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun x ↦ α x * φ x)
          fun h ↦ hxK ⟨h, subset_closure hx⟩
      rw [this, mul_zero]

omit [FiniteDimensional ℝ E] in
/-- A continuous compactly supported function `g` supported inside the support of a cut-off of
`Ω`, times a locally integrable function on `Ω`, is integrable on `Ω`: the product vanishes on `Ω`
outside the compact set `tsupport g ∩ closure Ω ⊆ Ω`. -/
theorem IsSobolevCutoff.integrableOn_mul_of_locallyIntegrableOn (hα : IsSobolevCutoff Ω α)
    {u : E → F} (hu : LocallyIntegrableOn u Ω μ) {g : E → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgα : tsupport g ⊆ tsupport α) :
    IntegrableOn (fun x ↦ g x • u x) Ω μ := by
  set K : Set E := tsupport g ∩ closure (Ω : Set E) with hKdef
  have hK : IsCompact K := hgc.inter_right isClosed_closure
  have hKΩ : K ⊆ Ω := fun x hx ↦ hα.tsupport_inter_closure_subset ⟨hgα hx.1, hx.2⟩
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  have hint : IntegrableOn (fun x ↦ g x • u x) K μ :=
    (hu.integrableOn_compact_subset hKΩ hK).bdd_smul C hg.aestronglyMeasurable
      (Eventually.of_forall hC)
  refine hint.of_forall_sdiff_eq_zero Ω.isOpen.measurableSet fun x hx ↦ ?_
  have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx.2 ⟨h, subset_closure hx.1⟩
  rw [this, zero_smul]

/-- **Extension by zero of `α u`** ([brezis2011functional] Chapter 9, Remark 4 (ii)): if `w` is
the weak derivative of `u` along `y` on `Ω`, both locally integrable on `Ω`, and `α` is a cut-off
for `Ω`, then the extension of `α u` by zero has, on the whole space, the weak derivative
`α w + (∂_y α) u` extended by zero. The proof is the book's: for a test function `φ` on the whole
space, `α φ` agrees on `Ω` with a test function `ψ` on `Ω`
(`IsSobolevCutoff.exists_testFunction_mul_eqOn`), and
`∫_Ω α u ∂_y φ = ∫_Ω u ∂_y ψ − ∫_Ω u (∂_y α) φ = −∫_Ω (α w + (∂_y α) u) φ`. Footnote 3 of the
book ("in general `ū ∉ W^{1,p}(ℝ^N)`") is why the cut-off is needed. -/
theorem HasWeakIteratedLineDerivOn.indicator_mul {y : E} {u w : E → F}
    (hu : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (hα : IsSobolevCutoff Ω α) :
    HasWeakIteratedLineDerivOn ![y] ((Ω : Set E).indicator fun x ↦ α x • u x)
      ((Ω : Set E).indicator fun x ↦ α x • w x + fderiv ℝ α x y • u x) ⊤ μ where
  locallyIntegrableOn :=
    (hα.locallyIntegrable_indicator_mul hu.locallyIntegrableOn).locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv := by
    have h1 := hα.locallyIntegrable_indicator_mul hu.locallyIntegrableOn_weakDeriv
    have h2 := hα.locallyIntegrable_indicator_smul (hα.contDiff_fderiv_apply y).continuous
      (tsupport_fderiv_apply_subset ℝ y) hu.locallyIntegrableOn
    refine ((h1.add h2).congr (Eventually.of_forall fun x ↦ ?_)).locallyIntegrableOn _
    by_cases hx : x ∈ (Ω : Set E) <;> simp [hx]
  integral_smul_eq φ := by
    obtain ⟨ψ, hψ⟩ := hα.exists_testFunction_mul_eqOn φ.contDiff φ.hasCompactSupport
    have hψd : ∀ x ∈ (Ω : Set E),
        fderiv ℝ ψ x y = fderiv ℝ α x y * φ x + α x * fderiv ℝ φ x y := by
      intro x hx
      have heq : (ψ : E → ℝ) =ᶠ[𝓝 x] fun z ↦ α z * φ z :=
        Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx) fun z hz ↦ hψ z hz
      rw [heq.fderiv_eq, fderiv_fun_mul (hα.contDiff.differentiable (by simp) x)
        (φ.contDiff.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have hmeas := Ω.isOpen.measurableSet
    have I1 : IntegrableOn (fun x ↦ fderiv ℝ ψ x y • u x) Ω μ := by
      have := (hu.integrable_smul (ψ.fderivApply y)).integrableOn (s := (Ω : Set E))
      simpa only [TestFunction.fderivApply_apply] using this
    have I2 : IntegrableOn (fun x ↦ (fderiv ℝ α x y * φ x) • u x) Ω μ :=
      hα.integrableOn_mul_of_locallyIntegrableOn hu.locallyIntegrableOn
        ((hα.contDiff_fderiv_apply y).continuous.mul φ.contDiff.continuous)
        φ.hasCompactSupport.mul_left
        (tsupport_mul_subset_left.trans (tsupport_fderiv_apply_subset ℝ y))
    have I3 : IntegrableOn (fun x ↦ ψ x • w x) Ω μ :=
      (hu.integrable_smul_weakDeriv ψ).integrableOn
    have hL : ∫ x in ((⊤ : Opens E) : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![y] •
        ((Ω : Set E).indicator fun x ↦ α x • u x) x ∂μ
        = ∫ x in (Ω : Set E), fderiv ℝ ψ x y • u x ∂μ
          - ∫ x in (Ω : Set E), (fderiv ℝ α x y * φ x) • u x ∂μ := by
      rw [Measure.restrict_coe_top, ← integral_sub I1 I2, ← integral_indicator hmeas]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      dsimp only
      by_cases hx : x ∈ (Ω : Set E)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, iteratedFDeriv_one_apply,
          Matrix.cons_val_zero, hψd x hx, add_smul, add_sub_cancel_left, smul_smul, mul_comm]
      · simp [Set.indicator_of_notMem hx]
    have hR : ∫ x in ((⊤ : Opens E) : Set E), φ x •
        ((Ω : Set E).indicator fun x ↦ α x • w x + fderiv ℝ α x y • u x) x ∂μ
        = ∫ x in (Ω : Set E), ψ x • w x ∂μ
          + ∫ x in (Ω : Set E), (fderiv ℝ α x y * φ x) • u x ∂μ := by
      rw [Measure.restrict_coe_top, ← integral_add I3 I2, ← integral_indicator hmeas]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      dsimp only
      by_cases hx : x ∈ (Ω : Set E)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hψ x hx, smul_add, smul_smul,
          smul_smul, mul_comm (φ x) (α x), mul_comm (φ x)]
      · simp [Set.indicator_of_notMem hx]
    rw [hL, hR, pow_one, neg_one_smul, neg_add, sub_eq_add_neg]
    congr 1
    have := hu.integral_smul_eq ψ
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, pow_one, neg_one_smul] at this
    exact this

end ZeroExtension

section MemIndicator

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {α : E → ℝ} {p : ℝ≥0∞}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The `L^p` norm of the zero extension of `g • u` off a measurable set `s`, for `g` bounded by
`M` on `s`, is at most `M` times the `L^p(s)` norm of `u`. -/
theorem eLpNorm_indicator_smul_le_of_forall_norm_le {s : Set E} (hs : MeasurableSet s)
    {g : E → ℝ} {M : ℝ} (hM : ∀ x ∈ s, ‖g x‖ ≤ M) (hg : AEStronglyMeasurable g (μ.restrict s))
    {u : E → F} (hu : AEStronglyMeasurable u (μ.restrict s)) :
    eLpNorm (s.indicator fun x ↦ g x • u x) p μ
      ≤ ENNReal.ofReal M * eLpNorm u p (μ.restrict s) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := fun x ↦ g x • u x) (hg.smul hu) ?_ p
  filter_upwards [self_mem_ae_restrict hs] with x hx
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The zero extension of `g • u` off a measurable set `s` lies in `L^p` when `g` is bounded and
measurable on `s` and `u ∈ L^p(s)`. -/
theorem memLp_indicator_smul_of_forall_norm_le {s : Set E} (hs : MeasurableSet s) {g : E → ℝ}
    {M : ℝ} (hM : ∀ x ∈ s, ‖g x‖ ≤ M) (hg : AEStronglyMeasurable g (μ.restrict s)) {u : E → F}
    (hu : MemLp u p (μ.restrict s)) : MemLp (s.indicator fun x ↦ g x • u x) p μ := by
  rw [memLp_indicator_iff_restrict hs]
  have hgtop : MemLp g ⊤ (μ.restrict s) :=
    memLp_top_of_bound hg M ((ae_restrict_mem hs).mono hM)
  exact hgtop.smul hu

/-- **Membership form of Remark 4 (ii)** ([brezis2011functional] Chapter 9): for
`u ∈ W^{1,p}(Ω)` and a cut-off `α` for `Ω`, the extension of `α u` by zero lies in
`W^{1,p}(E)`, the whole space. Direction by direction this is
`HasWeakIteratedLineDerivOn.indicator_mul`, after reading the multi-index `e_i` as the single
direction `b i`; the `L^p` memberships come from the bounds on `α` and `∇α`. -/
theorem MemSobolevMultiIndex.indicator_mul [IsLocallyFiniteMeasure μ] {ι : Type*} [Fintype ι]
    [LinearOrder ι] {b : Basis ι ℝ E} {u : E → F} (hp : 1 ≤ p)
    (hu : MemSobolevMultiIndex b u 1 p Ω μ) (hα : IsSobolevCutoff Ω α) :
    MemSobolevMultiIndex b ((Ω : Set E).indicator fun x ↦ α x • u x) 1 p ⊤ μ := by
  obtain ⟨M, hM0, hM⟩ := hα.exists_nonneg_bound
  have hmeas := Ω.isOpen.measurableSet
  have hαm : AEStronglyMeasurable α (μ.restrict Ω) := hα.continuous.aestronglyMeasurable
  have hαM : ∀ x ∈ (Ω : Set E), ‖α x‖ ≤ M := fun x _ ↦ (Real.norm_eq_abs _).trans_le (hM x).1
  have hmem : MemLp ((Ω : Set E).indicator fun x ↦ α x • u x) p μ :=
    memLp_indicator_smul_of_forall_norm_le hmeas hαM hαm hu.memLp
  refine ⟨by simpa [Measure.restrict_coe_top] using hmem, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    refine ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      ((hmem.locallyIntegrable hp).locallyIntegrableOn _), ?_⟩
    simpa [Measure.restrict_coe_top] using hmem
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    obtain ⟨w, hw, hwp⟩ := hu.2 (Pi.single i 1) (by simp)
    have hw' : HasWeakIteratedLineDerivOn ![b i] u w Ω μ :=
      hw.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
    refine ⟨_, (hw'.indicator_mul hα).of_perm (multiIndexTuple_single_perm (b : ι → E) i).symm,
      ?_⟩
    have h1 : MemLp ((Ω : Set E).indicator fun x ↦ α x • w x) p μ :=
      memLp_indicator_smul_of_forall_norm_le hmeas hαM hαm hwp
    have h2 : MemLp ((Ω : Set E).indicator fun x ↦ fderiv ℝ α x (b i) • u x) p μ :=
      memLp_indicator_smul_of_forall_norm_le hmeas (M := M * ‖b i‖)
        (fun x _ ↦ ((fderiv ℝ α x).le_opNorm (b i)).trans
          (mul_le_mul_of_nonneg_right (hM x).2 (norm_nonneg _)))
        (hα.contDiff_fderiv_apply (b i)).continuous.aestronglyMeasurable hu.memLp
    rw [Measure.restrict_coe_top]
    refine MemLp.ae_eq ?_ (h1.add h2)
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ (Ω : Set E) <;> simp [hx]

end MemIndicator

/-! ### Multipliers: `C^k` functions constant off a compact set, and cut-offs at every order -/

section MulAbs

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} {Ω : Opens E}

/-- A bounded measurable coefficient times an `L²(Ω)` function is in `L²(Ω)`. -/
theorem _root_.MeasureTheory.MemLp.mul_of_forall_abs_le {c w : E → ℝ}
    (hc : AEStronglyMeasurable c (μ.restrict (Ω : Set E))) {C : ℝ}
    (hC : ∀ x ∈ (Ω : Set E), |c x| ≤ C) (hw : MemLp w 2 (μ.restrict (Ω : Set E))) :
    MemLp (fun x ↦ c x * w x) 2 (μ.restrict (Ω : Set E)) :=
  hw.of_ae_norm_le_mul (hc.mul hw.aestronglyMeasurable)
    ((ae_restrict_mem Ω.isOpen.measurableSet).mono fun x hx ↦ by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hC x hx) (abs_nonneg _))

end MulAbs

section Multiplier

open SobolevMultiIndex

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-- A `C^1` function on an open set has its partial derivative `∂ᵢu = fderiv u · e_i` as weak
derivative along `e_i`. -/
theorem ContDiffOn.hasWeakIteratedLineDerivOn_single {u : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : ContDiffOn ℝ 1 u Ω) (i : Fin N) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u
      (fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1)) Ω volume := by
  have h := (ContDiffOn.hasWeakIteratedFDerivOn (μ := volume) hu (m := 1) le_rfl).lineDeriv
    ![EuclideanSpace.single i 1]
  exact h.congr_ae (Filter.EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ by
    simp [iteratedFDeriv_one_apply])

variable {Ω}

/-- **Multiplication by a `C^k` multiplier preserves `H^k(Ω)`**: for a multiplier `c`
(`IsContDiffConstOffCompact k c`) and `f ∈ H^k(Ω)`, the product `c f` lies in `H^k(Ω)`. By
induction on `k` through `memSobolevMultiIndex_succ_iff` and the product rule
`∂_i (c f) = (∂_i c) f + c (∂_i f)` (`HasWeakIteratedLineDerivOn.mul`). -/
theorem MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact (k : ℕ) :
    ∀ {c f : EuclideanSpace ℝ (Fin N) → ℝ}, IsContDiffConstOffCompact k c →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f k 2 Ω volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fun x ↦ c x * f x) k 2 Ω
      volume := by
  induction k with
  | zero =>
    intro c f hc hf
    rw [memSobolevMultiIndex_zero_iff] at hf ⊢
    obtain ⟨C, hC⟩ := hc.exists_bound
    exact MemLp.mul_of_forall_abs_le hc.continuous.aestronglyMeasurable (fun x _ ↦ hC x) hf
  | succ k ih =>
    intro c f hc hf
    obtain ⟨hf0, hfd⟩ := memSobolevMultiIndex_succ_iff.1 hf
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih (hc.of_le (Nat.le_succ k)) hf0, fun i ↦ ?_⟩
    obtain ⟨w, hw, hwm⟩ := hfd i
    rw [EuclideanSpace.basisFun_toBasis_apply] at hw ⊢
    have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    have hc1 : ContDiffOn ℝ 1 c Ω :=
      (hc.contDiff.of_le (by exact_mod_cast Nat.le_add_left 1 k)).contDiffOn
    have hcd := hc1.hasWeakIteratedLineDerivOn_single Ω i
    refine ⟨fun x ↦ fderiv ℝ c x (EuclideanSpace.single i 1) * f x + c x * w x, ?_, ?_⟩
    · exact hcd.mul rfl hw one_le_two h2 h2 (hc.continuous.continuousOn.locallyMemLpOn 2)
        ((hc.fderiv_apply _).continuous.continuousOn.locallyMemLpOn 2) hf0.memLp.locallyMemLpOn
        hwm.memLp.locallyMemLpOn
    · have h1 := ih (hc.fderiv_apply (EuclideanSpace.single i 1)) hf0
      have h2' := ih (hc.of_le (Nat.le_succ k)) hwm
      exact h1.add h2'

/-- A finite sum of products of multipliers and `H^k(Ω)` functions lies in `H^k(Ω)`. -/
theorem MemSobolevMultiIndex.sum_mul_of_isContDiffConstOffCompact {k : ℕ} {κ : Type*}
    (s : Finset κ) {c : κ → EuclideanSpace ℝ (Fin N) → ℝ}
    {f : κ → EuclideanSpace ℝ (Fin N) → ℝ} (hc : ∀ i ∈ s, IsContDiffConstOffCompact k (c i))
    (hf : ∀ i ∈ s, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (f i) k 2 Ω
      volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (fun x ↦ ∑ i ∈ s, c i x * f i x) k 2 Ω volume := by
  have := MemSobolevMultiIndex.finset_sum s (f := fun i x ↦ c i x * f i x) fun i hi ↦
    MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact k (hc i hi) (hf i hi)
  refine this.congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Finset.sum_apply]


/-- A smooth function constant off a compact set whose support misses the frontier of `Ω` is a
Sobolev cut-off for `Ω` (bounded with bounded derivative). -/
theorem IsSobolevCutoff.of_hasCompactSupport_sub {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) {κ : ℝ} (hθκ : HasCompactSupport fun x ↦ θ x - κ)
    (hθΓ : Disjoint (tsupport θ) (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    IsSobolevCutoff Ω θ where
  contDiff := hθ
  exists_bound := by
    obtain ⟨C₁, hC₁⟩ :=
      (IsContDiffConstOffCompact.mk (n := 1) (hθ.of_le (by simp)) ⟨κ, hθκ⟩).exists_bound
    obtain ⟨C₂, hC₂⟩ := (hθκ.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      ((hθ.sub contDiff_const).continuous_fderiv (by simp))
    refine ⟨max C₁ C₂, fun x ↦ ⟨(hC₁ x).trans (le_max_left _ _), ?_⟩⟩
    have := hC₂ x
    rw [fderiv_sub_const] at this
    exact this.trans (le_max_right _ _)
  disjoint_frontier := hθΓ

/-- The support of a partial derivative of `θ` misses the frontier of `Ω` when that of `θ`
does. -/
theorem tsupport_fderiv_apply_disjoint_frontier {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθΓ : Disjoint (tsupport θ) (frontier (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (y : EuclideanSpace ℝ (Fin N)) :
    Disjoint (tsupport fun x ↦ fderiv ℝ θ x y) (frontier (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hθΓ.mono_left (tsupport_fderiv_apply_subset ℝ y)

/-- **The zero extension of `θ f` at every order** ([brezis2011functional] Chapter 9, Remark 4
(ii), iterated): for a smooth `θ` constant off a compact set with support off the frontier of `Ω`
(the function `θ₀ = 1 − ∑ θᵢ` of a partition of unity) and `f ∈ H^k(Ω)`, the extension of `θ f`
by zero lies in `H^k(ℝ^N)`. Induction on `k` through `memSobolevMultiIndex_succ_iff`, the
derivative of the extension being the extension of `θ ∂_i f + (∂_i θ) f`
(`HasWeakIteratedLineDerivOn.indicator_mul`). -/
theorem MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub (k : ℕ) :
    ∀ {θ f : EuclideanSpace ℝ (Fin N) → ℝ}, ContDiff ℝ ∞ θ →
    (∃ κ : ℝ, HasCompactSupport fun x ↦ θ x - κ) →
    Disjoint (tsupport θ) (frontier (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f k 2 Ω volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦ θ x * f x) k 2 ⊤ volume := by
  induction k with
  | zero =>
    rintro θ f hθ ⟨κ, hθκ⟩ hθΓ hf
    rw [memSobolevMultiIndex_zero_iff] at hf ⊢
    have hcut := IsSobolevCutoff.of_hasCompactSupport_sub (Ω := Ω) hθ hθκ hθΓ
    obtain ⟨M, hM⟩ := hcut.exists_bound
    have := memLp_indicator_smul_of_forall_norm_le (μ := volume) Ω.isOpen.measurableSet
      (g := θ) (M := M) (fun x _ ↦ (Real.norm_eq_abs _).trans_le (hM x).1)
      hcut.continuous.aestronglyMeasurable hf
    rw [Opens.coe_top, Measure.restrict_univ]
    exact this
  | succ k ih =>
    rintro θ f hθ ⟨κ, hθκ⟩ hθΓ hf
    have hcut := IsSobolevCutoff.of_hasCompactSupport_sub (Ω := Ω) hθ hθκ hθΓ
    obtain ⟨hf0, hfd⟩ := memSobolevMultiIndex_succ_iff.1 hf
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih hθ ⟨κ, hθκ⟩ hθΓ hf0, fun i ↦ ?_⟩
    obtain ⟨w, hw, hwm⟩ := hfd i
    rw [EuclideanSpace.basisFun_toBasis_apply] at hw ⊢
    refine ⟨(Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦
      θ x * w x + fderiv ℝ θ x (EuclideanSpace.single i 1) * f x, ?_, ?_⟩
    · have := hw.indicator_mul hcut
      simpa only [smul_eq_mul] using this
    · have hθ' : ContDiff ℝ ∞ fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1) :=
        hcut.contDiff_fderiv_apply _
      have hθ'c : HasCompactSupport fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1) - 0 := by
        have := hθκ.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
        have e : (fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1) - 0)
            = fun x ↦ fderiv ℝ (fun x ↦ θ x - κ) x (EuclideanSpace.single i 1) := by
          funext x
          simp only [fderiv_sub_const, sub_zero]
        rw [e]
        exact this
      have h1 := ih hθ ⟨κ, hθκ⟩ hθΓ hwm
      have h2 := ih hθ' ⟨0, hθ'c⟩ (tsupport_fderiv_apply_disjoint_frontier hθΓ _) hf0
      refine (h1.add h2).congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.add_apply]
      by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx, add_zero]
end Multiplier

section PiLpNorm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} [Fintype ι]

/-- **The `ℓ^p` norm is monotone in each coordinate**: if `‖x i‖ ≤ ‖y i‖` for every `i`, then
`‖x‖ ≤ ‖y‖`, the two tuples possibly living in different families of spaces. -/
theorem PiLp.norm_le_norm_of_forall_norm_le {β β' : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, SeminormedAddCommGroup (β' i)] {x : PiLp p β} {y : PiLp p β'}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ciSup_mono (Finite.bddAbove_range _) h
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hP]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (h i) hP.le) (by positivity)

/-- **The `ℓ^p` norm is at most the `ℓ^1` norm**: `‖x‖ ≤ ∑ i, ‖x i‖`, by writing `x` as the sum of
its coordinates and the triangle inequality. -/
theorem PiLp.norm_le_sum_norm {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)]
    (x : PiLp p β) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  classical
  have e : x = ∑ i, PiLp.single p i (x i) := by
    refine PiLp.ext fun j ↦ ?_
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.ofLp_single]
    rw [Finset.sum_eq_single j (fun i _ hij ↦ Pi.single_eq_of_ne hij.symm _) (by simp),
      Pi.single_eq_same]
  calc ‖x‖ = ‖∑ i, PiLp.single p i (x i)‖ := by rw [← e]
    _ ≤ ∑ i, ‖PiLp.single p i (x i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ := by simp only [PiLp.norm_single]

end PiLpNorm

/-! ### `L^p` of a smaller measure -/

namespace MeasureTheory.Lp

variable {X G : Type*} [MeasurableSpace X] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ ν : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The identity `L^p(μ) → L^p(ν)` for a measure `ν ≤ μ`**, a bounded linear map of norm at most
one: an `L^p(μ)` function is in `L^p(ν)`, its `L^p(ν)` norm is at most its `L^p(μ)` norm, and
`μ`-almost everywhere equal functions are `ν`-almost everywhere equal. For `ν = μ.restrict s` this
is restriction to the set `s`; for `ν = μ.restrict Ω'` with `Ω' ⊆ Ω` and `μ = μ.restrict Ω` it is
the restriction `L^p(Ω) → L^p(Ω')` that `SobolevMultiIndex.restrictL` is built from. -/
def monoMeasureL (hνμ : ν ≤ μ) : Lp G p μ →L[ℝ] Lp G p ν :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).mono_measure hνμ).toLp f
      map_add' := fun f g ↦ by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ ((Lp.coeFn_add f g).filter_mono (ae_mono hνμ))
      map_smul' := fun c f ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ ((Lp.coeFn_smul c f).filter_mono (ae_mono hνμ)) }
    1 fun f ↦ by
      change ‖((Lp.memLp f).mono_measure hνμ).toLp f‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure _ hνμ)

/-- `MeasureTheory.Lp.monoMeasureL` is the class of the same function. -/
theorem monoMeasureL_apply (hνμ : ν ≤ μ) (f : Lp G p μ) :
    monoMeasureL hνμ f = ((Lp.memLp f).mono_measure hνμ).toLp f :=
  rfl

/-- `MeasureTheory.Lp.monoMeasureL` does not change the function, `ν`-almost everywhere. -/
theorem coeFn_monoMeasureL (hνμ : ν ≤ μ) (f : Lp G p μ) : monoMeasureL hνμ f =ᵐ[ν] f := by
  rw [monoMeasureL_apply]
  exact MemLp.coeFn_toLp _

/-- `MeasureTheory.Lp.monoMeasureL` does not increase the norm. -/
theorem norm_monoMeasureL_apply_le (hνμ : ν ≤ μ) (f : Lp G p μ) : ‖monoMeasureL hνμ f‖ ≤ ‖f‖ := by
  rw [monoMeasureL_apply, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure _ hνμ)

/-- The operator norm of `MeasureTheory.Lp.monoMeasureL` is at most one. -/
theorem norm_monoMeasureL_le (hνμ : ν ≤ μ) : ‖(monoMeasureL hνμ : Lp G p μ →L[ℝ] Lp G p ν)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end MeasureTheory.Lp

/-! ### `L^p ⊆ L^q` on a finite measure, as a bounded linear map -/

section MonoExponent

variable {α G : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

namespace MeasureTheory.Lp

variable (G p q μ) in
/-- **The inclusion `L^p(μ) ⊆ L^q(μ)` for `q ≤ p` on a finite measure**, as a bounded linear map
of norm at most `μ(univ)^{1/q − 1/p}`. -/
def monoExponentL [IsFiniteMeasure μ] (hqp : q ≤ p) : Lp G p μ →L[ℝ] Lp G q μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).mono_exponent hqp).toLp f
      map_add' := fun f g ↦ by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_add f g)
      map_smul' := fun c f ↦ by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_smul c f) }
    (μ univ ^ (1 / q.toReal - 1 / p.toReal)).toReal fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul,
        mul_comm]
      have hexp : 0 ≤ 1 / q.toReal - 1 / p.toReal := by
        rw [sub_nonneg]
        rcases eq_or_ne p ⊤ with rfl | hp
        · simp
        · exact one_div_le_one_div_of_le
            (ENNReal.toReal_pos (one_pos.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
              (ne_top_of_le_ne_top hp hqp)) (ENNReal.toReal_mono hp hqp)
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
        (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ univ))) ?_
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp (Lp.aestronglyMeasurable f)

/-- The inclusion `L^p ⊆ L^q` is the identity on functions, almost everywhere. -/
theorem coeFn_monoExponentL [IsFiniteMeasure μ] (hqp : q ≤ p) (f : Lp G p μ) :
    monoExponentL G μ p q hqp f =ᵐ[μ] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hqp)

/-- The inclusion `L^p ⊆ L^q` is injective. -/
theorem monoExponentL_injective [IsFiniteMeasure μ] (hqp : q ≤ p) :
    Function.Injective (monoExponentL G μ p q hqp) := fun f g hfg ↦
  Lp.ext ((coeFn_monoExponentL hqp f).symm.trans ((Lp.ext_iff.1 hfg).trans
    (coeFn_monoExponentL hqp g)))

/-- **`L^p(μ) ↪ L^q(μ)` is a continuous embedding for `q ≤ p` on a finite measure.** -/
theorem isContinuousEmbedding_monoExponentL [IsFiniteMeasure μ] (hqp : q ≤ p) :
    IsContinuousEmbedding (monoExponentL G μ p q hqp).toLinearMap :=
  ⟨monoExponentL_injective hqp, _, (monoExponentL G μ p q hqp).le_opNorm⟩

end MeasureTheory.Lp

end MonoExponent

/-! ### The typed operators: restriction, zero extension, inclusion -/

section Operators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω Ω' : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

omit [Fact (1 ≤ p)] in
/-- The weak derivatives of a sum are the sums of the weak derivatives. -/
theorem weakDeriv_add (u v : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    weakDeriv (u + v) α = weakDeriv u α + weakDeriv v α :=
  rfl

omit [Fact (1 ≤ p)] in
/-- The weak derivatives of a scalar multiple are the multiples of the weak derivatives. -/
theorem weakDeriv_smul (c : ℝ) (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    weakDeriv (c • u) α = c • weakDeriv u α :=
  rfl

omit [NormedSpace ℝ E] [OpensMeasurableSpace E] in
/-- The restriction of `μ.restrict Ω` to a smaller open set is smaller. -/
theorem restrict_le_restrict_of_le (h : Ω' ≤ Ω) :
    μ.restrict (Ω' : Set E) ≤ μ.restrict (Ω : Set E) :=
  Measure.restrict_mono h le_rfl

variable (F b k p μ) in
/-- The family of the restrictions to `Ω' ⊆ Ω` of the weak derivatives of `u ∈ W^{k,p}(Ω)`, as an
element of the ambient `ℓ^p` product over `Ω'`. -/
def restrictTuple (h : Ω' ≤ Ω) (u : SobolevMultiIndex F b k p Ω μ) :
    SobolevMultiIndexTuple F ι k p Ω' μ :=
  WithLp.toLp p fun α ↦ Lp.monoMeasureL (restrict_le_restrict_of_le h) (weakDeriv u α)

/-- The restricted family lies in `W^{k,p}(Ω')`: a weak derivative on `Ω` is one on `Ω'`. -/
theorem restrictTuple_mem (h : Ω' ≤ Ω) (u : SobolevMultiIndex F b k p Ω μ) :
    restrictTuple F b k p μ h u ∈ SobolevMultiIndex F b k p Ω' μ := fun α ↦
  ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u α).mono h).congr_ae
    (Lp.coeFn_monoMeasureL (restrict_le_restrict_of_le h) (weakDeriv u 0)).symm
    (Lp.coeFn_monoMeasureL (restrict_le_restrict_of_le h) (weakDeriv u α)).symm

variable (F b k p μ) in
/-- **Restriction to an open subset `Ω' ⊆ Ω` as a bounded linear map `W^{k,p}(Ω) → W^{k,p}(Ω')`**,
of norm at most one: every weak derivative is restricted, and the `ℓ^p` norm of the family does
not increase. Every "consider the restriction of `u` to `U ∩ Ω`" of [brezis2011functional] §9.2 is
this map. -/
def restrictL (h : Ω' ≤ Ω) : SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k p Ω' μ :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ ⟨restrictTuple F b k p μ h u, restrictTuple_mem h u⟩
      map_add' := fun u v ↦ Subtype.ext (PiLp.ext fun α ↦ by
        change Lp.monoMeasureL _ (weakDeriv (u + v) α)
          = Lp.monoMeasureL _ (weakDeriv u α) + Lp.monoMeasureL _ (weakDeriv v α)
        rw [weakDeriv_add, map_add])
      map_smul' := fun c u ↦ Subtype.ext (PiLp.ext fun α ↦ by
        change Lp.monoMeasureL _ (weakDeriv (c • u) α) = c • Lp.monoMeasureL _ (weakDeriv u α)
        rw [weakDeriv_smul, map_smul]) }
    1 fun u ↦ by
      rw [one_mul, ← Submodule.norm_coe, ← Submodule.norm_coe]
      exact PiLp.norm_le_norm_of_forall_norm_le fun α ↦ Lp.norm_monoMeasureL_apply_le _ _

/-- The weak derivatives of the restriction are the restrictions of the weak derivatives. -/
theorem weakDeriv_restrictL (h : Ω' ≤ Ω) (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k) :
    weakDeriv (restrictL F b k p μ h u) α =ᵐ[μ.restrict (Ω' : Set E)] weakDeriv u α :=
  Lp.coeFn_monoMeasureL _ _

/-- The function of the restriction is the function, almost everywhere on `Ω'`. -/
theorem fn_restrictL (h : Ω' ≤ Ω) (u : SobolevMultiIndex F b k p Ω μ) :
    fn (restrictL F b k p μ h u) =ᵐ[μ.restrict (Ω' : Set E)] fn u :=
  Lp.coeFn_monoMeasureL _ _

/-- Restriction does not increase the norm. -/
theorem norm_restrictL_apply_le (h : Ω' ≤ Ω) (u : SobolevMultiIndex F b k p Ω μ) :
    ‖restrictL F b k p μ h u‖ ≤ ‖u‖ := by
  rw [restrictL, LinearMap.mkContinuous_apply, ← Submodule.norm_coe, ← Submodule.norm_coe]
  exact PiLp.norm_le_norm_of_forall_norm_le fun α ↦ Lp.norm_monoMeasureL_apply_le _ _

/-- The operator norm of the restriction is at most one. -/
theorem norm_restrictL_le (h : Ω' ≤ Ω) : ‖restrictL F b k p μ h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! #### The inclusion `W^{k,p}(Ω) → L^q(Ω)` -/

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

variable (F b k p Ω μ) in
/-- **The inclusion of `W^{k,p}(Ω)` into `L^q(Ω)`**, as a linear map, given the membership: for
`h : ∀ u, MemLp (fn u) q (μ.restrict Ω)`, the map `u ↦ fn u`. Every "`W^{1,p}(Ω) ⊂ L^q(Ω)` with
continuous injection" of [brezis2011functional] §9.3 is `IsContinuousEmbedding (toLpₗ h)` for the
relevant `h`, and every compact injection of Theorem 9.16 is `IsCompactEmbedding (toLpₗ h)`, in
the vocabulary of `Numlib/Analysis/Normed/Operator/Embedding.lean`. For `q = p` it is the
underlying linear map of `SobolevMultiIndex.fnL` (`SobolevMultiIndex.toLpₗ_self`). -/
def toLpₗ (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E))) :
    SobolevMultiIndex F b k p Ω μ →ₗ[ℝ] Lp F q (μ.restrict (Ω : Set E)) where
  toFun u := (h u).toLp (fn u)
  map_add' u v := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (fn_add u v)
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (fn_smul c u)

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- `SobolevMultiIndex.toLpₗ h u` is the function of `u`, almost everywhere on `Ω`. -/
theorem toLpₗ_coeFn
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E)))
    (u : SobolevMultiIndex F b k p Ω μ) : toLpₗ F b k p Ω μ h u =ᵐ[μ.restrict (Ω : Set E)] fn u :=
  MemLp.coeFn_toLp (h u)

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- The inclusion `W^{k,p}(Ω) → L^q(Ω)` is injective: an element of `W^{k,p}(Ω)` is determined by
its function. -/
theorem toLpₗ_injective [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E))) :
    Function.Injective (toLpₗ F b k p Ω μ h) := fun u v huv ↦
  ext_of_fn_ae_eq <| (toLpₗ_coeFn h u).symm.trans <|
    (Lp.ext_iff.1 huv).trans (toLpₗ_coeFn h v)

/-- **A bound `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{k,p}(Ω)}` makes the inclusion a continuous embedding**
`W^{k,p}(Ω) ↪ L^q(Ω)`, in the sense of `IsContinuousEmbedding`. -/
theorem isContinuousEmbedding_toLpₗ [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E))) {C : ℝ}
    (hC : ∀ u, ‖toLpₗ F b k p Ω μ h u‖ ≤ C * ‖u‖) : IsContinuousEmbedding (toLpₗ F b k p Ω μ h) :=
  ⟨toLpₗ_injective h, C, hC⟩

/-- For `q = p` the inclusion is the underlying linear map of `SobolevMultiIndex.fnL`. -/
theorem toLpₗ_self : toLpₗ F b k p Ω μ (fun u ↦ memLp u) = (fnL F b k p Ω μ).toLinearMap :=
  LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn _ u).trans (Eventually.of_forall fun _ ↦ rfl))

/-- **`W^{k,p}(Ω) ↪ L^p(Ω)` is a continuous embedding**, along `SobolevMultiIndex.fnL`. -/
theorem isContinuousEmbedding_fnL [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] :
    IsContinuousEmbedding (fnL F b k p Ω μ).toLinearMap := by
  rw [← toLpₗ_self]
  exact isContinuousEmbedding_toLpₗ _ (C := 1) fun u ↦ by
    rw [toLpₗ_self, one_mul]
    exact norm_fnL_apply_le u

end SobolevMultiIndex

end Operators

section ExtendZero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [IsLocallyFiniteMeasure μ] {α : E → ℝ}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure μ] in
/-- Almost everywhere for `μ.restrict ⊤` is almost everywhere for `μ`. -/
theorem MeasureTheory.eventuallyEq_restrict_coe_top_iff {G : Type*} {f g : E → G} :
    f =ᵐ[μ.restrict ((⊤ : Opens E) : Set E)] g ↔ f =ᵐ[μ] g := by
  unfold Filter.EventuallyEq
  rw [Measure.restrict_coe_top]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure μ] in
/-- The `L^p` norm for `μ.restrict ⊤` is the `L^p` norm for `μ`. -/
theorem MeasureTheory.eLpNorm_restrict_coe_top {G : Type*} [NormedAddCommGroup G] (f : E → G)
    (p : ℝ≥0∞) : eLpNorm f p (μ.restrict ((⊤ : Opens E) : Set E)) = eLpNorm f p μ := by
  rw [Measure.restrict_coe_top]

namespace SobolevMultiIndex

/-- **The zero extension `u ↦ α u` of Remark 4 (ii) on the typed spaces**, as a function: the
element of `W^{1,p}(E)` whose function is `α u` extended by zero outside `Ω`
(`MemSobolevMultiIndex.indicator_mul` and `MemSobolevMultiIndex.exists_sobolevMultiIndex`). It is
linear (`SobolevMultiIndex.extendZeroMul_add`, `extendZeroMul_smul`) and bounded
(`SobolevMultiIndex.norm_extendZeroMul_le`); `SobolevMultiIndex.extendZeroMulL` is its bundled
form. -/
def extendZeroMul (hα : IsSobolevCutoff Ω α) (u : SobolevMultiIndex F b 1 p Ω μ) :
    SobolevMultiIndex F b 1 p ⊤ μ :=
  ((memSobolevMultiIndex u).indicator_mul Fact.out hα).exists_sobolevMultiIndex.choose

/-- The function of `SobolevMultiIndex.extendZeroMul hα u` is `α u` extended by zero. -/
theorem fn_extendZeroMul (hα : IsSobolevCutoff Ω α) (u : SobolevMultiIndex F b 1 p Ω μ) :
    fn (extendZeroMul hα u) =ᵐ[μ] (Ω : Set E).indicator fun x ↦ α x • fn u x :=
  eventuallyEq_restrict_coe_top_iff.1
    ((memSobolevMultiIndex u).indicator_mul Fact.out hα).exists_sobolevMultiIndex.choose_spec

/-- On `Ω`, the function of `SobolevMultiIndex.extendZeroMul hα u` is `α u`. -/
theorem fn_extendZeroMul_restrict (hα : IsSobolevCutoff Ω α) (u : SobolevMultiIndex F b 1 p Ω μ) :
    fn (extendZeroMul hα u) =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ α x • fn u x :=
  Filter.EventuallyEq.trans (ae_restrict_of_ae (fn_extendZeroMul hα u))
    (indicator_ae_eq_restrict Ω.isOpen.measurableSet)

/-- The partial derivative `∂_i` of the zero extension of `α u` is `α ∂_i u + (∂_i α) u` extended
by zero: the weak derivatives of `SobolevMultiIndex.extendZeroMul hα u` are the ones
`HasWeakIteratedLineDerivOn.indicator_mul` provides, by uniqueness. -/
theorem weakDeriv_extendZeroMul_single (hα : IsSobolevCutoff Ω α)
    (u : SobolevMultiIndex F b 1 p Ω μ) (i : ι) :
    weakDeriv (extendZeroMul hα u) (MultiIndexLE.single i) =ᵐ[μ] (Ω : Set E).indicator fun x ↦
      α x • weakDeriv u (MultiIndexLE.single i) x + fderiv ℝ α x (b i) • fn u x := by
  have h1 : HasWeakIteratedLineDerivOn ![b i] (fn (extendZeroMul hα u))
      (weakDeriv (extendZeroMul hα u) (MultiIndexLE.single i)) ⊤ μ :=
    (hasWeakIteratedLineDerivOn (extendZeroMul hα u) (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 : HasWeakIteratedLineDerivOn ![b i] (fn (extendZeroMul hα u))
      ((Ω : Set E).indicator fun x ↦
        α x • weakDeriv u (MultiIndexLE.single i) x + fderiv ℝ α x (b i) • fn u x) ⊤ μ := by
    exact (((hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm (b : ι → E) i)).indicator_mul hα).congr_ae
      (eventuallyEq_restrict_coe_top_iff.2 (fn_extendZeroMul hα u).symm)
      (Filter.EventuallyEq.refl _ _)
  filter_upwards [h1.ae_eq h2] with x hx using hx trivial

/-- The zero extension is additive. -/
theorem extendZeroMul_add (hα : IsSobolevCutoff Ω α) (u v : SobolevMultiIndex F b 1 p Ω μ) :
    extendZeroMul hα (u + v) = extendZeroMul hα u + extendZeroMul hα v := by
  refine ext_of_fn_ae_eq (eventuallyEq_restrict_coe_top_iff.2 ?_)
  have h1 : (fun x ↦ α x • fn (u + v) x) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ α x • fn u x + α x • fn v x := by
    filter_upwards [fn_add u v] with x hx
    rw [hx, Pi.add_apply, smul_add]
  refine (fn_extendZeroMul hα (u + v)).trans
    (((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1 h1).trans ?_)
  have h2 := eventuallyEq_restrict_coe_top_iff.1 (fn_add (extendZeroMul hα u) (extendZeroMul hα v))
  refine Filter.EventuallyEq.trans ?_ h2.symm
  filter_upwards [fn_extendZeroMul hα u, fn_extendZeroMul hα v] with x hxu hxv
  rw [Pi.add_apply, hxu, hxv]
  by_cases hx : x ∈ (Ω : Set E) <;> simp [hx]

/-- The zero extension commutes with scalar multiplication. -/
theorem extendZeroMul_smul (hα : IsSobolevCutoff Ω α) (c : ℝ) (u : SobolevMultiIndex F b 1 p Ω μ) :
    extendZeroMul hα (c • u) = c • extendZeroMul hα u := by
  refine ext_of_fn_ae_eq (eventuallyEq_restrict_coe_top_iff.2 ?_)
  have h1 : (fun x ↦ α x • fn (c • u) x) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ c • (α x • fn u x) := by
    filter_upwards [fn_smul c u] with x hx
    rw [hx, Pi.smul_apply, smul_comm]
  refine (fn_extendZeroMul hα (c • u)).trans
    (((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1 h1).trans ?_)
  have h2 := eventuallyEq_restrict_coe_top_iff.1 (fn_smul c (extendZeroMul hα u))
  refine Filter.EventuallyEq.trans ?_ h2.symm
  filter_upwards [fn_extendZeroMul hα u] with x hxu
  rw [Pi.smul_apply, hxu]
  by_cases hx : x ∈ (Ω : Set E) <;> simp [hx]

/-- **The `L^p` bound on the zero extension**: `‖α u‖_{L^p(E)} ≤ M ‖u‖_{L^p(Ω)}` for `|α| ≤ M`. -/
theorem eLpNorm_fn_extendZeroMul_le (hα : IsSobolevCutoff Ω α) {M : ℝ} (hM : ∀ x, |α x| ≤ M)
    (u : SobolevMultiIndex F b 1 p Ω μ) :
    eLpNorm (fn (extendZeroMul hα u)) p μ
      ≤ ENNReal.ofReal M * eLpNorm (fn u) p (μ.restrict (Ω : Set E)) := by
  rw [eLpNorm_congr_ae (fn_extendZeroMul hα u)]
  exact eLpNorm_indicator_smul_le_of_forall_norm_le Ω.isOpen.measurableSet
    (fun x _ ↦ (Real.norm_eq_abs _).trans_le (hM x)) hα.continuous.aestronglyMeasurable
    (memLp u).aestronglyMeasurable

/-- **The `W^{1,p}` bound on the zero extension**: for a cut-off `α` with `|α| ≤ M` and
`‖∇α‖ ≤ M`, `‖α u‖_{W^{1,p}(E)} ≤ (M + ∑ i, M (1 + ‖b i‖)) ‖u‖_{W^{1,p}(Ω)}`. This is the estimate
`‖ū_0‖_{W^{1,p}(ℝ^N)} ≤ C ‖u‖_{W^{1,p}(Ω)}` of [brezis2011functional] §9.2, proof of Theorem 9.7,
step (a). -/
theorem norm_extendZeroMul_le (hα : IsSobolevCutoff Ω α) {M : ℝ}
    (hM : ∀ x, |α x| ≤ M ∧ ‖fderiv ℝ α x‖ ≤ M) (u : SobolevMultiIndex F b 1 p Ω μ) :
    ‖extendZeroMul hα u‖ ≤ (M + ∑ i, M * (1 + ‖b i‖)) * ‖u‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0).1
  have hmeas := Ω.isOpen.measurableSet
  have hαm : AEStronglyMeasurable α (μ.restrict Ω) := hα.continuous.aestronglyMeasurable
  have hne : ∀ (c : ℝ) (v : Lp F p (μ.restrict (Ω : Set E))),
      ENNReal.ofReal c * eLpNorm v p (μ.restrict (Ω : Set E)) ≠ ⊤ := fun c v ↦
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top v)
  have h0 : ‖weakDeriv (extendZeroMul hα u) 0‖ ≤ M * ‖u‖ := by
    have h := ENNReal.toReal_mono (hne M (weakDeriv u 0))
      (eLpNorm_fn_extendZeroMul_le hα (fun x ↦ (hM x).1) u)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0] at h
    rw [Lp.norm_def, eLpNorm_restrict_coe_top]
    exact h.trans (mul_le_mul_of_nonneg_left
      ((Lp.norm_def (weakDeriv u 0)).symm.le.trans (norm_weakDeriv_le u 0)) hM0)
  have hi : ∀ i, ‖weakDeriv (extendZeroMul hα u) (MultiIndexLE.single i)‖
      ≤ M * (1 + ‖b i‖) * ‖u‖ := by
    intro i
    have hb : 0 ≤ M * ‖b i‖ := mul_nonneg hM0 (norm_nonneg _)
    have e1 : eLpNorm ((Ω : Set E).indicator fun x ↦ α x • weakDeriv u (MultiIndexLE.single i) x)
        p μ ≤ ENNReal.ofReal M * eLpNorm (weakDeriv u (MultiIndexLE.single i)) p (μ.restrict Ω) :=
      eLpNorm_indicator_smul_le_of_forall_norm_le hmeas
        (fun x _ ↦ (Real.norm_eq_abs _).trans_le (hM x).1) hαm (Lp.memLp _).aestronglyMeasurable
    have e2 : eLpNorm ((Ω : Set E).indicator fun x ↦ fderiv ℝ α x (b i) • fn u x) p μ
        ≤ ENNReal.ofReal (M * ‖b i‖) * eLpNorm (weakDeriv u 0) p (μ.restrict Ω) :=
      eLpNorm_indicator_smul_le_of_forall_norm_le hmeas
        (fun x _ ↦ ((fderiv ℝ α x).le_opNorm (b i)).trans
          (mul_le_mul_of_nonneg_right (hM x).2 (norm_nonneg _)))
        (hα.contDiff_fderiv_apply (b i)).continuous.aestronglyMeasurable
        (memLp u).aestronglyMeasurable
    have hsplit : ((Ω : Set E).indicator fun x ↦
          α x • weakDeriv u (MultiIndexLE.single i) x + fderiv ℝ α x (b i) • fn u x)
        = ((Ω : Set E).indicator fun x ↦ α x • weakDeriv u (MultiIndexLE.single i) x)
          + (Ω : Set E).indicator fun x ↦ fderiv ℝ α x (b i) • fn u x := by
      funext x
      by_cases hx : x ∈ (Ω : Set E) <;> simp [hx]
    have key : eLpNorm (weakDeriv (extendZeroMul hα u) (MultiIndexLE.single i)) p μ
        ≤ ENNReal.ofReal M * eLpNorm (weakDeriv u (MultiIndexLE.single i)) p (μ.restrict Ω)
          + ENNReal.ofReal (M * ‖b i‖) * eLpNorm (weakDeriv u 0) p (μ.restrict Ω) := by
      rw [eLpNorm_congr_ae (weakDeriv_extendZeroMul_single hα u i), hsplit]
      exact (eLpNorm_add_le Fact.out).trans (add_le_add e1 e2)
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hne _ _, hne _ _⟩) key
    rw [ENNReal.toReal_add (hne _ _) (hne _ _), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hM0, ENNReal.toReal_ofReal hb, ← Lp.norm_def, ← Lp.norm_def] at h
    rw [Lp.norm_def, eLpNorm_restrict_coe_top]
    calc (eLpNorm (weakDeriv (extendZeroMul hα u) (MultiIndexLE.single i)) p μ).toReal
        ≤ M * ‖weakDeriv u (MultiIndexLE.single i)‖ + M * ‖b i‖ * ‖weakDeriv u 0‖ := h
      _ ≤ M * ‖u‖ + M * ‖b i‖ * ‖u‖ := by
          gcongr
          · exact norm_weakDeriv_le u _
          · exact norm_weakDeriv_le u 0
      _ = M * (1 + ‖b i‖) * ‖u‖ := by ring
  calc ‖extendZeroMul hα u‖
      = ‖(extendZeroMul hα u : SobolevMultiIndexTuple F ι 1 p ⊤ μ)‖ := (Submodule.norm_coe _).symm
    _ ≤ ∑ β, ‖weakDeriv (extendZeroMul hα u) β‖ := PiLp.norm_le_sum_norm _
    _ = ‖weakDeriv (extendZeroMul hα u) 0‖
          + ∑ i, ‖weakDeriv (extendZeroMul hα u) (MultiIndexLE.single i)‖ :=
        MultiIndexLE.sum_univ_one _
    _ ≤ M * ‖u‖ + ∑ i, M * (1 + ‖b i‖) * ‖u‖ := add_le_add h0 (Finset.sum_le_sum fun i _ ↦ hi i)
    _ = (M + ∑ i, M * (1 + ‖b i‖)) * ‖u‖ := by rw [add_mul, Finset.sum_mul]

variable (F b p μ) in
/-- The zero extension `u ↦ α u` of Remark 4 (ii) as a linear map `W^{1,p}(Ω) → W^{1,p}(E)`. -/
def extendZeroMulₗ (hα : IsSobolevCutoff Ω α) :
    SobolevMultiIndex F b 1 p Ω μ →ₗ[ℝ] SobolevMultiIndex F b 1 p ⊤ μ where
  toFun := extendZeroMul hα
  map_add' := extendZeroMul_add hα
  map_smul' := extendZeroMul_smul hα

variable (F b p μ) in
/-- **The zero extension `u ↦ \overline{α u}` of [brezis2011functional] Chapter 9, Remark 4 (ii),
as a bounded linear map `W^{1,p}(Ω) → W^{1,p}(E)`**, for a cut-off `α` of `Ω`: its function is
`α u` extended by zero (`SobolevMultiIndex.fn_extendZeroMulL`), its partial derivatives are
`α ∂_i u + (∂_i α) u` extended by zero (`SobolevMultiIndex.weakDeriv_extendZeroMulL_single`), and
its norm is at most `M + ∑ i, M (1 + ‖b i‖)` for a bound `M` on `α` and `∇α`
(`SobolevMultiIndex.norm_extendZeroMulL_apply_le`). Steps (a) and (b) of the proof of the
extension theorem are this operator, with `θ_0` and with the `θ_i` on `U_i`. -/
def extendZeroMulL (hα : IsSobolevCutoff Ω α) :
    SobolevMultiIndex F b 1 p Ω μ →L[ℝ] SobolevMultiIndex F b 1 p ⊤ μ :=
  (extendZeroMulₗ F b p μ hα).mkContinuousOfExistsBound <| by
    obtain ⟨M, hM⟩ := hα.exists_bound
    exact ⟨M + ∑ i, M * (1 + ‖b i‖), norm_extendZeroMul_le hα hM⟩

/-- `SobolevMultiIndex.extendZeroMulL` is `SobolevMultiIndex.extendZeroMul`. -/
@[simp]
theorem extendZeroMulL_apply (hα : IsSobolevCutoff Ω α) (u : SobolevMultiIndex F b 1 p Ω μ) :
    extendZeroMulL F b p μ hα u = extendZeroMul hα u :=
  rfl

/-- The function of the zero extension is `α u` extended by zero outside `Ω`. -/
theorem fn_extendZeroMulL (hα : IsSobolevCutoff Ω α) (u : SobolevMultiIndex F b 1 p Ω μ) :
    fn (extendZeroMulL F b p μ hα u) =ᵐ[μ] (Ω : Set E).indicator fun x ↦ α x • fn u x :=
  fn_extendZeroMul hα u

/-- On `Ω`, the function of the zero extension is `α u`. -/
theorem fn_extendZeroMulL_restrict (hα : IsSobolevCutoff Ω α) (u : SobolevMultiIndex F b 1 p Ω μ) :
    fn (extendZeroMulL F b p μ hα u) =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ α x • fn u x :=
  fn_extendZeroMul_restrict hα u

/-- The partial derivatives of the zero extension are `α ∂_i u + (∂_i α) u` extended by zero. -/
theorem weakDeriv_extendZeroMulL_single (hα : IsSobolevCutoff Ω α)
    (u : SobolevMultiIndex F b 1 p Ω μ) (i : ι) :
    weakDeriv (extendZeroMulL F b p μ hα u) (MultiIndexLE.single i) =ᵐ[μ]
      (Ω : Set E).indicator fun x ↦
        α x • weakDeriv u (MultiIndexLE.single i) x + fderiv ℝ α x (b i) • fn u x :=
  weakDeriv_extendZeroMul_single hα u i

/-- The `L^p` bound on the zero extension: `‖α u‖_{L^p(E)} ≤ M ‖u‖_{L^p(Ω)}` for `|α| ≤ M`. -/
theorem eLpNorm_fn_extendZeroMulL_le (hα : IsSobolevCutoff Ω α) {M : ℝ} (hM : ∀ x, |α x| ≤ M)
    (u : SobolevMultiIndex F b 1 p Ω μ) :
    eLpNorm (fn (extendZeroMulL F b p μ hα u)) p μ
      ≤ ENNReal.ofReal M * eLpNorm (fn u) p (μ.restrict (Ω : Set E)) :=
  eLpNorm_fn_extendZeroMul_le hα hM u

/-- The `W^{1,p}` bound on the zero extension, with the explicit constant. -/
theorem norm_extendZeroMulL_apply_le (hα : IsSobolevCutoff Ω α) {M : ℝ}
    (hM : ∀ x, |α x| ≤ M ∧ ‖fderiv ℝ α x‖ ≤ M) (u : SobolevMultiIndex F b 1 p Ω μ) :
    ‖extendZeroMulL F b p μ hα u‖ ≤ (M + ∑ i, M * (1 + ‖b i‖)) * ‖u‖ :=
  norm_extendZeroMul_le hα hM u

end SobolevMultiIndex

end ExtendZero

section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ p)] in
/-- A continuous function lies in `L^p` of an open set with compact closure, for a measure finite
on compact sets: it is bounded there. -/
theorem _root_.Continuous.memLp_restrict_of_isCompact_closure [IsFiniteMeasureOnCompacts μ]
    {V : Set E} (hVc : IsCompact (closure V)) {G : Type*} [NormedAddCommGroup G] {h : E → G}
    (hh : Continuous h) : MemLp h p (μ.restrict V) := by
  have : IsFiniteMeasure (μ.restrict V) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hVc.measure_lt_top
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn hh.continuousOn
  exact ((memLp_top_of_bound hh.aestronglyMeasurable C
    ((ae_restrict_mem isClosed_closure.measurableSet).mono hC)).mono_measure
    (Measure.restrict_mono subset_closure le_rfl)).mono_exponent le_top

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℝ F]
  [CompleteSpace F] [Fact (1 ≤ p)] in
/-- Minkowski's inequality for a difference in a normed group, stated so that the instance search
does not go through `ESeminormedAddCommMonoid`; see `MeasureTheory.eLpNorm_add_le_of_norm`. -/
theorem _root_.MeasureTheory.eLpNorm_sub_le_of_norm {X G : Type*} [MeasurableSpace X]
    {ν : Measure X} [NormedAddCommGroup G] {a b : X → G} (hp : 1 ≤ p) :
    eLpNorm (a - b) p ν ≤ eLpNorm a p ν + eLpNorm b p ν := by
  rw [sub_eq_add_neg]
  exact (eLpNorm_add_le_of_norm hp).trans (by rw [eLpNorm_neg])

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℝ F]
  [CompleteSpace F] [Fact (1 ≤ p)] in
/-- `L^p` membership is closed under subtraction, stated for a normed group so that the instance
search does not go through the `ENorm` hierarchy; see `MeasureTheory.MemLp.add_of_norm`. -/
theorem _root_.MeasureTheory.MemLp.sub_of_norm {X G : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup G] {a b : X → G} (ha : MemLp a p ν) (hb : MemLp b p ν) :
    MemLp (a - b) p ν := by
  rw [sub_eq_add_neg]
  exact ha.add_of_norm hb.neg

namespace SobolevMultiIndex

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- The norm of `W^{k,p}(Ω)` is at most the sum of the `L^p(Ω)` norms of the weak derivatives. -/
theorem norm_le_sum_norm_weakDeriv (u : SobolevMultiIndex F b k p Ω μ) :
    ‖u‖ ≤ ∑ α, ‖weakDeriv u α‖ := by
  rw [← Submodule.norm_coe]
  exact PiLp.norm_le_sum_norm _

omit [Fact (1 ≤ p)] in
/-- The weak derivatives of an element of `W^{k,p}(Ω)` whose function is smooth are the classical
derivatives, almost everywhere on `Ω`. -/
theorem weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq [μ.IsAddHaarMeasure]
    (u : SobolevMultiIndex F b k p Ω μ) {φ : E → F} (hφ : ContDiff ℝ ∞ φ)
    (hu : fn u =ᵐ[μ.restrict (Ω : Set E)] φ) (α : MultiIndexLE ι k) :
    weakDeriv u α =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ iteratedFDeriv ℝ (∑ i, α.1 i) φ x (multiIndexTuple (b : ι → E) α.1) := by
  have h1 := (hasWeakIteratedLineDerivOn u α).congr_ae hu (Filter.EventuallyEq.refl _ _)
  have h2 := (ContDiffOn.hasWeakIteratedFDerivOn (Ω := Ω) (μ := μ) hφ.contDiffOn
    (m := ∑ i, α.1 i) (by simp)).lineDeriv (multiIndexTuple (b : ι → E) α.1)
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)

omit [Fact (1 ≤ p)] in
/-- **The `L^p` distance between two elements of `W^{k,p}(Ω)` with smooth functions**, weak
derivative by weak derivative, is bounded by the `L^p(Ω)` norm of the classical derivative of the
difference of the functions, up to the norm of the evaluation at the tuple of directions. -/
theorem eLpNorm_weakDeriv_sub_le_of_fn_ae_eq [μ.IsAddHaarMeasure]
    (u v : SobolevMultiIndex F b k p Ω μ) {φ ψ : E → F} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hu : fn u =ᵐ[μ.restrict (Ω : Set E)] φ)
    (hv : fn v =ᵐ[μ.restrict (Ω : Set E)] ψ) (α : MultiIndexLE ι k) :
    eLpNorm (weakDeriv (u - v) α) p (μ.restrict (Ω : Set E))
      ≤ ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α.1 i) ↦ E) F
          (multiIndexTuple (b : ι → E) α.1)‖ₑ
        * eLpNorm (iteratedFDeriv ℝ (∑ i, α.1 i) (φ - ψ)) p (μ.restrict (Ω : Set E)) := by
  have h : weakDeriv (u - v) α =ᵐ[μ.restrict (Ω : Set E)] fun x ↦
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α.1 i) ↦ E) F
        (multiIndexTuple (b : ι → E) α.1) (iteratedFDeriv ℝ (∑ i, α.1 i) (φ - ψ) x) := by
    have e : weakDeriv (u - v) α = weakDeriv u α - weakDeriv v α := rfl
    rw [e]
    filter_upwards [Lp.coeFn_sub (weakDeriv u α) (weakDeriv v α),
      weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq u hφ hu α,
      weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq v hψ hv α] with x hx hxu hxv
    rw [hx, Pi.sub_apply, hxu, hxv, ContinuousMultilinearMap.apply_apply,
      iteratedFDeriv_sub_apply (hφ.contDiffAt.of_le (by simp)) (hψ.contDiffAt.of_le (by simp)),
      sub_apply]
  rw [eLpNorm_congr_ae h]
  exact eLpNorm_comp_continuousLinearMap_le _ _ p

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] in
/-- The function `α • f` restricted to `Ω` has `L^p(Ω)` norm at most the `L^p(V)` norm of `f` when
`|α| ≤ 1` and `tsupport α ⊆ V`. -/
theorem _root_.MeasureTheory.eLpNorm_smul_restrict_le_of_tsupport_subset {V : Set E}
    (hV : MeasurableSet V) {α : E → ℝ} (hα : Continuous α) (hα1 : ∀ x, ‖α x‖ ≤ 1)
    (hαV : tsupport α ⊆ V) {f : E → F} (hf : AEStronglyMeasurable f (μ.restrict V)) :
    eLpNorm (fun x ↦ α x • f x) p (μ.restrict (Ω : Set E)) ≤ eLpNorm f p (μ.restrict V) := by
  have heq : (fun x ↦ α x • f x) = V.indicator fun x ↦ α x • f x := by
    funext x
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport fun h ↦ hx (hαV h), zero_smul]
  calc eLpNorm (fun x ↦ α x • f x) p (μ.restrict (Ω : Set E))
      ≤ eLpNorm (fun x ↦ α x • f x) p μ := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm (V.indicator fun x ↦ α x • f x) p μ := by rw [← heq]
    _ ≤ ENNReal.ofReal 1 * eLpNorm f p (μ.restrict V) :=
        eLpNorm_indicator_smul_le_of_forall_norm_le hV (fun x _ ↦ hα1 x)
          hα.aestronglyMeasurable hf
    _ = eLpNorm f p (μ.restrict V) := by rw [ENNReal.ofReal_one, one_mul]

variable [μ.IsAddHaarMeasure]

/-- **Lemma 9.5, at every order**: an element of `W^{k,p}(Ω)`, `1 ≤ p < ∞`, whose function
vanishes almost everywhere outside a compact subset `K` of `Ω` lies in `W_0^{k,p}(Ω)`
([brezis2011functional] Lemma 9.5, stated there for `k = 1`).

Proof: choose an open `V ⊇ K` with compact closure in `Ω` and a smooth `α` equal to `1` on `K`
and supported in `V`; the local approximation `MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`
gives smooth `g i` with `∂^m g i → ∂^m u` in `L^p(V)` for every `m ≤ k`. The test functions
`α g i` form a Cauchy sequence in `W^{k,p}(Ω)`, because `∂^m (α (g i − g j))` is bounded by the
Leibniz estimate `eLpNorm_iteratedFDeriv_smul_sub_le` in terms of the `L^p(V)` distances of the
derivatives of `g i` and `g j` — no weak Leibniz rule is used; their limit lies in the closed
subspace `W_0^{k,p}(Ω)`, and it is `u` because `α g i → α u = u` in `L^p(Ω)`. -/
theorem mem_zero_of_ae_eq_zero_compl_isCompact (hp' : p ≠ ⊤) (u : SobolevMultiIndex F b k p Ω μ)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hu : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ K → fn u x = 0) :
    u ∈ SobolevMultiIndexZero F b k p Ω μ := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  -- the open set `V` and the cut-off `α`
  obtain ⟨V, -, hVo, hKV, -, hVc, hVΩ, -⟩ := hK.exists_pos_forall_closedBall_subset Ω.isOpen hKΩ
  have hVΩ' : V ⊆ Ω := subset_closure.trans hVΩ
  obtain ⟨α, hαs, hα1, hαV, hα01⟩ := hK.exists_contDiff_eqOn_one hVo hKV
  have hαc : HasCompactSupport α :=
    hVc.of_isClosed_subset isClosed_closure (hαV.trans subset_closure)
  have hαb : ∀ x, ‖α x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hα01 x).1]
    exact (hα01 x).2
  have hαΩ : tsupport α ⊆ Ω := hαV.trans hVΩ'
  obtain ⟨M, -, hM⟩ := exists_bound_norm_iteratedFDeriv hαs hαc k
  -- `u = α u` almost everywhere on `Ω`
  have hαu : fn u =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ α x • fn u x := by
    filter_upwards [hu] with x hx
    by_cases hxK : x ∈ K
    · rw [hα1 hxK, Pi.one_apply, one_smul]
    · rw [hx hxK, smul_zero]
  -- the smooth approximants
  have hf : MemSobolev (fn u) k p Ω μ := (memSobolevMultiIndex u).memSobolev
  obtain ⟨g, hgs, hgt, hgdt⟩ := hf.exists_seq_contDiff_tendsto_eLpNorm hp hp' hVo hVc hVΩ
  -- the test functions `α g i`, as elements of `W^{k,p}(Ω)`
  have hφ : ∀ i, ∃ w ∈ testFunctions F b k p Ω μ,
      fn w =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ α x • g i x := fun i ↦
    TestFunction.exists_mem_sobolevMultiIndex_testFunctions
      ⟨fun x ↦ α x • g i x, hαs.smul (hgs i), hαc.smul_right (f' := g i),
        (tsupport_smul_subset_left α (g i)).trans hαΩ⟩
  choose w hwT hw using hφ
  -- the Leibniz estimate for the differences
  set e : ℕ → ℝ≥0∞ := fun i ↦ ∑ s ∈ Finset.range (k + 1),
    eLpNorm (iteratedFDeriv ℝ s (g i) - weakIteratedFDeriv s (fn u) Ω μ) p (μ.restrict V)
    with hedef
  have hetop : ∀ i, e i ≠ ⊤ := fun i ↦ ENNReal.sum_ne_top.2 fun s hs ↦
    (MemLp.sub_of_norm
      (((hgs i).continuous_iteratedFDeriv (m := s) (by simp)).memLp_restrict_of_isCompact_closure
        hVc)
      ((hf.memLp_weakIteratedFDeriv (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))).mono_measure
        (Measure.restrict_mono hVΩ' le_rfl))).eLpNorm_ne_top
  have het : Tendsto e atTop (𝓝 0) := by
    rw [hedef]
    simpa using tendsto_finsetSum (Finset.range (k + 1)) fun s hs ↦
      hgdt s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
  set D : ℝ≥0∞ := ENNReal.ofReal (((k : ℝ) + 1) * 2 ^ k * M) with hDdef
  set C : ℝ≥0∞ := ∑ α : MultiIndexLE ι k, ‖ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin (∑ i, α.1 i) ↦ E) F (multiIndexTuple (b : ι → E) α.1)‖ₑ with hCdef
  have hCtop : C ≠ ⊤ := ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top
  have hDtop : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdist : ∀ i j, ‖w i - w j‖ ≤ (C * (D * (e i + e j))).toReal := by
    intro i j
    have hbound : ∀ β : MultiIndexLE ι k, eLpNorm (weakDeriv (w i - w j) β) p (μ.restrict Ω)
        ≤ ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ l, β.1 l) ↦ E) F
            (multiIndexTuple (b : ι → E) β.1)‖ₑ * (D * (e i + e j)) := by
      intro β
      refine (eLpNorm_weakDeriv_sub_le_of_fn_ae_eq (w i) (w j) (hαs.smul (hgs i))
        (hαs.smul (hgs j)) (hw i) (hw j) β).trans ?_
      gcongr
      have hsub : (α • g i - α • g j : E → F) = fun y ↦ α y • (g i y - g j y) := by
        funext y
        simp [smul_sub]
      rw [hsub]
      refine (eLpNorm_iteratedFDeriv_smul_sub_le hVo hαs hαV hM (hgs i) (hgs j) hp
        β.2).trans ?_
      gcongr
      rw [hedef]
      simp only
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun s _ ↦ ?_
      have hsplit : iteratedFDeriv ℝ s (g i) - iteratedFDeriv ℝ s (g j)
          = (iteratedFDeriv ℝ s (g i) - weakIteratedFDeriv s (fn u) Ω μ)
            - (iteratedFDeriv ℝ s (g j) - weakIteratedFDeriv s (fn u) Ω μ) := by
        abel
      rw [hsplit]
      exact eLpNorm_sub_le_of_norm hp
    have hne : ∀ β : MultiIndexLE ι k, ‖ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin (∑ l, β.1 l) ↦ E) F (multiIndexTuple (b : ι → E) β.1)‖ₑ * (D * (e i + e j))
          ≠ ⊤ := fun β ↦
      ENNReal.mul_ne_top enorm_ne_top
        (ENNReal.mul_ne_top hDtop (ENNReal.add_ne_top.2 ⟨hetop i, hetop j⟩))
    calc ‖w i - w j‖ ≤ ∑ β, ‖weakDeriv (w i - w j) β‖ := norm_le_sum_norm_weakDeriv _
      _ = ∑ β, (eLpNorm (weakDeriv (w i - w j) β) p (μ.restrict Ω)).toReal := by
          simp only [Lp.norm_def]
      _ ≤ ∑ β : MultiIndexLE ι k, (‖ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin (∑ l, β.1 l) ↦ E) F (multiIndexTuple (b : ι → E) β.1)‖ₑ
              * (D * (e i + e j))).toReal :=
          Finset.sum_le_sum fun β _ ↦ ENNReal.toReal_mono (hne β) (hbound β)
      _ = (C * (D * (e i + e j))).toReal := by
          rw [hCdef, Finset.sum_mul, ENNReal.toReal_sum fun β _ ↦ hne β]
  -- the sequence is Cauchy
  have hCD : C * D ≠ ⊤ := ENNReal.mul_ne_top hCtop hDtop
  have hcauchy : CauchySeq w := by
    refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
    set c : ℝ := (C * D).toReal with hcdef
    have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
    set δ : ℝ := ε / (2 * (c + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 het (ENNReal.ofReal δ)
      (ENNReal.ofReal_pos.2 hδpos)).exists_forall_of_atTop
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_eq_norm]
    refine (hdist n N).trans_lt ?_
    calc (C * (D * (e n + e N))).toReal = c * ((e n).toReal + (e N).toReal) := by
          rw [← mul_assoc, ENNReal.toReal_mul, ENNReal.toReal_add (hetop n) (hetop N)]
      _ ≤ c * (δ + δ) := by
          gcongr
          · exact ENNReal.toReal_le_of_le_ofReal hδpos.le (hN n hn)
          · exact ENNReal.toReal_le_of_le_ofReal hδpos.le (hN N le_rfl)
      _ = c * ε / (c + 1) := by
          rw [hδ]
          field_simp
          ring
      _ < ε := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hvZ : v ∈ SobolevMultiIndexZero F b k p Ω μ :=
    SobolevMultiIndexZero.isClosed.mem_of_tendsto hv
      (Eventually.of_forall fun i ↦ SobolevMultiIndexZero.testFunctions_le (hwT i))
  -- the limit is `u`
  suffices hvu : u = v by rw [hvu]; exact hvZ
  refine fnL_injective (tendsto_nhds_unique ?_ ((fnL F b k p Ω μ).continuous.tendsto v |>.comp hv))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hkey : ∀ i, ‖fnL F b k p Ω μ (w i) - fnL F b k p Ω μ u‖
      ≤ (eLpNorm (g i - fn u) p (μ.restrict V)).toReal := by
    intro i
    have hae : (⇑(fnL F b k p Ω μ (w i) - fnL F b k p Ω μ u) : E → F) =ᵐ[μ.restrict (Ω : Set E)]
        fun x ↦ α x • (g i x - fn u x) := by
      filter_upwards [Lp.coeFn_sub (fnL F b k p Ω μ (w i)) (fnL F b k p Ω μ u), hw i, hαu]
        with x hx hxw hxu
      rw [hx, Pi.sub_apply, fnL_apply, fnL_apply, hxw, smul_sub]
      congr 1
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    refine ENNReal.toReal_mono ?_ (eLpNorm_smul_restrict_le_of_tsupport_subset hVo.measurableSet
      hαs.continuous hαb hαV ((hgs i).continuous.aestronglyMeasurable.sub
        (hf.memLp.aestronglyMeasurable.mono_measure (Measure.restrict_mono hVΩ' le_rfl))))
    exact (MemLp.sub_of_norm ((hgs i).continuous.memLp_restrict_of_isCompact_closure hVc)
      (hf.memLp.mono_measure (Measure.restrict_mono hVΩ' le_rfl))).eLpNorm_ne_top
  refine squeeze_zero (fun _ ↦ norm_nonneg _) hkey ?_
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgt
  simpa [Function.comp_def] using this

end SobolevMultiIndex

end CompactSupport

/-! ### `W^{k,p}(Ω) ⊆ W^{k,r}(Ω)` for `r ≤ p` on a set of finite measure -/

section LowerExponent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] [Fact (1 ≤ r)] in
/-- A function of `W^{k,p}(Ω)` lies in `W^{k,r}(Ω)` for `r ≤ p` when `μ Ω < ∞`
(`MemSobolev.mono_exponent` in the multi-index formulation). -/
theorem memSobolevMultiIndex_of_le (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p)
    (u : SobolevMultiIndex F b k p Ω μ) :
    MemSobolevMultiIndex b (fn u) k r Ω μ := by
  have : IsFiniteMeasure (μ.restrict (Ω : Set E)) := isFiniteMeasure_restrict.2 hΩ
  refine ⟨(SobolevMultiIndex.memLp u).mono_exponent hrp, fun α hα ↦ ?_⟩
  exact ⟨weakDeriv u ⟨α, hα⟩, hasWeakIteratedLineDerivOn u ⟨α, hα⟩,
    (Lp.memLp _).mono_exponent hrp⟩

variable (F b k p r μ) in
/-- **The inclusion `W^{k,p}(Ω) ⊆ W^{k,r}(Ω)`, `r ≤ p`, on a set of finite measure**, as an element
map: the element of `W^{k,r}(Ω)` with the same function. -/
def toLowerExponent (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) (u : SobolevMultiIndex F b k p Ω μ) :
    SobolevMultiIndex F b k r Ω μ :=
  (memSobolevMultiIndex_of_le hΩ hrp u).exists_sobolevMultiIndex.choose

omit [Fact (1 ≤ p)] in
/-- The function of `toLowerExponent u` is the function of `u`. -/
theorem fn_toLowerExponent (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) (u : SobolevMultiIndex F b k p Ω μ) :
    fn (toLowerExponent F b k p r μ hΩ hrp u) =ᵐ[μ.restrict (Ω : Set E)] fn u :=
  (memSobolevMultiIndex_of_le hΩ hrp u).exists_sobolevMultiIndex.choose_spec

omit [Fact (1 ≤ p)] in
/-- The weak derivatives of `toLowerExponent u` are those of `u`. -/
theorem weakDeriv_toLowerExponent (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k) :
    weakDeriv (toLowerExponent F b k p r μ hΩ hrp u) α =ᵐ[μ.restrict (Ω : Set E)] weakDeriv u α :=
  (ae_restrict_iff' Ω.isOpen.measurableSet).2
    (((hasWeakIteratedLineDerivOn _ α).congr_ae (fn_toLowerExponent hΩ hrp u)
      (Filter.EventuallyEq.refl _ _)).ae_eq (hasWeakIteratedLineDerivOn u α))

/-- The norm of each weak derivative of `toLowerExponent u` in `L^r(Ω)` is bounded by its norm in
`L^p(Ω)` times `μ(Ω)^{1/r − 1/p}`. -/
theorem norm_weakDeriv_toLowerExponent_le (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p)
    (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    ‖weakDeriv (toLowerExponent F b k p r μ hΩ hrp u) α‖
      ≤ (μ Ω ^ (1 / r.toReal - 1 / p.toReal)).toReal * ‖weakDeriv u α‖ := by
  have hexp : 0 ≤ 1 / r.toReal - 1 / p.toReal := by
    rw [sub_nonneg]
    rcases eq_or_ne p ⊤ with rfl | hp
    · simp
    · exact one_div_le_one_div_of_le
        (ENNReal.toReal_pos (one_pos.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ r)).ne'
          (ne_top_of_le_ne_top hp hrp)) (ENNReal.toReal_mono hp hrp)
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (weakDeriv_toLowerExponent hΩ hrp u α),
    ← ENNReal.toReal_mul, mul_comm]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _)
    (ENNReal.rpow_ne_top_of_nonneg hexp hΩ)) ?_
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict (Ω : Set E)) hrp
    (Lp.aestronglyMeasurable (weakDeriv u α))
  rwa [Measure.restrict_apply_univ] at this

/-- The inclusion `W^{k,p}(Ω) ⊆ W^{k,r}(Ω)` is bounded: `‖u‖_{k,r} ≤ C ‖u‖_{k,p}` with
`C = (#α) μ(Ω)^{1/r − 1/p}`. -/
theorem norm_toLowerExponent_le (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) (u : SobolevMultiIndex F b k p Ω μ) :
    ‖toLowerExponent F b k p r μ hΩ hrp u‖
      ≤ Fintype.card (MultiIndexLE ι k) * (μ Ω ^ (1 / r.toReal - 1 / p.toReal)).toReal * ‖u‖ := by
  refine (norm_le_sum_norm_weakDeriv _).trans ?_
  calc ∑ α, ‖weakDeriv (toLowerExponent F b k p r μ hΩ hrp u) α‖
      ≤ ∑ _α : MultiIndexLE ι k, (μ Ω ^ (1 / r.toReal - 1 / p.toReal)).toReal * ‖u‖ :=
        Finset.sum_le_sum fun α _ ↦ (norm_weakDeriv_toLowerExponent_le hΩ hrp u α).trans
          (mul_le_mul_of_nonneg_left (norm_weakDeriv_le u α) ENNReal.toReal_nonneg)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

variable (F b k p r μ) in
/-- **The inclusion `W^{k,p}(Ω) → W^{k,r}(Ω)`, `r ≤ p`, on a set of finite measure, as a bounded
linear map** (`MemSobolev.mono_exponent` typed); the device by which [brezis2011functional]
Theorem 9.16 reduces the case `p = N` to `p < N`. -/
def toLowerExponentL (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) :
    SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k r Ω μ :=
  LinearMap.mkContinuous
    { toFun := toLowerExponent F b k p r μ hΩ hrp
      map_add' := fun u v ↦ ext_of_fn_ae_eq <| by
        refine (fn_toLowerExponent hΩ hrp (u + v)).trans ((fn_add u v).trans ?_)
        refine ((fn_toLowerExponent hΩ hrp u).add (fn_toLowerExponent hΩ hrp v)).symm.trans ?_
        exact (fn_add _ _).symm
      map_smul' := fun c u ↦ ext_of_fn_ae_eq <| by
        refine (fn_toLowerExponent hΩ hrp (c • u)).trans ((fn_smul c u).trans ?_)
        refine ((fn_toLowerExponent hΩ hrp u).const_smul c).symm.trans ?_
        exact (fn_smul _ _).symm }
    _ (norm_toLowerExponent_le hΩ hrp)

/-- The function of `toLowerExponentL u` is the function of `u`. -/
theorem fn_toLowerExponentL (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) (u : SobolevMultiIndex F b k p Ω μ) :
    fn (toLowerExponentL F b k p r μ hΩ hrp u) =ᵐ[μ.restrict (Ω : Set E)] fn u :=
  fn_toLowerExponent hΩ hrp u

/-- `toLowerExponentL` is injective. -/
theorem toLowerExponentL_injective (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) :
    Function.Injective (toLowerExponentL F b k p r μ hΩ hrp) := fun u v huv ↦ by
  refine ext_of_fn_ae_eq ((fn_toLowerExponentL hΩ hrp u).symm.trans ?_)
  rw [huv]
  exact fn_toLowerExponentL hΩ hrp v

/-- **`W^{k,p}(Ω) ↪ W^{k,r}(Ω)` is a continuous embedding** for `r ≤ p` on a set of finite
measure. -/
theorem isContinuousEmbedding_toLowerExponentL (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) :
    IsContinuousEmbedding (toLowerExponentL F b k p r μ hΩ hrp).toLinearMap :=
  ⟨toLowerExponentL_injective hΩ hrp, _, (toLowerExponentL F b k p r μ hΩ hrp).le_opNorm⟩

end SobolevMultiIndex

end LowerExponent

/-! ### Forgetting orders, and the partial derivatives as maps between Sobolev spaces -/

section LowerOrder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k k' : ℕ} {p : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- The `ℓ^p` norm of an element of `W^{k,p}(Ω)` is at most the number of multi-indices of
order at most `k` times a common bound on its components. -/
theorem norm_le_card_mul_of_forall_norm_weakDeriv_le [Fact (1 ≤ p)]
    (u : SobolevMultiIndex F b k p Ω μ) {M : ℝ} (h : ∀ α, ‖weakDeriv u α‖ ≤ M) :
    ‖u‖ ≤ Fintype.card (MultiIndexLE ι k) * M := by
  rw [← Submodule.norm_coe]
  refine (PiLp.norm_le_sum_norm _).trans ?_
  calc ∑ α : MultiIndexLE ι k, ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) α‖
      ≤ ∑ _α : MultiIndexLE ι k, M := Finset.sum_le_sum fun α _ ↦ h α
    _ = Fintype.card (MultiIndexLE ι k) * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable (F b p Ω μ) in
/-- **Forgetting the top-order components**: an element of `W^{k,p}(Ω)` read in `W^{k',p}(Ω)` for
`k' ≤ k`, the typed form of `MemSobolevMultiIndex.mono_order`. -/
def toLowerOrder (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ) :
    SobolevMultiIndex F b k' p Ω μ :=
  ⟨WithLp.toLp p fun α : MultiIndexLE ι k' ↦ weakDeriv u ⟨α.1, α.2.trans hk⟩,
    fun α ↦ hasWeakIteratedLineDerivOn u ⟨α.1, α.2.trans hk⟩⟩

/-- The components of `toLowerOrder u` are those of `u`. -/
@[simp]
theorem weakDeriv_toLowerOrder (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k') :
    weakDeriv (toLowerOrder F b p Ω μ hk u) α = weakDeriv u ⟨α.1, α.2.trans hk⟩ :=
  rfl

/-- The function of `toLowerOrder u` is the function of `u`. -/
@[simp]
theorem fn_toLowerOrder (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ) :
    fn (toLowerOrder F b p Ω μ hk u) = fn u :=
  rfl

/-- Forgetting orders is additive. -/
theorem toLowerOrder_add (hk : k' ≤ k) (u v : SobolevMultiIndex F b k p Ω μ) :
    toLowerOrder F b p Ω μ hk (u + v) = toLowerOrder F b p Ω μ hk u + toLowerOrder F b p Ω μ hk v :=
  rfl

/-- Forgetting orders commutes with scalar multiplication. -/
theorem toLowerOrder_smul (hk : k' ≤ k) (c : ℝ) (u : SobolevMultiIndex F b k p Ω μ) :
    toLowerOrder F b p Ω μ hk (c • u) = c • toLowerOrder F b p Ω μ hk u :=
  rfl

/-- Forgetting components does not increase the `ℓ^p` norm. -/
theorem norm_toLowerOrder_le [Fact (1 ≤ p)] (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ) :
    ‖toLowerOrder F b p Ω μ hk u‖ ≤ ‖u‖ := by
  classical
  rw [← Submodule.norm_coe, ← Submodule.norm_coe]
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    refine ciSup_le fun α ↦ ?_
    exact le_ciSup (Finite.bddAbove_range fun β : MultiIndexLE ι k ↦
      ‖(u : SobolevMultiIndexTuple F ι k ⊤ Ω μ) β‖) (⟨α.1, α.2.trans hk⟩ : MultiIndexLE ι k)
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hP]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      ?_ (by positivity)
    calc ∑ α : MultiIndexLE ι k',
          ‖(toLowerOrder F b p Ω μ hk u : SobolevMultiIndexTuple F ι k' p Ω μ) α‖ ^ p.toReal
        = ∑ β ∈ Finset.univ.image
            (fun α : MultiIndexLE ι k' ↦ (⟨α.1, α.2.trans hk⟩ : MultiIndexLE ι k)),
            ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) β‖ ^ p.toReal := by
          rw [Finset.sum_image (MultiIndexLE.castLE_injective hk).injOn]
          rfl
      _ ≤ ∑ β : MultiIndexLE ι k, ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) β‖ ^ p.toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

variable (F b p Ω μ) in
/-- **The inclusion `W^{k,p}(Ω) → W^{k',p}(Ω)`, `k' ≤ k`, as a bounded linear map** of norm at most
one: forget the components of order above `k'`. -/
def toLowerOrderL [Fact (1 ≤ p)] (hk : k' ≤ k) :
    SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k' p Ω μ :=
  LinearMap.mkContinuous
    { toFun := toLowerOrder F b p Ω μ hk
      map_add' := toLowerOrder_add hk
      map_smul' := toLowerOrder_smul hk }
    1 fun u ↦ by rw [one_mul]; exact norm_toLowerOrder_le hk u

/-- `SobolevMultiIndex.toLowerOrderL` is `SobolevMultiIndex.toLowerOrder`. -/
@[simp]
theorem toLowerOrderL_apply [Fact (1 ≤ p)] (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ) :
    toLowerOrderL F b p Ω μ hk u = toLowerOrder F b p Ω μ hk u :=
  rfl

/-- The operator norm of `SobolevMultiIndex.toLowerOrderL` is at most one. -/
theorem norm_toLowerOrderL_le [Fact (1 ≤ p)] (hk : k' ≤ k) : ‖toLowerOrderL F b p Ω μ hk‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The inclusion `W^{k,p}(Ω) → L^p(Ω)` factors through `W^{k',p}(Ω)` for `k' ≤ k`. -/
theorem fnL_comp_toLowerOrderL [Fact (1 ≤ p)] (hk : k' ≤ k) :
    (fnL F b k' p Ω μ).comp (toLowerOrderL F b p Ω μ hk) = fnL F b k p Ω μ :=
  rfl

/-- `SobolevMultiIndex.toLowerOrderL` is injective: an element is determined by its function. -/
theorem toLowerOrderL_injective [Fact (1 ≤ p)] [FiniteDimensional ℝ E] [BorelSpace E]
    [CompleteSpace F] (hk : k' ≤ k) :
    Function.Injective (toLowerOrderL F b p Ω μ hk) := fun u v huv ↦ by
  have h1 : fn (toLowerOrderL F b p Ω μ hk u) = fn (toLowerOrderL F b p Ω μ hk v) :=
    congrArg fn huv
  exact ext_of_fn_ae_eq (by rw [show fn u = fn v from h1])

/-- **The `ℓ^p` norm is monotone under an injective reindexing of the components**: if the
components of `v ∈ W^{k',p}(Ω)` are components of `u ∈ W^{k,p}(Ω)` read along an injection of
the multi-indices, then `‖v‖ ≤ ‖u‖`. -/
theorem norm_le_norm_of_injective [Fact (1 ≤ p)] {u : SobolevMultiIndex F b k p Ω μ}
    {v : SobolevMultiIndex F b k' p Ω μ} {e : MultiIndexLE ι k' → MultiIndexLE ι k}
    (he : Function.Injective e) (h : ∀ α, weakDeriv v α = weakDeriv u (e α)) : ‖v‖ ≤ ‖u‖ := by
  classical
  rw [← Submodule.norm_coe, ← Submodule.norm_coe]
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    refine ciSup_le fun α ↦ ?_
    rw [show (v : SobolevMultiIndexTuple F ι k' ⊤ Ω μ) α = weakDeriv u (e α) from h α]
    exact le_ciSup (Finite.bddAbove_range fun β : MultiIndexLE ι k ↦
      ‖(u : SobolevMultiIndexTuple F ι k ⊤ Ω μ) β‖) (e α)
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hP]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      ?_ (by positivity)
    calc ∑ α : MultiIndexLE ι k', ‖(v : SobolevMultiIndexTuple F ι k' p Ω μ) α‖ ^ p.toReal
        = ∑ β ∈ Finset.univ.image e, ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) β‖ ^ p.toReal := by
          rw [Finset.sum_image he.injOn]
          exact Finset.sum_congr rfl fun α _ ↦ by
            rw [show (v : SobolevMultiIndexTuple F ι k' p Ω μ) α = weakDeriv u (e α) from h α]
            rfl
      _ ≤ ∑ β : MultiIndexLE ι k, ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) β‖ ^ p.toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

section PartialDeriv

/-- The weak derivative `∂_i u` of `u ∈ W^{k+1,p}(Ω)` along the basis direction `b i` is the
component of `u` at `e_i`. -/
theorem hasWeakIteratedLineDerivOn_single (u : SobolevMultiIndex F b (k + 1) p Ω μ) (i : ι) :
    HasWeakIteratedLineDerivOn ![b i] (fn u) (weakDeriv u (MultiIndexLE.singleLE i)) Ω μ :=
  (hasWeakIteratedLineDerivOn u (MultiIndexLE.singleLE i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)

/-- The component of `u` at `α + e_i` is the weak derivative `∂^α` of the component at `e_i`. -/
theorem hasWeakIteratedLineDerivOn_addSingle (u : SobolevMultiIndex F b (k + 1) p Ω μ) (i : ι)
    (α : MultiIndexLE ι k) :
    HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1)
      (weakDeriv u (MultiIndexLE.singleLE i)) (weakDeriv u (MultiIndexLE.addSingle i α)) Ω μ :=
  (hasWeakIteratedLineDerivOn_single u i).of_cons'
    ((hasWeakIteratedLineDerivOn u (MultiIndexLE.addSingle i α)).of_perm
      (multiIndexTuple_add_single_perm (b : ι → E) α.1 i).symm)

variable (F b p Ω μ) in
/-- **The partial derivative `∂_i` as a map `W^{k+1,p}(Ω) → W^{k,p}(Ω)`**: the element whose
component at `α` is the component of `u` at `α + e_i`; its function is the weak derivative
`∂_i u`. -/
def partialDeriv (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    SobolevMultiIndex F b k p Ω μ :=
  ⟨WithLp.toLp p fun α : MultiIndexLE ι k ↦ weakDeriv u (MultiIndexLE.addSingle i α), fun α ↦ by
    have e : (weakDeriv u (MultiIndexLE.addSingle i (0 : MultiIndexLE ι k)) : E → F)
        = weakDeriv u (MultiIndexLE.singleLE i) := by
      rw [MultiIndexLE.addSingle_zero]
    change HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1)
      (weakDeriv u (MultiIndexLE.addSingle i (0 : MultiIndexLE ι k)))
      (weakDeriv u (MultiIndexLE.addSingle i α)) Ω μ
    rw [e]
    exact hasWeakIteratedLineDerivOn_addSingle u i α⟩

/-- The components of `∂_i u` are the components of `u` at `α + e_i`. -/
@[simp]
theorem weakDeriv_partialDeriv (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ)
    (α : MultiIndexLE ι k) :
    weakDeriv (partialDeriv F b p Ω μ i u) α = weakDeriv u (MultiIndexLE.addSingle i α) :=
  rfl

/-- The function of `∂_i u` is the component of `u` at `e_i`. -/
theorem fn_partialDeriv (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    fn (partialDeriv F b p Ω μ i u) = weakDeriv u (MultiIndexLE.singleLE i) := by
  change (weakDeriv u (MultiIndexLE.addSingle i (0 : MultiIndexLE ι k)) : E → F) = _
  rw [MultiIndexLE.addSingle_zero]

/-- The function of `partialDeriv i u` is the weak derivative of `fn u` along `b i`. -/
theorem hasWeakIteratedLineDerivOn_fn_partialDeriv (i : ι)
    (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    HasWeakIteratedLineDerivOn ![b i] (fn u) (fn (partialDeriv F b p Ω μ i u)) Ω μ := by
  rw [fn_partialDeriv]
  exact hasWeakIteratedLineDerivOn_single u i

/-- The partial derivative is additive. -/
theorem partialDeriv_add (i : ι) (u v : SobolevMultiIndex F b (k + 1) p Ω μ) :
    partialDeriv F b p Ω μ i (u + v) = partialDeriv F b p Ω μ i u + partialDeriv F b p Ω μ i v :=
  rfl

/-- The partial derivative commutes with scalar multiplication. -/
theorem partialDeriv_smul (i : ι) (c : ℝ) (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    partialDeriv F b p Ω μ i (c • u) = c • partialDeriv F b p Ω μ i u :=
  rfl

/-- `‖∂_i u‖_{W^{k,p}} ≤ ‖u‖_{W^{k+1,p}}`. -/
theorem norm_partialDeriv_le [Fact (1 ≤ p)] (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    ‖partialDeriv F b p Ω μ i u‖ ≤ ‖u‖ :=
  norm_le_norm_of_injective (MultiIndexLE.addSingle_injective i) fun _ ↦ rfl

variable (F b p Ω μ) in
/-- **The partial derivative `∂_i : W^{k+1,p}(Ω) → W^{k,p}(Ω)` as a bounded linear map** of norm
at most one. -/
def partialDerivL [Fact (1 ≤ p)] (i : ι) :
    SobolevMultiIndex F b (k + 1) p Ω μ →L[ℝ] SobolevMultiIndex F b k p Ω μ :=
  LinearMap.mkContinuous
    { toFun := partialDeriv F b p Ω μ i
      map_add' := partialDeriv_add i
      map_smul' := partialDeriv_smul i }
    1 fun u ↦ by rw [one_mul]; exact norm_partialDeriv_le i u

/-- `SobolevMultiIndex.partialDerivL` is `SobolevMultiIndex.partialDeriv`. -/
@[simp]
theorem partialDerivL_apply [Fact (1 ≤ p)] (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    partialDerivL F b p Ω μ i u = partialDeriv F b p Ω μ i u :=
  rfl

/-- The operator norm of `SobolevMultiIndex.partialDerivL` is at most one. -/
theorem norm_partialDerivL_le [Fact (1 ≤ p)] (i : ι) :
    ‖(partialDerivL F b p Ω μ i :
      SobolevMultiIndex F b (k + 1) p Ω μ →L[ℝ] SobolevMultiIndex F b k p Ω μ)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end PartialDeriv

end SobolevMultiIndex

end LowerOrder

section Loc

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {f : E → F} {k : ℕ} {p : ℝ≥0∞}
  {Ω Ω' : Opens E} {μ : Measure E}

omit [OpensMeasurableSpace E] in
/-- Membership of `W^{k,p}` is inherited by open subsets. -/
theorem MemSobolevMultiIndex.mono_set (h : MemSobolevMultiIndex b f k p Ω μ) (hΩ : Ω' ≤ Ω) :
    MemSobolevMultiIndex b f k p Ω' μ :=
  ⟨h.1.mono_measure (Measure.restrict_mono hΩ le_rfl), fun α hα ↦
    let ⟨w, hw, hwp⟩ := h.2 α hα
    ⟨w, hw.mono hΩ, hwp.mono_measure (Measure.restrict_mono hΩ le_rfl)⟩⟩

variable (b f k p Ω μ) in
/-- **The local Sobolev space `W^{k,p}_loc(Ω)`**: `f` lies in `W^{k,p}(ω)` for every open `ω`
whose closure is a compact subset of `Ω` (`ω ⋐ Ω`). This is the reading "`u ∈ H^{m+2}(ω)` for
every `ω ⊂⊂ Ω`" of [brezis2011functional] Chapter 9, Remark 25. -/
def MemSobolevMultiIndexLoc : Prop :=
  ∀ V : Opens E, IsCompact (closure (V : Set E)) → closure (V : Set E) ⊆ Ω →
    MemSobolevMultiIndex b f k p V μ

omit [OpensMeasurableSpace E] in
/-- A function of `W^{k,p}(Ω)` lies in `W^{k,p}_loc(Ω)`. -/
theorem MemSobolevMultiIndex.memSobolevMultiIndexLoc (h : MemSobolevMultiIndex b f k p Ω μ) :
    MemSobolevMultiIndexLoc b f k p Ω μ := fun _ _ hV ↦
  h.mono_set (subset_closure.trans hV)

namespace MemSobolevMultiIndexLoc

omit [OpensMeasurableSpace E] in
/-- `W^{k,p}_loc(Ω)` decreases as the order increases. -/
theorem mono_order {k' : ℕ} (h : MemSobolevMultiIndexLoc b f k p Ω μ) (hk : k' ≤ k) :
    MemSobolevMultiIndexLoc b f k' p Ω μ := fun V hVc hVΩ ↦
  (h V hVc hVΩ).mono_order hk

omit [OpensMeasurableSpace E] in
/-- `W^{k,p}_loc` is inherited by open subsets. -/
theorem mono_set (h : MemSobolevMultiIndexLoc b f k p Ω μ) (hΩ : Ω' ≤ Ω) :
    MemSobolevMultiIndexLoc b f k p Ω' μ := fun V hVc hVΩ ↦
  h V hVc (hVΩ.trans hΩ)

omit [OpensMeasurableSpace E] in
/-- Membership of `W^{k,p}_loc(Ω)` only sees the function up to a null set of `Ω`. -/
theorem congr_ae {f' : E → F} (h : MemSobolevMultiIndexLoc b f k p Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') : MemSobolevMultiIndexLoc b f' k p Ω μ :=
  fun V hVc hVΩ ↦ (h V hVc hVΩ).congr_ae
    (ae_mono (Measure.restrict_mono (subset_closure.trans hVΩ) le_rfl) hf)

end MemSobolevMultiIndexLoc

section Classical

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

/-- **A `C^n` function on `Ω` lies in `W^{m,p}_loc(Ω)` for every `m ≤ n`**: on an open `V` with
compact closure in `Ω`, its derivatives of order `≤ m` are continuous on the compact `closure V`,
hence bounded, hence in `L^p(V)`, and the classical derivatives are the weak ones
(`ContDiffOn.hasWeakIteratedFDerivOn`). -/
theorem _root_.ContDiffOn.memSobolevMultiIndexLoc {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f Ω)
    {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n) : MemSobolevMultiIndexLoc b f m p Ω μ := by
  intro V hVc hVΩ
  have hVm : MeasurableSet (V : Set E) := V.isOpen.measurableSet
  have hVΩ' : (V : Set E) ⊆ Ω := subset_closure.trans hVΩ
  have : IsFiniteMeasure (μ.restrict (V : Set E)) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hVc.measure_lt_top).ne
  have hbound : ∀ j : ℕ, (j : WithTop ℕ∞) ≤ n →
      MemLp (iteratedFDeriv ℝ j f) p (μ.restrict (V : Set E)) := by
    intro j hj
    have hc : ContinuousOn (iteratedFDeriv ℝ j f) Ω := hf.continuousOn_iteratedFDeriv hj
    obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn (hc.mono hVΩ)
    refine MemLp.of_bound ((hc.mono hVΩ').aestronglyMeasurable hVm) C ?_
    filter_upwards [ae_restrict_mem hVm] with x hx
    exact hC x (subset_closure hx)
  have hf0 : MemLp f p (μ.restrict (V : Set E)) := by
    obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn (hf.continuousOn.mono hVΩ)
    refine MemLp.of_bound ((hf.continuousOn.mono hVΩ').aestronglyMeasurable hVm) C ?_
    filter_upwards [ae_restrict_mem hVm] with x hx
    exact hC x (subset_closure hx)
  refine MemSobolev.memSobolevMultiIndex ⟨hf0, fun j hj ↦ ?_⟩
  have hj' : (j : WithTop ℕ∞) ≤ n := (by exact_mod_cast hj : (j : WithTop ℕ∞) ≤ m).trans hm
  exact ⟨iteratedFDeriv ℝ j f, (hf.mono hVΩ').hasWeakIteratedFDerivOn hj', hbound j hj'⟩

end Classical


end Loc

/-! ### Extension domains

The abstract hypothesis under which the embedding and compactness theorems on a domain are stated
once: a bounded linear extension operator `W^{1,p}(Ω) → W^{1,p}(ℝ^N)` exists on the subspace `S`.
Its instances are the half space, the `C^1` chart domains with bounded boundary (the extension
theorem), and `W_0^{1,p}(Ω)` on any open set (extension by zero). -/

section ExtensionDomain

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **A subspace `S` of `W^{1,p}(Ω)` has a Sobolev extension operator** when there is a bounded
linear `P : S → W^{1,p}(ℝ^N)` with `P u = u` almost everywhere on `Ω`. This is the standing
hypothesis of [brezis2011functional] §9.3.B in the form its consequences use: the `L^p` bound of
Theorem 9.7 is not part of it, only the `W^{1,p}` bound. The subspace form is the primary one
because `W_0^{1,p}(Ω)` has such an operator on every open set (extension by zero, Remark 20) while
`W^{1,p}(Ω)` itself needs a regular boundary. -/
def HasSobolevExtensionOn (S : Submodule ℝ (SobolevEuclidean N 1 p Ω)) : Prop :=
  ∃ P : S →L[ℝ] SobolevEuclidean N 1 p ⊤, ∀ u : S,
    SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)

variable (N p Ω) in
/-- **`Ω` is a `W^{1,p}`-extension domain**: all of `W^{1,p}(Ω)` has a Sobolev extension operator
(`HasSobolevExtensionOn ⊤`), the standard name of the literature for the standing hypothesis of
[brezis2011functional] §9.3.B. Its instances are the half space, and the `C^1` chart domains with
bounded boundary of Theorem 9.7; a Lipschitz domain would enter through one more instance. -/
def IsSobolevExtensionDomain : Prop :=
  HasSobolevExtensionOn (⊤ : Submodule ℝ (SobolevEuclidean N 1 p Ω))

end ExtensionDomain

/-! ### Comparison with the tensor norm at order one -/

section Compare

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

omit [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- The Sobolev norm only sees the function up to a null set of `Ω`: the chosen weak derivatives
of two almost everywhere equal functions are almost everywhere equal, or both absent. -/
theorem sobolevNorm_congr_ae {k : ℕ} {f g : E → F} (hfg : f =ᵐ[μ.restrict (Ω : Set E)] g) :
    sobolevNorm f k p Ω μ = sobolevNorm g k p Ω μ := by
  have key : ∀ n : ℕ, eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict (Ω : Set E))
      = eLpNorm (weakIteratedFDeriv n g Ω μ) p (μ.restrict (Ω : Set E)) := by
    intro n
    by_cases h : ∃ w, HasWeakIteratedFDerivOn n f w Ω μ
    · obtain ⟨w, hw⟩ := h
      rw [eLpNorm_congr_ae
          ((ae_restrict_iff' Ω.isOpen.measurableSet).2 hw.weakIteratedFDeriv_ae_eq),
        eLpNorm_congr_ae ((ae_restrict_iff' Ω.isOpen.measurableSet).2
          (hw.congr_ae hfg (Filter.EventuallyEq.refl _ _)).weakIteratedFDeriv_ae_eq)]
    · have h' : ¬ ∃ w, HasWeakIteratedFDerivOn n g w Ω μ := fun ⟨w, hw⟩ ↦
        h ⟨w, hw.congr_ae hfg.symm (Filter.EventuallyEq.refl _ _)⟩
      simp only [weakIteratedFDeriv, dite_eq_right h, dite_eq_right h']
  rcases eq_or_ne p ⊤ with rfl | hp
  · simp only [sobolevNorm, key, ↓reduceIte]
  · simp only [sobolevNorm, hp, key, ↓reduceIte]

namespace SobolevMultiIndex

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- The function of a difference is the difference of the functions, almost everywhere on `Ω`. -/
theorem fn_sub {k : ℕ} (u v : SobolevMultiIndex F b k p Ω μ) :
    fn (u - v) =ᵐ[μ.restrict (Ω : Set E)] fn u - fn v :=
  Lp.coeFn_sub (weakDeriv u 0) (weakDeriv v 0)

/-- **The norm of `W^{1,p}(Ω)` in the multi-index formulation is bounded by the tensor Sobolev
norm** of `Numlib/Analysis/Sobolev/Domain.lean`, up to the constant `1 + ∑ i, ‖ev_{b i}‖`: the
function is the derivative of order `0`, and each partial derivative `∂_i u` is the weak
derivative tensor of order one evaluated at `b i`. -/
theorem ofReal_norm_le_sobolevNorm (hp' : p ≠ ⊤) (u : SobolevMultiIndex F b 1 p Ω μ) :
    ENNReal.ofReal ‖u‖ ≤ (1 + ∑ i, ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ E) F
      ![b i]‖ₑ) * sobolevNorm (fn u) 1 p Ω μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hf : MemSobolev (fn u) 1 p Ω μ := (memSobolevMultiIndex u).memSobolev
  have h0 : eLpNorm (fn u) p (μ.restrict (Ω : Set E)) ≤ sobolevNorm (fn u) 1 p Ω μ := by
    have hW := hasWeakIteratedFDerivOn_zero (μ := μ) (hf.memLp.locallyIntegrableOn hp)
    have hae : ∀ᵐ x ∂μ.restrict (Ω : Set E),
        ‖weakIteratedFDeriv 0 (fn u) Ω μ x‖ = ‖fn u x‖ := by
      filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).2 hW.weakIteratedFDeriv_ae_eq]
        with x hx
      rw [hx]
      exact LinearIsometryEquiv.norm_map _ _
    rw [← eLpNorm_congr_norm_ae (hf.memLp_weakIteratedFDeriv (Nat.zero_le 1)).aestronglyMeasurable
      hf.memLp.aestronglyMeasurable hae]
    exact eLpNorm_weakIteratedFDeriv_le_sobolevNorm hp hp' (Nat.zero_le 1)
  have hi : ∀ i, eLpNorm (weakDeriv u (MultiIndexLE.single i)) p (μ.restrict (Ω : Set E))
      ≤ ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ E) F ![b i]‖ₑ
        * sobolevNorm (fn u) 1 p Ω μ := by
    intro i
    have h1 := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm (b : ι → E) i)
    have h2 := (hf.hasWeakIteratedFDerivOn (n := 1) le_rfl).lineDeriv ![b i]
    have hae : (weakDeriv u (MultiIndexLE.single i) : E → F) =ᵐ[μ.restrict (Ω : Set E)]
        fun x ↦ ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ E) F ![b i]
          (weakIteratedFDeriv 1 (fn u) Ω μ x) :=
      (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_comp_continuousLinearMap_le _ _ p).trans ?_
    gcongr
    exact eLpNorm_weakIteratedFDeriv_le_sobolevNorm hp hp' le_rfl
  have hterm : ∀ β : MultiIndexLE ι 1, ENNReal.ofReal ‖weakDeriv u β‖
      = eLpNorm (weakDeriv u β) p (μ.restrict (Ω : Set E)) := fun β ↦ by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  calc ENNReal.ofReal ‖u‖ ≤ ENNReal.ofReal (∑ β, ‖weakDeriv u β‖) :=
        ENNReal.ofReal_le_ofReal (norm_le_sum_norm_weakDeriv u)
    _ = ∑ β, eLpNorm (weakDeriv u β) p (μ.restrict (Ω : Set E)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _]
        exact Finset.sum_congr rfl fun β _ ↦ hterm β
    _ = eLpNorm (fn u) p (μ.restrict (Ω : Set E))
          + ∑ i, eLpNorm (weakDeriv u (MultiIndexLE.single i)) p (μ.restrict (Ω : Set E)) :=
        MultiIndexLE.sum_univ_one _
    _ ≤ sobolevNorm (fn u) 1 p Ω μ + ∑ i, ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ E) F
          ![b i]‖ₑ * sobolevNorm (fn u) 1 p Ω μ :=
        add_le_add h0 (Finset.sum_le_sum fun i _ ↦ hi i)
    _ = _ := by rw [add_mul, one_mul, Finset.sum_mul]

/-- A smooth compactly supported function is the function of an element of `W^{k,p}(Ω)`. -/
theorem _root_.ContDiff.exists_sobolevMultiIndex_of_hasCompactSupport {k : ℕ} {v : E → F}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    ∃ u : SobolevMultiIndex F b k p Ω μ, fn u =ᵐ[μ.restrict (Ω : Set E)] v := by
  refine MemSobolevMultiIndex.exists_sobolevMultiIndex (MemSobolev.memSobolevMultiIndex ?_)
  refine ⟨(hv.continuous.memLp_of_hasCompactSupport hvc).restrict _, fun n _ ↦ ⟨_,
    ContDiffOn.hasWeakIteratedFDerivOn hv.contDiffOn (by simp), ?_⟩⟩
  exact ((hv.continuous_iteratedFDeriv (m := n) (by simp)).memLp_of_hasCompactSupport
    (hvc.iteratedFDeriv n)).restrict _

end SobolevMultiIndex

end Compare

/-! ### Density of `C_c^∞(ℝ^N)` on an extension domain -/

section DensityExtension

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Density of the restrictions of `C_c^∞(ℝ^N)` functions on a subspace with an extension
operator** — the abstract form of [brezis2011functional] Corollary 9.8: for `1 ≤ p < ∞` and
`HasSobolevExtensionOn S`, every `u ∈ S` is the limit in `W^{1,p}(Ω)` of elements whose functions
are (the restrictions to `Ω` of) smooth compactly supported functions on `ℝ^N`. The extension
`P u ∈ W^{1,p}(ℝ^N)` is approximated by `C_c^∞(ℝ^N)` functions in `W^{1,p}(ℝ^N)`
(`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`), and restriction to `Ω` is
`1`-Lipschitz (`SobolevMultiIndex.restrictL`). -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn
    (hp' : p ≠ ⊤) {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)} (hS : HasSobolevExtensionOn S)
    (u : S) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin N) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean N 1 p Ω,
        (∀ n, SobolevMultiIndex.fn (w n)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v n) ∧
        Tendsto w atTop (𝓝 (u : SobolevEuclidean N 1 p Ω)) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨P, hP⟩ := hS
  have hPu : MemSobolev (SobolevMultiIndex.fn (P u)) 1 p ⊤ volume :=
    (SobolevMultiIndex.memSobolevMultiIndex (P u)).memSobolev
  obtain ⟨v, hvs, hvc, hvt⟩ := hPu.exists_seq_hasCompactSupport_tendsto_sobolevNorm hp hp'
  choose V hV using fun n ↦ (hvs n).exists_sobolevMultiIndex_of_hasCompactSupport
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p)
    (Ω := (⊤ : Opens (EuclideanSpace ℝ (Fin N)))) (μ := volume) (hvc n)
  obtain ⟨R, hR⟩ : ∃ R : SobolevEuclidean N 1 p ⊤ →L[ℝ] SobolevEuclidean N 1 p Ω,
      R = SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume
        (le_top : Ω ≤ ⊤) := ⟨_, rfl⟩
  have hRfn : ∀ w, SobolevMultiIndex.fn (R w)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] SobolevMultiIndex.fn w := by
    intro w
    rw [hR]
    exact SobolevMultiIndex.fn_restrictL _ _
  have hRle : ∀ w, ‖R w‖ ≤ ‖w‖ := by
    intro w
    rw [hR]
    exact SobolevMultiIndex.norm_restrictL_apply_le _ _
  refine ⟨v, hvs, hvc, fun n ↦ R (V n), fun n ↦ ?_, ?_⟩
  · exact (hRfn _).trans (ae_mono (Measure.restrict_mono le_top le_rfl) (hV n))
  · have hRPu : R (P u) = (u : SobolevEuclidean N 1 p Ω) :=
      SobolevMultiIndex.ext_of_fn_ae_eq ((hRfn _).trans (hP u))
    rw [← hRPu, tendsto_iff_norm_sub_tendsto_zero]
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ≥0∞, C = 1 + ∑ i, ‖ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin 1 ↦ EuclideanSpace ℝ (Fin N)) ℝ
        ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]‖ₑ := ⟨_, rfl⟩
    have hC : C ≠ ⊤ := by
      rw [hCdef]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top⟩
    have hsub : ∀ n, sobolevNorm (SobolevMultiIndex.fn (V n - P u)) 1 p ⊤ volume
        = sobolevNorm (v n - SobolevMultiIndex.fn (P u)) 1 p ⊤ volume := fun n ↦
      sobolevNorm_congr_ae ((SobolevMultiIndex.fn_sub _ _).trans
        ((hV n).sub (Filter.EventuallyEq.refl _ _)))
    have hfin : ∀ᶠ n in atTop,
        sobolevNorm (v n - SobolevMultiIndex.fn (P u)) 1 p ⊤ volume ≠ ⊤ := by
      filter_upwards [ENNReal.tendsto_nhds_zero.1 hvt 1 one_pos] with n hn
      exact (hn.trans_lt ENNReal.one_lt_top).ne
    have hbound : ∀ n, sobolevNorm (v n - SobolevMultiIndex.fn (P u)) 1 p ⊤ volume ≠ ⊤ →
        ‖R (V n) - R (P u)‖
          ≤ (C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) 1 p ⊤ volume).toReal := by
      intro n hn
      rw [← map_sub]
      refine (hRle _).trans ?_
      have h := SobolevMultiIndex.ofReal_norm_le_sobolevNorm hp' (V n - P u)
      rw [hsub n, ← hCdef] at h
      exact (ENNReal.toReal_ofReal (norm_nonneg _)).symm.le.trans
        (ENNReal.toReal_mono (ENNReal.mul_ne_top hC hn) h)
    refine squeeze_zero' (g := fun n ↦
      (C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) 1 p ⊤ volume).toReal)
      (Eventually.of_forall fun _ ↦ norm_nonneg _) (hfin.mono hbound) ?_
    have h1 : Tendsto (fun n ↦ C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) 1 p ⊤ volume)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hvt (Or.inr hC)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using this

end DensityExtension

/-! ### The cut-off sequence `ζ_n u → u` -/

section CutoffSequence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} {Ω : Opens E} {μ : Measure E}

omit [FiniteDimensional ℝ E] in
/-- **The Leibniz rule for a smooth factor**, in the form `∂_y (g u) = g ∂_y u + (∂_y g) u` with
the classical derivative of `g` written through `fderiv`: `HasWeakIteratedLineDerivOn.mul_contDiff`
with the factors in the other order. -/
theorem HasWeakIteratedLineDerivOn.contDiff_mul {u w : E → ℝ} {y : E}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ g x * u x)
      (fun x ↦ g x * w x + fderiv ℝ g x y * u x) Ω μ :=
  (h.mul_contDiff rfl hg).congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    (Eventually.of_forall fun x ↦ by
      change w x * g x + u x * iteratedFDeriv ℝ 1 g x ![y] = g x * w x + fderiv ℝ g x y * u x
      rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
      ring)

/-- **The Leibniz rule for a smooth factor, in the tensor form at order one**: if `w` is a
first-order weak derivative of the real function `f` on `Ω` and `g` is smooth, then `g f` has the
weak derivative `g w + f ∂g`, `∂g = iteratedFDeriv ℝ 1 g` the classical derivative of `g`
(`HasWeakIteratedLineDerivOn.mul_contDiff` along every direction at once). -/
theorem HasWeakIteratedFDerivOn.contDiff_mul_one {f : E → ℝ} {w : E → E [×1]→L[ℝ] ℝ}
    (h : HasWeakIteratedFDerivOn 1 f w Ω μ) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    HasWeakIteratedFDerivOn 1 (fun x ↦ g x * f x)
      (fun x ↦ g x • w x + f x • iteratedFDeriv ℝ 1 g x) Ω μ where
  locallyIntegrableOn := by
    simpa only [mul_comm] using h.locallyIntegrableOn.mul_continuous hg.continuous
  locallyIntegrableOn_weakDeriv :=
    (h.locallyIntegrableOn_weakDeriv.continuousOn_smul Ω.isOpen.isLocallyClosed
      hg.continuous.continuousOn).add (h.locallyIntegrableOn.smul_continuousOn
        Ω.isOpen.isLocallyClosed
        (hg.iteratedFDeriv_right (m := ∞) (i := 1) (by simp)).continuous.continuousOn)
  integral_smul_eq φ y := by
    have key := ((h.lineDeriv y).mul_contDiff rfl hg).integral_smul_eq φ
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 φ x y • (g x * f x) ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 φ x y • (f x * g x) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by dsimp only; rw [mul_comm (g x)])
    have e2 : ∫ x in (Ω : Set E), φ x • (g x • w x + f x • iteratedFDeriv ℝ 1 g x) y ∂μ
        = ∫ x in (Ω : Set E), φ x • (w x y * g x + f x * iteratedFDeriv ℝ 1 g x y) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring)
    rw [e1, e2, key]

variable [IsLocallyFiniteMeasure μ]

omit [FiniteDimensional ℝ E] in
/-- **A smooth factor, bounded with bounded derivative, preserves `W^{1,p}(Ω)`**: for
`u ∈ W^{1,p}(Ω)` and `g` smooth with `|g| ≤ M` and `‖∇g‖ ≤ M`, `g u ∈ W^{1,p}(Ω)`, with the weak
derivatives `g ∂_i u + (∂_i g) u` (`HasWeakIteratedLineDerivOn.contDiff_mul`). -/
theorem MemSobolevMultiIndex.contDiff_mul {u : E → ℝ} (hp : 1 ≤ p)
    (hu : MemSobolevMultiIndex b u 1 p Ω μ) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M ∧ ‖fderiv ℝ g x‖ ≤ M) :
    MemSobolevMultiIndex b (fun x ↦ g x * u x) 1 p Ω μ := by
  have hum : AEStronglyMeasurable u (μ.restrict (Ω : Set E)) := hu.memLp.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g (μ.restrict (Ω : Set E)) := hg.continuous.aestronglyMeasurable
  have hbound : ∀ {f : E → ℝ}, MemLp f p (μ.restrict (Ω : Set E)) →
      MemLp (fun x ↦ g x * f x) p (μ.restrict (Ω : Set E)) := fun {f} hf ↦
    (hf.const_mul M).of_le (hgm.mul hf.aestronglyMeasurable) (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right ((hM x).1.trans (le_abs_self M)) (abs_nonneg _))
  have hgu := hbound hu.memLp
  refine ⟨hgu, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (hgu.locallyIntegrableOn hp), hgu⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    obtain ⟨w, hw, hwp⟩ := hu.2 (Pi.single i 1) (by simp)
    have hw' : HasWeakIteratedLineDerivOn ![b i] u w Ω μ :=
      hw.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
    refine ⟨_, (hw'.contDiff_mul hg).of_perm (multiIndexTuple_single_perm (b : ι → E) i).symm,
      (hbound hwp).add ((hu.memLp.const_mul (M * ‖b i‖)).of_le
        (((hg.fderiv_right (m := ∞) le_rfl).clm_apply
          contDiff_const).continuous.aestronglyMeasurable.mul hum)
        (Eventually.of_forall fun x ↦ ?_))⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right (((fderiv ℝ g x).le_opNorm (b i)).trans ?_) (abs_nonneg _)
    exact (mul_le_mul_of_nonneg_right (hM x).2 (norm_nonneg _)).trans (le_abs_self _)

variable [μ.IsAddHaarMeasure]

omit [IsLocallyFiniteMeasure μ] in
/-- The `L^p(s)` mass of a function outside a large ball tends to `0`: the restriction of
`MeasureTheory.MemLp.tendsto_eLpNorm_indicator_compl_ball` to a measurable set. -/
theorem MeasureTheory.MemLp.tendsto_eLpNorm_indicator_compl_ball_restrict {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (hp' : p ≠ ⊤) {s : Set E} (hs : MeasurableSet s)
    {f : E → G}
    (hf : MemLp f p (μ.restrict s)) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun j ↦ eLpNorm ((ball (0 : E) (r j))ᶜ.indicator f) p (μ.restrict s)) atTop
      (𝓝 0) := by
  refine (((memLp_indicator_iff_restrict hs).2 hf).tendsto_eLpNorm_indicator_compl_ball hp'
    hr).congr fun j ↦ ?_
  rw [Set.indicator_indicator, eLpNorm_indicator_eq_eLpNorm_restrict
    (measurableSet_ball.compl.inter hs), eLpNorm_indicator_eq_eLpNorm_restrict
    measurableSet_ball.compl, Measure.restrict_restrict measurableSet_ball.compl]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] [μ.IsAddHaarMeasure] in
/-- The function `(ζ_n − 1) f`, for a cut-off `ζ_n` with values in `[0, 1]` equal to `1` on
`ball 0 R`, has `L^p(Ω)` norm at most the `L^p(Ω)` norm of `f` outside `ball 0 R`. -/
theorem eLpNorm_sub_one_mul_le_of_eqOn_ball {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c : E → ℝ} (hc : Continuous c) (hc01 : ∀ x, c x ∈ Icc (0 : ℝ) 1) {R : ℝ}
    (hcR : ∀ x ∈ ball (0 : E) R, c x = 1) {f : E → G}
    (hf : AEStronglyMeasurable f (μ.restrict (Ω : Set E))) :
    eLpNorm (fun x ↦ (c x - 1) • f x) p (μ.restrict (Ω : Set E))
      ≤ eLpNorm ((ball (0 : E) R)ᶜ.indicator f) p (μ.restrict (Ω : Set E)) := by
  refine eLpNorm_mono_ae ((hc.sub continuous_const).aestronglyMeasurable.smul hf)
    (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ ball (0 : E) R
  · simp [hcR x hx]
  · rw [Set.indicator_of_mem (Set.mem_compl hx), norm_smul, Real.norm_eq_abs]
    refine mul_le_of_le_one_left (norm_nonneg _) (abs_le.2 ⟨?_, ?_⟩) <;>
      linarith [(hc01 x).1, (hc01 x).2]

/-- **The cut-off sequence approximates in `W^{1,p}(Ω)`, tensor form**, any open `Ω`,
`1 ≤ p < ∞`: for `ζ : E → ℝ` smooth with values in `[0, 1]`, equal to `1` on `closedBall 0 1`
and supported in `closedBall 0 2` (`exists_contDiff_eqOn_one_closedBall_one` of `Density.lean`),
put `ζ_n x = ζ ((n + 1)⁻¹ • x)`. Then for a real `f ∈ W^{1,p}(Ω)`, every `ζ_n f` lies in
`W^{1,p}(Ω)`, with the weak gradient `ζ_n ∇f + f ∇ζ_n` (`HasWeakIteratedFDerivOn.contDiff_mul_one`),
and `‖ζ_n f − f‖_{W^{1,p}(Ω)} → 0`: `(ζ_n − 1) f` and `(ζ_n − 1) ∇f` are bounded by the `L^p`
mass outside `ball 0 (n + 1)` (`MeasureTheory.MemLp.tendsto_eLpNorm_indicator_compl_ball_restrict`)
and `‖∇ζ_n‖_∞ ≤ ‖∇ζ‖_∞ / (n + 1)`. This is footnote 5 of [brezis2011functional] §9.1, the
sequence `ζ_n u` of Corollary 9.8, Theorem 9.17 and Proposition 9.18, in the reading of
`Numlib/Analysis/Sobolev/Domain.lean` (`MemSobolev`, `sobolevNorm`); the typed form is
`SobolevMultiIndex.tendsto_cutoff_smul`. -/
theorem MemSobolev.tendsto_sobolevNorm_cutoff_mul_sub (hp : 1 ≤ p) (hp' : p ≠ ⊤) {ζ : E → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζ01 : ∀ x, ζ x ∈ Icc (0 : ℝ) 1) (hζ1 : EqOn ζ 1 (closedBall 0 1))
    (hζs : tsupport ζ ⊆ closedBall 0 2) {f : E → ℝ} (hf : MemSobolev f 1 p Ω μ) :
    (∀ n : ℕ, MemSobolev (fun x ↦ ζ ((n + 1 : ℝ)⁻¹ • x) * f x) 1 p Ω μ) ∧
      Tendsto (fun n : ℕ ↦ sobolevNorm (fun x ↦ ζ ((n + 1 : ℝ)⁻¹ • x) * f x - f x) 1 p Ω μ)
        atTop (𝓝 0) := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hζc : HasCompactSupport ζ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport ζ) hζs
  obtain ⟨Mζ, hMζ0, hMζ⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hζc.fderiv ℝ).exists_bound_of_continuous (hζ.continuous_fderiv (by simp))
    exact ⟨max M 0, le_max_right _ _, fun x ↦ (hM x).trans (le_max_left _ _)⟩
  -- the cut-offs `ζ_n`
  set R : ℕ → ℝ := fun n ↦ (n : ℝ) + 1 with hRdef
  have hRpos : ∀ n, 0 < R n := fun n ↦ by simp only [hRdef]; positivity
  set c : ℕ → E → ℝ := fun n x ↦ ζ ((R n)⁻¹ • x) with hcdef
  have hcs : ∀ n, ContDiff ℝ ∞ (c n) := fun n ↦ hζ.comp (contDiff_id.const_smul _)
  have hc01 : ∀ n x, c n x ∈ Icc (0 : ℝ) 1 := fun n x ↦ hζ01 _
  have hcd : ∀ n x, fderiv ℝ (c n) x = (R n)⁻¹ • fderiv ℝ ζ ((R n)⁻¹ • x) := fun n x ↦ by
    have h : HasFDerivAt (c n) ((fderiv ℝ ζ ((R n)⁻¹ • x)).comp
        ((R n)⁻¹ • ContinuousLinearMap.id ℝ E)) x :=
      ((hζ.differentiable (by simp)) _).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul _)
    rw [h.fderiv, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
  have hcdn : ∀ n x, ‖iteratedFDeriv ℝ 1 (c n) x‖ ≤ (R n)⁻¹ * Mζ := fun n x ↦ by
    rw [norm_iteratedFDeriv_one, hcd, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hRpos n)]
    exact mul_le_mul_of_nonneg_left (hMζ _) (inv_pos.2 (hRpos n)).le
  have hc1 : ∀ n, ∀ x ∈ ball (0 : E) (R n), c n x = 1 := fun n x hx ↦ by
    refine hζ1 (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hRpos n), inv_mul_le_iff₀ (hRpos n),
      mul_one]
    exact (mem_ball_zero_iff.1 hx).le
  have hcbound : ∀ n, MemLp (c n) ⊤ (μ.restrict (Ω : Set E)) := fun n ↦
    memLp_top_of_bound (hcs n).continuous.aestronglyMeasurable 1 (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [(hc01 n x).1], (hc01 n x).2⟩)
  -- the weak gradients
  obtain ⟨w, hw, hwp⟩ := hf.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  have hwn : ∀ n, HasWeakIteratedFDerivOn 1 (fun x ↦ c n x * f x)
      (fun x ↦ c n x • w x + f x • iteratedFDeriv ℝ 1 (c n) x) Ω μ := fun n ↦
    hw.contDiff_mul_one (hcs n)
  have hwn' : ∀ n, HasWeakIteratedFDerivOn 1 (fun x ↦ c n x * f x - f x)
      (fun x ↦ (c n x - 1) • w x + f x • iteratedFDeriv ℝ 1 (c n) x) Ω μ := fun n ↦
    ((hwn n).sub hw).congr_ae (Eventually.of_forall fun x ↦ rfl)
      (Eventually.of_forall fun x ↦ by
        simp only [Pi.sub_apply, sub_smul, one_smul]
        abel)
  have hfD : ∀ n, MemLp (fun x ↦ f x • iteratedFDeriv ℝ 1 (c n) x) p (μ.restrict (Ω : Set E)) :=
    fun n ↦ by
    refine (hf.memLp.const_mul ((R n)⁻¹ * Mζ)).of_le
      (hf.memLp.aestronglyMeasurable.smul ((hcs n).iteratedFDeriv_right (m := ∞) (i := 1)
        (by simp)).continuous.aestronglyMeasurable) (Eventually.of_forall fun x ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (R n)⁻¹ * Mζ), mul_comm]
    exact mul_le_mul_of_nonneg_right (hcdn n x) (abs_nonneg _)
  -- membership
  have hmem : ∀ n, MemSobolev (fun x ↦ c n x * f x) 1 p Ω μ := fun n ↦ by
    have h0 : MemLp (fun x ↦ c n x * f x) p (μ.restrict (Ω : Set E)) :=
      (hcbound n).smul hf.memLp
    refine ⟨h0, fun m hm ↦ ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by exact_mod_cast hm) with rfl | rfl
    · exact ((memSobolev_zero_order hp).2 h0).2 0 le_rfl
    · exact ⟨_, hwn n, ((hcbound n).smul hwp).add (hfD n)⟩
  refine ⟨hmem, ?_⟩
  -- the estimates
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hind0 := hf.memLp.tendsto_eLpNorm_indicator_compl_ball_restrict hp' hΩm hR
  have hind1 := hwp.tendsto_eLpNorm_indicator_compl_ball_restrict hp' hΩm hR
  have hE0 : Tendsto (fun n ↦ eLpNorm (weakIteratedFDeriv 0 (fun x ↦ c n x * f x - f x) Ω μ) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hind0
      (fun _ ↦ zero_le) fun n ↦ ?_
    have hloc : LocallyIntegrableOn (fun x ↦ c n x * f x - f x) Ω μ :=
      (hwn' n).locallyIntegrableOn
    have hfm := hf.memLp.aestronglyMeasurable
    have hm1 : AEStronglyMeasurable (fun x ↦ c n x * f x - f x) (μ.restrict (Ω : Set E)) :=
      ((hcs n).continuous.aestronglyMeasurable.mul hfm).sub hfm
    rw [(hasWeakIteratedFDerivOn_zero hloc).eLpNorm_weakIteratedFDeriv,
      eLpNorm_congr_norm_ae (g := fun x ↦ (c n x - 1) • f x)
        ((continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous.comp_aestronglyMeasurable hm1)
        (((hcs n).continuous.sub continuous_const).aestronglyMeasurable.smul hfm)
        (Eventually.of_forall fun x ↦ by
          rw [LinearIsometryEquiv.norm_map, sub_smul, one_smul, smul_eq_mul])]
    exact eLpNorm_sub_one_mul_le_of_eqOn_ball (hcs n).continuous (hc01 n) (hc1 n)
      hf.memLp.aestronglyMeasurable
  have hE1 : Tendsto (fun n ↦ eLpNorm (weakIteratedFDeriv 1 (fun x ↦ c n x * f x - f x) Ω μ) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
    have hB : Tendsto (fun n ↦ ENNReal.ofReal ((R n)⁻¹ * Mζ)
        * eLpNorm f p (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n ↦ (R n)⁻¹ * Mζ) atTop (𝓝 0) := by
        simpa [hRdef, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const Mζ
      have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1)
        (Or.inr hf.memLp.eLpNorm_ne_top)
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hind1.add hB) (fun _ ↦ zero_le) fun n ↦ ?_
    rw [(hwn' n).eLpNorm_weakIteratedFDeriv]
    refine (eLpNorm_add_le hp).trans (add_le_add ?_ ?_)
    · exact eLpNorm_sub_one_mul_le_of_eqOn_ball (hcs n).continuous (hc01 n) (hc1 n)
        hwp.aestronglyMeasurable
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (f := fun x ↦ f x • iteratedFDeriv ℝ 1 (c n) x) (g := f) (c := (R n)⁻¹ * Mζ)
        (hfD n).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_) p
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hcdn n x) (norm_nonneg _)
  -- the convergence of the Sobolev norm
  have hsum : Tendsto (fun n ↦ (1 + 1 : ℝ≥0∞) *
      (eLpNorm (weakIteratedFDeriv 0 (fun x ↦ c n x * f x - f x) Ω μ) p (μ.restrict (Ω : Set E))
        + eLpNorm (weakIteratedFDeriv 1 (fun x ↦ c n x * f x - f x) Ω μ) p
          (μ.restrict (Ω : Set E)))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hE0.add hE1) (Or.inr (by simp))
  have key : ∀ n, sobolevNorm (fun x ↦ c n x * f x - f x) 1 p Ω μ ≤ (1 + 1 : ℝ≥0∞) *
      (eLpNorm (weakIteratedFDeriv 0 (fun x ↦ c n x * f x - f x) Ω μ) p (μ.restrict (Ω : Set E))
        + eLpNorm (weakIteratedFDeriv 1 (fun x ↦ c n x * f x - f x) Ω μ) p
          (μ.restrict (Ω : Set E))) := fun n ↦ by
    have := sobolevNorm_le_of_forall_eLpNorm_le (f := fun x ↦ c n x * f x - f x) (k := 1)
      (Ω := Ω) (μ := μ) hp hp'
      (c := eLpNorm (weakIteratedFDeriv 0 (fun x ↦ c n x * f x - f x) Ω μ) p
          (μ.restrict (Ω : Set E))
        + eLpNorm (weakIteratedFDeriv 1 (fun x ↦ c n x * f x - f x) Ω μ) p
          (μ.restrict (Ω : Set E))) fun m hm ↦ ?_
    · simpa using this
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
    · exact le_add_right le_rfl
    · exact le_add_left le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le) key

namespace SobolevMultiIndex

variable [Fact (1 ≤ p)]

/-- **The cut-off sequence approximates in `W^{1,p}(Ω)`**, any open `Ω`, `1 ≤ p < ∞`: for
`ζ : E → ℝ` smooth with values in `[0, 1]`, equal to `1` on `closedBall 0 1` and supported in
`closedBall 0 2` (`exists_contDiff_eqOn_one_closedBall_one` of `Density.lean`), put
`ζ_n x = ζ ((n + 1)⁻¹ • x)`. Then for `u ∈ W^{1,p}(Ω)` there is `v : ℕ → W^{1,p}(Ω)` with
`fn (v n) = ζ_n fn u` on `Ω`, `fn (v n) = 0` off `closedBall 0 (2 (n + 1))`, and `v n → u`. The
weak derivatives of `v n` are `ζ_n ∂_i u + (∂_i ζ_n) u` (`MemSobolevMultiIndex.contDiff_mul`);
`(ζ_n − 1) u` and `(ζ_n − 1) ∂_i u` are bounded by the `L^p` mass outside `ball 0 (n + 1)`
(`MeasureTheory.MemLp.tendsto_eLpNorm_indicator_compl_ball_restrict`) and
`‖∇ζ_n‖_∞ ≤ ‖∇ζ‖_∞ / (n + 1)`. This is footnote 5 of [brezis2011functional] §9.1 and the
sequence `ζ_n u` used in Corollary 9.8, Theorem 9.17 and Proposition 9.18. -/
theorem tendsto_cutoff_smul (hp' : p ≠ ⊤) {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζ01 : ∀ x, ζ x ∈ Icc (0 : ℝ) 1) (hζ1 : EqOn ζ 1 (closedBall 0 1))
    (hζs : tsupport ζ ⊆ closedBall 0 2) (u : SobolevMultiIndex ℝ b 1 p Ω μ) :
    ∃ v : ℕ → SobolevMultiIndex ℝ b 1 p Ω μ,
      (∀ n : ℕ, fn (v n) =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ ζ ((n + 1 : ℝ)⁻¹ • x) * fn u x) ∧
      (∀ n : ℕ, ∀ᵐ x ∂μ.restrict (Ω : Set E), 2 * (n + 1 : ℝ) < ‖x‖ → fn (v n) x = 0) ∧
      Tendsto v atTop (𝓝 u) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hζc : HasCompactSupport ζ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport ζ) hζs
  obtain ⟨Mζ, hMζ0, hMζ⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hζc.fderiv ℝ).exists_bound_of_continuous (hζ.continuous_fderiv (by simp))
    exact ⟨max M 0, le_max_right _ _, fun x ↦ (hM x).trans (le_max_left _ _)⟩
  -- the cut-offs `ζ_n`
  set R : ℕ → ℝ := fun n ↦ (n : ℝ) + 1 with hRdef
  have hRpos : ∀ n, 0 < R n := fun n ↦ by simp only [hRdef]; positivity
  have hRinv1 : ∀ n, (R n)⁻¹ ≤ 1 := fun n ↦ inv_le_one_of_one_le₀ (by simp [hRdef])
  set c : ℕ → E → ℝ := fun n x ↦ ζ ((R n)⁻¹ • x) with hcdef
  have hcs : ∀ n, ContDiff ℝ ∞ (c n) := fun n ↦ hζ.comp (contDiff_id.const_smul _)
  have hc01 : ∀ n x, c n x ∈ Icc (0 : ℝ) 1 := fun n x ↦ hζ01 _
  have hcd : ∀ n x, fderiv ℝ (c n) x = (R n)⁻¹ • fderiv ℝ ζ ((R n)⁻¹ • x) := fun n x ↦ by
    have h : HasFDerivAt (c n) ((fderiv ℝ ζ ((R n)⁻¹ • x)).comp
        ((R n)⁻¹ • ContinuousLinearMap.id ℝ E)) x :=
      ((hζ.differentiable (by simp)) _).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul _)
    rw [h.fderiv, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
  have hcdn : ∀ n x, ‖fderiv ℝ (c n) x‖ ≤ (R n)⁻¹ * Mζ := fun n x ↦ by
    rw [hcd, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hRpos n)]
    exact mul_le_mul_of_nonneg_left (hMζ _) (inv_pos.2 (hRpos n)).le
  have hcM : ∀ n x, |c n x| ≤ max 1 Mζ ∧ ‖fderiv ℝ (c n) x‖ ≤ max 1 Mζ := fun n x ↦
    ⟨(abs_le.2 ⟨by linarith [(hc01 n x).1], (hc01 n x).2⟩).trans (le_max_left _ _),
      (hcdn n x).trans ((mul_le_of_le_one_left hMζ0 (hRinv1 n)).trans (le_max_right _ _))⟩
  have hc1 : ∀ n, ∀ x ∈ ball (0 : E) (R n), c n x = 1 := fun n x hx ↦ by
    refine hζ1 (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hRpos n), inv_mul_le_iff₀ (hRpos n),
      mul_one]
    exact (mem_ball_zero_iff.1 hx).le
  have hc0 : ∀ n x, 2 * R n < ‖x‖ → c n x = 0 := fun n x hx ↦ by
    refine image_eq_zero_of_notMem_tsupport (f := ζ) (x := (R n)⁻¹ • x) fun hmem ↦ ?_
    have h := mem_closedBall_zero_iff.1 (hζs hmem)
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hRpos n), inv_mul_le_iff₀ (hRpos n)]
      at h
    linarith
  -- the elements `v n`
  have hmem : ∀ n, MemSobolevMultiIndex b (fun x ↦ c n x * fn u x) 1 p Ω μ := fun n ↦
    (memSobolevMultiIndex u).contDiff_mul hp (hcs n) (hcM n)
  choose v hv using fun n ↦ (hmem n).exists_sobolevMultiIndex
  refine ⟨v, hv, fun n ↦ ?_, ?_⟩
  · filter_upwards [hv n] with x hx hxn
    rw [hx, hc0 n x hxn, zero_mul]
  -- the weak derivatives of `v n`
  have hperm := fun i ↦ multiIndexTuple_single_perm (b : ι → E) i
  have hwu : ∀ i, HasWeakIteratedLineDerivOn ![b i] (fn u) (weakDeriv u (MultiIndexLE.single i))
      Ω μ := fun i ↦ (hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm (hperm i)
  have hwv : ∀ n i, weakDeriv (v n) (MultiIndexLE.single i) =ᵐ[μ.restrict (Ω : Set E)] fun x ↦
      c n x * weakDeriv u (MultiIndexLE.single i) x + fderiv ℝ (c n) x (b i) * fn u x := by
    intro n i
    have h1 : HasWeakIteratedLineDerivOn ![b i] (fun x ↦ c n x * fn u x)
        (weakDeriv (v n) (MultiIndexLE.single i)) Ω μ :=
      ((hasWeakIteratedLineDerivOn (v n) (MultiIndexLE.single i)).of_perm (hperm i)).congr_ae
        (hv n) (EventuallyEq.refl _ _)
    exact (ae_restrict_iff' hΩm).2 (h1.ae_eq ((hwu i).contDiff_mul (hcs n)))
  -- the estimates
  have hind : ∀ f : E → ℝ, MemLp f p (μ.restrict (Ω : Set E)) →
      Tendsto (fun n ↦ eLpNorm ((ball (0 : E) (R n))ᶜ.indicator f) p (μ.restrict (Ω : Set E)))
        atTop (𝓝 0) := fun f hf ↦
    hf.tendsto_eLpNorm_indicator_compl_ball_restrict hp' hΩm
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hE0 : Tendsto (fun n ↦ eLpNorm (weakDeriv (v n - u) 0) p (μ.restrict (Ω : Set E))) atTop
      (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hind _ (memLp u))
      (fun _ ↦ zero_le) fun n ↦ ?_
    have e : weakDeriv (v n - u) 0 = weakDeriv (v n) 0 - weakDeriv u 0 := rfl
    have h : weakDeriv (v n - u) 0 =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ (c n x - 1) • fn u x := by
      rw [e]
      filter_upwards [Lp.coeFn_sub (weakDeriv (v n) 0) (weakDeriv u 0), hv n] with x hx hxv
      rw [hx, Pi.sub_apply, weakDeriv_zero, weakDeriv_zero, hxv, smul_eq_mul]
      ring
    rw [eLpNorm_congr_ae h]
    exact eLpNorm_sub_one_mul_le_of_eqOn_ball (hcs n).continuous (hc01 n) (hc1 n)
      (memLp u).aestronglyMeasurable
  have hEi : ∀ i, Tendsto (fun n ↦ eLpNorm (weakDeriv (v n - u) (MultiIndexLE.single i)) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
    intro i
    have hB : Tendsto (fun n ↦ ENNReal.ofReal ((R n)⁻¹ * (Mζ * ‖b i‖))
        * eLpNorm (fn u) p (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n ↦ (R n)⁻¹ * (Mζ * ‖b i‖)) atTop (𝓝 0) := by
        simpa [hRdef, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (Mζ * ‖b i‖)
      have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1)
        (Or.inr (memLp u).eLpNorm_ne_top)
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (hind _ (Lp.memLp (weakDeriv u (MultiIndexLE.single i)))).add hB)
      (fun _ ↦ zero_le) fun n ↦ ?_
    have e : weakDeriv (v n - u) (MultiIndexLE.single i)
        = weakDeriv (v n) (MultiIndexLE.single i) - weakDeriv u (MultiIndexLE.single i) := rfl
    have h : weakDeriv (v n - u) (MultiIndexLE.single i) =ᵐ[μ.restrict (Ω : Set E)]
        (fun x ↦ (c n x - 1) • weakDeriv u (MultiIndexLE.single i) x)
          + fun x ↦ fderiv ℝ (c n) x (b i) * fn u x := by
      rw [e]
      filter_upwards [Lp.coeFn_sub (weakDeriv (v n) (MultiIndexLE.single i))
        (weakDeriv u (MultiIndexLE.single i)), hwv n i] with x hx hxv
      rw [hx, Pi.sub_apply, hxv, Pi.add_apply, smul_eq_mul]
      ring
    rw [eLpNorm_congr_ae h]
    refine (eLpNorm_add_le hp).trans (add_le_add ?_ ?_)
    · exact eLpNorm_sub_one_mul_le_of_eqOn_ball (hcs n).continuous (hc01 n) (hc1 n)
        (Lp.memLp _).aestronglyMeasurable
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := fun x ↦ fderiv ℝ (c n) x (b i) * fn u x)
        (g := fn u) (c := (R n)⁻¹ * (Mζ * ‖b i‖)) ?_ (Eventually.of_forall fun x ↦ ?_) p
      · exact (((hcs n).fderiv_right (m := ∞) le_rfl).clm_apply
          contDiff_const).continuous.aestronglyMeasurable.mul (memLp u).aestronglyMeasurable
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right (((fderiv ℝ (c n) x).le_opNorm (b i)).trans ?_)
        (norm_nonneg _)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hcdn n x) (norm_nonneg _)
  -- the convergence
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto (fun n ↦ (eLpNorm (weakDeriv (v n - u) 0) p (μ.restrict (Ω : Set E))).toReal
      + ∑ i, (eLpNorm (weakDeriv (v n - u) (MultiIndexLE.single i)) p
        (μ.restrict (Ω : Set E))).toReal) atTop (𝓝 0) := by
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE0
    have hi := fun i ↦ (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hEi i)
    simp only [Function.comp_def, ENNReal.toReal_zero] at h0 hi
    simpa using h0.add (tendsto_finsetSum Finset.univ fun i _ ↦ hi i)
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hsum
  calc ‖v n - u‖ ≤ ∑ α, ‖weakDeriv (v n - u) α‖ := norm_le_sum_norm_weakDeriv _
    _ = _ := by
      rw [MultiIndexLE.sum_univ_one]
      simp only [Lp.norm_def]

end SobolevMultiIndex

end CutoffSequence

/-! ### Zero extension across the edge of a chart, at every order -/

section IndicatorSmul

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω Ω' : Opens E}
  {μ : Measure E} {α : E → ℝ}

omit [NormedSpace ℝ E] in
/-- **The zero extension of `α v` off `Ω'` is locally integrable on `Ω ⊇ Ω'`**, for `v` locally
integrable on `Ω'` and `α` continuous with `tsupport α ∩ Ω ⊆ Ω'`: near a point of `Ω'` the
function `α` is bounded and `v` integrable, near a point of `Ω ∖ Ω'` the function `α` vanishes. -/
theorem LocallyIntegrableOn.indicator_smul_of_tsupport_inter_subset [ProperSpace E]
    (hα : Continuous α) (hαΩ' : tsupport α ∩ Ω ⊆ Ω') {v : E → F}
    (hv : LocallyIntegrableOn v Ω' μ) :
    LocallyIntegrableOn ((Ω' : Set E).indicator fun x ↦ α x • v x) Ω μ := by
  intro x hx
  by_cases hxΩ' : x ∈ (Ω' : Set E)
  · obtain ⟨ε, hε, hεΩ'⟩ := Metric.isOpen_iff.1 Ω'.isOpen x hxΩ'
    have hball : closedBall x (ε / 2) ⊆ Ω' :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεΩ'
    refine ⟨closedBall x (ε / 2), nhdsWithin_le_nhds (closedBall_mem_nhds x (half_pos hε)), ?_⟩
    obtain ⟨C, hC⟩ := (isCompact_closedBall x (ε / 2)).exists_bound_of_continuousOn
      hα.continuousOn
    have hint : IntegrableOn (fun z ↦ α z • v z) (closedBall x (ε / 2)) μ :=
      (hv.integrableOn_compact_subset hball (isCompact_closedBall _ _)).bdd_smul C
        hα.aestronglyMeasurable
        ((ae_restrict_mem measurableSet_closedBall).mono fun z hz ↦ hC z hz)
    exact hint.congr_fun (fun z hz ↦ (Set.indicator_of_mem (hball hz) fun x ↦ α x • v x).symm)
      measurableSet_closedBall
  · have hxα : x ∉ tsupport α := fun h ↦ hxΩ' (hαΩ' ⟨h, hx⟩)
    refine ⟨(tsupport α)ᶜ, nhdsWithin_le_nhds ((isClosed_tsupport α).isOpen_compl.mem_nhds hxα),
      ?_⟩
    refine (integrable_zero _ _ _).congr ?_
    filter_upwards [self_mem_ae_restrict (isClosed_tsupport α).isOpen_compl.measurableSet]
      with z hz
    by_cases hzΩ' : z ∈ (Ω' : Set E)
    · rw [Set.indicator_of_mem hzΩ', image_eq_zero_of_notMem_tsupport hz, zero_smul]
      rfl
    · rw [Set.indicator_of_notMem hzΩ']
      rfl

omit [NormedSpace ℝ E] in
/-- **The zero extension of `α v` off `Ω'` lies in `L^p(Ω)`** for `v ∈ L^p(Ω')`, `Ω' ≤ Ω`, and a
continuous `α` bounded by `M`. -/
theorem MeasureTheory.MemLp.indicator_smul_of_le {p : ℝ≥0∞} (hα : Continuous α)
    {M : ℝ} (hM : ∀ x, |α x| ≤ M) {v : E → F} (hv : MemLp v p (μ.restrict (Ω' : Set E))) :
    MemLp ((Ω' : Set E).indicator fun x ↦ α x • v x) p (μ.restrict (Ω : Set E)) :=
  (memLp_indicator_smul_of_forall_norm_le Ω'.isOpen.measurableSet
    (fun x _ ↦ (Real.norm_eq_abs _).trans_le (hM x)) hα.aestronglyMeasurable hv).mono_measure
    Measure.restrict_le_self

/-- **Zero extension across the edge of a chart, at order one**: for opens `Ω' ≤ Ω`, a smooth
compactly supported `α` with `tsupport α ∩ Ω ⊆ Ω'`, and `w` the weak derivative of `v` along `z`
on `Ω'`, the extension of `α v` by zero off `Ω'` has, on `Ω`, the weak derivative
`α w + (∂_z α) v` extended by zero. For a test function `φ` on `Ω`, `α φ` is a test function on
`Ω'`, and
`∫_{Ω'} α v ∂_z φ = ∫_{Ω'} v ∂_z (α φ) − ∫_{Ω'} v (∂_z α) φ = −∫_{Ω'} (α w + (∂_z α) v) φ`.
Remark 4 (ii) of [brezis2011functional] Chapter 9 (`HasWeakIteratedLineDerivOn.indicator_mul`)
is the case `Ω = ℝ^N` for a cut-off supported off `∂Ω'`; here `α` may reach `∂Ω' ∩ ∂Ω`, which is
why the extension is only to `Ω`. -/
theorem HasWeakIteratedLineDerivOn.indicator_smul_of_tsupport_inter_subset [ProperSpace E]
    (hΩ' : Ω' ≤ Ω) (hα : ContDiff ℝ ∞ α) (hαΩ' : tsupport α ∩ Ω ⊆ Ω') {z : E} {v w : E → F}
    (h : HasWeakIteratedLineDerivOn ![z] v w Ω' μ) :
    HasWeakIteratedLineDerivOn ![z] ((Ω' : Set E).indicator fun x ↦ α x • v x)
      ((Ω' : Set E).indicator fun x ↦ α x • w x + fderiv ℝ α x z • v x) Ω μ where
  locallyIntegrableOn :=
    LocallyIntegrableOn.indicator_smul_of_tsupport_inter_subset hα.continuous hαΩ'
      h.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv := by
    have h1 := LocallyIntegrableOn.indicator_smul_of_tsupport_inter_subset hα.continuous hαΩ'
      h.locallyIntegrableOn_weakDeriv
    have h2 := LocallyIntegrableOn.indicator_smul_of_tsupport_inter_subset
      ((hα.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
      (fun x hx ↦ hαΩ' ⟨tsupport_fderiv_apply_subset ℝ z hx.1, hx.2⟩) h.locallyIntegrableOn
    refine (h1.add h2).congr (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ (Ω' : Set E) <;> simp [hx]
  integral_smul_eq φ := by
    have hmeas := Ω'.isOpen.measurableSet
    set ψ : 𝓓(Ω', ℝ) := ⟨fun x ↦ α x * φ x, hα.mul φ.contDiff, φ.hasCompactSupport.mul_left,
      fun x hx ↦ hαΩ' ⟨tsupport_mul_subset_left hx,
        φ.tsupport_subset (tsupport_mul_subset_right hx)⟩⟩ with hψdef
    have hψ : ∀ x, ψ x = α x * φ x := fun x ↦ rfl
    have hψd : ∀ x, fderiv ℝ ψ x z = fderiv ℝ α x z * φ x + α x * fderiv ℝ φ x z := by
      intro x
      change fderiv ℝ (fun x ↦ α x * φ x) x z = _
      rw [fderiv_fun_mul (hα.differentiable (by simp) x) (φ.contDiff.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have I1 : IntegrableOn (fun x ↦ fderiv ℝ ψ x z • v x) Ω' μ := by
      have := (h.integrable_smul (ψ.fderivApply z)).integrableOn (s := (Ω' : Set E))
      simpa only [TestFunction.fderivApply_apply] using this
    have I2 : IntegrableOn (fun x ↦ (fderiv ℝ α x z * φ x) • v x) Ω' μ :=
      (h.locallyIntegrableOn.integrable_smul_left_of_tsupport_subset
        (((hα.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous.mul
          φ.contDiff.continuous) φ.hasCompactSupport.mul_left
        (fun x hx ↦ hαΩ' ⟨tsupport_fderiv_apply_subset ℝ z (tsupport_mul_subset_left hx),
          φ.tsupport_subset (tsupport_mul_subset_right hx)⟩)).integrableOn
    have I3 : IntegrableOn (fun x ↦ ψ x • w x) Ω' μ :=
      (h.integrable_smul_weakDeriv ψ).integrableOn
    have hΩΩ' : (Ω : Set E) ∩ Ω' = Ω' := Set.inter_eq_right.2 hΩ'
    have hL : ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] •
        ((Ω' : Set E).indicator fun x ↦ α x • v x) x ∂μ
        = ∫ x in (Ω' : Set E), fderiv ℝ ψ x z • v x ∂μ
          - ∫ x in (Ω' : Set E), (fderiv ℝ α x z * φ x) • v x ∂μ := by
      have e : (fun x ↦ iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] •
          ((Ω' : Set E).indicator fun x ↦ α x • v x) x)
          = (Ω' : Set E).indicator fun x ↦ iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] • (α x • v x) := by
        funext x
        by_cases hx : x ∈ (Ω' : Set E) <;> simp [hx]
      rw [e, setIntegral_indicator hmeas, hΩΩ', ← integral_sub I1 I2]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      dsimp only
      rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero, hψd x, add_smul, add_sub_cancel_left,
        smul_smul, mul_comm]
    have hR : ∫ x in (Ω : Set E), φ x •
        ((Ω' : Set E).indicator fun x ↦ α x • w x + fderiv ℝ α x z • v x) x ∂μ
        = ∫ x in (Ω' : Set E), ψ x • w x ∂μ
          + ∫ x in (Ω' : Set E), (fderiv ℝ α x z * φ x) • v x ∂μ := by
      have e : (fun x ↦ φ x • ((Ω' : Set E).indicator fun x ↦ α x • w x + fderiv ℝ α x z • v x) x)
          = (Ω' : Set E).indicator fun x ↦ φ x • (α x • w x + fderiv ℝ α x z • v x) := by
        funext x
        by_cases hx : x ∈ (Ω' : Set E) <;> simp [hx]
      rw [e, setIntegral_indicator hmeas, hΩΩ', ← integral_add I3 I2]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      dsimp only
      rw [hψ x, smul_add, smul_smul, smul_smul, mul_comm (φ x) (α x), mul_comm (φ x)]
    rw [hL, hR, pow_one, neg_one_smul, neg_add, sub_eq_add_neg]
    congr 1
    have := h.integral_smul_eq ψ
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, pow_one, neg_one_smul] at this
    exact this

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] {ι : Type*} [Fintype ι]
  [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [IsLocallyFiniteMeasure μ]

/-- **The zero extension of `α v` off `Ω'` has weak derivatives of every order on `Ω`**, along
every tuple of directions, when `v` has weak derivatives in `L^p(Ω')` along every tuple of
length at most `m`: the induction of [brezis2011functional] Chapter 9, Remark 25, one direction
at a time — `∂_z (α v) = α ∂_z v + (∂_z α) v` extended by zero
(`HasWeakIteratedLineDerivOn.indicator_smul_of_tsupport_inter_subset`), both terms again of the
same form with one order less. -/
theorem HasWeakIteratedLineDerivOn.exists_indicator_smul_of_forall_tuple (hp : 1 ≤ p)
    (hΩ' : Ω' ≤ Ω) : ∀ (m : ℕ) (y : Fin m → E) (α : E → ℝ), ContDiff ℝ ∞ α →
      HasCompactSupport α → tsupport α ∩ Ω ⊆ Ω' → ∀ v : E → F,
      (∀ (m' : ℕ) (y' : Fin m' → E), m' ≤ m → ∃ w : E → F,
        HasWeakIteratedLineDerivOn y' v w Ω' μ ∧ MemLp w p (μ.restrict (Ω' : Set E))) →
      ∃ w : E → F, HasWeakIteratedLineDerivOn y ((Ω' : Set E).indicator fun x ↦ α x • v x) w Ω μ ∧
        MemLp w p (μ.restrict (Ω : Set E)) := by
  intro m
  induction m with
  | zero =>
    intro y α hα hαc hαΩ' v hv
    obtain ⟨w₀, hw₀, hw₀p⟩ := hv 0 ![] le_rfl
    have hvp : MemLp v p (μ.restrict (Ω' : Set E)) :=
      hw₀p.ae_eq ((ae_restrict_iff' Ω'.isOpen.measurableSet).2 (hw₀.ae_eq_of_length_eq_zero rfl))
    obtain ⟨M, hM⟩ := hαc.exists_bound_of_continuous hα.continuous
    have hmem : MemLp ((Ω' : Set E).indicator fun x ↦ α x • v x) p (μ.restrict (Ω : Set E)) :=
      hvp.indicator_smul_of_le hα.continuous (fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hM x))
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero rfl y (hmem.locallyIntegrableOn hp),
      hmem⟩
  | succ m ih =>
    intro y α hα hαc hαΩ' v hv
    obtain ⟨g, hg, hgp⟩ := hv 1 ![y 0] (by omega)
    have hg' : ∀ (m' : ℕ) (y' : Fin m' → E), m' ≤ m → ∃ w : E → F,
        HasWeakIteratedLineDerivOn y' g w Ω' μ ∧ MemLp w p (μ.restrict (Ω' : Set E)) := by
      intro m' y' hm'
      obtain ⟨u, hu, hup⟩ := hv (m' + 1) (Fin.cons (y 0) y') (by omega)
      exact ⟨u, hg.of_cons' hu, hup⟩
    have hv' : ∀ (m' : ℕ) (y' : Fin m' → E), m' ≤ m → ∃ w : E → F,
        HasWeakIteratedLineDerivOn y' v w Ω' μ ∧ MemLp w p (μ.restrict (Ω' : Set E)) :=
      fun m' y' hm' ↦ hv m' y' (by omega)
    obtain ⟨w₁, hw₁, hw₁p⟩ := ih (Fin.tail y) α hα hαc hαΩ' g hg'
    obtain ⟨w₂, hw₂, hw₂p⟩ := ih (Fin.tail y) (fun x ↦ fderiv ℝ α x (y 0))
      ((hα.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const) (hαc.fderiv_apply ℝ (y 0))
      (fun x hx ↦ hαΩ' ⟨tsupport_fderiv_apply_subset ℝ (y 0) hx.1, hx.2⟩) v hv'
    have h1 := hg.indicator_smul_of_tsupport_inter_subset hΩ' hα hαΩ'
    have h2 : HasWeakIteratedLineDerivOn (Fin.tail y)
        ((Ω' : Set E).indicator fun x ↦ α x • g x + fderiv ℝ α x (y 0) • v x) (w₁ + w₂) Ω μ := by
      refine (hw₁.add hw₂).congr_ae (Eventually.of_forall fun x ↦ ?_) (EventuallyEq.refl _ _)
      by_cases hx : x ∈ (Ω' : Set E) <;> simp [hx]
    refine ⟨w₁ + w₂, ?_, hw₁p.add hw₂p⟩
    have := h1.cons' h2
    rwa [Fin.cons_self_tail] at this

/-- **Zero extension across the edge of a chart, at every order**: for opens `Ω' ≤ Ω`, a smooth
compactly supported `α` with `tsupport α ∩ Ω ⊆ Ω'`, and `v ∈ W^{k,p}(Ω')`, the function `α v`
extended by zero off `Ω'` lies in `W^{k,p}(Ω)`. The case `Ω' = Ω ⊓ U` with `tsupport α ⊆ U` is
"and thus, in fact, to `H²(Ω)`" of [brezis2011functional] §9.6, proof of Theorem 9.25, and the
case `Ω = ℝ^N` is Remark 25. The derivatives are the induction
`HasWeakIteratedLineDerivOn.exists_indicator_smul_of_forall_tuple`, fed by the tensor weak
derivatives of `v` (`MemSobolevMultiIndex.memSobolev`), which exist along every tuple. -/
theorem MemSobolevMultiIndex.indicator_smul_of_tsupport_subset {k : ℕ} (hp : 1 ≤ p)
    (hΩ' : Ω' ≤ Ω) (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (hαΩ' : tsupport α ∩ Ω ⊆ Ω') {v : E → F} (hv : MemSobolevMultiIndex b v k p Ω' μ) :
    MemSobolevMultiIndex b ((Ω' : Set E).indicator fun x ↦ α x • v x) k p Ω μ := by
  have hten := hv.memSobolev
  have hall : ∀ (m' : ℕ) (y' : Fin m' → E), m' ≤ k → ∃ w : E → F,
      HasWeakIteratedLineDerivOn y' v w Ω' μ ∧ MemLp w p (μ.restrict (Ω' : Set E)) := by
    intro m' y' hm'
    obtain ⟨w, hw, hwp⟩ := hten.exists_hasWeakIteratedFDerivOn (n := m') (by exact_mod_cast hm')
    exact ⟨_, hw.lineDeriv y',
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m' ↦ E) F y').comp_memLp' hwp⟩
  obtain ⟨M, hM⟩ := hαc.exists_bound_of_continuous hα.continuous
  refine ⟨hv.memLp.indicator_smul_of_le hα.continuous
    (fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hM x)), fun β hβ ↦ ?_⟩
  exact HasWeakIteratedLineDerivOn.exists_indicator_smul_of_forall_tuple hp hΩ' (∑ i, β i)
    (multiIndexTuple (b : ι → E) β) α hα hαc hαΩ' v fun m' y' hm' ↦ hall m' y' (hm'.trans hβ)

/-- **The cut-off of a locally Sobolev function is globally Sobolev, at every order**: for
`u ∈ W^{k,p}_loc(Ω)` and `θ ∈ 𝓓(Ω, ℝ)`, the function `θ u` extended by zero outside `Ω` lies in
`W^{k,p}(ℝ^N)`. This is the `θ`-reading of `H^{m+2}_loc(Ω)` in [brezis2011functional] Chapter 9,
Remark 25: `θ` is supported in an open `V ⋐ Ω`, on which `u ∈ W^{k,p}(V)`, and
`MemSobolevMultiIndex.indicator_smul_of_tsupport_subset` extends `θ u` from `V` to the whole
space. -/
theorem MemSobolevMultiIndexLoc.smul_testFunction {k : ℕ} {f : E → F} (hp : 1 ≤ p)
    (h : MemSobolevMultiIndexLoc b f k p Ω μ) (θ : 𝓓(Ω, ℝ)) :
    MemSobolevMultiIndex b ((Ω : Set E).indicator fun x ↦ θ x • f x) k p ⊤ μ := by
  obtain ⟨V, -, hVo, hθV, -, hVc, hVΩ, -⟩ :=
    θ.hasCompactSupport.exists_pos_forall_closedBall_subset Ω.isOpen θ.tsupport_subset
  have hVΩ' : V ⊆ Ω := subset_closure.trans hVΩ
  have hmem := MemSobolevMultiIndex.indicator_smul_of_tsupport_subset (Ω := ⊤) (Ω' := ⟨V, hVo⟩) hp
    le_top θ.contDiff θ.hasCompactSupport (fun x hx ↦ hθV hx.1) (h ⟨V, hVo⟩ hVc hVΩ)
  have heq : ((⟨V, hVo⟩ : Opens E) : Set E).indicator (fun x ↦ θ x • f x)
      = (Ω : Set E).indicator fun x ↦ θ x • f x := by
    change V.indicator (fun x ↦ θ x • f x) = (Ω : Set E).indicator fun x ↦ θ x • f x
    funext x
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV, Set.indicator_of_mem (hVΩ' hxV)]
    · rw [Set.indicator_of_notMem hxV]
      by_cases hxΩ : x ∈ (Ω : Set E)
      · rw [Set.indicator_of_mem hxΩ, image_eq_zero_of_notMem_tsupport fun h ↦ hxV (hθV h),
          zero_smul]
      · rw [Set.indicator_of_notMem hxΩ]
  rwa [heq] at hmem

end IndicatorSmul
