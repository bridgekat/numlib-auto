/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpSpace.KolmogorovRiesz`, with the restriction
operator in `Mathlib.MeasureTheory.Function.LpSpace.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Numlib.Analysis.Convolution.Lp
import Numlib.Topology.ContinuousMap.ArzelaAscoli

/-!
# The Kolmogorov–M. Riesz–Fréchet compactness criterion in `L^p`

A bounded family `F ⊆ L^p(G)`, `1 ≤ p < ∞`, on a finite-dimensional real normed space `G` with a
Haar measure `μ`, whose translates are uniformly continuous in `L^p`,
`‖f (· + h) - f‖ₚ → 0` as `h → 0` uniformly in `f ∈ F`, has compact closure once restricted to any
set `Ω` of finite measure:
`MeasureTheory.Lp.isCompact_closure_image_restrictCLM_of_uniform_translate`. If moreover the mass
of the family outside bounded sets is uniformly small, the family itself has compact closure in
`L^p(G)` (`MeasureTheory.Lp.isCompact_closure_of_uniform_translate_of_tight`). The convolution
with a fixed integrable kernel maps bounded sets to families of the first kind
(`MeasureTheory.Lp.isCompact_closure_image_restrictCLM_convolutionCLM`).

## Main definitions

* `MeasureTheory.Lp.restrictCLM 𝕜 E p μ s : Lp E p μ →L[𝕜] Lp E p (μ.restrict s)` — restriction
  of an `L^p` class to a set, a linear map of norm at most `1`. No measurability of `s` is needed.

## The proof

It follows [brezis2011functional] Theorem 4.26 in four steps, with the vector-valued
generalization costing nothing.

1. Mollification is uniformly close on `F`: for a normalized bump function `ρ` of small enough
   radius, `‖ρ ⋆ f - f‖ₚ ≤ ε` for all `f ∈ F`
   (`MeasureTheory.exists_forall_eLpNorm_convolution_sub_le_of_uniform_translate`). This is the
   weighted Minkowski inequality of `Numlib.Analysis.Convolution.Lp`, which bounds the error of
   mollification by the average of the translation errors over the support of `ρ`.
2. For a fixed `ρ` the mollified family is uniformly bounded and uniformly Lipschitz
   (`MeasureTheory.enorm_convolution_le_eLpNorm_mul_eLpNorm`,
   `MeasureTheory.lipschitzWith_convolution_of_contDiff`): Hölder's inequality for `ρ ⋆ f` and
   for `∇ρ ⋆ f = ∇(ρ ⋆ f)`.
3. The mass of the mollified family outside a large ball is uniformly small on `Ω`
   (`MeasureTheory.Lp.exists_forall_eLpNorm_indicator_compl_closedBall_le`), because `μ Ω < ∞`;
   with step 1 this is the book's Step 3, the same statement for the family itself.
4. On the compact ball the mollified family is precompact in the uniform norm by the
   Arzelà–Ascoli theorem, hence, after extension by zero, totally bounded in `L^p(Ω)`; steps 1 and
   3 put `F|_Ω` within `ε` of that set, so `F|_Ω` is totally bounded
   (`MeasureTheory.Lp.totallyBounded_image_restrictCLM_of_uniform_translate`), and `L^p(Ω)` is
   complete.

The set `Ω` need not be measurable and need not be bounded, only of finite measure; the family
`F` is a set of `L^p` classes and the translation hypothesis is stated on the coerced functions,
which is the form in which the Sobolev embedding theorems produce it.

## References

Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Universitext, Springer, 2011 [brezis2011functional], §4.5: Theorem 4.26, Corollaries 4.27 and
4.28, Lemma 4.3.
-/

open Filter Function MeasureTheory MeasureTheory.Measure Metric Set Topology
open ContinuousLinearMap
open scoped Convolution ENNReal NNReal

noncomputable section

namespace MeasureTheory

/-! ### Restriction of `L^p` classes to a set -/

section Restrict

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {α : Type*}
  [MeasurableSpace α] {p : ℝ≥0∞} {μ : Measure α}

variable (𝕜 E p μ) in
/-- **Restriction of an `L^p` class to a set** `s`, as a bounded linear map
`Lp E p μ →L[𝕜] Lp E p (μ.restrict s)` of norm at most `1` (the book's `F|_Ω`,
[brezis2011functional] Theorem 4.26). No measurability of `s` is needed. -/
def Lp.restrictCLM [Fact (1 ≤ p)] (s : Set α) : Lp E p μ →L[𝕜] Lp E p (μ.restrict s) :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).restrict s).toLp f
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (ae_restrict_of_ae (Lp.coeFn_add f g))
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (ae_restrict_of_ae (Lp.coeFn_smul c f)) }
    1 fun f => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def, one_mul]
      exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
        (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- The restriction of `f` to `s` is `f` almost everywhere on `s`. -/
theorem Lp.coeFn_restrictCLM [Fact (1 ≤ p)] (s : Set α) (f : Lp E p μ) :
    ⇑(Lp.restrictCLM 𝕜 E p μ s f) =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

/-- The restriction operator has norm at most `1`. -/
theorem Lp.norm_restrictCLM_le [Fact (1 ≤ p)] (s : Set α) : ‖Lp.restrictCLM 𝕜 E p μ s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The restriction of an `L^p` class does not increase its norm. -/
theorem Lp.norm_restrictCLM_apply_le [Fact (1 ≤ p)] (s : Set α) (f : Lp E p μ) :
    ‖Lp.restrictCLM 𝕜 E p μ s f‖ ≤ ‖f‖ := by
  have h := (Lp.restrictCLM 𝕜 E p μ s).le_of_opNorm_le (Lp.norm_restrictCLM_le s) f
  rwa [one_mul] at h

end Restrict

end MeasureTheory

/-! ### Total boundedness through approximation -/

/-- A set which is, for every `ε > 0`, within `ε` of a totally bounded set is totally bounded. -/
theorem Metric.totallyBounded_of_forall_exists_totallyBounded {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (h : ∀ ε > 0, ∃ t : Set X, TotallyBounded t ∧ ∀ x ∈ s, ∃ y ∈ t, dist x y < ε) :
    TotallyBounded s := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, ht, hst⟩ := h (ε / 2) (by positivity)
  obtain ⟨N, hN, htN⟩ := Metric.totallyBounded_iff.1 ht (ε / 2) (by positivity)
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hst x hx
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (htN hy)
  refine Set.mem_iUnion₂.2 ⟨z, hz, ?_⟩
  rw [Metric.mem_ball] at *
  linarith [dist_triangle x y z]

namespace MeasureTheory

/-! ### The four steps -/

section Steps

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞}

/-- **Step 1** of [brezis2011functional] Theorem 4.26: if the translates of the members of `F` are
uniformly continuous in `L^p`, then mollification by a normalized bump function of small enough
radius is uniformly close to the identity on `F`: there is `δ > 0` such that
`‖ρ ⋆ f - f‖ₚ ≤ ε` for all `f ∈ F` and every normalized bump `ρ` of outer radius `< δ`. -/
theorem exists_forall_eLpNorm_convolution_sub_le_of_uniform_translate [CompleteSpace E]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {F : Set (Lp E p μ)}
    (hτ : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ h : G, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p μ < ε)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : G), φ.rOut < δ → ∀ f ∈ F,
      eLpNorm (φ.normed μ ⋆[lsmul ℝ ℝ, μ] ⇑f - ⇑f) p μ ≤ ε := by
  have hp1 : 1 ≤ p := Fact.out
  have hq0 : (0:ℝ) < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp1).ne' hp
  obtain ⟨δ, hδ, hδF⟩ := hτ ε hε
  refine ⟨δ, hδ, fun φ hφ f hf => ?_⟩
  have hkey : eLpNorm (φ.normed μ ⋆[lsmul ℝ ℝ, μ] ⇑f - ⇑f) p μ ^ p.toReal ≤ ε ^ p.toReal := by
    refine (eLpNorm_convolution_sub_rpow_le hp1 hp (Lp.memLp f) φ.nonneg_normed
      φ.integrable_normed φ.integral_normed).trans ?_
    have hpt : ∀ t : G, ‖φ.normed μ t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal
        ≤ ‖φ.normed μ t‖ₑ * ε ^ p.toReal := by
      intro t
      by_cases ht : t ∈ support (φ.normed μ)
      · rw [φ.support_normed_eq, mem_ball_zero_iff] at ht
        gcongr
        have := hδF f hf (-t) (by rw [norm_neg]; linarith)
        simp only [← sub_eq_add_neg] at this
        exact this.le
      · simp [notMem_support.1 ht]
    calc ∫⁻ t, ‖φ.normed μ t‖ₑ * eLpNorm (fun x => f (x - t) - f x) p μ ^ p.toReal ∂μ
        ≤ ∫⁻ t, ‖φ.normed μ t‖ₑ * ε ^ p.toReal ∂μ := lintegral_mono hpt
      _ = ε ^ p.toReal := by
          rw [lintegral_mul_const'' _ φ.continuous_normed.aestronglyMeasurable.enorm,
            lintegral_enorm_eq_one φ.nonneg_normed φ.integrable_normed φ.integral_normed, one_mul]
  exact (ENNReal.rpow_le_rpow_iff hq0).1 hkey

/-- **Step 2** of [brezis2011functional] Theorem 4.26, the uniform bound (24): for `ρ ∈ L^q` and
`f ∈ L^p` with `1/p + 1/q = 1`, `‖(ρ ⋆ f) x‖ ≤ ‖ρ‖_q * ‖f‖ₚ` at every point. This is Mathlib's
`MeasureTheory.enorm_convolution_le` with the constant `‖lsmul ℝ ℝ‖ ≤ 1` removed. -/
theorem enorm_convolution_le_eLpNorm_mul_eLpNorm {q : ℝ≥0∞} [q.HolderConjugate p] {ρ : G → ℝ}
    {f : G → E} (hρ : AEStronglyMeasurable ρ μ) (hf : AEStronglyMeasurable f μ) (x : G) :
    ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ≤ eLpNorm ρ q μ * eLpNorm f p μ := by
  refine (enorm_convolution_le (p := q) (q := p) (lsmul ℝ ℝ) hρ hf x).trans ?_
  calc ‖(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ₑ * eLpNorm ρ q μ * eLpNorm f p μ
      ≤ 1 * eLpNorm ρ q μ * eLpNorm f p μ := by gcongr; exact opENorm_lsmul_le
    _ = eLpNorm ρ q μ * eLpNorm f p μ := by rw [one_mul]

/-- **Step 2** of [brezis2011functional] Theorem 4.26, the Lipschitz bound (25): for a `C¹`
kernel `ρ` with compact support and `f ∈ L^p`, `1/p + 1/q = 1`, the convolution `ρ ⋆ f` is
Lipschitz with constant `‖∇ρ‖_q * ‖f‖ₚ`, because `∇(ρ ⋆ f) = ∇ρ ⋆ f` is bounded by Hölder's
inequality. -/
theorem lipschitzWith_convolution_of_contDiff [CompleteSpace E] {q : ℝ≥0∞} [p.HolderConjugate q]
    {ρ : G → ℝ} (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ) {f : G → E} (hf : MemLp f p μ) :
    LipschitzWith ((eLpNorm (fderiv ℝ ρ) q μ).toNNReal * (eLpNorm f p μ).toNNReal)
      (ρ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hp1 : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  have hloc : LocallyIntegrable f μ := hf.locallyIntegrable hp1
  set L : ℝ →L[ℝ] E →L[ℝ] E := lsmul ℝ ℝ with hL
  have hderiv : ∀ x, HasFDerivAt (ρ ⋆[L, μ] f) ((fderiv ℝ ρ ⋆[L.precompL G, μ] f) x) x :=
    fun x => hcρ.hasFDerivAt_convolution_left L hρ hloc x
  have hdρ : MemLp (fderiv ℝ ρ) q μ :=
    (hρ.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport (hcρ.fderiv ℝ)
  have h1 : ‖L.precompL G‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 ((norm_precompL_le G L).trans opNorm_lsmul_le)
  have hbound : ∀ x, ‖(fderiv ℝ ρ ⋆[L.precompL G, μ] f) x‖ₑ
      ≤ eLpNorm (fderiv ℝ ρ) q μ * eLpNorm f p μ := by
    intro x
    refine (enorm_convolution_le (p := q) (q := p) (L.precompL G)
      hdρ.aestronglyMeasurable hf.aestronglyMeasurable x).trans ?_
    calc ‖L.precompL G‖ₑ * eLpNorm (fderiv ℝ ρ) q μ * eLpNorm f p μ
        ≤ 1 * eLpNorm (fderiv ℝ ρ) q μ * eLpNorm f p μ := by gcongr
      _ = eLpNorm (fderiv ℝ ρ) q μ * eLpNorm f p μ := by rw [one_mul]
  refine lipschitzWith_of_nnnorm_fderiv_le (fun x => (hderiv x).differentiableAt) fun x => ?_
  rw [(hderiv x).fderiv, ← ENNReal.coe_le_coe, ENNReal.coe_mul,
    ENNReal.coe_toNNReal hdρ.eLpNorm_ne_top, ENNReal.coe_toNNReal hf.eLpNorm_ne_top,
    ← enorm_eq_nnnorm]
  exact hbound x

omit [NormedSpace ℝ G] [FiniteDimensional ℝ G] [μ.IsAddHaarMeasure] [NormedSpace ℝ E] in
/-- The mass of a uniformly bounded family outside large balls is uniformly small on a set of
finite measure: for `M`-bounded functions `g` and `μ Ω ≠ ∞`, there is `R` with
`‖g‖_{L^p(Ω ∖ B(0, R))} ≤ ε` for all such `g`. -/
theorem exists_forall_eLpNorm_indicator_compl_closedBall_le_of_forall_norm_le [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {Ω : Set G} (hΩ : μ Ω ≠ ∞) {M : ℝ} {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ g : G → E, AEStronglyMeasurable g μ → (∀ x, ‖g x‖ ≤ M) →
      eLpNorm ((closedBall (0:G) R)ᶜ.indicator g) p (μ.restrict Ω) ≤ ε := by
  have hp1 : 1 ≤ p := Fact.out
  have hr : 0 < p.toReal⁻¹ := by
    rw [inv_pos]
    exact ENNReal.toReal_pos (zero_lt_one.trans_le hp1).ne' hp
  -- the measure of `Ω` outside the ball of radius `n` tends to `0`
  set Ω' := toMeasurable μ Ω with hΩ'
  have hΩ'm : MeasurableSet Ω' := measurableSet_toMeasurable μ Ω
  have hmeas : ∀ n : ℕ, NullMeasurableSet (Ω' \ closedBall (0:G) n) μ := fun n =>
    (hΩ'm.diff measurableSet_closedBall).nullMeasurableSet
  have hanti : Antitone fun n : ℕ => Ω' \ closedBall (0:G) n := fun m n hmn =>
    sdiff_subset_sdiff_right (closedBall_subset_closedBall (by exact_mod_cast hmn))
  have hinter : ⋂ n : ℕ, Ω' \ closedBall (0:G) n = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    rw [mem_iInter] at hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact (hx n).2 (mem_closedBall_zero_iff.2 hn)
  have htend : Tendsto (fun n : ℕ => μ (Ω' \ closedBall (0:G) n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop hmeas hanti
      ⟨0, ne_top_of_le_ne_top (by rwa [measure_toMeasurable]) (measure_mono sdiff_subset)⟩
    rwa [hinter, measure_empty] at this
  -- hence so does the bound `μ(Ω ∖ B)^(1/p) * M`
  have htend' : Tendsto
      (fun n : ℕ => μ (Ω' \ closedBall (0:G) n) ^ p.toReal⁻¹ * ENNReal.ofReal M) atTop (𝓝 0) := by
    have h1 := ((ENNReal.continuous_rpow_const (y := p.toReal⁻¹)).tendsto 0).comp htend
    rw [Function.comp_def, ENNReal.zero_rpow_of_pos hr] at h1
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 htend').2 ε hε).exists
  refine ⟨n, fun g hg hgM => ?_⟩
  have hsub : (closedBall (0:G) n)ᶜ ∩ Ω ⊆ Ω' \ closedBall (0:G) n := fun x hx =>
    ⟨subset_toMeasurable μ Ω hx.2, hx.1⟩
  calc eLpNorm ((closedBall (0:G) n)ᶜ.indicator g) p (μ.restrict Ω)
      = eLpNorm g p ((μ.restrict Ω).restrict (closedBall (0:G) n)ᶜ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall.compl
    _ ≤ ((μ.restrict Ω).restrict (closedBall (0:G) n)ᶜ) univ ^ p.toReal⁻¹ * ENNReal.ofReal M :=
        eLpNorm_le_of_ae_bound (hg.mono_measure (Measure.restrict_le_self.trans
          Measure.restrict_le_self)) (ae_of_all _ hgM)
    _ ≤ μ (Ω' \ closedBall (0:G) n) ^ p.toReal⁻¹ * ENNReal.ofReal M := by
        refine mul_le_mul_left (ENNReal.rpow_le_rpow ?_ hr.le) _
        rw [Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_closedBall.compl]
        exact measure_mono hsub
    _ ≤ ε := hn.le

/-! ### Step 4 and the theorem -/

/-- **Step 4** of [brezis2011functional] Theorem 4.26: under the hypotheses of the
Kolmogorov–M. Riesz–Fréchet theorem, the restrictions to `Ω` of the members of `F` form a totally
bounded subset of `L^p(Ω)`. For `ε > 0`, steps 1 and 3 give a mollifier `ρ` and a ball `K` such
that every `f|_Ω` is within `ε` of the extension by zero of `(ρ ⋆ f)|_K`, and these extensions
form a totally bounded set: the family `(ρ ⋆ f)|_K` is precompact in `C(K, E)` by the
Arzelà–Ascoli theorem (step 2), and extension by zero is Lipschitz from `C(K, E)` into
`L^p(Ω)`. -/
theorem Lp.totallyBounded_image_restrictCLM_of_uniform_translate [FiniteDimensional ℝ E]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {F : Set (Lp E p μ)} (hF : Bornology.IsBounded F)
    (hτ : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ h : G, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p μ < ε)
    {Ω : Set G} (hΩ : μ Ω ≠ ∞) : TotallyBounded (Lp.restrictCLM ℝ E p μ Ω '' F) := by
  classical
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨M, hM⟩ := hF.exists_norm_le
  set M₀ := max M 0 with hM₀
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hM' : ∀ f ∈ F, ‖f‖ ≤ M₀ := fun f hf => (hM f hf).trans (le_max_left _ _)
  set q := ENNReal.conjExponent p with hq
  have hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp1
  have hfin : IsFiniteMeasure (μ.restrict Ω) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  refine Metric.totallyBounded_of_forall_exists_totallyBounded fun ε hε => ?_
  have hε3 : (0:ℝ≥0∞) < ENNReal.ofReal (ε / 3) := ENNReal.ofReal_pos.2 (by positivity)
  -- Step 1: a mollifier uniformly close to the identity on `F`
  obtain ⟨δ, hδ, hδF⟩ := exists_forall_eLpNorm_convolution_sub_le_of_uniform_translate hp hτ hε3
  let φ : ContDiffBump (0 : G) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  set ρ := φ.normed μ with hρ
  have hρc : Continuous ρ := φ.continuous_normed
  have hρm : AEStronglyMeasurable ρ μ := hρc.aestronglyMeasurable
  have hρq : MemLp ρ q μ := hρc.memLp_of_hasCompactSupport φ.hasCompactSupport_normed
  have hρF : ∀ f ∈ F, eLpNorm (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f - ⇑f) p μ ≤ ENNReal.ofReal (ε / 3) :=
    fun f hf => hδF φ (by change δ / 2 < δ; linarith) f hf
  have hconv : ∀ f : Lp E p μ, Continuous (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) := fun f =>
    (φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (φ.contDiff_normed (n := 1))
      ((Lp.memLp f).locallyIntegrable hp1)).continuous
  -- Step 2: the mollified family is uniformly bounded and uniformly Lipschitz
  set B : ℝ := (eLpNorm ρ q μ).toReal * M₀ with hB
  have hbdd : ∀ f ∈ F, ∀ x, ‖(ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x‖ ≤ B := by
    intro f hf x
    have h1 : ‖(ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x‖ₑ ≤ eLpNorm ρ q μ * ENNReal.ofReal M₀ := by
      refine (enorm_convolution_le_eLpNorm_mul_eLpNorm (p := p) (q := q) hρm
        (Lp.aestronglyMeasurable f) x).trans ?_
      gcongr
      rw [← ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top, ← Lp.norm_def]
      exact ENNReal.ofReal_le_ofReal (hM' f hf)
    rw [← toReal_enorm, hB, ← ENNReal.toReal_ofReal hM₀0, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hρq.eLpNorm_ne_top ENNReal.ofReal_ne_top) h1
  set Lc : ℝ≥0 := (eLpNorm (fderiv ℝ ρ) q μ).toNNReal * M₀.toNNReal with hLc
  have hlip : ∀ f ∈ F, LipschitzWith Lc (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) := by
    intro f hf
    refine (lipschitzWith_convolution_of_contDiff (φ.contDiff_normed (n := 1))
      φ.hasCompactSupport_normed (Lp.memLp f)).weaken (mul_le_mul_right ?_ _)
    rw [← Lp.nnnorm_def, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hM₀0]
    exact hM' f hf
  -- Step 3: the mollified family has small mass outside a ball
  obtain ⟨R, hR⟩ := exists_forall_eLpNorm_indicator_compl_closedBall_le_of_forall_norm_le
    (E := E) (M := B) hp hΩ hε3
  set K := closedBall (0:G) R with hK
  have hKm : MeasurableSet K := measurableSet_closedBall
  have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 R)
  -- the mollified family on `K`, precompact in `C(K, E)` by Arzelà–Ascoli
  let T : Lp E p μ → C(K, E) := fun f => ContinuousMap.restrict K ⟨_, hconv f⟩
  have hT : ∀ f (x : K), T f x = (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x := fun f x => rfl
  have hS : TotallyBounded (T '' F) := by
    refine (ContinuousMap.isCompact_closure_of_forall_norm_le (M := B) ?_ ?_).totallyBounded.subset
      subset_closure
    · rintro g ⟨f, hf, rfl⟩ x
      exact hbdd f hf x
    · refine Metric.equicontinuous_of_continuity_modulus (fun d => (Lc : ℝ) * d) ?_ _ ?_
      · simpa using (tendsto_id (x := 𝓝 (0:ℝ))).const_mul (Lc : ℝ)
      · rintro x y ⟨g, f, hf, rfl⟩
        exact (hlip f hf).dist_le_mul (x : G) (y : G)
  -- extension by zero, `C(K, E) → L^p(Ω)`, is Lipschitz
  let ext : C(K, E) → G → E := fun g x => if h : x ∈ K then g ⟨x, h⟩ else 0
  have hext_bound : ∀ (g : C(K, E)) (x : G), ‖ext g x‖ ≤ ‖g‖ := by
    intro g x
    by_cases hx : x ∈ K
    · simpa [ext, hx] using g.norm_coe_le_norm ⟨x, hx⟩
    · simp [ext, hx]
  have hext_sub : ∀ g g' : C(K, E), ext g - ext g' = ext (g - g') := by
    intro g g'
    funext x
    by_cases hx : x ∈ K <;> simp [ext, hx]
  have hext_meas : ∀ g : C(K, E), AEStronglyMeasurable (ext g) (μ.restrict Ω) := by
    intro g
    have hind : ext g = K.indicator (ext g) := by
      funext x
      by_cases hx : x ∈ K <;> simp [ext, hx]
    have hcont : ContinuousOn (ext g) K := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert g.continuous using 1
      funext x
      simp [ext, Set.domRestrict, x.2]
    rw [hind]
    exact (aestronglyMeasurable_indicator_iff hKm).2 (hcont.aestronglyMeasurable hKm)
  have hext_mem : ∀ g : C(K, E), MemLp (ext g) p (μ.restrict Ω) := fun g =>
    MemLp.of_bound (hext_meas g) ‖g‖ (ae_of_all _ (hext_bound g))
  let Φ : C(K, E) → Lp E p (μ.restrict Ω) := fun g => (hext_mem g).toLp (ext g)
  have hΦ : LipschitzWith (μ Ω ^ p.toReal⁻¹).toNNReal Φ := by
    refine LipschitzWith.of_dist_le_mul fun g g' => ?_
    have h1 : dist (Φ g) (Φ g') = (eLpNorm (ext (g - g')) p (μ.restrict Ω)).toReal := by
      rw [Lp.dist_def, ← hext_sub]
      congr 1
      exact eLpNorm_congr_ae ((MemLp.coeFn_toLp _).sub (MemLp.coeFn_toLp _))
    have h2 : dist g g' = ‖g - g'‖ := _root_.dist_eq_norm g g'
    rw [h1, h2]
    change _ ≤ (μ Ω ^ p.toReal⁻¹).toReal * ‖g - g'‖
    refine (ENNReal.toReal_mono ?_ (eLpNorm_le_of_ae_bound (hext_meas (g - g'))
      (ae_of_all _ (hext_bound (g - g'))))).trans (le_of_eq ?_)
    · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
        (by rwa [Measure.restrict_apply_univ])) ENNReal.ofReal_ne_top
    · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), Measure.restrict_apply_univ]
  refine ⟨Φ '' (T '' F), hS.image hΦ.uniformContinuous, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨Φ (T f), ⟨T f, ⟨f, hf, rfl⟩, rfl⟩, ?_⟩
  -- `f|_Ω` is within `2ε/3` of `Φ (T f)`, the extension by zero of `(ρ ⋆ f)|_K`
  have hext_T : ext (T f) = K.indicator (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) := by
    funext x
    by_cases hx : x ∈ K <;> simp [ext, hT, hx]
  have hae : (⇑(Lp.restrictCLM ℝ E p μ Ω f) - ⇑(Φ (T f))) =ᵐ[μ.restrict Ω]
      fun x => (f x - (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x) + Kᶜ.indicator (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x := by
    filter_upwards [Lp.coeFn_restrictCLM (𝕜 := ℝ) Ω f, MemLp.coeFn_toLp (hext_mem (T f))]
      with x h2 h3
    rw [Pi.sub_apply, h2, h3, hext_T, Set.indicator_compl, Pi.sub_apply, sub_add_sub_cancel]
  have hmeas : AEStronglyMeasurable (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) μ :=
    hρm.convolution (lsmul ℝ ℝ) (Lp.aestronglyMeasurable f)
  have hbound : eLpNorm (⇑(Lp.restrictCLM ℝ E p μ Ω f) - ⇑(Φ (T f))) p (μ.restrict Ω)
      ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_add_le hp1).trans (add_le_add ?_ (hR _ hmeas (hbdd f hf)))
    calc eLpNorm (fun x => f x - (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x) p (μ.restrict Ω)
        ≤ eLpNorm (fun x => f x - (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x) p μ :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f - ⇑f) p μ := by
          rw [← eLpNorm_neg]
          congr 1
          funext x
          simp
      _ ≤ ENNReal.ofReal (ε / 3) := hρF f hf
  rw [Lp.dist_def]
  calc (eLpNorm (⇑(Lp.restrictCLM ℝ E p μ Ω f) - ⇑(Φ (T f))) p (μ.restrict Ω)).toReal
      ≤ (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)).toReal :=
        ENNReal.toReal_mono (by simp) hbound
    _ = ε / 3 + ε / 3 := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal (by positivity)]
    _ < ε := by linarith

/-- **The Kolmogorov–M. Riesz–Fréchet theorem** ([brezis2011functional] Theorem 4.26). Let `G` be
a finite-dimensional real normed space with a Haar measure `μ`, `E` a finite-dimensional real
normed space, `1 ≤ p < ∞`, and `F ⊆ L^p(μ, E)` a bounded family whose translates are uniformly
continuous in `L^p`: for every `ε > 0` there is `δ > 0` with `‖f (· + h) - f‖ₚ < ε` for all
`f ∈ F` and all `‖h‖ < δ`. Then for every set `Ω` of finite measure, measurable or not, the
restrictions `f|_Ω`, `f ∈ F`, have compact closure in `L^p(Ω)`. -/
theorem Lp.isCompact_closure_image_restrictCLM_of_uniform_translate [FiniteDimensional ℝ E]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {F : Set (Lp E p μ)} (hF : Bornology.IsBounded F)
    (hτ : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ h : G, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p μ < ε)
    {Ω : Set G} (hΩ : μ Ω ≠ ∞) : IsCompact (closure (Lp.restrictCLM ℝ E p μ Ω '' F)) :=
  isCompact_iff_totallyBounded_isComplete.2
    ⟨(Lp.totallyBounded_image_restrictCLM_of_uniform_translate hp hF hτ hΩ).closure,
      isClosed_closure.isComplete⟩

/-- **Step 3** of [brezis2011functional] Theorem 4.26: under the hypotheses of the theorem, the
mass of the family outside a large enough ball is uniformly small on `Ω`: there is `R` with
`‖f‖_{L^p(Ω ∖ B(0, R))} ≤ ε` for all `f ∈ F`. From step 1 and the same statement for the
mollified family. -/
theorem Lp.exists_forall_eLpNorm_indicator_compl_closedBall_le [CompleteSpace E] [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {F : Set (Lp E p μ)} (hF : Bornology.IsBounded F)
    (hτ : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ h : G, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p μ < ε)
    {Ω : Set G} (hΩ : μ Ω ≠ ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ f ∈ F, eLpNorm ((closedBall (0:G) R)ᶜ.indicator f) p (μ.restrict Ω) ≤ ε := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨M, hM⟩ := hF.exists_norm_le
  set M₀ := max M 0 with hM₀
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hM' : ∀ f ∈ F, ‖f‖ ≤ M₀ := fun f hf => (hM f hf).trans (le_max_left _ _)
  set q := ENNReal.conjExponent p with hq
  have hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp1
  have hε2 : (0:ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨δ, hδ, hδF⟩ := exists_forall_eLpNorm_convolution_sub_le_of_uniform_translate hp hτ hε2
  let φ : ContDiffBump (0 : G) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  set ρ := φ.normed μ with hρ
  have hρm : AEStronglyMeasurable ρ μ := φ.continuous_normed.aestronglyMeasurable
  have hρq : MemLp ρ q μ :=
    φ.continuous_normed.memLp_of_hasCompactSupport φ.hasCompactSupport_normed
  have hρF : ∀ f ∈ F, eLpNorm (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f - ⇑f) p μ ≤ ε / 2 :=
    fun f hf => hδF φ (by change δ / 2 < δ; linarith) f hf
  have hbdd : ∀ f ∈ F, ∀ x, ‖(ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x‖ ≤ (eLpNorm ρ q μ).toReal * M₀ := by
    intro f hf x
    have h1 : ‖(ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) x‖ₑ ≤ eLpNorm ρ q μ * ENNReal.ofReal M₀ := by
      refine (enorm_convolution_le_eLpNorm_mul_eLpNorm (p := p) (q := q) hρm
        (Lp.aestronglyMeasurable f) x).trans ?_
      gcongr
      rw [← ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top, ← Lp.norm_def]
      exact ENNReal.ofReal_le_ofReal (hM' f hf)
    rw [← toReal_enorm, ← ENNReal.toReal_ofReal hM₀0, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hρq.eLpNorm_ne_top ENNReal.ofReal_ne_top) h1
  obtain ⟨R, hR⟩ := exists_forall_eLpNorm_indicator_compl_closedBall_le_of_forall_norm_le
    (E := E) (M := (eLpNorm ρ q μ).toReal * M₀) hp hΩ hε2
  refine ⟨R, fun f hf => ?_⟩
  have hmeas : AEStronglyMeasurable (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) μ :=
    hρm.convolution (lsmul ℝ ℝ) (Lp.aestronglyMeasurable f)
  have hsplit : (closedBall (0:G) R)ᶜ.indicator ⇑f
      = (closedBall (0:G) R)ᶜ.indicator (⇑f - ρ ⋆[lsmul ℝ ℝ, μ] ⇑f)
        + (closedBall (0:G) R)ᶜ.indicator (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) := by
    rw [← Set.indicator_add', sub_add_cancel]
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans ?_
  calc eLpNorm ((closedBall (0:G) R)ᶜ.indicator (⇑f - ρ ⋆[lsmul ℝ ℝ, μ] ⇑f)) p (μ.restrict Ω)
        + eLpNorm ((closedBall (0:G) R)ᶜ.indicator (ρ ⋆[lsmul ℝ ℝ, μ] ⇑f)) p (μ.restrict Ω)
      ≤ eLpNorm (⇑f - ρ ⋆[lsmul ℝ ℝ, μ] ⇑f) p μ + ε / 2 := by
        gcongr
        · exact (eLpNorm_indicator_le _ measurableSet_closedBall.compl).trans
            (eLpNorm_mono_measure _ Measure.restrict_le_self)
        · exact hR _ hmeas (hbdd f hf)
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        rw [← eLpNorm_neg, neg_sub]
        exact hρF f hf
    _ = ε := ENNReal.add_halves ε

/-! ### The corollaries -/

/-- **Compactness in `L^p(G)` itself** ([brezis2011functional] Corollary 4.27): a bounded family
`F ⊆ L^p(G)`, `1 ≤ p < ∞`, whose translates are uniformly continuous in `L^p` and which is
*tight* — for every `ε > 0` there is a bounded measurable `Ω` with `‖f‖_{L^p(Ωᶜ)} < ε` for all
`f ∈ F` — has compact closure in `L^p(G)`. The restrictions to `Ω` are totally bounded by the
Kolmogorov–M. Riesz–Fréchet theorem, and their extensions by zero are within `ε` of `F`. -/
theorem Lp.isCompact_closure_of_uniform_translate_of_tight [FiniteDimensional ℝ E]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {F : Set (Lp E p μ)} (hF : Bornology.IsBounded F)
    (hτ : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ h : G, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p μ < ε)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ Ω : Set G, Bornology.IsBounded Ω ∧ MeasurableSet Ω ∧
      ∀ f ∈ F, eLpNorm (Ωᶜ.indicator f) p μ < ε) :
    IsCompact (closure F) := by
  refine isCompact_iff_totallyBounded_isComplete.2 ⟨TotallyBounded.closure ?_,
    isClosed_closure.isComplete⟩
  refine Metric.totallyBounded_of_forall_exists_totallyBounded fun ε hε => ?_
  obtain ⟨Ω, hΩb, hΩm, hΩF⟩ :=
    htight (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.2 (by positivity))
  have hΩ : μ Ω ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hΩb.isCompact_closure.measure_lt_top).ne
  have hT := Lp.totallyBounded_image_restrictCLM_of_uniform_translate hp hF hτ hΩ
  -- extension by zero, `L^p(Ω) → L^p(G)`, is an isometry
  obtain ⟨Ext, hExt_coe⟩ : ∃ Ext : Lp E p (μ.restrict Ω) → Lp E p μ,
      ∀ g : Lp E p (μ.restrict Ω), ⇑(Ext g) =ᵐ[μ] Ω.indicator ⇑g :=
    ⟨fun g => ((memLp_indicator_iff_restrict hΩm).2 (Lp.memLp g)).toLp (Ω.indicator g),
      fun g => MemLp.coeFn_toLp _⟩
  have hExt : LipschitzWith 1 Ext := by
    refine LipschitzWith.of_dist_le_mul fun g g' => ?_
    rw [NNReal.coe_one, one_mul, Lp.dist_def, Lp.dist_def]
    refine le_of_eq (congrArg ENNReal.toReal ?_)
    rw [eLpNorm_congr_ae ((hExt_coe g).sub (hExt_coe g')), ← Set.indicator_sub',
      eLpNorm_indicator_eq_eLpNorm_restrict hΩm]
  refine ⟨Ext '' (Lp.restrictCLM ℝ E p μ Ω '' F), hT.image hExt.uniformContinuous, ?_⟩
  intro f hf
  refine ⟨Ext (Lp.restrictCLM ℝ E p μ Ω f), ⟨_, ⟨f, hf, rfl⟩, rfl⟩, ?_⟩
  -- `f` is within `ε/2` of the extension by zero of its restriction
  have hae : (⇑f - ⇑(Ext (Lp.restrictCLM ℝ E p μ Ω f))) =ᵐ[μ] Ωᶜ.indicator f := by
    have h1 : Ω.indicator (⇑(Lp.restrictCLM ℝ E p μ Ω f)) =ᵐ[μ] Ω.indicator (⇑f) := by
      filter_upwards [(ae_restrict_iff' hΩm).1 (Lp.coeFn_restrictCLM (𝕜 := ℝ) Ω f)] with x hx
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ, hx hxΩ]
      · rw [Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ]
    filter_upwards [hExt_coe (Lp.restrictCLM ℝ E p μ Ω f), h1] with x h2 h3
    rw [Pi.sub_apply, h2, h3, Set.indicator_compl, Pi.sub_apply]
  rw [Lp.dist_def, eLpNorm_congr_ae hae]
  calc (eLpNorm (Ωᶜ.indicator ⇑f) p μ).toReal
      ≤ (ENNReal.ofReal (ε / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hΩF f hf).le
    _ = ε / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < ε := by linarith

/-- **Convolution with a fixed integrable kernel is compact on bounded sets, after restriction**
([brezis2011functional] Corollary 4.28): for `K ∈ L¹(G)`, a bounded `B ⊆ L^p(G)` with
`1 ≤ p < ∞` and any `Ω` of finite measure, the restrictions to `Ω` of the convolutions `K ⋆ u`,
`u ∈ B`, have compact closure in `L^p(Ω)`. The family `K ⋆ B` is bounded by Young's inequality
and its translates are uniformly continuous because `τ_h (K ⋆ u) - K ⋆ u = (τ_h K - K) ⋆ u` and
`‖τ_h K - K‖₁ → 0` (the continuity of translation in `L¹`, [brezis2011functional] Lemma 4.3). -/
theorem Lp.isCompact_closure_image_restrictCLM_convolutionCLM [FiniteDimensional ℝ E]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {K : G → ℝ} (hK : Integrable K μ) {B : Set (Lp E p μ)}
    (hB : Bornology.IsBounded B) {Ω : Set G} (hΩ : μ Ω ≠ ∞) :
    IsCompact (closure (Lp.restrictCLM ℝ E p μ Ω '' (Lp.convolutionCLM E p hK '' B))) := by
  have hp1 : 1 ≤ p := Fact.out
  have hK1 : MemLp K 1 μ := memLp_one_iff_integrable.2 hK
  obtain ⟨C, hC⟩ := hB.exists_norm_le
  set C₀ := max C 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  have hC' : ∀ u ∈ B, ‖u‖ ≤ C₀ := fun u hu => (hC u hu).trans (le_max_left _ _)
  refine Lp.isCompact_closure_image_restrictCLM_of_uniform_translate hp ?_ ?_ hΩ
  · -- `K ⋆ B` is bounded
    refine isBounded_iff_forall_norm_le.2 ⟨(eLpNorm K 1 μ).toReal * C₀, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (Lp.norm_convolutionCLM_apply_le hK u).trans
      (mul_le_mul_of_nonneg_left (hC' u hu) ENNReal.toReal_nonneg)
  · -- the translates of `K ⋆ u` are uniformly continuous in `L^p`
    intro ε hε
    have hlim : Tendsto (fun t : G => eLpNorm (fun x => K (x - t) - K x) 1 μ * ENNReal.ofReal C₀)
        (𝓝 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const (hK1.tendsto_eLpNorm_sub_translate le_rfl
        ENNReal.one_ne_top) (Or.inr ENNReal.ofReal_ne_top)
    obtain ⟨δ, hδ, hδK⟩ := Metric.eventually_nhds_iff.1 ((tendsto_order.1 hlim).2 ε hε)
    refine ⟨δ, hδ, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ h hh
    have hKh : Integrable (fun t => K (t + h)) μ := hK.comp_add_right h
    -- the translate of `K ⋆ u` is `(τ_h K) ⋆ u`, so the difference is `(τ_h K - K) ⋆ u`
    have hcoe : ⇑(Lp.convolutionCLM E p hK u) =ᵐ[μ] K ⋆[lsmul ℝ ℝ, μ] ⇑u :=
      Lp.coeFn_convolutionCLM hK u
    have hcoe' : (fun x => (Lp.convolutionCLM E p hK u) (x + h))
        =ᵐ[μ] fun x => (K ⋆[lsmul ℝ ℝ, μ] ⇑u) (x + h) :=
      (measurePreserving_add_right μ h).quasiMeasurePreserving.ae hcoe
    have hae : (fun x => (Lp.convolutionCLM E p hK u) (x + h) - (Lp.convolutionCLM E p hK u) x)
        =ᵐ[μ] ((fun t => K (t + h)) - K) ⋆[lsmul ℝ ℝ, μ] ⇑u := by
      filter_upwards [hcoe, hcoe',
        (memLp_one_iff_integrable.2 hKh).ae_convolutionExistsAt (L := lsmul ℝ ℝ) hp1 (Lp.memLp u),
        hK1.ae_convolutionExistsAt (L := lsmul ℝ ℝ) hp1 (Lp.memLp u)] with x h1 h2 h3 h4
      rw [h1, h2, convolution_apply_add_right, h3.sub_distrib h4]
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_convolution_lsmul_le hp1 (hKh.sub hK).aestronglyMeasurable
      (Lp.aestronglyMeasurable u)).trans_lt ?_
    have hKh' : eLpNorm ((fun t => K (t + h)) - K) 1 μ
        = eLpNorm (fun x => K (x - -h) - K x) 1 μ := by
      congr 1
      funext x
      simp [sub_neg_eq_add]
    calc eLpNorm ((fun t => K (t + h)) - K) 1 μ * eLpNorm (⇑u) p μ
        ≤ eLpNorm (fun x => K (x - -h) - K x) 1 μ * ENNReal.ofReal C₀ := by
          rw [hKh']
          gcongr
          rw [← ENNReal.ofReal_toReal (Lp.memLp u).eLpNorm_ne_top, ← Lp.norm_def]
          exact ENNReal.ofReal_le_ofReal (hC' u hu)
      _ < ε := hδK (by rwa [dist_zero_right, _root_.norm_neg])


end Steps


end MeasureTheory

end
