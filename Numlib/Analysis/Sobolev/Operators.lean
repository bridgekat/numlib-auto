/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/MultiIndex.lean` and `Numlib/Analysis/Sobolev/Cutoff.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Calculus.Gradient
import Numlib.Analysis.Sobolev.Cutoff

/-!
# The typed operators between Sobolev spaces

The bounded linear maps between the typed spaces `SobolevMultiIndex F b k p Ω μ` of
`Numlib/Analysis/Sobolev/MultiIndex.lean` that the Sobolev theory of Brezis, *Functional
Analysis, Sobolev Spaces and Partial Differential Equations*, chapter 9, uses without naming
them, each assembled by one fixed pattern — define the function, prove the membership and the
bound at the predicate level, bundle by `MemSobolevMultiIndex.exists_sobolevMultiIndex` and
`SobolevMultiIndex.ext_of_fn_ae_eq`, and bound the `ℓ^p` norm of the tuple of derivatives
coordinatewise (`PiLp.norm_le_norm_of_forall_norm_le`):

* **restriction** to an open subset, `SobolevMultiIndex.restrictL : W^{k,p}(Ω) → W^{k,p}(Ω')`
  for `Ω' ≤ Ω`, of norm at most `1`;
* **the inclusion `W^{k,p}(Ω) → L^q(Ω)`** given the membership, `SobolevMultiIndex.toLpₗ`, in
  the vocabulary of `IsContinuousEmbedding`, with `fnL` as its case `q = p`;
* **the zero extension `u ↦ α u`** for a cut-off `α` (`IsSobolevCutoff`), as a bounded linear
  map `W^{1,p}(Ω) → W^{1,p}(E)`, `SobolevMultiIndex.extendZeroMulL` — the step (a) of the proof
  of the extension theorem, typed;
* **Lemma 9.5**: a `W^{k,p}(Ω)` function vanishing outside a compact subset of `Ω` lies in
  `W_0^{k,p}(Ω)` (`SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact`), at every order,
  with the general `L^p` lemmas on functions of compact support that it needs;
* **the inclusion `W^{k,p}(Ω) → W^{k,r}(Ω)` for `r ≤ p`** on a set of finite measure,
  `SobolevMultiIndex.toLowerExponentL`, over `MeasureTheory.Lp.monoExponentL`;
* **forgetting orders**, `SobolevMultiIndex.toLowerOrderL : W^{k,p}(Ω) → W^{k',p}(Ω)` for
  `k' ≤ k`, and **the partial derivative** `∂_i : W^{k+1,p}(Ω) → W^{k,p}(Ω)`
  (`SobolevMultiIndex.partialDerivL`), the typed form of the inductive definition of
  `W^{m+1,p}`, with the inductive step `SobolevMultiIndex.exists_succ_of_partialDeriv` (a
  function lying in `W^{j+1,q}` together with its partial derivatives lies in `W^{j+2,q}`) and
  the lifting to order `k` of a bounded operator at order one that preserves `W^{k,p}`
  (`SobolevMultiIndex.exists_continuousLinearMap_of_order`, by the closed graph theorem);
* **the density of the restrictions of `C_c^∞(ℝ^N)` functions** on a subspace with an extension
  operator
  (`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn`),
  the abstract form of Corollary 9.8, which is the one consumer of `restrictL` in the cut-off
  theory;
* **the partial derivatives on `ℝ^N`**: `∂ᵢu` as the weak derivative of `fn u` along `eᵢ`
  (`SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single`), membership of `W^{1,p}(Ω)` from the
  `N` partial derivatives and their uniqueness
  (`SobolevEuclidean.memSobolevMultiIndex_one_of_forall`,
  `SobolevEuclidean.weakDeriv_single_ae_eq`), their identification with the classical ones for a
  `C¹` representative (`SobolevEuclidean.weakDeriv_single_ae_eq_fderiv`), and the restricted
  pointwise gradient `u ↦ ∇u|_S` as a bounded linear map `W^{1,p}(Ω) → L^p(S; ℝ^N)`
  (`SobolevEuclidean.gradFnL`).

The predicate-level cut-off theory — locality, `C_c^1` test functions, cut-off functions and the
zero extension of `α u`, the multipliers, the cut-off sequence, the local spaces and the extension
predicate — is `Numlib/Analysis/Sobolev/Cutoff.lean`, which this module continues.

## References

[brezis2011functional], §9.2 (proof of Theorem 9.7, step (a)), §9.4 (Lemma 9.5), Corollary 9.8,
Corollary 9.15 (proof).
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace Topology

noncomputable section

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

/-- The `L^p(Ω)` norm of the function of `u ∈ W^{k,p}(Ω)` is at most `‖u‖`. -/
theorem eLpNorm_fn_le_ofReal_norm [Fact (1 ≤ p)] (u : SobolevMultiIndex F b k p Ω μ) :
    eLpNorm (fn u) p (μ.restrict (Ω : Set E)) ≤ ENNReal.ofReal ‖u‖ := by
  have h : ‖weakDeriv u 0‖ = (eLpNorm (fn u) p (μ.restrict (Ω : Set E))).toReal := by
    rw [Lp.norm_def]
    rfl
  rw [← ENNReal.ofReal_toReal (SobolevMultiIndex.memLp u).eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (h ▸ norm_weakDeriv_le u 0)

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

section OrderLifting

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {k : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ q)] {Ω Ω' : Opens E} {μ : Measure E}
  [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

namespace SobolevMultiIndex

omit [IsFiniteMeasureOnCompacts μ] in
/-- **The inductive step of the order lowering**: if `u ∈ W^{k+1,p}(Ω)` is almost everywhere the
function of `w₀ ∈ W^{j+1,q}(Ω)` and each partial derivative `∂_i u` is almost everywhere the
function of `w i ∈ W^{j+1,q}(Ω)`, then `u` is almost everywhere the function of an element `z`
of `W^{j+2,q}(Ω)`, with `‖z‖ ≤ #{|β| ≤ j + 2} (‖w₀‖ + ∑ i, ‖w i‖)`. The weak derivative
`∂^β u` for `β = β' + e_i` is `∂^{β'} ∂_i u = ∂^{β'} (w i)`. -/
theorem exists_succ_of_partialDeriv {k j : ℕ} (u : SobolevMultiIndex F b (k + 1) p Ω μ)
    (w₀ : SobolevMultiIndex F b (j + 1) q Ω μ) (hw₀ : fn w₀ =ᵐ[μ.restrict (Ω : Set E)] fn u)
    (w : ι → SobolevMultiIndex F b (j + 1) q Ω μ)
    (hw : ∀ i, fn (w i) =ᵐ[μ.restrict (Ω : Set E)] fn (partialDeriv F b p Ω μ i u)) :
    ∃ z : SobolevMultiIndex F b (j + 1 + 1) q Ω μ, fn z =ᵐ[μ.restrict (Ω : Set E)] fn u ∧
      ‖z‖ ≤ Fintype.card (MultiIndexLE ι (j + 1 + 1)) * (‖w₀‖ + ∑ i, ‖w i‖) := by
  classical
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have h0 : MemLp (fn u) q (μ.restrict (Ω : Set E)) := (memLp w₀).ae_eq hw₀
  have hB0 : 0 ≤ ‖w₀‖ + ∑ i, ‖w i‖ :=
    add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  -- the weak derivatives of `fn u` of order at most `j + 2`, with their `L^q` bounds
  have hder : ∀ β : MultiIndexLE ι (j + 1 + 1), ∃ g : E → F,
      HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) β.1) (fn u) g Ω μ ∧
        MemLp g q (μ.restrict (Ω : Set E)) ∧
        eLpNorm g q (μ.restrict (Ω : Set E)) ≤ ENNReal.ofReal (‖w₀‖ + ∑ i, ‖w i‖) := by
    intro β
    rcases eq_or_ne β 0 with rfl | hβ
    · refine ⟨fn u, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
        (h0.locallyIntegrableOn hq1), h0, ?_⟩
      rw [← eLpNorm_congr_ae hw₀]
      exact (eLpNorm_fn_le_ofReal_norm w₀).trans (ENNReal.ofReal_le_ofReal
        (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)))
    · obtain ⟨i, β', rfl⟩ := MultiIndexLE.exists_eq_addSingle β hβ
      refine ⟨weakDeriv (w i) β', ?_, Lp.memLp _, ?_⟩
      · have h1 := ((hasWeakIteratedLineDerivOn (w i) β').congr_ae (hw i)
          (Filter.EventuallyEq.refl _ _))
        have h2 := (hasWeakIteratedLineDerivOn_fn_partialDeriv i u).cons' h1
        exact h2.of_perm (multiIndexTuple_add_single_perm (b : ι → E) β'.1 i)
      · rw [← ENNReal.ofReal_toReal (Lp.memLp (weakDeriv (w i) β')).eLpNorm_ne_top,
          ← Lp.norm_def]
        refine ENNReal.ofReal_le_ofReal ((norm_weakDeriv_le (w i) β').trans ?_)
        have := Finset.single_le_sum (f := fun i ↦ ‖w i‖) (fun _ _ ↦ norm_nonneg _)
          (Finset.mem_univ i)
        linarith [norm_nonneg w₀]
  choose g hg hgq hgn using hder
  have hmem : MemSobolevMultiIndex b (fn u) (j + 1 + 1) q Ω μ :=
    ⟨h0, fun α hα ↦ ⟨g ⟨α, hα⟩, hg ⟨α, hα⟩, hgq ⟨α, hα⟩⟩⟩
  obtain ⟨z, hz⟩ := hmem.exists_sobolevMultiIndex
  refine ⟨z, hz, norm_le_card_mul_of_forall_norm_weakDeriv_le z fun β ↦ ?_⟩
  -- each component of `z` is the corresponding `g β`, by uniqueness of the weak derivative
  have hae : (weakDeriv z β : E → F) =ᵐ[μ.restrict (Ω : Set E)] g β :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2
      (((hasWeakIteratedLineDerivOn z β).congr_ae hz (Filter.EventuallyEq.refl _ _)).ae_eq (hg β))
  rw [Lp.norm_def, eLpNorm_congr_ae hae]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgn β)).trans_eq (ENNReal.toReal_ofReal hB0)

variable [Fact (1 ≤ p)]

/-- **A bounded operator at order one which preserves membership of `W^{k,p}` restricts to a
bounded operator at order `k`** (`1 ≤ k`): for `T : W^{1,p}(Ω) →L[ℝ] W^{1,p}(Ω')` such that
`fn (T u) ∈ W^{k,p}(Ω')` whenever `fn u ∈ W^{k,p}(Ω)`, there is
`T' : W^{k,p}(Ω) →L[ℝ] W^{k,p}(Ω')` with `fn (T' u) = fn (T u)`, the closed graph theorem
(`SobolevMultiIndex.continuous_of_fnL_comp_eq`) supplying the bound. -/
theorem exists_continuousLinearMap_of_order (hk : 1 ≤ k)
    (T : SobolevMultiIndex F b 1 p Ω μ →L[ℝ] SobolevMultiIndex F b 1 p Ω' μ)
    (hT : ∀ u : SobolevMultiIndex F b k p Ω μ,
      MemSobolevMultiIndex b (fn (T (toLowerOrderL F b p Ω μ hk u))) k p Ω' μ) :
    ∃ T' : SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k p Ω' μ,
      ∀ u, fn (T' u) =ᵐ[μ.restrict (Ω' : Set E)] fn (T (toLowerOrderL F b p Ω μ hk u)) := by
  choose T' hT' using fun u ↦ (hT u).exists_sobolevMultiIndex
  have hfn : ∀ u, fnL F b k p Ω' μ (T' u)
      = fnL F b 1 p Ω' μ (T (toLowerOrderL F b p Ω μ hk u)) := fun u ↦ by
    apply Lp.ext
    rw [fnL_apply, fnL_apply]
    exact hT' u
  have hadd : ∀ u v, T' (u + v) = T' u + T' v := fun u v ↦ by
    refine ext_of_fn_ae_eq ((hT' (u + v)).trans (EventuallyEq.trans ?_ (fn_add _ _).symm))
    rw [map_add, map_add]
    exact (fn_add _ _).trans ((hT' u).add (hT' v)).symm
  have hsmul : ∀ (c : ℝ) u, T' (c • u) = c • T' u := fun c u ↦ by
    refine ext_of_fn_ae_eq ((hT' (c • u)).trans (EventuallyEq.trans ?_ (fn_smul _ _).symm))
    rw [map_smul, map_smul]
    exact (fn_smul _ _).trans ((hT' u).const_smul c).symm
  obtain ⟨Tₗ, hTₗ⟩ : ∃ Tₗ : SobolevMultiIndex F b k p Ω μ →ₗ[ℝ] SobolevMultiIndex F b k p Ω' μ,
      ∀ u, Tₗ u = T' u := ⟨{ toFun := T', map_add' := hadd, map_smul' := hsmul }, fun _ ↦ rfl⟩
  have hcont : Continuous Tₗ := by
    refine continuous_of_fnL_comp_eq Tₗ
      (G := fun u ↦ fnL F b 1 p Ω' μ (T (toLowerOrderL F b p Ω μ hk u))) ?_ fun u ↦ ?_
    · exact (fnL F b 1 p Ω' μ).continuous.comp
        (T.continuous.comp (toLowerOrderL F b p Ω μ hk).continuous)
    · rw [hTₗ]; exact hfn u
  exact ⟨⟨Tₗ, hcont⟩, fun u ↦ by rw [ContinuousLinearMap.coe_mk', hTₗ]; exact hT' u⟩

end SobolevMultiIndex

end OrderLifting

/-! ### The partial derivatives of `W^{k,p}(Ω)` on `ℝ^N`

The weak partial derivatives `∂ᵢu = weakDeriv u (single i)` of `u ∈ W^{1,p}(Ω)`, `Ω ⊆ ℝ^N` open,
as weak derivatives of the function `fn u` along `e_i`; membership of `W^{1,p}(Ω)` from the `N`
partial derivatives and their uniqueness; the identification of `∂ᵢu` with the classical partial
derivative of a `C¹` representative, at orders one and `k + 1`; the pointwise gradient
`gradFn u` against `Du` for such a representative, `∫_Ω |u|^p = ‖fnL u‖^p` and
`∫_Ω ‖Du‖^p ≤ N^p ‖u‖^p`; and the restricted pointwise gradient `u ↦ ∇u|_S` as a bounded linear
map `W^{1,p}(Ω) → L^p(S; ℝ^N)` (`SobolevEuclidean.gradFnL`). -/

section EuclideanPartials

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

open SobolevMultiIndex

omit [Fact (1 ≤ p)] in
/-- The partial derivative `∂_j u` of `u ∈ W^{1,p}(Ω)` is a weak derivative of `fn u` along
`e_j`. -/
theorem SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single (u : SobolevEuclidean N 1 p Ω)
    (j : Fin N) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] (fn u)
      (weakDeriv u (MultiIndexLE.single j)) Ω volume := by
  have := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single j)).of_perm
    (multiIndexTuple_single_perm
      ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) j)
  rwa [EuclideanSpace.basisFun_toBasis_apply] at this

omit [Fact (1 ≤ p)] in
/-- A function of `W^{1,p}` (as `MemSobolevMultiIndex`, over the standard basis) has a weak
derivative along each `eⱼ` in `L^p`. -/
theorem MemSobolevMultiIndex.exists_hasWeakIteratedLineDerivOn_single
    {Ω' : Opens (EuclideanSpace ℝ (Fin N))} {f : EuclideanSpace ℝ (Fin N) → ℝ} {q : ℝ≥0∞}
    (h : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f 1 q Ω' volume)
    (i : Fin N) :
    ∃ w : EuclideanSpace ℝ (Fin N) → ℝ,
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single i (1 : ℝ)] f w Ω' volume ∧
        MemLp w q (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨w, hw, hwp⟩ := h.2 (Pi.single i 1) (by simp)
  refine ⟨w, ?_, hwp⟩
  have := hw.of_perm (multiIndexTuple_single_perm
    ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) i)
  rwa [EuclideanSpace.basisFun_toBasis_apply] at this

/-- **Membership of `W^{1,p}(Ω)` from the partial derivatives**: a function of `L^p(Ω)` with a
weak derivative in `L^p(Ω)` along each `e_j` lies in `W^{1,p}(Ω)`. -/
theorem SobolevEuclidean.memSobolevMultiIndex_one_of_forall {F : EuclideanSpace ℝ (Fin N) → ℝ}
    (hF : MemLp F p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    {G : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hG : ∀ j, MemLp (G j) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hFG : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] F (G j) Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis F 1 p Ω volume := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  refine ⟨hF, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (hF.locallyIntegrableOn hp), hF⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    refine ⟨G i, ?_, hG i⟩
    have h' : HasWeakIteratedLineDerivOn
        ![((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) i]
        F (G i) Ω volume := by
      rw [EuclideanSpace.basisFun_toBasis_apply]
      exact hFG i
    exact h'.of_perm (multiIndexTuple_single_perm
      ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) i).symm

omit [Fact (1 ≤ p)] in
/-- **Uniqueness of the partial derivatives**: if `fn u` is almost everywhere `F` on `Ω` and
`G` is a weak derivative of `F` along `e_j` on `Ω`, then `∂_j u` is almost everywhere `G`. -/
theorem SobolevEuclidean.weakDeriv_single_ae_eq (u : SobolevEuclidean N 1 p Ω)
    {F G : EuclideanSpace ℝ (Fin N) → ℝ}
    (hF : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] F) {j : Fin N}
    (hG : HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] F G Ω volume) :
    weakDeriv u (MultiIndexLE.single j) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      G :=
  (ae_restrict_iff' Ω.isOpen.measurableSet).2
    (((SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single u j).congr_ae hF
      (EventuallyEq.refl _ _)).ae_eq hG)

omit [Fact (1 ≤ p)] in
/-- The partial derivatives of an element `U` of `W^{1,p}(Ω)` whose function is a `C¹` function
`u` are the classical ones, almost everywhere on `Ω` (at every `p`; the `H¹` case is
`Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn` of
`Numlib/Analysis/PDE/Elliptic/Dirichlet.lean`). -/
theorem SobolevEuclidean.weakDeriv_single_ae_eq_fderiv (U : SobolevEuclidean N 1 p Ω)
    {u : EuclideanSpace ℝ (Fin N) → ℝ} (hu : ContDiff ℝ 1 u)
    (hU : fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) (i : Fin N) :
    (weakDeriv U (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :=
  SobolevEuclidean.weakDeriv_single_ae_eq U hU (hu.contDiffOn.hasWeakIteratedLineDerivOn_single Ω i)

omit [Fact (1 ≤ p)] in
/-- The first-order weak derivative of `v ∈ W^{k+1,p}(Ω)` with a `C¹` representative `v'` is the
classical `∂ᵢ v'`, almost everywhere on `Ω` — the higher-order form of
`SobolevEuclidean.weakDeriv_single_ae_eq_fderiv`, the multi-index `e_i` of `W^{k+1,p}` being
`MultiIndexLE.singleLE i`. -/
theorem SobolevEuclidean.weakDeriv_singleLE_ae_eq_fderiv {k : ℕ}
    (v : SobolevEuclidean N (k + 1) p Ω) {v' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v')
    (hv' : ContDiff ℝ 1 v') (i : Fin N) :
    (weakDeriv v (MultiIndexLE.singleLE i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ v' x (EuclideanSpace.single i 1) := by
  have h1 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i (1 : ℝ)] (fn v)
      (weakDeriv v (MultiIndexLE.singleLE i)) Ω volume := by
    have := (hasWeakIteratedLineDerivOn v (MultiIndexLE.singleLE i)).of_perm
      (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
        Fin N → EuclideanSpace ℝ (Fin N)) i)
    rwa [EuclideanSpace.basisFun_toBasis_apply] at this
  have h2 := hv'.contDiffOn.hasWeakIteratedLineDerivOn_single Ω i
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2
    ((h1.congr_ae hv (EventuallyEq.refl _ _)).ae_eq h2)

omit [Fact (1 ≤ p)] in
/-- The pointwise gradient of an element of `W^{1,p}(Ω)` with a `C¹` function `u` has the norm
of `Du`, almost everywhere on `Ω`. -/
theorem SobolevEuclidean.norm_fderiv_ae_eq_norm_gradFn (U : SobolevEuclidean N 1 p Ω)
    {u : EuclideanSpace ℝ (Fin N) → ℝ} (hu : ContDiff ℝ 1 u)
    (hU : fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) :
    (fun x ↦ ‖fderiv ℝ u x‖) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ ‖gradFn U x‖ := by
  have h := ae_all_iff.2 fun i : Fin N ↦ SobolevEuclidean.weakDeriv_single_ae_eq_fderiv U hu hU i
  filter_upwards [h] with x hx
  rw [EuclideanSpace.norm_fderiv_eq]
  congr 1
  ext i
  rw [PiLp.toLp_apply, gradFn_apply, hx i]

/-- `∫_Ω |u|^p = ‖fnL U‖^p` for a representative `u` of `U ∈ W^{1,p}(Ω)`. -/
theorem SobolevEuclidean.integral_abs_rpow_eq_norm_fnL (hp : p ≠ ⊤) (U : SobolevEuclidean N 1 p Ω)
    {u : 𝔼 → ℝ} (hU : fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u) :
    ∫ x in (Ω : Set 𝔼), |u x| ^ p.toReal
      = ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume U‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  rw [Lp.norm_rpow_eq_integral hp0 hp, fnL_apply]
  refine integral_congr_ae (hU.mono fun x hx ↦ ?_)
  simp only [hx, Real.norm_eq_abs]

/-- `∫_Ω ‖Du‖^p ≤ N^p ‖U‖^p` for a `C¹` representative `u` of `U ∈ W^{1,p}(Ω)`. -/
theorem SobolevEuclidean.integral_norm_fderiv_rpow_le (hp : p ≠ ⊤) (U : SobolevEuclidean N 1 p Ω)
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u) (hU : fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u) :
    ∫ x in (Ω : Set 𝔼), ‖fderiv ℝ u x‖ ^ p.toReal ≤ (N : ℝ) ^ p.toReal * ‖U‖ ^ p.toReal := by
  have h := integral_norm_gradFn_rpow_le hp U
  rw [Fintype.card_fin] at h
  calc ∫ x in (Ω : Set 𝔼), ‖fderiv ℝ u x‖ ^ p.toReal
      = ∫ x in (Ω : Set 𝔼), ‖gradFn U x‖ ^ p.toReal :=
        integral_congr_ae ((SobolevEuclidean.norm_fderiv_ae_eq_norm_gradFn U hu hU).mono
          fun x hx ↦ by simp only at hx ⊢; rw [hx])
    _ ≤ (N : ℝ) ^ p.toReal * gradNorm U ^ p.toReal := h
    _ ≤ (N : ℝ) ^ p.toReal * ‖U‖ ^ p.toReal :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (gradNorm_nonneg U) (gradNorm_le_norm U)
          ENNReal.toReal_nonneg) (by positivity)

/-- The gradient norm is continuous on `W^{1,p}(Ω)`. -/
theorem SobolevEuclidean.continuous_gradNorm :
    Continuous fun u : SobolevEuclidean N 1 p Ω ↦ gradNorm u := by
  refine continuous_norm.comp ((PiLp.continuous_toLp p _).comp (continuous_pi fun i ↦ ?_))
  exact (weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
    (MultiIndexLE.single i)).continuous

/-- `‖∇u‖_{L^p(Ω)} ≤ N ‖∇u‖` for the Euclidean pointwise gradient (`gradFn`) and the `ℓ^p`
gradient norm (`gradNorm`). -/
theorem SobolevEuclidean.toReal_eLpNorm_gradFn_le (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p Ω) :
    (eLpNorm (gradFn u) p (volume.restrict (Ω : Set 𝔼))).toReal ≤ N * gradNorm u := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hP0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h := integral_norm_gradFn_rpow_le hp u
  rw [Fintype.card_fin] at h
  rw [(memLp_gradFn u).eLpNorm_eq_integral_rpow_norm hp0 hp,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x ↦ by positivity) _)]
  calc (∫ x in (Ω : Set 𝔼), ‖gradFn u x‖ ^ p.toReal) ^ p.toReal⁻¹
      ≤ ((N : ℝ) ^ p.toReal * gradNorm u ^ p.toReal) ^ p.toReal⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x ↦ by positivity) h (by positivity)
    _ = N * gradNorm u := by
        rw [← Real.mul_rpow (by positivity) (gradNorm_nonneg u), ← Real.rpow_mul
          (mul_nonneg N.cast_nonneg (gradNorm_nonneg u)), mul_inv_cancel₀ hP0.ne', Real.rpow_one]

variable (p Ω) in
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

end EuclideanPartials
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
