/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, beside the embeddings of
`Numlib/Analysis/Sobolev/EmbeddingDomain.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.EmbeddingDomain
import Numlib.Analysis.Sobolev.Extension
import Numlib.MeasureTheory.Function.LpSpace.KolmogorovRiesz
import Numlib.Topology.ContinuousMap.ArzelaAscoli

/-!
# The Rellich–Kondrachov theorem

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Theorem 9.16:
for a bounded open `Ω ⊆ ℝ^N` of class `C¹`, the injections `W^{1,p}(Ω) ⊂ L^q(Ω)` for
`q ∈ [1, p*)` when `p < N`, for `q ∈ [p, ∞)` when `p = N`, and `W^{1,p}(Ω) ⊂ C(Ω̄)` when `p > N`
are compact; in particular `W^{1,p}(Ω) ⊂ L^p(Ω)` is compact. Compact embeddings are
`IsCompactEmbedding` of `Numlib/Analysis/Normed/Operator/Embedding.lean`, along the inclusions
`SobolevMultiIndex.toLpₗ` / `SobolevMultiIndex.toLpₗOn` and the trace map
`SobolevEuclidean.toContinuousMapL` of `Numlib/Analysis/Sobolev/EmbeddingDomain.lean`.

## The proof

The case `p < N` is factored through an abstract lemma on a subspace `S` of `W^{1,p}(Ω)` with an
extension operator (`HasSobolevExtensionOn S`) and `volume Ω < ∞`
(`SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn`): the image `ℱ = P(ℋ)` of
the unit ball is bounded in `W^{1,p}(ℝ^N)`, hence in `L^q(ℝ^N)` by Corollary 9.10
(`HasSobolevExtensionOn.isBounded_image_closedBall`), and uniformly continuous under translation
in `L^q` by Proposition 9.3 in `L^p` interpolated with the `L^{p*}` bound
(`SobolevEuclidean.exists_forall_eLpNorm_fn_sub_translate_le`,
`HasSobolevExtensionOn.uniform_translate_image_closedBall`); the Kolmogorov–M. Riesz–Fréchet
theorem (`MeasureTheory.Lp.isCompact_closure_image_restrictCLM_of_uniform_translate`,
`Numlib/MeasureTheory/Function/LpSpace/KolmogorovRiesz.lean`) makes the restrictions to `Ω`
relatively compact, and `ℋ = ℱ|_Ω` (`HasSobolevExtensionOn.toLpₗOn_eq_restrictCLM`). For `q < p`
the case `q = p` is composed with the continuous inclusion `L^p(Ω) ⊆ L^q(Ω)`
(`MeasureTheory.Lp.monoExponentL`). The instances are `S = ⊤` with Theorem 9.7's operator
(`SobolevEuclidean.isCompactEmbedding_toLp_of_lt`) and, once `Zero.lean` provides it,
`S = W_0^{1,p}(Ω)` with the extension by zero (Remark 20).

The cases `p ≥ N` for `N ≥ 2` reduce to `p < N`: `W^{1,p}(Ω) ↪ W^{1,r}(Ω)` continuously on the
finite-measure `Ω` for an `r < N` with `r* > q` (`SobolevMultiIndex.toLowerExponentL`,
`NNReal.exists_lowerExponent`), and `W^{1,r}(Ω) ↪↪ L^q(Ω)`
(`SobolevEuclidean.isCompactEmbedding_toLp_of_le`, `…_of_eq`). The case `p > N` into `C(K)` for
a compact `K ⊇ Ω` is Arzelà–Ascoli (`ContinuousMap.isCompact_closure_of_forall_norm_le`) on the
uniformly bounded and uniformly Hölder image of the unit ball
(`HasSobolevExtensionOn.isCompactEmbedding_toContinuousMapOnL`,
`SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt`). The injection `W^{1,p}(Ω) ⊂ L^p(Ω)`
(`SobolevEuclidean.isCompactEmbedding_toLp_self`, `SobolevEuclidean.isCompactEmbedding_fnL`) is
covered for `1 ≤ p < ∞` whenever `p < N` or `N ≥ 2`; the case `N = 1 ≤ p` (an interval) and the
case `p = ∞` are not proved here.

## References

[brezis2011functional], Theorem 9.16 and its proof, Remark 20; Atkinson–Han, *Theoretical
Numerical Analysis*, Theorem 7.3.8.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

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

/-! ### The abstract Rellich–Kondrachov lemma -/

section Rellich

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- **The uniform translation modulus in `L^q` of a bounded set of `W^{1,p}(ℝ^N)`**, `p ≤ q < p*`:
for `v ∈ W^{1,p}(ℝ^N)` with `‖v‖ ≤ M`, `‖τ_h v − v‖_q ≤ ‖h‖^θ K` with `θ ∈ (0, 1]` the
interpolation parameter of `q` between `p` and `p*` and `K` depending only on `M`, `p`, `q`,
`N` — the estimate of [brezis2011functional] §9.3, proof of Theorem 9.16: Proposition 9.3 in
`L^p`, `‖τ_h v − v‖_{p*} ≤ 2 ‖v‖_{p*}` and Corollary 9.10 in `L^{p*}`, and the interpolation
inequality between the two. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_sub_translate_le {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q < p') (M : ℝ) :
    ∃ (θ : ℝ) (K : ℝ≥0∞), 0 < θ ∧ K ≠ ⊤ ∧ ∀ v : SobolevEuclidean N 1 p ⊤, ‖v‖ ≤ M →
      ∀ h : EuclideanSpace ℝ (Fin N),
        eLpNorm (fun x ↦ fn v (x + h) - fn v x) q volume ≤ ‖h‖ₑ ^ θ * K := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_inv_eq_ofReal_mul_inv_add (r := (q : ℝ≥0∞))
    (q := (p' : ℝ≥0∞)) hp0 (by exact_mod_cast hpq) (by exact_mod_cast hqp'.le)
  have hθpos : 0 < θ := by
    rcases hθ0.eq_or_lt with rfl | h
    · exfalso
      simp only [ENNReal.ofReal_zero, zero_mul, sub_zero, ENNReal.ofReal_one, one_mul,
        zero_add] at hθ
      exact hqp'.ne (by exact_mod_cast inv_inj.1 hθ)
    · exact h
  set A : ℝ≥0∞ := N * ENNReal.ofReal M with hA
  set B : ℝ≥0∞ := 2 * ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N * M) with hB
  have hAt : A ≠ ⊤ := by
    rw [hA]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hBt : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  refine ⟨θ, A ^ θ * B ^ (1 - θ), hθpos,
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ0 hAt)
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hBt), fun v hv h ↦ ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg v).trans hv
  have hg : AEStronglyMeasurable (fn v) volume := (SobolevEuclidean.memLp_fn v).aestronglyMeasurable
  have hgh : AEStronglyMeasurable (fun x ↦ fn v (x + h)) volume :=
    hg.comp_quasiMeasurePreserving (measurePreserving_add_right volume h).quasiMeasurePreserving
  -- the `L^p` translation estimate
  have h1 : eLpNorm (fun x ↦ fn v (x + h) - fn v x) p volume ≤ ‖h‖ₑ * A := by
    refine (SobolevEuclidean.eLpNorm_fn_sub_translate_le ENNReal.coe_ne_top v h).trans ?_
    refine mul_le_mul' le_rfl ((SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le v).trans ?_)
    rw [hA]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hv)
  -- the `L^{p*}` bound
  have h2 : eLpNorm (fun x ↦ fn v (x + h) - fn v x) p' volume ≤ B := by
    have hsub : (fun x ↦ fn v (x + h) - fn v x) = (fun x ↦ fn v (x + h)) - fn v := by
      funext x
      simp
    rw [hsub]
    refine (eLpNorm_sub_le (hp1.trans (by exact_mod_cast hpq.trans hqp'.le))).trans ?_
    rw [eLpNorm_comp_add_right hg h, ← two_mul, hB]
    refine mul_le_mul' le_rfl ((SobolevEuclidean.eLpNorm_fn_le_norm_of_eq hpN hp' v).trans ?_)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hv (by positivity))
  -- interpolation
  calc eLpNorm (fun x ↦ fn v (x + h) - fn v x) q volume
      ≤ eLpNorm (fun x ↦ fn v (x + h) - fn v x) p volume ^ θ
        * eLpNorm (fun x ↦ fn v (x + h) - fn v x) p' volume ^ (1 - θ) :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (hgh.sub hg) hθ0 hθ1 hθ
    _ ≤ (‖h‖ₑ * A) ^ θ * B ^ (1 - θ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow h1 hθ0) (ENNReal.rpow_le_rpow h2 (by linarith))
    _ = ‖h‖ₑ ^ θ * (A ^ θ * B ^ (1 - θ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0, mul_assoc]

/-- For `θ > 0` and `K < ∞`, `‖h‖^θ K` is small for small `‖h‖`. -/
theorem EuclideanSpace.exists_pos_forall_enorm_rpow_mul_lt {θ : ℝ} (hθ : 0 < θ) {K : ℝ≥0∞}
    (hK : K ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ < δ → ‖h‖ₑ ^ θ * K < ε := by
  have hlim : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ ^ θ * K) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ ^ θ) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ) (𝓝 0) (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))
      have := ((ENNReal.continuous_rpow_const (y := θ)).tendsto (0 : ℝ≥0∞)).comp h0
      rw [ENNReal.zero_rpow_of_pos hθ] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hK)
  obtain ⟨δ, hδ, hδ0⟩ := ((hlim.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ0, fun h hh ↦ lt_of_le_of_lt ?_ hδ⟩
  rw [← ofReal_norm]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hh.le) hθ.le) le_rfl

/-- The extension of the unit ball of `S` to `W^{1,p}(ℝ^N)`, read in `L^q(ℝ^N)`: the family `ℱ` of
[brezis2011functional] §9.3, proof of Theorem 9.16. -/
theorem HasSobolevExtensionOn.toLpₗOn_eq_restrictCLM [Fact (1 ≤ (q : ℝ≥0∞))]
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤)
    (hP : ∀ u : S, fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fn (u : SobolevEuclidean N 1 p Ω))
    (h : ∀ u : S, MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hmem : ∀ u : S, MemLp (fn (P u)) q volume) (u : S) :
    toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S h u
      = Lp.restrictCLM ℝ ℝ q volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ((hmem u).toLp _) := by
  refine Lp.ext ((toLpₗOn_coeFn h u).trans ?_)
  have e1 : fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      (hmem u).toLp (fn (P u)) :=
    Filter.EventuallyEq.symm (ae_restrict_of_ae (MemLp.coeFn_toLp (hmem u)))
  exact ((hP u).symm.trans e1).trans (Lp.coeFn_restrictCLM _ _).symm

/-- The family `ℱ = P(unit ball)` is bounded in `L^q(ℝ^N)`, `p ≤ q ≤ p*`
([brezis2011functional] §9.3, proof of Theorem 9.16, by Corollary 9.10). -/
theorem HasSobolevExtensionOn.isBounded_image_closedBall [Fact (1 ≤ (q : ℝ≥0∞))]
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    Bornology.IsBounded ((fun u : S ↦
      (SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp' (P u)).toLp _) ''
        closedBall (0 : S) 1) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨(1 + SobolevEuclidean.gnsConst N p * N) * ‖P‖, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hPu : ‖P u‖ ≤ ‖P‖ := by
    calc ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖P‖ := mul_one _
  have hC0 : (0 : ℝ) ≤ 1 + SobolevEuclidean.gnsConst N p * N :=
    add_nonneg zero_le_one (mul_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg _))
  have hb := SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' (P u)
  rw [mem_closedBall_zero_iff, Lp.norm_toLp]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg hC0 (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left hPu hC0

/-- The family `ℱ = P(unit ball)` has a uniform translation modulus in `L^q(ℝ^N)`,
`p ≤ q < p*` — the hypothesis of the Kolmogorov–M. Riesz–Fréchet theorem in
[brezis2011functional] §9.3, proof of Theorem 9.16. -/
theorem HasSobolevExtensionOn.uniform_translate_image_closedBall [Fact (1 ≤ (q : ℝ≥0∞))]
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q < p') :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ (fun u : S ↦
      (SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _) ''
        closedBall (0 : S) 1, ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ < δ →
          eLpNorm (fun x ↦ f (x + h) - f x) q volume < ε := by
  obtain ⟨θ, K, hθ, hK, hmod⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_sub_translate_le (q := q) hpN hp' hpq hqp' ‖P‖
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := EuclideanSpace.exists_pos_forall_enorm_rpow_mul_lt (N := N) hθ hK hε
  refine ⟨δ, hδ0, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ h hh
  have hPu : ‖P u‖ ≤ ‖P‖ := by
    calc ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖P‖ := mul_one _
  have hGae := MemLp.coeFn_toLp (SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u))
  have hae : (fun x ↦ ((SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _)
        (x + h) - ((SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _) x)
      =ᵐ[volume] fun x ↦ fn (P u) (x + h) - fn (P u) x := by
    have h1 := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hGae
    filter_upwards [h1, hGae] with x hx1 hx2
    simp only [Function.comp_apply] at hx1
    rw [hx1, hx2]
  rw [eLpNorm_congr_ae hae]
  exact (hmod (P u) hPu h).trans_lt (hδ h hh)

/-- **The abstract Rellich–Kondrachov lemma, the case `p ≤ q < p*`**: for a subspace `S` of
`W^{1,p}(Ω)` with an extension operator (`HasSobolevExtensionOn S`), `volume Ω < ∞`,
`1 ≤ p < N`, `1/p* = 1/p − 1/N` and `p ≤ q < p*`, the inclusion `S → L^q(Ω)` is a compact
embedding. The image of the unit ball is `F|_Ω` where `F = P(unit ball) ⊆ W^{1,p}(ℝ^N)` is bounded
in `L^q(ℝ^N)` (Corollary 9.10) with a uniform translation modulus in `L^q`
(`SobolevEuclidean.exists_forall_eLpNorm_fn_sub_translate_le`), so the Kolmogorov–M. Riesz–Fréchet
theorem `MeasureTheory.Lp.isCompact_closure_image_restrictCLM_of_uniform_translate` makes its
restriction to `Ω` relatively compact. [brezis2011functional] Theorem 9.16, the case `p < N`. -/
theorem HasSobolevExtensionOn.isCompactEmbedding_toLpOn_of_le_of_lt [Fact (1 ≤ (q : ℝ≥0∞))]
    (hS : HasSobolevExtensionOn S) (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q < p') :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le)) := by
  obtain ⟨P, hP⟩ := id hS
  have hcont := hS.isContinuousEmbedding_toLpOn_of_le_of_le hpN hp' hpq hqp'.le
  obtain ⟨ι, hι⟩ : ∃ ι : S →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ι = hcont.toContinuousLinearMap := ⟨_, rfl⟩
  have hιapply : ∀ u : S, ι u = Lp.restrictCLM ℝ ℝ q volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
      ((SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _) := by
    intro u
    rw [hι, IsContinuousEmbedding.coe_toContinuousLinearMap]
    exact HasSobolevExtensionOn.toLpₗOn_eq_restrictCLM P hP _
      (fun u ↦ SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)) u
  have himg : ⇑ι '' closedBall 0 1 = Lp.restrictCLM ℝ ℝ q volume
      (Ω : Set (EuclideanSpace ℝ (Fin N))) '' ((fun u : S ↦
        (SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp'.le (P u)).toLp _) ''
          closedBall (0 : S) 1) := by
    rw [Set.image_image]
    exact Set.image_congr fun u _ ↦ hιapply u
  have hK' : IsCompact (closure (⇑ι '' closedBall 0 1)) := by
    rw [himg]
    exact Lp.isCompact_closure_image_restrictCLM_of_uniform_translate ENNReal.coe_ne_top
      (HasSobolevExtensionOn.isBounded_image_closedBall P hpN hp' hpq hqp'.le)
      (HasSobolevExtensionOn.uniform_translate_image_closedBall P hpN hp' hpq hqp') hΩ
  have := isCompactEmbedding_of_isCompact_closure_image_closedBall (hι ▸ hcont.injective) hK'
  rw [hι] at this
  exact this

end Rellich

/-! ### Theorem 9.16, case `p < N`, for `1 ≤ q < p*` -/

section RellichLt

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- On a set of finite measure, `fn u ∈ L^q(Ω)` for `u ∈ S` and every `q ≤ p*`, `p < N`:
`L^p(Ω) ⊆ L^q(Ω)` for `q ≤ p`, Corollary 9.14 for `p ≤ q ≤ p*`. -/
theorem HasSobolevExtensionOn.memLp_fn_of_le_sobolevConj (hS : HasSobolevExtensionOn S)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q ≤ p') (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  rcases le_or_gt p q with hpq | hqp
  · exact hS.memLp_fn_of_le_of_le hpN hp' hpq hqp' u
  · have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      isFiniteMeasure_restrict.2 hΩ
    exact (SobolevMultiIndex.memLp (u : SobolevEuclidean N 1 p Ω)).mono_exponent
      (by exact_mod_cast hqp.le)

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- The Sobolev conjugate exponent exceeds `p`: `p < p*` for `p < N`. -/
theorem NNReal.lt_sobolevConj {p' : ℝ≥0} (hp0 : 0 < p) (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) : p < p' := by
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (NNReal.coe_nonneg p) (by exact_mod_cast hpN)
  have hp'0 : (0 : ℝ) < (p' : ℝ)⁻¹ := by
    rw [hp', sub_pos]
    exact inv_strictAnti₀ (by exact_mod_cast hp0) (by exact_mod_cast hpN)
  have h : (p' : ℝ)⁻¹ < (p : ℝ)⁻¹ := by
    rw [hp']
    exact sub_lt_self _ (by positivity)
  have := (inv_lt_inv₀ (inv_pos.1 hp'0) (by exact_mod_cast hp0)).1 h
  exact_mod_cast this

/-- **The abstract Rellich–Kondrachov lemma** ([brezis2011functional] Theorem 9.16, the case
`p < N`, in the generality of its proof): for a subspace `S` of `W^{1,p}(Ω)` with an extension
operator (`HasSobolevExtensionOn S`), `volume Ω < ∞`, `1 ≤ p < N`, `1/p* = 1/p − 1/N` and
`1 ≤ q < p*`, the inclusion `S → L^q(Ω)` (along `SobolevMultiIndex.toLpₗOn`) is a compact
embedding. For `q < p` it is the case `q = p` followed by the continuous inclusion
`L^p(Ω) ⊆ L^q(Ω)` ("since `Ω` is bounded, we may always assume that `q ≥ p`"). -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn [Fact (1 ≤ (q : ℝ≥0∞))]
    (hS : HasSobolevExtensionOn S) (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q < p') :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_of_le_sobolevConj hΩ hpN hp' hqp'.le)) := by
  rcases le_or_gt p q with hpq | hqp
  · exact hS.isCompactEmbedding_toLpOn_of_le_of_lt hΩ hpN hp' hpq hqp'
  · have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      isFiniteMeasure_restrict.2 hΩ
    have hp0 : 0 < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
    have hc := hS.isCompactEmbedding_toLpOn_of_le_of_lt hΩ hpN hp' le_rfl
      (NNReal.lt_sobolevConj hp0 hpN hp')
    have hqp' : (q : ℝ≥0∞) ≤ p := by exact_mod_cast hqp.le
    have hmono := Lp.isContinuousEmbedding_monoExponentL (G := ℝ)
      (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) hqp'
    have hcomp := hc.comp_isContinuousEmbedding hmono
    convert hcomp using 1
    refine LinearMap.ext fun u ↦ Lp.ext ?_
    refine (toLpₗOn_coeFn _ u).trans ?_
    refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_monoExponentL hqp' _).symm
    exact (toLpₗOn_coeFn _ u).symm

end RellichLt

/-! ### Theorem 9.16 on the whole space `W^{1,p}(Ω)` of a bounded `C¹` domain -/

section RellichTop

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The inclusion of `W^{k,p}(Ω)` into `L^q(Ω)` is the inclusion of the subspace `⊤` composed
with the identification `W^{k,p}(Ω) ≃ ⊤`; hence compactness of the latter gives compactness of
the former. -/
theorem SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Ω : Opens E} {μ : Measure E}
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E)))
    (hc : IsCompactEmbedding (toLpₗOn F b k p Ω μ ⊤ fun u ↦ h u)) :
    IsCompactEmbedding (toLpₗ F b k p Ω μ h) := by
  have hι : IsContinuousEmbedding ((LinearMap.id (R := ℝ)).codRestrict
      (⊤ : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)) fun _ ↦ Submodule.mem_top) :=
    ⟨fun u v huv ↦ by simpa using congrArg Subtype.val huv, 1, fun u ↦ by simp⟩
  have := hι.comp_isCompactEmbedding hc
  convert this using 1
  exact LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn h u).trans
    (toLpₗOn_coeFn (S := ⊤) (fun u ↦ h u) ⟨u, Submodule.mem_top⟩).symm)

/-- **Theorem 9.16 (Rellich–Kondrachov), the case `p < N`**: for a bounded open set `Ω ⊆ ℝ^N` of
class `C¹` (by charts), `1 ≤ p < N`, `1/p* = 1/p − 1/N` and `1 ≤ q < p*`, the injection
`W^{1,p}(Ω) ⊂ L^q(Ω)` is compact. The abstract lemma with `S = ⊤` and the extension operator of
Theorem 9.7 (`IsSobolevExtensionDomain.of_isContDiffChartDomain`; a bounded `Ω` has bounded
frontier and finite measure). [brezis2011functional] Theorem 9.16. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_lt {d : ℕ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) {p' : ℝ≥0}
    (hpN : p < ((d + 1 : ℕ) : ℝ≥0)) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹)
    (hqp' : q < p') :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      fun u ↦ (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
        (hb.closure.subset frontier_subset_closure)).memLp_fn_of_le_sobolevConj
          hb.measure_lt_top.ne hpN hp' hqp'.le ⟨u, Submodule.mem_top⟩) :=
  SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top _
    (SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn
      (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
        (hb.closure.subset frontier_subset_closure)) hb.measure_lt_top.ne hpN hp' hqp')

end RellichTop

/-! ### Theorem 9.16, case `p > N`: Arzelà–Ascoli -/

section RellichGt

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- **The abstract Rellich–Kondrachov lemma, case `p > N`**: for a subspace `S` of `W^{1,p}(Ω)`
with an extension operator, `N < p < ∞`, and a compact `K ⊇ Ω`, the trace map
`S → C(K, ℝ)` of `HasSobolevExtensionOn.toContinuousMapOnL` is a compact embedding: the image of
the unit ball is bounded in sup norm and uniformly Hölder, hence equicontinuous, and `K` is
compact, so the Arzelà–Ascoli theorem `ContinuousMap.isCompact_closure_of_forall_norm_le`
applies. [brezis2011functional] Theorem 9.16, the case `p > N`. -/
theorem HasSobolevExtensionOn.isCompactEmbedding_toContinuousMapOnL (hS : HasSobolevExtensionOn S)
    (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    IsCompactEmbedding (hS.toContinuousMapOnL hp K).toLinearMap := by
  refine isCompactEmbedding_of_isCompact_closure_image_closedBall
    (hS.toContinuousMapOnL_injective hp hK) ?_
  obtain ⟨C₁, hC₁0, hC₁⟩ := hS.exists_forall_norm_toContinuousMapOnL_le hp K
  obtain ⟨C₂, hC₂0, hC₂⟩ := hS.exists_forall_norm_toContinuousMapOnL_sub_le hp K
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hα : (0 : ℝ) < 1 - N / (p : ℝ) := sub_pos.2 ((div_lt_one hp0).2 hp)
  refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := C₁) ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩ x
    refine (ContinuousMap.norm_coe_le_norm _ x).trans ((hC₁ u).trans ?_)
    calc C₁ * ‖u‖ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) hC₁0
      _ = C₁ := mul_one _
  · refine Metric.equicontinuous_of_continuity_modulus (fun d ↦ C₂ * d ^ (1 - N / (p : ℝ))) ?_ _ ?_
    · have h1 : Tendsto (fun d : ℝ ↦ d ^ (1 - N / (p : ℝ))) (𝓝 0) (𝓝 0) := by
        have := (Real.continuous_rpow_const hα.le).tendsto 0
        rwa [Real.zero_rpow hα.ne'] at this
      simpa using h1.const_mul C₂
    · rintro x y ⟨_, ⟨u, hu, rfl⟩⟩
      simp only [dist_eq_norm, Subtype.dist_eq]
      refine (hC₂ u x y).trans ?_
      rw [← dist_eq_norm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _)
      calc C₂ * ‖u‖ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) hC₂0
        _ = C₂ := mul_one _

/-- **Theorem 9.16 (Rellich–Kondrachov), the case `p > N`**: for a bounded open `Ω ⊆ ℝ^N` of
class `C¹` (by charts), `N < p < ∞` and a compact `K ⊇ Ω` (such as `closure Ω`), the injection
`W^{1,p}(Ω) ⊂ C(K)` along `SobolevEuclidean.toContinuousMapL` is compact.
[brezis2011functional] Theorem 9.16, "`W^{1,p}(Ω) ⊂ C(Ω̄)` if `p > N`". -/
theorem SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ K) :
    IsCompactEmbedding (SobolevEuclidean.toContinuousMapL
      (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
        (hb.closure.subset frontier_subset_closure)) hp K).toLinearMap := by
  have hc := (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
    (hb.closure.subset frontier_subset_closure)).isCompactEmbedding_toContinuousMapOnL hp hK
  have hι : IsContinuousEmbedding ((LinearMap.id (R := ℝ)).codRestrict
      (⊤ : Submodule ℝ (SobolevEuclidean (d + 1) 1 p Ω)) fun _ ↦ Submodule.mem_top) :=
    ⟨fun u v huv ↦ by simpa using congrArg Subtype.val huv, 1, fun u ↦ by simp⟩
  exact hι.comp_isCompactEmbedding hc

end RellichGt

/-! ### Theorem 9.16, the cases `p ≥ N` by lowering the exponent -/

section RellichGe

open SobolevMultiIndex

/-- The auxiliary exponent `r` of the reduction of the case `p ≥ N` to `p < N`: for `N ≥ 2` and
`q ≥ N`, the exponent `1/r = 1/N + 1/(2q)` satisfies `1 ≤ r < N` and `q < r* = 2q`
([brezis2011functional] Theorem 9.16, proof: "the case `p = N` reduces to the case `p < N`"). -/
theorem NNReal.exists_lowerExponent {N : ℕ} (hN : 2 ≤ N) {q : ℝ≥0} (hq : (N : ℝ≥0) ≤ q) :
    ∃ r : ℝ≥0, 1 ≤ r ∧ r < N ∧ ((2 * q : ℝ≥0) : ℝ)⁻¹ = (r : ℝ)⁻¹ - (N : ℝ)⁻¹ ∧ q < 2 * q := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (zero_lt_two.trans_le hN)
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le hN0 (by exact_mod_cast hq)
  have hq0' : (0 : ℝ≥0) < q := by exact_mod_cast hq0
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (N : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : (0 : ℝ≥0) < (N : ℝ≥0)⁻¹ + (2 * q)⁻¹ := by positivity
  refine ⟨((N : ℝ≥0)⁻¹ + (2 * q)⁻¹)⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [one_le_inv₀ hpos]
    have h1 : (N : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hNr
    have h2 : (2 * q : ℝ)⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    have : (((N : ℝ≥0)⁻¹ + (2 * q)⁻¹ : ℝ≥0) : ℝ) ≤ 1 := by
      push_cast
      linarith
    exact_mod_cast this
  · rw [inv_lt_comm₀ hpos (by exact_mod_cast hN0)]
    exact lt_add_of_pos_right _ (by positivity)
  · push_cast
    rw [inv_inv]
    ring
  · exact lt_mul_left hq0' one_lt_two

/-- **Theorem 9.16 (Rellich–Kondrachov), the cases `p ≥ N` with `N ≥ 2`**: for a bounded open
`Ω ⊆ ℝ^N` of class `C¹` (by charts), `N ≥ 2`, `N ≤ p < ∞` and `1 ≤ q < ∞`, the injection
`W^{1,p}(Ω) ⊂ L^q(Ω)` is compact: `W^{1,p}(Ω) ↪ W^{1,r}(Ω)` continuously for an `r < N` with
`r* > q`, and `W^{1,r}(Ω) ↪↪ L^q(Ω)` by the case `p < N`. This covers the book's case `p = N`
(`q ∈ [N, ∞)`) and, for `p > N`, the injection into `L^p(Ω)` of the last sentence of the theorem.
[brezis2011functional] Theorem 9.16, "the case `p = N` reduces to the case `p < N`". -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_le {d : ℕ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hd : 1 ≤ d)
    (hp : ((d + 1 : ℕ) : ℝ≥0) ≤ p)
    (h : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsCompactEmbedding
      (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume h) := by
  have hN : 2 ≤ d + 1 := by omega
  obtain ⟨r, hr1, hrN, hr', hq2⟩ := NNReal.exists_lowerExponent (N := d + 1) hN
    (q := max q ((d + 1 : ℕ) : ℝ≥0)) (le_max_right _ _)
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  have hqr : q < 2 * max q ((d + 1 : ℕ) : ℝ≥0) := lt_of_le_of_lt (le_max_left _ _) hq2
  have hc := SobolevEuclidean.isCompactEmbedding_toLp_of_lt (p := r) (q := q) hΩ hb hrN hr' hqr
  have hrp : (r : ℝ≥0∞) ≤ p := by exact_mod_cast hrN.le.trans hp
  have hι := isContinuousEmbedding_toLowerExponentL (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (k := 1) (p := (p : ℝ≥0∞))
    (r := (r : ℝ≥0∞)) (μ := volume) (Ω := Ω) hb.measure_lt_top.ne hrp
  have := hι.comp_isCompactEmbedding hc
  convert this using 1
  refine LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn h u).trans ?_)
  exact ((toLpₗ_coeFn (fun v ↦ (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
    (hb.closure.subset frontier_subset_closure)).memLp_fn_of_le_sobolevConj hb.measure_lt_top.ne
      hrN hr' hqr.le ⟨v, Submodule.mem_top⟩) _).trans
    (fn_toLowerExponentL hb.measure_lt_top.ne hrp u)).symm

/-- **Theorem 9.16 (Rellich–Kondrachov), the case `p = N`**: for a bounded open `Ω ⊆ ℝ^N` of
class `C¹` (by charts), `N ≥ 2` and `N ≤ q < ∞`, the injection `W^{1,N}(Ω) ⊂ L^q(Ω)` is
compact. [brezis2011functional] Theorem 9.16, the second line. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_eq {d : ℕ} {q : ℝ≥0}
    [Fact (1 ≤ (((d + 1 : ℕ) : ℝ≥0) : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hd : 1 ≤ d)
    (h : ∀ u : SobolevEuclidean (d + 1) 1 ((d + 1 : ℕ) : ℝ≥0) Ω,
      MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1
      ((d + 1 : ℕ) : ℝ≥0) Ω volume h) :=
  SobolevEuclidean.isCompactEmbedding_toLp_of_le hΩ hb hd le_rfl h

/-- **Theorem 9.16, "in particular `W^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection"**, for a
bounded open `Ω ⊆ ℝ^N` of class `C¹` (by charts) and `1 ≤ p < ∞`, provided `p < N` or `N ≥ 2`
(the case `N = 1 ≤ p`, on an interval, is not covered here). [brezis2011functional]
Theorem 9.16, the last sentence. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_self {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hd : p < ((d + 1 : ℕ) : ℝ≥0) ∨ 1 ≤ d) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      fun u ↦ SobolevMultiIndex.memLp u) := by
  rcases lt_or_ge p ((d + 1 : ℕ) : ℝ≥0) with hpN | hpN
  · have hp0 : 0 < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
    have hN0 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    obtain ⟨p', hp'⟩ : ∃ p' : ℝ≥0, (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ :=
      ⟨(p⁻¹ - ((d + 1 : ℕ) : ℝ≥0)⁻¹)⁻¹, by
        rw [NNReal.coe_inv, NNReal.coe_sub (by
          exact_mod_cast (inv_strictAnti₀ hp0 hpN).le), inv_inv]
        simp⟩
    exact SobolevEuclidean.isCompactEmbedding_toLp_of_lt hΩ hb hpN hp'
      (NNReal.lt_sobolevConj hp0 hpN hp')
  · rcases hd with hd | hd
    · exact absurd hpN (not_le.2 hd)
    · exact SobolevEuclidean.isCompactEmbedding_toLp_of_le hΩ hb hd hpN _

/-- **`W^{1,p}(Ω) ↪↪ L^p(Ω)` along `SobolevMultiIndex.fnL`**, the form of
`SobolevEuclidean.isCompactEmbedding_toLp_self` on the bundled inclusion. -/
theorem SobolevEuclidean.isCompactEmbedding_fnL {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hd : p < ((d + 1 : ℕ) : ℝ≥0) ∨ 1 ≤ d) :
    IsCompactEmbedding (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω
      volume).toLinearMap := by
  rw [← toLpₗ_self]
  exact SobolevEuclidean.isCompactEmbedding_toLp_self hΩ hb hd

end RellichGe
