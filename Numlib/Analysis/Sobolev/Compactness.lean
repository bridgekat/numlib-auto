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
(`MeasureTheory.Lp.monoExponentL` of `Numlib/Analysis/Sobolev/Cutoff.lean`). The instances are
`S = ⊤` with Theorem 9.7's operator (`SobolevEuclidean.isCompactEmbedding_toLp_of_lt`) and
`S = W_0^{1,p}(Ω)` with the extension by
zero of `Numlib/Analysis/Sobolev/Zero.lean` (Remark 20,
`SobolevEuclideanZero.isCompactEmbedding_toLp_of_lt`).
At the exponent `q = p` itself no interpolation is needed — `ℱ` is bounded in `L^p(ℝ^N)` by `‖P‖`
and Proposition 9.3 is its translation modulus — so `S ↪↪ L^p(Ω)` holds for *every* `1 ≤ p < ∞`
in every dimension (`HasSobolevExtensionOn.isCompactEmbedding_toLpOn_self`); hence
`W_0^{1,p}(Ω) ↪↪ L^p(Ω)` on any open set of finite measure
(`SobolevEuclideanZero.isCompactEmbedding_toLp`, `SobolevEuclideanZero.isCompactOperator_fnL`,
the compactness of `H^1_0(Ω) ⊂ L²(Ω)` that Theorems 9.23 and 9.31 use) and
`W^{1,p}(Ω) ↪↪ L^p(Ω)` on any extension domain of finite measure
(`SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain`), including
`N = 1 = p`.

The cases `p ≥ N` for `N ≥ 2` reduce to `p < N`: `W^{1,p}(Ω) ↪ W^{1,r}(Ω)` continuously on the
finite-measure `Ω` for an `r < N` with `r* > q` (`SobolevMultiIndex.toLowerExponentL`,
`NNReal.exists_lowerExponent`), and `W^{1,r}(Ω) ↪↪ L^q(Ω)`
(`SobolevEuclidean.isCompactEmbedding_toLp_of_le`, `…_of_eq`). The case `p > N` into `C(K)` for
a compact `K ⊇ Ω` is Arzelà–Ascoli (`ContinuousMap.isCompact_closure_of_forall_norm_le`) on the
uniformly bounded and uniformly Hölder image of the unit ball
(`HasSobolevExtensionOn.isCompactEmbedding_toContinuousMapOnL`,
`SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt`). The injection `W^{1,p}(Ω) ⊂ L^p(Ω)`
(`SobolevEuclidean.isCompactEmbedding_toLp_self`, `SobolevEuclidean.isCompactEmbedding_fnL`) is
covered for `1 ≤ p < ∞` whenever `p < N` or `N ≥ 2`; for `p > N` it also factors through `C(Ω̄)`
and the continuous extension by zero `C(Ω̄, ℝ) → L^p(Ω)` (`ContinuousMap.extendZeroToLpL`,
`SobolevEuclidean.isCompactEmbedding_toLp_self_of_gt`), which covers `N = 1 < p`, so that
`SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one` / `isCompactEmbedding_fnL_of_ne_one`
leave out only `N = 1 = p` (an interval, where the one-dimensional theory applies); the case
`p = ∞`, `W^{1,∞}(Ω) ⊂⊂ L^∞(Ω)` on a bounded `W^{1,∞}`-extension domain, is Arzelà–Ascoli on
the Lipschitz representatives (`SobolevEuclidean.isCompactEmbedding_fnL_top`).

On `W_0^{1,p}(Ω)` the other clauses of Theorem 9.16 hold with no regularity of `Ω` (Remark 20):
`W_0^{1,N}(Ω) ↪↪ L^q(Ω)` for `N ≤ q < ∞`, `N ≥ 2`, through the inclusion
`W_0^{1,N}(Ω) ↪ W_0^{1,r}(Ω)` (`SobolevMultiIndexZero.toLowerExponentL` of
`Numlib/Analysis/Sobolev/EmbeddingDomain.lean`) and the pull-back lemma
`SobolevMultiIndex.isCompactEmbedding_toLpₗOn_of_comp` (same file)
(`SobolevEuclideanZero.isCompactEmbedding_toLp_of_eq`), and `W_0^{1,p}(Ω) ↪↪ C(K)` for `p > N`
and a compact `K ⊇ Ω` (`SobolevEuclideanZero.isCompactEmbedding_toContinuousMapOnL`).

The compact embedding between successive orders, `W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)` along
`SobolevMultiIndex.toLowerOrderL` (`SobolevEuclidean.isCompactEmbedding_toLower_of_lt`,
Atkinson–Han's Theorem 7.3.9), is proved by induction on `k` from the case `k = 0` above: the
inductive step (`SobolevMultiIndex.isCompactEmbedding_of_forall_weakDeriv_eq`, stated with the
operators as variables) extracts one subsequence along which `u_n` and all `∂_i u_n` converge in
`W^{k,p}(Ω)` (`IsCompactEmbedding.exists_subseq_forall_tendsto`), so that every component
`∂^β u_n` converges in `L^p(Ω)` and `u_n` converges in the closed subspace `W^{k+1,p}(Ω)`
(`SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv`).
`IsSobolevExtensionDomainAll.of_isContDiffChartDomain` (`EmbeddingDomain.lean`) records that
Theorem 9.7 makes a bounded `C¹` chart domain an extension domain for every exponent, the
hypothesis of Corollary 9.15.

The last sections are **the Rellich–Kondrachov theorem at every order on an extension domain**:
`W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)` on any extension domain of finite measure, every `1 ≤ p < ∞`
(`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain`,
`…_toLowerOrderL_of_lt`), the compact embeddings of `W^{k,p}(Ω)` into `L^q(Ω)` and `C(K)`
for `k < N/p`, `k = N/p`, `k > N/p` (`SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_lt`,
`…_of_order_of_eq`, `SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`),
Atkinson–Han's Theorems 7.3.8 and 7.3.9 under the extension hypothesis, through the pull-back
and composition lemmas `SobolevMultiIndex.isContinuousEmbedding_toLpₗ_of_le`,
`SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_comp` and the order lowering
`SobolevEuclidean.exists_continuousLinearMap_orderOne` (`EmbeddingDomain.lean`); and their
counterparts at `p = ∞`, `W^{k,∞}(Ω) ⊂⊂ W^{l,∞}(Ω)` for `l < k`
(`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt`).

## References

[brezis2011functional], Theorem 9.16 and its proof, Remark 20; Atkinson–Han, *Theoretical
Numerical Analysis*, Theorems 7.3.8 and 7.3.9.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

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

/-! ### Extension by zero of a continuous function on a compact set, into `L^p(Ω)` -/

section ExtendZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {K : Set E} [CompactSpace K] {Ω : Set E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace ContinuousMap

open scoped Classical in
variable (K) in
/-- The extension by zero of a function on a subset `K` to the whole space. -/
def extendZero (f : C(K, ℝ)) : E → ℝ := fun x ↦ if h : x ∈ K then f ⟨x, h⟩ else 0

omit [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [CompactSpace K] in
/-- The extension by zero agrees with `f` on `K`. -/
theorem extendZero_of_mem (f : C(K, ℝ)) {x : E} (hx : x ∈ K) :
    extendZero K f x = f ⟨x, hx⟩ := by
  simp [extendZero, hx]

omit [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- The extension by zero is bounded by the sup norm of `f`. -/
theorem norm_extendZero_le (f : C(K, ℝ)) (x : E) : ‖extendZero K f x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ K
  · rw [extendZero_of_mem f hx]
    exact f.norm_coe_le_norm _
  · simp [extendZero, hx]

omit [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [CompactSpace K] in
/-- The extension by zero is continuous on `K`. -/
theorem continuousOn_extendZero (f : C(K, ℝ)) : ContinuousOn (extendZero K f) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  funext x
  exact extendZero_of_mem f x.2

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
/-- The extension by zero of a continuous function on `K ⊇ Ω` lies in `L^p(Ω)` when `Ω` is
measurable of finite measure. -/
theorem memLp_extendZero (f : C(K, ℝ)) (hΩK : Ω ⊆ K) (hΩ : MeasurableSet Ω) (hμ : μ Ω ≠ ⊤) :
    MemLp (extendZero K f) p (μ.restrict Ω) := by
  have : IsFiniteMeasure (μ.restrict Ω) := ⟨by simpa [Measure.restrict_apply_univ] using hμ.lt_top⟩
  exact MemLp.of_bound (((continuousOn_extendZero f).mono hΩK).aestronglyMeasurable (μ := μ) hΩ)
    ‖f‖ (Eventually.of_forall (norm_extendZero_le f))

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
/-- The `L^p(Ω)` norm of the extension by zero is at most `μ(Ω)^{1/p} ‖f‖`. -/
theorem eLpNorm_extendZero_le (f : C(K, ℝ)) (hΩK : Ω ⊆ K) (hΩ : MeasurableSet Ω) :
    eLpNorm (extendZero K f) p (μ.restrict Ω) ≤ μ Ω ^ p.toReal⁻¹ * ENNReal.ofReal ‖f‖ := by
  refine (eLpNorm_le_of_ae_bound (C := ‖f‖) ?_ (Eventually.of_forall (norm_extendZero_le f))).trans
    (le_of_eq ?_)
  · exact ((continuousOn_extendZero f).mono hΩK).aestronglyMeasurable hΩ
  · rw [Measure.restrict_apply_univ]

variable (μ K Ω p) in
/-- **Extension by zero, `C(K, ℝ) → L^p(Ω)`, as a bounded linear map** for a compact `K ⊇ Ω`
and a measurable `Ω` of finite measure: `f ↦ (f extended by zero)|_Ω`, of norm at most
`μ(Ω)^{1/p}`. Composed with the trace map `W^{1,p}(Ω) → C(Ω̄, ℝ)` of Morrey's theorem it gives
the injection `W^{1,p}(Ω) ⊂ L^p(Ω)` through `C(Ω̄)`, the route by which
[brezis2011functional] Theorem 9.16 reads "`W^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection" for
`p > N`. -/
def extendZeroToLpL (hΩK : Ω ⊆ K) (hΩ : MeasurableSet Ω) (hμ : μ Ω ≠ ⊤) :
    C(K, ℝ) →L[ℝ] Lp ℝ p (μ.restrict Ω) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (memLp_extendZero f hΩK hΩ hμ).toLp _
      map_add' := fun f g ↦ by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ K <;> simp [extendZero, hx]
      map_smul' := fun c f ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ K <;> simp [extendZero, hx] }
    (μ Ω ^ p.toReal⁻¹).toReal fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal (norm_nonneg f),
        ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ) ENNReal.ofReal_ne_top) ?_
      exact eLpNorm_extendZero_le f hΩK hΩ

omit [NormedSpace ℝ E] in
/-- The extension by zero, as an `L^p(Ω)` element, is `f` almost everywhere on `Ω`. -/
theorem coeFn_extendZeroToLpL (hΩK : Ω ⊆ K) (hΩ : MeasurableSet Ω) (hμ : μ Ω ≠ ⊤) (f : C(K, ℝ)) :
    extendZeroToLpL μ K Ω p hΩK hΩ hμ f =ᵐ[μ.restrict Ω] extendZero K f :=
  MemLp.coeFn_toLp (memLp_extendZero f hΩK hΩ hμ)

omit [NormedSpace ℝ E] in
/-- **Extension by zero is injective for `Ω ⊆ K ⊆ closure Ω`**, `Ω` open and `μ` positive on open
sets: a continuous function on `K` vanishing almost everywhere on `Ω` vanishes on `Ω`, hence on
its closure. -/
theorem extendZeroToLpL_injective [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E]
    [μ.IsOpenPosMeasure] (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω) (hΩo : IsOpen Ω) (hμ : μ Ω ≠ ⊤) :
    Function.Injective (extendZeroToLpL μ K Ω p hΩK hΩo.measurableSet hμ) := by
  intro f g hfg
  have h1 : extendZero K f =ᵐ[μ.restrict Ω] extendZero K g :=
    (coeFn_extendZeroToLpL hΩK hΩo.measurableSet hμ f).symm.trans
      ((Lp.ext_iff.1 hfg).trans (coeFn_extendZeroToLpL hΩK hΩo.measurableSet hμ g))
  have h2 : EqOn (extendZero K f) (extendZero K g) Ω :=
    Measure.eqOn_open_of_ae_eq h1 hΩo ((continuousOn_extendZero f).mono hΩK)
      ((continuousOn_extendZero g).mono hΩK)
  have h3 : EqOn (extendZero K f) (extendZero K g) K :=
    h2.of_subset_closure (continuousOn_extendZero f) (continuousOn_extendZero g) hΩK hKΩ
  ext ⟨x, hx⟩
  have := h3 hx
  rwa [extendZero_of_mem f hx, extendZero_of_mem g hx] at this

omit [NormedSpace ℝ E] in
/-- **Extension by zero is a continuous embedding `C(K, ℝ) ↪ L^p(Ω)`** for
`Ω ⊆ K ⊆ closure Ω`, `Ω` open of finite positive measure. -/
theorem isContinuousEmbedding_extendZeroToLpL [TopologicalSpace.PseudoMetrizableSpace E]
    [BorelSpace E] [μ.IsOpenPosMeasure] (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω) (hΩo : IsOpen Ω)
    (hμ : μ Ω ≠ ⊤) :
    IsContinuousEmbedding (extendZeroToLpL μ K Ω p hΩK hΩo.measurableSet hμ).toLinearMap :=
  ⟨extendZeroToLpL_injective hΩK hKΩ hΩo hμ, _,
    (extendZeroToLpL μ K Ω p hΩK hΩo.measurableSet hμ).le_opNorm⟩

end ContinuousMap

end ExtendZero

/-! ### Theorem 9.16 for `p > N`: `W^{1,p}(Ω) ⊂⊂ L^p(Ω)` through `C(Ω̄)` -/

section RellichGtSelf

open SobolevMultiIndex

/-- **The injection `W^{1,p}(Ω) ⊂ L^p(Ω)` factors through `C(Ω̄, ℝ)` for `p > N`**: on an
extension domain of finite measure, the inclusion `SobolevMultiIndex.toLpₗ` is the extension by
zero `C(closure Ω, ℝ) → L^p(Ω)` composed with the trace map `SobolevEuclidean.toContinuousMapL`
of Morrey's representative. -/
theorem SobolevEuclidean.toLpₗ_eq_extendZeroToLpL_comp_toContinuousMapL {N : ℕ}
    {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p)
    [CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))]
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (fun u ↦ memLp u)
      = (ContinuousMap.extendZeroToLpL volume (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))
          (Ω : Set (EuclideanSpace ℝ (Fin N))) p subset_closure Ω.isOpen.measurableSet
          hμ).toLinearMap ∘ₗ
        (SobolevEuclidean.toContinuousMapL hΩ hp
          (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))).toLinearMap := by
  refine LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn _ u).trans ?_)
  refine Filter.EventuallyEq.trans ?_ (ContinuousMap.coeFn_extendZeroToLpL subset_closure
    Ω.isOpen.measurableSet hμ (SobolevEuclidean.toContinuousMapL hΩ hp
      (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) u)).symm
  refine (SobolevEuclidean.fn_ae_eq_toContinuousMapL hΩ hp
    (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) u).trans ?_
  refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx ↦ ?_
  rw [ContinuousMap.extendZero_of_mem _ (subset_closure hx)]
  rfl

/-- **Theorem 9.16, "`W^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection", for `p > N`**: for a bounded
open `Ω ⊆ ℝ^N` of class `C¹` (by charts) and `N < p < ∞`, the injection `W^{1,p}(Ω) ⊂ L^p(Ω)` is
compact — it factors through the compact injection `W^{1,p}(Ω) ⊂ C(Ω̄)` and the continuous
extension by zero `C(Ω̄) → L^p(Ω)`. This covers the case `N = 1 < p` of the last sentence of
[brezis2011functional] Theorem 9.16, left out of `SobolevEuclidean.isCompactEmbedding_toLp_self`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_self_of_gt {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      fun u ↦ SobolevMultiIndex.memLp u) := by
  have : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  rw [SobolevEuclidean.toLpₗ_eq_extendZeroToLpL_comp_toContinuousMapL
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure)) hp hb.measure_lt_top.ne]
  exact (SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt hΩ hb hp subset_closure)
    |>.comp_isContinuousEmbedding
      (ContinuousMap.isContinuousEmbedding_extendZeroToLpL subset_closure subset_rfl Ω.isOpen _)

/-- **Theorem 9.16, "`W^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection"**, for a bounded open
`Ω ⊆ ℝ^N` of class `C¹` (by charts) and `1 ≤ p < ∞`, provided `p ≠ 1` or `N ≥ 2`: the three
routes `p < N` (Rellich–Kondrachov), `N ≤ p` with `N ≥ 2` (lowering the exponent) and `p > N`
(through `C(Ω̄)`) together leave out only `N = 1 = p`. [brezis2011functional] Theorem 9.16, the
last sentence. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hd : p ≠ 1 ∨ 1 ≤ d) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      fun u ↦ SobolevMultiIndex.memLp u) := by
  rcases lt_or_ge p ((d + 1 : ℕ) : ℝ≥0) with hpN | hpN
  · exact SobolevEuclidean.isCompactEmbedding_toLp_self hΩ hb (Or.inl hpN)
  rcases hd with hp | hd
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
      exact SobolevEuclidean.isCompactEmbedding_toLp_self_of_gt hΩ hb
        (by simpa using lt_of_le_of_ne hp1 (Ne.symm hp))
    · exact SobolevEuclidean.isCompactEmbedding_toLp_self hΩ hb (Or.inr hd)
  · exact SobolevEuclidean.isCompactEmbedding_toLp_self hΩ hb (Or.inr hd)

/-- **`W^{1,p}(Ω) ↪↪ L^p(Ω)` along `SobolevMultiIndex.fnL`**, for `1 ≤ p < ∞` with `p ≠ 1` or
`N ≥ 2`: the form of `SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one` on the bundled
inclusion. -/
theorem SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one {d : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hd : p ≠ 1 ∨ 1 ≤ d) :
    IsCompactEmbedding (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω
      volume).toLinearMap := by
  rw [← toLpₗ_self]
  exact SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one hΩ hb hd

end RellichGtSelf

/-! ### `W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)`: the compact embedding between successive orders -/

section LowerOrder

/-- **A common convergent subsequence for finitely many sequences under a compact embedding**:
given bounded sequences `u i`, `i` in a finite type, there is one subsequence along which every
`κ (u i ·)` converges — the images lie in a finite product of compact sets. -/
theorem IsCompactEmbedding.exists_subseq_forall_tendsto {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 W] {κ : V →ₗ[𝕜] W} (h : IsCompactEmbedding κ) {ι : Type*} [Finite ι]
    (u : ι → ℕ → V) (hu : ∀ i, ∃ M : ℝ, ∀ n, ‖u i n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ w : W, Tendsto (fun n ↦ κ (u i (φ n))) atTop (𝓝 w) := by
  choose M hM using hu
  have hK : ∀ i, IsCompact (closure (κ '' closedBall 0 (M i))) := fun i ↦
    h.isCompactOperator.isCompact_closure_image_closedBall (M i)
  have hmem : ∀ n, (fun i ↦ κ (u i n)) ∈ Set.univ.pi fun i ↦ closure (κ '' closedBall 0 (M i)) :=
    fun n i _ ↦ subset_closure ⟨u i n, by simpa using hM i n, rfl⟩
  obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_univ_pi hK).tendsto_subseq hmem
  exact ⟨φ, hφ, fun i ↦ ⟨a i, tendsto_pi_nhds.1 ha i⟩⟩

/-- **The sequential criterion for a compact embedding**, on a bounded linear map that is a
continuous embedding: every bounded sequence has a subsequence whose image converges. -/
theorem IsCompactEmbedding.of_forall_exists_subseq_tendsto {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 W] {ι : V →L[𝕜] W} (hι : IsContinuousEmbedding ι.toLinearMap)
    (h : ∀ u : ℕ → V, (∃ M : ℝ, ∀ n, ‖u n‖ ≤ M) →
      ∃ (φ : ℕ → ℕ) (w : W), StrictMono φ ∧ Tendsto (fun n ↦ ι (u (φ n))) atTop (𝓝 w)) :
    IsCompactEmbedding ι.toLinearMap :=
  { hι with exists_subseq_tendsto := h }

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

/-- **A sequence of `W^{k,p}(Ω)` all of whose weak derivatives converge in `L^p(Ω)` converges in
`W^{k,p}(Ω)`**: the ambient space is an `ℓ^p` product of `L^p(Ω)` spaces, in which convergence is
componentwise, and `W^{k,p}(Ω)` is closed in it (`SobolevMultiIndex.isClosed`). -/
theorem SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv
    {x : ℕ → SobolevMultiIndex F b k p Ω μ}
    (h : ∀ α, ∃ L : Lp F p (μ.restrict (Ω : Set E)),
      Tendsto (fun n ↦ weakDeriv (x n) α) atTop (𝓝 L)) :
    ∃ y : SobolevMultiIndex F b k p Ω μ, Tendsto x atTop (𝓝 y) := by
  choose L hL using h
  have hconv : Tendsto (fun n ↦ (x n : SobolevMultiIndexTuple F ι k p Ω μ)) atTop
      (𝓝 (WithLp.toLp p L)) := by
    have h1 : Tendsto (fun n ↦ fun α ↦ weakDeriv (x n) α) atTop (𝓝 L) := tendsto_pi_nhds.2 hL
    have h2 := ((PiLp.continuous_toLp p fun _ : MultiIndexLE ι k ↦ Lp F p (μ.restrict (Ω : Set E)))
      |>.tendsto L).comp h1
    convert h2 using 1
    funext n
    rfl
  have hy : WithLp.toLp p L ∈ SobolevMultiIndex F b k p Ω μ :=
    SobolevMultiIndex.isClosed.mem_of_tendsto hconv (Eventually.of_forall fun n ↦ (x n).2)
  exact ⟨⟨WithLp.toLp p L, hy⟩, tendsto_subtype_rng.2 hconv⟩

end LowerOrder

section LowerOrderAbstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

namespace SobolevMultiIndex

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- The components of `SobolevMultiIndex.toLowerOrderL u` are those of `u`. -/
theorem weakDeriv_toLowerOrderL {k' : ℕ} (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k') :
    weakDeriv (toLowerOrderL F b p Ω μ hk u) α = weakDeriv u ⟨α.1, α.2.trans hk⟩ :=
  rfl

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- The only component of `SobolevMultiIndex.toLowerOrderL u` in `W^{0,p}(Ω)` is the function. -/
theorem weakDeriv_toLowerOrderL_zero (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι 0) :
    weakDeriv (toLowerOrderL F b p Ω μ (Nat.zero_le k) u) α = fnL F b k p Ω μ u := by
  obtain rfl : α = 0 := Subtype.ext (funext fun i ↦ Nat.le_zero.1
    ((Finset.single_le_sum (f := α.1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans α.2))
  rfl

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- The components of `SobolevMultiIndex.partialDerivL i u` are those of `u` at `α + e_i`. -/
theorem weakDeriv_partialDerivL (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ)
    (α : MultiIndexLE ι k) :
    weakDeriv (partialDerivL F b p Ω μ i u) α = weakDeriv u (MultiIndexLE.addSingle i α) :=
  rfl

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- `‖toLowerOrderL u‖ ≤ ‖u‖`. -/
theorem norm_toLowerOrderL_apply_le {k' : ℕ} (hk : k' ≤ k) (u : SobolevMultiIndex F b k p Ω μ) :
    ‖toLowerOrderL F b p Ω μ hk u‖ ≤ ‖u‖ :=
  norm_toLowerOrder_le hk u

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- `‖partialDerivL i u‖ ≤ ‖u‖`. -/
theorem norm_partialDerivL_apply_le (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    ‖partialDerivL F b p Ω μ i u‖ ≤ ‖u‖ :=
  norm_partialDeriv_le i u

variable [FiniteDimensional ℝ E] [BorelSpace E]

omit [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- **`W^{k,p}(Ω) ↪ W^{k',p}(Ω)` is a continuous embedding** for `k' ≤ k`, along
`SobolevMultiIndex.toLowerOrderL`. -/
theorem isContinuousEmbedding_toLowerOrderL {k' : ℕ} (hk : k' ≤ k) :
    IsContinuousEmbedding (toLowerOrderL F b p Ω μ hk).toLinearMap :=
  ⟨toLowerOrderL_injective hk, 1, fun u ↦ by rw [one_mul]; exact norm_toLowerOrder_le hk u⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **`W^{1,p}(Ω) ⊂⊂ W^{0,p}(Ω)` from `W^{1,p}(Ω) ⊂⊂ L^p(Ω)`, with the operator as a variable**:
a continuous embedding `T : W^{1,p}(Ω) → W^{0,p}(Ω)` whose only component is the function is a
compact embedding as soon as the inclusion `W^{1,p}(Ω) → L^p(Ω)` is one. -/
theorem isCompactEmbedding_of_forall_weakDeriv_eq_fnL
    {T : SobolevMultiIndex F b 1 p Ω μ →L[ℝ] SobolevMultiIndex F b 0 p Ω μ}
    (hTc : ∀ (v : SobolevMultiIndex F b 1 p Ω μ) (α : MultiIndexLE ι 0),
      weakDeriv (T v) α = fnL F b 1 p Ω μ v)
    (hι : IsContinuousEmbedding T.toLinearMap)
    (hc : IsCompactEmbedding (fnL F b 1 p Ω μ).toLinearMap) :
    IsCompactEmbedding T.toLinearMap := by
  refine IsCompactEmbedding.of_forall_exists_subseq_tendsto hι fun u hu ↦ ?_
  obtain ⟨φ, w, hφ, hw⟩ := hc.exists_subseq_tendsto u hu
  have hcomp : ∀ α : MultiIndexLE ι 0, ∃ L : Lp F p (μ.restrict (Ω : Set E)),
      Tendsto (fun n ↦ weakDeriv (T (u (φ n))) α) atTop (𝓝 L) := fun α ↦
    ⟨w, by simpa only [hTc, ContinuousLinearMap.coe_coe] using hw⟩
  obtain ⟨y, hy⟩ := SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv hcomp
  exact ⟨φ, y, hφ, hy⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The inductive step of `W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)`, with the operators as variables**:
given `T : W^{k+2,p}(Ω) → W^{k+1,p}(Ω)` and `T' : W^{k+1,p}(Ω) → W^{k,p}(Ω)` forgetting the top
components, and `D i : W^{k+2,p}(Ω) → W^{k+1,p}(Ω)` the partial derivatives, all bounded by one,
if `T'` is a compact embedding then so is `T`. For a bounded sequence `u_n` in `W^{k+2,p}(Ω)`,
the sequences `T u_n` and `D_i u_n` are bounded in `W^{k+1,p}(Ω)`, so along a common subsequence
their images under `T'` converge in `W^{k,p}(Ω)`; every component `∂^β u_n`, `|β| ≤ k + 1`, is a
component of one of them (`∂^β = ∂^{β'} ∂_i` for `|β| = k + 1`), hence converges in `L^p(Ω)`,
and `T u_n` converges in `W^{k+1,p}(Ω)`
(`SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv`). -/
theorem isCompactEmbedding_of_forall_weakDeriv_eq
    {T : SobolevMultiIndex F b (k + 1 + 1) p Ω μ →L[ℝ] SobolevMultiIndex F b (k + 1) p Ω μ}
    {T' : SobolevMultiIndex F b (k + 1) p Ω μ →L[ℝ] SobolevMultiIndex F b k p Ω μ}
    {D : ι → SobolevMultiIndex F b (k + 1 + 1) p Ω μ →L[ℝ] SobolevMultiIndex F b (k + 1) p Ω μ}
    (hTc : ∀ (v : SobolevMultiIndex F b (k + 1 + 1) p Ω μ) (β : MultiIndexLE ι (k + 1)),
      weakDeriv (T v) β = weakDeriv v ⟨β.1, β.2.trans (Nat.le_succ _)⟩)
    (hT'c : ∀ (v : SobolevMultiIndex F b (k + 1) p Ω μ) (γ : MultiIndexLE ι k),
      weakDeriv (T' v) γ = weakDeriv v ⟨γ.1, γ.2.trans (Nat.le_succ _)⟩)
    (hDc : ∀ (i : ι) (v : SobolevMultiIndex F b (k + 1 + 1) p Ω μ) (γ : MultiIndexLE ι (k + 1)),
      weakDeriv (D i v) γ = weakDeriv v (MultiIndexLE.addSingle i γ))
    (hTn : ∀ v, ‖T v‖ ≤ ‖v‖) (hDn : ∀ i v, ‖D i v‖ ≤ ‖v‖)
    (hι : IsContinuousEmbedding T.toLinearMap) (ih : IsCompactEmbedding T'.toLinearMap) :
    IsCompactEmbedding T.toLinearMap := by
  refine IsCompactEmbedding.of_forall_exists_subseq_tendsto hι fun u hu ↦ ?_
  obtain ⟨M, hM⟩ := hu
  -- the sequences `u_n` and `∂_i u_n` in `W^{k+1,p}(Ω)`
  obtain ⟨t, ht⟩ : ∃ t : Option ι → ℕ → SobolevMultiIndex F b (k + 1) p Ω μ,
      t = fun i n ↦ Option.elim i (T (u n)) (fun i ↦ D i (u n)) := ⟨_, rfl⟩
  have htb : ∀ i, ∃ M : ℝ, ∀ n, ‖t i n‖ ≤ M := fun i ↦ ⟨M, fun n ↦ by
    rw [ht]
    rcases i with _ | i
    · exact (hTn _).trans (hM n)
    · exact (hDn i _).trans (hM n)⟩
  obtain ⟨φ, hφ, hlim⟩ := ih.exists_subseq_forall_tendsto t htb
  choose w hw using hlim
  have hw' : ∀ (i : Option ι) (γ : MultiIndexLE ι k),
      Tendsto (fun n ↦ weakDeriv (T' (t i (φ n))) γ) atTop (𝓝 (weakDeriv (w i) γ)) := fun i γ ↦
    ((weakDerivL F b k p Ω μ γ).continuous.tendsto (w i)).comp (hw i)
  -- convergence of every component of `u (φ n)` in `W^{k+1,p}(Ω)`
  have hcomp : ∀ β : MultiIndexLE ι (k + 1), ∃ L : Lp F p (μ.restrict (Ω : Set E)),
      Tendsto (fun n ↦ weakDeriv (T (u (φ n))) β) atTop (𝓝 L) := by
    intro β
    rcases Nat.lt_or_ge (∑ j, β.1 j) (k + 1) with hlt | hge
    · -- `|β| ≤ k`: a component of `u_n` in `W^{k,p}(Ω)`
      have hβ : ∑ j, β.1 j ≤ k := Nat.lt_succ_iff.1 hlt
      refine ⟨weakDeriv (w none) ⟨β.1, hβ⟩, ?_⟩
      have := hw' none ⟨β.1, hβ⟩
      simp only [ht, Option.elim, hT'c, hTc] at this ⊢
      exact this
    · -- `|β| = k + 1`: `β = β' + e_i`, a component of `∂_i u_n` in `W^{k,p}(Ω)`
      obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, β.1 i ≠ 0 :=
        Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := β.1) (by omega)
      obtain ⟨β', hβ'⟩ : ∃ β' : ι → ℕ, β.1 = β' + Pi.single i 1 := by
        refine ⟨β.1 - Pi.single i 1, funext fun j ↦ ?_⟩
        by_cases hj : j = i
        · subst hj
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
          omega
        · simp [Pi.single_eq_of_ne hj]
      have hβ'k : ∑ j, β' j ≤ k := by
        have := β.2
        rw [hβ'] at this
        simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
          ite_true] at this
        omega
      have hβeq : (⟨β.1, β.2.trans (Nat.le_succ _)⟩ : MultiIndexLE ι (k + 1 + 1))
          = MultiIndexLE.addSingle i (⟨β', hβ'k.trans (Nat.le_succ k)⟩ : MultiIndexLE ι (k + 1)) :=
        Subtype.ext hβ'
      refine ⟨weakDeriv (w (some i)) ⟨β', hβ'k⟩, ?_⟩
      have := hw' (some i) ⟨β', hβ'k⟩
      simp only [ht, Option.elim, hT'c, hDc, hTc, hβeq] at this ⊢
      exact this
  obtain ⟨y, hy⟩ := SobolevMultiIndex.exists_tendsto_of_forall_tendsto_weakDeriv hcomp
  exact ⟨φ, y, hφ, hy⟩

end SobolevMultiIndex

end LowerOrderAbstract

section RellichLower

open SobolevMultiIndex

variable {d : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **`W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)`** for a bounded open `Ω ⊆ ℝ^N` of class `C¹` (by charts),
`1 ≤ p < ∞` with `p ≠ 1` or `N ≥ 2`: the inclusion `SobolevMultiIndex.toLowerOrderL` is a
compact embedding (Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 7.3.9, under `C¹`;
[brezis2011functional] Theorem 9.16 iterated). Induction on `k` from `W^{1,p}(Ω) ⊂⊂ L^p(Ω)`
(`SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one`), the step being
`SobolevMultiIndex.isCompactEmbedding_of_forall_weakDeriv_eq` for the operators forgetting the
top components and the partial derivatives. -/
theorem SobolevEuclidean.isCompactEmbedding_toLower_of_lt
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hd : p ≠ 1 ∨ 1 ≤ d)
    (k : ℕ) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p Ω
      volume (Nat.le_succ k)).toLinearMap := by
  induction k with
  | zero =>
    exact isCompactEmbedding_of_forall_weakDeriv_eq_fnL (weakDeriv_toLowerOrderL_zero)
      (isContinuousEmbedding_toLowerOrderL (Nat.zero_le 1))
      (SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one hΩ hb hd)
  | succ k ih =>
    exact isCompactEmbedding_of_forall_weakDeriv_eq (weakDeriv_toLowerOrderL (Nat.le_succ (k + 1)))
      (weakDeriv_toLowerOrderL (Nat.le_succ k))
      (weakDeriv_partialDerivL (F := ℝ) (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis)
        (p := p) (Ω := Ω) (μ := volume))
      (norm_toLowerOrderL_apply_le _) (norm_partialDerivL_apply_le)
      (isContinuousEmbedding_toLowerOrderL (Nat.le_succ (k + 1))) ih

end RellichLower

/-! ### The abstract Rellich–Kondrachov lemma at `q = p`: every `1 ≤ p < ∞`, every `N` -/

section RellichSelf

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- The family `ℱ = P(unit ball)` is bounded in `L^p(ℝ^N)` (by `‖P‖`), for every `p`. -/
theorem HasSobolevExtensionOn.isBounded_image_closedBall_self
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) :
    Bornology.IsBounded ((fun u : S ↦ (SobolevEuclidean.memLp_fn (P u)).toLp _) ''
      closedBall (0 : S) 1) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨‖P‖, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hPu : ‖P u‖ ≤ ‖P‖ := by
    calc ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖P‖ := mul_one _
  have hb : eLpNorm (fn (P u)) p volume ≤ ENNReal.ofReal ‖P u‖ := by
    rw [← eLpNorm_restrict_coe_top]
    exact SobolevMultiIndex.eLpNorm_fn_le_ofReal_norm (P u)
  rw [mem_closedBall_zero_iff, Lp.norm_toLp]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans ?_
  rw [ENNReal.toReal_ofReal (norm_nonneg _)]
  exact hPu

/-- The family `ℱ = P(unit ball)` has a uniform translation modulus in `L^p(ℝ^N)`, for every
`1 ≤ p < ∞`: Proposition 9.3, `‖τ_h v − v‖_p ≤ ‖h‖ ‖∇v‖_p ≤ ‖h‖ N ‖P‖` — the hypothesis of the
Kolmogorov–M. Riesz–Fréchet theorem in [brezis2011functional] §9.3, proof of Theorem 9.16, at
`q = p`, where no interpolation is needed. -/
theorem HasSobolevExtensionOn.uniform_translate_image_closedBall_self
    (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ (fun u : S ↦
      (SobolevEuclidean.memLp_fn (P u)).toLp _) '' closedBall (0 : S) 1,
        ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ < δ →
          eLpNorm (fun x ↦ f (x + h) - f x) p volume < ε := by
  intro ε hε
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = N * ENNReal.ofReal ‖P‖ := ⟨_, rfl⟩
  have hAt : A ≠ ⊤ := by
    rw [hA]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  obtain ⟨δ, hδ0, hδ⟩ := EuclideanSpace.exists_pos_forall_enorm_rpow_mul_lt (N := N) one_pos hAt hε
  refine ⟨δ, hδ0, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ h hh
  have hPu : ‖P u‖ ≤ ‖P‖ := by
    calc ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖P‖ := mul_one _
  have hGae := MemLp.coeFn_toLp (SobolevEuclidean.memLp_fn (P u))
  have hae : (fun x ↦ ((SobolevEuclidean.memLp_fn (P u)).toLp _) (x + h)
        - ((SobolevEuclidean.memLp_fn (P u)).toLp _) x)
      =ᵐ[volume] fun x ↦ fn (P u) (x + h) - fn (P u) x := by
    have h1 := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hGae
    filter_upwards [h1, hGae] with x hx1 hx2
    simp only [Function.comp_apply] at hx1
    rw [hx1, hx2]
  rw [eLpNorm_congr_ae hae]
  refine lt_of_le_of_lt ?_ (hδ h hh)
  rw [ENNReal.rpow_one, hA]
  refine (SobolevEuclidean.eLpNorm_fn_sub_translate_le ENNReal.coe_ne_top (P u) h).trans ?_
  refine mul_le_mul' le_rfl ((SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le (P u)).trans ?_)
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hPu)

/-- The inclusion `S → L^p(Ω)` along `fnL` sends `u` to the restriction to `Ω` of `fn (P u)`,
read in `L^p(ℝ^N)`: the image of the unit ball of `S` is `ℱ|_Ω`, `ℱ = P(unit ball)`. -/
theorem HasSobolevExtensionOn.fnL_comp_subtypeL_apply (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤)
    (hP : ∀ u : S, fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fn (u : SobolevEuclidean N 1 p Ω)) (u : S) :
    (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume ∘L S.subtypeL) u
      = Lp.restrictCLM ℝ ℝ p volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
          ((SobolevEuclidean.memLp_fn (P u)).toLp _) := by
  refine Lp.ext (Filter.EventuallyEq.trans ?_ (Lp.coeFn_restrictCLM _ _).symm)
  refine Filter.EventuallyEq.trans (hP u).symm (Filter.EventuallyEq.symm ?_)
  exact ae_restrict_of_ae (MemLp.coeFn_toLp (SobolevEuclidean.memLp_fn (P u)))

/-- **The image of the unit ball of `S` in `L^p(Ω)` has compact closure**, for a subspace `S` of
`W^{1,p}(Ω)` with an extension operator and `volume Ω < ∞`, every `1 ≤ p < ∞`: it is `ℱ|_Ω` where
`ℱ = P(unit ball) ⊆ W^{1,p}(ℝ^N)` is bounded in `L^p(ℝ^N)` with a uniform translation modulus
in `L^p` (Proposition 9.3), so the Kolmogorov–M. Riesz–Fréchet theorem
`MeasureTheory.Lp.isCompact_closure_image_restrictCLM_of_uniform_translate` applies. -/
theorem HasSobolevExtensionOn.isCompact_closure_image_closedBall_self
    (hS : HasSobolevExtensionOn S)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompact (closure (⇑(fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume ∘L
      S.subtypeL) '' closedBall 0 1)) := by
  obtain ⟨P, hP⟩ := id hS
  have himg : ⇑(fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume ∘L S.subtypeL) ''
      closedBall 0 1 = Lp.restrictCLM ℝ ℝ p volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ''
        ((fun u : S ↦ (SobolevEuclidean.memLp_fn (P u)).toLp _) '' closedBall (0 : S) 1) := by
    rw [Set.image_image]
    exact Set.image_congr fun u _ ↦ HasSobolevExtensionOn.fnL_comp_subtypeL_apply P hP u
  rw [himg]
  exact Lp.isCompact_closure_image_restrictCLM_of_uniform_translate ENNReal.coe_ne_top
    (HasSobolevExtensionOn.isBounded_image_closedBall_self P)
    (HasSobolevExtensionOn.uniform_translate_image_closedBall_self P) hΩ

/-- **The abstract Rellich–Kondrachov lemma at `q = p`**: for a subspace `S` of `W^{1,p}(Ω)` with
an extension operator (`HasSobolevExtensionOn S`), `volume Ω < ∞` and *any* `1 ≤ p < ∞` in *any*
dimension, the inclusion `S → L^p(Ω)` (along `SobolevMultiIndex.toLpₗOn`) is a compact embedding
(`HasSobolevExtensionOn.isCompact_closure_image_closedBall_self`). This is the last sentence of
[brezis2011functional] Theorem 9.16, "`W^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection", in the
generality of its proof, without the case distinction `p < N`, `p = N`, `p > N` (which the proof
needs only for the exponents `q ≠ p`). -/
theorem HasSobolevExtensionOn.isCompactEmbedding_toLpOn_self (hS : HasSobolevExtensionOn S)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      fun u ↦ memLp (u : SobolevEuclidean N 1 p Ω)) := by
  rw [toLpₗOn_self]
  exact isCompactEmbedding_of_isCompact_closure_image_closedBall
    (fun _ _ huv ↦ Subtype.ext (fnL_injective huv))
    (hS.isCompact_closure_image_closedBall_self hΩ)

/-- **Theorem 9.16, "`W^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection", on any extension domain of
finite measure and for every `1 ≤ p < ∞`** — in particular for `N = 1 = p`, the case left out
of `SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one`. [brezis2011functional]
Theorem 9.16, the last sentence. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      fun u ↦ SobolevMultiIndex.memLp u) :=
  SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top _ (hΩ.isCompactEmbedding_toLpOn_self hμ)

end RellichSelf

/-! ### Remark 20: the compactness clauses on `W_0^{1,p}(Ω)` of an arbitrary open set -/

section RellichZero

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

namespace SobolevEuclideanZero

/-- **Remark 20, the compactness clause: `W_0^{1,p}(Ω) ↪↪ L^p(Ω)` for an arbitrary open set `Ω`
of finite measure** (in particular a bounded one), with no regularity of `Ω`, for every
`1 ≤ p < ∞` and every `N`: the abstract lemma `HasSobolevExtensionOn.isCompactEmbedding_toLpOn_self`
with `S = W_0^{1,p}(Ω)` and the extension by zero `SobolevEuclideanZero.hasSobolevExtensionOn`.
"Similarly, the conclusion of Theorem 9.16 is true for `W_0^{1,p}(Ω)` with an arbitrary bounded
open set `Ω`" ([brezis2011functional] Chapter 9, Remark 20); the clauses for the other exponents
`q` of Theorem 9.16 are `SobolevEuclideanZero.isCompactEmbedding_toLp_of_lt` (`p < N`,
`1 ≤ q < p*`), `SobolevEuclideanZero.isCompactEmbedding_toLp_of_eq` (`p = N ≥ 2`, `N ≤ q < ∞`)
and `SobolevEuclideanZero.isCompactEmbedding_toContinuousMapOnL` (`p > N`, into `C(Ω̄)`). This
is the compactness of the injection `H^1_0(Ω) ⊂ L²(Ω)` used by the proofs of Theorems 9.23 and
9.31 (`SobolevEuclideanZero.isCompactOperator_fnL`). -/
theorem isCompactEmbedding_toLp (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclideanZero N 1 p Ω) fun u ↦ memLp (u : SobolevEuclidean N 1 p Ω)) :=
  hasSobolevExtensionOn.isCompactEmbedding_toLpOn_self hΩ

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- **`W_0^{1,p}(Ω) ↪↪ L^p(Ω)` along `SobolevMultiIndexZero.fnL`**, for an open set of finite
measure and `1 ≤ p < ∞` (stated for `p : ℝ≥0∞`, `p ≠ ∞`, the form the elliptic theory at `p = 2`
consumes). [brezis2011functional] Chapter 9, Remark 20. -/
theorem isCompactEmbedding_fnL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactEmbedding (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 p Ω volume).toLinearMap := by
  lift p to ℝ≥0 using hp
  have h := isCompactEmbedding_toLp (p := p) (Ω := Ω) hΩ
  rwa [SobolevMultiIndexZero.toLpₗOn_eq_fnL (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)
    (μ := volume)] at h

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- **The inclusion `W_0^{1,p}(Ω) → L^p(Ω)` is a compact operator** for an open set of finite
measure and `1 ≤ p < ∞`: the form of `SobolevEuclideanZero.isCompactEmbedding_toLp` that the
Fredholm alternative for the elliptic Dirichlet problem consumes at `p = 2`
([brezis2011functional] Theorem 9.23, proof: "`T : L² → L²` is a compact operator since `Ω` is
bounded"). -/
theorem isCompactOperator_fnL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    IsCompactOperator (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 p Ω volume) :=
  (isCompactEmbedding_fnL hp hΩ).isCompactOperator

/-- **Remark 20, case `p < N`, the membership**: `fn u ∈ L^q(Ω)` for `u ∈ W_0^{1,p}(Ω)` and
`1 ≤ q ≤ p*` on an open set of finite measure. -/
theorem memLp_fn_of_le_sobolevConj (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q ≤ p')
    (u : SobolevEuclideanZero N 1 p Ω) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hasSobolevExtensionOn.memLp_fn_of_le_sobolevConj hΩ hpN hp' hqp' u

/-- **Remark 20, the compactness clause, case `p < N`**: `W_0^{1,p}(Ω) ↪↪ L^q(Ω)` for an
arbitrary open set `Ω` of finite measure, `1 ≤ p < N`, `1/p* = 1/p − 1/N` and `1 ≤ q < p*`
([brezis2011functional] Remark 20; Theorem 9.16, the first line). -/
theorem isCompactEmbedding_toLp_of_lt [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q < p') :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclideanZero N 1 p Ω) (memLp_fn_of_le_sobolevConj hΩ hpN hp' hqp'.le)) :=
  SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn hasSobolevExtensionOn hΩ hpN
    hp' hqp'

/-- **Remark 20, the compactness clause, case `p = N`**: `W_0^{1,N}(Ω) ↪↪ L^q(Ω)` for an
arbitrary open set `Ω` of finite measure, `N ≥ 2` and `N ≤ q < ∞`: `W_0^{1,N}(Ω) ↪ W_0^{1,r}(Ω)`
continuously for an `r < N` with `r* > q` (`SobolevMultiIndexZero.toLowerExponentL`), and
`W_0^{1,r}(Ω) ↪↪ L^q(Ω)` by the case `p < N` ([brezis2011functional] Remark 20; Theorem 9.16,
the second line). -/
theorem isCompactEmbedding_toLp_of_eq [Fact (1 ≤ (N : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsCompactEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N Ω volume
      (SobolevEuclideanZero N 1 N Ω) (memLp_fn_of_eq hN hq)) := by
  obtain ⟨r, hr1, hrN, hr', hq2⟩ := NNReal.exists_lowerExponent hN hq
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  have hrp : (r : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by exact_mod_cast hrN.le
  exact SobolevMultiIndex.isCompactEmbedding_toLpₗOn_of_comp
    (SobolevMultiIndexZero.toLowerExponentL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1
      (N : ℝ≥0∞) (r : ℝ≥0∞) volume hΩ hrp)
    (SobolevMultiIndexZero.isContinuousEmbedding_toLowerExponentL hΩ hrp)
    (SobolevMultiIndexZero.fn_toLowerExponentL hΩ hrp)
    (SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn
      (S := SobolevEuclideanZero N 1 r Ω) hasSobolevExtensionOn hΩ hrN hr' hq2) _

/-- **Remark 20, the compactness clause, case `p > N`**: for an arbitrary open set `Ω`,
`N < p < ∞` and a compact `K ⊇ Ω` (such as `closure Ω` for a bounded `Ω`), the trace
`W_0^{1,p}(Ω) → C(K)` of the continuous representative (`HasSobolevExtensionOn.toContinuousMapOnL`
for the extension by zero) is a compact embedding: "`W_0^{1,p}(Ω) ⊂ C(Ω̄)` with compact
injection" ([brezis2011functional] Remark 20; Theorem 9.16, the third line). -/
theorem isCompactEmbedding_toContinuousMapOnL (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))}
    [CompactSpace K] (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    IsCompactEmbedding
      ((hasSobolevExtensionOn (N := N) (p := p) (Ω := Ω)).toContinuousMapOnL hp K).toLinearMap :=
  hasSobolevExtensionOn.isCompactEmbedding_toContinuousMapOnL hp hK

end SobolevEuclideanZero

end RellichZero

/-! ### `W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)` on an extension domain of finite measure -/

section CompactLower

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **`W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)` on an extension domain of finite measure**, for every
`1 ≤ p < ∞` and every dimension `N` (`[han2009theoretical]` Theorem 7.3.9, the book's Lipschitz
hypothesis replaced by the extension property): the inclusion `SobolevMultiIndex.toLowerOrderL`
is a compact embedding. Induction on `k` from `W^{1,p}(Ω) ⊂⊂ L^p(Ω)`
(`SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain`, which needs no
case distinction on `p` and `N`), the step being
`SobolevMultiIndex.isCompactEmbedding_of_forall_weakDeriv_eq` exactly as in
`SobolevEuclidean.isCompactEmbedding_toLower_of_lt`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (k : ℕ) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω
      volume (Nat.le_succ k)).toLinearMap := by
  induction k with
  | zero =>
    have hc := SobolevEuclidean.isCompactEmbedding_toLp_self_of_isSobolevExtensionDomain hΩ hμ
    rw [toLpₗ_self] at hc
    exact isCompactEmbedding_of_forall_weakDeriv_eq_fnL (weakDeriv_toLowerOrderL_zero)
      (isContinuousEmbedding_toLowerOrderL (Nat.zero_le 1)) hc
  | succ k ih =>
    exact isCompactEmbedding_of_forall_weakDeriv_eq (weakDeriv_toLowerOrderL (Nat.le_succ (k + 1)))
      (weakDeriv_toLowerOrderL (Nat.le_succ k))
      (weakDeriv_partialDerivL (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
        (p := p) (Ω := Ω) (μ := volume))
      (norm_toLowerOrderL_apply_le _) (norm_partialDerivL_apply_le)
      (isContinuousEmbedding_toLowerOrderL (Nat.le_succ (k + 1))) ih

end CompactLower

/-! ### Composition lemmas for the embeddings of `W^{k,p}(Ω)` -/

section Composition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (1 ≤ q)] {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- **`W^{k,p}(Ω) ↪ L^q(Ω)` for `q ≤ p` on a set of finite measure**, by Hölder's inequality
`‖f‖_q ≤ μ(Ω)^{1/q − 1/p} ‖f‖_p`. -/
theorem isContinuousEmbedding_toLpₗ_of_le (hΩ : μ Ω ≠ ⊤) (hqp : q ≤ p)
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E))) :
    IsContinuousEmbedding (toLpₗ F b k p Ω μ h) := by
  have hfin : μ (Ω : Set E) ^ (1 / q.toReal - 1 / p.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by
      have hp0 : (0 : ℝ≥0∞) < p := zero_lt_one.trans_le Fact.out
      rcases eq_or_ne p ⊤ with rfl | hp
      · simp only [ENNReal.toReal_top, div_zero, sub_zero]
        positivity
      · have hq0 : 0 < q.toReal :=
          ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' (ne_top_of_le_ne_top hp hqp)
        have := ENNReal.toReal_mono hp hqp
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hq0 this) hΩ
  refine isContinuousEmbedding_toLpₗ_of_eLpNorm_le h
    (C := (μ (Ω : Set E) ^ (1 / q.toReal - 1 / p.toReal)).toReal) fun u ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin, mul_comm]
  calc eLpNorm (fn u) q (μ.restrict (Ω : Set E))
      ≤ eLpNorm (fn u) p (μ.restrict (Ω : Set E))
        * (μ.restrict (Ω : Set E)) Set.univ ^ (1 / q.toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp (memLp u).aestronglyMeasurable
    _ ≤ ENNReal.ofReal ‖u‖ * μ (Ω : Set E) ^ (1 / q.toReal - 1 / p.toReal) := by
        rw [Measure.restrict_apply_univ]
        exact mul_le_mul' (eLpNorm_fn_le_ofReal_norm u) le_rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- **A compact embedding `W^{k',r}(Ω) ⊂⊂ L^q(Ω)` pulls back along a continuous embedding
`T : W^{k,p}(Ω) → W^{k',r}(Ω)` preserving the function**: `W^{k,p}(Ω) ⊂⊂ L^q(Ω)`. -/
theorem isCompactEmbedding_toLpₗ_of_comp {k' : ℕ} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (T : SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k' r Ω μ)
    (hT : IsContinuousEmbedding T.toLinearMap)
    (hfn : ∀ u, fn (T u) =ᵐ[μ.restrict (Ω : Set E)] fn u)
    {h' : ∀ v : SobolevMultiIndex F b k' r Ω μ, MemLp (fn v) q (μ.restrict (Ω : Set E))}
    (hc : IsCompactEmbedding (toLpₗ F b k' r Ω μ h')) :
    ∃ h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E)),
      IsCompactEmbedding (toLpₗ F b k p Ω μ h) := by
  refine ⟨fun u ↦ (memLp_congr_ae (hfn u)).1 (h' (T u)), ?_⟩
  have := hT.comp_isCompactEmbedding hc
  convert this using 1
  refine LinearMap.ext fun u ↦ Lp.ext ((toLpₗ_coeFn _ u).trans ?_)
  exact (hfn u).symm.trans (toLpₗ_coeFn h' (T u)).symm

end SobolevMultiIndex

end Composition

/-! ### Rellich–Kondrachov at every order on an extension domain -/

section HigherOrder

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **`W^{1,p}(Ω) ⊂⊂ L^q(Ω)` for `N ≤ p < ∞`, `N ≥ 2`, `1 ≤ q < ∞`, on an extension domain (for
every exponent) of finite measure**: `W^{1,p}(Ω) ↪ W^{1,r}(Ω)` for an `r < N` with `r* > q`
and the case `r < N` of the Rellich–Kondrachov theorem
(`SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn`); the generalization of
`SobolevEuclidean.isCompactEmbedding_toLp_of_le` from `C¹` chart domains to extension
domains. -/
theorem SobolevEuclidean.isCompactEmbedding_toLp_of_le_of_isSobolevExtensionDomainAll
    {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hN : 2 ≤ N) (hp : (N : ℝ≥0) ≤ p) :
    ∃ h : ∀ u : SobolevEuclidean N 1 p Ω,
        MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      IsCompactEmbedding
        (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume h) := by
  obtain ⟨r, hr1, hrN, hr', hq2⟩ := NNReal.exists_lowerExponent hN
    (q := max q (N : ℝ≥0)) (le_max_right _ _)
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  have hqr : q < 2 * max q (N : ℝ≥0) := lt_of_le_of_lt (le_max_left _ _) hq2
  have hc := SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top
    (fun u ↦ (hΩ r).memLp_fn_of_le_sobolevConj hμ hrN hr' hqr.le ⟨u, Submodule.mem_top⟩)
    (SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn (hΩ r) hμ hrN hr' hqr)
  have hrp : (r : ℝ≥0∞) ≤ p := by exact_mod_cast hrN.le.trans hp
  exact isCompactEmbedding_toLpₗ_of_comp (toLowerExponentL ℝ _ 1 p r volume hμ hrp)
    (isContinuousEmbedding_toLowerExponentL hμ hrp) (fn_toLowerExponentL hμ hrp) hc

/-- **`W^{1,p}(Ω) ⊂⊂ C(K)` for `N < p < ∞` and a compact `K ⊇ Ω`, on an extension domain**, along
`SobolevEuclidean.toContinuousMapL`: the generalization of
`SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt` from `C¹` chart domains to
extension domains (Arzelà–Ascoli, `HasSobolevExtensionOn.isCompactEmbedding_toContinuousMapOnL`). -/
theorem SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_isSobolevExtensionDomain
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N p Ω) (hp : (N : ℝ≥0) < p)
    {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    IsCompactEmbedding (SobolevEuclidean.toContinuousMapL hΩ hp K).toLinearMap := by
  have hc := hΩ.isCompactEmbedding_toContinuousMapOnL hp hK
  have hι : IsContinuousEmbedding ((LinearMap.id (R := ℝ)).codRestrict
      (⊤ : Submodule ℝ (SobolevEuclidean N 1 p Ω)) fun _ ↦ Submodule.mem_top) :=
    ⟨fun u v huv ↦ by simpa using congrArg Subtype.val huv, 1, fun u ↦ by simp⟩
  exact hι.comp_isCompactEmbedding hc

/-- **Rellich–Kondrachov at order `k + 1`, the case `k + 1 < N/p`**: on an extension domain (for
every exponent) of finite measure, `1 ≤ p`, `k + 1 < N/p`, `1/p* = 1/p − (k+1)/N` and
`1 ≤ q < p*`, the inclusion `W^{k+1,p}(Ω) ⊂ L^q(Ω)` is compact (Atkinson–Han, *Theoretical
Numerical Analysis*, Theorem 7.3.8 (a), the case `k ≥ 1` on the book's Lipschitz domain being
an extension domain): `W^{k+1,p}(Ω) ↪ W^{1,r}(Ω)` with `1/r = 1/p − k/N`, and `W^{1,r}(Ω) ⊂⊂ L^q(Ω)`
for `q < r* = p*`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_lt (k : ℕ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hk : ((k + 1 : ℕ) : ℝ) < N / p)
    {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (k + 1 : ℕ) / N) (hq : q < p') :
    ∃ h : ∀ u : SobolevEuclidean N (k + 1) p Ω,
        MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      IsCompactEmbedding
        (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume h) := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hN0 : (0 : ℝ) < N :=
    (div_pos_iff_of_pos_right hp0).1 (lt_of_le_of_lt (Nat.cast_nonneg _) hk)
  push_cast at hk
  have hk' : ((k : ℝ) + 1) / N < (p : ℝ)⁻¹ := by
    rw [div_lt_iff₀ hN0, inv_mul_eq_div]
    exact hk
  -- the intermediate exponent `1/r = 1/p − k/N`
  have hrinv_pos : (0 : ℝ) < (p : ℝ)⁻¹ - k / N := by
    have : (k : ℝ) / N < ((k : ℝ) + 1) / N :=
      div_lt_div_of_pos_right (by linarith) hN0
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ) = ((p : ℝ)⁻¹ - k / N)⁻¹ :=
    ⟨⟨_, inv_nonneg.2 hrinv_pos.le⟩, rfl⟩
  have hrinv : (r : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / N := by rw [hr, inv_inv]
  have hr0 : (0 : ℝ) < r := by rw [hr]; exact inv_pos.2 hrinv_pos
  have hpr : p ≤ r := by
    rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hr0 hp0, hrinv]
    exact sub_le_self _ (by positivity)
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
  have hN : 2 ≤ N ∨ 1 < p := by
    left
    have h1 : (1 : ℝ) < N / p := lt_of_le_of_lt (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hk
    have h2 : (p : ℝ) < N := by rwa [lt_div_iff₀ hp0, one_mul] at h1
    have h3 : (1 : ℝ) < N := lt_of_le_of_lt (by exact_mod_cast hp1) h2
    exact_mod_cast h3
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_orderOne k hΩ hN hpr hrinv.ge
  have hTemb : IsContinuousEmbedding T.toLinearMap :=
    ⟨fun u v huv ↦ ext_of_fn_ae_eq ((hT u).symm.trans (huv ▸ hT v)), _, T.le_opNorm⟩
  -- `r < N` and `r* = p*`
  have hrN : r < N := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_natCast, ← inv_lt_inv₀ hN0 hr0, hrinv]
    have : (k : ℝ) / N + (N : ℝ)⁻¹ = ((k : ℝ) + 1) / N := by
      rw [add_div, one_div]
    linarith
  have hp'r : (p' : ℝ)⁻¹ = (r : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
    rw [hp', hrinv]
    push_cast
    ring
  exact isCompactEmbedding_toLpₗ_of_comp T hTemb hT
    (SobolevMultiIndex.isCompactEmbedding_toLpₗ_of_top
      (fun u ↦ (hΩ r).memLp_fn_of_le_sobolevConj hμ hrN hp'r hq.le ⟨u, Submodule.mem_top⟩)
      (SobolevEuclidean.isCompactEmbedding_toLp_of_hasSobolevExtensionOn (hΩ r) hμ hrN hp'r hq))

/-- **Rellich–Kondrachov at order `k + 1`, the case `k + 1 = N/p`**: on an extension domain (for
every exponent) of finite measure with `N ≥ 2`, `1 ≤ p`, `k + 1 = N/p` and `1 ≤ q < ∞`, the
inclusion `W^{k+1,p}(Ω) ⊂ L^q(Ω)` is compact (the compact form of Atkinson–Han, *Theoretical
Numerical Analysis*, Theorem 7.3.8 (b)): `W^{k+1,p}(Ω) ↪ W^{1,N}(Ω)` and
`SobolevEuclidean.isCompactEmbedding_toLp_of_le_of_isSobolevExtensionDomainAll`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_eq (k : ℕ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hN : 2 ≤ N)
    (hk : ((k + 1 : ℕ) : ℝ) = N / p) :
    ∃ h : ∀ u : SobolevEuclidean N (k + 1) p Ω,
        MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      IsCompactEmbedding
        (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume h) := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have : Fact (1 ≤ ((N : ℝ≥0) : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ N)⟩
  have hpinv : (p : ℝ)⁻¹ = ((k + 1 : ℕ) : ℝ) / N := by
    rw [hk, div_div, mul_comm, ← div_div, div_self hN0.ne', one_div]
  have hpN : p ≤ (N : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast, ← inv_le_inv₀ hN0 hp0, hpinv, ← one_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_pos k) hN0.le
  have hrinv : (p : ℝ)⁻¹ - k / N ≤ ((N : ℝ≥0) : ℝ)⁻¹ := by
    rw [hpinv, NNReal.coe_natCast]
    refine le_of_eq ?_
    push_cast
    ring
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_orderOne k hΩ (Or.inl hN) hpN
    hrinv
  have hTemb : IsContinuousEmbedding T.toLinearMap :=
    ⟨fun u v huv ↦ ext_of_fn_ae_eq ((hT u).symm.trans (huv ▸ hT v)), _, T.le_opNorm⟩
  obtain ⟨h', hc⟩ :=
    SobolevEuclidean.isCompactEmbedding_toLp_of_le_of_isSobolevExtensionDomainAll (q := q) hΩ hμ
      hN le_rfl
  exact isCompactEmbedding_toLpₗ_of_comp T hTemb hT hc

end HigherOrder

/-! ### `W^{k,p}(Ω) ⊂⊂ C(K)` at every order, and `W^{k,p}(Ω) ⊂⊂ W^{l,p}(Ω)` for `l < k` -/

section HigherOrderContinuous

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **`W^{k+1,p}(Ω) ⊂⊂ C(K)` for `k + 1 > N/p` and a compact `K ⊇ Ω`, on an extension domain
(for every exponent)**, `1 ≤ p < ∞` and `N ≥ 2` or `p > 1`: there is a bounded linear
`ι : W^{k+1,p}(Ω) → C(K, ℝ)` sending `u` to the restriction of a continuous representative
of `u`, which is a compact embedding (Atkinson–Han, *Theoretical Numerical Analysis*,
Theorem 7.3.8 (c) with `β = 0` and `k − [N/p] − 1` replaced by `0`, and Example 7.4.2 at
`p = 2`): `W^{k+1,p}(Ω) ↪ W^{1,r}(Ω)` for the `r > N` of `NNReal.exists_morrey_exponent`, then
`SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_isSobolevExtensionDomain`. -/
theorem SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order (k : ℕ) {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hk : (N : ℝ) / p < (k + 1 : ℕ)) {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    ∃ ι : SobolevEuclidean N (k + 1) p Ω →L[ℝ] C(K, ℝ),
      (∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x : K, ι u x = ũ x) ∧
      IsCompactEmbedding ι.toLinearMap := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ≥0) < p := zero_lt_one.trans_le hp1
  obtain ⟨r, hpr, hNr, hr, -⟩ := NNReal.exists_morrey_exponent (N := N) k hp0 hk
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_orderOne k hΩ hN hpr hr
  have hTemb : IsContinuousEmbedding T.toLinearMap :=
    ⟨fun u v huv ↦ ext_of_fn_ae_eq ((hT u).symm.trans (huv ▸ hT v)), _, T.le_opNorm⟩
  refine ⟨(SobolevEuclidean.toContinuousMapL (hΩ r) hNr K).comp T, fun u ↦ ?_,
    hTemb.comp_isCompactEmbedding
      (SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_isSobolevExtensionDomain (hΩ r)
        hNr hK)⟩
  refine ⟨_, (SobolevEuclidean.contRep hNr _).continuous,
    (hT u).symm.trans (SobolevEuclidean.fn_ae_eq_toContinuousMapL (hΩ r) hNr K (T u)),
    fun x ↦ rfl⟩

/-- **`W^{k,p}(Ω) ⊂⊂ W^{l,p}(Ω)` for `l < k` on an extension domain of finite measure**
(Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 7.3.9, for `1 ≤ p < ∞`): the
inclusion `SobolevMultiIndex.toLowerOrderL` is a compact embedding, being
`W^{k,p}(Ω) ⊂⊂ W^{k−1,p}(Ω) ↪ W^{l,p}(Ω)`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {k l : ℕ} (hlk : l < k) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω
      volume hlk.le).toLinearMap := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc := SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain hΩ hμ k
  have hl : l ≤ k := Nat.lt_succ_iff.1 hlk
  have hι := isContinuousEmbedding_toLowerOrderL (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := (p : ℝ≥0∞)) (Ω := Ω) (μ := volume) hl
  have := hc.comp_isContinuousEmbedding hι
  convert this using 1
  exact LinearMap.ext fun u ↦ rfl

end HigherOrderContinuous

/-! ### Rellich–Kondrachov at `p = ∞`: `W^{1,∞}(Ω) ⊂⊂ L^∞(Ω)` by Arzelà–Ascoli -/

section RellichTop

open SobolevMultiIndex

/-- **The almost-everywhere bound from the `L^∞` norm**: if `‖f‖_{L^∞(μ)} ≤ L` then `‖f x‖ ≤ L`
almost everywhere. -/
theorem MeasureTheory.ae_norm_le_of_eLpNorm_top_le {α G : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup G] {f : α → G} (hf : AEStronglyMeasurable f μ) {L : ℝ}
    (hL : 0 ≤ L) (h : eLpNorm f ⊤ μ ≤ ENNReal.ofReal L) : ∀ᵐ x ∂μ, ‖f x‖ ≤ L := by
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [← eLpNorm_exponent_top hf] at hx
  rw [← ENNReal.ofReal_le_ofReal_iff hL, ofReal_norm]
  exact hx.trans h

/-- **The `L^∞` distance from a uniform bound on representatives**: if `g₁ = v₁` and `g₂ = v₂`
almost everywhere and `‖v₁ x − v₂ x‖ ≤ D` almost everywhere, then `dist g₁ g₂ ≤ D` in `L^∞`. -/
theorem MeasureTheory.Lp.dist_le_of_ae_eq_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g₁ g₂ : Lp ℝ ⊤ μ) {v₁ v₂ : α → ℝ} (h₁ : g₁ =ᵐ[μ] v₁) (h₂ : g₂ =ᵐ[μ] v₂) {D : ℝ}
    (hD : 0 ≤ D) (h : ∀ᵐ x ∂μ, ‖v₁ x - v₂ x‖ ≤ D) : dist g₁ g₂ ≤ D := by
  rw [Lp.dist_def]
  have hae : ∀ᵐ x ∂μ, ‖(⇑g₁ - ⇑g₂) x‖ ≤ D := by
    filter_upwards [h₁, h₂, h] with x hx₁ hx₂ hx
    rw [Pi.sub_apply, hx₁, hx₂]
    exact hx
  have := eLpNorm_le_of_ae_bound (p := ⊤)
    ((Lp.aestronglyMeasurable g₁).sub (Lp.aestronglyMeasurable g₂)) hae
  simp only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul] at this
  calc (eLpNorm (⇑g₁ - ⇑g₂) ⊤ μ).toReal ≤ (ENNReal.ofReal D).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    _ = D := ENNReal.toReal_ofReal hD

/-- **Arzelà–Ascoli for a uniformly bounded, uniformly Lipschitz sequence**, in the form of a
uniformly Cauchy subsequence on a compact set: if `‖v_n x‖ ≤ R` and every `v_n` is `L`-Lipschitz,
then along a subsequence `v_{φ n}` is uniformly Cauchy on the compact `K`
(`ContinuousMap.isCompact_closure_of_forall_norm_le` on the restrictions to `K`). -/
theorem exists_strictMono_forall_dist_lt_of_lipschitzWith {E : Type*}
    [PseudoMetricSpace E] {K : Set E} (hK : IsCompact K) (v : ℕ → E → ℝ) {L : ℝ≥0} {R : ℝ}
    (hvl : ∀ n, LipschitzWith L (v n)) (hvb : ∀ n x, ‖v n x‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ε > 0, ∃ n₀, ∀ m ≥ n₀, ∀ n ≥ n₀, ∀ x ∈ K,
      dist (v (φ m) x) (v (φ n) x) < ε := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨f, hf⟩ : ∃ f : ℕ → C(K, ℝ), ∀ n x, f n x = v n x :=
    ⟨fun n ↦ ⟨fun x ↦ v n x, (hvl n).continuous.comp continuous_subtype_val⟩, fun _ _ ↦ rfl⟩
  have hcomp : IsCompact (closure (Set.range f)) := by
    refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := R) ?_ ?_
    · rintro _ ⟨n, rfl⟩ x
      rw [hf]
      exact hvb n x
    · refine Metric.equicontinuous_of_continuity_modulus (fun d ↦ (L : ℝ) * d) ?_ _ ?_
      · have : Tendsto (fun d : ℝ ↦ (L : ℝ) * d) (𝓝 0) (𝓝 ((L : ℝ) * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rwa [mul_zero] at this
      · rintro x y ⟨_, ⟨n, rfl⟩⟩
        simp only [hf, Subtype.dist_eq]
        exact (hvl n).dist_le_mul x y
  obtain ⟨g, -, φ, hφ, hlim⟩ :=
    hcomp.tendsto_subseq (x := f) fun n ↦ subset_closure (Set.mem_range_self n)
  refine ⟨φ, hφ, fun ε hε ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
  refine ⟨n₀, fun m hm n hn x hx ↦ ?_⟩
  have := ContinuousMap.dist_apply_le_dist (f := f (φ m)) (g := f (φ n)) ⟨x, hx⟩
  rw [hf, hf] at this
  exact this.trans_lt (hn₀ m hm n hn)

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The Lipschitz representative of an element of `W^{1,∞}(ℝ^N)`**, with the constants read
off the norm: for `U ∈ W^{1,∞}(ℝ^N)` with `‖U‖ ≤ R` there is `v` with `U = v` almost everywhere,
`v` Lipschitz with constant `C_N R` (`C_N` the constant of
`SobolevMultiIndex.exists_hasWeakFDerivOn_fn`, depending on `N` only) and `‖v x‖ ≤ R` everywhere.
The Lipschitz representative is Brezis's Remark 7 on the convex set `ℝ^N`
(`HasWeakFDerivOn.exists_lipschitzOnWith_ae_eq_of_convex`); the bound holds almost everywhere
by the `L^∞` norm and everywhere by continuity, Lebesgue measure being positive on open sets. -/
theorem SobolevEuclidean.exists_lipschitzWith_ae_eq_top_of_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 0 ≤ R → ∀ U : SobolevEuclidean N 1 ⊤ ⊤, ‖U‖ ≤ R →
      ∃ v : EuclideanSpace ℝ (Fin N) → ℝ, fn U =ᵐ[volume] v ∧
        LipschitzWith (Real.toNNReal (C * R)) v ∧ ∀ x, ‖v x‖ ≤ R := by
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card (Fin N) •
      ‖(EuclideanSpace.basisFun (Fin N) ℝ).toBasis.equivFunL.toContinuousLinearMap‖ := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  refine ⟨Cb * N, by positivity, fun R hR U hU ↦ ?_⟩
  obtain ⟨w, hw, hwp, -, hwn⟩ := exists_hasWeakFDerivOn_fn U
  -- the almost everywhere bound of the weak derivative
  have hwae : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
      Set (EuclideanSpace ℝ (Fin N))), ‖w x‖ ≤ Cb * N * R := by
    have h1 : ∀ i : Fin N, eLpNorm (weakDeriv U (MultiIndexLE.single i)) ⊤
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
          Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal R := fun i ↦ by
      rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ← Lp.norm_def]
      exact ENNReal.ofReal_le_ofReal ((norm_weakDeriv_le U _).trans hU)
    have hwn' : eLpNorm w ⊤ (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
        Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal Cb *
          ∑ i, eLpNorm (weakDeriv U (MultiIndexLE.single i)) ⊤
            (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
              Set (EuclideanSpace ℝ (Fin N)))) := by
      rw [hCb]; exact hwn
    refine MeasureTheory.ae_norm_le_of_eLpNorm_top_le hwp.aestronglyMeasurable (by positivity)
      (hwn'.trans ?_)
    calc ENNReal.ofReal Cb * ∑ i, eLpNorm (weakDeriv U (MultiIndexLE.single i)) ⊤
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
            Set (EuclideanSpace ℝ (Fin N))))
        ≤ ENNReal.ofReal Cb * ∑ _i : Fin N, ENNReal.ofReal R := by
          gcongr with i
          exact h1 i
      _ = ENNReal.ofReal (Cb * N * R) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCb0, ENNReal.ofReal_natCast]
          ring
  -- the Lipschitz representative
  have hconv : Convex ℝ ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
      Set (EuclideanSpace ℝ (Fin N))) := by
    rw [Opens.coe_top]; exact convex_univ
  obtain ⟨v, hv, hvl⟩ := hw.exists_lipschitzOnWith_ae_eq_of_convex hconv (by positivity) hwae
  rw [Opens.coe_top, lipschitzOnWith_univ] at hvl
  rw [Opens.coe_top, Measure.restrict_univ] at hv
  -- the bound, almost everywhere by the `L^∞` norm, everywhere by continuity
  have hvae : ∀ᵐ x ∂volume, ‖v x‖ ≤ R := by
    have h1 : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) :
        Set (EuclideanSpace ℝ (Fin N))), ‖fn U x‖ ≤
          ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ ⊤ volume U‖ :=
      MeasureTheory.Lp.ae_norm_le_norm_top
        (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ ⊤ volume U)
    have h2 := (ae_restrict_iff' (⊤ : Opens (EuclideanSpace ℝ (Fin N))).isOpen.measurableSet).1 h1
    filter_upwards [h2, hv] with x hx hvx
    rw [← hvx]
    exact (hx (by simp)).trans ((norm_fnL_apply_le U).trans hU)
  have hcl : IsClosed {x | ‖v x‖ ≤ R} :=
    isClosed_le (continuous_norm.comp hvl.continuous) continuous_const
  have hset : {x | ‖v x‖ ≤ R} = univ :=
    hcl.closure_eq.symm.trans (Measure.dense_of_ae hvae).closure_eq
  exact ⟨v, hv, hvl, fun x ↦ eq_univ_iff_forall.1 hset x⟩

/-- **`W^{1,∞}(Ω) ⊂⊂ L^∞(Ω)` on a bounded `W^{1,∞}`-extension domain**: the inclusion
`SobolevMultiIndex.fnL` is a compact embedding. For a bounded sequence `u_n`, the extensions
`P u_n ∈ W^{1,∞}(ℝ^N)` have Lipschitz representatives `v_n`, uniformly bounded and uniformly
Lipschitz (`SobolevEuclidean.exists_lipschitzWith_ae_eq_top_of_norm_le`); on the compact
`closure Ω` the Arzelà–Ascoli theorem gives a uniformly Cauchy subsequence
(`exists_strictMono_forall_dist_lt_of_lipschitzWith`), which is Cauchy in
`L^∞(Ω)` (`MeasureTheory.Lp.dist_le_of_ae_eq_top`), hence convergent. This is the case `p = ∞`
left out of `Numlib/Analysis/Sobolev/Compactness.lean` (Atkinson–Han, *Theoretical Numerical
Analysis*, Theorem 7.3.9 at `p = ∞`). -/
theorem SobolevEuclidean.isCompactEmbedding_fnL_top (hΩ : IsSobolevExtensionDomain N ⊤ Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    IsCompactEmbedding
      (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ Ω volume).toLinearMap := by
  refine IsCompactEmbedding.of_forall_exists_subseq_tendsto isContinuousEmbedding_fnL
    fun u hu ↦ ?_
  obtain ⟨M, hM⟩ := hu
  obtain ⟨P, hP⟩ := hΩ
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_lipschitzWith_ae_eq_top_of_norm_le (N := N)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- the extensions `P u_n`, bounded in `W^{1,∞}(ℝ^N)`, and their Lipschitz representatives
  have hrep : ∀ n, ∃ v : EuclideanSpace ℝ (Fin N) → ℝ,
      fn (u n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v ∧
      LipschitzWith (Real.toNNReal (C * (‖P‖ * M))) v ∧ ∀ x, ‖v x‖ ≤ ‖P‖ * M := fun n ↦ by
    have hUn : ‖P ⟨u n, Submodule.mem_top⟩‖ ≤ ‖P‖ * M :=
      (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _))
    obtain ⟨v, hv, hvl, hvb⟩ := hC (‖P‖ * M) (by positivity) _ hUn
    exact ⟨v, (hP ⟨u n, Submodule.mem_top⟩).symm.trans (ae_restrict_of_ae hv), hvl, hvb⟩
  choose v hv hvl hvb using hrep
  -- Arzelà–Ascoli on the compact `closure Ω`
  obtain ⟨φ, hφ, hφc⟩ := exists_strictMono_forall_dist_lt_of_lipschitzWith
    hb.isCompact_closure v hvl hvb
  -- the subsequence is Cauchy in `L^∞(Ω)`
  have hcauchy : CauchySeq fun n ↦
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ Ω volume (u (φ n)) := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨n₀, hn₀⟩ := hφc (ε / 2) (by positivity)
    refine ⟨n₀, fun m hm n hn ↦ ?_⟩
    refine (MeasureTheory.Lp.dist_le_of_ae_eq_top _ _ (hv (φ m)) (hv (φ n)) (D := ε / 2)
      (by positivity) ?_).trans_lt (by linarith)
    filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet] with x hx
    rw [← dist_eq_norm]
    exact (hn₀ m hm n hn x (subset_closure hx)).le
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨φ, w, hφ, hw⟩

end RellichTop

/-! ### Rellich–Kondrachov at `p = ∞` and every order: `W^{k,∞}(Ω) ⊂⊂ W^{l,∞}(Ω)`, `l < k` -/

section RellichTopHigher

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **`W^{k+1,∞}(Ω) ⊂⊂ W^{k,∞}(Ω)` on a bounded `W^{1,∞}`-extension domain**: the inclusion
`SobolevMultiIndex.toLowerOrderL` is a compact embedding. Induction on `k` from
`W^{1,∞}(Ω) ⊂⊂ L^∞(Ω)` (`SobolevEuclidean.isCompactEmbedding_fnL_top`), the step being
`SobolevMultiIndex.isCompactEmbedding_of_forall_weakDeriv_eq` exactly as in
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain` for `p < ∞`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top
    (hΩ : IsSobolevExtensionDomain N ⊤ Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (k : ℕ) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis ⊤ Ω
      volume (Nat.le_succ k)).toLinearMap := by
  induction k with
  | zero =>
    exact isCompactEmbedding_of_forall_weakDeriv_eq_fnL (weakDeriv_toLowerOrderL_zero)
      (isContinuousEmbedding_toLowerOrderL (Nat.zero_le 1))
      (SobolevEuclidean.isCompactEmbedding_fnL_top hΩ hb)
  | succ k ih =>
    exact isCompactEmbedding_of_forall_weakDeriv_eq (weakDeriv_toLowerOrderL (Nat.le_succ (k + 1)))
      (weakDeriv_toLowerOrderL (Nat.le_succ k))
      (weakDeriv_partialDerivL (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
        (p := ⊤) (Ω := Ω) (μ := volume))
      (norm_toLowerOrderL_apply_le _) (norm_partialDerivL_apply_le)
      (isContinuousEmbedding_toLowerOrderL (Nat.le_succ (k + 1))) ih

/-- **`W^{k,∞}(Ω) ⊂⊂ W^{l,∞}(Ω)` for `l < k` on a bounded `W^{1,∞}`-extension domain**
(Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 7.3.9 at `p = ∞`): the inclusion
`SobolevMultiIndex.toLowerOrderL` is a compact embedding, being
`W^{k,∞}(Ω) ⊂⊂ W^{k−1,∞}(Ω) ↪ W^{l,∞}(Ω)`; the counterpart of
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt` for `p < ∞`. -/
theorem SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt
    (hΩ : IsSobolevExtensionDomain N ⊤ Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) {k l : ℕ} (hlk : l < k) :
    IsCompactEmbedding (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis ⊤ Ω
      volume hlk.le).toLinearMap := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc := SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top hΩ hb k
  have hl : l ≤ k := Nat.lt_succ_iff.1 hlk
  have hι := isContinuousEmbedding_toLowerOrderL (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := ⊤) (Ω := Ω) (μ := volume) hl
  have := hc.comp_isContinuousEmbedding hι
  convert this using 1
  exact LinearMap.ext fun u ↦ rfl

end RellichTopHigher
