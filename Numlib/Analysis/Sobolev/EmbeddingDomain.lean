/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, beside the whole-space
inequalities of `Numlib/Analysis/Sobolev/Embedding.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.MetricSpace.Holder
import Numlib.Analysis.Sobolev.Embedding

/-!
# The Sobolev embeddings on a domain with an extension operator

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.3.B: the
embeddings of `W^{1,p}(Ω)` for an open set `Ω ⊆ ℝ^N` of class `C¹` with bounded boundary, or the
half space — Corollary 9.14 in its three cases `p < N`, `p = N`, `p > N`, with the Hölder
estimate and the continuous representative up to the boundary (`W^{1,p}(Ω) ⊂ C(Ω̄)`) for
`p > N`.

## Design

The book's standing hypothesis for §9.3.B is replaced by the abstract predicate
`HasSobolevExtensionOn S` of `Numlib/Analysis/Sobolev/Cutoff.lean` — a subspace `S` of
`W^{1,p}(Ω)` carrying a bounded extension operator `P : S → W^{1,p}(ℝ^N)` with `P u = u` on `Ω` —
and its instance `IsSobolevExtensionDomain N p Ω` (`S = ⊤`). Theorem 9.7
(`IsSobolevExtensionDomain.of_isContDiffChartDomain`, `Numlib/Analysis/Sobolev/Extension.lean`),
the half space (`IsSobolevExtensionDomain.upperHalfSpace`,
`Numlib/Analysis/Sobolev/Reflection.lean`) and the extension by zero on `W_0^{1,p}(Ω)` of an
arbitrary open set (Remark 20, `Zero.lean`) are the instances; this module does not import
`Extension.lean`. Every statement is "obtain `P`, apply the whole-space theorem of
`Numlib/Analysis/Sobolev/Embedding.lean` to `P u`, restrict"
(`HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le`), with a constant `C` that depends on `P`
and is therefore existential.

## Main results

* `SobolevMultiIndex.toLpₗOn`: the inclusion of a subspace `S ⊆ W^{k,p}(Ω)` into `L^q(Ω)`, the
  shape in which the results hold on `W_0^{1,p}(Ω)`, with `isContinuousEmbedding_toLpₗOn` and
  `isContinuousEmbedding_toLpₗ_of_eLpNorm_le` turning an `eLpNorm` bound into an
  `IsContinuousEmbedding`.
* `HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_le_of_le`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_lt`:
  **Corollary 9.14, case `p < N`**, `W^{1,p}(Ω) ↪ L^q(Ω)` for `p ≤ q ≤ p*`.
* `HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_eq_finrank`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_eq`:
  **Corollary 9.14, case `p = N`**, `W^{1,N}(Ω) ↪ L^q(Ω)` for `N ≤ q < ∞`, `N ≥ 2`.
* `HasSobolevExtensionOn.exists_forall_continuous_holderWith_ae_eq`,
  `SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_top_of_hasSobolevExtension_of_lt`:
  **Corollary 9.14, case `p > N`** (`N < p < ∞`): a representative continuous on all of `ℝ^N`,
  Hölder with exponent `1 − N/p` and constant `C ‖u‖`, bounded by `C ‖u‖`, so
  `W^{1,p}(Ω) ⊂ L^∞(Ω)` and `W^{1,p}(Ω) ⊂ C(Ω̄)`.
* `HasSobolevExtensionOn.toContinuousMapOnL`, `SobolevEuclidean.toContinuousMapL`: the trace
  `u ↦ ũ|_K` of the continuous representative on a compact `K ⊇ Ω` (typically `closure Ω`) as a
  bounded linear map into `C(K, ℝ)`, independent of the extension operator
  (`toContinuousMapOnL_apply_of_ae_eq`), injective, bounded and uniformly Hölder on the unit
  ball — the map the third case of Theorem 9.16 is about.

The higher-order Corollary 9.15, Remark 15 (the equivalent norm), Remark 16 (the unbounded
`W^{1,N}` function) and the chart structure of balls are not proved here.

## References

[brezis2011functional], §9.3.B: Corollary 9.14, footnote 15, Remark 20.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

/-! ### The inclusion of a subspace of `W^{k,p}(Ω)` into `L^q(Ω)` -/

section Inclusion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p q : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

variable (F b k p Ω μ) in
/-- **The inclusion of a subspace `S ⊆ W^{k,p}(Ω)` into `L^q(Ω)`**, given the membership of its
elements: `u ↦ fn u`. This is `SobolevMultiIndex.toLpₗ` for the subspace, the shape in which
[brezis2011functional] Remark 20 reads Corollary 9.14 on `W_0^{1,p}(Ω)`. -/
def toLpₗOn (S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ))
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E))) :
    S →ₗ[ℝ] Lp F q (μ.restrict (Ω : Set E)) where
  toFun u := (h u).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (fn_add _ _)
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (fn_smul c _)

/-- `SobolevMultiIndex.toLpₗOn S h u` is the function of `u`, almost everywhere on `Ω`. -/
theorem toLpₗOn_coeFn {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E)))
    (u : S) :
    toLpₗOn F b k p Ω μ S h u =ᵐ[μ.restrict (Ω : Set E)] fn (u : SobolevMultiIndex F b k p Ω μ) :=
  MemLp.coeFn_toLp (h u)

/-- The norm of `SobolevMultiIndex.toLpₗOn S h u` is the `L^q(Ω)` norm of the function. -/
theorem norm_toLpₗOn [Fact (1 ≤ q)] {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E)))
    (u : S) :
    ‖toLpₗOn F b k p Ω μ S h u‖
      = (eLpNorm (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E))).toReal :=
  Lp.norm_toLp _ (h u)

/-- The inclusion of a subspace into `L^q(Ω)` is injective. -/
theorem toLpₗOn_injective [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E))) :
    Function.Injective (toLpₗOn F b k p Ω μ S h) := fun u v huv ↦
  Subtype.ext <| ext_of_fn_ae_eq <| (toLpₗOn_coeFn h u).symm.trans <|
    (Lp.ext_iff.1 huv).trans (toLpₗOn_coeFn h v)

/-- **A bound `‖fn u‖_{L^q(Ω)} ≤ C ‖u‖` on a subspace makes its inclusion into `L^q(Ω)` a
continuous embedding.** -/
theorem isContinuousEmbedding_toLpₗOn [Fact (1 ≤ p)] [Fact (1 ≤ q)] [FiniteDimensional ℝ E]
    [BorelSpace E] [CompleteSpace F] {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E)))
    {C : ℝ} (hC : ∀ u : S, eLpNorm (fn (u : SobolevMultiIndex F b k p Ω μ)) q
      (μ.restrict (Ω : Set E)) ≤ ENNReal.ofReal (C * ‖u‖)) :
    IsContinuousEmbedding (toLpₗOn F b k p Ω μ S h) :=
  ⟨toLpₗOn_injective h, max C 0, fun u ↦ by
    rw [norm_toLpₗOn]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC u)).trans ?_
    rw [ENNReal.toReal_ofReal']
    exact (max_le_max_right 0 (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))).trans
      (max_eq_left (by positivity)).le⟩

/-- **A bound `‖fn u‖_{L^q(Ω)} ≤ C ‖u‖` makes the inclusion `W^{k,p}(Ω) → L^q(Ω)` a continuous
embedding**, the `eLpNorm` form of `SobolevMultiIndex.isContinuousEmbedding_toLpₗ`. -/
theorem isContinuousEmbedding_toLpₗ_of_eLpNorm_le [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E)))
    {C : ℝ} (hC : ∀ u : SobolevMultiIndex F b k p Ω μ,
      eLpNorm (fn u) q (μ.restrict (Ω : Set E)) ≤ ENNReal.ofReal (C * ‖u‖)) :
    IsContinuousEmbedding (toLpₗ F b k p Ω μ h) :=
  isContinuousEmbedding_toLpₗ h (C := max C 0) fun u ↦ by
    rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC u)).trans ?_
    rw [ENNReal.toReal_ofReal']
    exact (max_le_max_right 0 (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))).trans
      (max_eq_left (by positivity)).le

end SobolevMultiIndex

end Inclusion

/-! ### Corollary 9.14: the embeddings on an extension domain -/

section Transfer

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- The bound of an extension operator on `S`: `HasSobolevExtensionOn S` provides
`P : S →L W^{1,p}(ℝ^N)` with `P u = u` on `Ω` and `‖P u‖ ≤ ‖P‖ ‖u‖`. -/
theorem HasSobolevExtensionOn.exists_forall_norm_le (hS : HasSobolevExtensionOn S) :
    ∃ (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ), 0 ≤ C ∧ ∀ u : S,
      fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fn (u : SobolevEuclidean N 1 p Ω) ∧ ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨P, hP⟩ := hS
  exact ⟨P, ‖P‖, norm_nonneg _, fun u ↦ ⟨hP u, P.le_opNorm u⟩⟩

/-- **The transfer principle of [brezis2011functional] §9.3.B**: a bound `‖fn v‖_{L^q(ℝ^N)} ≤ K ‖v‖`
on `W^{1,p}(ℝ^N)` gives `‖fn u‖_{L^q(Ω)} ≤ K C ‖u‖` on a subspace `S` of `W^{1,p}(Ω)` with an
extension operator of norm `C`, since `fn u = fn (P u)` on `Ω`. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le (hS : HasSobolevExtensionOn S)
    {q : ℝ≥0∞} {K : ℝ} (hK : ∀ v : SobolevEuclidean N 1 p ⊤,
      eLpNorm (fn v) q volume ≤ ENNReal.ofReal (K * ‖v‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) := by
  obtain ⟨P, C, hC0, hP⟩ := hS.exists_forall_norm_le
  refine ⟨max K 0 * C, by positivity, fun u ↦ ?_⟩
  rw [← eLpNorm_congr_ae (hP u).1]
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ((hK (P u)).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  calc K * ‖P u‖ ≤ max K 0 * ‖P u‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max K 0 * (C * ‖u‖) := mul_le_mul_of_nonneg_left (hP u).2 (le_max_right _ _)
    _ = max K 0 * C * ‖u‖ := by ring

end Transfer

section Domain

open SobolevMultiIndex
open scoped BoundedContinuousFunction

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-! #### The case `p < N` -/

/-- **Corollary 9.14, case `p < N`, on a subspace with an extension operator, the bound**: for
`HasSobolevExtensionOn S`, `1 ≤ p < N`, `1/p* = 1/p − 1/N` and `p ≤ q ≤ p*`, there is `C`
with `‖fn u‖_{L^q(Ω)} ≤ C ‖u‖` for all `u ∈ S`. [brezis2011functional] Corollary 9.14. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le_of_le_of_le
    (hS : HasSobolevExtensionOn S) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) :=
  hS.exists_forall_eLpNorm_fn_le fun v ↦
    SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' v

/-- **Corollary 9.14, case `p < N`, on a subspace, the membership**: `fn u ∈ L^q(Ω)`. -/
theorem HasSobolevExtensionOn.memLp_fn_of_le_of_le (hS : HasSobolevExtensionOn S) {p' : ℝ≥0}
    (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_le_of_le hpN hp' hpq hqp'
  exact memLp_iff.2 ((hC u).trans_lt ENNReal.ofReal_lt_top)

/-- **Corollary 9.14, case `p < N`, on a subspace with an extension operator**: `S ↪ L^q(Ω)`
with continuous injection for `p ≤ q ≤ p*`, along `SobolevMultiIndex.toLpₗOn`.
[brezis2011functional] Corollary 9.14 and Remark 20. -/
theorem HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_le_of_le [Fact (1 ≤ (q : ℝ≥0∞))]
    (hS : HasSobolevExtensionOn S) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_of_le_of_le hpN hp' hpq hqp')) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_le_of_le hpN hp' hpq hqp'
  exact isContinuousEmbedding_toLpₗOn _ hC

/-- **Corollary 9.14, case `p < N`, the membership** on an extension domain: `fn u ∈ L^q(Ω)`
for every `u ∈ W^{1,p}(Ω)` and `p ≤ q ≤ p*`. -/
theorem SobolevEuclidean.memLp_fn_of_isSobolevExtensionDomain_of_le_of_le
    (hΩ : IsSobolevExtensionDomain N p Ω) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p')
    (u : SobolevEuclidean N 1 p Ω) :
    MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hΩ.memLp_fn_of_le_of_le hpN hp' hpq hqp' ⟨u, Submodule.mem_top⟩

/-- **Corollary 9.14, case `p < N`**: for an extension domain `Ω` (a `C¹` open set with bounded
boundary, or the half space), `1 ≤ p < N`, `1/p* = 1/p − 1/N` and `p ≤ q ≤ p*`,
`W^{1,p}(Ω) ↪ L^q(Ω)` with continuous injection, along `SobolevMultiIndex.toLpₗ`.
[brezis2011functional] Corollary 9.14, the first line, with the range of `q` of
Corollary 9.10. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_lt
    [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N p Ω) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclidean.memLp_fn_of_isSobolevExtensionDomain_of_le_of_le hΩ hpN hp' hpq hqp')) := by
  obtain ⟨C, -, hC⟩ := hΩ.exists_forall_eLpNorm_fn_le_of_le_of_le hpN hp' hpq hqp'
  exact isContinuousEmbedding_toLpₗ_of_eLpNorm_le _ fun u ↦ by
    simpa using hC ⟨u, Submodule.mem_top⟩

/-! #### The case `p = N` -/

/-- **Corollary 9.14, case `p = N`, on a subspace with an extension operator, the bound**: for
`N ≥ 2`, `HasSobolevExtensionOn S` with `S ⊆ W^{1,N}(Ω)`, and `N ≤ q < ∞`, there is `C` with
`‖fn u‖_{L^q(Ω)} ≤ C ‖u‖` for all `u ∈ S`. [brezis2011functional] Corollary 9.14. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    {S : Submodule ℝ (SobolevEuclidean N 1 N Ω)} (hS : HasSobolevExtensionOn S) (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 N Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  refine hS.exists_forall_eLpNorm_fn_le (K := K.toReal) fun v ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
  exact hKu v

/-- **Corollary 9.14, case `p = N`, on a subspace, the membership**: `fn u ∈ L^q(Ω)`. -/
theorem HasSobolevExtensionOn.memLp_fn_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    {S : Submodule ℝ (SobolevEuclidean N 1 N Ω)} (hS : HasSobolevExtensionOn S) (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 N Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  exact memLp_iff.2 ((hC u).trans_lt ENNReal.ofReal_lt_top)

/-- **Corollary 9.14, case `p = N`, on a subspace with an extension operator**: `S ↪ L^q(Ω)`
with continuous injection for `N ≤ q < ∞`. [brezis2011functional] Corollary 9.14 and Remark 20. -/
theorem HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    [Fact (1 ≤ (q : ℝ≥0∞))] {S : Submodule ℝ (SobolevEuclidean N 1 N Ω)}
    (hS : HasSobolevExtensionOn S) (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N Ω volume S
      (hS.memLp_fn_of_eq_finrank hN hq)) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  exact isContinuousEmbedding_toLpₗOn _ hC

/-- **Corollary 9.14, case `p = N`, the membership** on an extension domain. -/
theorem SobolevEuclidean.memLp_fn_of_isSobolevExtensionDomain_of_eq_finrank
    [Fact (1 ≤ (N : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N N Ω) (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) (u : SobolevEuclidean N 1 N Ω) :
    MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hΩ.memLp_fn_of_eq_finrank hN hq ⟨u, Submodule.mem_top⟩

/-- **Corollary 9.14, case `p = N`**: for an extension domain `Ω`, `N ≥ 2` and `N ≤ q < ∞`,
`W^{1,N}(Ω) ↪ L^q(Ω)` with continuous injection. [brezis2011functional] Corollary 9.14, the
second line. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_eq
    [Fact (1 ≤ (N : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N N Ω)
    (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N Ω volume
      (SobolevEuclidean.memLp_fn_of_isSobolevExtensionDomain_of_eq_finrank hΩ hN hq)) := by
  obtain ⟨C, -, hC⟩ := hΩ.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  exact isContinuousEmbedding_toLpₗ_of_eLpNorm_le _ fun u ↦ by
    simpa using hC ⟨u, Submodule.mem_top⟩

/-! #### The case `p > N`: the continuous representative up to the boundary -/

/-- **Corollary 9.14, case `p > N`, on a subspace with an extension operator**: for
`HasSobolevExtensionOn S` and `N < p < ∞` there is `C = C(Ω, p, N)` such that every `u ∈ S` has
a representative `ũ`, continuous on all of `ℝ^N` (so on `Ω̄`), equal to `fn u` almost everywhere
on `Ω`, Hölder continuous of exponent `1 − N/p` with constant `C ‖u‖` (the inequality
`|u(x) − u(y)| ≤ C ‖u‖_{W^{1,p}} |x − y|^α`), and bounded by `C ‖u‖` everywhere
(`W^{1,p}(Ω) ⊂ L^∞(Ω)`). The representative is Morrey's for `P u`, whose Hölder and sup bounds
are in terms of `‖P u‖ ≤ ‖P‖ ‖u‖`. [brezis2011functional] Corollary 9.14, the case `p > N`,
and Remark 20. -/
theorem HasSobolevExtensionOn.exists_forall_continuous_holderWith_ae_eq
    (hS : HasSobolevExtensionOn S) (hp : N < p) :
    ∃ C : ℝ≥0, ∀ u : S, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
      fn (u : SobolevEuclidean N 1 p Ω) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      HolderWith (C * ‖u‖₊) (1 - (N : ℝ≥0) / p) ũ ∧ ∀ x, ‖ũ x‖ ≤ C * ‖u‖ := by
  obtain ⟨P, C₀, hC₀, hP⟩ := hS.exists_forall_norm_le
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ≥0∞,
    K₁ = morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * N := ⟨_, rfl⟩
  have hK₁t : K₁ ≠ ⊤ := by
    rw [hK₁]
    exact ENNReal.mul_ne_top (morreyConst_ne_top _ _) (by simp)
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ,
    K₂ = (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal :=
    ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := hK₂ ▸ ENNReal.toReal_nonneg
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hα : ((1 - (N : ℝ≥0) / p : ℝ≥0) : ℝ) = 1 - N / (p : ℝ) := by
    rw [NNReal.coe_sub ((div_le_one (by exact_mod_cast hp0)).2 hp.le)]
    simp
  have hα0 : (0 : ℝ) ≤ 1 - N / (p : ℝ) := by
    rw [← hα]
    exact NNReal.coe_nonneg _
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, C = max (K₁.toNNReal * C₀.toNNReal) (K₂ * C₀).toNNReal := ⟨_, rfl⟩
  refine ⟨C, fun u ↦ ?_⟩
  obtain ⟨ũ, hũ⟩ : ∃ ũ : EuclideanSpace ℝ (Fin N) →ᵇ ℝ, ũ = SobolevEuclidean.contRep hp (P u) :=
    ⟨_, rfl⟩
  refine ⟨ũ, ũ.continuous, ?_, ?_, ?_⟩
  · rw [hũ]
    exact (hP u).1.symm.trans (ae_restrict_of_ae (SobolevEuclidean.fn_ae_eq_contRep hp (P u)))
  · intro x y
    have h1 : ‖ũ x - ũ y‖ₑ
        ≤ K₁ * ENNReal.ofReal (C₀ * ‖u‖) * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ))) := by
      rw [hũ, hK₁]
      refine (SobolevEuclidean.enorm_contRep_sub_le hp (P u) x y).trans ?_
      calc morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
            * ∑ i, ENNReal.ofReal ‖weakDeriv (P u) (MultiIndexLE.single i)‖
          ≤ morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
            * (N * ENNReal.ofReal ‖P u‖) :=
            mul_le_mul' le_rfl (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le (P u))
        _ ≤ morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
            * (N * ENNReal.ofReal (C₀ * ‖u‖)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hP u).2))
        _ = _ := by ring
    have h2 : K₁ * ENNReal.ofReal (C₀ * ‖u‖)
        = ((K₁.toNNReal * C₀.toNNReal * ‖u‖₊ : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hK₁t, mul_assoc, ← ENNReal.coe_mul,
        ← norm_toNNReal, ← Real.toNNReal_mul hC₀]
      rfl
    have h3 : ((K₁.toNNReal * C₀.toNNReal * ‖u‖₊ : ℝ≥0) : ℝ≥0∞) ≤ ((C * ‖u‖₊ : ℝ≥0) : ℝ≥0∞) := by
      rw [hC]
      exact ENNReal.coe_le_coe.2 (mul_le_mul' (le_max_left _ _) le_rfl)
    rw [edist_eq_enorm_sub, edist_eq_enorm_sub, ← ofReal_norm (x - y), hα,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα0]
    exact h1.trans (mul_le_mul' (h2.le.trans h3) le_rfl)
  · intro x
    have h1 : ‖ũ x‖ ≤ K₂ * ‖P u‖ := by
      rw [hũ, hK₂]
      exact SobolevEuclidean.norm_contRep_apply_le hp (P u) x
    have h2 : (K₂ * C₀).toNNReal ≤ C := hC ▸ le_max_right _ _
    calc ‖ũ x‖ ≤ K₂ * ‖P u‖ := h1
      _ ≤ K₂ * (C₀ * ‖u‖) := mul_le_mul_of_nonneg_left (hP u).2 hK₂0
      _ = (K₂ * C₀).toNNReal * ‖u‖ := by
          rw [Real.coe_toNNReal _ (by positivity)]
          ring
      _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (norm_nonneg _)

/-- **Corollary 9.14, case `p > N`, on a subspace, `L^∞` membership**: `fn u ∈ L^∞(Ω)`. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_top_le (hS : HasSobolevExtensionOn S)
    (hp : N < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) ⊤
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) := by
  obtain ⟨C, hC⟩ := hS.exists_forall_continuous_holderWith_ae_eq hp
  refine ⟨C, C.coe_nonneg, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, -, hb⟩ := hC u
  rw [eLpNorm_congr_ae hae]
  refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (C * ‖u‖))
    hc.aestronglyMeasurable.restrict (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hb x)

/-- **Corollary 9.14, case `p > N`, on a subspace, the membership**: `fn u ∈ L^∞(Ω)`. -/
theorem HasSobolevExtensionOn.memLp_fn_top_of_lt (hS : HasSobolevExtensionOn S) (hp : N < p)
    (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) ⊤
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_top_le hp
  exact memLp_iff.2 ((hC u).trans_lt ENNReal.ofReal_lt_top)

/-- **Corollary 9.14, case `p > N`, on a subspace with an extension operator**: `S ↪ L^∞(Ω)` with
continuous injection. [brezis2011functional] Corollary 9.14, the third line, and Remark 20. -/
theorem HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_top_of_lt (hS : HasSobolevExtensionOn S)
    (hp : N < p) :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_top_of_lt hp)) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_top_le hp
  exact isContinuousEmbedding_toLpₗOn _ hC

/-- **Corollary 9.14, case `p > N`**: for an extension domain `Ω` and `N < p < ∞` there is
`C = C(Ω, p, N)` such that every `u ∈ W^{1,p}(Ω)` has a representative `ũ` continuous on `ℝ^N`
(so `W^{1,p}(Ω) ⊂ C(Ω̄)`, footnote 15), equal to `fn u` almost everywhere on `Ω`, Hölder
continuous of exponent `1 − N/p` with constant `C ‖u‖`
(`|u(x) − u(y)| ≤ C ‖u‖_{W^{1,p}} |x − y|^α`), and bounded by `C ‖u‖` (`W^{1,p}(Ω) ⊂ L^∞(Ω)`).
[brezis2011functional] Corollary 9.14, the case `p > N`. -/
theorem SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p) :
    ∃ C : ℝ≥0, ∀ u : SobolevEuclidean N 1 p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      HolderWith (C * ‖u‖₊) (1 - (N : ℝ≥0) / p) ũ ∧ ∀ x, ‖ũ x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := hΩ.exists_forall_continuous_holderWith_ae_eq hp
  exact ⟨C, fun u ↦ hC ⟨u, Submodule.mem_top⟩⟩

/-- **Corollary 9.14, case `p > N`, the membership** on an extension domain: `fn u ∈ L^∞(Ω)`. -/
theorem SobolevEuclidean.memLp_fn_top_of_isSobolevExtensionDomain_of_lt
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p) (u : SobolevEuclidean N 1 p Ω) :
    MemLp (fn u) ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hΩ.memLp_fn_top_of_lt hp ⟨u, Submodule.mem_top⟩

/-- **Corollary 9.14, case `p > N`, as a continuous embedding**: `W^{1,p}(Ω) ↪ L^∞(Ω)` for an
extension domain `Ω` and `N < p < ∞`. [brezis2011functional] Corollary 9.14, the third line. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_top_of_hasSobolevExtension_of_lt
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclidean.memLp_fn_top_of_isSobolevExtensionDomain_of_lt hΩ hp)) := by
  obtain ⟨C, -, hC⟩ := hΩ.exists_forall_eLpNorm_fn_top_le hp
  exact isContinuousEmbedding_toLpₗ_of_eLpNorm_le _ fun u ↦ by
    simpa using hC ⟨u, Submodule.mem_top⟩

end Domain

/-! ### The trace of the continuous representative on a compact set, `W^{1,p}(Ω) ⊂ C(Ω̄)` -/

section ToContinuousMap

open scoped BoundedContinuousFunction

/-- **Restriction of a bounded continuous function to a compact set** `K`, as a bounded linear
map `(E →ᵇ ℝ) →L[ℝ] C(K, ℝ)` of norm at most one. -/
def BoundedContinuousFunction.restrictCLM {E : Type*} [TopologicalSpace E] (K : Set E)
    [CompactSpace K] : (E →ᵇ ℝ) →L[ℝ] C(K, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (f : C(E, ℝ)).restrict K
      map_add' := fun f g ↦ by ext x; simp
      map_smul' := fun c f ↦ by ext x; simp }
    1 fun f ↦ by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ f.norm_coe_le_norm x

/-- The restriction evaluates as the function. -/
@[simp]
theorem BoundedContinuousFunction.restrictCLM_apply {E : Type*} [TopologicalSpace E] (K : Set E)
    [CompactSpace K] (f : E →ᵇ ℝ) (x : K) : restrictCLM K f x = f x :=
  rfl

/-- Restriction does not increase the sup norm. -/
theorem BoundedContinuousFunction.norm_restrictCLM_apply_le {E : Type*} [TopologicalSpace E]
    (K : Set E) [CompactSpace K] (f : E →ᵇ ℝ) : ‖restrictCLM K f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ f.norm_coe_le_norm x

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- **`W^{1,p}(Ω) ⊂ C(Ω̄)` as a bounded linear map, `N < p < ∞`**: on a subspace `S` with an
extension operator `P`, the map `u ↦ (P u)~|_K`, the trace on a compact set `K ⊇ Ω` (typically
`K = closure Ω`) of the continuous representative of the extension. It does not depend on the
choice of `P` (`HasSobolevExtensionOn.toContinuousMapOnL_apply_of_ae_eq`): two continuous
functions equal to `fn u` almost everywhere on `Ω` agree on `Ω`, hence on `closure Ω`. This is
the map Theorem 9.16's third case is about ([brezis2011functional] Corollary 9.14, footnote 15,
and Theorem 9.16). -/
noncomputable def HasSobolevExtensionOn.toContinuousMapOnL (hS : HasSobolevExtensionOn S)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] : S →L[ℝ] C(K, ℝ) :=
  (BoundedContinuousFunction.restrictCLM K).comp
    ((SobolevEuclidean.toBoundedContinuousMapL N p hp).comp hS.choose)

/-- The value of the trace map at a point of `K`. -/
theorem HasSobolevExtensionOn.toContinuousMapOnL_apply (hS : HasSobolevExtensionOn S)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] (u : S) (x : K) :
    hS.toContinuousMapOnL hp K u x = SobolevEuclidean.contRep hp (hS.choose u) x :=
  rfl

/-- The trace map is the continuous representative: for `u ∈ S`, the function
`x ↦ hS.toContinuousMapOnL hp K u x` is `fn u` almost everywhere on `Ω ⊆ K`. -/
theorem HasSobolevExtensionOn.fn_ae_eq_toContinuousMapOnL (hS : HasSobolevExtensionOn S)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] (u : S) :
    fn (u : SobolevEuclidean N 1 p Ω) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevEuclidean.contRep hp (hS.choose u) :=
  (hS.choose_spec u).symm.trans
    (ae_restrict_of_ae (SobolevEuclidean.fn_ae_eq_contRep hp (hS.choose u)))

/-- **The trace map does not depend on the extension operator**: any continuous `g` equal to
`fn u` almost everywhere on `Ω` agrees with `hS.toContinuousMapOnL hp K u` on `K ∩ closure Ω`. -/
theorem HasSobolevExtensionOn.toContinuousMapOnL_apply_of_ae_eq (hS : HasSobolevExtensionOn S)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] (u : S)
    {g : EuclideanSpace ℝ (Fin N) → ℝ} (hg : Continuous g)
    (hu : fn (u : SobolevEuclidean N 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g)
    (x : K) (hx : (x : EuclideanSpace ℝ (Fin N)) ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    hS.toContinuousMapOnL hp K u x = g x := by
  rw [hS.toContinuousMapOnL_apply]
  have heq : EqOn (SobolevEuclidean.contRep hp (hS.choose u)) g
      (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
    Measure.eqOn_open_of_ae_eq ((hS.fn_ae_eq_toContinuousMapOnL hp K u).symm.trans hu) Ω.isOpen
      (SobolevEuclidean.contRep hp (hS.choose u)).continuous.continuousOn hg.continuousOn
  exact heq.of_subset_closure (SobolevEuclidean.contRep hp (hS.choose u)).continuous.continuousOn
    hg.continuousOn subset_closure subset_rfl hx

/-- **The trace map is bounded**: `‖u~|_K‖_∞ ≤ C ‖u‖`, with `C` depending on `S`, `p`, `N`. -/
theorem HasSobolevExtensionOn.exists_forall_norm_toContinuousMapOnL_le
    (hS : HasSobolevExtensionOn S) (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N)))
    [CompactSpace K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, ‖hS.toContinuousMapOnL hp K u‖ ≤ C * ‖u‖ := by
  refine ⟨‖hS.toContinuousMapOnL hp K‖, norm_nonneg _, fun u ↦ ?_⟩
  exact (hS.toContinuousMapOnL hp K).le_opNorm u

/-- **The trace map is injective when `K ⊇ Ω`**: an element of `S` whose continuous
representative vanishes on `K ⊇ Ω` vanishes almost everywhere on `Ω`. -/
theorem HasSobolevExtensionOn.toContinuousMapOnL_injective (hS : HasSobolevExtensionOn S)
    (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    Function.Injective (hS.toContinuousMapOnL hp K) := by
  intro u v huv
  refine Subtype.ext (ext_of_fn_ae_eq ?_)
  refine (hS.fn_ae_eq_toContinuousMapOnL hp K u).trans
    (Filter.EventuallyEq.trans ?_ (hS.fn_ae_eq_toContinuousMapOnL hp K v).symm)
  refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx ↦ ?_
  have := congrArg (fun f : C(K, ℝ) ↦ f ⟨x, hK hx⟩) huv
  simpa [HasSobolevExtensionOn.toContinuousMapOnL_apply] using this

/-- **The trace map is uniformly Hölder on the unit ball**: there is `C` with
`‖u~ x − u~ y‖ ≤ C ‖u‖ ‖x − y‖^{1 − N/p}` for `x, y ∈ K` — the equicontinuity that Arzelà–Ascoli
needs in the third case of [brezis2011functional] Theorem 9.16. -/
theorem HasSobolevExtensionOn.exists_forall_norm_toContinuousMapOnL_sub_le
    (hS : HasSobolevExtensionOn S) (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N)))
    [CompactSpace K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : S) (x y : K), ‖hS.toContinuousMapOnL hp K u x
      - hS.toContinuousMapOnL hp K u y‖ ≤ C * ‖u‖ * ‖(x : EuclideanSpace ℝ (Fin N)) - y‖
        ^ (1 - N / (p : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = ‖hS.choose‖ := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := hC₀ ▸ norm_nonneg _
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ≥0∞,
    K₁ = morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * N := ⟨_, rfl⟩
  have hK₁t : K₁ ≠ ⊤ := by
    rw [hK₁]
    exact ENNReal.mul_ne_top (morreyConst_ne_top _ _) (by simp)
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hα0 : (0 : ℝ) ≤ 1 - N / (p : ℝ) := sub_nonneg.2 ((div_le_one hp0).2 hp.le)
  refine ⟨K₁.toReal * C₀, by positivity, fun u x y ↦ ?_⟩
  simp only [HasSobolevExtensionOn.toContinuousMapOnL_apply]
  have h1 : ‖SobolevEuclidean.contRep hp (hS.choose u) x
      - SobolevEuclidean.contRep hp (hS.choose u) y‖ₑ
      ≤ K₁ * ENNReal.ofReal ‖(hS.choose u : SobolevEuclidean N 1 p ⊤)‖
        * ENNReal.ofReal (‖(x : EuclideanSpace ℝ (Fin N)) - y‖ ^ (1 - N / (p : ℝ))) := by
    rw [hK₁]
    refine (SobolevEuclidean.enorm_contRep_sub_le hp (hS.choose u) x y).trans ?_
    calc morreyConst volume p * ENNReal.ofReal (‖(x : EuclideanSpace ℝ (Fin N)) - y‖
            ^ (1 - N / (p : ℝ)))
          * ∑ i, ENNReal.ofReal ‖weakDeriv (hS.choose u) (MultiIndexLE.single i)‖
        ≤ morreyConst volume p * ENNReal.ofReal (‖(x : EuclideanSpace ℝ (Fin N)) - y‖
            ^ (1 - N / (p : ℝ)))
            * (N * ENNReal.ofReal ‖(hS.choose u : SobolevEuclidean N 1 p ⊤)‖) :=
          mul_le_mul' le_rfl (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le _)
      _ = _ := by ring
  have h2 : ‖(hS.choose u : SobolevEuclidean N 1 p ⊤)‖ ≤ C₀ * ‖u‖ := by
    rw [hC₀]
    exact hS.choose.le_opNorm u
  rw [← toReal_enorm]
  refine (ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK₁t ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
    h1).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal (by positivity)]
  calc K₁.toReal * ‖(hS.choose u : SobolevEuclidean N 1 p ⊤)‖
        * ‖(x : EuclideanSpace ℝ (Fin N)) - y‖ ^ (1 - N / (p : ℝ))
      ≤ K₁.toReal * (C₀ * ‖u‖) * ‖(x : EuclideanSpace ℝ (Fin N)) - y‖ ^ (1 - N / (p : ℝ)) := by
        gcongr
    _ = K₁.toReal * C₀ * ‖u‖ * ‖(x : EuclideanSpace ℝ (Fin N)) - y‖ ^ (1 - N / (p : ℝ)) := by
        ring

/-- **`W^{1,p}(Ω) ⊂ C(Ω̄)` as a bounded linear map on the whole space `W^{1,p}(Ω)`** of an
extension domain, `N < p < ∞`: `HasSobolevExtensionOn.toContinuousMapOnL` on `S = ⊤`, with the
compact set `K ⊇ Ω` (typically `closure Ω`) as target. [brezis2011functional] Corollary 9.14,
footnote 15. -/
noncomputable def SobolevEuclidean.toContinuousMapL (hΩ : IsSobolevExtensionDomain N p Ω)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] :
    SobolevEuclidean N 1 p Ω →L[ℝ] C(K, ℝ) :=
  (hΩ.toContinuousMapOnL hp K).comp
    ((ContinuousLinearMap.id ℝ (SobolevEuclidean N 1 p Ω)).codRestrict ⊤ fun _ ↦ Submodule.mem_top)

/-- `SobolevEuclidean.toContinuousMapL` is the trace map on `⊤`. -/
theorem SobolevEuclidean.toContinuousMapL_apply (hΩ : IsSobolevExtensionDomain N p Ω)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K]
    (u : SobolevEuclidean N 1 p Ω) :
    SobolevEuclidean.toContinuousMapL hΩ hp K u
      = hΩ.toContinuousMapOnL hp K ⟨u, Submodule.mem_top⟩ :=
  rfl

/-- The trace map on `W^{1,p}(Ω)` is the continuous representative on `Ω`. -/
theorem SobolevEuclidean.fn_ae_eq_toContinuousMapL (hΩ : IsSobolevExtensionDomain N p Ω)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K]
    (u : SobolevEuclidean N 1 p Ω) :
    fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevEuclidean.contRep hp (hΩ.choose ⟨u, Submodule.mem_top⟩) :=
  hΩ.fn_ae_eq_toContinuousMapOnL hp K ⟨u, Submodule.mem_top⟩

/-- The trace map on `W^{1,p}(Ω)` is injective for `K ⊇ Ω`. -/
theorem SobolevEuclidean.toContinuousMapL_injective (hΩ : IsSobolevExtensionDomain N p Ω)
    (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    Function.Injective (SobolevEuclidean.toContinuousMapL hΩ hp K) := fun u v huv ↦ by
  have := hΩ.toContinuousMapOnL_injective hp hK huv
  simpa using congrArg Subtype.val this

/-- **`W^{1,p}(Ω) ↪ C(K)` is a continuous embedding** for an extension domain `Ω`, `N < p < ∞`
and a compact `K ⊇ Ω`: [brezis2011functional] Corollary 9.14, "`W^{1,p}(Ω) ⊂ C(Ω̄)`" with
continuous injection. -/
theorem SobolevEuclidean.isContinuousEmbedding_toContinuousMapL
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))}
    [CompactSpace K] (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    IsContinuousEmbedding (SobolevEuclidean.toContinuousMapL hΩ hp K).toLinearMap :=
  ⟨SobolevEuclidean.toContinuousMapL_injective hΩ hp hK, _,
    (SobolevEuclidean.toContinuousMapL hΩ hp K).le_opNorm⟩

end ToContinuousMap
