/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, beside the whole-space
inequalities of `Numlib/Analysis/Sobolev/Embedding.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Holder
import Numlib.Analysis.Sobolev.Chart
import Numlib.Analysis.Sobolev.Embedding

/-!
# The Sobolev embeddings on a domain with an extension operator

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.3.B: the
embeddings of `W^{1,p}(Ω)` for an open set `Ω ⊆ ℝ^N` of class `C¹` with bounded boundary, or the
half space — Corollary 9.14 in its three cases `p < N`, `p = N`, `p > N`, with the Hölder
estimate and the continuous representative up to the boundary (`W^{1,p}(Ω) ⊂ C(Ω̄)`) for
`p > N` — and their higher-order form, Corollary 9.15: `W^{m,p}(Ω) ⊂ L^q(Ω)`, `L^∞(Ω)` and
`C^k(Ω̄)` by repeated application of Corollary 9.14.

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

* `IsSobolevExtensionDomainAll`: an extension domain for every exponent, the standing
  hypothesis of Corollary 9.15 (supplied for `C¹` chart domains with bounded boundary by
  Theorem 9.7, in `Numlib/Analysis/Sobolev/Compactness.lean`).
* `SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension`,
  `SobolevEuclidean.memLp_fn_of_order_of_hasSobolevExtension`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension`:
  **Corollary 9.15, the `L^q` clauses**, `W^{m,p}(Ω) ↪ L^q(Ω)` for `p ≤ q < ∞` with
  `1/p − m/N ≤ 1/q`, by induction on `m` through the domain form of the inductive step
  (`SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le`) and
  Corollary 9.14.
* `SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension`,
  `SobolevEuclidean.memLp_fn_top_of_order_of_hasSobolevExtension`: **Corollary 9.15, the `L^∞`
  clause**, with a representative continuous on `ℝ^N` and Hölder.
* `SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order`,
  `SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order`,
  `SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_lt`: **Corollary 9.15, the `C^k(Ω̄)`
  clause** (footnote 16) for `k + N/p < m`: a representative of class `C^k` on `Ω`, each of
  whose derivatives of order `≤ k` agrees on `Ω` with a continuous function on `ℝ^N` bounded by
  `C ‖u‖`, the top one Hölder — of the sharp exponent `m − N/p − k` when it is less than `1`.

* `isContDiffDomain_ball`, `isContDiffChartDomain_ball`: an open ball of `ℝ^{d+1}` is a domain
  of class `C^∞` (graph and chart senses), the standard example of a `C¹` domain with bounded
  boundary.

* `SobolevEuclidean.norm_le_gradNorm_add_eLpNorm_of_isBounded`,
  `SobolevEuclidean.exists_forall_gradNorm_add_eLpNorm_le_norm`,
  `SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_lt` / `_of_eq_finrank` /
  `_of_gt`: **Remark 15**, the norm `‖∇u‖_p + ‖u‖_q` is equivalent to the norm of `W^{1,p}(Ω)`
  on a bounded extension domain for the `q` of Corollary 9.14, by interpolation and an
  Ehrling-type absorption (`ENNReal.le_max_mul_add_of_le_rpow_mul_rpow`).

Remark 16 (the unbounded `W^{1,N}` function) is not proved here.

## References

[brezis2011functional], §9.3.B: Corollary 9.14, footnote 15, Corollary 9.15 (footnotes 16–17),
Remark 15, Remark 20.
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

/-! ### Corollary 9.15: the higher-order embeddings on an extension domain -/

section HigherOrderDomain

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

variable (N Ω) in
/-- **`Ω` is a `W^{1,q}`-extension domain for every exponent `q`**: the standing hypothesis of
[brezis2011functional] Corollary 9.15 (an open set of class `C¹` with bounded boundary, for
which Theorem 9.7 holds for every `p`; or the half space), under which the higher-order embeddings
are proved by repeated application of Corollary 9.14 at the exponents that arise. -/
def IsSobolevExtensionDomainAll : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], IsSobolevExtensionDomain N q Ω

/-- An extension domain for every exponent is one for each. -/
theorem IsSobolevExtensionDomainAll.isSobolevExtensionDomain (h : IsSobolevExtensionDomainAll N Ω)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] : IsSobolevExtensionDomain N q Ω :=
  h q

/-- The `L^p(Ω)` norm of the function of `u ∈ W^{k,p}(Ω)` is at most `‖u‖`. -/
theorem SobolevMultiIndex.eLpNorm_fn_le_ofReal_norm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} (u : SobolevMultiIndex F b k p Ω μ) :
    eLpNorm (fn u) p (μ.restrict (Ω : Set E)) ≤ ENNReal.ofReal ‖u‖ := by
  have h : ‖weakDeriv u 0‖ = (eLpNorm (fn u) p (μ.restrict (Ω : Set E))).toReal := by
    rw [Lp.norm_def]
    rfl
  rw [← ENNReal.ofReal_toReal (SobolevMultiIndex.memLp u).eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (h ▸ norm_weakDeriv_le u 0)

/-- **The first-order embeddings of Corollary 9.14 in one statement**: for an extension domain,
`1 ≤ p ≤ q < ∞` with `1/p − 1/N ≤ 1/q`, and `N ≥ 2` or `p > 1`, there is a finite `K` with
`‖u‖_{L^q(Ω)} ≤ K ‖u‖` for every `u ∈ W^{1,p}(Ω)`: the whole-space statement
`SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le` transferred along the extension
operator. [brezis2011functional] Corollary 9.14. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le_of_hasSobolevExtension {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N p Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N 1 p Ω,
      eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        ≤ K * ENNReal.ofReal ‖u‖ := by
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le (N := N) hN hpq hq
  obtain ⟨C, hC0, hC⟩ := hΩ.exists_forall_eLpNorm_fn_le (K := K.toReal) fun v ↦ by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
    exact hKu v
  exact ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun u ↦ by
    rw [← ENNReal.ofReal_mul hC0]
    exact hC ⟨u, Submodule.mem_top⟩⟩

/-- **Corollary 9.15, the `L^q` bound at every order**: for an extension domain (for every
exponent), `1 ≤ p ≤ q < ∞` with `1/p − m/N ≤ 1/q`, and `N ≥ 2` or `p > 1`, there is a finite `K`
with `‖u‖_{L^q(Ω)} ≤ K ‖u‖` for every `u ∈ W^{m,p}(Ω)`; by induction on `m` through
`SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le`, as for
Corollary 9.13. [brezis2011functional] Corollary 9.15 ("by repeated application of
Corollary 9.14"). -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension (m : ℕ)
    {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N m p Ω,
      eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        ≤ K * ENNReal.ofReal ‖u‖ := by
  induction m generalizing p q with
  | zero =>
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
    have hq0 : (0 : ℝ) < q := hp0.trans_le (by exact_mod_cast hpq)
    obtain rfl : q = p := by
      refine le_antisymm ?_ hpq
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hp0 hq0]
      simpa using hq
    exact ⟨1, ENNReal.one_ne_top, fun u ↦ by
      rw [one_mul]
      exact SobolevMultiIndex.eLpNorm_fn_le_ofReal_norm u⟩
  | succ m ih =>
    have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
    obtain ⟨r, hpr, hrq, hr₁, hr₂⟩ :=
      NNReal.exists_intermediate_sobolev_exponent (N := N) m (zero_lt_one.trans_le hp1) hpq hq
    have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
    have hNr : 2 ≤ N ∨ 1 < r := hN.imp id fun h ↦ h.trans_le hpr
    obtain ⟨K₁, hK₁, hK₁u⟩ := ih (q := r) hN hpr hr₁
    obtain ⟨K₂, hK₂, hK₂u⟩ :=
      SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le_of_hasSobolevExtension (hΩ r)
        hNr hrq hr₂
    refine ⟨K₂ * ((N + 1) * K₁), ENNReal.mul_ne_top hK₂ (ENNReal.mul_ne_top (by simp) hK₁),
      fun u ↦ ?_⟩
    obtain ⟨w, hw, hwn⟩ :=
      SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le hK₁ hK₁u u
    rw [← eLpNorm_congr_ae hw]
    refine (hK₂u w).trans ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    calc ENNReal.ofReal ‖w‖ ≤ ENNReal.ofReal ((N + 1) * K₁.toReal * ‖u‖) :=
          ENNReal.ofReal_le_ofReal hwn
      _ = (N + 1) * K₁ * ENNReal.ofReal ‖u‖ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_toReal hK₁]
          congr 2
          rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one,
            ENNReal.ofReal_natCast]

/-- **Corollary 9.15, the `L^q` clauses, the membership**: for an extension domain,
`1 ≤ p ≤ q < ∞` with `1/p − m/N ≤ 1/q`, and `N ≥ 2` or `p > 1`, `fn u ∈ L^q(Ω)` for every
`u ∈ W^{m,p}(Ω)` — `W^{m,p}(Ω) ⊂ L^q(Ω)` for `1/q = 1/p − m/N` when `1/p − m/N > 0`, and for
every `q ∈ [p, ∞)` when `1/p − m/N ≤ 0`. [brezis2011functional] Corollary 9.15. -/
theorem SobolevEuclidean.memLp_fn_of_order_of_hasSobolevExtension {m : ℕ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) (u : SobolevEuclidean N m p Ω) :
    MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension m hΩ hN hpq hq
  exact memLp_iff.2 ((hKu u).trans_lt (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top))

/-- **Corollary 9.15, the `L^q` clauses, as continuous embeddings**: `W^{m,p}(Ω) ↪ L^q(Ω)`
along `SobolevMultiIndex.toLpₗ` for an extension domain, `1 ≤ p ≤ q < ∞` with
`1/p − m/N ≤ 1/q` (`N ≥ 2` or `p > 1`). [brezis2011functional] Corollary 9.15. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension {m : ℕ}
    {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m p Ω volume
      (SobolevEuclidean.memLp_fn_of_order_of_hasSobolevExtension hΩ hN hpq hq)) := by
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension m hΩ hN hpq hq
  refine isContinuousEmbedding_toLpₗ_of_eLpNorm_le _ (C := K.toReal) fun u ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
  exact hKu u

/-- **Corollary 9.15, the continuous representative**: for an extension domain, `m > N/p`
(`1 ≤ p < ∞`, and `N ≥ 2` or `p > 1`), there are `C ≥ 0` and a Hölder exponent `θ ∈ (0, 1]` —
the sharp `m − N/p` when it is less than `1` — such that every `u ∈ W^{m,p}(Ω)` has a
representative `ũ` continuous on all of `ℝ^N` (hence on `Ω̄`) with `‖ũ x‖ ≤ C ‖u‖` and
`‖ũ x − ũ y‖ ≤ C ‖u‖ ‖x − y‖^θ`; in particular `W^{m,p}(Ω) ⊂ L^∞(Ω) ∩ C(Ω̄)` when
`1/p − m/N < 0`. `W^{m,p}(Ω) ⊆ W^{1,r}(Ω)` for the `r > N` of `NNReal.exists_morrey_exponent`,
then Corollary 9.14 for `r > N`. [brezis2011functional] Corollary 9.15, footnote 16 at `k = 0`. -/
theorem SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension {m : ℕ}
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p < 1 → θ = m - N / p) ∧
      ∀ u : SobolevEuclidean N m p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
        (∀ x, ‖ũ x‖ ≤ C * ‖u‖) ∧ ∀ x y, ‖ũ x - ũ y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ≥0) < p := zero_lt_one.trans_le hp1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    refine ⟨m - 1, ?_⟩
    have : 0 < m := by exact_mod_cast (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ N / p) hm)
    omega
  obtain ⟨r, hpr, hNr, hr₁, hθ⟩ := NNReal.exists_morrey_exponent (N := N) m' hp0 hm
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
  obtain ⟨K₁, hK₁, hK₁u⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension m' hΩ hN hpr hr₁
  obtain ⟨C₁, hC₁⟩ := SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq (hΩ r) hNr
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (N + 1) * K₁.toReal := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ by positivity
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (Nat.cast_nonneg N) (by exact_mod_cast hNr)
  have hα : ((1 - (N : ℝ≥0) / r : ℝ≥0) : ℝ) = 1 - N / (r : ℝ) := by
    rw [NNReal.coe_sub ((div_le_one (by exact_mod_cast hr0)).2 hNr.le)]
    simp
  refine ⟨C₁ * D, 1 - N / r, by positivity, ?_, ?_, hθ, fun u ↦ ?_⟩
  · exact sub_pos.2 ((div_lt_one hr0).2 (by exact_mod_cast hNr))
  · exact sub_le_self _ (by positivity)
  obtain ⟨w, hw, hwn⟩ :=
    SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le hK₁ hK₁u u
  rw [← hD] at hwn
  obtain ⟨ũ, hũc, hũae, hũh, hũb⟩ := hC₁ w
  refine ⟨ũ, hũc, hw.symm.trans hũae, fun x ↦ ?_, fun x y ↦ ?_⟩
  · calc ‖ũ x‖ ≤ C₁ * ‖w‖ := hũb x
      _ ≤ C₁ * (D * ‖u‖) := mul_le_mul_of_nonneg_left hwn C₁.coe_nonneg
      _ = C₁ * D * ‖u‖ := by ring
  · have h1 := hũh.dist_le x y
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, hα] at h1
    calc ‖ũ x - ũ y‖ ≤ C₁ * ‖w‖ * ‖x - y‖ ^ (1 - N / (r : ℝ)) := h1
      _ ≤ C₁ * (D * ‖u‖) * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by gcongr
      _ = C₁ * D * ‖u‖ * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by ring

/-- **Corollary 9.15, `W^{m,p}(Ω) ⊆ L^∞(Ω)` for `1/p − m/N < 0`**, the membership, on an
extension domain (`N ≥ 2` or `p > 1`). -/
theorem SobolevEuclidean.memLp_fn_top_of_order_of_hasSobolevExtension {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hm : (N : ℝ) / p < m) (u : SobolevEuclidean N m p Ω) :
    MemLp (fn u) ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, θ, hC0, -, -, -, hC⟩ :=
    SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension hΩ hN hm
  obtain ⟨ũ, hc, hae, hb, -⟩ := hC u
  refine memLp_iff.2 ?_
  rw [eLpNorm_congr_ae hae]
  refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (C * ‖u‖))
    hc.aestronglyMeasurable.restrict (Eventually.of_forall fun x ↦ ?_)).trans_lt (by simp)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hb x)

/-- **Corollary 9.15, the `C^k(Ω̄)` representative, in the form of the induction**: for an
extension domain, `k + N/p < m` (`1 ≤ p < ∞`, and `N ≥ 2` or `p > 1`), there are `C ≥ 0` and a
Hölder exponent `θ ∈ (0, 1]` — the sharp `m − N/p − k` when that is less than `1` — such that
every `u ∈ W^{m,p}(Ω)` has a representative `ũ`, continuous on `ℝ^N` and of class `C^k` on `Ω`,
each of whose derivatives `D^j ũ`, `j ≤ k`, agrees on `Ω` with a continuous `G_j : ℝ^N → ⋯`
bounded by `C ‖u‖` (the continuous extension to `Ω̄` of the book's `C^k(Ω̄)`), the one of order
`k` being `θ`-Hölder with constant `C ‖u‖`. Induction on `k` as in
`SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order`, the derivatives being assembled from
the extensions of the partial derivatives' derivatives. [brezis2011functional] Corollary 9.15,
footnote 16. -/
theorem SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (k : ℕ) {m : ℕ}
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p - k < 1 → θ = m - N / p - k) ∧
      ∀ u : SobolevEuclidean N m p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        ContDiffOn ℝ k ũ Ω ∧ fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
        (∀ j ≤ k, ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
          Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω ∧ ∀ x, ‖G x‖ ≤ C * ‖u‖) ∧
        ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×k]→L[ℝ] ℝ),
          Continuous G ∧ EqOn (iteratedFDeriv ℝ k ũ) G Ω ∧ (∀ x, ‖G x‖ ≤ C * ‖u‖) ∧
          ∀ x y, ‖G x - G y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  induction k generalizing m with
  | zero =>
    rw [Nat.cast_zero, zero_add] at hm
    obtain ⟨C, θ, hC0, hθ0, hθ1, hθ, hC⟩ :=
      SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension hΩ hN hm
    refine ⟨C, θ, hC0, hθ0, hθ1, fun h ↦ ?_, fun u ↦ ?_⟩
    · rw [Nat.cast_zero, sub_zero] at h ⊢
      exact hθ h
    obtain ⟨ũ, hc, hae, hb, hh⟩ := hC u
    have hG : ∀ j ≤ 0, ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω ∧ ∀ x, ‖G x‖ ≤ C * ‖u‖ := by
      intro j hj
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      refine ⟨iteratedFDeriv ℝ 0 ũ, ?_, fun x _ ↦ rfl, fun x ↦ ?_⟩
      · rw [iteratedFDeriv_zero_eq_comp]
        exact (continuousMultilinearCurryFin0 ℝ _ ℝ).symm.continuous.comp hc
      · rw [norm_iteratedFDeriv_zero]
        exact hb x
    refine ⟨ũ, hc, contDiffOn_zero.2 hc.continuousOn, hae, hG, iteratedFDeriv ℝ 0 ũ, ?_,
      fun x _ ↦ rfl, fun x ↦ ?_, fun x y ↦ ?_⟩
    · rw [iteratedFDeriv_zero_eq_comp]
      exact (continuousMultilinearCurryFin0 ℝ _ ℝ).symm.continuous.comp hc
    · rw [norm_iteratedFDeriv_zero]
      exact hb x
    · rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
        LinearIsometryEquiv.norm_map]
      exact hh x y
  | succ k ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
      refine ⟨m - 1, ?_⟩
      have : 0 < m := by
        have h0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
        exact_mod_cast h0
      omega
    have hm' : (k : ℝ) + N / p < m' := by
      push_cast at hm
      linarith
    obtain ⟨C₀, θ, hC₀, hθ0, hθ1, hθ, hC⟩ := ih hm'
    have hθ' : ((m' + 1 : ℕ) : ℝ) - N / p - ((k + 1 : ℕ) : ℝ) < 1 →
        θ = ((m' + 1 : ℕ) : ℝ) - N / p - ((k + 1 : ℕ) : ℝ) := by
      intro h
      push_cast at h ⊢
      rw [hθ (by linarith)]
      ring
    obtain ⟨L, hL⟩ : ∃ L : Fin N → (ℝ →L[ℝ] (EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)),
      L = fun i ↦ (ContinuousLinearMap.id ℝ ℝ).smulRight (PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i) :=
      ⟨_, rfl⟩
    have hL0 : 0 ≤ ∑ i, ‖L i‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    refine ⟨C₀ * (1 + ∑ i, ‖L i‖), θ, by positivity, hθ0, hθ1, hθ', fun u ↦ ?_⟩
    -- the lower-order elements
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : SobolevEuclidean N m' p Ω,
        v₀ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume
          (Nat.le_succ m') u :=
      ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin N → SobolevEuclidean N m' p Ω,
        v = fun i ↦ partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume i u :=
      ⟨_, rfl⟩
    have hv₀fn : fn v₀ = fn u := by rw [hv₀]; rfl
    have hv₀n : ‖v₀‖ ≤ ‖u‖ := by rw [hv₀]; exact norm_toLowerOrder_le _ u
    have hvn : ∀ i, ‖v i‖ ≤ ‖u‖ := fun i ↦ by rw [hv]; exact norm_partialDeriv_le i u
    obtain ⟨ũ, hũc, hũk, hũae, hũG, -⟩ := hC v₀
    rw [hv₀fn] at hũae
    choose g hgc hgk hgae hgG hgH using fun i ↦ hC (v i)
    choose H hHc hHeq hHb hHh using hgH
    -- the tensor weak derivative of `fn u` on `Ω`, continuous
    obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
        w = fun x ↦ ∑ i, g i x • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i := ⟨_, rfl⟩
    have hwk : ContDiffOn ℝ k w Ω := by
      rw [hw]
      exact ContDiffOn.sum fun i _ ↦ (hgk i).smul contDiffOn_const
    have hwc : Continuous w := by
      rw [hw]
      exact continuous_finsetSum _ fun i _ ↦ (hgc i).smul continuous_const
    have hweak : HasWeakFDerivOn (fn u) w Ω volume := by
      rw [hw]
      exact SobolevEuclidean.hasWeakFDerivOn_sum_smul_proj u fun i ↦ by
        have h := hgae i
        rw [hv] at h
        exact h
    -- `ũ` is `C¹` on `Ω` with derivative `w`
    obtain ⟨v', hv'c, hv'ae, hv'd⟩ :=
      hweak.exists_contDiffOn_ae_eq_of_continuousOn hwc.continuousOn
    have hv'ũ : EqOn v' ũ Ω :=
      Measure.eqOn_open_of_ae_eq (hv'ae.symm.trans hũae) Ω.isOpen hv'c.continuousOn
        hũc.continuousOn
    have hd : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), HasFDerivAt ũ (w x) x := fun x hx ↦
      (hv'd x hx).congr_of_eventuallyEq (by
        filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
        exact (hv'ũ hy).symm)
    have hfd : EqOn (fderiv ℝ ũ) w Ω := fun x hx ↦ (hd x hx).fderiv
    have hũk' : ContDiffOn ℝ (k + 1) ũ Ω := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen Ω.isOpen]
      exact ⟨fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt, by simp,
        hwk.congr fun x hx ↦ hfd hx⟩
    -- the top derivative on `Ω`, and its extension
    have hDw : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), iteratedFDeriv ℝ k w x
        = ∑ i, (L i).compContinuousMultilinearMap (H i x) := by
      intro x hx
      rw [hw, hL, iteratedFDeriv_fun_sum_smul_const_of_contDiffAt
        (fun i ↦ (hgk i).contDiffAt (Ω.isOpen.mem_nhds hx)) _ le_rfl]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hHeq i hx]
    have hDũ : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), iteratedFDeriv ℝ (k + 1) ũ x
        = (continuousMultilinearCurryRightEquiv' ℝ k (EuclideanSpace ℝ (Fin N)) ℝ).symm
          (∑ i, (L i).compContinuousMultilinearMap (H i x)) := by
      intro x hx
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, ← hDw x hx]
      congr 1
      refine ((Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) ?_ k).eq_of_nhds)
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact hfd hy
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×(k + 1)]→L[ℝ] ℝ),
        G = fun x ↦ (continuousMultilinearCurryRightEquiv' ℝ k (EuclideanSpace ℝ (Fin N)) ℝ).symm
          (∑ i, (L i).compContinuousMultilinearMap (H i x)) := ⟨_, rfl⟩
    have hGc : Continuous G := by
      rw [hG]
      refine (continuousMultilinearCurryRightEquiv' ℝ k _ ℝ).symm.continuous.comp
        (continuous_finsetSum _ fun i _ ↦ ?_)
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ ℝ _ (L i)).continuous.comp
        (hHc i)
    have hGeq : EqOn (iteratedFDeriv ℝ (k + 1) ũ) G Ω := fun x hx ↦ by
      rw [hG, hDũ x hx]
    have hGb : ∀ x, ‖G x‖ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := fun x ↦ by
      rw [hG, LinearIsometryEquiv.norm_map]
      calc ‖∑ i, (L i).compContinuousMultilinearMap (H i x)‖
          ≤ ∑ i, ‖L i‖ * ‖H i x‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
              ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
        _ ≤ ∑ i, ‖L i‖ * (C₀ * ‖u‖) := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left ((hHb i x).trans
              (mul_le_mul_of_nonneg_left (hvn i) hC₀)) (norm_nonneg _)
        _ = C₀ * (∑ i, ‖L i‖) * ‖u‖ := by rw [← Finset.sum_mul]; ring
        _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by gcongr; linarith
    refine ⟨ũ, hũc, hũk', hũae, fun j hj ↦ ?_, G, hGc, hGeq, hGb, fun x y ↦ ?_⟩
    · rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · obtain ⟨G', hG'c, hG'eq, hG'b⟩ := hũG j (Nat.lt_succ_iff.1 hjk)
        refine ⟨G', hG'c, hG'eq, fun x ↦ (hG'b x).trans ?_⟩
        calc C₀ * ‖v₀‖ ≤ C₀ * ‖u‖ := mul_le_mul_of_nonneg_left hv₀n hC₀
          _ = C₀ * 1 * ‖u‖ := by ring
          _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by gcongr; linarith
      · obtain rfl : j = k + 1 := le_antisymm hj hjk
        exact ⟨G, hGc, hGeq, hGb⟩
    · rw [hG, ← map_sub, LinearIsometryEquiv.norm_map, ← Finset.sum_sub_distrib]
      calc ‖∑ i, ((L i).compContinuousMultilinearMap (H i x)
              - (L i).compContinuousMultilinearMap (H i y))‖
          ≤ ∑ i, ‖L i‖ * ‖H i x - H i y‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
              ContinuousLinearMap.norm_compContinuousMultilinearMap_sub_le _ _ _)
        _ ≤ ∑ i, ‖L i‖ * (C₀ * ‖u‖ * ‖x - y‖ ^ θ) := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left ((hHh i x y).trans (by gcongr; exact hvn i)) (norm_nonneg _)
        _ = C₀ * (∑ i, ‖L i‖) * ‖u‖ * ‖x - y‖ ^ θ := by rw [← Finset.sum_mul]; ring
        _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ * ‖x - y‖ ^ θ := by gcongr; linarith

/-- **Corollary 9.15, the `C^k(Ω̄)` clause**: for `m − N/p > 0` not an integer, `k = ⌊m − N/p⌋`
and `θ = m − N/p − k ∈ (0, 1)` (encoded as `0 < m − N/p − k < 1`), on an extension domain
(`1 ≤ p < ∞`, and `N ≥ 2` or `p > 1`), there is `C` such that every `u ∈ W^{m,p}(Ω)` has a
representative `ũ` continuous on `ℝ^N` and of class `C^k` on `Ω`, each of whose derivatives of
order `≤ k` agrees on `Ω` with a continuous function on `ℝ^N` bounded by `C ‖u‖` — so `ũ` lies
in the book's `C^k(Ω̄)` — the extension of the order-`k` derivative being `θ`-Hölder with
constant `C ‖u‖`. [brezis2011functional] Corollary 9.15, footnote 16. -/
theorem SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order {m k : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hθ0 : 0 < (m : ℝ) - N / p - k) (hθ1 : (m : ℝ) - N / p - k < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N m p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ,
      Continuous ũ ∧ ContDiffOn ℝ k ũ Ω ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      (∀ j ≤ k, ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω ∧ ∀ x, ‖G x‖ ≤ C * ‖u‖) ∧
      ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×k]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ k ũ) G Ω ∧
        ∀ x y, ‖G x - G y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ ((m : ℝ) - N / p - k) := by
  obtain ⟨C, θ, hC0, -, -, hθ, hC⟩ :=
    SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (N := N) k (m := m) hΩ hN
      (by linarith)
  obtain rfl := hθ hθ1
  refine ⟨C, hC0, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hk, hae, hG, G, hGc, hGeq, -, hGh⟩ := hC u
  exact ⟨ũ, hc, hk, hae, hG, G, hGc, hGeq, hGh⟩

/-- **Corollary 9.15's `C^k(Ω̄)` clause without the non-integer restriction**: for `1 ≤ p < ∞`,
integers `m, k` with `k + N/p < m`, and an extension domain (`N ≥ 2` or `p > 1`), there are `C`
and a Hölder exponent `θ ∈ (0, 1]` such that every `u ∈ W^{m,p}(Ω)` has a representative `ũ`,
continuous on `ℝ^N` and of class `C^k` on `Ω`, each of whose derivatives of order `≤ k` agrees
on `Ω` with a continuous function on `ℝ^N` bounded by `C ‖u‖` — the sup bound that makes
`D(A^ℓ) → C^k(Ω̄)` a bounded linear map for the heat equation — the extension of the order-`k`
derivative being `θ`-Hölder. [brezis2011functional] Corollary 9.15, and the proofs of
Theorems 10.1 and 10.8. -/
theorem SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_lt {m k : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ∀ u : SobolevEuclidean N m p Ω,
      ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧ ContDiffOn ℝ k ũ Ω ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      (∀ j ≤ k, ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω ∧ ∀ x, ‖G x‖ ≤ C * ‖u‖) ∧
      ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×k]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ k ũ) G Ω ∧
        ∀ x y, ‖G x - G y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  obtain ⟨C, θ, hC0, hθ0, hθ1, -, hC⟩ :=
    SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (N := N) k hΩ hN hm
  refine ⟨C, θ, hC0, hθ0, hθ1, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hk, hae, hG, G, hGc, hGeq, -, hGh⟩ := hC u
  exact ⟨ũ, hc, hk, hae, hG, G, hGc, hGeq, hGh⟩

end HigherOrderDomain

/-! ### Balls are domains of class `C^∞` -/

section Ball

variable {d : ℕ}

/-- A smooth positive function on `ℝ` equal to `a − s` for `0 ≤ s ≤ a / 4` (`a > 0`):
`a − s χ(s)` for a bump `χ` equal to `1` on `[−a/4, a/4]` and vanishing outside `(−a/2, a/2)`. -/
theorem exists_contDiff_pos_eq_sub {a : ℝ} (ha : 0 < a) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ s, 0 < φ s) ∧ ∀ s, 0 ≤ s → s ≤ a / 4 → φ s = a - s := by
  obtain ⟨χ, hχ⟩ : ∃ χ : ContDiffBump (0 : ℝ), χ = ⟨a / 4, a / 2, by positivity, by linarith⟩ :=
    ⟨_, rfl⟩
  have hIn : χ.rIn = a / 4 := by rw [hχ]
  have hOut : χ.rOut = a / 2 := by rw [hχ]
  refine ⟨fun s ↦ a - s * χ s, contDiff_const.sub (contDiff_id.mul (χ.contDiff (n := ⊤))),
    fun s ↦ ?_, fun s hs0 hs ↦ ?_⟩
  · have h0 : 0 ≤ χ s := χ.nonneg
    have h1 : χ s ≤ 1 := χ.le_one
    rcases le_or_gt s 0 with hs | hs
    · nlinarith
    · rcases le_or_gt s (a / 2) with hs2 | hs2
      · nlinarith
      · have : χ s = 0 := χ.zero_of_le_dist (by
          rw [hOut, dist_zero_right, Real.norm_eq_abs, abs_of_pos hs]
          exact hs2.le)
        change 0 < a - s * χ s
        rw [this]
        linarith
  · have : χ s = 1 := χ.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff, Real.norm_eq_abs, hIn, abs_le]
      constructor <;> linarith)
    change a - s * χ s = a - s
    rw [this, mul_one]

/-- **An open ball of `ℝ^{d+1}` is a domain of class `C^∞`** in the graph sense: near a boundary
point `x₀`, after the rigid motion `x ↦ R (x − c)` taking the unit vector from `x₀` to the
centre `c` to the last basis vector (so that `x₀` becomes the south pole `−r e_{d+1}`), the ball
is the region above the graph of `y' ↦ −√(r² − ‖y'‖²)`, a function made globally smooth by
freezing `r² − ‖y'‖²` away from `‖y'‖² ≤ r²/4` (`exists_contDiff_pos_eq_sub`), on the ball of
radius `r/2` about `x₀`. -/
theorem isContDiffDomain_ball (c : EuclideanSpace ℝ (Fin (d + 1))) {r : ℝ} (hr : 0 < r) :
    IsContDiffDomain ∞ (ball c r) := by
  refine ⟨isOpen_ball, fun x₀ hx₀ ↦ ?_⟩
  rw [frontier_ball c hr.ne'] at hx₀
  have hx₀' : ‖x₀ - c‖ = r := by rwa [mem_sphere_iff_norm] at hx₀
  -- the rigid motion
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin (d + 1)), v = r⁻¹ • (c - x₀) := ⟨_, rfl⟩
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, Real.norm_of_nonneg hr.le, norm_sub_rev, hx₀', inv_mul_cancel₀
      hr.ne']
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin (d + 1)), e = EuclideanSpace.single (Fin.last d) 1 :=
    ⟨_, rfl⟩
  have hen : ‖e‖ = 1 := by rw [he, PiLp.norm_single, norm_one]
  obtain ⟨R, hR⟩ : ∃ R : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)),
      R = Submodule.reflection (ℝ ∙ (v - e))ᗮ := ⟨_, rfl⟩
  have hRv : R v = e := by rw [hR]; exact Submodule.reflection_sub (hvn.trans hen.symm)
  obtain ⟨T, hT⟩ : ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)),
      T = (AffineIsometryEquiv.constVAdd ℝ _ (-c)).trans R.toAffineIsometryEquiv := ⟨_, rfl⟩
  have hTx : ∀ x, T x = R (x - c) := fun x ↦ by
    simp only [hT, AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.coe_constVAdd, LinearIsometryEquiv.coe_toAffineIsometryEquiv,
      vadd_eq_add, neg_add_eq_sub]
  -- the graph function
  obtain ⟨φ, hφs, hφpos, hφeq⟩ := exists_contDiff_pos_eq_sub (a := r ^ 2) (by positivity)
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, g = fun y' ↦ -√(φ (‖y'‖ ^ 2)) := ⟨_, rfl⟩
  have hgs : ContDiff ℝ ∞ g := by
    rw [hg]
    exact ((hφs.comp (contDiff_norm_sq ℝ)).sqrt fun y' ↦ (hφpos _).ne').neg
  refine ⟨r / 2, by positivity, T, g, hgs, ?_⟩
  -- the graph identity on the small ball
  have key : ∀ x ∈ ball x₀ (r / 2),
      (x ∈ ball c r ↔ g (EuclideanSpace.init (T x)) < T x (Fin.last d)) := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y, y = T x := ⟨_, rfl⟩
    have hy' : y = R (x - c) := by rw [hy, hTx]
    have h1 : y + r • e = R (x - x₀) := by
      rw [hy', ← hRv, ← map_smul, ← map_add, hv, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      congr 1
      abel
    have h2 : ‖y + r • e‖ < r / 2 := by
      rw [h1, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
      exact hx
    have h3 : EuclideanSpace.init (y + r • e) = EuclideanSpace.init y := by
      rw [EuclideanSpace.init_add, EuclideanSpace.init_smul, he, EuclideanSpace.init_single_last,
        smul_zero, add_zero]
    have h4 : ‖EuclideanSpace.init y‖ < r / 2 := by
      rw [← h3]
      exact (EuclideanSpace.norm_init_le _).trans_lt h2
    have h5 : (y + r • e) (Fin.last d) = y (Fin.last d) + r := by
      simp [he]
    have h6 : y (Fin.last d) + r < r / 2 := by
      rw [← h5]
      exact (le_abs_self _).trans_lt ((EuclideanSpace.abs_apply_last_le _).trans_lt h2)
    have h7 : y (Fin.last d) < 0 := by linarith
    have hs : ‖EuclideanSpace.init y‖ ^ 2 ≤ r ^ 2 / 4 := by
      have : ‖EuclideanSpace.init y‖ ^ 2 < (r / 2) ^ 2 := by
        gcongr
      nlinarith
    have hφ : φ (‖EuclideanSpace.init y‖ ^ 2) = r ^ 2 - ‖EuclideanSpace.init y‖ ^ 2 :=
      hφeq _ (by positivity) hs
    have hnorm : ‖x - c‖ ^ 2 = ‖EuclideanSpace.init y‖ ^ 2 + y (Fin.last d) ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq_init_add_last, hy', LinearIsometryEquiv.norm_map]
    rw [← hy, hg]
    change x ∈ ball c r ↔ -√(φ (‖EuclideanSpace.init y‖ ^ 2)) < y (Fin.last d)
    rw [hφ, mem_ball, dist_eq_norm, neg_lt, Real.lt_sqrt (by linarith), neg_sq]
    constructor
    · intro h
      have : ‖x - c‖ ^ 2 < r ^ 2 := by
        have := norm_nonneg (x - c)
        nlinarith
      linarith
    · intro h
      have hlt : ‖x - c‖ ^ 2 < r ^ 2 := by linarith
      nlinarith [norm_nonneg (x - c)]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hxΩ, hxB⟩
    exact ⟨hxB, (key x hxB).1 hxΩ⟩
  · rintro ⟨hxB, hgx⟩
    exact ⟨(key x hxB).2 hgx, hxB⟩

/-- **An open ball of `ℝ^{d+1}` is an open set of class `C^n`** in the chart sense of
[brezis2011functional] §9.2, for every `n : ℕ∞`: `isContDiffDomain_ball` through the bridge
`IsContDiffDomain.isContDiffChartDomain`. This is the standard example of a `C¹` domain with
bounded boundary, on which Corollary 9.15 applies to give the interior regularity of the
Dirichlet eigenfunctions ([brezis2011functional] Theorem 9.31). -/
theorem isContDiffChartDomain_ball (n : ℕ∞) (c : EuclideanSpace ℝ (Fin (d + 1))) {r : ℝ}
    (hr : 0 < r) : IsContDiffChartDomain n (ball c r) :=
  (isContDiffDomain_ball c hr).isContDiffChartDomain.of_le (by exact_mod_cast le_top)

end Ball

/-! ### Remark 15: an equivalent norm on `W^{1,p}(Ω)` -/

section EquivalentNorm

/-- **The absorption step of an Ehrling-type inequality**, on `ℝ≥0∞`: if
`A ≤ B^θ (K (A + G))^{1−θ}` with `0 < θ ≤ 1` and `A < ∞`, then `A ≤ C (B + G)` with
`C = max 1 (2K)^{(1−θ)/θ}` — either `A ≤ G`, or `A + G ≤ 2A` and `A^θ ≤ B^θ (2K)^{1−θ}`. -/
theorem ENNReal.le_max_mul_add_of_le_rpow_mul_rpow {A B G K : ℝ≥0∞} (hA : A ≠ ⊤) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (h : A ≤ B ^ θ * (K * (A + G)) ^ (1 - θ)) :
    A ≤ max 1 ((2 * K) ^ ((1 - θ) / θ)) * (B + G) := by
  rcases le_or_gt A G with hAG | hGA
  · calc A ≤ G := hAG
      _ ≤ 1 * (B + G) := by rw [one_mul]; exact le_add_self
      _ ≤ max 1 ((2 * K) ^ ((1 - θ) / θ)) * (B + G) := by gcongr; exact le_max_left _ _
  · have hA0 : A ≠ 0 := (lt_of_le_of_lt zero_le hGA).ne'
    have h2 : A + G ≤ 2 * A := by
      rw [two_mul]
      exact add_le_add le_rfl hGA.le
    have h3 : A ≤ B ^ θ * (2 * K) ^ (1 - θ) * A ^ (1 - θ) := by
      calc A ≤ B ^ θ * (K * (A + G)) ^ (1 - θ) := h
        _ ≤ B ^ θ * (K * (2 * A)) ^ (1 - θ) := by gcongr
        _ = B ^ θ * (2 * K) ^ (1 - θ) * A ^ (1 - θ) := by
            rw [show K * (2 * A) = 2 * K * A by ring,
              ENNReal.mul_rpow_of_nonneg _ _ (by linarith), mul_assoc]
    have h4 : A ^ θ ≤ B ^ θ * (2 * K) ^ (1 - θ) := by
      have hne : A ^ (1 - θ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hA).ne'
      have hnt : A ^ (1 - θ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hA
      have : A ^ θ * A ^ (1 - θ) ≤ B ^ θ * (2 * K) ^ (1 - θ) * A ^ (1 - θ) := by
        rwa [← ENNReal.rpow_add _ _ hA0 hA, add_sub_cancel, ENNReal.rpow_one]
      exact (ENNReal.mul_le_mul_iff_left hne hnt).1 this
    have h5 : A ≤ B * (2 * K) ^ ((1 - θ) / θ) := by
      calc A = (A ^ θ) ^ (1 / θ) := by
            rw [← ENNReal.rpow_mul, mul_one_div_cancel hθ0.ne', ENNReal.rpow_one]
        _ ≤ (B ^ θ * (2 * K) ^ (1 - θ)) ^ (1 / θ) := ENNReal.rpow_le_rpow h4 (by positivity)
        _ = B * (2 * K) ^ ((1 - θ) / θ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
              mul_one_div_cancel hθ0.ne', ENNReal.rpow_one, ← ENNReal.rpow_mul]
            congr 2
            ring
    calc A ≤ B * (2 * K) ^ ((1 - θ) / θ) := h5
      _ ≤ (B + G) * max 1 ((2 * K) ^ ((1 - θ) / θ)) := by gcongr <;> simp
      _ = max 1 ((2 * K) ^ ((1 - θ) / θ)) * (B + G) := mul_comm _ _

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

/-- The norm of `W^{1,p}(Ω)` is at most `‖u‖_p + |ι| ‖∇u‖_p`. -/
theorem SobolevMultiIndex.norm_le_norm_weakDeriv_zero_add_gradNorm
    (u : SobolevMultiIndex F b 1 p Ω μ) :
    ‖u‖ ≤ ‖SobolevMultiIndex.weakDeriv u 0‖ + Fintype.card ι * SobolevMultiIndex.gradNorm u := by
  calc ‖u‖ ≤ ∑ α, ‖SobolevMultiIndex.weakDeriv u α‖ := by
        rw [← Submodule.norm_coe]
        exact PiLp.norm_le_sum_norm _
    _ = ‖SobolevMultiIndex.weakDeriv u 0‖
        + ∑ i, ‖SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)‖ :=
        MultiIndexLE.sum_univ_one _
    _ ≤ ‖SobolevMultiIndex.weakDeriv u 0‖ + ∑ _i : ι, SobolevMultiIndex.gradNorm u :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦
          SobolevMultiIndex.norm_weakDeriv_single_le_gradNorm u i)
    _ = ‖SobolevMultiIndex.weakDeriv u 0‖ + Fintype.card ι * SobolevMultiIndex.gradNorm u := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end EquivalentNorm

section Remark15

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- `1/q − 1/r ≥ 0` for `1 ≤ q ≤ r` in `ℝ≥0∞`, the exponent of `|Ω|` in
`‖f‖_q ≤ ‖f‖_r |Ω|^{1/q − 1/r}`. -/
theorem ENNReal.one_div_toReal_sub_nonneg_of_le {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r) :
    0 ≤ 1 / q.toReal - 1 / r.toReal := by
  rw [sub_nonneg]
  rcases eq_or_ne r ⊤ with rfl | hr
  · simp
  · exact one_div_le_one_div_of_le (ENNReal.toReal_pos (one_pos.trans_le hq).ne'
      (ne_top_of_le_ne_top hr hqr)) (ENNReal.toReal_mono hr hqr)

/-- **Lowering the exponent of an embedding on a set of finite measure**: from
`‖u‖_{L^r(Ω)} ≤ K ‖u‖` and `1 ≤ q ≤ r` follows `‖u‖_{L^q(Ω)} ≤ K |Ω|^{1/q − 1/r} ‖u‖`. -/
theorem SobolevEuclidean.eLpNorm_fn_le_mul_of_le
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    {K : ℝ≥0∞}
    (hKu : ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖)
    (u : SobolevEuclidean N 1 p Ω) :
    eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ K * volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ^ (1 / q.toReal - 1 / r.toReal)
        * ENNReal.ofReal ‖u‖ := by
  have _ := hΩ
  have _ := hq
  calc eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ eLpNorm (fn u) r (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) univ
          ^ (1 / q.toReal - 1 / r.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqr
          (SobolevMultiIndex.memLp u).aestronglyMeasurable
    _ ≤ K * ENNReal.ofReal ‖u‖
        * volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ^ (1 / q.toReal - 1 / r.toReal) := by
        rw [Measure.restrict_apply_univ]
        gcongr
        exact hKu u
    _ = _ := by ring

/-- **Remark 15, the converse bound**: `‖∇u‖_p + ‖u‖_q ≤ C ‖u‖` on `Ω` of finite measure whenever
`W^{1,p}(Ω) ↪ L^r(Ω)` for some `r ≥ q` (the embedding of Corollary 9.14), since
`‖u‖_q ≤ |Ω|^{1/q − 1/r} ‖u‖_r`. -/
theorem SobolevEuclidean.exists_forall_gradNorm_add_eLpNorm_le_norm
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hKu : ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω,
      gradNorm u + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0∞, M = K * volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
      ^ (1 / q.toReal - 1 / r.toReal) := ⟨_, rfl⟩
  have hMt : M ≠ ⊤ := hM ▸ ENNReal.mul_ne_top hK (ENNReal.rpow_ne_top_of_nonneg
    (ENNReal.one_div_toReal_sub_nonneg_of_le hq hqr) hΩ)
  refine ⟨1 + M.toReal, by positivity, fun u ↦ ?_⟩
  have h2 : (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
      ≤ M.toReal * ‖u‖ := by
    rw [← ENNReal.toReal_ofReal (norm_nonneg u), ← ENNReal.toReal_mul, hM]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (hM ▸ hMt) ENNReal.ofReal_ne_top)
      (SobolevEuclidean.eLpNorm_fn_le_mul_of_le hΩ hq hqr hKu u)
  calc gradNorm u + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
      ≤ ‖u‖ + M.toReal * ‖u‖ := add_le_add (gradNorm_le_norm u) h2
    _ = (1 + M.toReal) * ‖u‖ := by ring

/-- **Remark 15 (an equivalent norm on `W^{1,p}(Ω)`), the main bound**: on an open `Ω` of finite
measure, `1 ≤ p < ∞`, if `W^{1,p}(Ω) ↪ L^r(Ω)` for some `r > p` (Corollary 9.14) and `1 ≤ q ≤ r`,
then `‖u‖_{W^{1,p}} ≤ C (‖∇u‖_p + ‖u‖_q)`. For `q ≥ p` this is `‖u‖_p ≤ |Ω|^{1/p − 1/q} ‖u‖_q`; for
`q < p` the interpolation `‖u‖_p ≤ ‖u‖_q^θ ‖u‖_r^{1−θ}` with `‖u‖_r ≤ K (‖u‖_p + N ‖∇u‖_p)` and the
absorption `ENNReal.le_max_mul_add_of_le_rpow_mul_rpow`. Together with
`SobolevEuclidean.exists_forall_gradNorm_add_eLpNorm_le_norm` this is the equivalence of the norms
`‖∇u‖_p + ‖u‖_q` and `‖u‖_{W^{1,p}}` of [brezis2011functional] Chapter 9, Remark 15, whose three
cases are `SobolevEuclidean.norm_le_gradNorm_add_eLpNorm_of_lt`, `…_of_eq_finrank` and `…_of_gt`. -/
theorem SobolevEuclidean.norm_le_gradNorm_add_eLpNorm_of_isBounded
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    (hpr : p < r) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hKu : ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  -- the `L^q` norm is finite
  have hBt : ∀ u : SobolevEuclidean N 1 p Ω,
      eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≠ ⊤ := fun u ↦
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK (ENNReal.rpow_ne_top_of_nonneg
      (ENNReal.one_div_toReal_sub_nonneg_of_le hq hqr) hΩ)) ENNReal.ofReal_ne_top)
      (SobolevEuclidean.eLpNorm_fn_le_mul_of_le hΩ hq hqr hKu u)
  -- the norm through the function and the gradient
  have hnorm : ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤
      (eLpNorm (fn u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        + N * gradNorm u := fun u ↦ by
    have := SobolevMultiIndex.norm_le_norm_weakDeriv_zero_add_gradNorm u
    rwa [Fintype.card_fin, Lp.norm_def] at this
  rcases le_or_gt p q with hpq | hqp
  · -- `p ≤ q`: `‖u‖_p ≤ |Ω|^{1/p − 1/q} ‖u‖_q`
    obtain ⟨M, hM⟩ : ∃ M : ℝ≥0∞, M = volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
        ^ (1 / p.toReal - 1 / q.toReal) := ⟨_, rfl⟩
    have hMt : M ≠ ⊤ := hM ▸ ENNReal.rpow_ne_top_of_nonneg
      (ENNReal.one_div_toReal_sub_nonneg_of_le hp1 hpq) hΩ
    refine ⟨max M.toReal N, le_max_of_le_right (Nat.cast_nonneg N), fun u ↦ ?_⟩
    have h1 : (eLpNorm (fn u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ M.toReal * (eLpNorm (fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
      rw [← ENNReal.toReal_mul, mul_comm]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top (hBt u) hMt) ?_
      have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq
        (SobolevMultiIndex.memLp u).aestronglyMeasurable
        (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      rwa [Measure.restrict_apply_univ, ← hM] at this
    calc ‖u‖ ≤ (eLpNorm (fn u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
          + N * gradNorm u := hnorm u
      _ ≤ M.toReal * (eLpNorm (fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal + N * gradNorm u :=
          add_le_add h1 le_rfl
      _ ≤ max M.toReal N * (gradNorm u + (eLpNorm (fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) := by
          have h3 := gradNorm_nonneg u
          have h4 := ENNReal.toReal_nonneg (a := eLpNorm (fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
          nlinarith [le_max_left M.toReal N, le_max_right M.toReal N]
  · -- `q < p`: interpolation between `q` and `r`, and absorption
    obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_inv_eq_ofReal_mul_inv_add hq0 hqp.le hpr.le
    have hθpos : 0 < θ := by
      rcases hθ0.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, ENNReal.ofReal_zero, zero_mul, zero_add, sub_zero, ENNReal.ofReal_one,
          one_mul] at hθ
        exact hpr.ne (inv_inj.1 hθ)
    obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ≥0∞, C₀ = max 1 ((2 * (K * (N + 1))) ^ ((1 - θ) / θ)) := ⟨_, rfl⟩
    have hC₀t : C₀ ≠ ⊤ := by
      rw [hC₀]
      exact max_ne_top ENNReal.one_ne_top (ENNReal.rpow_ne_top_of_nonneg
        (div_nonneg (by linarith) hθpos.le)
        (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hK (by simp))))
    refine ⟨(C₀.toReal + 1) * (N + 1), by positivity, fun u ↦ ?_⟩
    -- the key inequality in `ℝ≥0∞`
    obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞,
      A = eLpNorm (fn u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞,
      B = eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : ℝ≥0∞, G = ENNReal.ofReal (gradNorm u) := ⟨_, rfl⟩
    have hAt : A ≠ ⊤ := hA ▸ (SobolevMultiIndex.memLp u).eLpNorm_ne_top
    have hBt' : B ≠ ⊤ := hB ▸ hBt u
    have hGt : G ≠ ⊤ := hG ▸ ENNReal.ofReal_ne_top
    have hu : ENNReal.ofReal ‖u‖ ≤ (N + 1) * (A + G) := by
      calc ENNReal.ofReal ‖u‖ ≤ ENNReal.ofReal (A.toReal + N * gradNorm u) := by
            rw [hA]
            exact ENNReal.ofReal_le_ofReal (hnorm u)
        _ = A + N * G := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
              (mul_nonneg (Nat.cast_nonneg N) (gradNorm_nonneg u)), ENNReal.ofReal_toReal hAt,
              ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast, hG]
        _ ≤ (N + 1) * (A + G) := by
            have : (N + 1 : ℝ≥0∞) * (A + G) = A + N * G + (N * A + G) := by ring
            rw [this]
            exact le_self_add
    have hinterp : A ≤ B ^ θ * ((K * (N + 1)) * (A + G)) ^ (1 - θ) := by
      calc A ≤ B ^ θ * (eLpNorm (fn u) r
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ^ (1 - θ) := by
            rw [hA, hB]
            exact eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow
              (SobolevMultiIndex.memLp u).aestronglyMeasurable hθ0 hθ1 hθ
        _ ≤ B ^ θ * (K * ((N + 1) * (A + G))) ^ (1 - θ) := by
            gcongr
            exact (hKu u).trans (mul_le_mul' le_rfl hu)
        _ = B ^ θ * ((K * (N + 1)) * (A + G)) ^ (1 - θ) := by rw [mul_assoc]
    have hkey : A ≤ C₀ * (B + G) := by
      rw [hC₀]
      exact ENNReal.le_max_mul_add_of_le_rpow_mul_rpow hAt hθpos hθ1 hinterp
    -- back to real numbers
    have hkey' : A.toReal ≤ C₀.toReal * (B.toReal + gradNorm u) := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC₀t (ENNReal.add_ne_top.2 ⟨hBt', hGt⟩))
        hkey
      rwa [ENNReal.toReal_mul, ENNReal.toReal_add hBt' hGt, hG,
        ENNReal.toReal_ofReal (gradNorm_nonneg u)] at h
    have hC₀0 : 0 ≤ C₀.toReal := ENNReal.toReal_nonneg
    have hg0 := gradNorm_nonneg u
    have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
    calc ‖u‖ ≤ A.toReal + N * gradNorm u := hA ▸ hnorm u
      _ ≤ C₀.toReal * (B.toReal + gradNorm u) + N * gradNorm u := add_le_add hkey' le_rfl
      _ ≤ (C₀.toReal + 1) * (N + 1) * (gradNorm u + B.toReal) := by
          nlinarith [mul_nonneg hC₀0 hg0, mul_nonneg hC₀0 hB0, mul_nonneg (Nat.cast_nonneg N) hg0,
            mul_nonneg (Nat.cast_nonneg N) hB0,
            mul_nonneg (mul_nonneg hC₀0 (Nat.cast_nonneg N)) hg0,
            mul_nonneg (mul_nonneg hC₀0 (Nat.cast_nonneg N)) hB0]
      _ = (C₀.toReal + 1) * (N + 1) * (gradNorm u
          + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) := by
          rw [hB]

/-- **Remark 15 as an equivalence of norms**, abstractly: on `Ω` of finite measure, if
`W^{1,p}(Ω) ↪ L^r(Ω)` for some `r > p` and `1 ≤ q ≤ r`, the quantity `‖∇u‖_p + ‖u‖_q` is
equivalent to the norm of `W^{1,p}(Ω)`. -/
theorem SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    (hpr : p < r) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hKu : ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ :=
  ⟨SobolevEuclidean.norm_le_gradNorm_add_eLpNorm_of_isBounded hΩ hq hqr hpr hK hKu,
    SobolevEuclidean.exists_forall_gradNorm_add_eLpNorm_le_norm hΩ hq hqr hK hKu⟩

/-- The bound of Corollary 9.14 in the form `‖u‖_r ≤ K ‖u‖` with `K : ℝ≥0∞`. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_mul_ofReal_of_exists_forall
    {r : ℝ≥0∞} (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (⊤ : Submodule ℝ (SobolevEuclidean N 1 p Ω)),
      eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) r
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖)) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun u ↦ ?_⟩
  rw [← ENNReal.ofReal_mul hC0]
  exact hC ⟨u, Submodule.mem_top⟩

variable {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Remark 15, case `p < N`**: for a bounded extension domain, `1 ≤ p < N` and `1 ≤ q ≤ p*`,
the norm `‖∇u‖_p + ‖u‖_q` is equivalent to the norm of `W^{1,p}(Ω)`.
[brezis2011functional] Chapter 9, Remark 15. -/
theorem SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_lt
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqp' : q ≤ p') :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hN0 : (0 : ℝ) < N := hp0.trans (by exact_mod_cast hpN)
  have hpp' : p < p' := by
    have h1 : (0 : ℝ) < (p' : ℝ)⁻¹ := by
      rw [hp', sub_pos]
      exact inv_strictAnti₀ hp0 (by exact_mod_cast hpN)
    rw [← NNReal.coe_lt_coe, ← inv_lt_inv₀ (inv_pos.1 h1) hp0, hp']
    exact sub_lt_self _ (by positivity)
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_mul_ofReal_of_exists_forall
    (hΩ.exists_forall_eLpNorm_fn_le_of_le_of_le hpN hp' hpp'.le le_rfl)
  exact SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le hb.measure_lt_top.ne hq hqp'
    (by exact_mod_cast hpp') hK hKu

/-- **Remark 15, case `p = N`**: for a bounded extension domain, `N ≥ 2` and `1 ≤ q < ∞`, the
norm `‖∇u‖_N + ‖u‖_q` is equivalent to the norm of `W^{1,N}(Ω)`.
[brezis2011functional] Chapter 9, Remark 15. -/
theorem SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_eq_finrank
    [Fact (1 ≤ (N : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N N Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hN : 2 ≤ N) {q : ℝ≥0}
    (hq : 1 ≤ q) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 N Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 N Ω, gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_mul_ofReal_of_exists_forall
    (hΩ.exists_forall_eLpNorm_fn_le_of_eq_finrank hN (q := max q (N + 1)) (le_max_of_le_right
      (by exact_mod_cast Nat.le_succ N)))
  have hNlt : ((N : ℝ≥0) : ℝ≥0∞) < ((max q (N + 1) : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast lt_max_of_lt_right (by exact_mod_cast Nat.lt_succ_self N)
  exact SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le hb.measure_lt_top.ne
    (by exact_mod_cast hq) (by exact_mod_cast le_max_left q (N + 1)) hNlt hK hKu

/-- **Remark 15, case `p > N`**: for a bounded extension domain, `N < p < ∞` and `1 ≤ q ≤ ∞`,
the norm `‖∇u‖_p + ‖u‖_q` is equivalent to the norm of `W^{1,p}(Ω)`.
[brezis2011functional] Chapter 9, Remark 15. -/
theorem SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_gt
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hp : N < p) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_mul_ofReal_of_exists_forall
    (hΩ.exists_forall_eLpNorm_fn_top_le hp)
  exact SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le hb.measure_lt_top.ne hq le_top
    ENNReal.coe_lt_top hK hKu

end Remark15
