import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.Sobolev.Compactness
import NumlibSurface.Brezis.Chapter09.Section02

/-!
# Brezis §9.3: Sobolev inequalities

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §9.3, on `ℝ^N = EuclideanSpace ℝ (Fin N)` with Lebesgue
measure.

**A. The case `Ω = ℝ^N`.** Theorem 9.9 (Sobolev–Gagliardo–Nirenberg, `1 ≤ p < N`), Remark 10
(the scaling argument), Corollary 9.10 (`p ≤ q ≤ p*`), Corollary 9.11 (`p = N`), Theorem 9.12
(Morrey, `p > N`) with Remarks 11–12, Corollary 9.13 (`W^{m,p}(ℝ^N)`) and Remark 13
(`W^{N,1} ⊂ L^∞`). The backbone is `Numlib/Analysis/Sobolev/Embedding`.

**B. The case `Ω ⊂ ℝ^N`**, for `Ω` of class `C^1` with bounded boundary or `Ω = ℝ^N_+`
(`IsClassC1BoundedFrontierOrHalfSpace`): Corollary 9.14 (three cases and the Hölder estimate,
`W^{1,p}(Ω) ⊂ C(Ω̄)`), Corollary 9.15 (`W^{m,p}(Ω) ⊂ C^k(Ω̄)`, footnote 16, in the sense of
`ContDiffOnClosure`), Theorem 9.16 (Rellich–Kondrachov, for `Ω` bounded of class `C^1`),
Remark 14 (i), Remark 15. The backbone is `Numlib/Analysis/Sobolev/EmbeddingDomain` (through
the extension operator of §9.2, packaged as `IsSobolevExtensionDomain`) and
`Numlib/Analysis/Sobolev/Compactness`. The dimension is written `N = d + 1` in this part, as in
§9.2.

## Conventions

* "`W^{m,p}(Ω) ⊂ L^q(Ω)` with continuous injection" is `IsContinuousInjectionLp N m p q Ω`: the
  functions of `W^{m,p}(Ω)` lie in `L^q(Ω)` and the inclusion `u ↦ fn u` is an
  `IsContinuousEmbedding` (`Numlib/Analysis/Normed/Operator/Embedding`), equivalently
  `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{m,p}(Ω)}` (`isContinuousInjectionLp_iff`); "with compact injection"
  is `IsCompactInjectionLp`.
* The exponent `p* = Np/(N − p)` is written by its defining equation `1/p* = 1/p − 1/N` in
  `ℝ≥0`, as Mathlib does; `1 ≤ p` is the instance `[Fact (1 ≤ (p : ℝ≥0∞))]` of the type.
* `‖∇u‖_p` is `eLpNorm (gradient u) p`, the `L^p` norm of the Euclidean norm of the gradient
  vector `(∂_1 u, …, ∂_N u)` (§9.1), and `‖u‖_{W^{1,p}}`, `‖u‖_{W^{m,p}}` are the book's norms
  `bookNorm`, `bookNormHigher`.
* The book's "a.e. `x, y`" estimates are stated for a continuous representative, everywhere, and
  restated literally as `∀ᵐ x, ∀ᵐ y`.
* The higher-order statements (Corollaries 9.13 and 9.15) carry the hypothesis `2 ≤ N ∨ 1 < p`,
  and the cases `p = N` of Corollary 9.14 and Theorem 9.16 the hypothesis `N ≥ 2`: for `N = 1`,
  `p = 1` the chain of first-order embeddings the book invokes is stuck at `W^{1,1}(ℝ) ⊂ L^∞(ℝ)`,
  which is chapter 8's Theorem 8.8 and not a case of Corollary 9.11; the last sentence of
  Theorem 9.16 leaves out `N = 1 = p` likewise (`p ≠ 1 ∨ 1 ≤ d`), that case being
  Theorem 8.8 (7).

## Main results

* `IsContinuousInjectionLp`, `IsCompactInjectionLp`, `isContinuousInjectionLp_iff` — the
  vocabulary.
* `theorem_9_9`, `corollary_9_10`, `corollary_9_11`, `theorem_9_12`, `theorem_9_12_top`,
  `remark_9_11`, `remark_9_12`, `corollary_9_13` (with `corollary_9_13_lt`, `_eq`, `_gt`,
  `_holder`), `remark_9_13` — the whole space.
* `IsClassC1BoundedFrontierOrHalfSpace`, `corollary_9_14` (with `_lt`, `_eq`, `_gt`, `_holder`),
  `corollary_9_15_lp`, `corollary_9_15_ck`, `toContinuousMapClosure`, `theorem_9_16` (with
  `_lt`, `_eq`, `_gt`, `_self`), `remark_9_15` (with `_lt`, `_eq`, `_gt`) — the domain.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

/-! ### Continuous and compact injections into `L^q(Ω)` -/

/-- **"`W^{m,p}(Ω) ⊂ L^q(Ω)` with continuous injection"**, the conclusion of the Sobolev
embedding theorems of §9.3: every function of `W^{m,p}(Ω)` lies in `L^q(Ω)`, and the inclusion
`u ↦ fn u`, `W^{m,p}(Ω) → L^q(Ω)` (`SobolevMultiIndex.toLpₗ`), is a continuous embedding —
injective and bounded, `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{m,p}(Ω)}` (`isContinuousInjectionLp_iff`). -/
def IsContinuousInjectionLp (N m : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ h : ∀ u : sobolevSpaceHigher N m p Ω,
      MemLp (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    IsContinuousEmbedding (SobolevMultiIndex.toLpₗ ℝ
      (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) m p Ω volume h)

/-- **"`W^{m,p}(Ω) ⊂ L^q(Ω)` with compact injection"**, the conclusion of the Rellich–Kondrachov
theorem: the inclusion `u ↦ fn u` is a compact embedding (`IsCompactEmbedding`: continuous, and
every bounded sequence of `W^{m,p}(Ω)` has a subsequence whose functions converge in `L^q(Ω)`). -/
def IsCompactInjectionLp (N m : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ h : ∀ u : sobolevSpaceHigher N m p Ω,
      MemLp (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    IsCompactEmbedding (SobolevMultiIndex.toLpₗ ℝ
      (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) m p Ω volume h)

section WholeSpace

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`, as a `Basis`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

variable {m : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The book's reading of a continuous injection**: `W^{m,p}(Ω) ⊂ L^q(Ω)` with continuous
injection if and only if every `u ∈ W^{m,p}(Ω)` lies in `L^q(Ω)` and there is a constant `C` with
`‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{m,p}(Ω)}` for all `u`. -/
theorem isContinuousInjectionLp_iff :
    IsContinuousInjectionLp N m p q Ω ↔
      (∀ u : sobolevSpaceHigher N m p Ω,
        MemLp (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher N m p Ω,
        eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))
          ≤ ENNReal.ofReal (C * ‖u‖) := by
  constructor
  · rintro ⟨h, hemb⟩
    obtain ⟨c, hc⟩ := hemb.exists_bound
    refine ⟨h, max c 0, le_max_right _ _, fun u ↦ ?_⟩
    have h1 := hc u
    rw [SobolevMultiIndex.toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp] at h1
    rw [← ENNReal.ofReal_toReal (h u).eLpNorm_ne_top]
    refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · rintro ⟨h, C, hC0, hC⟩
    refine ⟨h, SobolevMultiIndex.isContinuousEmbedding_toLpₗ h (C := C) fun u ↦ ?_⟩
    rw [SobolevMultiIndex.toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp,
      ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ C * ‖u‖)]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC u)

/-- A compact injection is a continuous injection. -/
theorem IsCompactInjectionLp.isContinuousInjectionLp (h : IsCompactInjectionLp N m p q Ω) :
    IsContinuousInjectionLp N m p q Ω :=
  let ⟨h, hc⟩ := h
  ⟨h, hc.toIsContinuousEmbedding⟩

omit [Fact (1 ≤ q)] in
/-- `W^{m,p}(Ω) ⊂ L^p(Ω)` with continuous injection, trivially (`SobolevMultiIndex.fnL`). -/
theorem isContinuousInjectionLp_self : IsContinuousInjectionLp N m p p Ω :=
  ⟨fun u ↦ SobolevMultiIndex.memLp u, by
    rw [SobolevMultiIndex.toLpₗ_self]
    exact SobolevMultiIndex.isContinuousEmbedding_fnL⟩

/-! ### The gradient norm and the partial derivatives -/

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- `‖∂_i u‖_{L^p(Ω)} ≤ ‖∇u‖_{L^p(Ω)}`: a component of the gradient is bounded by its Euclidean
norm. -/
theorem eLpNorm_partialDeriv_le (u : sobolevSpace N p Ω) (i : Fin N) :
    eLpNorm (partialDeriv u i) p (volume.restrict (Ω : Set 𝔼))
      ≤ eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) :=
  eLpNorm_mono_ae (Lp.aestronglyMeasurable _)
    (Eventually.of_forall fun x ↦ PiLp.norm_apply_le (gradient u x) i)

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- The `L^p(Ω)` norm of `∂_i u`, as an `ℝ≥0∞`. -/
theorem ofReal_norm_partialDeriv (u : sobolevSpace N p Ω) (i : Fin N) :
    ENNReal.ofReal ‖partialDeriv u i‖
      = eLpNorm (partialDeriv u i) p (volume.restrict (Ω : Set 𝔼)) := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- `∑_i ‖∂_i u‖_{L^p(Ω)} ≤ N ‖∇u‖_{L^p(Ω)}`. -/
theorem sum_ofReal_norm_partialDeriv_le (u : sobolevSpace N p Ω) :
    ∑ i, ENNReal.ofReal ‖partialDeriv u i‖
      ≤ N * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  calc ∑ i, ENNReal.ofReal ‖partialDeriv u i‖
      ≤ ∑ _i : Fin N, eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) :=
        Finset.sum_le_sum fun i _ ↦ by
          rw [ofReal_norm_partialDeriv]
          exact eLpNorm_partialDeriv_le u i
    _ = N * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [Fact (1 ≤ q)] in
/-- `‖∇u‖_{L^p(Ω)} ≤ ∑_i ‖∂_i u‖_{L^p(Ω)}`: the Euclidean norm of the gradient is at most the sum
of the absolute values of its components. -/
theorem eLpNorm_gradient_le_sum (u : sobolevSpace N p Ω) :
    eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))
      ≤ ∑ i, ENNReal.ofReal ‖partialDeriv u i‖ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  calc eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))
      ≤ eLpNorm (fun x ↦ ∑ i, ‖partialDeriv u i x‖) p (volume.restrict (Ω : Set 𝔼)) :=
        eLpNorm_mono_ae (aestronglyMeasurable_gradient u) (Eventually.of_forall fun x ↦ by
          rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
          exact PiLp.norm_le_sum_norm (gradient u x))
    _ = eLpNorm (∑ i, fun x ↦ ‖partialDeriv u i x‖) p (volume.restrict (Ω : Set 𝔼)) := by
        congr 1
        funext x
        simp only [Finset.sum_apply]
    _ ≤ ∑ i, eLpNorm (fun x ↦ ‖partialDeriv u i x‖) p (volume.restrict (Ω : Set 𝔼)) :=
        eLpNorm_sum_le_of_norm hp
    _ = ∑ i, ENNReal.ofReal ‖partialDeriv u i‖ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [eLpNorm_norm _ (Lp.aestronglyMeasurable _), ofReal_norm_partialDeriv]

omit [Fact (1 ≤ q)] in
/-- The backbone's `ℓ^p` gradient norm `SobolevMultiIndex.gradNorm u = (∑ ‖∂_i u‖_p^p)^{1/p}` is
at most `N ‖∇u‖_{L^p(Ω)}`. -/
theorem gradNorm_le_eLpNorm_gradient (u : sobolevSpace N p Ω) :
    SobolevMultiIndex.gradNorm u
      ≤ N * (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal := by
  have h1 : SobolevMultiIndex.gradNorm u ≤ ∑ i, ‖partialDeriv u i‖ :=
    PiLp.norm_le_sum_norm (SobolevMultiIndex.grad u)
  refine h1.trans ?_
  have h2 := sum_ofReal_norm_partialDeriv_le u
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _] at h2
  have hfin : (N : ℝ≥0∞) * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (memLp_gradient u).eLpNorm_ne_top
  have := ENNReal.toReal_mono hfin h2
  rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at this

omit [Fact (1 ≤ q)] in
/-- `‖∇u‖_{L^p(Ω)}` is at most `N` times the backbone's `ℓ^p` gradient norm. -/
theorem toReal_eLpNorm_gradient_le_gradNorm (u : sobolevSpace N p Ω) :
    (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
      ≤ N * SobolevMultiIndex.gradNorm u := by
  have h2 := eLpNorm_gradient_le_sum u
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _] at h2
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at this
  refine this.trans ?_
  calc ∑ i, ‖partialDeriv u i‖ ≤ ∑ _i : Fin N, SobolevMultiIndex.gradNorm u :=
        Finset.sum_le_sum fun i _ ↦ SobolevMultiIndex.norm_weakDeriv_single_le_gradNorm u i
    _ = N * SobolevMultiIndex.gradNorm u := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


/-! ### Theorem 9.9: the Sobolev–Gagliardo–Nirenberg inequality -/

section GNS

variable {p p' q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Theorem 9.9 (Sobolev, Gagliardo, Nirenberg).** Let `1 ≤ p < N`. Then
`W^{1,p}(ℝ^N) ⊂ L^{p*}(ℝ^N)`, where `p*` is given by `1/p* = 1/p − 1/N`, with continuous
injection, and there is a constant `C = C(p, N)` such that `‖u‖_{p*} ≤ C ‖∇u‖_p` for all
`u ∈ W^{1,p}(ℝ^N)`. The backbone's `SobolevEuclidean.isContinuousEmbedding_toLp_of_eq` and
`SobolevEuclidean.eLpNorm_fn_le_of_eq`, from Mathlib's inequality for compactly supported `C^1`
functions by density and Fatou's lemma; the constant is `N` times Mathlib's
`SNormLESNormFDerivOfEqConst` (`SobolevEuclidean.gnsConst`), footnote 9's `(N − 1)p/(N − p)` not
being carried. -/
theorem theorem_9_9 [Fact (1 ≤ (p' : ℝ≥0∞))] (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) :
    IsContinuousInjectionLp N 1 p p' ⊤ ∧ ∃ C : ℝ≥0, ∀ u : sobolevSpace N p ⊤,
      eLpNorm (SobolevMultiIndex.fn u) p' volume ≤ C * eLpNorm (gradient u) p volume := by
  refine ⟨⟨fun u ↦ by
      simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_of_eq hpN hp' u,
    SobolevEuclidean.isContinuousEmbedding_toLp_of_eq hpN hp'⟩, SobolevEuclidean.gnsConst N p * N,
    fun u ↦ ?_⟩
  refine (SobolevEuclidean.eLpNorm_fn_le_of_eq hpN hp' u).trans ?_
  have h := sum_ofReal_norm_partialDeriv_le u
  rw [eLpNorm_restrict_coe_top] at h
  push_cast
  rw [mul_assoc]
  exact mul_le_mul' le_rfl h

/-- **Corollary 9.10.** Let `1 ≤ p < N`. Then `W^{1,p}(ℝ^N) ⊂ L^q(ℝ^N)` for all `q ∈ [p, p*]`
with continuous injection. The backbone's `SobolevEuclidean.isContinuousEmbedding_toLp_of_le_of_le`,
by the interpolation inequality `‖u‖_q ≤ ‖u‖_p^α ‖u‖_{p*}^{1−α} ≤ ‖u‖_p + ‖u‖_{p*}` (Remark 2 of
chapter 4 and Young's inequality) and Theorem 9.9. -/
theorem corollary_9_10 [Fact (1 ≤ (q : ℝ≥0∞))] (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (hpq : p ≤ q) (hqp' : q ≤ p') : IsContinuousInjectionLp N 1 p q ⊤ :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_le_of_le hpN hp' hpq hqp'⟩

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- **Corollary 9.11 (the limiting case `p = N`).** `W^{1,N}(ℝ^N) ⊂ L^q(ℝ^N)` for all
`q ∈ [N, +∞)`, with continuous injection, the constant depending on `q` and `N` (footnote 11).
The book's proof uses `N' = N/(N − 1)`, so `N ≥ 2`. The backbone's
`SobolevEuclidean.isContinuousEmbedding_toLp_of_eq_finrank`, the `|u|^{m−1} u` iteration
(20)–(23). -/
theorem corollary_9_11 [Fact (1 ≤ (N : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) : IsContinuousInjectionLp N 1 N q ⊤ :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_eq_finrank hN hq⟩

end GNS

/-! ### Theorem 9.12: Morrey's theorem -/

section Morrey

variable {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Theorem 9.12 (Morrey), the injection and the bound (24).** Let `N < p < ∞`. Then
`W^{1,p}(ℝ^N) ⊂ L^∞(ℝ^N)` with continuous injection, `‖u‖_∞ ≤ C ‖u‖_{W^{1,p}}`. The backbone's
`SobolevEuclidean.eLpNorm_fn_top_le_of_lt` (Morrey's estimate on balls, the constant
`MeasureTheory.morreySupConst`). -/
theorem theorem_9_12_top_le (hp : (N : ℝ≥0) < p) :
    IsContinuousInjectionLp N 1 p ⊤ ⊤ ∧ ∃ C : ℝ, ∀ u : sobolevSpace N p ⊤,
      eLpNorm (SobolevMultiIndex.fn u) ⊤ volume ≤ ENNReal.ofReal (C * bookNorm u) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞,
    K = morreySupConst (volume : Measure 𝔼) p * (N + 1) := ⟨_, rfl⟩
  have hKt : K ≠ ⊤ := hK ▸ ENNReal.mul_ne_top (morreySupConst_ne_top _ _) (by simp)
  have hbound : ∀ u : sobolevSpace N p ⊤,
      eLpNorm (SobolevMultiIndex.fn u) ⊤ volume ≤ ENNReal.ofReal (K.toReal * ‖u‖) := fun u ↦ by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKt, hK]
    exact SobolevEuclidean.eLpNorm_fn_top_le_of_lt hp u
  refine ⟨isContinuousInjectionLp_iff.2 ⟨fun u ↦ by
      simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_top_of_lt hp u,
      K.toReal, ENNReal.toReal_nonneg, fun u ↦ by
        simpa [Measure.restrict_coe_top] using hbound u⟩, K.toReal, fun u ↦ ?_⟩
  exact (hbound u).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (bookNorm_equiv u).1 ENNReal.toReal_nonneg))

/-- **Theorem 9.12 (Morrey), the estimate (25).** Let `N < p < ∞` and `α = 1 − N/p`. There is a
constant `C = C(p, N)` such that every `u ∈ W^{1,p}(ℝ^N)` has a continuous representative `ũ`
with `|ũ(x) − ũ(y)| ≤ C |x − y|^α ‖∇u‖_p` for all `x, y ∈ ℝ^N`; hence
`|u(x) − u(y)| ≤ C |x − y|^α ‖∇u‖_p` for a.e. `x, y ∈ ℝ^N`. The backbone's
`SobolevEuclidean.exists_continuous_ae_eq_of_lt` (the average over balls, the constant
`MeasureTheory.morreyConst`). -/
theorem theorem_9_12_holder (hp : (N : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∀ u : sobolevSpace N p ⊤, ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧
      SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
      (∀ x y, ‖ũ x - ũ y‖ₑ ≤ C * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
        * eLpNorm (gradient u) p volume) ∧
      ∀ᵐ x, ∀ᵐ y, ‖SobolevMultiIndex.fn u x - SobolevMultiIndex.fn u y‖ₑ
        ≤ C * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ))) * eLpNorm (gradient u) p volume := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = morreyConst (volume : Measure 𝔼) p * N := ⟨_, rfl⟩
  have hKt : K ≠ ⊤ := hK ▸ ENNReal.mul_ne_top (morreyConst_ne_top _ _) (by simp)
  refine ⟨K.toNNReal, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, hhold, -, -⟩ := SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u
  have hsum := sum_ofReal_norm_partialDeriv_le u
  rw [eLpNorm_restrict_coe_top] at hsum
  have hbound : ∀ x y, ‖ũ x - ũ y‖ₑ ≤ K.toNNReal * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
      * eLpNorm (gradient u) p volume := fun x y ↦ by
    refine (hhold x y).trans ?_
    rw [ENNReal.coe_toNNReal hKt, hK]
    calc morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
          * ∑ i, ENNReal.ofReal ‖SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)‖
        ≤ morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
          * (N * eLpNorm (gradient u) p volume) := mul_le_mul' le_rfl hsum
      _ = _ := by ring
  refine ⟨ũ, hc, hae, hbound, ?_⟩
  filter_upwards [hae] with x hx
  filter_upwards [hae] with y hy
  rw [hx, hy]
  exact hbound x y

/-- **Theorem 9.12 (Morrey).** Let `N < p < ∞`. Then `W^{1,p}(ℝ^N) ⊂ L^∞(ℝ^N)` with continuous
injection, `‖u‖_∞ ≤ C ‖u‖_{W^{1,p}}` (24); furthermore, for all `u ∈ W^{1,p}(ℝ^N)`,
`|u(x) − u(y)| ≤ C |x − y|^α ‖∇u‖_p` a.e. `x, y ∈ ℝ^N` (25), where `α = 1 − N/p` and `C`
depends only on `p` and `N`. The case `p = ∞` is `theorem_9_12_top`. -/
theorem theorem_9_12 (hp : (N : ℝ≥0) < p) :
    IsContinuousInjectionLp N 1 p ⊤ ⊤ ∧
    (∃ C : ℝ, ∀ u : sobolevSpace N p ⊤,
      eLpNorm (SobolevMultiIndex.fn u) ⊤ volume ≤ ENNReal.ofReal (C * bookNorm u)) ∧
    ∃ C : ℝ≥0, ∀ u : sobolevSpace N p ⊤, ∀ᵐ x, ∀ᵐ y,
      ‖SobolevMultiIndex.fn u x - SobolevMultiIndex.fn u y‖ₑ
        ≤ C * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ))) * eLpNorm (gradient u) p volume := by
  obtain ⟨h1, h2⟩ := theorem_9_12_top_le hp
  obtain ⟨C, hC⟩ := theorem_9_12_holder hp
  exact ⟨h1, h2, C, fun u ↦ (hC u).choose_spec.2.2.2⟩

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- **Theorem 9.12 for `p = ∞`.** `W^{1,∞}(ℝ^N) ⊂ L^∞(ℝ^N)` with continuous injection (the
inclusion is the identity on the function), and every `u ∈ W^{1,∞}(ℝ^N)` has a representative
`ũ` with `|ũ(x) − ũ(y)| ≤ ‖∇u‖_∞ |x − y|` for all `x, y` — the estimate (25) with `α = 1`,
which is Remark 7 (`remark_9_7_convex`) on the convex set `ℝ^N`. -/
theorem theorem_9_12_top :
    IsContinuousInjectionLp N 1 ⊤ ⊤ ⊤ ∧ ∀ u : sobolevSpace N ⊤ ⊤, ∃ ũ : 𝔼 → ℝ,
      SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
      ∀ x y, |ũ x - ũ y| ≤ (eLpNorm (gradient u) ⊤ volume).toReal * ‖x - y‖ := by
  refine ⟨isContinuousInjectionLp_self, fun u ↦ ?_⟩
  obtain ⟨ũ, hae, hlip⟩ := remark_9_7_convex (Ω := ⊤) (convex_univ) u
  refine ⟨ũ, eventuallyEq_restrict_coe_top_iff.1 hae, fun x y ↦ ?_⟩
  have := hlip x trivial y trivial
  rwa [eLpNorm_restrict_coe_top] at this

/-- **Remark 11.** For `N < p < ∞`, every `u ∈ W^{1,p}(ℝ^N)` admits a continuous representative:
there is a *unique* continuous `ũ : ℝ^N → ℝ` with `u = ũ` a.e. on `ℝ^N` (two continuous
functions that agree almost everywhere agree everywhere). The book thereafter denotes the
representative by `u`; the backbone bundles it as `SobolevEuclidean.contRep`. -/
theorem remark_9_11 (hp : (N : ℝ≥0) < p) (u : sobolevSpace N p ⊤) :
    ∃! ũ : 𝔼 → ℝ, Continuous ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ := by
  refine ⟨SobolevEuclidean.contRep hp u, ⟨(SobolevEuclidean.contRep hp u).continuous,
    SobolevEuclidean.fn_ae_eq_contRep hp u⟩, fun g ⟨hgc, hg⟩ ↦ ?_⟩
  exact Measure.eq_of_ae_eq (μ := volume) (hg.symm.trans (SobolevEuclidean.fn_ae_eq_contRep hp u))
    hgc (SobolevEuclidean.contRep hp u).continuous

/-- **Remark 12.** If `u ∈ W^{1,p}(ℝ^N)` with `N < p < ∞`, then `lim_{|x| → ∞} u(x) = 0` for the
continuous representative `ũ` of Remark 11: `ũ` is the uniform limit of the `C_c^1` approximants,
by (24). The last clause of the backbone's `SobolevEuclidean.exists_continuous_ae_eq_of_lt`. -/
theorem remark_9_12 (hp : (N : ℝ≥0) < p) (u : sobolevSpace N p ⊤) :
    ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
      Tendsto ũ (cocompact 𝔼) (𝓝 0) :=
  ⟨SobolevEuclidean.contRep hp u, (SobolevEuclidean.contRep hp u).continuous,
    SobolevEuclidean.fn_ae_eq_contRep hp u, SobolevEuclidean.tendsto_contRep_cocompact hp u⟩

end Morrey

/-! ### Corollary 9.13: the spaces `W^{m,p}(ℝ^N)` -/

section HigherOrder

variable {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- The exponent bookkeeping of Corollary 9.13: `1/p − m/N < 0` reads `N/p < m`. -/
theorem div_lt_of_inv_sub_div_neg {m : ℕ} (hp : (0 : ℝ) < p)
    (hm : (p : ℝ)⁻¹ - m / N < 0) : (N : ℝ) / p < m := by
  have hN : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg N)
    rw [this, div_zero, sub_zero] at hm
    exact absurd hm (not_lt.2 (inv_pos.2 hp).le)
  rw [div_lt_iff₀ hp]
  have := (sub_neg.1 hm)
  rwa [inv_lt_iff_one_lt_mul₀ hp, div_mul_eq_mul_div, one_lt_div hN] at this

/-- **Corollary 9.13, first clause.** For `m ≥ 1` and `1 ≤ p < ∞` with `1/p − m/N > 0`,
`W^{m,p}(ℝ^N) ⊂ L^q(ℝ^N)` with continuous injection, where `1/q = 1/p − m/N`. The backbone's
`SobolevEuclidean.isContinuousEmbedding_toLp_of_order`, by induction on `m` ("repeated
applications of Theorem 9.9"). The hypothesis `N ≥ 2 ∨ p > 1` is the book's implicit one: the
chain of first-order embeddings is stuck at `W^{1,1}(ℝ)`, where Corollary 9.11 needs `N ≥ 2`. -/
theorem corollary_9_13_lt [Fact (1 ≤ (q : ℝ≥0∞))] {m : ℕ} (hN : 2 ≤ N ∨ 1 < p)
    (hpos : 0 < (p : ℝ)⁻¹ - m / N) (hq : (q : ℝ)⁻¹ = p⁻¹ - m / N) :
    IsContinuousInjectionLp N m p q ⊤ := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hq0 : (0 : ℝ) < q := by
    rw [← inv_pos, hq]
    exact hpos
  have hpq : p ≤ q := by
    rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hq0 hp0, hq]
    exact sub_le_self _ (by positivity)
  exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order hN hpq hq.ge⟩

/-- **Corollary 9.13, second clause.** For `m ≥ 1` and `1 ≤ p < ∞` with `1/p − m/N = 0`,
`W^{m,p}(ℝ^N) ⊂ L^q(ℝ^N)` with continuous injection for all `q ∈ [p, +∞)`. The backbone's
`SobolevEuclidean.isContinuousEmbedding_toLp_of_order` ("repeated applications of Theorem 9.9
and Corollary 9.11"); `N ≥ 2 ∨ p > 1` as in `corollary_9_13_lt`. -/
theorem corollary_9_13_eq [Fact (1 ≤ (q : ℝ≥0∞))] {m : ℕ} (hN : 2 ≤ N ∨ 1 < p)
    (hm : (p : ℝ)⁻¹ - m / N = 0) (hpq : p ≤ q) : IsContinuousInjectionLp N m p q ⊤ :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order hN hpq (hm ▸ by positivity)⟩

/-- **Corollary 9.13, third clause.** For `m ≥ 1` and `1 ≤ p < ∞` with `1/p − m/N < 0`,
`W^{m,p}(ℝ^N) ⊂ L^∞(ℝ^N)` with continuous injection. The backbone's
`SobolevEuclidean.isContinuousEmbedding_toLp_top_of_order` ("repeated applications of
Theorem 9.9 and Theorem 9.12"); `N ≥ 2 ∨ p > 1` as in `corollary_9_13_lt`. -/
theorem corollary_9_13_gt {m : ℕ} (hN : 2 ≤ N ∨ 1 < p) (hm : (p : ℝ)⁻¹ - m / N < 0) :
    IsContinuousInjectionLp N m p ⊤ ⊤ := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_top_of_order hN
    (div_lt_of_inv_sub_div_neg hp0 hm)⟩

/-- **Corollary 9.13, the `C^k` clause (footnotes 12–14).** Let `m ≥ 1`, `1 ≤ p < ∞`, and
suppose `m − N/p > 0` is not an integer; set `k = [m − N/p]` (the integer part) and
`θ = m − N/p − k ∈ (0, 1)`. Then there is `C` such that every `u ∈ W^{m,p}(ℝ^N)` has a
representative `ũ` of class `C^k` with `‖D^α ũ‖_∞ ≤ C ‖u‖_{W^{m,p}}` for `|α| ≤ k` (stated for
the full derivative tensors `D^j ũ`, `j ≤ k`, which bound every component `D^α ũ`) and
`|D^α ũ(x) − D^α ũ(y)| ≤ C ‖u‖_{W^{m,p}} |x − y|^θ` for `|α| = k` and all `x, y`, hence a.e.; in
particular `W^{m,p}(ℝ^N) ⊂ C^k(ℝ^N)` modulo the choice of a representative. The backbone's
`SobolevEuclidean.exists_contDiff_ae_eq_of_order`; `N ≥ 2 ∨ p > 1` as in `corollary_9_13_lt`. -/
theorem corollary_9_13_holder {m : ℕ} (hN : 2 ≤ N ∨ 1 < p) (hm : 0 < (m : ℝ) - N / p)
    (hint : ∀ j : ℕ, (m : ℝ) - N / p ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher N m p ⊤, ∃ ũ : 𝔼 → ℝ,
      ContDiff ℝ ⌊(m : ℝ) - N / p⌋₊ ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
      (∀ j ≤ ⌊(m : ℝ) - N / p⌋₊, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * bookNormHigher u) ∧
      ∀ x y, ‖iteratedFDeriv ℝ ⌊(m : ℝ) - N / p⌋₊ ũ x - iteratedFDeriv ℝ ⌊(m : ℝ) - N / p⌋₊ ũ y‖
        ≤ C * bookNormHigher u * ‖x - y‖ ^ ((m : ℝ) - N / p - ⌊(m : ℝ) - N / p⌋₊) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊(m : ℝ) - N / p⌋₊ := ⟨_, rfl⟩
  have hθ0 : 0 < (m : ℝ) - N / p - k := by
    rw [hk]
    exact lt_of_le_of_ne (sub_nonneg.2 (Nat.floor_le hm.le)) fun h ↦ hint _ (sub_eq_zero.1 h.symm)
  have hθ1 : (m : ℝ) - N / p - k < 1 := by
    rw [hk, sub_lt_iff_lt_add, add_comm]
    exact Nat.lt_floor_add_one _
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_contDiff_ae_eq_of_order (N := N) (m := m) (k := k)
    hN hθ0 hθ1
  rw [← hk]
  refine ⟨C, hC0, fun u ↦ ?_⟩
  obtain ⟨ũ, hũ, hae, hb, hh⟩ := hC u
  have hnorm : C * ‖u‖ ≤ C * bookNormHigher u :=
    mul_le_mul_of_nonneg_left (bookNormHigher_equiv u).1 hC0
  refine ⟨ũ, hũ, hae, fun j hj x ↦ (hb j hj x).trans hnorm, fun x y ↦ (hh x y).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (norm_nonneg _) _)

/-- **Corollary 9.13.** Let `m ≥ 1` be an integer and `p ∈ [1, +∞)`. Then
`W^{m,p}(ℝ^N) ⊂ L^q(ℝ^N)` where `1/q = 1/p − m/N`, if `1/p − m/N > 0`;
`W^{m,p}(ℝ^N) ⊂ L^q(ℝ^N)` for all `q ∈ [p, +∞)`, if `1/p − m/N = 0`;
`W^{m,p}(ℝ^N) ⊂ L^∞(ℝ^N)`, if `1/p − m/N < 0`; all these injections are continuous. Moreover,
if `m − N/p > 0` is not an integer, with `k = [m − N/p]` and `θ = m − N/p − k`, every
`u ∈ W^{m,p}(ℝ^N)` has a `C^k` representative whose derivatives of order `≤ k` are bounded by
`C ‖u‖_{W^{m,p}}` and whose derivatives of order `k` are `θ`-Hölder with constant
`C ‖u‖_{W^{m,p}}`; in particular `W^{m,p}(ℝ^N) ⊂ C^k(ℝ^N)`. The hypothesis `N ≥ 2 ∨ p > 1` is
the book's implicit one (see `corollary_9_13_lt`); the case `m = N`, `p = 1` is Remark 13. -/
theorem corollary_9_13 {m : ℕ} (hN : 2 ≤ N ∨ 1 < p) :
    (∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], 0 < (p : ℝ)⁻¹ - m / N →
      (q : ℝ)⁻¹ = p⁻¹ - m / N → IsContinuousInjectionLp N m p q ⊤) ∧
    ((p : ℝ)⁻¹ - m / N = 0 → ∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLp N m p q ⊤) ∧
    ((p : ℝ)⁻¹ - m / N < 0 → IsContinuousInjectionLp N m p ⊤ ⊤) ∧
    (0 < (m : ℝ) - N / p → (∀ j : ℕ, (m : ℝ) - N / p ≠ j) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher N m p ⊤, ∃ ũ : 𝔼 → ℝ,
        ContDiff ℝ ⌊(m : ℝ) - N / p⌋₊ ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
        (∀ j ≤ ⌊(m : ℝ) - N / p⌋₊, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * bookNormHigher u) ∧
        ∀ x y, ‖iteratedFDeriv ℝ ⌊(m : ℝ) - N / p⌋₊ ũ x
            - iteratedFDeriv ℝ ⌊(m : ℝ) - N / p⌋₊ ũ y‖
          ≤ C * bookNormHigher u * ‖x - y‖ ^ ((m : ℝ) - N / p - ⌊(m : ℝ) - N / p⌋₊)) :=
  ⟨fun _ _ hpos hq ↦ corollary_9_13_lt hN hpos hq, fun hm _ _ hpq ↦ corollary_9_13_eq hN hm hpq,
    corollary_9_13_gt hN, corollary_9_13_holder hN⟩

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- **Remark 13.** The case `p = 1` and `m = N` is special: `W^{N,1}(ℝ^N) ⊂ L^∞(ℝ^N)` with
continuous injection, `‖u‖_∞ ≤ C ‖u‖_{W^{N,1}}` (with `C = 1`), and every `u ∈ W^{N,1}(ℝ^N)`
has a continuous representative `ũ` with `|ũ(x)| ≤ ‖u‖_{W^{N,1}}`. The backbone's
`SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one`: for `u ∈ C_c^∞`,
`u(x) = ∫_{−∞}^{x_1} ⋯ ∫_{−∞}^{x_N} ∂^N u/∂x_1 ⋯ ∂x_N`, so
`‖u‖_∞ ≤ ‖∂_1 ⋯ ∂_N u‖_1 ≤ ‖u‖_{W^{N,1}}`,
and the general case follows by density. The remark's negative clause (`W^{m,p} ⊄ L^∞` in
general for `p > 1`, `m = N/p`) is not formalized. -/
theorem remark_9_13 :
    IsContinuousInjectionLp N N 1 ⊤ ⊤ ∧ ∀ u : sobolevSpaceHigher N N 1 ⊤, ∃ ũ : 𝔼 → ℝ,
      Continuous ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧ ∀ x, |ũ x| ≤ bookNormHigher u := by
  have hbound : ∀ u : sobolevSpaceHigher N N 1 ⊤,
      eLpNorm (SobolevMultiIndex.fn u) ⊤ volume ≤ ENNReal.ofReal (1 * ‖u‖) := fun u ↦ by
    obtain ⟨ũ, hc, hae, hb⟩ := SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one u
    rw [eLpNorm_congr_ae hae, one_mul]
    refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal ‖u‖) hc.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb x)
  have hmem : ∀ u : sobolevSpaceHigher N N 1 ⊤, MemLp (SobolevMultiIndex.fn u) ⊤ volume :=
    fun u ↦ memLp_iff.2 ((hbound u).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨isContinuousInjectionLp_iff.2 ⟨fun u ↦ ?_, 1, zero_le_one, fun u ↦ ?_⟩, fun u ↦ ?_⟩
  · simpa [Measure.restrict_coe_top] using hmem u
  · simpa [Measure.restrict_coe_top] using hbound u
  · obtain ⟨ũ, hc, hae, hb⟩ := SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one u
    exact ⟨ũ, hc, hae, fun x ↦ (Real.norm_eq_abs _ ▸ hb x).trans (bookNormHigher_equiv u).1⟩

end HigherOrder

/-! ### Remark 15: from the backbone's gradient norm to the book's -/

section EquivNorm

omit [Fact (1 ≤ q)] in
/-- **The equivalence of norms of Remark 15, from the backbone's form to the book's**: if the norm
of `W^{1,p}(Ω)` is equivalent to `SobolevMultiIndex.gradNorm u + ‖u‖_q` (the `ℓ^p` gradient
norm), then the book's norm `‖u‖_{W^{1,p}}` is equivalent to `‖∇u‖_p + ‖u‖_q`, with the
Euclidean gradient norm `‖∇u‖_p = eLpNorm (gradient u) p` (§9.1): `‖u‖ ≤ ‖u‖_{W^{1,p}} ≤ (N+1) ‖u‖`
and `gradNorm u ≤ N ‖∇u‖_p ≤ N² gradNorm u`. -/
theorem bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add
    (h₁ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpace N p Ω, ‖u‖ ≤ C * (SobolevMultiIndex.gradNorm u
      + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal))
    (h₂ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpace N p Ω, SobolevMultiIndex.gradNorm u
      + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal ≤ C * ‖u‖) :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace N p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u := by
  obtain ⟨C, hC0, hC⟩ := h₁
  obtain ⟨C', hC'0, hC'⟩ := h₂
  refine ⟨(N + 1) * C * (N + 1), (N + 1) * C', fun u ↦ ⟨?_, ?_⟩⟩
  · have hg := gradNorm_le_eLpNorm_gradient u
    have hq0 : 0 ≤ (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal :=
      ENNReal.toReal_nonneg
    have hg0 : 0 ≤ (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal :=
      ENNReal.toReal_nonneg
    calc bookNorm u ≤ (N + 1) * ‖u‖ := (bookNorm_equiv u).2
      _ ≤ (N + 1) * (C * (SobolevMultiIndex.gradNorm u
          + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal)) :=
          mul_le_mul_of_nonneg_left (hC u) (by positivity)
      _ ≤ (N + 1) * (C * ((N + 1) * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
          + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal))) := by
          gcongr
          nlinarith
      _ = _ := by ring
  · have hg := toReal_eLpNorm_gradient_le_gradNorm u
    have hgn := SobolevMultiIndex.gradNorm_nonneg u
    have hq0 : 0 ≤ (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal :=
      ENNReal.toReal_nonneg
    calc (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
          + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
        ≤ (N + 1) * (SobolevMultiIndex.gradNorm u
          + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) := by
          nlinarith
      _ ≤ (N + 1) * (C' * ‖u‖) := mul_le_mul_of_nonneg_left (hC' u) (by positivity)
      _ ≤ (N + 1) * (C' * bookNorm u) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bookNorm_equiv u).1 hC'0)
            (by positivity)
      _ = _ := by ring

end EquivNorm
end WholeSpace




/-! ### Remark 10: the scaling argument -/

section Scaling

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **Scaling of the `L^q` norm**: for `t > 0`, `‖u(t ·)‖_q = t^{−N/q} ‖u‖_q` on `ℝ^N` (with
`N/q = 0` for `q = ∞`), from `d(tx) = t^N dx`. -/
theorem eLpNorm_comp_smul_eq {F : Type*} [NormedAddCommGroup F] {u : 𝔼 → F}
    (hu : AEStronglyMeasurable u volume) {t : ℝ} (ht : 0 < t) (q : ℝ≥0∞) :
    eLpNorm (fun x ↦ u (t • x)) q volume
      = ENNReal.ofReal (t ^ (-(N : ℝ) * (q⁻¹).toReal)) * eLpNorm u q volume := by
  have hmap : Measure.map (t • ·) (volume : Measure 𝔼)
      = ENNReal.ofReal |(t ^ N)⁻¹| • volume := by
    rw [Measure.map_addHaar_smul volume ht.ne', finrank_euclideanSpace_fin]
  have h1 : eLpNorm (fun x ↦ u (t • x)) q volume = eLpNorm u q (Measure.map (t • ·) volume) := by
    refine (eLpNorm_map_measure ?_ (measurable_const_smul t).aemeasurable).symm
    rw [hmap]
    exact hu.smul_measure _
  have hc0 : ENNReal.ofReal |(t ^ N)⁻¹| ≠ 0 := by
    rw [abs_of_pos (by positivity)]
    exact ENNReal.ofReal_pos.2 (by positivity) |>.ne'
  rw [h1, hmap, eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul, one_div,
    abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) ENNReal.toReal_nonneg]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_mul ht.le]

/-- The `L^p` norm of the gradient vector `∇u = (∂_1 u, …, ∂_N u)` of a `C^1` function equals the
`L^p` norm of its differential `x ↦ Du(x)`, the operator norm of `Du(x)` being the Euclidean norm
of `∇u(x)`. -/
theorem eLpNorm_gradientVec_eq {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ (WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) : 𝔼)) p
      volume = eLpNorm (fderiv ℝ u) p volume := by
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  refine eLpNorm_congr_norm_ae ?_ hd.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  · exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ hd.clm_apply
      continuous_const)).aestronglyMeasurable
  · exact (norm_eq_norm_toLp_apply_single (fderiv ℝ u x)).symm

/-- **Remark 10 (the scaling argument).** Assume that there are constants `C` and
`q ∈ [1, ∞]` such that `‖u‖_q ≤ C ‖∇u‖_p` for all `u ∈ C_c^∞(ℝ^N)`. Then necessarily
`q = p*`, i.e. `1/q = 1/p − 1/N`: plugging `u_λ(x) = u(λx)` into the inequality gives
`‖u‖_q ≤ C λ^{1 + N/q − N/p} ‖∇u‖_p` for all `λ > 0`, which forces `1 + N/q − N/p = 0` provided
`u` does not vanish identically. Here `∇u = (∂_1 u, …, ∂_N u)` and `1/q` is read as `0` for
`q = ∞`. -/
theorem remark_9_10 {p : ℝ≥0} (hp : 1 ≤ p) {q : ℝ≥0∞} (hq : 1 ≤ q) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ u : 𝔼 → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm u q volume ≤ C * eLpNorm
        (fun x ↦ (WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) : 𝔼)) p volume) :
    (q⁻¹).toReal = (p : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  have hp0' : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  -- a nonzero bump
  set u₀ : ContDiffBump (0 : 𝔼) := ⟨1, 2, one_pos, one_lt_two⟩ with hu₀
  have hu₀s : ContDiff ℝ ∞ u₀ := u₀.contDiff
  have hu₀c : HasCompactSupport u₀ := u₀.hasCompactSupport
  have hu₀0 : u₀ 0 = 1 := u₀.one_of_mem_closedBall (by simp [hu₀])
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = eLpNorm (u₀ : 𝔼 → ℝ) q volume := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = eLpNorm (fderiv ℝ (u₀ : 𝔼 → ℝ)) p volume := ⟨_, rfl⟩
  have hAt : A ≠ ⊤ := hA ▸ (u₀.continuous.memLp_of_hasCompactSupport hu₀c).eLpNorm_ne_top
  have hBt : B ≠ ⊤ := hB ▸ ((hu₀s.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
    (hu₀c.fderiv (𝕜 := ℝ))).eLpNorm_ne_top
  have hA0 : 0 < A.toReal := by
    refine ENNReal.toReal_pos (fun h0 ↦ ?_) hAt
    rw [hA, eLpNorm_eq_zero_iff (zero_lt_one.trans_le hq).ne'] at h0
    have := (u₀.continuous.ae_eq_iff_eq (μ := volume) continuous_const).1 h0
    have h00 : (u₀ : 𝔼 → ℝ) 0 = 0 := congrFun this 0
    rw [hu₀0] at h00
    exact one_ne_zero h00
  -- the scaled inequality `A ≤ D t^e`, `e = 1 + N/q − N/p`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (q⁻¹).toReal := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 + N * s - N * (p : ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C.toReal * B.toReal := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ by positivity
  have key : ∀ t : ℝ, 0 < t → A.toReal ≤ D * t ^ e := by
    intro t ht
    have hsm : ContDiff ℝ ∞ fun x : 𝔼 ↦ u₀ (t • x) :=
      hu₀s.comp (contDiff_const_smul t)
    have hcs : HasCompactSupport fun x : 𝔼 ↦ u₀ (t • x) := hu₀c.comp_smul ht.ne'
    have h1 := h _ hsm hcs
    rw [eLpNorm_gradientVec_eq (hsm.of_le (by simp))] at h1
    have hfd : fderiv ℝ (fun x : 𝔼 ↦ u₀ (t • x))
        = t • fun x ↦ fderiv ℝ (u₀ : 𝔼 → ℝ) (t • x) := by
      funext x
      exact fderiv_comp_smul t
    rw [hfd, eLpNorm_const_smul, eLpNorm_comp_smul_eq u₀.continuous.aestronglyMeasurable ht,
      eLpNorm_comp_smul_eq (hu₀s.continuous_fderiv (by simp)).aestronglyMeasurable ht, ← hA, ← hB,
      Real.enorm_eq_ofReal ht.le] at h1
    have hfin : C * (ENNReal.ofReal t * (ENNReal.ofReal (t ^ (-(N : ℝ) * (p⁻¹ : ℝ≥0∞).toReal))
        * B)) ≠ ⊤ :=
      ENNReal.mul_ne_top hC (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt))
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _), ENNReal.toReal_ofReal ht.le,
      ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _), ← hs, ← ENNReal.coe_inv hp0',
      ENNReal.coe_toReal, NNReal.coe_inv] at h2
    -- multiply by `t^{N s}`
    have hts : 0 < t ^ ((N : ℝ) * s) := Real.rpow_pos_of_pos ht _
    have h3 : t ^ (-(N : ℝ) * s) * t ^ ((N : ℝ) * s) = 1 := by
      rw [← Real.rpow_add ht, neg_mul, neg_add_cancel, Real.rpow_zero]
    have h4 : t * t ^ (-(N : ℝ) * (p : ℝ)⁻¹) * t ^ ((N : ℝ) * s) = t ^ e := by
      rw [he, show (1 : ℝ) + N * s - N * (p : ℝ)⁻¹ = 1 + (-(N : ℝ) * (p : ℝ)⁻¹) + N * s by ring,
        Real.rpow_add ht, Real.rpow_add ht, Real.rpow_one]
    calc A.toReal = t ^ (-(N : ℝ) * s) * A.toReal * t ^ ((N : ℝ) * s) := by
          rw [mul_comm _ A.toReal, mul_assoc, h3, mul_one]
      _ ≤ C.toReal * (t * (t ^ (-(N : ℝ) * (p : ℝ)⁻¹) * B.toReal)) * t ^ ((N : ℝ) * s) :=
          mul_le_mul_of_nonneg_right h2 hts.le
      _ = D * (t * t ^ (-(N : ℝ) * (p : ℝ)⁻¹) * t ^ ((N : ℝ) * s)) := by rw [hD]; ring
      _ = D * t ^ e := by rw [h4]
  -- the exponent must vanish
  have he0 : e = 0 := by
    by_contra hne
    rcases hD0.eq_or_lt with hD0' | hDpos
    · have := key 1 one_pos
      rw [← hD0', zero_mul] at this
      exact absurd this (not_le.2 hA0)
    · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (A.toReal / (2 * D)) ^ e⁻¹ := ⟨_, rfl⟩
      have htpos : 0 < t := ht ▸ Real.rpow_pos_of_pos (by positivity) _
      have hte : t ^ e = A.toReal / (2 * D) := ht ▸ Real.rpow_inv_rpow (by positivity) hne
      have h5 := key t htpos
      rw [hte] at h5
      have h6 : D * (A.toReal / (2 * D)) = A.toReal / 2 := by
        field_simp
      rw [h6] at h5
      linarith
  -- and `1 + N/q − N/p = 0` is `1/q = 1/p − 1/N`
  rw [← hs]
  rw [he0] at he
  have hN : (N : ℝ) ≠ 0 := by
    rintro hN0
    rw [hN0] at he
    linarith
  have h6 : (N : ℝ) * (s + (N : ℝ)⁻¹) = N * (p : ℝ)⁻¹ := by
    rw [mul_add, mul_inv_cancel₀ hN]
    linarith
  have := mul_left_cancel₀ hN h6
  linarith

end Scaling
/-! ### Remark 14 (i): the injection `W^{1,p}(ℝ^N) ⊂ L^p(ℝ^N)` is not compact -/

section NonCompact

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The translate `x ↦ φ(x − c)` of a `C^1` function with compact support**, as an element of
`W^{1,p}(ℝ^N)`: its function is the translate, and its `W^{1,p}` norm is that of `φ` (the Lebesgue
measure is translation invariant). -/
theorem exists_translate_mem_sobolevSpace {φ : 𝔼 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (c : 𝔼) :
    ∃ v : sobolevSpace N p ⊤, SobolevMultiIndex.fn v =ᵐ[volume] (fun x ↦ φ (x - c)) ∧
      bookNorm v = (eLpNorm φ p volume).toReal
        + ∑ i, (eLpNorm (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) p volume).toReal := by
  have hmp : MeasurePreserving (fun x : 𝔼 ↦ x - c) volume volume := measurePreserving_sub_right _ c
  have hφc' : HasCompactSupport fun x ↦ φ (x - c) := hφc.comp_homeomorph (Homeomorph.subRight c)
  have hφ' : ContDiff ℝ 1 fun x ↦ φ (x - c) := hφ.comp (contDiff_id.sub contDiff_const)
  have hd : ∀ i, HasCompactSupport fun x ↦ fderiv ℝ φ (x - c) (EuclideanSpace.single i 1) := by
    intro i
    have h1 : HasCompactSupport fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : 𝔼 →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) rfl
    exact h1.comp_homeomorph (Homeomorph.subRight c)
  have hdc : ∀ i, Continuous fun x ↦ fderiv ℝ φ (x - c) (EuclideanSpace.single i 1) := fun i ↦
    ((hφ.continuous_fderiv one_ne_zero).comp (continuous_id.sub continuous_const)).clm_apply
      continuous_const
  obtain ⟨v, hv, hvd⟩ := remark_9_2 (Ω := ⊤) (p := p) hφ'.contDiffOn
    (by simpa [Measure.restrict_coe_top] using hφ'.continuous.memLp_of_hasCompactSupport hφc')
    fun i ↦ by
      simp only [fderiv_comp_sub]
      simpa [Measure.restrict_coe_top] using (hdc i).memLp_of_hasCompactSupport (hd i)
  refine ⟨v, eventuallyEq_restrict_coe_top_iff.1 hv, ?_⟩
  have h0 : eLpNorm (fun x ↦ φ (x - c)) p volume = eLpNorm φ p volume :=
    eLpNorm_comp_measurePreserving hφ.continuous.aestronglyMeasurable hmp
  rw [bookNorm, Lp.norm_def, SobolevMultiIndex.weakDeriv_zero, eLpNorm_restrict_coe_top,
    eLpNorm_congr_ae (eventuallyEq_restrict_coe_top_iff.1 hv), h0]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Lp.norm_def, eLpNorm_restrict_coe_top, eLpNorm_congr_ae (eventuallyEq_restrict_coe_top_iff.1
    (hvd i))]
  simp only [fderiv_comp_sub]
  congr 1
  exact eLpNorm_comp_measurePreserving (g := fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable hmp

/-- **Remark 14 (i).** If `Ω` is not bounded, the injection `W^{1,p}(Ω) ⊂ L^p(Ω)` is, in
general, not compact: for `Ω = ℝ^N`, `N ≥ 1`, and every `1 ≤ p ≤ ∞`, it is not a compact
injection. The translates `u_n(x) = φ(x − 5n e_1)` of a bump `φ ∈ C_c^∞(ℝ^N)` are bounded in
`W^{1,p}(ℝ^N)` (translation invariance) and, their supports being disjoint, pairwise at
`L^p` distance at least `‖φ‖_p`, so no subsequence converges in `L^p(ℝ^N)` — the argument of
chapter 4's Remark 12 (Exercise 4.33) in `N` dimensions. Remark 14 (ii) (the injection into
`L^{p*}` is never compact) is not formalized. -/
theorem remark_9_14_i (hN : 0 < N) : ¬ IsCompactInjectionLp N 1 p p ⊤ := by
  rintro ⟨h, hc⟩
  -- the bump and its translates
  set φ : ContDiffBump (0 : 𝔼) := ⟨1, 2, one_pos, one_lt_two⟩ with hφ
  have hφs : ContDiff ℝ 1 φ := φ.contDiff
  have hφc : HasCompactSupport φ := φ.hasCompactSupport
  have hφ0 : φ 0 = 1 := φ.one_of_mem_closedBall (by simp [hφ])
  have hφp : 0 < eLpNorm (φ : 𝔼 → ℝ) p volume := by
    refine pos_iff_ne_zero.2 fun h0 ↦ ?_
    rw [eLpNorm_eq_zero_iff (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'] at h0
    have := (φ.continuous.ae_eq_iff_eq (μ := volume) continuous_const).1 h0
    have h00 : (φ : 𝔼 → ℝ) 0 = 0 := congrFun this 0
    rw [hφ0] at h00
    exact one_ne_zero h00
  have hφt : eLpNorm (φ : 𝔼 → ℝ) p volume ≠ ⊤ :=
    (φ.continuous.memLp_of_hasCompactSupport hφc).eLpNorm_ne_top
  obtain ⟨e, he⟩ : ∃ e : 𝔼, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, hN⟩ 1, by simp⟩
  set c : ℕ → 𝔼 := fun n ↦ (5 * n : ℝ) • e with hcdef
  have hcd : ∀ a b : ℕ, a ≠ b → 5 ≤ dist (c a) (c b) := by
    intro a b hab
    rw [dist_eq_norm, hcdef]
    simp only [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs, ← mul_sub, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    have : (1 : ℝ) ≤ |(a : ℝ) - b| := by
      rcases lt_or_gt_of_ne hab with h | h
      · have hab' : (a : ℝ) < b := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_pos (sub_pos.2 hab')]
        have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
        linarith
      · have hab' : (b : ℝ) < a := by exact_mod_cast h
        rw [abs_of_pos (sub_pos.2 hab')]
        have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
        linarith
    linarith
  choose v hv hvn using fun n ↦ exists_translate_mem_sobolevSpace (p := p) hφs hφc (c n)
  -- the translates are bounded in `W^{1,p}`
  have hbdd : ∃ M : ℝ, ∀ n, ‖v n‖ ≤ M :=
    ⟨_, fun n ↦ (bookNorm_equiv (v n)).1.trans (hvn n).le⟩
  obtain ⟨ψ, w, hψ, hw⟩ := hc.exists_subseq_tendsto v hbdd
  -- and pairwise separated in `L^p`
  have hsep : ∀ a b : ℕ, a ≠ b → eLpNorm (φ : 𝔼 → ℝ) p volume
      ≤ eLpNorm (SobolevMultiIndex.fn (v a) - SobolevMultiIndex.fn (v b)) p volume := by
    intro a b hab
    have hzero : ∀ x ∈ closedBall (c a) 2, φ (x - c b) = 0 := fun x hx ↦ by
      refine φ.zero_of_le_dist ?_
      rw [dist_zero_right, ← dist_eq_norm]
      have h1 := hcd a b hab
      have h2 := dist_triangle (c a) x (c b)
      rw [mem_closedBall, dist_comm] at hx
      simp only [hφ]
      linarith
    have hsupp : Function.support (fun x ↦ φ (x - c a)) ⊆ closedBall (c a) 2 := fun x hx ↦ by
      rw [mem_closedBall]
      by_contra hlt
      refine hx (φ.zero_of_le_dist ?_)
      rw [dist_zero_right, ← dist_eq_norm]
      simp only [hφ]
      exact (not_le.1 hlt).le
    have hmp : MeasurePreserving (fun x : 𝔼 ↦ x - c a) volume volume :=
      measurePreserving_sub_right _ (c a)
    have hae : SobolevMultiIndex.fn (v a) - SobolevMultiIndex.fn (v b)
        =ᵐ[volume] fun x ↦ φ (x - c a) - φ (x - c b) := by
      filter_upwards [hv a, hv b] with x hxa hxb
      simp [hxa, hxb]
    calc eLpNorm (φ : 𝔼 → ℝ) p volume
        = eLpNorm (fun x ↦ φ (x - c a)) p volume :=
          (eLpNorm_comp_measurePreserving (p := p) φ.continuous.aestronglyMeasurable hmp).symm
      _ = eLpNorm (fun x ↦ φ (x - c a)) p (volume.restrict (closedBall (c a) 2)) :=
          (eLpNorm_restrict_eq_of_support_subset
            (φ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
            hsupp).symm
      _ = eLpNorm (fun x ↦ φ (x - c a) - φ (x - c b)) p (volume.restrict (closedBall (c a) 2)) := by
          refine eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_closedBall fun x hx ↦ ?_)
          simp only [hzero x hx, sub_zero]
      _ ≤ eLpNorm (fun x ↦ φ (x - c a) - φ (x - c b)) p volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = _ := (eLpNorm_congr_ae hae).symm
  -- a convergent subsequence would be Cauchy, against the separation
  have hcs := hw.cauchySeq
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.1 hcs (eLpNorm (φ : 𝔼 → ℝ) p volume).toReal
    (ENNReal.toReal_pos hφp.ne' hφt)
  have h1 := hM (M + 1) (Nat.le_succ M)
  have hne : ψ (M + 1) ≠ ψ M := hψ.injective.ne (Nat.succ_ne_self M)
  have h2 := hsep _ _ hne
  rw [Lp.dist_def] at h1
  have hcoe : ⇑(SobolevMultiIndex.toLpₗ ℝ
        (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) 1 p ⊤ volume h
        (v (ψ (M + 1))))
      - ⇑(SobolevMultiIndex.toLpₗ ℝ
        (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) 1 p ⊤ volume h (v (ψ M)))
      =ᵐ[volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)]
        SobolevMultiIndex.fn (v (ψ (M + 1))) - SobolevMultiIndex.fn (v (ψ M)) := by
    filter_upwards [SobolevMultiIndex.toLpₗ_coeFn h (v (ψ (M + 1))),
      SobolevMultiIndex.toLpₗ_coeFn h (v (ψ M))] with x hxa hxb
    simp [hxa, hxb]
  rw [eLpNorm_congr_ae hcoe, eLpNorm_restrict_coe_top] at h1
  have hfin : eLpNorm (SobolevMultiIndex.fn (v (ψ (M + 1))) - SobolevMultiIndex.fn (v (ψ M))) p
      volume ≠ ⊤ :=
    ((SobolevEuclidean.memLp_fn (v (ψ (M + 1)))).sub
      (SobolevEuclidean.memLp_fn (v (ψ M)))).eLpNorm_ne_top
  exact absurd (ENNReal.toReal_mono hfin h2) (not_le.2 h1)

end NonCompact
/-! ### B. The case `Ω ⊂ ℝ^N` -/

section Domain

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- **The standing hypothesis of §9.3.B**: "we suppose here that `Ω` is an open set of class
`C^1` with `Γ` bounded, or else that `Ω = ℝ^N_+`". Both give the extension operator
`P : W^{1,p}(Ω) → W^{1,p}(ℝ^N)` of Theorem 9.7 for every `p` (`isSobolevExtensionDomainAll`),
which is all that the proofs of Corollaries 9.14–9.15 use. -/
def IsClassC1BoundedFrontierOrHalfSpace (Ω : Opens 𝔼) : Prop :=
  (IsClassC1 (Ω : Set 𝔼) ∧ Bornology.IsBounded (frontier (Ω : Set 𝔼))) ∨
    Ω = EuclideanSpace.upperHalfSpaceOpens d

/-- A bounded open set of class `C^1` satisfies the standing hypothesis of §9.3.B. -/
theorem isClassC1BoundedFrontierOrHalfSpace_of_isBounded {Ω : Opens 𝔼}
    (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    IsClassC1BoundedFrontierOrHalfSpace Ω :=
  Or.inl ⟨hΩ, hb.closure.subset frontier_subset_closure⟩

/-- The half space satisfies the standing hypothesis of §9.3.B. -/
theorem isClassC1BoundedFrontierOrHalfSpace_upperHalfSpace :
    IsClassC1BoundedFrontierOrHalfSpace (EuclideanSpace.upperHalfSpaceOpens d) :=
  Or.inr rfl

/-- Under the standing hypothesis of §9.3.B, `Ω` is a `W^{1,q}`-extension domain for every
`1 ≤ q ≤ ∞`: Theorem 9.7 for `Ω` of class `C^1` with bounded boundary
(`IsSobolevExtensionDomainAll.of_isContDiffChartDomain`), Lemma 9.2 for the half space
(`IsSobolevExtensionDomain.upperHalfSpace`). -/
theorem IsClassC1BoundedFrontierOrHalfSpace.isSobolevExtensionDomainAll {Ω : Opens 𝔼}
    (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω) : IsSobolevExtensionDomainAll (d + 1) Ω := by
  rcases hΩ with ⟨h1, h2⟩ | rfl
  · exact IsSobolevExtensionDomainAll.of_isContDiffChartDomain h1 h2
  · intro q _
    exact IsSobolevExtensionDomain.upperHalfSpace

/-- Under the standing hypothesis of §9.3.B, `Ω` is a `W^{1,p}`-extension domain. -/
theorem IsClassC1BoundedFrontierOrHalfSpace.isSobolevExtensionDomain {Ω : Opens 𝔼}
    (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsSobolevExtensionDomain (d + 1) p Ω :=
  hΩ.isSobolevExtensionDomainAll p

/-! ### Corollary 9.14 -/

variable {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Corollary 9.14, case `p < N`.** Under the standing hypothesis of §9.3.B, for `1 ≤ p < N`
and `1/p* = 1/p − 1/N`, `W^{1,p}(Ω) ⊂ L^{p*}(Ω)` with continuous injection — stated, as
Corollary 9.10, for every `q ∈ [p, p*]`. The extension operator of Theorem 9.7 followed by
Theorem 9.9: the backbone's
`SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_lt`. -/
theorem corollary_9_14_lt [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    {p' : ℝ≥0} (hpN : p < ((d + 1 : ℕ) : ℝ≥0)) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹)
    (hpq : p ≤ q) (hqp' : q ≤ p') : IsContinuousInjectionLp (d + 1) 1 p q Ω :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_lt
    (hΩ.isSobolevExtensionDomain p) hpN hp' hpq hqp'⟩

/-- **Corollary 9.14, case `p = N`.** Under the standing hypothesis of §9.3.B and for `N ≥ 2`,
`W^{1,N}(Ω) ⊂ L^q(Ω)` with continuous injection for all `q ∈ [N, +∞)`. The extension operator
followed by Corollary 9.11 (whose proof needs `N ≥ 2`; for `N = 1` the statement is chapter 8's
Theorem 8.8): the backbone's
`SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_eq`. -/
theorem corollary_9_14_eq [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hd : 1 ≤ d) (hp : p = ((d + 1 : ℕ) : ℝ≥0)) (hq : p ≤ q) :
    IsContinuousInjectionLp (d + 1) 1 p q Ω := by
  subst hp
  have : Fact (1 ≤ ((d + 1 : ℕ) : ℝ≥0∞)) := ‹_›
  exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_eq
    (hΩ.isSobolevExtensionDomain _) (by omega) hq⟩

/-- **Corollary 9.14, case `p > N`, the injection.** Under the standing hypothesis of §9.3.B and
for `N < p < ∞`, `W^{1,p}(Ω) ⊂ L^∞(Ω)` with continuous injection. The extension operator
followed by Theorem 9.12: the backbone's
`SobolevEuclidean.isContinuousEmbedding_toLp_top_of_hasSobolevExtension_of_lt`. -/
theorem corollary_9_14_gt (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) : IsContinuousInjectionLp (d + 1) 1 p ⊤ Ω :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_top_of_hasSobolevExtension_of_lt
    (hΩ.isSobolevExtensionDomain p) hp⟩

/-- **Corollary 9.14, case `p > N`, the Hölder estimate and `W^{1,p}(Ω) ⊂ C(Ω̄)`.** Under the
standing hypothesis of §9.3.B and for `N < p < ∞`, with `α = 1 − N/p`, there is
`C = C(Ω, p, N)` such that every `u ∈ W^{1,p}(Ω)` has a representative `ũ` continuous on `Ω̄`
(footnote 15: `W^{1,p}(Ω) ⊂ C(Ω̄)` modulo the choice of a representative) with
`|ũ(x) − ũ(y)| ≤ C ‖u‖_{W^{1,p}} |x − y|^α` for all `x, y ∈ Ω̄`, hence
`|u(x) − u(y)| ≤ C ‖u‖_{W^{1,p}} |x − y|^α` for a.e. `x, y ∈ Ω`. The backbone's
`SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq` (whose representative is in fact
continuous and Hölder on all of `ℝ^N`: it is Morrey's representative of `P u`). -/
theorem corollary_9_14_holder (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpace (d + 1) p Ω, ∃ ũ : 𝔼 → ℝ,
      ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
        |ũ x - ũ y| ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p)) ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
        |SobolevMultiIndex.fn u x - SobolevMultiIndex.fn u y|
          ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p) := by
  obtain ⟨C, hC⟩ := SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq
    (hΩ.isSobolevExtensionDomain p) hp
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hα : ((1 - ((d + 1 : ℕ) : ℝ≥0) / p : ℝ≥0) : ℝ) = 1 - ((d + 1 : ℕ) : ℝ) / p := by
    rw [NNReal.coe_sub ((div_le_one (by exact_mod_cast hp0)).2 hp.le)]
    simp
  refine ⟨C, C.coe_nonneg, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, hh, -⟩ := hC u
  have hbound : ∀ x y, |ũ x - ũ y| ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p) := by
    intro x y
    have h1 := hh.dist_le x y
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, hα] at h1
    refine h1.trans ?_
    gcongr
    exact (bookNorm_equiv u).1
  refine ⟨ũ, hc.continuousOn, hae, fun x _ y _ ↦ hbound x y, ?_⟩
  filter_upwards [hae] with x hx
  filter_upwards [hae] with y hy
  rw [hx, hy]
  exact hbound x y

/-- **Corollary 9.14.** Let `Ω` be of class `C^1` with `Γ` bounded, or `Ω = ℝ^N_+`, and
`1 ≤ p < ∞`. Then `W^{1,p}(Ω) ⊂ L^{p*}(Ω)` (`1/p* = 1/p − 1/N`) if `p < N`;
`W^{1,p}(Ω) ⊂ L^q(Ω)` for all `q ∈ [p, +∞)` if `p = N` (and `N ≥ 2`, see `corollary_9_14_eq`);
`W^{1,p}(Ω) ⊂ L^∞(Ω)` if `p > N`; all these injections are continuous. Moreover, if `p > N`,
`|u(x) − u(y)| ≤ C ‖u‖_{W^{1,p}} |x − y|^α` a.e. `x, y ∈ Ω` with `α = 1 − N/p`, `C` depending
only on `Ω`, `p`, `N`; in particular `W^{1,p}(Ω) ⊂ C(Ω̄)`. The case `p = ∞` of the book's
`1 ≤ p ≤ ∞` is `theorem_9_12_top` on `ℝ^N` and is not restated on `Ω`. -/
theorem corollary_9_14 (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω) :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < ((d + 1 : ℕ) : ℝ≥0) →
      (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ → p ≤ q → q ≤ p' →
        IsContinuousInjectionLp (d + 1) 1 p q Ω) ∧
    (1 ≤ d → p = ((d + 1 : ℕ) : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLp (d + 1) 1 p q Ω) ∧
    (((d + 1 : ℕ) : ℝ≥0) < p → IsContinuousInjectionLp (d + 1) 1 p ⊤ Ω) ∧
    (((d + 1 : ℕ) : ℝ≥0) < p → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpace (d + 1) p Ω, ∃ ũ : 𝔼 → ℝ,
      ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
        |ũ x - ũ y| ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p)) ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
        |SobolevMultiIndex.fn u x - SobolevMultiIndex.fn u y|
          ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p)) :=
  ⟨fun _ _ _ hpN hp' hpq hqp' ↦ corollary_9_14_lt hΩ hpN hp' hpq hqp',
    fun hd hp _ _ hq ↦ corollary_9_14_eq hΩ hd hp hq, corollary_9_14_gt hΩ,
    corollary_9_14_holder hΩ⟩

/-! ### Corollary 9.15 -/

/-- **Corollary 9.15, the `L^q` clauses.** Under the standing hypothesis of §9.3.B, the first
three clauses of Corollary 9.13 hold with `ℝ^N` replaced by `Ω`: for `m ≥ 1`, `1 ≤ p < ∞`,
`W^{m,p}(Ω) ⊂ L^q(Ω)` with `1/q = 1/p − m/N` if `1/p − m/N > 0`, `W^{m,p}(Ω) ⊂ L^q(Ω)` for all
`q ∈ [p, +∞)` if `1/p − m/N = 0`, `W^{m,p}(Ω) ⊂ L^∞(Ω)` if `1/p − m/N < 0`, with continuous
injections; "by repeated application of Corollary 9.14" (footnote 17: no `W^{m,p}` extension
operator is used). The backbone's
`SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension` and
`SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension`;
`N ≥ 2 ∨ p > 1` as in `corollary_9_13_lt`. -/
theorem corollary_9_15_lp {m : ℕ} (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hN : 2 ≤ d + 1 ∨ 1 < p) :
    (∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], 0 < (p : ℝ)⁻¹ - m / (d + 1 : ℕ) →
      (q : ℝ)⁻¹ = p⁻¹ - m / (d + 1 : ℕ) → IsContinuousInjectionLp (d + 1) m p q Ω) ∧
    ((p : ℝ)⁻¹ - m / (d + 1 : ℕ) = 0 → ∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLp (d + 1) m p q Ω) ∧
    ((p : ℝ)⁻¹ - m / (d + 1 : ℕ) < 0 → IsContinuousInjectionLp (d + 1) m p ⊤ Ω) := by
  have hall := hΩ.isSobolevExtensionDomainAll
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  refine ⟨fun q _ hpos hq ↦ ?_, fun hm q _ hpq ↦ ?_, fun hm ↦ ?_⟩
  · have hq0 : (0 : ℝ) < q := by
      rw [← inv_pos, hq]
      exact hpos
    have hpq : p ≤ q := by
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hq0 hp0, hq]
      exact sub_le_self _ (by positivity)
    exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension hall hN
      hpq hq.ge⟩
  · exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension hall hN
      hpq (hm ▸ by positivity)⟩
  · obtain ⟨C, θ, hC0, -, -, -, hC⟩ :=
      SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension hall hN
        (div_lt_of_inv_sub_div_neg hp0 hm)
    refine isContinuousInjectionLp_iff.2 ⟨fun u ↦ ?_, C, hC0, fun u ↦ ?_⟩
    · exact SobolevEuclidean.memLp_fn_top_of_order_of_hasSobolevExtension hall hN
        (div_lt_of_inv_sub_div_neg hp0 hm) u
    · obtain ⟨ũ, hc, hae, hb, -⟩ := hC u
      rw [eLpNorm_congr_ae hae]
      refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (C * ‖u‖))
        hc.aestronglyMeasurable.restrict (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hb x)

/-- **Corollary 9.15, the `C^k(Ω̄)` clause (footnote 16).** Under the standing hypothesis of
§9.3.B, if `m − N/p > 0` is not an integer then `W^{m,p}(Ω) ⊂ C^k(Ω̄)` with `k = [m − N/p]`,
where `C^k(Ω̄) = {u ∈ C^k(Ω) : D^α u` has a continuous extension to `Ω̄` for all `|α| ≤ k}` is
`ContDiffOnClosure ℝ k · Ω` (`Numlib/Analysis/Calculus/ContDiffOnClosure`): every
`u ∈ W^{m,p}(Ω)` has a representative `ũ ∈ C^k(Ω̄)` with, on `Ω`, `‖D^j ũ‖ ≤ C ‖u‖_{W^{m,p}}` for
`j ≤ k` and `|D^k ũ(x) − D^k ũ(y)| ≤ C ‖u‖_{W^{m,p}} |x − y|^θ`, `θ = m − N/p − k`. The
backbone's `SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order`; `N ≥ 2 ∨ p > 1` as in
`corollary_9_13_lt`. -/
theorem corollary_9_15_ck {m : ℕ} (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hN : 2 ≤ d + 1 ∨ 1 < p) (hm : 0 < (m : ℝ) - (d + 1 : ℕ) / p)
    (hint : ∀ j : ℕ, (m : ℝ) - (d + 1 : ℕ) / p ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher (d + 1) m p Ω, ∃ ũ : 𝔼 → ℝ,
      ContDiffOnClosure ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ Ω ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      (∀ j ≤ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊, ∀ x ∈ (Ω : Set 𝔼),
        ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * bookNormHigher u) ∧
      ∀ x ∈ (Ω : Set 𝔼), ∀ y ∈ (Ω : Set 𝔼),
        ‖iteratedFDeriv ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ x
            - iteratedFDeriv ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ y‖
          ≤ C * bookNormHigher u
            * ‖x - y‖ ^ ((m : ℝ) - (d + 1 : ℕ) / p - ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ := ⟨_, rfl⟩
  have hθ0 : 0 < (m : ℝ) - (d + 1 : ℕ) / p - k := by
    rw [hk]
    exact lt_of_le_of_ne (sub_nonneg.2 (Nat.floor_le hm.le)) fun h ↦ hint _ (sub_eq_zero.1 h.symm)
  have hθ1 : (m : ℝ) - (d + 1 : ℕ) / p - k < 1 := by
    rw [hk, sub_lt_iff_lt_add']
    exact Nat.lt_floor_add_one _
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order
    (N := d + 1) (m := m) (k := k) hΩ.isSobolevExtensionDomainAll hN hθ0 hθ1
  rw [← hk]
  refine ⟨C, hC0, fun u ↦ ?_⟩
  obtain ⟨ũ, -, hũ, hae, hG, G, hGc, hGeq, hGh⟩ := hC u
  have hnorm : C * ‖u‖ ≤ C * bookNormHigher u :=
    mul_le_mul_of_nonneg_left (bookNormHigher_equiv u).1 hC0
  refine ⟨ũ, ⟨hũ, fun j hj ↦ ?_⟩, hae, fun j hj x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · obtain ⟨G', hG'c, hG'eq, -⟩ := hG j (by exact_mod_cast hj)
    exact ⟨G', hG'c.continuousOn, hG'eq.symm⟩
  · obtain ⟨G', -, hG'eq, hG'b⟩ := hG j hj
    rw [hG'eq hx]
    exact (hG'b x).trans hnorm
  · rw [hGeq hx, hGeq hy]
    exact (hGh x y).trans (mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (norm_nonneg _) _))


/-- **Corollary 9.15.** The conclusion of Corollary 9.13 remains true if `ℝ^N` is replaced by
`Ω` of class `C^1` with `Γ` bounded, or by `ℝ^N_+`: the three `L^q` clauses
(`corollary_9_15_lp`) and, for `m − N/p > 0` not an integer, `W^{m,p}(Ω) ⊂ C^k(Ω̄)` with
`k = [m − N/p]` in the sense of footnote 16 (`corollary_9_15_ck`). `N ≥ 2 ∨ p > 1` as in
`corollary_9_13_lt`. -/
theorem corollary_9_15 {m : ℕ} (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hN : 2 ≤ d + 1 ∨ 1 < p) :
    ((∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], 0 < (p : ℝ)⁻¹ - m / (d + 1 : ℕ) →
      (q : ℝ)⁻¹ = p⁻¹ - m / (d + 1 : ℕ) → IsContinuousInjectionLp (d + 1) m p q Ω) ∧
    ((p : ℝ)⁻¹ - m / (d + 1 : ℕ) = 0 → ∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLp (d + 1) m p q Ω) ∧
    ((p : ℝ)⁻¹ - m / (d + 1 : ℕ) < 0 → IsContinuousInjectionLp (d + 1) m p ⊤ Ω)) ∧
    (0 < (m : ℝ) - (d + 1 : ℕ) / p → (∀ j : ℕ, (m : ℝ) - (d + 1 : ℕ) / p ≠ j) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher (d + 1) m p Ω, ∃ ũ : 𝔼 → ℝ,
        ContDiffOnClosure ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ Ω ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
        (∀ j ≤ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊, ∀ x ∈ (Ω : Set 𝔼),
          ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * bookNormHigher u) ∧
        ∀ x ∈ (Ω : Set 𝔼), ∀ y ∈ (Ω : Set 𝔼),
          ‖iteratedFDeriv ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ x
              - iteratedFDeriv ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ y‖
            ≤ C * bookNormHigher u
              * ‖x - y‖ ^ ((m : ℝ) - (d + 1 : ℕ) / p - ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊)) :=
  ⟨corollary_9_15_lp hΩ hN, corollary_9_15_ck hΩ hN⟩
/-! ### Theorem 9.16: the Rellich–Kondrachov theorem -/

/-- **The injection `W^{1,p}(Ω) ⊂ C(Ω̄)`, `u ↦ ũ|_{Ω̄}`**, for a bounded open `Ω` of class `C^1`
and `N < p < ∞`: the restriction to the compact set `Ω̄` of the continuous representative of
Corollary 9.14 (`corollary_9_14_holder`), as a bounded linear map into `C(Ω̄, ℝ)` — the
backbone's `SobolevEuclidean.toContinuousMapL` on `closure Ω`. -/
noncomputable def toContinuousMapClosure (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hp : ((d + 1 : ℕ) : ℝ≥0) < p) :
    sobolevSpace (d + 1) p Ω →L[ℝ] C(closure (Ω : Set 𝔼), ℝ) :=
  haveI : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  SobolevEuclidean.toContinuousMapL
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure))
    hp (closure (Ω : Set 𝔼))

/-- The injection `W^{1,p}(Ω) ⊂ C(Ω̄)` is the continuous representative: for every `u`,
`toContinuousMapClosure u` is the restriction to `Ω̄` of a continuous `ũ` with `u = ũ` a.e. on
`Ω`. -/
theorem exists_continuous_ae_eq_toContinuousMapClosure (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hp : ((d + 1 : ℕ) : ℝ≥0) < p)
    (u : sobolevSpace (d + 1) p Ω) :
    ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      ∀ x : closure (Ω : Set 𝔼), toContinuousMapClosure hΩ hb hp u x = ũ x := by
  have : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  refine ⟨_, (SobolevEuclidean.contRep hp _).continuous,
    SobolevEuclidean.fn_ae_eq_toContinuousMapL (IsSobolevExtensionDomain.of_isContDiffChartDomain
      hΩ (hb.closure.subset frontier_subset_closure)) hp (closure (Ω : Set 𝔼)) u, fun x ↦ rfl⟩

/-- **Theorem 9.16 (Rellich–Kondrachov), case `p < N`.** For `Ω` bounded of class `C^1`,
`1 ≤ p < N` and `1/p* = 1/p − 1/N`, `W^{1,p}(Ω) ⊂ L^q(Ω)` with compact injection for all
`q ∈ [1, p*)`. Theorem 4.26 (Kolmogorov–M. Riesz–Fréchet) applied to `P(unit ball)`, through
Proposition 9.3's translation estimate and the interpolation inequality: the backbone's
`SobolevEuclidean.isCompactEmbedding_toLp_of_lt`. -/
theorem theorem_9_16_lt [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {p' : ℝ≥0} (hpN : p < ((d + 1 : ℕ) : ℝ≥0))
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹) (hqp' : q < p') :
    IsCompactInjectionLp (d + 1) 1 p q Ω :=
  ⟨_, SobolevEuclidean.isCompactEmbedding_toLp_of_lt hΩ hb hpN hp' hqp'⟩

/-- **Theorem 9.16 (Rellich–Kondrachov), case `p = N`.** For `Ω` bounded of class `C^1`, `N ≥ 2`,
`W^{1,N}(Ω) ⊂ L^q(Ω)` with compact injection for all `q ∈ [N, +∞)`: "the case `p = N` reduces
to the case `p < N`" (`W^{1,N}(Ω) ↪ W^{1,r}(Ω)` for an `r < N` with `r* > q`). The backbone's
`SobolevEuclidean.isCompactEmbedding_toLp_of_eq`. -/
theorem theorem_9_16_eq [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hd : 1 ≤ d) (hp : p = ((d + 1 : ℕ) : ℝ≥0))
    (hq : p ≤ q) : IsCompactInjectionLp (d + 1) 1 p q Ω := by
  obtain ⟨h, -⟩ := corollary_9_14_eq (isClassC1BoundedFrontierOrHalfSpace_of_isBounded hΩ hb) hd
    hp hq
  subst hp
  exact ⟨h, SobolevEuclidean.isCompactEmbedding_toLp_of_eq hΩ hb hd h⟩

/-- **Theorem 9.16 (Rellich–Kondrachov), case `p > N`.** For `Ω` bounded of class `C^1` and
`N < p < ∞`, the injection `W^{1,p}(Ω) ⊂ C(Ω̄)`, `u ↦ ũ|_{Ω̄}` (`toContinuousMapClosure`), is
compact: Corollary 9.14 (the unit ball is bounded and uniformly Hölder in `C(Ω̄)`) and the
Ascoli–Arzelà theorem. The backbone's
`SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt`. -/
theorem theorem_9_16_gt (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) :
    haveI : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
    IsCompactEmbedding (toContinuousMapClosure hΩ hb hp).toLinearMap := by
  have : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  exact SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt hΩ hb hp subset_closure

/-- **Theorem 9.16, "in particular `W^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection for all `p`
(and all `N`)"**, for `Ω` bounded of class `C^1` and `1 ≤ p < ∞` with `p ≠ 1` or `N ≥ 2`: the
three cases `p < N`, `p = N` (`N ≥ 2`) and `p > N` (through `C(Ω̄)`). The case `N = 1 = p`
(an interval) is Theorem 8.8 (7) of chapter 8 and is not covered. The backbone's
`SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one`. -/
theorem theorem_9_16_self (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hd : p ≠ 1 ∨ 1 ≤ d) : IsCompactInjectionLp (d + 1) 1 p p Ω :=
  ⟨_, SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one hΩ hb hd⟩

/-- **Theorem 9.16 (Rellich–Kondrachov).** Suppose that `Ω` is bounded and of class `C^1`,
`1 ≤ p < ∞`. Then the following injections are compact: `W^{1,p}(Ω) ⊂ L^q(Ω)` for all
`q ∈ [1, p*)`, `1/p* = 1/p − 1/N`, if `p < N`; `W^{1,p}(Ω) ⊂ L^q(Ω)` for all `q ∈ [p, +∞)` if
`p = N` (and `N ≥ 2`); `W^{1,p}(Ω) ⊂ C(Ω̄)` if `p > N`. In particular `W^{1,p}(Ω) ⊂ L^p(Ω)`
with compact injection for all `p` and all `N` (here: `p ≠ 1` or `N ≥ 2`). -/
theorem theorem_9_16 (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < ((d + 1 : ℕ) : ℝ≥0) →
      (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ → q < p' → IsCompactInjectionLp (d + 1) 1 p q Ω) ∧
    (1 ≤ d → p = ((d + 1 : ℕ) : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsCompactInjectionLp (d + 1) 1 p q Ω) ∧
    (∀ hp : ((d + 1 : ℕ) : ℝ≥0) < p,
      haveI : CompactSpace (closure (Ω : Set 𝔼)) :=
        isCompact_iff_compactSpace.1 hb.isCompact_closure
      IsCompactEmbedding (toContinuousMapClosure hΩ hb hp).toLinearMap) ∧
    (p ≠ 1 ∨ 1 ≤ d → IsCompactInjectionLp (d + 1) 1 p p Ω) :=
  ⟨fun _ _ _ hpN hp' hqp' ↦ theorem_9_16_lt hΩ hb hpN hp' hqp',
    fun hd hp _ _ hq ↦ theorem_9_16_eq hΩ hb hd hp hq, theorem_9_16_gt hΩ hb,
    theorem_9_16_self hΩ hb⟩

/-! ### Remark 15: equivalent norms -/

/-- **Remark 15, case `1 ≤ p < N`.** Let `Ω` be a bounded open set of class `C^1`. Then the norm
`‖∇u‖_p + ‖u‖_q` is equivalent to the `W^{1,p}` norm for `1 ≤ q ≤ p*`. The backbone's
`SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_lt` (Corollary 9.14, the
interpolation inequality and an absorption argument), read on the book's norms through
`bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add`. -/
theorem remark_9_15_lt (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {p' : ℝ≥0} (hpN : p < ((d + 1 : ℕ) : ℝ≥0)) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hqp' : q ≤ p') :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace (d + 1) p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u :=
  let ⟨h₁, h₂⟩ := SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_lt
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure))
    hb hpN hp' hq hqp'
  bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add h₁ h₂

/-- **Remark 15, case `p = N`.** Let `Ω` be a bounded open set of class `C^1`, `N ≥ 2`. Then the
norm `‖∇u‖_N + ‖u‖_q` is equivalent to the `W^{1,N}` norm for `1 ≤ q < ∞`. The backbone's
`SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_eq_finrank`. -/
theorem remark_9_15_eq (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hd : 1 ≤ d) (hp : p = ((d + 1 : ℕ) : ℝ≥0)) {q : ℝ≥0} (hq : 1 ≤ q) :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace (d + 1) p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u := by
  subst hp
  have : Fact (1 ≤ ((d + 1 : ℕ) : ℝ≥0∞)) := ‹_›
  obtain ⟨h₁, h₂⟩ := SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_eq_finrank
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure))
    hb (by omega) hq
  exact bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add h₁ h₂

/-- **Remark 15, case `p > N`.** Let `Ω` be a bounded open set of class `C^1`, `N < p < ∞`. Then
the norm `‖∇u‖_p + ‖u‖_q` is equivalent to the `W^{1,p}` norm for `1 ≤ q ≤ ∞`. The backbone's
`SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_gt`. -/
theorem remark_9_15_gt (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace (d + 1) p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u :=
  let ⟨h₁, h₂⟩ := SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_gt
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure))
    hb hp hq
  bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add h₁ h₂

/-- **Remark 15.** Let `Ω` be a bounded open set of class `C^1` and `1 ≤ p < ∞`. Then the norm
`‖∇u‖_p + ‖u‖_q` is equivalent to the `W^{1,p}` norm so long as `1 ≤ q ≤ p*` if `1 ≤ p < N`,
`1 ≤ q < ∞` if `p = N` (and `N ≥ 2`), `1 ≤ q ≤ ∞` if `p > N`. -/
theorem remark_9_15 (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hcase : (∃ p' : ℝ≥0, p < ((d + 1 : ℕ) : ℝ≥0) ∧ (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ ∧
        q ≤ p') ∨
      (1 ≤ d ∧ p = ((d + 1 : ℕ) : ℝ≥0) ∧ q ≠ ⊤) ∨ ((d + 1 : ℕ) : ℝ≥0) < p) :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace (d + 1) p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u := by
  rcases hcase with ⟨p', hpN, hp', hqp'⟩ | ⟨hd, hp, hqt⟩ | hp
  · exact remark_9_15_lt hΩ hb hpN hp' hq hqp'
  · lift q to ℝ≥0 using hqt
    exact remark_9_15_eq hΩ hb hd hp (by exact_mod_cast hq)
  · exact remark_9_15_gt hΩ hb hp hq

end Domain
end Brezis.Chapter09
