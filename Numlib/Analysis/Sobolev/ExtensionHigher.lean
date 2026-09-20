/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Extension.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Analysis.Calculus.ContDiffConstOffCompact
import Numlib.Analysis.Sobolev.Compactness
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.Analysis.Sobolev.Extension

/-!
# The extension operator at every order on a `C^k` domain

The higher-order extension theorem: for an open set `Ω ⊆ ℝ^N` of class `C^k` (`k ≥ 1`) with
bounded boundary and `1 ≤ p ≤ ∞`, there is a bounded linear extension operator
`P : W^{k,p}(Ω) → W^{k,p}(ℝ^N)` with `P u = u` on `Ω`
(`SobolevEuclidean.exists_extensionL_of_order`, `IsSobolevExtensionDomainOfOrder`), and with it
the density of the restrictions of `C_c^∞(ℝ^N)` functions in `W^{k,p}(Ω)` for `p < ∞`
(`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order`). The order-one case
is Brezis's Theorem 9.7 (`Numlib/Analysis/Sobolev/Extension.lean`); the higher-order operator is
the classical variant by *higher-order reflection* (Brezis, Comments on Chapter 9; Lions–Magenes;
Evans §5.4, remark after Theorem 1): on the half cylinder, `u` is extended across `x_N = 0` by

`(P u)(x', x_N) = ∑_{j} a_j u(x', λ_j x_N)`  for `x_N < 0`,

with distinct scales `λ_j ∈ [-1, 0)` and coefficients `a_j` solving the Vandermonde system
`∑_j a_j λ_j^i = 1`, `i < k`, so that the one-sided normal derivatives of order `< k` match on the
interface.

## The proof

* **The higher-order reflection at order one** (`hasWeakFDerivOn_higherReflection`): for
  `u ∈ W^{1,p}(V₊)` and `∑ a_j = 1`, `P u ∈ W^{1,p}(V)` with the expected piecewise derivative.
  This is proved as Lemma 9.2 is not: the cancellation across the interface that the even
  reflection enjoys is lost, and the identity is instead obtained by interior approximation. The
  even reflection `u^⋆ ∈ W^{1,p}(V)` (Lemma 9.2) is approximated near any compact piece of `V`
  by smooth functions `w_n` (`MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`); for smooth `w_n`
  the reflected function `P w_n = w_n + 1_{x_N < 0} g_n`, `g_n = ∑ a_j w_n ∘ S_j − w_n`, has
  the piecewise derivative as weak derivative (`hasWeakFDerivOn_indicator_neg_of_contDiff`, the
  gluing lemma: `g_n` vanishes on the interface, and `η(n x_N) g_n → 1_{x_N < 0} g_n` in
  `W^{1,1}`), and the identity passes to the limit
    (`hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one`).
* **Every order** (`MemSobolevMultiIndex.higherReflection_of_order`): induction on `k` through
  `memSobolevMultiIndex_succ_iff`; the tangential derivative of `P_a u` is `P_a (∂_i u)` and the
  normal one is `P_{aλ} (∂_N u)` with the coefficients `a_j λ_j`, which satisfy the Vandermonde
  conditions one order lower.
* **Transport along a `C^k` chart** (`MemSobolevMultiIndex.comp_diffeoOn_of_order`): `H^k` is
  preserved by composition with a `C^k` diffeomorphism, by induction on `k` with the chain rule
  `∂_i (w ∘ J) = ∑_l (∂_i J)_l (∂_l w) ∘ J` and the Leibniz rule for a `C^1` multiplier
  (`HasWeakIteratedLineDerivOn.mul_contDiffOn_one`, from the `C_c^1` test functions of Remark 1).
* **The closed graph theorem** (`SobolevMultiIndex.exists_continuousLinearMap_of_order`): the
  order-one operator `P₁` of Theorem 9.7, built with the higher-order reflection in place of the
  even one, maps the functions of `W^{k,p}(Ω)` into `W^{k,p}(ℝ^N)`; its restriction
  `W^{k,p}(Ω) → W^{k,p}(ℝ^N)` is then bounded by the closed graph theorem, since convergence in
  `W^{k,p}` implies convergence in `W^{1,p}` and `P₁` is continuous there. No constant is tracked
  through the transports.

Two further consequences, for `p = ∞` and for the integer case of the Sobolev embeddings, are
written here beside the extension operator and are to be relocated: the Rellich–Kondrachov
theorem at `p = ∞`, `W^{k,∞}(Ω) ⊂⊂ W^{l,∞}(Ω)` for `l < k` on a bounded `W^{1,∞}`-extension
domain (`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt`, by Arzelà–Ascoli on the
Lipschitz representatives), and the bounded inclusion `W^{m+1+j,p}(Ω) → W^{j+1,r}(Ω)` of an
extension domain for `1/p − m/N ≤ 1/r`
(`SobolevEuclidean.exists_continuousLinearMap_lower_of_order`, Corollary 9.15 at every order
through the closed graph theorem).

## References

[brezis2011functional], §9.2, Theorem 9.7 and Lemma 9.2; Comments on Chapter 9, 3 (the
higher-order extension); [han2009theoretical], Theorems 7.3.2 and 7.3.5.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace EuclideanSpace
open scoped ContDiff Distributions ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

/-! ### The closed graph theorem for Sobolev operators -/

section ClosedGraph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω Ω' : Opens E} {μ : Measure E}
  [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

namespace SobolevMultiIndex

/-- **The closed graph theorem for an operator between Sobolev spaces**: a linear map
`T : W^{k,p}(Ω) → W^{k',q}(Ω')` whose function `u ↦ fn (T u) ∈ L^q(Ω')` is a continuous function
of `u` is continuous. Both spaces are Banach, and the graph is closed because the inclusions
`W^{k,p} → L^p` are continuous and injective. -/
theorem continuous_of_fnL_comp_eq {k' : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (T : SobolevMultiIndex F b k p Ω μ →ₗ[ℝ] SobolevMultiIndex F b k' q Ω' μ)
    {G : SobolevMultiIndex F b k p Ω μ → Lp F q (μ.restrict (Ω' : Set E))} (hG : Continuous G)
    (hT : ∀ u, fnL F b k' q Ω' μ (T u) = G u) : Continuous T := by
  refine T.continuous_of_seq_closed_graph fun u x y hu hTu ↦ ?_
  have h1 : Tendsto (fun n ↦ fnL F b k' q Ω' μ (T (u n))) atTop (𝓝 (fnL F b k' q Ω' μ y)) :=
    ((fnL F b k' q Ω' μ).continuous.tendsto y).comp hTu
  have h2 : Tendsto (fun n ↦ fnL F b k' q Ω' μ (T (u n))) atTop
      (𝓝 (fnL F b k' q Ω' μ (T x))) := by
    simp only [hT]
    exact (hG.tendsto x).comp hu
  exact fnL_injective (tendsto_nhds_unique h1 h2)

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

end ClosedGraph

/-! ### Algebra of `MemSobolevMultiIndex`

The lemmas of this section duplicate `MemSobolevMultiIndex.add`, `.finset_sum` and
`memSobolevMultiIndex_zero_iff` of `Numlib/Analysis/PDE/Elliptic/Regularity.lean`, which this
backbone module cannot import; they are kept under the namespace `ExtensionHigher` to avoid the
clash. -/

namespace ExtensionHigher

section Algebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

/-- `W^{k,p}(Ω)` is closed under addition. -/
theorem memSobolevMultiIndex_add {f g : E → F} (hf : MemSobolevMultiIndex b f k p Ω μ)
    (hg : MemSobolevMultiIndex b g k p Ω μ) : MemSobolevMultiIndex b (f + g) k p Ω μ :=
  ⟨hf.1.add hg.1, fun α hα ↦
    let ⟨w₁, hw₁, hw₁p⟩ := hf.2 α hα
    let ⟨w₂, hw₂, hw₂p⟩ := hg.2 α hα
    ⟨w₁ + w₂, hw₁.add hw₂, hw₁p.add hw₂p⟩⟩

omit [OpensMeasurableSpace E] in
/-- `W^{k,p}(Ω)` is closed under scalar multiplication. -/
theorem memSobolevMultiIndex_const_smul {f : E → F} (hf : MemSobolevMultiIndex b f k p Ω μ)
    (c : ℝ) : MemSobolevMultiIndex b (c • f) k p Ω μ :=
  ⟨hf.1.const_smul c, fun α hα ↦
    let ⟨w, hw, hwp⟩ := hf.2 α hα
    ⟨c • w, hw.const_smul c, hwp.const_smul c⟩⟩

/-- `W^{k,p}(Ω)` is closed under finite sums. -/
theorem memSobolevMultiIndex_finset_sum {κ : Type*} (s : Finset κ) {f : κ → E → F}
    (hf : ∀ i ∈ s, MemSobolevMultiIndex b (f i) k p Ω μ) :
    MemSobolevMultiIndex b (∑ i ∈ s, f i) k p Ω μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨MemLp.zero, fun α _ ↦ ⟨0, HasWeakIteratedLineDerivOn.zero, MemLp.zero⟩⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact memSobolevMultiIndex_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- `W^{0,p}(Ω)` is `L^p(Ω)`. -/
theorem memSobolevMultiIndex_zero_iff [Fact (1 ≤ p)] [IsLocallyFiniteMeasure μ] {f : E → F} :
    MemSobolevMultiIndex b f 0 p Ω μ ↔ MemLp f p (μ.restrict (Ω : Set E)) := by
  refine ⟨fun h ↦ h.memLp, fun hf ↦ ⟨hf, fun α hα ↦ ?_⟩⟩
  have h0 : ∑ i, α i = 0 := Nat.le_zero.1 hα
  exact ⟨f, HasWeakIteratedLineDerivOn.of_length_eq_zero h0 _ (hf.locallyIntegrableOn Fact.out),
    hf⟩

end Algebra

end ExtensionHigher

/-! ### The Leibniz rule for a `C^1` multiplier -/

section LeibnizC1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `φ c` is `C^1` on the whole space for a test function `φ` on `Ω` and a `c` of class `C^1`
on `Ω`: it is `C^1` on `Ω` and vanishes on the open complement of the support of `φ`. -/
theorem TestFunction.contDiff_mul_of_contDiffOn (φ : 𝓓(Ω, ℝ)) {c : E → ℝ}
    (hc : ContDiffOn ℝ 1 c Ω) : ContDiff ℝ 1 fun x ↦ φ x * c x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ (Ω : Set E)
  · exact (φ.contDiff.of_le (by simp)).contDiffAt.mul (hc.contDiffAt (Ω.isOpen.mem_nhds hx))
  · have hx' : x ∉ tsupport φ := fun h ↦ hx (φ.tsupport_subset h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx'] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- **The Leibniz rule for a `C^1` multiplier**, at every exponent: if `w` is the weak
derivative of `f` along `y` on `Ω` and `c` is of class `C^1` on `Ω`, then `c f` has the weak
derivative `c w + (∂_y c) f` along `y`. The test functions of the defining identity may be taken
`C_c^1` (`HasWeakIteratedLineDerivOn.integral_smul_eq_of_contDiff_one`, Brezis's Remark 1), and
`φ c` is one. Unlike `HasWeakIteratedLineDerivOn.mul` no exponent enters: only the local
integrability of `f` and `w` is used. -/
theorem HasWeakIteratedLineDerivOn.mul_contDiffOn_one {y : E} {f w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] f w Ω μ) {c : E → ℝ} (hc : ContDiffOn ℝ 1 c Ω) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ c x * f x)
      (fun x ↦ c x * w x + fderiv ℝ c x y * f x) Ω μ := by
  have hcc : ContinuousOn c Ω := hc.continuousOn
  have hdc : ContinuousOn (fun x ↦ fderiv ℝ c x y) Ω :=
    ((hc.fderiv_of_isOpen Ω.isOpen (m := 0) le_rfl).continuousOn).clm_apply continuousOn_const
  have hlc : IsLocallyClosed (Ω : Set E) := Ω.isOpen.isLocallyClosed
  have hl1 : LocallyIntegrableOn (fun x ↦ c x * f x) Ω μ :=
    h.locallyIntegrableOn.continuousOn_mul hcc hlc
  have hl2 : LocallyIntegrableOn (fun x ↦ c x * w x + fderiv ℝ c x y * f x) Ω μ :=
    (h.locallyIntegrableOn_weakDeriv.continuousOn_mul hcc hlc).add
      (h.locallyIntegrableOn.continuousOn_mul hdc hlc)
  refine ⟨hl1, hl2, fun φ ↦ ?_⟩
  have key := h.integral_smul_eq_of_contDiff_one (φ.contDiff_mul_of_contDiffOn hc)
    φ.hasCompactSupport.mul_right (tsupport_mul_subset_left.trans φ.tsupport_subset)
  have hd : ∀ x ∈ (Ω : Set E), fderiv ℝ (fun x ↦ φ x * c x) x y
      = fderiv ℝ φ x y * c x + φ x * fderiv ℝ c x y := by
    intro x hx
    rw [fderiv_fun_mul ((φ.contDiff.differentiable (by simp)) x)
      ((hc.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hx))]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one] at key ⊢
  have I1 : IntegrableOn (fun x ↦ fderiv ℝ φ x y * (c x * f x)) Ω μ :=
    (hl1.integrable_smul_left_of_tsupport_subset (φ.fderivApply y).contDiff.continuous
      (φ.fderivApply y).hasCompactSupport (φ.fderivApply y).tsupport_subset).integrableOn
  have I2 : IntegrableOn (fun x ↦ φ x * (fderiv ℝ c x y * f x)) Ω μ :=
    ((h.locallyIntegrableOn.continuousOn_mul hdc hlc).integrable_smul_left_of_tsupport_subset
      φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset).integrableOn
  have I3 : IntegrableOn (fun x ↦ φ x * (c x * w x)) Ω μ :=
    ((h.locallyIntegrableOn_weakDeriv.continuousOn_mul hcc
      hlc).integrable_smul_left_of_tsupport_subset
      φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset).integrableOn
  have e1 : ∫ x in (Ω : Set E), fderiv ℝ (fun x ↦ φ x * c x) x y * f x ∂μ
      = (∫ x in (Ω : Set E), fderiv ℝ φ x y * (c x * f x) ∂μ)
        + ∫ x in (Ω : Set E), φ x * (fderiv ℝ c x y * f x) ∂μ := by
    rw [← integral_add I1 I2]
    refine setIntegral_congr_fun Ω.isOpen.measurableSet fun x hx ↦ ?_
    rw [hd x hx]
    ring
  have e2 : ∫ x in (Ω : Set E), φ x * (c x * w x + fderiv ℝ c x y * f x) ∂μ
      = (∫ x in (Ω : Set E), φ x * (c x * w x) ∂μ)
        + ∫ x in (Ω : Set E), φ x * (fderiv ℝ c x y * f x) ∂μ := by
    rw [← integral_add I3 I2]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  have e3 : ∫ x in (Ω : Set E), φ x * c x * w x ∂μ = ∫ x in (Ω : Set E), φ x * (c x * w x) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  rw [e1, e3] at key
  rw [e2]
  linear_combination key

end LeibnizC1

/-! ### Multipliers at every order -/

section Multiplier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}
  [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [Fact (1 ≤ p)]
  [μ.IsAddHaarMeasure] in
/-- A bounded measurable multiple of an `L^p` function is in `L^p`. -/
theorem ExtensionHigher.memLp_mul_of_forall_abs_le {c f : E → ℝ}
    (hc : AEStronglyMeasurable c (μ.restrict (Ω : Set E))) {C : ℝ} (hC : ∀ x, |c x| ≤ C)
    (hf : MemLp f p (μ.restrict (Ω : Set E))) :
    MemLp (fun x ↦ c x * f x) p (μ.restrict (Ω : Set E)) :=
  hf.of_ae_norm_le_mul (hc.mul hf.aestronglyMeasurable) (Eventually.of_forall fun x ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _))

/-- **Multiplication by a `C^k` multiplier preserves `W^{k,p}(Ω)`**, `1 ≤ p ≤ ∞`: for a multiplier
`c` (`IsContDiffConstOffCompact k c`, of class `C^k` and constant off a compact set) and
`f ∈ W^{k,p}(Ω)`, the product `c f` lies in `W^{k,p}(Ω)`. By induction on `k` through
`memSobolevMultiIndex_succ_iff` and the Leibniz rule `∂_i (c f) = c ∂_i f + (∂_i c) f` for the
`C^1` factor `c` (`HasWeakIteratedLineDerivOn.mul_contDiffOn_one`); the `L^p` memberships come
from the bounds on `c` and `∂_i c`. The `H^k` version is
`MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact` of
`Numlib/Analysis/PDE/Elliptic/Regularity.lean`. -/
theorem ExtensionHigher.memSobolevMultiIndex_mul_of_isContDiffConstOffCompact (k : ℕ) :
    ∀ {c f : E → ℝ}, IsContDiffConstOffCompact k c → MemSobolevMultiIndex b f k p Ω μ →
    MemSobolevMultiIndex b (fun x ↦ c x * f x) k p Ω μ := by
  induction k with
  | zero =>
    intro c f hc hf
    rw [ExtensionHigher.memSobolevMultiIndex_zero_iff] at hf ⊢
    obtain ⟨C, hC⟩ := hc.exists_bound
    exact ExtensionHigher.memLp_mul_of_forall_abs_le hc.continuous.aestronglyMeasurable hC hf
  | succ k ih =>
    intro c f hc hf
    obtain ⟨hf0, hfd⟩ := memSobolevMultiIndex_succ_iff.1 hf
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih (hc.of_le (Nat.le_succ k)) hf0, fun i ↦ ?_⟩
    obtain ⟨w, hw, hwm⟩ := hfd i
    have hc1 : ContDiffOn ℝ 1 c Ω :=
      (hc.contDiff.of_le (by exact_mod_cast Nat.le_add_left 1 k)).contDiffOn
    refine ⟨fun x ↦ c x * w x + fderiv ℝ c x (b i) * f x, hw.mul_contDiffOn_one hc1, ?_⟩
    have h1 := ih (hc.of_le (Nat.le_succ k)) hwm
    have h2 := ih (hc.fderiv_apply (b i)) hf0
    exact ExtensionHigher.memSobolevMultiIndex_add h1 h2

/-- A finite sum of products of multipliers and `W^{k,p}(Ω)` functions lies in `W^{k,p}(Ω)`. -/
theorem ExtensionHigher.memSobolevMultiIndex_sum_mul_of_isContDiffConstOffCompact {k : ℕ}
    {κ : Type*} (s : Finset κ) {c : κ → E → ℝ} {f : κ → E → ℝ}
    (hc : ∀ i ∈ s, IsContDiffConstOffCompact k (c i))
    (hf : ∀ i ∈ s, MemSobolevMultiIndex b (f i) k p Ω μ) :
    MemSobolevMultiIndex b (fun x ↦ ∑ i ∈ s, c i x * f i x) k p Ω μ := by
  have := ExtensionHigher.memSobolevMultiIndex_finset_sum s (f := fun i x ↦ c i x * f i x)
    fun i hi ↦ ExtensionHigher.memSobolevMultiIndex_mul_of_isContDiffConstOffCompact k (hc i hi)
      (hf i hi)
  refine this.congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Finset.sum_apply]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth function equal to `1` on a compact subset `K` of an open `V`, with compact support in
`V`. -/
theorem ExtensionHigher.exists_contDiff_eqOn_one_hasCompactSupport {K V : Set E}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ θ : E → ℝ, ContDiff ℝ ∞ θ ∧ EqOn θ 1 K ∧ HasCompactSupport θ ∧ tsupport θ ⊆ V := by
  obtain ⟨L, hLc, hKL, hLV⟩ := exists_compact_between hK hV hKV
  obtain ⟨θ, hθ, hθ1, hθL, -⟩ := hK.exists_contDiff_eqOn_one isOpen_interior hKL
  exact ⟨θ, hθ, hθ1, hLc.of_isClosed_subset (isClosed_tsupport θ) (hθL.trans interior_subset),
    hθL.trans (interior_subset.trans hLV)⟩

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A `C^n` function with support in an open set `Q` times a `C^n` function on `Q` is `C^n`
everywhere. -/
theorem ExtensionHigher.contDiff_mul_of_tsupport_subset {n : WithTop ℕ∞} {χ f : E → ℝ}
    (hχ : ContDiff ℝ n χ) {Q : Set E} (hQ : IsOpen Q) (hf : ContDiffOn ℝ n f Q)
    (hχQ : tsupport χ ⊆ Q) : ContDiff ℝ n fun y ↦ χ y * f y := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ Q
  · exact hχ.contDiffAt.mul ((hf y hy).contDiffAt (hQ.mem_nhds hy))
  · have hy' : y ∉ tsupport χ := fun h ↦ hy (hχQ h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy'] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

end Multiplier

/-! ### Transport along a `C^k` diffeomorphism at every order -/

section Transport

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open SobolevMultiIndex

/-- A vector of `ℝ^N` is the sum of its coordinates times the basis vectors. -/
theorem ExtensionHigher.eq_sum_single_smul (z : EuclideanSpace ℝ (Fin N)) :
    z = ∑ k, z k • EuclideanSpace.single k (1 : ℝ) := by
  have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr z
  simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using this.symm

/-- A linear functional on `ℝ^N` evaluated at `z` is the sum of `z_k` times its values on the
basis vectors. -/
theorem ExtensionHigher.clm_apply_eq_sum_single (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin N)) : L z = ∑ k, z k * L (EuclideanSpace.single k 1) := by
  conv_lhs => rw [ExtensionHigher.eq_sum_single_smul z, map_sum]
  simp only [map_smul, smul_eq_mul]

omit [Fact (1 ≤ p)] in
/-- The partial derivative `∂ᵢ u` of `u ∈ W^{1,p}(Ω)` is its weak derivative along `eᵢ`. -/
theorem ExtensionHigher.weakDeriv_hasWeakIteratedLineDerivOn_single
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (u : SobolevEuclidean N 1 p Ω) (i : Fin N) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u)
      (weakDeriv u (MultiIndexLE.single i)) Ω volume := by
  have := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
      Fin N → EuclideanSpace ℝ (Fin N)) i)
  rwa [EuclideanSpace.basisFun_toBasis_apply] at this

/-- **`W^{k,p}` is preserved by a `C^k` diffeomorphism, at every order and exponent**: for a `C¹`
diffeomorphism `H : Ω' → Ω` with bounded Jacobians and inverse `J`, with `J` of class `C^k` on an
open set `V` containing a compact `K ⊇ Ω`, and `w ∈ W^{k,p}(Ω')`, the composite
`w ∘ J ∈ W^{k,p}(Ω)`. Induction on `k`: the chain rule
`∂ᵢ (w ∘ J) = ∑_l (∂_i J)_l · (∂_l w ∘ J)` (`HasWeakFDerivOn.comp_diffeoOn`), the inductive
hypothesis for `∂_l w ∘ J`, and the multiplier `(∂_i J)_l`, `C^{k-1}` on `V` and equal on `Ω` to
a compactly supported one
(`ExtensionHigher.memSobolevMultiIndex_mul_of_isContDiffConstOffCompact`). This is the
`H^k` statement `memSobolevMultiIndex_comp_chart_of_order` of
`Numlib/Analysis/PDE/Elliptic/Regularity.lean` at every exponent
([brezis2011functional] §9.6, proof of Theorem 9.25, "by returning to `Ω ∩ Uᵢ`"). -/
theorem MemSobolevMultiIndex.comp_diffeoOn_of_order (k : ℕ) :
    ∀ {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {M : ℝ}
    {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}, IsDiffeoOnWithBoundedJacobian H J Ω' Ω M →
    ∀ {V : Set (EuclideanSpace ℝ (Fin N))}, IsOpen V → ContDiffOn ℝ k J V →
    ∀ {K : Set (EuclideanSpace ℝ (Fin N))}, IsCompact K →
    (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K → K ⊆ V →
    ∀ {w : EuclideanSpace ℝ (Fin N) → ℝ},
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis w k p Ω' volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fun x ↦ w (J x)) k p Ω
      volume := by
  induction k with
  | zero =>
    intro H J M Ω' Ω h V hV hJ K hK hΩK hKV w hw
    rw [ExtensionHigher.memSobolevMultiIndex_zero_iff] at hw ⊢
    obtain ⟨D, -, hD⟩ := h.symm.exists_abs_det_fderiv_invFun_le
    refine h.symm.memLp_comp hD Ω.isOpen subset_rfl ?_
    rw [h.symm.bijOn.image_eq]
    exact hw
  | succ k ih =>
    intro H J M Ω' Ω h V hV hJ K hK hΩK hKV w hw
    have hΩV : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ V := hΩK.trans hKV
    -- the cut-off equal to `1` on `K` with support in `V`
    obtain ⟨χ, hχ, hχ1, hχc, hχV⟩ :=
      ExtensionHigher.exists_contDiff_eqOn_one_hasCompactSupport hK hV hKV
    -- the coefficients `c i l = (∂ᵢJ)_l`, `C^k` on `V`, and their compactly supported versions
    obtain ⟨c, hc⟩ : ∃ c : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
      c = fun i l x ↦ fderiv ℝ J x (EuclideanSpace.single i 1) l := ⟨_, rfl⟩
    have hdJ : ContDiffOn ℝ k (fderiv ℝ J) V := hJ.fderiv_of_isOpen hV (m := k) (by norm_cast)
    have hcV : ∀ i l, ContDiffOn ℝ k (c i l) V := fun i l ↦ by
      rw [hc]
      exact (EuclideanSpace.proj l).contDiff.comp_contDiffOn (hdJ.clm_apply contDiffOn_const)
    have hmult : ∀ i l, IsContDiffConstOffCompact k fun x ↦ χ x * c i l x := fun i l ↦
      IsContDiffConstOffCompact.of_hasCompactSupport
        (ExtensionHigher.contDiff_mul_of_tsupport_subset (hχ.of_le (by simp)) hV (hcV i l) hχV)
        hχc.mul_right
    -- `w ∈ W^{k,p}(Ω')`, its partial derivatives `g l ∈ W^{k,p}(Ω')`, and a tensor derivative `Dw`
    obtain ⟨hw1, hwd⟩ := memSobolevMultiIndex_succ_iff.1 hw
    choose g hg hgp using hwd
    simp only [EuclideanSpace.basisFun_toBasis_apply] at hg
    have hw1' : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis w 1 p Ω' volume :=
      hw.mono_order (by omega)
    obtain ⟨u, hu⟩ : ∃ u : SobolevEuclidean N 1 p Ω',
      fn u =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] w :=
      hw1'.exists_sobolevMultiIndex
    obtain ⟨Dw, hDw, -, hDwi, -⟩ := exists_hasWeakFDerivOn_fn u
    have hDw' : HasWeakFDerivOn w Dw Ω' volume :=
      HasWeakIteratedFDerivOn.congr_ae hDw hu (EventuallyEq.refl _ _)
    have hDwg : ∀ l, (fun y ↦ Dw y (EuclideanSpace.single l 1))
        =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] g l := by
      intro l
      have h1 := (ExtensionHigher.weakDeriv_hasWeakIteratedLineDerivOn_single u l).congr_ae hu
        (EventuallyEq.refl _ _)
      have h2 := (ae_restrict_iff' Ω'.isOpen.measurableSet).2 (h1.ae_eq (hg l))
      have h3 := hDwi l
      rw [EuclideanSpace.basisFun_toBasis_apply] at h3
      exact h3.trans h2
    -- the composite: `W^{k,p}` by the inductive hypothesis, and the derivatives
    have hcomp := hDw'.comp_diffeoOn h.symm
    have hJk : ContDiffOn ℝ k J V := hJ.of_le (by exact_mod_cast Nat.le_succ k)
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih h hV hJk hK hΩK hKV hw1, fun i ↦ ?_⟩
    rw [EuclideanSpace.basisFun_toBasis_apply]
    refine ⟨fun x ↦ ∑ l, χ x * c i l x * g l (J x), ?_, ?_⟩
    · have h1 := (hcomp : HasWeakIteratedFDerivOn 1 _ _ Ω volume).lineDeriv
        ![EuclideanSpace.single i 1]
      refine h1.congr_ae (EventuallyEq.refl _ _) ?_
      have hae : ∀ l, ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))),
          Dw (J x) (EuclideanSpace.single l 1) = g l (J x) := fun l ↦
        h.symm.ae_comp_restrict (hDwg l)
      filter_upwards [ae_all_iff.2 hae, self_mem_ae_restrict Ω.isOpen.measurableSet] with x hx hxΩ
      simp only [continuousMultilinearCurryFin1_symm_apply, Matrix.cons_val_zero,
        ContinuousLinearMap.comp_apply]
      rw [ExtensionHigher.clm_apply_eq_sum_single (Dw (J x))
        (fderiv ℝ J x (EuclideanSpace.single i 1))]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [hx l, hc, hχ1 (hΩK hxΩ), Pi.one_apply, one_mul]
    · refine ExtensionHigher.memSobolevMultiIndex_sum_mul_of_isContDiffConstOffCompact Finset.univ
        (c := fun l x ↦ χ x * c i l x) (f := fun l x ↦ g l (J x)) (fun l _ ↦ hmult i l)
        fun l _ ↦ ?_
      exact ih h hV hJk hK hΩK hKV (hgp l)

end Transport

/-! ### The zero extension at every order -/

section ZeroExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}
  [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- A smooth function constant off a compact set whose support misses the frontier of `Ω` is a
Sobolev cut-off for `Ω` (bounded with bounded derivative). -/
theorem ExtensionHigher.isSobolevCutoff_of_hasCompactSupport_sub {θ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) {κ : ℝ} (hθκ : HasCompactSupport fun x ↦ θ x - κ)
    (hθΓ : Disjoint (tsupport θ) (frontier (Ω : Set E))) : IsSobolevCutoff Ω θ where
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

/-- **The zero extension of `θ f` at every order and exponent** ([brezis2011functional] Chapter 9,
Remark 4 (ii), iterated): for a smooth `θ` constant off a compact set with support off the
frontier of `Ω` (the function `θ₀ = 1 − ∑ θᵢ` of a partition of unity, or a `θᵢ` compactly
supported in `Ω`) and `f ∈ W^{k,p}(Ω)`, the extension of `θ f` by zero lies in `W^{k,p}(E)`.
Induction on `k` through `memSobolevMultiIndex_succ_iff`, the derivative of the extension being
the extension of `θ ∂_i f + (∂_i θ) f` (`HasWeakIteratedLineDerivOn.indicator_mul`). The `H^k`
version is `MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub` of
`Numlib/Analysis/PDE/Elliptic/Regularity.lean`. -/
theorem ExtensionHigher.memSobolevMultiIndex_indicator_mul_of_hasCompactSupport_sub (k : ℕ) :
    ∀ {θ f : E → ℝ}, ContDiff ℝ ∞ θ → (∃ κ : ℝ, HasCompactSupport fun x ↦ θ x - κ) →
    Disjoint (tsupport θ) (frontier (Ω : Set E)) → MemSobolevMultiIndex b f k p Ω μ →
    MemSobolevMultiIndex b ((Ω : Set E).indicator fun x ↦ θ x * f x) k p ⊤ μ := by
  induction k with
  | zero =>
    rintro θ f hθ ⟨κ, hθκ⟩ hθΓ hf
    rw [ExtensionHigher.memSobolevMultiIndex_zero_iff] at hf ⊢
    have hcut := ExtensionHigher.isSobolevCutoff_of_hasCompactSupport_sub (Ω := Ω) hθ hθκ hθΓ
    obtain ⟨M, hM⟩ := hcut.exists_bound
    have := memLp_indicator_smul_of_forall_norm_le (μ := μ) Ω.isOpen.measurableSet
      (g := θ) (M := M) (fun x _ ↦ (Real.norm_eq_abs _).trans_le (hM x).1)
      hcut.continuous.aestronglyMeasurable hf
    rw [Opens.coe_top, Measure.restrict_univ]
    exact this
  | succ k ih =>
    rintro θ f hθ ⟨κ, hθκ⟩ hθΓ hf
    have hcut := ExtensionHigher.isSobolevCutoff_of_hasCompactSupport_sub (Ω := Ω) hθ hθκ hθΓ
    obtain ⟨hf0, hfd⟩ := memSobolevMultiIndex_succ_iff.1 hf
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih hθ ⟨κ, hθκ⟩ hθΓ hf0, fun i ↦ ?_⟩
    obtain ⟨w, hw, hwm⟩ := hfd i
    refine ⟨(Ω : Set E).indicator fun x ↦ θ x * w x + fderiv ℝ θ x (b i) * f x, ?_, ?_⟩
    · have := hw.indicator_mul hcut
      simpa only [smul_eq_mul] using this
    · have hθ' : ContDiff ℝ ∞ fun x ↦ fderiv ℝ θ x (b i) := hcut.contDiff_fderiv_apply _
      have hθ'c : HasCompactSupport fun x ↦ fderiv ℝ θ x (b i) - 0 := by
        have := hθκ.fderiv_apply (𝕜 := ℝ) (b i)
        have e : (fun x ↦ fderiv ℝ θ x (b i) - 0)
            = fun x ↦ fderiv ℝ (fun x ↦ θ x - κ) x (b i) := by
          funext x
          simp only [fderiv_sub_const, sub_zero]
        rw [e]
        exact this
      have h1 := ih hθ ⟨κ, hθκ⟩ hθΓ hwm
      have h2 := ih hθ' ⟨0, hθ'c⟩ (hθΓ.mono_left (tsupport_fderiv_apply_subset ℝ (b i))) hf0
      refine (ExtensionHigher.memSobolevMultiIndex_add h1 h2).congr_ae
        (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.add_apply]
      by_cases hx : x ∈ (Ω : Set E)
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx, add_zero]

end ZeroExtension

/-! ### Scaling the last coordinate, and the cylinders `Q_r` -/

section ScaleLast

variable {d : ℕ}

/-- `scaleLast l : (x', x_N) ↦ (x', l x_N)`, the linear map of `ℝ^{d+1}` scaling the last
coordinate by `l`. For `l < 0` it sends the lower half space into the upper one; the higher-order
reflection is a linear combination of the composites with `scaleLast (l j)`. -/
def scaleLast (l : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  ContinuousLinearMap.id ℝ _ +
    (l - 1) • (EuclideanSpace.proj (Fin.last d)).smulRight (single (Fin.last d) (1 : ℝ))

/-- The coordinates of `scaleLast l x`. -/
theorem scaleLast_apply (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin (d + 1)) :
    scaleLast l x i = if i = Fin.last d then l * x (Fin.last d) else x i := by
  simp only [scaleLast, add_apply, ContinuousLinearMap.id_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- The last coordinate of `scaleLast l x` is `l x_N`. -/
@[simp]
theorem scaleLast_apply_last (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLast l x (Fin.last d) = l * x (Fin.last d) := by
  simp [scaleLast_apply]

/-- `scaleLast l` keeps the first `d` coordinates. -/
@[simp]
theorem init_scaleLast (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    init (scaleLast l x) = init x := by
  ext i
  simp [scaleLast_apply, Fin.castSucc_ne_last]

/-- `scaleLast l ∘ scaleLast l' = scaleLast (l l')`. -/
theorem scaleLast_scaleLast (l l' : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLast l (scaleLast l' x) = scaleLast (l * l') x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; simp [mul_assoc]
  · rfl

/-- `scaleLast 1` is the identity. -/
theorem scaleLast_one (x : EuclideanSpace ℝ (Fin (d + 1))) : scaleLast 1 x = x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; ring
  · rfl

/-- `scaleLast l` fixes the hyperplane `x_N = 0`. -/
theorem scaleLast_of_apply_last_eq_zero (l : ℝ) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x (Fin.last d) = 0) : scaleLast l x = x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; rw [hx, mul_zero]
  · rfl

/-- `scaleLast l` as a continuous linear equivalence, `l ≠ 0`, with inverse `scaleLast l⁻¹`. -/
def scaleLastEquiv {l : ℝ} (hl : l ≠ 0) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  ContinuousLinearEquiv.equivOfInverse (scaleLast l) (scaleLast l⁻¹)
    (fun x ↦ by rw [scaleLast_scaleLast, inv_mul_cancel₀ hl, scaleLast_one])
    (fun x ↦ by rw [scaleLast_scaleLast, mul_inv_cancel₀ hl, scaleLast_one])

/-- `scaleLastEquiv hl` is `scaleLast l`. -/
@[simp]
theorem scaleLastEquiv_apply {l : ℝ} (hl : l ≠ 0) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLastEquiv hl x = scaleLast l x :=
  rfl

/-- The inverse of `scaleLastEquiv hl` is `scaleLast l⁻¹`. -/
@[simp]
theorem scaleLastEquiv_symm_apply {l : ℝ} (hl : l ≠ 0) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    (scaleLastEquiv hl).symm x = scaleLast l⁻¹ x :=
  rfl

/-- The linear map `scaleLast l`, for `l ≠ 0`, is a `C^1` diffeomorphism of `scaleLast l ⁻¹' Ω`
onto `Ω` with bounded Jacobians, for every open `Ω`. -/
theorem scaleLast_isDiffeoOnWithBoundedJacobian {l : ℝ} (hl : l ≠ 0)
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    ∃ M, IsDiffeoOnWithBoundedJacobian (scaleLast l) (scaleLast l⁻¹)
      (scaleLast l ⁻¹' (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) M := by
  have h := isDiffeoOnWithBoundedJacobian_affine (scaleLastEquiv hl) 0 Ω
  simp only [scaleLastEquiv_apply, add_zero, scaleLastEquiv_symm_apply, sub_zero] at h
  exact ⟨_, h⟩

end ScaleLast

section Cylinder

variable {d : ℕ}

/-- **The cylinder `Q_r = {(x', x_N) : ‖x'‖ < r, |x_N| < r}`** of radius `r`, an open subset of
the unit cylinder `Q` for `r ≤ 1`, with compact closure inside `Q` for `r < 1`. The chart-local
extensions of the higher-order theorem live on these: a chart is `C^k` on the closure of `Q` only,
and the transport of `W^{k,p}` along it needs `C^k` on an open neighbourhood of the closure of the
source, which `Q_r`, `r < 1`, has. -/
def cylinder (d : ℕ) (r : ℝ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨{x | ‖init x‖ < r ∧ |x (Fin.last d)| < r},
    (isOpen_lt continuous_init.norm continuous_const).inter
      (isOpen_lt continuous_abs_apply_last continuous_const)⟩

/-- Membership of the cylinder `Q_r`. -/
theorem mem_cylinder {r : ℝ} {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ cylinder d r ↔ ‖init x‖ < r ∧ |x (Fin.last d)| < r :=
  Iff.rfl

/-- The cylinder `Q_r`, `r ≤ 1`, lies in the unit cylinder. -/
theorem cylinder_subset_unitChartCube {r : ℝ} (hr : r ≤ 1) :
    (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ unitChartCube d :=
  fun _ hx ↦ ⟨hx.1.trans_le hr, hx.2.trans_le hr⟩

/-- The closure of `Q_r` lies in the closed cylinder of radius `r`. -/
theorem closure_cylinder_subset (r : ℝ) :
    closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ {x | ‖init x‖ ≤ r ∧ |x (Fin.last d)| ≤ r} :=
  closure_minimal (fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩)
    ((isClosed_le continuous_init.norm continuous_const).inter
      (isClosed_le continuous_abs_apply_last continuous_const))

/-- The closure of `Q_r`, `r < 1`, lies in the open unit cylinder `Q`. -/
theorem closure_cylinder_subset_unitChartCube {r : ℝ} (hr : r < 1) :
    closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ unitChartCube d :=
  fun _ hx ↦ ⟨(closure_cylinder_subset r hx).1.trans_lt hr,
    (closure_cylinder_subset r hx).2.trans_lt hr⟩

/-- The cylinder `Q_r` is bounded. -/
theorem isBounded_cylinder (r : ℝ) :
    Bornology.IsBounded (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  refine (isBounded_iff_forall_norm_le.2 ⟨2 * |r|, fun x hx ↦ ?_⟩)
  have h1 : ‖x‖ ^ 2 ≤ (2 * |r|) ^ 2 := by
    rw [norm_sq_eq_init_add_last]
    have hr : 0 ≤ |r| := abs_nonneg r
    have hi : ‖init x‖ ≤ |r| := hx.1.le.trans (le_abs_self r)
    have hl : |x (Fin.last d)| ≤ |r| := hx.2.le.trans (le_abs_self r)
    nlinarith [sq_abs (x (Fin.last d)), abs_nonneg (x (Fin.last d)), norm_nonneg (init x)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- The closure of `Q_r` is compact. -/
theorem isCompact_closure_cylinder (r : ℝ) :
    IsCompact (closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (isBounded_cylinder r).isCompact_closure

/-- The cylinder has finite volume. -/
theorem volume_cylinder_lt_top (r : ℝ) :
    volume (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) < ⊤ :=
  (isBounded_cylinder r).measure_lt_top

/-- The cylinder is convex. -/
theorem convex_cylinder (r : ℝ) :
    Convex ℝ (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  have e1 : {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖init x‖ < r}
      = initL.toLinearMap ⁻¹' ball (0 : EuclideanSpace ℝ (Fin d)) r := by
    ext x; simp [initL_apply, mem_ball, dist_zero_right]
  have e2 : {x : EuclideanSpace ℝ (Fin (d + 1)) | |x (Fin.last d)| < r}
      = (EuclideanSpace.proj (Fin.last d)).toLinearMap ⁻¹' ball (0 : ℝ) r := by
    ext x; simp [mem_ball]
  have h1 : Convex ℝ {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖init x‖ < r} := by
    rw [e1]; exact (convex_ball _ _).linear_preimage _
  have h2 : Convex ℝ {x : EuclideanSpace ℝ (Fin (d + 1)) | |x (Fin.last d)| < r} := by
    rw [e2]; exact (convex_ball _ _).linear_preimage _
  exact h1.inter h2

/-- The cylinder is symmetric under the reflection across `x_N = 0`. -/
theorem hyperplaneReflection_image_cylinder (r : ℝ) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) '' (cylinder d r : Set _) = cylinder d r :=
      by
  refine Function.Involutive.image_eq_of_forall_mem_iff (hyperplaneReflection_hyperplaneReflection
    _)
    fun x ↦ ?_
  simp [mem_cylinder, init_hyperplaneReflection_single_last,
    hyperplaneReflection_single_last_apply_last]

/-- `scaleLast l`, `|l| ≤ 1`, maps the cylinder into itself. -/
theorem scaleLast_mem_cylinder {l r : ℝ} (hl : |l| ≤ 1) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x ∈ cylinder d r) : scaleLast l x ∈ cylinder d r := by
  refine ⟨by rw [init_scaleLast]; exact hx.1, ?_⟩
  rw [scaleLast_apply_last, abs_mul]
  calc |l| * |x (Fin.last d)| ≤ 1 * |x (Fin.last d)| :=
        mul_le_mul_of_nonneg_right hl (abs_nonneg _)
    _ = |x (Fin.last d)| := one_mul _
    _ < r := hx.2

/-- The positive half of the cylinder for `v = e_N` is `Q_r ∩ {x_N > 0}`. -/
theorem coe_posHalf_cylinder (r : ℝ) :
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (cylinder d r : Set _) ∩ {x | 0 < x (Fin.last d)} := by
  rw [coe_posHalf]
  ext x
  simp [EuclideanSpace.inner_single_last_one]

/-- A compact subset of the unit cylinder lies in a cylinder `Q_r` with `r < 1`. -/
theorem exists_lt_one_subset_cylinder {K : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hK : IsCompact K) (hKQ : K ⊆ unitChartCube d) : ∃ r, r < 1 ∧ K ⊆ cylinder d r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, zero_lt_one, empty_subset _⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_init.norm.max continuous_abs_apply_last).continuousOn
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max ‖init x₀‖ |x₀ (Fin.last d)| := ⟨_, rfl⟩
  have hm1 : m < 1 := by rw [hm]; exact max_lt (hKQ hx₀).1 (hKQ hx₀).2
  refine ⟨(m + 1) / 2, by linarith, fun x hx ↦ ?_⟩
  have h : max ‖init x‖ |x (Fin.last d)| ≤ m := by rw [hm]; exact hmax hx
  exact ⟨by linarith [le_max_left ‖init x‖ |x (Fin.last d)|],
    by linarith [le_max_right ‖init x‖ |x (Fin.last d)|]⟩

end Cylinder

/-! ### The two halves of an open set, and the maps `scaleLast l` between them -/

section Halves

variable {d : ℕ} {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The negative half** `V₋ = V ∩ {x_N < 0}` of an open set of `ℝ^{d+1}`. Its positive half is
`posHalf e_N V` of `Numlib/Analysis/Sobolev/Reflection.lean`. -/
def negHalf (V : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ {x | x (Fin.last d) < 0}

/-- Membership of the negative half. -/
theorem mem_negHalf {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ negHalf V ↔ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∧ x (Fin.last d) < 0 :=
  Iff.rfl

/-- The negative half is open. -/
theorem isOpen_negHalf' : IsOpen (negHalf V) :=
  V.isOpen.inter (isOpen_lt continuous_apply_last continuous_const)

/-- Membership of the positive half `posHalf e_N V`, in coordinates. -/
theorem mem_posHalf_last_iff {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) ↔
      x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∧ 0 < x (Fin.last d) := by
  rw [coe_posHalf]
  simp [EuclideanSpace.inner_single_last_one]

/-- The positive half is a subset of `V`. -/
theorem posHalf_last_subset :
    (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) ⊆ (V : Set (EuclideanSpace ℝ (Fin (d + 1))))
      :=
  fun _ hx ↦ (mem_posHalf_last_iff.1 hx).1

/-- The negative half is a subset of `V`. -/
theorem negHalf_subset : negHalf V ⊆ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) := fun _ hx ↦ hx.1

/-- The hyperplane `x_N = 0` is a null set. -/
theorem ae_apply_last_ne_zero : ∀ᵐ x : EuclideanSpace ℝ (Fin (d + 1)), x (Fin.last d) ≠ 0 := by
  have hv : (single (Fin.last d) (1 : ℝ) : EuclideanSpace ℝ (Fin (d + 1))) ≠ 0 :=
    ne_zero_of_norm_ne_zero (by rw [EuclideanSpace.norm_single_last_one]; exact one_ne_zero)
  filter_upwards [ae_inner_ne_zero hv] with x hx
  rwa [EuclideanSpace.inner_single_last_one] at hx

/-- **A function equal to `A` on the positive half and to `B` on the negative half** agrees almost
everywhere on `V` with `1_{V₊} A + 1_{V₋} B`. -/
theorem ae_eq_indicator_add_of_piecewise {F : Type*} [NormedAddCommGroup F] {G A B : _ → F}
    (hA : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), 0 < x (Fin.last d) → G x = A x)
    (hB : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → G x = B x) :
    G =ᵐ[volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A + (negHalf V).indicator B := by
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet, ae_restrict_of_ae ae_apply_last_ne_zero]
    with x hxV hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hxm : x ∈ negHalf V := ⟨hxV, h⟩
    have hxp : x ∉ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) := fun h' ↦
      lt_asymm h (mem_posHalf_last_iff.1 h').2
    rw [Pi.add_apply, Set.indicator_of_notMem hxp, Set.indicator_of_mem hxm, zero_add, hB x hxV h]
  · have hxp : x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) :=
      mem_posHalf_last_iff.2 ⟨hxV, h⟩
    have hxm : x ∉ negHalf V := fun h' ↦ lt_asymm h h'.2
    rw [Pi.add_apply, Set.indicator_of_mem hxp, Set.indicator_of_notMem hxm, add_zero, hA x hxV h]

/-- Measurability of a function given by `A` on `V₊` and `B` on `V₋`. -/
theorem aestronglyMeasurable_of_piecewise {F : Type*} [NormedAddCommGroup F] {G A B : _ → F}
    (hA : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), 0 < x (Fin.last d) → G x = A x)
    (hB : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → G x = B x)
    (hAm : AEStronglyMeasurable A
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)))
    (hBm : AEStronglyMeasurable B (volume.restrict (negHalf V))) :
    AEStronglyMeasurable G (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  have h1 : AEStronglyMeasurable ((posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A
      + (negHalf V).indicator B) volume :=
    ((aestronglyMeasurable_indicator_iff (posHalf _ V).isOpen.measurableSet).2 hAm).add
      ((aestronglyMeasurable_indicator_iff isOpen_negHalf'.measurableSet).2 hBm)
  exact (h1.mono_measure Measure.restrict_le_self).congr (ae_eq_indicator_add_of_piecewise hA
    hB).symm

/-- The `L^p(V)` norm of a function given by `A` on `V₊` and `B` on `V₋` is at most
`‖A‖_{L^p(V₊)} + ‖B‖_{L^p(V₋)}`, `1 ≤ p`. -/
theorem eLpNorm_le_of_piecewise {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {G A B : _ → F}
    (hA : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), 0 < x (Fin.last d) → G x = A x)
    (hB : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → G x = B x) :
    eLpNorm G p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ eLpNorm A p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))
        + eLpNorm B p (volume.restrict (negHalf V)) := by
  calc eLpNorm G p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      = eLpNorm ((posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A
          + (negHalf V).indicator B) p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))
            :=
        eLpNorm_congr_ae (ae_eq_indicator_add_of_piecewise hA hB)
    _ ≤ eLpNorm ((posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A) p
          (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        + eLpNorm ((negHalf V).indicator B) p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d +
          1))))) := eLpNorm_add_le hp
    _ ≤ eLpNorm ((posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A) p volume
        + eLpNorm ((negHalf V).indicator B) p volume :=
        add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
          (eLpNorm_mono_measure _ Measure.restrict_le_self)
    _ = _ := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict (posHalf _ V).isOpen.measurableSet,
          eLpNorm_indicator_eq_eLpNorm_restrict isOpen_negHalf'.measurableSet]

/-- `scaleLast l`, `l < 0`, maps the negative half of `V` into the positive half, when it maps it
into `V`. -/
theorem scaleLast_mem_posHalf {l : ℝ} (hl : l < 0)
    (hV : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast l x ∈ V)
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ negHalf V) :
    scaleLast l x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) :=
  mem_posHalf_last_iff.2 ⟨hV x hx.1 hx.2, by
    rw [scaleLast_apply_last]; exact mul_pos_of_neg_of_neg hl hx.2⟩

/-- The negative half lies in the preimage of the positive half under `scaleLast l`, `l < 0`. -/
theorem negHalf_subset_preimage_scaleLast {l : ℝ} (hl : l < 0)
    (hV : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast l x ∈ V)
      :
    negHalf V ⊆ scaleLast l ⁻¹' (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) :=
  fun _ hx ↦ scaleLast_mem_posHalf hl hV hx

/-- The image of the negative half under `scaleLast l`, `l < 0`, lies in the positive half. -/
theorem image_negHalf_scaleLast_subset {l : ℝ} (hl : l < 0)
    (hV : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast l x ∈ V)
      :
    scaleLast l '' negHalf V ⊆ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) := by
  rintro _ ⟨x, hx, rfl⟩
  exact scaleLast_mem_posHalf hl hV hx

/-- **The transport facts for `f ↦ f ∘ scaleLast l` from the positive to the negative half**,
`l < 0`: measurability, the `L^p` bound with a constant `D`, and the pull-back of almost
everywhere statements. Packaged with the constant existential so that the consumers never see the
Jacobian. -/
theorem exists_scaleLast_negHalf_facts {l : ℝ} (hl : l < 0)
    (hV : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast l x ∈ V)
      (p : ℝ≥0∞) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      (∀ {F : Type*} [NormedAddCommGroup F] (f : EuclideanSpace ℝ (Fin (d + 1)) → F),
        AEStronglyMeasurable f
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) →
        AEStronglyMeasurable (fun x ↦ f (scaleLast l x)) (volume.restrict (negHalf V)) ∧
        eLpNorm (fun x ↦ f (scaleLast l x)) p (volume.restrict (negHalf V))
          ≤ D * eLpNorm f p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))) ∧
      (∀ {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop},
        (∀ᵐ x ∂volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _), P x) →
        ∀ᵐ x ∂volume.restrict (negHalf V), P (scaleLast l x)) := by
  obtain ⟨M, hS⟩ := scaleLast_isDiffeoOnWithBoundedJacobian hl.ne
    (posHalf (single (Fin.last d) (1 : ℝ)) V)
  obtain ⟨D, -, hD⟩ := hS.exists_abs_det_fderiv_invFun_le
  have hA : IsOpen (negHalf V) := isOpen_negHalf'
  have hAs := negHalf_subset_preimage_scaleLast hl hV
  have himg := image_negHalf_scaleLast_subset hl hV
  refine ⟨ENNReal.ofReal D ^ (1 / p.toReal), ENNReal.rpow_ne_top_of_nonneg (by positivity)
    ENNReal.ofReal_ne_top, fun f hf ↦ ⟨?_, ?_⟩, fun {P} hP ↦ ?_⟩
  · exact hS.aestronglyMeasurable_comp hA hAs
      (hf.mono_measure (Measure.restrict_mono himg le_rfl))
  · refine (hS.eLpNorm_comp_le hD hA hAs (hf.mono_measure (Measure.restrict_mono himg le_rfl))
      p).trans ?_
    gcongr
  · exact hS.ae_comp hA hAs (ae_restrict_of_ae_restrict_of_subset himg hP)

end Halves

/-! ### The higher-order reflection -/

section HigherReflection

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}

/-- **The higher-order reflection across `x_N = 0`**: `w` on `{x_N ≥ 0}`, and
`∑_j a_j w(x', l_j x_N)` on `{x_N < 0}`, for coefficients `a` and scales `l` (with `l_j < 0`).
For `m = 1`, `a = 1`, `l = −1` it is the even reflection `evenReflection e_N w`; with `a` solving
the Vandermonde system `∑_j a_j l_j^i = 1`, `i < k`, it preserves `W^{k,p}` (Brezis, Comments on
Chapter 9, 3; Lions–Magenes). -/
def higherReflection (a l : Fin m → ℝ) (w : EuclideanSpace ℝ (Fin (d + 1)) → F)
    (x : EuclideanSpace ℝ (Fin (d + 1))) : F :=
  if 0 ≤ x (Fin.last d) then w x else ∑ j, a j • w (scaleLast (l j) x)

/-- **The reflected tensor derivative**: `Dw` on `{x_N ≥ 0}`, and
`∑_j a_j (Dw ∘ S_j) ∘ S_j` on `{x_N < 0}`, `S_j = scaleLast (l j)` — the chain rule applied to
each term of the higher-order reflection. -/
def higherReflectionFDeriv (a l : Fin m → ℝ)
    (Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F)
    (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F :=
  if 0 ≤ x (Fin.last d) then Dw x
  else ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j))

variable (a l : Fin m → ℝ)

/-- On `{x_N ≥ 0}` the reflection is the function. -/
theorem higherReflection_of_nonneg {w : EuclideanSpace ℝ (Fin (d + 1)) → F}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : 0 ≤ x (Fin.last d)) :
    higherReflection a l w x = w x := by
  simp only [higherReflection, hx, ↓reduceIte]

/-- On `{x_N < 0}` the reflection is the combination of the scaled functions. -/
theorem higherReflection_of_neg {w : EuclideanSpace ℝ (Fin (d + 1)) → F}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x (Fin.last d) < 0) :
    higherReflection a l w x = ∑ j, a j • w (scaleLast (l j) x) := by
  simp only [higherReflection, not_le.2 hx, ↓reduceIte]

/-- On `{x_N ≥ 0}` the reflected derivative is the derivative. -/
theorem higherReflectionFDeriv_of_nonneg
    {Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : 0 ≤ x (Fin.last d)) :
    higherReflectionFDeriv a l Dw x = Dw x := by
  simp only [higherReflectionFDeriv, hx, ↓reduceIte]

/-- On `{x_N < 0}` the reflected derivative is the combination of the transported derivatives. -/
theorem higherReflectionFDeriv_of_neg
    {Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x (Fin.last d) < 0) :
    higherReflectionFDeriv a l Dw x
      = ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)) := by
  simp only [higherReflectionFDeriv, not_le.2 hx, ↓reduceIte]

/-- The higher-order reflection is additive. -/
theorem higherReflection_add (f g : EuclideanSpace ℝ (Fin (d + 1)) → F) :
    higherReflection a l (f + g) = higherReflection a l f + higherReflection a l g := by
  funext x
  simp only [higherReflection, Pi.add_apply]
  split_ifs
  · rfl
  · simp only [smul_add, Finset.sum_add_distrib]

/-- The higher-order reflection commutes with scalar multiplication. -/
theorem higherReflection_smul (c : ℝ) (f : EuclideanSpace ℝ (Fin (d + 1)) → F) :
    higherReflection a l (c • f) = c • higherReflection a l f := by
  funext x
  simp only [higherReflection, Pi.smul_apply]
  split_ifs
  · rfl
  · simp only [Finset.smul_sum, smul_comm c]

variable {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {a l}

/-- **The standing hypotheses on the scales and the set**: every `l j` lies in `[-1, 0)` and
`scaleLast (l j)` maps the negative half of `V` into `V`. -/
structure IsReflectionSet (l : Fin m → ℝ) (V : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Prop where
  neg : ∀ j, l j < 0
  neg_one_le : ∀ j, -1 ≤ l j
  mem : ∀ j, ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast (l j)
    x ∈ V

/-- The cylinders are reflection sets for scales in `[-1, 0)`. -/
theorem isReflectionSet_cylinder (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j) (r : ℝ) :
    IsReflectionSet l (cylinder d r) :=
  ⟨hl, hl1, fun j _ hx _ ↦
    scaleLast_mem_cylinder (abs_le.2 ⟨hl1 j, (hl j).le.trans zero_le_one⟩) hx⟩

/-- **The `L^p` facts of the higher-order reflection**, packaged: for a measurable `w` on `V₊`,
`P w` is measurable on `V` and `‖P w‖_{L^p(V)} ≤ C ‖w‖_{L^p(V₊)}`, and the same for
`higherReflectionFDeriv` with the same constant; and almost everywhere statements on `V₊`
transport to the `scaleLast (l j) x`, `x ∈ V₋`. -/
theorem IsReflectionSet.exists_facts (hV : IsReflectionSet l V) (a : Fin m → ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (∀ w : EuclideanSpace ℝ (Fin (d + 1)) → F,
        AEStronglyMeasurable w
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) →
        AEStronglyMeasurable (higherReflection a l w) (volume.restrict (V : Set (EuclideanSpace ℝ
          (Fin (d + 1))))) ∧
        eLpNorm (higherReflection a l w) p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d +
          1)))))
          ≤ C * eLpNorm w p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))) ∧
      (∀ Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F,
        AEStronglyMeasurable Dw
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) →
        AEStronglyMeasurable (higherReflectionFDeriv a l Dw) (volume.restrict (V : Set
          (EuclideanSpace ℝ (Fin (d + 1))))) ∧
        eLpNorm (higherReflectionFDeriv a l Dw) p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin
          (d + 1)))))
          ≤ C * eLpNorm Dw p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))) ∧
      (∀ {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop},
        (∀ᵐ x ∂volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _), P x) →
        ∀ᵐ x ∂volume.restrict (negHalf V), ∀ j, P (scaleLast (l j) x)) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  choose D hD hDf hDP using fun j ↦ exists_scaleLast_negHalf_facts (hV.neg j) (hV.mem j) p
  obtain ⟨K, hK⟩ : ∃ K : Fin m → ℝ≥0∞, K = fun j ↦ ENNReal.ofReal ‖scaleLast (l j)‖ :=
    ⟨fun j ↦ ENNReal.ofReal ‖scaleLast (l j)‖, rfl⟩
  have hK' : ∀ j, K j ≠ ⊤ := fun j ↦ by rw [hK]; exact ENNReal.ofReal_ne_top
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = 1 + ∑ j, ‖a j‖ₑ * (1 + K j) * D j := ⟨_, rfl⟩
  have hC' : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun j _ ↦
      ENNReal.mul_ne_top (ENNReal.mul_ne_top enorm_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hK' j⟩)) (hD j)⟩
  refine ⟨C, hC', fun w hw ↦ ⟨?_, ?_⟩, fun Dw hDw ↦ ⟨?_, ?_⟩, fun {P} hP ↦ ?_⟩
  · refine aestronglyMeasurable_of_piecewise (A := w)
      (B := fun x ↦ ∑ j, a j • w (scaleLast (l j) x))
      (fun x _ hx ↦ higherReflection_of_nonneg a l hx.le)
      (fun x _ hx ↦ higherReflection_of_neg a l hx) hw ?_
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ
      (f := fun j x ↦ a j • w (scaleLast (l j) x)) fun j _ ↦ ((hDf j w hw).1).const_smul (a j)
  · refine (eLpNorm_le_of_piecewise hp (A := w)
      (B := fun x ↦ ∑ j, a j • w (scaleLast (l j) x))
      (fun x _ hx ↦ higherReflection_of_nonneg a l hx.le)
      (fun x _ hx ↦ higherReflection_of_neg a l hx)).trans ?_
    have hB : eLpNorm (fun x ↦ ∑ j, a j • w (scaleLast (l j) x)) p (volume.restrict (negHalf V))
        ≤ ∑ j, ‖a j‖ₑ * D j * eLpNorm w p
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
      have e : (fun x ↦ ∑ j, a j • w (scaleLast (l j) x))
          = ∑ j, fun x ↦ a j • w (scaleLast (l j) x) := by
        funext x; simp only [Finset.sum_apply]
      rw [e]
      refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      have e' : (fun x ↦ a j • w (scaleLast (l j) x)) = a j • fun x ↦ w (scaleLast (l j) x) := rfl
      rw [e', eLpNorm_const_smul, mul_assoc]
      gcongr
      exact (hDf j w hw).2
    calc _ ≤ eLpNorm w p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))
          + ∑ j, ‖a j‖ₑ * D j * eLpNorm w p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) :=
          add_le_add le_rfl hB
      _ = (1 + ∑ j, ‖a j‖ₑ * D j) * eLpNorm w p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
          rw [add_mul, one_mul, Finset.sum_mul]
      _ ≤ C * eLpNorm w p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
          gcongr
          rw [hC]
          gcongr with j _
          exact le_mul_of_one_le_right zero_le (le_add_right le_rfl)
  · refine aestronglyMeasurable_of_piecewise (A := Dw)
      (B := fun x ↦ ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
      (fun x _ hx ↦ higherReflectionFDeriv_of_nonneg a l hx.le)
      (fun x _ hx ↦ higherReflectionFDeriv_of_neg a l hx) hDw ?_
    refine Finset.aestronglyMeasurable_fun_sum Finset.univ
      (f := fun j x ↦ a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
      fun j _ ↦ AEStronglyMeasurable.const_smul ?_ (a j)
    exact (((ContinuousLinearMap.compL ℝ _ _ F).flip (scaleLast (l j))).continuous
      |>.comp_aestronglyMeasurable (hDf j Dw hDw).1).congr (Eventually.of_forall fun x ↦ by simp)
  · refine (eLpNorm_le_of_piecewise hp (A := Dw)
      (B := fun x ↦ ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
      (fun x _ hx ↦ higherReflectionFDeriv_of_nonneg a l hx.le)
      (fun x _ hx ↦ higherReflectionFDeriv_of_neg a l hx)).trans ?_
    have hB : eLpNorm (fun x ↦ ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j))) p
        (volume.restrict (negHalf V))
        ≤ ∑ j, ‖a j‖ₑ * K j * D j * eLpNorm Dw p
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
      have e : (fun x ↦ ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
          = ∑ j, fun x ↦ a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)) := by
        funext x; simp only [Finset.sum_apply]
      rw [e]
      refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      have e' : (fun x ↦ a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
          = a j • fun x ↦ (Dw (scaleLast (l j) x)).comp (scaleLast (l j)) := rfl
      rw [e', eLpNorm_const_smul]
      have hm : AEStronglyMeasurable (fun x ↦ (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
          (volume.restrict (negHalf V)) :=
        (((ContinuousLinearMap.compL ℝ _ _ F).flip (scaleLast (l j))).continuous
          |>.comp_aestronglyMeasurable (hDf j Dw hDw).1).congr
          (Eventually.of_forall fun x ↦ by simp)
      have hΛ := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm (g := fun x ↦ Dw (scaleLast (l j) x))
        (c := ‖scaleLast (l j)‖) (Eventually.of_forall fun x ↦ by
          rw [mul_comm]
          exact ContinuousLinearMap.opNorm_comp_le _ _) p
      calc ‖a j‖ₑ * eLpNorm (fun x ↦ (Dw (scaleLast (l j) x)).comp (scaleLast (l j))) p
            (volume.restrict (negHalf V))
          ≤ ‖a j‖ₑ * (ENNReal.ofReal ‖scaleLast (l j)‖ * (D j * eLpNorm Dw p
              (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)))) := by
            gcongr
            refine hΛ.trans ?_
            gcongr
            exact (hDf j Dw hDw).2
        _ = ‖a j‖ₑ * K j * D j * eLpNorm Dw p
              (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
            rw [hK]; ring
    calc _ ≤ eLpNorm Dw p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))
          + ∑ j, ‖a j‖ₑ * K j * D j * eLpNorm Dw p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) :=
          add_le_add le_rfl hB
      _ = (1 + ∑ j, ‖a j‖ₑ * K j * D j) * eLpNorm Dw p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
          rw [add_mul, one_mul, Finset.sum_mul]
      _ ≤ C * eLpNorm Dw p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
          gcongr
          rw [hC]
          gcongr with j _
          exact le_add_left le_rfl
  · rw [ae_all_iff]
    exact fun j ↦ hDP j hP

end HigherReflection

/-! ### The gluing lemma: a `C^1` function vanishing on the hyperplane, cut to the lower half -/

section Gluing

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inner product with `-e_N` is minus the last coordinate. -/
theorem inner_neg_single_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ⟪x, -single (Fin.last d) (1 : ℝ)⟫ = -x (Fin.last d) := by
  rw [inner_neg_right, EuclideanSpace.inner_single_last_one]

/-- `x − scaleLast 0 x = x_N e_N`. -/
theorem sub_scaleLast_zero (x : EuclideanSpace ℝ (Fin (d + 1))) :
    x - scaleLast 0 x = x (Fin.last d) • single (Fin.last d) (1 : ℝ) := by
  ext i
  simp only [PiLp.sub_apply, scaleLast_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- `‖x − scaleLast 0 x‖ = |x_N|`. -/
theorem norm_sub_scaleLast_zero (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖x - scaleLast 0 x‖ = |x (Fin.last d)| := by
  rw [sub_scaleLast_zero, norm_smul, EuclideanSpace.norm_single_last_one, mul_one,
    Real.norm_eq_abs]

/-- The lower half space `{x_N < 0}` is measurable. -/
theorem measurableSet_lowerHalf :
    MeasurableSet {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0} :=
  (isOpen_lt continuous_apply_last continuous_const).measurableSet

/-- **The gluing lemma**: for `g` of class `C^1` vanishing on the hyperplane `x_N = 0`, the
function `1_{x_N < 0} g` has the weak derivative `1_{x_N < 0} ∇g` on every bounded convex open
set `Ω` closed under the projection `x ↦ (x', 0)`. Proof: `η_n g → 1_{x_N < 0} g` in `W^{1,1}(Ω)`
for the cut-offs `η_n(x) = η((n + 1)(−x_N))`, which are `1` on `{x_N ≤ −1/(n+1)}` and `0` on
`{x_N ≥ −1/(2(n+1))}`; the derivative term `g ∇η_n` is bounded because `|g| ≤ M |x_N|` (the mean
value theorem, `g` vanishing on the hyperplane) and `|∇η_n| ≤ C (n + 1)` on a strip of width
`1/(n+1)`, and it tends to `0` off the null hyperplane; the weak derivative is closed under `L^1`
limits (`hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one`). -/
theorem hasWeakFDerivOn_indicator_lowerHalf_of_contDiff {g : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hg : ContDiff ℝ 1 g) (hg0 : ∀ x, x (Fin.last d) = 0 → g x = 0)
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩc : IsCompact (closure (Ω : Set (EuclideanSpace
      ℝ (Fin (d + 1))))))
    (hΩv : Convex ℝ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ0 : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), scaleLast 0 x ∈ Ω) :
    HasWeakFDerivOn ({x | x (Fin.last d) < 0}.indicator g)
      ({x | x (Fin.last d) < 0}.indicator (fderiv ℝ g)) Ω volume := by
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin (d + 1)), v = -single (Fin.last d) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hvx : ∀ x, ⟪x, v⟫ = -x (Fin.last d) := fun x ↦ by rw [hv, inner_neg_single_last]
  have hL : MeasurableSet {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0} :=
    measurableSet_lowerHalf
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  have hΩfin : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hΩc.measure_lt_top).ne
  -- bounds for `g` and `∇g` on `Ω`
  obtain ⟨M, hM⟩ := hΩc.exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨M'₀, hM'₀⟩ :=
    hΩc.exists_bound_of_continuousOn (hg.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨M', hM'def⟩ : ∃ M' : ℝ, M' = max M'₀ 0 := ⟨_, rfl⟩
  have hM' : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ‖fderiv ℝ g x‖ ≤ M' :=
    fun x hx ↦ (hM'₀ x hx).trans (by rw [hM'def]; exact le_max_left _ _)
  have hM'0 : 0 ≤ M' := by rw [hM'def]; exact le_max_right _ _
  -- the mean value bound `‖g x‖ ≤ M' |x_N|` on `Ω`
  have hgx : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ‖g x‖ ≤ M' * |x (Fin.last d)| := by
    intro x hx
    have h0 : g (scaleLast 0 x) = 0 := hg0 _ (by rw [scaleLast_apply_last, zero_mul])
    have := hΩv.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hg.differentiable one_ne_zero).differentiableAt)
      (fun z hz ↦ hM' z (subset_closure hz)) (hΩ0 x hx) hx
    rwa [h0, sub_zero, norm_sub_scaleLast_zero] at this
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_deriv_reflectionCutoff_le
  -- the cut-offs and the approximants
  obtain ⟨η, hη⟩ : ∃ η : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
    η = fun (n : ℕ) x ↦ reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) := ⟨_, rfl⟩
  have hηx : ∀ n x, η n x = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) := fun n x ↦ by rw [hη]
  have hηs : ∀ n, ContDiff ℝ ∞ (η n) := fun n ↦ by
    rw [hη]
    exact contDiff_reflectionCutoff.comp (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))
  have hη01 : ∀ n x, |η n x| ≤ 1 := fun n x ↦ by rw [hηx]; exact abs_reflectionCutoff_le_one _
  have hηd : ∀ n x, HasFDerivAt (η n)
      (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • (((n : ℝ) + 1) • innerSL ℝ v)) x :=
    fun n x ↦ by rw [hη]; exact hasFDerivAt_reflectionCutoff_inner v _ x
  -- pointwise limits of the cut-offs off the hyperplane
  have hηlim : ∀ x, x (Fin.last d) ≠ 0 →
      Tendsto (fun n ↦ η n x) atTop (𝓝 ({x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x)) :=
        by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · rw [Set.indicator_of_mem (show x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
        from h)]
      simp only [hηx, hvx]
      exact tendsto_reflectionCutoff_mul (neg_pos.2 h)
    · rw [Set.indicator_of_notMem (show x ∉ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) <
      0}
        from not_lt.2 h.le)]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n ↦ ?_)
      change (0 : ℝ) = η n x
      rw [hηx, hvx, reflectionCutoff_of_le_half]
      have : ((n : ℝ) + 1) * -x (Fin.last d) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (neg_nonpos.2 h.le)
      linarith
  have hη'lim : ∀ x, x (Fin.last d) ≠ 0 →
      ∀ᶠ n : ℕ in atTop, deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) = 0 := by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · rw [hvx]
      exact eventually_deriv_reflectionCutoff_mul_eq_zero (neg_pos.2 h)
    · refine Eventually.of_forall fun n ↦ deriv_reflectionCutoff_eq_zero (Or.inl ?_)
      rw [hvx]
      have : ((n : ℝ) + 1) * -x (Fin.last d) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (neg_nonpos.2 h.le)
      linarith
  -- the bound on the derivative term `g ∇η_n`
  have hgη : ∀ (n : ℕ) x, x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) →
      ‖g x‖ * (|deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)| * (((n : ℝ) + 1) * ‖innerSL ℝ v‖))
        ≤ M' * Cη * ‖innerSL ℝ v‖ := by
    intro n x hx
    by_cases h1 : 1 < ((n : ℝ) + 1) * ⟪x, v⟫
    · rw [deriv_reflectionCutoff_eq_zero (Or.inr h1), abs_zero, zero_mul, mul_zero]
      exact mul_nonneg (mul_nonneg hM'0 hCη0) (norm_nonneg _)
    · rcases le_or_gt ⟪x, v⟫ 0 with hxv | hxv
      · have : ((n : ℝ) + 1) * ⟪x, v⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hxv
        rw [deriv_reflectionCutoff_eq_zero (Or.inl (by linarith)), abs_zero, zero_mul, mul_zero]
        exact mul_nonneg (mul_nonneg hM'0 hCη0) (norm_nonneg _)
      · have hxv' : |x (Fin.last d)| = ⟪x, v⟫ := by
          rw [hvx] at hxv ⊢
          rw [abs_of_neg (by linarith)]
        calc ‖g x‖ * (|deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)|
              * (((n : ℝ) + 1) * ‖innerSL ℝ v‖))
            ≤ (M' * |x (Fin.last d)|) * (Cη * (((n : ℝ) + 1) * ‖innerSL ℝ v‖)) :=
              mul_le_mul (hgx x hx) (mul_le_mul_of_nonneg_right (hCη _) (by positivity))
                (by positivity) (mul_nonneg hM'0 (abs_nonneg _))
          _ = M' * Cη * ‖innerSL ℝ v‖ * (((n : ℝ) + 1) * ⟪x, v⟫) := by rw [hxv']; ring
          _ ≤ M' * Cη * ‖innerSL ℝ v‖ * 1 := by
              gcongr
              exact not_lt.1 h1
          _ = M' * Cη * ‖innerSL ℝ v‖ := mul_one _
  -- the approximants `g_n = η_n g` are `C^1`, with the classical derivative as weak derivative
  obtain ⟨G, hG⟩ : ∃ G : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → F,
    G = fun (n : ℕ) x ↦ η n x • g x := ⟨_, rfl⟩
  have hGx : ∀ n x, G n x = η n x • g x := fun n x ↦ by rw [hG]
  have hGs : ∀ n, ContDiff ℝ 1 (G n) := fun n ↦ by
    rw [hG]
    exact ((hηs n).of_le (by simp)).smul hg
  have hGd : ∀ n x, HasFDerivAt (G n) (η n x • fderiv ℝ g x
      + (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • (((n : ℝ) + 1) • innerSL ℝ v)).smulRight
        (g x)) x := fun n x ↦ by
    rw [hG]
    exact (hηd n x).smul (hg.differentiable one_ne_zero x).hasFDerivAt
  have hGw : ∀ n, HasWeakIteratedFDerivOn 1 (G n)
      (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm (fderiv ℝ
        (G n) x)) Ω volume := by
    intro n
    have := (hGs n).contDiffOn.hasWeakIteratedFDerivOn (Ω := Ω) (μ := volume) (m := 1) le_rfl
    refine this.congr_ae (EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ ?_)
    ext m
    simp [iteratedFDeriv_one_apply]
  -- the limit function and derivative are locally integrable
  have hfl : LocallyIntegrableOn ({x | x (Fin.last d) < 0}.indicator g) Ω volume :=
    (hg.continuous.locallyIntegrable.indicator hL).locallyIntegrableOn _
  have hwl : LocallyIntegrableOn (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin
    (d + 1))) F).symm
      ({x | x (Fin.last d) < 0}.indicator (fderiv ℝ g) x)) Ω volume := by
    have h1 : LocallyIntegrable ({x | x (Fin.last d) < 0}.indicator (fderiv ℝ g)) volume :=
      (hg.continuous_fderiv one_ne_zero).locallyIntegrable.indicator hL
    exact (h1.locallyIntegrableOn _).comp_continuousLinearMap
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
        F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- the dominated convergence of the two `L^1(Ω)` norms
  have key := hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one hGw hfl hwl ?_ ?_
  · exact key
  · -- `G n → 1_{x_N<0} g` in `L^1(Ω)`
    have hmeas : ∀ n, AEStronglyMeasurable (G n - {x | x (Fin.last d) < 0}.indicator g)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun n ↦
      (hGs n).continuous.aestronglyMeasurable.sub
        (hg.continuous.aestronglyMeasurable.indicator hL)
    refine Tendsto.congr (fun n ↦ (eLpNorm_one_eq_lintegral_enorm (hmeas n)).symm) ?_
    rw [show (0 : ℝ≥0∞) = ∫⁻ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), (0 : ℝ≥0∞) from by
      simp]
    refine tendsto_lintegral_of_dominated_convergence' (fun _ ↦ ENNReal.ofReal M)
      (fun n ↦ (hmeas n).enorm) (fun n ↦ ?_) ?_ ?_
    · filter_upwards [ae_restrict_mem hΩm] with x hx
      rw [Pi.sub_apply, hGx]
      have hb : ‖η n x • g x - {x | x (Fin.last d) < 0}.indicator g x‖ ≤ M := by
        have e : η n x • g x - {x | x (Fin.last d) < 0}.indicator g x
            = (η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x) • g x := by
          rw [sub_smul]
          congr 1
          by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]
        rw [e, norm_smul, Real.norm_eq_abs]
        have h1 : |η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
          have := hη01 n x
          have h0 : 0 ≤ η n x := by rw [hηx]; exact reflectionCutoff_nonneg _
          by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
          · rw [Set.indicator_of_mem h]
            rw [abs_le] at this ⊢
            constructor <;> linarith
          · rw [Set.indicator_of_notMem h, sub_zero]
            exact this
        calc |η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x| * ‖g x‖
            ≤ 1 * M := mul_le_mul h1 (hM x (subset_closure hx)) (norm_nonneg _) zero_le_one
          _ = M := one_mul _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hb
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΩfin
    · filter_upwards [ae_restrict_of_ae ae_apply_last_ne_zero] with x hx
      have h1 := ((hηlim x hx).sub (tendsto_const_nhds (x := {x : EuclideanSpace ℝ (Fin (d + 1)) |
        x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x))).smul_const (g x)
      rw [sub_self, zero_smul] at h1
      have h2 : Tendsto (fun n ↦ G n x - {x | x (Fin.last d) < 0}.indicator g x) atTop (𝓝 0) := by
        refine h1.congr fun n ↦ ?_
        rw [hGx, sub_smul]
        congr 1
        by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]
      have := (continuous_enorm.tendsto (0 : F)).comp h2
      simpa [Function.comp_def, enorm_zero] using this
  · -- `∇G n → 1_{x_N<0} ∇g` in `L^1(Ω)`
    obtain ⟨e, he⟩ : ∃ e : (EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F) ≃ₗᵢ[ℝ]
        (EuclideanSpace ℝ (Fin (d + 1)) [×1]→L[ℝ] F),
      e = (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm := ⟨_, rfl⟩
    have hmeas : ∀ n, AEStronglyMeasurable
        ((fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
          (fderiv ℝ (G n) x))
          - fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
            ({x | x (Fin.last d) < 0}.indicator (fderiv ℝ g) x)) (volume.restrict (Ω : Set
              (EuclideanSpace ℝ (Fin (d + 1))))) :=
      fun n ↦ ((continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
        F).symm.continuous.comp_aestronglyMeasurable
        ((hGs n).continuous_fderiv one_ne_zero).aestronglyMeasurable).sub
        ((continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
          F).symm.continuous.comp_aestronglyMeasurable
          ((hg.continuous_fderiv one_ne_zero).aestronglyMeasurable.indicator hL))
    refine Tendsto.congr (fun n ↦ (eLpNorm_one_eq_lintegral_enorm (hmeas n)).symm) ?_
    rw [show (0 : ℝ≥0∞) = ∫⁻ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), (0 : ℝ≥0∞) from by
      simp]
    refine tendsto_lintegral_of_dominated_convergence'
      (fun _ ↦ ENNReal.ofReal (M' + M' * Cη * ‖innerSL ℝ v‖))
      (fun n ↦ (hmeas n).enorm) (fun n ↦ ?_) ?_ ?_
    · filter_upwards [ae_restrict_mem hΩm] with x hx
      rw [Pi.sub_apply, ← map_sub, ← ofReal_norm, LinearIsometryEquiv.norm_map]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [(hGd n x).fderiv]
      have e1 : η n x • fderiv ℝ g x
          + (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • (((n : ℝ) + 1) • innerSL ℝ
            v)).smulRight
            (g x) - {x | x (Fin.last d) < 0}.indicator (fderiv ℝ g) x
          = (η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x) • fderiv ℝ g x
            + (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)
              • (((n : ℝ) + 1) • innerSL ℝ v)).smulRight (g x) := by
        rw [sub_smul]
        by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]; abel
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]; abel
      rw [e1]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        have h1 : |η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
          have := hη01 n x
          have h0 : 0 ≤ η n x := by rw [hηx]; exact reflectionCutoff_nonneg _
          by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
          · rw [Set.indicator_of_mem h]
            rw [abs_le] at this ⊢
            constructor <;> linarith
          · rw [Set.indicator_of_notMem h, sub_zero]
            exact this
        calc |η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x| * ‖fderiv ℝ g x‖
            ≤ 1 * M' := mul_le_mul h1 (hM' x (subset_closure hx)) (norm_nonneg _) zero_le_one
          _ = M' := one_mul _
      · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), mul_comm]
        exact hgη n x hx
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΩfin
    · filter_upwards [ae_restrict_of_ae ae_apply_last_ne_zero] with x hx
      have h1 := ((hηlim x hx).sub (tendsto_const_nhds (x := {x : EuclideanSpace ℝ (Fin (d + 1)) |
        x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x))).smul_const (fderiv ℝ g x)
      rw [sub_self, zero_smul] at h1
      have h2 : Tendsto (fun n : ℕ ↦ (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)
          • (((n : ℝ) + 1) • innerSL ℝ v)).smulRight (g x)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hη'lim x hx] with n hn
        rw [hn, zero_smul, ContinuousLinearMap.zero_smulRight]
      have h3 : Tendsto (fun n ↦ fderiv ℝ (G n) x - {x | x (Fin.last d) < 0}.indicator (fderiv ℝ g)
        x)
          atTop (𝓝 0) := by
        have := h1.add h2
        rw [add_zero] at this
        refine this.congr fun n ↦ ?_
        rw [(hGd n x).fderiv, sub_smul]
        by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]; abel
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]; abel
      have h4 := ((continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
        F).symm.continuous.tendsto 0).comp h3
      rw [map_zero] at h4
      have := (continuous_enorm.tendsto (0 : EuclideanSpace ℝ (Fin (d + 1)) [×1]→L[ℝ] F)).comp h4
      simpa [Function.comp_def, map_sub, enorm_zero] using this

end Gluing

/-! ### The higher-order reflection at order one: the identity -/

section ReflectionIdentity

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
  {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- A compact subset of `Q_r` lies in a cylinder `Q_{r'}` with `r' < r`. -/
theorem exists_lt_subset_cylinder {r : ℝ} {K : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hK : IsCompact K) (hKQ : K ⊆ cylinder d r) : ∃ r', r' < r ∧ K ⊆ cylinder d r' := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨r - 1, by linarith, empty_subset _⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_init.norm.max continuous_abs_apply_last).continuousOn
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max ‖init x₀‖ |x₀ (Fin.last d)| := ⟨_, rfl⟩
  have hm1 : m < r := by rw [hm]; exact max_lt (hKQ hx₀).1 (hKQ hx₀).2
  refine ⟨(m + r) / 2, by linarith, fun x hx ↦ ?_⟩
  have h : max ‖init x‖ |x (Fin.last d)| ≤ m := by rw [hm]; exact hmax hx
  exact ⟨by linarith [le_max_left ‖init x‖ |x (Fin.last d)|],
    by linarith [le_max_right ‖init x‖ |x (Fin.last d)|]⟩

/-- The closure of `Q_{r'}`, `r' < r`, lies in `Q_r`. -/
theorem closure_cylinder_subset_cylinder {r' r : ℝ} (h : r' < r) :
    closure (cylinder d r' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ cylinder d r :=
  fun _ hx ↦ ⟨(closure_cylinder_subset r' hx).1.trans_lt h,
    (closure_cylinder_subset r' hx).2.trans_lt h⟩

/-- The higher-order reflection of a difference. -/
theorem higherReflection_sub (a l : Fin m → ℝ) (f g : EuclideanSpace ℝ (Fin (d + 1)) → F) :
    higherReflection a l (f - g) = higherReflection a l f - higherReflection a l g := by
  rw [sub_eq_add_neg, higherReflection_add, sub_eq_add_neg]
  congr 1
  rw [← neg_one_smul ℝ g, higherReflection_smul, neg_one_smul]

/-- The reflected derivative of a difference. -/
theorem higherReflectionFDeriv_sub (a l : Fin m → ℝ)
    (D₁ D₂ : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F) :
    higherReflectionFDeriv a l (D₁ - D₂)
      = higherReflectionFDeriv a l D₁ - higherReflectionFDeriv a l D₂ := by
  funext x
  simp only [higherReflectionFDeriv, Pi.sub_apply]
  split_ifs
  · rfl
  · simp only [ContinuousLinearMap.sub_comp, smul_sub, Finset.sum_sub_distrib]

/-- **The higher-order reflection of any function is the function plus a cut-off correction**:
`P g = g + 1_{x_N < 0} (∑ a_j g ∘ S_j − g)`. -/
theorem higherReflection_eq_add_indicator (a l : Fin m → ℝ)
    (g : EuclideanSpace ℝ (Fin (d + 1)) → F) :
    higherReflection a l g = g + {x | x (Fin.last d) < 0}.indicator
      (fun x ↦ ∑ j, a j • g (scaleLast (l j) x) - g x) := by
  funext x
  by_cases hx : x (Fin.last d) < 0
  · rw [Pi.add_apply, higherReflection_of_neg a l hx, Set.indicator_of_mem
      (show x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0} from hx)]
    abel
  · rw [Pi.add_apply, higherReflection_of_nonneg a l (not_lt.1 hx), Set.indicator_of_notMem
      (show x ∉ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0} from hx), add_zero]

/-- The derivative of the correction `∑ a_j g ∘ S_j − g` for a `C^1` function `g`. -/
theorem hasFDerivAt_sum_comp_scaleLast_sub (a l : Fin m → ℝ)
    {g : EuclideanSpace ℝ (Fin (d + 1)) → F} (hg : ContDiff ℝ 1 g)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    HasFDerivAt (fun x ↦ ∑ j, a j • g (scaleLast (l j) x) - g x)
      (∑ j, a j • (fderiv ℝ g (scaleLast (l j) x)).comp (scaleLast (l j)) - fderiv ℝ g x) x := by
  refine HasFDerivAt.sub (HasFDerivAt.fun_sum fun j _ ↦ HasFDerivAt.const_smul ?_ (a j))
    (hg.differentiable one_ne_zero x).hasFDerivAt
  exact (hg.differentiable one_ne_zero (scaleLast (l j) x)).hasFDerivAt.comp x
    (scaleLast (l j)).hasFDerivAt

/-- The correction `∑ a_j g ∘ S_j − g` is `C^1` when `g` is. -/
theorem contDiff_sum_comp_scaleLast_sub (a l : Fin m → ℝ)
    {g : EuclideanSpace ℝ (Fin (d + 1)) → F} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 fun x ↦ ∑ j, a j • g (scaleLast (l j) x) - g x :=
  (ContDiff.sum fun j _ ↦ (hg.comp (scaleLast (l j)).contDiff).const_smul (a j)).sub hg

/-- **The higher-order reflection of a `C^1` function has the piecewise derivative as weak
derivative** on the cylinder `Q_r`, when `∑ a_j = 1` and `|l_j| ≤ 1`: `P g = g + 1_{x_N<0} G`
with `G = ∑ a_j g ∘ S_j − g` vanishing on the hyperplane (since `S_j` fixes it and
`∑ a_j = 1`), and the gluing lemma `hasWeakFDerivOn_indicator_lowerHalf_of_contDiff`. -/
theorem hasWeakFDerivOn_higherReflection_of_contDiff {a l : Fin m → ℝ} (ha : ∑ j, a j = 1)
    {g : EuclideanSpace ℝ (Fin (d + 1)) → F} (hg : ContDiff ℝ 1 g) (r : ℝ) :
    HasWeakFDerivOn (higherReflection a l g) (higherReflectionFDeriv a l (fderiv ℝ g))
      (cylinder d r) volume := by
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (d + 1)) → F,
    G = fun x ↦ ∑ j, a j • g (scaleLast (l j) x) - g x := ⟨_, rfl⟩
  have hGs : ContDiff ℝ 1 G := by rw [hG]; exact contDiff_sum_comp_scaleLast_sub a l hg
  have hG0 : ∀ x, x (Fin.last d) = 0 → G x = 0 := by
    intro x hx
    rw [hG]
    simp only
    simp_rw [scaleLast_of_apply_last_eq_zero _ hx, ← Finset.sum_smul, ha, one_smul, sub_self]
  have hGd : ∀ x, fderiv ℝ G x
      = ∑ j, a j • (fderiv ℝ g (scaleLast (l j) x)).comp (scaleLast (l j)) - fderiv ℝ g x := by
    intro x
    rw [hG]
    exact (hasFDerivAt_sum_comp_scaleLast_sub a l hg x).fderiv
  have h1 := hasWeakFDerivOn_indicator_lowerHalf_of_contDiff hGs hG0 (isCompact_closure_cylinder r)
    (convex_cylinder r) (fun x hx ↦ scaleLast_mem_cylinder (by simp) hx)
  have h2 : HasWeakFDerivOn g (fderiv ℝ g) (cylinder d r) volume := by
    have := hg.contDiffOn.hasWeakIteratedFDerivOn (Ω := cylinder d r) (μ := volume) (m := 1) le_rfl
    refine this.congr_ae (EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ ?_)
    ext m
    simp [iteratedFDeriv_one_apply]
  have h3 := (h2 : HasWeakIteratedFDerivOn 1 g _ (cylinder d r) volume).add
    (h1 : HasWeakIteratedFDerivOn 1 _ _ (cylinder d r) volume)
  refine h3.congr_ae (Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
  · rw [higherReflection_eq_add_indicator a l g, hG]
  · simp only [Pi.add_apply, ← map_add]
    congr 1
    by_cases hx : x (Fin.last d) < 0
    · rw [Set.indicator_of_mem (show x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) |
          x (Fin.last d) < 0} from hx), higherReflectionFDeriv_of_neg a l hx, hGd]
      abel
    · rw [Set.indicator_of_notMem (show x ∉ {x : EuclideanSpace ℝ (Fin (d + 1)) |
          x (Fin.last d) < 0} from hx), higherReflectionFDeriv_of_nonneg a l (not_lt.1 hx),
            add_zero]

/-- The `L^1(Q_{r'})` norm of a reflected function tends to zero with the `L^1(Q_{r'}₊)` norm of
the function. -/
theorem tendsto_eLpNorm_higherReflection_of_tendsto {a l : Fin m → ℝ} (hl : IsReflectionSet l V)
    {f : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hf : ∀ i, AEStronglyMeasurable (f i)
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set (EuclideanSpace ℝ (Fin (d +
        1))))))
    (h : Tendsto (fun i ↦ eLpNorm (f i) 1
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set (EuclideanSpace ℝ (Fin (d +
        1)))))) atTop (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (higherReflection a l (f i)) 1
      (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hCf, -, -⟩ := hl.exists_facts (F := F) a 1
  have h' := ENNReal.Tendsto.const_mul h (Or.inr hC)
  rw [mul_zero] at h'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (fun _ ↦ zero_le)
    fun i ↦ (hCf (f i) (hf i)).2

/-- The `L^1(Q_{r'})` norm of a reflected derivative tends to zero with the `L^1(Q_{r'}₊)` norm
of the derivative. -/
theorem tendsto_eLpNorm_higherReflectionFDeriv_of_tendsto {a l : Fin m → ℝ}
    (hl : IsReflectionSet l V)
    {D : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    (hD : ∀ i, AEStronglyMeasurable (D i)
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set (EuclideanSpace ℝ (Fin (d +
        1))))))
    (h : Tendsto (fun i ↦ eLpNorm (D i) 1
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set (EuclideanSpace ℝ (Fin (d +
        1)))))) atTop (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (higherReflectionFDeriv a l (D i)) 1
      (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))) atTop (𝓝 0) := by
  obtain ⟨C, hC, -, hCD, -⟩ := hl.exists_facts (F := F) a 1
  have h' := ENNReal.Tendsto.const_mul h (Or.inr hC)
  rw [mul_zero] at h'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (fun _ ↦ zero_le)
    fun i ↦ (hCD (D i) (hD i)).2

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The tensor membership `w ∈ W^{1,1}(V₊)` from a weak derivative in `L^p`, on a set of finite
volume. -/
theorem memSobolev_one_of_hasWeakFDerivOn {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hVfin : volume (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
    {w : EuclideanSpace ℝ (Fin (d + 1)) → F}
    {Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    (hw : HasWeakFDerivOn w Dw V volume)
    (hwp : MemLp w p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hDp : MemLp Dw p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    MemSobolev w 1 1 V volume := by
  have hfin : IsFiniteMeasure (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hVfin⟩
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hw1 : MemLp w 1 (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hwp.mono_exponent hp
  have hD1 : MemLp Dw 1 (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hDp.mono_exponent hp
  refine ⟨hw1, fun n hn ↦ ?_⟩
  have hn' : n ≤ 1 := by exact_mod_cast hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · refine ⟨fun x ↦ (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
      (w x), hasWeakIteratedFDerivOn_zero (hw1.locallyIntegrableOn le_rfl), ?_⟩
    exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
      F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hw1
  · refine ⟨fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
      (Dw x), hw, ?_⟩
    exact (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
      F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hD1

variable [CompleteSpace F]

/-- **The higher-order reflection at order one, the identity** (the analogue of
[brezis2011functional] Lemma 9.2 for the multi-scale reflection): for `u ∈ W^{1,p}(Q_r₊)` with
weak derivative `Dw`, `1 ≤ p ≤ ∞`, scales `l_j ∈ [-1, 0)` and coefficients with `∑ a_j = 1`, the
reflection `P u` has the weak derivative `higherReflectionFDeriv a l Dw` on `Q_r`.

The cancellation across the interface that the even reflection enjoys is lost here, and the
identity is obtained by approximation instead: the even reflection `u^⋆ ∈ W^{1,1}(Q_r)`
(Lemma 9.2) is approximated on a smaller cylinder `Q_{r'}` by smooth functions `g_i`
(`MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`, the interior mollification); for the smooth
`g_i`, `P g_i` has the piecewise derivative (`hasWeakFDerivOn_higherReflection_of_contDiff`);
`P g_i → P u` and the derivatives converge in `L^1(Q_{r'})` (the `L^1` bound of the reflection);
the weak derivative is closed under `L^1` limits; and the identity on `Q_r` is local. -/
theorem hasWeakFDerivOn_higherReflection {r : ℝ} {a l : Fin m → ℝ} (ha : ∑ j, a j = 1)
    (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j) {w : EuclideanSpace ℝ (Fin (d + 1)) → F}
    {Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    (hw : HasWeakFDerivOn w Dw (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume)
    (hwp : MemLp w p
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace
        ℝ (Fin (d + 1))))))
    (hDp : MemLp Dw p
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace
        ℝ (Fin (d + 1)))))) :
    HasWeakFDerivOn (higherReflection a l w) (higherReflectionFDeriv a l Dw) (cylinder d r)
      volume := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hv : ‖(single (Fin.last d) (1 : ℝ) : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 :=
    EuclideanSpace.norm_single_last_one
  have hV := hyperplaneReflection_image_cylinder (d := d) r
  have hQ : IsReflectionSet l (cylinder d r) := isReflectionSet_cylinder hl hl1 r
  have hQfin : volume (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ
    (Fin (d + 1)))) ≠ ⊤ :=
    ((measure_mono (posHalf_le _ _)).trans_lt (volume_cylinder_lt_top r)).ne
  -- Lemma 9.2 for the even reflection, at exponent one
  have hu1 : MemSobolev w 1 1 (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume :=
    memSobolev_one_of_hasWeakFDerivOn hQfin hw hwp hDp
  have hev : HasWeakFDerivOn (evenReflection (single (Fin.last d) (1 : ℝ)) w)
      (reflectFDeriv (single (Fin.last d) (1 : ℝ)) Dw) (cylinder d r) volume :=
    hw.evenReflection hv hV hp hwp hDp
  have hevs : MemSobolev (evenReflection (single (Fin.last d) (1 : ℝ)) w) 1 1 (cylinder d r)
      volume := hu1.evenReflection hv hV le_rfl
  -- local integrability of the reflected function and derivative
  obtain ⟨C, hC, hCf, hCD, -⟩ := hQ.exists_facts (F := F) a p
  have hRp : MemLp (higherReflection a l w) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hCf w hwp.aestronglyMeasurable).2.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hwp)
  have hRDp : MemLp (higherReflectionFDeriv a l Dw) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hCD Dw hDp.aestronglyMeasurable).2.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hDp)
  have hRl : LocallyIntegrableOn (higherReflection a l w) (cylinder d r) volume :=
    hRp.locallyIntegrableOn hp
  have hRDl : LocallyIntegrableOn (fun x ↦ (continuousMultilinearCurryFin1 ℝ
      (EuclideanSpace ℝ (Fin (d + 1))) F).symm (higherReflectionFDeriv a l Dw x))
      (cylinder d r) volume :=
    (hRDp.locallyIntegrableOn hp).comp_continuousLinearMap
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
        F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- locality: it suffices to prove the identity on the cylinders `Q_{r'}`, `r' < r`
  refine HasWeakIteratedFDerivOn.of_forall_isCompact_closure_subset hRl hRDl fun Ω' hΩ'c hΩ'Q ↦ ?_
  obtain ⟨r', hr', hΩ'r'⟩ := exists_lt_subset_cylinder hΩ'c hΩ'Q
  refine HasWeakIteratedFDerivOn.mono ?_ (subset_closure.trans hΩ'r')
  have hQ' : IsReflectionSet l (cylinder d r') := isReflectionSet_cylinder hl hl1 r'
  have hQ'Q : (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set (EuclideanSpace ℝ (Fin
    (d + 1))))
      ⊆ (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d +
        1)))) := fun x hx ↦
    mem_posHalf_last_iff.2 ⟨closure_cylinder_subset_cylinder hr'
      (subset_closure (mem_posHalf_last_iff.1 hx).1), (mem_posHalf_last_iff.1 hx).2⟩
  -- the smooth approximants of `u^⋆` on `Q_{r'}`
  obtain ⟨g, hgs, hg0, hg1⟩ := hevs.exists_seq_contDiff_tendsto_eLpNorm le_rfl ENNReal.one_ne_top
    (cylinder d r').isOpen (isCompact_closure_cylinder r') (closure_cylinder_subset_cylinder hr')
  have hg1' := hg1 1 (by simp)
  -- the smooth approximants satisfy the identity
  have hGw : ∀ i, HasWeakIteratedFDerivOn 1 (higherReflection a l (g i))
      (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
        (higherReflectionFDeriv a l (fderiv ℝ (g i)) x)) (cylinder d r') volume := fun i ↦
    hasWeakFDerivOn_higherReflection_of_contDiff ha ((hgs i).of_le (by simp)) r'
  refine hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one hGw
    (hRl.mono_set (subset_closure.trans (closure_cylinder_subset_cylinder hr')))
    (hRDl.mono_set (subset_closure.trans (closure_cylinder_subset_cylinder hr'))) ?_ ?_
  · -- `P g_i → P u` in `L^1(Q_{r'})`
    have hsub : ∀ i, higherReflection a l (g i) - higherReflection a l w
        = higherReflection a l (g i - w) := fun i ↦ (higherReflection_sub a l _ _).symm
    simp only [hsub]
    refine tendsto_eLpNorm_higherReflection_of_tendsto hQ'
      (fun i ↦ (hgs i).continuous.aestronglyMeasurable.sub
        (hwp.aestronglyMeasurable.mono_measure (Measure.restrict_mono hQ'Q le_rfl))) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg0 (fun _ ↦ zero_le)
      fun i ↦ ?_
    calc eLpNorm (g i - w) 1 (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ))
          (cylinder d r') : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        = eLpNorm (g i - evenReflection (single (Fin.last d) (1 : ℝ)) w) 1
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
            (EuclideanSpace ℝ (Fin (d + 1))))) := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [ae_restrict_mem (posHalf _ (cylinder d r')).isOpen.measurableSet]
            with x hx
          rw [Pi.sub_apply, Pi.sub_apply, evenReflection_of_nonneg]
          rw [EuclideanSpace.inner_single_last_one]
          exact (mem_posHalf_last_iff.1 hx).2.le
      _ ≤ eLpNorm (g i - evenReflection (single (Fin.last d) (1 : ℝ)) w) 1
          (volume.restrict (cylinder d r' : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono (posHalf_le _ _) le_rfl)
  · -- the derivatives converge in `L^1(Q_{r'})`
    have hsub : ∀ i, (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
          F).symm (higherReflectionFDeriv a l (fderiv ℝ (g i)) x))
        - (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
          (higherReflectionFDeriv a l Dw x))
        = fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
          (higherReflectionFDeriv a l (fderiv ℝ (g i) - Dw) x) := fun i ↦ by
      funext x
      rw [Pi.sub_apply, ← map_sub, higherReflectionFDeriv_sub, Pi.sub_apply]
    simp only [hsub]
    obtain ⟨C', hC'0, hC'f, hC'D, -⟩ := hQ'.exists_facts (F := F) a 1
    have hmeasD : ∀ i, AEStronglyMeasurable (fderiv ℝ (g i) - Dw)
        (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
          (EuclideanSpace ℝ (Fin (d + 1))))) :=
      fun i ↦ ((hgs i).continuous_fderiv (by simp)).aestronglyMeasurable.sub
        (hDp.aestronglyMeasurable.mono_measure (Measure.restrict_mono hQ'Q le_rfl))
    have hiso : ∀ i, eLpNorm (fun x ↦ (continuousMultilinearCurryFin1 ℝ
          (EuclideanSpace ℝ (Fin (d + 1))) F).symm (higherReflectionFDeriv a l
            (fderiv ℝ (g i) - Dw) x)) 1 (volume.restrict (cylinder d r' : Set (EuclideanSpace ℝ
              (Fin (d + 1)))))
        = eLpNorm (higherReflectionFDeriv a l (fderiv ℝ (g i) - Dw)) 1
          (volume.restrict (cylinder d r' : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun i ↦ by
      refine eLpNorm_congr_enorm_ae ((continuousMultilinearCurryFin1 ℝ
        (EuclideanSpace ℝ (Fin (d + 1))) F).symm.continuous.comp_aestronglyMeasurable
        (hC'D _ (hmeasD i)).1) (hC'D _ (hmeasD i)).1 (Eventually.of_forall fun x ↦ ?_)
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
    simp only [hiso]
    refine tendsto_eLpNorm_higherReflectionFDeriv_of_tendsto hQ' hmeasD ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg1' (fun _ ↦ zero_le)
      fun i ↦ ?_
    have hae : ∀ᵐ x ∂volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
      (EuclideanSpace ℝ (Fin (d + 1)))),
        ‖(fderiv ℝ (g i) - Dw) x‖ₑ = ‖(iteratedFDeriv ℝ 1 (g i)
          - weakIteratedFDeriv 1 (evenReflection (single (Fin.last d) (1 : ℝ)) w) (cylinder d r)
            volume) x‖ₑ := by
      filter_upwards [ae_restrict_mem (posHalf _ (cylinder d r')).isOpen.measurableSet,
        ae_restrict_of_ae hev.weakIteratedFDeriv_ae_eq] with x hx hx'
      rw [Pi.sub_apply, Pi.sub_apply, hx' (closure_cylinder_subset_cylinder hr'
        (subset_closure (mem_posHalf_last_iff.1 hx).1)), reflectFDeriv_of_nonneg]
      · rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
        congr 1
        have e : iteratedFDeriv ℝ 1 (g i) x = (continuousMultilinearCurryFin1 ℝ
            (EuclideanSpace ℝ (Fin (d + 1))) F).symm (fderiv ℝ (g i) x) := by
          ext m
          simp [iteratedFDeriv_one_apply]
        rw [e, ← map_sub, LinearIsometryEquiv.nnnorm_map]
      · rw [EuclideanSpace.inner_single_last_one]
        exact (mem_posHalf_last_iff.1 hx).2.le
    calc eLpNorm (fderiv ℝ (g i) - Dw) 1
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
            (EuclideanSpace ℝ (Fin (d + 1)))))
        ≤ eLpNorm (iteratedFDeriv ℝ 1 (g i) - weakIteratedFDeriv 1
            (evenReflection (single (Fin.last d) (1 : ℝ)) w) (cylinder d r) volume) 1
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
            (EuclideanSpace ℝ (Fin (d + 1))))) :=
          eLpNorm_mono_enorm_ae (hmeasD i) (hae.mono fun x hx ↦ hx.le)
      _ ≤ eLpNorm (iteratedFDeriv ℝ 1 (g i) - weakIteratedFDeriv 1
            (evenReflection (single (Fin.last d) (1 : ℝ)) w) (cylinder d r) volume) 1
          (volume.restrict (cylinder d r' : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono (posHalf_le _ _) le_rfl)

end ReflectionIdentity

/-! ### The higher-order reflection at order one: membership and the typed operator -/

section ReflectionMembership

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
  {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {a l : Fin m → ℝ}

/-- The higher-order reflection only sees the function up to a null set of `V₊`. -/
theorem IsReflectionSet.higherReflection_congr_ae (hV : IsReflectionSet l V) (a : Fin m → ℝ)
    {f g : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (h : f =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V :
      Set (EuclideanSpace ℝ (Fin (d + 1))))] g) :
    _root_.higherReflection a l f =ᵐ[volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      _root_.higherReflection a l g := by
  obtain ⟨-, -, -, -, hP⟩ := hV.exists_facts (F := F) a 1
  have h1 : ∀ᵐ x ∂volume, x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) V :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) → f x = g x :=
    (ae_restrict_iff' (posHalf _ V).isOpen.measurableSet).1 h
  have h2 : ∀ᵐ x ∂volume, x ∈ negHalf V → ∀ j, f (scaleLast (l j) x) = g (scaleLast (l j) x) :=
    (ae_restrict_iff' isOpen_negHalf'.measurableSet).1 (hP h)
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet, ae_restrict_of_ae ae_apply_last_ne_zero,
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with x hxV hx hx1 hx2
  rcases lt_or_gt_of_ne hx with h | h
  · rw [higherReflection_of_neg a l h, higherReflection_of_neg a l h]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hx2 ⟨hxV, h⟩ j]
  · rw [higherReflection_of_nonneg a l h.le, higherReflection_of_nonneg a l h.le]
    exact hx1 (mem_posHalf_last_iff.2 ⟨hxV, h⟩)

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ (EuclideanSpace ℝ (Fin (d + 1)))}
  [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℝ}

/-- **The higher-order reflection at order one, membership**: for scales `l_j ∈ [-1, 0)`,
coefficients with `∑ a_j = 1` and `u ∈ W^{1,p}(Q_r₊)`, `1 ≤ p ≤ ∞`, the reflection `P u` lies in
`W^{1,p}(Q_r)` (the analogue of [brezis2011functional] Lemma 9.2). -/
theorem MemSobolev.higherReflection (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0)
    (hl1 : ∀ j, -1 ≤ l j) {u : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hu : MemSobolev u 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    MemSobolev (_root_.higherReflection a l u) 1 p (cylinder d r) volume := by
  obtain ⟨w, hw, hwp⟩ := hu.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  obtain ⟨e, he⟩ : ∃ e : (EuclideanSpace ℝ (Fin (d + 1)) [×1]→L[ℝ] F) ≃ₗᵢ[ℝ]
      (EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F),
    e = continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F := ⟨_, rfl⟩
  have hw' : HasWeakFDerivOn u (fun x ↦ e (w x))
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume := by
    unfold HasWeakFDerivOn
    rw [he]
    simpa using hw
  have hwp' : MemLp (fun x ↦ e (w x)) p (volume.restrict
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d +
        1))))) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hwp
  have hid := hasWeakFDerivOn_higherReflection ha hl hl1 hw' hu.memLp hwp'
  obtain ⟨C, hC, hCf, hCD, -⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a p
  have hup : MemLp (_root_.higherReflection a l u) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hCf u hu.memLp.aestronglyMeasurable).2.trans_lt
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hu.memLp)
  have hWp : MemLp (higherReflectionFDeriv a l fun x ↦ e (w x)) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hCD _ hwp'.aestronglyMeasurable).2.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hwp')
  refine ⟨hup, fun n hn ↦ ?_⟩
  have hn' : n ≤ 1 := by exact_mod_cast hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · refine ⟨fun x ↦ (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
      (_root_.higherReflection a l u x), hasWeakIteratedFDerivOn_zero hid.locallyIntegrableOn, ?_⟩
    exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
      F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hup
  · refine ⟨fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
      (higherReflectionFDeriv a l (fun x ↦ e (w x)) x), hid, ?_⟩
    exact (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
      F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hWp

/-- The higher-order reflection at order one in the multi-index formulation. -/
theorem MemSobolevMultiIndex.higherReflection (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0)
    (hl1 : ∀ j, -1 ≤ l j) {u : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hu : MemSobolevMultiIndex b u 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r))
      volume) :
    MemSobolevMultiIndex b (_root_.higherReflection a l u) 1 p (cylinder d r) volume :=
  (hu.memSobolev.higherReflection ha hl hl1).memSobolevMultiIndex

namespace SobolevMultiIndex

variable (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
include ha hl hl1

/-- **The higher-order reflection on the typed spaces**, as a function: the element of
`W^{1,p}(Q_r)` whose function is `P u`. It is linear and bounded;
`SobolevMultiIndex.higherReflectionL` is its bundled form. -/
def higherReflection (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    SobolevMultiIndex F b 1 p (cylinder d r) volume :=
  ((memSobolevMultiIndex u).higherReflection ha hl hl1).exists_sobolevMultiIndex.choose

/-- The function of `SobolevMultiIndex.higherReflection ha hl hl1 u` is `P u`. -/
theorem fn_higherReflection (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    fn (higherReflection ha hl hl1 u)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        _root_.higherReflection a l (fn u) :=
  ((memSobolevMultiIndex u).higherReflection ha hl hl1).exists_sobolevMultiIndex.choose_spec

/-- On `Q_r₊`, the reflected element is `u`. -/
theorem fn_higherReflection_restrict (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    fn (higherReflection ha hl hl1 u)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (posHalf_le _ _)
    (fn_higherReflection ha hl hl1 u),
    ae_restrict_mem (posHalf _ (cylinder d r)).isOpen.measurableSet] with x hx hxV
  rw [hx, higherReflection_of_nonneg a l (mem_posHalf_last_iff.1 hxV).2.le]

/-- The typed reflection is additive. -/
theorem higherReflection_add (u w : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    higherReflection ha hl hl1 (u + w)
      = higherReflection ha hl hl1 u + higherReflection ha hl hl1 w := by
  refine ext_of_fn_ae_eq ((fn_higherReflection ha hl hl1 (u + w)).trans (EventuallyEq.trans ?_
    (fn_add _ _).symm))
  refine ((isReflectionSet_cylinder hl hl1 r).higherReflection_congr_ae a (fn_add u w)).trans ?_
  rw [_root_.higherReflection_add]
  exact ((fn_higherReflection ha hl hl1 u).add (fn_higherReflection ha hl hl1 w)).symm

/-- The typed reflection commutes with scalar multiplication. -/
theorem higherReflection_smul (c : ℝ) (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    higherReflection ha hl hl1 (c • u) = c • higherReflection ha hl hl1 u := by
  refine ext_of_fn_ae_eq ((fn_higherReflection ha hl hl1 (c • u)).trans (EventuallyEq.trans ?_
    (fn_smul _ _).symm))
  refine ((isReflectionSet_cylinder hl hl1 r).higherReflection_congr_ae a (fn_smul c u)).trans ?_
  rw [_root_.higherReflection_smul]
  exact ((fn_higherReflection ha hl hl1 u).const_smul c).symm

/-- The partial derivatives of the reflected element, in terms of a tensor derivative `w` of
`u`: `∂ᵢ (P u) = (higherReflectionFDeriv a l w) (bᵢ)` almost everywhere on `Q_r`. -/
theorem weakDeriv_higherReflection_single (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume)
    {w : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    (hw : HasWeakFDerivOn (fn u) w (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume)
    (hwp : MemLp w p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))))) (i : ι) :
    weakDeriv (higherReflection ha hl hl1 u) (MultiIndexLE.single i)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ higherReflectionFDeriv a l w x (b i) := by
  have h1 := (hasWeakIteratedLineDerivOn (higherReflection ha hl hl1 u)
    (MultiIndexLE.single i)).of_perm (multiIndexTuple_single_perm (b : ι → _) i)
  have h2 := (((hasWeakFDerivOn_higherReflection ha hl hl1 hw (memLp u) hwp) :
    HasWeakIteratedFDerivOn 1 _ _ (cylinder d r) volume).lineDeriv ![b i]).congr_ae
    (fn_higherReflection ha hl hl1 u).symm (EventuallyEq.refl _ _)
  filter_upwards [(ae_restrict_iff' (cylinder d r).isOpen.measurableSet).2 (h1.ae_eq h2)] with x hx
  simpa using hx

/-- **The typed reflection is bounded**: `‖P u‖ ≤ C ‖u‖`. -/
theorem exists_norm_higherReflection_le :
    ∃ C : ℝ, ∀ u : SobolevMultiIndex F b 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume,
      ‖higherReflection ha hl hl1 u‖ ≤ C * ‖u‖ := by
  obtain ⟨C₀, hC₀, hCf, hCD, -⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a p
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card ι • ‖b.equivFunL.toContinuousLinearMap‖ :=
    ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = ∑ i, ‖b i‖ := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal Mb * (C₀ * ENNReal.ofReal Cb) := ⟨_, rfl⟩
  have hB' : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top)
  refine ⟨_, fun u ↦ norm_le_mul_norm_of_eLpNorm_le (higherReflection ha hl hl1 u) u hC₀ hB'
    ?_ fun i ↦ ?_⟩
  · rw [eLpNorm_congr_ae (fn_higherReflection ha hl hl1 u)]
    exact (hCf (fn u) (memLp u).aestronglyMeasurable).2
  obtain ⟨w, hw, hwp, -, hwn⟩ := exists_hasWeakFDerivOn_fn u
  rw [← hCb] at hwn
  have h1 : eLpNorm (weakDeriv (higherReflection ha hl hl1 u) (MultiIndexLE.single i)) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ ENNReal.ofReal Mb * eLpNorm (higherReflectionFDeriv a l w) p
        (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.memLp _).aestronglyMeasurable ?_ p
    filter_upwards [weakDeriv_higherReflection_single ha hl hl1 u hw hwp i] with x hx
    rw [hx, hMb]
    calc ‖higherReflectionFDeriv a l w x (b i)‖ ≤ ‖higherReflectionFDeriv a l w x‖ * ‖b i‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖higherReflectionFDeriv a l w x‖ * ∑ j, ‖b j‖ := by
          gcongr
          exact Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun _ _ ↦ norm_nonneg _)
            (Finset.mem_univ i)
      _ = (∑ j, ‖b j‖) * ‖higherReflectionFDeriv a l w x‖ := mul_comm _ _
  calc eLpNorm (weakDeriv (higherReflection ha hl hl1 u) (MultiIndexLE.single i)) p
        (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ ENNReal.ofReal Mb * (C₀ * (ENNReal.ofReal Cb
        * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
            Set (EuclideanSpace ℝ (Fin (d + 1))))))) := by
        refine h1.trans ?_
        gcongr
        exact (hCD w hwp.aestronglyMeasurable).2.trans (by gcongr)
    _ = B * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
            Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
        rw [hB]; ring

variable (F b p) in
/-- The higher-order reflection as a linear map `W^{1,p}(Q_r₊) → W^{1,p}(Q_r)`. -/
def higherReflectionₗ :
    SobolevMultiIndex F b 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume →ₗ[ℝ]
      SobolevMultiIndex F b 1 p (cylinder d r) volume where
  toFun := higherReflection ha hl hl1
  map_add' := higherReflection_add ha hl hl1
  map_smul' := higherReflection_smul ha hl hl1

variable (F b p) in
/-- **The higher-order reflection as a bounded linear map `W^{1,p}(Q_r₊) → W^{1,p}(Q_r)`**,
`u ↦ P u`, for scales `l_j ∈ [-1, 0)` and coefficients with `∑ a_j = 1`: its function is `P u`
(`SobolevMultiIndex.fn_higherReflectionL`), it restricts to `u` on `Q_r₊`
(`SobolevMultiIndex.fn_higherReflectionL_restrict`), and its `L^p` norm is bounded by a multiple
of `‖u‖_{L^p(Q_r₊)}` (`SobolevMultiIndex.exists_eLpNorm_fn_higherReflectionL_le`). It replaces
the even reflection `SobolevEuclidean.cubeReflectL` in the chart-local step of the proof of the
extension theorem when the Vandermonde conditions of higher order are imposed on `a`. -/
def higherReflectionL :
    SobolevMultiIndex F b 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume →L[ℝ]
      SobolevMultiIndex F b 1 p (cylinder d r) volume :=
  (higherReflectionₗ F b p ha hl hl1).mkContinuousOfExistsBound
    (exists_norm_higherReflection_le ha hl hl1)

/-- `SobolevMultiIndex.higherReflectionL` is `SobolevMultiIndex.higherReflection`. -/
@[simp]
theorem higherReflectionL_apply (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    higherReflectionL F b p ha hl hl1 u = higherReflection ha hl hl1 u :=
  rfl

/-- The function of `SobolevMultiIndex.higherReflectionL ha hl hl1 u` is `P u`. -/
theorem fn_higherReflectionL (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    fn (higherReflectionL F b p ha hl hl1 u)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        _root_.higherReflection a l (fn u) :=
  fn_higherReflection ha hl hl1 u

/-- On `Q_r₊`, `SobolevMultiIndex.higherReflectionL ha hl hl1 u` is `u`. -/
theorem fn_higherReflectionL_restrict (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    fn (higherReflectionL F b p ha hl hl1 u)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u :=
  fn_higherReflection_restrict ha hl hl1 u

/-- The `L^p` bound on `SobolevMultiIndex.higherReflectionL`. -/
theorem exists_eLpNorm_fn_higherReflectionL_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ u : SobolevMultiIndex F b 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume,
      eLpNorm (fn (higherReflectionL F b p ha hl hl1 u)) p
        (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        ≤ C * eLpNorm (fn u) p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ))
          (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  obtain ⟨C, hC, hCf, -, -⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a p
  refine ⟨C, hC, fun u ↦ ?_⟩
  rw [eLpNorm_congr_ae (fn_higherReflectionL ha hl hl1 u)]
  exact (hCf (fn u) (memLp u).aestronglyMeasurable).2

end SobolevMultiIndex

end ReflectionMembership

/-! ### The higher-order reflection at every order -/

section ReflectionHigher

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {m : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℝ} {a l : Fin m → ℝ}

open SobolevMultiIndex

/-- `scaleLast l` on the basis vectors: it scales `e_N` by `l` and fixes the others. -/
theorem scaleLast_single (l : ℝ) (i : Fin (d + 1)) :
    scaleLast l (single i (1 : ℝ)) = if i = Fin.last d then l • single i 1 else single i 1 := by
  ext j
  by_cases hi : i = Fin.last d
  · subst hi
    by_cases hj : j = Fin.last d
    · subst hj; simp [scaleLast_apply]
    · simp [scaleLast_apply, hj]
  · by_cases hj : j = Fin.last d
    · subst hj; simp [scaleLast_apply, hi, Ne.symm hi]
    · simp [scaleLast_apply, hi, hj]

/-- **The partial derivatives of the higher-order reflection**: for `u ∈ W^{1,p}(Q_r₊)` with
`∂ᵢ u = g` and `∑ a_j = 1`, the derivative `∂ᵢ (P_a u)` is `P_a g` for a tangential direction
`i ≠ N` and `P_{a l} (∂_N u)`, with the coefficients `a_j l_j`, for the normal one: the chain
rule on each term `a_j u ∘ S_j`, `S_j` fixing `eᵢ` for `i ≠ N` and scaling `e_N` by `l_j`. -/
theorem HasWeakIteratedLineDerivOn.higherReflection_single (ha : ∑ j, a j = 1)
    (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j) {u : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume)
    (i : Fin (d + 1)) {g : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hg : HasWeakIteratedLineDerivOn ![single i (1 : ℝ)] u g
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    HasWeakIteratedLineDerivOn ![single i (1 : ℝ)] (_root_.higherReflection a l u)
      (_root_.higherReflection (if i = Fin.last d then a * l else a) l g) (cylinder d r) volume :=
        by
  obtain ⟨U, hU⟩ := hu.exists_sobolevMultiIndex
  obtain ⟨Dw, hDw, hDwp, hDwi, -⟩ := exists_hasWeakFDerivOn_fn U
  have hDw' : HasWeakFDerivOn u Dw (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume :=
    HasWeakIteratedFDerivOn.congr_ae hDw hU (EventuallyEq.refl _ _)
  have hDwg : (fun y ↦ Dw y (single i 1)) =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ))
      (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))] g := by
    have h1 := ((hasWeakIteratedLineDerivOn U (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis :
        Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1))) i)).congr_ae hU (EventuallyEq.refl _ _)
    rw [EuclideanSpace.basisFun_toBasis_apply] at h1
    have h2 := (ae_restrict_iff' (posHalf _ (cylinder d r)).isOpen.measurableSet).2 (h1.ae_eq hg)
    have h3 := hDwi i
    rw [EuclideanSpace.basisFun_toBasis_apply] at h3
    exact h3.trans h2
  have hid := hasWeakFDerivOn_higherReflection ha hl hl1 hDw' hu.memLp hDwp
  have h1 := (hid : HasWeakIteratedFDerivOn 1 _ _ (cylinder d r) volume).lineDeriv
    ![single i (1 : ℝ)]
  refine h1.congr_ae (EventuallyEq.refl _ _) ?_
  -- the pointwise identification of the derivative
  obtain ⟨-, -, -, -, hP⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a 1
  have hneg : ∀ᵐ x ∂volume, x ∈ negHalf (cylinder d r) →
      ∀ j, Dw (scaleLast (l j) x) (single i 1) = g (scaleLast (l j) x) :=
    (ae_restrict_iff' isOpen_negHalf'.measurableSet).1 (hP hDwg)
  have hpos : ∀ᵐ x ∂volume, x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) → Dw x (single i 1) = g x :=
    (ae_restrict_iff' (posHalf _ (cylinder d r)).isOpen.measurableSet).1 hDwg
  filter_upwards [ae_restrict_mem (cylinder d r).isOpen.measurableSet,
    ae_restrict_of_ae ae_apply_last_ne_zero, ae_restrict_of_ae hneg, ae_restrict_of_ae hpos]
    with x hxV hx hx1 hx2
  simp only [continuousMultilinearCurryFin1_symm_apply, Matrix.cons_val_zero]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [higherReflectionFDeriv_of_neg a l h, higherReflection_of_neg _ l h]
    simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply, scaleLast_single]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs with hi
    · rw [map_smul, hx1 ⟨hxV, h⟩ j, Pi.mul_apply, mul_smul]
    · rw [hx1 ⟨hxV, h⟩ j]
  · rw [higherReflectionFDeriv_of_nonneg a l h.le, higherReflection_of_nonneg _ l h.le]
    exact hx2 (mem_posHalf_last_iff.2 ⟨hxV, h⟩)

/-- The Vandermonde conditions one order down for the coefficients `a_j l_j`. -/
theorem vandermonde_mul_of_succ {k : ℕ} (h : ∀ i < k + 1, ∑ j, a j * l j ^ i = 1) :
    ∀ i < k, ∑ j, (a * l) j * l j ^ i = 1 := fun i hi ↦ by
  have := h (i + 1) (by omega)
  rw [← this]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Pi.mul_apply, pow_succ]; ring

/-- **The higher-order reflection preserves `W^{k,p}`** ([brezis2011functional] Comments on
Chapter 9; Lions–Magenes): for scales `l_j ∈ [-1, 0)` and coefficients `a` with the Vandermonde
conditions `∑_j a_j l_j^i = 1` for `i < k`, the reflection `P_a` maps `W^{k,p}(Q_r₊)` into
`W^{k,p}(Q_r)`, `1 ≤ p ≤ ∞`. Induction on `k` through `memSobolevMultiIndex_succ_iff`: the
tangential derivatives of `P_a u` are `P_a (∂ᵢ u)` and the normal one is `P_{al} (∂_N u)`
(`HasWeakIteratedLineDerivOn.higherReflection_single`), and the coefficients `a_j l_j` satisfy
the Vandermonde conditions of order `k − 1` (`vandermonde_mul_of_succ`). -/
theorem MemSobolevMultiIndex.higherReflection_of_order (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    (k : ℕ) : ∀ (a : Fin m → ℝ), (∀ i < k, ∑ j, a j * l j ^ i = 1) →
    ∀ {u : EuclideanSpace ℝ (Fin (d + 1)) → F},
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u k p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (_root_.higherReflection a l u) k p (cylinder d r) volume := by
  induction k with
  | zero =>
    intro a _ u hu
    rw [ExtensionHigher.memSobolevMultiIndex_zero_iff] at hu ⊢
    obtain ⟨C, hC, hCf, -, -⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a p
    exact (hCf u hu.aestronglyMeasurable).2.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC)
      hu)
  | succ k ih =>
    intro a ha u hu
    have ha0 : ∑ j, a j = 1 := by
      have := ha 0 (Nat.succ_pos k)
      simpa using this
    obtain ⟨hu0, hud⟩ := memSobolevMultiIndex_succ_iff.1 hu
    have hu1 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u 1 p
        (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume := hu.mono_order (by omega)
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih a (fun i hi ↦ ha i (by omega)) hu0, fun i ↦ ?_⟩
    obtain ⟨g, hg, hgk⟩ := hud i
    rw [EuclideanSpace.basisFun_toBasis_apply] at hg ⊢
    refine ⟨_root_.higherReflection (if i = Fin.last d then a * l else a) l g,
      hg.higherReflection_single ha0 hl hl1 hu1 i, ?_⟩
    split_ifs with hi
    · exact ih (a * l) (vandermonde_mul_of_succ ha) hgk
    · exact ih a (fun i hi ↦ ha i (by omega)) hgk

/-- **The Vandermonde coefficients**: for the scales `l_j = −1/(j+1)`, `j < k`, there are
coefficients `a_j` with `∑_j a_j l_j^i = 1` for every `i < k`, the Vandermonde matrix of the
distinct nodes `l_j` being invertible. -/
theorem exists_vandermonde_coeffs (k : ℕ) :
    ∃ a : Fin k → ℝ, ∀ i < k, ∑ j, a j * (-((j : ℕ) + 1 : ℝ)⁻¹) ^ i = 1 := by
  obtain ⟨l, hl⟩ : ∃ l : Fin k → ℝ, l = fun j : Fin k ↦ -(((j : ℕ) : ℝ) + 1)⁻¹ := ⟨_, rfl⟩
  have hinj : Function.Injective l := by
    intro j j' h
    rw [hl] at h
    simp only [neg_inj, inv_inj, add_left_inj, Nat.cast_inj] at h
    exact Fin.ext h
  have hdet : (Matrix.vandermonde l).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.2 hinj
  refine ⟨((Matrix.vandermonde l).transpose)⁻¹.mulVec 1, fun i hi ↦ ?_⟩
  have key : (Matrix.vandermonde l).transpose.mulVec (((Matrix.vandermonde l).transpose)⁻¹.mulVec
    1) = 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have := congrFun key ⟨i, hi⟩
  rw [Matrix.mulVec_apply_eq_sum, Pi.one_apply] at this
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans this
  have hlj : l j = -(((j : ℕ) : ℝ) + 1)⁻¹ := by rw [hl]
  rw [Matrix.transpose_apply, Matrix.vandermonde_apply, hlj, mul_comm]

end ReflectionHigher

/-! ### The chart-local extension on the cylinders `Q_r` -/

section RestrictDiffeo

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {H : E' → E} {Hinv : E → E'} {s : Set E'} {t : Set E} {M : ℝ}

/-- A diffeomorphism with bounded Jacobians restricts to every open subset `A` of its source, as
a diffeomorphism of `A` onto `H '' A`. -/
theorem IsDiffeoOnWithBoundedJacobian.restrict (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M)
    {A : Set E'} (hA : IsOpen A) (hAs : A ⊆ s) :
    IsDiffeoOnWithBoundedJacobian H Hinv A (H '' A) M where
  isOpen_source := hA
  isOpen_target := by
    have e : H '' A = t ∩ Hinv ⁻¹' A := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨h.bijOn.mapsTo (hAs hy), by rw [mem_preimage, h.invOn.1 (hAs hy)]; exact hy⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨Hinv x, hx', h.invOn.2 hx⟩
    rw [e]
    exact h.contDiffOn_invFun.continuousOn.isOpen_inter_preimage h.isOpen_target hA
  bijOn := (h.bijOn.injOn.mono hAs).bijOn_image
  invOn := ⟨h.invOn.1.mono hAs, fun x hx ↦ h.invOn.2 (h.bijOn.mapsTo.image_subset (by
    exact (image_mono hAs) hx))⟩
  contDiffOn := h.contDiffOn.mono hAs
  contDiffOn_invFun := h.contDiffOn_invFun.mono (h.bijOn.mapsTo.image_subset.trans' (image_mono
    hAs))
  norm_fderiv_le := fun y hy ↦ h.norm_fderiv_le y (hAs hy)
  norm_fderiv_invFun_le := fun x hx ↦
    h.norm_fderiv_invFun_le x (h.bijOn.mapsTo.image_subset (image_mono hAs hx))

end RestrictDiffeo

section ChartCylinder

variable {d : ℕ} {n : WithTop ℕ∞} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The positive half of `Q_r`, `r < 1`, is `Q_r ∩ Q₊`. -/
theorem coe_posHalf_cylinder_eq_inter {r : ℝ} (hr : r < 1) :
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ unitChartCubePos d := by
  ext x
  rw [mem_posHalf_last_iff, mem_inter_iff, mem_unitChartCubePos]
  exact ⟨fun h ↦ ⟨h.1, cylinder_subset_unitChartCube hr.le h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩

namespace ContDiffChart

variable (c : ContDiffChart n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) {r : ℝ} (hr : r < 1)
include hr

/-- The image of the cylinder `Q_r` under a chart is `U ∩ H⁻¹ ⁻¹' Q_r`. -/
theorem image_cylinder_eq :
    c.toFun '' (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = c.U ∩ c.invFun ⁻¹' (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyQ : y ∈ unitChartCube d := cylinder_subset_unitChartCube hr.le hy
    exact ⟨c.mapsTo hyQ, by rw [mem_preimage, c.invFun_toFun hyQ]; exact hy⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨c.invFun x, hx', c.toFun_invFun hx⟩

/-- **The image `U_r = H(Q_r)` of the cylinder `Q_r` under a chart**, `r < 1`, as an `Opens`:
the open subset of `U` on which the chart-local extension at higher order lives. -/
def opensUr : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨c.toFun '' (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))), by
    rw [c.image_cylinder_eq hr]
    exact (c.contDiffOn_invFun.continuousOn.mono subset_closure).isOpen_inter_preimage c.isOpen_U
      (cylinder d r).isOpen⟩

/-- The underlying set of `c.opensUr hr` is `H(Q_r)`. -/
@[simp]
theorem coe_opensUr : (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))
    = c.toFun '' (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := rfl

/-- `U_r ⊆ U`. -/
theorem opensUr_subset : (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ c.U :=
  fun _ ⟨_, hy, hxy⟩ ↦ hxy ▸ c.mapsTo (cylinder_subset_unitChartCube hr.le hy)

/-- `U_r ∩ Ω` as an `Opens`. -/
def opensInterr : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨(c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ Ω, (c.opensUr hr).isOpen.inter Ω.isOpen⟩

/-- The underlying set of `c.opensInterr hr` is `U_r ∩ Ω`. -/
@[simp]
theorem coe_opensInterr : (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))
    = (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ Ω := rfl

/-- `U_r ∩ Ω ≤ Ω`. -/
theorem opensInterr_le : c.opensInterr hr ≤ Ω := fun _ hx ↦ hx.2

/-- `U_r ∩ Ω ≤ U_r`. -/
theorem opensInterr_le_opensUr : c.opensInterr hr ≤ c.opensUr hr := fun _ hx ↦ hx.1

/-- **The chart maps the positive half of `Q_r` onto `U_r ∩ Ω`**. -/
theorem image_posHalf_cylinder :
    c.toFun '' (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) = c.opensInterr hr := by
  rw [coe_opensInterr, coe_opensUr, coe_posHalf_cylinder_eq_inter hr,
    c.injOn.image_inter (cylinder_subset_unitChartCube hr.le) unitChartCubePos_subset, c.image_pos,
    ← inter_assoc]
  congr 1
  exact inter_eq_left.2 (c.opensUr_subset hr)

/-- A chart restricted to the positive half of `Q_r` is a `C^1` diffeomorphism onto `U_r ∩ Ω`
with bounded Jacobians. -/
theorem exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder (hn : 1 ≤ n) :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) M := by
  obtain ⟨M, hM⟩ := c.isDiffeoOnWithBoundedJacobian_pos hn Ω.isOpen
  have := hM.restrict (posHalf _ (cylinder d r)).isOpen (by
    rw [coe_posHalf_cylinder_eq_inter hr]; exact inter_subset_right)
  rw [c.image_posHalf_cylinder hr] at this
  exact ⟨M, this⟩

/-- A chart restricted to `Q_r` is a `C^1` diffeomorphism onto `U_r` with bounded Jacobians. -/
theorem exists_isDiffeoOnWithBoundedJacobian_cylinder (hn : 1 ≤ n) :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun
      (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) M := by
  obtain ⟨M, hM⟩ := c.isDiffeoOnWithBoundedJacobian hn
  exact ⟨M, hM.restrict (cylinder d r).isOpen (cylinder_subset_unitChartCube hr.le)⟩

/-- The closure of `U_r` lies in the compact `H(closure Q_r)`. -/
theorem closure_opensUr_subset_image_closure :
    closure (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ c.toFun '' closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  have hc : IsCompact (c.toFun '' closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (isCompact_closure_cylinder r).image_of_continuousOn
      (c.continuousOn.mono (closure_mono (cylinder_subset_unitChartCube hr.le)))
  exact closure_minimal (image_mono subset_closure) hc.isClosed

/-- The closure of `U_r`, `r < 1`, lies in `U`. -/
theorem closure_opensUr_subset :
    closure (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ c.U :=
  (c.closure_opensUr_subset_image_closure hr).trans
    ((image_mono (closure_cylinder_subset_unitChartCube hr)).trans c.mapsTo.image_subset)

/-- The closure of `U_r` is compact. -/
theorem isCompact_closure_opensUr :
    IsCompact (closure (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  ((isCompact_closure_cylinder r).image_of_continuousOn
    (c.continuousOn.mono (closure_mono (cylinder_subset_unitChartCube hr.le)))).of_isClosed_subset
    isClosed_closure (c.closure_opensUr_subset_image_closure hr)

omit hr in
/-- A compact subset of `U` lies in some `U_r`, `r < 1`. -/
theorem exists_lt_one_subset_opensUr {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hK : IsCompact K)
    (hKU : K ⊆ c.U) : ∃ r, ∃ hr : r < 1, K ⊆ c.opensUr hr := by
  have hK' : IsCompact (c.invFun '' K) :=
    hK.image_of_continuousOn ((c.contDiffOn_invFun.continuousOn.mono subset_closure).mono hKU)
  obtain ⟨r, hr, hKr⟩ := exists_lt_one_subset_cylinder hK' (image_subset_iff.2 fun x hx ↦
    c.mapsTo_invFun (hKU hx))
  refine ⟨r, hr, fun x hx ↦ ⟨c.invFun x, hKr (mem_image_of_mem _ hx), c.toFun_invFun (hKU hx)⟩⟩

end ContDiffChart

end ChartCylinder

section ChartLocalMem

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {m : ℕ}
  {a l : Fin m → ℝ}

namespace SobolevEuclidean

/-- **The chart-local extension preserves `W^{k,p}`, with the operators as variables**: for a
chart `H` of class `C^k`, the transports preserve `W^{k,p}`
(`MemSobolevMultiIndex.comp_diffeoOn_of_order`) and so does the higher-order reflection under the
Vandermonde conditions of order `k` (`MemSobolevMultiIndex.higherReflection_of_order`). -/
theorem chartExtend_mem_of_ops {r : ℝ} (hr : r < 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    {k : ℕ} {Ωc U : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {H Hinv : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))} {M M' : ℝ}
    (R : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p Ωc)
    (T₁ : SobolevEuclidean (d + 1) 1 p Ωc →L[ℝ] SobolevEuclidean (d + 1) 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)))
    (S : SobolevEuclidean (d + 1) 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) →L[ℝ]
      SobolevEuclidean (d + 1) 1 p (cylinder d r))
    (T₂ : SobolevEuclidean (d + 1) 1 p (cylinder d r) →L[ℝ] SobolevEuclidean (d + 1) 1 p U)
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u)
      =ᵐ[volume.restrict (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u)
    (hT₁fn : ∀ v, SobolevMultiIndex.fn (T₁ v)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fun y ↦ SobolevMultiIndex.fn v (H y))
    (hSfn : ∀ w, SobolevMultiIndex.fn (S w)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        higherReflection a l (SobolevMultiIndex.fn w))
    (hT₂fn : ∀ w, SobolevMultiIndex.fn (T₂ w)
      =ᵐ[volume.restrict (U : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ SobolevMultiIndex.fn w (Hinv x))
    (hT₁ : IsDiffeoOnWithBoundedJacobian H Hinv
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1)))) M)
    (hT₂ : IsDiffeoOnWithBoundedJacobian H Hinv
      (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (U : Set (EuclideanSpace ℝ (Fin (d + 1)))) M')
    (hHk : ContDiffOn ℝ k H (unitChartCube d)) {W : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hW : IsOpen W) (hHinvk : ContDiffOn ℝ k Hinv W)
    (hUW : closure (U : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ W)
    (hUc : IsCompact (closure (U : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hΩc : Ωc ≤ Ω) (hak : ∀ i < k, ∑ j, a j * l j ^ i = 1)
    (u : SobolevEuclidean (d + 1) 1 p Ω)
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn u) k p Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (T₂ (S (T₁ (R u))))) k p U volume := by
  have h1 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (R u)) k p Ωc volume :=
    (hu.mono_set hΩc).congr_ae (hRfn u).symm
  have h2 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (T₁ (R u))) k p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume := by
    refine (MemSobolevMultiIndex.comp_diffeoOn_of_order k hT₁.symm isOpen_unitChartCube hHk
      (isCompact_closure_cylinder r) ?_ (closure_cylinder_subset_unitChartCube hr) h1).congr_ae
      (hT₁fn (R u)).symm
    exact fun x hx ↦ subset_closure (posHalf_le _ _ hx)
  have h3 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (S (T₁ (R u)))) k p (cylinder d r) volume :=
    (MemSobolevMultiIndex.higherReflection_of_order hl hl1 k a hak h2).congr_ae
      (hSfn (T₁ (R u))).symm
  exact (MemSobolevMultiIndex.comp_diffeoOn_of_order k hT₂ hW hHinvk hUc subset_closure hUW
    h3).congr_ae (hT₂fn (S (T₁ (R u)))).symm

end SobolevEuclidean

end ChartLocalMem

section ChartLocalHigher

variable {d : ℕ} {n : WithTop ℕ∞} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {m : ℕ} {a l : Fin m → ℝ}

namespace SobolevEuclidean

variable (p) (c : ContDiffChart n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hn : 1 ≤ n)
  {r : ℝ} (hr : r < 1) (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)

/-- The restriction `W^{1,p}(Ω) → W^{1,p}(U_r ∩ Ω)`. -/
def chartRestrictLr :
    SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (c.opensInterr hr) :=
  SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume
    (c.opensInterr_le hr)

/-- The transfer `u ↦ u ∘ H : W^{1,p}(U_r ∩ Ω) → W^{1,p}(Q_r₊)`. -/
def chartTransferLr : SobolevEuclidean (d + 1) 1 p (c.opensInterr hr) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
    (c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec

/-- The higher-order reflection `W^{1,p}(Q_r₊) → W^{1,p}(Q_r)`. -/
def cubeReflectLr : SobolevEuclidean (d + 1) 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (cylinder d r) :=
  SobolevMultiIndex.higherReflectionL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p ha hl
    hl1

/-- The retransfer `w ↦ w ∘ H⁻¹ : W^{1,p}(Q_r) → W^{1,p}(U_r)`. -/
def chartRetransferLr : SobolevEuclidean (d + 1) 1 p (cylinder d r) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (c.opensUr hr) :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
    (c.exists_isDiffeoOnWithBoundedJacobian_cylinder hr hn).choose_spec.symm

/-- **The chart-local extension at higher order**, `W^{1,p}(Ω) → W^{1,p}(U_r)`: restrict to
`U_r ∩ Ω`, transfer to `Q_r₊` along `H`, reflect to `Q_r` by the higher-order reflection,
transfer back to `U_r` along `H⁻¹`. It agrees with `u` on `U_r ∩ Ω`
(`SobolevEuclidean.chartExtendLr_fn_ae_eq`) and, for a `C^k` chart and coefficients satisfying
the Vandermonde conditions of order `k`, maps the functions of `W^{k,p}(Ω)` into `W^{k,p}(U_r)`
(`SobolevEuclidean.chartExtendLr_mem_of_order`). -/
def chartExtendLr : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (c.opensUr
  hr) :=
  chartRetransferLr p c hn hr ∘L cubeReflectLr p ha hl hl1 ∘L chartTransferLr p c hn hr ∘L
    chartRestrictLr p c hr

/-- `chartExtendLr` is the composite of its four steps. -/
theorem chartExtendLr_apply (u : SobolevEuclidean (d + 1) 1 p Ω) :
    chartExtendLr p c hn hr ha hl hl1 u = chartRetransferLr p c hn hr (cubeReflectLr p ha hl hl1
      (chartTransferLr p c hn hr (chartRestrictLr p c hr u))) :=
  rfl

/-- The function of the restriction. -/
theorem fn_chartRestrictLr (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (chartRestrictLr p c hr u)
      =ᵐ[volume.restrict (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        SobolevMultiIndex.fn u :=
  SobolevMultiIndex.fn_restrictL _ _

/-- The function of the transfer is `u ∘ H`. -/
theorem fn_chartTransferLr (v : SobolevEuclidean (d + 1) 1 p (c.opensInterr hr)) :
    SobolevMultiIndex.fn (chartTransferLr p c hn hr v)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fun y ↦ SobolevMultiIndex.fn v (c.toFun y) :=
  SobolevMultiIndex.fn_compDiffeoL _ _

/-- The function of the reflection is the higher-order reflection of the function. -/
theorem fn_cubeReflectLr (w : SobolevEuclidean (d + 1) 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r))) :
    SobolevMultiIndex.fn (cubeReflectLr p ha hl hl1 w)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        higherReflection a l (SobolevMultiIndex.fn w) :=
  SobolevMultiIndex.fn_higherReflectionL ha hl hl1 w

/-- On `Q_r₊`, the reflected function is the function. -/
theorem fn_cubeReflectLr_restrict (w : SobolevEuclidean (d + 1) 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r))) :
    SobolevMultiIndex.fn (cubeReflectLr p ha hl hl1 w)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn w :=
  SobolevMultiIndex.fn_higherReflectionL_restrict ha hl hl1 w

/-- The function of the retransfer is `w ∘ H⁻¹`. -/
theorem fn_chartRetransferLr (w : SobolevEuclidean (d + 1) 1 p (cylinder d r)) :
    SobolevMultiIndex.fn (chartRetransferLr p c hn hr w)
      =ᵐ[volume.restrict (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ SobolevMultiIndex.fn w (c.invFun x) :=
  SobolevMultiIndex.fn_compDiffeoL _ _

include hn in
/-- Almost everywhere statements on `Q_r₊` pull back along `H⁻¹` to `U_r ∩ Ω`. -/
theorem ae_comp_chart_invFun_cylinder {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop}
    (hP : ∀ᵐ y ∂volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))), P y) :
    ∀ᵐ x ∂volume.restrict (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      P (c.invFun x) :=
  (c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec.symm.ae_comp_restrict
    hP

/-- **The chart-local extension agrees with `u` on `U_r ∩ Ω`**. -/
theorem chartExtendLr_fn_ae_eq (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (chartExtendLr p c hn hr ha hl hl1 u)
      =ᵐ[volume.restrict (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        SobolevMultiIndex.fn u := by
  rw [chartExtendLr_apply]
  exact SobolevEuclidean.chartExtend_fn_of_ops (chartRestrictLr p c hr) (chartTransferLr p c hn hr)
    (cubeReflectLr p ha hl hl1) (chartRetransferLr p c hn hr) (fn_chartRestrictLr p c hr)
    (fn_chartTransferLr p c hn hr) (fn_cubeReflectLr_restrict p ha hl hl1)
    (fn_chartRetransferLr p c hn hr) (fun h ↦ ae_comp_chart_invFun_cylinder c hn hr h)
    (c.opensInterr_le_opensUr hr) (fun x hx ↦ c.toFun_invFun (c.opensUr_subset hr hx.1)) u

/-- **The chart-local extension preserves `W^{k,p}`** for a chart of class `C^k` and coefficients
satisfying the Vandermonde conditions of order `k`. -/
theorem chartExtendLr_mem_of_order {k : ℕ} (hnk : (k : WithTop ℕ∞) ≤ n)
    (hak : ∀ i < k, ∑ j, a j * l j ^ i = 1) (u : SobolevEuclidean (d + 1) 1 p Ω)
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn u) k p Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (chartExtendLr p c hn hr ha hl hl1 u)) k p (c.opensUr hr) volume := by
  rw [chartExtendLr_apply]
  exact chartExtend_mem_of_ops hr hl hl1 (chartRestrictLr p c hr) (chartTransferLr p c hn hr)
    (cubeReflectLr p ha hl hl1) (chartRetransferLr p c hn hr) (fn_chartRestrictLr p c hr)
    (fn_chartTransferLr p c hn hr) (fn_cubeReflectLr p ha hl hl1) (fn_chartRetransferLr p c hn hr)
    (c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec
    (c.exists_isDiffeoOnWithBoundedJacobian_cylinder hr hn).choose_spec
    ((c.contDiffOn.of_le hnk).mono subset_closure) c.isOpen_U
    ((c.contDiffOn_invFun.of_le hnk).mono subset_closure) (c.closure_opensUr_subset hr)
    (c.isCompact_closure_opensUr hr) (c.opensInterr_le hr) hak u hu

end SobolevEuclidean

end ChartLocalHigher

/-! ### The extension operator at every order -/

section AssemblyHigher

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The assembled operator preserves `W^{k,p}`, with the operators as variables**: for
`P u = E₀ u + ∑ E i (C i u)`, where `E₀` and `E i` are the zero extensions of `θ₀ ·` from `Ω` and
of `θ i ·` from `U i`, and each `C i` maps the functions of `W^{k,p}(Ω)` into `W^{k,p}(U i)`, the
function of `P u` lies in `W^{k,p}(ℝ^N)` whenever the function of `u` lies in `W^{k,p}(Ω)`
(the zero extensions at every order,
`ExtensionHigher.memSobolevMultiIndex_indicator_mul_of_hasCompactSupport_sub`). -/
theorem SobolevEuclidean.extension_mem_of_ops {k n : ℕ}
    {U : Fin n → Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {E₀ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
    {E : ∀ i, SobolevEuclidean (d + 1) 1 p (U i) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
    {C : ∀ i, SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (U i)}
    {P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
    {θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {θ : Fin n → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hE₀fn : ∀ u, SobolevMultiIndex.fn (E₀ u) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun x ↦ θ₀ x • SobolevMultiIndex.fn u x)
    (hEfn : ∀ i w, SobolevMultiIndex.fn (E i w) =ᵐ[volume]
      (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun x ↦ θ i x • SobolevMultiIndex.fn w
        x)
    (hP : ∀ u, P u = E₀ u + ∑ i, E i (C i u))
    (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ₀κ : ∃ κ : ℝ, HasCompactSupport fun x ↦ θ₀ x - κ)
    (hθ₀Γ : Disjoint (tsupport θ₀) (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθc : ∀ i, HasCompactSupport (θ i))
    (hθU : ∀ i, tsupport (θ i) ⊆ U i)
    (hC : ∀ i (u : SobolevEuclidean (d + 1) 1 p Ω),
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn (C i u)) k p (U i) volume)
    (u : SobolevEuclidean (d + 1) 1 p Ω)
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn u) k p Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (P u)) k p ⊤ volume := by
  have h0 := ExtensionHigher.memSobolevMultiIndex_indicator_mul_of_hasCompactSupport_sub
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (p := p) (μ := volume) k hθ₀ hθ₀κ
    hθ₀Γ hu
  have hi : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((U i : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun x ↦
        θ i x * SobolevMultiIndex.fn (C i u) x) k p ⊤ volume := fun i ↦ by
    refine ExtensionHigher.memSobolevMultiIndex_indicator_mul_of_hasCompactSupport_sub k (hθ i)
      ⟨0, by simpa using hθc i⟩ ?_ (hC i u hu)
    exact (Set.disjoint_iff_inter_eq_empty.2 (U i).isOpen.inter_frontier_eq).mono_left (hθU i)
  have hsum := ExtensionHigher.memSobolevMultiIndex_add h0
    (ExtensionHigher.memSobolevMultiIndex_finset_sum Finset.univ fun i _ ↦ hi i)
  refine hsum.congr_ae (ae_restrict_of_ae ?_)
  have h1 := SobolevEuclidean.fn_extension_of_ops hP u
  have h2 : ∀ᵐ x ∂volume, ∀ i, SobolevMultiIndex.fn (E i (C i u)) x
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
        (fun x ↦ θ i x • SobolevMultiIndex.fn (C i u) x) x :=
    ae_all_iff.2 fun i ↦ hEfn i (C i u)
  filter_upwards [h1, hE₀fn u, h2] with x hx hx0 hxi
  rw [Pi.add_apply, Finset.sum_apply, hx, Pi.add_apply, Finset.sum_apply, hx0,
    Finset.sum_congr rfl fun i _ ↦ hxi i]
  rfl

/-- The scales `l_j = −1/(j+1)` of the higher-order reflection. -/
theorem neg_inv_succ_lt_zero {k : ℕ} (j : Fin k) : -(((j : ℕ) : ℝ) + 1)⁻¹ < 0 := by
  have : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
  exact neg_neg_of_pos (inv_pos.2 this)

/-- The scales `l_j = −1/(j+1)` lie in `[-1, 0)`. -/
theorem neg_one_le_neg_inv_succ {k : ℕ} (j : Fin k) : -1 ≤ -(((j : ℕ) : ℝ) + 1)⁻¹ := by
  rw [neg_le_neg_iff]
  exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ (j : ℕ))])

/-- **The Vandermonde coefficients and scales, packaged**: scales `l_j ∈ [-1, 0)` and
coefficients `a_j` with `∑ a_j = 1` and `∑_j a_j l_j^i = 1` for every `i < k`. -/
theorem exists_vandermonde_coeffs_scales (k : ℕ) (hk : 1 ≤ k) :
    ∃ a l : Fin k → ℝ, (∀ j, l j < 0) ∧ (∀ j, -1 ≤ l j) ∧ ∑ j, a j = 1 ∧
      ∀ i < k, ∑ j, a j * l j ^ i = 1 := by
  obtain ⟨a, ha⟩ := exists_vandermonde_coeffs k
  refine ⟨a, fun j : Fin k ↦ -(((j : ℕ) : ℝ) + 1)⁻¹, fun j ↦ neg_inv_succ_lt_zero j,
    fun j ↦ neg_one_le_neg_inv_succ j, ?_, ha⟩
  simpa using ha 0 hk

/-- **The assembly with the operators as variables**: for `E₀`, `E i`, `C i` as in
`SobolevEuclidean.fn_extension_ae_eq_of_ops` and `SobolevEuclidean.extension_mem_of_ops`, the
operator `P₁ = E₀ + ∑ E i ∘ C i` is the identity on `Ω` and maps the functions of `W^{k,p}(Ω)`
into `W^{k,p}(ℝ^N)`. -/
theorem SobolevEuclidean.exists_extension_of_ops_higher {k n : ℕ}
    {U Ωc : Fin n → Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩc : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ Ω)
    (E₀ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (E : ∀ i, SobolevEuclidean (d + 1) 1 p (U i) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (C : ∀ i, SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (U i))
    {θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {θ : Fin n → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1)
    (hE₀fn : ∀ u, SobolevMultiIndex.fn (E₀ u) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun x ↦ θ₀ x • SobolevMultiIndex.fn u x)
    (hEfn : ∀ i w, SobolevMultiIndex.fn (E i w) =ᵐ[volume]
      (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun x ↦ θ i x • SobolevMultiIndex.fn w
        x)
    (hCfn : ∀ i u, SobolevMultiIndex.fn (C i u)
      =ᵐ[volume.restrict (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u)
    (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ₀κ : ∃ κ : ℝ, HasCompactSupport fun x ↦ θ₀ x - κ)
    (hθ₀Γ : Disjoint (tsupport θ₀) (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθc : ∀ i, HasCompactSupport (θ i))
    (hθU : ∀ i, tsupport (θ i) ⊆ U i)
    (hC : ∀ i (u : SobolevEuclidean (d + 1) 1 p Ω),
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn (C i u)) k p (U i) volume) :
    ∃ P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤,
      (∀ u, SobolevMultiIndex.fn (P₁ u)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u) ∧
      ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
          (SobolevMultiIndex.fn u) k p Ω volume →
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
          (SobolevMultiIndex.fn (P₁ u)) k p ⊤ volume := by
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤,
      ∀ u, P₁ u = E₀ u + ∑ i, E i (C i u) :=
    ⟨E₀ + ∑ i, (E i).comp (C i), fun u ↦ by
      simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply]⟩
  refine ⟨P₁, fun u ↦ ?_, fun u hu ↦
    SobolevEuclidean.extension_mem_of_ops hE₀fn hEfn hP₁ hθ₀ hθ₀κ hθ₀Γ hθ hθc hθU hC u hu⟩
  refine SobolevEuclidean.fn_extension_ae_eq_of_ops hΩc (α₀ := θ₀) (α := θ) (χ := fun _ ↦ 1)
    (fun x _ ↦ hsum x) (fun i x hx ↦ ?_) hE₀fn hEfn hCfn hP₁ u
    (Eventually.of_forall fun x ↦ (one_mul _).symm)
  exact image_eq_zero_of_notMem_tsupport fun h ↦ hx (hθU i h)

/-- **From an order-one operator preserving `W^{k,p}` to the operator at order `k`**: the closed
graph theorem `SobolevMultiIndex.exists_continuousLinearMap_of_order`, with the identity on `Ω`
carried over. -/
theorem SobolevEuclidean.exists_extensionL_of_order_of_ops {k : ℕ} (hk : 1 ≤ k)
    (P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (hid : ∀ u, SobolevMultiIndex.fn (P₁ u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u)
    (hmem : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn (P₁ u)) k p ⊤ volume) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨Pk, hPk⟩ := SobolevMultiIndex.exists_continuousLinearMap_of_order hk P₁ fun u ↦
    hmem (SobolevMultiIndex.toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p Ω
      volume hk u) (SobolevMultiIndex.memSobolevMultiIndex u)
  refine ⟨Pk, ‖Pk‖, fun u ↦ ⟨?_, Pk.le_opNorm u⟩⟩
  exact Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset (subset_univ _) (hPk u))
    (hid _)

/-- **The order-one operator of the higher-order extension theorem, over an explicit atlas**: for
`C^k` charts `c i` (`k ≥ 1`), a partition of unity `θ₀, θ i` with `supp θ i ⊆ Hᵢ(Q_{rᵢ})`, and
coefficients `a` with the Vandermonde conditions of order `k` for the scales `l`, the operator
`P₁ = E₀ + ∑ E i ∘ C i` (zero extensions of `θ₀ ·` and `θ i ·`, chart-local extensions
`SobolevEuclidean.chartExtendLr`) is the identity on `Ω` and maps the functions of `W^{k,p}(Ω)`
into `W^{k,p}(ℝ^N)`. -/
theorem SobolevEuclidean.exists_extensionL_of_order_of_atlas {k n : ℕ} (hk : 1 ≤ k)
    (c : Fin n → ContDiffChart k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {θ : Fin n → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ₀κ : ∃ κ : ℝ, HasCompactSupport fun x ↦ θ₀ x - κ)
    (hθ₀Γ : Disjoint (tsupport θ₀) (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθc : ∀ i, HasCompactSupport (θ i))
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) {r : Fin n → ℝ} (hr : ∀ i, r i < 1)
    (hθr : ∀ i, tsupport (θ i) ⊆ (c i).opensUr (hr i)) {m : ℕ} {a l : Fin m → ℝ}
    (ha0 : ∑ j, a j = 1) (hl0 : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    (hak : ∀ i < k, ∑ j, a j * l j ^ i = 1) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  have hn : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hα₀ : IsSobolevCutoff Ω θ₀ :=
    ExtensionHigher.isSobolevCutoff_of_hasCompactSupport_sub hθ₀ hθ₀κ.choose_spec hθ₀Γ
  have hα : ∀ i, IsSobolevCutoff ((c i).opensUr (hr i)) (θ i) := fun i ↦
    IsSobolevCutoff.of_hasCompactSupport (hθ i) (hθc i) (hθr i)
  have hex := SobolevEuclidean.exists_extension_of_ops_higher (k := k)
    (U := fun i ↦ (c i).opensUr (hr i)) (Ωc := fun i ↦ (c i).opensInterr (hr i)) (fun i ↦ rfl)
    (SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
      hα₀)
    (fun i ↦ SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      p volume (hα i))
    (fun i ↦ SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1) hsum
    (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
    (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w)
    (fun i u ↦ SobolevEuclidean.chartExtendLr_fn_ae_eq p (c i) hn (hr i) ha0 hl0 hl1 u)
    hθ₀ hθ₀κ hθ₀Γ hθ hθc hθr
    (fun i u hu ↦ SobolevEuclidean.chartExtendLr_mem_of_order p (c i) hn (hr i) ha0 hl0 hl1 le_rfl
      hak u hu)
  obtain ⟨P₁, hid, hmem⟩ := hex
  exact SobolevEuclidean.exists_extensionL_of_order_of_ops hk P₁ hid hmem

/-- **The extension theorem at every order** (Brezis, Comments on Chapter 9; Lions–Magenes;
[han2009theoretical] Theorem 7.3.5 at order `k`): for an open set `Ω ⊆ ℝ^N` of class `C^k`,
`k ≥ 1`, with bounded boundary, and `1 ≤ p ≤ ∞`, there is a bounded linear extension operator
`P : W^{k,p}(Ω) → W^{k,p}(ℝ^N)` with `P u = u` on `Ω` and `‖P u‖ ≤ C ‖u‖`.

The operator is built at order one as in the proof of Theorem 9.7 — the partition of unity
`θ₀, θᵢ` of Lemma 9.3 subordinate to a finite atlas of `C^k` charts, the zero extension of `θ₀ u`,
and for each chart the zero extension of `θᵢ` times the chart-local extension
`SobolevEuclidean.chartExtendLr` on the cylinder `Q_{rᵢ}` containing `Hᵢ⁻¹(supp θᵢ)` — with the
*higher-order reflection* of `MemSobolevMultiIndex.higherReflection_of_order` in place of the
even one, its coefficients solving the Vandermonde system of order `k`
(`exists_vandermonde_coeffs`). This operator maps the functions of `W^{k,p}(Ω)` into
`W^{k,p}(ℝ^N)` (`SobolevEuclidean.extension_mem_of_ops`), and the closed graph theorem
(`SobolevMultiIndex.exists_continuousLinearMap_of_order`) makes its restriction to `W^{k,p}(Ω)`
bounded. At `k = 1` it is a second proof of Theorem 9.7 (`SobolevEuclidean.exists_extensionL`)
without the `L^p` bound. -/
theorem SobolevEuclidean.exists_extensionL_of_order {k : ℕ} (hk : 1 ≤ k)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  -- the atlas and the partition of unity
  obtain ⟨n, c, hc⟩ := hΩ.exists_finite_atlas hΓ
  have hK : IsCompact (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ
  obtain ⟨θ₀, θ, hθ₀, hθ, -, -, hsum, hθc, hθU, hθ₀K⟩ :=
    hK.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hc
  -- the radii `rᵢ < 1` with `supp θᵢ ⊆ Hᵢ(Q_{rᵢ})`
  choose r hr hθr using fun i ↦ (c i).exists_lt_one_subset_opensUr (hθc i) (hθU i)
  -- the scales and the Vandermonde coefficients
  obtain ⟨a, l, hl0, hl1, ha0, hak⟩ := exists_vandermonde_coeffs_scales k hk
  -- `θ₀ − 1 = −∑ θ i` is compactly supported
  have hθ₀κ : HasCompactSupport fun x ↦ θ₀ x - 1 := by
    have e : (fun x ↦ θ₀ x - 1) = -(∑ i, θ i) := by
      funext x
      rw [Pi.neg_apply, Finset.sum_apply]
      linarith [hsum x]
    rw [e]
    exact (HasCompactSupport.finset_sum fun i _ ↦ hθc i).neg
  exact SobolevEuclidean.exists_extensionL_of_order_of_atlas hk c hθ₀ ⟨1, hθ₀κ⟩ hθ₀K hθ hθc hsum
    hr hθr ha0 hl0 hl1 hak

variable (p Ω) in
/-- **`Ω` is a `W^{k,p}`-extension domain**: there is a bounded linear operator
`P : W^{k,p}(Ω) → W^{k,p}(ℝ^N)` with `P u = u` almost everywhere on `Ω`. At `k = 1` this is
`IsSobolevExtensionDomain N p Ω`; the instances are the open sets of class `C^k` with bounded
boundary (`IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain`). -/
def IsSobolevExtensionDomainOfOrder (N k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ P : SobolevEuclidean N k p Ω →L[ℝ] SobolevEuclidean N k p ⊤,
    ∀ u : SobolevEuclidean N k p Ω, SobolevMultiIndex.fn (P u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] SobolevMultiIndex.fn u

/-- **The extension theorem at every order as a domain predicate**: an open set of class `C^k`,
`k ≥ 1`, with bounded boundary is a `W^{k,p}`-extension domain for every `1 ≤ p ≤ ∞`. -/
theorem IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain {k : ℕ} (hk : 1 ≤ k)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsSobolevExtensionDomainOfOrder (d + 1) k p Ω := by
  obtain ⟨P, _, hP⟩ := SobolevEuclidean.exists_extensionL_of_order (p := p) hk hΩ hΓ
  exact ⟨P, fun u ↦ (hP u).1⟩

/-- A `W^{1,p}`-extension domain in the sense of every order is one in the sense of
`IsSobolevExtensionDomain`. -/
theorem IsSobolevExtensionDomainOfOrder.isSobolevExtensionDomain {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (h : IsSobolevExtensionDomainOfOrder N 1 p Ω) :
    IsSobolevExtensionDomain N p Ω := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P.comp (Submodule.subtypeL _), fun u ↦ hP u⟩

end AssemblyHigher

/-! ### Density of `C_c^∞(ℝ^N)` in `W^{k,p}(Ω)` on a `W^{k,p}`-extension domain -/

section DensityHigher

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}

/-- **The norm of `W^{k,p}(Ω)` in the multi-index formulation is bounded by the tensor Sobolev
norm** at every order, up to the constant `∑_α ‖ev_{multiIndexTuple b α}‖`: each `∂^α u` is the
weak derivative tensor of order `|α|` evaluated at the tuple naming `α`
(`SobolevMultiIndex.ofReal_norm_le_sobolevNorm` at order one). -/
theorem SobolevMultiIndex.ofReal_norm_le_sobolevNorm_of_order (hp' : p ≠ ⊤)
    (u : SobolevMultiIndex F b k p Ω μ) :
    ENNReal.ofReal ‖u‖ ≤ (∑ α : MultiIndexLE ι k, ‖ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin (∑ i, α.1 i) ↦ E) F (multiIndexTuple (b : ι → E) α.1)‖ₑ)
      * sobolevNorm (SobolevMultiIndex.fn u) k p Ω μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hf : MemSobolev (SobolevMultiIndex.fn u) k p Ω μ :=
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolev
  have hα : ∀ α : MultiIndexLE ι k, eLpNorm (SobolevMultiIndex.weakDeriv u α) p
      (μ.restrict (Ω : Set E)) ≤ ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α.1 i) ↦ E)
        F (multiIndexTuple (b : ι → E) α.1)‖ₑ * sobolevNorm (SobolevMultiIndex.fn u) k p Ω μ := by
    intro α
    have h1 := SobolevMultiIndex.hasWeakIteratedLineDerivOn u α
    have h2 := (hf.hasWeakIteratedFDerivOn (n := ∑ i, α.1 i) α.2).lineDeriv
      (multiIndexTuple (b : ι → E) α.1)
    have hae : (SobolevMultiIndex.weakDeriv u α : E → F) =ᵐ[μ.restrict (Ω : Set E)]
        fun x ↦ ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α.1 i) ↦ E) F
          (multiIndexTuple (b : ι → E) α.1)
          (weakIteratedFDeriv (∑ i, α.1 i) (SobolevMultiIndex.fn u) Ω μ x) :=
      (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_comp_continuousLinearMap_le _ _ p).trans ?_
    gcongr
    exact eLpNorm_weakIteratedFDeriv_le_sobolevNorm hp hp' α.2
  have hterm : ∀ α : MultiIndexLE ι k, ENNReal.ofReal ‖SobolevMultiIndex.weakDeriv u α‖
      = eLpNorm (SobolevMultiIndex.weakDeriv u α) p (μ.restrict (Ω : Set E)) := fun α ↦ by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  calc ENNReal.ofReal ‖u‖ ≤ ENNReal.ofReal (∑ α, ‖SobolevMultiIndex.weakDeriv u α‖) :=
        ENNReal.ofReal_le_ofReal (SobolevMultiIndex.norm_le_sum_norm_weakDeriv u)
    _ = ∑ α, eLpNorm (SobolevMultiIndex.weakDeriv u α) p (μ.restrict (Ω : Set E)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _]
        exact Finset.sum_congr rfl fun α _ ↦ hterm α
    _ ≤ ∑ α : MultiIndexLE ι k, ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α.1 i) ↦ E) F
          (multiIndexTuple (b : ι → E) α.1)‖ₑ * sobolevNorm (SobolevMultiIndex.fn u) k p Ω μ :=
        Finset.sum_le_sum fun α _ ↦ hα α
    _ = _ := by rw [Finset.sum_mul]

end DensityHigher

section DensityExtensionHigher

variable {N : ℕ} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Density of the restrictions of `C_c^∞(ℝ^N)` functions in `W^{k,p}(Ω)` on a
`W^{k,p}`-extension domain**, `1 ≤ p < ∞` (Brezis's Corollary 9.8 at every order;
[han2009theoretical] Theorem 7.3.2): every `u ∈ W^{k,p}(Ω)` is the limit in `W^{k,p}(Ω)` of
elements whose functions are (the restrictions to `Ω` of) smooth compactly supported functions.
The extension `P u ∈ W^{k,p}(ℝ^N)` is approximated by `C_c^∞(ℝ^N)` functions in the tensor norm
of `W^{k,p}(ℝ^N)` (`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`), which
dominates the multi-index norm (`SobolevMultiIndex.ofReal_norm_le_sobolevNorm_of_order`), and
restriction to `Ω` is `1`-Lipschitz. -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order (hp' : p ≠ ⊤)
    (hΩ : IsSobolevExtensionDomainOfOrder N k p Ω) (u : SobolevEuclidean N k p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin N) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean N k p Ω,
        (∀ n, SobolevMultiIndex.fn (w n)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v n) ∧
        Tendsto w atTop (𝓝 u) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨P, hP⟩ := hΩ
  have hPu : MemSobolev (SobolevMultiIndex.fn (P u)) k p ⊤ volume :=
    (SobolevMultiIndex.memSobolevMultiIndex (P u)).memSobolev
  obtain ⟨v, hvs, hvc, hvt⟩ := hPu.exists_seq_hasCompactSupport_tendsto_sobolevNorm hp hp'
  choose V hV using fun n ↦ (hvs n).exists_sobolevMultiIndex_of_hasCompactSupport
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := k) (p := p)
    (Ω := (⊤ : Opens (EuclideanSpace ℝ (Fin N)))) (μ := volume) (hvc n)
  obtain ⟨R, hR⟩ : ∃ R : SobolevEuclidean N k p ⊤ →L[ℝ] SobolevEuclidean N k p Ω,
      R = SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k p volume
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
  · have hRPu : R (P u) = u := SobolevMultiIndex.ext_of_fn_ae_eq ((hRfn _).trans (hP u))
    rw [← hRPu, tendsto_iff_norm_sub_tendsto_zero]
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ≥0∞, C = ∑ α : MultiIndexLE (Fin N) k,
      ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α.1 i) ↦ EuclideanSpace ℝ (Fin N)) ℝ
        (multiIndexTuple ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
          Fin N → EuclideanSpace ℝ (Fin N)) α.1)‖ₑ := ⟨_, rfl⟩
    have hC : C ≠ ⊤ := by
      rw [hCdef]
      exact ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top
    have hsub : ∀ n, sobolevNorm (SobolevMultiIndex.fn (V n - P u)) k p ⊤ volume
        = sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume := fun n ↦
      sobolevNorm_congr_ae ((SobolevMultiIndex.fn_sub _ _).trans
        ((hV n).sub (Filter.EventuallyEq.refl _ _)))
    have hfin : ∀ᶠ n in atTop,
        sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume ≠ ⊤ := by
      filter_upwards [ENNReal.tendsto_nhds_zero.1 hvt 1 one_pos] with n hn
      exact (hn.trans_lt ENNReal.one_lt_top).ne
    have hbound : ∀ n, sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume ≠ ⊤ →
        ‖R (V n) - R (P u)‖
          ≤ (C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume).toReal := by
      intro n hn
      rw [← map_sub]
      refine (hRle _).trans ?_
      have h := SobolevMultiIndex.ofReal_norm_le_sobolevNorm_of_order hp' (V n - P u)
      rw [hsub n, ← hCdef] at h
      exact (ENNReal.toReal_ofReal (norm_nonneg _)).symm.le.trans
        (ENNReal.toReal_mono (ENNReal.mul_ne_top hC hn) h)
    refine squeeze_zero' (g := fun n ↦
      (C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume).toReal)
      (Eventually.of_forall fun _ ↦ norm_nonneg _) (hfin.mono hbound) ?_
    have h1 : Tendsto (fun n ↦ C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hvt (Or.inr hC)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using this

/-- **Density of `C^∞(closure Ω)` in `W^{k,p}(Ω)` on a `C^k` domain with bounded boundary**,
`k ≥ 1`, `1 ≤ p < ∞` (Brezis's Corollary 9.8 at every order; [han2009theoretical]
Theorem 7.3.2): the restrictions of `C_c^∞(ℝ^N)` functions are dense in `W^{k,p}(Ω)`. -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_isContDiffChartDomain
    {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hp' : p ≠ ⊤) (hk : 1 ≤ k)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u : SobolevEuclidean (d + 1) k p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean (d + 1) k p Ω,
        (∀ n, SobolevMultiIndex.fn (w n)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order hp'
    (IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain hk hΩ hΓ) u

end DensityExtensionHigher

/-! ### Lowering the order at every level: `W^{m+1+j,p}(Ω) → W^{j+1,r}(Ω)` -/

section ClosedGraphGeneral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {k k' : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Ω Ω' : Opens E}
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

/-- **A bounded linear map into `L^q(Ω')` whose values lie in `W^{k',q}(Ω')` lifts to a bounded
linear map into `W^{k',q}(Ω')`**: the lift is defined through
`MemSobolevMultiIndex.exists_sobolevMultiIndex`, is linear by the uniqueness of the weak
derivatives, and is continuous by the closed graph theorem
(`SobolevMultiIndex.continuous_of_fnL_comp_eq`). -/
theorem SobolevMultiIndex.exists_continuousLinearMap_of_forall_memSobolevMultiIndex
    (G : SobolevMultiIndex F b k p Ω μ →L[ℝ] Lp F q (μ.restrict (Ω' : Set E)))
    (hG : ∀ u, MemSobolevMultiIndex b (G u) k' q Ω' μ) :
    ∃ T : SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k' q Ω' μ,
      ∀ u, fnL F b k' q Ω' μ (T u) = G u := by
  choose T' hT' using fun u ↦ (hG u).exists_sobolevMultiIndex
  have hfn : ∀ u, fnL F b k' q Ω' μ (T' u) = G u := fun u ↦ by
    apply Lp.ext
    rw [fnL_apply]
    exact hT' u
  have hadd : ∀ u v, T' (u + v) = T' u + T' v := fun u v ↦
    fnL_injective (by rw [map_add, hfn, hfn, hfn, map_add])
  have hsmul : ∀ (c : ℝ) u, T' (c • u) = c • T' u := fun c u ↦
    fnL_injective (by rw [map_smul, hfn, hfn, map_smul])
  obtain ⟨Tₗ, hTₗ⟩ : ∃ Tₗ : SobolevMultiIndex F b k p Ω μ →ₗ[ℝ] SobolevMultiIndex F b k' q Ω' μ,
      ∀ u, Tₗ u = T' u := ⟨{ toFun := T', map_add' := hadd, map_smul' := hsmul }, fun _ ↦ rfl⟩
  have hT : ∀ u, fnL F b k' q Ω' μ (Tₗ u) = G u := fun u ↦ by rw [hTₗ]; exact hfn u
  have hcont : Continuous Tₗ := continuous_of_fnL_comp_eq Tₗ G.continuous hT
  exact ⟨⟨Tₗ, hcont⟩, fun u ↦ hT u⟩

end ClosedGraphGeneral

section LowerOrder

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **Membership in `W^{j+1,r}(Ω)` from `W^{m+1+j,p}(Ω)`**, given the order-one inclusion
`W^{m+1,p}(Ω) ⊆ W^{1,r}(Ω)` on functions: induction on `j` through
`memSobolevMultiIndex_succ_iff`, each partial derivative of `f ∈ W^{m+1+(j+1),p}` lying in
`W^{m+1+j,p}`. -/
theorem MemSobolevMultiIndex.of_forall_mem_one (m : ℕ) {p r : ℝ≥0∞}
    (h1 : ∀ f : EuclideanSpace ℝ (Fin N) → ℝ,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f (m + 1) p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f 1 r Ω volume)
    (j : ℕ) : ∀ f : EuclideanSpace ℝ (Fin N) → ℝ,
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f (m + 1 + j) p Ω volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f (j + 1) r Ω volume := by
  induction j with
  | zero => exact fun f hf ↦ h1 f hf
  | succ j ih =>
    intro f hf
    obtain ⟨hf0, hfd⟩ := memSobolevMultiIndex_succ_iff.1 hf
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih f hf0, fun i ↦ ?_⟩
    obtain ⟨g, hg, hgm⟩ := hfd i
    exact ⟨g, hg, ih g hgm⟩

/-- **The inclusion `W^{k,p}(Ω) ⊆ W^{j+1,r}(Ω)` of an extension domain as a bounded linear map**,
for `k = m + 1 + j`, `1 ≤ p ≤ r < ∞` with `1/p − m/N ≤ 1/r` (and `N ≥ 2` or `p > 1`): the
order-one inclusion `W^{m+1,p}(Ω) → W^{1,r}(Ω)` of Corollary 9.15
(`SobolevEuclidean.exists_continuousLinearMap_orderOne`) applied to the derivatives of order
`≤ j`, with the bound from the closed graph theorem
(`SobolevMultiIndex.exists_continuousLinearMap_of_forall_memSobolevMultiIndex`). This is the
device by which the embeddings of `W^{k,p}(Ω)` into the Hölder spaces `C^{j,β}` are read off
those of `W^{j+1,r}(Ω)` for every large `r`, the integer case of the Sobolev embedding
theorem. -/
theorem SobolevEuclidean.exists_continuousLinearMap_lower_of_order (m j : ℕ) {p r : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (r : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hpr : p ≤ r) (hr : (p : ℝ)⁻¹ - m / N ≤ (r : ℝ)⁻¹) :
    ∃ T : SobolevEuclidean N (m + 1 + j) p Ω →L[ℝ] SobolevEuclidean N (j + 1) r Ω,
      ∀ u, fn (T u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u := by
  obtain ⟨T₁, hT₁⟩ := SobolevEuclidean.exists_continuousLinearMap_orderOne m hΩ hN hpr hr
  have h1 : ∀ f : EuclideanSpace ℝ (Fin N) → ℝ,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f (m + 1) p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f 1 r Ω volume := by
    intro f hf
    obtain ⟨v, hv⟩ := hf.exists_sobolevMultiIndex
    exact (memSobolevMultiIndex (T₁ v)).congr_ae ((hT₁ v).trans hv)
  have hmem := MemSobolevMultiIndex.of_forall_mem_one m h1 j
  obtain ⟨G, hG⟩ : ∃ G : SobolevEuclidean N (m + 1 + j) p Ω →L[ℝ]
      Lp ℝ r (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ u, (G u : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u :=
    ⟨(fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 r Ω volume).comp (T₁.comp
      (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume
        (Nat.le_add_right (m + 1) j))), fun u ↦ by
      simp only [ContinuousLinearMap.comp_apply, fnL_apply]
      exact hT₁ _⟩
  obtain ⟨T, hT⟩ := SobolevMultiIndex.exists_continuousLinearMap_of_forall_memSobolevMultiIndex G
    fun u ↦ (hmem (fn u) (memSobolevMultiIndex u)).congr_ae (hG u).symm
  refine ⟨T, fun u ↦ ?_⟩
  have := congrArg (fun w : Lp ℝ r (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦
    (w : EuclideanSpace ℝ (Fin N) → ℝ)) (hT u)
  rw [fnL_apply] at this
  exact (Filter.EventuallyEq.of_eq this).trans (hG u)

end LowerOrder

/-! ### Rellich–Kondrachov at `p = ∞`: `W^{1,∞}(Ω) ⊂⊂ L^∞(Ω)` by Arzelà–Ascoli

The material of this section belongs beside the Rellich–Kondrachov theorem of
`Numlib/Analysis/Sobolev/Compactness.lean` and its iteration in
`Numlib/Analysis/Sobolev/DenyLions.lean`, which cover `1 ≤ p < ∞`; it is written here (the
closing round) beside the higher-order extension, and is to be relocated. -/

section RellichTop

open SobolevMultiIndex

/-- **The almost-everywhere bound from the `L^∞` norm**: if `‖f‖_{L^∞(μ)} ≤ L` then `‖f x‖ ≤ L`
almost everywhere. -/
theorem ExtensionHigher.ae_norm_le_of_eLpNorm_top_le {α G : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup G] {f : α → G} (hf : AEStronglyMeasurable f μ) {L : ℝ}
    (hL : 0 ≤ L) (h : eLpNorm f ⊤ μ ≤ ENNReal.ofReal L) : ∀ᵐ x ∂μ, ‖f x‖ ≤ L := by
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [← eLpNorm_exponent_top hf] at hx
  rw [← ENNReal.ofReal_le_ofReal_iff hL, ofReal_norm]
  exact hx.trans h

/-- **An element of `L^∞` is bounded almost everywhere by its norm.** -/
theorem ExtensionHigher.ae_norm_le_norm_top {α G : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup G] (f : Lp G ⊤ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ :=
  ExtensionHigher.ae_norm_le_of_eLpNorm_top_le (Lp.aestronglyMeasurable f) (norm_nonneg f)
    (by rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)])

/-- **The `L^∞` distance from a uniform bound on representatives**: if `g₁ = v₁` and `g₂ = v₂`
almost everywhere and `‖v₁ x − v₂ x‖ ≤ D` almost everywhere, then `dist g₁ g₂ ≤ D` in `L^∞`. -/
theorem ExtensionHigher.dist_le_of_ae_eq_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
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
theorem ExtensionHigher.exists_strictMono_forall_dist_lt_of_lipschitzWith {E : Type*}
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
    refine ExtensionHigher.ae_norm_le_of_eLpNorm_top_le hwp.aestronglyMeasurable (by positivity)
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
      ExtensionHigher.ae_norm_le_norm_top
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
(`ExtensionHigher.exists_strictMono_forall_dist_lt_of_lipschitzWith`), which is Cauchy in
`L^∞(Ω)` (`ExtensionHigher.dist_le_of_ae_eq_top`), hence convergent. This is the case `p = ∞`
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
  obtain ⟨φ, hφ, hφc⟩ := ExtensionHigher.exists_strictMono_forall_dist_lt_of_lipschitzWith
    hb.isCompact_closure v hvl hvb
  -- the subsequence is Cauchy in `L^∞(Ω)`
  have hcauchy : CauchySeq fun n ↦
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 ⊤ Ω volume (u (φ n)) := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨n₀, hn₀⟩ := hφc (ε / 2) (by positivity)
    refine ⟨n₀, fun m hm n hn ↦ ?_⟩
    refine (ExtensionHigher.dist_le_of_ae_eq_top _ _ (hv (φ m)) (hv (φ n)) (D := ε / 2)
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
