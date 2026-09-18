/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.MetricSpace.Holder
import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Sobolev.Interval.Extension
import Numlib.Topology.ContinuousMap.ArzelaAscoli

/-!
# The Sobolev embeddings in one dimension

The embedding `W^{1,p}(I) ⊆ L^∞(I)` and its consequences, [brezis2011functional] Theorem 8.8
(5)–(6) and Corollaries 8.9–8.11 with Remarks 11–12, for every exponent `1 ≤ p ≤ ∞` and every
open interval `I ⊆ ℝ`.

## Main statements

* `SobolevIntervalLp.abs_rep_le_of_bounded` (Theorem 8.8 (5), bounded interval, with the
  constant): `|ũ(x)| ≤ |I|^{-1/p} ‖u‖_p + |I|^{1 - 1/p} ‖u'‖_p` on `Ī`;
  `SobolevIntervalLp.abs_rep_le_of_unbounded`: `|ũ(x)| ≤ ‖u‖_p + ‖u'‖_p` on an unbounded
  interval; `SobolevIntervalLp.abs_rep_le`, `eLpNorm_top_le`, `memLp_top`: **`W^{1,p}(I) ⊆ L^∞(I)`
  with continuous injection**, `‖u‖_∞ ≤ C ‖u‖_{W^{1,p}}` with the constant
  `SobolevIntervalLp.embeddingConst p I` depending only on `|I| ≤ ∞`.
* `SobolevIntervalLp.abs_rep_sub_rep_le`: the Hölder estimate
  `|ũ(x) - ũ(y)| ≤ ‖u'‖_p |x - y|^{1 - 1/p}`.
* `SobolevIntervalLp.toContinuousMap`: the embedding `W^{1,p}(a, b) ↪ C[a, b]` as a continuous
  linear map, with `SobolevIntervalLp.isCompactOperator_toContinuousMap` (Theorem 8.8 (6)): it is
  **compact for `1 < p ≤ ∞`**, by Arzelà–Ascoli on the uniformly Hölder unit ball.
* `SobolevIntervalLp.toLp` (Remark 12): the inclusions `W^{1,p}(I) ⊆ L^q(I)` for `p ≤ q ≤ ∞`, and
  `toLpOfBounded` for every `q` on a bounded interval; `SobolevIntervalLp.norm_equiv_of_bounded`
  (Remark 11): on a bounded interval `‖u'‖_p + ‖u‖_q` is a norm equivalent to the `W^{1,p}` norm,
  from the window estimate with an `L^q` function part (`enorm_rep_le_of_Icc_subset'`).
* `SobolevIntervalLp.tendsto_rep_cocompact` (Corollary 8.9): `ũ(x) → 0` as `|x| → ∞` on an
  unbounded interval, `1 ≤ p < ∞`.
* `SobolevIntervalLp.hasWeakDerivOn_rep_mul`, `memSobolevIntervalLp_mul`, `mul` and
  `integral_deriv_mul_add_mul_deriv` (Corollary 8.10): the product rule `(uv)' = u'v + uv'` in
  `W^{1,p}(I)` and integration by parts.
* `SobolevIntervalLp.hasWeakDerivOn_comp`, `memSobolevIntervalLp_comp` (Corollary 8.11): the
  chain rule `(G ∘ u)' = (G' ∘ u) u'` for `G ∈ C¹` with `G(0) = 0`.
* `SobolevIntervalLp.exists_subseq_tendsto_of_bounded_one` (Remark 10, Exercise 8.3): **Helly's
  selection theorem**, a bounded sequence of `W^{1,1}(a, b)` has a subsequence whose
  representatives converge at every point of `[a, b]`, from the selection theorem for monotone
  functions `exists_subseq_forall_tendsto_of_forall_monotoneOn`.

## Route: the representative, not density

The book proves (5) on `ℝ` for `C_c^1` functions and extends by density (its Theorem 8.7) and the
extension operator. Here everything is proved directly from the continuous representative
`SobolevIntervalLp.rep` of `Numlib/Analysis/Sobolev/Interval/Basic.lean`: on an interval `[c, d]`
of the closure of `I`, `|ũ(x)| ≤ |ũ(y)| + |∫_y^x u'|` for every `y`, averaged over `y ∈ (c, d)`
and combined with Hölder's inequality twice, gives
`|ũ(x)| ≤ (d - c)^{-1/p} ‖u‖_{L^p(c, d)} + (d - c)^{1 - 1/p} ‖u'‖_{L^p(c, d)}`
(`SobolevIntervalLp.enorm_rep_le_of_Icc_subset`); a bounded interval is one such window, and an
unbounded interval contains a window of length one around each of its points, which gives the
book's (5) with a constant depending only on `|I|`, and Corollary 8.9 by letting the window run
off to infinity. The product and chain rules are the calculus of absolutely continuous functions
(`SobolevIntervalLp.integral_deriv_mul_rep_add_mul_deriv` of `Interval/Extension`) followed by
Lemma 8.2, exactly as `Numlib/Analysis/Sobolev/Interval.lean` does at `p = 2`. The book's
inequality (8), `|ũ(x)|^p ≤ p ‖u‖_p^{p-1} ‖u'‖_p`, is not needed on this route; it is proved
separately (`SobolevIntervalLp.abs_rep_pow_le`) by the same absolutely-continuous calculus
applied to `|ũ|^p`, with Hölder's inequality and Corollary 8.9.

Compactness is stated with Mathlib's `IsCompactOperator` on the bundled embedding; the relation
`IsCompactEmbedding` of `Numlib/Analysis/Normed/Operator/Embedding.lean` is recovered through
`isCompactEmbedding_iff_isCompactOperator` (`SobolevIntervalLp.isCompactEmbedding_toContinuousMap`).
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Interval Topology

noncomputable section

/-! ### Hölder's inequality for set and interval integrals -/

section Holder

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The real exponent `1 - 1/p` of the Hölder conjugate of `p`, read from `ℝ≥0∞`: for `p = ∞` it
is `1`, in agreement with `p.toReal⁻¹ = 0`. -/
theorem ENNReal.toReal_one_sub_inv (hp : 1 ≤ p) : (1 - p⁻¹).toReal = 1 - p.toReal⁻¹ := by
  rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.2 hp) ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_inv]

omit [Fact (1 ≤ p)] in
/-- The exponent `1 - 1/p` is nonnegative for `1 ≤ p ≤ ∞`. -/
theorem one_sub_toReal_inv_nonneg (hp : 1 ≤ p) : 0 ≤ 1 - p.toReal⁻¹ := by
  rw [sub_nonneg]
  rcases eq_or_ne p ⊤ with rfl | hp'
  · simp
  · exact inv_le_one_of_one_le₀ (by
      have := ENNReal.toReal_mono hp' hp
      rwa [ENNReal.toReal_one] at this)

/-- **Hölder's inequality for the integral of `‖f‖` over a set**, in `ℝ≥0∞` and without any
hypothesis on `f`: `∫_s ‖f‖ ≤ μ(s)^{1 - 1/p} ‖f‖_{L^p(μ)}` for every `1 ≤ p ≤ ∞`. -/
theorem MeasureTheory.setLIntegral_enorm_le_rpow_mul_eLpNorm {μ : Measure ℝ} (f : ℝ → ℝ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ x in s, ‖f x‖ₑ ∂μ ≤ μ s ^ (1 - p.toReal⁻¹) * eLpNorm f p μ := by
  have hpq : ENNReal.HolderConjugate p (1 - p⁻¹)⁻¹ := ENNReal.holderConjugate_sub_inv_inv
  have hqp : ENNReal.HolderConjugate (1 - p⁻¹)⁻¹ p := ENNReal.HolderConjugate.symm
  have e : ∫⁻ x in s, ‖f x‖ₑ ∂μ = ∫⁻ x, ‖s.indicator (fun _ ↦ (1 : ℝ)) x • f x‖ₑ ∂μ := by
    rw [← lintegral_indicator hs]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, indicator_of_mem hx, one_smul]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_smul, enorm_zero]
  have hexp : 1 / ((1 - p⁻¹)⁻¹).toReal = 1 - p.toReal⁻¹ := by
    rw [ENNReal.toReal_inv, one_div, inv_inv, ENNReal.toReal_one_sub_inv Fact.out]
  calc ∫⁻ x in s, ‖f x‖ₑ ∂μ
      = ∫⁻ x, ‖s.indicator (fun _ ↦ (1 : ℝ)) x • f x‖ₑ ∂μ := e
    _ ≤ eLpNorm (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) x • f x) 1 μ :=
        lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm (s.indicator fun _ ↦ (1 : ℝ)) (1 - p⁻¹)⁻¹ μ * eLpNorm f p μ :=
        eLpNorm_smul_le_mul_eLpNorm_of_pos (φ := s.indicator fun _ ↦ (1 : ℝ)) (f := f) one_pos
    _ ≤ ‖(1 : ℝ)‖ₑ * μ s ^ (1 / ((1 - p⁻¹)⁻¹).toReal) * eLpNorm f p μ := by
        gcongr
        exact eLpNorm_indicator_const_le _ _ hs.nullMeasurableSet
    _ = μ s ^ (1 - p.toReal⁻¹) * eLpNorm f p μ := by
        rw [enorm_one, one_mul, hexp]

/-- **Hölder's inequality for an interval integral**, in `ℝ≥0∞` and without any hypothesis on
`f`: `‖∫_x^y f‖ ≤ |y - x|^{1 - 1/p} ‖f‖_{L^p(Ι x y)}`. -/
theorem MeasureTheory.enorm_intervalIntegral_le_rpow_mul_eLpNorm (f : ℝ → ℝ) (x y : ℝ) :
    ‖∫ t in x..y, f t‖ₑ ≤ ENNReal.ofReal |y - x| ^ (1 - p.toReal⁻¹)
      * eLpNorm f p (volume.restrict (Ι x y)) := by
  rw [← ofReal_norm, intervalIntegral.norm_integral_eq_norm_integral_uIoc, ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have := setLIntegral_enorm_le_rpow_mul_eLpNorm (p := p) (μ := volume.restrict (Ι x y)) f
    MeasurableSet.univ
  rw [Measure.restrict_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_uIoc] at this
  exact this

/-- `L^p` norms over a subinterval of the closure of an open interval only see the interval. -/
theorem MeasureTheory.eLpNorm_restrict_eq_of_subset_closure {I : Opens ℝ}
    (hI : (I : Set ℝ).OrdConnected) {s : Set ℝ} (hs : s ⊆ closure (I : Set ℝ)) (f : ℝ → ℝ)
    (q : ℝ≥0∞) : eLpNorm f q (volume.restrict s) = eLpNorm f q (volume.restrict (s ∩ I)) := by
  congr 1
  refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null (fun t ht ↦ ?_) (I.volume_closure_diff_eq_zero hI)
    exact ⟨hs ht.1, fun h ↦ ht.2 ⟨ht.1, h⟩⟩
  · rw [sdiff_eq_empty.2 inter_subset_left, measure_empty]

/-- `L^p` norms over a subset of the closure of an open interval are dominated by the `L^p(I)`
norm. -/
theorem MeasureTheory.eLpNorm_restrict_le_of_subset_closure {I : Opens ℝ}
    (hI : (I : Set ℝ).OrdConnected) {s : Set ℝ} (hs : s ⊆ closure (I : Set ℝ)) (f : ℝ → ℝ)
    (q : ℝ≥0∞) : eLpNorm f q (volume.restrict s) ≤ eLpNorm f q (volume.restrict I) := by
  rw [eLpNorm_restrict_eq_of_subset_closure hI hs]
  exact eLpNorm_mono_measure _ (Measure.restrict_mono inter_subset_right le_rfl)

end Holder

/-! ### Theorem 8.8 (5): `W^{1,p}(I) ⊆ L^∞(I)` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ}

/-- **The averaging argument of Theorem 8.8 (5)**, for a function `g` on `[c, d]` with
`g y - g x = ∫_x^y w`: from `|g x| ≤ |g y| + |∫_y^x w| ≤ |g y| + K` for every `y ∈ [c, d]`,
integrating over `y ∈ (c, d)`, `|g x| ≤ (d - c)⁻¹ ∫_c^d |g| + K`. Stated in `ℝ≥0∞`, where no
integrability is needed. -/
theorem enorm_le_of_forall_sub_eq_integral {c d : ℝ} (hcd : c < d) {g w : ℝ → ℝ}
    (hgw : ∀ x ∈ Icc c d, ∀ y ∈ Icc c d, g y - g x = ∫ t in x..y, w t) {K : ℝ≥0∞}
    (hK : ∀ x ∈ Icc c d, ∀ y ∈ Icc c d, ‖∫ t in x..y, w t‖ₑ ≤ K) {x : ℝ} (hx : x ∈ Icc c d) :
    ‖g x‖ₑ ≤ (ENNReal.ofReal (d - c))⁻¹ * (∫⁻ y in Ioo c d, ‖g y‖ₑ) + K := by
  set L := ENNReal.ofReal (d - c) with hL
  have hL0 : L ≠ 0 := by rw [hL]; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hcd)).ne'
  have hLtop : L ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : ∀ y ∈ Icc c d, ‖g x‖ₑ ≤ ‖g y‖ₑ + K := fun y hy ↦ by
    have e : g x = g y + (g x - g y) := by ring
    calc ‖g x‖ₑ = ‖g y + (g x - g y)‖ₑ := by rw [← e]
      _ ≤ ‖g y‖ₑ + ‖g x - g y‖ₑ := enorm_add_le _ _
      _ ≤ ‖g y‖ₑ + K := by
        gcongr
        rw [hgw y hy x hx]
        exact hK y hy x hx
  have hint : ‖g x‖ₑ * L ≤ (∫⁻ y in Ioo c d, ‖g y‖ₑ) + K * L := by
    have h1 : ∫⁻ _ in Ioo c d, ‖g x‖ₑ = ‖g x‖ₑ * L := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
    have h2 : ∫⁻ _ in Ioo c d, K = K * L := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
    rw [← h1, ← h2, ← lintegral_add_right _ measurable_const]
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun y hy ↦ ?_))
    exact hpt y (Ioo_subset_Icc_self hy)
  rw [← ENNReal.le_div_iff_mul_le (Or.inl hL0) (Or.inl hLtop)] at hint
  refine hint.trans (le_of_eq ?_)
  rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hL0 hLtop, ENNReal.div_eq_inv_mul]

variable [Fact (1 ≤ p)]

/-- **The window estimate, with an `L^q` norm of the function**: for `u ∈ W^{1,p}(I)`, a compact
interval `[c, d]` inside the closure of `I` and every `1 ≤ q ≤ ∞`,
`|ũ(x)| ≤ (d - c)^{-1/q} ‖u‖_{L^q(c, d)} + (d - c)^{1 - 1/p} ‖u'‖_{L^p(c, d)}` for every
`x ∈ [c, d]`, in `ℝ≥0∞`: the averaging argument of Theorem 8.8 (5) with Hölder's inequality
`‖ũ‖_{L^1(c, d)} ≤ (d - c)^{1 - 1/q} ‖ũ‖_{L^q(c, d)}` for the mean (Remark 11 of
[brezis2011functional], Chapter 8). -/
theorem enorm_rep_le_of_Icc_subset' (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] {c d : ℝ} (hcd : c < d) (hsub : Icc c d ⊆ closure (I : Set ℝ))
    {x : ℝ} (hx : x ∈ Icc c d) :
    ‖rep u x‖ₑ ≤ ENNReal.ofReal (d - c) ^ (-q.toReal⁻¹)
        * eLpNorm (fn u) q (volume.restrict (Ioo c d))
      + ENNReal.ofReal (d - c) ^ (1 - p.toReal⁻¹)
        * eLpNorm (deriv u 1) p (volume.restrict (Ioo c d)) := by
  set L := ENNReal.ofReal (d - c) with hL
  have hL0 : L ≠ 0 := by rw [hL]; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hcd)).ne'
  have hLtop : L ≠ ⊤ := ENNReal.ofReal_ne_top
  have hIcc : volume.restrict (Icc c d) = volume.restrict (Ioo c d) :=
    (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm
  -- the bound on the increments of `ũ`
  have hK : ∀ x ∈ Icc c d, ∀ y ∈ Icc c d, ‖∫ t in x..y, deriv u 1 t‖ₑ
      ≤ L ^ (1 - p.toReal⁻¹) * eLpNorm (deriv u 1) p (volume.restrict (Ioo c d)) := by
    intro x hx y hy
    refine (enorm_intervalIntegral_le_rpow_mul_eLpNorm (p := p) _ x y).trans ?_
    have hsub' : Ι x y ⊆ Icc c d := uIoc_subset_uIcc.trans (uIcc_subset_Icc hx hy)
    have hL1 : ENNReal.ofReal |y - x| ≤ L := ENNReal.ofReal_le_ofReal (by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
    have hL2 : eLpNorm (deriv u 1) p (volume.restrict (Ι x y))
        ≤ eLpNorm (deriv u 1) p (volume.restrict (Ioo c d)) := by
      rw [← hIcc]
      exact eLpNorm_mono_measure _ (Measure.restrict_mono hsub' le_rfl)
    exact mul_le_mul' (ENNReal.rpow_le_rpow hL1 (one_sub_toReal_inv_nonneg Fact.out)) hL2
  have hgw : ∀ x ∈ Icc c d, ∀ y ∈ Icc c d, rep u y - rep u x = ∫ t in x..y, deriv u 1 t :=
    fun x hx y hy ↦ rep_sub_rep hI u (hsub hx) (hsub hy)
  refine (enorm_le_of_forall_sub_eq_integral hcd hgw hK hx).trans ?_
  -- Hölder for the average of `|ũ|`
  have hae : fn u =ᵐ[volume.restrict (Ioo c d ∩ I)] rep u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right (fn_ae_eq_rep hI u)
  have h1 : (∫⁻ y in Ioo c d, ‖rep u y‖ₑ)
      ≤ L ^ (1 - q.toReal⁻¹) * eLpNorm (fn u) q (volume.restrict (Ioo c d)) := by
    have := setLIntegral_enorm_le_rpow_mul_eLpNorm (p := q) (μ := volume.restrict (Ioo c d))
      (rep u) MeasurableSet.univ
    rw [Measure.restrict_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioo, eLpNorm_restrict_eq_of_subset_closure hI
      (Ioo_subset_Icc_self.trans hsub), ← eLpNorm_congr_ae hae,
      ← eLpNorm_restrict_eq_of_subset_closure hI (Ioo_subset_Icc_self.trans hsub)] at this
    exact this
  have h2 : L⁻¹ * L ^ (1 - q.toReal⁻¹) = L ^ (-q.toReal⁻¹) := by
    rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hL0 hLtop]
    congr 1
    ring
  calc L⁻¹ * (∫⁻ y in Ioo c d, ‖rep u y‖ₑ)
        + L ^ (1 - p.toReal⁻¹) * eLpNorm (deriv u 1) p (volume.restrict (Ioo c d))
      ≤ L⁻¹ * (L ^ (1 - q.toReal⁻¹) * eLpNorm (fn u) q (volume.restrict (Ioo c d)))
        + L ^ (1 - p.toReal⁻¹) * eLpNorm (deriv u 1) p (volume.restrict (Ioo c d)) := by
        gcongr
    _ = _ := by rw [← mul_assoc, h2]

/-- **The window estimate**: for `u ∈ W^{1,p}(I)` and a compact interval `[c, d]` inside the
closure of `I`, `|ũ(x)| ≤ (d - c)^{-1/p} ‖u‖_{L^p(c, d)} + (d - c)^{1 - 1/p} ‖u'‖_{L^p(c, d)}`
for every `x ∈ [c, d]`, in `ℝ≥0∞`. Theorem 8.8 (5) of [brezis2011functional] on a bounded
interval, and the local estimate behind its unbounded case and Corollary 8.9. -/
theorem enorm_rep_le_of_Icc_subset (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {c d : ℝ} (hcd : c < d) (hsub : Icc c d ⊆ closure (I : Set ℝ)) {x : ℝ} (hx : x ∈ Icc c d) :
    ‖rep u x‖ₑ ≤ ENNReal.ofReal (d - c) ^ (-p.toReal⁻¹)
        * eLpNorm (fn u) p (volume.restrict (Ioo c d))
      + ENNReal.ofReal (d - c) ^ (1 - p.toReal⁻¹)
        * eLpNorm (deriv u 1) p (volume.restrict (Ioo c d)) :=
  enorm_rep_le_of_Icc_subset' hI u p hcd hsub hx

/-- The real form of `(ENNReal.ofReal L) ^ e * ‖x‖ₑ`. -/
theorem toReal_ofReal_rpow_mul_enorm {E : Type*} [NormedAddCommGroup E] {L : ℝ} (hL : 0 ≤ L)
    (e : ℝ) (x : E) : (ENNReal.ofReal L ^ e * ‖x‖ₑ).toReal = L ^ e * ‖x‖ := by
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hL, toReal_enorm]

/-- `(ENNReal.ofReal L) ^ e * ‖x‖ₑ` is finite for `L > 0`. -/
theorem ofReal_rpow_mul_enorm_ne_top {E : Type*} [NormedAddCommGroup E] {L : ℝ} (hL : 0 < L)
    (e : ℝ) (x : E) : ENNReal.ofReal L ^ e * ‖x‖ₑ ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg' (ENNReal.ofReal_pos.2 hL)
    ENNReal.ofReal_ne_top) enorm_ne_top

/-- **Theorem 8.8 (5) of [brezis2011functional] on a bounded interval, with the constant**: for
`a < b`, `1 ≤ p ≤ ∞`, `u ∈ W^{1,p}(a, b)` and `x ∈ [a, b]`,
`|ũ(x)| ≤ (b - a)^{-1/p} ‖u‖_{L^p} + (b - a)^{1 - 1/p} ‖u'‖_{L^p}` (with `1/p = 0` for `p = ∞`).
At `p = 2` this is the constant `(b - a)^{-1/2} + (b - a)^{1/2}` of
`SobolevInterval.abs_rep_le`. -/
theorem abs_rep_le_of_bounded {a b : ℝ} (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    |rep u x| ≤ (b - a) ^ (-p.toReal⁻¹) * ‖deriv u 0‖
      + (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖ := by
  have h := enorm_rep_le_of_Icc_subset (ordConnected_coe_Ioo a b) u hab
    (by rw [closure_coe_Ioo hab]) hx
  have e0 : eLpNorm (fn u) p (volume.restrict (Ioo a b)) = ‖deriv u 0‖ₑ := by
    rw [Lp.enorm_def]; rfl
  have e1 : eLpNorm (deriv u 1) p (volume.restrict (Ioo a b)) = ‖deriv u 1‖ₑ := by
    rw [Lp.enorm_def]; rfl
  rw [e0, e1] at h
  have hba : 0 < b - a := sub_pos.2 hab
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ofReal_rpow_mul_enorm_ne_top hba _ _,
    ofReal_rpow_mul_enorm_ne_top hba _ _⟩) h
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_add (ofReal_rpow_mul_enorm_ne_top hba _ _)
      (ofReal_rpow_mul_enorm_ne_top hba _ _),
    toReal_ofReal_rpow_mul_enorm hba.le, toReal_ofReal_rpow_mul_enorm hba.le] at this

/-- An unbounded open interval contains, around each point of its closure, a compact interval
of length one. -/
theorem exists_Icc_subset_closure_of_not_isBounded (hI : (I : Set ℝ).OrdConnected)
    (hunb : ¬ Bornology.IsBounded (I : Set ℝ)) {x : ℝ} (hx : x ∈ closure (I : Set ℝ)) :
    ∃ c, c < c + 1 ∧ x ∈ Icc c (c + 1) ∧ Icc c (c + 1) ⊆ closure (I : Set ℝ) := by
  have hcl := I.ordConnected_closure hI
  rw [isBounded_iff_bddBelow_bddAbove, not_and_or] at hunb
  rcases hunb with h | h
  · obtain ⟨y, hy, hyx⟩ : ∃ y ∈ (I : Set ℝ), y < x - 1 := by
      by_contra hcon
      push Not at hcon
      exact h ⟨x - 1, fun y hy ↦ hcon y hy⟩
    refine ⟨x - 1, by linarith, ⟨by linarith, by linarith⟩, ?_⟩
    rw [sub_add_cancel]
    exact (Icc_subset_Icc_left hyx.le).trans (hcl.out (subset_closure hy) hx)
  · obtain ⟨y, hy, hyx⟩ : ∃ y ∈ (I : Set ℝ), x + 1 < y := by
      by_contra hcon
      push Not at hcon
      exact h ⟨x + 1, fun y hy ↦ hcon y hy⟩
    refine ⟨x, by linarith, ⟨le_rfl, by linarith⟩, ?_⟩
    exact (Icc_subset_Icc_right hyx.le).trans (hcl.out hx (subset_closure hy))

/-- **Theorem 8.8 (5) of [brezis2011functional] on an unbounded interval**: for `1 ≤ p ≤ ∞`,
`u ∈ W^{1,p}(I)` and `x ∈ Ī`, `|ũ(x)| ≤ ‖u‖_{L^p(I)} + ‖u'‖_{L^p(I)}` — the window estimate on an
interval of length one around `x`. -/
theorem abs_rep_le_of_unbounded (hI : (I : Set ℝ).OrdConnected)
    (hunb : ¬ Bornology.IsBounded (I : Set ℝ)) (u : SobolevIntervalLp 1 p I) {x : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) : |rep u x| ≤ ‖deriv u 0‖ + ‖deriv u 1‖ := by
  obtain ⟨c, hc, hxc, hsub⟩ := exists_Icc_subset_closure_of_not_isBounded hI hunb hx
  have h := enorm_rep_le_of_Icc_subset hI u hc hsub hxc
  rw [add_sub_cancel_left, ENNReal.ofReal_one, ENNReal.one_rpow, ENNReal.one_rpow, one_mul,
    one_mul] at h
  have h0 : eLpNorm (fn u) p (volume.restrict (Ioo c (c + 1))) ≤ ‖deriv u 0‖ₑ := by
    rw [Lp.enorm_def]
    exact eLpNorm_restrict_le_of_subset_closure hI (Ioo_subset_Icc_self.trans hsub) _ _
  have h1 : eLpNorm (deriv u 1) p (volume.restrict (Ioo c (c + 1))) ≤ ‖deriv u 1‖ₑ := by
    rw [Lp.enorm_def]
    exact eLpNorm_restrict_le_of_subset_closure hI (Ioo_subset_Icc_self.trans hsub) _ _
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨enorm_ne_top, enorm_ne_top⟩)
    (h.trans (add_le_add h0 h1))
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_add enorm_ne_top enorm_ne_top, toReal_enorm, toReal_enorm] at this

variable (p I) in
/-- **The constant of the embedding `W^{1,p}(I) ⊆ L^∞(I)`**, a function of `|I| ≤ ∞` alone:
`max (2, |I|^{-1/p} + |I|^{1 - 1/p})`, where `|I| = (volume I).toReal` is `0` for an unbounded
interval, on which the constant `2` of the window estimate applies. -/
def embeddingConst : ℝ :=
  max 2 ((volume (I : Set ℝ)).toReal ^ (-p.toReal⁻¹)
    + (volume (I : Set ℝ)).toReal ^ (1 - p.toReal⁻¹))

omit [Fact (1 ≤ p)] in
/-- The embedding constant is at least `2`. -/
theorem two_le_embeddingConst (p : ℝ≥0∞) (I : Opens ℝ) : 2 ≤ embeddingConst p I :=
  le_max_left _ _

omit [Fact (1 ≤ p)] in
/-- The embedding constant is positive. -/
theorem embeddingConst_pos (p : ℝ≥0∞) (I : Opens ℝ) : 0 < embeddingConst p I :=
  zero_lt_two.trans_le (two_le_embeddingConst p I)

omit [Fact (1 ≤ p)] in
/-- The embedding constant of a bounded interval dominates `|I|^{-1/p} + |I|^{1 - 1/p}`. -/
theorem rpow_add_rpow_le_embeddingConst {a b : ℝ} (hab : a < b) :
    (b - a) ^ (-p.toReal⁻¹) + (b - a) ^ (1 - p.toReal⁻¹) ≤ embeddingConst p (Opens.Ioo a b) := by
  refine le_trans (le_of_eq ?_) (le_max_right _ _)
  rw [Opens.coe_Ioo, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_pos.2 hab).le]

/-- **Theorem 8.8 (5) of [brezis2011functional]**: for every `1 ≤ p ≤ ∞` and every open interval
`I`, `|ũ(x)| ≤ C ‖u‖_{W^{1,p}(I)}` on `Ī`, with `C = embeddingConst p I` depending only on
`|I| ≤ ∞`. -/
theorem abs_rep_le (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {x : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) : |rep u x| ≤ embeddingConst p I * ‖u‖ := by
  have h0 := norm_deriv_le u 0
  have h1 := norm_deriv_le u 1
  by_cases hb : Bornology.IsBounded (I : Set ℝ)
  · rcases I.eq_intervals_of_ordConnected hI with h | h | ⟨a, h⟩ | ⟨b, h⟩ | ⟨a, b, hab, h⟩
    · exact absurd hx (by rw [h, closure_empty]; exact notMem_empty x)
    · rw [h, isBounded_iff_bddBelow_bddAbove] at hb
      exact absurd hb.2 not_bddAbove_univ
    · rw [h, isBounded_iff_bddBelow_bddAbove] at hb
      exact absurd hb.2 (not_bddAbove_Ioi a)
    · rw [h, isBounded_iff_bddBelow_bddAbove] at hb
      exact absurd hb.1 (not_bddBelow_Iio b)
    · obtain rfl : I = Opens.Ioo a b := Opens.ext h
      rw [closure_coe_Ioo hab] at hx
      refine (abs_rep_le_of_bounded hab u hx).trans ?_
      have hba : 0 < b - a := sub_pos.2 hab
      calc (b - a) ^ (-p.toReal⁻¹) * ‖deriv u 0‖ + (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖
          ≤ (b - a) ^ (-p.toReal⁻¹) * ‖u‖ + (b - a) ^ (1 - p.toReal⁻¹) * ‖u‖ := by
            gcongr
        _ = ((b - a) ^ (-p.toReal⁻¹) + (b - a) ^ (1 - p.toReal⁻¹)) * ‖u‖ := by ring
        _ ≤ embeddingConst p (Opens.Ioo a b) * ‖u‖ :=
            mul_le_mul_of_nonneg_right (rpow_add_rpow_le_embeddingConst hab) (norm_nonneg _)
  · refine (abs_rep_le_of_unbounded hI hb u hx).trans ?_
    calc ‖deriv u 0‖ + ‖deriv u 1‖ ≤ ‖u‖ + ‖u‖ := add_le_add h0 h1
      _ = 2 * ‖u‖ := by ring
      _ ≤ embeddingConst p I * ‖u‖ :=
        mul_le_mul_of_nonneg_right (two_le_embeddingConst p I) (norm_nonneg _)

/-- **`W^{1,p}(I) ⊆ L^∞(I)` with continuous injection** ([brezis2011functional] Theorem 8.8 (5)):
`‖u‖_{L^∞(I)} ≤ C ‖u‖_{W^{1,p}(I)}` with `C = embeddingConst p I`. -/
theorem eLpNorm_top_le (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    eLpNorm (fn u) ⊤ (volume.restrict I) ≤ ENNReal.ofReal (embeddingConst p I * ‖u‖) := by
  have h := eLpNorm_le_of_ae_bound (p := ⊤) (μ := volume.restrict (I : Set ℝ))
    (Lp.aestronglyMeasurable (deriv u 0)) (C := embeddingConst p I * ‖u‖) ?_
  · rw [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul] at h
    exact h
  · filter_upwards [fn_ae_eq_rep hI u, ae_restrict_mem I.isOpen.measurableSet] with x hx hxI
    rw [Real.norm_eq_abs, deriv_zero, hx]
    exact abs_rep_le hI u (subset_closure hxI)

/-- The function of `u ∈ W^{1,p}(I)` lies in `L^∞(I)`. -/
theorem memLp_top (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    MemLp (fn u) ⊤ (volume.restrict I) :=
  memLp_iff.2 ((eLpNorm_top_le hI u).trans_lt ENNReal.ofReal_lt_top)

/-- The continuous representative of `u ∈ W^{1,p}(I)` lies in `L^∞(I)`, with the bound of
Theorem 8.8 (5). -/
theorem eLpNorm_top_rep_le (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    eLpNorm (rep u) ⊤ (volume.restrict I) ≤ ENNReal.ofReal (embeddingConst p I * ‖u‖) := by
  rw [← eLpNorm_congr_ae (fn_ae_eq_rep hI u)]
  exact eLpNorm_top_le hI u

/-- The continuous representative of `u ∈ W^{1,p}(I)` lies in `L^∞(I)`. -/
theorem memLp_top_rep (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    MemLp (rep u) ⊤ (volume.restrict I) :=
  (memLp_top hI u).ae_eq (fn_ae_eq_rep hI u)

end SobolevIntervalLp


/-! ### The Hölder estimate and the embedding `W^{1,p}(a, b) ↪ C[a, b]` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- **The Hölder estimate of Theorem 8.8's proof of (6)**: for `u ∈ W^{1,p}(I)` and
`x, y ∈ Ī`, `|ũ(x) - ũ(y)| ≤ ‖u'‖_p |x - y|^{1 - 1/p}` (the Lipschitz bound of Proposition
8.4 at `p = ∞`). -/
theorem abs_rep_sub_rep_le (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {x y : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    |rep u x - rep u y| ≤ ‖deriv u 1‖ * |x - y| ^ (1 - p.toReal⁻¹) := by
  rw [rep_sub_rep hI u hy hx]
  have h := enorm_intervalIntegral_le_rpow_mul_eLpNorm (p := p) (deriv u 1) y x
  have hsub : Ι y x ⊆ closure (I : Set ℝ) :=
    uIoc_subset_uIcc.trans ((I.ordConnected_closure hI).uIcc_subset hy hx)
  have h2 : eLpNorm (deriv u 1) p (volume.restrict (Ι y x)) ≤ ‖deriv u 1‖ₑ := by
    rw [Lp.enorm_def]
    exact eLpNorm_restrict_le_of_subset_closure hI hsub _ _
  have h3 := h.trans (mul_le_mul' le_rfl h2)
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
    (one_sub_toReal_inv_nonneg Fact.out) ENNReal.ofReal_ne_top) enorm_ne_top) h3
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _),
    toReal_ofReal_rpow_mul_enorm (abs_nonneg _), mul_comm] at this

/-- The continuous representative is uniformly Hölder continuous of exponent `1 - 1/p` on the
closure of `I`, with constant `‖u'‖_p`, in Mathlib's vocabulary. -/
theorem holderOnWith_rep (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    HolderOnWith ‖deriv u 1‖₊ ⟨1 - p.toReal⁻¹, one_sub_toReal_inv_nonneg Fact.out⟩ (rep u)
      (closure (I : Set ℝ)) := by
  intro x hx y hy
  change edist (rep u x) (rep u y)
    ≤ (‖deriv u 1‖₊ : ℝ≥0∞) * edist x y ^ (1 - p.toReal⁻¹)
  rw [edist_dist, Real.dist_eq, edist_dist, Real.dist_eq, ← enorm_eq_nnnorm,
    ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
    (one_sub_toReal_inv_nonneg Fact.out), ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_rep_sub_rep_le hI u hx hy)

variable {a b : ℝ}

/-- The embedding `W^{1,p}(a, b) → C[a, b]` as a linear map: `u ↦` its continuous
representative, restricted to `[a, b]`. Linearity is the canonicity of the representative. -/
def toContinuousMapₗ (hab : a < b) : SobolevIntervalLp 1 p (Opens.Ioo a b) →ₗ[ℝ] C(Icc a b, ℝ) where
  toFun u := ⟨fun x ↦ rep u x,
    (continuousOn_rep_Icc hab u).comp_continuous continuous_subtype_val fun x ↦ x.2⟩
  map_add' u v := ContinuousMap.ext fun x ↦ rep_add_Icc hab u v x.2
  map_smul' c u := ContinuousMap.ext fun x ↦ rep_smul_Icc hab c u x.2

/-- The embedding constant, for the linear map. -/
theorem norm_toContinuousMapₗ_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖toContinuousMapₗ hab u‖ ≤ embeddingConst p (Opens.Ioo a b) * ‖u‖ :=
  (ContinuousMap.norm_le _ (mul_nonneg (embeddingConst_pos p (Opens.Ioo a b)).le
    (norm_nonneg _))).2 fun x ↦ by
    rw [Real.norm_eq_abs]
    exact abs_rep_le (ordConnected_coe_Ioo a b) u (by rw [closure_coe_Ioo hab]; exact x.2)

/-- **The embedding `W^{1,p}(a, b) ↪ C[a, b]`** ([brezis2011functional] Theorem 8.8): the
continuous linear map sending `u` to its continuous representative on `[a, b]`, of norm at most
`embeddingConst p (Opens.Ioo a b)`. It is injective (`toContinuousMap_injective`) and, for
`1 < p ≤ ∞`, compact (`isCompactOperator_toContinuousMap`). -/
def toContinuousMap (hab : a < b) : SobolevIntervalLp 1 p (Opens.Ioo a b) →L[ℝ] C(Icc a b, ℝ) :=
  LinearMap.mkContinuous (toContinuousMapₗ hab) (embeddingConst p (Opens.Ioo a b))
    (fun u ↦ norm_toContinuousMapₗ_le hab u)

/-- The embedding is the continuous representative on `[a, b]`. -/
theorem toContinuousMap_apply (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b))
    (x : Icc a b) : toContinuousMap hab u x = rep u x := rfl

/-- **The embedding constant of `W^{1,p}(a, b) ↪ C[a, b]`**:
`‖u‖_∞ ≤ embeddingConst p (Opens.Ioo a b) * ‖u‖_{W^{1,p}}`. -/
theorem norm_toContinuousMap_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖toContinuousMap hab u‖ ≤ embeddingConst p (Opens.Ioo a b) * ‖u‖ :=
  norm_toContinuousMapₗ_le hab u

/-- The operator norm of the embedding `W^{1,p}(a, b) ↪ C[a, b]`. -/
theorem norm_toContinuousMap_le' (hab : a < b) :
    ‖(toContinuousMap hab : SobolevIntervalLp 1 p (Opens.Ioo a b) →L[ℝ] C(Icc a b, ℝ))‖
      ≤ embeddingConst p (Opens.Ioo a b) :=
  LinearMap.mkContinuous_norm_le _ (embeddingConst_pos p (Opens.Ioo a b)).le _

/-- The function of `u` agrees almost everywhere on `(a, b)` with its embedding into `C[a, b]`,
extended by the endpoint values outside `[a, b]`. -/
theorem coe_toContinuousMap_ae_eq (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hab.le (toContinuousMap hab u) :=
  (fn_ae_eq_rep (ordConnected_coe_Ioo a b) u).trans ((ae_restrict_iff' measurableSet_Ioo).2
    (Eventually.of_forall fun x hx ↦ by
      rw [IccExtend_of_mem hab.le _ (Ioo_subset_Icc_self hx)]; rfl))

/-- The embedding is canonical: any function continuous on `[a, b]` that agrees almost everywhere
with `u` on `(a, b)` is the embedding of `u` on all of `[a, b]`. -/
theorem toContinuousMap_eq_of_continuousOn (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b))
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) (hu : fn u =ᵐ[volume.restrict (Ioo a b)] g)
    (x : Icc a b) : toContinuousMap hab u x = g x :=
  rep_eq_of_continuousOn (ordConnected_coe_Ioo a b) u (by rwa [closure_coe_Ioo hab]) hu
    (by rw [closure_coe_Ioo hab]; exact x.2)

/-- **The fundamental theorem of calculus in `W^{1,p}(a, b)`**: the embedding of `u` into
`C[a, b]` is the integral of `u'` between any two points of `[a, b]`. -/
theorem toContinuousMap_sub_eq_integral (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b))
    (x y : Icc a b) :
    toContinuousMap hab u y - toContinuousMap hab u x = ∫ t in (x : ℝ)..y, deriv u 1 t :=
  rep_sub_rep_Ioo hab u x.2 y.2

/-- The embedding of `u` into `C[a, b]`, extended by the endpoint values outside `[a, b]`, is
absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_toContinuousMap (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    AbsolutelyContinuousOnInterval (IccExtend hab.le (toContinuousMap hab u)) a b :=
  (absolutelyContinuousOnInterval_rep (ordConnected_coe_Ioo a b) u
    (by rw [closure_coe_Ioo hab]; exact left_mem_Icc.2 hab.le)
    (by rw [closure_coe_Ioo hab]; exact right_mem_Icc.2 hab.le)).congr fun x hx ↦ by
    rw [uIcc_of_le hab.le] at hx
    rw [IccExtend_of_mem hab.le _ hx]; rfl

/-- **The embedding `W^{1,p}(a, b) ↪ C[a, b]` is injective**: the continuous representative
determines the `L^p` class of the function, and the weak derivative is determined by the
function almost everywhere. -/
theorem toContinuousMap_injective (hab : a < b) :
    Function.Injective (toContinuousMap hab : SobolevIntervalLp 1 p (Opens.Ioo a b) →L[ℝ] _) := by
  intro u v huv
  have h1 := coe_toContinuousMap_ae_eq hab u
  have h2 := coe_toContinuousMap_ae_eq hab v
  rw [huv] at h1
  exact SobolevMultiIndex.ext_of_fn_ae_eq (h1.trans h2.symm)

/-- **A function of `W^{1,p}(a, b)` continuous on `[a, b]` is the continuous representative of
an element**. -/
theorem exists_toContinuousMap_eq (hab : a < b) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (hmem : MemSobolevIntervalLp g 1 p (Opens.Ioo a b)) :
    ∃ u : SobolevIntervalLp 1 p (Opens.Ioo a b), ∀ t : Icc a b, toContinuousMap hab u t = g t := by
  obtain ⟨u, hu⟩ := hmem.exists_sobolevIntervalLp
  exact ⟨u, fun t ↦ toContinuousMap_eq_of_continuousOn hab u hg hu t⟩

/-- **Point evaluation on `W^{1,p}(a, b)`** at a point of `[a, b]`, as a bounded linear
functional: the composition of the embedding into `C[a, b]` with evaluation. -/
def evalCLM (hab : a < b) (c : Icc a b) : StrongDual ℝ (SobolevIntervalLp 1 p (Opens.Ioo a b)) :=
  (ContinuousMap.evalCLM ℝ c).comp (toContinuousMap hab)

/-- Point evaluation on `W^{1,p}(a, b)` evaluates the continuous representative. -/
@[simp]
theorem evalCLM_apply (hab : a < b) (c : Icc a b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    evalCLM hab c u = rep u c := rfl

omit [Fact (1 ≤ p)] in
/-- The exponent `1 - 1/p` is positive for `1 < p ≤ ∞`. -/
theorem one_sub_toReal_inv_pos (hp : 1 < p) : 0 < 1 - p.toReal⁻¹ := by
  rw [sub_pos]
  rcases eq_or_ne p ⊤ with rfl | hp'
  · simp
  · exact inv_lt_one_of_one_lt₀ (by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp').2 hp
      rwa [ENNReal.toReal_one] at this)

/-- **Theorem 8.8 (6) of [brezis2011functional]**: for `1 < p ≤ ∞` and a bounded interval, the
embedding `W^{1,p}(a, b) ↪ C[a, b]` is a compact operator. The image of the unit ball is bounded
in `C[a, b]` by (5) and uniformly Hölder continuous of exponent `1 - 1/p > 0`
(`SobolevIntervalLp.abs_rep_sub_rep_le`), so its closure is compact by Arzelà–Ascoli
(`ContinuousMap.isCompact_closure_of_forall_norm_le`); this is where `p > 1` enters. -/
theorem isCompactOperator_toContinuousMap (hab : a < b) (hp : 1 < p) :
    IsCompactOperator (toContinuousMap hab : SobolevIntervalLp 1 p (Opens.Ioo a b) →L[ℝ] _) := by
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (toContinuousMap (p := p) hab : SobolevIntervalLp 1 p (Opens.Ioo a b) →ₗ[ℝ] C(Icc a b, ℝ))
    one_pos).2 ?_
  refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := embeddingConst p (Opens.Ioo a b))
    ?_ ?_
  · rintro f ⟨u, hu, rfl⟩ x
    calc ‖toContinuousMap hab u x‖ ≤ ‖toContinuousMap hab u‖ :=
          (toContinuousMap hab u).norm_coe_le_norm x
      _ ≤ embeddingConst p (Opens.Ioo a b) * ‖u‖ := norm_toContinuousMap_le hab u
      _ ≤ embeddingConst p (Opens.Ioo a b) * 1 :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu)
            (embeddingConst_pos p (Opens.Ioo a b)).le
      _ = embeddingConst p (Opens.Ioo a b) := mul_one _
  · intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    set e : ℝ := 1 - p.toReal⁻¹ with he
    have he0 : 0 < e := one_sub_toReal_inv_pos hp
    set δ : ℝ := ε ^ (1 / e) with hδ
    have hδ0 : 0 < δ := Real.rpow_pos_of_pos hε _
    have hδe : δ ^ e = ε := by
      rw [hδ, ← Real.rpow_mul hε.le, one_div, inv_mul_cancel₀ he0.ne', Real.rpow_one]
    filter_upwards [Metric.ball_mem_nhds x₀ hδ0] with x hx
    rintro ⟨f, u, hu, rfl⟩
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    have hd : dist x₀ x < δ := by rw [dist_comm]; exact hx
    rw [Subtype.dist_eq, Real.dist_eq] at hd
    have hcl : ∀ y : Icc a b, (y : ℝ) ∈ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := fun y ↦ by
      rw [closure_coe_Ioo hab]; exact y.2
    calc dist (toContinuousMap hab u x₀) (toContinuousMap hab u x)
        = |rep u x₀ - rep u x| := by rw [Real.dist_eq]; rfl
      _ ≤ ‖deriv u 1‖ * |(x₀ : ℝ) - x| ^ e :=
          abs_rep_sub_rep_le (ordConnected_coe_Ioo a b) u (hcl x₀) (hcl x)
      _ ≤ 1 * |(x₀ : ℝ) - x| ^ e :=
          mul_le_mul_of_nonneg_right ((norm_deriv_le u 1).trans hu1) (by positivity)
      _ < 1 * δ ^ e := by
          rw [one_mul, one_mul]
          exact Real.rpow_lt_rpow (abs_nonneg _) hd he0
      _ = ε := by rw [one_mul, hδe]

/-- **Theorem 8.8 (6) of [brezis2011functional]**, in the vocabulary of
`Numlib/Analysis/Normed/Operator/Embedding.lean`: for `1 < p ≤ ∞`, `W^{1,p}(a, b) ↪ C[a, b]` is
a compact embedding. -/
theorem isCompactEmbedding_toContinuousMap (hab : a < b) (hp : 1 < p) :
    IsCompactEmbedding
      (toContinuousMap (p := p) hab : SobolevIntervalLp 1 p (Opens.Ioo a b) →ₗ[ℝ] C(Icc a b, ℝ)) :=
  isCompactEmbedding_iff_isCompactOperator.2
    ⟨toContinuousMap_injective hab, isCompactOperator_toContinuousMap hab hp⟩

end SobolevIntervalLp


/-! ### Remark 12: the inclusions `W^{1,p}(I) ⊆ L^q(I)` -/

section Interpolation

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **The interpolation inequality `‖f‖_q ≤ ‖f‖_p^{p/q} ‖f‖_∞^{1 - p/q}`** for `0 < p ≤ q < ∞`
([brezis2011functional] Remark 12 of chapter 8, and Remark 2 of chapter 4 with `q = ∞`): almost
everywhere `‖f‖^q = ‖f‖^p ‖f‖^{q - p} ≤ ‖f‖^p ‖f‖_∞^{q - p}`, integrated. -/
theorem MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_top_rpow {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) (hq : q ≠ ⊤) :
    eLpNorm f q μ ≤ eLpNorm f p μ ^ (p.toReal / q.toReal)
      * eLpNorm f ⊤ μ ^ (1 - p.toReal / q.toReal) := by
  have hp_top : p ≠ ⊤ := ne_top_of_le_ne_top hq hpq
  have hq0 : q ≠ 0 := fun h ↦ hp (le_antisymm (h ▸ hpq) zero_le)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hpqr : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  set M := eLpNorm f ⊤ μ with hM
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M := by
    rw [hM, eLpNorm_exponent_top hf]; exact ae_le_eLpNormEssSup
  have hpt : ∀ᵐ x ∂μ, ‖f x‖ₑ ^ q.toReal ≤ ‖f x‖ₑ ^ p.toReal * M ^ (q.toReal - p.toReal) := by
    filter_upwards [hbound] with x hx
    calc ‖f x‖ₑ ^ q.toReal = ‖f x‖ₑ ^ (p.toReal + (q.toReal - p.toReal)) := by
          congr 1; ring
      _ = ‖f x‖ₑ ^ p.toReal * ‖f x‖ₑ ^ (q.toReal - p.toReal) :=
          ENNReal.rpow_add_of_nonneg _ _ hpr.le (sub_nonneg.2 hpqr)
      _ ≤ ‖f x‖ₑ ^ p.toReal * M ^ (q.toReal - p.toReal) := by
          gcongr
  have hmeas : AEMeasurable (fun x ↦ ‖f x‖ₑ ^ p.toReal) μ := hf.enorm.pow_const _
  have hint : ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ
      ≤ (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) * M ^ (q.toReal - p.toReal) := by
    rw [← lintegral_mul_const'' _ hmeas]
    exact lintegral_mono_ae hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp_top hf]
  calc (∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal)
      ≤ ((∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) * M ^ (q.toReal - p.toReal)) ^ (1 / q.toReal) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / q.toReal)
          * M ^ ((q.toReal - p.toReal) * (1 / q.toReal)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.rpow_mul]
    _ = ((∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) ^ (p.toReal / q.toReal)
          * M ^ (1 - p.toReal / q.toReal) := by
        rw [← ENNReal.rpow_mul]
        congr 2
        · field_simp
        · field_simp

/-- **`L^p ∩ L^∞ ⊆ L^q` for `p ≤ q`** ([brezis2011functional] Remark 12 of chapter 8). -/
theorem MeasureTheory.MemLp.of_le_of_memLp_top {f : α → ℝ} {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q)
    (hfp : MemLp f p μ) (hft : MemLp f ⊤ μ) : MemLp f q μ := by
  rcases eq_or_ne q ⊤ with rfl | hq
  · exact hft
  refine memLp_iff.2 ((eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_top_rpow hfp.aestronglyMeasurable hp
    hpq hq).trans_lt (ENNReal.mul_lt_top ?_ ?_))
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hfp.eLpNorm_ne_top
  · have hpqr : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
    have hqr : 0 < q.toReal := ENNReal.toReal_pos (fun h ↦ hp (le_antisymm (h ▸ hpq) zero_le)) hq
    exact ENNReal.rpow_lt_top_of_nonneg (by rw [sub_nonneg, div_le_one hqr]; exact hpqr)
      hft.eLpNorm_ne_top

end Interpolation

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- **Remark 12 of [brezis2011functional]**: for `p ≤ q ≤ ∞`, the function of `u ∈ W^{1,p}(I)`
lies in `L^q(I)`, with `‖u‖_{L^q} ≤ C ‖u‖_{W^{1,p}}` for the constant of Theorem 8.8 (5), since
`‖u‖_q ≤ ‖u‖_p^{p/q} ‖u‖_∞^{1 - p/q}`. -/
theorem eLpNorm_le_of_le (hI : (I : Set ℝ).OrdConnected) {q : ℝ≥0∞} (hpq : p ≤ q)
    (u : SobolevIntervalLp 1 p I) :
    eLpNorm (fn u) q (volume.restrict I) ≤ ENNReal.ofReal (embeddingConst p I * ‖u‖) := by
  rcases eq_or_ne q ⊤ with rfl | hq
  · exact eLpNorm_top_le hI u
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  set C := ENNReal.ofReal (embeddingConst p I * ‖u‖) with hC
  have hθ0 : 0 ≤ p.toReal / q.toReal := by positivity
  have hθ1 : 0 ≤ 1 - p.toReal / q.toReal := by
    rw [sub_nonneg]
    rcases eq_or_ne q 0 with rfl | hq0
    · simp
    · exact (div_le_one (ENNReal.toReal_pos hq0 hq)).2 (ENNReal.toReal_mono hq hpq)
  have hp' : eLpNorm (fn u) p (volume.restrict I) ≤ C := by
    have e : eLpNorm (fn u) p (volume.restrict I) = ‖deriv u 0‖ₑ := by rw [Lp.enorm_def]; rfl
    rw [e, ← ofReal_norm, hC]
    refine ENNReal.ofReal_le_ofReal ((norm_deriv_le u 0).trans ?_)
    calc ‖u‖ = 1 * ‖u‖ := (one_mul _).symm
      _ ≤ embeddingConst p I * ‖u‖ :=
        mul_le_mul_of_nonneg_right (one_le_two.trans (two_le_embeddingConst p I)) (norm_nonneg _)
  calc eLpNorm (fn u) q (volume.restrict I)
      ≤ eLpNorm (fn u) p (volume.restrict I) ^ (p.toReal / q.toReal)
          * eLpNorm (fn u) ⊤ (volume.restrict I) ^ (1 - p.toReal / q.toReal) :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_top_rpow (Lp.aestronglyMeasurable (deriv u 0)) hp0
          hpq hq
    _ ≤ C ^ (p.toReal / q.toReal) * C ^ (1 - p.toReal / q.toReal) := by
        gcongr
        exact eLpNorm_top_le hI u
    _ = C := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0 hθ1, add_sub_cancel, ENNReal.rpow_one]

/-- **Remark 12 of [brezis2011functional]**: `W^{1,p}(I) ⊆ L^q(I)` for `p ≤ q ≤ ∞`. -/
theorem memLp_of_le (hI : (I : Set ℝ).OrdConnected) {q : ℝ≥0∞} (hpq : p ≤ q)
    (u : SobolevIntervalLp 1 p I) : MemLp (fn u) q (volume.restrict I) :=
  memLp_iff.2 ((eLpNorm_le_of_le hI hpq u).trans_lt ENNReal.ofReal_lt_top)

variable (p) in
/-- The inclusion `W^{1,p}(I) → L^q(I)`, `p ≤ q ≤ ∞`, as a linear map. -/
def toLpₗ (hI : (I : Set ℝ).OrdConnected) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q) :
    SobolevIntervalLp 1 p I →ₗ[ℝ] Lp ℝ q (volume.restrict (I : Set ℝ)) where
  toFun u := (memLp_of_le hI hpq u).toLp _
  map_add' u v := by
    rw [(memLp_of_le hI hpq (u + v)).toLp_congr ((memLp_of_le hI hpq u).add (memLp_of_le hI hpq v))
      (SobolevMultiIndex.fn_add u v), MemLp.toLp_add]
  map_smul' r u := by
    rw [RingHom.id_apply, (memLp_of_le hI hpq (r • u)).toLp_congr
      ((memLp_of_le hI hpq u).const_smul r) (SobolevMultiIndex.fn_smul r u), MemLp.toLp_const_smul]

/-- The `L^q` norm of the inclusion of `u`. -/
theorem norm_toLpₗ_le (hI : (I : Set ℝ).OrdConnected) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (u : SobolevIntervalLp 1 p I) : ‖toLpₗ p hI hpq u‖ ≤ embeddingConst p I * ‖u‖ := by
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNorm_le_of_le hI hpq u)).trans_eq ?_
  exact ENNReal.toReal_ofReal (mul_nonneg (embeddingConst_pos p I).le (norm_nonneg _))

variable (p) in
/-- **The inclusion `W^{1,p}(I) ↪ L^q(I)` for `p ≤ q ≤ ∞`** ([brezis2011functional] Remark 12),
as a continuous linear map of norm at most `embeddingConst p I`; at `q = ∞` this is the
embedding of Theorem 8.8 (5). -/
def toLp (hI : (I : Set ℝ).OrdConnected) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q) :
    SobolevIntervalLp 1 p I →L[ℝ] Lp ℝ q (volume.restrict (I : Set ℝ)) :=
  LinearMap.mkContinuous (toLpₗ p hI hpq) (embeddingConst p I) (fun u ↦ norm_toLpₗ_le hI hpq u)

/-- The inclusion into `L^q(I)` is the function, almost everywhere. -/
theorem coeFn_toLp (hI : (I : Set ℝ).OrdConnected) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (u : SobolevIntervalLp 1 p I) : ⇑(toLp p hI hpq u) =ᵐ[volume.restrict I] fn u :=
  (memLp_of_le hI hpq u).coeFn_toLp

/-- The norm of the inclusion `W^{1,p}(I) ↪ L^q(I)` is at most `embeddingConst p I`. -/
theorem norm_toLp_le (hI : (I : Set ℝ).OrdConnected) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q) :
    ‖toLp p hI hpq‖ ≤ embeddingConst p I :=
  LinearMap.mkContinuous_norm_le _ (embeddingConst_pos p I).le _

variable {a b : ℝ}

/-- On a bounded interval, the function of `u ∈ W^{1,p}(a, b)` lies in every `L^q(a, b)`,
`1 ≤ q ≤ ∞`, being bounded. -/
theorem memLp_of_bounded (q : ℝ≥0∞) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    MemLp (fn u) q (volume.restrict (Ioo a b)) := by
  have : IsFiniteMeasure (volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ)) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Opens.coe_Ioo, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  exact (memLp_top (ordConnected_coe_Ioo a b) u).mono_exponent le_top

/-- The `L^q(a, b)` norm of `u ∈ W^{1,p}(a, b)`: `‖u‖_q ≤ (b - a)^{1/q} ‖u‖_∞`. -/
theorem eLpNorm_le_of_bounded (q : ℝ≥0∞) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    eLpNorm (fn u) q (volume.restrict (Ioo a b))
      ≤ ENNReal.ofReal (b - a) ^ q.toReal⁻¹
        * ENNReal.ofReal (embeddingConst p (Opens.Ioo a b) * ‖u‖) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Ioo a b))
    (f := fn u) (p := q) (q := ⊤) le_top (Lp.aestronglyMeasurable (deriv u 0))
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo, ENNReal.toReal_top,
    div_zero, sub_zero, one_div, mul_comm] at h
  refine h.trans ?_
  gcongr
  exact eLpNorm_top_le (ordConnected_coe_Ioo a b) u

variable (p) in
/-- The inclusion `W^{1,p}(a, b) → L^q(a, b)`, every `1 ≤ q ≤ ∞`, as a linear map. -/
def toLpOfBoundedₗ (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    SobolevIntervalLp 1 p (Opens.Ioo a b) →ₗ[ℝ] Lp ℝ q (volume.restrict (Ioo a b)) where
  toFun u := (memLp_of_bounded q u).toLp _
  map_add' u v := by
    rw [(memLp_of_bounded q (u + v)).toLp_congr ((memLp_of_bounded q u).add
      (memLp_of_bounded q v)) (SobolevMultiIndex.fn_add u v), MemLp.toLp_add]
  map_smul' r u := by
    rw [RingHom.id_apply, (memLp_of_bounded q (r • u)).toLp_congr
      ((memLp_of_bounded q u).const_smul r) (SobolevMultiIndex.fn_smul r u),
      MemLp.toLp_const_smul]

/-- The `L^q(a, b)` norm of the inclusion of `u`. -/
theorem norm_toLpOfBoundedₗ_le (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖toLpOfBoundedₗ p q u‖
      ≤ (b - a) ^ q.toReal⁻¹ * embeddingConst p (Opens.Ioo a b) * ‖u‖ := by
  rw [toLpOfBoundedₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
  have hfin : ENNReal.ofReal (b - a) ^ q.toReal⁻¹
      * ENNReal.ofReal (embeddingConst p (Opens.Ioo a b) * ‖u‖) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  refine (ENNReal.toReal_mono hfin (eLpNorm_le_of_bounded q u)).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (sub_pos.2 hab).le,
    ENNReal.toReal_ofReal (mul_nonneg (embeddingConst_pos _ _).le (norm_nonneg _)), mul_assoc]

variable (p) in
/-- **The inclusion `W^{1,p}(a, b) ↪ L^q(a, b)` for every `1 ≤ q ≤ ∞`** on a bounded interval
([brezis2011functional] Remark 12 and Theorem 8.8 (5)), as a continuous linear map of norm at
most `(b - a)^{1/q} embeddingConst p (Opens.Ioo a b)`. -/
def toLpOfBounded (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    SobolevIntervalLp 1 p (Opens.Ioo a b) →L[ℝ] Lp ℝ q (volume.restrict (Ioo a b)) :=
  LinearMap.mkContinuous (toLpOfBoundedₗ p q)
    ((b - a) ^ q.toReal⁻¹ * embeddingConst p (Opens.Ioo a b))
    (fun u ↦ norm_toLpOfBoundedₗ_le hab q u)

/-- The inclusion into `L^q(a, b)` is the function, almost everywhere. -/
theorem coeFn_toLpOfBounded (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ⇑(toLpOfBounded p hab q u) =ᵐ[volume.restrict (Ioo a b)] fn u :=
  (memLp_of_bounded q u).coeFn_toLp

end SobolevIntervalLp


/-! ### Corollary 8.9: decay at infinity -/

section Tail

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The `L^p` norm of `f ∈ L^p(μ)`, `p < ∞`, over the tail `(x, ∞)` tends to `0` as `x → ∞`. -/
theorem MeasureTheory.tendsto_eLpNorm_restrict_Ioi_atTop {μ : Measure ℝ} {f : ℝ → ℝ} (hp : p ≠ ⊤)
    (hf : MemLp f p μ) : Tendsto (fun x ↦ eLpNorm f p (μ.restrict (Ioi x))) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ := hf.integrable_norm_rpow hp0 hp
  have h1 : Tendsto (fun x ↦ ∫ t in Ioi x, ‖f t‖ ^ p.toReal ∂μ) atTop
      (𝓝 (∫ t in ⋂ x : ℝ, Ioi x, ‖f t‖ ^ p.toReal ∂μ)) :=
    tendsto_setIntegral_of_antitone (fun _ ↦ measurableSet_Ioi) (fun _ _ hxy ↦ Ioi_subset_Ioi hxy)
      ⟨0, hint.integrableOn⟩
  have hempty : ⋂ x : ℝ, Ioi x = ∅ :=
    eq_empty_iff_forall_notMem.2 fun y hy ↦ lt_irrefl y (mem_iInter.1 hy y)
  rw [hempty, Measure.restrict_empty, integral_zero_measure] at h1
  have h2 : ∀ x, eLpNorm f p (μ.restrict (Ioi x))
      = ENNReal.ofReal ((∫ t in Ioi x, ‖f t‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) := fun x ↦
    (hf.restrict _).eLpNorm_eq_integral_rpow_norm hp0 hp
  simp_rw [h2]
  have h3 : Tendsto (fun x ↦ (∫ t in Ioi x, ‖f t‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) atTop (𝓝 0) := by
    have := h1.rpow_const (p := p.toReal⁻¹) (Or.inr (inv_nonneg.2 hpr.le))
    rwa [Real.zero_rpow (inv_ne_zero hpr.ne')] at this
  simpa using ENNReal.tendsto_ofReal h3

/-- The `L^p` norm of `f ∈ L^p(μ)`, `p < ∞`, over the tail `(-∞, x)` tends to `0` as `x → -∞`. -/
theorem MeasureTheory.tendsto_eLpNorm_restrict_Iio_atBot {μ : Measure ℝ} {f : ℝ → ℝ} (hp : p ≠ ⊤)
    (hf : MemLp f p μ) : Tendsto (fun x ↦ eLpNorm f p (μ.restrict (Iio x))) atBot (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ := hf.integrable_norm_rpow hp0 hp
  have h1 : Tendsto (fun x ↦ ∫ t in Iio (-x), ‖f t‖ ^ p.toReal ∂μ) atTop
      (𝓝 (∫ t in ⋂ x : ℝ, Iio (-x), ‖f t‖ ^ p.toReal ∂μ)) :=
    tendsto_setIntegral_of_antitone (fun _ ↦ measurableSet_Iio)
      (fun _ _ hxy ↦ Iio_subset_Iio (neg_le_neg hxy)) ⟨0, hint.integrableOn⟩
  have hempty : ⋂ x : ℝ, Iio (-x) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun y hy ↦ lt_irrefl y (by simpa using mem_iInter.1 hy (-y))
  rw [hempty, Measure.restrict_empty, integral_zero_measure] at h1
  have h2 : ∀ x, eLpNorm f p (μ.restrict (Iio x))
      = ENNReal.ofReal ((∫ t in Iio x, ‖f t‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) := fun x ↦
    (hf.restrict _).eLpNorm_eq_integral_rpow_norm hp0 hp
  simp_rw [h2]
  have h3 : Tendsto (fun x ↦ (∫ t in Iio (-x), ‖f t‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) atTop (𝓝 0) := by
    have := h1.rpow_const (p := p.toReal⁻¹) (Or.inr (inv_nonneg.2 hpr.le))
    rwa [Real.zero_rpow (inv_ne_zero hpr.ne')] at this
  have h4 := ENNReal.tendsto_ofReal h3
  rw [ENNReal.ofReal_zero] at h4
  have h5 := h4.comp tendsto_neg_atBot_atTop
  refine h5.congr fun x ↦ ?_
  simp only [Function.comp_apply, neg_neg]

end Tail

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- **The continuous representative tends to `0` along windows of length one whose `L^p` norms
tend to `0`**: the engine of Corollary 8.9, for any filter on the line. -/
theorem tendsto_rep_of_tendsto_window (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {l : Filter ℝ} {c : ℝ → ℝ}
    (hc : ∀ᶠ x in l, x ∈ Icc (c x) (c x + 1) ∧ Icc (c x) (c x + 1) ⊆ closure (I : Set ℝ))
    (h0 : Tendsto (fun x ↦ eLpNorm (fn u) p (volume.restrict (Ioo (c x) (c x + 1)))) l (𝓝 0))
    (h1 : Tendsto (fun x ↦ eLpNorm (deriv u 1) p (volume.restrict (Ioo (c x) (c x + 1)))) l
      (𝓝 0)) :
    Tendsto (rep u) l (𝓝 0) := by
  set A : ℝ → ℝ≥0∞ := fun x ↦ eLpNorm (fn u) p (volume.restrict (Ioo (c x) (c x + 1)))
    + eLpNorm (deriv u 1) p (volume.restrict (Ioo (c x) (c x + 1))) with hA
  have hAlim : Tendsto A l (𝓝 0) := by
    have := h0.add h1
    rwa [add_zero] at this
  have hbound : ∀ᶠ x in l, ‖rep u x‖ ≤ (A x).toReal := by
    filter_upwards [hc] with x hx
    have hfin : A x ≠ ⊤ := by
      rw [hA]
      refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
      · exact ((eLpNorm_restrict_le_of_subset_closure hI (Ioo_subset_Icc_self.trans hx.2)
          _ _).trans_lt (Lp.memLp (deriv u 0)).eLpNorm_lt_top).ne
      · exact ((eLpNorm_restrict_le_of_subset_closure hI (Ioo_subset_Icc_self.trans hx.2)
          _ _).trans_lt (Lp.memLp (deriv u 1)).eLpNorm_lt_top).ne
    have h := enorm_rep_le_of_Icc_subset hI u (by linarith : c x < c x + 1) hx.2 hx.1
    rw [add_sub_cancel_left, ENNReal.ofReal_one, ENNReal.one_rpow, ENNReal.one_rpow, one_mul,
      one_mul] at h
    have := ENNReal.toReal_mono hfin h
    rwa [toReal_enorm] at this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Eventually.of_forall fun x ↦ norm_nonneg _) hbound
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hAlim
  rw [ENNReal.toReal_zero] at this
  exact this

/-- The `L^p(I)` norms of `f ∈ L^p(I)`, `p < ∞`, over windows `(x, x + 1)` lying eventually in
the closure of `I` tend to `0` as `x → ∞`. -/
theorem tendsto_eLpNorm_window_atTop (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict I))
    (hsub : ∀ᶠ x in atTop, Icc x (x + 1) ⊆ closure (I : Set ℝ)) :
    Tendsto (fun x ↦ eLpNorm f p (volume.restrict (Ioo x (x + 1)))) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_restrict_Ioi_atTop hp hf) (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hsub] with x hx
  rw [eLpNorm_restrict_eq_of_subset_closure hI (Ioo_subset_Icc_self.trans hx),
    ← Measure.restrict_restrict measurableSet_Ioo]
  exact eLpNorm_mono_measure _ (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)

/-- The `L^p(I)` norms of `f ∈ L^p(I)`, `p < ∞`, over windows `(x - 1, x)` lying eventually in
the closure of `I` tend to `0` as `x → -∞`. -/
theorem tendsto_eLpNorm_window_atBot (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict I))
    (hsub : ∀ᶠ x in atBot, Icc (x - 1) (x - 1 + 1) ⊆ closure (I : Set ℝ)) :
    Tendsto (fun x ↦ eLpNorm f p (volume.restrict (Ioo (x - 1) (x - 1 + 1)))) atBot (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_restrict_Iio_atBot hp hf) (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hsub] with x hx
  rw [eLpNorm_restrict_eq_of_subset_closure hI (Ioo_subset_Icc_self.trans hx),
    ← Measure.restrict_restrict measurableSet_Ioo]
  refine eLpNorm_mono_measure _ (Measure.restrict_mono ?_ le_rfl)
  rw [sub_add_cancel]
  exact Ioo_subset_Iio_self

/-- **Corollary 8.9 of [brezis2011functional], the right end**: on an interval unbounded above,
`ũ(x) → 0` as `x → ∞`, for `1 ≤ p < ∞`. -/
theorem tendsto_rep_atTop (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (hunb : ¬ BddAbove (I : Set ℝ)) (u : SobolevIntervalLp 1 p I) :
    Tendsto (rep u) atTop (𝓝 0) := by
  have hcl := I.ordConnected_closure hI
  obtain ⟨y₀, hy₀⟩ : (I : Set ℝ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    exact hunb (by rw [h]; exact bddAbove_empty)
  have hsub : ∀ᶠ x in atTop, Icc x (x + 1) ⊆ closure (I : Set ℝ) := by
    filter_upwards [eventually_ge_atTop y₀] with x hx
    obtain ⟨y, hy, hxy⟩ := not_bddAbove_iff.1 hunb (x + 1)
    exact (Icc_subset_Icc hx hxy.le).trans (hcl.out (subset_closure hy₀) (subset_closure hy))
  refine tendsto_rep_of_tendsto_window hI u (c := id) ?_ ?_ ?_
  · filter_upwards [hsub] with x hx
    exact ⟨⟨le_rfl, by simp⟩, hx⟩
  · exact tendsto_eLpNorm_window_atTop hI hp (Lp.memLp (deriv u 0)) hsub
  · exact tendsto_eLpNorm_window_atTop hI hp (Lp.memLp (deriv u 1)) hsub

/-- **Corollary 8.9 of [brezis2011functional], the left end**: on an interval unbounded below,
`ũ(x) → 0` as `x → -∞`, for `1 ≤ p < ∞`. -/
theorem tendsto_rep_atBot (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (hunb : ¬ BddBelow (I : Set ℝ)) (u : SobolevIntervalLp 1 p I) :
    Tendsto (rep u) atBot (𝓝 0) := by
  have hcl := I.ordConnected_closure hI
  obtain ⟨y₀, hy₀⟩ : (I : Set ℝ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    exact hunb (by rw [h]; exact bddBelow_empty)
  have hsub : ∀ᶠ x in atBot, Icc (x - 1) (x - 1 + 1) ⊆ closure (I : Set ℝ) := by
    filter_upwards [eventually_le_atBot y₀] with x hx
    obtain ⟨y, hy, hxy⟩ := not_bddBelow_iff.1 hunb (x - 1)
    rw [sub_add_cancel]
    exact (Icc_subset_Icc hxy.le hx).trans (hcl.out (subset_closure hy) (subset_closure hy₀))
  refine tendsto_rep_of_tendsto_window hI u (c := fun x ↦ x - 1) ?_ ?_ ?_
  · filter_upwards [hsub] with x hx
    exact ⟨⟨by simp, by simp⟩, hx⟩
  · exact tendsto_eLpNorm_window_atBot hI hp (Lp.memLp (deriv u 0)) hsub
  · exact tendsto_eLpNorm_window_atBot hI hp (Lp.memLp (deriv u 1)) hsub

/-- **Corollary 8.9 of [brezis2011functional] (decay at infinity)**: on an unbounded open
interval `I` and for `1 ≤ p < ∞`, the continuous representative of `u ∈ W^{1,p}(I)` tends to `0`
as `|x| → ∞`, `x ∈ I`. Proved directly from the window estimate of Theorem 8.8 (5), whose
right-hand side tends to `0` along windows running off to infinity; no density argument. -/
theorem tendsto_rep_cocompact (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (u : SobolevIntervalLp 1 p I) :
    Tendsto (rep u) (cocompact ℝ ⊓ 𝓟 (I : Set ℝ)) (𝓝 0) := by
  rw [cocompact_eq_atBot_atTop, inf_sup_right, tendsto_sup]
  constructor
  · by_cases h : BddBelow (I : Set ℝ)
    · obtain ⟨m, hm⟩ := h
      have : atBot ⊓ 𝓟 (I : Set ℝ) = ⊥ :=
        inf_principal_eq_bot.2 ((eventually_lt_atBot m).mono fun x hx hxI ↦ (hm hxI).not_gt hx)
      rw [this]; exact tendsto_bot
    · exact (tendsto_rep_atBot hI hp h u).mono_left inf_le_left
  · by_cases h : BddAbove (I : Set ℝ)
    · obtain ⟨m, hm⟩ := h
      have : atTop ⊓ 𝓟 (I : Set ℝ) = ⊥ :=
        inf_principal_eq_bot.2 ((eventually_gt_atTop m).mono fun x hx hxI ↦ (hm hxI).not_gt hx)
      rw [this]; exact tendsto_bot
    · exact (tendsto_rep_atTop hI hp h u).mono_left inf_le_left

end SobolevIntervalLp


/-! ### Corollary 8.10: the product rule and integration by parts -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The continuous representative of `u ∈ W^{1,p}(I)` lies in `L^p(I)`. -/
theorem memLp_rep (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    MemLp (rep u) p (volume.restrict I) :=
  (Lp.memLp (deriv u 0)).ae_eq (fn_ae_eq_rep hI u)

/-- The continuous representative is continuous on `I`. -/
theorem continuousOn_rep' (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    ContinuousOn (rep u) I :=
  (continuousOn_rep hI u).mono subset_closure

/-- The Leibniz expression `u' ṽ + ũ v'` is locally integrable on `I`: each term is an `L^p`
function times a continuous one. -/
theorem locallyIntegrableOn_leibniz (hI : (I : Set ℝ).OrdConnected)
    (u v : SobolevIntervalLp 1 p I) :
    LocallyIntegrableOn (fun t ↦ deriv u 1 t * rep v t + rep u t * deriv v 1 t) I :=
  ((locallyIntegrableOn_deriv u 1).mul_continuousOn (continuousOn_rep' hI v)
    I.isOpen.isLocallyClosed).add ((locallyIntegrableOn_deriv v 1).continuousOn_mul
    (continuousOn_rep' hI u) I.isOpen.isLocallyClosed)

/-- **Corollary 8.10 of [brezis2011functional] (differentiation of a product), weak-derivative
form**: for `u, v ∈ W^{1,p}(I)`, the product `ũ ṽ` of the continuous representatives has the
weak derivative `u' ṽ + ũ v'` on `I`. The product is the primitive of that expression
(`SobolevIntervalLp.integral_deriv_mul_rep_add_mul_deriv`, Mathlib's product rule for absolutely
continuous functions), so Lemma 8.2 applies. -/
theorem hasWeakDerivOn_rep_mul (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    HasWeakDerivOn (fun t ↦ rep u t * rep v t)
      (fun t ↦ deriv u 1 t * rep v t + rep u t * deriv v 1 t) I := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · exact hasWeakDerivOn_of_eq_empty hI0 _ _
  have hy₀ := I.basePoint_mem hne
  have h0 := (locallyIntegrableOn_leibniz hI u v).hasWeakDerivOn_integral hI hy₀
    (rep u I.basePoint * rep v I.basePoint)
  refine h0.congr_ae ((ae_restrict_iff' I.isOpen.measurableSet).2 (Eventually.of_forall
    fun x hx ↦ ?_)) (EventuallyEq.refl _ _)
  have key := integral_deriv_mul_rep_add_mul_deriv hI u (η := rep v) (η' := deriv v 1)
    (subset_closure hy₀) (subset_closure hx)
    (absolutelyContinuousOnInterval_rep hI v (subset_closure hy₀) (subset_closure hx))
    (ae_deriv_rep_eq hI v)
  have e : ∫ t in I.basePoint..x, (deriv u 1 t * rep v t + rep u t * deriv v 1 t)
      = ∫ t in I.basePoint..x, (deriv v 1 t * rep u t + rep v t * deriv u 1 t) :=
    intervalIntegral.integral_congr fun t _ ↦ by ring
  change rep u I.basePoint * rep v I.basePoint
    + ∫ t in I.basePoint..x, (deriv u 1 t * rep v t + rep u t * deriv v 1 t) = rep u x * rep v x
  rw [e, key]
  ring

/-- The Leibniz expression `u' ṽ + ũ v'` lies in `L^p(I)`: a product of an `L^p` function and
an `L^∞` one (Theorem 8.8 (5)), twice. -/
theorem memLp_leibniz (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    MemLp (fun t ↦ deriv u 1 t * rep v t + rep u t * deriv v 1 t) p (volume.restrict I) :=
  ((Lp.memLp (deriv u 1)).mul (memLp_top_rep hI v)).add ((memLp_top_rep hI u).mul
    (Lp.memLp (deriv v 1)))

/-- The product of the continuous representatives lies in `L^p(I)`. -/
theorem memLp_rep_mul (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    MemLp (fun t ↦ rep u t * rep v t) p (volume.restrict I) :=
  (memLp_top_rep hI u).mul (memLp_rep hI v)

/-- **Corollary 8.10 of [brezis2011functional] (differentiation of a product)**: for
`u, v ∈ W^{1,p}(I)`, `1 ≤ p ≤ ∞`, the product `ũ ṽ` of the continuous representatives lies in
`W^{1,p}(I)`, with weak derivative `u' ṽ + ũ v'` (`SobolevIntervalLp.hasWeakDerivOn_rep_mul`). -/
theorem memSobolevIntervalLp_mul (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    MemSobolevIntervalLp (fun t ↦ rep u t * rep v t) 1 p I :=
  memSobolevIntervalLp_one_iff.2 ⟨memLp_rep_mul hI u v, _, hasWeakDerivOn_rep_mul hI u v,
    memLp_leibniz hI u v⟩

/-- **The product in `W^{1,p}(I)`**: the element `u v` whose function is `ũ ṽ` and whose weak
derivative is `u' ṽ + ũ v'`. -/
def mul (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    SobolevIntervalLp 1 p I :=
  SobolevIntervalLp.mk ![(memLp_rep_mul hI u v).toLp _, (memLp_leibniz hI u v).toLp _] fun j ↦ by
    have h0 : HasWeakIteratedDerivOn 0 ((memLp_rep_mul hI u v).toLp _)
        ((memLp_rep_mul hI u v).toLp _) I :=
      HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := I) Fact.out)
    have h1 : HasWeakIteratedDerivOn 1 ((memLp_rep_mul hI u v).toLp _)
        ((memLp_leibniz hI u v).toLp _) I :=
      (hasWeakDerivOn_rep_mul hI u v).congr_ae (memLp_rep_mul hI u v).coeFn_toLp.symm
        (memLp_leibniz hI u v).coeFn_toLp.symm
    fin_cases j
    · exact h0
    · exact h1

/-- The function of the product is `ũ ṽ`. -/
theorem fn_mul (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    fn (mul hI u v) =ᵐ[volume.restrict I] fun t ↦ rep u t * rep v t :=
  (memLp_rep_mul hI u v).coeFn_toLp

/-- The weak derivative of the product is `u' ṽ + ũ v'`. -/
theorem coeFn_deriv_mul (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    ⇑(deriv (mul hI u v) 1) =ᵐ[volume.restrict I]
      fun t ↦ deriv u 1 t * rep v t + rep u t * deriv v 1 t :=
  (memLp_leibniz hI u v).coeFn_toLp

/-- The continuous representative of the product is the product of the representatives, on the
closure of `I`. -/
theorem rep_mul (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    EqOn (rep (mul hI u v)) (fun t ↦ rep u t * rep v t) (closure (I : Set ℝ)) :=
  rep_eq_of_continuousOn hI _ ((continuousOn_rep hI u).mul (continuousOn_rep hI v)) (fn_mul hI u v)

/-- **Integration by parts in `W^{1,p}(I)`** ([brezis2011functional] Corollary 8.10, formula
(11)): for `x, y ∈ Ī`, `∫_y^x (u' ṽ + ũ v') = ũ(x) ṽ(x) - ũ(y) ṽ(y)`. -/
theorem integral_deriv_mul_add_mul_deriv (hI : (I : Set ℝ).OrdConnected)
    (u v : SobolevIntervalLp 1 p I) {x y : ℝ} (hx : x ∈ closure (I : Set ℝ))
    (hy : y ∈ closure (I : Set ℝ)) :
    ∫ t in y..x, (deriv u 1 t * rep v t + rep u t * deriv v 1 t)
      = rep u x * rep v x - rep u y * rep v y := by
  have key := integral_deriv_mul_rep_add_mul_deriv hI u (η := rep v) (η' := deriv v 1) hy hx
    (absolutelyContinuousOnInterval_rep hI v hy hx) (ae_deriv_rep_eq hI v)
  have e : ∫ t in y..x, (deriv u 1 t * rep v t + rep u t * deriv v 1 t)
      = ∫ t in y..x, (deriv v 1 t * rep u t + rep v t * deriv u 1 t) :=
    intervalIntegral.integral_congr fun t _ ↦ by ring
  rw [e, key]
  ring

/-- **Integration by parts in `W^{1,p}(I)` against an absolutely continuous factor** `ψ`:
`∫_y^x u' ψ = ũ(x) ψ(x) - ũ(y) ψ(y) - ∫_y^x ũ ψ'`, where `ψ'` is the classical derivative. -/
theorem integral_deriv_mul_eq_sub_integral_mul_deriv_of_absolutelyContinuousOnInterval
    (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {x y : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) {ψ : ℝ → ℝ}
    (hψ : AbsolutelyContinuousOnInterval ψ y x) :
    ∫ t in y..x, deriv u 1 t * ψ t
      = rep u x * ψ x - rep u y * ψ y - ∫ t in y..x, rep u t * _root_.deriv ψ t := by
  have key := integral_deriv_mul_rep_add_mul_deriv hI u (η := ψ) (η' := _root_.deriv ψ) hy hx hψ
    (Eventually.of_forall fun _ _ ↦ rfl)
  have i1 : IntervalIntegrable (fun t ↦ _root_.deriv ψ t * rep u t) volume y x :=
    hψ.intervalIntegrable_deriv.mul_continuousOn
      ((continuousOn_rep hI u).mono ((I.ordConnected_closure hI).uIcc_subset hy hx))
  have i2 : IntervalIntegrable (fun t ↦ ψ t * deriv u 1 t) volume y x :=
    (intervalIntegrable_deriv hI u 1 hy hx).continuousOn_mul hψ.continuousOn
  rw [intervalIntegral.integral_add i1 i2] at key
  have e1 : ∫ t in y..x, deriv u 1 t * ψ t = ∫ t in y..x, ψ t * deriv u 1 t :=
    intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _
  have e2 : ∫ t in y..x, rep u t * _root_.deriv ψ t = ∫ t in y..x, _root_.deriv ψ t * rep u t :=
    intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _
  rw [e1, e2]
  linarith [key]

/-- **Integration by parts in `W^{1,p}(I)` against a `C¹` factor** `ψ`, such as a coefficient of
a differential operator. -/
theorem integral_deriv_mul_contDiffOn (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {x y : ℝ} (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ 1 ψ (uIcc y x)) :
    ∫ t in y..x, deriv u 1 t * ψ t
      = rep u x * ψ x - rep u y * ψ y - ∫ t in y..x, rep u t * _root_.deriv ψ t :=
  integral_deriv_mul_eq_sub_integral_mul_deriv_of_absolutelyContinuousOnInterval hI u hx hy
    hψ.absolutelyContinuousOnInterval

/-- **Integration by parts in `W^{1,p}(I)`**, the form `∫_y^x u' ṽ = [ũ ṽ]_y^x - ∫_y^x ũ v'`. -/
theorem integral_deriv_mul_eq_sub_integral_mul_deriv (hI : (I : Set ℝ).OrdConnected)
    (u v : SobolevIntervalLp 1 p I) {x y : ℝ} (hx : x ∈ closure (I : Set ℝ))
    (hy : y ∈ closure (I : Set ℝ)) :
    ∫ t in y..x, deriv u 1 t * rep v t
      = rep u x * rep v x - rep u y * rep v y - ∫ t in y..x, rep u t * deriv v 1 t := by
  have key := integral_deriv_mul_add_mul_deriv hI u v hx hy
  have i1 : IntervalIntegrable (fun t ↦ deriv u 1 t * rep v t) volume y x :=
    (intervalIntegrable_deriv hI u 1 hy hx).mul_continuousOn
      ((continuousOn_rep hI v).mono ((I.ordConnected_closure hI).uIcc_subset hy hx))
  have i2 : IntervalIntegrable (fun t ↦ rep u t * deriv v 1 t) volume y x :=
    (intervalIntegrable_deriv hI v 1 hy hx).continuousOn_mul
      ((continuousOn_rep hI u).mono ((I.ordConnected_closure hI).uIcc_subset hy hx))
  rw [intervalIntegral.integral_add i1 i2] at key
  linarith [key]

end SobolevIntervalLp

/-! ### Corollary 8.11: the chain rule -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- **Corollary 8.11 of [brezis2011functional] (differentiation of a composition), weak-derivative
form**: for `G ∈ C¹(ℝ)` and `u ∈ W^{1,p}(I)`, `G ∘ ũ` has the weak derivative `(G' ∘ ũ) u'` on
`I`. The composition is absolutely continuous on every compact subinterval of `Ī` (`G` is
Lipschitz on the bounded range of `ũ`), its classical derivative is `G'(ũ) u'` almost everywhere
by the chain rule, and Lemma 8.2 applies to the resulting integral representation. -/
theorem hasWeakDerivOn_comp (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    HasWeakDerivOn (fun t ↦ G (rep u t)) (fun t ↦ _root_.deriv G (rep u t) * deriv u 1 t) I := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · exact hasWeakDerivOn_of_eq_empty hI0 _ _
  have hy₀ := I.basePoint_mem hne
  have hG' : Continuous (_root_.deriv G) := hG.continuous_deriv le_rfl
  have hloc : LocallyIntegrableOn (fun t ↦ _root_.deriv G (rep u t) * deriv u 1 t) I :=
    (locallyIntegrableOn_deriv u 1).continuousOn_mul
      (hG'.comp_continuousOn (continuousOn_rep' hI u)) I.isOpen.isLocallyClosed
  have h0 := hloc.hasWeakDerivOn_integral hI hy₀ (G (rep u I.basePoint))
  refine h0.congr_ae ((ae_restrict_iff' I.isOpen.measurableSet).2 (Eventually.of_forall
    fun x hx ↦ ?_)) (EventuallyEq.refl _ _)
  -- `G ∘ ũ` is absolutely continuous on `[y₀, x]`
  set M := embeddingConst p I * ‖u‖ with hM
  obtain ⟨K, hK⟩ := (hG.contDiffOn (s := Icc (-M) M)).exists_lipschitzOnWith one_ne_zero
    (convex_Icc _ _) isCompact_Icc
  have hmaps : MapsTo (rep u) (uIcc I.basePoint x) (Icc (-M) M) := fun t ht ↦ by
    have := abs_rep_le hI u ((I.ordConnected_closure hI).uIcc_subset (subset_closure hy₀)
      (subset_closure hx) ht)
    rw [hM]
    exact ⟨by linarith [neg_abs_le (rep u t)], by linarith [le_abs_self (rep u t)]⟩
  have hacu := absolutelyContinuousOnInterval_rep hI u (subset_closure hy₀) (subset_closure hx)
  have hac : AbsolutelyContinuousOnInterval (G ∘ rep u) I.basePoint x :=
    hK.comp_absolutelyContinuousOnInterval hmaps hacu
  have key := hac.integral_deriv_eq_sub
  change G (rep u I.basePoint) + ∫ t in I.basePoint..x, _root_.deriv G (rep u t) * deriv u 1 t
    = G (rep u x)
  have e : ∫ t in I.basePoint..x, _root_.deriv G (rep u t) * deriv u 1 t
      = ∫ t in I.basePoint..x, _root_.deriv (G ∘ rep u) t := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_restrict hI ((ae_restrict_iff' I.isOpen.measurableSet).2
      (ae_deriv_rep_eq hI u)) (subset_closure hy₀) (subset_closure hx),
      hacu.ae_differentiableAt] with t h1 h2 ht
    have hd : DifferentiableAt ℝ (rep u) t := h2 (uIoc_subset_uIcc ht)
    rw [← h1 ht]
    exact (((hG.differentiable one_ne_zero) (rep u t)).hasDerivAt.comp t hd.hasDerivAt).deriv.symm
  rw [e, key]
  simp only [Function.comp_apply]
  ring

/-- `G'(ũ) u'` lies in `L^p(I)` for `G ∈ C¹`: `G' ∘ ũ` is bounded (`ũ` is, Theorem 8.8 (5)). -/
theorem memLp_deriv_comp (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    MemLp (fun t ↦ _root_.deriv G (rep u t) * deriv u 1 t) p (volume.restrict I) := by
  have hG' : Continuous (_root_.deriv G) := hG.continuous_deriv le_rfl
  set M := embeddingConst p I * ‖u‖ with hM
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hG'.continuousOn (s := Icc (-M) M))
  have hmem : ∀ t ∈ (I : Set ℝ), rep u t ∈ Icc (-M) M := fun t ht ↦ by
    have := abs_rep_le hI u (subset_closure ht)
    rw [hM]
    exact ⟨by linarith [neg_abs_le (rep u t)], by linarith [le_abs_self (rep u t)]⟩
  have hbdd : MemLp (fun t ↦ _root_.deriv G (rep u t)) ⊤ (volume.restrict I) :=
    memLp_top_of_bound ((hG'.comp_continuousOn (continuousOn_rep' hI u)).aestronglyMeasurable
      I.isOpen.measurableSet) C ((ae_restrict_iff' I.isOpen.measurableSet).2
      (Eventually.of_forall fun t ht ↦ hC _ (hmem t ht)))
  exact hbdd.mul (Lp.memLp (deriv u 1))

/-- `G ∘ ũ` lies in `L^p(I)` when `G ∈ C¹` and `G(0) = 0`: `|G(s)| ≤ K |s|` on the bounded range
of `ũ`, so `|G ∘ ũ| ≤ K |ũ|`. This is where `G(0) = 0` is used (footnote 9 of
[brezis2011functional]). -/
theorem memLp_comp (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {G : ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) :
    MemLp (fun t ↦ G (rep u t)) p (volume.restrict I) := by
  set M := embeddingConst p I * ‖u‖ with hM
  have hM0 : 0 ≤ M := mul_nonneg (embeddingConst_pos p I).le (norm_nonneg _)
  obtain ⟨K, hK⟩ := (hG.contDiffOn (s := Icc (-M) M)).exists_lipschitzOnWith one_ne_zero
    (convex_Icc _ _) isCompact_Icc
  have hmem : ∀ t ∈ (I : Set ℝ), rep u t ∈ Icc (-M) M := fun t ht ↦ by
    have := abs_rep_le hI u (subset_closure ht)
    rw [hM]
    exact ⟨by linarith [neg_abs_le (rep u t)], by linarith [le_abs_self (rep u t)]⟩
  refine ((memLp_rep hI u).const_smul (K : ℝ)).of_le
    ((hG.continuous.comp_continuousOn (continuousOn_rep' hI u)).aestronglyMeasurable
      I.isOpen.measurableSet) ((ae_restrict_iff' I.isOpen.measurableSet).2
      (Eventually.of_forall fun t ht ↦ ?_))
  have h := hK.dist_le_mul (rep u t) (hmem t ht) 0 ⟨by linarith, hM0⟩
  rw [hG0, dist_zero_right, dist_zero_right] at h
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K.coe_nonneg)] using h

/-- **Corollary 8.11 of [brezis2011functional] (differentiation of a composition)**: for
`G ∈ C¹(ℝ)` with `G(0) = 0` and `u ∈ W^{1,p}(I)`, `1 ≤ p ≤ ∞`, the composition `G ∘ ũ` lies in
`W^{1,p}(I)` and `(G ∘ ũ)' = (G' ∘ ũ) u'`. The hypothesis `G(0) = 0` is only used to put `G ∘ ũ`
in `L^p(I)` on an unbounded interval (footnote 9); `memSobolevIntervalLp_comp_of_bounded` drops
it for a bounded interval. -/
theorem memSobolevIntervalLp_comp (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) :
    MemSobolevIntervalLp (fun t ↦ G (rep u t)) 1 p I ∧
      HasWeakDerivOn (fun t ↦ G (rep u t)) (fun t ↦ _root_.deriv G (rep u t) * deriv u 1 t) I :=
  ⟨memSobolevIntervalLp_one_iff.2 ⟨memLp_comp hI u hG hG0, _, hasWeakDerivOn_comp hI u hG,
    memLp_deriv_comp hI u hG⟩, hasWeakDerivOn_comp hI u hG⟩

/-- **Corollary 8.11 on a bounded interval, without `G(0) = 0`** (footnote 9 of
[brezis2011functional]): for `G ∈ C¹(ℝ)` and `u ∈ W^{1,p}(a, b)`, `G ∘ ũ ∈ W^{1,p}(a, b)` with
`(G ∘ ũ)' = (G' ∘ ũ) u'`. -/
theorem memSobolevIntervalLp_comp_of_bounded {a b : ℝ} (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    MemSobolevIntervalLp (fun t ↦ G (rep u t)) 1 p (Opens.Ioo a b) ∧
      HasWeakDerivOn (fun t ↦ G (rep u t)) (fun t ↦ _root_.deriv G (rep u t) * deriv u 1 t)
        (Opens.Ioo a b) := by
  have hmem : MemLp (fun t ↦ G (rep u t)) p (volume.restrict (Ioo a b)) := by
    have : IsFiniteMeasure (volume.restrict (Ioo a b)) := ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top⟩
    exact (hG.continuous.comp_continuousOn
      (continuousOn_rep_Icc hab u)).memLp_top_restrict_Ioo.mono_exponent le_top
  exact ⟨memSobolevIntervalLp_one_iff.2 ⟨hmem, _, hasWeakDerivOn_comp (ordConnected_coe_Ioo a b)
    u hG, memLp_deriv_comp (ordConnected_coe_Ioo a b) u hG⟩,
    hasWeakDerivOn_comp (ordConnected_coe_Ioo a b) u hG⟩

end SobolevIntervalLp


/-! ### Remark 11: equivalent norms on a bounded interval -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

/-- **Theorem 8.8 (5) on a bounded interval with an `L^q` norm of the function** (Remark 11 of
[brezis2011functional], Chapter 8): for `a < b`, `1 ≤ p, q ≤ ∞`, `u ∈ W^{1,p}(a, b)` and
`x ∈ [a, b]`, `|ũ(x)| ≤ (b - a)^{-1/q} ‖u‖_{L^q} + (b - a)^{1 - 1/p} ‖u'‖_{L^p}`. -/
theorem abs_rep_le_of_bounded' (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    |rep u x| ≤ (b - a) ^ (-q.toReal⁻¹) * ‖toLpOfBounded p hab q u‖
      + (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖ := by
  have h := enorm_rep_le_of_Icc_subset' (ordConnected_coe_Ioo a b) u q hab
    (by rw [closure_coe_Ioo hab]) hx
  have e0 : eLpNorm (fn u) q (volume.restrict (Ioo a b)) = ‖toLpOfBounded p hab q u‖ₑ := by
    rw [Lp.enorm_def]
    exact (eLpNorm_congr_ae (coeFn_toLpOfBounded hab q u)).symm
  have e1 : eLpNorm (deriv u 1) p (volume.restrict (Ioo a b)) = ‖deriv u 1‖ₑ := by
    rw [Lp.enorm_def]; rfl
  rw [e0, e1] at h
  have hba : 0 < b - a := sub_pos.2 hab
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ofReal_rpow_mul_enorm_ne_top hba _ _,
    ofReal_rpow_mul_enorm_ne_top hba _ _⟩) h
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_add (ofReal_rpow_mul_enorm_ne_top hba _ _)
      (ofReal_rpow_mul_enorm_ne_top hba _ _),
    toReal_ofReal_rpow_mul_enorm hba.le, toReal_ofReal_rpow_mul_enorm hba.le] at this

/-- **Remark 11 of [brezis2011functional], Chapter 8, first half**: on a bounded interval the
`W^{1,p}` norm is controlled by `‖u'‖_p` and any `L^q` norm of `u`:
`‖u‖_{W^{1,p}} ≤ (b - a)^{1/p} ((b - a)^{-1/q} ‖u‖_q + (b - a)^{1 - 1/p} ‖u'‖_p) + ‖u'‖_p`. -/
theorem norm_le_of_bounded' (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖u‖ ≤ (b - a) ^ p.toReal⁻¹ * ((b - a) ^ (-q.toReal⁻¹) * ‖toLpOfBounded p hab q u‖
      + (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖) + ‖deriv u 1‖ := by
  have hba : 0 < b - a := sub_pos.2 hab
  refine (norm_le_sum_norm_deriv u).trans ?_
  rw [Fin.sum_univ_two]
  refine add_le_add ?_ le_rfl
  rw [Lp.norm_def]
  have hC0 : 0 ≤ (b - a) ^ (-q.toReal⁻¹) * ‖toLpOfBounded p hab q u‖
      + (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖ := by positivity
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (Ioo a b)) (p := p)
    (Lp.aestronglyMeasurable (deriv u 0))
    (C := (b - a) ^ (-q.toReal⁻¹) * ‖toLpOfBounded p hab q u‖
      + (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖) ?_
  · rw [Measure.restrict_apply_univ, Real.volume_Ioo] at h
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) h).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hba.le,
      ENNReal.toReal_ofReal hC0]
  · filter_upwards [fn_ae_eq_rep (ordConnected_coe_Ioo a b) u, ae_restrict_mem measurableSet_Ioo]
      with x hx1 hx2
    rw [deriv_zero, hx1, Real.norm_eq_abs]
    exact abs_rep_le_of_bounded' hab q u (Ioo_subset_Icc_self hx2)

/-- **Remark 11 of [brezis2011functional], Chapter 8, second half**:
`‖u'‖_p + ‖u‖_q ≤ (1 + (b - a)^{1/q} C) ‖u‖_{W^{1,p}}` with `C` the embedding constant of
Theorem 8.8 (5). -/
theorem norm_deriv_add_norm_toLpOfBounded_le (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖deriv u 1‖ + ‖toLpOfBounded p hab q u‖
      ≤ (1 + (b - a) ^ q.toReal⁻¹ * embeddingConst p (Opens.Ioo a b)) * ‖u‖ := by
  rw [add_mul, one_mul]
  exact add_le_add (norm_deriv_le u 1) (norm_toLpOfBoundedₗ_le hab q u)

/-- **Remark 11 of [brezis2011functional], Chapter 8**: on a bounded interval `(a, b)`, for every
`1 ≤ q ≤ ∞`, the quantity `‖u'‖_p + ‖u‖_q` is a norm on `W^{1,p}(a, b)` equivalent to the
`W^{1,p}` norm. -/
theorem norm_equiv_of_bounded (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u : SobolevIntervalLp 1 p (Opens.Ioo a b),
      ‖u‖ ≤ C₁ * (‖deriv u 1‖ + ‖toLpOfBounded p hab q u‖) ∧
        ‖deriv u 1‖ + ‖toLpOfBounded p hab q u‖ ≤ C₂ * ‖u‖ := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hemb := embeddingConst_pos p (Opens.Ioo a b)
  refine ⟨(b - a) ^ p.toReal⁻¹ * ((b - a) ^ (-q.toReal⁻¹) + (b - a) ^ (1 - p.toReal⁻¹)) + 1,
    1 + (b - a) ^ q.toReal⁻¹ * embeddingConst p (Opens.Ioo a b), by positivity, by positivity,
    fun u ↦ ⟨?_, norm_deriv_add_norm_toLpOfBounded_le hab q u⟩⟩
  refine (norm_le_of_bounded' hab q u).trans ?_
  have hL : 0 ≤ (b - a) ^ p.toReal⁻¹ := by positivity
  have hA : 0 ≤ (b - a) ^ (-q.toReal⁻¹) := by positivity
  have hB : 0 ≤ (b - a) ^ (1 - p.toReal⁻¹) := by positivity
  have hN := norm_nonneg (toLpOfBounded p hab q u)
  have hD := norm_nonneg (deriv u 1)
  nlinarith [mul_nonneg (mul_nonneg hL hA) hD, mul_nonneg (mul_nonneg hL hB) hN]

end SobolevIntervalLp


/-! ### Theorem 8.8 (5): the book's inequality (8) -/

section AbsRpow

/-- `t ↦ |t|^r`, `r ≥ 1`, is Lipschitz on `[-M, M]` with constant `r M^{r-1}`. -/
theorem lipschitzOnWith_abs_rpow {r M : ℝ} (hr : 1 ≤ r) (hM : 0 ≤ M) :
    LipschitzOnWith ((r * M ^ (r - 1)).toNNReal * 1) (fun t : ℝ ↦ |t| ^ r) (Icc (-M) M) := by
  have h1 : LipschitzOnWith (r * M ^ (r - 1)).toNNReal (fun t : ℝ ↦ t ^ r) (Icc 0 M) := by
    refine (convex_Icc 0 M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun t ↦ r * t ^ (r - 1))
      (fun t _ ↦ (Real.hasDerivAt_rpow_const (Or.inr hr)).hasDerivWithinAt) fun t ht ↦ ?_
    have hC : 0 ≤ r * M ^ (r - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg hM _)
    rw [Real.le_toNNReal_iff_coe_le hC, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1 _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 (by linarith)) (by linarith)
  have h2 : LipschitzOnWith 1 (fun t : ℝ ↦ |t|) (Icc (-M) M) :=
    (lipschitzWith_one_norm (E := ℝ)).lipschitzOnWith
  exact h1.comp h2 fun t ht ↦ ⟨abs_nonneg t, abs_le.2 ht⟩

/-- `|t|^r → 0`-type continuity: `t ↦ ‖|t|^r‖ₑ` is continuous. -/
theorem continuous_enorm_abs_rpow {r : ℝ} (hr : 0 ≤ r) :
    Continuous fun t : ℝ ↦ ‖|t| ^ r‖ₑ :=
  continuous_enorm.comp ((Real.continuous_rpow_const hr).comp continuous_abs)

end AbsRpow

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- The cocompact filter restricted to an unbounded set is nontrivial. -/
theorem neBot_cocompact_inf_principal (hunb : ¬ Bornology.IsBounded (I : Set ℝ)) :
    (cocompact ℝ ⊓ 𝓟 (I : Set ℝ)).NeBot :=
  Filter.neBot_iff.2 fun h ↦ hunb (Bornology.isBounded_def.2
    ((Metric.cobounded_eq_cocompact (α := ℝ)) ▸ Filter.inf_principal_eq_bot.1 h))

/-- **The book's inequality (8), in `ℝ≥0∞`**: for an unbounded interval `I`, `1 ≤ p < ∞`,
`u ∈ W^{1,p}(I)` and `x ∈ Ī`, `|ũ(x)|^p ≤ p ‖u‖_p^{p-1} ‖u'‖_p`. The function `w = |ũ|^p` is
absolutely continuous on compact subintervals (`|·|^p` is Lipschitz on bounded sets), with
`|w'| ≤ p |ũ|^{p-1} |u'|` almost everywhere, so `|w(x) - w(y)| ≤ p ∫_I |ũ|^{p-1} |u'|`, which
Hölder's inequality bounds by `p ‖u‖_p^{p-1} ‖u'‖_p`; and `w(y) → 0` as `y → ∞` in `I`
(Corollary 8.9). -/
theorem enorm_abs_rep_rpow_le (hI : (I : Set ℝ).OrdConnected)
    (hunb : ¬ Bornology.IsBounded (I : Set ℝ)) (hp : p ≠ ⊤) (u : SobolevIntervalLp 1 p I)
    {x : ℝ} (hx : x ∈ closure (I : Set ℝ)) :
    ‖|rep u x| ^ p.toReal‖ₑ
      ≤ ENNReal.ofReal p.toReal * ‖deriv u 0‖ₑ ^ (p.toReal - 1) * ‖deriv u 1‖ₑ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hr : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
    rwa [ENNReal.toReal_one] at this
  have hr0 : 0 < p.toReal := by linarith
  -- the Hölder bound on the increments of `w = |ũ|^p`
  have hB : ∀ y ∈ closure (I : Set ℝ), ‖|rep u y| ^ p.toReal - |rep u x| ^ p.toReal‖ₑ
      ≤ ENNReal.ofReal p.toReal * ‖deriv u 0‖ₑ ^ (p.toReal - 1) * ‖deriv u 1‖ₑ := by
    intro y hy
    -- `w` is absolutely continuous on `[x, y]`
    obtain ⟨M, hM0, hM⟩ : ∃ M, 0 ≤ M ∧ ∀ t ∈ closure (I : Set ℝ), rep u t ∈ Icc (-M) M :=
      ⟨embeddingConst p I * ‖u‖, mul_nonneg (embeddingConst_pos p I).le (norm_nonneg _),
        fun t ht ↦ by
        have := abs_rep_le hI u ht
        exact ⟨by linarith [neg_abs_le (rep u t)], by linarith [le_abs_self (rep u t)]⟩⟩
    have hmaps : MapsTo (rep u) (uIcc x y) (Icc (-M) M) := fun t ht ↦
      hM t ((I.ordConnected_closure hI).uIcc_subset hx hy ht)
    have hacu := absolutelyContinuousOnInterval_rep hI u hx hy
    have hac : AbsolutelyContinuousOnInterval ((fun t : ℝ ↦ |t| ^ p.toReal) ∘ rep u) x y :=
      (lipschitzOnWith_abs_rpow hr hM0).comp_absolutelyContinuousOnInterval hmaps hacu
    -- the derivative of `w` is bounded by `p |ũ|^{p-1} |u'|` almost everywhere on `[x, y]`
    have hderiv : ∀ᵐ t, t ∈ Ι x y → ‖_root_.deriv ((fun t : ℝ ↦ |t| ^ p.toReal) ∘ rep u) t‖ₑ
        ≤ ENNReal.ofReal p.toReal * ‖rep u t‖ₑ ^ (p.toReal - 1) * ‖deriv u 1 t‖ₑ := by
      filter_upwards [ae_uIoc_of_ae_restrict hI ((ae_restrict_iff' I.isOpen.measurableSet).2
        (ae_deriv_rep_eq hI u)) hx hy, hacu.ae_differentiableAt] with t h1 h2 ht
      have hd : DifferentiableAt ℝ (rep u) t := h2 (uIoc_subset_uIcc ht)
      by_cases h0 : rep u t = 0
      · -- `w ≥ 0 = w t`: a minimum, so `w' t = 0` (or `w` is not differentiable there)
        have hmin : IsLocalMin ((fun t : ℝ ↦ |t| ^ p.toReal) ∘ rep u) t :=
          Eventually.of_forall fun s ↦ by
            simp only [Function.comp_apply, h0, abs_zero, Real.zero_rpow hr0.ne']
            positivity
        rw [hmin.deriv_eq_zero, enorm_zero]
        exact zero_le
      · -- the chain rule at a point where `ũ t ≠ 0`
        have h5 : HasDerivAt (rep u) (deriv u 1 t) t := by rw [← h1 ht]; exact hd.hasDerivAt
        have h3 : HasDerivAt (fun s : ℝ ↦ s ^ p.toReal)
            (p.toReal * |rep u t| ^ (p.toReal - 1)) |rep u t| :=
          Real.hasDerivAt_rpow_const (Or.inl (abs_ne_zero.2 h0))
        have key : ∀ σ : ℝ, |σ| = 1 → HasDerivAt (fun s : ℝ ↦ |s|) σ (rep u t) →
            ‖_root_.deriv ((fun t : ℝ ↦ |t| ^ p.toReal) ∘ rep u) t‖ₑ
              ≤ ENNReal.ofReal p.toReal * ‖rep u t‖ₑ ^ (p.toReal - 1) * ‖deriv u 1 t‖ₑ := by
          intro σ hσ h4
          have h34 := h3.comp (rep u t) h4
          have hd' := h34.comp t h5
          change ‖_root_.deriv (((fun s : ℝ ↦ s ^ p.toReal) ∘ fun s : ℝ ↦ |s|) ∘ rep u) t‖ₑ ≤ _
          rw [hd'.deriv, enorm_mul, enorm_mul, enorm_mul, Real.enorm_of_nonneg hr0.le,
            Real.enorm_rpow_of_nonneg (abs_nonneg _) (by linarith), Real.enorm_abs,
            Real.enorm_eq_ofReal_abs σ, hσ, ENNReal.ofReal_one, mul_one]
        rcases Ne.lt_or_gt h0 with hneg | hpos
        · exact key (-1) (by simp) (hasDerivAt_abs_neg hneg)
        · exact key 1 (by simp) (hasDerivAt_abs_pos hpos)
    -- the fundamental theorem of calculus and Hölder's inequality
    have hsub : Ι x y ⊆ closure (I : Set ℝ) :=
      uIoc_subset_uIcc.trans ((I.ordConnected_closure hI).uIcc_subset hx hy)
    have hcl : volume.restrict (closure (I : Set ℝ)) = volume.restrict I :=
      Measure.restrict_congr_set (ae_eq_set.2 ⟨I.volume_closure_diff_eq_zero hI,
        by rw [sdiff_eq_empty.2 subset_closure, measure_empty]⟩)
    have hmeas0 : AEMeasurable (fun t ↦ ‖rep u t‖ₑ ^ (p.toReal - 1)) (volume.restrict I) :=
      (memLp_rep hI u).aestronglyMeasurable.aemeasurable.enorm.pow_const _
    have hmeas1 : AEMeasurable (fun t ↦ ‖deriv u 1 t‖ₑ) (volume.restrict I) :=
      (Lp.aestronglyMeasurable (deriv u 1)).aemeasurable.enorm
    have e0 : eLpNorm (rep u) p (volume.restrict I) = ‖deriv u 0‖ₑ := by
      rw [Lp.enorm_def]
      exact (eLpNorm_congr_ae (fn_ae_eq_rep hI u)).symm
    have e1 : eLpNorm (deriv u 1) p (volume.restrict I) = ‖deriv u 1‖ₑ := by rw [Lp.enorm_def]
    calc ‖|rep u y| ^ p.toReal - |rep u x| ^ p.toReal‖ₑ
        = ‖∫ t in x..y, _root_.deriv ((fun t : ℝ ↦ |t| ^ p.toReal) ∘ rep u) t‖ₑ := by
          rw [hac.integral_deriv_eq_sub]; rfl
      _ ≤ ∫⁻ t in Ι x y, ‖_root_.deriv ((fun t : ℝ ↦ |t| ^ p.toReal) ∘ rep u) t‖ₑ := by
          rw [← ofReal_norm, intervalIntegral.norm_integral_eq_norm_integral_uIoc, ofReal_norm]
          exact enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ι x y, ENNReal.ofReal p.toReal * ‖rep u t‖ₑ ^ (p.toReal - 1)
            * ‖deriv u 1 t‖ₑ :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_uIoc).2 hderiv)
      _ ≤ ∫⁻ t in closure (I : Set ℝ), ENNReal.ofReal p.toReal * ‖rep u t‖ₑ ^ (p.toReal - 1)
            * ‖deriv u 1 t‖ₑ := lintegral_mono_set hsub
      _ = ∫⁻ t in I, ENNReal.ofReal p.toReal * ‖rep u t‖ₑ ^ (p.toReal - 1)
            * ‖deriv u 1 t‖ₑ := by rw [hcl]
      _ = ENNReal.ofReal p.toReal * ∫⁻ t in I, ‖rep u t‖ₑ ^ (p.toReal - 1) * ‖deriv u 1 t‖ₑ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp only [mul_assoc]
      _ ≤ ENNReal.ofReal p.toReal * (‖deriv u 0‖ₑ ^ (p.toReal - 1) * ‖deriv u 1‖ₑ) := by
          gcongr
          rcases hr.eq_or_lt with hr1 | hr1
          · -- `p = 1`: no Hölder is needed
            rw [← hr1, sub_self]
            simp only [ENNReal.rpow_zero, one_mul]
            rw [← e1, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
              (Lp.aestronglyMeasurable _), ← hr1]
            simp only [ENNReal.rpow_one, one_div, inv_one]
            exact le_rfl
          · -- `p > 1`: Hölder with the exponents `p/(p - 1)` and `p`
            have hconj := (Real.HolderConjugate.conjExponent hr1).symm
            have hq : Real.conjExponent p.toReal = p.toReal / (p.toReal - 1) := rfl
            refine (ENNReal.lintegral_mul_le_Lp_mul_Lq _ hconj hmeas0 hmeas1).trans (le_of_eq ?_)
            rw [← e0, ← e1, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
              (memLp_rep hI u).aestronglyMeasurable, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
              (Lp.aestronglyMeasurable _), ← ENNReal.rpow_mul, hq]
            congr 2
            · refine lintegral_congr fun t ↦ ?_
              rw [← ENNReal.rpow_mul]
              congr 1
              field_simp
            · field_simp
      _ = _ := by ring
  -- the tail: `w(y) → 0` as `y → ∞` in `I`
  have hne := neBot_cocompact_inf_principal (I := I) hunb
  have hlim : Tendsto (fun y ↦ ‖|rep u y| ^ p.toReal‖ₑ) (cocompact ℝ ⊓ 𝓟 (I : Set ℝ)) (𝓝 0) := by
    have := ((continuous_enorm_abs_rpow hr0.le).tendsto 0).comp (tendsto_rep_cocompact hI hp u)
    have h0 : ‖|(0 : ℝ)| ^ p.toReal‖ₑ = 0 := by simp [Real.zero_rpow hr0.ne']
    rw [h0] at this
    exact this
  have hlim' : Tendsto (fun y ↦ ENNReal.ofReal p.toReal * ‖deriv u 0‖ₑ ^ (p.toReal - 1)
      * ‖deriv u 1‖ₑ + ‖|rep u y| ^ p.toReal‖ₑ) (cocompact ℝ ⊓ 𝓟 (I : Set ℝ))
      (𝓝 (ENNReal.ofReal p.toReal * ‖deriv u 0‖ₑ ^ (p.toReal - 1) * ‖deriv u 1‖ₑ)) := by
    have := hlim.const_add (ENNReal.ofReal p.toReal * ‖deriv u 0‖ₑ ^ (p.toReal - 1)
      * ‖deriv u 1‖ₑ)
    rwa [add_zero] at this
  refine ge_of_tendsto hlim' ?_
  · rw [eventually_inf_principal]
    refine Eventually.of_forall fun y hy ↦ ?_
    calc ‖|rep u x| ^ p.toReal‖ₑ
        = ‖(|rep u x| ^ p.toReal - |rep u y| ^ p.toReal) + |rep u y| ^ p.toReal‖ₑ := by
          rw [sub_add_cancel]
      _ ≤ ‖|rep u x| ^ p.toReal - |rep u y| ^ p.toReal‖ₑ + ‖|rep u y| ^ p.toReal‖ₑ :=
          enorm_add_le _ _
      _ ≤ _ := by
          gcongr
          rw [← enorm_neg, neg_sub]
          exact hB y (subset_closure hy)


/-- **The book's inequality (8)** ([brezis2011functional], proof of Theorem 8.8 (5)): for an
unbounded interval `I`, `1 ≤ p < ∞`, `u ∈ W^{1,p}(I)` and `x ∈ Ī`,
`|ũ(x)|^p ≤ p ‖u‖_p^{p-1} ‖u'‖_p`. -/
theorem abs_rep_pow_le (hI : (I : Set ℝ).OrdConnected) (hunb : ¬ Bornology.IsBounded (I : Set ℝ))
    (hp : p ≠ ⊤) (u : SobolevIntervalLp 1 p I) {x : ℝ} (hx : x ∈ closure (I : Set ℝ)) :
    |rep u x| ^ p.toReal ≤ p.toReal * ‖deriv u 0‖ ^ (p.toReal - 1) * ‖deriv u 1‖ := by
  have hr : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
    rwa [ENNReal.toReal_one] at this
  have h := enorm_abs_rep_rpow_le hI hunb hp u hx
  rw [Real.enorm_of_nonneg (by positivity), ← ofReal_norm, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith),
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

end SobolevIntervalLp

/-! ### Helly's selection theorem -/

section Helly

/-- **Pointwise extraction on a countable set**: a sequence of real functions uniformly bounded on
a countable set `s` has a subsequence converging at every point of `s` — the diagonal argument,
here as the sequential compactness of the countable product `s → [-M, M]`. -/
theorem exists_subseq_forall_tendsto_of_countable {s : Set ℝ} (hs : s.Countable)
    {f : ℕ → ℝ → ℝ} {M : ℝ} (hbdd : ∀ n, ∀ x ∈ s, |f n x| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ x ∈ s, ∃ l, Tendsto (fun n ↦ f (φ n) x) atTop (𝓝 l) := by
  have : Countable s := hs.to_subtype
  obtain ⟨L, φ, hφ, hL⟩ := SeqCompactSpace.tendsto_subseq
    (fun n (x : s) ↦ (⟨f n x, abs_le.1 (hbdd n x x.2)⟩ : Icc (-M) M))
  refine ⟨φ, hφ, fun x hx ↦ ⟨(L ⟨x, hx⟩ : ℝ), ?_⟩⟩
  exact (continuous_subtype_val.tendsto _).comp (tendsto_pi_nhds.1 hL ⟨x, hx⟩)

/-- **Helly's selection theorem for monotone functions**: a sequence of functions nondecreasing
and uniformly bounded on `[a, b]` has a subsequence converging at every point of `[a, b]`.
Extract (`exists_subseq_forall_tendsto_of_countable`) a subsequence converging on the rationals of
`[a, b]` and at the endpoints, with limit `l`; the envelope `g x = inf {l r : r rational, x < r}`
is nondecreasing, so has countably many discontinuities (`Monotone.countable_not_continuousAt`);
extract again on these; at every other `x ∈ (a, b)` the subsequence converges to `g x`, squeezed
between its values at rationals `q < x < r`. -/
theorem exists_subseq_forall_tendsto_of_forall_monotoneOn {f : ℕ → ℝ → ℝ} {a b M : ℝ}
    (hmono : ∀ n, MonotoneOn (f n) (Icc a b)) (hbdd : ∀ n, ∀ x ∈ Icc a b, |f n x| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ x ∈ Icc a b, ∃ l, Tendsto (fun n ↦ f (φ n) x) atTop (𝓝 l) := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨id, strictMono_id, fun x hx ↦
      absurd hx (by rw [Icc_eq_empty_of_lt hba]; exact notMem_empty x)⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hbdd 0 a (left_mem_Icc.2 hab))
  -- the rationals of `[a, b]` and the endpoints
  obtain ⟨D₀, hD₀⟩ : ∃ D : Set ℝ, D = Icc a b ∩ (range ((↑) : ℚ → ℝ) ∪ {a, b}) := ⟨_, rfl⟩
  have hD₀c : D₀.Countable := hD₀ ▸
    ((countable_range _).union ((countable_singleton b).insert a)).mono inter_subset_right
  have hD₀I : D₀ ⊆ Icc a b := hD₀ ▸ inter_subset_left
  obtain ⟨φ₁, hφ₁, h₁⟩ := exists_subseq_forall_tendsto_of_countable hD₀c (f := f)
    fun n x hx ↦ hbdd n x (hD₀I hx)
  choose! l hl using h₁
  have hlM : ∀ x ∈ D₀, |l x| ≤ M := fun x hx ↦ abs_le.2
    ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds (hl x hx) fun n ↦
      (abs_le.1 (hbdd _ x (hD₀I hx))).1,
      le_of_tendsto_of_tendsto' (hl x hx) tendsto_const_nhds fun n ↦
      (abs_le.1 (hbdd _ x (hD₀I hx))).2⟩
  -- the nondecreasing envelope `g`
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun x ↦ sInf (l '' {r ∈ D₀ | x < r} ∪ {M}) := ⟨_, rfl⟩
  have hbelow : ∀ x, BddBelow (l '' {r ∈ D₀ | x < r} ∪ {M}) := fun x ↦ ⟨-M, by
    rintro y (⟨r, hr, rfl⟩ | rfl)
    · exact (abs_le.1 (hlM r hr.1)).1
    · linarith⟩
  have hg_mono : Monotone g := by
    intro x y hxy
    simp only [hg]
    refine csInf_le_csInf (hbelow x) ⟨M, Or.inr rfl⟩ ?_
    rintro z (⟨r, hr, rfl⟩ | rfl)
    · exact Or.inl ⟨r, ⟨hr.1, hxy.trans_lt hr.2⟩, rfl⟩
    · exact Or.inr rfl
  -- the second extraction, on the rationals and the discontinuities of `g`
  obtain ⟨D, hD⟩ : ∃ D : Set ℝ, D = (D₀ ∪ {x | ¬ContinuousAt g x}) ∩ Icc a b := ⟨_, rfl⟩
  have hDc : D.Countable := hD ▸
    (hD₀c.union hg_mono.countable_not_continuousAt).mono inter_subset_left
  obtain ⟨φ₂, hφ₂, h₂⟩ := exists_subseq_forall_tendsto_of_countable hDc
    (f := fun n ↦ f (φ₁ n)) (M := M) fun n x hx ↦ hbdd _ x (by rw [hD] at hx; exact hx.2)
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun x hx ↦ ?_⟩
  by_cases hxD : x ∈ D
  · exact h₂ x hxD
  -- `x` is an interior point of continuity of `g`, and the subsequence converges to `g x` there
  have hxD₀ : x ∉ D₀ := fun h ↦ hxD (hD ▸ ⟨Or.inl h, hx⟩)
  have hcont : ContinuousAt g x := by_contra fun h ↦ hxD (hD ▸ ⟨Or.inr h, hx⟩)
  have hxa : a < x := lt_of_le_of_ne hx.1 fun h ↦
    hxD₀ (hD₀ ▸ ⟨hx, Or.inr (by rw [← h]; exact mem_insert a {b})⟩)
  have hxb : x < b := lt_of_le_of_ne hx.2 fun h ↦
    hxD₀ (hD₀ ▸ ⟨hx, Or.inr (by rw [h]; exact mem_insert_of_mem a (mem_singleton b))⟩)
  refine ⟨g x, tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩⟩
  · -- from below: two rationals `q < q' < x` close to `x`, `c < g q ≤ l q'`
    obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hcont (g x - c) (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (x - δ) a < x from max_lt (by linarith) hxa)
    obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn hq2
    have hq'D : (q' : ℝ) ∈ D₀ := hD₀ ▸
      ⟨⟨(le_max_right _ _).trans (hq1.trans hq'1).le, hq'2.le.trans hxb.le⟩, Or.inl ⟨q', rfl⟩⟩
    have hgq : c < g q := by
      have := hδg (show dist (q : ℝ) x < δ by
        rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [le_max_left (x - δ) a])
      rw [Real.dist_eq, abs_sub_lt_iff] at this
      linarith [this.2]
    have hgl : g q ≤ l q' := by
      simp only [hg]
      exact csInf_le (hbelow q) (Or.inl ⟨q', ⟨hq'D, hq'1⟩, rfl⟩)
    have hev : ∀ᶠ n in atTop, c < f (φ₁ n) q' :=
      (hl q' hq'D).eventually (lt_mem_nhds (hgq.trans_le hgl))
    filter_upwards [hφ₂.tendsto_atTop.eventually hev] with n hn
    exact hn.trans_le (hmono _ (hD₀I hq'D) hx hq'2.le)
  · -- from above: some element of the defining set of `g x` is below `c`
    have : ∃ z ∈ l '' {r ∈ D₀ | x < r} ∪ {M}, z < c := by
      by_contra! h
      have := le_csInf ⟨M, Or.inr rfl⟩ h
      simp only [hg] at hc
      exact absurd (hc.trans_le this) (lt_irrefl _)
    obtain ⟨z, (⟨r, ⟨hrD, hxr⟩, rfl⟩ | rfl), hz⟩ := this
    · have hev : ∀ᶠ n in atTop, f (φ₁ n) r < c := (hl r hrD).eventually (gt_mem_nhds hz)
      filter_upwards [hφ₂.tendsto_atTop.eventually hev] with n hn
      exact (hmono _ hx (hD₀I hrD) hxr.le).trans_lt hn
    · exact Eventually.of_forall fun n ↦ (le_abs_self _).trans_lt ((hbdd _ x hx).trans_lt hz)

end Helly

namespace SobolevIntervalLp

variable {a b : ℝ}

/-- **Helly's selection theorem** ([brezis2011functional] Chapter 8, Remark 10 and Exercise 8.3):
a bounded sequence of `W^{1,1}(a, b)` has a subsequence whose continuous representatives converge
at every point of `[a, b]`. The representative is the difference of the two nondecreasing
functions `v_n(x) = ∫_a^x |u_n'|` and `w_n = v_n - ũ_n` (as `w_n(y) - w_n(x) = ∫_x^y (|u_n'| -
u_n') ≥ 0`), both bounded by a multiple of `‖u_n‖`; two applications of Helly's theorem for
monotone functions (`exists_subseq_forall_tendsto_of_forall_monotoneOn`) give the subsequence. -/
theorem exists_subseq_tendsto_of_bounded_one (hab : a < b)
    {u : ℕ → SobolevIntervalLp 1 1 (Opens.Ioo a b)} {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ x ∈ Icc a b, ∃ l, Tendsto (fun n ↦ rep (u (φ n)) x) atTop (𝓝 l) := by
  have hI := ordConnected_coe_Ioo a b
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by rw [closure_coe_Ioo hab]
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- the nondecreasing parts `v_n(x) = ∫_a^x |u_n'|` and `w_n = v_n - ũ_n`
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ → ℝ, v = fun n x ↦ ∫ t in a..x, |deriv (u n) 1 t| := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ → ℝ, w = fun n x ↦ v n x - rep (u n) x := ⟨_, rfl⟩
  have hint : ∀ n, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      IntervalIntegrable (fun t ↦ |deriv (u n) 1 t|) volume x y :=
    fun n x hx y hy ↦ (intervalIntegrable_deriv hI (u n) 1 (hcl hx) (hcl hy)).abs
  have hvsub : ∀ n, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      v n y - v n x = ∫ t in x..y, |deriv (u n) 1 t| := by
    intro n x hx y hy
    rw [hv]
    exact intervalIntegral.integral_interval_sub_left (hint n a ha y hy) (hint n a ha x hx)
  have hvmono : ∀ n, MonotoneOn (v n) (Icc a b) := fun n x hx y hy hxy ↦ by
    rw [← sub_nonneg, hvsub n x hx y hy]
    exact intervalIntegral.integral_nonneg hxy fun t _ ↦ abs_nonneg _
  have hwmono : ∀ n, MonotoneOn (w n) (Icc a b) := fun n x hx y hy hxy ↦ by
    rw [← sub_nonneg, hw]
    simp only
    rw [show v n y - rep (u n) y - (v n x - rep (u n) x)
        = (v n y - v n x) - (rep (u n) y - rep (u n) x) by ring, hvsub n x hx y hy,
      rep_sub_rep hI (u n) (hcl hx) (hcl hy), ← intervalIntegral.integral_sub (hint n x hx y hy)
        (intervalIntegrable_deriv hI (u n) 1 (hcl hx) (hcl hy))]
    exact intervalIntegral.integral_nonneg hxy fun t _ ↦ sub_nonneg.2 (le_abs_self _)
  -- the bounds
  have hnorm : ∀ n, ∫ t in a..b, |deriv (u n) 1 t| = ‖deriv (u n) 1‖ := by
    intro n
    rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _),
      ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable _),
      intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    simp only [Real.norm_eq_abs]
    rfl
  have hvbdd : ∀ n, ∀ x ∈ Icc a b, |v n x| ≤ M := by
    intro n x hx
    rw [hv]
    simp only
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg hx.1 fun t _ ↦ abs_nonneg _)]
    calc ∫ t in a..x, |deriv (u n) 1 t| ≤ ∫ t in a..b, |deriv (u n) 1 t| :=
          intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
            (Eventually.of_forall fun t ↦ abs_nonneg _) (hint n a ha b hb)
      _ = ‖deriv (u n) 1‖ := hnorm n
      _ ≤ M := (norm_deriv_le _ 1).trans (hM n)
  have hwbdd : ∀ n, ∀ x ∈ Icc a b, |w n x| ≤ M + embeddingConst 1 (Opens.Ioo a b) * M := by
    intro n x hx
    rw [hw]
    simp only
    refine (abs_sub _ _).trans (add_le_add (hvbdd n x hx) ?_)
    exact (abs_rep_le hI (u n) (hcl hx)).trans
      (mul_le_mul_of_nonneg_left (hM n) (embeddingConst_pos 1 _).le)
  -- two extractions
  obtain ⟨φ₁, hφ₁, h₁⟩ := exists_subseq_forall_tendsto_of_forall_monotoneOn hvmono hvbdd
  obtain ⟨φ₂, hφ₂, h₂⟩ := exists_subseq_forall_tendsto_of_forall_monotoneOn
    (f := fun n ↦ w (φ₁ n)) (fun n ↦ hwmono (φ₁ n)) (fun n ↦ hwbdd (φ₁ n))
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun x hx ↦ ?_⟩
  obtain ⟨l₁, hl₁⟩ := h₁ x hx
  obtain ⟨l₂, hl₂⟩ := h₂ x hx
  refine ⟨l₁ - l₂, ?_⟩
  have : (fun n ↦ rep (u (φ₁ (φ₂ n))) x) = fun n ↦ v (φ₁ (φ₂ n)) x - w (φ₁ (φ₂ n)) x := by
    funext n; rw [hw]; simp only; ring
  change Tendsto (fun n ↦ rep (u (φ₁ (φ₂ n))) x) atTop (𝓝 (l₁ - l₂))
  rw [this]
  exact (hl₁.comp hφ₂.tendsto_atTop).sub hl₂

end SobolevIntervalLp

end
