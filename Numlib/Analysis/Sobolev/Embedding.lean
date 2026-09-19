/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, beside the
Gagliardo–Nirenberg–Sobolev inequality for compactly supported `C¹` functions.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.MeasureTheory.Function.LpInterpolation

/-!
# The Sobolev inequalities on the whole space

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.3.A, on
`W^{1,p}(ℝ^N)`: the Sobolev–Gagliardo–Nirenberg inequality (Theorem 9.9), its consequence for the
intermediate exponents `p ≤ q ≤ p*` (Corollary 9.10), the limiting case `p = N` (Corollary 9.11),
and Morrey's theorem for `p > N` (Theorem 9.12) with the continuous representative of Remark 11
and the decay at infinity of Remark 12; then, on `W^{m,p}(ℝ^N)`, the higher-order embeddings of
Corollary 9.13 (`L^q`, `L^∞` and `C^k` with Hölder top derivatives) and the local `C^k`
representatives of `W^{m,p}_loc(Ω)`. The domain versions (Corollaries 9.14–9.15) are
`Numlib/Analysis/Sobolev/EmbeddingDomain.lean`, the compactness (Theorem 9.16)
`Numlib/Analysis/Sobolev/Compactness.lean`.

## Main results

Every inequality is stated first at the predicate level, for `HasWeakFDerivOn f w ⊤ μ` on a
finite-dimensional real normed space `E` with an additive Haar measure `μ` (the setting of
Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`), and then on the typed space
`SobolevEuclidean N 1 p ⊤` of `Numlib/Analysis/Sobolev/MultiIndex.lean`, as a bound on
`fn u` and as an `IsContinuousEmbedding` of the inclusion `SobolevMultiIndex.toLpₗ` into `L^q`.

* `HasWeakFDerivOn.exists_seq_contDiff_hasCompactSupport_tendsto_top`: the whole-space clause of
  Friedrichs' theorem read on the function and its gradient — smooth compactly supported `u_n`
  with `u_n → f` and `∇u_n → w` in `L^p`, which is what every density argument below uses.
* `HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq`, `SobolevEuclidean.eLpNorm_fn_le_of_eq`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_eq`: **Theorem 9.9**, `‖f‖_{p*} ≤ C ‖∇f‖_p` for
  `1 ≤ p < N`, `1/p* = 1/p − 1/N`, with Mathlib's constant `SNormLESNormFDerivOfEqConst`
  (`SobolevEuclidean.gnsConst` on `ℝ^N`); by density and Fatou's lemma from the compactly
  supported `C¹` case.
* `SobolevEuclidean.isContinuousEmbedding_toLp_of_le_of_le`: **Corollary 9.10**,
  `W^{1,p}(ℝ^N) ↪ L^q(ℝ^N)` for `p ≤ q ≤ p*`, by the interpolation inequality in the additive form
  `‖f‖_q ≤ ‖f‖_p + ‖f‖_{p*}` (`MeasureTheory.eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le`).
* `MeasureTheory.exists_forall_eLpNorm_le_of_eq_finrank`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_eq_finrank`: **Corollary 9.11**,
  `W^{1,N}(ℝ^N) ↪ L^q(ℝ^N)` for `N ≥ 2` and every `q ∈ [N, ∞)`: the `p = 1` inequality applied to
  `‖u‖^γ` gives the book's (20) (`ContDiff.eLpNorm_rpow_le_of_hasCompactSupport`), Young's
  inequality its (21), an induction on `γ = N, N + 1, …` and the interpolation inequality cover
  every `q`, and density and Fatou extend it to `W^{1,N}`.
* `ContDiff.lintegral_enorm_sub_le_of_mem_closedBall`, `ContDiff.enorm_sub_le_of_lt`,
  `ContDiff.enorm_le_of_lt`: **Morrey's estimates for `C¹` functions**, on balls rather than the
  book's cubes: `∫_B ‖u − u(x)‖ ≤ (2r/(1 − N/p)) μ(B)^{1−1/p} ‖∇u‖_{L^p(B)}` for `x` in a ball `B`
  of radius `r` (the segment bound, Fubini, the homothety `z ↦ x + t(z − x)` and Hölder), whence
  the Hölder estimate (25) `‖u x − u y‖ ≤ C ‖x − y‖^{1−N/p} ‖∇u‖_p` and the sup bound (24)
  `‖u x‖ ≤ C' (‖u‖_p + ‖∇u‖_p)`, with the explicit constants `MeasureTheory.morreyConst` and
  `MeasureTheory.morreySupConst`.
* `HasWeakFDerivOn.exists_continuous_holderWith_ae_eq`: **Theorem 9.12 (Morrey) with
  Remarks 11 and 12**, for `N < p < ∞`: the continuous representative, its Hölder estimate, its
  sup bound and its decay at infinity, by the uniform Cauchy property of the approximants in the
  Banach space of bounded continuous functions.
* `SobolevEuclidean.contRep`, `SobolevEuclidean.toBoundedContinuousMapL`,
  `SobolevEuclidean.isContinuousEmbedding_toBoundedContinuousMapL`: the continuous representative
  on the typed space and **`W^{1,p}(ℝ^N) ↪ C_b(ℝ^N) ⊆ L^∞(ℝ^N)`** as a bounded linear map.
* `SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le` lifts an `L^q` bound on
  `W^{m,p}(ℝ^N)` to `W^{m+1,p}(ℝ^N) ⊆ W^{1,q}(ℝ^N)`, the inductive step of Corollary 9.13.
* `SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order`, `SobolevEuclidean.memLp_fn_of_order`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_order`: **Corollary 9.13, the `L^q` clauses**
  in one statement, `W^{m,p}(ℝ^N) ↪ L^q(ℝ^N)` for `p ≤ q < ∞` with `1/p − m/N ≤ 1/q` (so
  `1/q = 1/p − m/N` when `1/p − m/N > 0`, every `q ∈ [p, ∞)` otherwise), by induction on `m` from
  the first-order case `SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le`.
* `SobolevEuclidean.exists_forall_continuous_ae_eq_of_order`,
  `SobolevEuclidean.memLp_fn_top_of_order`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_top_of_order`:
  **Corollary 9.13, the `L^∞` clause**, `W^{m,p}(ℝ^N) ⊂ L^∞(ℝ^N)` for `1/p − m/N < 0`, with a
  continuous Hölder representative.
* `SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order`,
  `SobolevEuclidean.exists_contDiff_ae_eq_of_order`, `SobolevEuclidean.exists_contDiff_ae_eq_of_lt`:
  **Corollary 9.13, the `C^k` clause**, `W^{m,p}(ℝ^N) ⊂ C^k(ℝ^N)` for `k + N/p < m`, with the
  derivatives of order `≤ k` bounded by `C ‖u‖` and those of order `k` Hölder — of the sharp
  exponent `m − N/p − k` when it is less than `1` — by induction on `k` through Remark 2's
  converse `HasWeakFDerivOn.exists_contDiffOn_ae_eq_of_continuousOn`.
* `MemSobolevMultiIndexLoc.exists_contDiffOn_of_lt`, `MemSobolevMultiIndexLoc.exists_contDiffOn`:
  the local form, `W^{m,p}_loc(Ω) ⊂ C^k(Ω)` for `k + N/p < m` and `⋂_m H^m_loc(Ω) ⊂ C^∞(Ω)`,
  by cut-offs and gluing.
* `SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one`: **Remark 13**,
  `W^{N,1}(ℝ^N) ⊂ L^∞(ℝ^N)` with a continuous representative bounded by `‖∂_1 ⋯ ∂_N u‖_1 ≤ ‖u‖`,
  from the iterated fundamental theorem of calculus over the coordinates
  (`ContDiff.enorm_le_lintegral_iteratedFDeriv_finrank`, through the line bound
  `ContDiff.enorm_le_lintegral_fderiv_line` and the Fubini step
  `MeasureTheory.lintegral_fin_succ_eq`).

## Design

Exponents are `ℝ≥0` with the Sobolev conjugate written by its defining relation
`(p' : ℝ)⁻¹ = p⁻¹ − N⁻¹`, as Mathlib does; the typed spaces carry `[Fact (1 ≤ (p : ℝ≥0∞))]`.
Morrey's theorem is stated for finite `p` only: the case `p = ∞` is the Lipschitz representative
of Remark 7 (`HasWeakFDerivOn.exists_lipschitzOnWith_ae_eq_of_convex`) and is not restated here.
Balls replace the cubes of the book's proof of Theorem 9.12 because the homothety
`z ↦ x + t(z − x)` maps any convex set containing `x` into itself and scales the Haar measure by
`t^N` (`MeasureTheory.setLIntegral_comp_homothety`), so no coordinates enter; the constants
differ from the book's cube constants accordingly. The higher-order statements carry the
hypothesis `2 ≤ N ∨ 1 < p`: the chain of first-order embeddings is stuck at `W^{1,1}(ℝ)`, where
Corollary 9.11 needs `N ≥ 2` (that case is the one-dimensional theory of
`Numlib/Analysis/Sobolev/Interval/Embedding.lean`). Remark 13 is the one case the chain misses
that the book settles, `W^{N,1}(ℝ^N) ⊂ L^∞(ℝ^N)`; it is proved directly on the smooth
approximants, and its tensor-to-multi-index step reads the mixed derivative `∂_1 ⋯ ∂_N` off the
weak derivative of order `N` through `HasWeakIteratedFDerivOn.lineDeriv` and the permutation
lemma `multiIndexDirections_multiIndexCount_perm`. Lemma 9.4 (Gagliardo's product lemma) in its
general form, `∫_{ℝ^N} ∏ i, f i x̃_i ≤ ∏ i, ‖f i‖_{L^{N−1}(ℝ^{N−1})}`, is
`MeasureTheory.lintegral_prod_comp_succAbove_le`, proved by the book's induction on `N` with the
coordinates split as `Fin.cons s t` (Hölder against the factor independent of the new coordinate,
the induction hypothesis, and the generalized Hölder inequality in the new coordinate); Theorem 9.9
itself goes through Mathlib's special case `MeasureTheory.lintegral_prod_lintegral_pow_le`.

## References

[brezis2011functional], §9.3.A: Theorem 9.9, Corollaries 9.10–9.11, Theorem 9.12, Remarks 11–12,
Corollary 9.13 (footnotes 12–14), Remark 13, and the proof of Theorem 9.31 (`e_n ∈ C^∞(Ω)`).
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

/-! ### From convergence in the Sobolev norm to convergence of the function and the gradient -/

section Approximation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {w : E → E →L[ℝ] F}
  {p : ℝ≥0∞}

omit [μ.IsAddHaarMeasure] in
/-- The `L^p` norm of a function with a first-order weak derivative on the whole space is bounded
by its Sobolev norm of order one. -/
theorem HasWeakFDerivOn.eLpNorm_le_sobolevNorm_one (h : HasWeakFDerivOn f w ⊤ μ) (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) : eLpNorm f p μ ≤ sobolevNorm f 1 p ⊤ μ := by
  have hloc : LocallyIntegrable f μ :=
    locallyIntegrableOn_univ.1 (by simpa using h.locallyIntegrableOn)
  have hW := hasWeakIteratedFDerivOn_zero (μ := μ) (Ω := ⊤) (locallyIntegrableOn_univ.2 hloc)
  have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖weakIteratedFDeriv 0 f ⊤ μ x‖ₑ := by
    filter_upwards [hW.weakIteratedFDeriv_ae_eq] with x hx
    rw [hx (by simp), enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
  calc eLpNorm f p μ ≤ eLpNorm (weakIteratedFDeriv 0 f ⊤ μ) p μ :=
        eLpNorm_mono_enorm_ae hloc.aestronglyMeasurable (hae.mono fun x hx ↦ hx.le)
    _ = eLpNorm (weakIteratedFDeriv 0 f ⊤ μ) p (μ.restrict ((⊤ : Opens E) : Set E)) := by
        rw [Measure.restrict_coe_top]
    _ ≤ sobolevNorm f 1 p ⊤ μ := eLpNorm_weakIteratedFDeriv_le_sobolevNorm hp hp' (Nat.zero_le 1)

omit [μ.IsAddHaarMeasure] in
/-- The `L^p` norm of a first-order weak derivative on the whole space is bounded by the Sobolev
norm of order one of the function. -/
theorem HasWeakFDerivOn.eLpNorm_weakDeriv_le_sobolevNorm_one (h : HasWeakFDerivOn f w ⊤ μ)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) : eLpNorm w p μ ≤ sobolevNorm f 1 p ⊤ μ := by
  have hloc : LocallyIntegrable w μ :=
    locallyIntegrableOn_univ.1 (by simpa using h.locallyIntegrableOn_weakDeriv)
  have hae : ∀ᵐ x ∂μ, ‖w x‖ₑ = ‖weakIteratedFDeriv 1 f ⊤ μ x‖ₑ := by
    filter_upwards [HasWeakIteratedFDerivOn.weakIteratedFDeriv_ae_eq h] with x hx
    rw [hx (by simp), enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
  calc eLpNorm w p μ ≤ eLpNorm (weakIteratedFDeriv 1 f ⊤ μ) p μ :=
        eLpNorm_mono_enorm_ae hloc.aestronglyMeasurable (hae.mono fun x hx ↦ hx.le)
    _ = eLpNorm (weakIteratedFDeriv 1 f ⊤ μ) p (μ.restrict ((⊤ : Opens E) : Set E)) := by
        rw [Measure.restrict_coe_top]
    _ ≤ sobolevNorm f 1 p ⊤ μ := eLpNorm_weakIteratedFDeriv_le_sobolevNorm hp hp' le_rfl

omit [FiniteDimensional ℝ E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- A difference of functions with first-order weak derivatives has the difference of the weak
derivatives as weak derivative. -/
protected theorem HasWeakFDerivOn.sub {Ω : Opens E} {f₁ f₂ : E → F} {w₁ w₂ : E → E →L[ℝ] F}
    (h₁ : HasWeakFDerivOn f₁ w₁ Ω μ) (h₂ : HasWeakFDerivOn f₂ w₂ Ω μ) :
    HasWeakFDerivOn (f₁ - f₂) (w₁ - w₂) Ω μ := by
  have := HasWeakIteratedFDerivOn.sub h₁ h₂
  unfold HasWeakFDerivOn
  convert this using 2 with x
  simp

omit [CompleteSpace F] in
/-- A `C¹` function has its classical derivative as weak derivative on any open set. -/
theorem ContDiff.hasWeakFDerivOn {Ω : Opens E} {g : E → F} (hg : ContDiff ℝ 1 g) :
    HasWeakFDerivOn g (fderiv ℝ g) Ω μ := by
  have := ContDiffOn.hasWeakIteratedFDerivOn (μ := μ) (Ω := Ω) (m := 1) hg.contDiffOn le_rfl
  unfold HasWeakFDerivOn
  convert this using 2 with x
  rw [iteratedFDeriv_one_eq_symm_fderiv]

/-- **Density of `C_c^∞` in `W^{1,p}(ℝ^N)`, read on the function and its gradient**: for
`f ∈ W^{1,p}(ℝ^N)` with weak derivative `w`, `1 ≤ p < ∞`, there are smooth compactly supported
`u_n` with `u_n → f` and `∇u_n → w` in `L^p`. This is the whole-space clause of
[brezis2011functional] Theorem 9.2 in the form the proofs of §9.3 use, obtained from
`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm` by reading the two components of the
Sobolev norm of `u_n - f`. -/
theorem HasWeakFDerivOn.exists_seq_contDiff_hasCompactSupport_tendsto_top
    (h : HasWeakFDerivOn f w ⊤ μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : MemLp f p μ)
    (hw : MemLp w p μ) :
    ∃ u : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      Tendsto (fun n ↦ eLpNorm (u n - f) p μ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p μ) atTop (𝓝 0) := by
  have hfs : MemSobolev f 1 p ⊤ μ := h.memSobolev (by simpa [Measure.restrict_coe_top] using hf)
    (by simpa [Measure.restrict_coe_top] using hw)
  obtain ⟨u, hus, huc, hut⟩ := hfs.exists_seq_hasCompactSupport_tendsto_sobolevNorm hp hp'
  refine ⟨u, hus, huc, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hut (fun _ ↦ zero_le)
      fun n ↦ ?_
    exact (((hus n).of_le (by simp)).hasWeakFDerivOn.sub h).eLpNorm_le_sobolevNorm_one hp hp'
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hut (fun _ ↦ zero_le)
      fun n ↦ ?_
    have := (((hus n).of_le (by simp)).hasWeakFDerivOn.sub h).eLpNorm_weakDeriv_le_sobolevNorm_one
      hp hp'
    simpa only [Pi.sub_apply, Pi.sub_def] using this

end Approximation

/-! ### Theorem 9.9: the Sobolev–Gagliardo–Nirenberg inequality on `W^{1,p}(ℝ^N)` -/

section GNS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {w : E → E →L[ℝ] F}

/-- **Theorem 9.9 (Sobolev–Gagliardo–Nirenberg) on `W^{1,p}(ℝ^N)`**: for `1 ≤ p < N`,
`1/p* = 1/p − 1/N`, and `f ∈ W^{1,p}(ℝ^N)` with weak derivative `w`,
`‖f‖_{p*} ≤ C ‖w‖_p` with Mathlib's constant `SNormLESNormFDerivOfEqConst`. The inequality for
compactly supported `C¹` functions is Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`;
it passes to `W^{1,p}` by density and Fatou's lemma: the approximants of
`HasWeakFDerivOn.exists_seq_contDiff_hasCompactSupport_tendsto_top` converge in `L^p`, hence
almost everywhere along a subsequence, and their `L^{p*}` norms are eventually bounded by
`C (‖w‖_p + δ)` for every `δ > 0`. [brezis2011functional] Theorem 9.9. -/
theorem HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq (h : HasWeakFDerivOn f w ⊤ μ)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpN : p < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) (hf : MemLp f p μ) (hw : MemLp w p μ) :
    eLpNorm f p' μ ≤ SNormLESNormFDerivOfEqConst F μ p * eLpNorm w p μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have hn : 0 < finrank ℝ E := by
    have : (0 : ℝ) < finrank ℝ E := lt_of_lt_of_le (by exact_mod_cast zero_lt_one.trans_le hp)
      (by exact_mod_cast hpN.le)
    exact_mod_cast this
  obtain ⟨u, hus, huc, hu0, hu1⟩ :=
    h.exists_seq_contDiff_hasCompactSupport_tendsto_top hp1 ENNReal.coe_ne_top hf hw
  -- an almost everywhere convergent subsequence
  have hmeas : TendstoInMeasure μ u atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (by exact_mod_cast (zero_lt_one.trans_le hp).ne') hu0
  obtain ⟨ns, hns_mono, hns⟩ := hmeas.exists_seq_tendsto_ae
  -- the bound on each approximant
  have hbound : ∀ n, eLpNorm (u n) p' μ
      ≤ SNormLESNormFDerivOfEqConst F μ p * eLpNorm (fderiv ℝ (u n)) p μ := fun n ↦
    eLpNorm_le_eLpNorm_fderiv_of_eq μ ((hus n).of_le (by simp)) (huc n) hp hn hp'
  -- for every `δ > 0`, the approximants are eventually bounded by `C (‖w‖_p + δ)`
  have key : ∀ δ : ℝ≥0∞, 0 < δ → eLpNorm f p' μ
      ≤ SNormLESNormFDerivOfEqConst F μ p * (eLpNorm w p μ + δ) := by
    intro δ hδ
    have hev : ∀ᶠ n in atTop, eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p μ ≤ δ :=
      ENNReal.tendsto_nhds_zero.1 hu1 δ hδ
    refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun n ↦ u (ns n)) ?_
      (fun n ↦ (hus _).continuous.aestronglyMeasurable) hf.aestronglyMeasurable hns
    filter_upwards [hns_mono.tendsto_atTop.eventually hev] with n hn
    refine (hbound (ns n)).trans (mul_le_mul' le_rfl ?_)
    have hsplit : fderiv ℝ (u (ns n)) = (fun x ↦ fderiv ℝ (u (ns n)) x - w x) + w := by
      funext x
      simp
    rw [hsplit]
    exact (eLpNorm_add_le hp1).trans (by rw [add_comm]; exact add_le_add le_rfl hn)
  -- let `δ → 0`
  have hlim : Tendsto (fun δ : ℝ≥0∞ ↦ SNormLESNormFDerivOfEqConst F μ p * (eLpNorm w p μ + δ))
      (𝓝[>] 0) (𝓝 (SNormLESNormFDerivOfEqConst F μ p * eLpNorm w p μ)) := by
    have : Tendsto (fun δ : ℝ≥0∞ ↦ eLpNorm w p μ + δ) (𝓝[>] 0) (𝓝 (eLpNorm w p μ + 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.add tendsto_id)
    rw [add_zero] at this
    exact ENNReal.Tendsto.const_mul this (Or.inr ENNReal.coe_ne_top)
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ ↦ key δ hδ)

/-- `MemLp` for the Sobolev conjugate exponent: the bound of
`HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq` is finite. -/
theorem HasWeakFDerivOn.memLp_of_eq (h : HasWeakFDerivOn f w ⊤ μ)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpN : p < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) (hf : MemLp f p μ) (hw : MemLp w p μ) :
    MemLp f p' μ :=
  memLp_iff.2 ((h.eLpNorm_le_eLpNorm_weakFDeriv_of_eq hp hpN hp' hf hw).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hw.eLpNorm_lt_top))

end GNS

/-! ### Theorem 9.9 on the typed space `W^{1,p}(ℝ^N)` -/

section Typed

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open SobolevMultiIndex

/-- The tensor weak derivative of `u ∈ W^{1,p}(ℝ^N)` is bounded in `L^p` by the `ℓ¹` sum of the
`L^p` norms of the partial derivatives: the operator norm of the derivative tensor is at most the
sum of the norms of its values on the standard basis. -/
theorem SobolevEuclidean.eLpNorm_le_sum_of_hasWeakFDerivOn (u : SobolevEuclidean N 1 p ⊤)
    {w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hw : HasWeakFDerivOn (fn u) w ⊤ volume) :
    eLpNorm w p volume ≤ ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  classical
  have hp : 1 ≤ p := Fact.out
  have hwm : AEStronglyMeasurable w volume :=
    (locallyIntegrableOn_univ.1 (by simpa using hw.locallyIntegrableOn_weakDeriv)
      |>.aestronglyMeasurable)
  -- the components of `w` are the partial derivatives
  have hcomp : ∀ i, (fun x ↦ w x (EuclideanSpace.single i 1))
      =ᵐ[volume] weakDeriv u (MultiIndexLE.single i) := by
    intro i
    have h1 := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
        Fin N → EuclideanSpace ℝ (Fin N)) i)
    have h2 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u)
        (fun x ↦ w x (EuclideanSpace.single i 1)) ⊤ volume := by
      have := HasWeakIteratedFDerivOn.lineDeriv hw ![EuclideanSpace.single i 1]
      simpa using this
    have h3 := HasWeakIteratedLineDerivOn.ae_eq h2 (by simpa using h1)
    filter_upwards [h3] with x hx
    exact hx (by simp)
  -- the pointwise bound, almost everywhere
  have hbound : ∀ᵐ x ∂volume, ‖w x‖ ≤ ‖∑ i, ‖weakDeriv u (MultiIndexLE.single i) x‖‖ := by
    have hall : ∀ᵐ x ∂volume, ∀ i, w x (EuclideanSpace.single i 1)
        = weakDeriv u (MultiIndexLE.single i) x := ae_all_iff.2 hcomp
    filter_upwards [hall] with x hx
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    refine (w x).norm_le_sum_norm_apply_single.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hx i]
  calc eLpNorm w p volume
      ≤ eLpNorm (fun x ↦ ∑ i, ‖weakDeriv u (MultiIndexLE.single i) x‖) p volume :=
        eLpNorm_mono_ae hwm hbound
    _ = eLpNorm (∑ i, fun x ↦ ‖weakDeriv u (MultiIndexLE.single i) x‖) p volume := by
        congr 1
        funext x
        simp only [Finset.sum_apply]
    _ ≤ ∑ i, eLpNorm (fun x ↦ ‖weakDeriv u (MultiIndexLE.single i) x‖) p volume :=
        eLpNorm_sum_le_of_norm hp
    _ = ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hm : AEStronglyMeasurable (weakDeriv u (MultiIndexLE.single i) : _ → ℝ) volume := by
          simpa only [Measure.restrict_coe_top] using
            Lp.aestronglyMeasurable (weakDeriv u (MultiIndexLE.single i))
        rw [eLpNorm_norm _ hm, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
          eLpNorm_restrict_coe_top]

/-- The `ℓ¹` sum of the `L^p` norms of the partial derivatives of `u ∈ W^{1,p}(Ω)` is at most
`N ‖u‖`. -/
theorem SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (u : SobolevEuclidean N 1 p Ω) :
    ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ ≤ N * ENNReal.ofReal ‖u‖ := by
  calc ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖
      ≤ ∑ _i : Fin N, ENNReal.ofReal ‖u‖ :=
        Finset.sum_le_sum fun i _ ↦ ENNReal.ofReal_le_ofReal (norm_weakDeriv_le u _)
    _ = N * ENNReal.ofReal ‖u‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [Fact (1 ≤ p)] in
/-- The function of an element of `W^{k,p}(ℝ^N)` lies in `L^p(ℝ^N)`. -/
theorem SobolevEuclidean.memLp_fn {k : ℕ} (u : SobolevEuclidean N k p ⊤) :
    MemLp (fn u) p volume := by
  simpa [Measure.restrict_coe_top] using SobolevMultiIndex.memLp u

/-- A weak gradient of `u ∈ W^{1,p}(ℝ^N)` in the tensor reading, with its `L^p` bound by the
`ℓ¹` sum of the partial derivatives. -/
theorem SobolevEuclidean.exists_hasWeakFDerivOn (u : SobolevEuclidean N 1 p ⊤) :
    ∃ w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
      HasWeakFDerivOn (fn u) w ⊤ volume ∧ MemLp w p volume ∧
      eLpNorm w p volume ≤ ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  obtain ⟨w, hw, hwp⟩ := ((memSobolevMultiIndex u).memSobolev).exists_hasWeakFDerivOn
  rw [Measure.restrict_coe_top] at hwp
  exact ⟨w, hw, hwp, SobolevEuclidean.eLpNorm_le_sum_of_hasWeakFDerivOn u hw⟩

end Typed

section TypedGNS

variable {N : ℕ} {p p' : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

open SobolevMultiIndex

variable (N) in
/-- **The constant of the Sobolev–Gagliardo–Nirenberg inequality on `ℝ^N`**, Mathlib's
`SNormLESNormFDerivOfEqConst` for real-valued functions and Lebesgue measure: the `C = C(p, N)`
of [brezis2011functional] Theorem 9.9. -/
def SobolevEuclidean.gnsConst (p : ℝ) : ℝ≥0 :=
  SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin N))) p

/-- **Theorem 9.9 on the typed space**: for `u ∈ W^{1,p}(ℝ^N)`, `1 ≤ p < N`, `1/p* = 1/p − 1/N`,
`‖u‖_{p*} ≤ C ∑_i ‖∂_i u‖_p`, with Mathlib's constant `C = SNormLESNormFDerivOfEqConst`.
[brezis2011functional] Theorem 9.9, the inequality (17). -/
theorem SobolevEuclidean.eLpNorm_fn_le_of_eq (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclidean N 1 p ⊤) :
    eLpNorm (fn u) (p' : ℝ≥0∞) volume ≤ SobolevEuclidean.gnsConst N p
      * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  have hp : 1 ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  obtain ⟨w, hw, hwp, hwle⟩ := SobolevEuclidean.exists_hasWeakFDerivOn u
  have hN : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  refine (hw.eLpNorm_le_eLpNorm_weakFDeriv_of_eq hp (by rw [hN]; exact_mod_cast hpN)
    (by rw [hN]; exact hp') (SobolevEuclidean.memLp_fn u) hwp).trans ?_
  exact mul_le_mul' le_rfl hwle

/-- **`W^{1,p}(ℝ^N) ⊆ L^{p*}(ℝ^N)`** for `1 ≤ p < N`: [brezis2011functional] Theorem 9.9, the
inclusion. -/
theorem SobolevEuclidean.memLp_fn_of_eq (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclidean N 1 p ⊤) : MemLp (fn u) (p' : ℝ≥0∞) volume :=
  memLp_iff.2 ((SobolevEuclidean.eLpNorm_fn_le_of_eq hpN hp' u).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.sum_lt_top.2 fun _ _ ↦ ENNReal.ofReal_lt_top)))

/-- **Theorem 9.9, the bound in the norm of `W^{1,p}(ℝ^N)`**: `‖u‖_{p*} ≤ C N ‖u‖`. -/
theorem SobolevEuclidean.eLpNorm_fn_le_norm_of_eq (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (u : SobolevEuclidean N 1 p ⊤) :
    eLpNorm (fn u) (p' : ℝ≥0∞) volume
      ≤ ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N * ‖u‖) := by
  refine (SobolevEuclidean.eLpNorm_fn_le_of_eq hpN hp' u).trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal, mul_assoc]
  exact mul_le_mul' le_rfl (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u)

/-- **Theorem 9.9 as a continuous embedding**: `W^{1,p}(ℝ^N) ↪ L^{p*}(ℝ^N)` for `1 ≤ p < N`,
along the inclusion `SobolevMultiIndex.toLpₗ`. [brezis2011functional] Theorem 9.9, "with
continuous injection". -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_eq [Fact (1 ≤ (p' : ℝ≥0∞))] (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_of_eq hpN hp' u) := by
  refine isContinuousEmbedding_toLpₗ _ (C := SobolevEuclidean.gnsConst N p * N)
    fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (show (0 : ℝ) ≤ SobolevEuclidean.gnsConst N p * N * ‖u‖ by positivity)]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  exact (eLpNorm_restrict_coe_top (fn u) (p' : ℝ≥0∞)).trans_le
    (SobolevEuclidean.eLpNorm_fn_le_norm_of_eq hpN hp' u)

end TypedGNS

/-! ### Corollary 9.10: the intermediate exponents -/

section Interpolation

/-- A weighted geometric mean is at most the sum: `a ^ θ * b ^ (1 - θ) ≤ a + b` for
`0 ≤ θ ≤ 1` — the form of Young's inequality that [brezis2011functional] Corollary 9.10 uses to
read the interpolation inequality `‖u‖_q ≤ ‖u‖_p^θ ‖u‖_{p*}^{1−θ}` as `‖u‖_q ≤ ‖u‖_p + ‖u‖_{p*}`. -/
theorem ENNReal.rpow_mul_rpow_one_sub_le_add (a b : ℝ≥0∞) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    a ^ θ * b ^ (1 - θ) ≤ a + b := by
  calc a ^ θ * b ^ (1 - θ) ≤ (a + b) ^ θ * (a + b) ^ (1 - θ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow le_self_add hθ₀)
          (ENNReal.rpow_le_rpow le_add_self (by linarith))
    _ = a + b := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hθ₀ (by linarith), add_sub_cancel, ENNReal.rpow_one]

/-- **The interpolation inequality in additive form** ([brezis2011functional] Corollary 9.10,
proof): for `p ≤ r ≤ q` and `p ≠ 0`, `‖f‖_r ≤ ‖f‖_p + ‖f‖_q`. -/
theorem MeasureTheory.eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le {α G : Type*}
    [MeasurableSpace α] {ν : Measure α} [NormedAddCommGroup G] {f : α → G}
    (hf : AEStronglyMeasurable f ν) {p q r : ℝ≥0∞} (hp : p ≠ 0) (hpr : p ≤ r) (hrq : r ≤ q) :
    eLpNorm f r ν ≤ eLpNorm f p ν + eLpNorm f q ν := by
  obtain ⟨θ, hθ₀, hθ₁, hr⟩ := exists_inv_eq_ofReal_mul_inv_add hp hpr hrq
  exact (eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hf hθ₀ hθ₁ hr).trans
    (ENNReal.rpow_mul_rpow_one_sub_le_add _ _ hθ₀ hθ₁)

end Interpolation

section TypedGNSLe

variable {N : ℕ} {p p' q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

open SobolevMultiIndex

/-- The `L^p` norm of the function of `u ∈ W^{k,p}(ℝ^N)` is at most `‖u‖`. -/
theorem SobolevEuclidean.eLpNorm_fn_le_ofReal_norm {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : SobolevEuclidean N k p ⊤) : eLpNorm (fn u) p volume ≤ ENNReal.ofReal ‖u‖ := by
  have h : ‖weakDeriv u 0‖ = (eLpNorm (fn u) p volume).toReal := by
    rw [Lp.norm_def, eLpNorm_restrict_coe_top]
    rfl
  rw [← ENNReal.ofReal_toReal (SobolevEuclidean.memLp_fn u).eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (h ▸ norm_weakDeriv_le u 0)

/-- **Corollary 9.10, the bound**: for `1 ≤ p < N`, `1/p* = 1/p − 1/N` and `p ≤ q ≤ p*`,
`‖u‖_q ≤ (1 + C N) ‖u‖` for `u ∈ W^{1,p}(ℝ^N)`, by the interpolation inequality between `p` and
`p*` and Theorem 9.9. [brezis2011functional] Corollary 9.10. -/
theorem SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p')
    (u : SobolevEuclidean N 1 p ⊤) :
    eLpNorm (fn u) (q : ℝ≥0∞) volume
      ≤ ENNReal.ofReal ((1 + SobolevEuclidean.gnsConst N p * N) * ‖u‖) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    have : (1 : ℝ≥0∞) ≤ p := Fact.out
    exact (zero_lt_one.trans_le this).ne'
  calc eLpNorm (fn u) (q : ℝ≥0∞) volume
      ≤ eLpNorm (fn u) p volume + eLpNorm (fn u) (p' : ℝ≥0∞) volume :=
        eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le
          (SobolevEuclidean.memLp_fn u).aestronglyMeasurable hp0 (by exact_mod_cast hpq)
          (by exact_mod_cast hqp')
    _ ≤ ENNReal.ofReal ‖u‖ + ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N * ‖u‖) :=
        add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
          (SobolevEuclidean.eLpNorm_fn_le_norm_of_eq hpN hp' u)
    _ = ENNReal.ofReal ((1 + SobolevEuclidean.gnsConst N p * N) * ‖u‖) := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (by positivity)]
        congr 1
        ring

/-- **`W^{1,p}(ℝ^N) ⊆ L^q(ℝ^N)` for `p ≤ q ≤ p*`**: [brezis2011functional] Corollary 9.10, the
inclusion. -/
theorem SobolevEuclidean.memLp_fn_of_le_of_le (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (hpq : p ≤ q) (hqp' : q ≤ p') (u : SobolevEuclidean N 1 p ⊤) :
    MemLp (fn u) (q : ℝ≥0∞) volume :=
  memLp_iff.2 ((SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' u).trans_lt
    ENNReal.ofReal_lt_top)

/-- **Corollary 9.10**: `W^{1,p}(ℝ^N) ↪ L^q(ℝ^N)` with continuous injection for `1 ≤ p < N` and
`p ≤ q ≤ p*`, `1/p* = 1/p − 1/N`. [brezis2011functional] Corollary 9.10. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_le_of_le [Fact (1 ≤ (q : ℝ≥0∞))]
    (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using
          SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp' u) := by
  refine isContinuousEmbedding_toLpₗ _ (C := 1 + SobolevEuclidean.gnsConst N p * N) fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (show (0 : ℝ) ≤ (1 + SobolevEuclidean.gnsConst N p * N) * ‖u‖ by positivity)]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  exact (eLpNorm_restrict_coe_top (fn u) (q : ℝ≥0∞)).trans_le
    (SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' u)

end TypedGNSLe

/-! ### Morrey's estimate for `C¹` functions

The analytic core of Theorem 9.12, on balls rather than the book's cubes: for `x` in a closed
ball `B` of radius `r` and `u ∈ C¹`,
`∫_B ‖u z − u x‖ dz ≤ (2r/(1 − N/p)) μ(B)^{1−1/p} ‖∇u‖_{L^p(B)}`, from the segment bound
`‖u z − u x‖ ≤ ‖z − x‖ ∫_0^1 ‖∇u(x + t(z − x))‖ dt`, Fubini, the homothety `z ↦ x + t(z − x)` of
ratio `t` (which maps `B` into itself and scales the measure by `t^N`), and Hölder's inequality
on the image. -/

section MorreyC1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- **The segment bound**: for `u ∈ C¹`,
`‖u z − u x‖ ≤ ‖z − x‖ ∫_0^1 ‖∇u(x + t(z − x))‖ dt`, the inequality (26) of
[brezis2011functional] §9.3, proof of Theorem 9.12. -/
theorem ContDiff.enorm_sub_le_enorm_mul_lintegral_fderiv (hu : ContDiff ℝ 1 u) (x z : E) :
    ‖u z - u x‖ₑ ≤ ‖z - x‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • (z - x))‖ₑ := by
  have hd : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t ↦ u (x + t • (z - x)))
      (fderiv ℝ u (x + t • (z - x)) (z - x)) t := fun t ↦ by
    have := (hd (x + t • (z - x))).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (z - x)).const_add x)
    simpa [Function.comp_def] using this
  have hcont : Continuous fun t : ℝ ↦ fderiv ℝ u (x + t • (z - x)) (z - x) := by
    have : Continuous fun t : ℝ ↦ fderiv ℝ u (x + t • (z - x)) :=
      (hu.continuous_fderiv one_ne_zero).comp (by fun_prop)
    exact this.clm_apply continuous_const
  have hFTC : u z - u x = ∫ t in (0 : ℝ)..1, fderiv ℝ u (x + t • (z - x)) (z - x) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
      (hcont.intervalIntegrable 0 1)
    simpa using this.symm
  rw [hFTC, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  refine lintegral_mono fun t ↦ ?_
  rw [mul_comm]
  exact ContinuousLinearMap.le_opENorm _ _

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The homothety of centre `x` and ratio `t ≠ 0` is injective. -/
theorem AffineMap.homothety_injective_of_ne_zero (x : E) {t : ℝ} (ht : t ≠ 0) :
    Function.Injective (AffineMap.homothety x t) := fun z₁ z₂ h ↦ by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_left_inj] at h
  simpa using smul_right_injective E ht h

omit [FiniteDimensional ℝ E] in
/-- The image of a measurable set under a homothety of nonzero ratio is measurable. -/
theorem MeasurableSet.image_homothety {s : Set E} (hs : MeasurableSet s) (x : E) {t : ℝ}
    (ht : t ≠ 0) : MeasurableSet (AffineMap.homothety x t '' s) := by
  have h : AffineMap.homothety x t '' s = AffineMap.homothety x t⁻¹ ⁻¹' s := by
    refine congrFun (Set.image_eq_preimage_of_inverse (f := ⇑(AffineMap.homothety x t))
      (g := ⇑(AffineMap.homothety x t⁻¹)) (fun z ↦ ?_) fun z ↦ ?_) s
    · rw [← AffineMap.homothety_mul_apply, inv_mul_cancel₀ ht, AffineMap.homothety_one,
        AffineMap.id_apply]
    · rw [← AffineMap.homothety_mul_apply, mul_inv_cancel₀ ht, AffineMap.homothety_one,
        AffineMap.id_apply]
  rw [h]
  exact hs.preimage (AffineMap.homothety_continuous x t⁻¹).measurable

/-- **A Haar measure under a homothety**: the pushforward of `μ` by the homothety of centre `x`
and ratio `t ≠ 0` is `|t^N|⁻¹ μ`. -/
theorem MeasureTheory.Measure.map_homothety (x : E) {t : ℝ} (ht : t ≠ 0) :
    μ.map (AffineMap.homothety x t) = ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| • μ := by
  have hφ : (AffineMap.homothety x t : E → E)
      = (fun y ↦ y + x) ∘ (fun y ↦ t • y) ∘ fun z ↦ z + -x := by
    funext z
    simp [AffineMap.homothety_apply, sub_eq_add_neg]
  rw [hφ, ← Measure.map_map (measurable_add_const x)
    ((measurable_const_smul t).comp (measurable_add_const (-x))),
    ← Measure.map_map (measurable_const_smul t) (measurable_add_const (-x)),
    map_add_right_eq_self μ (-x), Measure.map_addHaar_smul μ ht,
    Measure.map_smul _ (measurable_add_const x).aemeasurable, map_add_right_eq_self μ x]

/-- **Change of variables under a homothety** for a Lebesgue integral over a set: for measurable
`G` and `t ≠ 0`, `∫_s G(x + t(z − x)) dz = |t^N|⁻¹ ∫_{x + t(s − x)} G(y) dy`. This is the
substitution `y = tx` of [brezis2011functional] §9.3, proof of Theorem 9.12. -/
theorem MeasureTheory.setLIntegral_comp_homothety {G : E → ℝ≥0∞} (hG : Measurable G) (x : E)
    {t : ℝ} (ht : t ≠ 0) {s : Set E} (hs : MeasurableSet s) :
    ∫⁻ z in s, G (AffineMap.homothety x t z) ∂μ
      = ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| * ∫⁻ y in AffineMap.homothety x t '' s, G y ∂μ := by
  have hinj := AffineMap.homothety_injective_of_ne_zero x ht
  calc ∫⁻ z in s, G (AffineMap.homothety x t z) ∂μ
      = ∫⁻ z in AffineMap.homothety x t ⁻¹' (AffineMap.homothety x t '' s),
          G (AffineMap.homothety x t z) ∂μ := by rw [preimage_image_eq _ hinj]
    _ = ∫⁻ y in AffineMap.homothety x t '' s, G y ∂(μ.map (AffineMap.homothety x t)) :=
        (setLIntegral_map (hs.image_homothety x ht) hG
          (AffineMap.homothety_continuous x t).measurable).symm
    _ = ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| * ∫⁻ y in AffineMap.homothety x t '' s, G y ∂μ := by
        rw [Measure.map_homothety x ht, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The homothety of centre `x ∈ s` and ratio `t ∈ [0, 1]` maps a convex set `s` into itself. -/
theorem Convex.image_homothety_subset {s : Set E} (hs : Convex ℝ s) {x : E} (hx : x ∈ s) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : AffineMap.homothety x t '' s ⊆ s := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  rw [add_comm]
  exact hs.add_smul_sub_mem hx hz ht

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedSpace ℝ F] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- **Hölder's inequality on a subset**: the `L¹` norm of `g` on a set `S ⊆ B` is at most
`‖g‖_{L^p(B)} μ(S)^{1 − 1/p}`, for `1 ≤ p`. -/
theorem MeasureTheory.lintegral_enorm_le_eLpNorm_mul_measure_rpow {g : E → F}
    (hg : AEStronglyMeasurable g μ) {p : ℝ≥0} (hp : 1 ≤ p) {S B : Set E} (hSB : S ⊆ B) :
    ∫⁻ y in S, ‖g y‖ₑ ∂μ
      ≤ eLpNorm g p (μ.restrict B) * μ S ^ (1 - 1 / (p : ℝ)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  rw [← eLpNorm_one_eq_lintegral_enorm (hg.restrict)]
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hg.restrict).trans ?_
  rw [Measure.restrict_apply_univ]
  have h : 1 / (1 : ℝ≥0∞).toReal - 1 / (p : ℝ≥0∞).toReal = 1 - 1 / (p : ℝ) := by simp
  rw [h]
  exact mul_le_mul' (eLpNorm_mono_measure _ (Measure.restrict_mono hSB le_rfl)) le_rfl

/-- The integral `∫_0^1 t^{−N/p} dt = 1/(1 − N/p)` for `N < p`, as a Lebesgue integral. -/
theorem MeasureTheory.lintegral_Ioc_ofReal_rpow_neg_div {N : ℕ} {p : ℝ} (hp : N < p) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(N / p)))
      = ENNReal.ofReal (1 / (1 - N / p)) := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hexp : -1 < -(N / p) := by
    rw [neg_lt_neg_iff, div_lt_one hp0]
    exact hp
  have hint : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(N / p))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hexp
  rw [← ofReal_integral_eq_lintegral_ofReal hint.1 (ae_restrict_of_forall_mem measurableSet_Ioc
    fun t ht ↦ Real.rpow_nonneg ht.1.le _), ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hexp)]
  congr 1
  have h1 : -(N / p) + 1 = 1 - N / p := by ring
  rw [h1, Real.one_rpow, Real.zero_rpow (sub_pos.2 ((div_lt_one hp0).2 hp)).ne', sub_zero, one_div]

/-- The real identity `(t^N)⁻¹ (t^N)^{1 − 1/p} = t^{−N/p}` for `t > 0`. -/
theorem Real.inv_pow_mul_pow_rpow_eq_rpow_neg_div {t : ℝ} (ht : 0 < t) (N : ℕ) {p : ℝ}
    (hp : p ≠ 0) : (t ^ N)⁻¹ * (t ^ N) ^ (1 - 1 / p) = t ^ (-(N / p)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  field_simp
  ring

/-- **Morrey's mean estimate on a ball, `C¹` case**: for `u ∈ C¹`, a closed ball `B` of radius
`r > 0`, `x ∈ B` and `1 ≤ p`, `N < p`,
`∫_B ‖u z − u x‖ dz ≤ (2r / (1 − N/p)) μ(B)^{1 − 1/p} ‖∇u‖_{L^p(B)}`.
This is the estimate (27) of [brezis2011functional] §9.3, proof of Theorem 9.12, with the mean
over `B` replaced by the integral of `‖u z − u x‖` (the mean value at the end is not needed)
and the cube replaced by a ball. -/
theorem ContDiff.lintegral_enorm_sub_le_of_mem_closedBall (hu : ContDiff ℝ 1 u) {p : ℝ≥0}
    (hp1 : 1 ≤ p) (hp : finrank ℝ E < p) {c x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ closedBall c r) :
    ∫⁻ z in closedBall c r, ‖u z - u x‖ₑ ∂μ
      ≤ ENNReal.ofReal (2 * r / (1 - finrank ℝ E / p)) * (μ (closedBall c r) ^ (1 - 1 / (p : ℝ))
        * eLpNorm (fderiv ℝ u) p (μ.restrict (closedBall c r))) := by
  set N := finrank ℝ E with hN
  set B := closedBall c r with hB
  set G : E → ℝ≥0∞ := fun y ↦ ‖fderiv ℝ u y‖ₑ with hGdef
  have hGm : Measurable G := (hu.continuous_fderiv one_ne_zero).enorm.measurable
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hpN : (0 : ℝ) < 1 - N / p := sub_pos.2 ((div_lt_one hp0).2 hp)
  have hexp : (0 : ℝ) ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]
    exact_mod_cast hp1
  have hBm : MeasurableSet B := measurableSet_closedBall
  -- Step 1: the segment bound, integrated over the ball
  have h1 : ∫⁻ z in B, ‖u z - u x‖ₑ ∂μ ≤ ENNReal.ofReal (2 * r)
      * ∫⁻ z in B, (∫⁻ t in Ioc (0 : ℝ) 1, G (AffineMap.homothety x t z)) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ((ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz ↦ ?_))
    refine (hu.enorm_sub_le_enorm_mul_lintegral_fderiv x z).trans (mul_le_mul' ?_ (le_of_eq ?_))
    · rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖z - x‖ ≤ ‖z - c‖ + ‖c - x‖ := norm_sub_le_norm_sub_add_norm_sub z c x
        _ ≤ r + r := add_le_add (mem_closedBall_iff_norm.1 hz)
          (by rw [norm_sub_rev]; exact mem_closedBall_iff_norm.1 hx)
        _ = 2 * r := by ring
    · refine setLIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
      simp [hGdef, AffineMap.homothety_apply, add_comm]
  -- Step 2: Fubini
  have h2 : ∫⁻ z in B, (∫⁻ t in Ioc (0 : ℝ) 1, G (AffineMap.homothety x t z)) ∂μ
      = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in B, G (AffineMap.homothety x t z) ∂μ := by
    refine lintegral_lintegral_swap (f := fun z (t : ℝ) ↦ G (AffineMap.homothety x t z)) ?_
    have hc : Continuous (Function.uncurry fun z (t : ℝ) ↦ AffineMap.homothety x t z) := by
      simp only [Function.uncurry_def, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      fun_prop
    exact (hGm.comp hc.measurable).aemeasurable
  -- Step 3: for each `t ∈ (0, 1]`, change variables and apply Hölder's inequality
  have h3 : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ z in B, G (AffineMap.homothety x t z) ∂μ
      ≤ ENNReal.ofReal (t ^ (-(N / (p : ℝ))))
        * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B)) := by
    intro t ht
    rw [setLIntegral_comp_homothety hGm x ht.1.ne' hBm]
    have himg : AffineMap.homothety x t '' B ⊆ B :=
      (convex_closedBall c r).image_homothety_subset hx ⟨ht.1.le, ht.2⟩
    have hmeas : μ (AffineMap.homothety x t '' B) = ENNReal.ofReal (t ^ N) * μ B := by
      rw [Measure.addHaar_image_homothety, abs_of_nonneg (pow_nonneg ht.1.le _)]
    calc ENNReal.ofReal |(t ^ N)⁻¹| * ∫⁻ y in AffineMap.homothety x t '' B, G y ∂μ
        ≤ ENNReal.ofReal |(t ^ N)⁻¹| * (eLpNorm (fderiv ℝ u) p (μ.restrict B)
            * μ (AffineMap.homothety x t '' B) ^ (1 - 1 / (p : ℝ))) :=
          mul_le_mul' le_rfl (lintegral_enorm_le_eLpNorm_mul_measure_rpow
            (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable hp1 himg)
      _ = ENNReal.ofReal (t ^ (-(N / (p : ℝ))))
            * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B)) := by
          rw [hmeas, ENNReal.mul_rpow_of_nonneg _ _ hexp,
            abs_of_nonneg (inv_nonneg.2 (pow_nonneg ht.1.le _)),
            ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ht.1.le _) hexp, mul_comm (eLpNorm _ _ _),
            mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg ht.1.le _)),
            Real.inv_pow_mul_pow_rpow_eq_rpow_neg_div ht.1 N hp0.ne']
  -- Step 4: integrate in `t`
  have hm : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ (-(N / (p : ℝ)))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  calc ∫⁻ z in B, ‖u z - u x‖ₑ ∂μ
      ≤ ENNReal.ofReal (2 * r)
          * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in B, G (AffineMap.homothety x t z) ∂μ := by
        rw [← h2]
        exact h1
    _ ≤ ENNReal.ofReal (2 * r) * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(N / (p : ℝ))))
          * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B)) :=
        mul_le_mul' le_rfl (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall h3)))
    _ = ENNReal.ofReal (2 * r) * (ENNReal.ofReal (1 / (1 - N / p))
          * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B))) := by
        rw [lintegral_mul_const _ hm, lintegral_Ioc_ofReal_rpow_neg_div (N := N) (p := (p : ℝ)) hp]
    _ = ENNReal.ofReal (2 * r / (1 - N / p))
          * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_one_div]

variable (μ) in
/-- **The constant of Morrey's inequality** on a normed space `E` of dimension `N` with Haar
measure `μ`, for the exponent `p > N`: `C(p, N) = 4 μ(B(0,1))^{−1/p} / (1 − N/p)`, so that
`‖u x − u y‖ ≤ C ‖x − y‖^{1 − N/p} ‖∇u‖_p` (`ContDiff.enorm_sub_le_of_lt`). It is finite
(`morreyConst_ne_top`). The book's constant `2 · 2^{1−N/p}/(1 − N/p)` is for cubes; balls give
this one. -/
def MeasureTheory.morreyConst (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 / (1 - finrank ℝ E / p)) * μ (ball (0 : E) 1) ^ (-(1 / p))

variable (μ) in
/-- **The constant of the sup bound of Morrey's theorem**:
`C'(p, N) = 2 μ(B(0,1))^{−1/p}/(1 − N/p)`, so that `‖u x‖ ≤ C' (‖u‖_p + ‖∇u‖_p)`
(`ContDiff.enorm_le_of_lt`). Finite (`morreySupConst_ne_top`). -/
def MeasureTheory.morreySupConst (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 / (1 - finrank ℝ E / p)) * μ (ball (0 : E) 1) ^ (-(1 / p))

variable (μ) in
omit [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The constant of Morrey's inequality is finite. -/
theorem MeasureTheory.morreyConst_ne_top (p : ℝ) : morreyConst μ p ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg' (measure_ball_pos μ 0 one_pos) measure_ball_lt_top.ne)

variable (μ) in
omit [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The constant of the sup bound of Morrey's theorem is finite. -/
theorem MeasureTheory.morreySupConst_ne_top (p : ℝ) : morreySupConst μ p ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg' (measure_ball_pos μ 0 one_pos) measure_ball_lt_top.ne)

omit [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- `μ(B)^{1 − 1/p} / μ(B) = μ(B)^{−1/p}` for a ball `B` of radius `r > 0`. -/
theorem MeasureTheory.Measure.closedBall_rpow_div_self {x : E} {r : ℝ} (hr : 0 < r) (p : ℝ) :
    μ (closedBall x r) ^ (1 - 1 / p) / μ (closedBall x r) = μ (closedBall x r) ^ (-(1 / p)) := by
  have h0 : μ (closedBall x r) ≠ 0 := (measure_closedBall_pos μ x hr).ne'
  have ht : μ (closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [div_eq_mul_inv, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ h0 ht]
  congr 1
  ring

/-- **Morrey's inequality (25) for a `C¹` function**: for `1 ≤ p`, `N < p` and all `x y`,
`‖u x − u y‖ ≤ C(p, N) ‖x − y‖^{1 − N/p} ‖∇u‖_{L^p(B(x, ‖x − y‖))}`, with
`C(p, N) = morreyConst μ p`. Both points lie in the closed ball `B` of centre `x` and radius
`‖x − y‖`, `‖u x − u y‖ ≤ ‖u z − u x‖ + ‖u z − u y‖` for every `z ∈ B`, and integrating over
`B` reduces to `ContDiff.lintegral_enorm_sub_le_of_mem_closedBall` twice.
[brezis2011functional] §9.3, proof of Theorem 9.12, the inequality (25) for `u ∈ C_c^1`. -/
theorem ContDiff.enorm_sub_le_of_lt (hu : ContDiff ℝ 1 u) {p : ℝ≥0} (hp1 : 1 ≤ p)
    (hp : finrank ℝ E < p) (x y : E) :
    ‖u x - u y‖ₑ ≤ morreyConst μ p * ENNReal.ofReal (‖x - y‖ ^ (1 - finrank ℝ E / (p : ℝ)))
      * eLpNorm (fderiv ℝ u) p (μ.restrict (closedBall x ‖x - y‖)) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  set N := finrank ℝ E with hN
  set r := ‖x - y‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  set B := closedBall x r with hB
  have hxB : x ∈ B := mem_closedBall_self hr0.le
  have hyB : y ∈ B := by
    rw [hB, mem_closedBall, dist_eq_norm, norm_sub_rev]
  have hμB0 : μ B ≠ 0 := (measure_closedBall_pos μ x hr0).ne'
  have hμBt : μ B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hpN : (0 : ℝ) < 1 - N / p := sub_pos.2 ((div_lt_one hp0).2 hp)
  have hcont : Continuous u := hu.continuous
  -- the triangle inequality integrated over the ball
  have key : ‖u x - u y‖ₑ * μ B ≤ ∫⁻ z in B, ‖u z - u x‖ₑ ∂μ + ∫⁻ z in B, ‖u z - u y‖ₑ ∂μ := by
    rw [← lintegral_add_left (f := fun z ↦ ‖u z - u x‖ₑ)
      (hcont.sub continuous_const).enorm.measurable, ← setLIntegral_const]
    refine lintegral_mono fun z ↦ ?_
    calc ‖u x - u y‖ₑ = ‖(u z - u y) - (u z - u x)‖ₑ := by congr 1; abel
      _ ≤ ‖u z - u y‖ₑ + ‖u z - u x‖ₑ := enorm_sub_le
      _ = ‖u z - u x‖ₑ + ‖u z - u y‖ₑ := add_comm _ _
  have hx' := hu.lintegral_enorm_sub_le_of_mem_closedBall (μ := μ) hp1 hp hr0 hxB
  have hy' := hu.lintegral_enorm_sub_le_of_mem_closedBall (μ := μ) hp1 hp hr0 hyB
  rw [← hB] at hx' hy'
  set D := eLpNorm (fderiv ℝ u) p (μ.restrict B) with hD
  have h2 : ‖u x - u y‖ₑ * μ B
      ≤ ENNReal.ofReal (4 * r / (1 - N / p)) * (μ B ^ (1 - 1 / (p : ℝ)) * D) := by
    refine (key.trans (add_le_add hx' hy')).trans (le_of_eq ?_)
    rw [← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two]
    congr 2
    ring
  have h3 : ‖u x - u y‖ₑ
      ≤ ENNReal.ofReal (4 * r / (1 - N / p)) * (μ B ^ (1 - 1 / (p : ℝ)) * D) / μ B :=
    (ENNReal.le_div_iff_mul_le (Or.inl hμB0) (Or.inl hμBt)).2 h2
  have h4 : ENNReal.ofReal (4 * r / (1 - N / p)) * (μ B ^ (1 - 1 / (p : ℝ)) * D) / μ B
      = ENNReal.ofReal (4 * r / (1 - N / p)) * (μ B ^ (-(1 / (p : ℝ))) * D) := by
    rw [← Measure.closedBall_rpow_div_self (μ := μ) hr0, ← hB, ENNReal.div_eq_inv_mul,
      ENNReal.div_eq_inv_mul]
    ring
  refine (h3.trans_eq h4).trans (le_of_eq ?_)
  -- the measure of the ball, and the powers of `r`
  have hμB : μ B = ENNReal.ofReal (r ^ N) * μ (ball 0 1) := Measure.addHaar_closedBall μ x hr0.le
  have hrN : ENNReal.ofReal (r ^ N) ^ (-(1 / (p : ℝ))) = ENNReal.ofReal (r ^ (-(N / (p : ℝ)))) := by
    rw [ENNReal.ofReal_rpow_of_pos (pow_pos hr0 _), ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    congr 2
    ring
  have hr' : 4 * r / (1 - N / p) * r ^ (-(N / (p : ℝ)))
      = 4 / (1 - N / p) * r ^ (1 - N / (p : ℝ)) := by
    rw [show (1 - N / (p : ℝ)) = 1 + -(N / (p : ℝ)) by ring, Real.rpow_add hr0, Real.rpow_one]
    ring
  rw [morreyConst, hμB, ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne,
    hrN, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hr',
    ENNReal.ofReal_mul (by positivity)]
  ring

/-- **The sup bound (24) for a `C¹` function**: for `1 ≤ p`, `N < p` and all `x`,
`‖u x‖ ≤ C'(p, N) (‖u‖_p + ‖∇u‖_p)`, with `C'(p, N) = morreySupConst μ p`: on the closed unit
ball `B` about `x`, `‖u x‖ ≤ ‖u z − u x‖ + ‖u z‖` for every `z ∈ B`; integrating over `B`,
`ContDiff.lintegral_enorm_sub_le_of_mem_closedBall` bounds the first term and Hölder's
inequality the second. [brezis2011functional] §9.3, proof of Theorem 9.12, the inequality (24)
for `u ∈ C_c^1`. -/
theorem ContDiff.enorm_le_of_lt (hu : ContDiff ℝ 1 u) {p : ℝ≥0} (hp1 : 1 ≤ p)
    (hp : finrank ℝ E < p) (x : E) :
    ‖u x‖ₑ ≤ morreySupConst μ p * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) := by
  set N := finrank ℝ E with hN
  set B := closedBall x 1 with hB
  have hxB : x ∈ B := mem_closedBall_self zero_le_one
  have hμB0 : μ B ≠ 0 := (measure_closedBall_pos μ x one_pos).ne'
  have hμBt : μ B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hpN : (0 : ℝ) < 1 - N / p := sub_pos.2 ((div_lt_one hp0).2 hp)
  have hcont : Continuous u := hu.continuous
  have key : ‖u x‖ₑ * μ B ≤ ∫⁻ z in B, ‖u z - u x‖ₑ ∂μ + ∫⁻ z in B, ‖u z‖ₑ ∂μ := by
    rw [← lintegral_add_left (f := fun z ↦ ‖u z - u x‖ₑ)
      (hcont.sub continuous_const).enorm.measurable, ← setLIntegral_const]
    refine lintegral_mono fun z ↦ ?_
    calc ‖u x‖ₑ = ‖u z - (u z - u x)‖ₑ := by congr 1; abel
      _ ≤ ‖u z‖ₑ + ‖u z - u x‖ₑ := enorm_sub_le
      _ = ‖u z - u x‖ₑ + ‖u z‖ₑ := add_comm _ _
  have h1 := hu.lintegral_enorm_sub_le_of_mem_closedBall (μ := μ) hp1 hp one_pos hxB
  rw [← hB] at h1
  have h2 : ∫⁻ z in B, ‖u z‖ₑ ∂μ ≤ eLpNorm u p (μ.restrict B) * μ B ^ (1 - 1 / (p : ℝ)) :=
    lintegral_enorm_le_eLpNorm_mul_measure_rpow hcont.aestronglyMeasurable hp1 subset_rfl
  have hC : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 / (1 - N / p)) := by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ((le_div_iff₀ hpN).2 ?_)
    have : (0 : ℝ) ≤ N / p := by positivity
    linarith
  have hsum : ‖u x‖ₑ * μ B ≤ ENNReal.ofReal (2 / (1 - N / p)) * μ B ^ (1 - 1 / (p : ℝ))
      * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) := by
    set C := ENNReal.ofReal (2 / (1 - N / p)) with hCdef
    calc ‖u x‖ₑ * μ B ≤ (∫⁻ z in B, ‖u z - u x‖ₑ ∂μ) + ∫⁻ z in B, ‖u z‖ₑ ∂μ := key
      _ ≤ ENNReal.ofReal (2 * 1 / (1 - N / p))
            * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B))
          + eLpNorm u p (μ.restrict B) * μ B ^ (1 - 1 / (p : ℝ)) := add_le_add h1 h2
      _ ≤ C * μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p μ
          + C * μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm u p μ := by
          refine add_le_add ?_ ?_
          · rw [mul_one, mul_assoc]
            exact mul_le_mul' le_rfl
              (mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self))
          · calc eLpNorm u p (μ.restrict B) * μ B ^ (1 - 1 / (p : ℝ))
                ≤ 1 * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm u p μ) := by
                  rw [one_mul, mul_comm]
                  exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)
              _ ≤ C * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm u p μ) := mul_le_mul' hC le_rfl
              _ = C * μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm u p μ := by ring
      _ = C * μ B ^ (1 - 1 / (p : ℝ)) * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) := by ring
  have h3 : ‖u x‖ₑ ≤ ENNReal.ofReal (2 / (1 - N / p)) * μ B ^ (1 - 1 / (p : ℝ))
      * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) / μ B :=
    (ENNReal.le_div_iff_mul_le (Or.inl hμB0) (Or.inl hμBt)).2 hsum
  have h4 : ENNReal.ofReal (2 / (1 - N / p)) * μ B ^ (1 - 1 / (p : ℝ))
      * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) / μ B
      = ENNReal.ofReal (2 / (1 - N / p)) * (μ B ^ (-(1 / (p : ℝ)))
        * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ)) := by
    rw [← Measure.closedBall_rpow_div_self (μ := μ) one_pos, ← hB, ENNReal.div_eq_inv_mul,
      ENNReal.div_eq_inv_mul]
    ring
  refine (h3.trans_eq h4).trans (le_of_eq ?_)
  have hμB : μ B = μ (ball 0 1) := by
    rw [hB, Measure.addHaar_closedBall μ x zero_le_one, one_pow, ENNReal.ofReal_one, one_mul]
  rw [morreySupConst, hμB, mul_assoc]

end MorreyC1

/-! ### Theorem 9.12: Morrey's theorem on `W^{1,p}(ℝ^N)`, `N < p < ∞` -/

section ENNRealLimits

/-- If `a ≤ K (b + δ)` for every `δ > 0` and `K < ∞`, then `a ≤ K b`. -/
theorem ENNReal.le_mul_of_forall_pos_le_mul_add {a b K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * (b + δ)) : a ≤ K * b := by
  have hlim : Tendsto (fun δ : ℝ≥0∞ ↦ K * (b + δ)) (𝓝[>] 0) (𝓝 (K * b)) := by
    have : Tendsto (fun δ : ℝ≥0∞ ↦ b + δ) (𝓝[>] 0) (𝓝 (b + 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.add tendsto_id)
    rw [add_zero] at this
    exact ENNReal.Tendsto.const_mul this (Or.inr hK)
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ ↦ h δ hδ)

/-- `‖f‖_p ≤ ‖f − g‖_p + ‖g‖_p` for `1 ≤ p`. -/
theorem MeasureTheory.eLpNorm_le_eLpNorm_sub_add {α G : Type*} [MeasurableSpace α] {ν : Measure α}
    [NormedAddCommGroup G] {p : ℝ≥0∞} (hp : 1 ≤ p) (f g : α → G) :
    eLpNorm f p ν ≤ eLpNorm (fun x ↦ f x - g x) p ν + eLpNorm g p ν := by
  have hsplit : f = (fun x ↦ f x - g x) + g := by
    funext x
    simp
  conv_lhs => rw [hsplit]
  exact eLpNorm_add_le hp

end ENNRealLimits

section Morrey

open scoped BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {w : E → E →L[ℝ] F}

/-- **Theorem 9.12 (Morrey), with Remarks 11 and 12, on `W^{1,p}(ℝ^N)` for `N < p < ∞`**: a
function `f ∈ W^{1,p}(ℝ^N)` with weak derivative `w` has a continuous representative `ũ`
(Remark 11) which is Hölder continuous of exponent `1 − N/p`,
`‖ũ x − ũ y‖ ≤ C ‖x − y‖^{1 − N/p} ‖w‖_p` (the inequality (25)), bounded by
`‖ũ x‖ ≤ C' (‖f‖_p + ‖w‖_p)` (the inequality (24), `W^{1,p} ⊂ L^∞` with continuous injection),
and tends to `0` at infinity (Remark 12). The constants are `morreyConst μ p` and
`morreySupConst μ p`.

The proof is the "standard density argument" made explicit: the smooth compactly supported
approximants `u_n → f`, `∇u_n → w` in `L^p` satisfy (24) for their differences, so they form a
Cauchy sequence in the Banach space of bounded continuous functions; the limit `ũ` is continuous,
equals `f` almost everywhere (both are limits of `u_n`, uniformly and in `L^p`), inherits (25)
and (24) in the limit, and is a uniform limit of compactly supported functions.
[brezis2011functional] Theorem 9.12, Remark 11, Remark 12. -/
theorem HasWeakFDerivOn.exists_continuous_holderWith_ae_eq (h : HasWeakFDerivOn f w ⊤ μ)
    {p : ℝ≥0} (hp1 : 1 ≤ p) (hp : finrank ℝ E < p) (hf : MemLp f p μ) (hw : MemLp w p μ) :
    ∃ ũ : E → F, Continuous ũ ∧ f =ᵐ[μ] ũ ∧
      (∀ x y, ‖ũ x - ũ y‖ₑ ≤ morreyConst μ p
        * ENNReal.ofReal (‖x - y‖ ^ (1 - finrank ℝ E / (p : ℝ))) * eLpNorm w p μ) ∧
      (∀ x, ‖ũ x‖ₑ ≤ morreySupConst μ p * (eLpNorm f p μ + eLpNorm w p μ)) ∧
      Tendsto ũ (cocompact E) (𝓝 0) := by
  have hp1' : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp1
  obtain ⟨u, hus, huc, hu0, hu1⟩ :=
    h.exists_seq_contDiff_hasCompactSupport_tendsto_top hp1' ENNReal.coe_ne_top hf hw
  have hu1' : ∀ n, ContDiff ℝ 1 (u n) := fun n ↦ (hus n).of_le (by simp)
  -- the approximants as bounded continuous functions
  choose M hM using fun n ↦ (huc n).exists_bound_of_continuous (hus n).continuous
  let U : ℕ → E →ᵇ F := fun n ↦
    BoundedContinuousFunction.ofNormedAddCommGroup (u n) (hus n).continuous (M n) (hM n)
  have hU : ∀ n x, U n x = u n x := fun n x ↦ rfl
  set C' := morreySupConst μ p with hC'
  have hC't : C' ≠ ⊤ := morreySupConst_ne_top μ p
  -- the sup bound (24) for a difference of two approximants
  have hdiff : ∀ n m x, ‖u n x - u m x‖ₑ ≤ C' * (eLpNorm (u n - u m) p μ
      + eLpNorm (fun x ↦ fderiv ℝ (u n) x - fderiv ℝ (u m) x) p μ) := by
    intro n m x
    have := ((hu1' n).sub (hu1' m)).enorm_le_of_lt (μ := μ) hp1 hp x
    have e : (fderiv ℝ fun x ↦ u n x - u m x) = fun x ↦ fderiv ℝ (u n) x - fderiv ℝ (u m) x := by
      funext y
      exact fderiv_sub ((hu1' n).differentiable one_ne_zero y)
        ((hu1' m).differentiable one_ne_zero y)
    rw [e] at this
    exact this
  -- the approximants are Cauchy in the sup norm
  have hcauchy : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ0, hδ1, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ < 1 ∧ (C' * (4 * δ)).toReal < ε := by
      have : Tendsto (fun δ : ℝ≥0∞ ↦ (C' * (4 * δ)).toReal) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun δ : ℝ≥0∞ ↦ C' * (4 * δ)) (𝓝[>] 0) (𝓝 (C' * (4 * 0))) :=
          tendsto_nhdsWithin_of_tendsto_nhds
            (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul tendsto_id (Or.inr (by simp)))
              (Or.inr hC't))
        rw [mul_zero, mul_zero] at h1
        exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      have h1 : ∀ᶠ δ : ℝ≥0∞ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
      have h2 : ∀ᶠ δ : ℝ≥0∞ in 𝓝[>] 0, δ < 1 :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
      obtain ⟨δ, hδ, hδε, hδ1⟩ := ((this.eventually (gt_mem_nhds hε)).and (h1.and h2)).exists
      exact ⟨δ, hδε, hδ1, hδ⟩
    have hev0 : ∀ᶠ n in atTop, eLpNorm (u n - f) p μ ≤ δ := ENNReal.tendsto_nhds_zero.1 hu0 δ hδ0
    have hev1 : ∀ᶠ n in atTop, eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p μ ≤ δ :=
      ENNReal.tendsto_nhds_zero.1 hu1 δ hδ0
    obtain ⟨N₀, hN₀⟩ := (hev0.and hev1).exists_forall_of_atTop
    refine ⟨N₀, fun m hm n hn ↦ ?_⟩
    have hbound : dist (U m) (U n) ≤ (C' * (4 * δ)).toReal := by
      refine (BoundedContinuousFunction.dist_le ENNReal.toReal_nonneg).2 fun x ↦ ?_
      rw [hU, hU, dist_eq_norm, ← toReal_enorm]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top hC't
        (ENNReal.mul_ne_top (by simp) hδ1.ne_top)) ((hdiff m n x).trans ?_)
      refine mul_le_mul' le_rfl ?_
      have e1 : eLpNorm (u m - u n) p μ ≤ δ + δ := by
        have : u m - u n = (u m - f) - (u n - f) := by abel
        rw [this]
        exact (eLpNorm_sub_le hp1').trans (add_le_add (hN₀ m hm).1 (hN₀ n hn).1)
      have e2 : eLpNorm (fun x ↦ fderiv ℝ (u m) x - fderiv ℝ (u n) x) p μ ≤ δ + δ := by
        have : (fun x ↦ fderiv ℝ (u m) x - fderiv ℝ (u n) x)
            = (fun x ↦ fderiv ℝ (u m) x - w x) - fun x ↦ fderiv ℝ (u n) x - w x := by
          funext x
          simp
        rw [this]
        exact (eLpNorm_sub_le hp1').trans (add_le_add (hN₀ m hm).2 (hN₀ n hn).2)
      calc eLpNorm (u m - u n) p μ + eLpNorm (fun x ↦ fderiv ℝ (u m) x - fderiv ℝ (u n) x) p μ
          ≤ (δ + δ) + (δ + δ) := add_le_add e1 e2
        _ = 4 * δ := by ring
    exact hbound.trans_lt hδ
  -- the uniform limit
  obtain ⟨Ũ, hŨ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hpt : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (Ũ x)) := fun x ↦
    ((continuous_eval_const x).tendsto Ũ).comp hŨ
  refine ⟨Ũ, Ũ.continuous, ?_, ?_, ?_, ?_⟩
  -- it equals `f` almost everywhere
  · have hmeas : TendstoInMeasure μ u atTop f :=
      tendstoInMeasure_of_tendsto_eLpNorm (by exact_mod_cast (zero_lt_one.trans_le hp1).ne') hu0
    obtain ⟨ns, hns_mono, hns⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hns] with x hx
    exact tendsto_nhds_unique hx ((hpt x).comp hns_mono.tendsto_atTop)
  -- the Hölder estimate (25)
  · intro x y
    refine ENNReal.le_mul_of_forall_pos_le_mul_add
      (ENNReal.mul_ne_top (morreyConst_ne_top μ p) ENNReal.ofReal_ne_top) fun δ hδ ↦ ?_
    have hlim : Tendsto (fun n ↦ ‖u n x - u n y‖ₑ) atTop (𝓝 ‖Ũ x - Ũ y‖ₑ) :=
      (continuous_enorm.tendsto _).comp ((hpt x).sub (hpt y))
    refine le_of_tendsto hlim ?_
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hu1 δ hδ] with n hn
    refine ((hu1' n).enorm_sub_le_of_lt (μ := μ) hp1 hp x y).trans (mul_le_mul' le_rfl ?_)
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    refine (eLpNorm_le_eLpNorm_sub_add hp1' _ w).trans ?_
    rw [add_comm]
    exact add_le_add le_rfl hn
  -- the sup bound (24)
  · intro x
    refine ENNReal.le_mul_of_forall_pos_le_mul_add hC't fun δ hδ ↦ ?_
    have hlim : Tendsto (fun n ↦ ‖u n x‖ₑ) atTop (𝓝 ‖Ũ x‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hpt x)
    refine le_of_tendsto hlim ?_
    have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hu0 (δ / 2) hδ2,
      ENNReal.tendsto_nhds_zero.1 hu1 (δ / 2) hδ2] with n hn0 hn1
    refine ((hu1' n).enorm_le_of_lt (μ := μ) hp1 hp x).trans (mul_le_mul' le_rfl ?_)
    calc eLpNorm (u n) p μ + eLpNorm (fderiv ℝ (u n)) p μ
        ≤ (eLpNorm (fun x ↦ u n x - f x) p μ + eLpNorm f p μ)
          + (eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p μ + eLpNorm w p μ) :=
          add_le_add (eLpNorm_le_eLpNorm_sub_add hp1' _ f) (eLpNorm_le_eLpNorm_sub_add hp1' _ w)
      _ ≤ (δ / 2 + eLpNorm f p μ) + (δ / 2 + eLpNorm w p μ) :=
          add_le_add (add_le_add hn0 le_rfl) (add_le_add hn1 le_rfl)
      _ = eLpNorm f p μ + eLpNorm w p μ + δ := by
          rw [add_add_add_comm, ENNReal.add_halves, add_comm]
  -- the decay at infinity (Remark 12)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.1 hŨ ε hε).exists
    refine mem_cocompact.2 ⟨tsupport (u n), huc n, fun x hx ↦ ?_⟩
    have hx0 : u n x = 0 := image_eq_zero_of_notMem_tsupport hx
    change dist ‖Ũ x‖ 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    calc ‖Ũ x‖ = ‖U n x - Ũ x‖ := by rw [hU, hx0, zero_sub, norm_neg]
      _ ≤ dist (U n) Ũ := by rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist x
      _ < ε := hn

end Morrey

/-! ### Morrey's theorem on the typed space, and the map into the bounded continuous functions -/

section TypedMorrey

open scoped BoundedContinuousFunction
open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Theorem 9.12 (Morrey) on the typed space `W^{1,p}(ℝ^N)`, `N < p < ∞`**: every
`u ∈ W^{1,p}(ℝ^N)` has a continuous representative `ũ` with
`‖ũ x − ũ y‖ ≤ C ‖x − y‖^{1 − N/p} ∑_i ‖∂_i u‖_p`, `‖ũ x‖ ≤ C' (N + 1) ‖u‖`, and `ũ → 0` at
infinity. [brezis2011functional] Theorem 9.12, Remarks 11–12. -/
theorem SobolevEuclidean.exists_continuous_ae_eq_of_lt (hp : N < p)
    (u : SobolevEuclidean N 1 p ⊤) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧ fn u =ᵐ[volume] ũ ∧
      (∀ x y, ‖ũ x - ũ y‖ₑ ≤ morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p
        * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
        * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖) ∧
      (∀ x, ‖ũ x‖ₑ ≤ morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)
        * ENNReal.ofReal ‖u‖) ∧
      Tendsto ũ (cocompact (EuclideanSpace ℝ (Fin N))) (𝓝 0) := by
  have hp1 : 1 ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hN : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  obtain ⟨w, hw, hwp, hwle⟩ := SobolevEuclidean.exists_hasWeakFDerivOn u
  obtain ⟨ũ, hc, hae, hhold, hsup, hdecay⟩ := hw.exists_continuous_holderWith_ae_eq hp1
    (by rw [hN]; exact_mod_cast hp) (SobolevEuclidean.memLp_fn u) hwp
  refine ⟨ũ, hc, hae, fun x y ↦ ?_, fun x ↦ ?_, hdecay⟩
  · rw [hN] at hhold
    exact (hhold x y).trans (mul_le_mul' le_rfl hwle)
  · refine (hsup x).trans ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    calc eLpNorm (fn u) p volume + eLpNorm w p volume
        ≤ ENNReal.ofReal ‖u‖ + N * ENNReal.ofReal ‖u‖ :=
          add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
            (hwle.trans (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u))
      _ = (N + 1) * ENNReal.ofReal ‖u‖ := by ring

/-- The sup bound of Morrey's theorem on the typed space, in real form:
`‖ũ x‖ ≤ (C' (N + 1)).toReal ‖u‖`. -/
theorem SobolevEuclidean.norm_le_of_enorm_le_morreySupConst
    (u : SobolevEuclidean N 1 p ⊤) {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (h : ∀ x, ‖ũ x‖ₑ ≤ morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)
      * ENNReal.ofReal ‖u‖) (x : EuclideanSpace ℝ (Fin N)) :
    ‖ũ x‖ ≤ (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal
      * ‖u‖ := by
  have hK : morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (morreySupConst_ne_top _ _) (by simp)
  rw [← toReal_enorm, ← ENNReal.toReal_ofReal (norm_nonneg u), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) (h x)

/-- **The continuous representative of `u ∈ W^{1,p}(ℝ^N)`, `N < p < ∞`**, as a bounded
continuous function: a choice of the `ũ` of `SobolevEuclidean.exists_continuous_ae_eq_of_lt`.
Two continuous functions that agree almost everywhere agree everywhere, so the choice is
unique, and the map `u ↦ ũ` is linear (`SobolevEuclidean.toBoundedContinuousMapL`). -/
noncomputable def SobolevEuclidean.contRep (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    EuclideanSpace ℝ (Fin N) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose
    (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.1 _
    (SobolevEuclidean.norm_le_of_enorm_le_morreySupConst u
      (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.2.1)

/-- The continuous representative is a representative. -/
theorem SobolevEuclidean.fn_ae_eq_contRep (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    fn u =ᵐ[volume] SobolevEuclidean.contRep hp u :=
  (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.1

/-- The Hölder estimate (25) for the continuous representative. -/
theorem SobolevEuclidean.enorm_contRep_sub_le (hp : N < p) (u : SobolevEuclidean N 1 p ⊤)
    (x y : EuclideanSpace ℝ (Fin N)) :
    ‖SobolevEuclidean.contRep hp u x - SobolevEuclidean.contRep hp u y‖ₑ
      ≤ morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p
        * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
        * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ :=
  (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.1 x y

/-- The sup bound (24) for the continuous representative. -/
theorem SobolevEuclidean.norm_contRep_apply_le (hp : N < p) (u : SobolevEuclidean N 1 p ⊤)
    (x : EuclideanSpace ℝ (Fin N)) :
    ‖SobolevEuclidean.contRep hp u x‖
      ≤ (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal
        * ‖u‖ :=
  SobolevEuclidean.norm_le_of_enorm_le_morreySupConst u
    (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.2.1 x

/-- The continuous representative tends to `0` at infinity (Remark 12). -/
theorem SobolevEuclidean.tendsto_contRep_cocompact (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    Tendsto (SobolevEuclidean.contRep hp u) (cocompact (EuclideanSpace ℝ (Fin N))) (𝓝 0) :=
  (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.2.2

/-- A bounded continuous function almost everywhere equal to `fn u` is the continuous
representative: continuous functions agreeing almost everywhere for Lebesgue measure agree. -/
theorem SobolevEuclidean.contRep_eq_of_ae_eq (hp : N < p) (u : SobolevEuclidean N 1 p ⊤)
    {g : EuclideanSpace ℝ (Fin N) →ᵇ ℝ} (hg : fn u =ᵐ[volume] g) :
    SobolevEuclidean.contRep hp u = g :=
  BoundedContinuousFunction.ext <| congrFun <| Measure.eq_of_ae_eq (μ := volume)
    ((SobolevEuclidean.fn_ae_eq_contRep hp u).symm.trans hg)
    (SobolevEuclidean.contRep hp u).continuous g.continuous

/-- The sup norm of the continuous representative is bounded by `C ‖u‖`. -/
theorem SobolevEuclidean.norm_contRep_le (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    ‖SobolevEuclidean.contRep hp u‖
      ≤ (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal
        * ‖u‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).2
    (SobolevEuclidean.norm_contRep_apply_le hp u)

variable (N p) in
/-- **`W^{1,p}(ℝ^N) ⊂ L^∞(ℝ^N)` with continuous injection, `N < p < ∞`, as a bounded linear
map into the bounded continuous functions**: `u ↦ ũ`, the continuous representative of Morrey's
theorem, with `‖ũ‖_∞ ≤ C ‖u‖`. This is the map along which [brezis2011functional] Theorem 9.12
reads `W^{1,p}(ℝ^N) ⊂ L^∞(ℝ^N)`, and the pattern of `SobolevInterval.toContinuousMap`. -/
noncomputable def SobolevEuclidean.toBoundedContinuousMapL (hp : N < p) :
    SobolevEuclidean N 1 p ⊤ →L[ℝ] (EuclideanSpace ℝ (Fin N) →ᵇ ℝ) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := SobolevEuclidean.contRep hp
      map_add' := fun u v ↦ SobolevEuclidean.contRep_eq_of_ae_eq hp (u + v) <| by
        refine (eventuallyEq_restrict_coe_top_iff.1 (fn_add u v)).trans ?_
        filter_upwards [SobolevEuclidean.fn_ae_eq_contRep hp u,
          SobolevEuclidean.fn_ae_eq_contRep hp v] with x hu hv
        simp [hu, hv]
      map_smul' := fun c u ↦ SobolevEuclidean.contRep_eq_of_ae_eq hp (c • u) <| by
        refine (eventuallyEq_restrict_coe_top_iff.1 (fn_smul c u)).trans ?_
        filter_upwards [SobolevEuclidean.fn_ae_eq_contRep hp u] with x hu
        simp [hu] }
    ⟨_, SobolevEuclidean.norm_contRep_le hp⟩

/-- `SobolevEuclidean.toBoundedContinuousMapL` is the continuous representative. -/
@[simp]
theorem SobolevEuclidean.toBoundedContinuousMapL_apply (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    SobolevEuclidean.toBoundedContinuousMapL N p hp u = SobolevEuclidean.contRep hp u :=
  rfl

/-- `SobolevEuclidean.toBoundedContinuousMapL u` is `fn u` almost everywhere. -/
theorem SobolevEuclidean.fn_ae_eq_toBoundedContinuousMapL (hp : N < p)
    (u : SobolevEuclidean N 1 p ⊤) :
    fn u =ᵐ[volume] SobolevEuclidean.toBoundedContinuousMapL N p hp u :=
  SobolevEuclidean.fn_ae_eq_contRep hp u

/-- The bound `‖toBoundedContinuousMapL u‖ ≤ C ‖u‖` of [brezis2011functional] Theorem 9.12 (24). -/
theorem SobolevEuclidean.norm_toBoundedContinuousMapL_apply_le (hp : N < p)
    (u : SobolevEuclidean N 1 p ⊤) :
    ‖SobolevEuclidean.toBoundedContinuousMapL N p hp u‖
      ≤ (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal
        * ‖u‖ :=
  SobolevEuclidean.norm_contRep_le hp u

/-- `SobolevEuclidean.toBoundedContinuousMapL` is injective: the representative determines the
element. -/
theorem SobolevEuclidean.toBoundedContinuousMapL_injective (hp : N < p) :
    Function.Injective (SobolevEuclidean.toBoundedContinuousMapL N p hp) := fun u v huv ↦ by
  refine ext_of_fn_ae_eq (eventuallyEq_restrict_coe_top_iff.2 ?_)
  refine (SobolevEuclidean.fn_ae_eq_toBoundedContinuousMapL hp u).trans ?_
  rw [huv]
  exact (SobolevEuclidean.fn_ae_eq_toBoundedContinuousMapL hp v).symm

/-- **`W^{1,p}(ℝ^N) ↪ C_b(ℝ^N)` is a continuous embedding for `N < p < ∞`**:
[brezis2011functional] Theorem 9.12, "`W^{1,p}(ℝ^N) ⊂ L^∞(ℝ^N)` with continuous injection". -/
theorem SobolevEuclidean.isContinuousEmbedding_toBoundedContinuousMapL (hp : N < p) :
    IsContinuousEmbedding (SobolevEuclidean.toBoundedContinuousMapL N p hp).toLinearMap :=
  ⟨SobolevEuclidean.toBoundedContinuousMapL_injective hp, _,
    SobolevEuclidean.norm_toBoundedContinuousMapL_apply_le hp⟩

/-- **`W^{1,p}(ℝ^N) ⊆ L^∞(ℝ^N)` for `N < p < ∞`**: the function of `u` is essentially bounded,
with `‖fn u‖_∞ ≤ C ‖u‖`. -/
theorem SobolevEuclidean.eLpNorm_fn_top_le_of_lt (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    eLpNorm (fn u) ⊤ volume ≤ morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p
      * (N + 1) * ENNReal.ofReal ‖u‖ := by
  rw [eLpNorm_congr_ae (SobolevEuclidean.fn_ae_eq_contRep hp u)]
  refine (eLpNorm_le_of_ae_enorm_bound
    (SobolevEuclidean.contRep hp u).continuous.aestronglyMeasurable (Eventually.of_forall
      (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.2.1)).trans ?_
  simp

/-- **`W^{1,p}(ℝ^N) ⊆ L^∞(ℝ^N)` for `N < p < ∞`**, the membership. -/
theorem SobolevEuclidean.memLp_fn_top_of_lt (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    MemLp (fn u) ⊤ volume :=
  memLp_iff.2 ((SobolevEuclidean.eLpNorm_fn_top_le_of_lt hp u).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (morreySupConst_ne_top _ _).lt_top (by simp))
      ENNReal.ofReal_lt_top))

end TypedMorrey

/-! ### Corollary 9.11: the limiting case `p = N`

For `u ∈ C_c^1`, the `p = 1` Gagliardo–Nirenberg–Sobolev inequality applied to `‖u‖^γ`, `γ > 1`,
gives the inequality (20) of [brezis2011functional] §9.3,
`‖u‖_{γN'}^γ ≤ C γ ‖u‖_{(γ−1)N'}^{γ−1} ‖∇u‖_N`, where `N' = N/(N − 1)`; Young's inequality turns
it into (21), `‖u‖_{γN'} ≤ K (‖u‖_{(γ−1)N'} + ‖∇u‖_N)`, and the induction on `γ = N, N + 1, …`
with the interpolation inequality between consecutive exponents covers every `q ∈ [N, ∞)`. -/

section LimitingCase

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F}

/-- **The inequality (20) of [brezis2011functional] §9.3, proof of Corollary 9.11**: for
`u ∈ C_c^1(ℝ^N)`, `N ≥ 2`, `N' = N/(N − 1)` and `γ > 1`,
`‖u‖_{γN'}^γ ≤ C γ ‖u‖_{(γ−1)N'}^{γ−1} ‖∇u‖_N`, with `C = eLpNormLESNormFDerivOneConst μ N'`:
Mathlib's `p = 1` inequality applied to `‖u‖^γ`, whose derivative is bounded by
`γ ‖u‖^{γ−1} ‖∇u‖`, followed by Hölder's inequality with the exponents `N'` and `N`. -/
theorem ContDiff.eLpNorm_rpow_le_of_hasCompactSupport (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) (hN : 2 ≤ finrank ℝ E) {γ : ℝ≥0} (hγ : 1 < γ) :
    eLpNorm u ((γ * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ ^ (γ : ℝ)
      ≤ eLpNormLESNormFDerivOneConst μ (NNReal.conjExponent (finrank ℝ E)) * γ
        * eLpNorm u (((γ - 1) * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ
          ^ ((γ : ℝ) - 1)
        * eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ := by
  set n : ℕ := finrank ℝ E with hn
  set n' : ℝ≥0 := NNReal.conjExponent n with hn'
  have hn1 : (1 : ℝ≥0) < n := by exact_mod_cast hN
  have hnn' : NNReal.HolderConjugate n n' := .conjExponent hn1
  have hn0 : (n : ℝ≥0) ≠ 0 := hnn'.pos.ne'
  have hn'0 : n' ≠ 0 := hnn'.symm.pos.ne'
  have hn'r : (0 : ℝ) < n' := hnn'.symm.coe.pos
  have hγ0 : γ ≠ 0 := (zero_lt_one.trans hγ).ne'
  have hγ0r : (γ : ℝ) ≠ 0 := by exact_mod_cast hγ0
  have hγ1 : (0 : ℝ) < (γ : ℝ) - 1 := by
    rw [sub_pos]
    exact_mod_cast hγ
  have hγ1' : γ - 1 ≠ 0 := (tsub_pos_of_lt hγ).ne'
  have hγ1c : ((γ - 1 : ℝ≥0) : ℝ) = (γ : ℝ) - 1 := NNReal.coe_sub hγ.le
  have hu' : Continuous u := hu.continuous
  have hd : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  -- the function `‖u‖^γ`
  set v : E → ℝ := fun x ↦ ‖u x‖ ^ (γ : ℝ) with hv
  have hvs : ContDiff ℝ 1 v := hu.norm_rpow (by exact_mod_cast hγ)
  have hvc : HasCompactSupport v := h2u.norm.rpow_const hγ0r
  set C := eLpNormLESNormFDerivOneConst μ n' with hC
  -- the left side is the `L^{N'}` norm of `v`
  have h1 : eLpNorm u ((γ * n' : ℝ≥0) : ℝ≥0∞) μ ^ (γ : ℝ) = eLpNorm v n' μ := by
    rw [eLpNorm_nnreal_eq_lintegral (mul_ne_zero hγ0 hn'0) hu'.aestronglyMeasurable,
      eLpNorm_nnreal_eq_lintegral hn'0 hvs.continuous.aestronglyMeasurable, ← ENNReal.rpow_mul]
    congr 1
    · refine lintegral_congr fun x ↦ ?_
      rw [hv, Real.enorm_rpow_of_nonneg (norm_nonneg _) (NNReal.coe_nonneg γ), enorm_norm,
        ← ENNReal.rpow_mul, NNReal.coe_mul]
    · push_cast
      field_simp
  -- measurability of the two factors of Hölder's inequality
  have hm1 : Measurable fun x ↦ ‖u x‖ₑ ^ ((γ : ℝ) - 1) := by
    borelize F
    exact (hu'.measurable.enorm).pow_const _
  have hm2 : Measurable fun x ↦ ‖fderiv ℝ u x‖ₑ := hfd.measurable.enorm
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hnn'.symm.coe hm1.aemeasurable
    hm2.aemeasurable
  simp only [Pi.mul_apply] at hholder
  calc eLpNorm u ((γ * n' : ℝ≥0) : ℝ≥0∞) μ ^ (γ : ℝ) = eLpNorm v n' μ := h1
    _ ≤ C * eLpNorm (fderiv ℝ v) 1 μ := eLpNorm_le_eLpNorm_fderiv_one μ hvs hvc hnn'
    _ = C * ∫⁻ x, ‖fderiv ℝ v x‖ₑ ∂μ := by
        rw [eLpNorm_one_eq_lintegral_enorm (hvs.continuous_fderiv one_ne_zero).aestronglyMeasurable]
    _ ≤ C * (γ * ∫⁻ x, ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖ₑ ∂μ) := by
        rw [← lintegral_const_mul (r := (γ : ℝ≥0∞))
          (f := fun x ↦ ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖ₑ) (hm1.mul hm2)]
        refine mul_le_mul' le_rfl (lintegral_mono fun x ↦ ?_)
        simpa only [mul_assoc] using enorm_fderiv_norm_rpow_le hd hγ (x := x)
    _ ≤ C * (γ * ((∫⁻ x, (‖u x‖ₑ ^ ((γ : ℝ) - 1)) ^ (n' : ℝ) ∂μ) ^ (1 / (n' : ℝ))
          * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (n : ℝ) ∂μ) ^ (1 / (n : ℝ)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hholder)
    _ = C * γ * eLpNorm u (((γ - 1) * n' : ℝ≥0) : ℝ≥0∞) μ ^ ((γ : ℝ) - 1)
          * eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ := by
        rw [eLpNorm_nnreal_eq_lintegral hn0 hfd.aestronglyMeasurable,
          eLpNorm_nnreal_eq_lintegral (mul_ne_zero hγ1' hn'0) hu'.aestronglyMeasurable,
          ← ENNReal.rpow_mul, mul_assoc, mul_assoc]
        have hexp : 1 / (((γ - 1) * n' : ℝ≥0) : ℝ) * ((γ : ℝ) - 1) = 1 / (n' : ℝ) := by
          rw [NNReal.coe_mul, hγ1c]
          field_simp
        have hint : ∫⁻ x, ‖u x‖ₑ ^ (((γ - 1) * n' : ℝ≥0) : ℝ) ∂μ
            = ∫⁻ x, (‖u x‖ₑ ^ ((γ : ℝ) - 1)) ^ (n' : ℝ) ∂μ :=
          lintegral_congr fun x ↦ by rw [← ENNReal.rpow_mul, NNReal.coe_mul, hγ1c]
        rw [hexp, hint, NNReal.coe_natCast]

/-- **The inequality (21)**: for `γ > 1` there is a finite `K` with
`‖u‖_{γN'} ≤ K (‖u‖_{(γ−1)N'} + ‖∇u‖_N)` for every `u ∈ C_c^1(ℝ^N)`, `N ≥ 2` — from (20) by
Young's inequality in the form `b^θ c^{1−θ} ≤ b + c`. [brezis2011functional] §9.3, proof of
Corollary 9.11, (21). -/
theorem MeasureTheory.exists_forall_eLpNorm_le_of_hasCompactSupport_of_one_lt (hN : 2 ≤ finrank ℝ E)
    {γ : ℝ≥0} (hγ : 1 < γ) : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : E → F, ContDiff ℝ 1 u →
      HasCompactSupport u →
      eLpNorm u ((γ * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ
        ≤ K * (eLpNorm u (((γ - 1) * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ) := by
  set n' : ℝ≥0 := NNReal.conjExponent (finrank ℝ E) with hn'
  set C : ℝ≥0∞ := eLpNormLESNormFDerivOneConst μ n' * γ with hC
  have hγr : (0 : ℝ) < γ := by exact_mod_cast zero_lt_one.trans hγ
  have hγr1 : (0 : ℝ) < (γ : ℝ) - 1 := by
    rw [sub_pos]
    exact_mod_cast hγ
  refine ⟨C ^ (1 / (γ : ℝ)), ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top), fun u hu h2u ↦ ?_⟩
  have h20 := hu.eLpNorm_rpow_le_of_hasCompactSupport (μ := μ) h2u hN hγ
  rw [← hn', ← hC] at h20
  set A := eLpNorm u ((γ * n' : ℝ≥0) : ℝ≥0∞) μ with hA
  set B := eLpNorm u (((γ - 1) * n' : ℝ≥0) : ℝ≥0∞) μ with hB
  set D := eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ with hD
  calc A = (A ^ (γ : ℝ)) ^ (1 / (γ : ℝ)) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hγr.ne', ENNReal.rpow_one]
    _ ≤ (C * B ^ ((γ : ℝ) - 1) * D) ^ (1 / (γ : ℝ)) := ENNReal.rpow_le_rpow h20 (by positivity)
    _ = C ^ (1 / (γ : ℝ)) * (B ^ (((γ : ℝ) - 1) / γ) * D ^ (1 - ((γ : ℝ) - 1) / γ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_assoc]
        congr 3
        · ring
        · field_simp
          ring
    _ ≤ C ^ (1 / (γ : ℝ)) * (B + D) :=
        mul_le_mul' le_rfl (ENNReal.rpow_mul_rpow_one_sub_le_add _ _ (by positivity)
          ((div_le_one hγr).2 (by linarith)))

/-- **The induction of Corollary 9.11 on `C_c^1`**: for every `m`, there is a finite `K` with
`‖u‖_{(N − 1 + m) N'} ≤ K (‖u‖_N + ‖∇u‖_N)` for all `u ∈ C_c^1(ℝ^N)`, `N ≥ 2` — the case
`m = 0` is `(N − 1) N' = N`, and each step is the inequality (21) with `γ = N − 1 + m + 1`.
[brezis2011functional] §9.3, proof of Corollary 9.11, "reiterating this argument with
`m = N + 1`, `m = N + 2`, etc.". -/
theorem MeasureTheory.exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank_aux
    (hN : 2 ≤ finrank ℝ E) (m : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u (((finrank ℝ E - 1 + m : ℕ) * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ
        ≤ K * (eLpNorm u ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ) := by
  set n : ℕ := finrank ℝ E with hn
  set n' : ℝ≥0 := NNReal.conjExponent n with hn'
  have hn1 : (1 : ℝ≥0) < n := by exact_mod_cast hN
  have hnn' : NNReal.HolderConjugate n n' := .conjExponent hn1
  induction m with
  | zero =>
    refine ⟨1, ENNReal.one_ne_top, fun u _ _ ↦ ?_⟩
    have : ((n - 1 + 0 : ℕ) : ℝ≥0) * n' = n := by
      rw [add_zero, Nat.cast_tsub, Nat.cast_one, hnn'.sub_one_mul_conj]
    rw [this, one_mul]
    exact le_self_add
  | succ m ih =>
    obtain ⟨K, hK, hKu⟩ := ih
    have hγ : (1 : ℝ≥0) < ((n - 1 + (m + 1) : ℕ) : ℝ≥0) := by
      have : 2 ≤ n - 1 + (m + 1) := by omega
      exact_mod_cast this
    obtain ⟨K', hK', hK'u⟩ :=
      exists_forall_eLpNorm_le_of_hasCompactSupport_of_one_lt (μ := μ) (F := F) hN hγ
    refine ⟨K' * (K + 1), ENNReal.mul_ne_top hK' (ENNReal.add_ne_top.2 ⟨hK, ENNReal.one_ne_top⟩),
      fun u hu h2u ↦ ?_⟩
    have hsub : ((n - 1 + (m + 1) : ℕ) : ℝ≥0) - 1 = ((n - 1 + m : ℕ) : ℝ≥0) := by
      rw [show n - 1 + (m + 1) = (n - 1 + m) + 1 by omega, Nat.cast_succ, add_tsub_cancel_right]
    calc eLpNorm u (((n - 1 + (m + 1) : ℕ) * n' : ℝ≥0) : ℝ≥0∞) μ
        ≤ K' * (eLpNorm u (((((n - 1 + (m + 1) : ℕ) : ℝ≥0) - 1) * n' : ℝ≥0) : ℝ≥0∞) μ
            + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) := hK'u u hu h2u
      _ ≤ K' * (K * (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ)
            + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) := by
          rw [hsub]
          exact mul_le_mul' le_rfl (add_le_add (hKu u hu h2u) le_rfl)
      _ ≤ K' * (K + 1) * (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ
            + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) := by
          rw [mul_assoc, add_mul, one_mul]
          exact mul_le_mul' le_rfl (add_le_add le_rfl le_add_self)

/-- **Corollary 9.11 on `C_c^1`**: for `N ≥ 2` and `q ≥ N` there is a finite `K` with
`‖u‖_q ≤ K (‖u‖_N + ‖∇u‖_N)` for all `u ∈ C_c^1(ℝ^N)`: the inequality for the exponent
`(N − 1 + m) N' ≥ q` of the induction, interpolated with the exponent `N`.
[brezis2011functional] §9.3, proof of Corollary 9.11, the inequality (23). -/
theorem MeasureTheory.exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank
    (hN : 2 ≤ finrank ℝ E) {q : ℝ≥0} (hq : (finrank ℝ E : ℝ≥0) ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u q μ ≤ K * (eLpNorm u ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ
        + eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ) := by
  set n : ℕ := finrank ℝ E with hn
  set n' : ℝ≥0 := NNReal.conjExponent n with hn'
  have hn1 : (1 : ℝ≥0) < n := by exact_mod_cast hN
  have hnn' : NNReal.HolderConjugate n n' := .conjExponent hn1
  have hn'1 : 1 ≤ n' := hnn'.symm.lt.le
  obtain ⟨K, hK, hKu⟩ :=
    exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank_aux (μ := μ) (F := F) hN ⌈q⌉₊
  have hqle : q ≤ ((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) * n' := by
    calc q ≤ (⌈q⌉₊ : ℝ≥0) := Nat.le_ceil q
      _ ≤ ((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) := by exact_mod_cast Nat.le_add_left _ _
      _ = ((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) * 1 := (mul_one _).symm
      _ ≤ ((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) * n' := mul_le_mul' le_rfl hn'1
  refine ⟨1 + K, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hK⟩, fun u hu h2u ↦ ?_⟩
  have hn0 : ((n : ℝ≥0) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnn'.pos.ne'
  calc eLpNorm u q μ
      ≤ eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm u ((((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) * n' : ℝ≥0) : ℝ≥0∞) μ :=
        eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le hu.continuous.aestronglyMeasurable hn0
          (by exact_mod_cast hq) (by exact_mod_cast hqle)
    _ ≤ (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ)
          + K * (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) :=
        add_le_add le_self_add (hKu u hu h2u)
    _ = (1 + K) * (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) := by ring

variable [CompleteSpace F]

/-- **Corollary 9.11 (the limiting case `p = N`) on `W^{1,N}(ℝ^N)`**: for `N ≥ 2` and every
`q ∈ [N, ∞)` there is a finite `K = K(q, N)` such that every `f ∈ W^{1,N}(ℝ^N)` with weak
derivative `w` satisfies `‖f‖_q ≤ K (‖f‖_N + ‖w‖_N)` — in particular `W^{1,N}(ℝ^N) ⊆ L^q(ℝ^N)`
with continuous injection. The inequality on `C_c^1` extends by density and Fatou's lemma as in
Theorem 9.9. [brezis2011functional] Corollary 9.11. -/
theorem MeasureTheory.exists_forall_eLpNorm_le_of_eq_finrank (hN : 2 ≤ finrank ℝ E) {q : ℝ≥0}
    (hq : (finrank ℝ E : ℝ≥0) ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (f : E → F) (w : E → E →L[ℝ] F), HasWeakFDerivOn f w ⊤ μ →
      MemLp f ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ → MemLp w ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ →
      eLpNorm f q μ ≤ K * (eLpNorm f ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ
        + eLpNorm w ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ) := by
  set n : ℕ := finrank ℝ E with hn
  obtain ⟨K, hK, hKu⟩ :=
    exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank (μ := μ) (F := F) hN hq
  refine ⟨K, hK, fun f w h hf hw ↦ ?_⟩
  have hn1 : (1 : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast (one_le_two.trans hN)
  obtain ⟨u, hus, huc, hu0, hu1⟩ :=
    h.exists_seq_contDiff_hasCompactSupport_tendsto_top hn1 ENNReal.coe_ne_top hf hw
  have hmeas : TendstoInMeasure μ u atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hn1).ne' hu0
  obtain ⟨ns, hns_mono, hns⟩ := hmeas.exists_seq_tendsto_ae
  refine ENNReal.le_mul_of_forall_pos_le_mul_add hK fun δ hδ ↦ ?_
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  have hev0 := ENNReal.tendsto_nhds_zero.1 hu0 (δ / 2) hδ2
  have hev1 := ENNReal.tendsto_nhds_zero.1 hu1 (δ / 2) hδ2
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun n ↦ u (ns n)) ?_
    (fun n ↦ (hus _).continuous.aestronglyMeasurable) hf.aestronglyMeasurable hns
  filter_upwards [hns_mono.tendsto_atTop.eventually hev0,
    hns_mono.tendsto_atTop.eventually hev1] with k hk0 hk1
  refine (hKu _ ((hus _).of_le (by simp)) (huc _)).trans (mul_le_mul' le_rfl ?_)
  calc eLpNorm (u (ns k)) ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm (fderiv ℝ (u (ns k))) ((n : ℝ≥0) : ℝ≥0∞) μ
      ≤ (eLpNorm (fun x ↦ u (ns k) x - f x) ((n : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm f ((n : ℝ≥0) : ℝ≥0∞) μ)
        + (eLpNorm (fun x ↦ fderiv ℝ (u (ns k)) x - w x) ((n : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm w ((n : ℝ≥0) : ℝ≥0∞) μ) :=
        add_le_add (eLpNorm_le_eLpNorm_sub_add hn1 _ f) (eLpNorm_le_eLpNorm_sub_add hn1 _ w)
    _ ≤ (δ / 2 + eLpNorm f ((n : ℝ≥0) : ℝ≥0∞) μ) + (δ / 2 + eLpNorm w ((n : ℝ≥0) : ℝ≥0∞) μ) :=
        add_le_add (add_le_add hk0 le_rfl) (add_le_add hk1 le_rfl)
    _ = eLpNorm f ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm w ((n : ℝ≥0) : ℝ≥0∞) μ + δ := by
        rw [add_add_add_comm, ENNReal.add_halves, add_comm]

end LimitingCase

section TypedLimitingCase

open SobolevMultiIndex

variable {N : ℕ} {q : ℝ≥0}

/-- **Corollary 9.11 on the typed space, the bound**: for `N ≥ 2` and `q ∈ [N, ∞)` there is a
finite `K = K(q, N)` with `‖u‖_q ≤ K ‖u‖` for every `u ∈ W^{1,N}(ℝ^N)`.
[brezis2011functional] Corollary 9.11. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N 1 N ⊤,
      eLpNorm (fn u) q volume ≤ K * ENNReal.ofReal ‖u‖ := by
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  obtain ⟨K, hK, hKu⟩ := exists_forall_eLpNorm_le_of_eq_finrank
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin N)))) (F := ℝ) (by rw [hfin]; exact hN)
    (q := q) (by rw [hfin]; exact hq)
  rw [hfin, ENNReal.coe_natCast] at hKu
  refine ⟨K * (N + 1), ENNReal.mul_ne_top hK (by simp), fun u ↦ ?_⟩
  obtain ⟨w, hw, hwp, hwle⟩ := SobolevEuclidean.exists_hasWeakFDerivOn u
  refine (hKu _ w hw (SobolevEuclidean.memLp_fn u) hwp).trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  calc eLpNorm (fn u) N volume + eLpNorm w N volume
      ≤ ENNReal.ofReal ‖u‖ + N * ENNReal.ofReal ‖u‖ :=
        add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
          (hwle.trans (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u))
    _ = (N + 1) * ENNReal.ofReal ‖u‖ := by ring

/-- **`W^{1,N}(ℝ^N) ⊆ L^q(ℝ^N)` for `N ≥ 2`, `q ∈ [N, ∞)`**: [brezis2011functional]
Corollary 9.11, the inclusion. -/
theorem SobolevEuclidean.memLp_fn_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))] (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) (u : SobolevEuclidean N 1 N ⊤) : MemLp (fn u) q volume := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  exact memLp_iff.2 ((hKu u).trans_lt (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top))

/-- **Corollary 9.11 (the limiting case `p = N`)**: `W^{1,N}(ℝ^N) ↪ L^q(ℝ^N)` with continuous
injection for `N ≥ 2` and every `q ∈ [N, ∞)`, along `SobolevMultiIndex.toLpₗ`.
[brezis2011functional] Corollary 9.11. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using
          SobolevEuclidean.memLp_fn_of_eq_finrank hN hq u) := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  refine isContinuousEmbedding_toLpₗ _ (C := K.toReal) fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (norm_nonneg u), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) ?_
  exact (eLpNorm_restrict_coe_top (fn u) (q : ℝ≥0∞)).trans_le (hKu u)

end TypedLimitingCase

/-! ### Lifting an `L^q` bound at order `m` to `W^{1,q}` at order `m + 1` -/

section Lift

open SobolevMultiIndex

variable {N m : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **The inductive step of Corollary 9.13**: if `W^{m,p}(ℝ^N) ⊆ L^q(ℝ^N)` with the bound
`‖fn v‖_q ≤ K ‖v‖`, then every `u ∈ W^{m+1,p}(ℝ^N)` is (almost everywhere) the function of an
element `w ∈ W^{1,q}(ℝ^N)` with `‖w‖ ≤ (N + 1) K ‖u‖` — `u` and its partial derivatives `∂_i u`
lie in `W^{m,p}(ℝ^N)`, hence in `L^q(ℝ^N)`, and `∂_i u` is the weak derivative of `u`.
[brezis2011functional] Corollary 9.13, proof ("repeated applications"). -/
theorem SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le {K : ℝ≥0∞}
    (hK : K ≠ ⊤)
    (h : ∀ v : SobolevEuclidean N m p ⊤, eLpNorm (fn v) q volume ≤ K * ENNReal.ofReal ‖v‖)
    (u : SobolevEuclidean N (m + 1) p ⊤) :
    ∃ w : SobolevEuclidean N 1 q ⊤, fn w =ᵐ[volume] fn u ∧ ‖w‖ ≤ (N + 1) * K.toReal * ‖u‖ := by
  classical
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : SobolevEuclidean N m p ⊤,
      v₀ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p ⊤ volume
        (Nat.le_succ m) u :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin N → SobolevEuclidean N m p ⊤,
      v = fun i ↦ partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p ⊤ volume i u :=
    ⟨_, rfl⟩
  have hv₀fn : fn v₀ = fn u := by rw [hv₀]; rfl
  have hv₀n : ‖v₀‖ ≤ ‖u‖ := by rw [hv₀]; exact norm_toLowerOrder_le _ u
  have hvn : ∀ i, ‖v i‖ ≤ ‖u‖ := fun i ↦ by rw [hv]; exact norm_partialDeriv_le i u
  have hvd : ∀ i, HasWeakIteratedLineDerivOn ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
      (fn u) (fn (v i)) ⊤ volume := fun i ↦ by
    rw [hv]
    exact hasWeakIteratedLineDerivOn_fn_partialDeriv i u
  -- the `L^q` bounds
  have hK' : ∀ v : SobolevEuclidean N m p ⊤,
      eLpNorm (fn v) q volume ≤ ENNReal.ofReal (K.toReal * ‖v‖) := fun v ↦ by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
    exact h v
  have h0 : MemLp (fn u) q volume := by
    rw [← hv₀fn]
    exact memLp_iff.2 ((hK' v₀).trans_lt ENNReal.ofReal_lt_top)
  have hi : ∀ i, MemLp (fn (v i)) q volume := fun i ↦
    memLp_iff.2 ((hK' (v i)).trans_lt ENNReal.ofReal_lt_top)
  -- `fn u ∈ W^{1,q}(ℝ^N)`
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn u) 1 q ⊤
      volume := by
    refine ⟨by simpa [Measure.restrict_coe_top] using h0, fun β hβ ↦ ?_⟩
    rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with hz | ⟨i, hi'⟩
    · obtain rfl : β = 0 := congrArg Subtype.val hz
      refine ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
        ((h0.locallyIntegrable hq1).locallyIntegrableOn _), ?_⟩
      simpa [Measure.restrict_coe_top] using h0
    · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi'
      refine ⟨fn (v i), (hvd i).of_perm (multiIndexTuple_single_perm _ i).symm, ?_⟩
      simpa [Measure.restrict_coe_top] using hi i
  obtain ⟨w, hw⟩ := hmem.exists_sobolevMultiIndex
  rw [eventuallyEq_restrict_coe_top_iff] at hw
  refine ⟨w, hw, ?_⟩
  -- the bound on `‖w‖` through its components
  have hw0 : ‖weakDeriv w 0‖ ≤ K.toReal * ‖u‖ := by
    rw [Lp.norm_def, eLpNorm_restrict_coe_top, weakDeriv_zero]
    calc (eLpNorm (fn w) q volume).toReal
        = (eLpNorm (fn u) q volume).toReal := by rw [eLpNorm_congr_ae hw]
      _ ≤ (ENNReal.ofReal (K.toReal * ‖v₀‖)).toReal := by
          rw [← hv₀fn]
          exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hK' v₀)
      _ ≤ K.toReal * ‖u‖ := by
          rw [ENNReal.toReal_ofReal (by positivity)]
          exact mul_le_mul_of_nonneg_left hv₀n ENNReal.toReal_nonneg
  have hwi : ∀ i, ‖weakDeriv w (MultiIndexLE.single i)‖ ≤ K.toReal * ‖u‖ := fun i ↦ by
    have hwd : HasWeakIteratedLineDerivOn ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
        (fn u) (weakDeriv w (MultiIndexLE.single i)) ⊤ volume :=
      ((hasWeakIteratedLineDerivOn w (MultiIndexLE.single i)).of_perm
        (multiIndexTuple_single_perm _ i)).congr_ae (eventuallyEq_restrict_coe_top_iff.2 hw)
        (Filter.EventuallyEq.refl _ _)
    have hae : (weakDeriv w (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume] fn (v i) := by
      filter_upwards [hwd.ae_eq (hvd i)] with x hx
      exact hx (by simp)
    rw [Lp.norm_def, eLpNorm_restrict_coe_top, eLpNorm_congr_ae hae]
    calc (eLpNorm (fn (v i)) q volume).toReal
        ≤ (ENNReal.ofReal (K.toReal * ‖v i‖)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hK' (v i))
      _ ≤ K.toReal * ‖u‖ := by
          rw [ENNReal.toReal_ofReal (by positivity)]
          exact mul_le_mul_of_nonneg_left (hvn i) ENNReal.toReal_nonneg
  calc ‖w‖ ≤ ∑ α, ‖weakDeriv w α‖ := by
        rw [← Submodule.norm_coe]
        exact PiLp.norm_le_sum_norm _
    _ = ‖weakDeriv w 0‖ + ∑ i, ‖weakDeriv w (MultiIndexLE.single i)‖ :=
        MultiIndexLE.sum_univ_one _
    _ ≤ K.toReal * ‖u‖ + ∑ _i : Fin N, K.toReal * ‖u‖ :=
        add_le_add hw0 (Finset.sum_le_sum fun i _ ↦ hwi i)
    _ = (N + 1) * K.toReal * ‖u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The inductive step of Corollary 9.15**: if `W^{m,p}(Ω) ⊆ L^q(Ω)` with the bound
`‖fn v‖_{L^q(Ω)} ≤ K ‖v‖`, then every `u ∈ W^{m+1,p}(Ω)` is (almost everywhere on `Ω`) the
function of an element `w ∈ W^{1,q}(Ω)` with `‖w‖ ≤ (N + 1) K ‖u‖`, the domain form of
`SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le`.
[brezis2011functional] Corollary 9.15, proof ("repeated application of Corollary 9.14"). -/
theorem SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ v : SobolevEuclidean N m p Ω, eLpNorm (fn v) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖v‖)
    (u : SobolevEuclidean N (m + 1) p Ω) :
    ∃ w : SobolevEuclidean N 1 q Ω,
      fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u ∧
      ‖w‖ ≤ (N + 1) * K.toReal * ‖u‖ := by
  classical
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : SobolevEuclidean N m p Ω,
      v₀ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume
        (Nat.le_succ m) u :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin N → SobolevEuclidean N m p Ω,
      v = fun i ↦ partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume i u :=
    ⟨_, rfl⟩
  have hv₀fn : fn v₀ = fn u := by rw [hv₀]; rfl
  have hv₀n : ‖v₀‖ ≤ ‖u‖ := by rw [hv₀]; exact norm_toLowerOrder_le _ u
  have hvn : ∀ i, ‖v i‖ ≤ ‖u‖ := fun i ↦ by rw [hv]; exact norm_partialDeriv_le i u
  have hvd : ∀ i, HasWeakIteratedLineDerivOn ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
      (fn u) (fn (v i)) Ω volume := fun i ↦ by
    rw [hv]
    exact hasWeakIteratedLineDerivOn_fn_partialDeriv i u
  -- the `L^q` bounds
  have hK' : ∀ v : SobolevEuclidean N m p Ω,
      eLpNorm (fn v) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        ≤ ENNReal.ofReal (K.toReal * ‖v‖) := fun v ↦ by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
    exact h v
  have h0 : MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    rw [← hv₀fn]
    exact memLp_iff.2 ((hK' v₀).trans_lt ENNReal.ofReal_lt_top)
  have hi : ∀ i, MemLp (fn (v i)) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    fun i ↦ memLp_iff.2 ((hK' (v i)).trans_lt ENNReal.ofReal_lt_top)
  -- `fn u ∈ W^{1,q}(Ω)`
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn u) 1 q Ω
      volume := by
    refine ⟨h0, fun β hβ ↦ ?_⟩
    rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with hz | ⟨i, hi'⟩
    · obtain rfl : β = 0 := congrArg Subtype.val hz
      exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
        (h0.locallyIntegrableOn hq1), h0⟩
    · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi'
      exact ⟨fn (v i), (hvd i).of_perm (multiIndexTuple_single_perm _ i).symm, hi i⟩
  obtain ⟨w, hw⟩ := hmem.exists_sobolevMultiIndex
  refine ⟨w, hw, ?_⟩
  -- the bound on `‖w‖` through its components
  have hw0 : ‖weakDeriv w 0‖ ≤ K.toReal * ‖u‖ := by
    rw [Lp.norm_def, weakDeriv_zero]
    calc (eLpNorm (fn w) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        = (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
          rw [eLpNorm_congr_ae hw]
      _ ≤ (ENNReal.ofReal (K.toReal * ‖v₀‖)).toReal := by
          rw [← hv₀fn]
          exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hK' v₀)
      _ ≤ K.toReal * ‖u‖ := by
          rw [ENNReal.toReal_ofReal (by positivity)]
          exact mul_le_mul_of_nonneg_left hv₀n ENNReal.toReal_nonneg
  have hwi : ∀ i, ‖weakDeriv w (MultiIndexLE.single i)‖ ≤ K.toReal * ‖u‖ := fun i ↦ by
    have hwd : HasWeakIteratedLineDerivOn ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
        (fn u) (weakDeriv w (MultiIndexLE.single i)) Ω volume :=
      ((hasWeakIteratedLineDerivOn w (MultiIndexLE.single i)).of_perm
        (multiIndexTuple_single_perm _ i)).congr_ae hw (Filter.EventuallyEq.refl _ _)
    have hae : (weakDeriv w (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn (v i) :=
      (ae_restrict_iff' Ω.isOpen.measurableSet).2 (hwd.ae_eq (hvd i))
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    calc (eLpNorm (fn (v i)) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ (ENNReal.ofReal (K.toReal * ‖v i‖)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hK' (v i))
      _ ≤ K.toReal * ‖u‖ := by
          rw [ENNReal.toReal_ofReal (by positivity)]
          exact mul_le_mul_of_nonneg_left (hvn i) ENNReal.toReal_nonneg
  calc ‖w‖ ≤ ∑ α, ‖weakDeriv w α‖ := by
        rw [← Submodule.norm_coe]
        exact PiLp.norm_le_sum_norm _
    _ = ‖weakDeriv w 0‖ + ∑ i, ‖weakDeriv w (MultiIndexLE.single i)‖ :=
        MultiIndexLE.sum_univ_one _
    _ ≤ K.toReal * ‖u‖ + ∑ _i : Fin N, K.toReal * ‖u‖ :=
        add_le_add hw0 (Finset.sum_le_sum fun i _ ↦ hwi i)
    _ = (N + 1) * K.toReal * ‖u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Lift

/-! ### Corollary 9.13: the `L^q` clauses of the higher-order embeddings -/

section HigherOrderLq

open SobolevMultiIndex

variable {N : ℕ}

/-- **The first-order embeddings of §9.3.A in one statement**: for `1 ≤ p ≤ q < ∞` with
`1/p − 1/N ≤ 1/q`, and `N ≥ 2` or `p > 1`, there is a finite `K` with `‖u‖_q ≤ K ‖u‖` for every
`u ∈ W^{1,p}(ℝ^N)`: Corollary 9.10 when `p < N` (then `q ≤ p*`), Corollary 9.11 when `p = N`,
and Morrey's theorem interpolated with `L^p` when `p > N`. The case `N = 1 = p`, where
Corollary 9.11 does not apply, is excluded. [brezis2011functional] Corollary 9.13 at `m = 1`. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N 1 p ⊤,
      eLpNorm (fn u) q volume ≤ K * ENNReal.ofReal ‖u‖ := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hq0 : (0 : ℝ) < q := hp0.trans_le (by exact_mod_cast hpq)
  rcases lt_trichotomy p N with hpN | hpN | hpN
  · -- `p < N`: Corollary 9.10
    have hN0 : (0 : ℝ) < N := hp0.trans (by exact_mod_cast hpN)
    obtain ⟨p', hp'⟩ : ∃ p' : ℝ≥0, (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ :=
      ⟨(p⁻¹ - (N : ℝ≥0)⁻¹)⁻¹, by
        rw [NNReal.coe_inv, NNReal.coe_sub (by
          exact_mod_cast (inv_strictAnti₀ (zero_lt_one.trans_le hp1) hpN).le), inv_inv]
        simp⟩
    have hp'0 : (0 : ℝ) < (p' : ℝ)⁻¹ := by
      rw [hp', sub_pos]
      exact inv_strictAnti₀ hp0 (by exact_mod_cast hpN)
    have hqp' : q ≤ p' := by
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ (inv_pos.1 hp'0) hq0, hp']
      exact hq
    exact ⟨ENNReal.ofReal (1 + SobolevEuclidean.gnsConst N p * N), ENNReal.ofReal_ne_top,
      fun u ↦ by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' u⟩
  · -- `p = N`: Corollary 9.11
    subst hpN
    have hN2 : 2 ≤ N := by
      rcases hN with hN | hN
      · exact hN
      · exact_mod_cast hN
    have hfin : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
    obtain ⟨K, hK, hKu⟩ := exists_forall_eLpNorm_le_of_eq_finrank
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin N)))) (F := ℝ) (by rw [hfin]; exact hN2)
      (q := q) (by rw [hfin]; exact hpq)
    rw [hfin] at hKu
    refine ⟨K * (N + 1), ENNReal.mul_ne_top hK (by simp), fun u ↦ ?_⟩
    obtain ⟨w, hw, hwp, hwle⟩ := SobolevEuclidean.exists_hasWeakFDerivOn u
    refine (hKu _ w hw (SobolevEuclidean.memLp_fn u) hwp).trans ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    calc eLpNorm (fn u) (N : ℝ≥0) volume + eLpNorm w (N : ℝ≥0) volume
        ≤ ENNReal.ofReal ‖u‖ + N * ENNReal.ofReal ‖u‖ :=
          add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
            (hwle.trans (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u))
      _ = (N + 1) * ENNReal.ofReal ‖u‖ := by ring
  · -- `p > N`: Morrey, interpolated with `L^p`
    refine ⟨1 + morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1),
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
        ENNReal.mul_ne_top (morreySupConst_ne_top _ _) (by simp)⟩, fun u ↦ ?_⟩
    calc eLpNorm (fn u) q volume
        ≤ eLpNorm (fn u) p volume + eLpNorm (fn u) ⊤ volume :=
          eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le
            (SobolevEuclidean.memLp_fn u).aestronglyMeasurable (by exact_mod_cast hp0.ne')
            (by exact_mod_cast hpq) le_top
      _ ≤ ENNReal.ofReal ‖u‖ + morreySupConst volume p * (N + 1) * ENNReal.ofReal ‖u‖ :=
          add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
            (SobolevEuclidean.eLpNorm_fn_top_le_of_lt hpN u)
      _ = (1 + morreySupConst volume p * (N + 1)) * ENNReal.ofReal ‖u‖ := by ring

/-- The exponent `r` of the inductive step of Corollary 9.13: `1/r = max (1/p − m/N) (1/q)`,
which lies between `1/q` and `1/p` and satisfies `1/r − 1/N ≤ 1/q` when
`1/p − (m + 1)/N ≤ 1/q`. -/
theorem NNReal.exists_intermediate_sobolev_exponent {p q : ℝ≥0} (m : ℕ) (hp0 : 0 < p)
    (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - (m + 1 : ℕ) / N ≤ (q : ℝ)⁻¹) :
    ∃ r : ℝ≥0, p ≤ r ∧ r ≤ q ∧ (p : ℝ)⁻¹ - m / N ≤ (r : ℝ)⁻¹ ∧
      (r : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hq0 : (0 : ℝ) < q := hp0'.trans_le (by exact_mod_cast hpq)
  have hqinv : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.2 hq0
  have hmax : (0 : ℝ) < max ((p : ℝ)⁻¹ - m / N) (q : ℝ)⁻¹ := lt_max_of_lt_right hqinv
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ) = (max ((p : ℝ)⁻¹ - m / N) (q : ℝ)⁻¹)⁻¹ :=
    ⟨(max ((p : ℝ)⁻¹ - m / N) (q : ℝ)⁻¹)⁻¹.toNNReal, Real.coe_toNNReal _ (by positivity)⟩
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, hr, ← inv_le_inv₀ (inv_pos.2 hmax) hp0', inv_inv]
    refine max_le (sub_le_self _ (by positivity)) ?_
    exact inv_anti₀ hp0' (by exact_mod_cast hpq)
  · rw [← NNReal.coe_le_coe, hr, ← inv_le_inv₀ hq0 (inv_pos.2 hmax), inv_inv]
    exact le_max_right _ _
  · rw [hr, inv_inv]
    exact le_max_left _ _
  · rw [hr, inv_inv]
    rcases le_total ((p : ℝ)⁻¹ - m / N) (q : ℝ)⁻¹ with h | h
    · rw [max_eq_right h]
      exact sub_le_self _ (by positivity)
    · rw [max_eq_left h]
      refine le_trans (le_of_eq ?_) hq
      push_cast
      rw [add_div]
      ring

/-- **Corollary 9.13, the `L^q` bound at every order**: for `m ≥ 0`, `1 ≤ p ≤ q < ∞` with
`1/p − m/N ≤ 1/q`, and `N ≥ 2` or `p > 1`, there is a finite `K` with `‖u‖_q ≤ K ‖u‖` for every
`u ∈ W^{m,p}(ℝ^N)`. This contains the book's first two clauses — `W^{m,p} ⊂ L^q` for
`1/q = 1/p − m/N` when `1/p − m/N > 0`, and for every `q ∈ [p, ∞)` when `1/p − m/N ≤ 0` — and is
proved by induction on `m` through
`SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le` and the first-order
statement `SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le`, with the intermediate
exponent `1/r = max (1/p − m/N) (1/q)`. [brezis2011functional] Corollary 9.13
("repeated applications of Theorem 9.9, Corollary 9.11 and Theorem 9.12"). -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order (m : ℕ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N m p ⊤,
      eLpNorm (fn u) q volume ≤ K * ENNReal.ofReal ‖u‖ := by
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
      exact SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u⟩
  | succ m ih =>
    have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
    obtain ⟨r, hpr, hrq, hr₁, hr₂⟩ :=
      NNReal.exists_intermediate_sobolev_exponent (N := N) m (zero_lt_one.trans_le hp1) hpq hq
    have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
    have hNr : 2 ≤ N ∨ 1 < r := hN.imp id fun h ↦ h.trans_le hpr
    obtain ⟨K₁, hK₁, hK₁u⟩ := ih (q := r) hN hpr hr₁
    obtain ⟨K₂, hK₂, hK₂u⟩ :=
      SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le (N := N) hNr hrq hr₂
    refine ⟨K₂ * ((N + 1) * K₁), ENNReal.mul_ne_top hK₂ (ENNReal.mul_ne_top (by simp) hK₁),
      fun u ↦ ?_⟩
    obtain ⟨w, hw, hwn⟩ :=
      SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le hK₁ hK₁u u
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

end HigherOrderLq

/-! ### Corollary 9.13: the continuous representative at every order -/

section HigherOrderContinuous

open SobolevMultiIndex

variable {N : ℕ}

/-- The Hölder estimate (25) for the continuous representative of `u ∈ W^{1,p}(ℝ^N)`, `N < p`,
in real form: `‖ũ x − ũ y‖ ≤ (C N).toReal ‖u‖ ‖x − y‖^{1 − N/p}`. -/
theorem SobolevEuclidean.norm_contRep_sub_le {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : N < p)
    (u : SobolevEuclidean N 1 p ⊤) (x y : EuclideanSpace ℝ (Fin N)) :
    ‖SobolevEuclidean.contRep hp u x - SobolevEuclidean.contRep hp u y‖
      ≤ (morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * N).toReal * ‖u‖
        * ‖x - y‖ ^ (1 - N / (p : ℝ)) := by
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ≥0∞,
    K₁ = morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * N := ⟨_, rfl⟩
  have hK₁t : K₁ ≠ ⊤ := by
    rw [hK₁]
    exact ENNReal.mul_ne_top (morreyConst_ne_top _ _) (by simp)
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hα0 : (0 : ℝ) ≤ 1 - N / (p : ℝ) := sub_nonneg.2 ((div_le_one hp0).2 hp.le)
  have h1 : ‖SobolevEuclidean.contRep hp u x - SobolevEuclidean.contRep hp u y‖ₑ
      ≤ K₁ * ENNReal.ofReal ‖u‖ * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ))) := by
    rw [hK₁]
    refine (SobolevEuclidean.enorm_contRep_sub_le hp u x y).trans ?_
    calc morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
          * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖
        ≤ morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
            * (N * ENNReal.ofReal ‖u‖) :=
          mul_le_mul' le_rfl (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u)
      _ = _ := by ring
  rw [← hK₁, ← toReal_enorm]
  refine (ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK₁t ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
    h1).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal (by positivity)]

/-- The exponent `r` of the continuous-representative step of Corollary 9.13: for `N/p < m + 1`,
an `r ≥ p` with `N < r` and `1/p − m/N ≤ 1/r` (so that `W^{m+1,p} ⊆ W^{1,r}` by
`SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order`), whose Hölder exponent `1 − N/r` is the
sharp `(m + 1) − N/p` when the latter is less than `1`. -/
theorem NNReal.exists_morrey_exponent {p : ℝ≥0} (m : ℕ) (hp0 : 0 < p)
    (hm : (N : ℝ) / p < (m + 1 : ℕ)) :
    ∃ r : ℝ≥0, p ≤ r ∧ N < r ∧ (p : ℝ)⁻¹ - m / N ≤ (r : ℝ)⁻¹ ∧
      ((m + 1 : ℕ) - N / (p : ℝ) < 1 → 1 - N / (r : ℝ) = (m + 1 : ℕ) - N / (p : ℝ)) := by
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  push_cast at hm ⊢
  rcases lt_or_ge (m : ℝ) (N / p) with h | h
  · -- the sharp case `1/r = 1/p − m/N`
    have hN0 : (0 : ℝ) < N := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · exact absurd h (not_lt.2 (by simp [hN]))
      · exact_mod_cast hN
    have hpos : 0 < (p : ℝ)⁻¹ - m / N := by
      rw [sub_pos, div_lt_iff₀ hN0, inv_mul_eq_div, lt_div_iff₀ hp0']
      rwa [lt_div_iff₀ hp0'] at h
    obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ) = ((p : ℝ)⁻¹ - m / N)⁻¹ :=
      ⟨((p : ℝ)⁻¹ - m / N)⁻¹.toNNReal, Real.coe_toNNReal _ (by positivity)⟩
    have hrinv : (r : ℝ)⁻¹ = (p : ℝ)⁻¹ - m / N := by rw [hr, inv_inv]
    have hr0 : (0 : ℝ) < r := by rw [hr]; exact inv_pos.2 hpos
    refine ⟨r, ?_, ?_, hrinv.symm.le, fun _ ↦ ?_⟩
    · rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hr0 hp0', hrinv]
      exact sub_le_self _ (by positivity)
    · have : (N : ℝ) < r := by
        refine (inv_lt_inv₀ hr0 hN0).1 ?_
        rw [hrinv, sub_lt_iff_lt_add, inv_eq_one_div (N : ℝ), ← add_div, inv_eq_one_div,
          div_lt_div_iff₀ hp0' hN0, one_mul, add_comm]
        rwa [div_lt_iff₀ hp0'] at hm
      exact_mod_cast this
    · rw [div_eq_mul_inv (N : ℝ) (r : ℝ), hrinv]
      field_simp
      ring
  · -- `1/p − m/N ≤ 0`: take `r = p + N`
    refine ⟨p + N, le_self_add, ?_, ?_, fun h1 ↦ absurd h (not_le.2 (by linarith))⟩
    · rw [← NNReal.coe_lt_coe]
      push_cast
      linarith
    · push_cast
      rcases Nat.eq_zero_or_pos N with hN | hN
      · simp [hN]
      · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
        refine le_trans ?_ (inv_pos.2 (by positivity)).le
        rw [sub_nonpos, le_div_iff₀ hN0, inv_mul_eq_div, div_le_iff₀ hp0']
        rwa [div_le_iff₀ hp0'] at h

/-- **Corollary 9.13, the continuous representative**: for `m > N/p` (`m ≥ 1`, `1 ≤ p < ∞`,
and `N ≥ 2` or `p > 1`), there are `C ≥ 0` and a Hölder exponent `θ ∈ (0, 1]` — equal to the
sharp `m − N/p` when `m − N/p < 1` — such that every `u ∈ W^{m,p}(ℝ^N)` has a continuous
representative `ũ` with `‖ũ x‖ ≤ C ‖u‖` and `‖ũ x − ũ y‖ ≤ C ‖u‖ ‖x − y‖^θ`; in particular
`W^{m,p}(ℝ^N) ⊂ L^∞(ℝ^N)` when `1/p − m/N < 0`. Proof: `W^{m,p} ⊆ W^{1,r}` for an `r > N` with
`1/r = 1/p − (m − 1)/N` when that is positive (`NNReal.exists_morrey_exponent`,
`SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order`), then Morrey's theorem.
[brezis2011functional] Corollary 9.13, the third clause and the case `k = 0` of the `C^k` clause. -/
theorem SobolevEuclidean.exists_forall_continuous_ae_eq_of_order {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p < 1 → θ = m - N / p) ∧
      ∀ u : SobolevEuclidean N m p ⊤, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume] ũ ∧ (∀ x, ‖ũ x‖ ≤ C * ‖u‖) ∧
        ∀ x y, ‖ũ x - ũ y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ≥0) < p := zero_lt_one.trans_le hp1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    refine ⟨m - 1, ?_⟩
    have : 0 < m := by exact_mod_cast (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ N / p) hm)
    omega
  obtain ⟨r, hpr, hNr, hr₁, hθ⟩ := NNReal.exists_morrey_exponent (N := N) m' hp0 hm
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
  obtain ⟨K₁, hK₁, hK₁u⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order (N := N) m' hN hpr hr₁
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ,
    C₁ = (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) r * (N + 1)).toReal :=
    ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ,
    C₂ = (morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) r * N).toReal := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (N + 1) * K₁.toReal := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := hC₁ ▸ ENNReal.toReal_nonneg
  have hC₂0 : 0 ≤ C₂ := hC₂ ▸ ENNReal.toReal_nonneg
  have hD0 : 0 ≤ D := hD ▸ by positivity
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (Nat.cast_nonneg N) (by exact_mod_cast hNr)
  refine ⟨max C₁ C₂ * D, 1 - N / r, by positivity, ?_, ?_, hθ, fun u ↦ ?_⟩
  · exact sub_pos.2 ((div_lt_one hr0).2 (by exact_mod_cast hNr))
  · exact sub_le_self _ (by positivity)
  obtain ⟨w, hw, hwn⟩ :=
    SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le hK₁ hK₁u u
  rw [← hD] at hwn
  refine ⟨SobolevEuclidean.contRep hNr w, (SobolevEuclidean.contRep hNr w).continuous,
    hw.symm.trans (SobolevEuclidean.fn_ae_eq_contRep hNr w), fun x ↦ ?_, fun x y ↦ ?_⟩
  · calc ‖SobolevEuclidean.contRep hNr w x‖ ≤ C₁ * ‖w‖ := by
          rw [hC₁]
          exact SobolevEuclidean.norm_contRep_apply_le hNr w x
      _ ≤ C₁ * (D * ‖u‖) := mul_le_mul_of_nonneg_left hwn hC₁0
      _ ≤ max C₁ C₂ * D * ‖u‖ := by
          rw [← mul_assoc]
          gcongr
          exact le_max_left _ _
  · calc ‖SobolevEuclidean.contRep hNr w x - SobolevEuclidean.contRep hNr w y‖
        ≤ C₂ * ‖w‖ * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by
          rw [hC₂]
          exact SobolevEuclidean.norm_contRep_sub_le hNr w x y
      _ ≤ C₂ * (D * ‖u‖) * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by gcongr
      _ ≤ max C₁ C₂ * D * ‖u‖ * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by
          rw [← mul_assoc]
          gcongr
          exact le_max_right _ _

/-- **Corollary 9.13, `W^{m,p}(ℝ^N) ⊂ L^∞(ℝ^N)` for `1/p − m/N < 0`, the bound**: there is a
finite `K` with `‖u‖_∞ ≤ K ‖u‖` for every `u ∈ W^{m,p}(ℝ^N)` (`N ≥ 2` or `p > 1`).
[brezis2011functional] Corollary 9.13, the third clause. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_top_le_of_order {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N m p ⊤,
      eLpNorm (fn u) ⊤ volume ≤ K * ENNReal.ofReal ‖u‖ := by
  obtain ⟨C, θ, hC0, -, -, -, hC⟩ := SobolevEuclidean.exists_forall_continuous_ae_eq_of_order hN hm
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, hb, -⟩ := hC u
  rw [eLpNorm_congr_ae hae, ← ENNReal.ofReal_mul hC0]
  refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (C * ‖u‖))
    hc.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hb x)

/-- **Corollary 9.13, `W^{m,p}(ℝ^N) ⊆ L^∞(ℝ^N)` for `1/p − m/N < 0`**, the membership. -/
theorem SobolevEuclidean.memLp_fn_top_of_order {m : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) (u : SobolevEuclidean N m p ⊤) :
    MemLp (fn u) ⊤ volume := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_top_le_of_order hN hm
  exact memLp_iff.2 ((hKu u).trans_lt (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top))

/-- **Corollary 9.13, `W^{m,p}(ℝ^N) ↪ L^∞(ℝ^N)` with continuous injection** for
`1/p − m/N < 0`, along `SobolevMultiIndex.toLpₗ`. [brezis2011functional] Corollary 9.13. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_top_of_order {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m p ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_top_of_order hN hm u) := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_top_le_of_order hN hm
  refine isContinuousEmbedding_toLpₗ _ (C := K.toReal) fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (norm_nonneg u), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) ?_
  exact (eLpNorm_restrict_coe_top (fn u) ⊤).trans_le (hKu u)

/-- **Corollary 9.13, the `L^q` clauses, the membership**: for `1 ≤ p ≤ q < ∞` with
`1/p − m/N ≤ 1/q`, and `N ≥ 2` or `p > 1`, `fn u ∈ L^q(ℝ^N)` for every `u ∈ W^{m,p}(ℝ^N)` —
`W^{m,p} ⊂ L^q` for `1/q = 1/p − m/N` when `1/p − m/N > 0`, and for every `q ∈ [p, ∞)` when
`1/p − m/N ≤ 0`. The `L^∞` clause is `SobolevEuclidean.memLp_fn_top_of_order`.
[brezis2011functional] Corollary 9.13, the first two clauses. -/
theorem SobolevEuclidean.memLp_fn_of_order {m : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹)
    (u : SobolevEuclidean N m p ⊤) : MemLp (fn u) q volume := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order m hN hpq hq
  exact memLp_iff.2 ((hKu u).trans_lt (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top))

/-- **Corollary 9.13, the `L^q` clauses, as continuous embeddings**: `W^{m,p}(ℝ^N) ↪ L^q(ℝ^N)`
along `SobolevMultiIndex.toLpₗ` for `1 ≤ p ≤ q < ∞` with `1/p − m/N ≤ 1/q` (`N ≥ 2` or `p > 1`).
[brezis2011functional] Corollary 9.13, "all these injections are continuous". -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_order {m : ℕ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m p ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_of_order hN hpq hq u) := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order m hN hpq hq
  refine isContinuousEmbedding_toLpₗ _ (C := K.toReal) fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (norm_nonneg u), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) ?_
  exact (eLpNorm_restrict_coe_top (fn u) (q : ℝ≥0∞)).trans_le (hKu u)

end HigherOrderContinuous

/-! ### Corollary 9.13: the `C^k` representative -/

section HigherOrderContDiff

open SobolevMultiIndex

variable {N : ℕ}

/-- A continuous linear functional on `ℝ^N` is the sum of its values on the standard basis vectors
times the coordinate projections. -/
theorem ContinuousLinearMap.eq_sum_apply_single_smul_proj
    (T : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) :
    T = ∑ i, T (EuclideanSpace.single i 1) • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i := by
  ext v
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr v]
  simp [EuclideanSpace.basisFun_repr, mul_comm]

/-- `‖g ∘ a − g ∘ b‖ ≤ ‖g‖ ‖a − b‖` for the composition of continuous multilinear maps with a
continuous linear map. -/
theorem ContinuousLinearMap.norm_compContinuousMultilinearMap_sub_le {ι G G' : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (g : G →L[ℝ] G') (a b : ContinuousMultilinearMap ℝ E G) :
    ‖g.compContinuousMultilinearMap a - g.compContinuousMultilinearMap b‖ ≤ ‖g‖ * ‖a - b‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have e : (g.compContinuousMultilinearMap a - g.compContinuousMultilinearMap b) m
      = g ((a - b) m) := by
    simp
  rw [e, mul_assoc]
  exact g.le_opNorm_of_le ((a - b).le_opNorm m)

/-- The iterated derivatives of `x ↦ ∑ i, g i x • P i` at a point where the scalar functions
`g i` are `C^k`, `j ≤ k`: the pointwise form of `iteratedFDeriv_fun_sum_smul_const`. -/
theorem iteratedFDeriv_fun_sum_smul_const_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
    {g : ι → E → ℝ} {k : ℕ} {x : E} (hg : ∀ i, ContDiffAt ℝ k (g i) x) (P : ι → F) {j : ℕ}
    (hj : j ≤ k) :
    iteratedFDeriv ℝ j (fun x ↦ ∑ i, g i x • P i) x
      = ∑ i, ((ContinuousLinearMap.id ℝ ℝ).smulRight (P i)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j (g i) x) := by
  have hjk : (j : ℕ∞ω) ≤ k := by exact_mod_cast hj
  rw [iteratedFDeriv_fun_sum_apply (f := fun i x ↦ g i x • P i) (u := Finset.univ) fun i _ ↦
    (((hg i).smul contDiffAt_const).of_le hjk)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have e : (fun x ↦ g i x • P i) = ((ContinuousLinearMap.id ℝ ℝ).smulRight (P i)) ∘ g i := by
    funext y
    simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hg i) hjk]

/-- The iterated derivatives of `x ↦ ∑ i, g i x • P i` for `C^k` scalar functions `g i` and
constant vectors `P i`: the composition of the iterated derivatives of the `g i` with the maps
`c ↦ c • P i`. -/
theorem iteratedFDeriv_fun_sum_smul_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] {g : ι → E → ℝ} {k : ℕ}
    (hg : ∀ i, ContDiff ℝ k (g i)) (P : ι → F) {j : ℕ} (hj : j ≤ k) (x : E) :
    iteratedFDeriv ℝ j (fun x ↦ ∑ i, g i x • P i) x
      = ∑ i, ((ContinuousLinearMap.id ℝ ℝ).smulRight (P i)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j (g i) x) :=
  iteratedFDeriv_fun_sum_smul_const_of_contDiffAt (fun i ↦ (hg i).contDiffAt) P hj

/-- The tensor weak derivative of `u ∈ W^{m+1,p}(Ω)` assembled from (representatives of) its
partial derivatives: if `g i = ∂_i u` almost everywhere on `Ω`, then `x ↦ ∑ i, g i x • proj i` is
a weak derivative of `fn u` on `Ω`. -/
theorem SobolevEuclidean.hasWeakFDerivOn_sum_smul_proj {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (u : SobolevEuclidean N (m + 1) p Ω)
    {g : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hg : ∀ i, fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume i u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g i) :
    HasWeakFDerivOn (fn u) (fun x ↦ ∑ i, g i x • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i) Ω volume := by
  obtain ⟨w', hw'⟩ := ((memSobolevMultiIndex (toLowerOrder ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume (by omega : 1 ≤ m + 1) u)).memSobolev)
    |>.exists_hasWeakFDerivOn
  have hw'' : HasWeakFDerivOn (fn u) w' Ω volume := hw'.1
  have hcomp : ∀ i, (fun x ↦ w' x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g i := by
    intro i
    have h2 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u)
        (fun x ↦ w' x (EuclideanSpace.single i 1)) Ω volume := by
      have := HasWeakIteratedFDerivOn.lineDeriv hw'' ![EuclideanSpace.single i 1]
      simpa using this
    have h3 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u) (g i) Ω volume := by
      have := (hasWeakIteratedLineDerivOn_fn_partialDeriv i u).congr_ae
        (Filter.EventuallyEq.refl _ _) (hg i)
      simpa using this
    exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h2.ae_eq h3)
  have hae : w' =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ ∑ i, g i x • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i := by
    have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
        ∀ i, w' x (EuclideanSpace.single i 1) = g i x := ae_all_iff.2 hcomp
    filter_upwards [hall] with x hx
    rw [ContinuousLinearMap.eq_sum_apply_single_smul_proj (w' x)]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hx i]
  unfold HasWeakFDerivOn at hw'' ⊢
  refine hw''.congr_ae (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hae] with x hx
  simp only [hx]

/-- **Corollary 9.13, the `C^k` representative, in the form of the induction**: for `k + N/p < m`
(`1 ≤ p < ∞`, and `N ≥ 2` or `p > 1`), there are `C ≥ 0` and a Hölder exponent `θ ∈ (0, 1]` —
equal to the sharp `m − N/p − k` when that is less than `1` — such that every
`u ∈ W^{m,p}(ℝ^N)` has a `C^k` representative `ũ` with `‖D^j ũ x‖ ≤ C ‖u‖` for `j ≤ k` and
`‖D^k ũ x − D^k ũ y‖ ≤ C ‖u‖ ‖x − y‖^θ`. Induction on `k`: `u` and `∂_i u` lie in
`W^{m−1,p}(ℝ^N)` and have `C^{k−1}` representatives `ũ`, `g̃_i`; `x ↦ ∑ g̃_i x • proj i` is a
continuous weak derivative of `ũ`, so `ũ` is `C¹` with that derivative
(`HasWeakFDerivOn.exists_contDiffOn_ae_eq_of_continuousOn`, Remark 2), hence `C^k`, and its
derivatives of order `j + 1` are assembled from those of order `j` of the `g̃_i`.
[brezis2011functional] Corollary 9.13, the `C^k` clause. -/
theorem SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order (k : ℕ) {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p - k < 1 → θ = m - N / p - k) ∧
      ∀ u : SobolevEuclidean N m p ⊤, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ k ũ ∧
        fn u =ᵐ[volume] ũ ∧ (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * ‖u‖) ∧
        ∀ x y, ‖iteratedFDeriv ℝ k ũ x - iteratedFDeriv ℝ k ũ y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  induction k generalizing m with
  | zero =>
    rw [Nat.cast_zero, zero_add] at hm
    obtain ⟨C, θ, hC0, hθ0, hθ1, hθ, hC⟩ :=
      SobolevEuclidean.exists_forall_continuous_ae_eq_of_order hN hm
    refine ⟨C, θ, hC0, hθ0, hθ1, fun h ↦ ?_, fun u ↦ ?_⟩
    · rw [Nat.cast_zero, sub_zero] at h ⊢
      exact hθ h
    obtain ⟨ũ, hc, hae, hb, hh⟩ := hC u
    refine ⟨ũ, contDiff_zero.2 hc, hae, fun j hj x ↦ ?_, fun x y ↦ ?_⟩
    · obtain rfl : j = 0 := Nat.le_zero.1 hj
      rw [norm_iteratedFDeriv_zero]
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
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : SobolevEuclidean N m' p ⊤,
        v₀ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p ⊤ volume
          (Nat.le_succ m') u :=
      ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin N → SobolevEuclidean N m' p ⊤,
        v = fun i ↦ partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p ⊤ volume i u :=
      ⟨_, rfl⟩
    have hv₀fn : fn v₀ = fn u := by rw [hv₀]; rfl
    have hv₀n : ‖v₀‖ ≤ ‖u‖ := by rw [hv₀]; exact norm_toLowerOrder_le _ u
    have hvn : ∀ i, ‖v i‖ ≤ ‖u‖ := fun i ↦ by rw [hv]; exact norm_partialDeriv_le i u
    obtain ⟨ũ, hũc, hũae, hũb, hũh⟩ := hC v₀
    rw [hv₀fn] at hũae
    choose g hgc hgae hgb hgh using fun i ↦ hC (v i)
    -- the tensor weak derivative of `fn u`, continuous
    obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
        w = fun x ↦ ∑ i, g i x • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i := ⟨_, rfl⟩
    have hwc : ContDiff ℝ k w := by
      rw [hw]
      exact ContDiff.sum fun i _ ↦ (hgc i).smul contDiff_const
    have hweak : HasWeakFDerivOn (fn u) w ⊤ volume := by
      rw [hw]
      exact SobolevEuclidean.hasWeakFDerivOn_sum_smul_proj u fun i ↦ by
        have h := hgae i
        rw [hv] at h
        exact eventuallyEq_restrict_coe_top_iff.2 h
    have hDw : ∀ j ≤ k, ∀ x, iteratedFDeriv ℝ j w x
        = ∑ i, (L i).compContinuousMultilinearMap (iteratedFDeriv ℝ j (g i) x) := by
      intro j hj x
      rw [hw, hL]
      exact iteratedFDeriv_fun_sum_smul_const hgc _ hj x
    -- `ũ` is `C¹` with derivative `w`
    obtain ⟨v', hv'c, hv'ae, hv'd⟩ :=
      hweak.exists_contDiffOn_ae_eq_of_continuousOn hwc.continuous.continuousOn
    have hv'ũ : v' = ũ :=
      Measure.eq_of_ae_eq (μ := volume)
        ((eventuallyEq_restrict_coe_top_iff.1 hv'ae).symm.trans hũae)
        (by simpa using hv'c.continuousOn) hũc.continuous
    have hd : ∀ x, HasFDerivAt ũ (w x) x := fun x ↦ hv'ũ ▸ hv'd x (by simp)
    have hfd : fderiv ℝ ũ = w := funext fun x ↦ (hd x).fderiv
    have hũc' : ContDiff ℝ (k + 1) ũ :=
      contDiff_succ_iff_fderiv.2 ⟨fun x ↦ (hd x).differentiableAt, by simp, by rw [hfd]; exact hwc⟩
    refine ⟨ũ, hũc', hũae, fun j hj x ↦ ?_, fun x y ↦ ?_⟩
    · -- the bounds on the derivatives of order `≤ k + 1`
      rcases j with _ | j
      · calc ‖iteratedFDeriv ℝ 0 ũ x‖ ≤ C₀ * ‖v₀‖ := hũb 0 (Nat.zero_le _) x
          _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by
              calc C₀ * ‖v₀‖ ≤ C₀ * ‖u‖ := mul_le_mul_of_nonneg_left hv₀n hC₀
                _ = C₀ * 1 * ‖u‖ := by ring
                _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by gcongr; linarith
      · have hjk : j ≤ k := Nat.succ_le_succ_iff.1 hj
        rw [← norm_iteratedFDeriv_fderiv, hfd, hDw j hjk x]
        calc ‖∑ i, (L i).compContinuousMultilinearMap (iteratedFDeriv ℝ j (g i) x)‖
            ≤ ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ j (g i) x‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
                ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
          _ ≤ ∑ i, ‖L i‖ * (C₀ * ‖u‖) := Finset.sum_le_sum fun i _ ↦
              mul_le_mul_of_nonneg_left ((hgb i j hjk x).trans
                (mul_le_mul_of_nonneg_left (hvn i) hC₀)) (norm_nonneg _)
          _ = C₀ * (∑ i, ‖L i‖) * ‖u‖ := by rw [← Finset.sum_mul]; ring
          _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by gcongr; linarith
    · -- the Hölder estimate on the top derivative
      rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map, hfd, hDw k le_rfl x,
        hDw k le_rfl y, ← Finset.sum_sub_distrib]
      calc ‖∑ i, ((L i).compContinuousMultilinearMap (iteratedFDeriv ℝ k (g i) x)
              - (L i).compContinuousMultilinearMap (iteratedFDeriv ℝ k (g i) y))‖
          ≤ ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ k (g i) x - iteratedFDeriv ℝ k (g i) y‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
              ContinuousLinearMap.norm_compContinuousMultilinearMap_sub_le _ _ _)
        _ ≤ ∑ i, ‖L i‖ * (C₀ * ‖u‖ * ‖x - y‖ ^ θ) := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left ((hgh i x y).trans (by gcongr; exact hvn i)) (norm_nonneg _)
        _ = C₀ * (∑ i, ‖L i‖) * ‖u‖ * ‖x - y‖ ^ θ := by rw [← Finset.sum_mul]; ring
        _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ * ‖x - y‖ ^ θ := by gcongr; linarith

end HigherOrderContDiff

/-! ### Corollary 9.13, the `C^k` clause, and the local `C^k` representatives -/

section HigherOrderCorollaries

open SobolevMultiIndex

variable {N : ℕ}

/-- **Corollary 9.13, the `C^k` clause**: for `m − N/p > 0` not an integer, `k = ⌊m − N/p⌋` and
`θ = m − N/p − k ∈ (0, 1)` — encoded as `0 < m − N/p − k < 1` — with `1 ≤ p < ∞` and `N ≥ 2` or
`p > 1`, there is `C` such that every `u ∈ W^{m,p}(ℝ^N)` has a representative `ũ` of class
`C^k` whose derivatives of order `≤ k` are bounded by `C ‖u‖` and whose derivatives of order `k`
are `θ`-Hölder with constant `C ‖u‖`; in particular `W^{m,p}(ℝ^N) ⊂ C^k(ℝ^N)` modulo the choice
of a representative. [brezis2011functional] Corollary 9.13 (footnotes 13–14). -/
theorem SobolevEuclidean.exists_contDiff_ae_eq_of_order {m k : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hθ0 : 0 < (m : ℝ) - N / p - k)
    (hθ1 : (m : ℝ) - N / p - k < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N m p ⊤, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ,
      ContDiff ℝ k ũ ∧ fn u =ᵐ[volume] ũ ∧
      (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * ‖u‖) ∧
      ∀ x y, ‖iteratedFDeriv ℝ k ũ x - iteratedFDeriv ℝ k ũ y‖
        ≤ C * ‖u‖ * ‖x - y‖ ^ ((m : ℝ) - N / p - k) := by
  obtain ⟨C, θ, hC0, -, -, hθ, hC⟩ :=
    SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order (N := N) k (m := m) hN (by linarith)
  obtain rfl := hθ hθ1
  exact ⟨C, hC0, hC⟩

/-- **Corollary 9.13's `C^k` clause without the non-integer restriction**: for `1 ≤ p < ∞`,
integers `m, k` with `k + N/p < m`, and `N ≥ 2` or `p > 1`, there are `C` and a Hölder exponent
`θ ∈ (0, 1]` such that every `u ∈ W^{m,p}(ℝ^N)` has a `C^k` representative `ũ` with every
derivative of order `≤ k` bounded by `C ‖u‖` and the derivatives of order `k` `θ`-Hölder with
constant `C ‖u‖`. This is the form the heat equation needs (`H^{2ℓ}(ℝ^N) ⊆ C^k` for
`k + N/2 < 2ℓ`), where `2ℓ − N/2` is an integer for every even `N`.
[brezis2011functional] Corollary 9.13, and the proofs of Theorems 10.1 and 10.8. -/
theorem SobolevEuclidean.exists_contDiff_ae_eq_of_lt {m k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ∀ u : SobolevEuclidean N m p ⊤,
      ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ k ũ ∧ fn u =ᵐ[volume] ũ ∧
      (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * ‖u‖) ∧
      ∀ x y, ‖iteratedFDeriv ℝ k ũ x - iteratedFDeriv ℝ k ũ y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  obtain ⟨C, θ, hC0, hθ0, hθ1, -, hC⟩ :=
    SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order (N := N) k hN hm
  exact ⟨C, θ, hC0, hθ0, hθ1, hC⟩

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **`W^{m,p}_loc(Ω) ⊆ C^k(Ω)` for `k + N/p < m`** (`1 ≤ p < ∞`, `N ≥ 2` or `p > 1`): a function
of `W^{m,p}_loc(Ω)` has a representative of class `C^k` on `Ω`. On a ball `B` with
`closure B ⊆ Ω`, `θ f ∈ W^{m,p}(ℝ^N)` for a bump `θ = 1` on `B`
(`MemSobolevMultiIndexLoc.smul_testFunction`), which has a `C^k` representative by Corollary 9.13
(`SobolevEuclidean.exists_contDiff_ae_eq_of_lt`); the local representatives glue
(`MeasureTheory.exists_continuousOn_ae_eq_of_forall_exists_ball`) and `ContDiffOn` is local. -/
theorem MemSobolevMultiIndexLoc.exists_contDiffOn_of_lt {m k : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m)
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f m p Ω volume) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ k ũ Ω ∧
      f =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ := by
  obtain ⟨C, θ, -, -, -, hC⟩ := SobolevEuclidean.exists_contDiff_ae_eq_of_lt (N := N) hN hm
  -- the local representatives
  have hP : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∃ r > 0,
      ball x r ⊆ (Ω : Set (EuclideanSpace ℝ (Fin N))) ∧ ∃ g : EuclideanSpace ℝ (Fin N) → ℝ,
        ContDiffOn ℝ k g (ball x r) ∧ ContinuousOn g (ball x r) ∧
        f =ᵐ[volume.restrict (ball x r)] g := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
    obtain ⟨φ, hφ⟩ : ∃ φ : ContDiffBump x, φ = ⟨ε / 4, ε / 2, by positivity, by linarith⟩ :=
      ⟨_, rfl⟩
    have hIn : φ.rIn = ε / 4 := by rw [hφ]
    have hOut : φ.rOut = ε / 2 := by rw [hφ]
    have hsupp : tsupport φ ⊆ Ω := by
      rw [φ.tsupport_eq, hOut]
      exact (closedBall_subset_ball (by linarith)).trans hεΩ
    obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : 𝓓(Ω, ℝ), ϑ = ⟨φ, φ.contDiff (n := ⊤), φ.hasCompactSupport, hsupp⟩ :=
      ⟨_, rfl⟩
    have hϑ1 : ∀ y ∈ ball x (ε / 4), ϑ y = 1 := fun y hy ↦ by
      rw [hϑ, TestFunction.coe_mk]
      exact φ.one_of_mem_closedBall (hIn ▸ ball_subset_closedBall hy)
    have hmem := MemSobolevMultiIndexLoc.smul_testFunction (Fact.out) hf ϑ
    obtain ⟨U, hU⟩ := hmem.exists_sobolevMultiIndex
    rw [eventuallyEq_restrict_coe_top_iff] at hU
    obtain ⟨ũ, hũc, hũae, -, -⟩ := hC U
    refine ⟨ε / 4, by positivity, (ball_subset_ball (by linarith)).trans hεΩ, ũ, hũc.contDiffOn,
      hũc.continuous.continuousOn, ?_⟩
    have h1 : f =ᵐ[volume.restrict (ball x (ε / 4))]
        (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun y ↦ ϑ y • f y := by
      refine ae_restrict_of_forall_mem measurableSet_ball fun y hy ↦ ?_
      rw [Set.indicator_of_mem (hεΩ (ball_subset_ball (by linarith) hy)), hϑ1 y hy, one_smul]
    exact h1.trans (ae_restrict_of_ae (hU.symm.trans hũae))
  obtain ⟨v, -, hfv, hloc⟩ := exists_continuousOn_ae_eq_of_forall_exists_ball (μ := volume) (Ω := Ω)
    (u := f) (fun g s ↦ ContDiffOn ℝ k g s) hP
  refine ⟨v, contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_, hfv⟩
  obtain ⟨r, hr, -, g, hg, hvg⟩ := hloc x hx
  exact ⟨ball x r, isOpen_ball, mem_ball_self hr,
    (hg.mono inter_subset_right).congr fun y hy ↦ hvg hy.2⟩

/-- **A function of `H^m_loc(Ω)` for every `m` has a `C^∞` representative on `Ω`**: this is the
sentence "`e_n ∈ ⋂_m H^m(ω)` for all `ω ⊂⊂ Ω`, as a consequence `e_n ∈ C^∞(Ω)`" of the proof of
[brezis2011functional] Theorem 9.31. The `C^k` representatives of
`MemSobolevMultiIndexLoc.exists_contDiffOn_of_lt` are continuous on `Ω` and almost everywhere
equal, hence equal on `Ω`, so the `C^0` one is `C^k` for every `k`. -/
theorem MemSobolevMultiIndexLoc.exists_contDiffOn {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : ∀ m, MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f m 2 Ω volume) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ ∞ ũ Ω ∧
      f =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ := by
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  have hN : 2 ≤ N ∨ 1 < (2 : ℝ≥0) := Or.inr one_lt_two
  have hrep : ∀ k : ℕ, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ k ũ Ω ∧
      f =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ := fun k ↦
    MemSobolevMultiIndexLoc.exists_contDiffOn_of_lt (m := k + N + 1) hN
      (by
        have : (N : ℝ) / (2 : ℝ≥0) ≤ N := by
          rw [NNReal.coe_ofNat]
          exact half_le_self (Nat.cast_nonneg N)
        push_cast
        linarith)
      (hf _)
  choose v hvc hfv using hrep
  refine ⟨v 0, contDiffOn_infty.2 fun k ↦ ?_, hfv 0⟩
  refine (hvc k).congr fun x hx ↦ ?_
  exact Measure.eqOn_open_of_ae_eq ((hfv 0).symm.trans (hfv k)) Ω.isOpen
    (hvc 0).continuousOn (hvc k).continuousOn hx

end HigherOrderCorollaries

/-! ### Remark 13: `W^{N,1}(ℝ^N) ⊂ L^∞(ℝ^N)` -/

section LineFTC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The fundamental theorem of calculus along a line, as a bound**: for a compactly supported
`C¹` function `g` and a direction `v ≠ 0`, `|g x| ≤ ∫_ℝ |∂_v g (x + s v)| ds`, since `g` vanishes
far out along the line. -/
theorem ContDiff.enorm_le_lintegral_fderiv_line {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {v : E} (hv : v ≠ 0) (x : E) :
    ‖g x‖ₑ ≤ ∫⁻ s : ℝ, ‖fderiv ℝ g (x + s • v) v‖ₑ := by
  obtain ⟨h', hh'⟩ : ∃ h' : ℝ → ℝ, h' = fun s ↦ fderiv ℝ g (x + s • v) v := ⟨_, rfl⟩
  have hd : ∀ s, HasDerivAt (fun s ↦ g (x + s • v)) (h' s) s := fun s ↦ by
    have h1 : HasDerivAt (fun s : ℝ ↦ x + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    have h2 := (hg.differentiable one_ne_zero (x + s • v)).hasFDerivAt.comp_hasDerivAt s h1
    rw [hh']
    simpa [Function.comp_def] using h2
  have hc : Continuous h' := by
    rw [hh']
    exact ((hg.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  -- the function vanishes far out along the line
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ closedBall 0 R := by
    obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : E)).1 hgc.isCompact.isBounded
    exact ⟨max R 0, le_max_right _ _, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (R + ‖x‖) / ‖v‖ + 1 := ⟨_, rfl⟩
  have hT0 : 0 < T := by
    rw [hT]
    positivity
  have hzero : g (x + (-T) • v) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : ‖(-T) • v‖ - ‖x‖ ≤ ‖x + (-T) • v‖ := by
      have := norm_sub_norm_le ((-T) • v) (-x)
      rwa [sub_neg_eq_add, norm_neg, add_comm] at this
    rw [norm_smul, norm_neg, Real.norm_of_nonneg hT0.le] at h2
    have h3 : T * ‖v‖ = R + ‖x‖ + ‖v‖ := by
      rw [hT, add_mul, div_mul_cancel₀ _ hv0.ne', one_mul]
    linarith
  -- the fundamental theorem of calculus on `[-T, 0]`
  have hint : IntervalIntegrable h' volume (-T) 0 := hc.intervalIntegrable _ _
  have hftc : g x = ∫ s in (-T)..0, h' s := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s) hint
    rw [this, hzero, sub_zero]
    simp
  rw [hftc, intervalIntegral.integral_of_le (by linarith)]
  calc ‖∫ s in Ioc (-T) 0, h' s‖ₑ ≤ ∫⁻ s in Ioc (-T) 0, ‖h' s‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s, ‖h' s‖ₑ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ s, ‖fderiv ℝ g (x + s • v) v‖ₑ := by rw [hh']

end LineFTC

section FubiniStep

/-- **Fubini for one more coordinate**: an integral over `ℝ^{j+1}` is the integral over the last
`j` coordinates of the integral over the first, the coordinates being read as `Fin.cons s t`. -/
theorem MeasureTheory.lintegral_fin_succ_eq {j : ℕ} {H : (Fin (j + 1) → ℝ) → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ y, H y = ∫⁻ t : Fin j → ℝ, ∫⁻ s : ℝ, H (Fin.cons s t) := by
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (j + 1) ↦ ℝ) 0).symm
  rw [← hmp.lintegral_comp hH, Measure.volume_eq_prod,
    lintegral_prod_symm (fun a : ℝ × (Fin j → ℝ) ↦
      H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) ↦ ℝ) 0).symm a))
      (hH.comp hmp.measurable).aemeasurable]
  refine lintegral_congr fun t ↦ lintegral_congr fun s ↦ ?_
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

end FubiniStep

section IteratedFTC

variable {N : ℕ}

/-- The standard basis vectors of `ℝ^N` indexed by `ℕ`, `0` beyond `N`. -/
def EuclideanSpace.stdVec (N : ℕ) (n : ℕ) : EuclideanSpace ℝ (Fin N) :=
  if h : n < N then EuclideanSpace.single ⟨n, h⟩ 1 else 0

/-- `stdVec N n` for `n < N` is the basis vector `e_n`. -/
theorem EuclideanSpace.stdVec_of_lt {n : ℕ} (h : n < N) :
    EuclideanSpace.stdVec N n = EuclideanSpace.single ⟨n, h⟩ 1 := by
  simp [EuclideanSpace.stdVec, h]

/-- `stdVec N n ≠ 0` for `n < N`. -/
theorem EuclideanSpace.stdVec_ne_zero {n : ℕ} (h : n < N) : EuclideanSpace.stdVec N n ≠ 0 := by
  rw [EuclideanSpace.stdVec_of_lt h]
  intro h0
  have := congrArg (fun v : EuclideanSpace ℝ (Fin N) ↦ v ⟨n, h⟩) h0
  simp at this

/-- The tuple of directions `(e_{N−j}, …, e_{N−1})` of length `j`, the last `j` basis vectors of
`ℝ^N`: `stdDirs N j i = e_{N − j + i}`. -/
def EuclideanSpace.stdDirs (N j : ℕ) : Fin j → EuclideanSpace ℝ (Fin N) :=
  fun i ↦ EuclideanSpace.stdVec N (N - j + i)

/-- `stdDirs N (j + 1)` is `e_{N − 1 − j}` followed by `stdDirs N j`, for `j + 1 ≤ N`. -/
theorem EuclideanSpace.stdDirs_succ {j : ℕ} (hj : j + 1 ≤ N) :
    EuclideanSpace.stdDirs N (j + 1)
      = Fin.cons (EuclideanSpace.stdVec N (N - 1 - j)) (EuclideanSpace.stdDirs N j) := by
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp only [EuclideanSpace.stdDirs, Fin.cons_zero, Fin.val_zero, add_zero]
    congr 1
    omega
  · simp only [EuclideanSpace.stdDirs, Fin.cons_succ, Fin.val_succ]
    congr 1
    omega

/-- `stdDirs N N` is the standard basis in order. -/
theorem EuclideanSpace.stdDirs_self (i : Fin N) :
    EuclideanSpace.stdDirs N N i = EuclideanSpace.single i 1 := by
  simp only [EuclideanSpace.stdDirs, Nat.sub_self, zero_add]
  rw [EuclideanSpace.stdVec_of_lt i.2]

/-- **The iterated fundamental theorem of calculus, one direction at a time**: for a smooth
compactly supported `φ` on `ℝ^N` and `j ≤ N`,
`|φ x| ≤ ∫_{ℝ^j} |D^j φ (x + ∑ t_i e_{N−j+i}) (e_{N−j}, …, e_{N−1})| dt`, by induction on `j`
through the line bound `ContDiff.enorm_le_lintegral_fderiv_line` and the Fubini step
`MeasureTheory.lintegral_fin_succ_eq`. -/
theorem ContDiff.enorm_le_lintegral_iteratedFDeriv_stdDirs {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (x : EuclideanSpace ℝ (Fin N)) :
    ∀ j ≤ N, ‖φ x‖ₑ ≤ ∫⁻ t : Fin j → ℝ, ‖iteratedFDeriv ℝ j φ
      (x + ∑ i, t i • EuclideanSpace.stdDirs N j i) (EuclideanSpace.stdDirs N j)‖ₑ := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, iteratedFDeriv_zero_apply]
    rw [volume_pi, Measure.pi_of_empty _ (fun _ ↦ 0), lintegral_dirac]
  | succ j ih =>
    intro hj
    refine (ih (by omega)).trans ?_
    -- the pointwise line bound
    have hlt : N - 1 - j < N := by omega
    obtain ⟨v, hv⟩ : ∃ v, v = EuclideanSpace.stdVec N (N - 1 - j) := ⟨_, rfl⟩
    have hv0 : v ≠ 0 := hv ▸ EuclideanSpace.stdVec_ne_zero hlt
    have hg : ContDiff ℝ 1 fun z ↦ iteratedFDeriv ℝ j φ z (EuclideanSpace.stdDirs N j) :=
      (ContinuousMultilinearMap.apply ℝ _ ℝ (EuclideanSpace.stdDirs N j)).contDiff.comp
        (hφ.iteratedFDeriv_right (by simp))
    have hgc : HasCompactSupport ((fun T : EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ ↦
        T (EuclideanSpace.stdDirs N j)) ∘ iteratedFDeriv ℝ j φ) :=
      (hφc.iteratedFDeriv j).comp_left (by simp)
    have hfd : ∀ z, fderiv ℝ (fun z ↦ iteratedFDeriv ℝ j φ z (EuclideanSpace.stdDirs N j)) z v
        = iteratedFDeriv ℝ (j + 1) φ z (EuclideanSpace.stdDirs N (j + 1)) := fun z ↦ by
      rw [EuclideanSpace.stdDirs_succ hj, iteratedFDeriv_succ_apply_left, Fin.cons_zero,
        Fin.tail_cons, ← hv, fderiv_continuousMultilinear_apply_const_apply
          ((hφ.iteratedFDeriv_right (m := 1) (i := j) (by simp)).differentiable one_ne_zero z)]
    have hsum : ∀ (t : Fin j → ℝ) (s : ℝ), x + ∑ i, t i • EuclideanSpace.stdDirs N j i + s • v
        = x + ∑ i, (Fin.cons s t : Fin (j + 1) → ℝ) i • EuclideanSpace.stdDirs N (j + 1) i := by
      intro t s
      rw [EuclideanSpace.stdDirs_succ hj, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, ← hv,
        add_assoc, add_comm (s • v)]
      simp only [Fin.cons_succ]
    have hpt : ∀ t : Fin j → ℝ, ‖iteratedFDeriv ℝ j φ (x + ∑ i, t i • EuclideanSpace.stdDirs N j i)
        (EuclideanSpace.stdDirs N j)‖ₑ ≤ ∫⁻ s : ℝ, ‖iteratedFDeriv ℝ (j + 1) φ
          (x + ∑ i, (Fin.cons s t : Fin (j + 1) → ℝ) i • EuclideanSpace.stdDirs N (j + 1) i)
          (EuclideanSpace.stdDirs N (j + 1))‖ₑ := fun t ↦ by
      refine (hg.enorm_le_lintegral_fderiv_line hgc hv0 _).trans (le_of_eq ?_)
      refine lintegral_congr fun s ↦ ?_
      rw [hfd, hsum]
    -- integrate in the remaining variables and use Fubini
    have hcont : Continuous fun y : Fin (j + 1) → ℝ ↦ iteratedFDeriv ℝ (j + 1) φ
        (x + ∑ i, y i • EuclideanSpace.stdDirs N (j + 1) i) :=
      (hφ.continuous_iteratedFDeriv (m := j + 1) (by simp)).comp
        (continuous_const.add (continuous_finsetSum _ fun i _ ↦
          (continuous_apply i).smul continuous_const))
    have hcont2 : Continuous fun y : Fin (j + 1) → ℝ ↦ iteratedFDeriv ℝ (j + 1) φ
        (x + ∑ i, y i • EuclideanSpace.stdDirs N (j + 1) i) (EuclideanSpace.stdDirs N (j + 1)) :=
      (ContinuousMultilinearMap.apply ℝ _ ℝ (EuclideanSpace.stdDirs N (j + 1))).continuous.comp
        hcont
    have hmeas : Measurable fun y : Fin (j + 1) → ℝ ↦ ‖iteratedFDeriv ℝ (j + 1) φ
        (x + ∑ i, y i • EuclideanSpace.stdDirs N (j + 1) i) (EuclideanSpace.stdDirs N (j + 1))‖ₑ :=
      (continuous_enorm.comp hcont2).measurable
    calc ∫⁻ t : Fin j → ℝ, ‖iteratedFDeriv ℝ j φ (x + ∑ i, t i • EuclideanSpace.stdDirs N j i)
          (EuclideanSpace.stdDirs N j)‖ₑ
        ≤ ∫⁻ t : Fin j → ℝ, ∫⁻ s : ℝ, ‖iteratedFDeriv ℝ (j + 1) φ
            (x + ∑ i, (Fin.cons s t : Fin (j + 1) → ℝ) i • EuclideanSpace.stdDirs N (j + 1) i)
            (EuclideanSpace.stdDirs N (j + 1))‖ₑ := lintegral_mono hpt
      _ = _ := (MeasureTheory.lintegral_fin_succ_eq hmeas).symm

end IteratedFTC

section Remark13

open SobolevMultiIndex
open scoped BoundedContinuousFunction

variable {N : ℕ}

/-- The product of the norms of the standard basis vectors is one. -/
theorem EuclideanSpace.prod_norm_stdDirs_self :
    ∏ i : Fin N, ‖EuclideanSpace.stdDirs N N i‖ = 1 := by
  simp [EuclideanSpace.stdDirs_self]

/-- **Remark 13, the bound on smooth functions**: for `φ ∈ C_c^∞(ℝ^N)`,
`|φ x| ≤ ∫_{ℝ^N} |∂_1 ⋯ ∂_N φ|`, the iterated fundamental theorem of calculus over the
coordinates (`ContDiff.enorm_le_lintegral_iteratedFDeriv_stdDirs` at `j = N`, then the change
of variables `t ↦ x + t` in `ℝ^N`). [brezis2011functional] Chapter 9, Remark 13. -/
theorem ContDiff.enorm_le_lintegral_iteratedFDeriv_finrank {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (x : EuclideanSpace ℝ (Fin N)) :
    ‖φ x‖ₑ ≤ ∫⁻ y, ‖iteratedFDeriv ℝ N φ y (EuclideanSpace.stdDirs N N)‖ₑ := by
  refine (hφ.enorm_le_lintegral_iteratedFDeriv_stdDirs hφc x N le_rfl).trans (le_of_eq ?_)
  have hsum : ∀ t : Fin N → ℝ, ∑ i, t i • EuclideanSpace.stdDirs N N i = WithLp.toLp 2 t := by
    intro t
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (WithLp.toLp 2 t)]
    simp [EuclideanSpace.stdDirs_self]
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin N) ↦
      ‖iteratedFDeriv ℝ N φ (x + y) (EuclideanSpace.stdDirs N N)‖ₑ :=
    continuous_enorm.comp ((ContinuousMultilinearMap.apply ℝ _ ℝ _).continuous.comp
      ((hφ.continuous_iteratedFDeriv (m := N) (by simp)).comp (continuous_const.add continuous_id)))
  calc ∫⁻ t : Fin N → ℝ, ‖iteratedFDeriv ℝ N φ (x + ∑ i, t i • EuclideanSpace.stdDirs N N i)
        (EuclideanSpace.stdDirs N N)‖ₑ
      = ∫⁻ t : Fin N → ℝ, ‖iteratedFDeriv ℝ N φ (x + WithLp.toLp 2 t)
          (EuclideanSpace.stdDirs N N)‖ₑ := by simp_rw [hsum]
    _ = ∫⁻ y, ‖iteratedFDeriv ℝ N φ (x + y) (EuclideanSpace.stdDirs N N)‖ₑ :=
        (PiLp.volume_preserving_toLp (Fin N)).lintegral_comp hcont.measurable
    _ = ∫⁻ y, ‖iteratedFDeriv ℝ N φ y (EuclideanSpace.stdDirs N N)‖ₑ :=
        lintegral_add_left_eq_self (μ := volume)
          (fun y ↦ ‖iteratedFDeriv ℝ N φ y (EuclideanSpace.stdDirs N N)‖ₑ) x

/-- The `L¹` norm of the mixed component `∂_1 ⋯ ∂_N` of a tensor-valued function is at most the
`L¹` norm of the tensor. -/
theorem lintegral_enorm_apply_stdDirs_le_eLpNorm_one
    (T : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) [×N]→L[ℝ] ℝ) :
    ∫⁻ y, ‖T y (EuclideanSpace.stdDirs N N)‖ₑ ≤ eLpNorm T 1 volume := by
  refine (lintegral_mono fun y ↦ ?_).trans lintegral_enorm_le_eLpNorm_one
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [EuclideanSpace.prod_norm_stdDirs_self] using (T y).le_opNorm (EuclideanSpace.stdDirs N N)

/-- **Remark 13 (`W^{N,1}(ℝ^N) ⊂ L^∞(ℝ^N)`)**: every `u ∈ W^{N,1}(ℝ^N)` has a bounded continuous
representative `ũ` with `‖ũ x‖ ≤ ‖∂_1 ⋯ ∂_N u‖_1 ≤ ‖u‖`. For `φ ∈ C_c^∞`,
`|φ x| ≤ ∫ |∂_1 ⋯ ∂_N φ|` (`ContDiff.enorm_le_lintegral_iteratedFDeriv_finrank`), so the smooth
approximants of `u` in `W^{N,1}(ℝ^N)`
(`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`) are uniformly Cauchy; their
uniform limit is continuous, equals `u` almost everywhere, and inherits the bound.
[brezis2011functional] Chapter 9, Remark 13. -/
theorem SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one
    (u : SobolevEuclidean N N 1 ⊤) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧ fn u =ᵐ[volume] ũ ∧ ∀ x, ‖ũ x‖ ≤ ‖u‖ := by
  -- the tensor weak derivative of order `N` and its mixed component `∂_1 ⋯ ∂_N u`
  have hmem : MemSobolev (fn u) N 1 ⊤ volume := (memSobolevMultiIndex u).memSobolev
  obtain ⟨w, hw, hwp⟩ := hmem.2 N le_rfl
  rw [Measure.restrict_coe_top] at hwp
  obtain ⟨α₁, hα₁⟩ : ∃ α₁ : MultiIndexLE (Fin N) N,
      α₁ = ⟨multiIndexCount (id : Fin N → Fin N), (sum_multiIndexCount _).le⟩ := ⟨_, rfl⟩
  have hperm : (List.ofFn (multiIndexTuple
      ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) α₁.1)).Perm
      (List.ofFn (EuclideanSpace.stdDirs N N)) := by
    rw [hα₁, ← multiIndexDirections_eq_ofFn]
    refine (multiIndexDirections_multiIndexCount_perm _ id).symm.trans (List.Perm.of_eq ?_)
    congr 1
    funext i
    simp [EuclideanSpace.stdDirs_self]
  have hmixed : (fun y ↦ w y (EuclideanSpace.stdDirs N N)) =ᵐ[volume] weakDeriv u α₁ := by
    have h1 : HasWeakIteratedLineDerivOn (EuclideanSpace.stdDirs N N) (fn u)
        (fun y ↦ w y (EuclideanSpace.stdDirs N N)) ⊤ volume :=
      HasWeakIteratedFDerivOn.lineDeriv hw _
    have h2 : HasWeakIteratedLineDerivOn (EuclideanSpace.stdDirs N N) (fn u)
        (weakDeriv u α₁) ⊤ volume :=
      (hasWeakIteratedLineDerivOn u α₁).of_perm hperm
    filter_upwards [h1.ae_eq h2] with x hx
    exact hx (by simp)
  have hmixed_norm : ∫⁻ y, ‖w y (EuclideanSpace.stdDirs N N)‖ₑ ≤ ENNReal.ofReal ‖u‖ := by
    calc ∫⁻ y, ‖w y (EuclideanSpace.stdDirs N N)‖ₑ
        = ∫⁻ y, ‖weakDeriv u α₁ y‖ₑ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hmixed] with y hy
          rw [hy]
      _ = ENNReal.ofReal ‖weakDeriv u α₁‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_restrict_coe_top,
            eLpNorm_one_eq_lintegral_enorm (by
              simpa only [Measure.restrict_coe_top] using Lp.aestronglyMeasurable (weakDeriv u α₁))]
      _ ≤ ENNReal.ofReal ‖u‖ := ENNReal.ofReal_le_ofReal (norm_weakDeriv_le u α₁)
  have hwmeas : AEMeasurable (fun y ↦ ‖w y (EuclideanSpace.stdDirs N N)‖ₑ) volume :=
    ((ContinuousMultilinearMap.apply ℝ _ ℝ (EuclideanSpace.stdDirs N N)).continuous
      |>.comp_aestronglyMeasurable hwp.aestronglyMeasurable).enorm
  -- the smooth approximants and the two quantities controlling them
  obtain ⟨v, hvs, hvc, hvt⟩ := hmem.exists_seq_hasCompactSupport_tendsto_sobolevNorm le_rfl
    ENNReal.one_ne_top
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ≥0∞,
      D = fun n ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ N (v n) x - w x) 1 volume := ⟨_, rfl⟩
  have hvD : Tendsto D atTop (𝓝 0) := by
    rw [hD]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvt (fun _ ↦ zero_le)
      fun n ↦ ?_
    have hsub : HasWeakIteratedFDerivOn N (v n - fn u)
        (iteratedFDeriv ℝ N (v n) - w) ⊤ volume :=
      ((hvs n).contDiffOn.hasWeakIteratedFDerivOn (by simp)).sub hw
    exact hsub.eLpNorm_le_sobolevNorm_top le_rfl ENNReal.one_ne_top le_rfl
  have hv0 : Tendsto (fun n ↦ eLpNorm (v n - fn u) 1 volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvt (fun _ ↦ zero_le)
      fun n ↦ ?_
    have hloc : LocallyIntegrable (v n - fn u) volume :=
      ((hvs n).continuous.locallyIntegrable).sub
        ((SobolevEuclidean.memLp_fn u).locallyIntegrable le_rfl)
    have h0 := (hasWeakIteratedFDerivOn_zero (μ := volume) (Ω := ⊤)
      (locallyIntegrableOn_univ.2 hloc)).eLpNorm_le_sobolevNorm_top le_rfl ENNReal.one_ne_top
      (Nat.zero_le N)
    refine le_trans ?_ h0
    refine eLpNorm_mono_enorm_ae hloc.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
  -- the sup bound for one approximant and for a difference of two
  have hmixed_le : ∀ n, ∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ
      ≤ D n := fun n ↦ by
    rw [hD]
    exact lintegral_enorm_apply_stdDirs_le_eLpNorm_one fun y ↦ iteratedFDeriv ℝ N (v n) y - w y
  have hvmeas : ∀ n, AEMeasurable
      (fun y ↦ ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ) volume := by
    intro n
    have h1 : AEStronglyMeasurable (fun y ↦ iteratedFDeriv ℝ N (v n) y - w y) volume :=
      ((hvs n).continuous_iteratedFDeriv (m := N) (by simp)).aestronglyMeasurable.sub
        hwp.aestronglyMeasurable
    exact ((ContinuousMultilinearMap.apply ℝ _ ℝ (EuclideanSpace.stdDirs N N)).continuous
      |>.comp_aestronglyMeasurable h1).enorm
  have hbound : ∀ n x, ‖v n x‖ₑ ≤ D n + ENNReal.ofReal ‖u‖ := fun n x ↦ by
    refine ((hvs n).enorm_le_lintegral_iteratedFDeriv_finrank (hvc n) x).trans ?_
    calc ∫⁻ y, ‖iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)‖ₑ
        ≤ ∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ
          + ‖w y (EuclideanSpace.stdDirs N N)‖ₑ := by
          refine lintegral_mono fun y ↦ ?_
          rw [sub_apply]
          calc ‖iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)‖ₑ
              = ‖iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)
                  - w y (EuclideanSpace.stdDirs N N) + w y (EuclideanSpace.stdDirs N N)‖ₑ := by
                rw [sub_add_cancel]
            _ ≤ _ := enorm_add_le _ _
      _ = (∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ)
          + ∫⁻ y, ‖w y (EuclideanSpace.stdDirs N N)‖ₑ := lintegral_add_right' _ hwmeas
      _ ≤ D n + ENNReal.ofReal ‖u‖ := add_le_add (hmixed_le n) hmixed_norm
  have hdiff : ∀ n m x, ‖v n x - v m x‖ₑ ≤ D n + D m := fun n m x ↦ by
    have hs : ContDiff ℝ ∞ (v n - v m) := (hvs n).sub (hvs m)
    have hc : HasCompactSupport (v n - v m) := (hvc n).sub (hvc m)
    refine (hs.enorm_le_lintegral_iteratedFDeriv_finrank hc x).trans ?_
    rw [iteratedFDeriv_sub ((hvs n).of_le (by simp)) ((hvs m).of_le (by simp))]
    calc ∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) - iteratedFDeriv ℝ N (v m)) y
          (EuclideanSpace.stdDirs N N)‖ₑ
        ≤ ∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ
          + ‖(iteratedFDeriv ℝ N (v m) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ := by
          refine lintegral_mono fun y ↦ ?_
          simp only [Pi.sub_apply, sub_apply]
          calc ‖iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)
                - iteratedFDeriv ℝ N (v m) y (EuclideanSpace.stdDirs N N)‖ₑ
              = ‖(iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)
                  - w y (EuclideanSpace.stdDirs N N))
                - (iteratedFDeriv ℝ N (v m) y (EuclideanSpace.stdDirs N N)
                  - w y (EuclideanSpace.stdDirs N N))‖ₑ := by rw [sub_sub_sub_cancel_right]
            _ ≤ _ := enorm_sub_le
      _ = (∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ)
          + ∫⁻ y, ‖(iteratedFDeriv ℝ N (v m) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ :=
          lintegral_add_left' (hvmeas n) _
      _ ≤ D n + D m := add_le_add (hmixed_le n) (hmixed_le m)
  -- the approximants as bounded continuous functions, Cauchy in the sup norm
  choose M hM using fun n ↦ (hvc n).exists_bound_of_continuous (hvs n).continuous
  obtain ⟨U, hU⟩ : ∃ U : ℕ → EuclideanSpace ℝ (Fin N) →ᵇ ℝ, ∀ n x, U n x = v n x :=
    ⟨fun n ↦ BoundedContinuousFunction.ofNormedAddCommGroup (v n) (hvs n).continuous (M n) (hM n),
      fun n x ↦ rfl⟩
  have hcauchy : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ0, hδt, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ ≠ ⊤ ∧ (δ + δ).toReal < ε := by
      refine ⟨ENNReal.ofReal (ε / 4), ENNReal.ofReal_pos.2 (by positivity), ENNReal.ofReal_ne_top,
        ?_⟩
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.toReal_ofReal (by positivity)]
      linarith
    obtain ⟨N₀, hN₀⟩ := (ENNReal.tendsto_nhds_zero.1 hvD δ hδ0).exists_forall_of_atTop
    refine ⟨N₀, fun m hm n hn ↦ ?_⟩
    have hb : dist (U m) (U n) ≤ (δ + δ).toReal := by
      refine (BoundedContinuousFunction.dist_le ENNReal.toReal_nonneg).2 fun x ↦ ?_
      rw [hU, hU, dist_eq_norm, ← toReal_enorm]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hδt, hδt⟩)
        ((hdiff m n x).trans (add_le_add (hN₀ m hm) (hN₀ n hn)))
    exact hb.trans_lt hδ
  -- the uniform limit
  obtain ⟨Ũ, hŨ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hpt : ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (Ũ x)) := fun x ↦ by
    have := ((continuous_eval_const x).tendsto Ũ).comp hŨ
    simpa only [Function.comp_def, hU] using this
  refine ⟨Ũ, Ũ.continuous, ?_, fun x ↦ ?_⟩
  -- it equals `u` almost everywhere
  · have hmeas : TendstoInMeasure volume v atTop (fn u) :=
      tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hv0
    obtain ⟨ns, hns_mono, hns⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hns] with x hx
    exact tendsto_nhds_unique hx ((hpt x).comp hns_mono.tendsto_atTop)
  -- the sup bound
  · rw [← ENNReal.ofReal_le_ofReal_iff (norm_nonneg _), ofReal_norm]
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    have hlim : Tendsto (fun n ↦ ‖v n x‖ₑ) atTop (𝓝 ‖Ũ x‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hpt x)
    refine le_of_tendsto hlim ?_
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hvD δ (by exact_mod_cast hδ)] with n hn
    calc ‖v n x‖ₑ ≤ D n + ENNReal.ofReal ‖u‖ := hbound n x
      _ ≤ ENNReal.ofReal ‖u‖ + δ := by rw [add_comm]; exact add_le_add le_rfl hn

end Remark13

/-! ### Lemma 9.4: Gagliardo's product lemma in its general form -/

section Gagliardo

/-- Omitting the coordinate `succ j` from `x : Fin (n + 2) → α` keeps `x 0` in front:
`x ∘ (succ j).succAbove = Fin.cons (x 0) ((x ∘ succ) ∘ j.succAbove)`. -/
theorem Fin.comp_succ_succAbove {n : ℕ} {α : Type*} (x : Fin (n + 2) → α) (j : Fin (n + 1)) :
    x ∘ (Fin.succ j).succAbove = Fin.cons (x 0) ((x ∘ Fin.succ) ∘ j.succAbove) := by
  ext k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp
  · simp [Fin.succ_succAbove_succ]

/-- Omitting the coordinate `0` from `x : Fin (n + 1) → α` is `x ∘ succ`. -/
theorem Fin.comp_zero_succAbove {n : ℕ} {α : Type*} (x : Fin (n + 1) → α) :
    x ∘ (0 : Fin (n + 1)).succAbove = x ∘ Fin.succ := by
  ext k
  simp

/-- `Fin.cons` is measurable in the pair `(head, tail)`. -/
theorem measurable_fin_cons_prod {m : ℕ} :
    Measurable fun p : ℝ × (Fin m → ℝ) ↦ (Fin.cons p.1 p.2 : Fin (m + 1) → ℝ) := by
  refine Measurable.of_eval fun k ↦ ?_
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply k).comp measurable_snd

/-- `Fin.cons s` is measurable for a fixed head `s`. -/
theorem measurable_fin_cons_const {m : ℕ} (s : ℝ) :
    Measurable fun t : Fin m → ℝ ↦ (Fin.cons s t : Fin (m + 1) → ℝ) :=
  measurable_fin_cons_prod.comp (measurable_const.prodMk measurable_id)

/-- Omitting a coordinate is measurable. -/
theorem measurable_comp_succAbove {m : ℕ} (i : Fin (m + 1)) :
    Measurable fun x : Fin (m + 1) → ℝ ↦ x ∘ i.succAbove :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- **Fubini for one more coordinate, the first coordinate outermost**: an integral over
`ℝ^{j+1}` is the integral over the first coordinate of the integral over the last `j`, the
coordinates being read as `Fin.cons s t`. -/
theorem MeasureTheory.lintegral_fin_succ_eq' {j : ℕ} {H : (Fin (j + 1) → ℝ) → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ y, H y = ∫⁻ s : ℝ, ∫⁻ t : Fin j → ℝ, H (Fin.cons s t) := by
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (j + 1) ↦ ℝ) 0).symm
  rw [← hmp.lintegral_comp hH, Measure.volume_eq_prod,
    lintegral_prod (fun a : ℝ × (Fin j → ℝ) ↦
      H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) ↦ ℝ) 0).symm a))
      (hH.comp hmp.measurable).aemeasurable]
  refine lintegral_congr fun s ↦ lintegral_congr fun t ↦ ?_
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

/-- The integral over `ℝ^0` is evaluation at the unique point. -/
theorem MeasureTheory.lintegral_fin_zero (H : (Fin 0 → ℝ) → ℝ≥0∞) :
    ∫⁻ t : Fin 0 → ℝ, H t = H (Fin.elim0) := by
  rw [volume_pi, Measure.pi_of_empty, lintegral_dirac]
  exact congrArg H (funext fun k ↦ k.elim0)

/-- **Lemma 9.4 (Gagliardo's lemma), the case `N = 2`**: `∫∫ f₀(x₁) f₁(x₀) = (∫ f₀) (∫ f₁)`. -/
theorem MeasureTheory.lintegral_prod_comp_succAbove_two
    (f : Fin 2 → (Fin 1 → ℝ) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x ∘ i.succAbove) = ∏ i, ∫⁻ y, f i y := by
  have hG : Measurable fun x : Fin 2 → ℝ ↦ ∏ i, f i (x ∘ i.succAbove) :=
    Finset.measurable_prod _ fun i _ ↦ (hf i).comp (measurable_comp_succAbove i)
  rw [lintegral_fin_succ_eq' hG, Fin.prod_univ_two]
  have h1 : ∀ s : ℝ, ∫⁻ t : Fin 1 → ℝ, ∏ i, f i (Fin.cons s t ∘ i.succAbove)
      = (∫⁻ t, f 0 t) * f 1 (Fin.cons s Fin.elim0) := by
    intro s
    rw [← lintegral_mul_const _ (hf 0)]
    refine lintegral_congr fun t ↦ ?_
    rw [Fin.prod_univ_two, Fin.comp_zero_succAbove]
    have e0 : Fin.cons s t ∘ Fin.succ = t := by
      ext k
      simp
    have e1 : Fin.cons s t ∘ (1 : Fin 2).succAbove = Fin.cons s Fin.elim0 := by
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.comp_succ_succAbove, Fin.cons_zero]
      congr
      ext k
      exact k.elim0
    rw [e0, e1]
  simp_rw [h1]
  rw [lintegral_const_mul (f := fun s ↦ f 1 (Fin.cons s Fin.elim0)) _ ((hf 1).comp
    (measurable_fin_cons_prod.comp (measurable_id.prodMk measurable_const)))]
  congr 1
  rw [lintegral_fin_succ_eq' (hf 1)]
  refine lintegral_congr fun s ↦ ?_
  rw [lintegral_fin_zero]

/-- **Lemma 9.4 (Gagliardo's lemma), the inductive step**, from `N = n + 2` functions of `N − 1`
variables to `N + 1` functions of `N` variables: fix the first coordinate `s` (Fubini,
`MeasureTheory.lintegral_fin_succ_eq'`); for fixed `s` the factor `f 0` does not depend on `s`
and Hölder's inequality with exponents `N` and `N' = N/(N − 1)` separates it from the product of
the other `N` factors, to which the induction hypothesis applies with the functions
`f_i(s, ·)^{N'}`; then integrate in `s`, where each `s ↦ ‖f_i(s, ·)‖_{L^N}` lies in `L^N(ℝ)`, by
the generalized Hölder inequality for `N` factors (`ENNReal.lintegral_prod_norm_pow_le`) and
Fubini again ([brezis2011functional] §9.3, proof of Lemma 9.4). -/
theorem MeasureTheory.lintegral_prod_comp_succAbove_le_succ {n : ℕ}
    (ih : ∀ f : Fin (n + 2) → (Fin (n + 1) → ℝ) → ℝ≥0∞, (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x ∘ i.succAbove)
        ≤ ∏ i, (∫⁻ y, f i y ^ ((n : ℝ) + 1)) ^ (1 / ((n : ℝ) + 1)))
    (f : Fin (n + 3) → (Fin (n + 2) → ℝ) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x ∘ i.succAbove)
      ≤ ∏ i, (∫⁻ y, f i y ^ ((n : ℝ) + 2)) ^ (1 / ((n : ℝ) + 2)) := by
  -- the exponents
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (n : ℝ) + 2 := ⟨_, rfl⟩
  have hq1 : 1 < q := by rw [hq]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hq0 : 0 < q := zero_lt_one.trans hq1
  obtain ⟨q', hq'⟩ : ∃ q' : ℝ, q' = Real.conjExponent q := ⟨_, rfl⟩
  have hqq' : q.HolderConjugate q' := hq' ▸ Real.HolderConjugate.conjExponent hq1
  have hq'0 : 0 < q' := hqq'.symm.pos
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hq2 : q - 1 = (n : ℝ) + 1 := by rw [hq]; ring
  have hq'n : q' * ((n : ℝ) + 1) = q := by
    rw [hq', Real.conjExponent, hq2, div_mul_cancel₀ _ hn1.ne']
  rw [← hq]
  -- measurability
  have hG : Measurable fun x : Fin (n + 3) → ℝ ↦ ∏ i, f i (x ∘ i.succAbove) :=
    Finset.measurable_prod _ fun i _ ↦ (hf i).comp (measurable_comp_succAbove i)
  have hg : ∀ (s : ℝ) (j : Fin (n + 2)), Measurable fun y : Fin (n + 1) → ℝ ↦
      f (Fin.succ j) (Fin.cons s y) := fun s j ↦ (hf _).comp (measurable_fin_cons_const s)
  have hF : ∀ j : Fin (n + 2), Measurable fun s : ℝ ↦
      ∫⁻ y : Fin (n + 1) → ℝ, f (Fin.succ j) (Fin.cons s y) ^ q := fun j ↦
    Measurable.lintegral_prod_right (((hf _).comp measurable_fin_cons_prod).pow_const q)
  -- Step A: Fubini, the first coordinate outermost, and the product split
  rw [lintegral_fin_succ_eq' hG]
  have hsplit : ∀ (s : ℝ) (t : Fin (n + 2) → ℝ), ∏ i, f i (Fin.cons s t ∘ i.succAbove)
      = f 0 t * ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove)) := by
    intro s t
    rw [Fin.prod_univ_succ, Fin.comp_zero_succAbove]
    have e0 : Fin.cons s t ∘ Fin.succ = t := by
      ext k
      simp
    rw [e0]
    congr 1
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Fin.comp_succ_succAbove, Fin.cons_zero, e0]
  simp_rw [hsplit]
  -- Step B: the inner integral, by Hölder and the induction hypothesis
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ≥0∞, A₀ = (∫⁻ t, f 0 t ^ q) ^ (1 / q) := ⟨_, rfl⟩
  have hinner : ∀ s : ℝ, ∫⁻ t : Fin (n + 2) → ℝ,
      f 0 t * ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove))
      ≤ A₀ * ∏ j : Fin (n + 2),
        (∫⁻ y : Fin (n + 1) → ℝ, f (Fin.succ j) (Fin.cons s y) ^ q) ^ (1 / q) := by
    intro s
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hqq' (f := f 0)
      (g := fun t ↦ ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove)))
      (hf 0).aemeasurable
      (Finset.measurable_prod (Finset.univ : Finset (Fin (n + 2))) fun j _ ↦
        (hg s j).comp (measurable_comp_succAbove j)).aemeasurable
    refine hH.trans ?_
    rw [hA₀]
    refine mul_le_mul' le_rfl ?_
    -- the induction hypothesis on the functions `f (succ j) (cons s ·) ^ q'`
    have hIH := ih (fun j y ↦ f (Fin.succ j) (Fin.cons s y) ^ q') fun j ↦ (hg s j).pow_const q'
    have e1 : ∀ t : Fin (n + 2) → ℝ,
        (∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove))) ^ q'
          = ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove)) ^ q' := fun t ↦
      (ENNReal.prod_rpow_of_nonneg hq'0.le).symm
    have e2 : ∫⁻ t : Fin (n + 2) → ℝ,
        (∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove))) ^ q'
          = ∫⁻ t : Fin (n + 2) → ℝ,
            ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove)) ^ q' :=
      lintegral_congr e1
    rw [e2]
    refine (ENNReal.rpow_le_rpow hIH (by positivity)).trans_eq ?_
    rw [← ENNReal.prod_rpow_of_nonneg (by positivity)]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← ENNReal.rpow_mul]
    congr 1
    · refine lintegral_congr fun y ↦ ?_
      rw [← ENNReal.rpow_mul, hq'n]
    · rw [hq', Real.conjExponent, hq2, hq]
      field_simp
  -- Step C: the outer integral, by the generalized Hölder inequality
  refine (lintegral_mono hinner).trans ?_
  rw [lintegral_const_mul _ (Finset.measurable_prod _ fun j _ ↦ (hF j).pow_const _)]
  rw [Fin.prod_univ_succ, ← hA₀]
  refine mul_le_mul' le_rfl ?_
  have hHolder := ENNReal.lintegral_prod_norm_pow_le (μ := volume) Finset.univ
    (f := fun j s ↦ ∫⁻ y : Fin (n + 1) → ℝ, f (Fin.succ j) (Fin.cons s y) ^ q)
    (fun j _ ↦ (hF j).aemeasurable) (p := fun _ ↦ 1 / q) ?_ fun _ _ ↦ by positivity
  · refine hHolder.trans_eq ?_
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [lintegral_fin_succ_eq' ((hf _).pow_const q)]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hq]
    push_cast
    field_simp

/-- **Lemma 9.4 (Gagliardo's lemma), general form**: for `N = n + 2 ≥ 2` and measurable
`f i : ℝ^{N−1} → ℝ≥0∞`, `i < N`, the function `x ↦ ∏ i, f i x̃_i`, where `x̃_i = x ∘ i.succAbove` is
`x ∈ ℝ^N` with its `i`-th coordinate omitted, satisfies
`∫_{ℝ^N} ∏ i, f i x̃_i ≤ ∏ i, ‖f i‖_{L^{N−1}(ℝ^{N−1})}`; in particular it is integrable when every
`f i ∈ L^{N−1}(ℝ^{N−1})`. The case `N = 2` is Fubini
(`MeasureTheory.lintegral_prod_comp_succAbove_two`), the induction on `N` is
`MeasureTheory.lintegral_prod_comp_succAbove_le_succ`. Mathlib's
`MeasureTheory.lintegral_prod_lintegral_pow_le` is the special case
`f i x̃_i = (∫ f (update x i t) dt)^{1/(N−1)}` for a single `f`, which is all Theorem 9.9 needs.
[brezis2011functional] §9.3, Lemma 9.4. -/
theorem MeasureTheory.lintegral_prod_comp_succAbove_le {n : ℕ}
    (f : Fin (n + 2) → (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x ∘ i.succAbove)
      ≤ ∏ i, (∫⁻ y, f i y ^ ((n : ℝ) + 1)) ^ (1 / ((n : ℝ) + 1)) := by
  induction n with
  | zero =>
    rw [lintegral_prod_comp_succAbove_two f hf]
    simp
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [e]
    exact lintegral_prod_comp_succAbove_le_succ ih f hf

end Gagliardo
