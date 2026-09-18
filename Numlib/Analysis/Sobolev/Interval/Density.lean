/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.Analysis.Sobolev.Interval.Extension

/-!
# Density of `C_c^∞(ℝ)` in `W^{1,p}(I)`

The density theorem of [brezis2011functional] Theorem 8.7 — the restrictions to an open interval
`I` of the smooth compactly supported functions on `ℝ` are dense in `W^{1,p}(I)` for
`1 ≤ p < ∞` — together with Lemma 8.4 (convolution with an integrable kernel commutes with the
weak derivative on `ℝ`) and the bridge between the one-dimensional space `SobolevIntervalLp` and
the tensor formulation `MemSobolev` / `sobolevNorm` of `Numlib/Analysis/Sobolev/Domain.lean`,
on which the whole-space theory of `Numlib/Analysis/Sobolev/Density.lean` and
`Numlib/Analysis/Sobolev/Friedrichs.lean` is stated.

## Main statements

* `HasWeakDerivOn.hasWeakFDerivOn` and `HasWeakFDerivOn.hasWeakDerivOn`: on the line, a weak
  derivative `w` in the sense of `HasWeakDerivOn` is the weak derivative `x ↦ (t ↦ t w x)` in the
  tensor sense, and conversely the tensor derivative evaluated at `1` is a weak derivative;
  `memSobolevIntervalLp_iff_memSobolev`: `W^{1,p}(I)` in the two formulations contains the same
  functions.
* `SobolevIntervalLp.sobolevNorm_eq`: **the norm of `SobolevIntervalLp 1 p I` is the Sobolev norm
  `sobolevNorm (fn u) 1 p I volume`** of the tensor formulation, exactly — in dimension one the
  derivative tensor `ℝ →L[ℝ] ℝ` of `u` at `x` has operator norm `|u'(x)|`, so the `ℓ^p` sums
  agree term by term.
* `SobolevIntervalLp.exists_seq_contDiff_hasCompactSupport_tendsto` (**Theorem 8.7**): for
  `1 ≤ p < ∞` and `u ∈ W^{1,p}(I)` there are `g n ∈ C_c^∞(ℝ)` whose restrictions to `I`, as
  elements `v n` of `W^{1,p}(I)`, converge to `u`;
  `SobolevIntervalLp.dense_contDiff_hasCompactSupport` is the same as the density of a set.
* `SobolevIntervalLp.hasWeakDerivOn_convolution`, `memSobolevIntervalLp_convolution`
  (**Lemma 8.4**): for `ρ ∈ L¹(ℝ)` and `v ∈ W^{1,p}(ℝ)`, `1 ≤ p ≤ ∞`, `ρ ⋆ v ∈ W^{1,p}(ℝ)` with
  `(ρ ⋆ v)' = ρ ⋆ v'`.

## Route

Theorem 8.7 is not re-proved by the book's mollify-and-cut-off argument: the whole-space density
theorem is in the backbone in the tensor formulation,
`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`, whose proof is exactly the book's
steps (a)–(c). So the theorem here is: extend `u` to `W^{1,p}(ℝ)` by the extension operator
`SobolevIntervalLp.extensionCLM` (Theorem 8.6), pass to the tensor formulation on `ℝ`, apply the
whole-space theorem, and restrict to `I` with `SobolevMultiIndex.restrictL`, which does not
increase the norm; the comparison of the norms is `SobolevIntervalLp.sobolevNorm_eq`. Lemma 8.4
is the one-dimensional case of [brezis2011functional] Lemma 9.1,
`HasWeakIteratedLineDerivOn.convolution_of_integrable`, and is not needed for the theorem.

Every statement about density needs `p < ∞`: Theorem 8.7 fails at `p = ∞`, where uniform limits
of `C¹` functions have continuous derivatives but `W^{1,∞}` functions need not.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Topology

noncomputable section

/-! ### The two formulations of the first weak derivative on the line -/

section Bridge

variable {I : Opens ℝ} {f w : ℝ → ℝ}

/-- A first-order weak derivative in the tensor sense (`HasWeakFDerivOn`), evaluated at the
direction `1`, is a weak derivative on the line (`HasWeakDerivOn`). -/
theorem HasWeakFDerivOn.hasWeakDerivOn {W : ℝ → ℝ →L[ℝ] ℝ} (h : HasWeakFDerivOn f W I volume) :
    HasWeakDerivOn f (fun x ↦ W x 1) I := by
  have := h.lineDeriv (fun _ : Fin 1 ↦ (1 : ℝ))
  simpa only [continuousMultilinearCurryFin1_symm_apply] using this

/-- A weak derivative `w` on the line is, read as the family of linear maps `t ↦ t w x`, a
first-order weak derivative in the tensor sense: on `ℝ` the Fréchet derivative of a test function
in the direction `v` is `v φ'`. -/
theorem HasWeakDerivOn.hasWeakFDerivOn (h : HasWeakDerivOn f w I) :
    HasWeakFDerivOn f (fun x ↦ ContinuousLinearMap.toSpanSingleton ℝ (w x)) I volume := by
  obtain ⟨h1, h2, h3⟩ := hasWeakDerivOn_iff.1 h
  refine hasWeakFDerivOn_iff.2 ⟨h1, ?_, fun φ v ↦ ?_⟩
  · exact h2.comp_continuousLinearMap
      (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  · have e1 : ∀ x, fderiv ℝ φ x v • f x = v * (deriv φ x * f x) := fun x ↦ by
      rw [fderiv_eq_smul_deriv, smul_eq_mul, smul_eq_mul, mul_assoc]
    have e2 : ∀ x, φ x • ContinuousLinearMap.toSpanSingleton ℝ (w x) v = v * (φ x * w x) :=
      fun x ↦ by rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, smul_eq_mul]; ring
    simp only [e1, e2, integral_const_mul, h3 φ, mul_neg]

/-- **The two formulations of `W^{m,p}(I)` agree**: a function lies in `W^{m,p}(I)` in the sense
of `MemSobolevIntervalLp` (the multi-index formulation on the one-element basis of `ℝ`) if and
only if it does in the tensor sense of `MemSobolev`. -/
theorem memSobolevIntervalLp_iff_memSobolev {m : ℕ} {p : ℝ≥0∞} :
    MemSobolevIntervalLp f m p I ↔ MemSobolev f m p I volume :=
  (memSobolev_iff_memSobolevMultiIndex (Module.Basis.singleton Unit ℝ)).symm

end Bridge

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} {m : ℕ}

/-- The function of an element of `W^{m,p}(I)` lies in `W^{m,p}(I)` in the tensor sense. -/
theorem memSobolev_fn (u : SobolevIntervalLp m p I) : MemSobolev (fn u) m p I volume :=
  memSobolevIntervalLp_iff_memSobolev.1 (memSobolevIntervalLp_fn u)

/-- The weak derivative of order `0` of `fn u` chosen by `weakIteratedFDeriv` is `fn u` itself,
almost everywhere on `I`. -/
theorem weakIteratedFDeriv_zero_ae_eq [Fact (1 ≤ p)] (u : SobolevIntervalLp m p I) :
    weakIteratedFDeriv 0 (fn u) I volume =ᵐ[volume.restrict (I : Set ℝ)]
      fun x ↦ (continuousMultilinearCurryFin0 ℝ ℝ ℝ).symm (fn u x) :=
  (ae_restrict_iff' I.isOpen.measurableSet).2
    (hasWeakIteratedFDerivOn_zero (μ := volume)
      ((memLp_deriv u 0).locallyIntegrableOn Fact.out)).weakIteratedFDeriv_ae_eq

/-- The weak derivative of order `1` of `fn u` chosen by `weakIteratedFDeriv` is the family of
linear maps `t ↦ t u'(x)`, almost everywhere on `I`. -/
theorem weakIteratedFDeriv_one_ae_eq (u : SobolevIntervalLp (m + 1) p I) :
    weakIteratedFDeriv 1 (fn u) I volume =ᵐ[volume.restrict (I : Set ℝ)]
      fun x ↦ (continuousMultilinearCurryFin1 ℝ ℝ ℝ).symm
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv u 1 x)) :=
  (ae_restrict_iff' I.isOpen.measurableSet).2
    (HasWeakDerivOn.hasWeakFDerivOn (hasWeakDerivOn_deriv_succ u 0)).weakIteratedFDeriv_ae_eq

/-- The `L^p(I)` norm of the weak derivative of order `j ≤ 1` of `fn u` in the tensor sense is
the norm of `deriv u j`, for `u ∈ W^{1,p}(I)`. -/
theorem eLpNorm_weakIteratedFDeriv_eq [Fact (1 ≤ p)] (u : SobolevIntervalLp 1 p I) (j : Fin 2) :
    eLpNorm (weakIteratedFDeriv j (fn u) I volume) p (volume.restrict (I : Set ℝ))
      = ‖deriv u j‖ₑ := by
  rw [Lp.enorm_def]
  have hmeas : AEStronglyMeasurable (weakIteratedFDeriv j (fn u) I volume)
      (volume.restrict (I : Set ℝ)) :=
    ((memSobolev_fn u).memLp_weakIteratedFDeriv (Fin.is_le j)).aestronglyMeasurable
  refine eLpNorm_congr_norm_ae hmeas (Lp.aestronglyMeasurable _) ?_
  fin_cases j
  · filter_upwards [weakIteratedFDeriv_zero_ae_eq u] with x hx
    rw [hx, LinearIsometryEquiv.norm_map]
    rfl
  · filter_upwards [weakIteratedFDeriv_one_ae_eq u] with x hx
    rw [hx, LinearIsometryEquiv.norm_map, ContinuousLinearMap.norm_toSpanSingleton]
    rfl

variable [Fact (1 ≤ p)]

/-- **The norm of `W^{m,p}(I)` in `ℝ≥0∞`, `p < ∞`**: `‖u‖ₑ = (∑_{j ≤ m} ‖u^{(j)}‖_p^p)^{1/p}`. -/
theorem enorm_eq_sum (hp : p ≠ ⊤) (u : SobolevIntervalLp m p I) :
    ‖u‖ₑ = (∑ j : Fin (m + 1), ‖deriv u j‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [← ofReal_norm, norm_eq_sum hp,
    ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
  refine congrArg (· ^ (1 / p.toReal)) (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]

omit [Fact (1 ≤ p)] in
/-- **The norm of `W^{m,∞}(I)` in `ℝ≥0∞`**: `‖u‖ₑ = max_{j ≤ m} ‖u^{(j)}‖_∞`. -/
theorem enorm_eq_iSup (u : SobolevIntervalLp m ⊤ I) :
    ‖u‖ₑ = ⨆ j : Fin (m + 1), ‖deriv u j‖ₑ := by
  have hne : (⨆ j : Fin (m + 1), ‖deriv u j‖ₑ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑ j : Fin (m + 1), ‖deriv u j‖ₑ) ?_ ?_
    · exact ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top
    · exact iSup_le fun j ↦ Finset.single_le_sum (f := fun j ↦ ‖deriv u j‖ₑ)
        (fun _ _ ↦ zero_le) (Finset.mem_univ j)
  rw [← ofReal_norm, norm_eq_ciSup, ← ENNReal.ofReal_toReal hne,
    ENNReal.toReal_iSup fun _ ↦ enorm_ne_top]
  simp only [toReal_enorm]

/-- **The bridge to the tensor formulation in dimension one**: the norm of
`u ∈ SobolevIntervalLp 1 p I` is the Sobolev norm `sobolevNorm (fn u) 1 p I volume` of the
tensor formulation of `Numlib/Analysis/Sobolev/Domain.lean`, exactly: the derivative tensor
`ℝ →L[ℝ] ℝ` of `u` at `x` is `t ↦ t u'(x)`, of operator norm `|u'(x)|`, so the two `ℓ^p` sums
(the two maxima at `p = ∞`) of `L^p(I)` norms agree term by term. -/
theorem sobolevNorm_eq (u : SobolevIntervalLp 1 p I) :
    sobolevNorm (fn u) 1 p I volume = ‖u‖ₑ := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · simp only [sobolevNorm, ↓reduceIte, enorm_eq_iSup]
    exact iSup_congr fun j ↦ eLpNorm_weakIteratedFDeriv_eq u j
  · simp only [sobolevNorm, hp, ↓reduceIte, enorm_eq_sum hp]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [eLpNorm_weakIteratedFDeriv_eq u j]

/-! ### Theorem 8.7: density of `C_c^∞(ℝ)` in `W^{1,p}(I)` -/

/-- **Theorem 8.7 of [brezis2011functional] (density)**: for `1 ≤ p < ∞`, a nonempty open
interval `I` and `u ∈ W^{1,p}(I)`, there is a sequence `g n` of smooth compactly supported
functions on `ℝ` whose restrictions to `I`, as elements `v n` of `W^{1,p}(I)`, converge to `u`
in `W^{1,p}(I)`. The extension `P u ∈ W^{1,p}(ℝ)` (`SobolevIntervalLp.extensionCLM`, Theorem
8.6) is approximated in `W^{1,p}(ℝ)` by `C_c^∞(ℝ)` functions
(`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`, the book's mollify-and-cut-off
argument), the Sobolev norm being the norm of the type (`SobolevIntervalLp.sobolevNorm_eq`), and
restriction to `I` (`SobolevMultiIndex.restrictL`) does not increase the norm. -/
theorem exists_seq_contDiff_hasCompactSupport_tendsto (hI : (I : Set ℝ).OrdConnected)
    (hne : (I : Set ℝ).Nonempty) (hp : p ≠ ⊤) (u : SobolevIntervalLp 1 p I) :
    ∃ g : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      ∃ v : ℕ → SobolevIntervalLp 1 p I,
        (∀ n, fn (v n) =ᵐ[volume.restrict (I : Set ℝ)] g n) ∧ Tendsto v atTop (𝓝 u) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨P, hP⟩ : ∃ P : SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤,
      P = extensionCLM hI hne := ⟨_, rfl⟩
  have hPfn : ∀ w, fn (P w) =ᵐ[volume.restrict (I : Set ℝ)] fn w := by
    intro w
    rw [hP]
    exact fn_extensionCLM hI hne w
  obtain ⟨g, hgs, hgc, hgt⟩ :=
    (memSobolev_fn (P u)).exists_seq_hasCompactSupport_tendsto_sobolevNorm hp1 hp
  choose V hV using fun n ↦ (hgs n).exists_sobolevMultiIndex_of_hasCompactSupport
    (b := Module.Basis.singleton Unit ℝ) (p := p) (Ω := (⊤ : Opens ℝ)) (μ := volume) (hgc n)
  obtain ⟨R, hR⟩ : ∃ R : SobolevIntervalLp 1 p ⊤ →L[ℝ] SobolevIntervalLp 1 p I,
      R = SobolevMultiIndex.restrictL ℝ (Module.Basis.singleton Unit ℝ) 1 p volume
        (le_top : I ≤ ⊤) := ⟨_, rfl⟩
  have hRfn : ∀ w, fn (R w) =ᵐ[volume.restrict (I : Set ℝ)] fn w := by
    intro w
    rw [hR]
    exact SobolevMultiIndex.fn_restrictL _ _
  have hRle : ∀ w, ‖R w‖ ≤ ‖w‖ := by
    intro w
    rw [hR]
    exact SobolevMultiIndex.norm_restrictL_apply_le _ _
  refine ⟨g, hgs, hgc, fun n ↦ R (V n), fun n ↦ ?_, ?_⟩
  · exact (hRfn _).trans (ae_mono (Measure.restrict_mono le_top le_rfl) (hV n))
  · have hRPu : R (P u) = u := SobolevMultiIndex.ext_of_fn_ae_eq ((hRfn _).trans (hPfn u))
    rw [← hRPu, tendsto_iff_norm_sub_tendsto_zero]
    have hsub : ∀ n, sobolevNorm (fn (V n - P u)) 1 p ⊤ volume
        = sobolevNorm (g n - fn (P u)) 1 p ⊤ volume := fun n ↦
      sobolevNorm_congr_ae ((SobolevMultiIndex.fn_sub _ _).trans
        ((hV n).sub (EventuallyEq.refl _ _)))
    have hbound : ∀ n, ‖R (V n) - R (P u)‖
        ≤ (sobolevNorm (g n - fn (P u)) 1 p ⊤ volume).toReal := by
      intro n
      rw [← map_sub, ← hsub n, sobolevNorm_eq, toReal_enorm]
      exact hRle _
    refine squeeze_zero (fun _ ↦ norm_nonneg _) hbound ?_
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgt
    simpa [Function.comp_def] using this

/-- **Theorem 8.7 of [brezis2011functional], as the density of a set**: for `1 ≤ p < ∞` and a
nonempty open interval `I`, the elements of `W^{1,p}(I)` carried by the restrictions of smooth
compactly supported functions on `ℝ` are dense in `W^{1,p}(I)`. -/
theorem dense_contDiff_hasCompactSupport (hI : (I : Set ℝ).OrdConnected)
    (hne : (I : Set ℝ).Nonempty) (hp : p ≠ ⊤) :
    Dense {v : SobolevIntervalLp 1 p I | ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      fn v =ᵐ[volume.restrict (I : Set ℝ)] g} := fun u ↦ by
  obtain ⟨g, hgs, hgc, v, hv, hvt⟩ := exists_seq_contDiff_hasCompactSupport_tendsto hI hne hp u
  exact mem_closure_of_tendsto hvt (Eventually.of_forall fun n ↦ ⟨g n, hgs n, hgc n, hv n⟩)

/-! ### Lemma 8.4: convolution with an integrable kernel -/

/-- **Lemma 8.4 of [brezis2011functional]**: for `ρ ∈ L¹(ℝ)` and `v ∈ W^{1,p}(ℝ)`, `1 ≤ p ≤ ∞`,
the convolution `ρ ⋆ v'` is the weak derivative of `ρ ⋆ v` on `ℝ`. This is the one-dimensional
case of Lemma 9.1, `HasWeakIteratedLineDerivOn.convolution_of_integrable`, proved by Fubini's
theorem rather than by the book's approximation of `ρ` by continuous compactly supported
kernels. -/
theorem hasWeakDerivOn_convolution (v : SobolevIntervalLp 1 p ⊤) {ρ : ℝ → ℝ}
    (hρ : Integrable ρ) :
    HasWeakDerivOn (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] fn v)
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] deriv v 1) ⊤ :=
  (hasWeakDerivOn_fn v).convolution_of_integrable hρ Fact.out
    (memLp_restrict_top_iff.1 (memLp_deriv v 0)) (memLp_restrict_top_iff.1 (memLp_deriv v 1))

/-- **Lemma 8.4 of [brezis2011functional], membership form**: for `ρ ∈ L¹(ℝ)` and
`v ∈ W^{1,p}(ℝ)`, `1 ≤ p ≤ ∞`, the convolution `ρ ⋆ v` lies in `W^{1,p}(ℝ)`; its function and
weak derivative `ρ ⋆ v'` lie in `L^p(ℝ)` by Young's inequality. -/
theorem memSobolevIntervalLp_convolution (v : SobolevIntervalLp 1 p ⊤) {ρ : ℝ → ℝ}
    (hρ : Integrable ρ) :
    MemSobolevIntervalLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] fn v) 1 p ⊤ :=
  memSobolevIntervalLp_iff_memSobolev.2 ((memSobolev_fn v).convolution_of_integrable hρ Fact.out)

end SobolevIntervalLp

end
