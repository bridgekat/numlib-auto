/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.UniformSpace.Ascoli
import Numlib.Analysis.Sobolev.Interval.Density
import Numlib.Analysis.Sobolev.Interval.Zero
import Numlib.MeasureTheory.Function.LpSpace.KolmogorovRiesz

/-!
# `W^{1,p}(I)` by duality and by difference quotients

The characterizations of `W^{1,p}(I)`, `1 < p ≤ ∞`, that rest on the duality of the `L^p`
spaces, [brezis2011functional] §8.2–8.3: Proposition 8.3 (`u ∈ W^{1,p}(I)` iff
`|∫_I u φ'| ≤ C ‖φ‖_{p'}` on the test functions), Proposition 8.5 (on `ℝ`, `u ∈ W^{1,p}(ℝ)` iff
`‖τ_h u − u‖_p ≤ C |h|`), Remark 16 (ii) (`W_0^{1,p}(I)` by testing against `C_c^1(ℝ)`), the
weak compactness of bounded sets of `W^{1,p}(I)` of Remark 10 and Exercise 8.2, and the compact
embedding `W^{1,1}(I) ↪ L^q(I)` of Theorem 8.8 (7), which rests on the Kolmogorov–M. Riesz–Fréchet
theorem.

## Main statements

* `SobolevIntervalLp.abs_integral_mul_deriv_le` (**Proposition 8.3, (i) ⇒ (ii)**, with the
  constant `‖u'‖_p`, every `1 ≤ p ≤ ∞`) and
  `memSobolevIntervalLp_of_forall_abs_integral_mul_deriv_le` (**(ii) ⇒ (i)**, `1 < p ≤ ∞`, with
  the bound `‖u'‖_p ≤ C` on the weak derivative);
  `memSobolevIntervalLp_iff_forall_abs_integral_mul_deriv_le` is the equivalence.
* `MeasureTheory.eLpNorm_le_of_forall_abs_integral_testFunction_mul_le`: the `L^p(I)` norm of a
  function is computed by pairing with the test functions, `1 < p ≤ ∞` — the dual
  characterization behind the bound of (ii) ⇒ (i).
* `memSobolevIntervalLp_of_eLpNorm_translate_sub_le` (**Proposition 8.5, (ii) ⇒ (i)**):
  `‖τ_h u − u‖_p ≤ C |h|` for all `h` puts `u ∈ L^p(ℝ)` into `W^{1,p}(ℝ)`, `1 < p ≤ ∞`, with
  `‖u'‖_p ≤ C`; the converse with the constant `‖u'‖_p` is
  `SobolevIntervalLp.eLpNorm_translate_sub_le` of `Numlib/Analysis/Sobolev/Interval/Basic.lean`.
* `mem_sobolevIntervalLpZero_iff_forall_abs_integral_le` (**Remark 16 (ii)**): for `1 < p < ∞`,
  `u ∈ L^p(I)` is (the function of) an element of `W_0^{1,p}(I)` iff `|∫_I u φ'| ≤ C ‖φ‖_{L^q(I)}`
  for all test functions `φ` on `ℝ`.
* `SobolevIntervalLp.exists_subseq_tendsto_rep_of_bounded` (**Remark 10 (d), Exercise 8.2**):
  a bounded sequence of `W^{1,p}(I)`, `1 < p ≤ ∞`, has a subsequence whose continuous
  representatives converge uniformly on every bounded part of `Ī` to the representative of an
  element `v ∈ W^{1,p}(I)`, and whose derivatives converge to `v'` weakly in `L^p(I)`
  (weakly-∗ when `p = ∞`).
* `SobolevIntervalLp.isCompactOperator_toLp_one` (**Theorem 8.8 (7)**): the inclusion
  `W^{1,1}(a, b) ↪ L^q(a, b)` is compact for every `1 ≤ q < ∞`.
* `SobolevIntervalLp.memSobolevIntervalLp_of_tendsto_of_bounded_deriv` (**Remark 4, second
  clause**): an `L^p` limit of elements of `W^{1,p}(I)` with bounded derivatives lies in
  `W^{1,p}(I)`, `1 < p ≤ ∞`.

## Route

Propositions 8.3 and 8.5 are the one-dimensional instances of Proposition 9.3 of
[brezis2011functional], proved in `Numlib/Analysis/Sobolev/Friedrichs.lean` on any open subset of
a finite-dimensional space (`HasWeakFDerivOn.abs_integral_smul_fderiv_le`,
`HasWeakFDerivOn.of_forall_abs_integral_smul_fderiv_le`,
`abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le`), read on `E = ℝ` through the bridge
of `Numlib/Analysis/Sobolev/Interval/Density.lean`; the bound on the weak derivative is recovered
afterwards from the pairing with the test functions, which computes the `L^p` norm because the
test functions are dense in `L^q(I)`, `q < ∞` (`MeasureTheory.Lp.dense_contDiff_tsupport_subset`)
and the pairing is isometric (`MeasureTheory.Lp.norm_toDualCLM_apply`).

The weak compactness statement does not extract subsequences window by window: the derivatives
have a weakly-∗ convergent subsequence in `L^p(I) = (L^q(I))^*` by the sequential Banach–Alaoglu
theorem (`WeakDual.isSeqCompact_closedBall`, `L^q(I)` being separable), the values at one base
point of `I` have a convergent subsequence, and the representatives
`ũ_n(x) = ũ_n(y₀) + ∫_{y₀}^x u_n'` then converge at every point of `Ī`; their uniform Hölder
bound makes the convergence uniform on compact parts (`Equicontinuous.tendsto_uniformFun_iff_pi`),
and Fatou's lemma puts the limit into `L^p(I)`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Topology

noncomputable section

/-! ### Proposition 8.3 -/

section Duality

variable {I : Opens ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Proposition 8.3, (i) ⇒ (ii), with the constant `‖u'‖_p`** ([brezis2011functional], valid
for every `1 ≤ p ≤ ∞`, Remark 8): for `u ∈ W^{1,p}(I)`, `q` the conjugate exponent and every
test function `φ` on `I`, `|∫_I u φ'| ≤ ‖u'‖_p ‖φ‖_q`. The integration by parts formula and
Hölder's inequality, through the general `HasWeakFDerivOn.abs_integral_smul_fderiv_le`. -/
theorem SobolevIntervalLp.abs_integral_mul_deriv_le [ENNReal.HolderConjugate p q]
    (u : SobolevIntervalLp 1 p I) (φ : 𝓓(I, ℝ)) :
    |∫ x in (I : Set ℝ), SobolevIntervalLp.fn u x * _root_.deriv φ x|
      ≤ ‖SobolevIntervalLp.deriv u 1‖ * (eLpNorm φ q (volume.restrict I)).toReal := by
  have h := (SobolevIntervalLp.hasWeakDerivOn_fn u).hasWeakFDerivOn.abs_integral_smul_fderiv_le
    (p := p) (q := q) φ 1
  have e1 : ∀ x, fderiv ℝ φ x 1 • SobolevIntervalLp.fn u x
      = SobolevIntervalLp.fn u x * _root_.deriv φ x := fun x ↦ by
    rw [fderiv_apply_one_eq_deriv, smul_eq_mul, mul_comm]
  have e2 : eLpNorm (fun x ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (SobolevIntervalLp.deriv u 1 x)) p (volume.restrict (I : Set ℝ))
      = ‖SobolevIntervalLp.deriv u 1‖ₑ := by
    rw [Lp.enorm_def]
    exact eLpNorm_congr_norm_ae ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous
      |>.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)) (Lp.aestronglyMeasurable _)
      (Eventually.of_forall fun x ↦ ContinuousLinearMap.norm_toSpanSingleton _)
  simp only [e1, e2, enorm_one, one_mul] at h
  have hfin : ‖SobolevIntervalLp.deriv u 1‖ₑ * eLpNorm φ q (volume.restrict (I : Set ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top (φ.memLp' q).eLpNorm_ne_top
  have := ENNReal.toReal_mono hfin h
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    toReal_enorm] at this

/-- **The `L^p(I)` norm is computed by pairing with the test functions**, `1 < p ≤ ∞`: if
`w ∈ L^p(I)` and `|∫_I φ w| ≤ C ‖φ‖_q` for every test function `φ` on `I`, `q` the conjugate
exponent, then `‖w‖_p ≤ C`. The pairing `f ↦ ∫ w f` is a functional on `L^q(I)` of norm `‖w‖_p`
(`MeasureTheory.Lp.norm_toDualCLM_apply`), and its bound on the dense subspace of test functions
(`MeasureTheory.Lp.dense_contDiff_tsupport_subset`, `q < ∞`) is a bound on all of `L^q(I)`. -/
theorem MeasureTheory.eLpNorm_le_of_forall_abs_integral_testFunction_mul_le
    [ENNReal.HolderConjugate p q] (hq : q ≠ ⊤) {w : ℝ → ℝ} (hw : MemLp w p (volume.restrict I))
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : 𝓓(I, ℝ), |∫ x in (I : Set ℝ), φ x * w x|
      ≤ C * (eLpNorm φ q (volume.restrict I)).toReal) :
    eLpNorm w p (volume.restrict I) ≤ ENNReal.ofReal C := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨W, hW⟩ : ∃ W : Lp ℝ p (volume.restrict (I : Set ℝ)), W = hw.toLp w := ⟨_, rfl⟩
  have hWw : ⇑W =ᵐ[volume.restrict (I : Set ℝ)] w := by rw [hW]; exact hw.coeFn_toLp
  have key : ‖W‖ ≤ C := by
    rw [← Lp.norm_toDualCLM_apply (𝕜 := ℝ) (p := q) W]
    refine ContinuousLinearMap.opNorm_le_bound _ hC fun f ↦ ?_
    have hcl : IsClosed {f : Lp ℝ q (volume.restrict (I : Set ℝ)) |
        ‖Lp.toDualCLM ℝ q p (volume.restrict (I : Set ℝ)) W f‖ ≤ C * ‖f‖} :=
      isClosed_le ((Lp.toDualCLM ℝ q p _ W).continuous.norm) (continuous_const.mul continuous_norm)
    refine hcl.closure_subset_iff.2 ?_ (Lp.dense_contDiff_tsupport_subset I.isOpen hq f)
    rintro f ⟨g, hfg, hgc, hgs, hgI⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(I, ℝ), (φ : ℝ → ℝ) = g := ⟨⟨g, hgs, hgc, hgI⟩, rfl⟩
    have e1 : Lp.toDualCLM ℝ q p (volume.restrict (I : Set ℝ)) W f
        = ∫ x in (I : Set ℝ), φ x * w x := by
      rw [Lp.toDualCLM_apply, hφ]
      refine integral_congr_ae ?_
      filter_upwards [hWw, hfg] with x hx1 hx2
      rw [hx1, hx2, mul_comm]
    have e2 : ‖f‖ = (eLpNorm φ q (volume.restrict I)).toReal := by
      rw [Lp.norm_def, hφ, eLpNorm_congr_ae hfg]
    change ‖Lp.toDualCLM ℝ q p (volume.restrict (I : Set ℝ)) W f‖ ≤ C * ‖f‖
    rw [e1, e2, Real.norm_eq_abs]
    exact h φ
  rw [← ENNReal.ofReal_toReal hw.eLpNorm_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Lp.norm_toLp w hw, ← hW]
  exact key

/-- **Proposition 8.3, (ii) ⇒ (i)** ([brezis2011functional]): for `1 < p ≤ ∞`, `q` the conjugate
exponent, `u ∈ L^p(I)` and a constant `C` with `|∫_I u φ'| ≤ C ‖φ‖_q` for every test function
`φ` on `I`, `u` lies in `W^{1,p}(I)` and its weak derivative satisfies `‖u'‖_p ≤ C`. The
membership is the one-dimensional case of `HasWeakFDerivOn.of_forall_abs_integral_smul_fderiv_le`
(Hahn–Banach and the Riesz representation theorem); the bound is
`MeasureTheory.eLpNorm_le_of_forall_abs_integral_testFunction_mul_le`. -/
theorem memSobolevIntervalLp_of_forall_abs_integral_mul_deriv_le [ENNReal.HolderConjugate p q]
    (hq : q ≠ ⊤) {u : ℝ → ℝ} (hu : MemLp u p (volume.restrict I)) {C : ℝ}
    (h : ∀ φ : 𝓓(I, ℝ), |∫ x in (I : Set ℝ), u x * deriv φ x|
      ≤ C * (eLpNorm φ q (volume.restrict I)).toReal) :
    MemSobolevIntervalLp u 1 p I ∧ ∃ w : ℝ → ℝ, HasWeakDerivOn u w I ∧
      eLpNorm w p (volume.restrict I) ≤ ENNReal.ofReal C := by
  -- the constant may be taken nonnegative
  have hC' : ∀ φ : 𝓓(I, ℝ), |∫ x in (I : Set ℝ), u x * deriv φ x|
      ≤ max C 0 * (eLpNorm φ q (volume.restrict I)).toReal := fun φ ↦
    (h φ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
  have hCeq : ENNReal.ofReal (max C 0) = ENNReal.ofReal C := by
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  suffices key : ∀ C : ℝ, 0 ≤ C → (∀ φ : 𝓓(I, ℝ), |∫ x in (I : Set ℝ), u x * deriv φ x|
      ≤ C * (eLpNorm φ q (volume.restrict I)).toReal) →
      MemSobolevIntervalLp u 1 p I ∧ ∃ w : ℝ → ℝ, HasWeakDerivOn u w I ∧
        eLpNorm w p (volume.restrict I) ≤ ENNReal.ofReal C by
    rw [← hCeq]
    exact key _ (le_max_right _ _) hC'
  clear h hC' hCeq C
  intro C hC0 h
  have hmem : MemSobolev u 1 p I volume := by
    refine HasWeakFDerivOn.of_forall_abs_integral_smul_fderiv_le hq hu (C := ENNReal.ofReal C)
      ENNReal.ofReal_ne_top fun φ y ↦ ?_
    have e1 : ∀ x, fderiv ℝ φ x y • u x = y * (u x * deriv φ x) := fun x ↦ by
      rw [fderiv_eq_smul_deriv, smul_eq_mul, smul_eq_mul]; ring
    simp only [e1, integral_const_mul, enorm_mul]
    rw [mul_comm (ENNReal.ofReal C), mul_assoc]
    refine mul_le_mul' le_rfl ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_toReal (φ.memLp' q).eLpNorm_ne_top,
      ← ENNReal.ofReal_mul hC0]
    exact ENNReal.ofReal_le_ofReal (h φ)
  have hmem' : MemSobolevIntervalLp u 1 p I := memSobolevIntervalLp_iff_memSobolev.2 hmem
  obtain ⟨-, w, hw, hwp⟩ := memSobolevIntervalLp_one_iff.1 hmem'
  refine ⟨hmem', w, hw, ?_⟩
  refine eLpNorm_le_of_forall_abs_integral_testFunction_mul_le hq hwp hC0 fun φ ↦ ?_
  rw [← neg_neg (∫ x in (I : Set ℝ), φ x * w x), ← hw.integral_deriv_mul φ, abs_neg]
  refine le_trans (le_of_eq ?_) (h φ)
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

/-- **Proposition 8.3** ([brezis2011functional]), as an equivalence: for `1 < p ≤ ∞`, `q` the
conjugate exponent and `u ∈ L^p(I)`, `u ∈ W^{1,p}(I)` if and only if there is a constant `C` with
`|∫_I u φ'| ≤ C ‖φ‖_q` for every test function `φ` on `I`. -/
theorem memSobolevIntervalLp_iff_forall_abs_integral_mul_deriv_le [ENNReal.HolderConjugate p q]
    (hq : q ≠ ⊤) {u : ℝ → ℝ} (hu : MemLp u p (volume.restrict I)) :
    MemSobolevIntervalLp u 1 p I ↔ ∃ C : ℝ, ∀ φ : 𝓓(I, ℝ),
      |∫ x in (I : Set ℝ), u x * deriv φ x| ≤ C * (eLpNorm φ q (volume.restrict I)).toReal := by
  refine ⟨fun h ↦ ?_, fun ⟨C, hC⟩ ↦
    (memSobolevIntervalLp_of_forall_abs_integral_mul_deriv_le hq hu hC).1⟩
  obtain ⟨v, hv⟩ := h.exists_sobolevIntervalLp
  refine ⟨‖SobolevIntervalLp.deriv v 1‖, fun φ ↦ ?_⟩
  refine le_of_eq_of_le ?_ (SobolevIntervalLp.abs_integral_mul_deriv_le v φ)
  congr 1
  refine integral_congr_ae (hv.mono fun x hx ↦ ?_)
  simp only [hx]

end Duality

/-! ### Proposition 8.5: difference quotients on the line -/

section Translate

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Proposition 8.5, (ii) ⇒ (i)** ([brezis2011functional]): for `1 < p ≤ ∞`, `q` the conjugate
exponent, `u ∈ L^p(ℝ)` and a constant `C` with `‖τ_h u − u‖_p ≤ C |h|` for every `h`, `u` lies
in `W^{1,p}(ℝ)` and its weak derivative satisfies `‖u'‖_p ≤ C`. The translation estimate gives
the bound `|∫ u φ'| ≤ C ‖φ‖_q` of Proposition 8.3 (ii) by the difference-quotient argument of
`abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le` (Proposition 9.3, (iii) ⇒ (ii)),
and Proposition 8.3 concludes. The converse, with the constant `C = ‖u'‖_p`, is
`SobolevIntervalLp.eLpNorm_translate_sub_le`. -/
theorem memSobolevIntervalLp_of_eLpNorm_translate_sub_le [ENNReal.HolderConjugate p q]
    (hq : q ≠ ⊤) {u : ℝ → ℝ} (hu : MemLp u p volume) {C : ℝ}
    (hτ : ∀ h : ℝ, eLpNorm (fun x ↦ u (x + h) - u x) p volume ≤ ENNReal.ofReal (C * |h|)) :
    MemSobolevIntervalLp u 1 p ⊤ ∧ ∃ w : ℝ → ℝ, HasWeakDerivOn u w ⊤ ∧
      eLpNorm w p volume ≤ ENNReal.ofReal C := by
  have hu' : MemLp u p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    SobolevIntervalLp.memLp_restrict_top_iff.2 hu
  have hCeq : ENNReal.ofReal (max C 0) = ENNReal.ofReal C := by
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  -- the translation estimate with a nonnegative constant, in the shape of Proposition 9.3 (iii)
  have hC' : ∀ h : ℝ, eLpNorm (fun x ↦ u (x + h) - u x) p volume
      ≤ ENNReal.ofReal (max C 0) * ‖h‖ₑ := fun h ↦ by
    refine (hτ h).trans ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have key := abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le (Ω := ⊤) (μ := volume)
    (q := q) hu' (C := ENNReal.ofReal (max C 0))
    fun V _ _ _ a _ ↦ (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC' a)
  -- the bound of Proposition 8.3 (ii)
  have hbound : ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ),
      |∫ x in ((⊤ : Opens ℝ) : Set ℝ), u x * deriv φ x|
        ≤ max C 0 * (eLpNorm φ q (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))).toReal := by
    intro φ
    have h1 := key φ 1
    have e1 : ∀ x, fderiv ℝ φ x 1 • u x = u x * deriv φ x := fun x ↦ by
      rw [fderiv_apply_one_eq_deriv, smul_eq_mul, mul_comm]
    simp only [e1, enorm_one, mul_one] at h1
    have hfin : ENNReal.ofReal (max C 0)
        * eLpNorm φ q (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.memLp' q).eLpNorm_ne_top
    have := ENNReal.toReal_mono hfin h1
    rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (le_max_right _ _)] at this
  obtain ⟨hmem, w, hw, hwp⟩ :=
    memSobolevIntervalLp_of_forall_abs_integral_mul_deriv_le (I := ⊤) hq hu' hbound
  refine ⟨hmem, w, hw, ?_⟩
  rw [Measure.restrict_coe_top, hCeq] at hwp
  exact hwp

end Translate

/-! ### Remark 16 (ii): `W_0^{1,p}(I)` by testing against `C_c^∞(ℝ)` -/

section Zero

variable {I : Opens ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integral over `ℝ` of a product with the zero extension of `f` off the open set `I` is
the integral over `I` of the product with `f`. -/
theorem MeasureTheory.integral_mul_indicator_eq_setIntegral (I : Opens ℝ) (g f : ℝ → ℝ) :
    ∫ x, g x * (I : Set ℝ).indicator f x = ∫ x in (I : Set ℝ), g x * f x := by
  rw [← integral_indicator I.isOpen.measurableSet]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ (I : Set ℝ)
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, mul_zero]

/-- **Remark 16 (ii) of [brezis2011functional], Chapter 8**: for `1 < p < ∞`, `q` the conjugate
exponent, an open interval `I` and `u ∈ L^p(I)`, `u` is (almost everywhere on `I`) the function
of an element of `W_0^{1,p}(I)` if and only if there is a constant `C` with
`|∫_I u φ'| ≤ C ‖φ‖_{L^q(I)}` for every test function `φ` on the whole line. Forwards, the zero
extension `ū` of `v ∈ W_0^{1,p}(I)` has the zero extension of `v'` as weak derivative on `ℝ`
(`SobolevIntervalLpZero.hasWeakDerivOn_indicator`, Remark 16 (i)), so `∫_I u φ' = −∫_I v' φ` and
Hölder's inequality bounds it; backwards, the bound is Proposition 8.3 (ii) for `ū` on `ℝ`
(`memSobolevIntervalLp_of_forall_abs_integral_mul_deriv_le`), so `ū ∈ W^{1,p}(ℝ)`, which is
Remark 16 (i) (`mem_sobolevIntervalLpZero_iff_indicator_mem`). -/
theorem mem_sobolevIntervalLpZero_iff_forall_abs_integral_le [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hI : (I : Set ℝ).OrdConnected) {u : ℝ → ℝ}
    (hu : MemLp u p (volume.restrict I)) :
    (∃ v ∈ SobolevIntervalLpZero 1 p I, SobolevIntervalLp.fn v =ᵐ[volume.restrict I] u) ↔
      ∃ C : ℝ, ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ), |∫ x in (I : Set ℝ), u x * deriv φ x|
        ≤ C * (eLpNorm φ q (volume.restrict I)).toReal := by
  constructor
  · rintro ⟨v, hv, hvu⟩
    refine ⟨‖SobolevIntervalLp.deriv v 1‖, fun φ ↦ ?_⟩
    have h1 := (SobolevIntervalLpZero.hasWeakDerivOn_indicator hv).integral_deriv_mul φ
    rw [Measure.restrict_coe_top, integral_mul_indicator_eq_setIntegral,
      integral_mul_indicator_eq_setIntegral] at h1
    have e1 : ∫ x in (I : Set ℝ), u x * deriv φ x
        = -∫ x in (I : Set ℝ), φ x * SobolevIntervalLp.deriv v 1 x := by
      rw [← h1]
      refine integral_congr_ae (hvu.mono fun x hx ↦ ?_)
      simp only [hx, mul_comm]
    rw [e1, abs_neg]
    have h2 := enorm_integral_smul_le_eLpNorm_mul_eLpNorm (ν := volume.restrict (I : Set ℝ))
      (a := fun x ↦ (φ : ℝ → ℝ) x) (h := fun x ↦ SobolevIntervalLp.deriv v 1 x) (p := q) (q := p)
    simp only [smul_eq_mul] at h2
    have hfin : eLpNorm (fun x ↦ (φ : ℝ → ℝ) x) q (volume.restrict (I : Set ℝ))
        * eLpNorm (fun x ↦ SobolevIntervalLp.deriv v 1 x) p (volume.restrict (I : Set ℝ)) ≠ ⊤ :=
      ENNReal.mul_ne_top ((φ.memLp q volume).restrict _).eLpNorm_ne_top
        (Lp.memLp _).eLpNorm_ne_top
    have := ENNReal.toReal_mono hfin h2
    rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
      mul_comm, ← Lp.norm_def] at this
  · rintro ⟨C, hC⟩
    have hC' : ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ), |∫ x in (I : Set ℝ), u x * deriv φ x|
        ≤ max C 0 * (eLpNorm φ q (volume.restrict I)).toReal := fun φ ↦
      (hC φ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
    -- the zero extension lies in `W^{1,p}(ℝ)`
    have hind : MemSobolevIntervalLp ((I : Set ℝ).indicator u) 1 p ⊤ := by
      have hu' : MemLp ((I : Set ℝ).indicator u) p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
        SobolevIntervalLp.memLp_restrict_top_iff.2
          ((memLp_indicator_iff_restrict I.isOpen.measurableSet).2 hu)
      refine (memSobolevIntervalLp_of_forall_abs_integral_mul_deriv_le (I := ⊤) hq hu'
        (C := max C 0) fun φ ↦ ?_).1
      rw [Measure.restrict_coe_top]
      have e1 : ∫ x, (I : Set ℝ).indicator u x * deriv φ x
          = ∫ x in (I : Set ℝ), u x * deriv φ x :=
        calc ∫ x, (I : Set ℝ).indicator u x * deriv φ x
            = ∫ x, deriv φ x * (I : Set ℝ).indicator u x :=
              integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
          _ = ∫ x in (I : Set ℝ), deriv φ x * u x := integral_mul_indicator_eq_setIntegral I _ _
          _ = ∫ x in (I : Set ℝ), u x * deriv φ x :=
              integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
      rw [e1]
      refine (hC' φ).trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
      exact ENNReal.toReal_mono (φ.memLp q volume).eLpNorm_ne_top
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
    -- restricted to `I`, it is `u`, the function of some `v ∈ W^{1,p}(I)`
    have hmem : MemSobolevIntervalLp u 1 p I :=
      (MemSobolevMultiIndex.mono_set hind (le_top : I ≤ ⊤)).congr_ae
        (indicator_ae_eq_restrict I.isOpen.measurableSet)
    obtain ⟨v, hv⟩ := hmem.exists_sobolevIntervalLp
    refine ⟨v, ?_, hv⟩
    rw [mem_sobolevIntervalLpZero_iff_indicator_mem hI hp]
    refine hind.congr_ae ?_
    rw [Measure.restrict_coe_top]
    have := (ae_restrict_iff' I.isOpen.measurableSet).1 hv
    filter_upwards [this] with x hx
    by_cases hxI : x ∈ (I : Set ℝ)
    · rw [indicator_of_mem hxI, indicator_of_mem hxI, hx hxI]
    · rw [indicator_of_notMem hxI, indicator_of_notMem hxI]

end Zero

/-! ### Theorem 8.8 (7): the compact embedding `W^{1,1}(a, b) ↪ L^q(a, b)` -/

section Compact

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The translates of an `L^p(ℝ)` function agree almost everywhere with the translates of any
almost everywhere equal function. -/
theorem MeasureTheory.translate_sub_ae_eq {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) (h : ℝ) :
    (fun x ↦ f (x + h) - f x) =ᵐ[volume] fun x ↦ g (x + h) - g x := by
  have := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [this, hfg] with x hx1 hx2
  simp only [Function.comp_apply] at hx1
  rw [hx1, hx2]

namespace SobolevIntervalLp

/-- **The translation estimate in `L^q` for `W^{1,1}(ℝ)`**, the inequality of the proof of
[brezis2011functional] Theorem 8.8 (7): for `U ∈ W^{1,1}(ℝ)` and `1 ≤ q < ∞`,
`‖τ_h U − U‖_q ≤ (|h| ‖U'‖_1)^{1/q} (2 ‖U‖_∞)^{1 − 1/q}`, from `‖τ_h U − U‖_1 ≤ |h| ‖U'‖_1`
(Proposition 8.5) and the interpolation `‖g‖_q ≤ ‖g‖_1^{1/q} ‖g‖_∞^{1 − 1/q}`. -/
theorem eLpNorm_translate_sub_le_rpow (hq : q ≠ ⊤) (U : SobolevIntervalLp 1 1 ⊤) (h : ℝ) :
    eLpNorm (fun x ↦ fn U (x + h) - fn U x) q volume
      ≤ (ENNReal.ofReal |h| * ‖deriv U 1‖ₑ) ^ q.toReal⁻¹
        * (2 * eLpNorm (fn U) ⊤ volume) ^ (1 - q.toReal⁻¹) := by
  have hrep : fn U =ᵐ[volume] rep U :=
    eventuallyEq_restrict_top_iff.1 (fn_ae_eq_rep Opens.ordConnected_top U)
  have hUm : AEStronglyMeasurable (fn U) volume :=
    (memLp_restrict_top_iff.1 (memLp_deriv U 0)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun x ↦ fn U (x + h) - fn U x) volume :=
    (hUm.comp_measurePreserving (measurePreserving_add_right volume h)).sub hUm
  have h1 : eLpNorm (fun x ↦ fn U (x + h) - fn U x) 1 volume
      ≤ ENNReal.ofReal |h| * ‖deriv U 1‖ₑ := by
    rw [eLpNorm_congr_ae (translate_sub_ae_eq hrep h), Lp.enorm_def, eLpNorm_restrict_coe_top]
    exact eLpNorm_translate_sub_le U h
  have htop : eLpNorm (fun x ↦ fn U (x + h) - fn U x) ⊤ volume
      ≤ 2 * eLpNorm (fn U) ⊤ volume := by
    refine (eLpNorm_sub_le le_top).trans ?_
    rw [two_mul]
    refine add_le_add (le_of_eq ?_) le_rfl
    exact eLpNorm_comp_measurePreserving hUm (measurePreserving_add_right volume h)
  have hqi : 0 ≤ 1 - q.toReal⁻¹ := one_sub_toReal_inv_nonneg Fact.out
  refine (eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_top_rpow hmeas one_ne_zero Fact.out hq).trans ?_
  rw [ENNReal.toReal_one, one_div]
  gcongr

variable {a b : ℝ}

/-- **Theorem 8.8 (7) of [brezis2011functional]**: for `a < b` and `1 ≤ q < ∞`, the inclusion
`W^{1,1}(a, b) ↪ L^q(a, b)` is a compact operator. The extensions `P u`, `u` in the unit ball,
form a family bounded in `L^1(ℝ) ∩ L^∞(ℝ)`, hence in `L^q(ℝ)`, whose translates are uniformly
continuous in `L^q` by `SobolevIntervalLp.eLpNorm_translate_sub_le_rpow`; the
Kolmogorov–M. Riesz–Fréchet theorem
(`MeasureTheory.Lp.isCompact_closure_image_restrictCLM_of_uniform_translate`) makes its
restriction to `(a, b)`, which is the image of the unit ball, relatively compact in `L^q(a, b)`.
Compactness in the vocabulary of `IsCompactEmbedding` is
`SobolevIntervalLp.isCompactEmbedding_toLp_one`. -/
theorem isCompactOperator_toLp_one (hab : a < b) (hq : q ≠ ⊤) :
    IsCompactOperator (toLpOfBounded 1 hab q :
      SobolevIntervalLp 1 1 (Opens.Ioo a b) →L[ℝ] Lp ℝ q (volume.restrict (Ioo a b))) := by
  have hI := ordConnected_coe_Ioo a b
  have hne : ((Opens.Ioo a b : Opens ℝ) : Set ℝ).Nonempty := by
    rw [Opens.coe_Ioo]; exact nonempty_Ioo.2 hab
  obtain ⟨P, hP⟩ : ∃ P : SobolevIntervalLp 1 1 (Opens.Ioo a b) →L[ℝ] SobolevIntervalLp 1 1 ⊤,
      P = extensionCLM hI hne := ⟨_, rfl⟩
  have hPfn : ∀ u, fn (P u) =ᵐ[volume.restrict (Ioo a b)] fn u := by
    intro u; rw [hP]; exact fn_extensionCLM hI hne u
  obtain ⟨K, hK0, hPle⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ u, ‖P u‖ ≤ K * ‖u‖ :=
    ⟨‖P‖, norm_nonneg _, fun u ↦ P.le_opNorm u⟩
  obtain ⟨C₀, hC₀, hC₀def⟩ : ∃ C₀ : ℝ, 0 < C₀ ∧ C₀ = embeddingConst 1 ⊤ :=
    ⟨_, embeddingConst_pos _ _, rfl⟩
  -- the extensions lie in `L^1 ∩ L^∞`, hence in `L^q`
  have h1 : ∀ u, MemLp (fn (P u)) 1 volume := fun u ↦
    memLp_restrict_top_iff.1 (memLp_deriv (P u) 0)
  have h1' : ∀ u, eLpNorm (fn (P u)) 1 volume ≤ ENNReal.ofReal (K * ‖u‖) := fun u ↦ by
    have e0 : eLpNorm (fn (P u)) 1 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        = ‖deriv (P u) 0‖ₑ := by rw [Lp.enorm_def]; rfl
    rw [← eLpNorm_restrict_coe_top (fn (P u)) 1, e0, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((norm_deriv_le _ 0).trans (hPle u))
  have htop : ∀ u, eLpNorm (fn (P u)) ⊤ volume ≤ ENNReal.ofReal (C₀ * (K * ‖u‖)) := fun u ↦ by
    refine ((eLpNorm_restrict_coe_top (fn (P u)) ⊤).symm.trans_le
      (eLpNorm_top_le Opens.ordConnected_top (P u))).trans ?_
    rw [← hC₀def]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hPle u) hC₀.le)
  have htop' : ∀ u, MemLp (fn (P u)) ⊤ volume := fun u ↦
    memLp_iff.2 ((htop u).trans_lt ENNReal.ofReal_lt_top)
  have hq' : ∀ u, MemLp (fn (P u)) q volume := fun u ↦
    (h1 u).of_le_of_memLp_top one_ne_zero Fact.out (htop' u)
  -- the family
  obtain ⟨T, hT⟩ : ∃ T : SobolevIntervalLp 1 1 (Opens.Ioo a b) → Lp ℝ q volume,
      T = fun u ↦ (hq' u).toLp (fn (P u)) := ⟨_, rfl⟩
  have hTfn : ∀ u, ⇑(T u) =ᵐ[volume] fn (P u) := fun u ↦ by rw [hT]; exact (hq' u).coeFn_toLp
  have hqr : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq
  have hqi : 0 ≤ 1 - q.toReal⁻¹ := one_sub_toReal_inv_nonneg Fact.out
  -- the image of the unit ball under the inclusion is the restriction of the family
  have himage : (toLpOfBounded 1 hab q : SobolevIntervalLp 1 1 (Opens.Ioo a b) →ₗ[ℝ]
      Lp ℝ q (volume.restrict (Ioo a b))) '' Metric.closedBall 0 1
      = Lp.restrictCLM ℝ ℝ q volume (Ioo a b) '' (T '' Metric.closedBall 0 1) := by
    rw [image_image]
    refine image_congr fun u _ ↦ ?_
    refine (Lp.ext ?_).symm
    have e1 : ⇑(Lp.restrictCLM ℝ ℝ q volume (Ioo a b) (T u)) =ᵐ[volume.restrict (Ioo a b)] T u :=
      Lp.coeFn_restrictCLM _ _
    have e2 : ⇑(T u) =ᵐ[volume.restrict (Ioo a b)] fn (P u) := ae_restrict_of_ae (hTfn u)
    exact e1.trans (e2.trans ((hPfn u).trans (coeFn_toLpOfBounded hab q u).symm))
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (toLpOfBounded 1 hab q : SobolevIntervalLp 1 1 (Opens.Ioo a b) →ₗ[ℝ]
      Lp ℝ q (volume.restrict (Ioo a b))) one_pos).2 ?_
  rw [himage]
  refine Lp.isCompact_closure_image_restrictCLM_of_uniform_translate hq ?_ ?_ ?_
  · -- the family is bounded in `L^q(ℝ)`
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(ENNReal.ofReal (K * 1) ^ q.toReal⁻¹
      * ENNReal.ofReal (C₀ * (K * 1)) ^ (1 - q.toReal⁻¹)).toReal, ?_⟩
    rintro f ⟨u, hu, rfl⟩
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    rw [hT, Lp.norm_toLp]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hqi ENNReal.ofReal_ne_top)) ?_
    refine (eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_top_rpow (h1 u).aestronglyMeasurable one_ne_zero
      Fact.out hq).trans ?_
    rw [ENNReal.toReal_one, one_div]
    have e1 : eLpNorm (fn (P u)) 1 volume ≤ ENNReal.ofReal (K * 1) :=
      (h1' u).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hu1 hK0))
    have e2 : eLpNorm (fn (P u)) ⊤ volume ≤ ENNReal.ofReal (C₀ * (K * 1)) :=
      (htop u).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu1 hK0) hC₀.le))
    gcongr
  · -- the translates are uniformly continuous in `L^q(ℝ)`
    intro ε hε
    obtain ⟨B, hBdef⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal K ^ q.toReal⁻¹
      * (2 * ENNReal.ofReal (C₀ * (K * 1))) ^ (1 - q.toReal⁻¹) := ⟨_, rfl⟩
    have hB : B ≠ ⊤ := by
      rw [hBdef]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg hqi (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
          ENNReal.ofReal_ne_top))
    have hlim : Tendsto (fun h : ℝ ↦ ENNReal.ofReal |h| ^ q.toReal⁻¹ * B) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto (fun h : ℝ ↦ ENNReal.ofReal |h|) (𝓝 0) (𝓝 0) := by
        have := ENNReal.tendsto_ofReal (continuous_abs.tendsto (0 : ℝ))
        simpa using this
      have h2 : Tendsto (fun h : ℝ ↦ ENNReal.ofReal |h| ^ q.toReal⁻¹) (𝓝 0) (𝓝 0) := by
        have := ((ENNReal.continuous_rpow_const (y := q.toReal⁻¹)).tendsto 0).comp h1
        rwa [ENNReal.zero_rpow_of_pos (by positivity)] at this
      simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hB)
    obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 ((tendsto_order.1 hlim).2 ε hε)
    refine ⟨δ, hδ, ?_⟩
    rintro f ⟨u, hu, rfl⟩ h hh
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    have hK1 : ‖deriv (P u) 1‖ₑ ≤ ENNReal.ofReal K := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((norm_deriv_le _ 1).trans ((hPle u).trans
        (by nlinarith)))
    have e2 : eLpNorm (fn (P u)) ⊤ volume ≤ ENNReal.ofReal (C₀ * (K * 1)) :=
      (htop u).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu1 hK0) hC₀.le))
    calc eLpNorm (fun x ↦ (T u) (x + h) - (T u) x) q volume
        = eLpNorm (fun x ↦ fn (P u) (x + h) - fn (P u) x) q volume :=
          eLpNorm_congr_ae (translate_sub_ae_eq (hTfn u) h)
      _ ≤ (ENNReal.ofReal |h| * ‖deriv (P u) 1‖ₑ) ^ q.toReal⁻¹
          * (2 * eLpNorm (fn (P u)) ⊤ volume) ^ (1 - q.toReal⁻¹) :=
          eLpNorm_translate_sub_le_rpow hq (P u) h
      _ ≤ (ENNReal.ofReal |h| * ENNReal.ofReal K) ^ q.toReal⁻¹
          * (2 * ENNReal.ofReal (C₀ * (K * 1))) ^ (1 - q.toReal⁻¹) := by gcongr
      _ = ENNReal.ofReal |h| ^ q.toReal⁻¹ * B := by
          rw [hBdef, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), mul_assoc]
      _ < ε := hδε (by rw [Real.dist_eq, sub_zero]; exact hh)
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

/-- **Theorem 8.8 (7) of [brezis2011functional]**, in the vocabulary of
`Numlib/Analysis/Normed/Operator/Embedding.lean`: for `a < b` and `1 ≤ q < ∞`,
`W^{1,1}(a, b) ↪ L^q(a, b)` is a compact embedding. -/
theorem isCompactEmbedding_toLp_one (hab : a < b) (hq : q ≠ ⊤) :
    IsCompactEmbedding (toLpOfBounded 1 hab q :
      SobolevIntervalLp 1 1 (Opens.Ioo a b) →ₗ[ℝ] Lp ℝ q (volume.restrict (Ioo a b))) := by
  refine isCompactEmbedding_iff_isCompactOperator.2 ⟨fun u v huv ↦ eq_of_fn_ae_eq ?_,
    isCompactOperator_toLp_one hab hq⟩
  have h1 := coeFn_toLpOfBounded hab q u
  have h2 := coeFn_toLpOfBounded hab q v
  have huv' : toLpOfBounded 1 hab q u = toLpOfBounded 1 hab q v := huv
  rw [huv'] at h1
  exact h1.symm.trans h2

end SobolevIntervalLp

end Compact

/-! ### Weak-∗ sequential compactness in `L^p`, and uniform convergence from equicontinuity -/

section WeakStar

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}

/-- **Weak-∗ sequential compactness of bounded sets of `L^p`**, `1 < p ≤ ∞`: on a σ-finite
measure with `L^q` separable, `q < ∞` the conjugate exponent, a sequence `w n ∈ L^p` with
`‖w n‖ ≤ M` has a subsequence `w (φ n)` and a limit `w₀ ∈ L^p`, `‖w₀‖ ≤ M`, with
`∫ w (φ n) f → ∫ w₀ f` for every `f ∈ L^q`. This is the sequential Banach–Alaoglu theorem
`WeakDual.isSeqCompact_closedBall` read through the identification `L^p = (L^q)^*`
(`MeasureTheory.Lp.dualEquiv`); for `p < ∞` it is weak convergence, for `p = ∞` weak-∗
convergence in `σ(L^∞, L^1)`. -/
theorem MeasureTheory.Lp.exists_subseq_forall_tendsto_integral_mul [SigmaFinite μ]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] (hq : q ≠ ⊤)
    [TopologicalSpace.SeparableSpace (Lp ℝ q μ)] {w : ℕ → Lp ℝ p μ} {M : ℝ}
    (hw : ∀ n, ‖w n‖ ≤ M) :
    ∃ (w₀ : Lp ℝ p μ) (φ : ℕ → ℕ), StrictMono φ ∧ ‖w₀‖ ≤ M ∧
      ∀ f : Lp ℝ q μ, Tendsto (fun n ↦ ∫ x, w (φ n) x * f x ∂μ) atTop
        (𝓝 (∫ x, w₀ x * f x ∂μ)) := by
  obtain ⟨e, he⟩ : ∃ e : Lp ℝ p μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ q μ), e = Lp.dualEquiv ℝ q p μ hq :=
    ⟨_, rfl⟩
  have he_apply : ∀ (u : Lp ℝ p μ) (f : Lp ℝ q μ), e u f = ∫ x, u x * f x ∂μ := by
    intro u f; rw [he]; exact Lp.dualEquiv_apply hq u f
  have hmem : ∀ n, StrongDual.toWeakDual (e (w n))
      ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (Lp ℝ q μ)) M := by
    intro n
    rw [mem_preimage, mem_closedBall_zero_iff, StrongDual.toStrongDual_toWeakDual,
      LinearIsometryEquiv.norm_map]
    exact hw n
  obtain ⟨Ψ, hΨ, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := Lp ℝ q μ) 0 M hmem
  refine ⟨e.symm (WeakDual.toStrongDual Ψ), φ, hφ, ?_, fun f ↦ ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.1 hΨ
  · have h : Tendsto (fun i ↦ e (w (φ i)) f) atTop (𝓝 (Ψ f)) :=
      (tendsto_iff_forall_eval_tendsto_topDualPairing.1 hlim) f
    simp only [he_apply] at h
    have e2 : Ψ f = ∫ x, e.symm (WeakDual.toStrongDual Ψ) x * f x ∂μ := by
      rw [← he_apply, LinearIsometryEquiv.apply_symm_apply]
      rfl
    rw [e2] at h
    exact h

end WeakStar

section Equicontinuous

variable {X : Type*} [TopologicalSpace X] {F : ℕ → X → ℝ} {f : X → ℝ}

/-- **Pointwise convergence of an equicontinuous sequence is uniform on compact sets.** -/
theorem tendstoUniformlyOn_of_equicontinuousOn_of_tendsto {K : Set X} (hK : IsCompact K)
    (heq : EquicontinuousOn F K) (hpt : ∀ x ∈ K, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop K := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have heq' : Equicontinuous fun n (x : K) ↦ F n x := (equicontinuous_restrict_iff _).2 heq
  have key := (Equicontinuous.tendsto_uniformFun_iff_pi heq' atTop fun x : K ↦ f x).2
    (tendsto_pi_nhds.2 fun x ↦ hpt x x.2)
  rw [UniformFun.tendsto_iff_tendstoUniformly] at key
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact key

end Equicontinuous

/-! ### Remark 10 (d), Exercise 8.2: weak compactness of bounded sets of `W^{1,p}(I)` -/

section Subseq

variable {I : Opens ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded interval `Ioc c d` with endpoints in the closure of the open interval `I` differs
from `Ioc c d ∩ I` by a null set. -/
theorem TopologicalSpace.Opens.Ioc_inter_ae_eq (hI : (I : Set ℝ).OrdConnected) {c d : ℝ}
    (hc : c ∈ closure (I : Set ℝ)) (hd : d ∈ closure (I : Set ℝ)) :
    Ioc c d ∩ (I : Set ℝ) =ᵐ[volume] Ioc c d := by
  have hsub : Ioc c d ⊆ closure (I : Set ℝ) :=
    Ioc_subset_Icc_self.trans
      (Icc_subset_uIcc.trans ((I.ordConnected_closure hI).uIcc_subset hc hd))
  have h2 : Ioc c d \ (Ioc c d ∩ (I : Set ℝ)) ⊆ closure (I : Set ℝ) \ I :=
    fun x hx ↦ ⟨hsub hx.1, fun hxI ↦ hx.2 ⟨hx.1, hxI⟩⟩
  rw [ae_eq_set, sdiff_eq_empty.2 inter_subset_left, measure_empty]
  exact ⟨rfl, measure_mono_null h2 (I.volume_closure_diff_eq_zero hI)⟩

/-- The integral of `v` over `Ioc c d`, for `c, d` in the closure of the open interval `I`, is
the pairing of `v` with the indicator of `Ioc c d` over `I`. -/
theorem MeasureTheory.setIntegral_Ioc_eq_setIntegral_mul_indicator (hI : (I : Set ℝ).OrdConnected)
    {c d : ℝ} (hc : c ∈ closure (I : Set ℝ)) (hd : d ∈ closure (I : Set ℝ)) (v : ℝ → ℝ) :
    ∫ t in Ioc c d, v t = ∫ t in (I : Set ℝ), v t * (Ioc c d).indicator (fun _ ↦ (1 : ℝ)) t := by
  calc ∫ t in Ioc c d, v t = ∫ t in Ioc c d ∩ (I : Set ℝ), v t :=
        (setIntegral_congr_set (I.Ioc_inter_ae_eq hI hc hd)).symm
    _ = ∫ t in (I : Set ℝ), (Ioc c d).indicator v t := by
        rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
    _ = ∫ t in (I : Set ℝ), v t * (Ioc c d).indicator (fun _ ↦ (1 : ℝ)) t := by
        refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
        by_cases ht : t ∈ Ioc c d
        · simp only [indicator_of_mem ht, mul_one]
        · simp only [indicator_of_notMem ht, mul_zero]

/-- The indicator of a bounded interval lies in every `L^q(I)`. -/
theorem MeasureTheory.memLp_indicator_Ioc_one (I : Opens ℝ) (q : ℝ≥0∞) (c d : ℝ) :
    MemLp ((Ioc c d).indicator fun _ ↦ (1 : ℝ)) q (volume.restrict (I : Set ℝ)) :=
  memLp_indicator_const q measurableSet_Ioc 1 (Or.inr
    ((Measure.restrict_apply_le _ _).trans_lt measure_Ioc_lt_top).ne)

namespace SobolevIntervalLp

/-- **Remark 10 (d) and Exercise 8.2 of [brezis2011functional]** (weak compactness of bounded
sets of `W^{1,p}(I)`): for `1 < p ≤ ∞`, `q` the conjugate exponent, an open interval `I` and a
sequence `u n ∈ W^{1,p}(I)` with `‖u n‖ ≤ M`, there are `v ∈ W^{1,p}(I)` and a subsequence
`u (φ n)` whose continuous representatives converge to `ũ = ṽ` uniformly on every bounded part
`Ī ∩ [-R, R]` of `Ī`, and whose derivatives converge to `v'` weakly in `L^p(I)` — weakly-∗ in
`σ(L^∞, L^1)` when `p = ∞` — in the sense that `∫_I u_n' f → ∫_I v' f` for every `f ∈ L^q(I)`.

The derivatives have a weakly-∗ convergent subsequence by the sequential Banach–Alaoglu theorem
(`MeasureTheory.Lp.exists_subseq_forall_tendsto_integral_mul`), the values `ũ_n(y₀)` at a base
point a convergent one, so `ũ_n(x) = ũ_n(y₀) + ∫_{y₀}^x u_n'` converges at every `x ∈ Ī` to
`G(x) = L + ∫_{y₀}^x w₀`; the representatives are uniformly Hölder continuous
(`SobolevIntervalLp.abs_rep_sub_rep_le`), so the convergence is uniform on compact parts of `Ī`
(`tendstoUniformlyOn_of_equicontinuousOn_of_tendsto`); `G ∈ L^p(I)` by Fatou's lemma, and
`w₀` is its weak derivative (Lemma 8.2), so `G` is the representative of an element `v`. -/
theorem exists_subseq_tendsto_rep_of_bounded (hI : (I : Set ℝ).OrdConnected)
    [ENNReal.HolderConjugate p q] (hq : q ≠ ⊤) {u : ℕ → SobolevIntervalLp 1 p I} {M : ℝ}
    (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ (v : SobolevIntervalLp 1 p I) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ R : ℝ, TendstoUniformlyOn (fun n ↦ rep (u (φ n))) (rep v) atTop
        (closure (I : Set ℝ) ∩ Icc (-R) R)) ∧
      ∀ f : Lp ℝ q (volume.restrict (I : Set ℝ)),
        Tendsto (fun n ↦ ∫ x in (I : Set ℝ), deriv (u (φ n)) 1 x * f x) atTop
          (𝓝 (∫ x in (I : Set ℝ), deriv v 1 x * f x)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hq1 : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hqt : Fact (q ≠ ⊤) := ⟨hq⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- the empty interval
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · refine ⟨0, id, strictMono_id, fun R ↦ ?_, fun f ↦ ?_⟩
    · have hs : closure (I : Set ℝ) ∩ Icc (-R) R = ∅ := by
        rw [hI0, closure_empty, empty_inter]
      rw [hs]
      exact tendstoUniformlyOn_empty
    · have h0 : ∀ g : ℝ → ℝ, ∫ x in (I : Set ℝ), g x = 0 := fun g ↦
        setIntegral_measure_zero g (by rw [hI0, measure_empty])
      simp only [h0]
      exact tendsto_const_nhds
  obtain ⟨y₀, hy₀⟩ := hne
  have hy₀c : y₀ ∈ closure (I : Set ℝ) := subset_closure hy₀
  -- weak-∗ convergence of the derivatives along a subsequence
  obtain ⟨w₀, φ₁, hφ₁, -, hw₀⟩ := Lp.exists_subseq_forall_tendsto_integral_mul (p := p) (q := q)
    hq (w := fun n ↦ deriv (u n) 1) (M := M) fun n ↦ (norm_deriv_le (u n) 1).trans (hM n)
  -- convergence of the values at the base point along a further subsequence
  have hbdd : ∀ n, rep (u (φ₁ n)) y₀ ∈ Metric.closedBall (0 : ℝ) (embeddingConst p I * M) := by
    intro n
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact (abs_rep_le hI _ hy₀c).trans
      (mul_le_mul_of_nonneg_left (hM _) (embeddingConst_pos p I).le)
  obtain ⟨L, -, φ₂, hφ₂, hL⟩ := (isCompact_closedBall (0 : ℝ) _).tendsto_subseq hbdd
  have hL' : Tendsto (fun n ↦ rep (u (φ₁ (φ₂ n))) y₀) atTop (𝓝 L) := hL
  -- the pairing of the derivatives with functions of `L^q(I)`
  have hpair : ∀ g : ℝ → ℝ, MemLp g q (volume.restrict I) →
      Tendsto (fun n ↦ ∫ x in (I : Set ℝ), deriv (u (φ₁ (φ₂ n))) 1 x * g x) atTop
        (𝓝 (∫ x in (I : Set ℝ), w₀ x * g x)) := by
    intro g hg
    have h1 := (hw₀ (hg.toLp g)).comp hφ₂.tendsto_atTop
    have e : ∀ v : Lp ℝ p (volume.restrict (I : Set ℝ)),
        ∫ x in (I : Set ℝ), v x * (hg.toLp g) x = ∫ x in (I : Set ℝ), v x * g x := fun v ↦
      integral_congr_ae (hg.coeFn_toLp.mono fun x hx ↦ by simp only [hx])
    simp only [Function.comp_def, e] at h1
    exact h1
  -- the interval integrals of the derivatives converge
  have hint : ∀ x ∈ closure (I : Set ℝ),
      Tendsto (fun n ↦ ∫ t in y₀..x, deriv (u (φ₁ (φ₂ n))) 1 t) atTop
        (𝓝 (∫ t in y₀..x, w₀ t)) := by
    intro x hx
    rcases le_or_gt y₀ x with hle | hlt
    · have e : ∀ v : ℝ → ℝ, ∫ t in y₀..x, v t
          = ∫ t in (I : Set ℝ), v t * (Ioc y₀ x).indicator (fun _ ↦ (1 : ℝ)) t := fun v ↦ by
        rw [intervalIntegral.integral_of_le hle,
          setIntegral_Ioc_eq_setIntegral_mul_indicator hI hy₀c hx]
      simp only [e]
      exact hpair _ (memLp_indicator_Ioc_one I q y₀ x)
    · have e : ∀ v : ℝ → ℝ, ∫ t in y₀..x, v t
          = -∫ t in (I : Set ℝ), v t * (Ioc x y₀).indicator (fun _ ↦ (1 : ℝ)) t := fun v ↦ by
        rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hlt.le,
          setIntegral_Ioc_eq_setIntegral_mul_indicator hI hx hy₀c]
      simp only [e]
      exact (hpair _ (memLp_indicator_Ioc_one I q x y₀)).neg
  -- the limit function
  have hw₀mem : MemLp (⇑w₀) p (volume.restrict I) := Lp.memLp w₀
  set G : ℝ → ℝ := fun x ↦ L + ∫ t in y₀..x, w₀ t with hGdef
  have hGcont : ContinuousOn G (closure (I : Set ℝ)) :=
    continuousOn_integral_of_intervalIntegrable hy₀c
      (fun x hx y hy ↦ hw₀mem.intervalIntegrable_of_mem_closure hI hx hy) L
  have hpt : ∀ x ∈ closure (I : Set ℝ),
      Tendsto (fun n ↦ rep (u (φ₁ (φ₂ n))) x) atTop (𝓝 (G x)) := by
    intro x hx
    have e : ∀ n, rep (u (φ₁ (φ₂ n))) x
        = rep (u (φ₁ (φ₂ n))) y₀ + ∫ t in y₀..x, deriv (u (φ₁ (φ₂ n))) 1 t := fun n ↦ by
      have := rep_sub_rep hI (u (φ₁ (φ₂ n))) hy₀c hx
      linarith
    simp only [e]
    exact hL'.add (hint x hx)
  -- `G` lies in `L^p(I)` by Fatou's lemma
  have hGm : AEStronglyMeasurable G (volume.restrict (I : Set ℝ)) :=
    (hGcont.mono subset_closure).aestronglyMeasurable I.isOpen.measurableSet
  have hGmem : MemLp G p (volume.restrict I) := by
    refine memLp_iff.2 ?_
    have hlim : ∀ᵐ x ∂(volume.restrict (I : Set ℝ)),
        Tendsto (fun n ↦ fn (u (φ₁ (φ₂ n))) x) atTop (𝓝 (G x)) := by
      have hae : ∀ᵐ x ∂(volume.restrict (I : Set ℝ)), ∀ n,
          fn (u (φ₁ (φ₂ n))) x = rep (u (φ₁ (φ₂ n))) x :=
        ae_all_iff.2 fun n ↦ fn_ae_eq_rep hI _
      filter_upwards [hae, ae_restrict_mem I.isOpen.measurableSet] with x hx hxI
      exact (hpt x (subset_closure hxI)).congr fun n ↦ (hx n).symm
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n ↦ Lp.aestronglyMeasurable (deriv _ 0)) G hGm
      hlim).trans_lt ?_
    refine (liminf_le_of_frequently_le' (Frequently.of_forall fun n ↦ ?_)).trans_lt
      (ENNReal.ofReal_lt_top (r := M))
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((norm_deriv_le _ 0).trans (hM _))
  -- the element `v`
  obtain ⟨v, hv⟩ : ∃ v : SobolevIntervalLp 1 p I, v = mk ![hGmem.toLp G, w₀] fun j ↦ by
      fin_cases j
      · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
          ((Lp.memLp _).locallyIntegrableOn (Ω := I) Fact.out)
      · exact ((hw₀mem.locallyIntegrableOn hp1).hasWeakDerivOn_integral hI hy₀ L).congr_ae
          hGmem.coeFn_toLp.symm EventuallyEq.rfl := ⟨_, rfl⟩
  have hvfn : fn v =ᵐ[volume.restrict I] G := by rw [hv]; exact hGmem.coeFn_toLp
  have hvd : deriv v 1 = w₀ := by rw [hv]; rfl
  have hvrep : EqOn (rep v) G (closure (I : Set ℝ)) := rep_eq_of_continuousOn hI v hGcont hvfn
  refine ⟨v, φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun R ↦ ?_, fun f ↦ ?_⟩
  · -- uniform convergence on bounded parts of the closure
    have hK : IsCompact (closure (I : Set ℝ) ∩ Icc (-R) R) :=
      isCompact_Icc.inter_left isClosed_closure
    refine tendstoUniformlyOn_of_equicontinuousOn_of_tendsto hK ?_ fun x hx ↦
      (hvrep hx.1).symm ▸ hpt x hx.1
    -- equicontinuity from the uniform Hölder bound
    have hp_gt : 1 < p := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).1 hq.lt_top
    have he : 0 < 1 - p.toReal⁻¹ := one_sub_toReal_inv_pos hp_gt
    have hmod : Tendsto (fun d : ℝ ↦ M * d ^ (1 - p.toReal⁻¹)) (𝓝 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (1 - p.toReal⁻¹) (Or.inr he.le)).tendsto
      rw [Real.zero_rpow he.ne'] at this
      simpa using this.const_mul M
    refine (equicontinuous_restrict_iff _).1 (Metric.equicontinuous_of_continuity_modulus _ hmod
      (fun n (x : ↥(closure (I : Set ℝ) ∩ Icc (-R) R)) ↦ rep (u (φ₁ (φ₂ n))) x) fun x y n ↦ ?_)
    rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq]
    exact (abs_rep_sub_rep_le hI _ x.2.1 y.2.1).trans
      (mul_le_mul_of_nonneg_right ((norm_deriv_le _ 1).trans (hM _)) (by positivity))
  · rw [hvd]
    exact hpair _ (Lp.memLp f)

end SobolevIntervalLp

end Subseq

/-! ### Remark 4, second clause: an `L^p` limit with bounded derivatives is in `W^{1,p}` -/

section Remark4

variable {I : Opens ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SobolevIntervalLp

/-- The `L^p(I)` norm of the weak derivative of `u ∈ W^{1,p}(I)` read as a family of linear
maps `t ↦ t u'(x)` (the tensor formulation) is `‖u'‖_p`. -/
theorem eLpNorm_toSpanSingleton_deriv (u : SobolevIntervalLp 1 p I) :
    eLpNorm (fun x ↦ ContinuousLinearMap.toSpanSingleton ℝ (deriv u 1 x)) p
      (volume.restrict (I : Set ℝ)) = ‖deriv u 1‖ₑ := by
  rw [Lp.enorm_def]
  exact eLpNorm_congr_norm_ae ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous
    |>.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)) (Lp.aestronglyMeasurable _)
    (Eventually.of_forall fun x ↦ ContinuousLinearMap.norm_toSpanSingleton _)

/-- **Remark 4 of [brezis2011functional] §8.2, second clause** (the "in fact" sentence, Exercise
8.2): for `1 < p ≤ ∞`, if `u_n ∈ W^{1,p}(I)` converge to `f` in `L^p(I)` and `‖u_n'‖_p` stays
bounded, then `f ∈ W^{1,p}(I)`. No subsequence is extracted: the bound of Proposition 8.3 (ii)
passes to the limit, `MemSobolev.of_tendsto_eLpNorm_of_eLpNorm_le`. -/
theorem memSobolevIntervalLp_of_tendsto_of_bounded_deriv [ENNReal.HolderConjugate p q]
    (hq : q ≠ ⊤) {u : ℕ → SobolevIntervalLp 1 p I} {M : ℝ} (hM : ∀ n, ‖deriv (u n) 1‖ ≤ M)
    {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict I))
    (hlim : Tendsto (fun n ↦ eLpNorm (fn (u n) - f) p (volume.restrict I)) atTop (𝓝 0)) :
    MemSobolevIntervalLp f 1 p I := by
  refine memSobolevIntervalLp_iff_memSobolev.2 (MemSobolev.of_tendsto_eLpNorm_of_eLpNorm_le hq
    (u := fun n ↦ fn (u n))
    (w := fun n x ↦ ContinuousLinearMap.toSpanSingleton ℝ (deriv (u n) 1 x))
    (fun n ↦ memLp_deriv (u n) 0) (fun n ↦ (hasWeakDerivOn_fn (u n)).hasWeakFDerivOn)
    (M := ENNReal.ofReal M) ENNReal.ofReal_ne_top (fun n ↦ ?_) hf hlim)
  rw [eLpNorm_toSpanSingleton_deriv, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hM n)

end SobolevIntervalLp

end Remark4

end
