import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Brezis §4.1: some results about integration that everyone must know

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §4.1: the monotone and dominated convergence theorems,
Fatou's lemma, the density of `C_c(ℝ^N)` in `L¹(ℝ^N)`, Tonelli and Fubini, and (from the
Comments on chapter 4) Egorov's theorem. All are Mathlib's; the nodes restate them in the book's
form for real-valued functions on a measure space `(Ω, 𝓜, μ)`, written `(α, μ)`.

## Main results

* `theorem_4_1` — monotone convergence (Beppo Levi): an a.e. increasing sequence of integrable
  functions with bounded integrals converges a.e. to an integrable function, and in `L¹`.
* `theorem_4_2` — dominated convergence (Lebesgue).
* `lemma_4_1` — Fatou's lemma, with the a.e. `liminf` taken in `[0, ∞]` as the book allows.
* `theorem_4_3` — density of `C_c(ℝ^N)` in `L¹(ℝ^N)`.
* `theorem_4_4`, `theorem_4_5` — Tonelli and Fubini on a product of σ-finite measure spaces.
* `theorem_4_29` — Egorov's theorem on a finite measure space.

The book's `C_c(ℝ^N)` is `Continuous g ∧ HasCompactSupport g` on `EuclideanSpace ℝ (Fin N)` with
Lebesgue measure `volume`.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace Brezis.Chapter04

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### Theorem 4.2: the dominated convergence theorem -/

/-- **Theorem 4.2 (dominated convergence theorem, Lebesgue).** If `f n → g` a.e. and
`|f n| ≤ bound` a.e. for an integrable `bound`, then `g` is integrable and `‖f n - g‖₁ → 0`. -/
theorem theorem_4_2 {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {bound : α → ℝ}
    (hbound : Integrable bound μ) (hfb : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ bound x) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, |f n x - g x| ∂μ) atTop (𝓝 0) := by
  have hg_meas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hf n).aestronglyMeasurable) hlim
  have hgb : ∀ᵐ x ∂μ, |g x| ≤ bound x := by
    filter_upwards [hlim, ae_all_iff.2 hfb] with x hx hxb
    exact le_of_tendsto hx.abs (Eventually.of_forall hxb)
  have hg : Integrable g μ :=
    ⟨hg_meas, hasFiniteIntegral_of_dominated_convergence hbound.2 hfb hlim⟩
  refine ⟨hg, ?_⟩
  have := tendsto_integral_of_dominated_convergence (fun x => 2 * bound x)
    (fun n => ((hf n).sub hg).norm.aestronglyMeasurable) (hbound.const_mul 2)
    (fun n => ?_) (f := fun _ => (0 : ℝ)) ?_
  · simpa using this
  · filter_upwards [hfb n, hgb] with x hx hgx
    simp only [Real.norm_eq_abs, abs_abs, Pi.sub_apply]
    calc |f n x - g x| ≤ |f n x| + |g x| := abs_sub _ _
      _ ≤ 2 * bound x := by linarith
  · filter_upwards [hlim] with x hx
    simpa using (hx.sub_const (g x)).abs

/-! ### Theorem 4.1: the monotone convergence theorem -/

/-- **Theorem 4.1 (monotone convergence theorem, Beppo Levi).** An a.e. increasing sequence of
integrable functions whose integrals are bounded converges a.e. to a finite limit `g`, which is
integrable, and `‖f n - g‖₁ → 0`. -/
theorem theorem_4_1 {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (hbdd : BddAbove (Set.range fun n => ∫ x, f n x ∂μ)) :
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧
      Tendsto (fun n => ∫ x, |f n x - g x| ∂μ) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hbdd
  -- the increments `F n = f n - f 0 ≥ 0` and their supremum `S`
  set F : ℕ → α → ℝ := fun n x => f n x - f 0 x with hF_def
  have hF_int : ∀ n, Integrable (F n) μ := fun n => (hf n).sub (hf 0)
  have hF_nn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x := fun n =>
    hmono.mono fun x hx => sub_nonneg.2 (hx (Nat.zero_le n))
  have hF_mono : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (F n x) :=
    hmono.mono fun x hx m n hmn => ENNReal.ofReal_le_ofReal (sub_le_sub_right (hx hmn) _)
  have hF_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (F n x)) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hF_int n).aemeasurable
  set L : α → ℝ≥0∞ := fun x => ⨆ n, ENNReal.ofReal (F n x) with hL_def
  have hL_meas : AEMeasurable L μ := AEMeasurable.iSup hF_meas
  have hL_int : ∫⁻ x, L x ∂μ ≠ ∞ := by
    rw [hL_def, lintegral_iSup' hF_meas hF_mono]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B - ∫ x, f 0 x ∂μ))
      (iSup_le fun n => ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (hF_int n) (hF_nn n)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hF_def]
    simp only [integral_sub (hf n) (hf 0)]
    linarith [hB ⟨n, rfl⟩]
  have hL_fin : ∀ᵐ x ∂μ, L x < ∞ := ae_lt_top' hL_meas hL_int
  set S : α → ℝ := fun x => (L x).toReal with hS_def
  have hS_int : Integrable S μ := integrable_toReal_of_lintegral_ne_top hL_meas hL_int
  have hS_nn : ∀ x, 0 ≤ S x := fun x => ENNReal.toReal_nonneg
  -- `F n → S` a.e., hence `f n → f 0 + S`
  have hFS : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (S x)) := by
    filter_upwards [hL_fin, hF_mono, ae_all_iff.2 hF_nn] with x hx hmx hnn
    have h1 : Tendsto (fun n => ENNReal.ofReal (F n x)) atTop (𝓝 (L x)) := tendsto_atTop_iSup hmx
    have h2 := (ENNReal.tendsto_toReal hx.ne).comp h1
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, ENNReal.toReal_ofReal (hnn n)]
  have hFS_le : ∀ n, ∀ᵐ x ∂μ, F n x ≤ S x := fun n => by
    filter_upwards [hL_fin, hF_nn n] with x hx hnn
    rw [hS_def, ← ENNReal.toReal_ofReal hnn]
    exact ENNReal.toReal_mono hx.ne (le_iSup (fun n => ENNReal.ofReal (F n x)) n)
  refine ⟨fun x => f 0 x + S x, (hf 0).add hS_int, ?_, ?_⟩
  · filter_upwards [hFS] with x hx
    simpa [hF_def] using (tendsto_const_nhds (x := f 0 x)).add hx
  · -- dominated convergence with the bound `|f 0| + S`
    refine (theorem_4_2 hf ?_ ((hf 0).norm.add hS_int) fun n => ?_).2
    · filter_upwards [hFS] with x hx
      simpa [hF_def] using (tendsto_const_nhds (x := f 0 x)).add hx
    · filter_upwards [hFS_le n, hF_nn n] with x hx hnn
      simp only [Pi.add_apply, Real.norm_eq_abs]
      calc |f n x| = |f 0 x + F n x| := by rw [hF_def]; ring_nf
        _ ≤ |f 0 x| + |F n x| := abs_add_le _ _
        _ = |f 0 x| + F n x := by rw [abs_of_nonneg hnn]
        _ ≤ |f 0 x| + S x := by linarith

/-! ### Lemma 4.1: Fatou's lemma -/

/-- **Lemma 4.1 (Fatou's lemma).** For a sequence of a.e. nonnegative integrable functions with
bounded integrals, the a.e. limit inferior `f x = liminf fₙ x ≤ +∞` (taken in `[0, ∞]`, as the
book allows) is finite a.e., integrable, and `∫ f ≤ liminf ∫ fₙ`. -/
theorem lemma_4_1 {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hnn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) (hbdd : BddAbove (Set.range fun n => ∫ x, f n x ∂μ)) :
    (∀ᵐ x ∂μ, liminf (fun n => ENNReal.ofReal (f n x)) atTop < ∞) ∧
      Integrable (fun x => (liminf (fun n => ENNReal.ofReal (f n x)) atTop).toReal) μ ∧
      ∫ x, (liminf (fun n => ENNReal.ofReal (f n x)) atTop).toReal ∂μ ≤
        liminf (fun n => ∫ x, f n x ∂μ) atTop := by
  obtain ⟨B, hB⟩ := hbdd
  have hf_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hf n).aemeasurable
  set L : α → ℝ≥0∞ := fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop with hL_def
  have hL_meas : AEMeasurable L μ := AEMeasurable.liminf hf_meas
  have hI_nn : ∀ n, 0 ≤ ∫ x, f n x ∂μ := fun n => integral_nonneg_of_ae (hnn n)
  -- the integrals form a bounded sequence, so `ofReal` commutes with their `liminf`
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ∫ x, f n x ∂μ :=
    (isBoundedUnder_of ⟨B, fun n => hB ⟨n, rfl⟩⟩).isCoboundedUnder_ge
  have hbdd_below : IsBoundedUnder (· ≥ ·) atTop fun n => ∫ x, f n x ∂μ :=
    isBoundedUnder_of ⟨0, hI_nn⟩
  have hmono_ofReal : Monotone ENNReal.ofReal := fun _ _ h => ENNReal.ofReal_le_ofReal h
  have hofReal : ENNReal.ofReal (liminf (fun n => ∫ x, f n x ∂μ) atTop) =
      liminf (fun n => ENNReal.ofReal (∫ x, f n x ∂μ)) atTop :=
    hmono_ofReal.map_liminf_of_continuousAt _ ENNReal.continuous_ofReal.continuousAt
      hcobdd hbdd_below
  -- `∫⁻ L ≤ liminf ∫⁻ ofReal (f n) = ofReal (liminf ∫ f n) < ∞`
  have hL_le : ∫⁻ x, L x ∂μ ≤ ENNReal.ofReal (liminf (fun n => ∫ x, f n x ∂μ) atTop) := by
    rw [hofReal]
    refine (lintegral_liminf_le' hf_meas).trans (le_of_eq ?_)
    congr 1
    ext n
    exact (ofReal_integral_eq_lintegral_ofReal (hf n) (hnn n)).symm
  have hL_int : ∫⁻ x, L x ∂μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL_le
  have hL_fin : ∀ᵐ x ∂μ, L x < ∞ := ae_lt_top' hL_meas hL_int
  refine ⟨hL_fin, integrable_toReal_of_lintegral_ne_top hL_meas hL_int, ?_⟩
  rw [integral_toReal hL_meas hL_fin]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hL_le).trans (le_of_eq ?_)
  exact ENNReal.toReal_ofReal (le_liminf_of_le hcobdd (Eventually.of_forall hI_nn))

/-! ### Theorem 4.3: density of `C_c(ℝ^N)` in `L¹(ℝ^N)` -/

/-- **Theorem 4.3 (density).** `C_c(ℝ^N)` is dense in `L¹(ℝ^N)`: every integrable `f` is within
`ε` in `L¹` of a continuous function with compact support. -/
theorem theorem_4_3 {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : Integrable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin N) → ℝ, Continuous g ∧ HasCompactSupport g ∧
      ∫ x, |f x - g x| ≤ ε := by
  obtain ⟨g, hgs, hgε, hgc, -⟩ := hf.exists_hasCompactSupport_integral_sub_le hε
  exact ⟨g, hgc, hgs, by simpa [Real.norm_eq_abs] using hgε⟩

/-! ### Theorems 4.4 and 4.5: Tonelli and Fubini -/

variable {α₁ α₂ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂] {μ₁ : Measure α₁}
  {μ₂ : Measure α₂}

/-- **Theorem 4.4 (Tonelli).** On a product of σ-finite measure spaces, a measurable
`F : Ω₁ × Ω₂ → ℝ` such that (a) `∫ |F (x, y)| dμ₂ < ∞` for a.e. `x` and (b)
`∫ dμ₁ ∫ |F (x, y)| dμ₂ < ∞` is integrable on `Ω₁ × Ω₂`. Clause (a) is the integrability of the
sections and (b) the integrability of the iterated integral of `|F|`. -/
theorem theorem_4_4 [SigmaFinite μ₁] [SigmaFinite μ₂] {F : α₁ × α₂ → ℝ}
    (hF : AEStronglyMeasurable F (μ₁.prod μ₂))
    (ha : ∀ᵐ x ∂μ₁, Integrable (fun y => F (x, y)) μ₂)
    (hb : Integrable (fun x => ∫ y, |F (x, y)| ∂μ₂) μ₁) : Integrable F (μ₁.prod μ₂) :=
  (integrable_prod_iff hF).2 ⟨ha, by simpa [Real.norm_eq_abs] using hb⟩

/-- **Theorem 4.5 (Fubini).** On a product of σ-finite measure spaces, if `F ∈ L¹(Ω₁ × Ω₂)`
then for a.e. `x` the section `F (x, ·)` is integrable and `x ↦ ∫ F (x, y) dμ₂` is integrable;
symmetrically in the other variable; and the two iterated integrals both equal the integral of
`F` on the product. -/
theorem theorem_4_5 [SigmaFinite μ₁] [SigmaFinite μ₂] {F : α₁ × α₂ → ℝ}
    (hF : Integrable F (μ₁.prod μ₂)) :
    ((∀ᵐ x ∂μ₁, Integrable (fun y => F (x, y)) μ₂) ∧
        Integrable (fun x => ∫ y, F (x, y) ∂μ₂) μ₁) ∧
      ((∀ᵐ y ∂μ₂, Integrable (fun x => F (x, y)) μ₁) ∧
        Integrable (fun y => ∫ x, F (x, y) ∂μ₁) μ₂) ∧
      ∫ x, ∫ y, F (x, y) ∂μ₂ ∂μ₁ = ∫ z, F z ∂(μ₁.prod μ₂) ∧
      ∫ y, ∫ x, F (x, y) ∂μ₁ ∂μ₂ = ∫ z, F z ∂(μ₁.prod μ₂) :=
  ⟨⟨hF.prod_right_ae, hF.integral_prod_left⟩, ⟨hF.prod_left_ae, hF.integral_prod_right⟩,
    (integral_prod F hF).symm, (integral_prod_symm F hF).symm⟩

/-! ### Theorem 4.29: Egorov's theorem -/

/-- **Theorem 4.29 (Egorov; Comments on chapter 4).** On a finite measure space, if a sequence
of measurable functions converges a.e. to `g`, then for every `ε > 0` there is a measurable `A`
with `μ (Ω ∖ A) < ε` on which the convergence is uniform. -/
theorem theorem_4_29 [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : Set α, MeasurableSet A ∧ μ Aᶜ < ε ∧ TendstoUniformlyOn f g atTop A := by
  obtain ⟨t, ht, hμt, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto' hf hg hfg (lt_min (ENNReal.half_pos hε.ne') one_pos)
  refine ⟨tᶜ, ht.compl, ?_, hunif⟩
  rw [compl_compl]
  refine hμt.trans_lt ?_
  by_cases hε' : ε = ∞
  · rw [hε']
    exact (min_le_right _ _).trans_lt ENNReal.one_lt_top
  · exact (min_le_left _ _).trans_lt (ENNReal.half_lt_self hε.ne' hε')

end Brezis.Chapter04
