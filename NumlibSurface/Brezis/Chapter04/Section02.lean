import Numlib.MeasureTheory.Function.LpInterpolation
import Numlib.MeasureTheory.Function.LpSpace.Convergence
import NumlibSurface.Brezis.Chapter04.Section01

/-!
# Brezis §4.2: definition and elementary properties of `L^p` spaces

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §4.2. The space `L^p(Ω)` is Mathlib's
`MeasureTheory.Lp ℝ p μ` over a measure space `(α, μ)`, whose elements are classes of a.e. equal
functions, as in the book; membership of a function is `MemLp f p μ` and its (extended) norm is
`eLpNorm f p μ`. The two "Definition." paragraphs are read back as the book's formulas, and
Hölder, Minkowski, Fischer–Riesz and the a.e. subsequence theorem are Mathlib's, with Remark 2
and the domination clause of Theorem 4.9 from the backbone
`Numlib/MeasureTheory/Function/LpInterpolation` and `…/LpSpace/Convergence`.

## Main results

* `lpNorm_eq_integral_rpow`, `lInftyNorm_eq_sInf` — the definitions of `L^p`, `1 ≤ p < ∞`, and
  `L^∞` with their norms.
* `remark_4_1` — `|f| ≤ ‖f‖_∞` a.e.
* `theorem_4_6` — Hölder's inequality; `remark_4_2` — the `k`-fold Hölder inequality and the
  interpolation inequality.
* `theorem_4_7` — `L^p` is a normed vector space (Minkowski); `theorem_4_8` — Fischer–Riesz.
* `theorem_4_9` — a convergent sequence in `L^p` has an a.e. convergent subsequence dominated by
  an `L^p` function.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace Brezis.Chapter04

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### The definitions -/

/-- **The definition of `L^p` and `‖·‖_p` for `1 ≤ p < ∞`** (§4.2, first "Definition."): a
measurable `f : Ω → ℝ` belongs to `L^p` iff `|f| ^ p` is integrable, and then
`‖f‖_p = (∫ |f| ^ p) ^ (1 / p)`. -/
theorem lpNorm_eq_integral_rpow {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (∀ f : α → ℝ, AEStronglyMeasurable f μ →
      (MemLp f p μ ↔ Integrable (fun x => |f x| ^ p.toReal) μ)) ∧
    ∀ f : Lp ℝ p μ, ‖f‖ = (∫ x, |f x| ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine ⟨fun f hf => ?_, fun f => ?_⟩
  · rw [← memLp_norm_rpow_iff hf hp0 hp, ENNReal.div_self hp0 hp, memLp_one_iff_integrable]
    simp only [Real.norm_eq_abs]
  · have hint : Integrable (fun x => |f x| ^ p.toReal) μ := by
      simpa only [Real.norm_eq_abs] using (Lp.memLp f).integrable_norm_rpow hp0 hp
    rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.aestronglyMeasurable f),
      ← ENNReal.toReal_rpow]
    congr 1
    rw [← ENNReal.toReal_ofReal (integral_nonneg fun x => by positivity),
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hP.le, ← Real.norm_eq_abs, ofReal_norm]

/-- **The definition of `L^∞` and `‖·‖_∞`** (§4.2, second "Definition."): a measurable `f`
belongs to `L^∞` iff `|f| ≤ C` a.e. for some constant `C`, and then
`‖f‖_∞ = inf {C ; |f| ≤ C a.e.}`. -/
theorem lInftyNorm_eq_sInf :
    (∀ f : α → ℝ, AEStronglyMeasurable f μ → (MemLp f ∞ μ ↔ ∃ C : ℝ, ∀ᵐ x ∂μ, |f x| ≤ C)) ∧
    ∀ f : Lp ℝ ∞ μ, ‖f‖ = sInf {C : ℝ | ∀ᵐ x ∂μ, |f x| ≤ C} := by
  refine ⟨fun f hf => ⟨fun h => ⟨‖h.toLp f‖, ?_⟩, fun ⟨C, hC⟩ => memLp_top_of_bound hf C hC⟩,
    fun f => ?_⟩
  · filter_upwards [Lp.ae_norm_le_norm_top (h.toLp f), h.coeFn_toLp] with x hx hx'
    rw [← Real.norm_eq_abs, ← hx']
    exact hx
  · rcases eq_or_ne μ 0 with rfl | hμ
    · -- on the zero measure every constant works and both sides are `0`
      have h1 : {C : ℝ | ∀ᵐ x ∂(0 : Measure α), |f x| ≤ C} = Set.univ :=
        Set.eq_univ_of_forall fun C => by simp
      rw [h1, Real.sInf_of_not_bddBelow (not_bddBelow_univ (α := ℝ)), Lp.norm_def]
      simp
    · refine (IsLeast.csInf_eq ⟨?_, fun C hC => ?_⟩).symm
      · simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs] using Lp.ae_norm_le_norm_top f
      · rw [Set.mem_ofPred_eq] at hC
        by_cases hC0 : 0 ≤ C
        · rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f),
            ← ENNReal.toReal_ofReal hC0]
          refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
          exact eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using hC)
        · exfalso
          have : ∀ᵐ x ∂μ, False := hC.mono fun x hx => hC0 ((abs_nonneg _).trans hx)
          rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this
          exact hμ this

/-- **Remark 1.** For `f ∈ L^∞`, `|f| ≤ ‖f‖_∞` a.e. -/
theorem remark_4_1 (f : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, |f x| ≤ ‖f‖ := by
  simpa only [Real.norm_eq_abs] using Lp.ae_norm_le_norm_top f

/-! ### Hölder's inequality -/

/-- **Theorem 4.6 (Hölder's inequality).** For conjugate exponents `p, p'` (`1 ≤ p ≤ ∞`),
`f ∈ L^p` and `g ∈ L^{p'}`, the product `f g` is integrable and `∫ |f g| ≤ ‖f‖_p ‖g‖_{p'}`. -/
theorem theorem_4_6 {p q : ℝ≥0∞} [p.HolderConjugate q] {f g : α → ℝ} (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (f * g) μ ∧
      ∫ x, |f x * g x| ∂μ ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  refine ⟨hf.integrable_mul hg, ?_⟩
  have hfg : AEStronglyMeasurable (f * g) μ := hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have h : eLpNorm (f * g) 1 μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
    have := eLpNorm_smul_le_mul_eLpNorm_of_pos (φ := f) (f := g) (μ := μ) (r := 1) (p := p)
      (q := q) one_pos
    rwa [show f • g = f * g from funext fun x => smul_eq_mul _ _] at this
  calc ∫ x, |f x * g x| ∂μ = ∫ x, ‖(f * g) x‖ ∂μ := by simp only [Real.norm_eq_abs, Pi.mul_apply]
    _ = (eLpNorm (f * g) 1 μ).toReal := by
        rw [integral_norm_eq_lintegral_enorm hfg, eLpNorm_one_eq_lintegral_enorm hfg]
    _ ≤ (eLpNorm f p μ * eLpNorm g q μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) h
    _ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := ENNReal.toReal_mul

/-- **Remark 2.** (i) The `k`-fold Hölder inequality: if `f i ∈ L^{p i}` for `i ∈ s` and
`1 / p = ∑ 1 / p i ≤ 1`, then `∏ f i ∈ L^p` and `‖∏ f i‖_p ≤ ∏ ‖f i‖_{p i}`. (ii) The
interpolation inequality: if `f ∈ L^p ∩ L^q` with `1 ≤ p ≤ q ≤ ∞`, then `f ∈ L^r` for every
`p ≤ r ≤ q`, and `‖f‖_r ≤ ‖f‖_p ^ α ‖f‖_q ^ (1 - α)` where `1 / r = α / p + (1 - α) / q`,
`0 ≤ α ≤ 1`. -/
theorem remark_4_2 :
    (∀ {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) (p : ι → ℝ≥0∞) (r : ℝ≥0∞),
      (∀ i ∈ s, MemLp (f i) (p i) μ) → r⁻¹ = ∑ i ∈ s, (p i)⁻¹ → 1 ≤ r →
        MemLp (∏ i ∈ s, f i) r μ ∧
          eLpNorm (∏ i ∈ s, f i) r μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ) ∧
    ∀ (f : α → ℝ) (p q r : ℝ≥0∞) (θ : ℝ), 1 ≤ p → p ≤ r → r ≤ q → MemLp f p μ → MemLp f q μ →
      0 ≤ θ → θ ≤ 1 → r⁻¹ = ENNReal.ofReal θ * p⁻¹ + ENNReal.ofReal (1 - θ) * q⁻¹ →
        MemLp f r μ ∧ eLpNorm f r μ ≤ eLpNorm f p μ ^ θ * eLpNorm f q μ ^ (1 - θ) := by
  refine ⟨fun s f p r hf hr _ => ?_, fun f p q r θ hp hpr hrq hfp hfq hθ₀ hθ₁ hr => ?_⟩
  · have h := eLpNorm_finset_prod_le (fun i hi => (hf i hi).aestronglyMeasurable) hr
    refine ⟨memLp_iff.2 (h.trans_lt (ENNReal.prod_lt_top fun i hi => (hf i hi).eLpNorm_lt_top)), h⟩
  · exact ⟨hfp.interpolate (zero_lt_one.trans_le hp).ne' hfq hpr hrq,
      eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hfp.aestronglyMeasurable hθ₀ hθ₁ hr⟩

/-! ### `L^p` is a Banach space -/

/-- **Theorem 4.7.** `L^p` is a vector space and `‖·‖_p` is a norm, `1 ≤ p ≤ ∞`: sums and
scalar multiples of `L^p` functions are in `L^p` (`MemLp.add`, `MemLp.const_smul`), and on the
classes `‖f + g‖ ≤ ‖f‖ + ‖g‖` (Minkowski's inequality), `‖c • f‖ = |c| ‖f‖` and `‖f‖ = 0` iff
`f = 0`. -/
theorem theorem_4_7 {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (∀ f g : α → ℝ, MemLp f p μ → MemLp g p μ → MemLp (f + g) p μ) ∧
    (∀ (c : ℝ) (f : α → ℝ), MemLp f p μ → MemLp (c • f) p μ) ∧
    (∀ f g : Lp ℝ p μ, ‖f + g‖ ≤ ‖f‖ + ‖g‖) ∧
    (∀ (c : ℝ) (f : Lp ℝ p μ), ‖c • f‖ = |c| * ‖f‖) ∧
    ∀ f : Lp ℝ p μ, ‖f‖ = 0 ↔ f = 0 :=
  ⟨fun _ _ hf hg => hf.add hg, fun c _ hf => hf.const_smul c, fun f g => norm_add_le f g,
    fun c f => by rw [norm_smul, Real.norm_eq_abs], fun f => norm_eq_zero⟩

/-- **Theorem 4.8 (Fischer–Riesz).** `L^p` is a Banach space, `1 ≤ p ≤ ∞`. -/
theorem theorem_4_8 {p : ℝ≥0∞} [Fact (1 ≤ p)] : CompleteSpace (Lp ℝ p μ) := inferInstance

/-- **Theorem 4.9.** If `fₙ → f` in `L^p`, `1 ≤ p ≤ ∞`, there are a subsequence `f_{nₖ}` and
`h ∈ L^p` with (a) `f_{nₖ} → f` a.e. and (b) `|f_{nₖ}| ≤ h` a.e. for every `k`. -/
theorem theorem_4_9 {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℕ → Lp ℝ p μ} {g : Lp ℝ p μ}
    (hfg : Tendsto f atTop (𝓝 g)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ h : Lp ℝ p μ,
      (∀ᵐ x ∂μ, Tendsto (fun k => f (ns k) x) atTop (𝓝 (g x))) ∧
        ∀ k, ∀ᵐ x ∂μ, |f (ns k) x| ≤ h x := by
  obtain ⟨ns, hns, h, h1, h2⟩ := Lp.exists_subseq_tendsto_ae_ae_le_of_tendsto hfg
  exact ⟨ns, hns, h, h1, fun k => by simpa only [Real.norm_eq_abs] using h2 k⟩

end Brezis.Chapter04
