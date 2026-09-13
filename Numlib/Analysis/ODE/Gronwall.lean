import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Gronwall's lemma in integral form, and linear differential inequalities

Mathlib's `Mathlib/Analysis/ODE/Gronwall.lean` proves the *differential* form of Gronwall's
inequality with a constant coefficient and a constant forcing term
(`le_gronwallBound_of_liminf_deriv_right_le`, `norm_le_gronwallBound_of_norm_deriv_right_le`).
The numerical-analysis books state the lemma in *integral* form with a variable weight
([quarteroni2000numerical] Lemma 11.1, which cites Quarteroni–Valli for the proof): if
`φ t ≤ g t + ∫_a^t p φ` on `[a, b]` with `p ≥ 0` and `g` nondecreasing, then
`φ t ≤ g t exp (∫_a^t p)`. The energy estimates of the same books ([quarteroni2000numerical]
(13.7), (13.67)) use differential forms with a variable coefficient and a forcing term instead.

Everything here rests on one *variation-of-constants inequality*,
`Gronwall.le_exp_integral_mul_of_hasDerivWithinAt_le`: a function with right derivatives
satisfying `F' ≤ p F + q` on `[a, b)` is bounded by the solution of the equality,
`F t ≤ e^{P t} (F a + ∫_a^t e^{-P s} q s ds)` with `P t = ∫_a^t p`. Its proof is the comparison
`(e^{-P} F)' ≤ e^{-P} q` through Mathlib's `image_le_of_deriv_right_le_deriv_boundary`; nothing is
integrated, and no integrability of `F'` is needed. The integral form for a continuous weight
follows by applying it to the majorant `Ψ t = ∫_a^t p φ` shifted by `g t (e^{P} - 1)`, whose
right derivative is `p φ` by the fundamental theorem of calculus
(`Gronwall.hasDerivWithinAt_integral_Ici`); the book's version with a merely integrable weight
follows from the continuous one by approximating the weight in `L¹` by continuous functions.

Conventions. Intervals are `Icc a b` as in Mathlib's Gronwall file (the books' `[t₀, t₀ + T]` is
`a = t₀`, `b = t₀ + T`); derivatives are right derivatives on `Ico a b` together with continuity
on `Icc a b`, the weakest hypotheses under which the comparison argument runs, so that a consumer
holding `HasDerivWithinAt F (F' t) (Icc a b) t` converts with `HasDerivWithinAt.continuousOn` and
`HasDerivWithinAt.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)`.
-/

open Set Filter Topology intervalIntegral Real
open MeasureTheory (volume)

namespace Gronwall

variable {a b t : ℝ}

/-- The fundamental theorem of calculus in the form the comparison arguments below need: the
primitive `u ↦ ∫_a^u p` of a function continuous on `Icc a b` has right derivative `p t` at every
`t ∈ Ico a b`. -/
theorem hasDerivWithinAt_integral_Ici {p : ℝ → ℝ} (hp : ContinuousOn p (Icc a b))
    (ht : t ∈ Ico a b) : HasDerivWithinAt (fun u => ∫ s in a..u, p s) (p t) (Ici t) t := by
  have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
  have hint : IntervalIntegrable p volume a t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact (hp.mono (Icc_subset_Icc_right ht.2.le)).integrableOn_Icc
  have : Fact (t ∈ Icc a b) := ⟨ht'⟩
  have h : HasDerivWithinAt (fun u => ∫ s in a..u, p s) (p t) (Icc a b) t :=
    integral_hasDerivWithinAt_right hint
      (hp.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hp t ht')
  exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- The primitive `u ↦ ∫_a^u p` of a function continuous on `Icc a b` is continuous there. -/
theorem continuousOn_integral_Icc {p : ℝ → ℝ} (hp : ContinuousOn p (Icc a b)) :
    ContinuousOn (fun u => ∫ s in a..u, p s) (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · have h := continuousOn_primitive_interval (a := a) (b := b) (μ := volume) (f := p)
      (by rw [uIcc_of_le hab]; exact hp.integrableOn_Icc)
    rwa [uIcc_of_le hab] at h
  · simp [Icc_eq_empty_of_lt hab]

/-- **Variation-of-constants inequality.** If `F` is continuous on `Icc a b` with right
derivative `F'` on `Ico a b`, `p` and `q` are continuous on `Icc a b`, and `F' ≤ p F + q` on
`Ico a b`, then `F` is bounded by the solution of the corresponding linear equation:
`F t ≤ e^{P t} (F a + ∫_a^t e^{-P s} q s ds)` with `P t = ∫_a^t p`, for `t ∈ Icc a b`.

Every Gronwall-type inequality of this file is an instance. The proof is the comparison
`(e^{-P} F)' ≤ e^{-P} q` on `Ico a b`, closed by `image_le_of_deriv_right_le_deriv_boundary`; it
integrates nothing and needs no integrability of `F'`. -/
theorem le_exp_integral_mul_of_hasDerivWithinAt_le {F F' p q : ℝ → ℝ}
    (hF : ContinuousOn F (Icc a b)) (hF' : ∀ t ∈ Ico a b, HasDerivWithinAt F (F' t) (Ici t) t)
    (hp : ContinuousOn p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (bound : ∀ t ∈ Ico a b, F' t ≤ p t * F t + q t) (ht : t ∈ Icc a b) :
    F t ≤ exp (∫ s in a..t, p s) *
      (F a + ∫ s in a..t, exp (-∫ r in a..s, p r) * q s) := by
  set P : ℝ → ℝ := fun u => ∫ s in a..u, p s with hP
  have hPc : ContinuousOn P (Icc a b) := continuousOn_integral_Icc hp
  have hP' : ∀ u ∈ Ico a b, HasDerivWithinAt P (p u) (Ici u) u := fun u hu =>
    hasDerivWithinAt_integral_Ici hp hu
  have hQc : ContinuousOn (fun s => exp (-P s) * q s) (Icc a b) := (hPc.neg.rexp).mul hq
  set B : ℝ → ℝ := fun u => F a + ∫ s in a..u, exp (-P s) * q s with hB
  have hBc : ContinuousOn B (Icc a b) := continuousOn_const.add (continuousOn_integral_Icc hQc)
  have hB' : ∀ u ∈ Ico a b, HasDerivWithinAt B (exp (-P u) * q u) (Ici u) u := fun u hu =>
    (hasDerivWithinAt_integral_Ici hQc hu).const_add _
  have hGc : ContinuousOn (fun u => exp (-P u) * F u) (Icc a b) := (hPc.neg.rexp).mul hF
  have hG' : ∀ u ∈ Ico a b, HasDerivWithinAt (fun u => exp (-P u) * F u)
      (exp (-P u) * (F' u - p u * F u)) (Ici u) u := by
    intro u hu
    exact (((hP' u hu).neg.exp).mul (hF' u hu)).congr_deriv (by simp only [Pi.neg_apply]; ring)
  have key : exp (-P t) * F t ≤ B t := by
    refine image_le_of_deriv_right_le_deriv_boundary hGc hG' ?_ hBc hB' ?_ ht
    · simp [P, B]
    · intro u hu
      exact mul_le_mul_of_nonneg_left (by linarith [bound u hu]) (exp_pos _).le
  calc F t = exp (P t) * (exp (-P t) * F t) := by
        rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
    _ ≤ exp (P t) * B t := by gcongr

/-- **Differential Gronwall inequality with a variable coefficient and a forcing term**
([quarteroni2000numerical] (13.67); the differential form of their Lemma 11.1). If `Φ` is
continuous on `Icc a b` with right derivative `Φ'` on `Ico a b`, `p` and `g` are continuous and
nonnegative on `Icc a b`, and `Φ' ≤ p Φ + g` on `Ico a b`, then
`Φ t ≤ (Φ a + ∫_a^t g) exp (∫_a^t p)` for `t ∈ Icc a b`. -/
theorem le_mul_exp_integral_of_hasDerivWithinAt_le {Φ Φ' p g : ℝ → ℝ}
    (hΦ : ContinuousOn Φ (Icc a b)) (hΦ' : ∀ t ∈ Ico a b, HasDerivWithinAt Φ (Φ' t) (Ici t) t)
    (hp : ContinuousOn p (Icc a b)) (hp0 : ∀ t ∈ Icc a b, 0 ≤ p t)
    (hg : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (bound : ∀ t ∈ Ico a b, Φ' t ≤ p t * Φ t + g t) (ht : t ∈ Icc a b) :
    Φ t ≤ (Φ a + ∫ s in a..t, g s) * exp (∫ s in a..t, p s) := by
  have hPc : ContinuousOn (fun u => ∫ s in a..u, p s) (Icc a b) := continuousOn_integral_Icc hp
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hmono : ∫ s in a..t, exp (-∫ r in a..s, p r) * g s ≤ ∫ s in a..t, g s := by
    refine integral_mono_on ht.1 ?_ ?_ fun s hs => ?_
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
      exact (((hPc.neg.rexp).mul hg).mono hsub).integrableOn_Icc
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
      exact (hg.mono hsub).integrableOn_Icc
    · have h0 : 0 ≤ ∫ r in a..s, p r :=
        integral_nonneg hs.1 fun r hr => hp0 r (hsub ⟨hr.1, hr.2.trans hs.2⟩)
      exact mul_le_of_le_one_left (hg0 s (hsub hs)) (exp_le_one_iff.2 (neg_nonpos.2 h0))
  calc Φ t ≤ exp (∫ s in a..t, p s) * (Φ a + ∫ s in a..t, exp (-∫ r in a..s, p r) * g s) :=
        le_exp_integral_mul_of_hasDerivWithinAt_le hΦ hΦ' hp hg bound ht
    _ ≤ exp (∫ s in a..t, p s) * (Φ a + ∫ s in a..t, g s) := by gcongr
    _ = (Φ a + ∫ s in a..t, g s) * exp (∫ s in a..t, p s) := mul_comm _ _

/-- **Linear differential inequality with a constant coefficient and a forcing term**, the form
behind the exponential energy decay of the heat equation ([quarteroni2000numerical] (13.7)). If
`E` is continuous on `Icc a b` with right derivative `E'` on `Ico a b`, `g` is continuous on
`Icc a b` and `E' ≤ -γ E + g` on `Ico a b`, then for `t ∈ Icc a b`,
`E t ≤ e^{-γ (t - a)} E a + ∫_a^t e^{γ (s - t)} g s ds`. No sign condition on `γ`, `g` or `E`. -/
theorem le_exp_neg_mul_add_integral_of_hasDerivWithinAt_le {E E' g : ℝ → ℝ} {γ : ℝ}
    (hE : ContinuousOn E (Icc a b)) (hE' : ∀ t ∈ Ico a b, HasDerivWithinAt E (E' t) (Ici t) t)
    (hg : ContinuousOn g (Icc a b)) (bound : ∀ t ∈ Ico a b, E' t ≤ -γ * E t + g t)
    (ht : t ∈ Icc a b) :
    E t ≤ exp (-γ * (t - a)) * E a + ∫ s in a..t, exp (γ * (s - t)) * g s := by
  have key := le_exp_integral_mul_of_hasDerivWithinAt_le hE hE' (p := fun _ => -γ)
    continuousOn_const hg bound ht
  simp only [integral_const, smul_eq_mul] at key
  refine key.trans (le_of_eq ?_)
  rw [mul_add, ← integral_const_mul]
  congr 1
  · rw [show (t - a) * -γ = -γ * (t - a) by ring]
  · refine integral_congr fun s _ => ?_
    rw [← mul_assoc, ← exp_add]
    ring_nf

/-- **Gronwall's lemma, integral form, continuous weight** ([quarteroni2000numerical] Lemma 11.1
with a continuous `p`). Let `p`, `g`, `φ` be continuous
on `Icc a b`, `p ≥ 0` there, `g` nondecreasing there. If `φ t ≤ g t + ∫_a^t p φ` for all
`t ∈ Icc a b`, then `φ t ≤ g t exp (∫_a^t p)` for all `t ∈ Icc a b`. The book also assumes `g`
continuous; the proof never uses it (only the value `g t` at the point of evaluation enters).

Proof: with `Ψ u = ∫_a^u p φ` and `P u = ∫_a^u p`, the function `F u = Ψ u - g t (e^{P u} - 1)`
has right derivative `p φ - g t p e^{P}` on `Ico a t`, which the hypothesis, the monotonicity
of `g` and `p ≥ 0` bound by `p F`; the variation-of-constants inequality with `q = 0` and
`F a = 0` gives `F t ≤ 0`, i.e. `Ψ t ≤ g t (e^{P t} - 1)`, and `φ t ≤ g t + Ψ t`. -/
theorem le_mul_exp_integral_of_continuousOn {p g φ : ℝ → ℝ}
    (hp : ContinuousOn p (Icc a b)) (hp0 : ∀ t ∈ Icc a b, 0 ≤ p t) (hgm : MonotoneOn g (Icc a b))
    (hφ : ContinuousOn φ (Icc a b)) (hle : ∀ t ∈ Icc a b, φ t ≤ g t + ∫ s in a..t, p s * φ s)
    (ht : t ∈ Icc a b) : φ t ≤ g t * exp (∫ s in a..t, p s) := by
  set P : ℝ → ℝ := fun u => ∫ s in a..u, p s with hP
  set Ψ : ℝ → ℝ := fun u => ∫ s in a..u, p s * φ s with hΨ
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hsub' : Ico a t ⊆ Ico a b := Ico_subset_Ico_right ht.2
  have hPc : ContinuousOn P (Icc a t) := (continuousOn_integral_Icc hp).mono hsub
  have hΨc : ContinuousOn Ψ (Icc a t) := (continuousOn_integral_Icc (hp.mul hφ)).mono hsub
  have hFc : ContinuousOn (fun u => Ψ u - g t * (exp (P u) - 1)) (Icc a t) :=
    hΨc.sub (continuousOn_const.mul (hPc.rexp.sub continuousOn_const))
  have hF' : ∀ u ∈ Ico a t, HasDerivWithinAt (fun u => Ψ u - g t * (exp (P u) - 1))
      (p u * φ u - g t * (exp (P u) * p u)) (Ici u) u := fun u hu =>
    (hasDerivWithinAt_integral_Ici (hp.mul hφ) (hsub' hu)).sub
      (((hasDerivWithinAt_integral_Ici hp (hsub' hu)).exp.sub_const 1).const_mul _)
  have bound : ∀ u ∈ Ico a t, p u * φ u - g t * (exp (P u) * p u) ≤
      p u * (Ψ u - g t * (exp (P u) - 1)) + 0 := by
    intro u hu
    have hu' : u ∈ Icc a b := hsub (Ico_subset_Icc_self hu)
    have h1 : φ u ≤ g t + Ψ u := (hle u hu').trans (by gcongr; exact hgm hu' ht hu.2.le)
    have h2 : 0 ≤ p u := hp0 u hu'
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have key := le_exp_integral_mul_of_hasDerivWithinAt_le hFc hF' (hp.mono hsub)
    continuousOn_const bound (right_mem_Icc.2 ht.1)
  simp only [P, Ψ, integral_same, exp_zero, sub_self, mul_zero, integral_zero, add_zero] at key
  have := hle t ht
  linarith

/-- The `L¹` distance from an interval-integrable weight to a continuous nonnegative function can
be made arbitrarily small: given `p` integrable on `a..b`, nonnegative on `Icc a b`, and `ε > 0`,
there is a continuous `q ≥ 0` with `∫ s in a..b, |p s - q s| ≤ ε`. From the density of
continuous functions in `L¹` (`Integrable.exists_hasCompactSupport_integral_sub_le`), applied to
the indicator of `Ioc a b`, and truncation at `0`, which does not increase the distance to a
nonnegative function. -/
theorem exists_continuous_nonneg_integral_abs_sub_le {p : ℝ → ℝ} (hab : a ≤ b)
    (hp : IntervalIntegrable p volume a b) (hp0 : ∀ t ∈ Icc a b, 0 ≤ p t) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ → ℝ, Continuous q ∧ (∀ s, 0 ≤ q s) ∧ ∫ s in a..b, |p s - q s| ≤ ε := by
  have hP : MeasureTheory.Integrable ((Ioc a b).indicator p) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hp)
  obtain ⟨q₀, -, hq₀, hq₀c, hq₀i⟩ := hP.exists_hasCompactSupport_integral_sub_le hε
  refine ⟨fun s => max (q₀ s) 0, hq₀c.max continuous_const, fun s => le_max_right _ _, ?_⟩
  have hpI : MeasureTheory.IntegrableOn p (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hp
  have hqI : MeasureTheory.IntegrableOn (fun s => max (q₀ s) 0) (Ioc a b) volume :=
    (hq₀c.max continuous_const).integrableOn_Ioc
  calc ∫ s in a..b, |p s - max (q₀ s) 0|
      = ∫ s in Ioc a b, |p s - max (q₀ s) 0| := integral_of_le hab
    _ ≤ ∫ s in Ioc a b, ‖(Ioc a b).indicator p s - q₀ s‖ := by
        refine MeasureTheory.setIntegral_mono_on (hpI.sub hqI).abs
          (hP.sub hq₀i).norm.integrableOn measurableSet_Ioc fun s hs => ?_
        rw [Set.indicator_of_mem hs, Real.norm_eq_abs]
        have h0 : 0 ≤ p s := hp0 s (Ioc_subset_Icc_self hs)
        calc |p s - max (q₀ s) 0| = |max (p s) 0 - max (q₀ s) 0| := by rw [max_eq_left h0]
          _ ≤ |p s - q₀ s| := abs_max_sub_max_le_abs _ _ _
    _ ≤ ∫ s, ‖(Ioc a b).indicator p s - q₀ s‖ :=
        MeasureTheory.setIntegral_le_integral (hP.sub hq₀i).norm
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ε := hq₀

/-- **Gronwall's lemma, integral form** ([quarteroni2000numerical] Lemma 11.1 as printed).
Let `p` be integrable on `a..b` and nonnegative on
`Icc a b`, `φ` continuous on `Icc a b`, `g` nondecreasing on `Icc a b`. If
`φ t ≤ g t + ∫_a^t p φ` for all `t ∈ Icc a b`, then `φ t ≤ g t exp (∫_a^t p)` for all
`t ∈ Icc a b`. (The book also assumes `g` continuous; it is not needed.)

Proof: approximate `p` in `L¹(a, b)` within `ε` by a continuous `q ≥ 0`
(`exists_continuous_nonneg_integral_abs_sub_le`). With `C` a bound of `|φ|` on the interval, the
hypothesis holds for `q` with `g` replaced by `g + C ε`, so the continuous version gives
`φ t ≤ (g t + C ε) exp (∫_a^t q)` with `|∫_a^t q - ∫_a^t p| ≤ ε`; let `ε → 0⁺`. -/
theorem le_mul_exp_integral {p g φ : ℝ → ℝ} (hp : IntervalIntegrable p volume a b)
    (hp0 : ∀ t ∈ Icc a b, 0 ≤ p t) (hgm : MonotoneOn g (Icc a b)) (hφ : ContinuousOn φ (Icc a b))
    (hle : ∀ t ∈ Icc a b, φ t ≤ g t + ∫ s in a..t, p s * φ s) (ht : t ∈ Icc a b) :
    φ t ≤ g t * exp (∫ s in a..t, p s) := by
  have hab : a ≤ b := ht.1.trans ht.2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC t ht)
  set P : ℝ := ∫ s in a..t, p s with hP
  -- the estimate for a fixed `ε`
  have key : ∀ ε > 0, ∃ Q : ℝ, |Q - P| ≤ ε ∧ φ t ≤ (g t + C * ε) * exp Q := by
    intro ε hε
    obtain ⟨q, hqc, hq0, hqε⟩ := exists_continuous_nonneg_integral_abs_sub_le hab hp hp0 hε
    have hqint : ∀ t' ∈ Icc a b, IntervalIntegrable q volume a t' := fun t' _ =>
      hqc.intervalIntegrable _ _
    have hmem : ∀ t' ∈ Icc a b, t' ∈ uIcc a b := fun t' ht' => by
      rw [uIcc_of_le hab]; exact ht'
    have hpint : ∀ t' ∈ Icc a b, IntervalIntegrable p volume a t' := fun t' ht' =>
      hp.mono_set (uIcc_subset_uIcc_left (hmem t' ht'))
    have hdint : IntervalIntegrable (fun s => |p s - q s|) volume a b :=
      (hp.sub (hqint b ⟨hab, le_rfl⟩)).abs
    -- the `L¹` distance on a subinterval
    have hsub : ∀ t' ∈ Icc a b, ∫ s in a..t', |p s - q s| ≤ ε := fun t' ht' =>
      (integral_mono_interval le_rfl ht'.1 ht'.2
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hdint).trans hqε
    -- the hypothesis for the continuous weight, with `g + C ε`
    have hle' : ∀ t' ∈ Icc a b, φ t' ≤ (g t' + C * ε) + ∫ s in a..t', q s * φ s := by
      intro t' ht'
      have hφc : ContinuousOn φ (uIcc a t') := by
        rw [uIcc_of_le ht'.1]; exact hφ.mono (Icc_subset_Icc_right ht'.2)
      have h1 : IntervalIntegrable (fun s => p s * φ s) volume a t' :=
        (hpint t' ht').mul_continuousOn hφc
      have h2 : IntervalIntegrable (fun s => q s * φ s) volume a t' :=
        (hqint t' ht').mul_continuousOn hφc
      have hdiff : |(∫ s in a..t', p s * φ s) - ∫ s in a..t', q s * φ s| ≤ C * ε := by
        rw [← integral_sub h1 h2]
        refine (abs_integral_le_integral_abs ht'.1).trans ?_
        calc ∫ s in a..t', |p s * φ s - q s * φ s|
            ≤ ∫ s in a..t', C * |p s - q s| := by
              refine integral_mono_on ht'.1 (h1.sub h2).abs
                ((hdint.mono_set (uIcc_subset_uIcc_left (hmem t' ht'))).const_mul C)
                fun s hs => ?_
              rw [← sub_mul, abs_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right
                (by simpa [Real.norm_eq_abs] using hC s (Icc_subset_Icc_right ht'.2 hs))
                (abs_nonneg _)
          _ = C * ∫ s in a..t', |p s - q s| := integral_const_mul _ _
          _ ≤ C * ε := mul_le_mul_of_nonneg_left (hsub t' ht') hC0
      have := hle t' ht'
      linarith [(abs_le.1 hdiff).2]
    refine ⟨∫ s in a..t, q s, ?_, ?_⟩
    · rw [hP, ← integral_sub (hqint t ht) (hpint t ht)]
      refine (abs_integral_le_integral_abs ht.1).trans ((le_of_eq ?_).trans (hsub t ht))
      exact integral_congr fun s _ => abs_sub_comm _ _
    · exact le_mul_exp_integral_of_continuousOn hqc.continuousOn (fun s _ => hq0 s)
        (hgm.add_const _) hφ hle' ht
  -- pass to the limit `ε → 0⁺`
  set F : ℝ → ℝ := fun ε =>
    max ((g t + C * ε) * exp (P + ε)) ((g t + C * ε) * exp (P - ε)) with hF
  have hFc : Continuous F := by fun_prop
  have hF0 : F 0 = g t * exp P := by simp [F]
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), φ t ≤ F ε := by
    refine eventually_nhdsWithin_of_forall fun ε hε => ?_
    obtain ⟨Q, hQ, hφQ⟩ := key ε hε
    obtain ⟨hQ1, hQ2⟩ := abs_le.1 hQ
    refine hφQ.trans ?_
    rcases le_or_gt 0 (g t + C * ε) with hg | hg
    · exact (mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) hg).trans (le_max_left _ _)
    · exact (mul_le_mul_of_nonpos_left (exp_le_exp.2 (by linarith)) hg.le).trans
        (le_max_right _ _)
  have hlim : Filter.Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (g t * exp P)) :=
    hF0 ▸ (hFc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim hev

/-- **Gronwall's lemma with a constant weight**, the instance behind the Liapunov stability of the
Cauchy problem under a Lipschitz field ([quarteroni2000numerical] §11.1): if `φ` is continuous
on `Icc a b`, `g` nondecreasing there, `0 ≤ L`, and `φ t ≤ g t + L ∫_a^t φ` on the interval, then
`φ t ≤ g t exp (L (t - a))` there. -/
theorem le_mul_exp_of_le_add_integral {g φ : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hgm : MonotoneOn g (Icc a b)) (hφ : ContinuousOn φ (Icc a b))
    (hle : ∀ t ∈ Icc a b, φ t ≤ g t + L * ∫ s in a..t, φ s) (ht : t ∈ Icc a b) :
    φ t ≤ g t * exp (L * (t - a)) := by
  have key := le_mul_exp_integral_of_continuousOn (p := fun _ => L) continuousOn_const
    (fun _ _ => hL) hgm hφ (fun t ht => by simpa [integral_const_mul] using hle t ht) ht
  simpa [integral_const, smul_eq_mul, mul_comm] using key

end Gronwall
