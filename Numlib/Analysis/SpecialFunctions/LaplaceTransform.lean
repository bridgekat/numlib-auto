import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The Laplace transform

The Laplace transform `L(s) = ∫_0^∞ e^{-st} f(t) dt` of a function `f : ℝ → E` into a complex
normed space, in the *conditional* (improper) sense of the textbooks — the limit of the truncated
integrals `∫_0^T` as `T → ∞` — with its region of convergence and abscissa of convergence, the
relation to the Fourier transform, the transform of the unit step and of a derivative, the
transform of a sample-and-hold function, and the Z-transform of a sampled sequence as the discrete
Laplace transform. The material is [quarteroni2000numerical] §10.11.3–10.11.4 (Definitions
10.2–10.3, Property 10.4, Examples 10.8–10.9); the convergence theory follows
D. V. Widder, *The Laplace Transform*, Chapter II.

Mathlib has no Laplace transform (the closest object is the Mellin transform
`Mathlib/Analysis/MellinTransform.lean`, an absolutely convergent Bochner integral); the
substitution `t = e^{-u}` relating the two is not used here because the conditional convergence
of Property 10.4 is the point.

## Main definitions

* `LaplaceTransform.truncated f s T` — the truncated Laplace integral `∫_0^T e^{-st} • f t dt`.
* `LaplaceTransform.Converges f s` — the Laplace integral converges at `s`: the truncated
  integrals have a limit as `T → ∞`.
* `LaplaceTransform.laplaceTransform f s` — that limit, the Laplace transform `ℒ[f](s)`, and `0`
  where the integral does not converge.
* `LaplaceTransform.abscissaOfConvergence f : EReal` — the infimum `λ` of the real parts at which
  the Laplace integral converges.
* `zTransform f Δt z` — the Z-transform `∑_{n ≥ 0} f(nΔt) z^{-n}` of the samples of `f`.

## Main statements

* `LaplaceTransform.laplaceTransform_eq_integral`, `LaplaceTransform.integrableOn_of_re_le` — under
  absolute convergence the transform is the Bochner integral over `(0, ∞)`, and absolute
  convergence propagates to the right.
* `LaplaceTransform.converges_of_re_lt`, `LaplaceTransform.converges_of_abscissaOfConvergence_lt` —
  **Property 10.4**: convergence at `s₀` gives convergence at every `s` with `Re s > Re s₀`, so
  the integral converges on the open half-plane `Re s > λ`. The proof is Widder's integration by
  parts against the bounded, convergent primitive `φ(T) = ∫_0^T e^{-s₀t} f`; the integration by
  parts with a merely locally integrable `f` is `integral_smul_eq_smul_integral_sub`, proved
  through absolutely continuous functions and the Lebesgue differentiation theorem.
* `LaplaceTransform.laplaceTransform_eq_fourier` — `L(σ + iω) = 𝓕(e^{-σt} f̃)(ω/2π)` with `f̃` the
  extension of `f` by zero.
* `LaplaceTransform.laplaceTransform_indicator_Ioi`, `LaplaceTransform.converges_indicator_Ioi_iff`
  — Example 10.8, the unit step: `ℒ[1_{(0,∞)}](s) = 1/s`, and the integral converges exactly when
  `Re s > 0`.
* `LaplaceTransform.laplaceTransform_deriv` — Example 10.9, `ℒ[y'](s) = s ℒ[y](s) − y(0)`.
* `LaplaceTransform.laplaceTransform_stepFun`, `zTransform_eq_discreteLaplace` — the transform of
  the sample-and-hold function `f₀ = f(nΔt)` on `[nΔt, (n+1)Δt)` is `((1 − e^{-sΔt})/s)` times the
  discrete Laplace transform `∑_n f(nΔt) e^{-nsΔt}`, which is the Z-transform at `z = e^{sΔt}`.
* `summable_zTransform` — the Cauchy–Hadamard root test for the Z-transform.
-/

open MeasureTheory Filter Function Topology Complex Set

open scoped FourierTransform

namespace LaplaceTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Definitions -/

/-- **The truncated Laplace integral** `∫_0^T e^{-st} • f t dt` of `f : ℝ → E`, `E` a complex
normed space, at `s : ℂ`. -/
noncomputable def truncated (f : ℝ → E) (s : ℂ) (T : ℝ) : E :=
  ∫ t in (0 : ℝ)..T, Complex.exp (-(s * t)) • f t

theorem truncated_def (f : ℝ → E) (s : ℂ) (T : ℝ) :
    truncated f s T = ∫ t in (0 : ℝ)..T, Complex.exp (-(s * t)) • f t := rfl

/-- **The Laplace integral converges at `s`** in the sense of [quarteroni2000numerical]
Definition 10.2: the truncated integrals `∫_0^T e^{-st} • f t dt` have a limit as `T → ∞`. This
is *conditional* (improper) convergence; the stronger
`IntegrableOn (fun t => e^{-st} • f t) (Ioi 0)` is absolute convergence, and implies it
(`converges_of_integrableOn`). -/
def Converges (f : ℝ → E) (s : ℂ) : Prop :=
  ∃ L : E, Tendsto (truncated f s) atTop (𝓝 L)

open Classical in
/-- **The Laplace transform** `L(s) = ∫_0^∞ e^{-st} f(t) dt` of [quarteroni2000numerical]
Definition 10.2, as the limit of the truncated integrals (`tendsto_truncated`), and `0` where the
integral does not converge. Under absolute convergence it is the Bochner integral over `(0, ∞)`
(`laplaceTransform_eq_integral`). -/
noncomputable def laplaceTransform (f : ℝ → E) (s : ℂ) : E :=
  if h : Converges f s then h.choose else 0

/-- Where the Laplace integral converges, the truncated integrals tend to the transform. -/
theorem tendsto_truncated {f : ℝ → E} {s : ℂ} (h : Converges f s) :
    Tendsto (truncated f s) atTop (𝓝 (laplaceTransform f s)) := by
  rw [laplaceTransform, dite_eq_left h]
  exact h.choose_spec

/-- The transform is the limit of the truncated integrals, whenever there is one. -/
theorem laplaceTransform_eq_of_tendsto {f : ℝ → E} {s : ℂ} {L : E}
    (h : Tendsto (truncated f s) atTop (𝓝 L)) : laplaceTransform f s = L :=
  tendsto_nhds_unique (tendsto_truncated ⟨L, h⟩) h

/-- Where the Laplace integral does not converge, the transform is `0` by convention. -/
theorem laplaceTransform_of_not_converges {f : ℝ → E} {s : ℂ} (h : ¬ Converges f s) :
    laplaceTransform f s = 0 := by
  rw [laplaceTransform, dite_eq_right h]

/-- Absolute convergence of the Laplace integral implies its convergence. -/
theorem converges_of_integrableOn [CompleteSpace E] {f : ℝ → E} {s : ℂ}
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • f t) (Ioi 0)) : Converges f s :=
  ⟨_, intervalIntegral_tendsto_integral_Ioi 0 h tendsto_id⟩

/-- **Under absolute convergence the transform is the Bochner integral over `(0, ∞)`**,
`MeasureTheory.intervalIntegral_tendsto_integral_Ioi`. -/
theorem laplaceTransform_eq_integral [CompleteSpace E] {f : ℝ → E} {s : ℂ}
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • f t) (Ioi 0)) :
    laplaceTransform f s = ∫ t : ℝ in Ioi 0, Complex.exp (-(s * t)) • f t :=
  laplaceTransform_eq_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 h tendsto_id)

/-- `‖e^{-s t}‖ = e^{-Re s · t}`. -/
theorem norm_exp_neg_mul (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-(s * t))‖ = Real.exp (-(s.re * t)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- **Absolute convergence propagates to the right**: if `e^{-s₀t} • f` is integrable on `(0, ∞)`
and `f` is a.e.-strongly measurable there, then so is `e^{-st} • f` for every `s` with
`Re s₀ ≤ Re s`, since `‖e^{-st}‖ = e^{-Re s · t} ≤ e^{-Re s₀ · t}` for `t ≥ 0`. -/
theorem integrableOn_of_re_le {f : ℝ → E} {s₀ s : ℂ}
    (h₀ : IntegrableOn (fun t : ℝ => Complex.exp (-(s₀ * t)) • f t) (Ioi 0))
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hs : s₀.re ≤ s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • f t) (Ioi 0) := by
  refine Integrable.mono' h₀.norm ((Continuous.aestronglyMeasurable (by fun_prop)).smul hf) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_smul, norm_smul, norm_exp_neg_mul, norm_exp_neg_mul]
  gcongr
  exact le_of_lt ht

/-- **The abscissa of convergence** `λ` of [quarteroni2000numerical] Property 10.4: the infimum
of the real parts of the `s` at which the Laplace integral converges, as an extended real — `⊤`
when the integral converges nowhere, `⊥` when it converges at points of arbitrarily negative
real part. The integral converges on the open half-plane `Re s > λ`
(`converges_of_abscissaOfConvergence_lt`). -/
noncomputable def abscissaOfConvergence (f : ℝ → E) : EReal :=
  sInf ((fun s : ℂ => (s.re : EReal)) '' {s | Converges f s})

/-! ### The relation to the Fourier transform, and the unit step -/

/-- **The relation to the Fourier transform** ([quarteroni2000numerical], after Definition 10.2):
for `f : ℝ → ℂ` with `e^{-st} f` integrable on `(0, ∞)`,

`L(σ + iω) = 𝓕 (e^{-σt} f̃) (ω / 2π)`,

where `f̃` is `f` on `t > 0` and `0` on `t ≤ 0`; the argument is `ω / 2π` because
`Real.fourierIntegral` carries the kernel `e^{-2πiνt}` (the textbook writes `F(e^{-σt} f̃)` with no
argument). -/
theorem laplaceTransform_eq_fourier {f : ℝ → ℂ} {s : ℂ}
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * f t) (Ioi 0)) :
    laplaceTransform f s =
      𝓕 (fun t : ℝ => Complex.exp (-(s.re * t)) * Set.indicator (Ioi 0) f t)
        (s.im / (2 * Real.pi)) := by
  rw [laplaceTransform_eq_integral h, Real.fourier_real_eq_integral_exp_smul,
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  by_cases ht : t ∈ Ioi 0
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, ← mul_assoc, ← Complex.exp_add]
    congr 2
    have hre : -2 * Real.pi * t * (s.im / (2 * Real.pi)) = -(t * s.im) := by
      field_simp
    rw [hre]
    apply Complex.ext <;> simp [mul_comm]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero, mul_zero]

/-- **The Laplace transform of the unit step** ([quarteroni2000numerical] Example 10.8): for
`Re s > 0`, `ℒ[1_{(0,∞)}](s) = ∫_0^∞ e^{-st} dt = 1 / s`. -/
theorem laplaceTransform_indicator_Ioi {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t : ℝ => Set.indicator (Ioi 0) (fun _ => (1 : ℂ)) t) s = 1 / s := by
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • (Ioi 0).indicator
      (fun _ => (1 : ℂ)) t) (Ioi 0) := by
    refine (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    simp [Set.indicator_of_mem ht]
  rw [laplaceTransform_eq_integral hint]
  have := integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => Complex.exp (-s * t))
    (f := fun t : ℝ => Complex.exp (-(s * t)) • (Ioi 0).indicator (fun _ => (1 : ℂ)) t)
    (fun t ht => by simp [Set.indicator_of_mem ht]), this]
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  field_simp
  simp

/-! ### The region of convergence -/

section IBP

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The primitive `x ↦ ∫_c^x h` of an interval integrable vector-valued function is absolutely
continuous — Mathlib's `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`, which
is stated for real-valued `h`, transferred through `‖∫_x^y h‖ ≤ |∫_x^y ‖h‖|`. -/
theorem _root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral'
    {h : ℝ → F} {a b c : ℝ} (hh : IntervalIntegrable h volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, h v) a b := by
  have hR := hh.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  unfold AbsolutelyContinuousOnInterval at hR ⊢
  refine squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ hR
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  refine Finset.sum_le_sum fun i hi => ?_
  obtain ⟨hx, hy⟩ := hnI.1 i hi
  have hcx : IntervalIntegrable h volume c (I i).1 := hh.mono_set (uIcc_subset_uIcc hc hx)
  have hcy : IntervalIntegrable h volume c (I i).2 := hh.mono_set (uIcc_subset_uIcc hc hy)
  rw [dist_eq_norm, dist_eq_norm, intervalIntegral.integral_interval_sub_left hcx hcy,
    intervalIntegral.integral_interval_sub_left hcx.norm hcy.norm, Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

end IBP

variable [CompleteSpace E]

/-- **Integration by parts against a primitive**: for `g` interval integrable on `[0, T]`, `u`
differentiable with continuous derivative `u'`, and `Φ(t) = ∫_0^t g`,

`∫_0^T u • g = u(T) • Φ(T) − ∫_0^T u' • Φ`.

Since `g` is merely integrable, `Φ` is differentiable only almost everywhere (the Lebesgue
differentiation theorem `IntervalIntegrable.ae_hasDerivAt_integral`); the difference of the two
sides is an absolutely continuous function with almost everywhere vanishing derivative, hence
constant (`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`), and it vanishes at `0`. -/
theorem integral_smul_eq_smul_integral_sub {g : ℝ → E} {u u' : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hg : IntervalIntegrable g volume 0 T) (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') :
    ∫ t in (0 : ℝ)..T, u t • g t
      = u T • (∫ t in (0 : ℝ)..T, g t)
        - ∫ t in (0 : ℝ)..T, u' t • (∫ r in (0 : ℝ)..t, g r) := by
  set Φ : ℝ → E := fun x => ∫ r in (0 : ℝ)..x, g r with hΦ
  have hucont : Continuous u := continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt
  have huC1 : ContDiff ℝ 1 u := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hu x).differentiableAt.restrictScalars ℝ, ?_⟩
    have : deriv u = u' := funext fun x => (hu x).deriv
    rw [this]
    exact hu'
  -- the four absolutely continuous pieces
  have hΦ_ac : AbsolutelyContinuousOnInterval Φ 0 T :=
    hg.absolutelyContinuousOnInterval_intervalIntegral' (by simp)
  have hΦ_cont : ContinuousOn Φ (uIcc 0 T) :=
    intervalIntegral.continuousOn_primitive_interval' hg (by simp)
  have hu_ac : AbsolutelyContinuousOnInterval u 0 T :=
    (huC1.contDiffOn (s := uIcc 0 T)).absolutelyContinuousOnInterval
  have hug : IntervalIntegrable (fun t => u t • g t) volume 0 T :=
    hg.continuousOn_smul hucont.continuousOn
  have hu'Φ : IntervalIntegrable (fun t => u' t • Φ t) volume 0 T :=
    (hu'.continuousOn.smul hΦ_cont).intervalIntegrable
  set Ψ : ℝ → E := fun x => (∫ t in (0 : ℝ)..x, u t • g t) - u x • Φ x
    + ∫ t in (0 : ℝ)..x, u' t • Φ t with hΨ
  have hΨ_ac : AbsolutelyContinuousOnInterval Ψ 0 T :=
    ((hug.absolutelyContinuousOnInterval_intervalIntegral' (by simp)).sub
      (hu_ac.smul hΦ_ac)).add (hu'Φ.absolutelyContinuousOnInterval_intervalIntegral' (by simp))
  -- its derivative vanishes almost everywhere on `[0, T]`
  have hΨ_deriv : ∀ᵐ x, x ∈ uIcc 0 T → HasDerivAt Ψ 0 x := by
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have hT' : ∀ᵐ x : ℝ, x ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hg.ae_hasDerivAt_integral, hug.ae_hasDerivAt_integral, h0, hT']
      with x hx1 hx2 hx0 hxT hxI
    have hxIoo : x ∈ Ioo 0 T := by
      rw [uIcc_of_le hT] at hxI
      exact ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxT⟩
    have hd1 : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, u t • g t) (u x • g x) x :=
      hx2 hxI 0 (by simp)
    have hdΦ : HasDerivAt Φ (g x) x := hx1 hxI 0 (by simp)
    have hd2 : HasDerivAt (fun y => u y • Φ y) (u x • g x + u' x • Φ x) x :=
      (hu x).smul hdΦ
    have hd3 : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, u' t • Φ t) (u' x • Φ x) x := by
      refine intervalIntegral.integral_hasDerivAt_right
        (hu'Φ.mono_set (uIcc_subset_uIcc_left
          (by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self hxIoo)))
        ?_ ?_
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          ((hu'.continuousOn.smul hΦ_cont).mono (by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self))
          x hxIoo
      · exact (hu'.continuousOn.smul hΦ_cont).continuousAt
          (by rw [uIcc_of_le hT]; exact Icc_mem_nhds hxIoo.1 hxIoo.2)
    have key : HasDerivAt Ψ (u x • g x - (u x • g x + u' x • Φ x) + u' x • Φ x) x :=
      (hd1.sub hd2).add hd3
    rw [show u x • g x - (u x • g x + u' x • Φ x) + u' x • Φ x = 0 by abel] at key
    exact key
  obtain ⟨C, hC⟩ := hΨ_ac.const_of_ae_hasDerivAt_zero hΨ_deriv
  have hΨ0 : Ψ 0 = 0 := by simp [hΨ, hΦ]
  have hΨT : Ψ T = 0 := by rw [hC T (by simp), ← hC 0 (by simp), hΨ0]
  have hΨT' : (∫ t in (0 : ℝ)..T, u t • g t) - u T • Φ T
      + ∫ t in (0 : ℝ)..T, u' t • Φ t = 0 := hΨT
  apply eq_of_sub_eq_zero
  convert hΨT' using 1
  abel

omit [CompleteSpace E] in
/-- For `f` locally integrable on `[0, ∞)`, the integrand `e^{-st} • f t` of the Laplace integral
is interval integrable on every `[0, T]`. -/
theorem intervalIntegrable_exp_smul {f : ℝ → E} (hf : LocallyIntegrableOn f (Ici 0)) (s : ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => Complex.exp (-(s * t)) • f t) volume 0 T := by
  have h1 : IntegrableOn f (Icc 0 T) :=
    hf.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  have h2 : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr h1
  exact h2.continuousOn_smul (Continuous.continuousOn (by fun_prop))

omit [CompleteSpace E] in
/-- For `f` locally integrable on `[0, ∞)`, the truncated Laplace integral is a continuous
function of the truncation point `T ∈ [0, ∞)`. -/
theorem continuousOn_truncated {f : ℝ → E} (hf : LocallyIntegrableOn f (Ici 0)) (s : ℂ) :
    ContinuousOn (truncated f s) (Ici 0) := by
  intro x hx
  have hx' : (0 : ℝ) ≤ x := hx
  have h := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_exp_smul hf s (by linarith : (0 : ℝ) ≤ x + 1))
    (by simp : (0 : ℝ) ∈ uIcc 0 (x + 1))
  rw [uIcc_of_le (by linarith)] at h
  refine (h x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin (mem_nhdsWithin.mpr ?_)
  exact ⟨Iio (x + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, hy.1.le⟩⟩

/-- **Property 10.4 of [quarteroni2000numerical], first clause** (Widder, *The Laplace Transform*,
Theorem II.1): for `f : ℝ → E` locally integrable on `[0, ∞)`, `E` complete, if the Laplace
integral converges at `s₀` then it converges at every `s` with `Re s > Re s₀`.

With `δ = s − s₀` and `φ(T) = ∫_0^T e^{-s₀t} • f`, which is continuous, bounded and convergent,
integration by parts (`integral_smul_eq_smul_integral_sub`) gives

`∫_0^T e^{-st} • f = e^{-δT} • φ(T) + δ • ∫_0^T e^{-δt} • φ(t) dt`;

the first term tends to `0` and the integral converges absolutely because `φ` is bounded and
`Re δ > 0`. -/
theorem converges_of_re_lt {f : ℝ → E} (hf : LocallyIntegrableOn f (Ici 0)) {s₀ s : ℂ}
    (h₀ : Converges f s₀) (hs : s₀.re < s.re) : Converges f s := by
  obtain ⟨L, hL⟩ := h₀
  set δ : ℂ := s - s₀ with hδ
  have hδre : 0 < δ.re := by rw [hδ, Complex.sub_re]; linarith
  set φ := truncated f s₀ with hφ
  -- the derivative of the exponential weight
  have hu : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(δ * t)))
      (-δ * Complex.exp (-(δ * x))) x := by
    intro x
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(δ * z)))
        (Complex.exp (-(δ * x)) * -(δ * 1)) x :=
      ((hasDerivAt_id (x : ℂ)).const_mul δ).neg.cexp
    exact (h1.comp_ofReal).congr_deriv (by ring)
  -- the integration by parts identity, for every `T ≥ 0`
  have hIBP : ∀ T, 0 ≤ T → truncated f s T
      = Complex.exp (-(δ * T)) • φ T + δ • ∫ t in (0 : ℝ)..T, Complex.exp (-(δ * t)) • φ t := by
    intro T hT
    have hg := intervalIntegrable_exp_smul hf s₀ hT
    have key := integral_smul_eq_smul_integral_sub hT hg hu (by fun_prop)
    have hlhs : truncated f s T
        = ∫ t in (0 : ℝ)..T, Complex.exp (-(δ * t)) • (Complex.exp (-(s₀ * t)) • f t) := by
      rw [truncated_def]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [smul_smul, ← Complex.exp_add]
      congr 2
      rw [hδ]
      ring
    rw [hlhs, key]
    simp only [neg_mul, neg_smul, intervalIntegral.integral_neg, sub_neg_eq_add, mul_smul,
      intervalIntegral.integral_smul]
    rfl
  -- the boundary term tends to zero
  have hexp : Tendsto (fun T : ℝ => Complex.exp (-(δ * T))) atTop (𝓝 0) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    have : (fun T : ℝ => (-(δ * (T : ℂ))).re) = fun T => -(δ.re * T) := by
      funext T
      simp
    rw [this]
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hδre)
  have h1 : Tendsto (fun T : ℝ => Complex.exp (-(δ * T)) • φ T) atTop (𝓝 0) :=
    hexp.zero_smul_isBoundedUnder_le hL.norm.isBoundedUnder_le
  -- the remaining integral converges absolutely
  have hφcont : ContinuousOn φ (Ici 0) := continuousOn_truncated hf s₀
  obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ Ici (0 : ℝ), ‖φ t‖ ≤ C := by
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hL.norm.eventually (gt_mem_nhds (lt_add_one ‖L‖)))
    obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hφcont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) (max T₀ 0) ⊆ Ici 0))
    refine ⟨max C₁ (‖L‖ + 1), fun t ht => ?_⟩
    by_cases htT : t ≤ max T₀ 0
    · exact (hC₁ t ⟨ht, htT⟩).trans (le_max_left _ _)
    · exact (hT₀ t ((le_max_left _ _).trans (not_le.mp htT).le)).le.trans (le_max_right _ _)
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(δ * t)) • φ t) (Ioi 0) := by
    have hexpint : IntegrableOn (fun t : ℝ => C * Real.exp (-δ.re * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hδre) 0).const_mul C
    refine Integrable.mono' hexpint ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).smul
        ((hφcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_smul, norm_exp_neg_mul, neg_mul, mul_comm]
      gcongr
      exact hC t (mem_Ici.mpr (mem_Ioi.mp ht).le)
  have h2 : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, Complex.exp (-(δ * t)) • φ t) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, Complex.exp (-(δ * t)) • φ t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  refine ⟨0 + δ • ∫ t : ℝ in Ioi 0, Complex.exp (-(δ * t)) • φ t, ?_⟩
  refine (h1.add (h2.const_smul δ)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (hIBP T hT).symm

/-- **Property 10.4 of [quarteroni2000numerical], second clause**: for `f` locally integrable on
`[0, ∞)`, `E` complete, the Laplace integral converges at every `s` with
`Re s > abscissaOfConvergence f` — on the open half-plane to the right of the abscissa of
convergence, and everywhere when the abscissa is `⊥`. -/
theorem converges_of_abscissaOfConvergence_lt {f : ℝ → E} (hf : LocallyIntegrableOn f (Ici 0))
    {s : ℂ} (hs : abscissaOfConvergence f < (s.re : EReal)) : Converges f s := by
  have hne : ((fun s : ℂ => (s.re : EReal)) '' {s | Converges f s}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [abscissaOfConvergence, h, sInf_empty] at hs
    exact not_top_lt hs
  obtain ⟨x, ⟨s₀, hs₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hs
  exact converges_of_re_lt hf hs₀ (EReal.coe_lt_coe_iff.mp hlt)

/-! ### The unit step and the transform of a derivative -/

/-- **The transform of a derivative** ([quarteroni2000numerical] Example 10.9, (10.83)): for
`y : ℝ → E` of class `C¹` such that `e^{-st} • y` and `e^{-st} • y'` are integrable on `(0, ∞)` and
`e^{-st} • y(t) → 0` as `t → ∞`,

`ℒ[y'](s) = s • ℒ[y](s) − y(0)`.

Integration by parts on `[0, T]` and the limit `T → ∞`. Consequently the solution of
`y' + a y = g`, `y(0) = y₀`, satisfies `(s + a) Y(s) = G(s) + y₀` wherever the three transforms
converge absolutely. -/
theorem laplaceTransform_deriv {y : ℝ → E} {s : ℂ} (hy : ContDiff ℝ 1 y)
    (h : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • y t) (Ioi 0))
    (h' : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • deriv y t) (Ioi 0))
    (hlim : Tendsto (fun t : ℝ => Complex.exp (-(s * t)) • y t) atTop (𝓝 0)) :
    laplaceTransform (deriv y) s = s • laplaceTransform y s - y 0 := by
  have hu : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(s * t)))
      (-s * Complex.exp (-(s * x))) x := by
    intro x
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(s * z)))
        (Complex.exp (-(s * x)) * -(s * 1)) x :=
      ((hasDerivAt_id (x : ℂ)).const_mul s).neg.cexp
    exact (h1.comp_ofReal).congr_deriv (by ring)
  have hyd : ∀ x : ℝ, HasDerivAt y (deriv y x) x := fun x =>
    (hy.differentiable one_ne_zero x).hasDerivAt
  have hy' : Continuous (deriv y) := hy.continuous_deriv le_rfl
  -- integration by parts on `[0, T]`
  have hIBP : ∀ T : ℝ, truncated (deriv y) s T
      = Complex.exp (-(s * T)) • y T - y 0 + s • truncated y s T := by
    intro T
    rw [truncated_def, intervalIntegral.integral_smul_deriv_eq_deriv_smul (fun x _ => hu x)
      (fun x _ => hyd x) (Continuous.intervalIntegrable (by fun_prop) _ _)
      (hy'.intervalIntegrable _ _), truncated_def]
    simp only [neg_mul, neg_smul, intervalIntegral.integral_neg, sub_neg_eq_add, mul_smul,
      intervalIntegral.integral_smul]
    simp
  -- the limits
  have h1 : Tendsto (truncated (deriv y) s) atTop (𝓝 (laplaceTransform (deriv y) s)) :=
    tendsto_truncated (converges_of_integrableOn h')
  have h2 : Tendsto (fun T : ℝ => Complex.exp (-(s * T)) • y T - y 0 + s • truncated y s T)
      atTop (𝓝 (0 - y 0 + s • laplaceTransform y s)) :=
    (hlim.sub_const _).add ((tendsto_truncated (converges_of_integrableOn h)).const_smul s)
  have := tendsto_nhds_unique h1 (h2.congr fun T => (hIBP T).symm)
  rw [this]
  abel

/-- **The region of convergence of the unit step** ([quarteroni2000numerical] Example 10.8): the
Laplace integral of `1_{(0,∞)}` converges exactly when `Re s > 0`, so its abscissa of convergence
is `0`. For `Re s ≤ 0` the truncated integral is `T` when `s = 0`, and otherwise
`(1 − e^{-sT})/s`, whose convergence would force `e^{-sT}` to converge to a limit `M` of norm at
least `1`; then `e^{-sh} M = M` for every shift `h`, so `h ↦ e^{-sh}` is constant and its derivative
`−s` at `0` vanishes. -/
theorem converges_indicator_Ioi_iff {s : ℂ} :
    Converges (fun t : ℝ => Set.indicator (Ioi 0) (fun _ => (1 : ℂ)) t) s ↔ 0 < s.re := by
  constructor
  · rintro ⟨L, hL⟩
    by_contra hre
    rw [not_lt] at hre
    -- the truncated integrals in closed form
    have htr : ∀ T : ℝ, 0 ≤ T → truncated (fun t : ℝ => Set.indicator (Ioi 0)
        (fun _ => (1 : ℂ)) t) s T = ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) := by
      intro T hT
      rw [truncated_def]
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      rw [uIoc_of_le hT] at ht
      simp [Set.indicator_of_mem (show t ∈ Ioi 0 from ht.1)]
    by_cases hs0 : s = 0
    · -- the truncated integral is `T` itself, unbounded
      subst hs0
      have hT : Tendsto (fun T : ℝ => ‖truncated (fun t : ℝ => Set.indicator (Ioi (0 : ℝ))
          (fun _ => (1 : ℂ)) t) 0 T‖) atTop atTop := by
        refine tendsto_id.congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        rw [htr T hT]
        simp [abs_of_nonneg hT]
      exact not_tendsto_atTop_of_tendsto_nhds hL.norm hT
    · -- `e^{-sT} = 1 - s · truncated` converges, to a nonzero limit, and is periodic-like
      have hexp : Tendsto (fun T : ℝ => Complex.exp (-(s * T))) atTop (𝓝 (1 - s * L)) := by
        have h1 : Tendsto (fun T : ℝ => 1 - s * truncated (fun t : ℝ => Set.indicator (Ioi 0)
            (fun _ => (1 : ℂ)) t) s T) atTop (𝓝 (1 - s * L)) :=
          (hL.const_mul s).const_sub 1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        rw [htr T hT, integral_exp_mul_complex (neg_ne_zero.mpr hs0)]
        field_simp
        simp
      set M := 1 - s * L with hM
      -- the limit has norm at least one
      have hM1 : 1 ≤ ‖M‖ := by
        refine ge_of_tendsto hexp.norm ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        rw [norm_exp_neg_mul]
        exact Real.one_le_exp (by nlinarith)
      have hM0 : M ≠ 0 := fun h => by rw [h, norm_zero] at hM1; linarith
      -- the exponential factor `e^{-s h}` is `1` for every shift `h`
      have hshift : ∀ h : ℝ, Complex.exp (-(s * h)) = 1 := by
        intro h
        have h1 : Tendsto (fun T : ℝ => Complex.exp (-(s * (T + h)))) atTop (𝓝 M) := by
          have := hexp.comp (tendsto_atTop_add_const_right atTop h tendsto_id)
          refine this.congr fun T => ?_
          simp [Function.comp]
        have h2 : Tendsto (fun T : ℝ => Complex.exp (-(s * (T + h)))) atTop
            (𝓝 (Complex.exp (-(s * h)) * M)) := by
          refine (hexp.const_mul (Complex.exp (-(s * h)))).congr fun T => ?_
          rw [← Complex.exp_add]
          congr 1
          ring
        have := tendsto_nhds_unique h2 h1
        exact (mul_left_eq_self₀.mp this).resolve_right hM0
      -- so its derivative at `0`, which is `-s`, vanishes
      have hd : HasDerivAt (fun h : ℝ => Complex.exp (-(s * h))) (-s) 0 := by
        have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(s * z)))
            (Complex.exp (-(s * (0 : ℝ))) * -(s * 1)) ((0 : ℝ) : ℂ) :=
          ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul s).neg.cexp
        exact (h1.comp_ofReal).congr_deriv (by simp)
      have hd' : HasDerivAt (fun h : ℝ => Complex.exp (-(s * h))) 0 0 :=
        (hasDerivAt_const (0 : ℝ) (1 : ℂ)).congr_of_eventuallyEq
          (Eventually.of_forall fun h => hshift h)
      exact hs0 (neg_eq_zero.mp (hd.unique hd'))
  · intro hs
    exact converges_of_integrableOn ((integrableOn_exp_mul_complex_Ioi (a := -s)
      (by simpa using hs) 0).congr_fun (fun t ht => by simp [Set.indicator_of_mem ht])
      measurableSet_Ioi)

/-! ### The sample-and-hold function and the Z-transform -/

/-- The sampling intervals `[n Δt, (n + 1) Δt)`, `n : ℕ`, cover `[0, ∞)`. -/
theorem iUnion_Ico_nat_mul {Δt : ℝ} (hΔt : 0 < Δt) :
    ⋃ n : ℕ, Ico ((n : ℝ) * Δt) ((n + 1) * Δt) = Ici 0 := by
  ext t
  simp only [mem_iUnion, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨n, hn, -⟩
    exact le_trans (by positivity) hn
  · intro ht
    refine ⟨⌊t / Δt⌋₊, ?_, ?_⟩
    · rw [← le_div_iff₀ hΔt]
      exact Nat.floor_le (div_nonneg ht hΔt.le)
    · rw [← div_lt_iff₀ hΔt]
      exact Nat.lt_floor_add_one _

/-- The sampling intervals `[n Δt, (n + 1) Δt)` are pairwise disjoint. -/
theorem pairwise_disjoint_Ico_nat_mul {Δt : ℝ} (hΔt : 0 < Δt) :
    Pairwise (Disjoint on fun n : ℕ => Ico ((n : ℝ) * Δt) ((n + 1) * Δt)) := by
  intro m n hmn
  simp only [Function.onFun, Set.Ico_disjoint_Ico]
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · have : ((m : ℝ) + 1) * Δt ≤ n * Δt := by
      gcongr
      exact_mod_cast h
    exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
  · have : ((n : ℝ) + 1) * Δt ≤ m * Δt := by
      gcongr
      exact_mod_cast h
    exact (min_le_right _ _).trans (this.trans (le_max_left _ _))

/-- **The Laplace transform of the sample-and-hold function** ([quarteroni2000numerical]
§10.11.4): for `Δt > 0`, the piecewise constant `f₀(t) = f(⌊t/Δt⌋ Δt)`, equal to `f(nΔt)` on
`[nΔt, (n+1)Δt)`, and `s` with `Re s > 0` at which `∑_n ‖f(nΔt)‖ e^{-n Re s Δt}` converges,

`ℒ[f₀](s) = ((1 − e^{-sΔt}) / s) · ∑_{n ≥ 0} f(nΔt) e^{-nsΔt}`.

The integral over `(0, ∞)` splits over the sampling intervals, on each of which `e^{-st}`
integrates to `(e^{-nsΔt} − e^{-(n+1)sΔt})/s`. The series is the *discrete Laplace transform* of
`f₀`, and the Z-transform of the samples at `z = e^{sΔt}` (`zTransform_eq_discreteLaplace`). -/
theorem laplaceTransform_stepFun {f : ℝ → ℂ} {Δt : ℝ} (hΔt : 0 < Δt) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun n : ℕ => ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt))) :
    laplaceTransform (fun t : ℝ => f (⌊t / Δt⌋ * Δt)) s
      = ((1 - Complex.exp (-(s * Δt))) / s)
        * ∑' n : ℕ, f (n * Δt) * Complex.exp (-(n * s * Δt)) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  set f₀ : ℝ → ℂ := fun t => f (⌊t / Δt⌋ * Δt) with hf₀
  set g : ℝ → ℂ := fun t => Complex.exp (-(s * t)) • f₀ t with hg
  set S : ℕ → Set ℝ := fun n => Ico ((n : ℝ) * Δt) ((n + 1) * Δt) with hS
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => measurableSet_Ico
  have hSle : ∀ n : ℕ, (n : ℝ) * Δt ≤ (n + 1) * Δt := fun n => by nlinarith
  -- on each sampling interval, `f₀` is the sample
  have hf₀_piece : ∀ n : ℕ, ∀ t ∈ S n, f₀ t = f (n * Δt) := by
    intro n t ht
    have hfl : ⌊t / Δt⌋ = (n : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor
      · rw [le_div_iff₀ hΔt]
        exact ht.1
      · rw [div_lt_iff₀ hΔt]
        exact ht.2
    simp only [hf₀, hfl, Int.cast_natCast]
  -- the integral over each sampling interval
  have hpiece : ∀ n : ℕ, ∫ t in S n, g t
      = f (n * Δt)
        * ((Complex.exp (-(s * (n * Δt))) - Complex.exp (-(s * ((n + 1) * Δt)))) / s) := by
    intro n
    rw [setIntegral_congr_fun (hSmeas n) (f := g)
      (g := fun t : ℝ => Complex.exp (-s * t) * f (n * Δt))
      (fun t ht => by simp only [hg, smul_eq_mul]; rw [hf₀_piece n t ht, neg_mul]),
      integral_mul_const, hS]
    simp only
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hSle n),
      integral_exp_mul_complex (neg_ne_zero.mpr hs0)]
    have e1 : Complex.exp (-s * ((((n : ℝ) + 1) * Δt : ℝ) : ℂ))
        = Complex.exp (-(s * ((n + 1) * Δt))) := by congr 1; push_cast; ring
    have e2 : Complex.exp (-s * (((n : ℝ) * Δt : ℝ) : ℂ))
        = Complex.exp (-(s * (n * Δt))) := by congr 1; push_cast; ring
    rw [e1, e2]
    field_simp
    ring
  -- integrability on each sampling interval, with a summable bound on the norms
  have hpiece_int : ∀ n, IntegrableOn g (S n) := by
    intro n
    refine IntegrableOn.congr_fun (f := fun t : ℝ => Complex.exp (-(s * t)) * f (n * Δt)) ?_
      (fun t ht => ?_) (hSmeas n)
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ico_subset_Icc_self
    · simp only [hg, smul_eq_mul]
      rw [hf₀_piece n t ht]
  have hnorm_piece : ∀ n, ∫ t in S n, ‖g t‖
      ≤ ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt)) * Δt := by
    intro n
    calc ∫ t in S n, ‖g t‖
        ≤ ∫ _ in S n, ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt)) := by
          refine setIntegral_mono_on (hpiece_int n).norm (integrableOn_const ?_) (hSmeas n)
            fun t ht => ?_
          · rw [hS]
            simp only
            rw [Real.volume_Ico]
            exact ENNReal.ofReal_ne_top
          · simp only [hg, norm_smul, hf₀_piece n t ht, norm_exp_neg_mul]
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
            have := ht.1
            nlinarith
      _ = ‖f (n * Δt)‖ * Real.exp (-(n * s.re * Δt)) * Δt := by
          rw [setIntegral_const, smul_eq_mul, hS]
          simp only
          rw [Real.volume_real_Ico_of_le (hSle n)]
          ring
  have hint : IntegrableOn g (⋃ n, S n) :=
    integrableOn_iUnion_of_summable_integral_norm hpiece_int
      (Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm_piece
        (hsum.mul_right Δt))
  have hSunion : ⋃ n, S n = Ici 0 := iUnion_Ico_nat_mul hΔt
  rw [laplaceTransform_eq_integral (hint.mono_set (hSunion ▸ Ioi_subset_Ici_self)),
    ← integral_Ici_eq_integral_Ioi, ← hSunion,
    integral_iUnion hSmeas (pairwise_disjoint_Ico_nat_mul hΔt) hint]
  simp only [hpiece]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [show Complex.exp (-(s * ((n + 1) * Δt)))
      = Complex.exp (-(s * (n * Δt))) * Complex.exp (-(s * Δt)) by
    rw [← Complex.exp_add]; congr 1; ring]
  rw [show Complex.exp (-(n * s * Δt)) = Complex.exp (-(s * (n * Δt))) by congr 1; ring]
  field_simp

end LaplaceTransform

/-- **The Z-transform** of the samples `f(nΔt)` ([quarteroni2000numerical] Definition 10.3,
(10.84)): `Z(z) = ∑_{n ≥ 0} f(nΔt) z^{-n}`, a power series in `z⁻¹`; it converges for
`‖z‖ > limsup_n ‖f(nΔt)‖^{1/n}` (`summable_zTransform`). -/
noncomputable def zTransform (f : ℝ → ℂ) (Δt : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, f (n * Δt) * z⁻¹ ^ n

/-- **The Cauchy–Hadamard root test for the Z-transform**: the series `∑ f(nΔt) z^{-n}` converges
when `‖z‖ > R = limsup_n ‖f(nΔt)‖^{1/n}`, the limsup taken in `[0, ∞]` (as `ℝ≥0∞`, through
`‖·‖ₑ`) so that an unbounded sequence of roots gives `R = ∞` and no `z` — in `ℝ` the `limsup` of
an unbounded sequence is the junk value `0`, and the statement would be false. Choosing
`R < r < ‖z‖`, eventually `‖f(nΔt)‖ ≤ r^n`, and the terms are dominated by the geometric series
`(r/‖z‖)^n`. -/
theorem summable_zTransform {f : ℝ → ℂ} {Δt : ℝ} {z : ℂ}
    (hz : Filter.limsup (fun n : ℕ => ‖f (n * Δt)‖ₑ ^ (1 / (n : ℝ))) atTop < ‖z‖ₑ) :
    Summable fun n : ℕ => f (n * Δt) * z⁻¹ ^ n := by
  obtain ⟨r, hr, hrz⟩ := exists_between hz
  have hrtop : r ≠ ⊤ := (hrz.trans_le le_top).ne
  set ρ : ℝ := r.toReal with hρ
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hz0 : 0 < ‖z‖ := by
    have := ENNReal.toReal_strict_mono (enorm_ne_top) hrz
    rw [toReal_enorm] at this
    exact hρ0.trans_lt this
  have hρz : ρ < ‖z‖ := by
    have := ENNReal.toReal_strict_mono (enorm_ne_top) hrz
    rwa [toReal_enorm] at this
  have hev : ∀ᶠ n : ℕ in atTop, ‖f (n * Δt)‖ₑ ^ (1 / (n : ℝ)) < r :=
    Filter.eventually_lt_of_limsup_lt hr
  have hbound : ∀ᶠ n : ℕ in atTop, ‖f (n * Δt) * z⁻¹ ^ n‖ ≤ (ρ / ‖z‖) ^ n := by
    filter_upwards [hev, Filter.eventually_ge_atTop 1] with n hn hn1
    have hn0 : n ≠ 0 := by omega
    have hlt : ‖f (n * Δt)‖ ^ ((n : ℝ)⁻¹) < ρ := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity),
        ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hrtop] at *
      simpa [one_div] using hn
    have hle : ‖f (n * Δt)‖ ≤ ρ ^ n := by
      have := pow_le_pow_left₀ (by positivity) hlt.le n
      rwa [Real.rpow_inv_natCast_pow (norm_nonneg _) hn0] at this
    rw [norm_mul, norm_pow, norm_inv, div_pow, div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  refine Summable.of_norm_bounded_eventually (g := fun n => (ρ / ‖z‖) ^ n)
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hz0).mpr hρz)) ?_
  rwa [Nat.cofinite_eq_atTop]

/-- **The Z-transform is the discrete Laplace transform** under `z = e^{sΔt}`:
`Z(e^{sΔt}) = ∑_{n ≥ 0} f(nΔt) e^{-nsΔt}`, the series of `laplaceTransform_stepFun`. So under the
hypotheses of that theorem `ℒ[f₀](s) = ((1 − e^{-sΔt})/s) · Z(e^{sΔt})`. Erratum:
[quarteroni2000numerical] §10.11.4 prints the substitution as `z = e^{-sΔt}`; with
`Z(z) = ∑ f(nΔt) z^{-n}` and `Z^d(s) = ∑ f(nΔt) e^{-nsΔt}` it is `z = e^{sΔt}`. -/
theorem zTransform_eq_discreteLaplace (f : ℝ → ℂ) {Δt : ℝ} (s : ℂ) :
    zTransform f Δt (Complex.exp (s * Δt))
      = ∑' n : ℕ, f (n * Δt) * Complex.exp (-(n * s * Δt)) := by
  unfold zTransform
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
  congr 2
  ring
