import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.Fourier.FourierIntegral

/-!
# Periodisation of an integrable function

Upstreaming candidate: nothing here is specific to numerical analysis.

The **periodisation** of `g : ℝ → E` at period `T` is `Σ_{n ∈ ℤ} g (x + n T)`, a `T`-periodic
function whose integral over one period is the integral of `g` over the line.  Weighting by a
`T`-periodic factor gives the identity the Fourier side of wavelet theory runs on: the Fourier
coefficients of the periodisation of `g` are the values of the Fourier transform of `g` on the dual
lattice,

`∫_0^T 𝐞[-n x / T] (Σ_k g (x + k T)) dx = ĝ (n / T)`.

This is one step of the periodisation criterion for orthonormality of the integer translates of a
`φ ∈ L²(ℝ)`: with `g = |φ̂|²` it identifies the Fourier coefficients of `∑_k |φ̂(· + k)|²` with the
integrals `∫_ℝ |φ̂(ξ)|² 𝐞[-nξ] dξ`.  Two steps of that criterion are *not* here: identifying those
integrals with the inner products `⟪φ(· - n), φ⟫`, which is Plancherel together with the
translation rule for the `L²` Fourier transform, and the `L¹` uniqueness theorem on the circle,
that a function whose Fourier coefficients are those of the constant `1` equals `1` almost
everywhere.

## Main statements

* `integral_periodise`: `∫_{(0, T]} periodise T g = ∫_ℝ g` for integrable `g`.
* `integral_mul_periodise`: the same with a bounded `T`-periodic weight, which passes through the
  sum.
* `integral_fourierChar_mul_periodise`: the Fourier-coefficient form, `T = 1`.
* `Real.tsum_fourierIntegral_sub_div_eq_tsum_mul`: the dual statement, **the transform of a
  sampled signal is the periodisation of its transform** — for `g` continuous with polynomial
  decay, `∑_j ĝ(ν − j/Δt) = Δt ∑_k g(k Δt) e^{−2πiνkΔt}`, the aliasing formula of
  [quarteroni2000numerical] (10.82), from Mathlib's Poisson summation
  `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable` applied to the rescaled, modulated signal.

## Implementation notes

The proof is `MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum''` for the fundamental domain
`Ioc 0 T` of the lattice `T ℤ`, followed by `MeasureTheory.integral_tsum` to exchange the sum with
the integral; the `L¹` bound the exchange needs is the same decomposition for `lintegral`, which
needs no integrability.  The reindexing `ℤ ≃ T ℤ` is `zmultiplesEquivInt`.
-/

noncomputable section

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lattice `T ℤ ⊆ ℝ` is indexed by `ℤ`, for `T > 0`. -/
def zmultiplesEquivInt {T : ℝ} (hT : 0 < T) : ℤ ≃ AddSubgroup.zmultiples T :=
  Equiv.ofBijective
    (fun n : ℤ => (⟨n • T, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩ :
      AddSubgroup.zmultiples T))
    ⟨fun a b hab => (zsmul_left_strictMono hT).injective (congrArg Subtype.val hab),
      fun y => by
        obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
        exact ⟨k, Subtype.ext hk⟩⟩

@[simp]
theorem zmultiplesEquivInt_apply {T : ℝ} (hT : 0 < T) (n : ℤ) :
    ((zmultiplesEquivInt hT n : AddSubgroup.zmultiples T) : ℝ) = (n : ℝ) * T := by
  change n • T = _
  rw [zsmul_eq_mul]

/-- The **periodisation** of `g` at period `T`: the `T`-periodic function `∑_{n ∈ ℤ} g (x + n T)`.
The sum converges for almost every `x` when `g` is integrable, and is `0` by convention where it
does not. -/
def periodise (T : ℝ) (g : ℝ → E) (x : ℝ) : E := ∑' n : ℤ, g (x + n * T)

omit [NormedSpace ℝ E] in
theorem periodise_apply (T : ℝ) (g : ℝ → E) (x : ℝ) :
    periodise T g x = ∑' n : ℤ, g (x + n * T) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem vadd_zmultiplesEquivInt {T : ℝ} (hT : 0 < T) (n : ℤ) (x : ℝ) (g : ℝ → E) :
    g ((zmultiplesEquivInt hT n) +ᵥ x) = g (x + (n : ℝ) * T) := by
  congr 1
  change ((zmultiplesEquivInt hT n : AddSubgroup.zmultiples T) : ℝ) + x = _
  rw [zmultiplesEquivInt_apply]
  ring

private theorem isAddFundamentalDomain_Ioc_zero {T : ℝ} (hT : 0 < T) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples T) (Ioc (0 : ℝ) T) volume := by
  simpa using isAddFundamentalDomain_Ioc hT 0

omit [NormedSpace ℝ E] in
private theorem lintegral_periodise_enorm {T : ℝ} (hT : 0 < T) (g : ℝ → E) :
    ∑' n : ℤ, ∫⁻ x in Ioc (0 : ℝ) T, ‖g (x + n * T)‖ₑ = ∫⁻ x, ‖g x‖ₑ := by
  rw [(isAddFundamentalDomain_Ioc_zero hT).lintegral_eq_tsum'' (fun x => ‖g x‖ₑ),
    ← (zmultiplesEquivInt hT).tsum_eq
      (fun u : AddSubgroup.zmultiples T => ∫⁻ x in Ioc (0 : ℝ) T, ‖g (u +ᵥ x)‖ₑ)]
  exact tsum_congr fun n => lintegral_congr fun x =>
    congrArg _ (vadd_zmultiplesEquivInt hT n x g).symm

/-- The integral of the periodisation of `g` over one period is the integral of `g` over `ℝ`. -/
theorem integral_periodise {T : ℝ} (hT : 0 < T) {g : ℝ → E} (hg : Integrable g) :
    ∫ x in Ioc (0 : ℝ) T, periodise T g x = ∫ x, g x := by
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (fun x : ℝ => g (x + n * T))
      (volume.restrict (Ioc (0 : ℝ) T)) := fun n =>
    (hg.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_right volume ((n : ℝ) * T))).restrict
  have hfin : ∑' n : ℤ, ∫⁻ x in Ioc (0 : ℝ) T, ‖g (x + n * T)‖ₑ ≠ ⊤ := by
    rw [lintegral_periodise_enorm hT g]
    exact hg.2.ne
  simp only [periodise_apply]
  rw [integral_tsum hmeas hfin,
    (isAddFundamentalDomain_Ioc_zero hT).integral_eq_tsum'' g hg,
    ← (zmultiplesEquivInt hT).tsum_eq
      (fun u : AddSubgroup.zmultiples T => ∫ x in Ioc (0 : ℝ) T, g (u +ᵥ x))]
  exact tsum_congr fun n => integral_congr_ae
    (Filter.Eventually.of_forall fun x => (vadd_zmultiplesEquivInt hT n x g).symm)

/-- The periodisation identity with a bounded, `T`-periodic weight: the weight passes through the
sum, so this computes the Fourier coefficients of `periodise T g` from `g` itself. -/
theorem integral_mul_periodise {T : ℝ} (hT : 0 < T) {w g : ℝ → ℂ} (hw : Function.Periodic w T)
    (hwm : AEStronglyMeasurable w volume) {C : ℝ} (hwb : ∀ x, ‖w x‖ ≤ C) (hg : Integrable g) :
    ∫ x in Ioc (0 : ℝ) T, w x * periodise T g x = ∫ x, w x * g x := by
  have hwg : Integrable fun x => w x * g x :=
    hg.bdd_mul hwm (Filter.Eventually.of_forall hwb)
  have hkey : ∀ x : ℝ, periodise T (fun y => w y * g y) x = w x * periodise T g x := by
    intro x
    rw [periodise_apply, periodise_apply, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [hw.int_mul n x]
  simpa only [hkey] using integral_periodise hT hwg

open FourierTransform in
/-- **The Fourier coefficients of the periodisation are the samples of the Fourier transform.**
For `g` integrable on `ℝ`, the `n`-th Fourier coefficient of the `1`-periodisation of `g` is
`ĝ(n)`. -/
theorem integral_fourierChar_mul_periodise {g : ℝ → ℂ} (hg : Integrable g) (n : ℤ) :
    ∫ x in Ioc (0 : ℝ) 1, (𝐞 (-(x * n)) : ℂ) * periodise 1 g x
      = ∫ x : ℝ, (𝐞 (-(x * n)) : ℂ) * g x := by
  have hchar : ∀ m : ℤ, ((𝐞 (m : ℝ) : Circle) : ℂ) = 1 := by
    intro m
    rw [Real.fourierChar_apply,
      show ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I
          = (m : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I m
  have hper : Function.Periodic (fun x : ℝ => ((𝐞 (-(x * n)) : Circle) : ℂ)) 1 := by
    intro x
    simp only
    rw [show -((x + 1) * (n : ℝ)) = -(x * n) + ((-n : ℤ) : ℝ) by push_cast; ring,
      AddChar.map_add_eq_mul, Circle.coe_mul, hchar (-n), mul_one]
  have hcont : Continuous fun x : ℝ => ((𝐞 (-(x * n)) : Circle) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  exact integral_mul_periodise one_pos hper hcont.aestronglyMeasurable (C := 1)
    (fun x => le_of_eq (Circle.norm_coe _)) hg

/-! ### The transform of a sampled signal -/

namespace Real

open Asymptotics Filter FourierTransform

/-- **The transform of a sampled signal is the periodisation of its transform**
([quarteroni2000numerical] (10.82)). For `g : ℝ → ℂ` continuous with `g = O(|x|^{-b})` at
infinity for some `b > 1`, a sampling step `Δt > 0` and a frequency `ν` at which the periodised
transform `∑_j 𝓕 g (ν − j/Δt)` converges absolutely,

`∑' j : ℤ, 𝓕 g (ν − j / Δt) = Δt * ∑' k : ℤ, g (k Δt) * exp (−2πi ν k Δt)`:

the trapezoidal sum `Δt ∑_k g (k Δt) e^{−2πiνkΔt}` approximating `𝓕 g ν` is the periodic
repetition of `𝓕 g` with period `1/Δt`, that is `periodise (1/Δt) (𝓕 g) ν` — for a `g` supported in
`[0, T₀]` the right side is the finite trapezoidal sum of the textbook. Poisson summation
(`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`) at `x = 0` for the rescaled and modulated
signal `h t = Δt · 𝐞 (−t ν Δt) · g (Δt t)`, whose transform is `𝓕 h n = 𝓕 g (ν + n/Δt)` by the
modulation and scaling rules of `Numlib/Analysis/Fourier/FourierIntegral`. -/
theorem tsum_fourierIntegral_sub_div_eq_tsum_mul {g : ℝ → ℂ} (hg : Continuous g) {b : ℝ}
    (hb : 1 < b) (hdecay : g =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b)) {Δt : ℝ} (hΔt : 0 < Δt)
    {ν : ℝ} (hsum : Summable fun j : ℤ => 𝓕 g (ν - j / Δt)) :
    ∑' j : ℤ, 𝓕 g (ν - j / Δt)
      = Δt * ∑' k : ℤ, g (k * Δt) * Complex.exp (-(2 * π * ν * k * Δt) * Complex.I) := by
  -- the rescaled, modulated signal
  set h : ℝ → ℂ := fun t => Δt * ((𝐞 (-(t * (ν * Δt))) : ℂ) * g (Δt * t)) with hh
  have hcont : Continuous h := by
    refine continuous_const.mul (Continuous.mul ?_ (hg.comp (continuous_const.mul continuous_id)))
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  -- its Fourier transform is the shifted, rescaled transform of `g`
  have hF : ∀ n : ℤ, 𝓕 h n = 𝓕 g (ν + n / Δt) := by
    intro n
    have h1 : h = fun t => (Δt : ℂ) • ((𝐞 (-(t * (ν * Δt))) : ℂ) • (fun u => g (Δt * u)) t) := by
      funext t
      simp only [hh, smul_eq_mul]
    rw [h1, fourierIntegral_const_smul, fourierIntegral_fourierChar_mul,
      fourierIntegral_comp_mul_left hΔt.ne', abs_of_pos hΔt]
    rw [show ((n : ℝ) + ν * Δt) / Δt = ν + n / Δt by
      rw [add_div, mul_div_cancel_right₀ ν hΔt.ne', add_comm]]
    rw [smul_eq_mul, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hΔt.ne', Complex.ofReal_one, one_mul]
  -- decay of `h`
  have hdecay' : h =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b) := by
    have htend : Filter.Tendsto (fun t : ℝ => Δt * t) (cocompact ℝ) (cocompact ℝ) :=
      (Homeomorph.mulLeft₀ Δt hΔt.ne').isClosedEmbedding.tendsto_cocompact
    have h1 : (fun t => g (Δt * t)) =O[cocompact ℝ] fun t : ℝ => |Δt| ^ (-b) * |t| ^ (-b) := by
      refine (hdecay.comp_tendsto htend).trans
        (IsBigO.of_bound' (Filter.Eventually.of_forall fun t => ?_))
      simp only [Function.comp_apply, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
        norm_mul, Real.norm_eq_abs, le_refl]
    have h2 : (fun t : ℝ => (Δt : ℂ) * (𝐞 (-(t * (ν * Δt))) : ℂ)) =O[cocompact ℝ]
        fun _ : ℝ => (1 : ℝ) := by
      refine IsBigO.of_bound Δt (Filter.Eventually.of_forall fun t => ?_)
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hΔt, norm_one, mul_one]
    have h3 : h =O[cocompact ℝ] fun x : ℝ => |Δt| ^ (-b) * |x| ^ (-b) :=
      (h2.mul h1).congr (fun t => by simp only [hh]; exact mul_assoc _ _ _) fun x => one_mul _
    exact h3.of_const_mul_right
  -- summability of the transform of `h`
  have hsum' : Summable fun n : ℤ => 𝓕 h n := by
    simp only [hF]
    have := (Equiv.neg ℤ).summable_iff.mpr hsum
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
    ring_nf
  -- Poisson summation at `x = 0`
  have hpoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont hb hdecay' hsum' 0
  simp only [zero_add, hF, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hpoisson
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => 𝓕 g (ν + n / Δt))] at hpoisson
  simp only [Equiv.neg_apply, Int.cast_neg] at hpoisson
  rw [← tsum_mul_left]
  rw [show (fun j : ℤ => 𝓕 g (ν - j / Δt)) = fun j : ℤ => 𝓕 g (ν + -j / Δt) from
    funext fun j => by rw [neg_div, ← sub_eq_add_neg], ← hpoisson]
  refine tsum_congr fun n => ?_
  simp only [hh, Real.fourierChar_apply]
  rw [mul_comm (Δt : ℝ) (n : ℝ)]
  push_cast
  ring_nf

end Real
