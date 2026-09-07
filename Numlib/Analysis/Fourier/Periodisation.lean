import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

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
