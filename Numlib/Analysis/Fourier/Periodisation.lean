/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.Fourier.FourierIntegral

/-!
# Periodisation of an integrable function

The **periodisation** of a function $g \colon \mathbb{R} \to E$ at period $T > 0$ is the
$T$-periodic function $x \mapsto \sum_{n \in \mathbb{Z}} g(x + nT)$. Its integral over one period is
the integral of $g$ over the line. With a $T$-periodic weight, this gives the identity on which the
Fourier side of wavelet theory runs: the Fourier coefficients of the periodisation of $g$ are the
values of the Fourier transform $\hat{g}$ on the dual lattice,
$$\int_0^T e^{-2 \pi i n x / T} \sum_{k \in \mathbb{Z}} g(x + kT) \, dx = \hat{g}(n / T).$$
The module also proves the dual statement, by Poisson summation: the Fourier transform of a sampled
signal is the periodisation of the Fourier transform of the signal.

The identity is one step of the periodisation criterion for the orthonormality of the integer
translates of a function $\varphi \in L^2(\mathbb{R})$. With $g = |\hat{\varphi}|^2$, it identifies
the Fourier coefficients of $\sum_k |\hat{\varphi}(\cdot + k)|^2$ with the integrals
$\int_{\mathbb{R}} |\hat{\varphi}(\xi)|^2 e^{-2 \pi i n \xi} \, d\xi$. Two steps of that criterion
are not in this module: the identification of these integrals with the inner products
$\langle \varphi(\cdot - n), \varphi \rangle$, which is Plancherel's theorem together with the
translation rule for the $L^2$ Fourier transform; and the $L^1$ uniqueness theorem on the circle,
which says that a function whose Fourier coefficients are those of the constant $1$ equals $1$
almost everywhere.

## Main definitions

* `zmultiplesEquivInt`: the bijection $n \mapsto nT$ from $\mathbb{Z}$ onto the lattice
  $T \mathbb{Z}$.
* `periodise`: the periodisation $x \mapsto \sum_{n \in \mathbb{Z}} g(x + nT)$.

## Main results

* `integral_periodise`: $\int_{(0, T]} \sum_n g(x + nT) \, dx = \int_{\mathbb{R}} g$ for integrable
  $g$.
* `integral_mul_periodise`: the same identity with a bounded $T$-periodic weight, which passes
  through the sum.
* `integral_fourierChar_mul_periodise`: for $T = 1$, the Fourier coefficients of the periodisation
  of $g$ are the values $\hat{g}(n)$.
* `Real.tsum_fourierIntegral_sub_div_eq_tsum_mul`: the aliasing formula $\sum_j \hat{g}(\nu - j /
  \Delta t) = \Delta t \sum_k g(k \Delta t) e^{-2 \pi i \nu k \Delta t}$ of
  [quarteroni2000numerical], (10.82), for $g$ continuous with polynomial decay.

## Implementation notes

* The proof of `integral_periodise` is `MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum''` for
  the fundamental domain $(0, T]$ of the lattice $T \mathbb{Z}$, followed by
  `MeasureTheory.integral_tsum` to exchange the sum with the integral. The $L^1$ bound that the
  exchange needs is the same decomposition for the lower Lebesgue integral, which needs no
  integrability. The lattice is reindexed by $\mathbb{Z}$ through `zmultiplesEquivInt`.
* The aliasing formula is Mathlib's Poisson summation
  `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`, applied to the rescaled and modulated
  signal.
* Nothing in this module is specific to numerical analysis.
-/

noncomputable section

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For $T > 0$, the bijection $n \mapsto nT$ from $\mathbb{Z}$ onto the lattice
$T \mathbb{Z} = \{nT : n \in \mathbb{Z}\}$ of $\mathbb{R}$.

The lattice is `AddSubgroup.zmultiples T`. The bijection turns the sums over the lattice that
Mathlib's theorems on fundamental domains produce into sums over $\mathbb{Z}$. -/
def zmultiplesEquivInt {T : ℝ} (hT : 0 < T) : ℤ ≃ AddSubgroup.zmultiples T :=
  Equiv.ofBijective
    (fun n : ℤ => (⟨n • T, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩ :
      AddSubgroup.zmultiples T))
    ⟨fun a b hab => (zsmul_left_strictMono hT).injective (congrArg Subtype.val hab),
      fun y => by
        obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
        exact ⟨k, Subtype.ext hk⟩⟩

/-- For $T > 0$ and $n \in \mathbb{Z}$, the bijection sends $n$ to the real number $nT$. -/
@[simp]
theorem zmultiplesEquivInt_apply {T : ℝ} (hT : 0 < T) (n : ℤ) :
    ((zmultiplesEquivInt hT n : AddSubgroup.zmultiples T) : ℝ) = (n : ℝ) * T := by
  change n • T = _
  rw [zsmul_eq_mul]

/-- The **periodisation** of a function $g \colon \mathbb{R} \to E$ at period $T$: the function
$$x \mapsto \sum_{n \in \mathbb{Z}} g(x + nT).$$

The sum is a Lean `tsum`, so the value is $0$ at the points $x$ where the family $(g(x + nT))_n$
is not summable. For $T > 0$ and integrable $g$, the sum converges for almost every $x$, and the
periodisation is $T$-periodic. -/
def periodise (T : ℝ) (g : ℝ → E) (x : ℝ) : E := ∑' n : ℤ, g (x + n * T)

omit [NormedSpace ℝ E] in
/-- The defining formula of the periodisation: its value at $x$ is
$\sum_{n \in \mathbb{Z}} g(x + nT)$. -/
theorem periodise_apply (T : ℝ) (g : ℝ → E) (x : ℝ) :
    periodise T g x = ∑' n : ℤ, g (x + n * T) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- For $T > 0$, $n \in \mathbb{Z}$ and $x \in \mathbb{R}$, the translate of $x$ by the lattice
element of index $n$ is $x + nT$. Hence $g$ takes the value $g(x + nT)$ there. -/
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
/-- Let $T > 0$ and $g \colon \mathbb{R} \to E$. Then, for the lower Lebesgue integral of the
extended norm,
$$\sum_{n \in \mathbb{Z}} \int_{(0, T]} \|g(x + nT)\| \, dx = \int_{\mathbb{R}} \|g(x)\| \,
  dx.$$
This form of `integral_periodise` needs no integrability. -/
theorem tsum_setLIntegral_Ioc_enorm_add_mul {T : ℝ} (hT : 0 < T) (g : ℝ → E) :
    ∑' n : ℤ, ∫⁻ x in Ioc (0 : ℝ) T, ‖g (x + n * T)‖ₑ = ∫⁻ x, ‖g x‖ₑ := by
  rw [(isAddFundamentalDomain_Ioc_zero hT).lintegral_eq_tsum'' (fun x => ‖g x‖ₑ),
    ← (zmultiplesEquivInt hT).tsum_eq
      (fun u : AddSubgroup.zmultiples T => ∫⁻ x in Ioc (0 : ℝ) T, ‖g (u +ᵥ x)‖ₑ)]
  exact tsum_congr fun n => lintegral_congr fun x =>
    congrArg _ (vadd_zmultiplesEquivInt hT n x g).symm

/-- Let $T > 0$ and let $g \colon \mathbb{R} \to E$ be integrable, where $E$ is a real normed space.
Then the integral of the periodisation of $g$ over one period is the integral of $g$ over the
line:
$$\int_{(0, T]} \sum_{n \in \mathbb{Z}} g(x + nT) \, dx = \int_{\mathbb{R}} g(x) \, dx.$$
-/
theorem integral_periodise {T : ℝ} (hT : 0 < T) {g : ℝ → E} (hg : Integrable g) :
    ∫ x in Ioc (0 : ℝ) T, periodise T g x = ∫ x, g x := by
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (fun x : ℝ => g (x + n * T))
      (volume.restrict (Ioc (0 : ℝ) T)) := fun n =>
    (hg.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_right volume ((n : ℝ) * T))).restrict
  have hfin : ∑' n : ℤ, ∫⁻ x in Ioc (0 : ℝ) T, ‖g (x + n * T)‖ₑ ≠ ⊤ := by
    rw [tsum_setLIntegral_Ioc_enorm_add_mul hT g]
    exact hg.2.ne
  simp only [periodise_apply]
  rw [integral_tsum hmeas hfin,
    (isAddFundamentalDomain_Ioc_zero hT).integral_eq_tsum'' g hg,
    ← (zmultiplesEquivInt hT).tsum_eq
      (fun u : AddSubgroup.zmultiples T => ∫ x in Ioc (0 : ℝ) T, g (u +ᵥ x))]
  exact tsum_congr fun n => integral_congr_ae
    (Filter.Eventually.of_forall fun x => (vadd_zmultiplesEquivInt hT n x g).symm)

/-- Let $T > 0$, let $w \colon \mathbb{R} \to \mathbb{C}$ be $T$-periodic, almost everywhere
strongly measurable and bounded by a constant $C$, and let $g \colon \mathbb{R} \to \mathbb{C}$
be integrable. Then
$$\int_{(0, T]} w(x) \sum_{n \in \mathbb{Z}} g(x + nT) \, dx = \int_{\mathbb{R}} w(x) g(x) \,
  dx.$$

The weight passes through the sum. With $w(x) = e^{-2 \pi i n x / T}$, the identity computes the
Fourier coefficients of the periodisation of $g$ from $g$ itself. -/
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
/-- **The Fourier coefficients of the periodisation are the samples of the Fourier transform.** Let
$g \colon \mathbb{R} \to \mathbb{C}$ be integrable and let $n \in \mathbb{Z}$. Then
$$\int_{(0, 1]} e^{-2 \pi i x n} \sum_{k \in \mathbb{Z}} g(x + k) \, dx = \int_{\mathbb{R}}
  e^{-2 \pi i x n} g(x) \, dx,$$
and the right side is the Fourier transform $\hat{g}(n)$.

The exponential $e^{2 \pi i t}$ is `Real.fourierChar t`. -/
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

/-- **The Fourier transform of a sampled signal is the periodisation of the Fourier transform.** Let
$g \colon \mathbb{R} \to \mathbb{C}$ be continuous with $g(x) = O(|x|^{-b})$ as $|x| \to \infty$
for some $b > 1$, let $\Delta t > 0$, and let $\nu \in \mathbb{R}$ be a frequency at which the
family $(\hat{g}(\nu - j / \Delta t))_{j \in \mathbb{Z}}$ is summable. Then
$$\sum_{j \in \mathbb{Z}} \hat{g}\Bigl(\nu - \frac{j}{\Delta t}\Bigr) = \Delta t \sum_{k \in
  \mathbb{Z}} g(k \Delta t) \, e^{-2 \pi i \nu k \Delta t}.$$
This is the aliasing formula (10.82) of [quarteroni2000numerical].

The right side is the trapezoidal sum that approximates $\hat{g}(\nu)$. The left side is the
periodisation of $\hat{g}$ with period $1 / \Delta t$, evaluated at $\nu$. For $g$ supported in
$[0, T_0]$, the right side is the finite trapezoidal sum of [quarteroni2000numerical]. The
Fourier transform $\hat{g}$ is `𝓕 g`. The proof applies the Poisson summation formula
`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable` at $x = 0$ to the rescaled and modulated
signal $h(t) = \Delta t \, e^{-2 \pi i t \nu \Delta t} g(\Delta t \, t)$. Its transform is
$\hat{h}(n) = \hat{g}(\nu + n / \Delta t)$, by the modulation and scaling rules of
`Numlib.Analysis.Fourier.FourierIntegral`. -/
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
