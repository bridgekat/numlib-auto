import Numlib.Analysis.Calculus.Periodic
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Sobolev.Periodic

/-!
# Smooth periodic functions and their Fourier coefficients

The periodic Sobolev space `PeriodicSobolev s` of `Numlib/Analysis/Sobolev/Periodic` is a space of
coefficient sequences. This file is the bridge from the *function* side: a `2π`-periodic function
`f : ℝ → ℂ` of class `C^s` has Fourier coefficients
`f̂_n = (1/2π) ∫_0^{2π} f(x) e^{-inx} dx` — Mathlib's `fourierCoeff` of the lift `hf.lift` of `f` to
`AddCircle (2π)` — and

`∑_n |n|^{2k} |f̂_n|² = (1/2π) ‖f^{(k)}‖²_{L²(0,2π)}` for every `k ≤ s`

(`hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq`), because differentiation multiplies `f̂_n` by
`i n` (`fourierCoeff_lift_deriv`, from Mathlib's `fourierCoeffOn_of_hasDerivAt` and the
periodicity `f(2π) = f(0)`) and Parseval's identity holds for the continuous function `f^{(k)}`.
Hence the coefficient sequence lies in `PeriodicSobolev s`: that element is
`PeriodicSobolev.ofSmooth hf hd`, and its two properties are

* `PeriodicSobolev.eval_ofSmooth`: the sum of its series is `f` (for `s ≥ 1`), and
* `PeriodicSobolev.norm_ofSmooth_le`: `‖φ‖ ≤ (2π)^{-1/2} ‖f‖_s` with the classical norm
  `‖f‖²_s = ∑_{k ≤ s} ‖f^{(k)}‖²_{L²(0,2π)}` (`PeriodicSobolev.derivNormSq`).

Together with `PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le` this gives the spectral
accuracy of the trapezoidal rule, and with the aliasing bounds of `Numlib/Analysis/Fourier/Aliasing`
the error estimates for trigonometric interpolation, in the classical norm of
[quarteroni2000numerical] §10.9. The identification of the coefficient norm with the classical
norm is [han2009theoretical] Theorem 7.5.2, here in the form
`hasSum_sum_abs_pow_mul_norm_fourierCoeff_lift_sq`.

The period is fixed at `2π`, the period of both books; the general period `T` only changes the
constants (`f̂'_n = (2π i n / T) f̂_n`).
-/

open AddCircle Complex MeasureTheory
open scoped Real

/-! ### Derivatives of periodic functions -/

/-! ### The Fourier coefficients of the derivatives -/

section Deriv

variable {f : ℝ → ℂ}

/-- **Differentiation multiplies the `n`-th Fourier coefficient by `i n`**: for a `2π`-periodic
`C¹` function, `(f')^_n = i n f̂_n`. At `n ≠ 0` this is Mathlib's `fourierCoeffOn_of_hasDerivAt`
with the boundary term killed by `f(2π) = f(0)`; at `n = 0` it is the fundamental theorem of
calculus over one period. -/
theorem fourierCoeff_lift_deriv (hf : Function.Periodic f (2 * π)) (hd : ContDiff ℝ 1 f)
    (n : ℤ) :
    fourierCoeff hf.deriv.lift n = (I * n) * fourierCoeff hf.lift n := by
  have hcont : Continuous (deriv f) := hd.continuous_deriv le_rfl
  have hint : IntervalIntegrable (deriv f) volume 0 (0 + 2 * π) :=
    hcont.intervalIntegrable _ _
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Int.cast_zero, mul_zero, zero_mul, fourierCoeff_eq_intervalIntegral _ 0 0]
    simp only [neg_zero, fourier_zero, one_smul]
    have : ∫ x in (0 : ℝ)..0 + 2 * π, hf.deriv.lift (x : AddCircle (2 * π))
        = ∫ x in (0 : ℝ)..0 + 2 * π, deriv f x :=
      intervalIntegral.integral_congr fun x _ => Function.Periodic.lift_coe _ _
    rw [this, intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hd.differentiable one_ne_zero x) hint, hf 0, sub_self, smul_zero]
  · rw [Function.Periodic.fourierCoeff_lift_eq_fourierCoeffOn,
      Function.Periodic.fourierCoeff_lift_eq_fourierCoeffOn,
      fourierCoeffOn_of_hasDerivAt (lt_add_of_pos_right 0 Real.two_pi_pos) hn
        (fun x _ => (hd.differentiable one_ne_zero x).hasDerivAt) hint, hf 0, sub_self, mul_zero,
      zero_sub]
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring

/-- The `k`-th derivative multiplies the `n`-th Fourier coefficient by `(i n)^k`. -/
theorem fourierCoeff_lift_iteratedDeriv (hf : Function.Periodic f (2 * π)) {s : ℕ}
    (hd : ContDiff ℝ s f) {k : ℕ} (hk : k ≤ s) (n : ℤ) :
    fourierCoeff (hf.iteratedDeriv k).lift n = (I * n) ^ k * fourierCoeff hf.lift n := by
  induction k with
  | zero => simp only [pow_zero, one_mul]; rfl
  | succ k ih =>
    have hd1 : ContDiff ℝ 1 (iteratedDeriv k f) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv' 1 k
        (hd.of_le (by exact_mod_cast (show 1 + k ≤ s by omega)))
    have heq : (hf.iteratedDeriv (k + 1)).lift = (hf.iteratedDeriv k).deriv.lift :=
      Function.Periodic.lift_congr iteratedDeriv_succ _ _
    rw [heq, fourierCoeff_lift_deriv (hf.iteratedDeriv k) hd1 n, ih (by omega), pow_succ]
    ring

end Deriv

namespace PeriodicSobolev

variable {f : ℝ → ℂ}

/-! ### The classical norm -/

/-- The classical periodic Sobolev norm, squared: `‖f‖²_s = ∑_{k ≤ s} ‖f^{(k)}‖²_{L²(0,2π)}`, the
norm `‖·‖_s` of [quarteroni2000numerical] §10.9 and the `‖·‖_{H^k}` of [han2009theoretical]
Theorem 7.5.2. -/
noncomputable def derivNormSq (s : ℕ) (f : ℝ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range (s + 1), ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2

/-- The classical norm squared is nonnegative. -/
theorem derivNormSq_nonneg (s : ℕ) (f : ℝ → ℂ) : 0 ≤ derivNormSq s f :=
  Finset.sum_nonneg fun _ _ => intervalIntegral.integral_nonneg Real.two_pi_pos.le fun x _ => by
    positivity

/-- Each derivative's `L²` norm is at most the classical norm. -/
theorem intervalIntegral_norm_iteratedDeriv_sq_le_derivNormSq {s k : ℕ} (hk : k ≤ s)
    (f : ℝ → ℂ) :
    ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2 ≤ derivNormSq s f :=
  Finset.single_le_sum (f := fun k => ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2)
    (fun _ _ => intervalIntegral.integral_nonneg Real.two_pi_pos.le fun x _ => by positivity)
    (Finset.mem_range.mpr (by omega))

/-! ### Parseval for the derivatives -/

/-- **Parseval for the `k`-th derivative**: `∑_n |n|^{2k} |f̂_n|² = (1/2π) ‖f^{(k)}‖²_{L²(0,2π)}`
for a `2π`-periodic `f` of class `C^s` and `k ≤ s`. -/
theorem hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq (hf : Function.Periodic f (2 * π)) {s : ℕ}
    (hd : ContDiff ℝ s f) {k : ℕ} (hk : k ≤ s) :
    HasSum (fun n : ℤ => |(n : ℝ)| ^ (2 * k) * ‖fourierCoeff hf.lift n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2) := by
  have hcont : Continuous (iteratedDeriv k f) :=
    hd.continuous_iteratedDeriv k (by exact_mod_cast hk)
  have h := hasSum_sq_fourierCoeff_of_continuous' ((hf.iteratedDeriv k).continuous_lift hcont)
  have hint : ∫ x in (0 : ℝ)..2 * π, ‖(hf.iteratedDeriv k).lift (x : AddCircle (2 * π))‖ ^ 2
      = ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2 :=
    intervalIntegral.integral_congr fun x _ => by rw [Function.Periodic.lift_coe]
  rw [hint] at h
  refine h.congr_fun fun n => ?_
  rw [fourierCoeff_lift_iteratedDeriv hf hd hk, norm_mul, norm_pow, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_intCast, mul_pow, ← pow_mul, mul_comm k 2]

/-- **The classical norm on the Fourier side** ([han2009theoretical] Theorem 7.5.2):
`(1/2π) ‖f‖²_s = ∑_n (∑_{k ≤ s} |n|^{2k}) |f̂_n|²`. -/
theorem hasSum_sum_abs_pow_mul_norm_fourierCoeff_lift_sq (hf : Function.Periodic f (2 * π))
    {s : ℕ} (hd : ContDiff ℝ s f) :
    HasSum (fun n : ℤ =>
        (∑ k ∈ Finset.range (s + 1), |(n : ℝ)| ^ (2 * k)) * ‖fourierCoeff hf.lift n‖ ^ 2)
      ((2 * π)⁻¹ * derivNormSq s f) := by
  rw [derivNormSq, Finset.mul_sum]
  refine (hasSum_sum fun k hk => hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).congr_fun fun n => ?_
  rw [Finset.sum_mul]

/-! ### The coefficient sequence as an element of `PeriodicSobolev s` -/

/-- The weight squared is dominated by `1 + |m|^{2s}`, so the weighted norm is dominated by the
`L²` norms of `f` and of `f^{(s)}`. -/
private theorem weight_mul_norm_sq_le (s : ℕ) (m : ℤ) (a : ℂ) :
    (periodicSobolevWeight s m * ‖a‖) ^ 2 ≤ ‖a‖ ^ 2 + |(m : ℝ)| ^ (2 * s) * ‖a‖ ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [periodicSobolevWeight_zero, one_mul]
    nlinarith [sq_nonneg ‖a‖, pow_nonneg (abs_nonneg ((0 : ℤ) : ℝ)) (2 * s)]
  · rw [mul_pow, periodicSobolevWeight_sq _ hm,
      show (2 : ℝ) * (s : ℝ) = ((2 * s : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    nlinarith [sq_nonneg ‖a‖]

/-- The weighted coefficient family of a `C^s` function is square summable: the weight squared is
at most `1 + |m|^{2s}`, and Parseval at orders `0` and `s` sums both parts. -/
theorem summable_weight_mul_norm_fourierCoeff_lift_sq (hf : Function.Periodic f (2 * π)) {s : ℕ}
    (hd : ContDiff ℝ s f) :
    Summable fun m : ℤ => (periodicSobolevWeight s m * ‖fourierCoeff hf.lift m‖) ^ 2 := by
  have h0 := hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd (Nat.zero_le s)
  have hs := hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd (le_refl s)
  simp only [mul_zero, pow_zero, one_mul] at h0
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => weight_mul_norm_sq_le s m _) (h0.summable.add hs.summable)

/-- **The coefficient sequence of a smooth periodic function.** A `2π`-periodic `f` of class `C^s`
has Fourier coefficients in `PeriodicSobolev s`; this is the bridge from the function side to the
coefficient side, with `eval_ofSmooth` and `norm_ofSmooth_le` as its two properties. -/
noncomputable def ofSmooth (hf : Function.Periodic f (2 * π)) {s : ℕ} (hd : ContDiff ℝ s f) :
    PeriodicSobolev s :=
  ofCoeff s (fourierCoeff hf.lift) (memℓp_two_iff.2
    ((summable_weight_mul_norm_fourierCoeff_lift_sq hf hd).congr fun m => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (periodicSobolevWeight_pos _ m).le]))

/-- The coefficients of `ofSmooth hf hd` are the Fourier coefficients of `f`. -/
@[simp]
theorem coeff_ofSmooth (hf : Function.Periodic f (2 * π)) {s : ℕ} (hd : ContDiff ℝ s f) :
    coeff (ofSmooth hf hd) = fourierCoeff hf.lift :=
  coeff_ofCoeff _ _ _

/-- `‖φ‖² ≤ (1/2π) (‖f‖²_{L²} + ‖f^{(s)}‖²_{L²})` for the coefficient sequence of a `C^s`
function: the weight `w_s(m)²` is at most `1 + |m|^{2s}`. -/
theorem norm_ofSmooth_sq_le (hf : Function.Periodic f (2 * π)) {s : ℕ} (hd : ContDiff ℝ s f) :
    ‖ofSmooth hf hd‖ ^ 2 ≤ (2 * π)⁻¹ * ((∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2)
      + ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv s f x‖ ^ 2) := by
  have h0 := hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd (Nat.zero_le s)
  have hs := hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd (le_refl s)
  simp only [mul_zero, pow_zero, one_mul, iteratedDeriv_zero] at h0
  have hn := hasSum_norm_sq (ofSmooth hf hd)
  simp only [coeff_ofSmooth] at hn
  rw [mul_add]
  exact hasSum_le (fun m => weight_mul_norm_sq_le s m _) hn (h0.add hs)

/-- **The bridge to the classical norm**: `‖φ‖ ≤ (2π)^{-1/2} ‖f‖_s` with
`‖f‖²_s = ∑_{k ≤ s} ‖f^{(k)}‖²_{L²(0,2π)}`, for `s ≥ 1`. -/
theorem norm_ofSmooth_le (hf : Function.Periodic f (2 * π)) {s : ℕ} (hs : 1 ≤ s)
    (hd : ContDiff ℝ s f) :
    ‖ofSmooth hf hd‖ ≤ (√(2 * π))⁻¹ * √(derivNormSq s f) := by
  have hsq : ‖ofSmooth hf hd‖ ^ 2 ≤ (2 * π)⁻¹ * derivNormSq s f := by
    refine (norm_ofSmooth_sq_le hf hd).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [derivNormSq]
    have := Finset.add_le_sum (f := fun k => ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2)
      (s := Finset.range (s + 1)) (fun _ _ => intervalIntegral.integral_nonneg Real.two_pi_pos.le
        fun x _ => by positivity) (Finset.mem_range.mpr (by omega))
      (Finset.mem_range.mpr (by omega)) (show (0 : ℕ) ≠ s by omega)
    simpa only [iteratedDeriv_zero] using this
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hsq

/-- The sum of the Fourier series of a `C^s` function, `s ≥ 1`, is the function itself: the series
converges absolutely (`PeriodicSobolev.summable_coeff` at `s > 1/2`), hence pointwise to `f` by
`has_pointwise_sum_fourier_series_of_summable`. -/
theorem eval_ofSmooth (hf : Function.Periodic f (2 * π)) {s : ℕ} (hs : 1 ≤ s)
    (hd : ContDiff ℝ s f) : eval (2 * π) (ofSmooth hf hd) = f := by
  have hsum : Summable (fourierCoeff hf.lift) := by
    have := summable_coeff (s := (s : ℝ)) (by
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs
      linarith) (ofSmooth hf hd)
    rwa [coeff_ofSmooth] at this
  funext x
  rw [eval_eq_tsum_smul_fourier, coeff_ofSmooth]
  have h := (has_pointwise_sum_fourier_series_of_summable
    (f := ⟨hf.lift, hf.continuous_lift hd.continuous⟩) hsum (x : AddCircle (2 * π))).tsum_eq
  exact h.trans (Function.Periodic.lift_coe hf x)

end PeriodicSobolev
