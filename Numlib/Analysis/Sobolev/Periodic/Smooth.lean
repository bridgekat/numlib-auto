/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.Periodic
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Sobolev.Periodic

/-!
# Smooth periodic functions and their Fourier coefficients

The periodic Sobolev space $H^s$ of `Numlib.Analysis.Sobolev.Periodic` is a space of coefficient
sequences. This module connects it with functions. A $2\pi$-periodic function
$f : \mathbb{R} \to \mathbb{C}$ has the Fourier coefficients
$$\hat f_n = \frac{1}{2\pi} \int_0^{2\pi} f(x) e^{-inx} \, dx, \qquad n \in \mathbb{Z}.$$
If $f$ is of class $C^s$, then for every $k \le s$
$$\sum_{n \in \mathbb{Z}} |n|^{2k} |\hat f_n|^2 = \frac{1}{2\pi} \|f^{(k)}\|_{L^2(0, 2\pi)}^2,$$
because differentiation multiplies $\hat f_n$ by $in$ and Parseval's identity holds for the
continuous function $f^{(k)}$. Hence the coefficient sequence of $f$ lies in $H^s$. This element is
`PeriodicSobolev.ofSmooth`. For $s \ge 1$ the sum of its series is $f$, and its norm is at most
$(2\pi)^{-1/2} \|f\|_s$ for the classical norm $\|f\|_s^2 = \sum_{k \le s} \|f^{(k)}\|_{L^2(0,
2\pi)}^2$.

With `PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le`, this gives the spectral accuracy
of the trapezoidal rule for smooth periodic functions. With the aliasing bounds of
`Numlib.Analysis.Fourier.Aliasing`, it gives the error estimates for trigonometric interpolation in
the classical norm of [quarteroni2000numerical], §10.9. The expression of the classical norm through
the Fourier coefficients is Theorem 7.5.2 of [han2009theoretical].

## Main definitions

* `PeriodicSobolev.derivNormSq`: the square $\|f\|_s^2 = \sum_{k \le s} \|f^{(k)}\|_{L^2(0,
  2\pi)}^2$ of the classical periodic Sobolev norm.
* `PeriodicSobolev.ofSmooth`: the coefficient sequence of a $2\pi$-periodic $C^s$ function, as an
  element of $H^s$.

## Main results

* `fourierCoeff_lift_deriv`: for a $2\pi$-periodic $C^1$ function, $\widehat{f'}_n = in \hat f_n$.
* `fourierCoeff_lift_iteratedDeriv`: for a $2\pi$-periodic $C^s$ function and $k \le s$,
  $\widehat{f^{(k)}}_n = (in)^k \hat f_n$.
* `PeriodicSobolev.hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq`: Parseval's identity for the $k$-th
  derivative, $\sum_n |n|^{2k} |\hat f_n|^2 = (2\pi)^{-1} \|f^{(k)}\|_{L^2(0, 2\pi)}^2$.
* `PeriodicSobolev.hasSum_sum_abs_pow_mul_norm_fourierCoeff_lift_sq`: the classical norm through the
  Fourier coefficients, Theorem 7.5.2 of [han2009theoretical].
* `PeriodicSobolev.eval_ofSmooth`: for $s \ge 1$, the sum of the Fourier series of $f$ is $f$.
* `PeriodicSobolev.norm_ofSmooth_le`: for $s \ge 1$, the norm of the coefficient sequence in $H^s$
  is at most $(2\pi)^{-1/2} \|f\|_s$.

## Implementation notes

* The Fourier coefficients $\hat f_n$ are Mathlib's `fourierCoeff` of the lift `hf.lift` of $f$ to
  `AddCircle (2 * π)`.
* The period is fixed at $2\pi$, the period of both [quarteroni2000numerical] and
  [han2009theoretical]. A general period $T$ changes only the constants:
  $\widehat{f'}_n = (2\pi i n / T) \hat f_n$.
-/

open AddCircle Complex MeasureTheory
open scoped Real

/-! ### The Fourier coefficients of the derivatives -/

section Deriv

variable {f : ℝ → ℂ}

/-- **Differentiation multiplies the $n$-th Fourier coefficient by $in$.** Let
$f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class $C^1$. Then for every
$n \in \mathbb{Z}$,
$$\widehat{f'}_n = i n \, \hat f_n,$$
where $\hat f_n$ is the $n$-th Fourier coefficient of the lift of $f$ to the circle of
circumference $2\pi$.

For $n \ne 0$ this is Mathlib's `fourierCoeffOn_of_hasDerivAt`, where the boundary term vanishes
because $f(2\pi) = f(0)$. For $n = 0$ it is the fundamental theorem of calculus over one period. -/
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

/-- Let $f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class $C^s$, and let $k \le s$.
Then for every $n \in \mathbb{Z}$,
$$\widehat{f^{(k)}}_n = (i n)^k \, \hat f_n.$$
-/
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

/-- The square of the **classical periodic Sobolev norm** of order $s \in \mathbb{N}$:
$$\|f\|_s^2 = \sum_{k=0}^{s} \int_0^{2\pi} |f^{(k)}(x)|^2 \, dx.$$
This is the norm $\|\cdot\|_s$ of [quarteroni2000numerical], §10.9, and the norm
$\|\cdot\|_{H^k}$ of Theorem 7.5.2 of [han2009theoretical].

The definition assumes no regularity of $f$. The derivatives are Mathlib's `iteratedDeriv`. -/
noncomputable def derivNormSq (s : ℕ) (f : ℝ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range (s + 1), ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2

/-- For every $s$ and $f$, $\|f\|_s^2 \ge 0$. -/
theorem derivNormSq_nonneg (s : ℕ) (f : ℝ → ℂ) : 0 ≤ derivNormSq s f :=
  Finset.sum_nonneg fun _ _ => intervalIntegral.integral_nonneg Real.two_pi_pos.le fun x _ => by
    positivity

/-- For $k \le s$, $\int_0^{2\pi} |f^{(k)}(x)|^2 \, dx \le \|f\|_s^2$. -/
theorem intervalIntegral_norm_iteratedDeriv_sq_le_derivNormSq {s k : ℕ} (hk : k ≤ s)
    (f : ℝ → ℂ) :
    ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2 ≤ derivNormSq s f :=
  Finset.single_le_sum (f := fun k => ∫ x in (0 : ℝ)..2 * π, ‖iteratedDeriv k f x‖ ^ 2)
    (fun _ _ => intervalIntegral.integral_nonneg Real.two_pi_pos.le fun x _ => by positivity)
    (Finset.mem_range.mpr (by omega))

/-! ### Parseval for the derivatives -/

/-- **Parseval's identity for the $k$-th derivative.** Let $f : \mathbb{R} \to \mathbb{C}$ be
$2\pi$-periodic and of class $C^s$, and let $k \le s$. Then
$$\sum_{n \in \mathbb{Z}} |n|^{2k} |\hat f_n|^2 = \frac{1}{2\pi} \int_0^{2\pi} |f^{(k)}(x)|^2 \,
  dx.$$
-/
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

/-- **The classical norm through the Fourier coefficients.** Let $f : \mathbb{R} \to \mathbb{C}$ be
$2\pi$-periodic and of class $C^s$. Then
$$\sum_{n \in \mathbb{Z}} \Big( \sum_{k=0}^{s} |n|^{2k} \Big) |\hat f_n|^2 = \frac{1}{2\pi}
  \|f\|_s^2.$$
This is Theorem 7.5.2 of [han2009theoretical]. -/
theorem hasSum_sum_abs_pow_mul_norm_fourierCoeff_lift_sq (hf : Function.Periodic f (2 * π))
    {s : ℕ} (hd : ContDiff ℝ s f) :
    HasSum (fun n : ℤ =>
        (∑ k ∈ Finset.range (s + 1), |(n : ℝ)| ^ (2 * k)) * ‖fourierCoeff hf.lift n‖ ^ 2)
      ((2 * π)⁻¹ * derivNormSq s f) := by
  rw [derivNormSq, Finset.mul_sum]
  refine (hasSum_sum fun k hk => hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).congr_fun fun n => ?_
  rw [Finset.sum_mul]

/-! ### The coefficient sequence as an element of $H^s$ -/

/-- The square of the weight satisfies $(w_s(m) |a|)^2 \le |a|^2 + |m|^{2s} |a|^2$, so the weighted
norm is bounded by the $L^2$ norms of $f$ and of $f^{(s)}$. -/
private theorem weight_mul_norm_sq_le (s : ℕ) (m : ℤ) (a : ℂ) :
    (periodicSobolevWeight s m * ‖a‖) ^ 2 ≤ ‖a‖ ^ 2 + |(m : ℝ)| ^ (2 * s) * ‖a‖ ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [periodicSobolevWeight_zero, one_mul]
    nlinarith [sq_nonneg ‖a‖, pow_nonneg (abs_nonneg ((0 : ℤ) : ℝ)) (2 * s)]
  · rw [mul_pow, periodicSobolevWeight_sq _ hm,
      show (2 : ℝ) * (s : ℝ) = ((2 * s : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    nlinarith [sq_nonneg ‖a‖]

/-- Let $f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class $C^s$. Then the series
$\sum_{m \in \mathbb{Z}} (w_s(m) |\hat f_m|)^2$ converges, where $w_s$ is
`periodicSobolevWeight`.

The square of the weight is at most $1 + |m|^{2s}$, and Parseval's identity at the orders $0$
and $s$ sums both parts. -/
theorem summable_weight_mul_norm_fourierCoeff_lift_sq (hf : Function.Periodic f (2 * π)) {s : ℕ}
    (hd : ContDiff ℝ s f) :
    Summable fun m : ℤ => (periodicSobolevWeight s m * ‖fourierCoeff hf.lift m‖) ^ 2 := by
  have h0 := hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd (Nat.zero_le s)
  have hs := hasSum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd (le_refl s)
  simp only [mul_zero, pow_zero, one_mul] at h0
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => weight_mul_norm_sq_le s m _) (h0.summable.add hs.summable)

/-- **The coefficient sequence of a smooth periodic function.** Let $f : \mathbb{R} \to \mathbb{C}$
be $2\pi$-periodic and of class $C^s$. This is the element of $H^s$ whose coefficients are the
Fourier coefficients $\hat f_m$ of $f$.

It connects the functions with the coefficient sequences. Its two properties are
`PeriodicSobolev.eval_ofSmooth` and `PeriodicSobolev.norm_ofSmooth_le`. -/
noncomputable def ofSmooth (hf : Function.Periodic f (2 * π)) {s : ℕ} (hd : ContDiff ℝ s f) :
    PeriodicSobolev s :=
  ofCoeff s (fourierCoeff hf.lift) (memℓp_two_iff.2
    ((summable_weight_mul_norm_fourierCoeff_lift_sq hf hd).congr fun m => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (periodicSobolevWeight_pos _ m).le]))

/-- The coefficients of the element of $H^s$ given by a $2\pi$-periodic $C^s$ function $f$ are the
Fourier coefficients $\hat f_m$. -/
@[simp]
theorem coeff_ofSmooth (hf : Function.Periodic f (2 * π)) {s : ℕ} (hd : ContDiff ℝ s f) :
    coeff (ofSmooth hf hd) = fourierCoeff hf.lift :=
  coeff_ofCoeff _ _ _

/-- Let $f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class $C^s$, and let
$\varphi \in H^s$ be its coefficient sequence. Then
$$\|\varphi\|^2 \le \frac{1}{2\pi} \Big( \int_0^{2\pi} |f(x)|^2 \, dx + \int_0^{2\pi}
  |f^{(s)}(x)|^2 \, dx \Big).$$

The square of the weight $w_s(m)$ is at most $1 + |m|^{2s}$. -/
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

/-- Let $s \ge 1$, let $f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class $C^s$, and
let $\varphi \in H^s$ be its coefficient sequence. Then
$$\|\varphi\| \le (2\pi)^{-1/2} \|f\|_s, \qquad \|f\|_s^2 = \sum_{k=0}^{s} \|f^{(k)}\|_{L^2(0,
  2\pi)}^2.$$
-/
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

/-- Let $s \ge 1$ and let $f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class $C^s$.
Then the sum of the Fourier series of $f$, read with period $2\pi$, is $f$:
$$\sum_{m \in \mathbb{Z}} \hat f_m e^{imx} = f(x) \quad \text{for every } x \in \mathbb{R}.$$

The series converges absolutely because $s > 1/2$ (`PeriodicSobolev.summable_coeff`), so it
converges pointwise to $f$ by `has_pointwise_sum_fourier_series_of_summable`. -/
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
