import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A flat Gaussian cutoff and a Gaussian primitive

The cutoff is zero on the negative half-line and equals `exp (-x⁻²)` on the
positive half-line. Polynomial-weighted versions give a reusable proof of smoothness
and vanishing of every derivative at the junction.
-/

noncomputable section
open scoped Topology ContDiff
open Polynomial Real Filter Set MeasureTheory

namespace Analysis.FlatGaussian

/-- A Gaussian cutoff flat at the origin, with support in the positive half-line. -/
def cutoff (x : ℝ) : ℝ := if x ≤ 0 then 0 else exp (-(x⁻¹) ^ 2)

/-- The cutoff vanishes on the negative half-line, including the junction. -/
theorem cutoff_eq_zero {x : ℝ} (hx : x ≤ 0) : cutoff x = 0 := by simp [cutoff, hx]

/-- The positive branch is the prescribed inverse-square exponential. -/
theorem cutoff_eq_exp {x : ℝ} (hx : 0 < x) : cutoff x = exp (-(x⁻¹) ^ 2) := by
  simp [cutoff, hx.not_ge]

/-- The cutoff is nonnegative everywhere. -/
theorem cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := by
  unfold cutoff
  split_ifs <;> positivity

/-- The cutoff is positive exactly on the positive half-line. -/
theorem cutoff_pos_iff (x : ℝ) : 0 < cutoff x ↔ 0 < x := by
  by_cases hx : x ≤ 0
  · simp [cutoff_eq_zero hx, not_lt.mpr hx]
  · simp [cutoff, hx, exp_pos, lt_of_not_ge hx]

/-- Polynomial factors in the inverse variable preserve flatness at zero. -/
theorem tendsto_polynomial_inv_mul_cutoff (p : ℝ[X]) :
    Tendsto (fun x ↦ p.eval x⁻¹ * cutoff x) (𝓝 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using (expNegInvGlue.tendsto_polynomial_inv_mul_zero p).norm)
  filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
  by_cases h : x ≤ 0
  · simp only [cutoff_eq_zero h, mul_zero, norm_zero]
    positivity
  · have hp : 0 < x := lt_of_not_ge h
    have hi : 1 ≤ x⁻¹ := (one_le_inv₀ hp).mpr hx.le
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (cutoff_nonneg x), abs_of_nonneg (expNegInvGlue.nonneg x)]
    gcongr
    rw [cutoff_eq_exp hp, expNegInvGlue, ite_eq_right h]
    exact exp_le_exp.mpr (by nlinarith)

/-- Differentiating a polynomial-weighted cutoff updates its polynomial factor. -/
theorem hasDerivAt_polynomial_inv_mul_cutoff (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * cutoff x)
      ((2 * X ^ 3 * p - X ^ 2 * derivative p).eval x⁻¹ * cutoff x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [cutoff_eq_zero hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [cutoff_eq_zero hy.le, mul_zero]
  · simp only [cutoff_eq_zero le_rfl, mul_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_polynomial_inv_mul_cutoff (p * X)).mono_left inf_le_left).congr ?_
    intro x
    simp [slope_def_field, div_eq_mul_inv, cutoff_eq_zero le_rfl, mul_right_comm]
  · have h := ((p.hasDerivAt x⁻¹).mul
      (((hasDerivAt_id x⁻¹).pow 2).neg.exp)).comp x (hasDerivAt_inv hx.ne')
    convert h.congr_of_eventuallyEq ?_ using 1
    · simp [cutoff_eq_exp hx]
      ring
    · filter_upwards [lt_mem_nhds hx] with y hy
      simp [cutoff_eq_exp hy]

/-- Every polynomial-weighted cutoff is smooth, including its flat junction. -/
theorem contDiff_polynomial_inv_mul_cutoff {n : ℕ∞} (p : ℝ[X]) :
    ContDiff ℝ n (fun x ↦ p.eval x⁻¹ * cutoff x) := by
  apply contDiff_all_iff_nat.2 (fun m ↦ ?_) n
  induction m generalizing p with
  | zero =>
    apply contDiff_zero.mpr
    exact (show Differentiable ℝ _ from fun x ↦
      (hasDerivAt_polynomial_inv_mul_cutoff p x).differentiableAt).continuous
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.mpr ⟨fun x ↦
      (hasDerivAt_polynomial_inv_mul_cutoff p x).differentiableAt, by simp, ?_⟩
    convert ih (2 * X ^ 3 * p - X ^ 2 * derivative p) using 2
    exact (hasDerivAt_polynomial_inv_mul_cutoff p _).deriv

/-- The inverse-square cutoff is infinitely smooth. -/
@[fun_prop] theorem contDiff_cutoff {n : ℕ∞} : ContDiff ℝ n cutoff := by
  simpa using (contDiff_polynomial_inv_mul_cutoff (n := n) 1)

/-- The polynomial factor in the `n`th derivative of the cutoff. -/
noncomputable def cutoffPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => 2 * X ^ 3 * cutoffPolynomial n - X ^ 2 * derivative (cutoffPolynomial n)

/-- Every derivative is an explicit polynomial in the inverse variable times the cutoff. -/
theorem iteratedDeriv_cutoff (n : ℕ) (x : ℝ) :
    iteratedDeriv n cutoff x = (cutoffPolynomial n).eval x⁻¹ * cutoff x := by
  induction n generalizing x with
  | zero => simp [cutoffPolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n cutoff = fun x ↦ (cutoffPolynomial n).eval x⁻¹ * cutoff x :=
      funext ih
    rw [heq]
    exact (hasDerivAt_polynomial_inv_mul_cutoff (cutoffPolynomial n) x).deriv

/-- Every derivative, including the value, vanishes on the nonpositive half-line. -/
theorem iteratedDeriv_cutoff_eq_zero (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    iteratedDeriv n cutoff x = 0 := by
  rw [iteratedDeriv_cutoff, cutoff_eq_zero hx, mul_zero]

/-- The standard unnormalized Gaussian. -/
def gaussian (x : ℝ) : ℝ := exp (-(x ^ 2 / 2))

/-- The Gaussian is infinitely smooth. -/
@[fun_prop] theorem contDiff_gaussian : ContDiff ℝ ∞ gaussian := by
  unfold gaussian
  fun_prop

/-- The Gaussian is integrable on the whole line. -/
theorem integrable_gaussian : Integrable gaussian := by
  convert integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) using 1
  ext x
  unfold gaussian
  congr 1
  ring

/-- The positive Gaussian primitive with lower integration endpoint at negative infinity. -/
def primitive (x : ℝ) : ℝ := exp (1 / 2 : ℝ) * ∫ t in Iic x, gaussian t

/-- The improper primitive splits into its value at zero and a finite interval integral. -/
theorem primitive_eq_interval (x : ℝ) :
    primitive x = primitive 0 + exp (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..x, gaussian t := by
  have h := intervalIntegral.integral_Iic_sub_Iic
    (a := (0 : ℝ)) (b := x) integrable_gaussian.integrableOn
    integrable_gaussian.integrableOn
  dsimp [primitive]
  rw [← h]
  ring

/-- The derivative of the primitive is the prescribed Gaussian density. -/
theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (exp ((1 - x ^ 2) / 2)) x := by
  have h := (intervalIntegral.integral_hasDerivAt_right
    (contDiff_gaussian.continuous.intervalIntegrable 0 x)
    contDiff_gaussian.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    contDiff_gaussian.continuous.continuousAt).const_mul (exp (1 / 2 : ℝ))
  have h' := h.const_add (primitive 0)
  convert h'.congr_of_eventuallyEq (Eventually.of_forall primitive_eq_interval) using 1
  rw [gaussian, ← exp_add]
  congr 1
  ring

/-- The scalar derivative formula for the Gaussian primitive. -/
theorem deriv_primitive (x : ℝ) : deriv primitive x = exp ((1 - x ^ 2) / 2) :=
  (hasDerivAt_primitive x).deriv

/-- The Gaussian primitive is infinitely smooth. -/
@[fun_prop] theorem contDiff_primitive : ContDiff ℝ ∞ primitive := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_primitive x).differentiableAt, ?_⟩
  simp_rw [show deriv primitive = fun x ↦ exp ((1 - x ^ 2) / 2) from funext deriv_primitive]
  fun_prop

/-- The Gaussian primitive is strictly positive everywhere. -/
theorem primitive_pos (x : ℝ) : 0 < primitive x := by
  apply mul_pos (exp_pos _)
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun t ↦ (exp_pos (-(t ^ 2 / 2))).le)
    integrable_gaussian.integrableOn).mpr
  simp [Function.support, exp_ne_zero]

/-- On the unit interval, the derivative of the primitive exceeds one. -/
theorem one_lt_deriv_primitive {x : ℝ} (hx : |x| < 1) : 1 < deriv primitive x := by
  rw [deriv_primitive, one_lt_exp_iff]
  have h := (sq_lt_one_iff_abs_lt_one x).mpr hx
  linarith

/-- The total scaled Gaussian mass bounds every value of the primitive. -/
theorem primitive_le (x : ℝ) : primitive x ≤ exp (1 / 2 : ℝ) * Real.sqrt (2 * Real.pi) := by
  have h := setIntegral_le_integral integrable_gaussian
    (Eventually.of_forall fun t ↦ (exp_pos (-(t ^ 2 / 2))).le) (s := Iic x)
  have heq : (∫ t : ℝ, gaussian t) = Real.sqrt (2 * Real.pi) := by
    have h := integral_gaussian (1 / 2 : ℝ)
    convert h using 1
    · congr 1
      funext t
      unfold gaussian
      congr 1
      ring
    · congr 1
      ring
  unfold primitive
  gcongr
  exact h.trans_eq heq

end Analysis.FlatGaussian
