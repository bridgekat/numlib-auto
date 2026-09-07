/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric` for the Fourier
coefficients of `log ∘ sin`, and `Mathlib.Analysis.Fourier.AddCircle` for the operator.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The logarithmic single layer operator on the circle and its Fourier multipliers

The single layer potential of the unit circle, written in the arclength parameter, is the
convolution operator

`A φ t = -(1 / π) ∫_0^{2 π} φ s * log |2 e^(-1/2) sin ((t - s) / 2)| ds`,

whose kernel is the logarithm of the chord length `|e^(i t) - e^(i s)| = |2 sin ((t - s) / 2)|`,
rescaled so that the constant function is a fixed point. It is diagonal in the Fourier basis: `A`
multiplies the mode `e^(i m t)` by `1 / max 1 |m|`.

The analytic content is the value of the Fourier coefficients of `u ↦ log (sin (u / 2))` on
`[0, 2 π]`,

`∫_0^{2 π} log (sin (u / 2)) * cos (m u) du = -π / m`,  `m ≥ 1`,

which is `integral_log_sin_half_mul_cos` here. The proof used is an explicit antiderivative rather
than term-by-term integration of the classical expansion
`-log |2 sin (u / 2)| = ∑_{m ≥ 1} cos (m u) / m`, which converges only conditionally. Two elementary
multiple-angle identities do all the work:

* `cos_half_mul_sin_nat_mul`, the division-free form of
  `cot (u / 2) sin (m u) = 1 + 2 ∑_{k = 1}^{m - 1} cos (k u) + cos (m u)`, says that
  `log (sin (u / 2)) * cos (m u)` is the derivative on `(0, 2 π)` of an explicit elementary
  function;
* `sin_nat_mul_eq`, the factorization `sin (m u) = 2 sin (u / 2) ∑_{j < m} cos ((2 j + 1) (u / 2))`,
  together with the continuity of `x * log x` at `0`, says that this antiderivative extends
  continuously to the closed interval, so that the fundamental theorem of calculus applies to the
  improper endpoints.

## Main definitions

* `logSingleLayerKernel t s = -(1 / π) log |2 e^(-1/2) sin ((t - s) / 2)|`;
* `logSingleLayer φ t = ∫_0^{2 π} logSingleLayerKernel t s * φ s ds`, and its `ℂ`-valued
  counterpart `logSingleLayerC`.

## Main statements

* `integral_log_sin_half_mul_cos`, `integral_log_sin_half_mul_sin` and `integral_log_sin_half`, the
  Fourier coefficients of `u ↦ log (sin (u / 2))` on `[0, 2 π]`;
* `logSingleLayer_cos` and `logSingleLayer_sin`, that `A` multiplies `cos (m ·)` and `sin (m ·)` by
  `1 / max 1 m`;
* `logSingleLayerC_fourier`, the same for the complex modes `t ↦ e^(i m t)`, `m : ℤ`.
-/

open MeasureTheory

open scoped Real

/-! ### Two elementary multiple-angle identities -/

/-- `sin (m u) = 2 sin (u / 2) ∑_{j < m} cos ((2 j + 1) (u / 2))`: the sine of an integer multiple
of `u` factors through `sin (u / 2)` with a *continuous* cofactor. This is what makes
`log (sin (u / 2)) * sin (m u)` extend continuously by `0` to the zeros of `sin (u / 2)`. -/
theorem sin_nat_mul_eq (m : ℕ) (u : ℝ) :
    Real.sin (m * u)
      = 2 * Real.sin (u / 2) * ∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * (u / 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : Real.sin (((m : ℝ) + 1) * u) - Real.sin ((m : ℝ) * u)
        = 2 * Real.sin (u / 2) * Real.cos ((2 * (m : ℝ) + 1) * (u / 2)) := by
      rw [Real.sin_sub_sin, show (((m : ℝ) + 1) * u - (m : ℝ) * u) / 2 = u / 2 by ring,
        show (((m : ℝ) + 1) * u + (m : ℝ) * u) / 2 = (2 * (m : ℝ) + 1) * (u / 2) by ring]
    rw [Finset.sum_range_succ]
    push_cast at ih ⊢
    linear_combination ih + h

/-- `cos (u / 2) sin (m u) = sin (u / 2) (1 - cos (m u) + 2 ∑_{k < m} cos ((k + 1) u))`, the
division-free form of the classical identity
`cot (u / 2) sin (m u) = 1 + 2 ∑_{k = 1}^{m - 1} cos (k u) + cos (m u)`. It is what produces an
elementary antiderivative for `log (sin (u / 2)) * cos (m u)`. -/
theorem cos_half_mul_sin_nat_mul (m : ℕ) (u : ℝ) :
    Real.cos (u / 2) * Real.sin (m * u)
      = Real.sin (u / 2) * (1 - Real.cos (m * u)
          + 2 * ∑ k ∈ Finset.range m, Real.cos (((k : ℝ) + 1) * u)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : Real.cos ((m : ℝ) * u) + Real.cos (((m : ℝ) + 1) * u)
        = 2 * Real.cos ((2 * (m : ℝ) + 1) * (u / 2)) * Real.cos (u / 2) := by
      rw [Real.cos_add_cos,
        show ((m : ℝ) * u + ((m : ℝ) + 1) * u) / 2 = (2 * (m : ℝ) + 1) * (u / 2) by ring,
        show ((m : ℝ) * u - ((m : ℝ) + 1) * u) / 2 = -(u / 2) by ring, Real.cos_neg]
    have h' : Real.sin (((m : ℝ) + 1) * u) - Real.sin ((m : ℝ) * u)
        = 2 * Real.sin (u / 2) * Real.cos ((2 * (m : ℝ) + 1) * (u / 2)) := by
      rw [Real.sin_sub_sin, show (((m : ℝ) + 1) * u - (m : ℝ) * u) / 2 = u / 2 by ring,
        show (((m : ℝ) + 1) * u + (m : ℝ) * u) / 2 = (2 * (m : ℝ) + 1) * (u / 2) by ring]
    rw [Finset.sum_range_succ]
    push_cast at ih ⊢
    linear_combination ih + Real.cos (u / 2) * h' - Real.sin (u / 2) * h

/-! ### The Fourier coefficients of `log (sin (u / 2))` on `[0, 2 π]` -/

/-- An antiderivative of `1 - cos (m u) + 2 ∑_{k < m} cos ((k + 1) u)`. -/
private noncomputable def auxS (m : ℕ) (u : ℝ) : ℝ :=
  u - Real.sin (m * u) / m + 2 * ∑ k ∈ Finset.range m, Real.sin (((k : ℝ) + 1) * u) / ((k : ℝ) + 1)

/-- An antiderivative of `log (sin (u / 2)) * cos (m u)`, written so as to be continuous on all of
`ℝ`: on `(0, 2 π)` it is `log (sin (u / 2)) * sin (m u) / m - auxS m u / (2 m)`, but the first
summand is presented through `x * log x`, which is continuous at `0`. -/
private noncomputable def auxPhi (m : ℕ) (u : ℝ) : ℝ :=
  2 * (Real.sin (u / 2) * Real.log (Real.sin (u / 2)))
      * (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * (u / 2))) / m - auxS m u / (2 * m)

private theorem auxS_apply (m : ℕ) (u : ℝ) : auxS m u
    = u - Real.sin (m * u) / m
      + 2 * ∑ k ∈ Finset.range m, Real.sin (((k : ℝ) + 1) * u) / ((k : ℝ) + 1) := rfl

private theorem auxPhi_apply (m : ℕ) (u : ℝ) : auxPhi m u
    = 2 * (Real.sin (u / 2) * Real.log (Real.sin (u / 2)))
        * (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * (u / 2))) / m - auxS m u / (2 * m) := rfl

private theorem auxPhi_eq (m : ℕ) (u : ℝ) :
    auxPhi m u = Real.log (Real.sin (u / 2)) * Real.sin (m * u) / m - auxS m u / (2 * m) := by
  rw [auxPhi_apply, sin_nat_mul_eq m u]
  ring

private theorem continuous_auxPhi (m : ℕ) : Continuous (auxPhi m) := by
  have h1 : Continuous fun u : ℝ => Real.sin (u / 2) * Real.log (Real.sin (u / 2)) :=
    Real.continuous_mul_log.comp (by fun_prop)
  have h3 : Continuous (auxS m) := by unfold auxS; fun_prop
  unfold auxPhi
  exact (((h1.const_mul 2).mul (by fun_prop)).div_const (m : ℝ)).sub (h3.div_const (2 * (m : ℝ)))

private theorem hasDerivAt_auxS (m : ℕ) (hm : m ≠ 0) (u : ℝ) :
    HasDerivAt (auxS m)
      (1 - Real.cos (m * u) + 2 * ∑ k ∈ Finset.range m, Real.cos (((k : ℝ) + 1) * u)) u := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hsin : ∀ c : ℝ, HasDerivAt (fun y : ℝ => Real.sin (c * y)) (Real.cos (c * u) * c) u := by
    intro c
    have hlin : HasDerivAt (fun y : ℝ => c * y) c u := by
      simpa using (hasDerivAt_id u).const_mul c
    exact hlin.sin
  have h1 : HasDerivAt (fun y : ℝ => Real.sin ((m : ℝ) * y) / (m : ℝ))
      (Real.cos ((m : ℝ) * u)) u := by
    have := (hsin (m : ℝ)).div_const (m : ℝ)
    rw [mul_div_assoc, div_self hm', mul_one] at this
    exact this
  have h2 : ∀ k ∈ Finset.range m,
      HasDerivAt (fun y : ℝ => Real.sin (((k : ℝ) + 1) * y) / ((k : ℝ) + 1))
        (Real.cos (((k : ℝ) + 1) * u)) u := by
    intro k _
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    have := (hsin ((k : ℝ) + 1)).div_const ((k : ℝ) + 1)
    rw [mul_div_assoc, div_self hk, mul_one] at this
    exact this
  have hid : HasDerivAt (fun y : ℝ => y) 1 u := hasDerivAt_id u
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ k ∈ Finset.range m, Real.sin (((k : ℝ) + 1) * y) / ((k : ℝ) + 1))
      (∑ k ∈ Finset.range m, Real.cos (((k : ℝ) + 1) * u)) u := HasDerivAt.fun_sum h2
  exact (hid.sub h1).add (hsum.const_mul 2)

private theorem hasDerivAt_auxPhi {m : ℕ} (hm : m ≠ 0) {u : ℝ} (hu : Real.sin (u / 2) ≠ 0) :
    HasDerivAt (auxPhi m) (Real.log (Real.sin (u / 2)) * Real.cos (m * u)) u := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hhalf : HasDerivAt (fun y : ℝ => Real.sin (y / 2)) (Real.cos (u / 2) / 2) u := by
    have h0 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) u := (hasDerivAt_id u).div_const 2
    have h1 : HasDerivAt (fun y : ℝ => Real.sin (y / 2)) (Real.cos (u / 2) * (1 / 2)) u := h0.sin
    convert h1 using 1
    ring
  have hlog : HasDerivAt (fun y : ℝ => Real.log (Real.sin (y / 2)))
      (Real.cos (u / 2) / (2 * Real.sin (u / 2))) u := by
    have h := hhalf.log hu
    rw [div_div] at h
    exact h
  have hsinm : HasDerivAt (fun y : ℝ => Real.sin ((m : ℝ) * y))
      (Real.cos ((m : ℝ) * u) * (m : ℝ)) u := by
    have hlin : HasDerivAt (fun y : ℝ => (m : ℝ) * y) (m : ℝ) u := by
      simpa using (hasDerivAt_id u).const_mul (m : ℝ)
    exact hlin.sin
  have hprod : HasDerivAt
      (fun y : ℝ => Real.log (Real.sin (y / 2)) * Real.sin ((m : ℝ) * y) / (m : ℝ)
        - auxS m y / (2 * (m : ℝ)))
      ((Real.cos (u / 2) / (2 * Real.sin (u / 2)) * Real.sin ((m : ℝ) * u)
          + Real.log (Real.sin (u / 2)) * (Real.cos ((m : ℝ) * u) * (m : ℝ))) / (m : ℝ)
        - (1 - Real.cos ((m : ℝ) * u)
            + 2 * ∑ k ∈ Finset.range m, Real.cos (((k : ℝ) + 1) * u)) / (2 * (m : ℝ))) u :=
    ((hlog.mul hsinm).div_const (m : ℝ)).sub ((hasDerivAt_auxS m hm u).div_const (2 * (m : ℝ)))
  have hfun : auxPhi m = fun y : ℝ => Real.log (Real.sin (y / 2)) * Real.sin ((m : ℝ) * y)
      / (m : ℝ) - auxS m y / (2 * (m : ℝ)) := funext fun y => auxPhi_eq m y
  rw [hfun]
  refine hprod.congr_deriv ?_
  have hT : (1 : ℝ) - Real.cos ((m : ℝ) * u)
      + 2 * ∑ k ∈ Finset.range m, Real.cos (((k : ℝ) + 1) * u)
      = Real.cos (u / 2) * Real.sin ((m : ℝ) * u) / Real.sin (u / 2) := by
    rw [eq_div_iff hu, cos_half_mul_sin_nat_mul m u]
    ring
  rw [hT]
  field_simp
  ring

/-- The `m`-th cosine Fourier coefficient of `u ↦ log (sin (u / 2))` over `[0, 2 π]`, for
`m ≥ 1`. Equivalently, `∫_0^{2 π} log |2 sin (u / 2)| cos (m u) du = -π / m`, since
`∫_0^{2 π} cos (m u) du = 0`. -/
theorem integral_log_sin_half_mul_cos {m : ℕ} (hm : m ≠ 0) :
    ∫ u in (0 : ℝ)..(2 * π), Real.log (Real.sin (u / 2)) * Real.cos (m * u) = -π / m := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hint : IntervalIntegrable
      (fun u => Real.log (Real.sin (u / 2)) * Real.cos ((m : ℝ) * u)) volume 0 (2 * π) := by
    refine IntervalIntegrable.mul_continuousOn ?_ (by fun_prop)
    have h := (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left (c := (2 : ℝ)⁻¹)
    norm_num at h
    simpa [Function.comp_def, div_eq_inv_mul] using h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (by positivity : (0 : ℝ) ≤ 2 * π) (continuous_auxPhi m).continuousOn
    (fun u hu => (hasDerivAt_auxPhi hm (by
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by
        linarith [hu.2])))).hasDerivWithinAt) hint
  rw [hFTC]
  have h0 : auxPhi m 0 = 0 := by simp [auxPhi_apply, auxS_apply]
  have h2pi : auxPhi m (2 * π) = -π / m := by
    have hs : Real.sin ((2 : ℝ) * π / 2) = 0 := by
      rw [show (2 : ℝ) * π / 2 = π by ring, Real.sin_pi]
    have hsm : Real.sin ((m : ℝ) * (2 * π)) = 0 := by
      rw [show (m : ℝ) * (2 * π) = ((2 * m : ℕ) : ℝ) * π by push_cast; ring]
      exact Real.sin_nat_mul_pi _
    have hsk : ∀ k ∈ Finset.range m, Real.sin (((k : ℝ) + 1) * (2 * π)) = 0 := by
      intro k _
      rw [show ((k : ℝ) + 1) * (2 * π) = ((2 * (k + 1) : ℕ) : ℝ) * π by push_cast; ring]
      exact Real.sin_nat_mul_pi _
    rw [auxPhi_eq m, auxS_apply,
      Finset.sum_congr rfl (fun k hk => by rw [hsk k hk, zero_div])]
    simp only [hs, hsm, Real.log_zero, mul_zero, zero_div, zero_sub,
      Finset.sum_const_zero, sub_zero, add_zero]
    field_simp
  rw [h0, h2pi, sub_zero]

/-- The `m`-th sine Fourier coefficient of `u ↦ log (sin (u / 2))` over `[0, 2 π]` vanishes, because
the integrand is antisymmetric about `u = π`. -/
theorem integral_log_sin_half_mul_sin (m : ℕ) :
    ∫ u in (0 : ℝ)..(2 * π), Real.log (Real.sin (u / 2)) * Real.sin (m * u) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 2 * π) (d := 2 * π)
    (f := fun y => Real.log (Real.sin (y / 2)) * Real.sin ((m : ℝ) * y))
  rw [sub_zero, sub_self] at h
  have hcongr : ∫ u in (0 : ℝ)..(2 * π),
      Real.log (Real.sin ((2 * π - u) / 2)) * Real.sin ((m : ℝ) * (2 * π - u))
      = -∫ u in (0 : ℝ)..(2 * π), Real.log (Real.sin (u / 2)) * Real.sin ((m : ℝ) * u) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have e1 : Real.sin ((2 * π - u) / 2) = Real.sin (u / 2) := by
      rw [show (2 * π - u) / 2 = π - u / 2 by ring, Real.sin_pi_sub]
    have e2 : Real.sin ((m : ℝ) * (2 * π - u)) = -Real.sin ((m : ℝ) * u) := by
      rw [show (m : ℝ) * (2 * π - u) = -((m : ℝ) * u) + (m : ℝ) * (2 * π) by ring,
        Real.sin_add_nat_mul_two_pi, Real.sin_neg]
    rw [e1, e2]
    ring
  rw [hcongr] at h
  linarith

/-- The mean of `u ↦ log (sin (u / 2))` over `[0, 2 π]`, from `∫_0^π log (sin x) dx = -π log 2`. -/
theorem integral_log_sin_half :
    ∫ u in (0 : ℝ)..(2 * π), Real.log (Real.sin (u / 2)) = -(2 * π * Real.log 2) := by
  have h := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := 2 * π) (c := 2)
    (f := fun x => Real.log (Real.sin x)) two_ne_zero
  rw [show (2 : ℝ) * π / 2 = π by ring, zero_div] at h
  rw [h, integral_log_sin_zero_pi]
  simp only [smul_eq_mul]
  ring

/-! ### The logarithmic single layer operator -/

/-- The logarithmic single layer kernel as a function of the difference of its two parameters:
`logChord u = log |2 e^(-1/2) sin (u / 2)|`, written without the absolute value, since
`Real.log` already ignores the sign of its argument. Here `|2 sin (u / 2)|` is the chord length
`|e^(i t) - e^(i s)|` at `u = t - s`, and the factor `e^(-1/2)` is the normalization that makes the
constant function a fixed point of the operator below. -/
noncomputable def logChord (u : ℝ) : ℝ := Real.log 2 - 1 / 2 + Real.log (Real.sin (u / 2))

theorem logChord_eq_log_abs (u : ℝ) (hu : Real.sin (u / 2) ≠ 0) :
    logChord u = Real.log |2 * Real.exp (-(1 / 2)) * Real.sin (u / 2)| := by
  rw [Real.log_abs, Real.log_mul (by positivity) hu,
    Real.log_mul two_ne_zero (Real.exp_ne_zero _), Real.log_exp, logChord]
  ring

/-- `logChord` is `2 π`-periodic: `sin ((u + 2 π) / 2) = -sin (u / 2)`, and `Real.log` ignores the
sign. -/
theorem logChord_periodic : Function.Periodic logChord (2 * π) := by
  intro u
  rw [logChord, logChord, show (u + 2 * π) / 2 = u / 2 + π by ring, Real.sin_add_pi,
    Real.log_neg_eq_log]

theorem intervalIntegrable_logChord : IntervalIntegrable logChord volume 0 (2 * π) := by
  refine IntervalIntegrable.add intervalIntegrable_const ?_
  have h := (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left (c := (2 : ℝ)⁻¹)
  norm_num at h
  simpa [Function.comp_def, div_eq_inv_mul] using h

theorem intervalIntegrable_logChord_mul {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun y => logChord y * f y) volume 0 (2 * π) :=
  intervalIntegrable_logChord.mul_continuousOn hf.continuousOn

private theorem integral_cos_nat_mul {m : ℕ} (hm : m ≠ 0) :
    ∫ y in (0 : ℝ)..(2 * π), Real.cos ((m : ℝ) * y) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hm', integral_cos, mul_zero,
    Real.sin_zero, show (m : ℝ) * (2 * π) = ((2 * m : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi]
  simp

private theorem integral_sin_nat_mul (m : ℕ) :
    ∫ y in (0 : ℝ)..(2 * π), Real.sin ((m : ℝ) * y) = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
    rw [intervalIntegral.integral_comp_mul_left (f := Real.sin) hm', integral_sin, mul_zero,
      Real.cos_zero, Real.cos_nat_mul_two_pi]
    simp

/-- The `m`-th cosine Fourier coefficient of `logChord` over `[0, 2 π]` is `-π / max 1 m`. The
normalizing factor `e^(-1/2)` inside the logarithm is exactly what makes the value at `m = 0` agree
with the value at `m = 1`. -/
theorem integral_logChord_mul_cos (m : ℕ) :
    ∫ y in (0 : ℝ)..(2 * π), logChord y * Real.cos ((m : ℝ) * y) = -π / max 1 m := by
  have hsplit : ∀ f : ℝ → ℝ, Continuous f →
      ∫ y in (0 : ℝ)..(2 * π), logChord y * f y
        = (Real.log 2 - 1 / 2) * (∫ y in (0 : ℝ)..(2 * π), f y)
          + ∫ y in (0 : ℝ)..(2 * π), Real.log (Real.sin (y / 2)) * f y := by
    intro f hf
    have h1 : IntervalIntegrable (fun y : ℝ => (Real.log 2 - 1 / 2) * f y) volume 0 (2 * π) :=
      (hf.const_mul _).intervalIntegrable _ _
    have h2 : IntervalIntegrable
        (fun y : ℝ => Real.log (Real.sin (y / 2)) * f y) volume 0 (2 * π) := by
      have := intervalIntegrable_logChord_mul hf
      simpa [logChord, add_mul] using this.sub h1
    rw [show (fun y => logChord y * f y)
        = fun y => (Real.log 2 - 1 / 2) * f y + Real.log (Real.sin (y / 2)) * f y from
      funext fun y => by rw [logChord]; ring,
      intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [hsplit _ (by fun_prop)]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, integral_log_sin_half,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      show max 1 0 = 1 from max_eq_left (Nat.zero_le 1), Nat.cast_one, div_one]
    ring
  · rw [hsplit _ (by fun_prop), integral_cos_nat_mul hm, integral_log_sin_half_mul_cos hm,
      mul_zero, zero_add, max_eq_right (Nat.one_le_iff_ne_zero.2 hm)]

/-- The `m`-th sine Fourier coefficient of `logChord` over `[0, 2 π]` vanishes. -/
theorem integral_logChord_mul_sin (m : ℕ) :
    ∫ y in (0 : ℝ)..(2 * π), logChord y * Real.sin ((m : ℝ) * y) = 0 := by
  have h1 : IntervalIntegrable
      (fun y : ℝ => (Real.log 2 - 1 / 2) * Real.sin ((m : ℝ) * y)) volume 0 (2 * π) :=
    (Continuous.const_mul (by fun_prop) _).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun y : ℝ => Real.log (Real.sin (y / 2)) * Real.sin ((m : ℝ) * y)) volume 0 (2 * π) := by
    have := intervalIntegrable_logChord_mul (f := fun y : ℝ => Real.sin ((m : ℝ) * y)) (by fun_prop)
    simpa [logChord, add_mul] using this.sub h1
  rw [show (fun y => logChord y * Real.sin ((m : ℝ) * y))
      = fun y => (Real.log 2 - 1 / 2) * Real.sin ((m : ℝ) * y)
        + Real.log (Real.sin (y / 2)) * Real.sin ((m : ℝ) * y) from
    funext fun y => by rw [logChord]; ring,
    intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
    integral_sin_nat_mul, integral_log_sin_half_mul_sin, mul_zero, add_zero]

/-- **The kernel of the logarithmic single layer operator** of the unit circle,
`-(1 / π) log |2 e^(-1/2) sin ((t - s) / 2)|`, where `|2 sin ((t - s) / 2)| = |e^(i t) - e^(i s)|`
is the chord length. -/
noncomputable def logSingleLayerKernel (t s : ℝ) : ℝ :=
  -(1 / π) * Real.log |2 * Real.exp (-(1 / 2)) * Real.sin ((t - s) / 2)|

theorem logSingleLayerKernel_eq {t s : ℝ} (h : Real.sin ((t - s) / 2) ≠ 0) :
    logSingleLayerKernel t s = -(1 / π) * logChord (t - s) := by
  rw [logSingleLayerKernel, logChord_eq_log_abs _ h]

/-- **The logarithmic single layer operator** `A φ t = ∫_0^{2 π} k (t, s) φ s ds`. -/
noncomputable def logSingleLayer (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..(2 * π), logSingleLayerKernel t s * φ s

/-- The `ℂ`-valued logarithmic single layer operator, so that the Fourier modes `t ↦ e^(i m t)` are
admissible arguments. -/
noncomputable def logSingleLayerC (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..(2 * π), (logSingleLayerKernel t s : ℂ) * φ s

private theorem ae_sin_sub_ne_zero (t : ℝ) : ∀ᵐ s : ℝ, Real.sin ((t - s) / 2) ≠ 0 := by
  have hsub : {s : ℝ | Real.sin ((t - s) / 2) = 0}
      ⊆ Set.range fun n : ℤ => t - 2 * (n : ℝ) * π := by
    intro s hs
    rw [Set.mem_ofPred_eq, Real.sin_eq_zero_iff] at hs
    obtain ⟨n, hn⟩ := hs
    exact ⟨n, by linarith⟩
  have hc : ({s : ℝ | Real.sin ((t - s) / 2) = 0}).Countable :=
    Set.Countable.mono hsub (Set.countable_range _)
  rw [MeasureTheory.ae_iff]
  simpa using hc.measure_zero volume

/-- Reduction of the operator to a convolution against `logChord`: the change of variable
`s ↦ t - s` and the `2 π`-periodicity of the integrand. -/
private theorem logSingleLayer_eq_of_periodic {φ : ℝ → ℝ}
    (hper : Function.Periodic φ (2 * π)) (t : ℝ) :
    logSingleLayer φ t = -(1 / π) * ∫ y in (0 : ℝ)..(2 * π), logChord y * φ (t - y) := by
  have hcongr : logSingleLayer φ t
      = ∫ s in (0 : ℝ)..(2 * π), -(1 / π) * (logChord (t - s) * φ s) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_sin_sub_ne_zero t] with s hs _
    rw [logSingleLayerKernel_eq hs]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  congr 1
  have hsubst := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 2 * π) (d := t) (f := fun y => logChord y * φ (t - y))
  have hH : ∀ s : ℝ, logChord (t - s) * φ s
      = (fun y => logChord y * φ (t - y)) (t - s) := by
    intro s
    simp only [sub_sub_cancel]
  rw [show (fun s => logChord (t - s) * φ s)
      = fun s => (fun y => logChord y * φ (t - y)) (t - s) from funext hH]
  rw [hsubst, sub_zero]
  have hHper : Function.Periodic (fun y => logChord y * φ (t - y)) (2 * π) := by
    intro y
    have hb : φ (t - y - 2 * π) = φ (t - y) := by
      have h := hper (t - y - 2 * π)
      rw [show t - y - 2 * π + 2 * π = t - y by ring] at h
      exact h.symm
    change logChord (y + 2 * π) * φ (t - (y + 2 * π)) = logChord y * φ (t - y)
    rw [logChord_periodic y, show t - (y + 2 * π) = t - y - 2 * π by ring, hb]
  have := hHper.intervalIntegral_add_eq (t - 2 * π) 0
  rw [show t - 2 * π + 2 * π = t by ring, zero_add] at this
  exact this

/-- **The logarithmic single layer operator multiplies the cosine mode `cos (m ·)` by
`1 / max 1 m`.** -/
theorem logSingleLayer_cos (m : ℕ) (t : ℝ) :
    logSingleLayer (fun s => Real.cos ((m : ℝ) * s)) t = Real.cos ((m : ℝ) * t) / max 1 m := by
  have hper : Function.Periodic (fun s => Real.cos ((m : ℝ) * s)) (2 * π) := by
    intro s
    change Real.cos ((m : ℝ) * (s + 2 * π)) = Real.cos ((m : ℝ) * s)
    rw [show (m : ℝ) * (s + 2 * π) = (m : ℝ) * s + (m : ℕ) * (2 * π) by ring,
      Real.cos_add_nat_mul_two_pi]
  rw [logSingleLayer_eq_of_periodic hper t]
  have hexp : ∀ y : ℝ, logChord y * Real.cos ((m : ℝ) * (t - y))
      = Real.cos ((m : ℝ) * t) * (logChord y * Real.cos ((m : ℝ) * y))
        + Real.sin ((m : ℝ) * t) * (logChord y * Real.sin ((m : ℝ) * y)) := by
    intro y
    rw [show (m : ℝ) * (t - y) = (m : ℝ) * t - (m : ℝ) * y by ring, Real.cos_sub]
    ring
  rw [intervalIntegral.integral_congr (fun y _ => hexp y),
    intervalIntegral.integral_add
      ((intervalIntegrable_logChord_mul (by fun_prop)).const_mul _)
      ((intervalIntegrable_logChord_mul (by fun_prop)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_logChord_mul_cos, integral_logChord_mul_sin, mul_zero, add_zero]
  have hmax : (0 : ℝ) < ((max 1 m : ℕ) : ℝ) :=
    Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 m))
  field_simp

/-- **The logarithmic single layer operator multiplies the sine mode `sin (m ·)` by
`1 / max 1 m`.** -/
theorem logSingleLayer_sin (m : ℕ) (t : ℝ) :
    logSingleLayer (fun s => Real.sin ((m : ℝ) * s)) t = Real.sin ((m : ℝ) * t) / max 1 m := by
  have hper : Function.Periodic (fun s => Real.sin ((m : ℝ) * s)) (2 * π) := by
    intro s
    change Real.sin ((m : ℝ) * (s + 2 * π)) = Real.sin ((m : ℝ) * s)
    rw [show (m : ℝ) * (s + 2 * π) = (m : ℝ) * s + (m : ℕ) * (2 * π) by ring,
      Real.sin_add_nat_mul_two_pi]
  rw [logSingleLayer_eq_of_periodic hper t]
  have hexp : ∀ y : ℝ, logChord y * Real.sin ((m : ℝ) * (t - y))
      = Real.sin ((m : ℝ) * t) * (logChord y * Real.cos ((m : ℝ) * y))
        - Real.cos ((m : ℝ) * t) * (logChord y * Real.sin ((m : ℝ) * y)) := by
    intro y
    rw [show (m : ℝ) * (t - y) = (m : ℝ) * t - (m : ℝ) * y by ring, Real.sin_sub]
    ring
  rw [intervalIntegral.integral_congr (fun y _ => hexp y),
    intervalIntegral.integral_sub
      ((intervalIntegrable_logChord_mul (by fun_prop)).const_mul _)
      ((intervalIntegrable_logChord_mul (by fun_prop)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_logChord_mul_cos, integral_logChord_mul_sin, mul_zero, sub_zero]
  have hmax : (0 : ℝ) < ((max 1 m : ℕ) : ℝ) :=
    Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 m))
  field_simp

/-! ### The integer Fourier modes -/

theorem logSingleLayer_const_mul (c : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    logSingleLayer (fun s => c * φ s) t = c * logSingleLayer φ t := by
  rw [logSingleLayer, logSingleLayer, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun s _ => by ring

theorem logSingleLayer_neg (φ : ℝ → ℝ) (t : ℝ) :
    logSingleLayer (fun s => -φ s) t = -logSingleLayer φ t := by
  rw [logSingleLayer, logSingleLayer, ← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun s _ => by ring

private theorem cast_max_one_abs (n : ℕ) :
    ((max 1 |(n : ℤ)| : ℤ) : ℝ) = ((max 1 n : ℕ) : ℝ) ∧
      ((max 1 |(-(n : ℤ))| : ℤ) : ℝ) = ((max 1 n : ℕ) : ℝ) := by
  have h1 : |(n : ℤ)| = ((n : ℕ) : ℤ) := abs_of_nonneg (Int.natCast_nonneg n)
  have h2 : |(-(n : ℤ))| = ((n : ℕ) : ℤ) := by rw [abs_neg, h1]
  exact ⟨by rw [h1]; norm_cast, by rw [h2]; norm_cast⟩

/-- **The logarithmic single layer operator multiplies the cosine mode `cos (m ·)` by
`1 / max 1 |m|`**, for an integer frequency `m`. -/
theorem logSingleLayer_cos_int (m : ℤ) (t : ℝ) :
    logSingleLayer (fun s => Real.cos ((m : ℝ) * s)) t
      = Real.cos ((m : ℝ) * t) / max 1 |m| := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n : ℕ, m = (n : ℤ) ∨ m = -(n : ℤ) := ⟨m.natAbs, Int.natAbs_eq m⟩
  · rw [(cast_max_one_abs n).1]
    exact_mod_cast logSingleLayer_cos n t
  · rw [(cast_max_one_abs n).2]
    have hc : ∀ s : ℝ, Real.cos (((-(n : ℤ) : ℤ) : ℝ) * s) = Real.cos ((n : ℝ) * s) := by
      intro s
      rw [show (((-(n : ℤ) : ℤ) : ℝ)) = -(n : ℝ) by norm_cast, neg_mul, Real.cos_neg]
    simp only [hc]
    exact logSingleLayer_cos n t

/-- **The logarithmic single layer operator multiplies the sine mode `sin (m ·)` by
`1 / max 1 |m|`**, for an integer frequency `m`. -/
theorem logSingleLayer_sin_int (m : ℤ) (t : ℝ) :
    logSingleLayer (fun s => Real.sin ((m : ℝ) * s)) t
      = Real.sin ((m : ℝ) * t) / max 1 |m| := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n : ℕ, m = (n : ℤ) ∨ m = -(n : ℤ) := ⟨m.natAbs, Int.natAbs_eq m⟩
  · rw [(cast_max_one_abs n).1]
    exact_mod_cast logSingleLayer_sin n t
  · rw [(cast_max_one_abs n).2]
    have hc : ∀ s : ℝ, Real.sin (((-(n : ℤ) : ℤ) : ℝ) * s) = -Real.sin ((n : ℝ) * s) := by
      intro s
      rw [show (((-(n : ℤ) : ℤ) : ℝ)) = -(n : ℝ) by norm_cast, neg_mul, Real.sin_neg]
    simp only [hc]
    rw [logSingleLayer_neg, logSingleLayer_sin]
    ring

/-! ### The complex Fourier modes -/

theorem intervalIntegrable_logChord_sub (t : ℝ) :
    IntervalIntegrable (fun s => logChord (t - s)) volume 0 (2 * π) := by
  have h := (logChord_periodic.intervalIntegrable₀ (by positivity) intervalIntegrable_logChord
    (t - 2 * π) t).comp_sub_left t
  rw [sub_self, show t - (t - 2 * π) = 2 * π by ring] at h
  exact h.symm

theorem intervalIntegrable_logSingleLayerKernel_mul (t : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntervalIntegrable (fun s => logSingleLayerKernel t s * φ s) volume 0 (2 * π) := by
  refine IntervalIntegrable.congr_ae
    ((((intervalIntegrable_logChord_sub t).const_mul (-(1 / π))).mul_continuousOn
      hφ.continuousOn)) ?_
  refine (MeasureTheory.ae_restrict_of_ae (ae_sin_sub_ne_zero t)).mono fun s hs => ?_
  change -(1 / π) * logChord (t - s) * φ s = logSingleLayerKernel t s * φ s
  rw [logSingleLayerKernel_eq hs]

private theorem logSingleLayerC_of_re_im {f g : ℝ → ℝ} (t : ℝ)
    (hf : IntervalIntegrable (fun s => logSingleLayerKernel t s * f s) volume 0 (2 * π))
    (hg : IntervalIntegrable (fun s => logSingleLayerKernel t s * g s) volume 0 (2 * π)) :
    logSingleLayerC (fun s => (f s : ℂ) + (g s : ℂ) * Complex.I) t
      = (logSingleLayer f t : ℂ) + (logSingleLayer g t : ℂ) * Complex.I := by
  have hf' : IntervalIntegrable
      (fun s => ((logSingleLayerKernel t s * f s : ℝ) : ℂ)) volume 0 (2 * π) :=
    ⟨hf.1.ofReal, hf.2.ofReal⟩
  have hg' : IntervalIntegrable
      (fun s => ((logSingleLayerKernel t s * g s : ℝ) : ℂ) * Complex.I) volume 0 (2 * π) :=
    (IntervalIntegrable.mul_const (⟨hg.1.ofReal, hg.2.ofReal⟩) Complex.I)
  rw [logSingleLayerC, logSingleLayer, logSingleLayer,
    intervalIntegral.integral_congr (g := fun s => ((logSingleLayerKernel t s * f s : ℝ) : ℂ)
      + ((logSingleLayerKernel t s * g s : ℝ) : ℂ) * Complex.I)
      (fun s _ => by push_cast; ring),
    intervalIntegral.integral_add hf' hg', intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

/-- **(The Fourier diagonalization of the logarithmic single layer operator.)** `A` multiplies the
mode `ψ_m t = e^(i m t)` by `1 / max 1 |m|`; in particular it fixes the constant mode `ψ_0`. -/
theorem logSingleLayerC_fourier (m : ℤ) (t : ℝ) :
    logSingleLayerC (fun s => Complex.exp (m * s * Complex.I)) t
      = Complex.exp (m * t * Complex.I) / max 1 |m| := by
  have hexp : ∀ x : ℝ, Complex.exp ((m : ℂ) * (x : ℂ) * Complex.I)
      = (Real.cos ((m : ℝ) * x) : ℂ) + (Real.sin ((m : ℝ) * x) : ℂ) * Complex.I := by
    intro x
    rw [show (m : ℂ) * (x : ℂ) = (((m : ℝ) * x : ℝ) : ℂ) by push_cast; ring, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  have hM : (0 : ℝ) < ((max 1 |m| : ℤ) : ℝ) := by
    have : (1 : ℤ) ≤ max 1 |m| := le_max_left _ _
    exact_mod_cast lt_of_lt_of_le zero_lt_one this
  rw [show (fun s : ℝ => Complex.exp ((m : ℂ) * (s : ℂ) * Complex.I))
      = fun s : ℝ => (Real.cos ((m : ℝ) * s) : ℂ) + (Real.sin ((m : ℝ) * s) : ℂ) * Complex.I from
        funext hexp,
    logSingleLayerC_of_re_im t (intervalIntegrable_logSingleLayerKernel_mul t (by fun_prop))
      (intervalIntegrable_logSingleLayerKernel_mul t (by fun_prop)),
    logSingleLayer_cos_int, logSingleLayer_sin_int, hexp t, Complex.ofReal_div,
    Complex.ofReal_div, Complex.ofReal_intCast]
  ring
