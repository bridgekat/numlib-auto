/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric` for the Fourier
coefficients of `log ∘ sin`, and `Mathlib.Analysis.Fourier.AddCircle` for the operator.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The logarithmic single layer operator on the circle and its Fourier multipliers

The single layer potential of the unit circle, written in the arclength parameter, is the
convolution operator
$$A\varphi(t) = -\frac{1}{\pi} \int_0^{2\pi} \varphi(s) \log \bigl|2 e^{-1/2} \sin\bigl((t -
  s)/2\bigr)\bigr| \, ds.$$
Its kernel is the logarithm of the chord length $|e^{it} - e^{is}| = |2 \sin((t - s)/2)|$, rescaled
by the factor $e^{-1/2}$ so that the constant function is a fixed point of $A$. The operator is
diagonal in the Fourier basis: $A$ multiplies the mode $e^{imt}$, $m \in \mathbb{Z}$, by
$1/\max(1, |m|)$.

The analytic content is the value of the Fourier coefficients of $u \mapsto \log(\sin(u/2))$ on
$[0, 2\pi]$:
$$\int_0^{2\pi} \log(\sin(u/2)) \cos(mu) \, du = -\frac{\pi}{m}, \qquad m \ge 1.$$

## Main definitions

* `logChord`: the kernel as a function of the difference $u = t - s$, $\log|2 e^{-1/2} \sin(u/2)|$.
* `logSingleLayerKernel`: the kernel $k(t, s) = -\pi^{-1} \log|2 e^{-1/2} \sin((t - s)/2)|$.
* `logSingleLayer`: the operator $A\varphi(t) = \int_0^{2\pi} k(t, s) \varphi(s) \, ds$ on real
  functions.
* `logSingleLayerC`: the same operator on complex functions.

## Main results

* `integral_log_sin_half_mul_cos`, `integral_log_sin_half_mul_sin` and `integral_log_sin_half`: the
  Fourier coefficients of $u \mapsto \log(\sin(u/2))$ on $[0, 2\pi]$.
* `logSingleLayer_cos` and `logSingleLayer_sin`: $A$ multiplies $\cos(m \cdot)$ and $\sin(m \cdot)$
  by $1/\max(1, m)$ for $m \in \mathbb{N}$.
* `logSingleLayer_cos_int` and `logSingleLayer_sin_int`: the same for $m \in \mathbb{Z}$, with the
  factor $1/\max(1, |m|)$.
* `logSingleLayerC_fourier`: $A$ multiplies the complex mode $t \mapsto e^{imt}$,
  $m \in \mathbb{Z}$, by $1/\max(1, |m|)$.

## Proof outline

The coefficients are computed with an explicit antiderivative, not by integration term by term of
the classical expansion $-\log|2 \sin(u/2)| = \sum_{m \ge 1} \cos(mu)/m$, which converges only
conditionally. Two elementary identities for multiple angles do all the work. The first,
`cos_half_mul_sin_nat_mul`, is the form without division of
$$\cot(u/2) \sin(mu) = 1 + 2 \sum_{k=1}^{m-1} \cos(ku) + \cos(mu).$$
It shows that $\log(\sin(u/2)) \cos(mu)$ is the derivative on $(0, 2\pi)$ of an explicit elementary
function. The second, `sin_nat_mul_eq`, is the factorization $\sin(mu) = 2 \sin(u/2) \sum_{j<m}
\cos((2j + 1)u/2)$. Together with the continuity of $x \log x$ at $0$, it shows that this
antiderivative extends continuously to the closed interval $[0, 2\pi]$. So the fundamental theorem
of calculus applies up to the endpoints, where the integrand is unbounded.

## Implementation notes

* `Real.log` is the logarithm of the absolute value, with `Real.log 0 = 0`. So `logChord` needs no
  absolute value, and the kernel `logSingleLayerKernel t s` is $0$ where $\sin((t - s)/2) = 0$, a
  set of measure zero.
-/

open MeasureTheory

open scoped Real

/-! ### Two elementary identities for multiple angles -/

/-- For $m \in \mathbb{N}$ and $u \in \mathbb{R}$,
$$\sin(mu) = 2 \sin(u/2) \sum_{j=0}^{m-1} \cos\bigl((2j + 1) u/2\bigr).$$
So the sine of an integer multiple of $u$ factors through $\sin(u/2)$, with a continuous
cofactor.

This is what makes $\log(\sin(u/2)) \sin(mu)$ extend continuously by $0$ to the zeros of
$\sin(u/2)$. -/
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

/-- For $m \in \mathbb{N}$ and $u \in \mathbb{R}$,
$$\cos(u/2) \sin(mu) = \sin(u/2) \Bigl(1 - \cos(mu) + 2 \sum_{k=0}^{m-1} \cos((k + 1)u)\Bigr).$$
This is the form without division of the classical identity $\cot(u/2) \sin(mu) = 1 + 2
\sum_{k=1}^{m-1} \cos(ku) + \cos(mu)$.

It gives an elementary antiderivative of $\log(\sin(u/2)) \cos(mu)$. -/
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

/-! ### The Fourier coefficients of $\log(\sin(u/2))$ on $[0, 2\pi]$ -/

/-- An antiderivative $u - \sin(mu)/m + 2 \sum_{k<m} \sin((k + 1)u)/(k + 1)$ of
$1 - \cos(mu) + 2 \sum_{k<m} \cos((k + 1)u)$. -/
private noncomputable def auxS (m : ℕ) (u : ℝ) : ℝ :=
  u - Real.sin (m * u) / m + 2 * ∑ k ∈ Finset.range m, Real.sin (((k : ℝ) + 1) * u) / ((k : ℝ) + 1)

/-- An antiderivative of $\log(\sin(u/2)) \cos(mu)$ that is continuous on $\mathbb{R}$: on
$(0, 2\pi)$ it is $\log(\sin(u/2)) \sin(mu)/m - S(u)/(2m)$ with $S$ the function above, written
through $x \log x$ at $x = \sin(u/2)$, which is continuous at $0$. -/
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

/-- For a natural number $m \ge 1$, the $m$-th cosine Fourier coefficient of
$u \mapsto \log(\sin(u/2))$ on $[0, 2\pi]$ is
$$\int_0^{2\pi} \log(\sin(u/2)) \cos(mu) \, du = -\frac{\pi}{m}.$$
Since $\int_0^{2\pi} \cos(mu) \, du = 0$, also $\int_0^{2\pi} \log|2 \sin(u/2)| \cos(mu) \, du =
-\pi/m$. -/
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

/-- For every $m \in \mathbb{N}$, the $m$-th sine Fourier coefficient of $u \mapsto \log(\sin(u/2))$
on $[0, 2\pi]$ vanishes:
$$\int_0^{2\pi} \log(\sin(u/2)) \sin(mu) \, du = 0.$$
The reason is that the integrand is antisymmetric about $u = \pi$. -/
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

/-- The integral of $u \mapsto \log(\sin(u/2))$ over $[0, 2\pi]$:
$$\int_0^{2\pi} \log(\sin(u/2)) \, du = -2\pi \log 2.$$
This follows from $\int_0^\pi \log(\sin x) \, dx = -\pi \log 2$. -/
theorem integral_log_sin_half :
    ∫ u in (0 : ℝ)..(2 * π), Real.log (Real.sin (u / 2)) = -(2 * π * Real.log 2) := by
  have h := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := 2 * π) (c := 2)
    (f := fun x => Real.log (Real.sin x)) two_ne_zero
  rw [show (2 : ℝ) * π / 2 = π by ring, zero_div] at h
  rw [h, integral_log_sin_zero_pi]
  simp only [smul_eq_mul]
  ring

/-! ### The logarithmic single layer operator -/

/-- The logarithmic single layer kernel as a function of the difference $u = t - s$ of its two
parameters:
$$\ell(u) = \log 2 - \frac{1}{2} + \log(\sin(u/2)),$$
which is $\log|2 e^{-1/2} \sin(u/2)|$ where $\sin(u/2) \ne 0$.

The factor $|2 \sin(u/2)|$ is the chord length $|e^{it} - e^{is}|$ at $u = t - s$, and the
factor $e^{-1/2}$ is the normalization that makes the constant function a fixed point of the
operator `logSingleLayer`. The formula needs no absolute value, because `Real.log` is the
logarithm of the absolute value. Where $\sin(u/2) = 0$, the value is $\log 2 - 1/2$, because
`Real.log 0 = 0`. -/
noncomputable def logChord (u : ℝ) : ℝ := Real.log 2 - 1 / 2 + Real.log (Real.sin (u / 2))

/-- Where $\sin(u/2) \ne 0$, `logChord u` is $\log|2 e^{-1/2} \sin(u/2)|$. -/
theorem logChord_eq_log_abs (u : ℝ) (hu : Real.sin (u / 2) ≠ 0) :
    logChord u = Real.log |2 * Real.exp (-(1 / 2)) * Real.sin (u / 2)| := by
  rw [Real.log_abs, Real.log_mul (by positivity) hu,
    Real.log_mul two_ne_zero (Real.exp_ne_zero _), Real.log_exp, logChord]
  ring

/-- The function `logChord` is $2\pi$-periodic, because $\sin((u + 2\pi)/2) = -\sin(u/2)$ and the
logarithm ignores the sign. -/
theorem logChord_periodic : Function.Periodic logChord (2 * π) := by
  intro u
  rw [logChord, logChord, show (u + 2 * π) / 2 = u / 2 + π by ring, Real.sin_add_pi,
    Real.log_neg_eq_log]

/-- The function `logChord` is integrable on $[0, 2\pi]$. -/
theorem intervalIntegrable_logChord : IntervalIntegrable logChord volume 0 (2 * π) := by
  refine IntervalIntegrable.add intervalIntegrable_const ?_
  have h := (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left (c := (2 : ℝ)⁻¹)
  norm_num at h
  simpa [Function.comp_def, div_eq_inv_mul] using h

/-- For a continuous $f : \mathbb{R} \to \mathbb{R}$, the product $y \mapsto \ell(y) f(y)$ of
`logChord` and $f$ is integrable on $[0, 2\pi]$. -/
theorem intervalIntegrable_logChord_mul {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun y => logChord y * f y) volume 0 (2 * π) :=
  intervalIntegrable_logChord.mul_continuousOn hf.continuousOn

/-- For every $m \in \mathbb{N}$, the $m$-th cosine Fourier coefficient of $\ell = $ `logChord` on
$[0, 2\pi]$ is
$$\int_0^{2\pi} \ell(y) \cos(my) \, dy = -\frac{\pi}{\max(1, m)}.$$

The normalizing factor $e^{-1/2}$ inside the logarithm is exactly what makes the value at
$m = 0$ agree with the value at $m = 1$. -/
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
  · rw [hsplit _ (by fun_prop), integral_cos_nat_mul_eq_zero hm, integral_log_sin_half_mul_cos hm,
      mul_zero, zero_add, max_eq_right (Nat.one_le_iff_ne_zero.2 hm)]

/-- For every $m \in \mathbb{N}$, the $m$-th sine Fourier coefficient of $\ell = $ `logChord` on
$[0, 2\pi]$ vanishes: $\int_0^{2\pi} \ell(y) \sin(my) \, dy = 0$. -/
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
    integral_sin_nat_mul_eq_zero, integral_log_sin_half_mul_sin, mul_zero, add_zero]

/-- The **kernel of the logarithmic single layer operator** of the unit circle:
$$k(t, s) = -\frac{1}{\pi} \log \bigl|2 e^{-1/2} \sin\bigl((t - s)/2\bigr)\bigr|.$$
Here $|2 \sin((t - s)/2)| = |e^{it} - e^{is}|$ is the chord length.

Where $\sin((t - s)/2) = 0$, the value is $0$, because `Real.log 0 = 0`. -/
noncomputable def logSingleLayerKernel (t s : ℝ) : ℝ :=
  -(1 / π) * Real.log |2 * Real.exp (-(1 / 2)) * Real.sin ((t - s) / 2)|

/-- Where $\sin((t - s)/2) \ne 0$, the kernel is $k(t, s) = -\pi^{-1} \ell(t - s)$, with $\ell$ =
`logChord`. -/
theorem logSingleLayerKernel_eq {t s : ℝ} (h : Real.sin ((t - s) / 2) ≠ 0) :
    logSingleLayerKernel t s = -(1 / π) * logChord (t - s) := by
  rw [logSingleLayerKernel, logChord_eq_log_abs _ h]

/-- The **logarithmic single layer operator** on real functions
$\varphi : \mathbb{R} \to \mathbb{R}$:
$$A\varphi(t) = \int_0^{2\pi} k(t, s) \varphi(s) \, ds,$$
where $k$ is the kernel `logSingleLayerKernel`. -/
noncomputable def logSingleLayer (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..(2 * π), logSingleLayerKernel t s * φ s

/-- The logarithmic single layer operator on complex functions
$\varphi : \mathbb{R} \to \mathbb{C}$, $A\varphi(t) = \int_0^{2\pi} k(t, s) \varphi(s) \, ds$,
so that the Fourier modes $t \mapsto e^{imt}$ are admissible arguments. -/
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

/-- For a $2\pi$-periodic $\varphi$, $A\varphi(t) = -\pi^{-1} \int_0^{2\pi} \ell(y) \varphi(t - y)
\, dy$, by the change of variable $s \mapsto t - s$ and the periodicity of the integrand. -/
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

/-- **The logarithmic single layer operator multiplies a shifted cosine mode by $1/\max(1, m)$.**
For $m \in \mathbb{N}$ and $c, t \in \mathbb{R}$,
$$A\bigl(\cos(m \cdot + c)\bigr)(t) = \frac{\cos(mt + c)}{\max(1, m)}.$$
The cosine and sine modes are the cases $c = 0$ and $c = -\pi/2$. -/
theorem logSingleLayer_cos_add (m : ℕ) (c t : ℝ) :
    logSingleLayer (fun s => Real.cos ((m : ℝ) * s + c)) t
      = Real.cos ((m : ℝ) * t + c) / max 1 m := by
  have hper : Function.Periodic (fun s => Real.cos ((m : ℝ) * s + c)) (2 * π) := by
    intro s
    change Real.cos ((m : ℝ) * (s + 2 * π) + c) = Real.cos ((m : ℝ) * s + c)
    rw [show (m : ℝ) * (s + 2 * π) + c = ((m : ℝ) * s + c) + (m : ℕ) * (2 * π) by ring,
      Real.cos_add_nat_mul_two_pi]
  rw [logSingleLayer_eq_of_periodic hper t]
  have hexp : ∀ y : ℝ, logChord y * Real.cos ((m : ℝ) * (t - y) + c)
      = Real.cos ((m : ℝ) * t + c) * (logChord y * Real.cos ((m : ℝ) * y))
        + Real.sin ((m : ℝ) * t + c) * (logChord y * Real.sin ((m : ℝ) * y)) := by
    intro y
    rw [show (m : ℝ) * (t - y) + c = ((m : ℝ) * t + c) - (m : ℝ) * y by ring, Real.cos_sub]
    ring
  rw [intervalIntegral.integral_congr (fun y _ => hexp y),
    intervalIntegral.integral_add
      ((intervalIntegrable_logChord_mul (by fun_prop)).const_mul _)
      ((intervalIntegrable_logChord_mul (by fun_prop)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_logChord_mul_cos, integral_logChord_mul_sin, mul_zero, add_zero]
  field_simp

/-- **The logarithmic single layer operator multiplies the cosine mode by $1/\max(1, m)$.** For
$m \in \mathbb{N}$ and $t \in \mathbb{R}$,
$$A\bigl(\cos(m \cdot)\bigr)(t) = \frac{\cos(mt)}{\max(1, m)}.$$
-/
theorem logSingleLayer_cos (m : ℕ) (t : ℝ) :
    logSingleLayer (fun s => Real.cos ((m : ℝ) * s)) t = Real.cos ((m : ℝ) * t) / max 1 m := by
  simpa using logSingleLayer_cos_add m 0 t

/-- **The logarithmic single layer operator multiplies the sine mode by $1/\max(1, m)$.** For
$m \in \mathbb{N}$ and $t \in \mathbb{R}$,
$$A\bigl(\sin(m \cdot)\bigr)(t) = \frac{\sin(mt)}{\max(1, m)}.$$
-/
theorem logSingleLayer_sin (m : ℕ) (t : ℝ) :
    logSingleLayer (fun s => Real.sin ((m : ℝ) * s)) t = Real.sin ((m : ℝ) * t) / max 1 m := by
  have h := logSingleLayer_cos_add m (-(π / 2)) t
  simp only [← sub_eq_add_neg, Real.cos_sub_pi_div_two] at h
  exact h

/-! ### The integer Fourier modes -/

/-- The operator $A$ commutes with multiplication by a real constant:
$A(c\varphi)(t) = c \, A\varphi(t)$. -/
theorem logSingleLayer_const_mul (c : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    logSingleLayer (fun s => c * φ s) t = c * logSingleLayer φ t := by
  rw [logSingleLayer, logSingleLayer, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun s _ => by ring

/-- The operator $A$ commutes with negation: $A(-\varphi)(t) = -A\varphi(t)$. -/
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

/-- **The logarithmic single layer operator multiplies the cosine mode of an integer frequency by
$1/\max(1, |m|)$.** For $m \in \mathbb{Z}$ and $t \in \mathbb{R}$,
$$A\bigl(\cos(m \cdot)\bigr)(t) = \frac{\cos(mt)}{\max(1, |m|)}.$$
-/
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

/-- **The logarithmic single layer operator multiplies the sine mode of an integer frequency by
$1/\max(1, |m|)$.** For $m \in \mathbb{Z}$ and $t \in \mathbb{R}$,
$$A\bigl(\sin(m \cdot)\bigr)(t) = \frac{\sin(mt)}{\max(1, |m|)}.$$
-/
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

/-- For every $t \in \mathbb{R}$, the function $s \mapsto \ell(t - s)$ of `logChord` is integrable
on $[0, 2\pi]$. -/
theorem intervalIntegrable_logChord_sub (t : ℝ) :
    IntervalIntegrable (fun s => logChord (t - s)) volume 0 (2 * π) := by
  have h := (logChord_periodic.intervalIntegrable₀ (by positivity) intervalIntegrable_logChord
    (t - 2 * π) t).comp_sub_left t
  rw [sub_self, show t - (t - 2 * π) = 2 * π by ring] at h
  exact h.symm

/-- For every $t \in \mathbb{R}$ and every continuous $\varphi : \mathbb{R} \to \mathbb{R}$, the
function $s \mapsto k(t, s) \varphi(s)$ is integrable on $[0, 2\pi]$. -/
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

/-- **The Fourier diagonalization of the logarithmic single layer operator.** For $m \in \mathbb{Z}$
and $t \in \mathbb{R}$, the operator $A$ multiplies the mode $\psi_m(t) = e^{imt}$ by
$1/\max(1, |m|)$:
$$A\psi_m(t) = \frac{e^{imt}}{\max(1, |m|)}.$$
In particular, $A$ fixes the constant mode $\psi_0$.

The operator on complex functions is `logSingleLayerC`. -/
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
