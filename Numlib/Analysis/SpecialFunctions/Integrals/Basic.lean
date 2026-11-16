/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of $\cos(mx)$ and $\sin(mx)$ over a full period

For a natural number $m$, this file proves that $\int_0^{2\pi} \cos(mx)\,dx = 0$ when $m \neq 0$,
and that $\int_0^{2\pi} \sin(mx)\,dx = 0$ for every $m$. The proofs use Mathlib's `integral_cos` and
`integral_sin` after the change of variables $x \mapsto mx$.

## Main results

* `integral_cos_nat_mul_eq_zero`: $\int_0^{2\pi} \cos(mx)\,dx = 0$ for a natural number $m \neq 0$.
* `integral_sin_nat_mul_eq_zero`: $\int_0^{2\pi} \sin(mx)\,dx = 0$ for every natural number $m$.
-/

open Real

/-- Let $m \neq 0$ be a natural number. Then
$$\int_0^{2\pi} \cos(mx)\,dx = 0.$$
-/
theorem integral_cos_nat_mul_eq_zero {m : ℕ} (hm : m ≠ 0) :
    ∫ y in (0 : ℝ)..(2 * π), Real.cos ((m : ℝ) * y) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hm', integral_cos, mul_zero,
    Real.sin_zero, show (m : ℝ) * (2 * π) = ((2 * m : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi]
  simp

/-- Let $m$ be a natural number. Then
$$\int_0^{2\pi} \sin(mx)\,dx = 0.$$
-/
theorem integral_sin_nat_mul_eq_zero (m : ℕ) :
    ∫ y in (0 : ℝ)..(2 * π), Real.sin ((m : ℝ) * y) = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
    rw [intervalIntegral.integral_comp_mul_left (f := Real.sin) hm', integral_sin, mul_zero,
      Real.cos_zero, Real.cos_nat_mul_two_pi]
    simp
