/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of `cos (m x)` and `sin (m x)` over a full period

Over `[0, 2π]` the modes `cos (m x)`, `m ≠ 0`, and `sin (m x)` integrate to zero
(`integral_cos_nat_mul_eq_zero`, `integral_sin_nat_mul_eq_zero`), by Mathlib's `integral_cos`
and `integral_sin` after the change of variables `x ↦ m x`.
-/

open Real

/-- `∫_0^{2π} cos (m x) dx = 0` for a nonzero natural frequency `m`. -/
theorem integral_cos_nat_mul_eq_zero {m : ℕ} (hm : m ≠ 0) :
    ∫ y in (0 : ℝ)..(2 * π), Real.cos ((m : ℝ) * y) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hm', integral_cos, mul_zero,
    Real.sin_zero, show (m : ℝ) * (2 * π) = ((2 * m : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi]
  simp

/-- `∫_0^{2π} sin (m x) dx = 0` for every natural frequency `m`. -/
theorem integral_sin_nat_mul_eq_zero (m : ℕ) :
    ∫ y in (0 : ℝ)..(2 * π), Real.sin ((m : ℝ) * y) = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
    rw [intervalIntegral.integral_comp_mul_left (f := Real.sin) hm', integral_sin, mul_zero,
      Real.cos_zero, Real.cos_nat_mul_two_pi]
    simp
