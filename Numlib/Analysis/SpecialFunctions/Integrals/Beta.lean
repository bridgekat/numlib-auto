/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`, beside `integral_pow`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Beta integral with natural exponents

`∫₀¹ xᵃ (1 - x)ᵇ dx = a! b!/(a + b + 1)!` (`integral_pow_mul_one_sub_pow`), by induction on `b`
with one integration by parts per step. Mathlib has the complex Beta function
(`Complex.betaIntegral`, through the Gamma function); this is the elementary natural-exponent case,
used for the remainder of Padé approximants and for Dirichlet's integral on a triangle.
-/

open Set intervalIntegral
open scoped Nat

/-- **The Beta integral with natural exponents**: `∫₀¹ xᵃ (1 - x)ᵇ dx = a! b!/(a + b + 1)!`, by
induction on `b` with one integration by parts per step. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b = (a ! * b ! : ℝ) / (a + b + 1)! := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero a), sub_zero,
      Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  | succ b ih =>
    -- integration by parts: `u = (1 - x)^(b+1)`, `v = x^(a+1)/(a+1)`
    have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => (1 - x) ^ (b + 1))
        (-((b + 1 : ℝ) * (1 - x) ^ b)) x := by
      intro x _
      exact (((hasDerivAt_id' x).const_sub 1).pow (b + 1)).congr_deriv (by push_cast; ring)
    have ha1 : ((a : ℝ) + 1) ≠ 0 := by positivity
    have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ (a + 1) / (a + 1)) (x ^ a) x := by
      intro x _
      exact (((hasDerivAt_id' x).pow (a + 1)).div_const ((a : ℝ) + 1)).congr_deriv
        (by push_cast; field_simp)
    have hparts := integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -((b + 1 : ℝ) * (1 - x) ^ b)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => x ^ a).intervalIntegrable _ _)
    have e1 : ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1)
        = ∫ x in (0 : ℝ)..1, (1 - x) ^ (b + 1) * x ^ a :=
      integral_congr fun x _ => mul_comm _ _
    have e2 : ∫ x in (0 : ℝ)..1, -((b + 1 : ℝ) * (1 - x) ^ b) * (x ^ (a + 1) / (a + 1))
        = -((b + 1 : ℝ) / (a + 1)) * ∫ x in (0 : ℝ)..1, x ^ (a + 1) * (1 - x) ^ b := by
      rw [← intervalIntegral.integral_const_mul]
      exact integral_congr fun x _ => by ring
    rw [e1, hparts, e2, ih (a + 1)]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero b), zero_mul, one_pow, sub_zero, zero_sub,
      zero_pow (Nat.succ_ne_zero a), zero_div, mul_zero]
    rw [show a + 1 + b + 1 = (a + b + 1) + 1 by ring,
      show a + (b + 1) + 1 = (a + b + 1) + 1 by ring, Nat.factorial_succ (a + b + 1),
      Nat.factorial_succ b, Nat.factorial_succ a]
    push_cast
    field_simp
