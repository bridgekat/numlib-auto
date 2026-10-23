/-
Upstreaming candidate: an elementary real beta integral with one natural exponent.
Natural home: Mathlib.Analysis.SpecialFunctions.Integrals.Basic.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# Real beta kernels and finite shifted factorials

The denominator is the finite product `(k + β)! = ∏ i = 1, …, k, (i + β)`.
Integration by parts evaluates the beta kernel without the complex gamma function.
The real exponent may be any nonnegative number, including zero.
-/

open Set intervalIntegral
open scoped BigOperators

namespace Real
/-- Finite shifted factorial `(k+β)! = ∏_(i=1)^k (i+β)`. -/
noncomputable def shiftedFactorial (k : ℕ) (β : ℝ) : ℝ :=
  ∏ i ∈ Finset.range k, (β + (i : ℝ) + 1)
/-- The empty shifted factorial equals one. -/
@[simp] theorem shiftedFactorial_zero (β : ℝ) : shiftedFactorial 0 β = 1 := by
  simp [shiftedFactorial]
/-- Splitting off the first factor shifts the real parameter by one. -/
theorem shiftedFactorial_succ (k : ℕ) (β : ℝ) :
    shiftedFactorial (k + 1) β = (β + 1) * shiftedFactorial k (β + 1) := by
  rw [shiftedFactorial, Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  ring
/-- All factors are positive at a nonnegative shift. -/
theorem shiftedFactorial_pos (k : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 < shiftedFactorial k β := by
  unfold shiftedFactorial
  exact Finset.prod_pos fun i _ => by positivity
/-- At shift zero the finite product is the usual factorial. -/
@[simp] theorem shiftedFactorial_nat_zero (k : ℕ) : shiftedFactorial k 0 = (k.factorial : ℝ) := by
  simp only [shiftedFactorial, zero_add, Nat.factorial_eq_prod_range_add_one,
    Nat.cast_prod, Nat.cast_add, Nat.cast_one]
/-- At shift one the finite product is the next factorial. -/
@[simp] theorem shiftedFactorial_one (k : ℕ) : shiftedFactorial k 1 = ((k + 1).factorial : ℝ) := by
  have h := shiftedFactorial_succ k 0
  simpa using h.symm
/-- The real beta integral with a nonnegative real exponent and a natural exponent. -/
theorem integral_rpow_mul_one_sub_pow (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ∫ t in (0 : ℝ)..1, t ^ β * (1 - t) ^ n = n.factorial / shiftedFactorial (n + 1) β := by
  induction n generalizing β with
  | zero =>
    rw [show shiftedFactorial (0 + 1) β = β + 1 by simp [shiftedFactorial]]
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    rw [integral_rpow (Or.inl (by linarith)), one_rpow,
      zero_rpow (by linarith : β + 1 ≠ 0), sub_zero]
  | succ n ih =>
    have hu : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (1 - t) ^ (n + 1))
        (-((n + 1 : ℝ) * (1 - t) ^ n)) t := by
      intro t _
      exact (((hasDerivAt_id t).const_sub 1).pow (n + 1)).congr_deriv (by
        simp only [id_eq]
        push_cast
        ring)
    have hβ1 : β + 1 ≠ 0 := by positivity
    have hv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t ^ (β + 1) / (β + 1))
        (t ^ β) t := by
      intro t _
      have hd := (Real.hasDerivAt_rpow_const (x := t) (p := β + 1)
        (Or.inr (by linarith))).div_const (β + 1)
      convert hd using 1
      rw [add_sub_cancel_right]
      field_simp
    have hparts := integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun t : ℝ => -((n + 1 : ℝ) * (1 - t) ^ n)).intervalIntegrable _ _)
      ((Real.continuous_rpow_const hβ).intervalIntegrable _ _)
    have hparts' : (∫ t in (0 : ℝ)..1, (1 - t) ^ (n + 1) * t ^ β) =
        ((n + 1 : ℝ) / (β + 1)) * ∫ t in (0 : ℝ)..1, t ^ (β + 1) * (1 - t) ^ n := by
      rw [hparts]
      simp only [sub_self, zero_pow (Nat.succ_ne_zero n), zero_mul, one_rpow,
        sub_zero, one_pow, zero_rpow hβ1, zero_div, mul_zero, zero_sub]
      rw [← integral_const_mul, ← integral_neg]
      apply integral_congr
      intro t _
      ring
    calc (∫ t in (0 : ℝ)..1, t ^ β * (1 - t) ^ (n + 1)) =
        ∫ t in (0 : ℝ)..1, (1 - t) ^ (n + 1) * t ^ β := integral_congr fun _ _ => mul_comm _ _
      _ = ((n + 1 : ℝ) / (β + 1)) *
          ((n.factorial : ℝ) / shiftedFactorial (n + 1) (β + 1)) := by
        rw [hparts', ih (by linarith)]
      _ = ((n + 1).factorial : ℝ) / shiftedFactorial (n + 1 + 1) β := by
        rw [shiftedFactorial_succ (n + 1) β, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp
end Real
