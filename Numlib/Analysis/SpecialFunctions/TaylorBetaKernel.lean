import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The beta kernel with one natural exponent

The real beta integral specializes to a factorial divided by a finite product.
This normalization is useful for sharp Taylor estimates with fractional exponents.
-/

open Set
open scoped Nat

/-- The beta kernel for a nonnegative real exponent and a natural power.
The endpoint case `β = 0` uses the usual convention `0 ^ 0 = 1`. -/
theorem integral_rpow_mul_one_sub_pow {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    (∫ t : ℝ in 0..1, t ^ β * (1 - t) ^ n) =
      (n ! : ℝ) / ∏ i ∈ Finset.range (n + 1), (((i + 1 : ℕ) : ℝ) + β) := by
  have h := Complex.betaIntegral_eval_nat_add_one_right
    (u := (β + 1 : ℝ)) (by simpa using (show 0 < β + 1 by linarith)) n
  have hi : (∫ t : ℝ in 0..1, ((t ^ β * (1 - t) ^ n : ℝ) : ℂ)) =
      Complex.betaIntegral (β + 1) (n + 1) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1, Complex.ofReal_pow]
    push_cast
    simp only [add_sub_cancel_right]
    rw [← Complex.cpow_natCast]
  rw [intervalIntegral.integral_ofReal] at hi
  push_cast at h
  rw [h] at hi
  apply Complex.ofReal_injective
  rw [hi]
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring
