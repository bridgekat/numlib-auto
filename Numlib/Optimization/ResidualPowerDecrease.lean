import Numlib.Analysis.SpecialFunctions.Pow.Difference
import Numlib.Optimization.ResidualDescentExponent
import Mathlib.Tactic

/-!
# Normalized residual-power decrease

These scalar identities convert objective decrease into normalized derivative decrease. A
positive residual norm makes the normalization invertible.
-/

namespace Optimization

/-- Normalization by a positive residual power cancels after any real power. -/
theorem rpow_normalized_mul {c b ell alpha : ℝ} (hc : 0 ≤ c) (hb : 0 < b) :
    (c / b ^ (ell - 1)) ^ alpha * b ^ ((ell - 1) * alpha) = c ^ alpha := by
  rw [Real.div_rpow hc (Real.rpow_nonneg hb.le _), Real.rpow_mul hb.le]
  exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hb _) _))

/-- Multiplying true objective decrease by `ell` produces the exact normalized power bound. -/
theorem normalized_power_decrease {a b ell c alpha kappa : ℝ} (hell : 0 < ell)
    (hb : 0 < b) (hc : 0 ≤ c)
    (h : kappa * c ^ alpha ≤ a ^ ell / ell - b ^ ell / ell) :
    kappa * ell * (c / b ^ (ell - 1)) ^ alpha * b ^ ((ell - 1) * alpha) ≤
      a ^ ell - b ^ ell := by
  have hh := mul_le_mul_of_nonneg_right h hell.le
  rw [← sub_div, div_mul_cancel₀ _ hell.ne'] at hh
  calc
    kappa * ell * (c / b ^ (ell - 1)) ^ alpha * b ^ ((ell - 1) * alpha) =
        kappa * c ^ alpha * ell := by rw [mul_assoc, mul_assoc, rpow_normalized_mul hc hb]; ring
    _ ≤ _ := hh

/-- Positive scaling commutes with the nonnegative negative part. -/
theorem max_neg_div_eq {c d : ℝ} (hd : 0 ≤ d) :
    max 0 (-(c / d)) = max 0 (-c) / d := by
  simpa only [zero_div, neg_div] using max_div_div_right hd 0 (-c)

/-- The relative-successor branch of a residual-root decrease estimate, for arbitrary real
model degree and derivative order with positive denominator. -/
theorem residual_root_decrease {p j ell a b beta c kappa : ℝ} {i : ℕ}
    (hD : 0 < p - j + 1) (hell : 1 ≤ ell) (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hbeta : 0 < beta) (hrel : beta * a ≤ b) (hc : 0 ≤ c) (hkappa : 0 ≤ kappa)
    (hp : 0 ≤ p + 1)
    (hdec : kappa * ell * c ^ ((p + 1) / (p - j + 1)) *
      b ^ ((ell - 1) * ((p + 1) / (p - j + 1))) ≤ a ^ ell - b ^ ell) :
    (kappa * beta ^ ((ell - 1) * ((p + 1) / (p - j + 1))) / (2 : ℝ) ^ i) *
      c ^ ((p + 1) / (p - j + 1)) / a ^ residualDescentExponent p ell i j ≤
        a ^ (1 / (2 : ℝ) ^ i) - b ^ (1 / (2 : ℝ) ^ i) := by
  have ht : 0 < (1 : ℝ) / (2 : ℝ) ^ i := by positivity
  have ht1 : (1 : ℝ) / (2 : ℝ) ^ i ≤ 1 :=
    (div_le_one (by positivity : (0 : ℝ) < 2 ^ i)).2 (one_le_pow₀ (by norm_num))
  have hv : 0 ≤ (ell - 1) * ((p + 1) / (p - j + 1)) := by positivity
  have h := Real.root_decrease_of_power_decrease ha hb hba hbeta hrel ht
    (ht1.trans hell) hv hkappa hdec hc
  rw [residualDescentExponent_eq_power_difference hD.ne']
  convert h using 1
  ring

end Optimization
