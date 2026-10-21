import Numlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Differences of real powers

A comparison of two positive exponents gives a lower bound on differences of root powers.
All assertions include a zero lower endpoint. The quotient version requires a positive upper
endpoint so its denominator is positive.
-/

namespace Real

/-- The tangent bound for a convex power, allowing a zero lower endpoint. -/
theorem rpow_sub_rpow_le_of_nonneg {a b q : ℝ} (hq : 1 ≤ q) (hb : 0 ≤ b)
    (hba : b ≤ a) : a ^ q - b ^ q ≤ q * a ^ (q - 1) * (a - b) := by
  rcases eq_or_lt_of_le hba with rfl | hba
  · simp
  rcases eq_or_lt_of_le hb with rfl | hb
  · rw [Real.zero_rpow (by linarith : q ≠ 0), sub_zero, sub_zero,
      mul_assoc, ← Real.rpow_add_one hba.ne', sub_add_cancel]
    exact le_mul_of_one_le_left (Real.rpow_nonneg hba.le _) hq
  · exact Real.rpow_sub_rpow_le hq hb hba

/-- Comparing exponent differences gives the basic cascading-root bound. -/
theorem rpow_sub_rpow_le_mul_root_sub {a b ell t : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (ht : 0 < t) (hte : t ≤ ell) :
    a ^ ell - b ^ ell ≤ (ell / t) * a ^ (ell - t) * (a ^ t - b ^ t) := by
  have ha := hb.trans hba
  have he : 1 ≤ ell / t := (le_div_iff₀ ht).2 (by simpa using hte)
  have h := rpow_sub_rpow_le_of_nonneg he (Real.rpow_nonneg hb t)
    (Real.rpow_le_rpow hb hba ht.le)
  have hm : t * (ell / t) = ell := by field_simp
  have hm' : t * (ell / t - 1) = ell - t := by field_simp
  simpa only [← Real.rpow_mul ha, ← Real.rpow_mul hb, hm, hm'] using h

/-- Quotient form of the difference comparison; the positive upper endpoint is explicit. -/
theorem root_sub_root_ge_div {a b ell t : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hba : b ≤ a) (ht : 0 < t) (hte : t ≤ ell) :
    (a ^ ell - b ^ ell) / ((ell / t) * a ^ (ell - t)) ≤ a ^ t - b ^ t := by
  apply (div_le_iff₀ (mul_pos (div_pos (ht.trans_le hte) ht)
    (Real.rpow_pos_of_pos ha _))).2
  simpa only [mul_comm] using rpow_sub_rpow_le_mul_root_sub hb hba ht hte

/-- A relative reduction gives a corresponding reduction in any positive root potential. -/
theorem root_sub_root_ge_of_le_mul {a b beta t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbeta : 0 ≤ beta) (hrel : b ≤ beta * a) (ht : 0 ≤ t) :
    (1 - beta ^ t) * a ^ t ≤ a ^ t - b ^ t := by
  have h := Real.rpow_le_rpow hb hrel ht
  rw [Real.mul_rpow hbeta ha] at h
  nlinarith

/-- A normalized power decrease and a weak relative lower bound on the successor give a
root-potential decrease with its exact residual exponent. -/
theorem root_decrease_of_power_decrease {a b beta ell t v c alpha kappa : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) (hbeta : 0 < beta)
    (hrel : beta * a ≤ b) (ht : 0 < t) (hte : t ≤ ell) (hv : 0 ≤ v)
    (hkappa : 0 ≤ kappa)
    (hdec : kappa * ell * c ^ alpha * b ^ v ≤ a ^ ell - b ^ ell) (hc : 0 ≤ c) :
    kappa * beta ^ v * t * c ^ alpha / a ^ (ell - t - v) ≤ a ^ t - b ^ t := by
  have hell : 0 < ell := ht.trans_le hte
  have hbp := Real.rpow_le_rpow (mul_nonneg hbeta.le ha.le) hrel hv
  have hcoef : 0 ≤ kappa * ell * c ^ alpha :=
    mul_nonneg (mul_nonneg hkappa hell.le) (Real.rpow_nonneg hc _)
  have hlow := (mul_le_mul_of_nonneg_left hbp hcoef).trans hdec
  have hD : 0 < (ell / t) * a ^ (ell - t) :=
    mul_pos (div_pos hell ht) (Real.rpow_pos_of_pos ha _)
  calc
    kappa * beta ^ v * t * c ^ alpha / a ^ (ell - t - v) =
        kappa * ell * c ^ alpha * (beta * a) ^ v /
          ((ell / t) * a ^ (ell - t)) := by
      rw [Real.rpow_sub ha, Real.mul_rpow hbeta.le ha.le]
      field_simp
    _ ≤ (a ^ ell - b ^ ell) / ((ell / t) * a ^ (ell - t)) :=
      div_le_div_of_nonneg_right hlow hD.le
    _ ≤ a ^ t - b ^ t := root_sub_root_ge_div ha hb hba ht hte

end Real
