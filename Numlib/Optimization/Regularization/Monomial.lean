import Mathlib.Analysis.MeanInequalities

/-!
# Exact global minimizers of regularized monomials

Weighted arithmetic-geometric mean proves global minimization for arbitrary
integer model degree and criticality order. Negative scalar trials are handled
by their absolute value, so even and odd monomials are both covered.
-/

namespace MonomialRegularization

/-- The homogeneous weighted-power inequality underlying the actual global
minimum of a negative monomial plus a higher positive norm power. -/
theorem weighted_power {p q : ℕ} (hqp : q ≤ p) {x t : ℝ}
    (hx : 0 ≤ x) (ht : 0 ≤ t) :
    ((p + 1 : ℕ) : ℝ) * t ^ (p - q + 1) * x ^ q ≤
      (q : ℝ) * x ^ (p + 1) + (p - q + 1 : ℕ) * t ^ (p + 1) := by
  have hp : (0 : ℝ) < (p + 1 : ℕ) := by positivity
  have hexp : (p + 1 : ℝ) = (q : ℝ) + (p - q + 1 : ℕ) := by
    exact_mod_cast (show p + 1 = q + (p - q + 1) by omega)
  have hw := Real.geom_mean_le_arith_mean2_weighted
    (show (0 : ℝ) ≤ (q : ℝ) / (p + 1 : ℕ) by positivity)
    (show (0 : ℝ) ≤ (p - q + 1 : ℕ) / (p + 1 : ℕ) by positivity)
    (pow_nonneg hx (p + 1)) (pow_nonneg ht (p + 1))
    (show (q : ℝ) / (p + 1 : ℕ) + (p - q + 1 : ℕ) / (p + 1 : ℕ) = 1 by
      rw [← add_div]
      exact (div_eq_one_iff_eq hp.ne').mpr (by simpa using hexp.symm))
  have hxpow : (x ^ (p + 1)) ^ ((q : ℝ) / (p + 1 : ℕ)) = x ^ q := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hx]
    rw [show ((p + 1 : ℕ) : ℝ) * ((q : ℝ) / (p + 1 : ℕ)) = q by field_simp]
    rw [Real.rpow_natCast]
  have htpow : (t ^ (p + 1)) ^ (((p - q + 1 : ℕ) : ℝ) / (p + 1 : ℕ)) =
      t ^ (p - q + 1) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul ht]
    rw [show ((p + 1 : ℕ) : ℝ) * (((p - q + 1 : ℕ) : ℝ) / (p + 1 : ℕ)) =
        (p - q + 1 : ℕ) by field_simp]
    rw [Real.rpow_natCast]
  rw [hxpow, htpow] at hw
  have hh := mul_le_mul_of_nonneg_left hw hp.le
  convert hh using 1 <;> field_simp

/-- The balanced positive step globally minimizes the scalar regularized
monomial, including arbitrary negative competing trials. -/
theorem global_min {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) {t c b : ℝ}
    (ht : 0 ≤ t) (hc : 0 ≤ c) (u : ℝ) :
    b + c * (|t| ^ (p + 1) / (p + 1 : ℕ) - t ^ (p - q + 1) * t ^ q / q) ≤
      b + c * (|u| ^ (p + 1) / (p + 1 : ℕ) - t ^ (p - q + 1) * u ^ q / q) := by
  have hw := weighted_power hqp (abs_nonneg u) ht
  have hu : u ^ q ≤ |u| ^ q := by simpa only [abs_pow] using le_abs_self (u ^ q)
  have hprod := mul_le_mul_of_nonneg_left hu (pow_nonneg ht (p - q + 1))
  have hpq : p - q + 1 + q = p + 1 := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpR : (0 : ℝ) < (p + 1 : ℕ) := by positivity
  have hcoeff : ((p - q + 1 : ℕ) : ℝ) = (p + 1 : ℕ) - (q : ℝ) := by
    have he : p - q + 1 + q = p + 1 := by omega
    have heR : ((p - q + 1 : ℕ) : ℝ) + (q : ℝ) = (p + 1 : ℕ) := by
      exact_mod_cast he
    linarith
  have hbase : |t| ^ (p + 1) / (p + 1 : ℕ) - t ^ (p - q + 1) * t ^ q / q ≤
      |u| ^ (p + 1) / (p + 1 : ℕ) - t ^ (p - q + 1) * u ^ q / q := by
    rw [abs_of_nonneg ht, ←pow_add, hpq]
    apply (mul_le_mul_iff_left₀ (mul_pos hpR hqR)).mp
    field_simp
    rw [hcoeff] at hw
    nlinarith
  exact add_le_add_right (mul_le_mul_of_nonneg_left hbase hc) b

end MonomialRegularization
