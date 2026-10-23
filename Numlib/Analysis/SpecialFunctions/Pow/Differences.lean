import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Differences of real powers

A convex-power secant is bounded by its right tangent slope. Applying this to
`a^q` and `b^q` compares increments of any two positive ordered powers `q ≤ p`.
The estimate includes the degenerate case `a = b = 0` with real division.
-/

namespace Real

/-- The secant difference of a convex power is bounded by the right tangent slope. -/
theorem rpow_sub_le_mul_sub {a b p : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hp : 1 ≤ p) : a ^ p - b ^ p ≤ p * a ^ (p - 1) * (a - b) := by
  rcases eq_or_lt_of_le hba with rfl | hba
  · simp
  · have ha : 0 < a := hb.trans_lt hba
    have h := (convexOn_rpow hp).slope_le_of_hasDerivAt hb ha.le hba
      (hasDerivAt_rpow_const (Or.inl ha.ne'))
    rw [slope_def_field] at h
    exact (div_le_iff₀ (sub_pos.mpr hba)).mp h

/-- A difference between small powers controls the difference between larger powers. -/
theorem rpow_sub_div_le_rpow_sub {a b q p : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hq : 0 < q) (hqp : q ≤ p) :
    (a ^ p - b ^ p) / ((p / q) * a ^ (p - q)) ≤ a ^ q - b ^ q := by
  rcases eq_or_lt_of_le (hb.trans hba) with ha | ha
  · have hb0 : b = 0 := le_antisymm (ha ▸ hba) hb
    subst a; subst b
    simp [Real.zero_rpow (ne_of_gt hq), Real.zero_rpow (ne_of_gt (hq.trans_le hqp))]
  · have hA : 0 < a ^ q := rpow_pos_of_pos ha q
    have hB : 0 ≤ b ^ q := rpow_nonneg hb q
    have hBA : b ^ q ≤ a ^ q := rpow_le_rpow hb hba hq.le
    have hratio : 1 ≤ p / q := (le_div_iff₀ hq).mpr (by simpa using hqp)
    have h := rpow_sub_le_mul_sub hB hBA hratio
    have hAeq : (a ^ q) ^ (p / q) = a ^ p := by
      rw [← rpow_mul ha.le]
      congr 1
      field_simp
    have hBeq : (b ^ q) ^ (p / q) = b ^ p := by
      rw [← rpow_mul hb]
      congr 1
      field_simp
    have hDeq : (a ^ q) ^ (p / q - 1) = a ^ (p - q) := by
      rw [← rpow_mul ha.le]
      congr 1
      field_simp
    rw [hAeq, hBeq, hDeq] at h
    have hd : 0 < (p / q) * a ^ (p - q) :=
      mul_pos (div_pos (hq.trans_le hqp) hq) (rpow_pos_of_pos ha _)
    exact (div_le_iff₀ hd).mpr (by simpa [mul_comm] using h)

end Real

