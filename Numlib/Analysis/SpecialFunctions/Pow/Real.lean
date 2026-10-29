/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Pow.Real`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Comparing real and natural powers

`Real.rpow_div_le_pow_of_le_pow`: from `a ≤ t^m` one gets `a^{n/m} ≤ t^n` (`a, t ≥ 0`, `m > 0`).
This is the step converting a lower bound on a step length `‖s‖^m ≥ a` into a lower bound on a
decrease `‖s‖^n` in the complexity analyses of regularization methods.
-/

namespace Real

/-- `a^{n/m} ≤ t^n` from `a ≤ t^m`, for `a, t ≥ 0` and `m > 0`. -/
theorem rpow_div_le_pow_of_le_pow {a t : ℝ} {m n : ℕ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hm : 0 < m)
    (h : a ≤ t ^ m) : a ^ ((n : ℝ) / m) ≤ t ^ n := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  calc a ^ ((n : ℝ) / m) ≤ (t ^ m) ^ ((n : ℝ) / m) := by gcongr
    _ = t ^ n := by
        rw [← Real.rpow_natCast t m, ← Real.rpow_mul ht, mul_div_cancel₀ _ hm', Real.rpow_natCast]

end Real
