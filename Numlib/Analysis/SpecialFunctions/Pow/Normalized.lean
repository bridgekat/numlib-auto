import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Powers of normalized nonnegative quantities

Division and reconstruction preserve positive power bounds even when the
normalization vanishes, using the real division convention at zero.
-/

namespace Real
/-- Division by a nonnegative normalization followed by multiplication never increases a
nonnegative value. -/
theorem div_mul_normalizer_le {u w : ℝ} (hu : 0 ≤ u) : u / w * w ≤ u := by
  by_cases h : w = 0
  · simp [h,hu]
  · rw [div_mul_cancel₀ _ h]

/-- A positive power of a normalized nonnegative quantity reconstructs its original power,
with a valid inequality also at a zero normalization. -/
theorem normalized_rpow_mul_le {u w a : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (ha : 0 < a) :
    (u / w) ^ a * w ^ a ≤ u ^ a := by
  rw [←Real.mul_rpow (div_nonneg hu hw) hw]
  exact Real.rpow_le_rpow (mul_nonneg (div_nonneg hu hw) hw) (div_mul_normalizer_le hu) ha.le
end Real
