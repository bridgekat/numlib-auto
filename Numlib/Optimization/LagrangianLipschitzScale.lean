import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Euclidean scaling of weighted Lipschitz constants

The norm of an augmented multiplier bounds the sum norm. This comparison converts separate
scalar and vector Lipschitz constants into the common tested-radius budget, with an explicit
zero-constant branch.
-/

namespace Real
/-- The Euclidean two-coordinate multiplier scale controls its sum norm. -/
theorem one_add_le_sqrt_two_mul_sqrt_one_add_sq {r : ℝ} :
    1 + r ≤ sqrt 2 * sqrt (1 + r ^ 2) := by
  have h2 : (sqrt 2) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hr2 : (sqrt (1 + r ^ 2)) ^ 2 = 1 + r ^ 2 := sq_sqrt (by positivity)
  have hp : 0 ≤ sqrt 2 * sqrt (1 + r ^ 2) := by positivity
  nlinarith [sq_nonneg (r - 1)]
end Real
namespace Optimization.ConstrainedTaylorCriticality
/-- The weighted scalar/vector constant is controlled by the Euclidean scale. -/
theorem weighted_constant_le_scale {a b r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    a + r * b ≤ Real.sqrt 2 * max a b * Real.sqrt (1 + r ^ 2) := by
  calc
    _ ≤ max a b * (1 + r) := by
      have h := mul_le_mul_of_nonneg_left (le_max_right a b) hr
      nlinarith [le_max_left a b]
    _ ≤ max a b * (Real.sqrt 2 * Real.sqrt (1 + r ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.one_add_le_sqrt_two_mul_sqrt_one_add_sq)
        (ha.trans (le_max_left a b))
    _ = _ := by ring
/-- The weighted radius budget has a separate branch when both constants vanish. -/
theorem weighted_constant_mul_le_scale {a b r R B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hsmall : max a b = 0 ∨ R ≤ B / (Real.sqrt 2 * max a b)) :
    (a + r * b) * R ≤ B * Real.sqrt (1 + r ^ 2) := by
  by_cases hz : max a b = 0
  · have ha0 : a = 0 := le_antisymm (by simpa only [hz] using le_max_left a b) ha
    have hb0 : b = 0 := le_antisymm (by simpa only [hz] using le_max_right a b) hb
    simp only [ha0, hb0, mul_zero, add_zero, zero_mul]
    exact mul_nonneg hB (Real.sqrt_nonneg _)
  · have hs := hsmall.resolve_left hz
    have hp : 0 < Real.sqrt 2 * max a b :=
      mul_pos (by positivity) (lt_of_le_of_ne (ha.trans (le_max_left a b)) (Ne.symm hz))
    have hd := (le_div_iff₀ hp).mp hs
    calc
      _ ≤ (Real.sqrt 2 * max a b * Real.sqrt (1 + r ^ 2)) * R :=
        mul_le_mul_of_nonneg_right (weighted_constant_le_scale ha hr) hR
      _ = (R * (Real.sqrt 2 * max a b)) * Real.sqrt (1 + r ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _)

end Optimization.ConstrainedTaylorCriticality
