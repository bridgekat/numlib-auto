import Numlib.Optimization.Regularization.Cubic.LocalCountCounterexample
import Numlib.Optimization.Composite.SmoothExecution
import Numlib.Optimization.Composite.ZeroReturnCounterexample
import Mathlib.Tactic
/-!
# A Lipschitz subadditive outer function that is nonconvex

Truncating absolute value at one preserves its unit Lipschitz and subadditivity
bounds, while the midpoint between zero and two disproves convexity.
-/

namespace Composite.TruncatedAbs
/-- The absolute value truncated at height one. -/
noncomputable def h (x : ℝ) : ℝ := min |x| 1
/-- The outer function vanishes at zero. -/
theorem zero : h 0 = 0 := by norm_num [h]
/-- The truncated outer function is globally unit Lipschitz. -/
theorem lipschitz : LipschitzWith 1 h := by
  exact ZeroReturnCounterexample.outer_properties.1.min_const 1

/-- Truncation preserves subadditivity of absolute value. -/
theorem subadditive (x y : ℝ) : h (x+y) ≤ h x + h y := by
  have hx : 0 ≤ |x| := abs_nonneg _
  have hy : 0 ≤ |y| := abs_nonneg _
  by_cases hxl : |x| ≤ 1
  · by_cases hyl : |y| ≤ 1
    · simpa only [h, min_eq_left hxl, min_eq_left hyl] using
        (min_le_left |x+y| 1).trans (abs_add_le x y)
    · rw [h, h, h, min_eq_left hxl, min_eq_right (not_le.mp hyl).le]
      exact (min_le_right _ _).trans (by linarith)
  · rw [h, h, h, min_eq_right (not_le.mp hxl).le]
    exact (min_le_right _ _).trans (by have := le_min hy (by norm_num : (0:ℝ) ≤ 1);linarith)
/-- The midpoint inequality fails between zero and two. -/
theorem not_convex : ¬ConvexOn ℝ Set.univ h := by
  intro hc
  have hh := hc.2 (show (0 : ℝ) ∈ Set.univ by trivial)
    (show (2 : ℝ) ∈ Set.univ by trivial)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num)
  norm_num [h] at hh
end Composite.TruncatedAbs
