import Mathlib.Algebra.Order.Field.Basic

/-!
# Positive ordered-field reciprocal extrema

Taking reciprocals exchanges a minimum of positive values with their maximum.
-/

/-- Taking the reciprocal exchanges the positive minimum with the reciprocal maximum. -/
theorem one_div_min_eq_max {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b : K} (ha : 0 < a) (hb : 0 < b) :
    1 / min a b = max (1 / a) (1 / b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (one_div_le_one_div_of_le ha h)]
  · rw [min_eq_right h, max_eq_right (one_div_le_one_div_of_le hb h)]
