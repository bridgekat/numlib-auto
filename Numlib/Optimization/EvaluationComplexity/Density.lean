import Numlib.Optimization.EvaluationComplexity.Updates

/-!
# Translating inclusive iteration-density bounds

The source inclusive prefix at index k contains k+1 trials. Its additive
constant increases by one when counting the first N trials instead.
-/

namespace EvaluationComplexity
/-- An inclusive density rule implies the half-open rule with its exact additive correction. -/
theorem exclusive_density_of_inclusive {S : Set ℕ} {κR κA : ℝ} (hA : 0 ≤ κA)
    (h : ∀ k : ℕ, (k : ℝ) ≤ κR * (successfulIterations S (k + 1)).card + κA) :
    ∀ N : ℕ, (N : ℝ) ≤ κR * (successfulIterations S N).card + (κA + 1) := by
  intro N
  cases N with
  | zero =>
    simp only [Nat.cast_zero, successfulIterations, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty, mul_zero, zero_add]
    linarith
  | succ k =>
    have hh := h k
    push_cast
    linarith
end EvaluationComplexity
