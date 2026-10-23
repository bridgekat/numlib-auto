import Numlib.Optimization.LineSearch.Backtracking

/-!
# Positive and monotone geometric backtracking radii

The same geometric candidates serve line searches and finite model-criticality
radius loops. Their positivity and monotonicity do not depend on acceptance tests.
-/

namespace BacktrackingGradient

/-- Every geometric candidate from a positive initial radius is positive. -/
theorem step_pos {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (t : ℕ) : 0 < step δ₀ t :=
  div_pos hδ₀ (by positivity)

/-- Geometric candidates decrease with the number of halvings. -/
theorem step_antitone {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) : Antitone (step δ₀) := by
  apply antitone_nat_of_succ_le
  intro t
  rw [step_succ]
  exact div_le_self (div_nonneg hδ₀ (by positivity)) (by norm_num)

end BacktrackingGradient
