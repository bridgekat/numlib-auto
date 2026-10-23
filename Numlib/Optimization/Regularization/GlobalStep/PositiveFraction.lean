import Numlib.Optimization.Regularization.GlobalStep

/-!
# Positive fractions from actual strict model improvement

A strictly improving candidate attains a positive fraction of the genuine global gap.
-/

namespace ModelDecrease
variable {E : Type*} [NormedAddCommGroup E]
/-- Any actual strict improvement attains some positive global fraction when the model has a
global minimum. -/
theorem exists_positive_fraction_of_strict_decrease {m : E → ℝ} {s z : E}
    (hmin : ∀ u, m z ≤ m u) (hs : m s < m 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ApproximateGlobalStep m μ s := by
  let μ := (m 0 - m s) / (m 0 - m z)
  have hz : 0 < m 0 - m z := lt_of_lt_of_le (sub_pos.mpr hs) (sub_le_sub_left (hmin s) _)
  have hμ : 0 < μ := div_pos (sub_pos.mpr hs) hz
  refine ⟨μ, hμ, (div_le_one hz).mpr (sub_le_sub_left (hmin s) _), ?_⟩
  apply (approximateGlobalStep_iff_of_isMin hμ.le hmin).mpr
  dsimp [μ]
  exact le_of_eq (div_mul_cancel₀ _ hz.ne')
end ModelDecrease
