import Numlib.Optimization.Composite.ModelMinimum
import Numlib.Optimization.Regularization.GlobalGap

/-!
# Strict composite returns attain a positive global-gap fraction

The actual regularized composite model attains its global minimum. Therefore a
strictly improving outer return satisfies some positive global-gap fraction.
At a zero-improvement return that fraction additionally requires global
minimality of the starting point.
-/

namespace Composite
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every strictly improving actual composite model return attains a positive
fraction of its genuine global model gap. -/
theorem exists_fraction_of_strict_model_decrease (f : E → ℝ) (c : E → F)
    {h : F → ℝ} {K : NNReal} (hh : LipschitzWith K h) (p : ℕ) (x s : E)
    {σ : ℝ} (hσ : 0 < σ)
    (hs : regularizedModel f c h p x σ s < regularizedModel f c h p x σ 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧
      ModelDecrease.ApproximateGlobalStep (regularizedModel f c h p x σ) μ s := by
  obtain ⟨t, ht⟩ := exists_minimizer_regularizedModel f c hh p x hσ
  exact ModelDecrease.exists_fraction_of_strict_decrease ht hs

/-- For genuine composite models, a positive global-gap fraction is equivalent
to strict improvement or a zero return at an already global model minimum. -/
theorem exists_fraction_iff (f : E → ℝ) (c : E → F)
    {h : F → ℝ} {K : NNReal} (hh : LipschitzWith K h) (p : ℕ) (x s : E)
    {σ : ℝ} (hσ : 0 < σ) :
    (∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧
      ModelDecrease.ApproximateGlobalStep (regularizedModel f c h p x σ) μ s) ↔
    regularizedModel f c h p x σ s < regularizedModel f c h p x σ 0 ∨
      (regularizedModel f c h p x σ s = regularizedModel f c h p x σ 0 ∧
        ∀ t, regularizedModel f c h p x σ 0 ≤ regularizedModel f c h p x σ t) := by
  obtain ⟨t, ht⟩ := exists_minimizer_regularizedModel f c hh p x hσ
  exact ModelDecrease.exists_fraction_iff_of_isMin ht

end Composite
