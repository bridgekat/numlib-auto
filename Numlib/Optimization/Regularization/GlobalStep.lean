import Numlib.Optimization.Regularization.ModelMinimum

/-!
# Actual approximate-global model steps

The fraction-of-global-gap rule is expressed by comparisons with every actual
candidate model value. When a global minimizer exists, this is equivalent to
the usual comparison with its value. A positive norm-regularized finite tensor
model admits such steps. A zero-decrease return derives global minimality of
zero, rather than assuming a criticality or stationarity conclusion.
-/

namespace ModelDecrease
variable {E : Type*} [NormedAddCommGroup E]

/-- The computed step achieves a fraction `μ` of every available actual model
decrease, equivalently a fraction of the global optimal decrease when attained. -/
def ApproximateGlobalStep (m : E → ℝ) (μ : ℝ) (s : E) : Prop :=
  ∀ t : E, μ * (m 0 - m t) ≤ m 0 - m s

/-- At a genuine global minimizer, the comparison rule is exactly the standard
fraction-of-global-gap inequality. -/
theorem approximateGlobalStep_iff_of_isMin {m : E → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    {s tstar : E} (hmin : ∀ t, m tstar ≤ m t) :
    ApproximateGlobalStep m μ s ↔ μ * (m 0 - m tstar) ≤ m 0 - m s := by
  refine ⟨fun h => h tstar, fun h t => ?_⟩
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (hmin t) _) hμ).trans h

/-- A zero-decrease approximate-global return with positive fraction makes
zero an actual global model minimizer. -/
theorem ApproximateGlobalStep.isGlobalMin_zero {m : E → ℝ} {μ : ℝ} {s : E}
    (h : ApproximateGlobalStep m μ s) (hμ : 0 < μ) (hz : m 0 = m s) :
    ∀ t : E, m 0 ≤ m t := by
  intro t
  have ht := h t
  rw [hz, sub_self] at ht
  nlinarith

/-- A strictly improving actual reference candidate forces a strictly improving
approximate-global return. -/
theorem ApproximateGlobalStep.strict_decrease {m : E → ℝ} {μ : ℝ} {s d : E}
    (h : ApproximateGlobalStep m μ s) (hμ : 0 < μ) (hd : m d < m 0) : m s < m 0 := by
  have hpos := mul_pos hμ (sub_pos.mpr hd)
  have hs := h d
  linarith

variable [NormedSpace ℝ E] [ProperSpace E]

/-- Positive norm-regularized finite models genuinely admit every requested
fraction in `[0,1]`, by the proved existence of their actual global minimizers. -/
theorem exists_approximateGlobalStep_ofJet (A : FormalMultilinearSeries ℝ E ℝ)
    (p : ℕ) {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ s : E, ApproximateGlobalStep (penalized (TaylorModel.ofJet A p) p σ) μ s := by
  obtain ⟨s, hs⟩ := exists_minimizer_ofJet A p hσ
  refine ⟨s, (approximateGlobalStep_iff_of_isMin hμ hs).mpr ?_⟩
  exact mul_le_of_le_one_left (sub_nonneg.mpr (hs 0)) hμ1

end ModelDecrease
