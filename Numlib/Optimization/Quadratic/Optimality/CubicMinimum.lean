import Numlib.Optimization.Quadratic.Optimality.Regularization
import Mathlib.Topology.Order.Compact

/-!
# Attainment for cubic-regularized quadratic models

The positive cubic penalty dominates both quadratic and linear terms. Compact
minimization therefore supplies genuine global minimizers.
-/

namespace QuadraticOptimality
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- A positive cubic penalty makes every bounded quadratic attain a global minimum. -/
theorem exists_cubic_regularized_min (H : E →L[ℝ] E) (g : E) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s : E, ∀ t : E, regularized H g σ 3 s ≤ regularized H g σ 3 t := by
  let B := ‖g‖ + ‖H‖ / 2
  let R := max 1 (3 * B / σ)
  have hR : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  have hc : Continuous (regularized H g σ 3) := by
    exact (contDiff_model H g 0).continuous.add
      (continuous_const.mul (continuous_norm.rpow_const (by norm_num)))
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨0, by simpa using hR⟩ hc.continuousOn
  refine ⟨s, fun t => ?_⟩
  by_cases ht : t ∈ Metric.closedBall (0 : E) R
  · exact hmin ht
  · have htR : R ≤ ‖t‖ := by
      have hh : ¬‖t‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
      exact (not_le.mp hh).le
    have ht1 : 1 ≤ ‖t‖ := (le_max_left _ _).trans htR
    have hnorm := norm_nonneg t
    have hg := (abs_le.mp (abs_real_inner_le_norm g t)).1
    have hH := (abs_le.mp (abs_real_inner_le_norm (H t) t)).1
    have hop := mul_le_mul_of_nonneg_right (H.le_opNorm t) hnorm
    have hlin := mul_le_mul_of_nonneg_left (show ‖t‖ ≤ ‖t‖ ^ 2 by nlinarith) (norm_nonneg g)
    have hpen : 3 * B ≤ σ * ‖t‖ := by
      simpa only [mul_comm] using (div_le_iff₀ hσ).mp ((le_max_right _ _).trans htR)
    have hmul := mul_le_mul_of_nonneg_right hpen (sq_nonneg ‖t‖)
    have hnonneg : 0 ≤ regularized H g σ 3 t := by
      rw [regularized, model_eq, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
      dsimp [B] at hmul
      nlinarith
    have hz := hmin (show (0 : E) ∈ Metric.closedBall 0 R by simpa using hR)
    have he : regularized H g σ 3 0 = 0 := by simp [regularized, model_eq]
    exact hz.trans (he.le.trans hnonneg)
end QuadraticOptimality
