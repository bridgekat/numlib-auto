import Numlib.Optimization.Composite.ModelTaylor
import Numlib.Analysis.Calculus.TaylorModel.Growth
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Global minima of actual composite regularization models

A positive norm-power penalty dominates the scalar polynomial and the
Lipschitz outer function applied to the residual polynomial. Compactness
therefore provides a genuine global minimizer, including nonsmooth outer maps.
-/

namespace Composite
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual composite regularized finite model is continuous when its outer function is. -/
theorem continuous_regularizedModel (f : E → ℝ) (c : E → F) {h : F → ℝ}
    (hh : Continuous h) (p : ℕ) (x : E) (σ : ℝ) :
    Continuous (regularizedModel f c h p x σ) := by
  exact ((TaylorModel.contDiff_eval f p x 0).continuous.add
    (hh.comp (TaylorModel.contDiff_eval c p x 0).continuous)).add
      (continuous_const.mul (continuous_norm.pow _))

/-- A positive penalty produces a genuine global composite model minimizer. -/
theorem exists_minimizer_regularizedModel [ProperSpace E] (f : E → ℝ) (c : E → F)
    {h : F → ℝ} {K : NNReal} (hh : LipschitzWith K h)
    (p : ℕ) (x : E) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s : E, ∀ t : E, regularizedModel f c h p x σ s ≤
      regularizedModel f c h p x σ t := by
  let m := regularizedModel f c h p x σ
  let B := TaylorModel.jetNormSum (ftaylorSeries ℝ f x) p +
    (K : ℝ) * TaylorModel.jetNormSum (ftaylorSeries ℝ c x) p
  let a := σ / ((p + 1).factorial : ℝ)
  let R := max 1 ((B + |m 0| + |h 0| + 1) / a)
  have ha : 0 < a := div_pos hσ (by positivity)
  have hR : 0 ≤ R := le_trans (by norm_num) (le_max_left _ _)
  have houtside (t : E) (ht : R ≤ ‖t‖) : m 0 ≤ m t := by
    have ht1 : 1 ≤ ‖t‖ := (le_max_left _ _).trans ht
    have hfg := TaylorModel.norm_ofJet_le_mul_pow (ftaylorSeries ℝ f x) p t ht1
    have hcg := TaylorModel.norm_ofJet_le_mul_pow (ftaylorSeries ℝ c x) p t ht1
    have hhg := hh.dist_le_mul (TaylorModel.eval c p x t) 0
    rw [Real.dist_eq, dist_zero_right] at hhg
    have hhc := mul_le_mul_of_nonneg_left hcg K.coe_nonneg
    have hlower : -B * ‖t‖ ^ p - |h 0| ≤
        TaylorModel.eval f p x t + h (TaylorModel.eval c p x t) := by
      have hf0 := (abs_le.mp hfg).1
      have hh0 := (abs_le.mp hhg).1
      change -(_ * _) ≤ TaylorModel.eval f p x t at hf0
      change (K : ℝ) * ‖TaylorModel.eval c p x t‖ ≤ _ at hhc
      dsimp [B]
      nlinarith [le_abs_self (h 0), neg_abs_le (h 0)]
    have har : B + |m 0| + |h 0| + 1 ≤ a * ‖t‖ := by
      have hh : (B + |m 0| + |h 0| + 1) / a ≤ ‖t‖ := (le_max_right _ _).trans ht
      simpa only [mul_comm] using (div_le_iff₀ ha).mp hh
    have hp : 1 ≤ ‖t‖ ^ p := one_le_pow₀ ht1
    have hm := mul_le_mul_of_nonneg_right har (pow_nonneg (norm_nonneg t) p)
    have hb := le_mul_of_one_le_right
      (show 0 ≤ |m 0| + |h 0| + 1 by positivity) hp
    have he : m t = TaylorModel.eval f p x t + h (TaylorModel.eval c p x t) +
        a * ‖t‖ ^ (p + 1) := rfl
    rw [he, pow_succ]
    nlinarith [le_abs_self (m 0)]
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    (show (Metric.closedBall (0 : E) R).Nonempty from ⟨0, by simpa using hR⟩)
    (continuous_regularizedModel f c hh.continuous p x σ).continuousOn
  refine ⟨s, fun t => ?_⟩
  by_cases ht : t ∈ Metric.closedBall (0 : E) R
  · exact hmin ht
  · have htR : R ≤ ‖t‖ := by
      have hh : ¬‖t‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
      exact (not_le.mp hh).le
    exact (hmin (by simpa using hR)).trans (houtside t htR)
end Composite
