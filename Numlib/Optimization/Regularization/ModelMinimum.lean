import Numlib.Analysis.Calculus.TaylorModel.Growth
import Numlib.Optimization.HighOrder.ModelDecrease
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Tactic

/-!
# Global minima of norm-regularized finite tensor polynomials

The positive norm-power penalty dominates the actual finite tensor polynomial
outside an explicit ball. Compactness therefore supplies a genuine global model
minimizer, without postulating a model step or a criticality conclusion.
-/

namespace ModelDecrease
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite tensor polynomial with its positive-degree norm penalty is continuous. -/
theorem continuous_penalized_ofJet (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) :
    Continuous (penalized (TaylorModel.ofJet A p) p σ) :=
  (FormalMultilinearSeries.partialSum_continuous _ _).add
    (continuous_const.mul (continuous_norm.pow _))

/-- A positive regularization coefficient gives a genuine global minimizer of
the actual finite tensor polynomial plus its norm-power penalty. -/
theorem exists_minimizer_ofJet [ProperSpace E]
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s : E, ∀ t : E, penalized (TaylorModel.ofJet A p) p σ s ≤
      penalized (TaylorModel.ofJet A p) p σ t := by
  let m := penalized (TaylorModel.ofJet A p) p σ
  let B := TaylorModel.jetNormSum A p
  let c := σ / ((p + 1).factorial : ℝ)
  let R := max 1 ((B + |m 0| + 1) / c)
  have hc : 0 < c := div_pos hσ (by positivity)
  have hR : 0 ≤ R := le_trans (by norm_num) (le_max_left _ _)
  have houtside (t : E) (ht : R ≤ ‖t‖) : m 0 ≤ m t := by
    have ht1 : 1 ≤ ‖t‖ := (le_max_left _ _).trans ht
    have hgrowth := TaylorModel.norm_ofJet_le_mul_pow A p t ht1
    have hlower : -B * ‖t‖ ^ p ≤ TaylorModel.ofJet A p t := by
      have hh := (abs_le.mp hgrowth).1
      nlinarith
    have hcr : B + |m 0| + 1 ≤ c * ‖t‖ := by
      have hh : (B + |m 0| + 1) / c ≤ ‖t‖ := (le_max_right _ _).trans ht
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hh
    have hp : 1 ≤ ‖t‖ ^ p := one_le_pow₀ ht1
    have hm := mul_le_mul_of_nonneg_right hcr (pow_nonneg (norm_nonneg t) p)
    have ha := le_mul_of_one_le_right
      (show 0 ≤ |m 0| + 1 by positivity) hp
    have hvalue : m t = TaylorModel.ofJet A p t + c * ‖t‖ ^ (p + 1) := rfl
    rw [hvalue, pow_succ]
    nlinarith [le_abs_self (m 0)]
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    (show (Metric.closedBall (0 : E) R).Nonempty from ⟨0, by simpa using hR⟩)
    (continuous_penalized_ofJet A p σ).continuousOn
  refine ⟨s, fun t => ?_⟩
  by_cases ht : t ∈ Metric.closedBall (0 : E) R
  · exact hmin ht
  · have htR : R ≤ ‖t‖ := by
      have hh : ¬‖t‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
      exact (not_le.mp hh).le
    exact (hmin (by simpa using hR)).trans (houtside t htR)

/-- If one actual comparison step strictly improves the model, every selected
global minimizer is nonzero and improves at least as much as that step. -/
theorem exists_nonzero_minimizer_ofJet [ProperSpace E]
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) {σ : ℝ} (hσ : 0 < σ) (d : E)
    (hd : penalized (TaylorModel.ofJet A p) p σ d <
      penalized (TaylorModel.ofJet A p) p σ 0) :
    ∃ s : E, s ≠ 0 ∧
      (∀ t : E, penalized (TaylorModel.ofJet A p) p σ s ≤
        penalized (TaylorModel.ofJet A p) p σ t) ∧
      penalized (TaylorModel.ofJet A p) p σ s ≤ penalized (TaylorModel.ofJet A p) p σ d := by
  obtain ⟨s, hs⟩ := exists_minimizer_ofJet A p hσ
  refine ⟨s, ?_, hs, hs d⟩
  intro hz
  exact (not_lt_of_ge (hs d)) (hz ▸ hd)

end ModelDecrease
