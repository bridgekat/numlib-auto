import Numlib.Optimization.Regularization.Constrained.GlobalStep

/-!
# Actual constrained minima of norm-regularized finite models

The positive highest-degree penalty dominates the finite tensor polynomial.
Intersecting a large compact ball with the actual closed feasible set gives a
constrained global minimizer, from which positive-fraction model steps follow.
-/

namespace ModelDecrease
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A positive norm-regularized finite tensor model attains its actual global
minimum on every closed feasible displacement set containing zero. -/
theorem exists_minimizerOn_ofJet (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {C : Set E} (hC : IsClosed C) (hzero : (0 : E) ∈ C) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s ∈ C, IsMinOn (penalized (TaylorModel.ofJet A p) p σ) C s := by
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
  obtain ⟨s, hs, hmin⟩ := ((isCompact_closedBall (0 : E) R).inter_left hC).exists_isMinOn
    (show (C ∩ Metric.closedBall (0 : E) R).Nonempty from
      ⟨0, hzero, by simpa using hR⟩) (continuous_penalized_ofJet A p σ).continuousOn
  refine ⟨s, hs.1, fun t htC => ?_⟩
  by_cases ht : t ∈ Metric.closedBall (0 : E) R
  · exact hmin ⟨htC, ht⟩
  · have htR : R ≤ ‖t‖ := by
      have hh : ¬‖t‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
      exact (not_le.mp hh).le
    exact (hmin ⟨hzero, by simpa using hR⟩).trans (houtside t htR)

/-- Every normalized requested fraction has an actual feasible global-gap
model step, obtained from the proved constrained minimizer existence. -/
theorem exists_approximateGlobalStepOn_ofJet (A : FormalMultilinearSeries ℝ E ℝ)
    (p : ℕ) {C : Set E} (hC : IsClosed C) (hzero : (0 : E) ∈ C)
    {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ s, ApproximateGlobalStepOn (penalized (TaylorModel.ofJet A p) p σ) C μ s := by
  obtain ⟨s, hs, hmin⟩ := exists_minimizerOn_ofJet A p hC hzero hσ
  refine ⟨s, (approximateGlobalStepOn_iff_of_isMinOn hμ hs hmin).mpr ⟨hs, ?_⟩⟩
  exact mul_le_of_le_one_left (sub_nonneg.mpr (hmin hzero)) hμ1

end ModelDecrease
