import Numlib.Optimization.Regularization.ModelMinimum

/-!
# Actual regularized model minima on closed feasible sets

The norm-power penalty dominates the genuine finite tensor polynomial at
infinity. Compact minimization on a ball intersected with any nonempty closed
set therefore gives a true constrained global minimizer.
-/

namespace ModelDecrease
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive actual norm-power penalty attains its global minimum on every
nonempty closed feasible set, without boundedness or convexity assumptions. -/
theorem exists_minimizer_ofJet_on [ProperSpace E]
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {C : Set E} (hC : IsClosed C) (hne : C.Nonempty) :
    ∃ s ∈ C, ∀ t ∈ C, penalized (TaylorModel.ofJet A p) p σ s ≤
      penalized (TaylorModel.ofJet A p) p σ t := by
  obtain ⟨a, ha⟩ := hne
  let m := penalized (TaylorModel.ofJet A p) p σ
  let B := TaylorModel.jetNormSum A p
  let c := σ / ((p + 1).factorial : ℝ)
  let R := max (max 1 ‖a‖) ((B + |m a| + 1) / c)
  have hc : 0 < c := div_pos hσ (by positivity)
  have hR : 0 ≤ R := le_trans (le_trans (by norm_num) (le_max_left _ _)) (le_max_left _ _)
  have houtside (t : E) (ht : R ≤ ‖t‖) : m a ≤ m t := by
    have ht1 : 1 ≤ ‖t‖ := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
    have hgrowth := TaylorModel.norm_ofJet_le_mul_pow A p t ht1
    have hlower : -B * ‖t‖ ^ p ≤ TaylorModel.ofJet A p t := by
      have hh := (abs_le.mp hgrowth).1
      nlinarith
    have hcr : B + |m a| + 1 ≤ c * ‖t‖ := by
      have hh : (B + |m a| + 1) / c ≤ ‖t‖ := (le_max_right _ _).trans ht
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hh
    have hp : 1 ≤ ‖t‖ ^ p := one_le_pow₀ ht1
    have hm := mul_le_mul_of_nonneg_right hcr (pow_nonneg (norm_nonneg t) p)
    have ha := le_mul_of_one_le_right
      (show 0 ≤ |m a| + 1 by positivity) hp
    have hvalue : m t = TaylorModel.ofJet A p t + c * ‖t‖ ^ (p + 1) := rfl
    rw [hvalue, pow_succ]
    nlinarith [le_abs_self (m a)]
  have haR : a ∈ Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (le_max_right (1 : ℝ) ‖a‖).trans (le_max_left _ _)
  obtain ⟨s, hs, hmin⟩ := ((isCompact_closedBall (0 : E) R).inter_right hC).exists_isMinOn
    ⟨a, haR, ha⟩ (continuous_penalized_ofJet A p σ).continuousOn
  refine ⟨s, hs.2, fun t htC => ?_⟩
  by_cases ht : t ∈ Metric.closedBall (0 : E) R
  · exact hmin ⟨ht, htC⟩
  · have htR : R ≤ ‖t‖ := by
      have hh : ¬‖t‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
      exact (not_le.mp hh).le
    exact (hmin ⟨haR, ha⟩).trans (houtside t htR)

end ModelDecrease
