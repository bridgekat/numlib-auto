import Numlib.Optimization.Regularization.Inexact.Explicit.Termination

/-!
# Actual EDA termination complexity with a positive effective margin

All constants are positive and fixed before the requested accuracies or
execution data. Consistent actual prefixes pass the literal explicit stopping test. The added
condition theta < zeta/2 is explicit, and source unrestricted termination remains open.
Function evaluations have the
source inverse-power budget, while derivative evaluations have the additional
logarithmic accuracy budget. Derivative counters include initialization; objective
counts include two values
per actual trial and no unnecessary initial function call. Guarded-parameter and radius-
coefficient
repairs are retained explicitly in the constants.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Genuine EDA executions terminate at their first literal passing check under
the explicit positive effective margin. Both source accuracy rates and the
objective/derivative evaluation schedules have uniform fixed constants. -/
theorem evaluation_complexity {p q : ℕ} (f : E → ℝ) (P : Settings p q) (x₀ : E)
    (hf : ContDiff ℝ p f) (hmargin : P.theta < P.zeta / 2) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) :
    ∃ κA > 0, ∃ κB > 0, ∃ κF > 0, ∃ κD > 0,
      ∀ (ε : Fin q → ℝ) (D : ExecutionData E q), D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬StopsAt P ε D k) → Run f P ε D N) →
      ∃ K : ℕ, StopsAt P ε D K ∧
        (∀ a, 0 < D.checkedRadius K a ∧ D.checkedRadius K a ≤ 1) ∧
        (∀ a, TaylorModel.criticality f (modelOrder a) (D.point K)
          (D.checkedRadius K a) ≤ ε a * D.checkedRadius K a ^ modelOrder a /
            (modelOrder a).factorial) ∧ Run f P ε D K ∧
        (∀ k < K, ¬StopsAt P ε D k) ∧
        ((2 * (successfulIterations D.trials K).card) : ℝ) ≤
          κA * (f x₀ - flow) / accuracyFactor P.toSettings ε + κF ∧
        (derivativeEvaluations D.trials D.ratio P.eta1 K : ℝ) ≤
          κA * (f x₀ - flow) / accuracyFactor P.toSettings ε +
          κB * |Real.log (minimumAccuracy P.order_pos ε)| + κD := by
  let M := executionTensorCap P.toSettings L
  let S := executionParameterCap P.toSettings L
  let c := commonDecreaseCoefficient P L M S
  let κA := (2 * trialCountFactor P.toSettings + 1) / c
  let κB := accuracyCountSlope P.toSettings + 1
  let κF := 2 * trialCountFactor P.toSettings + 2 * |trialCountOffset P.toSettings S| + 2
  let κD := accuracyCountOffset P.toSettings M S + 2
  have hM : 1 ≤ M := one_le_executionTensorCap P.toSettings hL
  have hS : 0 < S := executionParameterCap_pos P.toSettings L
  have hc : 0 < c := commonDecreaseCoefficient_pos P hmargin hL hM hS.le
  have hfactor : 0 < trialCountFactor P.toSettings := zero_lt_one.trans_le
    (one_le_trialCountFactor P.toSettings)
  have hslope : 0 ≤ accuracyCountSlope P.toSettings := by
    exact div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hoffset : 1 ≤ accuracyCountOffset P.toSettings M S := by
    unfold accuracyCountOffset
    exact le_add_of_nonneg_right (div_nonneg (abs_nonneg _) (abs_nonneg _))
  have hA : 0 < κA := div_pos (by positivity) hc
  have hB : 0 < κB := by dsimp [κB]; linarith
  have hF : 0 < κF := by dsimp [κF]; positivity
  have hD : 0 < κD := by dsimp [κD]; linarith
  refine ⟨κA, hA, κB, hB, κF, hF, κD, hD, ?_⟩
  intro ε D hinit hprefix
  obtain ⟨K, htarget, hrun, hfirst⟩ := exists_stopping hprefix hf hmargin hL hlip hlow
  have hcaps := hrun.actual_caps hf hL hlip
  have hfcount := hrun.functionEvaluations_le hf hmargin hL hM (hlip p le_rfl)
    hcaps.1 hcaps.2 hlow hfirst
  have hdcount := hrun.derivativeEvaluations_le hf hmargin hL hM (hlip p le_rfl)
    hcaps.1 hcaps.2 hlow hfirst
  rw [hinit] at hfcount hdcount
  have hrate := accuracyFactor_pos P.toSettings hrun.accuracy_pos
  have hbase : 0 ≤ (f x₀ - flow) / (c * accuracyFactor P.toSettings ε) :=
    div_nonneg (sub_nonneg.mpr (hlow _)) (mul_pos hc hrate).le
  have he : κA * (f x₀ - flow) / accuracyFactor P.toSettings ε =
      (2 * trialCountFactor P.toSettings + 1) * ((f x₀ - flow) / (c * accuracyFactor
        P.toSettings ε)) := by
    dsimp only [κA]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  obtain ⟨hlegal, hopt⟩ := hrun.stopped_optimality le_rfl htarget
  refine ⟨K, htarget, hlegal, hopt, hrun, hfirst, ?_, ?_⟩
  · rw [he]
    dsimp only [κF]
    dsimp only [c] at hbase
    nlinarith [le_abs_self (trialCountOffset P.toSettings S)]
  · rw [he]
    dsimp only [κB, κD]
    dsimp only [c] at hbase
    have hprod := mul_nonneg hfactor.le hbase
    nlinarith [abs_nonneg (Real.log (minimumAccuracy P.order_pos ε))]

end InexactRegularization.Explicit
