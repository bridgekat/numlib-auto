import Numlib.Optimization.Regularization.Inexact.Termination

/-!
# Uniform evaluation complexity of actual inexact regularization

All constants are positive and fixed before the requested accuracies or
execution data. Consistent actual prefixes attain true criticality at an
actual inherited or checked radius vector. Function evaluations have the
source inverse-power budget, while derivative evaluations have the additional
logarithmic accuracy budget. Both counters include initialization and the
first target-reaching endpoint. Guarded-parameter and radius-coefficient
repairs are retained explicitly in the constants.
-/

namespace InexactRegularization
open InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Genuine actual executions attain true all-order approximate optimality
within uniform initialized function and derivative evaluation budgets. The
constants precede every requested accuracy and every computed trace. -/
theorem evaluation_complexity {p q : ℕ} (f : E → ℝ) (P : Settings p q) (x₀ : E)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) :
    ∃ κA > 0, ∃ κB > 0, ∃ κF > 0, ∃ κD > 0,
      ∀ (ε : Fin q → ℝ) (D : ExecutionData E q), D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬TargetAt f ε D k) → Run f P ε D N) →
      ∃ (K : ℕ) (δ : Fin q → ℝ),
        (δ = D.startRadius K ∨ δ = D.checkedRadius K) ∧
        OptimalityAt f ε (D.point K) δ ∧ Run f P ε D K ∧
        (∀ k < K, ¬TargetAt f ε D k) ∧
        (functionEvaluations D.trials K : ℝ) ≤
          κA * (f x₀ - flow) / accuracyFactor P ε + κF ∧
        (derivativeEvaluations D.trials D.ratio P.eta1 K : ℝ) ≤
          κA * (f x₀ - flow) / accuracyFactor P ε +
          κB * |Real.log (minimumAccuracy P.order_pos ε)| + κD := by
  let M := executionTensorCap P L
  let S := executionParameterCap P L
  let c := commonDecreaseCoefficient P L M S
  let κA := (trialCountFactor P + 1) / c
  let κB := accuracyCountSlope P + 1
  let κF := trialCountFactor P + |trialCountOffset P S| + 2
  let κD := accuracyCountOffset P M S + 2
  have hM : 1 ≤ M := one_le_executionTensorCap P hL
  have hS : 0 < S := executionParameterCap_pos P L
  have hc : 0 < c := commonDecreaseCoefficient_pos P hL hM hS.le
  have hfactor : 0 < trialCountFactor P := zero_lt_one.trans_le (one_le_trialCountFactor P)
  have hslope : 0 ≤ accuracyCountSlope P := by
    exact div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hoffset : 1 ≤ accuracyCountOffset P M S := by
    unfold accuracyCountOffset
    exact le_add_of_nonneg_right (div_nonneg (abs_nonneg _) (abs_nonneg _))
  have hA : 0 < κA := div_pos (by positivity) hc
  have hB : 0 < κB := by dsimp [κB]; linarith
  have hF : 0 < κF := by dsimp [κF]; positivity
  have hD : 0 < κD := by dsimp [κD]; linarith
  refine ⟨κA, hA, κB, hB, κF, hF, κD, hD, ?_⟩
  intro ε D hinit hprefix
  obtain ⟨K, htarget, hrun, hfirst⟩ := exists_approximate_optimality hprefix hf hL hlip hlow
  have hcaps := hrun.actual_caps hf hL hlip
  have hfcount := hrun.functionEvaluations_le hf hL hM (hlip p le_rfl)
    hcaps.1 hcaps.2 hlow hfirst
  have hdcount := hrun.derivativeEvaluations_le hf hL hM (hlip p le_rfl)
    hcaps.1 hcaps.2 hlow hfirst
  rw [hinit] at hfcount hdcount
  have hrate := accuracyFactor_pos P hrun.accuracy_pos
  have hbase : 0 ≤ (f x₀ - flow) / (c * accuracyFactor P ε) :=
    div_nonneg (sub_nonneg.mpr (hlow _)) (mul_pos hc hrate).le
  have he : κA * (f x₀ - flow) / accuracyFactor P ε =
      (trialCountFactor P + 1) * ((f x₀ - flow) / (c * accuracyFactor P ε)) := by
    dsimp only [κA]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hex : ∃ δ : Fin q → ℝ,
      (δ = D.startRadius K ∨ δ = D.checkedRadius K) ∧ OptimalityAt f ε (D.point K) δ := by
    rcases htarget with hstart | hchecked
    · exact ⟨D.startRadius K, Or.inl rfl, hstart⟩
    · exact ⟨D.checkedRadius K, Or.inr rfl, hchecked⟩
  obtain ⟨δ, hactual, hopt⟩ := hex
  refine ⟨K, δ, hactual, hopt, hrun, hfirst, ?_, ?_⟩
  · rw [he]
    dsimp only [κF]
    dsimp only [c] at hbase
    nlinarith [le_abs_self (trialCountOffset P S)]
  · rw [he]
    dsimp only [κB, κD]
    dsimp only [c] at hbase
    have hprod := mul_nonneg hfactor.le hbase
    nlinarith [abs_nonneg (Real.log (minimumAccuracy P.order_pos ε))]

end InexactRegularization
