import Numlib.Optimization.Regularization.Inexact.OracleSimulation.Rates

/-!
# Low-order fixed-cost oracle simulation of actual regularization

The completed actual regularization theorem supplies an iterate and evaluation
counts. Actual finite lower-order call batches, each with a uniform fixed cap,
then inherit a worst-component inverse-power bound. The uniform cost assumption
is explicit; merely finite but unbounded approximation work is insufficient.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Fixed-cost batches of lower-order oracle calls inherit actual ARqpIDA
certificate attainment and the corrected worst-component accuracy rate. The
constant precedes every accuracy, computed trace and finite call batch. -/
theorem lowOrderOracle_complexity {p q : ℕ} (f : E → ℝ) (P : Settings p q) (x₀ : E)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) (o C : ℕ) (_ho : o ≤ q) :
    ∃ κ > 0, ∀ (ε : Fin q → ℝ) (D : ExecutionData E q), D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬TargetAt f ε D k) → Run f P ε D N) →
      ∃ (K : ℕ) (δ : Fin q → ℝ),
        (δ = D.startRadius K ∨ δ = D.checkedRadius K) ∧
        OptimalityAt f ε (D.point K) δ ∧ Run f P ε D K ∧
        (∀ k < K, ¬TargetAt f ε D k) ∧
        ∀ batch : Fin (p + 1) → ℕ → List (Fin (o + 1)),
          (∀ i k, k < OracleSimulation.schedule p (functionEvaluations D.trials K)
            (derivativeEvaluations D.trials D.ratio P.eta1 K) i →
              (batch i k).length ≤ C) →
          (OracleSimulation.calls
            (OracleSimulation.schedule p (functionEvaluations D.trials K)
              (derivativeEvaluations D.trials D.ratio P.eta1 K)) batch : ℝ) ≤
            κ * minimumAccuracy P.order_pos ε ^ (-oracleRateExponent p q) := by
  obtain ⟨κA, hA, κB, hB, κF, hF, κD, hD, hall⟩ :=
    evaluation_complexity f P x₀ hf hL hlip hlow
  obtain ⟨κ, hκ, hcost⟩ := OracleSimulation.exists_calls_inverse_power_bound p C
    hA.le hB.le hF.le hD.le (sub_nonneg.mpr (hlow x₀)) (oracleRateExponent_pos P)
  refine ⟨κ, hκ, ?_⟩
  intro ε D hinit hprefix
  obtain ⟨K, δ, hactual, hopt, hrun, hfirst, hfcount, hdcount⟩ := hall ε D hinit hprefix
  refine ⟨K, δ, hactual, hopt, hrun, hfirst, ?_⟩
  intro batch hbatch
  have hμ := minimumAccuracy_pos P.order_pos hrun.accuracy_pos
  have hμ1 := (minimumAccuracy_le P.order_pos ε ⟨0, P.order_pos⟩).trans
    (hrun.accuracy_le_one _)
  apply hcost _ _ hμ hμ1
    (minimumAccuracy_pow_oracleRate_le P ε hrun.accuracy_pos hrun.accuracy_le_one)
    _ _ _ hdcount o batch hbatch
  have hh := mul_nonneg hB.le (abs_nonneg (Real.log (minimumAccuracy P.order_pos ε)))
  nlinarith [hfcount]

end InexactRegularization
