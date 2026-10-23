import Numlib.Optimization.EvaluationComplexity.OracleSimulation.Counts
import Numlib.Optimization.TrustRegion.Inexact.Complexity

/-!
# Fixed-cost low-order oracle simulation of trust-region executions

Actual trust-region optimality attainment and evaluation counts transfer to
finite batches of lower-order calls with a uniform fixed stencil cap. The
result uses the smallest requested accuracy and the worst-component exponent.
-/

namespace InexactTrustRegion
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Uniform finite lower-order oracle batches inherit the genuine TRqIDA
iterate certificate and its worst-component inverse-accuracy evaluation rate. -/
theorem lowOrderOracle_complexity {q : ℕ} (f : E → ℝ) (P : Settings q) (x₀ : E)
    {Δ₀ L flow : ℝ} (hL : 1 ≤ L) (hf : ContDiff ℝ q f)
    (hlip : ∀ i, i ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) (o C : ℕ) (_ho : o ≤ q) :
    ∃ κ > 0, ∀ (ε : Fin q → ℝ) (A : ℕ → FormalMultilinearSeries ℝ E ℝ)
      (T : Set ℕ)
      (j : ℕ → Fin q) (x d s : ℕ → E) (Δ ρ : ℕ → ℝ) (accuracy : ℕ →
        ℕ → ℝ),
      x 0 = x₀ → Δ 0 = Δ₀ →
      (∀ N, (∀ i < N, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) →
        Run f P ε A T j x d s Δ ρ accuracy N) →
      ∃ K, optimalityRadius P.theta (Δ K) ∈ Ioc 0 1 ∧
        (∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (x K)
          (optimalityRadius P.theta (Δ K)) ≤
            ε a * optimalityRadius P.theta (Δ K) ^ modelOrder a / (modelOrder a).factorial) ∧
        Run f P ε A T j x d s Δ ρ accuracy K ∧
        (∀ i < K, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) ∧
        ∀ batch : Fin (q + 1) → ℕ → List (Fin (o + 1)),
          (∀ i k, k < OracleSimulation.schedule q (functionEvaluations T K)
            (derivativeEvaluations T ρ P.eta1 K) i → (batch i k).length ≤ C) →
          (OracleSimulation.calls (OracleSimulation.schedule q (functionEvaluations T K)
            (derivativeEvaluations T ρ P.eta1 K)) batch : ℝ) ≤
              κ * minimumAccuracy P.order_pos ε ^ (-((q + 1 : ℕ) : ℝ)) := by
  obtain ⟨κA, hA, κB, hB, κC, hC, κE, hE, κF, hF, hall⟩ :=
    evaluation_complexity f P x₀ (Δ₀ := Δ₀) hL hf hlip hlow
  obtain ⟨κ, hκ, hcost⟩ := OracleSimulation.exists_calls_inverse_power_bound q C
    hA.le (add_nonneg hB.le hE.le) hC.le hF.le (sub_nonneg.mpr (hlow x₀))
    (by positivity : (0 : ℝ) < (q + 1 : ℕ))
  refine ⟨κ, hκ, ?_⟩
  intro ε A T j x d s Δ ρ accuracy hx hΔ hprefix
  obtain ⟨K, hrad, hopt, hrun, hfirst, hfcount, hdcount⟩ :=
    hall ε A T j x d s Δ ρ accuracy hx hΔ hprefix
  refine ⟨K, hrad, hopt, hrun, hfirst, ?_⟩
  intro batch hbatch
  have hμ := minimumAccuracy_pos P.order_pos hrun.accuracy_pos
  have hμ1 := (minimumAccuracy_le P.order_pos ε ⟨0, P.order_pos⟩).trans
    (hrun.accuracy_le_one _)
  apply hcost _ _ hμ hμ1 (by rw [Real.rpow_natCast]) _ _ _ _ o batch hbatch
  · have hh := mul_nonneg hE.le (abs_nonneg (Real.log (minimumAccuracy P.order_pos ε)))
    nlinarith [hfcount]
  · have hh := mul_nonneg hB.le (abs_nonneg (Real.log (minimumAccuracy P.order_pos ε)))
    nlinarith [hdcount]

end InexactTrustRegion
