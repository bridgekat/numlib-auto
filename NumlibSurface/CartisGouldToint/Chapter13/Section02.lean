import Numlib.Optimization.Regularization.Inexact.OracleSimulation.Complexity
import Numlib.Optimization.TrustRegion.Inexact.OracleSimulation.Complexity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fixed-cost low-order oracle complexity

These corrected companions require a uniform bound on the finite lower-order
call batches and use the worst tolerance. The literal source theorem remains
open: finite work alone gives no accuracy-independent stencil cost, and its
printed minima of inverse tolerance powers have the wrong extremum.
-/

namespace CartisGouldToint
open InexactTrustRegion Set

/-- Trust-region part of Theorem13.2.1 with uniform primitive stencil cost and
the corrected worst-component inverse-accuracy rate. Actual execution and
true criticality attainment come from the complete TRqIDA theorem. -/
theorem theorem_13_2_1_uniform_trustRegion {n q : ℕ} (f : EuclideanSpace ℝ (Fin n)
  → ℝ) (P : Settings q) (x₀ : EuclideanSpace ℝ (Fin n))
    {Δ₀ L flow : ℝ} (hL : 1 ≤ L) (hf : ContDiff ℝ q f)
    (hlip : ∀ i, i ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) (o C : ℕ) (ho : o ≤ q) :
    ∃ κ > 0, ∀ (ε : Fin q → ℝ) (A : ℕ → FormalMultilinearSeries ℝ
      (EuclideanSpace ℝ (Fin n)) ℝ) (T : Set ℕ)
      (j : ℕ → Fin q) (x d s : ℕ → EuclideanSpace ℝ (Fin n)) (Δ ρ : ℕ →
        ℝ) (accuracy : ℕ → ℕ → ℝ),
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
              κ * minimumAccuracy P.order_pos ε ^ (-((q + 1 : ℕ) : ℝ)) :=
  InexactTrustRegion.lowOrderOracle_complexity f P x₀ hL hf hlip hlow o C ho

/-- Regularization parts of Theorem13.2.1 with uniform primitive stencil cost
and the corrected worst-component rates for both q<=2 and q>2. Constants precede
all accuracies and actual primitive batches; true certificates are derived from
the complete operational ARqpIDA theorem. -/
theorem theorem_13_2_1_uniform_regularization {n p q : ℕ} (f : EuclideanSpace ℝ (Fin
  n) → ℝ) (P : InexactRegularization.Settings p q) (x₀ : EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) (o C : ℕ) (ho : o ≤ q) :
    ∃ κ > 0, ∀ (ε : Fin q → ℝ) (D : InexactRegularization.ExecutionData
      (EuclideanSpace ℝ (Fin n)) q), D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬InexactRegularization.TargetAt f ε D k) →
        InexactRegularization.Run f P ε D N) →
      ∃ (K : ℕ) (δ : Fin q → ℝ),
        (δ = D.startRadius K ∨ δ = D.checkedRadius K) ∧
        InexactRegularization.OptimalityAt f ε (D.point K) δ ∧
          InexactRegularization.Run f P ε D K ∧
        (∀ k < K, ¬InexactRegularization.TargetAt f ε D k) ∧
        ∀ batch : Fin (p + 1) → ℕ → List (Fin (o + 1)),
          (∀ i k, k < OracleSimulation.schedule p (functionEvaluations D.trials K)
            (derivativeEvaluations D.trials D.ratio P.eta1 K) i →
              (batch i k).length ≤ C) →
          (OracleSimulation.calls
            (OracleSimulation.schedule p (functionEvaluations D.trials K)
              (derivativeEvaluations D.trials D.ratio P.eta1 K)) batch : ℝ) ≤
            κ * minimumAccuracy P.order_pos ε ^ (-InexactRegularization.oracleRateExponent p q) :=
  InexactRegularization.lowOrderOracle_complexity f P x₀ hf hL hlip hlow o C ho

end CartisGouldToint
