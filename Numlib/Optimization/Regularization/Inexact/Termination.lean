import Numlib.Optimization.Regularization.Inexact.ExecutionBounds

/-!
# Finite attainment of true approximate optimality in inexact regularization

Every consistent primitive execution reaches the true all-order target at a
first finite index. The contradiction uses only the derived actual objective,
parameter-update and accuracy-update budgets. No observable stopping test,
termination index or finite-run existence conclusion is assumed.
-/

namespace InexactRegularization
open InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual consistent prefixes attain true approximate optimality at a first
finite index. The algorithm need not be able to observe this true target. -/
theorem exists_approximate_optimality {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {ε : Fin q → ℝ} {D : ExecutionData E q}
    (hprefix : ∀ N, (∀ k < N, ¬TargetAt f ε D k) → Run f P ε D N)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) :
    ∃ K, TargetAt f ε D K ∧ Run f P ε D K ∧ ∀ k < K, ¬TargetAt f ε D k := by
  classical
  have hex : ∃ K, TargetAt f ε D K := by
    by_contra hn
    push Not at hn
    let M := executionTensorCap P L
    let S := executionParameterCap P L
    let bound := trialCountFactor P * ((f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L M S * accuracyFactor P ε) + 1) +
      trialCountOffset P S +
      accuracyCountSlope P * |Real.log (minimumAccuracy P.order_pos ε)| +
      accuracyCountOffset P M S
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have h := hprefix N (fun k _ => hn k)
    have hcaps := h.actual_caps hf hL hlip
    have hb := h.iterations_le hf hL (one_le_executionTensorCap P hL) (hlip p le_rfl)
      hcaps.1 hcaps.2 hlow (fun k _ => hn k)
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩
  · exact fun k hk => Nat.find_min hex hk
  · exact fun k hk => Nat.find_min hex hk

end InexactRegularization
