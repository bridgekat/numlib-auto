import Numlib.Optimization.Regularization.Inexact.Explicit.Caps

/-!
# Finite literal stopping with a positive EDA margin

Every consistent primitive execution reaches the literal stopping test at a
first finite index. The contradiction uses only the derived actual objective,
parameter-update and accuracy-update budgets. No stopping index or finite-run existence
conclusion is assumed. The additional
positive margin is explicit; unrestricted source termination remains open.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual consistent prefixes pass the literal observable EDA stopping test
at a first finite index, under the explicit positive effective margin. -/
theorem exists_stopping {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {ε : Fin q → ℝ} {D : ExecutionData E q}
    (hprefix : ∀ N, (∀ k < N, ¬StopsAt P ε D k) → Run f P ε D N)
    (hf : ContDiff ℝ p f) (hmargin : P.theta < P.zeta / 2) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) :
    ∃ K, StopsAt P ε D K ∧ Run f P ε D K ∧ ∀ k < K, ¬StopsAt P ε D k := by
  classical
  have hex : ∃ K, StopsAt P ε D K := by
    by_contra hn
    push Not at hn
    let M := executionTensorCap P.toSettings L
    let S := executionParameterCap P.toSettings L
    let bound := trialCountFactor P.toSettings * ((f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L M S * accuracyFactor P.toSettings ε) + 1) +
      trialCountOffset P.toSettings S +
      accuracyCountSlope P.toSettings * |Real.log (minimumAccuracy P.order_pos ε)| +
      accuracyCountOffset P.toSettings M S
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have h := hprefix N (fun k _ => hn k)
    have hcaps := h.actual_caps hf hL hlip
    have hb := h.iterations_le hf hmargin hL (one_le_executionTensorCap P.toSettings hL)
      (hlip p le_rfl)
      hcaps.1 hcaps.2 hlow (fun k _ => hn k)
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩
  · exact fun k hk => Nat.find_min hex hk
  · exact fun k hk => Nat.find_min hex hk

end InexactRegularization.Explicit
