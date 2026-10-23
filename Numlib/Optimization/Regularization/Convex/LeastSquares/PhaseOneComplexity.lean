import Numlib.Optimization.Regularization.Convex.LeastSquares.PhaseOneBudget

/-!
# Exact initialized least-norm bounds for feasibility phases

The sharpened derivative budget removes the two additive evaluation sites
while retaining the complete source constants and every literal stopping test.
-/

namespace ConvexLeastSquares
open Set TaylorModel HighOrderRegularization LeastSquares ConvexRegularization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F]

/-- The exact source constants bound every initialized derivative count without
an additive offset, uniformly before the two requested accuracies. -/
theorem exists_uniform_complexity_without_offset {r : E → F} {C S : Set E} {p : ℕ}
    (P : Settings p) (ℓ : ℝ) (a : ℕ) (hclosed : IsClosed C) (hS : IsOpen S)
    (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (powerObjective r ℓ) S) {L β : ℝ} (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (hι : 0 ≤ cascadingExponent p ℓ a 1) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = max (1 / (1 - β ^ (1 / (2 : ℝ) ^ a)))
        ((2 : ℝ) ^ a / β ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / p) *
          ((p + 1).factorial / (P.eta1 * P.sigmaMin) *
            ((L + parameterCap P L + P.theta * p.factorial) / p.factorial) ^
              (((p + 1 : ℕ) : ℝ) / p))) ∧
      κA = κS * (1 + |Real.log P.gamma1| / Real.log P.gamma2) ∧
      κC = |Real.log P.gamma1| / Real.log P.gamma2 +
        Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2 + 2 ∧
      ∀ (ε₀ ε₁ : ℝ) (D : Data E),
        (∀ N, (∀ i < N, ¬Stop r ℓ C ε₀ ε₁ (D.point i)) →
          Run r ℓ C P ε₀ ε₁ D N) →
        ∃ K, Stop r ℓ C ε₀ ε₁ (D.point K) ∧ Run r ℓ C P ε₀ ε₁ D K ∧
          (∀ i < K, ¬Stop r ℓ C ε₀ ε₁ (D.point i)) ∧
          (ConvexRegularization.functionEvaluations K : ℝ) ≤
            κA * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
            lowerAccuracyFactor false p a ε₀ ε₁ 1 + κC ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ p →
            (derivativeEvaluations r ε₀ P D K j : ℝ) ≤
            κS * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
              lowerAccuracyFactor false p a ε₀ ε₁ 1 := by
  obtain ⟨κS, hκS, κA, hκA, κC, hκC, heq, hA, hCst, H⟩ :=
    exists_uniform_complexity P ℓ a hclosed hS hCS hC hf hL hlip hβ hβ1 hι
  refine ⟨κS, hκS, κA, hκA, κC, hκC, heq, hA, hCst, ?_⟩
  intro ε₀ ε₁ D hprefix
  obtain ⟨K, hs, hK, hfirst, hF, _⟩ := H ε₀ ε₁ D hprefix
  refine ⟨K, hs, hK, hfirst, hF, ?_⟩
  intro j _ _
  have hconst : lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin
      P.eta1 P.eta2 P.gamma3 L P.theta 1 β = κS :=
    (source_success_constant P ℓ a hL).trans heq.symm
  simpa only [hconst] using hK.derivative_count_le hclosed hS hCS hC hf hL hlip
    hβ hβ1 a hι j

end ConvexLeastSquares
