import NumlibSurface.CartisGouldToint.Chapter06.Section02
import Numlib.Optimization.Regularization.Convex.LeastSquares.Complexity
import Numlib.Optimization.LeastSquares.Exponents

/-!
# Convexly constrained least-Euclidean-norm complexity

Actual source ARpLE-CC executions use scaled constrained model criticality and
the literal residual or normalized objective stopping rule. The exact source
constants precede every accuracy, and both residual and per-order derivative
schedules are explicit. The auxiliary cascading displays use the normalized
measure; interpreting their displayed omega as unnormalized would double-count
the residual-power weight. The numbered complexity statement needs no repair.
-/

namespace CartisGouldToint
open Set

/-- The actual normalized constrained residual-power first-order measure. -/
noncomputable abbrev residualConvexFirstMeasure := @ConvexLeastSquares.firstMeasure

/-- The literal residual or normalized constrained first-order stopping disjunction. -/
abbrev arpLeastEuclideanConvexStop := @ConvexLeastSquares.Stop

/-- Primitive actual ARpLE-CC prefixes have true residual-power models, feasible
scaled model solves, objective ratios, updates and failures of the literal tests. -/
abbrev arpLeastEuclideanConvexRun := @ConvexLeastSquares.Run

/-- **Theorem6.3.1.** All printed first-order residual-power choices give the
exact positive source constants, the first actual constrained stopping point,
and every initialized residual/derivative bound. Constants are fixed before
both requested accuracies and every actual execution. -/
theorem theorem_6_3_1 {n m p a : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C S : Set (EuclideanSpace ℝ (Fin n))}
    (P : arpFirstOrderConvexSettings p) (ℓ : ℝ) (_hℓ : 1 < ℓ)
    (hchoice : (ℓ = (p : ℝ) ∧ Real.logb 2 (p : ℝ) < a) ∨
      ∃ o : ℕ, Odd o ∧ Even p ∧ p = o * 2 ^ a ∧
        ℓ = 1 + (o : ℝ) * ((2 : ℝ) ^ a - 1))
    (hclosed : IsClosed C) (hS : IsOpen S)
    (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (LeastSquares.powerObjective r ℓ) S) {L β : ℝ} (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (LeastSquares.powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (LeastSquares.powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = max (1 / (1 - β ^ (1 / (2 : ℝ) ^ a)))
        ((2 : ℝ) ^ a / β ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / p) *
          ((p + 1).factorial / (P.eta1 * P.sigmaMin) *
            ((L + ConvexRegularization.parameterCap P L + P.theta * p.factorial) / p.factorial) ^
              (((p + 1 : ℕ) : ℝ) / p))) ∧
      κA = κS * (1 + |Real.log P.gamma1| / Real.log P.gamma2) ∧
      κC = |Real.log P.gamma1| / Real.log P.gamma2 +
        Real.log (ConvexRegularization.parameterCap P L / P.sigmaInitial) /
          Real.log P.gamma2 + 2 ∧
      ∀ (ε₀ ε₁ : ℝ) (D : arpFirstOrderConvexData (EuclideanSpace ℝ (Fin n))),
        (∀ N, (∀ i < N, ¬arpLeastEuclideanConvexStop r ℓ C ε₀ ε₁ (D.point i)) →
          arpLeastEuclideanConvexRun r ℓ C P ε₀ ε₁ D N) →
        ∃ K, arpLeastEuclideanConvexStop r ℓ C ε₀ ε₁ (D.point K) ∧
          arpLeastEuclideanConvexRun r ℓ C P ε₀ ε₁ D K ∧
          (∀ i < K, ¬arpLeastEuclideanConvexStop r ℓ C ε₀ ε₁ (D.point i)) ∧
          (ConvexRegularization.functionEvaluations K : ℝ) ≤
            κA * max (‖r (D.point 0)‖ ^ (1 / (2 : ℝ) ^ a))
              (‖r (D.point 0)‖ ^ (1 - (ℓ - 1) / p)) /
            min (ε₀ ^ (1 / (2 : ℝ) ^ a)) (ε₁ ^ (((p + 1 : ℕ) : ℝ) / p)) + κC ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ p →
            (ConvexLeastSquares.derivativeEvaluations r ε₀ P D K j : ℝ) ≤
            κS * max (‖r (D.point 0)‖ ^ (1 / (2 : ℝ) ^ a))
              (‖r (D.point 0)‖ ^ (1 - (ℓ - 1) / p)) /
              min (ε₀ ^ (1 / (2 : ℝ) ^ a)) (ε₁ ^ (((p + 1 : ℕ) : ℝ) / p)) + 2 := by
  have H := LeastSquares.cascadingExponent_choices P.order_pos
  have hg : 0 ≤ LeastSquares.cascadingExponent p ℓ a 1 := by
    rcases hchoice with ⟨rfl, hlog⟩ | ⟨o, ho, heven, hfac, rfl⟩
    · exact (H.1 a hlog).le
    · exact (H.2.1 o a ho heven hfac).1.symm.le
  simpa only [LeastSquares.lowerBudget, LeastSquares.lowerAccuracyFactor,
    Bool.false_eq_true, ite_false] using
      ConvexLeastSquares.exists_uniform_complexity P ℓ a hclosed hS hCS hC hf hL hlip
        hβ hβ1 hg

end CartisGouldToint
