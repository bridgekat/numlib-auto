import Numlib.Optimization.Regularization.Convex.FirstOrderStep
import Numlib.Optimization.Regularization.Convex.FirstOrderComplexity
import Numlib.Optimization.Regularization.Convex.StepExistence

/-!
# Actual scaled first-order regularization with convex constraints

The ARp1-CC variant uses the step-scaled genuine constrained model measure.
Its successful decrease has the exact source coefficient, with local Cp
smoothness on an open neighborhood of the closed convex domain.
-/

namespace CartisGouldToint
open Set

/-- Fixed legal first-order constrained regularization settings. -/
abbrev arpFirstOrderConvexSettings := ConvexRegularization.Settings

/-- Actual first-order constrained regularization arrays. -/
abbrev arpFirstOrderConvexData := ConvexRegularization.Data

/-- The genuine ARp1-CC trace disables the higher tests and uses the actual
step-scaled model criticality test(6.2.29), objective ratios and update intervals. -/
abbrev arpFirstOrderConvexRun := @ConvexRegularization.ScaledRun

/-- **Lemma6.2.4.** Every successful actual ARp1-CC iteration gives the printed
power decrease in the actual endpoint constrained first-order measure, with
exact κ₁ from(4.1.32). A positive Lipschitz bound may always be chosen in the
source merit class; smoothness is needed only on its open neighborhood. -/
theorem lemma_6_2_4 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {C S : Set (EuclideanSpace ℝ (Fin n))} {P : arpFirstOrderConvexSettings p}
    {ε L : ℝ} {D : arpFirstOrderConvexData (EuclideanSpace ℝ (Fin n))} {N i : ℕ}
    (h : arpFirstOrderConvexRun f C P ε D N) (hclosed : IsClosed C)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hs : P.eta1 ≤ D.ratio i) :
    let σmax := max P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))
    let κ₁ := P.eta1 * P.sigmaMin / (p + 1).factorial *
      (p.factorial / (L + σmax + P.theta * p.factorial)) ^ (((p + 1 : ℕ) : ℝ) / p)
    κ₁ * TaylorModel.constrainedCriticality f 1 C (D.point (i + 1)) 1 ^
      (((p + 1 : ℕ) : ℝ) / p) ≤ f (D.point i) - f (D.point (i + 1)) :=
  h.successful_decrease hclosed hS hCS hC hf hL hlip hi hs

/-- **Theorem6.2.5.** Fixed exact positive source constants precede every
accuracy and every genuine ARp1-CC execution. Primitive consistent prefixes
reach the first actual constrained first-order stop. The initialized objective
and actual per-order derivative schedules satisfy the complete printed bounds.
A constrained global model minimum supplies a genuine feasible permitted step
at every point of positive first-order criticality. -/
theorem theorem_6_2_5 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {C S : Set (EuclideanSpace ℝ (Fin n))}
    (P : arpFirstOrderConvexSettings p) (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S)
    (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S) {L flow : ℝ} (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = (p + 1).factorial / (P.eta1 * P.sigmaMin) *
        ((L + ConvexRegularization.parameterCap P L + P.theta * p.factorial) / p.factorial) ^
          (((p + 1 : ℕ) : ℝ) / p) ∧
      κA = κS * (1 + |Real.log P.gamma1| / Real.log P.gamma2) ∧
      κC = |Real.log P.gamma1| / Real.log P.gamma2 +
        Real.log (ConvexRegularization.parameterCap P L / P.sigmaInitial) /
          Real.log P.gamma2 + 2 ∧
      ∀ (ε : ℝ) (D : arpFirstOrderConvexData (EuclideanSpace ℝ (Fin n))),
        (∀ N, (∀ i < N, ε < TaylorModel.constrainedCriticality f 1 C (D.point i) 1) →
          arpFirstOrderConvexRun f C P ε D N) →
        ∃ K, TaylorModel.constrainedCriticality f 1 C (D.point K) 1 ≤ ε ∧
          arpFirstOrderConvexRun f C P ε D K ∧
          (∀ i < K, ε < TaylorModel.constrainedCriticality f 1 C (D.point i) 1) ∧
          (ConvexRegularization.functionEvaluations K : ℝ) ≤ κA * (f (D.point 0) - flow) /
            ε ^ (((p + 1 : ℕ) : ℝ) / p) + κC ∧
          (ConvexRegularization.derivativeEvaluations P D K : ℝ) ≤
            κS * (f (D.point 0) - flow) /
            ε ^ (((p + 1 : ℕ) : ℝ) / p) + 2 ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ p →
            (ConvexRegularization.derivativeEvaluationsAtOrder P D K j : ℝ) ≤
              κS * (f (D.point 0) - flow) / ε ^ (((p + 1 : ℕ) : ℝ) / p) + 2 :=
  ConvexRegularization.exists_uniform_first_order_complexity P hclosed hS hCS hC hf hL
    hlip hlow

end CartisGouldToint
