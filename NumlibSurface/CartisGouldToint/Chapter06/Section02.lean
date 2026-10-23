import Numlib.Optimization.Regularization.Convex.DecreaseCounterexample
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

section DecreaseCounterexample
open ConvexRegularization.DecreaseCounterexample

/-- **Counterexample to the literal coefficient of Lemma6.2.2.** The genuine
p=2 first-order-only constrained execution has an exactly stationary improving
model trial. Both true criticality tests fail at the legal requested accuracy.
The literal coefficient with p! predicts a decrease larger than the actual
quadratic decrease. The model penalty uses(p+1)!, as reflected by the separately
proved fixed-tolerance decrease helpers. -/
theorem lemma_6_2_2_counterexample :
    IsClosed (univ : Set E) ∧ Convex ℝ (univ : Set E) ∧ (univ : Set E).Nonempty ∧
      ContDiff ℝ 2 objective ∧ 0 < L ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 objective x - iteratedFDeriv ℝ 2 objective y‖ ≤
        L * ‖x-y‖) ∧
      0 < epsilon ∧ epsilon < 1 ∧ ConvexRegularization.parameterCap settings L = 1 ∧
      ConvexRegularization.Run objective univ settings epsilon data 1 ∧
      settings.eta1 ≤ data.ratio 0 ∧
      epsilon < TaylorModel.constrainedCriticality objective 1 univ (data.point 0) 1 ∧
      epsilon < TaylorModel.constrainedCriticality objective 1 univ (data.point 1) 1 ∧
      fderiv ℝ (HighOrderRegularization.model objective 2 0 1) v = 0 ∧
      objective (data.point 0) - objective (data.point 1) = 667/4000 ∧
      printedCoefficient = settings.eta1 * settings.sigmaMin / (2 : ℕ).factorial *
        ((2 : ℕ).factorial * (1-settings.theta) /
          (L + ConvexRegularization.parameterCap settings L)) ^ (3/2 : ℝ) ∧
      printedCoefficient * epsilon ^ (3/2 : ℝ) = 342657/2000000 ∧
      ¬printedCoefficient * epsilon ^ (3/2 : ℝ) <
        objective (data.point 0) - objective (data.point 1) := by
  refine ⟨isClosed_univ,convex_univ,⟨0,mem_univ _⟩,objective_contDiff 2,
    by norm_num [L],objective_lipschitz,epsilon_bounds.1,
    epsilon_bounds.2.trans (by norm_num),parameter_cap,run,
    by norm_num [settings,data],initial_fails,endpoint_fails,model_derivative_zero,
    ?_,rfl,printed_decrease_value,printed_decrease_fails⟩
  norm_num [data,objective_values.1,objective_values.2]

end DecreaseCounterexample

end CartisGouldToint
