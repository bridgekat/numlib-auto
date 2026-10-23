import Numlib.Optimization.Regularization.Convex.TargetObstruction
import Numlib.Optimization.Regularization.Convex.DerivativeComplexity
import NumlibSurface.CartisGouldToint.Chapter06.Section01
import Numlib.Optimization.Regularization.Convex.CorrectedStep
import Numlib.Optimization.Regularization.Convex.DerivativeStep
import Numlib.Optimization.Regularization.Convex.DirectionCounterexample
import Numlib.Optimization.Regularization.Convex.DecreaseCounterexample
import Numlib.Optimization.Regularization.Convex.FirstOrderStep
import Numlib.Optimization.Regularization.Convex.FirstOrderComplexity
import Numlib.Optimization.Regularization.Convex.StepExistence

/-!
# Actual first- to third-order regularization with convex constraints

The ARp1-CC variant uses the step-scaled genuine constrained model measure.
Its successful decrease has the exact source coefficient. The full ARp-CC
execution uses every enabled actual restricted derivative test, with local Cp
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

section DirectionCounterexample
open ConvexRegularization.DirectionCounterexample
open HighOrderRegularization.ObstructionCounterexample (objective)

/-- **Counterexample to the literal directional clause of Lemma6.2.1.**
The source C¹ set in(6.1.8) does not include the unit ball. The genuine scalar
quadratic execution accepts a model trial to its minimizer. Direction100 is in
C¹ because the true endpoint derivative is zero, yet its actual model
functional has magnitude25, exceeding the displayed constant53/4. The
separately proved tensor-error estimates retain the required unit-ball domain. -/
theorem lemma_6_2_1_counterexample :
    IsClosed (univ : Set ℝ) ∧ Convex ℝ (univ : Set ℝ) ∧ (univ : Set ℝ).Nonempty ∧
      ContDiff ℝ 1 objective ∧
      (∀ x y : ℝ, ‖iteratedFDeriv ℝ 1 objective x -
        iteratedFDeriv ℝ 1 objective y‖ ≤ ‖x-y‖) ∧
      ConvexRegularization.Run objective univ settings (1/2) data 1 ∧
      settings.eta1 ≤ data.ratio 0 ∧ ConvexRegularization.parameterCap settings 1 = 12 ∧
      (data.point 0 = 1 ∧ data.point 1 = 0 ∧ data.step 0 = -1) ∧
      (100 : ℝ) ∈ TaylorModel.firstRestrictedDirections objective
        (TaylorModel.feasibleDisplacements univ (data.point 1)) (data.point 1)
        (settings.tau*(1/2)) ∧
      ‖(100 : ℝ)‖ = 100 ∧
      |fderiv ℝ (HighOrderRegularization.model objective 1 (data.point 0)
        (data.parameter 0)) (data.step 0) (100 : ℝ)| = 25 ∧
      ((1 : ℝ)+ConvexRegularization.parameterCap settings 1) / (1 : ℕ).factorial *
        ‖data.step 0‖ ^ 1 + settings.tau*(1/2) = 53/4 ∧
      ¬|fderiv ℝ (HighOrderRegularization.model objective 1 (data.point 0)
        (data.parameter 0)) (data.step 0) (100 : ℝ)| ≤
          ((1 : ℝ)+ConvexRegularization.parameterCap settings 1) / (1 : ℕ).factorial *
            ‖data.step 0‖ ^ 1 + settings.tau*(1/2) := by
  exact ⟨isClosed_univ,convex_univ,⟨0,mem_univ _⟩,regularity.1,regularity.2,run,
    by norm_num [settings,data],parameter_cap,⟨rfl,rfl,rfl⟩,restricted_direction,
    by norm_num,directional_value,printed_error_value,directional_bound_fails⟩

end DirectionCounterexample

/-- **Corrected Lemma6.2.1.** Every enabled order has the full printed strict
step bound on the actual model-restricted endpoint directions. The first
component is exactly the true constrained first-order measure, and the higher
components use the actual second and third objective derivatives. Both final
directional clauses retain the necessary unit-ball restriction. The exact
source parameter cap follows from the primitive actual prefix rules using only
local Cp regularity on an open neighborhood of the convex feasible set. -/
theorem lemma_6_2_1_corrected {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {C S : Set (EuclideanSpace ℝ (Fin n))}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N i : ℕ}
    (h : HighOrderRegularization.ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hx : ∀ k < N, x k ∈ C) (hxs : ∀ k < N, x k + s k ∈ C)
    (q : Fin 3) (hp : q.val + 1 ≤ p) (ε θ : Fin 3 → ℝ)
    (hε : ∀ j, 0 < ε j) (hθ : ∀ j, 0 < θ j)
    (hm : ∀ j ≤ q, ConvexRegularization.modelDerivativeCriticality f p C (x i) (σ i) (s i)
      (θ 0 * ε 0) (θ 1 * ε 1) j ≤ θ j * ε j)
    (hi : i < N) (hs : η₁ ≤ ρ i) (τ₁ τ₂ : ℝ) :
    let σmax := max (σ 0) (γ₃ * L / (1 - η₂))
    (∀ j : Fin 3, j ≤ q →
      ε j < TaylorModel.tensorCriticality (iteratedFDeriv ℝ (j.val + 1) f (x (i + 1)))
        (ConvexRegularization.modelRestrictedDirections f p C (x i) (σ i) (s i)
          (θ 0 * ε 0) (θ 1 * ε 1) j) →
      (p - j.val).factorial * (1 - θ j) / (L + σmax) * ε j < ‖s i‖^(p - j.val)) ∧
    (∀ d ∈ TaylorModel.firstRestrictedDirections f
        (TaylorModel.feasibleDisplacements C (x (i + 1)))
        (x (i + 1)) (τ₁ * ε 0), ‖d‖ ≤ 1 →
      |fderiv ℝ (HighOrderRegularization.model f p (x i) (σ i)) (s i) d| ≤
        (L + σmax) / p.factorial * ‖s i‖^p + τ₁ * ε 0) ∧
    (1 ≤ q.val → ∀ d ∈ TaylorModel.secondRestrictedDirections f
        (TaylorModel.feasibleDisplacements C (x (i + 1))) (x (i + 1)) (τ₁ * ε 0) (τ₂ * ε 1),
      ‖d‖ ≤ 1 →
      |iteratedFDeriv ℝ 2 (HighOrderRegularization.model f p (x i) (σ i)) (s i) (fun _ => d)| ≤
        (L + σmax) / (p - 1).factorial * ‖s i‖^(p - 1) + τ₂ * ε 1) :=
  ConvexRegularization.constrained_step_estimates h hS hCS hC hf hL hlip hx hxs q hp ε θ
    hε hθ hm hi hs τ₁ τ₂

/-- Fixed legal ARp-CC settings and its explicit number of enabled derivative tests. -/
abbrev arpConvexSettings := ConvexRegularization.DerivativeSettings

/-- Actual ARp-CC execution with genuine objective/model derivative restrictions,
feasible trials, objective ratios, parameter intervals and pretrial test failures. -/
abbrev arpConvexRun := @ConvexRegularization.DerivativeRun

/-- The literal ARp-CC termination test on all enabled true objective measures. -/
abbrev arpConvexStop := @ConvexRegularization.derivativeStop

/-- **Execution companion to Theorem6.2.3.** Fixed positive constants precede
every requested accuracy and actual finite-third-order ARp-CC execution.
The first literal true stop and initialized evaluation counts have the three
source accuracy powers, with an explicit two-site derivative overhead. The proof uses
the genuine(p+1)! model-penalty coefficient; the constants in this theorem are
existential, so the erroneous explicit coefficient of Lemma6.2.2 is unnecessary.
The hypothesis specifies consistent actual primitive prefixes; availability of
all third-order steps is a separate property and is not asserted here. -/
theorem theorem_6_2_3_execution {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {C S : Set (EuclideanSpace ℝ (Fin n))} (P : arpConvexSettings p 2)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L flow : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      ∀ (ε : Fin 3 → ℝ) (D : arpFirstOrderConvexData (EuclideanSpace ℝ (Fin n))),
        (∀ N, (∀ i < N, ¬arpConvexStop f C P ε (D.point i)) →
          arpConvexRun f C P ε D N) →
        ∃ K, (∀ j : Fin 3,
            constrainedCriticality f C (D.point K) P.tau P.tauTwo (ε 0) (ε 1) j ≤ ε j) ∧
          arpConvexRun f C P ε D K ∧
          (∀ i < K, ¬arpConvexStop f C P ε (D.point i)) ∧
          (ConvexRegularization.functionEvaluations K : ℝ) ≤
            κA * (f (D.point 0) - flow) /
              HighOrderRegularization.finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) + κC ∧
          (ConvexRegularization.derivativeEvaluations P.toSettings D K : ℝ) ≤
            κS * (f (D.point 0) - flow) /
              HighOrderRegularization.finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) + 2 ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ p →
            (ConvexRegularization.derivativeEvaluationsForOrder P D K j : ℝ) ≤
              κS * (f (D.point 0) - flow) /
                HighOrderRegularization.finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) + 2 := by
  obtain ⟨κS,hSpos,κA,hApos,κC,hCpos,hall⟩ :=
    ConvexRegularization.exists_uniform_derivative_complexity P hS hCS hC hf hL hlip hlow
  refine ⟨κS,hSpos,κA,hApos,κC,hCpos,?_⟩
  intro ε D hprefix
  obtain ⟨K,hstop,hK,hfirst,hF,hD,hDj⟩ := hall ε D hprefix
  refine ⟨K,?_,hK,hfirst,hF,hD,hDj⟩
  intro j
  have hj := hstop j (Fin.le_last j)
  fin_cases j
  · change TaylorModel.constrainedCriticality f 1 C (D.point K) 1 ≤ ε 0
    change ConvexRegularization.objectiveDerivativeCriticality f C (D.point K)
      (P.tau * ε 0) (P.tauTwo * ε 1) 0 ≤ ε 0 at hj
    rw [ConvexRegularization.objectiveDerivativeCriticality_zero] at hj
    exact hj
  · exact hj
  · exact hj

section ThirdOrderTargetObstruction
open ConvexRegularization.TargetObstruction

/-- **Counterexample to the literal output assertion of Theorem6.2.3.**
The genuine Euclidean quartic has a global minimum and globally Lipschitz third
derivative. With the displayed legal independent tolerances, every point passing
the first true test fails the third true test. At the global minimizer zero,
the actual regularized cubic model equals the objective, so the algorithm's
strict-improvement step is unavailable although its literal stop fails. The
separate execution companion retains valid counts for consistent actual runs. -/
theorem theorem_6_2_3_counterexample :
    IsClosed (univ : Set E) ∧ Convex ℝ (univ : Set E) ∧ (univ : Set E).Nonempty ∧
      ContDiff ℝ 3 euclideanObjective ∧ (∀ x : E, 0 ≤ euclideanObjective x) ∧
      euclideanObjective 0 = 0 ∧ IsMinOn euclideanObjective univ 0 ∧
      (∀ x y : E, ‖iteratedFDeriv ℝ 3 euclideanObjective x -
        iteratedFDeriv ℝ 3 euclideanObjective y‖ ≤ ‖x - y‖) ∧
      (∀ j : Fin 3, 0 < accuracy j ∧ accuracy j ≤ 1) ∧
      settings.tau = 1/2 ∧ settings.tauTwo = 1/2 ∧
      settings.sigmaInitial = 1 ∧ settings.sigmaMin = 1 ∧
      (∀ x : E, constrainedCriticality euclideanObjective univ x
        settings.tau settings.tauTwo (accuracy 0) (accuracy 1) 0 ≤ accuracy 0 →
        accuracy 2 < constrainedCriticality euclideanObjective univ x
          settings.tau settings.tauTwo (accuracy 0) (accuracy 1) 2) ∧
      (∀ x : E, ¬arpConvexStop euclideanObjective univ settings accuracy x) ∧
      (∀ s : E, HighOrderRegularization.model euclideanObjective 3 0 1 s =
        euclideanObjective s) ∧
      (∀ s : E, ¬HighOrderRegularization.model euclideanObjective 3 0 1 s <
        HighOrderRegularization.model euclideanObjective 3 0 1 0) ∧
      (∀ (D : arpFirstOrderConvexData E) (N : ℕ), D.point 0 = 0 →
        ¬arpConvexRun euclideanObjective univ settings accuracy D (N + 1)) := by
  refine ⟨isClosed_univ,convex_univ,⟨0,mem_univ _⟩,euclidean_contDiff,euclidean_nonneg,
    euclidean_zero,euclidean_global_minimum,euclidean_third_lipschitz,accuracy_bounds,
    rfl,rfl,rfl,rfl,?_,all_stops_fail,initial_model_eq,no_initial_step,no_positive_run⟩
  intro x hx
  exact euclidean_no_target hx

end ThirdOrderTargetObstruction

end CartisGouldToint
