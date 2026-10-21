import NumlibSurface.CartisGouldToint.Chapter14.Section03.BoundaryCounterexample
import Numlib.Optimization.ConstrainedRegularization
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Chapter 14, Section 3: an actual regularization backend at the equality boundary

The finite boundary execution uses Algorithm 6.2.2 (ARp1-CC), with its step-scaled
model test (6.2.29), weak stopping test (6.2.8), and inherited parameter conditions (6.2.7).
Its acceptance ratio uses the unregularized Taylor prediction. The finite oracle
schedules are exactly the paid schedules of the complete two-phase execution.
-/

noncomputable section
open Set Metric Optimization Optimization.ConstrainedRegularization
open Optimization.HigherOrderRegularization Optimization.RegularizedTaylorModel
open Optimization.FeasibleCriticality Optimization.ParameterUpdates
open scoped InnerProductSpace
namespace CartisGouldToint.Chapter14.Section03.TwoPhaseBoundary

/-- Fixed admissible parameters of the actual first-order regularization backend. -/
def regularizationParameters : RegularizationParameters where
  eta1 := 1 / 4
  eta2 := 2 / 5
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1 / 4
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num

/-- The initial point has the exact squared step norm. -/
theorem initial_norm_sq : ‖initialPoint‖ ^ 2 = 180 / 169 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [initialPoint, Fin.sum_univ_two]

/-- The trial reaches the returned point with a nonzero displacement. -/
theorem negative_initial_ne_zero : -initialPoint ≠ (0 : Plane) := by
  intro h
  have hh := congrArg (fun z : Plane => z 1) h
  norm_num [initialPoint] at hh

/-- The actual linear Taylor prediction is strictly positive. -/
theorem regularization_prediction :
    taylorModel (TargetLeastSquares.objective objective constraint 0) 1 initialPoint 0 -
      taylorModel (TargetLeastSquares.objective objective constraint 0) 1 initialPoint
        (-initialPoint) = 273 / 338 := by
  simp only [taylorModel_zero, taylorModel_one, target_fderiv_at]
  norm_num [targetGradient, scalarConstraint, objective, initialPoint, innerSL_apply_apply,
    PiLp.inner_apply, Fin.sum_univ_two]

/-- The regularized linear model decreases by a strictly positive amount. -/
theorem regularization_model_decrease :
    model (TargetLeastSquares.objective objective constraint 0) 1 initialPoint (3 / 4)
        (-initialPoint) <
      model (TargetLeastSquares.objective objective constraint 0) 1 initialPoint (3 / 4) 0 := by
  have h := regularization_prediction
  rw [model_zero]
  norm_num only [model, Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, Nat.cast_one,
    mul_one, div_div] at ⊢
  rw [norm_neg, initial_norm_sq]
  simp only [taylorModel_zero] at h
  linarith

/-- The actual acceptance ratio is above the very-successful threshold. -/
theorem regularization_ratio :
    ratio (TargetLeastSquares.objective objective constraint 0) 1 initialPoint
      (-initialPoint) = 169 / 364 := by
  rw [ratio, ite_eq_right negative_initial_ne_zero, regularization_prediction]
  simp only [add_neg_cancel]
  rw [target_objective_eq]
  norm_num [scalarConstraint, objective, initialPoint]

/-- The derivative of the actual regularized linear model. -/
theorem regularization_model_fderiv :
    fderiv ℝ (model (TargetLeastSquares.objective objective constraint 0) 1 initialPoint
      (3 / 4)) (-initialPoint) =
      innerSL ℝ (WithLp.toLp 2 ![23 / 52, 3 / 13] : Plane) := by
  have he : model (TargetLeastSquares.objective objective constraint 0) 1 initialPoint
      (3 / 4) = fun s => TargetLeastSquares.objective objective constraint 0 initialPoint +
        innerSL ℝ (targetGradient initialPoint) s + (3 / 8 : ℝ) * ‖s‖ ^ 2 := by
    funext s
    norm_num [model, taylorModel_one, target_fderiv_at]
  rw [he]
  have hh := (((innerSL ℝ (targetGradient initialPoint)).hasFDerivAt
    (x := -initialPoint)).const_add
      (TargetLeastSquares.objective objective constraint 0 initialPoint)).add
        ((hasStrictFDerivAt_norm_sq (-initialPoint)).hasFDerivAt.const_mul (3 / 8 : ℝ))
  calc
    _ = _ := hh.fderiv
    _ = _ := by
      ext z
      simp [targetGradient, scalarConstraint, objective, initialPoint, innerSL_apply_apply,
        PiLp.inner_apply, Fin.sum_univ_two]
      ring

/-- The actual model criticality satisfies the step-scaled first-order test. -/
theorem regularization_model_test :
    feasibleCriticality X (initialPoint + -initialPoint)
      (fderiv ℝ (model (TargetLeastSquares.objective objective constraint 0) 1 initialPoint
        (3 / 4)) (-initialPoint)) ≤ (1 / 2 : ℝ) * ‖-initialPoint‖ := by
  rw [add_neg_cancel, regularization_model_fderiv]
  apply (feasibleCriticality_le_iff simple_set_properties.1 (by simp [X]) _).mpr
  intro d hd
  have hn : ‖(WithLp.toLp 2 ![23 / 52, 3 / 13] : Plane)‖ ^ 2 = 673 / 2704 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_two]
  have hb : ‖(WithLp.toLp 2 ![23 / 52, 3 / 13] : Plane)‖ ≤
      (1 / 2 : ℝ) * ‖-initialPoint‖ := by
    rw [norm_neg]
    nlinarith [initial_norm_sq, norm_nonneg initialPoint,
      norm_nonneg (WithLp.toLp 2 ![23 / 52, 3 / 13] : Plane)]
  have he := (innerSL ℝ (WithLp.toLp 2 ![23 / 52, 3 / 13] : Plane)).le_opNorm d
  rw [innerSL_apply_norm] at he
  have he' : |innerSL ℝ (WithLp.toLp 2 ![23 / 52, 3 / 13] : Plane) d| ≤
      ‖(WithLp.toLp 2 ![23 / 52, 3 / 13] : Plane)‖ * ‖d‖ := by
    simpa only [Real.norm_eq_abs] using he
  exact (neg_le_abs _).trans (he'.trans
    ((mul_le_of_le_one_right (norm_nonneg _) hd.2).trans hb))

/-- The retained regularization parameter decreases within its very-successful interval. -/
def backendSigma (k : ℕ) : ℝ := if k = 0 then 3 / 4 else 1 / 2

/-- At the output, the first feasible derivative criticality equals the true Taylor gap. -/
theorem output_feasible_criticality :
    feasibleCriticality X (0 : Plane)
      (fderiv ℝ (TargetLeastSquares.objective objective constraint 0) 0) = 1 / 8 := by
  unfold feasibleCriticality
  convert target_gap using 1
  congr 1
  · funext d
    exact (Optimization.TaylorCriticality.taylorDecrement_one _ _ _).symm
  · ext d
    simp [unitFeasibleSteps, Optimization.ConstrainedTaylorCriticality.mem_feasibleDisplacements]

/-- The initial derivative test fails on an actual feasible unit displacement. -/
theorem initial_criticality_failure :
    ¬feasibleCriticality X initialPoint
      (fderiv ℝ (TargetLeastSquares.objective objective constraint 0) initialPoint) ≤
        (1 / 8 : ℝ) := by
  let d : Plane := WithLp.toLp 2 ![0, -1]
  have hd : d ∈ unitFeasibleSteps X initialPoint := by
    have hs : ‖initialPoint + d‖ ^ 2 = 37 / 169 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [initialPoint, d, Fin.sum_univ_two]
    have hn : ‖d‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [d, Fin.sum_univ_two]
    constructor
    · change dist (initialPoint + d) 0 ≤ 3
      rw [dist_zero_right]
      nlinarith [norm_nonneg (initialPoint + d)]
    · nlinarith [norm_nonneg d]
  have hb := neg_apply_le_feasibleCriticality simple_set_properties.1
    (fderiv ℝ (TargetLeastSquares.objective objective constraint 0) initialPoint) hd
  have he : -fderiv ℝ (TargetLeastSquares.objective objective constraint 0) initialPoint d =
      12 / 13 := by
    rw [target_fderiv_at]
    norm_num [targetGradient, scalarConstraint, objective, initialPoint, d,
      innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_two]
  rw [he] at hb
  linarith

/-- The additional inherited parameter restrictions (6.2.7) of Algorithm 6.2.2 are
satisfied by the chosen first-order model tolerance. Higher-order tests are disabled. -/
theorem source_model_parameters :
    ∃ τ₁ τ₂ θ₂ θ₃ : ℝ, τ₁ ∈ Ioo 0 1 ∧ τ₂ ∈ Ioo 0 1 ∧
      θ₂ ∈ Ioo 0 1 ∧ θ₃ ∈ Ioo 0 1 ∧
      (1 / 2 : ℝ) * (1 + τ₁) ≤ 3 / 4 ∧ (1 / 2 : ℝ) * (1 + τ₂) ≤ θ₂ := by
  refine ⟨1 / 4, 1 / 4, 3 / 4, 3 / 4, ?_⟩
  norm_num

/-- The complete recorded inner call is a genuine Algorithm 6.2.2 AR1-CC execution, including
its first stopping test and the retained parameter update. -/
theorem actual_regularization_run :
    FirstOrderRun regularizationParameters 1 (3 / 4) (1 / 8)
      (TargetLeastSquares.objective objective constraint 0) X ordinaryInner.point
      (fun _ => -initialPoint) backendSigma 1 := by
  refine { initial_lower := by norm_num [regularizationParameters, backendSigma]
           update := ?_, decrease := ?_, iterate := ?_,
           initial_feasible := initial_feasible, trial_feasible := ?_,
           degree_pos := by norm_num, theta_mem := by norm_num,
           epsilon_pos := by norm_num, residual := ?_, terminal := ?_, first := ?_ }
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [ordinaryInner, backendSigma, regularizationParameters, regularization_ratio]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact regularization_model_decrease
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [ordinaryInner, regularizationParameters, regularization_ratio]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp [ordinaryInner, X]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    have hb : (1 / 2 : ℝ) * ‖-initialPoint‖ ≤ (3 / 4 : ℝ) * ‖-initialPoint‖ := by
      nlinarith [norm_nonneg (-initialPoint)]
    simpa only [ordinaryInner, backendSigma, ite_true, pow_one] using
      regularization_model_test.trans hb
  · simpa [ordinaryInner] using output_feasible_criticality.le
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact initial_criticality_failure

/-- The recorded value queries are exactly the backend's initial and actual trial queries. -/
theorem backend_function_queries :
    functionQueryPoints ordinaryInner.point (fun _ => -initialPoint) 1 =
      [ordinaryInner.point 0, ordinaryInner.point ordinaryInner.length] := by
  simp [functionQueryPoints, ordinaryInner]

/-- The recorded derivative queries are exactly the initial and accepted-successor queries. -/
theorem backend_derivative_queries :
    derivativeQueryPoints regularizationParameters 1
      (TargetLeastSquares.objective objective constraint 0) ordinaryInner.point
      (fun _ => -initialPoint) 1 =
      [ordinaryInner.point 0, ordinaryInner.point ordinaryInner.length] := by
  norm_num [derivativeQueryPoints, Finset.range_one, Finset.filter_singleton, ordinaryInner,
    regularizationParameters, regularization_ratio]

/-- The sole actual Phase-2 call is the complete inner trace of the backend proof. -/
theorem phase_two_inner_eq_ordinary : phaseTwoTrace.inner 0 = ordinaryInner := by
  simp only [phaseTwoTrace, Optimization.ResidualLeastSquares.InnerTrace.prefix, ordinaryInner]
  congr 1
  funext i
  by_cases hi : i < 1
  · simp [hi, show i ≤ 1 by omega]
  · by_cases hie : i = 1
    · subst i
      rfl
    · simp [hi, hie, show ¬i ≤ 1 by omega]

/-- Every actually executed optimality-phase invocation is a complete actual AR1 run. -/
theorem every_executed_backend (k : ℕ) (hk : k < 1) :
    FirstOrderRun regularizationParameters 1 (3 / 4) (1 / 8)
      (TargetLeastSquares.objective objective constraint (phaseTwoTrace.target k)) X
      (phaseTwoTrace.inner k).point (fun _ => -initialPoint) backendSigma
      (phaseTwoTrace.inner k).length := by
  have hk0 : k = 0 := by omega
  subst k
  rw [phase_two_inner_eq_ordinary]
  exact actual_regularization_run

/-- The actual backend has the exponent prescribed in the simply constrained table. -/
theorem regularization_exponent :
    Chapter14.Section02.simpleConstraintExponent .ar 1 1 1 X (fun x : Plane => x 0) = 2 := by
  norm_num [Chapter14.Section02.simpleConstraintExponent, simple_set_properties.2.1]

/-- The backend's objective-query count is exactly the complete INNER event count. -/
theorem backend_function_count : functionEvaluations 1 = ordinaryInner.evaluations .function := by
  rw [ordinary_evaluations]
  rfl

/-- The backend's cached derivative count is exactly the complete INNER event count. -/
theorem backend_derivative_count :
    derivativeEvaluations regularizationParameters 1
      (TargetLeastSquares.objective objective constraint 0) ordinaryInner.point
      (fun _ => -initialPoint) 1 = ordinaryInner.evaluations .derivative := by
  rw [← length_derivativeQueryPoints, backend_derivative_queries, ordinary_evaluations]
  rfl

end CartisGouldToint.Chapter14.Section03.TwoPhaseBoundary

namespace CartisGouldToint.Chapter14.Section03
open TwoPhaseBoundary

/-- The correctness clause of Theorem 14.3.9 fails for a complete actual regularization
backend execution. All source geometry, positive-jet and tube bounds hold. Phase 1 has
no inner call; the sole Phase-2 call is a complete genuine constrained AR1 run with exactly
the paid objective and cached derivative schedules. The first-order exponent is exactly
the source table's value two. The returned point admits neither printed alternative. -/
theorem regularized_two_phase_boundary_counterexample :
    IsClosed X ∧ Convex ℝ X ∧ X.Nonempty ∧
      BoundedLipschitzJetsNearFeasibleSet objective 1 X ∧
      ComponentwiseBoundedLipschitzJetsNearFeasibleSet constraint 1 X ∧
      TwoPhaseTubeObjectiveBounds objective constraint X 1 (-3) 3 ∧
      (∃ τ₁ τ₂ θ₂ θ₃ : ℝ, τ₁ ∈ Ioo 0 1 ∧ τ₂ ∈ Ioo 0 1 ∧
        θ₂ ∈ Ioo 0 1 ∧ θ₃ ∈ Ioo 0 1 ∧
        (1 / 2 : ℝ) * (1 + τ₁) ≤ 3 / 4 ∧ (1 / 2 : ℝ) * (1 + τ₂) ≤ θ₂) ∧
      algorithm_14_3_2 objective constraint X 1 (1 / 2) 1 (1 / 2) (1 / 2)
        (fun _ => 1 / 4) (fun _ => 2) (fun _ => 1) (fun _ => 1)
        (innerStep 0) (innerTerminal 0) innerStep innerTerminal
        phaseOneTrace 0 phaseTwoTrace 1 ∧
      (∀ k < 1, FirstOrderRun regularizationParameters 1 (3 / 4) (1 / 8)
        (TargetLeastSquares.objective objective constraint (phaseTwoTrace.target k)) X
        (phaseTwoTrace.inner k).point (fun _ => -initialPoint) backendSigma
        (phaseTwoTrace.inner k).length) ∧
      functionQueryPoints ordinaryInner.point (fun _ => -initialPoint) 1 =
        [ordinaryInner.point 0, ordinaryInner.point ordinaryInner.length] ∧
      derivativeQueryPoints regularizationParameters 1
        (TargetLeastSquares.objective objective constraint 0) ordinaryInner.point
        (fun _ => -initialPoint) 1 =
        [ordinaryInner.point 0, ordinaryInner.point ordinaryInner.length] ∧
      functionEvaluations 1 = ordinaryInner.evaluations .function ∧
      derivativeEvaluations regularizationParameters 1
        (TargetLeastSquares.objective objective constraint 0) ordinaryInner.point
        (fun _ => -initialPoint) 1 = ordinaryInner.evaluations .derivative ∧
      phaseTwoTrace.point 1 = (0 : Plane) ∧
      ‖constraint (0 : Plane)‖ = 1 / 2 ∧
      ¬((1 / 2 : ℝ) < ‖constraint (0 : Plane)‖ ∨
        ∃ y : EuclideanSpace ℝ (Fin 1),
          Optimization.TaylorCriticality.gapOn
            (Optimization.TaylorCriticality.taylorDecrement
              (fun x => twoPhaseLagrangian objective constraint x y) 1 0)
            (Optimization.ConstrainedTaylorCriticality.feasibleDisplacements X
              (0 : Plane) ∩ closedBall 0 1) ≤
              (1 / 4 : ℝ) * Chapter07.Section01.multiplierScale y) :=
  ⟨simple_set_properties.1, simple_set_properties.2.1, simple_set_properties.2.2,
    component_jets.1, component_jets.2, tube_bounds, source_model_parameters, actual_execution,
    every_executed_backend,
    backend_function_queries, backend_derivative_queries, backend_function_count,
    backend_derivative_count, rfl, output_values.2, termination_alternatives_fail⟩

end CartisGouldToint.Chapter14.Section03
