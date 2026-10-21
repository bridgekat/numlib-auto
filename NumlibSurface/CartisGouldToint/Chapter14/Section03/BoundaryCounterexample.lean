import NumlibSurface.CartisGouldToint.Chapter14.Section03.TwoPhase
import Numlib.Optimization.TaylorCriticalityFirstOrder
import Numlib.Optimization.AffineJets

/-!
# Chapter 14, Section 3: the equality boundary in two-phase termination

The third Phase-2 branch permits equality between the final objective and its target.
The two-dimensional affine data carry an actual finite run;
all scalar and jet calculations concern the canonical objective and feasible Taylor gaps.
-/

noncomputable section
open Set Metric Optimization.ConstrainedTaylorCriticality Optimization.TaylorCriticality
open Optimization.ResidualLeastSquares Optimization.TwoPhaseTargets
open scoped InnerProductSpace
namespace CartisGouldToint.Chapter14.Section03.TwoPhaseBoundary
/-- The two-dimensional source domain of the boundary fixture. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-- The actual Lagrangian gradient at a scalar multiplier. -/
def g (y : ℝ) : Plane := WithLp.toLp 2 ![-y / 4, 1]
/-- The scalar-coordinate form of the source minus-sign Lagrangian. -/
def lagrangian (y : ℝ) (x : Plane) : ℝ := x 1 - y * (x 0 / 4 + 1 / 2)
/-- A closed convex simple set containing the complete unit ball at the output. -/
def X : Set Plane := closedBall 0 3

/-- Squared norm of the actual multiplier-dependent gradient. -/
theorem norm_g_sq (y : ℝ) : ‖g y‖ ^ 2 = y ^ 2 / 16 + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [g, Fin.sum_univ_two]
  ring

/-- Identification of the scalar Lagrangian with its affine linear functional. -/
theorem inner_g (y : ℝ) (x : Plane) : innerSL ℝ (g y) x - y / 2 = lagrangian y x := by
  simp [innerSL_apply_apply, PiLp.inner_apply, g, Fin.sum_univ_two, lagrangian]
  ring

/-- The actual Fréchet derivative of the scalar-coordinate Lagrangian. -/
theorem fderiv_lagrangian (y : ℝ) :
    fderiv ℝ (lagrangian y) 0 = innerSL ℝ (g y) := by
  have hh := ((innerSL ℝ (g y)).hasFDerivAt (x := (0 : Plane))).sub_const (y / 2)
  have he : (fun x : Plane => innerSL ℝ (g y) x - y / 2) = lagrangian y := by
    funext x
    exact inner_g y x
  rw [he] at hh
  exact hh.fderiv

/-- The entire unit displacement ball is feasible at the output. -/
theorem feasible_unit_ball : feasibleDisplacements X (0 : Plane) ∩ closedBall 0 1 =
    closedBall 0 1 := by
  apply inter_eq_right.mpr
  intro x hx
  simp only [mem_feasibleDisplacements, zero_add, X]
  exact closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3) hx

/-- The actual unit-radius first Taylor gap is the Lagrangian gradient norm. -/
theorem gap_lagrangian (y : ℝ) :
    gapOn (taylorDecrement (lagrangian y) 1 0)
      (feasibleDisplacements X (0 : Plane) ∩ closedBall 0 1) = ‖g y‖ := by
  rw [feasible_unit_ball, gapOn_taylorDecrement_one _ _ (by norm_num),
    fderiv_lagrangian, innerSL_apply_norm, one_mul]

/-- Every finite multiplier fails the printed scaled first-order inequality. -/
theorem fails_every_multiplier (y : ℝ) :
    (1 / 4 : ℝ) * Real.sqrt (1 + y ^ 2) <
      gapOn (taylorDecrement (lagrangian y) 1 0)
        (feasibleDisplacements X (0 : Plane) ∩ closedBall 0 1) := by
  rw [gap_lagrangian]
  have hs : (Real.sqrt (1 + y ^ 2)) ^ 2 = 1 + y ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hn := norm_g_sq y
  nlinarith [Real.sqrt_nonneg (1 + y ^ 2), norm_nonneg (g y)]
/-- The objective is the second coordinate. -/
def objective (x : Plane) : ℝ := x 1

/-- The single scalar constraint has a small nonzero first-coordinate derivative. -/
def scalarConstraint (x : Plane) : ℝ := x 0 / 4 + 1 / 2

/-- The actual one-dimensional Euclidean constraint residual. -/
def constraint (x : Plane) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 (fun _ => scalarConstraint x)

/-- The initial point meets the strict Phase-1 residual threshold. -/
def initialPoint : Plane := WithLp.toLp 2 ![-6 / 13, 12 / 13]

/-- The Euclidean constraint norm is its scalar absolute value. -/
theorem norm_constraint (x : Plane) : ‖constraint x‖ = |scalarConstraint x| := by
  rw [EuclideanSpace.norm_eq]
  simp [constraint, Real.sqrt_sq_eq_abs]

/-- Exact values of the affine data at the initial point. -/
theorem initial_values : objective initialPoint = 12 / 13 ∧
    ‖constraint initialPoint‖ = 5 / 13 := by
  constructor
  · rfl
  · norm_num [norm_constraint, scalarConstraint, initialPoint]

/-- Exact residual and objective values at the returned point. -/
theorem output_values : objective (0 : Plane) = 0 ∧ ‖constraint (0 : Plane)‖ = 1 / 2 := by
  simp [objective, norm_constraint, scalarConstraint]

/-- Both affine component families meet the source first-order neighbourhood assumptions. -/
theorem component_jets :
    BoundedLipschitzJetsNearFeasibleSet objective 1 X ∧
      ComponentwiseBoundedLipschitzJetsNearFeasibleSet constraint 1 X := by
  constructor
  · refine ⟨Set.univ, ‖(EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) : Plane →L[ℝ] ℝ)‖,
      0, Set.subset_univ _, ?_⟩
    convert affine_hasBoundedLipschitzJets_one
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) (0 : ℝ) using 1
    funext x
    change x 1 = x 1 + 0
    exact (add_zero _).symm
  · intro i
    let L : Plane →L[ℝ] ℝ := (1 / 4 : ℝ) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
    refine ⟨Set.univ, ‖L‖, 0, Set.subset_univ _, ?_⟩
    convert affine_hasBoundedLipschitzJets_one L (1 / 2 : ℝ) using 1
    funext x
    change x 0 / 4 + 1 / 2 = (1 / 4 : ℝ) * x 0 + 1 / 2
    ring

/-- The canonical target objective is the exact affine-residual quadratic. -/
theorem target_objective_eq (t : ℝ) :
    Optimization.TargetLeastSquares.objective objective constraint t =
      fun x => ((scalarConstraint x) ^ 2 + (objective x - t) ^ 2) / 2 := by
  funext x
  simp [Optimization.TargetLeastSquares.objective, norm_constraint, sq_abs]

/-- The exact first target-objective gradient, at an arbitrary point. -/
def targetGradient (x : Plane) : Plane :=
  WithLp.toLp 2 ![scalarConstraint x / 4, objective x]

/-- The derivative is the actual gradient functional of the squared affine residual. -/
theorem target_fderiv_at (x : Plane) :
    fderiv ℝ (Optimization.TargetLeastSquares.objective objective constraint 0) x =
      innerSL ℝ (targetGradient x) := by
  have hc : HasFDerivAt scalarConstraint
      ((1 / 4 : ℝ) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) x := by
    convert (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
      (x := x)).const_mul (1 / 4 : ℝ)).add_const (1 / 2 : ℝ) using 1
    funext z
    change z 0 / 4 + 1 / 2 = (1 / 4 : ℝ) * z 0 + 1 / 2
    ring
  have hf : HasFDerivAt objective (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have hh := ((hc.pow 2).add (hf.pow 2)).const_mul (1 / 2 : ℝ)
  simp only [Pi.add_apply] at hh
  have he : Optimization.TargetLeastSquares.objective objective constraint 0 =
      fun z => (1 / 2 : ℝ) * ((scalarConstraint z) ^ 2 + (objective z) ^ 2) := by
    rw [target_objective_eq]
    funext z
    simp only [sub_zero]
    ring
  rw [he, hh.fderiv]
  ext z
  simp [scalarConstraint, objective, targetGradient, innerSL_apply_apply, PiLp.inner_apply,
    Fin.sum_univ_two]
  ring

/-- The canonical target objective has the required actual derivative at the output. -/
theorem target_fderiv :
    fderiv ℝ (Optimization.TargetLeastSquares.objective objective constraint 0) 0 =
      innerSL ℝ (WithLp.toLp 2 ![1 / 8, 0] : Plane) := by
  convert target_fderiv_at 0 using 1
  norm_num [targetGradient, scalarConstraint, objective]

/-- At the output, the first target gap equals the prescribed inner accuracy exactly. -/
theorem target_gap :
    gapOn (taylorDecrement (Optimization.TargetLeastSquares.objective objective constraint 0)
      1 (0 : Plane)) (feasibleDisplacements X 0 ∩ closedBall 0 1) = 1 / 8 := by
  rw [feasible_unit_ball, gapOn_taylorDecrement_one _ _ (by norm_num), target_fderiv,
    innerSL_apply_norm, one_mul, EuclideanSpace.norm_eq]
  norm_num [Fin.sum_univ_two]

/-- The simple set satisfies the source geometric assumptions. -/
theorem simple_set_properties : IsClosed X ∧ Convex ℝ X ∧ X.Nonempty :=
  ⟨isClosed_closedBall, convex_closedBall _ _, ⟨0, by simp [X]⟩⟩

/-- The initial point lies inside the actual simple set. -/
theorem initial_feasible : initialPoint ∈ X := by
  have hs : ‖initialPoint‖ ^ 2 = 180 / 169 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [initialPoint, Fin.sum_univ_two]
  change dist initialPoint 0 ≤ 3
  rw [dist_zero_right]
  nlinarith [norm_nonneg initialPoint]

/-- The objective is bounded on the whole simple set and hence on its near-feasible tube. -/
theorem tube_bounds : TwoPhaseTubeObjectiveBounds objective constraint X 1 (-3) 3 := by
  rw [twoPhaseTubeObjectiveBounds_iff]
  intro x hx _
  have hn : ‖x‖ ≤ 3 := by simpa [X] using hx
  have he : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1
  exact abs_le.mp (he.trans hn)

/-- The literal deterministic translation used in the single actual Phase-2 transition. -/
def innerStep (_t : ℝ) (_τ : ℕ → ℝ) (a b : Plane × Unit)
    (events : List EvaluationKind) : Prop :=
  b.1 = a.1 - initialPoint ∧ events = [.function, .derivative]

/-- The terminal check records the actual endpoint and its two paid oracle channels. -/
def innerTerminal (_t : ℝ) (_τ : ℕ → ℝ) (a : Plane × Unit)
    (events : List EvaluationKind) : Prop :=
  a.1 = 0 ∧ events = [.function, .derivative]

/-- The actual one-transition complete inner trace. -/
def ordinaryInner : InnerTrace Plane Unit where
  point i := if i = 0 then initialPoint else 0
  state _ := ()
  length := 1
  queries i := if i ≤ 1 then [.function, .derivative] else []

/-- Each channel is charged at both the initial and the returned current point. -/
theorem ordinary_evaluations (a : EvaluationKind) : ordinaryInner.evaluations a = 2 := by
  cases a <;> norm_num [InnerTrace.evaluations, ordinaryInner, Finset.sum_range_succ]

/-- The actual complete invocation meets the ordinary INNER guarantees with fixed
coefficient one and exponent two, including the true target gap and paid terminal events. -/
theorem ordinary_contract : InnerContract X
    (Optimization.TargetLeastSquares.objective objective constraint 0) 0 1
    (fun _ => 1 / 8) (fun _ => 1) (fun _ => 2) (fun _ => 1)
    (innerStep 0) (innerTerminal 0) ordinaryInner := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h : i = 0
    · simpa [ordinaryInner, h] using initial_feasible
    · simp [ordinaryInner, h, X]
  · intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simp [innerStep, ordinaryInner]
  · simp [innerTerminal, ordinaryInner]
  · simp [ordinaryInner]
  · rw [target_objective_eq]
    norm_num [ordinaryInner, scalarConstraint, objective, initialPoint]
  · intro x _
    exact Optimization.TargetLeastSquares.objective_nonneg objective constraint 0 x
  · intro j _
    norm_num
  · intro j _
    norm_num
  · intro j _
    norm_num
  · intro j hj
    have hj1 : j = 1 := by have := Finset.mem_Icc.mp hj; omega
    subst j
    simpa [ordinaryInner] using target_gap.le
  · intro a
    norm_num
  · intro a
    have ht : 64 ≤ toleranceWeight 1 (fun _ => (1 / 8 : ℝ)) (fun _ => (2 : ℝ)) := by
      have hh := le_toleranceWeight (q := 1) (j := 1)
        (τ := fun _ => (1 / 8 : ℝ)) (π := fun _ => (2 : ℝ)) (by simp)
      norm_num [Real.rpow_neg, Real.rpow_two] at hh ⊢
      exact hh
    rw [ordinary_evaluations, target_objective_eq]
    norm_num [ordinaryInner, scalarConstraint, objective, initialPoint]
    linarith

/-- This complete call has no earlier target-interruption event. -/
def actualInnerCall : InterruptibleInnerCall X
    (Optimization.TargetLeastSquares.objective objective constraint 0) 0 1
    (fun _ => 1 / 8) (fun _ => 1) (fun _ => 2) (fun _ => 1)
    (innerStep 0) (innerTerminal 0) (TargetInterrupt objective constraint (1 / 2) 1 0)
    (ordinaryInner.prefix 1 (ordinaryInner.queries 1)) :=
  InterruptibleInnerCall.ofInnerContract ordinary_contract (by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    change ¬TargetInterrupt objective constraint (1 / 2) 1 0 initialPoint
    rw [TargetInterrupt]
    have hr : residualNorm objective constraint 0 initialPoint = 1 := by
      rw [residualNorm]
      norm_num [initial_values.1, initial_values.2]
    rw [hr, initial_values.1]
    norm_num)

/-- The zero-call LEN history remains at its initially feasible point. -/
def phaseOneTrace : Trace Plane Unit where
  point _ := initialPoint
  radius _ _ := 0
  state _ := ()
  inner _ :=
    { point := fun _ => initialPoint
      state := fun _ => ()
      length := 0
      queries := fun _ => [.function] }

/-- Every index of the constant LEN history already passes its residual stopping test. -/
theorem phase_one_stops (k : ℕ) :
    Stops X constraint 1 (1 / 2) (fun _ => 1 / 4) phaseOneTrace k := by
  left
  norm_num [phaseOneTrace, initial_values.2]

/-- The literal Phase-1 run makes no inner call, since its initial residual is small. -/
theorem phase_one_execution : algorithm_14_3_1_closedDual X constraint 1 (1 / 2) (1 / 2)
    (fun _ => 1 / 4) (fun _ => 2) (fun _ => 1)
    (innerStep 0) (innerTerminal 0) phaseOneTrace := by
  refine ⟨by norm_num, initial_feasible, by norm_num, ?_, by norm_num, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    norm_num
  · intro h
    norm_num [phaseOneTrace, initial_values.2] at h
  · intro j
    rfl
  · intro k
    rfl
  · intro k
    rfl
  · intro k
    rfl
  · intro k
    rfl
  · intro a
    norm_num
  · intro k h
    exact (h (phase_one_stops k)).elim

/-- The Phase-1 parameters satisfy the printed reciprocal restriction with a strictly
positive initial residual; no convention about a zero reciprocal is used. -/
theorem initial_factor : 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧
    (1 / 2 : ℝ) < (‖constraint initialPoint‖)⁻¹ := by
  norm_num [initial_values.2]

/-- This same Phase-1 history also uses the printed strict dual domain. -/
theorem phase_one_literal : algorithm_14_3_1 X constraint 1 (1 / 2) (1 / 2)
    (fun _ => 1 / 4) (fun _ => 2) (fun _ => 1)
    (innerStep 0) (innerTerminal 0) phaseOneTrace :=
  algorithm_14_3_1.ofClosedDual phase_one_execution (by intro j _; norm_num)
    (by exact ⟨initial_factor.1, lt_min initial_factor.2.1 initial_factor.2.2⟩)

/-- The finite outer history executes the single paid complete inner invocation. -/
def phaseTwoTrace : TargetTrace Plane Unit where
  point k := if k = 0 then initialPoint else 0
  target _ := 0
  radius _ _ := 1
  state _ := ()
  inner _ := ordinaryInner.prefix 1 (ordinaryInner.queries 1)
  initialQueries := [.function]

/-- The actual initial augmented residual is one. -/
theorem initial_residual : residualNorm objective constraint 0 initialPoint = 1 := by
  rw [residualNorm]
  norm_num [initial_values.1, initial_values.2]

/-- The actual output augmented residual lies exactly at the third-branch boundary. -/
theorem output_residual : residualNorm objective constraint 0 (0 : Plane) = 1 / 2 := by
  rw [residualNorm]
  norm_num [output_values.1, output_values.2]

/-- Paired value and derivative queries give exact raw component responses through order one. -/
def componentResponse (q : ℕ) (hq : q ≤ 1) (x : Plane) :
    ComponentOracleResponse objective constraint q x [.function, .derivative] where
  events := [.function, .derivative]
  paid := List.Sublist.refl _
  objectiveValue := objective x
  constraintValue := constraint x
  objectiveJet j := iteratedFDeriv ℝ (j.val + 1) objective x
  constraintJet j := iteratedFDeriv ℝ (j.val + 1) constraint x
  objective_exact := rfl
  constraint_exact := rfl
  objective_jet_exact _ := rfl
  constraint_jet_exact _ := rfl
  value_paid := by simp
  derivatives_paid := by simpa using hq

/-- The actual finite Phase-2 history satisfies every operational requirement. -/
theorem phase_two_execution : PhaseTwoExecution X objective constraint 1 (1 / 2) 1 (1 / 2)
    (fun _ => 1 / 4) (fun _ => 2) (fun _ => 1)
    innerStep innerTerminal phaseTwoTrace 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, by norm_num,
    initial_feasible, ?_, ?_, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    norm_num
  · norm_num [phaseTwoTrace, initial_values.2]
  · norm_num [phaseTwoTrace, resetTarget, initial_values.1, initial_values.2, Real.sqrt_div]
  · intro j _
    norm_num [phaseTwoTrace]
  · simp [phaseTwoTrace]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rfl
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rfl
  · intro k _
    rfl
  · intro k _
    rfl
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [phaseTwoTrace, initial_residual]
    exact ⟨actualInnerCall⟩
  · intro k hk i hi
    have hk0 : k = 0 := by omega
    subst k
    have hi1 : i ≤ 1 := hi
    have he : (phaseTwoTrace.inner 0).queries i = [.function, .derivative] := by
      by_cases hi0 : i = 0
      · subst i
        simp [phaseTwoTrace, InnerTrace.prefix, ordinaryInner]
      · have hiEq : i = 1 := by omega
        subst i
        simp [phaseTwoTrace, ordinaryInner]
    rw [he]
    exact ⟨componentResponse _ (by split_ifs <;> omega) _⟩
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp [phaseTwoTrace, targetAfter, output_residual, output_values.1]
  · intro k hk
    omega
  · left
    simp [phaseTwoTrace, output_residual, output_values.1]

/-- The complete actual two-phase run has a zero-call feasibility phase and one
ordinary inner call in the optimality phase. -/
theorem actual_execution : algorithm_14_3_2 objective constraint X 1 (1 / 2) 1
    (1 / 2) (1 / 2) (fun _ => 1 / 4) (fun _ => 2) (fun _ => 1) (fun _ => 1)
    (innerStep 0) (innerTerminal 0) innerStep innerTerminal phaseOneTrace 0 phaseTwoTrace 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    (by simpa only [mul_one] using phase_one_execution), phase_one_literal.input,
    (by simpa only [mul_one] using phase_one_stops 0), ?_,
    Or.inr ⟨?_, phase_two_execution, rfl, ?_⟩⟩
  · intro k hk
    omega
  · norm_num [phaseOneTrace, initial_values.2]
  · ext j
    simp [phaseTwoTrace, twoPhasePhaseOneRadii]

/-- The actual source Lagrangian agrees with the scalar-coordinate computation. -/
theorem source_lagrangian_eq (y : EuclideanSpace ℝ (Fin 1)) :
    (fun x => twoPhaseLagrangian objective constraint x y) = lagrangian (y 0) := by
  funext x
  change Chapter07.Section01.lagrangian objective constraint x y = lagrangian (y 0) x
  rw [Chapter07.Section01.lagrangian_eq_sub_inner]
  simp [objective, constraint, scalarConstraint, lagrangian, PiLp.inner_apply, mul_comm]

/-- The source's augmented multiplier norm has the scalar square-root formula. -/
theorem multiplier_scale (y : EuclideanSpace ℝ (Fin 1)) :
    Chapter07.Section01.multiplierScale y = Real.sqrt (1 + (y 0) ^ 2) := by
  rw [Chapter07.Section01.multiplierScale, EuclideanSpace.real_norm_sq_eq]
  simp [add_comm]

/-- Every actual vector multiplier fails the source first-order Taylor-gap bound. -/
theorem source_multiplier_failure (y : EuclideanSpace ℝ (Fin 1)) :
    (1 / 4 : ℝ) * Chapter07.Section01.multiplierScale y <
      gapOn (taylorDecrement (fun x => twoPhaseLagrangian objective constraint x y) 1 0)
        (feasibleDisplacements X (0 : Plane) ∩ closedBall 0 1) := by
  rw [source_lagrangian_eq, multiplier_scale]
  exact fails_every_multiplier (y 0)

/-- Neither of the printed first-order termination alternatives holds. The infeasible
alternative already fails its strict residual inequality; no finite multiplier satisfies
the approximate-solution alternative. -/
theorem termination_alternatives_fail :
    ¬((1 / 2 : ℝ) < ‖constraint (0 : Plane)‖ ∨
      ∃ y : EuclideanSpace ℝ (Fin 1),
        gapOn (taylorDecrement (fun x => twoPhaseLagrangian objective constraint x y) 1 0)
          (feasibleDisplacements X (0 : Plane) ∩ closedBall 0 1) ≤
            (1 / 4 : ℝ) * Chapter07.Section01.multiplierScale y) := by
  rintro (hc | ⟨y, hy⟩)
  · rw [output_values.2] at hc
    exact (lt_irrefl _ hc)
  · exact (not_le_of_gt (source_multiplier_failure y)) hy

end CartisGouldToint.Chapter14.Section03.TwoPhaseBoundary

namespace CartisGouldToint.Chapter14.Section03
open TwoPhaseBoundary

/-- A complete legal first-order TPqp-GC execution refutes Lemma 14.3.5 at the equality
boundary in its third branch. The full source geometric, smoothness and tube-boundedness
hypotheses hold. The returned point has residual exactly `theta * epsilon0`, and every
finite multiplier violates the scaled first-order Lagrangian inequality. -/
theorem literal_two_phase_boundary_counterexample :
    IsClosed X ∧ Convex ℝ X ∧ X.Nonempty ∧
      BoundedLipschitzJetsNearFeasibleSet objective 1 X ∧
      ComponentwiseBoundedLipschitzJetsNearFeasibleSet constraint 1 X ∧
      TwoPhaseTubeObjectiveBounds objective constraint X 1 (-3) 3 ∧
      algorithm_14_3_2 objective constraint X 1 (1 / 2) 1 (1 / 2) (1 / 2)
        (fun _ => 1 / 4) (fun _ => 2) (fun _ => 1) (fun _ => 1)
        (innerStep 0) (innerTerminal 0) innerStep innerTerminal
        phaseOneTrace 0 phaseTwoTrace 1 ∧
      phaseTwoTrace.point 1 = (0 : Plane) ∧
      ‖constraint (0 : Plane)‖ = 1 / 2 ∧
      ¬((1 / 2 : ℝ) < ‖constraint (0 : Plane)‖ ∨
        ∃ y : EuclideanSpace ℝ (Fin 1),
          gapOn (taylorDecrement (fun x => twoPhaseLagrangian objective constraint x y) 1 0)
            (feasibleDisplacements X (0 : Plane) ∩ closedBall 0 1) ≤
              (1 / 4 : ℝ) * Chapter07.Section01.multiplierScale y) :=
  ⟨simple_set_properties.1, simple_set_properties.2.1, simple_set_properties.2.2,
    component_jets.1, component_jets.2, tube_bounds, actual_execution, rfl,
    output_values.2, termination_alternatives_fail⟩

end CartisGouldToint.Chapter14.Section03
