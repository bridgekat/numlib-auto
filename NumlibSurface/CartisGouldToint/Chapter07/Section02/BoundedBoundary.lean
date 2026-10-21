import Numlib.Optimization.TwoPhaseBoundedBoundary
import NumlibSurface.CartisGouldToint.Chapter07.Section02.Execution
import Numlib.Analysis.Calculus.EuclideanOneHigherDeriv

/-!
# A bounded one-dimensional instance of the literal boundary defect

The primal space is the actual one-dimensional Euclidean space. There are no equality
constraints, so the multiplier space is zero-dimensional and the returned multiplier is unique.
The simple constraint set is the coordinate interval `[0,1]`.
-/

noncomputable section
namespace CartisGouldToint.Chapter07.Section02.BoundedBoundary
open Optimization TwoPhaseTargets FeasibleCriticality ConstrainedRegularization
open HigherOrderRegularization ParameterUpdates

/-- The identity objective on one-dimensional Euclidean space. -/
def objective (x : EuclideanSpace ℝ (Fin 1)) : ℝ := EuclideanOne.coord x

/-- The zero-dimensional equality residual, with no redundant multiplier coordinates. -/
def constraints (_ : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 0) := 0

/-- The actual closed bounded interval in Euclidean one-space. -/
def constraintSet : Set (EuclideanSpace ℝ (Fin 1)) :=
  EuclideanOne.coord ⁻¹' Set.Icc 0 1

/-- The scalar point expressed in the source's Euclidean primal type. -/
def point (i : ℕ) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanOne.coord.symm (TwoPhaseTargets.BoundedBoundary.point i)

/-- The complete one-trial Euclidean inner history. -/
def history : InnerHistory (EuclideanSpace ℝ (Fin 1)) where
  point := fun i => EuclideanOne.coord.symm (boundaryHistory.point i)
  step := fun i => EuclideanOne.coord.symm (boundaryHistory.step i)
  sigma := boundaryHistory.sigma
  length := boundaryHistory.length

/-- The simple set has all source C.CNe properties. -/
theorem constraint_assumptions : Chapter06.Section01.ConvexConstraintAssumptions constraintSet where
  isClosed := isClosed_Icc.preimage EuclideanOne.coord.continuous
  convex := (convex_Icc (0 : ℝ) 1).linear_preimage EuclideanOne.coord.toLinearMap
  nonempty := ⟨EuclideanOne.coord.symm 1, by simp [constraintSet]⟩

/-- The actual squared residual is the scalar shifted quadratic transported isometrically. -/
theorem target_objective (t : ℝ) : targetObjective objective constraints t =
    EuclideanOne.lift (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) t) := by
  funext x
  simp [targetObjective, TargetLeastSquares.objective, EuclideanOne.lift, objective, constraints]

/-- The actual augmented norm is the absolute coordinate-target gap. -/
theorem target_norm (t : ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    residualNorm objective constraints t x = |EuclideanOne.coord x - t| := by
  simp [residualNorm, constraints, objective, Real.sqrt_sq_eq_abs]

/-- The genuine quadratic target Taylor polynomial transports the scalar quadratic exactly. -/
theorem target_taylor (x s : EuclideanSpace ℝ (Fin 1)) :
    RegularizedTaylorModel.taylorModel (targetObjective objective constraints 0) 2 x s =
      EuclideanOne.coord x ^ 2 / 2 + EuclideanOne.coord x * EuclideanOne.coord s +
        EuclideanOne.coord s ^ 2 / 2 := by
  let φ := TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0
  have hd : Differentiable ℝ φ := by
    dsimp [φ]
    rw [boundary_objective]
    exact (differentiable_id.pow 2).div_const 2
  have hf : fderiv ℝ (EuclideanOne.lift φ) x s = EuclideanOne.coord x * EuclideanOne.coord s := by
    rw [EuclideanOne.fderiv_eq hd]
    simp [φ, boundary_deriv]
  have hh : fderiv ℝ (fderiv ℝ (EuclideanOne.lift φ)) x s s = EuclideanOne.coord s ^ 2 := by
    have h := EuclideanOne.fderiv_fderiv_apply hd
      (x := x) (d₂ := 1) (by dsimp [φ]; rw [boundary_deriv]; exact hasDerivAt_id _)
      s s
    nlinarith [h]
  rw [target_objective]
  change RegularizedTaylorModel.taylorModel (EuclideanOne.lift φ) 2 x s = _
  rw [show RegularizedTaylorModel.taylorModel (EuclideanOne.lift φ) 2 x s =
      RegularizedTaylorModel.taylorModel (EuclideanOne.lift φ) 1 x s +
        (Nat.factorial 2 : ℝ)⁻¹ • iteratedFDeriv ℝ 2 (EuclideanOne.lift φ) x (fun _ => s) from
      RegularizedTaylorModel.taylorModel_succ _ 1 x s]
  simp only [RegularizedTaylorModel.taylorModel_one, iteratedFDeriv_two_apply, hf, hh,
    EuclideanOne.lift_apply]
  dsimp [φ]
  rw [boundary_objective]
  norm_num
  ring

/-- The actual cubic regularized model is the scalar model composed with the coordinate. -/
theorem target_model (x : EuclideanSpace ℝ (Fin 1)) (sigma : ℝ) :
    model (targetObjective objective constraints 0) 2 x sigma =
      EuclideanOne.lift (model
        (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0)
          2 (EuclideanOne.coord x) sigma) := by
  funext s
  rw [EuclideanOne.lift_apply, boundary_model]
  unfold model
  rw [target_taylor]
  have hn : ‖s‖ = |EuclideanOne.coord s| := by
    simpa only [Real.norm_eq_abs] using (EuclideanOne.coord.norm_map s).symm
  rw [hn]
  norm_num [Nat.factorial]

/-- Every actual target family member satisfies source second-derivative smoothness with zero
Lipschitz constant, on an open global extension. -/
theorem target_smooth (t : ℝ) :
    SmoothOn (targetObjective objective constraints t) constraintSet 2 0 where
  degree_pos := by norm_num
  nonneg := le_rfl
  neighborhood := by
    refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩
    rw [target_objective]
    apply (EuclideanOne.contDiff ?_).contDiffOn
    rw [TwoPhaseTargets.BoundedBoundary.target_objective]
    exact ((contDiff_id.sub contDiff_const).pow 2).div_const 2
  lipschitz x _ y _ := by
    have hf : ContDiff ℝ 2
        (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) t) := by
      rw [TwoPhaseTargets.BoundedBoundary.target_objective]
      exact ((contDiff_id.sub contDiff_const).pow 2).div_const 2
    have hL : LipschitzWith 0 (iteratedDeriv 2
        (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) t)) := by
      rw [TwoPhaseTargets.BoundedBoundary.target_iteratedDeriv_two]
      exact LipschitzWith.const 1
    have h := (EuclideanOne.iteratedFDeriv_lipschitz hf hL).dist_le_mul x y
    rw [target_objective]
    simpa [dist_eq_norm] using h

/-- All analytic assumptions of Theorem 7.2.7 hold with beta=1 and objective bounds [0,1]. -/
theorem smoothness_assumptions :
    GeneralConstraintSmoothnessAssumptions objective constraints constraintSet 2 2 1 0 1 where
  constraintSet := constraint_assumptions
  residual := by
    refine ⟨0, ?_⟩
    have he : Chapter05.Section01.residualPowerObjective constraints 2 = fun _ => (0 : ℝ) := by
      funext x
      simp [Chapter05.Section01.residualPowerObjective, residualPowerObjective, constraints]
    rw [he]
    exact smoothOn_const (by norm_num) 0
  targets t := ⟨0, target_smooth t⟩
  bounds x hx := hx.1

/-- The actual target derivative is its coordinate gap times the coordinate functional. -/
theorem target_fderiv (x d : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ (targetObjective objective constraints 0) x d =
      EuclideanOne.coord x * EuclideanOne.coord d := by
  rw [target_objective, EuclideanOne.fderiv_eq]
  · simp [boundary_deriv]
  · rw [boundary_objective]
    exact (differentiable_id.pow 2).div_const 2

/-- The true constrained derivative gap on the coordinate interval is scalar slope times
coordinate distance to its left endpoint. -/
theorem criticality_coord (z : EuclideanSpace ℝ (Fin 1)) (hz : z ∈ constraintSet)
    (a : ℝ) (ha : 0 ≤ a) (A : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)
    (hA : ∀ d, A d = a * EuclideanOne.coord d) :
    feasibleCriticality constraintSet z A = a * EuclideanOne.coord z := by
  apply le_antisymm
  · apply (feasibleCriticality_le_iff constraint_assumptions.isClosed hz A).mpr
    intro d hd
    rw [hA]
    have hl : 0 ≤ EuclideanOne.coord z + EuclideanOne.coord d := by
      simpa only [constraintSet, Set.mem_preimage, Set.mem_Icc, map_add] using hd.1.1
    nlinarith
  · have hd : EuclideanOne.coord.symm (-EuclideanOne.coord z) ∈
        unitFeasibleSteps constraintSet z := by
      refine ⟨?_, ?_⟩
      · simp [constraintSet]
      · rw [EuclideanOne.coord.symm.norm_map]
        simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hz.1] using hz.2
    have hh := neg_apply_le_feasibleCriticality constraint_assumptions.isClosed A hd
    rw [hA] at hh
    simpa using hh

/-- The literal first stop cannot occur at the initial point by its target derivative test. -/
theorem initial_not_stationary :
    ¬TargetStationary objective constraints constraintSet (1 / 4) 0 (point 0) := by
  intro h
  rw [targetStationary_iff, target_norm] at h
  have he := criticality_coord (point 0) (by simp [point, constraintSet,
    TwoPhaseTargets.BoundedBoundary.point]) 1 (by norm_num)
    (fderiv ℝ (targetObjective objective constraints 0) (point 0))
    (by
      intro d
      simpa [point, TwoPhaseTargets.BoundedBoundary.point] using target_fderiv (point 0) d)
  rw [he] at h
  norm_num [point, TwoPhaseTargets.BoundedBoundary.point] at h

/-- The scalar cubic model's true derivative vanishes at the chosen nonzero trial. -/
theorem scalar_model_derivative_zero : HasDerivAt
    (model (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0) 2 1 4)
    0 (-(1 / 2)) := by
  have he : model (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0)
      2 1 4 = fun s : ℝ => (1 : ℝ) / 2 + s + s ^ 2 / 2 + (2 / 3) * |s| ^ 3 := by
    funext s
    rw [boundary_model]
    ring
  rw [he]
  convert (((hasDerivAt_id (-(1 / 2 : ℝ))).const_add (1 / 2)).add
    (((hasDerivAt_id (-(1 / 2 : ℝ))).pow 2).div_const 2)).add
    (((hasDerivAt_abs_neg (by norm_num : -(1 / 2 : ℝ) < 0)).pow 3).const_mul (2 / 3)) using 1
  · funext s; simp
  · norm_num

/-- The actual one-trial inner history has zero model derivative and actual ratio one. -/
theorem inner_run : history.IsRun false boundaryParameters 2 (3 / 4) (1 / 2) 1 (1 / 4)
    objective constraints constraintSet 0 := by
  have hr : ratio (targetObjective objective constraints 0) 2 (history.point 0)
      (history.step 0) = 1 := by
    rw [ratio, ite_eq_right]
    · rw [target_taylor, target_taylor]
      norm_num [history, boundaryHistory, targetObjective, TargetLeastSquares.objective,
        objective, constraints, map_add]
    · intro hz
      have hh := congrArg EuclideanOne.coord hz
      norm_num [history, boundaryHistory] at hh
  have hd : fderiv ℝ (model (targetObjective objective constraints 0) 2
      (history.point 0) (history.sigma 0)) (history.step 0) = 0 := by
    rw [target_model]
    have hh := EuclideanOne.hasFDerivAt (x := history.step 0)
      (by simpa [history, boundaryHistory] using scalar_model_derivative_zero)
    simpa [history, boundaryHistory] using hh.fderiv
  refine {
    initial_lower := by norm_num [history, boundaryHistory, boundaryParameters]
    update := ?_
    decrease := ?_
    iterate := ?_
    initial_feasible := by simp [history, boundaryHistory, constraintSet]
    trial_feasible := ?_
    degree_pos := by norm_num
    modelTheta_mem := by norm_num
    epsilon1_pos := by norm_num
    model_test := ?_
    terminal := Or.inl (by norm_num [history, boundaryHistory, target_norm])
    first := ?_ }
  · intro i hi
    have : i = 0 := by simpa [history, boundaryHistory] using hi
    subst i
    rw [hr]
    norm_num [history, boundaryHistory, boundaryParameters]
  · intro i hi
    have : i = 0 := by simpa [history, boundaryHistory] using hi
    subst i
    rw [target_model]
    norm_num [history, boundaryHistory, EuclideanOne.lift_apply, boundary_model]
    norm_num [boundary_objective]
  · intro i hi
    have : i = 0 := by simpa [history, boundaryHistory] using hi
    subst i
    rw [ite_eq_left (by norm_num [boundaryParameters, hr])]
    apply EuclideanOne.coord.injective
    norm_num [history, boundaryHistory, map_add]
  · intro i hi
    have : i = 0 := by simpa [history, boundaryHistory] using hi
    subst i
    norm_num [history, boundaryHistory, constraintSet, map_add]
  · intro i hi
    have : i = 0 := by simpa [history, boundaryHistory] using hi
    subst i
    rw [hd]
    apply (feasibleCriticality_le_iff constraint_assumptions.isClosed
      (by norm_num [history, boundaryHistory, constraintSet, map_add]) _).mpr
    intro d _
    norm_num
  · intro i hi
    have : i = 0 := by simpa [history, boundaryHistory] using hi
    subst i
    have hh := initial_not_stationary
    change ¬InnerStop false objective constraints constraintSet (1 / 2) 1 (1 / 4) 0 (point 0)
    norm_num [InnerStop, target_norm, objective, point,
      TwoPhaseTargets.BoundedBoundary.point] at *
    exact hh

/-- Phase 2 is a complete actual source-typed literal run with the first outer exit at equality. -/
theorem outer_run : OuterRun false boundaryParameters 2 (3 / 4) (1 / 2) 1 (1 / 4)
    objective constraints constraintSet point (fun _ => 0) (fun _ => history) 1 := by
  refine {
    theta_mem := by norm_num
    epsilon0_pos := by norm_num
    initial_feasible := by simp [point, TwoPhaseTargets.BoundedBoundary.point, constraintSet]
    initial_small := by norm_num [constraints]
    initial_target := by norm_num [point, TwoPhaseTargets.BoundedBoundary.point, resetTarget,
      objective, constraints]
    inner := ?_
    initial_link := ?_
    terminal_link := ?_
    target_update := ?_
    first := by intro k hk; omega
    nonempty := by norm_num
    terminal := Or.inl (by
      norm_num [point, TwoPhaseTargets.BoundedBoundary.point, target_norm, objective]) }
  · intro k hk
    have : k = 0 := by omega
    subst k
    exact inner_run
  · intro k hk
    have : k = 0 := by omega
    subst k
    rfl
  · intro k hk
    have : k = 0 := by omega
    subst k
    rfl
  · intro k hk
    have : k = 0 := by omega
    subst k
    norm_num [nextTarget, point, TwoPhaseTargets.BoundedBoundary.point, target_norm, objective]

/-- Phase 1 stops without any trial because the actual constraint residual is zero. -/
theorem phase_one_run : Chapter06.Section03.algorithm_6_3_1 boundaryParameters 2 (1 / 4)
    (3 / 4) (1 / 2) (1 / 4) constraints 2 constraintSet (fun _ => point 0)
    (fun _ => 0) (fun _ => 4) 0 where
  initial_lower := by norm_num [boundaryParameters]
  update := by intro k hk; omega
  decrease := by intro k hk; omega
  iterate := by intro k hk; omega
  initial_feasible := by simp [point, TwoPhaseTargets.BoundedBoundary.point, constraintSet]
  trial_feasible := by intro k hk; omega
  degree_pos := by norm_num
  theta_mem := by norm_num
  epsilon_pos := by norm_num
  residual := by intro k hk; omega
  exponent_ge_two := le_rfl
  residual_tolerance_pos := by norm_num
  terminal := ⟨by simp [point, TwoPhaseTargets.BoundedBoundary.point, constraintSet],
    Or.inl (by norm_num [constraints])⟩
  first := by intro k hk; omega
  tau_mem := by norm_num
  compatibility := by norm_num

/-- The full literal TPp-GC source execution, including its admissible Phase-1 exponent choice. -/
theorem full_execution : algorithm_7_2_1_literal boundaryParameters 2 (1 / 4) (3 / 4)
    (1 / 2) 2 1 1 (1 / 4) objective constraints constraintSet (fun _ => point 0)
    (fun _ => 0) (fun _ => 4) 0 point (fun _ => 0) (fun _ => history) 1 where
  theta_mem := by norm_num
  tolerance0 := by norm_num
  tolerance1 := by norm_num
  exponent_choice := ⟨2, Or.inl ⟨rfl, by
    norm_num only [Nat.cast_ofNat]
    rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num⟩⟩
  phase_one := by simpa only [mul_one] using phase_one_run
  phase_link := rfl
  phase_two := by simpa [constraints] using outer_run

/-- The actual squared-residual criticality at the returned point is one quarter. -/
theorem terminal_target_criticality :
    feasibleCriticality constraintSet (point 1)
      (fderiv ℝ (targetObjective objective constraints 0) (point 1)) = 1 / 4 := by
  have h := criticality_coord (point 1)
    (by norm_num [point, TwoPhaseTargets.BoundedBoundary.point, constraintSet]) (1 / 2)
    (by norm_num) (fderiv ℝ (targetObjective objective constraints 0) (point 1))
    (by
      intro d
      simpa [point, TwoPhaseTargets.BoundedBoundary.point] using target_fderiv (point 1) d)
  norm_num [point, TwoPhaseTargets.BoundedBoundary.point] at h ⊢
  exact h

/-- With zero equality coordinates, every multiplier is zero and the Lagrangian is the objective. -/
theorem lagrangian_eq_objective (y : EuclideanSpace ℝ (Fin 0)) :
    (fun z => Section01.lagrangian objective constraints z y) = objective := by
  funext z
  simp [Section01.lagrangian_eq_sub_inner, constraints]

/-- The actual Lagrangian feasible derivative gap at the returned point is one half,
for every multiplier in the zero-dimensional multiplier space. -/
theorem terminal_lagrangian_criticality (y : EuclideanSpace ℝ (Fin 0)) :
    Section01.lagrangianCriticality objective constraints constraintSet (point 1) y = 1 / 2 := by
  rw [Section01.lagrangianCriticality_eq_feasibleCriticality, lagrangian_eq_objective]
  have h := criticality_coord (point 1)
    (by norm_num [point, TwoPhaseTargets.BoundedBoundary.point, constraintSet]) 1 (by norm_num)
    (fderiv ℝ objective (point 1)) (by
      intro d
      have hf : HasFDerivAt objective
          EuclideanOne.coord.toContinuousLinearEquiv.toContinuousLinearMap (point 1) := by
        exact EuclideanOne.coord.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
      rw [hf.fderiv]
      simp)
  simpa [point, TwoPhaseTargets.BoundedBoundary.point] using h

/-- The augmented multiplier norm is one because the multiplier space is zero-dimensional. -/
theorem multiplier_scale (y : EuclideanSpace ℝ (Fin 0)) : Section01.multiplierScale y = 1 := by
  have hy : y = 0 := Subsingleton.elim _ _
  simp [hy, Section01.multiplierScale]

/-- Even the existential scaled-KKT conclusion fails, since zero-dimensional multipliers
cannot inflate the multiplier scale. -/
theorem no_scaled_kkt : ¬∃ y, Section01.IsScaledApproximateKKTPoint objective constraints
    constraintSet 1 (1 / 4) (point 1) y := by
  rintro ⟨y, hy⟩
  have h := hy.criticality_le
  rw [terminal_lagrangian_criticality, multiplier_scale] at h
  norm_num at h

/-- The three literal source output alternatives (7.2.14), (7.2.15), (7.2.16) for this
concrete choice ell=2, theta=1/2, epsilon0=1 and epsilon1=1/4. The final alternative is
allowed any multiplier, which is stronger than failure just at the prescribed multiplier. -/
def SourceOutput (x : EuclideanSpace ℝ (Fin 1)) : Prop :=
  (Chapter06.Section01.constrainedCriticality
      (Chapter05.Section01.residualPowerObjective constraints 2) constraintSet x 0 0 0 ≤
      (1 / 4) * ‖constraints x‖ ^ (2 - (1 : ℝ)) ∧ (1 / 2 : ℝ) < ‖constraints x‖) ∨
  (Chapter06.Section01.constrainedCriticality
      (Chapter05.Section01.residualPowerObjective constraints 2) constraintSet x 0 0 0 ≤
      (1 / 4) * ‖constraints x‖ ∧ (1 / 2 : ℝ) < ‖constraints x‖) ∨
  ∃ y, Section01.IsScaledApproximateKKTPoint objective constraints constraintSet 1 (1 / 4) x y

/-- None of the three source output clauses holds at the point actually returned. -/
theorem fails_source_output : ¬SourceOutput (point 1) := by
  simp only [SourceOutput, constraints, norm_zero]
  norm_num
  exact fun y hy => no_scaled_kkt ⟨y, hy⟩

/-- The complete source-typed bounded counterexample combines every analytic assumption,
a genuine full literal execution and failure of all promised output alternatives. It does
not modify the planned status of Theorem 7.2.7. -/
theorem full_counterexample :
    GeneralConstraintSmoothnessAssumptions objective constraints constraintSet 2 2 1 0 1 ∧
    algorithm_7_2_1_literal boundaryParameters 2 (1 / 4) (3 / 4) (1 / 2) 2 1 1 (1 / 4)
      objective constraints constraintSet (fun _ => point 0) (fun _ => 0) (fun _ => 4) 0
      point (fun _ => 0) (fun _ => history) 1 ∧ ¬SourceOutput (point 1) :=
  ⟨smoothness_assumptions, full_execution, fails_source_output⟩

end CartisGouldToint.Chapter07.Section02.BoundedBoundary
