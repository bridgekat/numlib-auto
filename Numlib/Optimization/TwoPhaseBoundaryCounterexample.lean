import Numlib.Optimization.TwoPhaseExecution
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# A literal weak-boundary execution without a stationarity certificate

The objective is the identity on the real line and the constraint residual vanishes. One
legal first-order fixed-tolerance Taylor step for the squared target residual reaches the
inner boundary exactly. The literal final branch exits even though its derivative test fails.
-/

noncomputable section
namespace Optimization.TwoPhaseTargets
open FeasibleCriticality ConstrainedRegularization HigherOrderRegularization ParameterUpdates

/-- Concrete regularization constants for the weak-boundary execution. -/
def boundaryParameters : RegularizationParameters where
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num

/-- The true squared target residual in the counterexample is a quadratic. -/
theorem boundary_objective :
    TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0 =
      fun x => x ^ 2 / 2 := by
  funext x
  simp [TargetLeastSquares.objective]

/-- Its actual derivative applied to a direction is multiplication by the current point. -/
theorem boundary_fderiv (x d : ℝ) :
    fderiv ℝ (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0) x d =
      x * d := by
  rw [boundary_objective, fderiv_eq_deriv_mul]
  have hd : HasDerivAt (fun z : ℝ => z ^ 2 / 2) x x := by
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1
    · funext z; simp
    · simp
  rw [hd.deriv]

/-- The derivative function of the counterexample objective is the identity. -/
theorem boundary_deriv :
    deriv (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0) = id := by
  funext x
  simpa only [fderiv_eq_deriv_mul, mul_one, id_eq] using boundary_fderiv x 1

/-- The true degree-two Taylor polynomial agrees with the quadratic objective. -/
theorem boundary_taylor (x s : ℝ) :
    RegularizedTaylorModel.taylorModel
      (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0) 2 x s =
      x ^ 2 / 2 + x * s + s ^ 2 / 2 := by
  rw [RegularizedTaylorModel.taylorModel_real]
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero,
    iteratedDeriv_zero, iteratedDeriv_succ, boundary_deriv, deriv_id,
    zero_add, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two,
    Nat.cast_one, Nat.cast_ofNat, div_one, pow_one, smul_eq_mul]
  rw [boundary_objective]
  simp only [id_eq]
  ring

/-- The actual degree-two regularized model contains its genuine cubic radial term. -/
theorem boundary_model (x sigma s : ℝ) :
    model (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0)
      2 x sigma s = x ^ 2 / 2 + x * s + s ^ 2 / 2 + sigma / 6 * |s| ^ 3 := by
  norm_num [model, boundary_taylor, Real.norm_eq_abs, Nat.factorial]

/-- The legal step from one to one half has actual acceptance ratio one. -/
theorem boundary_ratio :
    ratio (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0)
      2 1 (-(1 / 2)) = 1 := by
  rw [ratio, ite_eq_right (by norm_num : -(1 / 2 : ℝ) ≠ 0), boundary_taylor,
    boundary_taylor]
  norm_num [boundary_objective]

/-- The actual augmented residual is the absolute primal coordinate. -/
theorem boundary_residual (z : ℝ) :
    residualNorm (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0 z = |z| := by
  simp [residualNorm, Real.sqrt_sq_eq_abs]

/-- The full inner history contains one nonzero trial and both of its endpoints. -/
def boundaryHistory : InnerHistory ℝ where
  point := fun i => if i = 0 then 1 else 1 / 2
  step := fun _ => -(1 / 2)
  sigma := fun _ => 4
  length := 1

/-- The actual target derivative test fails both before and after the boundary step. -/
theorem boundary_not_stationary (z : ℝ) (hz : 0 < z) :
    ¬TargetStationary (fun x : ℝ => x) (fun _ => (0 : ℝ)) Set.univ (1 / 4) 0 z := by
  intro h
  have hd : (-1 : ℝ) ∈ unitFeasibleSteps Set.univ z := by
    simp [unitFeasibleSteps]
  have hl := neg_apply_le_feasibleCriticality isClosed_univ
    (fderiv ℝ (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0) z) hd
  rw [boundary_fderiv] at hl
  have hr : residualNorm (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0 z = z := by
    simp [residualNorm, Real.sqrt_sq hz.le]
  unfold TargetStationary at h
  rw [hr] at h
  linarith

/-- One genuine fixed-tolerance ARp trial stops at the literal equality boundary. -/
theorem boundary_inner_run :
    boundaryHistory.IsRun false boundaryParameters 2 (3 / 4) (1 / 2) 1 (1 / 4)
      (fun x : ℝ => x) (fun _ => (0 : ℝ)) Set.univ 0 := by
  have hmodel : model (TargetLeastSquares.objective (fun x : ℝ => x)
      (fun _ => (0 : ℝ)) 0) 2 1 4 =
      fun s : ℝ => (1 : ℝ) / 2 + s + s ^ 2 / 2 + (2 / 3) * |s| ^ 3 := by
    funext s
    rw [boundary_model]
    ring
  have hd : fderiv ℝ
      (fun s : ℝ => (1 : ℝ) / 2 + s + s ^ 2 / 2 + (2 / 3) * |s| ^ 3)
      (-(1 / 2)) = 0 := by
    have hh : HasDerivAt
        (fun s : ℝ => (1 : ℝ) / 2 + s + s ^ 2 / 2 + (2 / 3) * |s| ^ 3)
        0 (-(1 / 2)) := by
      convert (((hasDerivAt_id (-(1 / 2 : ℝ))).const_add (1 / 2)).add
        (((hasDerivAt_id (-(1 / 2 : ℝ))).pow 2).div_const 2)).add
        (((hasDerivAt_abs_neg (by norm_num : -(1 / 2 : ℝ) < 0)).pow 3).const_mul (2 / 3))
        using 1
      · funext s; simp
      · norm_num
    simpa using hh.hasFDerivAt.fderiv
  refine { initial_lower := by norm_num [boundaryParameters, boundaryHistory]
           update := ?_, decrease := ?_, iterate := ?_, initial_feasible := Set.mem_univ _,
           trial_feasible := fun _ _ => Set.mem_univ _, degree_pos := by norm_num,
           modelTheta_mem := by norm_num, epsilon1_pos := by norm_num,
           model_test := ?_, terminal := ?_, first := ?_ }
  · intro i hi
    have : i = 0 := by simpa [boundaryHistory] using hi
    subst i
    norm_num [boundaryHistory, boundaryParameters, boundary_ratio]
  · intro i hi
    have : i = 0 := by simpa [boundaryHistory] using hi
    subst i
    change model (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0)
      2 1 4 (-(1 / 2)) < model
        (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0) 2 1 4 0
    rw [boundary_model, boundary_model]
    norm_num
  · intro i hi
    have : i = 0 := by simpa [boundaryHistory] using hi
    subst i
    norm_num [boundaryHistory, boundaryParameters, boundary_ratio]
  · intro i hi
    have : i = 0 := by simpa [boundaryHistory] using hi
    subst i
    change feasibleCriticality Set.univ ((1 : ℝ) + -(1 / 2))
      (fderiv ℝ (model (TargetLeastSquares.objective (fun x : ℝ => x)
        (fun _ => (0 : ℝ)) 0) 2 1 4) (-(1 / 2))) ≤ (3 / 4) * (1 / 4)
    rw [hmodel, hd]
    apply (feasibleCriticality_le_iff isClosed_univ (Set.mem_univ _) _).mpr
    intro d _
    norm_num
  · apply Or.inl
    norm_num [boundaryHistory, boundary_residual]
  · intro i hi
    have : i = 0 := by simpa [boundaryHistory] using hi
    subst i
    simp only [InnerStop, boundaryHistory, ite_true, Bool.false_eq]
    have hn := boundary_not_stationary 1 (by norm_num)
    norm_num [boundary_residual] at *
    exact hn

/-- The literal target method has a complete legal run reaching the equality boundary
and exiting its final branch without the asserted squared-residual criticality certificate. -/
theorem literal_boundary_counterexample :
    let x : ℕ → ℝ := fun i => if i = 0 then 1 else 1 / 2
    let t : ℕ → ℝ := fun _ => 0
    OuterRun false boundaryParameters 2 (3 / 4) (1 / 2) 1 (1 / 4)
      (fun x : ℝ => x) (fun _ => (0 : ℝ)) Set.univ x t (fun _ => boundaryHistory) 1 ∧
    ¬TargetStationary (fun x : ℝ => x) (fun _ => (0 : ℝ)) Set.univ (1 / 4) (t 1) (x 1) := by
  dsimp only
  constructor
  · refine { theta_mem := by norm_num, epsilon0_pos := by norm_num,
             initial_feasible := Set.mem_univ _, initial_small := by norm_num,
             initial_target := by norm_num [resetTarget], inner := ?_, initial_link := ?_,
             terminal_link := ?_, target_update := ?_, first := ?_,
             nonempty := by norm_num, terminal := ?_ }
    · intro k hk
      have : k = 0 := by omega
      subst k
      exact boundary_inner_run
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
      norm_num [nextTarget, boundary_residual]
    · intro k hk
      omega
    · apply Or.inl
      norm_num [boundary_residual]
  · exact boundary_not_stationary (1 / 2) (by norm_num)

end Optimization.TwoPhaseTargets
