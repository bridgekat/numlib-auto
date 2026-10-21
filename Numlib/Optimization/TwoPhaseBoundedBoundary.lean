import Numlib.Optimization.TwoPhaseBoundaryCounterexample
import Numlib.Optimization.ConstrainedResidualRegularization

/-!
# The target-boundary defect on a bounded interval

A genuine literal target-method run on the closed convex interval `[0,1]` returns one half.
The identity objective is bounded on the entire constraint set. Both residual objectives
have globally smooth extensions with constant second derivatives. The source-prescribed
multiplier is zero; no claim is made about arbitrary multipliers for redundant constraints.
-/

noncomputable section
namespace Optimization.TwoPhaseTargets.BoundedBoundary
open FeasibleCriticality ConstrainedRegularization HigherOrderRegularization ParameterUpdates

/-- The closed convex interval constraining the scalar primal variable. -/
def constraintSet : Set ℝ := Set.Icc 0 1

/-- Closedness of the actual bounded constraint set. -/
theorem constraintSet_closed : IsClosed constraintSet := isClosed_Icc

/-- Convexity of the actual bounded constraint set. -/
theorem constraintSet_convex : Convex ℝ constraintSet := convex_Icc _ _

/-- The constraint set is nonempty and contains the initial point. -/
theorem initial_mem : (1 : ℝ) ∈ constraintSet := by norm_num [constraintSet]

/-- The exact initial-to-terminal point sequence. -/
def point (i : ℕ) : ℝ := if i = 0 then 1 else 1 / 2

/-- The target remains zero through the one literal final-branch iteration. -/
def target (_ : ℕ) : ℝ := 0

/-- Every target objective is the shifted scalar quadratic. -/
theorem target_objective (t : ℝ) :
    TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) t =
      fun x => (x - t) ^ 2 / 2 := by
  funext x
  simp [TargetLeastSquares.objective]

/-- The true target objective has scalar derivative `x-t` at every point. -/
theorem target_deriv (t : ℝ) :
    deriv (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) t) =
      fun x => x - t := by
  funext x
  have hd : HasDerivAt (fun z : ℝ => (z - t) ^ 2 / 2) (x - t) x := by
    convert (((hasDerivAt_id x).sub_const t).pow 2).div_const 2 using 1
    · funext z; simp
    · simp
  rw [target_objective]
  exact hd.deriv

/-- The actual second scalar derivative of every target objective is the constant one. -/
theorem target_iteratedDeriv_two (t : ℝ) :
    iteratedDeriv 2 (TargetLeastSquares.objective (fun x : ℝ => x)
      (fun _ => (0 : ℝ)) t) = fun _ => (1 : ℝ) := by
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, target_deriv]
  funext x
  exact ((hasDerivAt_id x).sub_const t).deriv

/-- Every target objective satisfies the actual second-derivative Lipschitz assumption
with constant zero on the whole interval, through a global smooth extension. -/
theorem target_smooth (t : ℝ) :
    SmoothOn (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) t)
      constraintSet 2 0 where
  degree_pos := by norm_num
  nonneg := le_rfl
  neighborhood := by
    refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩
    have h : ContDiff ℝ 2 (fun x : ℝ => (x - t) ^ 2 / 2) :=
      ((contDiff_id.sub contDiff_const).pow 2).div_const 2
    rw [target_objective]
    exact h.contDiffOn
  lipschitz x _ y _ := by
    have he : iteratedFDeriv ℝ 2
        (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) t) x =
        iteratedFDeriv ℝ 2
        (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) t) y := by
      simp [iteratedFDeriv_eq_equiv_comp, target_iteratedDeriv_two]
    simp [he]

/-- The Phase-1 residual-power objective is identically zero. -/
theorem residual_objective_zero : residualPowerObjective (fun _ : ℝ => (0 : ℝ)) 2 =
    fun _ => 0 := by
  funext x
  simp [residualPowerObjective]

/-- The actual Phase-1 smoothness assumption holds with Lipschitz constant zero. -/
theorem residual_smooth : SmoothOn
    (residualPowerObjective (fun _ : ℝ => (0 : ℝ)) 2) constraintSet 2 0 := by
  rw [residual_objective_zero]
  exact smoothOn_const (by norm_num) 0

/-- The identity objective satisfies the source bounds on the entire simple constraint set,
and hence on every near-feasible subset. -/
theorem objective_bounds (x : ℝ) (hx : x ∈ constraintSet) : 0 ≤ x ∧ x ≤ 1 := hx

/-- Restricting feasible steps to the interval can only decrease the true derivative gap. -/
theorem criticality_le_univ (x : ℝ) (hx : x ∈ constraintSet) (A : ℝ →L[ℝ] ℝ) :
    feasibleCriticality constraintSet x A ≤ feasibleCriticality Set.univ x A := by
  apply (feasibleCriticality_le_iff constraintSet_closed hx A).mpr
  intro d hd
  exact neg_apply_le_feasibleCriticality isClosed_univ A ⟨Set.mem_univ _, hd.2⟩

/-- The interval derivative gap at an interior point is exactly the scalar slope times
the distance to the left endpoint, for a nonnegative scalar slope. -/
theorem criticality_scalar (z a : ℝ) (hz : z ∈ constraintSet) (ha : 0 ≤ a)
    (A : ℝ →L[ℝ] ℝ) (hA : ∀ d, A d = a * d) :
    feasibleCriticality constraintSet z A = a * z := by
  apply le_antisymm
  · apply (feasibleCriticality_le_iff constraintSet_closed hz A).mpr
    intro d hd
    rw [hA]
    have hleft : 0 ≤ z + d := hd.1.1
    nlinarith
  · have hd : -z ∈ unitFeasibleSteps constraintSet z := by
      refine ⟨?_, ?_⟩
      · norm_num [constraintSet]
      · simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hz.1] using hz.2
    have hh := neg_apply_le_feasibleCriticality constraintSet_closed A hd
    rw [hA] at hh
    nlinarith

/-- The actual target criticality at the returned point is one quarter. -/
theorem terminal_target_criticality :
    feasibleCriticality constraintSet (1 / 2)
      (fderiv ℝ (TargetLeastSquares.objective (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0)
        (1 / 2)) = 1 / 4 := by
  convert criticality_scalar (1 / 2) (1 / 2) (by norm_num [constraintSet])
    (by norm_num) _ (boundary_fderiv (1 / 2)) using 1
  norm_num

/-- The literal target derivative test fails at the initial and final interval iterates. -/
theorem not_stationary_initial_terminal (z : ℝ) (hz : z = 1 ∨ z = 1 / 2) :
    ¬TargetStationary (fun x : ℝ => x) (fun _ => (0 : ℝ)) constraintSet (1 / 4) 0 z := by
  intro h
  rw [targetStationary_iff] at h
  have hh := criticality_scalar z z (by rcases hz with rfl | rfl <;> norm_num [constraintSet])
    (by rcases hz with rfl | rfl <;> norm_num) _ (boundary_fderiv z)
  rw [hh, boundary_residual] at h
  rcases hz with rfl | rfl <;> norm_num at h

/-- The existing genuine one-trial history remains legal after restricting to the interval. -/
theorem inner_run :
    boundaryHistory.IsRun false boundaryParameters 2 (3 / 4) (1 / 2) 1 (1 / 4)
      (fun x : ℝ => x) (fun _ => (0 : ℝ)) constraintSet 0 := by
  have h := boundary_inner_run
  refine { h with
    initial_feasible := initial_mem
    trial_feasible := ?_
    model_test := ?_
    terminal := Or.inl (by norm_num [boundaryHistory, boundary_residual])
    first := ?_ }
  · intro i hi
    have : i = 0 := by simpa [boundaryHistory] using hi
    subst i
    norm_num [boundaryHistory, constraintSet]
  · intro i hi
    have hx : boundaryHistory.point i + boundaryHistory.step i ∈ constraintSet := by
      have : i = 0 := by simpa [boundaryHistory] using hi
      subst i
      norm_num [boundaryHistory, constraintSet]
    exact (criticality_le_univ _ hx _).trans (h.model_test i hi)
  · intro i hi
    have : i = 0 := by simpa [boundaryHistory] using hi
    subst i
    simp only [InnerStop, boundaryHistory, ite_true, Bool.false_eq]
    have hn := not_stationary_initial_terminal 1 (Or.inl rfl)
    norm_num [boundary_residual] at *
    exact hn

/-- A complete actual literal Phase-2 run on the bounded interval exits at the weak boundary. -/
theorem outer_run :
    OuterRun false boundaryParameters 2 (3 / 4) (1 / 2) 1 (1 / 4)
      (fun x : ℝ => x) (fun _ => (0 : ℝ)) constraintSet point target
      (fun _ => boundaryHistory) 1 := by
  refine {
    theta_mem := by norm_num
    epsilon0_pos := by norm_num
    initial_feasible := initial_mem
    initial_small := by norm_num
    initial_target := by norm_num [point, target, resetTarget]
    inner := ?_
    initial_link := ?_
    terminal_link := ?_
    target_update := ?_
    first := ?_
    nonempty := by norm_num
    terminal := ?_ }
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
    norm_num [nextTarget, boundary_residual, point, target]
  · intro k hk
    omega
  · apply Or.inl
    norm_num [point, target, boundary_residual]

/-- Phase 1 is a genuine zero-trial residual-minimization run ending at the feasible point one. -/
theorem phase_one_run : ConstrainedResidualRegularization.IsRun boundaryParameters 2
    (3 / 4) (1 / 2) (1 / 4) (fun _ : ℝ => (0 : ℝ)) 2 constraintSet
    (fun _ => 1) (fun _ => 0) (fun _ => 4) 0 where
  initial_lower := by norm_num [boundaryParameters]
  update := by intro k hk; omega
  decrease := by intro k hk; omega
  iterate := by intro k hk; omega
  initial_feasible := initial_mem
  trial_feasible := by intro k hk; omega
  degree_pos := by norm_num
  theta_mem := by norm_num
  epsilon_pos := by norm_num
  residual := by intro k hk; omega
  exponent_ge_two := le_rfl
  residual_tolerance_pos := by norm_num
  terminal := ⟨initial_mem, Or.inl (by norm_num)⟩
  first := by intro k hk; omega

/-- The actual Lagrangian at the source-prescribed multiplier zero is the identity. -/
theorem lagrangian_zero :
    lagrangian (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0 = fun x => x := by
  funext x
  simp [lagrangian]

/-- The prescribed multiplier vanishes, so its appended Euclidean scale is one. -/
theorem returned_multiplier :
    targetMultiplier (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0 (1 / 2) = 0 ∧
    multiplierScale (targetMultiplier (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0 (1 / 2)) = 1 := by
  norm_num [targetMultiplier, multiplierScale]

/-- At the source-prescribed multiplier, actual Lagrangian criticality is one half. -/
theorem terminal_lagrangian_criticality :
    feasibleCriticality constraintSet (1 / 2)
      (fderiv ℝ (lagrangian (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0) (1 / 2)) = 1 / 2 := by
  rw [lagrangian_zero]
  convert criticality_scalar (1 / 2) 1 (by norm_num [constraintSet]) (by norm_num)
    (fderiv ℝ (fun x : ℝ => x) (1 / 2)) (fun d => by simp) using 1
  norm_num

/-- None of the three source output alternatives holds: both infeasibility branches require
a strictly positive constraint residual, and the prescribed scaled KKT test fails. -/
theorem fails_source_output :
    ¬((1 / 2 : ℝ) < ‖(0 : ℝ)‖ ∨ (1 / 2 : ℝ) < ‖(0 : ℝ)‖ ∨
      feasibleCriticality constraintSet (1 / 2)
        (fderiv ℝ (lagrangian (fun x : ℝ => x) (fun _ => (0 : ℝ))
          (targetMultiplier (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0 (1 / 2))) (1 / 2)) ≤
        (1 / 4) * multiplierScale
          (targetMultiplier (fun x : ℝ => x) (fun _ => (0 : ℝ)) 0 (1 / 2))) := by
  rw [returned_multiplier.1, terminal_lagrangian_criticality]
  norm_num [multiplierScale]

end Optimization.TwoPhaseTargets.BoundedBoundary
