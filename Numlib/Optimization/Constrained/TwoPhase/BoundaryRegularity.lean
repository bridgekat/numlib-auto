import Numlib.Optimization.Constrained.TwoPhase.BoundaryExecution
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Smooth bounded problem data for the literal boundary execution

The feasibility merit and every target merit have constant actual Hessians.
Thus the genuine execution satisfies the source smoothness and Lipschitz
assumptions on the whole ambient open domain, as well as a bounded convex region.
-/

namespace Constrained.TwoPhase.Boundary
open Set Metric TaylorModel

/-- The source feasibility merit for the admissible choice ℓ=p=2. -/
noncomputable def feasibilityMerit (x : E) : ℝ := ‖constraint x‖ ^ 2 / 2

/-- The actual feasibility merit is smooth to every order. -/
theorem feasibility_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n feasibilityMerit :=
  (((coordinates_contDiff n).2.norm_sq ℝ).div_const 2)

/-- The exact derivative of the genuine feasibility merit. -/
theorem feasibility_fderiv (x : E) : fderiv ℝ feasibilityMerit x = x 1 • P 1 := by
  have hc : HasFDerivAt constraint (P 1) x := (P 1).hasFDerivAt
  have hh := ((hc.pow 2).const_smul (1 / 2 : ℝ))
  have he : feasibilityMerit = fun z => (1 / 2 : ℝ) • constraint z ^ 2 := by
    funext z
    simp [feasibilityMerit, Real.norm_eq_abs, smul_eq_mul]
    ring
  change HasFDerivAt (fun z : E => (1 / 2 : ℝ) • constraint z ^ 2) _ x at hh
  rw [he, hh.fderiv]
  ext v
  simp [P, constraint]
  ring

/-- Every actual feasibility Hessian is the same coordinate quadratic form. -/
theorem feasibility_second (x : E) (w : Fin 2 → E) :
    iteratedFDeriv ℝ 2 feasibilityMerit x w = w 0 1 * w 1 1 := by
  have he : fderiv ℝ feasibilityMerit = fun z => z 1 • P 1 :=
    funext feasibility_fderiv
  have hd := ((P 1).hasFDerivAt (x := x)).smul_const (P 1)
  change HasFDerivAt (fun z : E => z 1 • P 1) _ x at hd
  rw [iteratedFDeriv_two_apply, he, hd.fderiv]
  simp [P, smul_eq_mul]

/-- Both genuine p=2 derivative tensors are globally Lipschitz with constant zero. -/
theorem actual_hessian_lipschitz :
    LipschitzWith 0 (iteratedFDeriv ℝ 2 feasibilityMerit) ∧
      ∀ t : ℝ, LipschitzWith 0 (iteratedFDeriv ℝ 2 (targetMerit objective constraint t)) := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : iteratedFDeriv ℝ 2 feasibilityMerit x =
        iteratedFDeriv ℝ 2 feasibilityMerit y := by
      ext w
      rw [feasibility_second, feasibility_second]
    simp [he]
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : iteratedFDeriv ℝ 2 (targetMerit objective constraint t) x =
        iteratedFDeriv ℝ 2 (targetMerit objective constraint t) y := by
      ext w
      rw [merit_second, merit_second]
    simp [he]

/-- The source region is nonempty, closed, convex and bounded. -/
theorem region_properties : region.Nonempty ∧ IsClosed region ∧ Convex ℝ region ∧
    Bornology.IsBounded region := by
  exact ⟨⟨0, by simp [region]⟩, isClosed_closedBall, convex_closedBall 0 2,
    isBounded_closedBall⟩

/-- The original objective is bounded on the whole region, hence on every
near-feasible subset required by the source. -/
theorem objective_bounds {x : E} (hx : x ∈ region) :
    -2 ≤ objective x ∧ objective x ≤ 2 := by
  have hn : ‖x‖ ≤ 2 := by simpa [region] using hx
  have hs : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs]
  change -2 ≤ x 0 ∧ x 0 ≤ 2
  constructor <;> nlinarith [sq_nonneg (x 1), norm_nonneg x]

/-- Phase one returns its initial feasible point immediately with no inner
trial. The selected even-power case satisfies the literal p=ℓ=2 admissibility. -/
theorem initially_feasible :
    (0 : E) ∈ region ∧ ‖constraint (0 : E)‖ ≤ (1 / 2 : ℝ) * (1 / 2) ∧
      (2 : ℝ) > Real.logb 2 2 ∧ (2 : ℝ) > 1 := by
  norm_num [region, constraint, Real.logb_self_eq_one]

/-- Full literal one-call obstruction with all source regularity assumptions:
Phase one is already feasible, Phase two genuinely terminates at its boundary,
and neither infeasible nor scaled Lagrangian optimality can hold. -/
theorem counterexample :
    ((0 : E) ∈ region ∧ ‖constraint (0 : E)‖ ≤ (1 / 2 : ℝ) * (1 / 2) ∧
      (2 : ℝ) > Real.logb 2 2 ∧ (2 : ℝ) > 1) ∧
    region.Nonempty ∧ IsClosed region ∧ Convex ℝ region ∧ Bornology.IsBounded region ∧
    ContDiff ℝ 2 feasibilityMerit ∧ LipschitzWith 0 (iteratedFDeriv ℝ 2 feasibilityMerit) ∧
    (∀ t : ℝ, ContDiff ℝ 2 (targetMerit objective constraint t) ∧
      LipschitzWith 0 (iteratedFDeriv ℝ 2 (targetMerit objective constraint t))) ∧
    (∀ x ∈ region, -2 ≤ objective x ∧ objective x ≤ 2) ∧
    PhaseTwoRun false objective constraint region settings
      (1 / 2) (1 / 10) (1 / 2) outerData 1 ∧
    StopAfter false objective constraint region (1 / 2) (1 / 10) (1 / 2)
      (outerData.target 0) (outerData.point 1) ∧
    ‖constraint (outerData.point 1)‖ = 0 ∧
    ¬∃ y : ℝ, firstCriticality (vectorLagrangian objective constraint y)
      region (outerData.point 1) ≤ (1 / 10 : ℝ) * multiplierNorm y := by
  exact ⟨initially_feasible, region_properties.1, region_properties.2.1, region_properties.2.2.1,
    region_properties.2.2.2, feasibility_contDiff 2, actual_hessian_lipschitz.1,
    fun t => ⟨merit_contDiff t 2, actual_hessian_lipschitz.2 t⟩,
    fun _ hx => objective_bounds hx, literal_run, literal_stop, by
      norm_num [outerData, constraint, endpoint, vec], no_multiplier⟩

end Constrained.TwoPhase.Boundary
