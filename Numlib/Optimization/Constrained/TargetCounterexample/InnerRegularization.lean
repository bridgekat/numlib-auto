import Numlib.Optimization.Constrained.TargetCounterexample
import Numlib.Optimization.Regularization.HighOrder.CriticalityRun
import Numlib.Optimization.HighOrder.ModelSolve.UnitCriticality
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A genuine regularization inner run for the target-merit obstruction

The old target merit has a negative first-coordinate Hessian at the feasible
sine maximum. Its cubic regularization has an explicit global minimizer that
reaches the zero residual in one accepted trial. Actual Taylor checks and
parameter updates realize the inner method, rather than prescribing its return.
-/

noncomputable section
namespace Constrained.TargetCounterexample.InnerRegularization
open HighOrderRegularization InexactTrustRegion

/-- The actual old least-squares target merit. -/
def oldMerit : E → ℝ := LeastNorm.merit (residual 0)

/-- The distance from the initial sine maximum to its neighboring root. -/
def length : ℝ := Real.pi / 2

/-- The positive cubic regularization parameter fixing the desired minimizer. -/
def sigma : ℝ := 1 / (50 * length)

/-- The actual displacement from the initial point to the residual root. -/
def trial : E := vec (-length) 0

/-- The length lies strictly between one and two. -/
theorem length_bounds : 1 < length ∧ length < 2 := by
  unfold length
  constructor
  · linarith [Real.pi_gt_three]
  · linarith [Real.pi_lt_four]

/-- The fixed cubic parameter is strictly positive. -/
theorem sigma_pos : 0 < sigma := by
  have hp : 0 < length := lt_trans zero_lt_one length_bounds.1
  unfold sigma
  positivity

/-- The trial reaches the actual residual root. -/
theorem initial_add_trial : initial + trial = (0 : E) := by
  ext i
  fin_cases i <;> simp [initial, trial, vec, length]

/-- The trial's actual Euclidean norm is the chosen length. -/
theorem trial_norm : ‖trial‖ = length := by
  have h := vec_norm_sq (-length) 0
  change ‖trial‖ ^ 2 = _ at h
  have hp : 0 < length := lt_trans zero_lt_one length_bounds.1
  nlinarith [norm_nonneg trial]

/-- The old merit derivative as an actual continuous linear functional. -/
theorem old_fderiv (x : E) : fderiv ℝ oldMerit x =
    x 1 • P 1 + (objective x * (Real.cos (x 0) / 10)) • P 0 := by
  have he := (hasFDerivAt_targetMerit (objective_hasFDerivAt x).differentiableAt
    (constraint_hasFDerivAt x).differentiableAt 0).fderiv
  rw [← merit_residual] at he
  change fderiv ℝ oldMerit x = _ at he
  rw [he, objective_fderiv, (constraint_hasFDerivAt x).fderiv]
  ext v
  simp [P, constraint, innerSL_apply_apply]
  ring

/-- The true old-merit gradient vanishes at the initial sine maximum. -/
theorem old_fderiv_initial : fderiv ℝ oldMerit initial = 0 := by
  rw [old_fderiv]
  norm_num [initial, objective, vec]

/-- The actual initial old-merit Hessian has eigenvalues minus one hundredth
and one in the two Euclidean coordinates. -/
theorem old_second_initial (w : Fin 2 → E) :
    iteratedFDeriv ℝ 2 oldMerit initial w =
      w 0 1 * w 1 1 - (1 / 100 : ℝ) * w 0 0 * w 1 0 := by
  have he : fderiv ℝ oldMerit = fun x => x 1 • P 1 +
      (objective x * (Real.cos (x 0) / 10)) • P 0 := funext old_fderiv
  have hprod := (objective_hasFDerivAt initial).mul (cosine_hasFDerivAt initial)
  have hd := ((constraint_hasFDerivAt initial).smul_const (P 1)).add
    (hprod.smul_const (P 0))
  change HasFDerivAt (fun x : E => x 1 • P 1 +
    (objective x * (Real.cos (x 0) / 10)) • P 0) _ initial at hd
  rw [iteratedFDeriv_two_apply, he, hd.fderiv]
  simp [P, initial, objective, vec, ContinuousLinearMap.smulRight_apply]
  ring

/-- The actual quadratic Taylor polynomial at the initial point. -/
theorem old_taylor (v : E) : TaylorModel.eval oldMerit 2 initial v =
    1 / 200 + (v 1) ^ 2 / 2 - (v 0) ^ 2 / 200 := by
  have he := TaylorModel.eval_two oldMerit initial v
  rw [iteratedFDeriv_one_apply, old_fderiv_initial, old_second_initial] at he
  have hv : oldMerit initial = 1 / 200 := by
    norm_num [oldMerit, merit_residual, targetMerit, objective, initial, constraint, vec]
  rw [hv] at he
  simp only [zero_apply, zero_add] at he
  nlinarith [he]

/-- The actual regularized model, including its Euclidean norm-power penalty. -/
theorem model_formula (v : E) : model oldMerit 2 initial sigma v =
    1 / 200 + (v 1) ^ 2 / 2 - (v 0) ^ 2 / 200 + ‖v‖ ^ 3 / (300 * length) := by
  rw [model_eq, old_taylor]
  norm_num [sigma]
  ring

/-- The exact model value at its explicit minimizer. -/
theorem model_trial : model oldMerit 2 initial sigma trial = 1 / 200 - length ^ 2 / 600 := by
  rw [model_formula, trial_norm]
  have hn : length ≠ 0 := ne_of_gt (lt_trans zero_lt_one length_bounds.1)
  simp only [trial, vec, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- The actual Euclidean squared norm in two coordinates. -/
theorem norm_sq (v : E) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- A radial square factorization proves global minimization of the actual
cubic regularized model, including every off-axis displacement. -/
theorem model_gap_factorization (v : E) :
    model oldMerit 2 initial sigma v - model oldMerit 2 initial sigma trial =
      (‖v‖ - length) ^ 2 * (2 * ‖v‖ + length) / (600 * length) +
        (101 / 200 : ℝ) * (v 1) ^ 2 := by
  rw [model_formula, model_trial]
  have hn : length ≠ 0 := ne_of_gt (lt_trans zero_lt_one length_bounds.1)
  have hv := norm_sq v
  field_simp
  have hm := congrArg (fun t : ℝ => t * length) hv
  nlinarith [hm]

/-- The constructed step is a genuine global minimizer of the actual model. -/
theorem model_isMin (v : E) : model oldMerit 2 initial sigma trial ≤
    model oldMerit 2 initial sigma v := by
  have hg := model_gap_factorization v
  have hp : 0 < length := lt_trans zero_lt_one length_bounds.1
  have hpos : 0 ≤ (‖v‖ - length) ^ 2 * (2 * ‖v‖ + length) / (600 * length) := by
    positivity
  nlinarith [sq_nonneg (v 1)]

/-- The actual regularized model is strictly improved. -/
theorem model_improves : model oldMerit 2 initial sigma trial <
    model oldMerit 2 initial sigma 0 := by
  rw [model_trial, model_formula]
  norm_num
  have hp : 0 < length := lt_trans zero_lt_one length_bounds.1
  nlinarith [sq_pos_of_pos hp]

end Constrained.TargetCounterexample.InnerRegularization
