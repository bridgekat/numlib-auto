import Numlib.Optimization.HigherOrderApproximateRegularization
import Numlib.Optimization.HigherOrderDerivativeFamily
import Numlib.Optimization.HigherOrderSharpness
import Numlib.Optimization.TaylorCriticalityFirstOrder

/-!
# Scalar quadratic regularization identities

The shifted unit-curvature quadratic supplies simple exact models for regularization.
All smoothness, derivative bounds, lower bounds and true Taylor gaps are verified directly.
-/

noncomputable section
open scoped Nat NNReal
namespace Optimization.QuadraticRegularization
open RegularizedTaylorModel TaylorCriticality HigherOrderApproximateRegularization

/-- A shifted unit-curvature quadratic. -/
def objective (b x : ℝ) : ℝ := x ^ 2 / 2 - b * x

/-- The derivative of the shifted quadratic. -/
@[simp] theorem deriv_objective (b x : ℝ) : deriv (objective b) x = x - b := by
  have h := (((hasDerivAt_id x).pow 2).div_const 2).sub ((hasDerivAt_id x).const_mul b)
  change HasDerivAt (objective b) _ x at h
  rw [h.deriv]
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

/-- The derivative has global Lipschitz constant one. -/
theorem derivative_lipschitz (b : ℝ) : LipschitzWith 1 (deriv (objective b)) := by
  have he : deriv (objective b) = fun x => x - b := funext (deriv_objective b)
  rw [he]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [show x - b - (y - b) = x - y by ring]

/-- The objective satisfies actual first-order derivative-family regularity. -/
theorem derivativeFamily (b : ℝ) : HigherOrderDerivativeFamily (objective b) 1 (fun _ => 1) := by
  have hf : ContDiff ℝ 1 (objective b) := by unfold objective; fun_prop
  refine ⟨hf, fun _ _ _ => by norm_num, ?_⟩
  intro j hj hjp x y d
  have he : j = 1 := by omega
  subst j
  have hl : LipschitzWith 1 (iteratedFDeriv ℝ 1 (objective b)) :=
    HigherOrderSharpness.iteratedFDeriv_lipschitz
      (by simpa only [iteratedDeriv_one] using derivative_lipschitz b)
  apply (HigherOrderRegularization.DiagonalLipschitz.of_operator hf (by norm_num) ?_).bound x y d
  intro a c
  simpa only [dist_eq_norm, NNReal.coe_one] using hl.dist_le_mul a c

/-- The exact completed-square global lower bound. -/
theorem objective_lower (b x : ℝ) : -(b ^ 2 / 2) ≤ objective b x := by
  dsimp [objective]
  nlinarith [sq_nonneg (x - b)]

/-- The actual first-order regularized model has this explicit quadratic form. -/
theorem model_formula (b x σ t : ℝ) :
    model (objective b) 1 x σ t = objective b x + (x - b) * t + σ * t ^ 2 / 2 := by
  change taylorModel (objective b) 1 x t + σ / ((1 + 1)! : ℝ) * ‖t‖ ^ (1 + 1) = _
  rw [taylorModel_one, fderiv_eq_deriv_mul, deriv_objective]
  norm_num [Real.norm_eq_abs, sq_abs]
  ring

/-- The exact derivative of the actual regularized model. -/
theorem model_deriv (b x σ t : ℝ) : deriv (model (objective b) 1 x σ) t = x - b + σ * t := by
  have he : model (objective b) 1 x σ =
      fun t => objective b x + (x - b) * t + σ * t ^ 2 / 2 := funext (model_formula b x σ)
  rw [he]
  have h := ((hasDerivAt_const t (objective b x)).add
    ((hasDerivAt_id t).const_mul (x - b))).add
    ((((hasDerivAt_id t).pow 2).const_mul σ).div_const 2)
  change HasDerivAt (fun t : ℝ => objective b x + (x - b) * t + σ * t ^ 2 / 2) _ t at h
  rw [h.deriv]
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

/-- The actual first-order Taylor decrement. -/
theorem decrement_formula (b x d : ℝ) : taylorDecrement (objective b) 1 x d = -(x - b) * d := by
  rw [taylorDecrement_one, fderiv_eq_deriv_mul, deriv_objective]
  ring

/-- The exact first-order Taylor gap at every nonnegative radius. -/
theorem gap_formula (b x δ : ℝ) (hδ : 0 ≤ δ) :
    gapOn (taylorDecrement (objective b) 1 x) (Metric.closedBall 0 δ) = δ * |x - b| := by
  rw [gapOn_taylorDecrement_one _ _ hδ, ← norm_deriv_eq_norm_fderiv,
    Real.norm_eq_abs, deriv_objective]

end Optimization.QuadraticRegularization
