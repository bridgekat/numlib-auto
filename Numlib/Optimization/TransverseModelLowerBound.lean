import Numlib.Optimization.TransverseCubicModel

/-!
# Quantitative bounds for quadratic-radial cubic models

The model's derivative norm is the Euclidean norm of its two scalar stationarity components.
Nonnegative curvature and a unit slope bound give a uniform global model lower bound.
That lower bound supplies the genuine minimizing-fraction inequality for prescribed steps.
-/

noncomputable section
namespace Optimization.TransverseModelLowerBound
open TransverseObjective TransverseCubicModel
open scoped InnerProductSpace

/-- The model derivative is the dual of its actual two-coordinate gradient. -/
theorem fderiv_model_eq_innerSL (a g H : ℝ) (s : Plane) :
    fderiv ℝ (model a g H) s = innerSL ℝ
      (point (a + s 0 + ‖s‖ * s 0) (-g + H * s 1 + ‖s‖ * s 1)) := by
  ext d
  rw [fderiv_model_apply]
  simp only [innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_two, point_zero_coord, point_one_coord, star_trivial]
  ring

/-- The operator norm of the model derivative equals the norm of its scalar components. -/
theorem norm_fderiv_model (a g H : ℝ) (s : Plane) :
    ‖fderiv ℝ (model a g H) s‖ =
      ‖point (a + s 0 + ‖s‖ * s 0) (-g + H * s 1 + ‖s‖ * s 1)‖ := by
  rw [fderiv_model_eq_innerSL, innerSL_apply_norm]

/-- The actual cubic Taylor-model derivative is the derivative of its explicit model. -/
theorem fderiv_actual_model {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) (s : Plane) :
    fderiv ℝ (HigherOrderRegularization.model objective 2 (point a b) 2) s =
      fderiv ℝ (model a (-InverseSqrtTail.first b) (InverseSqrtTail.second b)) s := by
  have he : HigherOrderRegularization.model objective 2 (point a b) 2 = fun d =>
      objective (point a b) + model a (-InverseSqrtTail.first b) (InverseSqrtTail.second b) d :=
    funext (actual_model_eq ha b)
  rw [he]
  exact fderiv_const_add _

/-- The actual cubic Taylor-model derivative norm has its genuine scalar coordinates. -/
theorem norm_fderiv_actual_model {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) (s : Plane) :
    ‖fderiv ℝ (HigherOrderRegularization.model objective 2 (point a b) 2) s‖ =
      ‖point (a + s 0 + ‖s‖ * s 0)
        (InverseSqrtTail.first b + InverseSqrtTail.second b * s 1 + ‖s‖ * s 1)‖ := by
  rw [fderiv_actual_model ha, norm_fderiv_model, neg_neg]

/-- Dropping nonnegative quadratic curvature bounds the model by its radial cubic minus
its linear slope norm times displacement norm. -/
theorem model_ge_linear_radial {a g H : ℝ} (hH : 0 ≤ H) (s : Plane) :
    -‖point a (-g)‖ * ‖s‖ + ‖s‖ ^ 3 / 3 ≤ model a g H s := by
  have hi := (abs_le.mp (abs_real_inner_le_norm (point a (-g)) s)).1
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    point_zero_coord, point_one_coord, star_trivial] at hi
  have hq := mul_nonneg hH (sq_nonneg (s 1))
  unfold model
  nlinarith [sq_nonneg (s 0)]

/-- A cubic with unit negative radial slope is globally bounded below by minus two thirds. -/
theorem radial_cubic_lower_bound {r : ℝ} (hr : 0 ≤ r) :
    -(2 / 3 : ℝ) ≤ -r + r ^ 3 / 3 := by
  nlinarith [mul_nonneg (sq_nonneg (r - 1)) (show 0 ≤ r + 2 by linarith)]

/-- The complete model is bounded below uniformly when its initial slope norm is at most one. -/
theorem model_ge_neg_two_thirds {a g H : ℝ} (hH : 0 ≤ H)
    (hv : ‖point a (-g)‖ ≤ 1) (s : Plane) : -(2 / 3 : ℝ) ≤ model a g H s := by
  have h := model_ge_linear_radial (a := a) (g := g) hH s
  have hr := radial_cubic_lower_bound (norm_nonneg s)
  have hm := mul_le_mul_of_nonneg_right hv (norm_nonneg s)
  linarith

/-- The same lower bound holds relative to the actual objective's Taylor-model constant. -/
theorem actual_model_ge {a : ℝ} (ha : |a| ≤ 1) (b : ℝ)
    (hv : ‖fderiv ℝ objective (point a b)‖ ≤ 1) (s : Plane) :
    objective (point a b) - 2 / 3 ≤
      HigherOrderRegularization.model objective 2 (point a b) 2 s := by
  have hg : ‖point a (-(-InverseSqrtTail.first b))‖ ≤ 1 := by
    simpa only [neg_neg, norm_fderiv_objective_local ha] using hv
  have h := model_ge_neg_two_thirds (InverseSqrtTail.second_nonneg b) hg s
  rw [actual_model_eq ha]
  linarith

/-- A prescribed decrease of at least one third of the squared tolerance satisfies the
squared-slope minimizing fraction against every comparison point, hence every global minimum. -/
theorem squaredSlope_fraction {a g H ε : ℝ} (hH : 0 ≤ H) (hε : ε ≤ 1)
    (hv : ‖point a (-g)‖ ≤ ε) {s : Plane}
    (hs : ε ^ 2 / 3 ≤ -model a g H s) (t : Plane) :
    (‖point a (-g)‖ ^ 2 / 100) * (0 - model a g H t) ≤ 0 - model a g H s := by
  have hv0 := norm_nonneg (point a (-g))
  have he0 : 0 ≤ ε := hv0.trans hv
  have hm := model_ge_neg_two_thirds hH (hv.trans hε) t
  have hsq : ‖point a (-g)‖ ^ 2 ≤ ε ^ 2 := (sq_le_sq₀ hv0 he0).mpr hv
  have hp := mul_le_mul_of_nonneg_left (show 0 - model a g H t ≤ 2 / 3 by linarith)
    (show 0 ≤ ‖point a (-g)‖ ^ 2 / 100 by positivity)
  nlinarith [sq_nonneg ε]

end Optimization.TransverseModelLowerBound
