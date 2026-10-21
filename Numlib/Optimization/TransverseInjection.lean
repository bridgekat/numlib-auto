import Numlib.Optimization.TransverseModelLowerBound
import Numlib.Optimization.ExactRegularizationPrescribedReturns

/-!
# A transverse injection for the fixed two-coordinate objective

A small positive transverse step retains every skew first-order inspection direction.
Its true cubic-model derivative satisfies a strict first-order inner tolerance, while the
actual objective has acceptance ratio at least one.
-/

noncomputable section
namespace Optimization.TransverseInjection
open TransverseObjective TransverseCubicModel TransverseModelLowerBound

/-- The local scalar inequalities defining the injection region. -/
structure Conditions (ε b : ℝ) : Prop where
  tolerance_pos : 0 < ε
  tolerance_le : ε ≤ 1 / 65536
  tail : 1 ≤ b
  slope_lower : ε / 3 < -InverseSqrtTail.first b
  slope_upper : -InverseSqrtTail.first b ≤ 2 * ε / 5
  curvature_upper : InverseSqrtTail.second b ≤ 1 / 100

/-- The prescribed short injection moves in both actual coordinates. -/
def step (ε : ℝ) : Plane := point (2 * ε / 3) (4 * ε)

/-- The injection has its specified transverse coordinate. -/
@[simp] theorem step_zero (ε : ℝ) : step ε 0 = 2 * ε / 3 := point_zero_coord _ _

/-- The injection has its specified slow coordinate. -/
@[simp] theorem step_one (ε : ℝ) : step ε 1 = 4 * ε := point_one_coord _ _

/-- The actual norm of the prescribed injection is bounded by five tolerances. -/
theorem norm_step_le {ε b : ℝ} (h : Conditions ε b) : ‖step ε‖ ≤ 5 * ε := by
  have hn := norm_point_sq (2 * ε / 3) (4 * ε)
  change ‖step ε‖ ^ 2 = _ at hn
  nlinarith [norm_nonneg (step ε), sq_nonneg ε, h.tolerance_pos]

/-- Every injection is strictly short. -/
theorem norm_step_lt_one {ε b : ℝ} (h : Conditions ε b) : ‖step ε‖ < 1 := by
  have hn := norm_step_le h
  linarith [h.tolerance_le]

/-- The cubic radial penalty is less than one thousandth of the squared tolerance. -/
theorem radial_penalty_le {ε b : ℝ} (h : Conditions ε b) :
    ‖step ε‖ ^ 3 / 3 ≤ ε ^ 2 / 1000 := by
  have hp := pow_le_pow_left₀ (norm_nonneg (step ε)) (norm_step_le h) 3
  have he := mul_le_mul_of_nonneg_right h.tolerance_le (sq_nonneg ε)
  nlinarith [sq_nonneg ε]

/-- The injection's actual explicit-model decrease is strictly greater than tolerance squared. -/
theorem model_decrease_gt {ε b : ℝ} (h : Conditions ε b) :
    ε ^ 2 < -model 0 (-InverseSqrtTail.first b) (InverseSqrtTail.second b) (step ε) := by
  have hg := mul_lt_mul_of_pos_right h.slope_lower h.tolerance_pos
  have hH := mul_le_mul_of_nonneg_right h.curvature_upper (sq_nonneg ε)
  have hr := radial_penalty_le h
  simp only [model, step_zero, step_one, zero_mul, zero_sub]
  nlinarith [sq_pos_of_pos h.tolerance_pos]

/-- The true Taylor prediction of the injection is positive. -/
theorem taylor_prediction_pos {ε b : ℝ} (h : Conditions ε b) :
    0 < TaylorCriticality.taylorDecrement objective 2 (point 0 b) (step ε) := by
  have hd := model_decrease_gt h
  rw [taylorDecrement_two_local (by norm_num : |(0 : ℝ)| ≤ 1)]
  simp only [model, step_zero, step_one, zero_mul, zero_sub] at hd ⊢
  nlinarith [pow_nonneg (norm_nonneg (step ε)) 3, sq_pos_of_pos h.tolerance_pos]

/-- The first model-gradient component is nonnegative and at most seven tenths of tolerance. -/
theorem gradient_first_bounds {ε b : ℝ} (h : Conditions ε b) :
    0 ≤ 2 * ε / 3 + ‖step ε‖ * (2 * ε / 3) ∧
      2 * ε / 3 + ‖step ε‖ * (2 * ε / 3) ≤ 7 * ε / 10 := by
  have hε := h.tolerance_pos
  have hn := norm_step_le h
  have he := mul_le_mul_of_nonneg_right h.tolerance_le h.tolerance_pos.le
  have hp := mul_le_mul_of_nonneg_right hn h.tolerance_pos.le
  constructor
  · positivity
  · nlinarith

/-- The second actual model-gradient component has magnitude at most half tolerance. -/
theorem gradient_second_bounds {ε b : ℝ} (h : Conditions ε b) :
    |InverseSqrtTail.first b + InverseSqrtTail.second b * (4 * ε) +
      ‖step ε‖ * (4 * ε)| ≤ ε / 2 := by
  have hH0 := InverseSqrtTail.second_nonneg b
  have hr0 := norm_nonneg (step ε)
  have hH := mul_le_mul_of_nonneg_right h.curvature_upper h.tolerance_pos.le
  have hr := mul_le_mul_of_nonneg_right (norm_step_le h) h.tolerance_pos.le
  have he := mul_le_mul_of_nonneg_right h.tolerance_le h.tolerance_pos.le
  have hpH := mul_nonneg hH0 h.tolerance_pos.le
  have hpr := mul_nonneg hr0 h.tolerance_pos.le
  rw [abs_le]
  constructor <;> nlinarith [h.slope_lower, h.slope_upper]

/-- The actual cubic-model derivative at the injection meets the strict inner target. -/
theorem norm_fderiv_model_lt {ε b : ℝ} (h : Conditions ε b) :
    ‖fderiv ℝ (HigherOrderRegularization.model objective 2 (point 0 b) 2) (step ε)‖ <
      7 / 8 * ε := by
  have hε := h.tolerance_pos
  rw [norm_fderiv_actual_model (by norm_num : |(0 : ℝ)| ≤ 1)]
  simp only [step_zero, step_one, zero_add]
  obtain ⟨hx0, hx1⟩ := gradient_first_bounds h
  have hy := (abs_le.mp (gradient_second_bounds h))
  have hxsq := (sq_le_sq₀ hx0 (show 0 ≤ 7 * ε / 10 by positivity)).mpr hx1
  have hysq := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ ε / 2 by positivity)).mpr
    (gradient_second_bounds h)
  rw [sq_abs] at hysq
  have hn := norm_point_sq (2 * ε / 3 + ‖step ε‖ * (2 * ε / 3))
    (InverseSqrtTail.first b + InverseSqrtTail.second b * (4 * ε) + ‖step ε‖ * (4 * ε))
  have hp := sq_pos_of_pos h.tolerance_pos
  nlinarith [norm_nonneg (point (2 * ε / 3 + ‖step ε‖ * (2 * ε / 3))
    (InverseSqrtTail.first b + InverseSqrtTail.second b * (4 * ε) + ‖step ε‖ * (4 * ε)))]

/-- The actual objective ratio is at least one for the injection. -/
theorem ratio_ge_one {ε b : ℝ} (h : Conditions ε b) :
    1 ≤ HigherOrderRegularization.ratio objective 2 (point 0 b) (step ε) := by
  have hε := h.tolerance_pos
  have hs0 : step ε ≠ 0 := by
    intro he
    have hh := congrArg (fun d : Plane => d 1) he
    simp only [step_one, PiLp.zero_apply] at hh
    linarith [h.tolerance_pos]
  have ha : |0 + step ε 0| ≤ 1 := by
    simp only [step_zero, zero_add]
    rw [abs_of_nonneg (by positivity)]
    linarith [h.tolerance_le]
  have ht := value_le_taylor (by norm_num : |(0 : ℝ)| ≤ 1) h.tail ha
    (show 0 ≤ step ε 1 by simp only [step_one]; positivity)
  have hp := taylor_prediction_pos h
  rw [HigherOrderRegularization.ratio, ite_eq_right hs0]
  have he := TaylorCriticality.taylorDecrement_eq objective 2 (point 0 b) (step ε)
  have hp' : 0 < RegularizedTaylorModel.taylorModel objective 2 (point 0 b) 0 -
      RegularizedTaylorModel.taylorModel objective 2 (point 0 b) (step ε) := by
    simpa only [RegularizedTaylorModel.taylorModel_zero] using (he ▸ hp)
  apply (le_div_iff₀ hp').mpr
  simp only [one_mul, RegularizedTaylorModel.taylorModel_zero]
  linarith

/-- The skew inspection direction uses half its radius in the slow coordinate. -/
def direction (δ : ℝ) : Plane := point (Real.sqrt 3 / 2 * δ) (δ / 2)

/-- Every real skew direction has norm equal to the absolute radius. -/
theorem norm_direction (δ : ℝ) : ‖direction δ‖ = |δ| := by
  have hn : ‖direction δ‖ ^ 2 = δ ^ 2 := by
    unfold direction
    rw [norm_point_sq, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  nlinarith [norm_nonneg (direction δ), abs_nonneg δ, sq_abs δ]

/-- The skew direction's model decrease is bounded uniformly over all real radii. -/
theorem direction_model_decrease_le (g H δ : ℝ) (hH : 0 ≤ H) :
    -model 0 g H (direction δ) ≤ g ^ 2 / 6 := by
  have hn := mul_nonneg hH (sq_nonneg (δ / 2))
  have hr := pow_nonneg (norm_nonneg (direction δ)) 3
  dsimp only [direction] at hr
  unfold model direction
  simp only [point_zero_coord, point_one_coord, zero_mul, zero_sub]
  rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [sq_nonneg (3 * δ - 2 * g)]

/-- Under the injection slope bound, every skew direction decreases the model by at most
 two seventy-fifths of tolerance squared. -/
theorem direction_decrease_le {ε b : ℝ} (h : Conditions ε b) (δ : ℝ) :
    -model 0 (-InverseSqrtTail.first b) (InverseSqrtTail.second b) (direction δ) ≤
      2 * ε ^ 2 / 75 := by
  have he := h.tolerance_pos
  have hg0 : 0 ≤ -InverseSqrtTail.first b := by linarith [h.slope_lower]
  have hg := (sq_le_sq₀ hg0 (show 0 ≤ 2 * ε / 5 by positivity)).mpr h.slope_upper
  have hd := direction_model_decrease_le (-InverseSqrtTail.first b)
    (InverseSqrtTail.second b) δ (InverseSqrtTail.second_nonneg b)
  nlinarith

/-- The actual injected step retains every skew direction, independently of search radius. -/
theorem actual_retained {ε b : ℝ} (h : Conditions ε b) (δ : ℝ) :
    HigherOrderRegularization.model objective 2 (point 0 b) 2 (step ε) ≤
      HigherOrderRegularization.model objective 2 (point 0 b) 2 (direction δ) := by
  rw [actual_model_eq (by norm_num : |(0 : ℝ)| ≤ 1),
    actual_model_eq (by norm_num : |(0 : ℝ)| ≤ 1)]
  have hs := model_decrease_gt h
  have hd := direction_decrease_le h δ
  nlinarith [sq_nonneg ε]

/-- The initial true slope norm is precisely the positive scalar tail slope. -/
theorem initial_slope_eq (b : ℝ) :
    ‖fderiv ℝ objective (point 0 b)‖ = -InverseSqrtTail.first b := by
  rw [norm_fderiv_objective_local (by norm_num : |(0 : ℝ)| ≤ 1)]
  have hn := norm_point_sq 0 (InverseSqrtTail.first b)
  have hg := InverseSqrtTail.first_nonpos b
  nlinarith [norm_nonneg (point 0 (InverseSqrtTail.first b))]

/-- The initial true slope norm is below tolerance and strictly positive. -/
theorem initial_slope_bounds {ε b : ℝ} (h : Conditions ε b) :
    0 < ‖fderiv ℝ objective (point 0 b)‖ ∧
      ‖fderiv ℝ objective (point 0 b)‖ ≤ ε := by
  rw [initial_slope_eq b]
  constructor <;> linarith [h.slope_lower, h.slope_upper, h.tolerance_pos]

/-- The fixed squared-gradient policy meets the genuine minimizing-fraction inequality
against every actual cubic Taylor-model comparison point. -/
theorem actual_fraction {ε b : ℝ} (h : Conditions ε b) (t : Plane) :
    (‖fderiv ℝ objective (point 0 b)‖ ^ 2 / 100) *
      (HigherOrderRegularization.model objective 2 (point 0 b) 2 0 -
        HigherOrderRegularization.model objective 2 (point 0 b) 2 t) ≤
      HigherOrderRegularization.model objective 2 (point 0 b) 2 0 -
        HigherOrderRegularization.model objective 2 (point 0 b) 2 (step ε) := by
  have he : ε ≤ 1 := by linarith [h.tolerance_le]
  have hv : ‖point 0 (-(-InverseSqrtTail.first b))‖ ≤ ε := by
    simpa only [neg_neg, norm_fderiv_objective_local (by norm_num : |(0 : ℝ)| ≤ 1)] using
      (initial_slope_bounds h).2
  have hs : ε ^ 2 / 3 ≤
      -model 0 (-InverseSqrtTail.first b) (InverseSqrtTail.second b) (step ε) := by
    have hh := model_decrease_gt h
    nlinarith [sq_nonneg ε]
  have hf := squaredSlope_fraction (InverseSqrtTail.second_nonneg b) he hv hs t
  simp only [actual_model_eq (by norm_num : |(0 : ℝ)| ≤ 1), model_zero, add_zero,
    neg_neg] at hf ⊢
  rw [norm_fderiv_objective_local (by norm_num : |(0 : ℝ)| ≤ 1)]
  convert hf using 1 <;> ring

/-- The endpoint stays inside the nonnegative transverse quadratic strip and advances
strictly along the inverse-square-root tail. -/
theorem endpoint_geometry {ε b : ℝ} (h : Conditions ε b) :
    0 ≤ 2 * ε / 3 ∧ 2 * ε / 3 ≤ 1 ∧ b < b + 4 * ε := by
  have he := h.tolerance_pos
  constructor
  · positivity
  constructor <;> linarith [h.tolerance_le]

/-- The actual endpoint's true derivative remains positive and strictly below tolerance. -/
theorem endpoint_slope_bounds {ε b : ℝ} (h : Conditions ε b) :
    0 < ‖fderiv ℝ objective (point 0 b + step ε)‖ ∧
      ‖fderiv ℝ objective (point 0 b + step ε)‖ < ε := by
  have he := h.tolerance_pos
  have ha : |2 * ε / 3| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith [h.tolerance_le]
  have hb : 1 ≤ b + 4 * ε := by linarith [h.tail]
  have hx : point 0 b + step ε = point (2 * ε / 3) (b + 4 * ε) := by
    simpa only [step, zero_add] using point_add 0 b (2 * ε / 3) (4 * ε)
  rw [hx]
  constructor
  · exact norm_pos_iff.mpr (fderiv_objective_ne_zero_of_tail _ hb)
  · rw [norm_fderiv_objective_local ha]
    have hm := InverseSqrtTail.monotoneOn_first h.tail hb
      (show b ≤ b + 4 * ε by linarith)
    have hy0 := InverseSqrtTail.first_nonpos (b + 4 * ε)
    have hy : -InverseSqrtTail.first (b + 4 * ε) ≤ 2 * ε / 5 := by
      linarith [h.slope_upper]
    have hysq := (sq_le_sq₀ (neg_nonneg.mpr hy0)
      (show 0 ≤ 2 * ε / 5 by positivity)).mpr hy
    rw [neg_sq] at hysq
    have hn := norm_point_sq (2 * ε / 3) (InverseSqrtTail.first (b + 4 * ε))
    nlinarith [norm_nonneg (point (2 * ε / 3) (InverseSqrtTail.first (b + 4 * ε))),
      sq_pos_of_pos he]

/-- The skew direction's true first-order decrement is half the slow slope times radius. -/
theorem direction_decrement_one (b δ : ℝ) :
    TaylorCriticality.taylorDecrement objective 1 (point 0 b) (direction δ) =
      -InverseSqrtTail.first b * δ / 2 := by
  rw [taylorDecrement_one_local (by norm_num : |(0 : ℝ)| ≤ 1)]
  simp only [direction, point_one_coord]
  ring

/-- Every nonnegative skew radius gives a genuine quarter-fraction first-order witness. -/
theorem direction_coefficientWitness {ε b : ℝ} (h : Conditions ε b) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    InexactRegularization.CoefficientWitness
      (fun i => iteratedFDeriv ℝ i objective (point 0 b)) 1 δ (1 / 4) (direction δ) := by
  refine ⟨by rw [norm_direction, abs_of_nonneg hδ], ?_⟩
  have he : InexactTaylorModels.decrement
      (fun i => iteratedFDeriv ℝ i objective (point 0 b)) 1 =
      TaylorCriticality.taylorDecrement objective 1 (point 0 b) :=
    funext (InexactTaylorModels.decrement_iteratedFDeriv _ _ _)
  rw [he, TaylorCriticality.gapOn_taylorDecrement_one _ _ hδ,
    direction_decrement_one, initial_slope_eq b]
  have hg := mul_nonneg (show 0 ≤ -InverseSqrtTail.first b by
    linarith [h.slope_lower, h.tolerance_pos]) hδ
  linarith

/-- Every positive skew radius fails the literal computed threshold strictly. -/
theorem direction_computed_failure {ε b : ℝ} (h : Conditions ε b) {δ : ℝ}
    (hδ : 0 < δ) : ε * δ / 8 <
      TaylorCriticality.taylorDecrement objective 1 (point 0 b) (direction δ) := by
  rw [direction_decrement_one]
  have hg := mul_lt_mul_of_pos_right h.slope_lower hδ
  nlinarith [mul_pos h.tolerance_pos hδ]

/-- All analytic gates produce an actual short inner return for the skew inspection.
The global model minimum, both actual transitions and the fixed fraction are constructed. -/
theorem exists_innerResult {ε b : ℝ} (h : Conditions ε b)
    (P : InexactRegularization.Parameters) (hp : P.p = 2) (hq : P.q = 1)
    (hθ : P.theta = 7 / 8) (he : P.epsilon 1 = ε) (c : ℝ) (radii : ℕ → ℝ) (δ : ℝ) :
    ∃ R : InexactRegularization.InnerResult P c
      (fun i => iteratedFDeriv ℝ i objective (point 0 b)) 2 radii (direction δ),
      R.step = step ε ∧ R.length = 2 ∧ R.radii = (fun _ => 1) ∧
      R.execution.state 0 = ⟨‖fderiv ℝ objective (point 0 b)‖ ^ 2 / 100,
        fun _ => 1, 0, .minimize⟩ := by
  have hμ := InexactRegularization.squaredGradientFraction_bounds objective (point 0 b)
    (fderiv_objective_ne_zero_of_tail _ h.tail)
    ((initial_slope_bounds h).2.trans (by linarith [h.tolerance_le] : ε ≤ 1))
  apply InexactRegularization.exists_exactShortFirstOrderInnerResult P hq objective (point 0 b)
    c 2 radii (direction δ) (step ε) (‖fderiv ℝ objective (point 0 b)‖ ^ 2 / 100)
    (by norm_num) hμ.1 hμ.2 (norm_step_lt_one h)
  · intro z _
    simpa only [hp] using actual_fraction h z
  · simpa only [hp, hθ, he] using (norm_fderiv_model_lt h).le
  · simpa only [hp] using actual_retained h δ

end Optimization.TransverseInjection
