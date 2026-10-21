import Numlib.Optimization.TransverseModelLowerBound
import Numlib.Optimization.ExactRegularizationPrescribedReturns
import Mathlib.Tactic

/-!
# Short vertical trials for a transverse objective

The fixed capped-quadratic and inverse-square-root objective admits explicit short vertical
trials in its slow tail. Their actual cubic models decrease more than every transverse
inspection direction, their actual model derivatives pass a first-order test, and the true
Taylor prediction is positive with acceptance ratio at least one.
-/

noncomputable section
namespace Optimization.TransverseTailTrial
open TransverseObjective TransverseCubicModel
open scoped InnerProductSpace

/-- The scalar tail window and tolerance range for the prescribed vertical trial. -/
structure Conditions (ε b : ℝ) : Prop where
  epsilon_pos : 0 < ε
  epsilon_le : ε ≤ 1 / 65536
  tail : 1 ≤ b
  slope_lower : ε / 12 < -InverseSqrtTail.first b
  slope_upper : -InverseSqrtTail.first b ≤ 2 * ε / 5
  curvature_upper : InverseSqrtTail.second b ≤ 1 / 100

/-- The prescribed vertical displacement leaves the transverse coordinate unchanged. -/
def step (ε : ℝ) : Plane := point 0 (8 * ε)

/-- The vertical displacement has exactly eight times the positive tolerance as norm. -/
theorem norm_step {ε : ℝ} (hε : 0 ≤ ε) : ‖step ε‖ = 8 * ε := by
  have hn := norm_point_sq 0 (8 * ε)
  change ‖step ε‖ ^ 2 = _ at hn
  nlinarith [norm_nonneg (step ε)]

/-- Every prescribed vertical trial in the tolerance range is strictly short. -/
theorem norm_step_lt_one {ε b : ℝ} (h : Conditions ε b) : ‖step ε‖ < 1 := by
  rw [norm_step h.epsilon_pos.le]
  linarith [h.epsilon_le]

/-- The prescribed vertical trial is nonzero. -/
theorem step_ne_zero {ε : ℝ} (hε : 0 < ε) : step ε ≠ 0 := by
  have hn := norm_step hε.le
  exact norm_pos_iff.mp (by linarith : 0 < ‖step ε‖)

/-- The fixed transverse coordinate lies in the objective's quadratic strip. -/
theorem transverse_abs_le_one {ε b : ℝ} (h : Conditions ε b) : |2 * ε / 3| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [h.epsilon_pos] : 0 ≤ 2 * ε / 3)]
  linarith [h.epsilon_le]

/-- The actual cubic-model decrease of the vertical step has an explicit scalar formula. -/
theorem model_decrease_eq {ε b : ℝ} (h : Conditions ε b) :
    HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 0 -
      HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 (step ε) =
      -8 * ε * InverseSqrtTail.first b - 32 * InverseSqrtTail.second b * ε ^ 2 -
        512 * ε ^ 3 / 3 := by
  rw [actual_model_eq (transverse_abs_le_one h),
    actual_model_eq (transverse_abs_le_one h)]
  rw [model_zero]
  have hn : ‖point 0 (8 * ε)‖ = 8 * ε := norm_step h.epsilon_pos.le
  simp only [model, step, point_zero_coord, point_one_coord, hn]
  ring

/-- The true unregularized Taylor prediction has its exact tail formula. -/
theorem prediction_eq {ε b : ℝ} (h : Conditions ε b) :
    TaylorCriticality.taylorDecrement objective 2 (point (2 * ε / 3) b) (step ε) =
      -8 * ε * InverseSqrtTail.first b - 32 * InverseSqrtTail.second b * ε ^ 2 := by
  rw [taylorDecrement_two_local (transverse_abs_le_one h)]
  simp only [step, point_zero_coord, point_one_coord]
  ring

/-- The true prediction is strictly larger than twenty-six seventy-fifths times the
squared tolerance. -/
theorem prediction_lower {ε b : ℝ} (h : Conditions ε b) :
    26 / 75 * ε ^ 2 <
      TaylorCriticality.taylorDecrement objective 2 (point (2 * ε / 3) b) (step ε) := by
  rw [prediction_eq h]
  have hs := mul_lt_mul_of_pos_right h.slope_lower h.epsilon_pos
  have hH := mul_le_mul_of_nonneg_right h.curvature_upper (sq_nonneg ε)
  nlinarith

/-- The true prediction of the prescribed trial is positive. -/
theorem prediction_pos {ε b : ℝ} (h : Conditions ε b) :
    0 < TaylorCriticality.taylorDecrement objective 2 (point (2 * ε / 3) b) (step ε) :=
  lt_trans (by nlinarith [sq_pos_of_pos h.epsilon_pos]) (prediction_lower h)

/-- The actual cubic model decreases by strictly more than one third of the squared
positive tolerance. -/
theorem model_decrease_lower {ε b : ℝ} (h : Conditions ε b) :
    ε ^ 2 / 3 < HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 0 -
      HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 (step ε) := by
  rw [model_decrease_eq h]
  have hs := mul_lt_mul_of_pos_right h.slope_lower h.epsilon_pos
  have hH := mul_le_mul_of_nonneg_right h.curvature_upper (sq_nonneg ε)
  have hc := mul_le_mul_of_nonneg_right h.epsilon_le (sq_nonneg ε)
  nlinarith [sq_pos_of_pos h.epsilon_pos]

/-- Every transverse inspection radius gives a uniformly bounded actual
cubic-model decrease, including radii outside the objective's quadratic strip. -/
theorem transverse_model_decrease_le {ε b : ℝ} (h : Conditions ε b) (δ : ℝ) :
    HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 0 -
      HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 (point (-δ) 0) ≤
      2 * ε ^ 2 / 9 := by
  rw [actual_model_eq (transverse_abs_le_one h),
    actual_model_eq (transverse_abs_le_one h)]
  rw [model_zero]
  simp only [model, point_zero_coord, point_one_coord]
  have hn : 0 ≤ ‖point (-δ) 0‖ ^ 3 := pow_nonneg (norm_nonneg _) _
  nlinarith [sq_nonneg (δ - 2 * ε / 3)]

/-- The prescribed actual vertical model value is strictly better than every
transverse inspection radius. -/
theorem retained_comparison {ε b : ℝ} (h : Conditions ε b) (δ : ℝ) :
    HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 (step ε) <
      HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 (point (-δ) 0) := by
  have hs := model_decrease_lower h
  have hd := transverse_model_decrease_le h δ
  nlinarith [sq_pos_of_pos h.epsilon_pos]

/-- The true endpoint is in the same quadratic strip and strictly farther along the tail. -/
theorem endpoint {ε b : ℝ} (h : Conditions ε b) :
    point (2 * ε / 3) b + step ε = point (2 * ε / 3) (b + 8 * ε) ∧
      |2 * ε / 3| ≤ 1 ∧ 1 ≤ b + 8 * ε ∧ b < b + 8 * ε := by
  refine ⟨?_, transverse_abs_le_one h, ?_, ?_⟩
  · simp [step]
  · linarith [h.tail, h.epsilon_pos]
  · linarith [h.epsilon_pos]

/-- The exact objective ratio of the prescribed vertical trial is at least one. -/
theorem ratio_ge_one {ε b : ℝ} (h : Conditions ε b) :
    1 ≤ HigherOrderRegularization.ratio objective 2 (point (2 * ε / 3) b) (step ε) := by
  have hs0 := step_ne_zero h.epsilon_pos
  have ht := value_le_taylor (transverse_abs_le_one h) h.tail
    (s := step ε) (by simpa [step] using transverse_abs_le_one h)
    (by simp only [step, point_one_coord]; linarith [h.epsilon_pos])
  have hp := prediction_pos h
  rw [TaylorCriticality.taylorDecrement_eq] at hp
  rw [HigherOrderRegularization.ratio, ite_eq_right hs0]
  rw [RegularizedTaylorModel.taylorModel_zero]
  apply (le_div_iff₀ hp).mpr
  simp only [one_mul]
  linarith

/-- The actual objective derivative at a tail trial's starting point is below the tolerance. -/
theorem norm_fderiv_lt_epsilon {ε b : ℝ} (h : Conditions ε b) :
    ‖fderiv ℝ objective (point (2 * ε / 3) b)‖ < ε := by
  rw [norm_fderiv_objective_local (transverse_abs_le_one h)]
  have hs : InverseSqrtTail.first b ^ 2 ≤ (2 * ε / 5) ^ 2 := by
    have hh := (sq_le_sq₀ (neg_nonneg.mpr (InverseSqrtTail.first_nonpos b))
      (by linarith [h.epsilon_pos] : 0 ≤ 2 * ε / 5)).mpr h.slope_upper
    simpa only [neg_sq] using hh
  have hn := norm_point_sq (2 * ε / 3) (InverseSqrtTail.first b)
  apply (sq_lt_sq₀ (norm_nonneg _) h.epsilon_pos.le).mp
  nlinarith [sq_pos_of_pos h.epsilon_pos]

/-- The true gradient norm cannot increase along the prescribed vertical step. -/
theorem endpoint_norm_fderiv_le {ε b : ℝ} (h : Conditions ε b) :
    ‖fderiv ℝ objective (point (2 * ε / 3) b + step ε)‖ ≤
      ‖fderiv ℝ objective (point (2 * ε / 3) b)‖ := by
  rw [(endpoint h).1, norm_fderiv_objective_local (transverse_abs_le_one h),
    norm_fderiv_objective_local (transverse_abs_le_one h)]
  have hm := InverseSqrtTail.monotoneOn_first h.tail (endpoint h).2.2.1
    (endpoint h).2.2.2.le
  have hs : InverseSqrtTail.first (b + 8 * ε) ^ 2 ≤ InverseSqrtTail.first b ^ 2 := by
    have hh := (sq_le_sq₀
      (neg_nonneg.mpr (InverseSqrtTail.first_nonpos (b + 8 * ε)))
      (neg_nonneg.mpr (InverseSqrtTail.first_nonpos b))).mpr (neg_le_neg hm)
    simpa only [neg_sq] using hh
  have hn₀ := norm_point_sq (2 * ε / 3) (InverseSqrtTail.first b)
  have hn₁ := norm_point_sq (2 * ε / 3) (InverseSqrtTail.first (b + 8 * ε))
  nlinarith [norm_nonneg (point (2 * ε / 3) (InverseSqrtTail.first b)),
    norm_nonneg (point (2 * ε / 3) (InverseSqrtTail.first (b + 8 * ε)))]

/-- The endpoint has a positive actual gradient norm below the tolerance. -/
theorem endpoint_norm_fderiv_bounds {ε b : ℝ} (h : Conditions ε b) :
    0 < ‖fderiv ℝ objective (point (2 * ε / 3) b + step ε)‖ ∧
      ‖fderiv ℝ objective (point (2 * ε / 3) b + step ε)‖ < ε := by
  constructor
  · rw [(endpoint h).1]
    exact norm_pos_iff.mpr (fderiv_objective_ne_zero_of_tail _ (endpoint h).2.2.1)
  · exact (endpoint_norm_fderiv_le h).trans_lt (norm_fderiv_lt_epsilon h)

/-- A forward vertical trial preserves the upper slope and curvature bounds and retains
an explicit positive lower slope bound. -/
theorem endpoint_scalar_bounds {ε b : ℝ} (h : Conditions ε b) :
    ε / 300 < -InverseSqrtTail.first (b + 8 * ε) ∧
      -InverseSqrtTail.first (b + 8 * ε) ≤ 2 * ε / 5 ∧
      InverseSqrtTail.second (b + 8 * ε) ≤ 1 / 100 := by
  have he := endpoint h
  have hm := InverseSqrtTail.monotoneOn_first h.tail he.2.2.1 he.2.2.2.le
  have hH := InverseSqrtTail.antitoneOn_second h.tail he.2.2.1 he.2.2.2.le
  refine ⟨?_, (neg_le_neg hm).trans h.slope_upper, hH.trans h.curvature_upper⟩
  have ht := InverseSqrtTail.first_add_le h.tail
    (by linarith [h.epsilon_pos] : 0 ≤ 8 * ε)
  have hmul := mul_le_mul_of_nonneg_right h.curvature_upper h.epsilon_pos.le
  linarith [h.slope_lower]

/-- The actual first Taylor decrement of a transverse inspection is independent of the
slow-coordinate slope. -/
theorem transverse_decrement_one {ε b : ℝ} (h : Conditions ε b) (δ : ℝ) :
    TaylorCriticality.taylorDecrement objective 1 (point (2 * ε / 3) b) (point (-δ) 0) =
      2 * ε * δ / 3 := by
  rw [taylorDecrement_one_local (transverse_abs_le_one h)]
  simp only [point_zero_coord, point_one_coord]
  ring

/-- Every transverse inspection captures a quarter of the actual first-order gap. -/
theorem transverse_coefficientWitness {ε b : ℝ} (h : Conditions ε b) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    InexactRegularization.CoefficientWitness
      (fun i => iteratedFDeriv ℝ i objective (point (2 * ε / 3) b))
      1 δ (1 / 4) (point (-δ) 0) := by
  have hn : ‖point (-δ) 0‖ = δ := by
    have hs := norm_point_sq (-δ) 0
    nlinarith [norm_nonneg (point (-δ) 0)]
  refine ⟨hn.le, ?_⟩
  have he : InexactTaylorModels.decrement
      (fun i => iteratedFDeriv ℝ i objective (point (2 * ε / 3) b)) 1 =
      TaylorCriticality.taylorDecrement objective 1 (point (2 * ε / 3) b) :=
    funext (InexactTaylorModels.decrement_iteratedFDeriv _ _ _)
  rw [he, TaylorCriticality.gapOn_taylorDecrement_one _ _ hδ,
    transverse_decrement_one h]
  have hmul := mul_le_mul_of_nonneg_left (norm_fderiv_lt_epsilon h).le hδ
  have hp := mul_nonneg h.epsilon_pos.le hδ
  nlinarith

/-- Every positive transverse inspection radius fails the computed one-eighth tolerance
threshold strictly. -/
theorem transverse_computed_failure {ε b : ℝ} (h : Conditions ε b) {δ : ℝ}
    (hδ : 0 < δ) :
    ε * δ / 8 < TaylorCriticality.taylorDecrement objective 1
      (point (2 * ε / 3) b) (point (-δ) 0) := by
  rw [transverse_decrement_one h]
  nlinarith [mul_pos h.epsilon_pos hδ]

/-- The slow component of the actual model gradient is bounded by half the tolerance. -/
theorem abs_model_vertical_gradient_le {ε b : ℝ} (h : Conditions ε b) :
    |InverseSqrtTail.first b + 8 * InverseSqrtTail.second b * ε + 64 * ε ^ 2| ≤ ε / 2 := by
  have hH0 := InverseSqrtTail.second_nonneg b
  have hH := mul_le_mul_of_nonneg_right h.curvature_upper h.epsilon_pos.le
  have hc := mul_le_mul_of_nonneg_right h.epsilon_le h.epsilon_pos.le
  have hm := mul_nonneg hH0 h.epsilon_pos.le
  have hf := InverseSqrtTail.first_nonpos b
  apply abs_le.mpr
  constructor <;> nlinarith [h.slope_upper, h.epsilon_pos, sq_nonneg ε]

/-- The derivative of the actual regularized Taylor model at the prescribed vertical
trial is strictly below seven eighths of the tolerance. -/
theorem norm_fderiv_model_lt {ε b : ℝ} (h : Conditions ε b) :
    ‖fderiv ℝ (HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2)
      (step ε)‖ < 7 * ε / 8 := by
  rw [TransverseModelLowerBound.norm_fderiv_actual_model (transverse_abs_le_one h)]
  have hn : ‖point 0 (8 * ε)‖ = 8 * ε := norm_step h.epsilon_pos.le
  simp only [step, point_zero_coord, point_one_coord, hn, add_zero, mul_zero]
  have hv : |InverseSqrtTail.first b + InverseSqrtTail.second b * (8 * ε) + 8 * ε * (8 * ε)| ≤
      ε / 2 := by
    have he : InverseSqrtTail.first b + InverseSqrtTail.second b * (8 * ε) +
        8 * ε * (8 * ε) = InverseSqrtTail.first b +
        8 * InverseSqrtTail.second b * ε + 64 * ε ^ 2 := by ring
    rw [he]
    exact abs_model_vertical_gradient_le h
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by linarith [h.epsilon_pos] : 0 ≤ ε / 2)).mpr hv
  rw [sq_abs] at hsq
  apply (sq_lt_sq₀ (norm_nonneg _) (by linarith [h.epsilon_pos] : 0 ≤ 7 * ε / 8)).mp
  have hs := norm_point_sq (2 * ε / 3)
    (InverseSqrtTail.first b + InverseSqrtTail.second b * (8 * ε) + 8 * ε * (8 * ε))
  nlinarith [sq_pos_of_pos h.epsilon_pos]

/-- The fixed squared-gradient fraction passes the actual minimizing-fraction test
against every model comparison point, hence against every actual global model minimum. -/
theorem minimizing_fraction {ε b : ℝ} (h : Conditions ε b) (z : Plane) :
    (‖fderiv ℝ objective (point (2 * ε / 3) b)‖ ^ 2 / 100) *
      (HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 0 -
        HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 z) ≤
      HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 0 -
        HigherOrderRegularization.model objective 2 (point (2 * ε / 3) b) 2 (step ε) := by
  have hv : ‖point (2 * ε / 3) (-(-InverseSqrtTail.first b))‖ ≤ ε := by
    simpa only [neg_neg, norm_fderiv_objective_local (transverse_abs_le_one h)] using
      (norm_fderiv_lt_epsilon h).le
  have hs := model_decrease_lower h
  rw [actual_model_eq (transverse_abs_le_one h),
    actual_model_eq (transverse_abs_le_one h), model_zero] at hs
  have hf := TransverseModelLowerBound.squaredSlope_fraction
    (InverseSqrtTail.second_nonneg b) (by linarith [h.epsilon_le] : ε ≤ 1) hv
    (s := step ε) (by linarith : ε ^ 2 / 3 ≤
      -model (2 * ε / 3) (-InverseSqrtTail.first b) (InverseSqrtTail.second b) (step ε)) z
  rw [norm_fderiv_objective_local (transverse_abs_le_one h)]
  rw [actual_model_eq (transverse_abs_le_one h),
    actual_model_eq (transverse_abs_le_one h), actual_model_eq (transverse_abs_le_one h),
    model_zero]
  simp only [neg_neg] at hf
  convert hf using 1 <;> ring

/-- The prescribed vertical step has a genuine two-transition exact-coefficient inner
return under the fixed squared-gradient initialization policy. The scalar constant and
incoming radii are arbitrary, and the retained direction may have any real radius. -/
theorem exists_innerResult {ε b : ℝ} (h : Conditions ε b)
    (P : InexactRegularization.Parameters) (hp : P.p = 2) (hq : P.q = 1)
    (hθ : P.theta = 7 / 8) (he : P.epsilon 1 = ε) (c : ℝ) (radii : ℕ → ℝ) (δ : ℝ) :
    ∃ R : InexactRegularization.InnerResult P c
      (fun i => iteratedFDeriv ℝ i objective (point (2 * ε / 3) b)) 2 radii (point (-δ) 0),
      R.step = step ε ∧ R.length = 2 ∧ R.radii = (fun _ => 1) ∧
      R.execution.state 0 = ⟨‖fderiv ℝ objective (point (2 * ε / 3) b)‖ ^ 2 / 100,
        fun _ => 1, 0, .minimize⟩ := by
  have hμ := InexactRegularization.squaredGradientFraction_bounds objective
    (point (2 * ε / 3) b) (fderiv_objective_ne_zero_of_tail _ h.tail)
    ((norm_fderiv_lt_epsilon h).le.trans (by linarith [h.epsilon_le] : ε ≤ 1))
  apply InexactRegularization.exists_exactShortFirstOrderInnerResult P hq objective
    (point (2 * ε / 3) b) c 2 radii (point (-δ) 0) (step ε)
    (‖fderiv ℝ objective (point (2 * ε / 3) b)‖ ^ 2 / 100)
    (by norm_num) hμ.1 hμ.2 (norm_step_lt_one h)
  · intro z _
    simpa only [hp] using minimizing_fraction h z
  · rw [hp, hθ, he]
    have hg := norm_fderiv_model_lt h
    linarith
  · simpa only [hp] using (retained_comparison h δ).le

end Optimization.TransverseTailTrial
