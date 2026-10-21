import Numlib.Optimization.TransverseObjective
import Numlib.Optimization.HigherOrderApproximateRegularization
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-!
# Cubic models with a transverse quadratic coordinate

The two-coordinate cubic model has explicit stationarity equations at a global minimum.
Positive slow-coordinate slope and nonnegative curvature determine its signs and bound its
step norm. The actual capped-quadratic and inverse-square-root objective supplies the same
model throughout its quadratic strip.
-/

noncomputable section
namespace Optimization.TransverseCubicModel
open TransverseObjective
open scoped InnerProductSpace

/-- A quadratic model with one unit curvature, regularized by one third of the norm cubed. -/
def model (a g H : ℝ) (s : Plane) : ℝ :=
  a * s 0 - g * s 1 + ((s 0) ^ 2 + H * (s 1) ^ 2) / 2 + ‖s‖ ^ 3 / 3

/-- At zero displacement, the model without its constant term is zero. -/
@[simp] theorem model_zero (a g H : ℝ) : model a g H 0 = 0 := by simp [model]

/-- The actual derivative includes the radial term even at the origin. -/
theorem hasFDerivAt_model (a g H : ℝ) (s : Plane) :
    HasFDerivAt (model a g H)
      (((a + s 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        (-g + H * s 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) +
        ‖s‖ • innerSL ℝ s) s := by
  have h₀ : HasFDerivAt (fun x : Plane => x 0)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) s :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have h₁ : HasFDerivAt (fun x : Plane => x 1)
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) s :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have hn := (hasFDerivAt_norm_rpow s (by norm_num : (1 : ℝ) < 3)).const_smul (1 / 3 : ℝ)
  norm_num only [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one] at hn
  have hp := ((h₀.const_mul a).sub (h₁.const_mul g)).add
    (((h₀.pow 2).add ((h₁.pow 2).const_mul H)).const_smul (1 / 2 : ℝ))
  convert hp.add hn using 1
  · ext x
    simp only [model, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Real.rpow_ofNat]
    ring
  · ext d
    simp
    ring

/-- Evaluation of the actual model derivative in any ambient direction. -/
theorem fderiv_model_apply (a g H : ℝ) (s d : Plane) :
    fderiv ℝ (model a g H) s d =
      (a + s 0) * d 0 + (-g + H * s 1) * d 1 + ‖s‖ * ⟪s, d⟫_ℝ := by
  rw [(hasFDerivAt_model a g H s).fderiv]
  simp

/-- The two stationarity equations hold at every actual global model minimum. -/
theorem minimizer_stationarity {a g H : ℝ} {s : Plane}
    (hmin : ∀ d, model a g H s ≤ model a g H d) :
    a + s 0 + ‖s‖ * s 0 = 0 ∧ -g + H * s 1 + ‖s‖ * s 1 = 0 := by
  have hl : IsLocalMin (model a g H) s := Filter.Eventually.of_forall hmin
  have hf := hl.fderiv_eq_zero
  have h₀ := congrArg (fun A : Plane →L[ℝ] ℝ => A (point 1 0)) hf
  have h₁ := congrArg (fun A : Plane →L[ℝ] ℝ => A (point 0 1)) hf
  rw [fderiv_model_apply] at h₀ h₁
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    point_zero_coord, point_one_coord, star_trivial, one_mul,
    mul_one, mul_zero, zero_mul, add_zero, zero_add, zero_apply] at h₀ h₁
  exact ⟨h₀, h₁⟩

/-- A positive slow-coordinate slope forces every model minimum to be nonzero. -/
theorem minimizer_ne_zero {a g H : ℝ} (hg : 0 < g) {s : Plane}
    (hmin : ∀ d, model a g H s ≤ model a g H d) : s ≠ 0 := by
  intro hs
  have h := (minimizer_stationarity hmin).2
  rw [hs] at h
  simp at h
  linarith

/-- The transverse component of a model minimum is the damped negative current coordinate. -/
theorem minimizer_first {a g H : ℝ} {s : Plane}
    (hmin : ∀ d, model a g H s ≤ model a g H d) :
    s 0 = -a / (1 + ‖s‖) := by
  have h := (minimizer_stationarity hmin).1
  apply (eq_div_iff (by positivity : 1 + ‖s‖ ≠ 0)).mpr
  nlinarith

/-- The slow-coordinate component is positive and has its exact curvature denominator. -/
theorem minimizer_second {a g H : ℝ} (hg : 0 < g) (hH : 0 ≤ H) {s : Plane}
    (hmin : ∀ d, model a g H s ≤ model a g H d) :
    s 1 = g / (H + ‖s‖) := by
  have hr := norm_pos_iff.mpr (minimizer_ne_zero hg hmin)
  have h := (minimizer_stationarity hmin).2
  apply (eq_div_iff (by positivity : H + ‖s‖ ≠ 0)).mpr
  nlinarith

/-- Every global minimum moves strictly forward in the slow coordinate. -/
theorem minimizer_second_pos {a g H : ℝ} (hg : 0 < g) (hH : 0 ≤ H) {s : Plane}
    (hmin : ∀ d, model a g H s ≤ model a g H d) : 0 < s 1 := by
  rw [minimizer_second hg hH hmin]
  exact div_pos hg (add_pos_of_nonneg_of_pos hH
    (norm_pos_iff.mpr (minimizer_ne_zero hg hmin)))

/-- A nonnegative transverse coordinate remains between zero and its previous value. -/
theorem minimizer_transverse_bounds {a g H : ℝ} (ha : 0 ≤ a) {s : Plane}
    (hmin : ∀ d, model a g H s ≤ model a g H d) :
    0 ≤ a + s 0 ∧ a + s 0 ≤ a := by
  have he := (minimizer_stationarity hmin).1
  have hs : s 0 ≤ 0 := by
    rw [minimizer_first hmin]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hn := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg s) hs
  constructor <;> linarith

/-- Nonnegative model curvature bounds the squared step norm by the initial slope norm. -/
theorem minimizer_norm_sq_le {a g H : ℝ} (hH : 0 ≤ H) {s : Plane}
    (hmin : ∀ d, model a g H s ≤ model a g H d) :
    ‖s‖ ^ 2 ≤ ‖point a (-g)‖ := by
  obtain ⟨h₀, h₁⟩ := minimizer_stationarity hmin
  have hn : ‖s‖ ^ 2 = (s 0) ^ 2 + (s 1) ^ 2 := by
    simpa only [point_coords] using norm_point_sq (s 0) (s 1)
  have hcs := (abs_le.mp (abs_real_inner_le_norm (point a (-g)) s)).1
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    point_zero_coord, point_one_coord, star_trivial] at hcs
  have hHsq := mul_nonneg hH (sq_nonneg (s 1))
  have hmul₀ := congrArg (fun x : ℝ => x * s 0) h₀
  have hmul₁ := congrArg (fun x : ℝ => x * s 1) h₁
  by_cases hz : ‖s‖ = 0
  · rw [hz]
    simp
  · have hr : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg s) (Ne.symm hz)
    nlinarith

/-- A slope norm below one forces every actual global model minimizer to be strictly short. -/
theorem minimizer_norm_lt_one {a g H : ℝ} (hH : 0 ≤ H)
    (hg : ‖point a (-g)‖ < 1) {s : Plane}
    (hmin : ∀ d, model a g H s ≤ model a g H d) : ‖s‖ < 1 := by
  have h := minimizer_norm_sq_le hH hmin
  nlinarith [norm_nonneg s]

/-- The actual cubic Taylor model agrees with the explicit quadratic-radial model. -/
theorem actual_model_eq {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) (s : Plane) :
    HigherOrderRegularization.model objective 2 (point a b) 2 s =
      objective (point a b) + model a (-InverseSqrtTail.first b) (InverseSqrtTail.second b) s := by
  rw [cubic_model_eq ha]
  unfold model
  ring

/-- Actual global cubic Taylor minimizers minimize the explicit model as well. -/
theorem actual_minimizer_model {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) {s : Plane}
    (hmin : ∀ d, HigherOrderRegularization.model objective 2 (point a b) 2 s ≤
      HigherOrderRegularization.model objective 2 (point a b) 2 d) :
    ∀ d, model a (-InverseSqrtTail.first b) (InverseSqrtTail.second b) s ≤
      model a (-InverseSqrtTail.first b) (InverseSqrtTail.second b) d := by
  intro d
  have h := hmin d
  rw [actual_model_eq ha, actual_model_eq ha] at h
  linarith

/-- The actual objective derivative has the Euclidean norm of its two local scalar slopes. -/
theorem norm_fderiv_objective_local {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) :
    ‖fderiv ℝ objective (point a b)‖ = ‖point a (InverseSqrtTail.first b)‖ := by
  rw [← toDual_gradient, LinearIsometryEquiv.norm_map, gradient_objective]
  simp only [point_zero_coord, point_one_coord, CappedQuadratic.first_eq_of_abs_le_one ha]

/-- Every actual global cubic Taylor minimum is strictly short when the true slope norm is. -/
theorem actual_minimizer_norm_lt_one {a : ℝ} (ha : |a| ≤ 1) (b : ℝ)
    (hg : ‖fderiv ℝ objective (point a b)‖ < 1) {s : Plane}
    (hmin : ∀ d, HigherOrderRegularization.model objective 2 (point a b) 2 s ≤
      HigherOrderRegularization.model objective 2 (point a b) 2 d) : ‖s‖ < 1 := by
  apply minimizer_norm_lt_one (InverseSqrtTail.second_nonneg b) _ (actual_minimizer_model ha b hmin)
  simpa only [neg_neg, norm_fderiv_objective_local ha] using hg

/-- A tail-region actual cubic minimum is nonzero and moves forward in the tail. -/
theorem actual_minimizer_movement {a : ℝ} (ha : |a| ≤ 1) {b : ℝ} (hb : 1 ≤ b)
    (ha0 : 0 ≤ a) {s : Plane}
    (hmin : ∀ d, HigherOrderRegularization.model objective 2 (point a b) 2 s ≤
      HigherOrderRegularization.model objective 2 (point a b) 2 d) :
    s ≠ 0 ∧ 0 ≤ a + s 0 ∧ a + s 0 ≤ a ∧ 0 < s 1 := by
  have hm := actual_minimizer_model ha b hmin
  have hg : 0 < -InverseSqrtTail.first b := neg_pos.mpr
    (InverseSqrtTail.first_neg_of_one_le hb)
  have hx := minimizer_transverse_bounds ha0 hm
  exact ⟨minimizer_ne_zero hg hm, hx.1, hx.2,
    minimizer_second_pos hg (InverseSqrtTail.second_nonneg b) hm⟩

/-- Any forward tail step with both transverse coordinates in the quadratic strip has
an actual value bounded above by the unregularized Taylor polynomial. -/
theorem value_le_taylor {a b : ℝ} (ha : |a| ≤ 1) (hb : 1 ≤ b) {s : Plane}
    (ha' : |a + s 0| ≤ 1) (hs : 0 ≤ s 1) :
    objective (point a b + s) ≤ RegularizedTaylorModel.taylorModel objective 2 (point a b) s := by
  have ht := TaylorCriticality.taylorDecrement_eq objective 2 (point a b) s
  rw [taylorDecrement_two_local ha] at ht
  have he : point a b + s = point (a + s 0) (b + s 1) := by
    simpa only [point_coords] using point_add a b (s 0) (s 1)
  rw [he, objective_point, CappedQuadratic.value_eq_of_abs_le_one ha']
  rw [objective_point, CappedQuadratic.value_eq_of_abs_le_one ha] at ht
  have h := InverseSqrtTail.taylor_upper hb hs
  nlinarith

/-- Every actual cubic minimum in the nonnegative quadratic strip is very successful,
using the true unregularized Taylor denominator of the acceptance ratio. -/
theorem actual_minimizer_ratio_ge_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 1 ≤ b) {s : Plane}
    (hmin : ∀ d, HigherOrderRegularization.model objective 2 (point a b) 2 s ≤
      HigherOrderRegularization.model objective 2 (point a b) 2 d) :
    1 ≤ HigherOrderRegularization.ratio objective 2 (point a b) s := by
  have ha : |a| ≤ 1 := by rwa [abs_of_nonneg ha0]
  obtain ⟨hs0, hx0, hx1, hsy⟩ := actual_minimizer_movement ha hb ha0 hmin
  have ha' : |a + s 0| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1.trans ha1
  have hm := hmin 0
  have hpred := HigherOrderRegularization.predicted_decrease_of_model_le hm
  have hpos : 0 < RegularizedTaylorModel.taylorModel objective 2 (point a b) 0 -
      RegularizedTaylorModel.taylorModel objective 2 (point a b) s := by
    have hr := norm_pos_iff.mpr hs0
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one] at hpred
    linarith [show 0 < (2 : ℝ) / 6 * ‖s‖ ^ 3 by positivity]
  rw [HigherOrderRegularization.ratio, ite_eq_right hs0]
  apply (le_div_iff₀ hpos).mpr
  have ht := value_le_taylor ha hb ha' hsy.le
  simp only [one_mul, RegularizedTaylorModel.taylorModel_zero]
  linarith

/-- Actual slope norms cannot increase along these globally minimizing forward-tail steps. -/
theorem actual_minimizer_norm_fderiv_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 1 ≤ b) {s : Plane}
    (hmin : ∀ d, HigherOrderRegularization.model objective 2 (point a b) 2 s ≤
      HigherOrderRegularization.model objective 2 (point a b) 2 d) :
    ‖fderiv ℝ objective (point a b + s)‖ ≤ ‖fderiv ℝ objective (point a b)‖ := by
  have ha : |a| ≤ 1 := by rwa [abs_of_nonneg ha0]
  obtain ⟨_, hx0, hx1, hs⟩ := actual_minimizer_movement ha hb ha0 hmin
  have ha' : |a + s 0| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1.trans ha1
  have hbb : 1 ≤ b + s 1 := by linarith
  have he : point a b + s = point (a + s 0) (b + s 1) := by
    simpa only [point_coords] using point_add a b (s 0) (s 1)
  rw [he, norm_fderiv_objective_local ha', norm_fderiv_objective_local ha]
  have hm := InverseSqrtTail.monotoneOn_first hb hbb (by linarith)
  have hs₀ := InverseSqrtTail.first_nonpos b
  have hs₁ := InverseSqrtTail.first_nonpos (b + s 1)
  have hf : InverseSqrtTail.first (b + s 1) ^ 2 ≤ InverseSqrtTail.first b ^ 2 := by
    have hh := (sq_le_sq₀ (neg_nonneg.mpr hs₁) (neg_nonneg.mpr hs₀)).mpr
      (neg_le_neg hm)
    simpa only [neg_sq] using hh
  have hx : (a + s 0) ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hx0 ha0).mpr hx1
  have hn₀ := norm_point_sq a (InverseSqrtTail.first b)
  have hn₁ := norm_point_sq (a + s 0) (InverseSqrtTail.first (b + s 1))
  nlinarith [norm_nonneg (point a (InverseSqrtTail.first b)),
    norm_nonneg (point (a + s 0) (InverseSqrtTail.first (b + s 1)))]

/-- The actual derivative stays nonzero in the tail, independently of the transverse value. -/
theorem fderiv_objective_ne_zero_of_tail (a : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    fderiv ℝ objective (point a b) ≠ 0 := by
  intro h
  have hh := congrArg (fun A : Plane →L[ℝ] ℝ => A (point 0 1)) h
  rw [fderiv_objective] at hh
  simp only [point_zero_coord, point_one_coord, mul_zero, mul_one, zero_add, zero_apply] at hh
  have hn := InverseSqrtTail.first_neg_of_one_le hb
  linarith

/-- There is an actual global cubic model minimum satisfying the entire short-step tail
invariant, preserving every strict upper bound on the true slope norm and having ratio at
least one. -/
theorem exists_short_accepted_minimizer {a b ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 1 ≤ b) (hε : ε ≤ 1) (hg : ‖fderiv ℝ objective (point a b)‖ < ε) :
    ∃ s : Plane,
      (∀ d, HigherOrderRegularization.model objective 2 (point a b) 2 s ≤
        HigherOrderRegularization.model objective 2 (point a b) 2 d) ∧
      s ≠ 0 ∧ ‖s‖ < 1 ∧ 0 ≤ a + s 0 ∧ a + s 0 ≤ a ∧ 0 < s 1 ∧
      1 ≤ HigherOrderRegularization.ratio objective 2 (point a b) s ∧
      0 < ‖fderiv ℝ objective (point a b + s)‖ ∧
      ‖fderiv ℝ objective (point a b + s)‖ < ε := by
  obtain ⟨s, hm⟩ := HigherOrderApproximateRegularization.exists_model_minimizer objective 2
    (point a b) (by norm_num : (0 : ℝ) < 2)
  have ha : |a| ≤ 1 := by rwa [abs_of_nonneg ha0]
  obtain ⟨hs0, hx0, hx1, hs1⟩ := actual_minimizer_movement ha hb ha0 hm
  have he : point a b + s = point (a + s 0) (b + s 1) := by
    simpa only [point_coords] using point_add a b (s 0) (s 1)
  refine ⟨s, hm, hs0, actual_minimizer_norm_lt_one ha b (hg.trans_le hε) hm,
    hx0, hx1, hs1, actual_minimizer_ratio_ge_one ha0 ha1 hb hm, ?_, ?_⟩
  · rw [he]
    exact norm_pos_iff.mpr (fderiv_objective_ne_zero_of_tail _ (by linarith))
  · exact (actual_minimizer_norm_fderiv_le ha0 ha1 hb hm).trans_lt hg

end Optimization.TransverseCubicModel
