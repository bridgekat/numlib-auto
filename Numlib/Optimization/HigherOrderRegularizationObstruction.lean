import Numlib.Optimization.HigherOrderRegularizationRun
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# An empty-direction obstruction to a third-order stopping rule

A quadratic objective with small positive curvature can generate empty model direction sets
for quartic regularization. Requiring these sets to be nonempty in the stopping condition
prevents termination, although all model residual and regularization update laws hold.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderRegularization.EmptyDirections
open ParameterUpdates RegularizedTaylorModel

/-- A smooth bounded-below scalar quadratic with constant curvature one half. -/
def objective (x : ℝ) : ℝ := (1 / 4 : ℝ) * x ^ 2

/-- Its actual scalar derivatives, including the vanishing cubic derivative. -/
theorem iteratedDeriv_objective (j : ℕ) (x : ℝ) :
    iteratedDeriv j objective x = (1 / 4 : ℝ) * (2).descFactorial j * x ^ (2 - j) := by
  change iteratedDeriv j (fun z : ℝ => (1 / 4 : ℝ) * z ^ 2) x = _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  ring

/-- Every order of actual derivative tensor is obtained from its scalar derivative. -/
theorem iteratedFDeriv_objective (j : ℕ) (x : ℝ) (v : Fin j → ℝ) :
    iteratedFDeriv ℝ j objective x v =
      ((1 / 4 : ℝ) * (2).descFactorial j * x ^ (2 - j)) * ∏ i, v i := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_objective]
  simp only [smul_eq_mul]
  ring

/-- The cubic Taylor polynomial of this quadratic is exact. -/
theorem taylor_objective (x s : ℝ) : taylorModel objective 3 x s = objective (x + s) := by
  rw [taylorModel_real]
  simp [Finset.sum_range_succ, iteratedDeriv_objective, objective]
  ring

/-- The actual quartically regularized model has an explicit polynomial formula. -/
theorem model_objective (x s : ℝ) : model objective 3 x 6 s =
    (1 / 4 : ℝ) * (x + s) ^ 2 + (1 / 4 : ℝ) * s ^ 4 := by
  rw [model, taylor_objective]
  norm_num [objective, Real.norm_eq_abs, ← abs_pow]
  positivity

/-- A positive model minimizer magnitude exists for every positive current point. -/
theorem exists_magnitude {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ x = t + 2 * t ^ 3 := by
  have hc : Continuous (fun t : ℝ => t + 2 * t ^ 3) := by fun_prop
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx.le _
  have ht := intermediate_value_Icc hx.le hc.continuousOn
    (show x ∈ Set.Icc ((0 : ℝ) + 2 * 0 ^ 3) (x + 2 * x ^ 3) by
      constructor <;> nlinarith)
  obtain ⟨t, ht, heq⟩ := ht
  refine ⟨t, ?_, heq.symm⟩
  by_contra hn
  have hzero : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
  subst t
  norm_num at heq
  linarith

/-- The positive displacement magnitude solving the exact model-gradient equation. -/
def magnitude (x : ℝ) : ℝ := if hx : 0 < x then Classical.choose (exists_magnitude hx) else 0

/-- The selected magnitude is positive and solves the model-gradient equation. -/
theorem magnitude_spec {x : ℝ} (hx : 0 < x) :
    0 < magnitude x ∧ x = magnitude x + 2 * magnitude x ^ 3 := by
  simpa [magnitude, hx] using Classical.choose_spec (exists_magnitude hx)

/-- Positive iterates obtained by exact quartic model minimization. -/
def point : ℕ → ℝ
  | 0 => 4
  | k + 1 => 2 * magnitude (point k) ^ 3

/-- Every iterate is strictly positive. -/
theorem point_pos (k : ℕ) : 0 < point k := by
  induction k with
  | zero => norm_num [point]
  | succ k ih => exact mul_pos (by norm_num) (pow_pos (magnitude_spec ih).1 _)

/-- Each step minimizes the quartic model and stays on the positive half-line. -/
def step (k : ℕ) : ℝ := -magnitude (point k)

/-- The trial point is exactly the next actual iterate. -/
theorem point_succ (k : ℕ) : point (k + 1) = point k + step k := by
  have h := (magnitude_spec (point_pos k)).2
  simp only [point, step]
  linarith

/-- Actual scalar model derivatives are the shifted objective derivatives plus quartic ones. -/
theorem iteratedDeriv_model (j : ℕ) (x s : ℝ) :
    iteratedDeriv j (model objective 3 x 6) s =
      (1 / 4 : ℝ) * (2).descFactorial j * (x + s) ^ (2 - j) +
      (1 / 4 : ℝ) * (4).descFactorial j * s ^ (4 - j) := by
  have he : model objective 3 x 6 =
      (fun s : ℝ ↦ objective (x + s)) + (fun s : ℝ ↦ (1 / 4 : ℝ) * s ^ 4) := by
    funext s
    exact model_objective x s
  rw [he, iteratedDeriv_add (by unfold objective; fun_prop) (by fun_prop),
    iteratedDeriv_comp_const_add]
  dsimp only
  rw [iteratedDeriv_objective,
    iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  ring

/-- Every actual model tensor is obtained from those scalar derivatives. -/
theorem iteratedFDeriv_model (j : ℕ) (x s : ℝ) (v : Fin j → ℝ) :
    iteratedFDeriv ℝ j (model objective 3 x 6) s v =
      ((1 / 4 : ℝ) * (2).descFactorial j * (x + s) ^ (2 - j) +
      (1 / 4 : ℝ) * (4).descFactorial j * s ^ (4 - j)) * ∏ i, v i := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_model]
  simp only [smul_eq_mul]
  ring

/-- The objective has genuine constant least Hessian curvature one half. -/
theorem objective_curvature (x : ℝ) :
    leastCurvature (fderiv ℝ (fderiv ℝ objective) x) = 1 / 2 := by
  apply leastCurvature_eq_of_scalar
  intro u
  have h := iteratedFDeriv_objective 2 x (fun _ ↦ u)
  simp only [iteratedFDeriv_two_apply] at h
  norm_num [Fin.prod_univ_two, Real.norm_eq_abs, sq_abs] at h ⊢
  nlinarith [h]

/-- The model Hessian coefficient is one half plus three squares. -/
theorem model_curvature (x s : ℝ) :
    leastCurvature (fderiv ℝ (fderiv ℝ (model objective 3 x 6)) s) = 1 / 2 + 3 * s ^ 2 := by
  apply leastCurvature_eq_of_scalar
  intro u
  have h := iteratedFDeriv_model 2 x s (fun _ ↦ u)
  simp only [iteratedFDeriv_two_apply] at h
  norm_num [Fin.prod_univ_two, Real.norm_eq_abs, sq_abs] at h ⊢
  nlinarith [h]

/-- The model's small-curvature directions are empty at every selected step. -/
theorem model_directions_empty (k : ℕ) :
    smallCurvatureDirections (model objective 3 (point k) 6) (step k)
      (1 * ‖step k‖ ^ (3 - 1)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hu : d ^ 2 = 1 := by
    rw [← sq_abs, show |d| = 1 from hd.1]
    norm_num
  have hH := iteratedFDeriv_model 2 (point k) (step k) (fun _ ↦ d)
  norm_num [Fin.prod_univ_two] at hH
  have hb := (abs_le.mp hd.2).2
  rw [hH] at hb
  norm_num [Real.norm_eq_abs, sq_abs] at hb
  nlinarith [sq_nonneg (step k)]

/-- The actual model derivative vanishes at each selected step. -/
theorem model_fderiv_zero (k : ℕ) :
    fderiv ℝ (model objective 3 (point k) 6) (step k) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have h := iteratedFDeriv_model 1 (point k) (step k) (fun _ ↦ u)
  have hm := (magnitude_spec (point_pos k)).2
  simp only [iteratedFDeriv_one_apply] at h
  norm_num [step] at h ⊢
  have hz : 1 / 2 * (point k + -magnitude (point k)) +
      (-magnitude (point k)) ^ 3 = 0 := by nlinarith [hm]
  rw [hz] at h
  simpa using h

/-- Every selected nonzero trial strictly reduces its actual regularized model. -/
theorem model_decrease (k : ℕ) :
    model objective 3 (point k) 6 (step k) < model objective 3 (point k) 6 0 := by
  have ht := (magnitude_spec (point_pos k)).1
  have hx := (magnitude_spec (point_pos k)).2
  rw [model_objective, model_objective]
  simp only [step]
  nlinarith [sq_pos_of_pos ht, pow_pos ht 4, sq_nonneg (magnitude (point k) ^ 3)]

/-- The exact Taylor prediction equals the true reduction at every selected trial. -/
theorem ratio_one (k : ℕ) : ratio objective 3 (point k) (step k) = 1 := by
  have hstep : step k ≠ 0 := neg_ne_zero.mpr (ne_of_gt (magnitude_spec (point_pos k)).1)
  rw [ratio, ite_eq_right hstep, taylor_objective, taylor_objective]
  simp only [add_zero]
  apply div_self
  have hm := model_decrease k
  rw [model_objective, model_objective] at hm
  have hreg : 0 ≤ (1 / 4 : ℝ) * step k ^ 4 := by positivity
  unfold objective
  nlinarith

/-- Fixed legal parameters for this exact quartic regularization execution. -/
def parameters : RegularizationParameters where
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

/-- Every finite segment obeys all actual third-order algorithm trial and residual laws. -/
theorem runPrefix (N : ℕ) :
    RunPrefix parameters 3 3 (fun _ ↦ 1) (fun _ ↦ 1) objective point step (fun _ ↦ 6) N := by
  refine
    { initial_lower := by norm_num [parameters]
      update := ?_
      decrease := ?_
      iterate := ?_
      order_pos := by norm_num
      order_le_three := by norm_num
      degree_ge_order := by norm_num
      theta_pos := by intro i; norm_num
      theta_le_one := by intro i; norm_num
      epsilon_pos := by intro i hi; norm_num
      residuals := ?_ }
  · intro k hk
    norm_num [ratio_one, parameters]
  · intro k hk
    exact model_decrease k
  · intro k hk
    simpa only [ratio_one, parameters, show (1 / 4 : ℝ) ≤ 1 by norm_num, ite_true]
      using point_succ k
  · intro k hk
    refine ⟨?_, ?_, ?_⟩
    · rw [model_fderiv_zero]
      simp
    · intro hq
      rw [model_curvature]
      norm_num [Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (step k)]
    · intro hq d hd
      rw [model_directions_empty k] at hd
      exact False.elim hd

/-- The objective is nonnegative everywhere. -/
theorem objective_nonneg (x : ℝ) : 0 ≤ objective x := by
  unfold objective
  positivity

/-- All derivatives of the scalar quadratic are continuous. -/
theorem objective_smooth : ContDiff ℝ 3 objective := by
  unfold objective
  fun_prop

/-- The actual cubic derivative tensor vanishes at every point. -/
theorem iteratedFDeriv_three_objective (x : ℝ) : iteratedFDeriv ℝ 3 objective x = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  have h := iteratedFDeriv_objective 3 x v
  norm_num at h ⊢
  exact h

/-- The cubic derivative is zero, so the actual highest derivative is globally Lipschitz. -/
theorem objective_lipschitz : DiagonalLipschitz objective 3 1 := by
  refine ⟨objective_smooth, by norm_num, ?_⟩
  intro x y d
  have hx := iteratedFDeriv_objective 3 x (fun _ ↦ d)
  have hy := iteratedFDeriv_objective 3 y (fun _ ↦ d)
  norm_num at hx hy
  simp only [sub_apply, hx, hy, sub_self, norm_zero, one_mul]
  positivity

/-- The actual initial derivative is larger than the gradient tolerance. -/
theorem initial_fderiv_norm : 1 < ‖fderiv ℝ objective (point 0)‖ := by
  have h := iteratedFDeriv_objective 1 4 (fun _ ↦ (1 : ℝ))
  norm_num at h
  rw [point, ← norm_deriv_eq_norm_fderiv, h]
  norm_num

/-- This genuine execution never satisfies the nonempty-direction third-order stop. -/
theorem never_stationary (k : ℕ) :
    ¬Stationary 3 (fun _ ↦ 1) objective (point k)
      (directionSequence 3 1 1 objective point step (fun _ ↦ 6) k) := by
  intro h
  cases k with
  | zero => exact (not_le_of_gt initial_fderiv_norm) h.first
  | succ k =>
    have hh := h.third (by decide) (by rw [objective_curvature]; norm_num)
    have hn := hh.1
    rw [directionSequence_succ, model_directions_empty] at hn
    exact Set.not_nonempty_empty hn

/-- Consequently no finite first-stop certificate exists for this legal infinite execution. -/
theorem not_isRun (N : ℕ) :
    ¬IsRun parameters 3 3 (fun _ ↦ 1) (fun _ ↦ 1) objective point step (fun _ ↦ 6) N := by
  intro h
  exact never_stationary N h.terminal

/-- The actual local laws hold for every finite length, on a smooth bounded-below objective,
although no index satisfies the algorithm's third-order stopping test. This obstruction
concerns stopping with a nonempty direction set, independently of any vacuous final quality
certificate that permits an empty set. -/
theorem infinite_execution :
    (∀ x, 0 ≤ objective x) ∧ DiagonalLipschitz objective 3 1 ∧
    (∀ N, RunPrefix parameters 3 3 (fun _ ↦ 1) (fun _ ↦ 1)
      objective point step (fun _ ↦ 6) N) ∧
    (∀ k, ¬Stationary 3 (fun _ ↦ 1) objective (point k)
      (directionSequence 3 1 1 objective point step (fun _ ↦ 6) k)) :=
  ⟨objective_nonneg, objective_lipschitz, runPrefix, never_stationary⟩

end Optimization.HigherOrderRegularization.EmptyDirections
