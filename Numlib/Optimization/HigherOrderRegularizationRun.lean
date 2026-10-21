import Numlib.Optimization.HigherOrderRegularization
import Numlib.Optimization.ParameterUpdatesFinite
import Numlib.Optimization.HessianCurvature

/-!
# Finite higher-order regularization runs

Executed trials strictly reduce their actual factorial-normalized Taylor model. Derivative
residual tests use the actual model derivatives. Third-order stopping is restricted to the
model's small-curvature directions; the direction set is updated even after a rejected trial.
Finite prefixes do not assume termination. A complete run separately records its first stop.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderRegularization
open ParameterUpdates RegularizedTaylorModel

variable {E : Type*} [NormedAddCommGroup E]

section Normed
variable [NormedSpace ℝ E]

/-- Actual model decrease, acceptance and interval updates on a finite executed prefix. -/
structure TrialPrefix (params : RegularizationParameters) (degree : ℕ) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    RegularizationPrefix params (fun k => ratio f degree (x k) (s k)) sigma N where
  decrease : ∀ k < N, model f degree (x k) (sigma k) (s k) < model f degree (x k) (sigma k) 0
  iterate : ∀ k < N, x (k + 1) = if params.eta1 ≤ ratio f degree (x k) (s k)
    then x k + s k else x k

variable {params : RegularizationParameters} {degree N : ℕ} {f : E → ℝ}
    {x s : ℕ → E} {sigma : ℕ → ℝ}

/-- Strict model decrease excludes zero executed steps. -/
theorem TrialPrefix.step_ne_zero (h : TrialPrefix params degree f x s sigma N)
    {k : ℕ} (hk : k < N) : s k ≠ 0 := by
  intro hz
  have hd := h.decrease k hk
  rw [hz] at hd
  exact lt_irrefl _ hd

/-- Every executed trial pays the full regularization term in Taylor reduction. -/
theorem TrialPrefix.predicted_decrease (h : TrialPrefix params degree f x s sigma N)
    {k : ℕ} (hk : k < N) :
    sigma k / ((degree + 1)! : ℝ) * ‖s k‖ ^ (degree + 1) ≤
      taylorModel f degree (x k) 0 - taylorModel f degree (x k) (s k) :=
  predicted_decrease_of_model_le (h.decrease k hk).le

/-- The denominator of every executed actual acceptance ratio is positive. -/
theorem TrialPrefix.predicted_pos (h : TrialPrefix params degree f x s sigma N)
    {k : ℕ} (hk : k < N) : 0 < taylorModel f degree (x k) 0 -
      taylorModel f degree (x k) (s k) :=
  (mul_pos (div_pos (h.toRegularizationPrefix.pos (by omega)) (by positivity))
    (pow_pos (norm_pos_iff.mpr (h.step_ne_zero hk)) _)).trans_le (h.predicted_decrease hk)

/-- Above the Taylor-error threshold every executed trial is very successful. -/
theorem TrialPrefix.ratio_ge_of_sigma_ge (h : TrialPrefix params degree f x s sigma N)
    {L : ℝ} (hf : DiagonalLipschitz f degree L) (hp : 1 ≤ degree)
    {k : ℕ} (hk : k < N) (hb : L / (1 - params.eta2) ≤ sigma k) :
    params.eta2 ≤ ratio f degree (x k) (s k) :=
  ratio_ge_of_prediction hf hp (h.step_ne_zero hk) (h.predicted_pos hk)
    (h.predicted_decrease hk) hb

/-- The standard parameter bound holds through the final index of a finite prefix. -/
theorem TrialPrefix.sigma_upper (h : TrialPrefix params degree f x s sigma N)
    {L : ℝ} (hf : DiagonalLipschitz f degree L) (hp : 1 ≤ degree)
    {k : ℕ} (hk : k ≤ N) :
    sigma k ≤ max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) :=
  h.toRegularizationPrefix.upper (fun _ hj hb => h.ratio_ge_of_sigma_ge hf hp hj hb) hk

/-- Successful trials realize their acceptance fraction of actual Taylor reduction. -/
theorem TrialPrefix.accepted_decrease (h : TrialPrefix params degree f x s sigma N)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f degree (x k) (s k)) :
    params.eta1 * (taylorModel f degree (x k) 0 - taylorModel f degree (x k) (s k)) ≤
      f (x k) - f (x (k + 1)) := by
  rw [h.iterate k hk, ite_eq_left hs]
  rw [ratio, ite_eq_right (h.step_ne_zero hk)] at hs
  exact (le_div_iff₀ (h.predicted_pos hk)).mp hs

/-- Every executed step is nonincreasing in the true objective. -/
theorem TrialPrefix.objective_nonincrease (h : TrialPrefix params degree f x s sigma N)
    {k : ℕ} (hk : k < N) : f (x (k + 1)) ≤ f (x k) := by
  by_cases hs : params.eta1 ≤ ratio f degree (x k) (s k)
  · have hd := h.accepted_decrease hk hs
    have hn := mul_nonneg params.eta1_pos.le (h.predicted_pos hk).le
    linarith
  · rw [h.iterate k hk, ite_eq_right hs]

/-- The source's unit directions of small absolute Hessian curvature. -/
def smallCurvatureDirections (g : E → ℝ) (z : E) (threshold : ℝ) : Set E :=
  {d | ‖d‖ = 1 ∧ |iteratedFDeriv ℝ 2 g z (fun _ => d)| ≤ threshold}

/-- Membership is precisely the unit-norm and actual second-derivative test. -/
@[simp] theorem mem_smallCurvatureDirections (g : E → ℝ) (z d : E) (threshold : ℝ) :
    d ∈ smallCurvatureDirections g z threshold ↔ ‖d‖ = 1 ∧
      |iteratedFDeriv ℝ 2 g z (fun _ => d)| ≤ threshold := Iff.rfl

/-- The initial direction set uses the objective; every successor set uses the latest trial's
model and computed step, including after a rejected trial. -/
def directionSequence (degree : ℕ) (theta2 epsilon2 : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) : ℕ → Set E
  | 0 => smallCurvatureDirections f (x 0) epsilon2
  | k + 1 => smallCurvatureDirections (model f degree (x k) (sigma k)) (s k)
      (theta2 * ‖s k‖ ^ (degree - 1))

/-- Initially, small-curvature directions refer to the actual objective at the initial point. -/
@[simp] theorem directionSequence_zero (degree : ℕ) (theta2 epsilon2 : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) :
    directionSequence degree theta2 epsilon2 f x s sigma 0 =
      smallCurvatureDirections f (x 0) epsilon2 := rfl

/-- The next direction set always refers to the model used for the latest computed trial. -/
@[simp] theorem directionSequence_succ (degree : ℕ) (theta2 epsilon2 : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) (k : ℕ) :
    directionSequence degree theta2 epsilon2 f x s sigma (k + 1) =
      smallCurvatureDirections (model f degree (x k) (sigma k)) (s k)
        (theta2 * ‖s k‖ ^ (degree - 1)) := rfl

/-- One objective value is computed initially and one at each executed trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Every derivative order through the model degree is evaluated initially and after each
accepted trial; rejected trials reuse the existing derivative tensors. -/
def derivativeEvaluations (params : RegularizationParameters) (degree : ℕ) (f : E → ℝ)
    (x s : ℕ → E) (N : ℕ) : ℕ :=
  successCount (fun k => params.eta1 ≤ ratio f degree (x k) (s k)) N + 1

end Normed

section Inner
variable [InnerProductSpace ℝ E]
variable {f : E → ℝ}

/-- Derivative conditions for an actual computed model step. Higher-order tests are activated
by `order`; third-order residuals are required only on the model direction set. -/
structure ModelResiduals (order degree : ℕ) (theta : Fin 3 → ℝ) (f : E → ℝ)
    (z : E) (sigma : ℝ) (step : E) : Prop where
  first : ‖fderiv ℝ (model f degree z sigma) step‖ ≤ theta 0 * ‖step‖ ^ degree
  second : 2 ≤ order → -(theta 1 * ‖step‖ ^ (degree - 1)) ≤
    leastCurvature (fderiv ℝ (fderiv ℝ (model f degree z sigma)) step)
  third : 3 ≤ order → ∀ d ∈ smallCurvatureDirections (model f degree z sigma) step
    (theta 1 * ‖step‖ ^ (degree - 1)),
    |iteratedFDeriv ℝ 3 (model f degree z sigma) step (fun _ => d)| ≤
      theta 2 * ‖step‖ ^ (degree - 2)

/-- Exact activated stopping tests, including strict positive-curvature termination and the
nonempty model-direction requirement for the third-order branch. -/
def Stationary (order : ℕ) (epsilon : Fin 3 → ℝ) (f : E → ℝ) (z : E) (D : Set E) : Prop :=
  ‖fderiv ℝ f z‖ ≤ epsilon 0 ∧
    (2 ≤ order → epsilon 1 < leastCurvature (fderiv ℝ (fderiv ℝ f) z) ∨
      (-epsilon 1 ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) z) ∧
        (3 ≤ order → D.Nonempty ∧ ∀ d ∈ D,
          |iteratedFDeriv ℝ 3 f z (fun _ => d)| ≤ epsilon 2 ∧
          |iteratedFDeriv ℝ 2 f z (fun _ => d)| ≤ epsilon 1)))

/-- First-order stopping is exactly the derivative-norm threshold. -/
@[simp] theorem stationary_one_iff (epsilon : Fin 3 → ℝ) (f : E → ℝ) (z : E) (D : Set E) :
    Stationary 1 epsilon f z D ↔ ‖fderiv ℝ f z‖ ≤ epsilon 0 := by simp [Stationary]

/-- Every activated stop passes the first derivative test. -/
theorem Stationary.first {order : ℕ} {epsilon : Fin 3 → ℝ} {z : E} {D : Set E}
    (h : Stationary order epsilon f z D) : ‖fderiv ℝ f z‖ ≤ epsilon 0 := h.1

/-- Every second-order stop has the required Hessian lower bound. -/
theorem Stationary.second {order : ℕ} {epsilon : Fin 3 → ℝ} {z : E} {D : Set E}
    (h : Stationary order epsilon f z D) (hq : 2 ≤ order) (he : 0 ≤ epsilon 1) :
    -epsilon 1 ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) z) := by
  rcases h.2 hq with hs | hs
  · linarith
  · exact hs.1

/-- When strict positive curvature has not already terminated the run, the third-order
branch explicitly controls the objective only along the current model direction set. -/
theorem Stationary.third {order : ℕ} {epsilon : Fin 3 → ℝ} {z : E} {D : Set E}
    (h : Stationary order epsilon f z D) (hq : 3 ≤ order)
    (hs : ¬epsilon 1 < leastCurvature (fderiv ℝ (fderiv ℝ f) z)) :
    D.Nonempty ∧ ∀ d ∈ D, |iteratedFDeriv ℝ 3 f z (fun _ => d)| ≤ epsilon 2 ∧
      |iteratedFDeriv ℝ 2 f z (fun _ => d)| ≤ epsilon 1 :=
  ((h.2 (by omega)).resolve_left hs).2 hq

/-- Full finite local algorithm laws without assuming a terminal test. -/
structure RunPrefix (params : RegularizationParameters) (order degree : ℕ)
    (theta epsilon : Fin 3 → ℝ) (f : E → ℝ) (x s : ℕ → E)
    (sigma : ℕ → ℝ) (N : ℕ) : Prop extends TrialPrefix params degree f x s sigma N where
  order_pos : 1 ≤ order
  order_le_three : order ≤ 3
  degree_ge_order : order ≤ degree
  theta_pos : ∀ i, 0 < theta i
  theta_le_one : ∀ i, theta i ≤ 1
  epsilon_pos : ∀ i : Fin 3, i.val < order → 0 < epsilon i
  residuals : ∀ k < N, ModelResiduals order degree theta f (x k) (sigma k) (s k)

/-- A complete finite execution stops at the first activated criticality test. -/
structure IsRun (params : RegularizationParameters) (order degree : ℕ)
    (theta epsilon : Fin 3 → ℝ) (f : E → ℝ) (x s : ℕ → E)
    (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    RunPrefix params order degree theta epsilon f x s sigma N where
  terminal : Stationary order epsilon f (x N)
    (directionSequence degree (theta 1) (epsilon 1) f x s sigma N)
  first : ∀ k < N, ¬Stationary order epsilon f (x k)
    (directionSequence degree (theta 1) (epsilon 1) f x s sigma k)

end Inner

end Optimization.HigherOrderRegularization
