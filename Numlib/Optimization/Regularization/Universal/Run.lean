import Numlib.Analysis.SpecialFunctions.FiniteFactorial
import Numlib.Analysis.Calculus.TaylorModel.PolynomialDerivative

/-!
# Universal regularization with real powers

The actual Taylor polynomial is regularized with the source finite factorial.
The trial-point derivative test precedes acceptance. Optional second-order
accuracy disables its test explicitly, and no lower parameter safeguard is added.
-/
namespace UniversalRegularization
attribute [local instance] Classical.propDecidable
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real-power regularized Taylor model. -/
noncomputable def model (f : E → ℝ) (p : ℕ) (r : ℝ) (x : E) (σ : ℝ) (s : E) : ℝ :=
  TaylorModel.eval f p x s + σ / Real.finiteFactorial r * ‖s‖ ^ r

/-- Fixed algorithm parameters, independent of requested accuracies. -/
structure Settings (p : ℕ) where
  r : ℝ
  theta1 : ℝ
  theta2 : ℝ
  alpha1 : ℝ
  alpha2 : ℝ
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  sigmaInitial : ℝ
  order_pos : 1 ≤ p
  power_gt : (p : ℝ) < r
  theta1_pos : 0 < theta1
  theta1_le : theta1 ≤ 1
  theta2_pos : 0 < theta2
  theta2_le : theta2 ≤ 1
  alpha1_pos : 0 < alpha1
  alpha1_le : alpha1 ≤ 1/3 * min 1 (Real.finiteFactorial (r-1))
  alpha2_pos : 0 < alpha2
  alpha2_le : alpha2 ≤ 1/3 * min 1 (Real.finiteFactorial (r-2))
  eta1_pos : 0 < eta1
  eta12 : eta1 ≤ eta2
  eta2_lt : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma1_lt : gamma1 < 1
  gamma2_gt : 1 < gamma2
  gamma23 : gamma2 < gamma3
  sigmaInitial_pos : 0 < sigmaInitial

/-- The algorithm's first- and optional second-order stopping tests. -/
def Stops (f : E → ℝ) (ε1 : ℝ) (ε2 : Option ℝ) (x : E) : Prop :=
  ‖fderiv ℝ f x‖ ≤ ε1 ∧ ∀ e ∈ ε2,
    ∀ v : E, ‖v‖ = 1 → -e ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)

/-- The primitive model improvement and true model derivative tests. -/
structure Step (f : E → ℝ) {p : ℕ} (P : Settings p) (ε2 : Option ℝ)
    (x s : E) (σ : ℝ) : Prop where
  improvement : model f p P.r x σ s < model f p P.r x σ 0
  first : ‖fderiv ℝ (model f p P.r x σ) s‖ ≤ P.theta1 * ‖s‖ ^ (P.r-1)
  second : ∀ e ∈ ε2, ∀ v : E, ‖v‖ = 1 →
    -P.theta2 * ‖s‖ ^ (P.r-2) ≤
      iteratedFDeriv ℝ 2 (model f p P.r x σ) s (fun _ => v)

/-- Actual points, trial steps and regularization parameters. -/
structure Data (E : Type*) where
  point : ℕ → E
  step : ℕ → E
  parameter : ℕ → ℝ

/-- The ratio uses the true objective and actual Taylor decrease. -/
noncomputable def ratio (f : E → ℝ) (p : ℕ) (D : Data E) (k : ℕ) : ℝ :=
  (f (D.point k) - f (D.point k + D.step k)) /
    (f (D.point k) - TaylorModel.eval f p (D.point k) (D.step k))

/-- Acceptance requires the two source length tests in addition to the ratio. -/
def LengthChecks (f : E → ℝ) {p : ℕ} (P : Settings p) (ε2 : Option ℝ)
    (D : Data E) (k : ℕ) : Prop :=
  P.alpha1 * ‖fderiv ℝ f (D.point k + D.step k)‖ ≤
    D.parameter k * ‖D.step k‖ ^ (P.r-1) ∧
  ∀ e ∈ ε2, ∀ v : E, ‖v‖ = 1 →
    -P.alpha2 * iteratedFDeriv ℝ 2 f (D.point k + D.step k) (fun _ => v) ≤
      D.parameter k * ‖D.step k‖ ^ (P.r-2)

/-- A prefix of the algorithm before any trial-point stopping test passes.
The initial check and all trial checks are literal derivative tests. -/
structure Run (f : E → ℝ) {p : ℕ} (P : Settings p) (ε1 : ℝ) (ε2 : Option ℝ)
    (D : Data E) (N : ℕ) : Prop where
  accuracy1_pos : 0 < ε1
  accuracy1_le : ε1 ≤ 1
  accuracy2 : ∀ e ∈ ε2, 0 < e ∧ e ≤ 1 ∧ 2 ≤ p
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_failure : ¬Stops f ε1 ε2 (D.point 0)
  step_test : ∀ k < N, Step f P ε2 (D.point k) (D.step k) (D.parameter k)
  trial_failure : ∀ k < N, ¬Stops f ε1 ε2 (D.point k + D.step k)
  point_update : ∀ k < N,
    D.point (k+1) = if P.eta1 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k
      then D.point k + D.step k else D.point k
  parameter_update : ∀ k < N,
    if P.eta2 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k then
      D.parameter (k+1) ∈ Icc (P.gamma1 * D.parameter k) (D.parameter k)
    else if P.eta1 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k then
      D.parameter (k+1) ∈ Icc (D.parameter k) (P.gamma2 * D.parameter k)
    else D.parameter (k+1) ∈ Icc (P.gamma2 * D.parameter k) (P.gamma3 * D.parameter k)

/-- At zero step, the actual model equals the current objective value. -/
@[simp] theorem model_zero (f : E → ℝ) {p : ℕ} (P : Settings p) (x : E) (σ : ℝ) :
    model f p P.r x σ 0 = f x := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hr := P.power_gt
  simp [model, Real.zero_rpow (by linarith : P.r ≠ 0)]

/-- Strict actual model improvement excludes zero steps. -/
theorem Step.ne_zero {f : E → ℝ} {p : ℕ} {P : Settings p} {ε2 : Option ℝ}
    {x s : E} {σ : ℝ} (h : Step f P ε2 x s σ) : s ≠ 0 := by
  intro hs
  have hh := h.improvement
  rw [hs] at hh
  exact (lt_irrefl _ hh)

/-- Actual strict model improvement gives the Taylor decrease with its exact coefficient. -/
theorem Step.taylor_decrease {f : E → ℝ} {p : ℕ} {P : Settings p} {ε2 : Option ℝ}
    {x s : E} {σ : ℝ} (h : Step f P ε2 x s σ) :
    σ / Real.finiteFactorial P.r * ‖s‖ ^ P.r <
      f x - TaylorModel.eval f p x s := by
  have hh := h.improvement
  rw [model_zero f P] at hh
  unfold model at hh
  linarith

/-- Every parameter in an actual finite prefix remains strictly positive. -/
theorem Run.parameter_pos {f : E → ℝ} {p : ℕ} {P : Settings p}
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k ≤ N) : 0 < D.parameter k := by
  induction k with
  | zero => rw [h.initial_parameter]; exact P.sigmaInitial_pos
  | succ k ih =>
    have hp := ih (by omega)
    have hu := h.parameter_update k (by omega)
    split_ifs at hu with hv hs
    · exact (mul_pos P.gamma1_pos hp).trans_le hu.1
    · exact hp.trans_le hu.1
    · exact (mul_pos (by linarith [P.gamma2_gt]) hp).trans_le hu.1

/-- Consequently every actual trial ratio has a positive Taylor denominator. -/
theorem Run.prediction_pos {f : E → ℝ} {p : ℕ} {P : Settings p}
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k < N) :
    0 < f (D.point k) - TaylorModel.eval f p (D.point k) (D.step k) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hr := P.power_gt
  have hfac := Real.finiteFactorial_pos (show 0 ≤ P.r by linarith)
  have hs := (h.step_test k hk).ne_zero
  have hb : 0 < D.parameter k / Real.finiteFactorial P.r * ‖D.step k‖ ^ P.r :=
    mul_pos (div_pos (h.parameter_pos hk.le) hfac) (Real.rpow_pos_of_pos (norm_pos_iff.mpr hs) _)
  exact hb.trans (h.step_test k hk).taylor_decrease
end UniversalRegularization
