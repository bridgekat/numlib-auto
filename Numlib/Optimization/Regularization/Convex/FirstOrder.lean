import Numlib.Optimization.Regularization.HighOrder.Parameter
import Numlib.Optimization.Constrained.FirstOrderCriticality

/-!
# Primitive first-order adaptive regularization on convex constraints

The first-order mode of ARp-CC disables both higher-order tests. Actual Taylor
models, feasible trials, objective ratios, parameter intervals and constrained
model-gradient tests specify each step. Termination and complexity are not
assumptions of the finite execution prefix.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed legal first-order ARp-CC settings, independent of all requested accuracies. -/
structure Settings (p : ℕ) where
  order_pos : 0 < p
  tau : ℝ
  theta : ℝ
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  sigmaMin : ℝ
  sigmaInitial : ℝ
  tau_pos : 0 < tau
  tau_lt_one : tau < 1
  theta_lower : (1 + tau) / 2 ≤ theta
  theta_lt_one : theta < 1
  eta1_pos : 0 < eta1
  eta1_le_eta2 : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma1_lt_one : gamma1 < 1
  one_lt_gamma2 : 1 < gamma2
  gamma2_lt_gamma3 : gamma2 < gamma3
  sigmaMin_pos : 0 < sigmaMin
  sigmaMin_le_initial : sigmaMin ≤ sigmaInitial

/-- Primitive arrays of actual constrained regularization iterates and trials. -/
structure Data (E : Type*) where
  point : ℕ → E
  step : ℕ → E
  parameter : ℕ → ℝ
  ratio : ℕ → ℝ

/-- The first-order-only source execution has actual constrained model tests.
The endpoint may be returned by a caller's additional stopping test. No endpoint
optimality or evaluation bound is required for a valid primitive prefix. -/
structure Run {p : ℕ} (f : E → ℝ) (C : Set E) (P : Settings p) (ε : ℝ)
    (D : Data E) (N : ℕ) : Prop where
  accuracy_pos : 0 < ε
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_mem : D.point 0 ∈ C
  modelTrace : ModelTrace f p D.point D.step D.parameter D.ratio
    P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N
  feasible_trial : ∀ i < N, D.point i + D.step i ∈ C
  model_test : ∀ i < N,
    constrainedCriticality (model f p (D.point i) (D.parameter i)) 1
      (feasibleDisplacements C (D.point i)) (D.step i) 1 ≤ P.theta * ε
  continues : ∀ i < N, ε < constrainedCriticality f 1 C (D.point i) 1

variable {p : ℕ} {f : E → ℝ} {C : Set E} {P : Settings p} {ε : ℝ}
  {D : Data E} {N : ℕ}

/-- Every actual iterate in a valid primitive execution remains feasible. -/
theorem Run.mem (h : Run f C P ε D N) {i : ℕ} (hi : i ≤ N) : D.point i ∈ C := by
  induction i with
  | zero => exact h.initial_mem
  | succ i ih =>
    rw [h.modelTrace.point_update i (by omega)]
    split_ifs
    · exact h.feasible_trial i (by omega)
    · exact ih (by omega)

/-- Restricting a primitive execution preserves every actual model and update rule. -/
theorem Run.restrict (h : Run f C P ε D N) {M : ℕ} (hM : M ≤ N) :
    Run f C P ε D M where
  accuracy_pos := h.accuracy_pos
  initial_parameter := h.initial_parameter
  initial_mem := h.initial_mem
  modelTrace := h.modelTrace.restrict hM
  feasible_trial := fun i hi => h.feasible_trial i (hi.trans_le hM)
  model_test := fun i hi => h.model_test i (hi.trans_le hM)
  continues := fun i hi => h.continues i (hi.trans_le hM)

/-- Every primitive trial has a genuine positive prediction denominator. -/
theorem Run.denominator_pos (h : Run f C P ε D N) {i : ℕ} (hi : i < N) :
    0 < decrement f p (D.point i) (D.step i) := h.modelTrace.denominator_pos hi

/-- Rejection preserves the actual point exactly. -/
theorem Run.rejected (h : Run f C P ε D N) {i : ℕ} (hi : i < N)
    (hn : D.ratio i < P.eta1) : D.point (i + 1) = D.point i := by
  rw [h.modelTrace.point_update i hi, ite_eq_right (not_le.mpr hn)]

/-- Actual accepted trials decrease the objective, and rejected trials leave it unchanged. -/
theorem Run.objective_succ_le (h : Run f C P ε D N) {i : ℕ} (hi : i < N) :
    f (D.point (i + 1)) ≤ f (D.point i) := by
  by_cases hs : P.eta1 ≤ D.ratio i
  · have hh := h.modelTrace.successful_decrease hi hs
    have hη := P.eta1_pos
    have hσ := P.sigmaMin_pos
    have hlo : 0 ≤ P.eta1 * P.sigmaMin / (p + 1).factorial * ‖D.step i‖ ^ (p + 1) := by
      positivity
    linarith
  · rw [h.modelTrace.point_update i hi, ite_eq_right hs]

/-- Any later actual inner iterate has objective no greater than an earlier one. -/
theorem Run.objective_le (h : Run f C P ε D N) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    f (D.point j) ≤ f (D.point i) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (h.objective_succ_le (by omega)).trans (ih (by omega))

end ConvexRegularization
