import Numlib.Optimization.Regularization.Convex.FirstOrderComplexity
import Numlib.Optimization.LeastSquares.LowerOrder

/-!
# Actual first-order convexly constrained least-norm regularization

The source residual-power merit and normalized constrained criticality specify
the actual stopping disjunction. Genuine scaled model tests, ratios, feasible
trials and parameter updates define the execution. A fixed-tolerance ARp1-CC
prefix is derived from failure of the relative stopping tests.
-/

namespace ConvexLeastSquares
open Set TaylorModel HighOrderRegularization LeastSquares
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- The actual constrained objective measure divided by the residual-power weight. -/
noncomputable def firstMeasure (r : E → F) (ℓ : ℝ) (C : Set E) (x : E) : ℝ :=
  constrainedCriticality (powerObjective r ℓ) 1 C x 1 / ‖r x‖ ^ (ℓ - 1)

/-- The exact first-order ARpLE-CC residual or normalized-criticality stopping rule. -/
def Stop (r : E → F) (ℓ : ℝ) (C : Set E) (ε₀ ε₁ : ℝ) (x : E) : Prop :=
  ‖r x‖ ≤ ε₀ ∨ firstMeasure r ℓ C x ≤ ε₁

/-- At a positive global tolerance the normalized stopping disjunction is
identical to its scaled form, including zero residuals. -/
theorem stop_iff_scaled (r : E → F) (ℓ : ℝ) (C : Set E) {ε₀ ε₁ : ℝ}
    (hε : 0 < ε₀) (x : E) : Stop r ℓ C ε₀ ε₁ x ↔
    ‖r x‖ ≤ ε₀ ∨ constrainedCriticality (powerObjective r ℓ) 1 C x 1 ≤
      ε₁ * ‖r x‖ ^ (ℓ - 1) := by
  by_cases hn : ‖r x‖ ≤ ε₀
  · simp [Stop, hn]
  · have hp : 0 < ‖r x‖ := hε.trans (not_le.mp hn)
    simp only [Stop, hn, false_or, firstMeasure]
    exact div_le_iff₀ (Real.rpow_pos_of_pos hp _)

/-- Primitive actual ARpLE-CC executions use exactly the scaled source model
test and the residual/normalized constrained first-order stopping rule. -/
structure Run {p : ℕ} (r : E → F) (ℓ : ℝ) (C : Set E)
    (P : ConvexRegularization.Settings p) (ε₀ ε₁ : ℝ)
    (D : ConvexRegularization.Data E) (N : ℕ) : Prop where
  residual_order : 1 < ℓ
  accuracy_global_pos : 0 < ε₀
  accuracy_first_pos : 0 < ε₁
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_mem : D.point 0 ∈ C
  trace : ModelTrace (powerObjective r ℓ) p D.point D.step D.parameter D.ratio
    P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N
  feasible_trial : ∀ i < N, D.point i + D.step i ∈ C
  model_test : ∀ i < N,
    constrainedCriticality (model (powerObjective r ℓ) p (D.point i) (D.parameter i)) 1
      (feasibleDisplacements C (D.point i)) (D.step i) 1 ≤ P.theta * ‖D.step i‖ ^ p
  continues : ∀ i < N, ¬Stop r ℓ C ε₀ ε₁ (D.point i)

variable {p : ℕ} {r : E → F} {ℓ : ℝ} {C : Set E}
  {P : ConvexRegularization.Settings p} {ε₀ ε₁ : ℝ}
  {D : ConvexRegularization.Data E} {N : ℕ}

/-- Nonterminal iterates have residual above the global tolerance. -/
theorem Run.residual_gt (h : Run r ℓ C P ε₀ ε₁ D N) {i : ℕ} (hi : i < N) :
    ε₀ < ‖r (D.point i)‖ := lt_of_not_ge ((not_or.mp (h.continues i hi)).1)

/-- Nonterminal iterates fail the true normalized constrained measure test. -/
theorem Run.measure_gt (h : Run r ℓ C P ε₀ ε₁ D N) {i : ℕ} (hi : i < N) :
    ε₁ < firstMeasure r ℓ C (D.point i) := lt_of_not_ge ((not_or.mp (h.continues i hi)).2)

/-- Actual relative-test failure derives a legal fixed-tolerance scaled trace;
this weaker auxiliary threshold is not an additional algorithm assumption. -/
theorem Run.scaledRun (h : Run r ℓ C P ε₀ ε₁ D N) :
    ConvexRegularization.ScaledRun (powerObjective r ℓ) C P
      (ε₁ * ε₀ ^ (ℓ - 1)) D N where
  accuracy_pos := mul_pos h.accuracy_first_pos
    (Real.rpow_pos_of_pos h.accuracy_global_pos _)
  initial_parameter := h.initial_parameter
  initial_mem := h.initial_mem
  modelTrace := h.trace
  feasible_trial := h.feasible_trial
  model_test := h.model_test
  continues := by
    intro i hi
    have hn := h.accuracy_global_pos.trans (h.residual_gt hi)
    have hm := (lt_div_iff₀ (Real.rpow_pos_of_pos hn (ℓ - 1))).mp (h.measure_gt hi)
    apply lt_of_le_of_lt _ hm
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h.accuracy_global_pos.le
      (h.residual_gt hi).le (by linarith [h.residual_order])) h.accuracy_first_pos.le

/-- Every actual iterate stays in the original convex feasible region. -/
theorem Run.mem (h : Run r ℓ C P ε₀ ε₁ D N) {i : ℕ} (hi : i ≤ N) : D.point i ∈ C :=
  h.scaledRun.mem hi

/-- Every actual trial decreases or preserves the residual norm. -/
theorem Run.residual_step_le (h : Run r ℓ C P ε₀ ε₁ D N) {i : ℕ} (hi : i < N) :
    ‖r (D.point (i + 1))‖ ≤ ‖r (D.point i)‖ := by
  by_cases hs : P.eta1 ≤ D.ratio i
  · have hd := h.trace.successful_decrease hi hs
    have hp : 0 ≤ P.eta1 * P.sigmaMin / (p + 1).factorial * ‖D.step i‖ ^ (p + 1) := by
      have := P.eta1_pos
      have := P.sigmaMin_pos
      positivity
    by_contra hn
    have hm := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (not_le.mp hn).le
        (by linarith [h.residual_order] : 0 ≤ ℓ))
      (by linarith [h.residual_order] : 0 ≤ ℓ)
    change powerObjective r ℓ (D.point i) ≤ powerObjective r ℓ (D.point (i + 1)) at hm
    linarith
  · rw [h.trace.point_update i hi, ite_eq_right hs]

/-- All actual residuals remain below the initial one. -/
theorem Run.residual_le_initial (h : Run r ℓ C P ε₀ ε₁ D N) {i : ℕ} (hi : i ≤ N) :
    ‖r (D.point i)‖ ≤ ‖r (D.point 0)‖ := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (h.residual_step_le (by omega)).trans (ih (by omega))

end ConvexLeastSquares
