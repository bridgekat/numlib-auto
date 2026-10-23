import Numlib.Optimization.Regularization.Convex.FirstOrder
import Numlib.Optimization.Regularization.HighOrder.ParameterOn

/-!
# Primitive actual scaled-test first-order constrained regularization

The ARp1-CC trial model test uses theta times the actual step norm to degree p.
Actual model ratios, feasible trials and update intervals specify the execution;
termination and evaluation complexity are derived separately.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual scaled first-order ARp1-CC execution. Both higher tests are
disabled; model criticality is bounded by θ times the actual step norm to p.
There is no endpoint optimality or complexity conclusion in these primitive rules. -/
structure ScaledRun {p : ℕ} (f : E → ℝ) (C : Set E) (P : Settings p) (ε : ℝ)
    (D : Data E) (N : ℕ) : Prop where
  accuracy_pos : 0 < ε
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_mem : D.point 0 ∈ C
  modelTrace : ModelTrace f p D.point D.step D.parameter D.ratio
    P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N
  feasible_trial : ∀ i < N, D.point i + D.step i ∈ C
  model_test : ∀ i < N,
    constrainedCriticality (model f p (D.point i) (D.parameter i)) 1
      (feasibleDisplacements C (D.point i)) (D.step i) 1 ≤ P.theta * ‖D.step i‖ ^ p
  continues : ∀ i < N, ε < constrainedCriticality f 1 C (D.point i) 1

variable {p : ℕ} {f : E → ℝ} {C S : Set E} {P : Settings p}
  {ε L : ℝ} {D : Data E} {N : ℕ}

/-- Every actual scaled-test iterate remains feasible. -/
theorem ScaledRun.mem (h : ScaledRun f C P ε D N) {i : ℕ} (hi : i ≤ N) :
    D.point i ∈ C := by
  induction i with
  | zero => exact h.initial_mem
  | succ i ih =>
    rw [h.modelTrace.point_update i (by omega)]
    split_ifs
    · exact h.feasible_trial i (by omega)
    · exact ih (by omega)

/-- Local source regularity bounds every actual scaled-test parameter. -/
theorem ScaledRun.parameter_le (h : ScaledRun f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i ≤ N) :
    D.parameter i ≤ max P.sigmaInitial (P.gamma3 * L / (1 - P.eta2)) := by
  have hh := h.modelTrace.parameter_le_on hS hCS hC hf hL hlip
    (fun j hj => h.mem hj.le) h.feasible_trial hi
  rwa [h.initial_parameter] at hh


end ConvexRegularization
