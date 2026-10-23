import Numlib.Optimization.Regularization.Convex.CorrectedStep
import Numlib.Optimization.Regularization.Convex.FirstOrder

/-!
# Actual finite constrained regularization with enabled derivative tests

An explicit enabled-order index represents the disabled higher tests. All
objective and model measures use genuine derivative tensors and restricted
unit balls. Primitive finite execution prefixes contain no decrease, stopping
success, parameter cap or evaluation bound as an assumption.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization

/-- Fixed source settings for one, two or three constrained derivative tests. -/
structure DerivativeSettings (p : ℕ) (q : Fin 3) extends Settings p where
  enabled_order : q.val + 1 ≤ p
  tauTwo : ℝ
  thetaTwo : ℝ
  thetaThree : ℝ
  tauTwo_pos : 0 < tauTwo
  tauTwo_lt_one : tauTwo < 1
  thetaTwo_lower : (1 + tauTwo) / 2 ≤ thetaTwo
  thetaTwo_lt_one : thetaTwo < 1
  thetaThree_pos : 0 < thetaThree
  thetaThree_lt_one : thetaThree < 1

/-- The three fixed source model fractions in their derivative order. -/
def DerivativeSettings.fractions {p : ℕ} {q : Fin 3} (P : DerivativeSettings p q) :
    Fin 3 → ℝ := ![P.theta,P.thetaTwo,P.thetaThree]

/-- The first fraction agrees with the legal first-order settings. -/
@[simp] theorem DerivativeSettings.fractions_zero {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) : P.fractions 0 = P.theta := rfl

/-- The second fraction is the fixed second-order model tolerance. -/
@[simp] theorem DerivativeSettings.fractions_one {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) : P.fractions 1 = P.thetaTwo := rfl

/-- The third fraction is the fixed third-order model tolerance. -/
@[simp] theorem DerivativeSettings.fractions_two {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) : P.fractions 2 = P.thetaThree := rfl

/-- All three source model fractions are positive. -/
theorem DerivativeSettings.fractions_pos {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) (j : Fin 3) : 0 < P.fractions j := by
  fin_cases j
  · change 0 < P.theta; have := P.theta_lower; have := P.tau_pos; linarith
  · change 0 < P.thetaTwo; have := P.thetaTwo_lower; have := P.tauTwo_pos; linarith
  · exact P.thetaThree_pos

/-- Every source model fraction is strictly smaller than one. -/
theorem DerivativeSettings.fractions_lt_one {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) (j : Fin 3) : P.fractions j < 1 := by
  fin_cases j
  · exact P.theta_lt_one
  · exact P.thetaTwo_lt_one
  · exact P.thetaThree_lt_one

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual objective direction restrictions at orders one, two and three. -/
noncomputable def objectiveRestrictedDirections (f : E → ℝ) (C : Set E) (x : E)
    (a b : ℝ) : Fin 3 → Set E :=
  ![feasibleDisplacements C x,
    firstRestrictedDirections f (feasibleDisplacements C x) x a,
    secondRestrictedDirections f (feasibleDisplacements C x) x a b]

/-- Order one uses exactly the feasible endpoint displacements. -/
@[simp] theorem objectiveRestrictedDirections_zero (f : E → ℝ) (C : Set E) (x : E)
    (a b : ℝ) : objectiveRestrictedDirections f C x a b 0 = feasibleDisplacements C x := rfl

/-- Order two uses exactly the genuine first-derivative restriction. -/
@[simp] theorem objectiveRestrictedDirections_one (f : E → ℝ) (C : Set E) (x : E)
    (a b : ℝ) : objectiveRestrictedDirections f C x a b 1 =
      firstRestrictedDirections f (feasibleDisplacements C x) x a := rfl

/-- Order three retains exactly both genuine lower-derivative restrictions. -/
@[simp] theorem objectiveRestrictedDirections_two (f : E → ℝ) (C : Set E) (x : E)
    (a b : ℝ) : objectiveRestrictedDirections f C x a b 2 =
      secondRestrictedDirections f (feasibleDisplacements C x) x a b := rfl

/-- The actual objective derivative measures use the source's restricted unit balls. -/
noncomputable def objectiveDerivativeCriticality (f : E → ℝ) (C : Set E) (x : E)
    (a b : ℝ) (j : Fin 3) : ℝ :=
  tensorCriticality (iteratedFDeriv ℝ (j.val + 1) f x)
    (objectiveRestrictedDirections f C x a b j)

/-- The first actual derivative measure is the genuine constrained linear measure. -/
@[simp] theorem objectiveDerivativeCriticality_zero (f : E → ℝ) (C : Set E) (x : E)
    (a b : ℝ) : objectiveDerivativeCriticality f C x a b 0 =
      constrainedCriticality f 1 C x 1 := tensorCriticality_one f C x

/-- The second actual measure uses the source true first-derivative restriction. -/
@[simp] theorem objectiveDerivativeCriticality_one (f : E → ℝ) (C : Set E) (x : E)
    (a b : ℝ) : objectiveDerivativeCriticality f C x a b 1 =
      tensorCriticality (iteratedFDeriv ℝ 2 f x)
        (firstRestrictedDirections f (feasibleDisplacements C x) x a) := rfl

/-- The third actual measure retains both source true lower-derivative restrictions. -/
@[simp] theorem objectiveDerivativeCriticality_two (f : E → ℝ) (C : Set E) (x : E)
    (a b : ℝ) : objectiveDerivativeCriticality f C x a b 2 =
      tensorCriticality (iteratedFDeriv ℝ 3 f x)
        (secondRestrictedDirections f (feasibleDisplacements C x) x a b) := rfl

/-- The literal enabled-order stopping test uses only actual objective derivatives. -/
def derivativeStop {p : ℕ} {q : Fin 3} (f : E → ℝ) (C : Set E)
    (P : DerivativeSettings p q) (ε : Fin 3 → ℝ) (x : E) : Prop :=
  ∀ j ≤ q, objectiveDerivativeCriticality f C x (P.tau * ε 0) (P.tauTwo * ε 1) j ≤ ε j

/-- An actual ARp-CC finite execution. The continuation clause is precisely
failure of the source's enabled-order stopping test before each trial. -/
structure DerivativeRun {p : ℕ} {q : Fin 3} (f : E → ℝ) (C : Set E)
    (P : DerivativeSettings p q) (ε : Fin 3 → ℝ) (D : Data E) (N : ℕ) : Prop where
  accuracy_pos : ∀ j, 0 < ε j
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_mem : D.point 0 ∈ C
  modelTrace : ModelTrace f p D.point D.step D.parameter D.ratio
    P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N
  feasible_trial : ∀ i < N, D.point i + D.step i ∈ C
  model_test : ∀ i < N, ∀ j ≤ q,
    modelDerivativeCriticality f p C (D.point i) (D.parameter i) (D.step i)
      (P.fractions 0 * ε 0) (P.fractions 1 * ε 1) j ≤ P.fractions j * ε j
  continues : ∀ i < N, ¬derivativeStop f C P ε (D.point i)

variable {p : ℕ} {q : Fin 3} {f : E → ℝ} {C : Set E}
  {P : DerivativeSettings p q} {ε : Fin 3 → ℝ} {D : Data E} {N : ℕ}

/-- Every actual constrained derivative execution remains feasible. -/
theorem DerivativeRun.mem (h : DerivativeRun f C P ε D N) {i : ℕ} (hi : i ≤ N) :
    D.point i ∈ C := by
  induction i with
  | zero => exact h.initial_mem
  | succ i ih =>
    rw [h.modelTrace.point_update i (by omega)]
    split_ifs
    · exact h.feasible_trial i (by omega)
    · exact ih (by omega)

/-- Restricting a prefix retains the actual feasibility, model and stopping rules. -/
theorem DerivativeRun.restrict (h : DerivativeRun f C P ε D N) {M : ℕ} (hM : M ≤ N) :
    DerivativeRun f C P ε D M where
  accuracy_pos := h.accuracy_pos
  initial_parameter := h.initial_parameter
  initial_mem := h.initial_mem
  modelTrace := h.modelTrace.restrict hM
  feasible_trial := fun i hi => h.feasible_trial i (hi.trans_le hM)
  model_test := fun i hi => h.model_test i (hi.trans_le hM)
  continues := fun i hi => h.continues i (hi.trans_le hM)

/-- Before a genuine trial, at least one enabled true derivative test fails. -/
theorem DerivativeRun.exists_failed_order (h : DerivativeRun f C P ε D N)
    {i : ℕ} (hi : i < N) : ∃ j ≤ q,
      ε j < objectiveDerivativeCriticality f C (D.point i)
        (P.tau * ε 0) (P.tauTwo * ε 1) j := by
  have hh := h.continues i hi
  simp only [derivativeStop,not_forall,not_le] at hh
  obtain ⟨j,hj,hf⟩ := hh
  exact ⟨j,hj,hf⟩

/-- Rejected trials retain exactly the same actual objective data. -/
theorem DerivativeRun.rejected (h : DerivativeRun f C P ε D N) {i : ℕ} (hi : i < N)
    (hs : ¬P.eta1 ≤ D.ratio i) : D.point (i + 1) = D.point i := by
  rw [h.modelTrace.point_update i hi,ite_eq_right hs]

end ConvexRegularization
