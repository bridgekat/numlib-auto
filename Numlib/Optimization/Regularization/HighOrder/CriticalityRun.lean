import Numlib.Optimization.HighOrder.ModelSolve.ComputationSharp
import Numlib.Optimization.Regularization.HighOrder.Parameter
import Numlib.Optimization.Regularization.HighOrder.StepTwoTermination
import Numlib.Optimization.TrustRegion.Inexact.Selection

/-!
# Primitive exact high-order adaptive regularization executions

Actual ordered objective Taylor tests, actual approximate-global model solves,
finite changing-candidate radius loops, objective ratios, accepted point and
radius updates and parameter intervals specify the computation. Zero model
decrease is a terminal branch. No positive decrease floor or complexity bound
is a field of the execution.
-/

namespace HighOrderRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed exact high-order regularization settings, before all accuracies. -/
structure Settings (p q : ℕ) where
  order_pos : 0 < q
  order_le : q ≤ p
  zeta : ℝ
  zeta_pos : 0 < zeta
  zeta_le_one : zeta ≤ 1
  theta : ℝ
  theta_pos : 0 < theta
  theta_lt_one : theta < 1
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  sigmaMin : ℝ
  sigmaInitial : ℝ
  eta1_pos : 0 < eta1
  eta1_le_eta2 : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma1_lt_one : gamma1 < 1
  one_lt_gamma2 : 1 < gamma2
  gamma2_lt_gamma3 : gamma2 < gamma3
  sigmaMin_pos : 0 < sigmaMin
  sigmaMin_le_initial : sigmaMin ≤ sigmaInitial

/-- An actual ordered objective optimality check. Only orders through the
first failing order need computed feasible approximate criticality directions. -/
structure OptimalityCheck (f : E → ℝ) {q : ℕ} (ζ : ℝ) (ε δ : Fin q → ℝ)
    (x : E) (direction : Fin q → E) (selected : Option (Fin q)) : Prop where
  feasible : ∀ a, (∀ b, selected = some b → a ≤ b) → ‖direction a‖ ≤ δ a
  approximation : ∀ a, (∀ b, selected = some b → a ≤ b) →
    ζ * TaylorModel.criticality f (modelOrder a) x (δ a) ≤
      TaylorModel.decrement f (modelOrder a) x (direction a)
  passed : selected = none → ∀ a, TaylorModel.decrement f (modelOrder a) x (direction a) <
    ζ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial
  failed : ∀ a, selected = some a →
    ζ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial ≤
      TaylorModel.decrement f (modelOrder a) x (direction a)
  earlier_passed : ∀ a, selected = some a → ∀ b < a,
    TaylorModel.decrement f (modelOrder b) x (direction b) <
      ζ * ε b * δ b ^ modelOrder b / (modelOrder b).factorial

/-- Computed arrays for an exact regularization execution. -/
structure ExecutionData (E : Type*) (q : ℕ) where
  point : ℕ → E
  step : ℕ → E
  parameter : ℕ → ℝ
  ratio : ℕ → ℝ
  radius : ℕ → Fin q → ℝ
  solvedRadius : ℕ → Fin q → ℝ
  direction : ℕ → Fin q → E
  selected : ℕ → Option (Fin q)

/-- A finite actual execution prefix, including its endpoint optimality check
and any endpoint zero-decrease model solve. Nonterminal trials strictly improve
the model because the literal zero-decrease branch terminates before evaluation
of a trial objective. All radius reductions record their actual primitive tests. -/
structure Run {p q : ℕ} (f : E → ℝ) (P : Settings p q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (N : ℕ) : Prop where
  accuracy_pos : ∀ a, 0 < ε a
  accuracy_le_one : ∀ a, ε a ≤ 1
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_radii : ∀ a, 0 < D.radius 0 a ∧ D.radius 0 a ≤ 1
  modelTrace : ModelTrace f p D.point D.step D.parameter D.ratio P.eta1 P.eta2
    P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N
  check : ∀ k ≤ N, OptimalityCheck f P.zeta ε (D.radius k) (D.point k)
    (D.direction k) (D.selected k)
  step_two : ∀ k ≤ N, D.selected k ≠ none →
    ModelSolve.StepComputation (model f p (D.point k) (D.parameter k))
      modelOrder P.theta P.zeta ε (D.step k) (D.solvedRadius k)
  continues : ∀ k < N, D.selected k ≠ none
  radius_update : ∀ k < N, D.radius (k + 1) =
    if P.eta1 ≤ D.ratio k then D.solvedRadius k else D.radius k

/-- True all-order approximate optimality at a specified legal radius vector. -/
def OptimalityAt {q : ℕ} (f : E → ℝ) (ε : Fin q → ℝ) (x : E)
    (δ : Fin q → ℝ) : Prop :=
  (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧ ∀ a,
    TaylorModel.criticality f (modelOrder a) x (δ a) ≤
      ε a * δ a ^ modelOrder a / (modelOrder a).factorial

/-- A target is either true optimality at the actual inherited radii or the
literal zero-decrease model-solve exit. The latter's true optimality is derived. -/
def TargetAt {p q : ℕ} (f : E → ℝ) (_P : Settings p q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (k : ℕ) : Prop :=
  OptimalityAt f ε (D.point k) (D.radius k) ∨
    (D.selected k ≠ none ∧ model f p (D.point k) (D.parameter k) 0 =
      model f p (D.point k) (D.parameter k) (D.step k))

/-- A passed actual objective check implies true approximate optimality. -/
theorem OptimalityCheck.optimality_of_none {f : E → ℝ} {q : ℕ} {ζ : ℝ}
    {ε δ : Fin q → ℝ} {x : E} {direction : Fin q → E} {selected : Option (Fin q)}
    (h : OptimalityCheck f ζ ε δ x direction selected) (hζ : 0 < ζ)
    (hδ : ∀ a, 0 < δ a ∧ δ a ≤ 1) (hselected : selected = none) :
    OptimalityAt f ε x δ := by
  refine ⟨hδ, fun a => ?_⟩
  have hguard : ∀ b, selected = some b → a ≤ b := by simp only [hselected, reduceCtorEq,
    false_implies, implies_true]
  have hh := (h.approximation a hguard).trans (h.passed hselected a).le
  apply le_of_mul_le_mul_left (a := ζ) _ hζ
  convert hh using 1
  ring

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every shorter prefix retains exactly the same primitive execution rules. -/
theorem restrict (h : Run f P ε D N) {M : ℕ} (hM : M ≤ N) : Run f P ε D M where
  accuracy_pos := h.accuracy_pos
  accuracy_le_one := h.accuracy_le_one
  initial_parameter := h.initial_parameter
  initial_radii := h.initial_radii
  modelTrace := h.modelTrace.restrict hM
  check := fun k hk => h.check k (hk.trans hM)
  step_two := fun k hk => h.step_two k (hk.trans hM)
  continues := fun k hk => h.continues k (hk.trans_le hM)
  radius_update := fun k hk => h.radius_update k (hk.trans_le hM)

/-- Every actual inherited radius is positive and at most one. -/
theorem radius_mem (h : Run f P ε D N) {k : ℕ} (hk : k ≤ N) (a : Fin q) :
    0 < D.radius k a ∧ D.radius k a ≤ 1 := by
  induction k with
  | zero => exact h.initial_radii a
  | succ k ih =>
    have hkN : k < N := by omega
    rw [h.radius_update k hkN]
    split_ifs
    · exact (h.step_two k hkN.le (h.continues k hkN)).radius_mem a
    · exact ih hkN.le

/-- A passed endpoint check already supplies an actual-radius target. -/
theorem target_of_none (h : Run f P ε D N) {k : ℕ} (hk : k ≤ N)
    (hselected : D.selected k = none) : TargetAt f P ε D k :=
  Or.inl ((h.check k hk).optimality_of_none P.zeta_pos (h.radius_mem hk) hselected)

end Run
end HighOrderRegularization
