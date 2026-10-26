import Numlib.Optimization.HighOrder.ModelSolve.ConstrainedSharp
import Numlib.Optimization.Regularization.Constrained.ModelCriticality
import Numlib.Optimization.Regularization.HighOrder.ConstrainedOuterReturn

/-!
# Actual constrained all-order adaptive regularization executions

Actual feasible Taylor directions select the first failing order. Model steps
are genuine feasible global-gap computations with finite criticality halvings.
True criticality, radius floors, parameter caps and evaluation budgets are
consequences rather than execution fields. Zero model returns are separate
terminal branches whose true certificates are derived from global minimality.
-/

namespace ConstrainedRegularization
open Set InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed regularization settings, chosen before all requested accuracies. -/
abbrev Settings := HighOrderRegularization.Settings

/-- Actual point, step, parameter, ratio, radius and direction arrays. -/
abbrev ExecutionData := HighOrderRegularization.ExecutionData

/-- A feasible true all-order constrained Taylor certificate at legal radii. -/
def OptimalityAt {q : ℕ} (f : E → ℝ) (X : Set E) (ε : Fin q → ℝ) (x : E)
    (δ : Fin q → ℝ) : Prop := x ∈ X ∧ (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧ ∀ a,
  TaylorModel.constrainedCriticality f (modelOrder a) X x (δ a) ≤
    ε a * δ a ^ modelOrder a / (modelOrder a).factorial

/-- Passing every actual relative Taylor check certifies true constrained
optimality at the same legal radii, without any smoothness assumptions. -/
theorem optimality_of_check_none {f : E → ℝ} {X : Set E} {q : ℕ}
    {ζ : ℝ} {ε δ : Fin q → ℝ} {x : E} {direction : Fin q → E}
    {selected : Option (Fin q)}
    (h : HighOrderRegularization.ConstrainedOptimalityCheck f X ζ ε δ x direction selected)
    (hζ : 0 < ζ) (hx : x ∈ X) (hδ : ∀ a, 0 < δ a ∧ δ a ≤ 1)
    (hselected : selected = none) : OptimalityAt f X ε x δ := by
  refine ⟨hx, hδ, fun a => ?_⟩
  have hguard : ∀ b, selected = some b → a ≤ b := by
    simp only [hselected, reduceCtorEq, false_implies, implies_true]
  have hh := (h.approximation a hguard).trans (h.passed hselected a).le
  apply le_of_mul_le_mul_left (a := ζ) _ hζ
  convert hh using 1
  ring

/-- A true certificate or a literal zero model return. True optimality of the
zero return is proved from the actual positive feasible global-gap computation. -/
def TargetAt {p q : ℕ} (f : E → ℝ) (X : Set E) (_P : Settings p q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (k : ℕ) : Prop :=
  OptimalityAt f X ε (D.point k) (D.radius k) ∨
    (D.selected k ≠ none ∧ HighOrderRegularization.model f p (D.point k) (D.parameter k) 0 =
      HighOrderRegularization.model f p (D.point k) (D.parameter k) (D.step k))

/-- A finite genuine constrained detailed-solver execution. Every continued
trial strictly improves the actual model; zero decrease exits before evaluating
the trial objective. All feasible model halvings are recorded explicitly. -/
structure Run {p q : ℕ} (f : E → ℝ) (X : Set E) (P : Settings p q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (N : ℕ) : Prop where
  accuracy_pos : ∀ a, 0 < ε a
  accuracy_le_one : ∀ a, ε a ≤ 1
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_radii : ∀ a, 0 < D.radius 0 a ∧ D.radius 0 a ≤ 1
  initial_feasible : D.point 0 ∈ X
  modelTrace : HighOrderRegularization.ModelTrace f p D.point D.step D.parameter D.ratio
    P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N
  check : ∀ k ≤ N, HighOrderRegularization.ConstrainedOptimalityCheck f X P.zeta ε
    (D.radius k) (D.point k) (D.direction k) (D.selected k)
  step_two : ∀ k ≤ N, D.selected k ≠ none →
    ModelSolve.ConstrainedStepComputation
      (HighOrderRegularization.model f p (D.point k) (D.parameter k))
      (TaylorModel.feasibleDisplacements X (D.point k)) modelOrder P.theta P.zeta
      ε (D.step k) (D.solvedRadius k)
  continues : ∀ k < N, D.selected k ≠ none
  radius_update : ∀ k < N, D.radius (k + 1) =
    if P.eta1 ≤ D.ratio k then D.solvedRadius k else D.radius k

namespace Run
variable {p q : ℕ} {f : E → ℝ} {X : Set E} {P : Settings p q}
  {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- Every shorter prefix retains every actual primitive execution rule. -/
theorem restrict (h : Run f X P ε D N) {M : ℕ} (hM : M ≤ N) : Run f X P ε D M where
  accuracy_pos := h.accuracy_pos
  accuracy_le_one := h.accuracy_le_one
  initial_parameter := h.initial_parameter
  initial_radii := h.initial_radii
  initial_feasible := h.initial_feasible
  modelTrace := h.modelTrace.restrict hM
  check := fun k hk => h.check k (hk.trans hM)
  step_two := fun k hk => h.step_two k (hk.trans hM)
  continues := fun k hk => h.continues k (hk.trans_le hM)
  radius_update := fun k hk => h.radius_update k (hk.trans_le hM)

/-- Actual step feasibility and accepted/rejected updates keep every iterate
in the constraint set, including the terminal endpoint. -/
theorem point_mem (h : Run f X P ε D N) {k : ℕ} (hk : k ≤ N) : D.point k ∈ X := by
  induction k with
  | zero => exact h.initial_feasible
  | succ k ih =>
    rw [h.modelTrace.point_update k (by omega)]
    split_ifs
    · exact (h.step_two k (by omega) (h.continues k (by omega))).feasible
    · exact ih (by omega)

/-- Actual finite solver radii and accepted/rejected updates preserve legal
positive radii at every inherited endpoint. -/
theorem radius_mem (h : Run f X P ε D N) {k : ℕ} (hk : k ≤ N) (a : Fin q) :
    0 < D.radius k a ∧ D.radius k a ≤ 1 := by
  induction k with
  | zero => exact h.initial_radii a
  | succ k ih =>
    rw [h.radius_update k (by omega)]
    split_ifs
    · exact (h.step_two k (by omega) (h.continues k (by omega))).radius_mem a
    · exact ih (by omega)

/-- An observable selected-none check is a true target at the actual inherited
radii; the algorithm cannot stop by this check before certificate attainment. -/
theorem target_of_selected_none (h : Run f X P ε D N) {k : ℕ} (hk : k ≤ N)
    (hselected : D.selected k = none) : TargetAt f X P ε D k :=
  Or.inl (optimality_of_check_none (h.check k hk) P.zeta_pos
    (h.point_mem hk) (h.radius_mem hk) hselected)

end Run
end ConstrainedRegularization

namespace ConstrainedRegularization
open Set InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {X : Set E} {P : Settings p q}
  {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- Both true-certificate and literal zero-return target branches yield actual
constrained all-order optimality at positive radii. No zero-return certificate
is assumed as an execution field. -/
theorem target_optimality (h : Run f X P ε D N) (hX : IsClosed X)
    (hf : ContDiffAt ℝ p f (D.point N)) (htarget : TargetAt f X P ε D N) :
    ∃ δ : Fin q → ℝ, OptimalityAt f X ε (D.point N) δ := by
  rcases htarget with ht | ⟨hselected, hzero⟩
  · exact ⟨D.radius N, ht⟩
  · obtain ⟨μ, hμ, _, hsolve⟩ := (h.step_two N le_rfl hselected).fraction
    obtain ⟨δ, hδ, hb⟩ := HighOrderRegularization.zero_step_constrained_optimality
      P.order_le hf hX (h.point_mem le_rfl) hμ hsolve hzero ε h.accuracy_pos
    exact ⟨δ, h.point_mem le_rfl, hδ, hb⟩

end Run
end ConstrainedRegularization
