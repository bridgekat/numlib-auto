import Numlib.Optimization.Regularization.Inexact.Run
import Numlib.Optimization.Regularization.Inexact.ParameterFunctionValues

/-!
# Operational explicit-accuracy high-order regularization executions

The trace includes the actual ordered Step1 radius loops, explicit stopping budgets,
Step2 model solves, both approximate objective values,
literal short-step request guard, objective ratio, point and radius updates,
parameter updates and accuracy-only branches. No true optimality, radius floor,
objective decrease or complexity bound is a field of the execution.
-/

namespace InexactRegularization.Explicit
open Set InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed EDA settings include known unit oracle bounds and the source
quarter-margin restrictions for both approximate objective evaluations. -/
structure Settings (p q : ℕ) extends InexactRegularization.Settings p q where
  known_error_bound : errorBound = 1
  function_acceptance_margin : stepCoefficient ≤ eta1 / 4
  function_success_margin : stepCoefficient ≤ (1 - eta2) / 4

/-- The actual arrays computed by an inexact high-order regularization
execution. Mathematical and operational requirements belong to `Run`. -/
structure ExecutionData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℕ)
    extends InexactRegularization.ExecutionData E q where
  functionStart : ℕ → ℝ
  functionTrial : ℕ → ℝ
  functionRequest : ℕ → ℝ

/-- The literal explicit termination test: all computed tests passed and every
actual finite tensor-error budget is small enough for certification. -/
def StopsAt {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (k : ℕ) : Prop :=
  D.selected k = none ∧ ∀ a : Fin q,
    tensorErrorBudget (D.accuracy k) (modelOrder a) (D.checkedRadius k a) ≤
      P.zeta / 2 * ε a * D.checkedRadius k a ^ modelOrder a / (modelOrder a).factorial

/-- A finite actual ARqpEDA execution. Step1's selected order and the literal
all-degree request guard determine whether an iteration proceeds to a trial.
The endpoint includes its completed optimality check and derivative data.
Accuracy-only iterations restore the inherited radii. Rejected trials reuse
unchanged derivative data, as specified by the source evaluation schedule. -/
structure Run {p q : ℕ} (f : E → ℝ) (P : Settings p q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (N : ℕ) : Prop where
  accuracy_pos : ∀ a, 0 < ε a
  accuracy_le_one : ∀ a, ε a ≤ 1
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_radii : ∀ a, ε a ≤ D.startRadius 0 a ∧ D.startRadius 0 a ≤ 1
  updates : TrialRegularizationUpdates D.trials D.parameter D.ratio P.eta1 P.eta2
    P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N
  initial_accuracy : ∀ i, 1 ≤ i → i ≤ p → D.accuracy 0 i ∈ Icc 0 P.initialCap
  accuracy_trial : ∀ k < N, k ∈ D.trials → ∀ i, 1 ≤ i → i ≤ p →
    D.accuracy (k + 1) i = D.accuracy k i
  accuracy_improvement : ∀ k < N, k ∉ D.trials → ∀ i, 1 ≤ i → i ≤ p →
    D.accuracy (k + 1) i = P.reduction * D.accuracy k i
  oracle_all : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p →
    ‖D.jet k i - iteratedFDeriv ℝ i f (D.point k)‖ ≤
      P.errorCoefficient i * D.accuracy k i
  constant_value : ∀ k < N, k ∈ D.trials →
    D.jet k 0 (fun _ => 0) = D.functionStart k
  error_initial : ∀ k < N, k ∈ D.trials →
    |D.functionStart k - f (D.point k)| ≤ D.functionRequest k
  error_trial : ∀ k < N, k ∈ D.trials →
    |D.functionTrial k - f (D.point k + D.step k)| ≤ D.functionRequest k
  request_positive : ∀ k < N, k ∈ D.trials → 0 < D.functionRequest k
  relative_request : ∀ k < N, k ∈ D.trials →
    D.functionRequest k ≤ P.stepCoefficient * TaylorModel.jetDecrement (D.jet k) p (D.step k)
  no_exit : ∀ k < N, ¬StopsAt P ε D k
  step_one : ∀ k ≤ N, StepOneComputation (D.jet k) p (D.parameter k) P.zeta ε
    (D.startRadius k) (D.checkedRadius k) (D.reference k)
    (D.checkDirection k) (D.checkCount k) (D.selected k)
  step_two : ∀ k < N, D.selected k ≠ none →
    StepTwoComputation (D.jet k) p modelOrder (D.parameter k) P.theta P.zeta ε
      (D.reference k) (D.checkedRadius k) (D.step k) (D.solvedRadius k)
  trial_rule : ∀ k < N, k ∈ D.trials ↔ D.selected k ≠ none ∧
    (1 ≤ ‖D.step k‖ ∨ ∀ i, 1 ≤ i → i ≤ p →
      D.accuracy k i ≤ P.stepCoefficient * ‖D.step k‖ ^ (p - i + 1))
  ratio : ∀ k < N, k ∈ D.trials → D.ratio k =
    (D.functionStart k - D.functionTrial k) / TaylorModel.jetDecrement (D.jet k) p (D.step k)
  point_trial : ∀ k < N, k ∈ D.trials →
    D.point (k + 1) = if P.eta1 ≤ D.ratio k then D.point k + D.step k else D.point k
  point_inactive : ∀ k < N, k ∉ D.trials → D.point (k + 1) = D.point k
  radius_trial : ∀ k < N, k ∈ D.trials → D.startRadius (k + 1) =
    if P.eta1 ≤ D.ratio k ∧ ‖D.step k‖ < 1 then D.solvedRadius k else D.checkedRadius k
  radius_inactive : ∀ k < N, k ∉ D.trials → D.startRadius (k + 1) = D.startRadius k
  derivative_reuse : ∀ k < N, k ∈ D.trials → ¬P.eta1 ≤ D.ratio k →
    ∀ i, 1 ≤ i → i ≤ p → D.jet (k + 1) i = D.jet k i

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every inherited radius remains positive and at most one under actual
Step1, Step2 and accepted/rejected/accuracy-only radius updates. -/
theorem startRadius_mem (h : Run f P ε D N) {k : ℕ} (hk : k ≤ N) :
    ∀ a, 0 < D.startRadius k a ∧ D.startRadius k a ≤ 1 := by
  classical
  induction k with
  | zero => intro a; exact ⟨(h.accuracy_pos a).trans_le (h.initial_radii a).1,
      (h.initial_radii a).2⟩
  | succ k ih =>
    have hprev := ih (by omega)
    have hchecked : ∀ a, 0 < D.checkedRadius k a ∧ D.checkedRadius k a ≤ 1 :=
      fun a => ⟨((h.step_one k (by omega)).radius_bounds hprev a).1,
        ((h.step_one k (by omega)).radius_bounds hprev a).2.2⟩
    by_cases ht : k ∈ D.trials
    · rw [h.radius_trial k (by omega) ht]
      split_ifs with hsuccess
      · exact ((h.step_two k (by omega) ((h.trial_rule k (by omega)).mp ht).1)).radius_mem
          hchecked
      · exact hchecked
    · rw [h.radius_inactive k (by omega) ht]
      exact hprev

/-- Actual Step1 outputs inherit positive radii bounded by one. -/
theorem checkedRadius_mem (h : Run f P ε D N) {k : ℕ} (hk : k ≤ N) (a : Fin q) :
    0 < D.checkedRadius k a ∧ D.checkedRadius k a ≤ 1 :=
  ⟨((h.step_one k hk).radius_bounds (h.startRadius_mem hk) a).1,
    ((h.step_one k hk).radius_bounds (h.startRadius_mem hk) a).2.2⟩

/-- A genuine execution supplies the shared EDA oracle/function trace. Reference
improvement and the all-degree guarded requests are derived from its actual
Step1 and Step2 components rather than postulated again. -/
theorem toFunctionTrace (h : Run f P ε D N) :
    FunctionTrace f p P.toOracleSettings D.jet D.trials D.point D.reference D.step D.accuracy
      D.parameter D.ratio D.functionStart D.functionTrial D.functionRequest
      P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N := by
  refine {
    order_pos := P.order_pos.trans_le P.order_le
    updates := h.updates
    initial_accuracy := h.initial_accuracy
    accuracy_trial := h.accuracy_trial
    accuracy_improvement := h.accuracy_improvement
    oracle := fun k hk _ i hi hip => h.oracle_all k hk.le i hi hip
    short_request := ?_
    reference_improvement := ?_
    comparison := fun k hk ht => (h.step_two k hk ((h.trial_rule k hk).mp ht).1).comparison
    point_update := h.point_trial
    point_inactive := h.point_inactive
    constant_value := h.constant_value
    error_initial := h.error_initial
    error_trial := h.error_trial
    request_positive := h.request_positive
    relative_request := h.relative_request
    ratio := h.ratio }
  · intro k hk ht hs
    rcases ((h.trial_rule k hk).mp ht).2 with hlarge | hrequests
    · exact (not_lt_of_ge hlarge hs).elim
    · exact hrequests
  · intro k hk ht
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp ((h.trial_rule k hk).mp ht).1
    have hone := h.step_one k hk.le
    rw [ha] at hone
    exact hone.reference_improvement P.zeta_pos (h.accuracy_pos a) (h.startRadius_mem hk.le)

/-- Restrict an actual inexact regularization execution to an earlier finite
prefix, retaining the same computed data and algorithm settings. -/
theorem restrict (h : Run f P ε D N) {n : ℕ} (hn : n ≤ N) : Run f P ε D n := by
  exact { h with
    updates := { h.updates with
      update := fun k hk => h.updates.update k (hk.trans_le hn)
      inactive := fun k hk => h.updates.inactive k (hk.trans_le hn) }
    accuracy_trial := fun k hk => h.accuracy_trial k (hk.trans_le hn)
    accuracy_improvement := fun k hk => h.accuracy_improvement k (hk.trans_le hn)
    oracle_all := fun k hk => h.oracle_all k (hk.trans hn)
    constant_value := fun k hk => h.constant_value k (hk.trans_le hn)
    error_initial := fun k hk => h.error_initial k (hk.trans_le hn)
    error_trial := fun k hk => h.error_trial k (hk.trans_le hn)
    request_positive := fun k hk => h.request_positive k (hk.trans_le hn)
    relative_request := fun k hk => h.relative_request k (hk.trans_le hn)
    no_exit := fun k hk => h.no_exit k (hk.trans_le hn)
    step_one := fun k hk => h.step_one k (hk.trans hn)
    step_two := fun k hk => h.step_two k (hk.trans_le hn)
    trial_rule := fun k hk => h.trial_rule k (hk.trans_le hn)
    ratio := fun k hk => h.ratio k (hk.trans_le hn)
    point_trial := fun k hk => h.point_trial k (hk.trans_le hn)
    point_inactive := fun k hk => h.point_inactive k (hk.trans_le hn)
    radius_trial := fun k hk => h.radius_trial k (hk.trans_le hn)
    radius_inactive := fun k hk => h.radius_inactive k (hk.trans_le hn)
    derivative_reuse := fun k hk => h.derivative_reuse k (hk.trans_le hn) }

/-- Every actual trial has a nonzero step because its selected Step1 reference
strictly improves the actual model and Step2 attains at least that improvement. -/
theorem step_nonzero (h : Run f P ε D N) {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) :
    D.step k ≠ 0 :=
  (h.step_two k hk ((h.trial_rule k hk).mp ht).1).nonzero
    (h.toFunctionTrace.toOracleTrace.reference_improvement k hk ht)

/-- Actual request updates preserve nonnegativity and the initial cap at every
endpoint, including accuracy-only iterations. -/
theorem accuracy_mem (h : Run f P ε D N) {k i : ℕ} (hk : k ≤ N)
    (hi : 1 ≤ i) (hip : i ≤ p) : D.accuracy k i ∈ Icc 0 P.initialCap :=
  h.toFunctionTrace.toOracleTrace.accuracy_mem_Icc hk hi hip

/-- Actual lower-derivative Lipschitz bounds and primitive oracle guarantees
bound every supplied positive-order derivative tensor uniformly. -/
theorem tensor_norm_le (h : Run f P ε D N) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ i, i < p → ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖)
    {k i : ℕ} (hk : k ≤ N) (hi : 1 ≤ i) (hip : i ≤ p) :
    ‖D.jet k i‖ ≤ L + P.errorBound * P.initialCap := by
  exact TaylorModel.norm_jet_le_of_lipschitz_oracle hL P.initialCap_nonneg hlip
    (D.jet k) (D.point k) P.errorCoefficient (D.accuracy k)
    (fun a ha hap => ⟨P.errorCoefficient_nonneg a ha hap, P.errorCoefficient_le a ha hap⟩)
    (fun a ha hap => (h.accuracy_mem hk ha hap).2) (h.oracle_all k hk) hi hip

/-- The literal guarded execution has the corrected uniform parameter bound,
including the initial and terminal endpoints. -/
theorem parameter_le (h : Run f P ε D N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y,
      ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖)
    {k : ℕ} (hk : k ≤ N) :
    D.parameter k ≤ max P.sigmaInitial
      (P.gamma3 * parameterCoefficient P.toOracleSettings L / (1 - P.eta2)) := by
  simpa only [h.initial_parameter] using
    h.toFunctionTrace.parameter_le hf hL hlip P.function_success_margin hk

end Run
end InexactRegularization.Explicit

namespace InexactRegularization.Explicit
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Known unit oracle bounds give the actual EDA error request for every
positive-order derivative, including the current endpoint. -/
theorem oracle_le_request (h : Run f P ε D N) {k i : ℕ} (hk : k ≤ N)
    (hi : 1 ≤ i) (hip : i ≤ p) :
    ‖D.jet k i - iteratedFDeriv ℝ i f (D.point k)‖ ≤ D.accuracy k i := by
  have hc : P.errorCoefficient i ≤ 1 := by
    simpa only [P.known_error_bound] using P.errorCoefficient_le i hi hip
  exact (h.oracle_all k hk i hi hip).trans
    (mul_le_of_le_one_left (h.accuracy_mem hk hi hip).1 hc)

variable [ProperSpace E]

/-- The literal explicit stopping test certifies true all-order objective
criticality at the actual checked radius vector. -/
theorem stopped_optimality (h : Run f P ε D N) {k : ℕ} (hk : k ≤ N)
    (hstop : StopsAt P ε D k) :
    (∀ a, 0 < D.checkedRadius k a ∧ D.checkedRadius k a ≤ 1) ∧
      ∀ a, TaylorModel.criticality f (modelOrder a) (D.point k) (D.checkedRadius k a) ≤
        ε a * D.checkedRadius k a ^ modelOrder a / (modelOrder a).factorial := by
  have hone := h.step_one k hk
  rw [hstop.1] at hone
  refine ⟨h.checkedRadius_mem hk, ?_⟩
  exact hone.true_optimality P.zeta_pos P.zeta_le_one h.accuracy_pos (h.startRadius_mem hk)
    (D.accuracy k) hstop.2 f (D.point k)
    (fun i hi hiq => h.oracle_le_request hk hi (hiq.trans P.order_le))

end Run
end InexactRegularization.Explicit
