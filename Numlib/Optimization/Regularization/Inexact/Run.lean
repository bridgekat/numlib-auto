import Numlib.Optimization.Regularization.Inexact.StepOne
import Numlib.Optimization.Regularization.Inexact.StepTwoBounds

/-!
# Operational executions of inexact high-order regularization

The trace includes the actual ordered Step1 radius loops, Step2 model solves,
literal short-step request guard, objective ratio, point and radius updates,
parameter updates and accuracy-only branches. No true optimality, radius floor,
objective decrease or complexity bound is a field of the execution.
-/

namespace InexactRegularization
open Set InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed settings of inexact high-order regularization, independent of all
requested optimality accuracies and computed execution data. -/
structure Settings (p q : ℕ) extends OracleSettings p where
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

/-- The actual arrays computed by an inexact high-order regularization
execution. Mathematical and operational requirements belong to `Run`. -/
structure ExecutionData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℕ) where
  jet : ℕ → FormalMultilinearSeries ℝ E ℝ
  trials : Set ℕ
  point : ℕ → E
  reference : ℕ → E
  step : ℕ → E
  parameter : ℕ → ℝ
  ratio : ℕ → ℝ
  accuracy : ℕ → ℕ → ℝ
  startRadius : ℕ → Fin q → ℝ
  checkedRadius : ℕ → Fin q → ℝ
  solvedRadius : ℕ → Fin q → ℝ
  checkDirection : ℕ → Fin q → ℕ → E
  checkCount : ℕ → Fin q → ℕ
  selected : ℕ → Option (Fin q)

/-- A finite actual ARqpIDA execution. Step1's selected order and the literal
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
  exact_value : ∀ k ≤ N, D.jet k 0 (fun _ => 0) = f (D.point k)
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
    InexactRegularization.ratio f (D.jet k) p (D.point k) (D.step k)
  point_trial : ∀ k < N, k ∈ D.trials →
    D.point (k + 1) = if P.eta1 ≤ D.ratio k then D.point k + D.step k else D.point k
  point_inactive : ∀ k < N, k ∉ D.trials → D.point (k + 1) = D.point k
  radius_trial : ∀ k < N, k ∈ D.trials → D.startRadius (k + 1) =
    if P.eta1 ≤ D.ratio k ∧ ‖D.step k‖ < 1 then D.solvedRadius k else D.checkedRadius k
  radius_inactive : ∀ k < N, k ∉ D.trials → D.startRadius (k + 1) = D.startRadius k
  jet_reuse : ∀ k < N, k ∈ D.trials → ¬P.eta1 ≤ D.ratio k → D.jet (k + 1) = D.jet k

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

/-- A genuine execution supplies the shared IDA oracle/model trace. Reference
improvement and the all-degree guarded requests are derived from its actual
Step1 and Step2 components rather than postulated again. -/
theorem toModelTrace (h : Run f P ε D N) :
    ModelTrace f p P.toOracleSettings D.jet D.trials D.point D.reference D.step D.accuracy
      D.parameter D.ratio P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N := by
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
    exact_value := fun k hk _ => h.exact_value k hk.le
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
    exact_value := fun k hk => h.exact_value k (hk.trans hn)
    step_one := fun k hk => h.step_one k (hk.trans hn)
    step_two := fun k hk => h.step_two k (hk.trans_le hn)
    trial_rule := fun k hk => h.trial_rule k (hk.trans_le hn)
    ratio := fun k hk => h.ratio k (hk.trans_le hn)
    point_trial := fun k hk => h.point_trial k (hk.trans_le hn)
    point_inactive := fun k hk => h.point_inactive k (hk.trans_le hn)
    radius_trial := fun k hk => h.radius_trial k (hk.trans_le hn)
    radius_inactive := fun k hk => h.radius_inactive k (hk.trans_le hn)
    jet_reuse := fun k hk => h.jet_reuse k (hk.trans_le hn) }

/-- Every actual trial has a nonzero step because its selected Step1 reference
strictly improves the actual model and Step2 attains at least that improvement. -/
theorem step_nonzero (h : Run f P ε D N) {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) :
    D.step k ≠ 0 :=
  (h.step_two k hk ((h.trial_rule k hk).mp ht).1).nonzero
    (h.toModelTrace.reference_improvement k hk ht)

/-- Actual request updates preserve nonnegativity and the initial cap at every
endpoint, including accuracy-only iterations. -/
theorem accuracy_mem (h : Run f P ε D N) {k i : ℕ} (hk : k ≤ N)
    (hi : 1 ≤ i) (hip : i ≤ p) : D.accuracy k i ∈ Icc 0 P.initialCap :=
  h.toModelTrace.toOracleTrace.accuracy_mem_Icc hk hi hip

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
  simpa only [h.initial_parameter] using h.toModelTrace.parameter_le hf hL hlip hk

end Run
end InexactRegularization
