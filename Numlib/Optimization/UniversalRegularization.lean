import Numlib.Optimization.HolderPowerTaylor
import Numlib.Optimization.HessianCurvature
import Numlib.Optimization.ParameterUpdates
import Mathlib.Order.Interval.Finset.Nat

/-!
# Universal adaptive regularization with real powers

A legal prefix uses the actual Taylor model, checks criticality at every trial point, and
requires both ratio and length tests for acceptance. Rejection is their logical complement.
The parameter is positive but has no fixed positive floor. A complete finite run separately
records the first stopping trial; the interface does not assert that every prefix terminates.
Oracle schedules charge active derivatives at every trial and reuse the other derivatives
at rejected iterates.
-/

noncomputable section
namespace Optimization.UniversalRegularization
open RegularizedTaylorModel

/-- Algorithm parameters for first- or second-order universal regularization. The active
order `q` encodes whether the second tolerance is finite. Smoothness is unknown to them. -/
structure Parameters (q p : ℕ) (r : ℝ) where
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  theta : Fin 2 → ℝ
  alpha : Fin 2 → ℝ
  epsilon : Fin 2 → ℝ
  order_pos : 1 ≤ q
  order_le_two : q ≤ 2
  degree_ge_order : q ≤ p
  power_gt_degree : (p : ℝ) < r
  eta1_pos : 0 < eta1
  eta1_le_eta2 : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma1_lt_one : gamma1 < 1
  gamma2_gt_one : 1 < gamma2
  gamma2_lt_gamma3 : gamma2 < gamma3
  theta_pos : ∀ i, 0 < theta i
  theta_le_one : ∀ i, theta i ≤ 1
  alpha_pos : ∀ i, 0 < alpha i
  alpha_le : ∀ i, alpha i ≤ min 1 (Real.powerFactorial (r - (i.val + 1))) / 3
  epsilon_pos : ∀ i, i.val < q → 0 < epsilon i
  epsilon_le_one : ∀ i, i.val < q → epsilon i ≤ 1

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {q p : ℕ} {r : ℝ}

/-- The actual Taylor polynomial plus its finite-product normalized radial real power. -/
def model (f : E → ℝ) (p : ℕ) (x : E) (sigma r : ℝ) (s : E) : ℝ :=
  regularizedModel f p x sigma (Real.powerFactorial r) r s

/-- The actual ratio of objective reduction to Taylor reduction. Strict model decrease
and positive regularization make its denominator positive on every legal computed step. -/
def ratio (f : E → ℝ) (p : ℕ) (x s : E) : ℝ :=
  (f x - f (x + s)) / (taylorModel f p x 0 - taylorModel f p x s)

/-- First-order stopping and the activated second-order curvature condition. The source's
strict-positive-curvature alternative is included in this equivalent combined test. -/
def Stationary (a : Parameters q p r) (f : E → ℝ) (z : E) : Prop :=
  ‖fderiv ℝ f z‖ ≤ a.epsilon 0 ∧
    (2 ≤ q → -a.epsilon 1 ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) z))

/-- The actual computed step strictly decreases the model and satisfies every activated
first- and second-derivative model residual. -/
structure ComputedStep (a : Parameters q p r) (f : E → ℝ) (x : E) (sigma : ℝ)
    (s : E) : Prop where
  decrease : model f p x sigma r s < model f p x sigma r 0
  first : ‖fderiv ℝ (model f p x sigma r) s‖ ≤ a.theta 0 * ‖s‖ ^ (r - 1)
  second : 2 ≤ q → -(a.theta 1 * ‖s‖ ^ (r - 2)) ≤
    leastCurvature (fderiv ℝ (fderiv ℝ (model f p x sigma r)) s)

/-- Every activated step-length test at the actual trial point. -/
def LongStep (a : Parameters q p r) (f : E → ℝ) (x : E) (sigma : ℝ) (s : E) : Prop :=
  a.alpha 0 * ‖fderiv ℝ f (x + s)‖ ≤ sigma * ‖s‖ ^ (r - 1) ∧
    (2 ≤ q → -a.alpha 1 * leastCurvature (fderiv ℝ (fderiv ℝ f) (x + s)) ≤
      sigma * ‖s‖ ^ (r - 2))

/-- Acceptance requires the ratio and every activated step-length test. -/
def Accepted (a : Parameters q p r) (f : E → ℝ) (x : E) (sigma : ℝ) (s : E) : Prop :=
  a.eta1 ≤ ratio f p x s ∧ LongStep a f x sigma s

/-- Very successful trials meet the higher ratio threshold and every length test. -/
def VerySuccessful (a : Parameters q p r) (f : E → ℝ) (x : E) (sigma : ℝ)
    (s : E) : Prop := a.eta2 ≤ ratio f p x s ∧ LongStep a f x sigma s

/-- The rejection branch is the logical OR of ratio failure and active length-test failure.
This resolves the conjunction misprint in the transcribed update rule. -/
theorem not_accepted_iff (a : Parameters q p r) (f : E → ℝ) (x : E) (sigma : ℝ) (s : E) :
    ¬Accepted a f x sigma s ↔ ratio f p x s < a.eta1 ∨
      sigma * ‖s‖ ^ (r - 1) < a.alpha 0 * ‖fderiv ℝ f (x + s)‖ ∨
      (2 ≤ q ∧ sigma * ‖s‖ ^ (r - 2) <
        -a.alpha 1 * leastCurvature (fderiv ℝ (fderiv ℝ f) (x + s))) := by
  simp only [Accepted, LongStep, not_and_or, not_le, not_forall, exists_prop]

/-- All three legal closed update intervals, including the nonincrease interval after a very
successful trial. Rejection includes ratio failure or any active length-test failure. -/
def LegalUpdate (a : Parameters q p r) (f : E → ℝ) (x s : E) (sigma next : ℝ) : Prop :=
  (VerySuccessful a f x sigma s → next ∈ Set.Icc (a.gamma1 * sigma) sigma) ∧
  (Accepted a f x sigma s → ¬VerySuccessful a f x sigma s →
    next ∈ Set.Icc sigma (a.gamma2 * sigma)) ∧
  (¬Accepted a f x sigma s → next ∈ Set.Icc (a.gamma2 * sigma) (a.gamma3 * sigma))

/-- The initial criticality test is at `x 0`; test `k+1` is at the actual trial `x k+s k`. -/
def observation (x s : ℕ → E) : ℕ → E
  | 0 => x 0
  | k + 1 => x k + s k

omit [InnerProductSpace ℝ E] in
/-- The initial observation is the given initial point. -/
@[simp] theorem observation_zero (x s : ℕ → E) : observation x s 0 = x 0 := rfl

omit [InnerProductSpace ℝ E] in
/-- Every later observation is a trial point, including after rejected trials. -/
@[simp] theorem observation_succ (x s : ℕ → E) (k : ℕ) :
    observation x s (k + 1) = x k + s k := rfl

open Classical in
/-- A finite prefix of fully processed, nonterminal trials. No continuation, positive
parameter floor, termination bound or complexity estimate is assumed. -/
structure RunPrefix (a : Parameters q p r) (f : E → ℝ) (x s : ℕ → E)
    (sigma : ℕ → ℝ) (N : ℕ) : Prop where
  initial_positive : 0 < sigma 0
  computed : ∀ k < N, ComputedStep a f (x k) (sigma k) (s k)
  nonterminal : ∀ i ≤ N, ¬Stationary a f (observation x s i)
  iterate : ∀ k < N, x (k + 1) = if Accepted a f (x k) (sigma k) (s k)
    then x k + s k else x k
  update : ∀ k < N, LegalUpdate a f (x k) (s k) (sigma k) (sigma (k + 1))

/-- A complete finite execution either stops initially or after its first stationary trial.
The terminal trial is checked before function evaluation, acceptance and parameter update. -/
def IsRun (a : Parameters q p r) (f : E → ℝ) (x s : ℕ → E) (sigma : ℕ → ℝ)
    (N : ℕ) : Prop :=
  0 < sigma 0 ∧ ((N = 0 ∧ Stationary a f (x 0)) ∨
    ∃ M, N = M + 1 ∧ RunPrefix a f x s sigma M ∧
      ComputedStep a f (x M) (sigma M) (s M) ∧ Stationary a f (observation x s N))

variable {a : Parameters q p r} {f : E → ℝ} {x s : ℕ → E} {sigma : ℕ → ℝ} {N : ℕ}

/-- Every legal update preserves positivity without imposing a uniform positive floor. -/
theorem LegalUpdate.positive {z t : E} {u v : ℝ}
    (h : LegalUpdate a f z t u v) (hu : 0 < u) : 0 < v := by
  classical
  by_cases hv : VerySuccessful a f z u t
  · exact (mul_pos a.gamma1_pos hu).trans_le (h.1 hv).1
  · by_cases ha : Accepted a f z u t
    · exact hu.trans_le (h.2.1 ha hv).1
    · exact (mul_pos (by linarith [a.gamma2_gt_one]) hu).trans_le (h.2.2 ha).1

/-- Every parameter reached by a finite legal prefix is positive. -/
theorem RunPrefix.positive (h : RunPrefix a f x s sigma N) {k : ℕ} (hk : k ≤ N) :
    0 < sigma k := by
  induction k with
  | zero => exact h.initial_positive
  | succ k ih => exact (h.update k (by omega)).positive (ih (by omega))

/-- Strict decrease excludes a zero computed step. -/
theorem ComputedStep.step_ne_zero {z t : E} {u : ℝ} (h : ComputedStep a f z u t) : t ≠ 0 := by
  intro ht
  have hd := h.decrease
  rw [ht] at hd
  exact lt_irrefl _ hd

/-- Every computed trial pays its complete real-power regularization in Taylor decrease. -/
theorem ComputedStep.predicted_decrease {z t : E} {u : ℝ}
    (h : ComputedStep a f z u t) :
    u / Real.powerFactorial r * ‖t‖ ^ r ≤ taylorModel f p z 0 - taylorModel f p z t := by
  have hp : (0 : ℝ) < p := by exact_mod_cast a.order_pos.trans a.degree_ge_order
  exact taylor_decrease_of_model_decrease (hp.trans a.power_gt_degree) h.decrease.le

/-- The actual ratio denominator is positive at every positive-parameter computed step. -/
theorem ComputedStep.predicted_positive {z t : E} {u : ℝ}
    (h : ComputedStep a f z u t) (hu : 0 < u) :
    0 < taylorModel f p z 0 - taylorModel f p z t := by
  have hp : (0 : ℝ) < p := by exact_mod_cast a.order_pos.trans a.degree_ge_order
  exact (mul_pos (div_pos hu (Real.powerFactorial_pos (hp.trans a.power_gt_degree).le))
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr h.step_ne_zero) _)).trans_le h.predicted_decrease

/-- Complete runs stop at the last recorded observation. -/
theorem IsRun.terminal (h : IsRun a f x s sigma N) :
    Stationary a f (observation x s N) := by
  rcases h.2 with ⟨rfl, ht⟩ | ⟨M, _, _, _, ht⟩
  · exact ht
  · exact ht

/-- Every earlier observation fails the activated stopping test. -/
theorem IsRun.first (h : IsRun a f x s sigma N) {i : ℕ} (hi : i < N) :
    ¬Stationary a f (observation x s i) := by
  rcases h.2 with ⟨rfl, _⟩ | ⟨M, rfl, hM, _, _⟩
  · omega
  · exact hM.nonterminal i (by omega)

/-- A function or derivative oracle call at an actual point; order zero means the value. -/
abbrev OracleCall (E : Type) := E × ℕ

/-- Calls for derivative orders `lo+1` through `hi`, inclusive, at the specified point. -/
def derivativeCalls (lo hi : ℕ) (z : E) : List (OracleCall E) :=
  (List.range (hi - lo)).map fun i => (z, lo + i + 1)

open Classical in
/-- Calls for one fully processed trial: active derivatives precede its value evaluation;
accepted trials then compute the remaining unavailable Taylor derivatives. -/
def processedTrialCalls (a : Parameters q p r) (f : E → ℝ) (x s : ℕ → E)
    (sigma : ℕ → ℝ) (k : ℕ) : List (OracleCall E) :=
  derivativeCalls 0 q (x k + s k) ++ [(x k + s k, 0)] ++
    if Accepted a f (x k) (sigma k) (s k) then derivativeCalls q p (x k + s k) else []

/-- The literal cache-aware oracle schedule of a finite run with `N` computed trials.
Active derivatives are charged at every trial, including its terminal and rejected trials.
The terminal trial stops before its value is requested. -/
def oracleCalls (a : Parameters q p r) (f : E → ℝ) (x s : ℕ → E)
    (sigma : ℕ → ℝ) (N : ℕ) : List (OracleCall E) :=
  [(x 0, 0)] ++ derivativeCalls 0 q (x 0) ++ if N = 0 then [] else
    derivativeCalls q p (x 0) ++
    ((List.range (N - 1)).flatMap fun k => processedTrialCalls a f x s sigma k) ++
    derivativeCalls 0 q (observation x s N)

/-- Actual per-order oracle counts are read from the call schedule, not postulated by a run. -/
def evaluations (a : Parameters q p r) (f : E → ℝ) (x s : ℕ → E)
    (sigma : ℕ → ℝ) (N j : ℕ) : ℕ :=
  ((oracleCalls a f x s sigma N).filter fun c => c.2 = j).length

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A derivative batch contains exactly one call for each order in its specified interval. -/
theorem derivativeCalls_count (lo hi j : ℕ) (z : E) :
    (derivativeCalls lo hi z).countP (fun c => decide (c.2 = j)) =
      if lo < j ∧ j ≤ hi then 1 else 0 := by
  have hc : ∀ m : ℕ, ((List.range m).map fun i => (z, lo + i + 1)).countP
      (fun c => decide (c.2 = j)) = if lo < j ∧ j ≤ lo + m then 1 else 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.countP_append, ih]
      simp only [List.map_singleton, List.countP_singleton]
      split_ifs <;> simp_all <;> omega
  rw [derivativeCalls, hc]
  split_ifs <;> omega

/-- Each fully processed trial charges every active derivative exactly once, independently
of acceptance; the remaining cached derivative orders do not duplicate those calls. -/
theorem processedTrialCalls_count_active {j : ℕ} (hj : 0 < j) (hjq : j ≤ q) (k : ℕ) :
    (processedTrialCalls a f x s sigma k).countP (fun c => decide (c.2 = j)) = 1 := by
  classical
  by_cases ha : Accepted a f (x k) (sigma k) (s k) <;>
    simp [processedTrialCalls, ha, derivativeCalls_count, hj, hjq,
      show ¬q < j by omega, show (0 : ℕ) ≠ j by omega]

/-- With `N` computed trials, every activated derivative is called at the initial point and
at all `N` trial points. Rejected and terminal trials are both included. -/
theorem evaluations_active {j : ℕ} (hj : 0 < j) (hjq : j ≤ q) :
    evaluations a f x s sigma N j = N + 1 := by
  classical
  have hinit : (derivativeCalls 0 q (x 0)).countP (fun c => decide (c.2 = j)) = 1 := by
    simp [derivativeCalls_count, hj, hjq]
  have hhigh : (derivativeCalls q p (x 0)).countP (fun c => decide (c.2 = j)) = 0 := by
    simp [derivativeCalls_count, show ¬q < j by omega]
  have hlast : (derivativeCalls 0 q (observation x s N)).countP
      (fun c => decide (c.2 = j)) = 1 := by simp [derivativeCalls_count, hj, hjq]
  have htrials : ((List.range (N - 1)).flatMap fun k =>
      processedTrialCalls a f x s sigma k).countP (fun c => decide (c.2 = j)) = N - 1 := by
    simp [List.countP_flatMap, Function.comp_def, processedTrialCalls_count_active hj hjq]
  rw [evaluations, ← List.countP_eq_length_filter]
  by_cases hN : N = 0
  · simp [oracleCalls, hN, hinit, show (0 : ℕ) ≠ j by omega]
  · simp only [oracleCalls, ite_eq_right hN, List.countP_append, hinit, hhigh, htrials, hlast]
    simp only [List.countP_singleton, show (0 : ℕ) ≠ j by omega, decide_false, Bool.false_eq_true,
      ↓reduceIte, zero_add]
    omega

/-- A processed nonterminal trial requests exactly one objective value. -/
theorem processedTrialCalls_count_value (k : ℕ) :
    (processedTrialCalls a f x s sigma k).countP (fun c => decide (c.2 = 0)) = 1 := by
  classical
  by_cases ha : Accepted a f (x k) (sigma k) (s k) <;>
    simp [processedTrialCalls, ha, derivativeCalls_count]

/-- The objective is evaluated initially and after every nonterminal trial. A terminal
trial stops before requesting its value, so `N` trials use `max 1 N` value evaluations. -/
theorem evaluations_value : evaluations a f x s sigma N 0 = max 1 N := by
  classical
  have htrials : ((List.range (N - 1)).flatMap fun k =>
      processedTrialCalls a f x s sigma k).countP (fun c => decide (c.2 = 0)) = N - 1 := by
    simp [List.countP_flatMap, Function.comp_def, processedTrialCalls_count_value]
  rw [evaluations, ← List.countP_eq_length_filter]
  by_cases hN : N = 0
  · simp [oracleCalls, hN, derivativeCalls_count]
  · simp [oracleCalls, hN, derivativeCalls_count, htrials]
    omega

open Classical in
/-- A processed trial calls an inactive Taylor derivative exactly when the trial is accepted. -/
theorem processedTrialCalls_count_high {j : ℕ} (hjq : q < j) (hjp : j ≤ p) (k : ℕ) :
    (processedTrialCalls a f x s sigma k).countP (fun c => decide (c.2 = j)) =
      if Accepted a f (x k) (sigma k) (s k) then 1 else 0 := by
  classical
  have hj : 0 < j := by omega
  by_cases ha : Accepted a f (x k) (sigma k) (s k) <;>
    simp [processedTrialCalls, ha, derivativeCalls_count, hjq, hjp,
      show ¬j ≤ q by omega, show (0 : ℕ) ≠ j by omega]

/-- Each derivative above the active order is computed initially if work is needed, then
only after accepted nonterminal trials; all other trials reuse the current Taylor data. -/
theorem evaluations_high {j : ℕ} (hjq : q < j) (hjp : j ≤ p) :
    evaluations a f x s sigma N j = if N = 0 then 0 else
      1 + ParameterUpdates.successCount (fun k => Accepted a f (x k) (sigma k) (s k)) (N - 1) := by
  classical
  have hj : 0 < j := by omega
  have hcount := (List.nodup_range (n := N - 1)).card_eq_countP
    (P := fun k => Accepted a f (x k) (sigma k) (s k))
  rw [List.toFinset_range] at hcount
  have htrials : ((List.range (N - 1)).flatMap fun k =>
      processedTrialCalls a f x s sigma k).countP (fun c => decide (c.2 = j)) =
      ParameterUpdates.successCount (fun k => Accepted a f (x k) (sigma k) (s k)) (N - 1) := by
    rw [List.countP_flatMap]
    simp_rw [Function.comp_def, processedTrialCalls_count_high hjq hjp]
    rw [ParameterUpdates.successCount, hcount]
    induction (List.range (N - 1)) with
    | nil => rfl
    | cons k l ih =>
      by_cases hk : Accepted a f (x k) (sigma k) (s k) <;>
        simp [hk, ih, Nat.add_comm]
  rw [evaluations, ← List.countP_eq_length_filter]
  by_cases hN : N = 0 <;>
    simp [oracleCalls, hN, derivativeCalls_count, hjq, hjp, htrials,
      show ¬j ≤ q by omega, show (0 : ℕ) ≠ j by omega]

end Optimization.UniversalRegularization
