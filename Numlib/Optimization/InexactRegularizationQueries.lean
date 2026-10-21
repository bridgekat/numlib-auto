import Numlib.Optimization.InexactRegularizationDecrease
import Numlib.Optimization.InexactRegularizationCounts

/-!
# Actual query logs for complete implicit-accuracy regularization runs

A complete run stores its states and event flags, while its legal transitions are
propositions. At each trial we select one of the transition's genuine completed inspections
and inner returns. This gives a canonical legal realization of the otherwise unrecorded
trial step. The choice uses the prefix ending at that transition, independently of the
horizon of any query log. In particular, rejected trial queries still come from an actual
legal returned step; accepted trial queries are the recorded successor points.

The objective log contains initialization and one query for every trial. The derivative log
contains the point and positive request vector of every fresh incoming tensor batch. Both
logs retain repeated query points, and their lengths equal the operational counters exactly.
Their finite index enumeration does not assert an ordering beyond that of `Finset.toList`.
-/

noncomputable section
namespace Optimization.InexactRegularization
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E}

/-- Select actual legal trial witnesses once for each transition of a complete run. The
choice is independent of a later query-log horizon; it retains the inspection, detailed
inner execution, accuracy check, ratio update, acceptance decision and successor state. -/
def Run.executedTrial (r : Run P checked f oracle) (k : ℕ) (ht : r.trial k = true) :
    ExecutedTrial P checked f oracle (r.state k) (r.state (k + 1)) (r.accepted k) :=
  (r.prefix (k + 1)).executedTrial (Nat.lt_succ_self k) ht

/-- The objective query point at a real trial is its incoming point plus the canonical
actual returned step. The fallback at a nontrial index is never entered in the trial log. -/
def Run.trialPoint (r : Run P checked f oracle) (k : ℕ) : E :=
  if ht : r.trial k = true then (r.state k).point + (r.executedTrial k ht).inner.step
  else (r.state k).point

/-- At every actual trial the query uses its selected legal returned inner step. -/
theorem Run.trialPoint_of_trial (r : Run P checked f oracle) {k : ℕ}
    (ht : r.trial k = true) :
    r.trialPoint k = (r.state k).point + (r.executedTrial k ht).inner.step := by
  simp only [Run.trialPoint, dite_eq_left ht]

/-- A nontrial index has the incoming-point fallback and adds no trial query to the log. -/
theorem Run.trialPoint_of_not_trial (r : Run P checked f oracle) {k : ℕ}
    (ht : r.trial k = false) : r.trialPoint k = (r.state k).point := by
  simp only [Run.trialPoint, ht, Bool.false_eq_true, not_false_eq_true, dite_eq_right]

/-- Every logged trial query, including a rejected one, has full actual operational
witnesses. No unrelated query point or hypothetical step is inserted into the log. -/
theorem Run.trialPoint_spec (r : Run P checked f oracle) {k : ℕ}
    (ht : r.trial k = true) :
    ∃ t : ExecutedTrial P checked f oracle (r.state k) (r.state (k + 1)) (r.accepted k),
      r.trialPoint k = (r.state k).point + t.inner.step :=
  ⟨r.executedTrial k ht, r.trialPoint_of_trial ht⟩

/-- An accepted trial queries exactly the recorded actual successor point. -/
theorem Run.trialPoint_of_accepted (r : Run P checked f oracle) {k : ℕ}
    (ha : r.accepted k = true) : r.trialPoint k = (r.state (k + 1)).point := by
  have ht := (r.transition_all k).accepted_is_trial ha
  exact (r.trialPoint_of_trial ht).trans ((r.executedTrial k ht).accepted_point ha).symm

/-- The selected trial point is exactly the objective argument in the actual ratio update. -/
theorem Run.ratio_eq_trialPoint (r : Run P checked f oracle) {k : ℕ}
    (ht : r.trial k = true) :
    ratio P f oracle (r.state k) (r.executedTrial k ht).inner.step =
      (f (r.state k).point - f (r.trialPoint k)) /
        InexactTaylorModels.decrement (oracle (r.state k).point (r.state k).request)
          P.p (r.executedTrial k ht).inner.step := by
  rw [r.trialPoint_of_trial ht]
  rfl

/-- All actual objective queries through a finite prefix: initialization and one query for
each trial index. Repeated points remain distinct paid list entries. -/
def Run.functionQueries (r : Run P checked f oracle) (N : ℕ) : List E :=
  (r.state 0).point ::
    (((Finset.range N).filter fun k => r.trial k).toList.map r.trialPoint)

/-- All actual fresh derivative batches through a finite prefix, retaining both the incoming
point and its request vector. Rejected trials reuse their cache and add no fresh batch. -/
def Run.derivativeQueries (r : Run P checked f oracle) (N : ℕ) : List (E × (ℕ → ℝ)) :=
  (((Finset.range N).filter fun k => (r.state k).fresh).toList.map
    fun k => ((r.state k).point, (r.state k).request))

/-- The objective log is the initialization query followed by the actual indexed trial
queries; this characterization permits consumers to avoid unfolding the definition. -/
theorem Run.functionQueries_eq (r : Run P checked f oracle) (N : ℕ) :
    r.functionQueries N = (r.state 0).point ::
      (((Finset.range N).filter fun k => r.trial k).toList.map r.trialPoint) := rfl

/-- The derivative log consists precisely of the actual incoming fresh-batch keys. -/
theorem Run.derivativeQueries_eq (r : Run P checked f oracle) (N : ℕ) :
    r.derivativeQueries N =
      (((Finset.range N).filter fun k => (r.state k).fresh).toList.map
        fun k => ((r.state k).point, (r.state k).request)) := rfl

/-- A zero-pass objective log pays its initialization query. -/
@[simp] theorem Run.functionQueries_zero (r : Run P checked f oracle) :
    r.functionQueries 0 = [(r.state 0).point] := by
  simp [r.functionQueries_eq]

/-- A zero-pass prefix inspects no incoming derivative batches. -/
@[simp] theorem Run.derivativeQueries_zero (r : Run P checked f oracle) :
    r.derivativeQueries 0 = [] := by
  simp [r.derivativeQueries_eq]

/-- The actual objective-query log has exactly the existing operational function count. -/
@[simp] theorem Run.functionQueries_length (r : Run P checked f oracle) (N : ℕ) :
    (r.functionQueries N).length = (r.prefix N).functionCount := by
  simp only [Run.functionQueries_eq, List.length_cons, List.length_map, Finset.length_toList,
    Execution.functionCount, Run.prefix]
  exact Nat.add_comm _ _

/-- The actual derivative-query log has exactly the existing count of fresh tensor batches. -/
@[simp] theorem Run.derivativeQueries_length (r : Run P checked f oracle) (N : ℕ) :
    (r.derivativeQueries N).length = (r.prefix N).derivativeBatches := by
  simp only [Run.derivativeQueries_eq, List.length_map, Finset.length_toList,
    Execution.derivativeBatches, Run.prefix]
  rfl

/-- Objective-log membership means initialization or an actual trial query in the prefix.
The list, unlike this membership proposition, also retains all repetitions. -/
theorem Run.mem_functionQueries_iff (r : Run P checked f oracle) (N : ℕ) (x : E) :
    x ∈ r.functionQueries N ↔ x = (r.state 0).point ∨
      ∃ k, k < N ∧ r.trial k = true ∧ r.trialPoint k = x := by
  simp only [Run.functionQueries_eq, List.mem_cons, List.mem_map, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_range]
  aesop

/-- Derivative-log membership means an actual fresh incoming point and request in the
prefix. Each occurrence is paid even when another batch has the same key. -/
theorem Run.mem_derivativeQueries_iff (r : Run P checked f oracle) (N : ℕ)
    (y : E × (ℕ → ℝ)) :
    y ∈ r.derivativeQueries N ↔
      ∃ k, k < N ∧ (r.state k).fresh = true ∧ ((r.state k).point, (r.state k).request) = y := by
  simp only [Run.derivativeQueries_eq, List.mem_map, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_range]
  aesop

/-- Every logged derivative batch has positive active requests bounded by the fixed initial
cap, as derived from its genuine transition prefix. -/
theorem Run.derivativeQueries_request_bounds (r : Run P checked f oracle) {N : ℕ}
    {x : E} {h : ℕ → ℝ} (hy : (x, h) ∈ r.derivativeQueries N)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) : 0 < h i ∧ h i ≤ P.kappaInitial := by
  obtain ⟨k, hk, _, he⟩ := (r.mem_derivativeQueries_iff N (x, h)).mp hy
  have hrequest : (r.state k).request = h := congrArg Prod.snd he
  rw [← hrequest]
  have hb := (r.prefix N).request_bounds (Nat.le_of_lt hk) hi
  exact ⟨hb.1, hb.2.trans ((r.prefix N).initial_request_le i hi)⟩

end Optimization.InexactRegularization
