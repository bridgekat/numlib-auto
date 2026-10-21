import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Find

/-!
# Oracle events and first attainment

An oracle evaluation, a saved-value read, an iteration, and internal work are distinct events.
Cache validity records which results are available, whereas evaluation costs count only actual
oracle queries. First attainment is optional because a requested goal need never be reached.
-/

namespace Optimization.OracleAccounting

variable {Q : Type*}

/-- A recorded query, saved-result read, iteration boundary, or internal operation. -/
inductive Event (Q : Type*) where
  | query (key : Q)
  | reuse (key : Q)
  | iteration
  | internal

/-- The actual oracle queries in a trace, excluding saved-result reads and internal work. -/
def queries (events : List (Event Q)) : List Q :=
  events.filterMap fun e => match e with
    | .query q => some q
    | _ => none

/-- An empty execution makes no oracle queries. -/
@[simp] theorem queries_nil : queries ([] : List (Event Q)) = [] := rfl

/-- A real oracle query appears in the actual query schedule. -/
@[simp] theorem queries_query (q : Q) (events : List (Event Q)) :
    queries (.query q :: events) = q :: queries events := rfl

/-- A saved-result read is omitted from the actual query schedule. -/
@[simp] theorem queries_reuse (q : Q) (events : List (Event Q)) :
    queries (.reuse q :: events) = queries events := rfl

/-- The number of actual queries of one derivative order; order zero denotes a value. -/
def evaluations (order : Q → ℕ) (events : List (Event Q)) (j : ℕ) : ℕ :=
  (queries events).countP fun q => order q = j

/-- The total number of derivative queries, counted separately from value queries. -/
def derivativeEvaluations (order : Q → ℕ) (events : List (Event Q)) : ℕ :=
  (queries events).countP fun q => 0 < order q

/-- Iteration complexity counts the recorded iteration boundaries. -/
def iterations (events : List (Event Q)) : ℕ :=
  events.countP fun e => match e with | .iteration => true | _ => false

/-- Internal subproblem work has its own counter and does not count as oracle evaluation. -/
def internalOperations (events : List (Event Q)) : ℕ :=
  events.countP fun e => match e with | .internal => true | _ => false

/-- Every saved-result read must have been available initially or queried earlier. -/
noncomputable def CacheValid : Set Q → List (Event Q) → Prop
  | _, [] => True
  | available, .query q :: events => CacheValid (insert q available) events
  | available, .reuse q :: events => q ∈ available ∧ CacheValid available events
  | available, _ :: events => CacheValid available events

/-- Every initial cache is valid for an empty execution. -/
@[simp] theorem cacheValid_nil (available : Set Q) : CacheValid available [] := trivial

/-- An iteration boundary leaves the available cache unchanged. -/
@[simp] theorem cacheValid_iteration (available : Set Q) (events : List (Event Q)) :
    CacheValid available (.iteration :: events) ↔ CacheValid available events := Iff.rfl

/-- An internal operation leaves the available cache unchanged. -/
@[simp] theorem cacheValid_internal (available : Set Q) (events : List (Event Q)) :
    CacheValid available (.internal :: events) ↔ CacheValid available events := Iff.rfl

/-- A real query makes its result available for all later saved-result reads. -/
@[simp] theorem cacheValid_query (available : Set Q) (q : Q) (events : List (Event Q)) :
    CacheValid available (.query q :: events) ↔ CacheValid (insert q available) events := Iff.rfl

/-- Reading a saved result requires that exact key to be available. -/
@[simp] theorem cacheValid_reuse (available : Set Q) (q : Q) (events : List (Event Q)) :
    CacheValid available (.reuse q :: events) ↔ q ∈ available ∧ CacheValid available events :=
  Iff.rfl

/-- Reusing a saved result adds no oracle evaluation of any order. -/
@[simp] theorem evaluations_reuse (order : Q → ℕ) (q : Q)
    (events : List (Event Q)) (j : ℕ) :
    evaluations order (.reuse q :: events) j = evaluations order events j := by
  simp [evaluations, queries]

/-- Internal subproblem work adds no oracle evaluation of any order. -/
@[simp] theorem evaluations_internal (order : Q → ℕ) (events : List (Event Q)) (j : ℕ) :
    evaluations order (.internal :: events) j = evaluations order events j := by
  simp [evaluations, queries]

/-- Separate value and derivative counts exhaust the actual query schedule. -/
theorem value_add_derivative_evaluations (order : Q → ℕ) (events : List (Event Q)) :
    evaluations order events 0 + derivativeEvaluations order events = (queries events).length := by
  suffices ∀ calls : List Q,
      calls.countP (fun q => order q = 0) + calls.countP (fun q => 0 < order q) = calls.length from
    this (queries events)
  intro calls
  induction calls with
  | nil => simp
  | cons q calls ih =>
    by_cases h : order q = 0
    · simp [h, ih, Nat.add_assoc, Nat.add_comm]
    · have hp : 0 < order q := Nat.pos_of_ne_zero h
      simp [h, hp, ih, Nat.add_comm, Nat.add_left_comm]

open Classical in
/-- The first successful test, with `none` representing nonattainment. -/
noncomputable def firstHittingTime (P : ℕ → Prop) : Option ℕ :=
  if h : ∃ n, P n then some (Nat.find h) else none

/-- Nonattainment means that every test fails. -/
@[simp] theorem firstHittingTime_eq_none (P : ℕ → Prop) :
    firstHittingTime P = none ↔ ∀ n, ¬P n := by
  classical
  simp [firstHittingTime, not_exists]

/-- A finite hitting time records success and failure of every preceding test. -/
theorem firstHittingTime_eq_some_iff (P : ℕ → Prop) (n : ℕ) :
    firstHittingTime P = some n ↔ P n ∧ ∀ k < n, ¬P k := by
  classical
  unfold firstHittingTime
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨Nat.find_spec h, fun k hk => Nat.find_min h hk⟩
    · rintro ⟨hn, hfirst⟩
      apply le_antisymm (Nat.find_min' h hn)
      by_contra hnle
      exact hfirst (Nat.find h) (by omega) (Nat.find_spec h)
  · simp only [false_iff]
    rintro ⟨hn, _⟩
    exact h ⟨n, hn⟩

end Optimization.OracleAccounting
