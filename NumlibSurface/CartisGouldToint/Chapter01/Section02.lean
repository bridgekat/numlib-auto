import Numlib.Optimization.OracleAccounting
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chapter 1, Section 2: evaluation-complexity accounting

Value, derivative, and derivative-product requests carry their actual evaluation point. Trace
events distinguish a real query from a saved-result read, an iteration, and internal work.
An optional first attainment index leaves nontermination explicit.
-/

namespace CartisGouldToint.Chapter01.Section02

/-- An oracle key: order zero denotes a value, positive orders denote derivatives, and
optional directions specify a partial tensor contraction. The number of supplied directions
is at most the derivative order, and unsupplied slots remain tensor slots. -/
structure OracleQuery (n : ℕ) where
  point : EuclideanSpace ℝ (Fin n)
  order : ℕ
  directions : Option (Σ k : Fin (order + 1), Fin k.val → EuclideanSpace ℝ (Fin n))

/-- The actual oracle, cache, iteration and internal-operation events. -/
abbrev EvaluationEvent (n : ℕ) := Optimization.OracleAccounting.Event (OracleQuery n)

/-- The separate function and derivative evaluation counts, `#F` and `#D`. -/
def evaluationCost {n : ℕ} (events : List (EvaluationEvent n)) : ℕ × ℕ :=
  (Optimization.OracleAccounting.evaluations OracleQuery.order events 0,
    Optimization.OracleAccounting.derivativeEvaluations OracleQuery.order events)

/-- Per-degree counts distinguish the oracles actually consulted. -/
def orderEvaluationCost {n : ℕ} (events : List (EvaluationEvent n)) (j : ℕ) : ℕ :=
  Optimization.OracleAccounting.evaluations OracleQuery.order events j

/-- Iteration complexity counts iteration events separately. -/
abbrev iterationCost {n : ℕ} (events : List (EvaluationEvent n)) : ℕ :=
  Optimization.OracleAccounting.iterations events

/-- Internal subproblem work is separate from the oracle count. -/
abbrev internalCost {n : ℕ} (events : List (EvaluationEvent n)) : ℕ :=
  Optimization.OracleAccounting.internalOperations events

/-- A saved result is usable only if the exact point, order and product key is available. -/
abbrev CacheValid {n : ℕ} (available : Set (OracleQuery n))
    (events : List (EvaluationEvent n)) : Prop :=
  Optimization.OracleAccounting.CacheValid available events

/-- Value and derivative counts exhaust the actual oracle requests. -/
theorem evaluationCost_sum {n : ℕ} (events : List (EvaluationEvent n)) :
    (evaluationCost events).1 + (evaluationCost events).2 =
      (Optimization.OracleAccounting.queries events).length :=
  Optimization.OracleAccounting.value_add_derivative_evaluations OracleQuery.order events

/-- Reading a saved value or derivative contributes no new per-order evaluation. -/
@[simp] theorem orderEvaluationCost_reuse {n : ℕ} (q : OracleQuery n)
    (events : List (EvaluationEvent n)) (j : ℕ) :
    orderEvaluationCost (.reuse q :: events) j = orderEvaluationCost events j :=
  Optimization.OracleAccounting.evaluations_reuse OracleQuery.order q events j

/-- The first goal-satisfying iterate; `none` records that the goal is never reached. -/
noncomputable def firstGoalIndex {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n))
    (goal : EuclideanSpace ℝ (Fin n) → Prop) : Option ℕ :=
  Optimization.OracleAccounting.firstHittingTime fun k => goal (x k)

/-- Finite attainment includes failure of the goal at every preceding iterate. -/
theorem firstGoalIndex_eq_some_iff {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n))
    (goal : EuclideanSpace ℝ (Fin n) → Prop) (k : ℕ) :
    firstGoalIndex x goal = some k ↔ goal (x k) ∧ ∀ i < k, ¬goal (x i) :=
  Optimization.OracleAccounting.firstHittingTime_eq_some_iff (fun i => goal (x i)) k

/-- Nonattainment leaves every goal test false. -/
@[simp] theorem firstGoalIndex_eq_none {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n))
    (goal : EuclideanSpace ℝ (Fin n) → Prop) :
    firstGoalIndex x goal = none ↔ ∀ k, ¬goal (x k) :=
  Optimization.OracleAccounting.firstHittingTime_eq_none (fun k => goal (x k))

end CartisGouldToint.Chapter01.Section02
