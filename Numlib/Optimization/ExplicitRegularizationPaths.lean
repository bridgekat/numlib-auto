import Numlib.Optimization.ExplicitRegularization
import Mathlib.Tactic

/-!
# Finite paths of inspected explicit regularization states

A path records actual transitions and their value-query logs without requiring a fresh
initial cache at each fragment. Paths concatenate at an entire inspected state, so the
boundary inspection, requests and cache remain exactly the ones that were computed.
Only conversion of the whole initialized path to an execution imposes initialization.
-/

noncomputable section
namespace Optimization.ExplicitRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

/-- An actual state together with its completed dependent inspection. -/
structure InspectedState (P : Parameters) (O : Oracle f P.p) where
  state : State E
  inspection : Inspection P O.derivative state

/-- A finite actual transition path, with total state and event functions beyond its length.
Fragments impose no initialization condition on their incoming cache or requests. -/
structure Path (P : Parameters) (O : Oracle f P.p) where
  length : ℕ
  node : ℕ → InspectedState P O
  trial : ℕ → Bool
  accepted : ℕ → Bool
  queries : ℕ → List (E × ℝ)
  transition : ∀ k, k < length →
    Transition P O (node k).state (node k).inspection (node (k + 1)).state
      (trial k) (accepted k) (queries k)

/-- Source initialization conditions are imposed once, at the whole path's first state. -/
structure Initialized (P : Parameters) (O : Oracle f P.p) (a : InspectedState P O) : Prop where
  fresh : a.state.fresh = true
  cache : a.state.valueCache = none
  sigma : P.sigmaMin ≤ a.state.sigma
  radii : HigherOrderApproximateRegularization.ValidRadii
    P.toImplicitParameters.toParameters a.state.radii
  tolerance : ∀ j, 1 ≤ j → j ≤ P.q → P.epsilon j ≤ a.state.radii j
  request_pos : ∀ i ∈ Finset.Icc 1 P.p, 0 < a.state.request i
  request_le : ∀ i ∈ Finset.Icc 1 P.p, a.state.request i ≤ P.kappaInitial

variable {P : Parameters} {O : Oracle f P.p}

/-- The empty path keeps its actual inspected endpoint and has no events. -/
def Path.nil (a : InspectedState P O) : Path P O where
  length := 0
  node := fun _ => a
  trial := fun _ => false
  accepted := fun _ => false
  queries := fun _ => []
  transition := by intro k hk; omega

/-- The empty path has zero length. -/
@[simp] theorem Path.nil_length (a : InspectedState P O) : (Path.nil a).length = 0 := rfl

/-- Every node of the empty path is its given inspected endpoint. -/
@[simp] theorem Path.nil_node (a : InspectedState P O) (k : ℕ) :
    (Path.nil a).node k = a := rfl

/-- One actual transition and its terminal inspection form a one-edge path. -/
def Path.single (a b : InspectedState P O) (trial accepted : Bool) (queries : List (E × ℝ))
    (h : Transition P O a.state a.inspection b.state trial accepted queries) : Path P O where
  length := 1
  node := fun k => if k = 0 then a else b
  trial := fun k => if k = 0 then trial else false
  accepted := fun k => if k = 0 then accepted else false
  queries := fun k => if k = 0 then queries else []
  transition := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact h

/-- A one-edge path has length one. -/
@[simp] theorem Path.single_length (a b : InspectedState P O) (t c : Bool)
    (q : List (E × ℝ)) (h : Transition P O a.state a.inspection b.state t c q) :
    (Path.single a b t c q h).length = 1 := rfl

/-- The initial node of a one-edge path is the actual initial inspection. -/
@[simp] theorem Path.single_node_zero (a b : InspectedState P O) (t c : Bool)
    (q : List (E × ℝ)) (h : Transition P O a.state a.inspection b.state t c q) :
    (Path.single a b t c q h).node 0 = a := rfl

/-- The terminal node of a one-edge path keeps the supplied dependent inspection. -/
@[simp] theorem Path.single_node_one (a b : InspectedState P O) (t c : Bool)
    (q : List (E × ℝ)) (h : Transition P O a.state a.inspection b.state t c q) :
    (Path.single a b t c q h).node 1 = b := rfl

private def joinedNode (l r : Path P O) (k : ℕ) : InspectedState P O :=
  if k ≤ l.length then l.node k else r.node (k - l.length)

private theorem joinedNode_left (l r : Path P O) {k : ℕ} (hk : k ≤ l.length) :
    joinedNode l r k = l.node k := ite_eq_left hk

private theorem joinedNode_right (l r : Path P O)
    (h : l.node l.length = r.node 0) {k : ℕ} (hk : l.length ≤ k) :
    joinedNode l r k = r.node (k - l.length) := by
  by_cases he : k = l.length
  · subst k
    simpa only [joinedNode, le_refl, ite_true, Nat.sub_self] using h
  · exact ite_eq_right (by omega)

/-- Paths concatenate only when their whole boundary nodes, including inspections, agree. -/
def Path.append (l r : Path P O) (h : l.node l.length = r.node 0) : Path P O where
  length := l.length + r.length
  node := joinedNode l r
  trial := fun k => if k < l.length then l.trial k else r.trial (k - l.length)
  accepted := fun k => if k < l.length then l.accepted k else r.accepted (k - l.length)
  queries := fun k => if k < l.length then l.queries k else r.queries (k - l.length)
  transition := by
    intro k hk
    by_cases hl : k < l.length
    · rw [joinedNode_left l r hl.le, joinedNode_left l r (by omega)]
      simpa only [ite_true, hl] using l.transition k hl
    · have hr : l.length ≤ k := by omega
      rw [joinedNode_right l r h hr, joinedNode_right l r h (by omega)]
      have hs : k + 1 - l.length = k - l.length + 1 := by omega
      rw [hs]
      simpa only [ite_false, hl] using r.transition (k - l.length) (by omega)

/-- Path concatenation adds actual transition counts. -/
@[simp] theorem Path.append_length (l r : Path P O) (h : l.node l.length = r.node 0) :
    (l.append r h).length = l.length + r.length := rfl

/-- The left path's entire inspected prefix is retained, including the common endpoint. -/
theorem Path.append_node_left (l r : Path P O) (h : l.node l.length = r.node 0)
    {k : ℕ} (hk : k ≤ l.length) : (l.append r h).node k = l.node k :=
  joinedNode_left l r hk

/-- The right path's entire inspected tail starts at the common endpoint. -/
theorem Path.append_node_right (l r : Path P O) (h : l.node l.length = r.node 0)
    {k : ℕ} (hk : l.length ≤ k) : (l.append r h).node k = r.node (k - l.length) :=
  joinedNode_right l r h hk

/-- Queries of the concatenated prefix are exactly the left path's actual requests. -/
theorem Path.append_queries_left (l r : Path P O) (h : l.node l.length = r.node 0)
    {k : ℕ} (hk : k < l.length) : (l.append r h).queries k = l.queries k := ite_eq_left hk

/-- Queries of the concatenated tail are exactly the right path's shifted requests. -/
theorem Path.append_queries_right (l r : Path P O) (h : l.node l.length = r.node 0)
    {k : ℕ} (hk : l.length ≤ k) :
    (l.append r h).queries k = r.queries (k - l.length) := ite_eq_right (by omega)

/-- Trial labels before the boundary are preserved exactly. -/
theorem Path.append_trial_left (l r : Path P O) (h : l.node l.length = r.node 0)
    {k : ℕ} (hk : k < l.length) : (l.append r h).trial k = l.trial k := ite_eq_left hk

/-- Trial labels after the boundary are the right path's shifted labels. -/
theorem Path.append_trial_right (l r : Path P O) (h : l.node l.length = r.node 0)
    {k : ℕ} (hk : l.length ≤ k) :
    (l.append r h).trial k = r.trial (k - l.length) := ite_eq_right (by omega)

/-- Acceptance labels before the boundary are preserved exactly. -/
theorem Path.append_accepted_left (l r : Path P O) (h : l.node l.length = r.node 0)
    {k : ℕ} (hk : k < l.length) : (l.append r h).accepted k = l.accepted k := ite_eq_left hk

/-- Acceptance labels after the boundary are the right path's shifted labels. -/
theorem Path.append_accepted_right (l r : Path P O) (h : l.node l.length = r.node 0)
    {k : ℕ} (hk : l.length ≤ k) :
    (l.append r h).accepted k = r.accepted (k - l.length) := ite_eq_right (by omega)

/-- Concatenation starts at the exact original inspected state. -/
@[simp] theorem Path.append_node_zero (l r : Path P O) (h : l.node l.length = r.node 0) :
    (l.append r h).node 0 = l.node 0 := l.append_node_left r h (Nat.zero_le _)

/-- Concatenation ends at the right path's entire inspected endpoint. -/
@[simp] theorem Path.append_node_end (l r : Path P O) (h : l.node l.length = r.node 0) :
    (l.append r h).node (l.append r h).length = r.node r.length := by
  rw [Path.append_length, Path.append_node_right l r h (by omega), Nat.add_sub_cancel_left]

/-- An initialized actual path is a complete finite execution with the same inspections. -/
def Path.toExecution (p : Path P O) (h : Initialized P O (p.node 0)) : Execution P O p.length where
  state := fun k => (p.node k).state
  inspection := fun k => (p.node k).inspection
  trial := p.trial
  accepted := p.accepted
  queries := p.queries
  initial_fresh := h.fresh
  initial_cache := h.cache
  initial_sigma := h.sigma
  initial_radii := h.radii
  initial_tolerance := h.tolerance
  initial_request := h.request_pos
  initial_request_le := h.request_le
  transition := p.transition

/-- The conversion preserves every actual state. -/
@[simp] theorem Path.toExecution_state (p : Path P O) (h : Initialized P O (p.node 0)) (k : ℕ) :
    (p.toExecution h).state k = (p.node k).state := rfl

/-- The conversion preserves every actual query log. -/
@[simp] theorem Path.toExecution_queries (p : Path P O) (h : Initialized P O (p.node 0)) (k : ℕ) :
    (p.toExecution h).queries k = p.queries k := rfl

/-- Conversion retains the dependent inspection at every actual state. -/
@[simp] theorem Path.toExecution_inspection (p : Path P O)
    (h : Initialized P O (p.node 0)) (k : ℕ) :
    (p.toExecution h).inspection k = (p.node k).inspection := rfl

/-- Conversion retains all actual trial flags. -/
@[simp] theorem Path.toExecution_trial (p : Path P O)
    (h : Initialized P O (p.node 0)) (k : ℕ) :
    (p.toExecution h).trial k = p.trial k := rfl

/-- Conversion retains all actual acceptance flags. -/
@[simp] theorem Path.toExecution_accepted (p : Path P O)
    (h : Initialized P O (p.node 0)) (k : ℕ) :
    (p.toExecution h).accepted k = p.accepted k := rfl

/-- Every finite execution supplies its actual path without changing its events. -/
def Path.ofExecution {N : ℕ} (r : Execution P O N) : Path P O where
  length := N
  node := fun k => ⟨r.state k, r.inspection k⟩
  trial := r.trial
  accepted := r.accepted
  queries := r.queries
  transition := r.transition

/-- The original execution supplies precisely the initialization required for its path. -/
theorem Path.ofExecution_initialized {N : ℕ} (r : Execution P O N) :
    Initialized P O ((Path.ofExecution r).node 0) :=
  ⟨r.initial_fresh, r.initial_cache, r.initial_sigma, r.initial_radii,
    r.initial_tolerance, r.initial_request, r.initial_request_le⟩

/-- The path logs the concatenation of the actual value-query lists along its edges. -/
def Path.functionQueries (p : Path P O) : List (E × ℝ) :=
  ((List.range p.length).map p.queries).flatten

/-- Conversion to an execution retains the whole actual value-query log. -/
@[simp] theorem Path.toExecution_functionQueries (p : Path P O)
    (h : Initialized P O (p.node 0)) : (p.toExecution h).functionQueries = p.functionQueries := rfl

/-- An empty path makes no actual value calls. -/
@[simp] theorem Path.nil_functionQueries (a : InspectedState P O) :
    (Path.nil a).functionQueries = [] := rfl

/-- A single actual transition retains exactly its given value-query log. -/
@[simp] theorem Path.single_functionQueries (a b : InspectedState P O) (t c : Bool)
    (q : List (E × ℝ)) (h : Transition P O a.state a.inspection b.state t c q) :
    (Path.single a b t c q h).functionQueries = q := by
  simp [Path.functionQueries, Path.single]

/-- Actual value-query count is the finite sum of the edge-log lengths. -/
theorem Path.functionQueries_length (p : Path P O) :
    p.functionQueries.length = ∑ k ∈ Finset.range p.length, (p.queries k).length := by
  have aux (n : ℕ) : ((List.range n).map p.queries).flatten.length =
      ∑ k ∈ Finset.range n, (p.queries k).length := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  exact aux p.length

/-- Actual value-query counts add under path concatenation; no payment bound is assumed. -/
theorem Path.append_functionQueries_length (l r : Path P O)
    (h : l.node l.length = r.node 0) :
    (l.append r h).functionQueries.length =
      l.functionQueries.length + r.functionQueries.length := by
  simp only [Path.functionQueries_length, Path.append_length, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Path.append_queries_left l r h (Finset.mem_range.mp hk)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Path.append_queries_right l r h (by omega), Nat.add_sub_cancel_left]

end Optimization.ExplicitRegularization
