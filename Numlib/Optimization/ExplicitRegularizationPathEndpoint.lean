import Numlib.Optimization.ExplicitRegularizationPaths

/-!
# Replacing an unexecuted terminal inspection

An actual transition uses its initial inspection and its successor state. A finite path's
terminal inspection is therefore replaceable by any completed inspection at the same actual
state. Every executed inspection, all state data and all query logs remain identical.
-/

noncomputable section
namespace Optimization.ExplicitRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
variable {P : Parameters} {O : Oracle f P.p}

private def endpointNode (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) (k : ℕ) : InspectedState P O :=
  if k = p.length then ⟨(p.node p.length).state, I⟩ else p.node k

private theorem endpointNode_state (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) (k : ℕ) :
    (endpointNode p I k).state = (p.node k).state := by
  unfold endpointNode
  split_ifs with hk
  · subst k
    rfl
  · rfl

private theorem endpointNode_lt (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) {k : ℕ} (hk : k < p.length) :
    endpointNode p I k = p.node k := ite_eq_right (by omega)

/-- Replace the unexecuted terminal inspection without changing the actual finite path. -/
def Path.withEndpointInspection (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) : Path P O where
  length := p.length
  node := endpointNode p I
  trial := p.trial
  accepted := p.accepted
  queries := p.queries
  transition := by
    intro k hk
    rw [endpointNode_lt p I hk, endpointNode_state p I]
    exact p.transition k hk

/-- Replacing the terminal inspection preserves the number of executed transitions. -/
@[simp] theorem Path.withEndpointInspection_length (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) :
    (p.withEndpointInspection I).length = p.length := rfl

/-- Every actual state is preserved, including cache, requests, parameter and freshness. -/
@[simp] theorem Path.withEndpointInspection_state (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) (k : ℕ) :
    ((p.withEndpointInspection I).node k).state = (p.node k).state := endpointNode_state p I k

/-- Every executed inspected node is retained in full. -/
theorem Path.withEndpointInspection_node_lt (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) {k : ℕ} (hk : k < p.length) :
    (p.withEndpointInspection I).node k = p.node k := endpointNode_lt p I hk

/-- The terminal node contains precisely the new completed inspection at the old state. -/
@[simp] theorem Path.withEndpointInspection_node_end (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) :
    (p.withEndpointInspection I).node p.length = ⟨(p.node p.length).state, I⟩ := by
  simp only [Path.withEndpointInspection, endpointNode, ite_true]

/-- Every actual trial label remains identical. -/
@[simp] theorem Path.withEndpointInspection_trial (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) (k : ℕ) :
    (p.withEndpointInspection I).trial k = p.trial k := rfl

/-- Every actual acceptance label remains identical. -/
@[simp] theorem Path.withEndpointInspection_accepted (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) (k : ℕ) :
    (p.withEndpointInspection I).accepted k = p.accepted k := rfl

/-- Every actual edge-query list remains identical. -/
@[simp] theorem Path.withEndpointInspection_queries (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) (k : ℕ) :
    (p.withEndpointInspection I).queries k = p.queries k := rfl

/-- The whole value-query log is unchanged by the terminal inspection replacement. -/
@[simp] theorem Path.withEndpointInspection_functionQueries (p : Path P O)
    (I : Inspection P O.derivative (p.node p.length).state) :
    (p.withEndpointInspection I).functionQueries = p.functionQueries := rfl

end Optimization.ExplicitRegularization
