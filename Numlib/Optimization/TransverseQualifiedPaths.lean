import Numlib.Optimization.ExplicitRegularizationPathEndpoint
import Numlib.Optimization.ExplicitRegularizationBounds
import Numlib.Optimization.TransverseQualifiedContinuation

/-!
# Finite paths retaining actual qualified inner calls

The fixed transverse objective's finite paths retain the actual chosen inner returns and
invariants through their terminal states. Concatenation and replacement of an unexecuted
terminal inspection preserve these operational witnesses, including discarded inner calls.
-/

noncomputable section
namespace Optimization.TransverseQualifiedContinuation
open TransverseObjective ExplicitRegularization TransverseRegularizationContinuation

/-- A finite actual path with its chosen call-qualified branches and all state invariants.
No count, initialization or eventual termination assertion is part of this interface. -/
structure QualifiedPath {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) where
  path : Path (parameters ε hε hε1) exactOracle
  branch : ∀ k, k < path.length → Branch hε hε1 (path.node k).state
    (path.node k).inspection (path.node (k + 1)).state
      (path.trial k) (path.accepted k) (path.queries k)
  invariant : ∀ k, k ≤ path.length → Invariant (path.node k).state

variable {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}

/-- The empty qualified path has the supplied actual inspection and invariant state. -/
def QualifiedPath.nil (a : InspectedState (parameters ε hε hε1) exactOracle)
    (ha : Invariant a.state) : QualifiedPath hε hε1 where
  path := Path.nil a
  branch := by intro k hk; change k < 0 at hk; omega
  invariant := fun _ _ => ha

/-- A qualified path cannot execute a transition from a certified inspected state. -/
theorem QualifiedPath.not_certified (p : QualifiedPath hε hε1) {k : ℕ}
    (hk : k < p.path.length) :
    ¬Certified (parameters ε hε hε1) (p.path.node k).state (p.path.node k).inspection :=
  (p.path.transition k hk).not_certified

/-- Whole-node concatenation retains each actual call and every invariant state. -/
def QualifiedPath.append (l r : QualifiedPath hε hε1)
    (h : l.path.node l.path.length = r.path.node 0) : QualifiedPath hε hε1 where
  path := l.path.append r.path h
  branch := by
    intro k hk
    by_cases hl : k < l.path.length
    · rw [Path.append_node_left l.path r.path h hl.le,
        Path.append_node_left l.path r.path h (by omega), Path.append_trial_left l.path r.path h hl,
        Path.append_accepted_left l.path r.path h hl, Path.append_queries_left l.path r.path h hl]
      exact l.branch k hl
    · have hr : l.path.length ≤ k := by omega
      rw [Path.append_node_right l.path r.path h hr,
        Path.append_node_right l.path r.path h (by omega),
        Path.append_trial_right l.path r.path h hr, Path.append_accepted_right l.path r.path h hr,
        Path.append_queries_right l.path r.path h hr]
      rw [show k + 1 - l.path.length = k - l.path.length + 1 by omega]
      exact r.branch (k - l.path.length) (by change k < _ + _ at hk; omega)
  invariant := by
    intro k hk
    by_cases hl : k ≤ l.path.length
    · rw [Path.append_node_left l.path r.path h hl]
      exact l.invariant k hl
    · rw [Path.append_node_right l.path r.path h (by omega)]
      exact r.invariant (k - l.path.length) (by change k ≤ _ + _ at hk; omega)

/-- The underlying actual path of qualified concatenation is ordinary whole-node append. -/
@[simp] theorem QualifiedPath.append_path (l r : QualifiedPath hε hε1)
    (h : l.path.node l.path.length = r.path.node 0) :
    (l.append r h).path = l.path.append r.path h := rfl

/-- A new terminal inspection changes no executed chosen call or invariant state. -/
def QualifiedPath.withEndpointInspection (p : QualifiedPath hε hε1)
    (I : Inspection (parameters ε hε hε1) exactOracle.derivative
      (p.path.node p.path.length).state) : QualifiedPath hε hε1 where
  path := p.path.withEndpointInspection I
  branch := by
    intro k hk
    change k < p.path.length at hk
    rw [Path.withEndpointInspection_node_lt p.path I hk,
      Path.withEndpointInspection_state p.path I]
    exact p.branch k hk
  invariant := by
    intro k hk
    rw [Path.withEndpointInspection_state p.path I]
    exact p.invariant k hk

/-- Qualified terminal inspection replacement has precisely the ordinary actual path. -/
@[simp] theorem QualifiedPath.withEndpointInspection_path (p : QualifiedPath hε hε1)
    (I : Inspection (parameters ε hε hε1) exactOracle.derivative
      (p.path.node p.path.length).state) :
    (p.withEndpointInspection I).path = p.path.withEndpointInspection I := rfl

end Optimization.TransverseQualifiedContinuation
