import Numlib.Optimization.TransverseQualifiedPaths
import Numlib.Optimization.TransverseAcceptedSchedule
import Numlib.Optimization.TransverseTrialSegments

/-!
# Finite qualified prelude, injection and tail

Finite trial paths concatenate at their actual complete states. Selecting the next
segment's inspection changes only the previous unexecuted endpoint inspection, retaining
all executed calls, requests, caches and value queries.
-/

noncomputable section
namespace Optimization.TransverseFinitePrefix
open TransverseObjective ExplicitRegularization TransverseRegularizationContinuation
open TransverseQualifiedContinuation

variable {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}

private def endpointInspection (a b : InspectedState (parameters ε hε hε1) exactOracle)
    (h : a.state = b.state) :
    Inspection (parameters ε hε hε1) exactOracle.derivative a.state := h.symm ▸ b.inspection

private theorem endpoint_eq (a b : InspectedState (parameters ε hε hε1) exactOracle)
    (h : a.state = b.state) : ⟨a.state, endpointInspection a b h⟩ = b := by
  cases a
  cases b
  cases h
  rfl

private theorem endpoint_match (p r : QualifiedPath hε hε1)
    (h : (p.path.node p.path.length).state = (r.path.node 0).state) :
    let I := endpointInspection (p.path.node p.path.length) (r.path.node 0) h
    (p.withEndpointInspection I).path.node (p.withEndpointInspection I).path.length =
      r.path.node 0 := by
  dsimp only
  let I := endpointInspection (p.path.node p.path.length) (r.path.node 0) h
  change (p.path.withEndpointInspection I).node p.path.length = r.path.node 0
  exact (Path.withEndpointInspection_node_end p.path I).trans (endpoint_eq _ _ h)

/-- Concatenate actual qualified fragments whose complete boundary states agree. Only
an unexecuted terminal inspection is chosen to match the next actual segment. -/
def appendAtState (p r : QualifiedPath hε hε1)
    (h : (p.path.node p.path.length).state = (r.path.node 0).state) :
    QualifiedPath hε hε1 :=
  let I := endpointInspection (p.path.node p.path.length) (r.path.node 0) h
  (p.withEndpointInspection I).append r (endpoint_match p r h)

/-- State-based concatenation adds the actual finite transition lengths. -/
@[simp] theorem appendAtState_length (p r : QualifiedPath hε hε1)
    (h : (p.path.node p.path.length).state = (r.path.node 0).state) :
    (appendAtState p r h).path.length = p.path.length + r.path.length := rfl

/-- State-based concatenation keeps every initial state field, even for an empty prefix. -/
theorem appendAtState_initial_state (p r : QualifiedPath hε hε1)
    (h : (p.path.node p.path.length).state = (r.path.node 0).state) :
    ((appendAtState p r h).path.node 0).state = (p.path.node 0).state := by
  let I := endpointInspection (p.path.node p.path.length) (r.path.node 0) h
  let q := p.withEndpointInspection I
  calc
    _ = (q.path.node 0).state :=
      congrArg InspectedState.state (Path.append_node_zero q.path r.path (endpoint_match p r h))
    _ = _ := Path.withEndpointInspection_state p.path I 0

/-- The entire terminal node is the right fragment's actual terminal inspection and state. -/
theorem appendAtState_node_end (p r : QualifiedPath hε hε1)
    (h : (p.path.node p.path.length).state = (r.path.node 0).state) :
    (appendAtState p r h).path.node (appendAtState p r h).path.length =
      r.path.node r.path.length := by
  exact Path.append_node_end
    (p.withEndpointInspection (endpointInspection _ _ h)).path r.path (endpoint_match p r h)

/-- State-based concatenation adds the actual query-log lengths without any payment premise. -/
theorem appendAtState_functionQueries_length (p r : QualifiedPath hε hε1)
    (h : (p.path.node p.path.length).state = (r.path.node 0).state) :
    (appendAtState p r h).path.functionQueries.length =
      p.path.functionQueries.length + r.path.functionQueries.length := by
  let I := endpointInspection (p.path.node p.path.length) (r.path.node 0) h
  let q := p.withEndpointInspection I
  calc
    _ = q.path.functionQueries.length + r.path.functionQueries.length :=
      Path.append_functionQueries_length q.path r.path (endpoint_match p r h)
    _ = _ := congrArg (fun qs : List (Plane × ℝ) =>
      qs.length + r.path.functionQueries.length)
        (Path.withEndpointInspection_functionQueries p.path I)

open TransverseAcceptedSchedule

/-- Every actual scheduled start has a finite qualified trial segment reaching the next
scheduled point, with exactly two genuine value queries. -/
theorem exists_step_segment (hsmall : ε ≤ 1 / 65536) (n : ℕ)
    (hn : n < totalCount ε hε) (a : State Plane) (ha : Invariant a)
    (hpoint : a.point = pointAt ε hε n) :
    ∃ p : QualifiedPath hε hε1,
      (p.path.node 0).state = a ∧
      (p.path.node p.path.length).state.point = pointAt ε hε (n + 1) ∧
      0 < p.path.length ∧ p.path.functionQueries.length = 2 := by
  suffices ∃ p : QualifiedPath hε hε1,
      (p.path.node 0).state = a ∧
      (p.path.node p.path.length).state.point = a.point + stepAt ε hε n ∧
      0 < p.path.length ∧ p.path.functionQueries.length = 2 by
    obtain ⟨p, hp0, hp1, hlen, hcount⟩ := this
    refine ⟨p, hp0, ?_, hlen, hcount⟩
    exact hp1.trans (by rw [hpoint, pointAt_succ hε hn])
  by_cases hpre : n < TransversePrelude.crossingIndex ε hε
  · have hc := prelude_conditions hε hpre
    have hp : a.point = point 0 (TransversePrelude.ordinate n) :=
      hpoint.trans (pointAt_prelude hε hpre.le)
    obtain ⟨p, hp0, hp1, hlen, hcount, _⟩ :=
      TransverseTrialSegments.exists_prelude_segment hε hε1 hc.1 hc.2 a ha hp
    refine ⟨p, hp0, ?_, hlen, hcount⟩
    simpa only [stepAt_prelude hε hpre] using hp1
  · by_cases he : n = TransversePrelude.crossingIndex ε hε
    · subst n
      have hp := hpoint.trans (pointAt_prelude hε le_rfl)
      obtain ⟨p, hp0, hp1, hlen, hcount, _⟩ :=
        TransverseTrialSegments.exists_injection_segment
          (injection_conditions hε hsmall) hε1 a ha hp
      refine ⟨p, hp0, ?_, hlen, hcount⟩
      simpa only [stepAt_injection] using hp1
    · have htail : TransversePrelude.crossingIndex ε hε < n := by omega
      have hc := tail_conditions hε hsmall htail hn.le
      have hp : a.point = point (2 * ε / 3) (pointAt ε hε n 1) := by
        rw [hpoint, pointAt_tail hε htail]
        rfl
      obtain ⟨p, hp0, hp1, hlen, hcount, _⟩ :=
        TransverseTrialSegments.exists_tail_segment hc hε1 a ha hp
      refine ⟨p, hp0, ?_, hlen, hcount⟩
      simpa only [stepAt_tail hε htail] using hp1

/-- Every finite initial portion of the accepted schedule has an actual qualified path
from the fixed initial state. Its query count is derived by concatenating actual logs. -/
theorem exists_schedule_prefix (hsmall : ε ≤ 1 / 65536) (n : ℕ)
    (hn : n ≤ totalCount ε hε) :
    ∃ p : QualifiedPath hε hε1,
      (p.path.node 0).state = initialState ∧
      (p.path.node p.path.length).state.point = pointAt ε hε n ∧
      p.path.functionQueries.length = 2 * n ∧ n ≤ p.path.length := by
  induction n with
  | zero =>
    let I := Classical.choice (exists_inspection hε hε1 initialState initialState_invariant)
    let p := QualifiedPath.nil ⟨initialState, I⟩ initialState_invariant
    exact ⟨p, rfl, (pointAt_zero ε hε).symm, rfl, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨p, hp0, hp1, hpc, hpl⟩ := ih (by omega)
    obtain ⟨r, hr0, hr1, hrl, hrc⟩ := exists_step_segment (hε1 := hε1) hsmall n (by omega)
      (p.path.node p.path.length).state (p.invariant _ le_rfl) hp1
    refine ⟨appendAtState p r hr0.symm,
      (appendAtState_initial_state p r hr0.symm).trans hp0, ?_, ?_, ?_⟩
    · exact (congrArg (fun a => a.state.point)
        (appendAtState_node_end p r hr0.symm)).trans hr1
    · rw [appendAtState_functionQueries_length, hpc, hrc]
      omega
    · rw [appendAtState_length]
      omega

/-- The complete actual prelude, injection and common-window tail starts at the fixed
initial state, has its true endpoint gradient below tolerance, and makes two actual value
queries per accepted step. Every selected inspection through its endpoint fails certification. -/
theorem exists_finite_prefix (hsmall : ε ≤ 1 / 65536) :
    ∃ p : QualifiedPath hε hε1,
      (p.path.node 0).state = initialState ∧
      (p.path.node p.path.length).state.point = pointAt ε hε (totalCount ε hε) ∧
      p.path.functionQueries.length = 2 * totalCount ε hε ∧
      totalCount ε hε ≤ p.path.length ∧
      ‖fderiv ℝ objective (p.path.node p.path.length).state.point‖ < ε ∧
      ∀ k, k ≤ p.path.length →
        ¬Certified (parameters ε hε hε1) (p.path.node k).state (p.path.node k).inspection := by
  obtain ⟨p, hp0, hp1, hcount, hlen⟩ :=
    exists_schedule_prefix (hε1 := hε1) hsmall (totalCount ε hε) le_rfl
  have hc := TransverseTailWindow.tailOrdinate_conditions hε hsmall
    (le_refl (TransverseTailWindow.tailCount ε hε))
  have hp : (p.path.node p.path.length).state.point = point (2 * ε / 3)
      (TransverseTailWindow.tailOrdinate ε hε (TransverseTailWindow.tailCount ε hε)) :=
    hp1.trans (pointAt_totalCount ε hε)
  have hr : (p.path.node p.path.length).state.radii 1 ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [(p.invariant _ le_rfl).2.2.2.2.2.1]
    norm_num
  obtain ⟨I, ho, _⟩ := TransverseRefinementBlocks.exists_tail_inspection
    hc hε1 (p.path.node p.path.length).state hp hr
  let q := p.withEndpointInspection I
  have hstate (k : ℕ) : (q.path.node k).state = (p.path.node k).state :=
    Path.withEndpointInspection_state p.path I k
  have hqpoint : (q.path.node q.path.length).state.point =
      pointAt ε hε (totalCount ε hε) :=
    (congrArg (fun a : State Plane => a.point) (hstate p.path.length)).trans hp1
  refine ⟨q, (hstate 0).trans hp0, hqpoint,
    ?_, hlen, ?_, ?_⟩
  · exact (congrArg List.length (Path.withEndpointInspection_functionQueries p.path I)).trans
      hcount
  · rw [hqpoint]
    exact pointAt_norm_fderiv_lt_epsilon hε hsmall
      (crossingIndex_lt_totalCount ε hε) le_rfl
  · intro k hk
    by_cases hlt : k < q.path.length
    · exact q.not_certified hlt
    · have he : k = p.path.length := by
        change k ≤ p.path.length at hk
        change ¬k < p.path.length at hlt
        omega
      subst k
      change ¬Certified (parameters ε hε hε1)
        ((p.path.withEndpointInspection I).node p.path.length).state
        ((p.path.withEndpointInspection I).node p.path.length).inspection
      rw [Path.withEndpointInspection_node_end p.path I]
      intro hcert
      have := hcert.1
      change I.order = 2 at this
      omega

end Optimization.TransverseFinitePrefix
