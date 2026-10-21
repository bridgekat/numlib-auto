import Numlib.Optimization.TransverseFinitePrefix
import Numlib.Optimization.TransverseDyadicRates
import Numlib.Optimization.ExplicitRegularizationToleranceParameters

/-!
# Actual certification counts for the transverse fixed-data family

The finite prelude, injection and tail extend to a full call-qualified execution. Actual
value-query logs are monotone under taking longer prefixes, so certification must follow
the whole constructed log. The tolerance family fixes the objective, oracle, initialization
and all outer controls before any proposed rate coefficients.
-/

noncomputable section
namespace Optimization.TransverseCertificationRates
open TransverseObjective ExplicitRegularization TransverseRegularizationContinuation
open TransverseQualifiedContinuation TransverseAcceptedSchedule TransverseFinitePrefix

variable {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}

/-- The fixed initial state supplies exactly the existing source initialization conditions. -/
theorem initialized_of_initialState (p : QualifiedPath hε hε1)
    (h : (p.path.node 0).state = initialState) :
    Initialized (parameters ε hε hε1) exactOracle (p.path.node 0) := by
  constructor
  · exact congrArg (fun a : State Plane => a.fresh) h
  · exact congrArg (fun a : State Plane => a.valueCache) h
  · rw [h]
    norm_num [parameters, initialState]
  · rw [h]
    intro j _ _
    constructor <;> norm_num [initialState]
  · rw [h]
    intro j _ _
    exact hε1.le
  · rw [h]
    intro i _
    norm_num [initialState]
  · rw [h]
    intro i _
    norm_num [initialState, parameters]

/-- The actual value-query log of a full run through a finite index. -/
def functionQueries (s : Run ε hε hε1) (N : ℕ) : List (Plane × ℝ) :=
  ((List.range N).map s.queries).flatten

/-- The true log length is the sum of its actual edge-list lengths. -/
theorem functionQueries_length (s : Run ε hε hε1) (N : ℕ) :
    (functionQueries s N).length = ∑ k ∈ Finset.range N, (s.queries k).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simpa [functionQueries, List.range_succ, Finset.sum_range_succ] using
      congrArg (fun n : ℕ => n + (s.queries N).length) ih

/-- Extending the finite prefix cannot remove any actual value calls. -/
theorem functionQueries_length_mono (s : Run ε hε hε1) {N M : ℕ} (h : N ≤ M) :
    (functionQueries s N).length ≤ (functionQueries s M).length := by
  rw [functionQueries_length s N, functionQueries_length s M]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- A fully initialized call-qualified execution contains the complete actual failed
prefix. Any certificate of this run follows at least twice the available tail length in
actual value queries, including all forced accuracy refinements and their inner calls. -/
theorem exists_long_prefix_run (hsmall : ε ≤ 1 / 65536) :
    ∃ (s : Run ε hε hε1) (N : ℕ),
      (s.node 0).state = initialState ∧
      IsExecution (parameters ε hε hε1) exactOracle
        (fun k => (s.node k).state) (fun k => (s.node k).inspection)
        s.trial s.accepted s.queries ∧
      (∀ k, k ≤ N →
        ¬Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection) ∧
      (functionQueries s N).length = 2 * totalCount ε hε ∧
      (∀ k, N ≤ k → ‖fderiv ℝ objective (s.node k).state.point‖ < ε) ∧
      (∀ k, N ≤ k → Certified (parameters ε hε hε1)
        (s.node k).state (s.node k).inspection → s.node (k + 1) = s.node k) ∧
      ∀ k, Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection →
        2 * TransverseTailWindow.tailCount ε hε ≤ (functionQueries s k).length := by
  obtain ⟨p, hp0, hp1, hcount, _hlen, hcap, hfailed⟩ :=
    exists_finite_prefix (hε := hε) (hε1 := hε1) hsmall
  let r := p.path.toExecution (initialized_of_initialState p hp0)
  obtain ⟨s, hsnode, hsevent, hscap, hsfrozen, hsexec⟩ :=
    exists_run_extension hε hε1 r p.invariant p.branch
  have hs0 : (s.node 0).state = initialState :=
    (congrArg (fun a : Node ε hε hε1 => a.state)
      (hsnode 0 (Nat.zero_le _))).trans hp0
  have hnone (k : ℕ) (hk : k ≤ p.path.length) :
      ¬Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection := by
    rw [hsnode k hk]
    exact hfailed k hk
  have hlog : (functionQueries s p.path.length).length =
      p.path.functionQueries.length := by
    rw [functionQueries_length s p.path.length, Path.functionQueries_length p.path]
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg List.length (hsevent k (Finset.mem_range.mp hk)).2.2
  refine ⟨s, p.path.length, hs0, hsexec, hnone, hlog.trans hcount,
    fun k hk => (hscap k hk).trans_lt hcap, hsfrozen, ?_⟩
  intro k hc
  have hNk : p.path.length < k := by
    by_contra! hle
    exact hnone k hle hc
  calc
    2 * TransverseTailWindow.tailCount ε hε ≤ 2 * totalCount ε hε := by
      unfold totalCount
      omega
    _ = (functionQueries s p.path.length).length := (hlog.trans hcount).symm
    _ ≤ (functionQueries s k).length := functionQueries_length_mono s hNk.le

/-- A single full-run selection policy is fixed as a function of the tolerance, before
any proposed rate coefficients. Its actual branches retain every returned call. -/
def chosenRun (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) : Run ε hε hε1 :=
  Classical.choose (exists_long_prefix_run (hε := hε) (hε1 := hε1) hsmall)

/-- Every selected full run starts at the same actual fixed state. -/
theorem chosenRun_initial (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) :
    ((chosenRun hε hε1 hsmall).node 0).state = initialState := by
  have h := Classical.choose_spec (Classical.choose_spec
    (exists_long_prefix_run (hε := hε) (hε1 := hε1) hsmall))
  exact h.1

/-- The selected actual run obeys the source operational algorithm until certification. -/
theorem chosenRun_isExecution (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) :
    let s := chosenRun hε hε1 hsmall
    IsExecution (parameters ε hε hε1) exactOracle
      (fun k => (s.node k).state) (fun k => (s.node k).inspection)
      s.trial s.accepted s.queries := by
  have h := Classical.choose_spec (Classical.choose_spec
    (exists_long_prefix_run (hε := hε) (hε1 := hε1) hsmall))
  exact h.2.1

/-- Every actual certificate of the selected run follows the constructed query lower bound. -/
theorem chosenRun_certified_query_lower
    (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) (k : ℕ)
    (hc : Certified (parameters ε hε hε1)
      ((chosenRun hε hε1 hsmall).node k).state
      ((chosenRun hε hε1 hsmall).node k).inspection) :
    2 * TransverseTailWindow.tailCount ε hε ≤
      (functionQueries (chosenRun hε hε1 hsmall) k).length := by
  have h := Classical.choose_spec (Classical.choose_spec
    (exists_long_prefix_run (hε := hε) (hε1 := hε1) hsmall))
  exact h.2.2.2.2.2.2 k hc

/-- Replacing tolerances leaves every outer control in this family exactly fixed. -/
theorem parameters_withTolerances {ε₀ : ℝ} (h₀ : 0 < ε₀) (h₀1 : ε₀ < 1)
    (hε : 0 < ε) (hε1 : ε < 1) :
    (parameters ε₀ h₀ h₀1).withTolerances (fun _ => ε)
      (fun _ _ _ => hε) (fun _ _ _ => hε1) = parameters ε hε hε1 := rfl

/-- Every member of the dyadic family is an admissible strict tolerance. -/
theorem dyadic_epsilon_lt_one {m : ℕ} (hm : 3 ≤ m) :
    TransverseDyadicRates.epsilon m < 1 := by
  have h := TransverseDyadicRates.epsilon_le hm
  linarith

/-- On one fixed actual run-selection family, every proposed corrected three-halves
function-count rate fails at arbitrarily small dyadic tolerances. The coefficients and
minimum index precede the choice of tolerance; the run-selection function is already fixed. -/
theorem exists_rate_violating_run (A C : ℝ) (M : ℕ) :
    ∃ (m : ℕ) (hm : max 3 M ≤ m),
      let h3 := (le_max_left 3 M).trans hm
      let ε := TransverseDyadicRates.epsilon m
      let hε := TransverseDyadicRates.epsilon_pos m
      let hε1 := dyadic_epsilon_lt_one h3
      let hsmall := TransverseDyadicRates.epsilon_le h3
      let s := chosenRun hε hε1 hsmall
      ∀ k, Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection →
        A * ε ^ (-(3 / 2 : ℝ)) + C < (functionQueries s k).length := by
  obtain ⟨m, hm, hrate⟩ := TransverseDyadicRates.exists_tailCount_gt A C M
  refine ⟨m, hm, ?_⟩
  dsimp only
  intro k hc
  have hq := chosenRun_certified_query_lower
    (TransverseDyadicRates.epsilon_pos m)
    (dyadic_epsilon_lt_one ((le_max_left 3 M).trans hm))
    (TransverseDyadicRates.epsilon_le ((le_max_left 3 M).trans hm)) k hc
  have hq' : TransverseTailWindow.tailCount (TransverseDyadicRates.epsilon m)
      (TransverseDyadicRates.epsilon_pos m) ≤
      (functionQueries (chosenRun (TransverseDyadicRates.epsilon_pos m)
        (dyadic_epsilon_lt_one ((le_max_left 3 M).trans hm))
        (TransverseDyadicRates.epsilon_le ((le_max_left 3 M).trans hm))) k).length := by
    omega
  exact hrate.trans_le (by exact_mod_cast hq')

/-- No tolerance-independent corrected three-halves bound can promise certification
for this single fixed objective, oracle, initialization, controls and run-selection family. -/
theorem no_uniform_certification_bound :
    ¬∃ A C : ℝ, ∀ (m : ℕ) (hm : 3 ≤ m),
      let ε := TransverseDyadicRates.epsilon m
      let hε := TransverseDyadicRates.epsilon_pos m
      let hε1 := dyadic_epsilon_lt_one hm
      let hsmall := TransverseDyadicRates.epsilon_le hm
      let s := chosenRun hε hε1 hsmall
      ∃ k, Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection ∧
        (functionQueries s k).length ≤ A * ε ^ (-(3 / 2 : ℝ)) + C := by
  rintro ⟨A, C, hbound⟩
  obtain ⟨m, hm, hviol⟩ := exists_rate_violating_run A C 0
  have h3 : 3 ≤ m := (le_max_left 3 0).trans hm
  obtain ⟨k, hc, hq⟩ := hbound m h3
  exact (not_lt_of_ge hq) (hviol k hc)

end Optimization.TransverseCertificationRates
