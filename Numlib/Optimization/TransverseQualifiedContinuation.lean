import Numlib.Optimization.TransverseRegularizationContinuation

/-!
# Continuation retaining actual returned inner calls

Chosen branch data retain every actual inner result, its returned unit radii and its
squared-gradient initialization fraction, including calls discarded by accuracy refinement.
Fresh trials retain their actual requests and cache update. Natural recursion selects this
data before projecting to the ordinary outer transition relation.
-/

noncomputable section
namespace Optimization.TransverseQualifiedContinuation
open TransverseObjective InexactTaylorModels ExplicitRegularization
open TransverseRegularizationContinuation

/-- An actual returned inner call with the fixed fraction rule and unit returned radii. -/
structure Returned {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    {a : State Plane} (I : Inspection (parameters ε hε hε1) exactOracle.derivative a)
    (hq : I.order ≤ (parameters ε hε hε1).q) where
  result : InexactRegularization.InnerResult (parameters ε hε hε1).toImplicitParameters 0
    (exactOracle.derivative a.point a.request) a.sigma I.radii (I.direction hq)
  radii_eq : result.radii = fun _ => 1
  mu_eq : (result.execution.state 0).mu = ‖fderiv ℝ objective a.point‖ ^ 2 / 100

/-- Every active returned radius required in the low-order source policy equals one. -/
theorem Returned.radius_eq_one {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    {a : State Plane} {I : Inspection (parameters ε hε hε1) exactOracle.derivative a}
    {hq : I.order ≤ (parameters ε hε hε1).q} (R : Returned I hq) (j : ℕ) :
    R.result.radii j = 1 := congrFun R.radii_eq j

/-- Operational branch data retain the actual returned call before selecting a successor.
The trial branch uses the two fresh value requests and the actual trial-state cache update. -/
inductive Branch {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (I : Inspection (parameters ε hε hε1) exactOracle.derivative a) :
    State Plane → Bool → Bool → List (Plane × ℝ) → Type where
  | refineInspection (hall : I.order = (parameters ε hε hε1).q + 1)
      (herr : ¬ErrorCheck (parameters ε hε hε1) a I) :
      Branch hε hε1 a I (refine (parameters ε hε hε1) a) false false []
  | refineStep (hq : I.order ≤ (parameters ε hε hε1).q) (R : Returned I hq)
      (hinaccurate : ¬InexactRegularization.StepAccurate
        (parameters ε hε hε1).toImplicitParameters (parameters ε hε hε1).q
        a.request R.result.step) :
      Branch hε hε1 a I (refine (parameters ε hε hε1) a) false false []
  | trial (hq : I.order ≤ (parameters ε hε hε1).q) (R : Returned I hq)
      (haccurate : InexactRegularization.StepAccurate
        (parameters ε hε hε1).toImplicitParameters (parameters ε hε hε1).q
        a.request R.result.step)
      (hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 R.result.step)
      (hupdate : HigherOrderApproximateRegularization.ParameterUpdate
        (parameters ε hε hε1).toImplicitParameters.toParameters
        (freshValueTrial hε hε1 a R.result.step hp).ratio a.sigma 2) :
      Branch hε hε1 a I
        (trialState a I hq R.result (freshValueTrial hε hε1 a R.result.step hp) 2) true
        (decide ((parameters ε hε hε1).eta1 ≤
          (freshValueTrial hε hε1 a R.result.step hp).ratio))
        (freshValueTrial hε hε1 a R.result.step hp).queries

/-- Forgetting the retained witness data gives precisely an ordinary legal transition. -/
theorem Branch.transition {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    {a b : State Plane} {I : Inspection (parameters ε hε hε1) exactOracle.derivative a}
    {t ac : Bool} {qs : List (Plane × ℝ)} (B : Branch hε hε1 a I b t ac qs) :
    Transition (parameters ε hε hε1) exactOracle a I b t ac qs := by
  cases B with
  | refineInspection hall herr => exact Transition.refineInspection hall herr
  | refineStep hq R hi => exact Transition.refineStep hq R.result hi
  | trial hq R ha hp hu => exact Transition.trial hq R.result ha _ 2 hu

/-- The actual query list contains two fresh value calls on a trial and no calls on a
refinement branch. This counts the stored endpoint queries themselves. -/
theorem Branch.queries_length {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    {a b : State Plane} {I : Inspection (parameters ε hε hε1) exactOracle.derivative a}
    {t ac : Bool} {qs : List (Plane × ℝ)} (B : Branch hε hε1 a I b t ac qs) :
    qs.length = if t then 2 else 0 := by
  cases B <;> rfl

/-- Extract the actual chosen inner call, including a return discarded by refinement.
An all-pass inspection refinement makes no inner call. -/
def Branch.innerCall {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    {a b : State Plane} {I : Inspection (parameters ε hε hε1) exactOracle.derivative a}
    {t ac : Bool} {qs : List (Plane × ℝ)} (B : Branch hε hε1 a I b t ac qs) :
    Option (Σ' hq : I.order ≤ (parameters ε hε hε1).q, Returned I hq) :=
  match B with
  | .refineInspection _ _ => none
  | .refineStep hq R _ => some ⟨hq, R⟩
  | .trial hq R _ _ _ => some ⟨hq, R⟩

/-- Every extracted call has the actual unit returned radii, including the source's
active low orders; the conclusion refers to the chosen return rather than the incoming state. -/
theorem Branch.innerCall_radii {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    {a b : State Plane} {I : Inspection (parameters ε hε hε1) exactOracle.derivative a}
    {t ac : Bool} {qs : List (Plane × ℝ)} (B : Branch hε hε1 a I b t ac qs)
    {hq : I.order ≤ (parameters ε hε hε1).q} {R : Returned I hq}
    (_hcall : B.innerCall = some ⟨hq, R⟩) (j : ℕ) : R.result.radii j = 1 :=
  R.radius_eq_one j

/-- Every extracted call retains the actual initialization fraction from its inner execution. -/
theorem Branch.innerCall_mu {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    {a b : State Plane} {I : Inspection (parameters ε hε hε1) exactOracle.derivative a}
    {t ac : Bool} {qs : List (Plane × ℝ)} (B : Branch hε hε1 a I b t ac qs)
    {hq : I.order ≤ (parameters ε hε hε1).q} {R : Returned I hq}
    (_hcall : B.innerCall = some ⟨hq, R⟩) :
    (R.result.execution.state 0).mu = ‖fderiv ℝ objective a.point‖ ^ 2 / 100 := R.mu_eq

/-- There are no requested orders from three through the active first-order target. -/
theorem higher_radius_policy_vacuous {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (j : ℕ) :
    ¬(3 ≤ j ∧ j ≤ (parameters ε hε hε1).q) := by
  change ¬(3 ≤ j ∧ j ≤ 1)
  omega

/-- Every noncertified actual inspection has a legal next outer transition preserving the
fixed-objective invariant. The inner return is constructed from an attained global minimum. -/
theorem exists_qualified_successor {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (ha : Invariant a)
    (I : Inspection (parameters ε hε hε1) exactOracle.derivative a)
    (hn : ¬Certified (parameters ε hε hε1) a I) :
    ∃ (b : State Plane) (trial accepted : Bool) (queries : List (Plane × ℝ)),
      Invariant b ∧ ‖fderiv ℝ objective b.point‖ ≤ ‖fderiv ℝ objective a.point‖ ∧
        Nonempty (Branch hε hε1 a I b trial accepted queries) := by
  classical
  by_cases hall : I.order = (parameters ε hε hε1).q + 1
  · have herr : ¬ErrorCheck (parameters ε hε hε1) a I := fun he => hn ⟨hall, he⟩
    exact ⟨refine (parameters ε hε hε1) a, false, false, [], invariant_refine hε hε1 ha, le_rfl,
      ⟨Branch.refineInspection hall herr⟩⟩
  · have hq : I.order ≤ (parameters ε hε hε1).q := by
      change I.order ≤ 1
      have ho : I.order ≤ 2 := I.order_le
      have hn2 : I.order ≠ 2 := hall
      omega
    rcases ha with ⟨hx0, hx1, hy, hg, hσ, hr, hh⟩
    obtain ⟨z, hm, hz, hzshort, hx0', hx1', hy', hratio, hgpos', hg'⟩ :=
      TransverseCubicModel.exists_short_accepted_minimizer hx0 hx1 hy
        (by norm_num : (1 : ℝ) ≤ 1) (by simpa only [point_coords] using hg)
    have hmon := TransverseCubicModel.actual_minimizer_norm_fderiv_le hx0 hx1 hy hm
    simp only [point_coords] at hm hratio hgpos' hg' hmon
    have hg0 : fderiv ℝ objective a.point ≠ 0 := by
      simpa only [point_coords] using
        TransverseCubicModel.fderiv_objective_ne_zero_of_tail (a.point 0) hy
    have hmP : ∀ t, HigherOrderApproximateRegularization.model objective
        (parameters ε hε hε1).p a.point a.sigma z ≤
        HigherOrderApproximateRegularization.model objective
          (parameters ε hε hε1).p a.point a.sigma t := by
      simpa only [parameters, hσ] using hm
    let R := InexactRegularization.squaredGradientGlobalMinInnerResult
      (parameters ε hε hε1).toImplicitParameters rfl objective a.point 0 a.sigma
      I.radii (I.direction hq) z
      hmP hg0 hg.le hzshort
    have hR : R.step = z := rfl
    have hRr : R.radii = fun _ => 1 :=
      InexactRegularization.squaredGradientGlobalMinInnerResult_radii _ rfl _ _ _ _ _ _ _
        hmP hg0 hg.le hzshort
    let Q : Returned I hq := ⟨R, hRr, rfl⟩
    by_cases hacc : InexactRegularization.StepAccurate
        (parameters ε hε hε1).toImplicitParameters (parameters ε hε hε1).q a.request R.step
    · have hpred : 0 < decrement (exactOracle.derivative a.point a.request) 2 R.step := by
        have hdec := HigherOrderRegularization.predicted_decrease_of_model_le (hm 0)
        have hnorm : 0 < ‖z‖ ^ 3 := pow_pos (norm_pos_iff.mpr hz) 3
        change 0 < decrement (fun i => iteratedFDeriv ℝ i objective a.point) 2 R.step
        rw [hR, decrement_iteratedFDeriv, TaylorCriticality.taylorDecrement_eq]
        norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul,
          Nat.cast_one, RegularizedTaylorModel.taylorModel_zero] at hdec
        linarith
      let v := freshValueTrial hε hε1 a R.step hpred
      have hρ : 1 ≤ v.ratio := by
        rw [freshValueTrial_ratio hε hε1 a R.step (by simpa only [hR] using hz) hpred, hR]
        exact hratio
      have haccept : (parameters ε hε hε1).eta1 ≤ v.ratio := by
        change (1 / 4 : ℝ) ≤ v.ratio
        linarith
      have haccept' : (parameters ε hε hε1).eta1 ≤ v.ratio := haccept
      refine ⟨trialState a I hq R v 2, true, true, v.queries, ?_, ?_, ?_⟩
      · have he : trialState a I hq R v 2 =
            ⟨⟨a.point + R.step, 2, R.radii, a.request, true⟩, some v.request⟩ :=
          ite_eq_left haccept'
        rw [he]
        refine ⟨?_, ?_, ?_, ?_, rfl, hRr, hh⟩
        · simpa only [hR, PiLp.add_apply] using hx0'
        · have : a.point 0 + z 0 ≤ 1 := hx1'.trans hx1
          simpa only [hR, PiLp.add_apply] using this
        · change 1 ≤ (a.point + R.step) 1
          simp only [hR, PiLp.add_apply]
          linarith
        · simpa only [hR] using hg'
      · have he : trialState a I hq R v 2 =
            ⟨⟨a.point + R.step, 2, R.radii, a.request, true⟩, some v.request⟩ :=
          ite_eq_left haccept'
        rw [he]
        simpa only [hR] using hmon
      · refine ⟨?_⟩
        convert Branch.trial hq Q hacc hpred
          (parameterUpdate_of_eq_two hε hε1 hσ hρ) using 1
        · rfl
        · exact (decide_eq_true haccept).symm
        · rfl
    · exact ⟨refine (parameters ε hε hε1) a, false, false, [],
        invariant_refine hε hε1 ⟨hx0, hx1, hy, hg, hσ, hr, hh⟩, le_rfl,
        ⟨Branch.refineStep hq Q hacc⟩⟩

private structure Next {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} (u : Node ε hε hε1) where
  node : Node ε hε hε1
  trial : Bool
  accepted : Bool
  queries : List (Plane × ℝ)
  slope_nonincrease : ‖fderiv ℝ objective node.state.point‖ ≤
    ‖fderiv ℝ objective u.state.point‖
  branch : ¬Certified (parameters ε hε hε1) u.state u.inspection →
    Branch hε hε1 u.state u.inspection node.state
      trial accepted queries

private def next {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} (u : Node ε hε hε1) : Next u := by
  classical
  by_cases hc : Certified (parameters ε hε hε1) u.state u.inspection
  · exact ⟨u, false, false, [], le_rfl, fun hn => False.elim (hn hc)⟩
  · have hex : Nonempty (Next u) := by
      obtain ⟨b, t, ac, qs, hb, hg, ht⟩ :=
        exists_qualified_successor hε hε1 u.state u.valid u.inspection hc
      exact ⟨⟨⟨b, hb, Classical.choice (exists_inspection hε hε1 b hb)⟩,
        t, ac, qs, hg, fun _ => Classical.choice ht⟩⟩
    exact Classical.choice hex

private def nodes {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} (u : Node ε hε hε1) :
    ℕ → Node ε hε hε1 := Nat.rec u (fun _ v => (next v).node)

private theorem nodes_slope_le {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    (u : Node ε hε hε1) (k : ℕ) :
    ‖fderiv ℝ objective (nodes u k).state.point‖ ≤ ‖fderiv ℝ objective u.state.point‖ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (next (nodes u k)).slope_nonincrease.trans ih

/-- A full sequence retains actual chosen branch data at every noncertified inspection.
Its nodes carry the invariant and their actual dependent inspections. -/
structure Run (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) where
  node : ℕ → Node ε hε hε1
  trial : ℕ → Bool
  accepted : ℕ → Bool
  queries : ℕ → List (Plane × ℝ)
  branch : ∀ k, ¬Certified (parameters ε hε hε1) (node k).state (node k).inspection →
    Branch hε hε1 (node k).state (node k).inspection (node (k + 1)).state
      (trial k) (accepted k) (queries k)

/-- A retained-branch run is an ordinary full execution whenever its initial state agrees
with that of an initialized finite execution. -/
theorem Run.isExecution {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    (s : Run ε hε hε1) {N : ℕ} (r : Execution (parameters ε hε hε1) exactOracle N)
    (hzero : (s.node 0).state = r.state 0) :
    IsExecution (parameters ε hε hε1) exactOracle
      (fun k => (s.node k).state) (fun k => (s.node k).inspection)
      s.trial s.accepted s.queries := by
  intro M hn
  refine ⟨{
    state := fun k => (s.node k).state
    inspection := fun k => (s.node k).inspection
    trial := s.trial
    accepted := s.accepted
    queries := s.queries
    initial_fresh := by rw [hzero]; exact r.initial_fresh
    initial_cache := by rw [hzero]; exact r.initial_cache
    initial_sigma := by rw [hzero]; exact r.initial_sigma
    initial_radii := by rw [hzero]; exact r.initial_radii
    initial_tolerance := by rw [hzero]; exact r.initial_tolerance
    initial_request := by rw [hzero]; exact r.initial_request
    initial_request_le := by rw [hzero]; exact r.initial_request_le
    transition := fun k hk => (s.branch k (hn k hk)).transition },
    rfl, HEq.rfl, rfl, rfl, rfl⟩

private def continued {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    (u : Node ε hε hε1) : Run ε hε hε1 where
  node := nodes u
  trial k := (next (nodes u k)).trial
  accepted k := (next (nodes u k)).accepted
  queries k := (next (nodes u k)).queries
  branch k := (next (nodes u k)).branch

private theorem next_frozen {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    (u : Node ε hε hε1)
    (hc : Certified (parameters ε hε hε1) u.state u.inspection) :
    (next u).node = u := by
  simp only [next, dite_eq_left hc]

/-- Qualified continuation from the fixed initialization preserves the true-gradient cap,
retains every actual returned call and freezes both state and inspection after certification. -/
theorem exists_run {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s : Run ε hε hε1,
      (s.node 0).state = initialState ∧
      (∀ k, ‖fderiv ℝ objective (s.node k).state.point‖ ≤
        ‖fderiv ℝ objective initialState.point‖) ∧
      (∀ k, Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection →
        s.node (k + 1) = s.node k) ∧
      IsExecution (parameters ε hε hε1) exactOracle
        (fun k => (s.node k).state) (fun k => (s.node k).inspection)
        s.trial s.accepted s.queries := by
  let u : Node ε hε hε1 := ⟨initialState, initialState_invariant,
    Classical.choice (exists_inspection hε hε1 initialState initialState_invariant)⟩
  refine ⟨continued u, rfl, fun k => nodes_slope_le u k, ?_, ?_⟩
  · intro k hc
    exact next_frozen (nodes u k) hc
  · let r : Execution (parameters ε hε hε1) exactOracle 0 := {
      state := fun _ => initialState
      inspection := fun _ => u.inspection
      trial := fun _ => false
      accepted := fun _ => false
      queries := fun _ => []
      initial_fresh := rfl
      initial_cache := rfl
      initial_sigma := by norm_num [initialState, parameters]
      initial_radii := by intro j _ _; constructor <;> norm_num [initialState]
      initial_tolerance := by intro j _ _; exact hε1.le
      initial_request := by intro i _; norm_num [initialState]
      initial_request_le := by intro i _; norm_num [initialState, parameters]
      transition := by intro k hk; omega }
    exact (continued u).isExecution r rfl

private def splicedNodes {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} {N : ℕ}
    (r : Execution (parameters ε hε hε1) exactOracle N)
    (hv : ∀ k, k ≤ N → Invariant (r.state k)) : ℕ → Node ε hε hε1 :=
  Nat.rec ⟨r.state 0, hv 0 (Nat.zero_le N), r.inspection 0⟩
    (fun k u => if hk : k < N then
      ⟨r.state (k + 1), hv (k + 1) (by omega), r.inspection (k + 1)⟩ else (next u).node)

private theorem splicedNodes_prefix {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} {N : ℕ}
    (r : Execution (parameters ε hε hε1) exactOracle N)
    (hv : ∀ k, k ≤ N → Invariant (r.state k)) {k : ℕ} (hk : k ≤ N) :
    splicedNodes r hv k = ⟨r.state k, hv k hk, r.inspection k⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : k < N := by omega
    simp only [splicedNodes, dite_eq_left h]

private theorem splicedNodes_tail_slope_le {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} {N : ℕ}
    (r : Execution (parameters ε hε hε1) exactOracle N)
    (hv : ∀ k, k ≤ N → Invariant (r.state k)) (n : ℕ) :
    ‖fderiv ℝ objective (splicedNodes r hv (N + n)).state.point‖ ≤
      ‖fderiv ℝ objective (r.state N).point‖ := by
  induction n with
  | zero =>
    rw [Nat.add_zero, splicedNodes_prefix r hv le_rfl]
  | succ n ih =>
    have hn : ¬N + n < N := by omega
    change ‖fderiv ℝ objective (splicedNodes r hv ((N + n) + 1)).state.point‖ ≤ _
    have he : splicedNodes r hv ((N + n) + 1) =
        (next (splicedNodes r hv (N + n))).node := by
      simp only [splicedNodes, dite_eq_right hn]
    rw [he]
    exact (next (splicedNodes r hv (N + n))).slope_nonincrease.trans ih

/-- A finite actual prefix extends with its exact inspected nodes, events and query lists.
Qualification is required of the prefix's actual branch witnesses, including hidden returned
calls used by refinement. The continuation freezes at every subsequent certificate and its
true gradient stays below the prefix endpoint's gradient. -/
theorem exists_run_extension {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {N : ℕ}
    (r : Execution (parameters ε hε hε1) exactOracle N)
    (hv : ∀ k, k ≤ N → Invariant (r.state k))
    (hb : ∀ k, k < N → Branch hε hε1 (r.state k) (r.inspection k)
      (r.state (k + 1)) (r.trial k) (r.accepted k) (r.queries k)) :
    ∃ s : Run ε hε hε1,
      (∀ k, (hk : k ≤ N) → s.node k = ⟨r.state k, hv k hk, r.inspection k⟩) ∧
      (∀ k, k < N → s.trial k = r.trial k ∧ s.accepted k = r.accepted k ∧
        s.queries k = r.queries k) ∧
      (∀ k, N ≤ k → ‖fderiv ℝ objective (s.node k).state.point‖ ≤
        ‖fderiv ℝ objective (r.state N).point‖) ∧
      (∀ k, N ≤ k →
        Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection →
        s.node (k + 1) = s.node k) ∧
      IsExecution (parameters ε hε hε1) exactOracle
        (fun k => (s.node k).state) (fun k => (s.node k).inspection)
        s.trial s.accepted s.queries := by
  classical
  let u := splicedNodes r hv
  have heq (k : ℕ) (hk : k ≤ N) : u k = ⟨r.state k, hv k hk, r.inspection k⟩ :=
    splicedNodes_prefix r hv hk
  let s : Run ε hε hε1 := {
    node := u
    trial := fun k => if k < N then r.trial k else (next (u k)).trial
    accepted := fun k => if k < N then r.accepted k else (next (u k)).accepted
    queries := fun k => if k < N then r.queries k else (next (u k)).queries
    branch := by
      intro k hn
      by_cases hk : k < N
      · rw [heq k hk.le, heq (k + 1) (by omega)]
        simpa only [ite_eq_left hk] using hb k hk
      · have hnext : u (k + 1) = (next (u k)).node := by
          simp only [u, splicedNodes, dite_eq_right hk]
        rw [hnext]
        simpa only [ite_eq_right hk] using (next (u k)).branch hn }
  refine ⟨s, heq, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨ite_eq_left hk, ite_eq_left hk, ite_eq_left hk⟩
  · intro k hk
    have he : k = N + (k - N) := by omega
    change ‖fderiv ℝ objective (splicedNodes r hv k).state.point‖ ≤ _
    rw [he]
    exact splicedNodes_tail_slope_le r hv (k - N)
  · intro k hk hc
    change u (k + 1) = u k
    have hkn : ¬k < N := by omega
    have he : u (k + 1) = (next (u k)).node := by
      simp only [u, splicedNodes, dite_eq_right hkn]
    exact he.trans (next_frozen (u k) hc)
  · exact s.isExecution r (congrArg Node.state (heq 0 (Nat.zero_le N)))

end Optimization.TransverseQualifiedContinuation
