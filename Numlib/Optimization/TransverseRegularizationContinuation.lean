import Numlib.Optimization.FirstOrderRegularizationInspection
import Numlib.Optimization.ExplicitRegularization
import Numlib.Optimization.ExactRegularizationInnerReturns
import Numlib.Optimization.TransverseCubicModel

/-!
# Operational continuation on a fixed transverse objective

The outer controls and initial requests are fixed independently of the tolerance. Every
noncertified inspected state in the invariant region has a genuine refinement or an accepted
exact-value trial, using an actual global cubic minimum and the squared-gradient inner policy.
-/

noncomputable section
namespace Optimization.TransverseRegularizationContinuation
open TransverseObjective InexactTaylorModels ExplicitRegularization

/-- The fixed outer controls; only the active first-order tolerance varies. -/
def parameters (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) : Parameters where
  p := 2
  q := 1
  order_pos := by norm_num
  order_le := by norm_num
  epsilon := fun _ => ε
  epsilon_pos := fun _ _ _ => hε
  epsilon_lt_one := fun _ _ _ => hε1
  theta := 7 / 8
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  fraction := 1 / 4
  fraction_pos := by norm_num
  fraction_le_one := by norm_num
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num
  kappaInitial := 1
  kappaInitial_nonneg := by norm_num
  kappaStep := 1 / 32
  gammaAccuracy := 1 / 2
  kappaStep_pos := by norm_num
  gammaAccuracy_pos := by norm_num
  gammaAccuracy_lt_one := by norm_num
  step_acceptance := by norm_num
  step_success := by norm_num

/-- The fixed initial point, all unit requests and radii, and an empty value cache. -/
def initialState : State Plane :=
  ⟨⟨point 0 1, 2, fun _ => 1, fun _ => 1, true⟩, none⟩

/-- The region preserved by actual global-minimum continuations. Every request is positive;
the current cache may contain the request of a previous accepted endpoint. -/
def Invariant (a : State Plane) : Prop :=
  0 ≤ a.point 0 ∧ a.point 0 ≤ 1 ∧ 1 ≤ a.point 1 ∧
    ‖fderiv ℝ objective a.point‖ < 1 ∧ a.sigma = 2 ∧
    a.radii = (fun _ => 1) ∧ ∀ i, 0 < a.request i

/-- The fixed initial state lies in the continuation region. -/
theorem initialState_invariant : Invariant initialState := by
  have hg := first_gap_initial
  rw [TaylorCriticality.gapOn_taylorDecrement_one _ _ (by norm_num)] at hg
  norm_num only [one_mul] at hg
  refine ⟨by norm_num [initialState], by norm_num [initialState],
    by norm_num [initialState], ?_, rfl, rfl, fun _ => by norm_num [initialState]⟩
  change ‖fderiv ℝ objective (point 0 1)‖ < 1
  linarith

/-- A complete actual inspection exists at every state with unit incoming radii. -/
theorem exists_inspection {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (ha : Invariant a) :
    Nonempty (Inspection (parameters ε hε hε1) exactOracle.derivative a) := by
  apply InexactRegularization.exists_firstOrderInspection _ rfl
  rw [ha.2.2.2.2.2.1]
  norm_num

/-- Actual accuracy refinement preserves the continuation region and the previous value cache. -/
theorem invariant_refine {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {a : State Plane} (ha : Invariant a) :
    Invariant (refine (parameters ε hε hε1) a) := by
  rcases ha with ⟨hx0, hx1, hy, hg, hσ, hr, hh⟩
  exact ⟨hx0, hx1, hy, hg, hσ, hr,
    fun i => mul_pos (parameters ε hε hε1).gammaAccuracy_pos (hh i)⟩

/-- A fresh trial requests both actual endpoint values at half the allowed shared budget. -/
def freshValueTrial {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (s : Plane)
    (hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 s) :
    ValueTrial (parameters ε hε hε1) exactOracle a s where
  request := (1 / 32) * decrement (exactOracle.derivative a.point a.request) 2 s / 2
  request_pos := by positivity
  budget := by
    change (1 / 32 : ℝ) * decrement (exactOracle.derivative a.point a.request) 2 s / 2 ≤
      (1 / 32) * decrement (exactOracle.derivative a.point a.request) 2 s
    linarith
  currentRequest := (1 / 32) * decrement (exactOracle.derivative a.point a.request) 2 s / 2
  current_pos := by positivity
  current_le := le_rfl
  recompute := true
  fresh_request := fun _ => rfl
  cached_request := by simp

/-- The fresh trial records precisely the old and candidate endpoint requests. -/
theorem freshValueTrial_queries {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (s : Plane)
    (hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 s) :
    let v := freshValueTrial hε hε1 a s hp
    v.queries = [(a.point, v.request), (a.point + s, v.request)] := rfl

/-- Exact requested endpoint values recover the true Taylor ratio for a nonzero step. -/
theorem freshValueTrial_ratio {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (s : Plane) (hs : s ≠ 0)
    (hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 s) :
    (freshValueTrial hε hε1 a s hp).ratio =
      HigherOrderRegularization.ratio objective 2 a.point s := by
  simp only [ValueTrial.ratio, exactOracle_value, HigherOrderRegularization.ratio,
    ite_eq_right hs, show exactOracle.derivative a.point a.request =
      (fun i => iteratedFDeriv ℝ i objective a.point) from rfl,
    decrement_iteratedFDeriv, TaylorCriticality.taylorDecrement_eq,
    RegularizedTaylorModel.taylorModel_zero, parameters]

/-- A very successful exact trial legally keeps the fixed regularization parameter two. -/
theorem parameterUpdate_two {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hρ : 1 ≤ ρ) :
    HigherOrderApproximateRegularization.ParameterUpdate
      (parameters ε hε hε1).toImplicitParameters.toParameters ρ 2 2 := by
  have hρ' : (1 / 2 : ℝ) ≤ ρ := by linarith
  norm_num [HigherOrderApproximateRegularization.ParameterUpdate, parameters, hρ']

/-- The very-successful update remains legal when the incoming parameter is presented
through an equality with the fixed value two. -/
theorem parameterUpdate_of_eq_two {ε ρ σ : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hσ : σ = 2) (hρ : 1 ≤ ρ) :
    HigherOrderApproximateRegularization.ParameterUpdate
      (parameters ε hε hε1).toImplicitParameters.toParameters ρ σ 2 := by
  subst σ
  exact parameterUpdate_two hε hε1 hρ

/-- Every noncertified actual inspection has a legal next outer transition preserving the
fixed-objective invariant. The inner return is constructed from an attained global minimum. -/
theorem exists_successor {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (ha : Invariant a)
    (I : Inspection (parameters ε hε hε1) exactOracle.derivative a)
    (hn : ¬Certified (parameters ε hε hε1) a I) :
    ∃ (b : State Plane) (trial accepted : Bool) (queries : List (Plane × ℝ)),
      Invariant b ∧ ‖fderiv ℝ objective b.point‖ ≤ ‖fderiv ℝ objective a.point‖ ∧
        Transition (parameters ε hε hε1) exactOracle a I b trial accepted queries := by
  classical
  by_cases hall : I.order = (parameters ε hε hε1).q + 1
  · have herr : ¬ErrorCheck (parameters ε hε hε1) a I := fun he => hn ⟨hall, he⟩
    exact ⟨refine (parameters ε hε hε1) a, false, false, [], invariant_refine hε hε1 ha, le_rfl,
      Transition.refineInspection hall herr⟩
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
      · convert Transition.trial hq R hacc v 2
          (parameterUpdate_of_eq_two hε hε1 hσ hρ) using 1
        · exact (decide_eq_true haccept).symm
        · rfl
    · exact ⟨refine (parameters ε hε hε1) a, false, false, [],
        invariant_refine hε hε1 ⟨hx0, hx1, hy, hg, hσ, hr, hh⟩, le_rfl,
        Transition.refineStep hq R hacc⟩

/-- An inspected state in the invariant region, used for ordinary natural recursion. -/
structure Node (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) where
  state : State Plane
  valid : Invariant state
  inspection : Inspection (parameters ε hε hε1) exactOracle.derivative state

private structure Next {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} (u : Node ε hε hε1) where
  node : Node ε hε hε1
  trial : Bool
  accepted : Bool
  queries : List (Plane × ℝ)
  slope_nonincrease : ‖fderiv ℝ objective node.state.point‖ ≤
    ‖fderiv ℝ objective u.state.point‖
  legal : ¬Certified (parameters ε hε hε1) u.state u.inspection →
    Transition (parameters ε hε hε1) exactOracle u.state u.inspection node.state
      trial accepted queries

private def next {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} (u : Node ε hε hε1) : Next u := by
  classical
  by_cases hc : Certified (parameters ε hε hε1) u.state u.inspection
  · exact ⟨u, false, false, [], le_rfl, fun hn => False.elim (hn hc)⟩
  · have hex : Nonempty (Next u) := by
      obtain ⟨b, t, ac, qs, hb, hg, ht⟩ :=
        exists_successor hε hε1 u.state u.valid u.inspection hc
      exact ⟨⟨⟨b, hb, Classical.choice (exists_inspection hε hε1 b hb)⟩,
        t, ac, qs, hg, fun _ => ht⟩⟩
    exact Classical.choice hex

private def nodes {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1} (u : Node ε hε hε1) :
    ℕ → Node ε hε hε1 := Nat.rec u (fun _ v => (next v).node)

private theorem nodes_slope_le {ε : ℝ} {hε : 0 < ε} {hε1 : ε < 1}
    (u : Node ε hε hε1) (k : ℕ) :
    ‖fderiv ℝ objective (nodes u k).state.point‖ ≤ ‖fderiv ℝ objective u.state.point‖ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (next (nodes u k)).slope_nonincrease.trans ih

/-- A full operational run starts at the fixed initialization. The ordinary natural
recursion freezes its state and inspection after certification, and uses legal successors
at every earlier index. The derivative norm never exceeds its initial value; no eventual
stopping assumption is made. -/
theorem exists_isExecution_with_slope_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (state : ℕ → State Plane)
      (inspection : ∀ k, Inspection (parameters ε hε hε1) exactOracle.derivative (state k))
      (trial accepted : ℕ → Bool) (queries : ℕ → List (Plane × ℝ)),
      state 0 = initialState ∧ (∀ k, Invariant (state k)) ∧
      (∀ k, ‖fderiv ℝ objective (state k).point‖ ≤
        ‖fderiv ℝ objective initialState.point‖) ∧
      IsExecution (parameters ε hε hε1) exactOracle state inspection trial accepted queries := by
  let u : Node ε hε hε1 := ⟨initialState, initialState_invariant,
    Classical.choice (exists_inspection hε hε1 initialState initialState_invariant)⟩
  let state := fun k => (nodes u k).state
  let inspection := fun k => (nodes u k).inspection
  let trial := fun k => (next (nodes u k)).trial
  let accepted := fun k => (next (nodes u k)).accepted
  let queries := fun k => (next (nodes u k)).queries
  refine ⟨state, inspection, trial, accepted, queries, rfl,
    fun k => (nodes u k).valid, fun k => nodes_slope_le u k, ?_⟩
  intro N hn
  refine ⟨{
    state := state
    inspection := inspection
    trial := trial
    accepted := accepted
    queries := queries
    initial_fresh := rfl
    initial_cache := rfl
    initial_sigma := by norm_num [state, nodes, u, initialState, parameters]
    initial_radii := by
      intro j _ _
      constructor <;> norm_num [state, nodes, u, initialState]
    initial_tolerance := by
      intro j _ _
      exact hε1.le
    initial_request := by intro i _; norm_num [state, nodes, u, initialState]
    initial_request_le := by intro i _; norm_num [state, nodes, u, initialState, parameters]
    transition := fun k hk => (next (nodes u k)).legal (hn k hk) }, rfl, HEq.rfl, rfl, rfl, rfl⟩

/-- The fixed initialization has a full legal operational continuation. -/
theorem exists_isExecution {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (state : ℕ → State Plane)
      (inspection : ∀ k, Inspection (parameters ε hε hε1) exactOracle.derivative (state k))
      (trial accepted : ℕ → Bool) (queries : ℕ → List (Plane × ℝ)),
      state 0 = initialState ∧ (∀ k, Invariant (state k)) ∧
      IsExecution (parameters ε hε hε1) exactOracle state inspection trial accepted queries := by
  obtain ⟨state, inspection, trial, accepted, queries, hzero, hv, _, hr⟩ :=
    exists_isExecution_with_slope_bound hε hε1
  exact ⟨state, inspection, trial, accepted, queries, hzero, hv, hr⟩

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

/-- Every actual finite prefix whose inspected states remain in the invariant region extends
to a full execution with exactly the same initial state, inspections, event labels and queries
through that prefix. Later noncertified states have legal transitions in the invariant region,
and their derivative norms stay below every strict upper bound valid at the prefix endpoint. -/
theorem exists_isExecution_extension_with_slope_bound {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) {N : ℕ}
    (r : Execution (parameters ε hε hε1) exactOracle N)
    (hv : ∀ k, k ≤ N → Invariant (r.state k)) :
    ∃ (state : ℕ → State Plane)
      (inspection : ∀ k, Inspection (parameters ε hε hε1) exactOracle.derivative (state k))
      (trial accepted : ℕ → Bool) (queries : ℕ → List (Plane × ℝ)),
      (∀ k, k ≤ N → state k = r.state k ∧ HEq (inspection k) (r.inspection k)) ∧
      (∀ k, k < N → trial k = r.trial k ∧ accepted k = r.accepted k ∧
        queries k = r.queries k) ∧
      (∀ k, Invariant (state k)) ∧
      (∀ k, N ≤ k → ‖fderiv ℝ objective (state k).point‖ ≤
        ‖fderiv ℝ objective (r.state N).point‖) ∧
      IsExecution (parameters ε hε hε1) exactOracle state inspection trial accepted queries := by
  classical
  let u := splicedNodes r hv
  let state := fun k => (u k).state
  let inspection := fun k => (u k).inspection
  let trial := fun k => if k < N then r.trial k else (next (u k)).trial
  let accepted := fun k => if k < N then r.accepted k else (next (u k)).accepted
  let queries := fun k => if k < N then r.queries k else (next (u k)).queries
  have heq (k : ℕ) (hk : k ≤ N) : u k = ⟨r.state k, hv k hk, r.inspection k⟩ :=
    splicedNodes_prefix r hv hk
  refine ⟨state, inspection, trial, accepted, queries, ?_, ?_,
    fun k => (u k).valid, ?_, ?_⟩
  · intro k hk
    dsimp only [state, inspection]
    rw [heq k hk]
    exact ⟨rfl, HEq.rfl⟩
  · intro k hk
    exact ⟨ite_eq_left hk, ite_eq_left hk, ite_eq_left hk⟩
  · intro k hk
    have he : k = N + (k - N) := by omega
    change ‖fderiv ℝ objective (splicedNodes r hv k).state.point‖ ≤ _
    rw [he]
    exact splicedNodes_tail_slope_le r hv (k - N)
  · intro M hn
    have hzero : state 0 = r.state 0 := congrArg Node.state (heq 0 (Nat.zero_le N))
    refine ⟨{
      state := state
      inspection := inspection
      trial := trial
      accepted := accepted
      queries := queries
      initial_fresh := by rw [hzero]; exact r.initial_fresh
      initial_cache := by rw [hzero]; exact r.initial_cache
      initial_sigma := by rw [hzero]; exact r.initial_sigma
      initial_radii := by rw [hzero]; exact r.initial_radii
      initial_tolerance := by rw [hzero]; exact r.initial_tolerance
      initial_request := by rw [hzero]; exact r.initial_request
      initial_request_le := by rw [hzero]; exact r.initial_request_le
      transition := ?_ }, rfl, HEq.rfl, rfl, rfl, rfl⟩
    intro k hk
    by_cases hkN : k < N
    · dsimp only [state, inspection, trial, accepted, queries]
      rw [heq k hkN.le, heq (k + 1) (by omega)]
      simpa only [ite_eq_left hkN] using r.transition k hkN
    · have hnext : u (k + 1) = (next (u k)).node := by
        simp only [u, splicedNodes, dite_eq_right hkN]
      dsimp only [state, inspection, trial, accepted, queries]
      rw [hnext]
      simpa only [ite_eq_right hkN] using (next (u k)).legal (hn k hk)

/-- A finite actual prefix extends without changing any inspected prefix state or query
log. Its endpoint cache and requests seed the legal invariant continuation. -/
theorem exists_isExecution_extension {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {N : ℕ}
    (r : Execution (parameters ε hε hε1) exactOracle N)
    (hv : ∀ k, k ≤ N → Invariant (r.state k)) :
    ∃ (state : ℕ → State Plane)
      (inspection : ∀ k, Inspection (parameters ε hε hε1) exactOracle.derivative (state k))
      (trial accepted : ℕ → Bool) (queries : ℕ → List (Plane × ℝ)),
      (∀ k, k ≤ N → state k = r.state k ∧ HEq (inspection k) (r.inspection k)) ∧
      (∀ k, k < N → trial k = r.trial k ∧ accepted k = r.accepted k ∧
        queries k = r.queries k) ∧
      (∀ k, Invariant (state k)) ∧
      IsExecution (parameters ε hε hε1) exactOracle state inspection trial accepted queries := by
  obtain ⟨state, inspection, trial, accepted, queries, hp, hl, hv', _, hr⟩ :=
    exists_isExecution_extension_with_slope_bound hε hε1 r hv
  exact ⟨state, inspection, trial, accepted, queries, hp, hl, hv', hr⟩

end Optimization.TransverseRegularizationContinuation
