import Numlib.Optimization.ExplicitRegularization

/-!
# Certificates, cache invariants and actual payments for explicit regularization

Known derivative errors make an observable completed inspection a true optimality
certificate. Both endpoint errors are charged against the common value budget, including
when the current endpoint reuses an older, more accurate cached value.
-/

noncomputable section
open scoped Nat
namespace Optimization.ExplicitRegularization
open InexactTaylorModels TaylorCriticality
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {P : Parameters} {O : Oracle f P.p}
  {a b : State E} {I : Inspection P O.derivative a} {trial accepted : Bool}
  {queries : List (E × ℝ)}

/-- Every permitted transition preserves the positive regularization floor. -/
theorem Transition.sigma_floor (t : Transition P O a I b trial accepted queries)
    (ha : P.sigmaMin ≤ a.sigma) : P.sigmaMin ≤ b.sigma := by
  cases t with
  | refineInspection => exact ha
  | refineStep => exact ha
  | trial hq s hacc v next hu =>
    have hh := hu.floor_le ha
    unfold trialState
    split_ifs <;> exact hh

/-- Every transition preserves valid radii, restoring incoming radii on refinement. -/
theorem Transition.valid_radii (t : Transition P O a I b trial accepted queries)
    (ha : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii) :
    HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters b.radii := by
  cases t with
  | refineInspection => exact ha
  | refineStep => exact ha
  | trial hq s hacc v next hu =>
    have hi := I.valid_radii ha
    unfold trialState
    split_ifs
    · exact s.valid_radii hi
    · exact hi

/-- A transition contracts positive requests or keeps their exact cache key. -/
theorem Transition.request_bounds (t : Transition P O a I b trial accepted queries)
    {i : ℕ} (hi : 0 < a.request i) :
    0 < b.request i ∧ b.request i ≤ a.request i := by
  cases t with
  | refineInspection =>
    exact ⟨mul_pos P.gammaAccuracy_pos hi,
      mul_le_of_le_one_left hi.le P.gammaAccuracy_lt_one.le⟩
  | refineStep =>
    exact ⟨mul_pos P.gammaAccuracy_pos hi,
      mul_le_of_le_one_left hi.le P.gammaAccuracy_lt_one.le⟩
  | trial => unfold trialState; split_ifs <;> exact ⟨hi, le_rfl⟩

/-- Every available cached value was requested with a positive error allowance. -/
theorem Transition.cache_positive (t : Transition P O a I b trial accepted queries)
    (ha : ∀ h, a.valueCache = some h → 0 < h) :
    ∀ h, b.valueCache = some h → 0 < h := by
  cases t with
  | refineInspection => exact ha
  | refineStep => exact ha
  | trial hq s hacc v next hu =>
    unfold trialState
    split_ifs <;> intro h hh <;> simp only at hh
    · exact (Option.some.inj hh) ▸ v.request_pos
    · exact (Option.some.inj hh) ▸ v.current_pos

/-- Rejected trials reuse exactly the same derivative point and request vector. -/
theorem Transition.rejected_cache (t : Transition P O a I b trial accepted queries)
    (ht : trial = true) (ha : accepted = false) :
    b.point = a.point ∧ b.request = a.request ∧ b.fresh = false := by
  cases t with
  | refineInspection => cases ht
  | refineStep => cases ht
  | trial hq s hacc v next hu =>
    have hn : ¬P.eta1 ≤ v.ratio := by simpa using ha
    simp [trialState, hn]

/-- Accuracy-only branches make no value calls and retain point, parameter, radii and cache. -/
theorem Transition.accuracy_only (t : Transition P O a I b false accepted queries) :
    queries = [] ∧ b.point = a.point ∧ b.sigma = a.sigma ∧ b.radii = a.radii ∧
      b.valueCache = a.valueCache := by
  cases t <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A transition cannot execute past its own observable stopping certificate. -/
theorem Transition.not_certified (t : Transition P O a I b trial accepted queries) :
    ¬Certified P a I := by
  intro hc
  have horder := hc.1
  cases t with
  | refineInspection hall herr => exact herr hc.2
  | refineStep hq => omega
  | trial hq => omega

/-- A value trial can only be formed with a strictly positive actual model decrement. -/
theorem ValueTrial.prediction_pos {s : E} (v : ValueTrial P O a s) :
    0 < decrement (O.derivative a.point a.request) P.p s := by
  exact pos_of_mul_pos_right (v.request_pos.trans_le v.budget) P.kappaStep_pos.le

/-- A cached endpoint meets the new common error budget even when its original request differs. -/
theorem ValueTrial.current_accuracy {s : E} (v : ValueTrial P O a s) :
    |O.value a.point v.currentRequest - f a.point| ≤ v.request :=
  (O.value_accuracy _ _ v.current_pos).trans v.current_le

/-- The actual inexact ratio pays both endpoint errors and retains half the acceptance factor. -/
theorem ValueTrial.accepted_decrease {s : E} (v : ValueTrial P O a s)
    (ha : P.eta1 ≤ v.ratio) :
    P.eta1 * decrement (O.derivative a.point a.request) P.p s / 2 ≤
      f a.point - f (a.point + s) := by
  have hp := v.prediction_pos
  have hb : 2 * v.request ≤
      P.eta1 * decrement (O.derivative a.point a.request) P.p s / 2 := by
    have hc := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp P.step_acceptance
    nlinarith [mul_le_mul_of_nonneg_right hc hp.le, v.budget]
  exact true_decrease_of_inexact_acceptance f a.point (a.point + s) hp
    v.current_accuracy (O.value_accuracy _ _ v.request_pos) ha hb

/-- Actual value-call costs are zero for refinement and between one and two for a trial. -/
theorem Transition.query_length (t : Transition P O a I b trial accepted queries) :
    (if trial then 1 else 0) ≤ queries.length ∧
      queries.length ≤ if trial then 2 else 0 := by
  cases t with
  | refineInspection => simp
  | refineStep => simp
  | trial hq s hacc v next hu =>
    simp only [ValueTrial.queries_length, ↓reduceIte]
    cases v.recompute <;> norm_num

/-- With no cached endpoint, every trial must request both function values. -/
theorem ValueTrial.recompute_of_cache_none {s : E} (v : ValueTrial P O a s)
    (ha : a.valueCache = none) : v.recompute = true := by
  cases hh : v.recompute
  · have hc := v.cached_request hh
    simp [ha] at hc
  · rfl

/-- The true objective is nonincreasing at every operational transition. -/
theorem Transition.objective_nonincrease (t : Transition P O a I b trial accepted queries) :
    f b.point ≤ f a.point := by
  cases t with
  | refineInspection => exact le_rfl
  | refineStep => exact le_rfl
  | trial hq s hacc v next hu =>
    unfold trialState
    split_ifs with hs
    · have hd := v.accepted_decrease hs
      have hp := v.prediction_pos
      have hn : 0 ≤ P.eta1 * decrement (O.derivative a.point a.request) P.p s.step / 2 :=
        div_nonneg (mul_nonneg P.eta1_pos.le hp.le) (by norm_num)
      change f (a.point + s.step) ≤ f a.point
      linarith
    · exact le_rfl

/-- Fresh derivative tensors are needed precisely after a success or accuracy refinement. -/
theorem Transition.fresh_iff (t : Transition P O a I b trial accepted queries) :
    b.fresh = true ↔ accepted = true ∨ trial = false := by
  cases t with
  | refineInspection => simp [refine, InexactRegularization.refine]
  | refineStep => simp [refine, InexactRegularization.refine]
  | trial hq s hacc v next hu =>
    unfold trialState
    split_ifs <;> simp_all

variable {N : ℕ}

/-- All reachable regularization parameters retain their prescribed positive floor. -/
theorem Execution.sigma_floor (r : Execution P O N) {k : ℕ} (hk : k ≤ N) :
    P.sigmaMin ≤ (r.state k).sigma := by
  induction k with
  | zero => exact r.initial_sigma
  | succ k ih => exact (r.transition k (by omega)).sigma_floor (ih (by omega))

/-- Reachable active radii remain positive and at most one. -/
theorem Execution.valid_radii (r : Execution P O N) {k : ℕ} (hk : k ≤ N) :
    HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters (r.state k).radii := by
  induction k with
  | zero => exact r.initial_radii
  | succ k ih => exact (r.transition k (by omega)).valid_radii (ih (by omega))

/-- All reachable active requests are positive and bounded by their initial requests. -/
theorem Execution.request_bounds (r : Execution P O N) {k i : ℕ} (hk : k ≤ N)
    (hi : i ∈ Finset.Icc 1 P.p) :
    0 < (r.state k).request i ∧ (r.state k).request i ≤ (r.state 0).request i := by
  induction k with
  | zero => exact ⟨r.initial_request i hi, le_rfl⟩
  | succ k ih =>
    have hh := ih (by omega)
    have hb := (r.transition k (by omega)).request_bounds hh.1
    exact ⟨hb.1, hb.2.trans hh.2⟩

/-- No actual finite prefix continues after a certificate on its retained inspection. -/
theorem Execution.not_certified (r : Execution P O N) {k : ℕ} (hk : k < N) :
    ¬Certified P (r.state k) (r.inspection k) :=
  (r.transition k hk).not_certified

/-- Without a cache, an actual trial requests both endpoints. -/
theorem Transition.query_length_of_cache_none
    (t : Transition P O a I b trial accepted queries) (ht : trial = true)
    (ha : a.valueCache = none) : queries.length = 2 := by
  cases t with
  | refineInspection => cases ht
  | refineStep => cases ht
  | trial hq s hacc v next hu => simp [v.recompute_of_cache_none ha]

/-- Before the first actual trial, accuracy refinements leave the value cache empty. -/
theorem Execution.cache_none_before_first_trial (r : Execution P O N) {k : ℕ}
    (hk : k ≤ N) (hfirst : ∀ j < k, r.trial j = false) :
    (r.state k).valueCache = none := by
  induction k with
  | zero => exact r.initial_cache
  | succ k ih =>
    have ht := r.transition k (by omega)
    rw [hfirst k (by omega)] at ht
    rw [ht.accuracy_only.2.2.2.2]
    exact ih (by omega) (fun j hj => hfirst j (by omega))

/-- At the first actual trial, including any preceding accuracy refinements, both endpoint
values must be requested. -/
theorem Execution.first_trial_queries (r : Execution P O N) {k : ℕ} (hk : k < N)
    (ht : r.trial k = true) (hfirst : ∀ j < k, r.trial j = false) :
    (r.queries k).length = 2 :=
  (r.transition k hk).query_length_of_cache_none ht
    (r.cache_none_before_first_trial hk.le hfirst)

/-- The exact number of calls in the recorded list is the sum of its actual trial logs. -/
@[simp] theorem Execution.functionQueries_length (r : Execution P O N) :
    r.functionQueries.length = ∑ k ∈ Finset.range N, (r.queries k).length := by
  simp only [Execution.functionQueries, List.length_flatten, List.map_map]
  simpa only [List.toFinset_range, Function.comp_def] using
    (List.sum_toFinset (fun k => (r.queries k).length) (List.nodup_range)).symm

/-- The actual value-query schedule makes at least one and at most two calls per trial. -/
theorem Execution.functionQueries_bounds (r : Execution P O N) :
    ((Finset.range N).filter fun k => r.trial k).card ≤ r.functionQueries.length ∧
      r.functionQueries.length ≤ 2 * ((Finset.range N).filter fun k => r.trial k).card := by
  rw [r.functionQueries_length]
  have hl := Finset.sum_le_sum (s := Finset.range N) (fun k hk =>
    (r.transition k (Finset.mem_range.mp hk)).query_length.1)
  have hu := Finset.sum_le_sum (s := Finset.range N) (fun k hk =>
    (r.transition k (Finset.mem_range.mp hk)).query_length.2)
  constructor
  · simpa using hl
  · simpa [Finset.sum_ite, Nat.mul_comm] using hu

/-- Batch requests retain precisely the fresh inspection keys, including the endpoint. -/
@[simp] theorem Execution.derivativeQueries_length (r : Execution P O N) :
    r.derivativeQueries.length =
      ((Finset.range (N + 1)).filter fun k => (r.state k).fresh).card := by
  simp [Execution.derivativeQueries]

/-- Every actual objective value is nonincreasing along a finite legal execution. -/
theorem Execution.objective_nonincrease (r : Execution P O N) {k : ℕ} (hk : k < N) :
    f (r.state (k + 1)).point ≤ f (r.state k).point :=
  (r.transition k hk).objective_nonincrease

/-- Known absolute errors and the observable certificate prove true optimality at the
actual reachable post-inspection radii. This is the certification clause only, independent
of any unproved global parameter bound or request-threshold reachability assertion. -/
theorem Execution.certified_quality [ProperSpace E] (r : Execution P O N)
    (hc : Certified P (r.state N) (r.inspection N)) :
    ∀ j, 1 ≤ j → j ≤ P.q →
      gapOn (taylorDecrement f j (r.state N).point)
        (Metric.closedBall 0 ((r.inspection N).radii j)) ≤
          P.epsilon j * (r.inspection N).radii j ^ j / (j ! : ℝ) := by
  intro j hj hjq
  have hv := (r.inspection N).valid_radii (r.valid_radii le_rfl) j hj hjq
  have hh := approximate_gap_certifies (O.derivative (r.state N).point (r.state N).request)
    (fun i => iteratedFDeriv ℝ i f (r.state N).point) (r.state N).request
    (isCompact_closedBall (0 : E) ((r.inspection N).radii j))
    ⟨0, by simpa using hv.1.le⟩ hv.1.le (Set.Subset.refl _)
    (fun i hi => O.derivative_accuracy _ _
      (fun i hi => (r.request_bounds le_rfl hi).1) i
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
        (Finset.mem_Icc.mp hi).2.trans (hjq.trans P.order_le)⟩))
    ((r.inspection N).passed_gap hc.1 hj hjq) ?_
  · have he : decrement (fun i => iteratedFDeriv ℝ i f (r.state N).point) j =
        taylorDecrement f j (r.state N).point :=
      funext (decrement_iteratedFDeriv f (r.state N).point j)
    rw [he] at hh
    exact hh
  · exact (hc.2 j hj hjq).trans (by
      have hn : 0 ≤ P.epsilon j * (r.inspection N).radii j ^ j := by
        exact mul_nonneg (P.epsilon_pos j hj hjq).le (pow_nonneg hv.1.le _)
      have hm := mul_le_mul_of_nonneg_right P.fraction_le_one hn
      simpa only [one_mul, mul_assoc] using div_le_div_of_nonneg_right hm
        (by positivity : (0 : ℝ) ≤ 2 * (j ! : ℝ)))

/-- A prefix retains all actual states, inspections, decisions and query logs. -/
noncomputable def Execution.prefix {k : ℕ} (r : Execution P O N) (hk : k ≤ N) :
    Execution P O k where
  state := r.state
  inspection := r.inspection
  trial := r.trial
  accepted := r.accepted
  queries := r.queries
  initial_fresh := r.initial_fresh
  initial_cache := r.initial_cache
  initial_sigma := r.initial_sigma
  initial_radii := r.initial_radii
  initial_tolerance := r.initial_tolerance
  initial_request := r.initial_request
  initial_request_le := r.initial_request_le
  transition := fun j hj => r.transition j (hj.trans_le hk)

/-- Prefixing preserves the exact state and value-cache keys. -/
@[simp] theorem Execution.prefix_state {k : ℕ} (r : Execution P O N) (hk : k ≤ N) :
    (r.prefix hk).state = r.state := rfl

/-- Prefixing preserves every chosen radius-search witness. -/
@[simp] theorem Execution.prefix_inspection {k : ℕ} (r : Execution P O N) (hk : k ≤ N) :
    (r.prefix hk).inspection = r.inspection := rfl

/-- Prefixing preserves the exact value-query schedule. -/
@[simp] theorem Execution.prefix_queries {k : ℕ} (r : Execution P O N) (hk : k ≤ N) :
    (r.prefix hk).queries = r.queries := rfl

end Optimization.ExplicitRegularization
