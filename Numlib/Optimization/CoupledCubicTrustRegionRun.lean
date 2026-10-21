import Numlib.Optimization.CoupledCubicTrustRegionContinuation

/-!
# An actual finite constrained continuation

Compact feasible-ball maximizers supply every witness. An increasing-order scan chooses
an actual failed test, and the selected maximizer is executed as the trial. Positive
coordinates make every such trial very successful, so a fixed radius is permitted.
-/

noncomputable section
namespace Optimization.CoupledCubic
namespace Continuation
attribute [local instance] Classical.propDecidable
open ConstrainedTrustRegion TaylorCriticality HigherOrderTrustRegion Set Metric

/-- Geometric invariant of the coupled continuation at a fixed radius. -/
structure State (R : ℝ) where
  y : ℝ
  z : ℝ
  feasible : point 0 y z ∈ box
  lower_y : R ≤ y
  lower_z : R ≤ z

/-- The ambient point of a continuation state. -/
def State.location {R : ℝ} (s : State R) : Space := point 0 s.y s.z

variable {R : ℝ}

/-- Every requested order has an actual global feasible-ball maximizing direction. -/
def direction (hR : 0 ≤ R) (s : State R) (j : ℕ) : Space :=
  if hj : 1 ≤ j ∧ j ≤ 2 then
    Classical.choose (exists_positive_maximizer hR s.lower_y s.lower_z s.feasible hj.1 hj.2)
  else 0

/-- Maximizers retain their whole-ball optimality, feasibility, and coordinate signs. -/
theorem direction_spec (hR : 0 ≤ R) (s : State R) {j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ 2) :
    direction hR s j ∈ testingSet box s.location R ∧
      direction hR s j 0 = 0 ∧ 0 ≤ direction hR s j 1 ∧ 0 ≤ direction hR s j 2 ∧
      taylorDecrement objective j s.location (direction hR s j) =
        gapOn (taylorDecrement objective j s.location) (testingSet box s.location R) := by
  simpa only [direction, dite_eq_left (And.intro hj hjq), State.location] using
    Classical.choose_spec (exists_positive_maximizer hR s.lower_y s.lower_z s.feasible hj hjq)

/-- Passing the actual source test for an inspected maximizing witness. -/
def Passed (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) (j : ℕ) : Prop :=
  taylorDecrement objective j s.location (direction hR s j) ≤
    p.fraction * epsilon j * R ^ j / (j.factorial : ℝ)

/-- All source tests pass at the current state. -/
def Terminal (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) : Prop :=
  ∀ j, 1 ≤ j → j ≤ 2 → Passed p epsilon hR s j

/-- The literal increasing-order scan selects order one when it fails, otherwise order two. -/
def selected (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) : ℕ :=
  if Passed p epsilon hR s 1 then 2 else 1

/-- The selected order is always requested. -/
theorem selected_bounds (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) :
    1 ≤ selected p epsilon hR s ∧ selected p epsilon hR s ≤ 2 := by
  unfold selected
  split_ifs <;> omega

/-- Prior tests pass and the selected test fails whenever the scan is nonterminal. -/
theorem selected_failure (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R)
    (hs : ¬Terminal p epsilon hR s) :
    (∀ j, 1 ≤ j → j < selected p epsilon hR s → Passed p epsilon hR s j) ∧
      ¬Passed p epsilon hR s (selected p epsilon hR s) := by
  unfold selected
  split_ifs with h
  · refine ⟨?_, ?_⟩
    · intro j hj hj2
      have : j = 1 := by omega
      simpa [this] using h
    · intro h2
      apply hs
      intro j hj hjq
      interval_cases j <;> assumption
  · exact ⟨by intros; omega, h⟩

/-- The trial direction is the actual selected global maximizer. -/
def trial (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) : Space :=
  direction hR s (selected p epsilon hR s)

/-- The computed trial is feasible and has the signs that force acceptance. -/
theorem trial_spec (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) :
    trial p epsilon hR s ∈ testingSet box s.location R ∧
      trial p epsilon hR s 0 = 0 ∧ 0 ≤ trial p epsilon hR s 1 ∧
        0 ≤ trial p epsilon hR s 2 := by
  have h := direction_spec hR s (selected_bounds p epsilon hR s).1
    (selected_bounds p epsilon hR s).2
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- A trial endpoint again satisfies the geometric invariant. -/
def advanced (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) : State R where
  y := s.y + trial p epsilon hR s 1
  z := s.z + trial p epsilon hR s 2
  feasible := by
    have h := (mem_testingSet.mp (trial_spec p epsilon hR s).1).1
    convert h using 1
    ext i
    fin_cases i <;> simp [State.location, (trial_spec p epsilon hR s).2.1]
  lower_y := le_trans s.lower_y (le_add_of_nonneg_right (trial_spec p epsilon hR s).2.2.1)
  lower_z := le_trans s.lower_z (le_add_of_nonneg_right (trial_spec p epsilon hR s).2.2.2)

/-- The advanced location is exactly the actual trial endpoint. -/
theorem advanced_location (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) :
    (advanced p epsilon hR s).location = s.location + trial p epsilon hR s := by
  ext i
  fin_cases i <;> simp [State.location, advanced, (trial_spec p epsilon hR s).2.1]

/-- The state transition freezes after the actual all-orders stopping test. -/
def next (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) : State R :=
  if Terminal p epsilon hR s then s else advanced p epsilon hR s

/-- A total natural-number execution, retaining its terminal state forever. -/
def states (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) : ℕ → State R :=
  Nat.rec s (fun _ u => next p epsilon hR u)

/-- The first state is the specified initial state. -/
@[simp] theorem states_zero (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) :
    states p epsilon hR s 0 = s := rfl

/-- Every successor is the actual frozen-or-advanced state transition. -/
@[simp] theorem states_succ (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R)
    (k : ℕ) : states p epsilon hR s (k + 1) = next p epsilon hR (states p epsilon hR s k) := rfl

/-- The actual source trace uses the fixed radius and the selected maximizing direction. -/
def trace (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R) : Trace Space where
  point k := (states p epsilon hR s k).location
  step k := if Terminal p epsilon hR (states p epsilon hR s k) then 0
    else trial p epsilon hR (states p epsilon hR s k)
  radius _ := R
  witness k j := direction hR (states p epsilon hR s k) j
  order k := selected p epsilon hR (states p epsilon hR s k)

/-- The capped testing radius is the fixed radius whenever the cap allows it. -/
theorem trace_testRadius (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R)
    (hcap : R ≤ p.theta) (k : ℕ) : testRadius p (trace p epsilon hR s) k = R :=
  min_eq_left hcap

/-- The operational stopping test is exactly the computed maximizing-witness test. -/
theorem stops_iff (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R)
    (hcap : R ≤ p.theta) (k : ℕ) :
    Stops p 2 epsilon objective (trace p epsilon hR s) k ↔
      Terminal p epsilon hR (states p epsilon hR s k) := by
  unfold Stops Terminal Passed
  simp only [trace_testRadius p epsilon hR s hcap]
  rfl

/-- Failure of the scan forces a strictly positive selected prediction. -/
theorem prediction_pos (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 < R)
    (he : ∀ j, 1 ≤ j → j ≤ 2 → 0 < epsilon j) (s : State R)
    (hs : ¬Terminal p epsilon hR.le s) :
    0 < taylorDecrement objective (selected p epsilon hR.le s) s.location
      (trial p epsilon hR.le s) := by
  have hf := (selected_failure p epsilon hR.le s hs).2
  have hb := selected_bounds p epsilon hR.le s
  have hp : 0 < p.fraction * epsilon (selected p epsilon hR.le s) *
      R ^ selected p epsilon hR.le s / ((selected p epsilon hR.le s).factorial : ℝ) := by
    exact div_pos (mul_pos (mul_pos p.fraction_pos (he _ hb.1 hb.2)) (pow_pos hR _))
      (by positivity)
  exact hp.trans (lt_of_not_ge hf)

/-- The actual selected-order acceptance ratio is at least one at every executed trial. -/
theorem trace_ratio_ge_one (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 < R)
    (he : ∀ j, 1 ≤ j → j ≤ 2 → 0 < epsilon j) (s : State R) {k : ℕ}
    (hs : ¬Terminal p epsilon hR.le (states p epsilon hR.le s k)) :
    1 ≤ ratio objective (trace p epsilon hR.le s) k := by
  let u := states p epsilon hR.le s k
  have ht := trial_spec p epsilon hR.le u
  have hb := selected_bounds p epsilon hR.le u
  have hdec := reduction_ge_taylor (hR.le.trans u.lower_y) (hR.le.trans u.lower_z)
    ht.2.1 ht.2.2.1 ht.2.2.2 hb.1 hb.2
  change 1 ≤ (objective u.location - objective (u.location +
    (if Terminal p epsilon hR.le u then 0 else trial p epsilon hR.le u))) /
      taylorDecrement objective (selected p epsilon hR.le u) u.location
        (if Terminal p epsilon hR.le u then 0 else trial p epsilon hR.le u)
  rw [ite_eq_right hs]
  exact (one_le_div (prediction_pos p epsilon hR he u hs)).mpr hdec

/-- Before stopping, the retained successor is the feasible maximizing trial endpoint. -/
theorem trace_point_succ (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R)
    {k : ℕ} (hs : ¬Terminal p epsilon hR (states p epsilon hR s k)) :
    (trace p epsilon hR s).point (k + 1) =
      (trace p epsilon hR s).point k + (trace p epsilon hR s).step k := by
  change (states p epsilon hR s (k + 1)).location =
    (states p epsilon hR s k).location +
      (if Terminal p epsilon hR (states p epsilon hR s k) then 0 else _)
  rw [states_succ, next, ite_eq_right hs, ite_eq_right hs, advanced_location]

/-- The constructed trace supplies every actual constrained trial law until its source stop. -/
theorem isRun (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 < R)
    (hcap : R ≤ p.theta) (hmax : R ≤ p.radiusMax)
    (he : ∀ j, 1 ≤ j → j ≤ 2 → 0 < epsilon j) (s : State R) :
    ConstrainedTrustRegion.IsRun box p 2 epsilon objective (trace p epsilon hR.le s) := by
  intro N hN
  have hn (k : ℕ) (hk : k < N) :
      ¬Terminal p epsilon hR.le (states p epsilon hR.le s k) :=
    fun hh => hN k hk ((stops_iff p epsilon hR.le s hcap k).mpr hh)
  refine {
    initial_pos := hR
    initial_cap := hmax
    witness_feasible := ?_
    nonterminal := hN
    order_pos := ?_
    order_le := ?_
    first_failure := ?_
    failure := ?_
    step_feasible := ?_
    prediction := ?_
    iterate := ?_
    update := ?_
    initial_mem := s.feasible
    witness_mem := ?_
    trial_mem := ?_
    witness_fraction := ?_ }
  · intro k hk j hj hjq
    rw [trace_testRadius p epsilon hR.le s hcap]
    exact (mem_testingSet.mp (direction_spec hR.le _ hj hjq).1).2
  · intro k hk
    exact (selected_bounds p epsilon hR.le _).1
  · intro k hk
    exact (selected_bounds p epsilon hR.le _).2
  · intro k hk j hj hjq
    rw [trace_testRadius p epsilon hR.le s hcap]
    exact (selected_failure p epsilon hR.le _ (hn k hk)).1 j hj hjq
  · intro k hk
    rw [trace_testRadius p epsilon hR.le s hcap]
    exact lt_of_not_ge (selected_failure p epsilon hR.le _ (hn k hk)).2
  · intro k hk
    change ‖if Terminal p epsilon hR.le (states p epsilon hR.le s k) then 0 else _‖ ≤ R
    rw [ite_eq_right (hn k hk)]
    exact (mem_testingSet.mp (trial_spec p epsilon hR.le _).1).2
  · intro k hk
    change _ ≤ taylorDecrement objective _ _
      (if Terminal p epsilon hR.le (states p epsilon hR.le s k) then 0 else _)
    rw [ite_eq_right (hn k hk)]
    exact le_rfl
  · intro k hk
    rw [ite_eq_left ((p.eta_le.trans p.eta2_lt_one.le).trans
      (trace_ratio_ge_one p epsilon hR he s (hn k hk)))]
    exact trace_point_succ p epsilon hR.le s (hn k hk)
  · intro k hk
    rw [ite_eq_left (p.eta2_lt_one.le.trans (trace_ratio_ge_one p epsilon hR he s (hn k hk)))]
    exact ⟨le_rfl, le_min hmax (le_mul_of_one_le_left hR.le p.one_le_gamma3)⟩
  · intro k hk j hj hjq
    exact (mem_testingSet.mp (direction_spec hR.le _ hj hjq).1).1
  · intro k hk
    change (states p epsilon hR.le s k).location +
      (if Terminal p epsilon hR.le (states p epsilon hR.le s k) then 0 else _) ∈ box
    rw [ite_eq_right (hn k hk)]
    exact (mem_testingSet.mp (trial_spec p epsilon hR.le _).1).1
  · intro k hk j hj hjq
    rw [trace_testRadius p epsilon hR.le s hcap]
    have hd := direction_spec hR.le (states p epsilon hR.le s k) hj hjq
    change p.fraction * gapOn (taylorDecrement objective j (states p epsilon hR.le s k).location)
      (testingSet box (states p epsilon hR.le s k).location R) ≤
        taylorDecrement objective j (states p epsilon hR.le s k).location
          (direction hR.le (states p epsilon hR.le s k) j)
    rw [hd.2.2.2.2]
    exact mul_le_of_le_one_left
      (ConstrainedTaylorCriticality.taylorGap_nonneg objective isClosed_box j
        (states p epsilon hR.le s k).feasible hR.le) p.fraction_le_one

/-- The positive fixed payment forced by the selected failed test. -/
def payment (p : Parameters) (epsilon : ℕ → ℝ) (R : ℝ) : ℝ :=
  min (p.fraction * epsilon 1 * R) (p.fraction * epsilon 2 * R ^ 2 / 2)

/-- Positive tolerances and radius make the derived payment strictly positive. -/
theorem payment_pos (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 < R)
    (he : ∀ j, 1 ≤ j → j ≤ 2 → 0 < epsilon j) : 0 < payment p epsilon R := by
  apply lt_min
  · exact mul_pos (mul_pos p.fraction_pos (he 1 le_rfl (by omega))) hR
  · exact div_pos (mul_pos (mul_pos p.fraction_pos (he 2 (by omega) le_rfl))
      (pow_pos hR 2)) (by norm_num)

/-- Every actual nonterminal trial pays more than the fixed positive minimum of its two tests. -/
theorem decrease_gt_payment (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 < R)
    (s : State R) {k : ℕ}
    (hs : ¬Terminal p epsilon hR.le (states p epsilon hR.le s k)) :
    payment p epsilon R < objective (trace p epsilon hR.le s |>.point k) -
      objective (trace p epsilon hR.le s |>.point (k + 1)) := by
  let u := states p epsilon hR.le s k
  have ht := trial_spec p epsilon hR.le u
  have hb := selected_bounds p epsilon hR.le u
  have hd := reduction_ge_taylor (hR.le.trans u.lower_y) (hR.le.trans u.lower_z)
    ht.2.1 ht.2.2.1 ht.2.2.2 hb.1 hb.2
  have hf : p.fraction * epsilon (selected p epsilon hR.le u) *
      R ^ selected p epsilon hR.le u / ((selected p epsilon hR.le u).factorial : ℝ) <
      taylorDecrement objective (selected p epsilon hR.le u) u.location
        (trial p epsilon hR.le u) :=
    lt_of_not_ge (selected_failure p epsilon hR.le u hs).2
  have hm : payment p epsilon R ≤ p.fraction * epsilon (selected p epsilon hR.le u) *
      R ^ selected p epsilon hR.le u / ((selected p epsilon hR.le u).factorial : ℝ) := by
    have hb' : selected p epsilon hR.le u = 1 ∨ selected p epsilon hR.le u = 2 := by omega
    rcases hb' with h | h
    · simpa only [payment, h, pow_one, Nat.factorial_one, Nat.cast_one, div_one] using
        (min_le_left (p.fraction * epsilon 1 * R) (p.fraction * epsilon 2 * R ^ 2 / 2))
    · simpa only [payment, h, Nat.factorial_two, Nat.cast_ofNat] using
        (min_le_right (p.fraction * epsilon 1 * R) (p.fraction * epsilon 2 * R ^ 2 / 2))
  rw [trace_point_succ p epsilon hR.le s hs]
  change payment p epsilon R < objective u.location - objective (u.location +
    (if Terminal p epsilon hR.le u then 0 else trial p epsilon hR.le u))
  rw [ite_eq_right hs]
  exact hm.trans_lt (hf.trans_le hd)

/-- The actual source scan must stop after finitely many maximizing feasible trials. -/
theorem exists_stop (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 < R)
    (hcap : R ≤ p.theta) (he : ∀ j, 1 ≤ j → j ≤ 2 → 0 < epsilon j) (s : State R) :
    ∃ K, Stops p 2 epsilon objective (trace p epsilon hR.le s) K := by
  by_contra! hnone
  have hn (k : ℕ) : ¬Terminal p epsilon hR.le (states p epsilon hR.le s k) :=
    fun hh => hnone k ((stops_iff p epsilon hR.le s hcap k).mpr hh)
  have hb (k : ℕ) : objective (trace p epsilon hR.le s |>.point k) ≤
      objective s.location - (k : ℝ) * payment p epsilon R := by
    induction k with
    | zero => simp [trace]
    | succ k ih =>
      have hd := decrease_gt_payment p epsilon hR s (hn k)
      push_cast
      nlinarith
  obtain ⟨K, hK⟩ := exists_nat_gt ((objective s.location + 4) / payment p epsilon R)
  have hmul := (div_lt_iff₀ (payment_pos p epsilon hR he)).mp hK
  have hlow := objective_lower_bound (states p epsilon hR.le s K).feasible
  have hBK := hb K
  change -4 ≤ objective (trace p epsilon hR.le s |>.point K) at hlow
  linarith

/-- Once the source stops, all retained states and trial fields remain frozen. -/
theorem states_after_stop (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R)
    {K : ℕ} (hK : Terminal p epsilon hR (states p epsilon hR s K)) (n : ℕ) :
    states p epsilon hR s (K + n) = states p epsilon hR s K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, states_succ, ih, next, ite_eq_left hK]


/-- The actual post-stop trace freezes its point, maximizing witnesses, selected order,
and radius, and executes no further trial. -/
theorem trace_after_stop (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 ≤ R) (s : State R)
    {K : ℕ} (hK : Terminal p epsilon hR (states p epsilon hR s K)) (n : ℕ) :
    (trace p epsilon hR s).point (K + n) = (trace p epsilon hR s).point K ∧
      (trace p epsilon hR s).step (K + n) = 0 ∧
      (trace p epsilon hR s).witness (K + n) = (trace p epsilon hR s).witness K ∧
      (trace p epsilon hR s).order (K + n) = (trace p epsilon hR s).order K ∧
      (trace p epsilon hR s).radius (K + n) = R := by
  simp only [trace, states_after_stop p epsilon hR s hK n, ite_eq_left hK, and_self]

/-- Every geometrically admissible initial continuation state has a finite first source
stop, an actual legal constrained execution, and frozen trial fields thereafter. -/
theorem finite_run (p : Parameters) (epsilon : ℕ → ℝ) (hR : 0 < R)
    (hcap : R ≤ p.theta) (hmax : R ≤ p.radiusMax)
    (he : ∀ j, 1 ≤ j → j ≤ 2 → 0 < epsilon j) (s : State R) :
    ∃ t : Trace Space, ∃ K : ℕ,
      t.point 0 = s.location ∧ t.radius 0 = R ∧
      ConstrainedTrustRegion.IsRun box p 2 epsilon objective t ∧
      ConstrainedTrustRegion.LegalPrefix box p 2 epsilon objective t K ∧
      Stops p 2 epsilon objective t K ∧
      (∀ k < K, ¬Stops p 2 epsilon objective t k) ∧
      (∀ n, t.point (K + n) = t.point K ∧ t.step (K + n) = 0 ∧
        t.witness (K + n) = t.witness K ∧ t.order (K + n) = t.order K ∧
        t.radius (K + n) = R) := by
  let t := trace p epsilon hR.le s
  have hex := exists_stop p epsilon hR hcap he s
  let K := Nat.find hex
  have hK : Stops p 2 epsilon objective t K := Nat.find_spec hex
  have hfirst : ∀ k < K, ¬Stops p 2 epsilon objective t k :=
    fun k hk => Nat.find_min hex hk
  have hr := isRun p epsilon hR hcap hmax he s
  refine ⟨t, K, rfl, rfl, hr, hr K hfirst, hK, hfirst, ?_⟩
  exact trace_after_stop p epsilon hR.le s ((stops_iff p epsilon hR.le s hcap K).mp hK)

/-- The bad pure-second-coordinate trial can be continued from `(0,R,b)` through a
finite actual source stop without changing the radius. -/
theorem exists_finite_continuation (p : Parameters) (epsilon : ℕ → ℝ) {b : ℝ}
    (hR : 0 < R) (hRb : R ≤ b) (hb : b ≤ 1 / 2)
    (hcap : R ≤ p.theta) (hmax : R ≤ p.radiusMax)
    (he : ∀ j, 1 ≤ j → j ≤ 2 → 0 < epsilon j) :
    ∃ t : Trace Space, ∃ K : ℕ,
      t.point 0 = point 0 R b ∧ t.radius 0 = R ∧
      ConstrainedTrustRegion.IsRun box p 2 epsilon objective t ∧
      ConstrainedTrustRegion.LegalPrefix box p 2 epsilon objective t K ∧
      Stops p 2 epsilon objective t K ∧
      (∀ k < K, ¬Stops p 2 epsilon objective t k) ∧
      (∀ n, t.point (K + n) = t.point K ∧ t.step (K + n) = 0 ∧
        t.witness (K + n) = t.witness K ∧ t.order (K + n) = t.order K ∧
        t.radius (K + n) = R) := by
  let s : State R := {
    y := R
    z := b
    feasible := by
      rw [point_mem_box, abs_zero, abs_of_pos hR, abs_of_nonneg (hR.le.trans hRb)]
      exact ⟨by norm_num, by linarith, by linarith⟩
    lower_y := le_rfl
    lower_z := hRb }
  exact finite_run p epsilon hR hcap hmax he s


end Continuation
end Optimization.CoupledCubic
