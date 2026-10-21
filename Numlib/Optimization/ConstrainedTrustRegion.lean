import Numlib.Optimization.HigherOrderTrustRegion
import Numlib.Optimization.ConstrainedTaylorGaps

/-!
# Trust-region trials with feasible Taylor witnesses

The numerical core retains the increasing-order scan, selected-order ratio, acceptance,
and interval radius updates. Constraint-dependent laws concern actual initial, witness,
and trial endpoints and the Taylor gap over the entire feasible testing ball.
-/

noncomputable section
namespace Optimization.ConstrainedTrustRegion
open HigherOrderTrustRegion TaylorCriticality RegularizedTaylorModel
open ConstrainedTaylorCriticality Metric Set
open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual feasible testing displacements, including the whole testing ball. -/
def testingSet (X : Set E) (x : E) (r : ℝ) : Set E :=
  feasibleDisplacements X x ∩ closedBall 0 r

omit [NormedSpace ℝ E] in
/-- A testing displacement satisfies both endpoint feasibility and the radius bound. -/
@[simp] theorem mem_testingSet {X : Set E} {x d : E} {r : ℝ} :
    d ∈ testingSet X x r ↔ x + d ∈ X ∧ ‖d‖ ≤ r := by
  simp [testingSet]

omit [NormedSpace ℝ E] in
/-- At a feasible center the zero testing displacement is available. -/
theorem zero_mem_testingSet {X : Set E} {x : E} {r : ℝ} (hx : x ∈ X) (hr : 0 ≤ r) :
    (0 : E) ∈ testingSet X x r := by simpa using And.intro hx hr

omit [NormedSpace ℝ E] in
/-- Testing sets are compact for closed constraints in a proper normed space. -/
theorem isCompact_testingSet [ProperSpace E] {X : Set E} (hX : IsClosed X)
    (x : E) (r : ℝ) : IsCompact (testingSet X x r) :=
  isCompact_feasibleDisplacements_inter_closedBall hX x r

/-- Every actual Taylor decrement attains its full feasible testing gap. -/
theorem exists_maximizer [ProperSpace E] {X : Set E} (hX : IsClosed X)
    {x : E} (hx : x ∈ X) {r : ℝ} (hr : 0 ≤ r) (f : E → ℝ) (j : ℕ) :
    ∃ d ∈ testingSet X x r,
      taylorDecrement f j x d = gapOn (taylorDecrement f j x) (testingSet X x r) :=
  by
    obtain ⟨d, hd, hn, he⟩ := exists_eq_taylorGap f hX j hx hr
    exact ⟨d, mem_testingSet.mpr ⟨hd, hn⟩, he⟩

omit [NormedSpace ℝ E] in
/-- With no constraints, the testing domain is the full closed ball. -/
@[simp] theorem testingSet_univ (x : E) (r : ℝ) :
    testingSet univ x r = closedBall 0 r := by ext d; simp

omit [NormedSpace ℝ E] in
/-- A testing ball contained in the translated feasible set is unchanged by constraints. -/
theorem testingSet_eq_closedBall {X : Set E} {x : E} {r : ℝ}
    (h : ∀ d, ‖d‖ ≤ r → x + d ∈ X) :
    testingSet X x r = closedBall 0 r := by
  ext d
  simp only [mem_testingSet, mem_closedBall_zero_iff]
  exact ⟨And.right, fun hd => ⟨h d hd, hd⟩⟩

/-- Constraint-independent numerical laws of the exact higher-order trust-region method. -/
structure OperationalPrefix (p : Parameters) (q : ℕ) (epsilon : ℕ → ℝ) (f : E → ℝ)
    (t : Trace E) (N : ℕ) : Prop where
  initial_pos : 0 < t.radius 0
  initial_cap : t.radius 0 ≤ p.radiusMax
  witness_feasible : ∀ k ≤ N, ∀ j, 1 ≤ j → j ≤ q →
    ‖t.witness k j‖ ≤ testRadius p t k
  nonterminal : ∀ k < N, ¬Stops p q epsilon f t k
  order_pos : ∀ k < N, 1 ≤ t.order k
  order_le : ∀ k < N, t.order k ≤ q
  first_failure : ∀ k < N, ∀ j, 1 ≤ j → j < t.order k →
    taylorDecrement f j (t.point k) (t.witness k j) ≤
      p.fraction * epsilon j * testRadius p t k ^ j / (j ! : ℝ)
  failure : ∀ k < N, p.fraction * epsilon (t.order k) *
    testRadius p t k ^ t.order k / ((t.order k)! : ℝ) <
      taylorDecrement f (t.order k) (t.point k) (t.witness k (t.order k))
  step_feasible : ∀ k < N, ‖t.step k‖ ≤ t.radius k
  prediction : ∀ k < N, taylorDecrement f (t.order k) (t.point k)
    (t.witness k (t.order k)) ≤ taylorDecrement f (t.order k) (t.point k) (t.step k)
  iterate : ∀ k < N, t.point (k + 1) =
    if p.eta1 ≤ ratio f t k then t.point k + t.step k else t.point k
  update : ∀ k < N, if p.eta2 ≤ ratio f t k
    then t.radius (k + 1) ∈ Icc (t.radius k) (min p.radiusMax (p.gamma3 * t.radius k))
    else if p.eta1 ≤ ratio f t k
    then t.radius (k + 1) ∈ Icc (p.gamma2 * t.radius k) (t.radius k)
    else t.radius (k + 1) ∈ Icc (p.gamma1 * t.radius k) (p.gamma2 * t.radius k)

/-- Actual constrained finite execution, with all computed endpoints feasible. -/
structure LegalPrefix (X : Set E) (p : Parameters) (q : ℕ) (epsilon : ℕ → ℝ)
    (f : E → ℝ) (t : Trace E) (N : ℕ) : Prop extends
    OperationalPrefix p q epsilon f t N where
  initial_mem : t.point 0 ∈ X
  witness_mem : ∀ k ≤ N, ∀ j, 1 ≤ j → j ≤ q → t.point k + t.witness k j ∈ X
  trial_mem : ∀ k < N, t.point k + t.step k ∈ X
  witness_fraction : ∀ k ≤ N, ∀ j, 1 ≤ j → j ≤ q →
    p.fraction * gapOn (taylorDecrement f j (t.point k))
      (testingSet X (t.point k) (testRadius p t k)) ≤
        taylorDecrement f j (t.point k) (t.witness k j)

variable {X : Set E} {p : Parameters} {q N : ℕ} {epsilon : ℕ → ℝ}
  {f : E → ℝ} {t : Trace E}

/-- Every retained point of a legal constrained execution is feasible. -/
theorem LegalPrefix.point_mem (h : LegalPrefix X p q epsilon f t N)
    {k : ℕ} (hk : k ≤ N) : t.point k ∈ X := by
  induction k with
  | zero => exact h.initial_mem
  | succ k ih =>
    rw [h.iterate k (by omega)]
    split_ifs
    · exact h.trial_mem k (by omega)
    · exact ih (by omega)

/-- A full-ball legal execution gives the same numerical core. -/
theorem operationalOfUnconstrained (h : HigherOrderTrustRegion.LegalPrefix p q epsilon f t N) :
    OperationalPrefix p q epsilon f t N where
  initial_pos := h.initial_pos
  initial_cap := h.initial_cap
  witness_feasible := h.witness_feasible
  nonterminal := h.nonterminal
  order_pos := h.order_pos
  order_le := h.order_le
  first_failure := h.first_failure
  failure := h.failure
  step_feasible := h.step_feasible
  prediction := h.prediction
  iterate := h.iterate
  update := h.update

/-- Unconstrained execution is exactly constrained execution on the universal set. -/
theorem legalPrefix_univ_iff : LegalPrefix (univ : Set E) p q epsilon f t N ↔
    HigherOrderTrustRegion.LegalPrefix p q epsilon f t N := by
  constructor
  · intro h
    exact { h.toOperationalPrefix with witness_fraction := by simpa using h.witness_fraction }
  · intro h
    exact { operationalOfUnconstrained h with
      initial_mem := mem_univ _
      witness_mem := by intros; trivial
      trial_mem := by intros; trivial
      witness_fraction := by simpa using h.witness_fraction }

/-- Full-ball prefixes remain legal when their testing balls and actual trials are feasible. -/
theorem of_unconstrained (h : HigherOrderTrustRegion.LegalPrefix p q epsilon f t N)
    (h0 : t.point 0 ∈ X)
    (hball : ∀ k ≤ N, ∀ d, ‖d‖ ≤ testRadius p t k → t.point k + d ∈ X)
    (htrial : ∀ k < N, t.point k + t.step k ∈ X) :
    LegalPrefix X p q epsilon f t N where
  toOperationalPrefix := operationalOfUnconstrained h
  initial_mem := h0
  witness_mem := fun k hk j hj hjq => hball k hk _ (h.witness_feasible k hk j hj hjq)
  trial_mem := htrial
  witness_fraction := by
    intro k hk j hj hjq
    rw [testingSet_eq_closedBall (hball k hk)]
    exact h.witness_fraction k hk j hj hjq

/-- Source stopping tests certify all true feasible Taylor gaps. -/
theorem LegalPrefix.gaps_at_stop (h : LegalPrefix X p q epsilon f t N)
    (hs : Stops p q epsilon f t N) :
    ∀ j, 1 ≤ j → j ≤ q → gapOn (taylorDecrement f j (t.point N))
      (testingSet X (t.point N) (testRadius p t N)) ≤
        epsilon j * testRadius p t N ^ j / (j ! : ℝ) := by
  intro j hj hjq
  have hw := h.witness_fraction N le_rfl j hj hjq
  have hh := hs j hj hjq
  have heq : p.fraction * epsilon j * testRadius p t N ^ j / (j ! : ℝ) =
      p.fraction * (epsilon j * testRadius p t N ^ j / (j ! : ℝ)) := by ring
  rw [heq] at hh
  nlinarith [hw.trans hh, p.fraction_pos]

/-- Restricting a finite execution retains all endpoint witness and trial laws. -/
theorem LegalPrefix.restrict (h : LegalPrefix X p q epsilon f t N) {M : ℕ} (hMN : M ≤ N) :
    LegalPrefix X p q epsilon f t M where
  initial_pos := h.initial_pos
  initial_cap := h.initial_cap
  witness_feasible := fun k hk => h.witness_feasible k (hk.trans hMN)
  nonterminal := fun k hk => h.nonterminal k (hk.trans_le hMN)
  order_pos := fun k hk => h.order_pos k (hk.trans_le hMN)
  order_le := fun k hk => h.order_le k (hk.trans_le hMN)
  first_failure := fun k hk => h.first_failure k (hk.trans_le hMN)
  failure := fun k hk => h.failure k (hk.trans_le hMN)
  step_feasible := fun k hk => h.step_feasible k (hk.trans_le hMN)
  prediction := fun k hk => h.prediction k (hk.trans_le hMN)
  iterate := fun k hk => h.iterate k (hk.trans_le hMN)
  update := fun k hk => h.update k (hk.trans_le hMN)
  initial_mem := h.initial_mem
  witness_mem := fun k hk => h.witness_mem k (hk.trans hMN)
  trial_mem := fun k hk => h.trial_mem k (hk.trans_le hMN)
  witness_fraction := fun k hk => h.witness_fraction k (hk.trans hMN)

/-- An execution is legal only for prefixes preceding its first actual stopping test. -/
def IsRun (X : Set E) (p : Parameters) (q : ℕ) (epsilon : ℕ → ℝ)
    (f : E → ℝ) (t : Trace E) : Prop :=
  ∀ N, (∀ k < N, ¬Stops p q epsilon f t k) → LegalPrefix X p q epsilon f t N

end Optimization.ConstrainedTrustRegion
