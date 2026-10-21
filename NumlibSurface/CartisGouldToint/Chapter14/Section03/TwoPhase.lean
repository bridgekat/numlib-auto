import NumlibSurface.CartisGouldToint.Chapter14.Section03.ResidualJets
import NumlibSurface.CartisGouldToint.Chapter07.Section02.Execution
import Numlib.Optimization.TwoPhaseHigherOrder

/-!
# Chapter 14, Section 3: literal higher-order two-phase executions

The finite execution records actual LEN and interrupted INNER histories. Phase-2 index
zero is source index one. Target updates retain the printed strict and weak boundaries,
including equality in the third terminal branch; no Lagrangian certificate is an input.
The printed LEN dual domain is strict, whereas TWO-PHASE permits its upper endpoint.
The closed-dual LEN extension handles that endpoint with the same operations. Phase 1
separately retains the unconditional printed beta input, which excludes zero initial residual.
The strict residual sign in the Phase-1 postcondition (14.3.31) is read as weak, consistently
with the actual initial LEN test and the weak feasibility conclusions of Lemma 14.3.7.
This postcondition is derived from the execution, not imposed as an extra output assumption.
-/

noncomputable section
open Set Metric Optimization Optimization.ResidualLeastSquares
open Optimization.ConstrainedTaylorCriticality Optimization.TwoPhaseTargets
open Optimization.TaylorCriticality
namespace CartisGouldToint.Chapter14.Section03
variable {n m q : ℕ} {S₁ S₂ : Type}

/-- The radii associated with the Phase-1 return. An initially feasible zero-call return
has unit radii; every noninitial return retains the radii actually supplied by LEN. -/
def twoPhasePhaseOneRadii (t : Trace (EuclideanSpace ℝ (Fin n)) S₁) (K : ℕ) : ℕ → ℝ :=
  if K = 0 then fun _ => 1 else t.radius K

/-- A zero-call Phase-1 return supplies unit radii without performing an extra gap test. -/
@[simp] theorem twoPhasePhaseOneRadii_zero
    (t : Trace (EuclideanSpace ℝ (Fin n)) S₁) :
    twoPhasePhaseOneRadii t 0 = fun _ => 1 := by simp [twoPhasePhaseOneRadii]

/-- A noninitial Phase-1 return keeps exactly its actual LEN output radii. -/
theorem twoPhasePhaseOneRadii_of_pos
    (t : Trace (EuclideanSpace ℝ (Fin n)) S₁) {K : ℕ} (hK : 0 < K) :
    twoPhasePhaseOneRadii t K = t.radius K := by
  simp [twoPhasePhaseOneRadii, Nat.ne_of_gt hK]

/-- The Phase-1 output guarantee, with the residual sign in (14.3.31) corrected to weak
to agree with actual LEN stopping. It will be proved from the actual execution. -/
def twoPhasePhaseOneTest (X : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (q : ℕ)
    (θ ε₀ : ℝ) (ε δ : ℕ → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖c x‖ ≤ θ * ε₀ ∨ ∀ j ∈ Finset.Icc 1 q,
    gapOn (taylorDecrement (squaredResidual c) j x)
      (feasibleDisplacements X x ∩ closedBall 0 (δ j)) ≤
        ε j * ‖c x‖ * δ j ^ j / (j.factorial : ℝ)

/-- A small residual, including equality, needs no Phase-1 derivative-gap query. -/
theorem twoPhasePhaseOneTest.of_small {X : Set (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {q : ℕ} {θ ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : ‖c x‖ ≤ θ * ε₀) : twoPhasePhaseOneTest X c q θ ε₀ ε δ x := Or.inl h

/-- Above the Phase-1 threshold, its actual output guarantee gives every displayed gap. -/
theorem twoPhasePhaseOneTest.gaps {X : Set (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {q : ℕ} {θ ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : twoPhasePhaseOneTest X c q θ ε₀ ε δ x) (hr : θ * ε₀ < ‖c x‖) :
    ∀ j ∈ Finset.Icc 1 q,
      gapOn (taylorDecrement (squaredResidual c) j x)
        (feasibleDisplacements X x ∩ closedBall 0 (δ j)) ≤
          ε j * ‖c x‖ * δ j ^ j / (j.factorial : ℝ) :=
  h.resolve_left (not_le.mpr hr)

/-- The actual TPqp-GC finite execution (Algorithm 14.3.2). The selected INNER transition
relations encode its backend degree; criticality orders are exactly one through three.
Phase 1 is the actual LEN execution; its output guarantee is derived. Phase 2 retains
all call prefixes,
actual returned radii, retained solver state, target updates and evaluation events. Its
stopping fields are the literal algorithmic tests, not a claimed constrained solution. -/
structure algorithm_14_3_2
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (X : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) (θ ε₀ β₁ β₂ : ℝ)
    (ε π : ℕ → ℝ) (κ₁ κ₂ : EvaluationKind → ℝ)
    (step₁ : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₁ →
      EuclideanSpace ℝ (Fin n) × S₁ → List EvaluationKind → Prop)
    (terminal₁ : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₁ → List EvaluationKind → Prop)
    (step₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
      EuclideanSpace ℝ (Fin n) × S₂ → List EvaluationKind → Prop)
    (terminal₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
      List EvaluationKind → Prop)
    (phaseOne : Trace (EuclideanSpace ℝ (Fin n)) S₁) (K : ℕ)
    (phaseTwo : TargetTrace (EuclideanSpace ℝ (Fin n)) S₂) (N : ℕ) : Prop where
  /-- The source's upper limit on criticality order. Positivity follows from LEN. -/
  order_le_three : q ≤ 3
  /-- The feasibility fraction is strictly between zero and one. -/
  fraction : θ ∈ Ioo 0 1
  /-- The primal tolerance includes the source's upper endpoint. -/
  primal : ε₀ ∈ Ioc 0 1
  /-- The actual Phase-1 LEN execution, including its endpoint extension for dual tolerances. -/
  phase_one : algorithm_14_3_1_closedDual X c q (θ * ε₀) β₁ ε π κ₁
    step₁ terminal₁ phaseOne
  /-- The unconditional beta restriction printed before the Phase-1 initial residual test. -/
  phase_one_input : LiteralLENInput c (phaseOne.point 0) β₁
  /-- Phase 1 has actually met a LEN stopping test. -/
  phase_one_stop : Stops X c q (θ * ε₀) ε phaseOne K
  /-- No previous Phase-1 stage has stopped. -/
  phase_one_first : ∀ k < K, ¬Stops X c q (θ * ε₀) ε phaseOne k
  /-- The actual infeasible exit or complete finite Phase-2 history. There is no initial
  Phase-2 criticality test: a feasible Phase-1 return executes at least one inner call. -/
  phase_two :
    (θ * ε₀ < ‖c (phaseOne.point K)‖ ∧ N = 0) ∨
    (‖c (phaseOne.point K)‖ ≤ θ * ε₀ ∧
      PhaseTwoExecution X f c q θ ε₀ β₂ ε π κ₂ step₂ terminal₂ phaseTwo N ∧
      phaseTwo.point 0 = phaseOne.point K ∧
      phaseTwo.radius 0 = twoPhasePhaseOneRadii phaseOne K)

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
  {X : Set (EuclideanSpace ℝ (Fin n))} {θ ε₀ β₁ β₂ : ℝ}
  {ε π : ℕ → ℝ} {κ₁ κ₂ : EvaluationKind → ℝ}
  {step₁ : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₁ →
    EuclideanSpace ℝ (Fin n) × S₁ → List EvaluationKind → Prop}
  {terminal₁ : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₁ → List EvaluationKind → Prop}
  {step₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
    EuclideanSpace ℝ (Fin n) × S₂ → List EvaluationKind → Prop}
  {terminal₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
    List EvaluationKind → Prop}
  {phaseOne : Trace (EuclideanSpace ℝ (Fin n)) S₁} {K N : ℕ}
  {phaseTwo : TargetTrace (EuclideanSpace ℝ (Fin n)) S₂}

/-- The canonical target gap test is exactly the source test using the actual augmented
Euclidean residual, not a product maximum norm. -/
theorem twoPhaseScaledTargetGaps_iff {δ : ℕ → ℝ} {t : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    ScaledTargetGaps X f c q ε δ t x ↔
      ∀ j ∈ Finset.Icc 1 q,
        gapOn (taylorDecrement ((twoPhaseResidualObjectives f c).2 t) j x)
          (feasibleDisplacements X x ∩ closedBall 0 (δ j)) ≤
            ε j * ‖twoPhaseResidual f c t x‖ * δ j ^ j / (j.factorial : ℝ) := by
  rw [scaledTargetGaps_iff]
  simp only [ twoPhaseResidualObjectives_snd, twoPhaseResidual,
    Chapter07.Section02.norm_targetResidual_eq_residualNorm]

/-- Every full two-phase execution has one of the source's three criticality orders. -/
theorem algorithm_14_3_2.order
    (h : algorithm_14_3_2 f c X q θ ε₀ β₁ β₂ ε π κ₁ κ₂ step₁ terminal₁ step₂ terminal₂
      phaseOne K phaseTwo N) : q ∈ Finset.Icc 1 3 :=
  Finset.mem_Icc.mpr ⟨h.phase_one.order_pos, h.order_le_three⟩

/-- The actual Phase-1 return lies in the simple constraint set. -/
theorem algorithm_14_3_2.phase_one_feasible
    (h : algorithm_14_3_2 f c X q θ ε₀ β₁ β₂ ε π κ₁ κ₂ step₁ terminal₁ step₂ terminal₂
      phaseOne K phaseTwo N) : phaseOne.point K ∈ X := by
  cases K with
  | zero => exact h.phase_one.initial_feasible
  | succ k =>
    have hi := (h.phase_one.solve k (h.phase_one_first k (by omega))).feasible _ le_rfl
    simpa only [h.phase_one.finish] using hi

/-- The Phase-1 radii are positive and at most one, including the initial feasible case. -/
theorem algorithm_14_3_2.phase_one_radius
    (h : algorithm_14_3_2 f c X q θ ε₀ β₁ β₂ ε π κ₁ κ₂ step₁ terminal₁ step₂ terminal₂
      phaseOne K phaseTwo N) {j : ℕ} (hj : j ∈ Finset.Icc 1 q) :
    0 < twoPhasePhaseOneRadii phaseOne K j ∧ twoPhasePhaseOneRadii phaseOne K j ≤ 1 := by
  cases K with
  | zero => simp
  | succ k =>
    rw [twoPhasePhaseOneRadii_of_pos phaseOne (by omega)]
    exact (h.phase_one.solve k (h.phase_one_first k (by omega))).radius j hj

/-- The corrected weak Phase-1 output guarantee follows from the actual LEN stopping
record. In the infeasible branch every displayed gap uses the radii actually returned. -/
theorem algorithm_14_3_2.phase_one_test
    (h : algorithm_14_3_2 f c X q θ ε₀ β₁ β₂ ε π κ₁ κ₂ step₁ terminal₁ step₂ terminal₂
      phaseOne K phaseTwo N) :
    twoPhasePhaseOneTest X c q θ ε₀ ε (twoPhasePhaseOneRadii phaseOne K)
      (phaseOne.point K) := by
  by_cases hc : ‖c (phaseOne.point K)‖ ≤ θ * ε₀
  · exact Or.inl hc
  · right
    have hK : 0 < K := by
      rcases h.phase_one_stop with hh | ⟨hk, _⟩
      · exact (hc hh).elim
      · exact hk
    rw [twoPhasePhaseOneRadii_of_pos phaseOne hK]
    have hs := (h.phase_one.stops_iff_certificate K).mp h.phase_one_stop
    intro j hj
    exact (hs.resolve_left hc j hj).2

/-- A successful Phase-1 feasibility test exposes the actual complete Phase-2 history. -/
theorem algorithm_14_3_2.phase_two_execution
    (h : algorithm_14_3_2 f c X q θ ε₀ β₁ β₂ ε π κ₁ κ₂ step₁ terminal₁ step₂ terminal₂
      phaseOne K phaseTwo N) (hc : ‖c (phaseOne.point K)‖ ≤ θ * ε₀) :
    PhaseTwoExecution X f c q θ ε₀ β₂ ε π κ₂ step₂ terminal₂ phaseTwo N := by
  rcases h.phase_two with ⟨hn, _⟩ | ⟨_, he, _⟩
  · exact (not_lt_of_ge hc hn).elim
  · exact he

/-- The initial Phase-2 square root has a nonnegative radicand. -/
theorem algorithm_14_3_2.initial_radicand_nonneg
    (h : algorithm_14_3_2 f c X q θ ε₀ β₁ β₂ ε π κ₁ κ₂ step₁ terminal₁ step₂ terminal₂
      phaseOne K phaseTwo N) (hc : ‖c (phaseOne.point K)‖ ≤ θ * ε₀) :
    0 ≤ ε₀ ^ 2 - ‖c (phaseOne.point K)‖ ^ 2 := by
  have hh : ‖c (phaseOne.point K)‖ ≤ ε₀ := hc.trans (by nlinarith [h.fraction.2, h.primal.1])
  nlinarith [norm_nonneg (c (phaseOne.point K))]

/-- Phase-2 residual annuli use the book's actual augmented Euclidean vector. -/
theorem algorithm_14_3_2.phase_two_residual_bounds
    (h : algorithm_14_3_2 f c X q θ ε₀ β₁ β₂ ε π κ₁ κ₂ step₁ terminal₁ step₂ terminal₂
      phaseOne K phaseTwo N) (hc : ‖c (phaseOne.point K)‖ ≤ θ * ε₀)
    {k : ℕ} (hk : k ≤ N) :
    θ * ε₀ ≤ ‖twoPhaseResidual f c (phaseTwo.target k) (phaseTwo.point k)‖ ∧
      ‖twoPhaseResidual f c (phaseTwo.target k) (phaseTwo.point k)‖ ≤ ε₀ := by
  simpa only [twoPhaseResidual, Chapter07.Section02.norm_targetResidual_eq_residualNorm]
    using (h.phase_two_execution hc).residual_bounds hk

/-- Actual Phase-2 termination gives the source's all-order residual-scaled `μ` tests.
No Lagrangian multiplier conclusion is assumed or asserted here. -/
theorem algorithm_14_3_2.phase_two_gaps
    (h : algorithm_14_3_2 f c X q θ ε₀ β₁ β₂ ε π κ₁ κ₂ step₁ terminal₁ step₂ terminal₂
      phaseOne K phaseTwo N) (hc : ‖c (phaseOne.point K)‖ ≤ θ * ε₀) :
    ∀ j ∈ Finset.Icc 1 q,
      gapOn (taylorDecrement ((twoPhaseResidualObjectives f c).2 (phaseTwo.target N)) j
        (phaseTwo.point N))
        (feasibleDisplacements X (phaseTwo.point N) ∩ closedBall 0 (phaseTwo.radius N j)) ≤
          ε j * ‖twoPhaseResidual f c (phaseTwo.target N) (phaseTwo.point N)‖ *
            phaseTwo.radius N j ^ j / (j.factorial : ℝ) :=
  twoPhaseScaledTargetGaps_iff.mp (h.phase_two_execution hc).terminal_scaled_gaps

/-- Count actual Phase-1 events and, only if Phase 2 is executed, its initial event and
all actually executed interrupted INNER calls. Cached target updates are not new calls. -/
def twoPhaseEvaluations (phaseOne : Trace (EuclideanSpace ℝ (Fin n)) S₁) (K : ℕ)
    (phaseTwo : TargetTrace (EuclideanSpace ℝ (Fin n)) S₂) (N : ℕ)
    (a : EvaluationKind) : ℕ :=
  totalEvaluations phaseOne a K + if N = 0 then 0 else phaseTwo.evaluations N a

end CartisGouldToint.Chapter14.Section03
