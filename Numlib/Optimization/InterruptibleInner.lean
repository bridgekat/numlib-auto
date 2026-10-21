import Numlib.Optimization.ResidualLeastSquares

/-!
# Early interruption of complete inner solver traces

A monitored prefix retains the actual points, solver state and query events of an INNER
execution. An early return retains explicit paid boundary observations, which are a
sublist of the completion stage events. Costs charge the executed prefix and its return.
-/

noncomputable section
open Set Metric
namespace Optimization.ResidualLeastSquares

/-- Truncate an actual trace, retaining the paid current-point observations at the
return boundary. Earlier transition events remain unchanged. -/
def InnerTrace.prefix {E S : Type*} (t : InnerTrace E S) (k : ℕ)
    (returnedEvents : List EvaluationKind) : InnerTrace E S where
  point := t.point
  state := t.state
  length := k
  queries i := if i < k then t.queries i else if i = k then returnedEvents else []

/-- Prefix points are the original actual points. -/
@[simp] theorem InnerTrace.prefix_point {E S : Type*} (t : InnerTrace E S) (k i : ℕ)
    (events : List EvaluationKind) : (t.prefix k events).point i = t.point i := rfl

/-- Prefix solver states retain the actual state at the selected stage. -/
@[simp] theorem InnerTrace.prefix_state {E S : Type*} (t : InnerTrace E S) (k i : ℕ)
    (events : List EvaluationKind) : (t.prefix k events).state i = t.state i := rfl

/-- The prefix has exactly the supplied number of executed transitions. -/
@[simp] theorem InnerTrace.prefix_length {E S : Type*} (t : InnerTrace E S) (k : ℕ)
    (events : List EvaluationKind) : (t.prefix k events).length = k := rfl

/-- Every executed prefix transition retains its original query events. -/
theorem InnerTrace.prefix_queries_of_lt {E S : Type*} (t : InnerTrace E S) {k i : ℕ}
    (events : List EvaluationKind) (hi : i < k) :
    (t.prefix k events).queries i = t.queries i := by simp [InnerTrace.prefix, hi]

/-- The actual return boundary contains exactly the supplied paid observations. -/
@[simp] theorem InnerTrace.prefix_queries_terminal {E S : Type*} (t : InnerTrace E S)
    (k : ℕ) (events : List EvaluationKind) : (t.prefix k events).queries k = events := by
  simp [InnerTrace.prefix]

/-- Every channel count of an actual prefix is bounded by the complete execution count,
provided its return events are retained from the completion's current stage. -/
theorem InnerTrace.prefix_evaluations_le {E S : Type*} (t : InnerTrace E S) {k : ℕ}
    (hk : k ≤ t.length) {events : List EvaluationKind} (he : events.Sublist (t.queries k))
    (a : EvaluationKind) : (t.prefix k events).evaluations a ≤ t.evaluations a := by
  classical
  unfold evaluations
  apply le_trans (Finset.sum_le_sum (g := fun i => (t.queries i).count a) ?_)
  · exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.add_le_add_right hk 1))
  · intro i _
    simp only [InnerTrace.prefix]
    split_ifs with hlt heq
    · exact le_rfl
    · subst i
      exact he.count_le a
    · exact Nat.zero_le _

/-- A complete prefix retaining its complete terminal list has exactly the original
count in every evaluation channel. -/
@[simp] theorem InnerTrace.prefix_evaluations_full {E S : Type*} (t : InnerTrace E S)
    (a : EvaluationKind) :
    (t.prefix t.length (t.queries t.length)).evaluations a = t.evaluations a := by
  classical
  unfold evaluations
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ t.length := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hc : i < t.length ∨ i = t.length := by omega
  rcases hc with hc | rfl
  · simp [InnerTrace.prefix, hc]
  · simp [InnerTrace.prefix]

variable {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A supplied complete INNER execution with an actually monitored stopping stage.
The completion witnesses the selected solver's ordinary guarantee, not the outcome of the
outer algorithm. Its unexecuted suffix is excluded from the charged trace. The interruption
predicate is evaluated on the actual point, and output radii remain positive and bounded. -/
structure InterruptibleInnerCall (X : Set E) (f : E → ℝ) (low : ℝ)
    (q : ℕ) (τ δ π : ℕ → ℝ) (κ : EvaluationKind → ℝ)
    (step : (ℕ → ℝ) → E × S → E × S → List EvaluationKind → Prop)
    (terminal : (ℕ → ℝ) → E × S → List EvaluationKind → Prop)
    (interrupt : E → Prop) (t : InnerTrace E S) where
  /-- An actual complete execution of the selected INNER method. -/
  completion : InnerTrace E S
  /-- The radii that the ordinary complete invocation would return. -/
  completionRadius : ℕ → ℝ
  /-- The ordinary solver guarantees hold on the supplied completion. -/
  contract : InnerContract X f low q τ completionRadius π κ step terminal completion
  /-- The actual call stops no later than its supplied completion. -/
  length_le : t.length ≤ completion.length
  /-- Actual observations made at the returned current point. -/
  returnedEvents : List EvaluationKind
  /-- Return observations are part of the complete solver's paid current-stage events. -/
  returned_sublist : returnedEvents.Sublist (completion.queries t.length)
  /-- A complete return retains every ordinary terminal event. -/
  returned_full : t.length = completion.length → returnedEvents = completion.queries t.length
  /-- The executed call is exactly the selected prefix, including its paid return boundary. -/
  trace_eq : t = completion.prefix t.length returnedEvents
  /-- An early return passes the actual interruption test. -/
  early : t.length < completion.length → interrupt (t.point t.length)
  /-- No earlier monitored point has passed the interruption test. -/
  first : ∀ i < t.length, ¬interrupt (t.point i)
  /-- The solver monitors objective nonincrease at the point actually returned. -/
  objective_nonincrease : f (t.point t.length) ≤ f (t.point 0)
  /-- Actual output radii are admissible even at an early return. -/
  radius : ∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1
  /-- A complete return retains the ordinary solver's output radii. -/
  radius_full : t.length = completion.length →
    ∀ j ∈ Finset.Icc 1 q, δ j = completionRadius j

variable {X : Set E} {f : E → ℝ} {low : ℝ} {q : ℕ} {τ δ π : ℕ → ℝ}
  {κ : EvaluationKind → ℝ}
  {step : (ℕ → ℝ) → E × S → E × S → List EvaluationKind → Prop}
  {terminal : (ℕ → ℝ) → E × S → List EvaluationKind → Prop}
  {interrupt : E → Prop} {t : InnerTrace E S}

/-- Every actually visited point of an interrupted invocation is feasible. -/
theorem InterruptibleInnerCall.feasible
    (h : InterruptibleInnerCall X f low q τ δ π κ step terminal interrupt t)
    {i : ℕ} (hi : i ≤ t.length) : t.point i ∈ X := by
  have he : t.point i = h.completion.point i := by
    have hh := congrArg (fun z : InnerTrace E S => z.point i) h.trace_eq
    exact hh
  rw [he]
  exact h.contract.feasible i (hi.trans h.length_le)

/-- Every actually executed transition obeys the selected INNER solver's real rules. -/
theorem InterruptibleInnerCall.legal
    (h : InterruptibleInnerCall X f low q τ δ π κ step terminal interrupt t)
    {i : ℕ} (hi : i < t.length) :
    step τ (t.point i, t.state i) (t.point (i + 1), t.state (i + 1)) (t.queries i) := by
  have heq : ∀ j, t.point j = h.completion.point j ∧ t.state j = h.completion.state j := by
    intro j
    have hp := congrArg (fun z : InnerTrace E S => z.point j) h.trace_eq
    have hs := congrArg (fun z : InnerTrace E S => z.state j) h.trace_eq
    exact ⟨hp, hs⟩
  rw [(heq i).1, (heq i).2, (heq (i + 1)).1, (heq (i + 1)).2]
  have hq : t.queries i = h.completion.queries i := by
    conv_lhs => rw [h.trace_eq]
    exact h.completion.prefix_queries_of_lt h.returnedEvents hi
  rw [hq]
  exact h.contract.legal i (hi.trans_le h.length_le)

/-- Every interrupted evaluation count inherits the complete invocation's valid bound. -/
theorem InterruptibleInnerCall.cost
    (h : InterruptibleInnerCall X f low q τ δ π κ step terminal interrupt t)
    (a : EvaluationKind) : (t.evaluations a : ℝ) ≤
      κ a * (f (t.point 0) - low) * toleranceWeight q τ π := by
  have he : t.point 0 = h.completion.point 0 := by
    have hh := congrArg (fun z : InnerTrace E S => z.point 0) h.trace_eq
    exact hh
  have hcount : t.evaluations a ≤ h.completion.evaluations a := by
    conv_lhs => rw [h.trace_eq]
    exact h.completion.prefix_evaluations_le h.length_le h.returned_sublist a
  have hcast : (t.evaluations a : ℝ) ≤ (h.completion.evaluations a : ℝ) := by
    exact_mod_cast hcount
  exact hcast.trans (by simpa only [he] using h.contract.cost a)

/-- An interrupted invocation returns either a true interruption event or the ordinary
all-order Taylor-gap guarantee at the actual output radii. -/
theorem InterruptibleInnerCall.gap_or_interrupt
    (h : InterruptibleInnerCall X f low q τ δ π κ step terminal interrupt t) :
    interrupt (t.point t.length) ∨
      ∀ j ∈ Finset.Icc 1 q,
        TaylorCriticality.gapOn (TaylorCriticality.taylorDecrement f j (t.point t.length))
          (ConstrainedTaylorCriticality.feasibleDisplacements X (t.point t.length) ∩
            closedBall 0 (δ j)) ≤ τ j * δ j ^ j / (j.factorial : ℝ) := by
  rcases lt_or_eq_of_le h.length_le with hlt | heq
  · exact Or.inl (h.early hlt)
  · right
    have hp : t.point t.length = h.completion.point h.completion.length := by
      have hh := congrArg (fun z : InnerTrace E S => z.point t.length) h.trace_eq
      simpa only [InnerTrace.prefix_point, heq] using hh
    intro j hj
    rw [hp, h.radius_full heq j hj]
    exact h.contract.gap j hj

/-- An ordinary complete invocation is an interruptible invocation when none of its
preceding points passes the monitor. Its complete terminal events are retained. -/
def InterruptibleInnerCall.ofInnerContract
    (h : InnerContract X f low q τ δ π κ step terminal t)
    (hfirst : ∀ i < t.length, ¬interrupt (t.point i)) :
    InterruptibleInnerCall X f low q τ δ π κ step terminal interrupt
      (t.prefix t.length (t.queries t.length)) where
  completion := t
  completionRadius := δ
  contract := h
  length_le := le_rfl
  returnedEvents := t.queries t.length
  returned_sublist := List.Sublist.refl _
  returned_full := by intro _; rfl
  trace_eq := rfl
  early := by simp
  first := hfirst
  objective_nonincrease := h.objective_nonincrease
  radius := h.radius
  radius_full := by intro _ j _; rfl

end Optimization.ResidualLeastSquares
