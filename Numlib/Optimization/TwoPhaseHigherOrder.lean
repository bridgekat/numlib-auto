import Numlib.Optimization.InterruptibleInner
import Numlib.Optimization.TwoPhaseTargets

/-!
# Higher-order target updates with actual interrupted inner executions

The target objective is the canonical squared augmented residual. All-order tests use its
actual Taylor jets. A finite outer execution retains the inner query prefixes and solver
state; only literal stopping tests, not an outer stationarity conclusion, govern its end.
-/

noncomputable section
open Set Metric
namespace Optimization.TwoPhaseTargets
open ResidualLeastSquares ConstrainedTaylorCriticality TaylorCriticality
variable {E F S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

/-- All residual-scaled target Taylor-gap tests at the supplied output radii. -/
def ScaledTargetGaps (X : Set E) (f : E → ℝ) (c : E → F) (q : ℕ)
    (ε δ : ℕ → ℝ) (t : ℝ) (x : E) : Prop :=
  ∀ j ∈ Finset.Icc 1 q,
    gapOn (taylorDecrement (TargetLeastSquares.objective f c t) j x)
      (feasibleDisplacements X x ∩ closedBall 0 (δ j)) ≤
        ε j * residualNorm f c t x * δ j ^ j / (j.factorial : ℝ)

/-- The target criticality test exposes exactly its actual all-order Taylor inequalities. -/
theorem scaledTargetGaps_iff {X : Set E} {f : E → ℝ} {c : E → F} {q : ℕ}
    {ε δ : ℕ → ℝ} {t : ℝ} {x : E} :
    ScaledTargetGaps X f c q ε δ t x ↔
      ∀ j ∈ Finset.Icc 1 q,
        gapOn (taylorDecrement (TargetLeastSquares.objective f c t) j x)
          (feasibleDisplacements X x ∩ closedBall 0 (δ j)) ≤
            ε j * residualNorm f c t x * δ j ^ j / (j.factorial : ℝ) := Iff.rfl

/-- Literal target update: reset after a small residual, otherwise reflect after crossing
below the old target, and retain the old target in the third terminal branch. -/
def targetAfter (f : E → ℝ) (c : E → F) (θ ε₀ t : ℝ) (x : E) : ℝ :=
  if residualNorm f c t x < θ * ε₀ then resetTarget f c ε₀ x
  else if f x < t then reflectTarget f t x else t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The small-residual branch resets the target by the square-root formula. -/
theorem targetAfter_of_small {f : E → ℝ} {c : E → F} {θ ε₀ t : ℝ} {x : E}
    (h : residualNorm f c t x < θ * ε₀) :
    targetAfter f c θ ε₀ t x = resetTarget f c ε₀ x := by simp [targetAfter, h]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The large-residual crossing branch reflects the target. -/
theorem targetAfter_of_crossing {f : E → ℝ} {c : E → F} {θ ε₀ t : ℝ} {x : E}
    (hr : θ * ε₀ ≤ residualNorm f c t x) (hf : f x < t) :
    targetAfter f c θ ε₀ t x = reflectTarget f t x := by
  simp [targetAfter, not_lt.mpr hr, hf]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The third branch retains the old target, including the equality boundary `f x = t`. -/
theorem targetAfter_of_noncrossing {f : E → ℝ} {c : E → F} {θ ε₀ t : ℝ} {x : E}
    (hr : θ * ε₀ ≤ residualNorm f c t x) (hf : t ≤ f x) :
    targetAfter f c θ ε₀ t x = t := by
  simp [targetAfter, not_lt.mpr hr, not_lt.mpr hf]

/-- An inner invocation may stop early at precisely the small-residual or target-crossing
tests; its ordinary termination retains the all-order INNER guarantee. -/
def TargetInterrupt (f : E → ℝ) (c : E → F) (θ ε₀ t : ℝ) (x : E) : Prop :=
  residualNorm f c t x < θ * ε₀ ∨ f x < t

/-- The outer algorithm stops at the third branch, or after a target update when all actual
Taylor-gap tests pass. The update itself chooses between reset, reflection and retention. -/
def TargetOuterStops (X : Set E) (f : E → ℝ) (c : E → F) (q : ℕ)
    (θ ε₀ : ℝ) (ε δ : ℕ → ℝ) (t : ℝ) (x : E) : Prop :=
  (θ * ε₀ ≤ residualNorm f c t x ∧ t ≤ f x) ∨
    ScaledTargetGaps X f c q ε δ (targetAfter f c θ ε₀ t x) x

/-- Actual Phase-2 data, indexed from zero: index zero is the first Phase-2 point and
initial target. Paid component observations are recorded in each inner prefix; target-only
arithmetic reuses those responses. Smoothness identities justify jet reconstruction. -/
structure TargetTrace (E S : Type*) where
  /-- Actual outer points. -/
  point : ℕ → E
  /-- Actual targets, constant during each individual inner invocation. -/
  target : ℕ → ℝ
  /-- Positive output radii at the outer points. -/
  radius : ℕ → ℕ → ℝ
  /-- Retained solver state at outer points. -/
  state : ℕ → S
  /-- Actually executed inner prefixes. -/
  inner : ℕ → InnerTrace E S
  /-- Initial function/residual events needed to construct the first target. -/
  initialQueries : List EvaluationKind

/-- Charge the initial target evaluation and exactly the executed inner prefixes.
No hypothetical completion or repeated target-only arithmetic is charged. -/
def TargetTrace.evaluations (t : TargetTrace E S) (N : ℕ) (a : EvaluationKind) : ℕ :=
  t.initialQueries.count a + ∑ k ∈ Finset.range N, (t.inner k).evaluations a

/-- An exact paired component-oracle response at a specified point, with its own paid
events retained in the actual stage list. Each positive order costs one paired derivative
query. These raw component jets are the data used in retargeting; reconstructing target
jets from them additionally uses the usual smoothness identities. No such identity for
totalized derivatives of arbitrary nonsmooth functions is asserted here. -/
structure ComponentOracleResponse [NormedSpace ℝ F] (f : E → ℝ) (c : E → F)
    (q : ℕ) (x : E) (charged : List EvaluationKind) where
  /-- Events that produced this response at the specified point. -/
  events : List EvaluationKind
  /-- Every response event occurs in the actual charged stage. -/
  paid : events.Sublist charged
  /-- Returned objective value. -/
  objectiveValue : ℝ
  /-- Returned constraint value. -/
  constraintValue : F
  /-- Returned positive objective jets through the active order. -/
  objectiveJet : (j : Fin q) → E [×(j.val + 1)]→L[ℝ] ℝ
  /-- Returned positive constraint jets through the active order. -/
  constraintJet : (j : Fin q) → E [×(j.val + 1)]→L[ℝ] F
  /-- Exact objective-value oracle semantics. -/
  objective_exact : objectiveValue = f x
  /-- Exact constraint-value oracle semantics. -/
  constraint_exact : constraintValue = c x
  /-- Exact objective-jet oracle semantics. -/
  objective_jet_exact : ∀ j, objectiveJet j = iteratedFDeriv ℝ (j.val + 1) f x
  /-- Exact constraint-jet oracle semantics. -/
  constraint_jet_exact : ∀ j, constraintJet j = iteratedFDeriv ℝ (j.val + 1) c x
  /-- A paired objective/constraint value query is paid. -/
  value_paid : 1 ≤ events.count .function
  /-- Every active derivative order is paid. -/
  derivatives_paid : q ≤ events.count .derivative

/-- A response's value evaluation is included in the actual stage count. -/
theorem ComponentOracleResponse.value_count [NormedSpace ℝ F]
    {f : E → ℝ} {c : E → F} {q : ℕ} {x : E} {charged : List EvaluationKind}
    (h : ComponentOracleResponse f c q x charged) : 1 ≤ charged.count .function :=
  h.value_paid.trans (h.paid.count_le .function)

/-- All requested component derivative orders are included in the actual stage count. -/
theorem ComponentOracleResponse.derivative_count [NormedSpace ℝ F]
    {f : E → ℝ} {c : E → F} {q : ℕ} {x : E} {charged : List EvaluationKind}
    (h : ComponentOracleResponse f c q x charged) : q ≤ charged.count .derivative :=
  h.derivatives_paid.trans (h.paid.count_le .derivative)

variable [NormedSpace ℝ F]

/-- A finite lawful Phase-2 execution with arbitrary positive criticality order. Each
supplied inner invocation is an actually executed prefix of a guaranteed INNER run. -/
structure PhaseTwoExecution (X : Set E) (f : E → ℝ) (c : E → F) (q : ℕ)
    (θ ε₀ β : ℝ) (ε π : ℕ → ℝ) (κ : EvaluationKind → ℝ)
    (step : ℝ → (ℕ → ℝ) → E × S → E × S → List EvaluationKind → Prop)
    (terminal : ℝ → (ℕ → ℝ) → E × S → List EvaluationKind → Prop)
    (t : TargetTrace E S) (N : ℕ) : Prop where
  /-- Active orders are nonempty. -/
  order_pos : 1 ≤ q
  /-- The feasibility fraction is strictly between zero and one. -/
  fraction : 0 < θ ∧ θ < 1
  /-- The primal tolerance is positive and at most one. -/
  primal : 0 < ε₀ ∧ ε₀ ≤ 1
  /-- Every active dual tolerance is positive and at most one. -/
  dual : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1
  /-- The inner scaling factor is positive and no larger than the feasibility fraction. -/
  factor : 0 < β ∧ β ≤ θ
  /-- Phase 2 starts from an approximately feasible point. -/
  initial_feasible : t.point 0 ∈ X
  /-- Phase 1 has met its feasibility threshold. -/
  initial_constraint : ‖c (t.point 0)‖ ≤ θ * ε₀
  /-- The first target uses the actual square-root reset formula. -/
  initial_target : t.target 0 = resetTarget f c ε₀ (t.point 0)
  /-- The initial radius is admissible, including zero-call Phase-1 returns. -/
  initial_radius : ∀ j ∈ Finset.Icc 1 q, 0 < t.radius 0 j ∧ t.radius 0 j ≤ 1
  /-- The initial objective value needed for the target is evaluated. -/
  initial_value : 1 ≤ t.initialQueries.count .function
  /-- Step 1 is called at least once, even if an initial gap test would pass. -/
  length_pos : 0 < N
  /-- Each executed inner invocation starts at the current outer point. -/
  start : ∀ k < N, (t.inner k).point 0 = t.point k
  /-- The actual inner return is the following outer point. -/
  finish : ∀ k < N, (t.inner k).point (t.inner k).length = t.point (k + 1)
  /-- Inner calls use the retained solver state. -/
  state_start : ∀ k < N, (t.inner k).state 0 = t.state k
  /-- Output state is retained across changes to the target. -/
  state_finish : ∀ k < N, (t.inner k).state (t.inner k).length = t.state (k + 1)
  /-- Real interrupted executions use the exact target and residual-scaled input accuracy. -/
  solve : ∀ k < N, Nonempty (InterruptibleInnerCall X (TargetLeastSquares.objective f c
      (t.target k)) 0 q (fun j => β * residualNorm f c (t.target k) (t.point k) * ε j)
      (t.radius (k + 1)) π κ (step (t.target k)) (terminal (t.target k))
      (TargetInterrupt f c θ ε₀ (t.target k)) (t.inner k))
  /-- Every monitored current point, including an early return, has actual raw component
  values, and its returned point also has all active raw jets. Their queries are included
  in the completion cost through the prefix contract;
  a generic target-objective INNER guarantee alone does not supply this instrumentation. -/
  observations : ∀ k < N, ∀ i ≤ (t.inner k).length,
    Nonempty (ComponentOracleResponse f c (if i = (t.inner k).length then q else 0)
      ((t.inner k).point i) ((t.inner k).queries i))
  /-- Step 2 performs exactly the appropriate algebraic target update. -/
  update : ∀ k < N, t.target (k + 1) = targetAfter f c θ ε₀ (t.target k) (t.point (k + 1))
  /-- Earlier outer iterations fail the actual literal stopping test. -/
  continues : ∀ k, k + 1 < N →
    ¬TargetOuterStops X f c q θ ε₀ ε (t.radius (k + 1)) (t.target k) (t.point (k + 1))
  /-- The last outer iteration passes a literal terminal test. -/
  stops : TargetOuterStops X f c q θ ε₀ ε (t.radius N) (t.target (N - 1)) (t.point N)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Every literal target update makes the scalar objective residual nonnegative, including
the third branch's equality case. -/
theorem targetAfter_gap_nonneg (f : E → ℝ) (c : E → F) (θ ε₀ t : ℝ) (x : E) :
    0 ≤ f x - targetAfter f c θ ε₀ t x := by
  unfold targetAfter
  split_ifs with hs hc
  · exact reset_gap_nonneg f c ε₀ x
  · exact (reflect_gap_pos hc).le
  · exact sub_nonneg.mpr (le_of_not_gt hc)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The square root used by a small-residual reset has a nonnegative radicand. -/
theorem reset_radicand_nonneg_of_small {f : E → ℝ} {c : E → F} {θ ε₀ t : ℝ} {x : E}
    (he : 0 ≤ ε₀) (hθ : θ ≤ 1) (hr : residualNorm f c t x < θ * ε₀) :
    0 ≤ ε₀ ^ 2 - ‖c x‖ ^ 2 := by
  have hh : ‖c x‖ ≤ ε₀ := (norm_constraint_le f c t x).trans
    (hr.le.trans (by nlinarith))
  nlinarith [norm_nonneg (c x)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A residual at most the primal tolerance remains in the target residual annulus after
the actual update. The reset branch is justified by its genuine constraint component. -/
theorem targetAfter_residual_bounds {f : E → ℝ} {c : E → F} {θ ε₀ t : ℝ} {x : E}
    (he : 0 ≤ ε₀) (hθ : θ ≤ 1) (hr : residualNorm f c t x ≤ ε₀) :
    θ * ε₀ ≤ residualNorm f c (targetAfter f c θ ε₀ t x) x ∧
      residualNorm f c (targetAfter f c θ ε₀ t x) x ≤ ε₀ := by
  by_cases hs : residualNorm f c t x < θ * ε₀
  · rw [targetAfter_of_small hs, residualNorm_reset he]
    · exact ⟨by nlinarith, le_rfl⟩
    · exact (norm_constraint_le f c t x).trans (hs.le.trans (by nlinarith))
  · by_cases hc : f x < t
    · rw [targetAfter_of_crossing (le_of_not_gt hs) hc, residualNorm_reflect]
      exact ⟨le_of_not_gt hs, hr⟩
    · rw [targetAfter_of_noncrossing (le_of_not_gt hs) (le_of_not_gt hc)]
      exact ⟨le_of_not_gt hs, hr⟩

variable {X : Set E} {f : E → ℝ} {c : E → F} {q N : ℕ}
  {θ ε₀ β : ℝ} {ε π : ℕ → ℝ} {κ : EvaluationKind → ℝ}
  {step : ℝ → (ℕ → ℝ) → E × S → E × S → List EvaluationKind → Prop}
  {terminal : ℝ → (ℕ → ℝ) → E × S → List EvaluationKind → Prop}
  {t : TargetTrace E S}

/-- The actual returned point has paid raw values and every active component jet,
ready for a target change under the source smoothness assumptions. -/
theorem PhaseTwoExecution.returned_observations
    (h : PhaseTwoExecution X f c q θ ε₀ β ε π κ step terminal t N)
    {k : ℕ} (hk : k < N) :
    Nonempty (ComponentOracleResponse f c q ((t.inner k).point (t.inner k).length)
      ((t.inner k).queries (t.inner k).length)) := by
  simpa only [ite_true] using h.observations k hk (t.inner k).length le_rfl

/-- Every actually returned Phase-2 radius is admissible; no radius is manufactured by
an unexecuted completion or by a later target update. -/
theorem PhaseTwoExecution.radius
    (h : PhaseTwoExecution X f c q θ ε₀ β ε π κ step terminal t N)
    {k : ℕ} (hk : k ≤ N) {j : ℕ} (hj : j ∈ Finset.Icc 1 q) :
    0 < t.radius k j ∧ t.radius k j ≤ 1 := by
  cases k with
  | zero => exact h.initial_radius j hj
  | succ k =>
    obtain ⟨hi⟩ := h.solve k (by omega)
    exact hi.radius j hj

/-- Every outer point through the actual final index is feasible. -/
theorem PhaseTwoExecution.feasible
    (h : PhaseTwoExecution X f c q θ ε₀ β ε π κ step terminal t N)
    {k : ℕ} (hk : k ≤ N) : t.point k ∈ X := by
  cases k with
  | zero => exact h.initial_feasible
  | succ k =>
    have hkN : k < N := by omega
    obtain ⟨hi⟩ := h.solve k hkN
    simpa only [h.finish k hkN] using hi.feasible (i := (t.inner k).length) le_rfl

/-- An actual inner return cannot increase the augmented residual at its fixed target. -/
theorem PhaseTwoExecution.inner_residual_le
    (h : PhaseTwoExecution X f c q θ ε₀ β ε π κ step terminal t N)
    {k : ℕ} (hk : k < N) :
    residualNorm f c (t.target k) (t.point (k + 1)) ≤
      residualNorm f c (t.target k) (t.point k) := by
  obtain ⟨hi⟩ := h.solve k hk
  have hm := hi.objective_nonincrease
  rw [h.start k hk, h.finish k hk, objective_eq_half_sq, objective_eq_half_sq] at hm
  nlinarith [residualNorm_nonneg f c (t.target k) (t.point (k + 1)),
    residualNorm_nonneg f c (t.target k) (t.point k)]

/-- Genuine residual invariants of every finite Phase-2 execution, derived from actual
inner objective nonincrease and the three algebraic target branches. -/
theorem PhaseTwoExecution.residual_bounds
    (h : PhaseTwoExecution X f c q θ ε₀ β ε π κ step terminal t N)
    {k : ℕ} (hk : k ≤ N) :
    θ * ε₀ ≤ residualNorm f c (t.target k) (t.point k) ∧
      residualNorm f c (t.target k) (t.point k) ≤ ε₀ := by
  induction k with
  | zero =>
    rw [h.initial_target, residualNorm_reset h.primal.1.le]
    · exact ⟨by nlinarith [h.fraction.2, h.primal.1], le_rfl⟩
    · exact h.initial_constraint.trans (by nlinarith [h.fraction.2, h.primal.1])
  | succ k ih =>
    have hkN : k < N := by omega
    have hb := (h.inner_residual_le hkN).trans (ih (by omega)).2
    rw [h.update k hkN]
    exact targetAfter_residual_bounds h.primal.1.le h.fraction.2.le hb

/-- The objective-target residual is nonnegative at every actual outer point. -/
theorem PhaseTwoExecution.gap_nonneg
    (h : PhaseTwoExecution X f c q θ ε₀ β ε π κ step terminal t N)
    {k : ℕ} (hk : k ≤ N) : 0 ≤ f (t.point k) - t.target k := by
  cases k with
  | zero => rw [h.initial_target]; exact reset_gap_nonneg f c ε₀ (t.point 0)
  | succ k =>
    rw [h.update k (by omega)]
    exact targetAfter_gap_nonneg f c θ ε₀ (t.target k) (t.point (k + 1))

/-- Every actual inner return meets one of the three literal Step-1 exit tests. The
ordinary INNER accuracy is strengthened to the residual-scaled test using the derived
residual invariant, not an assumed output certificate. -/
theorem PhaseTwoExecution.inner_exit_test
    (h : PhaseTwoExecution X f c q θ ε₀ β ε π κ step terminal t N)
    {k : ℕ} (hk : k < N) :
    TargetInterrupt f c θ ε₀ (t.target k) (t.point (k + 1)) ∨
      ScaledTargetGaps X f c q ε (t.radius (k + 1)) (t.target k) (t.point (k + 1)) := by
  obtain ⟨hi⟩ := h.solve k hk
  rcases hi.gap_or_interrupt with hearly | hgap
  · exact Or.inl (by simpa only [h.finish k hk] using hearly)
  · by_cases hs : TargetInterrupt f c θ ε₀ (t.target k) (t.point (k + 1))
    · exact Or.inl hs
    · right
      have hr : θ * ε₀ ≤ residualNorm f c (t.target k) (t.point (k + 1)) := by
        by_contra hn
        exact hs (Or.inl (lt_of_not_ge hn))
      have hscale : β * residualNorm f c (t.target k) (t.point k) ≤
          residualNorm f c (t.target k) (t.point (k + 1)) := by
        calc
          β * residualNorm f c (t.target k) (t.point k) ≤ β * ε₀ :=
            mul_le_mul_of_nonneg_left (h.residual_bounds (by omega)).2 h.factor.1.le
          _ ≤ θ * ε₀ := mul_le_mul_of_nonneg_right h.factor.2 h.primal.1.le
          _ ≤ _ := hr
      intro j hj
      have hg := hgap j hj
      rw [h.finish k hk] at hg
      apply hg.trans
      have hδ : 0 ≤ t.radius (k + 1) j := (hi.radius j hj).1.le
      have he : 0 ≤ ε j := (h.dual j hj).1.le
      have hh := mul_le_mul_of_nonneg_right hscale he
      have hhh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hh (pow_nonneg hδ j))
        (Nat.cast_nonneg (j.factorial) : (0 : ℝ) ≤ j.factorial)
      convert hhh using 1; ring

/-- At the actual terminal point all residual-scaled target tests hold, including the
third branch. There, the inner exit test forces its ordinary all-order alternative. -/
theorem PhaseTwoExecution.terminal_scaled_gaps
    (h : PhaseTwoExecution X f c q θ ε₀ β ε π κ step terminal t N) :
    ScaledTargetGaps X f c q ε (t.radius N) (t.target N) (t.point N) := by
  have hN := h.length_pos
  have hk : N - 1 < N := by omega
  have he : N - 1 + 1 = N := by omega
  have ht : t.target N = targetAfter f c θ ε₀ (t.target (N - 1)) (t.point N) := by
    simpa only [he] using h.update (N - 1) hk
  rcases h.stops with hb | hg
  · have hkeep := targetAfter_of_noncrossing hb.1 hb.2
    have hexit := h.inner_exit_test hk
    simp only [he] at hexit
    have hn : ¬TargetInterrupt f c θ ε₀ (t.target (N - 1)) (t.point N) := by
      rintro (hs | hc)
      · exact not_lt_of_ge hb.1 hs
      · exact not_lt_of_ge hb.2 hc
    have hg := hexit.resolve_left hn
    rwa [ht, hkeep]
  · rwa [ht]

end Optimization.TwoPhaseTargets
