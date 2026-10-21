import Numlib.Optimization.CompositeRegularization
import Numlib.Optimization.CompositeTaylorModelConstants

/-!
# Smooth executions as genuine composite executions

A nonzero norm composition with a constant zero inner map preserves smooth model values,
gaps, and acceptance ratios. Actual computed composite failures are supplied explicitly when
embedding transitions, since the two methods have different strict boundary conventions.
-/

noncomputable section
open scoped Nat NNReal
open Set Metric
namespace Optimization.CompositeRegularization
open RegularizedTaylorModel CompositeTaylorModels TaylorCriticality
open HigherOrderApproximateRegularization (Parameters ValidRadii OuterState OuterOutcome)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The smooth part of the composite regularized model is the canonical smooth model. -/
theorem smoothModel_eq (f : E → ℝ) (p : ℕ) (x : E) (σ : ℝ) :
    smoothModel f p x σ = HigherOrderApproximateRegularization.model f p x σ := by
  ext s
  unfold smoothModel HigherOrderApproximateRegularization.model HigherOrderRegularization.model
  ring

/-- The generalized inner decrement agrees with its actual smooth-model counterpart. -/
@[simp] theorem modelDecrement_const_zero (f : E → ℝ)
    (h : LipschitzSubadditiveComposition F) (p j : ℕ) (x : E) (σ : ℝ) (s d : E) :
    modelDecrement f (fun _ => (0 : F)) h p j x σ s d =
      taylorDecrement (HigherOrderApproximateRegularization.model f p x σ) j s d := by
  simp [modelDecrement, vectorModel, smoothModel_eq]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem objective_const_zero (f : E → ℝ) (h : LipschitzSubadditiveComposition F)
    (x : E) : objective f (fun _ => (0 : F)) h x = f x := by simp [objective]

/-- Smooth model-step certificates yield genuine composite certificates under the embedding. -/
def ModelStep.ofSmooth {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ} {δ : ℕ → ℝ}
    (h : LipschitzSubadditiveComposition F)
    (a : HigherOrderApproximateRegularization.ModelStep P f x σ δ) :
    ModelStep P f (fun _ => (0 : F)) h x σ where
  step := a.step
  radii := a.radii
  radii_valid := a.radii_valid
  nonincrease := by simpa using a.nonincrease
  direction := a.direction
  quality := by
    rcases a.quality with ha | ha
    · exact Or.inl ha.1.le
    · right
      intro j hj hjq
      obtain ⟨hw, ht⟩ := ha j hj hjq
      refine ⟨⟨hw.feasible, ?_⟩, ?_⟩
      · simpa [vectorModel, smoothModel_eq] using hw.fraction_le
      · simpa using ht

/-- A successful smooth computed test remains successful with the source's nonstrict bound. -/
def PassedTest.ofSmooth {P : Parameters} {f : E → ℝ} {x : E} {δ : ℕ → ℝ}
    (h : LipschitzSubadditiveComposition F)
    (a : HigherOrderApproximateRegularization.PassedTest P f x δ) :
    PassedTest P f (fun _ => (0 : F)) h x δ where
  direction := a.direction
  witness j hj hjq := ⟨(a.witness j hj hjq).feasible, by
    simpa using (a.witness j hj hjq).fraction_le⟩
  passes j hj hjq := by
    simpa only [decrement_const_zero, mul_div_assoc, mul_assoc] using (a.passes j hj hjq).le

/-- A strict true generalized gap failure gives an actual strict computed failure.
An exact maximizing direction is permissible even when the requested fraction is smaller. -/
theorem failedTest_of_true_gap [ProperSpace E] {P : Parameters} {f : E → ℝ} {c : E → F}
    {h : F → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h) {x : E} {δ : ℕ → ℝ}
    (hδ : ValidRadii P δ) (hfail : ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      P.epsilon j * δ j ^ j / (j ! : ℝ) <
        gapOn (decrement f c h j x) (closedBall 0 (δ j))) :
    Nonempty (FailedTest P f c h x δ) := by
  classical
  let bad (j : ℕ) := 1 ≤ j ∧ j ≤ P.q ∧ P.epsilon j * δ j ^ j / (j ! : ℝ) <
    gapOn (decrement f c h j x) (closedBall 0 (δ j))
  have hb : ∃ j, bad j := hfail
  let j := Nat.find hb
  have hj : bad j := Nat.find_spec hb
  have he : ∀ i, ∃ d : E, (1 ≤ i ∧ i ≤ j) →
      GapWitness f c h i x (δ i) P.fraction d ∧
      decrement f c h i x d =
        P.fraction * gapOn (decrement f c h i x) (closedBall 0 (δ i)) := by
    intro i
    by_cases hi : 1 ≤ i ∧ i ≤ j
    · obtain ⟨d, hd, heq⟩ := exists_fraction_gapWitness f c hh i x
        (hδ i hi.1 (hi.2.trans hj.2.1)).1.le P.fraction_pos.le P.fraction_le_one
      exact ⟨d, fun _ => ⟨hd, heq⟩⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose d hd using he
  refine ⟨⟨j, hj.1, hj.2.1, d, fun i hi hij => (hd i ⟨hi, hij⟩).1, ?_, ?_⟩⟩
  · intro i hi hij
    rw [(hd i ⟨hi, hij.le⟩).2]
    apply mul_le_mul_of_nonneg_left _ P.fraction_pos.le
    by_contra hn
    have hi' : bad i := ⟨hi, hij.le.trans hj.2.1, lt_of_not_ge hn⟩
    exact (Nat.find_min hb hij) hi'
  · rw [(hd j ⟨hj.1, le_rfl⟩).2]
    exact mul_lt_mul_of_pos_left hj.2.2 P.fraction_pos

/-- Continuing smooth transitions embed whenever the actual composite failed test is supplied.
No implication from a failed conservative witness to true gap failure is used. -/
theorem OuterTransition.ofSmooth {P : Parameters} {f : E → ℝ}
    (h : LipschitzSubadditiveComposition F) {a b : OuterState E}
    {nf nd : ℕ} (ht : HigherOrderApproximateRegularization.OuterTransition P f a (.next b) nf nd)
    (hfail : a.test = true → Nonempty (FailedTest P f (fun _ => (0 : F)) h a.point a.radii)) :
    OuterTransition P f (fun _ => (0 : F)) h a (.next b) nf nd := by
  cases ht with
  | trial hf hcache trial hstrict σ hu =>
    have hr : ratio f (fun _ => (0 : F)) h P.p a.point trial.step =
        (f a.point - f (a.point + trial.step)) / taylorDecrement f P.p a.point trial.step := by
      simp [ratio]
    simpa only [ModelStep.ofSmooth, hr] using
      OuterTransition.trial a hfail hcache (.ofSmooth h trial)
      (by simpa only [ModelStep.ofSmooth, regularizedModel_const_zero] using hstrict) σ
      (by simpa only [ModelStep.ofSmooth, hr] using hu)

/-- A finite smooth execution ending at its true stopping test embeds with exactly the same
function and derivative costs, provided its continuing computed tests have composite failures. -/
def OuterExecution.ofSmooth {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (h : LipschitzSubadditiveComposition F)
    (run : HigherOrderApproximateRegularization.OuterExecution P f x σ δ N)
    (hstop : run.last = .stopTest (run.state N))
    (hfail : ∀ k, k < N → (run.state k).test = true →
      Nonempty (FailedTest P f (fun _ => (0 : F)) h (run.state k).point (run.state k).radii)) :
    OuterExecution P f (fun _ => (0 : F)) h x σ δ N where
  state := run.state
  functionCalls := run.functionCalls
  derivativeCalls := run.derivativeCalls
  last := .stopTest (run.state N)
  initial := run.initial
  valid := run.valid
  transition k hk := OuterTransition.ofSmooth h (run.transition k hk) (hfail k hk)
  final := by
    have ht := run.final
    rw [hstop] at ht
    generalize hnf : run.functionCalls N = nf at ht ⊢
    generalize hnd : run.derivativeCalls N = nd at ht ⊢
    generalize ha : run.state N = a at ht ⊢
    cases ht with
    | stop ht hc hp => exact .stop _ ht hc (.ofSmooth h hp)

/-- The constant embedding preserves all actual function calls. -/
theorem OuterExecution.ofSmooth_functionCount {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (h : LipschitzSubadditiveComposition F)
    (run : HigherOrderApproximateRegularization.OuterExecution P f x σ δ N)
    (hstop : run.last = .stopTest (run.state N))
    (hfail : ∀ k, k < N → (run.state k).test = true →
      Nonempty (FailedTest P f (fun _ => (0 : F)) h (run.state k).point (run.state k).radii)) :
    (OuterExecution.ofSmooth h run hstop hfail).functionCount = run.functionCount := rfl

/-- The constant embedding preserves all actual derivative calls. -/
theorem OuterExecution.ofSmooth_derivativeCount {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (h : LipschitzSubadditiveComposition F)
    (run : HigherOrderApproximateRegularization.OuterExecution P f x σ δ N)
    (hstop : run.last = .stopTest (run.state N))
    (hfail : ∀ k, k < N → (run.state k).test = true →
      Nonempty (FailedTest P f (fun _ => (0 : F)) h (run.state k).point (run.state k).radii)) :
    (OuterExecution.ofSmooth h run hstop hfail).derivativeCount = run.derivativeCount := rfl

end Optimization.CompositeRegularization
