import Numlib.Optimization.HigherOrderTrustRegion

/-!
# Trust-region steps with implicit derivative accuracy

An accuracy refinement is forced by a computed all-orders test or by a failed
step-accuracy check. Function ratios use exact objective values and the actual
polynomial supplied by an accuracy oracle. A prefix has no stopping certificate.
-/

noncomputable section
open scoped Nat
attribute [local instance] Classical.propDecidable
namespace Optimization.InexactTrustRegion
open InexactTaylorModels TaylorCriticality HigherOrderTrustRegion
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An arbitrary derivative oracle with fixed, existentially hidden error multipliers. -/
structure Oracle (f : E → ℝ) (q : ℕ) where
  derivative : E → (ℕ → ℝ) → ∀ i : ℕ,
    ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ
  accuracy : ∃ κ : ℕ → ℝ, (∀ i ∈ Finset.Icc 1 q, 0 ≤ κ i) ∧
    ∀ x h, (∀ i ∈ Finset.Icc 1 q, 0 < h i) →
      ∀ i ∈ Finset.Icc 1 q,
        ‖derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ κ i * h i

/-- Accuracy reduction and step-accuracy parameters, independent of unknown oracle errors. -/
structure AccuracyParameters where
  contraction : ℝ
  stepConstant : ℝ
  contraction_pos : 0 < contraction
  contraction_lt_one : contraction < 1
  stepConstant_pos : 0 < stepConstant

/-- The two forced accuracy branches and the branch that evaluates a trial objective. -/
inductive Branch where
  | testRefinement
  | stepRefinement
  | trial
  deriving DecidableEq

/-- Actual data from a finite or infinite execution, including the requests to the oracle. -/
structure Trace (E : Type*) extends HigherOrderTrustRegion.Trace E where
  request : ℕ → ℕ → ℝ
  branch : ℕ → Branch

/-- Coefficients actually returned for the current point and request vector. -/
def coefficients {f : E → ℝ} {q : ℕ} (O : Oracle f q) (t : Trace E) (k : ℕ) :=
  O.derivative (t.point k) (t.request k)

/-- The actual approximate Taylor decrement, with no function-value approximation. -/
def prediction {f : E → ℝ} {q : ℕ} (O : Oracle f q) (t : Trace E)
    (k j : ℕ) (s : E) : ℝ := decrement (coefficients O t k) j s

/-- The compact-ball criticality gap of the actual returned polynomial. -/
def approximateGap {f : E → ℝ} {q : ℕ} (O : Oracle f q) (t : Trace E)
    (k j : ℕ) (δ : ℝ) : ℝ := gapOn (InexactTrustRegion.prediction O t k j) (closedBall 0 δ)

/-- The radius of the computed optimality test. -/
def testRadius (p : Parameters) (t : Trace E) (k : ℕ) : ℝ := min (t.radius k) p.theta

/-- The literal computed half-threshold test, which requests refinement rather than stops. -/
def AllPass {f : E → ℝ} {q : ℕ} (p : Parameters) (epsilon : ℕ → ℝ)
    (O : Oracle f q) (t : Trace E) (k : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ q → InexactTrustRegion.prediction O t k j (t.witness k j) ≤
    p.fraction * epsilon j * testRadius p t k ^ j / (2 * (j ! : ℝ))

/-- The literal candidate-step accuracy check on every requested derivative order. -/
def StepAccurate (a : AccuracyParameters) (q : ℕ) (t : Trace E) (k : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 q, t.request k i ≤ a.stepConstant * ‖t.step k‖ ^ (q - i + 1)

/-- Acceptance uses exact function values and the selected approximate decrement. -/
def ratio {f : E → ℝ} {q : ℕ} (O : Oracle f q) (t : Trace E) (k : ℕ) : ℝ :=
  (f (t.point k) - f (t.point k + t.step k)) /
    InexactTrustRegion.prediction O t k (t.order k) (t.step k)

/-- A successful iteration is an executed trial whose actual ratio passes acceptance. -/
def Successful {f : E → ℝ} {q : ℕ} (p : Parameters) (O : Oracle f q)
    (t : Trace E) (k : ℕ) : Prop := t.branch k = .trial ∧ p.eta1 ≤ ratio O t k

/-- A selected witness's scaled decrement. Only the non-test branches use this value. -/
def scaledGap {f : E → ℝ} {q : ℕ} (p : Parameters) (O : Oracle f q)
    (t : Trace E) (k : ℕ) : ℝ :=
  ((t.order k)! : ℝ) * InexactTrustRegion.prediction O t k (t.order k) (t.witness k (t.order k)) /
    testRadius p t k ^ t.order k

/-- Legal executed transitions. Test refinement requires all computed witnesses to pass;
step refinement requires the selected failure and a failed accuracy check. Trial transitions
preserve requests, refinement transitions contract them, and rejected trials retain their jets.
The selected witness is retained when a rejected trial returns to cached step computation. -/
structure LegalPrefix {f : E → ℝ} {q : ℕ} (p : Parameters) (a : AccuracyParameters)
    (epsilon : ℕ → ℝ) (O : Oracle f q) (t : Trace E) (N : ℕ) : Prop where
  initial_pos : 0 < t.radius 0
  initial_cap : t.radius 0 ≤ p.radiusMax
  request_pos : ∀ i ∈ Finset.Icc 1 q, 0 < t.request 0 i
  witness_feasible : ∀ k ≤ N, ∀ j, 1 ≤ j → j ≤ q →
    ‖t.witness k j‖ ≤ testRadius p t k
  witness_fraction : ∀ k ≤ N, ∀ j, 1 ≤ j → j ≤ q →
    p.fraction * approximateGap O t k j (testRadius p t k) ≤
      InexactTrustRegion.prediction O t k j (t.witness k j)
  test_branch : ∀ k < N, t.branch k = .testRefinement ↔ AllPass p epsilon O t k
  order_pos : ∀ k < N, t.branch k ≠ .testRefinement → 1 ≤ t.order k
  order_le : ∀ k < N, t.branch k ≠ .testRefinement → t.order k ≤ q
  first_failure : ∀ k < N, t.branch k ≠ .testRefinement →
    ∀ j, 1 ≤ j → j < t.order k → InexactTrustRegion.prediction O t k j (t.witness k j) ≤
      p.fraction * epsilon j * testRadius p t k ^ j / (2 * (j ! : ℝ))
  failure : ∀ k < N, t.branch k ≠ .testRefinement →
    p.fraction * epsilon (t.order k) * testRadius p t k ^ t.order k /
      (2 * ((t.order k)! : ℝ)) <
      InexactTrustRegion.prediction O t k (t.order k) (t.witness k (t.order k))
  step_feasible : ∀ k < N, t.branch k ≠ .testRefinement → ‖t.step k‖ ≤ t.radius k
  prediction : ∀ k < N, t.branch k ≠ .testRefinement →
    InexactTrustRegion.prediction O t k (t.order k) (t.witness k (t.order k)) ≤
      InexactTrustRegion.prediction O t k (t.order k) (t.step k)
  step_branch : ∀ k < N, t.branch k ≠ .testRefinement →
    (t.branch k = .trial ↔ StepAccurate a q t k)
  iterate : ∀ k < N, t.point (k + 1) =
    if Successful p O t k then t.point k + t.step k else t.point k
  request_update : ∀ k < N, ∀ i, t.request (k + 1) i =
    if t.branch k = .trial then t.request k i else a.contraction * t.request k i
  accuracy_radius : ∀ k < N, t.branch k ≠ .trial → t.radius (k + 1) = t.radius k
  trial_radius : ∀ k < N, t.branch k = .trial →
    if p.eta2 ≤ ratio O t k
    then t.radius (k + 1) ∈ Icc (t.radius k) (min p.radiusMax (p.gamma3 * t.radius k))
    else if p.eta1 ≤ ratio O t k
    then t.radius (k + 1) ∈ Icc (p.gamma2 * t.radius k) (t.radius k)
    else t.radius (k + 1) ∈ Icc (p.gamma1 * t.radius k) (p.gamma2 * t.radius k)
  reuse : ∀ k < N, t.branch k = .trial → ¬p.eta1 ≤ ratio O t k →
    p.theta ≤ t.radius (k + 1) →
      t.order (k + 1) = t.order k ∧
      t.witness (k + 1) (t.order (k + 1)) = t.witness k (t.order k)

variable {f : E → ℝ} {q N : ℕ} {p : Parameters} {a : AccuracyParameters}
  {epsilon : ℕ → ℝ} {O : Oracle f q} {t : Trace E}

/-- Every allowed update retains the smallest contraction factor. -/
theorem LegalPrefix.radius_update_lower (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k < N) (hr : 0 ≤ t.radius k) :
    p.gamma1 * t.radius k ≤ t.radius (k + 1) := by
  by_cases ht : t.branch k = .trial
  · have hu := h.trial_radius k hk ht
    split_ifs at hu
    · exact (mul_le_of_le_one_left hr (p.gamma_le.trans p.gamma2_lt_one.le)).trans hu.1
    · exact (mul_le_mul_of_nonneg_right p.gamma_le hr).trans hu.1
    · exact hu.1
  · rw [h.accuracy_radius k hk ht]
    exact mul_le_of_le_one_left hr (p.gamma_le.trans p.gamma2_lt_one.le)

/-- Radius positivity is preserved also at accuracy-only iterations. -/
theorem LegalPrefix.radius_pos (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k ≤ N) : 0 < t.radius k := by
  induction k with
  | zero => exact h.initial_pos
  | succ k ih =>
    have hp := ih (by omega)
    exact (mul_pos p.gamma1_pos hp).trans_le (h.radius_update_lower (by omega) hp.le)

/-- Every computed gap uses a positive radius at most one. -/
theorem LegalPrefix.testRadius_bounds (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k ≤ N) : 0 < testRadius p t k ∧ testRadius p t k ≤ 1 :=
  ⟨lt_min (h.radius_pos hk) p.theta_pos, (min_le_right _ _).trans p.theta_le_one⟩

/-- Positive requests stay positive under both caching and geometric refinement. -/
theorem LegalPrefix.requests_pos (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k ≤ N) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) : 0 < t.request k i := by
  induction k with
  | zero => exact h.request_pos i hi
  | succ k ih =>
    rw [h.request_update k (by omega)]
    split_ifs
    · exact ih (by omega)
    · exact mul_pos a.contraction_pos (ih (by omega))

/-- Rejected trials reuse precisely the same oracle inputs and therefore the same tensors. -/
theorem LegalPrefix.coefficients_cached (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k < N) (ht : t.branch k = .trial) (ha : ¬p.eta1 ≤ ratio O t k) :
    coefficients O t (k + 1) = coefficients O t k := by
  have hx : t.point (k + 1) = t.point k := by simp [h.iterate k hk, Successful, ha]
  have hh : t.request (k + 1) = t.request k := by
    funext i
    simp [h.request_update k hk i, ht]
  simp [coefficients, hx, hh]

/-- A selected computed failure gives the half-threshold scaled-gap lower bound. -/
theorem LegalPrefix.scaledGap_lower (h : LegalPrefix p a epsilon O t N)
    {emin : ℝ} (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    {k : ℕ} (hk : k < N) (ht : t.branch k ≠ .testRefinement) :
    p.fraction * emin / 2 < scaledGap p O t k := by
  have hd := h.failure k hk ht
  have hr := pow_pos (h.testRadius_bounds (k := k) (by omega)).1 (t.order k)
  have hj : (0 : ℝ) < ((t.order k)! : ℝ) := by positivity
  have he' := mul_le_mul_of_nonneg_left (he _ (h.order_pos k hk ht) (h.order_le k hk ht))
    p.fraction_pos.le
  unfold scaledGap
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right he' (by norm_num : (0 : ℝ) ≤ 2))
  apply (lt_div_iff₀ hr).mpr
  have hh := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hj)).mp hd
  nlinarith

/-- The computed step retains the entire selected witness decrement. -/
theorem LegalPrefix.predicted_ge_scaledGap (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k < N) (ht : t.branch k ≠ .testRefinement) :
    scaledGap p O t k * testRadius p t k ^ t.order k / ((t.order k)! : ℝ) ≤
      InexactTrustRegion.prediction O t k (t.order k) (t.step k) := by
  have hr := (pow_pos (h.testRadius_bounds (k := k) (by omega)).1 (t.order k)).ne'
  have hj : ((t.order k)! : ℝ) ≠ 0 := by positivity
  simpa only [scaledGap, div_mul_cancel₀ _ hr, mul_div_cancel_left₀ _ hj] using
    h.prediction k hk ht

/-- Every selected step has positive approximate decrement. -/
theorem LegalPrefix.predicted_pos (h : LegalPrefix p a epsilon O t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j)
    {k : ℕ} (hk : k < N) (ht : t.branch k ≠ .testRefinement) :
    0 < InexactTrustRegion.prediction O t k (t.order k) (t.step k) := by
  have hp : 0 < p.fraction * epsilon (t.order k) * testRadius p t k ^ t.order k /
      (2 * ((t.order k)! : ℝ)) := by
    exact div_pos (mul_pos (mul_pos p.fraction_pos (he _ (h.order_pos k hk ht)
      (h.order_le k hk ht))) (pow_pos (h.testRadius_bounds (by omega)).1 _)) (by positivity)
  exact (hp.trans (h.failure k hk ht)).trans_le (h.prediction k hk ht)

/-- Acceptance realizes a fraction of the actual approximate decrement in the true objective. -/
theorem LegalPrefix.accepted_decrease (h : LegalPrefix p a epsilon O t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j)
    {k : ℕ} (hk : k < N) (hs : Successful p O t k) :
    p.eta1 * InexactTrustRegion.prediction O t k (t.order k) (t.step k) ≤
      f (t.point k) - f (t.point (k + 1)) := by
  have ht : t.branch k ≠ .testRefinement := by simp [hs.1]
  have hh := (le_div_iff₀ (h.predicted_pos he hk ht)).mp hs.2
  simpa only [ratio, h.iterate k hk, ite_eq_left hs] using hh

/-- The objective is nonincreasing at trials and at both kinds of forced refinement. -/
theorem LegalPrefix.objective_mono (h : LegalPrefix p a epsilon O t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j)
    {k : ℕ} (hk : k < N) : f (t.point (k + 1)) ≤ f (t.point k) := by
  by_cases hs : Successful p O t k
  · have hd := h.accepted_decrease he hk hs
    have hp := h.predicted_pos he hk (by simp [hs.1])
    have hm := mul_nonneg p.eta1_pos.le hp.le
    linarith
  · simp [h.iterate k hk, hs]

/-- Accuracy-only transitions leave the point, radius, and cached exact objective unchanged. -/
theorem LegalPrefix.accuracy_fixed (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k < N) (ht : t.branch k ≠ .trial) :
    t.point (k + 1) = t.point k ∧ t.radius (k + 1) = t.radius k := by
  exact ⟨by simp [h.iterate k hk, Successful, ht], h.accuracy_radius k hk ht⟩

/-- Executed trial indices, excluding both accuracy-only branches. -/
def trials (t : Trace E) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k => t.branch k = .trial

/-- Successful executed trial indices. -/
def successes (p : Parameters) (O : Oracle f q) (t : Trace E) (N : ℕ) : Finset ℕ :=
  (trials t N).filter fun k => p.eta1 ≤ ratio O t k

/-- Unsuccessful executed trial indices. -/
def failures (p : Parameters) (O : Oracle f q) (t : Trace E) (N : ℕ) : Finset ℕ :=
  (trials t N).filter fun k => ¬p.eta1 ≤ ratio O t k

/-- Executed accuracy-only indices. -/
def refinements (t : Trace E) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k => t.branch k ≠ .trial

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Every executed iteration is exactly one trial or one refinement. -/
theorem trials_add_refinements (t : Trace E) (N : ℕ) :
    (trials t N).card + (refinements t N).card = N := by
  simpa [trials, refinements] using
    Finset.card_filter_add_card_filter_not (s := Finset.range N) (fun k => t.branch k = .trial)

/-- Trial acceptance partitions executed trials into successes and failures. -/
theorem successes_add_failures (p : Parameters) (O : Oracle f q) (t : Trace E) (N : ℕ) :
    (successes p O t N).card + (failures p O t N).card = (trials t N).card := by
  exact Finset.card_filter_add_card_filter_not (fun k => p.eta1 ≤ ratio O t k)

/-- The actual objective-query log, with the initial value and one query per executed trial. -/
def functionQueries (t : Trace E) (N : ℕ) : List E :=
  t.point 0 :: ((trials t N).sort (· ≤ ·)).map (fun k => t.point k + t.step k)

/-- A chosen eager derivative-batch schedule, recording both point and requested accuracies.
One full batch is prepared initially and after each success or refinement, including the endpoint.
It bounds the source algorithm's incremental visited-order derivative work by full batches; it
does not claim an exact log of individual positive-order derivative evaluations. Rejected trials
retain cached tensors and add no batch. -/
def derivativeQueries (p : Parameters) (O : Oracle f q) (t : Trace E) (N : ℕ) :
    List (E × (ℕ → ℝ)) :=
  (t.point 0, t.request 0) ::
    ((((Finset.range N).filter fun k => Successful p O t k ∨ t.branch k ≠ .trial).sort
      (· ≤ ·)).map fun k => (t.point (k + 1), t.request (k + 1)))

omit [NormedSpace ℝ E] in
/-- Objective evaluations are exactly the trial count plus initialization. -/
@[simp] theorem functionQueries_length (t : Trace E) (N : ℕ) :
    (functionQueries t N).length = (trials t N).card + 1 := by
  simp [functionQueries]

/-- Eager batch costs count accepted steps and accuracy refinements separately. This is a full
batch upper envelope for the source's incremental per-order evaluations. -/
@[simp] theorem derivativeQueries_length (p : Parameters) (O : Oracle f q)
    (t : Trace E) (N : ℕ) :
    (derivativeQueries p O t N).length =
      (successes p O t N).card + (refinements t N).card + 1 := by
  have heq : (Finset.range N).filter (fun k => Successful p O t k ∨ t.branch k ≠ .trial) =
      successes p O t N ∪ refinements t N := by
    ext k
    rw [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hk, hs | hr⟩
      · exact Or.inl (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hk, hs.1⟩, hs.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hk, hr⟩)
    · rintro (hs | hr)
      · have hs' := Finset.mem_filter.mp hs
        have ht := Finset.mem_filter.mp hs'.1
        exact ⟨ht.1, Or.inl ⟨ht.2, hs'.2⟩⟩
      · have hr' := Finset.mem_filter.mp hr
        exact ⟨hr'.1, Or.inr hr'.2⟩
  have hd : Disjoint (successes p O t N) (refinements t N) := by
    apply Finset.disjoint_left.mpr
    intro k hk hr
    exact (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp
      (Finset.mem_filter.mp hk).1).2
  simp only [derivativeQueries, List.length_cons, List.length_map, Finset.length_sort,
    heq, Finset.card_union_of_disjoint hd]

/-- Logarithmic radius changes are charged only to trials; refinements contribute zero. -/
theorem LegalPrefix.log_radius_budget (h : LegalPrefix p a epsilon O t N) :
    Real.log (t.radius N / t.radius 0) ≤
      (successes p O t N).card * Real.log p.gamma3 +
        (failures p O t N).card * Real.log p.gamma2 := by
  have hg2 : 0 < p.gamma2 := p.gamma1_pos.trans_le p.gamma_le
  have hg3 : 0 < p.gamma3 := zero_lt_one.trans_le p.one_le_gamma3
  have hstep : ∀ k < N, Real.log (t.radius (k + 1)) - Real.log (t.radius k) ≤
      if t.branch k = .trial then
        if p.eta1 ≤ ratio O t k then Real.log p.gamma3 else Real.log p.gamma2
      else 0 := by
    intro k hk
    have hr := h.radius_pos (k := k) (by omega)
    by_cases ht : t.branch k = .trial
    · rw [ite_eq_left ht]
      have hu := h.trial_radius k hk ht
      by_cases hs : p.eta1 ≤ ratio O t k
      · rw [ite_eq_left hs]
        have hh : t.radius (k + 1) ≤ p.gamma3 * t.radius k := by
          split_ifs at hu
          · exact hu.2.trans (min_le_right _ _)
          · exact hu.2.trans (le_mul_of_one_le_left hr.le p.one_le_gamma3)
        have hl := Real.log_le_log (h.radius_pos (by omega)) hh
        rw [Real.log_mul hg3.ne' hr.ne'] at hl
        linarith
      · rw [ite_eq_right hs]
        rw [ite_eq_right (not_le.mpr ((lt_of_not_ge hs).trans_le p.eta_le)),
          ite_eq_right hs] at hu
        have hl := Real.log_le_log (h.radius_pos (by omega)) hu.2
        rw [Real.log_mul hg2.ne' hr.ne'] at hl
        linarith
    · simp [ht, h.accuracy_radius k hk ht]
  have hh := Finset.sum_le_sum (s := Finset.range N) (fun k hk => hstep k
    (Finset.mem_range.mp hk))
  rw [show (∑ k ∈ Finset.range N,
    (Real.log (t.radius (k + 1)) - Real.log (t.radius k))) =
      Real.log (t.radius N) - Real.log (t.radius 0) from
        Finset.sum_range_sub (fun k => Real.log (t.radius k)) N] at hh
  rw [Real.log_div (h.radius_pos le_rfl).ne' h.initial_pos.ne']
  convert hh using 1
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, successes, failures, trials, Finset.filter_filter]

/-- A positive terminal radius lower bound bounds trials by successes and a logarithmic term.
Accuracy-only iterations are absent from both sides of the multiplicative radius budget. -/
theorem LegalPrefix.trial_count_le (h : LegalPrefix p a epsilon O t N)
    {rmin : ℝ} (hm : 0 < rmin) (hmin : rmin ≤ t.radius N) :
    ((trials t N).card : ℝ) ≤ (successes p O t N).card *
      (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
        |Real.log (rmin / t.radius 0)| / |Real.log p.gamma2| := by
  have hg2 : 0 < p.gamma2 := p.gamma1_pos.trans_le p.gamma_le
  have hb : 0 < -Real.log p.gamma2 := neg_pos.mpr (Real.log_neg hg2 p.gamma2_lt_one)
  have habs : |Real.log p.gamma2| = -Real.log p.gamma2 :=
    abs_of_neg (Real.log_neg hg2 p.gamma2_lt_one)
  have hh := h.log_radius_budget
  have hl := Real.log_le_log (div_pos hm h.initial_pos)
    (div_le_div_of_nonneg_right hmin h.initial_pos.le)
  have hc : ((successes p O t N).card : ℝ) + (failures p O t N).card =
      (trials t N).card := by exact_mod_cast successes_add_failures p O t N
  rw [habs]
  apply (mul_le_mul_iff_left₀ hb).mp
  rw [show ((successes p O t N).card *
      (1 + Real.log p.gamma3 / -Real.log p.gamma2) +
      |Real.log (rmin / t.radius 0)| / -Real.log p.gamma2) * -Real.log p.gamma2 =
      (successes p O t N).card * (-Real.log p.gamma2 + Real.log p.gamma3) +
        |Real.log (rmin / t.radius 0)| by
          field_simp [show Real.log p.gamma2 ≠ 0 by linarith]
          ring]
  have ha := neg_le_abs (Real.log (rmin / t.radius 0))
  nlinarith

end Optimization.InexactTrustRegion
