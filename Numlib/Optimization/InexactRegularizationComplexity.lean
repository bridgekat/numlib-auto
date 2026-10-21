import Numlib.Optimization.InexactRegularizationDecrease
import Numlib.Optimization.InexactRegularizationRefinementBounds
import Numlib.Optimization.InexactRegularizationCounts
import Numlib.Optimization.HigherOrderApproximateRegularizationComplexity

/-!
# First true point quality and actual implicit-accuracy evaluation budgets

The complete operational run supplies every finite prefix. Genuine accepted objective
payments, literal parameter intervals and geometric request refinements bound every prefix
before true point quality. The resulting finite prefix bound forces a first true-quality
point. Objective evaluations have no logarithmic accuracy cost; cached derivative batches
include that cost. Structural formulas retain the fixed initial request-ratio dependence.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels

/-- The fixed accepted-objective payment coefficient, before the simultaneous tolerance
measure. Its formula uses the corrected parameter and actual inner-radius constants. -/
def acceptedDecreaseCoefficient (P : Parameters) (h0 : ℕ → ℝ) (σ0 L K M : ℝ) : ℝ :=
  P.eta1 * HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos
    P.theta (correctedTransferConstant P h0 σ0 L K)
      (prescribedRadiusCoefficient P M (correctedSigmaBound P h0 σ0 L K)) P.sigmaMin

/-- Positive fixed initialization and normalized analytic constants give positive payment. -/
theorem acceptedDecreaseCoefficient_pos (P : Parameters) (h0 : ℕ → ℝ) {σ0 L K M : ℝ}
    (hσ0 : 0 ≤ σ0) (hL : 1 ≤ L) (hK : 0 ≤ K) (hM : 1 ≤ M) :
    0 < acceptedDecreaseCoefficient P h0 σ0 L K M :=
  mul_pos P.eta1_pos (corrected_decrease_coefficient_pos P h0 hσ0 hL hK
    (prescribedRadiusCoefficient_pos P hM))

/-- The fixed multiplier from actual successful trials to all trials. -/
def trialCountMultiplier (P : Parameters) : ℝ :=
  HigherOrderApproximateRegularization.trialMultiplier P.toParameters

/-- The trial-count multiplier is strictly positive. -/
theorem trialCountMultiplier_pos (P : Parameters) : 0 < trialCountMultiplier P := by
  have h := div_nonneg (abs_nonneg (Real.log P.gamma1))
    (Real.log_pos P.one_lt_gamma2).le
  change 0 < 1 + |Real.log P.gamma1| / Real.log P.gamma2
  linarith

/-- The fixed additive parameter-change budget from the corrected sigma bound. -/
def trialLogBudget (P : Parameters) (h0 : ℕ → ℝ) (σ0 L K : ℝ) : ℝ :=
  Real.log (correctedSigmaBound P h0 σ0 L K / σ0) / Real.log P.gamma2

/-- A positive initialized sigma makes the parameter-change budget nonnegative. -/
theorem trialLogBudget_nonneg (P : Parameters) (h0 : ℕ → ℝ) {σ0 : ℝ}
    (hσ0 : 0 < σ0) (L K : ℝ) : 0 ≤ trialLogBudget P h0 σ0 L K := by
  apply div_nonneg _ (Real.log_pos P.one_lt_gamma2).le
  apply Real.log_nonneg
  apply (le_div_iff₀ hσ0).mpr
  simpa only [one_mul] using initial_le_correctedSigmaBound P h0 σ0 L K

/-- The fixed initialization term in the accuracy-refinement budget, including its two
integer-boundary allowances. It contains no tolerance value. -/
def refinementCountConstant (P : Parameters) (h0 : ℕ → ℝ) (σ0 L K M : ℝ) : ℝ :=
  refinementLogConstant P h0
    (refinementAccuracyCoefficient P M (correctedSigmaBound P h0 σ0 L K) K) + 2

/-- The fixed additive refinement budget is strictly positive. -/
theorem refinementCountConstant_pos (P : Parameters) (h0 : ℕ → ℝ) (σ0 L K M : ℝ) :
    0 < refinementCountConstant P h0 σ0 L K M :=
  add_pos_of_nonneg_of_pos (refinementLogConstant_nonneg P h0 _) (by norm_num)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Parameters} {f : E → ℝ}

/-- Every accepted actual transition before successor point quality pays the fixed
simultaneous tolerance-power decrease. Its parameter bound, coefficient powers and returned
radii are all derived from the global analytic contracts and actual operational prefix. -/
theorem Run.accepted_decrease_before_pointQuality (O : InexactTrustRegion.Oracle f P.p)
    (r : Run P P.q f O.derivative) {L K M : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hM : 1 ≤ M)
    (hA : ∀ (x : E) (h : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.kappaInitial) →
      ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ M)
    (k : ℕ) (ha : r.accepted k = true)
    (hnot : ¬PointQuality P f (r.state (k + 1)).point) :
    acceptedDecreaseCoefficient P (r.state 0).request (r.state 0).sigma L K M *
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon ≤
        f (r.state k).point - f (r.state (k + 1)).point := by
  let rp := r.prefix (k + 1)
  have hk : k < k + 1 := Nat.lt_succ_self k
  have ht : rp.trial k = true := (r.transition_all k).accepted_is_trial ha
  let t := rp.executedTrial hk ht
  have hAr : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (rp.state k).point (rp.state k).request i‖ ≤ M := by
    apply hA
    intro i hi
    exact ⟨(rp.request_bounds hk.le hi).1,
      (rp.request_bounds hk.le hi).2.trans (rp.initial_request_le i hi)⟩
  have hrad : ‖t.inner.step‖ < 1 → PrescribedModelRadii P
      (prescribedRadiusCoefficient P M
        (correctedSigmaBound P (r.state 0).request (r.state 0).sigma L K)) t.inner.radii := by
    intro hs
    exact rp.prescribedModelRadii_of_bounds O P.order_pos hk.le t.inspection t.order_le
      t.inner hf hK hO hM hAr hs
  have hfail := not_criteria_of_not_pointQuality hnot
    (rp.valid_radii (k := k + 1) le_rfl)
  have hb := rp.accepted_decrease_of_true_gap_failure O P.order_pos hk ht ha
    hf hL hK hO (prescribedRadiusCoefficient_pos P hM)
    (prescribedRadiusCoefficient_le_one P hM) hrad hfail
  simpa only [acceptedDecreaseCoefficient, mul_assoc, rp, Run.prefix_state] using hb

/-- Before first point quality, actual accepted trials consume at most the objective gap
budget, with one possible last successful transition that attains point quality. -/
theorem Run.accepted_count_before_pointQuality (O : InexactTrustRegion.Oracle f P.p)
    (r : Run P P.q f O.derivative) {L K M low : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hM : 1 ≤ M)
    (hA : ∀ (x : E) (h : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.kappaInitial) →
      ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ M)
    (hlow : ∀ x, low ≤ f x) (N : ℕ)
    (hfirst : ∀ k < N, ¬PointQuality P f (r.state k).point) :
    ((r.prefix N).acceptedCount : ℝ) ≤ (f (r.state 0).point - low) /
      (acceptedDecreaseCoefficient P (r.state 0).request (r.state 0).sigma L K M *
        HigherOrderApproximateRegularization.toleranceMeasure
          P.p P.q P.order_pos P.epsilon) + 1 := by
  have hd := mul_pos (acceptedDecreaseCoefficient_pos P (r.state 0).request
    (P.sigmaMin_pos.le.trans r.initial_sigma) hL hK hM)
    (HigherOrderApproximateRegularization.toleranceMeasure_pos P.toParameters)
  exact r.accepted_count_before_test_le hd hlow
    (fun k ha hn => r.accepted_decrease_before_pointQuality O hf hL hK hO hM hA k ha hn)
    N hfirst

/-- Every quality-free prefix has the actual trial, refinement, function and derivative
budgets. Objective evaluations have no logarithmic accuracy term; derivative batches retain
that term and reject-cache reuse. All sigma, radius and decrease estimates are derived. -/
theorem Run.evaluation_bounds_before_pointQuality (O : InexactTrustRegion.Oracle f P.p)
    (r : Run P P.q f O.derivative) {L K M low ε : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hM : 1 ≤ M)
    (hA : ∀ (x : E) (h : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.kappaInitial) →
      ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ M)
    (hlow : ∀ x, low ≤ f x) (hε : 0 < ε)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (N : ℕ) (hfirst : ∀ k < N, ¬PointQuality P f (r.state k).point) :
    let d := acceptedDecreaseCoefficient P (r.state 0).request (r.state 0).sigma L K M
    let τ := HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon
    let gap := f (r.state 0).point - low
    let G := trialCountMultiplier P
    let C := trialLogBudget P (r.state 0).request (r.state 0).sigma L K
    let E := refinementLogSlope P
    let F := refinementCountConstant P (r.state 0).request (r.state 0).sigma L K M
    ((r.prefix N).trialCount : ℝ) ≤ G * (gap / (d * τ)) + G + C ∧
      ((r.prefix N).refinementCount N : ℝ) ≤ E * |Real.log ε| + F ∧
      ((r.prefix N).functionCount : ℝ) ≤ G * (gap / (d * τ)) + G + C + 1 ∧
      ((r.prefix N).derivativeBatches : ℝ) ≤ gap / (d * τ) + E * |Real.log ε| + F + 2 ∧
      (N : ℝ) ≤ G * (gap / (d * τ)) + G + C + E * |Real.log ε| + F := by
  dsimp only
  let rp := r.prefix N
  have ha := r.accepted_count_before_pointQuality O hf hL hK hO hM hA hlow N hfirst
  have ht := rp.trial_count_le (rp.sigma_le_correctedSigmaBound O P.order_pos hf hK hO le_rfl)
  have hG : 0 ≤ trialCountMultiplier P := (trialCountMultiplier_pos P).le
  have ht' : (rp.trialCount : ℝ) ≤ trialCountMultiplier P *
      ((f (r.state 0).point - low) /
        (acceptedDecreaseCoefficient P (r.state 0).request (r.state 0).sigma L K M *
          HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon)) +
        trialCountMultiplier P + trialLogBudget P (r.state 0).request (r.state 0).sigma L K := by
    have hm := mul_le_mul_of_nonneg_left ha hG
    change (rp.trialCount : ℝ) ≤ (rp.acceptedCount : ℝ) * trialCountMultiplier P +
      trialLogBudget P (r.state 0).request (r.state 0).sigma L K at ht
    linarith
  have hAr : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (rp.state k).point (rp.state k).request i‖ ≤ M := by
    intro k hk
    apply hA
    intro i hi
    exact ⟨(rp.request_bounds hk hi).1,
      (rp.request_bounds hk hi).2.trans (rp.initial_request_le i hi)⟩
  have hr : (rp.refinementCount N : ℝ) ≤ refinementLogSlope P * |Real.log ε| +
      refinementCountConstant P (r.state 0).request (r.state 0).sigma L K M := by
    simpa only [refinementCountConstant, correctedSigmaBound, rp, Run.prefix_state, add_assoc]
      using (rp.refinement_count_before_pointQuality O hf hK hO hM hAr hfirst hε hεj).2
  have hnf : (rp.functionCount : ℝ) = (rp.trialCount : ℝ) + 1 := by
    exact_mod_cast rp.functionCount_eq_trialCount_add_one
  have hnd : (rp.derivativeBatches : ℝ) ≤ (rp.acceptedCount : ℝ) +
      (rp.refinementCount N : ℝ) + 1 := by exact_mod_cast rp.derivativeBatches_le
  have hn : (rp.trialCount : ℝ) + (rp.refinementCount N : ℝ) = N := by
    exact_mod_cast rp.trialCount_add_refinementCount
  exact ⟨ht', hr, by linarith, by linarith, by linarith⟩

/-- Every complete actual literal checked-q run reaches a FIRST true point-quality iterate
with the explicit finite prefix budget and its actual objective and cached-derivative counts.
This is true quality attainment, not an observable IDA return or an assumed stopping index. -/
theorem Run.first_pointQuality_bounds (O : InexactTrustRegion.Oracle f P.p)
    (r : Run P P.q f O.derivative) {L K M low ε : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hM : 1 ≤ M)
    (hA : ∀ (x : E) (h : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.kappaInitial) →
      ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ M)
    (hlow : ∀ x, low ≤ f x) (hε : 0 < ε)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j) :
    let d := acceptedDecreaseCoefficient P (r.state 0).request (r.state 0).sigma L K M
    let τ := HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon
    let gap := f (r.state 0).point - low
    let G := trialCountMultiplier P
    let C := trialLogBudget P (r.state 0).request (r.state 0).sigma L K
    let E := refinementLogSlope P
    let F := refinementCountConstant P (r.state 0).request (r.state 0).sigma L K M
    ∃ n ≤ ⌊G * (gap / (d * τ)) + G + C + E * |Real.log ε| + F⌋₊,
      PointQuality P f (r.state n).point ∧
      (∀ k < n, ¬PointQuality P f (r.state k).point) ∧
      ((r.prefix n).functionCount : ℝ) ≤ G * (gap / (d * τ)) + G + C + 1 ∧
      ((r.prefix n).derivativeBatches : ℝ) ≤ gap / (d * τ) + E * |Real.log ε| + F + 2 := by
  dsimp only
  obtain ⟨n, hn, hquality, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (fun N hN => (r.evaluation_bounds_before_pointQuality O hf hL hK hO hM hA hlow
      hε hεj N hN).2.2.2.2)
  have hb := r.evaluation_bounds_before_pointQuality O hf hL hK hO hM hA hlow hε hεj n hfirst
  exact ⟨n, hn, hquality, hfirst, hb.2.2.1, hb.2.2.2.1⟩

end Optimization.InexactRegularization
