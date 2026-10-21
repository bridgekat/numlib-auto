import Numlib.Optimization.InexactTrustRegionBounds
import Numlib.Optimization.MeasureDomination

/-!
# Finite accuracy-refinement budgets

Requests contract only on actual accuracy-only transitions. Their exact powers count these
transitions separately from objective trials and cached derivative batches. A small-request
condition is derived from actual Taylor errors and coefficient bounds before it is used to
bound any execution prefix.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactTrustRegion
open HigherOrderTrustRegion HigherOrderRegularization TaylorCriticality
attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {q N : ℕ} {p : Parameters} {a : AccuracyParameters}
  {epsilon : ℕ → ℝ} {O : Oracle f q} {t : Trace E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Adding one executed iteration increments the refinement count exactly on the two accuracy
branches. -/
theorem refinements_succ (t : Trace E) (k : ℕ) :
    (refinements t (k + 1)).card =
      (refinements t k).card + if t.branch k = .trial then 0 else 1 := by
  by_cases ht : t.branch k = .trial
  · simp [refinements, Finset.range_add_one, Finset.filter_insert, ht]
  · simp [refinements, Finset.range_add_one, Finset.filter_insert, ht]

/-- Each actual request is its initial value times the exact number of geometric refinements. -/
theorem LegalPrefix.request_eq_pow (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k ≤ N) (i : ℕ) :
    t.request k i = a.contraction ^ (refinements t k).card * t.request 0 i := by
  induction k with
  | zero => simp [refinements]
  | succ k ih =>
    rw [h.request_update k (by omega) i, refinements_succ]
    split_ifs with ht
    · simpa using ih (by omega)
    · rw [ih (by omega), pow_succ]
      ring

/-- Initial request bounds propagate with the same exact geometric refinement exponent. -/
theorem LegalPrefix.request_le_pow (h : LegalPrefix p a epsilon O t N)
    {H0 : ℝ} (hh : ∀ i ∈ Finset.Icc 1 q, t.request 0 i ≤ H0)
    {k : ℕ} (hk : k ≤ N) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) :
    t.request k i ≤ a.contraction ^ (refinements t k).card * H0 := by
  rw [h.request_eq_pow hk i]
  exact mul_le_mul_of_nonneg_left (hh i hi) (pow_nonneg a.contraction_pos.le _)

/-- The common requested-accuracy threshold obtained from a radius floor and bounded returned
coefficients. The multiplier `K+1` avoids division by a potentially zero oracle constant. -/
def requestThreshold (a : AccuracyParameters) (q : ℕ) (emin b α M K : ℝ) : ℝ :=
  min (a.stepConstant * (min 1 ((α * b ^ q / (q ! : ℝ)) / (2 * M))) ^ q)
    (emin * b ^ q / (4 * (q ! : ℝ) * (K + 1)))

/-- Every threshold is positive for positive scalar analytic bounds. -/
theorem requestThreshold_pos {emin b α M K : ℝ} (he : 0 < emin) (hb : 0 < b)
    (hα : 0 < α) (hM : 0 < M) (hK : 0 ≤ K) :
    0 < requestThreshold a q emin b α M K := by
  have hs := a.stepConstant_pos
  unfold requestThreshold
  positivity

/-- Before true quality, sufficiently accurate requests force an actual objective trial.
Both exits to refinement are excluded using the literal tests and actual tensor bounds. -/
theorem LegalPrefix.trial_of_small_requests [ProperSpace E]
    (h : LegalPrefix p a epsilon O t N) {emin b α M K : ℝ}
    (he : 0 < emin) (hb : 0 < b) (hb1 : b ≤ 1) (hα : 0 < α)
    (hM : 0 < M) (hK : 0 ≤ K) (hO : UniformAccuracy O K)
    (heps : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    {k : ℕ} (hk : k < N) (hr : b ≤ InexactTrustRegion.testRadius p t k)
    (hg : t.branch k ≠ .testRefinement → α ≤ InexactTrustRegion.scaledGap p O t k)
    (hA : ∀ i ∈ Finset.Icc 1 q, ‖coefficients O t k i‖ ≤ M)
    (hnq : ¬Quality (q := q) p epsilon f t k)
    (hh : ∀ i ∈ Finset.Icc 1 q,
      t.request k i ≤ requestThreshold a q emin b α M K) : t.branch k = .trial := by
  have hT := requestThreshold_pos (a := a) (q := q) he hb hα hM hK
  have hnt : t.branch k ≠ .testRefinement := by
    intro ht
    apply hnq
    apply h.quality_at_pass hK hT.le hO (by omega) hh ((h.test_branch k hk).mp ht)
    intro j hj hjq
    have hl := tolerance_monomial_lower he.le hb.le hb1 hr hjq (heps j hj hjq)
    have hc : 4 * K * requestThreshold a q emin b α M K ≤ emin * b ^ q / (q ! : ℝ) := by
      have ht := min_le_right
        (a.stepConstant * (min 1 ((α * b ^ q / (q ! : ℝ)) / (2 * M))) ^ q)
        (emin * b ^ q / (4 * (q ! : ℝ) * (K + 1)))
      change requestThreshold a q emin b α M K ≤ _ at ht
      have hden : 0 < 4 * (q ! : ℝ) * (K + 1) := by positivity
      have hx := (le_div_iff₀ hden).mp ht
      have hf : (0 : ℝ) < (q ! : ℝ) := by positivity
      apply (le_div_iff₀ hf).mpr
      nlinarith [mul_nonneg hT.le hf.le]
    exact hc.trans hl
  have hdec := h.predicted_lower_two hb.le hb1 hα.le hk hnt hr (hg hnt)
  have hs := h.step_norm_lower_min hM hk hnt hA hdec
  apply h.step_accurate_of_requests
    (lt_min (by norm_num : (0 : ℝ) < 1) (by positivity)).le (min_le_left _ _) hk hnt hs
  intro i hi
  exact (hh i hi).trans (min_le_left _ _)

/-- If a genuine request threshold forces trials, its geometric countdown bounds all
accuracy-only transitions. This is a counting lemma, not an algorithmic progress premise. -/
theorem LegalPrefix.refinement_count_le (h : LegalPrefix p a epsilon O t N)
    {H0 H : ℝ} (hh0 : ∀ i ∈ Finset.Icc 1 q, t.request 0 i ≤ H0)
    {R : ℕ} (hR : a.contraction ^ R * H0 ≤ H)
    (hforce : ∀ k < N, (∀ i ∈ Finset.Icc 1 q, t.request k i ≤ H) → t.branch k = .trial) :
    (refinements t N).card ≤ R := by
  have hall : ∀ k ≤ N, (refinements t k).card ≤ R := by
    intro k hk
    induction k with
    | zero => simp [refinements]
    | succ k ih =>
      have hi := ih (by omega)
      rw [refinements_succ]
      by_cases ht : t.branch k = .trial
      · simpa [ht] using hi
      · simp only [ht, ite_false]
        have hlt : (refinements t k).card < R := by
          by_contra! hn
          have heq : (refinements t k).card = R := by omega
          apply ht
          apply hforce k (by omega)
          intro i hi
          exact (h.request_le_pow hh0 (by omega) hi).trans (by simpa [heq] using hR)
        omega
  exact hall N le_rfl

/-- A logarithmic countdown for a positive accuracy threshold. -/
def refinementBudget (a : AccuracyParameters) (H0 H : ℝ) : ℕ :=
  MeasureDomination.geometricIterationCount H0 a.contraction⁻¹ H

/-- The accuracy countdown really attains the requested threshold. -/
theorem refinementBudget_spec {H0 H : ℝ} (hH : 0 < H) :
    a.contraction ^ refinementBudget a H0 H * H0 ≤ H := by
  have hb : 1 < a.contraction⁻¹ := (one_lt_inv₀ a.contraction_pos).mpr a.contraction_lt_one
  apply MeasureDomination.geometric_tolerance hb hH
    (u := fun k => a.contraction ^ k * H0)
    (fun k => by simp [div_eq_mul_inv, inv_pow, mul_comm]) le_rfl

/-- The uniform radius floor used in the finite accuracy and evaluation budgets. -/
def radiusFloor (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K emin : ℝ) : ℝ :=
  InexactTrustRegion.radiusCoefficient p initial (errorCoefficient q L K a.stepConstant) *
    p.fraction * emin / 2

/-- The uniform positive approximate decrement paid for by every accepted trial. -/
def decreaseFloor (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K emin : ℝ) : ℝ := radiusFloor p a q initial L K emin ^ (q + 1) / (q ! : ℝ)

/-- A single positive request threshold that excludes both refinement branches before quality. -/
def analysisThreshold (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K M emin : ℝ) : ℝ :=
  requestThreshold a q emin (radiusFloor p a q initial L K emin) (p.fraction * emin / 2) M K

/-- Accepted-trial budget from the true objective's lower bound. -/
def successBudget (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K emin gap : ℝ) : ℝ :=
  gap / (p.eta1 * decreaseFloor p a q initial L K emin)

/-- The multiplicative overhead of unsuccessful actual trials. -/
def trialFactor (p : Parameters) : ℝ := 1 + Real.log p.gamma3 / |Real.log p.gamma2|

/-- Trial budget; the logarithmic term is the actual radius-update budget. -/
def trialBudget (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K emin gap : ℝ) : ℝ :=
  successBudget p a q initial L K emin gap * trialFactor p +
    |Real.log (radiusFloor p a q initial L K emin / initial)| / |Real.log p.gamma2|

/-- A finite-prefix bound before true quality, with trials and accuracy refinements separated. -/
theorem LegalPrefix.budgets_before_quality [ProperSpace E]
    (h : LegalPrefix p a epsilon O t N)
    {emin K L M H0 low : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1)
    (hetheta : emin ≤ p.theta) (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    (hK : 0 ≤ K) (hL : 0 < L) (hM : 0 < M) (hO : UniformAccuracy O K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    (hA : ∀ k < N, ∀ i ∈ Finset.Icc 1 q, ‖coefficients O t k i‖ ≤ M)
    (hh0 : ∀ i ∈ Finset.Icc 1 q, t.request 0 i ≤ H0)
    (hlow : low ≤ f (t.point N)) (hnq : ∀ k < N, ¬Quality (q := q) p epsilon f t k) :
    ((successes p O t N).card : ℝ) ≤
      successBudget p a q (t.radius 0) L K emin (f (t.point 0) - low) ∧
    ((trials t N).card : ℝ) ≤
      InexactTrustRegion.trialBudget p a q (t.radius 0) L K emin (f (t.point 0) - low) ∧
    (refinements t N).card ≤ refinementBudget a H0
      (analysisThreshold p a q (t.radius 0) L K M emin) := by
  have hks := a.stepConstant_pos
  have hfrac := p.fraction_pos
  have hC : 0 < errorCoefficient q L K a.stepConstant := by
    dsimp [errorCoefficient]; positivity
  have hc := radiusCoefficient_pos (p := p) h.initial_pos hC
  let b := radiusFloor p a q (t.radius 0) L K emin
  have hb : 0 < b := by dsimp [b, radiusFloor]; positivity
  have hc1 := radiusCoefficient_le_one (p := p) (t.radius 0)
    (errorCoefficient q L K a.stepConstant)
  have hcf : InexactTrustRegion.radiusCoefficient p (t.radius 0)
      (errorCoefficient q L K a.stepConstant) * p.fraction ≤ 1 :=
    (mul_le_mul_of_nonneg_right hc1 hfrac.le).trans (by simpa using p.fraction_le_one)
  have hbe : b ≤ emin := by
    dsimp [b, radiusFloor]
    nlinarith [mul_le_mul_of_nonneg_right hcf hemin.le]
  have hbr : ∀ k ≤ N, b ≤ InexactTrustRegion.testRadius p t k := by
    intro k hk
    exact le_min (h.radius_lower hemin heone hetheta he hK hL hO hf hk) (hbe.trans hetheta)
  have hα : 0 < p.fraction * emin / 2 := by positivity
  have hT : 0 < analysisThreshold p a q (t.radius 0) L K M emin :=
    requestThreshold_pos hemin hb hα hM hK
  have hs := h.success_count_le hemin heone hetheta he hK hL hO hf hlow
  have ht := h.trial_count_le hb
    (h.radius_lower hemin heone hetheta he hK hL hO hf le_rfl)
  have hfactor : 0 ≤ trialFactor p := by
    unfold trialFactor
    exact add_nonneg (by norm_num) (div_nonneg (Real.log_nonneg p.one_le_gamma3) (abs_nonneg _))
  have htrials : ((trials t N).card : ℝ) ≤
      InexactTrustRegion.trialBudget p a q (t.radius 0) L K emin (f (t.point 0) - low) := by
    have hm := add_le_add (mul_le_mul_of_nonneg_right hs hfactor)
      (le_refl (|Real.log (b / t.radius 0)| / |Real.log p.gamma2|))
    exact ht.trans (by
      simpa only [InexactTrustRegion.trialBudget, successBudget, decreaseFloor,
        radiusFloor, trialFactor, b] using hm)
  refine ⟨hs, htrials, h.refinement_count_le hh0 (refinementBudget_spec hT) ?_⟩
  intro k hk hh
  exact h.trial_of_small_requests hemin hb (hbe.trans heone) hα hM hK hO he hk
    (hbr k (by omega)) (fun hn => (h.scaledGap_lower he hk hn).le)
    (hA k hk) (hnq k hk) hh

/-- A run consists solely of actual legal finite prefixes; it contains no decrease, quality,
termination, or complexity oracle. Accuracy-only continuations remain possible after quality. -/
def IsRun (p : Parameters) (a : AccuracyParameters) (epsilon : ℕ → ℝ)
    (O : Oracle f q) (t : Trace E) : Prop := ∀ N, LegalPrefix p a epsilon O t N

/-- The total prefix budget is the sum of trials and geometric accuracy refinements. -/
def prefixBudget (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K M H0 emin gap : ℝ) : ℝ :=
  InexactTrustRegion.trialBudget p a q initial L K emin gap +
    refinementBudget a H0 (analysisThreshold p a q initial L K M emin)

/-- Actual legal runs reach true all-orders quality within a finite bound. Objective calls are
actual query-log lengths. Derivative costs use the chosen eager full-batch upper envelope,
including refreshed endpoint jets, for incremental positive-order work. No observable stopping
certificate is asserted: the first true quality index is an analysis-only index. -/
theorem IsRun.exists_first_quality [ProperSpace E] (h : IsRun p a epsilon O t)
    {emin K L M H0 low : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1)
    (hetheta : emin ≤ p.theta) (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    (hK : 0 ≤ K) (hL : 0 < L) (hM : 0 < M) (hO : UniformAccuracy O K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    (hA : ∀ k, ∀ i ∈ Finset.Icc 1 q, ‖coefficients O t k i‖ ≤ M)
    (hh0 : ∀ i ∈ Finset.Icc 1 q, t.request 0 i ≤ H0)
    (hlow : ∀ x, low ≤ f x) :
    ∃ k ≤ ⌊prefixBudget p a q (t.radius 0) L K M H0 emin (f (t.point 0) - low)⌋₊,
      Quality (q := q) p epsilon f t k ∧ (∀ j < k, ¬Quality (q := q) p epsilon f t j) ∧
      (0 < InexactTrustRegion.testRadius p t k ∧ InexactTrustRegion.testRadius p t k ≤ 1) ∧
      ((functionQueries t k).length : ℝ) ≤
        InexactTrustRegion.trialBudget p a q (t.radius 0) L K emin (f (t.point 0) - low) + 1 ∧
      ((derivativeQueries p O t k).length : ℝ) ≤
        successBudget p a q (t.radius 0) L K emin (f (t.point 0) - low) +
          refinementBudget a H0 (analysisThreshold p a q (t.radius 0) L K M emin) + 1 := by
  have hb : ∀ N, (∀ j < N, ¬Quality (q := q) p epsilon f t j) →
      (N : ℝ) ≤ prefixBudget p a q (t.radius 0) L K M H0 emin (f (t.point 0) - low) := by
    intro N hn
    have H := (h N).budgets_before_quality hemin heone hetheta he hK hL hM hO hf
      (fun k _ => hA k) hh0 (hlow _) hn
    have hc : ((trials t N).card : ℝ) + (refinements t N).card = N := by
      exact_mod_cast trials_add_refinements t N
    have hr : ((refinements t N).card : ℝ) ≤
        refinementBudget a H0 (analysisThreshold p a q (t.radius 0) L K M emin) := by
      exact_mod_cast H.2.2
    dsimp [prefixBudget]
    linarith [H.2.1]
  obtain ⟨k, hk, hq, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hb
  have H := (h k).budgets_before_quality hemin heone hetheta he hK hL hM hO hf
    (fun k _ => hA k) hh0 (hlow _) hfirst
  refine ⟨k, hk, hq, hfirst, (h k).testRadius_bounds le_rfl, ?_, ?_⟩
  · rw [functionQueries_length, Nat.cast_add, Nat.cast_one]
    linarith [H.2.1]
  · rw [derivativeQueries_length]
    push_cast
    have hr : ((refinements t k).card : ℝ) ≤
        refinementBudget a H0 (analysisThreshold p a q (t.radius 0) L K M emin) := by
      exact_mod_cast H.2.2
    linarith [H.1]

end Optimization.InexactTrustRegion
