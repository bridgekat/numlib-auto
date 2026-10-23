import Numlib.Optimization.Regularization.Inexact.RunBudget

/-!
# Actual trial and accuracy-update counts for inexact regularization

The primitive parameter updates and a genuine uniform cap bound objective
trials by successful trials. Actual accuracy-only branches have a separate
logarithmic bound from the positive request envelope. Together these give
finite iteration and initialized evaluation budgets before true optimality.
-/

namespace InexactRegularization
open InexactTrustRegion EvaluationComplexity

/-- The parameter-update multiplier relating all trials to accepted trials. -/
noncomputable def trialCountFactor {p q : ℕ} (P : Settings p q) : ℝ :=
  1 + |Real.log P.gamma1| / Real.log P.gamma2

/-- The fixed logarithmic trial-count offset from a genuine parameter cap. -/
noncomputable def trialCountOffset {p q : ℕ} (P : Settings p q) (S : ℝ) : ℝ :=
  Real.log (S / P.sigmaInitial) / Real.log P.gamma2

/-- The positive logarithmic denominator makes the trial multiplier at least one. -/
theorem one_le_trialCountFactor {p q : ℕ} (P : Settings p q) : 1 ≤ trialCountFactor P := by
  unfold trialCountFactor
  exact le_add_of_nonneg_right (div_nonneg (abs_nonneg _) (Real.log_pos P.one_lt_gamma2).le)

/-- The slope of the accuracy-only count with respect to `|log epsilon_min|`. -/
noncomputable def accuracyCountSlope {p q : ℕ} (P : Settings p q) : ℝ :=
  (p * (q + 1) : ℕ) / |Real.log P.reduction|

/-- The accuracy-only count's fixed intercept uses a strictly positive oracle
coefficient even for exact oracles and a positive initial request envelope. -/
noncomputable def accuracyCountOffset {p q : ℕ} (P : Settings p q) (M S : ℝ) : ℝ :=
  1 + |Real.log (regularizedAccuracyCoefficient P
    (stepRadiusCoefficient P.zeta P.theta M S) M (max 1 P.errorBound) / envelopeInitial P)| /
      |Real.log P.reduction|

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- The actual three-way parameter updates give the trial-count bound from
accepted trials and a genuine parameter cap, including accuracy-only gaps. -/
theorem trial_card_le_successful (h : Run f P ε D N) {S : ℝ}
    (hS : D.parameter N ≤ S) :
    ((successfulIterations D.trials N).card : ℝ) ≤
      (successfulIterations (successfulSet D.trials D.ratio P.eta1) N).card *
        trialCountFactor P + trialCountOffset P S := by
  have hh := iteration_bound_of_parameter_upper_on_trials
    (S := successfulSet D.trials D.ratio P.eta1) (T := D.trials) (σ := D.parameter)
    (fun _ hi => hi.1) (fun i hi => h.updates.pos hi)
    P.gamma1_pos P.gamma1_lt_one P.one_lt_gamma2 hS
    (fun i hi hsuccess => h.updates.successful_ge hi hsuccess.1 hsuccess.2)
    (fun i hi ht hnot => h.updates.unsuccessful_ge hi ht (fun ha => hnot ⟨ht, ha⟩))
    (fun i hi ht => h.updates.inactive_eq hi ht)
  simpa only [trialCountFactor, trialCountOffset, h.initial_parameter] using hh

/-- A genuine uniform parameter and tensor cap give the accuracy-only bound
without any positivity assumption on the original oracle error bound. -/
theorem accuracy_card_le (h : Run f P ε D N) {M S : ℝ} (hM : 1 ≤ M)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hnot : ∀ k < N, ¬TargetAt f ε D k) :
    ((successfulIterations D.trialsᶜ N).card : ℝ) ≤
      accuracyCountSlope P * |Real.log (minimumAccuracy P.order_pos ε)| +
        accuracyCountOffset P M S := by
  have hκ := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one.le hM
  have hfloor := (h.radius_floor_sharp hM hparam
    (fun k hk i hi hip => hjet k hk i (by omega) hip)).2.1
  exact h.accuracy_reductions_le_log hκ.1 hκ.2 hM
    (zero_lt_one.trans_le (le_max_left _ _)) (le_max_right _ _)
    (fun k hk => hfloor k hk.le) (fun k hk => hjet k hk.le) hnot

/-- All actual objective trials before the target obey the successful budget
and the fixed parameter-update logarithm. -/
theorem trial_card_le (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L M S flow : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬TargetAt f ε D k) :
    ((successfulIterations D.trials N).card : ℝ) ≤
      trialCountFactor P * ((f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L M S * accuracyFactor P ε) + 1) +
      trialCountOffset P S := by
  have ht := h.trial_card_le_successful (hparam N le_rfl)
  have hs := h.successful_card_le hf hL hM hlip hparam
    (fun k hk i hi hip => hjet k hk i (by omega) hip) hlow hnot
  have hfac : 0 ≤ trialCountFactor P := zero_le_one.trans (one_le_trialCountFactor P)
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_right hs hfac])

/-- The whole actual iteration count has a finite power-plus-logarithm budget.
The endpoint may be the first point attaining true approximate optimality. -/
theorem iterations_le (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L M S flow : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬TargetAt f ε D k) :
    (N : ℝ) ≤ trialCountFactor P * ((f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L M S * accuracyFactor P ε) + 1) +
      trialCountOffset P S +
      accuracyCountSlope P * |Real.log (minimumAccuracy P.order_pos ε)| +
      accuracyCountOffset P M S := by
  have ht := h.trial_card_le hf hL hM hlip hparam hjet hlow hnot
  have ha := h.accuracy_card_le hM hparam hjet hnot
  have hpart : (N : ℝ) = (successfulIterations D.trials N).card +
      (successfulIterations D.trialsᶜ N).card := by
    exact_mod_cast (card_successful_add_card_unsuccessful D.trials N).symm
  rw [hpart]
  linarith

/-- Objective evaluations include initialization and every actual objective trial. -/
theorem functionEvaluations_le (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L M S flow : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬TargetAt f ε D k) :
    (functionEvaluations D.trials N : ℝ) ≤
      trialCountFactor P * ((f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L M S * accuracyFactor P ε) + 1) +
      trialCountOffset P S + 1 := by
  have ht := h.trial_card_le hf hL hM hlip hparam hjet hlow hnot
  simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
  linarith

/-- Every derivative order is initialized and refreshed after actual successes
or accuracy reductions, including the endpoint first attaining the target. -/
theorem derivativeEvaluations_le (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L M S flow : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬TargetAt f ε D k) :
    (derivativeEvaluations D.trials D.ratio P.eta1 N : ℝ) ≤
      (f (D.point 0) - flow) / (commonDecreaseCoefficient P L M S * accuracyFactor P ε) +
      accuracyCountSlope P * |Real.log (minimumAccuracy P.order_pos ε)| +
      accuracyCountOffset P M S + 2 := by
  have hs := h.successful_card_le hf hL hM hlip hparam
    (fun k hk i hi hip => hjet k hk i (by omega) hip) hlow hnot
  have ha := h.accuracy_card_le hM hparam hjet hnot
  simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  linarith

end Run
end InexactRegularization
