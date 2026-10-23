import Numlib.Optimization.Regularization.Inexact.Explicit.Budget
import Numlib.Optimization.Regularization.Inexact.Explicit.Accuracy
import Numlib.Optimization.Regularization.Inexact.RunCounting

/-!
# Actual EDA evaluation and iteration counts before literal stopping

Successful objective budgets, actual parameter updates and the geometric
accuracy envelope bound every iteration and both evaluation schedules.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion EvaluationComplexity
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
        trialCountFactor P.toSettings + trialCountOffset P.toSettings S := by
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
    (hnot : ∀ k < N, ¬StopsAt P ε D k) :
    ((successfulIterations D.trialsᶜ N).card : ℝ) ≤
      accuracyCountSlope P.toSettings * |Real.log (minimumAccuracy P.order_pos ε)| +
        accuracyCountOffset P.toSettings M S := by
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
    (hmargin : P.theta < P.zeta / 2)
    {L M S flow : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬StopsAt P ε D k) :
    ((successfulIterations D.trials N).card : ℝ) ≤
      trialCountFactor P.toSettings * ((f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L M S * accuracyFactor P.toSettings ε) + 1) +
      trialCountOffset P.toSettings S := by
  have ht := h.trial_card_le_successful (hparam N le_rfl)
  have hs := h.successful_card_le hf hmargin hL hM hlip hparam
    (fun k hk i hi hip => hjet k hk i (by omega) hip) hlow hnot
  have hfac : 0 ≤ trialCountFactor P.toSettings := zero_le_one.trans
    (one_le_trialCountFactor P.toSettings)
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_right hs hfac])

/-- The whole actual iteration count has a finite power-plus-logarithm budget.
The endpoint may be the first point attaining true approximate optimality. -/
theorem iterations_le (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    (hmargin : P.theta < P.zeta / 2)
    {L M S flow : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬StopsAt P ε D k) :
    (N : ℝ) ≤ trialCountFactor P.toSettings * ((f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L M S * accuracyFactor P.toSettings ε) + 1) +
      trialCountOffset P.toSettings S +
      accuracyCountSlope P.toSettings * |Real.log (minimumAccuracy P.order_pos ε)| +
      accuracyCountOffset P.toSettings M S := by
  have ht := h.trial_card_le hf hmargin hL hM hlip hparam hjet hlow hnot
  have ha := h.accuracy_card_le hM hparam hjet hnot
  have hpart : (N : ℝ) = (successfulIterations D.trials N).card +
      (successfulIterations D.trialsᶜ N).card := by
    exact_mod_cast (card_successful_add_card_unsuccessful D.trials N).symm
  rw [hpart]
  linarith

/-- Each actual trial evaluates both approximate function values; no separate
initial objective evaluation is needed. -/
theorem functionEvaluations_le (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    (hmargin : P.theta < P.zeta / 2)
    {L M S flow : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬StopsAt P ε D k) :
    ((2 * (successfulIterations D.trials N).card) : ℝ) ≤
      2 * (trialCountFactor P.toSettings * ((f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L M S * accuracyFactor P.toSettings ε) + 1) +
      trialCountOffset P.toSettings S) := by
  have ht := h.trial_card_le hf hmargin hL hM hlip hparam hjet hlow hnot
  linarith

/-- Every derivative order is initialized and refreshed after actual successes
or accuracy reductions, including the endpoint first attaining the target. -/
theorem derivativeEvaluations_le (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    (hmargin : P.theta < P.zeta / 2)
    {L M S flow : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬StopsAt P ε D k) :
    (derivativeEvaluations D.trials D.ratio P.eta1 N : ℝ) ≤
      (f (D.point 0) - flow) / (commonDecreaseCoefficient P L M S * accuracyFactor
        P.toSettings ε) +
      accuracyCountSlope P.toSettings * |Real.log (minimumAccuracy P.order_pos ε)| +
      accuracyCountOffset P.toSettings M S + 2 := by
  have hs := h.successful_card_le hf hmargin hL hM hlip hparam
    (fun k hk i hi hip => hjet k hk i (by omega) hip) hlow hnot
  have ha := h.accuracy_card_le hM hparam hjet hnot
  simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  linarith

end Run
end InexactRegularization.Explicit
