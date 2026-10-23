import Numlib.Optimization.Regularization.Inexact.Explicit.Caps
import Numlib.Optimization.Regularization.Inexact.ReferenceDecrease
import Numlib.Optimization.TrustRegion.Inexact.Decrease

/-!
# Literal EDA stopping from the current computed check

Every selected Step1 check supplies a quantitative reference model decrease.
The actual Step2 comparison, derived radius floors and acceptance ratio give
one fixed positive decrease per successful trial, even after true criticality
has already been attained. This yields literal stopping without an additional
margin between theta and zeta.

The resulting bound uses the coarser factor `epsilon_min^(q+1)`. It does not
assert the source's sharper p-dependent regularization rates without that margin.
All constants precede the requested accuracies and computed execution data.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The positive current-reference coefficient fixed before requested accuracies. -/
noncomputable def currentReferenceCoefficient {p q : ℕ} (P : Settings p q)
    (M S : ℝ) : ℝ :=
  P.zeta * (stepRadiusCoefficient P.zeta P.theta M S) ^ q / (4 * (q.factorial : ℝ))

/-- The accepted true-objective coefficient for the current computed check. -/
noncomputable def currentDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (M S : ℝ) : ℝ := P.eta1 / 2 * currentReferenceCoefficient P M S

/-- The current-reference coefficient is strictly positive without an effective-margin
condition. -/
theorem currentReferenceCoefficient_pos {p q : ℕ} (P : Settings p q)
    {M S : ℝ} (hM : 1 ≤ M) : 0 < currentReferenceCoefficient P M S := by
  have hk := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one.le hM
  unfold currentReferenceCoefficient
  exact div_pos (mul_pos P.zeta_pos (pow_pos hk.1 _)) (by positivity)

/-- The true-objective coefficient is strictly positive before all requested
accuracies. -/
theorem currentDecreaseCoefficient_pos {p q : ℕ} (P : Settings p q)
    {M S : ℝ} (hM : 1 ≤ M) : 0 < currentDecreaseCoefficient P M S :=
  mul_pos (half_pos P.eta1_pos) (currentReferenceCoefficient_pos P hM)

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every actual trial has a computed Taylor decrease from its current failed check,
without a next-point nonoptimality hypothesis. -/
theorem computed_decrement_lower_current (h : Run f P ε D N)
    {M S : ℝ} (hM : 1 ≤ M) (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) :
    currentReferenceCoefficient P M S * (minimumAccuracy P.order_pos ε) ^ (q + 1) ≤
      TaylorModel.jetDecrement (D.jet k) p (D.step k) := by
  let μ := minimumAccuracy P.order_pos ε
  let κ := stepRadiusCoefficient P.zeta P.theta M S
  have hκ := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one.le hM
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp ((h.trial_rule k hk).mp ht).1
  have hone := h.step_one k hk.le
  rw [ha] at hone
  have hreference := hone.outcome.2.2.1
  have hcompare := (h.step_two k hk ((h.trial_rule k hk).mp ht).1).comparison
  have hgap := reference_gap_le_computed_decrement (h.updates.pos hk.le).le hcompare
  have hfloor := (h.radius_floor_sharp hM hparam hjet).2.1 k hk.le a
  have hμa : μ ≤ ε a := minimumAccuracy_le P.order_pos ε a
  have hb : 0 ≤ κ * μ := mul_nonneg hκ.1.le hμ.le
  have hb1 : κ * μ ≤ 1 :=
    (mul_le_of_le_one_left hμ.le hκ.2).trans (hμa.trans (h.accuracy_le_one a))
  have hbδ : κ * μ ≤ D.checkedRadius k a :=
    (mul_le_mul_of_nonneg_left hμa hκ.1.le).trans hfloor
  have haj : modelOrder a ≤ q := by unfold modelOrder; omega
  have hpow := (pow_div_factorial_antitone (j := modelOrder a) hb hb1 haj).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hb hbδ (modelOrder a))
      (Nat.cast_nonneg _))
  have hz := P.zeta_pos
  have he := h.accuracy_pos a
  have hscale := mul_le_mul
    (mul_le_mul_of_nonneg_left hμa (show 0 ≤ P.zeta / 4 by positivity)) hpow
    (div_nonneg (pow_nonneg hb _) (Nat.cast_nonneg _))
    (show 0 ≤ P.zeta / 4 * ε a by positivity)
  have hc : currentReferenceCoefficient P M S * μ ^ (q + 1) =
      P.zeta / 4 * μ * ((κ * μ) ^ q / (q.factorial : ℝ)) := by
    unfold currentReferenceCoefficient
    dsimp [κ]
    rw [mul_pow, pow_succ]
    ring
  rw [hc]
  exact hscale.trans (by simpa only [mul_div_assoc] using hreference.trans hgap)

/-- Every accepted actual trial consumes the fixed current-check objective decrease,
including trials that already follow a true criticality certificate. -/
theorem function_decrease_uniform_current (h : Run f P ε D N)
    {M S : ℝ} (hM : 1 ≤ M) (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (ha : P.eta1 ≤ D.ratio k) :
    currentDecreaseCoefficient P M S * (minimumAccuracy P.order_pos ε) ^ (q + 1) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hc := mul_le_mul_of_nonneg_left
    (h.computed_decrement_lower_current hM hparam hjet hk ht)
    (half_pos P.eta1_pos).le
  calc _ ≤ P.eta1 / 2 * TaylorModel.jetDecrement (D.jet k) p (D.step k) := by
          simpa only [currentDecreaseCoefficient, mul_assoc] using hc
    _ ≤ _ := h.function_decrease_ge_computed hk ht ha

/-- A lower objective bound controls every accepted trial through the current-check
decrease. -/
theorem successful_card_le_current (h : Run f P ε D N)
    {M S flow : ℝ} (hM : 1 ≤ M) (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : flow ≤ f (D.point N)) :
    ((successfulIterations (successfulSet D.trials D.ratio P.eta1) N).card : ℝ) ≤
      (f (D.point 0) - flow) / (currentDecreaseCoefficient P M S *
        (minimumAccuracy P.order_pos ε) ^ (q + 1)) := by
  apply card_successful_le_gap_div (S := successfulSet D.trials D.ratio P.eta1)
    (f := fun i => f (D.point i)) (k := N)
    (mul_pos (currentDecreaseCoefficient_pos P hM)
      (pow_pos (minimumAccuracy_pos P.order_pos h.accuracy_pos) _)) hlow
  · intro k hk ha
    exact h.function_decrease_uniform_current hM hparam hjet hk ha.1 ha.2
  · intro k hk ha
    exact (h.objective_eq_of_not_successful hk ha).le

/-- Actual parameter and accuracy updates give an inverse-power-plus-logarithm
iteration budget with no effective-margin assumption. -/
theorem iterations_le_current (h : Run f P ε D N)
    {M S flow : ℝ} (hM : 1 ≤ M) (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : flow ≤ f (D.point N)) :
    (N : ℝ) ≤ trialCountFactor P.toSettings * ((f (D.point 0) - flow) /
      (currentDecreaseCoefficient P M S * (minimumAccuracy P.order_pos ε) ^ (q + 1))) +
      trialCountOffset P.toSettings S +
      accuracyCountSlope P.toSettings * |Real.log (minimumAccuracy P.order_pos ε)| +
      accuracyCountOffset P.toSettings M S := by
  have hs := h.successful_card_le_current hM hparam
    (fun k hk i hi hip => hjet k hk i (by omega) hip) hlow
  have ht := h.trial_card_le_successful (hparam N le_rfl)
  have ha := h.accuracy_card_le hM hparam hjet h.no_exit
  have hf : 0 ≤ trialCountFactor P.toSettings := zero_le_one.trans
    (one_le_trialCountFactor P.toSettings)
  have hscale := mul_le_mul_of_nonneg_right hs hf
  have ht' : ((successfulIterations D.trials N).card : ℝ) ≤
      trialCountFactor P.toSettings * ((f (D.point 0) - flow) /
        (currentDecreaseCoefficient P M S * (minimumAccuracy P.order_pos ε) ^ (q + 1))) +
        trialCountOffset P.toSettings S := by nlinarith
  have hpart : (N : ℝ) = (successfulIterations D.trials N).card +
      (successfulIterations D.trialsᶜ N).card := by
    exact_mod_cast (card_successful_add_card_unsuccessful D.trials N).symm
  rw [hpart]
  linarith
end Run
/-- Every consistent actual EDA execution reaches its first literal stopping test
without an effective-margin assumption. -/
theorem exists_stopping_current {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {ε : Fin q → ℝ} {D : ExecutionData E q}
    (hprefix : ∀ N, (∀ k < N, ¬StopsAt P ε D k) → Run f P ε D N)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) :
    ∃ K, StopsAt P ε D K ∧ Run f P ε D K ∧ ∀ k < K, ¬StopsAt P ε D k := by
  classical
  have hex : ∃ K, StopsAt P ε D K := by
    by_contra hn
    push Not at hn
    let M := executionTensorCap P.toSettings L
    let S := executionParameterCap P.toSettings L
    let bound := trialCountFactor P.toSettings * ((f (D.point 0) - flow) /
        (currentDecreaseCoefficient P M S * (minimumAccuracy P.order_pos ε) ^ (q + 1))) +
      trialCountOffset P.toSettings S +
      accuracyCountSlope P.toSettings * |Real.log (minimumAccuracy P.order_pos ε)| +
      accuracyCountOffset P.toSettings M S
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have h := hprefix N (fun k _ => hn k)
    have hcaps := h.actual_caps hf hL hlip
    have hb := h.iterations_le_current (one_le_executionTensorCap P.toSettings hL)
      hcaps.1 hcaps.2 (hlow _)
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩
  · exact fun k hk => Nat.find_min hex hk
  · exact fun k hk => Nat.find_min hex hk
/-- Actual EDA stopping and initialized evaluation counts have uniform constants and
the coarse epsilon_min inverse-(q+1) rate, with no additional margin. -/
theorem evaluation_complexity_current (f : E → ℝ) {p q : ℕ} (P : Settings p q) (x₀ : E)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) :
    let M := executionTensorCap P.toSettings L
    let S := executionParameterCap P.toSettings L
    ∃ c > 0, ∀ (ε : Fin q → ℝ) (D : ExecutionData E q), D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬StopsAt P ε D k) → Run f P ε D N) →
      ∃ K, StopsAt P ε D K ∧ Run f P ε D K ∧
        (∀ k < K, ¬StopsAt P ε D k) ∧
        (∀ a, 0 < D.checkedRadius K a ∧ D.checkedRadius K a ≤ 1) ∧
        (∀ a, TaylorModel.criticality f (modelOrder a) (D.point K)
          (D.checkedRadius K a) ≤ ε a * D.checkedRadius K a ^ modelOrder a /
            (modelOrder a).factorial) ∧
        ((2 * (successfulIterations D.trials K).card) : ℝ) ≤
          2 * trialCountFactor P.toSettings * ((f x₀ - flow) /
            (c * (minimumAccuracy P.order_pos ε) ^ (q + 1))) +
            2 * |trialCountOffset P.toSettings S| + 2 ∧
        (derivativeEvaluations D.trials D.ratio P.eta1 K : ℝ) ≤
          (f x₀ - flow) / (c * (minimumAccuracy P.order_pos ε) ^ (q + 1)) +
            accuracyCountSlope P.toSettings * |Real.log (minimumAccuracy P.order_pos ε)| +
            accuracyCountOffset P.toSettings M S + 1 := by
  let M := executionTensorCap P.toSettings L
  let S := executionParameterCap P.toSettings L
  let c := currentDecreaseCoefficient P M S
  have hM : 1 ≤ M := one_le_executionTensorCap P.toSettings hL
  refine ⟨c, currentDecreaseCoefficient_pos P hM, ?_⟩
  intro ε D hinit hprefix
  obtain ⟨K, hstop, hrun, hfirst⟩ := exists_stopping_current hprefix hf hL hlip hlow
  obtain ⟨hparam, hjet⟩ := hrun.actual_caps hf hL hlip
  have hs := hrun.successful_card_le_current hM hparam
    (fun k hk i hi hip => hjet k hk i (by omega) hip) (hlow _)
  have ht := hrun.trial_card_le_successful (hparam K le_rfl)
  have ha := hrun.accuracy_card_le hM hparam hjet hfirst
  have hfac : 0 ≤ trialCountFactor P.toSettings := zero_le_one.trans
    (one_le_trialCountFactor P.toSettings)
  have hscale := mul_le_mul_of_nonneg_right hs hfac
  rw [hinit] at hs hscale
  obtain ⟨hlegal, hopt⟩ := hrun.stopped_optimality le_rfl hstop
  refine ⟨K, hstop, hrun, hfirst, hlegal, hopt, ?_, ?_⟩
  · have hoff := le_abs_self (trialCountOffset P.toSettings S)
    dsimp only [c, S] at *
    nlinarith
  · simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
    dsimp only [c]
    linarith
end InexactRegularization.Explicit
