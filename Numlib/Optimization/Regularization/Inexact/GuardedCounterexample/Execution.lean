import Numlib.Optimization.Regularization.Inexact.GuardedCounterexample.ScalarModel
import Numlib.Optimization.Regularization.Inexact.Explicit.Run
/-!
# A finite execution with large accumulated regularization

The sine objective admits an actual 125-iteration dynamic accuracy execution.
Forty rejected large steps increase the parameter, one inaccurate short step
and 83 exact short steps improve derivative accuracy, and the final exact trial
is accepted. Every primitive model check, function ratio and update is verified.
The actual gradient remains greater than the requested accuracy throughout.
-/

namespace InexactRegularization.GuardedCounterexample
open InexactTrustRegion EvaluationComplexity
/-- Fixed legal settings with a large initial derivative-error allowance. -/
noncomputable def settings : Explicit.Settings 1 1 where
  stepCoefficient := 1 / 16
  stepCoefficient_pos := by norm_num
  initialCap := 2 ^ 40
  initialCap_nonneg := by positivity
  errorBound := 1
  errorBound_nonneg := zero_le_one
  errorCoefficient := fun _ => 1
  errorCoefficient_nonneg := fun _ _ _ => zero_le_one
  errorCoefficient_le := fun _ _ _ => le_rfl
  reduction := 1 / 2
  reduction_pos := by norm_num
  reduction_lt_one := by norm_num
  order_pos := by omega
  order_le := le_rfl
  zeta := 1 / 2
  zeta_pos := by norm_num
  zeta_le_one := by norm_num
  theta := 9 / 10
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  eta1 := 1 / 4
  eta2 := 3 / 4
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1
  sigmaInitial := 1
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := zero_lt_one
  sigmaMin_le_initial := le_rfl
  known_error_bound := rfl
  function_acceptance_margin := by norm_num
  function_success_margin := by norm_num
/-- Rejected large trials double the parameter forty times; subsequent calls preserve it. -/
noncomputable def parameter (k : ℕ) : ℝ := 2 ^ min k 40
/-- The accepted final trial moves once from zero by minus two to the power minus forty. -/
noncomputable def point (k : ℕ) : ℝ := if 124 < k then -(1 / 2 ^ 40) else 0
/-- An inaccurate negative derivative is reused until the first accuracy-only iteration.
Subsequent derivative data are exact. -/
noncomputable def slope (k : ℕ) : ℝ := if k ≤ 40 then -(2 ^ 39) else Real.cos (point k)
/-- Initial derivative requests are unchanged on trials and halved 84 times on accuracy calls. -/
noncomputable def accuracy (k : ℕ) : ℝ := 2 ^ 40 / 2 ^ min (k - 40) 84
/-- Each candidate is the actual global minimizer of its computed regularized model. -/
noncomputable def trialStep (k : ℕ) : ℝ := -slope k / parameter k
/-- The actual optimality loop has zero, one or forty geometric radius reductions. -/
noncomputable def checkCount (k : ℕ) : ℕ := if k < 40 then 0 else if k = 40 then 1 else 40
/-- The reference direction follows the sign of the actual computed derivative. -/
noncomputable def orientation (k : ℕ) : ℝ := if k ≤ 40 then 1 else -1
/-- The completed optimality loop returns its actual geometric candidate radius. -/
noncomputable def checkedRadius (k : ℕ) : ℝ := BacktrackingGradient.step 1 (checkCount k)
/-- All reference candidates attain the computed scalar Taylor criticality. -/
noncomputable def direction (k t : ℕ) : ℝ := orientation k * BacktrackingGradient.step 1 t
/-- Explicit derivative, function, model, ratio and update arrays for the finite execution. -/
noncomputable def data : Explicit.ExecutionData ℝ 1 where
  jet := fun k => jet (Real.sin (point k)) (slope k)
  trials := {k | k < 40 ∨ k = 124}
  point := point
  reference := fun k => direction k (checkCount k)
  step := trialStep
  parameter := parameter
  ratio := fun k => (Real.sin (point k) - Real.sin (point k + trialStep k)) /
    TaylorModel.jetDecrement (jet (Real.sin (point k)) (slope k)) 1 (trialStep k)
  accuracy := fun k _ => accuracy k
  startRadius := fun _ _ => 1
  checkedRadius := fun k _ => checkedRadius k
  solvedRadius := fun _ _ => 1
  checkDirection := fun k _ t => direction k t
  checkCount := fun k _ => checkCount k
  selected := fun _ => some 0
  functionStart := fun k => Real.sin (point k)
  functionTrial := fun k => Real.sin (point k + trialStep k)
  functionRequest := fun k => 1 / 32 *
    TaylorModel.jetDecrement (jet (Real.sin (point k)) (slope k)) 1 (trialStep k)
/-- The actual derivative at the accepted endpoint remains at least 0.99. -/
theorem endpoint_cos :
    (99 : ℝ) / 100 ≤ Real.cos (point 125) ∧ Real.cos (point 125) ≤ 1 := by
  have h := Real.abs_cos_sub_cos_le (point 125) 0
  norm_num [point] at h
  constructor
  · norm_num [point]
    linarith [(abs_le.mp h).1]
  · exact Real.cos_le_one _
/-- Every point in the specified sequence has true derivative between 0.99 and one. -/
theorem cos_mem (k : ℕ) :
    (99 : ℝ) / 100 ≤ Real.cos (point k) ∧ Real.cos (point k) ≤ 1 := by
  by_cases hk : 124 < k
  · simpa only [point, ite_eq_left hk, ite_eq_left (by omega : 124 < 125)] using endpoint_cos
  · norm_num [point, hk]
/-- Every supplied derivative is nonzero with magnitude at least 0.99. -/
theorem slope_abs_lower (k : ℕ) : (99 : ℝ) / 100 ≤ |slope k| := by
  by_cases hk : k ≤ 40
  · norm_num [slope, hk]
  · rw [slope, ite_eq_right hk, abs_of_pos (by linarith [(cos_mem k).1])]
    exact (cos_mem k).1
/-- Every completed optimality check satisfies all primitive ordered halving rules. -/
theorem computation_one (k : ℕ) :
    StepOneComputation (data.jet k) 1 (data.parameter k) settings.zeta
      (fun _ => 1 / 2) (data.startRadius k) (data.checkedRadius k) (data.reference k)
      (data.checkDirection k) (data.checkCount k) (data.selected k) := by
  change StepOneComputation (jet _ (slope k)) 1 (parameter k) (1 / 2)
    (fun _ => 1 / 2) (fun _ => 1) (fun _ => BacktrackingGradient.step 1 (checkCount k))
    (orientation k * BacktrackingGradient.step 1 (checkCount k))
    (fun _ t => orientation k * BacktrackingGradient.step 1 t) (fun _ => checkCount k) (some 0)
  apply stepOne _ _ _ _ |slope k| _
  · unfold orientation
    split_ifs <;> norm_num
  · by_cases hk : k ≤ 40
    · norm_num [slope, orientation, hk]
    · rw [slope, orientation, ite_eq_right hk, ite_eq_right hk,
        abs_of_pos (by linarith [(cos_mem k).1])]
      ring
  · linarith [slope_abs_lower k]
  · by_cases hk : k < 40
    · have hpow : (2 : ℝ) ^ k ≤ 2 ^ 39 := pow_le_pow_right₀ (by norm_num) (by omega)
      simp only [parameter, min_eq_left hk.le, checkCount, ite_eq_left hk,
        BacktrackingGradient.step, pow_zero, div_one, mul_one, slope,
        ite_eq_left (by omega : k ≤ 40)]
      norm_num
      linarith
    · by_cases heq : k = 40
      · subst k
        norm_num [parameter, checkCount, BacktrackingGradient.step, slope]
      · have hk40 : 40 < k := by omega
        simp only [parameter, min_eq_right hk40.le, checkCount, ite_eq_right hk,
          ite_eq_right heq, BacktrackingGradient.step, slope, ite_eq_right (by omega : ¬k ≤ 40)]
        norm_num
        rw [abs_of_pos (by linarith [(cos_mem k).1])]
        linarith [(cos_mem k).1]
  · intro t ht
    by_cases hk : k < 40
    · simp only [checkCount, ite_eq_left hk] at ht
      omega
    · by_cases heq : k = 40
      · subst k
        norm_num [checkCount] at ht
        obtain rfl : t = 0 := by omega
        norm_num [slope, parameter, BacktrackingGradient.step]
      · have hk40 : 40 < k := by omega
        have ht40 : t < 40 := by simpa [checkCount, hk, heq] using ht
        have hpow : (2 : ℝ) ^ t ≤ 2 ^ 39 := pow_le_pow_right₀ (by norm_num) (by omega)
        have hrad : (2 : ℝ) ≤ 2 ^ 40 * BacktrackingGradient.step 1 t := by
          simp only [BacktrackingGradient.step, mul_one_div]
          apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ t)).mpr
          norm_num at *
          linarith
        simp only [slope, ite_eq_right (by omega : ¬k ≤ 40), parameter, min_eq_right hk40.le]
        rw [abs_of_pos (by linarith [(cos_mem k).1])]
        linarith [(cos_mem k).2]
/-- Every supplied regularization parameter is strictly positive. -/
theorem parameter_pos (k : ℕ) : 0 < parameter k := by unfold parameter; positivity
/-- The first forty global model minimizers have magnitude at least one. -/
theorem trialStep_large {k : ℕ} (hk : k < 40) : 1 ≤ ‖trialStep k‖ := by
  have hp : (2 : ℝ) ^ k ≤ 2 ^ 39 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hn : 0 < (2 : ℝ) ^ k := by positivity
  simp only [trialStep, slope, ite_eq_left (by omega : k ≤ 40), neg_neg,
    parameter, min_eq_left hk.le, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 39), abs_of_pos hn]
  apply (le_div_iff₀ hn).mpr
  simpa using hp
/-- All later global model minimizers have magnitude strictly less than one. -/
theorem trialStep_small {k : ℕ} (hk : 40 ≤ k) : ‖trialStep k‖ < 1 := by
  by_cases heq : k = 40
  · subst k
    norm_num [trialStep, slope, parameter]
  · have hkg : ¬k ≤ 40 := by omega
    simp only [trialStep, slope, ite_eq_right hkg, parameter, min_eq_right hk,
      Real.norm_eq_abs, abs_div, abs_neg]
    norm_num
    nlinarith [Real.abs_cos_le_one (point k)]
/-- Every candidate satisfies the actual model comparison and full Step2 tests. -/
theorem computation_two (k : ℕ) :
    StepTwoComputation (data.jet k) 1 modelOrder (data.parameter k) settings.theta
      settings.zeta (fun _ => 1 / 2) (data.reference k) (data.checkedRadius k)
      (data.step k) (data.solvedRadius k) := by
  have h := stepTwo (parameter_pos k) (Real.sin (point k)) (slope k)
    (direction k (checkCount k)) (fun _ : Fin 1 => checkedRadius k)
  change StepTwoComputation (jet _ _) 1 modelOrder (parameter k) (9 / 10) (1 / 2)
    (fun _ => 1 / 2) _ (fun _ => checkedRadius k) (-slope k / parameter k) (fun _ => 1)
  by_cases hk : k < 40
  · have hs : 1 ≤ ‖-slope k / parameter k‖ := trialStep_large hk
    simpa [data, hs, checkedRadius, checkCount, hk] using h
  · have hs : ¬1 ≤ ‖-slope k / parameter k‖ := not_le_of_gt (trialStep_small (by omega))
    simpa only [data, ite_eq_right hs] using h
/-- Every supplied derivative satisfies its actual multilinear operator error allowance. -/
theorem oracle (k i : ℕ) (hi : 1 ≤ i) (hip : i ≤ 1) :
    ‖data.jet k i - iteratedFDeriv ℝ i Real.sin (data.point k)‖ ≤
      settings.errorCoefficient i * data.accuracy k i := by
  obtain rfl : i = 1 := by omega
  change ‖jet (Real.sin (point k)) (slope k) 1 - iteratedFDeriv ℝ 1 Real.sin (point k)‖ ≤
    1 * accuracy k
  rw [oracle_error, one_mul]
  by_cases hk : k ≤ 40
  · have hx : point k = 0 := by simp [point, show ¬124 < k by omega]
    have hsub : k - 40 = 0 := Nat.sub_eq_zero_of_le hk
    norm_num [slope, hk, hx, accuracy, hsub]
  · simp only [slope, ite_eq_right hk, sub_self, abs_zero]
    unfold accuracy
    positivity
/-- Every computed constant tensor is the exact current objective value. -/
theorem exact_value (k : ℕ) : data.jet k 0 (fun _ => 0) = Real.sin (data.point k) :=
  constant_value _ _
/-- The literal computed optimality test selects a trial at every listed point. -/
theorem never_stops (k : ℕ) : ¬Explicit.StopsAt settings (fun _ => 1 / 2) data k := by
  intro h
  simpa only [data, reduceCtorEq] using h.1
/-- The initial rejected trial displacements are positive. -/
theorem trialStep_pos {k : ℕ} (hk : k < 40) : 0 < trialStep k := by
  unfold trialStep
  rw [slope, ite_eq_left (by omega : k ≤ 40), neg_neg]
  exact div_pos (by positivity) (parameter_pos k)
/-- The computed Taylor decrement at its quadratic minimizer is an exact quotient. -/
theorem computed_decrement (k : ℕ) :
    TaylorModel.jetDecrement (data.jet k) 1 (data.step k) = (slope k) ^ 2 / parameter k := by
  change TaylorModel.jetDecrement (jet _ _) 1 (-slope k / parameter k) = _
  rw [decrement]
  ring
/-- Every computed candidate has strictly positive Taylor decrement. -/
theorem computed_decrement_pos (k : ℕ) :
    0 < TaylorModel.jetDecrement (data.jet k) 1 (data.step k) := by
  rw [computed_decrement]
  have hs : slope k ≠ 0 := by
    intro hh
    have h := slope_abs_lower k
    rw [hh, abs_zero] at h
    norm_num at h
  exact div_pos (sq_pos_of_ne_zero hs) (parameter_pos k)
/-- The actual sine objective ratio rejects all forty initial large trials. -/
theorem ratio_rejected {k : ℕ} (hk : k < 40) : data.ratio k < (1 : ℝ) / 4 := by
  have hx : point k = 0 := by simp [point, show ¬124 < k by omega]
  have hlarge : 1 ≤ trialStep k := by
    simpa only [Real.norm_eq_abs, abs_of_pos (trialStep_pos hk)] using trialStep_large hk
  have hD : (2 : ℝ) ^ 39 ≤ TaylorModel.jetDecrement (data.jet k) 1 (data.step k) := by
    change 2 ^ 39 ≤ TaylorModel.jetDecrement (jet _ (slope k)) 1 (trialStep k)
    rw [decrement, slope, ite_eq_left (by omega : k ≤ 40)]
    nlinarith
  change (Real.sin (point k) - Real.sin (point k + trialStep k)) /
    TaylorModel.jetDecrement (data.jet k) 1 (data.step k) < 1 / 4
  apply (div_lt_iff₀ (computed_decrement_pos k)).mpr
  rw [hx, Real.sin_zero, zero_add]
  linarith [Real.neg_one_le_sin (trialStep k)]
/-- The final exact tiny step is very successful for the actual sine objective. -/
theorem ratio_success : (3 : ℝ) / 4 ≤ data.ratio 124 := by
  have hs := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 1 / 2 ^ 40 by positivity)
  norm_num at hs
  norm_num [data, point, trialStep, slope, parameter, decrement]
  linarith
/-- The literal short-step request guard selects precisely the specified trials. -/
theorem trial_rule {k : ℕ} (hk : k < 125) :
    k ∈ data.trials ↔ data.selected k ≠ none ∧
      (1 ≤ ‖data.step k‖ ∨ ∀ i, 1 ≤ i → i ≤ 1 →
        data.accuracy k i ≤ settings.stepCoefficient * ‖data.step k‖ ^ (1 - i + 1)) := by
  change (k < 40 ∨ k = 124) ↔ (some (0 : Fin 1) ≠ none) ∧
    (1 ≤ ‖trialStep k‖ ∨ ∀ i, 1 ≤ i → i ≤ 1 →
      accuracy k ≤ (1 / 16) * ‖trialStep k‖ ^ (1 - i + 1))
  by_cases hearly : k < 40
  · simp only [hearly, true_or, true_iff, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    exact Or.inl (trialStep_large hearly)
  · by_cases hlast : k = 124
    · subst k
      norm_num [trialStep, slope, parameter, point, accuracy]
      intro i hi hip
      obtain rfl : i = 1 := by omega
      norm_num
    · have hk40 : 40 ≤ k := by omega
      have hs := trialStep_small hk40
      simp only [hearly, hlast, false_or, false_iff, ne_eq, reduceCtorEq,
        not_false_eq_true, true_and, not_or]
      refine ⟨not_le_of_gt hs, ?_⟩
      intro hall
      have h := hall 1 le_rfl le_rfl
      by_cases heq : k = 40
      · subst k
        norm_num [accuracy, trialStep, slope, parameter] at h
      · have hk124 : k ≤ 124 := by omega
        have hpoint : point k = 0 := by simp [point, show ¬124 < k by omega]
        have hpow : (2 : ℝ) ^ min (k - 40) 84 ≤ 2 ^ 83 :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hden : (0 : ℝ) < 2 ^ min (k - 40) 84 := by positivity
        have hacc : (1 : ℝ) / 2 ^ 43 ≤ accuracy k := by
          unfold accuracy
          have hh := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 ^ 40)
            hden hpow
          norm_num at hh ⊢
          exact hh
        norm_num [trialStep, slope, parameter, hpoint,
          show ¬k ≤ 40 by omega, min_eq_right hk40] at h
        norm_num at hacc
        linarith
/-- Every initial rejection doubles the actual regularization parameter. -/
theorem parameter_succ_early {k : ℕ} (hk : k < 40) : parameter (k + 1) = 2 * parameter k := by
  rw [parameter, parameter, min_eq_left (by omega : k + 1 ≤ 40), min_eq_left hk.le,
    pow_succ]
  ring
/-- All actual ratios and parameter changes satisfy their primitive update intervals. -/
theorem updates : TrialRegularizationUpdates data.trials data.parameter data.ratio
    settings.eta1 settings.eta2 settings.gamma1 settings.gamma2 settings.gamma3
      settings.sigmaMin 125 := by
  refine ⟨by norm_num [settings], by norm_num [settings, data, parameter],
    by norm_num [settings], by norm_num [settings], by norm_num [settings],
    by norm_num [settings], by norm_num [settings], by norm_num [settings],
    by norm_num [settings], ?_, ?_⟩
  · intro k hk ht
    change k < 40 ∨ k = 124 at ht
    rcases ht with hearly | rfl
    · have hr := ratio_rejected hearly
      have hn1 : ¬settings.eta1 ≤ data.ratio k := by change ¬1 / 4 ≤ _; linarith
      have hn2 : ¬settings.eta2 ≤ data.ratio k := by change ¬3 / 4 ≤ _; linarith
      rw [ite_eq_right hn2, ite_eq_right hn1]
      change parameter (k + 1) ∈ Set.Icc (2 * parameter k) (3 * parameter k)
      rw [parameter_succ_early hearly]
      exact ⟨le_rfl, by linarith [parameter_pos k]⟩
    · have hr : settings.eta2 ≤ data.ratio 124 := ratio_success
      rw [ite_eq_left hr]
      norm_num [settings, data, parameter]
  · intro k hk ht
    have hlate : 40 ≤ k := by change ¬(k < 40 ∨ k = 124) at ht; omega
    change parameter (k + 1) = parameter k
    simp only [parameter, min_eq_right hlate, min_eq_right (by omega : 40 ≤ k + 1)]
/-- Actual derivative requests are reused at trial iterations. -/
theorem accuracy_trial {k : ℕ} (ht : k ∈ data.trials) : accuracy (k + 1) = accuracy k := by
  change k < 40 ∨ k = 124 at ht
  rcases ht with hk | rfl
  · simp only [accuracy, Nat.sub_eq_zero_of_le hk.le,
      Nat.sub_eq_zero_of_le (by omega : k + 1 ≤ 40)]
  · norm_num [accuracy]
/-- Every nontrial iteration multiplies derivative requests by one half. -/
theorem accuracy_improvement {k : ℕ} (hk : k < 125) (ht : k ∉ data.trials) :
    accuracy (k + 1) = (1 / 2) * accuracy k := by
  change ¬(k < 40 ∨ k = 124) at ht
  have hk40 : 40 ≤ k := by omega
  have hlt : k < 124 := by omega
  have he : k + 1 - 40 = k - 40 + 1 := by omega
  unfold accuracy
  rw [min_eq_left (by omega : k + 1 - 40 ≤ 84),
    min_eq_left (by omega : k - 40 ≤ 84), he, pow_succ]
  ring
/-- Each trial updates the point according to its actual objective acceptance ratio. -/
theorem point_trial {k : ℕ} (ht : k ∈ data.trials) :
    data.point (k + 1) = if settings.eta1 ≤ data.ratio k then
      data.point k + data.step k else data.point k := by
  change k < 40 ∨ k = 124 at ht
  rcases ht with hk | rfl
  · have hr := ratio_rejected hk
    have hn : ¬settings.eta1 ≤ data.ratio k := by change ¬1 / 4 ≤ _; linarith
    rw [ite_eq_right hn]
    simp [data, point, show ¬124 < k by omega, show ¬124 < k + 1 by omega]
  · have hr : settings.eta1 ≤ data.ratio 124 := le_trans (by norm_num [settings]) ratio_success
    rw [ite_eq_left hr]
    norm_num [data, point, trialStep, slope, parameter]
/-- Accuracy-only iterations preserve the current point. -/
theorem point_inactive {k : ℕ} (hk : k < 125) (ht : k ∉ data.trials) :
    data.point (k + 1) = data.point k := by
  have hlt : k < 124 := by change ¬(k < 40 ∨ k = 124) at ht; omega
  simp [data, point, show ¬124 < k by omega, show ¬124 < k + 1 by omega]
/-- Rejected trials reuse their actual positive-order derivative tensors. -/
theorem derivative_reuse {k i : ℕ} (ht : k ∈ data.trials)
    (hr : ¬settings.eta1 ≤ data.ratio k) (hi : 1 ≤ i) (hip : i ≤ 1) :
    data.jet (k + 1) i = data.jet k i := by
  obtain rfl : i = 1 := by omega
  have hk : k < 40 := by
    change k < 40 ∨ k = 124 at ht
    rcases ht with h | rfl
    · exact h
    · exact (hr (le_trans (by norm_num [settings]) ratio_success)).elim
  change jet _ (slope (k + 1)) 1 = jet _ (slope k) 1
  rw [slope, slope, ite_eq_left (by omega : k + 1 ≤ 40), ite_eq_left hk.le]
  exact first_tensor_eq _ _ _
/-- All 125 iterations satisfy the complete operational ARqpEDA execution rules. -/
theorem run : Explicit.Run Real.sin settings (fun _ => 1 / 2) data 125 where
  accuracy_pos := fun _ => by norm_num
  accuracy_le_one := fun _ => by norm_num
  initial_parameter := by norm_num [data, parameter, settings]
  initial_radii := fun _ => by norm_num [data]
  updates := updates
  initial_accuracy := fun _ _ _ => by norm_num [data, accuracy, settings]
  accuracy_trial := fun _ _ ht _ _ _ => accuracy_trial ht
  accuracy_improvement := fun _ hk ht _ _ _ => accuracy_improvement hk ht
  oracle_all := fun k _ i hi hip => oracle k i hi hip
  constant_value := fun k _ _ => exact_value k
  error_initial := by
    intro k hk ht
    change |Real.sin (point k) - Real.sin (point k)| ≤ _
    rw [sub_self, abs_zero]
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 32) (computed_decrement_pos k)).le
  error_trial := by
    intro k hk ht
    change |Real.sin (point k + trialStep k) - Real.sin (point k + trialStep k)| ≤ _
    rw [sub_self, abs_zero]
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 32) (computed_decrement_pos k)).le
  request_positive := fun k _ _ =>
    mul_pos (by norm_num : (0 : ℝ) < 1 / 32) (computed_decrement_pos k)
  relative_request := by
    intro k hk ht
    change 1 / 32 * TaylorModel.jetDecrement (data.jet k) 1 (data.step k) ≤
      1 / 16 * TaylorModel.jetDecrement (data.jet k) 1 (data.step k)
    linarith [computed_decrement_pos k]
  no_exit := fun k _ => never_stops k
  step_one := fun k _ => computation_one k
  step_two := fun k _ _ => computation_two k
  trial_rule := fun _ hk => trial_rule hk
  ratio := fun _ _ _ => rfl
  point_trial := fun _ _ ht => point_trial ht
  point_inactive := fun _ hk ht => point_inactive hk ht
  radius_trial := by
    intro k hk ht
    change k < 40 ∨ k = 124 at ht
    rcases ht with hearly | rfl
    · have hc : checkedRadius k = 1 := by simp [checkedRadius, checkCount, hearly]
      change (fun _ : Fin 1 => (1 : ℝ)) = if _ then (fun _ => 1) else (fun _ => checkedRadius k)
      rw [hc]
      split_ifs <;> rfl
    · have hh : settings.eta1 ≤ data.ratio 124 ∧ ‖data.step 124‖ < 1 :=
        ⟨le_trans (by norm_num [settings]) ratio_success, trialStep_small (by omega)⟩
      rw [ite_eq_left hh]
      rfl
  radius_inactive := fun _ _ _ => rfl
  derivative_reuse := fun _ _ ht hr _ hi hip => derivative_reuse ht hr hi hip
/-- Every point produced by the finite trace fails true first-order optimality
at every positive radius, even though its objective and derivative data are globally regular. -/
theorem not_critical (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (1 / 2) * δ < TaylorModel.criticality Real.sin 1 (point k) δ := by
  rw [sine_criticality hδ.le, abs_of_pos (by linarith [(cos_mem k).1])]
  nlinarith [(cos_mem k).1]
/-- The same exact objective evaluations satisfy all 125 operational ARqpIDA iterations,
including reuse of the entire jet on rejected trials. -/
theorem ida_run : InexactRegularization.Run Real.sin settings.toSettings
    (fun _ => 1 / 2) data.toExecutionData 125 where
  accuracy_pos := run.accuracy_pos
  accuracy_le_one := run.accuracy_le_one
  initial_parameter := run.initial_parameter
  initial_radii := run.initial_radii
  updates := run.updates
  initial_accuracy := run.initial_accuracy
  accuracy_trial := run.accuracy_trial
  accuracy_improvement := run.accuracy_improvement
  oracle_all := run.oracle_all
  exact_value := fun k _ => exact_value k
  step_one := run.step_one
  step_two := run.step_two
  trial_rule := run.trial_rule
  ratio := fun _ _ _ => rfl
  point_trial := run.point_trial
  point_inactive := run.point_inactive
  radius_trial := run.radius_trial
  radius_inactive := run.radius_inactive
  jet_reuse := by
    intro k hk ht hr
    have hearly : k < 40 := by
      change k < 40 ∨ k = 124 at ht
      rcases ht with h | rfl
      · exact h
      · exact (hr (le_trans (by norm_num [settings]) ratio_success)).elim
    change jet (Real.sin (point (k + 1))) (slope (k + 1)) =
      jet (Real.sin (point k)) (slope k)
    simp [point, slope, show ¬124 < k + 1 by omega, show ¬124 < k by omega,
      show k + 1 ≤ 40 by omega, show k ≤ 40 by omega]
end InexactRegularization.GuardedCounterexample
