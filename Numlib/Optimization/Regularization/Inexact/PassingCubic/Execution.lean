import Numlib.Optimization.Regularization.Inexact.PassingCubic.Data

/-!
# Primitive cubic execution rules

The actual oracle allowances, candidate computations, short-step guard, objective
rejection ratio and explicit verification failures hold for every listed iteration.
-/

namespace InexactRegularization.PassingCubic
open InexactTrustRegion EvaluationComplexity

/-- Every actual error request is strictly positive. -/
theorem accuracy_pos (k : ℕ) : 0 < accuracy k := by unfold accuracy height; positivity

/-- All requests through iteration 382 permit the small positive missing true gradient. -/
theorem accuracy_lower {k : ℕ} (hk : k ≤ 382) : perturbation ≤ accuracy k := by
  have he : (k - 1) ≤ 381 := by omega
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he
  have hnum : perturbation * (2 : ℝ) ^ 381 = 2 * height := by
    rw [show (381 : ℕ) = 150 + 150 + 81 by rfl, pow_add, pow_add]
    norm_num [perturbation, height]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (k - 1))).mpr
  calc perturbation * 2 ^ (k - 1) ≤ perturbation * 2 ^ 381 :=
      mul_le_mul_of_nonneg_left hp (by unfold perturbation; positivity)
    _ = 2 * height := hnum

/-- The accuracy request at iteration 382 is exactly the omitted true first derivative. -/
theorem accuracy_at_bad : accuracy 382 = perturbation := by
  unfold accuracy
  norm_num only [Nat.reduceSub]
  rw [show (381 : ℕ) = 150 + 150 + 81 by rfl, pow_add, pow_add]
  norm_num [perturbation, height]

/-- The actual ghost tensor error is the sum of the large negative computed gradient and
small true gradient; higher tensors are exact. -/
theorem ghost_oracle_error {j : ℕ} (hj : 1 ≤ j) (hj3 : j ≤ 3) :
    ‖ghostJet height curvature j - iteratedFDeriv ℝ j (objective perturbation curvature) 0‖ =
      if j = 1 then height + perturbation else 0 := by
  change ‖iteratedFDeriv ℝ j (ghostPolynomial height curvature).eval 0 -
    iteratedFDeriv ℝ j (objective perturbation curvature) 0‖ = _
  simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
  rw [← map_sub, LinearIsometryEquiv.norm_map, ghost_jets _ _ hj3, objective_jets _ _ hj3]
  interval_cases j <;> norm_num only [Real.norm_eq_abs, Nat.reduceEqDiff, reduceIte,
    sub_self, abs_zero]
  rw [show -height - perturbation = -(height + perturbation) by ring,
    abs_neg, abs_of_nonneg (by unfold height perturbation; positivity)]

/-- Every supplied derivative tensor satisfies its actual operator error allowance,
including the exact endpoint refresh. -/
theorem oracle {k i : ℕ} (hi : 1 ≤ i) (hip : i ≤ 3) :
    ‖data.jet k i - iteratedFDeriv ℝ i (objective perturbation curvature) (data.point k)‖ ≤
      settings.errorCoefficient i * data.accuracy k i := by
  change ‖computedJet k i - iteratedFDeriv ℝ i (objective perturbation curvature) 0‖ ≤
    1 * accuracy k
  rw [one_mul]
  by_cases hk : k < 2
  · rw [computedJet, ite_eq_left hk, ghost_oracle_error hi hip]
    have ha : accuracy k = 2 * height := by
      simp [accuracy, Nat.sub_eq_zero_of_le (by omega : k ≤ 1)]
    rw [ha]
    split_ifs
    · linarith [numeric_bounds.1, numeric_bounds.2.2.2.2.1]
    · linarith [numeric_bounds.1]
  · by_cases hk382 : k ≤ 382
    · rw [computedJet, ite_eq_right hk, ite_eq_left hk382, oracle_error _ _ hi hip]
      split_ifs
      · rw [abs_of_nonneg (by unfold perturbation; positivity)]
        exact accuracy_lower hk382
      · exact (accuracy_pos k).le
    · simp only [computedJet, hk, hk382, reduceIte, ftaylorSeries, sub_self, norm_zero]
      exact (accuracy_pos k).le

/-- Every supplied constant tensor equals the true objective value at the current point. -/
theorem exact_value (k : ℕ) : data.jet k 0 (fun _ => 0) = objective perturbation curvature 0 := by
  change computedJet k 0 (fun _ => 0) = _
  by_cases hk : k < 2
  · simp only [computedJet, ite_eq_left hk]
    change (ghostPolynomial height curvature).eval 0 = _
    simp [ghostPolynomial, polynomial, objective]
  · by_cases hk382 : k ≤ 382
    · simp only [computedJet, ite_eq_right hk, ite_eq_left hk382]
      change (polynomial curvature).eval 0 = _
      simp [polynomial, objective]
    · simp only [computedJet, ite_eq_right hk, ite_eq_right hk382, ftaylorSeries,
        iteratedFDeriv_zero_apply]

/-- The computed Taylor decrement at the initial large trial has its exact positive
polynomial value. -/
theorem first_prediction :
    TaylorModel.jetDecrement (data.jet 0) 3 (data.step 0) =
      2 * height - 2 * curvature + 4 / 3 := by
  change TaylorModel.jetDecrement (ghostJet height curvature) 3 2 = _
  rw [TaylorModel.jetDecrement, ghost_value _ _ (by omega), ghost_value _ _ (by omega)]
  norm_num
  ring

/-- The initial trial has strictly positive computed Taylor decrement. -/
theorem first_prediction_pos : 0 < TaylorModel.jetDecrement (data.jet 0) 3 (data.step 0) := by
  rw [first_prediction]
  linarith [numeric_bounds.1, numeric_bounds.2.2.1]

/-- The true objective ratio at the initial large trial is below the acceptance threshold. -/
theorem ratio_rejected : data.ratio 0 < settings.eta1 := by
  have hH : 100 ≤ height := by norm_num [height]
  have hG : 0 ≤ perturbation := by unfold perturbation; positivity
  have hB := numeric_bounds.2.1.le
  have hf : -3 ≤ objective perturbation curvature 2 := by
    unfold objective
    have hb : 0 ≤ curvature * (1 - Real.cos 2) :=
      mul_nonneg hB (sub_nonneg.mpr (Real.cos_le_one 2))
    linarith [Real.neg_one_le_sin (2 : ℝ)]
  change (objective perturbation curvature 0 - objective perturbation curvature 2) /
    TaylorModel.jetDecrement (ghostJet height curvature) 3 2 < 1 / 4
  have hz : objective perturbation curvature 0 = 0 := by simp [objective]
  rw [hz]
  apply (div_lt_iff₀ first_prediction_pos).mpr
  have hp : TaylorModel.jetDecrement (ghostJet height curvature) 3 2 =
      2 * height - 2 * curvature + 4 / 3 := first_prediction
  rw [first_prediction]
  linarith [numeric_bounds.2.2.1]

/-- Every selected preterminal check has an actual Step2 model return with the required
comparison and criticality tests. -/
theorem computation_two {k : ℕ} (hk : k < 383) (hs : data.selected k ≠ none) :
    StepTwoComputation (data.jet k) 3 modelOrder (data.parameter k) settings.theta
      settings.zeta (fun _ => 1 / 2) (data.reference k) (data.checkedRadius k)
      (data.step k) (data.solvedRadius k) := by
  by_cases h0 : k = 0
  · subst k
    change StepTwoComputation (ghostJet height curvature) 3 modelOrder height (9 / 10)
      (1 / 2) (fun _ => 1 / 2) firstCheck.reference firstCheck.reduced 2 (fun _ => 1)
    rw [firstCheck_spec.2.2.1]
    exact ghost_first_step_two numeric_bounds.1 numeric_bounds.2.1.le
      numeric_bounds.2.2.1 firstCheck_spec.2.2.2 (fun _ => 1)
  · by_cases h1 : k = 1
    · subst k
      simpa only [data, computedJet, parameter, check, trialStep, solvedRadius,
        show ¬(1 : ℕ) = 0 by decide, reduceIte, Nat.reduceLT, settings] using
        shortData_spec.2.2.1
    · have hsel : data.selected k = none := by
        simpa only [data, check, h0, h1, show k ≤ 382 by omega, reduceIte] using
          passingCheck_spec.2.1
      exact (hs hsel).elim

/-- Exactly the initial iteration is a trial under the literal selected-order and short-
step error-request guard. -/
theorem trial_rule {k : ℕ} (hk : k < 383) : k ∈ data.trials ↔ data.selected k ≠ none ∧
    (1 ≤ ‖data.step k‖ ∨ ∀ i, 1 ≤ i → i ≤ 3 →
      data.accuracy k i ≤ settings.stepCoefficient * ‖data.step k‖ ^ (3 - i + 1)) := by
  by_cases h0 : k = 0
  · subst k
    simp only [data, Set.mem_singleton_iff, check, reduceIte, firstCheck_spec.2.1,
      reduceCtorEq, trialStep]
    norm_num
  · have ht : k ∉ data.trials := by simpa only [data, Set.mem_singleton_iff] using h0
    simp only [ht, false_iff]
    by_cases h1 : k = 1
    · subst k
      intro h
      have hn : ‖data.step 1‖ < 1 := by
        simpa only [data, trialStep, show ¬(1 : ℕ) = 0 by decide, reduceIte] using
          shortData_spec.2.2.2
      rcases h.2 with hlarge | hrequests
      · linarith
      · have hr := hrequests 3 (by omega) (by omega)
        change accuracy 1 ≤ 1 / 16 * ‖shortData.step‖ ^ (3 - 3 + 1) at hr
        norm_num [accuracy] at hr
        have hh := shortData_spec.2.2.2
        rw [Real.norm_eq_abs] at hh
        linarith [numeric_bounds.1]
    · have hsel : data.selected k = none := by
        simpa only [data, check, h0, h1, show k ≤ 382 by omega, reduceIte] using
          passingCheck_spec.2.1
      exact fun h => h.1 hsel

/-- No preterminal explicit stopping test passes; after the ghost phase the actual tensor
verification budget is too large. -/
theorem never_stops {k : ℕ} (hk : k < 383) :
    ¬Explicit.StopsAt settings (fun _ => 1 / 2) data k := by
  intro hs
  by_cases h0 : k = 0
  · subst k
    have hh := hs.1
    simp only [data, check, reduceIte, firstCheck_spec.2.1, reduceCtorEq] at hh
  · by_cases h1 : k = 1
    · subst k
      have hh := hs.1
      simp only [data, check, show ¬(1 : ℕ) = 0 by decide, reduceIte,
        shortData_spec.2.1, reduceCtorEq] at hh
    · have hδ := passingCheck_spec.2.2.1
      have hb := passingCheck_spec.2.2.2
      have hfail := verification_fails hδ numeric_bounds.2.1.le hb numeric_bounds.2.2.2.1
      have hupper := hs.2 2
      have hrad : data.checkedRadius k 2 = passingCheck.reduced 2 := by
        simp only [data, check, h0, h1, show k ≤ 382 by omega, reduceIte]
      rw [hrad] at hupper
      have hm : tensorErrorBudget (fun _ => perturbation) 3 (passingCheck.reduced 2) ≤
          tensorErrorBudget (data.accuracy k) 3 (passingCheck.reduced 2) := by
        unfold tensorErrorBudget
        apply Finset.sum_le_sum
        intro i hi
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_right (accuracy_lower (k := k) (by omega))
          (pow_nonneg hδ.le _)
      have ho : modelOrder (2 : Fin 3) = 3 := rfl
      rw [ho] at hupper
      norm_num only [settings, Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at hupper
      linarith

end InexactRegularization.PassingCubic
