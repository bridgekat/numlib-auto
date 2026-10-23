import Numlib.Optimization.Regularization.Universal.Penalty

/-!
# Successful decrease in universal regularization

The true ratio, accepted point update, length checks and parameter caps imply
the exact first - and second-order Hölder accuracy powers.
-/
namespace UniversalRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed single-test cap is positive independently of the accuracy. -/
theorem uniformCapOne_pos {p : ℕ} (P : Settings p) (H β : ℝ) :
    0 < uniformCapOne P H β := P.sigmaInitial_pos.trans_le (le_max_left _ _)

/-- The fixed two-test cap is positive independently of the accuracies. -/
theorem uniformCapTwo_pos {p : ℕ} (P : Settings p) (H β : ℝ) :
    0 < uniformCapTwo P H β := (uniformCapOne_pos P H β).trans_le (le_max_left _ _)

/-- Acceptance gives actual objective decrease at least the regularization penalty. -/
theorem Run.accepted_decrease {p : ℕ} {P : Settings p} {f : E → ℝ}
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k < N)
    (hs : P.eta1 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k) :
    P.eta1 / Real.finiteFactorial P.r * (D.parameter k * ‖D.step k‖ ^ P.r) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hp := h.prediction_pos hk
  have hh := (le_div_iff₀ hp).mp hs.1
  have hd := mul_le_mul_of_nonneg_left (h.step_test k hk).taylor_decrease.le
    P.eta1_pos.le
  rw [h.point_update k hk,ite_eq_left hs]
  convert hd.trans hh using 1
  ring

/-- The exact fixed successful - decrease constant for first-order requests. -/
noncomputable def decreaseCoefficientOne {p : ℕ} (P : Settings p) (H β : ℝ) : ℝ :=
  P.eta1 / Real.finiteFactorial P.r * (P.alpha1 ^ P.r / uniformCapOne P H β) ^ (1 / (P.r - 1))

/-- The exact fixed successful - decrease constant for two enabled tests. -/
noncomputable def decreaseCoefficientTwo {p : ℕ} (P : Settings p) (H β : ℝ) : ℝ :=
  P.eta1 / Real.finiteFactorial P.r * min ((P.alpha1 ^ P.r / uniformCapTwo P H β) ^ (1 / (P.r - 1)))
      ((P.alpha2 ^ P.r / (uniformCapTwo P H β) ^ (2 : ℝ)) ^ (1 / (P.r - 2)))

/-- Every successful actual first-order trial has the precise source decrease. -/
theorem Run.successful_decrease_one {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε : ℝ} {D : Data E} {N k : ℕ} (h : Run f P ε none D N) (hk : k < N)
    (hs : P.eta1 ≤ ratio f p D k ∧ LengthChecks f P none D k) :
    decreaseCoefficientOne P H β * ε ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1)) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hfail : ε < ‖fderiv ℝ f (D.point k + D.step k)‖ := by
    have hh := h.trial_failure k hk
    simpa [Stops] using hh
  have hlen : P.alpha1 * ε ≤ D.parameter k * ‖D.step k‖ ^ (P.r - 1) :=
    (mul_le_mul_of_nonneg_left hfail.le P.alpha1_pos.le).trans hs.2.1
  have hp := penalty_lower_accuracy P.alpha1_pos h.accuracy1_pos
    (h.parameter_pos hk.le) (norm_pos_iff.mpr (h.step_test k hk).ne_zero)
    (uniformCapOne_pos P H β) (show (0 : ℝ) ≤ 1 by norm_num) ha har
    (h.parameter_le_uniform_one hf hH hβ hβ1 hholder ha har hk.le) hlen
  rw [Real.rpow_one] at hp
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hpr : 0 < Real.finiteFactorial P.r :=
    Real.finiteFactorial_pos (by linarith [P.power_gt])
  have hh := mul_le_mul_of_nonneg_left hp (div_pos P.eta1_pos hpr).le
  calc
    _ ≤ P.eta1 / Real.finiteFactorial P.r *
        (D.parameter k * ‖D.step k‖ ^ P.r) := by
      simpa only [decreaseCoefficientOne,mul_assoc] using hh
    _ ≤ _ := h.accepted_decrease hk hs

/-- Every successful actual two-test trial has the minimum of the exact source powers. -/
theorem Run.successful_decrease_two {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε1 ε2 : ℝ} {D : Data E} {N k : ℕ} (h : Run f P ε1 (some ε2) D N) (hk : k < N)
    (hs : P.eta1 ≤ ratio f p D k ∧ LengthChecks f P (some ε2) D k) :
    decreaseCoefficientTwo P H β * min (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1)))
        (ε2 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 2))) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  let a : ℝ := (p : ℝ) + β
  let δ := min (ε1 ^ (a / (a - 1))) (ε2 ^ (a / (a - 2)))
  let U := uniformCapTwo P H β
  have hε2 : 0 < ε2 := (h.accuracy2 ε2 (by simp)).1
  have hδ : 0 < δ := lt_min (Real.rpow_pos_of_pos h.accuracy1_pos _)
    (Real.rpow_pos_of_pos hε2 _)
  have hcap : D.parameter k ≤ U * δ ^ ((a - P.r) / a) := by
    refine (h.parameter_le_uniform_two hf hH hβ hβ1 hholder ha har hk.le).trans ?_
    apply mul_le_mul_of_nonneg_left _ (uniformCapTwo_pos P H β).le
    exact max_le (parameter_accuracy_le h.accuracy1_pos hδ (by norm_num)
      (by linarith) har (min_le_left _ _))
      (parameter_accuracy_le hε2 hδ (by norm_num) ha har (min_le_right _ _))
  have hσ := h.parameter_pos hk.le
  have ht := norm_pos_iff.mpr (h.step_test k hk).ne_zero
  have hU := uniformCapTwo_pos P H β
  have hpen : min ((P.alpha1 ^ P.r / U) ^ (1 / (P.r - 1)))
      ((P.alpha2 ^ P.r / U ^ (2 : ℝ)) ^ (1 / (P.r - 2))) * δ ≤
        D.parameter k * ‖D.step k‖ ^ P.r := by
    by_cases hg : ε1 < ‖fderiv ℝ f (D.point k + D.step k)‖
    · have hl := accuracy_scale_le h.accuracy1_pos hδ (by norm_num : (0 : ℝ) ≤ 1)
        (show 1 < a by dsimp [a];linarith) (min_le_left _ _)
      have hlen := (mul_le_mul_of_nonneg_left (hl.trans hg.le) P.alpha1_pos.le).trans hs.2.1
      have hh := penalty_lower_scale P.alpha1_pos hδ hσ ht hU
        (show (0 : ℝ) ≤ 1 by norm_num) (show 1 < a by dsimp [a];linarith) har hcap hlen
      rw [Real.rpow_one] at hh
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hδ.le).trans hh
    · have hc : ¬∀ v : E, ‖v‖ = 1 →
          -ε2 ≤ iteratedFDeriv ℝ 2 f (D.point k + D.step k) (fun _ => v) := by
        intro hall
        apply h.trial_failure k hk
        refine ⟨le_of_not_gt hg,?_⟩
        intro e he
        have heq : ε2 = e := Option.some.inj (Option.mem_def.mp he)
        subst e
        exact hall
      push Not at hc
      obtain ⟨v,hv,hneg⟩ := hc
      have hl := accuracy_scale_le hε2 hδ (by norm_num : (0 : ℝ) ≤ 2) ha
        (min_le_right _ _)
      have hlen := (mul_le_mul_of_nonneg_left (hl.trans (by linarith :
          ε2 ≤ -iteratedFDeriv ℝ 2 f (D.point k + D.step k) (fun _ => v)))
            P.alpha2_pos.le).trans (by simpa only [mul_neg, neg_mul] using
              (hs.2.2 ε2 (by simp) v hv))
      have hh := penalty_lower_scale P.alpha2_pos hδ hσ ht hU
        (show (0 : ℝ) ≤ 2 by norm_num) ha har hcap hlen
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hδ.le).trans hh
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hpr : 0 < Real.finiteFactorial P.r :=
    Real.finiteFactorial_pos (by linarith [P.power_gt])
  have hh := mul_le_mul_of_nonneg_left hpen (div_pos P.eta1_pos hpr).le
  calc
    _ ≤ P.eta1 / Real.finiteFactorial P.r *
        (D.parameter k * ‖D.step k‖ ^ P.r) := by
      simpa only [decreaseCoefficientTwo,mul_assoc] using hh
    _ ≤ _ := h.accepted_decrease hk hs
end UniversalRegularization
