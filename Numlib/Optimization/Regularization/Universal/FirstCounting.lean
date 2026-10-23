import Numlib.Optimization.Regularization.Universal.Counting
/-!
# First-order-only universal evaluation bounds

Actual objective decreases, update intervals and literal stopping checks give
the single accuracy power, logarithm and initialized evaluation schedules.
-/
namespace UniversalRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact first-order decrease coefficient is positive independently of the accuracy. -/
theorem decreaseCoefficientOne_pos {p : ℕ} (P : Settings p) (H β : ℝ) :
    0 < decreaseCoefficientOne P H β := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hfac := Real.finiteFactorial_pos (show 0 ≤ P.r by linarith [P.power_gt])
  unfold decreaseCoefficientOne
  exact mul_pos (div_pos P.eta1_pos hfac)
    (Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos P.alpha1_pos _)
      (uniformCapOne_pos P H β)) _)

/-- Genuine first-order prefixes have the source successful trial budget. -/
theorem Run.successful_card_le_one {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β flow : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    (hlow : ∀ x, flow ≤ f x) {ε : ℝ} {D : Data E} {N : ℕ}
    (h : Run f P ε none D N) :
    ((successfulIterations (successful f P none D) N).card : ℝ) ≤
      (f (D.point 0) - flow) / (decreaseCoefficientOne P H β *
        ε ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1))) := by
  exact card_successful_le_gap_div (S := successful f P none D)
    (f := fun i => f (D.point i)) (k := N)
    (mul_pos (decreaseCoefficientOne_pos P H β)
      (Real.rpow_pos_of_pos h.accuracy1_pos _)) (hlow _)
    (fun _ hi hs => h.successful_decrease_one hf hH hβ hβ1 hholder ha har hi hs)
    (fun _ hi hu => (h.unsuccessful_objective hi hu).le)

/-- Actual parameter updates give the first-order trial budget and its single logarithm. -/
theorem Run.iterations_le_one {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β flow : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    (hlow : ∀ x, flow ≤ f x) {ε : ℝ} {D : Data E} {N : ℕ}
    (h : Run f P ε none D N) :
    (N : ℝ) ≤ (f (D.point 0) - flow) / (decreaseCoefficientOne P H β *
        ε ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1))) *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      (Real.log (uniformCapOne P H β / P.sigmaInitial) +
        (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε|) /
          Real.log P.gamma2 := by
  have ht := iteration_bound_of_parameter_upper
    (S := successful f P none D) (fun _ hi => h.parameter_pos hi)
    P.gamma1_pos P.gamma1_lt P.gamma2_gt
    (h.parameter_le_uniform_one hf hH hβ hβ1 hholder ha har le_rfl)
    (fun _ hi hs => h.successful_parameter_lower hi hs)
    (fun _ hi hu => h.unsuccessful_parameter_lower hi hu)
  rw [h.initial_parameter] at ht
  have hl : Real.log ε = -|Real.log ε| := by
    rw [abs_of_nonpos (Real.log_nonpos h.accuracy1_pos.le h.accuracy1_le),neg_neg]
  have hid : Real.log (uniformCapOne P H β *
      ε ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1)) / P.sigmaInitial) =
      Real.log (uniformCapOne P H β / P.sigmaInitial) +
        (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε| := by
    rw [Real.log_div (mul_pos (uniformCapOne_pos P H β)
      (Real.rpow_pos_of_pos h.accuracy1_pos _)).ne' P.sigmaInitial_pos.ne',
      Real.log_mul (uniformCapOne_pos P H β).ne' (Real.rpow_pos_of_pos h.accuracy1_pos _).ne',
      Real.log_rpow h.accuracy1_pos,
      Real.log_div (uniformCapOne_pos P H β).ne' P.sigmaInitial_pos.ne',hl]
    simp only [abs_neg,abs_abs]
    ring
  rw [hid] at ht
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right
      (h.successful_card_le_one hf hH hβ hβ1 hholder ha har hlow)
        (by positivity [Real.log_pos P.gamma2_gt])) le_rfl)
end UniversalRegularization
