import Numlib.Optimization.Regularization.Universal.Decrease
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Actual universal-regularization trial budgets

Successful trials consume the objective gap. Failed trials leave the point
unchanged and increase the parameter by its actual update factor.
-/
namespace UniversalRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local instance] Classical.propDecidable

/-- Accepted trials use both the true ratio and every active length test. -/
def successful {p : ℕ} (f : E → ℝ) (P : Settings p) (ε2 : Option ℝ) (D : Data E) : Set ℕ :=
  {k | P.eta1 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k}

/-- Every successful update can reduce the parameter by at most its allowed factor. -/
theorem Run.successful_parameter_lower {p : ℕ} {P : Settings p} {f : E → ℝ}
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k < N) (hs : k ∈ successful f P ε2 D) :
    P.gamma1 * D.parameter k ≤ D.parameter (k + 1) := by
  have hu := h.parameter_update k hk
  split_ifs at hu with hv hc
  · exact hu.1
  · exact (show P.gamma1 * D.parameter k ≤ D.parameter k by
      nlinarith [h.parameter_pos hk.le,P.gamma1_lt]).trans hu.1
  · exact (hc hs).elim

/-- A failed trial increases the parameter by at least the unsuccessful factor. -/
theorem Run.unsuccessful_parameter_lower {p : ℕ} {P : Settings p} {f : E → ℝ}
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k < N) (hs : k ∉ successful f P ε2 D) :
    P.gamma2 * D.parameter k ≤ D.parameter (k + 1) := by
  change ¬(P.eta1 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k) at hs
  have hv : ¬(P.eta2 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k) := by
    rintro ⟨hr,hl⟩
    exact hs ⟨P.eta12.trans hr,hl⟩
  have hu := h.parameter_update k hk
  rw [ite_eq_right hv,ite_eq_right hs] at hu
  exact hu.1

/-- The actual point update preserves the objective on every failed trial. -/
theorem Run.unsuccessful_objective {p : ℕ} {P : Settings p} {f : E → ℝ}
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k < N) (hs : k ∉ successful f P ε2 D) :
    f (D.point (k + 1)) = f (D.point k) := by
  change ¬(P.eta1 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k) at hs
  rw [h.point_update k hk,ite_eq_right hs]

/-- The exact two-test decrease coefficient is positive, including zero Hölder constants. -/
theorem decreaseCoefficientTwo_pos {p : ℕ} (P : Settings p) (H β : ℝ) :
    0 < decreaseCoefficientTwo P H β := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hfac := Real.finiteFactorial_pos (show 0 ≤ P.r by linarith [P.power_gt])
  unfold decreaseCoefficientTwo
  exact mul_pos (div_pos P.eta1_pos hfac) (lt_min
      (Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos P.alpha1_pos _)
        (uniformCapTwo_pos P H β)) _)
      (Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos P.alpha2_pos _)
        (Real.rpow_pos_of_pos (uniformCapTwo_pos P H β) _)) _))

/-- Every genuine two-test prefix has the exact source successful-trial budget. -/
theorem Run.successful_card_le_two {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β flow : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    (hlow : ∀ x, flow ≤ f x) {ε1 ε2 : ℝ} {D : Data E} {N : ℕ}
    (h : Run f P ε1 (some ε2) D N) :
    ((successfulIterations (successful f P (some ε2) D) N).card : ℝ) ≤
      (f (D.point 0) - flow) / (decreaseCoefficientTwo P H β *
        min (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1)))
          (ε2 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 2)))) := by
  have hc := decreaseCoefficientTwo_pos P H β
  have hε2 : 0 < ε2 := (h.accuracy2 ε2 (by simp)).1
  exact card_successful_le_gap_div (S := successful f P (some ε2) D)
    (f := fun i => f (D.point i)) (k := N)
    (mul_pos hc (lt_min (Real.rpow_pos_of_pos h.accuracy1_pos _)
      (Real.rpow_pos_of_pos hε2 _))) (hlow _)
    (fun _ hi hs => h.successful_decrease_two hf hH hβ hβ1 hholder ha har hi hs)
    (fun _ hi hu => (h.unsuccessful_objective hi hu).le)

/-- The two-test parameter cap is bounded by a product of its accuracy powers. -/
theorem Run.parameter_le_product_two {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε1 ε2 : ℝ} {D : Data E} {N : ℕ} (h : Run f P ε1 (some ε2) D N) :
    D.parameter N ≤ uniformCapTwo P H β *
      (ε1 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1))) *
      (ε2 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2))) := by
  have hu1 := one_le_accuracy_power h.accuracy1_pos h.accuracy1_le
    (show 1 < (p : ℝ) + β by linarith) har
  have hu2 := one_le_accuracy_power (h.accuracy2 ε2 (by simp)).1
    (h.accuracy2 ε2 (by simp)).2.1 ha har
  have hm : max (ε1 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1)))
      (ε2 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2))) ≤
        (ε1 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1))) *
        (ε2 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2))) := by
    apply max_le <;> nlinarith
  have hh := mul_le_mul_of_nonneg_left hm (uniformCapTwo_pos P H β).le
  rw [←mul_assoc] at hh
  exact (h.parameter_le_uniform_two hf hH hβ hβ1 hholder ha har le_rfl).trans hh

/-- The source update intervals bound total trials by successful trials and the two logs. -/
theorem Run.iterations_le_two {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β flow : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    (hlow : ∀ x, flow ≤ f x) {ε1 ε2 : ℝ} {D : Data E} {N : ℕ}
    (h : Run f P ε1 (some ε2) D N) :
    (N : ℝ) ≤ (f (D.point 0) - flow) / (decreaseCoefficientTwo P H β *
        min (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1)))
          (ε2 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 2)))) *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      (Real.log (uniformCapTwo P H β / P.sigmaInitial) +
        (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε1| +
        (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 2) * |Real.log ε2|) /
          Real.log P.gamma2 := by
  have ht := iteration_bound_of_parameter_upper
    (S := successful f P (some ε2) D) (fun _ hi => h.parameter_pos hi)
    P.gamma1_pos P.gamma1_lt P.gamma2_gt
    (h.parameter_le_product_two hf hH hβ hβ1 hholder ha har)
    (fun _ hi hs => h.successful_parameter_lower hi hs)
    (fun _ hi hu => h.unsuccessful_parameter_lower hi hu)
  rw [h.initial_parameter] at ht
  have he2 := (h.accuracy2 ε2 (by simp)).1
  have hl1 : Real.log ε1 = -|Real.log ε1| := by
    rw [abs_of_nonpos (Real.log_nonpos h.accuracy1_pos.le h.accuracy1_le),neg_neg]
  have hl2 : Real.log ε2 = -|Real.log ε2| := by
    rw [abs_of_nonpos (Real.log_nonpos he2.le (h.accuracy2 ε2 (by simp)).2.1),neg_neg]
  have hid : Real.log (uniformCapTwo P H β *
      ε1 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1)) *
      ε2 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2)) / P.sigmaInitial) =
      Real.log (uniformCapTwo P H β / P.sigmaInitial) +
        (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε1| +
        (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 2) * |Real.log ε2| := by
    rw [Real.log_div (mul_pos (mul_pos (uniformCapTwo_pos P H β)
      (Real.rpow_pos_of_pos h.accuracy1_pos _)) (Real.rpow_pos_of_pos he2 _)).ne'
        P.sigmaInitial_pos.ne',
      Real.log_mul (mul_pos (uniformCapTwo_pos P H β)
        (Real.rpow_pos_of_pos h.accuracy1_pos _)).ne' (Real.rpow_pos_of_pos he2 _).ne',
      Real.log_mul (uniformCapTwo_pos P H β).ne' (Real.rpow_pos_of_pos h.accuracy1_pos _).ne',
      Real.log_rpow h.accuracy1_pos,Real.log_rpow he2,
      Real.log_div (uniformCapTwo_pos P H β).ne' P.sigmaInitial_pos.ne',hl1,hl2]
    simp only [abs_neg,abs_abs]
    ring
  rw [hid] at ht
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right
      (h.successful_card_le_two hf hH hβ hβ1 hholder ha har hlow)
        (by positivity [Real.log_pos P.gamma2_gt])) le_rfl)
end UniversalRegularization
