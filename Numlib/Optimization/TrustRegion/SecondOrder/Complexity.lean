import Numlib.Optimization.TrustRegion.SecondOrder.Finite

/-!
# Second-order trust-region evaluation complexity

The exact source decrease coefficient yields a uniform objective budget on
successful trials. Actual radius updates then bound all trials. A consistent
execution terminates by contradiction with these finite prefix budgets.
-/

namespace SecondOrderTrustRegion
open Set EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The accuracy factor in the second-order trust-region complexity bound. -/
def secondOrderAccuracyFactor (ε₁ ε₂ : ℝ) : ℝ := min (ε₁ ^ 2 * ε₂) (ε₂ ^ 3)

/-- Factoring out the curvature tolerance leaves the square of the smaller tolerance. -/
theorem secondOrderAccuracyFactor_eq {ε₁ ε₂ : ℝ} (h₁ : 0 ≤ ε₁) (h₂ : 0 ≤ ε₂) :
    secondOrderAccuracyFactor ε₁ ε₂ = ε₂ * (min ε₁ ε₂) ^ 2 := by
  unfold secondOrderAccuracyFactor
  by_cases h : ε₁ ≤ ε₂
  · have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h₁ h 2) h₂
    have hh : ε₁ ^ 2 * ε₂ ≤ ε₂ ^ 3 := by nlinarith
    rw [min_eq_left h, min_eq_left hh]
    ring
  · have hh : ε₂ ≤ ε₁ := le_of_not_ge h
    have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h₂ hh 2) h₂
    have hp' : ε₂ ^ 3 ≤ ε₁ ^ 2 * ε₂ := by nlinarith
    rw [min_eq_right hh, min_eq_right hp']
    ring

/-- The reciprocal of the source's successful-iteration coefficient. -/
noncomputable def secondOrderDecreaseCoefficient (Δ₀ η₁ η₂ γ₁ H L : ℝ) : ℝ :=
  η₁ / 2 * min (1 / (1 + H)) ((secondOrderRadiusConstant Δ₀ η₂ γ₁ H L) ^ 2)

namespace Run
variable {f : E → ℝ} {x s sC sE u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ H L : ℝ} {N : ℕ}

/-- The printed decrease coefficient is positive and accuracy independent. -/
theorem secondOrderDecreaseCoefficient_pos
    (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hH : 1 ≤ H) (hL : 0 ≤ L) :
    0 < secondOrderDecreaseCoefficient (Δ 0) η₁ η₂ γ₁ H L := by
  have hk := (h.radiusConstant_mem_Ioo hH hL).1
  have hη := h.updates.eta1_pos
  unfold secondOrderDecreaseCoefficient
  positivity

/-- The Cauchy model decrease holds without choosing the gradient stopping branch. -/
theorem model_decrease_cauchy
    (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    {i : ℕ} (hi : i < N) :
    (1 / 2 : ℝ) * ‖gradient f (x i)‖ *
      min (‖gradient f (x i)‖ / (1 + ‖hessian f (x i)‖)) (Δ i) ≤
        TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) (s i) := by
  have hh := QuadraticTrustRegion.cauchy_decrease (h.updates.pos (show i ≤ N by omega)).le
    ((isCauchyPoint_iff f (x i) (Δ i) (sC i)).mp (h.cauchy i hi))
  simp only [model_eq_taylor] at hh
  linarith [h.model_cauchy i hi]

/-- Each nonterminal model achieves the printed uniform second-order decrease.
Only the second tolerance is required to be at most one. -/
theorem model_decrease
    (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L) (hε₂ : ε₂ ≤ 1)
    (hbound : ∀ y, ‖hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) :
    (1 / 2 : ℝ) * min (1 / (1 + H))
      ((secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L) ^ 2) * secondOrderAccuracyFactor ε₁ ε₂ ≤
        TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) (s i) := by
  let a := min ε₁ ε₂
  let k := secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L
  let c := min (1 / (1 + H)) (k ^ 2)
  have ha : 0 ≤ a := le_min h.accuracy_first_pos.le h.accuracy_second_pos.le
  have hk0 : 0 < k := (h.radiusConstant_mem_Ioo hH hL.le).1
  have hk1 : k < 1 := (h.radiusConstant_mem_Ioo hH hL.le).2
  have hc0 : 0 ≤ c := le_min (by positivity) (sq_nonneg k)
  have hcA : c ≤ 1 / (1 + H) := min_le_left _ _
  have hck : c ≤ k ^ 2 := min_le_right _ _
  have hck' : c ≤ k := hck.trans (by nlinarith)
  have hr : k * a ≤ Δ i := h.radius_lower hf hH hL hε₂ hbound hlip (by omega)
  rw [secondOrderAccuracyFactor_eq h.accuracy_first_pos.le h.accuracy_second_pos.le]
  change (1 / 2 : ℝ) * c * (ε₂ * a ^ 2) ≤ _
  rcases h.not_terminated i hi with hg | hc
  · have hga : a ≤ ‖gradient f (x i)‖ := (min_le_left ε₁ ε₂).trans hg.le
    have hfirst : c * a ≤ ‖gradient f (x i)‖ / (1 + ‖hessian f (x i)‖) := by
      calc
        _ ≤ (1 / (1 + H)) * a := mul_le_mul_of_nonneg_right hcA ha
        _ = a / (1 + H) := by ring
        _ ≤ ‖gradient f (x i)‖ / (1 + H) :=
          div_le_div_of_nonneg_right hga (by linarith)
        _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (by linarith [hbound (x i)])
    have hsecond : c * a ≤ Δ i :=
      (mul_le_mul_of_nonneg_right hck' ha).trans hr
    have hh := mul_le_mul_of_nonneg_left (le_min hfirst hsecond)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg (gradient f (x i))))
    have hprod := mul_le_mul_of_nonneg_right hga (mul_nonneg hc0 ha)
    have heps := mul_le_mul_of_nonneg_right hε₂ (mul_nonneg hc0 (sq_nonneg a))
    nlinarith [hh.trans (h.model_decrease_cauchy hi)]
  · have hm : μ i < 0 := by linarith [h.accuracy_second_pos]
    have hp := h.eigenpoint i hi
    rw [ite_eq_left hm] at hp
    have hd := TaylorModel.eigenpoint_decrease f (x i) (u i)
      (h.updates.pos (show i ≤ N by omega)).le hm
      (h.least_eigenpair i (by omega)).unit (h.least_eigenpair i (by omega)).eigenvector
      (h.eigenvector_sign i hi) hp
    have habs : ε₂ ≤ |μ i| := by rw [abs_of_neg hm]; linarith
    have hpow : (k * a) ^ 2 ≤ (Δ i) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hk0.le ha) hr 2
    have hcscale := mul_le_mul_of_nonneg_right hck (mul_nonneg h.accuracy_second_pos.le
      (sq_nonneg a))
    have hscale := mul_le_mul hpow habs h.accuracy_second_pos.le (sq_nonneg _)
    nlinarith [h.model_eigen i hi]

/-- Success converts the uniform model decrease into an actual objective decrease. -/
theorem successful_decrease
    (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L) (hε₂ : ε₂ ≤ 1)
    (hbound : ∀ y, ‖hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) :
    secondOrderDecreaseCoefficient (Δ 0) η₁ η₂ γ₁ H L * secondOrderAccuracyFactor ε₁ ε₂ ≤
      f (x i) - f (x (i + 1)) := by
  have hh := (le_div_iff₀ (h.denominator_pos hf hi)).mp ((h.ratio i hi) ▸ hs)
  have hd := mul_le_mul_of_nonneg_left (h.model_decrease hf hH hL hε₂ hbound hlip hi)
    h.updates.eta1_pos.le
  rw [h.step i hi, ite_eq_left hs]
  unfold secondOrderDecreaseCoefficient
  nlinarith

/-- The initial objective gap bounds all successful trials before termination. -/
theorem successful_card_le
    (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L) (hε₂ : ε₂ ≤ 1)
    (hbound : ∀ y, ‖hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {flow : ℝ} (hlow : flow ≤ f (x N)) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤ (f (x 0) - flow) /
      (secondOrderDecreaseCoefficient (Δ 0) η₁ η₂ γ₁ H L *
        secondOrderAccuracyFactor ε₁ ε₂) := by
  have hc := h.secondOrderDecreaseCoefficient_pos hH hL.le
  have ha : 0 < secondOrderAccuracyFactor ε₁ ε₂ := by
    unfold secondOrderAccuracyFactor
    have h₁ := h.accuracy_first_pos
    have h₂ := h.accuracy_second_pos
    positivity
  exact card_successful_le_gap_div (S := {i | η₁ ≤ ρ i}) (f := fun i => f (x i))
    (mul_pos hc ha) hlow
    (fun i hi hs => h.successful_decrease hf hH hL hε₂ hbound hlip hi hs)
    (fun i hi hu => by
      change ¬η₁ ≤ ρ i at hu
      rw [h.step i hi, ite_eq_right hu])

/-- Every nonterminal prefix has the complete finite trial bound, with all
constants fixed independently of both requested accuracies. -/
theorem iterations_le
    (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L) (hε₂ : ε₂ ≤ 1)
    (hbound : ∀ y, ‖hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {flow : ℝ} (hlow : flow ≤ f (x N)) :
    (N : ℝ) ≤ (f (x 0) - flow) /
      (secondOrderDecreaseCoefficient (Δ 0) η₁ η₂ γ₁ H L * secondOrderAccuracyFactor ε₁ ε₂) *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      (|Real.log (secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L / Δ 0)| +
        |Real.log (min ε₁ ε₂)|) / |Real.log γ₂| := by
  have hk := (h.radiusConstant_mem_Ioo hH hL.le).1
  have ha := lt_min h.accuracy_first_pos h.accuracy_second_pos
  have ht := iteration_bound_of_parameter_lower
    (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.updates.pos hi)
    (by linarith [h.updates.one_lt_gamma3])
    (h.updates.gamma1_pos.trans_le h.updates.gamma1_le_gamma2)
    h.updates.gamma2_lt_one (h.radius_lower hf hH hL hε₂ hbound hlip le_rfl)
    (mul_pos hk ha) (fun _ hi hs => h.updates.successful_le hi hs)
    (fun _ hi hu => h.updates.unsuccessful_le hi hu)
  have hA : 0 ≤ 1 + Real.log γ₃ / |Real.log γ₂| := by
    have hg3 := Real.log_pos h.updates.one_lt_gamma3
    positivity
  have hl : |Real.log (secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L * min ε₁ ε₂ / Δ 0)| ≤
      |Real.log (secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L / Δ 0)| +
        |Real.log (min ε₁ ε₂)| := by
    have he : secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L * min ε₁ ε₂ / Δ 0 =
        (secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L / Δ 0) * min ε₁ ε₂ := by ring
    rw [he, Real.log_mul (div_pos hk h.updates.initial_pos).ne' ha.ne']
    exact abs_add_le _ _
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.successful_card_le hf hH hL hε₂ hbound hlip hlow) hA)
    (div_le_div_of_nonneg_right hl (abs_nonneg _)))
end Run

/-- A consistent actual finite-tolerance execution terminates with both tests.
The stopping index is the first one satisfying them. -/
theorem exists_termination {f : E → ℝ} {x s sC sE u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ H L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂) →
      Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L) (hε₂ : ε₂ ≤ 1)
    (hbound : ∀ y, ‖hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, ‖gradient f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K ∧
      Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ K ∧
      ∀ i < K, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂ := by
  have hex : ∃ K, ‖gradient f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K := by
    by_contra hn
    push Not at hn
    have hnon : ∀ i, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂ := by
      intro i
      by_cases hg : ε₁ < ‖gradient f (x i)‖
      · exact Or.inl hg
      · exact Or.inr (hn i (le_of_not_gt hg))
    let bound := (f (x 0) - flow) /
      (secondOrderDecreaseCoefficient (Δ 0) η₁ η₂ γ₁ H L * secondOrderAccuracyFactor ε₁ ε₂) *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      (|Real.log (secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L / Δ 0)| +
        |Real.log (min ε₁ ε₂)|) / |Real.log γ₂|
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hnon i)).iterations_le hf hH hL hε₂ hbound hlip (hlow _)
    exact (not_le_of_gt hN) hb
  have hnon : ∀ i < Nat.find hex, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂ := by
    intro i hi
    have hh := Nat.find_min hex hi
    by_cases hg : ε₁ < ‖gradient f (x i)‖
    · exact Or.inl hg
    · exact Or.inr (lt_of_not_ge (fun hc => hh ⟨le_of_not_gt hg, hc⟩))
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    hprefix _ hnon, hnon⟩
end SecondOrderTrustRegion
