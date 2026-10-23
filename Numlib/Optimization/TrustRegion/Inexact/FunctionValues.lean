import Numlib.Optimization.TrustRegion.Inexact.Acceptance

/-!
# Trust-region acceptance with inexact objective values

The computed model decrement is independent of its constant tensor. Relative
errors in both objective values consume part of the acceptance margin; the
remaining part is supplied by the actual Taylor and derivative error bounds.
-/

namespace InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SelectedTrials
variable {q : ℕ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {j : ℕ → Fin q} {Δ : ℕ → ℝ} {d s : ℕ → E} {ε : Fin q → ℝ} {ζ θ : ℝ}

/-- A small radius controls the true decrease error by half the specified margin.
No exact or approximate constant coefficient is required. -/
theorem objective_error_le_margin (h : SelectedTrials A T j Δ d s ε ζ θ)
    {f : E → ℝ} (hf : ContDiff ℝ q f) {L K τ : ℝ}
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (x : ℕ → E) {i : ℕ} (hi : i ∈ T)
    (herr : ∀ a, 1 ≤ a → a ≤ modelOrder (j i) →
      ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ K * ‖s i‖ ^ (q - a + 1))
    (hsmall : Δ i ≤ min θ (τ / acceptanceCoefficient q L K * scaledGap A j Δ d θ i)) :
    |(f (x i) - f (x i + s i)) - decrement (A i) (modelOrder (j i)) (s i)| ≤
      τ / 2 * decrement (A i) (modelOrder (j i)) (s i) := by
  have hjq : modelOrder (j i) ≤ q := (j i).isLt
  have hj : 0 < modelOrder (j i) := by simp [modelOrder]
  have hcap : Δ i ≤ θ := hsmall.trans (min_le_left _ _)
  have hδ : optimalityRadius θ (Δ i) = Δ i := min_eq_right hcap
  have hsnorm : ‖s i‖ ≤ 1 := (h.step_feasible i hi).trans (hcap.trans h.cap_le_one)
  have hcoef : 0 < acceptanceCoefficient q L K := by
    dsimp [acceptanceCoefficient]
    positivity
  have hmodel := h.model_decrease hi
  rw [hδ] at hmodel
  have hfac : (0 : ℝ) < (modelOrder (j i)).factorial := by positivity
  have hsmall' : acceptanceCoefficient q L K * Δ i ≤ τ * scaledGap A j Δ d θ i := by
    have hh : Δ i ≤ (τ * scaledGap A j Δ d θ i) / acceptanceCoefficient q L K := by
      convert hsmall.trans (min_le_right _ _) using 1; ring
    simpa only [mul_comm] using (le_div_iff₀ hcoef).mp hh
  have he := objective_decrement_error_le hj hjq hf hL hK hlip (A i) (x i) (s i)
    hsnorm herr
  calc _ ≤ (acceptanceCoefficient q L K / 2) * ‖s i‖ ^ (modelOrder (j i) + 1) /
        (modelOrder (j i)).factorial := he
    _ ≤ (acceptanceCoefficient q L K / 2) * Δ i ^ (modelOrder (j i) + 1) /
        (modelOrder (j i)).factorial := by gcongr; exact h.step_feasible i hi
    _ = (acceptanceCoefficient q L K * Δ i / 2) * Δ i ^ modelOrder (j i) /
        (modelOrder (j i)).factorial := by rw [pow_succ]; ring
    _ ≤ (τ * scaledGap A j Δ d θ i / 2) * Δ i ^ modelOrder (j i) /
        (modelOrder (j i)).factorial :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hsmall' (by norm_num))
          (pow_nonneg (h.radius_pos i hi).le _)) hfac.le
    _ = τ / 2 * (scaledGap A j Δ d θ i * Δ i ^ modelOrder (j i) /
        (modelOrder (j i)).factorial) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmodel (div_nonneg hτ (by norm_num))

/-- Relative errors in both objective values preserve very successful acceptance
when they use at most one quarter of the margin each. -/
theorem very_successful_inexact_values (h : SelectedTrials A T j Δ d s ε ζ θ)
    {f : E → ℝ} (hf : ContDiff ℝ q f) {L K η₂ : ℝ}
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hη : η₂ < 1) (hKsmall : K ≤ (1 - η₂) / 4)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (x : ℕ → E) {i : ℕ} (hi : i ∈ T)
    (herr : ∀ a, 1 ≤ a → a ≤ modelOrder (j i) →
      ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ K * ‖s i‖ ^ (q - a + 1))
    (hsmall : Δ i ≤ min θ ((1 - η₂) / acceptanceCoefficient q L K *
      scaledGap A j Δ d θ i))
    (F₀ F₁ : ℝ)
    (hF₀ : |F₀ - f (x i)| ≤ K * decrement (A i) (modelOrder (j i)) (s i))
    (hF₁ : |F₁ - f (x i + s i)| ≤ K * decrement (A i) (modelOrder (j i)) (s i)) :
    η₂ ≤ (F₀ - F₁) / decrement (A i) (modelOrder (j i)) (s i) := by
  have hgap : 0 < scaledGap A j Δ d θ i :=
    (mul_pos (div_pos h.zeta_pos (by norm_num))
      (minimumAccuracy_pos h.order_pos h.accuracy_pos)).trans_le (h.scaledGap_lower hi)
  have hmodel := h.model_decrease hi
  have hδ := h.optimalityRadius_pos hi
  have hdenom : 0 < decrement (A i) (modelOrder (j i)) (s i) :=
    (div_pos (mul_pos hgap (pow_pos hδ _)) (by positivity)).trans_le hmodel
  have he := h.objective_error_le_margin hf hL hK (by linarith : 0 ≤ 1 - η₂)
    hlip x hi herr hsmall
  have he' := (neg_le_abs ((f (x i) - f (x i + s i)) -
    decrement (A i) (modelOrder (j i)) (s i))).trans he
  have h0 := (neg_le_abs (F₀ - f (x i))).trans hF₀
  have h1 := (le_abs_self (F₁ - f (x i + s i))).trans hF₁
  apply (le_div_iff₀ hdenom).mpr
  have hKm := mul_le_mul_of_nonneg_right hKsmall hdenom.le
  nlinarith

end SelectedTrials

omit [NormedSpace ℝ E] in
/-- Accepted computed objective ratios yield true decrease after accounting for
both relative objective errors. -/
theorem true_decrease_of_inexact_values {f : E → ℝ} {x s : E} {D K η : ℝ}
    (hD : 0 < D) (hK : K ≤ η / 4) (F₀ F₁ : ℝ)
    (hF₀ : |F₀ - f x| ≤ K * D) (hF₁ : |F₁ - f (x + s)| ≤ K * D)
    (haccept : η ≤ (F₀ - F₁) / D) : η / 2 * D ≤ f x - f (x + s) := by
  have h0 := (le_abs_self (F₀ - f x)).trans hF₀
  have h1 := (neg_le_abs (F₁ - f (x + s))).trans hF₁
  have ha := (le_div_iff₀ hD).mp haccept
  have hKm := mul_le_mul_of_nonneg_right hK hD.le
  nlinarith

end InexactTrustRegion
