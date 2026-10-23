import Numlib.Optimization.TrustRegion.Inexact.FunctionValues
import Numlib.Optimization.TrustRegion.Inexact.Radius

/-!
# Radius floors with explicit dynamic objective accuracy

Both approximate objective evaluations and the actual computed acceptance ratio
are primitive data. The known unit tensor oracle and relative requests yield
small-radius acceptance and the same operational radius floor as in the IDA case.
-/

namespace InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The EDA computed model, derivative requests, approximate function values,
actual computed ratios and permitted radius updates. No radius floor is a field. -/
structure FunctionModelTrace {q : ℕ} (f : E → ℝ)
    (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ) (j : ℕ → Fin q)
    (x d s : ℕ → E) (Δ ρ F₀ F₁ h₀ : ℕ → ℝ) (ε : Fin q → ℝ)
    (accuracy : ℕ → ℕ → ℝ) (ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax : ℝ)
      (N : ℕ) : Prop
    extends SelectedTrials A T j Δ d s ε ζ θ where
  updates : EvaluationComplexity.TrialTrustRegionUpdates T Δ ρ η₁ η₂ γ₁ γ₂
    γ₃ Δmax N
  initial_cap : θ ≤ Δ 0
  cap_accuracy : minimumAccuracy order_pos ε ≤ θ
  request_factor_nonneg : 0 ≤ κs
  request_factor_small : κs ≤ (1 - η₂) / 4
  oracle : ∀ i < N, i ∈ T → ∀ a, 1 ≤ a → a ≤ q →
    ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ accuracy i a
  requests : ∀ i < N, i ∈ T → ∀ a, 1 ≤ a → a ≤ q →
    accuracy i a ≤ κs * ‖s i‖ ^ (q - a + 1)
  request_positive : ∀ i < N, i ∈ T → 0 < h₀ i
  relative_request : ∀ i < N, i ∈ T →
    h₀ i ≤ κs * decrement (A i) (modelOrder (j i)) (s i)
  error_initial : ∀ i < N, i ∈ T → |F₀ i - f (x i)| ≤ h₀ i
  error_trial : ∀ i < N, i ∈ T → |F₁ i - f (x i + s i)| ≤ h₀ i
  ratio : ∀ i < N, i ∈ T →
    ρ i = (F₀ i - F₁ i) / decrement (A i) (modelOrder (j i)) (s i)

namespace FunctionModelTrace
variable {q : ℕ} {f : E → ℝ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → E} {Δ ρ F₀ F₁ h₀ : ℕ → ℝ}
  {ε : Fin q → ℝ} {accuracy : ℕ → ℕ → ℝ}
  {ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax L : ℝ} {N : ℕ}

/-- Actual tensor errors follow from the known unit oracle and requested accuracies. -/
theorem tensor_error (h : FunctionModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
    ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N) {i : ℕ} (hi : i < N) (hT : i ∈ T)
    {a : ℕ} (ha : 1 ≤ a) (haq : a ≤ q) :
    ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ κs * ‖s i‖ ^ (q - a + 1) :=
  (h.oracle i hi hT a ha haq).trans (h.requests i hi hT a ha haq)

/-- Actual approximate objective errors preserve very successful small trials. -/
theorem very_successful (h : FunctionModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
    ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N) (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i : ℕ} (hi : i < N) (hT : i ∈ T)
    (hsmall : Δ i ≤ min θ ((1 - η₂) / acceptanceCoefficient q L κs *
      scaledGap A j Δ d θ i)) : η₂ ≤ ρ i := by
  rw [h.ratio i hi hT]
  exact h.toSelectedTrials.very_successful_inexact_values hf hL h.request_factor_nonneg
    h.updates.eta2_lt_one h.request_factor_small hlip x hT
    (fun a ha haj => h.tensor_error hi hT ha (haj.trans (j i).isLt)) hsmall (F₀ i) (F₁ i)
    ((h.error_initial i hi hT).trans (h.relative_request i hi hT))
    ((h.error_trial i hi hT).trans (h.relative_request i hi hT))

/-- Any admissible coefficient gives the EDA optimality-radius floor using the
actual computed-ratio update rules, including unchanged accuracy-only iterations. -/
theorem optimalityRadius_lower
    (h : FunctionModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
      ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {κ : ℝ} (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L κs))
    {k : ℕ} (hk : k ≤ N) :
    ζ * (κ / 2) * minimumAccuracy h.order_pos ε ≤ optimalityRadius θ (Δ k) := by
  have hκs0 := h.request_factor_nonneg
  have hC : 1 ≤ acceptanceCoefficient q L κs := by
    have hh : 0 ≤ 4 * ((q + 1).factorial : ℝ) * κs := by positivity
    dsimp [acceptanceCoefficient]
    linarith
  have hη0 : 0 ≤ η₂ := h.updates.eta1_pos.le.trans h.updates.eta1_le_eta2
  have hc : (1 - η₂) / acceptanceCoefficient q L κs ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hκγ : κ ≤ γ₁ := hκ.trans (mul_le_of_le_one_right h.updates.gamma1_pos.le hc)
  have hμ := minimumAccuracy_pos h.order_pos h.accuracy_pos
  have hγ1 : γ₁ ≤ 1 := h.updates.gamma1_le_gamma2.trans h.updates.gamma2_lt_one.le
  have hsmall : ζ * (κ / 2) * minimumAccuracy h.order_pos ε ≤ γ₁ * θ := by
    calc _ = κ * (ζ / 2 * minimumAccuracy h.order_pos ε) := by ring
      _ ≤ γ₁ * minimumAccuracy h.order_pos ε := by
        apply mul_le_mul hκγ _
          (mul_nonneg (div_nonneg h.zeta_pos.le (by norm_num)) hμ.le)
          h.updates.gamma1_pos.le
        nlinarith [h.zeta_le_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left h.cap_accuracy h.updates.gamma1_pos.le
  apply le_min
  · exact hsmall.trans (mul_le_of_le_one_left h.cap_pos.le hγ1)
  · have hrad := h.updates.min_cap_scaled_gap_le h.cap_pos.le h.initial_cap
      (div_nonneg (by linarith [h.updates.eta2_lt_one]) (by linarith : 0 ≤
        acceptanceCoefficient q L κs)) hκ
      (mul_nonneg (div_nonneg h.zeta_pos.le (by norm_num)) hμ.le)
      (scaledGap A j Δ d θ)
      (fun i _ hi => h.toSelectedTrials.scaledGap_lower hi)
      (fun i hi hT hh => h.very_successful hf hL hlip hi hT hh) hk
    have heq : κ * (ζ / 2 * minimumAccuracy h.order_pos ε) =
        ζ * (κ / 2) * minimumAccuracy h.order_pos ε := by ring
    rw [heq, min_eq_right hsmall] at hrad
    exact hrad

end FunctionModelTrace
end InexactTrustRegion
