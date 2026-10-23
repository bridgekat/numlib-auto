import Numlib.Optimization.TrustRegion.Inexact.FunctionRadius
import Numlib.Optimization.TrustRegion.Inexact.RadiusConsequences
/-!
# True decreases with explicit dynamic accuracy

Actual computed ratios and two separate objective error requests preserve half
of the accepted computed model decrease. The operational EDA radius floor then
gives the same fixed computed and objective decrease bounds as the IDA method.
-/

namespace InexactTrustRegion.FunctionModelTrace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {q : ℕ} {f : E → ℝ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → E} {Δ ρ F₀ F₁ h₀ : ℕ → ℝ}
  {ε : Fin q → ℝ} {accuracy : ℕ → ℕ → ℝ}
  {ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax L κ : ℝ} {N : ℕ}
/-- Every admissible fixed radius coefficient is at most one under the primitive update rules. -/
theorem radiusCoefficient_le_one
    (h : FunctionModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
      ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N) (hL : 1 ≤ L)
    (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L κs)) : κ ≤ 1 := by
  have hC : 1 ≤ acceptanceCoefficient q L κs := by
    have hh : 0 ≤ 4 * ((q + 1).factorial : ℝ) * κs := by
      have := h.request_factor_nonneg
      positivity
    dsimp [acceptanceCoefficient]
    linarith
  have hη : 0 ≤ η₂ := h.updates.eta1_pos.le.trans h.updates.eta1_le_eta2
  have hc : (1 - η₂) / acceptanceCoefficient q L κs ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  exact hκ.trans ((mul_le_of_le_one_right h.updates.gamma1_pos.le hc).trans
    (h.updates.gamma1_le_gamma2.trans h.updates.gamma2_lt_one.le))
/-- The actual computed Taylor decrement has the source uniform lower bound
from the operational EDA radius floor, including the initial endpoint. -/
theorem model_decrease
    (h : FunctionModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
      ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L κs))
    {i : ℕ} (hi : i ≤ N) (hT : i ∈ T) :
    (ζ * (κ / 2)) ^ (q + 1) / q.factorial * minimumAccuracy h.order_pos ε ^ (q + 1) ≤
      decrement (A i) (modelOrder (j i)) (s i) :=
  h.toSelectedTrials.decrease_of_radius_floor (by positivity)
    (by linarith [h.radiusCoefficient_le_one hL hκ]) hT
      (h.optimalityRadius_lower hf hL hlip hκ hi)
/-- Accepted actual inexact objective ratios imply the source true objective decrease
after accounting for both independently bounded objective evaluations. -/
theorem function_decrease
    (h : FunctionModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
      ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L κs))
    (hacceptMargin : κs ≤ η₁ / 4)
    (hpoint : ∀ i < N, i ∈ T → x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i)
    {i : ℕ} (hi : i < N) (hT : i ∈ T) (haccept : η₁ ≤ ρ i) :
    η₁ * (ζ * (κ / 2)) ^ (q + 1) / (2 * (q.factorial : ℝ)) *
      minimumAccuracy h.order_pos ε ^ (q + 1) ≤ f (x i) - f (x (i + 1)) := by
  have hd := h.model_decrease hf hL hlip hκ0 hκ hi.le hT
  have hh := true_decrease_of_inexact_values (h.toSelectedTrials.denominator_pos hT)
    hacceptMargin (F₀ i) (F₁ i)
    ((h.error_initial i hi hT).trans (h.relative_request i hi hT))
    ((h.error_trial i hi hT).trans (h.relative_request i hi hT))
    (by rwa [←h.ratio i hi hT])
  rw [hpoint i hi hT, ite_eq_left haccept]
  have hm := mul_le_mul_of_nonneg_left hd (half_pos h.updates.eta1_pos).le
  convert hm.trans hh using 1; ring
end InexactTrustRegion.FunctionModelTrace
