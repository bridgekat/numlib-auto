import Numlib.Optimization.TrustRegion.Inexact.Decrease
import Numlib.Optimization.TrustRegion.Inexact.Radius
import Numlib.Optimization.Regularization.Inexact.ModelDecrease

/-!
# Operational consequences of inexact trust-region radius floors

Actual point updates extend the model and oracle trace. The proved radius floor
then yields both computed model decrease and true decrease on accepted steps.
-/

namespace InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The model/oracle/radius trace together with actual accepted, rejected and
accuracy-only point updates. No decrease or radius floor is a field. -/
structure ExecutionTrace {q : ℕ} (f : E → ℝ)
    (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ) (j : ℕ → Fin q)
    (x d s : ℕ → E) (Δ ρ : ℕ → ℝ) (ε : Fin q → ℝ) (accuracy : ℕ → ℕ → ℝ)
    (ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax : ℝ) (N : ℕ) : Prop
    extends ModelTrace f A T j x d s Δ ρ ε accuracy
      ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N where
  point_trial : ∀ i < N, i ∈ T → x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i
  point_inactive : ∀ i < N, i ∉ T → x (i + 1) = x i

namespace SelectedTrials
variable {q : ℕ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {j : ℕ → Fin q} {Δ : ℕ → ℝ} {d s : ℕ → E} {ε : Fin q → ℝ} {ζ θ : ℝ}

/-- The selected strict failure and actual comparison make the acceptance
ratio denominator strictly positive. -/
theorem denominator_pos (h : SelectedTrials A T j Δ d s ε ζ θ) {i : ℕ} (hi : i ∈ T) :
    0 < decrement (A i) (modelOrder (j i)) (s i) := by
  have hh := h.failed_test i hi
  have hδ := h.optimalityRadius_pos hi
  have hζ := h.zeta_pos
  have hε := h.accuracy_pos (j i)
  have hp : 0 < ζ / 2 * ε (j i) * optimalityRadius θ (Δ i) ^ modelOrder (j i) /
      (modelOrder (j i)).factorial := by positivity
  have hm := sub_le_sub_left (h.model_comparison i hi)
    (TaylorModel.ofJet (A i) (modelOrder (j i)) 0)
  exact (hp.trans hh).trans_le hm

end SelectedTrials
namespace ModelTrace
variable {q : ℕ} {f : E → ℝ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → E} {Δ ρ : ℕ → ℝ} {ε : Fin q → ℝ}
  {ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax L κ : ℝ} {N : ℕ}
  {accuracy : ℕ → ℕ → ℝ}

/-- An admissible radius coefficient is at most one under the actual
acceptance and update parameter restrictions. -/
theorem radiusCoefficient_le_one (h : ModelTrace f A T j x d s Δ ρ ε accuracy
    ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N) (hL : 1 ≤ L)
    (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L (κs * κmax))) : κ ≤ 1 := by
  have hC : 1 ≤ acceptanceCoefficient q L (κs * κmax) := by
    have hprod := mul_nonneg h.request_factor_nonneg h.oracle_constant_nonneg
    dsimp [acceptanceCoefficient]
    have hh : 0 ≤ 4 * ((q + 1).factorial : ℝ) * (κs * κmax) := by positivity
    linarith
  have hη0 : 0 ≤ η₂ := h.updates.eta1_pos.le.trans h.updates.eta1_le_eta2
  have hc : (1 - η₂) / acceptanceCoefficient q L (κs * κmax) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  exact hκ.trans ((mul_le_of_le_one_right h.updates.gamma1_pos.le hc).trans
    (h.updates.gamma1_le_gamma2.trans h.updates.gamma2_lt_one.le))

/-- The actual computed model decrease follows from the derived radius floor,
for every admissible fixed radius coefficient. -/
theorem model_decrease (h : ModelTrace f A T j x d s Δ ρ ε accuracy
    ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L (κs * κmax)))
    {i : ℕ} (hi : i ≤ N) (hT : i ∈ T) :
    (ζ * (κ / 2)) ^ (q + 1) / q.factorial * minimumAccuracy h.order_pos ε ^ (q + 1) ≤
      decrement (A i) (modelOrder (j i)) (s i) :=
  h.toSelectedTrials.decrease_of_radius_floor (by positivity) (by linarith) hT
    (h.optimalityRadius_lower hf hL hlip hκ hi)

end ModelTrace
namespace ExecutionTrace
variable {q : ℕ} {f : E → ℝ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → E} {Δ ρ : ℕ → ℝ} {ε : Fin q → ℝ}
  {ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax L κ : ℝ} {N : ℕ}
  {accuracy : ℕ → ℕ → ℝ}

/-- Accepted actual trials give at least half the exact-ratio model decrease,
as in the source bound that is shared with the EDA variant. -/
theorem function_decrease (h : ExecutionTrace f A T j x d s Δ ρ ε accuracy
    ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L (κs * κmax)))
    {i : ℕ} (hi : i < N) (hT : i ∈ T) (haccept : η₁ ≤ ρ i) :
    η₁ * (ζ * (κ / 2)) ^ (q + 1) / (2 * (q.factorial : ℝ)) *
      minimumAccuracy h.order_pos ε ^ (q + 1) ≤ f (x i) - f (x (i + 1)) := by
  have hd := h.toModelTrace.model_decrease hf hL hlip hκ0 hκ1 hκ hi.le hT
  have hden := h.toSelectedTrials.denominator_pos hT
  have ha := haccept
  rw [h.ratio i hi hT] at ha
  have hh := (le_div_iff₀ hden).1 ha
  rw [h.point_trial i hi hT, ite_eq_left haccept]
  have hm := mul_le_mul_of_nonneg_left hd h.updates.eta1_pos.le
  have hp : 0 ≤ η₁ * ((ζ * (κ / 2)) ^ (q + 1) / q.factorial *
      minimumAccuracy h.order_pos ε ^ (q + 1)) := by
    have hμ := (minimumAccuracy_pos h.order_pos h.accuracy_pos).le
    have hη := h.updates.eta1_pos
    have hζ := h.zeta_pos
    positivity
  have heq : η₁ * (ζ * (κ / 2)) ^ (q + 1) / (2 * (q.factorial : ℝ)) *
      minimumAccuracy h.order_pos ε ^ (q + 1) =
      (η₁ * ((ζ * (κ / 2)) ^ (q + 1) / q.factorial *
        minimumAccuracy h.order_pos ε ^ (q + 1))) / 2 := by ring
  rw [heq]
  linarith

end ExecutionTrace
end InexactTrustRegion
