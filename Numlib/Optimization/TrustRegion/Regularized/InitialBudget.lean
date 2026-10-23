import Numlib.Optimization.TrustRegion.Regularized.SecondOrder

/-!
# Initialized finite-second-order objective budgets

Retaining the initial potential credit removes the startup success allowance
when the initial gradient test passes. Otherwise a positive objective gap chosen
before both accuracies absorbs that allowance into the leading coefficient.
-/

namespace RegularizedTrustRegion
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Run
variable {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}

/-- If the initial gradient test passes, its potential credit removes the
startup success allowance from the finite-second-order objective budget. -/
theorem secondOrder_successful_card_le_of_initial_gradient
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hfinite : ε₂ = (ε : WithTop ℝ)) (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y)
    (hinit : ‖gradient f (x 0)‖ ≤ ε₁) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      2 * (f (x 0) - flow) /
        (decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε) := by
  classical
  let d := decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε
  have hc := decreaseCoefficient_pos h.updates.eta1_pos h.updates.eta2_lt_one
    h.updates.gamma1_pos (zero_lt_one.trans_le hL) h.theta_pos.le
  have hd : 0 < d := mul_pos hc (secondOrderScale_pos h.first_accuracy_pos h.regularization_pos)
  have hlo : flow - d / 2 ≤ creditPotential f ε₁ d (x N) :=
    (sub_le_sub_right (hlow _) _).trans (creditPotential_bounds f ε₁ hd.le (x N)).1
  have hh := card_successful_le_gap_div
    (S := {i | η₁ ≤ ρ i}) (f := fun i => creditPotential f ε₁ d (x i))
    (show 0 < d / 2 by positivity) hlo
    (fun i hi ha => h.successful_credit_decrease hfinite hf hL hlip hi ha)
    (fun i hi ha => by rw [h.rejected_point hi ha])
  have heq : (creditPotential f ε₁ d (x 0) - (flow - d / 2)) / (d / 2) =
      2 * (f (x 0) - flow) / d := by
    unfold creditPotential
    rw [ite_eq_left hinit]
    field_simp
    ring
  simpa only [heq, d] using hh

/-- A fixed positive objective gap absorbs the startup success when the initial
gradient test fails. The resulting coefficient is independent of both accuracies. -/
theorem secondOrder_successful_card_le_with_gap
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hfinite : ε₂ = (ε : WithTop ℝ)) (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow δ : ℝ} (hlow : ∀ y, flow ≤ f y)
    (hδ : 0 < δ) (hgap : gradient f (x 0) ≠ 0 → δ ≤ f (x 0) - flow)
    (hε : ε ≤ 1) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      (2 / decreaseCoefficient η₁ η₂ γ₁ L θ + 1 / δ) *
        (f (x 0) - flow) / secondOrderScale ε₁ ε := by
  let c := decreaseCoefficient η₁ η₂ γ₁ L θ
  let a := secondOrderScale ε₁ ε
  have hc : 0 < c := decreaseCoefficient_pos h.updates.eta1_pos h.updates.eta2_lt_one
    h.updates.gamma1_pos (zero_lt_one.trans_le hL) h.theta_pos.le
  have ha : 0 < a := secondOrderScale_pos h.first_accuracy_pos h.regularization_pos
  have ha1 : a ≤ 1 := (min_le_left _ _).trans
    (pow_le_one₀ h.regularization_pos.le hε)
  have hnonneg : 0 ≤ (1 / δ) * (f (x 0) - flow) / a := by
    exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (hlow _))) ha.le
  by_cases hinit : ‖gradient f (x 0)‖ ≤ ε₁
  · have hb := h.secondOrder_successful_card_le_of_initial_gradient hfinite hf hL hlip
      hlow hinit
    calc
      _ ≤ 2 * (f (x 0) - flow) / (c * a) := hb
      _ ≤ 2 * (f (x 0) - flow) / (c * a) + (1 / δ) * (f (x 0) - flow) / a :=
        le_add_of_nonneg_right hnonneg
      _ = _ := by dsimp [c, a]; ring
  · have hgz : gradient f (x 0) ≠ 0 := by
      intro hz
      apply hinit
      simpa only [hz, norm_zero] using h.first_accuracy_pos.le
    have hδgap := hgap hgz
    have hδa : δ * a ≤ f (x 0) - flow :=
      (mul_le_of_le_one_right hδ.le ha1).trans hδgap
    have hpay : 1 ≤ (1 / δ) * (f (x 0) - flow) / a := by
      apply (le_div_iff₀ ha).mpr
      have hh := (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hδa)
      calc
        1 * a = a := one_mul _
        _ ≤ (f (x 0) - flow) / δ := hh
        _ = (1 / δ) * (f (x 0) - flow) := by ring
    have hb := h.secondOrder_successful_card_le hfinite hf hL hlip hlow
    calc
      _ ≤ 2 * (f (x 0) - flow) / (c * a) + 1 := hb
      _ ≤ 2 * (f (x 0) - flow) / (c * a) + (1 / δ) * (f (x 0) - flow) / a :=
        add_le_add_right hpay _
      _ = _ := by dsimp [c, a]; ring

end Run
end RegularizedTrustRegion
