import Numlib.Optimization.Regularization.Convex.DerivativeBudget

/-!
# Corrected factorial decrease for constrained derivative tests

The true norm-power model penalty has coefficient `sigma/(p+1)!`. Every
permitted first-, second- and third-order model test transfers through its
actual tensor error to the matching strict objective reduction. Disabled
higher tests require no additional derivative order.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every enabled endpoint failure on its actual model-restricted direction
set yields the strict source decrease with the corrected `(p+1)!` factor. -/
theorem DerivativeRun.successful_decrease_of_model_endpoint_failure
    {p : ℕ} {q : Fin 3} {f : E → ℝ} {C S : Set E} {P : DerivativeSettings p q}
    {ε : Fin 3 → ℝ} {D : Data E} {N i : ℕ}
    (h : DerivativeRun f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hs : P.eta1 ≤ D.ratio i) (j : Fin 3) (hj : j ≤ q)
    (hfail : ε j < tensorCriticality (iteratedFDeriv ℝ (j.val + 1) f (D.point (i + 1)))
      (modelRestrictedDirections f p C (D.point i) (D.parameter i) (D.step i)
        (P.fractions 0 * ε 0) (P.fractions 1 * ε 1) j)) :
    derivativeDecreaseCoefficient P L j * ε j ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)) <
      f (D.point i) - f (D.point (i + 1)) := by
  have horder := P.enabled_order
  have hjq : j.val ≤ q.val := hj
  have hjp : j.val + 1 ≤ p := by omega
  have hm : 0 < p - j.val := by omega
  have hexp : p - (j.val + 1) + 1 = p - j.val := by omega
  have hcap := h.modelTrace.parameter_le_on hS hCS hC hf hL hlip
    (fun k hk => h.mem hk.le) h.feasible_trial hi.le
  rw [h.initial_parameter] at hcap
  change D.parameter i ≤ parameterCap P.toSettings L at hcap
  have hzero := zero_mem_modelRestrictedDirections (f := f) (p := p)
    (σ := D.parameter i) (h.feasible_trial i hi)
    (mul_nonneg (P.fractions_pos 0).le (h.accuracy_pos 0).le)
    (mul_nonneg (P.fractions_pos 1).le (h.accuracy_pos 1).le) j
  rw [h.modelTrace.successful_point hi hs] at hfail
  have ht := derivative_step_lower_of_model_test hjp hS hCS hC hf hL
    (h.modelTrace.updates.pos hi.le) hcap hlip (h.mem hi.le) (h.feasible_trial i hi)
    (h.modelTrace.step_ne_zero hi) hzero (h.model_test i hi j hj) hfail
  have ht' : derivativeStepThreshold P L j * ε j < ‖D.step i‖ ^ (p - j.val) := by
    simpa only [hexp, derivativeStepThreshold] using ht
  have hb := rpow_step_lower (n := p + 1) hm (derivativeStepThreshold_pos P hL j).le
    (h.accuracy_pos j).le (norm_nonneg (D.step i)) ht'.le
  have hcoeff : 0 ≤ P.eta1 * P.sigmaMin / (p + 1).factorial := by
    exact div_nonneg (mul_nonneg P.eta1_pos.le P.sigmaMin_pos.le) (Nat.cast_nonneg _)
  calc
    _ = P.eta1 * P.sigmaMin / (p + 1).factorial *
        ((derivativeStepThreshold P L j) ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)) *
          ε j ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ))) := by
            unfold derivativeDecreaseCoefficient
            ring
    _ ≤ P.eta1 * P.sigmaMin / (p + 1).factorial * ‖D.step i‖ ^ (p + 1) :=
      mul_le_mul_of_nonneg_left hb hcoeff
    _ < _ := h.modelTrace.successful_decrease hi hs

end ConvexRegularization
