import Numlib.Optimization.CompositeRegularization

/-!
# Composite value errors and parameter bounds

A Taylor value remainder for the smooth components, combined through the Lipschitz
composition, gives the usual very-successful-trial threshold and uniform parameter bound.
The argument uses the actual ratio and model nonincrease, and needs no differentiability
of the nonsmooth composition.
-/

noncomputable section
open scoped Nat NNReal
namespace Optimization.CompositeRegularization
open CompositeTaylorModels
open HigherOrderApproximateRegularization (Parameters OuterState OuterOutcome ParameterUpdate)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Strict actual model decrease implies positive predicted generalized decrease. -/
theorem decrement_pos_of_model_lt {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p : ℕ} {x s : E} {σ : ℝ} (hσ : 0 ≤ σ)
    (hs : regularizedModel f c h p x σ s < regularizedModel f c h p x σ 0) :
    0 < decrement f c h p x s := by
  have hn : 0 ≤ σ * ‖s‖ ^ (p + 1) / (p + 1)! := by positivity
  simp only [regularizedModel] at hs
  dsimp [decrement]
  simp only [norm_zero, zero_pow (Nat.succ_ne_zero p), mul_zero, zero_div, add_zero] at hs
  linarith

/-- A sufficiently large parameter makes a strict actual model step very successful. -/
theorem very_successful_of_error {P : Parameters} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {x s : E} {σ L : ℝ} (hσ : 0 ≤ σ)
    (herr : |objective f c h (x + s) - model f c h P.p x s| ≤
      L * ‖s‖ ^ (P.p + 1) / (P.p + 1)!)
    (hs : regularizedModel f c h P.p x σ s < regularizedModel f c h P.p x σ 0)
    (hlarge : L / (1 - P.eta2) ≤ σ) : P.eta2 ≤ ratio f c h P.p x s := by
  have hη : 0 < 1 - P.eta2 := sub_pos.mpr P.eta2_lt_one
  have hden := decrement_pos_of_model_lt hσ hs
  have hpred := regularized_decrement_lower_bound hs.le
  have hlarge' : L ≤ σ * (1 - P.eta2) := (div_le_iff₀ hη).mp hlarge
  have hscale : 0 ≤ ‖s‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hlarge' hscale
  have hpaid := mul_le_mul_of_nonneg_left hpred hη.le
  have hcomb : L * ‖s‖ ^ (P.p + 1) / (P.p + 1)! ≤
      (1 - P.eta2) * decrement f c h P.p x s := by
    calc
      _ = L * (‖s‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ)) := by ring
      _ ≤ σ * (1 - P.eta2) * (‖s‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ)) := hscaled
      _ = (1 - P.eta2) * (σ * ‖s‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ)) := by ring
      _ ≤ _ := hpaid
  have herror := (abs_le.mp herr).2
  rw [ratio, le_div_iff₀ hden]
  rw [decrement_eq] at hpaid
  simp only [decrement_eq, objective] at *
  nlinarith only [hcomb, herror]

/-- A real continuing transition preserves the old parameter or the source threshold. -/
theorem OuterTransition.sigma_bound {P : Parameters} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {a b : OuterState E} {nf nd : ℕ} {L : ℝ}
    (herr : ∀ x s, |objective f c h (x + s) - model f c h P.p x s| ≤
      L * ‖s‖ ^ (P.p + 1) / (P.p + 1)!)
    (ht : OuterTransition P f c h a (.next b) nf nd) (hσ : 0 ≤ a.sigma) :
    b.sigma ≤ max a.sigma (P.gamma3 * (L / (1 - P.eta2))) := by
  cases ht with
  | trial hf hc trial hs σ hu =>
    have hb : (if P.eta1 ≤ ratio f c h P.p a.point trial.step then
        (⟨a.point + trial.step, σ, trial.radii, 0, true⟩ : OuterState E) else
        ⟨a.point, σ, a.radii, P.p, false⟩).sigma = σ := by split_ifs <;> rfl
    rw [hb]
    by_cases hlarge : L / (1 - P.eta2) ≤ a.sigma
    · have hv := very_successful_of_error hσ (herr _ _) hs hlarge
      have hu' : σ ≤ a.sigma := by
        unfold ParameterUpdate at hu
        rw [ite_eq_left hv] at hu
        exact hu.2
      exact hu'.trans (le_max_left _ _)
    · have hu' : σ ≤ P.gamma3 * a.sigma := by
        unfold ParameterUpdate at hu
        split_ifs at hu with hv ha
        · exact hu.2.trans (by nlinarith [P.gamma2_lt_gamma3, P.one_lt_gamma2])
        · exact hu.2.trans (mul_le_mul_of_nonneg_right P.gamma2_lt_gamma3.le hσ)
        · exact hu.2
      exact hu'.trans ((mul_le_mul_of_nonneg_left (le_of_not_ge hlarge)
        (by linarith [P.gamma2_lt_gamma3, P.one_lt_gamma2])).trans (le_max_right _ _))

/-- Every actual finite execution satisfies the uniform regularization parameter bound. -/
theorem OuterExecution.sigma_upper {P : Parameters} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {x : E} {σ L : ℝ} {δ : ℕ → ℝ} {N : ℕ}
    (run : OuterExecution P f c h x σ δ N)
    (herr : ∀ x s, |objective f c h (x + s) - model f c h P.p x s| ≤
      L * ‖s‖ ^ (P.p + 1) / (P.p + 1)!) {k : ℕ} (hk : k ≤ N) :
    (run.state k).sigma ≤ max σ (P.gamma3 * (L / (1 - P.eta2))) := by
  induction k with
  | zero =>
    rw [run.initial.2.2]
    exact le_max_left _ _
  | succ k ih =>
    have hstep := (run.transition k (by omega)).sigma_bound herr
      (P.sigmaMin_pos.le.trans (run.valid k (by omega)).1)
    exact hstep.trans (max_le (ih (by omega)) (le_max_right _ _))

end Optimization.CompositeRegularization
