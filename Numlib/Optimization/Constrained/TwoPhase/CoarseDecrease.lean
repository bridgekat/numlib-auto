import Numlib.Optimization.Constrained.TwoPhase.InnerBudget
import Numlib.Optimization.Constrained.TargetPerturbation

/-!
# Safe fractional endpoint charges in the two-phase method

An endpoint above a fixed fraction of the inner absolute tolerance still
spends a positive true objective decrease when that fraction exceeds the
model-tolerance factor. The remaining reflection returns spend target gap.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- Actual model-error transfer at a fraction above the model tolerance gives
a genuine step-power bound, without altering any primitive execution rule. -/
theorem Run.fractional_step_lower {p : ℕ} {f : E → ℝ} {C S : Set E} {P : Settings p}
    {ε L β : ℝ} {D : Data E} {N i : ℕ} (h : Run f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hs : P.eta1 ≤ D.ratio i)
    (hlarge : β * ε ≤ constrainedCriticality f 1 C (D.point (i + 1)) 1) :
    p.factorial * (β - P.theta) / (L + parameterCap P L) * ε ≤ ‖D.step i‖ ^ p := by
  have hh := h.trial_criticality_le hclosed hS hCS hC hf hL.le hlip hi
  rw [← h.modelTrace.successful_point hi hs] at hh
  have hcap := h.parameter_le hS hCS hC hf hL.le hlip hi.le
  have hfac : (0 : ℝ) < p.factorial := by positivity
  have hcap0 := P.sigmaMin_pos.trans_le (P.sigmaMin_le_initial.trans
    (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have hden : 0 < L + parameterCap P L := by positivity
  have hb : (L + D.parameter i) / p.factorial * ‖D.step i‖ ^ p ≤
      (L + parameterCap P L) / p.factorial * ‖D.step i‖ ^ p :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (by linarith : L + D.parameter i ≤ L + parameterCap P L)
      hfac.le) (pow_nonneg (norm_nonneg _) _)
  have he : (β - P.theta) * ε ≤
      (L + parameterCap P L) / p.factorial * ‖D.step i‖ ^ p := by
        nlinarith only [hh, hb, hlarge]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have he' := (le_div_iff₀ hfac).mp (by simpa only [div_mul_eq_mul_div] using he)
  nlinarith only [he']

/-- Positive true decrease coefficient for the fractional endpoint charge. -/
noncomputable def fractionalDecreaseCoefficient {p : ℕ} (P : Settings p) (L β : ℝ) : ℝ :=
  P.eta1 * P.sigmaMin / (p + 1).factorial *
    (p.factorial * (β - P.theta) / (L + parameterCap P L)) ^ (((p + 1 : ℕ) : ℝ) / p)

/-- The fixed fractional coefficient is positive when the margin is strict. -/
theorem fractionalDecreaseCoefficient_pos {p : ℕ} (P : Settings p) {L β : ℝ}
    (hL : 0 < L) (hβ : P.theta < β) : 0 < fractionalDecreaseCoefficient P L β := by
  have hcap0 := P.sigmaMin_pos.trans_le (P.sigmaMin_le_initial.trans
    (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  unfold fractionalDecreaseCoefficient
  positivity

/-- Actual successful trials whose endpoint passes the fractional threshold
consume the uniform absolute-tolerance objective budget. -/
theorem Run.fractional_successful_decrease {p : ℕ} {f : E → ℝ} {C S : Set E}
    {P : Settings p} {ε L β : ℝ} {D : Data E} {N i : ℕ} (h : Run f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hβ : P.theta < β) (hi : i < N) (hs : P.eta1 ≤ D.ratio i)
    (hlarge : β * ε ≤ constrainedCriticality f 1 C (D.point (i + 1)) 1) :
    fractionalDecreaseCoefficient P L β * ε ^ (((p + 1 : ℕ) : ℝ) / p) ≤
      f (D.point i) - f (D.point (i + 1)) := by
  have hcap0 := P.sigmaMin_pos.trans_le (P.sigmaMin_le_initial.trans
    (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have hcoef : 0 ≤ p.factorial * (β - P.theta) / (L + parameterCap P L) := by positivity
  exact h.modelTrace.decrease_of_step_lower hi hs P.order_pos hcoef h.accuracy_pos.le
    (h.fractional_step_lower hclosed hS hCS hC hf hL hlip hi hs hlarge)

end ConvexRegularization
