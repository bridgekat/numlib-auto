import Numlib.Optimization.Composite.DerivativeBounds

/-!
# Generalized Taylor trials for actual composite regularization models

The smooth scalar part includes the integer norm-power penalty, while the
residual polynomial is retained inside the outer Lipschitz function. Actual
model derivative bounds yield the exact coefficient `3*(Df+K*Dc)+sigma`.
-/

namespace Composite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The smooth part of the actual regularized composite model. -/
noncomputable def smoothModel (f : E → ℝ) (p : ℕ) (x : E) (σ : ℝ) : E → ℝ :=
  ModelDecrease.penalized (TaylorModel.eval f p x) p σ

/-- The residual polynomial retained inside the outer function. -/
noncomputable def residualModel (c : E → F) (p : ℕ) (x : E) : E → F :=
  TaylorModel.eval c p x

omit [FiniteDimensional ℝ E] in
/-- The actual regularized composite model splits into its smooth part and residual. -/
theorem regularizedModel_eq (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (p : ℕ) (x : E) (σ : ℝ) (s : E) :
    regularizedModel f c h p x σ s = smoothModel f p x σ s + h (residualModel c p x s) := by
  simp only [regularizedModel, smoothModel, residualModel, taylorModel,
    ModelDecrease.penalized]
  ring

/-- A small generalized Taylor trial retains half the predicted decrease in the
actual regularized composite model, with the exact coefficient `3*(Df+K*Dc)+σ`. -/
theorem regularizedModel_decrement_ge_half (f : E → ℝ) (c : E → F) {h : F → ℝ}
    {p j : ℕ} (hj : 0 < j) (hjp : j ≤ p) {Df Dc σ α δ : ℝ} {K : NNReal}
    (hDf : 0 ≤ Df) (hDc : 0 ≤ Dc) (hσ : 0 < σ) (hh : LipschitzWith K h)
    (x s d : E) (hs : ‖s‖ ≤ 1)
    (hAf : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ Df)
    (hAc : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a c x‖ ≤ Dc)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ‖d‖ ≤ δ)
    (hsmall : δ ≤ α / (4 * (3 * (Df + (K : ℝ) * Dc) + σ)))
    (htest : α * δ ^ j / j.factorial ≤
      decrement (smoothModel f p x σ) (residualModel c p x) h j s d) :
    α / 2 * δ ^ j / j.factorial ≤
      regularizedModel f c h p x σ s - regularizedModel f c h p x σ (s + d) := by
  have hF : ContDiff ℝ p (smoothModel f p x σ) :=
    ModelDecrease.contDiff_penalized_ofJet _ p p le_rfl σ
  have hC : ContDiff ℝ p (residualModel c p x) := TaylorModel.contDiff_eval c p x p
  have hLF : ∀ u v,
      ‖iteratedFDeriv ℝ p (smoothModel f p x σ) u -
        iteratedFDeriv ℝ p (smoothModel f p x σ) v‖ ≤ σ * ‖u - v‖ :=
    ModelDecrease.norm_sub_iteratedFDeriv_penalized_ofJet_le _ p hσ.le
  have hLC : ∀ u v,
      ‖iteratedFDeriv ℝ p (residualModel c p x) u -
        iteratedFDeriv ℝ p (residualModel c p x) v‖ ≤ 0 * ‖u - v‖ := by
    intro u v
    rw [show iteratedFDeriv ℝ p (residualModel c p x) u =
      iteratedFDeriv ℝ p (residualModel c p x) v from
      TaylorModel.iteratedFDeriv_ofJet_top_eq _ p u v, sub_self, norm_zero, zero_mul]
  have hBF : ∀ a, j < a → a ≤ p →
      ‖iteratedFDeriv ℝ a (smoothModel f p x σ) s‖ ≤ 3 * Df + σ := by
    intro a hja hap
    exact ModelDecrease.norm_iteratedFDeriv_penalized_ofJet_le_three_mul_add _ hap
      hσ.le hDf (fun i hai hip => hAf i (by omega) hip) hs
  have hBC : ∀ a, j < a → a ≤ p →
      ‖iteratedFDeriv ℝ a (residualModel c p x) s‖ ≤ 3 * Dc := by
    intro a hja hap
    exact TaylorModel.norm_iteratedFDeriv_ofJet_le_three_mul _ hap hDc
      (fun i hai hip => hAc i (by omega) hip) hs
  have hb : 0 < (3 * Df + σ) + (K : ℝ) * (3 * Dc) := by positivity
  have hB : σ + (K : ℝ) * 0 ≤ (3 * Df + σ) + (K : ℝ) * (3 * Dc) := by
    nlinarith [mul_nonneg K.coe_nonneg hDc]
  have hsmall' : δ ≤ α / (4 * ((3 * Df + σ) + (K : ℝ) * (3 * Dc))) := by
    convert hsmall using 1
    ring
  have hret := value_decrement_ge_half_of_taylor_test hj hjp hF hC hσ.le (by norm_num)
    (by positivity : 0 ≤ 3 * Df + σ) (by positivity : 0 ≤ 3 * Dc)
    hb hB hLF hLC hh s d hδ hδ1 hd hsmall' hBF hBC htest
  simpa only [regularizedModel_eq] using hret
end Composite
