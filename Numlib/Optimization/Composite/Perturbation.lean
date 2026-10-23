import Numlib.Optimization.Composite.TaylorDecrease

/-!
# Perturbations of actual generalized composite Taylor criticality

The scalar decrement cancels its constant term. The retained outer function
contributes a basepoint difference and a Taylor-value difference, each controlled
by its Lipschitz constant. Actual multilinear derivative operator errors control
the positive-degree finite sum, and compactness transfers the bound to criticality.
-/

namespace Composite
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact generalized decrement separates a smooth scalar decrement from the
retained outer-function increment. -/
theorem decrement_eq_jetDecrement (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (j : ℕ) (x d : E) :
    decrement f c h j x d =
      TaylorModel.jetDecrement (ftaylorSeries ℝ f x) j d +
        h (c x) - h (TaylorModel.eval c j x d) := by
  rw [decrement_eq]
  simp only [TaylorModel.jetDecrement, TaylorModel.ofJet_zero, ftaylorSeries,
    iteratedFDeriv_zero_apply]
  unfold taylorModel TaylorModel.eval
  ring

/-- Scalar and residual derivative perturbations control actual generalized
Taylor decrements; the residual constant contributes twice its Lipschitz error. -/
theorem decrement_sub_decrement_le (f₁ f₂ : E → ℝ) (c₁ c₂ : E → F) {h : F → ℝ}
    {K : NNReal} (hh : LipschitzWith K h) (j : ℕ) (x₁ x₂ d : E) :
    decrement f₁ c₁ h j x₁ d - decrement f₂ c₂ h j x₂ d ≤
      (∑ i ∈ Finset.range j,
        (‖iteratedFDeriv ℝ (i + 1) f₁ x₁ - iteratedFDeriv ℝ (i + 1) f₂ x₂‖ +
          (K : ℝ) * ‖iteratedFDeriv ℝ (i + 1) c₁ x₁ -
            iteratedFDeriv ℝ (i + 1) c₂ x₂‖) * ‖d‖ ^ (i + 1) / (i + 1).factorial) +
        2 * (K : ℝ) * ‖c₁ x₁ - c₂ x₂‖ := by
  let Af := ftaylorSeries ℝ f₁ x₁
  let Bf := ftaylorSeries ℝ f₂ x₂
  let Ac := ftaylorSeries ℝ c₁ x₁
  let Bc := ftaylorSeries ℝ c₂ x₂
  have hf := TaylorModel.norm_jetDecrement_sub_le Af Bf j d
  have hc := TaylorModel.norm_jetDecrement_sub_le Ac Bc j d
  have hzero : TaylorModel.jetDecrement Ac j d - TaylorModel.jetDecrement Bc j d =
      (c₁ x₁ - c₂ x₂) -
        (TaylorModel.eval c₁ j x₁ d - TaylorModel.eval c₂ j x₂ d) := by
    simp only [TaylorModel.jetDecrement, TaylorModel.ofJet_zero, Ac, Bc, ftaylorSeries,
      iteratedFDeriv_zero_apply]
    change (c₁ x₁ - TaylorModel.eval c₁ j x₁ d) -
      (c₂ x₂ - TaylorModel.eval c₂ j x₂ d) = _
    abel
  have hvalue : ‖TaylorModel.eval c₁ j x₁ d - TaylorModel.eval c₂ j x₂ d‖ ≤
      ‖c₁ x₁ - c₂ x₂‖ + ∑ i ∈ Finset.range j,
        ‖Ac (i + 1) - Bc (i + 1)‖ * ‖d‖ ^ (i + 1) / (i + 1).factorial := by
    have he : TaylorModel.eval c₁ j x₁ d - TaylorModel.eval c₂ j x₂ d =
        (c₁ x₁ - c₂ x₂) - (TaylorModel.jetDecrement Ac j d -
          TaylorModel.jetDecrement Bc j d) := by rw [hzero]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hc)
  have hb := hh.dist_le_mul (c₁ x₁) (c₂ x₂)
  have hv := hh.dist_le_mul (TaylorModel.eval c₁ j x₁ d) (TaylorModel.eval c₂ j x₂ d)
  rw [Real.dist_eq, dist_eq_norm] at hb hv
  have hv' := hv.trans (mul_le_mul_of_nonneg_left hvalue K.coe_nonneg)
  rw [decrement_eq_jetDecrement, decrement_eq_jetDecrement]
  have hsum : (∑ i ∈ Finset.range j,
      (‖iteratedFDeriv ℝ (i + 1) f₁ x₁ - iteratedFDeriv ℝ (i + 1) f₂ x₂‖ +
        (K : ℝ) * ‖iteratedFDeriv ℝ (i + 1) c₁ x₁ -
          iteratedFDeriv ℝ (i + 1) c₂ x₂‖) * ‖d‖ ^ (i + 1) / (i + 1).factorial) =
      (∑ i ∈ Finset.range j, ‖Af (i + 1) - Bf (i + 1)‖ *
        ‖d‖ ^ (i + 1) / (i + 1).factorial) +
        (K : ℝ) * ∑ i ∈ Finset.range j, ‖Ac (i + 1) - Bc (i + 1)‖ *
          ‖d‖ ^ (i + 1) / (i + 1).factorial := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [Af, Bf, Ac, Bc, ftaylorSeries]
    ring
  rw [hsum]
  have hf' := (abs_le.mp hf).2
  have hb' := (abs_le.mp hb).2
  have hv'' := (abs_le.mp hv').1
  linarith

/-- Actual composite criticalities obey the same tensor perturbation bound on a
common ball; no closure or regularity of the underlying maps is required. -/
theorem criticality_le_add_tensor_errors [ProperSpace E]
    (f₁ f₂ : E → ℝ) (c₁ c₂ : E → F) {h : F → ℝ}
    {K : NNReal} (hh : LipschitzWith K h) (j : ℕ) (x₁ x₂ : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    criticality f₁ c₁ h j x₁ δ ≤ criticality f₂ c₂ h j x₂ δ +
      (∑ i ∈ Finset.range j,
        (‖iteratedFDeriv ℝ (i + 1) f₁ x₁ - iteratedFDeriv ℝ (i + 1) f₂ x₂‖ +
          (K : ℝ) * ‖iteratedFDeriv ℝ (i + 1) c₁ x₁ -
            iteratedFDeriv ℝ (i + 1) c₂ x₂‖) * δ ^ (i + 1) / (i + 1).factorial) +
        2 * (K : ℝ) * ‖c₁ x₁ - c₂ x₂‖ := by
  obtain ⟨d, hd, he⟩ := exists_decrement_eq_criticality f₁ c₁ hh.continuous j x₁ hδ
  have hdiff := decrement_sub_decrement_le f₁ f₂ c₁ c₂ hh j x₁ x₂ d
  have hsum : (∑ i ∈ Finset.range j,
      (‖iteratedFDeriv ℝ (i + 1) f₁ x₁ - iteratedFDeriv ℝ (i + 1) f₂ x₂‖ +
        (K : ℝ) * ‖iteratedFDeriv ℝ (i + 1) c₁ x₁ -
          iteratedFDeriv ℝ (i + 1) c₂ x₂‖) * ‖d‖ ^ (i + 1) / (i + 1).factorial) ≤
      ∑ i ∈ Finset.range j,
        (‖iteratedFDeriv ℝ (i + 1) f₁ x₁ - iteratedFDeriv ℝ (i + 1) f₂ x₂‖ +
          (K : ℝ) * ‖iteratedFDeriv ℝ (i + 1) c₁ x₁ -
            iteratedFDeriv ℝ (i + 1) c₂ x₂‖) * δ ^ (i + 1) / (i + 1).factorial := by
    apply Finset.sum_le_sum
    intro i hi
    gcongr
  have hmodel := decrement_le_criticality f₂ c₂ hh.continuous j x₂ hd
  change decrement f₂ c₂ h j x₂ d ≤ _ at hmodel
  change decrement f₁ c₁ h j x₁ d = _ at he
  rw [he] at hdiff
  linarith
end Composite
