import Numlib.Optimization.Constrained.TargetMerit
import Numlib.Optimization.HighOrder.CriticalityApproximate
/-!
# First-order certificates from the actual target merit

A positive objective-target gap scales the true Lagrangian derivative and every
feasible first-order Taylor decrement. Compact attainment transfers that exact
identity to constrained criticality. The residual norm is the same gap times
the augmented multiplier norm, giving the valid first-order termination bound.
-/

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- The actual first-order target merit decrement is the target gap times the
Lagrangian decrement for the computed multiplier. -/
theorem decrement_one_targetMerit {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    {t : ℝ} (ht : f x - t ≠ 0) (d : E) :
    TaylorModel.decrement (targetMerit f c t) 1 x d = (f x - t) *
      TaylorModel.decrement (vectorLagrangian f c (targetMultiplier f c t x)) 1 x d := by
  rw [TaylorModel.decrement_one, TaylorModel.decrement_one,
    inner_gradient_left, inner_gradient_left, fderiv_targetMerit_eq_lagrangian hf hc ht]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- A positive target gap scales the exact constrained first-order criticality,
including arbitrary closed feasible sets. -/
theorem constrainedCriticality_one_targetMerit {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    {t δ : ℝ} (ht : 0 < f x - t) {X : Set E} (hX : IsClosed X)
    (hx : x ∈ X) (hδ : 0 ≤ δ) :
    TaylorModel.constrainedCriticality (targetMerit f c t) 1 X x δ = (f x - t) *
      TaylorModel.constrainedCriticality
        (vectorLagrangian f c (targetMultiplier f c t x)) 1 X x δ := by
  apply le_antisymm
  · obtain ⟨d, hfeas, hd, he⟩ := TaylorModel.exists_decrement_eq_constrainedCriticality
      (targetMerit f c t) 1 hX hx hδ
    rw [←he, decrement_one_targetMerit hf hc ht.ne']
    exact mul_le_mul_of_nonneg_left (TaylorModel.decrement_le_constrainedCriticality
      _ 1 hX hfeas hd) ht.le
  · obtain ⟨d, hfeas, hd, he⟩ := TaylorModel.exists_decrement_eq_constrainedCriticality
      (vectorLagrangian f c (targetMultiplier f c t x)) 1 hX hx hδ
    rw [←he, ←decrement_one_targetMerit hf hc ht.ne']
    exact TaylorModel.decrement_le_constrainedCriticality _ 1 hX hfeas hd

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- The augmented residual norm is the positive target gap times the norm of
the computed augmented multiplier. -/
theorem targetMultiplier_norm_identity (f : E → ℝ) (c : E → F) {t : ℝ} {x : E}
    (ht : 0 < f x - t) :
    (f x - t) * multiplierNorm (targetMultiplier f c t x) =
      Real.sqrt (‖c x‖ ^ 2 + (f x - t) ^ 2) := by
  have hn : ‖targetMultiplier f c t x‖ = (f x - t)⁻¹ * ‖c x‖ := by
    simp only [targetMultiplier, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_inv, abs_of_pos ht]
  have hm : multiplierNorm (targetMultiplier f c t x) ^ 2 =
      1 + ((f x - t)⁻¹ * ‖c x‖) ^ 2 := by
    rw [multiplierNorm, Real.sq_sqrt (by positivity), hn]
  have hs := Real.sq_sqrt (show 0 ≤ ‖c x‖ ^ 2 + (f x - t) ^ 2 by positivity)
  have he : ((f x - t) * multiplierNorm (targetMultiplier f c t x)) ^ 2 =
      ‖c x‖ ^ 2 + (f x - t) ^ 2 := by
    rw [mul_pow, hm]
    field_simp
    ring
  nlinarith [Real.sqrt_nonneg (‖c x‖ ^ 2 + (f x - t) ^ 2),
    mul_pos ht (multiplierNorm_pos (targetMultiplier f c t x))]
/-- A genuine normalized target merit certificate gives the first-order
Lagrangian certificate on the same actual feasible displacement set. -/
theorem lagrangian_first_order_of_targetMerit {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    {t δ ε : ℝ} (ht : 0 < f x - t) {X : Set E} (hX : IsClosed X)
    (hx : x ∈ X) (hδ : 0 ≤ δ)
    (hcrit : TaylorModel.constrainedCriticality (targetMerit f c t) 1 X x δ ≤
      ε * Real.sqrt (‖c x‖ ^ 2 + (f x - t) ^ 2) * δ) :
    TaylorModel.constrainedCriticality
      (vectorLagrangian f c (targetMultiplier f c t x)) 1 X x δ ≤
        ε * multiplierNorm (targetMultiplier f c t x) * δ := by
  apply le_of_mul_le_mul_left (a := f x - t) _ ht
  rw [←constrainedCriticality_one_targetMerit hf hc ht hX hx hδ]
  rw [←targetMultiplier_norm_identity f c ht] at hcrit
  convert hcrit using 1
  ring
end Constrained
