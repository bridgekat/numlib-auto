import Numlib.Optimization.Constrained.LagrangianStability

/-!
# The actual target merit and its Lagrangian derivative

The squared constraint residual and squared objective-target residual give the
true two-phase merit. Its actual derivative is the positive objective-target
gap times the derivative of the Lagrangian with the associated multiplier.
-/

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- The actual squared residual merit with an explicit objective target. -/
noncomputable def targetMerit (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) : ℝ :=
  ‖c x‖ ^ 2 / 2 + (f x - t) ^ 2 / 2

/-- The multiplier computed from the target gap and constraint residual. -/
noncomputable def targetMultiplier (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) : F :=
  -(f x - t)⁻¹ • c x

/-- The actual derivative of the target merit, including both residual terms. -/
theorem hasFDerivAt_targetMerit {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (t : ℝ) :
    HasFDerivAt (targetMerit f c t)
      ((innerSL ℝ (c x)).comp (fderiv ℝ c x) + (f x - t) • fderiv ℝ f x) x := by
  have hd := (hc.hasFDerivAt.norm_sq.const_smul (1 / 2 : ℝ)).add
    (((hf.hasFDerivAt.sub_const t).pow 2).const_smul (1 / 2 : ℝ))
  convert hd using 1
  · funext z
    change ‖c z‖ ^ 2 / 2 + (f z - t) ^ 2 / 2 =
      (1 / 2 : ℝ) * ‖c z‖ ^ 2 + (1 / 2 : ℝ) * (f z - t) ^ 2
    ring
  · ext v
    simp [innerSL_apply_apply, smul_eq_mul]
    ring

/-- The directional derivative of the genuine target merit. -/
theorem fderiv_targetMerit {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (t : ℝ) (v : E) :
    fderiv ℝ (targetMerit f c t) x v =
      inner ℝ (c x) (fderiv ℝ c x v) + (f x - t) * fderiv ℝ f x v := by
  rw [(hasFDerivAt_targetMerit hf hc t).fderiv]
  rfl

/-- The true target merit derivative equals its target gap times the Lagrangian derivative. -/
theorem fderiv_targetMerit_eq_lagrangian {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    {t : ℝ} (ht : f x - t ≠ 0) :
    fderiv ℝ (targetMerit f c t) x =
      (f x - t) • fderiv ℝ (vectorLagrangian f c (targetMultiplier f c t x)) x := by
  ext v
  rw [fderiv_targetMerit hf hc]
  have hl := (hf.hasFDerivAt.sub (((innerSL ℝ (targetMultiplier f c t x)).hasFDerivAt).comp x
    hc.hasFDerivAt)).fderiv
  change fderiv ℝ (f - (innerSL ℝ (targetMultiplier f c t x)) ∘ c) x = _ at hl
  change _ = (f x - t) * fderiv ℝ (f - (innerSL ℝ (targetMultiplier f c t x)) ∘ c) x v
  rw [hl]
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, targetMultiplier, real_inner_smul_left]
  field_simp
  ring
end Constrained
