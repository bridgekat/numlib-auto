import Numlib.Optimization.ModelBased.QuadraticModel
import Numlib.Optimization.ModelBased.RatioTest

/-! # Choosing the initial radius -/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter17

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The two initial-radius choices in (17.2.1). -/
noncomputable def initialRadiusChoices (g : E) : ℝ × ℝ :=
  (1, ‖g‖ / 10)

/-- The right-hand side of (17.2.2) is the parameter of the unnormalized gradient ray. -/
noncomputable def cauchyRayParameter (g : E) (H : E →L[ℝ] E) : ℝ :=
  ‖g‖ ^ 2 / ⟪g, H g⟫

/-- Corrected (17.2.2). The initial radius is the norm of the minimizing step. -/
noncomputable def cauchyInitialRadius (g : E) (H : E →L[ℝ] E) : ℝ :=
  cauchyRayParameter g H * ‖g‖

/-- For positive ray curvature, the corrected radius is the length of the
unconstrained quadratic minimizer on the steepest-descent ray. -/
theorem cauchyInitialRadius_spec {g : E} {H : E →L[ℝ] E} (hH : 0 < ⟪g, H g⟫) :
    let t := cauchyRayParameter g H
    ‖-(t • g)‖ = cauchyInitialRadius g H ∧
      ∀ u : ℝ, Subproblem.quadModel g H (-(t • g)) ≤
        Subproblem.quadModel g H (-(u • g)) := by
  let t := cauchyRayParameter g H
  have ht : 0 ≤ t := div_nonneg (sq_nonneg _) hH.le
  refine ⟨by rw [norm_neg, norm_smul, Real.norm_of_nonneg ht]; rfl, fun u ↦ ?_⟩
  rw [Optimization.quadModel_neg_smul, Optimization.quadModel_neg_smul]
  have hparam : t * ⟪g, H g⟫ = ‖g‖ ^ 2 := div_mul_cancel₀ _ hH.ne'
  rw [← hparam]
  nlinarith only [mul_nonneg (sq_nonneg (u - t)) hH.le]

/-- The displacement probe (17.2.3) before subtracting it from the base point. -/
noncomputable def initialProbeDisplacement (g : E) (Δ : ℝ) : E :=
  (Δ / ‖g‖) • g

/-- The probe displacement has the given radius for a nonzero gradient. -/
theorem norm_initialProbeDisplacement {g : E} (hg : g ≠ 0) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ‖initialProbeDisplacement g Δ‖ = Δ := by
  rw [initialProbeDisplacement, norm_smul, Real.norm_of_nonneg (by positivity),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hg)]

/-- The initial probe ratio (17.2.4) for a model that agrees at the base point. -/
noncomputable def initialProbeRatio (f m : E → ℝ) (x d : E) : ℝ :=
  (f x - f (x - d)) / (f x - m (x - d))

end ConnGouldToint.Chapter17
