import NumlibSurface.ConnGouldToint.Chapter14.Section01
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Ring

/-! # The quadratic penalty and augmented Lagrangian -/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter14

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The quadratic penalty function (14.2.1). -/
noncomputable def quadraticPenalty (f : E → ℝ) (c : E → F) (μ : ℝ) (x : E) : ℝ :=
  f x + (2 * μ)⁻¹ * ‖c x‖ ^ 2

/-- The augmented Lagrangian (14.2.2). -/
noncomputable def augmentedLagrangian (f : E → ℝ) (c : E → F) (y : F) (μ : ℝ) (x : E) : ℝ :=
  lagrangian f c y x + (2 * μ)⁻¹ * ‖c x‖ ^ 2

/-- The first-order multiplier estimate (14.2.5). -/
noncomputable def firstOrderMultiplier (c : E → F) (y : F) (μ : ℝ) (x : E) : F :=
  y - μ⁻¹ • c x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The constraint violation is a scaled multiplier difference, as in (14.2.6). -/
theorem constraint_eq_multiplier_difference (c : E → F) (y : F) {μ : ℝ} (hμ : μ ≠ 0) (x : E) :
    c x = μ • (y - firstOrderMultiplier c y μ x) := by
  rw [firstOrderMultiplier, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hμ, one_smul]

/-- The equality-constrained stationarity and feasibility conditions (14.2.3).
Both derivatives are evaluated at the same point `x`. -/
def IsEqualityKKT (f : E → ℝ) (c : E → F) (x : E) (y : F) : Prop :=
  c x = 0 ∧ fderiv ℝ f x = (innerSL ℝ y).comp (fderiv ℝ c x)

private theorem hasFDerivAt_lagrangian {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (y : F) :
    HasFDerivAt (lagrangian f c y)
      (fderiv ℝ f x - (innerSL ℝ y).comp (fderiv ℝ c x)) x :=
  hf.hasFDerivAt.sub ((innerSL ℝ y).hasFDerivAt.comp x hc.hasFDerivAt)

/-- The derivative identity (14.2.7). The estimated multiplier is held fixed when
differentiating the Lagrangian. -/
theorem fderiv_augmentedLagrangian_eq {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (y : F) (μ : ℝ) :
    fderiv ℝ (augmentedLagrangian f c y μ) x =
      fderiv ℝ (lagrangian f c (firstOrderMultiplier c y μ x)) x := by
  have hpen := hc.hasFDerivAt.norm_sq.const_smul ((2 * μ)⁻¹)
  change fderiv ℝ (lagrangian f c y + (2 * μ)⁻¹ • (fun z ↦ ‖c z‖ ^ 2)) x = _
  rw [((hasFDerivAt_lagrangian hf hc y).add hpen).fderiv,
    (hasFDerivAt_lagrangian hf hc _).fderiv]
  ext d
  simp [firstOrderMultiplier, mul_inv_rev]
  ring

/-- Equation (14.2.4). At a local minimum of the augmented Lagrangian, the objective
derivative equals the constraint derivative paired with the first-order multiplier estimate. -/
theorem fderiv_lagrangian_eq_zero_of_augmentedLagrangian_min
    {f : E → ℝ} {c : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) {y : F} {μ : ℝ} (hmin : IsLocalMin
      (augmentedLagrangian f c y μ) x) :
    fderiv ℝ f x = (innerSL ℝ (firstOrderMultiplier c y μ x)).comp (fderiv ℝ c x) := by
  have hdiff : DifferentiableAt ℝ (augmentedLagrangian f c y μ) x :=
    ((hasFDerivAt_lagrangian hf hc y).add
      (hc.hasFDerivAt.norm_sq.const_smul ((2 * μ)⁻¹))).differentiableAt
  have hzero := hmin.hasFDerivAt_eq_zero hdiff.hasFDerivAt
  rw [fderiv_augmentedLagrangian_eq hf hc, (hasFDerivAt_lagrangian hf hc _).fderiv] at hzero
  exact sub_eq_zero.mp hzero

end ConnGouldToint.Chapter14
