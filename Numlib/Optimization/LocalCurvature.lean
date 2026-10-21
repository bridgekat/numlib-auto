import Numlib.Optimization.HessianCurvatureContinuity
import Numlib.Optimization.CubicSecondOrder

/-!
# Uniform curvature near a reference point

A Lipschitz family of bilinear forms inherits a quantitative lower curvature bound on a
closed ball. The argument only uses the operator norm and applies without symmetry or
finite dimension. The Hessian specialization uses actual Fréchet derivatives.
-/

noncomputable section
namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

/-- A reference curvature loses at most the norm of a bilinear perturbation. -/
theorem leastCurvature_ge_sub_norm (B C : E →L[ℝ] E →L[ℝ] ℝ) :
    leastCurvature C - ‖B - C‖ ≤ leastCurvature B := by
  have h := leastCurvature_sub_le C B
  rw [norm_sub_rev] at h
  linarith

/-- A Lipschitz family retains half its reference curvature on the indicated ball. -/
theorem leastCurvature_ge_half_on_closedBall
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {xstar x : E} {L lambda : ℝ}
    (hL : 0 < L) (hlambda : lambda ≤ leastCurvature (B xstar))
    (hB : ‖B x - B xstar‖ ≤ L * ‖x - xstar‖)
    (hx : x ∈ Metric.closedBall xstar (lambda / (2 * L))) :
    lambda / 2 ≤ leastCurvature (B x) := by
  have hx' : ‖x - xstar‖ ≤ lambda / (2 * L) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hd : ‖x - xstar‖ * (2 * L) ≤ lambda := (le_div_iff₀ (by positivity)).mp hx'
  have hp := leastCurvature_ge_sub_norm (B x) (B xstar)
  linarith

/-- The half-curvature bound also gives the corresponding quadratic-form inequality. -/
theorem apply_self_ge_half_on_closedBall
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {xstar x : E} {L lambda : ℝ}
    (hL : 0 < L) (hlambda : lambda ≤ leastCurvature (B xstar))
    (hB : ‖B x - B xstar‖ ≤ L * ‖x - xstar‖)
    (hx : x ∈ Metric.closedBall xstar (lambda / (2 * L))) (u : E) :
    lambda / 2 * ‖u‖ ^ 2 ≤ B x u u :=
  (le_leastCurvature_iff _ _).mp
    (leastCurvature_ge_half_on_closedBall hL hlambda hB hx) u

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Nontrivial F]

/-- Actual Lipschitz Hessians retain half their reference least curvature. -/
theorem CubicRegularization.HessianLipschitz.leastCurvature_ge_half
    {f : F → ℝ} {L : ℝ} (hf : CubicRegularization.HessianLipschitz f L)
    (hL : 0 < L) (xstar : F) {x : F}
    (hx : x ∈ Metric.closedBall xstar
      (leastCurvature (fderiv ℝ (fderiv ℝ f) xstar) / (2 * L))) :
    leastCurvature (fderiv ℝ (fderiv ℝ f) xstar) / 2 ≤
      leastCurvature (fderiv ℝ (fderiv ℝ f) x) :=
  leastCurvature_ge_half_on_closedBall hL le_rfl (hf.curried_bound x xstar) hx

end Optimization
