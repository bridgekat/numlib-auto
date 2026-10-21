import Numlib.Optimization.HessianCurvature

/-!
# Continuity of least curvature

Least bilinear curvature is Lipschitz in the bilinear operator norm, without symmetry or
finite-dimensional hypotheses. Nontriviality supplies a nonzero Rayleigh direction.
-/

noncomputable section
namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

/-- Perturbing a bilinear form shifts least curvature by at most the perturbation norm. -/
theorem leastCurvature_sub_le (B C : E →L[ℝ] E →L[ℝ] ℝ) :
    leastCurvature B - leastCurvature C ≤ ‖B - C‖ := by
  have hB := (le_leastCurvature_iff B (leastCurvature B)).mp le_rfl
  have hC : leastCurvature B - ‖B - C‖ ≤ leastCurvature C := by
    apply (le_leastCurvature_iff C _).mpr
    intro d
    have h := ContinuousLinearMap.abs_apply_self_le (B - C) d
    simp only [sub_apply] at h
    have := (abs_le.mp h).2
    nlinarith [hB d]
  linarith

/-- The absolute perturbation of least curvature is bounded by the operator norm. -/
theorem abs_leastCurvature_sub_le (B C : E →L[ℝ] E →L[ℝ] ℝ) :
    |leastCurvature B - leastCurvature C| ≤ ‖B - C‖ := by
  have h := leastCurvature_sub_le C B
  rw [norm_sub_rev] at h
  exact abs_le.mpr ⟨by linarith, leastCurvature_sub_le B C⟩

/-- Least curvature is a one-Lipschitz function of the bilinear form. -/
theorem lipschitzWith_leastCurvature :
    LipschitzWith 1 (leastCurvature (E := E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro B C
  simpa [Real.dist_eq, dist_eq_norm] using abs_leastCurvature_sub_le B C

/-- Least curvature is continuous in the bilinear operator norm. -/
theorem continuous_leastCurvature : Continuous (leastCurvature (E := E)) :=
  lipschitzWith_leastCurvature.continuous

end Optimization
