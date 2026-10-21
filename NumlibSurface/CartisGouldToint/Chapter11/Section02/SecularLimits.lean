import Numlib.Optimization.SecularAsymptotics
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Chapter 11: leading secular limits

The actual shifted inverse has the leading coefficient used in the radius/weight comparison.
These component limits do not yet assert the complete inverse-parameter asymptotics.
-/

noncomputable section
namespace CartisGouldToint.Chapter11.Section02
open Filter Topology
open Chapter08.Section01 Chapter08.Section02

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The energy-space right-hand-side norm is precisely the inverse-metric gradient norm. -/
theorem secular_rightHandSide_norm (hM : M.PosDef) :
    ‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖ =
      weightedNorm M⁻¹ g := by
  rw [← Real.sqrt_sq (norm_nonneg _), hM.isPreconditioner_toEuclideanLin.norm_toEnergy_inv_sq]
  rfl

/-- The leading squared coefficient of the genuine source secular function. -/
theorem tendsto_mul_sq_secularData (hH : H.IsSymm) (hM : M.PosDef) :
    Tendsto (fun t : ℝ => t ^ 2 * secularData g H M t) atTop
      (𝓝 (weightedNorm M⁻¹ g ^ 2)) := by
  have he : (fun t : ℝ => t ^ 2 * secularData g H M t) =ᶠ[atTop]
      (fun t => t ^ 2 * Optimization.SecularResolvent.normSqResolvent (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) t) := by
    filter_upwards [eventually_gt_atTop (secularThreshold hH hM)] with t ht
    rw [secularData_eq_resolvent hH hM ht]
  apply Tendsto.congr' he.symm
  simpa only [secular_rightHandSide_norm hM] using
    Optimization.SecularResolvent.tendsto_mul_sq_normSqResolvent
      (secularHessian_isSymmetric hH hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))

/-- Along the actual inverse steps, shift times weighted step norm tends to the gradient norm. -/
theorem tendsto_mul_secularStep_norm (hH : H.IsSymm) (hM : M.PosDef) :
    Tendsto (fun t : ℝ => t * weightedNorm M (secularStep g H M t)) atTop
      (𝓝 (weightedNorm M⁻¹ g)) := by
  have hs := (tendsto_mul_sq_secularData (g := g) hH hM).sqrt
  have hg : 0 ≤ weightedNorm M⁻¹ g := Real.sqrt_nonneg _
  rw [Real.sqrt_sq hg] at hs
  apply Tendsto.congr' _ hs
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hd : 0 ≤ weightedNorm M (secularStep g H M t) := Real.sqrt_nonneg _
  rw [secularData, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le, Real.sqrt_sq hd]

end CartisGouldToint.Chapter11.Section02
