import Numlib.Optimization.Quadratic.Optimality.Metric
import Numlib.Analysis.InnerProductSpace.Symmetric.SpectralExtrema

/-!
# The largest generalized eigenvalue in the genuine metric inner product

The symmetric energy-space Hessian represents the original pencil exactly.
Its greatest actual eigenvalue bounds the corresponding quadratic form.
-/

namespace QuadraticOptimality.Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (M : E →L[ℝ] E) (hM : M.toLinearMap.IsSymmetricCoercive)

/-- The largest actual eigenvalue of the metric Hessian, representing the original pencil. -/
noncomputable def greatestEigenvalue (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (hpos : 0 < Module.finrank ℝ E) : ℝ :=
  (hessian_symmetric M hM hH).greatestEigenvalue
    (WithEnergy.equiv M.toLinearMap hM).symm.finrank_eq hpos

/-- The actual largest generalized eigenvalue bounds the energy Hessian quadratic form. -/
theorem inner_hessian_le_greatestEigenvalue (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (hpos : 0 < Module.finrank ℝ E)
    (v : WithEnergy M.toLinearMap hM) :
    inner ℝ (hessian M hM H v) v ≤ greatestEigenvalue M hM H hH hpos * ‖v‖ ^ 2 :=
  (hessian_symmetric M hM hH).inner_apply_le_greatestEigenvalue
    (WithEnergy.equiv M.toLinearMap hM).symm.finrank_eq hpos v
end QuadraticOptimality.Metric
