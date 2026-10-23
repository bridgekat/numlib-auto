import Numlib.Optimization.Quadratic.Optimality.MetricInverse
import Numlib.Krylov.Conjugation

/-!
# Actual preconditioned Krylov spaces in metric coordinates

The actual inverse-metric Hessian intertwines with its Riesz representative.
The finite Krylov subspaces and their true grade therefore agree exactly under
the original-coordinate map.
-/

namespace QuadraticKrylov.Metric
open QuadraticOptimality.Metric QuadraticRegularization.Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (H M : E →L[ℝ] E) (hM : M.toLinearMap.IsSymmetricCoercive)

/-- Every actual metric Krylov space maps onto the original preconditioned Krylov space. -/
theorem subspace_hessian (g : E) (m : ℕ) :
    (Krylov.subspace (hessian M hM H).toLinearMap (gradient M hM g) m).map
      (toOriginal M hM).toLinearMap =
      Krylov.subspace (M.inverse.comp H).toLinearMap (M.inverse g) m := by
  have hh := Krylov.map_subspace_of_semiconj (N := (toOriginal M hM).toLinearMap)
    (B := (hessian M hM H).toLinearMap) (C := (M.inverse.comp H).toLinearMap)
    (fun v => hessian_intertwines M hM H v) (gradient M hM g) m
  change _ = Krylov.subspace (M.inverse.comp H).toLinearMap
    (toOriginal M hM (gradient M hM g)) m at hh
  rw [gradient_intertwines] at hh
  exact hh

/-- The metric Krylov grade is the actual original preconditioned Hessian-gradient grade. -/
theorem grade_hessian (g : E) :
    Krylov.grade (hessian M hM H).toLinearMap (gradient M hM g) =
      Krylov.grade (M.inverse.comp H).toLinearMap (M.inverse g) := by
  have hh := Krylov.grade_eq_of_semiconj_equiv
    (WithEnergy.equiv M.toLinearMap hM).symm
    (A := (hessian M hM H).toLinearMap) (B := (M.inverse.comp H).toLinearMap)
    (fun v => hessian_intertwines M hM H v) (gradient M hM g)
  change _ = Krylov.grade (M.inverse.comp H).toLinearMap
    (toOriginal M hM (gradient M hM g)) at hh
  rw [gradient_intertwines] at hh
  exact hh
end QuadraticKrylov.Metric
