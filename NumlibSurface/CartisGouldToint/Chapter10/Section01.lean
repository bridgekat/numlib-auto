import Numlib.Krylov.Lanczos.Residual
import Numlib.Optimization.Quadratic.Krylov.Metric

/-!
# Actual preconditioned Lanczos subspaces and models

The canonical basis is built in the true metric inner product. The metric
Hessian and gradient are proved to be the actual inverse - metric objects in
original coordinates; the embedding preserves the metric norm exactly.
Projected regularization models use the actual Lanczos tridiagonal matrix.
-/

open Krylov QuadraticOptimality.Metric QuadraticRegularization.Metric
namespace CartisGouldToint
variable {n : ℕ}
variable (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  (hM : M.toLinearMap.IsSymmetricCoercive)

/-- The canonical actual metric - isometric embedding of the preconditioned Krylov space. -/
noncomputable def lanczosSubspaceData (g : EuclideanSpace ℝ (Fin n))
    {m : ℕ} (hm : m ≤ grade (hessian M hM H).toLinearMap (gradient M hM g)) :=
  Lanczos.basisEmbedding (hessian M hM H).toLinearMap (gradient M hM g) hm

/-- The actual projected regularized model (10.1.6), with dimension `m + 1`. -/
noncomputable def lanczosRegularizationModel (g : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (σ r : ℝ) (y : EuclideanSpace ℝ (Fin (m + 1))) :=
  QuadraticOptimality.regularized
    (Matrix.toEuclideanLin (Lanczos.tridiag (hessian M hM H).toLinearMap (gradient M hM g)
      (m + 1))).toContinuousLinearMap
    (‖gradient M hM g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) σ r y

end CartisGouldToint
