import Numlib.Analysis.InnerProductSpace.Energy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted quadratic subproblems

The source models use an actual symmetric positive-definite metric operator.
Its induced inner product and norm laws are supplied by `WithEnergy` and
`LinearMap.IsSymmetricCoercive`, rather than postulated norm properties.
-/

namespace CartisGouldToint

/-- The constant-free quadratic model (8.1.1). -/
noncomputable def quadraticModel {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner ℝ g s + inner ℝ (H s) s / 2

/-- The metric norm induced by a symmetric positive-definite operator, (8.1.2).
The accompanying hypothesis gives the induced `WithEnergy` inner product. -/
noncomputable def weightedNorm {n : ℕ}
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (_hM : M.toLinearMap.IsSymmetricCoercive) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyNorm M.toLinearMap s

/-- The regularized quadratic subproblem model (8.1.4), for source parameters
`σ>0`, `r>2`. Minimization hypotheses enter the optimality theorems. -/
noncomputable def regularizationSubproblemModel {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n))
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hM : M.toLinearMap.IsSymmetricCoercive) (σ r : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  quadraticModel g H s + σ / r * (weightedNorm M hM s) ^ r

end CartisGouldToint
