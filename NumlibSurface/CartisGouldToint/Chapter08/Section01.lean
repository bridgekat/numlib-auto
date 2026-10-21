import Numlib.Optimization.WeightedQuadraticSubproblem

/-!
# Chapter 8, Section 1: the context of the step computation

The quadratic model and its trust-region and power-regularized subproblems, with an arbitrary
symmetric positive definite scaling matrix. The norm is the square root of the matrix quadratic
form, as in the source, and minimizers refer to the actual objectives.
-/

open scoped InnerProductSpace
open Set

namespace CartisGouldToint.Chapter08.Section01

variable {n : ℕ}

/-- The quadratic model (8.1.1). -/
noncomputable def quadraticModel (g : EuclideanSpace ℝ (Fin n)) (H : Matrix (Fin n) (Fin n) ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner ℝ g s + (1 / 2 : ℝ) * inner ℝ s (Matrix.toEuclideanLin H s)

/-- The matrix norm used in (8.1.2)–(8.1.4), for positive definite `M`. -/
noncomputable def weightedNorm (M : Matrix (Fin n) (Fin n) ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (inner ℝ s (Matrix.toEuclideanLin M s))

/-- A feasible global minimizer of the trust-region subproblem (8.1.2). -/
def trustRegionMinimizer (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (delta : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  weightedNorm M s ≤ delta ∧
    IsMinOn (quadraticModel g H) {x | weightedNorm M x ≤ delta} s

/-- The regularized model (8.1.4). -/
noncomputable def regularizedModel (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (sigma r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  quadraticModel g H s + sigma / r * weightedNorm M s ^ r

/-- A global minimizer of the regularized subproblem (8.1.3). -/
def regularizedMinimizer (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (sigma r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsMinOn (regularizedModel g H M sigma r) univ s

/-- Identification of the source norm with the reusable energy norm. -/
theorem weightedNorm_eq_energyNorm (M : Matrix (Fin n) (Fin n) ℝ)
    (s : EuclideanSpace ℝ (Fin n)) :
    weightedNorm M s = energyNorm (Matrix.toEuclideanLin M) s := by
  simp only [weightedNorm, energyNorm, RCLike.re_to_real, real_inner_comm]

/-- Identification of the source quadratic model with the backbone objective. -/
theorem quadraticModel_eq_quadratic (g : EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) :
    quadraticModel g H = Optimization.QuadraticSubproblem.quadratic g
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) := rfl

/-- Identification of the source regularized model with the weighted backbone objective. -/
theorem regularizedModel_eq_weightedPowerQuadratic (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (sigma r : ℝ) :
    regularizedModel g H M sigma r = Optimization.QuadraticSubproblem.weightedPowerQuadratic
      g (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) (Matrix.toEuclideanLin M) sigma r := by
  ext s
  simp only [regularizedModel, Optimization.QuadraticSubproblem.weightedPowerQuadratic,
    quadraticModel_eq_quadratic, weightedNorm_eq_energyNorm]

end CartisGouldToint.Chapter08.Section01
