import Numlib.Analysis.InnerProductSpace.Energy

/-!
# Weighted Euclidean norms

Appendix A.2's inner-product norm convention, with the positive definite matrix
inner product used throughout the book. The norm and induced space are the existing
`energyNorm` and `WithEnergy`; ordinary finite `ℓp` spaces retain Mathlib's `WithLp` norms.
-/

namespace CartisGouldToint.AppendixA.Section02

variable {n : ℕ}

/-- The weighted Euclidean norm `‖x‖_M = √⟨x, Mx⟩`. Its norm properties below
require the real matrix `M` to be symmetric positive definite. -/
noncomputable abbrev weightedEuclideanNorm (M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := energyNorm (Matrix.toEuclideanLin M) x

/-- The textbook formula in the ordinary Euclidean inner product. -/
theorem weightedEuclideanNorm_eq_sqrt (M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    weightedEuclideanNorm M x = Real.sqrt (inner ℝ x (Matrix.toEuclideanLin M x)) := by
  simp only [weightedEuclideanNorm, energyNorm, RCLike.re_to_real]
  rw [real_inner_comm]

/-- The weighted norm is the genuine norm of the existing induced inner-product space. -/
theorem weightedEuclideanNorm_eq_norm (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) :
    weightedEuclideanNorm M x =
      ‖WithEnergy.equiv (Matrix.toEuclideanLin M) hM.isSymmetricCoercive_toEuclideanLin x‖ := rfl

/-- A weighted Euclidean norm is nonnegative. -/
theorem weightedEuclideanNorm_nonneg (M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ weightedEuclideanNorm M x :=
  energyNorm_nonneg _ _

/-- A positive definite weight gives a definite norm. -/
@[simp] theorem weightedEuclideanNorm_eq_zero_iff (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    weightedEuclideanNorm M x = 0 ↔ x = 0 :=
  hM.isSymmetricCoercive_toEuclideanLin.energyNorm_eq_zero_iff

/-- A positive definite weight gives a strictly positive norm away from zero. -/
theorem weightedEuclideanNorm_pos (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) : 0 < weightedEuclideanNorm M x :=
  hM.isSymmetricCoercive_toEuclideanLin.energyNorm_pos hx

/-- The weighted and ordinary Euclidean norms are equivalent, with positive constants
independent of the vector. This includes the zero-dimensional space. -/
theorem weightedEuclideanNorm_equivalent (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      c * ‖x‖ ≤ weightedEuclideanNorm M x ∧ weightedEuclideanNorm M x ≤ C * ‖x‖ := by
  let A := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
  have hA : (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetricCoercive :=
    hM.isSymmetricCoercive_toEuclideanLin
  obtain ⟨c, hc, hco⟩ := hA.isCoercive
  refine ⟨Real.sqrt c, Real.sqrt ‖A‖ + 1, Real.sqrt_pos.2 hc, by positivity, fun x => ?_⟩
  refine ⟨hco.norm_le_energyNorm hc.le x, ?_⟩
  exact (hA.energyNorm_le_norm x).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg x))

/-- The induced weighted norm obeys the triangle inequality. -/
theorem weightedEuclideanNorm_add_le (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (x y : EuclideanSpace ℝ (Fin n)) :
    weightedEuclideanNorm M (x + y) ≤ weightedEuclideanNorm M x + weightedEuclideanNorm M y := by
  simpa only [weightedEuclideanNorm_eq_norm M hM, map_add] using
    norm_add_le (WithEnergy.equiv (Matrix.toEuclideanLin M) hM.isSymmetricCoercive_toEuclideanLin x)
      (WithEnergy.equiv (Matrix.toEuclideanLin M) hM.isSymmetricCoercive_toEuclideanLin y)

/-- Scalar homogeneity of the induced weighted norm. -/
theorem weightedEuclideanNorm_smul (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    weightedEuclideanNorm M (r • x) = |r| * weightedEuclideanNorm M x := by
  simp only [weightedEuclideanNorm_eq_norm M hM, map_smul, norm_smul, Real.norm_eq_abs]

end CartisGouldToint.AppendixA.Section02
