import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized

/-!
# Quadratic models from linearized least squares

The normal-equation and pseudoinverse interfaces supply the Gram structure and its range
property directly, including rank-deficient models.
-/

noncomputable section
namespace Matrix.LeastSquaresModel

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The half squared norm of an affine residual. -/
def value (J : Matrix ι κ ℝ) (r : EuclideanSpace ℝ ι) (s : EuclideanSpace ℝ κ) : ℝ :=
  ‖r + toEuclideanLin J s‖ ^ 2 / 2

omit [DecidableEq ι] in
/-- The model at zero is the half squared residual norm. -/
@[simp] theorem value_zero (J : Matrix ι κ ℝ) (r : EuclideanSpace ℝ ι) :
    value J r 0 = ‖r‖ ^ 2 / 2 := by simp [value]

/-- The exact normal-equation gradient of an affine least-squares model. -/
theorem hasGradientAt_value (J : Matrix ι κ ℝ) (r : EuclideanSpace ℝ ι)
    (s : EuclideanSpace ℝ κ) :
    HasGradientAt (value J r) (toEuclideanLin Jᵀ (r + toEuclideanLin J s)) s := by
  change HasGradientAt (fun y => ‖r + toEuclideanLin J y‖ ^ 2 / 2) _ s
  simpa [sub_neg_eq_add, add_comm] using hasGradientAt_leastSquaresObjective J (-r) s

/-- The gradient decomposes into its constant vector and Gram matrix. -/
theorem hasGradientAt_value_gram (J : Matrix ι κ ℝ) (r : EuclideanSpace ℝ ι)
    (s : EuclideanSpace ℝ κ) : HasGradientAt (value J r)
      (toEuclideanLin Jᵀ r + toEuclideanLin (Jᵀ * J) s) s := by
  simpa only [map_add, toEuclideanLin_mul_apply] using hasGradientAt_value J r s

/-- The actual quadratic expansion of an affine least-squares model. -/
theorem value_eq_quadratic (J : Matrix ι κ ℝ) (r : EuclideanSpace ℝ ι)
    (s : EuclideanSpace ℝ κ) : value J r s = ‖r‖ ^ 2 / 2 +
      inner ℝ (toEuclideanLin Jᵀ r) s + inner ℝ s (toEuclideanLin (Jᵀ * J) s) / 2 := by
  have hg : inner ℝ (toEuclideanLin Jᵀ r) s = inner ℝ r (toEuclideanLin J s) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      toEuclideanLin_conjTranspose_inner_left J s r
  have hq : ‖toEuclideanLin J s‖ ^ 2 = inner ℝ s (toEuclideanLin (Jᵀ * J) s) := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [conjTranspose_eq_transpose_of_trivial] using J.inner_toEuclideanLin_apply s s
  rw [value, norm_add_sq_real, ← hg, hq]
  ring

omit [DecidableEq ι] [DecidableEq κ] [Fintype κ] in
/-- Every least-squares Gram matrix is positive semidefinite. -/
theorem gram_posSemidef [Finite κ] (J : Matrix ι κ ℝ) : (Jᵀ * J).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self J

/-- The constant gradient lies in the Gram matrix range, even when it is singular. -/
theorem constantGradient_mem_range_gram (J : Matrix ι κ ℝ) (r : EuclideanSpace ℝ ι) :
    toEuclideanLin Jᵀ r ∈ LinearMap.range (toEuclideanLin (Jᵀ * J)) := by
  refine ⟨toEuclideanLin J.pinv r, ?_⟩
  simpa only [conjTranspose_eq_transpose_of_trivial] using normalEquations_pinv J r

end Matrix.LeastSquaresModel
