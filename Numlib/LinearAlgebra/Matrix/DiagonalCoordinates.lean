import Numlib.LinearAlgebra.Matrix.AbsoluteScaling
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.InnerProductSpace.Energy

/-!
# Coordinates for positive diagonal congruences

A positive diagonal weight and a unitary basis give an invertible square-root coordinate change.
-/

open scoped InnerProductSpace
open Unitary

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Square-root coordinate matrix for positive diagonal weights in a unitary basis. -/
noncomputable def diagonalCoordinateMatrix (V : unitaryGroup n ℝ) (a : n → ℝ) :
    Matrix n n ℝ := diagonal (fun i => Real.sqrt (a i)) * star V.val

/-- Inverse square-root coordinate matrix. -/
noncomputable def diagonalRecoveryMatrix (V : unitaryGroup n ℝ) (a : n → ℝ) :
    Matrix n n ℝ := V.val * diagonal (fun i => (Real.sqrt (a i))⁻¹)

/-- In standard coordinates the coordinate matrix is the square-root diagonal. -/
@[simp] theorem diagonalCoordinateMatrix_one (a : n → ℝ) :
    diagonalCoordinateMatrix (1 : unitaryGroup n ℝ) a =
      diagonal (fun i => Real.sqrt (a i)) := by simp [diagonalCoordinateMatrix]

/-- In standard coordinates recovery is the inverse-square-root diagonal. -/
@[simp] theorem diagonalRecoveryMatrix_one (a : n → ℝ) :
    diagonalRecoveryMatrix (1 : unitaryGroup n ℝ) a =
      diagonal (fun i => (Real.sqrt (a i))⁻¹) := by simp [diagonalRecoveryMatrix]

/-- The inverse transpose gives the transformed-gradient matrix. -/
theorem diagonalRecoveryMatrix_transpose (V : unitaryGroup n ℝ) (a : n → ℝ) :
    (diagonalRecoveryMatrix V a)ᵀ =
      diagonal (fun i => (Real.sqrt (a i))⁻¹) * V.valᵀ := by
  simp [diagonalRecoveryMatrix, transpose_mul]

/-- The coordinate matrix followed by recovery is the identity. -/
theorem diagonalCoordinateMatrix_mul_recovery (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) : diagonalCoordinateMatrix V a * diagonalRecoveryMatrix V a = 1 := by
  simp only [diagonalCoordinateMatrix, diagonalRecoveryMatrix, ← mul_assoc]
  rw [mul_assoc (diagonal _), Unitary.coe_star_mul_self, mul_one,
    diagonal_mul_diagonal]
  have h : (fun i => Real.sqrt (a i) * (Real.sqrt (a i))⁻¹) = fun _ => (1 : ℝ) := by
    ext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (ha i)).ne'
  rw [h, diagonal_one]

/-- Recovery followed by the coordinate matrix is the identity. -/
theorem diagonalRecoveryMatrix_mul_coordinate (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) : diagonalRecoveryMatrix V a * diagonalCoordinateMatrix V a = 1 := by
  simp only [diagonalCoordinateMatrix, diagonalRecoveryMatrix, mul_assoc]
  rw [← mul_assoc (diagonal _), diagonal_mul_diagonal]
  have h : (fun i => (Real.sqrt (a i))⁻¹ * Real.sqrt (a i)) = fun _ => (1 : ℝ) := by
    ext i
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (ha i)).ne'
  rw [h, diagonal_one, one_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self]

/-- The invertible linear change of coordinates given by the square-root metric. -/
noncomputable def diagonalCoordinateEquiv (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) : EuclideanSpace ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ n where
  toLinearMap := toEuclideanLin (diagonalCoordinateMatrix V a)
  invFun := toEuclideanLin (diagonalRecoveryMatrix V a)
  left_inv x := by
    change toEuclideanLin _ (toEuclideanLin _ x) = x
    rw [← toEuclideanLin_mul_apply, diagonalRecoveryMatrix_mul_coordinate V ha]
    simp
  right_inv x := by
    change toEuclideanLin _ (toEuclideanLin _ x) = x
    rw [← toEuclideanLin_mul_apply, diagonalCoordinateMatrix_mul_recovery V ha]
    simp

/-- The coordinate equivalence applies the concrete square-root coordinate matrix. -/
@[simp] theorem diagonalCoordinateEquiv_apply (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (x : EuclideanSpace ℝ n) :
    diagonalCoordinateEquiv V ha x = toEuclideanLin (diagonalCoordinateMatrix V a) x := rfl

/-- The inverse equivalence applies the concrete recovery matrix. -/
@[simp] theorem diagonalCoordinateEquiv_symm_apply (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (x : EuclideanSpace ℝ n) :
    (diagonalCoordinateEquiv V ha).symm x =
      toEuclideanLin (diagonalRecoveryMatrix V a) x := rfl

/-- The coordinate matrix factors the positive spectral metric. -/
theorem diagonalCoordinateMatrix_transpose_mul (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) :
    (diagonalCoordinateMatrix V a)ᵀ * diagonalCoordinateMatrix V a =
      unitaryDiagonalScaling V a := by
  simp only [diagonalCoordinateMatrix, unitaryDiagonalScaling_eq,
    star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, transpose_mul,
    transpose_transpose, diagonal_transpose, mul_assoc]
  rw [← mul_assoc (diagonal _), diagonal_mul_diagonal]
  have h : (fun i => Real.sqrt (a i) * Real.sqrt (a i)) = a := by
    ext i
    exact Real.mul_self_sqrt (ha i).le
  rw [h]

/-- The metric norm is exactly the ordinary norm of the new coordinates. -/
theorem energyNorm_diagonalCoordinateEquiv (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (x : EuclideanSpace ℝ n) :
    energyNorm (toEuclideanLin (unitaryDiagonalScaling V a)) x =
      ‖diagonalCoordinateEquiv V ha x‖ := by
  rw [energyNorm, ← diagonalCoordinateMatrix_transpose_mul V ha, toEuclideanLin_mul_apply,
    toEuclideanLin_transpose_inner_left, real_inner_self_eq_norm_sq]
  exact Real.sqrt_sq (norm_nonneg _)

/-- Congruence by the recovery matrix divides each diagonal Hessian entry by its metric weight. -/
theorem diagonalRecoveryMatrix_congruence (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (d : n → ℝ) :
    (diagonalRecoveryMatrix V a)ᵀ * unitaryDiagonalScaling V d *
      diagonalRecoveryMatrix V a = diagonal (fun i => d i / a i) := by
  rw [diagonalRecoveryMatrix_transpose, ← conjTranspose_eq_transpose_of_trivial,
    ← star_eq_conjTranspose]
  simp only [diagonalRecoveryMatrix, unitaryDiagonalScaling_eq,
    ← conjTranspose_eq_transpose_of_trivial,
    ← star_eq_conjTranspose]
  calc
    _ = diagonal (fun i => (Real.sqrt (a i))⁻¹) * (star V.val * V.val) *
        diagonal d * (star V.val * V.val) * diagonal (fun i => (Real.sqrt (a i))⁻¹) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [Unitary.coe_star_mul_self, mul_one, mul_one,
        diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      ext i
      have hn := (Real.sqrt_pos.mpr (ha i)).ne'
      field_simp [hn, (ha i).ne']
      rw [Real.sq_sqrt (ha i).le]
      ring

/-- Transforming a linear term by the inverse transpose preserves its value. -/
theorem inner_diagonalCoordinateEquiv (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (g x : EuclideanSpace ℝ n) :
    inner ℝ (toEuclideanLin (diagonalRecoveryMatrix V a)ᵀ g)
      (diagonalCoordinateEquiv V ha x) = inner ℝ g x := by
  rw [toEuclideanLin_transpose_inner_left]
  exact congrArg (inner ℝ g) ((diagonalCoordinateEquiv V ha).symm_apply_apply x)

/-- The Hessian transforms by the actual inverse congruence. -/
theorem inner_hessian_diagonalCoordinateEquiv (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (H : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    inner ℝ (diagonalCoordinateEquiv V ha x)
      (toEuclideanLin ((diagonalRecoveryMatrix V a)ᵀ * H * diagonalRecoveryMatrix V a)
        (diagonalCoordinateEquiv V ha x)) = inner ℝ x (toEuclideanLin H x) := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_transpose_inner_right]
  have h : toEuclideanLin (diagonalRecoveryMatrix V a) (diagonalCoordinateEquiv V ha x) = x :=
    (diagonalCoordinateEquiv V ha).symm_apply_apply x
  rw [h]

end Matrix
