/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares
import NumlibSurface.BenIsraelGreville.Chapter02.Section02

/-!
# Least-squares solutions

Section 3.1 of [benIsrael2003generalized] characterizes $\{1,3\}$-inverses as the matrices
that send every right-hand side to a least-squares solution. The least-squares solution set
is an affine space whose direction is the kernel of the original matrix.
-/

namespace BenIsraelGreville.Chapter03

open Matrix
open BenIsraelGreville.Chapter01 (definition_1 mem_one_three_iff)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {A : Matrix m n ℂ}

/-- **Section 3.1** of [benIsrael2003generalized]. A least-squares solution of $Ax=b$ is
a minimizer of the Euclidean norm of the residual. -/
abbrev leastSquaresSolution (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) : Prop :=
  IsLeastSquaresSolution A b x

/-- A vector solves least squares exactly when its image equals the image of $A^\dagger b$. -/
theorem leastSquaresSolution_iff_image_eq {b : EuclideanSpace ℂ m} {x : EuclideanSpace ℂ n} :
    leastSquaresSolution A b x ↔
      toEuclideanLin A x = toEuclideanLin A (toEuclideanLin A.pinv b) := by
  constructor
  · intro hx
    have hd := toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
      (isLeastSquaresSolution_iff_normalEquations.mp hx)
    rw [map_sub, sub_eq_zero] at hd
    exact hd
  · intro hx
    apply isLeastSquaresSolution_iff_normalEquations.mpr
    rw [toEuclideanLin_mul_apply, hx,
      ← toEuclideanLin_mul_apply, normalEquations_pinv]

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 3. A matrix $X$ maps each right-hand
side $b$ to a least-squares solution of $Ax=b$ exactly when $X$ is a $\{1,3\}$-inverse of $A$. -/
theorem theorem_1 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    X ∈ definition_1 A {.inner, .hermitianMul} ↔
      ∀ b, leastSquaresSolution A b (toEuclideanLin X b) := by
  have hp : A.pinv ∈ definition_1 A {.inner, .hermitianMul} :=
    mem_one_three_iff.mpr ⟨A.mul_pinv_mul_self, A.isHermitian_mul_pinv⟩
  rw [Chapter02.theorem_3 hp]
  simp only [leastSquaresSolution_iff_image_eq, ← toEuclideanLin_mul_apply]
  exact ⟨fun h b => congrArg (fun M => toEuclideanLin M b) h,
    fun h => toEuclideanLin.injective (LinearMap.ext h)⟩

/-- **Corollary 1** of [benIsrael2003generalized], Chapter 3. For a $\{1,3\}$-inverse $X$,
the least-squares solutions are precisely the vectors with image $AXb$, which are all vectors
of the form $Xb+(I-XA)y$. -/
theorem corollary_1 {X : Matrix n m ℂ} (hX : X ∈ definition_1 A {.inner, .hermitianMul})
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    (leastSquaresSolution A b x ↔ toEuclideanLin A x = toEuclideanLin (A * X) b) ∧
      (leastSquaresSolution A b x ↔ ∃ y : EuclideanSpace ℂ n,
        x = toEuclideanLin X b + toEuclideanLin (1 - X * A) y) := by
  have hp : A.pinv ∈ definition_1 A {.inner, .hermitianMul} :=
    mem_one_three_iff.mpr ⟨A.mul_pinv_mul_self, A.isHermitian_mul_pinv⟩
  have hEq := (Chapter02.theorem_3 hp).mp hX
  have hx : leastSquaresSolution A b x ↔ toEuclideanLin A x = toEuclideanLin (A * X) b := by
    rw [leastSquaresSolution_iff_image_eq, ← toEuclideanLin_mul_apply, hEq]
  refine ⟨hx, hx.trans ?_⟩
  constructor
  · intro h
    have hd : toEuclideanLin A (x - toEuclideanLin X b) = 0 := by
      rw [map_sub, ← toEuclideanLin_mul_apply, h, sub_self]
    refine ⟨x - toEuclideanLin X b, ?_⟩
    rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply, hd,
      map_zero, sub_zero, add_sub_cancel]
  · rintro ⟨y, rfl⟩
    have hzero : A * (1 - X * A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
        isInnerInverse_iff.mp (mem_one_three_iff.mp hX).1, sub_self]
    rw [map_add, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, hzero]
    simp only [toEuclideanLin_zero_apply, add_zero]

end BenIsraelGreville.Chapter03
