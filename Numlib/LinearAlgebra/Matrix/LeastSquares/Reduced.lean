/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares

/-!
# Reduced normal equations

A matrix factorization $A = F G$ with $G$ of full row rank reduces the normal equation
$A^H A x = A^H b$ to $F^H A x = F^H b$. With an isometric left factor $Q$, the thin QR
equation is $R x = Q^H b$.
-/

namespace Matrix

open scoped ComplexOrder

variable {𝕜 m n k : Type*} [RCLike 𝕜]
  [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]

/-- If $A = F G$ and $G^H$ acts injectively, then $x$ minimizes the residual of $A x = b$
if and only if $F^H A x = F^H b$. -/
theorem isLeastSquaresSolution_iff_leftFactor_normalEquations
    [DecidableEq k] {A : Matrix m n 𝕜} {F : Matrix m k 𝕜} {G : Matrix k n 𝕜} (hA : A = F * G)
    (hG : Function.Injective (toEuclideanLin Gᴴ))
    {x : EuclideanSpace 𝕜 n} {b : EuclideanSpace 𝕜 m} :
    IsLeastSquaresSolution A b x ↔
      toEuclideanLin Fᴴ (toEuclideanLin A x) = toEuclideanLin Fᴴ b := by
  rw [isLeastSquaresSolution_iff_normalEquations, toEuclideanLin_mul_apply]
  have hAH : Aᴴ = Gᴴ * Fᴴ := by rw [hA, conjTranspose_mul]
  simp only [hAH, toEuclideanLin_mul_apply]
  exact hG.eq_iff

/-- If $A = F G$ and $G$ has full row rank, then $x$ minimizes the residual of $A x = b$
if and only if $F^H A x = F^H b$. -/
theorem isLeastSquaresSolution_iff_fullRowRank_factor_normalEquations
    {A : Matrix m n 𝕜} {F : Matrix m k 𝕜} {G : Matrix k n 𝕜} (hA : A = F * G)
    (hG : LinearIndependent 𝕜 G) {x : EuclideanSpace 𝕜 n} {b : EuclideanSpace 𝕜 m} :
    IsLeastSquaresSolution A b x ↔
      toEuclideanLin Fᴴ (toEuclideanLin A x) = toEuclideanLin Fᴴ b := by
  classical
  refine isLeastSquaresSolution_iff_leftFactor_normalEquations hA ?_
  have hunit := (posDef_self_mul_conjTranspose_of_linearIndependent hG).isUnit
  have hleft : (G * Gᴴ)⁻¹ * G * Gᴴ = 1 := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit)]
  refine Function.LeftInverse.injective (g := toEuclideanLin ((G * Gᴴ)⁻¹ * G)) ?_
  intro z
  rw [← toEuclideanLin_mul_apply, hleft, toEuclideanLin_one, LinearMap.id_apply]

/-- If $A = Q R$, $Q^H Q = I$, and $R$ has full row rank, then $x$ minimizes the residual
of $A x = b$ if and only if $R x = Q^H b$. -/
theorem isLeastSquaresSolution_iff_isometricFactor
    [DecidableEq k] {A : Matrix m n 𝕜} {Q : Matrix m k 𝕜} {R : Matrix k n 𝕜}
    (hA : A = Q * R) (hQ : Qᴴ * Q = 1) (hR : LinearIndependent 𝕜 R)
    {x : EuclideanSpace 𝕜 n} {b : EuclideanSpace 𝕜 m} :
    IsLeastSquaresSolution A b x ↔ toEuclideanLin R x = toEuclideanLin Qᴴ b := by
  rw [isLeastSquaresSolution_iff_fullRowRank_factor_normalEquations hA hR,
    ← toEuclideanLin_mul_apply, hA, ← Matrix.mul_assoc, hQ, Matrix.one_mul]

end Matrix
