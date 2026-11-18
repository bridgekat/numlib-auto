/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares.Reduced

/-!
# Computation of least-squares solutions

Section 7.6 of [benIsrael2003generalized] reduces the normal equations using a factorization
with a full-row-rank right factor. With orthonormal columns in the left factor, the reduced
system is the thin QR system.

## Main declarations

* `BenIsraelGreville.Chapter07.leastSquaresResidual` is the residual $b-Ax$.
* `BenIsraelGreville.Chapter07.isLeastSquaresSolution_iff_factor_normalEquations` gives the
  normal equations after canceling the adjoint of the full-row-rank factor.
* `BenIsraelGreville.Chapter07.isLeastSquaresSolution_iff_thinQR` gives the thin QR system.

## Deviations from the source

* **Equation (65)** (correction). The full rotated equation also imposes consistency of the
  discarded rows. Equation (66) uses the leading rows and is valid for every right-hand side.
-/

namespace BenIsraelGreville.Chapter07

open Matrix

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n]

/-- **Equation (62)** of [benIsrael2003generalized]. The **residual** for $A x=b$ at $x$
is $b-Ax$. -/
noncomputable def leastSquaresResidual (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ m :=
  b - toEuclideanLin A x

/-- **Equations (63)–(64)** of [benIsrael2003generalized]. Let $A = FG$ with $G$ of full row
rank. A vector $x$ minimizes the Euclidean norm of the residual for $Ax=b$ if and only if
$F^H A x = F^H b$. -/
theorem isLeastSquaresSolution_iff_factor_normalEquations
    {A : Matrix m n ℂ} {F : Matrix m k ℂ} {G : Matrix k n ℂ} (hA : A = F * G)
    (hG : LinearIndependent ℂ G) {x : EuclideanSpace ℂ n} {b : EuclideanSpace ℂ m} :
    IsLeastSquaresSolution A b x ↔
      toEuclideanLin Fᴴ (toEuclideanLin A x) = toEuclideanLin Fᴴ b :=
  Matrix.isLeastSquaresSolution_iff_fullRowRank_factor_normalEquations hA hG

/-- **Equation (66)** of [benIsrael2003generalized]. Let $A = \widetilde Q \widetilde R$,
where $\widetilde Q^H \widetilde Q=I$ and $\widetilde R$ is an invertible upper triangular
matrix. A vector $x$ is a least-squares solution if and only if
$\widetilde R x = \widetilde Q^H b$.

**Correction.** Equation (65) uses the full unitary completion $Q$ on both sides. Its equality
$Q^H Ax=Q^H b$ implies $Ax=b$, which can fail even when a least-squares solution exists.
The leading block expressed in Equation (66) gives the least-squares criterion. -/
theorem isLeastSquaresSolution_iff_thinQR [LinearOrder n]
    {A : Matrix m n ℂ} {Q : Matrix m n ℂ} {R : Matrix n n ℂ}
    (hA : A = Q * R) (hQ : Qᴴ * Q = 1) (hR : IsUnit R)
    (_htriangular : R.BlockTriangular id)
    {x : EuclideanSpace ℂ n} {b : EuclideanSpace ℂ m} :
    IsLeastSquaresSolution A b x ↔ toEuclideanLin R x = toEuclideanLin Qᴴ b := by
  have hrows : LinearIndependent ℂ R.row :=
    Matrix.vecMul_injective_iff.mp (Matrix.vecMul_injective_iff_isUnit.mpr hR)
  exact Matrix.isLeastSquaresSolution_iff_isometricFactor hA hQ hrows

end BenIsraelGreville.Chapter07
