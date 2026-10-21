import Numlib.LinearAlgebra.Matrix.TridiagonalInverseDecay
import NumlibSurface.CartisGouldToint.Chapter10.Section02.ResidualIdentity

/-!
# Appendix to Chapter 10: inverse decay and exact Lanczos residuals

The inverse bound uses the actual extreme eigenvalues. Its proof constructs a
Chebyshev polynomial and uses matrix bandwidth. Residual identities delegate to
the earlier chapter's actual preconditioned Lanczos construction.
-/

noncomputable section
open scoped InnerProductSpace
open Optimization.KrylovSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
open CartisGouldToint.Chapter10.Section02
namespace CartisGouldToint.AppendixB.Chapter10
variable {n m : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}

/-- Lemma B.10.1: every inverse entry of a symmetric positive definite tridiagonal
matrix obeys the geometric estimate with its actual extreme eigenvalues. A zero-order
matrix has no entry indices; a scalar spectral interval gives zero off the diagonal. -/
theorem lemma_B_10_1 {d : ℕ} {T : Matrix (Fin d) (Fin d) ℝ}
    (hP : T.PosDef) (hT : T.IsTridiagonal) (i j : Fin d) :
    |T⁻¹ i j| ≤ (2 / (⨅ k, hP.1.eigenvalues k)) *
      ((Real.sqrt ((⨆ k, hP.1.eigenvalues k) / (⨅ k, hP.1.eigenvalues k)) - 1) /
        (Real.sqrt ((⨆ k, hP.1.eigenvalues k) / (⨅ k, hP.1.eigenvalues k)) + 1)) ^
          Nat.dist i j :=
  hP.tridiagonal_inv_entry_le hT i j

/-- Identities (B.10.1) and (B.10.2) for the actual shifted reduced solve in the
preconditioned Lanczos basis, including the zero coefficient at the grade. -/
theorem lanczosResidualIdentity (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    (hm : m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
    {lambda : ℝ} (y : EuclideanSpace ℝ (Fin (m + 1)))
    (hy : ∀ i, (Lanczos.tridiag (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
      (m + 1)).mulVec y i + lambda * y i =
        -(if i = 0 then weightedNorm M⁻¹ g else 0))
    (hunit : IsUnit (Lanczos.tridiag (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
      (m + 1) + lambda • 1)) :
    let b := hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
    let gamma := Lanczos.beta (secularHessian H hM) b m
    let T := Lanczos.tridiag (secularHessian H hM) b (m + 1) + lambda • 1
    weightedNorm M⁻¹ (g + Matrix.toEuclideanLin H (lanczosPrimalStep H hM g y) +
        lambda • Matrix.toEuclideanLin M (lanczosPrimalStep H hM g y)) =
        gamma * |y (Fin.last m)| ∧
      gamma * |y (Fin.last m)| =
        gamma * weightedNorm M⁻¹ g * |T⁻¹ (Fin.last m) 0| ∧
      (m + 1 = Krylov.grade (secularHessian H hM) b → gamma = 0) :=
  lanczosDualResidualIdentity hH hM hg hm y hy hunit

end CartisGouldToint.AppendixB.Chapter10
