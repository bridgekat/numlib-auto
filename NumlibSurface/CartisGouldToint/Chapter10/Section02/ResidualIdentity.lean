import NumlibSurface.CartisGouldToint.Chapter10.Section02
import Numlib.Optimization.KrylovInverseResidual

/-!
# Exact dual residual identities for the reduced shifted solve

The primal step is the actual Lanczos expansion in the metric energy space. The
identities concern any nonsingular shifted reduced solve, and include the grade.
-/

noncomputable section
open scoped InnerProductSpace
open Optimization.KrylovSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter10.Section02
variable {n m : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}

/-- The norm of the actual transformed starting gradient is its original dual metric norm. -/
theorem lanczosStartingGradient_norm (hM : M.PosDef) :
    ‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖ =
      weightedNorm M⁻¹ g := by
  rw [← Real.sqrt_sq (norm_nonneg _), hM.isPreconditioner_toEuclideanLin.norm_toEnergy_inv_sq]
  rfl

/-- The full original-coordinate dual residual equals the last-coordinate expression
and the actual shifted inverse entry. The next coefficient is the energy-space Lanczos
coefficient and is zero at the grade; no normalization of a zero vector is used. -/
theorem lanczosDualResidualIdentity (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
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
      (m + 1 = Krylov.grade (secularHessian H hM) b → gamma = 0) := by
  dsimp only
  have hb : hM.isPreconditioner_toEuclideanLin.toEnergy
      (Matrix.toEuclideanLin M⁻¹ g) ≠ 0 := by
    intro he
    have hz := hM.isPreconditioner_toEuclideanLin.toEnergy.map_eq_zero_iff.mp he
    apply hg
    simpa only [map_zero, hM.isPreconditioner_toEuclideanLin.apply_inv] using
      congrArg (Matrix.toEuclideanLin M) hz
  have hsys : ∀ i, (Lanczos.tridiag (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
      (m + 1)).mulVec y i + lambda * y i =
        -(if i = 0 then
          ‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖
          else 0) := by simpa only [lanczosStartingGradient_norm hM] using hy
  have he := lanczos_shifted_residual_norm_eq_inv (secularHessian_isSymmetric hH hM)
    hb hm y hsys hunit
  rw [lanczosPrimalStep_residual_norm hM y, lanczosStartingGradient_norm hM] at he
  exact ⟨he.1, he.2, fun hgrade => (Lanczos.beta_eq_zero_iff
    (A := secularHessian H hM)
    (b := hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) m).mpr
      hgrade.ge⟩

end CartisGouldToint.Chapter10.Section02
