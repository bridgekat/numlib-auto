import NumlibSurface.CartisGouldToint.Chapter10.Section01.LanczosIdentities
import Numlib.Optimization.KrylovSubproblemBounds

/-!
# Chapter 10, Section 2: regularized Lanczos subproblems

The reduced model uses the actual Lanczos tridiagonal in the metric energy space.
Its multiplier is the radial derivative at the actual reduced global minimizer.
Cyclicity excludes an internal hard case, and Chebyshev coordinate decay bounds
the actual full model gradient in the dual metric.
-/

noncomputable section
open scoped InnerProductSpace
open Set Optimization.KrylovSubproblem Optimization.QuadraticSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter10.Section02
variable {n m : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}

/-- The actual radial multiplier (10.2.3) of a represented reduced step. -/
def reducedRegularizationMultiplier {k : ℕ} (sigma r : ℝ)
    (y : EuclideanSpace ℝ (Fin k)) : ℝ := sigma * ‖y‖ ^ (r - 2)

/-- The exact reduced model (10.1.6) in the actual energy-space Lanczos basis. -/
def reducedLanczosModel (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (m : ℕ) (sigma r : ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) → ℝ :=
  let b := hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
  powerRegularizedQuadratic (‖b‖ • EuclideanSpace.single 0 1)
    (LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (Lanczos.tridiag (secularHessian H hM) b (m + 1)))) sigma r

/-- The actual represented step in the original primal coordinates. -/
def lanczosPrimalStep (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  hM.isPreconditioner_toEuclideanLin.toEnergy.symm
    (lanczosStep (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) y)

/-- The energy-space gradient norm is exactly the dual metric norm of the original
model gradient. This identity uses the actual primal step, not a residual certificate. -/
theorem lanczosPrimalStep_residual_norm (hM : M.PosDef)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (lambda : ℝ) :
    let hp := hM.isPreconditioner_toEuclideanLin
    let b := hp.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
    let z := lanczosStep (secularHessian H hM) b y
    ‖b + secularHessian H hM z + lambda • z‖ =
      weightedNorm M⁻¹ (g + Matrix.toEuclideanLin H (lanczosPrimalStep H hM g y) +
        lambda • Matrix.toEuclideanLin M (lanczosPrimalStep H hM g y)) := by
  dsimp only
  let hp := hM.isPreconditioner_toEuclideanLin
  let s := lanczosPrimalStep H hM g y
  have hre : hp.toEnergy s = lanczosStep (secularHessian H hM)
      (hp.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) y := hp.toEnergy.apply_symm_apply _
  rw [← hre]
  have he : hp.toEnergy (Matrix.toEuclideanLin M⁻¹ g) +
      secularHessian H hM (hp.toEnergy s) + lambda • hp.toEnergy s =
      hp.toEnergy (Matrix.toEuclideanLin M⁻¹ (g + Matrix.toEuclideanLin H s +
        lambda • Matrix.toEuclideanLin M s)) := by
    change hp.toEnergy (Matrix.toEuclideanLin M⁻¹ g) +
      energyHessian hp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
        (hp.toEnergy s) + lambda • hp.toEnergy s = _
    rw [energyHessian_apply]
    simp only [map_add, map_smul, hp.inv_apply]
    rfl
  rw [he]
  rw [← Real.sqrt_sq (norm_nonneg _), hp.norm_toEnergy_inv_sq]
  rfl

/-- The source multiplier has the stationary system (10.2.2), and the shifted
unreduced matrix is positive definite, including at the final grade. -/
theorem reducedRegularizationMultiplier_spec (hM : M.PosDef) (hg : g ≠ 0)
    (hm : m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
    {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hmin : IsMinOn (reducedLanczosModel H hM g m sigma r) univ y) :
    let b := hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
    let T := Lanczos.tridiag (secularHessian H hM) b (m + 1)
    (∀ i, T.mulVec y i + reducedRegularizationMultiplier sigma r y * y i =
      -(if i = 0 then ‖b‖ else 0)) ∧
    (T + reducedRegularizationMultiplier sigma r y • 1).PosDef := by
  apply lanczos_regularized_shift_posDef (hm := hm) (hsigma := hsigma) (hr := hr)
    (hmin := hmin)
  intro hb
  have hzero : Matrix.toEuclideanLin M⁻¹ g = 0 :=
    hM.isPreconditioner_toEuclideanLin.toEnergy.map_eq_zero_iff.mp hb
  apply hg
  have h := congrArg (Matrix.toEuclideanLin M) hzero
  simpa only [map_zero, hM.isPreconditioner_toEuclideanLin.apply_inv] using h

/-- Theorem 10.2.2: the actual model gradient obeys the geometric estimate. Any
positive spectral enclosure of the actual shifted reduced matrix may be used;
choosing its extreme eigenvalues gives the source condition number. -/
theorem theorem_10_2_2 (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    (hm : m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
    {sigma r a b C : ℝ} (hsigma : 0 < sigma) (hr : 2 < r) (ha : 0 < a) (hab : a ≤ b)
    (hC0 : 0 ≤ C) (hC : ∀ z, ‖secularHessian H hM z‖ ≤ C * ‖z‖)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hmin : IsMinOn (reducedLanczosModel H hM g m sigma r) univ y)
    (hB : (Matrix.toEuclideanLin
      (Lanczos.tridiag (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) (m + 1) +
          reducedRegularizationMultiplier sigma r y • 1)).IsSymmetricBoundedBy a b) :
    weightedNorm M⁻¹ (g + Matrix.toEuclideanLin H (lanczosPrimalStep H hM g y) +
      reducedRegularizationMultiplier sigma r y •
        Matrix.toEuclideanLin M (lanczosPrimalStep H hM g y)) ≤
      2 * C * (b / a) *
        (reducedRegularizationMultiplier sigma r y / sigma) ^ (1 / (r - 2)) *
          ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ m := by
  have hspec := reducedRegularizationMultiplier_spec hM hg hm hsigma.le hr hmin
  dsimp only at hspec
  have hgn : hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g) ≠ 0 := by
    intro hb
    have hzero : Matrix.toEuclideanLin M⁻¹ g = 0 :=
      hM.isPreconditioner_toEuclideanLin.toEnergy.map_eq_zero_iff.mp hb
    apply hg
    simpa only [map_zero, hM.isPreconditioner_toEuclideanLin.apply_inv] using
      congrArg (Matrix.toEuclideanLin M) hzero
  have hnorm : (reducedRegularizationMultiplier sigma r y / sigma) ^ (1 / (r - 2)) = ‖y‖ := by
    rw [reducedRegularizationMultiplier, mul_div_cancel_left₀ _ hsigma.ne', one_div,
      Real.rpow_rpow_inv (norm_nonneg _) (by linarith : r - 2 ≠ 0)]
  rw [← lanczosPrimalStep_residual_norm hM y, hnorm]
  exact lanczos_subproblem_residual_bound (secularHessian_isSymmetric hH hM) hgn
    hC0 hC ha hab m hm _ y le_rfl hB hspec.1

end CartisGouldToint.Chapter10.Section02
