import NumlibSurface.CartisGouldToint.Chapter10.Section02

/-!
# Chapter 10, Section 3: trust-region Lanczos residuals

The multiplier interface is exactly the necessary and sufficient reduced trust-region
optimality conditions. The residual is the actual original shifted gradient, and its
bound uses the actual subspace step and dual metric. Cyclicity excludes singular
shifted reduced matrices even when the multiplier vanishes.
-/

noncomputable section
open scoped InnerProductSpace
open Set Metric Optimization.KrylovSubproblem Optimization.QuadraticSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
open CartisGouldToint.Chapter10.Section02
namespace CartisGouldToint.Chapter10.Section03
variable {n m : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}

/-- The actual residual (10.3.1) for the supplied primal step and its multiplier. -/
def trustRegionLanczosResidual (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (lambda : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  g + Matrix.toEuclideanLin H s + lambda • Matrix.toEuclideanLin M s

/-- The associated reduced trust-region multiplier: primal feasibility, shifted
stationarity, positive semidefiniteness and complementarity. These are precisely
the global reduced optimality conditions, not an assumption about the residual bound. -/
def IsTrustRegionLanczosMultiplier (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (delta lambda : ℝ)
    (y : EuclideanSpace ℝ (Fin (m + 1))) : Prop :=
  let b := hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
  let T := LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin (Lanczos.tridiag (secularHessian H hM) b (m + 1)))
  ‖y‖ ≤ delta ∧ 0 ≤ lambda ∧
    ‖b‖ • EuclideanSpace.single 0 1 + T y + lambda • y = 0 ∧
    (T + lambda • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (m + 1)))).IsPositive ∧
    lambda * (‖y‖ ^ 2 - delta ^ 2) = 0

/-- A feasible reduced global minimizer has exactly an associated multiplier in
the above interface. Inactive-radius and zero-multiplier cases are included. -/
theorem isMinOn_reduced_trustRegion_iff (hM : M.PosDef) {delta : ℝ}
    (hdelta : 0 < delta) (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (‖y‖ ≤ delta ∧ IsMinOn
      (quadratic
        (‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖ •
          EuclideanSpace.single 0 1)
        (Matrix.toEuclideanLin
          (Lanczos.tridiag (secularHessian H hM)
            (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
            (m + 1))).toContinuousLinearMap) (closedBall 0 delta) y) ↔
      ∃ lambda, IsTrustRegionLanczosMultiplier H hM g delta lambda y := by
  have hsym := (Lanczos.tridiag_isSymm (secularHessian H hM)
    (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
    (m + 1)).isSymmetric_toEuclideanLin
  simpa only [IsTrustRegionLanczosMultiplier, exists_and_left] using
    isMinOn_ball_iff_shift
      (H := (Matrix.toEuclideanLin
        (Lanczos.tridiag (secularHessian H hM)
          (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
          (m + 1))).toContinuousLinearMap)
      (g := ‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖ •
        EuclideanSpace.single 0 1)
      (by simpa only [LinearMap.coe_toContinuousLinearMap] using hsym)
      hdelta (s := y)

/-- Theorem 10.3.2: the actual trust-region residual has the geometric bound for
any positive spectral enclosure of its actual shifted reduced matrix. -/
theorem theorem_10_3_2 (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    (hm : m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
    {delta lambda a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hC0 : 0 ≤ C) (hC : ∀ z, ‖secularHessian H hM z‖ ≤ C * ‖z‖)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hKKT : IsTrustRegionLanczosMultiplier H hM g delta lambda y)
    (hB : (Matrix.toEuclideanLin
      (Lanczos.tridiag (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) (m + 1) +
          lambda • 1)).IsSymmetricBoundedBy a b) :
    weightedNorm M⁻¹ (trustRegionLanczosResidual g H M lambda (lanczosPrimalStep H hM g y)) ≤
      2 * C * (b / a) * delta *
        ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ m := by
  have hgn : hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g) ≠ 0 := by
    intro hb
    have hzero : Matrix.toEuclideanLin M⁻¹ g = 0 :=
      hM.isPreconditioner_toEuclideanLin.toEnergy.map_eq_zero_iff.mp hb
    apply hg
    simpa only [map_zero, hM.isPreconditioner_toEuclideanLin.apply_inv] using
      congrArg (Matrix.toEuclideanLin M) hzero
  obtain ⟨hy, _, hstat, hpos, _⟩ := hKKT
  have hstat' :
      ‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖ •
          EuclideanSpace.single 0 1 +
        Matrix.toEuclideanLin
          (Lanczos.tridiag (secularHessian H hM)
            (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) (m + 1)) y +
        lambda • y = 0 := by
    simpa only [LinearMap.coe_toContinuousLinearMap'] using hstat
  have hspec := lanczos_shift_posDef_of_stationary hgn hm lambda hstat' hpos
  rw [trustRegionLanczosResidual, ← lanczosPrimalStep_residual_norm hM y]
  exact lanczos_subproblem_residual_bound (secularHessian_isSymmetric hH hM) hgn
    hC0 hC ha hab m hm lambda y hy hB hspec.1

end CartisGouldToint.Chapter10.Section03
