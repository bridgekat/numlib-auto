import NumlibSurface.CartisGouldToint.Chapter09.Section01
import Numlib.Optimization.WeightedPowerDerivatives

/-!
# Appendix B: factor solves and weighted model residuals

The negative differentiated shifted system uses actual step derivatives. Its forward and
diagonal solves therefore differ in sign from the positive auxiliary convention of
Algorithm 9.1.1. The pairing follows from the existing exact factor-solve interface.

The weighted model identities use actual first and second derivatives in the original
coordinates. The Hessian bound remains relative to the metric and includes the zero step.
-/

noncomputable section
namespace CartisGouldToint.AppendixB.Chapter09
open scoped InnerProductSpace
open Matrix
open Optimization.SecularResolvent
open CartisGouldToint.Chapter08.Section02
open CartisGouldToint.Chapter08.Section01

/-- The actual derivative recurrence solved through the three factors, with the negative
cross-pairing from the appendix proof of Corollary 9.1.1. -/
theorem factorizedDerivativeIdentity {n : ℕ} {g : EuclideanSpace ℝ (Fin n)}
    {H M L D : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) (hp : (H + t • M).PosDef)
    (hL : L.IsLowerTriangular) (hD : D.IsDiag) (hf : L * D * Lᵀ = H + t • M) (k : ℕ) :
    let u := iteratedDeriv k (secularStep g H M) t
    let v := iteratedDeriv (k + 1) (secularStep g H M) t
    let y := ldlForward L (-((k + 1 : ℕ) : ℝ) • Matrix.toEuclideanLin M u)
    let z := ldlDiagonal D y
    Matrix.toEuclideanLin L y = -((k + 1 : ℕ) : ℝ) • Matrix.toEuclideanLin M u ∧
      Matrix.toEuclideanLin D z = y ∧ Matrix.toEuclideanLin Lᵀ v = z ∧
      ((k + 1 : ℕ) : ℝ) * inner ℝ u (Matrix.toEuclideanLin M v) = -inner ℝ y z := by
  dsimp only
  obtain ⟨hl, hd⟩ := ldl_pivots_ne_zero hL hD hf hp.isUnit
  let u := iteratedDeriv k (secularStep g H M) t
  let v := iteratedDeriv (k + 1) (secularStep g H M) t
  let b := -((k + 1 : ℕ) : ℝ) • Matrix.toEuclideanLin M u
  let y := ldlForward L b
  let z := ldlDiagonal D y
  have hy : Matrix.toEuclideanLin L y = b := ldlForward_equation hL hl b
  have hz : Matrix.toEuclideanLin D z = y := ldlDiagonal_equation hD hd y
  have hrec : Matrix.toEuclideanLin (H + t • M) v = b :=
    ((theorem_8_2_6 (g := g) hH hM hp).2 k).2.2.1
  have hv : v = ldlSolve L D b := by
    apply hp.isSymmetricCoercive_toEuclideanLin.isCoercive.injective
    exact hrec.trans (ldlSolve_equation hL hl hD hd hf b).symm
  have hvz : Matrix.toEuclideanLin Lᵀ v = z := by
    rw [hv]
    exact ldlBackward_equation hL hl z
  refine ⟨hy, hz, hvz, ?_⟩
  have hpair := ldl_factor_pairing hy hvz hM.isHermitian.isSymm
  linarith

section Residual
variable {n : ℕ} {g s : EuclideanSpace ℝ (Fin n)}
  {H M : Matrix (Fin n) (Fin n) ℝ} {sigma r lambda : ℝ}

/-- The source objective identity obtained from its actual shifted stationarity equation. -/
theorem regularizationShift_objective_identity (hM : M.PosDef) (hr : 2 < r)
    (hstat : Matrix.toEuclideanLin (H + lambda • M) s = -g) :
    regularizedModel g H M sigma r s =
      -(1 / 2 : ℝ) * inner ℝ s (Matrix.toEuclideanLin (H + lambda • M) s) +
        weightedNorm M s ^ 2 * (sigma / r * weightedNorm M s ^ (r - 2) - lambda / 2) := by
  simpa only [regularizedModel_eq_weightedPowerQuadratic, weightedNorm_eq_energyNorm,
    toEuclideanLin_metric_shift, LinearMap.add_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe] using
    Optimization.QuadraticSubproblem.weightedPowerQuadratic_eq_of_shift
      hM.isPreconditioner_toEuclideanLin g (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) sigma hr
      ((metric_shift_stationary_iff lambda).mpr hstat)

/-- The source gradient is the actual metric-scaled radial residual. -/
theorem regularizationShift_gradient_identity (hH : H.IsSymm) (hM : M.PosDef) (hr : 2 < r)
    (hstat : Matrix.toEuclideanLin (H + lambda • M) s = -g) :
    gradient (regularizedModel g H M sigma r) s =
      (sigma * weightedNorm M s ^ (r - 2) - lambda) • Matrix.toEuclideanLin M s := by
  simpa only [regularizedModel_eq_weightedPowerQuadratic, weightedNorm_eq_energyNorm] using
    Optimization.QuadraticSubproblem.gradient_weightedPowerQuadratic_of_shift
      hM.isPreconditioner_toEuclideanLin hH.isSymmetric_toEuclideanLin sigma
      (by linarith : 1 < r) ((metric_shift_stationary_iff lambda).mpr hstat)

/-- The exact inverse-metric norm used by the source gradient stopping test. -/
theorem regularizationShift_gradient_norm_identity (hH : H.IsSymm) (hM : M.PosDef)
    (hr : 2 < r) (hstat : Matrix.toEuclideanLin (H + lambda • M) s = -g) :
    weightedNorm M⁻¹ (gradient (regularizedModel g H M sigma r) s) =
      |sigma * weightedNorm M s ^ (r - 2) - lambda| * weightedNorm M s := by
  simpa only [regularizedModel_eq_weightedPowerQuadratic, weightedNorm_eq_energyNorm] using
    Optimization.QuadraticSubproblem.energyNorm_gradient_weightedPowerQuadratic_of_shift
      hM.isPreconditioner_toEuclideanLin hH.isSymmetric_toEuclideanLin sigma
      (by linarith : 1 < r) ((metric_shift_stationary_iff lambda).mpr hstat)

/-- The actual Hessian is the shifted matrix plus the radial residual and rank-one term.
The formula also holds at zero with the usual totalized real powers. -/
theorem regularizationShift_hessian_identity (hH : H.IsSymm) (hM : M.PosDef) (hr : 2 < r)
    (u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) s u v =
      inner ℝ (Matrix.toEuclideanLin (H + lambda • M) u) v +
      (sigma * weightedNorm M s ^ (r - 2) - lambda) * inner ℝ (Matrix.toEuclideanLin M u) v +
      sigma * (r - 2) * weightedNorm M s ^ (r - 4) *
        inner ℝ (Matrix.toEuclideanLin M s) u * inner ℝ (Matrix.toEuclideanLin M s) v := by
  rw [regularizedModel_eq_weightedPowerQuadratic,
    Optimization.QuadraticSubproblem.fderiv_fderiv_weightedPowerQuadratic_apply
      hM.isPreconditioner_toEuclideanLin g hH.isSymmetric_toEuclideanLin sigma hr]
  simp only [weightedNorm_eq_energyNorm, toEuclideanLin_metric_shift,
    LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    inner_add_left, real_inner_smul_left]
  ring

/-- The nonnegative rank-one correction yields the invariant metric Hessian lower bound. -/
theorem regularizationShift_hessian_lower (hH : H.IsSymm) (hM : M.PosDef)
    (hr : 2 < r) (hsigma : 0 ≤ sigma) (hA : (H + lambda • M).PosSemidef)
    (d : EuclideanSpace ℝ (Fin n)) :
    (sigma * weightedNorm M s ^ (r - 2) - lambda) * weightedNorm M d ^ 2 ≤
      fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) s d d := by
  have hp : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H +
      lambda • (Matrix.toEuclideanLin M).toContinuousLinearMap).IsPositive := by
    change (Matrix.toEuclideanLin H + lambda • Matrix.toEuclideanLin M).IsPositive
    simpa only [map_add, map_smul] using Matrix.isPositive_toEuclideanLin_iff.mpr hA
  simpa only [regularizedModel_eq_weightedPowerQuadratic, weightedNorm_eq_energyNorm] using
    Optimization.QuadraticSubproblem.weightedPowerQuadratic_hessian_lower_of_shift
      hM.isPreconditioner_toEuclideanLin g hH.isSymmetric_toEuclideanLin hsigma hr hp s d

/-- The separate zero-step derivative case: stationarity forces a zero gradient, and the
radial Hessian vanishes for every regularization exponent above two. -/
theorem regularizationShift_zero_derivatives (hH : H.IsSymm) (hM : M.PosDef) (hr : 2 < r)
    (hstat : Matrix.toEuclideanLin (H + lambda • M) (0 : EuclideanSpace ℝ (Fin n)) = -g) :
    gradient (regularizedModel g H M sigma r) 0 = 0 ∧
      ∀ u v, fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) 0 u v =
        inner ℝ (Matrix.toEuclideanLin H u) v := by
  constructor
  · rw [regularizationShift_gradient_identity hH hM hr hstat]
    simp
  · intro u v
    rw [regularizationShift_hessian_identity (lambda := 0) hH hM hr]
    simp [weightedNorm, Real.zero_rpow (by linarith : r - 2 ≠ 0)]

/-- The appendix's objective, gradient, exact rank-one Hessian and metric lower identities.
The hypotheses permit singular positive semidefinite shifts and the zero step. -/
theorem regularizationShiftResidualIdentities (hH : H.IsSymm) (hM : M.PosDef)
    (hr : 2 < r) (hsigma : 0 ≤ sigma) (hA : (H + lambda • M).PosSemidef)
    (hstat : Matrix.toEuclideanLin (H + lambda • M) s = -g) :
    (regularizedModel g H M sigma r s =
      -(1 / 2 : ℝ) * inner ℝ s (Matrix.toEuclideanLin (H + lambda • M) s) +
        weightedNorm M s ^ 2 * (sigma / r * weightedNorm M s ^ (r - 2) - lambda / 2)) ∧
    (gradient (regularizedModel g H M sigma r) s =
      (sigma * weightedNorm M s ^ (r - 2) - lambda) • Matrix.toEuclideanLin M s) ∧
    (∀ u v, fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) s u v =
      inner ℝ (Matrix.toEuclideanLin (H + lambda • M) u) v +
      (sigma * weightedNorm M s ^ (r - 2) - lambda) * inner ℝ (Matrix.toEuclideanLin M u) v +
      sigma * (r - 2) * weightedNorm M s ^ (r - 4) *
        inner ℝ (Matrix.toEuclideanLin M s) u * inner ℝ (Matrix.toEuclideanLin M s) v) ∧
    (∀ d, (sigma * weightedNorm M s ^ (r - 2) - lambda) * weightedNorm M d ^ 2 ≤
      fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) s d d) :=
  ⟨regularizationShift_objective_identity hM hr hstat,
    regularizationShift_gradient_identity hH hM hr hstat,
    regularizationShift_hessian_identity hH hM hr,
    regularizationShift_hessian_lower hH hM hr hsigma hA⟩

end Residual
end CartisGouldToint.AppendixB.Chapter09
