import Numlib.Optimization.LeastSquaresAugmentedSystem
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Chapter 11, Section 3: least-squares models

The residual and Jacobian data may be exact or approximate, as in the source. Their Gram
structure yields the normal equation, a zero spectral cutoff, and the augmented system.
-/

noncomputable section
open scoped InnerProductSpace Matrix
namespace CartisGouldToint.Chapter11.Section03

variable {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ)
  (r : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))

/-- The linearized residual model (11.3.1). -/
def linearizedLeastSquaresModel : ℝ := Matrix.LeastSquaresModel.value J r s

/-- Expansion (11.3.1), using the earlier source quadratic model. -/
theorem linearizedLeastSquaresModel_eq_quadratic :
    linearizedLeastSquaresModel J r s = ‖r‖ ^ 2 / 2 +
      Chapter08.Section01.quadraticModel (Matrix.toEuclideanLin Jᵀ r) (Jᵀ * J) s := by
  rw [linearizedLeastSquaresModel, Matrix.LeastSquaresModel.value_eq_quadratic]
  unfold Chapter08.Section01.quadraticModel
  ring

/-- The constant normal-equation gradient and Gram Hessian give the actual model derivative. -/
theorem hasGradientAt_linearizedLeastSquaresModel :
    HasGradientAt (linearizedLeastSquaresModel J r)
      (Matrix.toEuclideanLin Jᵀ r + Matrix.toEuclideanLin (Jᵀ * J) s) s :=
  Matrix.LeastSquaresModel.hasGradientAt_value_gram J r s

/-- The Hessian of (11.3.1) is positive semidefinite, including rank-deficient Jacobians. -/
theorem linearizedLeastSquaresModel_posSemidef : (Jᵀ * J).PosSemidef :=
  Matrix.LeastSquaresModel.gram_posSemidef J

/-- The matrix in (11.3.2) is positive semidefinite at every nonnegative shift. -/
theorem leastSquares_shift_posSemidef {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) {lambda : ℝ} (hl : 0 ≤ lambda) :
    (Jᵀ * J + lambda • M).PosSemidef :=
  Matrix.LeastSquaresModel.shiftedGram_posSemidef J hM.posSemidef hl

/-- The right-hand side of (11.3.2) lies in the Gram range even at zero shift. -/
theorem linearizedLeastSquaresModel_gradient_mem_range :
    Matrix.toEuclideanLin Jᵀ r ∈ LinearMap.range (Matrix.toEuclideanLin (Jᵀ * J)) :=
  Matrix.LeastSquaresModel.constantGradient_mem_range_gram J r

/-- No generalized Gram eigenvalue is negative in any positive definite source metric. -/
theorem leastSquares_generalizedEigenvalues_nonneg
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) (i) :
    0 ≤ Chapter08.Section02.secularEigenvalues
      (linearizedLeastSquaresModel_posSemidef J).isSymm hM i := by
  exact (Matrix.LeastSquaresModel.energyHessian_gram_isPositive J hM).toLinearMap.nonneg_eigenvalues
    rfl i

/-- The source cutoff `λ_S` is zero, so the negative-curvature hard case does not arise. -/
theorem leastSquares_secularThreshold_zero {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) :
    Chapter08.Section02.secularThreshold
      (linearizedLeastSquaresModel_posSemidef J).isSymm hM = 0 := by
  simp only [Chapter08.Section02.secularThreshold, NNReal.coe_eq_zero]
  apply (Finset.sup_eq_bot_iff _ _).mpr
  intro i _
  apply Subtype.ext
  exact max_eq_left (neg_nonpos.mpr (leastSquares_generalizedEigenvalues_nonneg J hM i))

/-- Elimination in (11.3.3): the normal equation holds precisely when the actual residual
completes the step to a solution of the displayed block system. -/
theorem leastSquaresAugmentedSystem (M : Matrix (Fin n) (Fin n) ℝ) (lambda : ℝ) :
    (Jᵀ * J + lambda • M) *ᵥ s.ofLp = -(Jᵀ *ᵥ r.ofLp) ↔
      ∃ z : EuclideanSpace ℝ (Fin m),
        Matrix.LeastSquaresModel.IsAugmentedSolution J M lambda r.ofLp s.ofLp z.ofLp := by
  rw [Matrix.LeastSquaresModel.normal_iff_exists_augmented]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨WithLp.toLp 2 z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z.ofLp, hz⟩

/-- With a fixed residual variable, (11.3.3) is exactly (11.3.2) and `z=Js+r`. -/
theorem leastSquaresAugmentedSystem_iff_normal_residual
    (M : Matrix (Fin n) (Fin n) ℝ) (lambda : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    Matrix.LeastSquaresModel.IsAugmentedSolution J M lambda r.ofLp s.ofLp z.ofLp ↔
      (Jᵀ * J + lambda • M) *ᵥ s.ofLp = -(Jᵀ *ᵥ r.ofLp) ∧
        z.ofLp = J *ᵥ s.ofLp + r.ofLp :=
  Matrix.LeastSquaresModel.isAugmentedSolution_iff_normal J M lambda r.ofLp s.ofLp z.ofLp

/-- At a positive shift the actual inverse solves (11.3.2). -/
theorem leastSquares_inverse_normal_solution {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) {lambda : ℝ} (hl : 0 < lambda) :
    (Jᵀ * J + lambda • M) *ᵥ
      ((Jᵀ * J + lambda • M)⁻¹ *ᵥ (-(Jᵀ *ᵥ r.ofLp))) = -(Jᵀ *ᵥ r.ofLp) :=
  Matrix.LeastSquaresModel.inverse_normal_solution J hM hl r.ofLp

/-- For positive shifts (11.3.3) has exactly one step/residual pair. -/
theorem leastSquares_existsUnique_augmentedSolution {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) {lambda : ℝ} (hl : 0 < lambda) :
    ∃! sz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      Matrix.LeastSquaresModel.IsAugmentedSolution J M lambda r.ofLp sz.1.ofLp sz.2.ofLp := by
  obtain ⟨sz, hs, hu⟩ := Matrix.LeastSquaresModel.existsUnique_augmentedSolution J hM hl r.ofLp
  refine ⟨(WithLp.toLp 2 sz.1, WithLp.toLp 2 sz.2), hs, ?_⟩
  intro yz hy
  have hh := hu (yz.1.ofLp, yz.2.ofLp) hy
  exact Prod.ext (WithLp.ofLp_injective 2 (congrArg Prod.fst hh))
    (WithLp.ofLp_injective 2 (congrArg Prod.snd hh))

end CartisGouldToint.Chapter11.Section03
