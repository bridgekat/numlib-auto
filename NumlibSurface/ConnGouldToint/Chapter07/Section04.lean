import Numlib.Optimization.Subproblem.Matrix

/-!
# The scaled Euclidean trust-region problem

Section 7.4 of [conn2000trust].
-/

open Matrix Metric
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter07

open Subproblem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H M : Matrix ι ι ℝ} {g : EuclideanSpace ℝ ι} {Δ : ℝ}

/-- The trust-region norm induced by the positive definite scaling matrix. -/
noncomputable def mNorm (M : Matrix ι ι ℝ) (s : EuclideanSpace ℝ ι) : ℝ :=
  √⟪s, toEuclideanLin M s⟫

/-- The matrix quadratic objective of (7.4.1). -/
noncomputable def matrixQuadModel (g : EuclideanSpace ℝ ι) (H : Matrix ι ι ℝ)
    (s : EuclideanSpace ℝ ι) : ℝ :=
  ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫

/-- The ellipsoidal feasible set of (7.4.1). -/
def weightedTrustRegion (M : Matrix ι ι ℝ) (Δ : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {s | mNorm M s ≤ Δ}

private theorem norm_toScaled_eq_mNorm (hM : M.PosDef) (s : EuclideanSpace ℝ ι) :
    ‖toScaled hM s‖ = mNorm M s := by
  rw [norm_toScaled, mNorm, real_inner_comm]

/-- The weighted subproblem is the ordinary ball subproblem in the `M`-inner product.
The identity map to the scaled space implements the change of coordinates intrinsically. -/
theorem isMinOn_weightedTrustRegion_iff_scaled (hM : M.PosDef) (s : EuclideanSpace ℝ ι) :
    IsMinOn (matrixQuadModel g H) (weightedTrustRegion M Δ) s ↔
      IsMinOn (quadModel (scaledGrad hM g) (scaledOp H hM)) (closedBall 0 Δ)
        (toScaled hM s) := by
  simp only [isMinOn_iff, weightedTrustRegion, Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  constructor
  · intro hs y hy
    obtain ⟨x, rfl⟩ := (toScaled hM).surjective y
    rw [norm_toScaled_eq_mNorm] at hy
    simpa only [matrixQuadModel, quadModel_scaled (hM := hM)] using hs x hy
  · intro hs y hy
    have hy' : ‖toScaled hM y‖ ≤ Δ := by rwa [norm_toScaled_eq_mNorm]
    simpa only [matrixQuadModel, quadModel_scaled (hM := hM)] using hs (toScaled hM y) hy'

/-- The congruence in (7.4.2)–(7.4.4): for an invertible `S` with `Sᵀ M S = I`,
the weighted problem becomes the Euclidean ball problem with gradient `Sᵀ g`
and Hessian `Sᵀ H S`. Solutions transform by multiplication by `S`. -/
theorem isMinOn_weightedTrustRegion_iff_congruence {S : Matrix ι ι ℝ} (hS : IsUnit S)
    (hcongr : Sᵀ * M * S = 1) (y : EuclideanSpace ℝ ι) :
    IsMinOn (matrixQuadModel g H) (weightedTrustRegion M Δ) (toEuclideanLin S y) ↔
      IsMinOn (matrixQuadModel (toEuclideanLin Sᵀ g) (Sᵀ * H * S)) (closedBall 0 Δ) y := by
  have hnorm (z : EuclideanSpace ℝ ι) : mNorm M (toEuclideanLin S z) = ‖z‖ := by
    rw [mNorm, real_inner_comm, ← inner_toEuclideanLin_conjTranspose_mul_mul_apply,
      conjTranspose_eq_transpose_of_trivial, hcongr, toEuclideanLin_one_apply,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hmodel (z : EuclideanSpace ℝ ι) :
      matrixQuadModel (toEuclideanLin Sᵀ g) (Sᵀ * H * S) z =
        matrixQuadModel g H (toEuclideanLin S z) := by
    have hquad : ⟪z, toEuclideanLin (Sᵀ * H * S) z⟫ =
        ⟪toEuclideanLin S z, toEuclideanLin H (toEuclideanLin S z)⟫ := calc
      _ = ⟪toEuclideanLin (Sᵀ * H * S) z, z⟫ := real_inner_comm _ _
      _ = ⟪toEuclideanLin H (toEuclideanLin S z), toEuclideanLin S z⟫ := by
        simpa only [conjTranspose_eq_transpose_of_trivial] using
          inner_toEuclideanLin_conjTranspose_mul_mul_apply H S z
      _ = _ := real_inner_comm _ _
    rw [matrixQuadModel, matrixQuadModel, toEuclideanLin_transpose_inner_left, hquad]
  simp only [isMinOn_iff, weightedTrustRegion, Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  constructor
  · intro hm z hz
    simpa only [hmodel] using hm (toEuclideanLin S z) (by simpa only [hnorm] using hz)
  · intro hm u hu
    let z := toEuclideanLin S⁻¹ u
    have hz : toEuclideanLin S z = u := toEuclideanLin_mul_nonsing_inv_apply hS u
    rw [← hz] at hu ⊢
    rw [hnorm] at hu
    simpa only [hmodel] using hm z hu

/-- Theorem 7.4.1. A global minimizer over the weighted ball solves the shifted system
with a nonnegative complementary multiplier and positive semidefinite shifted matrix.
Positive definiteness implies uniqueness. A positive radius is required, as in Section 7.2. -/
theorem theorem_7_4_1 (hM : M.PosDef) (hH : H.IsHermitian) (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ ι} (hs : s ∈ weightedTrustRegion M Δ)
    (hmin : IsMinOn (matrixQuadModel g H) (weightedTrustRegion M Δ) s) :
    ∃ μ : ℝ, toEuclideanLin (H + μ • M) s = -g ∧ (H + μ • M).PosSemidef ∧
      0 ≤ μ ∧ μ * (mNorm M s - Δ) = 0 ∧
      ((H + μ • M).PosDef → ∀ u ∈ weightedTrustRegion M Δ,
        IsMinOn (matrixQuadModel g H) (weightedTrustRegion M Δ) u → u = s) := by
  have hsymm := isSymmetric_scaledOp (hM := hM) hH
  have hs' : ‖toScaled hM s‖ ≤ Δ := by rwa [norm_toScaled_eq_mNorm]
  have hm := (isMinOn_weightedTrustRegion_iff_scaled hM s).mp hmin
  obtain ⟨μ, hμ⟩ := (isMinOn_closedBall_iff hsymm hΔ hs').mp hm
  refine ⟨μ, (add_smul_scaledOp_toScaled_eq_neg_iff μ g s).mp hμ.shifted,
    (posSemidef_add_smul_iff_isPositive μ).mpr hμ.isPositive, hμ.nonneg, ?_, ?_⟩
  · simpa only [norm_toScaled_eq_mNorm] using hμ.complementarity
  · intro hpd u hu hminu
    have hc := ((posDef_add_smul_iff_isSymmetricCoercive (hM := hM) μ).mp hpd).isCoercive
    have hu' : ‖toScaled hM u‖ ≤ Δ := by rwa [norm_toScaled_eq_mNorm]
    have hmu := (isMinOn_weightedTrustRegion_iff_scaled hM u).mp hminu
    exact (toScaled hM).injective (eq_of_isMinOn_closedBall_of_posDef hsymm hμ hs' hc hu' hmu)

end ConnGouldToint.Chapter07
