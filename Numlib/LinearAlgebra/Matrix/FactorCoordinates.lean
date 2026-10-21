import Numlib.LinearAlgebra.Matrix.DiagonalCoordinates

/-!
# Coordinates for invertible diagonal congruences

The factor need only be invertible; it need not be orthogonal. Lower metric bounds explicitly
retain the inverse-factor bound.
-/

open scoped InnerProductSpace ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An invertible matrix as an equivalence of Euclidean spaces, with its actual matrix inverse. -/
noncomputable def invertibleEuclideanEquiv (F : Matrix n n ℝ) (hF : IsUnit F) :
    EuclideanSpace ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ n where
  toLinearMap := toEuclideanLin F
  invFun := toEuclideanLin F⁻¹
  left_inv x := by
    change toEuclideanLin F⁻¹ (toEuclideanLin F x) = x
    exact toEuclideanLin_nonsing_inv_mul_apply hF x
  right_inv x := by
    change toEuclideanLin F (toEuclideanLin F⁻¹ x) = x
    exact toEuclideanLin_mul_nonsing_inv_apply hF x

/-- The invertible matrix equivalence applies the supplied matrix. -/
@[simp] theorem invertibleEuclideanEquiv_apply (F : Matrix n n ℝ) (hF : IsUnit F)
    (s : EuclideanSpace ℝ n) : invertibleEuclideanEquiv F hF s = toEuclideanLin F s := rfl

/-- The inverse matrix equivalence applies the actual matrix inverse. -/
@[simp] theorem invertibleEuclideanEquiv_symm_apply (F : Matrix n n ℝ) (hF : IsUnit F)
    (s : EuclideanSpace ℝ n) : (invertibleEuclideanEquiv F hF).symm s =
      toEuclideanLin F⁻¹ s := rfl

/-- The metric of an invertible diagonal congruence. -/
noncomputable def factorScaling (F : Matrix n n ℝ) (a : n → ℝ) : Matrix n n ℝ :=
  F * diagonal a * Fᵀ

/-- Positive weights and an invertible factor give a positive definite metric. -/
theorem factorScaling_posDef {F : Matrix n n ℝ} (hF : IsUnit F) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) : (factorScaling F a).PosDef := by
  have hi := mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det Fᵀ).mpr (by
      simpa only [det_transpose] using (isUnit_iff_isUnit_det F).mp hF))
  simpa only [factorScaling, conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    (posDef_diagonal_iff.mpr ha).conjTranspose_mul_mul_same hi

/-- The square-root coordinates for a general invertible diagonal congruence. -/
noncomputable def factorCoordinates (F : Matrix n n ℝ) (hF : IsUnit F) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) : EuclideanSpace ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ n :=
  (invertibleEuclideanEquiv Fᵀ ((isUnit_iff_isUnit_det Fᵀ).mpr (by
      simpa only [det_transpose] using (isUnit_iff_isUnit_det F).mp hF))).trans
    (diagonalCoordinateEquiv 1 ha)

/-- The forward factor coordinates are the stated square-root matrix formula. -/
theorem factorCoordinates_apply (F : Matrix n n ℝ) (hF : IsUnit F) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (s : EuclideanSpace ℝ n) :
    factorCoordinates F hF ha s =
      toEuclideanLin (diagonal (fun i => Real.sqrt (a i)) * Fᵀ) s := by
  simp [factorCoordinates, invertibleEuclideanEquiv, diagonalCoordinateEquiv_apply,
    diagonalCoordinateMatrix_one]

/-- The matrix that recovers the original variables from factor coordinates. -/
noncomputable def factorRecoveryMatrix (F : Matrix n n ℝ) (a : n → ℝ) : Matrix n n ℝ :=
  F⁻¹ᵀ * diagonal (fun i => (Real.sqrt (a i))⁻¹)

/-- Recovery uses the inverse transpose of the supplied factor. -/
theorem factorCoordinates_symm_apply (F : Matrix n n ℝ) (hF : IsUnit F) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (s : EuclideanSpace ℝ n) :
    (factorCoordinates F hF ha).symm s = toEuclideanLin (factorRecoveryMatrix F a) s := by
  simp [factorCoordinates, invertibleEuclideanEquiv, diagonalCoordinateEquiv_symm_apply,
    diagonalRecoveryMatrix_one, factorRecoveryMatrix, transpose_nonsing_inv]

/-- The metric norm is the Euclidean norm of the factor coordinates. -/
theorem energyNorm_factorCoordinates (F : Matrix n n ℝ) (hF : IsUnit F) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (s : EuclideanSpace ℝ n) :
    energyNorm (toEuclideanLin (factorScaling F a)) s = ‖factorCoordinates F hF ha s‖ := by
  have hm : energyNorm (toEuclideanLin (factorScaling F a)) s =
      energyNorm (toEuclideanLin (diagonal a)) (toEuclideanLin Fᵀ s) := by
    simp only [energyNorm, factorScaling, toEuclideanLin_mul_apply]
    rw [← toEuclideanLin_transpose_inner_left Fᵀ s, transpose_transpose]
  rw [hm]
  simpa [factorCoordinates, invertibleEuclideanEquiv, unitaryDiagonalScaling_one] using
    energyNorm_diagonalCoordinateEquiv (1 : unitaryGroup n ℝ) ha (toEuclideanLin Fᵀ s)

/-- Inverse congruence divides a supplied diagonal Hessian by its positive diagonal weights. -/
theorem factorRecoveryMatrix_congruence {F : Matrix n n ℝ} (hF : IsUnit F) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (d : n → ℝ) :
    (factorRecoveryMatrix F a)ᵀ * factorScaling F d * factorRecoveryMatrix F a =
      diagonal (fun i => d i / a i) := by
  have hl : F⁻¹ * F = 1 := nonsing_inv_mul F ((isUnit_iff_isUnit_det F).mp hF)
  have hr : Fᵀ * F⁻¹ᵀ = 1 := by rw [← transpose_mul, hl, transpose_one]
  simp only [factorRecoveryMatrix, factorScaling, transpose_mul, diagonal_transpose,
    transpose_transpose]
  calc
    _ = diagonal (fun i => (Real.sqrt (a i))⁻¹) * (F⁻¹ * F) * diagonal d *
        (Fᵀ * F⁻¹ᵀ) * diagonal (fun i => (Real.sqrt (a i))⁻¹) := by simp only [mul_assoc]
    _ = _ := by
      rw [hl, hr, mul_one, mul_one]
      simpa only [diagonalRecoveryMatrix_one, unitaryDiagonalScaling_one, diagonal_transpose] using
        diagonalRecoveryMatrix_congruence (1 : unitaryGroup n ℝ) ha d

/-- The inverse transpose gives the actual transformed gradient formula. -/
theorem factorRecoveryMatrix_transpose (F : Matrix n n ℝ) (a : n → ℝ) :
    (factorRecoveryMatrix F a)ᵀ = diagonal (fun i => (Real.sqrt (a i))⁻¹) * F⁻¹ := by
  simp [factorRecoveryMatrix, transpose_mul]

/-- Inverse-transpose transformation preserves the linear term. -/
theorem inner_factorCoordinates (F : Matrix n n ℝ) (hF : IsUnit F) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (g s : EuclideanSpace ℝ n) :
    inner ℝ (toEuclideanLin (factorRecoveryMatrix F a)ᵀ g) (factorCoordinates F hF ha s) =
      inner ℝ g s := by
  rw [toEuclideanLin_transpose_inner_left]
  rw [← factorCoordinates_symm_apply F hF ha, LinearEquiv.symm_apply_apply]

/-- The actual inverse congruence preserves the Hessian quadratic form. -/
theorem inner_hessian_factorCoordinates (F : Matrix n n ℝ) (hF : IsUnit F) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) (H : Matrix n n ℝ) (s : EuclideanSpace ℝ n) :
    inner ℝ (factorCoordinates F hF ha s)
      (toEuclideanLin ((factorRecoveryMatrix F a)ᵀ * H * factorRecoveryMatrix F a)
        (factorCoordinates F hF ha s)) = inner ℝ s (toEuclideanLin H s) := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_transpose_inner_right, ← factorCoordinates_symm_apply F hF ha,
    LinearEquiv.symm_apply_apply]

/-- Diagonal spectral floors give explicit energy-norm lower bounds. -/
theorem sqrt_mul_norm_le_energyNorm_diagonal {a : n → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ i, δ ≤ a i) (s : EuclideanSpace ℝ n) :
    Real.sqrt δ * ‖s‖ ≤ energyNorm (toEuclideanLin (diagonal a)) s := by
  have hD : (diagonal a).IsHermitian := by simp
  have hco : (toEuclideanLin (diagonal a)).IsCoerciveWith δ := by
    apply (LinearMap.IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue
      (isSymmetric_toEuclideanLin_iff.mpr hD) δ).mpr
    intro μ hμ
    rw [hasEigenvalue_toEuclideanLin_iff] at hμ
    have hm : μ ∈ Set.range a := by simpa using hμ
    obtain ⟨i, rfl⟩ := hm
    exact ha i
  exact hco.norm_le_energyNorm hδ s

/-- A uniform inverse-transpose bound and a diagonal floor give a uniform metric lower bound.
The inverse bound is essential; positivity of the diagonal weights alone does not control it. -/
theorem factorScaling_energyNorm_lower {F : Matrix n n ℝ} (hF : IsUnit F) {a : n → ℝ}
    {δ K : ℝ} (hδ : 0 ≤ δ) (ha : ∀ i, δ ≤ a i) (hK : 0 < K)
    (hbound : ∀ y : EuclideanSpace ℝ n, ‖toEuclideanLin F⁻¹ᵀ y‖ ≤ K * ‖y‖)
    (s : EuclideanSpace ℝ n) :
    Real.sqrt δ / K * ‖s‖ ≤ energyNorm (toEuclideanLin (factorScaling F a)) s := by
  have hFt : IsUnit Fᵀ := (isUnit_iff_isUnit_det Fᵀ).mpr (by
    simpa only [det_transpose] using (isUnit_iff_isUnit_det F).mp hF)
  have hi := hbound (toEuclideanLin Fᵀ s)
  rw [transpose_nonsing_inv, toEuclideanLin_nonsing_inv_mul_apply hFt] at hi
  have hlo := sqrt_mul_norm_le_energyNorm_diagonal hδ ha (toEuclideanLin Fᵀ s)
  have hm : energyNorm (toEuclideanLin (factorScaling F a)) s =
      energyNorm (toEuclideanLin (diagonal a)) (toEuclideanLin Fᵀ s) := by
    simp only [energyNorm, factorScaling, toEuclideanLin_mul_apply]
    rw [← toEuclideanLin_transpose_inner_left Fᵀ s, transpose_transpose]
  rw [hm, div_mul_eq_mul_div, div_le_iff₀ hK]
  calc
    Real.sqrt δ * ‖s‖ ≤ Real.sqrt δ * (K * ‖toEuclideanLin Fᵀ s‖) :=
      mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg δ)
    _ ≤ energyNorm (toEuclideanLin (diagonal a)) (toEuclideanLin Fᵀ s) * K := by
      nlinarith [mul_le_mul_of_nonneg_right hlo hK.le]

/-- An operator-norm bound on the actual inverse factor supplies the required uniform lower
metric bound; the inverse transpose has the same Euclidean operator norm. -/
theorem factorScaling_energyNorm_lower_of_inverse_norm {F : Matrix n n ℝ} (hF : IsUnit F)
    {a : n → ℝ} {δ K : ℝ} (hδ : 0 ≤ δ) (ha : ∀ i, δ ≤ a i) (hK : 0 < K)
    (hbound : ‖toEuclideanCLM (𝕜 := ℝ) F⁻¹‖ ≤ K) (s : EuclideanSpace ℝ n) :
    Real.sqrt δ / K * ‖s‖ ≤ energyNorm (toEuclideanLin (factorScaling F a)) s := by
  apply factorScaling_energyNorm_lower hF hδ ha hK _ s
  intro y
  have ht : ‖toEuclideanCLM (𝕜 := ℝ) F⁻¹ᵀ‖ ≤ K := by
    simpa only [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose,
      map_star, norm_star] using hbound
  exact (toEuclideanCLM (𝕜 := ℝ) F⁻¹ᵀ).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_right ht (norm_nonneg y))

end Matrix
