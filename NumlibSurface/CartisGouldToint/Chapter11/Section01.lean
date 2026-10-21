import Numlib.LinearAlgebra.Matrix.FactorCoordinates
import Numlib.Order.Filter.ExtremaEquiv
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Chapter 11, Section 1: variable scaling

The diagonal and band choices of Section 11.1.1 and the modified absolute spectral matrix of
Section 11.1.2. The band formula uses the off-diagonal row absolute sum, correcting the malformed
summation indices in the supplied transcription. The spectral matrix uses the actual symmetric
Hessian eigenbasis. The normalized curvature includes the equality cases at the spectral floor.
The square-root change of coordinates preserves both subproblem objectives and their minimizers.
The signed subproblem classifications remain separate obligations.
-/

open Matrix

namespace CartisGouldToint.Chapter11.Section01

variable {n : ℕ}

/-- The diagonal and band scaling choices of Section 11.1.1, with the stated diagonal maxima. -/
noncomputable def diagonalAndBandedScaling (H : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (δ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
  (H.positiveDiagonalScaling δ, H.positiveBandScaling m δ)

/-- Both choices are positive definite; the band choice is strictly diagonally dominant. -/
theorem diagonalAndBandedScaling_spec {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (diagonalAndBandedScaling H m δ).1.PosDef ∧
      (diagonalAndBandedScaling H m δ).2.IsSymm ∧
      (diagonalAndBandedScaling H m δ).2.IsStrictDiagDominant ∧
      (diagonalAndBandedScaling H m δ).2.PosDef :=
  ⟨Matrix.positiveDiagonalScaling_posDef H hδ, Matrix.positiveBandScaling_isSymm hH m δ,
    Matrix.positiveBandScaling_isStrictDiagDominant H m hδ,
    Matrix.positiveBandScaling_posDef hH m hδ⟩

/-- The modified absolute matrix (11.1.2)–(11.1.4), using the actual spectral theorem for `H`. -/
noncomputable def modifiedAbsoluteScaling {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (δ : ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.modifiedAbsoluteScaling hH δ

/-- The modified absolute scaling is positive definite for every positive floor. -/
theorem modifiedAbsoluteScaling_posDef {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) : (modifiedAbsoluteScaling hH δ).PosDef :=
  Matrix.modifiedAbsoluteScaling_posDef hH hδ

/-- Every eigenvalue of the source scaling matrix is bounded below by the perturbation. -/
theorem modifiedAbsoluteScaling_eigenvalues_ge {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) {δ : ℝ} (hδ : 0 < δ) (i : Fin n) :
    δ ≤ (modifiedAbsoluteScaling_posDef hH hδ).isHermitian.eigenvalues i :=
  Matrix.modifiedAbsoluteScaling_eigenvalues_ge hH hδ i

/-- The normalized diagonal Hessian entries in (11.1.7). -/
noncomputable def normalizedSpectralCurvature {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (δ : ℝ) (i : Fin n) : ℝ :=
  Matrix.normalizedCurvature ((Matrix.isHermitian_iff_isSymm.mpr hH).eigenvalues i) δ

/-- The corrected closed-interval bound for every entry of the normalized diagonal Hessian. -/
theorem normalizedSpectralCurvature_mem_Icc {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) {δ : ℝ} (hδ : 0 < δ) (i : Fin n) :
    normalizedSpectralCurvature hH δ i ∈ Set.Icc (-1) 1 := by
  exact abs_le.mp (Matrix.abs_normalizedCurvature_le_one _ hδ)

/-- The coordinate change `sD = diag(sqrt(ai)) Vᵀ s` from Section 11.1.2. -/
noncomputable def spectralCoordinates {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.diagonalCoordinateEquiv (Matrix.isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary
    (fun i => Matrix.absoluteScalingWeight_pos
      ((Matrix.isHermitian_iff_isSymm.mpr hH).eigenvalues i) hδ)

/-- The diagonal Hessian of (11.1.5). -/
noncomputable def spectralDiagonal {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (δ : ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (normalizedSpectralCurvature hH δ)

/-- The transformed gradient `gD = diag(1/sqrt(ai)) Vᵀ g`. -/
noncomputable def spectralGradient {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (δ : ℝ) (g : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin
    (Matrix.diagonalRecoveryMatrix (Matrix.isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary
      (fun i => Matrix.absoluteScalingWeight
        ((Matrix.isHermitian_iff_isSymm.mpr hH).eigenvalues i) δ))ᵀ g

/-- Recovering source coordinates is the stated inverse square-root matrix formula. -/
theorem spectralCoordinates_symm_apply {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) (s : EuclideanSpace ℝ (Fin n)) :
    (spectralCoordinates hH hδ).symm s = Matrix.toEuclideanLin
      (Matrix.diagonalRecoveryMatrix (Matrix.isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary
        (fun i => Matrix.absoluteScalingWeight
          ((Matrix.isHermitian_iff_isSymm.mpr hH).eigenvalues i) δ)) s := rfl

/-- The transformed spectral gradient has the stated inverse-square-root formula. -/
theorem spectralGradient_eq {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (δ : ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    spectralGradient hH δ g = Matrix.toEuclideanLin
      (Matrix.diagonal (fun i => (Real.sqrt (Matrix.absoluteScalingWeight
        ((Matrix.isHermitian_iff_isSymm.mpr hH).eigenvalues i) δ))⁻¹) *
        (Matrix.isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary.valᵀ) g := by
  unfold spectralGradient
  rw [Matrix.diagonalRecoveryMatrix_transpose]

/-- The actual source Hessian becomes the normalized diagonal Hessian under inverse congruence. -/
theorem spectralDiagonal_eq_congruence {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) :
    (Matrix.diagonalRecoveryMatrix (Matrix.isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary
      (fun i => Matrix.absoluteScalingWeight
        ((Matrix.isHermitian_iff_isSymm.mpr hH).eigenvalues i) δ))ᵀ * H *
      Matrix.diagonalRecoveryMatrix (Matrix.isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary
        (fun i => Matrix.absoluteScalingWeight
          ((Matrix.isHermitian_iff_isSymm.mpr hH).eigenvalues i) δ) = spectralDiagonal hH δ := by
  let hh := Matrix.isHermitian_iff_isSymm.mpr hH
  have hHspec : H = Matrix.unitaryDiagonalScaling hh.eigenvectorUnitary hh.eigenvalues :=
    hh.spectral_theorem
  conv_lhs => arg 1; arg 2; rw [hHspec]
  rw [Matrix.diagonalRecoveryMatrix_congruence _
    (fun i => Matrix.absoluteScalingWeight_pos (hh.eigenvalues i) hδ)]
  rfl

/-- The genuine source matrix norm is the ordinary norm of the transformed coordinates. -/
theorem weightedNorm_spectralCoordinates {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) (s : EuclideanSpace ℝ (Fin n)) :
    Chapter08.Section01.weightedNorm (modifiedAbsoluteScaling hH δ) s =
      ‖spectralCoordinates hH hδ s‖ := by
  rw [Chapter08.Section01.weightedNorm_eq_energyNorm]
  exact Matrix.energyNorm_diagonalCoordinateEquiv _ _ s

/-- The ordinary Euclidean norm is the source norm for the identity matrix. -/
theorem weightedNorm_one (s : EuclideanSpace ℝ (Fin n)) :
    Chapter08.Section01.weightedNorm (1 : Matrix (Fin n) (Fin n) ℝ) s = ‖s‖ := by
  simp [Chapter08.Section01.weightedNorm, Real.sqrt_sq]

/-- The change of coordinates preserves every value of the source quadratic model. -/
theorem quadraticModel_spectralCoordinates {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) :
    Chapter08.Section01.quadraticModel (spectralGradient hH δ g) (spectralDiagonal hH δ)
      (spectralCoordinates hH hδ s) = Chapter08.Section01.quadraticModel g H s := by
  unfold Chapter08.Section01.quadraticModel
  rw [← spectralDiagonal_eq_congruence hH hδ]
  unfold spectralCoordinates spectralGradient
  rw [Matrix.inner_hessian_diagonalCoordinateEquiv]
  rw [Matrix.inner_diagonalCoordinateEquiv]

/-- The transformed regularizer uses the norm of `sD`, preserving the entire source objective. -/
theorem regularizedModel_spectralCoordinates {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Chapter08.Section01.regularizedModel (spectralGradient hH δ g) (spectralDiagonal hH δ) 1
      σ r (spectralCoordinates hH hδ s) =
        Chapter08.Section01.regularizedModel g H (modifiedAbsoluteScaling hH δ) σ r s := by
  simp only [Chapter08.Section01.regularizedModel, quadraticModel_spectralCoordinates,
    weightedNorm_one, weightedNorm_spectralCoordinates hH hδ]

/-- Trust-region global minimizers transfer in both directions under the coordinate equivalence. -/
theorem trustRegionMinimizer_spectralCoordinates {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) :
    Chapter08.Section01.trustRegionMinimizer g H (modifiedAbsoluteScaling hH δ) Δ s ↔
      Chapter08.Section01.trustRegionMinimizer (spectralGradient hH δ g)
        (spectralDiagonal hH δ) 1 Δ (spectralCoordinates hH hδ s) := by
  unfold Chapter08.Section01.trustRegionMinimizer
  apply and_congr
  · simp only [weightedNorm_one, weightedNorm_spectralCoordinates hH hδ]
  · exact Equiv.isMinOn_iff_of_comp_eq (spectralCoordinates hH hδ).toEquiv _ _ _ _
      (quadraticModel_spectralCoordinates hH hδ g)
      (fun x => by
        simp only [weightedNorm_one, weightedNorm_spectralCoordinates hH hδ]
        rfl) s

/-- Power-regularized global minimizers transfer in both directions, for every exponent. -/
theorem regularizedMinimizer_spectralCoordinates {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Chapter08.Section01.regularizedMinimizer g H (modifiedAbsoluteScaling hH δ) σ r s ↔
      Chapter08.Section01.regularizedMinimizer (spectralGradient hH δ g)
        (spectralDiagonal hH δ) 1 σ r (spectralCoordinates hH hδ s) := by
  exact Equiv.isMinOn_iff_of_comp_eq (spectralCoordinates hH hδ).toEquiv _ _
    (fun _ => True) (fun _ => True)
    (fun x => regularizedModel_spectralCoordinates hH hδ g x σ r) (fun _ => Iff.rfl) s

/-- The spectral coordinate change preserves the actual metric, both objectives and both sets
of minimizers in (11.1.5)–(11.1.6). The definitions give the explicit forward, inverse and gradient
matrix formulas; `normalizedCurvature_of_ge` and `normalizedCurvature_of_le_neg` include equality
at the floor in (11.1.7). -/
theorem spectralScalingEquivalence {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) (Δ σ r : ℝ) :
    Chapter08.Section01.weightedNorm (modifiedAbsoluteScaling hH δ) s =
        ‖spectralCoordinates hH hδ s‖ ∧
      Chapter08.Section01.quadraticModel (spectralGradient hH δ g) (spectralDiagonal hH δ)
        (spectralCoordinates hH hδ s) = Chapter08.Section01.quadraticModel g H s ∧
      Chapter08.Section01.regularizedModel (spectralGradient hH δ g) (spectralDiagonal hH δ) 1
        σ r (spectralCoordinates hH hδ s) =
          Chapter08.Section01.regularizedModel g H (modifiedAbsoluteScaling hH δ) σ r s ∧
      (Chapter08.Section01.trustRegionMinimizer g H (modifiedAbsoluteScaling hH δ) Δ s ↔
        Chapter08.Section01.trustRegionMinimizer (spectralGradient hH δ g)
          (spectralDiagonal hH δ) 1 Δ (spectralCoordinates hH hδ s)) ∧
      (Chapter08.Section01.regularizedMinimizer g H (modifiedAbsoluteScaling hH δ) σ r s ↔
        Chapter08.Section01.regularizedMinimizer (spectralGradient hH δ g)
          (spectralDiagonal hH δ) 1 σ r (spectralCoordinates hH hδ s)) :=
  ⟨weightedNorm_spectralCoordinates hH hδ s, quadraticModel_spectralCoordinates hH hδ g s,
    regularizedModel_spectralCoordinates hH hδ g s σ r,
    trustRegionMinimizer_spectralCoordinates hH hδ g s Δ,
    regularizedMinimizer_spectralCoordinates hH hδ g s σ r⟩

/-- Scaling from a supplied invertible diagonal factorization, as in Section 11.1.4. -/
noncomputable def indefiniteFactorScaling (F : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (δ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.factorScaling F (fun i => Matrix.absoluteScalingWeight (d i) δ)

/-- Invertibility of the supplied factor and a positive floor ensure positive definiteness. -/
theorem indefiniteFactorScaling_posDef {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsUnit F)
    (d : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) : (indefiniteFactorScaling F d δ).PosDef :=
  Matrix.factorScaling_posDef hF (fun i => Matrix.absoluteScalingWeight_pos (d i) hδ)

/-- The factor-based forward and recovery coordinate maps, with the actual inverse factor. -/
noncomputable def indefiniteFactorCoordinates (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsUnit F)
    (d : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.factorCoordinates F hF (fun i => Matrix.absoluteScalingWeight_pos (d i) hδ)

/-- The transformed gradient uses `diag(1/sqrt(ai)) F⁻¹ g`. -/
noncomputable def indefiniteFactorGradient (F : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (δ : ℝ) (g : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin
    (Matrix.factorRecoveryMatrix F (fun i => Matrix.absoluteScalingWeight (d i) δ))ᵀ g

/-- The transformed Hessian has diagonal entries `dᵢ/max(|dᵢ|,δ)`. -/
noncomputable def indefiniteFactorDiagonal (d : Fin n → ℝ) (δ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => Matrix.normalizedCurvature (d i) δ)

/-- Forward factor variables are exactly `diag(sqrt(ai)) Fᵀ s`. -/
theorem indefiniteFactorCoordinates_apply (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsUnit F)
    (d : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) (s : EuclideanSpace ℝ (Fin n)) :
    indefiniteFactorCoordinates F hF d hδ s = Matrix.toEuclideanLin
      (Matrix.diagonal (fun i => Real.sqrt (Matrix.absoluteScalingWeight (d i) δ)) * Fᵀ) s :=
  Matrix.factorCoordinates_apply F hF _ s

/-- Recovering the original variables uses exactly `F⁻ᵀ diag(1/sqrt(ai)) sD`. -/
theorem indefiniteFactorCoordinates_symm_apply (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsUnit F)
    (d : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) (s : EuclideanSpace ℝ (Fin n)) :
    (indefiniteFactorCoordinates F hF d hδ).symm s = Matrix.toEuclideanLin
      (F⁻¹ᵀ * Matrix.diagonal (fun i => (Real.sqrt (Matrix.absoluteScalingWeight (d i) δ))⁻¹)) s :=
  Matrix.factorCoordinates_symm_apply F hF _ s

/-- The factor gradient has the stated inverse-factor formula. -/
theorem indefiniteFactorGradient_eq (F : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (δ : ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    indefiniteFactorGradient F d δ g = Matrix.toEuclideanLin
      (Matrix.diagonal (fun i => (Real.sqrt (Matrix.absoluteScalingWeight (d i) δ))⁻¹) * F⁻¹) g :=
    by
  unfold indefiniteFactorGradient
  rw [Matrix.factorRecoveryMatrix_transpose]

/-- The factor-based metric norm is exactly the norm of the transformed variables. -/
theorem weightedNorm_indefiniteFactorCoordinates {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : IsUnit F) (d : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) (s : EuclideanSpace ℝ (Fin n)) :
    Chapter08.Section01.weightedNorm (indefiniteFactorScaling F d δ) s =
      ‖indefiniteFactorCoordinates F hF d hδ s‖ := by
  rw [Chapter08.Section01.weightedNorm_eq_energyNorm]
  exact Matrix.energyNorm_factorCoordinates F hF _ s

/-- A supplied exact diagonal congruence gives the exact quadratic objective in factor variables. -/
theorem quadraticModel_indefiniteFactorCoordinates {F H : Matrix (Fin n) (Fin n) ℝ}
    (hF : IsUnit F) (d : Fin n → ℝ) (hH : H = F * Matrix.diagonal d * Fᵀ)
    {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) :
    Chapter08.Section01.quadraticModel (indefiniteFactorGradient F d δ g)
      (indefiniteFactorDiagonal d δ) (indefiniteFactorCoordinates F hF d hδ s) =
        Chapter08.Section01.quadraticModel g H s := by
  subst H
  unfold Chapter08.Section01.quadraticModel indefiniteFactorDiagonal
  rw [show (fun i => Matrix.normalizedCurvature (d i) δ) =
      (fun i => d i / Matrix.absoluteScalingWeight (d i) δ) from rfl,
    ← Matrix.factorRecoveryMatrix_congruence hF
      (fun i => Matrix.absoluteScalingWeight_pos (d i) hδ) d]
  unfold indefiniteFactorCoordinates indefiniteFactorGradient
  rw [Matrix.inner_hessian_factorCoordinates, Matrix.inner_factorCoordinates]
  rfl

/-- The entire power-regularized objective also transports, with the transformed step norm. -/
theorem regularizedModel_indefiniteFactorCoordinates {F H : Matrix (Fin n) (Fin n) ℝ}
    (hF : IsUnit F) (d : Fin n → ℝ) (hH : H = F * Matrix.diagonal d * Fᵀ)
    {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Chapter08.Section01.regularizedModel (indefiniteFactorGradient F d δ g)
      (indefiniteFactorDiagonal d δ) 1 σ r (indefiniteFactorCoordinates F hF d hδ s) =
        Chapter08.Section01.regularizedModel g H (indefiniteFactorScaling F d δ) σ r s := by
  simp only [Chapter08.Section01.regularizedModel,
    quadraticModel_indefiniteFactorCoordinates hF d hH hδ, weightedNorm_one,
    weightedNorm_indefiniteFactorCoordinates hF d hδ]

/-- Trust-region minimizers correspond under the invertible factor coordinate change. -/
theorem trustRegionMinimizer_indefiniteFactorCoordinates {F H : Matrix (Fin n) (Fin n) ℝ}
    (hF : IsUnit F) (d : Fin n → ℝ) (hH : H = F * Matrix.diagonal d * Fᵀ)
    {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) :
    Chapter08.Section01.trustRegionMinimizer g H (indefiniteFactorScaling F d δ) Δ s ↔
      Chapter08.Section01.trustRegionMinimizer (indefiniteFactorGradient F d δ g)
        (indefiniteFactorDiagonal d δ) 1 Δ (indefiniteFactorCoordinates F hF d hδ s) := by
  unfold Chapter08.Section01.trustRegionMinimizer
  apply and_congr
  · simp only [weightedNorm_one, weightedNorm_indefiniteFactorCoordinates hF d hδ]
  · exact Equiv.isMinOn_iff_of_comp_eq (indefiniteFactorCoordinates F hF d hδ).toEquiv _ _ _ _
      (quadraticModel_indefiniteFactorCoordinates hF d hH hδ g)
      (fun x => by
        simp only [weightedNorm_one, weightedNorm_indefiniteFactorCoordinates hF d hδ]
        rfl) s

/-- Power-regularized minimizers correspond under the invertible factor coordinate change. -/
theorem regularizedMinimizer_indefiniteFactorCoordinates {F H : Matrix (Fin n) (Fin n) ℝ}
    (hF : IsUnit F) (d : Fin n → ℝ) (hH : H = F * Matrix.diagonal d * Fᵀ)
    {δ : ℝ} (hδ : 0 < δ) (g s : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Chapter08.Section01.regularizedMinimizer g H (indefiniteFactorScaling F d δ) σ r s ↔
      Chapter08.Section01.regularizedMinimizer (indefiniteFactorGradient F d δ g)
        (indefiniteFactorDiagonal d δ) 1 σ r (indefiniteFactorCoordinates F hF d hδ s) := by
  exact Equiv.isMinOn_iff_of_comp_eq (indefiniteFactorCoordinates F hF d hδ).toEquiv _ _
    (fun _ => True) (fun _ => True)
    (fun x => regularizedModel_indefiniteFactorCoordinates hF d hH hδ g x σ r)
    (fun _ => Iff.rfl) s

/-- The uniform lower metric estimate retains an explicit uniform bound on the inverse factor. -/
theorem indefiniteFactorScaling_uniform_lower {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsUnit F)
    (d : Fin n → ℝ) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hbound : ∀ y : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin F⁻¹ᵀ y‖ ≤ K * ‖y‖)
    (s : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt δ / K * ‖s‖ ≤ Chapter08.Section01.weightedNorm (indefiniteFactorScaling F d δ) s := by
  rw [Chapter08.Section01.weightedNorm_eq_energyNorm]
  exact Matrix.factorScaling_energyNorm_lower hF hδ.le
    (fun i => Matrix.le_absoluteScalingWeight (d i) δ) hK hbound s

/-- A uniform Euclidean operator bound on `F⁻¹` gives a uniform lower bound on the source norm. -/
theorem indefiniteFactorScaling_lower_of_inverse_norm {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : IsUnit F) (d : Fin n → ℝ) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) F⁻¹‖ ≤ K) (s : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt δ / K * ‖s‖ ≤ Chapter08.Section01.weightedNorm (indefiniteFactorScaling F d δ) s := by
  rw [Chapter08.Section01.weightedNorm_eq_energyNorm]
  exact Matrix.factorScaling_energyNorm_lower_of_inverse_norm hF hδ.le
    (fun i => Matrix.le_absoluteScalingWeight (d i) δ) hK hbound s

end CartisGouldToint.Chapter11.Section01
