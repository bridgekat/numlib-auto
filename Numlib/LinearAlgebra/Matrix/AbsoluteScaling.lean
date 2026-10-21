import Numlib.LinearAlgebra.Matrix.Scaling

/-!
# Modified absolute spectral scaling

The spectral theorem chooses an actual orthonormal eigenbasis of the supplied symmetric matrix.
Replacing every eigenvalue by its absolute value, floored at a positive number, gives a positive
metric. The normalized curvature lies in the closed unit interval, including equality at the floor.
-/

open scoped ComplexOrder
open Unitary

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An absolute value with a lower floor. -/
noncomputable def absoluteScalingWeight (lam δ : ℝ) : ℝ := max |lam| δ

/-- The modified absolute weight is bounded below by the floor. -/
theorem le_absoluteScalingWeight (lam δ : ℝ) : δ ≤ absoluteScalingWeight lam δ := le_max_right _ _

/-- The modified absolute weight is positive for a positive floor. -/
theorem absoluteScalingWeight_pos (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 < absoluteScalingWeight lam δ := hδ.trans_le (le_absoluteScalingWeight lam δ)

/-- Above or at the floor, the weight is the absolute curvature. -/
theorem absoluteScalingWeight_of_abs_ge {lam δ : ℝ} (h : δ ≤ |lam|) :
    absoluteScalingWeight lam δ = |lam| := max_eq_left h

/-- Below or at the floor, the weight is the floor. -/
theorem absoluteScalingWeight_of_abs_le {lam δ : ℝ} (h : |lam| ≤ δ) :
    absoluteScalingWeight lam δ = δ := max_eq_right h

/-- Curvature after dividing by the modified absolute metric. -/
noncomputable def normalizedCurvature (lam δ : ℝ) : ℝ := lam / absoluteScalingWeight lam δ

/-- Every normalized curvature lies in the closed unit interval. -/
theorem abs_normalizedCurvature_le_one (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |normalizedCurvature lam δ| ≤ 1 := by
  rw [normalizedCurvature, abs_div, abs_of_pos (absoluteScalingWeight_pos lam hδ)]
  exact (div_le_one (absoluteScalingWeight_pos lam hδ)).mpr (le_max_left _ _)

/-- Strictly below the floor, the normalized curvature is strictly inside the unit interval. -/
theorem abs_normalizedCurvature_lt_one {lam δ : ℝ} (hδ : 0 < δ) (h : |lam| < δ) :
    |normalizedCurvature lam δ| < 1 := by
  rw [normalizedCurvature, absoluteScalingWeight_of_abs_le h.le, abs_div, abs_of_pos hδ]
  exact (div_lt_one hδ).mpr h

/-- Positive curvature at or beyond the floor normalizes to one, including equality. -/
theorem normalizedCurvature_of_ge {lam δ : ℝ} (hδ : 0 < δ) (h : δ ≤ lam) :
    normalizedCurvature lam δ = 1 := by
  have hlam : 0 < lam := hδ.trans_le h
  rw [normalizedCurvature, absoluteScalingWeight_of_abs_ge (by simpa [abs_of_pos hlam]),
    abs_of_pos hlam, div_self hlam.ne']

/-- Negative curvature at or beyond the floor normalizes to minus one, including equality. -/
theorem normalizedCurvature_of_le_neg {lam δ : ℝ} (hδ : 0 < δ) (h : lam ≤ -δ) :
    normalizedCurvature lam δ = -1 := by
  have hlam : lam < 0 := lt_of_le_of_lt h (neg_neg_of_pos hδ)
  rw [normalizedCurvature, absoluteScalingWeight_of_abs_ge (by rw [abs_of_neg hlam]; linarith),
    abs_of_neg hlam, div_neg, div_self hlam.ne]

/-- A diagonal matrix expressed in the coordinates of a unitary matrix. -/
noncomputable def unitaryDiagonalScaling (V : unitaryGroup n ℝ) (a : n → ℝ) : Matrix n n ℝ :=
  conjStarAlgAut ℝ _ V (diagonal a)

/-- The concrete matrix formula for a unitary diagonal scaling. -/
theorem unitaryDiagonalScaling_eq (V : unitaryGroup n ℝ) (a : n → ℝ) :
    unitaryDiagonalScaling V a = V.val * diagonal a * V.valᵀ := by
  simp [unitaryDiagonalScaling, star_eq_conjTranspose]

/-- In the standard basis a unitary diagonal scaling is the original diagonal matrix. -/
@[simp] theorem unitaryDiagonalScaling_one (a : n → ℝ) :
    unitaryDiagonalScaling (1 : unitaryGroup n ℝ) a = diagonal a := by
  simp [unitaryDiagonalScaling]

/-- Positive spectral weights give a positive definite matrix. -/
theorem unitaryDiagonalScaling_posDef (V : unitaryGroup n ℝ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) : (unitaryDiagonalScaling V a).PosDef := by
  simpa only [unitaryDiagonalScaling, conjStarAlgAut_apply,
    Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe (U := V))] using
    (posDef_diagonal_iff.mpr ha : (diagonal a).PosDef)

/-- Spectral weights above a floor give a positive semidefinite difference from that floor. -/
theorem unitaryDiagonalScaling_sub_floor_posSemidef (V : unitaryGroup n ℝ) {a : n → ℝ}
    {δ : ℝ} (ha : ∀ i, δ ≤ a i) :
    (unitaryDiagonalScaling V a - δ • (1 : Matrix n n ℝ)).PosSemidef := by
  have hdiag : (diagonal (fun i => a i - δ)).PosSemidef :=
    posSemidef_diagonal_iff.mpr fun i => sub_nonneg.mpr (ha i)
  have heq : unitaryDiagonalScaling V a - δ • (1 : Matrix n n ℝ) =
      conjStarAlgAut ℝ _ V (diagonal (fun i => a i - δ)) := by
    rw [show diagonal (fun i => a i - δ) = diagonal a - δ • (1 : Matrix n n ℝ) by
      ext i j
      by_cases h : i = j <;> simp [h]]
    simp only [unitaryDiagonalScaling, conjStarAlgAut_apply, mul_sub, sub_mul,
      mul_smul_comm, smul_mul_assoc, mul_one, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  rw [heq]
  simpa only [conjStarAlgAut_apply,
    Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe (U := V))] using hdiag

/-- The spectrum of a unitary diagonal scaling is precisely its supplied weights. -/
theorem spectrum_unitaryDiagonalScaling (V : unitaryGroup n ℝ) (a : n → ℝ) :
    spectrum ℝ (unitaryDiagonalScaling V a) = Set.range a := by
  simp [unitaryDiagonalScaling]

/-- The modified absolute matrix chosen by the actual spectral theorem of `H`. -/
noncomputable def modifiedAbsoluteScaling {H : Matrix n n ℝ} (hH : H.IsSymm) (δ : ℝ) :
    Matrix n n ℝ :=
  unitaryDiagonalScaling (isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary
    (fun i => absoluteScalingWeight ((isHermitian_iff_isSymm.mpr hH).eigenvalues i) δ)

/-- The spectral construction uses the actual eigenbasis and the floored absolute eigenvalues. -/
theorem modifiedAbsoluteScaling_eq {H : Matrix n n ℝ} (hH : H.IsSymm) (δ : ℝ) :
    modifiedAbsoluteScaling hH δ =
      (isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary.val *
        diagonal (fun i => absoluteScalingWeight
          ((isHermitian_iff_isSymm.mpr hH).eigenvalues i) δ) *
        (isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary.valᵀ := by
  simp [modifiedAbsoluteScaling, unitaryDiagonalScaling, star_eq_conjTranspose]

/-- The actual modified absolute matrix is positive definite. -/
theorem modifiedAbsoluteScaling_posDef {H : Matrix n n ℝ} (hH : H.IsSymm) {δ : ℝ}
    (hδ : 0 < δ) : (modifiedAbsoluteScaling hH δ).PosDef :=
  unitaryDiagonalScaling_posDef _ fun _ => absoluteScalingWeight_pos _ hδ

/-- The actual modified absolute matrix has the requested spectral floor in matrix form. -/
theorem modifiedAbsoluteScaling_sub_floor_posSemidef {H : Matrix n n ℝ} (hH : H.IsSymm)
    (δ : ℝ) : (modifiedAbsoluteScaling hH δ - δ • (1 : Matrix n n ℝ)).PosSemidef :=
  unitaryDiagonalScaling_sub_floor_posSemidef _ fun _ => le_absoluteScalingWeight _ δ

/-- Every eigenvalue of the modified absolute matrix is at least the specified floor. -/
theorem modifiedAbsoluteScaling_eigenvalues_ge {H : Matrix n n ℝ} (hH : H.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) (i : n) :
    δ ≤ (modifiedAbsoluteScaling_posDef hH hδ).isHermitian.eigenvalues i := by
  have hi := (modifiedAbsoluteScaling_posDef hH hδ).isHermitian.eigenvalues_mem_spectrum_real i
  change _ ∈ spectrum ℝ (unitaryDiagonalScaling
    (isHermitian_iff_isSymm.mpr hH).eigenvectorUnitary
    (fun j => absoluteScalingWeight ((isHermitian_iff_isSymm.mpr hH).eigenvalues j) δ)) at hi
  rw [spectrum_unitaryDiagonalScaling] at hi
  obtain ⟨j, hj⟩ := hi
  rw [← hj]
  exact le_absoluteScalingWeight _ _

end Matrix
