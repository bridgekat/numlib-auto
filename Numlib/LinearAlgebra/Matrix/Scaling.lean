import Numlib.LinearAlgebra.Matrix.DiagDominant

/-!
# Positive diagonal and band scalings

Perturbing the diagonal of a symmetric band truncation gives a positive definite matrix.
The bandwidth is measured by the distance between the finite ordinal row and column indices.
-/

open scoped ComplexOrder

namespace Matrix

variable {ι : Type*} [DecidableEq ι]

/-- Diagonal scaling with each entry bounded below by `δ`. -/
noncomputable def positiveDiagonalScaling (H : Matrix ι ι ℝ) (δ : ℝ) :
    Matrix ι ι ℝ := diagonal fun i => max (H i i) δ

/-- A positive floor makes the diagonal scaling positive definite. -/
theorem positiveDiagonalScaling_posDef (H : Matrix ι ι ℝ) {δ : ℝ}
    (hδ : 0 < δ) : (positiveDiagonalScaling H δ).PosDef :=
  posDef_diagonal_iff.mpr fun i => hδ.trans_le (le_max_right (H i i) δ)

/-- The entries of the positive diagonal scaling. -/
@[simp] theorem positiveDiagonalScaling_apply (H : Matrix ι ι ℝ) (δ : ℝ) (i j : ι) :
    positiveDiagonalScaling H δ i j = if i = j then max (H i i) δ else 0 := by
  simp [positiveDiagonalScaling, diagonal_apply]

variable {n : ℕ}

/-- Off-diagonal entries retained by a band truncation. -/
noncomputable def bandOffDiagonal (H : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ≠ j ∧ i.val ≤ j.val + m ∧ j.val ≤ i.val + m then H i j else 0

/-- Inside the off-diagonal band the Hessian entries are retained. -/
theorem bandOffDiagonal_of_mem (H : Matrix (Fin n) (Fin n) ℝ) (m : ℕ)
    {i j : Fin n} (hij : i ≠ j) (hijm : i.val ≤ j.val + m) (hjim : j.val ≤ i.val + m) :
    bandOffDiagonal H m i j = H i j := by simp [bandOffDiagonal, hij, hijm, hjim]

/-- Outside the band all entries vanish. -/
theorem bandOffDiagonal_of_outside (H : Matrix (Fin n) (Fin n) ℝ) (m : ℕ)
    {i j : Fin n} (h : i.val + m < j.val ∨ j.val + m < i.val) :
    bandOffDiagonal H m i j = 0 := by
  rcases h with h | h <;> simp [bandOffDiagonal, not_le.mpr h]

/-- The off-diagonal band has zero diagonal. -/
@[simp] theorem bandOffDiagonal_diag (H : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (i : Fin n) :
    bandOffDiagonal H m i i = 0 := by simp [bandOffDiagonal]

/-- Band truncation preserves symmetry. -/
theorem bandOffDiagonal_isSymm {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (m : ℕ) :
    (bandOffDiagonal H m).IsSymm := by
  ext i j
  simp only [transpose_apply, bandOffDiagonal]
  rw [hH.apply i j]
  by_cases hij : i = j <;> simp [hij, ne_comm, and_comm]

/-- Symmetric band scaling: keep the band and raise the diagonal above its row absolute sum. -/
noncomputable def positiveBandScaling (H : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (δ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i = j then max (H i i) ((∑ k, |bandOffDiagonal H m i k|) + δ)
  else bandOffDiagonal H m i j

/-- The diagonal of the band scaling is the specified maximum. -/
@[simp] theorem positiveBandScaling_diag (H : Matrix (Fin n) (Fin n) ℝ)
    (m : ℕ) (δ : ℝ) (i : Fin n) :
    positiveBandScaling H m δ i i = max (H i i) ((∑ k, |bandOffDiagonal H m i k|) + δ) := by
  simp [positiveBandScaling]

/-- Off the diagonal the original band truncation is retained. -/
theorem positiveBandScaling_offDiag (H : Matrix (Fin n) (Fin n) ℝ)
    (m : ℕ) (δ : ℝ) {i j : Fin n} (hij : i ≠ j) :
    positiveBandScaling H m δ i j = bandOffDiagonal H m i j := by
  simp [positiveBandScaling, hij]

/-- The band scaling is symmetric whenever the supplied Hessian is symmetric. -/
theorem positiveBandScaling_isSymm {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (m : ℕ) (δ : ℝ) : (positiveBandScaling H m δ).IsSymm := by
  ext i j
  by_cases hij : i = j
  · subst j; rfl
  · simp only [transpose_apply, positiveBandScaling, hij, Ne.symm hij, ite_false]
    exact (bandOffDiagonal_isSymm hH m).apply i j

/-- Every diagonal entry is positive when the perturbation is positive. -/
theorem positiveBandScaling_diag_pos (H : Matrix (Fin n) (Fin n) ℝ) (m : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (i : Fin n) : 0 < positiveBandScaling H m δ i i := by
  rw [positiveBandScaling_diag]
  exact (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => abs_nonneg _) hδ).trans_le
    (le_max_right _ _)

/-- The positive perturbation gives strict row diagonal dominance. -/
theorem positiveBandScaling_isStrictDiagDominant (H : Matrix (Fin n) (Fin n) ℝ)
    (m : ℕ) {δ : ℝ} (hδ : 0 < δ) : (positiveBandScaling H m δ).IsStrictDiagDominant := by
  intro i
  have hs : ∑ j ∈ Finset.univ.erase i, ‖positiveBandScaling H m δ i j‖ =
      ∑ j, |bandOffDiagonal H m i j| := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, |bandOffDiagonal H m i j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [positiveBandScaling_offDiag H m δ (Ne.symm (Finset.ne_of_mem_erase hj)),
          Real.norm_eq_abs]
      _ = _ := by rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]; simp
  rw [hs, Real.norm_eq_abs, abs_of_pos (positiveBandScaling_diag_pos H m hδ i),
    positiveBandScaling_diag]
  exact (lt_add_of_pos_right _ hδ).trans_le (le_max_right _ _)

/-- The symmetric band construction is positive definite. -/
theorem positiveBandScaling_posDef {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (m : ℕ) {δ : ℝ} (hδ : 0 < δ) : (positiveBandScaling H m δ).PosDef := by
  apply IsStrictDiagDominant.posDef
    (by simpa only [isHermitian_iff_isSymm] using positiveBandScaling_isSymm hH m δ)
    (positiveBandScaling_isStrictDiagDominant H m hδ)
  intro i
  exact positiveBandScaling_diag_pos H m hδ i

end Matrix
