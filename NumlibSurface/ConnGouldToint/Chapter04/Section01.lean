import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Linear equations in optimization

The optimization matrix and its structured systems in Section 4.1 of [conn2000trust].
Equation (4.1.2) requires the middle inverse in addition to the inverses of `H` and `D`.
-/

open Matrix
open scoped Matrix

namespace ConnGouldToint.Chapter04

variable {m n : ℕ}

/-- **(4.1.1)** The symmetric block structure used for optimization systems. -/
abbrev optimizationMatrix (H : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  Matrix.saddleMatrix H Aᵀ (-D)

/-- **(4.1.2)** The Sherman–Morrison–Woodbury expression solves the structured
system when all three inverses in the expression exist. -/
theorem woodbury_solution_4_1_2 {H : Matrix (Fin n) (Fin n) ℝ}
    {D : Matrix (Fin m) (Fin m) ℝ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hH : IsUnit H) (hD : IsUnit D) (hS : IsUnit (D⁻¹ + A * H⁻¹ * Aᵀ))
    (b : Fin n → ℝ) :
    (H + Aᵀ * D * A) *ᵥ
      (H⁻¹ *ᵥ b - (H⁻¹ * Aᵀ * (D⁻¹ + A * H⁻¹ * Aᵀ)⁻¹ * A * H⁻¹) *ᵥ b) = b := by
  have hW := Matrix.add_mul_mul_inv_eq_sub H Aᵀ D A hH hD hS
  have hB : IsUnit (H + Aᵀ * D * A) := by
    obtain ⟨_⟩ := hH.nonempty_invertible
    obtain ⟨_⟩ := hD.nonempty_invertible
    obtain ⟨hSI⟩ := hS.nonempty_invertible
    simp only [← invOf_eq_nonsing_inv] at hSI
    let := Matrix.invertibleAddMulMul H Aᵀ D A
    exact isUnit_of_invertible _
  rw [← sub_mulVec, ← hW]
  exact Matrix.mulVec_nonsing_inv_mulVec hB b

/-- The middle factor in (4.1.2) can be singular even with invertible
`H` and `D`. The scalar blocks `H = -1`, `D = A = 1` suffice. -/
theorem woodbury_middle_inverse_counterexample :
    ∃ H D A : Matrix (Fin 1) (Fin 1) ℝ,
      IsUnit H ∧ IsUnit D ∧ ¬ IsUnit (D⁻¹ + A * H⁻¹ * Aᵀ) := by
  have hInv : (-1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = -1 :=
    Matrix.inv_eq_left_inv (by simp)
  refine ⟨-1, 1, 1, isUnit_one.neg, isUnit_one, ?_⟩
  simp [hInv]

/-- **(4.1.3)** The augmented system is equivalent to the original structured
system and the equation defining the auxiliary variable. -/
theorem augmented_system_4_1_3 {H : Matrix (Fin n) (Fin n) ℝ}
    {D : Matrix (Fin m) (Fin m) ℝ} (A : Matrix (Fin m) (Fin n) ℝ) (hD : IsUnit D)
    (x b : Fin n → ℝ) (y : Fin m → ℝ) :
    optimizationMatrix H A D⁻¹ *ᵥ Sum.elim x y = Sum.elim b 0 ↔
      (H + Aᵀ * D * A) *ᵥ x = b ∧ y = D *ᵥ (A *ᵥ x) := by
  rw [optimizationMatrix, Matrix.saddleMatrix_mulVec_elim]
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_transpose, neg_mulVec,
    ← sub_eq_add_neg, sub_eq_zero]
  have hy : A *ᵥ x = D⁻¹ *ᵥ y ↔ y = D *ᵥ (A *ᵥ x) := by
    constructor
    · intro h
      rw [h, Matrix.mulVec_nonsing_inv_mulVec hD]
    · intro h
      rw [h, Matrix.nonsing_inv_mulVec_mulVec hD]
  rw [hy]
  constructor <;> rintro ⟨h, hy⟩
  · refine ⟨?_, hy⟩
    simpa [add_mulVec, ← mulVec_mulVec, ← hy] using h
  · refine ⟨?_, hy⟩
    simpa [add_mulVec, ← mulVec_mulVec, ← hy] using h

end ConnGouldToint.Chapter04
