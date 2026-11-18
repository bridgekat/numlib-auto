/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section01
import NumlibSurface.BenIsraelGreville.Chapter01.Section06

/-!
# Spectral inverse of a diagonalizable matrix

Section 4.3 of [benIsrael2003generalized] constructs the spectral inverse by replacing
each eigenvalue in a diagonal form with its generalized reciprocal.
-/

namespace BenIsraelGreville.Chapter04

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equation (19)** of [benIsrael2003generalized], Chapter 4. Replacing each eigenvalue
in a diagonal form of $A$ by its reciprocal, with zero sent to zero, gives a
reflexive inverse of $A$ commuting with $A$. -/
theorem diagonalizable_spectral_inverse (P : (Matrix n n ℂ)ˣ) (eigenvalues : n → ℂ) :
    IsGroupInverse
      ((P : Matrix n n ℂ) * diagonal eigenvalues * (↑P⁻¹ : Matrix n n ℂ))
      ((P : Matrix n n ℂ) * diagonal (fun i => (eigenvalues i)⁻¹) * (↑P⁻¹ : Matrix n n ℂ)) := by
  suffices IsGroupInverse (diagonal eigenvalues) (diagonal (fun i => (eigenvalues i)⁻¹)) by
    exact this.conj P
  rw [isGroupInverse_iff]
  refine ⟨?_, ?_, ?_⟩
  · change diagonal eigenvalues * diagonal (fun i => (eigenvalues i)⁻¹) =
      diagonal (fun i => (eigenvalues i)⁻¹) * diagonal eigenvalues
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : eigenvalues i = 0 <;> simp [h]
  · rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : eigenvalues i = 0 <;> simp [h]

/-- **Equation (18)** of [benIsrael2003generalized], Chapter 4.
The action on the diagonalizing columns determines the matrix uniquely. -/
theorem diagonalizable_spectral_inverse_of_columns (P : (Matrix n n ℂ)ˣ) (eigenvalues : n → ℂ)
    (X : Matrix n n ℂ) :
    X * (P : Matrix n n ℂ) = (P : Matrix n n ℂ) * (diagonal eigenvalues).pinv ↔
      X = (P : Matrix n n ℂ) * (diagonal eigenvalues).pinv * (↑P⁻¹ : Matrix n n ℂ) := by
  constructor
  · intro h
    calc
      X = (X * (P : Matrix n n ℂ)) * (↑P⁻¹ : Matrix n n ℂ) :=
        (Units.mul_inv_cancel_right X P).symm
      _ = _ := by rw [h]
  · rintro rfl
    exact Units.inv_mul_cancel_right _ P

/-- **Equation (19)** of [benIsrael2003generalized], Chapter 4.
The Moore–Penrose inverse in diagonalizing coordinates gives the
group inverse in the original coordinates. -/
theorem diagonalizable_spectral_inverse_pinv (P : (Matrix n n ℂ)ˣ) (eigenvalues : n → ℂ) :
    IsGroupInverse
      ((P : Matrix n n ℂ) * diagonal eigenvalues * (↑P⁻¹ : Matrix n n ℂ))
      ((P : Matrix n n ℂ) * (diagonal eigenvalues).pinv * (↑P⁻¹ : Matrix n n ℂ)) := by
  rw [BenIsraelGreville.Chapter01.pinv_diagonal]
  exact diagonalizable_spectral_inverse P eigenvalues

end BenIsraelGreville.Chapter04
