/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section01

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

end BenIsraelGreville.Chapter04
