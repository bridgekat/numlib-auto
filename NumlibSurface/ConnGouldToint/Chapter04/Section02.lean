/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Spectrum

/-! # Special matrices

Orthonormal matrices in Section 4.2 of [conn2000trust].
-/

open Matrix
open scoped Matrix

namespace ConnGouldToint.Chapter04

variable {n : ℕ}

/-- **(4.2.1)** A square real matrix is orthonormal when its transpose times itself
is the identity. -/
def IsOrthonormalMatrix (Q : Matrix (Fin n) (Fin n) ℝ) : Prop := Qᵀ * Q = 1

/-- Over the reals, orthonormal matrices are precisely the members of the unitary group. -/
theorem isOrthonormalMatrix_iff_mem_unitaryGroup (Q : Matrix (Fin n) (Fin n) ℝ) :
    IsOrthonormalMatrix Q ↔ Q ∈ Matrix.unitaryGroup (Fin n) ℝ := by
  rw [IsOrthonormalMatrix, Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-- The solution of an orthonormal system is obtained by multiplying by the transpose. -/
theorem orthonormal_solution_4_2_1 {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : IsOrthonormalMatrix Q)
    {x b : Fin n → ℝ} (h : Q *ᵥ x = b) : x = Qᵀ *ᵥ b := by
  rw [← h, mulVec_mulVec, hQ, one_mulVec]

end ConnGouldToint.Chapter04
