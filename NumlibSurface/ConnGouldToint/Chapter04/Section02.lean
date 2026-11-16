/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Conn, Gould and Toint, Section 4.2: Special matrices

This module formalizes the orthonormal matrices of Section 4.2 of [conn2000trust]. A square real
matrix $Q$ is orthonormal if $Q^T Q = I$ (4.2.1). Then the system $Qx = b$ has the solution
$x = Q^T b$. The proofs use Mathlib's `Matrix.unitaryGroup`.

## Main definitions

* Equation (4.2.1), `ConnGouldToint.Chapter04.IsOrthonormalMatrix`: $Q^T Q = I$.

## Main results

* Equation (4.2.1), `ConnGouldToint.Chapter04.isOrthonormalMatrix_iff_mem_unitaryGroup`: the
  orthonormal matrices are the members of the unitary group.
* Equation (4.2.1), `ConnGouldToint.Chapter04.orthonormal_solution_4_2_1`: if $Q$ is orthonormal and
  $Qx = b$, then $x = Q^T b$.
-/

open Matrix
open scoped Matrix

namespace ConnGouldToint.Chapter04

variable {n : ℕ}

/-- **Equation (4.2.1)** of [conn2000trust]. A matrix $Q \in \mathbb{R}^{n \times n}$ is
**orthonormal** if $Q^T Q = I$. -/
def IsOrthonormalMatrix (Q : Matrix (Fin n) (Fin n) ℝ) : Prop := Qᵀ * Q = 1

/-- **Equation (4.2.1)** of [conn2000trust]. A matrix $Q \in \mathbb{R}^{n \times n}$ is orthonormal
if and only if it belongs to the unitary group `Matrix.unitaryGroup (Fin n) ℝ`, that is,
$Q^T Q = Q Q^T = I$. -/
theorem isOrthonormalMatrix_iff_mem_unitaryGroup (Q : Matrix (Fin n) (Fin n) ℝ) :
    IsOrthonormalMatrix Q ↔ Q ∈ Matrix.unitaryGroup (Fin n) ℝ := by
  rw [IsOrthonormalMatrix, Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-- **Equation (4.2.1)** of [conn2000trust]. Let $Q \in \mathbb{R}^{n \times n}$ be orthonormal, and
let $x, b \in \mathbb{R}^n$ with $Qx = b$. Then $x = Q^T b$. -/
theorem orthonormal_solution_4_2_1 {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : IsOrthonormalMatrix Q)
    {x b : Fin n → ℝ} (h : Q *ᵥ x = b) : x = Qᵀ *ᵥ b := by
  rw [← h, mulVec_mulVec, hQ, one_mulVec]

end ConnGouldToint.Chapter04
