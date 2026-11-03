import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.SymmetricIndefinite
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Analysis.Normed.Ring.CondNumber

/-! # Direct methods for solving linear systems

The Cholesky and symmetric indefinite factorizations in Section 4.3 of [conn2000trust].
The conversion from an `LDLᵀ` factorization to Cholesky scales the columns of
the lower triangular factor by the square roots of the diagonal entries.
-/

open Matrix
open scoped Matrix

namespace ConnGouldToint.Chapter04

section Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **(4.3.2)–(4.3.3)** A scaled perturbation with norm below one has a Neumann
inverse with the stated norm bound. -/
theorem neumann_bound_4_3_3 {T : E →L[ℝ] E} (hT : ‖T‖ < 1) :
    IsUnit (1 + T) ∧ ‖Ring.inverse (1 + T)‖ ≤ 1 / (1 - ‖T‖) := by
  have hn : ‖-T‖ < 1 := by simpa using hT
  constructor
  · simpa using isUnit_one_sub_of_norm_lt_one hn
  · have h₁ : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa using NormedRing.norm_inverse_one_sub_le_of_norm_one_le h₁ hn

/-- **(4.3.1)** Subtracting the exact and perturbed equations expresses the solution
error through the inverse of the scaled perturbation. -/
theorem perturbed_solution_4_3_1 {A dA : E →L[ℝ] E} (hA : IsUnit A)
    {x dx b db : E} (hx : A x = b) (hxd : (A + dA) (x + dx) = b + db)
    (hsmall : ‖Ring.inverse A * dA‖ < 1) :
    dx = Ring.inverse (1 + Ring.inverse A * dA) (Ring.inverse A (db - dA x)) := by
  let B := 1 + Ring.inverse A * dA
  have hB : IsUnit B := (neumann_bound_4_3_3 hsmall).1
  have hfactor : A * B = A + dA := by
    dsimp [B]
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel _ hA, one_mul]
  have he : (A + dA) dx = db - dA x := by
    rw [map_add, add_apply, hx, add_assoc] at hxd
    have hh := add_left_cancel hxd
    exact eq_sub_of_add_eq (by simpa [add_comm] using hh)
  calc
    dx = (Ring.inverse B * B) dx := by rw [Ring.inverse_mul_cancel _ hB]; rfl
    _ = Ring.inverse B (B dx) := rfl
    _ = Ring.inverse B ((Ring.inverse A * (A * B)) dx) := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ hA, one_mul]
    _ = Ring.inverse B (Ring.inverse A (db - dA x)) := by
      rw [hfactor]
      change Ring.inverse B (Ring.inverse A ((A + dA) dx)) = _
      rw [he]

/-- **(4.3.4)** The relative solution error is bounded by the condition number times
the relative data errors, scaled by the Neumann denominator. The exact right-hand
side is assumed nonzero for the relative errors to be defined. -/
theorem relative_solution_error_4_3_4 {A dA : E →L[ℝ] E} (hA : IsUnit A)
    {x dx b db : E} (hx : A x = b) (hxd : (A + dA) (x + dx) = b + db)
    (hb : b ≠ 0) (hsmall : ‖Ring.inverse A * dA‖ < 1) :
    ‖dx‖ / ‖x‖ ≤ NormedRing.condNumber A / (1 - ‖Ring.inverse A * dA‖) *
      (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖) := by
  let q := 1 - ‖Ring.inverse A * dA‖
  let C := Ring.inverse (1 + Ring.inverse A * dA)
  have hq : 0 < q := sub_pos.2 hsmall
  have hx₀ : 0 < ‖x‖ := norm_pos_iff.2 fun h => hb (by simpa [h] using hx.symm)
  have hb₀ : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hbA : ‖b‖ ≤ ‖A‖ * ‖x‖ := by rw [← hx]; exact A.le_opNorm x
  have hA₀ : 0 < ‖A‖ := by
    by_contra! h
    exact (not_lt_of_ge ((hbA.trans (mul_nonpos_of_nonpos_of_nonneg h hx₀.le)))) hb₀
  have hC : ‖C‖ ≤ 1 / q := (neumann_bound_4_3_3 hsmall).2
  have herr : ‖dx‖ ≤ (1 / q * ‖Ring.inverse A‖) * (‖db‖ + ‖dA‖ * ‖x‖) := by
    rw [perturbed_solution_4_3_1 hA hx hxd hsmall]
    change ‖C (Ring.inverse A (db - dA x))‖ ≤ _
    calc
      _ ≤ ‖C‖ * ‖Ring.inverse A (db - dA x)‖ := C.le_opNorm _
      _ ≤ (1 / q) * (‖Ring.inverse A‖ * ‖db - dA x‖) := by
        gcongr
        exact (Ring.inverse A).le_opNorm _
      _ ≤ _ := by
        rw [mul_assoc]
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add_right (dA.le_opNorm x) _)
  have hratio : 1 / ‖x‖ ≤ ‖A‖ / ‖b‖ := by
    apply (div_le_div_iff₀ hx₀ hb₀).2
    simpa using hbA
  calc
    ‖dx‖ / ‖x‖ ≤ ((1 / q * ‖Ring.inverse A‖) * (‖db‖ + ‖dA‖ * ‖x‖)) / ‖x‖ :=
      div_le_div_of_nonneg_right herr hx₀.le
    _ = (1 / q * ‖Ring.inverse A‖) * (‖db‖ * (1 / ‖x‖) + ‖dA‖) := by
      field_simp
    _ ≤ (1 / q * ‖Ring.inverse A‖) * (‖db‖ * (‖A‖ / ‖b‖) + ‖dA‖) := by gcongr
    _ = _ := by
      change _ = NormedRing.condNumber A / q * (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖)
      rw [NormedRing.condNumber]
      field_simp; ring

end Perturbation

variable {n : ℕ}

/-- **(4.3.5)** A real symmetric positive-definite matrix is the product of a
lower triangular factor and its transpose. -/
theorem cholesky_4_3_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ, L.IsLowerTriangular ∧ A = L * Lᵀ := by
  refine ⟨Matrix.cholesky A, Matrix.isLowerTriangular_cholesky A, ?_⟩
  simpa [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    (Matrix.isCholesky_cholesky hA).conjTranspose_mul_self.symm

/-- In the conversion after (4.3.5), the diagonal square root multiplies the unit
lower triangular factor on the right, giving `Lᴄ = Lᴸ D^(1/2)`. -/
theorem cholesky_of_ldl (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    let R := Matrix.diagonal (fun i => √(d i))
    (L * R) * (L * R)ᵀ = L * Matrix.diagonal d * Lᵀ := by
  dsimp only
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  simp only [Real.mul_self_sqrt (hd _), ← Matrix.mul_assoc]

/-- **(4.3.6)–(4.3.7)** Comparing the blocks of a first-column Cholesky partition
gives the pivot, column entries, and trailing Schur complement. -/
theorem cholesky_first_column_4_3_7 (a₁₁ l₁₁ : ℝ) (a l : Fin n → ℝ)
    (A L : Matrix (Fin n) (Fin n) ℝ) (hl : 0 < l₁₁)
    (h : Matrix.fromBlocks (Matrix.of fun _ _ : Unit => a₁₁) (Matrix.of fun _ j => a j) (Matrix.of fun i _ => a i) A =
      Matrix.fromBlocks (Matrix.of fun _ _ : Unit => l₁₁) 0 (Matrix.of fun i _ => l i) L *
        (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => l₁₁) 0 (Matrix.of fun i _ => l i) L)ᵀ) :
    l₁₁ = √a₁₁ ∧ (∀ i, l i = a i / l₁₁) ∧ L * Lᵀ = A - Matrix.vecMulVec l l := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] at h
  obtain ⟨h11, -, h21, h22⟩ := Matrix.fromBlocks_inj.1 h
  have h11' : a₁₁ = l₁₁ * l₁₁ := by
    simpa [Matrix.mul_apply] using congrFun (congrFun h11 ()) ()
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [h11', Real.sqrt_mul_self hl.le]
  · apply (eq_div_iff hl.ne').2
    simpa [Matrix.mul_apply] using (congrFun (congrFun h21 i) ()).symm
  · ext i j
    have he := congrFun (congrFun h22 i) j
    simp [Matrix.mul_apply, Matrix.vecMulVec] at he ⊢
    linarith

/-- **(4.3.8)** Bordering a Cholesky factor gives a triangular solve for the new
row and the square root formula for its diagonal entry. -/
theorem cholesky_next_row_4_3_8 (L A : Matrix (Fin n) (Fin n) ℝ)
    (a l : Fin n → ℝ) (α ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (h : Matrix.fromBlocks A (Matrix.of fun i _ => a i) (Matrix.of fun _ j => a j) (Matrix.of fun _ _ : Unit => α) =
      Matrix.fromBlocks L 0 (Matrix.of fun _ j => l j) (Matrix.of fun _ _ : Unit => ℓ) *
        (Matrix.fromBlocks L 0 (Matrix.of fun _ j => l j) (Matrix.of fun _ _ : Unit => ℓ))ᵀ) :
    L *ᵥ l = a ∧ ℓ = √(α - l ⬝ᵥ l) := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] at h
  obtain ⟨-, h12, -, h22⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_⟩
  · funext i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using (congrFun (congrFun h12 i) ()).symm
  · have he : α = l ⬝ᵥ l + ℓ * ℓ := by
      simpa [Matrix.mul_apply, dotProduct] using congrFun (congrFun h22 ()) ()
    rw [he, add_comm, add_sub_cancel_right, Real.sqrt_mul_self hℓ]

/-- **(4.3.9)** After the same permutation of rows and columns, a real symmetric
matrix has a unit lower triangular block `LDLᵀ` factorization with pivots of size
at most two. -/
theorem indefinite_factorization_4_3_9 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ (σ : Equiv.Perm (Fin n)) (L B : Matrix (Fin n) (Fin n) ℝ),
      Matrix.IsBlockLDL (A.submatrix σ σ) L B :=
  Matrix.exists_perm_isBlockLDL hA

end ConnGouldToint.Chapter04
