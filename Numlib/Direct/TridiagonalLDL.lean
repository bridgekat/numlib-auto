import Numlib.LinearAlgebra.Matrix.Cholesky

/-!
# Positive definite tridiagonal LDL factorization

The existing Thomas pivots and multipliers specialize to a symmetric LDL factorization.
Their positivity is equivalent to positive definiteness, so a nonpositive computed pivot
is a certificate that the symmetric input is not positive definite.
-/

noncomputable section
namespace Matrix
namespace TridiagonalLDL

/-- The symmetric tridiagonal matrix with diagonal `d` and subdiagonal `e`.
The unused value `e 0` has no effect on the matrix. -/
def matrix (d e : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  tridiagonalOfNat d e (fun i => e (i + 1)) n

/-- The scalar Thomas pivot on the symmetric tridiagonal input. -/
def pivot (d e : ℕ → ℝ) : ℕ → ℝ := thomasAlpha d e (fun i => e (i + 1))

/-- The scalar lower multiplier on the symmetric tridiagonal input. -/
def multiplier (d e : ℕ → ℝ) : ℕ → ℝ := thomasBeta d e (fun i => e (i + 1))

/-- The exact unit lower bidiagonal Thomas factor. -/
def lower (d e : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  thomasLower d e (fun i => e (i + 1)) n

/-- The diagonal matrix of scalar pivots. -/
def diagonal (d e : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => pivot d e i

/-- The symmetric Thomas upper factor is the pivot diagonal times the lower transpose. -/
theorem diagonal_mul_lower_transpose (d e : ℕ → ℝ) {n : ℕ}
    (h : ∀ i, i + 1 < n → pivot d e i ≠ 0) :
    diagonal d e n * (lower d e n)ᵀ = thomasUpper d e (fun i => e (i + 1)) n := by
  ext i j
  simp only [diagonal, Matrix.diagonal_mul, transpose_apply, lower, thomasLower,
    thomasUpper, of_apply]
  by_cases hij : i = j
  · subst j
    simp [pivot]
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ite_false]
    by_cases hs : (i : ℕ) + 1 = j
    · simp only [hs, ite_true]
      rw [← hs, thomasBeta_succ]
      change pivot d e i * (e (i + 1) / pivot d e i) = e (i + 1)
      exact mul_div_cancel₀ _ (h i (by omega))
    · simp only [hs, ite_false, mul_zero]

/-- Nonvanishing earlier pivots give the actual LDL factorization, including when
the final pivot is zero or negative. -/
theorem isLDM (d e : ℕ → ℝ) {n : ℕ}
    (h : ∀ i, i + 1 < n → pivot d e i ≠ 0) :
    IsLDM (matrix d e n) (lower d e n) (diagonal d e n) (lower d e n) := by
  have ht := isLU_tridiagonal_thomas d e (fun i => e (i + 1)) h
  refine ⟨ht.isUnitLowerTriangular, isDiag_diagonal _, ht.isUnitLowerTriangular, ?_⟩
  rw [Matrix.mul_assoc, diagonal_mul_lower_transpose d e h]
  exact ht.mul_eq

/-- Positive pivots imply positive definiteness of the original symmetric tridiagonal. -/
theorem posDef_of_pivot_pos (d e : ℕ → ℝ) {n : ℕ}
    (h : ∀ i, i < n → 0 < pivot d e i) : (matrix d e n).PosDef := by
  have ht := isLDM d e (n := n) (fun i hi => (h i (by omega)).ne')
  have ht' : IsLDM (matrix d e n) (lower d e n) (diagonal d e n)
      (lower d e n)ᴴᵀ := by simpa using ht
  apply ht'.posDef_iff.mpr
  intro i
  simpa only [diagonal, Matrix.diagonal_apply_eq] using h i i.isLt

/-- A leading prefix is exactly the corresponding symmetric tridiagonal matrix. -/
theorem matrix_submatrix (d e : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (matrix d e n).submatrix (Fin.castLE hmn) (Fin.castLE hmn) = matrix d e m := rfl

/-- Positive definiteness forces every actual recursively computed Thomas pivot positive. -/
theorem pivot_pos_of_posDef (d e : ℕ → ℝ) {n : ℕ} (hA : (matrix d e n).PosDef)
    {i : ℕ} (hi : i < n) : 0 < pivot d e i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hm : i + 1 ≤ n := by omega
    have hp : (matrix d e (i + 1)).PosDef := by
      rw [← matrix_submatrix d e hm]
      exact hA.submatrix (Fin.castLE_injective hm)
    have ht := isLDM d e (n := i + 1) (fun j hj =>
      (ih j (by omega) (by omega)).ne')
    have ht' : IsLDM (matrix d e (i + 1)) (lower d e (i + 1)) (diagonal d e (i + 1))
        (lower d e (i + 1))ᴴᵀ := by simpa using ht
    have hpos := ht'.posDef_iff.mp hp (Fin.last i)
    simpa only [diagonal, Matrix.diagonal_apply_eq, Fin.val_last] using hpos

/-- A nonpositive actual pivot certifies failure of positive definiteness. -/
theorem not_posDef_of_pivot_nonpos (d e : ℕ → ℝ) {n i : ℕ} (hi : i < n)
    (hp : pivot d e i ≤ 0) : ¬(matrix d e n).PosDef := by
  intro hA
  exact (not_lt_of_ge hp) (pivot_pos_of_posDef d e hA hi)

/-- Positive definiteness is exactly positivity of all recursively computed pivots. -/
theorem posDef_iff_pivot_pos (d e : ℕ → ℝ) (n : ℕ) :
    (matrix d e n).PosDef ↔ ∀ i, i < n → 0 < pivot d e i :=
  ⟨fun h _ hi => pivot_pos_of_posDef d e h hi, posDef_of_pivot_pos d e⟩

end TridiagonalLDL
end Matrix
