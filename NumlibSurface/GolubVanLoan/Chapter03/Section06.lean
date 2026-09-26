import NumlibSurface.GolubVanLoan.Chapter03.Section02

/-!
# Golub–Van Loan §3.6: parallel LU

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §3.6.
By the scope rules only the precise mathematics of §3.6.1 is formalized: the pivoted factorization
of a tall block column (3.6.2) and the partial factorization (3.6.5). The algorithm itself is "left
as an exercise" in the book (P3.6.1), so there is no program. The block-cyclic distribution,
processor grids, (3.6.6), the figures and tournament pivoting (§3.6.3) state no proposition.
A block row or column split is `Fin (r + s)` read as `Fin r ⊕ Fin s`.
-/

open Matrix

namespace GolubVanLoan.Chapter03

variable {r s : ℕ}

/-- **(3.6.2)**: "using an obvious rectangular matrix version of Algorithm 3.4.1 we obtain the
factorization `P₁ [A₁₁; …; A_N1] = [L₁₁; …; L_N1] U₁₁`" — a tall block column
`W ∈ ℝ^{(r+s)×r}` has a row permutation `P₁` with `P₁ W = L U₁₁`, `L` unit lower trapezoidal with
`|ℓ_ij| ≤ 1` and `U₁₁` upper triangular. -/
theorem equation_3_6_2 (W : Matrix (Fin (r + s)) (Fin r) ℝ) :
    ∃ (σ : Equiv.Perm (Fin (r + s))) (L : Matrix (Fin (r + s)) (Fin r) ℝ)
      (U : Matrix (Fin r) (Fin r) ℝ), IsRectLU (σ.permMatrix ℝ * W) L U ∧ ∀ i j, |L i j| ≤ 1 := by
  obtain ⟨σ, L, U, h, hL⟩ := exists_permMatrix_mul_isRectLU W (by omega)
  exact ⟨σ, L, U, h, fun i j => by simpa only [Real.norm_eq_abs] using hL i j⟩

/-- **(3.6.3)–(3.6.5)**, the partial factorization after Parts A–C: with `P₁ A = [Ã₁₁ Ã₁₂; Ã₂₁
Ã₂₂]`, the block column factored as `[Ã₁₁; Ã₂₁] = [L₁₁; L₂₁] U₁₁` (3.6.2) and the multiple
right-hand side solve `L₁₁ U₁₂ = Ã₁₂` (3.6.4),
`P₁ A = [L₁₁ 0; L₂₁ I] [I 0; 0 A^{new}] [U₁₁ U₁₂; 0 I]` with `A^{new} = Ã₂₂ - L₂₁ U₁₂`. The
Schur-complement identity (3.2.9) applied to the permuted matrix. -/
theorem equation_3_6_5 {A₁₁ L₁₁ U₁₁ : Matrix (Fin r) (Fin r) ℝ}
    {A₁₂ U₁₂ : Matrix (Fin r) (Fin s) ℝ} {A₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ}
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ) (h₁₁ : A₁₁ = L₁₁ * U₁₁) (h₂₁ : A₂₁ = L₂₁ * U₁₁)
    (h₁₂ : L₁₁ * U₁₂ = A₁₂) :
    fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ =
      fromBlocks L₁₁ 0 L₂₁ 1 * fromBlocks 1 0 0 (A₂₂ - L₂₁ * U₁₂) * fromBlocks U₁₁ U₁₂ 0 1 :=
  (equation_3_2_9 A₂₂ h₁₁ h₂₁ h₁₂).1

end GolubVanLoan.Chapter03
