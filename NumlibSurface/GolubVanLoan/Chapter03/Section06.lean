import NumlibSurface.GolubVanLoan.Chapter03.Section02

/-!
# Golub–Van Loan §3.6: parallel LU

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §3.6.
By the scope rules only the precise mathematics of §3.6.1 is formalized: the pivoted factorization
of a tall block column (3.6.2) and the partial factorization (3.6.5). The algorithm itself is "left
as an exercise" in the book (P3.6.1), so there is no program; the assembly of the pivoted block
LU factorization from the pieces (`blockLUPivoting`) and the induction on the block columns that
builds one for every square matrix (`exists_blockLUPivoting`) are theorems. The block-cyclic
distribution, processor grids, (3.6.6), the figures and tournament pivoting (§3.6.3) state no
proposition.
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

/-- **§3.6.1, the assembled pivoted block LU factorization**: with `P₁ A = [Ã₁₁ Ã₁₂; Ã₂₁ Ã₂₂]`
(3.6.3), the block column factored as `[Ã₁₁; Ã₂₁] = [L₁₁; L₂₁] U₁₁` (3.6.2), `L₁₁ U₁₂ = Ã₁₂`
(3.6.4), and a pivoted factorization `P^{new} A^{new} = L^{new} U^{new}` of
`A^{new} = Ã₂₂ - L₂₁ U₁₂` (3.6.5): with `L̃₂₁ = P^{new} L₂₁` and
`P = [I 0; 0 P^{new}] P₁` (the permutation matrix of `σ₁` followed by `[I 0; 0 σ^{new}]`),
"`P A = [L₁₁ 0; L̃₂₁ L^{new}] [U₁₁ U₁₂; 0 U^{new}]` is the pivoted block LU factorization of `A`".
On `Fin (r + s)` through `finSumFinEquiv`. -/
theorem blockLUPivoting {A : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    {σ₁ : Equiv.Perm (Fin (r + s))}
    {Ã₁₁ L₁₁ U₁₁ : Matrix (Fin r) (Fin r) ℝ} {Ã₁₂ U₁₂ : Matrix (Fin r) (Fin s) ℝ}
    {Ã₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ} {Ã₂₂ : Matrix (Fin s) (Fin s) ℝ}
    {σ : Equiv.Perm (Fin s)} {L U : Matrix (Fin s) (Fin s) ℝ}
    (hP₁ : σ₁.permMatrix ℝ * A =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks Ã₁₁ Ã₁₂ Ã₂₁ Ã₂₂))
    (h₁₁ : IsLU Ã₁₁ L₁₁ U₁₁) (h₂₁ : Ã₂₁ = L₂₁ * U₁₁) (h₁₂ : L₁₁ * U₁₂ = Ã₁₂)
    (hnew : IsLU (σ.permMatrix ℝ * (Ã₂₂ - L₂₁ * U₁₂)) L U) :
    (σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r)) σ)).permMatrix ℝ =
        reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (σ.permMatrix ℝ)) *
          σ₁.permMatrix ℝ ∧
      IsLU ((σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r)) σ)).permMatrix ℝ *
          A)
        (reindex finSumFinEquiv finSumFinEquiv (fromBlocks L₁₁ 0 (σ.permMatrix ℝ * L₂₁) L))
        (reindex finSumFinEquiv finSumFinEquiv (fromBlocks U₁₁ U₁₂ 0 U)) := by
  have hP :
      (σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r)) σ)).permMatrix ℝ =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (σ.permMatrix ℝ)) *
        σ₁.permMatrix ℝ := by
    rw [permMatrix_mul, permMatrix_permCongr_sumCongr, Matrix.permMatrix_refl]
  refine ⟨hP, ?_⟩
  have hPA :
      (σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r)) σ)).permMatrix ℝ * A =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks Ã₁₁ Ã₁₂ (σ.permMatrix ℝ * Ã₂₁) (σ.permMatrix ℝ * Ã₂₂)) := by
    rw [hP, Matrix.mul_assoc, hP₁, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  rw [hPA]
  refine blockLU_of_schur h₁₁ (by rw [h₂₁, Matrix.mul_assoc]) h₁₂ ?_
  rwa [Matrix.mul_assoc, ← Matrix.mul_sub]

/-- **§3.6.1, the induction on the block columns**: for a block size `r > 0`, every square `A`
has a pivoted factorization `P A = L U` with `|ℓ_ij| ≤ 1`, built block column by block column —
(3.6.2) on the first block column (a rectangular partial pivoting factorization), the solve
(3.6.4) for `U₁₂`, the pivoted factorization of `A^{new}` by induction, assembled by
`blockLUPivoting`. The book assumes `n = r N` "for clarity"; the last block column may be
narrower here. -/
theorem exists_blockLUPivoting {r : ℕ} (hr : 0 < r) :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), ∃ (σ : Equiv.Perm (Fin n))
      (L U : Matrix (Fin n) (Fin n) ℝ), IsLU (σ.permMatrix ℝ * A) L U ∧ ∀ i j, |L i j| ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A
  by_cases hn : n ≤ r
  · obtain ⟨σ, L, U, h, hL⟩ := equation_3_6_2 (r := n) (s := 0) A
    exact ⟨σ, L, U, isRectLU_iff_isLU.1 h, hL⟩
  obtain ⟨s, rfl⟩ : ∃ s, n = r + s := ⟨n - r, by omega⟩
  -- (3.6.2) on the first block column
  obtain ⟨σ₁, L, U₁₁, hRect, hL⟩ :=
    equation_3_6_2 (r := r) (s := s) (fun i k => A i (finSumFinEquiv (Sum.inl k)))
  set Ã := σ₁.permMatrix ℝ * A with hÃ
  set Ã₁₁ : Matrix (Fin r) (Fin r) ℝ := of fun i j =>
    Ã (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) with hÃ₁₁
  set Ã₁₂ : Matrix (Fin r) (Fin s) ℝ := of fun i j =>
    Ã (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) with hÃ₁₂
  set Ã₂₁ : Matrix (Fin s) (Fin r) ℝ := of fun i j =>
    Ã (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) with hÃ₂₁
  set Ã₂₂ : Matrix (Fin s) (Fin s) ℝ := of fun i j =>
    Ã (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) with hÃ₂₂
  set L₁₁ : Matrix (Fin r) (Fin r) ℝ := of fun i k => L (finSumFinEquiv (Sum.inl i)) k with hL₁₁
  set L₂₁ : Matrix (Fin s) (Fin r) ℝ := of fun i k => L (finSumFinEquiv (Sum.inr i)) k with hL₂₁
  have hcol : ∀ i k, Ã i (finSumFinEquiv (Sum.inl k)) = ∑ t, L i t * U₁₁ t k := fun i k => by
    rw [← mul_apply, hRect.mul_eq, hÃ, mul_apply]
    rfl
  have hL₁₁unit : L₁₁.IsUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : (i : ℕ) < j := Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 hij)
      exact hRect.lower _ _ (by
        simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, add_zero]; exact hij')
    · exact hRect.lower_apply_self _ _ (by simp)
  have hU₁₁upper : U₁₁.IsUpperTriangular := fun i j hij =>
    hRect.upper i j (by have := Fin.lt_def.1 (show j < i from hij); omega)
  have h₁₁ : IsLU Ã₁₁ L₁₁ U₁₁ := ⟨hL₁₁unit, hU₁₁upper, by
    ext i j; rw [mul_apply, hÃ₁₁, of_apply, hcol]; rfl⟩
  have h₂₁ : Ã₂₁ = L₂₁ * U₁₁ := by
    ext i j; rw [mul_apply, hÃ₂₁, of_apply, hcol]; rfl
  -- (3.6.4): the multiple right-hand side solve
  have hdetL : IsUnit L₁₁.det := by rw [hL₁₁unit.det_eq_one]; exact isUnit_one
  set U₁₂ := L₁₁⁻¹ * Ã₁₂ with hU₁₂
  have h₁₂ : L₁₁ * U₁₂ = Ã₁₂ := by
    rw [hU₁₂, ← Matrix.mul_assoc, mul_nonsing_inv _ hdetL, Matrix.one_mul]
  -- the induction hypothesis on `A^{new}`
  obtain ⟨σ, Ln, Un, hnew, hLn⟩ := ih s (by omega) (Ã₂₂ - L₂₁ * U₁₂)
  have hP₁ : σ₁.permMatrix ℝ * A =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks Ã₁₁ Ã₁₂ Ã₂₁ Ã₂₂) := by
    ext i j
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> rfl
  obtain ⟨_, h⟩ := blockLUPivoting hP₁ h₁₁ h₂₁ h₁₂ hnew
  refine ⟨_, _, _, h, fun i j => ?_⟩
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b
  · exact hL _ _
  · simp
  · rw [fromBlocks_apply₂₁, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    exact hL _ _
  · exact hLn _ _

end GolubVanLoan.Chapter03
