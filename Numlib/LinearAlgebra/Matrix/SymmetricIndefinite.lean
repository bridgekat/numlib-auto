/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LDL`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.GroupTheory.Perm.Fin
import Numlib.LinearAlgebra.Matrix.LU

/-!
# Factorizations of symmetric indefinite matrices

Factorization specifications for symmetric indefinite matrices ([golub2013matrix] §4.4;
[higham2002accuracy] Ch. 11): the Aasen factorization `P A Pᵀ = L T Lᵀ` with `T` tridiagonal
(`Matrix.IsAasen`) and the block `L D Lᵀ` factorization with `1 × 1` and `2 × 2` pivots
(`Matrix.IsBlockLDL`, `Matrix.IsPivotBlockDiagonal`), with their existence theorems and solve
chains.

## Main definitions

* `Matrix.IsPivotBlockDiagonal D`: `D` is symmetric and block diagonal with `1 × 1` and `2 × 2`
  diagonal blocks, on `Fin n`: a symmetric tridiagonal matrix no two consecutive subdiagonal
  entries of which are nonzero.
* `Matrix.IsBlockLDL A L D`: `A = L D Lᵀ` with `L` unit lower triangular carrying the identity in
  each `2 × 2` diagonal block and `D` pivot-block-diagonal.
* `Matrix.IsAasen A L T`: `A = L T Lᵀ` with `L` unit lower triangular of first column `e₁` and
  `T` symmetric tridiagonal.

## Main results

* `Matrix.exists_isUnit_principal_pivot`: a nonzero symmetric matrix has a nonsingular `1 × 1` or
  `2 × 2` principal pivot, the step of the existence proof of (4.4.2).
* `Matrix.exists_perm_isBlockLDL`: [golub2013matrix] (4.4.2), every symmetric matrix has a
  symmetric permutation with a block `L D Lᵀ` factorization, by bordering one pivot block at a
  time (`Matrix.isBlockLDL_pivot`, `Matrix.exists_perm_isBlockLDL_of_pivot`, which carries a
  property of the multipliers through the induction);
  `Matrix.exists_perm_isBlockLDL_abs_le`: with the Bunch–Parlett pivot rule the multipliers are
  bounded by `max (1/α) (1/(1 - α))` (not by `1`, as the book prints).
* `Matrix.exists_perm_isAasen`: [golub2013matrix] (4.4.1), the Aasen factorization with
  `|l_ij| ≤ 1`, by the Parlett–Reid process on the trailing block.
* `Matrix.IsBlockLDL.solve`, `Matrix.IsAasen.solve`: the solve chains `L z = P b`, `D w = z` (or
  `T w = z`), `Lᵀ y = w`, `x = Pᵀ y`.
* `Matrix.IsAasen.isUpperHessenberg_mul_transpose`: `A = L H` with `H = T Lᵀ` upper Hessenberg,
  [golub2013matrix] (4.4.5).

## Implementation notes

These are specifications, not algorithms, in the style of `Matrix.IsLU` and `Matrix.IsLDM`
(`Numlib/LinearAlgebra/Matrix/LU`). The permutation is a `σ : Equiv.Perm (Fin n)` acting as
`A.submatrix σ σ`, which is `P A Pᵀ` for `P = σ.permMatrix`. The `D` of a block `L D Lᵀ`
factorization is described on `Fin n` by its entries rather than by a sigma-typed block
structure, so that `L D Lᵀ` stays an ordinary product. What is numerical about the symmetric
indefinite factorizations — the Bunch–Parlett element growth, the Stewart–Todd bound — is in
`Numlib/Direct/SymmetricIndefinite`; the equilibrium (saddle point) matrix of §4.4.5 is
`Matrix.saddleMatrix` of `Numlib/LinearAlgebra/Matrix/SchurComplement`.

## References

* [golub2013matrix] §4.4.
* [higham2002accuracy] Ch. 11.
-/

namespace Matrix

variable {n : ℕ} {K : Type*}

/-- **Block diagonal with `1 × 1` and `2 × 2` pivot blocks** ([golub2013matrix] (4.4.2): "`D` is a
direct sum of 1-by-1 and 2-by-2 pivot blocks"): `D` is symmetric and tridiagonal, and no two
consecutive subdiagonal entries are nonzero, so that each nonzero subdiagonal entry `D (i+1) i`
belongs to a `2 × 2` block on the indices `i, i + 1`. -/
structure IsPivotBlockDiagonal [Zero K] (D : Matrix (Fin n) (Fin n) K) : Prop where
  /-- The block diagonal matrix is symmetric. -/
  isSymm : D.IsSymm
  /-- The block diagonal matrix is tridiagonal. -/
  isTridiagonal : D.IsTridiagonal
  /-- Two `2 × 2` blocks do not overlap. -/
  apply_eq_zero : ∀ (i : ℕ) (h : i + 2 < n), D ⟨i + 1, by omega⟩ ⟨i, by omega⟩ ≠ 0 →
    D ⟨i + 2, h⟩ ⟨i + 1, by omega⟩ = 0

/-- **The block `L D Lᵀ` factorization** ([golub2013matrix] (4.4.2)): `L` unit lower triangular,
`D` block diagonal with `1 × 1` and `2 × 2` pivots, `L` the identity on each `2 × 2` diagonal
block, and `L D Lᵀ = A`. -/
structure IsBlockLDL [Semiring K] (A L D : Matrix (Fin n) (Fin n) K) : Prop where
  /-- The lower factor is unit lower triangular. -/
  isUnitLowerTriangular : L.IsUnitLowerTriangular
  /-- The middle factor is block diagonal with `1 × 1` and `2 × 2` blocks. -/
  isPivotBlockDiagonal : D.IsPivotBlockDiagonal
  /-- The lower factor is the identity on each `2 × 2` diagonal block. -/
  block : ∀ i j : Fin n, (j : ℕ) + 1 = i → D i j ≠ 0 → L i j = 0
  /-- The factors multiply to `A`. -/
  mul_eq : L * D * Lᵀ = A

/-- A matrix with a block `L D Lᵀ` factorization is symmetric. -/
theorem IsBlockLDL.isSymm [CommSemiring K] {A L D : Matrix (Fin n) (Fin n) K}
    (h : IsBlockLDL A L D) : A.IsSymm := by
  rw [IsSymm, ← h.mul_eq, transpose_mul, transpose_mul, transpose_transpose,
    h.isPivotBlockDiagonal.isSymm.eq, Matrix.mul_assoc]

/-- **The solve chain of the block `L D Lᵀ` factorization** ([golub2013matrix], after (4.4.2)):
if `P A Pᵀ = L D Lᵀ` with `P` the permutation matrix of `σ`, then solving `L z = P b`, `D w = z`,
`Lᵀ y = w` and setting `x = Pᵀ y` solves `A x = b`. -/
theorem IsBlockLDL.solve [CommSemiring K] {A L D : Matrix (Fin n) (Fin n) K}
    {σ : Equiv.Perm (Fin n)} (h : IsBlockLDL (A.submatrix σ σ) L D) {b z w y : Fin n → K}
    (hz : L *ᵥ z = b ∘ σ) (hw : D *ᵥ w = z) (hy : Lᵀ *ᵥ y = w) :
    A *ᵥ (y ∘ σ.symm) = b := by
  have h1 : A.submatrix σ σ *ᵥ y = b ∘ σ := by
    rw [← h.mul_eq, ← mulVec_mulVec, ← mulVec_mulVec, hy, hw, hz]
  rw [submatrix_mulVec_equiv] at h1
  funext i
  simpa using congrFun h1 (σ.symm i)

/-- **The Aasen factorization** ([golub2013matrix] (4.4.1), §4.4.2): `A = L T Lᵀ` with `L` unit
lower triangular whose first column is `e₁` (the book's `L(:, 1) = e₁`) and `T` symmetric
tridiagonal. -/
structure IsAasen [Semiring K] (A L T : Matrix (Fin n) (Fin n) K) : Prop where
  /-- The lower factor is unit lower triangular. -/
  isUnitLowerTriangular : L.IsUnitLowerTriangular
  /-- The first column of the lower factor is `e₁`. -/
  col_zero : ∀ (i : Fin n) (h : 0 < n), i ≠ ⟨0, h⟩ → L i ⟨0, h⟩ = 0
  /-- The middle factor is symmetric. -/
  isSymm : T.IsSymm
  /-- The middle factor is tridiagonal. -/
  isTridiagonal : T.IsTridiagonal
  /-- The factors multiply to `A`. -/
  mul_eq : L * T * Lᵀ = A

/-- [golub2013matrix] (4.4.5): if `A = L T Lᵀ` is an Aasen factorization, then `H = T Lᵀ` is
upper Hessenberg and `A = L H`, so that the columns of `A` are the combinations
`A(:, j) = ∑_{k ≤ j+1} L(:, k) h_kj` from which Aasen's method computes `L` column by column. -/
theorem IsAasen.isUpperHessenberg_mul_transpose [CommRing K] {A L T : Matrix (Fin n) (Fin n) K}
    (h : IsAasen A L T) : (T * Lᵀ).IsUpperHessenberg ∧ A = L * (T * Lᵀ) :=
  ⟨h.isTridiagonal.isUpperHessenberg.mul_isUpperTriangular
      h.isUnitLowerTriangular.isLowerTriangular.transpose_isUpperTriangular,
    by rw [← h.mul_eq, Matrix.mul_assoc]⟩

/-- **The solve chain of the Aasen factorization** ([golub2013matrix], after (4.4.2)): if
`P A Pᵀ = L T Lᵀ`, then `L z = P b`, `T w = z`, `Lᵀ y = w` and `x = Pᵀ y` give `A x = b`. -/
theorem IsAasen.solve [CommSemiring K] {A L T : Matrix (Fin n) (Fin n) K}
    {σ : Equiv.Perm (Fin n)} (h : IsAasen (A.submatrix σ σ) L T) {b z w y : Fin n → K}
    (hz : L *ᵥ z = b ∘ σ) (hw : T *ᵥ w = z) (hy : Lᵀ *ᵥ y = w) :
    A *ᵥ (y ∘ σ.symm) = b := by
  have h1 : A.submatrix σ σ *ᵥ y = b ∘ σ := by
    rw [← h.mul_eq, ← mulVec_mulVec, ← mulVec_mulVec, hy, hw, hz]
  rw [submatrix_mulVec_equiv] at h1
  funext i
  simpa using congrFun h1 (σ.symm i)

/-- **A nonzero symmetric matrix has a nonsingular principal pivot of order one or two**
([golub2013matrix] §4.4.4, the step "if `A` is nonzero it is always possible to choose `s` and
`P₁` so that `E` is nonsingular"): a nonzero diagonal entry, or a pair `i ≠ j` whose principal
`2 × 2` minor is nonzero. If every diagonal entry vanishes, a nonzero `A i j`, `i ≠ j`, gives the
minor `-A i j ^ 2`. -/
theorem exists_isUnit_principal_pivot {m : Type*} [Field K] {A : Matrix m m K} (hA : A.IsSymm)
    (hA0 : A ≠ 0) :
    (∃ i, A i i ≠ 0) ∨ ∃ i j, i ≠ j ∧ A i i * A j j - A i j * A j i ≠ 0 := by
  by_cases hd : ∃ i, A i i ≠ 0
  · exact Or.inl hd
  push Not at hd
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hA0 (Matrix.ext hcon)
  refine Or.inr ⟨i, j, fun h => hij (by rw [h]; exact hd j), ?_⟩
  rw [hd i, hd j, zero_mul, zero_sub, hA.apply i j, neg_ne_zero]
  exact mul_ne_zero hij hij

/-! ### Existence of the block `L D Lᵀ` factorization -/

section Bordering

variable [Field K] {s m : ℕ}

/-- The Schur complement `N₂₂ - N₂₁ N₁₁⁻¹ N₁₂` of the leading block of a two-block matrix. -/
noncomputable def pivotSchur (N : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) K) :
    Matrix (Fin m) (Fin m) K :=
  N.toBlocks₂₂ - N.toBlocks₂₁ * N.toBlocks₁₁⁻¹ * N.toBlocks₁₂

/-- The lower factor bordered by one pivot block: `[I 0; C E⁻¹ L']`. -/
noncomputable def pivotLower (N : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) K)
    (L' : Matrix (Fin m) (Fin m) K) : Matrix (Fin (s + m)) (Fin (s + m)) K :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 (N.toBlocks₂₁ * N.toBlocks₁₁⁻¹) L')

/-- The block diagonal factor bordered by one pivot block: `[E 0; 0 D']`. -/
noncomputable def pivotDiag (N : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) K)
    (D' : Matrix (Fin m) (Fin m) K) : Matrix (Fin (s + m)) (Fin (s + m)) K :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks N.toBlocks₁₁ 0 0 D')

/-- **The bordering step of the block `L D Lᵀ` factorization** ([golub2013matrix] §4.4.4): if
`N = [E Cᵀ; C B]` is symmetric with a nonsingular pivot block `E` of order `s ≤ 2`, and the Schur
complement `B - C E⁻¹ Cᵀ` has the block factorization `L' D' L'ᵀ`, then
`[I 0; C E⁻¹ L'] [E 0; 0 D'] [I 0; C E⁻¹ L']ᵀ` is a block `L D Lᵀ` factorization of `N`, read on
`Fin (s + m)`. -/
theorem isBlockLDL_pivot (hs : s ≤ 2) {N : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) K}
    (hN : N.IsSymm) (hE : IsUnit N.toBlocks₁₁.det) {L' D' : Matrix (Fin m) (Fin m) K}
    (h : IsBlockLDL (pivotSchur N) L' D') :
    IsBlockLDL (reindex finSumFinEquiv finSumFinEquiv N) (pivotLower N L') (pivotDiag N D') := by
  have hE' : N.toBlocks₁₁.IsSymm := IsSymm.ext fun i j => hN.apply (Sum.inl i) (Sum.inl j)
  have hC : N.toBlocks₁₂ = N.toBlocks₂₁ᵀ := by
    ext i j
    exact hN.apply (Sum.inr j) (Sum.inl i)
  have hD' := h.isPivotBlockDiagonal
  have hL' := h.isUnitLowerTriangular
  -- entries of the two factors
  have hLe : ∀ i j, pivotLower N L' i j =
      fromBlocks 1 0 (N.toBlocks₂₁ * N.toBlocks₁₁⁻¹) L' (finSumFinEquiv.symm i)
        (finSumFinEquiv.symm j) := fun _ _ => rfl
  have hDe : ∀ i j, pivotDiag N D' i j =
      fromBlocks N.toBlocks₁₁ 0 0 D' (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) :=
    fun _ _ => rfl
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨?_, ?_, fun i hi hne => ?_⟩, fun i j hij hne => ?_, ?_⟩
  · -- lower triangular
    have hij' : (i : ℕ) < j := OrderDual.toDual_lt_toDual.1 hij
    rw [hLe]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;>
      rcases finSumFinEquiv_symm_cases j with ⟨hj, ej⟩ | ⟨hj, ej⟩ <;> rw [ei, ej]
    · rw [fromBlocks_apply₁₁, one_apply_ne]
      exact fun he => by simp only [Fin.mk.injEq] at he; omega
    · rw [fromBlocks_apply₁₂, zero_apply]
    · omega
    · rw [fromBlocks_apply₂₂]
      exact hL'.isLowerTriangular (OrderDual.toDual_lt_toDual.2 (Fin.lt_def.2 (by simp; omega)))
  · -- unit diagonal
    rw [hLe]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;> rw [ei]
    · rw [fromBlocks_apply₁₁, one_apply_eq]
    · rw [fromBlocks_apply₂₂, hL'.diag_eq_one]
  · -- `D` is symmetric
    refine IsSymm.ext fun i j => ?_
    rw [hDe, hDe]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;>
      rcases finSumFinEquiv_symm_cases j with ⟨hj, ej⟩ | ⟨hj, ej⟩ <;> rw [ei, ej]
    · rw [fromBlocks_apply₁₁, fromBlocks_apply₁₁, hE'.apply]
    · rw [fromBlocks_apply₂₁, fromBlocks_apply₁₂, zero_apply, zero_apply]
    · rw [fromBlocks_apply₂₁, fromBlocks_apply₁₂, zero_apply, zero_apply]
    · rw [fromBlocks_apply₂₂, fromBlocks_apply₂₂, hD'.isSymm.apply]
  · -- `D` is tridiagonal
    rw [isTridiagonal_iff_fin]
    intro i j hij
    rw [hDe]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;>
      rcases finSumFinEquiv_symm_cases j with ⟨hj, ej⟩ | ⟨hj, ej⟩ <;> rw [ei, ej]
    · omega
    · rw [fromBlocks_apply₁₂, zero_apply]
    · rw [fromBlocks_apply₂₁, zero_apply]
    · rw [fromBlocks_apply₂₂]
      exact isTridiagonal_iff_fin.1 hD'.isTridiagonal _ _ (by simp only; omega)
  · -- the `2 × 2` blocks do not overlap
    rw [hDe] at hne ⊢
    rcases finSumFinEquiv_symm_cases (⟨i + 1, by omega⟩ : Fin (s + m)) with ⟨h1, e1⟩ | ⟨h1, e1⟩
    · rcases finSumFinEquiv_symm_cases (⟨i + 2, hi⟩ : Fin (s + m)) with ⟨h2, e2⟩ | ⟨h2, e2⟩
      · simp only at h2
        omega
      · rw [e1, e2, fromBlocks_apply₂₁, zero_apply]
    · rcases finSumFinEquiv_symm_cases (⟨i, by omega⟩ : Fin (s + m)) with ⟨h0, e0⟩ | ⟨h0, e0⟩
      · rw [e1, e0, fromBlocks_apply₂₁, zero_apply] at hne
        exact absurd rfl hne
      · rcases finSumFinEquiv_symm_cases (⟨i + 2, hi⟩ : Fin (s + m)) with ⟨h2, e2⟩ | ⟨h2, e2⟩
        · simp only at h2 h1
          omega
        rw [e1, e0, fromBlocks_apply₂₂] at hne
        rw [e2, e1, fromBlocks_apply₂₂]
        simp only at h0 h1 h2 hne ⊢
        have key := hD'.apply_eq_zero (i - s) (by omega)
        have ea : (⟨i + 1 - s, by omega⟩ : Fin m) = ⟨i - s + 1, by omega⟩ :=
          Fin.ext (by simp; omega)
        have eb : (⟨i + 2 - s, by omega⟩ : Fin m) = ⟨i - s + 2, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [ea] at hne ⊢
        rw [eb]
        exact key hne
  · -- `L` is the identity on the `2 × 2` blocks
    rw [hDe] at hne
    rw [hLe]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;>
      rcases finSumFinEquiv_symm_cases j with ⟨hj, ej⟩ | ⟨hj, ej⟩ <;> rw [ei, ej] at hne ⊢
    · rw [fromBlocks_apply₁₁, one_apply_ne]
      exact fun he => by simp only [Fin.mk.injEq] at he; omega
    · omega
    · rw [fromBlocks_apply₂₁, zero_apply] at hne
      exact absurd rfl hne
    · rw [fromBlocks_apply₂₂] at hne ⊢
      exact h.block _ _ (by simp only; omega) hne
  · -- the product
    have hinvT : (N.toBlocks₁₁⁻¹)ᵀ = N.toBlocks₁₁⁻¹ := by
      rw [transpose_nonsing_inv, hE'.eq]
    have hprod : fromBlocks 1 0 (N.toBlocks₂₁ * N.toBlocks₁₁⁻¹) L' *
        fromBlocks N.toBlocks₁₁ 0 0 D' *
        (fromBlocks 1 0 (N.toBlocks₂₁ * N.toBlocks₁₁⁻¹) L')ᵀ = N := by
      rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
      conv_rhs => rw [← fromBlocks_toBlocks N]
      have h1 : N.toBlocks₁₁ * N.toBlocks₁₁⁻¹ = 1 := mul_nonsing_inv _ hE
      have h2 : N.toBlocks₁₁⁻¹ * N.toBlocks₁₁ = 1 := nonsing_inv_mul _ hE
      have hS := h.mul_eq
      rw [pivotSchur] at hS
      have hS' : L' * (D' * L'ᵀ) =
          N.toBlocks₂₂ - N.toBlocks₂₁ * (N.toBlocks₁₁⁻¹ * N.toBlocks₁₂) := by
        simpa only [Matrix.mul_assoc] using hS
      congr 1 <;> simp only [transpose_one, transpose_zero, transpose_mul, hinvT, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc]
      · rw [← Matrix.mul_assoc N.toBlocks₁₁, h1, Matrix.one_mul, hC]
      · rw [h2, Matrix.mul_one]
      · rw [hS', ← hC, ← Matrix.mul_assoc N.toBlocks₁₁ N.toBlocks₁₁⁻¹, h1, Matrix.one_mul]
        abel
    rw [pivotLower, pivotDiag, reindex_apply, reindex_apply, transpose_submatrix,
      submatrix_mul_equiv, submatrix_mul_equiv, hprod, reindex_apply]

end Bordering

section Existence

variable [Field K]

/-- The Schur complement of a pivot block of a symmetric matrix is symmetric. -/
theorem IsSymm.pivotSchur {s m : ℕ} {N : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) K}
    (hN : N.IsSymm) : (pivotSchur N).IsSymm := by
  have hE' : N.toBlocks₁₁.IsSymm := IsSymm.ext fun i j => hN.apply (Sum.inl i) (Sum.inl j)
  have hB : N.toBlocks₂₂.IsSymm := IsSymm.ext fun i j => hN.apply (Sum.inr i) (Sum.inr j)
  have hC : N.toBlocks₁₂ = N.toBlocks₂₁ᵀ := by
    ext i j
    exact hN.apply (Sum.inr j) (Sum.inl i)
  change (N.toBlocks₂₂ - N.toBlocks₂₁ * N.toBlocks₁₁⁻¹ * N.toBlocks₁₂)ᵀ =
    N.toBlocks₂₂ - N.toBlocks₂₁ * N.toBlocks₁₁⁻¹ * N.toBlocks₁₂
  rw [transpose_sub, transpose_mul, transpose_mul, hB.eq, hC,
    transpose_transpose, transpose_nonsing_inv, hE'.eq, Matrix.mul_assoc]

/-- **One bordering step of the existence proof of the block `L D Lᵀ` factorization**, with a
predicate `P` on the entries of the lower factor carried along: if the leading `s × s` block
(`s ∈ {1, 2}`) of `A.submatrix τ τ` is nonsingular with multipliers `C E⁻¹` satisfying `P`, and
every symmetric matrix of order `m` has a factorization whose lower factor satisfies `P`, so does
`A`. -/
theorem exists_isBlockLDL_step (P : K → Prop) (hP0 : P 0) (hP1 : P 1) {s m : ℕ} (hs : s ≤ 2)
    {A : Matrix (Fin (s + m)) (Fin (s + m)) K} (hA : A.IsSymm) (τ : Equiv.Perm (Fin (s + m)))
    (hE : IsUnit ((A.submatrix τ τ).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁.det)
    (hC : ∀ i j, P ((((A.submatrix τ τ).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ *
      ((A.submatrix τ τ).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁⁻¹) i j))
    (ih : ∀ B : Matrix (Fin m) (Fin m) K, B.IsSymm →
      ∃ (σ : Equiv.Perm (Fin m)) (L D : Matrix (Fin m) (Fin m) K),
        IsBlockLDL (B.submatrix σ σ) L D ∧ ∀ i j, P (L i j)) :
    ∃ (σ : Equiv.Perm (Fin (s + m))) (L D : Matrix (Fin (s + m)) (Fin (s + m)) K),
      IsBlockLDL (A.submatrix σ σ) L D ∧ ∀ i j, P (L i j) := by
  set M := (A.submatrix τ τ).submatrix finSumFinEquiv finSumFinEquiv with hM
  have hMs : M.IsSymm := IsSymm.ext fun i j => hA.apply _ _
  obtain ⟨σ', L', D', h', hL'⟩ := ih (pivotSchur M) hMs.pivotSchur
  set M' := M.submatrix (Sum.map id σ') (Sum.map id σ') with hM'
  have hM's : M'.IsSymm := IsSymm.ext fun i j => hMs.apply _ _
  have hschur : pivotSchur M' = (pivotSchur M).submatrix σ' σ' := by
    ext i j
    rfl
  have hE' : IsUnit M'.toBlocks₁₁.det := hE
  have key := isBlockLDL_pivot hs hM's hE' (hschur ▸ h')
  set ρ : Equiv.Perm (Fin (s + m)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl _) σ').trans finSumFinEquiv) with hρ
  refine ⟨τ * ρ, pivotLower M' L', pivotDiag M' D', ?_, fun i j => ?_⟩
  · have hA' : A.submatrix (τ * ρ) (τ * ρ) = reindex finSumFinEquiv finSumFinEquiv M' := by
      ext i j
      simp [hM', hM, hρ, reindex_apply, Equiv.sumCongr_apply]
    rw [hA']
    exact key
  · change P (fromBlocks 1 0 (M'.toBlocks₂₁ * M'.toBlocks₁₁⁻¹) L'
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b
    · rw [fromBlocks_apply₁₁, one_apply]
      split_ifs
      · exact hP1
      · exact hP0
    · rw [fromBlocks_apply₁₂]
      exact hP0
    · rw [fromBlocks_apply₂₁]
      exact hC (σ' a) b
    · rw [fromBlocks_apply₂₂]
      exact hL' a b

/-- The trivial block `L D Lᵀ` factorization of the zero matrix. -/
theorem isBlockLDL_zero {n : ℕ} : IsBlockLDL (0 : Matrix (Fin n) (Fin n) K) 1 0 where
  isUnitLowerTriangular := isUnitLowerTriangular_one
  isPivotBlockDiagonal :=
    ⟨isSymm_zero, fun _ _ _ => rfl, fun _ _ h => absurd rfl h⟩
  block := fun _ _ _ h => absurd rfl h
  mul_eq := by simp

/-- **The block `L D Lᵀ` factorization exists, with a pivot rule** ([golub2013matrix] §4.4.4):
if every nonzero symmetric matrix admits a nonsingular `1 × 1` or `2 × 2` principal pivot whose
multipliers satisfy `P`, then every symmetric matrix has a symmetric permutation with a block
`L D Lᵀ` factorization whose lower factor satisfies `P` entrywise. Strong induction on the order,
bordering one pivot block at a time (`Matrix.exists_isBlockLDL_step`). -/
theorem exists_perm_isBlockLDL_of_pivot (P : K → Prop) (hP0 : P 0) (hP1 : P 1)
    (hpiv : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) K), A.IsSymm → A ≠ 0 →
      (∃ r : Fin n, A r r ≠ 0 ∧ ∀ i, i ≠ r → P (A i r / A r r)) ∨
      ∃ r t : Fin n, r ≠ t ∧ A r r * A t t - A r t * A t r ≠ 0 ∧ ∀ i, i ≠ r → i ≠ t →
        P ((A i r * A t t - A i t * A t r) / (A r r * A t t - A r t * A t r)) ∧
        P ((A i t * A r r - A i r * A r t) / (A r r * A t t - A r t * A t r))) :
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) K), A.IsSymm →
      ∃ (σ : Equiv.Perm (Fin n)) (L D : Matrix (Fin n) (Fin n) K),
        IsBlockLDL (A.submatrix σ σ) L D ∧ ∀ i j, P (L i j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA
  by_cases hA0 : A = 0
  · refine ⟨1, 1, 0, ?_, fun i j => ?_⟩
    · rw [hA0]
      exact isBlockLDL_zero
    · rw [one_apply]
      split_ifs
      · exact hP1
      · exact hP0
  rcases hpiv A hA hA0 with ⟨r, hr, hrP⟩ | ⟨r, t, hrt, hdet, htP⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by have := r.2; omega⟩
    set τ : Equiv.Perm (Fin (1 + m)) := Equiv.swap ⟨0, by omega⟩ r with hτ
    have hτ0 : τ ⟨0, by omega⟩ = r := Equiv.swap_apply_left _ _
    have hE00 : ((A.submatrix τ τ).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ 0 0 =
        A r r := by
      simp only [toBlocks₁₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left]
      rw [show (Fin.castAdd m (0 : Fin 1)) = ⟨0, by omega⟩ from rfl, hτ0]
    refine exists_isBlockLDL_step P hP0 hP1 (by norm_num) hA τ ?_ (fun i j => ?_)
      (fun B hB => ih m (by omega) B hB)
    · rw [det_unique, show (default : Fin 1) = 0 from rfl, hE00]
      exact isUnit_iff_ne_zero.2 hr
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rw [mul_apply, Fin.sum_univ_one, inv_def, adjugate_fin_one, det_unique,
        show (default : Fin 1) = 0 from rfl, hE00]
      simp only [smul_apply, one_apply_eq, smul_eq_mul, mul_one, Ring.inverse_eq_inv']
      have hx : τ (Fin.natAdd 1 i) ≠ r := by
        rw [← hτ0]
        exact τ.injective.ne (fun h => by simp [Fin.ext_iff] at h)
      have := hrP _ hx
      have hτc : τ (Fin.castAdd m (0 : Fin 1)) = r := hτ0
      simpa [toBlocks₂₁, div_eq_mul_inv, finSumFinEquiv_apply_right, hτc] using this
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by
      have := r.2; have := t.2
      by_contra hcon
      have : n ≤ 1 := by omega
      exact hrt (Fin.ext (by omega))⟩
    set z : Fin (2 + m) := ⟨0, by omega⟩ with hz
    set o : Fin (2 + m) := ⟨1, by omega⟩ with ho
    set u := Equiv.swap z r t with hu
    have hu0 : u ≠ z := fun h => hrt (by
      have := congrArg (Equiv.swap z r) h
      rwa [hu, Equiv.swap_apply_self, Equiv.swap_apply_left, eq_comm] at this)
    have hzo : z ≠ o := by simp [hz, ho, Fin.ext_iff]
    set τ : Equiv.Perm (Fin (2 + m)) := Equiv.swap z r * Equiv.swap o u with hτ
    have hτz : τ z = r := by
      rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzo hu0.symm,
        Equiv.swap_apply_left]
    have hτo : τ o = t := by
      rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hu, Equiv.swap_apply_self]
    set N := (A.submatrix τ τ).submatrix finSumFinEquiv finSumFinEquiv with hN
    have hN00 : N.toBlocks₁₁ 0 0 = A r r := by
      simp only [hN, toBlocks₁₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left]
      rw [show (Fin.castAdd m (0 : Fin 2)) = z from rfl, hτz]
    have hN01 : N.toBlocks₁₁ 0 1 = A r t := by
      simp only [hN, toBlocks₁₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left]
      rw [show (Fin.castAdd m (0 : Fin 2)) = z from rfl, show (Fin.castAdd m (1 : Fin 2)) = o from
        rfl, hτz, hτo]
    have hN10 : N.toBlocks₁₁ 1 0 = A t r := by
      simp only [hN, toBlocks₁₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left]
      rw [show (Fin.castAdd m (0 : Fin 2)) = z from rfl, show (Fin.castAdd m (1 : Fin 2)) = o from
        rfl, hτz, hτo]
    have hN11 : N.toBlocks₁₁ 1 1 = A t t := by
      simp only [hN, toBlocks₁₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left]
      rw [show (Fin.castAdd m (1 : Fin 2)) = o from rfl, hτo]
    have hdetN : N.toBlocks₁₁.det = A r r * A t t - A r t * A t r := by
      rw [det_fin_two, hN00, hN01, hN10, hN11]
    refine exists_isBlockLDL_step P hP0 hP1 le_rfl hA τ ?_ (fun i j => ?_)
      (fun B hB => ih m (by omega) B hB)
    · rw [hdetN]
      exact isUnit_iff_ne_zero.2 hdet
    · have hx1 : τ (Fin.natAdd 2 i) ≠ r := by
        rw [← hτz]
        exact τ.injective.ne (fun h => by simp [hz, Fin.ext_iff] at h)
      have hx2 : τ (Fin.natAdd 2 i) ≠ t := by
        rw [← hτo]
        exact τ.injective.ne (fun h => by simp [ho, Fin.ext_iff] at h; omega)
      have hC0 : N.toBlocks₂₁ i 0 = A (τ (Fin.natAdd 2 i)) r := by
        simp only [hN, toBlocks₂₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right]
        rw [show (Fin.castAdd m (0 : Fin 2)) = z from rfl, hτz]
      have hC1 : N.toBlocks₂₁ i 1 = A (τ (Fin.natAdd 2 i)) t := by
        simp only [hN, toBlocks₂₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right]
        rw [show (Fin.castAdd m (1 : Fin 2)) = o from rfl, hτo]
      obtain ⟨hP0', hP1'⟩ := htP _ hx1 hx2
      change P ((N.toBlocks₂₁ * N.toBlocks₁₁⁻¹) i j)
      rw [mul_apply, Fin.sum_univ_two, inv_def, adjugate_fin_two, hdetN, hC0, hC1]
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, smul_apply, of_apply, cons_val', cons_val_zero,
          cons_val_one, empty_val', cons_val_fin_one, smul_eq_mul, Ring.inverse_eq_inv', hN11, hN10]
        convert hP0' using 1
        field_simp
        ring
      · simp only [Fin.mk_one, Fin.isValue, smul_apply, of_apply, cons_val', cons_val_zero,
          cons_val_one, empty_val', cons_val_fin_one, smul_eq_mul, Ring.inverse_eq_inv', hN01,
          hN00]
        convert hP1' using 1
        field_simp
        ring

/-- **[golub2013matrix] (4.4.2), existence**: every symmetric matrix over a field has a symmetric
permutation `P A Pᵀ = L D Lᵀ` with `L` unit lower triangular and `D` block diagonal with `1 × 1`
and `2 × 2` pivots. Strong induction on the order: a nonzero symmetric matrix has a nonsingular
principal pivot of order one or two (`Matrix.exists_isUnit_principal_pivot`), moved to the front,
and the factorization of the Schur complement is bordered back. The multipliers are not bounded by
`1` in general (the book's `|ℓ_ij| ≤ 1` is false; see `Matrix.exists_perm_isBlockLDL_abs_le` for the
bound of the Bunch–Parlett pivot rule). -/
theorem exists_perm_isBlockLDL {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : A.IsSymm) :
    ∃ (σ : Equiv.Perm (Fin n)) (L D : Matrix (Fin n) (Fin n) K),
      IsBlockLDL (A.submatrix σ σ) L D := by
  obtain ⟨σ, L, D, h, -⟩ := exists_perm_isBlockLDL_of_pivot (fun _ : K => True) trivial trivial
    (fun A hA hA0 => by
      rcases exists_isUnit_principal_pivot hA hA0 with ⟨r, hr⟩ | ⟨r, t, hrt, hdet⟩
      · exact Or.inl ⟨r, hr, fun _ _ => trivial⟩
      · exact Or.inr ⟨r, t, hrt, hdet, fun _ _ _ => ⟨trivial, trivial⟩⟩) A hA
  exact ⟨σ, L, D, h⟩

end Existence

section BunchParlett

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The multiplier bound of the Bunch–Parlett pivot rule** ([golub2013matrix] (4.4.2) and
§4.4.4; [higham2002accuracy] §11.1.1): for `0 < α < 1`, every symmetric `A` has a symmetric
permutation `P A Pᵀ = L D Lᵀ` with `|l_ij| ≤ max (1/α) (1/(1 - α))`. With `μ₀ = max |a_ij|` and
`μ₁ = max |a_ii|`: if `μ₁ ≥ α μ₀` the pivot is the diagonal entry of modulus `μ₁`, with multipliers
at most `μ₀ / μ₁ ≤ 1/α`; otherwise it is the `2 × 2` block around an entry of modulus `μ₀`, whose
determinant exceeds `(1 - α²) μ₀²` in modulus while the numerators of the multipliers are at most
`(1 + α) μ₀²`. The book prints `|ℓ_ij| ≤ 1`, which is false for this rule: at
`α = (1 + √17)/8`, `A = [1 3/2; 3/2 0]` takes a `1 × 1` pivot with multiplier `3/2`. -/
theorem exists_perm_isBlockLDL_abs_le {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : A.IsSymm)
    {α : K} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (σ : Equiv.Perm (Fin n)) (L D : Matrix (Fin n) (Fin n) K),
      IsBlockLDL (A.submatrix σ σ) L D ∧ ∀ i j, |L i j| ≤ max α⁻¹ (1 - α)⁻¹ := by
  set c := max α⁻¹ (1 - α)⁻¹ with hc
  have hα1' : 0 < 1 - α := sub_pos.2 hα1
  have hc1 : α⁻¹ ≤ c := le_max_left _ _
  have hc2 : (1 - α)⁻¹ ≤ c := le_max_right _ _
  have hαinv : 1 ≤ α⁻¹ := (one_le_inv₀ hα0).2 hα1.le
  refine exists_perm_isBlockLDL_of_pivot (fun x => |x| ≤ c) (by simp; linarith)
    (by simp; linarith) (fun {m} B hB hB0 => ?_) A hA
  obtain ⟨i₀, j₀, hij₀⟩ : ∃ i j, B i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hB0 (Matrix.ext hcon)
  obtain ⟨⟨p, q⟩, -, hpq⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m × Fin m))
    (fun x => |B x.1 x.2|) ⟨(i₀, j₀), Finset.mem_univ _⟩
  obtain ⟨r, -, hr⟩ := Finset.exists_max_image Finset.univ (fun i => |B i i|)
    ⟨i₀, Finset.mem_univ _⟩
  have hμ : ∀ i j, |B i j| ≤ |B p q| := fun i j => hpq (i, j) (Finset.mem_univ _)
  have hμd : ∀ i, |B i i| ≤ |B r r| := fun i => hr i (Finset.mem_univ _)
  have hμ₀ : 0 < |B p q| := lt_of_lt_of_le (abs_pos.2 hij₀) (hμ i₀ j₀)
  by_cases h : α * |B p q| ≤ |B r r|
  · have hμ₁ : 0 < |B r r| := lt_of_lt_of_le (mul_pos hα0 hμ₀) h
    refine Or.inl ⟨r, abs_pos.1 hμ₁, fun i _ => ?_⟩
    rw [abs_div, div_le_iff₀ hμ₁]
    calc |B i r| ≤ |B p q| := hμ i r
      _ ≤ α⁻¹ * |B r r| := (le_inv_mul_iff₀ hα0).2 h
      _ ≤ c * |B r r| := mul_le_mul_of_nonneg_right hc1 hμ₁.le
  · push Not at h
    have hpq' : p ≠ q := by
      rintro rfl
      have := hμd p
      nlinarith
    have hsym : B q p = B p q := hB.apply p q
    have hsq : B p q * B q p = |B p q| ^ 2 := by rw [hsym, sq_abs, sq]
    have hdd : |B p p * B q q| ≤ |B r r| ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul (hμd p) (hμd q) (abs_nonneg _) (abs_nonneg _)
    have hμ₁sq : |B r r| ^ 2 < α ^ 2 * |B p q| ^ 2 := by
      rw [← mul_pow]
      exact pow_lt_pow_left₀ h (abs_nonneg _) two_ne_zero
    set det := B p p * B q q - B p q * B q p with hdet
    have hdetlow : (1 - α) * (1 + α) * |B p q| ^ 2 < |det| := by
      have h1 : |B p q| ^ 2 - |B p p * B q q| ≤ |det| := by
        rw [hdet, hsq, abs_sub_comm]
        have := abs_sub_abs_le_abs_sub (|B p q| ^ 2) (B p p * B q q)
        rwa [abs_of_nonneg (sq_nonneg _)] at this
      nlinarith
    have hdetpos : 0 < |det| := lt_of_le_of_lt (by positivity) hdetlow
    have hbound : ∀ a b x y : K, |a| ≤ |B p q| → |b| ≤ |B p q| → |x| ≤ |B r r| →
        |y| ≤ |B p q| → |(a * x - b * y) / det| ≤ c := by
      intro a b x y ha hb hx hy
      rw [abs_div, div_le_iff₀ hdetpos]
      have hnum : |a * x - b * y| ≤ (1 + α) * |B p q| ^ 2 := by
        calc |a * x - b * y| ≤ |a| * |x| + |b| * |y| := by
              rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
          _ ≤ |B p q| * (α * |B p q|) + |B p q| * |B p q| := by
              gcongr
              · exact hx.trans h.le
          _ = (1 + α) * |B p q| ^ 2 := by ring
      calc |a * x - b * y| ≤ (1 + α) * |B p q| ^ 2 := hnum
        _ ≤ (1 - α)⁻¹ * |det| := by
            rw [le_inv_mul_iff₀ hα1']
            nlinarith
        _ ≤ c * |det| := mul_le_mul_of_nonneg_right hc2 hdetpos.le
    refine Or.inr ⟨p, q, hpq', abs_pos.1 hdetpos, fun i _ _ => ⟨?_, ?_⟩⟩
    · exact hbound _ _ _ _ (hμ i p) (hμ i q) (hμd q) (hμ q p)
    · exact hbound _ _ _ _ (hμ i q) (hμ i p) (hμd p) (hμ p q)

end BunchParlett

/-! ### Existence of the Aasen factorization -/

section Aasen

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The Gauss transform `I - l e₀ᵀ` of Aasen's method, and its inverse `I + l e₀ᵀ` when
`l 0 = 0`. -/
private theorem one_add_mul_one_sub {m : ℕ} {l : Fin (m + 1) → K} (hl : l 0 = 0) :
    (1 + vecMulVec l (Pi.single (0 : Fin (m + 1)) (1 : K))) *
      (1 - vecMulVec l (Pi.single (0 : Fin (m + 1)) (1 : K))) = 1 := by
  have hsq : vecMulVec l (Pi.single (0 : Fin (m + 1)) (1 : K)) *
      vecMulVec l (Pi.single (0 : Fin (m + 1)) (1 : K)) = 0 := by
    rw [vecMulVec_mul_vecMulVec, single_dotProduct, one_mul, hl, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  rw [add_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hsq, sub_zero, sub_add_cancel]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `I + l e₀ᵀ` is unit lower triangular when `l 0 = 0`. -/
private theorem isUnitLowerTriangular_one_add {m : ℕ} {l : Fin (m + 1) → K} (hl : l 0 = 0) :
    (1 + vecMulVec l (Pi.single (0 : Fin (m + 1)) (1 : K))).IsUnitLowerTriangular := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    have hj : j ≠ 0 := fun h => by rw [h] at hij'; exact absurd hij' (Fin.not_lt_zero _)
    simp [vecMulVec_apply, hj, hij'.ne]
  · by_cases hi : i = 0
    · subst hi
      simp [vecMulVec_apply, hl]
    · simp [vecMulVec_apply, hi]

/-- **[golub2013matrix] (4.4.1), existence with the pivoting bound**, in the strong form used by the
induction: every symmetric matrix over a linearly ordered field has a symmetric permutation fixing
the first index with an Aasen factorization `P A Pᵀ = L T Lᵀ`, `|l_ij| ≤ 1`. -/
theorem exists_perm_isAasen_aux :
    ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) K}, A.IsSymm →
      ∃ (σ : Equiv.Perm (Fin n)) (L T : Matrix (Fin n) (Fin n) K),
        IsAasen (A.submatrix σ σ) L T ∧ (∀ i j, |L i j| ≤ 1) ∧
          ∀ h : 0 < n, σ ⟨0, h⟩ = ⟨0, h⟩
  | 0, A, hA => ⟨1, 1, A, ⟨isUnitLowerTriangular_one, fun _ h => absurd h (lt_irrefl 0), hA,
      fun i => i.elim0, Subsingleton.elim _ _⟩, fun i => i.elim0, fun h => absurd h (lt_irrefl 0)⟩
  | 1, A, hA => by
    refine ⟨1, 1, A, ⟨isUnitLowerTriangular_one, fun i h hi => absurd (Subsingleton.elim _ _) hi,
      hA, isTridiagonal_iff_fin.2 fun i j hij => ?_, by simp⟩, fun i j => ?_, fun _ => rfl⟩
    · omega
    · rw [one_apply]
      split_ifs <;> simp
  | m + 2, A, hA => by
    -- the first row and column, and the trailing block
    set c : Fin (m + 1) → K := fun i => A i.succ 0 with hc
    set B : Matrix (Fin (m + 1)) (Fin (m + 1)) K := fun i j => A i.succ j.succ with hBd
    obtain ⟨q, -, hq⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|)
      Finset.univ_nonempty
    set π : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 q with hπ
    set c₀ := c q with hc₀
    set l : Fin (m + 1) → K := fun i => if i = 0 then 0 else c (π i) / c₀ with hl
    have hl0 : l 0 = 0 := by simp [hl]
    have hlabs : ∀ i, |l i| ≤ 1 := fun i => by
      simp only [hl]
      split_ifs
      · simp
      · rw [abs_div]
        rcases eq_or_ne c₀ 0 with h0 | h0
        · simp [h0]
        · rw [div_le_one (abs_pos.2 h0)]
          exact hq _ (Finset.mem_univ _)
    set M := 1 - vecMulVec l (Pi.single (0 : Fin (m + 1)) (1 : K)) with hM
    set A' := M * B.submatrix π π * Mᵀ with hA'
    have hBs : B.IsSymm := IsSymm.ext fun i j => hA.apply _ _
    have hA's : A'.IsSymm := by
      rw [IsSymm, hA', transpose_mul, transpose_mul, transpose_transpose, transpose_submatrix,
        hBs.eq, Matrix.mul_assoc]
    obtain ⟨σ', L', T', h', hL', hσ'0⟩ := exists_perm_isAasen_aux hA's
    have hσ0 : σ' 0 = 0 := hσ'0 (Nat.succ_pos m)
    set l' : Fin (m + 1) → K := fun i => l (σ' i) with hl'
    have hl'0 : l' 0 = 0 := by simp [hl', hσ0, hl0]
    set Minv := 1 + vecMulVec l' (Pi.single (0 : Fin (m + 1)) (1 : K)) with hMinv
    set N := Minv * L' with hN
    set ρ : Equiv.Perm (Fin (m + 1)) := π * σ' with hρ
    -- the Gauss transform commutes with `σ'`
    have hMσ : M.submatrix σ' σ' = 1 - vecMulVec l' (Pi.single (0 : Fin (m + 1)) (1 : K)) := by
      ext i j
      have hj : σ' j = 0 ↔ j = 0 := σ'.injective.eq_iff' hσ0
      simp [hM, hl', vecMulVec_apply, Pi.single_apply, one_apply, σ'.injective.eq_iff, hj]
    have hkey : N * T' * Nᵀ = B.submatrix ρ ρ := by
      have h1 : A'.submatrix σ' σ' =
          (1 - vecMulVec l' (Pi.single (0 : Fin (m + 1)) (1 : K))) * B.submatrix ρ ρ *
          (1 - vecMulVec l' (Pi.single (0 : Fin (m + 1)) (1 : K)))ᵀ := by
        rw [hA', ← hMσ, ← submatrix_mul_equiv _ _ _ σ' _, ← submatrix_mul_equiv _ _ _ σ' _,
          transpose_submatrix, submatrix_submatrix]
        rfl
      have h2 := one_add_mul_one_sub hl'0
      calc N * T' * Nᵀ = Minv * (L' * T' * L'ᵀ) * Minvᵀ := by
            rw [hN, transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = (Minv * (1 - vecMulVec l' (Pi.single (0 : Fin (m + 1)) (1 : K)))) * B.submatrix ρ ρ *
            (Minv * (1 - vecMulVec l' (Pi.single (0 : Fin (m + 1)) (1 : K))))ᵀ := by
            rw [h'.mul_eq, h1, transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = B.submatrix ρ ρ := by rw [h2, transpose_one, Matrix.one_mul, Matrix.mul_one]
    -- the first column of `L'` and the entries of `N`
    have hL'col : ∀ k, L' k 0 = if k = 0 then 1 else 0 := fun k => by
      split_ifs with hk
      · rw [hk]
        exact h'.isUnitLowerTriangular.diag_eq_one 0
      · exact h'.col_zero k (Nat.succ_pos m) hk
    have hMinv : ∀ i k, Minv i k = (if i = k then 1 else 0) + if k = 0 then l' i else 0 := by
      intro i k
      simp [hMinv, vecMulVec_apply, Pi.single_apply, one_apply]
    have hN0 : ∀ i, N i 0 = if i = 0 then 1 else l' i := fun i => by
      rw [hN, mul_apply, Finset.sum_eq_single 0
        (fun k _ hk => by rw [hL'col, ite_eq_right hk, mul_zero]) (by simp), hL'col,
        ite_eq_left rfl, mul_one, hMinv]
      by_cases hi : i = 0
      · simp [hi, hl'0]
      · simp [hi]
    have hNj : ∀ i j, j ≠ 0 → N i j = L' i j := fun i j hj => by
      have hL'0 : L' 0 j = 0 := h'.isUnitLowerTriangular.isLowerTriangular
        (OrderDual.toDual_lt_toDual.2 (Fin.pos_iff_ne_zero.2 hj))
      rw [hN, mul_apply]
      simp only [hMinv, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_ite_eq', hL'0, mul_zero, add_zero]
    have hcρ : ∀ i, c (ρ i) = c₀ * N i 0 := fun i => by
      rw [hN0]
      by_cases hi : i = 0
      · simp [hi, hρ, hσ0, hπ, hc₀]
      · have hσi : σ' i ≠ 0 := fun h => hi (by rw [← hσ0] at h; exact σ'.injective h)
        simp only [hi, ite_false, hl', hl, hσi]
        rcases eq_or_ne c₀ 0 with h0 | h0
        · have := hq (π (σ' i)) (Finset.mem_univ _)
          rw [h0, abs_zero, abs_nonpos_iff] at this
          rw [h0, zero_mul]
          exact this
        · rw [mul_div_left_comm, div_self h0, mul_one]
          rfl
    -- the factors
    set σ : Equiv.Perm (Fin (m + 2)) := Equiv.Perm.decomposeFin.symm (0, ρ) with hσd
    have hσ0' : σ 0 = 0 := Equiv.Perm.decomposeFin_symm_apply_zero _ _
    have hσs : ∀ x, σ x.succ = (ρ x).succ := fun x => by
      rw [hσd, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    set L : Matrix (Fin (m + 2)) (Fin (m + 2)) K := of fun i j =>
      Fin.cases (motive := fun _ => K) (Fin.cases (motive := fun _ => K) 1 (fun _ => 0) j)
        (fun i' => Fin.cases (motive := fun _ => K) 0 (fun j' => N i' j') j) i with hLd
    set T : Matrix (Fin (m + 2)) (Fin (m + 2)) K := of fun i j =>
      Fin.cases (motive := fun _ => K)
        (Fin.cases (motive := fun _ => K) (A 0 0) (fun j' => if j' = 0 then c₀ else 0) j)
        (fun i' => Fin.cases (motive := fun _ => K) (if i' = 0 then c₀ else 0)
          (fun j' => T' i' j') j) i with hTd
    have hNu : N.IsUnitLowerTriangular :=
      (isUnitLowerTriangular_one_add hl'0).mul h'.isUnitLowerTriangular
    refine ⟨σ, L, T, ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i h hi => ?_, ?_, ?_, ?_⟩,
      fun i j => ?_, fun _ => hσ0'⟩
    · -- `L` is lower triangular
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij' (lt_irrefl _)
        | succ j' => simp [hLd]
      | succ i' =>
        induction j using Fin.cases with
        | zero => exact absurd hij' (not_lt.2 (Fin.zero_le _))
        | succ j' =>
          simp only [hLd, of_apply, Fin.cases_succ]
          exact hNu.isLowerTriangular (OrderDual.toDual_lt_toDual.2 (Fin.succ_lt_succ_iff.1 hij'))
    · induction i using Fin.cases with
      | zero => simp [hLd]
      | succ i' => simp [hLd, hNu.diag_eq_one]
    · -- the first column of `L` is `e₁`
      have e0 : (⟨0, h⟩ : Fin (m + 2)) = 0 := rfl
      rw [e0] at hi ⊢
      induction i using Fin.cases with
      | zero => exact absurd rfl hi
      | succ i' => simp [hLd]
    · -- `T` is symmetric
      refine IsSymm.ext fun i j => ?_
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j' => simp [hTd]
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [hTd]
        | succ j' => simp [hTd, h'.isSymm.apply]
    · -- `T` is tridiagonal
      refine isTridiagonal_iff_fin.2 fun i j hij => ?_
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          have hj' : j' ≠ 0 := fun h => by subst h; simp at hij
          simp [hTd, hj']
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          have hi' : i' ≠ 0 := fun h => by subst h; simp at hij
          simp [hTd, hi']
        | succ j' =>
          simp only [hTd, of_apply, Fin.cases_succ]
          exact isTridiagonal_iff_fin.1 h'.isTridiagonal _ _ (by simpa using hij)
    · -- the product
      ext i j
      rw [submatrix_apply]
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero =>
          rw [hσ0']
          simp [mul_apply, Fin.sum_univ_succ, hLd, hTd]
        | succ j' =>
          rw [hσ0', hσs, hA.apply (ρ j').succ 0]
          change _ = c (ρ j')
          rw [hcρ]
          simp only [mul_apply, transpose_apply, Fin.sum_univ_succ, hLd, hTd, of_apply,
            Fin.cases_zero, Fin.cases_succ, Fin.succ_ne_zero, ite_true,
            ite_false, zero_mul, mul_zero, one_mul, Finset.sum_const_zero, add_zero,
            zero_add]
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          rw [hσ0', hσs]
          change _ = c (ρ i')
          rw [hcρ]
          simp only [mul_apply, transpose_apply, Fin.sum_univ_succ, hLd, hTd, of_apply,
            Fin.cases_zero, Fin.cases_succ, Fin.succ_ne_zero, ite_true,
            ite_false, zero_mul, mul_zero, mul_one, Finset.sum_const_zero, add_zero,
            zero_add]
          ring
        | succ j' =>
          rw [hσs, hσs]
          change _ = B (ρ i') (ρ j')
          rw [show B (ρ i') (ρ j') = (N * T' * Nᵀ) i' j' from
            (congrFun (congrFun hkey i') j').symm]
          simp only [mul_apply, transpose_apply, Fin.sum_univ_succ, hLd, hTd, of_apply,
            Fin.cases_zero, Fin.cases_succ, Fin.succ_ne_zero, ite_true,
            ite_false, zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
            zero_add]
    · -- the bound on the multipliers
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp [hLd]
        | succ j' => simp [hLd]
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [hLd]
        | succ j' =>
          simp only [hLd, of_apply, Fin.cases_succ]
          by_cases hj' : j' = 0
          · rw [hj', hN0]
            split_ifs
            · simp
            · exact hlabs _
          · rw [hNj _ _ hj']
            exact hL' i' j'

/-- **[golub2013matrix] (4.4.1), existence with the pivoting bound**: every symmetric matrix over a
linearly ordered field has a symmetric permutation `P A Pᵀ = L T Lᵀ` with `L` unit lower
triangular of first column `e₁`, `T` symmetric tridiagonal and `|l_ij| ≤ 1`. The Parlett–Reid
process (§4.4.1): the largest entry of the first column below the diagonal is moved up by a
permutation fixing the first index, the Gauss transform `I - l e₂ᵀ` with `|l_i| ≤ 1` annihilates
the rest of the column, and the trailing block is factored recursively. -/
theorem exists_perm_isAasen {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : A.IsSymm) :
    ∃ (σ : Equiv.Perm (Fin n)) (L T : Matrix (Fin n) (Fin n) K),
      IsAasen (A.submatrix σ σ) L T ∧ ∀ i j, |L i j| ≤ 1 := by
  obtain ⟨σ, L, T, h, hL, -⟩ := exists_perm_isAasen_aux hA
  exact ⟨σ, L, T, h, hL⟩

end Aasen

end Matrix
