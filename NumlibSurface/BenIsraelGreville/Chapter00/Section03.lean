/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

/-!
# Elementary operations and permutations

Section 0.3 of [benIsrael2003generalized] represents elementary operations
by matrix multiplication, and permutations by matrices of Kronecker deltas.

## Deviations from the source

* **Section 0.3.2** (composition order). With the entries $P_\pi(i,j)=\delta_{\pi(i),j}$
  and ordinary function composition, $P_\pi P_\sigma=P_{\sigma\circ\pi}$.
* **Exercise 49** (distinct indices). The inverse law for adding a multiple of one
  row to another uses distinct row indices.
-/

namespace BenIsraelGreville.Chapter00

open Matrix Equiv

variable {K m n : Type*} [Field K] [DecidableEq n]

/-- **Operation (1)** of [benIsrael2003generalized], Chapter 0, §3.1. Scale row $i$
of the identity matrix by $a$. -/
abbrev scaleRowMatrix (i : n) (a : K) : Matrix n n K :=
  Matrix.rowScale i a

/-- **Operation (2)** of [benIsrael2003generalized], Chapter 0, §3.1. Add $b$
times row $j$ of the identity matrix to row $i$. -/
abbrev addRowMatrix (i j : n) (b : K) : Matrix n n K :=
  Matrix.transvection i j b

/-- **Operation (3)** of [benIsrael2003generalized], Chapter 0, §3.1. Swap rows
$i$ and $j$ of the identity matrix. -/
abbrev swapRowMatrix (i j : n) : Matrix n n K :=
  Matrix.swap K i j

private theorem transvection_mul_eq_updateRow [Fintype n] (A : Matrix n m K)
    (i j : n) (b : K) :
    addRowMatrix i j b * A = A.updateRow i (A.row i + b • A.row j) := by
  ext k l
  by_cases hk : k = i
  · subst k
    simp [Matrix.row]
  · rw [Matrix.transvection_mul_apply_of_ne i j k l hk, Matrix.updateRow_ne hk]

/-- **Section 0.3.1** of [benIsrael2003generalized]. Multiplication on the left
by each elementary matrix performs the corresponding row operation. -/
theorem elementaryRowMatrices_mul [Fintype n] (A : Matrix n m K)
    (i j : n) (a b : K) :
    scaleRowMatrix i a * A = A.updateRow i (a • A.row i) ∧
    addRowMatrix i j b * A = A.updateRow i (A.row i + b • A.row j) ∧
    swapRowMatrix i j * A = A.submatrix (Equiv.swap i j) id :=
  ⟨Matrix.rowScale_mul i a A, transvection_mul_eq_updateRow A i j b,
    PEquiv.toMatrix_toPEquiv_mul _ _⟩

/-- **Section 0.3.1** of [benIsrael2003generalized]. Multiplication on the right
performs the corresponding column operation. Adding a multiple of column $j$
to column $i$ uses the transpose of the corresponding row operation matrix. -/
theorem elementaryColumnMatrices_mul [Fintype n] (A : Matrix m n K)
    (i j : n) (a b : K) :
    A * scaleRowMatrix i a = A.updateCol i (a • A.col i) ∧
    A * addRowMatrix j i b = A.updateCol i (A.col i + b • A.col j) ∧
    A * swapRowMatrix i j = A.submatrix id (Equiv.swap i j) := by
  refine ⟨Matrix.mul_rowScale i a A, ?_, ?_⟩
  · ext k l
    by_cases hl : l = i
    · subst l
      simp [Matrix.col]
    · rw [Matrix.mul_transvection_apply_of_ne j i k l hl, Matrix.updateCol_ne hl]
  · simpa [swapRowMatrix, Matrix.swap] using
      (PEquiv.mul_toMatrix_toPEquiv A (Equiv.swap i j))

/-- **Section 0.3.2** of [benIsrael2003generalized]. The permutation matrix for
$\pi$ has entry $1$ exactly where $\pi(i)=j$. -/
abbrev permutationMatrix (π : Equiv.Perm n) : Matrix n n K :=
  π.permMatrix K

/-- The permutation matrix determines the permutation. -/
theorem permutationMatrix_injective :
    Function.Injective (permutationMatrix (K := K) (n := n)) := by
  intro π σ h
  ext i
  have hi := congrArg (fun M : Matrix n n K => M i (π i)) h
  have he : σ i = π i := by
    simpa [permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Pi.single_apply] using hi
  exact he.symm

/-- Permutation matrices reverse the order of composition for the book's
entry convention. -/
theorem permutationMatrix_mul [Fintype n] (π σ : Equiv.Perm n) :
    permutationMatrix (K := K) π * permutationMatrix σ = permutationMatrix (σ * π) :=
  (Matrix.permMatrix_mul σ π).symm

/-- Left multiplication by the permutation matrix applies $\pi$ to row
indices. Right multiplication applies $\pi^{-1}$ to column indices. -/
theorem permutationMatrix_mul_eq_submatrix [Fintype n] (π : Equiv.Perm n)
    (A : Matrix n m K) (B : Matrix m n K) :
    permutationMatrix π * A = A.submatrix π id ∧
    B * permutationMatrix π = B.submatrix id π.symm :=
  ⟨PEquiv.toMatrix_toPEquiv_mul _ _, PEquiv.mul_toMatrix_toPEquiv _ _⟩

/-- Every permutation of a finite index set is a product of transpositions. -/
theorem perm_exists_list_swaps [Finite n] (π : Equiv.Perm n) :
    ∃ l : List (Equiv.Perm n), l.prod = π ∧ ∀ σ ∈ l, Equiv.Perm.IsSwap σ := by
  let _ := Fintype.ofFinite n
  obtain ⟨l, hl⟩ := (Equiv.Perm.truncSwapFactors π).out
  exact ⟨l, hl⟩

/-- The sign of a product of transpositions is minus one raised to their number. -/
theorem sign_eq_neg_one_pow_length_swaps [Fintype n] (l : List (Equiv.Perm n))
    (hl : ∀ σ ∈ l, Equiv.Perm.IsSwap σ) :
    l.prod.sign = (-1) ^ l.length :=
  Equiv.Perm.sign_prod_list_swap hl

/-- **Exercise 49(a)** of [benIsrael2003generalized], Chapter 0. The inverses of
elementary row operations use reciprocal scaling, a negated row multiple,
and the same swap, respectively. -/
theorem exercise_49_a [Fintype n] (i j : n) (hij : i ≠ j) (a b : K) (ha : a ≠ 0) :
    (IsUnit (scaleRowMatrix i a) ∧ (scaleRowMatrix i a)⁻¹ = scaleRowMatrix i a⁻¹) ∧
    (IsUnit (addRowMatrix i j b) ∧ (addRowMatrix i j b)⁻¹ = addRowMatrix i j (-b)) ∧
    (IsUnit (swapRowMatrix (K := K) i j) ∧
      (swapRowMatrix (K := K) i j)⁻¹ = swapRowMatrix i j) := by
  have h₁ : scaleRowMatrix i a⁻¹ * scaleRowMatrix i a = 1 := by
    rw [Matrix.rowScale_mul_rowScale, inv_mul_cancel₀ ha, Matrix.rowScale_one]
  have h₂ : addRowMatrix i j (-b) * addRowMatrix i j b = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel, Matrix.transvection_zero]
  have h₃ : swapRowMatrix (K := K) i j * swapRowMatrix i j = 1 := Matrix.swap_mul_self i j
  exact ⟨⟨isUnit_iff_exists_inv'.mpr ⟨_, h₁⟩, Matrix.inv_eq_left_inv h₁⟩,
    ⟨isUnit_iff_exists_inv'.mpr ⟨_, h₂⟩, Matrix.inv_eq_left_inv h₂⟩,
    ⟨isUnit_iff_exists_inv'.mpr ⟨_, h₃⟩, Matrix.inv_eq_left_inv h₃⟩⟩

private theorem addRowMatrix_mulVec_apply [Fintype n] (i j : n) (b : K)
    (x : n → K) (k : n) :
    (addRowMatrix i j b *ᵥ x) k = x k + if k = i then b * x j else 0 := by
  simp [addRowMatrix, Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec,
    Function.update_apply]

/-- **Exercise 49(b)** of [benIsrael2003generalized], Chapter 0. A row swap
is a product of three row additions and a scaling by $-1$. -/
theorem exercise_49_b [Fintype n] (i j : n) (hij : i ≠ j) :
    swapRowMatrix (K := K) i j =
      scaleRowMatrix i (-1 : K) * addRowMatrix j i 1 *
        addRowMatrix i j (-1) * addRowMatrix j i 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  simp only [swapRowMatrix, Matrix.swap_mulVec, ← Matrix.mulVec_mulVec]
  funext k
  rw [scaleRowMatrix, Matrix.rowScale, Matrix.mulVec_diagonal]
  simp only [addRowMatrix_mulVec_apply, Function.comp_apply]
  rcases eq_or_ne k i with rfl | hki
  · simp [hij]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [hij, hij.symm]
    · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- An elementary row scaling or addition, corresponding to types 1 and 2
in Section 0.3.1. -/
def IsScaleOrAddRowMatrix (E : Matrix n n K) : Prop :=
  (∃ (i : n) (a : K), a ≠ 0 ∧ E = scaleRowMatrix i a) ∨
    ∃ (i j : n) (b : K), i ≠ j ∧ E = addRowMatrix i j b

/-- **Exercise 49(c)** of [benIsrael2003generalized], Chapter 0. Every permutation
matrix is a product of elementary row scalings and additions. -/
theorem exercise_49_c [Fintype n] (π : Equiv.Perm n) :
    ∃ l : List (Matrix n n K), l.prod = permutationMatrix π ∧
      ∀ E ∈ l, IsScaleOrAddRowMatrix E := by
  let S : Set (Matrix n n K) := {E | IsScaleOrAddRowMatrix E}
  have h : permutationMatrix π ∈ Submonoid.closure S := by
    induction π using Equiv.Perm.swap_induction_on with
    | one => rw [permutationMatrix, Matrix.permMatrix_one]; exact (Submonoid.closure S).one_mem
    | swap_mul π i j hij ih =>
      rw [← permutationMatrix_mul]
      refine (Submonoid.closure S).mul_mem ih ?_
      change swapRowMatrix i j ∈ Submonoid.closure S
      rw [exercise_49_b i j hij]
      apply (Submonoid.closure S).mul_mem
      · apply (Submonoid.closure S).mul_mem
        · apply (Submonoid.closure S).mul_mem
          · exact Submonoid.subset_closure (Or.inl ⟨i, -1, neg_ne_zero.mpr one_ne_zero, rfl⟩)
          · exact Submonoid.subset_closure (Or.inr ⟨j, i, 1, hij.symm, rfl⟩)
        · exact Submonoid.subset_closure (Or.inr ⟨i, j, -1, hij, rfl⟩)
      · exact Submonoid.subset_closure (Or.inr ⟨j, i, 1, hij.symm, rfl⟩)
  obtain ⟨l, hmem, hl⟩ := Submonoid.exists_list_of_mem_closure h
  exact ⟨l, hl, hmem⟩

/-- A diagonal matrix is built by successively scaling the untouched rows of
the identity matrix. -/
theorem diagonal_insert_eq_scale_mul [Fintype n] (D : n → K) (s : Finset n) (i : n)
    (hi : i ∉ s) :
    diagonal (fun j => if j ∈ insert i s then D j else 1) =
      scaleRowMatrix i (D i) * diagonal (fun j => if j ∈ s then D j else 1) := by
  classical
  rw [scaleRowMatrix, Matrix.rowScale, diagonal_mul_diagonal]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp [hi]
  · simp [hj]

/-- Every nonsingular matrix is a product of elementary row scalings and additions. -/
theorem exists_list_scaleOrAdd_of_isUnit [Fintype n] (E : Matrix n n K) (hE : IsUnit E) :
    ∃ l : List (Matrix n n K), l.prod = E ∧ ∀ T ∈ l, IsScaleOrAddRowMatrix T := by
  let S : Set (Matrix n n K) := {T | IsScaleOrAddRowMatrix T}
  let M := Submonoid.closure S
  have h : E ∈ M := by
    apply diagonal_transvection_induction_of_det_ne_zero (fun T => T ∈ M) E
      ((isUnit_iff_isUnit_det E).mp hE).ne_zero
    · intro D hD
      rw [det_diagonal, Finset.prod_ne_zero_iff] at hD
      have hMem (s : Finset n) : diagonal (fun j => if j ∈ s then D j else 1) ∈ M := by
        induction s using Finset.induction_on with
        | empty => simpa only [Finset.notMem_empty, ite_false, diagonal_one] using M.one_mem
        | insert i s hi ih =>
            rw [diagonal_insert_eq_scale_mul D s i hi]
            have hScale : scaleRowMatrix i (D i) ∈ S :=
              Or.inl ⟨i, D i, hD i (Finset.mem_univ _), rfl⟩
            exact M.mul_mem (Submonoid.subset_closure hScale) ih
      simpa only [Finset.mem_univ, ite_true] using hMem Finset.univ
    · intro t
      exact Submonoid.subset_closure (Or.inr ⟨t.i, t.j, t.c, t.hij, rfl⟩)
    · intro T U _ _ hT hU
      exact M.mul_mem hT hU
  obtain ⟨l, hmem, hl⟩ := Submonoid.exists_list_of_mem_closure h
  exact ⟨l, hl, hmem⟩

private theorem insertLast_bijective {d : ℕ} (i : Fin (d + 1)) (σ : Equiv.Perm (Fin d)) :
    Function.Bijective (Fin.insertNth i (Fin.last d) fun j => (σ j).castSucc) := by
  apply Finite.injective_iff_bijective.mp
  intro x y h
  have hc (a : Fin (d + 1)) : a = i ∨ ∃ j, i.succAbove j = a :=
    (eq_or_ne a i).imp_right Fin.exists_succAbove_eq
  rcases hc x with rfl | ⟨j, rfl⟩ <;> rcases hc y with rfl | ⟨k, rfl⟩
  · rfl
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at h
    exact (Fin.castSucc_ne_last _ h.symm).elim
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at h
    exact (Fin.castSucc_ne_last _ h).elim
  · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at h
    exact congrArg i.succAbove (σ.injective (Fin.castSucc_injective _ h))

/-- Insert the largest value into position $i$ of the displayed permutation,
retaining the order of all its other values. -/
noncomputable def insertLastPermutation {d : ℕ} (i : Fin (d + 1)) (σ : Equiv.Perm (Fin d)) :
    Equiv.Perm (Fin (d + 1)) :=
  Equiv.ofBijective (Fin.insertNth i (Fin.last d) fun j => (σ j).castSucc)
    (insertLast_bijective i σ)

/-- **Exercise 50** of [benIsrael2003generalized], Chapter 0. Choosing a permutation
of the first $d$ values and a gap in its display enumerates the permutations of
$d+1$ values exactly once. -/
noncomputable def exercise_50 (d : ℕ) :
    (Fin (d + 1) × Equiv.Perm (Fin d)) ≃ Equiv.Perm (Fin (d + 1)) :=
  Equiv.ofBijective (fun (p : Fin (d + 1) × Equiv.Perm (Fin d)) =>
    insertLastPermutation p.1 p.2) (by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · rintro ⟨i, σ⟩ ⟨k, τ⟩ h
      have hi : insertLastPermutation i σ i = Fin.last d := by simp [insertLastPermutation]
      have hk : insertLastPermutation k τ k = Fin.last d := by simp [insertLastPermutation]
      have he := congrArg (fun p : Equiv.Perm _ => p i) h
      have hik : i = k :=
        (insertLastPermutation k τ).injective (he.symm.trans (hi.trans hk.symm))
      subst k
      have hστ : σ = τ := by
        ext j : 1
        have he := congrArg (fun p : Equiv.Perm _ => p (i.succAbove j)) h
        simpa [insertLastPermutation] using he
      exact Prod.ext rfl hστ
    · rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin,
        Nat.factorial_succ])

/-- The insertion equivalence places the largest value in the chosen gap and
shifts the remaining entries past that gap. -/
theorem exercise_50_apply (d : ℕ) (i : Fin (d + 1)) (σ : Equiv.Perm (Fin d)) :
    exercise_50 d (i, σ) i = Fin.last d ∧
      ∀ j : Fin d, exercise_50 d (i, σ) (i.succAbove j) = (σ j).castSucc :=
  by simp [exercise_50, insertLastPermutation]

end BenIsraelGreville.Chapter00
