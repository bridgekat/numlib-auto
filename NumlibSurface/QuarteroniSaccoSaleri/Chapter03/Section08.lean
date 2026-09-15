import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.SchurComplement
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section07

/-!
# Quarteroni–Sacco–Saleri §3.8: block systems

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.8, over the backbone `Numlib/LinearAlgebra/Matrix/SchurComplement`
(the Schur complement `Matrix.schurComplement` and the block LDU factorization
`Matrix.fromBlocks_eq_mul_fromBlocks_of_mul_eq`), `Numlib/LinearAlgebra/Matrix/LU` (the block LU
specification `Matrix.IsBlockLU` along a labelling and its existence and uniqueness theorem
`Matrix.existsUnique_isBlockLU_iff`) and
`Numlib/LinearAlgebra/Matrix/NonsingularInverse` (the Sherman–Morrison–Woodbury formula).

## Conventions

A `2 × 2` partition of a matrix is `Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂` on `Fin r ⊕ Fin s`, as in
§3.9; the Schur complement `Δ₂ = A₂₂ - A₂₁ A₁₁⁻¹ A₁₂` of the leading block is
`Matrix.schurComplement`. A partition into `m × m` blocks is a *labelling*
`b : Fin N → Fin m`, the block `(k, l)` of a matrix `X` being `X.toBlock (b · = k) (b · = l)`;
the book's contiguous blocks of sizes `n₁, …, n_m` are a monotone `b`, but nothing below needs
monotonicity. `Matrix.IsBlockLU b A L U` is the book's block LU factorization: `L` is block lower
triangular with identity diagonal blocks ("`L` having unit diagonal entries"), `U` is block upper
triangular, and `L U = A`. The `m - 1` "dominant principal block minors" are the leading block
submatrices `A(b < k)` for the labels `k` attained by `b`: the one for the smallest label is
empty and the one for the largest is `A` without its last block row and column.

## Contents

* `blockLDU` — §3.8.1, the block LDU factorization with a factored leading block.
* `theorem_3_7` — the existence and uniqueness of the block LU factorization.
* `equation_3_57` — the Sherman–Morrison–Woodbury formula of §3.8.2.
* `blockTridiagonal_isBlockBidiagonal`, `blockTridiagonal_lu` — §3.8.3, the block Thomas
  recurrences `U₁ = A₁₁`, `L_{i-1} U_{i-1} = A_{i,i-1}`, `U_i = A_{ii} - L_{i-1} A_{i-1,i}`.

The storage counts, the block Cholesky–Thomas reduction of a symmetric positive definite block
tridiagonal system and the `(7/6)(n - 1) p³` flop count are prose.

## Readings

§3.8.3 posits the shape of the factors (`L` block unit lower bidiagonal, `U` block upper
bidiagonal with the superdiagonal blocks of `A`) and reads off the recurrence by equating blocks.
Here the shape is *proved*: `blockTridiagonal_isBlockBidiagonal` is the block form of Property
3.4 — the lower clause under the hypothesis of Theorem 3.7, as in §3.7 — and `blockTridiagonal_lu`
then states the three recurrences for any block LU factorization of a block tridiagonal matrix.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

/-! ### §3.8.1: block LU factorization -/

section BlockLDU

variable {r s : ℕ}

/-- **§3.8.1, the block LDU factorization.** Let `A = [[A₁₁, A₁₂], [A₂₁, A₂₂]]` with
`A₁₁ ∈ ℝ^{r×r}` nonsingular and with a known factorization `A₁₁ = L₁₁ D₁ R₁₁` into nonsingular
factors. Then

`[[A₁₁, A₁₂], [A₂₁, A₂₂]] = [[L₁₁, 0], [L₂₁, I]] [[D₁, 0], [0, Δ₂]] [[R₁₁, R₁₂], [0, I]]`,

where `L₂₁ = A₂₁ R₁₁⁻¹ D₁⁻¹`, `R₁₂ = D₁⁻¹ L₁₁⁻¹ A₁₂` and `Δ₂ = A₂₂ - L₂₁ D₁ R₁₂` is the Schur
complement of `A₁₁` (backbone `Matrix.fromBlocks_eq_mul_fromBlocks_of_mul_eq`,
`Matrix.schurComplement_fromBlocks_of_mul_eq`). Repeating the reduction on `Δ₂` gives the block
version of the LU factorization; when `A₁₁` is a scalar it is one step of Gaussian elimination. -/
theorem blockLDU {A₁₁ L₁₁ D₁ R₁₁ : Matrix (Fin r) (Fin r) ℝ} {A₁₂ R₁₂ : Matrix (Fin r) (Fin s) ℝ}
    {A₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ} {A₂₂ Δ₂ : Matrix (Fin s) (Fin s) ℝ}
    (hL : IsUnit L₁₁) (hD : IsUnit D₁) (hR : IsUnit R₁₁) (hA : A₁₁ = L₁₁ * D₁ * R₁₁)
    (hL₂₁ : L₂₁ = A₂₁ * R₁₁⁻¹ * D₁⁻¹) (hR₁₂ : R₁₂ = D₁⁻¹ * L₁₁⁻¹ * A₁₂)
    (hΔ : Δ₂ = A₂₂ - L₂₁ * D₁ * R₁₂) :
    Δ₂ = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).schurComplement ∧
      fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ =
        fromBlocks L₁₁ 0 L₂₁ 1 * fromBlocks D₁ 0 0 Δ₂ * fromBlocks R₁₁ R₁₂ 0 1 := by
  subst hL₂₁ hR₁₂
  have hΔ' : Δ₂ = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).schurComplement := by
    rw [hΔ, schurComplement_fromBlocks_of_mul_eq hD hA]
  exact ⟨hΔ', by rw [hΔ']; exact fromBlocks_eq_mul_fromBlocks_of_mul_eq hL hD hR hA⟩

end BlockLDU

/-! ### Theorem 3.7 -/

/-- **Theorem 3.7.** Let `A ∈ ℝ^{N×N}` be partitioned into `m × m` blocks `A_{ij}` by a labelling
`b : Fin N → Fin m`. Then `A` admits a unique block LU factorization (with `L` having unit
diagonal blocks) if and only if the `m - 1` dominant principal block minors of `A` are nonzero,
that is, the leading block submatrices `A(b < k)` are nonsingular for every label `k` attained by
`b` (backbone `Matrix.existsUnique_isBlockLU_iff`). It extends Theorem 3.4, which is the case
`m = N`, `b = id` (`Matrix.isBlockLU_id_iff`). -/
theorem theorem_3_7 {N m : ℕ} (b : Fin N → Fin m) (A : Matrix (Fin N) (Fin N) ℝ) :
    (∃! LU : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ, IsBlockLU b A LU.1 LU.2) ↔
      ∀ k ∈ Set.range b, IsUnit (A.toBlock (b · < k) (b · < k)) :=
  existsUnique_isBlockLU_iff b A

/-! ### §3.8.2: the inverse of a block-partitioned matrix -/

/-- **(3.57), the Sherman–Morrison or Woodbury formula.** For a block matrix `A = C + U B V` with
`C` and `I + B V C⁻¹ U` nonsingular,

`A⁻¹ = (C + U B V)⁻¹ = C⁻¹ - C⁻¹ U (I + B V C⁻¹ U)⁻¹ B V C⁻¹`

(backbone `Matrix.add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add`; `B` itself may be singular,
unlike in Mathlib's `Matrix.add_mul_mul_inv_eq_sub`). It is effective when `C` — for instance the
block diagonal of `A` — is easy to invert and `U`, `B`, `V` carry connections between the diagonal
blocks that are of modest relevance. -/
theorem equation_3_57 {n m : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} (hC : IsUnit C)
    (U : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin m) (Fin n) ℝ)
    (hW : IsUnit (1 + B * V * C⁻¹ * U)) :
    (C + U * B * V)⁻¹ = C⁻¹ - C⁻¹ * U * (1 + B * V * C⁻¹ * U)⁻¹ * B * V * C⁻¹ :=
  add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add hC U B V hW

/-! ### §3.8.3: block tridiagonal systems -/

section BlockTridiagonal

variable {N m : ℕ} {b : Fin N → Fin m} {A L U : Matrix (Fin N) (Fin N) ℝ}

/-- A product of two blocks, entry by entry, as a sum over the labels of the middle block. -/
private theorem toBlock_mul_toBlock_apply (k : Fin m) {p r : Fin N → Prop}
    (X Y : Matrix (Fin N) (Fin N) ℝ) (i : {x : Fin N // p x}) (j : {x : Fin N // r x}) :
    (X.toBlock p (fun x => b x = k) * Y.toBlock (fun x => b x = k) r) i j =
      ∑ j' ∈ univ.filter fun x => b x = k, X i.1 j' * Y j' j.1 := by
  rw [mul_apply]
  exact (Finset.sum_subtype _ (fun x => by simp) fun j' => X i.1 j' * Y j' j.1).symm

/-- A row of `U` agrees with the corresponding row of `A` as soon as the entries of `U` in the
blocks strictly below the label of that row do not meet the column: the first block row of a
block LU factorization, and the superdiagonal blocks of a block bidiagonal one. -/
private theorem upper_apply_eq (h : IsBlockLU b A L U) {i j : Fin N}
    (hlow : ∀ j', b j' < b i → U j' j = 0) : U i j = A i j := by
  have key : (L * U) i j = ((1 : Matrix (Fin N) (Fin N) ℝ) * U) i j := by
    rw [mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rcases lt_trichotomy (b j') (b i) with hb | hb | hb
    · rw [hlow j' hb, mul_zero, mul_zero]
    · rw [h.isBlockUnitLowerTriangular.apply_eq_one_of_eq i j' hb.symm]
    · rw [h.isBlockUnitLowerTriangular.blockTriangular (OrderDual.toDual_lt_toDual.2 hb),
        one_apply_ne fun hij => hb.ne (congrArg b hij), zero_mul]
  rw [h.mul_eq, Matrix.one_mul] at key
  exact key.symm

/-- **§3.8.3, the block bandwidth of the factors.** For a block tridiagonal `A` — the blocks
`A_{ij}` with `|i - j| ≥ 2` vanish — whose leading principal block submatrices are nonsingular,
the block LU factors are block bidiagonal: `L` has only its diagonal and first subdiagonal
blocks, `U` only its diagonal and first superdiagonal blocks. This is the block form of Property
3.4; as there, the clause for `U` needs no hypothesis on the leading blocks, while the clause for
`L` does (backbone `Matrix.IsBlockLU.toBlock`, `Matrix.IsBlockLU.toBlock_not_left`,
`Matrix.IsBlockLU.toBlock_not_right`). -/
theorem blockTridiagonal_isBlockBidiagonal (h : IsBlockLU b A L U)
    (htriL : ∀ i j, (b j : ℕ) + 1 < b i → A i j = 0)
    (htriU : ∀ i j, (b i : ℕ) + 1 < b j → A i j = 0)
    (hlead : ∀ k : Fin m, IsUnit (A.toBlock (b · ≤ k) (b · ≤ k))) :
    (∀ i j, (b j : ℕ) + 1 < b i → L i j = 0) ∧ ∀ i j, (b i : ℕ) + 1 < b j → U i j = 0 := by
  constructor
  · intro i j hij
    have hp : ∀ x y : Fin N, b x ≤ b j → b y ≤ b x → b y ≤ b j := fun _ _ hx hyx => hyx.trans hx
    have hLp : IsUnit (L.toBlock (b · ≤ b j) (b · ≤ b j)) :=
      (h.toBlock hp).isBlockUnitLowerTriangular.isUnit
    have hUp : IsUnit (U.toBlock (b · ≤ b j) (b · ≤ b j)) := by
      have hmul := (h.toBlock hp).mul_eq
      rw [isUnit_iff_isUnit_det] at hLp ⊢
      have hAp := hlead (b j)
      rw [isUnit_iff_isUnit_det, ← hmul, det_mul] at hAp
      exact isUnit_of_mul_isUnit_right hAp
    have hLeq : L.toBlock (fun x => ¬ b x ≤ b j) (b · ≤ b j) =
        A.toBlock (fun x => ¬ b x ≤ b j) (b · ≤ b j) *
          (U.toBlock (b · ≤ b j) (b · ≤ b j))⁻¹ := by
      rw [h.toBlock_not_left hp, Matrix.mul_assoc,
        mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hUp), Matrix.mul_one]
    have hi : ¬ b i ≤ b j := not_le.2 (Fin.lt_def.2 (by omega))
    have hentry := congrFun (congrFun hLeq ⟨i, hi⟩) ⟨j, le_rfl⟩
    rw [toBlock_apply, mul_apply] at hentry
    rw [hentry]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [toBlock_apply, htriL i x.1 (by have := Fin.le_def.1 x.2; omega), zero_mul]
  · intro i j hij
    have hp : ∀ x y : Fin N, b x ≤ b i → b y ≤ b x → b y ≤ b i := fun _ _ hx hyx => hyx.trans hx
    have hLp : IsUnit (L.toBlock (b · ≤ b i) (b · ≤ b i)) :=
      (h.toBlock hp).isBlockUnitLowerTriangular.isUnit
    have hUeq : U.toBlock (b · ≤ b i) (fun x => ¬ b x ≤ b i) =
        (L.toBlock (b · ≤ b i) (b · ≤ b i))⁻¹ *
          A.toBlock (b · ≤ b i) (fun x => ¬ b x ≤ b i) := by
      rw [h.toBlock_not_right hp, ← Matrix.mul_assoc,
        nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hLp), Matrix.one_mul]
    have hj : ¬ b j ≤ b i := not_le.2 (Fin.lt_def.2 (by omega))
    have hentry := congrFun (congrFun hUeq ⟨i, le_rfl⟩) ⟨j, hj⟩
    rw [toBlock_apply, mul_apply] at hentry
    rw [hentry]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [toBlock_apply, htriU x.1 j (by have := Fin.le_def.1 x.2; omega), mul_zero]

/-- **§3.8.3, the block Thomas factorization (3.58).** Let `A` be block tridiagonal with
nonsingular leading principal block submatrices and let `A = L U` be its block LU factorization,
which by `blockTridiagonal_isBlockBidiagonal` is block bidiagonal. Equating the blocks gives
`U₁ = A₁₁`, the superdiagonal blocks of `U` are those of `A`, and the remaining blocks are
obtained sequentially, for `i = 2, …, n`, by solving `L_{i-1} U_{i-1} = A_{i,i-1}` for the
subdiagonal block of `L` and computing `U_i = A_{ii} - L_{i-1} A_{i-1,i}`. -/
theorem blockTridiagonal_lu (h : IsBlockLU b A L U)
    (htriL : ∀ i j, (b j : ℕ) + 1 < b i → A i j = 0)
    (htriU : ∀ i j, (b i : ℕ) + 1 < b j → A i j = 0)
    (hlead : ∀ k : Fin m, IsUnit (A.toBlock (b · ≤ k) (b · ≤ k))) :
    (∀ k : Fin m, (∀ i, k ≤ b i) →
        U.toBlock (b · = k) (b · = k) = A.toBlock (b · = k) (b · = k)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        U.toBlock (b · = k) (b · = l) = A.toBlock (b · = k) (b · = l)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        L.toBlock (b · = l) (b · = k) * U.toBlock (b · = k) (b · = k) =
          A.toBlock (b · = l) (b · = k)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        U.toBlock (b · = l) (b · = l) = A.toBlock (b · = l) (b · = l) -
          L.toBlock (b · = l) (b · = k) * A.toBlock (b · = k) (b · = l)) := by
  obtain ⟨hLbd, hUbd⟩ := blockTridiagonal_isBlockBidiagonal h htriL htriU hlead
  have hsuper : ∀ {i j : Fin N}, ((b i : ℕ) + 1 = b j ∨ ∀ x, b i ≤ b x) → U i j = A i j := by
    rintro i j (hij | hmin)
    · exact upper_apply_eq h fun j' hj' => hUbd j' j (by have := Fin.lt_def.1 hj'; omega)
    · exact upper_apply_eq h fun j' hj' => absurd (hmin j') (not_le.2 hj')
  refine ⟨fun k hk => ?_, fun k l hkl => ?_, fun k l hkl => ?_, fun k l hkl => ?_⟩
  · ext i j
    exact hsuper (Or.inr fun x => by rw [i.2]; exact hk x)
  · ext i j
    exact hsuper (Or.inl (by rw [i.2, j.2]; exact hkl))
  · ext i j
    rw [toBlock_mul_toBlock_apply, toBlock_apply, ← h.mul_eq, mul_apply]
    refine Finset.sum_subset (filter_subset _ _) fun x _ hx => ?_
    have hxk : b x ≠ k := by simpa using hx
    rcases lt_or_gt_of_ne hxk with hlt | hgt
    · rw [hLbd i.1 x (by rw [i.2]; have := Fin.lt_def.1 hlt; omega), zero_mul]
    · rcases eq_or_lt_of_le (show l ≤ b x from Fin.le_def.2 (by
        have := Fin.lt_def.1 hgt; omega)) with heq | hlt'
      · rw [h.blockTriangular (show b j.1 < b x by
          rw [j.2, ← heq]; exact Fin.lt_def.2 (by omega)), mul_zero]
      · rw [h.isBlockUnitLowerTriangular.blockTriangular
          (OrderDual.toDual_lt_toDual.2 (show b i.1 < b x by rw [i.2]; exact hlt')), zero_mul]
  · ext i j
    have hone : ∀ x ∈ univ.filter fun x => b x = k,
        (1 : Matrix (Fin N) (Fin N) ℝ) i.1 x * U x j.1 = 0 := by
      intro x hx
      have hxk : b x = k := by simpa using hx
      rw [one_apply_ne fun hij => by rw [← hij, i.2] at hxk; omega, zero_mul]
    have hrest : ∀ x ∈ univ.filter fun x => ¬ b x = k,
        L i.1 x * U x j.1 = (1 : Matrix (Fin N) (Fin N) ℝ) i.1 x * U x j.1 := by
      intro x hx
      have hxk : b x ≠ k := by simpa using hx
      rcases lt_or_gt_of_ne hxk with hlt | hgt
      · have hne : i.1 ≠ x := fun hij => by
          rw [← hij, i.2] at hlt; exact absurd (Fin.lt_def.1 hlt) (by omega)
        rw [hLbd i.1 x (by rw [i.2]; have := Fin.lt_def.1 hlt; omega), one_apply_ne hne,
          zero_mul]
      · rcases eq_or_lt_of_le (show l ≤ b x from Fin.le_def.2 (by
          have := Fin.lt_def.1 hgt; omega)) with heq | hlt'
        · rw [h.isBlockUnitLowerTriangular.apply_eq_one_of_eq i.1 x (by rw [i.2, ← heq])]
        · have hne : i.1 ≠ x := fun hij => by
            rw [← hij, i.2] at hlt'; exact absurd hlt' (lt_irrefl _)
          rw [h.isBlockUnitLowerTriangular.blockTriangular
            (OrderDual.toDual_lt_toDual.2 (show b i.1 < b x by rw [i.2]; exact hlt')),
            one_apply_ne hne, zero_mul]
    have hsum : A i.1 j.1 =
        (∑ x ∈ univ.filter fun x => b x = k, L i.1 x * U x j.1) + U i.1 j.1 := by
      have hall : (∑ x ∈ univ.filter fun x => b x = k,
            (1 : Matrix (Fin N) (Fin N) ℝ) i.1 x * U x j.1) +
          ∑ x ∈ univ.filter fun x => ¬ b x = k,
            (1 : Matrix (Fin N) (Fin N) ℝ) i.1 x * U x j.1 = U i.1 j.1 := by
        rw [Finset.sum_filter_add_sum_filter_not univ (fun x => b x = k)
          fun x => (1 : Matrix (Fin N) (Fin N) ℝ) i.1 x * U x j.1, ← mul_apply, Matrix.one_mul]
      rw [Finset.sum_eq_zero hone, zero_add] at hall
      rw [← h.mul_eq, mul_apply,
        ← Finset.sum_filter_add_sum_filter_not univ (fun x => b x = k)
          fun x => L i.1 x * U x j.1, Finset.sum_congr rfl hrest, hall]
    have hAU : ∀ x ∈ univ.filter fun x => b x = k, L i.1 x * A x j.1 = L i.1 x * U x j.1 := by
      intro x hx
      have hxk : b x = k := by simpa using hx
      rw [hsuper (Or.inl (by rw [hxk, j.2]; exact hkl))]
    rw [toBlock_apply, Matrix.sub_apply, toBlock_apply, toBlock_mul_toBlock_apply,
      Finset.sum_congr rfl hAU, hsum]
    ring

end BlockTridiagonal

end QuarteroniSaccoSaleri.Chapter03
