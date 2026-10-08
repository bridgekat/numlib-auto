import Numlib.LinearAlgebra.Matrix.BlockTridiagonal
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
* `blockTridiagonal_lu` — §3.8.3, the block Thomas recurrences, from the backbone's
  `Matrix.IsBlockLU.blockBidiagonal_of_blockTridiagonal`: `U₁ = A₁₁`, `L_{i-1} U_{i-1} = A_{i,i-1}`,
  `U_i = A_{ii} - L_{i-1} A_{i-1,i}`.

The storage counts, the block Cholesky–Thomas reduction of a symmetric positive definite block
tridiagonal system and the `(7/6)(n - 1) p³` flop count are prose.

## Readings

§3.8.3 posits the shape of the factors (`L` block unit lower bidiagonal, `U` block upper
bidiagonal with the superdiagonal blocks of `A`) and reads off the recurrence by equating blocks.
Here the shape is *proved*: the backbone's `Matrix.IsBlockLU.blockBidiagonal_of_blockTridiagonal` is
the block form of Property 3.4 — the lower clause under the hypothesis of Theorem 3.7, as in §3.7 —
and `blockTridiagonal_lu`
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

/-- **§3.8.3, the block Thomas factorization (3.58).** Let `A` be block tridiagonal with
nonsingular leading principal block submatrices and let `A = L U` be its block LU factorization,
which by `Matrix.IsBlockLU.blockBidiagonal_of_blockTridiagonal` is block bidiagonal. Equating the
blocks gives
`U₁ = A₁₁`, the superdiagonal blocks of `U` are those of `A`, and the remaining blocks are
obtained sequentially, for `i = 2, …, n`, by solving `L_{i-1} U_{i-1} = A_{i,i-1}` for the
subdiagonal block of `L` and computing `U_i = A_{ii} - L_{i-1} A_{i-1,i}`. Backbone
`Matrix.IsBlockLU.toBlock_recurrence_of_blockTridiagonal`. -/
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
          L.toBlock (b · = l) (b · = k) * A.toBlock (b · = k) (b · = l)) :=
  h.toBlock_recurrence_of_blockTridiagonal htriL htriU hlead

end BlockTridiagonal

end QuarteroniSaccoSaleri.Chapter03
