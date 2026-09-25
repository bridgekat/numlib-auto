import Numlib.Direct.CyclicReduction

/-!
# Golub–Van Loan §4.5: block tridiagonal systems

Surface file for [golub2013matrix] §4.5: the block LU factorization (4.5.3) with its recurrence
(4.5.4), block diagonal dominance (4.5.6) and its consequences (4.5.7)–(4.5.8), one step of block
cyclic reduction and its back substitution (§4.5.3), and the block scaling (4.5.13)→(4.5.14) of the
SPIKE framework. The section has no numbered theorem and no numbered algorithm.

## Conventions

The matrix (4.5.2) has `q × q` real blocks, `N + 1` diagonal blocks `D 0, …, D N` (0-based; the
book's `D_1, …, D_N` with `N` one larger), subdiagonal blocks `E 0, …, E (N − 1)` and superdiagonal
blocks `F 0, …, F (N − 1)`. In the block ring `Matrix (Fin q) (Fin q) ℝ` it is
`Matrix.tridiagonalOf E D F`, and the book's scalar matrix is its flattening
`Matrix.blockTridiagonal E F D : Matrix (Fin (N + 1) × Fin q) (Fin (N + 1) × Fin q) ℝ` by Mathlib's
`Matrix.comp` (a ring isomorphism, `Matrix.compRingEquiv`). The block recurrence (4.5.4) is the
backbone's `ℕ`-indexed `Matrix.tridiagonalLUPivot` (`U_i`) and `Matrix.tridiagonalLUMultiplier`
(`L_i`), so the blocks of the §4.5.1–4.5.2 statements are `ℕ`-indexed families. The book's `‖·‖₁`
of a block is `Matrix.lpOpNorm 1`. The constant-block system (4.5.9) is the backbone operator
`CyclicReduction.constBlockTridiagonal D F`, which is `Matrix.blockTridiagonal` applied to the
flattened vector (`CyclicReduction.constBlockTridiagonal_eq_blockTridiagonal_mulVec`).

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/BlockTridiagonal` (the recurrence, the factorization, block
dominance) and `Numlib/Direct/CyclicReduction`. The block substitution (4.5.5), the flop count of
cyclic reduction, Buneman's stabilization and the rest of the SPIKE framework (whose displays
(4.5.11)–(4.5.12) and the refined blockings were lost in conversion) are not formalized.

## Readings and errata

(4.5.8) prints `‖U_i‖₁ ≤ ‖A_n‖₁`, whose right-hand side has no referent in the section; it is read
as the `1`-norm of the whole matrix `A`. The `N = 7` display of §4.5.3 prints
`b₄ = F x₅ + D x₄ + F x₅` for `b₄ = F x₃ + D x₄ + F x₅`.
-/

open Matrix Finset

namespace GolubVanLoan.Chapter04

variable {N q : ℕ}

/-! ### §4.5.1 Block tridiagonal LU factorization -/

/-- **(4.5.3) with (4.5.4).** "By comparing blocks in `A = L U` we formally obtain the following
algorithm for computing the `L_i` and `U_i`: `U_1 = D_1`; for `i = 2:N`, solve `L_{i−1} U_{i−1} =
E_{i−1}` for `L_{i−1}`, `U_i = D_i − L_{i−1} F_{i−1}`. The procedure is defined as long as the `U_i`
are nonsingular." If the pivots `U_0, …, U_{N−1}` are nonsingular, the block tridiagonal matrix is
the product of the block unit lower bidiagonal matrix with subdiagonal blocks `L_i` and the block
upper bidiagonal matrix with diagonal blocks `U_i` and superdiagonal blocks `F_i`; the multipliers
solve `L_i U_i = E_i`. -/
theorem equation_4_5_3 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hU : ∀ i < N, IsUnit (tridiagonalLUPivot E D F i)) :
    blockTridiagonal (N := N) (fun i => E i) (fun i => F i) (fun i => D i) =
        blockTridiagonal (fun i => tridiagonalLUMultiplier E D F i) 0 1 *
          blockTridiagonal 0 (fun i => F i) (fun i => tridiagonalLUPivot E D F i) ∧
      ∀ i < N, tridiagonalLUMultiplier E D F i * tridiagonalLUPivot E D F i = E i := by
  refine ⟨?_, fun i hi => tridiagonalLUMultiplier_mul_tridiagonalLUPivot E D F (hU i hi)⟩
  simp only [blockTridiagonal, ← compRingEquiv_apply, ← map_mul]
  rw [tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot E D F hU]

/-! ### §4.5.2 Block diagonal dominance -/

/-- **(4.5.6).** "If we have `‖D_i⁻¹‖₁ (‖F_{i−1}‖₁ + ‖E_i‖₁) < 1`, `E_N ≡ F_0 ≡ 0`, for
`i = 1:N`, then the factorization (4.5.3) exists": every pivot `U_i` is nonsingular (so (4.5.3)
holds, `equation_4_5_3`), and the matrix `A` itself is nonsingular (the book's P4.5.1(a)). The
condition is stated 0-based, with the nonsingularity of the `D_i` it presupposes. -/
theorem equation_4_5_6 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    (∀ i ≤ N, IsUnit (tridiagonalLUPivot E D F i)) ∧
      IsUnit (blockTridiagonal (N := N) (fun i => E i) (fun i => F i) (fun i => D i)) := by
  have hdom := (isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
  exact ⟨fun i hi => (hdom.isUnit_tridiagonalLUPivot hi).1, hdom.isUnit_blockTridiagonal⟩

/-- **(4.5.7).** Under the block diagonal dominance (4.5.6), the multipliers of (4.5.3) satisfy
`‖L_i‖₁ ≤ 1`. -/
theorem equation_4_5_7 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    ∀ i < N, lpOpNorm 1 (tridiagonalLUMultiplier E D F i) ≤ 1 := fun _ hi =>
  ((isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
    ).lpOpNorm_tridiagonalLUMultiplier_le hi

/-- **(4.5.8)**, read as `‖U_i‖₁ ≤ ‖A‖₁`: under the block diagonal dominance (4.5.6), the pivots of
(4.5.3) are bounded by the `1`-norm of the whole block tridiagonal matrix `A` (the printed
`‖A_n‖₁` has no referent in the section). -/
theorem equation_4_5_8 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    ∀ i ≤ N, lpOpNorm 1 (tridiagonalLUPivot E D F i) ≤
      lpOpNorm 1 (blockTridiagonal (N := N) (fun i => E i) (fun i => F i) (fun i => D i)) :=
  fun _ hi => ((isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
    ).lpOpNorm_tridiagonalLUPivot_le hi

/-! ### §4.5.3 Block-cyclic reduction -/

open CyclicReduction in
/-- **§4.5.3, block cyclic reduction.** For the system (4.5.9) with constant blocks `D`, `F`
satisfying `D F = F D`: "for `i = 2, 4, 6` we multiply equations `i − 1`, `i`, and `i + 1` by `F`,
`−D`, and `F`, respectively, and add the resulting equations"; "we have removed the odd-indexed
`x_i` and are left with a reduced block tridiagonal system … where `D⁽¹⁾ = 2F² − D²` and
`F⁽¹⁾ = F²` commute." In general (0-based, `2M + 1` unknowns): the unknowns `x_1, x_3, …` solve the
system of the same form with blocks `D⁽¹⁾ = 2F² − D²` (`reducedDiag`), `F⁽¹⁾ = F²` (`reducedOff`)
and right-hand side `b⁽¹⁾_j = F (b_{2j} + b_{2j+2}) − D b_{2j+1}` (`reducedRhs`); the new blocks
commute; and for `N = 2^{k+1} − 1` unknowns (`size (k + 1)`) the reduction repeated `k` times
leaves "a single `q × q` system" `D_k x_{2^k − 1} = b_k` for the middle unknown. -/
theorem cyclicReduction_step {D F : Matrix (Fin q) (Fin q) ℝ} (hDF : D * F = F * D) :
    (∀ (M : ℕ) (x b : Fin (2 * M + 1) → Fin q → ℝ), constBlockTridiagonal D F x = b →
      constBlockTridiagonal (reducedDiag D F) (reducedOff F)
        (fun j : Fin M => x ⟨2 * j + 1, by omega⟩) = reducedRhs D F b) ∧
    reducedDiag D F * reducedOff F = reducedOff F * reducedDiag D F ∧
    (∀ (k : ℕ) (x b : Fin (size (k + 1)) → Fin q → ℝ), constBlockTridiagonal D F x = b →
      diagIter k D F *ᵥ x ⟨size k, by simp only [size]; omega⟩ = rhsIter k D F b) :=
  ⟨fun _ _ _ h => constBlockTridiagonal_reduce hDF h, commute_reduced hDF,
    fun k _ _ h => constBlockTridiagonal_iterate_reduce k hDF h⟩

open CyclicReduction in
/-- **§4.5.3, the back substitution.** "The vectors `x_2` and `x_6` are then found by solving the
systems `D⁽¹⁾ x_2 = b⁽¹⁾_2 − F⁽¹⁾ x_4`, … Finally, we use the first, third, fifth, and seventh
equations in the original system to compute `x_1, x_3, x_5`, and `x_7`": once the odd-indexed
unknowns (0-based) are known, the even-indexed ones solve `q × q` systems with matrix `D`,
`D x_{2j} = b_{2j} − F (x_{2j−1} + x_{2j+1})`, a missing neighbour being zero (`extend`). -/
theorem cyclicReduction_back {D F : Matrix (Fin q) (Fin q) ℝ} {M : ℕ}
    {x b : Fin (2 * M + 1) → Fin q → ℝ} (h : constBlockTridiagonal D F x = b) (j : Fin (M + 1)) :
    D *ᵥ x ⟨2 * j, by omega⟩ =
      b ⟨2 * j, by omega⟩ - F *ᵥ (extend x (2 * (j : ℕ) - 1) + extend x (2 * (j : ℕ) + 1)) :=
  constBlockTridiagonal_odd_eq h j

/-! ### §4.5.4 The SPIKE framework -/

/-- The block scaling in the block ring: `diag(D_i⁻¹) · tridiag(E, D, F) = tridiag(Ẽ, I, F̃)` with
`F̃_i = D_i⁻¹ F_i` and `Ẽ_i = D_{i+1}⁻¹ E_i`. -/
private theorem diagonal_inv_mul_tridiagonalOf (E F : Fin N → Matrix (Fin q) (Fin q) ℝ)
    (D : Fin (N + 1) → Matrix (Fin q) (Fin q) ℝ) (hD : ∀ i, IsUnit (D i)) :
    diagonal (fun i => (D i)⁻¹) * tridiagonalOf E D F =
      tridiagonalOf (fun i => (D i.succ)⁻¹ * E i) (fun _ => 1)
        (fun i => (D i.castSucc)⁻¹ * F i) := by
  ext1 i j
  have hi := i.isLt
  have hj := j.isLt
  rw [diagonal_mul]
  simp only [tridiagonalOf, of_apply]
  split_ifs with h1 h2 h3
  · rw [Fin.ext h1]
    exact nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (hD j))
  · have e : (⟨j, by omega⟩ : Fin N).succ = i := Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [e]
  · congr 2
  · rw [Matrix.mul_zero]

/-- **(4.5.13)→(4.5.14), the SPIKE scaling.** "If we premultiply the above matrix by the inverse of
`diag(D_1, D_2, D_3, D_4)`, then … the original linear system (4.5.13) transforms to (4.5.14),
where `D_i b̃_i = b_i`, `D_i F̃_i = F_i`, and `D_{i+1} Ẽ_i = E_i`": for nonsingular diagonal blocks,
`diag(D_i⁻¹) A` is the block tridiagonal matrix with identity diagonal blocks, superdiagonal
blocks `F̃_i = D_i⁻¹ F_i` and subdiagonal blocks `Ẽ_i = D_{i+1}⁻¹ E_i`, and `A x = b` iff
`(diag(D_i⁻¹) A) x = b̃` with `b̃_i = D_i⁻¹ b_i`. -/
theorem equation_4_5_14 (E F : Fin N → Matrix (Fin q) (Fin q) ℝ)
    (D : Fin (N + 1) → Matrix (Fin q) (Fin q) ℝ) (hD : ∀ i, IsUnit (D i)) :
    comp _ _ _ _ ℝ (diagonal fun i => (D i)⁻¹) * blockTridiagonal E F D =
        blockTridiagonal (fun i => (D i.succ)⁻¹ * E i) (fun i => (D i.castSucc)⁻¹ * F i)
          (fun _ => 1) ∧
      ∀ x b : Fin (N + 1) × Fin q → ℝ, blockTridiagonal E F D *ᵥ x = b ↔
        blockTridiagonal (fun i => (D i.succ)⁻¹ * E i) (fun i => (D i.castSucc)⁻¹ * F i)
            (fun _ => 1) *ᵥ x = fun p => ((D p.1)⁻¹ *ᵥ fun k => b (p.1, k)) p.2 := by
  have hmul : comp _ _ _ _ ℝ (diagonal fun i => (D i)⁻¹) * blockTridiagonal E F D =
      blockTridiagonal (fun i => (D i.succ)⁻¹ * E i) (fun i => (D i.castSucc)⁻¹ * F i)
        (fun _ => 1) := by
    simp only [blockTridiagonal, ← compRingEquiv_apply, ← map_mul]
    rw [diagonal_inv_mul_tridiagonalOf E F D hD]
  refine ⟨hmul, fun x b => ?_⟩
  set P := comp _ _ _ _ ℝ (diagonal fun i => (D i)⁻¹)
  have hQP : comp _ _ _ _ ℝ (diagonal D) * P = 1 := by
    simp only [P, ← compRingEquiv_apply, ← map_mul, diagonal_mul_diagonal]
    rw [← map_one (compRingEquiv (Fin (N + 1)) (Fin q) ℝ), ← diagonal_one]
    congr 2
    funext i
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (hD i))
  have hb : P *ᵥ b = fun p => ((D p.1)⁻¹ *ᵥ fun k => b (p.1, k)) p.2 := by
    ext ⟨i, k⟩
    simp only [P, mulVec, dotProduct, comp_apply, Fintype.sum_prod_type, diagonal_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  rw [← hmul, ← mulVec_mulVec, ← hb]
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg (comp _ _ _ _ ℝ (diagonal D) *ᵥ ·) h
    simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hQP, Matrix.one_mul, one_mulVec] using h'

end GolubVanLoan.Chapter04
