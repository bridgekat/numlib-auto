import Numlib.LinearAlgebra.Matrix.LU.Pivoting
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section04

/-!
# Quarteroni–Sacco–Saleri §3.5: pivoting

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.5, over the backbone `Numlib/LinearAlgebra/Matrix/LU/Pivoting`
(the pivoted stages `Matrix.gemPivotStage`, the partial-pivoting strategy
`Matrix.partialPivotRow`, the factorizations `P A = L U` and `P A Q = L U`) and
`Numlib/LinearAlgebra/Matrix/LU/Elimination`.

## Conventions

Gaussian elimination with a pivoting strategy `piv` is the backbone recurrence
`Matrix.gemPivotStage A piv k`, the pair of the matrix `A^{(k+1)}` after `k` stages and the row
permutation `σ_k` accumulated so far (`0`-based stages, as in §3.3); at stage `k` the row
`r = piv A^{(k)} k ≥ k` is exchanged with row `k` by the elementary permutation matrix
`P_k = (swap k r).permMatrix ℝ`, then the Gaussian transformation `M_k` of the exchanged matrix
eliminates the column. Partial pivoting by rows is the strategy `Matrix.partialPivotRow`, the
first row of maximal modulus in the current column, and `P = P_{n-1} ⋯ P_1` is the permutation
matrix `(gemPivotStage A piv n).2.permMatrix ℝ` of the accumulated interchanges. A permutation
matrix is `σ.permMatrix ℝ` for a permutation `σ` of the indices; `σ.permMatrix ℝ * A` permutes
the rows of `A`, `A * τ.permMatrix ℝ` its columns.

## Contents

* `example_3_5` — the zero pivot of (3.33) cured by a row exchange, with (3.50).
* `equation_3_51` — `U = M_{n-1} P_{n-1} ⋯ M_1 P_1 A`, stage by stage and as a product.
* `equation_3_52` — `P A = L U` for partial pivoting, with `|l_ij| ≤ 1`, `L = P M⁻¹`, the solve
  through `L y = P b`, `U x = y`, and the existence for every square matrix.
* `completePivoting` — `P A Q = L U` with `|l_ij| ≤ 1` and rows of `U` dominated by the pivot.
* `pivoting_multipliers` — the entries of `L` are the multipliers of GEM without pivoting on
  `P A`.

Example 3.6 (a `16`-digit run), Remarks 3.3–3.4 (a numerical run and prose) and Program 9 are
not nodes.

## Readings

(3.52) is proved in the book for nonsingular `A`, so that a nonzero pivot exists at every stage;
the existence of `P A = L U` with `|l_ij| ≤ 1` holds for every square matrix (a zero pivot column
is skipped, backbone `Matrix.exists_permMatrix_mul_isLU`), and the recurrence with partial
pivoting produces it whenever its pivots are nonzero, which is automatic for nonsingular `A`
(`Matrix.gemPivotStage_partialPivotRow_pivot_ne_zero_of_isUnit`).
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Example 3.5 -/

/-- **Example 3.5, with (3.50).** For the matrix `A` of (3.33), the first Gaussian transformation
is `M⁽¹⁾ = [1, 0, 0; -2, 1, 0; -7, 0, 1]`, and exchanging the second and third rows of the stage
`A^{(2)} = M⁽¹⁾ A` of (3.33) by the permutation matrix `P = [1, 0, 0; 0, 0, 1; 0, 1, 0]` gives
`[1, 2, 3; 0, -6, -12; 0, 0, -1] = U`, already upper triangular, so that `M⁽²⁾ = I`; thus
`A = M₁⁻¹ P M₂⁻¹ U` and `P A = L U` with `L = [1, 0, 0; 7, 1, 0; 2, 0, 1]`. -/
theorem example_3_5 :
    gaussTransform !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 0 = !![1, 0, 0; -2, 1, 0; -7, 0, 1] ∧
    gemStage !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 1 =
      !![1, 0, 0; -2, 1, 0; -7, 0, 1] * !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] ∧
    !![(1 : ℝ), 0, 0; 0, 0, 1; 0, 1, 0] * gemStage !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 1 =
      !![1, 2, 3; 0, -6, -12; 0, 0, -1] ∧
    gaussTransform !![(1 : ℝ), 2, 3; 0, -6, -12; 0, 0, -1] 1 = 1 ∧
    !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] =
      (gaussTransform !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 0)⁻¹ *
        !![(1 : ℝ), 0, 0; 0, 0, 1; 0, 1, 0] *
          (gaussTransform !![(1 : ℝ), 2, 3; 0, -6, -12; 0, 0, -1] 1)⁻¹ *
            !![1, 2, 3; 0, -6, -12; 0, 0, -1] ∧
    IsLU (!![(1 : ℝ), 0, 0; 0, 0, 1; 0, 1, 0] * !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9])
      !![1, 0, 0; 7, 1, 0; 2, 0, 1] !![1, 2, 3; 0, -6, -12; 0, 0, -1] := by
  have hM1 : gaussTransform !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 0 =
      !![1, 0, 0; -2, 1, 0; -7, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [gaussTransform, elimMultipliers_apply, Fin.lt_def]
  have hM2 : gaussTransform !![(1 : ℝ), 2, 3; 0, -6, -12; 0, 0, -1] 1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gaussTransform, elimMultipliers_apply, Fin.lt_def, one_apply]
  have hstage : gemStage !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 1 =
      !![1, 0, 0; -2, 1, 0; -7, 0, 1] * !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] := by
    rw [gemStage_succ_eq_gaussTransform_mul _ (by norm_num : 0 < 3), gemStage_zero]
    exact congrArg (· * _) hM1
  have hM1inv : (!![(1 : ℝ), 0, 0; -2, 1, 0; -7, 0, 1])⁻¹ = !![1, 0, 0; 2, 1, 0; 7, 0, 1] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, one_apply]
  have hPA : !![(1 : ℝ), 0, 0; 0, 0, 1; 0, 1, 0] * !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] =
      !![1, 0, 0; 7, 1, 0; 2, 0, 1] * !![1, 2, 3; 0, -6, -12; 0, 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  refine ⟨hM1, hstage, ?_, hM2, ?_, ?_⟩
  · rw [hstage]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  · rw [hM1, hM2, hM1inv, inv_one, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  · rw [hPA]
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, rfl⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> simp
    · fin_cases i <;> fin_cases j <;> simp_all

/-! ### (3.51)–(3.52): the factorization `P A = L U` -/

section Pivoted

variable (A : Matrix (Fin n) (Fin n) ℝ) (piv : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n)

/-- The factor `M_k P_k` of stage `k` of pivoted Gaussian elimination: the permutation matrix
of the interchange, followed by the Gaussian transformation of the exchanged matrix (`1` past
the last stage). -/
private noncomputable def pivotFactor (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : k < n then
    gaussTransform ((gemPivotSwap A piv k h).permMatrix ℝ * (gemPivotStage A piv k).1) ⟨k, h⟩ *
      (gemPivotSwap A piv k h).permMatrix ℝ
  else 1

/-- The permutation matrix `P_k` of the interchange of stage `k` (`1` past the last stage). -/
private noncomputable def pivotPerm (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : k < n then (gemPivotSwap A piv k h).permMatrix ℝ else 1

/-- After `k` stages the current matrix is the product of the stage factors applied to `A`,
`A^{(k+1)} = M_{k-1} P_{k-1} ⋯ M_0 P_0 A`. -/
private theorem gemPivotStage_fst_eq_prod (k : ℕ) :
    (gemPivotStage A piv k).1 =
      (List.ofFn fun i : Fin k => pivotFactor A piv i).reverse.prod * A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.prod_cons, Matrix.mul_assoc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    by_cases h : k < n
    · rw [gemPivotStage_succ_fst_eq_gaussTransform_mul A piv h, pivotFactor, dite_eq_left h,
        Matrix.mul_assoc]
    · rw [gemPivotStage_succ_of_le A piv (not_lt.1 h), pivotFactor, dite_eq_right h, Matrix.one_mul]

/-- The permutation accumulated after `k` stages has the permutation matrix `P_{k-1} ⋯ P_0`. -/
private theorem gemPivotStage_snd_permMatrix_eq_prod (k : ℕ) :
    (gemPivotStage A piv k).2.permMatrix ℝ =
      (List.ofFn fun i : Fin k => pivotPerm A piv i).reverse.prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.prod_cons]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    by_cases h : k < n
    · rw [gemPivotStage_succ_of_lt A piv h, Matrix.permMatrix_mul, pivotPerm, dite_eq_left h]
    · rw [gemPivotStage_succ_of_le A piv (not_lt.1 h), pivotPerm, dite_eq_right h, Matrix.one_mul]

/-- The stage factors indexed by `Fin n`, as in (3.51). -/
private theorem ofFn_pivotFactor :
    (List.ofFn fun k : Fin n => pivotFactor A piv k) =
      List.ofFn fun k : Fin n =>
        gaussTransform ((gemPivotSwap A piv k k.2).permMatrix ℝ * (gemPivotStage A piv k).1) k *
          (gemPivotSwap A piv k k.2).permMatrix ℝ :=
  congrArg List.ofFn (funext fun k => by rw [pivotFactor, dite_eq_left k.2])

/-- **(3.51).** Gaussian elimination with (partial) pivoting, `piv` any strategy: at each stage
`A^{(k+2)} = M_k P_k A^{(k+1)}`, where `P_k` is the elementary permutation matrix exchanging row
`k` with the chosen row and `M_k` the Gaussian transformation of the exchanged matrix, so that
the final upper triangular matrix is `U = A^{(n)} = M_{n-1} P_{n-1} ⋯ M_1 P_1 A` and the
accumulated permutation matrix is `P = P_{n-1} ⋯ P_1` (backbone
`Matrix.gemPivotStage_succ_fst_eq_gaussTransform_mul`, `Matrix.gemPivotStage_succ_of_lt`). -/
theorem equation_3_51 :
    (∀ k : Fin n, (gemPivotStage A piv (k + 1)).1 =
      gaussTransform ((gemPivotSwap A piv k k.2).permMatrix ℝ * (gemPivotStage A piv k).1) k *
        ((gemPivotSwap A piv k k.2).permMatrix ℝ * (gemPivotStage A piv k).1)) ∧
    (gemPivotStage A piv n).1 =
      (List.ofFn fun k : Fin n =>
        gaussTransform ((gemPivotSwap A piv k k.2).permMatrix ℝ * (gemPivotStage A piv k).1) k *
          (gemPivotSwap A piv k k.2).permMatrix ℝ).reverse.prod * A ∧
    (gemPivotStage A piv n).2.permMatrix ℝ =
      (List.ofFn fun k : Fin n => (gemPivotSwap A piv k k.2).permMatrix ℝ).reverse.prod := by
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have := gemPivotStage_succ_fst_eq_gaussTransform_mul A piv k.2
    simpa only [Fin.eta] using this
  · rw [gemPivotStage_fst_eq_prod A piv n, ofFn_pivotFactor]
  · rw [gemPivotStage_snd_permMatrix_eq_prod A piv n]
    congr 2
    exact congrArg List.ofFn (funext fun k => by rw [pivotPerm, dite_eq_left k.2])

/-- **(3.52).** For a nonsingular `A`, Gaussian elimination with partial pivoting produces
`U = M A` with `M = M_{n-1} P_{n-1} ⋯ M_1 P_1` and the permutation matrix `P = P_{n-1} ⋯ P_1`
of (3.51), and `L = P M⁻¹` is unit lower triangular, so that `P A = L U`; the entries of `L` are
the multipliers of GEM without pivoting applied to `P A`, they satisfy `|l_ij| ≤ 1`, and solving
`L y = P b`, `U x = y` solves `A x = b` (backbone `Matrix.gemPivotStage_permMatrix_mul_isLU`,
`Matrix.gemPivotStage_partialPivotRow_norm_gemLower_le_one`, `Matrix.mulVec_luSolve_permMatrix`).
Moreover *every* square matrix has a factorization `P A = L U` with `|l_ij| ≤ 1`
(`Matrix.exists_permMatrix_mul_isLU`). -/
theorem equation_3_52 (hA : IsUnit A) :
    IsLU ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A)
        (gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A))
        (gemPivotStage A partialPivotRow n).1 ∧
      (∀ i j, |gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) i j| ≤ 1) ∧
      gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) =
        (gemPivotStage A partialPivotRow n).2.permMatrix ℝ *
          ((List.ofFn fun k : Fin n =>
            gaussTransform ((gemPivotSwap A partialPivotRow k k.2).permMatrix ℝ *
              (gemPivotStage A partialPivotRow k).1) k *
              (gemPivotSwap A partialPivotRow k k.2).permMatrix ℝ).reverse.prod)⁻¹ ∧
      (∀ b, A *ᵥ luSolve (gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A))
        (gemPivotStage A partialPivotRow n).1
        ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ *ᵥ b) = b) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ (σ : Equiv.Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) ℝ),
        IsLU (σ.permMatrix ℝ * B) L U ∧ ∀ i j, |L i j| ≤ 1 := by
  have hpiv : ∀ (M : Matrix (Fin n) (Fin n) ℝ) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  have hLU := gemPivotStage_permMatrix_mul_isLU A partialPivotRow hpiv fun k hk _ =>
    gemPivotStage_partialPivotRow_pivot_ne_zero_of_isUnit A hA k hk
  set P := (gemPivotStage A partialPivotRow n).2.permMatrix ℝ with hP
  set M := (List.ofFn fun k : Fin n =>
    gaussTransform ((gemPivotSwap A partialPivotRow k k.2).permMatrix ℝ *
      (gemPivotStage A partialPivotRow k).1) k *
      (gemPivotSwap A partialPivotRow k k.2).permMatrix ℝ).reverse.prod with hM
  have hU : (gemPivotStage A partialPivotRow n).1 = M * A := (equation_3_51 A partialPivotRow).2.1
  have hMunit : IsUnit M := by
    refine List.prod_isUnit fun m hm => ?_
    rw [List.mem_reverse, List.mem_ofFn] at hm
    obtain ⟨k, rfl⟩ := hm
    exact (IsUnit.of_mul_eq_one _ (gaussTransform_mul_elimMul _ _)).mul (isUnit_permMatrix _)
  refine ⟨hLU, fun i j => ?_, ?_, fun b => ?_, fun B => ?_⟩
  · simpa [Real.norm_eq_abs] using gemPivotStage_partialPivotRow_norm_gemLower_le_one A i j
  · have h1 : gemLower (P * A) * M * A = P * A := by
      rw [Matrix.mul_assoc, ← hU, hLU.mul_eq]
    have hAdet := (isUnit_iff_isUnit_det A).1 hA
    have h2 : gemLower (P * A) * M = P := by
      calc gemLower (P * A) * M = gemLower (P * A) * M * A * A⁻¹ := by
            rw [Matrix.mul_nonsing_inv_cancel_right _ _ hAdet]
        _ = P * A * A⁻¹ := by rw [h1]
        _ = P := Matrix.mul_nonsing_inv_cancel_right _ _ hAdet
    calc gemLower (P * A) = gemLower (P * A) * M * M⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right _ _ ((isUnit_iff_isUnit_det M).1 hMunit)).symm
      _ = P * M⁻¹ := by rw [h2]
  · refine mulVec_luSolve_permMatrix b hLU fun i => ?_
    have hdet : (P * A).det ≠ 0 := by
      rw [det_mul]
      exact mul_ne_zero (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 (isUnit_permMatrix _)))
        (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det A).1 hA))
    rw [hLU.det_eq_prod_diag, Finset.prod_ne_zero_iff] at hdet
    exact hdet i (mem_univ i)
  · obtain ⟨σ, L, U, h, hL⟩ := exists_permMatrix_mul_isLU B
    exact ⟨σ, L, U, h, fun i j => by simpa [Real.norm_eq_abs] using hL i j⟩

/-- **§3.5, complete pivoting.** Exchanging at each stage the current row and column with those
of the entry of largest modulus in the trailing block gives permutation matrices `P` (rows) and
`Q` (columns) with `P A Q = L U`, `L` unit lower triangular with entries of modulus at most `1`
and every row of `U` dominated by its diagonal entry (backbone
`Matrix.exists_permMatrix_mul_mul_permMatrix_isLU`). -/
theorem completePivoting :
    ∃ (σ τ : Equiv.Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) ℝ),
      IsLU (σ.permMatrix ℝ * A * τ.permMatrix ℝ) L U ∧ (∀ i j, |L i j| ≤ 1) ∧
        ∀ i j, |U i j| ≤ |U i i| := by
  obtain ⟨σ, τ, L, U, h, hL, hU⟩ := exists_permMatrix_mul_mul_permMatrix_isLU A
  exact ⟨σ, τ, L, U, h, fun i j => by simpa [Real.norm_eq_abs] using hL i j,
    fun i j => by simpa [Real.norm_eq_abs] using hU i j⟩

/-- **§3.5, the multipliers of pivoted elimination.** "The entries of the matrix `L` coincide
with the multipliers computed by LU factorization, without pivoting, when applied to the matrix
`P A`": if `P A = L U` and `P A` satisfies the hypothesis of Theorem 3.4, then `L` is the
multiplier matrix and `U` the last stage of GEM without pivoting on `P A` (backbone
`Matrix.IsLU.eq_of_permMatrix_mul`). -/
theorem pivoting_multipliers {σ : Equiv.Perm (Fin n)} {L U : Matrix (Fin n) (Fin n) ℝ}
    (h : IsLU (σ.permMatrix ℝ * A) L U)
    (hPA : ∀ k, IsUnit ((σ.permMatrix ℝ * A).strictLeadingPrincipalSubmatrix k)) :
    L = gemLower (σ.permMatrix ℝ * A) ∧ U = gemStage (σ.permMatrix ℝ * A) n :=
  h.eq_of_permMatrix_mul hPA

end Pivoted

end QuarteroniSaccoSaleri.Chapter03
