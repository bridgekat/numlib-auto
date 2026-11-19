/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LU.Pivoting
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section04

/-!
# Quarteroni, Sacco and Saleri, Section 3.5: Pivoting

This module formalizes Section 3.5 of [quarteroni2000numerical]. Gaussian elimination stops at a
zero pivot even for a nonsingular matrix, as (3.33) shows. Pivoting cures this: at stage $k$ a row
$r \ge k$ is exchanged with row $k$ by an elementary permutation matrix $P_k$, and the Gaussian
transformation $M_k$ of the exchanged matrix then eliminates column $k$. The result is
$U = M_{n-1} P_{n-1} \cdots M_0 P_0 A$ (3.51). With partial pivoting, which chooses a row of largest
modulus in the current column, this gives $PA = LU$ with $|l_{ij}| \le 1$ for every nonsingular $A$
(3.52). Complete pivoting also exchanges columns and gives $PAQ = LU$.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.LU.Pivoting` (the pivoted
stages `Matrix.gemPivotStage`, the partial pivoting strategy `Matrix.partialPivotRow`, the
factorizations $PA = LU$ and $PAQ = LU$) and `Numlib.LinearAlgebra.Matrix.LU.Elimination`.

## Main results

* Example 3.5, `QuarteroniSaccoSaleri.Chapter03.example_3_5`: one row exchange cures the zero pivot
  of (3.33), with (3.50).
* (3.51), `QuarteroniSaccoSaleri.Chapter03.equation_3_51`: $U = M_{n-1} P_{n-1} \cdots M_0 P_0 A$,
  stage by stage and as a product.
* (3.52), `QuarteroniSaccoSaleri.Chapter03.equation_3_52`: partial pivoting gives $PA = LU$ with
  $|l_{ij}| \le 1$ and $L = PM^{-1}$, and every square matrix has such a factorization.
* Section 3.5, `QuarteroniSaccoSaleri.Chapter03.completePivoting`: complete pivoting gives
  $PAQ = LU$ with $|l_{ij}| \le 1$ and $|u_{ij}| \le |u_{ii}|$.
* Section 3.5, `QuarteroniSaccoSaleri.Chapter03.pivoting_multipliers`: the entries of $L$ are the
  multipliers of GEM without pivoting on $PA$.

## Conventions

* Gaussian elimination with a pivoting strategy `piv` is `Matrix.gemPivotStage A piv k`, the pair of
  the matrix $A^{(k)}$ after $k$ stages and the row permutation accumulated so far. Stages are
  $0$-based, as in `NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section03`, so $A^{(0)} = A$ and
  $A^{(n)} = U$.
* At stage $k$ the row $r \ge k$ that `piv` chooses for $A^{(k)}$ is exchanged with row $k$ by the
  elementary permutation matrix $P_k$ = `(Equiv.swap k r).permMatrix ℝ` (the backbone's
  `Matrix.gemPivotSwap`), and the Gaussian transformation $M_k$ of the exchanged matrix eliminates
  column $k$.
* Partial pivoting by rows is the strategy `Matrix.partialPivotRow`: the first row $r \ge k$ of
  maximal modulus in column $k$. The permutation matrix $P = P_{n-1} \cdots P_0$ of the accumulated
  interchanges is `(gemPivotStage A piv n).2.permMatrix ℝ`.
* A permutation matrix is `σ.permMatrix ℝ` for a permutation `σ` of the indices. The product
  `σ.permMatrix ℝ * A` permutes the rows of $A$, and `A * τ.permMatrix ℝ` permutes its columns.

## Deviations from the source

* **(3.52)** (generalization). The source proves the factorization for nonsingular $A$. The
  existence of $PA = LU$ with $|l_{ij}| \le 1$ is also stated for every square matrix. See
  `QuarteroniSaccoSaleri.Chapter03.equation_3_52`.
* **Complete pivoting** (reading). The theorem concludes existence with entrywise bounds
  for both factors for every square matrix.

## Not formalized

* **Example 3.6**, a run in $16$-digit arithmetic.
* **Remarks 3.3–3.4**, a numerical run and prose.
* **Program 9.**
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Example 3.5 -/

/-- **Example 3.5** of [quarteroni2000numerical], with equation (3.50). Let $A$ be the matrix of
(3.33),
$$A = \begin{bmatrix} 1 & 2 & 3 \\ 2 & 4 & 5 \\ 7 & 8 & 9 \end{bmatrix}.$$
Its first Gaussian transformation is
$$M_1 = \begin{bmatrix} 1 & 0 & 0 \\ -2 & 1 & 0 \\ -7 & 0 & 1 \end{bmatrix},$$
and the second stage is $A^{(2)} = M_1 A$. The permutation matrix $P$ that exchanges the second
and third rows gives
$$P A^{(2)} = \begin{bmatrix} 1 & 2 & 3 \\ 0 & -6 & -12 \\ 0 & 0 & -1 \end{bmatrix} = U, \qquad
  P = \begin{bmatrix} 1 & 0 & 0 \\ 0 & 0 & 1 \\ 0 & 1 & 0 \end{bmatrix},$$
which is already upper triangular, so that the second Gaussian transformation is $M_2 = I$.
Hence $A = M_1^{-1} P M_2^{-1} U$, and $PA = LU$ is an LU factorization with
$$L = \begin{bmatrix} 1 & 0 & 0 \\ 7 & 1 & 0 \\ 2 & 0 & 1 \end{bmatrix}.$$

The transformations $M_1$ and $M_2$ are `Matrix.gaussTransform A 0` and
`Matrix.gaussTransform U 1`.
The stage $A^{(2)}$ of the book is `Matrix.gemStage A 1`. -/
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
      norm_num [gaussTransform, elimMultipliers_apply, Fin.lt_def, Matrix.one_apply]
  have hstage : gemStage !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 1 =
      !![1, 0, 0; -2, 1, 0; -7, 0, 1] * !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] := by
    rw [gemStage_succ_eq_gaussTransform_mul _ (by norm_num : 0 < 3), gemStage_zero]
    exact congrArg (· * _) hM1
  have hM1inv : (!![(1 : ℝ), 0, 0; -2, 1, 0; -7, 0, 1])⁻¹ = !![1, 0, 0; 2, 1, 0; 7, 0, 1] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
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

/-- The factor $M_k P_k$ of stage $k$ of pivoted Gaussian elimination: the permutation matrix of the
interchange, followed by the Gaussian transformation of the exchanged matrix; it is the identity
for $k \ge n$. -/
private noncomputable def pivotFactor (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : k < n then
    gaussTransform ((gemPivotSwap A piv k h).permMatrix ℝ * (gemPivotStage A piv k).1) ⟨k, h⟩ *
      (gemPivotSwap A piv k h).permMatrix ℝ
  else 1

/-- The permutation matrix $P_k$ of the interchange of stage $k$; it is the identity for $k \ge n$.
-/
private noncomputable def pivotPerm (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : k < n then (gemPivotSwap A piv k h).permMatrix ℝ else 1

/-- After $k$ stages the current matrix is $A^{(k)} = M_{k-1} P_{k-1} \cdots M_0 P_0 A$. -/
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

/-- After $k$ stages the accumulated permutation has the permutation matrix $P_{k-1} \cdots P_0$. -/
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

/-- The stage factors $M_k P_k$ indexed by $k \in \{0, \ldots, n - 1\}$, in the form of (3.51). -/
private theorem ofFn_pivotFactor :
    (List.ofFn fun k : Fin n => pivotFactor A piv k) =
      List.ofFn fun k : Fin n =>
        gaussTransform ((gemPivotSwap A piv k k.2).permMatrix ℝ * (gemPivotStage A piv k).1) k *
          (gemPivotSwap A piv k k.2).permMatrix ℝ :=
  congrArg List.ofFn (funext fun k => by rw [pivotFactor, dite_eq_left k.2])

/-- **Equation (3.51)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$, and let
`piv` be any pivoting strategy. Let $A^{(k)}$ be the stages of Gaussian elimination with this
strategy, let $P_k$ be the elementary permutation matrix that exchanges row $k$ with the chosen
row, and let $M_k$ be the Gaussian transformation of $P_k A^{(k)}$ at the pivot $k$. Then for
every $k \in \{0, \ldots, n - 1\}$,
$$A^{(k+1)} = M_k P_k A^{(k)},$$
the final upper triangular matrix is
$$U = A^{(n)} = M_{n-1} P_{n-1} \cdots M_0 P_0 A,$$
and the accumulated permutation matrix is $P = P_{n-1} \cdots P_0$.

The stages are $0$-based; the book writes $M_{n-1} P_{n-1} \cdots M_1 P_1 A$. The strategy `piv`
is any function that chooses a row for a matrix and a stage. The proof uses
`Matrix.gemPivotStage_succ_fst_eq_gaussTransform_mul` and `Matrix.gemPivotStage_succ_of_lt`. -/
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

/-- **Equation (3.52)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular. Let Gaussian elimination with partial pivoting give $U = A^{(n)} = MA$ with
$M = M_{n-1} P_{n-1} \cdots M_0 P_0$ and the permutation matrix $P = P_{n-1} \cdots P_0$ of
(3.51), and let $L$ be the multiplier matrix of GEM without pivoting on $PA$. Then:

* $PA = LU$ is an LU factorization, with $L$ unit lower triangular and $U$ upper triangular;
* $|l_{ij}| \le 1$ for all $i, j$;
* $L = P M^{-1}$;
* for every $b \in \mathbb{R}^n$, solving $Ly = Pb$ by forward substitution and $Ux = y$ by
  backward substitution gives a solution $x$ of $Ax = b$.

Moreover, every matrix $B \in \mathbb{R}^{n \times n}$, singular or not, has a permutation
matrix $P$ and an LU factorization $PB = LU$ with $|l_{ij}| \le 1$.

**Generalization.** The source proves (3.52) for nonsingular $A$, so that a nonzero pivot exists
at every stage. The last statement holds for every square matrix: a zero pivot column is
skipped. The recurrence with partial pivoting produces the factorization whenever its pivots are
nonzero, which is automatic for nonsingular $A$.

The solve is `Matrix.luSolve`. The proof uses `Matrix.gemPivotStage_permMatrix_mul_isLU`,
`Matrix.gemPivotStage_partialPivotRow_norm_gemLower_le_one`, `Matrix.mulVec_luSolve_permMatrix`,
`Matrix.gemPivotStage_partialPivotRow_pivot_ne_zero_of_isUnit` and
`Matrix.exists_permMatrix_mul_isLU`. -/
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

/-- **Section 3.5** of [quarteroni2000numerical], complete pivoting. Let
$A \in \mathbb{R}^{n \times n}$. There exist permutation matrices $P$ (of the rows) and $Q$ (of
the columns) and an LU factorization
$$PAQ = LU,$$
with $L$ unit lower triangular, $U$ upper triangular, $|l_{ij}| \le 1$ for all $i, j$, and
$|u_{ij}| \le |u_{ii}|$ for all $i, j$.

The factorization comes from exchanging, at each stage, the current row and column with those of
an entry of largest modulus in the trailing block. No nonsingularity is needed. The proof
specializes `Matrix.exists_permMatrix_mul_mul_permMatrix_isLU`.

**Reading.** The source describes the maximum-pivot algorithm. This gives an existence
statement for all square matrices, with bounds on the entries of both triangular factors. -/
theorem completePivoting :
    ∃ (σ τ : Equiv.Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) ℝ),
      IsLU (σ.permMatrix ℝ * A * τ.permMatrix ℝ) L U ∧ (∀ i j, |L i j| ≤ 1) ∧
        ∀ i j, |U i j| ≤ |U i i| := by
  obtain ⟨σ, τ, L, U, h, hL, hU⟩ := exists_permMatrix_mul_mul_permMatrix_isLU A
  exact ⟨σ, τ, L, U, h, fun i j => by simpa [Real.norm_eq_abs] using hL i j,
    fun i j => by simpa [Real.norm_eq_abs] using hU i j⟩

/-- **Section 3.5** of [quarteroni2000numerical], the multipliers of pivoted elimination. Let
$A \in \mathbb{R}^{n \times n}$, let $P$ be a permutation matrix, and let $PA = LU$ be an LU
factorization. If the leading principal submatrices of $PA$ of orders $0, \ldots, n - 1$ are
nonsingular (the hypothesis of Theorem 3.4), then $L$ is the multiplier matrix and $U$ is the
last stage of GEM without pivoting on $PA$.

This is the remark of the source that the entries of $L$ coincide with the multipliers computed
by the LU factorization without pivoting, when it is applied to $PA$. The proof uses
`Matrix.IsLU.eq_of_permMatrix_mul`.

**Reading.** The identification of the factors is stated under the nonzero proper leading
minors of the permuted matrix, which ensure uniqueness. -/
theorem pivoting_multipliers {σ : Equiv.Perm (Fin n)} {L U : Matrix (Fin n) (Fin n) ℝ}
    (h : IsLU (σ.permMatrix ℝ * A) L U)
    (hPA : ∀ k, IsUnit ((σ.permMatrix ℝ * A).strictLeadingPrincipalSubmatrix k)) :
    L = gemLower (σ.permMatrix ℝ * A) ∧ U = gemStage (σ.permMatrix ℝ * A) n :=
  h.eq_of_permMatrix_mul hPA

end Pivoted

end QuarteroniSaccoSaleri.Chapter03
