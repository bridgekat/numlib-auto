/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.Kronecker
import NumlibSurface.GolubVanLoan.Chapter03.Section04
import NumlibSurface.GolubVanLoan.Chapter04.Section01

/-!
# Golub and Van Loan, Section 4.2: Positive definite systems

This module formalizes §4.2 of [golub2013matrix]. A matrix $A \in \mathbb{R}^{n \times n}$ is
positive definite if $x^T A x > 0$ for every nonzero $x \in \mathbb{R}^n$; no symmetry is assumed.
Such a matrix is positive definite exactly when its symmetric part $T = (A + A^T)/2$ is (Theorems
4.2.1–4.2.3), it has an LU factorization (Corollary 4.2.4), and Theorem 4.2.6 bounds the growth
$\| |L| |U| \|_F$ of its factors, which gives the backward error (4.2.7) of Gaussian elimination
without pivoting. A symmetric positive definite matrix has a unique Cholesky factorization
$A = GG^T$ (Theorem 4.2.7), and the entries of $G$ are bounded by the diagonal of $A$. A symmetric
positive semidefinite matrix satisfies the entry bounds of Theorem 4.2.8 and has a pivoted
factorization $PAP^T = LDL^T$ that reveals its rank, (4.2.17).

The module defines gaxpy Cholesky (Algorithm 4.2.1), the outer product $LDL^T$ factorization with
diagonal pivoting (Algorithm 4.2.2), and recursive and nonrecursive block Cholesky (Algorithms 4.2.3
and 4.2.4) as programs. It proves a rounding bridge and Wilkinson's backward error bound for
Algorithm 4.2.1, and the exact correctness of all four algorithms, with the invariant (4.2.16) of
Algorithm 4.2.2 and the block equations (4.2.18) and (4.2.19). The proofs specialize
`Numlib.LinearAlgebra.Matrix.HermitianPart`, `Numlib.LinearAlgebra.Matrix.Cholesky`,
`Numlib.Analysis.Matrix.OperatorNorm` and `Numlib.FloatingPoint.LU`.

## Main definitions

* §4.2, `GolubVanLoan.Chapter04.IsPositiveDefinite`: $x^T A x > 0$ for every nonzero $x$, without
  symmetry.
* Theorem 4.2.5, `GolubVanLoan.Chapter04.blockPD`: the matrix $\begin{bmatrix} \alpha & v^T \\ v & B
  \end{bmatrix} + \begin{bmatrix} 0 & -w^T \\ w & C \end{bmatrix}$ of the theorem.
* Algorithm 4.2.1, `GolubVanLoan.Chapter04.algorithm_4_2_1`: gaxpy Cholesky.
* §4.2.6, `GolubVanLoan.Chapter04.solveCholesky`: the two triangular solves with the computed
  Cholesky factor.
* Algorithm 4.2.2, `GolubVanLoan.Chapter04.algorithm_4_2_2`: outer product $LDL^T$ with diagonal
  pivoting, with its pivot `GolubVanLoan.Chapter04.diagPivot` and its step
  `GolubVanLoan.Chapter04.ldltPivotStep`.
* (4.2.16), `GolubVanLoan.Chapter04.pivotedLower` and `GolubVanLoan.Chapter04.pivotedMiddle`: the
  factors $L_k$ and $\operatorname{diag}(D_k, A_k)$ after $k$ steps of Algorithm 4.2.2, and
  `GolubVanLoan.Chapter04.pivotElim`, one exact elimination step.
* Algorithm 4.2.3, `GolubVanLoan.Chapter04.algorithm_4_2_3`: recursive block Cholesky, with its
  parts `GolubVanLoan.Chapter04.choleskyLower`, `GolubVanLoan.Chapter04.solveRowsLower` and
  `GolubVanLoan.Chapter04.mulTransposeDiff`.
* (4.2.19), `GolubVanLoan.Chapter04.blockOf` and `GolubVanLoan.Chapter04.updateBlock`: reading and
  overwriting the block $A_{ij}$.
* Algorithm 4.2.4, `GolubVanLoan.Chapter04.algorithm_4_2_4`: nonrecursive block Cholesky, with its
  step `GolubVanLoan.Chapter04.blockCholeskyStep`.

## Main results

* §4.2.2, `GolubVanLoan.Chapter04.isPositiveDefinite_iff`: $A$ is positive definite if and only if
  $T = (A + A^T)/2$ is symmetric positive definite.
* Theorem 4.2.1, `GolubVanLoan.Chapter04.theorem_4_2_1`: if $A$ is positive definite and $X$ has
  full column rank, then $X^T A X$ is positive definite.
* Corollary 4.2.2, `GolubVanLoan.Chapter04.corollary_4_2_2`: the principal submatrices of a positive
  definite matrix are positive definite, and its diagonal is positive.
* Theorem 4.2.3, `GolubVanLoan.Chapter04.theorem_4_2_3`: $A$ is positive definite if and only if $T$
  has positive eigenvalues.
* Corollary 4.2.4, `GolubVanLoan.Chapter04.corollary_4_2_4`: a positive definite matrix has an LU
  factorization, and the diagonal of $U$ is positive.
* Theorem 4.2.5, `GolubVanLoan.Chapter04.theorem_4_2_5`: one step of elimination on a positive
  definite matrix, (4.2.1)–(4.2.3).
* Theorem 4.2.6, `GolubVanLoan.Chapter04.theorem_4_2_6`: $\| |L| |U| \|_F \le n (\|T\|_2 + \|S
  T^{-1} S\|_2)$.
* (4.2.7), `GolubVanLoan.Chapter04.equation_4_2_7`: the backward error of Gaussian elimination
  without pivoting on a positive definite matrix.
* §4.2.2, `GolubVanLoan.Chapter04.l2_opNorm_symmPart_le`: $\|T\|_2 \le \|A\|_2$.
* Theorem 4.2.7, `GolubVanLoan.Chapter04.theorem_4_2_7`: existence and uniqueness of the Cholesky
  factorization.
* (4.2.9), `GolubVanLoan.Chapter04.equation_4_2_9`: the column equations of $A = GG^T$.
* Algorithm 4.2.1, `GolubVanLoan.Chapter04.algorithm_4_2_1_rounds`,
  `GolubVanLoan.Chapter04.algorithm_4_2_1_run_nonempty` and
  `GolubVanLoan.Chapter04.algorithm_4_2_1_spec`: every run with a nonzero diagonal is a computed
  Cholesky factorization, the runs exist over a total rounding model, and the exact run is the
  Cholesky factor.
* §4.2.6, `GolubVanLoan.Chapter04.cholesky_entry_bound`: $g_{ij}^2 \le a_{ii}$.
* §4.2.6, `GolubVanLoan.Chapter04.l2_opNorm_cholesky_sq`: $\|G\|_2^2 = \|A\|_2$.
* §4.2.6, `GolubVanLoan.Chapter04.condNumber_eq_div_eigenvalues`: $\kappa_2(A) = \lambda_{\max}(A) /
  \lambda_{\min}(A)$.
* §4.2.6, `GolubVanLoan.Chapter04.cholesky_backward_error`: Wilkinson's backward error bound for the
  solution computed through Algorithm 4.2.1.
* (4.2.10), `GolubVanLoan.Chapter04.equation_4_2_10`: $PAP^T = LDL^T$ with
  $d_1 \ge \dots \ge d_n > 0$ for a symmetric positive definite $A$.
* (4.2.11), `GolubVanLoan.Chapter04.equation_4_2_11`: a symmetric positive semidefinite matrix of
  rank $r$ has nonnegative eigenvalues, exactly $r$ of them nonzero.
* Theorem 4.2.8, `GolubVanLoan.Chapter04.theorem_4_2_8`: the bounds (4.2.12)–(4.2.15) on the entries
  of a symmetric positive semidefinite matrix, also stated one by one in
  `GolubVanLoan.Chapter04.theorem_4_2_8_a`, `GolubVanLoan.Chapter04.theorem_4_2_8_b`,
  `GolubVanLoan.Chapter04.theorem_4_2_8_c` and `GolubVanLoan.Chapter04.theorem_4_2_8_d`.
* (4.2.16), `GolubVanLoan.Chapter04.equation_4_2_16`: the factorization of the state after $k$ steps
  of Algorithm 4.2.2.
* Algorithm 4.2.2, `GolubVanLoan.Chapter04.algorithm_4_2_2_spec`: the exact run gives
  $PAP^T = LDL^T$ with a nonnegative, nonincreasing diagonal $D$.
* (4.2.17), `GolubVanLoan.Chapter04.equation_4_2_17`, `GolubVanLoan.Chapter04.equation_4_2_17_sum`
  and `GolubVanLoan.Chapter04.equation_4_2_17_algorithm`: the rank-revealing factorization of a
  symmetric positive semidefinite matrix, its rank-one expansion, and its computation by Algorithm
  4.2.2.
* (4.2.18), `GolubVanLoan.Chapter04.equation_4_2_18`: the $2 \times 2$ block equations of the
  Cholesky factorization.
* Algorithm 4.2.3, `GolubVanLoan.Chapter04.algorithm_4_2_3_spec`: the exact run is the Cholesky
  factor.
* (4.2.19), `GolubVanLoan.Chapter04.equation_4_2_19`: the $N \times N$ block equations of the
  Cholesky factorization.
* Algorithm 4.2.4, `GolubVanLoan.Chapter04.algorithm_4_2_4_spec`: the lower triangle of the exact
  run is the Cholesky factor.

## Conventions

* Matrices are real and indexed by `Fin n`, so indices are 0-based.
* "Positive definite" for a general matrix is `GolubVanLoan.Chapter04.IsPositiveDefinite`.
  "Symmetric positive definite" and "symmetric positive semidefinite" are Mathlib's `Matrix.PosDef`
  and `Matrix.PosSemidef`. The symmetric part $T = (A + A^T)/2$ is `Matrix.hermitianPart A`.
* The lower Cholesky factor $G$ of the source is `Matrix.cholesky A`. Its transpose is the upper
  factor of `Matrix.IsCholesky`.
* The norm $\|\cdot\|_2$ is `Matrix.lpOpNorm 2`.
* The condition number $\kappa_2$ is `Matrix.condNumberLp 2`.
* The matrix $|A|$ of absolute values is `Matrix.abs A`.
* For a permutation $\sigma$ with permutation matrix $P$, the matrix $PAP^T$ is `A.submatrix σ σ`.

## Implementation notes

* Algorithm 4.2.1 follows the algorithm conventions of `NumlibSurface.GolubVanLoan`. The gaxpy
  $A(j{:}n, j) - A(j{:}n, 1{:}j-1) A(j, 1{:}j-1)^T$ is a running difference from the entry of $A$
  (`FloatingPoint.runningDiff`). The square root is `Real.sqrt` followed by one rounding, and the
  whole column, diagonal included, is divided by the rounded square root. So the computed diagonal
  is $\mathrm{fl}(t / \mathrm{fl}(\sqrt t))$, the operation order of the backbone relation
  `FloatingPoint.RoundsCholeskyDiv`.
* In exact arithmetic, Algorithm 4.2.1 computes the backbone recurrence `Matrix.cholesky` for every
  input. Off the positive definite cone both compute the same values, because the square root of a
  negative number is $0$ and $x / 0 = 0$.
* The triangular solves call the column-oriented substitutions of Chapter 3, Algorithms 3.1.3 and
  3.1.4.
* The block algorithms store the lower triangle of the output of Algorithm 4.2.1
  (`GolubVanLoan.Chapter04.choleskyLower`), solve $XG^T = B$ row by row
  (`GolubVanLoan.Chapter04.solveRowsLower`), and form the updates $A_{22} - G_{21} G_{21}^T$ and
  $A_{ij} - \sum_{k<j} G_{ik} G_{jk}^T$ by running differences
  (`GolubVanLoan.Chapter04.mulTransposeDiff`). Their exact specifications compare the blocks with
  (4.2.18) and (4.2.19).
* The exact specification of Algorithm 4.2.2 writes the state after $k$ steps as
  $L_k \operatorname{diag}(D_k, A_k) L_k^T$. One step is a symmetric interchange, which commutes
  with both factors because the pivot is at or after $k$, followed by a congruence with the column
  operator of the multipliers.

## Deviations from the source

* **(4.2.7)** (generalization). The source prints a first-order bound with the extra term
  $2n \|A\|_F$. The library proves the rigorous bound $\|E\|_F \le \gamma_{3n} c n (\|T\|_2 + \|S
  T^{-1} S\|_2)$. See `GolubVanLoan.Chapter04.equation_4_2_7`.
* **Theorem 4.2.8, (4.2.13)** (generalization). The source states
  $|a_{ij}| \le \sqrt{a_{ii} a_{jj}}$ for $i \neq j$. The library states it for all $i, j$. See
  `GolubVanLoan.Chapter04.theorem_4_2_8_b`.
* **Algorithm 4.2.2** (correction). The source gives $d_n > 0$ for a semidefinite input. For a
  singular $A$ the computed $d_n$ is $0$; the library states $d_i \ge 0$, and $d_i > 0$ when $A$ is
  positive definite. See `GolubVanLoan.Chapter04.algorithm_4_2_2_spec`.
* **Algorithm 4.2.2** (reading). The source writes $P = P_1 \cdots P_n$. The library takes the
  product of the interchanges in the order in which they are applied. See
  `GolubVanLoan.Chapter04.algorithm_4_2_2_spec`.

## Not formalized

* **§4.2.4, matrix square roots.** They are the subject of Chapter 9.
* **§4.2.10, packed formats.**
* **Flop counts.**
* **The numerical example with the matrix $\begin{bmatrix} \epsilon & m \\ -m & \epsilon
  \end{bmatrix}$.**
* **Wilkinson's completion criterion $q_n u \kappa_2(A) \le 1$ (§4.2.6).** The source quotes it
  without derivation.
* **The numerical-rank threshold of §4.2.8.** The source quotes it without derivation.
-/

open FloatingPoint Matrix Finset

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### §4.2.1–4.2.2 Positive definiteness of a general matrix -/

/-- **Section 4.2** of [golub2013matrix], definition of a positive definite matrix. A matrix
$A \in \mathbb{R}^{n \times n}$ is **positive definite** if
$$x^T A x > 0 \quad \text{for all nonzero } x \in \mathbb{R}^n.$$
No symmetry is assumed.

The index type is any finite type. For a symmetric matrix the predicate is Mathlib's
`Matrix.PosDef` (`GolubVanLoan.Chapter04.isPositiveDefinite_iff_posDef`). -/
def IsPositiveDefinite {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

/-- **Section 4.2.2** of [golub2013matrix]. A matrix $A \in \mathbb{R}^{n \times n}$ is positive
definite if and only if its symmetric part $T = (A + A^T)/2$ is symmetric positive definite: the
positive definiteness of a general matrix is inherited from its symmetric part.

The reason is that $x^T S x = 0$ for the skew-symmetric part $S = (A - A^T)/2$. The matrix $T$
is `Matrix.hermitianPart A`, and "symmetric positive definite" is `Matrix.PosDef`. The index
type is any finite type. -/
theorem isPositiveDefinite_iff {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    IsPositiveDefinite A ↔ (hermitianPart A).PosDef := by
  rw [posDef_hermitianPart_iff_forall_dotProduct_mulVec_pos]
  simp [IsPositiveDefinite]

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric. Then $A$ is positive definite in the sense of
`GolubVanLoan.Chapter04.IsPositiveDefinite` if and only if it is positive definite in the sense
of Mathlib's `Matrix.PosDef`. -/
theorem isPositiveDefinite_iff_posDef {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) : IsPositiveDefinite A ↔ A.PosDef := by
  have h : hermitianPart A = A := by
    ext i j
    simp only [hermitianPart_apply, starRingEnd_apply, star_trivial, hA.apply i j]
    ring
  rw [isPositiveDefinite_iff, h]

/-- **Theorem 4.2.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite
and let $X \in \mathbb{R}^{n \times k}$ have rank $k$. Then
$B = X^T A X \in \mathbb{R}^{k \times k}$ is positive definite. -/
theorem theorem_4_2_1 {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsPositiveDefinite A)
    {X : Matrix (Fin n) (Fin k) ℝ} (hX : X.rank = k) : IsPositiveDefinite (Xᵀ * A * X) := by
  have hinj : Function.Injective X.mulVec := by
    have h1 := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank ℝ (LinearMap.ker X.mulVecLin) = 0 := by
      have : X.rank = Module.finrank ℝ (LinearMap.range X.mulVecLin) := rfl
      omega
    rw [Submodule.finrank_eq_zero, LinearMap.ker_eq_bot, coe_mulVecLin] at h2
    exact h2
  intro z hz
  have hXz : X *ᵥ z ≠ 0 := fun h => hz (hinj (by rw [h, mulVec_zero]))
  have := hA _ hXz
  rwa [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- **Corollary 4.2.2** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite. Then all principal submatrices of $A$ are positive definite. In particular, all
diagonal entries of $A$ are positive.

A principal submatrix $A(v, v)$ is `A.submatrix e e` for an injective map `e : Fin k → Fin n`. -/
theorem corollary_4_2_2 {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsPositiveDefinite A)
    {e : Fin k → Fin n} (he : Function.Injective e) :
    IsPositiveDefinite (A.submatrix e e) ∧ ∀ i, 0 < A i i := by
  refine ⟨?_, fun i => ?_⟩
  · rw [isPositiveDefinite_iff, hermitianPart_submatrix]
    exact ((isPositiveDefinite_iff A).1 hA).submatrix he
  · have := hA (Pi.single i 1) (by simp)
    simpa [mulVec, dotProduct, Pi.single_apply] using this

/-- **Theorem 4.2.3** of [golub2013matrix]. A matrix $A \in \mathbb{R}^{n \times n}$ is positive
definite if and only if all eigenvalues of the symmetric matrix $T = (A + A^T)/2$ are positive.

The eigenvalues are `Matrix.IsHermitian.eigenvalues` of `Matrix.hermitianPart A`. -/
theorem theorem_4_2_3 (A : Matrix (Fin n) (Fin n) ℝ) :
    IsPositiveDefinite A ↔ ∀ i, 0 < (hermitianPart_isHermitian A).eigenvalues i :=
  (isPositiveDefinite_iff A).trans (hermitianPart_isHermitian A).posDef_iff_eigenvalues_pos

/-- **Corollary 4.2.4** of [golub2013matrix]. If $A \in \mathbb{R}^{n \times n}$ is positive
definite, then it has an LU factorization $A = LU$, with $L$ unit lower triangular and $U$ upper
triangular, and the diagonal entries of $U$ are positive.

The factorization is `Matrix.IsLU A L U`. -/
theorem corollary_4_2_4 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsPositiveDefinite A) :
    ∃ L U, IsLU A L U ∧ ∀ i, 0 < U i i := by
  simpa using exists_isLU_of_posDef_hermitianPart ((isPositiveDefinite_iff A).1 hA)

/-- If $M \in \mathbb{R}^{n \times n}$ satisfies $M^T = -M$, then $x^T M x = 0$ for every $x$. -/
private theorem dotProduct_mulVec_eq_zero_of_transpose_eq_neg {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℝ} (hM : Mᵀ = -M) (x : ι → ℝ) : x ⬝ᵥ (M *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (M *ᵥ x) = -(x ⬝ᵥ (M *ᵥ x)) := by
    conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hM, neg_mulVec, neg_dotProduct,
      dotProduct_comm]
  linarith

/-- For $a, b, z \in \mathbb{R}^n$, the quadratic form of the rank-one matrix $ab^T$ is
$z^T (ab^T) z = (z^T a)(b^T z)$. -/
private theorem dotProduct_vecMulVec_mulVec (a b z : Fin n → ℝ) :
    z ⬝ᵥ (vecMulVec a b *ᵥ z) = (z ⬝ᵥ a) * (b ⬝ᵥ z) := by
  rw [dotProduct, dotProduct, dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [vecMulVec_apply]; ring

/-- The matrix of Theorem 4.2.5 of [golub2013matrix]. For $\alpha \in \mathbb{R}$,
$v, w \in \mathbb{R}^n$ and $B, C \in \mathbb{R}^{n \times n}$, it is
$$A = \begin{bmatrix} \alpha & v^T \\ v & B \end{bmatrix} + \begin{bmatrix} 0 & -w^T \\ w & C
  \end{bmatrix} \in \mathbb{R}^{(1+n) \times (1+n)}.$$
The matrix is indexed by `Fin 1 ⊕ Fin n`. -/
abbrev blockPD (α : ℝ) (v w : Fin n → ℝ) (B C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
  fromBlocks (of fun _ _ => α) (replicateRow (Fin 1) v) (replicateCol (Fin 1) v) B +
    fromBlocks 0 (-replicateRow (Fin 1) w) (replicateCol (Fin 1) w) C

/-- If $C^T = -C$, then the quadratic form of the matrix of Theorem 4.2.5 at the vector $(\mu, z)$
is $\mu^2 \alpha + 2 \mu v^T z + z^T B z$: the skew-symmetric part contributes nothing. -/
private theorem quad_blockPD {α μ : ℝ} {v w z : Fin n → ℝ} {B C : Matrix (Fin n) (Fin n) ℝ}
    (hC : Cᵀ = -C) :
    Sum.elim (fun _ : Fin 1 => μ) z ⬝ᵥ (blockPD α v w B C *ᵥ Sum.elim (fun _ => μ) z) =
      μ * μ * α + 2 * μ * (v ⬝ᵥ z) + z ⬝ᵥ (B *ᵥ z) := by
  have hskew : (fromBlocks 0 (-replicateRow (Fin 1) w) (replicateCol (Fin 1) w) C)ᵀ =
      -fromBlocks 0 (-replicateRow (Fin 1) w) (replicateCol (Fin 1) w) C := by
    rw [fromBlocks_transpose, fromBlocks_neg, transpose_replicateCol, transpose_neg,
      transpose_replicateRow, hC]
    simp
  rw [blockPD, add_mulVec, dotProduct_add, dotProduct_mulVec_eq_zero_of_transpose_eq_neg hskew,
    add_zero, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  have h1 : (replicateRow (Fin 1) v *ᵥ z) = fun _ => v ⬝ᵥ z := rfl
  have h2 : (replicateCol (Fin 1) v *ᵥ fun _ : Fin 1 => μ) = μ • v := by
    ext i; simp [mulVec, dotProduct, mul_comm]
  have e1 : (fun _ : Fin 1 => μ) ⬝ᵥ ((of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
      fun _ => μ) = μ * μ * α := by
    simp [dotProduct, mulVec]; ring
  have e2 : (fun _ : Fin 1 => μ) ⬝ᵥ (fun _ => v ⬝ᵥ z) = μ * (v ⬝ᵥ z) := by simp [dotProduct]
  rw [h1, h2, dotProduct_add, e1, e2]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm z v]
  ring

/-- **Theorem 4.2.5** of [golub2013matrix], with (4.2.1)–(4.2.3). Let $\alpha \in \mathbb{R}$ and
$v, w \in \mathbb{R}^n$, let $B \in \mathbb{R}^{n \times n}$ be symmetric and
$C \in \mathbb{R}^{n \times n}$ skew-symmetric, and suppose that
$$A = \begin{bmatrix} \alpha & v^T \\ v & B \end{bmatrix} + \begin{bmatrix} 0 & -w^T \\ w & C
  \end{bmatrix}$$
is positive definite. Then
$$A = \begin{bmatrix} 1 & 0 \\ (v + w)/\alpha & I_n \end{bmatrix} \begin{bmatrix} \alpha & (v -
  w)^T \\ 0 & B_1 + C_1 \end{bmatrix}, \qquad (4.2.1)$$
where
$$B_1 = B - \frac{1}{\alpha}(vv^T - ww^T) \qquad (4.2.2)$$
is symmetric positive definite and
$$C_1 = C - \frac{1}{\alpha}(wv^T - vw^T) \qquad (4.2.3)$$
is skew-symmetric.

The matrix $A$ is `GolubVanLoan.Chapter04.blockPD`, indexed by `Fin 1 ⊕ Fin n`. Since $A$ is
positive definite, $\alpha > 0$. -/
theorem theorem_4_2_5 {α : ℝ} {v w : Fin n → ℝ} {B C : Matrix (Fin n) (Fin n) ℝ} (hB : Bᵀ = B)
    (hC : Cᵀ = -C) (hA : IsPositiveDefinite (blockPD α v w B C)) :
    blockPD α v w B C =
      fromBlocks 1 0 (replicateCol (Fin 1) (α⁻¹ • (v + w))) 1 *
        fromBlocks (of fun _ _ => α) (replicateRow (Fin 1) (v - w)) 0
          ((B - α⁻¹ • (vecMulVec v v - vecMulVec w w)) +
            (C - α⁻¹ • (vecMulVec w v - vecMulVec v w))) ∧
      (B - α⁻¹ • (vecMulVec v v - vecMulVec w w)).PosDef ∧
      (C - α⁻¹ • (vecMulVec w v - vecMulVec v w))ᵀ =
        -(C - α⁻¹ • (vecMulVec w v - vecMulVec v w)) := by
  -- `α > 0`: the quadratic form at `e₁`
  have hα : 0 < α := by
    have := hA (Sum.elim (fun _ => 1) 0) (fun h => by simpa using congrFun h (Sum.inl 0))
    rw [quad_blockPD hC] at this
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rw [blockPD, fromBlocks_add, fromBlocks_multiply]
    congr 1
    · ext i j; simp
    · ext i j; simp; ring
    · ext i j
      simp only [Matrix.add_apply, Matrix.mul_zero, Matrix.zero_apply, add_zero, Matrix.mul_apply,
        Fin.sum_univ_one, replicateCol_apply, of_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      field_simp
    · ext i j
      simp [Matrix.mul_apply, vecMulVec_apply]
      field_simp
      ring
  · rw [posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun z hz => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_sub, transpose_vecMulVec, transpose_vecMulVec, hB]
    · simp only [star_trivial]
      have hq := hA (Sum.elim (fun _ => -(v ⬝ᵥ z) / α) z)
        (fun h => hz (funext fun i => by simpa using congrFun h (Sum.inr i)))
      rw [quad_blockPD hC] at hq
      have hw : 0 ≤ (w ⬝ᵥ z) * (w ⬝ᵥ z) / α := div_nonneg (mul_self_nonneg _) hα.le
      have key : z ⬝ᵥ ((B - α⁻¹ • (vecMulVec v v - vecMulVec w w)) *ᵥ z) =
          z ⬝ᵥ (B *ᵥ z) - (v ⬝ᵥ z) * (v ⬝ᵥ z) / α + (w ⬝ᵥ z) * (w ⬝ᵥ z) / α := by
        rw [sub_mulVec, smul_mulVec, sub_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_sub,
          dotProduct_vecMulVec_mulVec, dotProduct_vecMulVec_mulVec, smul_eq_mul,
          dotProduct_comm z v, dotProduct_comm z w]
        field_simp
        ring
      rw [key]
      have : -(v ⬝ᵥ z) / α * (-(v ⬝ᵥ z) / α) * α + 2 * (-(v ⬝ᵥ z) / α) * (v ⬝ᵥ z) =
          -((v ⬝ᵥ z) * (v ⬝ᵥ z) / α) := by
        field_simp
        ring
      linarith
  · rw [transpose_sub, transpose_smul, transpose_sub, transpose_vecMulVec, transpose_vecMulVec,
      hC]
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- The matrix $(A + A^T)/2$ is `Matrix.hermitianPart A`. -/
private theorem half_add_transpose_eq_hermitianPart (A : Matrix (Fin n) (Fin n) ℝ) :
    (2 : ℝ)⁻¹ • (A + Aᵀ) = hermitianPart A := by
  rw [hermitianPart, conjTranspose_eq_transpose_of_trivial]

/-- The matrix $(A - A^T)/2$ is $A - T$, where $T$ is `Matrix.hermitianPart A`. -/
private theorem half_sub_transpose_eq_sub_hermitianPart (A : Matrix (Fin n) (Fin n) ℝ) :
    (2 : ℝ)⁻¹ • (A - Aᵀ) = A - hermitianPart A := by
  rw [hermitianPart, conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  ring

open scoped Matrix.Norms.Frobenius in
/-- **Theorem 4.2.6** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, and set $T = (A + A^T)/2$ and $S = (A - A^T)/2$. If $A = LU$ is an LU factorization of
$A$, then
$$\| |L| |U| \|_F \le n \left( \|T\|_2 + \|S T^{-1} S\|_2 \right). \qquad (4.2.5)$$

The source refers to Golub and Van Loan (1979) for the proof. The proof here applies
`Matrix.IsLU.frobenius_norm_abs_mul_abs_le`, which bounds each rank-one term $|\ell_k| |u_k^T|$
through $A T^{-1} A^T = T - S T^{-1} S$. The norm $\|\cdot\|_2$ is `Matrix.lpOpNorm 2`, and the
Frobenius norm is the scoped norm of `Matrix.Norms.Frobenius`. -/
theorem theorem_4_2_6 {A L U T S : Matrix (Fin n) (Fin n) ℝ} (hA : IsPositiveDefinite A)
    (hT : T = (2 : ℝ)⁻¹ • (A + Aᵀ)) (hS : S = (2 : ℝ)⁻¹ • (A - Aᵀ)) (h : IsLU A L U) :
    ‖L.abs * U.abs‖ ≤ n * (lpOpNorm 2 T + lpOpNorm 2 (S * T⁻¹ * S)) := by
  rw [hT, hS, half_add_transpose_eq_hermitianPart, half_sub_transpose_eq_sub_hermitianPart,
    lpOpNorm_two, lpOpNorm_two]
  have := IsLU.frobenius_norm_abs_mul_abs_le ((isPositiveDefinite_iff A).1 hA) h
  rw [Fintype.card_fin] at this
  exact this

open scoped Matrix.Norms.Frobenius in
/-- **Equation (4.2.7)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, let $T = (A + A^T)/2$ and $S = (A - A^T)/2$, and let $A = LU$ be an LU factorization
of $A$. Let the unit roundoff $u$ satisfy $u < 1$ and $3nu < 1$. Let $\hat L$ and $\hat U$ be
computed LU factors of $A$ whose diagonal entries $\hat u_{jj}$ are nonzero, let $\hat y$ be
computed from $\hat L y = b$ by forward substitution, and let $\hat x$ be computed from
$\hat U x = \hat y$ by back substitution. If $c \ge 0$ and
$$\| |\hat L| |\hat U| \|_F \le c \, \| |L| |U| \|_F, \qquad (4.2.6)$$
then there is $E \in \mathbb{R}^{n \times n}$ with
$$(A + E) \hat x = b, \qquad \|E\|_F \le \gamma_{3n} \, c \, n \left( \|T\|_2 + \|S T^{-1} S\|_2
  \right).$$

**Generalization.** The source assumes (4.2.6) with a constant $c$ of modest size and prints the
first-order bound $\|E\|_F \le u \left( 2n \|A\|_F + 4cn^2 (\|T\|_2 + \|S T^{-1} S\|_2)
\right) + O(u^2)$, which it derives from (4.2.1) and the analysis of §3.3. The bound here is
rigorous and does not need the term $2n \|A\|_F$. It implies the printed bound, because
$\gamma_{3n} \le 4nu$ when $3nu \le 1/4$.

The computed factors and the two solves are the relations `FloatingPoint.RoundsLU`,
`FloatingPoint.RoundsForwardSubst` and `FloatingPoint.RoundsBackSubst`, and the primed names
`L'`, `U'` and `x'` stand for $\hat L$, $\hat U$ and $\hat x$. The proof combines
$|E| \le \gamma_{3n} |\hat L| |\hat U|$ (`FloatingPoint.exists_roundsLU_solve_eq`) with Theorem
4.2.6. -/
theorem equation_4_2_7 {fp : RoundingModel ℝ} {A L U L' U' T S : Matrix (Fin n) (Fin n) ℝ}
    {b y x' : Fin n → ℝ} {c : ℝ} (hA : IsPositiveDefinite A) (hT : T = (2 : ℝ)⁻¹ • (A + Aᵀ))
    (hS : S = (2 : ℝ)⁻¹ • (A - Aᵀ)) (h : IsLU A L U) (hu : fp.u < 1)
    (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1) (hLU : RoundsLU fp A L' U') (hd : ∀ j, U' j j ≠ 0)
    (hy : RoundsForwardSubst fp L' b y) (hx : RoundsBackSubst fp U' y x') (hc0 : 0 ≤ c)
    (hc : ‖L'.abs * U'.abs‖ ≤ c * ‖L.abs * U.abs‖) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x' = b ∧
      ‖E‖ ≤ gamma fp.u (3 * n) * (c * (n * (lpOpNorm 2 T + lpOpNorm 2 (S * T⁻¹ * S)))) := by
  obtain ⟨E, hE, hEx⟩ := exists_roundsLU_solve_eq hu (by simpa using hn) hLU hd hy hx
  rw [Fintype.card_fin] at hE
  have hγ : 0 ≤ gamma fp.u (3 * n) := gamma_nonneg fp.u_nonneg hn
  refine ⟨E, hEx, ?_⟩
  calc ‖E‖ ≤ ‖gamma fp.u (3 * n) • (L'.abs * U'.abs)‖ :=
        frobenius_norm_le_of_abs_entrywiseLE
          (hE.trans fun i j => le_abs_self ((gamma fp.u (3 * n) • (L'.abs * U'.abs)) i j))
    _ = gamma fp.u (3 * n) * ‖L'.abs * U'.abs‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    _ ≤ gamma fp.u (3 * n) * (c * ‖L.abs * U.abs‖) := mul_le_mul_of_nonneg_left hc hγ
    _ ≤ _ := by
        gcongr
        exact theorem_4_2_6 hA hT hS h

/-! ### §4.2.3–4.2.6 The Cholesky factorization -/

/-- **Section 4.2.2** of [golub2013matrix], the remark before (4.2.8). For
$A \in \mathbb{R}^{n \times n}$, the symmetric part $T = (A + A^T)/2$ satisfies
$$\|T\|_2 \le \|A\|_2.$$

The source says that this is easy to show. The matrix $T$ is `Matrix.hermitianPart A`. -/
theorem l2_opNorm_symmPart_le (A : Matrix (Fin n) (Fin n) ℝ) :
    lpOpNorm 2 (hermitianPart A) ≤ lpOpNorm 2 A := by
  rw [lpOpNorm_two, lpOpNorm_two]
  exact l2_opNorm_hermitianPart_le A

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. Then its lower triangular
Cholesky factor $G$, which is `Matrix.cholesky A`, satisfies $GG^T = A$. -/
theorem cholesky_mul_transpose {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    cholesky A * (cholesky A)ᵀ = A := by
  simpa [conjTranspose_eq_transpose_of_trivial] using
    (isCholesky_cholesky hA).conjTranspose_mul_self

/-- If $A \in \mathbb{R}^{n \times n}$ is symmetric positive definite, then every diagonal entry of
its Cholesky factor `Matrix.cholesky A` is positive. -/
theorem cholesky_diag_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (i : Fin n) :
    0 < cholesky A i i := by
  simpa [conjTranspose_eq_transpose_of_trivial] using (isCholesky_cholesky hA).diag_pos i

/-- **Theorem 4.2.7** of [golub2013matrix] (Cholesky factorization). If
$A \in \mathbb{R}^{n \times n}$ is symmetric positive definite, then there is a unique lower
triangular $G \in \mathbb{R}^{n \times n}$ with positive diagonal entries such that $A = GG^T$.
This matrix is `Matrix.cholesky A`: it is lower triangular, its diagonal entries are positive,
and $A = GG^T$. -/
theorem theorem_4_2_7 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (∃! G : Matrix (Fin n) (Fin n) ℝ, G.IsLowerTriangular ∧ (∀ i, 0 < G i i) ∧ A = G * Gᵀ) ∧
      (cholesky A).IsLowerTriangular ∧ (∀ i, 0 < cholesky A i i) ∧
        A = cholesky A * (cholesky A)ᵀ := by
  have hc : (cholesky A).IsLowerTriangular ∧ (∀ i, 0 < cholesky A i i) ∧
      A = cholesky A * (cholesky A)ᵀ :=
    ⟨isLowerTriangular_cholesky A, cholesky_diag_pos hA, (cholesky_mul_transpose hA).symm⟩
  refine ⟨⟨cholesky A, hc, fun G ⟨hG, hd, hGG⟩ => ?_⟩, hc⟩
  have h : IsCholesky A Gᵀ := by
    refine ⟨fun i j hij => hG (OrderDual.toDual_lt_toDual.2 hij), fun i => hd i, ?_⟩
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, hGG]
  rw [cholesky_eq_of_isCholesky h, conjTranspose_eq_transpose_of_trivial, transpose_transpose]

/-- **Equation (4.2.9)** of [golub2013matrix]. Let $A, G \in \mathbb{R}^{n \times n}$, with $G$
lower triangular and $A = GG^T$. Then for every column index $j$,
$$G(j, j) \, G(:, j) = A(:, j) - \sum_{k < j} G(j, k) \, G(:, k).$$

The source obtains this equation by comparing the $j$th columns in $A = GG^T$. -/
theorem equation_4_2_9 {A G : Matrix (Fin n) (Fin n) ℝ} (hG : G.IsLowerTriangular)
    (hA : A = G * Gᵀ) (j : Fin n) :
    G j j • (fun i => G i j) =
      (fun i => A i j) - ∑ k ∈ univ.filter (· < j), G j k • fun i => G i k := by
  ext i
  have hsum : A i j = ∑ k ∈ univ.filter (· ≤ j), G i k * G j k := by
    rw [hA, Matrix.mul_apply]
    refine (Finset.sum_subset (filter_subset _ _) fun k _ hk => ?_).symm
    have hjk : j < k := not_le.1 fun h => hk (mem_filter.2 ⟨mem_univ _, h⟩)
    rw [transpose_apply, hG (OrderDual.toDual_lt_toDual.2 hjk), mul_zero]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply]
  rw [hsum, sum_filter_le_eq_add]
  have : ∑ k ∈ univ.filter (· < j), G j k * G i k = ∑ k ∈ univ.filter (· < j), G i k * G j k :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this]
  ring

/-- **Section 4.2.6** of [golub2013matrix], the bound on the entries of the Cholesky factor. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let $G$ be its Cholesky
factor. Then for all $i$ and $j$,
$$g_{ij}^2 \le \sum_{k \le i} g_{ik}^2 = a_{ii}.$$

The source says that the entries in the Cholesky triangle are nicely bounded. The Lean statement
gives $g_{ij}^2 \le a_{ii}$ and $\sum_{k \le i} g_{ik}^2 = a_{ii}$ separately, with $G$ =
`Matrix.cholesky A`. -/
theorem cholesky_entry_bound {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (i j : Fin n) :
    cholesky A i j ^ 2 ≤ A i i ∧
      ∑ k ∈ univ.filter (· ≤ i), cholesky A i k ^ 2 = A i i := by
  refine ⟨by simpa [Real.norm_eq_abs, sq_abs] using sq_norm_cholesky_apply_le hA i j, ?_⟩
  conv_rhs => rw [← cholesky_mul_transpose hA]
  rw [Matrix.mul_apply]
  refine Eq.trans ?_ (Finset.sum_subset (filter_subset (· ≤ i) univ) ?_)
  · exact Finset.sum_congr rfl fun k _ => by rw [transpose_apply, sq]
  · intro k _ hk
    have hik : i < k := not_le.1 fun h => hk (mem_filter.2 ⟨mem_univ _, h⟩)
    rw [isLowerTriangular_cholesky A (OrderDual.toDual_lt_toDual.2 hik), zero_mul]

/-- **Section 4.2.6** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite and let $G$ be its Cholesky factor. Then
$$\|G\|_2^2 = \|A\|_2.$$

The source says that the bound on the entries of $G$ can also be reached from this equation. -/
theorem l2_opNorm_cholesky_sq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    lpOpNorm 2 (cholesky A) ^ 2 = lpOpNorm 2 A := by
  rw [lpOpNorm_two, lpOpNorm_two]
  exact Matrix.l2_opNorm_cholesky_sq hA

open scoped Matrix.Norms.L2Operator in
/-- **Section 4.2.6** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, with $n \ge 1$. Then
$$\kappa_2(A) = \frac{\lambda_{\max}(A)}{\lambda_{\min}(A)}.$$

The condition number is `Matrix.condNumberLp 2 A`. The numbers $\lambda_{\max}(A)$ and
$\lambda_{\min}(A)$ are the supremum and the infimum of `Matrix.IsHermitian.eigenvalues`. -/
theorem condNumber_eq_div_eigenvalues [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    condNumberLp 2 A = (⨆ i, hA.1.eigenvalues i) / ⨅ i, hA.1.eigenvalues i := by
  rw [← hA.condNumber_l2_eq_div_eigenvalues, condNumberLp, lpOpNorm_two, lpOpNorm_two,
    NormedRing.condNumber, nonsing_inv_eq_ringInverse]

/-! ### Algorithm 4.2.1: gaxpy Cholesky -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.2.1** of [golub2013matrix] (gaxpy Cholesky). Given a symmetric positive definite
$A \in \mathbb{R}^{n \times n}$, the algorithm computes a lower triangular $G$ such that
$A = GG^T$. For all $i \ge j$, $G(i, j)$ overwrites $A(i, j)$.
```
for j = 1:n
    if j > 1
        A(j:n, j) = A(j:n, j) − A(j:n, 1:j−1) · A(j, 1:j−1)ᵀ
    end
    A(j:n, j) = A(j:n, j) / sqrt(A(j, j))
end
```

The gaxpy is a running difference from each entry of $A(j{:}n, j)$ (`FloatingPoint.runningDiff`,
empty for the first column). It reads the row $A(j, 1{:}j-1)$ of the state at the start of the
column, which the column update does not change. The square root is rounded once, and the whole
column, diagonal included, is divided by it. The strict upper triangle keeps the entries of $A$.
The program has no hypothesis on $A$. -/
noncomputable def algorithm_4_2_1 (A : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) => do
    let B ← ((List.finRange n).filter (j ≤ ·)).foldlM
      (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
        let t ← runningDiff rnd ((List.finRange n).filter (· < j)) (B i) (A j) (B i j)
        pure (B.updateRow i (Function.update (B i) j t))) A
    let s ← rnd (Real.sqrt (B j j))
    ((List.finRange n).filter (j ≤ ·)).foldlM
      (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
        let g ← rnd (C i j / s)
        pure (C.updateRow i (Function.update (C i) j g))) B) A

end Programs

section Bridge

variable (fp : RoundingModel ℝ)

/-- Column $j$ of the state $S$ is a finished column of Algorithm 4.2.1: there are a pivot $t$, the
running difference of $a_{jj}$ and the rounded products $s_{jk} s_{jk}$ for $k < j$, and a
rounding $\hat s$ of $\sqrt t$, such that $s_{jj}$ is a rounding of $t / \hat s$ and, for
$i > j$, $s_{ij}$ is a rounding of $r / \hat s$ for a running difference $r$ of $a_{ij}$ and the
rounded products $s_{ik} s_{jk}$. -/
private def CholDone (A S : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : Prop :=
  ∃ t sh : ℝ, RoundsRunningDiff fp (below j) (S j) (S j) (A j j) t ∧ fp.Rounds (Real.sqrt t) sh ∧
    fp.Rounds (t / sh) (S j j) ∧
    ∀ i, j < i → ∃ r, RoundsRunningDiff fp (below j) (S i) (S j) (A i j) r ∧
      fp.Rounds (r / sh) (S i j)

private theorem CholDone.congr {A S S' : Matrix (Fin n) (Fin n) ℝ} {j : Fin n}
    (h : CholDone fp A S j) (hS : ∀ i k, k ≤ j → S' i k = S i k) : CholDone fp A S' j := by
  obtain ⟨t, sh, hd, hs, hjj, hcol⟩ := h
  have hb : ∀ i, ∀ k ∈ below j, S' i k = S i k := fun i k hk => hS i k (le_of_lt (mem_below.1 hk))
  refine ⟨t, sh, hd.congr (hb j) (hb j), hs, by rw [hS j j le_rfl]; exact hjj, fun i hi => ?_⟩
  obtain ⟨r, hr, hl⟩ := hcol i hi
  exact ⟨r, hr.congr (hb i) (hb j), by rw [hS i j le_rfl]; exact hl⟩

/-- The loop invariant of Algorithm 4.2.1 after $c$ columns: the columns from $c$ on are those of
$A$, and the columns before $c$ are finished. -/
private def CholInv (A : Matrix (Fin n) (Fin n) ℝ) (c : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i k : Fin n, c ≤ k.val → S i k = A i k) ∧ ∀ j : Fin n, j.val < c → CholDone fp A S j

/-- One column step of Algorithm 4.2.1 keeps the loop invariant. -/
private theorem cholInv_step (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : CholInv fp A j S) (S' : Matrix (Fin n) (Fin n) ℝ)
    (hS' : S' ∈ ((do
      let B ← ((List.finRange n).filter (j ≤ ·)).foldlM
        (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
          let t ← runningDiff fp.round (below j) (B i) (S j) (B i j)
          pure (B.updateRow i (Function.update (B i) j t))) S
      let s ← fp.round (Real.sqrt (B j j))
      ((List.finRange n).filter (j ≤ ·)).foldlM
        (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
          let g ← fp.round (C i j / s)
          pure (C.updateRow i (Function.update (C i) j g))) B) : SetM _).run) :
    CholInv fp A (j + 1) S' := by
  obtain ⟨hA, hdone⟩ := hS
  simp only [SetM.mem_run_bind] at hS'
  obtain ⟨B, hB, s, hs, hS'⟩ := hS'
  have hmem : ∀ i, i ∈ (List.finRange n).filter (j ≤ ·) ↔ j ≤ i := fun i => by simp
  have hnd : ((List.finRange n).filter (j ≤ ·)).Nodup := (List.nodup_finRange n).filter _
  obtain ⟨hB1, hB2⟩ := (mem_run_foldlM_updateRow_iff hnd j
    (fun i r => runningDiff fp.round (below j) r (S j) (r j)) S B).1 hB
  obtain ⟨hC1, hC2⟩ := (mem_run_foldlM_updateRow_iff hnd j
    (fun i r => fp.round (r j / s)) B S').1 hS'
  -- entries outside column `j` never change
  have hBo : ∀ i k, k ≠ j → B i k = S i k := fun i k hk => by
    by_cases hi : j ≤ i
    · obtain ⟨x, -, hx⟩ := hB2 i ((hmem i).2 hi)
      rw [hx, Function.update_of_ne hk]
    · rw [hB1 i fun h => hi ((hmem i).1 h)]
  have hSo : ∀ i k, k ≠ j → S' i k = S i k := fun i k hk => by
    by_cases hi : j ≤ i
    · obtain ⟨x, -, hx⟩ := hC2 i ((hmem i).2 hi)
      rw [hx, Function.update_of_ne hk, hBo i k hk]
    · rw [hC1 i fun h => hi ((hmem i).1 h), hBo i k hk]
  -- column `j`, on and below the diagonal
  have hcol : ∀ i, j ≤ i → ∃ t, RoundsRunningDiff fp (below j) (S' i) (S' j) (A i j) t ∧
      B i j = t ∧ fp.Rounds (t / s) (S' i j) := by
    intro i hi
    obtain ⟨t, ht, hx⟩ := hB2 i ((hmem i).2 hi)
    obtain ⟨g, hg, hy⟩ := hC2 i ((hmem i).2 hi)
    have hBij : B i j = t := by rw [hx, Function.update_self]
    refine ⟨t, ?_, hBij, ?_⟩
    · have ht' := (mem_run_runningDiff_iff (nodup_below j)).1 ht
      rw [hA i j le_rfl] at ht'
      exact ht'.congr (fun k hk => hSo i k (ne_of_lt (mem_below.1 hk)))
        (fun k hk => hSo j k (ne_of_lt (mem_below.1 hk)))
    · rw [hy, Function.update_self, ← hBij]
      exact hg
  refine ⟨fun i k hk => ?_, fun j' hj' => ?_⟩
  · have hkj : k ≠ j := fun h => by rw [h] at hk; simp at hk
    rw [hSo i k hkj]
    exact hA i k (by omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | hj'
    · refine (hdone j' hj').congr fp fun i k hk => hSo i k ?_
      intro h
      rw [h] at hk
      exact absurd (Fin.lt_def.1 (lt_of_le_of_lt hk (Fin.lt_def.2 hj'))) (lt_irrefl _)
    · have hjj : j' = j := Fin.ext hj'
      subst hjj
      obtain ⟨t, ht, hBt, hjj⟩ := hcol j' le_rfl
      refine ⟨t, s, ht, ?_, hjj, fun i hi => ?_⟩
      · rw [← hBt]; exact hs
      · obtain ⟨r, hr, -, hl⟩ := hcol i hi.le
        exact ⟨r, hr, hl⟩

/-- Every run of Algorithm 4.2.1 has all its columns finished. -/
private theorem cholDone_of_mem_run (A : Matrix (Fin n) (Fin n) ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F ∈ (algorithm_4_2_1 fp.round A).run) (j : Fin n) :
    CholDone fp A F j :=
  (SetM.forall_mem_run_foldlM_finRange (CholInv fp A)
    ⟨fun _ _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    (fun j S hS S' hS' => cholInv_step fp A j S hS S' hS') F hF).2 j j.isLt

/-- On and below the diagonal, $F - \operatorname{strictUpper}(F)$ agrees with $F$. -/
private theorem sub_strictUpper_apply_of_le (F : Matrix (Fin n) (Fin n) ℝ) {i k : Fin n}
    (hki : k ≤ i) : (F - F.strictUpper) i k = F i k := by
  simp [strictUpper, not_lt.2 hki]

/-- **Algorithm 4.2.1** of [golub2013matrix], rounding bridge. Let $A \in \mathbb{R}^{n \times n}$
be arbitrary. Let $F$ be a matrix that Algorithm 4.2.1 can compute from $A$ in the rounding
model `fp`, with every diagonal entry $f_{jj}$ nonzero, and let $\hat G$ be the lower triangle
of $F$. Then $\hat G$ is a computed Cholesky factor of $A$ in the operation order of the
algorithm. That is, for each $j$ there are a number $t_j \ge 0$, obtained from $a_{jj}$ by
subtracting roundings of the products $\hat g_{jk}^2$, $k < j$, one after the other with one
rounding per subtraction, and a rounding $\hat s_j$ of $\sqrt{t_j}$, such that $\hat g_{jj}$ is
a rounding of $t_j / \hat s_j$ and, for $i > j$, $\hat g_{ij}$ is a rounding of
$t_{ij} / \hat s_j$, with $t_{ij}$ obtained in the same way from $a_{ij}$ and the products
$\hat g_{ik} \hat g_{jk}$, $k < j$.

The relation is `FloatingPoint.RoundsCholeskyDiv fp A (F - F.strictUpper)`. The hypothesis is on
the returned diagonal, not on the intermediate pivots, and it forces every computed pivot $t_j$
to be positive: if $t_j \le 0$, then $\sqrt{t_j} = 0$, whose rounding is $0$, and then
$\hat g_{jj} = \mathrm{fl}(t_j / 0) = 0$. -/
theorem algorithm_4_2_1_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ F ∈ (algorithm_4_2_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      RoundsCholeskyDiv fp A (F - F.strictUpper) := by
  intro F hF hd
  have hG : ∀ i k, k ≤ i → (F - F.strictUpper) i k = F i k :=
    fun i k hki => sub_strictUpper_apply_of_le F hki
  choose t sh hpiv hs hjj hcol using cholDone_of_mem_run fp A hF
  refine ⟨fun i k hik => by simp [strictUpper, hik], t, sh, fun j => ?_, fun j => ?_,
    fun j => ?_, fun i j hji => ?_⟩
  · obtain ⟨p, hp, hsum⟩ := hpiv j
    refine ⟨below j, nodup_below j, fun k => mem_below, p, fun k hk => ?_, hsum⟩
    rw [hG j k (mem_below.1 hk).le]
    exact hp k hk
  · -- the pivot is positive
    have ht : 0 ≤ t j := by
      by_contra hneg
      have h0 : Real.sqrt (t j) = 0 := Real.sqrt_eq_zero'.2 (le_of_lt (not_le.1 hneg))
      have hsh : sh j = 0 := (h0 ▸ hs j).eq_zero_of_zero
      have := hjj j
      rw [hsh, div_zero] at this
      exact hd j this.eq_zero_of_zero
    exact ⟨Real.sqrt (t j), Real.sqrt_nonneg _, Real.mul_self_sqrt ht, hs j⟩
  · rw [hG j j le_rfl]; exact hjj j
  · obtain ⟨r, ⟨p, hp, hsum⟩, hl⟩ := hcol j i hji
    refine ⟨below j, r, nodup_below j, fun k => mem_below, ⟨p, fun k hk => ?_, hsum⟩, ?_⟩
    · rw [hG i k (lt_trans (mem_below.1 hk) hji).le, hG j k (mem_below.1 hk).le]
      exact hp k hk
    · rw [hG i j hji.le]; exact hl

/-- **Algorithm 4.2.1** of [golub2013matrix], existence of runs. If every real number has an
admissible rounding in the rounding model `fp`, then for every $A \in \mathbb{R}^{n \times n}$
the set of runs of Algorithm 4.2.1 on $A$ is nonempty.

So `GolubVanLoan.Chapter04.algorithm_4_2_1_rounds` and the stability statements built on it are
not vacuous. The hypothesis is `FloatingPoint.RoundingModel.IsTotal`. -/
theorem algorithm_4_2_1_run_nonempty {fp : RoundingModel ℝ} (hfp : fp.IsTotal)
    (A : Matrix (Fin n) (Fin n) ℝ) : (algorithm_4_2_1 fp.round A).run.Nonempty :=
  SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
    (SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
      (runningDiff_run_nonempty hfp _ _ _ _) fun _ _ => ⟨_, SetM.mem_run_pure.2 rfl⟩) _)
    fun _ _ => SetM.run_bind_nonempty (RoundingModel.run_round_nonempty hfp _) fun _ _ =>
      SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
        (RoundingModel.run_round_nonempty hfp _) fun _ _ => ⟨_, SetM.mem_run_pure.2 rfl⟩) _) A

end Bridge

/-- The exact run of Algorithm 4.2.1 is one of its runs in the exact rounding model. -/
private theorem algorithm_4_2_1_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_2_1 pure A) ∈ (algorithm_4_2_1 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_4_2_1, runningDiff, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- In exact arithmetic, for every $A \in \mathbb{R}^{n \times n}$, the lower triangle of the output
of Algorithm 4.2.1 is the backbone Cholesky recurrence `Matrix.cholesky A`.

Off the positive definite cone both compute the same values, because the square root of a
negative number is $0$ and $x / 0 = 0$. The proof reads the relational invariant at the exact
model, column by column. -/
theorem algorithm_4_2_1_lower_eq_cholesky (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_2_1 pure A) - (Id.run (algorithm_4_2_1 pure A)).strictUpper =
      cholesky A := by
  obtain ⟨F, hF⟩ : ∃ F, Id.run (algorithm_4_2_1 pure A) = F := ⟨_, rfl⟩
  have hdone := cholDone_of_mem_run (RoundingModel.exact ℝ) A (hF ▸ algorithm_4_2_1_mem_exact A)
  rw [hF]
  have hset : ∀ j : Fin n, (below j).toFinset = univ.filter (· < j) := fun j => by
    ext k; simp [below]
  -- column by column, on and below the diagonal
  have key : ∀ j i : Fin n, j ≤ i → F i j = cholesky A i j := by
    intro j
    induction j using WellFoundedLT.induction with
    | _ j ih =>
    obtain ⟨t, sh, hpiv, hs, hjj, hcol⟩ := hdone j
    rw [RoundingModel.exact_rounds_iff] at hs hjj
    have ht := hpiv.eq_of_exact (nodup_below j)
    rw [hset] at ht
    have hsum : ∀ i, j ≤ i → ∑ k ∈ univ.filter (· < j), F i k * F j k =
        ∑ k ∈ univ.filter (· < j), cholesky A i k * cholesky A j k := fun i hi =>
      Finset.sum_congr rfl fun k hk => by
        have hkj := (mem_filter.1 hk).2
        rw [ih k hkj i (hkj.le.trans hi), ih k hkj j hkj.le]
    have hdiag : F j j = cholesky A j j := by
      rw [hjj, hs, Real.div_sqrt, ht, cholesky_apply_self, hsum j le_rfl]
      simp [Real.norm_eq_abs, sq]
    intro i hji
    rcases eq_or_lt_of_le hji with rfl | hji'
    · exact hdiag
    · obtain ⟨r, hr, hl⟩ := hcol i hji'
      rw [RoundingModel.exact_rounds_iff] at hl
      have hr' := hr.eq_of_exact (nodup_below j)
      rw [hset] at hr'
      rw [hl, hr', hs, cholesky_apply_of_lt A hji', ← hdiag, hjj, hs, Real.div_sqrt, ht,
        hsum i hji]
      simp
  ext i k
  rcases le_or_gt k i with hki | hik
  · rw [sub_strictUpper_apply_of_le F hki, key k i hki]
  · simp [strictUpper, hik, cholesky_apply_of_gt A hik]

/-- **Algorithm 4.2.1** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive definite, and let $G$ be the lower triangle of the output of Algorithm
4.2.1 in exact arithmetic. Then $G$ is the Cholesky factor `Matrix.cholesky A`, and $A = GG^T$.

The lower triangle of the output `F` is `F - F.strictUpper`. Exact arithmetic is the monad `Id`
with the hook `pure`. -/
theorem algorithm_4_2_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    Id.run (algorithm_4_2_1 pure A) - (Id.run (algorithm_4_2_1 pure A)).strictUpper =
        cholesky A ∧
      A = (Id.run (algorithm_4_2_1 pure A) - (Id.run (algorithm_4_2_1 pure A)).strictUpper) *
        (Id.run (algorithm_4_2_1 pure A) - (Id.run (algorithm_4_2_1 pure A)).strictUpper)ᵀ := by
  rw [algorithm_4_2_1_lower_eq_cholesky]
  exact ⟨rfl, (cholesky_mul_transpose hA).symm⟩

section Solve

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Section 4.2.6** of [golub2013matrix], the solve stage. Let $F$ be an output of Algorithm
4.2.1, with lower triangle $\hat G = F - \operatorname{strictUpper}(F)$, and let
$b \in \mathbb{R}^n$. The program solves $\hat G y = b$ and then $\hat G^T x = y$, and returns
$x$.

The two solves are the column-oriented substitutions of Chapter 3,
`GolubVanLoan.Chapter03.algorithm_3_1_3` and `GolubVanLoan.Chapter03.algorithm_3_1_4`. -/
noncomputable def solveCholesky (F : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let y ← Chapter03.algorithm_3_1_3 rnd (F - F.strictUpper) b
  Chapter03.algorithm_3_1_4 rnd (F - F.strictUpper)ᵀ y

end Solve

/-- **Section 4.2.6** of [golub2013matrix] (Wilkinson's backward error bound). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $b \in \mathbb{R}^n$, and let the unit roundoff
$u$ satisfy $(3n + 3)u < 1$ and $n \gamma_{n+3} < 1$. Let $F$ be a matrix that Algorithm 4.2.1
can compute from $A$, with every diagonal entry nonzero, and let $\hat x$ be a vector that
`GolubVanLoan.Chapter04.solveCholesky` can compute from $F$ and $b$. Then there is
$E \in \mathbb{R}^{n \times n}$ with
$$(A + E) \hat x = b, \qquad \|E\|_2 \le \frac{n \gamma_{3n+3}}{1 - n \gamma_{n+3}} \|A\|_2.$$

The source says that the computed solution $\hat x$ obtained via the Cholesky process solves
$(A + E) \hat x = b$ with $\|E\|_2 \le c_n u \|A\|_2$, where $c_n$ is a small constant that
depends on $n$. The theorem makes this constant explicit, $c_n \approx 3n^2$. The hypothesis on
the returned diagonal forces every computed pivot to be positive
(`GolubVanLoan.Chapter04.algorithm_4_2_1_rounds`). The claim of the source that the process runs
to completion when $q_n u \kappa_2(A) \le 1$ is not formalized. -/
theorem cholesky_backward_error {fp : RoundingModel ℝ} (hn : ((3 * n + 3 : ℕ) : ℝ) * fp.u < 1)
    (hγ : n * gamma fp.u (n + 3) < 1) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (b : Fin n → ℝ) :
    ∀ F ∈ (algorithm_4_2_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      ∀ x ∈ (solveCholesky fp.round F b).run,
        ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x = b ∧
          lpOpNorm 2 E ≤ n * gamma fp.u (3 * n + 3) * lpOpNorm 2 A /
            (1 - n * gamma fp.u (n + 3)) := by
  intro F hF hd x hx
  have hu : fp.u < 1 := by
    have h1 : (1 : ℝ) * fp.u ≤ ((3 * n + 3 : ℕ) : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by norm_cast; omega) fp.u_nonneg
    linarith
  simp only [solveCholesky, SetM.mem_run_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨E, hE, hAx⟩ := l2_opNorm_le_of_roundsCholeskyDiv hu (by simpa using hn)
    (by simpa using hγ) hA (algorithm_4_2_1_rounds fp A F hF hd)
    (fun j => by rw [sub_strictUpper_apply_of_le F le_rfl]; exact hd j)
    (Chapter03.algorithm_3_1_3_rounds fp _ b y hy) (Chapter03.algorithm_3_1_4_rounds fp _ y x hx)
  exact ⟨E, hAx, by simpa using hE⟩

/-! ### §4.2.7 The $LDL^T$ factorization with symmetric pivoting -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The pivot of step $k$ of Algorithm 4.2.2 of [golub2013matrix]: the first index $j \ge k$ with
$a_{jj} = \max\{a_{kk}, \dots, a_{nn}\}$. The comparisons of the stored values are exact. -/
noncomputable def diagPivot (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Fin n :=
  ((List.finRange n).filter (k ≤ ·)).foldl (fun (b i : Fin n) => if A b b < A i i then i else b) k

/-- One step of Algorithm 4.2.2 of [golub2013matrix], the body of its loop. Step $k$ takes the state
$(A, \mathrm{piv})$ and chooses the pivot $j$ by `GolubVanLoan.Chapter04.diagPivot`. It
interchanges rows $k$ and $j$ and columns $k$ and $j$ of $A$, and sets $\alpha = a_{kk}$ and
$v = A(k{+}1{:}n, k)$. It overwrites $a_{ik}$, $i > k$, with $\mathrm{fl}(v_i / \alpha)$ and
$a_{il}$, $i, l > k$, with $\mathrm{fl}(a_{il} - \mathrm{fl}(\mathrm{fl}(v_i v_l) / \alpha))$.
It records $\mathrm{piv}(k) = j$.

See `GolubVanLoan.Chapter04.algorithm_4_2_2` for the conventions. -/
noncomputable def ldltPivotStep (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) (k : Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) := do
  let j := diagPivot st.1 k
  let A := st.1.submatrix (Equiv.swap k j) (Equiv.swap k j)
  let α := A k k
  let v : Fin n → ℝ := fun i => A i k
  let B ← ((List.finRange n).filter (k < ·)).foldlM
    (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
      let l ← rnd (v i / α)
      pure (B.updateRow i (Function.update (B i) k l))) A
  let C ← ((List.finRange n).filter (k < ·)).foldlM
    (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
      ((List.finRange n).filter (k < ·)).foldlM
        (fun (C : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) => do
          let p ← rnd (v i * v l)
          let q ← rnd (p / α)
          let c ← rnd (C i l - q)
          pure (C.updateRow i (Function.update (C i) l c))) C) B
  pure (C, Function.update st.2 k j)

/-- **Algorithm 4.2.2** of [golub2013matrix] (outer product $LDL^T$ with pivoting). Given a
symmetric positive semidefinite $A \in \mathbb{R}^{n \times n}$, the algorithm computes a
permutation $P$, a unit lower triangular $L$, and a diagonal matrix
$D = \operatorname{diag}(d_1, \dots, d_n)$ such that $PAP^T = LDL^T$. The entry $a_{ij}$ is
overwritten by $d_i$ if $i = j$ and by $\ell_{ij}$ if $i > j$.
```
for k = 1:n
    piv(k) = j where a_jj = max{a_kk, …, a_nn}
    A(k, :) ↔ A(j, :)
    A(:, k) ↔ A(:, j)
    α = A(k, k)
    v = A(k+1:n, k)
    A(k+1:n, k) = v/α
    A(k+1:n, k+1:n) = A(k+1:n, k+1:n) − vvᵀ/α
end
```

The state is the matrix and the pivot vector, with $\mathrm{piv}(k) = j$; the pivot vector
starts as the identity. The interchanges act on whole rows and columns, and $v$ is a copy. The
update $a_{il} \leftarrow \mathrm{fl}(a_{il} - \mathrm{fl}(\mathrm{fl}(v_i v_l) / \alpha))$ is
in the order of the source. The program has no guard on $\alpha = 0$: for a semidefinite input
the trailing block then vanishes, and $x / 0 = 0$. -/
noncomputable def algorithm_4_2_2 (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) :=
  (List.finRange n).foldlM (ldltPivotStep rnd) (A, fun i => i)

end Programs

/-! ### §4.2.8 The symmetric semidefinite case -/

/-- **Equation (4.2.11)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive semidefinite of rank $r$. Then all eigenvalues of $A$ are nonnegative, and exactly $r$
of them are nonzero.

The source orders the eigenvalues as $0 = \lambda_n = \dots = \lambda_{r+1} < \lambda_r \le
\dots \le \lambda_1$. The eigenvalues `Matrix.IsHermitian.eigenvalues` of Mathlib are not
ordered, so the ordering is a relabelling. -/
theorem equation_4_2_11 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (∀ i, 0 ≤ hA.1.eigenvalues i) ∧ Fintype.card {i // hA.1.eigenvalues i ≠ 0} = A.rank :=
  ⟨hA.eigenvalues_nonneg, hA.1.rank_eq_card_non_zero_eigs.symm⟩

/-- **Theorem 4.2.8** of [golub2013matrix], inequality (4.2.12). Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive semidefinite. Then for all $i$ and $j$,
$$|a_{ij}| \le (a_{ii} + a_{jj}) / 2.$$
-/
theorem theorem_4_2_8_a {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i j : Fin n) :
    |A i j| ≤ (A i i + A j j) / 2 := by
  simpa using hA.norm_apply_le_add_re_diag_div_two i j

/-- **Theorem 4.2.8** of [golub2013matrix], inequality (4.2.13). Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive semidefinite. Then for all $i$ and $j$,
$$|a_{ij}| \le \sqrt{a_{ii} a_{jj}}.$$

**Generalization.** The source states the inequality for $i \neq j$. It also holds for $i = j$,
where it says $|a_{ii}| \le a_{ii}$. -/
theorem theorem_4_2_8_b {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i j : Fin n) :
    |A i j| ≤ Real.sqrt (A i i * A j j) :=
  Real.abs_le_sqrt (by simpa [sq_abs] using hA.norm_apply_sq_le_mul_re_diag i j)

/-- **Theorem 4.2.8** of [golub2013matrix], equation (4.2.14). Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive semidefinite. Then $|a_{ij}| \le \max\{a_{ii}, a_{jj}\}$ for all $i$ and
$j$, and, if $n \ge 1$,
$$\max_{i, j} |a_{ij}| = \max_i a_{ii}.$$

The maxima are the suprema `⨆` over the finite index sets. -/
theorem theorem_4_2_8_c {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (∀ i j, |A i j| ≤ max (A i i) (A j j)) ∧
      ∀ [NeZero n], (⨆ i, ⨆ j, |A i j|) = ⨆ i, A i i := by
  have h1 : ∀ i j, |A i j| ≤ max (A i i) (A j j) := fun i j => by
    simpa using hA.norm_apply_le_max_re_diag i j
  refine ⟨h1, fun {_} => le_antisymm ?_ ?_⟩
  · have hb : BddAbove (Set.range fun i => A i i) := (Set.finite_range _).bddAbove
    exact ciSup_le fun i => ciSup_le fun j =>
      (h1 i j).trans (max_le (le_ciSup hb i) (le_ciSup hb j))
  · have hb : ∀ i, BddAbove (Set.range fun j => |A i j|) := fun i => (Set.finite_range _).bddAbove
    have hb' : BddAbove (Set.range fun i => ⨆ j, |A i j|) := (Set.finite_range _).bddAbove
    refine ciSup_le fun i => ?_
    calc A i i = |A i i| := (abs_of_nonneg hA.diag_nonneg).symm
      _ ≤ ⨆ j, |A i j| := le_ciSup (hb i) i
      _ ≤ ⨆ i, ⨆ j, |A i j| := le_ciSup hb' i

/-- **Theorem 4.2.8** of [golub2013matrix], implication (4.2.15). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive semidefinite. If $a_{ii} = 0$, then
$A(i, :) = 0$ and $A(:, i) = 0$. -/
theorem theorem_4_2_8_d {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {i : Fin n}
    (hi : A i i = 0) : (∀ j, A i j = 0) ∧ ∀ j, A j i = 0 :=
  ⟨fun j => (hA.apply_eq_zero_of_diag_eq_zero hi j).1,
    fun j => (hA.apply_eq_zero_of_diag_eq_zero hi j).2⟩

/-- **Theorem 4.2.8** of [golub2013matrix]. If $A \in \mathbb{R}^{n \times n}$ is symmetric positive
semidefinite, then for all $i$ and $j$
$$|a_{ij}| \le (a_{ii} + a_{jj}) / 2, \qquad (4.2.12)$$
$$|a_{ij}| \le \sqrt{a_{ii} a_{jj}}, \qquad (4.2.13)$$
$$|a_{ij}| \le \max\{a_{ii}, a_{jj}\}, \quad \text{and} \quad \max_{i, j} |a_{ij}| = \max_i
  a_{ii} \text{ if } n \ge 1, \qquad (4.2.14)$$
$$a_{ii} = 0 \implies A(i, :) = 0, \ A(:, i) = 0. \qquad (4.2.15)$$

**Generalization.** The source states (4.2.13) for $i \neq j$. It holds for all $i$ and $j$.

The four parts are `GolubVanLoan.Chapter04.theorem_4_2_8_a`,
`GolubVanLoan.Chapter04.theorem_4_2_8_b`, `GolubVanLoan.Chapter04.theorem_4_2_8_c` and
`GolubVanLoan.Chapter04.theorem_4_2_8_d`. -/
theorem theorem_4_2_8 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (∀ i j, |A i j| ≤ (A i i + A j j) / 2) ∧ (∀ i j, |A i j| ≤ Real.sqrt (A i i * A j j)) ∧
      ((∀ i j, |A i j| ≤ max (A i i) (A j j)) ∧
        ∀ [NeZero n], (⨆ i, ⨆ j, |A i j|) = ⨆ i, A i i) ∧
      ∀ i, A i i = 0 → (∀ j, A i j = 0) ∧ ∀ j, A j i = 0 :=
  ⟨theorem_4_2_8_a hA, theorem_4_2_8_b hA, theorem_4_2_8_c hA, fun _ => theorem_4_2_8_d hA⟩

/-- **Equation (4.2.10)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite. Then there are a permutation matrix $P$, a unit lower triangular
$L \in \mathbb{R}^{n \times n}$ and $D = \operatorname{diag}(d_1, \dots, d_n)$ with
$$PAP^T = LDL^T, \qquad d_1 \ge d_2 \ge \dots \ge d_n > 0.$$

This is the factorization that the diagonal pivoting strategy produces. The permutation is
`σ : Equiv.Perm (Fin n)`, and $PAP^T$ is `A.submatrix σ σ`. -/
theorem equation_4_2_10 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ (σ : Equiv.Perm (Fin n)) (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      L.IsUnitLowerTriangular ∧ A.submatrix σ σ = L * diagonal d * Lᵀ ∧ Antitone d ∧
        ∀ i, 0 < d i := by
  obtain ⟨σ, L, d, hL, heq, hanti, hpos, -⟩ := hA.posSemidef.exists_perm_ldl_rank
  have hr : A.rank = n := by rw [rank_of_isUnit A hA.isUnit, Fintype.card_fin]
  refine ⟨σ, L, d, hL, by simpa [conjTranspose_eq_transpose_of_trivial] using heq, hanti,
    fun i => hpos i (by rw [hr]; exact i.isLt)⟩

/-- For a diagonal matrix $D = \operatorname{diag}(d)$, the entry $(a, b)$ of $XDX^T$ is
$\sum_k x_{ak} d_k x_{bk}$. -/
private theorem mul_diagonal_mul_transpose_apply {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (d : κ → ℝ) (a b : ι) :
    (X * diagonal d * Xᵀ) a b = ∑ k, X a k * d k * X b k := by
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply]

/-- **Equation (4.2.17)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive semidefinite of rank $r$. Then there are a permutation matrix $P$, a matrix $L =
\begin{bmatrix} L_{11} \\ L_{21} \end{bmatrix} \in \mathbb{R}^{n \times r}$ whose first $r$ rows
$L_{11}$ form a unit lower triangular matrix, and $D_r = \operatorname{diag}(d_1, \dots, d_r)$
with $d_1, \dots, d_r > 0$, such that
$$PAP^T = \begin{bmatrix} L_{11} \\ L_{21} \end{bmatrix} D_r \begin{bmatrix} L_{11}^T & L_{21}^T
  \end{bmatrix}.$$

The block $L_{11}$ is `L.submatrix (Fin.castLE _) id`, and the rank is `Matrix.rank A`. The
permutation is `σ`, and $PAP^T$ is `A.submatrix σ σ`. -/
theorem equation_4_2_17 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    ∃ (σ : Equiv.Perm (Fin n)) (L : Matrix (Fin n) (Fin A.rank) ℝ) (d : Fin A.rank → ℝ),
      (L.submatrix (Fin.castLE (A.rank_le_width)) id).IsUnitLowerTriangular ∧
        (∀ i, 0 < d i) ∧ A.submatrix σ σ = L * diagonal d * Lᵀ := by
  obtain ⟨σ, Lf, d, hL, heq, -, hpos, hzero⟩ := hA.exists_perm_ldl_rank
  set h := A.rank_le_width
  refine ⟨σ, Lf.submatrix id (Fin.castLE h), d ∘ Fin.castLE h, ⟨fun a b hab => ?_, fun a => ?_⟩,
    fun i => hpos _ (by rw [Fin.val_castLE]; exact i.isLt), ?_⟩
  · exact hL.isLowerTriangular (show Fin.castLE h a < Fin.castLE h b from hab)
  · exact hL.diag_eq_one _
  · have heq' : A.submatrix σ σ = Lf * diagonal d * Lfᵀ := by
      simpa [conjTranspose_eq_transpose_of_trivial] using heq
    rw [heq']
    ext i j
    rw [mul_diagonal_mul_transpose_apply, mul_diagonal_mul_transpose_apply]
    simp only [submatrix_apply, id, Function.comp_apply]
    exact Fin.sum_eq_sum_castLE_of_forall_le h _ fun k hk => by rw [hzero k hk]; ring

/-- **Section 4.2.8** of [golub2013matrix], the rank-one expansion. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive semidefinite of rank $r$. Then there are
$P$, $L \in \mathbb{R}^{n \times r}$ and $d_1, \dots, d_r$ as in (4.2.17) with
$$PAP^T = \sum_{j=1}^{r} d_j \ell_j \ell_j^T,$$
where $\ell_j$ is the $j$th column of $L$.

The source calls this expansion a relatively cheap alternative to the SVD rank-1 expansion. -/
theorem equation_4_2_17_sum {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    ∃ (σ : Equiv.Perm (Fin n)) (L : Matrix (Fin n) (Fin A.rank) ℝ) (d : Fin A.rank → ℝ),
      (L.submatrix (Fin.castLE (A.rank_le_width)) id).IsUnitLowerTriangular ∧
        (∀ i, 0 < d i) ∧
        A.submatrix σ σ = ∑ j, d j • vecMulVec (fun i => L i j) (fun i => L i j) := by
  obtain ⟨σ, L, d, hL, hd, heq⟩ := equation_4_2_17 hA
  refine ⟨σ, L, d, hL, hd, ?_⟩
  rw [heq]
  ext a b
  rw [mul_diagonal_mul_transpose_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### §4.2.9 Block Cholesky -/

/-- **Equation (4.2.18)** of [golub2013matrix], with the block equations of block Cholesky. Let
$A \in \mathbb{R}^{(r+s) \times (r+s)}$ be symmetric positive definite, blocked as
$$A = \begin{bmatrix} A_{11} & A_{21}^T \\ A_{21} & A_{22} \end{bmatrix}, \qquad A_{11} \in
  \mathbb{R}^{r \times r},$$
and let $G = \begin{bmatrix} G_{11} & G_{12} \\ G_{21} & G_{22} \end{bmatrix}$ be its Cholesky
factor, blocked in the same way. Then $G_{12} = 0$,
$$A_{11} = G_{11} G_{11}^T, \qquad A_{21} = G_{21} G_{11}^T, \qquad A_{22} = G_{21} G_{21}^T +
  G_{22} G_{22}^T,$$
and $A_{22} - G_{21} G_{21}^T = A_{22} - A_{21} A_{11}^{-1} A_{21}^T$. Moreover $G_{11}$ is the
Cholesky factor of $A_{11}$, and $G_{22}$ is the Cholesky factor of
$A_{22} - A_{21} A_{11}^{-1} A_{21}^T$.

The last statement is Step 3 of the derivation in the source. The blocks are read along
`finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)` with `Matrix.toBlocks₁₁` and its companions, and
the Cholesky factor is `Matrix.cholesky`. -/
theorem equation_4_2_18 {r s : ℕ} {A : Matrix (Fin (r + s)) (Fin (r + s)) ℝ} (hA : A.PosDef) :
    let A' := A.submatrix finSumFinEquiv finSumFinEquiv
    let G' := (cholesky A).submatrix finSumFinEquiv finSumFinEquiv
    G'.toBlocks₁₂ = 0 ∧ A'.toBlocks₁₁ = G'.toBlocks₁₁ * G'.toBlocks₁₁ᵀ ∧
      A'.toBlocks₂₁ = G'.toBlocks₂₁ * G'.toBlocks₁₁ᵀ ∧
      A'.toBlocks₂₂ = G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ + G'.toBlocks₂₂ * G'.toBlocks₂₂ᵀ ∧
      A'.toBlocks₂₂ - G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ =
        A'.toBlocks₂₂ - A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ ∧
      G'.toBlocks₁₁ = cholesky A'.toBlocks₁₁ ∧
      G'.toBlocks₂₂ = cholesky (A'.toBlocks₂₂ - A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ)
    := by
  intro A' G'
  have hblk : G' = fromBlocks G'.toBlocks₁₁ 0 G'.toBlocks₂₁ G'.toBlocks₂₂ := by
    have := cholesky_finSumFin hA
    simp only [G', this, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  have h12 : G'.toBlocks₁₂ = 0 := by
    have := cholesky_finSumFin hA
    simp only [G', this, toBlocks_fromBlocks₁₂]
  have hAA : A' = G' * G'ᵀ := by
    simp only [A', G']
    conv_lhs => rw [← cholesky_mul_transpose hA]
    rw [← submatrix_mul_equiv _ _ _ finSumFinEquiv, transpose_submatrix]
  have hprod : A' = fromBlocks (G'.toBlocks₁₁ * G'.toBlocks₁₁ᵀ) (G'.toBlocks₁₁ * G'.toBlocks₂₁ᵀ)
      (G'.toBlocks₂₁ * G'.toBlocks₁₁ᵀ)
      (G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ + G'.toBlocks₂₂ * G'.toBlocks₂₂ᵀ) := by
    rw [hAA, hblk, fromBlocks_transpose, fromBlocks_multiply]
    simp
  have hsym : A'.toBlocks₁₂ = A'.toBlocks₂₁ᵀ := by
    ext i j
    change A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) =
      A (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inl i))
    have := hA.1.apply (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inl i))
    simpa using this
  have hc := cholesky_finSumFin hA
  have h11 : G'.toBlocks₁₁ = cholesky A'.toBlocks₁₁ := by
    simp only [G', hc, toBlocks_fromBlocks₁₁]
    rfl
  have h22 : G'.toBlocks₂₂ = cholesky A'.schurComplement := by
    simp only [G', hc, toBlocks_fromBlocks₂₂]
    rfl
  have hS : A'.schurComplement =
      A'.toBlocks₂₂ - A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ := by
    rw [schurComplement_eq, hsym]
  -- the Schur complement is `A₂₂ − G₂₁ G₂₁ᵀ`
  have hG11 : IsUnit G'.toBlocks₁₁ := by
    rw [h11]
    have hp : A'.toBlocks₁₁.PosDef := (hA.submatrix finSumFinEquiv.injective).submatrix
      Sum.inl_injective
    have := (isCholesky_cholesky hp).isUnit
    simpa [conjTranspose_eq_transpose_of_trivial, isUnit_transpose] using this
  have h11' : A'.toBlocks₁₁ = G'.toBlocks₁₁ * G'.toBlocks₁₁ᵀ := by
    rw [hprod]; simp
  have h21' : A'.toBlocks₂₁ = G'.toBlocks₂₁ * G'.toBlocks₁₁ᵀ := by
    rw [hprod]; simp
  have hschur : A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ =
      G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ := by
    have hdet : IsUnit G'.toBlocks₁₁.det := (isUnit_iff_isUnit_det _).1 hG11
    have hdetT : IsUnit G'.toBlocks₁₁ᵀ.det := by rwa [det_transpose]
    rw [h11', h21', Matrix.mul_inv_rev, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G'.toBlocks₁₁ᵀ, mul_nonsing_inv _ hdetT, Matrix.one_mul,
      ← Matrix.mul_assoc G'.toBlocks₁₁⁻¹, nonsing_inv_mul _ hdet, Matrix.one_mul]
  refine ⟨h12, h11', h21', by rw [hprod]; simp, by rw [hschur], h11, by rw [h22, hS]⟩

/-- The $r \times r$ block $A_{ij}$ of a matrix $A \in \mathbb{R}^{Nr \times Nr}$ in the blocking
(4.2.19) of [golub2013matrix]. With 0-based indices, the entry $(p, q)$ of $A_{ij}$ is
$a_{ir + p, \, jr + q}$; the index pairs are read along
`finProdFinEquiv : Fin N × Fin r ≃ Fin (N * r)`. -/
def blockOf {N r : ℕ} (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) (i j : Fin N) :
    Matrix (Fin r) (Fin r) ℝ :=
  of fun p q => A (finProdFinEquiv (i, p)) (finProdFinEquiv (j, q))

/-- **Equation (4.2.19)** of [golub2013matrix], with the block equations of Algorithm 4.2.4. Let
$n = Nr$, let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, and let $G$ be its
Cholesky factor, both blocked into $r \times r$ blocks $A_{ij}$ and $G_{ij}$,
$1 \le i, j \le N$. Then for all block indices $i$ and $j$:
* $G_{ij} = 0$ if $i < j$;
* $A_{ij} = \sum_{k \le j} G_{ik} G_{jk}^T$ if $i \ge j$;
* $G_{jj}$ is the Cholesky factor of $A_{jj} - \sum_{k < j} G_{jk} G_{jk}^T$;
* $G_{ij} G_{jj}^T = A_{ij} - \sum_{k < j} G_{ik} G_{jk}^T$ if $i > j$.

The blocks are `GolubVanLoan.Chapter04.blockOf`, and the Cholesky factor is `Matrix.cholesky`. -/
theorem equation_4_2_19 {N r : ℕ} {A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ} (hA : A.PosDef)
    (i j : Fin N) :
    (i < j → blockOf (cholesky A) i j = 0) ∧
    (j ≤ i → blockOf A i j =
      ∑ k ∈ univ.filter (· ≤ j), blockOf (cholesky A) i k * (blockOf (cholesky A) j k)ᵀ) ∧
    blockOf (cholesky A) j j = cholesky (blockOf A j j -
      ∑ k ∈ univ.filter (· < j), blockOf (cholesky A) j k * (blockOf (cholesky A) j k)ᵀ) ∧
    (j < i → blockOf (cholesky A) i j * (blockOf (cholesky A) j j)ᵀ = blockOf A i j -
      ∑ k ∈ univ.filter (· < j), blockOf (cholesky A) i k * (blockOf (cholesky A) j k)ᵀ) := by
  set G := cholesky A with hGdef
  have hGl : ∀ a b : Fin N, a < b → blockOf G a b = 0 := fun a b hab => by
    ext p q
    exact isLowerTriangular_cholesky A
      (OrderDual.toDual_lt_toDual.2 (finProdFinEquiv_lt_finProdFinEquiv_iff.2 (Or.inl hab)))
  -- block multiplication
  have hmul : ∀ a b : Fin N, b ≤ a →
      blockOf A a b = ∑ k ∈ univ.filter (· ≤ b), blockOf G a k * (blockOf G b k)ᵀ := by
    intro a b hba
    ext p q
    have h1 : A (finProdFinEquiv (a, p)) (finProdFinEquiv (b, q)) =
        ∑ x : Fin N × Fin r, G (finProdFinEquiv (a, p)) (finProdFinEquiv x) *
          G (finProdFinEquiv (b, q)) (finProdFinEquiv x) := by
      conv_lhs => rw [← cholesky_mul_transpose hA]
      rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv]
      rfl
    rw [blockOf, of_apply, h1, Fintype.sum_prod_type, Matrix.sum_apply]
    refine (Finset.sum_subset (subset_univ (univ.filter (· ≤ b))) fun k _ hk => ?_).symm.trans
      ?_
    · have hbk : b < k := not_le.1 fun h => hk (mem_filter.2 ⟨mem_univ _, h⟩)
      refine Finset.sum_eq_zero fun s _ => ?_
      have := congrFun (congrFun (hGl b k hbk) q) s
      simp only [blockOf, of_apply, Matrix.zero_apply] at this
      rw [this, mul_zero]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [blockOf, Matrix.mul_apply]
  refine ⟨hGl i j, hmul i j, ?_, fun hji => ?_⟩
  · -- the diagonal block is the Cholesky factor of `S`
    have hS : blockOf A j j - ∑ k ∈ univ.filter (· < j), blockOf G j k * (blockOf G j k)ᵀ =
        blockOf G j j * (blockOf G j j)ᵀ := by
      rw [hmul j j le_rfl, sum_filter_le_eq_add, add_sub_cancel_left]
    rw [hS]
    have hc : IsCholesky (blockOf G j j * (blockOf G j j)ᵀ) (blockOf G j j)ᵀ := by
      refine ⟨fun p q hpq => ?_, fun p => ?_, ?_⟩
      · simp only [transpose_apply, blockOf, of_apply]
        exact isLowerTriangular_cholesky A (OrderDual.toDual_lt_toDual.2
          (by rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
              exact Nat.add_lt_add_right hpq _))
      · simpa [blockOf] using cholesky_diag_pos hA (finProdFinEquiv (j, p))
      · rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
    rw [cholesky_eq_of_isCholesky hc, conjTranspose_eq_transpose_of_trivial, transpose_transpose]
  · rw [hmul i j hji.le, sum_filter_le_eq_add, add_sub_cancel_left]

/-! ### Algorithms 4.2.3–4.2.4: block Cholesky -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The Cholesky factorization of a block in Algorithms 4.2.3 and 4.2.4 of [golub2013matrix]. For
$A \in \mathbb{R}^{m \times m}$, the program runs Algorithm 4.2.1 on $A$ and returns the lower
triangle $F - \operatorname{strictUpper}(F)$ of its output $F$. The block algorithms store this
lower triangle as the Cholesky factor.

Setting the strict upper triangle to zero is exact. -/
noncomputable def choleskyLower {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    M (Matrix (Fin m) (Fin m) ℝ) := do
  let F ← algorithm_4_2_1 rnd A
  pure (F - F.strictUpper)

/-- The triangular solve $XG^T = B$ with several right-hand sides, Step 2 of Algorithm 4.2.3 of
[golub2013matrix]. For $G \in \mathbb{R}^{r \times r}$ and $B \in \mathbb{R}^{m \times r}$, the
program overwrites each row $B(i, :)$, $i = 1, \dots, m$, with the solution $x$ of
$Gx = B(i, :)^T$.

Each row is solved by Algorithm 3.1.3 of Chapter 3, `GolubVanLoan.Chapter03.algorithm_3_1_3`. -/
noncomputable def solveRowsLower {m r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin m) (Fin r) ℝ) : M (Matrix (Fin m) (Fin r) ℝ) :=
  (List.finRange m).foldlM (fun (X : Matrix (Fin m) (Fin r) ℝ) (i : Fin m) => do
    let x ← Chapter03.algorithm_3_1_3 rnd G (B i)
    pure (X.updateRow i x)) B

/-- The block update $C - XY^T$ of block Cholesky in [golub2013matrix]: the matrix
$\tilde A = A_{22} - G_{21} G_{21}^T$ of Algorithm 4.2.3 and the matrix
$S = A_{ij} - \sum_{k<j} G_{ik} G_{jk}^T$ of Algorithm 4.2.4. For
$C \in \mathbb{R}^{m \times m'}$, matrices $X$ and $Y$ with $m$ and $m'$ rows and a common
column index type, and a list $o$ of column indices, the entry $(i, j)$ of the result is the
running difference of $c_{ij}$ and the rounded products $x_{ik} y_{jk}$, $k$ along $o$.

The running difference is `FloatingPoint.runningDiff`. -/
noncomputable def mulTransposeDiff {m m' : ℕ} {ι : Type} (o : List ι)
    (C : Matrix (Fin m) (Fin m') ℝ) (X : Matrix (Fin m) ι ℝ) (Y : Matrix (Fin m') ι ℝ) :
    M (Matrix (Fin m) (Fin m') ℝ) :=
  (List.finRange m).foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (i : Fin m) =>
    (List.finRange m').foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (j : Fin m') => do
      let t ← runningDiff rnd o (X i) (Y j) (C i j)
      pure (D.updateRow i (Function.update (D i) j t))) D) C

/-- **Algorithm 4.2.3** of [golub2013matrix] (recursive block Cholesky). Suppose that
$A \in \mathbb{R}^{n \times n}$ is symmetric positive definite and $r$ is a positive integer.
The algorithm computes a lower triangular $G \in \mathbb{R}^{n \times n}$ such that $A = GG^T$.
```
function G = BlockCholesky(A, n, r)
if n ≤ r
    Compute the Cholesky factorization A = GGᵀ.
else
    Compute the Cholesky factorization A(1:r, 1:r) = G₁₁G₁₁ᵀ.
    Solve G₂₁G₁₁ᵀ = A(r+1:n, 1:r) for G₂₁.
    Ã = A(r+1:n, r+1:n) − G₂₁G₂₁ᵀ
    G₂₂ = BlockCholesky(Ã, n − r, r)
    G = [G₁₁ 0; G₂₁ G₂₂]
end
```

The Cholesky factorizations are Algorithm 4.2.1, whose lower triangle is returned
(`GolubVanLoan.Chapter04.choleskyLower`). The block $G_{21}$ is solved row by row by Algorithm
3.1.3 (`GolubVanLoan.Chapter04.solveRowsLower`). The matrix $\tilde A$ is formed by running
differences (`GolubVanLoan.Chapter04.mulTransposeDiff`), without use of its symmetry. The blocks
are read along `finSumFinEquiv : Fin r ⊕ Fin (n - r) ≃ Fin (r + (n - r))` and $n = r + (n - r)$.
The recursion is on $n$, which decreases because $r > 0$. -/
noncomputable def algorithm_4_2_3 (r : ℕ) (hr : 0 < r) :
    (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → M (Matrix (Fin n) (Fin n) ℝ)
  | n, A =>
    if h : n ≤ r then choleskyLower rnd A
    else do
      let e : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
      let B := A.submatrix e e
      let G₁₁ ← choleskyLower rnd B.toBlocks₁₁
      let G₂₁ ← solveRowsLower rnd G₁₁ B.toBlocks₂₁
      let Ã ← mulTransposeDiff rnd (List.finRange r) B.toBlocks₂₂ G₂₁ G₂₁
      let G₂₂ ← algorithm_4_2_3 r hr (n - r) Ã
      pure ((fromBlocks G₁₁ 0 G₂₁ G₂₂).submatrix e.symm e.symm)
  termination_by n => n
  decreasing_by omega

end Programs

/-- In exact arithmetic, for every $A \in \mathbb{R}^{m \times m}$,
`GolubVanLoan.Chapter04.choleskyLower` returns the Cholesky factor `Matrix.cholesky A`. -/
theorem choleskyLower_id {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    Id.run (choleskyLower (M := Id) pure A) = cholesky A := by
  rw [choleskyLower, Id.run_bind, Id.run_pure]
  exact algorithm_4_2_1_lower_eq_cholesky A

/-- In exact arithmetic, `GolubVanLoan.Chapter04.solveRowsLower` replaces each row $B(i, :)$ by the
forward substitution solution `Matrix.forwardSubst G (B i)`. -/
theorem solveRowsLower_id {m r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin m) (Fin r) ℝ) :
    Id.run (solveRowsLower (M := Id) pure G B) = of fun i => G.forwardSubst (B i) := by
  suffices h : ∀ (l : List (Fin m)) (X : Matrix (Fin m) (Fin r) ℝ),
      Id.run (l.foldlM (fun (X : Matrix (Fin m) (Fin r) ℝ) (i : Fin m) => do
        let x ← Chapter03.algorithm_3_1_3 (M := Id) pure G (B i)
        pure (X.updateRow i x)) X) = of fun i => if i ∈ l then G.forwardSubst (B i) else X i by
    rw [solveRowsLower, h]
    ext i j
    simp
  intro l
  induction l with
  | nil => intro X; ext i j; simp
  | cons a l ih =>
    intro X
    rw [List.foldlM_cons, Id.run_bind, Id.run_bind, Id.run_pure, ih,
      Chapter03.algorithm_3_1_3_eq_forwardSubst]
    ext i j
    by_cases hi : i = a
    · subst hi
      by_cases hl : i ∈ l <;> simp [hl]
    · by_cases hl : i ∈ l <;> simp [hl, hi]

/-- In exact arithmetic, the entry $(i, j)$ of the result of
`GolubVanLoan.Chapter04.mulTransposeDiff` is $c_{ij} - \sum_{k \in o} x_{ik} y_{jk}$. -/
theorem mulTransposeDiff_id {m m' : ℕ} {ι : Type} (o : List ι) (C : Matrix (Fin m) (Fin m') ℝ)
    (X : Matrix (Fin m) ι ℝ) (Y : Matrix (Fin m') ι ℝ) :
    Id.run (mulTransposeDiff (M := Id) pure o C X Y) =
      of fun i j => C i j - (o.map fun k => X i k * Y j k).sum := by
  have inner : ∀ (i : Fin m) (l : List (Fin m')) (D : Matrix (Fin m) (Fin m') ℝ),
      Id.run (l.foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (j : Fin m') => do
        let t ← runningDiff (M := Id) pure o (X i) (Y j) (C i j)
        pure (D.updateRow i (Function.update (D i) j t))) D) =
        of fun a b => if a = i ∧ b ∈ l then C a b - (o.map fun k => X a k * Y b k).sum
          else D a b := by
    intro i l
    induction l with
    | nil => intro D; ext a b; simp
    | cons c l ih =>
      intro D
      rw [List.foldlM_cons, Id.run_bind, Id.run_bind, Id.run_pure, ih, runningDiff_id]
      ext a b
      by_cases ha : a = i
      · subst ha
        by_cases hb : b = c
        · subst hb; by_cases hl : b ∈ l <;> simp [hl]
        · by_cases hl : b ∈ l <;> simp [hl, hb]
      · simp [ha]
  have outer : ∀ (l : List (Fin m)) (D : Matrix (Fin m) (Fin m') ℝ),
      Id.run (l.foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (i : Fin m) =>
        (List.finRange m').foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (j : Fin m') => do
          let t ← runningDiff (M := Id) pure o (X i) (Y j) (C i j)
          pure (D.updateRow i (Function.update (D i) j t))) D) D) =
        of fun a b => if a ∈ l then C a b - (o.map fun k => X a k * Y b k).sum else D a b := by
    intro l
    induction l with
    | nil => intro D; ext a b; simp
    | cons c l ih =>
      intro D
      rw [List.foldlM_cons, Id.run_bind, inner, ih]
      ext a b
      by_cases ha : a = c
      · subst ha; by_cases hl : a ∈ l <;> simp [hl]
      · by_cases hl : a ∈ l <;> simp [hl, ha]
  rw [mulTransposeDiff, outer]
  ext a b
  simp

/-- Reindexing along a cast `finCongr` of `Fin` commutes with the Cholesky factor. -/
private theorem cholesky_submatrix_finCongr {m k : ℕ} (h : m = k) (A : Matrix (Fin k) (Fin k) ℝ) :
    cholesky (A.submatrix (finCongr h) (finCongr h)) =
      (cholesky A).submatrix (finCongr h) (finCongr h) := by
  subst h
  simp

/-- **Algorithm 4.2.3** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive definite and let $r > 0$. Then Algorithm 4.2.3 in exact arithmetic returns
the Cholesky factor `Matrix.cholesky A`.

The proof is by strong induction on $n$. The base case is
`GolubVanLoan.Chapter04.algorithm_4_2_1_lower_eq_cholesky`. The step compares the blocks with
(4.2.18): $G_{11}$ is the Cholesky factor of $A_{11}$, the rows of $G_{21}$ are the unique
solutions of the triangular systems with $G_{11}$, and $\tilde A = A_{22} - G_{21} G_{21}^T$ is
the positive definite Schur complement. -/
theorem algorithm_4_2_3_spec {r : ℕ} (hr : 0 < r) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : Id.run (algorithm_4_2_3 pure r hr n A) = cholesky A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [algorithm_4_2_3]
  split_ifs with h
  · exact choleskyLower_id A
  have hn : r + (n - r) = n := by omega
  set A₀ : Matrix (Fin (r + (n - r))) (Fin (r + (n - r))) ℝ :=
    A.submatrix (finCongr hn) (finCongr hn) with hA₀
  have hA₀pd : A₀.PosDef := hA.submatrix (finCongr hn).injective
  set A' := A₀.submatrix finSumFinEquiv finSumFinEquiv with hA'
  have hA'pd : A'.PosDef := hA₀pd.submatrix finSumFinEquiv.injective
  have hB : A.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn)) =
      A' := rfl
  obtain ⟨h12, h11', h21', -, hS, h11, h22⟩ := equation_4_2_18 hA₀pd
  set G' := (cholesky A₀).submatrix finSumFinEquiv finSumFinEquiv with hG'
  simp only [Id.run_bind, Id.run_pure]
  rw [hB, choleskyLower_id, solveRowsLower_id, mulTransposeDiff_id]
  have h11pd : A'.toBlocks₁₁.PosDef := hA'pd.submatrix Sum.inl_injective
  -- the rows of `G₂₁` solve `G₁₁ gᵀ = a`
  have hG21 : (of fun i => (cholesky A'.toBlocks₁₁).forwardSubst (A'.toBlocks₂₁ i)) =
      G'.toBlocks₂₁ := by
    ext i j
    have hx : cholesky A'.toBlocks₁₁ *ᵥ G'.toBlocks₂₁ i = A'.toBlocks₂₁ i := by
      ext k
      rw [h21', ← h11]
      simp only [mulVec, dotProduct, Matrix.mul_apply, transpose_apply]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [of_apply, forwardSubst_eq_of_mulVec_eq _ (isLowerTriangular_cholesky _)
      (fun k => (cholesky_diag_pos h11pd k).ne') hx]
  -- the updated block is the Schur complement, which is positive definite
  have hÃ : (of fun i j => A'.toBlocks₂₂ i j -
      ((List.finRange r).map fun k => G'.toBlocks₂₁ i k * G'.toBlocks₂₁ j k).sum) =
      A'.toBlocks₂₂ - G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ := by
    ext i j
    rw [of_apply, ← Fin.sum_univ_def, Matrix.sub_apply, Matrix.mul_apply]
    rfl
  have hsym : A'.toBlocks₁₂ = A'.toBlocks₂₁ᵀ := by
    ext i j
    have := hA'pd.1.apply (Sum.inl i) (Sum.inr j)
    simpa [toBlocks₁₂, toBlocks₂₁] using this.symm
  have hSpd : (A'.toBlocks₂₂ - A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ).PosDef := by
    have := hA'pd.schurComplement
    rwa [schurComplement_eq, hsym] at this
  rw [hG21, hÃ, hS, ih (n - r) (by omega) hSpd, ← h11, ← h22, ← h12, fromBlocks_toBlocks, hG',
    hA₀, cholesky_submatrix_finCongr]
  ext i j
  simp

/-- For $A \in \mathbb{R}^{Nr \times Nr}$, block indices $i$ and $j$, and
$X \in \mathbb{R}^{r \times r}$, `updateBlock A i j X` is the matrix $A$ with its block $A_{ij}$
in the blocking (4.2.19) of [golub2013matrix] replaced by $X$.

The blocks are read along `finProdFinEquiv`, as in `GolubVanLoan.Chapter04.blockOf`. -/
def updateBlock {N r : ℕ} (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) (i j : Fin N)
    (X : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
  of fun a b => if (finProdFinEquiv.symm a).1 = i ∧ (finProdFinEquiv.symm b).1 = j then
    X (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm b).2 else A a b

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One block step of Algorithm 4.2.4 of [golub2013matrix], for the block pair $(i, j)$ with
$i \ge j$. The step computes $S = A_{ij} - \sum_{k=1}^{j-1} G_{ik} G_{jk}^T$. If $i = j$, it
computes the Cholesky factorization $S = G_{jj} G_{jj}^T$; otherwise it solves
$G_{ij} G_{jj}^T = S$ for $G_{ij}$. Then it overwrites $A_{ij}$ with $G_{ij}$.

The matrix $S$ is formed by running differences over the pairs $(k, s)$ with $k < j$ of the
block columns already overwritten (`GolubVanLoan.Chapter04.mulTransposeDiff`). The Cholesky
factor is `GolubVanLoan.Chapter04.choleskyLower`, and the solve is row by row by Algorithm 3.1.3
(`GolubVanLoan.Chapter04.solveRowsLower`) with the stored block $G_{jj}$. -/
noncomputable def blockCholeskyStep {N r : ℕ} (j i : Fin N)
    (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) : M (Matrix (Fin (N * r)) (Fin (N * r)) ℝ) := do
  let S ← mulTransposeDiff rnd ((List.finRange N).filter (· < j) ×ˢ List.finRange r)
    (blockOf A i j) (of fun p ks => A (finProdFinEquiv (i, p)) (finProdFinEquiv ks))
    (of fun q ks => A (finProdFinEquiv (j, q)) (finProdFinEquiv ks))
  let G ← (if i = j then choleskyLower rnd S else solveRowsLower rnd (blockOf A j j) S)
  pure (updateBlock A i j G)

/-- **Algorithm 4.2.4** of [golub2013matrix] (nonrecursive block Cholesky). Given a symmetric
positive definite $A \in \mathbb{R}^{n \times n}$ with $n = Nr$ and the blocking (4.2.19), the
algorithm computes a lower triangular $G \in \mathbb{R}^{n \times n}$ such that $A = GG^T$. The
lower triangular part of $A$ is overwritten by the lower triangular part of $G$.
```
for j = 1:N
    for i = j:N
        Compute S = A_ij − ∑_{k=1}^{j−1} G_ik G_jkᵀ.
        if i = j
            Compute Cholesky factorization S = G_jj G_jjᵀ.
        else
            Solve G_ij G_jjᵀ = S for G_ij.
        end
        A_ij = G_ij
    end
end
```

The input is `Matrix (Fin (N * r)) (Fin (N * r)) ℝ`, and its blocks
`GolubVanLoan.Chapter04.blockOf A i j` are read along `finProdFinEquiv`. The loop body is
`GolubVanLoan.Chapter04.blockCholeskyStep`. The diagonal blocks store the lower triangle of the
factor, so their strict upper triangles are set to zero. -/
noncomputable def algorithm_4_2_4 (N r : ℕ) (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :
    M (Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :=
  (List.finRange N).foldlM (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) (j : Fin N) =>
    ((List.finRange N).filter (j ≤ ·)).foldlM
      (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) (i : Fin N) => blockCholeskyStep rnd j i A)
      A) A

end Programs

/-- The matrix whose blocks $(i, k)$ with $P(i, k)$ true are those of $G$, and whose other blocks
are those of $A$. -/
private def blockMix {N r : ℕ} (A G : Matrix (Fin (N * r)) (Fin (N * r)) ℝ)
    (P : Fin N → Fin N → Bool) : Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
  of fun a b => if P (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1 then G a b else A a b

private theorem blockMix_apply {N r : ℕ} (A G : Matrix (Fin (N * r)) (Fin (N * r)) ℝ)
    (P : Fin N → Fin N → Bool) (i k : Fin N) (p q : Fin r) :
    blockMix A G P (finProdFinEquiv (i, p)) (finProdFinEquiv (k, q)) =
      if P i k then G (finProdFinEquiv (i, p)) (finProdFinEquiv (k, q))
      else A (finProdFinEquiv (i, p)) (finProdFinEquiv (k, q)) := by
  simp only [blockMix, of_apply, Equiv.symm_apply_apply]

private theorem blockOf_blockMix {N r : ℕ} (A G : Matrix (Fin (N * r)) (Fin (N * r)) ℝ)
    (P : Fin N → Fin N → Bool) (i k : Fin N) :
    blockOf (blockMix A G P) i k = if P i k then blockOf G i k else blockOf A i k := by
  ext p q
  simp only [blockOf, of_apply, blockMix_apply]
  split_ifs <;> rfl

private theorem updateBlock_blockMix {N r : ℕ} (A G : Matrix (Fin (N * r)) (Fin (N * r)) ℝ)
    (P : Fin N → Fin N → Bool) (i j : Fin N) :
    updateBlock (blockMix A G P) i j (blockOf G i j) =
      blockMix A G fun a b => P a b || (a == i && b == j) := by
  ext a b
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp only [updateBlock, of_apply, Equiv.symm_apply_apply, blockMix_apply, blockOf,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  by_cases h : a₁ = i ∧ b₁ = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left (Or.inr ⟨rfl, rfl⟩)]
  · rw [ite_eq_right h]
    by_cases hP : P a₁ b₁ = true
    · rw [ite_eq_left hP, ite_eq_left (Or.inl hP)]
    · rw [ite_eq_right hP, ite_eq_right (by tauto)]

/-- In exact arithmetic, the step of Algorithm 4.2.4 for the block pair $(i, j)$ overwrites the
block $(i, j)$ with the Cholesky factor of $S = A_{ij} - \sum_{k<j} G_{ik} G_{jk}^T$ if $i = j$,
and with the row-wise forward substitution solution of $X A_{jj}^T = S$ otherwise. -/
private theorem blockCholeskyStep_id {N r : ℕ} (j i : Fin N)
    (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :
    Id.run (blockCholeskyStep (M := Id) pure j i A) = updateBlock A i j
      (if i = j then cholesky (of fun a b => blockOf A i j a b -
          (((List.finRange N).filter (· < j) ×ˢ List.finRange r).map fun ks =>
            A (finProdFinEquiv (i, a)) (finProdFinEquiv ks) *
              A (finProdFinEquiv (j, b)) (finProdFinEquiv ks)).sum)
        else of fun a => (blockOf A j j).forwardSubst ((of fun a b => blockOf A i j a b -
          (((List.finRange N).filter (· < j) ×ˢ List.finRange r).map fun ks =>
            A (finProdFinEquiv (i, a)) (finProdFinEquiv ks) *
              A (finProdFinEquiv (j, b)) (finProdFinEquiv ks)).sum) a)) := by
  rw [blockCholeskyStep, Id.run_bind, mulTransposeDiff_id, Id.run_bind, Id.run_pure]
  congr 1
  split_ifs
  · exact choleskyLower_id _
  · exact solveRowsLower_id _ _

/-- **Algorithm 4.2.4** of [golub2013matrix], exact correctness. Let $n = Nr$ and let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. Then the lower triangle of the
output of Algorithm 4.2.4 in exact arithmetic is the Cholesky factor `Matrix.cholesky A`.

The proof is by induction over the block columns, and within a column over the block rows, with
the invariant that the blocks already visited are those of $G$. The block $S$ is then
$A_{ij} - \sum_{k<j} G_{ik} G_{jk}^T$, whose Cholesky factor is $G_{jj}$ and for which
$G_{ij} G_{jj}^T = S$ by (4.2.19); the solution of the triangular system is unique. The lower
triangle of the output `F` is `F - F.strictUpper`. -/
theorem algorithm_4_2_4_spec {N r : ℕ} {A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ}
    (hA : A.PosDef) :
    Id.run (algorithm_4_2_4 pure N r A) - (Id.run (algorithm_4_2_4 pure N r A)).strictUpper =
      cholesky A := by
  have h19 := equation_4_2_19 hA
  have hsorted := List.pairwise_lt_finRange N
  -- the invariant of the column loop
  have hcol : ∀ (p : List (Fin N)) (j : Fin N) (q : List (Fin N)), List.finRange N = p ++ j :: q →
      ((List.finRange N).filter (j ≤ ·)).foldl
        (fun s i => Id.run (blockCholeskyStep (M := Id) pure j i s))
        (blockMix A (cholesky A) fun i k => decide (k ∈ p ∧ k ≤ i)) =
        blockMix A (cholesky A) fun i k => decide (k ∈ p ++ [j] ∧ k ≤ i) := by
    intro p j q hpq
    have hp : ∀ k, k ∈ p ↔ k < j := fun k => by
      refine ⟨fun hk => ?_, fun hk => List.mem_prefix_of_pairwise hsorted hpq
        (List.mem_finRange k) (ne_of_lt hk) (lt_asymm hk)⟩
      have hs := hsorted
      rw [hpq] at hs
      exact (List.pairwise_append.1 hs).2.2 k hk j List.mem_cons_self
    set L := (List.finRange N).filter (j ≤ ·) with hLdef
    have hLmem : ∀ i, i ∈ L ↔ j ≤ i := fun i => by simp [hLdef]
    have hLsorted : L.Pairwise (· < ·) := hsorted.filter _
    have hLnodup : L.Nodup := (List.nodup_finRange N).filter _
    have e0 : (fun i k => decide (k ∈ p ∧ k ≤ i)) =
        fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ ([] : List (Fin N)))) := by
      funext i k
      simp
    have e1 : (fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ L))) =
        fun i k => decide (k ∈ p ++ [j] ∧ k ≤ i) := by
      funext i k
      simp only [hLmem, List.mem_append, List.mem_singleton, decide_eq_decide]
      constructor
      · rintro (⟨hk, hki⟩ | ⟨rfl, hki⟩)
        · exact ⟨Or.inl hk, hki⟩
        · exact ⟨Or.inr rfl, hki⟩
      · rintro ⟨hk | rfl, hki⟩
        · exact Or.inl ⟨hk, hki⟩
        · exact Or.inr ⟨rfl, hki⟩
    rw [e0, ← e1]
    refine List.foldl_prefix_induction (l := L) _ (fun p' s => s = blockMix A (cholesky A)
      fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p'))) rfl fun p' i q' hL s hs => ?_
    subst hs
    have hiL : j ≤ i := (hLmem i).1 (by rw [hL]; simp)
    have hip' : i ∉ p' := by
      have hn := hLnodup
      rw [hL] at hn
      exact fun h => (List.nodup_append.1 hn).2.2 i h i List.mem_cons_self rfl
    -- the entries read by the step
    have hG : ∀ (a k : Fin N), k < j → j ≤ a → ∀ (x y : Fin r),
        blockMix A (cholesky A) (fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p')))
          (finProdFinEquiv (a, x)) (finProdFinEquiv (k, y)) =
          cholesky A (finProdFinEquiv (a, x)) (finProdFinEquiv (k, y)) := by
      intro a k hk hja x y
      rw [blockMix_apply, ite_eq_left]
      simp [(hp k).2 hk, hk.le.trans hja]
    have hij : blockOf (blockMix A (cholesky A)
        fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p'))) i j = blockOf A i j := by
      rw [blockOf_blockMix, ite_eq_right]
      simp [hip', hp]
    have hnd : ((List.finRange N).filter (· < j) ×ˢ List.finRange r).Nodup :=
      ((List.nodup_finRange N).filter _).product (List.nodup_finRange r)
    have hfs : ((List.finRange N).filter (· < j) ×ˢ List.finRange r).toFinset =
        Finset.univ.filter (· < j) ×ˢ Finset.univ := by
      ext ⟨k, t⟩
      simp
    have hS : (of fun a b => blockOf (blockMix A (cholesky A)
        fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p'))) i j a b -
          (((List.finRange N).filter (· < j) ×ˢ List.finRange r).map fun ks =>
            blockMix A (cholesky A) (fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p')))
              (finProdFinEquiv (i, a)) (finProdFinEquiv ks) *
            blockMix A (cholesky A) (fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p')))
              (finProdFinEquiv (j, b)) (finProdFinEquiv ks)).sum) =
        blockOf A i j - ∑ k ∈ Finset.univ.filter (· < j),
          blockOf (cholesky A) i k * (blockOf (cholesky A) j k)ᵀ := by
      rw [hij]
      ext a b
      rw [of_apply, ← List.sum_toFinset _ hnd, hfs, Finset.sum_product, Matrix.sub_apply,
        Matrix.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkj : k < j := (Finset.mem_filter.1 hk).2
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hG i k hkj hiL a y, hG j k hkj le_rfl b y]
      simp [blockOf]
    have e2 : (fun a b => decide ((b ∈ p ∧ b ≤ a) ∨ (b = j ∧ a ∈ p')) || (a == i && b == j)) =
        fun a b => decide ((b ∈ p ∧ b ≤ a) ∨ (b = j ∧ a ∈ p' ++ [i])) := by
      funext a b
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
        List.mem_append, List.mem_singleton]
      tauto
    change _ = blockMix A (cholesky A)
      fun a b => decide ((b ∈ p ∧ b ≤ a) ∨ (b = j ∧ a ∈ p' ++ [i]))
    rw [← e2, ← updateBlock_blockMix, blockCholeskyStep_id, hS]
    congr 1
    by_cases hij' : i = j
    · subst hij'
      rw [ite_eq_left rfl, (h19 i i).2.2.1]
    · have hji : j < i := lt_of_le_of_ne hiL (Ne.symm hij')
      have hjp' : j ∈ p' := List.mem_prefix_of_pairwise hLsorted hL ((hLmem j).2 le_rfl)
        (Ne.symm hij') (lt_asymm hji)
      rw [ite_eq_right hij', blockOf_blockMix, ite_eq_left (by simp [hjp'])]
      have hlow : (blockOf (cholesky A) j j).IsLowerTriangular := by
        rw [(h19 j j).2.2.1]
        exact isLowerTriangular_cholesky _
      have hdiag : ∀ x, blockOf (cholesky A) j j x x ≠ 0 := fun x =>
        (cholesky_diag_pos hA (finProdFinEquiv (j, x))).ne'
      ext a b
      have hx : blockOf (cholesky A) j j *ᵥ blockOf (cholesky A) i j a = (blockOf A i j -
          ∑ k ∈ Finset.univ.filter (· < j),
            blockOf (cholesky A) i k * (blockOf (cholesky A) j k)ᵀ) a := by
        rw [← (h19 i j).2.2.2 hji]
        ext c
        simp only [mulVec, dotProduct, Matrix.mul_apply, transpose_apply]
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _
      rw [of_apply, forwardSubst_eq_of_mulVec_eq _ hlow hdiag hx]
  have hfin : (List.finRange N).foldl (fun s j => ((List.finRange N).filter (j ≤ ·)).foldl
      (fun s i => Id.run (blockCholeskyStep (M := Id) pure j i s)) s) A =
      blockMix A (cholesky A) fun i k => decide (k ∈ List.finRange N ∧ k ≤ i) :=
    List.foldl_prefix_induction (l := List.finRange N) _
      (fun p s => s = blockMix A (cholesky A) fun i k => decide (k ∈ p ∧ k ≤ i))
      (by ext a b; simp [blockMix]) fun p j q hpq s hs => by
        subst hs
        exact hcol p j q hpq
  rw [algorithm_4_2_4, List.idRun_foldlM]
  simp only [List.idRun_foldlM]
  rw [hfin]
  ext a b
  obtain ⟨⟨i, p⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨k, q⟩, rfl⟩ := finProdFinEquiv.surjective b
  rw [Matrix.sub_apply]
  by_cases hlt : finProdFinEquiv (i, p) < finProdFinEquiv (k, q)
  · simp only [strictUpper, of_apply, ite_eq_left hlt, sub_self]
    exact (isLowerTriangular_cholesky A (OrderDual.toDual_lt_toDual.2 hlt)).symm
  · simp only [strictUpper, of_apply, ite_eq_right hlt, sub_zero]
    have hki : k ≤ i := not_lt.1 fun h => hlt (finProdFinEquiv_lt_finProdFinEquiv_iff.2 (Or.inl h))
    rw [blockMix_apply, ite_eq_left (by simp [hki])]

/-! ### Algorithm 4.2.2: the exact specification ((4.2.16), (4.2.17)) -/

/-- One elimination step of Algorithm 4.2.2 of [golub2013matrix] in exact arithmetic. For an index
$k$ and $A \in \mathbb{R}^{n \times n}$, the result has the entries
$$a_{il} - a_{ik} a_{lk} / a_{kk} \quad (i, l > k), \qquad a_{ik} / a_{kk} \quad (i > k, \ l =
  k),$$
and $a_{il}$ elsewhere.

The step contains no interchange. If $a_{kk} = 0$, the quotients are $0$, by the convention
$x / 0 = 0$. -/
noncomputable def pivotElim (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i l => if k < i ∧ k < l then A i l - A i k * A l k / A k k
    else if l = k ∧ k < i then A i k / A k k else A i l

/-- A loop that writes one entry of a fixed column $k$ per row, with values $w_i$ that do not depend
on the state, sets the entries $(i, k)$ for the rows $i$ of the list to $w_i$ and keeps the
other entries. -/
private theorem foldl_updateRow_col_const (k : Fin n) (w : Fin n → ℝ) (L : List (Fin n))
    (D : Matrix (Fin n) (Fin n) ℝ) :
    L.foldl (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        B.updateRow i (Function.update (B i) k (w i))) D =
      of fun a b => if b = k ∧ a ∈ L then w a else D a b := by
  induction L generalizing D with
  | nil => ext a b; simp
  | cons c L ih =>
    rw [List.foldl_cons, ih]
    ext a b
    by_cases ha : a = c
    · subst ha
      by_cases hb : b = k <;> simp [hb]
    · by_cases hb : b = k <;> simp [hb, ha]

/-- A loop over a duplicate-free list of columns $l$ that subtracts $w_l$ from the entry $(i, l)$
subtracts $w_l$ exactly at those entries. -/
private theorem foldl_updateRow_sub (i : Fin n) (w : Fin n → ℝ) {L : List (Fin n)}
    (hL : L.Nodup) (D : Matrix (Fin n) (Fin n) ℝ) :
    L.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) =>
        C.updateRow i (Function.update (C i) l (C i l - w l))) D =
      of fun a b => if a = i ∧ b ∈ L then D a b - w b else D a b := by
  rw [List.foldl_lens (fun C : Matrix (Fin n) (Fin n) ℝ => C i) (fun C r => C.updateRow i r)
      (by simp) (by simp [updateRow_idem]) (by simp [updateRow_eq_self])
      (fun v l => Function.update v l (v l - w l)),
    List.foldl_update_of_nodup hL (fun l v => v l - w l) fun _ _ _ _ _ h => by rw [h]]
  ext a b
  by_cases ha : a = i
  · subst ha; simp
  · simp [ha]

/-- The rank-one update loop over a duplicate-free list of rows and columns subtracts $w_{al}$ from
exactly the entries $(a, l)$ with $a$ and $l$ in the list. -/
private theorem foldl_foldl_updateRow_sub (w : Fin n → Fin n → ℝ) {L : List (Fin n)}
    (hL : L.Nodup) (D : Matrix (Fin n) (Fin n) ℝ) :
    L.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
      L.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) =>
        C.updateRow i (Function.update (C i) l (C i l - w i l))) C) D =
      of fun a b => if a ∈ L ∧ b ∈ L then D a b - w a b else D a b := by
  suffices h : ∀ (L' : List (Fin n)), L'.Nodup → ∀ D : Matrix (Fin n) (Fin n) ℝ,
      L'.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        L.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) =>
          C.updateRow i (Function.update (C i) l (C i l - w i l))) C) D =
        of fun a b => if a ∈ L' ∧ b ∈ L then D a b - w a b else D a b from h L hL D
  intro L' hL'
  induction L' with
  | nil => intro D; ext a b; simp
  | cons c L' ih =>
    intro D
    rcases List.nodup_cons.1 hL' with ⟨hc, hL''⟩
    rw [List.foldl_cons, foldl_updateRow_sub c (w c) hL, ih hL'']
    ext a b
    by_cases ha : a = c
    · subst ha
      simp [hc]
    · simp [ha]

/-- In exact arithmetic, step $k$ of Algorithm 4.2.2 interchanges rows and columns $k$ and $j$ of
the state, where $j$ is `GolubVanLoan.Chapter04.diagPivot` of the state at $k$, then applies
`GolubVanLoan.Chapter04.pivotElim` at $k$, and records $\mathrm{piv}(k) = j$. -/
theorem ldltPivotStep_id (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) (k : Fin n) :
    Id.run (ldltPivotStep (M := Id) pure st k) =
      (pivotElim k (st.1.submatrix (Equiv.swap k (diagPivot st.1 k))
        (Equiv.swap k (diagPivot st.1 k))), Function.update st.2 k (diagPivot st.1 k)) := by
  simp only [ldltPivotStep, Id.run_bind, Id.run_pure, List.idRun_foldlM]
  rw [foldl_updateRow_col_const, foldl_foldl_updateRow_sub _ ((List.nodup_finRange n).filter _)]
  congr 1
  ext a b
  simp only [pivotElim, of_apply, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  by_cases hab : k < a ∧ k < b
  · rw [ite_eq_left hab, ite_eq_left hab, ite_eq_right (fun h => (ne_of_gt hab.2) h.1)]
  · rw [ite_eq_right hab, ite_eq_right hab]


/-- The unit lower triangular factor $L_k$ of (4.2.16) of [golub2013matrix], after $k$ steps of
Algorithm 4.2.2. For a packed state $S$, $L_k$ has the entry $s_{ij}$ at the positions $(i, j)$
with $j < k$ and $j < i$, ones on the diagonal, and zeros elsewhere.

The index $k$ counts steps, and the column indices $j < k$ are 0-based. -/
def pivotedLower (k : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (j : ℕ) < k ∧ j < i then S i j else if i = j then 1 else 0

/-- The middle factor $\operatorname{diag}(D_k, A_k)$ of (4.2.16) of [golub2013matrix], after $k$
steps of Algorithm 4.2.2. For a packed state $S$, it has the diagonal entries $d_1, \dots, d_k$
of $S$ in the first $k$ positions, the trailing block $A_k = S(k{+}1{:}n, k{+}1{:}n)$, and zeros
elsewhere. -/
def pivotedMiddle (k : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (i : ℕ) < k ∨ (j : ℕ) < k then (if i = j then S i j else 0) else S i j

/-- For a symmetric permutation $\sigma$ that fixes the first $k$ indices and maps the other indices
to indices at or after $k$, $L_k$ of the permuted state is $L_k$ of the state, permuted by
$\sigma$. -/
private theorem pivotedLower_submatrix {k : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (h1 : ∀ m : Fin n, (m : ℕ) < k → σ m = m)
    (h2 : ∀ m : Fin n, k ≤ (m : ℕ) → k ≤ (σ m : ℕ)) :
    pivotedLower k (S.submatrix σ σ) = (pivotedLower k S).submatrix σ σ := by
  ext i l
  simp only [pivotedLower, of_apply, submatrix_apply, σ.injective.eq_iff]
  by_cases hl : (l : ℕ) < k
  · have hli : l < i ↔ l < σ i := by
      by_cases hi : (i : ℕ) < k
      · rw [h1 i hi]
      · have := h2 i (not_lt.1 hi)
        simp only [Fin.lt_def]
        omega
    rw [h1 l hl]
    simp only [hli]
  · have hσl : ¬ ((σ l : ℕ) < k) := not_lt.2 (h2 l (not_lt.1 hl))
    simp [hl, hσl]

/-- For a symmetric permutation $\sigma$ that fixes the first $k$ indices and maps the other indices
to indices at or after $k$, $\operatorname{diag}(D_k, A_k)$ of the permuted state is that of the
state, permuted by $\sigma$. -/
private theorem pivotedMiddle_submatrix {k : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (h1 : ∀ m : Fin n, (m : ℕ) < k → σ m = m)
    (h2 : ∀ m : Fin n, k ≤ (m : ℕ) → k ≤ (σ m : ℕ)) :
    pivotedMiddle k (S.submatrix σ σ) = (pivotedMiddle k S).submatrix σ σ := by
  have hk : ∀ m : Fin n, (σ m : ℕ) < k ↔ (m : ℕ) < k := fun m =>
    ⟨fun h => by_contra fun h' => absurd h (not_lt.2 (h2 m (not_lt.1 h'))),
      fun h => by rw [h1 m h]; exact h⟩
  ext i l
  simp only [pivotedMiddle, of_apply, submatrix_apply, σ.injective.eq_iff, hk]

/-- The interchange of step $k$ with a pivot $j \ge k$ fixes the indices below $k$ and maps the
other indices to indices at or after $k$. -/
private theorem swap_fixes {k j : Fin n} (hkj : k ≤ j) :
    (∀ m : Fin n, (m : ℕ) < k → Equiv.swap k j m = m) ∧
      ∀ m : Fin n, (k : ℕ) ≤ m → (k : ℕ) ≤ (Equiv.swap k j m : ℕ) := by
  refine ⟨fun m hm => Equiv.swap_apply_of_ne_of_ne (fun h => by subst h; omega)
    (fun h => by subst h; exact absurd (Fin.le_def.1 hkj) (by omega)), fun m hm => ?_⟩
  rw [Equiv.swap_apply_def]
  split_ifs
  · exact Fin.le_def.1 hkj
  · exact le_rfl
  · exact hm

/-- The column operator of step $k$: the identity matrix with $w_i$ added at the positions $(i, k)$,
$i > k$. -/
private def colOp (k : Fin n) (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i l => if l = k ∧ k < i then w i else if i = l then 1 else 0

private theorem colOp_mul_apply (k : Fin n) (w : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (i b : Fin n) : (colOp k w * X) i b = X i b + if k < i then w i * X k b else 0 := by
  have h : ∀ a, colOp k w i a * X a b =
      (if i = a then X a b else 0) + (if a = k then (if k < i then w i * X a b else 0) else 0) := by
    intro a
    simp only [colOp, of_apply]
    by_cases hak : a = k
    · subst hak
      by_cases hi : a < i
      · simp [hi, (ne_of_gt hi)]
      · by_cases hia : i = a <;> simp [hi, hia]
    · by_cases hia : i = a <;> simp [hak, hia]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp

private theorem mul_colOp_transpose_apply (k : Fin n) (w : Fin n → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (i l : Fin n) :
    (X * (colOp k w)ᵀ) i l = X i l + if k < l then X i k * w l else 0 := by
  have h := colOp_mul_apply k w Xᵀ l i
  rw [← transpose_apply (X * (colOp k w)ᵀ), transpose_mul, transpose_transpose, h]
  simp [transpose_apply, mul_comm]

/-- The column operator with $-w$ is the inverse of the column operator with $w$. -/
private theorem colOp_neg_mul_colOp (k : Fin n) (w : Fin n → ℝ) :
    colOp k (-w) * colOp k w = 1 := by
  ext i l
  rw [colOp_mul_apply]
  by_cases hl : l = k
  · subst hl
    by_cases hi : l < i
    · simp [colOp, hi, (ne_of_gt hi)]
    · simp [colOp, hi, Matrix.one_apply]
  · simp [colOp, hl, Ne.symm hl, Matrix.one_apply]

/-- The multipliers $a_{ik} / a_{kk}$ of step $k$. -/
private noncomputable def multipliers (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun i => A i k / A k k

/-- The unit lower factor in (4.2.16): $L_{k+1} = L_k E_k$, where $E_k$ is the column operator of
the multipliers of step $k$. -/
private theorem pivotedLower_succ (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    pivotedLower ((k : ℕ) + 1) (pivotElim k A) =
      pivotedLower k A * colOp k (multipliers k A) := by
  ext i l
  rw [Matrix.mul_apply]
  by_cases hl : l = k
  · subst hl
    rw [Finset.sum_eq_single i]
    · by_cases hi : l < i
      · simp only [pivotedLower, pivotElim, colOp, multipliers, of_apply, lt_irrefl, hi,
          Nat.lt_succ_self, and_self, and_false, ite_true, ite_false, one_mul]
      · simp only [pivotedLower, pivotElim, colOp, of_apply, lt_irrefl, hi, and_false,
          ite_true, ite_false, one_mul]
    · intro a _ hai
      by_cases ha : a < l
      · simp only [colOp, of_apply, lt_asymm ha, ne_of_lt ha, and_false, ite_false, mul_zero]
      · have ha' : ¬ ((a : ℕ) < l) := fun h => ha (Fin.lt_def.2 h)
        simp only [pivotedLower, of_apply, ha', false_and, ite_false, Ne.symm hai, zero_mul]
    · simp
  · rw [Finset.sum_eq_single l]
    · have hkl' : (l : ℕ) ≠ k := fun h => hl (Fin.ext h)
      by_cases hlk : (l : ℕ) < k
      · have hkl : ¬ k < l := fun h => absurd (Fin.lt_def.1 h) (by omega)
        have hl1 : (l : ℕ) < k + 1 := by omega
        simp only [pivotedLower, pivotElim, colOp, of_apply, hl, hlk, hl1, hkl, true_and,
          false_and, and_false, ite_false, ite_true, mul_one]
      · have hkl : ¬ (l : ℕ) < k + 1 := by omega
        simp only [pivotedLower, colOp, of_apply, hl, hlk, hkl, false_and, ite_false, ite_true,
          mul_one]
    · intro a _ hal
      simp only [colOp, of_apply, hl, hal, false_and, ite_false, mul_zero]
    · simp

/-- The middle factor in (4.2.16): $\operatorname{diag}(D_k, A_k) = E_k \operatorname{diag}(D_{k+1},
A_{k+1}) E_k^T$, provided that a zero pivot has a zero column below it and that the entries
$(k, i)$ and $(i, k)$, $i > k$, agree. -/
private theorem pivotedMiddle_eq (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ)
    (h0 : A k k = 0 → ∀ i, k < i → A i k = 0) (hsym : ∀ i, k < i → A k i = A i k) :
    pivotedMiddle k A = colOp k (multipliers k A) * pivotedMiddle ((k : ℕ) + 1) (pivotElim k A) *
      (colOp k (multipliers k A))ᵀ := by
  ext i l
  rw [mul_colOp_transpose_apply, colOp_mul_apply, colOp_mul_apply]
  have hk1 : ¬ (k : ℕ) < k := lt_irrefl _
  have hk2 : (k : ℕ) < k + 1 := Nat.lt_succ_self _
  rcases lt_trichotomy i k with hi | rfl | hi
  · have hi' : (i : ℕ) < k := Fin.lt_def.1 hi
    have hik : ¬ k < i := lt_asymm hi
    have hne : i ≠ k := ne_of_lt hi
    simp [pivotedMiddle, pivotElim, hi, hi.le, hik, hne]
  · rcases lt_trichotomy l i with hl | rfl | hl
    · have hl' : (l : ℕ) < i := Fin.lt_def.1 hl
      simp [pivotedMiddle, pivotElim, hl, lt_asymm hl, ne_of_gt hl]
    · simp [pivotedMiddle, pivotElim]
    · have hl' : ¬ (l : ℕ) < i + 1 := by have := Fin.lt_def.1 hl; omega
      have hl'' : ¬ (l : ℕ) < i := by have := Fin.lt_def.1 hl; omega
      simp only [pivotedMiddle, pivotElim, multipliers, of_apply, hl, hl', hl'', hk1, hk2,
        lt_irrefl, ne_of_lt hl, and_false, or_false, ↓reduceIte, or_true, zero_add, add_zero]
      by_cases h : A i i = 0
      · rw [h, hsym l hl, h0 h l hl]
        simp
      · rw [hsym l hl]
        field_simp
  · have hi' : ¬ (i : ℕ) < k := by have := Fin.lt_def.1 hi; omega
    have hi'' : ¬ (i : ℕ) < k + 1 := by have := Fin.lt_def.1 hi; omega
    rcases lt_trichotomy l k with hl | rfl | hl
    · have hl' : (l : ℕ) < k := Fin.lt_def.1 hl
      simp [pivotedMiddle, pivotElim, hl, hl.le, lt_asymm hl, ne_of_gt hl,
        ne_of_gt (hl.trans hi)]
    · simp only [pivotedMiddle, pivotElim, multipliers, of_apply, hi, hi', hi'', hk1, hk2,
        lt_irrefl, ne_of_gt hi, and_false, or_false, ↓reduceIte, or_true, zero_add, add_zero,
        and_self]
      by_cases h : A l l = 0
      · rw [h, h0 h i hi]
        simp
      · field_simp
    · have hl' : ¬ (l : ℕ) < k := by have := Fin.lt_def.1 hl; omega
      have hl'' : ¬ (l : ℕ) < k + 1 := by have := Fin.lt_def.1 hl; omega
      simp only [pivotedMiddle, pivotElim, multipliers, of_apply, hi, hl, hi', hi'', hl', hl'',
        hk2, lt_irrefl, ne_of_gt hi, ne_of_lt hl, and_false, or_false, ↓reduceIte, or_true,
        zero_add, mul_zero, add_zero, and_self]
      by_cases h : A k k = 0
      · simp [h]
      · field_simp
        ring

/-- The pivot of step $k$ is at or after $k$, and its diagonal entry is the largest among the
diagonal entries at or after $k$. -/
private theorem diagPivot_spec (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    k ≤ diagPivot A k ∧ ∀ i, k ≤ i → A i i ≤ A (diagPivot A k) (diagPivot A k) := by
  have key : ∀ (l : List (Fin n)) (b : Fin n), k ≤ b → (∀ i ∈ l, k ≤ i) →
      k ≤ l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b ∧
        A b b ≤ A (l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b)
          (l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b) ∧
        ∀ i ∈ l, A i i ≤ A (l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b)
          (l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b) := by
    intro l
    induction l with
    | nil => intro b hb _; exact ⟨hb, le_rfl, by simp⟩
    | cons c l ih =>
      intro b hb hl
      rw [List.foldl_cons]
      by_cases h : A b b < A c c
      · rw [ite_eq_left h]
        obtain ⟨h1, h2, h3⟩ := ih c (hl c List.mem_cons_self)
          fun i hi => hl i (List.mem_cons_of_mem _ hi)
        refine ⟨h1, h.le.trans h2, fun i hi => ?_⟩
        rcases List.mem_cons.1 hi with rfl | hi
        · exact h2
        · exact h3 i hi
      · rw [ite_eq_right h]
        obtain ⟨h1, h2, h3⟩ := ih b hb fun i hi => hl i (List.mem_cons_of_mem _ hi)
        refine ⟨h1, h2, fun i hi => ?_⟩
        rcases List.mem_cons.1 hi with rfl | hi
        · exact (not_lt.1 h).trans h2
        · exact h3 i hi
  obtain ⟨h1, -, h3⟩ := key ((List.finRange n).filter (k ≤ ·)) k le_rfl
    fun i hi => by simpa using hi
  exact ⟨h1, fun i hi => h3 i (by simp [hi])⟩

/-- The invariant (4.2.16) of Algorithm 4.2.2 after the steps of a prefix of $0, \dots, n-1$. -/
private theorem ldltPivot_invariant {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (l : List (Fin n)) (hl : l <+: List.finRange n) :
    A.submatrix
        (Chapter03.pivPermUpTo
          (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i)).2
          l.length)
        (Chapter03.pivPermUpTo
          (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i)).2
          l.length) =
      pivotedLower l.length (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
          (A, fun i => i)).1 *
        pivotedMiddle l.length (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
          (A, fun i => i)).1 *
        (pivotedLower l.length (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
          (A, fun i => i)).1)ᵀ ∧
      (pivotedMiddle l.length (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
          (A, fun i => i)).1).PosSemidef ∧
      ∀ i j : Fin n, (i : ℕ) < l.length → i ≤ j →
        (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
            (A, fun i => i)).1 j j ≤
          (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
            (A, fun i => i)).1 i i := by
  obtain ⟨rest₀, hrest₀⟩ := hl
  refine List.foldl_prefix_induction (l := l) _
    (fun pre (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) =>
    A.submatrix (Chapter03.pivPermUpTo st.2 pre.length) (Chapter03.pivPermUpTo st.2 pre.length) =
      pivotedLower pre.length st.1 * pivotedMiddle pre.length st.1 *
        (pivotedLower pre.length st.1)ᵀ ∧
      (pivotedMiddle pre.length st.1).PosSemidef ∧
      ∀ i j : Fin n, (i : ℕ) < pre.length → i ≤ j → st.1 j j ≤ st.1 i i) ?_ ?_
  · refine ⟨?_, ?_, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
    · have hL : pivotedLower 0 A = 1 := by
        ext i j
        simp [pivotedLower, Matrix.one_apply]
      have hM : pivotedMiddle 0 A = A := by
        ext i j
        simp [pivotedMiddle]
      simp [Chapter03.pivPermUpTo, hL, hM]
    · have hM : pivotedMiddle 0 A = A := by
        ext i j
        simp [pivotedMiddle]
      simpa [hM] using hA
  · intro pre a rest hpre st ⟨hfac, hpsd, hdom⟩
    -- the step index is the length of the prefix
    have ha : (a : ℕ) = pre.length := by
      have hlt : pre.length < (List.finRange n).length := by
        rw [← hrest₀, hpre]
        simp
      have h1 : (List.finRange n)[pre.length]'hlt = a := by
        simp [← hrest₀, hpre]
      rw [← h1]
      simp
    rw [ldltPivotStep_id, List.length_append, List.length_singleton]
    obtain ⟨hkj, hmax⟩ := diagPivot_spec st.1 a
    set j := diagPivot st.1 a with hj
    set sw := Equiv.swap a j with hsw
    set A' := st.1.submatrix sw sw with hA'
    obtain ⟨hfix, hge⟩ := swap_fixes hkj
    rw [← ha] at hfac hpsd hdom ⊢
    -- the new permutation
    have hperm : Chapter03.pivPermUpTo (Function.update st.2 a j) ((a : ℕ) + 1) =
        Chapter03.pivPermUpTo st.2 a * sw := by
      rw [Chapter03.pivPermUpTo_succ, Function.update_self,
        Chapter03.pivPermUpTo_congr (piv' := st.2) fun m hm =>
          Function.update_of_ne (fun h => by subst h; omega) _ _]
    -- the factorization, after the interchange
    have hL' : pivotedLower a A' = (pivotedLower a st.1).submatrix sw sw :=
      pivotedLower_submatrix st.1 sw hfix hge
    have hM' : pivotedMiddle a A' = (pivotedMiddle a st.1).submatrix sw sw :=
      pivotedMiddle_submatrix st.1 sw hfix hge
    have hpsd' : (pivotedMiddle a A').PosSemidef := by
      rw [hM']
      exact hpsd.submatrix sw
    have hfac' : A.submatrix (Chapter03.pivPermUpTo st.2 a * sw)
        (Chapter03.pivPermUpTo st.2 a * sw) =
        pivotedLower a A' * pivotedMiddle a A' * (pivotedLower a A')ᵀ := by
      rw [Equiv.Perm.coe_mul, ← submatrix_submatrix, hfac, hL', hM', transpose_submatrix,
        submatrix_mul_equiv _ _ _ sw _, submatrix_mul_equiv _ _ _ sw _]
    -- the entries of the middle factor at and after the pivot
    have hmid : ∀ i l : Fin n, a ≤ i → a ≤ l → pivotedMiddle a A' i l = A' i l := by
      intro i l hi hl
      have hi' : ¬ (i : ℕ) < a := not_lt.2 (Fin.le_def.1 hi)
      have hl' : ¬ (l : ℕ) < a := not_lt.2 (Fin.le_def.1 hl)
      simp [pivotedMiddle, not_lt.2 hi, not_lt.2 hl]
    have h0 : A' a a = 0 → ∀ i, a < i → A' i a = 0 := by
      intro h i hi
      rw [← hmid a a le_rfl le_rfl] at h
      have := (hpsd'.apply_eq_zero_of_diag_eq_zero h i).2
      rwa [hmid i a hi.le le_rfl] at this
    have hsym : ∀ i, a < i → A' a i = A' i a := by
      intro i hi
      have := hpsd'.1.apply i a
      rw [hmid a i le_rfl hi.le, hmid i a hi.le le_rfl] at this
      simpa using this
    have hE := pivotedMiddle_eq a A' h0 hsym
    have hα : 0 ≤ A' a a := by
      rw [← hmid a a le_rfl le_rfl]
      exact hpsd'.diag_nonneg
    refine ⟨?_, ?_, ?_⟩
    · rw [hperm, hfac', pivotedLower_succ, hE, transpose_mul]
      simp only [Matrix.mul_assoc]
    · -- the new middle factor is congruent to the old one
      have hinv : pivotedMiddle ((a : ℕ) + 1) (pivotElim a A') =
          colOp a (-multipliers a A') * pivotedMiddle a A' *
            (colOp a (-multipliers a A'))ᵀ := by
        rw [hE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, colOp_neg_mul_colOp, Matrix.one_mul,
          Matrix.mul_assoc, ← transpose_mul, colOp_neg_mul_colOp, transpose_one, Matrix.mul_one]
      rw [hinv]
      simpa [conjTranspose_eq_transpose_of_trivial] using
        hpsd'.mul_mul_conjTranspose_same (colOp a (-multipliers a A'))
    · -- the pivots dominate the later diagonal
      have hCdiag : ∀ m : Fin n, pivotElim a A' m m ≤ A' m m := by
        intro m
        simp only [pivotElim, of_apply]
        split_ifs with h1 h2
        · have : 0 ≤ A' m a * A' m a / A' a a := div_nonneg (mul_self_nonneg _) hα
          linarith
        · exact absurd h2.1 (ne_of_gt h2.2)
        · exact le_rfl
      have hCle : ∀ m : Fin n, ¬ a < m → pivotElim a A' m m = A' m m := by
        intro m hm
        simp [pivotElim, hm]
      intro i l hi hil
      dsimp only
      refine (hCdiag l).trans ?_
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · -- an earlier pivot
        have hia : i < a := Fin.lt_def.2 hi
        rw [hCle i (lt_asymm hia)]
        change st.1 (sw l) (sw l) ≤ st.1 (sw i) (sw i)
        rw [hfix i hi]
        refine hdom i (sw l) hi ?_
        by_cases hl : (l : ℕ) < a
        · rw [hfix l hl]
          exact hil
        · exact Fin.le_def.2 (le_trans (le_of_lt hi) (hge l (not_lt.1 hl)))
      · -- the pivot just chosen
        have hia : i = a := Fin.ext hi
        subst hia
        rw [hCle i (lt_irrefl i)]
        change st.1 (sw l) (sw l) ≤ st.1 (sw i) (sw i)
        rw [hsw, Equiv.swap_apply_left]
        exact hmax _ (Fin.le_def.2 (hge l (Fin.le_def.1 hil)))


/-- **Equation (4.2.16)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive semidefinite and let $k \le n$. Let $S$ be the matrix after the first $k$ steps of
Algorithm 4.2.2 in exact arithmetic, and let $\tilde P$ be the product of the interchanges of
these steps. Then
$$\tilde P A \tilde P^T = \begin{bmatrix} L_{11} & 0 \\ L_{21} & I \end{bmatrix} \begin{bmatrix}
  D_k & 0 \\ 0 & A_k \end{bmatrix} \begin{bmatrix} L_{11} & 0 \\ L_{21} & I \end{bmatrix}^T,$$
where:
* the matrix $\operatorname{diag}(D_k, A_k)$ is positive semidefinite;
* for $i < k$ and $j \ge i$, $s_{jj} \le s_{ii}$;
* if $s_{mm} = 0$ for some $m < k$, then $A_k = 0$.

The second statement gives $d_1, \dots, d_k \ge 0$ and $A_k$ positive semidefinite. The third
says that each pivot dominates every later diagonal entry, so $d_1 \ge \dots \ge d_k$ and the
diagonal of $A_k$ is at most $d_k$. The last is the remark of the source that $A_k = 0$ as soon
as $d_k = 0$; it follows from (4.2.15), because the pivot is the largest diagonal entry. The two
factors are `GolubVanLoan.Chapter04.pivotedLower` and `GolubVanLoan.Chapter04.pivotedMiddle` of
$S$. The matrix $\tilde P A \tilde P^T$ is `A.submatrix σ σ` with
`σ = GolubVanLoan.Chapter03.pivPermUpTo piv k`, and indices are 0-based. -/
theorem equation_4_2_16 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {k : ℕ} (hk : k ≤ n) :
    let st := ((List.finRange n).take k).foldl
      (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i)
    A.submatrix (Chapter03.pivPermUpTo st.2 k) (Chapter03.pivPermUpTo st.2 k) =
        pivotedLower k st.1 * pivotedMiddle k st.1 * (pivotedLower k st.1)ᵀ ∧
      (pivotedMiddle k st.1).PosSemidef ∧
      (∀ i j : Fin n, (i : ℕ) < k → i ≤ j → st.1 j j ≤ st.1 i i) ∧
      ∀ m : Fin n, (m : ℕ) < k → st.1 m m = 0 →
        ∀ i l : Fin n, k ≤ (i : ℕ) → k ≤ (l : ℕ) → st.1 i l = 0 := by
  intro st
  have hlen : ((List.finRange n).take k).length = k := by simp [hk]
  have h := ldltPivot_invariant hA _ (List.take_prefix k _)
  rw [hlen] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, h3, fun m hm hm0 i l hi hl => ?_⟩
  have hmid : ∀ i l : Fin n, k ≤ (i : ℕ) → k ≤ (l : ℕ) → pivotedMiddle k st.1 i l = st.1 i l := by
    intro i l hi hl
    simp [pivotedMiddle, not_lt.2 hi, not_lt.2 hl]
  have hii : st.1 i i = 0 := by
    refine le_antisymm ?_ ?_
    · have := h3 m i hm (Fin.le_def.2 (by omega))
      rwa [hm0] at this
    · rw [← hmid i i hi hi]
      exact h2.diag_nonneg
  have := (h2.apply_eq_zero_of_diag_eq_zero (i := i) (by rw [hmid i i hi hi]; exact hii) l).1
  rwa [hmid i l hi hl] at this

/-- The exact run of Algorithm 4.2.2 is the fold of its exact steps. -/
private theorem algorithm_4_2_2_id (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_2_2 pure A) = (List.finRange n).foldl
      (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i) := by
  rw [algorithm_4_2_2, List.idRun_foldlM]

/-- After all $n$ steps, $L_n$ is the unit lower triangular matrix
`GolubVanLoan.Chapter03.packedL S` stored in the packed state. -/
private theorem pivotedLower_self (S : Matrix (Fin n) (Fin n) ℝ) :
    pivotedLower n S = Chapter03.packedL S := by
  ext i j
  by_cases hji : j < i
  · simp [pivotedLower, Chapter03.packedL_apply_of_lt S hji, hji]
  · rcases eq_or_lt_of_le (not_lt.1 hji) with rfl | hij
    · simp [pivotedLower, Chapter03.packedL_apply_self]
    · simp [pivotedLower, Chapter03.packedL_apply_of_lt' S hij, hji, ne_of_lt hij]

/-- After all $n$ steps, $\operatorname{diag}(D_n, A_n)$ is the diagonal of the packed state. -/
private theorem pivotedMiddle_self (S : Matrix (Fin n) (Fin n) ℝ) :
    pivotedMiddle n S = diagonal S.diag := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [pivotedMiddle]
  · simp [pivotedMiddle, hij]

/-- **Algorithm 4.2.2** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive semidefinite, and let $(F, \mathrm{piv})$ be the output of Algorithm 4.2.2
in exact arithmetic. Let $P$ be the permutation matrix of the interchanges, let $L$ be the unit
lower triangular matrix stored below the diagonal of $F$, and let $d_i = f_{ii}$. Then
$$PAP^T = L \operatorname{diag}(d_1, \dots, d_n) L^T,$$
with $L$ unit lower triangular, $d_i \ge 0$ for all $i$, $d_1 \ge d_2 \ge \dots \ge d_n$, and
$d_i > 0$ for all $i$ if $A$ is positive definite.

**Correction.** The source gives $d_n > 0$ for a semidefinite input. This fails when $A$ is
singular: then $d_n = 0$ (`GolubVanLoan.Chapter04.equation_4_2_17_algorithm`). The theorem
states $d_i \ge 0$, and $d_i > 0$ only when $A$ is positive definite.

**Reading.** The source writes $P = P_1 \cdots P_n$. Here $P$ is the product of the interchanges
in the order in which they are applied, `GolubVanLoan.Chapter03.pivPerm piv`.

The factorization is `Matrix.IsLDM`, with $PAP^T$ as `A.submatrix σ σ`, $L$ as
`GolubVanLoan.Chapter03.packedL F` and $D$ as `Matrix.diagonal F.diag`. The proof uses the
invariant `GolubVanLoan.Chapter04.equation_4_2_16` at $k = n$. -/
theorem algorithm_4_2_2_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    IsLDM (A.submatrix (Chapter03.pivPerm (Id.run (algorithm_4_2_2 pure A)).2)
        (Chapter03.pivPerm (Id.run (algorithm_4_2_2 pure A)).2))
      (Chapter03.packedL (Id.run (algorithm_4_2_2 pure A)).1)
      (diagonal (Id.run (algorithm_4_2_2 pure A)).1.diag)
      (Chapter03.packedL (Id.run (algorithm_4_2_2 pure A)).1) ∧
    (∀ i, 0 ≤ (Id.run (algorithm_4_2_2 pure A)).1 i i) ∧
    (∀ i j, i ≤ j → (Id.run (algorithm_4_2_2 pure A)).1 j j ≤
      (Id.run (algorithm_4_2_2 pure A)).1 i i) ∧
    (A.PosDef → ∀ i, 0 < (Id.run (algorithm_4_2_2 pure A)).1 i i) := by
  have h := ldltPivot_invariant hA (List.finRange n) (List.prefix_refl _)
  rw [List.length_finRange] at h
  rw [algorithm_4_2_2_id]
  generalize (List.finRange n).foldl
    (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i) = st at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  rw [pivotedLower_self, pivotedMiddle_self] at h1
  rw [pivotedMiddle_self] at h2
  have hLu : (Chapter03.packedL st.1).IsUnitLowerTriangular :=
    ⟨fun i j hij => Chapter03.packedL_apply_of_lt' st.1 (OrderDual.toDual_lt_toDual.1 hij),
      Chapter03.packedL_apply_self st.1⟩
  refine ⟨⟨hLu, isDiag_diagonal _, hLu, h1.symm⟩, fun i => ?_,
    fun i j hij => h3 i j i.isLt hij, fun hPD i => ?_⟩
  · simpa using h2.diag_nonneg (i := i)
  · -- the middle factor is congruent to `P A Pᵀ`, positive definite
    set L := Chapter03.packedL st.1 with hL
    have hdet : IsUnit L.det := by rw [hLu.det_eq_one]; exact isUnit_one
    have hX : (A.submatrix (Chapter03.pivPermUpTo st.2 n)
        (Chapter03.pivPermUpTo st.2 n)).PosDef :=
      hPD.submatrix (Chapter03.pivPermUpTo st.2 n).injective
    have hD : diagonal st.1.diag = L⁻¹ * A.submatrix (Chapter03.pivPermUpTo st.2 n)
        (Chapter03.pivPermUpTo st.2 n) * L⁻¹ᵀ := by
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul,
        Matrix.mul_assoc, ← transpose_mul, nonsing_inv_mul _ hdet, transpose_one, Matrix.mul_one]
    have hinj : Function.Injective L⁻¹.vecMul :=
      vecMul_injective_iff_isUnit.2 ((isUnit_nonsing_inv_iff).2 ((isUnit_iff_isUnit_det L).2 hdet))
    have hPDD := hX.mul_mul_conjTranspose_same hinj
    rw [conjTranspose_eq_transpose_of_trivial, ← hD] at hPDD
    simpa using hPDD.diag_pos (i := i)

/-- **Equation (4.2.17)** of [golub2013matrix], for the output of Algorithm 4.2.2. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive semidefinite of rank $r$, and let
$d_1, \dots, d_n$ be the diagonal of the output of Algorithm 4.2.2 in exact arithmetic. Then
$d_i > 0$ for $i \le r$ and $d_i = 0$ for $i > r$.

With `GolubVanLoan.Chapter04.algorithm_4_2_2_spec`, the computed $P$, $L(:, 1{:}r)$ and
$D_r = \operatorname{diag}(d_1, \dots, d_r)$ therefore realize (4.2.17):
$PAP^T = L(:, 1{:}r) D_r L(:, 1{:}r)^T$. The proof uses that the rank of $PAP^T = LDL^T$ is the
number of nonzero pivots, and that the pivots are nonnegative and nonincreasing. The Lean
statement is 0-based: $d_i > 0$ for $i < r$ and $d_i = 0$ for $r \le i$. -/
theorem equation_4_2_17_algorithm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i : Fin n) :
    ((i : ℕ) < A.rank → 0 < (Id.run (algorithm_4_2_2 pure A)).1 i i) ∧
      (A.rank ≤ i → (Id.run (algorithm_4_2_2 pure A)).1 i i = 0) := by
  obtain ⟨hLDM, hnn, hanti, -⟩ := algorithm_4_2_2_spec hA
  set F := (Id.run (algorithm_4_2_2 pure A)).1
  set σ := Chapter03.pivPerm (Id.run (algorithm_4_2_2 pure A)).2
  set L := Chapter03.packedL F
  have hdet : IsUnit L.det := by
    rw [hLDM.isUnitLowerTriangular_left.det_eq_one]
    exact isUnit_one
  have hdetT : IsUnit Lᵀ.det := by rwa [det_transpose]
  -- the rank is the number of nonzero pivots
  have hrank : A.rank = Fintype.card {j // F j j ≠ 0} := by
    rw [← rank_submatrix A σ σ, ← hLDM.mul_eq, rank_mul_eq_left_of_isUnit_det _ _ hdetT,
      rank_mul_eq_right_of_isUnit_det _ _ hdet, rank_diagonal]
    rfl
  rw [hrank, Fintype.card_subtype]
  constructor
  · intro hi
    refine lt_of_le_of_ne (hnn i) fun h0 => ?_
    have hsub : Finset.univ.filter (fun j : Fin n => F j j ≠ 0) ⊆
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < i) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra hji
      exact hj (le_antisymm (h0 ▸ hanti i j (Fin.le_def.2 (not_lt.1 hji))) (hnn j))
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt i.isLt)] at this
    omega
  · intro hi
    by_contra h0
    have hpos : 0 < F i i := lt_of_le_of_ne (hnn i) (Ne.symm h0)
    have hsub : Finset.univ.filter (fun j : Fin n => (j : ℕ) < i + 1) ⊆
        Finset.univ.filter (fun j : Fin n => F j j ≠ 0) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (lt_of_lt_of_le hpos (hanti j i (Fin.le_def.2 (by omega)))).ne'
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.succ_le_of_lt i.isLt)] at this
    omega

end GolubVanLoan.Chapter04
