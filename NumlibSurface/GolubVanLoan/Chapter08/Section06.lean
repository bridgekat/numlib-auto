/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.SingularValues
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.Jacobi
import Numlib.LinearAlgebra.Matrix.Bidiagonal
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.PlaneRotation
import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.GolubVanLoan.Chapter05.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section07
import NumlibSurface.GolubVanLoan.Chapter08.Section03
import NumlibSurface.GolubVanLoan.Chapter08.Section05

/-!
# Golub and Van Loan, Section 8.6: Computing the SVD

This module formalizes §8.6 of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with singular
values $\sigma_1(A) \ge \sigma_2(A) \ge \dots$. The SVD of $A$ is tied to the symmetric
eigenproblems of $A^T A$, $AA^T$ and the Jordan–Wielandt matrix
$\begin{bmatrix} 0 & A^T \\ A & 0 \end{bmatrix}$ by (8.6.1)–(8.6.3). Through these connections the
module states the min-max characterization of singular values (Theorem 8.6.1), their perturbation
bounds (Corollary 8.6.2 and Theorem 8.6.4, with (8.6.4)), their interlacing under the removal of a
column (Corollary 8.6.3), and the perturbation of singular subspace pairs (Theorem 8.6.5), together
with a counterexample to Theorem 8.6.5 as printed.

For the SVD algorithm of §8.6.3 the module states that $T = B^T B$ is tridiagonal for an upper
bidiagonal $B$, the rules by which a bidiagonal problem decouples, the Golub–Kahan SVD step
(Algorithm 8.6.1) and the SVD algorithm (Algorithm 8.6.2), with their exact semantics. For the
Jacobi SVD procedures of §8.6.4 it states the $2 \times 2$ SVD by two rotations and the
orthogonality condition of one-sided Jacobi. The proofs use the backbone modules
`Numlib.Analysis.Matrix.SingularValues`, `Numlib.LinearAlgebra.Matrix.SVD`,
`Numlib.LinearAlgebra.Matrix.Bidiagonal` and `Numlib.Eigen.Jacobi`.

## Main definitions

* §8.6.2, `GolubVanLoan.Chapter08.IsSingularSubspacePair`: subspaces $S \subseteq \mathbb{R}^n$ and
  $T \subseteq \mathbb{R}^m$ of equal dimension with $AS \subseteq T$ and $A^T T \subseteq S$.
* Algorithm 8.6.1, `GolubVanLoan.Chapter08.algorithm_8_6_1`: the Golub–Kahan SVD step on a
  bidiagonal matrix.
* Algorithm 8.6.2, `GolubVanLoan.Chapter08.algorithm_8_6_2`: the SVD algorithm.

## Main results

* (8.6.1)–(8.6.2), `GolubVanLoan.Chapter08.equation_8_6_1`: an SVD $U^T A V = \Sigma$ diagonalizes
  $A^T A$ and $AA^T$.
* (8.6.3), `GolubVanLoan.Chapter08.equation_8_6_3`: an SVD of $A$ gives an orthogonal
  diagonalization of the Jordan–Wielandt matrix, with eigenvalues $\pm\sigma_i$ and $m - n$ zeros.
* Theorem 8.6.1, `GolubVanLoan.Chapter08.theorem_8_6_1`: the max-min and min-max characterizations
  of $\sigma_k(A)$.
* Corollary 8.6.2, `GolubVanLoan.Chapter08.corollary_8_6_2`: $|\sigma_k(A + E) - \sigma_k(A)| \le
  \sigma_1(E) = \|E\|_2$.
* Corollary 8.6.3, `GolubVanLoan.Chapter08.corollary_8_6_3`: the singular values of the first $r$
  columns of $A$ interlace those of the first $r + 1$ columns.
* (8.6.4), `GolubVanLoan.Chapter08.equation_8_6_4`: the Jordan–Wielandt matrix of $E$ has Frobenius
  norm $\sqrt 2 \|E\|_F$ and 2-norm $\|E\|_2$.
* Theorem 8.6.4, `GolubVanLoan.Chapter08.theorem_8_6_4`: $\sum_{k=1}^n (\sigma_k(A + E) -
  \sigma_k(A))^2 \le \|E\|_F^2$.
* Theorem 8.6.5, `GolubVanLoan.Chapter08.theorem_8_6_5`: a singular subspace pair with separated
  singular values persists under a small perturbation $E$.
* Theorem 8.6.5, `GolubVanLoan.Chapter08.theorem_8_6_5_counterexample`: the theorem as printed fails
  for $m > n$.
* §8.6.3, `GolubVanLoan.Chapter08.gram_bidiagonal`: for upper bidiagonal $B$, the matrix $B^T B$ is
  symmetric tridiagonal, with explicit entries, and unreduced exactly when every $d_i f_i \ne 0$.
* §8.6.3, `GolubVanLoan.Chapter08.bidiagonal_decouple`: a zero superdiagonal entry splits $B$, and a
  zero diagonal entry can be moved by rotations into a zero row or column.
* Algorithm 8.6.1, `GolubVanLoan.Chapter08.algorithm_8_6_1_spec`: in exact arithmetic, the
  Golub–Kahan step is the implicit-shift QR step on $B^T B$, up to signs.
* Algorithm 8.6.2, `GolubVanLoan.Chapter08.algorithm_8_6_2_spec`: in exact arithmetic, the SVD
  algorithm returns $U^T (A + E) V = B$ with orthogonal $U$, $V$, a bound on $\|E\|_F$, and $B$
  diagonal if the loop stopped.
* §8.6.4, `GolubVanLoan.Chapter08.jacobiSVD_twoByTwo`: two rotations diagonalize any real
  $2 \times 2$ matrix, and the two-sided Jacobi update decreases $\operatorname{off}^2$ by
  $a_{pq}^2 + a_{qp}^2$.
* §8.6.4, `GolubVanLoan.Chapter08.oneSidedJacobi_orthogonal`: one-sided Jacobi makes two columns
  orthogonal, and orthogonal columns give the SVD by scaling.

## Conventions

* The book's $\sigma_k(A)$ for `A : Matrix (Fin m) (Fin n) ℝ` is `A.sortedSingularValues (k - 1)`,
  the sorted `LinearMap.singularValues` of `toEuclideanLin A`, indexed from $0$ and zero from the
  rank on.
* Square upper bidiagonal matrices are `Matrix.IsUpperBidiagonal`, and rectangular ones are
  `Matrix.IsUpperBidiagonalRect`.
* The Jordan–Wielandt matrix $\begin{bmatrix} 0 & A^T \\ A & 0 \end{bmatrix}$ is
  `Matrix.hermitianDilation A`, with the domain block first.
* In Theorem 8.6.5 the orthogonal matrices are given by their column blocks, $V = [V_1\ V_2]$ and
  $U = [U_1\ U_2]$, through `Matrix.fromCols`.

## Implementation notes

* Algorithms 8.6.1 and 8.6.2 follow the algorithm conventions of the library index. They use the
  `givens` of Chapter 5 (`GolubVanLoan.Chapter05.algorithm_5_1_3`) and the Givens updates on index
  lists. Algorithm 8.6.1 acts on a window of consecutive indices of the $m \times n$ array and
  accumulates $U$ and $V$. Algorithm 8.6.2 starts from the bidiagonalization of Chapter 5
  (`GolubVanLoan.Chapter05.algorithm_5_4_2`) and runs a loop of at most `fuel` passes with a flag
  `done`.
* The exact semantics of Algorithm 8.6.1, for a square $B$ and the full window, is the chase of one
  bulge, alternately below the diagonal and to the right of the superdiagonal, combined with the
  implicit-shift argument of `GolubVanLoan.Chapter08.algorithm_8_3_2_spec` for $B^T B$.
* The exact semantics of Algorithm 8.6.2 is a backward error statement, as for
  `GolubVanLoan.Chapter08.algorithm_8_3_3_spec`. Every step of Algorithm 8.6.1 and every
  zero-diagonal chase on the window of $B_{22}$ is a two-sided rotation of an array that is
  decoupled along the window, so it is the full rotation and changes only the block. The deflations,
  carried back to $A$, form the backward error.

## Deviations from the source

* **Theorem 8.6.5** (typo). The source swaps $P$ and $Q$: its $Q$ is $(n - r) \times r$. See
  `GolubVanLoan.Chapter08.theorem_8_6_5`.
* **Theorem 8.6.5** (correction). As printed, the theorem is false for $m > n$. For $m > n$ the
  declaration adds Wedin's condition $\delta \le \sigma_{\min}(A_{11})$. See
  `GolubVanLoan.Chapter08.theorem_8_6_5` and `GolubVanLoan.Chapter08.theorem_8_6_5_counterexample`.
* **Algorithm 8.6.1** (typo). The source says $B \in \mathbb{R}^{m \times n}$ for a square $B$. See
  `GolubVanLoan.Chapter08.algorithm_8_6_1`.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {m n : ℕ}

/-! ### §8.6.1 Connections to the symmetric eigenvalue problem -/

/-- **Equations (8.6.1)–(8.6.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with
$m \ge n$, let $U \in \mathbb{R}^{m \times m}$ and $V \in \mathbb{R}^{n \times n}$ be
orthogonal, and let $U^T A V = \Sigma$, where $\Sigma \in \mathbb{R}^{m \times n}$ has the
entries $\sigma_1, \dots, \sigma_n$ on its diagonal and zeros elsewhere. Then
$$V^T (A^T A) V = \operatorname{diag}(\sigma_1^2, \dots, \sigma_n^2), \qquad U^T (AA^T) U =
  \operatorname{diag}(\sigma_1^2, \dots, \sigma_n^2, 0, \dots, 0),$$
with $m - n$ zeros.

The numbers $\sigma_i$ need not be sorted or nonnegative. The matrix $\Sigma$ is
`Matrix.rectDiagonal σ` for `σ : ℕ → ℝ`, indexed from $0$. -/
theorem equation_8_6_1 {A : Matrix (Fin m) (Fin n) ℝ} (hmn : n ≤ m) {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {σ : ℕ → ℝ} (hA : Uᵀ * A * V = rectDiagonal σ) :
    Vᵀ * (Aᵀ * A) * V = diagonal (fun j : Fin n => σ j ^ 2) ∧
      Uᵀ * (A * Aᵀ) * U = diagonal (fun i : Fin m => if (i : ℕ) < n then σ i ^ 2 else 0) := by
  have hUU : U * Uᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hVV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hUU' : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU
  have hVV' : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hV
  have hAV : A * V = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) := by
    rw [← hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hUA : Uᵀ * A = (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
    rw [← hA, Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hT : (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ)ᵀ = rectDiagonal σ := by
    rw [← conjTranspose_eq_transpose_of_trivial, rectDiagonal_conjTranspose]
    rfl
  constructor
  · have e : Vᵀ * (Aᵀ * A) * V =
        (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ)ᵀ * rectDiagonal σ := by
      calc Vᵀ * (Aᵀ * A) * V = (A * V)ᵀ * (A * V) := by
            simp only [transpose_mul, Matrix.mul_assoc]
        _ = _ := by
          rw [hAV, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU', Matrix.one_mul]
    rw [e, hT, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    congr 1
    funext j
    simp [show (j : ℕ) < m by omega, sq]
  · have e : Uᵀ * (A * Aᵀ) * U =
        rectDiagonal σ * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ)ᵀ := by
      calc Uᵀ * (A * Aᵀ) * U = (Uᵀ * A) * (Uᵀ * A)ᵀ := by
            simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
        _ = _ := by
          rw [hUA, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ,
            hVV', Matrix.one_mul]
    rw [e, hT, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    congr 1
    funext i
    split_ifs <;> simp [sq]

set_option linter.unusedTactic false in
/-- The constant block matrix $M = \begin{bmatrix} I & I & 0 \\ I & -I & 0 \\ 0 & 0 & \sqrt 2 I
\end{bmatrix}$ of (8.6.3), before the scaling, satisfies $M^T M = MM^T = 2I$. -/
private theorem jw_mul_self {n p : ℕ} :
    let M : Matrix (Fin n ⊕ (Fin n ⊕ Fin p)) (Fin n ⊕ (Fin n ⊕ Fin p)) ℝ :=
      fromBlocks 1 (fromCols 1 0) (fromRows 1 0) (fromBlocks (-1) 0 0 (√2 • 1))
    Mᵀ * M = (2 : ℝ) • 1 ∧ M * Mᵀ = (2 : ℝ) • 1 := by
  intro M
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  constructor <;>
  · ext (i | i | i) (j | j | j) <;>
      first
      | (simp [M, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h2]; done)
      | (rcases eq_or_ne i j with rfl | h <;>
          [simp [M, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h2];
           simp [M, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h2, h,
               h.symm]]) <;> norm_num

/-- For the matrix $M$ of (8.6.3), $M^T \begin{bmatrix} 0 & [\Sigma\ 0] \\ [\Sigma; 0] & 0
\end{bmatrix} M = 2 \operatorname{diag}(\Sigma, -\Sigma, 0)$. -/
private theorem jw_conj {n p : ℕ} (σ : Fin n → ℝ) :
    let M : Matrix (Fin n ⊕ (Fin n ⊕ Fin p)) (Fin n ⊕ (Fin n ⊕ Fin p)) ℝ :=
      fromBlocks 1 (fromCols 1 0) (fromRows 1 0) (fromBlocks (-1) 0 0 (√2 • 1))
    Mᵀ * fromBlocks 0 (fromCols (diagonal σ) 0) (fromRows (diagonal σ) 0) 0 * M =
      (2 : ℝ) • diagonal (Sum.elim σ (Sum.elim (-σ) 0)) := by
  intro M
  ext (i | i | i) (j | j | j) <;>
    first
    | (simp [M, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, diagonal_apply]; done)
    | (rcases eq_or_ne i j with rfl | h <;>
        [simp [M, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, diagonal_apply,
            two_mul];
         simp [M, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, diagonal_apply, h]])

/-- **Equation (8.6.3)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, let
$U = [U_1\ U_2] \in \mathbb{R}^{m \times m}$ be orthogonal with
$U_1 \in \mathbb{R}^{m \times n}$ and $U_2 \in \mathbb{R}^{m \times (m - n)}$, let
$V \in \mathbb{R}^{n \times n}$ be orthogonal, and let
$$U^T A V = \begin{bmatrix} \Sigma \\ 0 \end{bmatrix}, \qquad \Sigma =
  \operatorname{diag}(\sigma_1, \dots, \sigma_n).$$
Then the matrix
$$Q = \frac{1}{\sqrt 2} \begin{bmatrix} V & V & 0 \\ U_1 & -U_1 & \sqrt 2\, U_2 \end{bmatrix}$$
satisfies $Q^T Q = QQ^T = I$ and
$$Q^T \begin{bmatrix} 0 & A^T \\ A & 0 \end{bmatrix} Q = \operatorname{diag}(\sigma_1, \dots,
  \sigma_n, -\sigma_1, \dots, -\sigma_n, 0, \dots, 0),$$
with $m - n$ zeros. So the eigenvalues of the Jordan–Wielandt matrix are the $\pm\sigma_i$ and
$m - n$ zeros.

The block rows of $Q$ have $n$ and $m$ rows, and its block columns have $n$, $n$ and $m - n$
columns. The hypotheses force $m \ge n$. The orthogonality of $U$ is stated as $U^T U = I$ and
$UU^T = I$, and the Jordan–Wielandt matrix is `Matrix.hermitianDilation A`. -/
theorem equation_8_6_3 {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin n) ℝ}
    {U₂ : Matrix (Fin m) (Fin (m - n)) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hU : (fromCols U₁ U₂)ᵀ * fromCols U₁ U₂ = 1) (hU' : fromCols U₁ U₂ * (fromCols U₁ U₂)ᵀ = 1)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {σ : Fin n → ℝ}
    (hA : (fromCols U₁ U₂)ᵀ * A * V = fromRows (diagonal σ) 0) :
    let Q : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ (Fin n ⊕ Fin (m - n))) ℝ :=
      (√2)⁻¹ • fromBlocks V (fromCols V 0) U₁ (fromCols (-U₁) (√2 • U₂))
    Qᵀ * Q = 1 ∧ Q * Qᵀ = 1 ∧
      Qᵀ * hermitianDilation A * Q = diagonal (Sum.elim σ (Sum.elim (-σ) 0)) := by
  intro Q
  set U := fromCols U₁ U₂ with hUdef
  set M : Matrix (Fin n ⊕ (Fin n ⊕ Fin (m - n))) (Fin n ⊕ (Fin n ⊕ Fin (m - n))) ℝ :=
    fromBlocks 1 (fromCols 1 0) (fromRows 1 0) (fromBlocks (-1) 0 0 (√2 • 1)) with hM
  set W : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ (Fin n ⊕ Fin (m - n))) ℝ := fromBlocks V 0 0 U
    with hW
  have hVV : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hV
  have hVV' : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hQ : Q = (√2)⁻¹ • (W * M) := by
    simp only [Q, W, M, U, fromBlocks_multiply, mul_fromCols, fromCols_mul_fromRows,
      fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.mul_neg, Matrix.mul_smul]
  have hWW : Wᵀ * W = 1 := by
    rw [hW, fromBlocks_transpose, fromBlocks_multiply, hVV, hU]
    simp
  have hWW' : W * Wᵀ = 1 := by
    rw [hW, fromBlocks_transpose, fromBlocks_multiply, hVV', hU']
    simp
  have hD : Wᵀ * hermitianDilation A * W =
      fromBlocks 0 (fromCols (diagonal σ) 0) (fromRows (diagonal σ) 0) 0 := by
    have hA' : Vᵀ * Aᵀ * U = fromCols (diagonal σ) 0 := by
      have := congrArg transpose hA
      simpa [transpose_mul, Matrix.mul_assoc, transpose_fromRows] using this
    rw [hW, hermitianDilation, conjTranspose_eq_transpose_of_trivial, fromBlocks_transpose,
      fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, transpose_zero]
    rw [hA', hA]
  obtain ⟨hMM, hMM'⟩ := jw_mul_self (n := n) (p := m - n)
  have h2 : (√2)⁻¹ * (√2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2, transpose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hWW, Matrix.one_mul, hMM, smul_smul]
    norm_num
  · rw [hQ, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2, transpose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc M, hMM', Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, hWW', smul_smul]
    norm_num
  · rw [hQ, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2,
      transpose_mul, show Mᵀ * Wᵀ * hermitianDilation A * (W * M) =
        Mᵀ * (Wᵀ * hermitianDilation A * W) * M by simp only [Matrix.mul_assoc], hD,
      jw_conj σ, smul_smul]
    norm_num

/-! ### §8.6.1 Perturbation theory -/

/-- **Theorem 8.6.1** of [golub2013matrix] (min-max characterization of singular values). Let
$A \in \mathbb{R}^{m \times n}$ and $1 \le k \le \min\{m, n\}$. Then
$$\sigma_k(A) = \max_{\dim S = k} \ \min_{0 \ne x \in S} \frac{\|Ax\|_2}{\|x\|_2}, \qquad
  \sigma_k(A) = \min_{\dim S = n - k + 1} \ \max_{0 \ne x \in S,\ 0 \ne y \in \mathbb{R}^m}
  \frac{y^T A x}{\|x\|_2 \|y\|_2},$$
where $S$ ranges over the subspaces of $\mathbb{R}^n$.

In Lean the index is 0-based: the statement is about `A.sortedSingularValues k` with $k < m$ and
$k < n$. The maximum and the minimum are stated without division. The first: $\sigma_k(A)$ is
the greatest $c$ for which some $S$ of dimension $k$ has $c\|x\|_2 \le \|Ax\|_2$ for all
$x \in S$. The second: $\sigma_k(A)$ is the least $c$ for which some $S$ of dimension
$n - k + 1$ has $y^T A x \le c \|x\|_2 \|y\|_2$ for all $x \in S$ and $y \in \mathbb{R}^m$. -/
theorem theorem_8_6_1 (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ} (hkm : k < m) (hkn : k < n) :
    IsGreatest {c : ℝ | ∃ S : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ S = k + 1 ∧
      ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖} (A.sortedSingularValues k) ∧
    IsLeast {c : ℝ | ∃ S : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ S = n - k ∧
      ∀ x ∈ S, ∀ y : Fin m → ℝ, y ⬝ᵥ A *ᵥ x ≤ c * (‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖)}
      (A.sortedSingularValues k) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hk : k < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by rw [hfin]; exact hkn
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) := by
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    infer_instance
  set e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  set T := toEuclideanLin A
  obtain ⟨hG1, hG2⟩ := T.isGreatest_singularValues hk
  obtain ⟨hL1, hL2⟩ := T.isLeast_singularValues_bilinear hk
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨S, hS, h⟩ := hG1
    refine ⟨S.map e.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hS], fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact h y hy
  · rintro c ⟨S, hS, h⟩
    refine hG2 ⟨S.map e.symm.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hS], fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact h y hy
  · obtain ⟨S, hS, h⟩ := hL1
    refine ⟨S.map e.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hS, hfin],
      fun x hx y => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    have := h z hz (WithLp.toLp 2 y)
    simpa [T, e, toEuclideanLin_apply, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using this
  · rintro c ⟨S, hS, h⟩
    refine hL2 ⟨S.map e.symm.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hS, hfin],
      fun x hx y => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    have := h z hz (WithLp.ofLp y)
    simpa [T, e, toEuclideanLin_toLp, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm] using this

open scoped Matrix.Norms.L2Operator in
/-- **Corollary 8.6.2** of [golub2013matrix]. Let $A, E \in \mathbb{R}^{m \times n}$. Then for every
$k$,
$$|\sigma_k(A + E) - \sigma_k(A)| \le \sigma_1(E) = \|E\|_2.$$

The index $k$ is any natural number, 0-based; for $k$ beyond $\min\{m, n\}$ both singular values
are $0$. The 2-norm is `Matrix.lpOpNorm 2 E`. -/
theorem corollary_8_6_2 (A E : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    |(A + E).sortedSingularValues k - A.sortedSingularValues k| ≤ E.sortedSingularValues 0 ∧
      E.sortedSingularValues 0 = lpOpNorm 2 E := by
  have hE : E.sortedSingularValues 0 = lpOpNorm 2 E := by
    rw [lpOpNorm_two, sortedSingularValues_zero_eq_l2_opNorm]
  refine ⟨?_, hE⟩
  rw [hE, lpOpNorm_two]
  refine LinearMap.abs_singularValues_sub_le (norm_nonneg E) (fun x => ?_) k
  rw [map_add, add_sub_cancel_left]
  exact norm_toEuclideanLin_apply_le E x

open scoped Matrix.Norms.L2Operator in
/-- The Jordan–Wielandt matrix $\begin{bmatrix} 0 & E^T \\ E & 0 \end{bmatrix}$ has the same 2-norm
as $E$. -/
private theorem lpOpNorm_hermitianDilation (E : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 (hermitianDilation E) = lpOpNorm 2 E := by
  apply le_antisymm
  · rw [lpOpNorm_two, lpOpNorm_two]
    have h := l2_opNorm_fromBlocks_le (E := (0 : Matrix (Fin n) (Fin n) ℝ)) (C := Eᴴ) (C' := E)
      (D := (0 : Matrix (Fin m) (Fin m) ℝ)) (μ := 0) (γ := ‖E‖) (δ := 0) (by simp)
      (by rw [l2_opNorm_conjTranspose]) le_rfl (by simp)
    have hs : √((0 - 0) ^ 2 + 4 * ‖E‖ ^ 2) = 2 * ‖E‖ := by
      rw [show ((0 : ℝ) - 0) ^ 2 + 4 * ‖E‖ ^ 2 = (2 * ‖E‖) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [hs, zero_add, zero_add, mul_div_cancel_left₀ _ two_ne_zero] at h
    exact h
  · have h := lpOpNorm_submatrix_le (p := 2) (hermitianDilation E) Sum.inr_injective
      Sum.inl_injective
    have he : (hermitianDilation E).submatrix Sum.inr Sum.inl = E := by
      ext i j; simp [hermitianDilation]
    rwa [he] at h

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Equation (8.6.4)** of [golub2013matrix]. Let $A, E \in \mathbb{R}^{m \times n}$, and let
$\tilde A$, $\tilde E$ and $\widetilde{A + E}$ be the Jordan–Wielandt matrices of $A$, $E$ and
$A + E$. Then
$$\tilde E = \begin{bmatrix} 0 & E^T \\ E & 0 \end{bmatrix}, \qquad \widetilde{A + E} = \tilde
  A + \tilde E, \qquad \|\tilde E\|_F^2 = 2 \|E\|_F^2, \qquad \|\tilde E\|_2 = \|E\|_2.$$

These norms turn Theorem 8.1.4 and Corollary 8.1.6 for $\tilde A$ into Theorem 8.6.4 and
Corollary 8.6.2. The Jordan–Wielandt matrix is `Matrix.hermitianDilation`. -/
theorem equation_8_6_4 (A E : Matrix (Fin m) (Fin n) ℝ) :
    hermitianDilation E = fromBlocks 0 Eᵀ E 0 ∧
      hermitianDilation (A + E) = hermitianDilation A + hermitianDilation E ∧
      ‖hermitianDilation E‖ ^ 2 = 2 * ‖E‖ ^ 2 ∧
      lpOpNorm 2 (hermitianDilation E) = lpOpNorm 2 E :=
  ⟨by rw [hermitianDilation, conjTranspose_eq_transpose_of_trivial], hermitianDilation_add A E,
    frobenius_norm_hermitianDilation_sq E, lpOpNorm_hermitianDilation E⟩

/-- **Theorem 8.6.4** of [golub2013matrix] (Wielandt–Hoffman theorem for singular values). Let
$A, E \in \mathbb{R}^{m \times n}$ with $m \ge n$. Then
$$\sum_{k=1}^n \bigl(\sigma_k(A + E) - \sigma_k(A)\bigr)^2 \le \|E\|_F^2.$$

This is `Matrix.sum_sq_sortedSingularValues_sub_le`, whose proof is the proof of the source:
Theorem 8.1.4 for the matrices of (8.6.4). -/
theorem theorem_8_6_4 (hmn : n ≤ m) (A E : Matrix (Fin m) (Fin n) ℝ) :
    ∑ k : Fin n, ((A + E).sortedSingularValues k - A.sortedSingularValues k) ^ 2 ≤ ‖E‖ ^ 2 := by
  have h := sum_sq_sortedSingularValues_sub_le A E
  rwa [Fintype.card_fin, Fintype.card_fin, min_eq_right hmn,
    ← Fin.sum_univ_eq_sum_range (fun k => ((A + E).sortedSingularValues k -
      A.sortedSingularValues k) ^ 2)] at h

end Frobenius

/-- **Corollary 8.6.3** of [golub2013matrix] (interlacing). Let $A = [a_1 \mid \dots \mid a_n] \in
\mathbb{R}^{m \times n}$, let $r + 1 \le n$, and let $A_r = [a_1 \mid \dots \mid a_r]$ be the
matrix of its first $r$ columns. Then for every $k \ge 1$
$$\sigma_k(A_{r+1}) \ge \sigma_k(A_r) \ge \sigma_{k+1}(A_{r+1}),$$
so that $\sigma_1(A_{r+1}) \ge \sigma_1(A_r) \ge \sigma_2(A_{r+1}) \ge \dots \ge \sigma_r(A_r)
\ge \sigma_{r+1}(A_{r+1})$.

The index is 0-based in Lean, and the inequalities hold for every index; for $k > r$ they are
trivial because $\sigma_k(A_r) = 0$. The proof in the source cites "Corollary 8.1.7" where it
means Theorem 8.1.7. -/
theorem corollary_8_6_3 (A : Matrix (Fin m) (Fin n) ℝ) {r : ℕ} (hr : r + 1 ≤ n) (k : ℕ) :
    (A.submatrix id (Fin.castLE (by omega : r ≤ n))).sortedSingularValues k ≤
        (A.submatrix id (Fin.castLE hr)).sortedSingularValues k ∧
      (A.submatrix id (Fin.castLE hr)).sortedSingularValues (k + 1) ≤
        (A.submatrix id (Fin.castLE (by omega : r ≤ n))).sortedSingularValues k := by
  -- the first `r` columns of `A_{r+1}` through the zero-extension isometry
  set P : Matrix (Fin (r + 1)) (Fin r) ℝ := (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ).submatrix id
    Fin.castSucc
  have hP : Pᴴ * P = 1 := by
    ext i j
    simp [P, Matrix.mul_apply, Matrix.one_apply, Fin.castSucc_inj]
  let ι : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r + 1)) :=
    { toLinearMap := toEuclideanLin P
      norm_map' := norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hP }
  have hcomp : toEuclideanLin (A.submatrix id (Fin.castLE hr)) ∘ₗ ι.toLinearMap =
      toEuclideanLin (A.submatrix id (Fin.castLE (by omega : r ≤ n))) := by
    change toEuclideanLin _ ∘ₗ toEuclideanLin P = _
    rw [← toEuclideanLin_mul]
    congr 1
    ext i j
    simp only [P, Matrix.mul_apply, submatrix_apply, id, Matrix.one_apply]
    rw [Finset.sum_eq_single (Fin.castSucc j)]
    · simp [Fin.castLE_castSucc]
    · intro b _ hb; simp [hb]
    · simp
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) + 1 =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (r + 1))) := by simp
  refine ⟨?_, ?_⟩
  · have := LinearMap.singularValues_comp_linearIsometry_le
      (toEuclideanLin (A.submatrix id (Fin.castLE hr))) ι k
    rwa [hcomp] at this
  · have := LinearMap.singularValues_add_le_singularValues_comp_linearIsometry
      (toEuclideanLin (A.submatrix id (Fin.castLE hr))) ι hdim k
    rwa [hcomp] at this

/-- **Section 8.6.2** of [golub2013matrix], singular subspace pairs. Let
$A \in \mathbb{R}^{m \times n}$. Subspaces $S \subseteq \mathbb{R}^n$ and
$T \subseteq \mathbb{R}^m$ form a **singular subspace pair** for $A$ if $\dim S = \dim T$,
$Ax \in T$ for every $x \in S$, and $A^T y \in S$ for every $y \in T$. -/
def IsSingularSubspacePair (A : Matrix (Fin m) (Fin n) ℝ)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
  Module.finrank ℝ S = Module.finrank ℝ T ∧ S.map (toEuclideanLin A) ≤ T ∧
    T.map (toEuclideanLin Aᵀ) ≤ S

/-! ### §8.6.3 The SVD algorithm -/

/-- **Section 8.6.3** of [golub2013matrix], first sentence. Let $A \in \mathbb{R}^{m \times n}$,
$B \in \mathbb{R}^{m \times n}$ and $V \in \mathbb{R}^{n \times n}$, and let
$U \in \mathbb{R}^{m \times m}$ be orthogonal. If $U^T A V = B$, then $V^T (A^T A) V = B^T B$.

The source applies this to a bidiagonalization, where $V$ is orthogonal and $B$ is bidiagonal,
to get a tridiagonal decomposition of $A^T A$. Neither condition is needed for the identity. -/
theorem gram_of_bidiagonalization {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin m) (Fin n) ℝ}
    (hU : U ∈ orthogonalGroup (Fin m) ℝ) (h : Uᵀ * A * V = B) : Vᵀ * (Aᵀ * A) * V = Bᵀ * B := by
  rw [← h, transpose_mul, transpose_mul, transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U, (mem_orthogonalGroup_iff (Fin m) ℝ).1 hU, Matrix.one_mul]

/-- **Section 8.6.3** of [golub2013matrix], the matrix $B^T B$ of a bidiagonal $B$. Let
$B \in \mathbb{R}^{n \times n}$ be upper bidiagonal with diagonal $d_1, \dots, d_n$ and
superdiagonal $f_1, \dots, f_{n-1}$, and put $f_0 = 0$. Then $T = B^T B$ is symmetric and
tridiagonal, with
$$t_{ii} = d_i^2 + f_{i-1}^2, \qquad t_{i,i+1} = d_i f_i,$$
and $T$ is unreduced if and only if $d_i f_i \ne 0$ for $i = 1, \dots, n - 1$.

In Lean, $d_i$ is `B i i`, $f_i$ is `B i j` with $j = i + 1$, and $f_{i-1}^2$ is written as a
sum over the index $j$ with $j + 1 = i$. That a bidiagonalization $U^T A V = B$ gives the
tridiagonal decomposition $V^T (A^T A) V = B^T B$ is
`GolubVanLoan.Chapter08.gram_of_bidiagonalization`. -/
theorem gram_bidiagonal {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsUpperBidiagonal) :
    (Bᵀ * B).IsSymm ∧ (Bᵀ * B).IsTridiagonal ∧
      (∀ i : Fin n, (Bᵀ * B) i i =
        B i i ^ 2 + ∑ j : Fin n, if (j : ℕ) + 1 = i then B j i ^ 2 else 0) ∧
      (∀ (i j : Fin n), (j : ℕ) = i + 1 → (Bᵀ * B) i j = B i i * B i j) ∧
      (IsUnreducedTridiagonal (Bᵀ * B) ↔
        ∀ (i j : Fin n), (j : ℕ) = i + 1 → B i i * B i j ≠ 0) := by
  -- the support of a bidiagonal matrix
  have hsupp : ∀ i j : Fin n, B i j ≠ 0 → (j : ℕ) = i ∨ (j : ℕ) = i + 1 := fun i j h => by
    by_contra hc
    push Not at hc
    refine h (hB i j ?_)
    rcases lt_or_ge (j : ℕ) i with hji | hji
    · exact Or.inl (Fin.lt_def.2 hji)
    · exact Or.inr ⟨⟨i + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩
  have hsymm : (Bᵀ * B).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_transpose]
  have hentry : ∀ i j : Fin n, (Bᵀ * B) i j = ∑ k, B k i * B k j := fun i j => by
    simp [Matrix.mul_apply]
  have htri : (Bᵀ * B).IsTridiagonal := fun i j hij => by
    rw [hentry]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_contra h0
    have h1 := hsupp k i (left_ne_zero_of_mul h0)
    have h2 := hsupp k j (right_ne_zero_of_mul h0)
    rcases hij with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩ <;>
      simp only [Fin.lt_def] at hc1 hc2 <;> omega
  have hsuper : ∀ (i j : Fin n), (j : ℕ) = i + 1 → (Bᵀ * B) i j = B i i * B i j := by
    intro i j hij
    rw [hentry, Finset.sum_eq_single i]
    · intro k _ hki
      by_contra h0
      have h1 := hsupp k i (left_ne_zero_of_mul h0)
      have h2 := hsupp k j (right_ne_zero_of_mul h0)
      have : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
      omega
    · simp
  refine ⟨hsymm, htri, fun i => ?_, hsuper, ?_⟩
  · have hterm : ∀ k : Fin n, B k i * B k i =
        (if k = i then B i i ^ 2 else 0) + (if (k : ℕ) + 1 = i then B k i ^ 2 else 0) := by
      intro k
      by_cases hk : k = i
      · subst hk; simp [sq]
      · by_cases hk' : (k : ℕ) + 1 = i
        · simp [hk, hk', sq]
        · have h0 : B k i = 0 := by
            by_contra h0
            rcases hsupp k i h0 with h | h
            · exact hk (Fin.ext h.symm)
            · exact hk' h.symm
          simp [hk, hk', h0]
    rw [hentry, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp
  · rw [IsUnreducedTridiagonal, isUnreducedUpperHessenberg_iff_fin]
    constructor
    · rintro ⟨-, -, h⟩ i j hij
      have h1 := h i (by have := j.isLt; omega)
      have e : (⟨(i : ℕ) + 1, by have := j.isLt; omega⟩ : Fin n) = j := Fin.ext hij.symm
      rw [e, Fin.eta] at h1
      rw [← hsuper i j hij, ← hsymm.apply i j]
      exact h1
    · intro h
      refine ⟨htri, htri.isUpperHessenberg, fun k hk => ?_⟩
      rw [← hsymm.apply]
      rw [hsuper ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl]
      exact h _ _ rfl

/-! ### §8.6.4 Jacobi SVD procedures -/

/-- The rotation $\begin{bmatrix} c & s \\ -s & c \end{bmatrix}$ is the plane rotation
`planeRotation 0 1 c (-s)` of order $2$. -/
private theorem planeRotation_fin_two (c s : ℝ) :
    planeRotation (0 : Fin 2) 1 c (-s) = !![c, s; -s, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeRotation_apply]

/-- A $2 \times 2$ matrix with zero off-diagonal entries is diagonal. -/
private theorem eq_diagonal_of_fin_two {N : Matrix (Fin 2) (Fin 2) ℝ} (h01 : N 0 1 = 0)
    (h10 : N 1 0 = 0) : N = diagonal fun i => N i i := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

/-- **Section 8.6.4** of [golub2013matrix], the two-sided Jacobi SVD subproblem (Problem P8.6.5).
For every $M \in \mathbb{R}^{2 \times 2}$ there are $c_1, s_1, c_2, s_2 \in \mathbb{R}$ with
$c_1^2 + s_1^2 = 1$, $c_2^2 + s_2^2 = 1$ and
$$\begin{bmatrix} c_1 & s_1 \\ -s_1 & c_1 \end{bmatrix}^T M \begin{bmatrix} c_2 & s_2 \\ -s_2 &
  c_2 \end{bmatrix} = \operatorname{diag}(d_1, d_2)$$
for some $d_1, d_2$. Moreover, for every $A \in \mathbb{R}^{n \times n}$ and $p \ne q$ there are
such pairs for which $B = J(p, q, \theta_1)^T A J(p, q, \theta_2)$ satisfies
$b_{pq} = b_{qp} = 0$ and
$$\operatorname{off}(B)^2 = \operatorname{off}(A)^2 - a_{pq}^2 - a_{qp}^2.$$

The matrix $A$ need not be symmetric. The first rotation makes the $2 \times 2$ block symmetric
(P8.6.5(a)), and the second is the symmetric Schur rotation of Algorithm 8.5.1,
`Matrix.jacobiRotation`; the identity for $\operatorname{off}$ is P8.6.5(c). -/
theorem jacobiSVD_twoByTwo :
    (∀ M : Matrix (Fin 2) (Fin 2) ℝ, ∃ c₁ s₁ c₂ s₂ : ℝ, c₁ ^ 2 + s₁ ^ 2 = 1 ∧
      c₂ ^ 2 + s₂ ^ 2 = 1 ∧ ∃ d : Fin 2 → ℝ,
        (!![c₁, s₁; -s₁, c₁])ᵀ * M * !![c₂, s₂; -s₂, c₂] = diagonal d) ∧
    ∀ (A : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n}, p ≠ q → ∃ c₁ s₁ c₂ s₂ : ℝ,
      c₁ ^ 2 + s₁ ^ 2 = 1 ∧ c₂ ^ 2 + s₂ ^ 2 = 1 ∧
        ((planeRotation p q c₁ (-s₁))ᵀ * A * planeRotation p q c₂ (-s₂)) p q = 0 ∧
        ((planeRotation p q c₁ (-s₁))ᵀ * A * planeRotation p q c₂ (-s₂)) q p = 0 ∧
        off ((planeRotation p q c₁ (-s₁))ᵀ * A * planeRotation p q c₂ (-s₂)) ^ 2 =
          off A ^ 2 - A p q ^ 2 - A q p ^ 2 := by
  -- the `2 × 2` problem
  have h2 : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, ∃ c₁ s₁ c₂ s₂ : ℝ, c₁ ^ 2 + s₁ ^ 2 = 1 ∧
      c₂ ^ 2 + s₂ ^ 2 = 1 ∧ ∃ d : Fin 2 → ℝ,
        (!![c₁, s₁; -s₁, c₁])ᵀ * M * !![c₂, s₂; -s₂, c₂] = diagonal d := by
    intro M
    -- a rotation `R₀ = [c s; -s c]` making `R₀ M` symmetric: `c (m₀₁ - m₁₀) + s (m₁₁ + m₀₀) = 0`
    set c := (givensPair (M 1 1 + M 0 0) (M 1 0 - M 0 1)).1
    set s := (givensPair (M 1 1 + M 0 0) (M 1 0 - M 0 1)).2
    have hcs : c ^ 2 + s ^ 2 = 1 := givensPair_sq_add_sq _ _
    have hsym0 : c * (M 0 1 - M 1 0) + s * (M 1 1 + M 0 0) = 0 := by
      have := (givensPair_fst_mul_add_snd_mul (M 1 1 + M 0 0) (M 1 0 - M 0 1)).2
      linear_combination -this
    set S := !![c, s; -s, c] * M
    have hS : S.IsSymm := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [S, Fin.sum_univ_two, vecMul, dotProduct] <;> linarith [hsym0]
    -- the symmetric Schur rotation of `S`
    set cJ := jacobiCos S 0 1
    set sJ := jacobiSin S 0 1
    have hJ : jacobiRotation S 0 1 = !![cJ, -sJ; sJ, cJ] := by
      have h := planeRotation_fin_two cJ (-sJ)
      simp only [neg_neg] at h
      rw [jacobiRotation]
      exact h
    have hcsJ : cJ ^ 2 + sJ ^ 2 = 1 := jacobiCos_sq_add_jacobiSin_sq S 0 1
    have hzero : jacobiStep S 0 1 0 1 = 0 := jacobiStep_apply_eq_zero S hS (by decide)
    have hzero' : jacobiStep S 0 1 1 0 = 0 :=
      ((isSymm_jacobiStep hS 0 1).apply 0 1).trans hzero
    refine ⟨c * cJ - s * sJ, -(c * sJ + s * cJ), cJ, -sJ, ?_, by rw [neg_sq]; exact hcsJ,
      fun i => jacobiStep S 0 1 i i, ?_⟩
    · linear_combination (cJ ^ 2 + sJ ^ 2) * hcs + hcsJ
    · have hL : (!![c * cJ - s * sJ, -(c * sJ + s * cJ); -(-(c * sJ + s * cJ)), c * cJ - s * sJ])ᵀ =
          (jacobiRotation S 0 1)ᵀ * !![c, s; -s, c] := by
        rw [hJ]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
      have hR : !![cJ, -sJ; -(-sJ), cJ] = jacobiRotation S 0 1 := by rw [hJ, neg_neg]
      rw [hL, hR, Matrix.mul_assoc (jacobiRotation S 0 1)ᵀ !![c, s; -s, c] M]
      exact eq_diagonal_of_fin_two hzero hzero'
  refine ⟨h2, fun A p q hpq => ?_⟩
  obtain ⟨c₁, s₁, c₂, s₂, h1, h2', d, hd⟩ := h2 !![A p p, A p q; A q p, A q q]
  refine ⟨c₁, s₁, c₂, s₂, h1, h2', ?_⟩
  set G₁ := planeRotation p q c₁ (-s₁)
  set G₂ := planeRotation p q c₂ (-s₂)
  set B := G₁ᵀ * A * G₂
  -- the entries of `B`
  have hB : ∀ i j, B i j =
      if i = p then c₁ * (A * G₂) p j + -s₁ * (A * G₂) q j
      else if i = q then -(-s₁) * (A * G₂) p j + c₁ * (A * G₂) q j
      else (A * G₂) i j := fun i j => by
    simp only [B, G₁, Matrix.mul_assoc]
    exact transpose_planeRotation_mul_apply hpq _ i j
  have hAG : ∀ i j, (A * G₂) i j =
      if j = p then c₂ * A i p + -s₂ * A i q
      else if j = q then -(-s₂) * A i p + c₂ * A i q
      else A i j := fun i j => mul_planeRotation_apply hpq A i j
  -- the `(p, q)` block of `B` is the `2 × 2` product
  have hblock : ∀ a b : Fin 2, B (![p, q] a) (![p, q] b) =
      ((!![c₁, s₁; -s₁, c₁])ᵀ * !![A p p, A p q; A q p, A q q] * !![c₂, s₂; -s₂, c₂]) a b := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [hB, hAG, hpq.symm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hpq0 : B p q = 0 := by
    have := hblock 0 1; rw [hd] at this; simpa using this
  have hqp0 : B q p = 0 := by
    have := hblock 1 0; rw [hd] at this; simpa using this
  refine ⟨hpq0, hqp0, ?_⟩
  -- the diagonal outside the plane is unchanged, the Frobenius mass of the block is preserved
  have hdiag : ∀ i, i ≠ p → i ≠ q → B i i = A i i := fun i hip hiq => by
    simp only [hB, hAG]; simp [hip, hiq]
  have hbpp : B p p = c₁ * (c₂ * A p p + -s₂ * A p q) + -s₁ * (c₂ * A q p + -s₂ * A q q) := by
    simp [hB, hAG]
  have hbqq : B q q = -(-s₁) * (-(-s₂) * A p p + c₂ * A p q) +
      c₁ * (-(-s₂) * A q p + c₂ * A q q) := by
    simp [hB, hAG, hpq.symm]
  have hbpq : B p q =
      c₁ * (-(-s₂) * A p p + c₂ * A p q) + -s₁ * (-(-s₂) * A q p + c₂ * A q q) := by
    simp [hB, hAG, hpq.symm]
  have hbqp : B q p =
      -(-s₁) * (c₂ * A p p + -s₂ * A p q) + c₁ * (c₂ * A q p + -s₂ * A q q) := by
    simp [hB, hAG, hpq.symm]
  have hmass : B p p ^ 2 + B q q ^ 2 = A p p ^ 2 + A q q ^ 2 + A p q ^ 2 + A q p ^ 2 := by
    have e : B p p ^ 2 + B q q ^ 2 + B p q ^ 2 + B q p ^ 2 =
        A p p ^ 2 + A q q ^ 2 + A p q ^ 2 + A q p ^ 2 := by
      rw [hbpp, hbqq, hbpq, hbqp]
      linear_combination (A p p ^ 2 + A q q ^ 2 + A p q ^ 2 + A q p ^ 2) *
        ((c₂ ^ 2 + s₂ ^ 2) * h1 + h2')
    rw [hpq0, hqp0] at e
    linarith
  have hsumdiag : ∑ i, B i i ^ 2 = ∑ i, A i i ^ 2 + A p q ^ 2 + A q p ^ 2 := by
    have e := Fintype.sum_eq_add p q hpq (f := fun i => B i i ^ 2 - A i i ^ 2) fun i hi => by
      simp [hdiag i hi.1 hi.2]
    rw [Finset.sum_sub_distrib] at e
    linarith
  -- the Frobenius mass of `B` is that of `A`
  have hG₁ : G₁ᵀ ∈ unitaryGroup (Fin n) ℝ := by
    rw [planeRotation_transpose hpq]
    exact planeRotation_mem_orthogonalGroup hpq (by rw [neg_neg]; linarith [neg_sq s₁])
  have hG₂ : G₂ ∈ unitaryGroup (Fin n) ℝ :=
    planeRotation_mem_orthogonalGroup hpq (by rw [neg_sq]; exact h2')
  have hfro : ∑ i, ∑ j, B i j ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
    have h := congrArg (· ^ 2) (frobenius_norm_unitary_mul_mul_unitary hG₁ A hG₂)
    simp only [frobenius_norm_sq_eq_sum_sq, Real.norm_eq_abs, sq_abs] at h
    exact h
  rw [off_sq, off_sq]
  have eB := offDiagNormSq_add_sum_diag_sq_real B
  have eA := offDiagNormSq_add_sum_diag_sq_real A
  linarith

/-- **Section 8.6.4** of [golub2013matrix], one-sided Jacobi. Let $A \in \mathbb{R}^{m \times n}$
and $p \ne q$. Then:

* for all $c, s$ and $J = J(p, q, \theta)$, the inner product of columns $p$ and $q$ of $AJ$ is
  $(J^T (A^T A) J)_{pq}$, so the two columns are orthogonal if and only if this entry is zero;
* for the rotation of Algorithm 8.5.1 applied to $A^T A$, columns $p$ and $q$ of $AJ$ are
  orthogonal;
* for every $V \in \mathbb{R}^{n \times n}$ such that the columns of $AV$ are pairwise
  orthogonal, there is $U \in \mathbb{R}^{m \times n}$ with pairwise orthogonal columns such
  that $AV = U \Sigma$, where $\Sigma = \operatorname{diag}(\|(AV)(:, j)\|_2)$, and $U(:, j)$
  has unit length whenever $(AV)(:, j) \ne 0$.

The last part is the column scaling that finishes the one-sided Jacobi SVD. The rotation of
Algorithm 8.5.1 for $A^T A$ is `(Matrix.jacobiCosSmall (Aᵀ * A) p q, Matrix.jacobiSinSmall (Aᵀ *
A) p q)`. -/
theorem oneSidedJacobi_orthogonal (A : Matrix (Fin m) (Fin n) ℝ) {p q : Fin n} (hpq : p ≠ q) :
    (∀ c s : ℝ, (A * planeRotation p q c (-s)).col p ⬝ᵥ (A * planeRotation p q c (-s)).col q =
      ((planeRotation p q c (-s))ᵀ * (Aᵀ * A) * planeRotation p q c (-s)) p q) ∧
    (A * planeRotation p q (jacobiCosSmall (Aᵀ * A) p q) (-jacobiSinSmall (Aᵀ * A) p q)).col p ⬝ᵥ
      (A * planeRotation p q (jacobiCosSmall (Aᵀ * A) p q) (-jacobiSinSmall (Aᵀ * A) p q)).col q =
        0 ∧
    ∀ V : Matrix (Fin n) (Fin n) ℝ, (∀ i j, i ≠ j → (A * V).col i ⬝ᵥ (A * V).col j = 0) →
      ∃ U : Matrix (Fin m) (Fin n) ℝ,
        A * V = U * diagonal (fun j => ‖WithLp.toLp 2 ((A * V).col j)‖) ∧
        (∀ i j, i ≠ j → U.col i ⬝ᵥ U.col j = 0) ∧
        ∀ j, (A * V).col j ≠ 0 → U.col j ⬝ᵥ U.col j = 1 := by
  have hdot : ∀ {k : ℕ} (M : Matrix (Fin m) (Fin k) ℝ) (i j : Fin k),
      M.col i ⬝ᵥ M.col j = (Mᵀ * M) i j := fun M i j => by
    simp [dotProduct, Matrix.mul_apply, col_apply]
  have hconj : ∀ c s : ℝ, (A * planeRotation p q c (-s)).col p ⬝ᵥ
      (A * planeRotation p q c (-s)).col q =
        ((planeRotation p q c (-s))ᵀ * (Aᵀ * A) * planeRotation p q c (-s)) p q := fun c s => by
    rw [hdot, transpose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨hconj, ?_, fun V hV => ?_⟩
  · have hsym : (Aᵀ * A).IsSymm := by rw [IsSymm, transpose_mul, transpose_transpose]
    rw [hconj, ← jacobiRotation_eq_planeRotation_small]
    exact jacobiStep_apply_eq_zero (Aᵀ * A) hsym hpq
  · set σ : Fin n → ℝ := fun j => ‖WithLp.toLp 2 ((A * V).col j)‖
    have hσ0 : ∀ j, σ j = 0 → (A * V).col j = 0 := fun j h => by
      have : (WithLp.toLp 2 ((A * V).col j) : EuclideanSpace ℝ (Fin m)) = 0 := norm_eq_zero.1 h
      simpa using congrArg WithLp.ofLp this
    refine ⟨Matrix.of fun i j => (σ j)⁻¹ * (A * V) i j, ?_, fun i j hij => ?_, fun j hj => ?_⟩
    · ext i j
      rw [mul_diagonal, of_apply]
      by_cases h : σ j = 0
      · have := congrFun (hσ0 j h) i
        simp only [col_apply, Pi.zero_apply] at this
        simp [h, this]
      · field_simp
    · have := hV i j hij
      simp only [dotProduct, col_apply, of_apply] at this ⊢
      calc ∑ x, (σ i)⁻¹ * (A * V) x i * ((σ j)⁻¹ * (A * V) x j) =
            (σ i)⁻¹ * (σ j)⁻¹ * ∑ x, (A * V) x i * (A * V) x j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        _ = 0 := by rw [this, mul_zero]
    · have hne : σ j ≠ 0 := fun h => hj (hσ0 j h)
      have hsq : (A * V).col j ⬝ᵥ (A * V).col j = σ j ^ 2 := dotProduct_self_eq_norm_sq _
      simp only [dotProduct, col_apply, of_apply] at hsq ⊢
      calc ∑ x, (σ j)⁻¹ * (A * V) x j * ((σ j)⁻¹ * (A * V) x j) =
            (σ j)⁻¹ ^ 2 * ∑ x, (A * V) x j * (A * V) x j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        _ = 1 := by rw [hsq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hne)]

/-! ### §8.6.2 Theorem 8.6.5, and its failure for $m > n$ as printed -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- If $W$ has orthonormal columns, then $W \begin{bmatrix} I \\ P \end{bmatrix}$ has a range of
dimension $r$. -/
private theorem finrank_range_mul_fromRows_one {l r s : ℕ}
    {W : Matrix (Fin l) (Fin r ⊕ Fin s) ℝ} (hW : Wᵀ * W = 1) (P : Matrix (Fin s) (Fin r) ℝ) :
    Module.finrank ℝ (LinearMap.range
      (toEuclideanLin (W * fromRows (1 : Matrix (Fin r) (Fin r) ℝ) P))) = r := by
  have hinj : Function.Injective
      (toEuclideanLin (W * fromRows (1 : Matrix (Fin r) (Fin r) ℝ) P)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : (fromRows (1 : Matrix (Fin r) (Fin r) ℝ) P) *ᵥ WithLp.ofLp y = 0 := by
      have := congrArg (fun v => Wᵀ *ᵥ WithLp.ofLp v) hy
      simp only [toEuclideanLin_apply, WithLp.ofLp_toLp, mulVec_mulVec, ← Matrix.mul_assoc,
        hW, Matrix.one_mul, WithLp.ofLp_zero, mulVec_zero] at this
      exact this
    ext i
    have := congrFun h1 (Sum.inl i)
    rw [fromRows_mulVec, Sum.elim_inl, one_mulVec] at this
    exact this
  rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_fin]

/-- **Theorem 8.6.5** of [golub2013matrix] (perturbation of singular subspace pairs). Let
$A, E \in \mathbb{R}^{m \times n}$ with $m \ge n$, and let
$V = [V_1\ V_2] \in \mathbb{R}^{n \times n}$ and $U = [U_1\ U_2] \in \mathbb{R}^{m \times m}$ be
orthogonal, where $V_1$ and $U_1$ have $r$ columns, such that
$$U^T A V = \begin{bmatrix} A_{11} & 0 \\ 0 & A_{22} \end{bmatrix}, \qquad A_{11} \in
  \mathbb{R}^{r \times r}.$$
Let $\delta > 0$ satisfy $\delta \le |\sigma_i(A_{11}) - \sigma_j(A_{22})|$ for
$i = 1, \dots, r$ and $j = 1, \dots, n - r$, and, if $m > n$, also
$\delta \le \sigma_{\min}(A_{11})$. If $\|E\|_F \le \delta/5$, then there are
$P \in \mathbb{R}^{(n - r) \times r}$ and $Q \in \mathbb{R}^{(m - r) \times r}$ with
$$\left\| \begin{bmatrix} Q \\ P \end{bmatrix} \right\|_F \le \frac{4 \|E\|_F}{\delta}$$
such that $\operatorname{ran}(V_1 + V_2 P)$ and $\operatorname{ran}(U_1 + U_2 Q)$ form a
singular subspace pair for $A + E$.

**Correction.** As printed, the theorem is false for $m > n$; see
`GolubVanLoan.Chapter08.theorem_8_6_5_counterexample`. For $m > n$ the declaration adds Wedin's
condition $\delta \le \sigma_{\min}(A_{11})$.

**Typo.** The source swaps $P$ and $Q$: its $Q$ is $(n - r) \times r$.

The block form of $U^T A V$ makes $(\operatorname{ran} V_1, \operatorname{ran} U_1)$ a singular
subspace pair for $A$, the unperturbed pair; the declaration does not state this. The source
takes $\delta = \min |\sigma - \gamma| > 0$ over the singular values $\sigma$ of $A_{11}$ and
$\gamma$ of $A_{22}$; here $\delta$ is any positive lower bound of these gaps. The orthogonality
of $U$ and $V$ is stated as $U^T U = UU^T = I$ and $V^T V = VV^T = I$. The theorem specializes
`Matrix.exists_singularSubspacePair_perturbation` (Stewart 1973, Wedin 1972). -/
theorem theorem_8_6_5 (hmn : n ≤ m) {r : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {V₁ : Matrix (Fin n) (Fin r) ℝ} {V₂ : Matrix (Fin n) (Fin (n - r)) ℝ}
    {U₁ : Matrix (Fin m) (Fin r) ℝ} {U₂ : Matrix (Fin m) (Fin (m - r)) ℝ}
    (hV : (fromCols V₁ V₂)ᵀ * fromCols V₁ V₂ = 1) (hV' : fromCols V₁ V₂ * (fromCols V₁ V₂)ᵀ = 1)
    (hU : (fromCols U₁ U₂)ᵀ * fromCols U₁ U₂ = 1) (hU' : fromCols U₁ U₂ * (fromCols U₁ U₂)ᵀ = 1)
    {A₁₁ : Matrix (Fin r) (Fin r) ℝ} {A₂₂ : Matrix (Fin (m - r)) (Fin (n - r)) ℝ}
    (hA : (fromCols U₁ U₂)ᵀ * A * fromCols V₁ V₂ = fromBlocks A₁₁ 0 0 A₂₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i < r, ∀ j < n - r,
      δ ≤ |A₁₁.sortedSingularValues i - A₂₂.sortedSingularValues j|)
    (hw : n < m → ∀ i < r, δ ≤ A₁₁.sortedSingularValues i) (hE : ‖E‖ ≤ δ / 5) :
    ∃ (P : Matrix (Fin (n - r)) (Fin r) ℝ) (Q : Matrix (Fin (m - r)) (Fin r) ℝ),
      ‖fromRows Q P‖ ≤ 4 * ‖E‖ / δ ∧
      IsSingularSubspacePair (A + E) (LinearMap.range (toEuclideanLin (V₁ + V₂ * P)))
        (LinearMap.range (toEuclideanLin (U₁ + U₂ * Q))) := by
  have hct : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ), Xᴴ = Xᵀ :=
    fun X => conjTranspose_eq_transpose_of_trivial X
  have hA' : (fromCols U₁ U₂)ᴴ * A * fromCols V₁ V₂ = fromBlocks A₁₁ 0 0 A₂₂ := by
    rw [conjTranspose_eq_transpose_of_trivial]; exact hA
  obtain ⟨P, Q, hPQ, ⟨M, hM⟩, ⟨N, hN⟩⟩ := exists_singularSubspacePair_perturbation (k := Fin r)
    (p := Fin (n - r)) (q := Fin (m - r)) (A := A) (E := E)
    (by rw [conjTranspose_eq_transpose_of_trivial]; exact hU)
    (by rw [conjTranspose_eq_transpose_of_trivial]; exact hU')
    (by rw [conjTranspose_eq_transpose_of_trivial]; exact hV)
    (by rw [conjTranspose_eq_transpose_of_trivial]; exact hV')
    (by rw [hA', toBlocks_fromBlocks₁₂]) (by rw [hA', toBlocks_fromBlocks₂₁]) hδ
    (fun i hi j hj => by
      rw [hA', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]
      simp only [Fintype.card_fin] at hi hj
      exact hsep i hi j (by omega))
    (fun hpq i hi => by
      rw [hA', toBlocks_fromBlocks₁₁]
      simp only [Fintype.card_fin] at hpq hi
      exact hw (by omega) i hi) hE
  have hVP : fromCols V₁ V₂ * fromRows 1 P = V₁ + V₂ * P := by
    rw [fromCols_mul_fromRows, Matrix.mul_one]
  have hUQ : fromCols U₁ U₂ * fromRows 1 Q = U₁ + U₂ * Q := by
    rw [fromCols_mul_fromRows, Matrix.mul_one]
  rw [hVP] at hM hN
  rw [hUQ] at hM hN
  rw [conjTranspose_eq_transpose_of_trivial] at hN
  refine ⟨P, Q, hPQ, ?_, ?_, ?_⟩
  · rw [← hVP, ← hUQ, finrank_range_mul_fromRows_one hV, finrank_range_mul_fromRows_one hU]
  · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨WithLp.toLp 2 (M *ᵥ WithLp.ofLp y), ?_⟩
    simp only [toEuclideanLin_apply, mulVec_mulVec, ← hM]
  · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨WithLp.toLp 2 (N *ᵥ WithLp.ofLp y), ?_⟩
    simp only [toEuclideanLin_apply, mulVec_mulVec, ← hN]


/-- **Theorem 8.6.5** of [golub2013matrix], counterexample for $m > n$. Let $m = 3$, $n = 2$,
$r = 1$,
$$A = \begin{bmatrix} 0 & 0 \\ 0 & 1 \\ 0 & 0 \end{bmatrix}, \qquad E = \begin{bmatrix} 0 & 0 \\
  0 & 0 \\ \varepsilon & 0 \end{bmatrix} = \varepsilon e_3 e_1^T, \qquad 0 < \varepsilon \le
  1/5,$$
and $U = I_3$, $V = I_2$, so that $V_1 = e_1$, $V_2 = e_2$, $U_1 = e_1$ and $U_2 = [e_2\ e_3]$.
Then $\|E\|_F = \varepsilon \le 1/5$, and there are no $P \in \mathbb{R}^{1 \times 1}$ and
$Q \in \mathbb{R}^{2 \times 1}$ such that $(\operatorname{ran}(V_1 + V_2 P),
\operatorname{ran}(U_1 + U_2 Q))$ is a singular subspace pair for $A + E$.

Here $A_{11} = [0]$ and $A_{22} = \begin{bmatrix} 1 \\ 0 \end{bmatrix}$, so the gap of the
source is $\delta = 1$ and $\|E\|_F \le \delta/5$. The added hypothesis
$\delta \le \sigma_{\min}(A_{11}) = 0$ of `GolubVanLoan.Chapter08.theorem_8_6_5` fails. -/
theorem theorem_8_6_5_counterexample {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 5) :
    let A : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 1; 0, 0]
    let E : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 0; ε, 0]
    let V₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    let V₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
    let U₁ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]
    let U₂ : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 1, 0; 0, 1]
    ‖E‖ = ε ∧ ‖E‖ ≤ 1 / 5 ∧
      ¬ ∃ (P : Matrix (Fin 1) (Fin 1) ℝ) (Q : Matrix (Fin 2) (Fin 1) ℝ),
        IsSingularSubspacePair (A + E) (LinearMap.range (toEuclideanLin (V₁ + V₂ * P)))
          (LinearMap.range (toEuclideanLin (U₁ + U₂ * Q))) := by
  intro A E V₁ V₂ U₁ U₂
  have hE : ‖E‖ = ε := by
    have h' : ‖E‖ ^ 2 = ε ^ 2 := by
      rw [frobenius_norm_sq_eq_sum_sq]
      simp [E, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    exact (pow_left_inj₀ (norm_nonneg _) hε.le two_ne_zero).1 h'
  refine ⟨hE, hE ▸ hε', ?_⟩
  rintro ⟨P, Q, -, hST, -⟩
  -- `(A + E) (1, p) = (0, p, ε)` must be a multiple of `(1, q₁, q₂)`
  have hmem : toEuclideanLin (A + E) (toEuclideanLin (V₁ + V₂ * P) (WithLp.toLp 2 ![1])) ∈
      LinearMap.range (toEuclideanLin (U₁ + U₂ * Q)) :=
    hST (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ _))
  obtain ⟨y, hy⟩ := hmem
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hy
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hy
  simp [A, E, V₁, V₂, U₁, U₂, toEuclideanLin_apply, dotProduct, Fin.sum_univ_succ, vecMul,
    vecHead, vecTail] at h0 h2
  simp only [h0, mul_zero] at h2
  linarith

end Frobenius


/-- The row chase of §8.6.3 moves the bulge in row $k$ one column to the right: if the rows other
than $k$ have the bidiagonal pattern and row $k$ is supported in column $j$, the rotation in the
plane $(j, k)$ by the Givens pair of $(c_{jj}, c_{kj})$ keeps the pattern and moves the support
of row $k$ to column $j + 1$. -/
private theorem rowChase_step {C : Matrix (Fin n) (Fin n) ℝ} {k j : Fin n} (hkj : k < j)
    (hrows : ∀ i l, i ≠ k → C i l ≠ 0 → l = i ∨ (l : ℕ) = i + 1)
    (hrow : ∀ l, C k l ≠ 0 → l = j) :
    let R := planeRotation j k (givensPair (C j j) (C k j)).1 (givensPair (C j j) (C k j)).2
    (∀ i l, i ≠ k → (Rᵀ * C) i l ≠ 0 → l = i ∨ (l : ℕ) = i + 1) ∧
      (∀ l, (Rᵀ * C) k l ≠ 0 → (l : ℕ) = j + 1) := by
  intro R
  have hjk : j ≠ k := (ne_of_lt hkj).symm
  have hkj' : k ≠ j := ne_of_lt hkj
  obtain ⟨-, h2⟩ := givensPair_fst_mul_add_snd_mul (C j j) (C k j)
  set c := (givensPair (C j j) (C k j)).1
  set s := (givensPair (C j j) (C k j)).2
  have happ : ∀ p q, (Rᵀ * C) p q =
      if p = j then c * C j q + s * C k q
      else if p = k then -s * C j q + c * C k q
      else C p q := fun p q => transpose_planeRotation_mul_apply hjk C p q
  refine ⟨fun i l hik h => ?_, fun l h => ?_⟩
  · rw [happ] at h
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl] at h
      by_cases h1 : C i l = 0
      · rw [h1, mul_zero, zero_add] at h
        have := hrow l (right_ne_zero_of_mul h)
        exact Or.inl this
      · exact hrows i l hik h1
    · rw [ite_eq_right hij, ite_eq_right hik] at h
      exact hrows i l hik h
  · rw [happ, ite_eq_right hkj', ite_eq_left rfl] at h
    by_cases hl : l = j
    · subst hl
      exact absurd h2 h
    · have h0 : C k l = 0 := by
        by_contra h0
        exact hl (hrow l h0)
      rw [h0, mul_zero, add_zero] at h
      rcases hrows j l hjk (right_ne_zero_of_mul h) with h3 | h3
      · exact absurd h3 hl
      · exact h3

/-- An upper bidiagonal matrix has $b_{il} \ne 0$ only for $l = i$ or $l = i + 1$. -/
private theorem support_of_isUpperBidiagonal {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : C.IsUpperBidiagonal) (i l : Fin n) (h : C i l ≠ 0) : l = i ∨ (l : ℕ) = i + 1 := by
  by_contra hc
  push Not at hc
  refine h (hC i l ?_)
  rcases lt_or_ge (l : ℕ) i with hli | hli
  · exact Or.inl (Fin.lt_def.2 hli)
  · have : (i : ℕ) ≠ l := fun h' => hc.1 (Fin.ext h'.symm)
    exact Or.inr ⟨⟨i + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩

/-- A matrix whose nonzero entries lie on the diagonal and the first superdiagonal is upper
bidiagonal. -/
private theorem isUpperBidiagonal_of_support {C : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i l, C i l ≠ 0 → l = i ∨ (l : ℕ) = i + 1) : C.IsUpperBidiagonal := fun i l hil => by
  by_contra h0
  rcases h i l h0 with h1 | h1
  · subst h1
    rcases hil with h2 | ⟨m, h2, h3⟩
    · exact lt_irrefl _ h2
    · exact lt_asymm h2 h3
  · rcases hil with h2 | ⟨m, h2, h3⟩
    · rw [Fin.lt_def] at h2; omega
    · rw [Fin.lt_def] at h2 h3; omega

/-- If $B$ is upper bidiagonal and $b_{kk} = 0$, there is an orthogonal $G$, a product of row
rotations in the planes $(k, k+1), \dots, (k, n)$, such that $G^T B$ is upper bidiagonal with
zero row $k$. -/
private theorem bidiagonal_rowChase :
    ∀ {B : Matrix (Fin n) (Fin n) ℝ}, B.IsUpperBidiagonal → ∀ k : Fin n,
    B k k = 0 → ∃ G ∈ orthogonalGroup (Fin n) ℝ, (Gᵀ * B).IsUpperBidiagonal ∧
      ∀ l, (Gᵀ * B) k l = 0 := by
  intro B hB k hk
  have hsupp := support_of_isUpperBidiagonal hB
  have key : ∀ t, (k : ℕ) + 1 + t ≤ n → ∃ G ∈ orthogonalGroup (Fin n) ℝ,
      (∀ i l, i ≠ k → (Gᵀ * B) i l ≠ 0 → l = i ∨ (l : ℕ) = i + 1) ∧
        ∀ l, (Gᵀ * B) k l ≠ 0 → (l : ℕ) = k + 1 + t := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨1, one_mem _, fun i l _ h => ?_, fun l h => ?_⟩
      · rw [transpose_one, Matrix.one_mul] at h
        exact hsupp i l h
      · rw [transpose_one, Matrix.one_mul] at h
        rcases hsupp k l h with h1 | h1
        · subst h1; exact absurd hk h
        · simpa using h1
    | succ t ih =>
      intro ht
      obtain ⟨G, hG, hrows, hrow⟩ := ih (by omega)
      set j : Fin n := ⟨k + 1 + t, by omega⟩
      have hkj : k < j := Fin.lt_def.2 (show (k : ℕ) < k + 1 + t by omega)
      have hrow' : ∀ l, (Gᵀ * B) k l ≠ 0 → l = j := fun l h => Fin.ext (hrow l h)
      obtain ⟨h1, h2⟩ := rowChase_step hkj hrows hrow'
      set R := planeRotation j k (givensPair ((Gᵀ * B) j j) ((Gᵀ * B) k j)).1
        (givensPair ((Gᵀ * B) j j) ((Gᵀ * B) k j)).2
      have hR : R ∈ orthogonalGroup (Fin n) ℝ :=
        planeRotation_mem_orthogonalGroup (ne_of_lt hkj).symm (givensPair_sq_add_sq _ _)
      have e : (G * R)ᵀ * B = Rᵀ * (Gᵀ * B) := by
        rw [transpose_mul, Matrix.mul_assoc]
      refine ⟨G * R, Submonoid.mul_mem _ hG hR, fun i l hik h => ?_, fun l h => ?_⟩
      · rw [e] at h; exact h1 i l hik h
      · rw [e] at h
        have := h2 l h
        simp only [j] at this
        omega
  obtain ⟨G, hG, hrows, hrow⟩ := key (n - (k + 1)) (by omega)
  have hzero : ∀ l, (Gᵀ * B) k l = 0 := fun l => by
    by_contra h
    have := hrow l h
    omega
  refine ⟨G, hG, isUpperBidiagonal_of_support fun i l h => ?_, hzero⟩
  by_cases hik : i = k
  · subst hik; exact absurd (hzero l) h
  · exact hrows i l hik h

/-- If $B$ is upper bidiagonal with $f_k = 0$, then $B = \operatorname{diag}(B_1, B_2)$, and $B^T B$
has the characteristic polynomial of $\operatorname{diag}(B_1^T B_1, B_2^T B_2)$. -/
private theorem bidiagonal_split {a b : ℕ}
    {B : Matrix (Fin (a + 1 + (b + 1))) (Fin (a + 1 + (b + 1))) ℝ} (hB : B.IsUpperBidiagonal)
    (hf : B (Fin.castAdd (b + 1) (Fin.last a)) (Fin.natAdd (a + 1) 0) = 0) :
    B.submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks (B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))) 0 0
          (B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))) ∧
      (Bᵀ * B).charpoly =
        ((B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1)))ᵀ *
            B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))).charpoly *
          ((B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1)))ᵀ *
            B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))).charpoly := by
  have hsupp := support_of_isUpperBidiagonal hB
  have hblock : B.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))) 0 0
        (B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))) := by
    ext (i | i) (j | j)
    · rfl
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        fromBlocks_apply₁₂, Matrix.zero_apply]
      by_contra h0
      rcases hsupp _ _ h0 with h1 | h1
      · have := congrArg Fin.val h1; simp at this; omega
      · simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
        have hi : i = Fin.last a := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
        have hj : j = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
        subst hi hj
        exact h0 hf
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        fromBlocks_apply₂₁, Matrix.zero_apply]
      by_contra h0
      rcases hsupp _ _ h0 with h1 | h1
      · have := congrArg Fin.val h1; simp at this; omega
      · simp only [Fin.val_natAdd, Fin.val_castAdd] at h1; omega
    · rfl
  refine ⟨hblock, ?_⟩
  have hgram : (Bᵀ * B).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks ((B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1)))ᵀ *
          B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))) 0 0
        ((B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1)))ᵀ *
          B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))) := by
    rw [← submatrix_mul_equiv _ _ _ finSumFinEquiv, ← transpose_submatrix, hblock,
      fromBlocks_transpose, fromBlocks_multiply]
    simp
  rw [← charpoly_fromBlocks_zero₁₂, ← hgram]
  exact (charpoly_reindex finSumFinEquiv.symm (Bᵀ * B)).symm

/-- If $B$ is upper bidiagonal with zero last diagonal entry, there is an orthogonal $G$, a product
of column rotations, such that $BG$ is upper bidiagonal with zero last column. -/
private theorem bidiagonal_colChase {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsUpperBidiagonal)
    (h : 0 < n) (hd : B ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 0) :
    ∃ G ∈ orthogonalGroup (Fin n) ℝ, (B * G).IsUpperBidiagonal ∧
      ∀ i, (B * G) i ⟨n - 1, by omega⟩ = 0 := by
  set B' : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i l => B (Fin.rev l) (Fin.rev i)
  have hsupp := support_of_isUpperBidiagonal hB
  have hB' : B'.IsUpperBidiagonal := isUpperBidiagonal_of_support fun i l h0 => by
    rcases hsupp _ _ h0 with h1 | h1
    · exact Or.inl (Fin.rev_injective h1.symm)
    · simp only [Fin.val_rev] at h1
      right; omega
  have hd' : B' ⟨0, h⟩ ⟨0, h⟩ = 0 := by
    have e : Fin.rev (⟨0, h⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext (by simp)
    simp only [B', of_apply, e]
    exact hd
  obtain ⟨G', hG', hbid, hrow⟩ := bidiagonal_rowChase hB' ⟨0, h⟩ hd'
  have hentry : ∀ i l, (B * G'.submatrix Fin.rev Fin.rev) i l =
      (G'ᵀ * B') (Fin.rev l) (Fin.rev i) := fun i l => by
    simp only [Matrix.mul_apply, submatrix_apply, transpose_apply, B', of_apply, Fin.rev_rev]
    exact (Fintype.sum_equiv Fin.revPerm _ _ fun m => by simp [mul_comm]).symm
  have hsuppX := support_of_isUpperBidiagonal hbid
  refine ⟨G'.submatrix Fin.rev Fin.rev, ?_, isUpperBidiagonal_of_support fun i l h0 => ?_,
    fun i => ?_⟩
  · have hGG := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hG'
    refine (mem_orthogonalGroup_iff' (Fin n) ℝ).2 ?_
    have e : (G'.submatrix Fin.rev Fin.rev)ᵀ * G'.submatrix Fin.rev Fin.rev =
        (G'ᵀ * G').submatrix Fin.rev Fin.rev := by
      ext i j
      simp only [Matrix.mul_apply, submatrix_apply, transpose_apply]
      exact Fintype.sum_equiv Fin.revPerm _ _ fun m => by simp
    rw [e, hGG]
    ext i j
    simp [Matrix.one_apply]
  · rw [hentry] at h0
    rcases hsuppX _ _ h0 with h1 | h1
    · exact Or.inl (Fin.rev_injective h1).symm
    · simp only [Fin.val_rev] at h1
      right; omega
  · have e : Fin.rev (⟨n - 1, by omega⟩ : Fin n) = ⟨0, h⟩ := Fin.ext (by simp; omega)
    rw [hentry, e]
    exact hrow _

/-- **Section 8.6.3** of [golub2013matrix], the decoupling rules. Let $B$ be upper bidiagonal with
diagonal $d_1, \dots, d_n$ and superdiagonal $f_1, \dots, f_{n-1}$.

* (i) If $f_k = 0$, then $B = \operatorname{diag}(B_1, B_2)$ with $B_1$ of order $k$, and
  $\det(B^T B - xI) = \det(B_1^T B_1 - xI) \det(B_2^T B_2 - xI)$, so the singular values of $B$
  are those of $B_1$ and $B_2$ together.
* (ii) If $d_k = 0$, there is an orthogonal $G$ such that $G^T B$ is upper bidiagonal and its
  row $k$ is zero.
* (iii) If $n \ge 1$ and $d_n = 0$, there is an orthogonal $G$ such that $BG$ is upper
  bidiagonal and its last column is zero.

So the SVD problem decouples whenever $f_1 \cdots f_{n-1} = 0$ or $d_1 \cdots d_n = 0$. In (ii),
$G$ is the product of the row rotations in the planes $(k, k+1), \dots, (k, n)$, each by the
Givens pair of the current entries $(j, j)$ and $(k, j)$, which chase the bulge one column to
the right. In (iii), $G$ is the product of the column rotations in the planes
$(n-1, n), \dots, (1, n)$. In (i), the orders of $B_1$ and $B_2$ are `a + 1` and `b + 1` in
Lean, the matrix $B$ is reindexed by `finSumFinEquiv`, and the equality of spectra is the
equality of characteristic polynomials. -/
theorem bidiagonal_decouple :
    (∀ {a b : ℕ} {B : Matrix (Fin (a + 1 + (b + 1))) (Fin (a + 1 + (b + 1))) ℝ},
      B.IsUpperBidiagonal → B (Fin.castAdd (b + 1) (Fin.last a)) (Fin.natAdd (a + 1) 0) = 0 →
        B.submatrix finSumFinEquiv finSumFinEquiv =
            fromBlocks (B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))) 0 0
              (B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))) ∧
          (Bᵀ * B).charpoly =
            ((B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1)))ᵀ *
                B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))).charpoly *
              ((B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1)))ᵀ *
                B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))).charpoly) ∧
    (∀ {B : Matrix (Fin n) (Fin n) ℝ}, B.IsUpperBidiagonal → ∀ k : Fin n, B k k = 0 →
      ∃ G ∈ orthogonalGroup (Fin n) ℝ, (Gᵀ * B).IsUpperBidiagonal ∧ ∀ l, (Gᵀ * B) k l = 0) ∧
    (∀ {B : Matrix (Fin n) (Fin n) ℝ}, B.IsUpperBidiagonal → ∀ h : 0 < n,
      B ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 0 →
      ∃ G ∈ orthogonalGroup (Fin n) ℝ, (B * G).IsUpperBidiagonal ∧
        ∀ i, (B * G) i ⟨n - 1, by omega⟩ = 0) :=
  ⟨fun hB hf => bidiagonal_split hB hf, bidiagonal_rowChase, fun hB h hd =>
    bidiagonal_colChase hB h hd⟩

/-! ### §8.6.3 The SVD algorithm: Algorithms 8.6.1–8.6.2 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One chasing pair of Algorithm 8.6.1 on the state $(B, U, V, \mathit{prev})$ at consecutive
window indices $(a, b)$. For the first pair ($\mathit{prev}$ empty) let
$(y, z) = (t_{11} - \mu, t_{12})$, and afterwards $(y, z) = (b_{\mathit{prev}, a},
b_{\mathit{prev}, b})$, which are the book's $y = b_{k,k+1}$ and $z = b_{k,k+2}$. Compute
$(c, s) = \mathrm{givens}(y, z)$, set $B = B\,G(a, b, \theta)$ over the rows of the window and
$V = V\,G(a, b, \theta)$. Then compute $(c, s) = \mathrm{givens}(b_{aa}, b_{ba})$, set
$B = G(a, b, \theta)^T B$ over the columns of the window and $U = U\,G(a, b, \theta)$.

The condition $[y\ z] \begin{bmatrix} c & s \\ -s & c \end{bmatrix} = [*\ 0]$ of the source is
the condition $sy + cz = 0$ of `GolubVanLoan.Chapter05.algorithm_5_1_3`. -/
noncomputable def golubKahanRotate (hnm : n ≤ m) (w : List (Fin n)) (y₀ z₀ : ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Option (Fin n)) (ab : Fin n × Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Option (Fin n)) := do
  let yz : ℝ × ℝ := st.2.2.2.elim (y₀, z₀) fun pr =>
    (st.1 (Fin.castLE hnm pr) ab.1, st.1 (Fin.castLE hnm pr) ab.2)
  let cs ← Chapter05.algorithm_5_1_3 rnd yz.1 yz.2
  let B₁ ← Chapter05.givensApplyRight rnd ab.1 ab.2 cs.1 cs.2 (w.map (Fin.castLE hnm)) st.1
  let V₁ ← Chapter05.givensApplyRight rnd ab.1 ab.2 cs.1 cs.2 (List.finRange n) st.2.2.1
  let cs' ← Chapter05.algorithm_5_1_3 rnd (B₁ (Fin.castLE hnm ab.1) ab.1)
    (B₁ (Fin.castLE hnm ab.2) ab.1)
  let B₂ ← Chapter05.givensApplyLeft rnd (Fin.castLE hnm ab.1) (Fin.castLE hnm ab.2) cs'.1 cs'.2
    w B₁
  let U₁ ← Chapter05.givensApplyRight rnd (Fin.castLE hnm ab.1) (Fin.castLE hnm ab.2) cs'.1
    cs'.2 (List.finRange m) st.2.1
  pure (B₂, U₁, V₁, some ab.1)

/-- **Algorithm 8.6.1** of [golub2013matrix] (Golub–Kahan SVD step). "Given a bidiagonal matrix $B$
having no zeros on its diagonal or superdiagonal, the following algorithm overwrites $B$ with
the bidiagonal matrix $\bar B = \bar U^T B \bar V$ where $\bar U$ and $\bar V$ are orthogonal
and $\bar V$ is essentially the orthogonal matrix that would be obtained by applying Algorithm
8.3.2 to $T = B^T B$."
```
Let μ be the eigenvalue of the trailing 2-by-2 submatrix of T = BᵀB that is closer to t_nn.
y = t₁₁ - μ;  z = t₁₂
for k = 1:n-1
    Determine c, s such that [y z] [c s; -s c] = [* 0];   B = B G(k, k+1, θ)
    y = b_kk;  z = b_{k+1,k}
    Determine c, s such that [c s; -s c]ᵀ [y; z] = [*; 0]; B = G(k, k+1, θ)ᵀ B
    if k < n-1:  y = b_{k,k+1};  z = b_{k,k+2}
end
```

**Typo.** The source says $B \in \mathbb{R}^{m \times n}$ for a square $B$.

The program acts on a window $w$ of consecutive column indices of an $m \times n$ array with
$n \le m$; the rows of the window are the same indices, and the step of the source is the full
window $w$ = `List.finRange n`. It also accumulates $U = U \bar U$ and $V = V \bar V$, as
Algorithm 8.6.2 needs. For a window of length $N \ge 2$ with diagonal $d$ and superdiagonal $f$,
the shift $\mu$ is computed by the formula of Algorithm 8.3.2 from $t_{N-1,N-1} =
\mathrm{fl}(\mathrm{fl}(d_{N-1}^2) + \mathrm{fl}(f_{N-2}^2))$, where $f_{N-2} = 0$ for $N = 2$,
from $t_{NN} = \mathrm{fl}(\mathrm{fl}(d_N^2) + \mathrm{fl}(f_{N-1}^2))$ and from
$t_{N,N-1} = \mathrm{fl}(d_{N-1} f_{N-1})$; then $y = \mathrm{fl}(\mathrm{fl}(d_1^2) - \mu)$ and
$z = \mathrm{fl}(d_1 f_1)$. For $N \le 1$ the program does nothing. -/
noncomputable def algorithm_8_6_1 (hnm : n ≤ m) (w : List (Fin n)) (B : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  match w with
  | f₀ :: f₁ :: rest => do
    let b : Fin n → Fin n → ℝ := fun i j => B (Fin.castLE hnm i) j
    let l := (f₁ :: rest).getLast (List.cons_ne_nil _ _)
    let l' := (f₀ :: f₁ :: rest).dropLast.getLast (by simp)
    let f₂ : ℝ := match rest with
      | [] => 0
      | _ => b ((f₀ :: f₁ :: rest).dropLast.dropLast.getLast?.getD l') l'
    let tpp ← rnd ((← rnd (b l' l' * b l' l')) + (← rnd (f₂ * f₂)))
    let tnn ← rnd ((← rnd (b l l * b l l)) + (← rnd (b l' l * b l' l)))
    let tnp ← rnd (b l' l' * b l' l)
    let μ ← wilkinsonShiftComputed rnd tpp tnn tnp
    let y₀ ← rnd ((← rnd (b f₀ f₀ * b f₀ f₀)) - μ)
    let z₀ ← rnd (b f₀ f₀ * b f₀ f₁)
    let st ← ((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
      (golubKahanRotate rnd hnm (f₀ :: f₁ :: rest) y₀ z₀) (B, U, V, none)
    pure (st.1, st.2.1, st.2.2.1)
  | _ => pure (B, U, V)

/-- The deflation pass of Algorithm 8.6.2: for $i = 1, \dots, n - 1$, set $b_{i,i+1} = 0$ if
$|b_{i,i+1}| \le \mathrm{fl}(\varepsilon \cdot \mathrm{fl}(|b_{ii}| + |b_{i+1,i+1}|))$. The
right side is rounded, and the absolute values and the comparison are exact. -/
noncomputable def svdDeflate (hnm : n ≤ m) (ε : ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) => do
    if h : (i : ℕ) + 1 < n then do
      let e ← rnd (ε * (← rnd (|B (Fin.castLE hnm i) i| +
        |B (Fin.castLE hnm ⟨i + 1, h⟩) ⟨i + 1, h⟩|)))
      if |B (Fin.castLE hnm i) ⟨i + 1, h⟩| ≤ e then
        pure (of fun r s => if r = Fin.castLE hnm i ∧ s = ⟨i + 1, h⟩ then 0 else B r s)
      else pure B
    else pure B) B

open Classical in
/-- The block $B_{22}$ of Algorithm 8.6.2 as a window of consecutive indices. Let $q$ be the largest
number such that the last $q$ columns form a diagonal block $B_{33}$ decoupled from the rest,
and let $p$ be the smallest number such that $B_{22}$ has a nonzero superdiagonal. The window is
$[p, \dots, n - q - 1]$, and it is empty when $q = n$. -/
noncomputable def bidiagonalWindow (hnm : n ≤ m) (B : Matrix (Fin m) (Fin n) ℝ) : List (Fin n) :=
  lastRunWindow n fun i => ∃ h : i + 1 < n,
    B (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0

/-- The decoupling rotations of Algorithm 8.6.2 on a window $w$ of $B$ with a zero diagonal entry
$b_{kk}$, as in `GolubVanLoan.Chapter08.bidiagonal_decouple` (ii) and (iii). If $k$ is not the
last index of the window, rotations of the rows $(j, k)$, $j = k + 1, \dots$, zero row $k$:
$(c, s) = \mathrm{givens}(b_{jj}, b_{kj})$, $B = G(j, k, \theta)^T B$ and
$U = U\,G(j, k, \theta)$. If $k$ is the last index, rotations of the columns $(j, k)$,
$j = k - 1, \dots, p$, zero column $k$: $(c, s) = \mathrm{givens}(b_{jj}, b_{jk})$,
$B = B\,G(j, k, \theta)$ and $V = V\,G(j, k, \theta)$. -/
noncomputable def zeroDiagonalChase (hnm : n ≤ m) (w : List (Fin n)) (k : Fin n)
    (B : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  if w.getLast? = some k then
    ((w.filter (· < k)).reverse).foldlM (fun (st : Matrix (Fin m) (Fin n) ℝ ×
        Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ) j => do
      let cs ← Chapter05.algorithm_5_1_3 rnd (st.1 (Fin.castLE hnm j) j)
        (st.1 (Fin.castLE hnm j) k)
      let B₁ ← Chapter05.givensApplyRight rnd j k cs.1 cs.2 (w.map (Fin.castLE hnm)) st.1
      let V₁ ← Chapter05.givensApplyRight rnd j k cs.1 cs.2 (List.finRange n) st.2.2
      pure (B₁, st.2.1, V₁)) (B, U, V)
  else
    (w.filter (k < ·)).foldlM (fun (st : Matrix (Fin m) (Fin n) ℝ ×
        Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ) j => do
      let cs ← Chapter05.algorithm_5_1_3 rnd (st.1 (Fin.castLE hnm j) j)
        (st.1 (Fin.castLE hnm k) j)
      let B₁ ← Chapter05.givensApplyLeft rnd (Fin.castLE hnm j) (Fin.castLE hnm k) cs.1 cs.2 w
        st.1
      let U₁ ← Chapter05.givensApplyRight rnd (Fin.castLE hnm j) (Fin.castLE hnm k) cs.1 cs.2
        (List.finRange m) st.2.1
      pure (B₁, U₁, st.2.2)) (B, U, V)

open Classical in
/-- One pass of the `until q = n` loop of Algorithm 8.6.2 on the state $(B, U, V, \mathit{done})$.
The pass deflates $B$ and finds the window of $B_{22}$. If the window is empty ($q = n$), the
loop stops. Otherwise, if $B_{22}$ has a zero diagonal entry, the pass decouples by
`GolubVanLoan.Chapter08.zeroDiagonalChase`, and if not, it applies Algorithm 8.6.1 to the window
with the accumulators. -/
noncomputable def svdPass (hnm : n ≤ m) (ε : ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :=
  if st.2.2.2 then pure st else do
    let B ← svdDeflate rnd hnm ε st.1
    match bidiagonalWindow hnm B with
    | [] => pure (B, st.2.1, st.2.2.1, true)
    | w => do
      let r ← match w.find? fun k => B (Fin.castLE hnm k) k = 0 with
        | some k => zeroDiagonalChase rnd hnm w k B st.2.1 st.2.2.1
        | none => algorithm_8_6_1 rnd hnm w B st.2.1 st.2.2.1
      pure (r.1, r.2.1, r.2.2, false)

/-- **Algorithm 8.6.2** of [golub2013matrix] (the SVD algorithm). "Given
$A \in \mathbb{R}^{m \times n}$ ($m \ge n$) and $\varepsilon$, a small multiple of the unit
roundoff, the following algorithm overwrites $A$ with $U^T A V = D + E$, where
$U \in \mathbb{R}^{m \times m}$ is orthogonal, $V \in \mathbb{R}^{n \times n}$ is orthogonal,
$D \in \mathbb{R}^{m \times n}$ is diagonal, and $E$ satisfies $\|E\|_2 \approx u \|A\|_2$."
```
Use Algorithm 5.4.2 to compute the bidiagonalization [B; 0] = (U₁ ⋯ U_n)ᵀ A (V₁ ⋯ V_{n-2})
until q = n
    For i = 1:n-1, set b_{i,i+1} to zero if |b_{i,i+1}| ≤ ε(|b_ii| + |b_{i+1,i+1}|)
    Find the largest q and the smallest p such that B = diag(B₁₁, B₂₂, B₃₃) with B₃₃
    diagonal (q × q) and B₂₂ with a nonzero superdiagonal
    if q < n
        if any diagonal entry in B₂₂ is zero, then zero the superdiagonal entry in the same row
        else apply Algorithm 8.6.1 to B₂₂:
            B = diag(I_p, U, I_{q+m-n})ᵀ B diag(I_p, V, I_q)
    end
end
```

The initial $B$ is the bidiagonal part of the array of Algorithm 5.4.2, and $U$ and $V$ are the
forward accumulations (§5.1.6) of its stored reflectors with the returned values of $\beta$. The
loop runs at most `fuel` passes, with a flag `done`. The result is the tuple of the final $B$,
$U$, $V$ and the flag. -/
noncomputable def algorithm_8_6_2 (hnm : n ≤ m) (ε : ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (fuel : ℕ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) := do
  let r ← Chapter05.algorithm_5_4_2 rnd hnm A
  let U ← Chapter05.forwardAccumulation rnd (Chapter05.storedReflectors r.1 r.2.1)
  let V ← Chapter05.forwardAccumulation rnd
    (List.ofFn fun k => (Chapter05.storedRowVec hnm r.1 k, r.2.2 k))
  (List.range fuel).foldlM (fun st _ => svdPass rnd hnm ε st)
    (Chapter05.bidiagonalPart r.1, U, V, false)

end Programs


/-! ### Algorithm 8.6.2: exact semantics -/

section SVDAlgorithm

open Chapter07 (francisWindow)

/-! ### Rotations of an $m \times n$ array, and windows -/

/-- A row index lies in the rows of the window $[p, q)$ if and only if its value lies in $[p, q)$.
-/
private theorem mem_map_castLE_francisWindow (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n) (r : Fin m) :
    r ∈ (francisWindow n p q).map (Fin.castLE hnm) ↔ p ≤ (r : ℕ) ∧ (r : ℕ) < q := by
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa using Chapter07.mem_francisWindow.1 hi
  · rintro ⟨h1, h2⟩
    exact ⟨⟨r, by omega⟩, Chapter07.mem_francisWindow.2 ⟨h1, h2⟩, Fin.ext rfl⟩

/-- The matrix $X$ agrees with $B$ off the block $[p, q) \times [p, q)$, rows and columns taken by
value. -/
private def AgreeOff (p q : ℕ) (X B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (r : Fin m) (s : Fin n), ¬ ((p ≤ (r : ℕ) ∧ (r : ℕ) < q) ∧ (p ≤ (s : ℕ) ∧ (s : ℕ) < q)) →
    X r s = B r s

/-- The matrix $B$ is decoupled along the window $[p, q)$: its entries with the row in the window
and the column outside it, or the other way round, vanish. -/
private def IsDecoupledAt (p q : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (r : Fin m) (s : Fin n), ((p ≤ (r : ℕ) ∧ (r : ℕ) < q) ∧ ¬ (p ≤ (s : ℕ) ∧ (s : ℕ) < q)) ∨
    (¬ (p ≤ (r : ℕ) ∧ (r : ℕ) < q) ∧ (p ≤ (s : ℕ) ∧ (s : ℕ) < q)) → B r s = 0

private theorem AgreeOff.trans {p q : ℕ} {X Y B : Matrix (Fin m) (Fin n) ℝ}
    (h₁ : AgreeOff p q X Y) (h₂ : AgreeOff p q Y B) : AgreeOff p q X B :=
  fun r s h => (h₁ r s h).trans (h₂ r s h)

private theorem IsDecoupledAt.of_agreeOff {p q : ℕ} {X B : Matrix (Fin m) (Fin n) ℝ}
    (hB : IsDecoupledAt p q B) (h : AgreeOff p q X B) : IsDecoupledAt p q X :=
  fun r s hrs => (h r s (by tauto)).trans (hB r s hrs)

/-- A column rotation in two window columns of a decoupled array changes only the block. -/
private theorem agreeOff_mul_givensRotation {p q : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    (hX : IsDecoupledAt p q X) {a b : Fin n} (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q)
    (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b) (c s : ℝ) :
    AgreeOff p q (X * Chapter05.givensRotation a b c s) X := by
  intro r t hrt
  rw [Chapter05.mul_givensRotation_apply hab]
  by_cases hta : t = a
  · subst hta
    have hr : ¬ (p ≤ (r : ℕ) ∧ (r : ℕ) < q) := fun hr => hrt ⟨hr, ha⟩
    rw [ite_eq_left rfl, hX r t (Or.inr ⟨hr, ha⟩), hX r b (Or.inr ⟨hr, hb⟩)]
    ring
  · by_cases htb : t = b
    · subst htb
      have hr : ¬ (p ≤ (r : ℕ) ∧ (r : ℕ) < q) := fun hr => hrt ⟨hr, hb⟩
      rw [ite_eq_right hta, ite_eq_left rfl, hX r a (Or.inr ⟨hr, ha⟩), hX r t (Or.inr ⟨hr, hb⟩)]
      ring
    · rw [ite_eq_right hta, ite_eq_right htb]

/-- A row rotation in two window rows of a decoupled array changes only the block. -/
private theorem agreeOff_givensRotation_transpose_mul {p q : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    (hX : IsDecoupledAt p q X) {a b : Fin m} (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q)
    (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b) (c s : ℝ) :
    AgreeOff p q ((Chapter05.givensRotation a b c s)ᵀ * X) X := by
  intro r t hrt
  rw [Chapter05.givensRotation_transpose_mul_apply hab]
  by_cases hra : r = a
  · subst hra
    have ht : ¬ (p ≤ (t : ℕ) ∧ (t : ℕ) < q) := fun ht => hrt ⟨ha, ht⟩
    rw [ite_eq_left rfl, hX r t (Or.inl ⟨ha, ht⟩), hX b t (Or.inl ⟨hb, ht⟩)]
    ring
  · by_cases hrb : r = b
    · subst hrb
      have ht : ¬ (p ≤ (t : ℕ) ∧ (t : ℕ) < q) := fun ht => hrt ⟨hb, ht⟩
      rw [ite_eq_right hra, ite_eq_left rfl, hX a t (Or.inl ⟨ha, ht⟩), hX r t (Or.inl ⟨hb, ht⟩)]
      ring
    · rw [ite_eq_right hra, ite_eq_right hrb]

/-- On a decoupled array, the column update over the rows of the window is the full column rotation.
-/
private theorem givensApplyRight_window (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n)
    {X : Matrix (Fin m) (Fin n) ℝ} (hX : IsDecoupledAt p q X) {a b : Fin n}
    (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q) (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b) (c s : ℝ) :
    Id.run (Chapter05.givensApplyRight pure a b c s
        ((francisWindow n p q).map (Fin.castLE hnm)) X) =
      X * Chapter05.givensRotation a b c s := by
  refine Chapter07.givensApplyRight_eq_mul hab c s
    ((Chapter07.nodup_francisWindow n p q).map (Fin.castLE_injective hnm)) fun r hr => ?_
  rw [mem_map_castLE_francisWindow hnm hq] at hr
  exact ⟨hX r a (Or.inr ⟨hr, ha⟩), hX r b (Or.inr ⟨hr, hb⟩)⟩

/-- On a decoupled array, the row update over the columns of the window is the full row rotation. -/
private theorem givensApplyLeft_window {p q : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    (hX : IsDecoupledAt p q X) {a b : Fin m} (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q)
    (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b) (c s : ℝ) :
    Id.run (Chapter05.givensApplyLeft pure a b c s (francisWindow n p q) X) =
      (Chapter05.givensRotation a b c s)ᵀ * X := by
  refine Chapter07.givensApplyLeft_eq_mul hab c s (Chapter07.nodup_francisWindow n p q)
    fun t ht => ?_
  rw [Chapter07.mem_francisWindow] at ht
  exact ⟨hX a t (Or.inl ⟨ha, ht⟩), hX b t (Or.inl ⟨hb, ht⟩)⟩

/-! ### Algorithm 8.6.1 on a window of an $m \times n$ array -/

/-- The zero pattern of the Golub–Kahan chase before the pair $(a, a + 1)$: upper bidiagonal except
for the bulge at $(a - 1, a + 1)$. -/
private def IsRowBulgeAt (a : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (i : Fin m) (l : Fin n), ((l : ℕ) < i ∨ (i : ℕ) + 1 < l) →
    ¬ ((i : ℕ) + 1 = a ∧ (l : ℕ) = a + 1) → X i l = 0

/-- The zero pattern after the column rotation of the pair $(a, a + 1)$: upper bidiagonal except for
the bulge at $(a + 1, a)$. -/
private def IsColBulgeAt (a : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (i : Fin m) (l : Fin n), ((l : ℕ) < i ∨ (i : ℕ) + 1 < l) →
    ¬ ((i : ℕ) = a + 1 ∧ (l : ℕ) = a) → X i l = 0

/-- The column rotation of the pair $(a, a + 1)$, which annihilates the bulge at $(a - 1, a + 1)$,
moves the bulge to $(a + 1, a)$. -/
private theorem isColBulgeAt_mul {a : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} (hX : IsRowBulgeAt a X)
    {a' b' : Fin n} (ha : (a' : ℕ) = a) (hb : (b' : ℕ) = a + 1) {c s : ℝ}
    (hz : ∀ pr : Fin m, (pr : ℕ) + 1 = a → s * X pr a' + c * X pr b' = 0) :
    IsColBulgeAt a (X * Chapter05.givensRotation a' b' c s) := by
  have hab : a' ≠ b' := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  intro i l hil hnb
  rw [Chapter05.mul_givensRotation_apply hab]
  by_cases hla : l = a'
  · rw [ite_eq_left hla]
    subst hla
    rw [hX i l (by omega) (by omega), hX i b' (by omega) (by omega)]
    ring
  rw [ite_eq_right hla]
  by_cases hlb : l = b'
  · rw [ite_eq_left hlb]
    subst hlb
    by_cases hi1 : (i : ℕ) + 1 = a
    · linear_combination hz i hi1
    · rw [hX i a' (by omega) (by omega), hX i l (by omega) (by omega)]
      ring
  rw [ite_eq_right hlb]
  exact hX i l hil (fun h => hlb (Fin.ext (by omega)))

/-- The row rotation of the pair $(a, a + 1)$, which annihilates the bulge at $(a + 1, a)$, moves
the bulge to $(a, a + 2)$. -/
private theorem isRowBulgeAt_mul {a : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} (hX : IsColBulgeAt a X)
    {ra rb : Fin m} {a' : Fin n} (hra : (ra : ℕ) = a) (hrb : (rb : ℕ) = a + 1)
    (ha : (a' : ℕ) = a) {c s : ℝ} (hz : s * X ra a' + c * X rb a' = 0) :
    IsRowBulgeAt (a + 1) ((Chapter05.givensRotation ra rb c s)ᵀ * X) := by
  have hab : ra ≠ rb := fun e => by rw [Fin.ext_iff, hra, hrb] at e; omega
  intro i l hil hnb
  rw [Chapter05.givensRotation_transpose_mul_apply hab]
  by_cases hia : i = ra
  · rw [ite_eq_left hia]
    subst hia
    rw [hX i l (by omega) (by omega), hX rb l (by omega) (by omega)]
    ring
  rw [ite_eq_right hia]
  by_cases hib : i = rb
  · rw [ite_eq_left hib]
    subst hib
    by_cases hla : l = a'
    · subst hla
      exact hz
    · have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext (by omega))
      rw [hX ra l (by omega) (by omega), hX i l (by omega) (by omega)]
      ring
  rw [ite_eq_right hib]
  exact hX i l hil (fun h => hib (Fin.ext (by omega)))

/-- In exact arithmetic, one chasing pair of Algorithm 8.6.1 on a window of a decoupled array gives
the state $(G'^T X G, UG', VG, a)$, where $G$ is the column rotation of the pair and $G'$ is the
row rotation of the new entries $(x_{aa}, x_{ba})$. -/
private theorem golubKahanRotate_window (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n)
    {X : Matrix (Fin m) (Fin n) ℝ} (hX : IsDecoupledAt p q X) {a b : Fin n}
    (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q) (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b)
    (y₀ z₀ : ℝ) (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    (prev : Option (Fin n)) :
    let yz : ℝ × ℝ := prev.elim (y₀, z₀) fun pr =>
      (X (Fin.castLE hnm pr) a, X (Fin.castLE hnm pr) b)
    let cs := Id.run (Chapter05.algorithm_5_1_3 pure yz.1 yz.2)
    let B₁ := X * Chapter05.givensRotation a b cs.1 cs.2
    let cs' := Id.run (Chapter05.algorithm_5_1_3 pure (B₁ (Fin.castLE hnm a) a)
      (B₁ (Fin.castLE hnm b) a))
    Id.run (golubKahanRotate pure hnm (francisWindow n p q) y₀ z₀ (X, U, V, prev) (a, b)) =
      ((Chapter05.givensRotation (Fin.castLE hnm a) (Fin.castLE hnm b) cs'.1 cs'.2)ᵀ * B₁,
        U * Chapter05.givensRotation (Fin.castLE hnm a) (Fin.castLE hnm b) cs'.1 cs'.2,
        V * Chapter05.givensRotation a b cs.1 cs.2, some a) := by
  intro yz cs B₁ cs'
  have hcab : Fin.castLE hnm a ≠ Fin.castLE hnm b := fun e => hab (Fin.castLE_injective hnm e)
  have hB₁ : ∀ c s : ℝ, IsDecoupledAt p q (X * Chapter05.givensRotation a b c s) := fun c s =>
    hX.of_agreeOff (agreeOff_mul_givensRotation hX ha hb hab c s)
  simp only [golubKahanRotate, Id.run_bind, Id.run_pure]
  rw [givensApplyRight_window hnm hq hX ha hb hab,
    givensApplyLeft_window (hB₁ _ _) ha hb hcab,
    Chapter05.givensApplyRight_spec_of_forall_mem hab _ _ (List.nodup_finRange n)
      List.mem_finRange,
    Chapter05.givensApplyRight_spec_of_forall_mem hcab _ _ (List.nodup_finRange m)
      List.mem_finRange]

/-- The loop invariant of Algorithm 8.6.1 on the window $[p, q)$ after $j$ chasing pairs: the state
is $(G^T B H, UG, VH, p + j - 1)$ for orthogonal $G$ and $H$, the first entry agrees with $B$
off the block and has the zero pattern of the chase, and for $j \ge 1$ the first column $He_p$
is that of the first rotation $G(p, p + 1, \theta_0)$ with
$(c_0, s_0) = \mathrm{givens}(y_0, z_0)$. -/
private def GKWindowInv (p q : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin m) (Fin m) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (y₀ z₀ : ℝ) (f₀ f₁ : Fin n) (j : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Option (Fin n)) : Prop :=
  ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
    st.1 = Gᵀ * B * H ∧ st.2.1 = U * G ∧ st.2.2.1 = V * H ∧ AgreeOff p q st.1 B ∧
    IsRowBulgeAt (p + j) st.1 ∧ st.2.2.2.elim (j = 0) (fun pr => 1 ≤ j ∧ (pr : ℕ) + 1 = p + j) ∧
    (j = 0 → H = 1) ∧
    (1 ≤ j → ∃ c₀ s₀ : ℝ, c₀ ^ 2 + s₀ ^ 2 = 1 ∧ s₀ * y₀ + c₀ * z₀ = 0 ∧
      H *ᵥ Pi.single f₀ 1 = Chapter05.givensRotation f₀ f₁ c₀ s₀ *ᵥ Pi.single f₀ 1)

/-- In exact arithmetic, the loop invariant of Algorithm 8.6.1 holds after the $q - p - 1$ chasing
pairs of the window $[p, q)$, for every first pair $(y_0, z_0)$. -/
private theorem gkWindowInv_run (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n) (hpq : p + 2 ≤ q)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (y₀ z₀ : ℝ) (f₀ f₁ : Fin n)
    (hf₀ : (f₀ : ℕ) = p) (hf₁ : (f₁ : ℕ) = p + 1) :
    GKWindowInv p q B U V y₀ z₀ f₀ f₁ (q - p - 1)
      (Id.run (((francisWindow n p q).zip (francisWindow n p q).tail).foldlM
        (golubKahanRotate pure hnm (francisWindow n p q) y₀ z₀) (B, U, V, none))) := by
  set w := francisWindow n p q with hwdef
  have hlen : w.length = q - p := Chapter07.length_francisWindow hq
  have hval : ∀ k (hk : k < w.length), (w[k] : ℕ) = p + k := Chapter07.val_getElem_francisWindow hq
  have hzlen : (w.zip w.tail).length = q - p - 1 := by simp [hlen]
  rw [← hzlen]
  refine List.idRun_foldlM_induction' _ _ (init := (B, U, V, none))
    ⟨1, one_mem _, 1, one_mem _, by simp,
    (Matrix.mul_one U).symm, (Matrix.mul_one V).symm, fun _ _ _ => rfl,
    fun i l hil _ => hB i l (by omega) (by omega), rfl, fun _ => rfl,
    fun h => absurd h (by omega)⟩ ?_
  intro j hj ⟨X, Ua, Va, prev⟩ ⟨G, hGo, H, hHo, hX, hUa, hVa, hXa, hXc, hprev, hH1, hcol⟩
  simp only at hX hUa hVa hXa hXc hprev
  rw [hzlen] at hj
  have hja : j < w.length := by omega
  have hjb : j + 1 < w.length := by omega
  have hpair : (w.zip w.tail)[j]'(by rw [hzlen]; exact hj) = (w[j], w[j + 1]) := by
    simp [List.getElem_zip, List.getElem_tail]
  rw [hpair]
  set a := w[j] with hadef
  set b := w[j + 1] with hbdef
  have ha : (a : ℕ) = p + j := hval j hja
  have hb : (b : ℕ) = p + j + 1 := hval (j + 1) hjb
  have hab : a ≠ b := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  have hXd : IsDecoupledAt p q X := hBd.of_agreeOff hXa
  have haw : p ≤ (a : ℕ) ∧ (a : ℕ) < q := ⟨by omega, by omega⟩
  have hbw : p ≤ (b : ℕ) ∧ (b : ℕ) < q := ⟨by omega, by omega⟩
  rw [golubKahanRotate_window hnm hq hXd haw hbw hab]
  set yz : ℝ × ℝ := prev.elim (y₀, z₀) fun pr =>
    (X (Fin.castLE hnm pr) a, X (Fin.castLE hnm pr) b) with hyz
  obtain ⟨hcs, hzcs, -⟩ := Chapter05.algorithm_5_1_3_spec yz.1 yz.2
  set cs := Id.run (Chapter05.algorithm_5_1_3 pure yz.1 yz.2)
  set Gc := Chapter05.givensRotation a b cs.1 cs.2 with hGc
  set ra := Fin.castLE hnm a with hradef
  set rb := Fin.castLE hnm b with hrbdef
  have hra : (ra : ℕ) = p + j := ha
  have hrb : (rb : ℕ) = p + j + 1 := hb
  have hrab : ra ≠ rb := fun e => by rw [Fin.ext_iff, hra, hrb] at e; omega
  obtain ⟨hcs', hzcs', -⟩ := Chapter05.algorithm_5_1_3_spec ((X * Gc) ra a) ((X * Gc) rb a)
  set cs' := Id.run (Chapter05.algorithm_5_1_3 pure ((X * Gc) ra a) ((X * Gc) rb a))
  set Gr := Chapter05.givensRotation ra rb cs'.1 cs'.2 with hGr
  have hGco : Gc ∈ orthogonalGroup (Fin n) ℝ :=
    Chapter05.givensRotation_mem_orthogonalGroup hab hcs
  have hGro : Gr ∈ orthogonalGroup (Fin m) ℝ :=
    Chapter05.givensRotation_mem_orthogonalGroup hrab hcs'
  have hXGa : AgreeOff p q (X * Gc) X := agreeOff_mul_givensRotation hXd haw hbw hab _ _
  have hXGd : IsDecoupledAt p q (X * Gc) := hXd.of_agreeOff hXGa
  have hXGc : IsColBulgeAt (p + j) (X * Gc) := isColBulgeAt_mul hXc ha hb fun pr hpr => by
    cases prev with
    | none =>
      have hj0 : j = 0 := hprev
      rw [hXd pr a (Or.inr ⟨by omega, haw⟩), hXd pr b (Or.inr ⟨by omega, hbw⟩)]
      ring
    | some pr' =>
      have h2 : (pr' : ℕ) + 1 = p + j := hprev.2
      have hpr' : pr = Fin.castLE hnm pr' := Fin.ext (by simp only [Fin.val_castLE]; omega)
      subst hpr'
      exact hzcs
  refine ⟨G * Gr, Submonoid.mul_mem _ hGo hGro, H * Gc, Submonoid.mul_mem _ hHo hGco, ?_, ?_, ?_,
    (agreeOff_givensRotation_transpose_mul hXGd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hrab
      _ _).trans (hXGa.trans hXa), ?_, ⟨Nat.succ_pos _, by omega⟩,
    fun h => absurd h (Nat.succ_ne_zero _), fun _ => ?_⟩
  · simp only
    rw [hX, transpose_mul]
    simp only [Matrix.mul_assoc]
  · simp only
    rw [hUa, Matrix.mul_assoc]
  · simp only
    rw [hVa, Matrix.mul_assoc]
  · have := isRowBulgeAt_mul hXGc hra hrb ha hzcs'
    rwa [show p + j + 1 = p + (j + 1) by omega] at this
  · rcases Nat.eq_zero_or_pos j with rfl | hj1
    · cases prev with
      | some pr => exact absurd hprev.1 (by omega)
      | none =>
        have ha' : a = f₀ := Fin.ext (by rw [ha, hf₀]; rfl)
        have hb' : b = f₁ := Fin.ext (by rw [hb, hf₁])
        refine ⟨cs.1, cs.2, hcs, hzcs, ?_⟩
        rw [hH1 rfl, Matrix.one_mul, hGc, ha', hb']
    · obtain ⟨c₀, s₀, h₀, hz₀, he₀⟩ := hcol hj1
      refine ⟨c₀, s₀, h₀, hz₀, ?_⟩
      rw [← mulVec_mulVec, givensRotation_mulVec_single_of_ne hab
        (fun e => by rw [e, ha] at hf₀; omega) (fun e => by rw [e, hb] at hf₀; omega), he₀]

/-- A matrix with the zero pattern of the chase after the last pair of the window $[p, q)$ that
agrees with an upper bidiagonal matrix off the block is upper bidiagonal. -/
private theorem isUpperBidiagonalRect_of_isRowBulgeAt {p q : ℕ} (hpq : p + 2 ≤ q)
    {X B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hXa : AgreeOff p q X B)
    (hX : IsRowBulgeAt (q - 1) X) : X.IsUpperBidiagonalRect := by
  intro i l h1 h2
  by_cases hb : (i : ℕ) + 1 = q - 1 ∧ (l : ℕ) = q - 1 + 1
  · rw [hXa i l (fun h => by omega)]
    exact hB i l h1 h2
  · exact hX i l (by omega) hb

/-- In exact arithmetic, for an upper bidiagonal $B$ decoupled along a window $[p, q)$ of at least
two indices, Algorithm 8.6.1 on the window returns $(G^T B H, UG, VH)$ for orthogonal $G$ and
$H$, and $G^T B H$ is upper bidiagonal and agrees with $B$ off the block. -/
private theorem algorithm_8_6_1_window (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n) (hpq : p + 2 ≤ q)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    let out := Id.run (algorithm_8_6_1 pure hnm (francisWindow n p q) B U V)
    ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      out.1 = Gᵀ * B * H ∧ out.2.1 = U * G ∧ out.2.2 = V * H ∧ out.1.IsUpperBidiagonalRect ∧
      AgreeOff p q out.1 B := by
  intro out
  obtain ⟨f₀, f₁, rest, hw⟩ := List.exists_cons_cons_of_two_le_length (l := francisWindow n p q)
    (by rw [Chapter07.length_francisWindow hq]; omega)
  have hlw : 1 < (francisWindow n p q).length := by
    rw [Chapter07.length_francisWindow hq]
    omega
  have hf₀ : (f₀ : ℕ) = p := by
    have := Chapter07.val_getElem_francisWindow hq 0 (Nat.zero_lt_of_lt hlw)
    simpa [hw] using this
  have hf₁ : (f₁ : ℕ) = p + 1 := by
    have := Chapter07.val_getElem_francisWindow hq 1 hlw
    simpa [hw] using this
  have key := fun y₀ z₀ => gkWindowInv_run hnm hq hpq hB hBd U V y₀ z₀ f₀ f₁ hf₀ hf₁
  rw [hw] at key
  simp only [List.tail_cons] at key
  obtain ⟨y₀, z₀, hout⟩ : ∃ y₀ z₀ : ℝ, out =
      ((Id.run (((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
          (golubKahanRotate pure hnm (f₀ :: f₁ :: rest) y₀ z₀) (B, U, V, none))).1,
        (Id.run (((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
          (golubKahanRotate pure hnm (f₀ :: f₁ :: rest) y₀ z₀) (B, U, V, none))).2.1,
        (Id.run (((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
          (golubKahanRotate pure hnm (f₀ :: f₁ :: rest) y₀ z₀) (B, U, V, none))).2.2.1) := by
    exact ⟨_, _, by
      change Id.run (algorithm_8_6_1 pure hnm (francisWindow n p q) B U V) = _
      rw [hw]
      rfl⟩
  obtain ⟨G, hG, H, hH, h1, h2, h3, ha, hc, -⟩ := key y₀ z₀
  rw [hout]
  exact ⟨G, hG, H, hH, h1, h2, h3, isUpperBidiagonalRect_of_isRowBulgeAt hpq hB ha
    (by rwa [show p + (q - p - 1) = q - 1 by omega] at hc), ha⟩

/-! ### Algorithm 8.6.1 on the whole square array -/

/-- In exact arithmetic, the shift that Algorithm 8.6.1 computes from the entries of an upper
bidiagonal $B$ is the Wilkinson shift (8.3.3) of $T = B^T B$. -/
private theorem algorithm_8_6_1_shift {N : ℕ} {B : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hB : B.IsUpperBidiagonal) (f₂ : ℝ)
    (hf₂ : f₂ = if h : N = 0 then 0 else B ⟨N - 1, by omega⟩ (Fin.last N).castSucc) :
    Id.run (wilkinsonShiftComputed pure
      (B (Fin.last N).castSucc (Fin.last N).castSucc * B (Fin.last N).castSucc (Fin.last N).castSucc
        + f₂ * f₂)
      (B (Fin.last (N + 1)) (Fin.last (N + 1)) * B (Fin.last (N + 1)) (Fin.last (N + 1)) +
        B (Fin.last N).castSucc (Fin.last (N + 1)) * B (Fin.last N).castSucc (Fin.last (N + 1)))
      (B (Fin.last N).castSucc (Fin.last N).castSucc * B (Fin.last N).castSucc (Fin.last (N + 1))))
      = wilkinsonShift (Bᵀ * B) := by
  obtain ⟨hTs, -, hdiag, hsup, -⟩ := gram_bidiagonal hB
  set l := Fin.last (N + 1)
  set l' := (Fin.last N).castSucc
  have hl : (l : ℕ) = N + 1 := rfl
  have hl' : (l' : ℕ) = N := by simp [l']
  -- the trailing entries of `T = BᵀB`
  have ha : (Bᵀ * B) l l = B l l * B l l + B l' l * B l' l := by
    rw [hdiag, Finset.sum_eq_single l', ite_eq_left (by rw [hl, hl'])]
    · ring
    · intro j _ hj
      exact ite_eq_right (fun h => hj (Fin.ext (by rw [hl'] ; rw [hl] at h; omega)))
    · simp
  have ha' : (Bᵀ * B) l' l' = B l' l' * B l' l' + f₂ * f₂ := by
    rw [hdiag, hf₂]
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · rw [Finset.sum_eq_zero fun j _ => ite_eq_right (by rw [hl']; omega)]
      simp only [dite_eq_left h0, mul_zero, add_zero]
      ring
    · rw [dite_eq_right (by omega : ¬ N = 0), Finset.sum_eq_single ⟨N - 1, by omega⟩,
        ite_eq_left (by simp only; rw [hl']; omega)]
      · ring
      · intro j _ hj
        exact ite_eq_right fun h => hj (Fin.ext (by rw [hl'] at h; simp only; omega))
      · simp
  have hb : (Bᵀ * B) l l' = B l' l' * B l' l := by
    rw [hTs.apply l' l, hsup l' l (by rw [hl, hl'])]
  rw [wilkinsonShiftComputed_pure, (equation_8_3_3 (Bᵀ * B)).2.2]
  simp only [← ha, ← ha', ← hb]
  rfl

/-- **Algorithm 8.6.1** of [golub2013matrix], exact semantics. Let $B \in \mathbb{R}^{n \times n}$,
$n \ge 2$, be upper bidiagonal with nonzero diagonal and superdiagonal entries, let $T = B^T B$,
let $\mu$ be the Wilkinson shift of $T$, and let $U, V \in \mathbb{R}^{n \times n}$. In exact
arithmetic, Algorithm 8.6.1 on the full window returns $(\bar B, U', V')$, and there are
orthogonal $\bar U$ and $\bar V$ such that:

* $\bar B = \bar U^T B \bar V$ is upper bidiagonal, $U' = U \bar U$ and $V' = V \bar V$;
* $\bar B^T \bar B = \bar V^T T \bar V$;
* $\bar V e_1$ is a multiple of $(T - \mu I) e_1$, and $\bar V^T (T - \mu I)$ is upper
  triangular;
* if $T - \mu I$ is nonsingular, then $\bar B^T \bar B = D\, \hat T\, D$ for a diagonal matrix
  $D$ with entries $\pm 1$, where $\hat T$ is the QR step of $T$ with shift $\mu$.

So the step is the step of Algorithm 8.3.2 on $T$, up to signs; see
`GolubVanLoan.Chapter08.algorithm_8_3_2_spec`. In Lean the order is `N + 2`, the shift is
`GolubVanLoan.Chapter08.wilkinsonShift (Bᵀ * B)`, and the QR step is `Matrix.shiftedQrStep μ T`.
The matrices $\bar U$ and $\bar V$ are the products of the $n - 1$ row rotations and of the
$n - 1$ column rotations. The proof chases one bulge, alternately below the diagonal and to the
right of the superdiagonal. -/
theorem algorithm_8_6_1_spec {N : ℕ} {B : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hB : B.IsUpperBidiagonal) (hd : ∀ i, B i i ≠ 0)
    (hf : ∀ i j : Fin (N + 2), (j : ℕ) = i + 1 → B i j ≠ 0)
    (U V : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) :
    let out := Id.run (algorithm_8_6_1 pure le_rfl (List.finRange (N + 2)) B U V)
    ∃ Ub ∈ orthogonalGroup (Fin (N + 2)) ℝ, ∃ Vb ∈ orthogonalGroup (Fin (N + 2)) ℝ,
      out.1 = Ubᵀ * B * Vb ∧ out.2.1 = U * Ub ∧ out.2.2 = V * Vb ∧ out.1.IsUpperBidiagonal ∧
      out.1ᵀ * out.1 = Vbᵀ * (Bᵀ * B) * Vb ∧
      Vb.col 0 ∈ Submodule.span ℝ {(Bᵀ * B - wilkinsonShift (Bᵀ * B) • 1).col 0} ∧
      (Vbᵀ * (Bᵀ * B - wilkinsonShift (Bᵀ * B) • 1)).IsUpperTriangular ∧
      (IsUnit (Bᵀ * B - wilkinsonShift (Bᵀ * B) • 1).det →
        ∃ d : Fin (N + 2) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧
          out.1ᵀ * out.1 = diagonal d * shiftedQrStep (wilkinsonShift (Bᵀ * B)) (Bᵀ * B) *
            diagonal d) := by
  intro out
  set T := Bᵀ * B with hT
  set μ := wilkinsonShift T with hμ
  obtain ⟨hTs, hTt, hdiag, hsup, hunred⟩ := gram_bidiagonal hB
  have hTu : IsUnreducedTridiagonal T := hunred.2 fun i j hj => mul_ne_zero (hd i) (hf i j hj)
  -- the window and its trailing pair
  have hval : ∀ k (hk : k < (List.finRange (N + 2)).length),
      ((List.finRange (N + 2))[k] : ℕ) = k := fun k hk => by simp
  have hlen : (List.finRange (N + 2)).length = N + 2 := by simp
  obtain ⟨f₀, f₁, rest, hw⟩ :=
    List.exists_cons_cons_of_two_le_length (l := List.finRange (N + 2)) (by simp)
  have hlen' : (f₀ :: f₁ :: rest).length = N + 2 := hw ▸ hlen
  have hval' : ∀ k (hk : k < (f₀ :: f₁ :: rest).length), ((f₀ :: f₁ :: rest)[k] : ℕ) = k :=
    fun k hk => by rw [← List.getElem_of_eq hw]; exact hval k (by omega)
  have hf₀ : f₀ = 0 := Fin.ext (by have := hval' 0 (by simp); simpa using this)
  have hf₁ : f₁ = 1 := Fin.ext (by have := hval' 1 (by simp); simpa using this)
  have hl : (f₁ :: rest).getLast (List.cons_ne_nil _ _) = Fin.last (N + 1) := by
    refine Fin.ext ?_
    rw [← List.getLast_cons (List.cons_ne_nil f₁ rest) (a := f₀), List.getLast_eq_getElem,
      hval' _ (by omega), hlen']
    simp
  have hl' : (f₀ :: f₁ :: rest).dropLast.getLast (by simp) = (Fin.last N).castSucc := by
    refine Fin.ext ?_
    rw [List.getLast_eq_getElem, List.getElem_dropLast, hval' _ (by simp)]
    simp only [List.length_dropLast, hlen']
    simp
  -- the program is the fold of `golubKahanRotate` over the consecutive pairs
  have hBr : B.IsUpperBidiagonalRect := isUpperBidiagonalRect_iff_isUpperBidiagonal.2 hB
  have hBd : IsDecoupledAt 0 (N + 2) B := fun r s h => by
    have := r.isLt
    have := s.isLt
    omega
  have key := gkWindowInv_run le_rfl le_rfl (by omega) hBr hBd U V (B 0 0 * B 0 0 - μ)
    (B 0 0 * B 0 1) 0 1 rfl rfl
  rw [Chapter07.francisWindow_zero] at key
  set st := Id.run (((List.finRange (N + 2)).zip (List.finRange (N + 2)).tail).foldlM
    (golubKahanRotate pure le_rfl (List.finRange (N + 2)) (B 0 0 * B 0 0 - μ) (B 0 0 * B 0 1))
    (B, U, V, none)) with hst
  have hout : out = (st.1, st.2.1, st.2.2.1) := by
    change Id.run (algorithm_8_6_1 pure le_rfl (List.finRange (N + 2)) B U V) = _
    rw [hst, hw, List.tail_cons]
    simp only [algorithm_8_6_1, pure_bind, Id.run_bind, Fin.castLE_refl]
    rw [hl, hl']
    have hrl : rest.length = N := by simp at hlen'; omega
    split
    · have hN : N = 0 := by simp at hlen'; omega
      rw [algorithm_8_6_1_shift hB 0 (by rw [dite_eq_left hN])]
      subst hf₀ hf₁
      rfl
    · rename_i hr
      have hN : N ≠ 0 := fun h0 => hr (List.eq_nil_of_length_eq_zero (by omega))
      have hf₂ : B ((f₀ :: f₁ :: rest).dropLast.dropLast.getLast?.getD (Fin.last N).castSucc)
          (Fin.last N).castSucc = B ⟨N - 1, by omega⟩ (Fin.last N).castSucc := by
        congr 1
        have hne : (f₀ :: f₁ :: rest).dropLast.dropLast ≠ [] := by
          rcases rest with _ | ⟨r, rest'⟩
          · exact absurd rfl hr
          · simp
        rw [List.getLast?_eq_some_getLast hne, Option.getD_some]
        refine Fin.ext ?_
        rw [List.getLast_eq_getElem, List.getElem_dropLast, List.getElem_dropLast,
          hval' _ (by simp; omega)]
        simp
        omega
      rw [algorithm_8_6_1_shift hB _ (by rw [dite_eq_right hN]; exact hf₂)]
      subst hf₀ hf₁
      rfl
  -- the invariant after the last pair
  obtain ⟨Ub, hUo, Vb, hVo, h1, h2, h3, hXa, hXc, -, -, hcol⟩ := key
  rw [hout]
  have hUU : Ub * Ubᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hUo
  have hVV : Vb * Vbᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hVo
  have hVV' : Vbᵀ * Vb = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hVo
  have hbid : st.1.IsUpperBidiagonal := isUpperBidiagonalRect_iff_isUpperBidiagonal.1
    (isUpperBidiagonalRect_of_isRowBulgeAt (by omega) hBr hXa (by simpa using hXc))
  have hgram : st.1ᵀ * st.1 = Vbᵀ * T * Vb := by
    rw [h1, hT, transpose_mul, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ub Ubᵀ, hUU, Matrix.one_mul]
  have htri : (Vbᵀ * T * Vb).IsTridiagonal := hgram ▸ (gram_bidiagonal hbid).2.1
  -- the first column of `V̄`
  obtain ⟨c₀, s₀, hcs, hz, he⟩ := hcol (by omega)
  rw [show ((0 : Fin (N + 2)) : Fin (N + 2)) = 0 from rfl,
    givensRotation_mulVec_single_zero] at he
  have hT00 : T 0 0 = B 0 0 * B 0 0 := by
    rw [hT, hdiag, Finset.sum_eq_zero fun j _ => ite_eq_right (by simp)]
    ring
  have hT10 : T 1 0 = B 0 0 * B 0 1 := by
    rw [hT, ← hTs.apply 1 0, hsup 0 1 (by simp)]
  rw [← hT00, ← hT10] at hz
  have hsub : T 1 0 ≠ 0 := by
    have := hTu.2.apply_succ_castSucc_ne_zero (0 : Fin (N + 1))
    simpa using this
  have hT0 : (T - μ • 1).col 0 = (T 0 0 - μ) • Pi.single 0 1 + T 1 0 • Pi.single 1 1 := by
    funext t
    rw [col_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h0 : t = 0
    · subst h0; simp
    · by_cases h1 : t = 1
      · subst h1; simp
      · have ht : T t 0 = 0 := hTu.1 t 0 (Or.inl ⟨1, by simp, by
          rw [Fin.lt_def]; have : (t : ℕ) ≠ 0 := fun e => h0 (Fin.ext e)
          have : (t : ℕ) ≠ 1 := fun e => h1 (Fin.ext e)
          simp; omega⟩)
        simp [h0, h1, ht]
  set r := c₀ * (T 0 0 - μ) - s₀ * T 1 0 with hr
  have hTr : (T - μ • 1).col 0 = r • Vb.col 0 := by
    have ex : T 0 0 - μ = r * c₀ := by
      rw [hr]; linear_combination (-(T 0 0 - μ)) * hcs + s₀ * hz
    have ez : T 1 0 = -(r * s₀) := by
      rw [hr]; linear_combination (-(T 1 0)) * hcs + c₀ * hz
    rw [← mulVec_single_one Vb 0, he, hT0, ex, ez]
    module
  have hr0 : r ≠ 0 := by
    intro h0
    have := congrFun hTr 1
    rw [h0, zero_smul, Pi.zero_apply, col_apply, Matrix.sub_apply, Matrix.smul_apply,
      one_apply_ne (by simp), smul_zero, sub_zero] at this
    exact hsub this
  have hcol' : Vb.col 0 ∈ Submodule.span ℝ {(T - μ • 1).col 0} := by
    have : Vb.col 0 = r⁻¹ • (T - μ • 1).col 0 := by
      rw [hTr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hstar : star Vb = Vbᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have haeval : Polynomial.aeval T (Polynomial.X - Polynomial.C μ) = T - μ • 1 := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hUT : (Vbᵀ * (T - μ • 1)).IsUpperTriangular := by
    have := IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval hTu.2
      (Polynomial.X - Polynomial.C μ) hVo (by rw [hstar]; exact htri.isUpperHessenberg)
      (by rw [haeval, mulVec_single_one]; exact hcol')
    rwa [haeval, hstar] at this
  refine ⟨Ub, hUo, Vb, hVo, h1, h2, h3, hbid, hgram, hcol', hUT, fun hdet => ?_⟩
  have hstep : IsShiftedQrStep μ T (st.1ᵀ * st.1) := by
    refine ⟨Vb, hVo, Vbᵀ * (T - μ • 1), hUT, ?_, ?_⟩
    · rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
    · rw [hgram, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        hVV', sub_add_cancel]
  obtain ⟨d, hd, hdd⟩ := (isShiftedQrStep_shiftedQrStep μ T).unique_of_isUnit hstep hdet
  refine ⟨d, fun i => ?_, ?_⟩
  · have := hd i
    rw [Real.norm_eq_abs] at this
    exact (abs_eq zero_le_one).1 this
  · rw [hdd, star_eq_conjTranspose, diagonal_conjTranspose, star_trivial]

/-! ### The zero-diagonal chases of Algorithm 8.6.2 -/

/-- One step of the row chase of §8.6.3 on an $m \times n$ array: if the rows other than $k$ have
the bidiagonal pattern and row $k$ is supported in column $j > k$, the rotation of the rows
$(j, k)$ by $\mathrm{givens}(x_{jj}, x_{kj})$ keeps the pattern and moves the support of row $k$
to column $j + 1$. -/
private theorem rowChase_step' {k j : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} {rj rk : Fin m}
    {cj : Fin n} (hrj : (rj : ℕ) = j) (hrk : (rk : ℕ) = k) (hcj : (cj : ℕ) = j) (hkj : k < j)
    (hrows : ∀ (i : Fin m) (l : Fin n), (i : ℕ) ≠ k → X i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1)
    (hrow : ∀ (i : Fin m) (l : Fin n), (i : ℕ) = k → X i l ≠ 0 → (l : ℕ) = j) {c s : ℝ}
    (hz : s * X rj cj + c * X rk cj = 0) :
    (∀ (i : Fin m) (l : Fin n), (i : ℕ) ≠ k →
        ((Chapter05.givensRotation rj rk c s)ᵀ * X) i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (i : ℕ) = k →
        ((Chapter05.givensRotation rj rk c s)ᵀ * X) i l ≠ 0 → (l : ℕ) = j + 1 := by
  have hjk : rj ≠ rk := fun e => by rw [Fin.ext_iff, hrj, hrk] at e; omega
  refine ⟨fun i l hik h => ?_, fun i l hik h => ?_⟩
  · rw [Chapter05.givensRotation_transpose_mul_apply hjk] at h
    by_cases h1 : i = rj
    · rw [ite_eq_left h1] at h
      by_cases hx : X rk l = 0
      · rw [hx, mul_zero, sub_zero] at h
        have := hrows rj l (by omega) (right_ne_zero_of_mul h)
        rwa [h1]
      · have := hrow rk l hrk hx
        left
        rw [h1]
        omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : i = rk
      · exact (hik (by rw [h2]; exact hrk)).elim
      · rw [ite_eq_right h2] at h
        exact hrows i l hik h
  · have hi : i = rk := Fin.ext (by omega)
    rw [Chapter05.givensRotation_transpose_mul_apply hjk, ite_eq_right (by rw [hi]; exact hjk.symm),
      ite_eq_left hi] at h
    by_cases hl : l = cj
    · rw [hl] at h
      exact absurd hz h
    · have hx : X rk l = 0 := by
        by_contra hx
        exact hl (Fin.ext (by rw [hrow rk l hrk hx, hcj]))
      rw [hx, mul_zero, add_zero] at h
      rcases hrows rj l (by omega) (right_ne_zero_of_mul h) with h3 | h3
      · exact absurd (Fin.ext (by omega)) hl
      · omega

/-- One step of the column chase of §8.6.3: if the columns other than $k$ have the bidiagonal
pattern and column $k$ is supported in row $j < k$, the rotation of the columns $(j, k)$ by
$\mathrm{givens}(x_{jj}, x_{jk})$ keeps the pattern and moves the support of column $k$ to row
$j - 1$. -/
private theorem colChase_step' {k j : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} {rj : Fin m}
    {cj ck : Fin n} (hrj : (rj : ℕ) = j) (hcj : (cj : ℕ) = j) (hck : (ck : ℕ) = k) (hjk : j < k)
    (hcols : ∀ (i : Fin m) (l : Fin n), (l : ℕ) ≠ k → X i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1)
    (hcol : ∀ (i : Fin m) (l : Fin n), (l : ℕ) = k → X i l ≠ 0 → (i : ℕ) = j) {c s : ℝ}
    (hz : s * X rj cj + c * X rj ck = 0) :
    (∀ (i : Fin m) (l : Fin n), (l : ℕ) ≠ k →
        (X * Chapter05.givensRotation cj ck c s) i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (l : ℕ) = k →
        (X * Chapter05.givensRotation cj ck c s) i l ≠ 0 → (i : ℕ) + 1 = j := by
  have hjk' : cj ≠ ck := fun e => by rw [Fin.ext_iff, hcj, hck] at e; omega
  refine ⟨fun i l hlk h => ?_, fun i l hlk h => ?_⟩
  · rw [Chapter05.mul_givensRotation_apply hjk'] at h
    by_cases h1 : l = cj
    · rw [ite_eq_left h1] at h
      by_cases hx : X i ck = 0
      · rw [hx, mul_zero, sub_zero] at h
        have := hcols i cj (by omega) (right_ne_zero_of_mul h)
        rwa [h1]
      · have := hcol i ck hck hx
        left
        rw [h1]
        omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : l = ck
      · exact (hlk (by rw [h2]; exact hck)).elim
      · rw [ite_eq_right h2] at h
        exact hcols i l hlk h
  · have hl : l = ck := Fin.ext (by omega)
    rw [Chapter05.mul_givensRotation_apply hjk', ite_eq_right (by rw [hl]; exact hjk'.symm),
      ite_eq_left hl] at h
    by_cases hi : i = rj
    · rw [hi] at h
      exact absurd hz h
    · have hx : X i ck = 0 := by
        by_contra hx
        exact hi (Fin.ext (by rw [hcol i ck hck hx, hrj]))
      rw [hx, mul_zero, add_zero] at h
      rcases hcols i cj (by omega) (right_ne_zero_of_mul h) with h3 | h3
      · exact absurd (Fin.ext (by omega)) hi
      · omega

/-- The indices of the window $[p, q)$ greater than $k \ge p$ form the window $[k + 1, q)$. -/
private theorem filter_gt_francisWindow {p q : ℕ} (k : Fin n) (hpk : p ≤ (k : ℕ)) :
    (francisWindow n p q).filter (fun j => decide (k < j)) = francisWindow n (k + 1) q := by
  unfold Chapter07.francisWindow
  rw [List.filter_filter]
  refine List.filter_congr fun i _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.lt_def]
  omega

/-- The indices of the window $[p, q)$ less than $k \le q$ form the window $[p, k)$. -/
private theorem filter_lt_francisWindow {p q : ℕ} (k : Fin n) (hkq : (k : ℕ) ≤ q) :
    (francisWindow n p q).filter (fun j => decide (j < k)) = francisWindow n p k := by
  unfold Chapter07.francisWindow
  rw [List.filter_filter]
  refine List.filter_congr fun i _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.lt_def]
  omega

/-- In exact arithmetic, for an upper bidiagonal $B$ decoupled along the window $[p, q)$ with
$b_{kk} = 0$ and $k$ not the last index of the window, the rotations of the rows $(j, k)$,
$j = k + 1, \dots, q - 1$, give an orthogonal $G$ such that $G^T B$ is upper bidiagonal with
zero row $k$ and agrees with $B$ off the block; the loop body may be any function whose exact
run is that of the program. -/
private theorem rowChase_spec (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    {k : Fin n} (hpk : p ≤ (k : ℕ)) (hkq : (k : ℕ) + 1 < q) (hkk : B (Fin.castLE hnm k) k = 0)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    {f : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ → Fin n →
      Id (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ)}
    (hf : ∀ st j, Id.run (f st j) =
      (Id.run (Chapter05.givensApplyLeft pure (Fin.castLE hnm j) (Fin.castLE hnm k)
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm k) j))).1
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm k) j))).2 (francisWindow n p q) st.1),
        Id.run (Chapter05.givensApplyRight pure (Fin.castLE hnm j) (Fin.castLE hnm k)
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm k) j))).1
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm k) j))).2 (List.finRange m) st.2.1), st.2.2)) :
    let out := Id.run ((francisWindow n (k + 1) q).foldlM f (B, U, V))
    ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      out.1 = Gᵀ * B * H ∧ out.2.1 = U * G ∧ out.2.2 = V * H ∧ out.1.IsUpperBidiagonalRect ∧
      AgreeOff p q out.1 B := by
  intro out
  set L := francisWindow n (k + 1) q with hL
  have hlen : L.length = q - (k + 1) := Chapter07.length_francisWindow hq
  have hval : ∀ t (ht : t < L.length), (L[t] : ℕ) = k + 1 + t :=
    Chapter07.val_getElem_francisWindow hq
  have key : ∃ G ∈ orthogonalGroup (Fin m) ℝ, out.1 = Gᵀ * B ∧ out.2.1 = U * G ∧ out.2.2 = V ∧
      AgreeOff p q out.1 B ∧
      (∀ (i : Fin m) (l : Fin n), (i : ℕ) ≠ k → out.1 i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (i : ℕ) = k → out.1 i l ≠ 0 → (l : ℕ) = k + 1 + L.length := by
    refine List.idRun_foldlM_induction' L (fun t st => ∃ G ∈ orthogonalGroup (Fin m) ℝ,
      st.1 = Gᵀ * B ∧ st.2.1 = U * G ∧ st.2.2 = V ∧ AgreeOff p q st.1 B ∧
      (∀ (i : Fin m) (l : Fin n), (i : ℕ) ≠ k → st.1 i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (i : ℕ) = k → st.1 i l ≠ 0 → (l : ℕ) = k + 1 + t)
      (init := (B, U, V))
      ⟨1, one_mem _, by simp, (Matrix.mul_one U).symm, rfl, fun _ _ _ => rfl,
        fun i l _ h => ?_, fun i l hi h => ?_⟩ ?_
    · by_contra hc
      exact h (hB i l (by omega) (by omega))
    · by_contra hc
      refine h ?_
      by_cases hl : (l : ℕ) = k
      · rw [show i = Fin.castLE hnm k from Fin.ext hi, show l = k from Fin.ext hl]
        exact hkk
      · exact hB i l (by omega) (by omega)
    intro t ht ⟨X, Ua, Va⟩ ⟨G, hGo, hX, hUa, hVa, hXa, hrows, hrow⟩
    simp only at hX hUa hVa hXa hrows hrow
    have hj : (L[t] : ℕ) = k + 1 + t := hval t ht
    have hjq : (L[t] : ℕ) < q := by omega
    have hrj : (Fin.castLE hnm L[t] : ℕ) = k + 1 + t := hj
    have hrk : (Fin.castLE hnm k : ℕ) = k := rfl
    have hjk : Fin.castLE hnm L[t] ≠ Fin.castLE hnm k := fun e => by
      rw [Fin.ext_iff, hrj, hrk] at e; omega
    have hXd : IsDecoupledAt p q X := hBd.of_agreeOff hXa
    rw [hf]
    simp only
    obtain ⟨hcs, hzcs, -⟩ := Chapter05.algorithm_5_1_3_spec (X (Fin.castLE hnm L[t]) L[t])
      (X (Fin.castLE hnm k) L[t])
    set cs := Id.run (Chapter05.algorithm_5_1_3 pure (X (Fin.castLE hnm L[t]) L[t])
      (X (Fin.castLE hnm k) L[t]))
    have hjw : p ≤ (Fin.castLE hnm L[t] : ℕ) ∧ (Fin.castLE hnm L[t] : ℕ) < q :=
      ⟨by omega, by omega⟩
    have hkw : p ≤ (Fin.castLE hnm k : ℕ) ∧ (Fin.castLE hnm k : ℕ) < q := ⟨by omega, by omega⟩
    rw [givensApplyLeft_window hXd hjw hkw hjk,
      Chapter05.givensApplyRight_spec_of_forall_mem hjk _ _ (List.nodup_finRange m)
        List.mem_finRange]
    obtain ⟨h1, h2⟩ := rowChase_step' hrj hrk hj (by omega) hrows hrow hzcs
    refine ⟨G * Chapter05.givensRotation (Fin.castLE hnm L[t]) (Fin.castLE hnm k) cs.1 cs.2,
      Submonoid.mul_mem _ hGo (Chapter05.givensRotation_mem_orthogonalGroup hjk hcs), ?_, ?_, hVa,
      (agreeOff_givensRotation_transpose_mul hXd hjw hkw hjk _ _).trans hXa, h1,
      fun i l hi h => by have := h2 i l hi h; omega⟩
    · rw [hX, transpose_mul, Matrix.mul_assoc]
    · rw [hUa, Matrix.mul_assoc]
  obtain ⟨G, hG, h1, h2, h3, ha, hrows, hrow⟩ := key
  refine ⟨G, hG, 1, one_mem _, by rw [h1, Matrix.mul_one], h2, by rw [h3, Matrix.mul_one],
    fun i l hl1 hl2 => ?_, ha⟩
  by_contra h0
  by_cases hik : (i : ℕ) = k
  · have hlq := hrow i l hik h0
    rw [hlen] at hlq
    exact h0 ((ha i l fun h => by omega).trans (hB i l (by omega) (by omega)))
  · rcases hrows i l hik h0 with h | h <;> omega

/-- In exact arithmetic, for an upper bidiagonal $B$ decoupled along the window $[p, q)$ with
$b_{kk} = 0$ and $k = q - 1$ the last index of the window, the rotations of the columns
$(j, k)$, $j = k - 1, \dots, p$, give an orthogonal $H$ such that $BH$ is upper bidiagonal with
zero column $k$ and agrees with $B$ off the block. -/
private theorem colChase_spec (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    {k : Fin n} (hpk : p + 1 ≤ (k : ℕ)) (hkq : (k : ℕ) < q) (hkk : B (Fin.castLE hnm k) k = 0)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    {f : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ → Fin n →
      Id (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ)}
    (hf : ∀ st j, Id.run (f st j) =
      (Id.run (Chapter05.givensApplyRight pure j k
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm j) k))).1
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm j) k))).2 ((francisWindow n p q).map (Fin.castLE hnm)) st.1),
        st.2.1,
        Id.run (Chapter05.givensApplyRight pure j k
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm j) k))).1
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm j) k))).2 (List.finRange n) st.2.2))) :
    let out := Id.run ((francisWindow n p k).reverse.foldlM f (B, U, V))
    ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      out.1 = Gᵀ * B * H ∧ out.2.1 = U * G ∧ out.2.2 = V * H ∧ out.1.IsUpperBidiagonalRect ∧
      AgreeOff p q out.1 B := by
  intro out
  set L := (francisWindow n p k).reverse with hL
  have hlen : L.length = k - p := by
    rw [hL, List.length_reverse, Chapter07.length_francisWindow (by omega)]
  have hval : ∀ t (ht : t < L.length), (L[t] : ℕ) + t + 1 = k := fun t ht => by
    have ht' := ht
    rw [hlen] at ht'
    simp only [hL, List.getElem_reverse]
    rw [Chapter07.val_getElem_francisWindow (by omega), Chapter07.length_francisWindow (by omega)]
    omega
  have key : ∃ H ∈ orthogonalGroup (Fin n) ℝ, out.1 = B * H ∧ out.2.1 = U ∧ out.2.2 = V * H ∧
      AgreeOff p q out.1 B ∧
      (∀ (i : Fin m) (l : Fin n), (l : ℕ) ≠ k → out.1 i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (l : ℕ) = k → out.1 i l ≠ 0 → (i : ℕ) + L.length + 1 = k := by
    refine List.idRun_foldlM_induction' L (fun t st => ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      st.1 = B * H ∧ st.2.1 = U ∧ st.2.2 = V * H ∧ AgreeOff p q st.1 B ∧
      (∀ (i : Fin m) (l : Fin n), (l : ℕ) ≠ k → st.1 i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (l : ℕ) = k → st.1 i l ≠ 0 → (i : ℕ) + t + 1 = k)
      (init := (B, U, V))
      ⟨1, one_mem _, (Matrix.mul_one B).symm, rfl, (Matrix.mul_one V).symm, fun _ _ _ => rfl,
        fun i l _ h => ?_, fun i l hl h => ?_⟩ ?_
    · by_contra hc
      exact h (hB i l (by omega) (by omega))
    · by_contra hc
      refine h ?_
      by_cases hi : (i : ℕ) = k
      · rw [show i = Fin.castLE hnm k from Fin.ext hi, show l = k from Fin.ext hl]
        exact hkk
      · exact hB i l (by omega) (by omega)
    intro t ht ⟨X, Ua, Va⟩ ⟨H, hHo, hX, hUa, hVa, hXa, hcols, hcol⟩
    simp only at hX hUa hVa hXa hcols hcol
    have hj : (L[t] : ℕ) + t + 1 = k := hval t ht
    have hrj : (Fin.castLE hnm L[t] : ℕ) = k - 1 - t := by simp only [Fin.val_castLE]; omega
    have hcj : (L[t] : ℕ) = k - 1 - t := by omega
    have hjk : L[t] ≠ k := fun e => by rw [Fin.ext_iff] at e; omega
    have hXd : IsDecoupledAt p q X := hBd.of_agreeOff hXa
    rw [hf]
    simp only
    obtain ⟨hcs, hzcs, -⟩ := Chapter05.algorithm_5_1_3_spec (X (Fin.castLE hnm L[t]) L[t])
      (X (Fin.castLE hnm L[t]) k)
    set cs := Id.run (Chapter05.algorithm_5_1_3 pure (X (Fin.castLE hnm L[t]) L[t])
      (X (Fin.castLE hnm L[t]) k))
    have hjw : p ≤ (L[t] : ℕ) ∧ (L[t] : ℕ) < q := by
      have hmem : L[t] ∈ francisWindow n p k := List.mem_reverse.1 (List.getElem_mem ht)
      have := Chapter07.mem_francisWindow.1 hmem
      omega
    have hkw : p ≤ (k : ℕ) ∧ (k : ℕ) < q := ⟨by omega, hkq⟩
    rw [givensApplyRight_window hnm hq hXd hjw hkw hjk,
      Chapter05.givensApplyRight_spec_of_forall_mem hjk _ _ (List.nodup_finRange n)
        List.mem_finRange]
    obtain ⟨h1, h2⟩ := colChase_step' hrj hcj rfl (by omega) hcols
      (fun i l hl h => by have := hcol i l hl h; omega) hzcs
    refine ⟨H * Chapter05.givensRotation L[t] k cs.1 cs.2,
      Submonoid.mul_mem _ hHo (Chapter05.givensRotation_mem_orthogonalGroup hjk hcs), ?_, hUa, ?_,
      (agreeOff_mul_givensRotation hXd hjw hkw hjk _ _).trans hXa, h1,
      fun i l hl h => by have := h2 i l hl h; omega⟩
    · rw [hX, Matrix.mul_assoc]
    · rw [hVa, Matrix.mul_assoc]
  obtain ⟨H, hH, h1, h2, h3, ha, hcols, hcol⟩ := key
  refine ⟨1, one_mem _, H, hH, by rw [h1, transpose_one, Matrix.one_mul],
    by rw [h2, Matrix.mul_one],
    h3, fun i l hl1 hl2 => ?_, ha⟩
  by_contra h0
  by_cases hlk : (l : ℕ) = k
  · have hip := hcol i l hlk h0
    rw [hlen] at hip
    exact h0 ((ha i l fun h => by omega).trans (hB i l (by omega) (by omega)))
  · rcases hcols i l hlk h0 with h | h <;> omega

/-- In exact arithmetic, for an upper bidiagonal $B$ decoupled along a window $[p, q)$ of at least
two indices and a window index $k$ with $b_{kk} = 0$, the zero-diagonal chase gives orthogonal
$G$ and $H$ such that $B' = G^T B H$ is upper bidiagonal, agrees with $B$ off the block, and the
accumulators become $UG$ and $VH$. -/
private theorem zeroDiagonalChase_window (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n) (hpq : p + 2 ≤ q)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    {k : Fin n} (hk : p ≤ (k : ℕ) ∧ (k : ℕ) < q) (hkk : B (Fin.castLE hnm k) k = 0)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    let out := Id.run (zeroDiagonalChase pure hnm (francisWindow n p q) k B U V)
    ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      out.1 = Gᵀ * B * H ∧ out.2.1 = U * G ∧ out.2.2 = V * H ∧ out.1.IsUpperBidiagonalRect ∧
      AgreeOff p q out.1 B := by
  intro out
  have hlast : (francisWindow n p q).getLast? = some k ↔ (k : ℕ) = q - 1 := by
    have hl : (francisWindow n p q).length - 1 < (francisWindow n p q).length := by
      rw [Chapter07.length_francisWindow hq]; omega
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hl, Option.some_inj]
    constructor
    · rintro h
      rw [← h, Chapter07.val_getElem_francisWindow hq, Chapter07.length_francisWindow hq]
      omega
    · intro h
      apply Fin.ext
      rw [Chapter07.val_getElem_francisWindow hq, h, Chapter07.length_francisWindow hq]
      omega
  by_cases hkl : (k : ℕ) = q - 1
  · have hk' := hlast.2 hkl
    simp only [out, zeroDiagonalChase, hk', ↓reduceIte, filter_lt_francisWindow k hk.2.le]
    exact colChase_spec hnm hq hB hBd (by omega) hk.2 hkk U V (by intros; rfl)
  · have hk' : ¬ (francisWindow n p q).getLast? = some k := fun h => hkl (hlast.1 h)
    simp only [out, zeroDiagonalChase, hk', ↓reduceIte, filter_gt_francisWindow k hk.1]
    exact rowChase_spec hnm hq hB hBd hk.1 (by omega) hkk U V (by intros; rfl)

/-! ### The deflation pass of Algorithm 8.6.2 -/

/-- The deflation test of Algorithm 8.6.2 at the superdiagonal entry $a$, in exact arithmetic:
$|b_{a,a+1}| \le \varepsilon (|b_{aa}| + |b_{a+1,a+1}|)$. -/
private def IsSmallSuper (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ) (a : ℕ) : Prop :=
  ∃ h : a + 1 < n, |D ⟨a, by omega⟩ ⟨a + 1, h⟩| ≤
    ε * (|D ⟨a, by omega⟩ ⟨a, by omega⟩| + |D ⟨a + 1, by omega⟩ ⟨a + 1, h⟩|)

open Classical in
/-- The array after the first $k$ tests of the deflation pass of Algorithm 8.6.2 in exact
arithmetic: the small superdiagonal entries among the first $k$ are set to $0$. -/
private noncomputable def svdDeflateStage (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun r s => if ∃ a < k, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a then 0
    else D r s

open Classical in
private theorem svdDeflateStage_succ_apply (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) (r : Fin m) (s : Fin n) :
    svdDeflateStage hnm ε D (k + 1) r s =
      if (r : ℕ) = k ∧ (s : ℕ) = k + 1 ∧ IsSmallSuper hnm ε D k then 0
      else svdDeflateStage hnm ε D k r s := by
  simp only [svdDeflateStage, of_apply]
  by_cases h1 : ∃ a < k, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a
  · obtain ⟨a, ha, hr, hs, hsm⟩ := h1
    have h1' : ∃ a < k + 1, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a :=
      ⟨a, by omega, hr, hs, hsm⟩
    have h1'' : ∃ a < k, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a :=
      ⟨a, ha, hr, hs, hsm⟩
    rw [ite_eq_left h1', ite_eq_left h1'', ite_self]
  · rw [ite_eq_right h1]
    by_cases h2 : (r : ℕ) = k ∧ (s : ℕ) = k + 1 ∧ IsSmallSuper hnm ε D k
    · have h2' : ∃ a < k + 1, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a :=
        ⟨k, by omega, h2⟩
      rw [ite_eq_left h2', ite_eq_left h2]
    · rw [ite_eq_right, ite_eq_right h2]
      rintro ⟨a, ha, hr, hs, hsm⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · exact h1 ⟨a, ha, hr, hs, hsm⟩
      · exact h2 ⟨hr, hs, hsm⟩

/-- The deflation keeps the entries off the superdiagonal. -/
private theorem svdDeflateStage_apply_of_ne (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ)
    {k : ℕ} {r : Fin m} {s : Fin n} (h : (s : ℕ) ≠ r + 1) :
    svdDeflateStage hnm ε D k r s = D r s := by
  rw [svdDeflateStage, of_apply, ite_eq_right]
  rintro ⟨a, -, h1, h2, -⟩
  omega

open Classical in
/-- The deflation sets the small superdiagonal entries to $0$ and keeps the other superdiagonal
entries. -/
private theorem svdDeflateStage_apply_super (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n) (h : (a : ℕ) + 1 < n) :
    svdDeflateStage hnm ε D n (Fin.castLE hnm a) ⟨a + 1, h⟩ =
      if IsSmallSuper hnm ε D a then 0 else D (Fin.castLE hnm a) ⟨a + 1, h⟩ := by
  simp only [svdDeflateStage, of_apply]
  by_cases hs : IsSmallSuper hnm ε D a
  · rw [ite_eq_left ⟨a, a.isLt, rfl, rfl, hs⟩, ite_eq_left hs]
  · rw [ite_eq_right, ite_eq_right hs]
    rintro ⟨b, -, h1, -, h3⟩
    have hb : b = a := by simp only [Fin.val_castLE] at h1; omega
    subst hb
    exact hs h3


/-- In exact arithmetic, the deflation pass of Algorithm 8.6.2 sets exactly the small superdiagonal
entries of its input to $0$, since every test reads entries that no earlier step has changed. -/
private theorem svdDeflate_pure (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (svdDeflate pure hnm ε D) = svdDeflateStage hnm ε D n := by
  unfold svdDeflate
  refine List.idRun_foldlM_finRange_induction (fun k D' => D' = svdDeflateStage hnm ε D k) ?_ ?_
  · ext r s
    simp only [svdDeflateStage, of_apply]
    rw [ite_eq_right (fun ⟨a, ha, _⟩ => absurd ha (Nat.not_lt_zero a))]
  · intro k D' hD'
    have hstage : ∀ (r : Fin m) (s : Fin n), (s : ℕ) ≠ r + 1 ∨ (k : ℕ) ≤ r → D' r s = D r s := by
      intro r s h
      rw [hD', svdDeflateStage, of_apply, ite_eq_right]
      rintro ⟨a, ha, h1, h2, -⟩
      omega
    by_cases h : (k : ℕ) + 1 < n
    · have e1 := hstage (Fin.castLE hnm k) k (Or.inl (by simp))
      have e2 := hstage (Fin.castLE hnm ⟨k + 1, h⟩) ⟨k + 1, h⟩ (Or.inl (by simp))
      have e3 := hstage (Fin.castLE hnm k) ⟨k + 1, h⟩ (Or.inr (by simp))
      simp only [h, ↓reduceDIte, pure_bind, e1, e2, e3]
      split_ifs with hsm
      · have hsm' : IsSmallSuper hnm ε D k := ⟨h, hsm⟩
        ext r s
        rw [Id.run_pure, of_apply, svdDeflateStage_succ_apply]
        by_cases hp : (r : ℕ) = k ∧ (s : ℕ) = k + 1
        · rw [ite_eq_left (show r = Fin.castLE hnm k ∧ s = ⟨k + 1, h⟩ from
            ⟨Fin.ext hp.1, Fin.ext hp.2⟩), ite_eq_left ⟨hp.1, hp.2, hsm'⟩]
        · rw [ite_eq_right (fun h' => hp ⟨by rw [h'.1]; rfl, by rw [h'.2]⟩),
            ite_eq_right (fun h' => hp ⟨h'.1, h'.2.1⟩), hD']
      · have hsm' : ¬ IsSmallSuper hnm ε D k := fun ⟨_, h'⟩ => hsm h'
        rw [Id.run_pure, hD']
        ext r s
        rw [svdDeflateStage_succ_apply, ite_eq_right (fun h' => hsm' h'.2.2)]
    · simp only [h, ↓reduceDIte, Id.run_pure]
      rw [hD']
      ext r s
      rw [svdDeflateStage_succ_apply, ite_eq_right (fun h' => h h'.2.2.1)]

/-- The deflation keeps an array upper bidiagonal. -/
private theorem isUpperBidiagonalRect_svdDeflateStage (hnm : n ≤ m) (ε : ℝ)
    {D : Matrix (Fin m) (Fin n) ℝ} (hD : D.IsUpperBidiagonalRect) (k : ℕ) :
    (svdDeflateStage hnm ε D k).IsUpperBidiagonalRect := fun i j h1 h2 => by
  rw [svdDeflateStage_apply_of_ne hnm ε D h2]
  exact hD i j h1 h2

open Classical in
/-- The set of indices $a$ with zero superdiagonal entry $b_{a,a+1} = 0$ of an $m \times n$ array.
-/
private noncomputable def zeroSupers (hnm : n ≤ m) (D : Matrix (Fin m) (Fin n) ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ h : (a : ℕ) + 1 < n, D (Fin.castLE hnm a) ⟨a + 1, h⟩ = 0

open Classical in
/-- The set of superdiagonal entries that the deflation of Algorithm 8.6.2 newly sets to $0$. -/
private noncomputable def newSupers (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => IsSmallSuper hnm ε D a ∧
    ∃ h : (a : ℕ) + 1 < n, D (Fin.castLE hnm a) ⟨a + 1, h⟩ ≠ 0

/-- There are at most $n - 1$ zero superdiagonal entries. -/
private theorem card_zeroSupers_le (hnm : n ≤ m) (D : Matrix (Fin m) (Fin n) ℝ) :
    (zeroSupers hnm D).card ≤ n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (Finset.card_le_univ _).trans (by simp)
  have hsub : zeroSupers hnm D ⊆ Finset.univ.erase ⟨n - 1, by omega⟩ := fun a ha => by
    simp only [zeroSupers, Finset.mem_filter] at ha
    obtain ⟨-, h, -⟩ := ha
    refine Finset.mem_erase.2 ⟨fun e => ?_, Finset.mem_univ _⟩
    rw [e] at h
    simp at h
    omega
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- The deflation adds exactly the new zeros to the zero superdiagonal entries. -/
private theorem zeroSupers_svdDeflateStage (hnm : n ≤ m) (ε : ℝ)
    (D : Matrix (Fin m) (Fin n) ℝ) :
    (zeroSupers hnm (svdDeflateStage hnm ε D n)).card =
      (zeroSupers hnm D).card + (newSupers hnm ε D).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext a
    simp only [zeroSupers, newSupers, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h, h0⟩
      rw [svdDeflateStage_apply_super] at h0
      by_cases hs : IsSmallSuper hnm ε D a
      · by_cases hz : D (Fin.castLE hnm a) ⟨a + 1, h⟩ = 0
        · exact Or.inl ⟨h, hz⟩
        · exact Or.inr ⟨hs, h, hz⟩
      · rw [ite_eq_right hs] at h0
        exact Or.inl ⟨h, h0⟩
    · rintro (⟨h, h0⟩ | ⟨hs, h, -⟩)
      · refine ⟨h, ?_⟩
        rw [svdDeflateStage_apply_super]
        split_ifs
        · rfl
        · exact h0
      · exact ⟨h, by rw [svdDeflateStage_apply_super, ite_eq_left hs]⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [zeroSupers, newSupers, Finset.mem_filter] at ha hb
    obtain ⟨-, h, h0⟩ := ha
    obtain ⟨-, -, h', hne⟩ := hb
    exact hne h0

/-- The part of $D$ at the superdiagonal entry $(a, a + 1)$: the matrix with that entry of $D$ and
zeros elsewhere. -/
private def superPart (D : Matrix (Fin m) (Fin n) ℝ) (a : Fin n) : Matrix (Fin m) (Fin n) ℝ :=
  of fun r s => if (r : ℕ) = a ∧ (s : ℕ) = a + 1 then D r s else 0

/-- The change made by the deflation is the sum of the superdiagonal parts at the new zeros. -/
private theorem sub_svdDeflateStage_eq_sum (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ) :
    D - svdDeflateStage hnm ε D n = ∑ a ∈ newSupers hnm ε D, superPart D a := by
  classical
  ext r s
  rw [Matrix.sub_apply, Matrix.sum_apply]
  by_cases hrs : (s : ℕ) = r + 1
  swap
  · rw [svdDeflateStage_apply_of_ne hnm ε D hrs, sub_self]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [superPart, of_apply, ite_eq_right]
    rintro ⟨h1, h2⟩
    omega
  obtain ⟨c, hc, rfl, rfl⟩ : ∃ c : Fin n, ∃ hc : (c : ℕ) + 1 < n,
      r = Fin.castLE hnm c ∧ s = ⟨c + 1, hc⟩ :=
    ⟨⟨r, by omega⟩, by simp only; omega, Fin.ext rfl, Fin.ext hrs⟩
  have hsum : ∑ a ∈ newSupers hnm ε D, superPart D a (Fin.castLE hnm c) ⟨c + 1, hc⟩ =
      if c ∈ newSupers hnm ε D then D (Fin.castLE hnm c) ⟨c + 1, hc⟩ else 0 := by
    rw [← Finset.sum_ite_eq' (newSupers hnm ε D) c (fun _ => D (Fin.castLE hnm c) ⟨c + 1, hc⟩)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [superPart, of_apply]
    by_cases hac : a = c
    · subst hac
      rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl]
    · rw [ite_eq_right (fun h' => hac (Fin.ext h'.1.symm)), ite_eq_right hac]
  rw [hsum, svdDeflateStage_apply_super]
  have hmem : c ∈ newSupers hnm ε D ↔
      IsSmallSuper hnm ε D c ∧ D (Fin.castLE hnm c) ⟨c + 1, hc⟩ ≠ 0 := by
    simp only [newSupers, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hc, h2⟩⟩
  by_cases hsm : IsSmallSuper hnm ε D c
  · rw [ite_eq_left hsm, sub_zero]
    by_cases hz : D (Fin.castLE hnm c) ⟨c + 1, hc⟩ = 0
    · rw [ite_eq_right (fun h' => (hmem.1 h').2 hz), hz]
    · rw [ite_eq_left (hmem.2 ⟨hsm, hz⟩)]
  · rw [ite_eq_right hsm, sub_self, ite_eq_right (fun h' => hsm (hmem.1 h').1)]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The superdiagonal part at the entry $(a, a + 1)$ has Frobenius norm at most the absolute value
of that entry. -/
private theorem norm_superPart_le (hnm : n ≤ m) (D : Matrix (Fin m) (Fin n) ℝ) (a : Fin n)
    (h : (a : ℕ) + 1 < n) : ‖superPart D a‖ ≤ |D (Fin.castLE hnm a) ⟨a + 1, h⟩| := by
  have hsq : ‖superPart D a‖ ^ 2 = |D (Fin.castLE hnm a) ⟨a + 1, h⟩| ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_sq, Finset.sum_eq_single (Fin.castLE hnm a)]
    · rw [Finset.sum_eq_single (⟨a + 1, h⟩ : Fin n)]
      · simp [superPart, Real.norm_eq_abs]
      · intro s _ hs
        rw [superPart, of_apply, ite_eq_right (fun h' => hs (Fin.ext h'.2))]
        simp
      · simp
    · intro r _ hr
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [superPart, of_apply, ite_eq_right (fun h' => hr (Fin.ext h'.1))]
      simp
    · simp
  exact ((pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 hsq).le

/-- The deflation changes $D$ by at most $2 \varepsilon \|D\|_F$ in Frobenius norm for each new
zero. -/
private theorem norm_sub_svdDeflateStage_le (hnm : n ≤ m) {ε : ℝ} (hε : 0 ≤ ε)
    (D : Matrix (Fin m) (Fin n) ℝ) :
    ‖D - svdDeflateStage hnm ε D n‖ ≤ (newSupers hnm ε D).card * (2 * ε * ‖D‖) := by
  rw [sub_svdDeflateStage_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun a ha => ?_
  simp only [newSupers, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨⟨h, hsm⟩, -⟩ := ha
  refine (norm_superPart_le hnm D a h).trans ?_
  have h1 := abs_apply_le_frobenius_norm D (Fin.castLE hnm a) a
  have h2 := abs_apply_le_frobenius_norm D (Fin.castLE hnm ⟨a + 1, h⟩) ⟨a + 1, h⟩
  have hsm' : |D (Fin.castLE hnm a) ⟨a + 1, h⟩| ≤ ε * (|D (Fin.castLE hnm a) a| +
      |D (Fin.castLE hnm ⟨a + 1, h⟩) ⟨a + 1, h⟩|) := hsm
  nlinarith

/-- The loop invariant of Algorithm 8.6.2 on the state $(B, U, V, \mathit{done})$: $U$ and $V$ are
orthogonal, $B$ is upper bidiagonal, $U^T (A + F) V = B$ for a matrix $F$ (the deflations so
far, carried back to $A$) whose norm is at most $\kappa$ for each zero superdiagonal entry of
$B$ when $\kappa$ is large enough, and $B$ is diagonal once the loop has stopped. -/
private def SVDInv (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) (ε κ : ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Bool) : Prop :=
  st.2.1 ∈ orthogonalGroup (Fin m) ℝ ∧ st.2.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧
    st.1.IsUpperBidiagonalRect ∧
    (∃ F : Matrix (Fin m) (Fin n) ℝ, st.2.1ᵀ * (A + F) * st.2.2.1 = st.1 ∧
      (2 * ε * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F‖ ≤ κ * (zeroSupers hnm st.1).card)) ∧
    (st.2.2.2 = true → ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → st.1 i j = 0)

/-- The loop invariant after a step of Algorithm 8.6.2 on the window $[p, q)$ of the deflated array,
either Algorithm 8.6.1 or a zero-diagonal chase: the step is a two-sided orthogonal
transformation that keeps the array upper bidiagonal and changes only the block, whose
superdiagonal is nonzero. -/
private theorem svdInv_window_step (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ} {ε κ : ℝ}
    (hκ0 : 0 ≤ κ) {p q : ℕ} {D₁ F₁ : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (hF₁ : Uᵀ * (A + F₁) * V = D₁)
    (hF₁n : 2 * ε * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F₁‖ ≤ κ * (zeroSupers hnm D₁).card)
    (hrun : ∀ (a : Fin n) (h : (a : ℕ) + 1 < n), p ≤ (a : ℕ) → (a : ℕ) + 1 < q →
      D₁ (Fin.castLE hnm a) ⟨a + 1, h⟩ ≠ 0)
    {M : Id (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ)}
    (hr : ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      (Id.run M).1 = Gᵀ * D₁ * H ∧ (Id.run M).2.1 = U * G ∧ (Id.run M).2.2 = V * H ∧
      (Id.run M).1.IsUpperBidiagonalRect ∧ AgreeOff p q (Id.run M).1 D₁) :
    SVDInv hnm A ε κ (do let r ← M; pure (r.1, r.2.1, r.2.2, false) :
      Id (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Bool)) := by
  change SVDInv hnm A ε κ ((Id.run M).1, (Id.run M).2.1, (Id.run M).2.2, false)
  set r := Id.run M
  obtain ⟨G, hG, H, hH, h1, h2, h3, hb, ha⟩ := hr
  have hzero : (zeroSupers hnm D₁).card ≤ (zeroSupers hnm r.1).card := by
    refine Finset.card_le_card fun a ha' => ?_
    simp only [zeroSupers, Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢
    obtain ⟨h, h0⟩ := ha'
    refine ⟨h, ?_⟩
    rw [ha _ _ fun hin => hrun a h hin.1.1 hin.2.2 h0]
    exact h0
  refine ⟨?_, ?_, hb, ⟨F₁, ?_, fun hκ => ?_⟩, fun h => absurd h (by simp)⟩
  · dsimp only
    rw [h2]
    exact Submonoid.mul_mem _ hU hG
  · dsimp only
    rw [h3]
    exact Submonoid.mul_mem _ hV hH
  · dsimp only
    rw [h1, h2, h3, ← hF₁, transpose_mul]
    simp only [Matrix.mul_assoc]
  · exact (hF₁n hκ).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hzero) hκ0)

/-- In exact arithmetic, one pass of Algorithm 8.6.2 keeps the loop invariant. -/
private theorem svdPass_inv (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ} {ε κ : ℝ} (hε : 0 ≤ ε)
    (hκ0 : 0 ≤ κ)
    {st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool}
    (h : SVDInv hnm A ε κ st) : SVDInv hnm A ε κ (Id.run (svdPass pure hnm ε st)) := by
  obtain ⟨D, U, V, done⟩ := st
  obtain ⟨hU, hV, hDb, ⟨F, hF, hFn⟩, hdone⟩ := h
  dsimp only at hU hV hDb hF hFn hdone
  cases done with
  | true => exact ⟨hU, hV, hDb, ⟨F, hF, hFn⟩, hdone⟩
  | false =>
  unfold svdPass
  simp only [Bool.false_eq_true, ↓reduceIte, Id.run_bind, svdDeflate_pure]
  set D₁ := svdDeflateStage hnm ε D n with hD₁
  have hD₁b : D₁.IsUpperBidiagonalRect := isUpperBidiagonalRect_svdDeflateStage hnm ε hDb n
  have hUt : Uᵀ ∈ orthogonalGroup (Fin m) ℝ := by
    refine (mem_orthogonalGroup_iff' _ ℝ).2 ?_
    rw [transpose_transpose]
    exact (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hVt : Vᵀ ∈ orthogonalGroup (Fin n) ℝ := by
    refine (mem_orthogonalGroup_iff' _ ℝ).2 ?_
    rw [transpose_transpose]
    exact (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hUU : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU
  -- the deflation, carried back
  set F₁ := F - U * (D - D₁) * Vᵀ with hF₁
  have hF₁eq : Uᵀ * (A + F₁) * V = D₁ := by
    have e : A + F₁ = (A + F) - U * (D - D₁) * Vᵀ := by rw [hF₁]; abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul, hF]
    simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ ℝ).1 hV, Matrix.mul_one]
    abel
  have hF₁n : 2 * ε * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F₁‖ ≤ κ * (zeroSupers hnm D₁).card := by
    intro hκ
    have hFb := hFn hκ
    have hz := card_zeroSupers_le hnm D
    have hDn : ‖D‖ ≤ ‖A‖ + κ * (n - 1 : ℕ) := by
      rw [← hF, frobenius_norm_unitary_mul_mul_unitary hUt (A + F) hV]
      have h1 := hFb.trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.2 hz : ((zeroSupers hnm D).card : ℝ) ≤ ((n - 1 : ℕ) : ℝ)) hκ0)
      linarith [norm_add_le A F]
    have hconj : ‖U * (D - D₁) * Vᵀ‖ = ‖D - D₁‖ :=
      frobenius_norm_unitary_mul_mul_unitary hU (D - D₁) hVt
    have he := norm_sub_svdDeflateStage_le hnm hε D
    rw [hD₁, zeroSupers_svdDeflateStage, Nat.cast_add]
    calc ‖F₁‖ ≤ ‖F‖ + ‖U * (D - D₁) * Vᵀ‖ := norm_sub_le _ _
      _ ≤ κ * (zeroSupers hnm D).card + (newSupers hnm ε D).card * (2 * ε * ‖D‖) := by
          rw [hconj]; exact add_le_add hFb he
      _ ≤ κ * (zeroSupers hnm D).card + (newSupers hnm ε D).card * κ := by
          gcongr
          nlinarith
      _ = κ * ((zeroSupers hnm D).card + (newSupers hnm ε D).card) := by ring
  -- the window of `B₂₂`
  have hspec := lastRunWindow_spec (n := n)
    (nz := fun i => ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0)
    (fun i ⟨h, _⟩ => h)
  have hwin : bidiagonalWindow hnm D₁ = lastRunWindow n
      (fun i => ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0) := rfl
  split
  · -- `q = n`: `D₁` is diagonal
    rename_i hw
    refine ⟨hU, hV, hD₁b, ⟨F₁, hF₁eq, hF₁n⟩, fun _ i j hij => ?_⟩
    change D₁ i j = 0
    have hnz : ∀ i, ¬ ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0 := by
      rcases hspec with ⟨-, hno⟩ | ⟨p, e, hpe, he, hw', -⟩
      · exact hno
      · rw [← hwin, hw] at hw'
        have : (⟨p, by omega⟩ : Fin n) ∈ Chapter07.francisWindow n p (e + 2) :=
          Chapter07.mem_francisWindow.2 ⟨le_rfl, show p < e + 2 by omega⟩
        rw [← hw'] at this
        exact absurd this List.not_mem_nil
    by_contra h0
    by_cases hj : (j : ℕ) = i + 1
    · have hj' : j = ⟨i + 1, by omega⟩ := Fin.ext hj
      rw [hj'] at h0
      exact hnz i ⟨by omega, h0⟩
    · exact h0 (hD₁b i j (fun h => hij h.symm) hj)
  · -- `q < n`: a step on the window
    rename_i hne
    obtain ⟨p, e, hpe, he, hw', hrun, hbefore, hafter⟩ : ∃ p e : ℕ, p ≤ e ∧ e + 1 < n ∧
        bidiagonalWindow hnm D₁ = Chapter07.francisWindow n p (e + 2) ∧
        (∀ i, p ≤ i → i ≤ e →
          ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0) ∧
        (0 < p → ¬ ∃ h : p - 1 + 1 < n,
          D₁ (Fin.castLE hnm ⟨p - 1, by omega⟩) ⟨p - 1 + 1, h⟩ ≠ 0) ∧
        ∀ i, e < i → ¬ ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0 := by
      rcases hspec with ⟨hw0, -⟩ | ⟨p, e, hpe, he, hw', h1, h2, h3⟩
      · exact absurd (hwin.trans hw0) hne
      · exact ⟨p, e, hpe, he, hwin.trans hw', h1, h2, h3⟩
    -- `D₁` is decoupled along the window
    have hDd : IsDecoupledAt p (e + 2) D₁ := by
      intro r s hrs
      by_contra h0
      by_cases hsr : (s : ℕ) = r + 1
      · rcases hrs with ⟨hr, hs⟩ | ⟨hr, hs⟩
        · have he1 : e + 1 < n := by omega
          have he2 : e + 1 + 1 < n := by omega
          have hr' : r = Fin.castLE hnm ⟨e + 1, he1⟩ :=
            Fin.ext (by simp only [Fin.val_castLE]; omega)
          have hs' : s = ⟨e + 1 + 1, he2⟩ := Fin.ext (by simp only; omega)
          subst hr' hs'
          exact hafter (e + 1) (by omega) ⟨_, h0⟩
        · have hp : 0 < p := by omega
          have hp1 : p - 1 < n := by omega
          have hp2 : p - 1 + 1 < n := by omega
          have hr' : r = Fin.castLE hnm ⟨p - 1, hp1⟩ :=
            Fin.ext (by simp only [Fin.val_castLE]; omega)
          have hs' : s = ⟨p - 1 + 1, hp2⟩ := Fin.ext (by simp only; omega)
          subst hr' hs'
          exact hbefore hp ⟨_, h0⟩
      · refine h0 (hD₁b r s (fun h => ?_) hsr)
        rcases hrs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have hrun' : ∀ (a : Fin n) (h : (a : ℕ) + 1 < n), p ≤ (a : ℕ) → (a : ℕ) + 1 < e + 2 →
        D₁ (Fin.castLE hnm a) ⟨a + 1, h⟩ ≠ 0 := fun a h hpa hae => by
      obtain ⟨_, hne0⟩ := hrun a hpa (by omega)
      exact hne0
    have he2 : e + 2 ≤ n := by omega
    rw [hw']
    split
    · rename_i k hk
      have hkw := Chapter07.mem_francisWindow.1 (List.mem_of_find?_eq_some hk)
      have hkk : D₁ (Fin.castLE hnm k) k = 0 := by simpa using List.find?_some hk
      exact svdInv_window_step hnm hκ0 hU hV hF₁eq hF₁n hrun'
        (zeroDiagonalChase_window hnm he2 (by omega) hD₁b hDd hkw hkk U V)
    · exact svdInv_window_step hnm hκ0 hU hV hF₁eq hF₁n hrun'
        (algorithm_8_6_1_window hnm he2 (by omega) hD₁b hDd U V)

/-- **Algorithm 8.6.2** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{m \times n}$
with $m \ge n$, let the deflation tolerance satisfy $\varepsilon \ge 0$, and let the number of
passes be arbitrary. In exact arithmetic, the output $(B, U, V, \mathit{done})$ of Algorithm
8.6.2 satisfies:

* $U$ and $V$ are orthogonal, and $B \in \mathbb{R}^{m \times n}$ is upper bidiagonal, so zero
  below row $n$;
* $B = U^T (A + E) V$ for a matrix $E$ with $\|E\|_F \le c\varepsilon \|A\|_F / (1 -
  c\varepsilon)$, $c = 2(n - 1)$, whenever $c\varepsilon < 1$;
* if the loop stopped on its test ($q = n$), then $B$ is diagonal.

The matrix $E$ collects the deflations $b_{i,i+1} := 0$, carried back to $A$. Each deflation
sets to zero an entry with $|b_{i,i+1}| \le \varepsilon (|b_{ii}| + |b_{i+1,i+1}|)$ of the
current $B$, of size at most $2\varepsilon \|B\|_F \le 2\varepsilon (\|A\|_F + \|E\|_F)$. A zero
superdiagonal entry stays zero, because the steps of Algorithm 8.6.1 and the zero-diagonal
chases act only on the unreduced block $B_{22}$, so there are at most $n - 1$ deflations. The
forward form $U^T A V = B + E$ with $E$ supported on the deflated positions is false, as for
`GolubVanLoan.Chapter08.algorithm_8_3_3_spec`: a later rotation on a window starting at $p$
mixes a deflated entry $b_{p-1,p}$ into $b_{p-1,p+1}$. Convergence, that is, that some finite
number of passes suffices, is not claimed. -/
theorem algorithm_8_6_2_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (fuel : ℕ) :
    let out := Id.run (algorithm_8_6_2 pure hnm ε A fuel)
    out.2.1 ∈ orthogonalGroup (Fin m) ℝ ∧ out.2.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧
      out.1.IsUpperBidiagonalRect ∧
      (∃ E : Matrix (Fin m) (Fin n) ℝ, out.2.1ᵀ * (A + E) * out.2.2.1 = out.1 ∧
        (2 * ((n - 1 : ℕ) : ℝ) * ε < 1 →
          ‖E‖ ≤ 2 * ((n - 1 : ℕ) : ℝ) * ε * ‖A‖ / (1 - 2 * ((n - 1 : ℕ) : ℝ) * ε))) ∧
      (out.2.2.2 = true → ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → out.1 i j = 0) := by
  intro out
  set c : ℝ := 2 * ((n - 1 : ℕ) : ℝ) * ε with hc
  set κ : ℝ := if c < 1 then 2 * ε * ‖A‖ / (1 - c) else 0 with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    split_ifs with h
    · exact div_nonneg (by positivity) (by linarith)
    · exact le_rfl
  -- the initial state: chapter 5's bidiagonalization
  obtain ⟨hbid, -, -⟩ := Chapter05.algorithm_5_4_2_spec hnm A
  have h0 : SVDInv hnm A ε κ
      (Chapter05.bidiagonalPart (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).1,
        Id.run (Chapter05.forwardAccumulation pure (Chapter05.storedReflectors
          (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).1
          (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).2.1)),
        Id.run (Chapter05.forwardAccumulation pure (List.ofFn fun k =>
          (Chapter05.storedRowVec hnm (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).1 k,
            (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).2.2 k))),
        false) := by
    rw [Chapter05.forwardAccumulation_spec, Chapter05.forwardAccumulation_spec]
    refine ⟨hbid.mem_unitaryGroup_left, hbid.mem_unitaryGroup_right, hbid.isUpperBidiagonalRect,
      ⟨0, ?_, fun _ => ?_⟩, fun h => absurd h (by simp)⟩
    · rw [add_zero, ← conjTranspose_eq_transpose_of_trivial]
      exact hbid.conjTranspose_mul_mul
    · rw [norm_zero]
      exact mul_nonneg hκ0 (Nat.cast_nonneg _)
  have key : SVDInv hnm A ε κ out :=
    List.idRun_foldlM_induction' (List.range fuel) (fun _ st => SVDInv hnm A ε κ st) h0
      (fun _ _ _ h => svdPass_inv hnm hε hκ0 h)
  obtain ⟨hU, hV, hb, ⟨F, hF, hFn⟩, hdone⟩ := key
  refine ⟨hU, hV, hb, ⟨F, hF, fun hc1 => ?_⟩, hdone⟩
  have hκ : κ = 2 * ε * ‖A‖ / (1 - c) := by rw [hκdef, ite_eq_left hc1]
  rw [hκ, hc] at hFn
  exact deflation_bound (by norm_num) hε (norm_nonneg _) hc1 (card_zeroSupers_le hnm out.1) hFn

/-- **Algorithm 8.6.2** of [golub2013matrix] in the forward form "$U^T A V = D + E$" of the source.
Let $A \in \mathbb{R}^{m \times n}$ with $m \ge n$ and $\varepsilon \ge 0$. In exact arithmetic,
the output $(B, U, V, \mathit{done})$ of Algorithm 8.6.2 satisfies $U^T A V = B + E'$ for a
matrix $E'$ with $\|E'\|_F \le c\varepsilon \|A\|_F / (1 - c\varepsilon)$, $c = 2(n - 1)$,
whenever $c\varepsilon < 1$.

The matrix $E'$ is $-U^T E V$ for the backward error $E$ of
`GolubVanLoan.Chapter08.algorithm_8_6_2_spec`; it has the same Frobenius norm because $U$ and
$V$ are orthogonal. -/
theorem algorithm_8_6_2_forward (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (fuel : ℕ) :
    let out := Id.run (algorithm_8_6_2 pure hnm ε A fuel)
    ∃ E' : Matrix (Fin m) (Fin n) ℝ, out.2.1ᵀ * A * out.2.2.1 = out.1 + E' ∧
      (2 * ((n - 1 : ℕ) : ℝ) * ε < 1 →
        ‖E'‖ ≤ 2 * ((n - 1 : ℕ) : ℝ) * ε * ‖A‖ / (1 - 2 * ((n - 1 : ℕ) : ℝ) * ε)) := by
  intro out
  obtain ⟨hU, hV, -, ⟨E, hE, hEn⟩, -⟩ := algorithm_8_6_2_spec hnm A hε fuel
  refine ⟨-(out.2.1ᵀ * E * out.2.2.1), ?_, fun hc => ?_⟩
  · rw [← hE, Matrix.mul_add, Matrix.add_mul]
    abel
  · rw [norm_neg, frobenius_norm_unitary_mul_mul_unitary
      (Matrix.transpose_mem_unitaryGroup_iff.2 hU) E hV]
    exact hEn hc

end Frobenius

end SVDAlgorithm

end GolubVanLoan.Chapter08
