/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.GSVD
import Numlib.LinearAlgebra.Matrix.LeastSquares.Total
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section01

/-!
# Golub and Van Loan, Section 6.3: Total least squares

This module formalizes §6.3 of [golub2013matrix]. The ordinary least-squares problem
$\min_x \|Ax - b\|_2$ can be recast as $\min \|r\|_2$ over the $r$ with
$b + r \in \operatorname{ran}(A)$ (6.3.1). The total least-squares (TLS) problem (6.3.2)–(6.3.3)
also perturbs $A$: for nonsingular diagonal weights $D = \operatorname{diag}(d_1, \dots, d_m)$ and
$T = \operatorname{diag}(t_1, \dots, t_{n+k})$, it asks for a pair $(E_0, R_0)$ with
$\operatorname{ran}(B + R_0) \subseteq \operatorname{ran}(A + E_0)$ that minimizes
$\|D[E_0 \mid R_0]T\|_F$, and a TLS solution is any $X$ with $(A + E_0)X = B + R_0$. The problem can
fail to have a solution. Theorem 6.3.1 says that under the generic condition
$\sigma_n(C_1) > \sigma_{n+1}(C)$ for $C = D[A \mid B]T = [C_1 \mid C_2]$, the perturbation (6.3.4)
built from the SVD of $C$ is the TLS perturbation, $V_{22}$ is nonsingular, and
$X_{TLS} = -T_1 V_{12} V_{22}^{-1} T_2^{-1}$ is the unique TLS solution.

For one right-hand side $b$ (§6.3.2), the module states the Householder construction of the TLS
solution from the trailing right singular vectors of $C$, and Algorithm 6.3.1 with its
exact-arithmetic correctness. §6.3.3 gives two interpretations: $x_{TLS}$ minimizes the
orthogonal-regression objective (6.3.6), and each term of that objective is the squared distance
from a data point to a hyperplane. The proofs specialize
`Numlib.LinearAlgebra.Matrix.LeastSquares.Total` and `Numlib.Analysis.Matrix.SingularValues`.

## Main definitions

* §6.3.2, `GolubVanLoan.Chapter06.trailingColumns`: the trailing columns $V(:, r{+}1{:}n)$ of a
  matrix.
* §6.3.2, `GolubVanLoan.Chapter06.tlsMatrix`: the matrix $C = D[A \mid b]T$ of the single right-hand
  side, with $n + 1$ columns.
* §6.3.2, `GolubVanLoan.Chapter06.tailStart`: the index $n - p$ where the run
  $\sigma_{n-p+1} = \dots = \sigma_{n+1}$ of computed singular values starts.
* §6.3.2, `GolubVanLoan.Chapter06.tlsScale`: the program that forms $D[A \mid b]T$ entry by entry.
* Algorithm 6.3.1, `GolubVanLoan.Chapter06.algorithm_6_3_1`: total least squares with one right-hand
  side.

## Main results

* Equation (6.3.1), `GolubVanLoan.Chapter06.equation_6_3_1`: $x$ is a least-squares solution if and
  only if $\|Ax - b\|_2$ is the least $\|r\|_2$ with $b + r \in \operatorname{ran}(A)$.
* §6.3, `GolubVanLoan.Chapter06.tls_not_exists_example`: a TLS problem with no solution.
* Theorem 6.3.1, `GolubVanLoan.Chapter06.theorem_6_3_1_isUnit`: if
  $\sigma_n(C_1) > \sigma_{n+1}(C)$, then $V_{22}$ is nonsingular.
* Theorem 6.3.1, `GolubVanLoan.Chapter06.theorem_6_3_1`: under the same condition, (6.3.4) is the
  unique TLS perturbation and $X_{TLS}$ is the unique TLS solution.
* §6.3.1, `GolubVanLoan.Chapter06.tls_tauNorm`: $\|X_{TLS}\|_\tau^2 = \|V_{12}V_{22}^{-1}\|_2^2 =
  (1 - \sigma_k(V_{22})^2)/\sigma_k(V_{22})^2$.
* §6.3.2, `GolubVanLoan.Chapter06.tls_single`: the Householder construction of $x_{TLS}$ for one
  right-hand side, and its failure when $\alpha = 0$.
* Algorithm 6.3.1, `GolubVanLoan.Chapter06.algorithm_6_3_1_spec`: in exact arithmetic the algorithm
  returns a TLS solution, or reports that none exists.
* Equation (6.3.6), `GolubVanLoan.Chapter06.equation_6_3_6`: $x_{TLS}$ minimizes $\psi(x) = \sum_i
  d_i^2 (a_i^T x - b_i)^2 / (x^T T_1^{-2} x + t_{n+1}^{-2})$.
* §6.3.3, `GolubVanLoan.Chapter06.tls_distance`: each term $\delta_i$ of $\psi$ is the squared
  $T$-weighted distance from $[a_i; b_i]$ to the hyperplane $\{[a; b] : b = x^T a\}$.

## Conventions

* Matrices are real and indices are 0-based. The TLS problem with weights
  $D = \operatorname{diag}(d)$ and $T = \operatorname{diag}(t)$ is
  `Matrix.IsTLSPerturbation d t A B E R`, and a TLS solution is `Matrix.IsTLSSolution`. The columns
  of $[A \mid B]$ are indexed by `Fin n ⊕ Fin k`, or by `Fin n ⊕ Unit` for one right-hand side,
  where a column $b$ is `Matrix.replicateCol Unit b`. Problem (6.3.2) is the case $d = 1$, $t = 1$.
* The Frobenius norm is the scoped `Matrix.Norms.Frobenius` norm, and the 2-norm is the scoped
  `Matrix.Norms.L2Operator` norm.
* In Theorem 6.3.1, the matrix $C = D[A \mid B]T = [C_1 \mid C_2]$ is reindexed to the columns
  `Fin (n + k)` by `finSumFinEquiv`. The blocks $V_{12} = V(1{:}n, n{+}1{:}n{+}k)$ and
  $V_{22} = V(n{+}1{:}n{+}k, n{+}1{:}n{+}k)$ are submatrices of $V$.
* For one right-hand side, the matrix $C = D[A \mid b]T$ with the columns `Fin (n + 1)` is
  `GolubVanLoan.Chapter06.tlsMatrix`. It is `Matrix.tlsWeighted` reindexed by
  `finSuccEquivLastSumUnit`, so that the last column belongs to $b$, with the column weights
  `GolubVanLoan.Chapter06.tlsWeights t`. The index $n - p$ of $v_{n+1-p}$ in the source is the
  0-based index `r`.

## Implementation notes

* Algorithm 6.3.1 follows the algorithm conventions of the library: every product and quotient is
  rounded by `rnd`; the step "Compute the SVD" belongs to Chapter 8 and is a monadic parameter; $p$
  is read off the computed singular values by exact comparisons; and the Householder reflection is
  `GolubVanLoan.Chapter05.houseOn` with `GolubVanLoan.Chapter05.householderApplyRight` on index
  lists.

## Deviations from the source

* **Theorem 6.3.1, nonsingularity of $V_{22}$** (generalization). The source assumes that $D$ and
  $T$ are nonsingular and $m \ge n + k$. The nonsingularity of $V_{22}$ holds without these
  hypotheses. See `GolubVanLoan.Chapter06.theorem_6_3_1_isUnit`.
* **§6.3.2, the single right-hand side** (generalization). The source takes $\tilde Q$ to be a
  Householder matrix. The statement holds for every orthogonal $\tilde Q$ with the same zero
  pattern. See `GolubVanLoan.Chapter06.tls_single`.
* **§6.3.2, the single right-hand side** (reading). The source says that the last column has the
  largest $(n{+}1)$st component of all vectors in the span. The statement compares absolute values
  over the unit vectors of the span. See `GolubVanLoan.Chapter06.tls_single`.

## Not formalized

* **The variants of §6.3.4.**
* **The flop count of Algorithm 6.3.1.**
* **The display $[I_{n-1}\ 0; 0\ \tilde Q]\, U^T (D[A \mid b]T)\, V [I_{n-p}\ 0; 0\ \tilde Q] =
  \Sigma$ of §6.3.2.** Its block sizes do not match.
* **The line "$|t_{n+1}| \|Db\|_2 \ge \sigma_n(DAT_1)$" printed after §6.3.4.** It is a displaced
  fragment of Problem P6.3.1(b).
-/

open Matrix

namespace GolubVanLoan.Chapter06

variable {m n : ℕ}

/-- **Equation (6.3.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$b \in \mathbb{R}^m$ and $x \in \mathbb{R}^n$. Then $x$ is a least-squares solution, that is,
$x$ minimizes $\|Ay - b\|_2$ over $y \in \mathbb{R}^n$, if and only if $\|Ax - b\|_2$ is the
least value of $\|r\|_2$ over the $r \in \mathbb{R}^m$ with $b + r \in \operatorname{ran}(A)$:
$$\|Ax - b\|_2 = \min_{b + r \in \operatorname{ran}(A)} \|r\|_2.$$

The minimum is attained at $r = Ax - b$. A least-squares solution is
`Matrix.IsLeastSquaresSolution`, and the least value is `IsLeast` of the image of the feasible
set under the norm. -/
theorem equation_6_3_1 {A : Matrix (Fin m) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} :
    IsLeastSquaresSolution A b x ↔
      IsLeast ((fun r => ‖r‖) '' {r | b + r ∈ LinearMap.range (toEuclideanLin A)})
        ‖toEuclideanLin A x - b‖ := by
  constructor
  · intro h
    refine ⟨⟨toEuclideanLin A x - b, ⟨x, by abel⟩, rfl⟩, ?_⟩
    rintro _ ⟨r, ⟨y, hy⟩, rfl⟩
    have hr : r = toEuclideanLin A y - b := by rw [hy]; abel
    rw [hr]
    exact h y
  · intro h y
    exact h.2 ⟨toEuclideanLin A y - b, ⟨y, by abel⟩, rfl⟩

section Example

open scoped Matrix.Norms.Frobenius

/-- With unit weights, the weighted matrix $D[E \mid R]T$ is $[E \mid R]$. -/
private theorem tlsWeighted_one_one {k : Type*} [Fintype k] [DecidableEq k]
    (E : Matrix (Fin 3) (Fin 2) ℝ) (R : Matrix (Fin 3) k ℝ) :
    tlsWeighted 1 1 E R = fromCols E R := by
  simp [tlsWeighted]

/-- **Section 6.3** of [golub2013matrix], a TLS problem without a solution. Let $$A =
\begin{bmatrix} 1 & 0 \\ 0 & 0 \\ 0 & 0 \end{bmatrix}, \qquad b = \begin{bmatrix} 1 \\ 1 \\ 1
\end{bmatrix}, \qquad E_\varepsilon = \begin{bmatrix} 0 & 0 \\ 0 & \varepsilon \\ 0 &
\varepsilon \end{bmatrix}.$$ Then $b \in \operatorname{ran}(A + E_\varepsilon)$ for every
$\varepsilon > 0$, but the TLS problem (6.3.2) for $A$ and $b$ (with unit weights) has no
solution: no feasible pair $(E, r)$ has the least value of $\|[E \mid r]\|_F$.

A minimizer would satisfy $\|[E \mid r]\|_F \le \|[E_\varepsilon \mid 0]\|_F = \sqrt 2\,
\varepsilon$ for every $\varepsilon > 0$, so $[E \mid r] = 0$ and $b \in \operatorname{ran}(A)$,
which is false. The column $b$ is `Matrix.replicateCol Unit b`, and the TLS problem is
`Matrix.IsTLSPerturbation 1 1`. -/
theorem tls_not_exists_example :
    (∀ ε : ℝ, 0 < ε → ∃ x : Fin 2 → ℝ,
      (!![(1 : ℝ), 0; 0, 0; 0, 0] + ε • !![(0 : ℝ), 0; 0, 1; 0, 1]) *ᵥ x = ![1, 1, 1]) ∧
    ¬ ∃ (E : Matrix (Fin 3) (Fin 2) ℝ) (r : Matrix (Fin 3) Unit ℝ),
      IsTLSPerturbation 1 1 !![(1 : ℝ), 0; 0, 0; 0, 0] (replicateCol Unit ![1, 1, 1]) E r := by
  refine ⟨fun ε hε => ⟨![1, 1 / ε], ?_⟩, ?_⟩
  · ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp
  rintro ⟨E, R, hP⟩
  set E₁ : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 1; 0, 1] with hE₁
  have hfeas : ∀ ε : ℝ, 0 < ε →
      LinearMap.range (replicateCol Unit ![(1 : ℝ), 1, 1] + 0).mulVecLin ≤
        LinearMap.range (!![(1 : ℝ), 0; 0, 0; 0, 0] + ε • E₁).mulVecLin := by
    intro ε hε
    rintro _ ⟨v, rfl⟩
    refine ⟨v () • ![1, 1 / ε], ?_⟩
    ext i
    fin_cases i <;> simp [hE₁, mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp
  set c := ‖fromCols E₁ (0 : Matrix (Fin 3) Unit ℝ)‖
  have hbound : ∀ ε : ℝ, 0 < ε → ‖fromCols E R‖ ≤ ε * c := by
    intro ε hε
    have h := hP.norm_le (ε • E₁) 0 (hfeas ε hε)
    rw [tlsWeighted_one_one, tlsWeighted_one_one] at h
    have e : fromCols (ε • E₁) (0 : Matrix (Fin 3) Unit ℝ) = ε • fromCols E₁ 0 := by
      ext i (j | j) <;> simp
    rwa [e, norm_smul, Real.norm_of_nonneg hε.le] at h
  have hzero : fromCols E R = 0 := by
    rw [← norm_le_zero_iff]
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hc : 0 ≤ c := norm_nonneg _
    have h := hbound (δ / (c + 1)) (by positivity)
    have : δ / (c + 1) * c ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hE : E = 0 := by
    ext i j
    simpa using congrFun (congrFun hzero i) (Sum.inl j)
  have hR : R = 0 := by
    ext i j
    simpa using congrFun (congrFun hzero i) (Sum.inr j)
  have hb := hP.range_le ⟨fun _ => 1, rfl⟩
  obtain ⟨y, hy⟩ := hb
  have h1 := congrFun hy 1
  simp [hE, hR, mulVec, dotProduct, Fin.sum_univ_two] at h1

end Example

/-- **Theorem 6.3.1** of [golub2013matrix], nonsingularity of $V_{22}$. Let
$A \in \mathbb{R}^{m \times n}$, $B \in \mathbb{R}^{m \times k}$, $d \in \mathbb{R}^m$,
$t_1 \in \mathbb{R}^n$ and $t_2 \in \mathbb{R}^k$, and let $D = \operatorname{diag}(d)$,
$T_1 = \operatorname{diag}(t_1)$ and $T_2 = \operatorname{diag}(t_2)$. Let $U^T C V = \Sigma =
\operatorname{diag}(\sigma_1, \dots, \sigma_{n+k})$ be an SVD of $$C = [C_1 \mid C_2] = [DAT_1
\mid DBT_2].$$ If $\sigma_n(C_1) > \sigma_{n+1}$, then the block
$V_{22} = V(n{+}1{:}n{+}k, n{+}1{:}n{+}k)$ is nonsingular.

**Generalization.** The source assumes that $D$ and $T$ are nonsingular and that $m \ge n + k$.
This part of the theorem holds without these hypotheses.

The nonsingularity of $V_{22}$ is the first fact of the proof in the source, and the formula
$X_{TLS} = -T_1 V_{12} V_{22}^{-1} T_2^{-1}$ rests on it. The SVD is `Matrix.IsSVD` of $C$ with
its columns reindexed by `finSumFinEquiv`, so `σ n` is $\sigma_{n+1}$. The number
$\sigma_n(C_1)$ is `sortedSingularValues (n - 1)` of $C_1$. -/
theorem theorem_6_3_1_isUnit {k : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin m) (Fin k) ℝ}
    (d : Fin m → ℝ) (t₁ : Fin n → ℝ) (t₂ : Fin k → ℝ) {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n + k)) (Fin (n + k)) ℝ}
    (hC : IsSVD ((fromCols (diagonal d * A * diagonal t₁) (diagonal d * B * diagonal t₂)).submatrix
      id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (diagonal d * A * diagonal t₁).sortedSingularValues (n - 1)) :
    IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n)) :=
  isUnit_lowerRightBlock_of_lt hC hσ

/-- With $T = \operatorname{diag}(t_1, t_2)$, the weighted matrix $D[E \mid R]T$ is
$[DET_1 \mid DRT_2]$. -/
private theorem tlsWeighted_sumElim {k : ℕ} (d : Fin m → ℝ) (t₁ : Fin n → ℝ) (t₂ : Fin k → ℝ)
    (E : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin m) (Fin k) ℝ) :
    tlsWeighted d (Sum.elim t₁ t₂) E R =
      fromCols (diagonal d * E * diagonal t₁) (diagonal d * R * diagonal t₂) := by
  ext i (j | j) <;> simp [tlsWeighted, mul_diagonal, diagonal_mul]

/-- If $m \ge n + k$, the trailing part $U \Sigma' V^T$ of an SVD, where $\Sigma'$ keeps only the
singular values $\sigma_{n+1}, \dots, \sigma_{n+k}$, equals
$U_2 \Sigma_2 [V_{12}^T \mid V_{22}^T]$ with $U_2 = U(:, n{+}1{:}n{+}k)$ and $\Sigma_2 =
\operatorname{diag}(\sigma_{n+1}, \dots, \sigma_{n+k})$. -/
private theorem mul_rectDiagonal_tail_mul_transpose {k : ℕ} (hmnk : n + k ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → ℝ) (V : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) :
    U * (rectDiagonal (fun i => if i < n then 0 else σ i) : Matrix (Fin m) (Fin (n + k)) ℝ) *
        Vᵀ =
      U.submatrix id (fun j : Fin k => Fin.castLE hmnk (Fin.natAdd n j)) *
        diagonal (fun j : Fin k => σ (n + j)) * (V.submatrix id (Fin.natAdd n))ᵀ := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add, Finset.sum_eq_zero fun i _ => ?_,
      zero_add]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : n + (j : ℕ) < m := by omega
    rw [mul_rectDiagonal_apply, mul_diagonal]
    simp only [Fin.val_natAdd, hj, ↓reduceDIte, add_lt_iff_neg_left, not_lt_zero, ite_false,
      submatrix_apply, id_eq, transpose_apply]
    rfl
  · rw [mul_rectDiagonal_apply]
    split_ifs with h h' <;> simp_all

/-- **Theorem 6.3.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ and
$B \in \mathbb{R}^{m \times k}$ with $m \ge n + k$. Let
$D = \operatorname{diag}(d_1, \dots, d_m)$, $T_1 = \operatorname{diag}(t_1, \dots, t_n)$ and
$T_2 = \operatorname{diag}(t_{n+1}, \dots, t_{n+k})$ be nonsingular, and let
$T = \operatorname{diag}(T_1, T_2)$. Let the SVD of $$C = D[A \mid B]T = [C_1 \mid C_2]$$ be
$U^T C V = \operatorname{diag}(\sigma_1, \dots, \sigma_{n+k}) = \Sigma$, and partition $$U =
[U_1 \mid U_2], \qquad V = \begin{bmatrix} V_{11} & V_{12} \\ V_{21} & V_{22} \end{bmatrix},
\qquad \Sigma = \begin{bmatrix} \Sigma_1 & 0 \\ 0 & \Sigma_2 \end{bmatrix}$$ with the column
blocks of sizes $n$ and $k$, so that $U_2 = U(:, n{+}1{:}n{+}k)$ and $\Sigma_2 =
\operatorname{diag}(\sigma_{n+1}, \dots, \sigma_{n+k})$. If $\sigma_n(C_1) > \sigma_{n+1}(C)$,
then there are $E_0 \in \mathbb{R}^{m \times n}$ and $R_0 \in \mathbb{R}^{m \times k}$ such
that:

* $D[E_0 \mid R_0]T = -U_2 \Sigma_2 [V_{12}^T \mid V_{22}^T]$ (6.3.4);
* $(E_0, R_0)$ solves the TLS problem (6.3.3), and every solution of (6.3.3) equals
  $(E_0, R_0)$;
* $V_{22}$ is nonsingular;
* a matrix $X \in \mathbb{R}^{n \times k}$ satisfies $(A + E_0) X = B + R_0$ if and only if
  $X = X_{TLS}$, where $$X_{TLS} = -T_1 V_{12} V_{22}^{-1} T_2^{-1};$$
* $X$ is a TLS solution if and only if $X = X_{TLS}$.

The source does not state that (6.3.4) is the only TLS perturbation; it follows from
`Matrix.existsUnique_isTLSPerturbation`. The proof in the source cites Corollary 2.4.5 for
$\sigma_n(C) \ge \sigma_n(C_1)$, but that corollary does not give it: the inequality is column
interlacing (Corollary 8.6.3). The backbone does not need $m \ge n + k$; the hypothesis is used
here only to write $U_2 \Sigma_2 [V_{12}^T \mid V_{22}^T]$. The SVD is `Matrix.IsSVD` of $C$
with its columns reindexed by `finSumFinEquiv`, $T$ is `Sum.elim t₁ t₂` on the columns
`Fin n ⊕ Fin k`, and the last two parts come from `Matrix.isTLSSolution_iff_eq`. -/
theorem theorem_6_3_1 {k : ℕ} (hmnk : n + k ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    {B : Matrix (Fin m) (Fin k) ℝ} {d : Fin m → ℝ} {t₁ : Fin n → ℝ} {t₂ : Fin k → ℝ}
    (hd : ∀ i, d i ≠ 0) (ht₁ : ∀ j, t₁ j ≠ 0) (ht₂ : ∀ j, t₂ j ≠ 0)
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + k)) (Fin (n + k)) ℝ}
    (hC : IsSVD ((fromCols (diagonal d * A * diagonal t₁) (diagonal d * B * diagonal t₂)).submatrix
      id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (diagonal d * A * diagonal t₁).sortedSingularValues (n - 1)) :
    ∃ E₀ R₀,
      (fromCols (diagonal d * E₀ * diagonal t₁) (diagonal d * R₀ * diagonal t₂)).submatrix id
          finSumFinEquiv.symm =
        -(U.submatrix id (fun j : Fin k => Fin.castLE hmnk (Fin.natAdd n j)) *
          diagonal (fun j : Fin k => σ (n + j)) * (V.submatrix id (Fin.natAdd n))ᵀ) ∧
      IsTLSPerturbation d (Sum.elim t₁ t₂) A B E₀ R₀ ∧
      (∀ E R, IsTLSPerturbation d (Sum.elim t₁ t₂) A B E R → E = E₀ ∧ R = R₀) ∧
      IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n)) ∧
      (∀ X, (A + E₀) * X = B + R₀ ↔
        X = -(diagonal t₁ * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
          (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ * (diagonal t₂)⁻¹)) ∧
      (∀ X, IsTLSSolution d (Sum.elim t₁ t₂) A B X ↔
        X = -(diagonal t₁ * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
          (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ * (diagonal t₂)⁻¹)) := by
  have ht : ∀ j, Sum.elim t₁ t₂ j ≠ 0 := by
    rintro (j | j)
    exacts [ht₁ j, ht₂ j]
  have hC' := hC
  rw [← tlsWeighted_sumElim] at hC'
  have hσ' : σ n < (tlsWeighted d (Sum.elim t₁ t₂) A B).toCols₁.sortedSingularValues (n - 1) := by
    rwa [tlsWeighted_sumElim, toCols₁_fromCols]
  obtain ⟨⟨E₀, R₀⟩, h₀, huniq⟩ := existsUnique_isTLSPerturbation hd ht hC' hσ'
  have hX := isTLSSolution_iff_eq hd ht hC' hσ'
  simp only [Sum.elim_inl, Sum.elim_inr, RCLike.ofReal_real_eq_id, id_eq] at hX
  have hsol : ∀ X, IsTLSSolution d (Sum.elim t₁ t₂) A B X ↔ (A + E₀) * X = B + R₀ := by
    intro X
    refine ⟨fun ⟨E, R, hP, hEq⟩ => ?_, fun h => ⟨E₀, R₀, h₀, h⟩⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 (huniq (E, R) hP)
    exact hEq
  refine ⟨E₀, R₀, ?_, h₀, fun E R h => Prod.ext_iff.1 (huniq (E, R) h),
    theorem_6_3_1_isUnit d t₁ t₂ hC hσ, fun X => (hsol X).symm.trans (hX X), hX⟩
  -- (6.3.4): `D[E₀ | R₀]T = C_n − C = −U₂Σ₂V₂ᵀ`
  have h' := (isTLSPerturbation_iff hd ht hC' hσ').1 h₀
  rw [tlsWeighted_add] at h'
  have e : (tlsWeighted d (Sum.elim t₁ t₂) E₀ R₀).submatrix id finSumFinEquiv.symm =
      -((tlsWeighted d (Sum.elim t₁ t₂) A B).submatrix id finSumFinEquiv.symm -
        svdTruncation U σ V n) := by
    rw [neg_sub, eq_sub_of_add_eq' h']
    ext i j
    simp
  rw [← tlsWeighted_sumElim, e, hC'.sub_svdTruncation,
    ← mul_rectDiagonal_tail_mul_transpose hmnk, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]
  congr 3

open scoped Matrix.Norms.L2Operator in
/-- **Section 6.3.1** of [golub2013matrix], the $\tau$-norm of the TLS solution. Let
$V \in \mathbb{R}^{(n+k) \times (n+k)}$ be orthogonal with $k \ge 1$, partitioned as in Theorem
6.3.1, and assume that $V_{22}$ is nonsingular. Let $T_1 = \operatorname{diag}(t_1)$ and
$T_2 = \operatorname{diag}(t_2)$ be nonsingular, and let $X = -T_1 V_{12} V_{22}^{-1} T_2^{-1}$.
With the $\tau$-norm $\|Z\|_\tau = \|T_1^{-1} Z T_2\|_2$ on $\mathbb{R}^{n \times k}$,
$$\|X\|_\tau^2 = \|V_{12} V_{22}^{-1}\|_2^2 = \frac{1 -
\sigma_k(V_{22})^2}{\sigma_k(V_{22})^2}.$$

The source derives the identity from the thin CS decomposition. The proof here needs only
$V_{12}^T V_{12} + V_{22}^T V_{22} = I$. The number $\sigma_k(V_{22})$ is
`sortedSingularValues (k - 1)` of $V_{22}$. -/
theorem tls_tauNorm {k : ℕ} [NeZero k] {V : Matrix (Fin (n + k)) (Fin (n + k)) ℝ}
    (hV : V ∈ orthogonalGroup (Fin (n + k)) ℝ)
    (hV₂₂ : IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n))) {t₁ : Fin n → ℝ}
    {t₂ : Fin k → ℝ} (ht₁ : ∀ i, t₁ i ≠ 0) (ht₂ : ∀ j, t₂ j ≠ 0) :
    ‖(diagonal t₁)⁻¹ * -(diagonal t₁ * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ * (diagonal t₂)⁻¹) * diagonal t₂‖ ^ 2 =
      ‖V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹‖ ^ 2 ∧
    ‖V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹‖ ^ 2 =
      (1 - (V.submatrix (Fin.natAdd n) (Fin.natAdd n)).sortedSingularValues (k - 1) ^ 2) /
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n)).sortedSingularValues (k - 1) ^ 2 := by
  set V₁₂ := V.submatrix (Fin.castAdd k) (Fin.natAdd n)
  set V₂₂ := V.submatrix (Fin.natAdd n) (Fin.natAdd n)
  have hd₁ : IsUnit (diagonal t₁).det := by
    rw [det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => ht₁ i).isUnit
  have hd₂ : IsUnit (diagonal t₂).det := by
    rw [det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => ht₂ i).isUnit
  refine ⟨?_, ?_⟩
  · congr 1
    have e : (diagonal t₁)⁻¹ * -(diagonal t₁ * V₁₂ * V₂₂⁻¹ * (diagonal t₂)⁻¹) * diagonal t₂ =
        -(((diagonal t₁)⁻¹ * diagonal t₁) * (V₁₂ * V₂₂⁻¹) * ((diagonal t₂)⁻¹ * diagonal t₂)) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    rw [e, nonsing_inv_mul _ hd₁, nonsing_inv_mul _ hd₂, Matrix.one_mul, Matrix.mul_one, norm_neg]
  · have hVV : Vᵀ * V = 1 := by
      exact (mem_orthogonalGroup_iff' _ ℝ).1 hV
    have hblk : V₁₂ᴴ * V₁₂ + V₂₂ᴴ * V₂₂ = 1 := by
      ext i j
      have h := congrFun (congrFun hVV (Fin.natAdd n i)) (Fin.natAdd n j)
      rw [Matrix.mul_apply, Fin.sum_univ_add] at h
      rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
      simp only [conjTranspose_apply, transpose_apply, star_trivial, V₁₂, V₂₂,
        submatrix_apply] at h ⊢
      rw [h, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.natAdd_inj]
    have := l2_opNorm_mul_inv_sq_eq hV₂₂ hblk
    rwa [Fintype.card_fin] at this

/-- **Equation (6.3.6)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $m > n$,
$b \in \mathbb{R}^m$, $d \in \mathbb{R}^m$, and let $t \in \mathbb{R}^{n+1}$ have nonzero
entries; let $D = \operatorname{diag}(d)$, $T = \operatorname{diag}(t)$ and
$T_1 = \operatorname{diag}(t_1, \dots, t_n)$. Let $U^T C V = \operatorname{diag}(\sigma_1,
\dots, \sigma_{n+1})$ be an SVD of $C = D[A \mid b]T = [C_1 \mid c]$, and assume
$\sigma_n(C_1) > \sigma_{n+1}$. Then the TLS solution $x_{TLS}$, with entries $$x_i = -\frac{t_i
v_{i,n+1}}{t_{n+1} v_{n+1,n+1}}, \qquad i = 1, \dots, n,$$ minimizes over all
$x \in \mathbb{R}^n$ the function $$\psi(x) = \sum_{i=1}^m d_i^2 \frac{(a_i^T x - b_i)^2}{x^T
T_1^{-2} x + t_{n+1}^{-2}}.$$

This is the generic case of Theorem 6.3.1 with one right-hand side, where
$x_{TLS} = -T_1 V_{12} V_{22}^{-1} t_{n+1}^{-1}$. The function $\psi$ is
`Matrix.tlsObjective d t A b`. The statement does not need $d$ to be nonzero. -/
theorem equation_6_3_6 (hmn : n < m) (d : Fin m → ℝ) {t : Fin (n + 1) → ℝ}
    (ht : ∀ j, t j ≠ 0) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hC : IsSVD ((fromCols (diagonal d * A * diagonal fun j => t (Fin.castSucc j))
      (replicateCol (Fin 1) fun i => d i * b i * t (Fin.last n))).submatrix id
        finSumFinEquiv.symm) U σ V)
    (hsep : σ n < (diagonal d * A * diagonal fun j => t (Fin.castSucc j)).sortedSingularValues
      (n - 1)) :
    IsMinOn (tlsObjective d t A b) Set.univ fun j =>
      -(t (Fin.castSucc j) * V (Fin.castSucc j) (Fin.last n)) /
        (t (Fin.last n) * V (Fin.last n) (Fin.last n)) :=
  isMinOn_tlsObjective hmn d ht A b hC hsep

/-! ### §6.3.2 The single right-hand side, Algorithm 6.3.1 -/

/-- The trailing columns $V(:, r{+}1{:}n)$ of a matrix $V$ with $n$ columns: the 0-based columns
$r, \dots, n - 1$. For $r \ge n$ the result has no columns. -/
def trailingColumns {l n : ℕ} (V : Matrix (Fin l) (Fin n) ℝ) (r : ℕ) :
    Matrix (Fin l) (Fin (n - r)) ℝ :=
  V.submatrix id fun j => ⟨r + j, by omega⟩

/-- For $r \le n$, the trailing columns $V(:, r{+}1{:}n)$ are the last $n - r$ columns of $V$, as
given by `Matrix.lastColumns`. -/
theorem trailingColumns_eq_lastColumns {l n : ℕ} (V : Matrix (Fin l) (Fin n) ℝ) {r : ℕ}
    (hr : r ≤ n) : trailingColumns V r = lastColumns V (Nat.sub_le n r) :=
  (lastColumns_eq_submatrix V _ fun j => by simp only; omega).symm

/-- For an orthogonal $V \in \mathbb{R}^{n \times n}$, the trailing columns $W = V(:, r{+}1{:}n)$
are orthonormal: $W^T W = I$. -/
theorem trailingColumns_transpose_mul_self {n : ℕ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (r : ℕ) :
    (trailingColumns V r)ᵀ * trailingColumns V r = 1 := by
  have hVV : Vᵀ * V = 1 := by
    exact (mem_orthogonalGroup_iff' _ ℝ).1 hV
  rw [trailingColumns, transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hVV]
  exact submatrix_one _ fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)

/-- A vector lies in the span of the columns $r, \dots, n$ (0-based) of $V$ if and only if it is
$V(:, r{+}1{:}n{+}1)\, y$ for some $y$. -/
private theorem mem_span_iff_exists_trailingColumns_mulVec
    {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {r : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    x ∈ Submodule.span ℝ ((fun j => (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace ℝ (Fin (n + 1)))) ''
        {j | r ≤ (j : ℕ)}) ↔
      ∃ y, trailingColumns V r *ᵥ y = WithLp.ofLp x := by
  have hset : ((fun j => (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace ℝ (Fin (n + 1)))) ''
      {j | r ≤ (j : ℕ)}) = Set.range fun k : Fin (n + 1 - r) =>
        (WithLp.toLp 2 (Vᵀ ⟨r + k, by omega⟩) : EuclideanSpace ℝ (Fin (n + 1))) := by
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' : r ≤ (j : ℕ) := hj
      have := j.isLt
      refine ⟨⟨j - r, by omega⟩, ?_⟩
      dsimp only
      congr 2
      exact Fin.ext (by simp only; omega)
    · rintro ⟨k, rfl⟩
      exact ⟨_, show r ≤ r + (k : ℕ) by omega, rfl⟩
  rw [hset, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc]
    funext i
    simp [trailingColumns, mulVec, dotProduct, mul_comm]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hx' : x = WithLp.toLp 2 (trailingColumns V r *ᵥ y) := by rw [hy, WithLp.toLp_ofLp]
    rw [hx']
    ext i
    simp [trailingColumns, mulVec, dotProduct, mul_comm]

/-- The column weights $T = \operatorname{diag}(t_1, \dots, t_{n+1})$ of $[A \mid b]$, with the
columns indexed by `Fin n ⊕ Unit`: the weight $t_j$ on column $j$ of $A$ and $t_{n+1}$ on $b$. -/
def tlsWeights (t : Fin (n + 1) → ℝ) : Fin n ⊕ Unit → ℝ :=
  Sum.elim (fun j => t (Fin.castSucc j)) fun _ => t (Fin.last n)

/-- The matrix $C = D[A \mid b]T \in \mathbb{R}^{m \times (n+1)}$ of the single right-hand side in
§6.3.2 of [golub2013matrix], with $D = \operatorname{diag}(d)$ and $T = \operatorname{diag}(t)$;
the last column belongs to $b$. It is `Matrix.tlsWeighted` with the weights
`GolubVanLoan.Chapter06.tlsWeights t`, with its columns reindexed from `Fin n ⊕ Unit` to
`Fin (n + 1)`. -/
noncomputable def tlsMatrix (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Matrix (Fin m) (Fin (n + 1)) ℝ :=
  (tlsWeighted d (tlsWeights t) A (replicateCol Unit b)).submatrix id (finSuccEquivLastSumUnit n)

/-- If the weights $t_1, \dots, t_{n+1}$ are nonzero, then every column weight in
`GolubVanLoan.Chapter06.tlsWeights t` is nonzero. -/
theorem tlsWeights_ne_zero {t : Fin (n + 1) → ℝ} (ht : ∀ j, t j ≠ 0) (j : Fin n ⊕ Unit) :
    tlsWeights t j ≠ 0 := by
  rcases j with j | u
  · exact ht _
  · exact ht _

/-- For $w \in \mathbb{R}^{n+1}$, the product $Cw$ with $C = D[A \mid b]T$ equals the product of the
weighted matrix with columns indexed by `Fin n ⊕ Unit` and the reindexed vector $w$. -/
theorem tlsMatrix_mulVec (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (w : Fin (n + 1) → ℝ) :
    tlsMatrix d t A b *ᵥ w = tlsWeighted d (tlsWeights t) A (replicateCol Unit b) *ᵥ
      (w ∘ (finSuccEquivLastSumUnit n).symm) := by
  rw [tlsMatrix, submatrix_mulVec_equiv]
  rfl

/-- Reindexing a vector by a bijection does not change its Euclidean norm. -/
private theorem norm_toLp_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v : ι → ℝ) :
    ‖(WithLp.toLp 2 (v ∘ e.symm) : EuclideanSpace ℝ κ)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq, comp_equiv_symm_dotProduct]
  congr 1
  funext i
  simp

/-- Let $m > n$ and let $U^T C V = \operatorname{diag}(\sigma_1, \dots, \sigma_{n+1})$ be an SVD of
$C = D[A \mid b]T$. Then the least singular value of $D[A \mid b]T$ is $\sigma_{n+1}$.

The left side is the infimum of `Matrix.colSingularValues` of the weighted matrix with columns
indexed by `Fin n ⊕ Unit`. The singular values are 0-based, so $\sigma_{n+1}$ has the index $n$. -/
theorem iInf_singularValues_tlsWeighted_eq (hmn : n < m) {d : Fin m → ℝ} {t : Fin (n + 1) → ℝ}
    {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hC : IsSVD (tlsMatrix d t A b) U σ V) :
    ⨅ i, (tlsWeighted d (tlsWeights t) A (replicateCol Unit b)).colSingularValues i = σ n := by
  have h0 := hC.iInf_colSingularValues_eq (Nat.succ_pos n) hmn
  rw [Nat.add_sub_cancel] at h0
  rw [← h0, iInf_colSingularValues_eq_iInf_norm,
    iInf_colSingularValues_eq_iInf_norm]
  set e := finSuccEquivLastSumUnit n
  let E : {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ = 1} ≃
      {x : EuclideanSpace ℝ (Fin n ⊕ Unit) // ‖x‖ = 1} :=
    { toFun := fun y => ⟨WithLp.toLp 2 (WithLp.ofLp y.1 ∘ e.symm), by
        rw [norm_toLp_comp_equiv, WithLp.toLp_ofLp]; exact y.2⟩
      invFun := fun x => ⟨WithLp.toLp 2 (WithLp.ofLp x.1 ∘ e.symm.symm), by
        rw [norm_toLp_comp_equiv, WithLp.toLp_ofLp]; exact x.2⟩
      left_inv := fun y => by
        ext i
        simp
      right_inv := fun x => by
        ext i
        simp }
  refine (Equiv.iInf_congr E fun y => ?_).symm
  change ‖toEuclideanLin (tlsWeighted d (tlsWeights t) A (replicateCol Unit b))
      (WithLp.toLp 2 (WithLp.ofLp y.1 ∘ e.symm))‖ = ‖toEuclideanLin (tlsMatrix d t A b) y.1‖
  rw [toEuclideanLin_apply, toEuclideanLin_toLp, tlsMatrix_mulVec]

/-- **Section 6.3.2** of [golub2013matrix], the single right-hand side. Let
$A \in \mathbb{R}^{m \times n}$ with $m > n$ and $b \in \mathbb{R}^m$, and let
$D = \operatorname{diag}(d_1, \dots, d_m)$ and $T = \operatorname{diag}(t_1, \dots, t_{n+1})$ be
nonsingular. Let $U^T C V = \operatorname{diag}(\sigma_1, \dots, \sigma_{n+1})$ be an SVD of
$C = D[A \mid b]T$, with $V = [v_1 \mid \dots \mid v_{n+1}]$. Let $0 \le r \le n$ with
$$\sigma_1, \dots, \sigma_r > \sigma_{r+1} = \sigma_{n+1}$$ (the source writes $r = n - p$), and
let $\tilde Q \in \mathbb{R}^{(p+1) \times (p+1)}$ be orthogonal with $$V(:, r{+}1{:}n{+}1)\,
\tilde Q = \begin{bmatrix} W & z \\ 0 & \alpha \end{bmatrix},$$ that is, the last row of the
product is zero except in its last entry $\alpha$. Then:

* the last column $[z; \alpha]$ has the largest $(n{+}1)$st component in absolute value among
  the unit vectors of $\operatorname{span}\{v_{r+1}, \dots, v_{n+1}\}$:
  $|(V(:, r{+}1{:}n{+}1)\, y)_{n+1}| \le |\alpha|$ for every unit vector
  $y \in \mathbb{R}^{p+1}$;
* if $\alpha = 0$, then the TLS problem has no solution;
* if $\alpha \neq 0$, then there is a TLS perturbation $(E_0, r_0)$ with
  $(A + E_0)\, x_{TLS} = b + r_0$ for $x_{TLS} = -T_1 z / (t_{n+1} \alpha)$, where
  $T_1 = \operatorname{diag}(t_1, \dots, t_n)$, and $$D[E_0 \mid r_0]T = -D[A \mid b]T
  \begin{bmatrix} z \\ \alpha \end{bmatrix} [z^T \mid \alpha].$$

**Generalization.** The source takes $\tilde Q$ to be a Householder matrix. Any orthogonal
matrix with the zero pattern works, and a Householder matrix is one.

**Reading.** The source says that the last column has the largest $(n{+}1)$st component of all
the vectors in the span. The statement reads this as a comparison of absolute values over the
unit vectors of the span.

The source also prints the display $[I_{n-1}\ 0; 0\ \tilde Q]\, U^T (D[A \mid b]T)\, V [I_{n-p}\
0; 0\ \tilde Q] = \Sigma$. Its block sizes do not match, and it is not stated. Here $C$ is
`GolubVanLoan.Chapter06.tlsMatrix d t A b`, $V(:, r{+}1{:}n{+}1)$ is
`GolubVanLoan.Chapter06.trailingColumns V r`, and the TLS problem is `Matrix.IsTLSPerturbation`
with the weights `d` and `GolubVanLoan.Chapter06.tlsWeights t`. -/
theorem tls_single (hmn : n < m) {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) {t : Fin (n + 1) → ℝ}
    (ht : ∀ j, t j ≠ 0) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hC : IsSVD (tlsMatrix d t A b) U σ V) {r : ℕ} (hr : r ≤ n) (hgap : ∀ j < r, σ n < σ j)
    (heq : σ r = σ n) {Q : Matrix (Fin (n + 1 - r)) (Fin (n + 1 - r)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (n + 1 - r)) ℝ)
    (hW : ∀ j : Fin (n + 1 - r), (j : ℕ) < n - r → (trailingColumns V r * Q) (Fin.last n) j = 0) :
    (∀ y : Fin (n + 1 - r) → ℝ, y ⬝ᵥ y = 1 →
      |(trailingColumns V r *ᵥ y) (Fin.last n)| ≤
        |(trailingColumns V r * Q) (Fin.last n) ⟨n - r, by omega⟩|) ∧
    ((trailingColumns V r * Q) (Fin.last n) ⟨n - r, by omega⟩ = 0 →
      ¬ ∃ X, IsTLSSolution d (tlsWeights t) A (replicateCol Unit b) X) ∧
    ((trailingColumns V r * Q) (Fin.last n) ⟨n - r, by omega⟩ ≠ 0 →
      ∃ E R, IsTLSPerturbation d (tlsWeights t) A (replicateCol Unit b) E R ∧
        (A + E) * replicateCol Unit (fun j =>
          -(t (Fin.castSucc j) * (trailingColumns V r * Q) (Fin.castSucc j) ⟨n - r, by omega⟩) /
            (t (Fin.last n) * (trailingColumns V r * Q) (Fin.last n) ⟨n - r, by omega⟩)) =
          replicateCol Unit b + R ∧
        tlsWeighted d (tlsWeights t) E R =
          -vecMulVec (tlsWeighted d (tlsWeights t) A (replicateCol Unit b) *ᵥ
            fun x => (trailingColumns V r * Q) ((finSuccEquivLastSumUnit n).symm x)
              ⟨n - r, by omega⟩)
            fun x => (trailingColumns V r * Q) ((finSuccEquivLastSumUnit n).symm x)
              ⟨n - r, by omega⟩) := by
  set e := finSuccEquivLastSumUnit n with he
  set Vt := trailingColumns V r with hVt
  set W : Matrix (Fin n ⊕ Unit) (Fin (n + 1 - r)) ℝ := Vt.submatrix e.symm id with hWdef
  have hV := hC.mem_unitaryGroup_right
  have ht' := tlsWeights_ne_zero ht
  have hinf := iInf_singularValues_tlsWeighted_eq hmn hC
  -- the columns of `W` are orthonormal
  have hWW : Wᴴ * W = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial, hWdef, transpose_submatrix,
      submatrix_mul_equiv _ _ _ e.symm, trailingColumns_transpose_mul_self hV r, submatrix_id_id]
  -- the minimizers of `‖C w‖ / ‖w‖` are the range of `W`
  have hmin : ∀ w : EuclideanSpace ℝ (Fin n ⊕ Unit),
      ‖toEuclideanLin (tlsWeighted d (tlsWeights t) A (replicateCol Unit b)) w‖ =
          (⨅ j, (tlsWeighted d (tlsWeights t) A (replicateCol Unit b)).colSingularValues j) *
            ‖w‖ ↔ w ∈ LinearMap.range (toEuclideanLin W) := by
    intro w
    set x : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (WithLp.ofLp w ∘ e) with hx
    have hCx : toEuclideanLin (tlsWeighted d (tlsWeights t) A (replicateCol Unit b)) w =
        toEuclideanLin (tlsMatrix d t A b) x := by
      rw [toEuclideanLin_apply, toEuclideanLin_apply, hx, tlsMatrix_mulVec]
      congr 2
      funext j
      simp only [Function.comp_apply, he, Equiv.apply_symm_apply]
    have hnx : ‖w‖ = ‖x‖ := by
      rw [hx, show WithLp.ofLp w ∘ e = WithLp.ofLp w ∘ e.symm.symm from rfl,
        norm_toLp_comp_equiv, WithLp.toLp_ofLp]
    have hspan := hC.norm_toEuclideanLin_eq_iff_mem_span (r := r) (by omega)
      (by simpa using hgap) (by simpa using heq) x
    simp only [Nat.add_sub_cancel] at hspan
    rw [hCx, hnx, hinf, hspan, mem_span_iff_exists_trailingColumns_mulVec, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨WithLp.toLp 2 y, ?_⟩
      rw [toEuclideanLin_apply]
      apply (WithLp.equiv 2 _).injective
      funext i
      have := congrFun hy (e.symm i)
      simp only [hx, Function.comp_apply, Equiv.apply_symm_apply] at this
      exact this
    · rintro ⟨y, hy⟩
      refine ⟨WithLp.ofLp y, ?_⟩
      rw [hx, WithLp.ofLp_toLp, ← hy, toEuclideanLin_apply, WithLp.ofLp_toLp]
      funext j
      change _ = (Vt *ᵥ WithLp.ofLp y) (e.symm (e j))
      rw [Equiv.symm_apply_apply]
  -- the zero pattern of `W Q`
  have hz : ∀ j, j ≠ (⟨n - r, by omega⟩ : Fin (n + 1 - r)) → (W * Q) (Sum.inr ()) j = 0 := by
    intro j hj
    exact hW j (by
      have := j.isLt
      have : (j : ℕ) ≠ n - r := fun h => hj (Fin.ext h)
      omega)
  obtain ⟨ha, hb, hc⟩ := tls_single_rhs (A := A) (b := b) hd ht' hWW hmin hQ hz
  refine ⟨fun y hy => ?_, hb, fun hα => ?_⟩
  · -- (a)
    have hy1 : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (n + 1 - r)))‖ = 1 := by
      have h2 : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (n + 1 - r)))‖ ^ 2 = 1 := by
        rw [← dotProduct_self_eq_norm_sq, hy]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
    have := ha _ hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    exact this
  · -- (c)
    obtain ⟨E, R, hP, hsol, hER⟩ := hc hα
    refine ⟨E, R, hP, ?_, ?_⟩
    · convert hsol using 4
      simp only [tlsWeights, Sum.elim_inl, Sum.elim_inr, RCLike.ofReal_real_eq_id, id_eq]
      rfl
    · rw [hER]
      rfl

/-- The entries of $C = D[A \mid b]T$ are $c_{ij} = d_i a_{ij} t_j$, where $a_{i,n+1} = b_i$. -/
theorem tlsMatrix_apply (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (i : Fin m) (j : Fin (n + 1)) :
    tlsMatrix d t A b i j = d i * Fin.lastCases (b i) (A i) j * t j := by
  rw [tlsMatrix, submatrix_apply, tlsWeighted, mul_diagonal, diagonal_mul]
  refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [finSuccEquivLastSumUnit, tlsWeights]

/-- The start $r$ of the run of values equal to the last one, $\sigma_r = \dots = \sigma_n$
(0-based), found by exact comparisons: $r = n + 1 - \#\{j \le n : \sigma_j = \sigma_n\}$. This
is the index $n - p$ of Algorithm 6.3.1 of [golub2013matrix]. -/
noncomputable def tailStart (σ : ℕ → ℝ) (n : ℕ) : ℕ :=
  open Classical in n + 1 - ((Finset.range (n + 1)).filter fun j => σ j = σ n).card

/-- For a nonincreasing sequence $\sigma$ and $j \le n$, $\sigma_j = \sigma_n$ if and only if $j$ is
at least `GolubVanLoan.Chapter06.tailStart σ n`. -/
private theorem eq_iff_tailStart_le {σ : ℕ → ℝ} (hσ : Antitone σ) {j : ℕ} (hj : j ≤ n) :
    σ j = σ n ↔ tailStart σ n ≤ j := by
  classical
  unfold tailStart
  constructor
  · intro h
    have hsub : Finset.Icc j n ⊆ (Finset.range (n + 1)).filter fun k => σ k = σ n := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, le_antisymm (h ▸ hσ hk.1) (hσ hk.2)⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  · intro h
    by_contra hne
    have hsub : ((Finset.range (n + 1)).filter fun k => σ k = σ n) ⊆ Finset.Ioc j n := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_Ioc]
      refine ⟨?_, by omega⟩
      by_contra hkj
      have h1 : σ j ≤ σ k := hσ (not_lt.1 hkj)
      rw [hk.2] at h1
      exact hne (le_antisymm h1 (hσ hj))
    have := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at this
    omega

/-- For a nonincreasing sequence $\sigma$, the index $r$ = `GolubVanLoan.Chapter06.tailStart σ n`
satisfies $r \le n$, $\sigma_j > \sigma_n$ for all $j < r$, and $\sigma_r = \sigma_n$ (0-based).
This determines the $p$ of Algorithm 6.3.1 of [golub2013matrix]. -/
theorem tailStart_spec {σ : ℕ → ℝ} (hσ : Antitone σ) :
    tailStart σ n ≤ n ∧ (∀ j < tailStart σ n, σ n < σ j) ∧ σ (tailStart σ n) = σ n := by
  have hn := (eq_iff_tailStart_le (n := n) (j := n) hσ le_rfl).1 rfl
  refine ⟨hn, fun j hj => ?_, (eq_iff_tailStart_le hσ hn).2 le_rfl⟩
  refine lt_of_le_of_ne (hσ (by omega)) fun h => ?_
  have := (eq_iff_tailStart_le hσ (by omega)).1 h.symm
  omega

/-- The index list $[n, n - 1, \dots, r]$ in `Fin (n + 1)`: the columns $V(:, r{:}n)$ (0-based) in
reverse order, with the pivot $n$ first. -/
def tailIndices (n r : ℕ) : List (Fin (n + 1)) :=
  (List.finRange (n + 1)).reverse.filter fun j => r ≤ (j : ℕ)

/-- An index $j$ is in `GolubVanLoan.Chapter06.tailIndices n r` if and only if $r \le j$. -/
theorem mem_tailIndices {r : ℕ} {j : Fin (n + 1)} : j ∈ tailIndices n r ↔ r ≤ (j : ℕ) := by
  simp [tailIndices]

/-- The list `GolubVanLoan.Chapter06.tailIndices n r` has no duplicates. -/
theorem tailIndices_nodup (r : ℕ) : (tailIndices n r).Nodup :=
  (List.nodup_reverse.2 (List.nodup_finRange _)).filter _

/-- For $r \le n$, the list `GolubVanLoan.Chapter06.tailIndices n r` is nonempty. -/
theorem tailIndices_ne_nil {r : ℕ} (hr : r ≤ n) : tailIndices n r ≠ [] :=
  List.ne_nil_of_mem (mem_tailIndices.2 (by simpa using hr) : Fin.last n ∈ tailIndices n r)

/-- For $r \le n$, the list `GolubVanLoan.Chapter06.tailIndices n r` is $n$ followed by the indices
$j$ with $r \le j < n$ in decreasing order. -/
private theorem tailIndices_eq_cons {r : ℕ} (hr : r ≤ n) :
    tailIndices n r = Fin.last n ::
      ((List.finRange n).map Fin.castSucc).reverse.filter fun j => r ≤ (j : ℕ) := by
  rw [tailIndices, List.finRange_succ_last, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.filter_cons_of_pos (by simpa using hr)]

/-- For $r \le n$, the first element (the pivot) of `GolubVanLoan.Chapter06.tailIndices n r` is $n$.
-/
theorem tailIndices_head {r : ℕ} (hr : r ≤ n) :
    (tailIndices n r).head (tailIndices_ne_nil hr) = Fin.last n := by
  have key : ∀ (l : List (Fin (n + 1))) (hl : l ≠ []) (t : List (Fin (n + 1))),
      l = Fin.last n :: t → l.head hl = Fin.last n := by
    rintro _ _ _ rfl
    rfl
  exact key _ _ _ (tailIndices_eq_cons hr)

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The program that forms $C = D[A \mid b]T$ entry by entry, as
$c_{ij} = fl(fl(d_i a_{ij})\, t_j)$, where $a_{i,n+1} = b_i$. It is the first step of Algorithm
6.3.1 of [golub2013matrix]. -/
def tlsScale (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : M (Matrix (Fin m) (Fin (n + 1)) ℝ) := do
  let C ← (List.finRange m).foldlM (fun (C : Fin m → Fin (n + 1) → ℝ) i => do
    let row ← (List.finRange (n + 1)).foldlM (fun (row : Fin (n + 1) → ℝ) j => do
      let c ← (do let p ← rnd (d i * Fin.lastCases (b i) (A i) j); rnd (p * t j))
      pure (Function.update row j c)) 0
    pure (Function.update C i row)) 0
  pure (Matrix.of C)

/-- **Algorithm 6.3.1** of [golub2013matrix] (total least squares). Given
$A \in \mathbb{R}^{m \times n}$ with $m > n$, $b \in \mathbb{R}^m$, nonsingular
$D = \operatorname{diag}(d_1, \dots, d_m)$ and nonsingular
$T = \operatorname{diag}(t_1, \dots, t_{n+1})$, the algorithm computes, if possible, a vector
$x_{TLS} \in \mathbb{R}^n$ such that $(A + E_0)\, x_{TLS} = b + r_0$ and
$\|D[E_0 \mid r_0]T\|_F$ is minimal.
```
Compute the SVD Uᵀ(D[A | b]T)V = diag(σ₁, …, σ_{n+1}) and save V.
Determine p such that σ₁ ≥ ⋯ ≥ σ_{n−p} > σ_{n−p+1} = ⋯ = σ_{n+1}.
Compute a Householder P such that if Ṽ = VP, then Ṽ(n+1, n−p+1 : n) = 0.
if ṽ_{n+1,n+1} ≠ 0
    for i = 1:n
        x_i = −t_i ṽ_{i,n+1}/(t_{n+1} ṽ_{n+1,n+1})
    end
    x_TLS = x
end
```
The program forms $D[A \mid b]T$ entry by entry with `GolubVanLoan.Chapter06.tlsScale`, and
calls the parameter `svd` for the SVD. It finds $n - p$ by exact comparisons of the computed
$\sigma$ with `GolubVanLoan.Chapter06.tailStart`. The Householder $P$ is
`GolubVanLoan.Chapter05.houseOn` on the last row of $V$ over the index list
$[n, n - 1, \dots, n - p]$ with the pivot $n$, applied to the columns of $V$ by
`GolubVanLoan.Chapter05.householderApplyRight`. The output is `some x`, or `none` when
$\tilde v_{n+1,n+1} = 0$. -/
noncomputable def algorithm_6_3_1
    (svd : Matrix (Fin m) (Fin (n + 1)) ℝ →
      M (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) :
    M (Option (Fin n → ℝ)) := do
  let C ← tlsScale rnd d t A b
  let S ← svd C
  let o := tailIndices n (tailStart S.2.1 n)
  let vβ ← Chapter05.houseOn rnd o (S.2.2 (Fin.last n))
  let W ← Chapter05.householderApplyRight rnd vβ.1 vβ.2 (List.finRange (n + 1)) o S.2.2
  if W (Fin.last n) (Fin.last n) ≠ 0 then do
    let x ← (List.finRange n).foldlM (fun (x : Fin n → ℝ) i => do
      let q ← (do
        let a ← rnd (t (Fin.castSucc i) * W (Fin.castSucc i) (Fin.last n))
        let c ← rnd (t (Fin.last n) * W (Fin.last n) (Fin.last n))
        rnd (-a / c))
      pure (Function.update x i q)) 0
    pure (some x)
  else pure none

end Programs

/-- In exact arithmetic, a loop that writes each listed entry with a value that does not depend on
the state sets the listed entries to these values and keeps the other entries. -/
private theorem idRun_foldlM_update_const {ι β : Type} [DecidableEq ι] (g : ι → Id β)
    (l : List ι) (hl : l.Nodup) (y₀ : ι → β) (i : ι) :
    Id.run (l.foldlM (fun (y : ι → β) a => do
      let b ← g a; pure (Function.update y a b)) y₀) i =
      if i ∈ l then Id.run (g i) else y₀ i :=
  List.idRun_foldlM_update_apply (fun a _ => g a) l hl y₀ i

/-- In exact arithmetic, a loop that writes each listed entry $a$ with the value $g(a)$ sets the
listed entries to these values and keeps the other entries. -/
private theorem idRun_foldlM_update_pure {ι β : Type} [DecidableEq ι] (g : ι → β)
    (l : List ι) (hl : l.Nodup) (y₀ : ι → β) (i : ι) :
    Id.run (l.foldlM (fun (y : ι → β) a => pure (Function.update y a (g a))) y₀) i =
      if i ∈ l then g i else y₀ i :=
  idRun_foldlM_update_const (fun a => pure (g a)) l hl y₀ i

/-- In exact arithmetic, `GolubVanLoan.Chapter06.tlsScale` returns $C = D[A \mid b]T$. -/
theorem tlsScale_spec (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Id.run (tlsScale pure d t A b) = tlsMatrix d t A b := by
  ext i j
  simp only [tlsScale, Id.run_bind, Id.run_pure, of_apply, pure_bind,
    idRun_foldlM_update_const _ _ (List.nodup_finRange _),
    idRun_foldlM_update_pure _ _ (List.nodup_finRange _), List.mem_finRange, ite_true]
  rw [tlsMatrix_apply]

/-- Let $P = I - \beta v v^T$ be orthogonal with $v_i = 0$ for $i < r$. Then the block of $P$ on the
indices $r, \dots, n$ is orthogonal, and on the columns $r, \dots, n$ the product $VP$ equals
$V(:, r{:}n)$ times that block. -/
private theorem householder_tail {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r : ℕ}
    {v : Fin (n + 1) → ℝ} {β : ℝ} (hv : ∀ i : Fin (n + 1), (i : ℕ) < r → v i = 0)
    (hP : (1 - β • vecMulVec v v) ∈ orthogonalGroup (Fin (n + 1)) ℝ) :
    ((1 - β • vecMulVec v v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))) ∈
      orthogonalGroup (Fin (n + 1 - r)) ℝ ∧
    ∀ i (k : Fin (n + 1 - r)), (V * (1 - β • vecMulVec v v)) i ⟨r + k, by omega⟩ =
      (trailingColumns V r *
        (1 - β • vecMulVec v v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))) i k := by
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1 - β • vecMulVec v v with hPdef
  set f : Fin (n + 1 - r) → Fin (n + 1) := fun k => ⟨r + k, by omega⟩ with hf
  have hfinj : Function.Injective f := fun a b hab =>
    Fin.ext (by simpa [hf] using congrArg Fin.val hab)
  have hoff : ∀ l, l ∉ Set.range f → ∀ k, P l (f k) = 0 := by
    intro l hl k
    have hlr : (l : ℕ) < r := by
      by_contra h
      exact hl ⟨⟨l - r, by omega⟩, Fin.ext (by simp only [hf]; omega)⟩
    have hne : l ≠ f k := fun e => by
      have := congrArg Fin.val e
      simp only [hf] at this
      omega
    rw [hPdef, Matrix.sub_apply, one_apply_ne hne, Matrix.smul_apply, vecMulVec_apply, hv l hlr]
    simp
  have hPP : Pᵀ * P = 1 := by
    exact (mem_orthogonalGroup_iff' _ ℝ).1 hP
  refine ⟨?_, fun i k => ?_⟩
  · rw [mem_orthogonalGroup_iff']
    ext k k'
    have h := congrFun (congrFun hPP (f k)) (f k')
    rw [Matrix.mul_apply] at h
    have e1 : (1 : Matrix (Fin (n + 1 - r)) (Fin (n + 1 - r)) ℝ) k k' =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (f k) (f k') := by
      simp only [Matrix.one_apply, hfinj.eq_iff]
    rw [e1, ← h, Matrix.mul_apply]
    exact Fintype.sum_of_injective f hfinj _ _
      (fun l hl => by rw [transpose_apply, hoff l hl k, zero_mul]) (fun _ => rfl)
  · rw [Matrix.mul_apply, Matrix.mul_apply]
    exact (Fintype.sum_of_injective f hfinj _ _ (fun l hl => by rw [hoff l hl k, mul_zero])
      (fun k' => rfl)).symm

/-- **Algorithm 6.3.1** of [golub2013matrix], exact arithmetic. Let $A \in \mathbb{R}^{m \times n}$
with $m > n$ and $b \in \mathbb{R}^m$, let $d_1, \dots, d_m$ and $t_1, \dots, t_{n+1}$ be
nonzero, and let `svd` return an SVD of every matrix. If the algorithm returns a vector $x$,
then $x$ is a TLS solution of $(A + E_0)x = b + r_0$ with the weights
$D = \operatorname{diag}(d)$ and $T = \operatorname{diag}(t)$. If it returns `none`, then the
TLS problem has no solution.

The run is at `M := Id` with `rnd := pure`. A TLS solution is `Matrix.IsTLSSolution` with the
weights `d` and `GolubVanLoan.Chapter06.tlsWeights t`, for the columns
`Matrix.replicateCol Unit b` and `Matrix.replicateCol Unit x`. -/
theorem algorithm_6_3_1_spec (hmn : n < m)
    (svd : Matrix (Fin m) (Fin (n + 1)) ℝ →
      Id (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (hsvd : ∀ C, IsSVD C (Id.run (svd C)).1 (Id.run (svd C)).2.1 (Id.run (svd C)).2.2)
    {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) {t : Fin (n + 1) → ℝ} (ht : ∀ j, t j ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∀ x, Id.run (algorithm_6_3_1 pure svd A b d t) = some x →
      IsTLSSolution d (tlsWeights t) A (replicateCol Unit b) (replicateCol Unit x)) ∧
    (Id.run (algorithm_6_3_1 pure svd A b d t) = none →
      ¬ ∃ X, IsTLSSolution d (tlsWeights t) A (replicateCol Unit b) X) := by
  have hS := hsvd (tlsMatrix d t A b)
  generalize hSdef : Id.run (svd (tlsMatrix d t A b)) = S at hS
  obtain ⟨hr, hgap, heq⟩ := tailStart_spec (n := n) hS.antitone
  generalize hrdef : tailStart S.2.1 n = r at hr hgap heq
  have ho := tailIndices_nodup (n := n) r
  have hne := tailIndices_ne_nil hr
  obtain ⟨-, hvoff, -, hPorth, hPx⟩ := Chapter05.houseOn_spec ho hne (S.2.2 (Fin.last n))
  generalize hvβ : Id.run (Chapter05.houseOn pure (tailIndices n r) (S.2.2 (Fin.last n))) = vβ
    at hvoff hPorth hPx
  have hW : Id.run (Chapter05.householderApplyRight pure vβ.1 vβ.2 (List.finRange (n + 1))
      (tailIndices n r) S.2.2) = S.2.2 * (1 - vβ.2 • vecMulVec vβ.1 vβ.1) :=
    Chapter05.householderApplyRight_spec_of_forall_mem (List.nodup_finRange _) ho
      List.mem_finRange hvoff _ _
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1 - vβ.2 • vecMulVec vβ.1 vβ.1 with hPdef
  have hrun : Id.run (algorithm_6_3_1 pure svd A b d t) =
      if (S.2.2 * P) (Fin.last n) (Fin.last n) ≠ 0 then
        some (fun i => -(t (Fin.castSucc i) * (S.2.2 * P) (Fin.castSucc i) (Fin.last n)) /
          (t (Fin.last n) * (S.2.2 * P) (Fin.last n) (Fin.last n)))
      else none := by
    simp only [algorithm_6_3_1, Id.run_bind, tlsScale_spec, hSdef, hrdef, hvβ, hW]
    split_ifs with h
    · simp only [Id.run_bind, Id.run_pure]
      congr 1
      funext i
      simp only [pure_bind, idRun_foldlM_update_pure _ _ (List.nodup_finRange n),
        List.mem_finRange, ite_true]
    · rfl
  obtain ⟨hQ, hsub⟩ := householder_tail (V := S.2.2) (r := r)
    (fun i hi => hvoff i (by rw [mem_tailIndices]; omega)) hPorth
  have hPt : Pᵀ = P := transpose_one_sub_smul_vecMulVec _ _
  have hrow : ∀ j, (S.2.2 * P) (Fin.last n) j = (P *ᵥ S.2.2 (Fin.last n)) j := by
    intro j
    conv_rhs => rw [← hPt, mulVec_transpose]
    rfl
  have hWz : ∀ j : Fin (n + 1 - r), (j : ℕ) < n - r →
      (trailingColumns S.2.2 r * P.submatrix
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))) (Fin.last n) j = 0 := by
    intro j hj
    rw [← hsub, hrow, hPx, tailIndices_head hr]
    dsimp only
    rw [ite_eq_right (fun e => by
      have := congrArg Fin.val e; simp at this; omega),
      ite_eq_left (mem_tailIndices.2 (by simp))]
  obtain ⟨-, hb, hc⟩ := tls_single hmn hd ht A b hS hr hgap heq hQ hWz
  have hcol : ∀ i, (trailingColumns S.2.2 r * P.submatrix
      (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))
      (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))) i ⟨n - r, by omega⟩ =
        (S.2.2 * P) i (Fin.last n) := by
    intro i
    rw [← hsub]
    have hfl : ∀ h, (⟨r + (n - r), h⟩ : Fin (n + 1)) = Fin.last n := fun h =>
      Fin.ext (by simp only [Fin.val_last]; omega)
    exact congrArg _ (hfl _)
  rw [hrun]
  split_ifs with h
  · refine ⟨fun x hx => ?_, fun hx => absurd hx (by simp)⟩
    obtain rfl := (Option.some.inj hx).symm
    obtain ⟨E, R, hP', hsol, -⟩ := hc (by rwa [hcol])
    refine ⟨E, R, hP', ?_⟩
    simp only [hPdef] at hcol ⊢
    simpa only [hcol] using hsol
  · refine ⟨fun x hx => absurd hx (by simp), fun _ => hb ?_⟩
    rw [hcol]
    exact not_not.1 h

/-! ### §6.3.3 A geometric interpretation -/

/-- For $x \in \mathbb{R}^n$ and $w \in \mathbb{R}^{n+1}$, the normal $[x; -1]$ satisfies
$[x; -1]^T w = x^T w_{1:n} - w_{n+1}$. -/
private theorem snoc_neg_one_dotProduct (x : Fin n → ℝ) (w : Fin (n + 1) → ℝ) :
    (Fin.snoc x (-1) : Fin (n + 1) → ℝ) ⬝ᵥ w =
      (x ⬝ᵥ fun j => w (Fin.castSucc j)) - w (Fin.last n) := by
  rw [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last, dotProduct]
  simp only [Fin.snoc_castSucc]
  ring

/-- For $x \in \mathbb{R}^n$ and $t \in \mathbb{R}^{n+1}$, $\sum_j ([x; -1]_j / t_j)^2 = \sum_{j \le
n} x_j^2 / t_j^2 + 1 / t_{n+1}^2$. -/
private theorem sum_snoc_neg_one_div_sq (x : Fin n → ℝ) (t : Fin (n + 1) → ℝ) :
    ∑ j, ((Fin.snoc x (-1) : Fin (n + 1) → ℝ) j / t j) ^ 2 =
      ∑ j : Fin n, x j ^ 2 / t (Fin.castSucc j) ^ 2 + 1 / t (Fin.last n) ^ 2 := by
  rw [Fin.sum_univ_castSucc, Fin.snoc_last]
  simp only [Fin.snoc_castSucc, div_pow, neg_one_sq]

/-- **Section 6.3.3** of [golub2013matrix], the geometric interpretation. Let
$t \in \mathbb{R}^{n+1}$ have nonzero entries, $T = \operatorname{diag}(t)$ and
$T_1 = \operatorname{diag}(t_1, \dots, t_n)$, and let $a, x \in \mathbb{R}^n$ and
$\beta \in \mathbb{R}$. Let $P_x = \{[a'; b'] : a' \in \mathbb{R}^n,\ b' \in \mathbb{R},\ b' =
x^T a'\}$, and measure distances in $\mathbb{R}^{n+1}$ by the norm $\|z\| = \|Tz\|_2$. Then the
squared distance from $[a; \beta]$ to $P_x$ is $$\inf_{w \in P_x} \|T([a; \beta] - w)\|_2^2 =
\frac{|a^T x - \beta|^2}{x^T T_1^{-2} x + t_{n+1}^{-2}},$$ and some $w \in P_x$ attains this
value.

For $[a; \beta] = [a_i; b_i]$, the right side is the term $\delta_i$ of the objective $\psi$ of
(6.3.6). -/
theorem tls_distance {t : Fin (n + 1) → ℝ} (ht : ∀ j, t j ≠ 0) (a : Fin n → ℝ) (β : ℝ)
    (x : Fin n → ℝ) :
    (⨅ w : {w : Fin (n + 1) → ℝ // w (Fin.last n) = x ⬝ᵥ fun j => w (Fin.castSucc j)},
        ‖(WithLp.toLp 2 (diagonal t *ᵥ ((Fin.snoc a β : Fin (n + 1) → ℝ) - w.1)) :
          EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) =
      |a ⬝ᵥ x - β| ^ 2 /
        (∑ j : Fin n, x j ^ 2 / t (Fin.castSucc j) ^ 2 + 1 / t (Fin.last n) ^ 2) ∧
    ∃ w : Fin (n + 1) → ℝ, w (Fin.last n) = (x ⬝ᵥ fun j => w (Fin.castSucc j)) ∧
      ‖(WithLp.toLp 2 (diagonal t *ᵥ ((Fin.snoc a β : Fin (n + 1) → ℝ) - w)) :
          EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 =
        |a ⬝ᵥ x - β| ^ 2 /
          (∑ j : Fin n, x j ^ 2 / t (Fin.castSucc j) ^ 2 + 1 / t (Fin.last n) ^ 2) := by
  have hν : (Fin.snoc x (-1) : Fin (n + 1) → ℝ) ≠ 0 := fun h => by
    have := congrFun h (Fin.last n)
    rw [Fin.snoc_last, Pi.zero_apply] at this
    norm_num at this
  have hiff : ∀ w : Fin (n + 1) → ℝ, w (Fin.last n) = (x ⬝ᵥ fun j => w (Fin.castSucc j)) ↔
      (Fin.snoc x (-1) : Fin (n + 1) → ℝ) ⬝ᵥ w = 0 := fun w => by
    rw [snoc_neg_one_dotProduct, sub_eq_zero, eq_comm]
  have hnum : ((Fin.snoc x (-1) : Fin (n + 1) → ℝ) ⬝ᵥ (Fin.snoc a β : Fin (n + 1) → ℝ)) ^ 2 =
      |a ⬝ᵥ x - β| ^ 2 := by
    rw [snoc_neg_one_dotProduct, sq_abs, Fin.snoc_last]
    simp only [Fin.snoc_castSucc]
    rw [dotProduct_comm]
  obtain ⟨h1, w, hw, h2⟩ :=
    iInf_sq_norm_diagonal_mulVec_sub_hyperplane ht hν (Fin.snoc a β : Fin (n + 1) → ℝ)
  rw [hnum, sum_snoc_neg_one_div_sq] at h1 h2
  refine ⟨?_, w, (hiff w).2 hw, h2⟩
  rw [← h1]
  exact Equiv.iInf_congr (Equiv.subtypeEquivRight hiff) fun _ => rfl

end GolubVanLoan.Chapter06
