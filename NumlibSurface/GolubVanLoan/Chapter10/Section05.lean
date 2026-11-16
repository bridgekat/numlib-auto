/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.ImplicitRestart
import Numlib.Krylov.BiLanczos
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub and Van Loan, Section 10.5: Krylov methods for unsymmetric problems

This module formalizes §10.5 of [golub2013matrix], Krylov subspace methods for the eigenvalues of a
large sparse unsymmetric $A \in \mathbb{R}^{n \times n}$. The Arnoldi process (Algorithm 10.5.1)
computes orthonormal vectors $q_1, \dots, q_k$ that span $\mathcal{K}(A, q_1, k)$ and an upper
Hessenberg $H_k$ with
$$A Q_k = Q_k H_k + r_k e_k^T, \qquad Q_k^T r_k = 0,$$
a $k$-step Arnoldi decomposition (10.5.1)–(10.5.2). An eigenpair $(\lambda, y)$ of $H_k$ gives the
Ritz pair $(\lambda, Q_k y)$ of $A$, with backward error $|y_k| \|r_k\|_2$. Restarting applies $p$
shifted QR steps (10.5.4) to $H_c$. By Theorem 10.5.1, the first column of the new basis is a
multiple of $p(A) q_1$ for the filter polynomial $p(\lambda) = (\lambda - \mu_1) \cdots (\lambda -
\mu_p)$, and the truncated decomposition is again an Arnoldi decomposition, so that implicit
restarting does not repeat the Arnoldi steps from step 1.

The module also formalizes the explicitly and the implicitly restarted Arnoldi loops of §10.5.3, the
Krylov–Schur restart of §10.5.4, the unsymmetric Lanczos tridiagonalization (10.5.11)–(10.5.13) with
its termination and breakdown, and the block biorthogonality step (10.5.14)–(10.5.16). The proofs
specialize `Numlib.Krylov.Arnoldi`, `Numlib.Krylov.Decomposition`,
`Numlib.LinearAlgebra.Matrix.KrylovDecomposition`, `Numlib.Eigen.QRAlgorithm`,
`Numlib.Eigen.ImplicitRestart` and `Numlib.Krylov.BiLanczos`.

## Main definitions

* Algorithm 10.5.1, `GolubVanLoan.Chapter10.algorithm_10_5_1`: the Arnoldi process with the modified
  Gram–Schmidt inner loop, as a program with a rounding hook.
* §10.5.1, `GolubVanLoan.Chapter10.IsArnoldiDecomposition`: a $k$-step Arnoldi decomposition
  $A Q_k = Q_k H_k + r_k e_k^T$.
* Equation (10.5.4), `GolubVanLoan.Chapter10.shiftedQrSteps`: $p$ steps of the shifted QR iteration
  on an upper Hessenberg matrix.
* Equation (10.5.10), `GolubVanLoan.Chapter10.explicitlyRestartedArnoldi`: explicitly restarted
  Arnoldi.
* §10.5.3, `GolubVanLoan.Chapter10.implicitlyRestartedArnoldi`: implicitly restarted Arnoldi.
* Equation (10.5.11), `GolubVanLoan.Chapter10.unsymmetricLanczos`: the unsymmetric Lanczos
  tridiagonalization.
* §10.5.5, `GolubVanLoan.Chapter10.IsSeriousBreakdown`: a serious breakdown of the unsymmetric
  Lanczos process.

## Main results

* Algorithm 10.5.1, `GolubVanLoan.Chapter10.algorithm_10_5_1_spec`: in exact arithmetic the
  algorithm computes the Arnoldi vectors and coefficients.
* Equation (10.5.1), `GolubVanLoan.Chapter10.equation_10_5_1`: $\operatorname{span}\{q_1, \dots,
  q_k\} = \operatorname{span}\{q_1, A q_1, \dots, A^{k-1} q_1\}$.
* Equation (10.5.2), `GolubVanLoan.Chapter10.equation_10_5_2`: $A Q_k = Q_k H_k + r_k e_k^T$, an
  Arnoldi decomposition below the grade of $q_1$.
* §10.5.1, `GolubVanLoan.Chapter10.isArnoldiDecomposition_iff`: the source's Arnoldi decomposition
  is `Matrix.IsArnoldiDecomposition`.
* §10.5.1, `GolubVanLoan.Chapter10.arnoldi_ritzPair_backwardError`: an eigenpair of $H_k$ gives a
  Ritz pair of $A$ that is an exact eigenpair of $A + E$ with $\|E\|_2 = |y_k| \|r_k\|_2$.
* Equation (10.5.4), `GolubVanLoan.Chapter10.equation_10_5_4`: in exact arithmetic the shifted QR
  steps form a chain with orthogonal upper Hessenberg $V_i$ and upper triangular $R_i$.
* Equation (10.5.6), `GolubVanLoan.Chapter10.equation_10_5_6`: $V$ is orthogonal and
  $H_+ = V^T H_c V$.
* Theorem 10.5.1, `GolubVanLoan.Chapter10.theorem_10_5_1`:
  $V R = (H_c - \mu_1 I) \cdots (H_c - \mu_p I)$.
* §10.5.3, `GolubVanLoan.Chapter10.filter_firstColumn`: $R(1, 1) V(:, 1) = p(H_c) e_1$.
* Equation (10.5.9), `GolubVanLoan.Chapter10.equation_10_5_9`: $A Q_+ = Q_+ H_+ + r_c e_m^T V$ with
  $Q_+ = Q_c V$.
* §10.5.3, `GolubVanLoan.Chapter10.restart_firstColumn_eq`: the restarted starting vector satisfies
  $R(1, 1) q_+ = p(A) q_1$.
* Equation (10.5.10), `GolubVanLoan.Chapter10.explicitRestartCycle_spec` and
  `GolubVanLoan.Chapter10.equation_10_5_10`: in exact arithmetic each cycle of explicit restarting
  replaces $q_1$ by a unit vector $q_+$ with $R(1, 1) q_+ = p(A) q_1$.
* §10.5.3, `GolubVanLoan.Chapter10.implicitRestart_isArnoldiDecomposition`: the leading $j$ columns
  after $p$ shifted QR steps form a $j$-step Arnoldi decomposition.
* §10.5.3, `GolubVanLoan.Chapter10.implicitRestartCycle_spec` and
  `GolubVanLoan.Chapter10.implicitlyRestartedArnoldi_spec`: in exact arithmetic implicit restarting
  keeps an $m$-step Arnoldi decomposition whose first column is filtered as in explicit restarting.
* §10.5.4, `GolubVanLoan.Chapter10.krylovSchur_isArnoldiDecomposition`: the Krylov–Schur restart
  gives a Krylov decomposition and then an Arnoldi decomposition.
* Equation (10.5.11), `GolubVanLoan.Chapter10.equation_10_5_11`: the computed Lanczos vectors are
  biorthonormal, span Krylov subspaces of $A$ and $A^T$, and $\tilde Q_k^T A Q_k = T_k$.
* Equation (10.5.12), `GolubVanLoan.Chapter10.equation_10_5_12`: $A Q_k = Q_k T_k + r_k e_k^T$.
* Equation (10.5.13), `GolubVanLoan.Chapter10.equation_10_5_13`: $A^T \tilde Q_k = \tilde Q_k
  T_k^T + \tilde r_k e_k^T$.
* §10.5.5, `GolubVanLoan.Chapter10.unsymmetricLanczos_invariant`: if $r_k = 0$ or $\tilde r_k = 0$,
  the process has found an invariant subspace of $A$ or of $A^T$.
* Equation (10.5.16), `GolubVanLoan.Chapter10.equation_10_5_16`: the block step (10.5.14)–(10.5.15)
  gives $\tilde Q_{k+1}^T Q_{k+1} = I_p$.

## Conventions

* As in §10.1 (`GolubVanLoan.Chapter10.Section01`), $A \in \mathbb{R}^{n \times n}$ is
  `A : Matrix (Fin n) (Fin n) ℝ`, it acts on `EuclideanSpace ℝ (Fin n)` through
  `Matrix.toEuclideanLin`, and indices are 0-based.
* The Arnoldi vectors are the Gram–Schmidt orthonormalization of the Krylov sequence
  $q_1, A q_1, A^2 q_1, \dots$; they are $0$ after a breakdown. $Q_k$ is
  `Arnoldi.basisMatrix A q₁ k`, $H_k$ is `Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k`, the
  residual $r_k$ is `(Arnoldi.w (Matrix.toEuclideanLin A) q₁ (k - 1)).ofLp`, and $e_k$ is
  `Krylov.lastVec 1 k`.
* The Krylov subspace $\mathcal{K}(A, q, k) = \operatorname{span}\{q, Aq, \dots, A^{k-1} q\}$ is
  `Krylov.subspace (Matrix.toEuclideanLin A) q k`. The grade of $q$ for $A$ is the dimension of
  $\bigcup_k \mathcal{K}(A, q, k)$, `Krylov.grade`; below the grade the Arnoldi process does not
  break down.
* The source's $k$-step Arnoldi decomposition `GolubVanLoan.Chapter10.IsArnoldiDecomposition` has
  $k$ columns, while the backbone's `Matrix.IsArnoldiDecomposition` with index `k` has $k + 1$
  columns (`GolubVanLoan.Chapter10.isArnoldiDecomposition_iff`). So in the restarting statements the
  source's $m$ and $j$ are `m + 1` and `j + 1`, and $m = j + p$ becomes `j + p + 1`.
* The shifted QR steps (10.5.4) are `Matrix.IsShiftedQrChain Hs V R μ p`: the source's $H^{(i)}$,
  $V_{i+1}$, $R_{i+1}$ and $\mu_{i+1}$ are `Hs i`, `V i`, `R i` and `μ i`, and $V = V_1 \cdots V_p$
  and $R = R_p \cdots R_1$ are list products.

## Implementation notes

* The shifted QR steps (10.5.4), `GolubVanLoan.Chapter10.shiftedQrSteps`, call the Givens QR
  factorization of a Hessenberg matrix of Chapter 5 (Algorithm 5.2.5) and its rotation updates. The
  theorems about shifted QR chains hold for every chain with the properties that the exact run has
  (`GolubVanLoan.Chapter10.equation_10_5_4`).
* Explicit restarting (10.5.10) and the implicitly restarted framework of §10.5.3 run Algorithm
  10.5.1, (10.5.4) and the matrix products of Chapter 1. The implicit framework continues the
  Arnoldi loop body `GolubVanLoan.Chapter10.arnoldiStep` from the truncated decomposition, with the
  residual of `GolubVanLoan.Chapter10.implicitRestart_isArnoldiDecomposition`.
* The filter values of the restart loops are a function `shifts` of $H_c$ that the caller supplies;
  the source leaves their choice to heuristics.
* The unsymmetric Lanczos process (10.5.11) is analysed directly from its recurrences.

## Deviations from the source

* **Equation (10.5.4)** (typo). The source prints the loop as `for i = 0:p`. It runs for
  $i = 1, \dots, p$. See `GolubVanLoan.Chapter10.shiftedQrSteps`.
* **Theorem 10.5.1** (generalization). The source defines $V_i$ and $R_i$ by QR factorizations. The
  identity holds for any matrices that satisfy the two lines of (10.5.4). See
  `GolubVanLoan.Chapter10.theorem_10_5_1`.
* **§10.5.3, the filter in the first column** (generalization). The source writes
  $V(:, 1) = p(H_c) e_1 / R(1, 1)$, which assumes $R(1, 1) \neq 0$. The statement
  $R(1, 1) V(:, 1) = p(H_c) e_1$ holds without this assumption. See
  `GolubVanLoan.Chapter10.filter_firstColumn`.
* **§10.5.3, the restarted starting vector** (generalization). The source writes
  $q_+ = c (A - \mu_1 I) \cdots (A - \mu_p I) q_1$ with $c = 1/R(1, 1)$. The statement
  $R(1, 1) q_+ = p(A) q_1$ holds also when $R(1, 1) = 0$. See
  `GolubVanLoan.Chapter10.restart_firstColumn_eq`.
* **§10.5.3, the truncated Arnoldi decomposition** (correction). The source gives the new residual
  as $v_{mj} r_c$. The residual is $h^+_{j+1,j} q^+_{j+1} + v_{mj} r_c$. See
  `GolubVanLoan.Chapter10.implicitRestart_isArnoldiDecomposition` and
  `GolubVanLoan.Chapter10.implicitlyRestartedArnoldi`.
* **§10.5.4, the Krylov–Schur restart** (typo). The source asks for a Schur decomposition of $A$
  where it means one of $H_m$, and its display has $r_c c_m^T U$ for $r_m e_m^T U$. See
  `GolubVanLoan.Chapter10.krylovSchur_isArnoldiDecomposition`.
* **§10.5.4, the Krylov–Schur restart** (generalization). The source uses a Schur decomposition of
  $H_m$. Only the block upper triangular form of $U^T H_m U$ is needed. See
  `GolubVanLoan.Chapter10.krylovSchur_isArnoldiDecomposition`.

## Not formalized

* **The expansion of the filtered vector in eigenvectors of $A$, (10.5.3).**
* **The exact-shift heuristic** for the filter values.
* **The look-ahead idea of §10.5.6.**
* **Operation counts.**
-/

open scoped Matrix
open Krylov FloatingPoint Polynomial
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

variable {n : ℕ}

/-! ### Arnoldi decompositions (§10.5.1) -/

/-- **Section 10.5.1** of [golub2013matrix], definition of a $k$-step Arnoldi decomposition. Let
$A \in \mathbb{R}^{n \times n}$. Matrices $Q_k \in \mathbb{R}^{n \times k}$ and
$H_k \in \mathbb{R}^{k \times k}$ and a vector $r_k \in \mathbb{R}^n$ form a **$k$-step Arnoldi
decomposition** of $A$ if $Q_k$ has orthonormal columns, $H_k$ is upper Hessenberg,
$Q_k^T r_k = 0$, and
$$A Q_k = Q_k H_k + r_k e_k^T.$$

The vector $e_k$ is `Krylov.lastVec 1 k`, the zero vector when $k = 0$. -/
structure IsArnoldiDecomposition {k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (H : Matrix (Fin k) (Fin k) ℝ) (r : Fin n → ℝ) : Prop where
  /-- The columns of $Q_k$ are orthonormal: $Q_k^T Q_k = I_k$. -/
  transpose_mul_self : Qᵀ * Q = 1
  /-- The matrix $H_k$ is upper Hessenberg. -/
  isUpperHessenberg : H.IsUpperHessenberg
  /-- The residual is orthogonal to the columns of $Q_k$: $Q_k^T r_k = 0$. -/
  transpose_mulVec : Qᵀ *ᵥ r = 0
  /-- The decomposition $A Q_k = Q_k H_k + r_k e_k^T$. -/
  mul_eq : A * Q = Q * H + Matrix.vecMulVec r (Krylov.lastVec (1 : ℝ) k)

/-- **Section 10.5.1** of [golub2013matrix], definition of an Arnoldi decomposition, compared with
the backbone. Let $A \in \mathbb{R}^{n \times n}$, $Q \in \mathbb{R}^{n \times (k+1)}$,
$H \in \mathbb{R}^{(k+1) \times (k+1)}$ and $r \in \mathbb{R}^n$. Then $(Q, H, r)$ is a
$(k+1)$-step Arnoldi decomposition of $A$ in the sense of the source if and only if it is one in
the sense of `Matrix.IsArnoldiDecomposition`.

Over $\mathbb{R}$ the conjugate transpose is the transpose, and $e_{k+1}$ is
`Pi.single (Fin.last k) 1` by `Krylov.lastVec_succ`. -/
theorem isArnoldiDecomposition_iff {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (k + 1)) ℝ} {H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {r : Fin n → ℝ} :
    IsArnoldiDecomposition A Q H r ↔ Matrix.IsArnoldiDecomposition A Q H r := by
  constructor
  · intro h
    exact ⟨⟨by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact h.transpose_mul_self,
      by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact h.transpose_mulVec,
      by rw [h.mul_eq, Krylov.lastVec_succ]⟩, h.isUpperHessenberg⟩
  · intro h
    refine ⟨?_, h.isUpperHessenberg, ?_, ?_⟩
    · rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact h.conjTranspose_mul_self
    · rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact h.conjTranspose_mulVec
    · rw [h.mul_eq, Krylov.lastVec_succ]

/-- **Equation (10.5.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$,
$q_1 \in \mathbb{R}^n$ and $k \ge 0$. The Arnoldi vectors of $A$ from $q_1$ span the Krylov
subspaces:
$$\operatorname{span}\{q_1, \dots, q_k\} = \operatorname{span}\{q_1, A q_1, \dots, A^{k-1}
  q_1\}.$$
That is, $Q_k$ and the Krylov matrix $K(A, q_1, k) = [q_1 | A q_1 | \cdots | A^{k-1} q_1]$ have
the same column space.

The Krylov matrix is `Matrix.krylovMatrix A q₁ k`. The identity holds for every $k$, also past
the grade, where the columns of $Q_k$ are $0$. The proof specializes `Arnoldi.range_basisMatrix`
and `Matrix.range_krylovMatrix`. -/
theorem equation_10_5_1 (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    LinearMap.range (Matrix.toEuclideanLin (Arnoldi.basisMatrix A q₁ k)) =
      LinearMap.range (Matrix.toEuclideanLin (Matrix.krylovMatrix A q₁.ofLp k)) := by
  rw [Arnoldi.range_basisMatrix, Matrix.range_krylovMatrix, WithLp.toLp_ofLp]

/-- **Equation (10.5.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$,
$q_1 \in \mathbb{R}^n$ and $k \ge 1$. After $k$ steps of the Arnoldi process,
$$A Q_k = Q_k H_k + r_k e_k^T,$$
where $H_k$ is upper Hessenberg and $r_k = A q_k - \sum_{i \le k} h_{ik} q_i$ is the residual.
If $k$ is at most the grade of $q_1$ for $A$, then $(Q_k, H_k, r_k)$ is a $k$-step Arnoldi
decomposition.

The proof specializes `Arnoldi.mul_basisMatrix` and
`Arnoldi.isArnoldiDecomposition_basisMatrix`. -/
theorem equation_10_5_2 (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : 1 ≤ k) :
    A * Arnoldi.basisMatrix A q₁ k =
        Arnoldi.basisMatrix A q₁ k * Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k +
          Matrix.vecMulVec (Arnoldi.w (Matrix.toEuclideanLin A) q₁ (k - 1)).ofLp
            (Krylov.lastVec (1 : ℝ) k) ∧
      (Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k).IsUpperHessenberg ∧
      (k ≤ grade (Matrix.toEuclideanLin A) q₁ →
        IsArnoldiDecomposition A (Arnoldi.basisMatrix A q₁ k)
          (Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k)
          (Arnoldi.w (Matrix.toEuclideanLin A) q₁ (k - 1)).ofLp) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨by simpa using Arnoldi.mul_basisMatrix A q₁ k,
    Arnoldi.hessenbergSq_isUpperHessenberg _ q₁ _, fun hg => ?_⟩
  rw [Nat.add_sub_cancel, isArnoldiDecomposition_iff]
  exact Arnoldi.isArnoldiDecomposition_basisMatrix A q₁ hg

/-- Let $A \in \mathbb{R}^{n \times n}$ and $q_1 \in \mathbb{R}^n$, and let $y \in \mathbb{R}^{k+1}$
and $\lambda \in \mathbb{R}$ satisfy $H_{k+1} y = \lambda y$. Then $A (Q_{k+1} y) - \lambda
Q_{k+1} y = y_{k+1} r_{k+1}$, the last entry of $y$ times the residual. -/
theorem arnoldi_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (k : ℕ) {y : Fin (k + 1) → ℝ} {θ : ℝ}
    (hy : (Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ (k + 1)) *ᵥ y = θ • y) :
    Matrix.toEuclideanLin A (WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ (k + 1) *ᵥ y)) -
        θ • WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ (k + 1) *ᵥ y) =
      y (Fin.last k) • Arnoldi.w (Matrix.toEuclideanLin A) q₁ k := by
  rw [toLp_basisMatrix_mulVec, Arnoldi.apply_sub_smul_sum_eq _ q₁ k _ _ hy,
    Arnoldi.coeff_succ_self, Arnoldi.vec_succ_eq]
  rcases eq_or_ne (Arnoldi.w (Matrix.toEuclideanLin A) q₁ k) 0 with h0 | h0
  · simp [h0]
  · have hn : ‖Arnoldi.w (Matrix.toEuclideanLin A) q₁ k‖ ≠ 0 := norm_ne_zero_iff.2 h0
    simp only [RCLike.ofReal_real_eq_id, id, smul_smul]
    congr 1
    field_simp

open scoped Matrix.Norms.L2Operator in
/-- **Section 10.5.1** of [golub2013matrix], Ritz pairs and their backward error. Let
$A \in \mathbb{R}^{n \times n}$ and $q_1 \in \mathbb{R}^n$, and let $1 \le k \le g$, where $g$
is the grade of $q_1$ for $A$. Let $y \in \mathbb{R}^k$ with $\|y\|_2 = 1$ and
$\lambda \in \mathbb{R}$ satisfy $H_k y = \lambda y$, and let $x = Q_k y$ and
$v = (e_k^T y) r_k$. Then:
* $(A - \lambda I) x = v$;
* $(\lambda, x)$ is a Ritz pair of $A$ with respect to $\mathcal{K}(A, q_1, k)$;
* with $E = -v x^T$,
$$(A + E) x = \lambda x, \qquad \|E\|_2 = |y_k| \, \|r_k\|_2.$$

As in the source, only real eigenpairs of $H_k$ are considered. The Ritz pair is
`Krylov.IsRitzPair`, and $\|E\|_2$ is the operator 2-norm. The proof specializes
`Arnoldi.isRitzPair_of_mulVec_eq_smul` and `Arnoldi.apply_sub_smul_sum_eq`. -/
theorem arnoldi_ritzPair_backwardError (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ grade (Matrix.toEuclideanLin A) q₁) {y : EuclideanSpace ℝ (Fin k)} (hy1 : ‖y‖ = 1)
    {θ : ℝ} (hy : (Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k) *ᵥ y.ofLp = θ • y.ofLp) :
    let x := Arnoldi.basisMatrix A q₁ k *ᵥ y.ofLp
    let r := (Arnoldi.w (Matrix.toEuclideanLin A) q₁ (k - 1)).ofLp
    let v := y.ofLp ⟨k - 1, by omega⟩ • r
    A *ᵥ x - θ • x = v ∧
      Krylov.IsRitzPair (Matrix.toEuclideanLin A) (Krylov.subspace (Matrix.toEuclideanLin A) q₁ k)
        θ (WithLp.toLp 2 x) ∧
      (A + -Matrix.vecMulVec v x) *ᵥ x = θ • x ∧
      ‖-Matrix.vecMulVec v x‖ =
        |y.ofLp ⟨k - 1, by omega⟩| * ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖ := by
  intro x r v
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hlast : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by simp)
  have hres := arnoldi_residual_eq A q₁ k hy
  have hx1 : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    change ‖(WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ (k + 1) *ᵥ y.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ = 1
    rw [toLp_basisMatrix_mulVec, Krylov.norm_sum_smul_vec_eq _ q₁ _
      (fun j hj => absurd (lt_of_lt_of_le j.isLt hk) (not_lt.2 hj))]
    exact hy1
  have hxx : x ⬝ᵥ x = 1 := by
    have := real_inner_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
    rw [hx1, one_pow, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
    exact this
  have h1 : A *ᵥ x - θ • x = v := by
    have := congrArg WithLp.ofLp hres
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul] at this
    simp only [v, r, Nat.add_sub_cancel]
    exact this
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [toLp_basisMatrix_mulVec]
    refine Arnoldi.isRitzPair_of_mulVec_eq_smul _ q₁ hk (fun h => ?_) hy
    have : y = 0 := by ext j; simpa using congrFun h j
    rw [this, norm_zero] at hy1
    exact zero_ne_one hy1
  · have hvx : Matrix.vecMulVec v x *ᵥ x = v := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [show ∑ j, x j * x j = x ⬝ᵥ x from rfl, hxx, mul_one]
    rw [Matrix.add_mulVec, Matrix.neg_mulVec, hvx, ← h1]
    abel
  · rw [norm_neg, Matrix.l2_opNorm_vecMulVec, hx1, mul_one]
    simp only [v, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-! ### Implicit restarting (§10.5.2–10.5.3) -/

/-- **Theorem 10.5.1** of [golub2013matrix]. Let $H_c \in \mathbb{R}^{m \times m}$, let
$\mu_1, \dots, \mu_p \in \mathbb{R}$, and let $H^{(0)} = H_c$ and matrices $V_i$, $R_i$,
$H^{(i)}$ satisfy the two lines of (10.5.4),
$$H^{(i-1)} - \mu_i I = V_i R_i, \qquad H^{(i)} = R_i V_i + \mu_i I, \qquad i = 1, \dots, p.$$
Then $V = V_1 \cdots V_p$ and $R = R_p \cdots R_1$ satisfy (10.5.7),
$$V R = (H_c - \mu_1 I) \cdots (H_c - \mu_p I).$$

**Generalization.** The source defines $V_i$ and $R_i$ by QR factorizations. The identity holds
for any factorizations that satisfy the two lines of (10.5.4); neither the orthogonality of
$V_i$ nor the triangularity of $R_i$ is needed.

The chain is `Matrix.IsShiftedQrChain`. The proof specializes
`Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one`, the backbone form of (7.5.7). -/
theorem theorem_10_5_1 {m : ℕ} {Hs V R : ℕ → Matrix (Fin m) (Fin m) ℝ} {μ : ℕ → ℝ} {p : ℕ}
    (h : Matrix.IsShiftedQrChain Hs V R μ p) :
    ((List.range p).map V).prod * ((List.range p).reverse.map R).prod =
      ((List.range p).map fun i => Hs 0 - μ i • 1).prod :=
  Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one h

/-- **Equation (10.5.6)** of [golub2013matrix]. Let $H^{(i)}$, $V_i$, $R_i$ satisfy (10.5.4) for
$i = 1, \dots, p$, with every $V_i$ orthogonal. Then $V = V_1 \cdots V_p$ of (10.5.5) is
orthogonal and
$$H_+ = H^{(p)} = V^T H_c V.$$

The proof specializes `Matrix.IsShiftedQrChain.conjTranspose_mul_mul`. -/
theorem equation_10_5_6 {m : ℕ} {Hs V R : ℕ → Matrix (Fin m) (Fin m) ℝ} {μ : ℕ → ℝ} {p : ℕ}
    (h : Matrix.IsShiftedQrChain Hs V R μ p)
    (hV : ∀ i < p, V i ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    ((List.range p).map V).prod ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧
      Hs p = (((List.range p).map V).prod)ᵀ * Hs 0 * ((List.range p).map V).prod := by
  obtain ⟨h1, h2⟩ := h.conjTranspose_mul_mul hV
  refine ⟨h1, ?_⟩
  rw [h2, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- A product of upper triangular matrices is upper triangular. -/
private theorem isUpperTriangular_list_prod {m : ℕ} {R : ℕ → Matrix (Fin m) (Fin m) ℝ}
    (l : List ℕ) (hR : ∀ i ∈ l, (R i).IsUpperTriangular) :
    ((l.map R).prod).IsUpperTriangular := by
  induction l with
  | nil => simpa using Matrix.blockTriangular_one
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (hR a List.mem_cons_self).mul (ih fun i hi => hR i (List.mem_cons_of_mem a hi))

/-- The filter polynomial $p(\lambda) = (\lambda - \mu_1) \cdots (\lambda - \mu_p)$ of (10.5.3),
where the source's $\mu_1, \dots, \mu_p$ are `μ 0, …, μ (p - 1)`. -/
noncomputable def filterPolynomial (μ : ℕ → ℝ) (p : ℕ) : ℝ[X] :=
  ((List.range p).map fun i => X - C (μ i)).prod

/-- For a square matrix $M$, the filter polynomial satisfies
$p(M) = (M - \mu_1 I) \cdots (M - \mu_p I)$. -/
theorem aeval_filterPolynomial {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (μ : ℕ → ℝ) (p : ℕ) :
    aeval M (filterPolynomial μ p) = ((List.range p).map fun i => M - μ i • 1).prod := by
  rw [filterPolynomial, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp [Algebra.algebraMap_eq_smul_one]

/-- **Section 10.5.3** of [golub2013matrix], the filter in the first column. Let $H^{(i)}$, $V_i$,
$R_i$ be $(m+1) \times (m+1)$ matrices that satisfy (10.5.4) for $i = 1, \dots, p$, with every
$R_i$ upper triangular, and let $p$ be the filter polynomial. Then $R = R_p \cdots R_1$ is upper
triangular, and
$$R(1, 1) \, V(:, 1) = p(H_c) e_1.$$

**Generalization.** The source writes $V(:, 1) = p(H_c) e_1 / R(1, 1)$, that is $c = 1/R(1, 1)$,
which assumes $R(1, 1) \neq 0$. The statement without the division holds without this
assumption.

The orthogonality of $V_i$ is not needed. The proof specializes
`Matrix.IsShiftedQrChain.mulVec_first`. -/
theorem filter_firstColumn {m : ℕ} {Hs V R : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {μ : ℕ → ℝ} {p : ℕ} (h : Matrix.IsShiftedQrChain Hs V R μ p)
    (hR : ∀ i < p, (R i).IsUpperTriangular) :
    (((List.range p).reverse.map R).prod).IsUpperTriangular ∧
      ((List.range p).reverse.map R).prod 0 0 • (((List.range p).map V).prod *ᵥ Pi.single 0 1) =
        aeval (Hs 0) (filterPolynomial μ p) *ᵥ Pi.single 0 1 :=
  ⟨isUpperTriangular_list_prod _ fun i hi => hR i (List.mem_range.1 (List.mem_reverse.1 hi)),
    by rw [aeval_filterPolynomial]; exact (h.mulVec_first hR).symm⟩

/-- **Equation (10.5.9)** of [golub2013matrix]. Let $A Q_c = Q_c H_c + r_c e_m^T$ (10.5.8) be an
$m$-step Arnoldi decomposition of $A \in \mathbb{R}^{n \times n}$, and apply (10.5.4) to $H_c$
with orthogonal $V_i$. Then $Q_+ = Q_c V$ has orthonormal columns, and
$$A Q_+ = Q_+ H_+ + r_c e_m^T V.$$

The source's $m$ is `m + 1` here. The proof specializes
`Matrix.IsKrylovDecomposition.mul_of_conjTranspose_mul_self`. -/
theorem equation_10_5_9 {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (m + 1)) ℝ} {H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {r : Fin n → ℝ} (hQ : IsArnoldiDecomposition A Q H r)
    {Hs V R : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {μ : ℕ → ℝ} {p : ℕ}
    (h : Matrix.IsShiftedQrChain Hs V R μ p) (h0 : Hs 0 = H)
    (hV : ∀ i < p, V i ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ) :
    A * (Q * ((List.range p).map V).prod) =
        (Q * ((List.range p).map V).prod) * Hs p +
          Matrix.vecMulVec r (Krylov.lastVec (1 : ℝ) (m + 1) ᵥ* ((List.range p).map V).prod) ∧
      (Q * ((List.range p).map V).prod)ᵀ * (Q * ((List.range p).map V).prod) = 1 := by
  obtain ⟨hmem, hconj⟩ := equation_10_5_6 h hV
  have hU : (((List.range p).map V).prod)ᴴ * ((List.range p).map V).prod = 1 := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.mem_orthogonalGroup_iff' _ _).1 hmem
  have hK := Matrix.IsKrylovDecomposition.mul_of_conjTranspose_mul_self
    (isArnoldiDecomposition_iff.1 hQ).toIsKrylovDecomposition hU
  have e1 := hK.mul_eq
  have e2 := hK.conjTranspose_mul_self
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← h0, ← hconj, ← Krylov.lastVec_succ] at e1
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at e2
  exact ⟨e1, e2⟩

/-- **Section 10.5.3** of [golub2013matrix], the restarted starting vector. Let $(Q_c, H_c, r_c)$ be
an $m$-step Arnoldi decomposition of $A \in \mathbb{R}^{n \times n}$ with $m = j + p$, and let
$q_1 = Q_c e_1$. If $m \ge 2$, then for every $\mu \in \mathbb{R}$
$$(A - \mu I) q_1 = Q_c (H_c - \mu I) e_1.$$
If (10.5.4) is applied to $H_c$ with upper triangular $R_i$, then
$q_+ = Q_+(:, 1) = Q_c V(:, 1)$ satisfies
$$R(1, 1) \, q_+ = p(A) q_1,$$
where $p$ is the filter polynomial.

**Generalization.** The source writes $q_+ = c (A - \mu_1 I) \cdots (A - \mu_p I) q_1$ with
$c = 1/R(1, 1)$, which assumes $R(1, 1) \neq 0$. The statement without the division holds
without this assumption.

The source's $m$ is `j + p + 1` here, so $p < m$. The second statement does not need the
orthogonality of $V_i$. The proof specializes `Matrix.IsArnoldiDecomposition.aeval_mulVec_first`
and `Matrix.IsArnoldiDecomposition.implicitRestart_first`. -/
theorem restart_firstColumn_eq {j p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (j + p + 1)) ℝ} {H : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ}
    {r : Fin n → ℝ} (hQ : IsArnoldiDecomposition A Q H r) :
    (0 < j + p → ∀ μ : ℝ, (A - μ • 1) *ᵥ (Q *ᵥ Pi.single 0 1) =
        Q *ᵥ ((H - μ • 1) *ᵥ Pi.single 0 1)) ∧
      ∀ {Hs V R : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ} {μ : ℕ → ℝ},
        Matrix.IsShiftedQrChain Hs V R μ p → Hs 0 = H → (∀ i < p, (R i).IsUpperTriangular) →
        ((List.range p).reverse.map R).prod 0 0 •
            ((Q * ((List.range p).map V).prod) *ᵥ Pi.single 0 1) =
          aeval A (filterPolynomial μ p) *ᵥ (Q *ᵥ Pi.single 0 1) := by
  have hQ' := isArnoldiDecomposition_iff.1 hQ
  refine ⟨fun hjp μ => ?_, fun hc h0 hR => (hQ'.implicitRestart_first hc h0 hR).symm⟩
  have h := hQ'.aeval_mulVec_first (p := X - C μ) (by
    rw [natDegree_X_sub_C]; omega)
  simpa [Algebra.algebraMap_eq_smul_one] using h

/-- **Section 10.5.3** of [golub2013matrix], the truncated Arnoldi decomposition of implicit
restarting. Let $(Q_c, H_c, r_c)$ be an $m$-step Arnoldi decomposition of
$A \in \mathbb{R}^{n \times n}$, let $p \ge 1$ and $j = m - p \ge 1$, and apply (10.5.4) to
$H_c$ with orthogonal upper Hessenberg $V_i$ and upper triangular $R_i$, as the Givens QR
factorization gives. Then $V = V_1 \cdots V_p$ has lower bandwidth $p$, so that
$V(m, 1:j-1) = 0$. With $Q_+ = Q_c V$ and $H_+ = H^{(p)}$, the leading $j$ columns form a
$j$-step Arnoldi decomposition
$$A Q_+(:, 1:j) = Q_+(:, 1:j) H_+(1:j, 1:j) + r_+ e_j^T, \qquad r_+ = h^+_{j+1,j} Q_+(:, j+1) +
  v_{mj} r_c.$$

**Correction.** The source gives the new residual as $v_{mj} r_c$, also in the loop step
"Replace $r_c$ with $v_{mj} r_c$". This drops the Hessenberg term $h^+_{j+1,j} q^+_{j+1}$, which
the formulation of implicit restarting by Sorensen (1992) has.

The source's $m$ and $j$ are `j + p + 1` and `j + 1` here. The proof specializes
`Matrix.IsArnoldiDecomposition.implicitRestart`. -/
theorem implicitRestart_isArnoldiDecomposition {j p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (j + p + 1)) ℝ} {H : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ}
    {r : Fin n → ℝ} (hQ : IsArnoldiDecomposition A Q H r)
    {Hs V R : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ} {μ : ℕ → ℝ}
    (hc : Matrix.IsShiftedQrChain Hs V R μ p) (h0 : Hs 0 = H)
    (hV : ∀ i < p, V i ∈ Matrix.orthogonalGroup (Fin (j + p + 1)) ℝ)
    (hVH : ∀ i < p, (V i).IsUpperHessenberg) (hR : ∀ i < p, (R i).IsUpperTriangular)
    (hp : 0 < p) :
    (((List.range p).map V).prod).HasLowerBandwidth p ∧
      IsArnoldiDecomposition A
        ((Q * ((List.range p).map V).prod).submatrix id
          (Fin.castLE (by omega : j + 1 ≤ j + p + 1)))
        ((Hs p).submatrix (Fin.castLE (by omega : j + 1 ≤ j + p + 1))
          (Fin.castLE (by omega : j + 1 ≤ j + p + 1)))
        (Hs p ⟨j + 1, by omega⟩ ⟨j, by omega⟩ •
            (Q * ((List.range p).map V).prod).col ⟨j + 1, by omega⟩ +
          ((List.range p).map V).prod (Fin.last (j + p)) ⟨j, by omega⟩ • r) :=
  ⟨Matrix.IsShiftedQrChain.hasLowerBandwidth_prod hVH, isArnoldiDecomposition_iff.2
    ((isArnoldiDecomposition_iff.1 hQ).implicitRestart hc h0 hV hVH hR hp)⟩

/-- **Section 10.5.4** of [golub2013matrix], the Krylov–Schur restart. Let $(Q_m, H_m, r_m)$ be an
$m$-step Arnoldi decomposition of $A \in \mathbb{R}^{n \times n}$, let $1 \le j \le m$, and let
$U \in \mathbb{R}^{m \times m}$ be orthogonal with
$$U^T H_m U = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}, \qquad T_{11} \in
  \mathbb{R}^{j \times j}.$$
Let $Q_+ = Q_m U$ and $u^T = U(m, 1:j)$. Then:
* (a) $A Q_+(:, 1:j) = Q_+(:, 1:j) T_{11} + r_m u^T$ is a Krylov decomposition: $Q_+(:, 1:j)$
  has orthonormal columns and $r_m$ is orthogonal to them;
* (b) there are an orthogonal $Z \in \mathbb{R}^{j \times j}$ and $\tau \in \mathbb{R}$ such
  that
$$A (Q_+(:, 1:j) Z) = (Q_+(:, 1:j) Z)(Z^T T_{11} Z) + \tau r_m e_j^T$$
is a $j$-step Arnoldi decomposition.

**Typo.** The source asks for a Schur decomposition of $A$ where it means one of $H_m$, and its
display has $r_c c_m^T U$ for $r_m e_m^T U$.

**Generalization.** The source uses a Schur decomposition of $H_m$. Only the block upper
triangular form of $U^T H_m U$ is needed.

The source's $m$ and $j$ are `k + 1` and `j + 1` here. The Krylov decomposition is
`Matrix.IsKrylovDecomposition`. The matrix $Z$, with $Z^T T_{11} Z$ upper Hessenberg and
$Z^T u = \tau e_j$, comes from Problem P10.5.2 (`Matrix.exists_isUpperHessenberg_conj_lastCol`).
The proof specializes `Matrix.IsArnoldiDecomposition.krylovSchur`. -/
theorem krylovSchur_isArnoldiDecomposition {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (k + 1)) ℝ} {H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {r : Fin n → ℝ} (hQ : IsArnoldiDecomposition A Q H r)
    {U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hU : U ∈ Matrix.orthogonalGroup (Fin (k + 1)) ℝ)
    (j : Fin (k + 1)) (hT : ∀ i l : Fin (k + 1), l ≤ j → j < i → (Uᵀ * H * U) i l = 0) :
    Matrix.IsKrylovDecomposition A ((Q * U).submatrix id (Fin.castLE j.isLt))
        ((Uᵀ * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt)) r
        (fun l => U (Fin.last k) (Fin.castLE j.isLt l)) ∧
      ∃ Z ∈ Matrix.orthogonalGroup (Fin (j + 1)) ℝ, ∃ τ : ℝ,
        IsArnoldiDecomposition A ((Q * U).submatrix id (Fin.castLE j.isLt) * Z)
          (Zᵀ * (Uᵀ * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt) * Z) (τ • r) := by
  have hUs : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hks := (isArnoldiDecomposition_iff.1 hQ).krylovSchur hU j (by rw [hUs]; exact hT)
  rw [hUs] at hks
  refine ⟨hks.1, ?_⟩
  obtain ⟨Z, hZ, hZH, τ, hZu⟩ := Matrix.exists_isUpperHessenberg_conj_lastCol
    ((Uᵀ * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt))
    (star fun l => U (Fin.last k) (Fin.castLE j.isLt l))
  have hZs : star Z = Zᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have h := hks.2 Z hZ τ hZH hZu
  rw [hZs, star_trivial] at h
  exact ⟨Z, hZ, τ, isArnoldiDecomposition_iff.2 h⟩

/-! ### Block biorthogonality (§10.5.6) -/

/-- **Equation (10.5.16)** of [golub2013matrix], with (10.5.15), the block step of (10.5.14). Let
$R_k, S_k \in \mathbb{R}^{n \times p}$ with $S_k^T R_k$ nonsingular, and let
$B_k, C_k \in \mathbb{R}^{p \times p}$ satisfy $C_k^T B_k = S_k^T R_k$. Then $B_k$ and $C_k$ are
nonsingular, and $Q_{k+1} = R_k B_k^{-1}$ and $\tilde Q_{k+1} = S_k C_k^{-1}$ satisfy
$$\tilde Q_{k+1}^T Q_{k+1} = I_p.$$

The identity is $C_k^{-T} (S_k^T R_k) B_k^{-1} = I_p$. -/
theorem equation_10_5_16 {p : ℕ} {Rk Sk : Matrix (Fin n) (Fin p) ℝ}
    {B C : Matrix (Fin p) (Fin p) ℝ} (hSR : IsUnit (Skᵀ * Rk)) (hCB : Cᵀ * B = Skᵀ * Rk) :
    IsUnit B ∧ IsUnit C ∧ (Sk * C⁻¹)ᵀ * (Rk * B⁻¹) = 1 := by
  rw [← hCB, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, IsUnit.mul_iff] at hSR
  have hB : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 hSR.2
  have hC : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_transpose]
    exact hSR.1
  refine ⟨hB, hC, ?_⟩
  have hCt : IsUnit Cᵀ.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det C).1 hC
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.mul_assoc, ← Matrix.mul_assoc Skᵀ,
    ← hCB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCt, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det B).1 hB)]

/-! ### Algorithm 10.5.1 (the Arnoldi process) -/

/-- The state of Algorithm 10.5.1: the number $k$ of Arnoldi vectors computed, the vectors, the
Hessenberg entries, the current residual $r_k$, and a flag that records that the loop
"while $h_{k+1,k} \neq 0$" has stopped. -/
structure ArnoldiState (n : ℕ) where
  /-- The step counter $k$ of the source. -/
  k : ℕ
  /-- The Arnoldi vectors: `q j` is the source's $q_{j+1}$. -/
  q : ℕ → Fin n → ℝ
  /-- The Hessenberg entries: `h i j` is the source's $h_{i+1,j+1}$. -/
  h : ℕ → ℕ → ℝ
  /-- The current residual $r_k$. -/
  r : Fin n → ℝ
  /-- Whether the loop has stopped because $h_{k+1,k} = 0$. -/
  done : Bool

section ArnoldiProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The modified Gram–Schmidt inner loop of Algorithm 10.5.1: for $i = 1, \dots, k$ it computes
$h_{ik} = q_i^T r_k$ and then $r_k \leftarrow r_k - h_{ik} q_i$, so that each coefficient is
taken against the current $r_k$. It returns the orthogonalized vector and the column of
coefficients. -/
def mgsLoop (q : ℕ → Fin n → ℝ) (k : ℕ) (r : Fin n → ℝ) : M ((Fin n → ℝ) × (ℕ → ℝ)) :=
  (List.range k).foldlM (fun (p : (Fin n → ℝ) × (ℕ → ℝ)) i => do
    let c ← algorithm_1_1_1 rnd (q i) p.1
    let v ← algorithm_1_1_2 rnd (-c) (q i) p.1
    pure (v, Function.update p.2 i c)) (r, fun _ => 0)

/-- One pass of the `while` loop of Algorithm 10.5.1, which does nothing once the loop has stopped:
```
q_{k+1} = r_k/h_{k+1,k},  k = k + 1,  r_k = A q_k
for i = 1:k: h_{ik} = q_iᵀ r_k, r_k = r_k − h_{ik} q_i
h_{k+1,k} = ‖r_k‖₂
```
with $h_{10} = 1$ at the first pass. -/
noncomputable def arnoldiStep (A : Matrix (Fin n) (Fin n) ℝ) (s : ArnoldiState n) :
    M (ArnoldiState n) :=
  if s.done then pure s else do
    let hk : ℝ := if s.k = 0 then 1 else s.h s.k (s.k - 1)
    let qk ← vecDiv rnd s.r hk
    let q := Function.update s.q s.k qk
    let v ← algorithm_1_1_3 rnd A qk 0
    let vh ← mgsLoop rnd q (s.k + 1) v
    let b ← vecNorm rnd vh.1
    pure
      { k := s.k + 1
        q := q
        h := fun i j => if j = s.k then (if i = s.k + 1 then b else vh.2 i) else s.h i j
        r := vh.1
        done := decide (b = 0) }

/-- **Algorithm 10.5.1** of [golub2013matrix] (Arnoldi process). If $A \in \mathbb{R}^{n \times n}$
and $q_1 \in \mathbb{R}^n$ has unit 2-norm, the algorithm computes a matrix $Q_t = [q_1 |
\cdots | q_t] \in \mathbb{R}^{n \times t}$ with orthonormal columns and an upper Hessenberg
matrix $H_t = (h_{ij}) \in \mathbb{R}^{t \times t}$ with $A Q_t = Q_t H_t$:
```
k = 0, r_0 = q₁, h_{10} = 1
while h_{k+1,k} ≠ 0
  q_{k+1} = r_k/h_{k+1,k},  k = k + 1,  r_k = A q_k
  for i = 1:k: h_{ik} = q_iᵀ r_k, r_k = r_k − h_{ik} q_i end
  h_{k+1,k} = ‖r_k‖₂
end
t = k
```

The `while` loop is at most `fuel` passes of `GolubVanLoan.Chapter10.arnoldiStep`, and every
arithmetic result passes through the rounding hook `rnd`. The exact semantics is
`GolubVanLoan.Chapter10.algorithm_10_5_1_spec`. -/
noncomputable def algorithm_10_5_1 (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (fuel : ℕ) :
    M (ArnoldiState n) :=
  (List.range fuel).foldlM (fun s _ => arnoldiStep rnd A s)
    { k := 0, q := fun _ => 0, h := fun _ _ => 0, r := q₁, done := false }

end ArnoldiProgram

/-- In exact arithmetic, if the first $m$ vectors are Arnoldi vectors of $A$, the modified
Gram–Schmidt loop of $m$ steps from $A q_{k+1}$ returns the modified Gram–Schmidt sweep and,
below $m$, the Arnoldi coefficients $h_{i+1,k+1}$. -/
private theorem mgsLoop_id (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (q : ℕ → Fin n → ℝ) (k m : ℕ)
    (hq : ∀ i < m, q i = (Arnoldi.vec (Matrix.toEuclideanLin A) q₁ i).ofLp) :
    Id.run (mgsLoop pure q m (A *ᵥ (Arnoldi.vec (Matrix.toEuclideanLin A) q₁ k).ofLp)) =
      ((InnerProductSpace.modifiedGramSchmidtSweep ℝ (Arnoldi.vec (Matrix.toEuclideanLin A) q₁)
          (Matrix.toEuclideanLin A (Arnoldi.vec (Matrix.toEuclideanLin A) q₁ k)) m).ofLp,
        fun i => if i < m then Arnoldi.coeff (Matrix.toEuclideanLin A) q₁ i k else 0) := by
  set T := Matrix.toEuclideanLin A
  induction m with
  | zero => rfl
  | succ m ih =>
    have ih' := ih fun i hi => hq i (by omega)
    simp only [mgsLoop, List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      Id.run_bind] at ih' ⊢
    rw [ih']
    simp only [Id.run_pure, algorithm_1_1_1_spec, algorithm_1_1_2_spec, hq m (by omega)]
    have hc : (Arnoldi.vec T q₁ m).ofLp ⬝ᵥ
        (InnerProductSpace.modifiedGramSchmidtSweep ℝ (Arnoldi.vec T q₁) (T (Arnoldi.vec T q₁ k))
          m).ofLp = Arnoldi.coeff T q₁ m k := by
      rw [Arnoldi.coeff_eq_inner_modifiedGramSchmidtSweep, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial, dotProduct_comm]
    rw [hc]
    refine Prod.ext ?_ (funext fun i => ?_)
    · simp only [InnerProductSpace.modifiedGramSchmidtSweep_succ, WithLp.ofLp_sub,
        WithLp.ofLp_smul]
      rw [← hc, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
      simp [sub_eq_add_neg]
    · by_cases him : i = m
      · subst him; simp
      · simp only [Function.update_of_ne him]
        by_cases hi : i < m
        · rw [ite_eq_left hi, ite_eq_left (by omega)]
        · rw [ite_eq_right hi, ite_eq_right (by omega)]

/-- The exact run with $t + 1$ passes is one pass of `GolubVanLoan.Chapter10.arnoldiStep` after the
exact run with $t$ passes. -/
private theorem algorithm_10_5_1_succ (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (t : ℕ) :
    Id.run (algorithm_10_5_1 pure A q₁ (t + 1)) =
      Id.run (arnoldiStep pure A (Id.run (algorithm_10_5_1 pure A q₁ t))) := by
  simp only [algorithm_10_5_1, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Algorithm 10.5.1** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$,
let $q_1 \in \mathbb{R}^n$ be a unit vector, and let $g$ be the grade of $q_1$ for $A$. In exact
arithmetic, the run with at most `fuel` passes ends with $t = k = \min(\mathrm{fuel}, g)$. For
$j = 1, \dots, t$ the computed $q_j$ is the $j$-th Arnoldi vector of $A$ from $q_1$, and the
computed $h_{ij}$ is the Arnoldi coefficient for $i \le j + 1$. If $t \ge 1$, the last residual
$r_t$ is the residual of the Arnoldi process.

The Arnoldi vectors, coefficients and residuals are `Arnoldi.vec`, `Arnoldi.coeff` and
`Arnoldi.w`, 0-based. The inner loop is `InnerProductSpace.modifiedGramSchmidtSweep`, whose
coefficients against the orthonormal $q_i$ are the classical ones
(`Arnoldi.coeff_eq_inner_modifiedGramSchmidtSweep`). The normalization is `Arnoldi.vec_succ_eq`
with $h_{k+1,k} = \|r_k\|_2$ (`Arnoldi.coeff_succ_self`), and the exit test is
`Arnoldi.coeff_succ_self_eq_zero_iff`. The orthonormality of the $q_j$ (Problem P10.5.1) is
`Arnoldi.orthonormal`. -/
theorem algorithm_10_5_1_spec (A : Matrix (Fin n) (Fin n) ℝ) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) (fuel : ℕ) :
    let s := Id.run (algorithm_10_5_1 pure A q₁ fuel)
    let T := Matrix.toEuclideanLin A
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q₁
    s.k = min fuel (grade T q) ∧
      (∀ j < s.k, s.q j = (Arnoldi.vec T q j).ofLp ∧
        ∀ i ≤ j + 1, s.h i j = Arnoldi.coeff T q i j) ∧
      (0 < s.k → s.r = (Arnoldi.w T q (s.k - 1)).ofLp) := by
  intro s T q
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : ‖q‖ = 1 := hq
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hg : 0 < grade T q := Krylov.grade_pos_of_ne_zero _ _ hq0
  let P : ℕ → ArnoldiState n → Prop := fun t s =>
    s.k = min t (grade T q) ∧ s.done = decide (grade T q ≤ s.k) ∧
      (∀ j < s.k, s.q j = (Arnoldi.vec T q j).ofLp ∧
        ∀ i ≤ j + 1, s.h i j = Arnoldi.coeff T q i j) ∧
      s.r = if s.k = 0 then q₁ else (Arnoldi.w T q (s.k - 1)).ofLp
  have hP : ∀ t, P t (Id.run (algorithm_10_5_1 pure A q₁ t)) := by
    intro t
    induction t with
    | zero =>
      refine ⟨by simp [algorithm_10_5_1], ?_, fun j hj => ?_, by simp [algorithm_10_5_1]⟩
      · simp [algorithm_10_5_1, hg.ne']
      · simp [algorithm_10_5_1] at hj
    | succ t ih =>
      rw [algorithm_10_5_1_succ]
      set s := Id.run (algorithm_10_5_1 pure A q₁ t)
      obtain ⟨hk, hdone, hvec, hr⟩ := ih
      cases hsd : s.done with
      | true =>
        have hle : grade T q ≤ s.k := by simpa [hsd] using hdone.symm
        simp only [arnoldiStep, hsd, ↓reduceIte, Id.run_pure]
        refine ⟨?_, hdone, hvec, hr⟩
        rw [hk] at hle ⊢
        omega
      | false =>
        have hlt : s.k < grade T q := by
          have : ¬ grade T q ≤ s.k := by simpa [hsd] using hdone.symm
          omega
        -- the new Arnoldi vector
        have hqk : (if s.k = 0 then 1 else s.h s.k (s.k - 1))⁻¹ • s.r =
            (Arnoldi.vec T q s.k).ofLp := by
          rcases Nat.eq_zero_or_pos s.k with h0 | hpos
          · simp only [hr, h0, ↓reduceIte]
            rw [Arnoldi.vec_zero T q hq0, show ‖q‖ = 1 from hq]
            simp [q]
          · obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
            simp only [hr, hj, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
              Nat.add_sub_cancel]
            rw [((hvec j (by omega)).2 (j + 1) le_rfl), Arnoldi.coeff_succ_self,
              Arnoldi.vec_succ_eq]
            simp
        have hqs : ∀ i < s.k + 1, Function.update s.q s.k (Arnoldi.vec T q s.k).ofLp i =
            (Arnoldi.vec T q i).ofLp := fun i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [Function.update_of_ne hi.ne]; exact (hvec i hi).1
          · simp
        simp only [P, arnoldiStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          Id.run_pure, vecDiv_spec, algorithm_1_1_3_spec, zero_add, vecNorm_spec]
        rw [hqk, mgsLoop_id A q _ s.k (s.k + 1) hqs]
        have hsweep : InnerProductSpace.modifiedGramSchmidtSweep ℝ (Arnoldi.vec T q)
            (T (Arnoldi.vec T q s.k)) (s.k + 1) = Arnoldi.w T q s.k := by
          rw [InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum ℝ
            (fun _ _ h => Arnoldi.inner_vec_eq_zero T q h), Arnoldi.w]
          rfl
        rw [hsweep, WithLp.toLp_ofLp]
        refine ⟨by omega, ?_, fun j hj => ⟨hqs j hj, fun i hi => ?_⟩, by simp⟩
        · have h0 := Arnoldi.coeff_succ_self_eq_zero_iff T q s.k
          rw [Arnoldi.coeff_succ_self] at h0
          simp only [RCLike.ofReal_real_eq_id, id] at h0
          simp only [h0]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · simp only [ite_eq_right hj.ne]
            exact (hvec j hj).2 i hi
          · simp only [↓reduceIte]
            by_cases hik : i = s.k + 1
            · subst hik
              simp only [↓reduceIte]
              rw [Arnoldi.coeff_succ_self]
              rfl
            · rw [ite_eq_right hik, ite_eq_left (by omega)]
  obtain ⟨hk, -, hvec, hr⟩ := hP fuel
  have hr' : s.r = if s.k = 0 then q₁ else (Arnoldi.w T q (s.k - 1)).ofLp := hr
  refine ⟨hk, hvec, fun hpos => ?_⟩
  simp only [hr', hpos.ne', ↓reduceIte]

/-! ### The shifted QR steps (10.5.4) -/

section ShiftedQrProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One row of $B + \mu I$: the diagonal entry $x_r$ is replaced by $\mathrm{fl}(x_r + \mu)$, and
the other entries are copied. -/
def shiftDiagRow {m : ℕ} (μ : ℝ) (r : Fin m) (x : Fin m → ℝ) : M (Fin m → ℝ) := do
  let d ← rnd (x r + μ)
  pure (Function.update x r d)

/-- The matrix $B + \mu I$, with each diagonal entry rounded once. The shift $B - \mu I$ is the
shift by $-\mu$, since negation is exact. -/
def shiftDiag {m : ℕ} (μ : ℝ) (B : Matrix (Fin m) (Fin m) ℝ) : M (Matrix (Fin m) (Fin m) ℝ) :=
  (List.finRange m).foldlM (fun (B : Fin m → Fin m → ℝ) r => do
    let b ← shiftDiagRow rnd μ r (B r)
    pure (Function.update B r b)) B

/-- The product $B G_1 \cdots G_k$ for the Givens rotations $G_{j+1} = G(j, j+1, \theta_j)$ given by
the pairs $(c_j, s_j)$ = `cs j`, as Algorithm 5.2.5 returns them. Each rotation is applied to
all rows by `GolubVanLoan.Chapter05.givensApplyRight`. -/
def rotationsApplyRight {k : ℕ} (cs : Fin k → ℝ × ℝ) (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    M (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :=
  (List.finRange k).foldlM (fun B j =>
    Chapter05.givensApplyRight rnd j.castSucc j.succ (cs j).1 (cs j).2 (List.finRange (k + 1)) B) B

end ShiftedQrProgram

/-- The state of the shifted QR steps (10.5.4) on an $(m+1) \times (m+1)$ matrix: the iterates
$H^{(i)}$, the factors $V_{i+1}$ and $R_{i+1}$, and the accumulated product $V_1 \cdots V_i$
after $i$ steps. -/
structure ShiftedQrState (m : ℕ) where
  /-- The iterates: `H i` is the source's $H^{(i)}$. -/
  H : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  /-- The orthogonal factors: `V i` is the source's $V_{i+1}$. -/
  V : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  /-- The triangular factors: `R i` is the source's $R_{i+1}$. -/
  R : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  /-- The accumulated product $V = V_1 \cdots V_i$. -/
  acc : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ

section ShiftedQrProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- Step $i + 1$ of (10.5.4): the Givens QR factorization $H^{(i)} - \mu_{i+1} I = V_{i+1} R_{i+1}$
of a Hessenberg matrix by Algorithm 5.2.5, which returns $R_{i+1}$ and the rotation pairs; the
matrix $V_{i+1}$ formed from the rotations; $H^{(i+1)} = R_{i+1} V_{i+1} + \mu_{i+1} I$, with
the rotations applied to $R_{i+1}$ on the right; and the update $V \leftarrow V V_{i+1}$. -/
noncomputable def shiftedQrStep {m : ℕ} (μ : ℕ → ℝ) (st : ShiftedQrState m) (i : ℕ) :
    M (ShiftedQrState m) := do
  let B ← shiftDiag rnd (-μ i) (st.H i)
  let RC ← Chapter05.algorithm_5_2_5 rnd B
  let Vi ← rotationsApplyRight rnd RC.2 1
  let RV ← rotationsApplyRight rnd RC.2 RC.1
  let Hn ← shiftDiag rnd (μ i) RV
  let acc ← rotationsApplyRight rnd RC.2 st.acc
  pure { H := Function.update st.H (i + 1) Hn, V := Function.update st.V i Vi,
         R := Function.update st.R i RC.1, acc := acc }

/-- **Equation (10.5.4)** of [golub2013matrix], $p$ steps of the shifted QR iteration on an upper
Hessenberg $H_c$:
```
H^(0) = H_c
for i = 1:p
    H^(i−1) − μ_i I = V_i R_i   (Givens QR)
    H^(i) = R_i V_i + μ_i I
end
H₊ = H^(p)
```
together with the accumulation of $V = V_1 \cdots V_p$ (10.5.5).

**Typo.** The source prints the loop as `for i = 0:p`. It runs for $i = 1, \dots, p$.

The shifts are `μ 0, …, μ (p - 1)`, the source's $\mu_1, \dots, \mu_p$, and the source's $m$ is
`m + 1` here. Every arithmetic result passes through the rounding hook `rnd`. The exact
semantics is `GolubVanLoan.Chapter10.equation_10_5_4`. -/
noncomputable def shiftedQrSteps {m : ℕ} (Hc : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (μ : ℕ → ℝ) (p : ℕ) : M (ShiftedQrState m) :=
  (List.range p).foldlM (shiftedQrStep rnd μ)
    { H := fun _ => Hc, V := fun _ => 1, R := fun _ => 1, acc := 1 }

end ShiftedQrProgram

/-- In exact arithmetic, `GolubVanLoan.Chapter10.shiftDiag` returns $B + \mu I$. -/
theorem shiftDiag_spec {m : ℕ} (μ : ℝ) (B : Matrix (Fin m) (Fin m) ℝ) :
    Id.run (shiftDiag pure μ B) = B + μ • 1 := by
  ext r c
  have h := congrFun (List.idRun_foldlM_update_apply
    (fun r x => shiftDiagRow (pure : ℝ → Id ℝ) μ r x) (List.finRange m) (List.nodup_finRange m)
    B r) c
  rw [ite_eq_left (List.mem_finRange r)] at h
  refine h.trans ?_
  simp only [shiftDiagRow, Id.run_bind, Id.run_pure, Function.update_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hrc : c = r
  · subst hrc; simp
  · simp [hrc, Ne.symm hrc]

/-- In exact arithmetic, `GolubVanLoan.Chapter10.rotationsApplyRight` returns $B G_1 \cdots G_k$,
the product with the rotation matrices $G(j, j+1, \theta_j)$ of Chapter 5 in increasing order of
$j$. This product is the matrix $Q$ of Algorithm 5.2.5. -/
theorem rotationsApplyRight_spec {k : ℕ} (cs : Fin k → ℝ × ℝ)
    (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Id.run (rotationsApplyRight pure cs B) = B * (List.ofFn fun j : Fin k =>
      Chapter05.givensRotation j.castSucc j.succ (cs j).1 (cs j).2).prod := by
  rw [List.ofFn_eq_map]
  unfold rotationsApplyRight
  generalize List.finRange k = l
  induction l generalizing B with
  | nil => simp
  | cons j l ih =>
    rw [List.foldlM_cons, Id.run_bind, Chapter05.givensApplyRight_spec_of_forall_mem
      j.castSucc_lt_succ.ne _ _ (List.nodup_finRange _) (List.mem_finRange), ih,
      List.map_cons, List.prod_cons, Matrix.mul_assoc]

/-- **Equation (10.5.4)** of [golub2013matrix], exact semantics. Let
$H_c \in \mathbb{R}^{(m+1) \times (m+1)}$ be upper Hessenberg, and let
$\mu_1, \dots, \mu_p \in \mathbb{R}$. In exact arithmetic, the run of the $p$ shifted QR steps
satisfies:
* $H^{(0)} = H_c$, and the computed $H^{(i)}$, $V_i$ and $R_i$ satisfy the two lines of
  (10.5.4);
* every $V_i$ is orthogonal and upper Hessenberg, and every $R_i$ is upper triangular;
* every $H^{(i)}$, $i = 0, \dots, p$, is upper Hessenberg;
* the accumulated product is $V = V_1 \cdots V_p$.

The two lines of (10.5.4) are `Matrix.IsShiftedQrChain`. The properties of $V_i$ and $R_i$ come
from `GolubVanLoan.Chapter05.algorithm_5_2_5_spec`. The Hessenberg form of $H^{(i)}$ is the
source's reference to §7.4.2, `Matrix.IsShiftedQrChain.isUpperHessenberg`. -/
theorem equation_10_5_4 {m : ℕ} {Hc : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hH : Hc.IsUpperHessenberg) (μ : ℕ → ℝ) (p : ℕ) :
    let st := Id.run (shiftedQrSteps pure Hc μ p)
    st.H 0 = Hc ∧ Matrix.IsShiftedQrChain st.H st.V st.R μ p ∧
      (∀ i < p, st.V i ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ ∧ (st.V i).IsUpperHessenberg ∧
        (st.R i).IsUpperTriangular) ∧
      (∀ i ≤ p, (st.H i).IsUpperHessenberg) ∧ st.acc = ((List.range p).map st.V).prod := by
  intro st
  let P : ℕ → ShiftedQrState m → Prop := fun p st =>
    st.H 0 = Hc ∧ Matrix.IsShiftedQrChain st.H st.V st.R μ p ∧
      (∀ i < p, st.V i ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ ∧ (st.V i).IsUpperHessenberg ∧
        (st.R i).IsUpperTriangular) ∧ st.acc = ((List.range p).map st.V).prod
  have hHess : ∀ p st, P p st → ∀ i ≤ p, (st.H i).IsUpperHessenberg := by
    rintro p st ⟨h0, hc, hVR, -⟩
    exact hc.isUpperHessenberg (h0 ▸ hH) (fun i hi => (hVR i hi).2.2) (fun i hi => (hVR i hi).2.1)
  suffices hP : ∀ p, P p (Id.run (shiftedQrSteps pure Hc μ p)) by
    obtain ⟨h0, hc, hVR, hacc⟩ := hP p
    exact ⟨h0, hc, hVR, hHess p _ (hP p), hacc⟩
  intro p
  induction p with
  | zero =>
    refine ⟨rfl, ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
  | succ p ih =>
    have hrun : Id.run (shiftedQrSteps pure Hc μ (p + 1)) =
        Id.run (shiftedQrStep pure μ (Id.run (shiftedQrSteps pure Hc μ p)) p) := by
      simp only [shiftedQrSteps, List.range_succ, List.foldlM_append, List.foldlM_cons,
        List.foldlM_nil, bind_pure, Id.run_bind]
    rw [hrun]
    set s := Id.run (shiftedQrSteps pure Hc μ p)
    obtain ⟨h0, hc, hVR, hacc⟩ := ih
    have hHp : (s.H p).IsUpperHessenberg := hHess p s ⟨h0, hc, hVR, hacc⟩ p le_rfl
    set B := s.H p + (-μ p) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) with hB
    have hBH : B.IsUpperHessenberg := hHp.add_smul_one _
    obtain ⟨hQR, hQH⟩ := Chapter05.algorithm_5_2_5_spec B hBH
    set RC := Id.run (Chapter05.algorithm_5_2_5 pure B)
    set Q := (List.ofFn fun j : Fin m => Chapter05.givensRotation j.castSucc j.succ
      (RC.2 j).1 (RC.2 j).2).prod
    simp only [shiftedQrStep, Id.run_bind, Id.run_pure, shiftDiag_spec, rotationsApplyRight_spec]
    try rw [← hB]
    dsimp only [P]
    simp only [Matrix.one_mul]
    have hVs : ∀ i < p, Function.update s.V p Q i = s.V i := fun i hi =>
      Function.update_of_ne hi.ne _ _
    have hRs : ∀ i < p, Function.update s.R p RC.1 i = s.R i := fun i hi =>
      Function.update_of_ne hi.ne _ _
    have hHs : ∀ i ≤ p, Function.update s.H (p + 1) (RC.1 * Q + μ p • 1) i = s.H i :=
      fun i hi => Function.update_of_ne (by omega) _ _
    refine ⟨by rw [hHs 0 (Nat.zero_le _)]; exact h0, ⟨fun i hi => ?_, fun i hi => ?_⟩,
      fun i hi => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hHs i hi.le, hVs i hi, hRs i hi]; exact hc.sub_eq i hi
      · rw [hHs i le_rfl, Function.update_self, Function.update_self, hQR.mul_eq, hB,
          neg_smul, sub_eq_add_neg]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hHs (i + 1) hi, hVs i hi, hRs i hi]; exact hc.succ_eq i hi
      · rw [Function.update_self, Function.update_self, Function.update_self]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hVs i hi, hRs i hi]; exact hVR i hi
      · rw [Function.update_self, Function.update_self]
        exact ⟨hQR.mem_unitaryGroup, hQH, fun a b hab => hQR.apply_eq_zero a b hab⟩
    · rw [hacc, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, Function.update_self]
      congr 1
      exact congrArg List.prod (List.map_congr_left fun i hi => (hVs i (List.mem_range.1 hi)).symm)

/-! ### Explicit restarting (10.5.10) -/

/-- The $n \times K$ matrix whose column $l$ is the computed vector $q_{l+1}$ of a run of Algorithm
10.5.1. -/
def ArnoldiState.qMatrix (s : ArnoldiState n) (K : ℕ) : Matrix (Fin n) (Fin K) ℝ :=
  Matrix.of fun i l => s.q l i

/-- The leading $K \times K$ block $(h_{il})$ of the computed Hessenberg entries of a run of
Algorithm 10.5.1. -/
def ArnoldiState.hMatrix (s : ArnoldiState n) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun i l => s.h i l

section RestartPrograms

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One cycle of explicit restarting (10.5.10), with $m = j + p + 1$: $m$ steps of Algorithm 10.5.1
from $q_1$, which give $Q_c$ and $H_c$; the filter values `shifts` $H_c$; $p$ steps of (10.5.4)
on $H_c$; and the new starting vector $Q_c V(:, 1)$, computed by the gaxpy of Chapter 1. -/
noncomputable def explicitRestartCycle (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let s ← algorithm_10_5_1 rnd A q₁ (j + p + 1)
  let st ← shiftedQrSteps rnd (s.hMatrix (j + p + 1)) (shifts (s.hMatrix (j + p + 1))) p
  algorithm_1_1_3 rnd (s.qMatrix (j + p + 1)) (fun i => st.acc i 0) 0

/-- **Equation (10.5.10)** of [golub2013matrix] (explicitly restarted Arnoldi), repeated `cycles`
times:
```
Repeat:
  With starting vector q₁, perform m steps of the Arnoldi iteration obtaining Q_c, H_c.
  Determine filter values μ_1, …, μ_p.
  Perform p steps of the shifted QR iteration (10.5.4) obtaining H₊ and V.
  Replace q₁ with the first column of Q_c V.
```

Here $m$ is `j + p + 1`. The filter values are chosen by the function `shifts` of $H_c$ that the
caller supplies; the source leaves the choice to heuristics, and only the values `shifts H_c i`
for `i < p` are used. Each cycle is `GolubVanLoan.Chapter10.explicitRestartCycle`. -/
noncomputable def explicitlyRestartedArnoldi (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ)
    (cycles : ℕ) : M (Fin n → ℝ) :=
  (List.range cycles).foldlM (fun q _ => explicitRestartCycle rnd A j p shifts q) q₁

end RestartPrograms

/-- The coefficients returned by the modified Gram–Schmidt loop of $k$ steps vanish from index $k$
on. -/
private theorem mgsLoop_snd_eq_zero (q : ℕ → Fin n → ℝ) (k : ℕ) (r : Fin n → ℝ) {i : ℕ}
    (hi : k ≤ i) : (Id.run (mgsLoop pure q k r)).2 i = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := ih (by omega)
    simp only [mgsLoop, List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      Id.run_bind, Id.run_pure, bind_pure] at h ⊢
    rw [Function.update_of_ne (by omega)]
    exact h

/-- The exact run of Algorithm 10.5.1 has $h_{il} = 0$ for $i > l + 1$. -/
private theorem algorithm_10_5_1_h_eq_zero (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ)
    (t : ℕ) {i l : ℕ} (hil : l + 1 < i) : (Id.run (algorithm_10_5_1 pure A q₁ t)).h i l = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [algorithm_10_5_1_succ]
    cases hsd : (Id.run (algorithm_10_5_1 pure A q₁ t)).done with
    | true => simp only [arnoldiStep, hsd, ↓reduceIte, Id.run_pure]; exact ih
    | false =>
      simp only [arnoldiStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure]
      by_cases h1 : l = (Id.run (algorithm_10_5_1 pure A q₁ t)).k
      · rw [ite_eq_left h1, ite_eq_right (by omega)]
        exact mgsLoop_snd_eq_zero _ _ _ (by omega)
      · rw [ite_eq_right h1]; exact ih

/-- **Algorithm 10.5.1** of [golub2013matrix], the computed matrices. Let
$A \in \mathbb{R}^{n \times n}$, let $q_1 \in \mathbb{R}^n$ be a unit vector, and let $K$ be at
most the grade of $q_1$ for $A$. In exact arithmetic, the run with $K$ passes makes all $K$
steps and returns the matrices $Q_K$ and $H_K$ of the Arnoldi process, and, if $K \ge 1$, its
residual $r_K$.

The matrices are `Arnoldi.basisMatrix`, `Arnoldi.hessenbergSq` and `Arnoldi.w`, read off by
`GolubVanLoan.Chapter10.ArnoldiState.qMatrix` and `GolubVanLoan.Chapter10.ArnoldiState.hMatrix`. -/
theorem algorithm_10_5_1_matrices (A : Matrix (Fin n) (Fin n) ℝ) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) {K : ℕ}
    (hK : K ≤ grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁)) :
    (Id.run (algorithm_10_5_1 pure A q₁ K)).k = K ∧
      (Id.run (algorithm_10_5_1 pure A q₁ K)).qMatrix K =
        Arnoldi.basisMatrix A (WithLp.toLp 2 q₁) K ∧
      (Id.run (algorithm_10_5_1 pure A q₁ K)).hMatrix K =
        Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) K ∧
      (0 < K → (Id.run (algorithm_10_5_1 pure A q₁ K)).r =
        (Arnoldi.w (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) (K - 1)).ofLp) := by
  obtain ⟨hk, hvec, hr⟩ := algorithm_10_5_1_spec A hq K
  have hk' : (Id.run (algorithm_10_5_1 pure A q₁ K)).k = K := by
    rw [hk]; exact min_eq_left hK
  refine ⟨hk', ?_, ?_, fun h => (hr (by rw [hk']; exact h)).trans (by rw [hk'])⟩
  · ext i l
    simp only [ArnoldiState.qMatrix, Arnoldi.basisMatrix, Matrix.of_apply]
    rw [(hvec l (by rw [hk']; exact l.isLt)).1]
  · ext i l
    simp only [ArnoldiState.hMatrix, Arnoldi.hessenbergSq, Matrix.of_apply]
    by_cases hil : (i : ℕ) ≤ l + 1
    · exact (hvec l (by rw [hk']; exact l.isLt)).2 i hil
    · rw [algorithm_10_5_1_h_eq_zero A q₁ K (by omega),
        Arnoldi.coeff_eq_zero_of_lt _ _ (by omega)]

/-- A matrix with orthonormal columns maps $e_1$ to a unit vector. -/
private theorem norm_mulVec_single_zero {K : ℕ} {W : Matrix (Fin n) (Fin (K + 1)) ℝ}
    (hW : Wᵀ * W = 1) :
    ‖(WithLp.toLp 2 (W *ᵥ Pi.single 0 1) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have h := congrFun (congrFun hW 0) 0
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.transpose_apply] at h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simpa [Matrix.mulVec_single_one, sq] using h

/-- For a unit vector $q$, the first column of $Q_{K+1}$ is $q$. -/
private theorem basisMatrix_mulVec_single_zero (A : Matrix (Fin n) (Fin n) ℝ) {q : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ = 1) (K : ℕ) :
    Arnoldi.basisMatrix A (WithLp.toLp 2 q) (K + 1) *ᵥ Pi.single 0 1 = q := by
  have hq0 : (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hq; exact zero_ne_one hq
  ext i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Arnoldi.basisMatrix,
    Matrix.of_apply, Fin.val_zero]
  rw [Arnoldi.vec_zero _ _ hq0, hq]
  simp

/-- **Equation (10.5.10)** of [golub2013matrix], one cycle. Let $A \in \mathbb{R}^{n \times n}$, let
$q \in \mathbb{R}^n$ be a unit vector, and let $m = j + p + 1$ be at most the grade of $q$ for
$A$. Let $H_c = H_m$ be the Hessenberg matrix of $m$ Arnoldi steps from $q$, let $p$ be the
filter polynomial of the shifts chosen from $H_c$, and let $R = R_p \cdots R_1$ be the product
of the triangular factors of the $p$ shifted QR steps on $H_c$. In exact arithmetic, the new
starting vector $q_+$ of the cycle is a unit vector, and
$$R(1, 1) \, q_+ = p(A) q.$$

This is the source's $q_+ = c \, p(A) q_1$ of §10.5.3, with $c = 1/R(1, 1)$, without the
division. -/
theorem explicitRestartCycle_spec (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) {q : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ = 1)
    (hg : j + p + 1 ≤ grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 q)) :
    let Hc := Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) (WithLp.toLp 2 q) (j + p + 1)
    let st := Id.run (shiftedQrSteps pure Hc (shifts Hc) p)
    let q' := Id.run (explicitRestartCycle pure A j p shifts q)
    ‖(WithLp.toLp 2 q' : EuclideanSpace ℝ (Fin n))‖ = 1 ∧
      ((List.range p).reverse.map st.R).prod 0 0 • q' =
        aeval A (filterPolynomial (shifts Hc) p) *ᵥ q := by
  intro Hc st q'
  obtain ⟨-, hQ, hH, -⟩ := algorithm_10_5_1_matrices A hq hg
  set Q := Arnoldi.basisMatrix A (WithLp.toLp 2 q) (j + p + 1)
  have hq' : q' = (Q * st.acc) *ᵥ Pi.single 0 1 := by
    simp only [q', explicitRestartCycle, Id.run_bind, algorithm_1_1_3_spec, zero_add]
    rw [hQ, hH, ← Matrix.mulVec_mulVec]
    congr 1
    ext i
    simp [st, Hc]
  have hD := (equation_10_5_2 A (WithLp.toLp 2 q) (k := j + p + 1) (by omega)).2.2 hg
  obtain ⟨h0, hc, hVR, -, hacc⟩ :=
    equation_10_5_4 (Arnoldi.hessenbergSq_isUpperHessenberg (Matrix.toEuclideanLin A)
      (WithLp.toLp 2 q) (j + p + 1)) (shifts Hc) p
  rw [hq', hacc]
  refine ⟨norm_mulVec_single_zero (equation_10_5_9 hD hc h0 fun i hi => (hVR i hi).1).2, ?_⟩
  rw [(restart_firstColumn_eq hD).2 hc h0 fun i hi => (hVR i hi).2.2,
    basisMatrix_mulVec_single_zero A hq]

/-- The run with $\ell + 1$ cycles is one cycle after the run with $\ell$ cycles. -/
private theorem explicitlyRestartedArnoldi_succ (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ) (ℓ : ℕ) :
    Id.run (explicitlyRestartedArnoldi pure A j p shifts q₁ (ℓ + 1)) =
      Id.run (explicitRestartCycle pure A j p shifts
        (Id.run (explicitlyRestartedArnoldi pure A j p shifts q₁ ℓ))) := by
  simp only [explicitlyRestartedArnoldi, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Equation (10.5.10)** of [golub2013matrix], exact semantics. Let
$A \in \mathbb{R}^{n \times n}$, let $q_1 \in \mathbb{R}^n$ be a unit vector, let
$m = j + p + 1$, and let $L \ge 0$. Let $q^{(\ell)}$ be the starting vector after $\ell$ cycles,
with $q^{(0)} = q_1$, let $p_\ell$ be the filter polynomial of cycle $\ell$, with the shifts
chosen from its $H_c$, and let $\rho_\ell$ be the entry $R(1, 1)$ of the product of its
triangular factors. Assume that no cycle $\ell < L$ breaks down, that is, $m$ is at most the
grade of $q^{(\ell)}$ for $A$. Then in exact arithmetic:
* every $q^{(\ell)}$ with $\ell \le L$ is a unit vector;
* $\rho_\ell \, q^{(\ell+1)} = p_\ell(A) q^{(\ell)}$ for every $\ell < L$;
* if every $\rho_\ell$ with $\ell < L$ is nonzero, then $q^{(L)}$ is a multiple of
  $p_{L-1}(A) \cdots p_0(A) q_1$. -/
theorem equation_10_5_10 (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) (L : ℕ) :
    let q : ℕ → Fin n → ℝ := fun ℓ => Id.run (explicitlyRestartedArnoldi pure A j p shifts q₁ ℓ)
    let Hc : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ := fun ℓ =>
      Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) (WithLp.toLp 2 (q ℓ)) (j + p + 1)
    let ρ : ℕ → ℝ := fun ℓ =>
      ((List.range p).reverse.map (Id.run (shiftedQrSteps pure (Hc ℓ) (shifts (Hc ℓ)) p)).R).prod
        0 0
    (∀ ℓ < L, j + p + 1 ≤ grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 (q ℓ))) →
      (∀ ℓ ≤ L, ‖(WithLp.toLp 2 (q ℓ) : EuclideanSpace ℝ (Fin n))‖ = 1) ∧
      (∀ ℓ < L, ρ ℓ • q (ℓ + 1) = aeval A (filterPolynomial (shifts (Hc ℓ)) p) *ᵥ q ℓ) ∧
      ((∀ ℓ < L, ρ ℓ ≠ 0) → ∃ c : ℝ, q L = c •
        (aeval A ((List.range L).map fun ℓ => filterPolynomial (shifts (Hc ℓ)) p).prod *ᵥ q₁)) := by
  intro q Hc ρ hg
  have hsucc : ∀ ℓ, q (ℓ + 1) = Id.run (explicitRestartCycle pure A j p shifts (q ℓ)) :=
    explicitlyRestartedArnoldi_succ A j p shifts q₁
  have hunit : ∀ ℓ ≤ L, ‖(WithLp.toLp 2 (q ℓ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    intro ℓ hℓ
    induction ℓ with
    | zero => exact hq
    | succ ℓ ih =>
      rw [hsucc]
      exact (explicitRestartCycle_spec A j p shifts (ih (by omega)) (hg ℓ (by omega))).1
  have hrel : ∀ ℓ < L,
      ρ ℓ • q (ℓ + 1) = aeval A (filterPolynomial (shifts (Hc ℓ)) p) *ᵥ q ℓ := by
    intro ℓ hℓ
    rw [hsucc]
    exact (explicitRestartCycle_spec A j p shifts (hunit ℓ hℓ.le) (hg ℓ hℓ)).2
  refine ⟨hunit, hrel, fun hρ => ?_⟩
  have key : ∀ L' ≤ L, ∃ c : ℝ, q L' = c •
      (aeval A ((List.range L').map fun ℓ => filterPolynomial (shifts (Hc ℓ)) p).prod *ᵥ q₁) := by
    intro L' hL'
    induction L' with
    | zero => exact ⟨1, by simp [q, explicitlyRestartedArnoldi]⟩
    | succ L' ih =>
      obtain ⟨c, hc⟩ := ih (by omega)
      refine ⟨(ρ L')⁻¹ * c, ?_⟩
      have h := hrel L' (by omega)
      rw [← eq_inv_smul_iff₀ (hρ L' (by omega))] at h
      rw [h, hc, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, mul_comm, map_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
        smul_smul]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul, ← map_mul,
        mul_comm (filterPolynomial (shifts (Hc L')) p), mul_comm c]
  exact key L le_rfl

/-! ### Implicit restarting (§10.5.3, the modified framework) -/

section ImplicitProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One cycle of the implicitly restarted framework from an $m$-step state, $m = j + p + 1$: the
filter values `shifts` $H_c$; $p$ steps of (10.5.4) on $H_c$; $Q_+ = Q_c V$ by Algorithm 1.1.5;
then $Q_c \leftarrow Q_+(:, 1:j+1)$, $H_c \leftarrow H_+(1:j+1, 1:j+1)$, the residual $r_c
\leftarrow h^+_{j+2,j+1} Q_+(:, j+2) + v_{m,j+1} r_c$ of
`GolubVanLoan.Chapter10.implicitRestart_isArnoldiDecomposition` and $h_{j+2,j+1} = \|r_c\|_2$;
and finally the Arnoldi steps $j + 2, \dots, m$, continued from that state by $p$ passes of
`GolubVanLoan.Chapter10.arnoldiStep`. -/
noncomputable def implicitRestartCycle (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (s : ArnoldiState n) :
    M (ArnoldiState n) := do
  let st ← shiftedQrSteps rnd (s.hMatrix (j + p + 1)) (shifts (s.hMatrix (j + p + 1))) p
  let Qp ← algorithm_1_1_5 rnd (s.qMatrix (j + p + 1)) st.acc 0
  let t ← algorithm_1_1_2 rnd (st.acc (Fin.last (j + p)) ⟨j, by omega⟩) s.r 0
  let r ← algorithm_1_1_2 rnd
    (if h : j + 1 < j + p + 1 then st.H p ⟨j + 1, h⟩ ⟨j, by omega⟩ else 0)
    (fun i => if h : j + 1 < j + p + 1 then Qp i ⟨j + 1, h⟩ else 0) t
  let b ← vecNorm rnd r
  (List.range p).foldlM (fun s _ => arnoldiStep rnd A s)
    { k := j + 1
      q := fun l i => if h : l < j + p + 1 then Qp i ⟨l, h⟩ else 0
      h := fun i l => if h : i < j + 1 ∧ l < j + 1 then st.H p ⟨i, by omega⟩ ⟨l, by omega⟩
        else if i = j + 1 ∧ l = j then b else 0
      r := r
      done := decide (b = 0) }

/-- **Section 10.5.3** of [golub2013matrix], implicitly restarted Arnoldi, repeated `cycles` times
after the first $m$ Arnoldi steps:
```
With starting vector q₁, perform m steps of the Arnoldi iteration obtaining Q_c, H_c, r_c.
Repeat:
  Determine filter values μ_1, …, μ_p.
  Perform p steps of the shifted QR iteration (10.5.4) applied to H_c obtaining H₊ and V.
  Replace Q_c with the first j columns of Q_c V, H_c with H₊(1:j, 1:j), r_c with v_{mj} r_c.
  Starting with A Q_c = Q_c H_c + r_c e_jᵀ, perform steps j+1, …, j+p = m of the Arnoldi
  iteration obtaining A Q_m = Q_m H_m + r_m e_mᵀ.
  Set Q_c = Q_m, H_c = H_m, r_c = r_m.
```

**Correction.** The source replaces $r_c$ with $v_{mj} r_c$. The program uses the residual
$h^+_{j+1,j} q^+_{j+1} + v_{mj} r_c$ of the truncated decomposition, see
`GolubVanLoan.Chapter10.implicitRestart_isArnoldiDecomposition`.

The source's $m$ and $j$ are `j + p + 1` and `j + 1` here. The filter values are chosen by the
function `shifts` of $H_c$ that the caller supplies. Each cycle is
`GolubVanLoan.Chapter10.implicitRestartCycle`. -/
noncomputable def implicitlyRestartedArnoldi (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ)
    (cycles : ℕ) : M (ArnoldiState n) := do
  let s ← algorithm_10_5_1 rnd A q₁ (j + p + 1)
  (List.range cycles).foldlM (fun s _ => implicitRestartCycle rnd A j p shifts s) s

end ImplicitProgram

/-- The Arnoldi relations of a state, column by column: the vectors $q_0, \dots, q_{k-1}$ are
orthonormal, the residual $r$ is orthogonal to them, $A q_b = \sum_{i < k} h_{ib} q_i$ plus $r$
for the last column, $h$ vanishes below the subdiagonal, $h_{k,k-1} = \|r\|$, and the flag
records whether $\|r\| = 0$. -/
private def ArnoldiInv (A : Matrix (Fin n) (Fin n) ℝ) (s : ArnoldiState n) : Prop :=
  0 < s.k ∧
    (∀ a < s.k, ∀ b < s.k, s.q a ⬝ᵥ s.q b = if a = b then 1 else 0) ∧
    (∀ a < s.k, s.q a ⬝ᵥ s.r = 0) ∧
    (∀ b < s.k, A *ᵥ s.q b =
      ∑ i ∈ Finset.range s.k, s.h i b • s.q i + if b + 1 = s.k then s.r else 0) ∧
    (∀ i l, l + 1 < i → s.h i l = 0) ∧
    s.h s.k (s.k - 1) = ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ ∧
    s.done = decide (‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ = 0)

/-- Against orthonormal vectors $q_i$, the modified Gram–Schmidt loop returns the classical
projection $v - \sum_{i < k} (q_i^T v) q_i$ and the coefficients $q_i^T v$. -/
private theorem mgsLoop_orthonormal (q : ℕ → Fin n → ℝ) (k : ℕ) (v : Fin n → ℝ)
    (hq : ∀ a < k, ∀ b < k, q a ⬝ᵥ q b = if a = b then 1 else 0) :
    Id.run (mgsLoop pure q k v) = (v - ∑ i ∈ Finset.range k, (q i ⬝ᵥ v) • q i,
      fun i => if i < k then q i ⬝ᵥ v else 0) := by
  induction k with
  | zero => simp [mgsLoop]
  | succ k ih =>
    have ih' := ih fun a ha b hb => hq a (by omega) b (by omega)
    simp only [mgsLoop, List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      Id.run_bind, Id.run_pure, bind_pure] at ih' ⊢
    rw [ih']
    simp only [algorithm_1_1_1_spec, algorithm_1_1_2_spec]
    have hc : q k ⬝ᵥ (v - ∑ i ∈ Finset.range k, (q i ⬝ᵥ v) • q i) = q k ⬝ᵥ v := by
      rw [dotProduct_sub, dotProduct_sum]
      rw [Finset.sum_eq_zero fun i hi => by
        rw [dotProduct_smul, hq k (by omega) i (by simp at hi; omega),
          ite_eq_right (by simp at hi; omega), smul_zero], sub_zero]
    rw [hc]
    refine Prod.ext ?_ (funext fun i => ?_)
    · simp only [Finset.sum_range_succ]
      rw [neg_smul, ← sub_eq_add_neg, sub_sub]
    · by_cases hik : i = k
      · subst hik; simp
      · simp only [Function.update_of_ne hik]
        by_cases hi : i < k
        · rw [ite_eq_left hi, ite_eq_left (by omega)]
        · rw [ite_eq_right hi, ite_eq_right (by omega)]

/-- A state gives a $(K+1)$-step Arnoldi decomposition if and only if the Arnoldi relations hold
column by column. -/
private theorem isArnoldiDecomposition_iff_vec (A : Matrix (Fin n) (Fin n) ℝ)
    (s : ArnoldiState n) (K : ℕ) :
    IsArnoldiDecomposition A (s.qMatrix (K + 1)) (s.hMatrix (K + 1)) s.r ↔
      (∀ a < K + 1, ∀ b < K + 1, s.q a ⬝ᵥ s.q b = if a = b then 1 else 0) ∧
      (∀ a < K + 1, s.q a ⬝ᵥ s.r = 0) ∧
      (∀ b < K + 1, A *ᵥ s.q b =
        ∑ i ∈ Finset.range (K + 1), s.h i b • s.q i + if b + 1 = K + 1 then s.r else 0) ∧
      (∀ i < K + 1, ∀ l < K + 1, l + 1 < i → s.h i l = 0) := by
  have hQQ : ∀ a b : Fin (K + 1), ((s.qMatrix (K + 1))ᵀ * s.qMatrix (K + 1)) a b =
      s.q a ⬝ᵥ s.q b := fun a b => by
    simp [Matrix.mul_apply, ArnoldiState.qMatrix, dotProduct]
  have hQr : ∀ a : Fin (K + 1), ((s.qMatrix (K + 1))ᵀ *ᵥ s.r) a = s.q a ⬝ᵥ s.r := fun a => by
    simp [Matrix.mulVec, ArnoldiState.qMatrix, dotProduct]
  have hcol : ∀ (b : Fin (K + 1)) (x : Fin n),
      (A * s.qMatrix (K + 1)) x b = (A *ᵥ s.q b) x ∧
      (s.qMatrix (K + 1) * s.hMatrix (K + 1) +
          Matrix.vecMulVec s.r (Krylov.lastVec (1 : ℝ) (K + 1))) x b =
        (∑ i ∈ Finset.range (K + 1), s.h i b • s.q i +
          if (b : ℕ) + 1 = K + 1 then s.r else 0) x := fun b x => by
    refine ⟨by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, ArnoldiState.qMatrix], ?_⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, ArnoldiState.qMatrix, ArnoldiState.hMatrix,
      Matrix.of_apply, Matrix.vecMulVec_apply, Krylov.lastVec, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => s.q i x * s.h i b)]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · split_ifs <;> simp
  constructor
  · intro h
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_, fun b hb => ?_, fun i hi l hl hil => ?_⟩
    · have := congrFun (congrFun h.transpose_mul_self ⟨a, ha⟩) ⟨b, hb⟩
      rw [hQQ, Matrix.one_apply] at this
      rw [this]
      simp [Fin.ext_iff]
    · have := congrFun h.transpose_mulVec ⟨a, ha⟩
      rwa [hQr] at this
    · ext x
      have := congrFun (congrFun h.mul_eq x) ⟨b, hb⟩
      rw [(hcol ⟨b, hb⟩ x).1, (hcol ⟨b, hb⟩ x).2] at this
      exact this
    · exact h.isUpperHessenberg ⟨i, hi⟩ ⟨l, hl⟩
        ((GolubVanLoan.Chapter05.exists_between_iff _ _).2 hil)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, fun i l hil => ?_, ?_, ?_⟩
    · ext a b
      rw [hQQ, h1 a a.isLt b b.isLt, Matrix.one_apply]
      simp [Fin.ext_iff]
    · exact h4 i i.isLt l l.isLt ((GolubVanLoan.Chapter05.exists_between_iff _ _).1 hil)
    · ext a
      rw [hQr, h2 a a.isLt]
      rfl
    · ext x b
      rw [(hcol b x).1, (hcol b x).2, h3 b b.isLt]

/-- One exact pass of the loop body of Algorithm 10.5.1 keeps the Arnoldi relations and the first
vector, and does not decrease the step counter. -/
private theorem arnoldiStep_inv (A : Matrix (Fin n) (Fin n) ℝ) {s : ArnoldiState n}
    (hs : ArnoldiInv A s) :
    ArnoldiInv A (Id.run (arnoldiStep pure A s)) ∧ (Id.run (arnoldiStep pure A s)).q 0 = s.q 0 ∧
      s.k ≤ (Id.run (arnoldiStep pure A s)).k := by
  obtain ⟨hk0, horth, hperp, hrel, hzero, hnorm, hdone⟩ := hs
  cases hsd : s.done with
  | true =>
    have hid : Id.run (arnoldiStep pure A s) = s := by simp [arnoldiStep, hsd]
    rw [hid]
    exact ⟨⟨hk0, horth, hperp, hrel, hzero, hnorm, hdone⟩, rfl, le_rfl⟩
  | false =>
    set ρ := ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ with hρ
    have hρ0 : ρ ≠ 0 := by simpa [hsd] using hdone.symm
    have hrr : s.r ⬝ᵥ s.r = ρ ^ 2 := by
      rw [hρ, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial]
    have hhk : (if s.k = 0 then 1 else s.h s.k (s.k - 1)) = ρ := by
      rw [ite_eq_right (by omega), hnorm]
    set qk := ρ⁻¹ • s.r with hqk
    set q' := Function.update s.q s.k qk with hq'
    have hq'old : ∀ a < s.k, q' a = s.q a := fun a ha => Function.update_of_ne ha.ne _ _
    have hq'new : q' s.k = qk := Function.update_self _ _ _
    have horth' : ∀ a < s.k + 1, ∀ b < s.k + 1, q' a ⬝ᵥ q' b = if a = b then 1 else 0 := by
      have hnew : ∀ a < s.k, q' a ⬝ᵥ q' s.k = 0 := fun a ha => by
        rw [hq'old a ha, hq'new, hqk, dotProduct_smul, hperp a ha, smul_zero]
      intro a ha b hb
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
        · rw [hq'old a ha, hq'old b hb]; exact horth a ha b hb
        · rw [hnew a ha, ite_eq_right ha.ne]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
        · rw [dotProduct_comm, hnew b hb, ite_eq_right hb.ne']
        · rw [ite_eq_left rfl, hq'new, hqk, dotProduct_smul, smul_dotProduct, hrr, smul_eq_mul,
            smul_eq_mul]
          field_simp
    have hmgs := mgsLoop_orthonormal q' (s.k + 1) (A *ᵥ qk) horth'
    set w := A *ᵥ qk - ∑ i ∈ Finset.range (s.k + 1), (q' i ⬝ᵥ A *ᵥ qk) • q' i with hw
    have hperp' : ∀ a < s.k + 1, q' a ⬝ᵥ w = 0 := by
      intro a ha
      rw [hw, dotProduct_sub, dotProduct_sum, Finset.sum_eq_single a (fun i hi hia => by
        rw [dotProduct_smul, horth' a ha i (Finset.mem_range.1 hi), ite_eq_right (Ne.symm hia),
          smul_zero]) (fun h => absurd (Finset.mem_range.2 ha) h), dotProduct_smul,
        horth' a ha a ha, ite_eq_left rfl, smul_eq_mul, mul_one, sub_self]
    simp only [arnoldiStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
      vecDiv_spec, algorithm_1_1_3_spec, zero_add, vecNorm_spec, hhk]
    rw [← hqk, ← hq', hmgs]
    unfold ArnoldiInv
    dsimp only
    refine ⟨⟨Nat.succ_pos _, horth', hperp', fun b hb => ?_, fun i l hil => ?_, ?_, ?_⟩,
      hq'old 0 hk0, Nat.le_succ _⟩
    · rw [Finset.sum_range_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · -- an old column
        rw [Finset.sum_congr rfl (g := fun i => s.h i b • s.q i) fun i hi => by
          simp only [ite_eq_right hb.ne, hq'old i (Finset.mem_range.1 hi)]]
        rw [ite_eq_right hb.ne, ite_eq_right (show b + 1 ≠ s.k + 1 by omega), hq'old b hb, hq'new,
          hrel b hb, add_zero]
        rcases Nat.lt_or_ge (b + 1) s.k with hbk | hbk
        · rw [ite_eq_right hbk.ne, hzero s.k b hbk, zero_smul, add_zero]
        · rw [ite_eq_left (by omega), show b = s.k - 1 by omega, hnorm, hqk, smul_smul,
            mul_inv_cancel₀ hρ0, one_smul]
      · -- the new column
        rw [Finset.sum_congr rfl (g := fun i => (q' i ⬝ᵥ A *ᵥ qk) • q' i) fun i hi => by
          have := Finset.mem_range.1 hi
          simp only [↓reduceIte, ite_eq_right (show i ≠ s.k + 1 by omega),
            ite_eq_left (show i < s.k + 1 by omega)]]
        simp only [↓reduceIte, ite_eq_right (show s.k ≠ s.k + 1 by omega),
          ite_eq_left (show s.k < s.k + 1 by omega)]
        rw [hw, Finset.sum_range_succ, hq'new]
        abel
    · -- zeros below the subdiagonal
      by_cases hl : l = s.k
      · rw [ite_eq_left hl, ite_eq_right (by omega), ite_eq_right (by omega)]
      · rw [ite_eq_right hl]; exact hzero i l hil
    · simp
    · rfl

/-- Any number of exact passes of the loop body of Algorithm 10.5.1 keep the Arnoldi relations and
the first vector. -/
private theorem arnoldiSteps_inv (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) {s : ArnoldiState n}
    (hs : ArnoldiInv A s) :
    ArnoldiInv A (Id.run ((List.range t).foldlM (fun s _ => arnoldiStep pure A s) s)) ∧
      (Id.run ((List.range t).foldlM (fun s _ => arnoldiStep pure A s) s)).q 0 = s.q 0 := by
  induction t with
  | zero => exact ⟨hs, rfl⟩
  | succ t ih =>
    simp only [List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      bind_pure, Id.run_bind]
    obtain ⟨h1, h2, -⟩ := arnoldiStep_inv A ih.1
    exact ⟨h1, h2.trans ih.2⟩

/-- The exact state from which an implicit restart continues the Arnoldi steps: $Q_+ = Q_c V$
truncated to $j + 1$ columns, $H_+$ truncated to its leading $(j+1) \times (j+1)$ block, the
corrected residual $r_+$, and the entry $\|r_+\|$ below that block. -/
private noncomputable def restartState (j p : ℕ) (s : ArnoldiState n)
    (st : ShiftedQrState (j + p)) :
    ArnoldiState n :=
  let Qp := s.qMatrix (j + p + 1) * st.acc
  let r := st.acc (Fin.last (j + p)) ⟨j, by omega⟩ • s.r +
    (if h : j + 1 < j + p + 1 then st.H p ⟨j + 1, h⟩ ⟨j, by omega⟩ else 0) •
      (fun i => if h : j + 1 < j + p + 1 then Qp i ⟨j + 1, h⟩ else 0)
  { k := j + 1
    q := fun l i => if h : l < j + p + 1 then Qp i ⟨l, h⟩ else 0
    h := fun i l => if h : i < j + 1 ∧ l < j + 1 then st.H p ⟨i, by omega⟩ ⟨l, by omega⟩
      else if i = j + 1 ∧ l = j then ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖ else 0
    r := r
    done := decide (‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖ = 0) }

/-- The exact cycle of implicit restarting is the continuation of the Arnoldi steps from the
restarted state. -/
private theorem implicitRestartCycle_eq (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (s : ArnoldiState n) :
    Id.run (implicitRestartCycle pure A j p shifts s) =
      Id.run ((List.range p).foldlM (fun s _ => arnoldiStep pure A s) (restartState j p s
        (Id.run (shiftedQrSteps pure (s.hMatrix (j + p + 1))
          (shifts (s.hMatrix (j + p + 1))) p)))) := by
  simp only [implicitRestartCycle, restartState, Id.run_bind, algorithm_1_1_5_spec,
    algorithm_1_1_2_spec, vecNorm_spec, zero_add]

/-- **Section 10.5.3** of [golub2013matrix], one cycle of implicitly restarted Arnoldi. Let
$A \in \mathbb{R}^{n \times n}$, let $p \ge 1$ and $m = j + p + 1$, and let the input state
$(Q_c, H_c, r_c)$ be an $m$-step Arnoldi decomposition of $A$. Let $p$ be the filter polynomial
of the shifts chosen from $H_c$, let $R = R_p \cdots R_1$ be the product of the triangular
factors of the $p$ shifted QR steps on $H_c$, and let $q_1 = Q_c e_1$. In exact arithmetic, if
the output state again has $m$ columns, then it is an $m$-step Arnoldi decomposition, and its
first column $q_+$ satisfies
$$R(1, 1) \, q_+ = p(A) q_1.$$

The hypothesis on the output says that the continued Arnoldi steps do not break down. -/
theorem implicitRestartCycle_spec (A : Matrix (Fin n) (Fin n) ℝ) {j p : ℕ} (hp : 0 < p)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) {s : ArnoldiState n}
    (hs : IsArnoldiDecomposition A (s.qMatrix (j + p + 1)) (s.hMatrix (j + p + 1)) s.r) :
    let Hc := s.hMatrix (j + p + 1)
    let st := Id.run (shiftedQrSteps pure Hc (shifts Hc) p)
    let s' := Id.run (implicitRestartCycle pure A j p shifts s)
    s'.k = j + p + 1 →
      IsArnoldiDecomposition A (s'.qMatrix (j + p + 1)) (s'.hMatrix (j + p + 1)) s'.r ∧
      ((List.range p).reverse.map st.R).prod 0 0 • (s'.qMatrix (j + p + 1) *ᵥ Pi.single 0 1) =
        aeval A (filterPolynomial (shifts Hc) p) *ᵥ (s.qMatrix (j + p + 1) *ᵥ Pi.single 0 1) := by
  intro Hc st s' hk
  simp only [s', st, Hc, implicitRestartCycle_eq] at hk ⊢
  obtain ⟨h0, hc, hVR, hHs, hacc⟩ := equation_10_5_4 (Hc := s.hMatrix (j + p + 1))
    hs.isUpperHessenberg (shifts (s.hMatrix (j + p + 1))) p
  generalize Id.run (shiftedQrSteps pure (s.hMatrix (j + p + 1))
    (shifts (s.hMatrix (j + p + 1))) p) = st at hk h0 hc hVR hHs hacc ⊢
  have hjp : j + 1 < j + p + 1 := by omega
  obtain ⟨-, hT⟩ := implicitRestart_isArnoldiDecomposition hs hc h0 (fun i hi => (hVR i hi).1)
    (fun i hi => (hVR i hi).2.1) (fun i hi => (hVR i hi).2.2) hp
  rw [← hacc] at hT
  set s₀ := restartState j p s st with hs₀
  have hT' : IsArnoldiDecomposition A (s₀.qMatrix (j + 1)) (s₀.hMatrix (j + 1)) s₀.r := by
    convert hT using 1
    · ext i l
      have := l.isLt
      simp only [s₀, restartState, ArnoldiState.qMatrix, Matrix.of_apply, Matrix.submatrix_apply,
        id]
      split_ifs with h
      · rfl
      · omega
    · ext i l
      have := i.isLt
      have := l.isLt
      simp only [s₀, restartState, ArnoldiState.hMatrix, Matrix.of_apply, Matrix.submatrix_apply]
      split_ifs with h h' <;> first | rfl | exact absurd ⟨by omega, by omega⟩ h
    · simp only [s₀, restartState, hjp, ↓reduceDIte]
      rw [add_comm]
      rfl
  obtain ⟨h1, h2, h3, -⟩ := (isArnoldiDecomposition_iff_vec A s₀ j).1 hT'
  have hinv : ArnoldiInv A s₀ := by
    refine ⟨by simp [s₀, restartState], h1, h2, h3, fun i l hil => ?_, ?_, rfl⟩
    · simp only [s₀, restartState]
      split_ifs with h h'
      · exact (hHs p le_rfl) ⟨i, by omega⟩ ⟨l, by omega⟩
          ((GolubVanLoan.Chapter05.exists_between_iff _ _).2 hil)
      · omega
      · rfl
    · simp [s₀, restartState]
  obtain ⟨hinv', hq0⟩ := arnoldiSteps_inv A p hinv
  obtain ⟨-, i1, i2, i3, i4, -, -⟩ := hinv'
  rw [hk] at i1 i2 i3
  refine ⟨(isArnoldiDecomposition_iff_vec A _ (j + p)).2
    ⟨i1, i2, i3, fun i _ l _ h => i4 i l h⟩, ?_⟩
  have hfirst : ArnoldiState.qMatrix (Id.run ((List.range p).foldlM
      (fun s _ => arnoldiStep pure A s) s₀)) (j + p + 1) *ᵥ Pi.single 0 1 =
      (s.qMatrix (j + p + 1) * ((List.range p).map st.V).prod) *ᵥ Pi.single 0 1 := by
    ext x
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, ArnoldiState.qMatrix,
      Matrix.of_apply, Fin.val_zero, hq0]
    simp [s₀, restartState, hacc]
    rfl
  rw [hfirst]
  exact (restart_firstColumn_eq hs).2 hc h0 fun i hi => (hVR i hi).2.2

/-- The run with $\ell + 1$ cycles is one cycle after the run with $\ell$ cycles. -/
private theorem implicitlyRestartedArnoldi_succ (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ) (ℓ : ℕ) :
    Id.run (implicitlyRestartedArnoldi pure A j p shifts q₁ (ℓ + 1)) =
      Id.run (implicitRestartCycle pure A j p shifts
        (Id.run (implicitlyRestartedArnoldi pure A j p shifts q₁ ℓ))) := by
  simp only [implicitlyRestartedArnoldi, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Section 10.5.3** of [golub2013matrix], exact semantics of implicitly restarted Arnoldi. Let
$A \in \mathbb{R}^{n \times n}$, let $p \ge 1$, let $q_1 \in \mathbb{R}^n$ be a unit vector, let
$m = j + p + 1$ be at most the grade of $q_1$ for $A$, and let $L \ge 0$. Let
$(Q^{(\ell)}, H^{(\ell)}, r^{(\ell)})$ be the state after $\ell$ cycles, let
$q^{(\ell)} = Q^{(\ell)} e_1$, let $p_\ell$ be the filter polynomial of cycle $\ell$, and let
$\rho_\ell$ be the entry $R(1, 1)$ of the product of its triangular factors. Assume that every
state with $\ell \le L$ has $m$ columns, that is, no continued Arnoldi step breaks down. Then in
exact arithmetic:
* every state with $\ell \le L$ is an $m$-step Arnoldi decomposition $A Q^{(\ell)} = Q^{(\ell)}
  H^{(\ell)} + r^{(\ell)} e_m^T$;
* $q^{(0)} = q_1$;
* $\rho_\ell \, q^{(\ell+1)} = p_\ell(A) q^{(\ell)}$ for every $\ell < L$.

So the first column is, up to the factor $\rho_\ell$, the starting vector that explicit
restarting (10.5.10) would use, obtained without restarting the Arnoldi process from step 1. By
the implicit Q theorem `Matrix.IsArnoldiDecomposition.implicitQ`, an unreduced Arnoldi
decomposition is determined by its first column. -/
theorem implicitlyRestartedArnoldi_spec (A : Matrix (Fin n) (Fin n) ℝ) {j p : ℕ} (hp : 0 < p)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1)
    (hg : j + p + 1 ≤ grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁)) (L : ℕ) :
    let S : ℕ → ArnoldiState n := fun ℓ =>
      Id.run (implicitlyRestartedArnoldi pure A j p shifts q₁ ℓ)
    let H : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ := fun ℓ =>
      (S ℓ).hMatrix (j + p + 1)
    let ρ : ℕ → ℝ := fun ℓ =>
      ((List.range p).reverse.map (Id.run (shiftedQrSteps pure (H ℓ) (shifts (H ℓ)) p)).R).prod
        0 0
    (∀ ℓ ≤ L, (S ℓ).k = j + p + 1) →
      (∀ ℓ ≤ L, IsArnoldiDecomposition A ((S ℓ).qMatrix (j + p + 1)) (H ℓ) (S ℓ).r) ∧
      (S 0).qMatrix (j + p + 1) *ᵥ Pi.single 0 1 = q₁ ∧
      ∀ ℓ < L, ρ ℓ • ((S (ℓ + 1)).qMatrix (j + p + 1) *ᵥ Pi.single 0 1) =
        aeval A (filterPolynomial (shifts (H ℓ)) p) *ᵥ
          ((S ℓ).qMatrix (j + p + 1) *ᵥ Pi.single 0 1) := by
  intro S H ρ hk
  have hsucc : ∀ ℓ, S (ℓ + 1) = Id.run (implicitRestartCycle pure A j p shifts (S ℓ)) :=
    implicitlyRestartedArnoldi_succ A j p shifts q₁
  obtain ⟨-, hQ0, hH0, hr0⟩ := algorithm_10_5_1_matrices A hq hg
  have hS0 : S 0 = Id.run (algorithm_10_5_1 pure A q₁ (j + p + 1)) := by
    simp [S, implicitlyRestartedArnoldi]
  have hdec : ∀ ℓ ≤ L, IsArnoldiDecomposition A ((S ℓ).qMatrix (j + p + 1)) (H ℓ) (S ℓ).r := by
    intro ℓ hℓ
    induction ℓ with
    | zero =>
      simp only [H]
      rw [hS0, hQ0, hH0, hr0 (by omega)]
      exact (equation_10_5_2 A (WithLp.toLp 2 q₁) (k := j + p + 1) (by omega)).2.2 hg
    | succ ℓ ih =>
      have h := implicitRestartCycle_spec A hp shifts (ih (by omega))
      simp only [H] at h ⊢
      rw [hsucc] at ⊢
      exact (h (by rw [← hsucc]; exact hk (ℓ + 1) hℓ)).1
  refine ⟨hdec, by rw [hS0, hQ0]; exact basisMatrix_mulVec_single_zero A hq _, fun ℓ hℓ => ?_⟩
  have h := implicitRestartCycle_spec A hp shifts (hdec ℓ hℓ.le)
  rw [hsucc]
  exact (h (by rw [← hsucc]; exact hk (ℓ + 1) hℓ)).2

/-! ### The unsymmetric Lanczos process (§10.5.5) -/

/-- The state of the unsymmetric Lanczos tridiagonalization (10.5.11): the number $k$ of pairs of
Lanczos vectors computed, the right and the left vectors, the coefficients $\alpha$, $\beta$ and
$\gamma$, the residuals $r_k$ and $\tilde r_k$, and a flag that records that the loop has
stopped. -/
structure UnsymLanczosState (n : ℕ) where
  /-- The step counter $k$ of the source. -/
  k : ℕ
  /-- The right Lanczos vectors: `q j` is the source's $q_{j+1}$. -/
  q : ℕ → Fin n → ℝ
  /-- The left Lanczos vectors: `qt j` is the source's $\tilde q_{j+1}$. -/
  qt : ℕ → Fin n → ℝ
  /-- The diagonal coefficients: `alpha j` is the source's $\alpha_{j+1}$. -/
  alpha : ℕ → ℝ
  /-- The coefficients $\beta_j$, computed at the start of pass $j$, counted from $0$: `beta j` is
  the source's $\beta_j$. -/
  beta : ℕ → ℝ
  /-- The coefficients $\gamma_j$, computed at the start of pass $j$, counted from $0$: `gamma j` is
  the source's $\gamma_j$. -/
  gamma : ℕ → ℝ
  /-- The right residual $r_k$. -/
  r : Fin n → ℝ
  /-- The left residual $\tilde r_k$, the source's $s_k$. -/
  s : Fin n → ℝ
  /-- Whether the loop has stopped because $r_k = 0$, $\tilde r_k = 0$ or $\tilde r_k^T r_k = 0$. -/
  done : Bool

section UnsymProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ}

/-- One pass of the loop of (10.5.11), which does nothing once the loop has stopped:
```
β_k = ‖r_k‖₂,  γ_k = r̃_kᵀ r_k / β_k,  q_{k+1} = r_k/β_k,  q̃_{k+1} = r̃_k/γ_k,  k = k + 1
α_k = q̃_kᵀ A q_k,  r_k = (A − α_k I) q_k − γ_{k−1} q_{k−1}
r̃_k = (A − α_k I)ᵀ q̃_k − β_{k−1} q̃_{k−1}
```
with $q_0 = \tilde q_0 = 0$. The loop test ($r_k \neq 0$, $\tilde r_k \neq 0$ and
$\tilde r_k^T r_k \neq 0$) is evaluated on the computed values at the end of the pass. -/
noncomputable def unsymLanczosStep (A : Matrix (Fin n) (Fin n) ℝ) (st : UnsymLanczosState n) :
    M (UnsymLanczosState n) :=
  if st.done then pure st else do
    let b ← vecNorm rnd st.r
    let sr ← algorithm_1_1_1 rnd st.s st.r
    let g ← rnd (sr / b)
    let q ← vecDiv rnd st.r b
    let qt ← vecDiv rnd st.s g
    let Aq ← algorithm_1_1_3 rnd A q 0
    let a ← algorithm_1_1_1 rnd qt Aq
    let r ← algorithm_1_1_2 rnd (-a) q Aq
    let r ← algorithm_1_1_2 rnd (-g) (if st.k = 0 then 0 else st.q (st.k - 1)) r
    let Atq ← algorithm_1_1_3 rnd Aᵀ qt 0
    let s ← algorithm_1_1_2 rnd (-a) qt Atq
    let s ← algorithm_1_1_2 rnd (-b) (if st.k = 0 then 0 else st.qt (st.k - 1)) s
    let sr' ← algorithm_1_1_1 rnd s r
    pure
      { k := st.k + 1
        q := Function.update st.q st.k q
        qt := Function.update st.qt st.k qt
        alpha := Function.update st.alpha st.k a
        beta := Function.update st.beta st.k b
        gamma := Function.update st.gamma st.k g
        r := r
        s := s
        done := decide (r = 0 ∨ s = 0 ∨ sr' = 0) }

/-- **Equation (10.5.11)** of [golub2013matrix] (unsymmetric Lanczos tridiagonalization), with the
choice $\beta_k = \|r_k\|_2$:
```
q₁, q̃₁ given unit 2-norm vectors with q̃₁ᵀq₁ ≠ 0
k = 0, q_0 = 0, r_0 = q₁, q̃_0 = 0, s_0 = q̃₁
while (r_k ≠ 0) and (r̃_k ≠ 0) and (r̃_kᵀ r_k ≠ 0)
  β_k = ‖r_k‖₂,  γ_k = r̃_kᵀ r_k/β_k,  q_{k+1} = r_k/β_k,  q̃_{k+1} = r̃_k/γ_k,  k = k + 1
  α_k = q̃_kᵀ A q_k,  r_k = (A − α_k I) q_k − γ_{k−1} q_{k−1}
  r̃_k = (A − α_k I)ᵀ q̃_k − β_{k−1} q̃_{k−1}
end
```

The source's $s_0$ is $\tilde r_0$. The loop is at most `fuel` passes of
`GolubVanLoan.Chapter10.unsymLanczosStep`, every arithmetic result passes through the rounding
hook `rnd`, and the entry test is evaluated on $q_1$ and $\tilde q_1$. -/
noncomputable def unsymmetricLanczos (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (fuel : ℕ) : M (UnsymLanczosState n) := do
  let sr ← algorithm_1_1_1 rnd qt₁ q₁
  (List.range fuel).foldlM (fun st _ => unsymLanczosStep rnd A st)
    { k := 0, q := fun _ => 0, qt := fun _ => 0, alpha := fun _ => 0, beta := fun _ => 0,
      gamma := fun _ => 0, r := q₁, s := qt₁, done := decide (q₁ = 0 ∨ qt₁ = 0 ∨ sr = 0) }

end UnsymProgram

/-- **Section 10.5.5** of [golub2013matrix], definition of a serious breakdown. The unsymmetric
Lanczos process has a **serious breakdown** at a state if $r_k \neq 0$ and $\tilde r_k \neq 0$
but $\tilde r_k^T r_k = 0$. Then the tridiagonalization ends without information about an
invariant subspace. -/
def IsSeriousBreakdown {n : ℕ} (st : UnsymLanczosState n) : Prop :=
  st.r ≠ 0 ∧ st.s ≠ 0 ∧ st.s ⬝ᵥ st.r = 0

/-- The tridiagonal matrix $T_k$ of (10.5.12) of the computed coefficients:
$\alpha_1, \dots, \alpha_k$ on the diagonal, $\beta_1, \dots, \beta_{k-1}$ below it and
$\gamma_1, \dots, \gamma_{k-1}$ above it. -/
def unsymTridiag {n : ℕ} (st : UnsymLanczosState n) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then st.alpha i else if (i : ℕ) + 1 = j then st.gamma j
    else if (j : ℕ) + 1 = i then st.beta i else 0

/-- The matrix $Q_k = [q_1 | \cdots | q_k]$ of the computed right Lanczos vectors. -/
def unsymQ {n : ℕ} (st : UnsymLanczosState n) (k : ℕ) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => st.q j i

/-- The matrix $\tilde Q_k = [\tilde q_1 | \cdots | \tilde q_k]$ of the computed left Lanczos
vectors. -/
def unsymQt {n : ℕ} (st : UnsymLanczosState n) (k : ℕ) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => st.qt j i

/-- The exact run with $t + 1$ passes is one pass after the exact run with $t$ passes. -/
private theorem unsymmetricLanczos_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ qt₁ : Fin n → ℝ) (t : ℕ) :
    Id.run (unsymmetricLanczos pure A q₁ qt₁ (t + 1)) =
      Id.run (unsymLanczosStep pure A (Id.run (unsymmetricLanczos pure A q₁ qt₁ t))) := by
  simp only [unsymmetricLanczos, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- The exact run satisfies the three-term relations of every column of (10.5.12) and (10.5.13), and
its flag records the loop test on the current residuals. -/
private theorem unsym_relations {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (t : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ t)
    st.done = decide (st.r = 0 ∨ st.s = 0 ∨ st.s ⬝ᵥ st.r = 0) ∧
    ∀ j < st.k,
      A *ᵥ st.q j = st.gamma j • (if j = 0 then 0 else st.q (j - 1)) + st.alpha j • st.q j +
          (if j + 1 < st.k then st.beta (j + 1) • st.q (j + 1) else st.r) ∧
      Aᵀ *ᵥ st.qt j = st.beta j • (if j = 0 then 0 else st.qt (j - 1)) + st.alpha j • st.qt j +
          (if j + 1 < st.k then st.gamma (j + 1) • st.qt (j + 1) else st.s) := by
  intro st
  let P : UnsymLanczosState n → Prop := fun st =>
    st.done = decide (st.r = 0 ∨ st.s = 0 ∨ st.s ⬝ᵥ st.r = 0) ∧
    ∀ j < st.k,
      A *ᵥ st.q j = st.gamma j • (if j = 0 then 0 else st.q (j - 1)) + st.alpha j • st.q j +
          (if j + 1 < st.k then st.beta (j + 1) • st.q (j + 1) else st.r) ∧
      Aᵀ *ᵥ st.qt j = st.beta j • (if j = 0 then 0 else st.qt (j - 1)) + st.alpha j • st.qt j +
          (if j + 1 < st.k then st.gamma (j + 1) • st.qt (j + 1) else st.s)
  suffices hP : ∀ t, P (Id.run (unsymmetricLanczos pure A q₁ qt₁ t)) from hP t
  intro t
  induction t with
  | zero =>
    refine ⟨by simp [unsymmetricLanczos, algorithm_1_1_1_spec], fun j hj => ?_⟩
    simp [unsymmetricLanczos] at hj
  | succ t ih =>
    rw [unsymmetricLanczos_succ]
    set s0 := Id.run (unsymmetricLanczos pure A q₁ qt₁ t) with hs0
    obtain ⟨hdone, hrel⟩ := ih
    cases hsd : s0.done with
    | true =>
      simp only [unsymLanczosStep, hsd, ↓reduceIte, Id.run_pure]
      exact ⟨hdone, hrel⟩
    | false =>
      have htest : ¬ (s0.r = 0 ∨ s0.s = 0 ∨ s0.s ⬝ᵥ s0.r = 0) := by
        simpa [hsd] using hdone.symm
      push Not at htest
      obtain ⟨hr0, -, hsr⟩ := htest
      have hb : ‖(WithLp.toLp 2 s0.r : EuclideanSpace ℝ (Fin n))‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        intro h
        exact hr0 (by simpa using congrArg WithLp.ofLp h)
      have hg : s0.s ⬝ᵥ s0.r / ‖(WithLp.toLp 2 s0.r : EuclideanSpace ℝ (Fin n))‖ ≠ 0 :=
        div_ne_zero hsr hb
      simp only [P, unsymLanczosStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
        Id.run_pure, vecNorm_spec, algorithm_1_1_1_spec, vecDiv_spec, algorithm_1_1_3_spec,
        algorithm_1_1_2_spec, zero_add]
      refine ⟨by simp, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · -- an old column
        obtain ⟨h1, h2⟩ := hrel j hj
        have hne : j ≠ s0.k := hj.ne
        simp only [Function.update_of_ne hne]
        by_cases hj1 : j + 1 < s0.k
        · have hne1 : j + 1 ≠ s0.k := hj1.ne
          have hne0 : j - 1 ≠ s0.k := by omega
          simp only [Function.update_of_ne hne1, Function.update_of_ne hne0,
            ite_eq_left (show j + 1 < s0.k + 1 by omega), ite_eq_left hj1] at h1 h2 ⊢
          exact ⟨h1, h2⟩
        · have hk : j + 1 = s0.k := by omega
          have hne0 : j - 1 ≠ s0.k := by omega
          simp only [ite_eq_right hj1] at h1 h2
          simp only [Function.update_of_ne hne0, hk, Function.update_self]
          refine ⟨?_, ?_⟩
          · rw [h1, smul_smul, mul_inv_cancel₀ hb, one_smul, ite_eq_left (lt_add_one s0.k)]
          · rw [h2, smul_smul, mul_inv_cancel₀ hg, one_smul, ite_eq_left (lt_add_one s0.k)]
      · -- the new column
        simp only [Function.update_self, ite_eq_right (show ¬ s0.k + 1 < s0.k + 1 by omega)]
        refine ⟨?_, ?_⟩
        · by_cases h0 : s0.k = 0
          · simp only [h0, ↓reduceIte]
            module
          · simp only [h0, ↓reduceIte, Function.update_of_ne (show s0.k - 1 ≠ s0.k by omega)]
            module
        · by_cases h0 : s0.k = 0
          · simp only [h0, ↓reduceIte]
            module
          · simp only [h0, ↓reduceIte, Function.update_of_ne (show s0.k - 1 ≠ s0.k by omega)]
            module

/-- The matrix $T_k$ is `Matrix.tridiagonalOfNat` of $\alpha$, $\beta$ and the shifted sequence of
$\gamma$. -/
private theorem unsymTridiag_eq {n : ℕ} (st : UnsymLanczosState n) (k : ℕ) :
    unsymTridiag st k =
      Matrix.tridiagonalOfNat st.alpha st.beta (fun i => st.gamma (i + 1)) k := by
  ext i j
  simp only [unsymTridiag, Matrix.tridiagonalOfNat, Matrix.of_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- The matrix $T_k^T$ is `Matrix.tridiagonalOfNat` of $\alpha$, $\gamma$ and the shifted sequence
of $\beta$. -/
private theorem unsymTridiag_transpose {n : ℕ} (st : UnsymLanczosState n) (k : ℕ) :
    (unsymTridiag st k)ᵀ =
      Matrix.tridiagonalOfNat st.alpha st.gamma (fun i => st.beta (i + 1)) k := by
  ext i j
  simp only [Matrix.transpose_apply, unsymTridiag, Matrix.tridiagonalOfNat, Matrix.of_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega) | congr 1

/-- **Equation (10.5.12)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$q_1, \tilde q_1 \in \mathbb{R}^n$, and consider the exact run of (10.5.11), which ends after
$k$ passes. Then
$$A Q_k = Q_k T_k + r_k e_k^T,$$
where $Q_k = [q_1 | \cdots | q_k]$ and $T_k$ is the tridiagonal matrix of the computed $\alpha$,
$\beta$ and $\gamma$.

No hypothesis on $q_1$ and $\tilde q_1$ is needed. The proof works column by column from the
recurrence, with `Matrix.tridiagonalOfNat_mulVec`. -/
theorem equation_10_5_12 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (fuel : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ fuel)
    A * unsymQ st st.k = unsymQ st st.k * unsymTridiag st st.k +
      Matrix.vecMulVec st.r (Krylov.lastVec (1 : ℝ) st.k) := by
  intro st
  have hrel : ∀ j < st.k,
      A *ᵥ st.q j = st.gamma j • (if j = 0 then 0 else st.q (j - 1)) + st.alpha j • st.q j +
          (if j + 1 < st.k then st.beta (j + 1) • st.q (j + 1) else st.r) :=
    fun j hj => ((unsym_relations A q₁ qt₁ fuel).2 j hj).1
  ext x j
  have h := congrFun (hrel j j.isLt) x
  rw [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mul_apply]
  rw [show (∑ l, A x l * unsymQ st st.k l j) = (A *ᵥ st.q j) x from rfl, h,
    show (∑ l, unsymQ st st.k x l * unsymTridiag st st.k l j)
      = ((fun l : Fin st.k => st.q l x) ᵥ* unsymTridiag st st.k) j from rfl,
    ← Matrix.transpose_transpose (unsymTridiag st st.k), unsymTridiag_transpose,
    Matrix.vecMul_transpose, Matrix.tridiagonalOfNat_mulVec]
  simp only [Krylov.lastVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
  · by_cases h1 : 1 < st.k
    · simp [h0, h1, show (1 : ℕ) ≠ st.k by omega]
    · simp [h0, show st.k = 1 by omega]
  · by_cases h1 : (j : ℕ) + 1 < st.k
    · simp [h0.ne', h1, show (j : ℕ) + 1 ≠ st.k by omega]
    · simp [h0.ne', show (j : ℕ) + 1 = st.k by omega]

/-- **Equation (10.5.13)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$q_1, \tilde q_1 \in \mathbb{R}^n$, and consider the exact run of (10.5.11), which ends after
$k$ passes. Then
$$A^T \tilde Q_k = \tilde Q_k T_k^T + \tilde r_k e_k^T,$$
where $\tilde Q_k = [\tilde q_1 | \cdots | \tilde q_k]$.

The proof works column by column from the recurrence for $\tilde q_j$, with
`Matrix.tridiagonalOfNat_mulVec`. -/
theorem equation_10_5_13 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (fuel : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ fuel)
    Aᵀ * unsymQt st st.k = unsymQt st st.k * (unsymTridiag st st.k)ᵀ +
      Matrix.vecMulVec st.s (Krylov.lastVec (1 : ℝ) st.k) := by
  intro st
  have hrel : ∀ j < st.k,
      Aᵀ *ᵥ st.qt j = st.beta j • (if j = 0 then 0 else st.qt (j - 1)) + st.alpha j • st.qt j +
          (if j + 1 < st.k then st.gamma (j + 1) • st.qt (j + 1) else st.s) :=
    fun j hj => ((unsym_relations A q₁ qt₁ fuel).2 j hj).2
  ext x j
  have h := congrFun (hrel j j.isLt) x
  rw [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mul_apply]
  rw [show (∑ l, Aᵀ x l * unsymQt st st.k l j) = (Aᵀ *ᵥ st.qt j) x from rfl, h,
    show (∑ l, unsymQt st st.k x l * (unsymTridiag st st.k)ᵀ l j)
      = ((fun l : Fin st.k => st.qt l x) ᵥ* (unsymTridiag st st.k)ᵀ) j from rfl,
    Matrix.vecMul_transpose, unsymTridiag_eq, Matrix.tridiagonalOfNat_mulVec]
  simp only [Krylov.lastVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
  · by_cases h1 : 1 < st.k
    · simp [h0, h1, show (1 : ℕ) ≠ st.k by omega]
    · simp [h0, show st.k = 1 by omega]
  · by_cases h1 : (j : ℕ) + 1 < st.k
    · simp [h0.ne', h1, show (j : ℕ) + 1 ≠ st.k by omega]
    · simp [h0.ne', show (j : ℕ) + 1 = st.k by omega]

/-- The exact run of (10.5.11) keeps $\tilde q_a^T q_a = 1$ and $\alpha_a = \tilde q_a^T A q_a$, its
computed $\beta$ and $\gamma$ are nonzero, and its first vectors are nonzero multiples of $q_1$
and $\tilde q_1$. -/
private theorem unsym_normalized {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (t : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ t)
    (∀ a < st.k, st.qt a ⬝ᵥ st.q a = 1 ∧ st.alpha a = st.qt a ⬝ᵥ A *ᵥ st.q a ∧
      st.beta a ≠ 0 ∧ st.gamma a ≠ 0) ∧
    (st.k = 0 → st.r = q₁ ∧ st.s = qt₁) ∧
    (0 < st.k → st.q 0 = (st.beta 0)⁻¹ • q₁ ∧ st.qt 0 = (st.gamma 0)⁻¹ • qt₁) := by
  intro st
  let P : UnsymLanczosState n → Prop := fun st =>
    (∀ a < st.k, st.qt a ⬝ᵥ st.q a = 1 ∧ st.alpha a = st.qt a ⬝ᵥ A *ᵥ st.q a ∧
      st.beta a ≠ 0 ∧ st.gamma a ≠ 0) ∧
    (st.k = 0 → st.r = q₁ ∧ st.s = qt₁) ∧
    (0 < st.k → st.q 0 = (st.beta 0)⁻¹ • q₁ ∧ st.qt 0 = (st.gamma 0)⁻¹ • qt₁)
  suffices hP : ∀ t, P (Id.run (unsymmetricLanczos pure A q₁ qt₁ t)) from hP t
  intro t
  induction t with
  | zero =>
    refine ⟨fun a ha => ?_, fun _ => ?_, fun h => ?_⟩ <;> simp [unsymmetricLanczos] at *
  | succ t ih =>
    have hdone := (unsym_relations A q₁ qt₁ t).1
    rw [unsymmetricLanczos_succ]
    set s0 := Id.run (unsymmetricLanczos pure A q₁ qt₁ t) with hs0
    obtain ⟨I1, I5, I6⟩ := ih
    cases hsd : s0.done with
    | true =>
      simp only [unsymLanczosStep, hsd, ↓reduceIte, Id.run_pure]
      exact ⟨I1, I5, I6⟩
    | false =>
      have htest : ¬ (s0.r = 0 ∨ s0.s = 0 ∨ s0.s ⬝ᵥ s0.r = 0) := by
        simpa [hsd] using hdone.symm
      push Not at htest
      obtain ⟨hr0, -, hsr⟩ := htest
      simp only [P, unsymLanczosStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
        Id.run_pure, vecNorm_spec, algorithm_1_1_1_spec, vecDiv_spec, algorithm_1_1_3_spec,
        algorithm_1_1_2_spec, zero_add]
      set β := ‖(WithLp.toLp 2 s0.r : EuclideanSpace ℝ (Fin n))‖ with hβ
      have hβ0 : β ≠ 0 := by
        rw [hβ, norm_ne_zero_iff]
        intro h
        exact hr0 (by simpa using congrArg WithLp.ofLp h)
      set γ := s0.s ⬝ᵥ s0.r / β with hγ
      have hγ0 : γ ≠ 0 := div_ne_zero hsr hβ0
      have hnn : (γ⁻¹ • s0.s) ⬝ᵥ (β⁻¹ • s0.r) = 1 := by
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hγ]
        field_simp
      refine ⟨fun a ha => ?_, fun h => by omega, fun _ => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · simp only [Function.update_of_ne ha.ne]
          exact I1 a ha
        · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_self]
          · exact hnn
          · exact hβ0
          · exact hγ0
      · rcases Nat.eq_zero_or_pos s0.k with h0 | h0
        · obtain ⟨hr, hs⟩ := I5 h0
          rw [← h0, Function.update_self, Function.update_self, Function.update_self,
            Function.update_self, hr, hs]
          exact ⟨rfl, rfl⟩
        · simp only [Function.update_of_ne h0.ne]
          exact I6 h0

/-- The exact run of (10.5.11) is biorthogonal: $\tilde q_a^T q_b = \delta_{ab}$ and
$\tilde q_a^T r_k = 0$. -/
private theorem unsym_biorth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (t : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ t)
    (∀ a < st.k, ∀ b < st.k, st.qt a ⬝ᵥ st.q b = if a = b then 1 else 0) ∧
    (∀ a < st.k, st.qt a ⬝ᵥ st.r = 0) := by
  intro st
  have N := (unsym_normalized A q₁ qt₁ t).1
  have hrel := (unsym_relations A q₁ qt₁ t).2
  -- the two families, closed by the residuals
  set v : ℕ → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (Function.update st.q st.k st.r j)
    with hv
  set w : ℕ → EuclideanSpace ℝ (Fin n) :=
    fun j => WithLp.toLp 2 (Function.update st.qt st.k st.s j) with hw
  have hvo : ∀ j < st.k, v j = WithLp.toLp 2 (st.q j) := fun j hj => by
    simp only [hv, Function.update_of_ne hj.ne]
  have hwo : ∀ j < st.k, w j = WithLp.toLp 2 (st.qt j) := fun j hj => by
    simp only [hw, Function.update_of_ne hj.ne]
  have hvk : v st.k = WithLp.toLp 2 st.r := by simp only [hv, Function.update_self]
  have hwk : w st.k = WithLp.toLp 2 st.s := by simp only [hw, Function.update_self]
  have hvp : ∀ j < st.k, (if j = 0 then 0 else v (j - 1)) =
      WithLp.toLp 2 (if j = 0 then 0 else st.q (j - 1)) := fun j hj => by
    split_ifs
    · simp
    · rw [hvo _ (by omega)]
  have hwp : ∀ j < st.k, (if j = 0 then 0 else w (j - 1)) =
      WithLp.toLp 2 (if j = 0 then 0 else st.qt (j - 1)) := fun j hj => by
    split_ifs
    · simp
    · rw [hwo _ (by omega)]
  set β' := Function.update st.beta st.k 1 with hβ'
  set γ' := Function.update st.gamma st.k 1 with hγ'
  have hvn : ∀ j < st.k, β' (j + 1) • v (j + 1) =
      WithLp.toLp 2 (if j + 1 < st.k then st.beta (j + 1) • st.q (j + 1) else st.r) := by
    intro j hj
    by_cases hj1 : j + 1 < st.k
    · rw [hβ', Function.update_of_ne hj1.ne, hvo _ hj1, ite_eq_left hj1, WithLp.toLp_smul]
    · rw [show j + 1 = st.k by omega, hβ', Function.update_self, one_smul, hvk,
        ite_eq_right (lt_irrefl _)]
  have hwn : ∀ j < st.k, γ' (j + 1) • w (j + 1) =
      WithLp.toLp 2 (if j + 1 < st.k then st.gamma (j + 1) • st.qt (j + 1) else st.s) := by
    intro j hj
    by_cases hj1 : j + 1 < st.k
    · rw [hγ', Function.update_of_ne hj1.ne, hwo _ hj1, ite_eq_left hj1, WithLp.toLp_smul]
    · rw [show j + 1 = st.k by omega, hγ', Function.update_self, one_smul, hwk,
        ite_eq_right (lt_irrefl _)]
  have hinner := EuclideanSpace.inner_toLp_toLp_real (ι := Fin n)
  obtain ⟨I1, I2, -⟩ := BiLanczos.inner_eq_ite_of_threeTerm (A := Matrix.toEuclideanLin A)
    (B := Matrix.toEuclideanLin Aᵀ)
    (LinearMap.isAdjointPair_inner_iff'.2 fun x y =>
      (Matrix.toEuclideanLin_transpose_inner_right A x y).symm)
    (v := v) (w := w) (α := st.alpha) (β := β') (γ := γ') (m := st.k)
    (fun j hj => by
      rw [hvo j hj, hvp j hj, hvn j hj, hγ', Function.update_of_ne hj.ne,
        Matrix.toEuclideanLin_toLp, (hrel j hj).1, WithLp.toLp_add, WithLp.toLp_add,
        WithLp.toLp_smul, WithLp.toLp_smul])
    (fun j hj => by
      rw [hwo j hj, hwp j hj, conj_trivial, conj_trivial, conj_trivial, hwn j hj, hβ',
        Function.update_of_ne hj.ne, Matrix.toEuclideanLin_toLp, (hrel j hj).2,
        WithLp.toLp_add, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul])
    (fun j hj => by
      rw [hwo j hj, hvo j hj, Matrix.toEuclideanLin_toLp, hinner, (N j hj).2.1])
    (fun j hj => by rw [hwo j hj, hvo j hj, hinner, (N j hj).1])
    (fun j hj => by
      by_cases hj1 : j + 1 < st.k
      · rw [hβ', Function.update_of_ne hj1.ne]; exact (N _ hj1).2.2.1
      · rw [show j + 1 = st.k by omega, hβ', Function.update_self]; exact one_ne_zero)
    (fun j hj => by
      by_cases hj1 : j + 1 < st.k
      · rw [hγ', Function.update_of_ne hj1.ne]; exact (N _ hj1).2.2.2
      · rw [show j + 1 = st.k by omega, hγ', Function.update_self]; exact one_ne_zero)
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have h := I1 a ha b hb
    rwa [hwo a ha, hvo b hb, hinner] at h
  · have h := I2 a ha
    rwa [hwo a ha, hvk, hinner] at h

/-- A three-term recurrence spans the Krylov subspaces: if $v_0$ is a nonzero multiple of $w$ and $B
v_a = c^{(1)}_a v_{a-1} + c^{(2)}_a v_a + c^{(3)}_{a+1} v_{a+1}$ with $c^{(3)}_{a+1} \neq 0$ for
$a + 1 < k$, then $\operatorname{span}\{v_0, \dots, v_{j-1}\} = \mathcal{K}(B, w, j)$ for
$j \le k$. -/
private theorem span_eq_subspace_of_threeTerm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (v : ℕ → Fin n → ℝ) (v₁ : Fin n → ℝ) (k : ℕ) (c c₁ c₂ c₃ : ℕ → ℝ)
    (h0 : 0 < k → v 0 = c 0 • v₁ ∧ c 0 ≠ 0)
    (hrel : ∀ a, a + 1 < k → B *ᵥ v a =
      c₁ a • (if a = 0 then 0 else v (a - 1)) + c₂ a • v a + c₃ (a + 1) • v (a + 1))
    (hne : ∀ a < k, c₃ a ≠ 0) :
    ∀ j ≤ k, Submodule.span ℝ (Set.range fun i : Fin j =>
        (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n))) =
      Krylov.subspace (Matrix.toEuclideanLin B) (WithLp.toLp 2 v₁) j :=
  Krylov.span_eq_subspace_of_threeTerm (Matrix.toEuclideanLin B) (fun i => WithLp.toLp 2 (v i))
    (WithLp.toLp 2 v₁) k (c 0) c₁ c₂ c₃
    (fun hk => ⟨by rw [(h0 hk).1, WithLp.toLp_smul], (h0 hk).2⟩)
    (fun a ha => by
      rw [Matrix.toEuclideanLin_toLp, hrel a ha]
      split_ifs <;> simp only [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_zero])
    hne
/-- **Equation (10.5.11)** of [golub2013matrix], exact semantics. Let
$A \in \mathbb{R}^{n \times n}$ and $q_1, \tilde q_1 \in \mathbb{R}^n$, and consider the exact
run of (10.5.11), which ends after $k$ passes. Then:
* the computed vectors are biorthonormal, $\tilde Q_k^T Q_k = I_k$;
* they span Krylov subspaces: $\operatorname{span}\{q_1, \dots, q_j\} = \mathcal{K}(A, q_1, j)$
  and $\operatorname{span}\{\tilde q_1, \dots, \tilde q_j\} = \mathcal{K}(A^T, \tilde q_1, j)$
  for $j \le k$;
* $\tilde Q_k^T A Q_k = T_k$, the tridiagonal matrix of the computed $\alpha$, $\beta$ and
  $\gamma$.

No hypothesis on $q_1$ and $\tilde q_1$ is needed: the loop stops at a breakdown, so every
executed pass had $r_k \neq 0$, $\tilde r_k \neq 0$ and $\tilde r_k^T r_k \neq 0$. The proof
uses the recurrences (10.5.12)–(10.5.13). The biorthogonality is
`BiLanczos.inner_eq_ite_of_threeTerm`, which allows the source's normalization
$\beta_k = \|r_k\|_2$ as well as the normalization $\delta_{j+1} = |\langle \hat w, \hat v
\rangle|^{1/2}$ of `Numlib.Krylov.BiLanczos`. -/
theorem equation_10_5_11 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (fuel : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ fuel)
    (unsymQt st st.k)ᵀ * unsymQ st st.k = 1 ∧
      (∀ j ≤ st.k, Submodule.span ℝ (Set.range fun i : Fin j =>
          (WithLp.toLp 2 (st.q i) : EuclideanSpace ℝ (Fin n))) =
        Krylov.subspace (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) j) ∧
      (∀ j ≤ st.k, Submodule.span ℝ (Set.range fun i : Fin j =>
          (WithLp.toLp 2 (st.qt i) : EuclideanSpace ℝ (Fin n))) =
        Krylov.subspace (Matrix.toEuclideanLin Aᵀ) (WithLp.toLp 2 qt₁) j) ∧
      (unsymQt st st.k)ᵀ * A * unsymQ st st.k = unsymTridiag st st.k := by
  intro st
  obtain ⟨I1, I2⟩ := unsym_biorth A q₁ qt₁ fuel
  obtain ⟨N, -, I6⟩ := unsym_normalized A q₁ qt₁ fuel
  have I4 : ∀ a < st.k, st.beta a ≠ 0 ∧ st.gamma a ≠ 0 := fun a ha => ⟨(N a ha).2.2.1,
    (N a ha).2.2.2⟩
  have hrel := (unsym_relations A q₁ qt₁ fuel).2
  have hQQ : (unsymQt st st.k)ᵀ * unsymQ st st.k = 1 := by
    ext a b
    have := I1 a a.isLt b b.isLt
    simp only [Matrix.mul_apply, Matrix.transpose_apply, unsymQt, unsymQ, Matrix.of_apply,
      Matrix.one_apply, Fin.ext_iff]
    exact this
  refine ⟨hQQ, span_eq_subspace_of_threeTerm A st.q q₁ st.k (fun _ => (st.beta 0)⁻¹)
    st.gamma st.alpha st.beta (fun hk => ⟨(I6 hk).1, inv_ne_zero (I4 0 hk).1⟩)
    (fun a ha => by
      have h := (hrel a (Nat.lt_of_succ_lt ha)).1
      rwa [ite_eq_left ha] at h) (fun a ha => (I4 a ha).1),
    span_eq_subspace_of_threeTerm Aᵀ st.qt qt₁ st.k (fun _ => (st.gamma 0)⁻¹)
    st.beta st.alpha st.gamma (fun hk => ⟨(I6 hk).2, inv_ne_zero (I4 0 hk).2⟩)
    (fun a ha => by
      have h := (hrel a (Nat.lt_of_succ_lt ha)).2
      rwa [ite_eq_left ha] at h) (fun a ha => (I4 a ha).2), ?_⟩
  have h12 := equation_10_5_12 A q₁ qt₁ fuel
  have hQr : (unsymQt st st.k)ᵀ *ᵥ st.r = 0 := by
    ext a
    have := I2 a a.isLt
    simpa [Matrix.mulVec, dotProduct, unsymQt] using this
  rw [Matrix.mul_assoc, h12, Matrix.mul_add, ← Matrix.mul_assoc, hQQ, Matrix.one_mul,
    Matrix.mul_vecMulVec, hQr, Matrix.zero_vecMulVec, add_zero]


/-- **Section 10.5.5** of [golub2013matrix], termination with an invariant subspace. Let
$A \in \mathbb{R}^{n \times n}$ and $q_1, \tilde q_1 \in \mathbb{R}^n$, and consider the exact
run of (10.5.11), which ends after $k$ passes. If $r_k = 0$, then
$\operatorname{span}\{q_1, \dots, q_k\}$ is invariant under $A$: $A Q_k y = Q_k (T_k y)$ for
every $y \in \mathbb{R}^k$. If $\tilde r_k = 0$, then $\operatorname{span}\{\tilde q_1, \dots,
\tilde q_k\}$ is invariant under $A^T$: $A^T \tilde Q_k y = \tilde Q_k (T_k^T y)$ for every
$y \in \mathbb{R}^k$.

The proof uses (10.5.12)–(10.5.13), which give $A Q_k = Q_k T_k$ and
$A^T \tilde Q_k = \tilde Q_k T_k^T$ in these cases. -/
theorem unsymmetricLanczos_invariant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ qt₁ : Fin n → ℝ) (fuel : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ fuel)
    (st.r = 0 → ∀ y : Fin st.k → ℝ, A *ᵥ (unsymQ st st.k *ᵥ y) =
      unsymQ st st.k *ᵥ (unsymTridiag st st.k *ᵥ y)) ∧
    (st.s = 0 → ∀ y : Fin st.k → ℝ, Aᵀ *ᵥ (unsymQt st st.k *ᵥ y) =
      unsymQt st st.k *ᵥ ((unsymTridiag st st.k)ᵀ *ᵥ y)) := by
  intro st
  refine ⟨fun hr y => ?_, fun hs y => ?_⟩
  · have h := equation_10_5_12 A q₁ qt₁ fuel
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, hr, Matrix.zero_vecMulVec, add_zero]
  · have h := equation_10_5_13 A q₁ qt₁ fuel
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, hs, Matrix.zero_vecMulVec, add_zero]

end GolubVanLoan.Chapter10
