/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Krylov.Bidiagonalization
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub and Van Loan, Section 10.4: Large sparse SVD frameworks

This module formalizes §10.4 of [golub2013matrix], which reduces the singular value problem for a
large sparse $A \in \mathbb{R}^{m \times n}$ to bidiagonal form. For $m \ge n$ there are orthogonal
$U$ and $V$ such that $U^T A V = B$ is upper bidiagonal (10.4.1). The columns of $AV = UB$ and
$A^T U = V B^T$ give the Golub–Kahan recurrences (10.4.2)–(10.4.3),
$$A v_k = \alpha_k u_k + \beta_{k-1} u_{k-1}, \qquad A^T u_k = \alpha_k v_k + \beta_k v_{k+1}.$$
Run from a unit vector $v_c$ (Algorithm 10.4.1), they produce $V_k = [v_1 | \cdots | v_k]$,
$U_k = [u_1 | \cdots | u_k]$ and the upper bidiagonal $B_k$ of (10.4.8) with $A V_k = U_k B_k$ and
$A^T U_k = V_k B_k^T + p_k e_k^T$ (10.4.9)–(10.4.10). The columns of $V_k$ and $U_k$ span the Krylov
subspaces $\mathcal{K}(A^T A, v_c, k)$ and $\mathcal{K}(A A^T, A v_c, k)$, and $B_k^T B_k$ is the
Lanczos tridiagonal matrix of $A^T A$, so that the singular values of $B_k$ approximate singular
values of $A$.

The module also formalizes the Ritz approximations (10.4.13)–(10.4.15), the tridiagonal–bidiagonal
connection of §10.4.3, the Paige–Saunders lower bidiagonalization (10.4.18)–(10.4.19) with Algorithm
10.4.2, the truncated SVD as a best approximation of rank $k$ (10.4.20), and the identities
(10.4.22)–(10.4.24) behind the CUR approximation of §10.4.5. The proofs specialize the Golub–Kahan
process of `Numlib.Krylov.Bidiagonalization` and the SVD results of
`Numlib.LinearAlgebra.Matrix.SVD` and `Numlib.Analysis.Matrix.SingularValues`.

## Main definitions

* Algorithm 10.4.1, `GolubVanLoan.Chapter10.algorithm_10_4_1`: Golub–Kahan bidiagonalization, as a
  program with a rounding hook.
* Algorithm 10.4.2, `GolubVanLoan.Chapter10.algorithm_10_4_2`: Paige–Saunders lower
  bidiagonalization, as a program with a rounding hook.

## Main results

* Equation (10.4.1), `GolubVanLoan.Chapter10.equation_10_4_1`: for $m \ge n$ there are orthogonal
  $U$, $V$ with $U^T A V$ upper bidiagonal, and $U^T A V$ has the singular values of $A$.
* Equation (10.4.2), `GolubVanLoan.Chapter10.equation_10_4_2`:
  $A v_k = \alpha_k u_k + \beta_{k-1} u_{k-1}$, column $k$ of $AV = UB$.
* Equation (10.4.3), `GolubVanLoan.Chapter10.equation_10_4_3`:
  $A^T u_k = \alpha_k v_k + \beta_k v_{k+1}$, column $k$ of $A^T U = V B^T$.
* Equation (10.4.6), `GolubVanLoan.Chapter10.equation_10_4_6`: $A V(:, 1:k) = U(:, 1:k) B(1:k, 1:k)$
  for every $k \le n$.
* Equation (10.4.7), `GolubVanLoan.Chapter10.equation_10_4_7`: if $\beta_k = 0$, then
  $A^T A V(:, 1:k) = V(:, 1:k) B_k^T B_k$ with $B_k = B(1:k, 1:k)$.
* §10.4.1, `GolubVanLoan.Chapter10.singularValues_bidiag_subset`: if $\beta_k = 0$, every singular
  value of $B(1:k, 1:k)$ is a singular value of $A$.
* Algorithm 10.4.1, `GolubVanLoan.Chapter10.algorithm_10_4_1_spec`: in exact arithmetic the
  algorithm computes the Golub–Kahan vectors and coefficients.
* Equation (10.4.9), `GolubVanLoan.Chapter10.equation_10_4_9`: $A V_k = U_k B_k$.
* Equation (10.4.10), `GolubVanLoan.Chapter10.equation_10_4_10`: $A^T U_k = V_k B_k^T + p_k e_k^T$
  with $p_k = \beta_k v_{k+1}$.
* Equation (10.4.11), `GolubVanLoan.Chapter10.equation_10_4_11`: $\operatorname{span}\{v_1, \dots,
  v_k\} = \mathcal{K}(A^T A, v_c, k)$.
* Equation (10.4.12), `GolubVanLoan.Chapter10.equation_10_4_12`: $\operatorname{span}\{u_1, \dots,
  u_k\} = \mathcal{K}(A A^T, A v_c, k)$.
* §10.4.1, `GolubVanLoan.Chapter10.bidiag_transpose_mul_bidiag`: $B_k^T B_k$ is the Lanczos
  tridiagonal matrix of $A^T A$ from $v_c$.
* Equation (10.4.14), `GolubVanLoan.Chapter10.equation_10_4_14`: an SVD $F_k^T B_k G_k = \Gamma$
  gives $A Y_k = Z_k \Gamma$ for $Y_k = V_k G_k$ and $Z_k = U_k F_k$.
* Equation (10.4.15), `GolubVanLoan.Chapter10.equation_10_4_15`:
  $A^T Z_k = Y_k \Gamma + p_k e_k^T F_k$.
* §10.4.2, `GolubVanLoan.Chapter10.isRitzPair_gram`: $(\gamma_i^2, y_i)$ is a Ritz pair of $A^T A$
  with respect to $\mathcal{K}(A^T A, v_c, k)$.
* §10.4.3, `GolubVanLoan.Chapter10.lanczos_jordanWielandt`: the Lanczos process of the
  Jordan–Wielandt matrix of $A$ has zero diagonal and off-diagonal
  $\alpha_1, \beta_1, \alpha_2, \beta_2, \dots$.
* Equation (10.4.18), `GolubVanLoan.Chapter10.equation_10_4_18`: there are orthogonal $U$, $V$ with
  $U^T A V$ lower bidiagonal.
* Algorithm 10.4.2, `GolubVanLoan.Chapter10.algorithm_10_4_2_spec`: in exact arithmetic the
  algorithm is the Golub–Kahan process of $A^T$ from $u_c$.
* Equation (10.4.19), `GolubVanLoan.Chapter10.equation_10_4_19`: $A V(:, 1:k) = U(:, 1:k) B(1:k,
  1:k) + p_k e_k^T$ for the lower bidiagonalization.
* Equation (10.4.20), `GolubVanLoan.Chapter10.equation_10_4_20`: the truncated SVD $\tilde A_k$
  equals $Z_1 Z_1^T A$, has rank $k$, and is a closest matrix of rank at most $k$ in the 2-norm.
* Equation (10.4.20), `GolubVanLoan.Chapter10.equation_10_4_20_frobenius`: $\tilde A_k$ is a closest
  matrix of rank at most $k$ in the Frobenius norm.
* Equation (10.4.22), `GolubVanLoan.Chapter10.equation_10_4_22`: $C \Phi = Z_1 \Sigma_1^{-1} Y_1^T$
  for $\Phi = Y_1 \Sigma_1^{-2} Y_1^T$.
* Equation (10.4.23), `GolubVanLoan.Chapter10.equation_10_4_23`: the SVD of $C$ substituted in the
  selected rows of $\Psi^T R$.
* Equation (10.4.24), `GolubVanLoan.Chapter10.equation_10_4_24`: $C U R = Z_1 (D_R Z_1(\mathrm{row},
  :))^T D_R A(\mathrm{row}, :)$ for $U = \Phi \Psi^T$.

## Conventions

* $A \in \mathbb{R}^{m \times n}$ is `A : Matrix (Fin m) (Fin n) ℝ`, and indices are 0-based. A
  submatrix $X(:, 1:k)$ is `X.submatrix id (Fin.castLE _)`.
* The Golub–Kahan vectors are defined from the starting vector $v_c$ by Gram–Schmidt
  orthonormalization of Krylov sequences: $v_1, v_2, \dots$ are the Arnoldi vectors of $A^T A$ from
  $v_c$, and $u_1, u_2, \dots$ are the Arnoldi vectors of $A A^T$ from $A v_c$. The coefficients are
  $\alpha_j = u_j^T A v_j$ and $\beta_j = v_{j+1}^T A^T u_j$. Hence $v_1 = v_c / \|v_c\|_2$, and the
  identities do not need $\|v_c\|_2 = 1$. After a breakdown the vectors and the coefficients are
  $0$.
* With `T = Matrix.toEuclideanLin A` and `Ts = Matrix.toEuclideanLin Aᵀ`, the source's $v_{j+1}$,
  $u_{j+1}$, $\alpha_{j+1}$, $\beta_{j+1}$ are `GolubKahan.rightVec T Ts v j`,
  `GolubKahan.leftVec T Ts v j`, `GolubKahan.alpha T Ts v j` and `GolubKahan.beta T Ts v j`. The
  matrices $V_k$, $U_k$, $B_k$ are `GolubKahan.rightMatrix A v k`, `GolubKahan.leftMatrix A v k` and
  `GolubKahan.bidiag T Ts v k`.
* The Krylov subspace $\mathcal{K}(M, x, k) = \operatorname{span}\{x, Mx, \dots, M^{k-1}x\}$ is
  `Krylov.subspace (Matrix.toEuclideanLin M) x k`. The grade of $x$ for $M$ is the dimension of
  $\bigcup_k \mathcal{K}(M, x, k)$, `Krylov.grade`.
* The Paige–Saunders lower bidiagonalization of $A$ from $u_c$ (Algorithm 10.4.2) is the Golub–Kahan
  process of $A^T$ from $u_c$.

## Implementation notes

* Algorithms 10.4.1 and 10.4.2 are one loop, `GolubVanLoan.Chapter10.bidiagLoop`, for the pairs
  $(A, A^T)$ and $(A^T, A)$, with the state `GolubVanLoan.Chapter10.BidiagState`. Every arithmetic
  result passes through the rounding hook `rnd`, and the `while` loop is at most `fuel` passes.

## Deviations from the source

* **Algorithms 10.4.1–10.4.2, zero normalization coefficients** (reading). The exact results
  identify the totalized vectors and coefficients. A zero normalization coefficient can give a
  zero vector. For Algorithm 10.4.2 this can occur even when the leading square block is
  nonsingular. See `GolubVanLoan.Chapter10.bidiagLoop_spec` and
  `GolubVanLoan.Chapter10.algorithm_10_4_2_spec`.
* **§10.4.5, CUR product** (correction). Equation (10.4.24) also needs the transpose on $D_R
  Z_1(\mathrm{row},:)$. See `GolubVanLoan.Chapter10.equation_10_4_24`.
* **Equation (10.4.6)** (typo). The source prints $A U(:, 1:k) = V(:, 1:k) B(1:k, 1:k)$, with $U$
  and $V$ exchanged. See `GolubVanLoan.Chapter10.equation_10_4_6`.
* **Equation (10.4.6)** (generalization). The source attributes the identity to $\beta_k = 0$. It
  holds for every $k \le n$. See `GolubVanLoan.Chapter10.equation_10_4_6`.
* **Equation (10.4.7)** (typo). The source prints $A^T V(:, 1:k) = U(:, 1:k) B(1:k, 1:k)^T$, with
  $U$ and $V$ exchanged. See `GolubVanLoan.Chapter10.equation_10_4_7`.
* **Algorithm 10.4.1** (generalization). The source assumes that $A$ has full column rank. The exact
  semantics holds for every $A$; full column rank only makes every $\alpha_j$ positive. See
  `GolubVanLoan.Chapter10.algorithm_10_4_1_spec`.
* **§10.4.2, Ritz pairs of $A^T A$** (correction). The source prints
  $A^T A y_i = \gamma_i^2 z_i + [F_k]_{ki} p_k$. The identity is $A^T A y_i = \gamma_i^2 y_i +
  \gamma_i [F_k]_{ki} p_k$. See `GolubVanLoan.Chapter10.isRitzPair_gram`.
* **§10.4.2, Ritz pairs of $A^T A$** (reading). The source names the Ritz pair $\{\gamma_i, y_i\}$.
  The Ritz value of $A^T A$ is $\gamma_i^2$. See `GolubVanLoan.Chapter10.isRitzPair_gram`.
* **Algorithm 10.4.2** (typo). The source states $u_c \in \mathbb{R}^n$. The starting vector is
  $u_c \in \mathbb{R}^m$. See `GolubVanLoan.Chapter10.algorithm_10_4_2`.
* **Algorithm 10.4.2** (generalization). The source assumes that $A(1:n, 1:n)$ is nonsingular. The
  exact semantics holds for every $A$. See `GolubVanLoan.Chapter10.algorithm_10_4_2_spec`.
* **Equation (10.4.24)** (typo). The source prints $(C\Phi)(\Psi R)$. The product is
  $(C\Phi)(\Psi^T R)$, as in (10.4.23). See `GolubVanLoan.Chapter10.equation_10_4_24`.

## Not formalized

* **The randomized sampling of §10.4.5** and its probabilistic error bound.
* **The $4 \times 3$ permutation example of §10.4.3.**
* **Operation counts.**
-/

open Matrix Krylov FloatingPoint
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

/-! ### The upper bidiagonal form (§10.4.1) -/

/-- **Equation (10.4.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $m \ge n$.
There are orthogonal $U \in \mathbb{R}^{m \times m}$ and $V \in \mathbb{R}^{n \times n}$ such
that $B = U^T A V$ is zero below row $n$, its leading block $B(1:n, 1:n)$ is upper bidiagonal,
and $B$ and $A$ have the same singular values.

The singular values are compared as sorted sequences, `Matrix.sortedSingularValues`. The proof
specializes `Matrix.exists_unitary_mul_mul_unitary_isUpperBidiagonal`. The Householder
bidiagonalization of Chapter 5 computes such a factorization. -/
theorem equation_10_4_1 {m n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin m) ℝ, ∃ V ∈ orthogonalGroup (Fin n) ℝ,
      (∀ (i : Fin m) (j : Fin n), n ≤ (i : ℕ) → (Uᵀ * A * V) i j = 0) ∧
      ((Uᵀ * A * V).submatrix (Fin.castLE hnm) id).IsUpperBidiagonal ∧
      (Uᵀ * A * V).sortedSingularValues = A.sortedSingularValues := by
  obtain ⟨U, hU, V, hV, h1, h2⟩ := exists_unitary_mul_mul_unitary_isUpperBidiagonal hnm A
  rw [conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact ⟨U, hU, V, hV, h1, h2,
    A.sortedSingularValues_unitary_mul_mul (transpose_mem_unitaryGroup_iff.2 hU) hV⟩

section Columns

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
  {V : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin m) (Fin n) ℝ}

/-- If $U$ is orthogonal and $U^T A V = B$, then $A V = U B$. -/
private theorem mul_eq_mul_of_transpose_mul_mul (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hB : Uᵀ * A * V = B) : A * V = U * B := by
  rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ _).1 hU,
    Matrix.one_mul]

/-- If $V$ is orthogonal and $U^T A V = B$, then $A^T U = V B^T$. -/
private theorem transpose_mul_eq_mul_transpose (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hB : Uᵀ * A * V = B) : Aᵀ * U = V * Bᵀ := by
  rw [← hB, transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ _).1 hV, Matrix.one_mul]

/-- **Equation (10.4.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$,
let $U \in \mathbb{R}^{m \times m}$ be orthogonal, let $V \in \mathbb{R}^{n \times n}$, and let
$B = U^T A V$ be upper bidiagonal. Let $u_k$ and $v_k$ be the columns of $U$ and $V$, and let
$\alpha_k = b_{kk}$ and $\beta_{k-1} = b_{k-1,k}$. Then for $k = 1, \dots, n$
$$A v_k = \alpha_k u_k + \beta_{k-1} u_{k-1},$$
where the term $\beta_0 u_0$ is zero. This is column $k$ of $AV = UB$.

The orthogonality of $V$ is not needed. Upper bidiagonal is `Matrix.IsUpperBidiagonalRect`. The
index `k : Fin n` is 0-based, and $u_k$ is `U.col (Fin.castLE hnm k)`. -/
theorem equation_10_4_2 (hnm : n ≤ m) (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect) (k : Fin n) :
    A *ᵥ V.col k = B (Fin.castLE hnm k) k • U.col (Fin.castLE hnm k) +
      (if h : 0 < (k : ℕ) then B ⟨k - 1, by omega⟩ k • U.col ⟨k - 1, by omega⟩ else 0) := by
  have hAV := mul_eq_mul_of_transpose_mul_mul hU hB
  ext x
  have h1 : (A *ᵥ V.col k) x = (U * B) x k := by
    rw [← hAV, Matrix.mul_apply, mulVec, dotProduct]
    rfl
  rw [h1, Matrix.mul_apply]
  have hz : ∀ i : Fin m, (i : ℕ) ≠ k → (i : ℕ) + 1 ≠ k → U x i * B i k = 0 :=
    fun i h1 h2 => by rw [hBb i k (Ne.symm h1) (Ne.symm h2), mul_zero]
  split_ifs with hk
  · rw [Fintype.sum_eq_add (Fin.castLE hnm k) ⟨k - 1, by omega⟩
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun i hi => hz i (fun h => hi.1 (Fin.ext (by simpa using h)))
        (fun h => hi.2 (Fin.ext (by simp; omega))))]
    simp [mul_comm]
  · rw [Fintype.sum_eq_single (Fin.castLE hnm k)
      (fun i hi => hz i (fun h => hi (Fin.ext (by simpa using h))) (by omega))]
    simp [mul_comm]

/-- **Equation (10.4.3)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$,
let $U \in \mathbb{R}^{m \times m}$, let $V \in \mathbb{R}^{n \times n}$ be orthogonal, and let
$B = U^T A V$ be upper bidiagonal. Let $u_k$ and $v_k$ be the columns of $U$ and $V$, and let
$\alpha_k = b_{kk}$ and $\beta_k = b_{k,k+1}$. Then for $k = 1, \dots, n$
$$A^T u_k = \alpha_k v_k + \beta_k v_{k+1},$$
where the term $\beta_n v_{n+1}$ is zero. This is column $k$ of $A^T U = V B^T$.

The orthogonality of $U$ is not needed. The index `k : Fin n` is 0-based. -/
theorem equation_10_4_3 (hnm : n ≤ m) (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect) (k : Fin n) :
    Aᵀ *ᵥ U.col (Fin.castLE hnm k) = B (Fin.castLE hnm k) k • V.col k +
      (if h : (k : ℕ) + 1 < n then B (Fin.castLE hnm k) ⟨k + 1, h⟩ • V.col ⟨k + 1, h⟩
        else 0) := by
  have hAU := transpose_mul_eq_mul_transpose hV hB
  ext x
  have h1 : (Aᵀ *ᵥ U.col (Fin.castLE hnm k)) x = (V * Bᵀ) x (Fin.castLE hnm k) := by
    rw [← hAU, Matrix.mul_apply, mulVec, dotProduct]
    rfl
  rw [h1, Matrix.mul_apply]
  have hz : ∀ i : Fin n, i ≠ k → (i : ℕ) ≠ k + 1 → V x i * Bᵀ i (Fin.castLE hnm k) = 0 :=
    fun i h1 h2 => by
      rw [transpose_apply, hBb _ i (by simpa [Fin.ext_iff] using h1) (by simpa using h2),
        mul_zero]
  split_ifs with hk
  · rw [Fintype.sum_eq_add k ⟨k + 1, hk⟩ (fun h => by have := congrArg Fin.val h; simp at this)
      (fun i hi => hz i hi.1 (fun h => hi.2 (Fin.ext h)))]
    simp [mul_comm]
  · rw [Fintype.sum_eq_single k (fun i hi => hz i hi (by have := i.isLt; omega))]
    simp [mul_comm]

/-- A sum over $i < m$ whose terms vanish for $i \ge k$ is the sum over $i < k$. -/
private theorem sum_fin_eq_sum_castLE {M : Type*} [AddCommMonoid M] {k m : ℕ} (hkm : k ≤ m)
    (f : Fin m → M) (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) :
    ∑ i, f i = ∑ i : Fin k, f (Fin.castLE hkm i) := by
  rw [show (∑ i : Fin k, f (Fin.castLE hkm i)) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb hkm), f i by
    rw [Finset.sum_map]; rfl]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_).symm
  by_contra h
  exact hi (Finset.mem_map.2 ⟨⟨i, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/-- **Equation (10.4.6)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$,
let $U \in \mathbb{R}^{m \times m}$ be orthogonal, let $V \in \mathbb{R}^{n \times n}$, and let
$B = U^T A V$ be upper bidiagonal. Then for every $k \le n$
$$A V(:, 1:k) = U(:, 1:k) B(1:k, 1:k).$$

**Typo.** The source prints $A U(:, 1:k) = V(:, 1:k) B(1:k, 1:k)$, which exchanges $U$ and $V$;
the product $AU$ is not defined unless $m = n$.

**Generalization.** The source attributes the identity to $\beta_k = 0$. It holds for every
$k \le n$; only (10.4.7) needs $\beta_k = 0$. -/
theorem equation_10_4_6 (hnm : n ≤ m) (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect) {k : ℕ} (hk : k ≤ n) :
    A * V.submatrix id (Fin.castLE hk) =
      U.submatrix id (Fin.castLE (hk.trans hnm)) *
        B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk) := by
  have hAV := mul_eq_mul_of_transpose_mul_mul hU hB
  ext x j
  have h1 : (A * V.submatrix id (Fin.castLE hk)) x j = (U * B) x (Fin.castLE hk j) := by
    rw [← hAV]
    rfl
  rw [h1, Matrix.mul_apply, Matrix.mul_apply, sum_fin_eq_sum_castLE (hk.trans hnm) _ fun i hi => by
    rw [hBb i _ (by simp; omega) (by simp; omega), mul_zero]]
  rfl

/-- **Equation (10.4.7)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$,
let $U \in \mathbb{R}^{m \times m}$ and $V \in \mathbb{R}^{n \times n}$ be orthogonal, and let
$B = U^T A V$ be upper bidiagonal. Let $1 \le k \le n$, assume that $\beta_k = b_{k,k+1} = 0$ if
$k < n$, and let $B_k = B(1:k, 1:k)$. Then
$$A^T U(:, 1:k) = V(:, 1:k) B_k^T \quad \text{and} \quad A^T A V(:, 1:k) = V(:, 1:k) B_k^T
  B_k.$$

**Typo.** The source prints $A^T V(:, 1:k) = U(:, 1:k) B_k^T$, which exchanges $U$ and $V$.

For $k = n$ the hypothesis on $\beta_k$ is empty. In 0-based indices it is on the entry
`B ⟨k - 1, _⟩ ⟨k, _⟩`. -/
theorem equation_10_4_7 (hnm : n ≤ m) (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) (hβ : ∀ h : k < n, B ⟨k - 1, by omega⟩ ⟨k, h⟩ = 0) :
    Aᵀ * U.submatrix id (Fin.castLE (hk.trans hnm)) =
        V.submatrix id (Fin.castLE hk) *
          (B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk))ᵀ ∧
      Aᵀ * A * V.submatrix id (Fin.castLE hk) =
        V.submatrix id (Fin.castLE hk) *
          ((B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk))ᵀ *
            B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk)) := by
  have hAU := transpose_mul_eq_mul_transpose hV hB
  have h1 : Aᵀ * U.submatrix id (Fin.castLE (hk.trans hnm)) =
      V.submatrix id (Fin.castLE hk) *
        (B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk))ᵀ := by
    ext x j
    have e : (Aᵀ * U.submatrix id (Fin.castLE (hk.trans hnm))) x j =
        (V * Bᵀ) x (Fin.castLE (hk.trans hnm) j) := by
      rw [← hAU]
      rfl
    rw [e, Matrix.mul_apply, Matrix.mul_apply, sum_fin_eq_sum_castLE hk _ fun i hi => ?_]
    · rfl
    · rw [transpose_apply]
      by_cases h2 : (i : ℕ) = k ∧ (j : ℕ) + 1 = k
      · have hz := hβ (by rw [← h2.1]; exact i.isLt)
        have hB0 : B (Fin.castLE (hk.trans hnm) j) i = 0 := by
          convert hz using 2 <;> apply Fin.ext <;> simp <;> omega
        rw [hB0, mul_zero]
      · rw [hBb _ i (by simp; omega) (by simp; omega), mul_zero]
  refine ⟨h1, ?_⟩
  rw [Matrix.mul_assoc, equation_10_4_6 hnm hU hB hBb hk, ← Matrix.mul_assoc, h1,
    Matrix.mul_assoc]

end Columns

/-- **Section 10.4.1** of [golub2013matrix], the singular values of $B(1:k, 1:k)$. Let
$A \in \mathbb{R}^{m \times n}$ with $n \le m$, let $U \in \mathbb{R}^{m \times m}$ and
$V \in \mathbb{R}^{n \times n}$ be orthogonal, and let $B = U^T A V$ be upper bidiagonal. Let
$1 \le k \le n$ and assume that $\beta_k = b_{k,k+1} = 0$ if $k < n$. Then every singular value
of $B_k = B(1:k, 1:k)$ is a singular value of $A$.

The singular values are `Matrix.colSingularValues`, listed with multiplicity in no fixed order:
for each index $i$ of $B_k$ there is an index $j$ of $A$ with $\sigma_i(B_k) = \sigma_j(A)$. By
(10.4.7) the range of $V(:, 1:k)$ is invariant under $A^T A$, which acts there as $B_k^T B_k$.
So an eigenvector $y$ of $B_k^T B_k$ gives the eigenvector $V(:, 1:k) y$ of $A^T A$ for the same
eigenvalue, and the singular values are the square roots of these eigenvalues
(`Matrix.sq_colSingularValues`). -/
theorem singularValues_bidiag_subset {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin m) (Fin n) ℝ}
    (hnm : n ≤ m) (hU : U ∈ orthogonalGroup (Fin m) ℝ) (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    (hβ : ∀ h : k < n, B ⟨k - 1, by omega⟩ ⟨k, h⟩ = 0) (i : Fin k) :
    ∃ j : Fin n, (B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk)).colSingularValues i =
      A.colSingularValues j := by
  set Bk := B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk) with hBk
  set Vk := V.submatrix id (Fin.castLE hk) with hVk
  have hgram := (equation_10_4_7 hnm hU hV hB hBb hk1 hk hβ).2
  have hVkV : Vkᵀ * Vk = 1 := by
    ext a b
    have h := congrFun (congrFun ((mem_orthogonalGroup_iff' _ _).1 hV) (Fin.castLE hk a))
      (Fin.castLE hk b)
    simpa [hVk, Matrix.mul_apply, Matrix.one_apply, Fin.ext_iff] using h
  set hH := isHermitian_conjTranspose_mul_self Bk
  set y : Fin k → ℝ := ⇑(hH.eigenvectorBasis i) with hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [hy] at h
    apply hH.eigenvectorBasis.orthonormal.ne_zero i
    ext a
    simpa using congrFun h a
  have hey : (Bkᴴ * Bk) *ᵥ y = hH.eigenvalues i • y := hH.mulVec_eigenvectorBasis i
  rw [← conjTranspose_eq_transpose_of_trivial Bk] at hgram
  -- the eigenvector of `AᵀA`
  have hAA : (Aᵀ * A) *ᵥ (Vk *ᵥ y) = hH.eigenvalues i • (Vk *ᵥ y) := by
    rw [mulVec_mulVec, hgram, ← mulVec_mulVec, hey, mulVec_smul]
  have hVy : Vk *ᵥ y ≠ 0 := by
    intro h
    apply hy0
    have := congrArg (Vkᵀ *ᵥ ·) h
    simpa only [mulVec_mulVec, hVkV, one_mulVec, mulVec_zero] using this
  have hG := isHermitian_conjTranspose_mul_self A
  have hspec : hH.eigenvalues i ∈ spectrum ℝ (Aᴴ * A) := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨Vk *ᵥ y, hVy, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, smul_mulVec, one_mulVec,
      conjTranspose_eq_transpose_of_trivial A, hAA, sub_self]
  rw [hG.spectrum_real_eq_range_eigenvalues] at hspec
  obtain ⟨j, hj⟩ := hspec
  refine ⟨j, ?_⟩
  have h1 := Bk.sq_colSingularValues i
  have h2 := A.sq_colSingularValues j
  rw [← hj] at h1
  rw [← h2] at h1
  exact (pow_left_inj₀ (Bk.colSingularValues_nonneg i) (A.colSingularValues_nonneg j)
    two_ne_zero).1 h1

/-! ### The Golub–Kahan relations (§10.4.1) -/

section GolubKahan

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))

/-- **Equation (10.4.9)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$v_c \in \mathbb{R}^n$ and $k \ge 0$. Let $V_k$ and $U_k$ be the matrices of the first $k$
Golub–Kahan vectors of $A$ from $v_c$, and let $B_k$ be the $k \times k$ upper bidiagonal matrix
(10.4.8) with diagonal $\alpha_1, \dots, \alpha_k$ and superdiagonal
$\beta_1, \dots, \beta_{k-1}$. Then
$$A V_k = U_k B_k.$$

The identity holds for every $k$: after a breakdown both sides have zero columns. The proof
specializes `GolubKahan.mul_rightMatrix`.

**Reading.** Same bidiagonal product for totalized basis, no positive pivot assumption.
-/
theorem equation_10_4_9 (k : ℕ) :
    A * GolubKahan.rightMatrix A v k =
      GolubKahan.leftMatrix A v k *
        GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k := by
  have h := GolubKahan.mul_rightMatrix A v k
  rw [conjTranspose_eq_transpose_of_trivial] at h
  simpa using h

/-- **Equation (10.4.10)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$v_c \in \mathbb{R}^n$ and $k \ge 1$, with $V_k$, $U_k$ and $B_k$ as in (10.4.9). Then
$$A^T U_k = V_k B_k^T + p_k e_k^T, \qquad p_k = \beta_k v_{k+1},$$
where $e_k$ is the last unit vector of $\mathbb{R}^k$.

In 0-based indices $\beta_k$ and $v_{k+1}$ are `GolubKahan.beta T Ts v (k - 1)` and
`GolubKahan.rightVec T Ts v k`, and $e_k$ is `Krylov.lastVec 1 k`. The proof splits
`GolubKahan.conjTranspose_mul_leftMatrix`, which is $A^T U_k = V_{k+1} \bar B_k$, into the first
$k$ columns of $V_{k+1}$ and the last one.

**Reading.** Same transpose relation with explicit residual, valid with totalization even when alpha
vanishes.
-/
theorem equation_10_4_10 {k : ℕ} (hk : 1 ≤ k) :
    Aᵀ * GolubKahan.leftMatrix A v k =
      GolubKahan.rightMatrix A v k *
          (GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k)ᵀ +
        vecMulVec (GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (k - 1) •
            (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v k).ofLp)
          (Krylov.lastVec (1 : ℝ) k) := by
  have h := GolubKahan.conjTranspose_mul_leftMatrix A v k
  rw [conjTranspose_eq_transpose_of_trivial] at h
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  have hsub := GolubKahan.bidiagLower_submatrix_castSucc (toEuclideanLin A) (toEuclideanLin Aᵀ)
    v k
  rw [h]
  ext x j
  rw [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mul_apply, vecMulVec_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (congrFun hsub i) j
    simp only [submatrix_apply, id] at this
    rw [this]
    rfl
  · have hj := j.isLt
    simp only [GolubKahan.rightMatrix, of_apply, Fin.val_last, GolubKahan.bidiagLower_apply,
      Krylov.lastVec, Pi.smul_apply, smul_eq_mul, conjTranspose_eq_transpose_of_trivial]
    by_cases h1 : (j : ℕ) + 1 = k
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h1,
        show k - 1 = j by omega]
      ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1]
      ring

/-- **Equation (10.4.11)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$v_c \in \mathbb{R}^n$ and $k \ge 0$. The first $k$ right Golub–Kahan vectors of $A$ from $v_c$
span the Krylov subspace of $A^T A$:
$$\operatorname{span}\{v_1, \dots, v_k\} = \mathcal{K}(A^T A, v_c, k).$$

The proof specializes `GolubKahan.span_rightVec`.

**Reading.** Same right Krylov span for every prefix, including padded vectors.
-/
theorem equation_10_4_11 (k : ℕ) :
    Submodule.span ℝ (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin (Aᵀ * A)) v k := by
  rw [GolubKahan.span_rightVec, toEuclideanLin_mul]

/-- **Equation (10.4.12)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$v_c \in \mathbb{R}^n$ and $k \ge 0$. The first $k$ left Golub–Kahan vectors of $A$ from $v_c$
span the Krylov subspace of $A A^T$ from $A v_c$:
$$\operatorname{span}\{u_1, \dots, u_k\} = \mathcal{K}(A A^T, A v_c, k).$$

The proof specializes `GolubKahan.span_leftVec`.

**Reading.** Same left Krylov span for every prefix, including padded vectors.
-/
theorem equation_10_4_12 (k : ℕ) :
    Submodule.span ℝ (GolubKahan.leftVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin (A * Aᵀ)) (toEuclideanLin A v) k := by
  rw [GolubKahan.span_leftVec, toEuclideanLin_mul]

/-- **Section 10.4.1** of [golub2013matrix], the connection with the Lanczos process. Let
$A \in \mathbb{R}^{m \times n}$, $v_c \in \mathbb{R}^n$ and $k \ge 0$, and let $B_k$ be as in
(10.4.9). Then
$$B_k^T B_k = T_k(A^T A, v_c),$$
the $k \times k$ Lanczos tridiagonal matrix of $A^T A$ from $v_c$.

So the squares of the singular values of $B_k$ are the Ritz values of $A^T A$ on
$\mathcal{K}(A^T A, v_c, k)$ (`Lanczos.ritzValues`), which Theorems 10.1.2–10.1.4 bound; this is
how the source applies the convergence theory of the symmetric Lanczos process. The Lanczos
matrix is `Lanczos.tridiag`. The proof specializes `GolubKahan.bidiag_conjTranspose_mul_bidiag`.

**Reading.** Same Gram identity for all prefix lengths, including beyond grade.
-/
theorem bidiag_transpose_mul_bidiag (k : ℕ) :
    (GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k)ᵀ *
        GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k =
      Lanczos.tridiag (toEuclideanLin (Aᵀ * A)) v k := by
  have h := GolubKahan.bidiag_conjTranspose_mul_bidiag (A := toEuclideanLin A)
    (Astar := toEuclideanLin Aᵀ) v (LinearMap.isAdjointPair_inner_iff.2 fun u x => by
      have := toEuclideanLin_conjTranspose_inner_left A x u
      rwa [conjTranspose_eq_transpose_of_trivial] at this) k
  rw [conjTranspose_eq_transpose_of_trivial] at h
  rw [h, toEuclideanLin_mul]

/-! ### Ritz approximations (§10.4.2) -/

/-- **Equation (10.4.14)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$v_c \in \mathbb{R}^n$ and $k \ge 0$, with $V_k$, $U_k$ and $B_k$ as in (10.4.9). Let
$F_k, G_k \in \mathbb{R}^{k \times k}$ with $F_k$ orthogonal, and let $\gamma \in \mathbb{R}^k$
satisfy (10.4.13), $F_k^T B_k G_k = \Gamma = \operatorname{diag}(\gamma_1, \dots, \gamma_k)$.
Then $Y_k = V_k G_k$ and $Z_k = U_k F_k$ satisfy
$$A Y_k = Z_k \Gamma,$$
that is, $A y_i = \gamma_i z_i$ for every column.

The orthogonality of $G_k$ is not needed. The proof uses (10.4.9).

**Reading.** Uses orthogonal F and transformed bidiagonal equation; no orthogonality of G or sorted
diagonal required.
-/
theorem equation_10_4_14 {k : ℕ} {F G : Matrix (Fin k) (Fin k) ℝ}
    (hF : F ∈ orthogonalGroup (Fin k) ℝ) {γ : Fin k → ℝ}
    (hSVD : Fᵀ * GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k * G = diagonal γ) :
    A * (GolubKahan.rightMatrix A v k * G) = (GolubKahan.leftMatrix A v k * F) * diagonal γ := by
  rw [← Matrix.mul_assoc, equation_10_4_9, ← hSVD]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (GolubKahan.leftMatrix A v k) F Fᵀ, (mem_orthogonalGroup_iff _ _).1 hF,
    Matrix.mul_one]

/-- **Equation (10.4.15)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$v_c \in \mathbb{R}^n$ and $k \ge 1$, let $F_k, G_k \in \mathbb{R}^{k \times k}$ be orthogonal,
and let $F_k^T B_k G_k = \Gamma = \operatorname{diag}(\gamma_1, \dots, \gamma_k)$. With
$Y_k = V_k G_k$, $Z_k = U_k F_k$ and $p_k = \beta_k v_{k+1}$ as in (10.4.10),
$$A^T Z_k = Y_k \Gamma + p_k e_k^T F_k,$$
that is, $A^T z_i = \gamma_i y_i + [F_k]_{ki} p_k$ for every column.

The row vector $e_k^T F_k$ is `Krylov.lastVec 1 k ᵥ* F`. The proof uses (10.4.10).

**Reading.** Same residual row rotated by F, with diagonal equality and orthogonality rather than
sorted SVD conventions.
-/
theorem equation_10_4_15 {k : ℕ} (hk : 1 ≤ k) {F G : Matrix (Fin k) (Fin k) ℝ}
    (hF : F ∈ orthogonalGroup (Fin k) ℝ) (hG : G ∈ orthogonalGroup (Fin k) ℝ) {γ : Fin k → ℝ}
    (hSVD : Fᵀ * GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k * G = diagonal γ) :
    Aᵀ * (GolubKahan.leftMatrix A v k * F) =
      (GolubKahan.rightMatrix A v k * G) * diagonal γ +
        vecMulVec (GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (k - 1) •
            (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v k).ofLp)
          (Krylov.lastVec (1 : ℝ) k ᵥ* F) := by
  set Bk := GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k
  have hBF : Bkᵀ * F = G * diagonal γ := by
    have hB : Bk = F * diagonal γ * Gᵀ := by
      rw [← hSVD]
      simp only [← Matrix.mul_assoc]
      rw [(mem_orthogonalGroup_iff _ _).1 hF, Matrix.one_mul, Matrix.mul_assoc,
        (mem_orthogonalGroup_iff _ _).1 hG, Matrix.mul_one]
    rw [hB, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
      Matrix.mul_assoc, Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hF, Matrix.mul_one]
  rw [← Matrix.mul_assoc, equation_10_4_10 A v hk, Matrix.add_mul, vecMulVec_mul,
    Matrix.mul_assoc, hBF, Matrix.mul_assoc]

end GolubKahan

/-! ### The lower bidiagonal form (§10.4.4) -/

/-- **Equation (10.4.18)** of [golub2013matrix]. For every $A \in \mathbb{R}^{m \times n}$ there are
orthogonal $U \in \mathbb{R}^{m \times m}$ and $V \in \mathbb{R}^{n \times n}$ such that
$U^T A V$ is lower bidiagonal: its only nonzero entries are at the positions $(i, i)$ and
$(i + 1, i)$. In particular, for $m > n$ only the first $n + 1$ rows can be nonzero.

Lower bidiagonal is `Matrix.IsLowerBidiagonalRect`. No relation between $m$ and $n$ is assumed.
The factorization is the transpose of an upper bidiagonalization of $A^T$
(`Matrix.exists_unitary_mul_mul_unitary_apply_eq_zero`).

**Reading.** Lower bidiagonal existence for all rectangular shapes, including wide and square.
-/
theorem equation_10_4_18 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin m) ℝ, ∃ V ∈ orthogonalGroup (Fin n) ℝ,
      (Uᵀ * A * V).IsLowerBidiagonalRect := by
  obtain ⟨U', hU', V', hV', h⟩ := exists_unitary_mul_mul_unitary_apply_eq_zero Aᵀ
  refine ⟨V', hV', U', hU', fun i j h1 h2 => ?_⟩
  have := h j i (Ne.symm h1) (fun h' => h2 (by omega))
  rw [conjTranspose_eq_transpose_of_trivial] at this
  have e : V'ᵀ * A * U' = (U'ᵀ * Aᵀ * V')ᵀ := by
    simp [transpose_mul, Matrix.mul_assoc]
  rw [e, transpose_apply]
  exact this

/-- **Equation (10.4.19)** of [golub2013matrix] (Paige–Saunders lower bidiagonalization). Let
$A \in \mathbb{R}^{m \times n}$, $u_c \in \mathbb{R}^m$ and $k \ge 1$. Let
$u_1, u_2, \dots \in \mathbb{R}^m$ and $v_1, v_2, \dots \in \mathbb{R}^n$ be the vectors of the
lower bidiagonalization of $A$ from $u_c$, that is, the right and the left Golub–Kahan vectors
of $A^T$ from $u_c$, and let $B(1:k, 1:k)$ be the $k \times k$ lower bidiagonal matrix of its
coefficients. Then
$$A V(:, 1:k) = U(:, 1:k) B(1:k, 1:k) + p_k e_k^T, \qquad p_k = \beta_{k+1} u_{k+1}.$$

The source's $u_j$ is `GolubKahan.rightVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u_c (j - 1)`
and its $v_j$ is the corresponding `GolubKahan.leftVec`. The matrix $B(1:k, 1:k)$ is the
transpose of the upper bidiagonal `GolubKahan.bidiag` of the pair $(A^T, A)$. The statement is
(10.4.10) for $A^T$.

**Reading.** Same residual relation under transpose-targeted construction with totalized vectors.
-/
theorem equation_10_4_19 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin m))
    {k : ℕ} (hk : 1 ≤ k) :
    A * GolubKahan.leftMatrix Aᵀ u k =
      GolubKahan.rightMatrix Aᵀ u k *
          (GolubKahan.bidiag (toEuclideanLin Aᵀ) (toEuclideanLin A) u k)ᵀ +
        vecMulVec (GolubKahan.beta (toEuclideanLin Aᵀ) (toEuclideanLin A) u (k - 1) •
            (GolubKahan.rightVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u k).ofLp)
          (Krylov.lastVec (1 : ℝ) k) := by
  have h := equation_10_4_10 Aᵀ u hk
  rwa [transpose_transpose] at h

/-! ### Randomized low-rank approximation (§10.4.5) -/

/-- For the first $k$ columns $\tilde Z_1 = U(:, 1:k)$ of $U$,
$\tilde Z_1 \tilde Z_1^T = U P_k U^T$, where $P_k$ is the diagonal projector onto the first $k$
coordinates. -/
private theorem submatrix_castLE_mul_transpose {m k : ℕ} (hkm : k ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    U.submatrix id (Fin.castLE hkm) * (U.submatrix id (Fin.castLE hkm))ᵀ =
      U * (rectDiagonal fun i => if i < k then (1 : ℝ) else 0) * Uᵀ := by
  ext a b
  simp only [Matrix.mul_apply, submatrix_apply, id_eq, transpose_apply, rectDiagonal_apply]
  set F : ℕ → ℝ := fun i => if h : i < m then U a ⟨i, h⟩ * U b ⟨i, h⟩ else 0 with hF
  have h1 : ∀ j : Fin k, U a (Fin.castLE hkm j) * U b (Fin.castLE hkm j) = F j := fun j => by
    have hj : (j : ℕ) < m := by omega
    simp only [hF, hj, ↓reduceDIte]
    rfl
  have h2 : ∀ i : Fin m,
      (∑ l : Fin m, U a l * (if (l : ℕ) = i then (if (l : ℕ) < k then (1 : ℝ) else 0) else 0)) *
        U b i = (fun i : ℕ => if i < k then F i else 0) i := fun i => by
    rw [Finset.sum_eq_single i (fun l _ hl => by rw [ite_eq_right (fun h => hl (Fin.ext h)),
      mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
    simp only [hF, i.isLt, ↓reduceDIte, ite_true]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_congr rfl fun i _ => h2 i,
    Fin.sum_univ_eq_sum_range F k,
    Fin.sum_univ_eq_sum_range (fun i => if i < k then F i else 0) m, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

open scoped Matrix.Norms.L2Operator in
/-- **Equation (10.4.20)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have the SVD
$A = \tilde Z \tilde \Sigma \tilde Y^T$, with $\tilde Z$ and $\tilde Y$ orthogonal and singular
values $\sigma_1 \ge \sigma_2 \ge \dots \ge 0$, and let $k \le \operatorname{rank} A$. Let
$\tilde Z_1 = \tilde Z(:, 1:k)$ and let $\tilde A_k = \tilde Z_1 \tilde \Sigma_1 \tilde Y_1^T =
\sum_{i \le k} \sigma_i \tilde z_i \tilde y_i^T$ be the truncation (2.4.3). Then
$\tilde A_k = \tilde Z_1 \tilde Z_1^T A$, $\operatorname{rank} \tilde A_k = k$, and $\tilde A_k$
is a closest matrix of rank at most $k$ to $A$ in the 2-norm:
$$\|A - \tilde A_k\|_2 \le \|A - B\|_2 \quad \text{for every } B \in \mathbb{R}^{m \times n}
  \text{ with } \operatorname{rank} B \le k.$$

The SVD is `Matrix.IsSVD A U σ V` with the orthogonal factors `U` and `V`, and the truncation is
`Matrix.svdTruncation U σ V k`. The minimality is the Eckart–Young theorem, Theorem 2.4.8
(`GolubVanLoan.Chapter02.theorem_2_4_8`); the Frobenius-norm form is
`GolubVanLoan.Chapter10.equation_10_4_20_frobenius`. The proof specializes
`Matrix.rank_svdTruncation`, `Matrix.l2_opNorm_sub_svdTruncation` and
`Matrix.isLeast_l2_opNorm_sub_of_rank_le`, the backbone form of Theorem 2.4.8. -/
theorem equation_10_4_20 {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    {k : ℕ} (hk : k ≤ A.rank) :
    let Z₁ := U.submatrix id
      (Fin.castLE (hk.trans ((rank_le_card_height A).trans_eq (Fintype.card_fin m))))
    svdTruncation U σ V k = Z₁ * Z₁ᵀ * A ∧ (svdTruncation U σ V k).rank = k ∧
      ∀ B : Matrix (Fin m) (Fin n) ℝ, B.rank ≤ k →
        ‖A - svdTruncation U σ V k‖ ≤ ‖A - B‖ := by
  intro Z₁
  have hkm : k ≤ m := hk.trans ((rank_le_card_height A).trans_eq (Fintype.card_fin m))
  refine ⟨?_, rank_svdTruncation h hk, fun B hB => ?_⟩
  · have hUU : Uᵀ * U = 1 := by
      have := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left
      rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
    have hPR : (rectDiagonal fun i => if i < k then (1 : ℝ) else 0 : Matrix (Fin m) (Fin m) ℝ) *
        (rectDiagonal fun i => ((σ i : ℝ) : ℝ) : Matrix (Fin m) (Fin n) ℝ) =
          rectDiagonal fun i => if i < k then σ i else 0 := by
      rw [rectDiagonal_mul_rectDiagonal]
      congr 1
      funext i
      split_ifs <;> first | simp | omega
    simp only [Z₁]
    rw [submatrix_castLE_mul_transpose hkm]
    conv_rhs => rw [h.eq_mul_mul_star]
    simp only [Matrix.mul_assoc, RCLike.ofReal_real_eq_id, id]
    rw [← Matrix.mul_assoc Uᵀ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc _ _ (star V), hPR]
    simp only [svdTruncation, Matrix.mul_assoc, RCLike.ofReal_real_eq_id, id]
  · rw [l2_opNorm_sub_svdTruncation h k]
    exact (isLeast_l2_opNorm_sub_of_rank_le A k).2 ⟨B, hB, rfl⟩

open scoped Matrix.Norms.Frobenius in
/-- **Equation (10.4.20)** of [golub2013matrix], the Frobenius norm. Let
$A \in \mathbb{R}^{m \times n}$ have an SVD as in (10.4.20), let $k \ge 0$, and let $\tilde A_k$
be the truncation (2.4.3). Then $\tilde A_k$ is a closest matrix of rank at most $k$ to $A$ in
the Frobenius norm:
$$\|A - \tilde A_k\|_F \le \|A - B\|_F \quad \text{for every } B \in \mathbb{R}^{m \times n}
  \text{ with } \operatorname{rank} B \le k.$$

This is the Eckart–Young–Mirsky remark after Theorem 2.4.8. No bound on $k$ is needed. The proof
specializes `Matrix.frobenius_norm_sub_svdTruncation` and
`Matrix.isLeast_frobenius_norm_sub_of_rank_le`.

**Reading.** Norm optimality for every k, including above matrix rank.
-/
theorem equation_10_4_20_frobenius {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    (k : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) (hB : B.rank ≤ k) :
    ‖A - svdTruncation U σ V k‖ ≤ ‖A - B‖ := by
  rw [frobenius_norm_sub_svdTruncation h k]
  have := (isLeast_frobenius_norm_sub_of_rank_le A k).2 ⟨B, hB, rfl⟩
  simpa only [Fintype.card_fin] using this

/-! ### The CUR identities (§10.4.5) -/

section CUR

variable {m c k r s : ℕ} {C : Matrix (Fin m) (Fin c) ℝ} {Z₁ : Matrix (Fin m) (Fin k) ℝ}
  {Z₂ : Matrix (Fin m) (Fin r) ℝ} {σ₁ : Fin k → ℝ} {σ₂ : Fin r → ℝ}
  {Y₁ : Matrix (Fin c) (Fin k) ℝ} {Y₂ : Matrix (Fin c) (Fin r) ℝ}

/-- **Equation (10.4.22)** of [golub2013matrix]. Let $C \in \mathbb{R}^{m \times c}$ have the split
SVD $C = Z_1 \Sigma_1 Y_1^T + Z_2 \Sigma_2 Y_2^T$ with $Z_1 \in \mathbb{R}^{m \times k}$,
$Z_2 \in \mathbb{R}^{m \times r}$, $Y_1 \in \mathbb{R}^{c \times k}$,
$Y_2 \in \mathbb{R}^{c \times r}$ and diagonal $\Sigma_1 \in \mathbb{R}^{k \times k}$,
$\Sigma_2 \in \mathbb{R}^{r \times r}$. Assume that $Y_1^T Y_1 = I$, $Y_2^T Y_1 = 0$ and that
$\Sigma_1$ is nonsingular, and let $\Phi = Y_1 \Sigma_1^{-2} Y_1^T$. Then
$$C \Phi = Z_1 \Sigma_1^{-1} Y_1^T.$$

In the source $Y = [Y_1 | Y_2]$ is orthogonal; only the two relations $Y_1^T Y_1 = I$ and
$Y_2^T Y_1 = 0$ are used. The diagonals of $\Sigma_1$ and $\Sigma_2$ are vectors `σ₁` and `σ₂`.

**Reading.** Algebraic identity with just right-block orthogonality and nonzero retained diagonal.
-/
theorem equation_10_4_22 (hC : C = Z₁ * diagonal σ₁ * Y₁ᵀ + Z₂ * diagonal σ₂ * Y₂ᵀ)
    (hY₁ : Y₁ᵀ * Y₁ = 1) (hY₂₁ : Y₂ᵀ * Y₁ = 0) (hσ : ∀ i, σ₁ i ≠ 0) :
    C * (Y₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) * Y₁ᵀ) =
      Z₁ * diagonal (fun i => (σ₁ i)⁻¹) * Y₁ᵀ := by
  have hd : diagonal σ₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) = diagonal (fun i => (σ₁ i)⁻¹) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    field_simp [hσ i]
  rw [hC, Matrix.add_mul]
  have e1 : Z₁ * diagonal σ₁ * Y₁ᵀ * (Y₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) * Y₁ᵀ) =
      Z₁ * diagonal (fun i => (σ₁ i)⁻¹) * Y₁ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y₁ᵀ Y₁, hY₁, Matrix.one_mul, ← Matrix.mul_assoc (diagonal σ₁), hd]
  have e2 : Z₂ * diagonal σ₂ * Y₂ᵀ * (Y₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) * Y₁ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y₂ᵀ Y₁, hY₂₁, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  rw [e1, e2, add_zero]

/-- Selecting rows commutes with multiplication on the right:
$(MN)(\mathrm{row}, :) = M(\mathrm{row}, :) N$. -/
private theorem submatrix_mul_id {p q t : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (N : Matrix (Fin q) (Fin t) ℝ) (row : Fin s → Fin p) :
    (M * N).submatrix row id = M.submatrix row id * N := by
  ext i j
  simp [Matrix.mul_apply]

/-- **Equation (10.4.23)** of [golub2013matrix]. Let $C \in \mathbb{R}^{m \times c}$ have the split
SVD $C = Z_1 \Sigma_1 Y_1^T + Z_2 \Sigma_2 Y_2^T$ as in (10.4.22), and let
$A \in \mathbb{R}^{m \times n}$. Select $s$ rows by indices
$\mathrm{row}(1), \dots, \mathrm{row}(s)$, let $D_R = \operatorname{diag}(d)$ for
$d \in \mathbb{R}^s$, and let $R = D_R A(\mathrm{row}, :)$ and $\Psi = D_R C(\mathrm{row}, :)$.
Then
$$\Psi^T R = \bigl(D_R (Z_1(\mathrm{row}, :) \Sigma_1 Y_1^T + Z_2(\mathrm{row}, :) \Sigma_2
  Y_2^T)\bigr)^T D_R A(\mathrm{row}, :).$$

This is the SVD of $C$ substituted in the selected rows; no relation between the factors is
needed. The source writes the left side as $\Psi^T R$ here and as $\Psi R$ in (10.4.24). The
selection is a map `row : Fin s → Fin m`, which need not be injective.

**Correction.** Deterministic shape-correct identity for arbitrary selected rows and scale.
-/
theorem equation_10_4_23 {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (row : Fin s → Fin m)
    (d : Fin s → ℝ) (hC : C = Z₁ * diagonal σ₁ * Y₁ᵀ + Z₂ * diagonal σ₂ * Y₂ᵀ) :
    (diagonal d * C.submatrix row id)ᵀ * (diagonal d * A.submatrix row id) =
      (diagonal d * (Z₁.submatrix row id * diagonal σ₁ * Y₁ᵀ +
          Z₂.submatrix row id * diagonal σ₂ * Y₂ᵀ))ᵀ * (diagonal d * A.submatrix row id) := by
  rw [hC, submatrix_add, Pi.add_apply, Pi.add_apply, submatrix_mul_id, submatrix_mul_id,
    submatrix_mul_id, submatrix_mul_id]

/-- **Equation (10.4.24)** of [golub2013matrix]. Let $C$, $Z_1$, $Y_1$, $\Sigma_1$ and $\Phi$ be as
in (10.4.22), with $Y_1^T Y_1 = I$, $Y_2^T Y_1 = 0$ and $\Sigma_1$ nonsingular, and let $A$,
$D_R$, $R$ and $\Psi$ be as in (10.4.23). Then $U = \Phi \Psi^T$ satisfies
$$C U R = (C \Phi)(\Psi^T R) = Z_1 (D_R Z_1(\mathrm{row}, :))^T (D_R A(\mathrm{row}, :)).$$

**Typo.** The source prints $(C\Phi)(\Psi R)$ and omits the transpose. The product $\Psi R$ is
not defined unless $s = c$, and (10.4.23) has $\Psi^T R$.

The proof combines (10.4.22), (10.4.23) and $Y_1^T Y_2 = 0$.

**Correction.** The last product in the printed equation also needs the transpose on $D_R
Z_1(\mathrm{row},:)$. The formal expression gives it on both sides. -/
theorem equation_10_4_24 {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (row : Fin s → Fin m)
    (d : Fin s → ℝ) (hC : C = Z₁ * diagonal σ₁ * Y₁ᵀ + Z₂ * diagonal σ₂ * Y₂ᵀ)
    (hY₁ : Y₁ᵀ * Y₁ = 1) (hY₂₁ : Y₂ᵀ * Y₁ = 0) (hσ : ∀ i, σ₁ i ≠ 0) :
    C * ((Y₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) * Y₁ᵀ) * (diagonal d * C.submatrix row id)ᵀ) *
        (diagonal d * A.submatrix row id) =
      Z₁ * (diagonal d * Z₁.submatrix row id)ᵀ * (diagonal d * A.submatrix row id) := by
  have hY₁₂ : Y₁ᵀ * Y₂ = 0 := by
    rw [← transpose_transpose (Y₁ᵀ * Y₂), transpose_mul, transpose_transpose, hY₂₁,
      transpose_zero]
  have hinv : diagonal (fun i => (σ₁ i)⁻¹) * diagonal σ₁ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hσ i)
  rw [← Matrix.mul_assoc C, equation_10_4_22 hC hY₁ hY₂₁ hσ, Matrix.mul_assoc,
    equation_10_4_23 A row d hC]
  simp only [transpose_mul, transpose_add, transpose_transpose, diagonal_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Y₁ᵀ Y₁, hY₁, Matrix.one_mul, ← Matrix.mul_assoc Y₁ᵀ Y₂, hY₁₂]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  rw [← Matrix.mul_assoc (diagonal fun i => (σ₁ i)⁻¹), hinv, Matrix.one_mul]

end CUR

/-! ### Ritz pairs of $A^T A$ (§10.4.2) -/

/-- **Section 10.4.2** of [golub2013matrix], Ritz pairs of $A^T A$. Let
$A \in \mathbb{R}^{m \times n}$ and $v_c \in \mathbb{R}^n$, and let $1 \le k \le g$, where $g$
is the grade of $v_c$ for $A^T A$. Let $F_k, G_k \in \mathbb{R}^{k \times k}$ be orthogonal with
$F_k^T B_k G_k = \operatorname{diag}(\gamma_1, \dots, \gamma_k)$ as in (10.4.13), let
$1 \le i \le k$, and let $y_i = V_k G_k e_i$ and $p_k = \beta_k v_{k+1}$. Then
$$A^T A y_i = \gamma_i^2 y_i + \gamma_i [F_k]_{ki} p_k,$$
and $(\gamma_i^2, y_i)$ is a Ritz pair of $A^T A$ with respect to $\mathcal{K}(A^T A, v_c, k)$:
$y_i$ is a nonzero vector of this subspace, and $A^T A y_i - \gamma_i^2 y_i$ is orthogonal to
it.

**Correction.** The source prints $A^T A y_i = \gamma_i^2 z_i + [F_k]_{ki} p_k$. The vector
$z_i \in \mathbb{R}^m$ does not belong in this identity, and the coefficient of $p_k$ has the
factor $\gamma_i$. The stated identity follows from (10.4.14) and (10.4.15).

**Reading.** The source names the Ritz pair $\{\gamma_i, y_i\}$. The Ritz value of $A^T A$ is
$\gamma_i^2$, the square of the singular value estimate $\gamma_i$.

The Ritz pair is `Krylov.IsRitzPair` and the grade is `Krylov.grade`. The proof uses that
$B_k^T B_k = T_k(A^T A)$ has the eigenvector $G_k e_i$ for the eigenvalue $\gamma_i^2$, and
applies `Arnoldi.isRitzPair_of_mulVec_eq_smul`. -/
theorem isRitzPair_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ grade (toEuclideanLin (Aᵀ * A)) v)
    {F G : Matrix (Fin k) (Fin k) ℝ} (hF : F ∈ orthogonalGroup (Fin k) ℝ)
    (hG : G ∈ orthogonalGroup (Fin k) ℝ) {γ : Fin k → ℝ}
    (hSVD : Fᵀ * GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k * G = diagonal γ)
    (i : Fin k) :
    let y := (GolubKahan.rightMatrix A v k * G) *ᵥ Pi.single i 1
    let p := GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (k - 1) •
      (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v k).ofLp
    (Aᵀ * A) *ᵥ y = (γ i ^ 2) • y + (γ i * F ⟨k - 1, by omega⟩ i) • p ∧
      Krylov.IsRitzPair (toEuclideanLin (Aᵀ * A))
        (Krylov.subspace (toEuclideanLin (Aᵀ * A)) v k) (γ i ^ 2) (WithLp.toLp 2 y) := by
  intro y p
  set Bk := GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k with hBk
  have hGG : Gᵀ * G = 1 := (mem_orthogonalGroup_iff' _ _).1 hG
  have hB : Bk = F * diagonal γ * Gᵀ := by
    rw [← hSVD]
    simp only [← Matrix.mul_assoc]
    rw [(mem_orthogonalGroup_iff _ _).1 hF, Matrix.one_mul, Matrix.mul_assoc,
      (mem_orthogonalGroup_iff _ _).1 hG, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · have h14 := equation_10_4_14 A v hF hSVD
    have h15 := equation_10_4_15 A v hk1 hF hG hSVD
    have hw : (Krylov.lastVec (1 : ℝ) k ᵥ* F) i = F ⟨k - 1, by omega⟩ i := by
      simp only [vecMul, dotProduct, Krylov.lastVec]
      rw [Finset.sum_eq_single ⟨k - 1, by omega⟩ (fun l _ hl => by
        rw [ite_eq_right (fun h => hl (Fin.ext (by simp; omega))), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp only [ite_eq_left (show k - 1 + 1 = k by omega), one_mul]
    have hs : ∀ c : ℝ, (Pi.single i c : Fin k → ℝ) = c • Pi.single i (1 : ℝ) := fun c => by
      ext l
      simp [Pi.single_apply]
    simp only [y, p]
    generalize GolubKahan.rightMatrix A v k = V at h14 h15 ⊢
    generalize GolubKahan.leftMatrix A v k = U at h14 h15
    generalize GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (k - 1) •
      (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v k).ofLp = p' at h15 ⊢
    have hmat : (Aᵀ * A) * (V * G) = (V * G) * diagonal γ * diagonal γ +
        vecMulVec p' (Krylov.lastVec (1 : ℝ) k ᵥ* F) * diagonal γ := by
      rw [Matrix.mul_assoc, h14, ← Matrix.mul_assoc, h15, Matrix.add_mul]
    have t1 : ((V * G) * diagonal γ * diagonal γ) *ᵥ Pi.single i 1 =
        (γ i ^ 2) • ((V * G) *ᵥ Pi.single i 1) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, diagonal_mulVec_single, diagonal_mulVec_single,
        hs, mulVec_smul, sq, mul_one]
    have t2 : (vecMulVec p' (Krylov.lastVec (1 : ℝ) k ᵥ* F) * diagonal γ) *ᵥ Pi.single i 1 =
        (γ i * F ⟨k - 1, by omega⟩ i) • p' := by
      rw [← mulVec_mulVec, diagonal_mulVec_single, vecMulVec_mulVec, dotProduct_single, hw,
        op_smul_eq_smul, mul_one, mul_comm]
    rw [mulVec_mulVec, hmat, add_mulVec, t1, t2]
  · have hsymm : (toEuclideanLin (Aᵀ * A)).IsSymmetric :=
      isSymmetric_toEuclideanLin_iff.mpr (by
        have := isHermitian_conjTranspose_mul_self A
        rwa [conjTranspose_eq_transpose_of_trivial] at this)
    have hy0 : G *ᵥ Pi.single i 1 ≠ 0 := by
      intro h
      have h2 : Gᵀ *ᵥ (G *ᵥ Pi.single i 1) = Pi.single i 1 := by
        rw [mulVec_mulVec, hGG, one_mulVec]
      rw [h, mulVec_zero] at h2
      have h3 := congrFun h2 i
      simp at h3
    have hBB : (Bkᵀ * Bk) * G = G * diagonal (fun j => γ j ^ 2) := by
      rw [hB, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Fᵀ F, (mem_orthogonalGroup_iff' _ _).1 hF, Matrix.one_mul,
        hGG, Matrix.mul_one, diagonal_mul_diagonal]
      congr 2
      funext j
      ring
    have hH : (Arnoldi.hessenbergSq (toEuclideanLin (Aᵀ * A)) v k) *ᵥ (G *ᵥ Pi.single i 1) =
        (γ i ^ 2) • (G *ᵥ Pi.single i 1) := by
      rw [Lanczos.hessenbergSq_eq_map_tridiag v hsymm, ← bidiag_transpose_mul_bidiag A v k]
      simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]
      rw [mulVec_mulVec, hBB, ← mulVec_mulVec, diagonal_mulVec_single]
      ext x
      simp only [mulVec, dotProduct, Pi.single_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      ring
    simp only [y]
    rw [← mulVec_mulVec, GolubKahan.rightMatrix_eq_basisMatrix,
      conjTranspose_eq_transpose_of_trivial, toLp_basisMatrix_mulVec]
    exact Arnoldi.isRitzPair_of_mulVec_eq_smul _ v hk hy0 hH

/-! ### Algorithms 10.4.1 and 10.4.2 -/

/-- The state of the bidiagonalization programs of Algorithms 10.4.1 and 10.4.2: the step counter
$k$, the right and the left vectors, the coefficients $\alpha$ and $\beta$, the vector $p_k$,
and a flag that records that the loop "while $\beta_k \neq 0$" has stopped. -/
structure BidiagState (m n : ℕ) where
  /-- The step counter $k$ of the source. -/
  k : ℕ
  /-- The right vectors: `v j` is the source's $v_{j+1}$ in Algorithm 10.4.1. -/
  v : ℕ → Fin n → ℝ
  /-- The left vectors: `u j` is the source's $u_{j+1}$ in Algorithm 10.4.1. -/
  u : ℕ → Fin m → ℝ
  /-- The diagonal coefficients: `alpha j` is the source's $\alpha_{j+1}$ in Algorithm 10.4.1. -/
  alpha : ℕ → ℝ
  /-- The off-diagonal coefficients: `beta j` is the source's $\beta_{j+1}$ in Algorithm 10.4.1. -/
  beta : ℕ → ℝ
  /-- The current vector $p_k$. -/
  p : Fin n → ℝ
  /-- Whether the loop has stopped because $\beta_k = 0$. -/
  done : Bool

section BidiagProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m n : ℕ}

/-- One pass of the `while` loop of Algorithm 10.4.1 for a pair of matrices $(B, C)$, where $C$
plays the role of $B^T$; once the loop has stopped, the pass does nothing. The pass computes
```
v_{k+1} = p_k/β_k,  k = k + 1,  r_k = B v_k − β_{k−1} u_{k−1},  α_k = ‖r_k‖₂,  u_k = r_k/α_k,
p_k = C u_k − α_k v_k,  β_k = ‖p_k‖₂
```
with $\beta_0 = 1$ and $u_0 = 0$ at the first pass. For $(B, C) = (A, A^T)$ it is the loop body
of Algorithm 10.4.1, and for $(A^T, A)$ it is the loop body of Algorithm 10.4.2 with the roles
of $u$ and $v$ exchanged.

**Reading.** Shared two-operator loop, rounded arithmetic and total normalization.
-/
noncomputable def bidiagStep (B : Matrix (Fin m) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (s : BidiagState m n) : M (BidiagState m n) :=
  if s.done then pure s else do
    let bk : ℝ := if s.k = 0 then 1 else s.beta (s.k - 1)
    let vk ← vecDiv rnd s.p bk
    let w ← algorithm_1_1_3 rnd B vk 0
    let r ← algorithm_1_1_2 rnd (-bk) (if s.k = 0 then 0 else s.u (s.k - 1)) w
    let a ← vecNorm rnd r
    let uk ← vecDiv rnd r a
    let z ← algorithm_1_1_3 rnd C uk 0
    let p ← algorithm_1_1_2 rnd (-a) vk z
    let b ← vecNorm rnd p
    pure
      { k := s.k + 1
        v := Function.update s.v s.k vk
        u := Function.update s.u s.k uk
        alpha := Function.update s.alpha s.k a
        beta := Function.update s.beta s.k b
        p := p
        done := decide (b = 0) }

/-- The bidiagonalization loop for a pair $(B, C)$ from the starting vector $v_0$: at most `fuel`
passes of `GolubVanLoan.Chapter10.bidiagStep`, from the state with $k = 0$, $p = v_0$ and all
vectors and coefficients zero.

**Reading.** Shared loop with explicit finite fuel and stopped flag.
-/
noncomputable def bidiagLoop (B : Matrix (Fin m) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (v₀ : Fin n → ℝ) (fuel : ℕ) : M (BidiagState m n) :=
  (List.range fuel).foldlM (fun s _ => bidiagStep rnd B C s)
    { k := 0, v := fun _ => 0, u := fun _ => 0, alpha := fun _ => 0, beta := fun _ => 0,
      p := v₀, done := false }

/-- **Algorithm 10.4.1** of [golub2013matrix] (Golub–Kahan bidiagonalization). Given
$A \in \mathbb{R}^{m \times n}$ with full column rank and a unit vector $v_c \in \mathbb{R}^n$,
the algorithm computes the factorization $AV = UB$:
```
k = 0, p_0 = v_c, β_0 = 1, u_0 = 0
while β_k ≠ 0
  v_{k+1} = p_k/β_k,  k = k + 1
  r_k = A v_k − β_{k−1} u_{k−1},  α_k = ‖r_k‖₂,  u_k = r_k/α_k
  p_k = Aᵀ u_k − α_k v_k,  β_k = ‖p_k‖₂
end
```

The program is `GolubVanLoan.Chapter10.bidiagLoop` for the pair $(A, A^T)$. The `while` loop is
at most `fuel` passes, and every arithmetic result passes through the rounding hook `rnd`. The
exact semantics is `GolubVanLoan.Chapter10.algorithm_10_4_1_spec`.

**Reading.** Same upper recurrence with bounded fuel and totalized division.
-/
noncomputable def algorithm_10_4_1 (A : Matrix (Fin m) (Fin n) ℝ) (vc : Fin n → ℝ) (fuel : ℕ) :
    M (BidiagState m n) :=
  bidiagLoop rnd A Aᵀ vc fuel

/-- **Algorithm 10.4.2** of [golub2013matrix] (Paige–Saunders lower bidiagonalization). Given
$A \in \mathbb{R}^{m \times n}$ such that $A(1:n, 1:n)$ is nonsingular and a unit vector
$u_c \in \mathbb{R}^m$, the algorithm computes the factorization
$AV(:, 1:k) = U(:, 1:k+1) B(1:k+1, 1:k)$:
```
k = 1, p_0 = u_c, β_1 = 1, v_0 = 0
while β_k > 0
  u_k = p_{k−1}/β_k,  r_k = Aᵀ u_k − β_k v_{k−1},  α_k = ‖r_k‖₂,  v_k = r_k/α_k
  p_k = A v_k − α_k u_k,  β_{k+1} = ‖p_k‖₂,  k = k + 1
end
```

**Typo.** The source states $u_c \in \mathbb{R}^n$. The vector $u_c$ is multiplied by $A^T$, so
$u_c \in \mathbb{R}^m$.

The program is `GolubVanLoan.Chapter10.bidiagLoop` for the pair $(A^T, A)$: the right vectors
`v` of the state are the source's $u_k$, and its left vectors `u` are the source's $v_k$. The
exact semantics is `GolubVanLoan.Chapter10.algorithm_10_4_2_spec`. -/
noncomputable def algorithm_10_4_2 (A : Matrix (Fin m) (Fin n) ℝ) (uc : Fin m → ℝ) (fuel : ℕ) :
    M (BidiagState n m) :=
  bidiagLoop rnd Aᵀ A uc fuel

end BidiagProgram

/-- If $c \ge 0$, $x$ is a unit vector unless $x = 0$, and $x = 0$ forces $c = 0$, then
$\|c x\| = c$. -/
private theorem norm_smul_of_unit_or {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ≠ 0 → ‖x‖ = 1) (h0 : x = 0 → c = 0) :
    ‖c • x‖ = c := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  rcases eq_or_ne x 0 with h | h
  · rw [h0 h, zero_mul]
  · rw [hx h, mul_one]

/-- The exact run with $t + 1$ passes is one pass of `GolubVanLoan.Chapter10.bidiagStep` after the
exact run with $t$ passes. -/
private theorem bidiagLoop_succ {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (v₀ : Fin n → ℝ) (t : ℕ) :
    Id.run (bidiagLoop pure B C v₀ (t + 1)) =
      Id.run (bidiagStep pure B C (Id.run (bidiagLoop pure B C v₀ t))) := by
  simp only [bidiagLoop, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- Exact semantics of `GolubVanLoan.Chapter10.bidiagLoop` for the pair $(B, B^T)$. Let
$B \in \mathbb{R}^{m \times n}$ and let $v_0 \in \mathbb{R}^n$ be a unit vector. In exact
arithmetic the run ends with the step counter $\min(\mathrm{fuel}, g)$, where $g$ is the grade
of $v_0$ for $B^T B$, and for every $j$ below this counter the computed $v_{j+1}$, $u_{j+1}$,
$\alpha_{j+1}$, $\beta_{j+1}$ are the Golub–Kahan vectors and coefficients of $B$ from $v_0$.

**Reading.** The identities compare the attained vectors with the backbone's totalized
recurrences. When a normalization coefficient is zero, division returns the zero vector, which
is not a unit bidiagonalization vector. -/
theorem bidiagLoop_spec {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) {v₀ : Fin n → ℝ}
    (hv : ‖(WithLp.toLp 2 v₀ : EuclideanSpace ℝ (Fin n))‖ = 1) (fuel : ℕ) :
    let s := Id.run (bidiagLoop pure B Bᵀ v₀ fuel)
    let T := Matrix.toEuclideanLin B
    let Ts := Matrix.toEuclideanLin Bᵀ
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v₀
    s.k = min fuel (grade (Ts ∘ₗ T) q) ∧
      ∀ j < s.k, s.v j = (GolubKahan.rightVec T Ts q j).ofLp ∧
        s.u j = (GolubKahan.leftVec T Ts q j).ofLp ∧ s.alpha j = GolubKahan.alpha T Ts q j ∧
        s.beta j = GolubKahan.beta T Ts q j := by
  intro s T Ts q
  have hadj : LinearMap.IsAdjointPair (innerₛₗ ℝ).flip (innerₛₗ ℝ).flip T Ts :=
    LinearMap.isAdjointPair_inner_iff.2 fun u x => by
      have := Matrix.toEuclideanLin_conjTranspose_inner_left B x u
      rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hTx : ∀ x, (T x).ofLp = B *ᵥ x.ofLp := fun x => rfl
  have hTsx : ∀ x, (Ts x).ofLp = Bᵀ *ᵥ x.ofLp := fun x => rfl
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : ‖q‖ = 1 := hv
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hg : 0 < grade (Ts ∘ₗ T) q := Krylov.grade_pos_of_ne_zero _ _ hq0
  have hunit_r : ∀ j, GolubKahan.rightVec T Ts q j ≠ 0 → ‖GolubKahan.rightVec T Ts q j‖ = 1 :=
    fun j h => Arnoldi.norm_vec_eq_one_of_ne_zero _ _ h
  have hunit_l : ∀ j, GolubKahan.leftVec T Ts q j ≠ 0 → ‖GolubKahan.leftVec T Ts q j‖ = 1 :=
    fun j h => Arnoldi.norm_vec_eq_one_of_ne_zero _ _ h
  have halpha0 : ∀ j, GolubKahan.leftVec T Ts q j = 0 → GolubKahan.alpha T Ts q j = 0 :=
    fun j h => by rw [GolubKahan.alpha, h, inner_zero_left, map_zero]
  have hbeta0 : ∀ j, GolubKahan.rightVec T Ts q (j + 1) = 0 → GolubKahan.beta T Ts q j = 0 :=
    fun j h => by rw [GolubKahan.beta, h, inner_zero_left, map_zero]
  let P : ℕ → BidiagState m n → Prop := fun t s =>
    s.k = min t (grade (Ts ∘ₗ T) q) ∧ s.done = decide (grade (Ts ∘ₗ T) q ≤ s.k) ∧
      (∀ j < s.k, s.v j = (GolubKahan.rightVec T Ts q j).ofLp ∧
        s.u j = (GolubKahan.leftVec T Ts q j).ofLp ∧ s.alpha j = GolubKahan.alpha T Ts q j ∧
        s.beta j = GolubKahan.beta T Ts q j) ∧
      s.p = if s.k = 0 then v₀ else
        (GolubKahan.beta T Ts q (s.k - 1) • GolubKahan.rightVec T Ts q s.k).ofLp
  have hP : ∀ t, P t (Id.run (bidiagLoop pure B Bᵀ v₀ t)) := by
    intro t
    induction t with
    | zero =>
      refine ⟨by simp [bidiagLoop], ?_, fun j hj => ?_, by simp [bidiagLoop]⟩
      · simp [bidiagLoop, hg.ne']
      · simp [bidiagLoop] at hj
    | succ t ih =>
      rw [bidiagLoop_succ]
      set s := Id.run (bidiagLoop pure B Bᵀ v₀ t)
      obtain ⟨hk, hdone, hvec, hp⟩ := ih
      cases hsd : s.done with
      | true =>
        have hle : grade (Ts ∘ₗ T) q ≤ s.k := by simpa [hsd] using hdone.symm
        simp only [bidiagStep, hsd, ↓reduceIte, Id.run_pure]
        refine ⟨?_, hdone, hvec, hp⟩
        rw [hk] at hle ⊢
        omega
      | false =>
        have hlt : s.k < grade (Ts ∘ₗ T) q := by
          have : ¬ grade (Ts ∘ₗ T) q ≤ s.k := by simpa [hsd] using hdone.symm
          omega
        have hvk_ne : GolubKahan.rightVec T Ts q s.k ≠ 0 := by
          rw [GolubKahan.rightVec, Ne, Arnoldi.vec_eq_zero_iff]
          omega
        -- the new right vector
        have hvk : (if s.k = 0 then 1 else s.beta (s.k - 1))⁻¹ • s.p =
            (GolubKahan.rightVec T Ts q s.k).ofLp := by
          rcases Nat.eq_zero_or_pos s.k with h0 | hpos
          · simp only [hp, h0, ↓reduceIte, inv_one, one_smul]
            rw [GolubKahan.rightVec, Arnoldi.vec_zero _ q hq0, show ‖q‖ = 1 from hv]
            simp [q]
          · obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
            simp only [hp, hj, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
              Nat.add_sub_cancel]
            rw [(hvec j (by omega)).2.2.2]
            have hb : GolubKahan.beta T Ts q j ≠ 0 := by
              intro h
              apply hvk_ne
              rw [hj]
              exact GolubKahan.rightVec_eq_zero_of_beta_eq_zero _ _ _ h
            rw [WithLp.ofLp_smul, smul_smul, inv_mul_cancel₀ hb, one_smul]
        -- `r_k = B v_k − β_{k−1} u_{k−1} = α_k u_k`
        have hr : B *ᵥ (GolubKahan.rightVec T Ts q s.k).ofLp +
              (-(if s.k = 0 then 1 else s.beta (s.k - 1))) •
                (if s.k = 0 then 0 else s.u (s.k - 1)) =
            (GolubKahan.alpha T Ts q s.k • GolubKahan.leftVec T Ts q s.k).ofLp := by
          rcases Nat.eq_zero_or_pos s.k with h0 | hpos
          · simp only [h0, ↓reduceIte, smul_zero, add_zero]
            rw [← hTx, GolubKahan.apply_rightVec_zero]
            rfl
          · obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
            simp only [hj, add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
            rw [(hvec j (by omega)).2.1, (hvec j (by omega)).2.2.2, ← hTx,
              GolubKahan.apply_rightVec q hadj j]
            simp only [WithLp.ofLp_add, WithLp.ofLp_smul, RCLike.ofReal_real_eq_id, id]
            module
        have ha : ‖(WithLp.toLp 2 ((GolubKahan.alpha T Ts q s.k •
            GolubKahan.leftVec T Ts q s.k).ofLp) : EuclideanSpace ℝ (Fin m))‖ =
            GolubKahan.alpha T Ts q s.k := by
          rw [WithLp.toLp_ofLp]
          exact norm_smul_of_unit_or (GolubKahan.alpha_nonneg _ _ _ _) (hunit_l s.k)
            (halpha0 s.k)
        have huk : (GolubKahan.alpha T Ts q s.k)⁻¹ •
            (GolubKahan.alpha T Ts q s.k • GolubKahan.leftVec T Ts q s.k).ofLp =
            (GolubKahan.leftVec T Ts q s.k).ofLp := by
          by_cases h0 : GolubKahan.alpha T Ts q s.k = 0
          · rw [GolubKahan.leftVec_eq_zero_of_alpha_eq_zero _ _ _ h0]
            simp
          · rw [WithLp.ofLp_smul, smul_smul, inv_mul_cancel₀ h0, one_smul]
        -- `p_k = Bᵀ u_k − α_k v_k = β_k v_{k+1}`
        have hpk : Bᵀ *ᵥ (GolubKahan.leftVec T Ts q s.k).ofLp +
              (-GolubKahan.alpha T Ts q s.k) • (GolubKahan.rightVec T Ts q s.k).ofLp =
            (GolubKahan.beta T Ts q s.k • GolubKahan.rightVec T Ts q (s.k + 1)).ofLp := by
          rw [← hTsx, GolubKahan.adjoint_apply_leftVec q hadj s.k]
          simp only [WithLp.ofLp_add, WithLp.ofLp_smul, RCLike.ofReal_real_eq_id, id]
          module
        have hb : ‖(WithLp.toLp 2 ((GolubKahan.beta T Ts q s.k •
            GolubKahan.rightVec T Ts q (s.k + 1)).ofLp) : EuclideanSpace ℝ (Fin n))‖ =
            GolubKahan.beta T Ts q s.k := by
          rw [WithLp.toLp_ofLp]
          exact norm_smul_of_unit_or (GolubKahan.beta_nonneg _ _ _ _) (hunit_r (s.k + 1))
            (hbeta0 s.k)
        simp only [P, bidiagStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          Id.run_pure, vecDiv_spec, algorithm_1_1_3_spec, algorithm_1_1_2_spec, vecNorm_spec,
          zero_add]
        rw [hvk, hr, ha, huk, hpk, hb]
        refine ⟨by omega, ?_, fun j hj => ?_, by simp⟩
        · have hiff : GolubKahan.beta T Ts q s.k = 0 ↔ grade (Ts ∘ₗ T) q ≤ s.k + 1 := by
            rw [← Arnoldi.vec_eq_zero_iff]
            exact ⟨GolubKahan.rightVec_eq_zero_of_beta_eq_zero _ _ _, hbeta0 s.k⟩
          simp only [hiff]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · simp only [Function.update_of_ne hj.ne]
            exact hvec j hj
          · simp
  obtain ⟨hk, -, hvec, -⟩ := hP fuel
  exact ⟨hk, hvec⟩

/-- **Algorithm 10.4.1** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{m \times n}$,
let $v_c \in \mathbb{R}^n$ be a unit vector, and let $g$ be the grade of $v_c$ for $A^T A$. In
exact arithmetic, the run with at most `fuel` passes ends with $k = \min(\mathrm{fuel}, g)$, and
for $j = 1, \dots, k$ the computed $v_j$, $u_j$, $\alpha_j$ and $\beta_j$ are the Golub–Kahan
vectors and coefficients of $A$ from $v_c$. If moreover $A$ has full column rank, then every
computed $\alpha_j$ is positive, so that the loop never divides by zero.

**Generalization.** The source assumes that $A$ has full column rank. The identification with
the Golub–Kahan process holds for every $A$; full column rank is used only for $\alpha_j > 0$.

In 0-based indices the computed quantities are `GolubKahan.rightVec T Ts q (j - 1)`,
`GolubKahan.leftVec T Ts q (j - 1)`, `GolubKahan.alpha T Ts q (j - 1)` and
`GolubKahan.beta T Ts q (j - 1)`, and full column rank is `LinearMap.ker T = ⊥`. Each $\alpha_j$
and $\beta_j$ is a norm and so nonnegative (`GolubKahan.alpha_nonneg`). Positivity uses that the
grades of $v_c$ for $A^T A$ and of $A v_c$ for $A A^T$ agree when $\ker A = 0$
(`GolubKahan.grade_comp_adjoint_add_finrank`). The proof is an induction on an invariant of the
loop, with `GolubKahan.apply_rightVec` and `GolubKahan.adjoint_apply_leftVec`. -/
theorem algorithm_10_4_1_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {vc : Fin n → ℝ}
    (hv : ‖(WithLp.toLp 2 vc : EuclideanSpace ℝ (Fin n))‖ = 1) (fuel : ℕ) :
    let s := Id.run (algorithm_10_4_1 pure A vc fuel)
    let T := Matrix.toEuclideanLin A
    let Ts := Matrix.toEuclideanLin Aᵀ
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 vc
    s.k = min fuel (grade (Ts ∘ₗ T) q) ∧
      ∀ j < s.k, s.v j = (GolubKahan.rightVec T Ts q j).ofLp ∧
        s.u j = (GolubKahan.leftVec T Ts q j).ofLp ∧ s.alpha j = GolubKahan.alpha T Ts q j ∧
        s.beta j = GolubKahan.beta T Ts q j ∧
        (LinearMap.ker T = ⊥ → 0 < s.alpha j) := by
  intro s T Ts q
  obtain ⟨hk, hvec⟩ := bidiagLoop_spec A hv fuel
  refine ⟨hk, fun j hj => ⟨(hvec j hj).1, (hvec j hj).2.1, (hvec j hj).2.2.1, (hvec j hj).2.2.2,
    fun hker => ?_⟩⟩
  have hgr := GolubKahan.grade_comp_adjoint_add_finrank T Ts q
  rw [hker, inf_bot_eq, finrank_bot, add_zero] at hgr
  have hne : GolubKahan.leftVec T Ts q j ≠ 0 := by
    rw [GolubKahan.leftVec, Ne, Arnoldi.vec_eq_zero_iff, hgr]
    have : s.k = min fuel (grade (Ts ∘ₗ T) q) := hk
    omega
  have hα : GolubKahan.alpha T Ts q j ≠ 0 := fun h =>
    hne (GolubKahan.leftVec_eq_zero_of_alpha_eq_zero _ _ _ h)
  have hsα : s.alpha j = GolubKahan.alpha T Ts q j := (hvec j hj).2.2.1
  rw [hsα]
  exact lt_of_le_of_ne (GolubKahan.alpha_nonneg _ _ _ _) (Ne.symm hα)

/-- **Algorithm 10.4.2** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{m \times n}$,
let $u_c \in \mathbb{R}^m$ be a unit vector, and let $g$ be the grade of $u_c$ for $A A^T$. In
exact arithmetic, the run with at most `fuel` passes ends with the step counter
$\min(\mathrm{fuel}, g)$, and for every $j$ up to this counter the computed $u_j$, $v_j$,
$\alpha_j$ and $\beta_{j+1}$ are the Golub–Kahan vectors and coefficients of $A^T$ from $u_c$.
So Algorithm 10.4.2 is Algorithm 10.4.1 for $A^T$ from $u_c$.

**Generalization.** The source assumes that $A(1:n, 1:n)$ is nonsingular. The identification
holds for every $A$. This hypothesis is also not what the algorithm needs to avoid a division by
zero; that is full column rank.

In 0-based indices the computed quantities are `GolubKahan.rightVec T Ts q (j - 1)`,
`GolubKahan.leftVec T Ts q (j - 1)`, `GolubKahan.alpha T Ts q (j - 1)` and
`GolubKahan.beta T Ts q (j - 1)` for `T = Matrix.toEuclideanLin Aᵀ` and
`Ts = Matrix.toEuclideanLin A`.

**Limitation.** The source assumes a nonsingular leading square block, which can still give
$A^T u_c = 0$ for a rectangular matrix. For example, $A=(1,0)^T$ and $u_c=(0,1)^T$ produce
$\alpha_1=0$. The exact theorem identifies the totalized vectors and coefficients. It does not
assert that a vector computed by division by a zero coefficient is a unit basis vector. -/
theorem algorithm_10_4_2_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {uc : Fin m → ℝ}
    (hu : ‖(WithLp.toLp 2 uc : EuclideanSpace ℝ (Fin m))‖ = 1) (fuel : ℕ) :
    let s := Id.run (algorithm_10_4_2 pure A uc fuel)
    let T := Matrix.toEuclideanLin Aᵀ
    let Ts := Matrix.toEuclideanLin A
    let q : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 uc
    s.k = min fuel (grade (Ts ∘ₗ T) q) ∧
      ∀ j < s.k, s.v j = (GolubKahan.rightVec T Ts q j).ofLp ∧
        s.u j = (GolubKahan.leftVec T Ts q j).ofLp ∧ s.alpha j = GolubKahan.alpha T Ts q j ∧
        s.beta j = GolubKahan.beta T Ts q j := by
  have h := bidiagLoop_spec Aᵀ hu fuel
  rwa [transpose_transpose] at h

/-! ### The tridiagonal–bidiagonal connection (§10.4.3) -/

/-- **Section 10.4.3** of [golub2013matrix], the tridiagonal–bidiagonal connection, with
(10.4.16)–(10.4.17). Let $A \in \mathbb{R}^{m \times n}$, $v_c \in \mathbb{R}^n$ and $k \ge 0$.
Let
$$C = \begin{bmatrix} 0 & A^T \\ A & 0 \end{bmatrix} \in \mathbb{R}^{(n+m) \times (n+m)},$$
and let $T_k$ be the $k \times k$ Lanczos tridiagonal matrix of $C$ from $(v_c, 0)$. Then $T_k$
has zero diagonal and the off-diagonal $\alpha_1, \beta_1, \alpha_2, \beta_2, \dots$, where
$\alpha_j$ and $\beta_j$ are the Golub–Kahan coefficients of $A$ from $v_c$:
$$T_k = \begin{bmatrix} 0 & \alpha_1 & & & \\ \alpha_1 & 0 & \beta_1 & & \\ & \beta_1 & 0 &
  \alpha_2 & \\ & & \alpha_2 & 0 & \ddots \\ & & & \ddots & \ddots \end{bmatrix}.$$

The source's matrix is $\begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix}$ on $\mathbb{R}^{m+n}$
with the starting vector $(0, v_c)$. Here the two blocks are exchanged; the two operators differ
by a permutation of the blocks and have the same Lanczos coefficients. In 0-based indices the
entry $(i, i+1)$ is `GolubKahan.alpha T Ts v (i / 2)` for even $i$ and
`GolubKahan.beta T Ts v (i / 2)` for odd $i$. The matrix $C$ is the Hermitian dilation
`LinearMap.hermitianDilation` in coordinates. The proof carries
`GolubKahan.lanczos_jordanWielandt` to coordinates by `Arnoldi.coeff_conj_linearIsometryEquiv`
along `PiLp.sumPiLpEquivProdLpPiLp`.

**Reading.** Canonical block swap with same alternating entries, allows all shapes, orders and
starting vectors.
-/
theorem lanczos_jordanWielandt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Lanczos.tridiag (toEuclideanLin (Matrix.fromBlocks 0 Aᵀ A 0))
        (WithLp.toLp 2 (Sum.elim v.ofLp 0)) k =
      Matrix.of fun i j : Fin k =>
        if (i : ℕ) + 1 = j then
          (if (i : ℕ) % 2 = 0 then GolubKahan.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) v (i / 2)
            else GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (i / 2))
        else if (j : ℕ) + 1 = i then
          (if (j : ℕ) % 2 = 0 then GolubKahan.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) v (j / 2)
            else GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (j / 2))
        else 0 := by
  have hadj : LinearMap.IsAdjointPair (innerₛₗ ℝ).flip (innerₛₗ ℝ).flip (toEuclideanLin A)
      (toEuclideanLin Aᵀ) :=
    LinearMap.isAdjointPair_inner_iff.2 fun u x => by
      have := Matrix.toEuclideanLin_conjTranspose_inner_left A x u
      rwa [conjTranspose_eq_transpose_of_trivial] at this
  set e := (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin n ⊕ Fin m => ℝ)).symm with he
  set D := LinearMap.hermitianDilation (toEuclideanLin A) (toEuclideanLin Aᵀ) with hD
  have hconj : e.toLinearEquiv.conj D = toEuclideanLin (Matrix.fromBlocks 0 Aᵀ A 0) := by
    refine LinearMap.ext fun z => ?_
    ext (i | i) <;>
      simp [e, D, LinearEquiv.conj_apply, Matrix.fromBlocks_mulVec, Matrix.toEuclideanLin_apply,
        LinearMap.hermitianDilation_apply] <;> rfl
  have hb : e (WithLp.toLp 2 (v, 0)) = WithLp.toLp 2 (Sum.elim v.ofLp 0) := by
    ext (i | i) <;> simp [e]
  rw [← hconj, ← hb, Lanczos.tridiag_eq_of_coeff_eq (Arnoldi.coeff_conj_linearIsometryEquiv _ _ _),
    GolubKahan.lanczos_jordanWielandt v hadj]

end GolubVanLoan.Chapter10
