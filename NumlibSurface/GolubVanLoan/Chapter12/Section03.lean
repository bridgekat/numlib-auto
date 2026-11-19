/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.Kronecker.Spectral
import Numlib.LinearAlgebra.Matrix.KroneckerApprox
import Numlib.LinearAlgebra.Matrix.QR
import NumlibSurface.GolubVanLoan.Chapter01.Section03

/-!
# Golub and Van Loan, Section 12.3: Kronecker product computations

This module formalizes §12.3 of [golub2013matrix]. For $B \in \mathbb{R}^{m_1 \times n_1}$ and
$C \in \mathbb{R}^{m_2 \times n_2}$, the Kronecker product $B \otimes C \in \mathbb{R}^{m_1 m_2
\times n_1 n_2}$ is the block matrix with the blocks $b_{ij} C$. The module proves the properties of
§12.3.1: the perfect shuffle identity (12.3.1), Kronecker products of permutation matrices (12.3.2),
the structures and factorizations that the Kronecker product preserves, the Schur decomposition and
the eigenvalues (12.3.3), the SVD and the singular values (12.3.4), and the rank, determinant, trace
and norms. It treats the Tracy–Singh product (12.3.5)–(12.3.8), the Hadamard and Khatri–Rao products
(§12.3.3), the operations vec and reshape (12.3.9)–(12.3.12), and the two-pass transposition of
§12.3.5. For the nearest Kronecker product problems it uses the rearrangement $\mathcal{R}(A)$,
which permutes the entries of $A$ and turns $\min \|A - B \otimes C\|_F$ into a nearest rank-one
problem for $\mathcal{R}(A)$. This gives (12.3.14)–(12.3.15), the Kronecker product SVD of Theorem
12.3.1, the nearest sums of Kronecker products (12.3.19), and the nearest $X \otimes X$ and
$X \otimes Y - Y \otimes X$ with Lemmas 12.3.2–12.3.3 and (12.3.20)–(12.3.21). The module ends with
the reshaping identity of §12.3.10.

The proofs specialize `Numlib.LinearAlgebra.Matrix.Kronecker`,
`Numlib.LinearAlgebra.Matrix.Kronecker.Spectral` and `Numlib.LinearAlgebra.Matrix.KroneckerApprox`,
and the Eckart–Young–Mirsky theorem `Matrix.isLeast_frobenius_norm_sub_of_rank_le` for competitors
of rank at most $\tilde r$. They use (1.3.5) and (1.3.6) of Chapter 1
(`GolubVanLoan.Chapter01.equation_1_3_5`, `GolubVanLoan.Chapter01.equation_1_3_6`).

## Main definitions

* §12.3.2, `GolubVanLoan.Chapter12.tracySinghFin`: the Tracy–Singh product $B \otimes_{TS} C$ of two
  block matrices.
* §12.3.3, `GolubVanLoan.Chapter12.blockKhatriRao`: the block Khatri–Rao product, with the blocks
  $B_{ij} \otimes C_{ij}$.
* `GolubVanLoan.Chapter12.reshapeVec`: the source's $\operatorname{reshape}(a, m, n)$, the matrix
  $A$ with $\operatorname{vec}(A) = a$.
* §12.3.6, `GolubVanLoan.Chapter12.rearrangement`: the rearrangement $\mathcal{R}(A)$, whose rows
  are $\operatorname{vec}(A_{ij})^T$.

## Main results

* Equation (12.3.1), `GolubVanLoan.Chapter12.equation_12_3_1`: $\mathcal{P}_{m_1,m_2} (B \otimes C)
  \mathcal{P}_{n_1,n_2}^T = C \otimes B$.
* Equation (12.3.2), `GolubVanLoan.Chapter12.equation_12_3_2`:
  $I_m(p, :) \otimes I_n(q, :) = I_{mn}(w, :)$ with an explicit permutation $w$.
* §12.3.1, `GolubVanLoan.Chapter12.kronecker_structure_preserved`: Kronecker products of orthogonal,
  stochastic or symmetric positive definite matrices have the same property.
* §12.3.1, `GolubVanLoan.Chapter12.kronecker_factorizations`: the Cholesky, LU and QR factorizations
  of $B \otimes C$ are Kronecker products of those of $B$ and $C$.
* §12.3.1, `GolubVanLoan.Chapter12.kronecker_thin_qr`: the thin pivoted QR factorization of
  $B \otimes C$.
* Equation (12.3.3), `GolubVanLoan.Chapter12.equation_12_3_3`: the Schur decomposition of
  $B \otimes C$, and $\lambda(B \otimes C) = \{\beta_i \gamma_j\}$.
* Equation (12.3.4), `GolubVanLoan.Chapter12.equation_12_3_4`: the SVD of $B \otimes C$, and its
  singular values are the products of those of $B$ and $C$.
* §12.3.1, `GolubVanLoan.Chapter12.kronecker_invariants`: eigenvectors, rank, determinant and trace
  of $B \otimes C$.
* §12.3.1, `GolubVanLoan.Chapter12.kronecker_frobenius_norm` and
  `GolubVanLoan.Chapter12.kronecker_l2_norm`: $\|B \otimes C\| = \|B\| \|C\|$ in the Frobenius norm
  and in the 2-norm.
* Equations (12.3.5)–(12.3.6), `GolubVanLoan.Chapter12.equation_12_3_6`:
  $B \otimes_{TS} C = P (B \otimes C) Q^T$ for permutation matrices $P$ and $Q$.
* Equations (12.3.7)–(12.3.8), `GolubVanLoan.Chapter12.equation_12_3_7`: $P$ and $Q$ as products of
  perfect shuffles.
* §12.3.3, `GolubVanLoan.Chapter12.hadamard_khatriRao_submatrix_kronecker`: the Hadamard and
  Khatri–Rao products are submatrices of the Kronecker and Tracy–Singh products.
* Equation (12.3.9), `GolubVanLoan.Chapter12.equation_12_3_9`: $Y = C X B^T$ if and only if
  $\operatorname{vec}(Y) = (B \otimes C) \operatorname{vec}(X)$.
* Equations (12.3.10)–(12.3.11), `GolubVanLoan.Chapter12.equation_12_3_11`: the vec form of
  $\sum_k F_k X G_k^T = C$.
* Equation (12.3.12), `GolubVanLoan.Chapter12.equation_12_3_12`: $\operatorname{vec}(A^T) =
  \mathcal{P}_{r,q} \operatorname{vec}(A)$.
* §12.3.5, `GolubVanLoan.Chapter12.perfectShuffle_two_pass`: the two-pass transposition, in
  corrected form.
* Equation (12.3.14), `GolubVanLoan.Chapter12.equation_12_3_14`: $\|A - B \otimes C\|_F =
  \|\mathcal{R}(A) - \operatorname{vec}(B) \operatorname{vec}(C)^T\|_F$.
* Equation (12.3.15), `GolubVanLoan.Chapter12.equation_12_3_15`: the nearest Kronecker product from
  the leading singular triple of $\mathcal{R}(A)$.
* Theorem 12.3.1, `GolubVanLoan.Chapter12.theorem_12_3_1`: the Kronecker product SVD.
* Equation (12.3.19), `GolubVanLoan.Chapter12.equation_12_3_19`: the truncated Kronecker product SVD
  is a nearest sum of $\tilde r$ Kronecker products.
* Equation (12.3.20), `GolubVanLoan.Chapter12.equation_12_3_20`: $\|A - X \otimes X\|_F =
  \|\mathcal{R}(A) - \operatorname{vec}(X) \operatorname{vec}(X)^T\|_F$.
* Lemma 12.3.2, `GolubVanLoan.Chapter12.lemma_12_3_2`: the nearest symmetric matrix of rank at most
  one, in corrected form.
* §12.3.8, `GolubVanLoan.Chapter12.nearest_kronecker_self`: the nearest $X \otimes X$, in corrected
  form.
* Equation (12.3.21), `GolubVanLoan.Chapter12.equation_12_3_21`: the same identity for
  $X \otimes Y - Y \otimes X$.
* Lemma 12.3.3, `GolubVanLoan.Chapter12.lemma_12_3_3`: the nearest skew-symmetric matrix of rank at
  most two, in corrected form.
* §12.3.10, `GolubVanLoan.Chapter12.kronecker_mulVec_reshape`: $\operatorname{reshape}((P \otimes Q)
  x) = Q \operatorname{reshape}(x) P^T$.

## Conventions

* Where the positional layout of the source matters (perfect shuffles, vec, reshape and
  $\mathcal{R}$), matrices are indexed by `Fin`, and $B \otimes C$ is the Kronecker product
  `Matrix.kroneckerFin B C` of Chapter 1. Its block $(i, j)$ is $b_{ij} C$, and its row $(i_1, i_2)$
  is at the 0-based position $i_2 + m_2 i_1$. The column stacking $\operatorname{vec}$ is
  `Matrix.vecFin`, which puts the entry $(i, j)$ at the position $i + mj$. Statements that do not
  depend on the layout use Mathlib's Kronecker product `B ⊗ₖ C` on product index types.
* The perfect shuffle $\mathcal{P}_{p,r}$ is `Matrix.perfectShuffle p r`. Where two products of
  sizes, such as $rq \cdot q$ and $q \cdot rq$, must be identified, the statement uses `finCongr`.

## Implementation notes

* The four basic identities of §12.3.1 (transpose, inverse, product and associativity) are
  (1.3.1)–(1.3.4) of Chapter 1, and they are not restated here.
* The rearrangement $\mathcal{R}(A)$ is the backbone's typed `Matrix.kroneckerRearrange`, read
  through `finProdFinEquiv`. It permutes the entries, so every nearest Kronecker product problem is
  a nearest low-rank problem for $\mathcal{R}(A)$.
* Lemma 12.3.2 and §12.3.8 are stated for an arbitrary Schur decomposition
  $Q^T T Q = \operatorname{diag}(\alpha)$ of the symmetric part $T = (M + M^T)/2$, as in the source.
  The symmetric part is `Matrix.hermitianPart M`.

## Deviations from the source

* **Equations (12.3.3)–(12.3.4)** (reading). The Kronecker congruences require only the two
  factor identities. The SVD statement uses real matrices and column-indexed singular values.
  See `GolubVanLoan.Chapter12.equation_12_3_3` and `GolubVanLoan.Chapter12.equation_12_3_4`.
* **Theorem 12.3.1 and (12.3.19)** (generalization). The exact expansion accepts arbitrary outer
  products. The truncation may include zero singular values. See
  `GolubVanLoan.Chapter12.theorem_12_3_1` and `GolubVanLoan.Chapter12.equation_12_3_19`.
* **Equation (12.3.9)** (typo). The source states $X \in \mathbb{R}^{n_1 \times m_2}$ for
  $X \in \mathbb{R}^{n_2 \times n_1}$. See `GolubVanLoan.Chapter12.equation_12_3_9`.
* **§12.3.5, the two-pass transposition** (correction). The source prints
  $\Gamma_1 = \mathcal{P}_{r,q} \otimes I_q$, which generally has the opposite shuffle
  orientation, and announces a factorization of $\mathcal{P}_{rq,q}$ before it writes
  $\mathcal{P}_{q,rq}$. See
  `GolubVanLoan.Chapter12.perfectShuffle_two_pass`.
* **Equation (12.3.21)** (typo). The source writes $\phi_{skew}(X)$ for $\phi_{skew}(X, Y)$ and
  drops a parenthesis. See `GolubVanLoan.Chapter12.equation_12_3_21`.
* **Lemma 12.3.2** (correction). The minimum over $\operatorname{rank}(Z) = 1$ is not attained for
  $T = 0$; the statement uses $\operatorname{rank}(Z) \le 1$. See
  `GolubVanLoan.Chapter12.lemma_12_3_2`.
* **§12.3.8, the nearest $X \otimes X$** (correction). The eigenvalue must be the algebraically
  largest one, not one of largest modulus, and it enters through its positive part. See
  `GolubVanLoan.Chapter12.nearest_kronecker_self`.
* **Lemma 12.3.3** (correction). For $S = 0$ the minimizer has rank $0$; the statement minimizes
  over rank at most two. See `GolubVanLoan.Chapter12.lemma_12_3_3`.
* **Lemma 12.3.3** (generalization). Of the hypothesis $S [u \,|\, v] = [u \,|\, v] \begin{bmatrix}
  0 & \mu \\ -\mu & 0 \end{bmatrix}$ only $Sv = \mu u$ is needed. See
  `GolubVanLoan.Chapter12.lemma_12_3_3`.

## Not formalized

* **§12.3.7, constrained nearest Kronecker products.** The positive definiteness and the
  nonnegativity of $B_{opt}$ and $C_{opt}$ are cited without proof, and the reduction for Toeplitz
  constraints is a method sketch.
* **The memory-hierarchy discussion of multipass transposition in §12.3.5**, beyond the two-pass
  identity.
* **The dynamic-programming remark of §12.3.10**, beyond the reshaping identity.
* **The remark of §12.3.1 that rectangular $R$ factors need row permutations to become triangular.**
  It is prose.
* **The small numerical examples.** Numerical examples are out of scope for the library.
* **The operation counts.** Operation counts are out of scope for the library.
* **The Problems of §12.3.** Problems are out of scope for the library.
-/

open Matrix
open scoped Kronecker

namespace GolubVanLoan.Chapter12

variable {m₁ n₁ m₂ n₂ : ℕ}

/-! ### §12.3.1: basic properties -/

/-- **Equation (12.3.1)** of [golub2013matrix]. Let $B \in \mathbb{R}^{m_1 \times n_1}$ and
$C \in \mathbb{R}^{m_2 \times n_2}$. Then $$\mathcal{P}_{m_1,m_2} (B \otimes C)
\mathcal{P}_{n_1,n_2}^T = C \otimes B,$$ where $\mathcal{P}_{p,r}$ is the perfect shuffle
permutation matrix.

This is (1.3.5) of Chapter 1, `GolubVanLoan.Chapter01.equation_1_3_5`. The product $B \otimes C$
is `Matrix.kroneckerFin B C`. The perfect shuffle $\mathcal{P}_{p,r}$ is
`Matrix.perfectShuffle p r`. -/
theorem equation_12_3_1 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    perfectShuffle m₁ m₂ * kroneckerFin B C *
        (perfectShuffle n₁ n₂ : Matrix (Fin (n₂ * n₁)) (Fin (n₁ * n₂)) ℝ)ᵀ =
      kroneckerFin C B :=
  Chapter01.equation_1_3_5 B C

/-- The row permutation $w$ of (12.3.2) in [golub2013matrix]: in the positional layout of the index
pairs, it maps the pair $(i, j)$ to $(p_i, q_j)$. -/
def kroneckerPermIndex {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m * n)) :=
  finProdFinEquiv.symm.trans ((p.prodCongr q).trans finProdFinEquiv)

/-- **Equation (12.3.2)** of [golub2013matrix]. Let $p$ be a permutation of $1{:}m$ and $q$ a
permutation of $1{:}n$. Then $$I_m(p, :) \otimes I_n(q, :) = I_{mn}(w, :),$$ where $w =
(\mathbf{1}_m \otimes q) + n \cdot (p - \mathbf{1}_m) \otimes \mathbf{1}_n$; with 0-based
indices, $w(in + j) = q_j + n p_i$. In particular, the Kronecker product of two permutation
matrices is a permutation matrix.

The permutation $w$ is `GolubVanLoan.Chapter12.kroneckerPermIndex p q`. -/
theorem equation_12_3_2 {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n)) :
    kroneckerFin ((1 : Matrix (Fin m) (Fin m) ℝ).submatrix p id)
        ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix q id) =
      (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ).submatrix (kroneckerPermIndex p q) id ∧
    ∀ i j, (kroneckerPermIndex p q (finProdFinEquiv (i, j)) : ℕ) = q j + n * p i := by
  refine ⟨?_, fun i j => by simp [kroneckerPermIndex, finProdFinEquiv_apply_val]⟩
  ext I J
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective J
  simp only [kroneckerFin_apply, submatrix_apply, id, Matrix.one_apply, kroneckerPermIndex,
    Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  rw [ite_zero_mul_ite_zero, one_mul]

/-- **§12.3.1** of [golub2013matrix], structure preserved by the Kronecker product. Let
$B \in \mathbb{R}^{m \times m}$ and $C \in \mathbb{R}^{n \times n}$. If $B$ and $C$ are
orthogonal, then $B \otimes C$ is orthogonal. If $B$ and $C$ are stochastic, then $B \otimes C$
is stochastic. If $B$ and $C$ are symmetric positive definite, then $B \otimes C$ is symmetric
positive definite. If $B = G_B G_B^T$ and $C = G_C G_C^T$, then $$B \otimes C = (G_B \otimes
G_C)(G_B \otimes G_C)^T.$$

The Kronecker product is Mathlib's `B ⊗ₖ C`, and a stochastic matrix is an element of
`Matrix.rowStochastic`. -/
theorem kronecker_structure_preserved {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    (B ∈ orthogonalGroup (Fin m) ℝ → C ∈ orthogonalGroup (Fin n) ℝ →
      B ⊗ₖ C ∈ orthogonalGroup (Fin m × Fin n) ℝ) ∧
    (B ∈ rowStochastic ℝ (Fin m) → C ∈ rowStochastic ℝ (Fin n) →
      B ⊗ₖ C ∈ rowStochastic ℝ (Fin m × Fin n)) ∧
    (B.PosDef → C.PosDef → (B ⊗ₖ C).PosDef) ∧
    ∀ G_B G_C : Matrix _ _ ℝ, B = G_B * G_Bᵀ → C = G_C * G_Cᵀ →
      B ⊗ₖ C = (G_B ⊗ₖ G_C) * (G_B ⊗ₖ G_C)ᵀ :=
  ⟨fun hB hC => kronecker_mem_unitary hB hC, kronecker_mem_rowStochastic, PosDef.kronecker,
    fun G_B G_C hB hC => by rw [hB, hC, mul_kronecker_mul, kroneckerMap_transpose]⟩

/-- If $Q_1 \in \mathbb{R}^{m \times m}$ and $Q_2 \in \mathbb{R}^{n \times n}$ are orthogonal, then
their Kronecker product $Q_1 \otimes Q_2$ in the positional layout is orthogonal. -/
theorem kroneckerFin_mem_orthogonalGroup {m n : ℕ} {Q₁ : Matrix (Fin m) (Fin m) ℝ}
    {Q₂ : Matrix (Fin n) (Fin n) ℝ} (h₁ : Q₁ ∈ orthogonalGroup (Fin m) ℝ)
    (h₂ : Q₂ ∈ orthogonalGroup (Fin n) ℝ) :
    kroneckerFin Q₁ Q₂ ∈ orthogonalGroup (Fin (m * n)) ℝ := by
  rw [mem_orthogonalGroup_iff] at h₁ h₂ ⊢
  rw [transpose_kroneckerFin, kroneckerFin_mul_kroneckerFin, h₁, h₂, kroneckerFin_one_one]

/-- **§12.3.1** of [golub2013matrix], factorizations of a Kronecker product. Let
$B \in \mathbb{R}^{m \times m}$ and $C \in \mathbb{R}^{n \times n}$. If $B = H_B^T H_B$ and
$C = H_C^T H_C$ are Cholesky factorizations, with $H_B$ and $H_C$ upper triangular with positive
diagonal, then $B \otimes C = (H_B \otimes H_C)^T (H_B \otimes H_C)$ is the Cholesky
factorization of $B \otimes C$. If $P_B B = L_B U_B$ and $P_C C = L_C U_C$ are LU
factorizations, for any matrices $P_B$ and $P_C$, then $$(P_B \otimes P_C)(B \otimes C) = (L_B
\otimes L_C)(U_B \otimes U_C)$$ is an LU factorization. If $B = Q_B R_B$ and $C = Q_C R_C$ are
QR factorizations, then $B \otimes C = (Q_B \otimes Q_C)(R_B \otimes R_C)$ is a QR
factorization.

All Kronecker products are in the positional layout of the source. The factorizations are
`Matrix.IsCholesky`, `Matrix.IsLU` and `Matrix.IsQR`. The thin pivoted QR factorization is
`GolubVanLoan.Chapter12.kronecker_thin_qr`. -/
theorem kronecker_factorizations {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    (∀ H_B H_C, IsCholesky B H_B → IsCholesky C H_C →
      IsCholesky (kroneckerFin B C) (kroneckerFin H_B H_C)) ∧
    (∀ P_B L_B U_B P_C L_C U_C, IsLU (P_B * B) L_B U_B → IsLU (P_C * C) L_C U_C →
      IsLU (kroneckerFin P_B P_C * kroneckerFin B C) (kroneckerFin L_B L_C)
        (kroneckerFin U_B U_C)) ∧
    (∀ Q_B R_B Q_C R_C, IsQR B Q_B R_B → IsQR C Q_C R_C →
      IsQR (kroneckerFin B C) (kroneckerFin Q_B Q_C) (kroneckerFin R_B R_C)) := by
  refine ⟨fun _ _ hB hC => hB.kroneckerFin hC, fun P_B L_B U_B P_C L_C U_C hB hC => ?_,
    fun Q_B R_B Q_C R_C hB hC => ?_⟩
  · rw [kroneckerFin_mul_kroneckerFin]
    exact hB.kroneckerFin hC
  · have hRB : R_B.IsUpperTriangular := fun i j h => hB.apply_eq_zero i j h
    have hRC : R_C.IsUpperTriangular := fun i j h => hC.apply_eq_zero i j h
    refine ⟨kroneckerFin_mem_orthogonalGroup hB.mem_unitaryGroup hC.mem_unitaryGroup,
      fun i j h => (hRB.kroneckerFin hRC) h, ?_⟩
    rw [kroneckerFin_mul_kroneckerFin, hB.mul_eq, hC.mul_eq]

/-- **§12.3.1** of [golub2013matrix], the thin pivoted QR factorization of a Kronecker product. Let
$B \in \mathbb{R}^{m_1 \times n_1}$ and $C \in \mathbb{R}^{m_2 \times n_2}$, let $P_B$ and $P_C$
be permutation matrices, and let $B P_B = Q_B R_B$ and $C P_C = Q_C R_C$, where
$Q_B \in \mathbb{R}^{m_1 \times n_1}$ and $Q_C \in \mathbb{R}^{m_2 \times n_2}$ have orthonormal
columns and $R_B \in \mathbb{R}^{n_1 \times n_1}$ and $R_C \in \mathbb{R}^{n_2 \times n_2}$ are
upper triangular. Then $$(B \otimes C)(P_B \otimes P_C) = (Q_B \otimes Q_C)(R_B \otimes R_C),$$
$Q_B \otimes Q_C$ has orthonormal columns, and $R_B \otimes R_C$ is upper triangular.

The source's remark that rectangular $R$ factors need row permutations to become triangular is
prose and is not formalized. -/
theorem kronecker_thin_qr {m₁ n₁ m₂ n₂ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) (P_B : Equiv.Perm (Fin n₁)) (P_C : Equiv.Perm (Fin n₂))
    (Q_B : Matrix (Fin m₁) (Fin n₁) ℝ) (R_B : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Q_C : Matrix (Fin m₂) (Fin n₂) ℝ) (R_C : Matrix (Fin n₂) (Fin n₂) ℝ)
    (hB : B * P_B.permMatrix ℝ = Q_B * R_B) (hC : C * P_C.permMatrix ℝ = Q_C * R_C)
    (hQB : Q_Bᵀ * Q_B = 1) (hQC : Q_Cᵀ * Q_C = 1) (hRB : R_B.IsUpperTriangular)
    (hRC : R_C.IsUpperTriangular) :
    kroneckerFin B C * kroneckerFin (P_B.permMatrix ℝ) (P_C.permMatrix ℝ) =
        kroneckerFin Q_B Q_C * kroneckerFin R_B R_C ∧
      (kroneckerFin Q_B Q_C)ᵀ * kroneckerFin Q_B Q_C = 1 ∧
      (kroneckerFin R_B R_C).IsUpperTriangular := by
  refine ⟨?_, ?_, hRB.kroneckerFin hRC⟩
  · rw [kroneckerFin_mul_kroneckerFin, kroneckerFin_mul_kroneckerFin, hB, hC]
  · rw [transpose_kroneckerFin, kroneckerFin_mul_kroneckerFin, hQB, hQC, kroneckerFin_one_one]

/-- **Equation (12.3.3)** of [golub2013matrix] and the display before it. Let
$B, Q_B, T_B \in \mathbb{C}^{m \times m}$ and $C, Q_C, T_C \in \mathbb{C}^{n \times n}$ with
$Q_B^H B Q_B = T_B$ and $Q_C^H C Q_C = T_C$. Then $$(Q_B \otimes Q_C)^H (B \otimes C)(Q_B
\otimes Q_C) = T_B \otimes T_C,$$ and $T_B \otimes T_C$ is upper triangular if $T_B$ and $T_C$
are. Hence $\lambda(B \otimes C) = \{\beta_i \gamma_j\}$: if the characteristic polynomials of
$B$ and $C$ are $\prod_i (x - \beta_i)$ and $\prod_j (x - \gamma_j)$, then the characteristic
polynomial of $B \otimes C$ is $\prod_{i,j} (x - \beta_i \gamma_j)$.

The identity does not need $Q_B$ and $Q_C$ to be unitary.

**Generalization.** The congruence identity holds for arbitrary factors satisfying the two
input equalities. The spectral products are stated with characteristic multiplicities. -/
theorem equation_12_3_3 {m n : ℕ} (B Q_B T_B : Matrix (Fin m) (Fin m) ℂ)
    (C Q_C T_C : Matrix (Fin n) (Fin n) ℂ) (hB : Q_Bᴴ * B * Q_B = T_B)
    (hC : Q_Cᴴ * C * Q_C = T_C) :
    (kroneckerFin Q_B Q_C)ᴴ * kroneckerFin B C * kroneckerFin Q_B Q_C = kroneckerFin T_B T_C ∧
      (T_B.IsUpperTriangular → T_C.IsUpperTriangular →
        (kroneckerFin T_B T_C).IsUpperTriangular) ∧
      ∀ (β : Fin m → ℂ) (γ : Fin n → ℂ),
        B.charpoly = ∏ i, (Polynomial.X - Polynomial.C (β i)) →
        C.charpoly = ∏ j, (Polynomial.X - Polynomial.C (γ j)) →
        (B ⊗ₖ C).charpoly = ∏ i, ∏ j, (Polynomial.X - Polynomial.C (β i * γ j)) := by
  refine ⟨?_, fun h₁ h₂ => h₁.kroneckerFin h₂, fun β γ h₁ h₂ => charpoly_kronecker B C h₁ h₂⟩
  rw [conjTranspose_kroneckerFin, kroneckerFin_mul_kroneckerFin, kroneckerFin_mul_kroneckerFin,
    hB, hC]

/-- **Equation (12.3.4)** of [golub2013matrix] and the display before (12.3.3). Let
$B \in \mathbb{R}^{m_1 \times n_1}$ and $C \in \mathbb{R}^{m_2 \times n_2}$, and let
$U_B, V_B, U_C, V_C$ be square matrices with $U_B^T B V_B = S_B$ and $U_C^T C V_C = S_C$. Then
$$(U_B \otimes U_C)^T (B \otimes C)(V_B \otimes V_C) = S_B \otimes S_C.$$ Moreover, the singular
values of $B \otimes C$ are the products of those of $B$ and $C$: there is a bijection $e$ of
the index pairs with $\sigma_{e(i,j)}(B \otimes C) = \sigma_i(B) \sigma_j(C)$.

The identity does not need $U_B, V_B, U_C, V_C$ to be orthogonal. The singular values are
indexed by the columns, `Matrix.colSingularValues`, so $B \otimes C$ has $n_1 n_2$ of them.

**Reading.** The source uses conjugate transpose. Here the factors and matrices are real, and
the singular-value product uses column-indexed values with zeros appended as needed. -/
theorem equation_12_3_4 {m₁ n₁ m₂ n₂ : ℕ} (U_B : Matrix (Fin m₁) (Fin m₁) ℝ)
    (V_B : Matrix (Fin n₁) (Fin n₁) ℝ) (U_C : Matrix (Fin m₂) (Fin m₂) ℝ)
    (V_C : Matrix (Fin n₂) (Fin n₂) ℝ) (Bᵣ : Matrix (Fin m₁) (Fin n₁) ℝ)
    (Cᵣ : Matrix (Fin m₂) (Fin n₂) ℝ) (S_B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (S_C : Matrix (Fin m₂) (Fin n₂) ℝ) (hB : U_Bᵀ * Bᵣ * V_B = S_B)
    (hC : U_Cᵀ * Cᵣ * V_C = S_C) :
    (U_B ⊗ₖ U_C)ᵀ * (Bᵣ ⊗ₖ Cᵣ) * (V_B ⊗ₖ V_C) = S_B ⊗ₖ S_C ∧
      ∃ e : Fin n₁ × Fin n₂ ≃ Fin n₁ × Fin n₂, ∀ q,
        (Bᵣ ⊗ₖ Cᵣ).colSingularValues (e q) =
          Bᵣ.colSingularValues q.1 * Cᵣ.colSingularValues q.2 := by
  refine ⟨?_, colSingularValues_kronecker Bᵣ Cᵣ⟩
  rw [← kroneckerMap_transpose, ← mul_kronecker_mul, ← mul_kronecker_mul, hB, hC]

/-- **§12.3.1** of [golub2013matrix], after (12.3.4). Let $B \in \mathbb{R}^{m \times m}$ and
$C \in \mathbb{R}^{n \times n}$. If $By = \beta y$ and $Cz = \gamma z$, then $(B \otimes C)(y
\otimes z) = \beta\gamma (y \otimes z)$. Moreover $$\operatorname{rank}(B \otimes C) =
\operatorname{rank}(B) \operatorname{rank}(C), \quad \det(B \otimes C) = \det(B)^n \det(C)^m,
\quad \operatorname{tr}(B \otimes C) = \operatorname{tr}(B) \operatorname{tr}(C).$$

The vector $y \otimes z$ is `Matrix.kroneckerVec y z`. -/
theorem kronecker_invariants {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (y : Fin m → ℝ) (z : Fin n → ℝ) (β γ : ℝ), B *ᵥ y = β • y → C *ᵥ z = γ • z →
      (B ⊗ₖ C) *ᵥ kroneckerVec y z = (β * γ) • kroneckerVec y z) ∧
    (B ⊗ₖ C).rank = B.rank * C.rank ∧
    (B ⊗ₖ C).det = B.det ^ n * C.det ^ m ∧
    (B ⊗ₖ C).trace = B.trace * C.trace := by
  refine ⟨fun y z β γ hy hz => ?_, rank_kronecker B C, ?_, trace_kronecker B C⟩
  · rw [kronecker_mulVec, hy, hz, kroneckerVec_smul_left, kroneckerVec_smul_right, smul_smul]
  · rw [det_kronecker, Fintype.card_fin, Fintype.card_fin]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§12.3.1** of [golub2013matrix]. For $B \in \mathbb{R}^{m_1 \times n_1}$ and
$C \in \mathbb{R}^{m_2 \times n_2}$, $$\|B \otimes C\|_F = \|B\|_F \|C\|_F.$$
-/
theorem kronecker_frobenius_norm {m₁ n₁ m₂ n₂ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) : ‖B ⊗ₖ C‖ = ‖B‖ * ‖C‖ :=
  frobenius_norm_kronecker B C

end Frobenius

section L2

open scoped Matrix.Norms.L2Operator

/-- **§12.3.1** of [golub2013matrix]. For $B \in \mathbb{R}^{m_1 \times n_1}$ and
$C \in \mathbb{R}^{m_2 \times n_2}$, $$\|B \otimes C\|_2 = \|B\|_2 \|C\|_2.$$
-/
theorem kronecker_l2_norm {m₁ n₁ m₂ n₂ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) : ‖B ⊗ₖ C‖ = ‖B‖ * ‖C‖ :=
  l2_opNorm_kronecker B C

end L2

/-! ### The Tracy–Singh, Hadamard and Khatri–Rao products (§12.3.2–12.3.3) -/

section TracySingh

variable {M₁ N₁ M₂ N₂ : ℕ}

/-- The row layout of the Tracy–Singh product: the index $((I_1, I_2), (i_1, i_2))$ is ordered by
the block row $I_1$, then the block row $I_2$, then the Kronecker row $(i_1, i_2)$, with the
first index of each pair varying slowest. -/
def tracySinghIndex (M₁ M₂ m₁ m₂ : ℕ) :
    (Fin M₁ × Fin M₂) × (Fin m₁ × Fin m₂) ≃ Fin (M₁ * M₂ * (m₁ * m₂)) :=
  (finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- **§12.3.2** of [golub2013matrix], the Tracy–Singh product (12.3.5). Let
$B \in \mathbb{R}^{M_1 m_1 \times N_1 n_1}$ be an $M_1 \times N_1$ block matrix with the blocks
$B_{ij} \in \mathbb{R}^{m_1 \times n_1}$, and let $C \in \mathbb{R}^{M_2 m_2 \times N_2 n_2}$ be
an $M_2 \times N_2$ block matrix with the blocks $C_{kl} \in \mathbb{R}^{m_2 \times n_2}$. The
**Tracy–Singh product** $B \otimes_{TS} C$ is the $M_1 \times N_1$ block matrix whose block
$(i, j)$ is the block matrix $[B_{ij} \otimes C_{kl}]_{k,l}$.

The blocks are laid out by `finProdFinEquiv`, with the block index varying slowest. The product
is the backbone's typed `Matrix.tracySingh`, read through
`GolubVanLoan.Chapter12.tracySinghIndex`. -/
def tracySinghFin (B : Matrix (Fin (M₁ * m₁)) (Fin (N₁ * n₁)) ℝ)
    (C : Matrix (Fin (M₂ * m₂)) (Fin (N₂ * n₂)) ℝ) :
    Matrix (Fin (M₁ * M₂ * (m₁ * m₂))) (Fin (N₁ * N₂ * (n₁ * n₂))) ℝ :=
  (tracySingh (B.submatrix finProdFinEquiv finProdFinEquiv)
    (C.submatrix finProdFinEquiv finProdFinEquiv)).reindex (tracySinghIndex M₁ M₂ m₁ m₂)
      (tracySinghIndex N₁ N₂ n₁ n₂)

/-- The position of the row $((I_1, I_2), (i_1, i_2))$ in $B \otimes C$: the row of $B \otimes C$
formed by the row $(I_1, i_1)$ of $B$ and the row $(I_2, i_2)$ of $C$. -/
def kroneckerBlockIndex (M₁ M₂ m₁ m₂ : ℕ) :
    (Fin M₁ × Fin M₂) × (Fin m₁ × Fin m₂) ≃ Fin (M₁ * m₁ * (M₂ * m₂)) :=
  (Equiv.prodProdProdComm _ _ _ _).trans
    ((finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv)

/-- **Equations (12.3.5)–(12.3.6)** of [golub2013matrix]. The Tracy–Singh product is a row and
column permutation of the Kronecker product: $$B \otimes_{TS} C = P (B \otimes C) Q^T,$$ where
$P$ and $Q$ are the permutation matrices that take the Kronecker order of the rows and the
columns to the Tracy–Singh order.

The matrices $P$ and $Q$ are the matrices of the index permutations formed from
`GolubVanLoan.Chapter12.tracySinghIndex` and `GolubVanLoan.Chapter12.kroneckerBlockIndex`, as
for the perfect shuffle of Chapter 1. The backbone fact is
`Matrix.tracySingh_eq_reindex_kronecker`. -/
theorem equation_12_3_6 (B : Matrix (Fin (M₁ * m₁)) (Fin (N₁ * n₁)) ℝ)
    (C : Matrix (Fin (M₂ * m₂)) (Fin (N₂ * n₂)) ℝ) :
    tracySinghFin B C =
      ((tracySinghIndex M₁ M₂ m₁ m₂).symm.trans
          (kroneckerBlockIndex M₁ M₂ m₁ m₂)).toPEquiv.toMatrix *
        kroneckerFin B C *
        (((tracySinghIndex N₁ N₂ n₁ n₂).symm.trans
          (kroneckerBlockIndex N₁ N₂ n₁ n₂)).toPEquiv.toMatrix)ᵀ := by
  rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext I J
  obtain ⟨⟨⟨I₁, I₂⟩, ⟨i₁, i₂⟩⟩, rfl⟩ := (tracySinghIndex M₁ M₂ m₁ m₂).surjective I
  obtain ⟨⟨⟨J₁, J₂⟩, ⟨j₁, j₂⟩⟩, rfl⟩ := (tracySinghIndex N₁ N₂ n₁ n₂).surjective J
  simp [tracySinghFin, kroneckerBlockIndex, tracySingh, kroneckerFin_apply]

/-- **§12.3.3** of [golub2013matrix], the block Khatri–Rao product. For two $M \times N$ block
matrices $B$ and $C$, with the blocks $B_{ij}$ and $C_{ij}$, it is the $M \times N$ block matrix
with the blocks $B_{ij} \otimes C_{ij}$.

The block indices are the types `M` and `N`. -/
def blockKhatriRao {M N p₁ q₁ p₂ q₂ : Type*} (B : Matrix (M × p₁) (N × q₁) ℝ)
    (C : Matrix (M × p₂) (N × q₂) ℝ) : Matrix (M × (p₁ × p₂)) (N × (q₁ × q₂)) ℝ :=
  of fun I J => B (I.1, I.2.1) (J.1, J.2.1) * C (I.1, I.2.2) (J.1, J.2.2)

/-- **§12.3.3** of [golub2013matrix], the Hadamard and Khatri–Rao products as submatrices. Let
$B, C \in \mathbb{R}^{m \times n}$, $F \in \mathbb{R}^{m_1 \times r}$ and
$G \in \mathbb{R}^{m_2 \times r}$. The Hadamard product $B .* C$ is the submatrix of
$B \otimes C$ in the rows $(i, i)$ and the columns $(j, j)$. The column Khatri–Rao product $$F
\odot G = [f_1 \otimes g_1 \,|\, \cdots \,|\, f_r \otimes g_r]$$ is the submatrix of
$F \otimes G$ in the columns $(j, j)$, and its column $j$ is $f_j \otimes g_j$. The block
Khatri–Rao product of two block matrices is a submatrix of their Tracy–Singh product.

The Hadamard product is `B ⊙ C`, and the column Khatri–Rao product is `Matrix.khatriRao F G`. -/
theorem hadamard_khatriRao_submatrix_kronecker {m n r : ℕ} (B C : Matrix (Fin m) (Fin n) ℝ)
    (F : Matrix (Fin m₁) (Fin r) ℝ) (G : Matrix (Fin m₂) (Fin r) ℝ) :
    B ⊙ C = (B ⊗ₖ C).submatrix (fun i => (i, i)) (fun j => (j, j)) ∧
      khatriRao F G = (F ⊗ₖ G).submatrix id (fun j => (j, j)) ∧
      (∀ j, (fun x => khatriRao F G x j) = kroneckerVec (fun i => F i j) fun i => G i j) ∧
      ∀ {M N p₁ q₁ p₂ q₂ : Type*} (B' : Matrix (M × p₁) (N × q₁) ℝ)
        (C' : Matrix (M × p₂) (N × q₂) ℝ),
        blockKhatriRao B' C' =
          (tracySingh B' C').submatrix (fun I => ((I.1, I.1), I.2)) fun J => ((J.1, J.1), J.2) :=
  ⟨hadamard_eq_submatrix_kronecker B C, khatriRao_eq_submatrix_kronecker F G,
    fun _ => rfl, fun _ _ => rfl⟩

end TracySingh

/-! ### The operations vec and reshape (12.3.9)–(12.3.12) -/

/-- The source's $\operatorname{reshape}(a, m, n)$ of a vector $a \in \mathbb{R}^{mn}$: the matrix
$A \in \mathbb{R}^{m \times n}$ with $\operatorname{vec}(A) = a$. -/
def reshapeVec {m n : ℕ} (a : Fin (n * m) → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i j => a (finProdFinEquiv (j, i))

/-- For every vector $a \in \mathbb{R}^{mn}$, $\operatorname{vec}(\operatorname{reshape}(a, m, n)) =
a$. -/
@[simp]
theorem vecFin_reshapeVec {m n : ℕ} (a : Fin (n * m) → ℝ) : vecFin (reshapeVec a) = a := by
  funext t
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective t
  rw [vecFin_apply, reshapeVec, of_apply]

/-- **Equation (12.3.9)** of [golub2013matrix]. Let $B \in \mathbb{R}^{m_1 \times n_1}$,
$C \in \mathbb{R}^{m_2 \times n_2}$, $X \in \mathbb{R}^{n_2 \times n_1}$ and
$Y \in \mathbb{R}^{m_2 \times m_1}$. Then $$Y = C X B^T \iff \operatorname{vec}(Y) = (B \otimes
C) \operatorname{vec}(X).$$

**Typo.** The source states $X \in \mathbb{R}^{n_1 \times m_2}$. The product $C X B^T$ needs
$X \in \mathbb{R}^{n_2 \times n_1}$.

This is (1.3.6) of Chapter 1, `GolubVanLoan.Chapter01.equation_1_3_6`. -/
theorem equation_12_3_9 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ)
    (X : Matrix (Fin n₂) (Fin n₁) ℝ) (Y : Matrix (Fin m₂) (Fin m₁) ℝ) :
    Y = C * X * Bᵀ ↔ vecFin Y = kroneckerFin B C *ᵥ vecFin X :=
  Chapter01.equation_1_3_6 B C X Y

/-- The operation vec is additive over finite sums: $\operatorname{vec}(\sum_k A_k) = \sum_k
\operatorname{vec}(A_k)$. -/
theorem vecFin_sum {m n p : ℕ} (A : Fin p → Matrix (Fin m) (Fin n) ℝ) :
    vecFin (∑ k, A k) = ∑ k, vecFin (A k) := by
  funext t
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective t
  simp [vecFin_apply, Finset.sum_apply, Matrix.sum_apply]

/-- **Equations (12.3.10)–(12.3.11)** of [golub2013matrix]. Let
$F_k \in \mathbb{R}^{m_2 \times n_2}$ and $G_k \in \mathbb{R}^{m_1 \times n_1}$ for
$k = 1, \dots, p$, and let $X \in \mathbb{R}^{n_2 \times n_1}$ and
$C \in \mathbb{R}^{m_2 \times m_1}$. Then $$F_1 X G_1^T + \cdots + F_p X G_p^T = C \iff (G_1
\otimes F_1 + \cdots + G_p \otimes F_p) \operatorname{vec}(X) = \operatorname{vec}(C).$$
Moreover, for $u \in \mathbb{R}^m$ and $v \in \mathbb{R}^n$, $\operatorname{reshape}(v \otimes
u, m, n) = uv^T$.

The second part is stated on product index types, with `Matrix.unvec` for reshape. -/
theorem equation_12_3_11 {p : ℕ} (F : Fin p → Matrix (Fin m₂) (Fin n₂) ℝ)
    (G : Fin p → Matrix (Fin m₁) (Fin n₁) ℝ) (X : Matrix (Fin n₂) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin m₁) ℝ) :
    (∑ k, F k * X * (G k)ᵀ = C ↔ (∑ k, kroneckerFin (G k) (F k)) *ᵥ vecFin X = vecFin C) ∧
      ∀ {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ), unvec (kroneckerVec v u) = vecMulVec u v := by
  refine ⟨?_, fun u v => unvec_kroneckerVec v u⟩
  rw [sum_mulVec]
  have h : ∀ k, kroneckerFin (G k) (F k) *ᵥ vecFin X = vecFin (F k * X * (G k)ᵀ) :=
    fun k => ((equation_12_3_9 (G k) (F k) X _).1 rfl).symm
  simp only [h, ← vecFin_sum]
  exact ⟨fun h' => h' ▸ rfl, fun h' => vecFin_injective h'⟩

/-- **Equation (12.3.12)** of [golub2013matrix]. For $A \in \mathbb{R}^{q \times r}$,
$$\operatorname{vec}(A^T) = \mathcal{P}_{r,q} \operatorname{vec}(A).$$
-/
theorem equation_12_3_12 {q r : ℕ} (A : Matrix (Fin q) (Fin r) ℝ) :
    vecFin Aᵀ = perfectShuffle r q *ᵥ vecFin A :=
  (perfectShuffle_mulVec_vecFin A).symm

/-! ### The two-pass transposition (§12.3.5) -/

section TwoPass

/-- For every matrix $Y$, $\operatorname{reshape}(\operatorname{vec}(Y)) = Y$. -/
@[simp]
theorem reshapeVec_vecFin {m n : ℕ} (Y : Matrix (Fin m) (Fin n) ℝ) :
    reshapeVec (vecFin Y) = Y := by
  ext i j
  rw [reshapeVec, of_apply, vecFin_apply]

variable {q r : ℕ}

/-- The entry $(k, j, i)$ of the first pass $\Gamma_1 \operatorname{vec}(A)$ is $(A_k)_{ij}$. -/
private theorem twoPass_first (A : Matrix (Fin (r * q)) (Fin q) ℝ) (k : Fin r) (i j : Fin q) :
    (kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ
      (vecFin A ∘ finCongr (by ring))) (finProdFinEquiv (finProdFinEquiv (k, j), i)) =
      A (finProdFinEquiv (k, i)) j := by
  rw [kroneckerFin_perfectShuffle_one_mulVec, Function.comp_apply]
  have : finCongr (by ring) (finProdFinEquiv (finProdFinEquiv (j, k), i)) =
      (finProdFinEquiv (j, finProdFinEquiv (k, i)) : Fin (q * (r * q))) := by
    ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [this, vecFin_apply]

/-- The entry $(k, a, b)$ of the two passes $\Gamma_2 \Gamma_1 \operatorname{vec}(A)$ is
$(A_k)_{ab}$. -/
private theorem twoPass_second (A : Matrix (Fin (r * q)) (Fin q) ℝ) (k : Fin r) (a b : Fin q) :
    (kroneckerFin (1 : Matrix (Fin r) (Fin r) ℝ) (perfectShuffle q q) *ᵥ
      ((kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ
        (vecFin A ∘ finCongr (by ring))) ∘ finCongr (by ring)))
      (finProdFinEquiv (k, finProdFinEquiv (a, b))) = A (finProdFinEquiv (k, a)) b := by
  rw [kroneckerFin_one_perfectShuffle_mulVec, Function.comp_apply]
  have : finCongr (by ring) (finProdFinEquiv (k, finProdFinEquiv (b, a))) =
      (finProdFinEquiv (finProdFinEquiv (k, b), a) : Fin (r * q * q)) := by
    ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [this]
  exact twoPass_first A k a b

/-- **§12.3.5** of [golub2013matrix], the two-pass transposition. Let $A = \begin{bmatrix} A_1 \\
\vdots \\ A_r \end{bmatrix}$ with $A_k \in \mathbb{R}^{q \times q}$, and let
$\Gamma_1 = \mathcal{P}_{q,r} \otimes I_q$ and $\Gamma_2 = I_r \otimes \mathcal{P}_{q,q}$. Then
$$\operatorname{reshape}(\Gamma_1 \operatorname{vec}(A), q, rq) = [A_1 \,|\, \cdots \,|\, A_r],
\qquad \operatorname{reshape}(\Gamma_2 \Gamma_1 \operatorname{vec}(A), q, rq) = [A_1^T \,|\,
\cdots \,|\, A_r^T] = A^T,$$ and $\mathcal{P}_{q,rq} = \Gamma_2 \Gamma_1$.

**Correction.** The source prints $\Gamma_1 = \mathcal{P}_{r,q} \otimes I_q$, the transpose of
the matrix here; the two agree only for $r = q$. The source also announces a factorization of
$\mathcal{P}_{rq,q}$ before it writes $\mathcal{P}_{q,rq}$.

The sizes $rq \cdot q$ and $q \cdot rq$ are identified by `finCongr`. -/
theorem perfectShuffle_two_pass (A : Matrix (Fin (r * q)) (Fin q) ℝ) :
    reshapeVec (kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ
        (vecFin A ∘ finCongr (by ring))) =
      (of fun i J => A (finProdFinEquiv ((finProdFinEquiv.symm J).1, i))
        (finProdFinEquiv.symm J).2 : Matrix (Fin q) (Fin (r * q)) ℝ) ∧
    reshapeVec ((kroneckerFin (1 : Matrix (Fin r) (Fin r) ℝ) (perfectShuffle q q) *ᵥ
        ((kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ
          (vecFin A ∘ finCongr (by ring))) ∘ finCongr (by ring))) ∘ finCongr (by ring)) = Aᵀ ∧
    (perfectShuffle q (r * q) : Matrix (Fin (r * q * q)) (Fin (q * (r * q))) ℝ).submatrix
        (finCongr (by ring)) id =
      kroneckerFin (1 : Matrix (Fin r) (Fin r) ℝ) (perfectShuffle q q) *
        (kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ)).submatrix
          (finCongr (by ring)) (finCongr (by ring)) := by
  refine ⟨?_, ?_, Matrix.perfectShuffle_submatrix_eq_kroneckerFin_mul⟩
  · ext i J
    obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective J
    rw [reshapeVec, of_apply, twoPass_first, of_apply, Equiv.symm_apply_apply]
  · ext i R'
    obtain ⟨⟨k, a⟩, rfl⟩ := finProdFinEquiv.surjective R'
    rw [reshapeVec, of_apply, Function.comp_apply, transpose_apply]
    have : finCongr (by ring) (finProdFinEquiv (finProdFinEquiv (k, a), i)) =
        (finProdFinEquiv (k, finProdFinEquiv (a, i)) : Fin (r * (q * q))) := by
      ext
      simp [finProdFinEquiv_apply_val]
      ring
    rw [this, twoPass_second]

end TwoPass

/-! ### The Tracy–Singh permutations (12.3.7)–(12.3.8) -/

section TracySinghPerm

variable {M₁ M₂ m₁ m₂ : ℕ}

/-- The row permutation of (12.3.7) acting on a vector: it takes the Kronecker order
$(I_1, i_1, I_2, i_2)$ to the Tracy–Singh order $(I_1, I_2, i_1, i_2)$. -/
private theorem tracySinghPerm_mulVec (x : Fin (M₁ * m₁ * (M₂ * m₂)) → ℝ)
    (t : Fin (M₁ * M₂ * (m₁ * m₂))) :
    (kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *ᵥ
        ((kroneckerFin (1 : Matrix (Fin M₁) (Fin M₁) ℝ) (perfectShuffle m₁ (M₂ * m₂)) *ᵥ
          (x ∘ finCongr (by ring))) ∘ finCongr (by ring))) t =
      x (((tracySinghIndex M₁ M₂ m₁ m₂).symm.trans (kroneckerBlockIndex M₁ M₂ m₁ m₂)) t) := by
  obtain ⟨⟨⟨I₁, I₂⟩, ⟨i₁, i₂⟩⟩, rfl⟩ := (tracySinghIndex M₁ M₂ m₁ m₂).surjective t
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  change (kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *ᵥ _)
    (finProdFinEquiv (finProdFinEquiv (I₁, I₂), finProdFinEquiv (i₁, i₂))) = _
  rw [kroneckerFin_one_perfectShuffle_mulVec, Function.comp_apply]
  have e1 : finCongr (by ring) (finProdFinEquiv (finProdFinEquiv (I₁, I₂),
      finProdFinEquiv (i₂, i₁))) = (finProdFinEquiv (I₁, finProdFinEquiv
        (finProdFinEquiv (I₂, i₂), i₁)) : Fin (M₁ * (M₂ * m₂ * m₁))) := by
    ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [e1, kroneckerFin_one_perfectShuffle_mulVec, Function.comp_apply]
  congr 1
  ext
  simp [finProdFinEquiv_apply_val, kroneckerBlockIndex]
  ring

/-- **Equations (12.3.7)–(12.3.8)** of [golub2013matrix]. The permutation matrices of (12.3.6) are
$$P = (I_{M_1 M_2} \otimes \mathcal{P}_{m_2,m_1})(I_{M_1} \otimes \mathcal{P}_{m_1,M_2 m_2}),
\qquad Q = (I_{N_1 N_2} \otimes \mathcal{P}_{n_2,n_1})(I_{N_1} \otimes \mathcal{P}_{n_1,N_2
n_2}),$$ so that $B \otimes_{TS} C = P (B \otimes C) Q^T$.

The Kronecker products and the perfect shuffles are those of Chapter 1 in the positional layout.
The products of sizes are identified by `finCongr`. -/
theorem equation_12_3_7 {N₁ N₂ n₁ n₂ : ℕ} (B : Matrix (Fin (M₁ * m₁)) (Fin (N₁ * n₁)) ℝ)
    (C : Matrix (Fin (M₂ * m₂)) (Fin (N₂ * n₂)) ℝ) :
    ((tracySinghIndex M₁ M₂ m₁ m₂).symm.trans
        (kroneckerBlockIndex M₁ M₂ m₁ m₂)).toPEquiv.toMatrix =
      kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *
        (kroneckerFin (1 : Matrix (Fin M₁) (Fin M₁) ℝ) (perfectShuffle m₁ (M₂ * m₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring)) ∧
    ((tracySinghIndex N₁ N₂ n₁ n₂).symm.trans
        (kroneckerBlockIndex N₁ N₂ n₁ n₂)).toPEquiv.toMatrix =
      kroneckerFin (1 : Matrix (Fin (N₁ * N₂)) (Fin (N₁ * N₂)) ℝ) (perfectShuffle n₂ n₁) *
        (kroneckerFin (1 : Matrix (Fin N₁) (Fin N₁) ℝ) (perfectShuffle n₁ (N₂ * n₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring)) ∧
    tracySinghFin B C =
      (kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *
        (kroneckerFin (1 : Matrix (Fin M₁) (Fin M₁) ℝ) (perfectShuffle m₁ (M₂ * m₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring))) * kroneckerFin B C *
      (kroneckerFin (1 : Matrix (Fin (N₁ * N₂)) (Fin (N₁ * N₂)) ℝ) (perfectShuffle n₂ n₁) *
        (kroneckerFin (1 : Matrix (Fin N₁) (Fin N₁) ℝ) (perfectShuffle n₁ (N₂ * n₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring)))ᵀ := by
  have key : ∀ {M₁ M₂ m₁ m₂ : ℕ},
      ((tracySinghIndex M₁ M₂ m₁ m₂).symm.trans
        (kroneckerBlockIndex M₁ M₂ m₁ m₂)).toPEquiv.toMatrix =
      kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *
        (kroneckerFin (1 : Matrix (Fin M₁) (Fin M₁) ℝ) (perfectShuffle m₁ (M₂ * m₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring)) := by
    intro M₁ M₂ m₁ m₂
    refine ext_of_mulVec_single fun j => ?_
    rw [← mulVec_mulVec, submatrix_mulVec_equiv, finCongr_symm, PEquiv.toMatrix_toPEquiv_mulVec]
    funext t
    rw [Function.comp_apply, tracySinghPerm_mulVec]
  refine ⟨key, key, ?_⟩
  rw [← key, ← key]
  exact equation_12_3_6 B C

end TracySinghPerm

/-! ### The rearrangement and the Kronecker product SVD (§12.3.6) -/

/-- **§12.3.6** of [golub2013matrix], definition of the rearrangement. Let
$A \in \mathbb{R}^{m_1 m_2 \times n_1 n_2}$ be blocked as in (12.3.16), with the blocks
$A_{ij} \in \mathbb{R}^{m_2 \times n_2}$ for $i = 1, \dots, m_1$ and $j = 1, \dots, n_1$. The
**rearrangement** $\mathcal{R}(A) \in \mathbb{R}^{m_1 n_1 \times m_2 n_2}$ is the matrix whose
row $(j - 1) m_1 + i$ is $\operatorname{vec}(A_{ij})^T$, so that its rows are ordered by the
block columns $\tilde A_1, \dots, \tilde A_{n_1}$.

It is the backbone's `Matrix.kroneckerRearrange`, read through `finProdFinEquiv`. -/
def rearrangement (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) ℝ :=
  (kroneckerRearrange (A.reindex finProdFinEquiv.symm finProdFinEquiv.symm)).reindex
    finProdFinEquiv finProdFinEquiv

/-- The entries of the rearrangement: the entry of $\mathcal{R}(A)$ in the row $(j, i)$ and the
column $(l, k)$ is $(A_{ij})_{kl}$. -/
@[simp]
theorem rearrangement_apply (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) (i : Fin m₁)
    (j : Fin n₁) (k : Fin m₂) (l : Fin n₂) :
    rearrangement A (finProdFinEquiv (j, i)) (finProdFinEquiv (l, k)) =
      A (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) := by
  simp [rearrangement]

/-- The rearrangement preserves differences: $\mathcal{R}(A - A') = \mathcal{R}(A) -
\mathcal{R}(A')$. -/
theorem rearrangement_sub (A A' : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    rearrangement (A - A') = rearrangement A - rearrangement A' :=
  rfl

/-- The rearrangement commutes with scalar multiples: $\mathcal{R}(cA) = c \mathcal{R}(A)$. -/
theorem rearrangement_smul (c : ℝ) (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    rearrangement (c • A) = c • rearrangement A :=
  rfl

/-- The rearrangement commutes with finite sums: $\mathcal{R}(\sum_k X_k) = \sum_k
\mathcal{R}(X_k)$. -/
theorem rearrangement_sum {ι : Type*} (s : Finset ι)
    (X : ι → Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    rearrangement (∑ k ∈ s, X k) = ∑ k ∈ s, rearrangement (X k) := by
  ext I J
  simp [rearrangement, Matrix.sum_apply]

/-- The rearrangement of a Kronecker product has rank at most one: $\mathcal{R}(B \otimes C) =
\operatorname{vec}(B) \operatorname{vec}(C)^T$. -/
theorem rearrangement_kroneckerFin (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    rearrangement (kroneckerFin B C) = vecMulVec (vecFin B) (vecFin C) := by
  ext I J
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨l, k⟩, rfl⟩ := finProdFinEquiv.surjective J
  rw [rearrangement_apply, kroneckerFin_apply, vecMulVec_apply, vecFin_apply, vecFin_apply]

section Norm

open scoped Matrix.Norms.Frobenius

/-- The rearrangement preserves the Frobenius norm, $\|\mathcal{R}(A)\|_F = \|A\|_F$, because it
permutes the entries. -/
theorem frobenius_norm_rearrangement (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    ‖rearrangement A‖ = ‖A‖ := by
  rw [rearrangement, reindex_apply, frobenius_norm_submatrix_equiv,
    frobenius_norm_kroneckerRearrange, reindex_apply, frobenius_norm_submatrix_equiv]

/-- **Equation (12.3.14)** of [golub2013matrix] and the display after the example. For
$A \in \mathbb{R}^{m_1 m_2 \times n_1 n_2}$, $B \in \mathbb{R}^{m_1 \times n_1}$ and
$C \in \mathbb{R}^{m_2 \times n_2}$, $$\phi(B, C) = \|A - B \otimes C\|_F = \|\mathcal{R}(A) -
\operatorname{vec}(B) \operatorname{vec}(C)^T\|_F.$$ So to minimize $\phi$ is to find a nearest
rank-one matrix to $\mathcal{R}(A)$. -/
theorem equation_12_3_14 (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ)
    (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    ‖A - kroneckerFin B C‖ = ‖rearrangement A - vecMulVec (vecFin B) (vecFin C)‖ := by
  rw [← frobenius_norm_rearrangement, rearrangement_sub, rearrangement_kroneckerFin]

/-- **Equation (12.3.20)** of [golub2013matrix]. For $A \in \mathbb{R}^{m^2 \times m^2}$ and
$X \in \mathbb{R}^{m \times m}$, $$\phi_{sym}(X) = \|A - X \otimes X\|_F = \|\mathcal{R}(A) -
\operatorname{vec}(X) \operatorname{vec}(X)^T\|_F.$$
-/
theorem equation_12_3_20 {m : ℕ} (A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ)
    (X : Matrix (Fin m) (Fin m) ℝ) :
    ‖A - kroneckerFin X X‖ = ‖rearrangement A - vecMulVec (vecFin X) (vecFin X)‖ :=
  equation_12_3_14 A X X

/-- **Equation (12.3.21)** of [golub2013matrix]. For $A \in \mathbb{R}^{m^2 \times m^2}$ and
$X, Y \in \mathbb{R}^{m \times m}$, $$\phi_{skew}(X, Y) = \|A - (X \otimes Y - Y \otimes
X)\|_F = \|\mathcal{R}(A) - (\operatorname{vec}(X) \operatorname{vec}(Y)^T -
\operatorname{vec}(Y) \operatorname{vec}(X)^T)\|_F.$$

**Typo.** The source writes $\phi_{skew}(X)$ for $\phi_{skew}(X, Y)$ and drops a parenthesis. -/
theorem equation_12_3_21 {m : ℕ} (A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ)
    (X Y : Matrix (Fin m) (Fin m) ℝ) :
    ‖A - (kroneckerFin X Y - kroneckerFin Y X)‖ =
      ‖rearrangement A - (vecMulVec (vecFin X) (vecFin Y) - vecMulVec (vecFin Y) (vecFin X))‖ := by
  rw [← frobenius_norm_rearrangement, rearrangement_sub, rearrangement_sub,
    rearrangement_kroneckerFin, rearrangement_kroneckerFin]

end Norm

/-- **Theorem 12.3.1** of [golub2013matrix] (Kronecker product SVD). Let
$A \in \mathbb{R}^{m_1 m_2 \times n_1 n_2}$, and let the expansion (12.3.17) $$\mathcal{R}(A) =
\sum_{k=1}^r \sigma_k u_k v_k^T$$ hold with $u_k \in \mathbb{R}^{m_1 n_1}$ and
$v_k \in \mathbb{R}^{m_2 n_2}$. Then (12.3.18) holds: $$A = \sum_{k=1}^r \sigma_k U_k \otimes
V_k, \qquad U_k = \operatorname{reshape}(u_k, m_1, n_1), \quad V_k = \operatorname{reshape}(v_k,
m_2, n_2).$$ If moreover the expansion is an SVD, that is, $\sigma_k > 0$ for all $k$ and both
$u_1, \dots, u_r$ and $v_1, \dots, v_r$ are orthonormal, then $r$ is the Kronecker product rank
of $A$, the rank of $\mathcal{R}(A)$.

The Kronecker product rank is `Matrix.kroneckerRank`.

**Generalization.** The expansion holds for any decomposition into outer products. Positivity
and orthonormality yield the rank equality. -/
theorem theorem_12_3_1 {r : ℕ} (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) (σ : Fin r → ℝ)
    (u : Fin r → Fin (n₁ * m₁) → ℝ) (v : Fin r → Fin (n₂ * m₂) → ℝ)
    (hA : rearrangement A = ∑ k, σ k • vecMulVec (u k) (v k)) :
    A = ∑ k, σ k • kroneckerFin (reshapeVec (u k)) (reshapeVec (v k)) ∧
      ((∀ k, 0 < σ k) → (∀ k l, u k ⬝ᵥ u l = if k = l then 1 else 0) →
        (∀ k l, v k ⬝ᵥ v l = if k = l then 1 else 0) →
        kroneckerRank (A.reindex finProdFinEquiv.symm finProdFinEquiv.symm) = r) := by
  refine ⟨?_, fun hσ hu hv => ?_⟩
  · ext I J
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective I
    obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective J
    have h := congrFun (congrFun hA (finProdFinEquiv (j, i))) (finProdFinEquiv (l, k))
    rw [rearrangement_apply] at h
    rw [h, Matrix.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [reshapeVec, kroneckerFin_apply, vecMulVec_apply]
  · have hR : kroneckerRank (A.reindex finProdFinEquiv.symm finProdFinEquiv.symm) =
        (rearrangement A).rank := by
      rw [kroneckerRank, rearrangement, rank_reindex]
    rw [hR, hA]
    set U : Matrix (Fin (n₁ * m₁)) (Fin r) ℝ := of fun I t => u t I
    set V : Matrix (Fin (n₂ * m₂)) (Fin r) ℝ := of fun J t => v t J
    have hUV : (∑ t, σ t • vecMulVec (u t) (v t)) = U * diagonal σ * Vᵀ := by
      ext I J
      simp [U, V, Matrix.sum_apply, Matrix.mul_apply, vecMulVec_apply, diagonal_apply, mul_comm,
        mul_left_comm]
    have hU : Uᵀ * U = 1 := by
      ext t l
      rw [Matrix.mul_apply, Matrix.one_apply, ← hu t l]
      rfl
    have hV : Vᵀ * V = 1 := by
      ext t l
      rw [Matrix.mul_apply, Matrix.one_apply, ← hv t l]
      rfl
    rw [hUV]
    refine le_antisymm ?_ ?_
    · refine (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans ?_)
      exact (rank_le_card_width U).trans (by simp)
    · have hD : Uᵀ * (U * diagonal σ * Vᵀ) * V = diagonal σ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hV,
          Matrix.mul_one]
      have hrk : (diagonal σ).rank = r := by
        rw [rank_diagonal, Fintype.card_subtype, Finset.filter_true_of_mem
          (fun t _ => (hσ t).ne'), Finset.card_univ, Fintype.card_fin]
      calc r = (diagonal σ).rank := hrk.symm
        _ = (Uᵀ * (U * diagonal σ * Vᵀ) * V).rank := by rw [hD]
        _ ≤ (U * diagonal σ * Vᵀ).rank :=
          (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- A sum of $r$ rank-one matrices $x_k y_k^T$ has rank at most $r$. -/
private theorem rank_sum_vecMulVec_le {p q r : ℕ} (x : Fin r → Fin p → ℝ)
    (y : Fin r → Fin q → ℝ) : (∑ k, vecMulVec (x k) (y k)).rank ≤ r := by
  have h : (∑ k, vecMulVec (x k) (y k)) =
      (of fun I k => x k I : Matrix (Fin p) (Fin r) ℝ) * of fun k J => y k J := by
    ext I J
    simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]
  rw [h]
  exact (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans (by simp))

open scoped Matrix.Norms.Frobenius in
/-- **Equation (12.3.19)** of [golub2013matrix] and the paragraph before it. Let
$A \in \mathbb{R}^{m_1 m_2 \times n_1 n_2}$, let $U^T \mathcal{R}(A) V = \Sigma$ be an SVD of
the rearrangement as in (12.3.17), with the singular values $\sigma_1 \ge \sigma_2 \ge \cdots$,
and let $\tilde r \le m_1 n_1$ and $\tilde r \le m_2 n_2$. Let $U_k =
\operatorname{reshape}(U(:, k), m_1, n_1)$, $V_k = \operatorname{reshape}(V(:, k), m_2, n_2)$
and $$A_{\tilde r} = \sum_{k=1}^{\tilde r} \sigma_k U_k \otimes V_k.$$ Then for all
$B_k \in \mathbb{R}^{m_1 \times n_1}$ and $C_k \in \mathbb{R}^{m_2 \times n_2}$, $$\|A -
A_{\tilde r}\|_F \le \Bigl\|A - \sum_{k=1}^{\tilde r} B_k \otimes C_k\Bigr\|_F.$$ So
$A_{\tilde r}$ is a closest matrix to $A$ in the Frobenius norm among the sums of $\tilde r$
Kronecker products.

The SVD is `Matrix.IsSVD`. Because $\mathcal{R}$ is an isometry, this is the Eckart–Young–Mirsky
theorem for $\mathcal{R}(A)$, `Matrix.isLeast_frobenius_norm_sub_of_rank_le`: the matrix
$\mathcal{R}(\sum_k B_k \otimes C_k) = \sum_k \operatorname{vec}(B_k) \operatorname{vec}(C_k)^T$
has rank at most $\tilde r$, and $\mathcal{R}(A_{\tilde r})$ is the truncated SVD
(`Matrix.svdTruncation_eq_sum`). The Frobenius form of the Eckart–Young theorem in Chapter 2,
`GolubVanLoan.Chapter02.svdTruncation_isLeast_frobenius`, compares only matrices whose rank is
equal to some $k < \operatorname{rank}(A)$. It does not apply as stated, because here the
competitors have rank at most $\tilde r$.

**Generalization.** The truncation may include zero singular values when its length exceeds the
rank. -/
theorem equation_12_3_19 (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ)
    {U : Matrix (Fin (n₁ * m₁)) (Fin (n₁ * m₁)) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n₂ * m₂)) (Fin (n₂ * m₂)) ℝ} (h : IsSVD (rearrangement A) U σ V) {r : ℕ}
    (hr₁ : r ≤ n₁ * m₁) (hr₂ : r ≤ n₂ * m₂) (B : Fin r → Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Fin r → Matrix (Fin m₂) (Fin n₂) ℝ) :
    ‖A - ∑ k : Fin r, σ k • kroneckerFin (reshapeVec fun I => U I (Fin.castLE hr₁ k))
        (reshapeVec fun J => V J (Fin.castLE hr₂ k))‖ ≤
      ‖A - ∑ k, kroneckerFin (B k) (C k)‖ := by
  rw [← frobenius_norm_rearrangement, rearrangement_sub, rearrangement_sum,
    ← frobenius_norm_rearrangement (A - _), rearrangement_sub, rearrangement_sum]
  simp only [rearrangement_smul, rearrangement_kroneckerFin, vecFin_reshapeVec]
  have hT : (∑ k : Fin r, σ k • vecMulVec (fun I => U I (Fin.castLE hr₁ k))
      fun J => V J (Fin.castLE hr₂ k)) = svdTruncation U σ V r := by
    rw [svdTruncation_eq_sum U σ V hr₁ hr₂]
    simp [Matrix.col, star_trivial]
    rfl
  rw [hT, frobenius_norm_sub_svdTruncation h]
  have := (isLeast_frobenius_norm_sub_of_rank_le (rearrangement A) r).2
    ⟨_, rank_sum_vecMulVec_le (fun k => vecFin (B k)) (fun k => vecFin (C k)), rfl⟩
  simpa using this

/-- The operation reshape commutes with scalar multiples: $\operatorname{reshape}(ca) = c
\operatorname{reshape}(a)$. -/
theorem reshapeVec_smul {m n : ℕ} (c : ℝ) (a : Fin (n * m) → ℝ) :
    reshapeVec (c • a) = c • reshapeVec a := by
  ext i j
  simp [reshapeVec]

open scoped Matrix.Norms.Frobenius in
/-- **Equation (12.3.15)** of [golub2013matrix] and the sentence after it. Let
$A \in \mathbb{R}^{m_1 m_2 \times n_1 n_2}$ with $m_1 n_1 \ge 1$ and $m_2 n_2 \ge 1$, and let
$U^T \mathcal{R}(A) V = \Sigma$ be an SVD of $\mathcal{R}(A)$. Then the matrices $B_{opt}$ and
$C_{opt}$ with $$\operatorname{vec}(B_{opt}) = \sqrt{\sigma_1}\, U(:, 1), \qquad
\operatorname{vec}(C_{opt}) = \sqrt{\sigma_1}\, V(:, 1)$$ minimize
$\phi(B, C) = \|A - B \otimes C\|_F$, and so do $\alpha B_{opt}$ and $C_{opt}/\alpha$ for every
$\alpha \neq 0$: $$\|A - (\alpha B_{opt}) \otimes (C_{opt}/\alpha)\|_F \le \|A - B \otimes
C\|_F$$ for all $B \in \mathbb{R}^{m_1 \times n_1}$ and $C \in \mathbb{R}^{m_2 \times n_2}$.

This is the case $\tilde r = 1$ of (12.3.19), `GolubVanLoan.Chapter12.equation_12_3_19`, because
$B_{opt} \otimes C_{opt} = \sigma_1 U_1 \otimes V_1$. -/
theorem equation_12_3_15 (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ)
    {U : Matrix (Fin (n₁ * m₁)) (Fin (n₁ * m₁)) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n₂ * m₂)) (Fin (n₂ * m₂)) ℝ} (h : IsSVD (rearrangement A) U σ V)
    (h₁ : 0 < n₁ * m₁) (h₂ : 0 < n₂ * m₂) {α : ℝ} (hα : α ≠ 0)
    (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    ‖A - kroneckerFin (α • reshapeVec (√(σ 0) • fun I => U I ⟨0, h₁⟩))
        (α⁻¹ • reshapeVec (√(σ 0) • fun J => V J ⟨0, h₂⟩))‖ ≤ ‖A - kroneckerFin B C‖ := by
  have hopt : kroneckerFin (α • reshapeVec (√(σ 0) • fun I => U I ⟨0, h₁⟩))
      (α⁻¹ • reshapeVec (√(σ 0) • fun J => V J ⟨0, h₂⟩)) =
      ∑ k : Fin 1, σ k • kroneckerFin (reshapeVec fun I => U I (Fin.castLE h₁ k))
        (reshapeVec fun J => V J (Fin.castLE h₂ k)) := by
    rw [Fin.sum_univ_one, kroneckerFin_smul_left, kroneckerFin_smul_right, reshapeVec_smul,
      reshapeVec_smul, kroneckerFin_smul_left, kroneckerFin_smul_right, smul_smul, smul_smul,
      smul_smul, mul_assoc, mul_assoc, Real.mul_self_sqrt (h.nonneg 0), ← mul_assoc,
      mul_inv_cancel₀ hα, one_mul]
    rfl
  have hBC : kroneckerFin B C = ∑ k : Fin 1, kroneckerFin ((fun _ => B) k) ((fun _ => C) k) := by
    rw [Fin.sum_univ_one]
  rw [hopt, hBC]
  exact equation_12_3_19 A h h₁ h₂ _ _

/-! ### Lemma 12.3.2 and the nearest $X \otimes X$ (§12.3.8) -/

section Symmetric

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- For a Schur decomposition $Q^T T Q = \operatorname{diag}(\alpha)$ with $Q$ orthogonal, and
$y = Q^T x$, we have $x^T T x = \sum_i \alpha_i y_i^2$ and $\sum_i y_i^2 = x^T x$. -/
private theorem dotProduct_mulVec_eq_sum {T Q : Matrix (Fin n) (Fin n) ℝ} {α : Fin n → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hT : Qᵀ * T * Q = diagonal α) (x : Fin n → ℝ) :
    x ⬝ᵥ (T *ᵥ x) = ∑ i, α i * (Qᵀ *ᵥ x) i ^ 2 ∧ ∑ i, (Qᵀ *ᵥ x) i ^ 2 = x ⬝ᵥ x := by
  have h1 : Q * Qᵀ = 1 := by
    exact (mem_orthogonalGroup_iff _ _).1 hQ
  have h2 : Qᵀ * Q = 1 := by
    exact (mem_orthogonalGroup_iff' _ _).1 hQ
  have hT' : T = Q * diagonal α * Qᵀ := by
    rw [← hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  have hy : ∀ w : Fin n → ℝ, x ⬝ᵥ (Q *ᵥ w) = (Qᵀ *ᵥ x) ⬝ᵥ w := fun w => by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  constructor
  · rw [hT', ← mulVec_mulVec, ← mulVec_mulVec, hy]
    simp only [dotProduct, mulVec_diagonal, sq]
    exact Finset.sum_congr rfl fun i _ => by ring
  · have h3 : (Qᵀ *ᵥ x) ⬝ᵥ (Qᵀ *ᵥ x) = x ⬝ᵥ x := by
      rw [← hy, mulVec_mulVec, h1, one_mulVec]
    rw [← h3]
    simp [dotProduct, sq]

/-- The column $q_k$ of the orthogonal matrix $Q$ in a Schur decomposition
$Q^T T Q = \operatorname{diag}(\alpha)$ is a unit eigenvector: $q_k^T q_k = 1$ and
$q_k^T T q_k = \alpha_k$. -/
private theorem col_dotProduct {T Q : Matrix (Fin n) (Fin n) ℝ} {α : Fin n → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hT : Qᵀ * T * Q = diagonal α) (k : Fin n) :
    (fun i => Q i k) ⬝ᵥ (fun i => Q i k) = 1 ∧
      (fun i => Q i k) ⬝ᵥ (T *ᵥ fun i => Q i k) = α k := by
  have h2 : Qᵀ * Q = 1 := by
    exact (mem_orthogonalGroup_iff' _ _).1 hQ
  have hy : Qᵀ *ᵥ (fun i => Q i k) = Pi.single k 1 := by
    funext i
    have := congrFun (congrFun h2 i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [Pi.single_apply]
    simpa [mulVec, dotProduct, eq_comm] using this
  obtain ⟨h1, h1'⟩ := dotProduct_mulVec_eq_sum hQ hT fun i => Q i k
  rw [hy] at h1 h1'
  refine ⟨?_, ?_⟩
  · rw [← h1']
    simp [Pi.single_apply]
  · rw [h1]
    simp [Pi.single_apply]

/-- For a Schur decomposition $Q^T T Q = \operatorname{diag}(\alpha)$ and a unit vector $x$: if
$|\alpha_i| \le |\alpha_k|$ for all $i$, then $|x^T T x| \le |\alpha_k|$, and if
$\alpha_i \le \alpha_k$ for all $i$, then $x^T T x \le \alpha_k$. -/
private theorem rayleigh_bounds {T Q : Matrix (Fin n) (Fin n) ℝ} {α : Fin n → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hT : Qᵀ * T * Q = diagonal α) {x : Fin n → ℝ}
    (hx : x ⬝ᵥ x = 1) (k : Fin n) :
    ((∀ i, |α i| ≤ |α k|) → |x ⬝ᵥ (T *ᵥ x)| ≤ |α k|) ∧
      ((∀ i, α i ≤ α k) → x ⬝ᵥ (T *ᵥ x) ≤ α k) := by
  obtain ⟨h1, h2⟩ := dotProduct_mulVec_eq_sum hQ hT x
  rw [hx] at h2
  set y := Qᵀ *ᵥ x
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rw [h1]
    calc |∑ i, α i * y i ^ 2| ≤ ∑ i, |α i| * y i ^ 2 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          simp_rw [abs_mul, abs_sq]
      _ ≤ ∑ i, |α k| * y i ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hk i) (sq_nonneg _)
      _ = |α k| := by rw [← Finset.mul_sum, h2, mul_one]
  · rw [h1]
    calc ∑ i, α i * y i ^ 2 ≤ ∑ i, α k * y i ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hk i) (sq_nonneg _)
      _ = α k := by rw [← Finset.mul_sum, h2, mul_one]

/-- **Lemma 12.3.2** of [golub2013matrix]. Let $M \in \mathbb{R}^{n \times n}$ and
$T = (M + M^T)/2$, and let $Q \in \mathbb{R}^{n \times n}$ be orthogonal with $Q^T T Q =
\operatorname{diag}(\alpha_1, \dots, \alpha_n)$. If $|\alpha_k| = \max_i |\alpha_i|$, then
$$Z_{opt} = \alpha_k q_k q_k^T, \qquad q_k = Q(:, k),$$ minimizes $\|M - Z\|_F$ over all
symmetric $Z \in \mathbb{R}^{n \times n}$ with $\operatorname{rank}(Z) \le 1$.

**Correction.** The source minimizes over $\operatorname{rank}(Z) = 1$. For $T = 0$ no matrix of
rank exactly one attains the infimum. The statement uses $\operatorname{rank}(Z) \le 1$, which
agrees with the source when $T \neq 0$.

The symmetric part $T$ is `Matrix.hermitianPart M`. The statement holds for an arbitrary Schur
decomposition of $T$, as in the source. -/
theorem lemma_12_3_2 (M Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hT : Qᵀ * hermitianPart M * Q = diagonal α) {k : Fin n}
    (hk : ∀ i, |α i| ≤ |α k|) :
    IsMinOn (fun Z => ‖M - Z‖) {Z | Z.IsSymm ∧ Z.rank ≤ 1}
      (α k • vecMulVec (fun i => Q i k) fun i => Q i k) := by
  have : Nonempty (Fin n) := ⟨k⟩
  set q : Fin n → ℝ := fun i => Q i k
  obtain ⟨hq, hqT⟩ := col_dotProduct hQ hT k
  have hqM : q ⬝ᵥ (M *ᵥ q) = α k := by rw [← dotProduct_mulVec_hermitianPart]; exact hqT
  have hopt : ‖M - α k • vecMulVec q q‖ ^ 2 = ‖M‖ ^ 2 - α k ^ 2 := by
    rw [norm_sub_smul_vecMulVec_self_sq M hq, hqM]
    ring
  rintro Z ⟨hZs, hZr⟩
  obtain ⟨β, x, hx, rfl⟩ := exists_eq_smul_vecMulVec_self_of_rank_le_one hZs hZr
  have ht : |x ⬝ᵥ (M *ᵥ x)| ≤ |α k| := by
    rw [← dotProduct_mulVec_hermitianPart]
    exact (rayleigh_bounds hQ hT hx k).1 hk
  have ht2 := sq_le_sq.2 ht
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  change ‖M - α k • vecMulVec q q‖ ^ 2 ≤ ‖M - β • vecMulVec x x‖ ^ 2
  rw [hopt, norm_sub_smul_vecMulVec_self_sq M hx]
  nlinarith [sq_nonneg (β - x ⬝ᵥ (M *ᵥ x)), sq_abs (x ⬝ᵥ (M *ᵥ x)), sq_abs (α k)]

end Symmetric

section NearestSelf

open scoped Matrix.Norms.Frobenius

/-- **§12.3.8** of [golub2013matrix], the nearest $X \otimes X$. Let
$A \in \mathbb{R}^{m^2 \times m^2}$, let $T = (\mathcal{R}(A) + \mathcal{R}(A)^T)/2$, and let
$Q$ be orthogonal with $Q^T T Q = \operatorname{diag}(\alpha)$. If $\alpha_k = \max_i \alpha_i$,
then $$X_{opt} = \operatorname{reshape}\bigl(\sqrt{\alpha_k^+}\, q_k, m, m\bigr), \qquad
\alpha_k^+ = \max(\alpha_k, 0),$$ minimizes $\phi_{sym}(X) = \|A - X \otimes X\|_F$ over all
$X \in \mathbb{R}^{m \times m}$.

**Correction.** The source states that "the solution $X_{opt}$ is a reshaping of an eigenvector
associated with the symmetric part of $\mathcal{R}(A)$". The statement here is the form of this
claim that is true. Lemma 12.3.2 alone does not give it:
$\operatorname{vec}(X) \operatorname{vec}(X)^T$ is positive semidefinite, so a negative
eigenvalue of largest modulus is not admissible. The statement takes the algebraically largest
eigenvalue and its positive part. -/
theorem nearest_kronecker_self {m : ℕ} (A Q : Matrix (Fin (m * m)) (Fin (m * m)) ℝ)
    (α : Fin (m * m) → ℝ) (hQ : Q ∈ orthogonalGroup (Fin (m * m)) ℝ)
    (hT : Qᵀ * hermitianPart (rearrangement A) * Q = diagonal α) {k : Fin (m * m)}
    (hk : ∀ i, α i ≤ α k) :
    IsMinOn (fun X : Matrix (Fin m) (Fin m) ℝ => ‖A - kroneckerFin X X‖) Set.univ
      (reshapeVec (√(max (α k) 0) • fun i => Q i k)) := by
  intro X _
  change ‖A - kroneckerFin (reshapeVec (√(max (α k) 0) • fun i => Q i k))
      (reshapeVec (√(max (α k) 0) • fun i => Q i k))‖ ≤ ‖A - kroneckerFin X X‖
  rw [equation_12_3_20, equation_12_3_20, vecFin_reshapeVec]
  set R := rearrangement A
  set a := max (α k) 0 with ha
  set q : Fin (m * m) → ℝ := fun i => Q i k
  obtain ⟨hq, hqT⟩ := col_dotProduct hQ hT k
  have hqR : q ⬝ᵥ (R *ᵥ q) = α k := by rw [← dotProduct_mulVec_hermitianPart]; exact hqT
  have ha0 : 0 ≤ a := le_max_right _ _
  have haα : a * α k = a ^ 2 := by
    rcases le_total 0 (α k) with h | h
    · rw [ha, max_eq_left h]; ring
    · rw [ha, max_eq_right h]; ring
  have hopt : ‖R - vecMulVec (√a • q) (√a • q)‖ ^ 2 = ‖R‖ ^ 2 - a ^ 2 := by
    rw [smul_vecMulVec, vecMulVec_smul, smul_smul, Real.mul_self_sqrt ha0,
      norm_sub_smul_vecMulVec_self_sq R hq, hqR]
    nlinarith [haα]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hopt]
  set x := vecFin X
  by_cases hx0 : x ⬝ᵥ x = 0
  · have : x = 0 := by
      funext i
      have h := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j)) |>.1 hx0 i
        (Finset.mem_univ i)
      simpa using h
    have h0 : vecMulVec x x = 0 := by
      rw [this]
      ext i j
      simp [vecMulVec_apply]
    rw [h0, sub_zero]
    nlinarith [sq_nonneg a]
  · have hβ : 0 < x ⬝ᵥ x := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)) (Ne.symm hx0)
    set β := x ⬝ᵥ x
    set w := (√β)⁻¹ • x
    have hsβ : 0 < √β := Real.sqrt_pos.2 hβ
    have hw : w ⬝ᵥ w = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← sq, inv_pow,
        Real.sq_sqrt hβ.le, inv_mul_cancel₀ hβ.ne']
    have hc : β * ((√β)⁻¹ * (√β)⁻¹) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hβ.le, mul_inv_cancel₀ hβ.ne']
    have hxw : vecMulVec x x = β • vecMulVec w w := by
      ext i j
      simp only [w, vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(x i * x j)) * hc
    have ht : w ⬝ᵥ (R *ᵥ w) ≤ a := by
      rw [← dotProduct_mulVec_hermitianPart]
      exact ((rayleigh_bounds hQ hT hw k).2 hk).trans (le_max_left _ _)
    rw [hxw, norm_sub_smul_vecMulVec_self_sq R hw]
    nlinarith [sq_nonneg (β - a)]

end NearestSelf

/-! ### The reshaping identity of §12.3.10 -/

/-- **§12.3.10** of [golub2013matrix], the reshaping identity. Let
$y = (B_1 \otimes \cdots \otimes B_p) x$, and write
$B_1 \otimes \cdots \otimes B_p = P \otimes Q$ with $P = B_1 \otimes \cdots \otimes B_i \in
\mathbb{R}^{M_i \times N_i}$ and $Q = B_{i+1} \otimes \cdots \otimes B_p$, by the associativity
(1.3.4) of Chapter 1. Then $$\operatorname{reshape}(y, M_p/M_i, M_i) = Q \cdot
\operatorname{reshape}(x, N_p/N_i, N_i) \cdot P^T.$$

The Lean statement is for the two factors: for $P \in \mathbb{R}^{a \times b}$,
$Q \in \mathbb{R}^{c \times e}$ and $x \in \mathbb{R}^{be}$, $\operatorname{reshape}((P \otimes
Q) x, c, a) = Q \operatorname{reshape}(x, e, b) P^T$. -/
theorem kronecker_mulVec_reshape {a b c e : ℕ} (P : Matrix (Fin a) (Fin b) ℝ)
    (Q : Matrix (Fin c) (Fin e) ℝ) (x : Fin (b * e) → ℝ) :
    reshapeVec (kroneckerFin P Q *ᵥ x) = Q * reshapeVec x * Pᵀ := by
  apply vecFin_injective
  rw [vecFin_reshapeVec, ← kroneckerFin_mulVec_vecFin, vecFin_reshapeVec]

/-! ### Lemma 12.3.3 -/

section SkewNearest

open scoped Matrix.Norms.Frobenius

/-- **Lemma 12.3.3** of [golub2013matrix]. Let $M \in \mathbb{R}^{n \times n}$ and
$S = (M - M^T)/2$. Let $u, v \in \mathbb{R}^n$ be orthonormal, let $\mu = \rho(S)$ be the
spectral radius of $S$, and assume $Sv = \mu u$. Then $$Z_{opt} = \mu (uv^T - vu^T)$$ minimizes
$\|M - Z\|_F$ over all skew-symmetric $Z \in \mathbb{R}^{n \times n}$ with
$\operatorname{rank}(Z) \le 2$.

**Correction.** The source minimizes over the skew-symmetric matrices of rank $2$. For $S = 0$
the minimizer $Z_{opt} = 0$ has rank $0$, so the statement uses rank at most two.

**Generalization.** The source assumes $S [u \,|\, v] = [u \,|\, v] \begin{bmatrix} 0 & \mu \\
-\mu & 0 \end{bmatrix}$. Only its second column, $Sv = \mu u$, is needed.

The spectral radius is computed over $\mathbb{C}$, `Matrix.complexSpectralRadius`. For the
normal matrix $S$ it equals $\|S\|_2$
(`Matrix.complexSpectralRadius_toReal_eq_lpOpNorm_two_of_transpose_eq_neg`). The proof
specializes `Matrix.isMinOn_frobenius_norm_sub_skew_rank_le_two`. -/
theorem lemma_12_3_3 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {u v : Fin n → ℝ} {μ : ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (hSv : ((1 / 2 : ℝ) • (M - Mᵀ)) *ᵥ v = μ • u)
    (hμ : μ = (complexSpectralRadius ((1 / 2 : ℝ) • (M - Mᵀ))).toReal) :
    IsMinOn (fun Z => ‖M - Z‖) {Z | Zᵀ = -Z ∧ Z.rank ≤ 2}
      (μ • (vecMulVec u v - vecMulVec v u)) := by
  have hskew : ((1 / 2 : ℝ) • (M - Mᵀ))ᵀ = -((1 / 2 : ℝ) • (M - Mᵀ)) := by
    rw [transpose_smul, transpose_sub, transpose_transpose, ← smul_neg, neg_sub]
  rw [complexSpectralRadius_toReal_eq_lpOpNorm_two_of_transpose_eq_neg hskew] at hμ
  exact isMinOn_frobenius_norm_sub_skew_rank_le_two M hu hv huv hSv hμ

end SkewNearest

end GolubVanLoan.Chapter12
