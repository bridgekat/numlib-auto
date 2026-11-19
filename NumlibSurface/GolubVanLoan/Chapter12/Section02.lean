/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Semiseparable
import Numlib.LinearAlgebra.Matrix.RealSchur
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter12.Section01

/-!
# Golub and Van Loan, Section 12.2: Structured-rank problems

This module formalizes §12.2 of [golub2013matrix], on matrices whose off-diagonal blocks have rank
at most one. A matrix $A \in \mathbb{R}^{n \times n}$ is semiseparable if every submatrix
$A(i_1{:}i_2, j_1{:}j_2)$ with $j_2 \le i_1$ or $i_2 \le j_1$ has rank at most one, and
quasiseparable if this holds for the submatrices with $j_2 < i_1$ or $i_2 < j_1$, which lie strictly
below or strictly above the diagonal. The module proves the characterizations (12.2.1) and (12.2.5),
the generator representation (12.2.6) and the quasiseparable representation (12.2.8), and the facts
of §12.2.3 on inverses: the inverse of a tridiagonal matrix is semiseparable, and the inverse of a
quasiseparable matrix is quasiseparable. It treats triangular semiseparable matrices with the fast
product and solve (12.2.9), the LU factorization Algorithm 12.2.1, the Givens-vector representation
(12.2.11), the QR factorization Algorithm 12.2.2 with (12.2.14) and (12.2.16), the banded inverses
of §12.2.8, and the orthogonal Hessenberg eigenproblem (12.2.18)–(12.2.19) with the facts of
§12.2.10.

The proofs specialize `Numlib.LinearAlgebra.Matrix.Semiseparable`, which rests on the nullity
theorem, and `Numlib.LinearAlgebra.Matrix.RealSchur`. The Givens pairs of Algorithm 12.2.2 come from
Algorithm 5.1.3, `GolubVanLoan.Chapter05.algorithm_5_1_3`.

## Main definitions

* Algorithm 12.2.1, `GolubVanLoan.Chapter12.algorithm_12_2_1`: the LU factorization of a
  semiseparable matrix $\mathbf{S}(u, v, t, u .* v, p, q, r)$ from its representation.
* Algorithm 12.2.2, `GolubVanLoan.Chapter12.SemiseparableQRState`: the state of the loop of
  Algorithm 12.2.2.
* Algorithm 12.2.2, `GolubVanLoan.Chapter12.algorithm_12_2_2Step`: one step of the loop of Algorithm
  12.2.2.
* Algorithm 12.2.2, `GolubVanLoan.Chapter12.algorithm_12_2_2`: the QR factorization of
  $\operatorname{tril}(uv^T) + \operatorname{triu}(pq^T, 1)$ by $n - 1$ Givens rotations.

## Main results

* Equation (12.2.1), `GolubVanLoan.Chapter12.equation_12_2_1`: the characterization of semiseparable
  matrices by the rank of all their blocks that do not cross the diagonal.
* Equation (12.2.3), `GolubVanLoan.Chapter12.equation_12_2_3`: the entries of $B(r)^{-1}$, which is
  semiseparable.
* §12.2.1, `GolubVanLoan.Chapter12.unitBidiagonal_introduces_zeros`: $B(r)^T x = x_1 e_1$ for
  $r = x(2{:}n) ./ x(1{:}n-1)$.
* Equation (12.2.4), `GolubVanLoan.Chapter12.equation_12_2_4`: the entries of a product of
  $2 \times 2$ blocks in consecutive coordinate planes, which is quasiseparable.
* Equation (12.2.5), `GolubVanLoan.Chapter12.equation_12_2_5`: the characterization of
  quasiseparable matrices, and semiseparable matrices are quasiseparable.
* Equation (12.2.6), `GolubVanLoan.Chapter12.equation_12_2_6`: the generator representation is
  $\mathbf{S}(u, v, 1, d, p, q, 1)$, quasiseparable, and semiseparable if $d = u .* v = p .* q$.
* §12.2.3, `GolubVanLoan.Chapter12.unitBidiagonal_not_generatorRepresentable`: for $n \ge 3$, $B(r)$
  has no generator representation.
* Equation (12.2.7), `GolubVanLoan.Chapter12.equation_12_2_7`: the entrywise product of two
  quasiseparable matrices is quasiseparable.
* Equation (12.2.8), `GolubVanLoan.Chapter12.equation_12_2_8`: a matrix is quasiseparable if and
  only if it has a quasiseparable representation, in corrected form.
* Equation (12.2.8), `GolubVanLoan.Chapter12.equation_12_2_8_b`: the special cases of
  $\mathbf{S}(u, v, t, d, p, q, r)$: semiseparable, symmetric, and semiseparable plus diagonal.
* Fact 1 of §12.2.3, `GolubVanLoan.Chapter12.inv_tridiagonal_isSemiseparable`: the inverse of a
  nonsingular tridiagonal matrix is semiseparable.
* Fact 2 of §12.2.3, `GolubVanLoan.Chapter12.inv_isQuasiseparable`: the inverse of a nonsingular
  quasiseparable matrix is quasiseparable.
* Fact 3 of §12.2.3, `GolubVanLoan.Chapter12.inv_diagonal_add_semiseparable`: the inverse of
  diagonal plus semiseparable is diagonal plus semiseparable.
* §12.2.4, `GolubVanLoan.Chapter12.triangular_semiseparable_rep`: the representations of lower and
  upper triangular semiseparable matrices.
* Equation (12.2.9), `GolubVanLoan.Chapter12.equation_12_2_9`: the fast product with
  $\operatorname{triu}(pq^T) .* B(r)^{-1}$ and the solution of the corresponding system.
* §12.2.5, `GolubVanLoan.Chapter12.semiseparable_lu_factors`: the LU factors of a semiseparable
  matrix are semiseparable, in corrected form.
* Algorithm 12.2.1, `GolubVanLoan.Chapter12.algorithm_12_2_1_spec`: in exact arithmetic, Algorithm
  12.2.1 returns an LU factorization, with closed forms for $\tau$ and $\tilde p$.
* Equation (12.2.11), `GolubVanLoan.Chapter12.equation_12_2_11`: the Givens-vector representation of
  a lower triangular semiseparable matrix.
* Equation (12.2.14), `GolubVanLoan.Chapter12.equation_12_2_14`: the rotations of the Givens-vector
  representation reduce $A$ to upper triangular form.
* Algorithm 12.2.2, `GolubVanLoan.Chapter12.algorithm_12_2_2_spec`: in exact arithmetic, Algorithm
  12.2.2 returns an orthogonal $Q^T$ with $Q^T A = \operatorname{triu}(fg^T + hq^T)$.
* Equation (12.2.16), `GolubVanLoan.Chapter12.equation_12_2_16`: the factor $R$ is the upper
  triangular part of a matrix of rank at most two.
* §12.2.8, `GolubVanLoan.Chapter12.inv_banded_of_generatorRepresentable`: the inverse of a
  nonsingular $\{p, q\}$-generator representable matrix is banded.
* Equation (12.2.18), `GolubVanLoan.Chapter12.equation_12_2_18`: the product form of an orthogonal
  upper Hessenberg matrix, in corrected form.
* Equation (12.2.19), `GolubVanLoan.Chapter12.equation_12_2_19`: the eigenvalues of an orthogonal
  matrix of order $2m$ with determinant $1$ are $m$ conjugate pairs $e^{\pm i\theta_k}$.
* §12.2.10, `GolubVanLoan.Chapter12.orthogonalHessenberg_isQuasiseparable`: an orthogonal upper
  Hessenberg matrix is quasiseparable.
* Fact 1 of §12.2.10, `GolubVanLoan.Chapter12.orthogonalHessenberg_fact_1`: $H = G_1 \cdots G_n$ is
  similar to $H_o H_e$.
* Fact 2 of §12.2.10, `GolubVanLoan.Chapter12.orthogonalHessenberg_fact_2`: the eigenvalues of
  $(H_o \pm H_e)/2$ are $\pm\cos(\theta_k/2)$ and $\pm\sin(\theta_k/2)$.

## Conventions

* Indices are 0-based. $B(r)$ for $r \in \mathbb{R}^{n-1}$, the unit upper bidiagonal matrix with
  $-r_i$ in position $(i, i+1)$, is `Matrix.unitBidiagonal n r` with `r : ℕ → ℝ`; the entries of `r`
  after the index $n - 2$ are not used.
* The matrix $\mathbf{S}(u, v, t, d, p, q, r)$ of (12.2.8) has the entries
  $u_i t_j \cdots t_{i-1} v_j$ below the diagonal, $d_i$ on the diagonal and
  $p_i r_i \cdots r_{j-1} q_j$ above the diagonal. It is `Matrix.quasiseparableOf u v t d p q r`,
  with the arguments in the order of the source.
* The MATLAB operations $\operatorname{tril}(A, -1)$, $\operatorname{triu}(A, 1)$ and
  $\operatorname{diag}(A)$ are `Matrix.strictLower`, `Matrix.strictUpper` and `Matrix.diagPart`, and
  the entrywise product $.*$ of matrices is `⊙`. The entrywise product and quotient of vectors are
  `*` and `/` of functions.
* The product $G_1 \cdots G_{n-1}$ of $2 \times 2$ blocks embedded in the coordinate planes
  $(k, k+1)$ is `Matrix.givensChain`.

## Implementation notes

* The quasiseparable representation with the transfer products $t_{j+1} \cdots t_{i-1}$ and
  $r_{i+1} \cdots r_{j-1}$ of Eidelman and Gohberg is `Matrix.quasiseparableRep`. It has one
  transfer factor fewer than $\mathbf{S}(u, v, t, d, p, q, r)$, and it represents every
  quasiseparable matrix.
* Algorithms 12.2.1 and 12.2.2 are monadic programs with a rounding hook `rnd`, as in the algorithm
  conventions of `NumlibSurface.GolubVanLoan`. The state of Algorithm 12.2.2 is the structure
  `GolubVanLoan.Chapter12.SemiseparableQRState`. The source analyses no rounding errors in this
  section, so there are only exact specifications. The exact specification of Algorithm 12.2.2 is a
  downward induction on the source's matrices $A^{(k)} = G_k \cdots G_{n-1} A$.

## Deviations from the source

* **Equation (12.2.3)** (correction). The inverse blocks have rank at most one, allowing
  vanishing blocks. See `GolubVanLoan.Chapter12.equation_12_2_3`.
* **Equations (12.2.15)–(12.2.16)** (correction). The second term in (12.2.15) uses the strict
  upper triangle, as in Algorithm 12.2.2, so the diagonal is included only once. See
  `GolubVanLoan.Chapter12.equation_12_2_16`.
* **§12.2.10, quasiseparability and Facts 1–2** (generalization). The rank bound holds for all
  orthogonal upper Hessenberg matrices. The reflector product similarity and the even-order
  spectral relation allow arbitrary angles. See
  `GolubVanLoan.Chapter12.orthogonalHessenberg_isQuasiseparable`,
  `GolubVanLoan.Chapter12.orthogonalHessenberg_fact_1`, and
  `GolubVanLoan.Chapter12.orthogonalHessenberg_fact_2`.
* **§12.2.3, $B(r)$ has no generator representation** (generalization). The source takes $r$ with
  nonzero entries; $r_1 \neq 0$ and $r_2 \neq 0$ suffice. See
  `GolubVanLoan.Chapter12.unitBidiagonal_not_generatorRepresentable`.
* **Equation (12.2.8)** (correction). Not every quasiseparable matrix is
  $\mathbf{S}(u, v, t, d, p, q, r)$: for $n \ge 3$ and $r_1 r_2 \neq 0$, $B(r)$ is not. The
  statement uses the representation of Eidelman and Gohberg. See
  `GolubVanLoan.Chapter12.equation_12_2_8`.
* **§12.2.5** (correction). The lower LU factor of a semiseparable matrix need not be semiseparable
  when $A$ is singular. The statement assumes that the leading principal submatrices are
  nonsingular. See `GolubVanLoan.Chapter12.semiseparable_lu_factors`.
* **Algorithm 12.2.1** (correction). The hypothesis "$A$ has an LU factorization" does not ensure
  the divisions by $u_k$. The statement assumes $u_k \neq 0$ for $k = 1, \dots, n - 1$. See
  `GolubVanLoan.Chapter12.algorithm_12_2_1_spec`.
* **Algorithm 12.2.1** (typo). The text's "$M = B(\tau)$" should read $M = B(\tau)^T$. See
  `GolubVanLoan.Chapter12.algorithm_12_2_1_spec`.
* **Equation (12.2.11)** (correction). The Givens-vector representation needs $(A_L)_{n1} \neq 0$.
  See `GolubVanLoan.Chapter12.equation_12_2_11`.
* **Algorithm 12.2.2** (typo). The update of $g_k$ prints $u_k$ for $\tilde u_k$. See
  `GolubVanLoan.Chapter12.algorithm_12_2_2Step`.
* **Algorithm 12.2.2** (generalization). The correctness does not need the hypothesis
  $u .* v = p .* q$. See `GolubVanLoan.Chapter12.algorithm_12_2_2_spec`.
* **Equation (12.2.18)** (correction). The source assumes a nonzero subdiagonal. The statement
  assumes a positive subdiagonal, even order and $\det H = 1$. See
  `GolubVanLoan.Chapter12.equation_12_2_18`.

## Not formalized

* **The operation and storage counts.** Operation counts are out of scope for the library.
* **The $\{p, q\}$-semiseparable definition of §12.2.8.** It is misprinted.
* **The extended, sequentially semiseparable and hierarchical classes of §12.2.8.** The display
  (12.2.17) shows only a shape.
* **§12.2.9.** It describes eigenvalue methods in prose with citations.
* **The pivoting variant of Algorithm 12.2.1.** The source describes it in words only.
* **Fact 3 of §12.2.10.** It names neither the perfect shuffles nor the positions of the bidiagonal
  blocks, and the source proves nothing.
* **The Problems of §12.2.** Problems are out of scope for the library.
-/

open Matrix

namespace GolubVanLoan.Chapter12

variable {n : ℕ}

/-! ### Semiseparable and quasiseparable matrices (§12.2.1–12.2.3) -/

/-- **Equation (12.2.1)** of [golub2013matrix]. A matrix $A \in \mathbb{R}^{n \times n}$ is
semiseparable if and only if every submatrix $A(i_1{:}i_2, j_1{:}j_2)$ with $j_2 \le i_1$ or
$i_2 \le j_1$ has rank at most one.

The definition `Matrix.IsSemiseparable` asks this only of the maximal such blocks
$A(k{:}n, 1{:}k)$ and $A(1{:}k, k{:}n)$. The submatrix $A(i_1{:}i_2, j_1{:}j_2)$ is `A.toBlock`
for the index intervals `Set.Icc i₁ i₂` and `Set.Icc j₁ j₂`. -/
theorem equation_12_2_1 (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsSemiseparable ↔ ∀ i₁ i₂ j₁ j₂ : Fin n, j₂ ≤ i₁ ∨ i₂ ≤ j₁ →
      (A.toBlock (· ∈ Set.Icc i₁ i₂) (· ∈ Set.Icc j₁ j₂)).rank ≤ 1 := by
  convert isSemiseparable_iff_forall_rank_toBlock_Icc_le (A := A)

/-- **Equation (12.2.3)** of [golub2013matrix] and the sentence before it. Let
$r \in \mathbb{R}^{n-1}$. The inverse of $B(r)$ is upper triangular, with the entries
$$[B(r)^{-1}]_{ij} = r_i r_{i+1} \cdots r_{j-1} \qquad (i \le j),$$ in particular $1$ on the
diagonal, and $B(r)^{-1}$ is semiseparable.

The source leaves the proof to Problem P12.2.1.

**Correction.** The source says relevant blocks have unit rank. The definition uses rank at
most one, so it covers rank-zero blocks, including blocks that vanish when some $r_k = 0$. -/
theorem equation_12_2_3 (r : ℕ → ℝ) :
    (unitBidiagonal n r)⁻¹ =
        of (fun (i j : Fin n) => if i ≤ j then ∏ l ∈ Finset.Ico (i : ℕ) j, r l else 0) ∧
      (unitBidiagonal n r)⁻¹.IsSemiseparable :=
  ⟨inv_unitBidiagonal r, isSemiseparable_inv_unitBidiagonal r⟩

/-- **§12.2.1** of [golub2013matrix], zeros introduced by $B(r)$. Let $x \in \mathbb{R}^n$ with
$x_1, \dots, x_{n-1} \neq 0$, and let $r = x(2{:}n) ./ x(1{:}n-1)$, that is,
$r_k = x_{k+1}/x_k$. Then $$B(r)^T x = x_1 e_1.$$

The order of the matrix is `n + 1` in the Lean statement. -/
theorem unitBidiagonal_introduces_zeros {x : Fin (n + 1) → ℝ} {r : ℕ → ℝ}
    (hx : ∀ (l : ℕ) (h : l < n), x ⟨l, by omega⟩ ≠ 0)
    (hr : ∀ (l : ℕ) (h : l < n), r l = x ⟨l + 1, by omega⟩ / x ⟨l, by omega⟩) :
    (unitBidiagonal (n + 1) r)ᵀ *ᵥ x = Pi.single 0 (x 0) :=
  unitBidiagonal_transpose_mulVec_eq_single hx hr

/-- **Equation (12.2.4)** of [golub2013matrix]. Let $M_k = \begin{bmatrix} \alpha_k & \beta_k \\
\gamma_k & \delta_k \end{bmatrix}$ for $k = 1, \dots, n - 1$, and let $M = M_1 \cdots M_{n-1}$
be the product of these blocks embedded in the coordinate planes $(k, k+1)$ of $\mathbb{R}^n$.
Then $$m_{ij} = \begin{cases} \gamma_j & \text{if } i = j + 1, \\ \delta_{i-1} \beta_i \cdots
\beta_{j-1} \alpha_j & \text{if } i \le j, \\ 0 & \text{if } i > j + 1, \end{cases}$$ with
$\delta_0 = 1$ and $\alpha_n = 1$, and $M$ is quasiseparable.

Here $n = N + 1$, and $M$ is `Matrix.givensChain N M`. The Lean statement is 0-based: the block
$M_k$ is `M (k - 1)`.

**Generalization.** General entry formula extends the five-dimensional display to every positive
order.
-/
theorem equation_12_2_4 {N : ℕ} (M : ℕ → Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ i j : Fin (N + 1), givensChain N M i j =
      if (i : ℕ) = j + 1 then M j 1 0
      else if (i : ℕ) ≤ j then
        ((if (i : ℕ) = 0 then 1 else M (i - 1) 1 1) * ∏ l ∈ Finset.Ico (i : ℕ) j, M l 0 1) *
          (if (j : ℕ) = N then 1 else M j 0 0)
      else 0) ∧
      (givensChain N M).IsQuasiseparable :=
  ⟨givensChain_apply, givensChain_isQuasiseparable⟩

/-- **Equation (12.2.5)** of [golub2013matrix] and the sentence after it. A matrix
$A \in \mathbb{R}^{n \times n}$ is quasiseparable if and only if every submatrix
$A(i_1{:}i_2, j_1{:}j_2)$ with $j_2 < i_1$ or $i_2 < j_1$ has rank at most one. Every
semiseparable matrix is quasiseparable.

The definition `Matrix.IsQuasiseparable` asks this only of the maximal such blocks
$A(k+1{:}n, 1{:}k)$ and $A(1{:}k, k+1{:}n)$. -/
theorem equation_12_2_5 (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.IsQuasiseparable ↔ ∀ i₁ i₂ j₁ j₂ : Fin n, j₂ < i₁ ∨ i₂ < j₁ →
      (A.toBlock (· ∈ Set.Icc i₁ i₂) (· ∈ Set.Icc j₁ j₂)).rank ≤ 1) ∧
      (A.IsSemiseparable → A.IsQuasiseparable) := by
  refine ⟨?_, IsSemiseparable.isQuasiseparable⟩
  convert isQuasiseparable_iff_forall_rank_toBlock_Icc_le (A := A)

/-- **Equation (12.2.6)** of [golub2013matrix]. Let $u, v, d, p, q \in \mathbb{R}^n$. The generator
representation $$\operatorname{tril}(uv^T, -1) + \operatorname{diag}(d) +
\operatorname{triu}(pq^T, 1)$$ is the matrix $\mathbf{S}(u, v, 1, d, p, q, 1)$. It is
quasiseparable, and it is semiseparable if $d = u .* v = p .* q$.

The vectors of ones $t = r = 1$ are the constant sequence `1`. -/
theorem equation_12_2_6 (u v d p q : Fin n → ℝ) :
    (vecMulVec u v).strictLower + diagonal d + (vecMulVec p q).strictUpper =
        quasiseparableOf u v 1 d p q 1 ∧
      (quasiseparableOf u v 1 d p q 1).IsQuasiseparable ∧
      (d = u * v → d = p * q → (quasiseparableOf u v 1 d p q 1).IsSemiseparable) := by
  refine ⟨?_, isQuasiseparable_quasiseparableOf _ _ _ _ _ _ _,
    isSemiseparable_quasiseparableOf _ _ _ _ _ _ _⟩
  ext i j
  simp only [Matrix.add_apply, strictLower, strictUpper, of_apply, vecMulVec_apply,
    diagonal_apply, quasiseparableOf, Pi.one_apply, Finset.prod_const_one, mul_one]
  rcases lt_trichotomy j i with h | rfl | h
  · simp [h, h.ne', not_lt.2 h.le]
  · simp
  · simp [h, h.ne, not_lt.2 h.le]

/-- **§12.2.3** of [golub2013matrix], $B(r)$ has no generator representation. Let $n \ge 3$ and let
$r \in \mathbb{R}^{n-1}$ with $r_1 \neq 0$ and $r_2 \neq 0$. Then $B(r)$ has no generator
representation (12.2.6): $B(r) \neq \mathbf{S}(u, v, 1, d, p, q, 1)$ for all
$u, v, d, p, q \in \mathbb{R}^n$.

**Generalization.** The source takes $r$ with nonzero entries. The first two entries suffice.

In the 0-based Lean statement, $r_1$ and $r_2$ are `r 0` and `r 1`. -/
theorem unitBidiagonal_not_generatorRepresentable {r : ℕ → ℝ} (hn : 3 ≤ n) (h₀ : r 0 ≠ 0)
    (h₁ : r 1 ≠ 0) (u v d p q : Fin n → ℝ) :
    unitBidiagonal n r ≠ quasiseparableOf u v 1 d p q 1 :=
  unitBidiagonal_ne_generatorRep hn h₀ h₁ u v d p q

/-- **Equation (12.2.7)** of [golub2013matrix]. If $A, B \in \mathbb{R}^{n \times n}$ are
quasiseparable, then their entrywise product $A .* B$ is quasiseparable.

The source leaves the proof to Problem P12.2.8. The entrywise product is `A ⊙ B`. -/
theorem equation_12_2_7 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsQuasiseparable)
    (hB : B.IsQuasiseparable) : (A ⊙ B).IsQuasiseparable :=
  hA.hadamard hB

/-- **Equation (12.2.8)** of [golub2013matrix], in corrected form. A matrix
$A \in \mathbb{R}^{n \times n}$ is quasiseparable if and only if there are
$u, v, d, p, q \in \mathbb{R}^n$ and sequences $t$ and $r$ with $$a_{ij} = \begin{cases} u_i
\bigl(\prod_{j < l < i} t_l\bigr) v_j & \text{if } i > j, \\ d_i & \text{if } i = j, \\ p_i
\bigl(\prod_{i < l < j} r_l\bigr) q_j & \text{if } i < j. \end{cases}$$ Moreover, if $n \ge 3$
and $r \in \mathbb{R}^{n-1}$ has $r_1 \neq 0$ and $r_2 \neq 0$, then $B(r)$ is quasiseparable,
but $B(r) \neq \mathbf{S}(u, v, t, d, p, q, r')$ for all $u, v, t, d, p, q, r'$.

**Correction.** The source states that $A$ is quasiseparable if and only if
$A = \mathbf{S}(u, v, t, d, p, q, r)$ for some $u, v, t, d, p, q, r$. This is false for
$n \ge 3$. The entries of $\mathbf{S}(u, v, t, d, p, q, r)$ satisfy
$a_{12} a_{23} = a_{13} p_2 q_2$, but $B(r)$ with $r_1 r_2 \neq 0$ has
$a_{12} a_{23} = r_1 r_2 \neq 0$ and $a_{13} = 0$. The statement uses instead the representation
of Eidelman and Gohberg, `Matrix.quasiseparableRep`, which has one transfer factor fewer. -/
theorem equation_12_2_8 (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.IsQuasiseparable ↔ ∃ u v t d p q r, A = quasiseparableRep u v t d p q r) ∧
      (3 ≤ n → ∀ r : ℕ → ℝ, r 0 ≠ 0 → r 1 ≠ 0 → (unitBidiagonal n r).IsQuasiseparable ∧
        ∀ u v t d p q r', unitBidiagonal n r ≠ quasiseparableOf u v t d p q r') :=
  ⟨exists_quasiseparableRep, fun hn r h₀ h₁ =>
    ⟨isQuasiseparable_unitBidiagonal r,
      fun u v t d p q r' => unitBidiagonal_ne_quasiseparableOf hn h₀ h₁ u v t d p q r'⟩⟩

/-- **Equation (12.2.8)** of [golub2013matrix], the special cases listed after it. Let
$u, v, d, p, q \in \mathbb{R}^n$, and let $t$ and $r$ be sequences. If $d = u .* v = p .* q$,
then $\mathbf{S}(u, v, t, d, p, q, r)$ is semiseparable. The matrix
$\mathbf{S}(u, v, t, d, v, u, t)$, with $q = u$, $p = v$ and $r = t$, is symmetric. If
$u .* v = p .* q$, then $\mathbf{S}(u, v, t, d, p, q, r) - \operatorname{diag}(d - u .* v)$ is
semiseparable, so $\mathbf{S}(u, v, t, d, p, q, r)$ is semiseparable plus diagonal.

The case $t = r = 1$, the generator representation (12.2.6), is
`GolubVanLoan.Chapter12.equation_12_2_6`. -/
theorem equation_12_2_8_b (u v d p q : Fin n → ℝ) (t r : ℕ → ℝ) :
    (d = u * v → d = p * q → (quasiseparableOf u v t d p q r).IsSemiseparable) ∧
      (quasiseparableOf u v t d v u t)ᵀ = quasiseparableOf u v t d v u t ∧
      (u * v = p * q →
        (quasiseparableOf u v t d p q r - diagonal (d - u * v)).IsSemiseparable) := by
  refine ⟨isSemiseparable_quasiseparableOf _ _ _ _ _ _ _, transpose_quasiseparableOf _ _ _ _ _ _ _,
    fun h => ?_⟩
  have : quasiseparableOf u v t d p q r - diagonal (d - u * v) =
      quasiseparableOf u v t (u * v) p q r := by
    ext i j
    simp only [Matrix.sub_apply, quasiseparableOf, of_apply, diagonal_apply, Pi.sub_apply,
      Pi.mul_apply]
    rcases lt_trichotomy j i with hji | rfl | hji
    · simp [hji, hji.ne']
    · simp
    · simp [hji.ne, not_lt.2 hji.le]
  rw [this]
  exact isSemiseparable_quasiseparableOf _ _ _ _ _ _ _ rfl h

/-- **Fact 1 of §12.2.3** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular
and tridiagonal. Then $A^{-1}$ is semiseparable. If moreover all subdiagonal and superdiagonal
entries of $A$ are nonzero, then $A^{-1}$ has a generator representation:
$A^{-1} = \mathbf{S}(u, v, 1, u .* v, p, q, 1)$ for some $u, v, p, q \in \mathbb{R}^n$ with
$u .* v = p .* q$. -/
theorem inv_tridiagonal_isSemiseparable {A : Matrix (Fin n) (Fin n) ℝ} (hT : A.IsTridiagonal)
    (hA : IsUnit A) :
    A⁻¹.IsSemiseparable ∧
      ((∀ i j : Fin n, (i : ℕ) = j + 1 → A i j ≠ 0) → (∀ i j : Fin n, (j : ℕ) = i + 1 → A i j ≠ 0) →
        ∃ u v p q, u * v = p * q ∧ A⁻¹ = quasiseparableOf u v 1 (u * v) p q 1) :=
  ⟨hT.isSemiseparable_inv hA, fun hsub hsup => hT.inv_eq_generatorRep hA hsub hsup⟩

/-- **Fact 2 of §12.2.3** of [golub2013matrix]. If $A \in \mathbb{R}^{n \times n}$ is nonsingular
and quasiseparable, then $A^{-1}$ is quasiseparable. -/
theorem inv_isQuasiseparable {A : Matrix (Fin n) (Fin n) ℝ} (h : A.IsQuasiseparable)
    (hA : IsUnit A) : A⁻¹.IsQuasiseparable :=
  h.inv hA

/-- **Fact 3 of §12.2.3** of [golub2013matrix]. Let $D = \operatorname{diag}(\delta) \in
\mathbb{R}^{n \times n}$ with $\delta_i \neq 0$ for all $i$, let $S \in \mathbb{R}^{n \times n}$
be semiseparable, and let $D + S$ be nonsingular. Then $(D + S)^{-1} = D^{-1} + S_1$ for some
semiseparable $S_1$. -/
theorem inv_diagonal_add_semiseparable {δ : Fin n → ℝ} (hδ : ∀ i, δ i ≠ 0)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsSemiseparable) (hu : IsUnit (diagonal δ + S)) :
    ∃ S₁ : Matrix (Fin n) (Fin n) ℝ, S₁.IsSemiseparable ∧
      (diagonal δ + S)⁻¹ = (diagonal δ)⁻¹ + S₁ :=
  inv_diagonal_add_eq_add hδ hS hu

/-! ### Triangular semiseparable matrices (§12.2.4–12.2.5) -/

/-- **§12.2.4** of [golub2013matrix], triangular semiseparable matrices. A lower triangular
semiseparable matrix $L \in \mathbb{R}^{n \times n}$ is $\mathbf{S}(u, v, t, u .* v, 0, 0, 0)$
for some $u, v \in \mathbb{R}^n$ and some sequence $t$. An upper triangular semiseparable matrix
$U \in \mathbb{R}^{n \times n}$ is $\mathbf{S}(0, 0, 0, p .* q, p, q, r)$ for some
$p, q \in \mathbb{R}^n$ and some sequence $r$. -/
theorem triangular_semiseparable_rep (L U : Matrix (Fin n) (Fin n) ℝ) :
    (L.IsSemiseparable → L.IsLowerTriangular → ∃ u v t, L = quasiseparableOf u v t (u * v) 0 0 0) ∧
      (U.IsSemiseparable → U.IsUpperTriangular →
        ∃ p q r, U = quasiseparableOf 0 0 0 (p * q) p q r) := by
  refine ⟨exists_lower_semiseparable_rep, fun hS hU => ?_⟩
  obtain ⟨u, v, t, h⟩ := exists_lower_semiseparable_rep hS.transpose hU.transpose
  refine ⟨v, u, t, ?_⟩
  rw [← transpose_transpose U, h, transpose_quasiseparableOf, mul_comm v u]

/-- **Equation (12.2.9)** of [golub2013matrix] and the displays after it. Let
$p, q \in \mathbb{R}^n$ and $r \in \mathbb{R}^{n-1}$. For every $x \in \mathbb{R}^n$,
$$\bigl(\operatorname{triu}(pq^T) .* B(r)^{-1}\bigr) x = p .* \bigl(B(r)^{-1} (q .* x)\bigr),$$
that is, the upper triangular semiseparable matrix $\operatorname{triu}(pq^T) .* B(r)^{-1}$ is
$\operatorname{diag}(p) B(r)^{-1} \operatorname{diag}(q)$. If all entries of $p$ and $q$ are
nonzero, then every solution of $\bigl(\operatorname{triu}(pq^T) .* B(r)^{-1}\bigr) x = y$ is
$$x = \bigl(B(r)(y ./ p)\bigr) ./ q.$$

The Lean statement writes $pq^T .* B(r)^{-1}$ without $\operatorname{triu}$. This is the same
matrix, because $B(r)^{-1}$ is upper triangular. -/
theorem equation_12_2_9 (p q : Fin n → ℝ) (r : ℕ → ℝ) :
    (∀ x, (vecMulVec p q ⊙ (unitBidiagonal n r)⁻¹) *ᵥ x = p * ((unitBidiagonal n r)⁻¹ *ᵥ (q * x))) ∧
      ((∀ i, p i ≠ 0) → (∀ i, q i ≠ 0) → ∀ x y,
        (vecMulVec p q ⊙ (unitBidiagonal n r)⁻¹) *ᵥ x = y →
          x = (unitBidiagonal n r *ᵥ (y / p)) / q) :=
  ⟨vecMulVec_hadamard_inv_unitBidiagonal_mulVec p q r, fun hp hq _ _ h =>
    eq_div_of_vecMulVec_hadamard_inv_unitBidiagonal_mulVec_eq r hp hq h⟩

/-- **§12.2.5** of [golub2013matrix], the LU factors of a semiseparable matrix. Let
$A \in \mathbb{R}^{n \times n}$ be semiseparable, and let $A = LU$ with $L$ unit lower
triangular and $U$ upper triangular. Then $U$ is semiseparable. If moreover the leading
principal submatrices of $A$ of orders $1, \dots, n - 1$ are nonsingular, then $L$ is
semiseparable.

**Correction.** The source states that both factors are semiseparable, without a condition. The
claim for $L$ fails for singular $A$: for $$L = \begin{bmatrix} 1 & 0 & 0 \\ 0 & 1 & 0 \\ 1 & 0
& 1 \end{bmatrix}, \qquad U = \begin{bmatrix} 0 & 0 & 0 \\ 0 & 1 & z \\ 0 & 0 & 1
\end{bmatrix},$$ the product $A = LU = U$ is semiseparable, but $L(2{:}3, 1{:}2)$ has rank two.

The factorization is `Matrix.IsLU`, and the leading principal submatrices are
`Matrix.strictLeadingPrincipalSubmatrix`. -/
theorem semiseparable_lu_factors {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hA : A.IsSemiseparable) :
    U.IsSemiseparable ∧
      ((∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) → L.IsSemiseparable) :=
  ⟨h.isSemiseparable_upper hA, h.isSemiseparable_lower hA⟩

/-! ### LU of a semiseparable matrix (Algorithm 12.2.1) -/

section LU

/-- One step of Algorithm 12.2.1, with the 0-based index $k$ for the source's $k + 1$:
$\tau_k = t_k u_{k+1}/u_k$, with two roundings, and $\tilde p_{k+1} = p_{k+1} - p_k \tau_k r_k$,
with three roundings from left to right.

**Reading.** Makes arithmetic rounding explicit and uses total division.
-/
noncomputable def algorithm_12_2_1Step {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (u p : Fin n → ℝ) (t r : ℕ → ℝ) (k : Fin (n - 1)) : M (ℝ × ℝ) := do
  let τk ← rnd ((← rnd (t k * u ⟨k + 1, by omega⟩)) / u ⟨k, by omega⟩)
  let pk ← rnd (p ⟨k + 1, by omega⟩ - (← rnd ((← rnd (p ⟨k, by omega⟩ * τk)) * r k)))
  pure (τk, pk)

/-- **Algorithm 12.2.1** of [golub2013matrix]. Let $u, v, p, q \in \mathbb{R}^n$ with
$u .* v = p .* q$, let $t, r \in \mathbb{R}^{n-1}$, and let
$A = \mathbf{S}(u, v, t, u .* v, p, q, r)$. The algorithm computes $\tilde p \in \mathbb{R}^n$
and $\tau \in \mathbb{R}^{n-1}$ such that $A = LU$ with $L = B(\tau)^{-T}$ and $U =
\operatorname{triu}(\tilde p q^T) .* B(r)^{-1}$. For $k = n - 1, n - 2, \dots, 1$ it sets
$$\tau_k = t_k u_{k+1}/u_k, \qquad \tilde p_{k+1} = p_{k+1} - p_k \tau_k r_k,$$ and then it sets
$\tilde p_1 = p_1$.

Every arithmetic result passes through the rounding hook `rnd`. The loop stores the pair
$(\tau_k, \tilde p_{k+1})$ of step $k$, computed by
`GolubVanLoan.Chapter12.algorithm_12_2_1Step`. The vectors $v$ and $q$ enter only the
specification. The returned $\tau$ is a sequence `ℕ → ℝ` that is zero after the index $n - 2$.

**Reading.** Same descending loop with explicit rounding and total division; pads unused
coefficients with zero.
-/
noncomputable def algorithm_12_2_1 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) (u p : Fin n → ℝ)
    (t r : ℕ → ℝ) : M ((Fin n → ℝ) × (ℕ → ℝ)) := do
  let st ← vecLoopOn (List.finRange (n - 1)).reverse (algorithm_12_2_1Step rnd u p t r)
  pure (fun i => if h : (i : ℕ) = 0 then p i else (st ⟨i - 1, by omega⟩).2,
    fun k => if h : k < n - 1 then (st ⟨k, h⟩).1 else 0)

/-- **Algorithm 12.2.1** of [golub2013matrix], correctness in exact arithmetic. Let
$u, v, p, q \in \mathbb{R}^n$ with $u .* v = p .* q$ and $u_k \neq 0$ for $k = 1, \dots, n - 1$,
let $t$ and $r$ be sequences, and let $A = \mathbf{S}(u, v, t, u .* v, p, q, r)$. Then the
vectors $\tilde p$ and $\tau$ that the algorithm computes in exact arithmetic give the LU
factorization $$A = B(\tau)^{-T} \bigl(\operatorname{triu}(\tilde p q^T) .* B(r)^{-1}\bigr),$$
and they have the closed forms $$\tau = (u(2{:}n) .* t) ./ u(1{:}n-1), \qquad \tilde p =
\begin{bmatrix} p_1 \\ p(2{:}n) - p(1{:}n-1) .* \tau .* r \end{bmatrix}.$$

**Correction.** The source assumes only that $A$ has an LU factorization. This does not ensure
that the divisions by $u_k$ are defined, so the statement assumes $u_k \neq 0$ for
$k = 1, \dots, n - 1$.

**Typo.** The text's "$M = B(\tau)$" should read $M = B(\tau)^T$.

The factorization is `Matrix.IsLU`. The Lean statement writes $\tilde p q^T .* B(r)^{-1}$
without $\operatorname{triu}$, which is the same matrix because $B(r)^{-1}$ is upper triangular. -/
theorem algorithm_12_2_1_spec (u v p q : Fin n → ℝ) (t r : ℕ → ℝ) (huv : u * v = p * q)
    (hu : ∀ k : Fin n, (k : ℕ) + 1 < n → u k ≠ 0) :
    IsLU (quasiseparableOf u v t (u * v) p q r)
        (unitBidiagonal n (Id.run (algorithm_12_2_1 pure u p t r)).2)ᵀ⁻¹
        (vecMulVec (Id.run (algorithm_12_2_1 pure u p t r)).1 q ⊙ (unitBidiagonal n r)⁻¹) ∧
      (∀ k (h : k + 1 < n), (Id.run (algorithm_12_2_1 pure u p t r)).2 k =
        t k * u ⟨k + 1, h⟩ / u ⟨k, by omega⟩) ∧
      (∀ h : 0 < n, (Id.run (algorithm_12_2_1 pure u p t r)).1 ⟨0, h⟩ = p ⟨0, h⟩) ∧
      ∀ k (h : k + 1 < n), (Id.run (algorithm_12_2_1 pure u p t r)).1 ⟨k + 1, h⟩ =
        p ⟨k + 1, h⟩ - p ⟨k, by omega⟩ * (Id.run (algorithm_12_2_1 pure u p t r)).2 k * r k := by
  have hrun : Id.run (algorithm_12_2_1 pure u p t r) =
      (fun i : Fin n => if h : (i : ℕ) = 0 then p i else
          p i - p ⟨i - 1, by omega⟩ * (t (i - 1) * u i / u ⟨i - 1, by omega⟩) * r (i - 1),
        fun k => if h : k < n - 1 then t k * u ⟨k + 1, by omega⟩ / u ⟨k, by omega⟩ else 0) := by
    simp only [algorithm_12_2_1, Id.run_bind, Id.run_pure]
    rw [idRun_vecLoopOn _ (List.nodup_reverse.2 (List.nodup_finRange _))
      (fun i => List.mem_reverse.2 (List.mem_finRange i))]
    simp only [algorithm_12_2_1Step, Id.run_bind, Id.run_pure]
    ext i
    · dsimp only
      split_ifs with h
      · rfl
      · have : (⟨(i : ℕ) - 1 + 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
        simp only [this, mul_assoc]
    · rfl
  have hτ : ∀ k (h : k + 1 < n), (Id.run (algorithm_12_2_1 pure u p t r)).2 k =
      t k * u ⟨k + 1, h⟩ / u ⟨k, by omega⟩ := fun k h => by
    rw [hrun]
    simp [show k < n - 1 by omega]
  have hp : ∀ k (h : k + 1 < n), (Id.run (algorithm_12_2_1 pure u p t r)).1 ⟨k + 1, h⟩ =
      p ⟨k + 1, h⟩ - p ⟨k, by omega⟩ * (Id.run (algorithm_12_2_1 pure u p t r)).2 k * r k :=
    fun k h => by
      rw [hτ k h, hrun]
      simp
  have hp₀ : ∀ h : 0 < n, (Id.run (algorithm_12_2_1 pure u p t r)).1 ⟨0, h⟩ = p ⟨0, h⟩ :=
    fun h => by rw [hrun]; simp
  refine ⟨isLU_quasiseparableOf u v p q _ t r _ huv (fun k h => ?_) hp₀ hp, hτ, hp₀, hp⟩
  rw [hτ k h, div_mul_cancel₀ _ (hu ⟨k, by omega⟩ h)]

end LU

/-! ### The Givens-vector representation and QR (§12.2.6–12.2.7) -/

/-- **Equation (12.2.11)** of [golub2013matrix], the Givens-vector representation. Let
$A_L \in \mathbb{R}^{n \times n}$ be lower triangular and semiseparable with
$(A_L)_{n1} \neq 0$. Then there are cosine–sine pairs $(c_k, s_k)$, with $c_k^2 + s_k^2 = 1$ and
$s_k \neq 0$, and a vector $v \in \mathbb{R}^n$ such that $$(A_L)_{ij} = c_i s_j s_{j+1} \cdots
s_{i-1} v_j \qquad (j \le i),$$ with $c_n = 1$. That is,
$A_L = B(s)^{-T} .* \operatorname{tril}(cv^T)$ with $c = (c_1, \dots, c_{n-1}, 1)$.

**Correction.** The source states the representation without the hypothesis $(A_L)_{n1} \neq 0$.
Its argument ("it is not hard to show") needs this hypothesis: with $s_k \neq 0$ and $c_n = 1$,
the representation forces the first column to vanish when $(A_L)_{n1} = 0$.

Here $n = m + 1$, and the pairs are sequences `ℕ → ℝ`. -/
theorem equation_12_2_11 {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hA : A.IsSemiseparable) (hL : A.IsLowerTriangular) (h0 : A (Fin.last m) 0 ≠ 0) :
    ∃ c s : ℕ → ℝ, (∀ k, c k ^ 2 + s k ^ 2 = 1) ∧ (∀ k, s k ≠ 0) ∧ ∃ v : Fin (m + 1) → ℝ,
      ∀ i j, A i j =
        if j ≤ i then ((if (i : ℕ) = m then 1 else c i) * ∏ l ∈ Finset.Ico (j : ℕ) i, s l) * v j
        else 0 :=
  exists_givensVector_rep hA hL h0

/-- **Equation (12.2.14)** of [golub2013matrix] and the sentences after it. Let $n = N + 1$, let
$(c_k, s_k)$ be cosine–sine pairs, $c_k^2 + s_k^2 = 1$, and let $A \in \mathbb{R}^{n \times n}$
have the lower triangle $\operatorname{tril}(A) = B(s)^{-T} .* \operatorname{tril}(cv^T)$ of the
Givens-vector representation (12.2.11), with $c = (c_1, \dots, c_{n-1}, 1)$. Let
$Q^T = G_1 \cdots G_{n-1}$, where $G_k$ is the rotation $\begin{bmatrix} c_k & s_k \\ -s_k & c_k
\end{bmatrix}$ in the plane $(k, k+1)$. Then $$Q^T \operatorname{tril}(A) =
\operatorname{triu}\bigl((\mathcal{D}_n c) v^T\bigr) .* B(s)^{-1},$$ where
$\mathcal{D}_n c = (1, c_1, \dots, c_{n-1})$. Moreover $Q^T$ is upper Hessenberg,
$Q^T \operatorname{triu}(A, 1)$ is upper triangular, and so $Q^T A = R$ is upper triangular.
Since each $G_k$ is orthogonal, this is a QR factorization of $A$.

The source cites Problem P12.2.9 for the QR factorization. The lower triangle
$\operatorname{tril}(A)$ is `A.strictLower + A.diagPart`, and $Q^T$ is `Matrix.givensChain`. The
Lean statement writes the first product without $\operatorname{triu}$, which is the same matrix
because $B(s)^{-1}$ is upper triangular. -/
theorem equation_12_2_14 {N : ℕ} {c s : ℕ → ℝ} (hcs : ∀ k, c k ^ 2 + s k ^ 2 = 1)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {v : Fin (N + 1) → ℝ}
    (hA : ∀ i j : Fin (N + 1), j ≤ i →
      A i j = ((if (i : ℕ) = N then 1 else c i) * ∏ l ∈ Finset.Ico (j : ℕ) i, s l) * v j) :
    (givensChain N fun k => !![c k, s k; -s k, c k]) * (A.strictLower + A.diagPart) =
        vecMulVec (fun i : Fin (N + 1) => if (i : ℕ) = 0 then 1 else c ((i : ℕ) - 1)) v ⊙
          (unitBidiagonal (N + 1) s)⁻¹ ∧
      (givensChain N fun k => !![c k, s k; -s k, c k]).IsUpperHessenberg ∧
      ((givensChain N fun k => !![c k, s k; -s k, c k]) * A.strictUpper).IsUpperTriangular ∧
      ((givensChain N fun k => !![c k, s k; -s k, c k]) * A).IsUpperTriangular := by
  obtain ⟨h1, h2⟩ := givensChain_mul_strictLower_add_diagPart hcs hA
  refine ⟨h1, givensChain_isUpperHessenberg, h2, ?_⟩
  have hsplit : A = (A.strictLower + A.diagPart) + A.strictUpper := by
    ext i j
    simp only [Matrix.add_apply, strictLower, strictUpper, diagPart, of_apply, diagonal_apply,
      diag_apply]
    rcases lt_trichotomy j i with h | rfl | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp
    · simp [h, h.ne, not_lt.2 h.le]
  rw [hsplit, Matrix.mul_add, h1]
  intro i j hij
  have hij' : j < i := hij
  rw [Matrix.add_apply, h2 hij, add_zero, hadamard_apply, inv_unitBidiagonal, of_apply,
    ite_eq_right (not_le.2 hij'), mul_zero]

/-! ### Algorithm 12.2.2 -/

/-- **Algorithm 12.2.2** of [golub2013matrix], the state of the loop before the step $k$ (0-based).
It consists of the scalars $\tilde u_{k+1}$ and $\tilde f_{k+1}$ and the arrays $c$, $s$, $f$,
$g$ and $h$. The entry $h_{k+1}$ holds the source's $\tilde h_{k+1}$. -/
structure SemiseparableQRState (N : ℕ) where
  /-- The scalar $\tilde u$ of the source. -/
  ut : ℝ
  /-- The scalar $\tilde f$ of the source. -/
  ft : ℝ
  /-- The cosines $c_k$. -/
  c : ℕ → ℝ
  /-- The sines $s_k$. -/
  s : ℕ → ℝ
  /-- The vector $f$. -/
  f : Fin (N + 1) → ℝ
  /-- The vector $g$. -/
  g : Fin (N + 1) → ℝ
  /-- The vector $h$. -/
  h : Fin (N + 1) → ℝ

section QR

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {N : ℕ}

/-- **Algorithm 12.2.2** of [golub2013matrix], one step of the loop, with the 0-based index $k$ for
the source's $k + 1$. The step determines $c_k$ and $s_k$ such that $$\begin{bmatrix} c_k & s_k
\\ -s_k & c_k \end{bmatrix} \begin{bmatrix} u_k \\ \tilde u_{k+1} \end{bmatrix} =
\begin{bmatrix} \tilde u_k \\ 0 \end{bmatrix},$$ sets $\tilde f_k = s_k \tilde f_{k+1}$ and
$f_{k+1} = c_k \tilde f_{k+1}$, computes $$\begin{bmatrix} h_k \\ h_{k+1} \end{bmatrix} =
\begin{bmatrix} c_k & s_k \\ -s_k & c_k \end{bmatrix} \begin{bmatrix} p_k \\ h_{k+1}
\end{bmatrix},$$ and sets $g_k = (\tilde u_k v_k - h_k q_k)/\tilde f_k$.

**Typo.** The display of the source computes $g_k$ with $u_k$ for $\tilde u_k$. The derivation
in the source uses $\tilde u_k$.

The pair $(c_k, s_k)$ is Algorithm 5.1.3, `GolubVanLoan.Chapter05.algorithm_5_1_3`, applied to
$(u_k, \tilde u_{k+1})$. Its rotation is the transpose of the rotation here, so $s_k$ is its
sine with the sign changed, which is exact. The value $\tilde u_k$ is the first entry of the
rotated vector. Every product, sum and quotient is rounded. -/
noncomputable def algorithm_12_2_2Step (u v p q : Fin (N + 1) → ℝ) (st : SemiseparableQRState N)
    (k : Fin N) : M (SemiseparableQRState N) := do
  let cs ← Chapter05.algorithm_5_1_3 rnd (u k.castSucc) st.ut
  let cc := cs.1
  let ss := -cs.2
  let ut ← rnd ((← rnd (cc * u k.castSucc)) + (← rnd (ss * st.ut)))
  let ft ← rnd (ss * st.ft)
  let fk ← rnd (cc * st.ft)
  let hk ← rnd ((← rnd (cc * p k.castSucc)) + (← rnd (ss * st.h k.succ)))
  let hk' ← rnd ((← rnd (cc * st.h k.succ)) - (← rnd (ss * p k.castSucc)))
  let gk ← rnd ((← rnd ((← rnd (ut * v k.castSucc)) - (← rnd (hk * q k.castSucc)))) / ft)
  pure
    { ut := ut
      ft := ft
      c := Function.update st.c k cc
      s := Function.update st.s k ss
      f := Function.update st.f k.succ fk
      g := Function.update st.g k.castSucc gk
      h := Function.update (Function.update st.h k.succ hk') k.castSucc hk }

/-- **Algorithm 12.2.2** of [golub2013matrix]. Let $u, v, p, q \in \mathbb{R}^n$ with
$u .* v = p .* q$ and $u_n \neq 0$, and let $A = \operatorname{tril}(uv^T) +
\operatorname{triu}(pq^T, 1)$. The algorithm computes cosine–sine pairs
$(c_1, s_1), \dots, (c_{n-1}, s_{n-1})$ and vectors $f, g, h \in \mathbb{R}^n$ such that
$Q^T A = R = \operatorname{triu}(fg^T + hq^T)$, where $Q$ is defined by (12.2.12) and (12.2.13).
It sets $\tilde u_n = u_n$, $\tilde f_n = u_n$, $g_n = v_n$ and $h_n = 0$, performs the step
`GolubVanLoan.Chapter12.algorithm_12_2_2Step` for $k = n - 1, n - 2, \dots, 1$, and sets
$f_1 = \tilde f_1$.

The program works on `Fin (N + 1)`, so $n = N + 1$, with 0-based indices. It returns
$(c, s, f, g, h)$, with the pairs as sequences `ℕ → ℝ`, the form that `Matrix.givensChain`
takes. The hypotheses on $u$, $v$, $p$ and $q$ belong to the specification
`GolubVanLoan.Chapter12.algorithm_12_2_2_spec`.

**Reading.** Updated numerator and explicit rounded descending loop.
-/
noncomputable def algorithm_12_2_2 (u v p q : Fin (N + 1) → ℝ) :
    M ((ℕ → ℝ) × (ℕ → ℝ) × (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) := do
  let st ← (List.finRange N).reverse.foldlM (algorithm_12_2_2Step rnd u v p q)
    { ut := u (Fin.last N), ft := u (Fin.last N), c := 0, s := 0, f := 0,
      g := Function.update 0 (Fin.last N) (v (Fin.last N)), h := 0 }
  pure (st.c, st.s, Function.update st.f 0 st.ft, st.g, st.h)

end QR

/-- The rotation block $\begin{bmatrix} c_k & s_k \\ -s_k & c_k \end{bmatrix}$ of Algorithm 12.2.2.
-/
private abbrev rotBlock (c s : ℕ → ℝ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![c k, s k; -s k, c k]

/-- The matrix $A^{(t)} = G_t \cdots G_{n-1} A$ of the source's derivation, built from the state
before the step $t - 1$: the rows above $t$ are those of $A$, row $t$ is $\tilde u_t v_j$ left
of the diagonal and $\tilde f_t g_j + \tilde h_t q_j$ from the diagonal on, and the rows below
$t$ are those of $\operatorname{triu}(fg^T + hq^T)$. -/
private def stage {N : ℕ} (u v p q : Fin (N + 1) → ℝ) (t : ℕ) (st : SemiseparableQRState N) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  of fun i j => if (i : ℕ) < t then (if j ≤ i then u i * v j else p i * q j)
    else if (i : ℕ) = t then (if (j : ℕ) < t then st.ut * v j else st.ft * st.g j + st.h i * q j)
    else if j < i then 0 else st.f i * st.g j + st.h i * q j

/-- One rotation of the derivation, $G_k A^{(k+1)} = A^{(k)}$, for a pair $(c, s)$ that annihilates
$\tilde u_{k+1}$, that is $-s u_k + c \tilde u_{k+1} = 0$, and with
$\tilde f_k = s \tilde f_{k+1} \neq 0$. -/
private theorem stage_step {N : ℕ} (u v p q : Fin (N + 1) → ℝ) (st : SemiseparableQRState N)
    (a : Fin N) {c s : ℝ} {c' s' : ℕ → ℝ} (hz : -s * u a.castSucc + c * st.ut = 0)
    (hft : s * st.ft ≠ 0) :
    planeEmbed a.castSucc a.succ !![c, s; -s, c] * stage u v p q ((a : ℕ) + 1) st =
      stage u v p q (a : ℕ)
        { ut := c * u a.castSucc + s * st.ut, ft := s * st.ft, c := c', s := s',
          f := Function.update st.f a.succ (c * st.ft),
          g := Function.update st.g a.castSucc
            (((c * u a.castSucc + s * st.ut) * v a.castSucc -
              (c * p a.castSucc + s * st.h a.succ) * q a.castSucc) / (s * st.ft)),
          h := Function.update (Function.update st.h a.succ (c * st.h a.succ - s * p a.castSucc))
            a.castSucc (c * p a.castSucc + s * st.h a.succ) } := by
  have hne : a.castSucc ≠ a.succ := a.castSucc_lt_succ.ne
  ext i j
  rw [planeEmbed_mul_apply _ hne]
  simp only [stage, of_apply, Function.update_apply, Fin.ext_iff, Fin.le_def, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  split_ifs <;> try first
    | (exfalso; omega)
    | ring1
  · have hj : j = a.castSucc := Fin.ext (by assumption)
    subst hj
    have hs : s ≠ 0 := left_ne_zero_of_mul hft
    have hf : st.ft ≠ 0 := right_ne_zero_of_mul hft
    field_simp
    ring
  · linear_combination (v j) * hz

/-- A factor `Matrix.givensFactor N M k` of a chain depends only on the block $M_k$. -/
private theorem givensFactor_congr {N : ℕ} {M M' : ℕ → Matrix (Fin 2) (Fin 2) ℝ} {k : ℕ}
    (h : M k = M' k) : givensFactor N M k = givensFactor N M' k := by
  simp only [givensFactor, h]

/-- For $k < N$, the factor $G_k$ of a chain is the block $M_k$ embedded in the plane $(k, k + 1)$.
-/
private theorem givensFactor_of_lt {N : ℕ} (M : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (a : Fin N) :
    givensFactor N M a = planeEmbed a.castSucc a.succ (M a) := by
  rw [givensFactor, dite_eq_left_of_eq_true (eq_true a.isLt)]
  rfl

/-- In exact arithmetic, one step of Algorithm 12.2.2 takes the rotation
$\begin{bmatrix} c & s \\ -s & c \end{bmatrix}$ from Algorithm 5.1.3 on $(u_k, \tilde u_{k+1})$,
with $s$ the sine of Algorithm 5.1.3 with the sign changed, and updates $\tilde u$, $\tilde f$,
$c$, $s$, $f$, $g$ and $h$ by the formulas of the step, without rounding.

**Correction.** Unfolds the corrected numerator in exact arithmetic.
-/
theorem algorithm_12_2_2Step_pure {N : ℕ} (u v p q : Fin (N + 1) → ℝ)
    (st : SemiseparableQRState N) (a : Fin N) :
    Id.run (algorithm_12_2_2Step pure u v p q st a) =
      { ut := (Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * u a.castSucc +
          -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 * st.ut
        ft := -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 * st.ft
        c := Function.update st.c a
          (Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1
        s := Function.update st.s a
          (-(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2)
        f := Function.update st.f a.succ
          ((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * st.ft)
        g := Function.update st.g a.castSucc
          ((((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * u a.castSucc +
            -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 * st.ut) *
              v a.castSucc -
            ((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * p a.castSucc +
              -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 *
                st.h a.succ) * q a.castSucc) /
            (-(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 * st.ft))
        h := Function.update (Function.update st.h a.succ
            ((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * st.h a.succ -
              -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 *
                p a.castSucc)) a.castSucc
          ((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * p a.castSucc +
            -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 *
              st.h a.succ) } :=
  rfl

/-- **Algorithm 12.2.2** of [golub2013matrix], correctness in exact arithmetic. Let $n = N + 1$, let
$u, v, p, q \in \mathbb{R}^n$ with $u_n \neq 0$, and let $A = \operatorname{tril}(uv^T) +
\operatorname{triu}(pq^T, 1)$. Let $(c, s, f, g, h)$ be the output of the algorithm in exact
arithmetic, and let $Q^T = G_1 \cdots G_{n-1}$ as in (12.2.12)–(12.2.13), with the rotations
$G_k = \begin{bmatrix} c_k & s_k \\ -s_k & c_k \end{bmatrix}$ in the planes $(k, k+1)$. Then
$Q^T$ is orthogonal, $$Q^T A = R = \operatorname{triu}(fg^T + hq^T),$$ and $s_k \neq 0$ for
$k = 1, \dots, n - 1$.

**Generalization.** The source assumes $u .* v = p .* q$. The statement does not need this
hypothesis.

The source argues that the $s_k$ are nonzero because $|\tilde u_k| = \|u(k{:}n)\|_2 \neq 0$. So
every division of the algorithm by $\tilde f_k = s_k \cdots s_{n-1} u_n$ is by a nonzero number.
The matrix $Q^T$ is `Matrix.givensChain` of the blocks $G_k$. The proof is a downward induction
on the source's $A^{(k)} = G_k \cdots G_{n-1} A$, one rotation per step. -/
theorem algorithm_12_2_2_spec {N : ℕ} (u v p q : Fin (N + 1) → ℝ) (hu : u (Fin.last N) ≠ 0) :
    givensChain N (fun k => !![(Id.run (algorithm_12_2_2 pure u v p q)).1 k,
        (Id.run (algorithm_12_2_2 pure u v p q)).2.1 k;
        -(Id.run (algorithm_12_2_2 pure u v p q)).2.1 k,
        (Id.run (algorithm_12_2_2 pure u v p q)).1 k]) ∈ orthogonalGroup (Fin (N + 1)) ℝ ∧
      givensChain N (fun k => !![(Id.run (algorithm_12_2_2 pure u v p q)).1 k,
          (Id.run (algorithm_12_2_2 pure u v p q)).2.1 k;
          -(Id.run (algorithm_12_2_2 pure u v p q)).2.1 k,
          (Id.run (algorithm_12_2_2 pure u v p q)).1 k]) *
          (of fun i j => if j ≤ i then u i * v j else p i * q j) =
        (of fun i j => if i ≤ j then
          (Id.run (algorithm_12_2_2 pure u v p q)).2.2.1 i *
            (Id.run (algorithm_12_2_2 pure u v p q)).2.2.2.1 j +
          (Id.run (algorithm_12_2_2 pure u v p q)).2.2.2.2 i * q j else 0) ∧
      ∀ k < N, (Id.run (algorithm_12_2_2 pure u v p q)).2.1 k ≠ 0 := by
  set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    of fun i j => if j ≤ i then u i * v j else p i * q j with hA
  let st₀ : SemiseparableQRState N :=
    { ut := u (Fin.last N)
      ft := u (Fin.last N)
      c := 0
      s := 0
      f := 0
      g := Function.update 0 (Fin.last N) (v (Fin.last N))
      h := 0 }
  -- the invariant after the steps `N − 1, …, t`
  let Inv : ℕ → SemiseparableQRState N → Prop := fun t st =>
    t ≤ N ∧ prodFwd (fun k => givensFactor N (rotBlock st.c st.s) (t + k)) (N - t) * A =
      stage u v p q t st ∧ st.ut ≠ 0 ∧ st.ft ≠ 0 ∧
      ∀ k, t ≤ k → k < N → st.c k ^ 2 + st.s k ^ 2 = 1 ∧ st.s k ≠ 0
  have hfin := List.foldl_prefix_induction
    (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k))
    (l := (List.finRange N).reverse) (fun pre st => Inv (N - pre.length) st) (b := st₀) ?h0 ?hs
  case h0 =>
    refine ⟨Nat.sub_le _ _, ?_, hu, hu, fun k hk hk' => absurd hk' (by simp at hk; omega)⟩
    simp only [List.length_nil, Nat.sub_zero, Nat.sub_self, prodFwd_zero, Matrix.one_mul]
    ext i j
    simp only [stage, hA, of_apply]
    by_cases hiN : (i : ℕ) < N
    · rw [ite_eq_left hiN]
    · have hiL : i = Fin.last N := Fin.ext (by simp; omega)
      subst hiL
      rw [ite_eq_right hiN, ite_eq_left (Fin.val_last N)]
      by_cases hj : (j : ℕ) < N
      · rw [ite_eq_left hj, ite_eq_left (Fin.le_last j)]
      · have hjL : j = Fin.last N := Fin.ext (by simp; omega)
        subst hjL
        simp [st₀]
  case hs =>
    intro pre a rest hl st hInv
    have hlen : pre.length < N := by
      have := congrArg List.length hl
      simp at this
      omega
    have ha : (a : ℕ) = N - 1 - pre.length := by
      have h1 : (List.finRange N).reverse[pre.length]'(by simpa using hlen) = a := by
        simp [hl]
      rw [List.getElem_reverse, List.getElem_finRange] at h1
      rw [← h1]
      simp
    obtain ⟨-, hprod, hut, hft, hcs⟩ := hInv
    rw [show N - pre.length = (a : ℕ) + 1 by omega] at hprod hcs
    simp only [List.length_append, List.length_singleton,
      show N - (pre.length + 1) = (a : ℕ) by omega]
    obtain ⟨hcs1, hcs2, hcs3⟩ := Chapter05.algorithm_5_1_3_spec (u a.castSucc) st.ut
    set cs := Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut) with hcsdef
    have hs0 : cs.2 ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_add] at hcs2
      have hc : cs.1 ≠ 0 := by
        intro hc
        rw [hc, h0] at hcs1
        norm_num at hcs1
      exact hut ((mul_eq_zero.1 hcs2).resolve_left hc)
    rw [algorithm_12_2_2Step_pure]
    refine ⟨by omega, ?_, ?_, mul_ne_zero (neg_ne_zero.2 hs0) hft, fun k hk hk' => ?_⟩
    · rw [show N - (a : ℕ) = (N - ((a : ℕ) + 1)) + 1 by omega, prodFwd_succ',
        Matrix.mul_assoc]
      have htail : prodFwd (fun k => givensFactor N (rotBlock (Function.update st.c a cs.1)
          (Function.update st.s a (-cs.2))) ((a : ℕ) + (k + 1))) (N - ((a : ℕ) + 1)) =
          prodFwd (fun k => givensFactor N (rotBlock st.c st.s) ((a : ℕ) + 1 + k))
            (N - ((a : ℕ) + 1)) := by
        refine prodFwd_congr fun k _ => ?_
        rw [show (a : ℕ) + (k + 1) = (a : ℕ) + 1 + k by omega]
        refine givensFactor_congr ?_
        have hne : (a : ℕ) + 1 + k ≠ (a : ℕ) := by omega
        simp only [rotBlock, Function.update_of_ne hne]
      rw [htail, hprod, add_zero, givensFactor_of_lt]
      simp only [rotBlock, Function.update_self]
      exact stage_step u v p q st a (by rw [neg_neg]; linarith)
        (mul_ne_zero (neg_ne_zero.2 hs0) hft)
    · -- `|ũ_k| = √(u_k² + ũ_{k+1}²) > 0`
      intro h0
      have h2 : cs.1 * u a.castSucc - cs.2 * st.ut = 0 := by linarith
      rw [h2, abs_zero] at hcs3
      have := (Real.sqrt_eq_zero (by positivity)).1 hcs3.symm
      exact hut (by nlinarith [sq_nonneg (u a.castSucc), sq_nonneg st.ut])
    · rcases eq_or_lt_of_le hk with hk | hk
      · subst hk
        simp only [Function.update_self]
        exact ⟨by rw [neg_sq]; exact hcs1, neg_ne_zero.2 hs0⟩
      · have hne : k ≠ (a : ℕ) := by omega
        simp only [Function.update_of_ne hne]
        exact hcs k (by omega) hk'
  -- read off the final state
  obtain ⟨-, hprod, -, -, hcs⟩ := hfin
  simp only [List.length_reverse, List.length_finRange, Nat.sub_self, zero_add,
    Nat.sub_zero] at hprod hcs
  have hrun : Id.run (algorithm_12_2_2 pure u v p q) =
      (((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).c,
        ((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).s,
        Function.update ((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).f 0
          ((List.finRange N).reverse.foldl
            (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).ft,
        ((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).g,
        ((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).h) := by
    rw [algorithm_12_2_2, Id.run_bind, List.idRun_foldlM, Id.run_pure]
  rw [hrun]
  generalize (List.finRange N).reverse.foldl
    (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀ = st at hprod hcs ⊢
  refine ⟨prodFwd_mem_orthogonalGroup (r := N) (fun k _ => ?_), ?_,
    fun k hk => (hcs k (Nat.zero_le _) hk).2⟩
  · by_cases hk : k < N
    · rw [givensFactor, dite_eq_left_of_eq_true (eq_true hk)]
      have h := planeRotation_mem_orthogonalGroup (j := (⟨k, by omega⟩ : Fin (N + 1)))
        (k := ⟨k + 1, by omega⟩) (Fin.ne_of_lt (Fin.mk_lt_mk.2 (Nat.lt_succ_self k)))
        (c := st.c k) (s := -st.s k) (by rw [neg_sq]; exact (hcs k (Nat.zero_le _) hk).1)
      rw [planeRotation, neg_neg] at h
      exact h
    · rw [givensFactor, dite_eq_right_of_eq_false (eq_false hk)]
      exact one_mem _
  · change prodFwd (fun k => givensFactor N (rotBlock st.c st.s) k) N * A = _
    rw [hprod]
    ext i j
    simp only [stage, of_apply, Nat.not_lt_zero, ↓reduceIte, Function.update_apply]
    by_cases hi : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst hi0
      simp
    · rw [ite_eq_right hi, ite_eq_right (fun h : i = 0 => hi (by rw [h]; rfl))]
      by_cases hji : j < i
      · rw [ite_eq_left hji, ite_eq_right (not_le.2 hji)]
      · rw [ite_eq_right hji, ite_eq_left (not_lt.1 hji)]

/-- **Equation (12.2.16)** of [golub2013matrix]. Let $u, v, p, q \in \mathbb{R}^n$ with
$u_n \neq 0$, and let $A = \operatorname{tril}(uv^T) + \operatorname{triu}(pq^T, 1)$, the
generator representation (12.2.15). Then there are an orthogonal matrix $Q^T$ and vectors
$f, g, h \in \mathbb{R}^n$ with $$Q^T A = R = \operatorname{triu}(fg^T + hq^T).$$ So $R$ is the
upper triangular part of a matrix of rank at most two.

The matrix $Q^T$ is that of Algorithm 12.2.2, `GolubVanLoan.Chapter12.algorithm_12_2_2_spec`.

**Correction.** The second term in the printed (12.2.15) includes the diagonal, whereas
Algorithm 12.2.2 uses $\operatorname{triu}(pq^T, 1)$. This statement follows the algorithm,
which takes the diagonal from $uv^T$ alone. -/
theorem equation_12_2_16 {N : ℕ} (u v p q : Fin (N + 1) → ℝ) (hu : u (Fin.last N) ≠ 0) :
    ∃ Qt ∈ orthogonalGroup (Fin (N + 1)) ℝ, ∃ f g h : Fin (N + 1) → ℝ,
      Qt * (of fun i j => if j ≤ i then u i * v j else p i * q j) =
        of fun i j => if i ≤ j then f i * g j + h i * q j else 0 := by
  obtain ⟨h1, h2, -⟩ := algorithm_12_2_2_spec u v p q hu
  exact ⟨_, h1, _, _, _, h2⟩

/-! ### Banded inverses (§12.2.8) -/

/-- **§12.2.8** of [golub2013matrix], banded inverses. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular and $\{p, q\}$-generator representable: there are $U, V \in \mathbb{R}^{n \times p}$
and $P, Q \in \mathbb{R}^{n \times q}$ with $\operatorname{tril}(A, p - 1) =
\operatorname{tril}(UV^T, p - 1)$ and $\operatorname{triu}(A, -q + 1) =
\operatorname{triu}(PQ^T, -q + 1)$. Then $A^{-1}$ has lower bandwidth $p$ and upper bandwidth
$q$: $[A^{-1}]_{ij} = 0$ if $i > j + p$ or $j > i + q$.

The hypothesis is `Matrix.IsGeneratorRepresentableOfOrder`. -/
theorem inv_banded_of_generatorRepresentable {A : Matrix (Fin n) (Fin n) ℝ} {p q : ℕ}
    (h : A.IsGeneratorRepresentableOfOrder p q) (hA : IsUnit A) :
    A⁻¹.HasLowerBandwidth p ∧ A⁻¹.HasUpperBandwidth q :=
  h.hasBandwidth_inv hA

/-! ### The orthogonal Hessenberg eigenproblem (§12.2.10) -/

/-- **Equation (12.2.18)** of [golub2013matrix]. Let $H \in \mathbb{R}^{n \times n}$ be orthogonal
and upper Hessenberg, with positive subdiagonal entries and $\det H = 1$, and let $n$ be even.
Then there are angles $\varphi_1, \dots, \varphi_{n-1}$ with $0 < \varphi_k < \pi$ and $$H = G_1
\cdots G_{n-1} G_n,$$ where $G_k$ is the reflection $R(\varphi_k) = \begin{bmatrix}
-\cos\varphi_k & \sin\varphi_k \\ \sin\varphi_k & \cos\varphi_k \end{bmatrix}$ in the plane
$(k, k+1)$ for $k < n$, and $G_n = \operatorname{diag}(1, \dots, 1, -1)$.

**Correction.** The source assumes only a nonzero subdiagonal. A positive subdiagonal is reached
by a diagonal similarity with entries $\pm 1$. Even order and $\det H = 1$ are the cases that
remain after the text deflates the others.

Here $n = N + 1$, $R(\varphi)$ is `Matrix.planeReflector φ`, and $G_1 \cdots G_{n-1}$ is
`Matrix.givensChain`. -/
theorem equation_12_2_18 {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hH : H ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hHess : H.IsUpperHessenberg)
    (hsub : ∀ i : Fin N, 0 < H i.succ i.castSucc) (hdet : H.det = 1) (heven : Even (N + 1)) :
    ∃ φ : ℕ → ℝ, (∀ k < N, 0 < φ k ∧ φ k < Real.pi) ∧
      H = givensChain N (fun k => planeReflector (φ k)) *
        diagonal fun i : Fin (N + 1) => if (i : ℕ) = N then -1 else 1 :=
  exists_orthogonalHessenberg_eq_prod_planeReflector hH hHess hsub hdet heven

/-- **Equation (12.2.19)** of [golub2013matrix]. Let $H \in \mathbb{R}^{2m \times 2m}$ be orthogonal
and upper Hessenberg with $\det H = 1$. Then there are angles $\theta_1, \dots, \theta_m$ such
that the eigenvalues of $H$ are $\cos\theta_k \pm i \sin\theta_k = e^{\pm i\theta_k}$ for
$k = 1, \dots, m$: $m$ conjugate pairs on the unit circle. Precisely, the characteristic
polynomial of $H$ over $\mathbb{C}$ is $$\prod_{k=1}^m (x - e^{i\theta_k})(x -
e^{-i\theta_k}).$$

The Hessenberg structure is not used in the proof. -/
theorem equation_12_2_19 {m : ℕ} {H : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hH : H ∈ orthogonalGroup (Fin (2 * m)) ℝ) (_hHess : H.IsUpperHessenberg) (hdet : H.det = 1) :
    ∃ θ : Fin m → ℝ, (H.map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (Complex.exp (θ k * Complex.I))) *
        (Polynomial.X - Polynomial.C (Complex.exp (-θ k * Complex.I))) :=
  exists_charpoly_eq_prod_of_mem_specialOrthogonalGroup
    (mem_specialOrthogonalGroup_iff.2 ⟨hH, hdet⟩)

/-- **§12.2.10** of [golub2013matrix], quasiseparability. Every orthogonal upper Hessenberg matrix
$H \in \mathbb{R}^{n \times n}$ is quasiseparable. The source derives this from (12.2.4) and
(12.2.18).

**Generalization.** The statement imposes no parity, determinant, or sign restrictions on the
subdiagonal. The rank bound follows directly from orthogonality and the upper Hessenberg
structure. -/
theorem orthogonalHessenberg_isQuasiseparable {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H ∈ orthogonalGroup (Fin n) ℝ) (hHess : H.IsUpperHessenberg) : H.IsQuasiseparable :=
  Matrix.orthogonalHessenberg_isQuasiseparable hH hHess

/-- **Fact 1 of §12.2.10** of [golub2013matrix]. Let $\varphi_1, \dots, \varphi_{n-1}$ be angles,
let $G_1, \dots, G_n$ be the factors of the product form (12.2.18), and let
$H = G_1 \cdots G_n$. Let $H_o = G_1 G_3 \cdots$ be the product of the factors with odd index
and $H_e = G_2 G_4 \cdots$ the product of the factors with even index. Then $H$ is similar to
$\tilde H = H_o H_e$. For even $n$, $H_o = \operatorname{diag}(R(\varphi_1), R(\varphi_3),
\dots, R(\varphi_{n-1}))$ and $H_e = \operatorname{diag}(1, R(\varphi_2), \dots,
R(\varphi_{n-2}), -1)$.

The factors are `Matrix.reflectorFactor N φ`, with $n = N + 1$, and $H$ is
`prodFwd (Matrix.reflectorFactor N φ) (N + 1)`. With 0-based indices, $H_o$ is the product
`prodFwdEven` of the factors with even index and $H_e$ is the product `prodFwdOdd` of the
factors with odd index. The statement holds for every order $n$ and all angles.

**Reading.** Product similarity holds for arbitrary reflector angles.
-/
theorem orthogonalHessenberg_fact_1 {N : ℕ} (φ : ℕ → ℝ) :
    (prodFwd (reflectorFactor N φ) (N + 1)).IsSimilar
      (prodFwdEven (reflectorFactor N φ) (N + 1) * prodFwdOdd (reflectorFactor N φ) (N + 1)) :=
  isSimilar_prod_planeReflector_oddEven φ

/-- **Fact 2 of §12.2.10** of [golub2013matrix]. Let $n = 2m$, let $\varphi_1, \dots, \varphi_{n-1}$
be angles, let $H = G_1 \cdots G_n$ be the product form (12.2.18), and let $H_o$ and $H_e$ be as
in Fact 1. Then there are angles $\theta_1, \dots, \theta_m$ such that the characteristic
polynomial of $H$ over $\mathbb{C}$ is $\prod_k (x - e^{i\theta_k})(x - e^{-i\theta_k})$, and
such that the matrices $C = (H_o + H_e)/2$ and $S = (H_o - H_e)/2$ are symmetric and tridiagonal
with the characteristic polynomials $$\prod_{k=1}^m \bigl(x - \cos(\theta_k/2)\bigr)\bigl(x +
\cos(\theta_k/2)\bigr) \quad \text{and} \quad \prod_{k=1}^m \bigl(x -
\sin(\theta_k/2)\bigr)\bigl(x + \sin(\theta_k/2)\bigr).$$ So
$\lambda(C) = \{\pm\cos(\theta_k/2)\}$ and $\lambda(S) = \{\pm\sin(\theta_k/2)\}$.

The angles $\theta_k$ exist by (12.2.19), because $H$ is a product of $2m$ reflections and so
special orthogonal (`Matrix.prodFwd_reflectorFactor_mem_specialOrthogonalGroup`). No condition
on the angles $\varphi_k$ is needed.

**Reading.** Allows arbitrary angles and makes matching signed cosine and sine eigenvalues explicit
via characteristic polynomials.
-/
theorem orthogonalHessenberg_fact_2 {N m : ℕ} (hNm : N + 1 = 2 * m) (φ : ℕ → ℝ) :
    ∃ θ : Fin m → ℝ,
      ((prodFwd (reflectorFactor N φ) (N + 1)).map (algebraMap ℝ ℂ)).charpoly =
        ∏ k, (Polynomial.X - Polynomial.C (Complex.exp (θ k * Complex.I))) *
          (Polynomial.X - Polynomial.C (Complex.exp (-θ k * Complex.I))) ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) +
          prodFwdOdd (reflectorFactor N φ) (N + 1))).IsSymm ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) +
          prodFwdOdd (reflectorFactor N φ) (N + 1))).IsTridiagonal ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) +
          prodFwdOdd (reflectorFactor N φ) (N + 1))).charpoly =
        ∏ k, (Polynomial.X - Polynomial.C (Real.cos (θ k / 2))) *
          (Polynomial.X + Polynomial.C (Real.cos (θ k / 2))) ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) -
          prodFwdOdd (reflectorFactor N φ) (N + 1))).IsSymm ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) -
          prodFwdOdd (reflectorFactor N φ) (N + 1))).IsTridiagonal ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) -
          prodFwdOdd (reflectorFactor N φ) (N + 1))).charpoly =
        ∏ k, (Polynomial.X - Polynomial.C (Real.sin (θ k / 2))) *
          (Polynomial.X + Polynomial.C (Real.sin (θ k / 2))) := by
  set H := prodFwd (reflectorFactor N φ) (N + 1)
  set e : Fin (N + 1) ≃ Fin (2 * m) := finCongr hNm
  obtain ⟨hH, hdet⟩ := mem_specialOrthogonalGroup_iff.1
    (prodFwd_reflectorFactor_mem_specialOrthogonalGroup φ hNm)
  have hH' : H.reindex e e ∈ specialOrthogonalGroup (Fin (2 * m)) ℝ := by
    refine mem_specialOrthogonalGroup_iff.2 ⟨?_, by rw [det_reindex_self, hdet]⟩
    rw [mem_orthogonalGroup_iff] at hH ⊢
    rw [reindex_apply, transpose_submatrix, submatrix_mul_equiv, hH, submatrix_one_equiv]
  obtain ⟨θ, hθ⟩ := exists_charpoly_eq_prod_of_mem_specialOrthogonalGroup hH'
  have hθ' : (H.map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (Complex.exp (θ k * Complex.I))) *
        (Polynomial.X - Polynomial.C (Complex.exp (-θ k * Complex.I))) := by
    rw [← hθ, ← charpoly_reindex e (H.map (algebraMap ℝ ℂ))]
    rfl
  obtain ⟨hC3, hS3⟩ := charpoly_oddEven_half_sum φ θ hθ'
  exact ⟨θ, hθ', isSymm_oddEvenHalfSum φ, isTridiagonal_oddEvenHalfSum φ, hC3,
    isSymm_oddEvenHalfDiff φ, isTridiagonal_oddEvenHalfDiff φ, hS3⟩

end GolubVanLoan.Chapter12
